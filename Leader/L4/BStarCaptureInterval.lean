import Leader.L4.BStarBankTrace
import Leader.L4.BStarLongEvents

/-! Capture framing at the actual joined pair row. This does not infer
the owning descriptor from a dirty F or from a matching D alone. -/
namespace L4.BStarCaptureInterval
open AllSizeProtocol BStarTrace BStarLongLayout BStarLongWork
open BStarLongClaims BStarBankCapture BStarBankTrace

def payloadView (b : Fin 3) (x : BitVec LW) :
    (Fin 9 → BitVec 4) × (Fin 9 → BitVec 1) :=
  (fun i => (bankDigit b i).read x,fun i => (bankHeader b i).read x)

def selectedHeader (x : BitVec LW) : Fin 3 × (Fin 9 → BitVec 1) :=
  (BStarLongPublication.readSel x,(payloadView (BStarLongPublication.readSel x) x).2)

theorem payload_protected {b : Fin 3} {q : Patch LW} (h : Protected b q) (x : BitVec LW) :
    payloadView b (q.apply x)=payloadView b x := by
  exact Prod.ext (funext (digit_read h x)) (funext (header_read h x))

theorem selector_protected {b : Fin 3} {q : Patch LW} (h : Protected b q) (x : BitVec LW) :
    BStarLongPublication.readSel (q.apply x)=BStarLongPublication.readSel x := by
  unfold BStarLongPublication.readSel
  rw [selector_read h x]

theorem header_protected {q : Patch LW} (x : BitVec LW)
    (h : Protected (BStarLongPublication.readSel x) q) :
    selectedHeader (q.apply x)=selectedHeader x := by
  unfold selectedHeader
  rw [selector_protected h x,payload_protected h x]

theorem scratch_frame (g : Pair LongGeometry) (x : Pair (BitVec LW))
    (s : Side) (b : Fin 3) : Protected b (lane (sideFlag s) (longScratch g x)) := by
  have a (f : Field LW 1) (v : BitVec 1) (h : 2362≤f.offset) :
      Protected b (f.assign v) := by
    apply frame_assign
    · right
      simp only [bankBase]
      omega
    · exact .inr h
  cases s
  · exact frame_compose (a shField _ (by decide)) (a seField _ (by decide))
  · apply frame_assign
    · right
      change bankBase b+45≤2364
      simp only [bankBase]
      omega
    · exact .inr (by decide)

theorem door_guard_frame (b : Fin 3) (g : Pair LongGeometry) (x : Pair (BitVec LW))
    (q : Pair (Patch LW)) (s : Side) (h : Protected b (lane (sideFlag s) q)) :
    Protected b (lane (sideFlag s) (LongDoorGuard.pairGuard manifest g x q)) := by
  cases s
  · exact h
  · change Protected b (LongDoorGuard.guard manifest g.2.axes.h6 x.2 q.2)
    unfold LongDoorGuard.guard
    split
    · exact frame_compose h (BStarBankWork.of_beforeBank BStarBankWork.repair_frame b)
    · exact h

def joinedPatch (g : Pair LongGeometry) (x : Pair (BitVec LW)) : Pair (Patch LW) :=
  let lw := longWork g x
  let sc := longScratch g x
  LongDoorGuard.pairGuard manifest g x (lw.1.compose sc.1,lw.2.compose sc.2)

theorem joined_protects (g : Pair LongGeometry) (x : Pair (BitVec LW)) (s : Side) (b : Fin 3)
    (h : ∀ o∈offers g x, SafeOffer g x s b o) :
    Protected b (lane (sideFlag s) (joinedPatch g x)) := by
  unfold joinedPatch
  apply door_guard_frame
  have eq : lane (sideFlag s) (((longWork g x).1.compose (longScratch g x).1),
      ((longWork g x).2.compose (longScratch g x).2)) =
      (lane (sideFlag s) (longWork g x)).compose (lane (sideFlag s) (longScratch g x)) := by
    cases s <;> rfl
  rw [eq]
  exact frame_compose (longWork_protects g x s b h) (scratch_frame g x s b)

/-- When the actual event list publishes nothing at this endpoint, only
the owner agreement of any STAGE offer is needed. A suppressed offer is
not a publication and is never used to deduce one. -/
theorem safe_from_events (g : Pair LongGeometry) (x : Pair (BitVec LW)) (s : Side)
    (b : Fin 3)
    (owned : ∀ c p, (c,BStarLongCommand.Offer.advance p)∈offers g x →
      c.source.side=s → StageLiveAt g x b c p)
    (no : ∀ e∈(longTrace g x).publications, e.endpoint≠s) :
    ∀ o∈offers g x, SafeOffer g x s b o := by
  rintro ⟨c,o⟩ ho
  cases o <;> try trivial
  rename_i p
  intro hs
  refine ⟨owned c p ho hs,?_⟩
  cases h : (outEffect g x c p).published with
  | none => rfl
  | some bank =>
    let e : Publication := ⟨c.source.side,bank⟩
    have hh : e∈(selected g x (c,.advance p)).publications := by
      change e∈(outEffect g x c p).published.toList.map (fun b => ⟨c.source.side,b⟩)
      rw [h]
      simp [e]
    have ev := (BStarLongEvents.selected_pub_iff g x c p e).mp hh
    exact (no e ((BStarLongEvents.literal_event_iff g x e).mpr ⟨c,p,ho,ev⟩) hs).elim

def joinedRead (g : Pair LongGeometry) (x : Pair (BitVec LW)) (s : Side) : BitVec LW :=
  (lane (sideFlag s) (joinedPatch g x)).apply (lane (sideFlag s) x)

private theorem abstract_pair_long {a : LargeParams} (b : LargeRows a)
    (x : Pair (LargeSite a)) (s : Side) :
    let g := Pair.map (longGeometry b) x
    let raw := Pair.map LargeSite.long x
    let lw := b.longWork g raw
    let sc := b.longScratch g raw
    let q := LongDoorGuard.pairGuard a.alu g raw (lw.1.compose sc.1,lw.2.compose sc.2)
    (lane (sideFlag s) (largePair b x)).long=(lane (sideFlag s) q).apply (lane (sideFlag s) raw) := by
  cases s <;> rfl

theorem joined_read (k₁ k₂ t₂ J₁ J₂ r c p c₁ : Nat) (hp : 0<p)
    (x : Pair (LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁))) (s : Side) :
    let b := bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
    let g := Pair.map (longGeometry b) x
    let raw : Pair (BitVec LW) := Pair.map LargeSite.long x
    (lane (sideFlag s) (largePair b x)).long=joinedRead g raw s := by
  dsimp only
  rw [abstract_pair_long]
  rfl

/-- The guarded mark records the owner selector even on a nonheader
site. The same selected bank is then read at every physical offset. -/
inductive HeldStep (b : Fin 3) : BitVec LW → BitVec LW → Prop where
  | noTouch (x : BitVec LW) : HeldStep b x x
  | touch (g : Pair LongGeometry) (x : Pair (BitVec LW)) (s : Side)
      (h : ∀ o∈offers g x, SafeOffer g x s b o) :
      HeldStep b (lane (sideFlag s) x) (joinedRead g x s)

theorem held_step_reads {b : Fin 3} {x y : BitVec LW} (h : HeldStep b x y) :
    BStarLongPublication.readSel y=BStarLongPublication.readSel x ∧
      payloadView b y=payloadView b x := by
  cases h with
  | noTouch => exact ⟨rfl,rfl⟩
  | touch g x s safe =>
    exact ⟨selector_protected (joined_protects g x s b safe) _,
      payload_protected (joined_protects g x s b safe) _⟩

inductive HeldTrace (b : Fin 3) : BitVec LW → BitVec LW → Prop where
  | empty (x : BitVec LW) : HeldTrace b x x
  | next {x y z : BitVec LW} : HeldTrace b x y → HeldStep b y z → HeldTrace b x z

theorem held_trace_reads {b : Fin 3} {x y : BitVec LW} (h : HeldTrace b x y) :
    BStarLongPublication.readSel y=BStarLongPublication.readSel x ∧
      payloadView b y=payloadView b x := by
  induction h with
  | empty => exact ⟨rfl,rfl⟩
  | next _ step ih =>
    have F := held_step_reads step
    exact ⟨F.1.trans ih.1,F.2.trans ih.2⟩

set_option maxRecDepth 16000 in
/-- A touched site in the actual joined concrete pair makes a protected
step when the literal ownership and no-publication premises hold. -/
theorem bStar_held_step (k₁ k₂ t₂ J₁ J₂ r c p c₁ : Nat) (hp : 0<p)
    (x : Pair (LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁))) (s : Side) (b : Fin 3) :
    let producer := bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
    let g := Pair.map (longGeometry producer) x
    let raw : Pair (BitVec LW) := Pair.map LargeSite.long x
    (∀ o∈offers g raw, SafeOffer g raw s b o) →
      HeldStep b (lane (sideFlag s) x).long (lane (sideFlag s) (largePair producer x)).long := by
  dsimp only
  intro H
  rw [joined_read _ _ _ _ _ _ _ _ _ hp x s]
  let producer := bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
  let g := Pair.map (longGeometry producer) x
  let raw : Pair (BitVec LW) := Pair.map LargeSite.long x
  have oldEq : (lane (sideFlag s) x).long=lane (sideFlag s) raw := by cases s <;> rfl
  rw [oldEq]
  exact .touch g raw s H

/-- S9's common pre-edge operand may be read at any protected prefix,
using the header's captured selector for every offset. -/
theorem held_operand {r : Nat} {head preHead : BitVec LW}
    {digit preDigit : Fin r → BitVec LW}
    (hhead : HeldTrace (BStarLongPublication.readSel head) head preHead)
    (hdig : ∀ j, HeldTrace (BStarLongPublication.readSel head) (digit j) (preDigit j)) :
    selectedHeader preHead=selectedHeader head ∧
      ∀ j, (payloadView (BStarLongPublication.readSel preHead) (preDigit j)).1 =
        (payloadView (BStarLongPublication.readSel head) (digit j)).1 := by
  have h := held_trace_reads hhead
  constructor
  · unfold selectedHeader
    rw [h.1,h.2]
  · intro j
    rw [h.1,(held_trace_reads (hdig j)).2]

#print axioms bStar_held_step
#print axioms safe_from_events
#print axioms joined_read
#print axioms joined_protects
#print axioms held_operand
end L4.BStarCaptureInterval
