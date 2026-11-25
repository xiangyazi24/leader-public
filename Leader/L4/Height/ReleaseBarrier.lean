import Leader.L4.BStarRepeatedPace

namespace L4.Height.ReleaseBarrier
open AllSizeProtocol BStarLongDoor BStarLongLayout BStarLongToken BStarLongWork
open BStarAcquireVisitOrder BStarH6WordChart BStarAcquireLiteralChain BStarTrace
open BStarResetChartTouch BStarGeneratedOwner BStarLongFixedRouting BStarOwnerControlHistory
open BStarResetChartService BStarGeneratedPCAncestry BStarResetControllerProgress
open BStarLiteralPC BStarArithmeticControllerReturn BStarResetControllerEntry BStarLongCommand

set_option maxRecDepth 4096
set_option maxHeartbeats 1600000

def Past (pc : Nat) : Prop := pc≤2 ∨ 11<pc

private theorem reply_step (old : BitVec LW) (f : Payload)
    (legal : (ctrlOp.read old).toNat<413) (oldPast : Past (ctrlOp.read old).toNat)
    (beforeRelease : ¬((ctrlOp.read old).toNat=2 ∧ pcNext old f=3)) :
    Past (pcNext old f) := by
  unfold Past at *
  rcases oldPast with lo|hi
  · have split : (ctrlOp.read old).toNat=0 ∨ (ctrlOp.read old).toNat=1 ∨
        (ctrlOp.read old).toNat=2 := by omega
    rcases split with eq|eq|eq <;>
      simp only [pcNext,eq] at beforeRelease ⊢ <;>
      split <;> simp_all [nextOrdinary,arithKind] <;> try decide
  · unfold pcNext
    dsimp only
    split
    next => exact .inl (by decide)
    next =>
      split
      next ar =>
        have range := arithmetic_range _ ar
        rcases successor_order old _ range.2 with h|h <;> omega
      next => rcases ordinary_progress old _ f legal with h|h <;> omega

private theorem past_after_fence (old : BitVec LW) (f : Payload) (pc : (ctrlOp.read old).toNat=11) :
    Past (pcNext old f) := by
  have legal : (ctrlOp.read old).toNat<413 := by omega
  unfold pcNext
  dsimp only
  split
  next => exact .inl (by decide)
  next =>
    have no : (arithKind (ctrlOp.read old).toNat).isSome=false := by rw [pc]; decide
    simp only [no,Bool.false_eq_true,if_false]
    rcases ordinary_progress old _ f legal with h|h <;> unfold Past <;> omega

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step (n:=n) B

def source (x : X) (i : Fin n) := (ctrlOp.read (x i).long).toNat

theorem fence_receipt {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (same : ∀ i,Layout B base i=Layout B x i) (e : Fin n)
    (cur : Current hp base (fun j=>S.getD j fall) len x (.busy 11 (.back 0)))
    (ev : Event hp (fun j=>S.getD j fall) len x e (.busy 11 (.back 0)) .idle) :
    Past (source (step x e) (S.getD 0 fall).1) := by
  have root := root_header hp C same
  obtain ⟨f,_,pc⟩ := consume_pc hp (base:=base) (addr:=fun j=>S.getD j fall) (len:=len) (op:=11) root.2 root.1 (sep e) cur ev
  unfold source
  rw [pc]
  exact past_after_fence _ f cur.1.2.2.2

theorem preserve {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (same : ∀ i,Layout B base i=Layout B x i) (e : Fin n) {m d : Mode}
    (cur : Current hp base (fun j=>S.getD j fall) len x m)
    (ev : Event hp (fun j=>S.getD j fall) len x e m d)
    (after : Current hp base (fun j=>S.getD j fall) len (step x e) d)
    (old : Past (source x (S.getD 0 fall).1))
    (notRel : ¬(source x (S.getD 0 fall).1=2 ∧ source (step x e) (S.getD 0 fall).1=3)) :
    Past (source (step x e) (S.getD 0 fall).1) := by
  let root := (S.getD 0 fall).1
  have idleStep (idle : Current hp base (fun j=>S.getD j fall) len x .idle) :
      source (step x e) root=source x root ∨ source (step x e) root=0 := by
    rcases idle_launch_or_hold hp C same idle.2 sep e idle.1 with A|A|A
    · exact .inl (congrArg (fun c : BitVec 2×BitVec 9=>c.2.toNat) A.2.2.1)
    · exact .inr (congrArg (fun c : (Token×BitVec 2)×BitVec 9=>c.2.toNat) A.2.2.1)
    · obtain ⟨_,_,snap⟩ := A.2.1.2
      exact .inl (congrArg (fun c : (Token×BitVec 2)×BitVec 9=>c.2.toNat) snap)
  have idleOK (idle : Current hp base (fun j=>S.getD j fall) len x .idle) :
      Past (source (step x e) root) := by
    rcases idleStep idle with H|H
    · exact H.symm ▸ old
    · rw [H]; exact .inl (by decide)
  cases ev with
  | idle_hold => exact idleOK cur
  | bad_issue => exact idleOK cur
  | launch => exact idleOK cur
  | transit => 
    unfold source at old ⊢
    rw [after.1.2.2.2,←cur.1.2.2.2]
    exact old
  | arrived_hold => 
    unfold source at old ⊢
    rw [after.1.2.2.2,←cur.1.2.2.2]
    exact old
  | consume op own cleared =>
    have R := root_header hp C same
    obtain ⟨f,_,newpc⟩ := consume_pc hp (base:=base) (addr:=fun j=>S.getD j fall) (len:=len) (op:=op) R.2 R.1 (sep e) cur (.consume op own cleared)
    have valid := cur.1.2.1
    unfold LongDoorGuard.valid at valid
    have legal := of_decide_eq_true (Bool.and_eq_true_iff.mp valid).2
    have before : ¬((ctrlOp.read (x root).long).toNat=2 ∧ pcNext (x root).long f=3) :=
      fun H => notRel ⟨H.1,newpc.trans H.2⟩
    unfold source
    rw [newpc]
    exact reply_step _ f legal old before

private theorem initial_current {base x : X} {addr : Nat → Pos n} {L : Nat}
    {a b : Mode} {w : List (Fin n)} (G : GeneratedOwner hp base addr L x a w b) :
    Current hp base addr L x a := by
  cases G <;> assumption

/-- Between the receipt of FENCE and the next actual 2-to-3 source step,
a generated owner cannot return to a busy FENCE on any physical suffix. -/
theorem no_return_before_release {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    {w : List (Fin n)} {m d : Mode}
    (G : GeneratedOwner hp base (fun j=>S.getD j fall) len x m w d)
    (frame : ∀ a j,Layout B base j=Layout B (BStarResetSchedule.run step x a) j)
    (old : Past (source x (S.getD 0 fall).1))
    (stay : ∀ a e b, w=a++e::b →
      ¬(source (BStarResetSchedule.run step x a) (S.getD 0 fall).1=2 ∧
        source (step (BStarResetSchedule.run step x a) e) (S.getD 0 fall).1=3)) :
    ∀ z, d≠.busy 11 z := by
  induction G with
  | endpoint cur =>
    intro z eq
    subst_vars
    have pc : source _ (S.getD 0 fall).1=11 := cur.1.2.2.2
    have impossible : ¬Past 11 := by unfold Past; omega
    exact impossible (Eq.mp (congrArg Past pc) old)
  | @next y a e u b dest cur ev tail ih =>
    apply ih
    · exact fun v j => frame (e::v) j
    · exact preserve hp C sep (frame []) e cur ev (initial_current hp tail) old
        (stay [] e u rfl)
    · intro v f post eq
      exact stay (e::v) f post (congrArg (List.cons e) eq)

#print axioms no_return_before_release
#print axioms preserve
#print axioms fence_receipt
end L4.Height.ReleaseBarrier
