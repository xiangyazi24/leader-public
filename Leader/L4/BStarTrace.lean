import Leader.L4.ShortByteReadouts
import Leader.L4.WidthByteRows

/-! Production manifest, literal long
scratch, and ordered write-intent lowering. The assembler below is
parameterized by the actual remaining producer rows. -/
namespace L4.BStarTrace
open AllSizeProtocol

def manifest : LongManifest := ⟨182,369,413⟩

def production (k₁ k₂ t₂ J₁ J₂ r c p c₁ : Nat) : LargeParams :=
  ⟨k₁,k₂,t₂,J₁,J₂,r,c,p,c₁,manifest⟩

abbrev LW := longWidth manifest

theorem production_long_width : LW=2367 := by decide

abbrev Row (G : Type) (w : Nat) := Pair G → Pair (BitVec w) → Pair (Patch w)

def Transfer {G V : Type} {w : Nat} (read : BitVec w → V) (row : Row G w)
    (step : Pair G → Pair V → Pair V) : Prop :=
  ∀ h x, Prod.map read read (patchPair (row h x) x) = step h (Prod.map read read x)

def offsetL (x : BitVec LW) : Nat := min 5 (x.extractLsb' 2364 3).toNat
def endL (x : BitVec LW) : Bool := x.getLsbD 2362

def currHL (x : BitVec LW) : Bool :=
  let s := (x.extractLsb' 2360 2).toNat
  x.getLsbD (2222+45*(2-(if s<3 then s else 0))+3)

def issue {w} (q : Pair (Patch w)) (t : Bool × Patch w) : Pair (Patch w) :=
  if t.1 then (q.1,q.2.compose t.2) else (q.1.compose t.2,q.2)

def lower {w} (L : List (Bool × Patch w)) : Pair (Patch w) :=
  L.foldl issue (.empty w,.empty w)

def runWrite {w} (x : Pair (BitVec w)) (t : Bool × Patch w) : Pair (BitVec w) :=
  if t.1 then (x.1,t.2.apply x.2) else (t.2.apply x.1,x.2)

theorem issue_apply {w} (q : Pair (Patch w)) (t : Bool × Patch w) (x : Pair (BitVec w)) :
    patchPair (issue q t) x = runWrite (patchPair q x) t := by
  obtain ⟨side,patch⟩ := t
  cases side <;> simp [issue,runWrite,patchPair,Patch.compose_apply]

theorem fold_apply {w} (L : List (Bool × Patch w)) (q : Pair (Patch w)) (x : Pair (BitVec w)) :
    patchPair (L.foldl issue q) x = L.foldl runWrite (patchPair q x) := by
  induction L generalizing q with
  | nil => rfl
  | cons t L ih => simp only [List.foldl_cons,ih,issue_apply]

theorem lower_apply {w} (L : List (Bool × Patch w)) (x : Pair (BitVec w)) :
    patchPair (lower L) x = L.foldl runWrite x := by
  rw [lower,fold_apply]
  cases x
  simp [patchPair,Patch.empty,Patch.apply]

def lane {α : Type} (s : Bool) (x : Pair α) : α := if s then x.2 else x.1

private theorem issue_mask {w} (q : Pair (Patch w)) (t : Bool × Patch w)
    (s : Bool) (i : Nat) :
    (lane s (issue q t)).mask.getLsbD i =
      ((lane s q).mask.getLsbD i || (t.1 == s && t.2.mask.getLsbD i)) := by
  obtain ⟨b,t⟩ := t
  cases b <;> cases s <;> simp [lane,issue,Patch.compose]

/-- This checks *issued* support, not an old/new decoded difference. -/
theorem fold_mask {w} (L : List (Bool × Patch w)) (q : Pair (Patch w))
    (s : Bool) (i : Nat) :
    (lane s (L.foldl issue q)).mask.getLsbD i =
      ((lane s q).mask.getLsbD i || L.any (fun t => t.1 == s && t.2.mask.getLsbD i)) := by
  induction L generalizing q with
  | nil => simp
  | cons t L ih => simp [ih,issue_mask,Bool.or_assoc]

theorem lower_mask {w} (L : List (Bool × Patch w)) (s : Bool) (i : Nat) :
    (lane s (lower L)).mask.getLsbD i = L.any (fun t => t.1 == s && t.2.mask.getLsbD i) := by
  rw [lower,fold_mask]
  cases s <;> simp [lane,Patch.empty]

structure Write (w : Nat) where
  right : Bool
  width : Nat
  field : Field w width
  value : BitVec width

def Write.patch {w} (t : Write w) : Bool × Patch w :=
  (t.right,t.field.assign t.value)

structure Trace (w : Nat) (Event : Type) where
  writes : List (Write w)
  events : List Event

def Trace.lower {w : Nat} {Event : Type} (T : Trace w Event) : Pair (Patch w) :=
  BStarTrace.lower (T.writes.map Write.patch)

theorem Trace.mask_iff {w : Nat} {Event : Type} (T : Trace w Event) (s : Bool) (i : Nat) :
    (lane s T.lower).mask.getLsbD i=true ↔
      ∃ t ∈ T.writes, t.right=s ∧ t.field.offset≤i ∧ i<t.field.offset+t.width := by
  rw [Trace.lower,lower_mask,List.any_eq_true]
  constructor
  · rintro ⟨u,hu,H⟩
    obtain ⟨t,ht,rfl⟩ := List.mem_map.mp hu
    obtain ⟨hs,hm⟩ := Bool.and_eq_true_iff.mp H
    exact ⟨t,ht,beq_iff_eq.mp hs,(t.field.inMask t.value i).mp hm⟩
  · rintro ⟨t,ht,hs,hl,hr⟩
    refine ⟨t.patch,List.mem_map.mpr ⟨t,ht,rfl⟩,?_⟩
    exact Bool.and_eq_true_iff.mpr ⟨beq_iff_eq.mpr hs,(t.field.inMask t.value i).mpr ⟨hl,hr⟩⟩

def shField : Field LW 1 := ⟨2363,by decide⟩
def seField : Field LW 1 := ⟨2362,by decide⟩
def offField : Field LW 3 := ⟨2364,by decide⟩

def nextOffset (g : Pair LongGeometry) : Nat :=
  let i := if g.1.axes.h6 then 0 else min 5 g.1.offset
  if g.2.axes.h6 then 0 else min 5 (i+1)

def longScratch : Row LongGeometry LW := fun g _ =>
  ((shField.assign (BitVec.ofBool g.2.axes.h6)).compose
    (seField.assign (BitVec.ofBool (g.2.inside && g.2.last))),
  offField.assign (BitVec.ofNat 3 (nextOffset g)))

theorem longScratch_values (g : Pair LongGeometry) (x : Pair (BitVec LW)) :
    let y := patchPair (longScratch g x) x
    shField.read y.1=BitVec.ofBool g.2.axes.h6 ∧
    seField.read y.1=BitVec.ofBool (g.2.inside && g.2.last) ∧
    offField.read y.2=BitVec.ofNat 3 (nextOffset g) := by
  simp only [longScratch,patchPair,Patch.compose_apply]
  refine ⟨?_,Field.read_assign ..,Field.read_assign ..⟩
  rw [Field.read_other_assign shField seField _ _ (by decide),Field.read_assign]

theorem longScratch_mask (g : Pair LongGeometry) (x : Pair (BitVec LW)) (i : Nat) :
    ((longScratch g x).1.mask.getLsbD i=true ↔ i=2362 ∨ i=2363) ∧
    ((longScratch g x).2.mask.getLsbD i=true ↔ 2364≤i ∧ i<2367) := by
  simp only [longScratch,Patch.compose,BitVec.getLsbD_or,Bool.or_eq_true,Field.inMask,
    shField,seField,offField]
  exact ⟨by omega,True.intro⟩

theorem longScratch_holds (g : Pair LongGeometry) (x : Pair (BitVec LW)) (i : Nat) :
    (i≠2362 → i≠2363 →
      ((patchPair (longScratch g x) x).1).getLsbD i=x.1.getLsbD i) ∧
    ((i<2364 ∨ 2367≤i) →
      ((patchPair (longScratch g x) x).2).getLsbD i=x.2.getLsbD i) := by
  obtain ⟨L,R⟩ := longScratch_mask g x i
  constructor
  · intro h₁ h₂
    apply Patch.hold
    exact Bool.eq_false_iff.mpr (fun H => (L.mp H).elim h₁ h₂)
  · intro ho
    apply Patch.hold
    exact Bool.eq_false_iff.mpr (fun H => by have := R.mp H; omega)

/-- Same-snapshot reference; a spare selector value chooses bank zero. -/
def reference (h : Headers) (x : BitVec LW) : RefView :=
  ⟨h.h6,currHL x⟩

/-- Fixed production envelope; component arguments are intentional open
ports, not a claim that the remaining producer traces have been implemented. -/
def bundle (a : LargeParams) (ha : a.alu=manifest)
    (mis : Row Bool 96)
    (r1 : Row Bool (reportWidth (a.k1+1) 1 a.J1))
    (r2 : Row Bool (reportWidth 2 a.t2 a.J2))
    (width : Row Bool (30+ell (a.c+1)))
    (work : Row LongGeometry LW) (pub : SharedRows a.p a.c1) :
    LargeRows a := by
  cases a
  simp only at ha
  subst_vars
  exact {
    misSelected := ShortByteReadouts.misSelected
    report1Pulse := ShortByteReadouts.report1Pulse _
    report2Pulse := ShortByteReadouts.report2Pulse _
    widthInside := WidthByteRows.inside
    widthLast := WidthByteRows.last
    longOffset := offsetL
    longSuccessorEnd := endL
    longCurrH := currHL
    mis := mis
    report1 := r1
    report2 := r2
    widthClient := width
    longWork := work
    longScratch := longScratch
    shared := pub }

#print axioms lower_apply
#print axioms Trace.mask_iff
#print axioms longScratch_values
#print axioms longScratch_mask
#print axioms longScratch_holds
#print axioms bundle

structure ScratchView where
  successorHeader : Bool
  successorEnd : Bool
  offset : Nat
  currentH : Bool
  deriving DecidableEq, Repr

def readScratch (x : BitVec LW) : ScratchView :=
  ⟨x.getLsbD 2363,endL x,offsetL x,currHL x⟩

def refreshScratch (g : Pair LongGeometry) (x : Pair ScratchView) : Pair ScratchView :=
  (⟨g.2.axes.h6,g.2.inside && g.2.last,x.1.offset,x.1.currentH⟩,
    ⟨x.2.successorHeader,x.2.successorEnd,nextOffset g,x.2.currentH⟩)

private theorem high_index (x : BitVec LW) :
    2222+45*(2-(if (x.extractLsb' 2360 2).toNat<3
      then (x.extractLsb' 2360 2).toNat else 0))+3<2362 := by
  have h : 2-(if (x.extractLsb' 2360 2).toNat<3
      then (x.extractLsb' 2360 2).toNat else 0)≤2 := Nat.sub_le ..
  omega

/-- Literal scratch transfer, including old selected-bank H, unchanged
on both endpoints. The dormant spare selector retains its raw bits. -/
theorem long_scratch : Transfer readScratch longScratch refreshScratch := by
  intro g x
  let y := patchPair (longScratch g x) x
  obtain ⟨M,E,O⟩ := longScratch_values g x
  change shField.read y.1=BitVec.ofBool g.2.axes.h6 at M
  change seField.read y.1=BitVec.ofBool (g.2.inside && g.2.last) at E
  change offField.read y.2=BitVec.ofNat 3 (nextOffset g) at O
  have span : nextOffset g ≤5 := by unfold nextOffset; dsimp only; split; exact Nat.zero_le _; exact Nat.min_le_left _ _
  have sameL (i : Nat) (hi : i<2362) : y.1.getLsbD i=x.1.getLsbD i :=
    (longScratch_holds g x i).1 (by omega) (by omega)
  have sameR (i : Nat) (hi : i<2364) : y.2.getLsbD i=x.2.getLsbD i :=
    (longScratch_holds g x i).2 (.inl hi)
  have offL : y.1.extractLsb' 2364 3=x.1.extractLsb' 2364 3 := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [BitVec.getLsbD_extractLsb',hi,decide_true,Bool.true_and]
    exact (longScratch_holds g x (2364+i)).1 (by omega) (by omega)
  have selL : y.1.extractLsb' 2360 2=x.1.extractLsb' 2360 2 := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [BitVec.getLsbD_extractLsb',hi,decide_true,Bool.true_and]
    exact sameL _ (by omega)
  have selR : y.2.extractLsb' 2360 2=x.2.extractLsb' 2360 2 := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [BitVec.getLsbD_extractLsb',hi,decide_true,Bool.true_and]
    exact sameR _ (by omega)
  have chL : currHL y.1=currHL x.1 := by
    unfold currHL
    rw [selL]
    exact sameL _ (high_index _)
  have chR : currHL y.2=currHL x.2 := by
    unfold currHL
    rw [selR]
    exact sameR _ (by have := high_index x.2; omega)
  have hM := congrArg (fun u : BitVec 1 => u.getLsbD 0) M
  have hE := congrArg (fun u : BitVec 1 => u.getLsbD 0) E
  have hh : y.1.getLsbD 2363=g.2.axes.h6 := by
    simpa [shField,Field.read] using hM
  have he : y.1.getLsbD 2362=(g.2.inside && g.2.last) := by
    simpa [seField,Field.read] using hE
  have hr : offsetL y.2=nextOffset g := by
    change y.2.extractLsb' 2364 3=BitVec.ofNat 3 (nextOffset g) at O
    unfold offsetL
    rw [O,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega : nextOffset g<2^3),
      Nat.min_eq_right span]
  change (readScratch y.1,readScratch y.2)=refreshScratch g (readScratch x.1,readScratch x.2)
  simp only [refreshScratch,readScratch,endL,hh,he,hr,chL,chR,
    sameR 2363 (by decide),sameR 2362 (by decide)]
  simp only [offsetL,offL]

#print axioms long_scratch
end L4.BStarTrace
