import Leader.L3.Grant.LeaderlessSpatial

/-!
# G17: the finite short-counter rows

On the finite advice branch (`useSmall = true`) the `small` field of a site
is `OFF`, `SPENT` or `RUN j`.  A selected edge `e = (i, i+1)` writes
`RUN 0` at the responder, unconditionally, and advances the initiator:
`RUN j → RUN (j+1)` for `j + 1 < K`, `RUN (K-1) → SPENT` with a success
report, a padded `RUN j` (`j ≥ K`) is repaired to `RUN 0` without a success,
and `OFF`/`SPENT` stay.  Both writes use only the two old `small` fields.

`shortStep` is that row on `Small`; `grantShortPhysicalSmall` proves it for
`headlinePhysicalNext`; `grantShortPhysicalCostLe` bounds the physical cost of
`headlineGrantReady ∨ headlineGeneratedTarget` by the cost of the first
success of the abstract chain on the vector of `small` fields.
-/

namespace L3

open Classical
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

set_option autoImplicit false
set_option Elab.async false

/-- The finite counter row (C.22) on the two old `small` values: the new
initiator value, the new responder value and the success report. -/
def shortStep (k : Nat) (sx _sy : Small) : Small × Small × Bool :=
  match sx with
  | Small.RUN j =>
      if k ≤ j.val then (smallRunZero, smallRunZero, false)
      else if j.val + 1 < k then (smallRun (j.val + 1), smallRunZero, false)
      else (Small.SPENT, smallRunZero, true)
  | _ => (sx, smallRunZero, false)

/-- `smallPair` is the row `shortStep` on the two `small` fields.

Consumer: `grantShortPhysicalSmall`. -/
theorem smallPairIsShortStep {c : Compiled} (ax ay : Agent c) (k : Nat) :
    smallPair ax ay k = shortStep k ax.small ay.small := by
  unfold smallPair shortStep
  rcases hx : ax.small with _ | _ | j <;> rcases hy : ay.small with _ | _ | j' <;>
    simp [parseRun]
  all_goals
    by_cases h1 : k ≤ j.val
    · simp [h1]
    · by_cases h2 : j.val + 1 < k
      · simp [h1, h2]
      · have h3 : j.val + 1 = k := by omega
        simp [h1, h2, h3]


/-- Both `small` outputs of the literal Base step on the finite branch.

Consumer: `shortTransitionFields`. -/
private theorem shortBaseStepFields (c : Compiled)
    (ev : CertEvent) (x y : Agent c)
    (hsmall : c.useSmall = true) :
    (baseStep c ev x y).1.small = (smallPair x y c.K).1 ∧
    (baseStep c ev x y).2.small = (smallPair x y c.K).2.1 := by
  constructor
  · simp [baseStep, hsmall, Agent.setNative,
      Agent.setCPriv] <;>
      repeat (first | rfl | split)
  · simp [baseStep, hsmall, Agent.setNative,
      Agent.setCPriv] <;>
      repeat (first | rfl | split)

/-- The full transition preserves both `small` outputs of the Base step.

Consumer: `grantShortPhysicalSmall`. -/
private theorem shortTransitionFields (c : Compiled)
    (x y : Agent c) (hsmall : c.useSmall = true) :
    (transition c x y).1.small = (smallPair x y c.K).1 ∧
    (transition c x y).2.small = (smallPair x y c.K).2.1 := by
  rcases hc : certificateStep c x y with ⟨cx, cy, ev⟩
  rcases hh : hKStep c x y with ⟨hx, hy⟩
  have hb := shortBaseStepFields c ev x y hsmall
  simpa [transition, hc, hh, assemble] using hb

/-- Three-way `if` evaluation on a plain type.

Consumer: `grantShortPhysicalSmall`. -/
private theorem shortIteFirst {α : Type} (P Q : Prop) [Decidable P]
    [Decidable Q] (a b c : α) (hp : P) :
    (if P then a else if Q then b else c) = a := by
  rw [if_pos hp]

/-- Consumer: `grantShortPhysicalSmall`. -/
private theorem shortIteSecond {α : Type} (P Q : Prop) [Decidable P]
    [Decidable Q] (a b c : α) (hp : ¬ P) (hq : Q) :
    (if P then a else if Q then b else c) = b := by
  rw [if_neg hp, if_pos hq]

/-- Consumer: `grantShortPhysicalSmall`. -/
private theorem shortIteNeg {α : Type} (P Q : Prop) [Decidable P]
    [Decidable Q] (a b c : α) (hp : ¬ P) (hq : ¬ Q) :
    (if P then a else if Q then b else c) = c := by
  rw [if_neg hp, if_neg hq]

/-- **The finite counter rows on the physical step.**  One selected edge
`e = (e, e+1)` writes the initiator and the responder `small` fields by
`shortStep` and leaves every other site's `small` field unchanged.

Consumer: `grantShortPhysicalCostLe`. -/
theorem grantShortPhysicalSmall {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (hsmall : (compileAdvice (ceilLogTwo n)).useSmall = true)
    (C : HeadlineConfiguration n) (e i : Fin n) :
    (headlinePhysicalNext ring C e i).small =
      (if i = e then
        (shortStep (compileAdvice (ceilLogTwo n)).K (C e).small
          (C (ring.rightNeighbor e)).small).1
      else if i = ring.rightNeighbor e then
        (shortStep (compileAdvice (ceilLogTwo n)).K (C e).small
          (C (ring.rightNeighbor e)).small).2.1
      else (C i).small) := by
  have hne : ring.rightNeighbor e ≠ e :=
    EWord.rightNeighborDifferent ring hn e
  have hdef : headlinePhysicalNext ring C e i =
      (if i = e then
        (transition (compileAdvice (ceilLogTwo n))
          (C e) (C (ring.rightNeighbor e))).1
      else if i = ring.rightNeighbor e then
        (transition (compileAdvice (ceilLogTwo n))
          (C e) (C (ring.rightNeighbor e))).2
      else C i) := rfl
  have hf := shortTransitionFields (compileAdvice (ceilLogTwo n))
    (C e) (C (ring.rightNeighbor e)) hsmall
  have e1 := smallPairIsShortStep (c := compileAdvice (ceilLogTwo n))
    (C e) (C (ring.rightNeighbor e)) (compileAdvice (ceilLogTwo n)).K
  rw [e1] at hf
  by_cases hie : i = e
  · have hl := hdef.trans (shortIteFirst _ _ _ _ _ hie)
    rw [hl, if_pos hie]
    exact hf.1
  · by_cases hir : i = ring.rightNeighbor e
    · have hl := hdef.trans (shortIteSecond _ _ _ _ _ hie hir)
      rw [hl, if_neg hie, if_pos hir]
      exact hf.2
    · have hl := hdef.trans (shortIteNeg _ _ _ _ _ hie hir)
      rw [hl, if_neg hie, if_neg hir]

/-- The abstract one-step update of the vector of `small` fields. -/
def shortNext {n : Nat} (ring : DirectedRing n) (k : Nat)
    (s : Fin n → Small) (e : Fin n) : Fin n → Small :=
  fun i =>
    if i = e then (shortStep k (s e) (s (ring.rightNeighbor e))).1
    else if i = ring.rightNeighbor e then
      (shortStep k (s e) (s (ring.rightNeighbor e))).2.1
    else s i

/-- The success report of the abstract step. -/
def shortSucc {n : Nat} (ring : DirectedRing n) (k : Nat)
    (s : Fin n → Small) (e : Fin n) : Bool :=
  (shortStep k (s e) (s (ring.rightNeighbor e))).2.2

/-- The abstract chain: the vector of `small` fields together with the
flag "a success has been reported". -/
def shortAbsNext {n : Nat} (ring : DirectedRing n) (k : Nat)
    (z : (Fin n → Small) × Bool) (e : Fin n) :
    (Fin n → Small) × Bool :=
  (shortNext ring k z.1 e, z.2 || shortSucc ring k z.1 e)

/-- The vector of `small` fields of a configuration. -/
def shortSmalls {n : Nat} (C : HeadlineConfiguration n) : Fin n → Small :=
  fun i => (C i).small

/-- Cost transfer along a simulation.

Consumer: `grantShortPhysicalCostLe`. -/
private theorem shortCostSimLe {X Y : Type} {n : Nat}
    (next' : X → Fin n → X) (next : Y → Fin n → Y)
    (Sim : X → Y → Prop) (Good' : X → Prop) (Good : Y → Prop)
    (hstep : ∀ x y e, Sim x y → ¬ Good' x → Sim (next' x e) (next y e))
    (hgood : ∀ x y, Sim x y → Good y → Good' x) :
    ∀ T x y, Sim x y →
      costNumerator next' Good' x T ≤ costNumerator next Good y T := by
  classical
  intro T
  induction T with
  | zero => intro x y _; simp
  | succ T ih =>
    intro x y hxy
    by_cases hx : Good' x
    · rw [costNumerator_terminal next' Good' x hx]
      exact Nat.zero_le _
    · have hy : ¬ Good y := fun hy => hx (hgood x y hxy hy)
      rw [costNumerator_succ next' Good' x hx T,
        costNumerator_succ next Good y hy T]
      exact Nat.add_le_add_left
        (ofFn_sum_le _ _ (fun e => ih _ _ (hstep x y e hxy hx))) _

/-- **The physical cost is at most the abstract first-success cost.**  From a
purified configuration on the finite branch, the cost of reaching
`headlineGrantReady ∨ headlineGeneratedTarget` is at most the cost of the
first success of the abstract chain on the `small` fields: before the target
a purified configuration is leaderless and grant-free, the `small` fields
follow the finite counter rows, and a success report mints a physical grant
(`grantClockSmallSuccessMintsPhysicalGrant`).

Consumer: `grantShortCostBound` (GrantShortBound.lean). -/
theorem grantShortPhysicalCostLe {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hsmall : (compileAdvice (ceilLogTwo n)).useSmall = true)
    (C : HeadlineConfiguration n) (hp : headlinePurified ring C) :
    ∀ T, costNumerator (headlinePhysicalNext ring)
        (fun D => headlineGrantReady ring D ∨
          headlineGeneratedTarget ring D) C T ≤
      costNumerator
        (shortAbsNext ring (compileAdvice (ceilLogTwo n)).K)
        (fun z => z.2 = true) (shortSmalls C, false) T := by
  have hn2 : 2 ≤ n := by omega
  refine fun T => shortCostSimLe (headlinePhysicalNext ring)
    (shortAbsNext ring (compileAdvice (ceilLogTwo n)).K)
    (fun x y => headlinePurified ring x ∧ y.1 = shortSmalls x ∧
      (y.2 = true → headlineGrantReady ring x ∨
        headlineGeneratedTarget ring x))
    (fun D => headlineGrantReady ring D ∨ headlineGeneratedTarget ring D)
    (fun z => z.2 = true) ?_ ?_ T C _ ⟨hp, rfl, by simp⟩
  · intro x y e hxy hnot
    obtain ⟨hxp, hys, hyd⟩ := hxy
    have hpost : headlinePurified ring (headlinePhysicalNext ring x e) :=
      headlineStagesPurifiedStep ring hn x e hxp
    have hy2 : y.2 = false := by
      cases h : y.2 with
      | false => rfl
      | true => exact False.elim (hnot (hyd h))
    refine ⟨hpost, ?_, ?_⟩
    · funext i
      have h := grantShortPhysicalSmall ring hn2 hsmall x e i
      show shortNext ring (compileAdvice (ceilLogTwo n)).K y.1 e i =
        (headlinePhysicalNext ring x e i).small
      rw [hys]
      exact h.symm
    · intro hd
      have hsucc : shortSucc ring (compileAdvice (ceilLogTwo n)).K
          y.1 e = true := by
        change (y.2 || shortSucc ring (compileAdvice (ceilLogTwo n)).K
          y.1 e) = true at hd
        rw [hy2] at hd
        simpa using hd
      obtain ⟨hroot, hzero⟩ :=
        grantBlockG18PendingRootlessGrantless ring x hxp hnot
      have hsp : (smallPair (x e) (x (ring.rightNeighbor e))
          (compileAdvice (ceilLogTwo n)).K).2.2 = true := by
        have e1 := smallPairIsShortStep
          (c := compileAdvice (ceilLogTwo n)) (x e)
          (x (ring.rightNeighbor e)) (compileAdvice (ceilLogTwo n)).K
        rw [e1]
        rw [hys] at hsucc
        exact hsucc
      have hg := grantClockSmallSuccessMintsPhysicalGrant ring x e hsmall
        hroot hzero hsp
      exact Or.inl (Or.inr ⟨hpost, e, hg⟩)
  · intro x y hxy hy
    exact hxy.2.2 hy

end L3

#print axioms L3.smallPairIsShortStep
#print axioms L3.grantShortPhysicalSmall
#print axioms L3.grantShortPhysicalCostLe
