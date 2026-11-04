import Leader.Wu.Elimination.GapClosure

/-!
# Select the shortest actual attack gap

A cyclic layout supplies real gap frames and a total length, not a chosen
minimum or a two-gap span bound. We compute the first minimum gap, take its
cyclic predecessor as recovery, and derive both `k*b ≤ n` and `a + 2*b ≤ n`.
The latter supplies strict sub-ring geometry for `k ≥ 3`, even when recovery
is much longer than attack. The physical configuration and state carrier are
unchanged. There is no enumeration producer or stochastic service claim here.
-/

namespace K2MinimumAttack

open LDSinkGapCleanup LDTwoGapFrame LDSinkTwoGapReachInvariant
  K2GlobalGapClosure FiniteUniformStoppingTree

set_option autoImplicit false

/-! ## A computable finite minimum and the existing cyclic successor -/

/-- First index attaining the minimum of a nonempty finite sequence.
Ties are resolved toward the smaller original index. -/
def minimumIndex : (k : Nat) → 0 < k → (Fin k → Nat) → Fin k
  | 0, hk, _ => False.elim (by omega)
  | 1, _, _ => 0
  | k + 2, _, d =>
    let i := minimumIndex (k + 1) (by omega) (fun j => d j.succ)
    if d 0 ≤ d i.succ then 0 else i.succ

/-- The computed index minimizes every entry; no minimum-existence premise
or choice field is supplied by a layout. -/
theorem minimumIndex_le : ∀ (k : Nat) (hk : 0 < k) (d : Fin k → Nat) (j : Fin k),
    d (minimumIndex k hk d) ≤ d j
  | 0, _, _, j => Fin.elim0 j
  | 1, _, d, j => Fin.cases (Nat.le_refl _) (fun z => Fin.elim0 z) j
  | k + 2, hk, d, j => by
    let i := minimumIndex (k + 1) (by omega) (fun t => d t.succ)
    have htail := minimumIndex_le (k + 1) (by omega) (fun t => d t.succ)
    change d (if d 0 ≤ d i.succ then 0 else i.succ) ≤ d j
    by_cases h : d 0 ≤ d i.succ
    · rw [if_pos h]
      exact Fin.cases (Nat.le_refl _) (fun t => Nat.le_trans h (htail t)) j
    · rw [if_neg h]
      exact Fin.cases (by omega) (fun t => htail t) j

/-- Cyclic predecessor in the existing layout index set. This creates no
physical agent identifier and does not change the layout's successor. -/
def cyclicPred {k : Nat} (i : Fin k) : Fin k :=
  if h : i.val = 0 then ⟨k - 1, by have := i.isLt; omega⟩
  else ⟨i.val - 1, by have := i.isLt; omega⟩

/-- The predecessor is inverse to the production layout's cyclic successor. -/
theorem cyclicSucc_pred {k : Nat} (i : Fin k) :
    MinimalTripleChoice.cyclicSucc (cyclicPred i) = i := by
  apply Fin.ext
  change ((cyclicPred i).val + 1) % k = i.val
  by_cases h : i.val = 0
  · simp only [cyclicPred, dif_pos h]
    have he : k - 1 + 1 = k := by have := i.isLt; omega
    rw [he, Nat.mod_self, h]
  · simp only [cyclicPred, dif_neg h]
    have he : i.val - 1 + 1 = i.val := by omega
    rw [he, Nat.mod_eq_of_lt i.isLt]

/-! ## Total length pays for the minimum and an unselected third gap -/

private theorem sum_single_weight {k : Nat} (i : Fin k) (w : Nat) :
    (List.ofFn (fun j : Fin k => if j = i then w else 0)).sum = w := by
  induction k with
  | zero => exact Fin.elim0 i
  | succ k ih =>
    have hz : ∀ j : Fin k, j.succ ≠ (0 : Fin (k + 1)) := by
      intro j he
      have := congrArg Fin.val he
      change j.val + 1 = 0 at this
      omega
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [List.ofFn_succ, hz, FiniteUniformStoppingTree.ofFn_sum_const]
    · rw [List.ofFn_succ, List.sum_cons]
      have hh : (0 : Fin (k + 1)) ≠ j.succ := fun he => hz j he.symm
      simpa [hh] using ih j

/-- A minimum `b` contributes once for every real gap in the exact mass sum. -/
theorem minimum_average {n k : Nat} (L : CyclicLayout n k) (i : Fin k)
    (hmin : ∀ j, (L.gap i).d ≤ (L.gap j).d) :
    k * (L.gap i).d ≤ n := by
  have hs := ofFn_sum_le (fun _ : Fin k => (L.gap i).d)
    (fun j => (L.gap j).d) hmin
  rw [FiniteUniformStoppingTree.ofFn_sum_const, L.mass] at hs
  exact hs

/-- Keep an arbitrary gap's true length `a` in the sum, and bound the other
entries by the minimum `b`. With at least three entries, at least one further
positive gap remains beyond recovery and attack: `a + 2*b ≤ n`. -/
theorem minimum_third_gap_room {n k : Nat} (L : CyclicLayout n k)
    (hk : 3 ≤ k) (i p : Fin k)
    (hmin : ∀ j, (L.gap i).d ≤ (L.gap j).d) :
    (L.gap p).d + 2 * (L.gap i).d ≤ n := by
  let b := (L.gap i).d
  let a := (L.gap p).d
  have hba : b ≤ a := hmin p
  have hs := ofFn_sum_le
    (fun j : Fin k => b + if j = p then a - b else 0)
    (fun j => (L.gap j).d) (by
      intro j
      by_cases hj : j = p
      · subst j
        rw [if_pos rfl]
        change b + (a - b) ≤ a
        omega
      · simpa only [if_neg hj, Nat.add_zero] using hmin j)
  rw [ofFn_sum_add, FiniteUniformStoppingTree.ofFn_sum_const, sum_single_weight, L.mass] at hs
  have hthree := Nat.mul_le_mul_right b hk
  change a + 2 * b ≤ n
  omega

/-- The actual attack index is computed from the original layout. -/
def attackIndex {n k : Nat} (L : CyclicLayout n k) (hk : 3 ≤ k) : Fin k :=
  minimumIndex k (by omega) (fun i => (L.gap i).d)

/-- Build the real adjacent two-gap frame at the minimum attack. Its strict
span bound is derived from the layout's mass and a third positive gap. -/
def minimumAttackFrame {n k : Nat} (L : CyclicLayout n k) (hk : 3 ≤ k) :
    TwoGapFrame n where
  recovery := L.gap (cyclicPred (attackIndex L hk))
  attack := L.gap (attackIndex L hk)
  shared := by simpa only [cyclicSucc_pred] using L.shared (cyclicPred (attackIndex L hk))
  length_lt := by
    have hmin := minimumIndex_le k (by omega) (fun i => (L.gap i).d)
    have hroom := minimum_third_gap_room L hk (attackIndex L hk)
      (cyclicPred (attackIndex L hk)) hmin
    have hb := (L.gap (attackIndex L hk)).hd
    omega

/-- Every selected frame has a globally minimum attack, `b ≤ a`, the sharp
minimum-average bound `k*b ≤ n`, and explicit room for a third gap. -/
theorem minimumAttackFrame_bounds {n k : Nat} (L : CyclicLayout n k) (hk : 3 ≤ k) :
    (∀ j, (minimumAttackFrame L hk).attack.d ≤ (L.gap j).d) ∧
    (minimumAttackFrame L hk).attack.d ≤ (minimumAttackFrame L hk).recovery.d ∧
    k * (minimumAttackFrame L hk).attack.d ≤ n ∧
    (minimumAttackFrame L hk).recovery.d + 2 * (minimumAttackFrame L hk).attack.d ≤ n := by
  have hm := minimumIndex_le k (by omega) (fun i => (L.gap i).d)
  exact ⟨hm, hm _, minimum_average L _ hm, minimum_third_gap_room L hk _ _ hm⟩

/-- Real endpoint/interior realization and the global invariant produce the
repository's exact `GapPair` at the selected frame, for every existing phase.
The resulting state's configuration is definitionally the original `C`. -/
theorem minimumAttackFrame_gapPair {n k ψ : Nat} (hψ : 0 < ψ)
    (ring : DirectedRing n) (L : CyclicLayout n k) (hk : 3 ≤ k)
    (C : Fin n → AgentState ψ) (hC : GlobalInvariant hψ ring C)
    (hE : ∀ i, GapEndpointsPresent (L.gap i) C)
    (hI : ∀ i, GapInteriorFollowers (L.gap i) C)
    (phase : LDSinkTwoGapNoResetKernel.APhase) :
    GapPair hψ (minimumAttackFrame L hk) ⟨C, phase⟩ :=
  selected_gapPair hψ ring C hC (minimumAttackFrame L hk) (hE _) (hI _) (hE _) (hI _) phase

/-- Selector interface for physical minimum-attack service. No minimum,
span bound, or `GapPair` is an input promise; all three are derived. -/
theorem select_minimum_attack {n ψ : Nat} (hψ : 0 < ψ) (ring : DirectedRing n)
    (k : Nat) (hk : 3 ≤ k) (C : Fin n → AgentState ψ)
    (hC : GlobalInvariant hψ ring C) (L : CyclicLayout n k)
    (hE : ∀ i, GapEndpointsPresent (L.gap i) C)
    (hI : ∀ i, GapInteriorFollowers (L.gap i) C) :
    ∃ F : TwoGapFrame n,
      F.attack.d ≤ F.recovery.d ∧ k * F.attack.d ≤ n ∧
      ∀ phase : LDSinkTwoGapNoResetKernel.APhase, GapPair hψ F ⟨C, phase⟩ := by
  obtain ⟨_, hba, havg, _⟩ := minimumAttackFrame_bounds L hk
  exact ⟨minimumAttackFrame L hk, hba, havg,
    minimumAttackFrame_gapPair hψ ring L hk C hC hE hI⟩

/-! ## Nonuniform physical layout: recovery eight, attack two -/

/-- Twelve actual cells with leaders at 0, 8, and 10, label modulus one,
zero signals and no bullets. The ordinary state carrier is unchanged. -/
def nonuniformConfig (i : Fin 12) : AgentState 1 :=
  { PPLLNoCheckBirthOutputLegitimacy.outputCore (by decide) i with
    leader := decide (i.val = 0 ∨ i.val = 8 ∨ i.val = 10) }

/-- The three real gap lengths are `[8,2,2]`, in physical cyclic order. -/
def nonuniformLayout : CyclicLayout 12 3 where
  gap := fun i =>
    if i = 0 then ⟨⟨by decide⟩, 0, 8, by decide, by decide⟩
    else if i = 1 then ⟨⟨by decide⟩, 8, 2, by decide, by decide⟩
    else ⟨⟨by decide⟩, 10, 2, by decide, by decide⟩
  shared := by decide
  mass := by decide

/-- This is a real three-leader configuration in the imported global class,
not only a list of gap lengths. -/
theorem nonuniform_global :
    GlobalClass (by decide) ⟨by decide⟩ 3 nonuniformConfig := by
  refine ⟨by decide, by decide, ?_⟩
  apply global_of_signals_zero
  · unfold Separated
    decide
  · exact K2OutputSafety.cyclicLabels_one _ _
  · intro i
    rfl

/-- Every supplied frame has the actual endpoint leaders and follower
interior required by the physical selector. -/
theorem nonuniform_realization :
    (∀ i, GapEndpointsPresent (nonuniformLayout.gap i) nonuniformConfig) ∧
    (∀ i, GapInteriorFollowers (nonuniformLayout.gap i) nonuniformConfig) := by
  constructor
  · unfold GapEndpointsPresent
    decide
  · have hd : ∀ i, (nonuniformLayout.gap i).d ≤ 8 := by decide
    have hf : ∀ i : Fin 3, ∀ t : Fin 8,
        1 ≤ t.val → t.val < (nonuniformLayout.gap i).d →
        (nonuniformConfig ((nonuniformLayout.gap i).pos t.val)).leader = false := by decide
    intro i t ht htd
    exact hf i ⟨t, by have := hd i; omega⟩ ht htd

/-- The deterministic minimum chooses attack index one, with recovery length
8 and attack length 2. Its span 10 is larger than the competing span 4, and
fails the old `k*(a+b) ≤ 2*n` restriction, while the new bounds and actual
`GapPair` hold for every phase. -/
theorem nonuniform_selection :
    let F := minimumAttackFrame nonuniformLayout (by decide)
    attackIndex nonuniformLayout (by decide) = (1 : Fin 3) ∧
    F.recovery.d = 8 ∧ F.attack.d = 2 ∧
    3 * F.attack.d ≤ 12 ∧ F.recovery.d + F.attack.d < 12 ∧
    2 * 12 < 3 * (F.recovery.d + F.attack.d) ∧
    (nonuniformLayout.gap 1).d + (nonuniformLayout.gap 2).d < F.recovery.d + F.attack.d ∧
    ∀ phase : LDSinkTwoGapNoResetKernel.APhase, GapPair (by decide) F ⟨nonuniformConfig, phase⟩ := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, ?_⟩
  exact minimumAttackFrame_gapPair (by decide) ⟨by decide⟩ nonuniformLayout (by decide)
    nonuniformConfig nonuniform_global.2.2 nonuniform_realization.1 nonuniform_realization.2

end K2MinimumAttack

#print axioms K2MinimumAttack.minimumIndex_le
#print axioms K2MinimumAttack.cyclicSucc_pred
#print axioms K2MinimumAttack.minimum_average
#print axioms K2MinimumAttack.minimum_third_gap_room
#print axioms K2MinimumAttack.minimumAttackFrame_bounds
#print axioms K2MinimumAttack.minimumAttackFrame_gapPair
#print axioms K2MinimumAttack.select_minimum_attack
#print axioms K2MinimumAttack.nonuniform_global
#print axioms K2MinimumAttack.nonuniform_realization
#print axioms K2MinimumAttack.nonuniform_selection
