import Leader.Wu.ShortGap.CleanBase

/-!
# General strict-base budgets and the composed clean-start budget

The imported end-to-end certificates state the strict-base cost bound only at
the hand-built `physicalCandidateStart`, i.e. at the single rearmed all-Race
configuration `strictRoundStart`. Nothing in those files uses that particular
state: the whole argument is the start credit of the composed Bellman
super-solution, and every `Round` state has the same credit bound. This file
upstreams the general statement on both lanes:

* `Uniform.generalStrictBase_truncatedCost_le` - for every `Round R` state,
  with the unchanged constant `n*m*(2h+1) + n*(2h-1)`;
* `Variable.generalStrictBase_truncatedCost_le` - for every `Round R` state of
  the variable-length lane, with `n*m + 2n^2 + n*(2 hMax - 1)`;
* the predicate form of each (a `GhostRing2` state satisfying `RoundBase`
  together with `HasRace` on its round word), and the reciprocal success tails.

It also assembles the clean start out of the two phases:

* `strictBase_reached_or_success` - the preparation process of
  `ShortGapCleanBase` stops only at a virtual candidate or at a genuine strict
  base, and in the latter case an actual `Round` state is produced;
* `preparation_handoff_truncatedCost_le` - at that handoff the general
  strict-base bound already applies;
* `clean_truncatedCost_le_composed` - the clean-start budget written as
  `preparation + strict`, and `clean_truncatedCost_le_of_composition`, which
  re-derives the repository's clean-start constant from that decomposition
  instead of from the single-round start credit.

Scope note, stated so nothing is overclaimed: the composition here is a
composition of *budgets*, discharged through the imported credit decomposition
(`ShortGapCleanBase.*.clean_credit_decomposition`) and the handoff soundness
lemma. It is not a stopping-time decomposition theorem: no statement of this
file asserts that the composed process literally runs the standalone
`preparationStep` process first. The two phases are connected only by the
credit identity and by `strictBase_reached_or_success`.
-/

namespace ShortGapStrictBaseGeneral
open FiniteUniformStoppingTree
set_option autoImplicit false

/-! ## A public copy of the reciprocal tail helper

The imported files keep this argument `private`, so it is reproved here from
the same public ingredients. It converts a uniform truncated-cost bound into a
division-free success tail. -/
theorem success_tail_of_cost_bound {S : Type} {n B : Nat}
    (step : S → Fin n → StopNode S) (s : S)
    (hn : ∀ s e, step s e ≠ .failure) (hB : 0 < B)
    (hc : ∀ T, truncatedActiveCostNumerator step (.active s) T ≤ n^T*B) (factor : Nat) :
    (factor-1)*n^(factor*B) ≤ factor*successCount step (.active s) (factor*B) := by
  have hd := horizon_mul_activeCount_le_truncatedActiveCostNumerator step (.active s) (factor*B)
  have hb := hc (factor*B)
  have hmul : B * (factor * activeCount step (.active s) (factor*B)) ≤ B*n^(factor*B) := by
    calc
      _ = (factor*B)*activeCount step (.active s) (factor*B) := by ac_rfl
      _ ≤ n^(factor*B)*B := Nat.le_trans hd hb
      _ = _ := Nat.mul_comm _ _
  have hactive := Nat.le_of_mul_le_mul_left hmul hB
  have hfailure :=
    BalancedFailureRestart.failureCount_eq_zero_of_step_ne_failure step hn s (factor*B)
  have hp := node_count_partition step (.active s) (factor*B)
  have hsum : activeCount step (.active s) (factor*B) + successCount step (.active s) (factor*B)
      = n^(factor*B) := by omega
  by_cases hf : factor = 0
  · simp [hf]
  · obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hf
    simp only [Nat.add_sub_cancel,Nat.succ_eq_add_one] at hactive hsum ⊢
    rw [← hsum] at hactive ⊢
    rw [Nat.mul_add]
    simp only [Nat.add_mul,Nat.one_mul] at hactive ⊢
    omega

/-! ## Uniform lane -/

namespace Uniform
open ShortGapLiteralGapRows ShortGapLiteralRingRows ShortGapTwoEpoch
open ShortGapLineage2Closure ShortGapGhostComposition2

/-- Every strict round base carries the same start credit as the hand-built
`strictRoundStart`: at most one reserve `n*m`, one rearm insurance `n*m`, one
full service budget `n*m*(2h-1)` and the reserved latch allowance. -/
theorem generalStrictBase_start_le (R : RFrame) (s : Round R) :
    physicalCandidatePotential R (.active (.account (.round s))) ≤
      R.n*R.m*(2*R.h+1)+R.n*(2*R.h-1) := by
  have hp : physicalCandidatePotential R (.active (.account (.round s))) =
      roundPotential R (.active s) + (R.n*R.m + R.n*R.m*(2*R.h-1)) + R.n*(2*R.h-1) := rfl
  rw [hp]
  have hr := roundPotential_le R s
  have ht := tightBudget_eq R
  omega

/-- **General strict-base end-to-end budget.** The imported capstone
`physicalCandidate_truncatedCost_le` is the special case `s = strictRoundStart`. -/
theorem generalStrictBase_truncatedCost_le (R : RFrame) (s : Round R) (T : Nat) :
    truncatedActiveCostNumerator (physicalCandidateStep R) (.active (.account (.round s))) T ≤
      R.n^T*(R.n*R.m*(2*R.h+1)+R.n*(2*R.h-1)) := by
  have hb := truncatedActiveCostNumerator_mul_le_of_natSuperSolution
    (physicalCandidateStep R) 1 (physicalCandidatePotential R) (physicalCandidate_bellman R)
    (.active (.account (.round s))) T
  simp only [Nat.one_mul] at hb
  exact Nat.le_trans hb (Nat.mul_le_mul_left _ (generalStrictBase_start_le R s))

theorem strictBudget_pos (R : RFrame) : 0 < R.n*R.m*(2*R.h+1)+R.n*(2*R.h-1) := by
  have h : 0 < R.n*R.m*(2*R.h+1) := Nat.mul_pos
    (Nat.mul_pos (Nat.mul_pos (by have := R.hm; omega) R.hh) (by have := R.hm; omega)) (by omega)
  omega

/-- Reciprocal success tail from an arbitrary strict round base. -/
theorem generalStrictBase_success_one_minus_inv_factor (R : RFrame) (s : Round R) (factor : Nat) :
    (factor-1)*R.n^(factor*(R.n*R.m*(2*R.h+1)+R.n*(2*R.h-1))) ≤
      factor*successCount (physicalCandidateStep R) (.active (.account (.round s)))
        (factor*(R.n*R.m*(2*R.h+1)+R.n*(2*R.h-1))) :=
  success_tail_of_cost_bound _ _ (physicalCandidate_no_failure R) (strictBudget_pos R)
    (generalStrictBase_truncatedCost_le R s) factor

/-- Predicate form: the five strict-base conditions are exactly the two
imported structure fields, `RoundBase` (lineage, all roots entered, zero
predecessor debt, no virtual candidate) plus a remaining Race root. -/
theorem roundBase_truncatedCost_le (R : RFrame) (r : Nat) (x : GhostRing2 R)
    (hb : RoundBase R r x) (hr : PeriodHIncidenceChoice.HasRace (word2 R r x)) (T : Nat) :
    truncatedActiveCostNumerator (physicalCandidateStep R)
        (.active (.account (.round ⟨r,x,hb,hr⟩))) T ≤
      R.n^T*(R.n*R.m*(2*R.h+1)+R.n*(2*R.h-1)) :=
  generalStrictBase_truncatedCost_le R ⟨r,x,hb,hr⟩ T

theorem roundBase_success_one_minus_inv_factor (R : RFrame) (r : Nat) (x : GhostRing2 R)
    (hb : RoundBase R r x) (hr : PeriodHIncidenceChoice.HasRace (word2 R r x)) (factor : Nat) :
    (factor-1)*R.n^(factor*(R.n*R.m*(2*R.h+1)+R.n*(2*R.h-1))) ≤
      factor*successCount (physicalCandidateStep R) (.active (.account (.round ⟨r,x,hb,hr⟩)))
        (factor*(R.n*R.m*(2*R.h+1)+R.n*(2*R.h-1))) :=
  generalStrictBase_success_one_minus_inv_factor R ⟨r,x,hb,hr⟩ factor

/-- The imported capstone is recovered as one instance. -/
theorem strictStart_truncatedCost_le (R : RFrame) (T : Nat) :
    truncatedActiveCostNumerator (physicalCandidateStep R)
        (.active (physicalCandidateStart R)) T ≤
      R.n^T*(R.n*R.m*(2*R.h+1)+R.n*(2*R.h-1)) :=
  generalStrictBase_truncatedCost_le R (strictRoundStart R) T

/-! ### Preparation handoff and the composed clean start -/

/-- **Where preparation can stop.** The standalone preparation process of
`ShortGapCleanBase` exits only into a virtual candidate or into an actual
strict base, and in the latter case the exit child is literally the state of
an inhabited `Round R` at the next index. -/
theorem strictBase_reached_or_success (R : RFrame) (s : Service R) (e : Fin R.n)
    (h : ShortGapCleanBase.Uniform.preparationStep R s e = .success) :
    VirtualSuccess R s.idx (ghostStep2 R s.state (edgeVtx R e)) ∨
      ∃ t : Round R, t.idx = s.idx+1 ∧ t.state = ghostStep2 R s.state (edgeVtx R e) := by
  rcases ShortGapCleanBase.Uniform.preparation_success_sound R s e h with hv | hbr
  · exact Or.inl hv
  · exact Or.inr ⟨⟨s.idx+1,_,hbr.1,hbr.2⟩,rfl,rfl⟩

/-- No preparation state is already a strict base at the next index; the base
is reached only in the exit child. Recorded so the handoff is unambiguous. -/
theorem preparation_not_next_base (R : RFrame) (s : Service R) :
    ¬ RoundBase R (s.idx+1) s.state :=
  ShortGapCleanBase.Uniform.service_not_next_base R s

/-- **Phase-two budget at the handoff.** Whenever preparation stops without a
virtual candidate, the general strict-base certificate already applies at the
state it stops in, with the strict constant. -/
theorem preparation_handoff_truncatedCost_le (R : RFrame) (s : Service R) (e : Fin R.n)
    (h : ShortGapCleanBase.Uniform.preparationStep R s e = .success)
    (hv : ¬ VirtualSuccess R s.idx (ghostStep2 R s.state (edgeVtx R e))) (T : Nat) :
    ∃ t : Round R, t.idx = s.idx+1 ∧ t.state = ghostStep2 R s.state (edgeVtx R e) ∧
      truncatedActiveCostNumerator (physicalCandidateStep R)
          (.active (.account (.round t))) T ≤
        R.n^T*(R.n*R.m*(2*R.h+1)+R.n*(2*R.h-1)) := by
  rcases strictBase_reached_or_success R s e h with hs | ⟨t,hi,ht⟩
  · exact absurd hs hv
  · exact ⟨t,hi,ht,generalStrictBase_truncatedCost_le R t T⟩

/-- The two phase budgets add up to the imported clean-start constant. -/
theorem composed_clean_budget_eq (R : RFrame) :
    R.n*R.m*(2*R.h-1) + (R.n*R.m*(2*R.h+1)+R.n*(2*R.h-1)) =
      4*R.n*R.m*R.h+R.n*(2*R.h-1) := by
  have hsum : R.n*R.m*(2*R.h-1) + R.n*R.m*(2*R.h+1) = 4*R.n*R.m*R.h := by
    have he : (2*R.h-1)+(2*R.h+1) = 4*R.h := by have := R.hh; omega
    calc
      R.n*R.m*(2*R.h-1) + R.n*R.m*(2*R.h+1) = R.n*R.m*((2*R.h-1)+(2*R.h+1)) :=
        (Nat.mul_add _ _ _).symm
      _ = R.n*R.m*(4*R.h) := by rw [he]
      _ = 4*R.n*R.m*R.h := by ac_rfl
  omega

/-- The clean start's credit is exactly the preparation budget plus the general
strict-base budget. This is the imported credit decomposition with the
preparation budget substituted for the initial service potential. -/
theorem clean_credit_eq_preparation_add_strict (R : RFrame) :
    physicalCandidatePotential R (.active (physicalCandidateCleanStart R)) =
      R.n*R.m*(2*R.h-1) + (R.n*R.m*(2*R.h+1)+R.n*(2*R.h-1)) := by
  rw [ShortGapCleanBase.Uniform.clean_credit_decomposition R,
    ShortGapCleanBase.Uniform.preparation_initial_potential R]
  omega

/-- **Composed clean-start budget**, in the `preparation + strict` shape. -/
theorem clean_truncatedCost_le_composed (R : RFrame) (T : Nat) :
    truncatedActiveCostNumerator (physicalCandidateStep R)
        (.active (physicalCandidateCleanStart R)) T ≤
      R.n^T*(R.n*R.m*(2*R.h-1) + (R.n*R.m*(2*R.h+1)+R.n*(2*R.h-1))) := by
  have hb := truncatedActiveCostNumerator_mul_le_of_natSuperSolution
    (physicalCandidateStep R) 1 (physicalCandidatePotential R) (physicalCandidate_bellman R)
    (.active (physicalCandidateCleanStart R)) T
  simp only [Nat.one_mul,clean_credit_eq_preparation_add_strict R] at hb
  exact hb

/-- The repository's clean-start constant, now obtained by composing the
preparation budget with the general strict-base budget. -/
theorem clean_truncatedCost_le_of_composition (R : RFrame) (T : Nat) :
    truncatedActiveCostNumerator (physicalCandidateStep R)
        (.active (physicalCandidateCleanStart R)) T ≤
      R.n^T*(4*R.n*R.m*R.h+R.n*(2*R.h-1)) := by
  rw [← composed_clean_budget_eq R]
  exact clean_truncatedCost_le_composed R T

theorem cleanBudget_pos (R : RFrame) : 0 < 4*R.n*R.m*R.h+R.n*(2*R.h-1) := by
  have h : 0 < 4*R.n*R.m*R.h := Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (by decide)
    (Nat.mul_pos (by have := R.hm; omega) R.hh)) (by have := R.hm; omega)) R.hh
  omega

/-- Reciprocal success tail of the composed clean-start bound. -/
theorem clean_success_one_minus_inv_factor_of_composition (R : RFrame) (factor : Nat) :
    (factor-1)*R.n^(factor*(4*R.n*R.m*R.h+R.n*(2*R.h-1))) ≤
      factor*successCount (physicalCandidateStep R) (.active (physicalCandidateCleanStart R))
        (factor*(4*R.n*R.m*R.h+R.n*(2*R.h-1))) :=
  success_tail_of_cost_bound _ _ (physicalCandidate_no_failure R) (cleanBudget_pos R)
    (clean_truncatedCost_le_of_composition R) factor

end Uniform

/-! ## Variable-length lane -/

namespace Variable
open ShortGapLiteralGapRows ShortGapGhostVarLength

/-- Every strict round base of the variable-length lane carries the same start
credit as `strictRoundStart`. -/
theorem generalStrictBase_start_le (R : VFrame) (s : Round R) :
    physicalCandidatePotential R (.active (.account (.round s))) ≤
      R.n*R.m+2*R.n*R.n+R.n*(2*hMax R-1) := by
  have hp : physicalCandidatePotential R (.active (.account (.round s))) =
      roundPotential R (.active s) + (R.n*R.m + R.n*(2*R.n-R.m)) + R.n*(2*hMax R-1) := rfl
  rw [hp]
  have hr := roundPotential_le R s
  have ht := tightBudget_eq R
  omega

/-- **General strict-base end-to-end budget, variable gap lengths.** -/
theorem generalStrictBase_truncatedCost_le (R : VFrame) (s : Round R) (T : Nat) :
    truncatedActiveCostNumerator (physicalCandidateStep R) (.active (.account (.round s))) T ≤
      R.n^T*(R.n*R.m+2*R.n*R.n+R.n*(2*hMax R-1)) := by
  have hb := truncatedActiveCostNumerator_mul_le_of_natSuperSolution
    (physicalCandidateStep R) 1 (physicalCandidatePotential R) (physicalCandidate_bellman R)
    (.active (.account (.round s))) T
  simp only [Nat.one_mul] at hb
  exact Nat.le_trans hb (Nat.mul_le_mul_left _ (generalStrictBase_start_le R s))

theorem strictBudget_pos (R : VFrame) : 0 < R.n*R.m+2*R.n*R.n+R.n*(2*hMax R-1) := by
  have h : 0 < R.n*R.m := Nat.mul_pos (n_pos R) (by have := R.hm; omega)
  omega

/-- Reciprocal success tail from an arbitrary variable-length strict base. -/
theorem generalStrictBase_success_one_minus_inv_factor (R : VFrame) (s : Round R) (factor : Nat) :
    (factor-1)*R.n^(factor*(R.n*R.m+2*R.n*R.n+R.n*(2*hMax R-1))) ≤
      factor*successCount (physicalCandidateStep R) (.active (.account (.round s)))
        (factor*(R.n*R.m+2*R.n*R.n+R.n*(2*hMax R-1))) :=
  success_tail_of_cost_bound _ _ (physicalCandidate_no_failure R) (strictBudget_pos R)
    (generalStrictBase_truncatedCost_le R s) factor

theorem roundBase_truncatedCost_le (R : VFrame) (r : Nat) (x : GhostRing2 R)
    (hb : RoundBase R r x) (hr : PeriodHIncidenceChoice.HasRace (word2 R r x)) (T : Nat) :
    truncatedActiveCostNumerator (physicalCandidateStep R)
        (.active (.account (.round ⟨r,x,hb,hr⟩))) T ≤
      R.n^T*(R.n*R.m+2*R.n*R.n+R.n*(2*hMax R-1)) :=
  generalStrictBase_truncatedCost_le R ⟨r,x,hb,hr⟩ T

theorem roundBase_success_one_minus_inv_factor (R : VFrame) (r : Nat) (x : GhostRing2 R)
    (hb : RoundBase R r x) (hr : PeriodHIncidenceChoice.HasRace (word2 R r x)) (factor : Nat) :
    (factor-1)*R.n^(factor*(R.n*R.m+2*R.n*R.n+R.n*(2*hMax R-1))) ≤
      factor*successCount (physicalCandidateStep R) (.active (.account (.round ⟨r,x,hb,hr⟩)))
        (factor*(R.n*R.m+2*R.n*R.n+R.n*(2*hMax R-1))) :=
  generalStrictBase_success_one_minus_inv_factor R ⟨r,x,hb,hr⟩ factor

theorem strictStart_truncatedCost_le (R : VFrame) (T : Nat) :
    truncatedActiveCostNumerator (physicalCandidateStep R)
        (.active (physicalCandidateStart R)) T ≤
      R.n^T*(R.n*R.m+2*R.n*R.n+R.n*(2*hMax R-1)) :=
  generalStrictBase_truncatedCost_le R (strictRoundStart R) T

/-! ### Preparation handoff and the composed clean start -/

theorem strictBase_reached_or_success (R : VFrame) (s : Service R) (e : Fin R.n)
    (h : ShortGapCleanBase.Variable.preparationStep R s e = .success) :
    VirtualSuccess R s.idx (ghostStep2 R s.state (edgeVtx R e)) ∨
      ∃ t : Round R, t.idx = s.idx+1 ∧ t.state = ghostStep2 R s.state (edgeVtx R e) := by
  rcases ShortGapCleanBase.Variable.preparation_success_sound R s e h with hv | hbr
  · exact Or.inl hv
  · exact Or.inr ⟨⟨s.idx+1,_,hbr.1,hbr.2⟩,rfl,rfl⟩

theorem preparation_not_next_base (R : VFrame) (s : Service R) :
    ¬ RoundBase R (s.idx+1) s.state :=
  ShortGapCleanBase.Variable.service_not_next_base R s

theorem preparation_handoff_truncatedCost_le (R : VFrame) (s : Service R) (e : Fin R.n)
    (h : ShortGapCleanBase.Variable.preparationStep R s e = .success)
    (hv : ¬ VirtualSuccess R s.idx (ghostStep2 R s.state (edgeVtx R e))) (T : Nat) :
    ∃ t : Round R, t.idx = s.idx+1 ∧ t.state = ghostStep2 R s.state (edgeVtx R e) ∧
      truncatedActiveCostNumerator (physicalCandidateStep R)
          (.active (.account (.round t))) T ≤
        R.n^T*(R.n*R.m+2*R.n*R.n+R.n*(2*hMax R-1)) := by
  rcases strictBase_reached_or_success R s e h with hs | ⟨t,hi,ht⟩
  · exact absurd hs hv
  · exact ⟨t,hi,ht,generalStrictBase_truncatedCost_le R t T⟩

/-- The variable-length phase budgets add up to the imported clean constant. -/
theorem composed_clean_budget_eq (R : VFrame) :
    R.n*(2*R.n-R.m) + (R.n*R.m+2*R.n*R.n+R.n*(2*hMax R-1)) =
      4*R.n*R.n+R.n*(2*hMax R-1) := by
  have h := reserve_service_eq R
  have h4 : 4*R.n*R.n = 2*R.n*R.n + 2*R.n*R.n := by rw [← Nat.add_mul,← Nat.add_mul]
  omega

theorem clean_credit_eq_preparation_add_strict (R : VFrame) :
    physicalCandidatePotential R (.active (physicalCandidateCleanStart R)) =
      R.n*(2*R.n-R.m) + (R.n*R.m+2*R.n*R.n+R.n*(2*hMax R-1)) := by
  rw [ShortGapCleanBase.Variable.clean_credit_decomposition R,
    ShortGapCleanBase.Variable.preparation_initial_potential R]
  omega

theorem clean_truncatedCost_le_composed (R : VFrame) (T : Nat) :
    truncatedActiveCostNumerator (physicalCandidateStep R)
        (.active (physicalCandidateCleanStart R)) T ≤
      R.n^T*(R.n*(2*R.n-R.m) + (R.n*R.m+2*R.n*R.n+R.n*(2*hMax R-1))) := by
  have hb := truncatedActiveCostNumerator_mul_le_of_natSuperSolution
    (physicalCandidateStep R) 1 (physicalCandidatePotential R) (physicalCandidate_bellman R)
    (.active (physicalCandidateCleanStart R)) T
  simp only [Nat.one_mul,clean_credit_eq_preparation_add_strict R] at hb
  exact hb

theorem clean_truncatedCost_le_of_composition (R : VFrame) (T : Nat) :
    truncatedActiveCostNumerator (physicalCandidateStep R)
        (.active (physicalCandidateCleanStart R)) T ≤
      R.n^T*(4*R.n*R.n+R.n*(2*hMax R-1)) := by
  rw [← composed_clean_budget_eq R]
  exact clean_truncatedCost_le_composed R T

theorem cleanBudget_pos (R : VFrame) : 0 < 4*R.n*R.n+R.n*(2*hMax R-1) := by
  have h : 0 < 4*R.n*R.n := Nat.mul_pos (Nat.mul_pos (by decide) (n_pos R)) (n_pos R)
  omega

theorem clean_success_one_minus_inv_factor_of_composition (R : VFrame) (factor : Nat) :
    (factor-1)*R.n^(factor*(4*R.n*R.n+R.n*(2*hMax R-1))) ≤
      factor*successCount (physicalCandidateStep R) (.active (physicalCandidateCleanStart R))
        (factor*(4*R.n*R.n+R.n*(2*hMax R-1))) :=
  success_tail_of_cost_bound _ _ (physicalCandidate_no_failure R) (cleanBudget_pos R)
    (clean_truncatedCost_le_of_composition R) factor

end Variable

/-! ## The checked small instance

For `m = 2`, `h = 1` (so `n = 2`) the strict all-Race base is reached from the
actual clean start `ghostStart2` in two interactions. This is a witness for one
instance only; general reachability of the strict base from the clean start
remains open. -/

namespace SmallCase
open ShortGapLiteralGapRows ShortGapLiteralRingRows ShortGapTwoEpoch
open ShortGapLineage2Closure ShortGapGhostComposition2

def F : RFrame := ⟨2,1,by decide,by decide,.out1,Or.inl rfl⟩

theorem F_n : F.n = 2 := by decide

def v0 : Vtx F := (⟨0,by decide⟩,⟨0,by decide⟩)
def v1 : Vtx F := (⟨1,by decide⟩,⟨0,by decide⟩)

/-- Two interactions of the actual clean start. -/
def reachedStrict : GhostRing2 F := ghostStep2 F (ghostStep2 F (ghostStart2 F) v0) v1

theorem reachedStrict_cfg_eq : reachedStrict.cfg = (strictStart F).cfg := by
  funext v
  obtain ⟨g,a⟩ := v
  revert g a
  decide

theorem reachedStrict_k_eq : reachedStrict.k = (strictStart F).k := by
  funext g
  revert g
  decide

theorem reachedStrict_epoch_eq : reachedStrict.epoch = (strictStart F).epoch := by
  funext g
  revert g
  decide

/-- The whole history function agrees, not merely a bounded prefix: both are
`some R.b` at generation 0 and `none` at every later generation. -/
theorem reachedStrict_hist_eq : reachedStrict.hist = (strictStart F).hist := by
  funext g q
  match q, g with
  | 0, ⟨0,_⟩ => rfl
  | 0, ⟨1,_⟩ => rfl
  | 1, ⟨0,_⟩ => rfl
  | 1, ⟨1,_⟩ => rfl
  | (q+2), ⟨0,_⟩ => rfl
  | (q+2), ⟨1,_⟩ => rfl

/-- **The strict base is literally reached in two interactions** in this
instance: not only the physical configuration, but every ghost field
(generations, epochs, full history) equals the hand-built `strictStart F`. -/
theorem strictStart_reached_in_two_interactions : reachedStrict = strictStart F := by
  have h : (GhostRing2.mk reachedStrict.cfg reachedStrict.k reachedStrict.hist
      reachedStrict.epoch : GhostRing2 F) = strictStart F := by
    rw [reachedStrict_cfg_eq,reachedStrict_k_eq,reachedStrict_hist_eq,reachedStrict_epoch_eq]
  exact h

/-- Consequently the hand-built strict start of this instance is reachable from
the actual clean start, by the two-letter scheduler word `[v0,v1]`. -/
theorem strictStart_reachable : Reachable2 F (strictStart F) :=
  ⟨[v0,v1],strictStart_reached_in_two_interactions⟩

/-- The same statement about the state carried by the index-carrying round
base that the imported capstone starts from. -/
theorem strictRoundStart_state_reachable : Reachable2 F (strictRoundStart F).state :=
  strictStart_reachable

/-- The three budgets of this instance, and the numeric composition
`preparation + strict = clean` behind `composed_clean_budget_eq`. -/
theorem smallCase_budgets :
    F.n*F.m*(2*F.h+1)+F.n*(2*F.h-1) = 14 ∧
      4*F.n*F.m*F.h+F.n*(2*F.h-1) = 18 ∧
        F.n*F.m*(2*F.h-1) = 4 ∧ 4 + 14 = 18 := by decide

end SmallCase

#print axioms Uniform.generalStrictBase_start_le
#print axioms Uniform.generalStrictBase_truncatedCost_le
#print axioms Uniform.generalStrictBase_success_one_minus_inv_factor
#print axioms Uniform.roundBase_truncatedCost_le
#print axioms Uniform.roundBase_success_one_minus_inv_factor
#print axioms Uniform.strictStart_truncatedCost_le
#print axioms Uniform.strictBase_reached_or_success
#print axioms Uniform.preparation_not_next_base
#print axioms Uniform.preparation_handoff_truncatedCost_le
#print axioms Uniform.composed_clean_budget_eq
#print axioms Uniform.clean_credit_eq_preparation_add_strict
#print axioms Uniform.clean_truncatedCost_le_composed
#print axioms Uniform.clean_truncatedCost_le_of_composition
#print axioms Uniform.clean_success_one_minus_inv_factor_of_composition
#print axioms Variable.generalStrictBase_start_le
#print axioms Variable.generalStrictBase_truncatedCost_le
#print axioms Variable.generalStrictBase_success_one_minus_inv_factor
#print axioms Variable.roundBase_truncatedCost_le
#print axioms Variable.roundBase_success_one_minus_inv_factor
#print axioms Variable.strictStart_truncatedCost_le
#print axioms Variable.strictBase_reached_or_success
#print axioms Variable.preparation_not_next_base
#print axioms Variable.preparation_handoff_truncatedCost_le
#print axioms Variable.composed_clean_budget_eq
#print axioms Variable.clean_credit_eq_preparation_add_strict
#print axioms Variable.clean_truncatedCost_le_composed
#print axioms Variable.clean_truncatedCost_le_of_composition
#print axioms Variable.clean_success_one_minus_inv_factor_of_composition
#print axioms SmallCase.strictStart_reached_in_two_interactions
#print axioms SmallCase.strictStart_reachable
#print axioms SmallCase.strictRoundStart_state_reachable
#print axioms SmallCase.smallCase_budgets

end ShortGapStrictBaseGeneral
