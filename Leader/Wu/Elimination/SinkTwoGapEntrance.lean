import Leader.Wu.Elimination.SinkTwoGapNoResetKernel
import Leader.Core.PredictableSerialRace

namespace LDSinkTwoGapEntrance

open LDSinkTwoGapNoResetKernel PredictableRenewalOverlap
open LDSinkGapCleanup LDTwoGapFrame PPLLRepair
open FiniteUniformStoppingTree
open Classical

set_option autoImplicit false

variable {n ψ : Nat}

/-- The physical entrance required by the checked serial race: the tagged
live shot is parked immediately to the right of j, and j's recovery gap has
returned to CleanReady. -/
def RaceReady (F : TwoGapFrame n) (C : Fin n → AgentState ψ) : Prop :=
  (C (F.attack.pos 1)).bullet = (2 : Fin 3) ∧
  CleanReady F.recovery C

/-- Either the serial-race entrance is reached, or one of the tagged three
leaders has already disappeared. -/
def EntranceSuccess (F : TwoGapFrame n)
    (C : Fin n → AgentState ψ) : Prop :=
  RaceReady F C ∨ NoResetSuccess F C

/-- Turn the inner Attempt2 absorption terminal back into an active successor.
The fallback is the same post-configuration/phase update used by Attempt2's
ordinary active branch. -/
def reactivateFailure {S : Type} (fallback : S) : StopNode S → StopNode S
  | .failure => .active fallback
  | z => z

/-- Attempt2's physical raw step, retargeted to the larger success predicate.
NoResetSuccess is still success.  RaceReady is added as success.  Absorption is no
longer terminal failure: it continues from `advanceAState F x C'`. -/
noncomputable def entranceStep (hψ : ψ > 0) (F : TwoGapFrame n)
    (x : AState n ψ) (e : Fin n) : StopNode (AState n ψ) := by
  classical
  let C' := attemptStepConf hψ F x e
  exact
    if EntranceSuccess F C' then .success
    else
      reactivateFailure (advanceAState F x C')
        (attemptStepRaw hψ F x e)

theorem entranceStep_eq_success_iff (hψ : ψ > 0) (F : TwoGapFrame n)
    (x : AState n ψ) (e : Fin n) :
    entranceStep hψ F x e = .success ↔
      EntranceSuccess F (attemptStepConf hψ F x e) := by
  classical
  by_cases hE : EntranceSuccess F (attemptStepConf hψ F x e)
  · simp [entranceStep, hE]
  · have hS : ¬ NoResetSuccess F (attemptStepConf hψ F x e) := by
      intro hs
      exact hE (Or.inr hs)
    simp [entranceStep, hE, reactivateFailure, attemptStepRaw, hS]
    split <;> simp_all [reactivateFailure]

theorem entranceStep_ne_failure (hψ : ψ > 0) (F : TwoGapFrame n)
    (x : AState n ψ) (e : Fin n) :
    entranceStep hψ F x e ≠ .failure := by
  classical
  by_cases hE : EntranceSuccess F (attemptStepConf hψ F x e)
  · simp [entranceStep, hE]
  · have hS : ¬ NoResetSuccess F (attemptStepConf hψ F x e) := by
      intro hs
      exact hE (Or.inr hs)
    simp [entranceStep, hE, reactivateFailure, attemptStepRaw, hS]
    split <;> simp_all [reactivateFailure]

/-- Candidate Bellman potential inherited from Attempt2.  On an active node it
is `n * R`; both stopped outcomes have value zero. -/
noncomputable def entrancePotential (F : TwoGapFrame n) : StopNode (AState n ψ) → Nat
  | .active x => n * R F x
  | .success => 0
  | .failure => 0

/-- The one genuinely new entrance obligation.  Attempt2's checked laws do not
supply this automatically because an absorption child was `.failure` there but
is `.active` here.  Proving this amounts to proving the reset/absorption child
is prepaid by the current rank. -/
def EntranceBellman (hψ : ψ > 0) (F : TwoGapFrame n) : Prop :=
  NatBellmanSuperSolution (entranceStep hψ F) 1 (entrancePotential F)

/-- Under the single new Bellman seam, the Attempt2 rank bound immediately
transfers to the entrance process. -/
theorem entrance_truncatedCost_le
    (hψ : ψ > 0) (F : TwoGapFrame n)
    (hSuper : EntranceBellman hψ F)
    (x : AState n ψ)
    (hrec : GapInvariant hψ F.recovery x.conf)
    (hatt : GapInvariant hψ F.attack x.conf)
    (T : Nat) :
    truncatedActiveCostNumerator (entranceStep hψ F) (.active x) T ≤
      n ^ T * (16 * n * (F.recovery.d + F.attack.d)) := by
  have hc :=
    truncatedActiveCostNumerator_mul_le_of_natSuperSolution
      (entranceStep hψ F) 1 (entrancePotential F) hSuper (.active x) T
  have hr := R_le hψ F x hrec hatt
  have hp : entrancePotential F (.active x) ≤
      16 * n * (F.recovery.d + F.attack.d) := by
    change n * R F x ≤ 16 * n * (F.recovery.d + F.attack.d)
    calc
      n * R F x ≤ n * (16 * (F.recovery.d + F.attack.d)) :=
        Nat.mul_le_mul_left n hr
      _ = 16 * n * (F.recovery.d + F.attack.d) := by
        ac_rfl
  calc
    truncatedActiveCostNumerator (entranceStep hψ F) (.active x) T ≤
        n ^ T * entrancePotential F (.active x) := by
      simpa using hc
    _ ≤ n ^ T * (16 * n * (F.recovery.d + F.attack.d)) :=
      Nat.mul_le_mul_left (n ^ T) hp

/-- Every successful depth-T word has all n one-edge extensions successful. -/
private theorem n_mul_successCount_le_succ
    {S : Type} {n : Nat} (step : S → Fin n → StopNode S) :
    ∀ x T,
      n * successCount step x T ≤ successCount step x (T + 1) := by
  intro x T
  induction T generalizing x with
  | zero =>
      cases x with
      | active s =>
          change 0 ≤ successCount step (.active s) 1
          exact Nat.zero_le _
      | failure =>
          change 0 ≤ successCount step (.failure : StopNode S) 1
          exact Nat.zero_le _
      | success =>
          simp only [successCount, treeWeight, successWeight, stepNode,
            Nat.mul_one]
          rw [FiniteUniformStoppingTree.ofFn_sum_const]
          simp
  | succ T ih =>
      change
        n *
            (List.ofFn (fun e : Fin n =>
              treeWeight step successWeight (stepNode step x e) T)).sum ≤
          (List.ofFn (fun e : Fin n =>
            treeWeight step successWeight (stepNode step x e) (T + 1))).sum
      rw [← ofFn_sum_mul_left]
      apply ofFn_sum_le
      intro e
      simpa only [successCount] using ih (stepNode step x e)

/-- Success mass at horizon U can be extended through T further raw choices. -/
private theorem pow_mul_successCount_le_add
    {S : Type} {n : Nat} (step : S → Fin n → StopNode S) :
    ∀ x U T,
      n ^ T * successCount step x U ≤ successCount step x (U + T) := by
  intro x U T
  induction T with
  | zero => simp
  | succ T ih =>
      calc
        n ^ (T + 1) * successCount step x U =
            n * (n ^ T * successCount step x U) := by
          rw [Nat.pow_succ]
          ac_rfl
        _ ≤ n * successCount step x (U + T) :=
          Nat.mul_le_mul_left n ih
        _ ≤ successCount step x ((U + T) + 1) :=
          n_mul_successCount_le_succ step x (U + T)
        _ = successCount step x (U + (T + 1)) := by
          rw [Nat.add_assoc]

/-- Reciprocal-tail bound at the exact Bellman horizon `2 * potential`. -/
theorem entrance_success_half_at_rank
    (hψ : ψ > 0) (F : TwoGapFrame n)
    (hSuper : EntranceBellman hψ F)
    (x : AState n ψ) :
    n ^ (2 * entrancePotential F (.active x)) ≤
      2 * successCount (entranceStep hψ F) (.active x)
        (2 * entrancePotential F (.active x)) := by
  have hn : 0 < n := by
    have h := (F.attack.pos 0).isLt
    omega
  have hp : 0 < entrancePotential F (.active x) := by
    change 0 < n * R F x
    exact Nat.mul_pos hn (R_pos F x)
  have h :=
    BalancedFailureRestart.pred_mul_pow_le_factor_mul_successCount
      (factor := 2)
      (entranceStep hψ F) (entrancePotential F) hSuper
      (fun state edge => entranceStep_ne_failure hψ F state edge) x hp
  simpa using h

/-- Fixed-horizon form requested by the entrance reduction.  The exact
reciprocal-tail horizon is at most `32*n*(a+b)` by `R_le`; absorbing success
mass is then extended to the larger uniform horizon. -/
theorem entrance_success_half
    (hψ : ψ > 0) (F : TwoGapFrame n)
    (hSuper : EntranceBellman hψ F)
    (x : AState n ψ)
    (hrec : GapInvariant hψ F.recovery x.conf)
    (hatt : GapInvariant hψ F.attack x.conf) :
    n ^ (32 * n * (F.recovery.d + F.attack.d)) ≤
      2 * successCount (entranceStep hψ F) (.active x)
        (32 * n * (F.recovery.d + F.attack.d)) := by
  let H := 32 * n * (F.recovery.d + F.attack.d)
  let h0 := 2 * entrancePotential F (.active x)
  change n ^ H ≤ 2 * successCount (entranceStep hψ F) (.active x) H
  have hr := R_le hψ F x hrec hatt
  have hh : h0 ≤ H := by
    dsimp [h0, H, entrancePotential]
    calc
      2 * (n * R F x) ≤
          2 * (n * (16 * (F.recovery.d + F.attack.d))) :=
        Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left n hr)
      _ = 32 * n * (F.recovery.d + F.attack.d) := by
        simp [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
  have hhalf :
      n ^ h0 ≤
        2 * successCount (entranceStep hψ F) (.active x) h0 := by
    dsimp [h0]
    exact entrance_success_half_at_rank hψ F hSuper x
  let K := H - h0
  have hsum : h0 + K = H := by
    dsimp [K]
    omega
  have hsum' : K + h0 = H := by
    omega
  have hext := pow_mul_successCount_le_add
    (entranceStep hψ F) (.active x) h0 K
  calc
    n ^ H = n ^ K * n ^ h0 := by
      rw [← Nat.pow_add, hsum']
    _ ≤ n ^ K *
        (2 * successCount (entranceStep hψ F) (.active x) h0) :=
      Nat.mul_le_mul_left (n ^ K) hhalf
    _ = 2 *
        (n ^ K * successCount (entranceStep hψ F) (.active x) h0) := by
      ac_rfl
    _ ≤ 2 * successCount (entranceStep hψ F) (.active x) (h0 + K) :=
      Nat.mul_le_mul_left 2 hext
    _ = 2 * successCount (entranceStep hψ F) (.active x) H := by
      rw [hsum]

/-!
The next desired theorem is intentionally not stated as a Lean theorem here:
`entrance_then_serial_mass` needs an exported projection from a physical
`RaceReady F C` configuration to the abstract `SerialRaceState.first` payload,
plus a simulation showing the physical continuation refines `serialRaceStep`.
Those data are not present in the pasted Attempt2/serial-race interfaces.
-/

#print axioms entranceStep_eq_success_iff
#print axioms entranceStep_ne_failure
#print axioms entrance_truncatedCost_le
#print axioms entrance_success_half_at_rank
#print axioms entrance_success_half

end LDSinkTwoGapEntrance
