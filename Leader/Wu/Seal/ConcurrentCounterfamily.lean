import Leader.Wu.Seal.WeakFairConcurrencyNoGo
import Leader.Wu.Seal.MacroConcurrentCounterfamily

/-!
# Exact-carrier concurrent counterfamily for the seal sweep

The four macro states of `SealSweepConcurrentCounterfamilySol` are realized
inside the accepted factor-four `P_partial` carrier at `psi = 2`.  The two
physical representatives are the closed leader and follower states already
used by the six-site overlay counterexample; changing only the outer seal bit
gives their unsealed versions.

The resulting embedding commutes with the exact ordered-pair transition and
therefore lifts the macro counterfamily at every even size `2 * m >= 4`.
The lifted initial configuration is all closed.  Its explicit periodic
execution uses every directed edge infinitely often, retains two output
leaders at every time, and never satisfies `PopulationProtocol.IsSafe`.
-/

namespace PPLLCompleteMultiLeaderCleanup
namespace PPartialSealSweepConcurrentCounterfamilySol

open PPLL PPLLResearchFormulation
open PPLLStaticDoubleCoverNoGo
open PPartialSealSweepOverlaySol
open PPartialSealSweepConcurrencyNoGoSol
open SealSweepConcurrentCycleSol
open SealSweepConcurrentCycleSol.SealMacroState
open SealSweepConcurrentCounterfamilySol

/-! ## A transition-preserving realization of the four macro states -/

/-- The closed leader representative from the exact factor-four carrier. -/
def exactLS (kappa tau : Nat) :
    SealSweepState OverlayNoGoPsi kappa tau :=
  overlaySeparatedLeaderState kappa tau

/-- The closed follower representative from the exact factor-four carrier. -/
def exactFS (kappa tau : Nat) :
    SealSweepState OverlayNoGoPsi kappa tau :=
  overlaySeparatedFollowerState kappa tau

/-- The same physical leader with its outer seal bit open. -/
def exactLU (kappa tau : Nat) :
    SealSweepState OverlayNoGoPsi kappa tau :=
  ((overlaySeparatedLeaderState kappa tau).1, false)

/-- The same physical follower with its outer seal bit open. -/
def exactFU (kappa tau : Nat) :
    SealSweepState OverlayNoGoPsi kappa tau :=
  ((overlaySeparatedFollowerState kappa tau).1, false)

/-- Embed the abstract leader/follower and sealed/unsealed modes into the
exact `P_partialSealSweepProtocol` carrier. -/
def embedSealMacro (kappa tau : Nat) :
    SealMacroState → SealSweepState OverlayNoGoPsi kappa tau
  | LS => exactLS kappa tau
  | FS => exactFS kappa tau
  | LU => exactLU kappa tau
  | FU => exactFU kappa tau

/-- The carrier embedding preserves the output leader predicate. -/
theorem embedSealMacro_output (kappa tau : Nat) (q : SealMacroState) :
    isLeaderOutput
        ((P_partialSealSweepProtocol OverlayNoGoPsi kappa tau).output
          (embedSealMacro kappa tau q)) =
      sealMacroOutput q := by
  cases q <;> rfl

/-- The outer exact-carrier bit is precisely the macro sealed predicate. -/
theorem embedSealMacro_closed (kappa tau : Nat) (q : SealMacroState) :
    (embedSealMacro kappa tau q).2 = sealMacroSealed q := by
  cases q <;> rfl

/-- On the four representatives, the exact factor-four transition is exactly
the audited macro rule, including physical leader clearing at collisions. -/
theorem embedSealMacro_transition (kappa tau : Nat)
    (l r : SealMacroState) :
    P_partialSealSweep (embedSealMacro kappa tau l)
        (embedSealMacro kappa tau r) =
      (embedSealMacro kappa tau (sealMacroTransition l r).1,
        embedSealMacro kappa tau (sealMacroTransition l r).2) := by
  cases l <;> cases r <;> rfl

/-! ## Configuration and schedule transport -/

/-- Pointwise lift of a macro configuration to the exact protocol carrier. -/
def liftMacroConfig (kappa tau : Nat) {n : Nat}
    (C : Fin n → SealMacroState) :
    Fin n → SealSweepState OverlayNoGoPsi kappa tau :=
  fun i => embedSealMacro kappa tau (C i)

/-- One exact protocol step commutes with pointwise lifting. -/
theorem liftMacroConfig_step (kappa tau : Nat) {n : Nat}
    (ring : DirectedRing n) (C : Fin n → SealMacroState)
    (e : Fin n) :
    (P_partialSealSweepProtocol OverlayNoGoPsi kappa tau).step ring
        (liftMacroConfig kappa tau C) e =
      liftMacroConfig kappa tau
        (sealMacroProtocol.step ring C e) := by
  funext i
  simp only [PopulationProtocol.step, P_partialSealSweepProtocol,
    sealMacroProtocol, liftMacroConfig]
  rw [embedSealMacro_transition]
  by_cases hie : i = e
  · simp [hie]
  · by_cases hir : i = ring.rightNeighbor e
    · have hne : ring.rightNeighbor e ≠ e := by
        intro h
        exact hie (hir.trans h)
      simp [hir, hne]
    · simp [hie, hir]

/-- Any finite macro schedule commutes with the exact-carrier lift. -/
theorem liftMacroConfig_runSchedule (kappa tau : Nat) {n : Nat}
    (ring : DirectedRing n) (C : Fin n → SealMacroState)
    (word : List (Fin n)) :
    runSchedule (P_partialSealSweepProtocol OverlayNoGoPsi kappa tau) ring
        (liftMacroConfig kappa tau C) word =
      liftMacroConfig kappa tau
        (runSchedule sealMacroProtocol ring C word) := by
  induction word generalizing C with
  | nil => rfl
  | cons e rest ih =>
      simp only [runSchedule]
      rw [liftMacroConfig_step]
      exact ih (sealMacroProtocol.step ring C e)

/-- Macro all-sealed configurations lift to literal all-closed exact states. -/
theorem liftMacroConfig_allClosed (kappa tau m : Nat)
    {C : EvenSealConfig m} (hclosed : EvenAllSealed m C) :
    SealSweepAllClosed (liftMacroConfig kappa tau C) := by
  intro i
  change (embedSealMacro kappa tau (C i)).2 = true
  rw [embedSealMacro_closed]
  exact hclosed i

/-- Two macro leaders lift to two distinct exact output leaders. -/
theorem liftMacroConfig_hasTwo (kappa tau m : Nat)
    {C : EvenSealConfig m} (htwo : EvenHasTwoLeaders m C) :
    HasTwoLeaderOutputs
      (P_partialSealSweepProtocol OverlayNoGoPsi kappa tau)
      isLeaderOutput (liftMacroConfig kappa tau C) := by
  obtain ⟨i, j, hij, hi, hj⟩ := htwo
  refine ⟨i, j, hij, ?_, ?_⟩
  · change isLeaderOutput
      ((P_partialSealSweepProtocol OverlayNoGoPsi kappa tau).output
        (embedSealMacro kappa tau (C i))) = true
    rw [embedSealMacro_output]
    exact hi
  · change isLeaderOutput
      ((P_partialSealSweepProtocol OverlayNoGoPsi kappa tau).output
        (embedSealMacro kappa tau (C j))) = true
    rw [embedSealMacro_output]
    exact hj

/-- Two exact output leaders already contradict the uniqueness conjunct of
semantic safety. -/
theorem liftMacroConfig_not_isSafe (kappa tau m : Nat) (hm : 0 < m)
    {C : EvenSealConfig m} (htwo : EvenHasTwoLeaders m C) :
    ¬ PopulationProtocol.IsSafe
      (P_partialSealSweepProtocol OverlayNoGoPsi kappa tau)
      (evenRing m hm) (liftMacroConfig kappa tau C) isLeaderOutput := by
  intro hsafe
  exact (hasTwoLeaders_not_unique
    (P_partialSealSweepProtocol OverlayNoGoPsi kappa tau)
    isLeaderOutput (liftMacroConfig_hasTwo kappa tau m htwo)) hsafe.1

/-! ## The exact all-closed periodic counterexecution -/

/-- Exact all-closed alternating source at size `2 * m`. -/
def exactAlternatingClosed (m kappa tau : Nat) :
    (P_partialSealSweepProtocol OverlayNoGoPsi kappa tau).Configuration
      (2 * m) :=
  liftMacroConfig kappa tau (alternatingSealed m)

/-- The source is the explicit alternating word of the two closed physical
representatives: exact leaders at even sites and exact followers at odd sites. -/
theorem exactAlternatingClosed_pointwise
    (m kappa tau : Nat) (i : Fin (2 * m)) :
    exactAlternatingClosed m kappa tau i =
      if i.val % 2 = 0 then exactLS kappa tau else exactFS kappa tau := by
  rw [exactAlternatingClosed, liftMacroConfig,
    alternatingSealed_pointwise]
  by_cases h : i.val % 2 = 0
  · simp [h, embedSealMacro, exactLS]
    rfl
  · simp [h, embedSealMacro, exactFS]
    rfl

/-- Pointwise exact-carrier image of the macro periodic execution. -/
def exactPeriodicExecution (m : Nat) (hm : 0 < m)
    (kappa tau t : Nat) :
    (P_partialSealSweepProtocol OverlayNoGoPsi kappa tau).Configuration
      (2 * m) :=
  liftMacroConfig kappa tau (evenPeriodicExecution m hm t)

theorem exactAlternatingClosed_allClosed
    (m kappa tau : Nat) :
    SealSweepAllClosed (exactAlternatingClosed m kappa tau) := by
  exact liftMacroConfig_allClosed kappa tau m
    (alternatingSealed_allSealed m)

theorem exactPeriodicExecution_initial
    (m : Nat) (hm : 0 < m) (kappa tau : Nat) :
    exactPeriodicExecution m hm kappa tau 0 =
      exactAlternatingClosed m kappa tau := by
  exact congrArg (liftMacroConfig kappa tau)
    (evenPeriodicExecution_initial m hm)

/-- Every scheduled interaction is an exact step of
`P_partialSealSweepProtocol`, not merely a macro-level transition. -/
theorem exactPeriodicExecution_step
    (m : Nat) (hm : 0 < m) (kappa tau t : Nat) :
    (P_partialSealSweepProtocol OverlayNoGoPsi kappa tau).step
        (evenRing m hm) (exactPeriodicExecution m hm kappa tau t)
        (evenPeriodicSchedule m hm t) =
      exactPeriodicExecution m hm kappa tau (t + 1) := by
  change (P_partialSealSweepProtocol OverlayNoGoPsi kappa tau).step
      (evenRing m hm)
      (liftMacroConfig kappa tau (evenPeriodicExecution m hm t))
      (evenPeriodicSchedule m hm t) =
    liftMacroConfig kappa tau (evenPeriodicExecution m hm (t + 1))
  calc
    _ = liftMacroConfig kappa tau
        (sealMacroProtocol.step (evenRing m hm)
          (evenPeriodicExecution m hm t)
          (evenPeriodicSchedule m hm t)) :=
      liftMacroConfig_step kappa tau (evenRing m hm)
        (evenPeriodicExecution m hm t) (evenPeriodicSchedule m hm t)
    _ = _ := congrArg (liftMacroConfig kappa tau)
      (evenPeriodicExecution_step m hm t)

/-- The exact execution has period `2 * m`. -/
theorem exactPeriodicExecution_periodic
    (m : Nat) (hm : 0 < m) (kappa tau t : Nat) :
    exactPeriodicExecution m hm kappa tau (t + 2 * m) =
      exactPeriodicExecution m hm kappa tau t := by
  exact congrArg (liftMacroConfig kappa tau)
    (evenPeriodicExecution_periodic m hm t)

/-- Every point of the exact execution has two distinct output leaders. -/
theorem exactPeriodicExecution_hasTwo
    (m : Nat) (hm : 2 ≤ m) (kappa tau t : Nat) :
    HasTwoLeaderOutputs
      (P_partialSealSweepProtocol OverlayNoGoPsi kappa tau)
      isLeaderOutput
      (exactPeriodicExecution m (by omega) kappa tau t) := by
  exact liftMacroConfig_hasTwo kappa tau m
    (evenPeriodicExecution_hasTwo m hm t)

/-- Hence no point of this exact execution is semantically safe. -/
theorem exactPeriodicExecution_not_isSafe
    (m : Nat) (hm : 2 ≤ m) (kappa tau t : Nat) :
    ¬ PopulationProtocol.IsSafe
      (P_partialSealSweepProtocol OverlayNoGoPsi kappa tau)
      (evenRing m (by omega))
      (exactPeriodicExecution m (by omega) kappa tau t)
      isLeaderOutput := by
  exact liftMacroConfig_not_isSafe kappa tau m (by omega)
    (evenPeriodicExecution_hasTwo m hm t)

/-- One finite even/odd period returns the exact all-closed source to itself. -/
theorem exact_run_evenPeriodWord_eq
    (m : Nat) (hm : 0 < m) (kappa tau : Nat) :
    runSchedule (P_partialSealSweepProtocol OverlayNoGoPsi kappa tau)
        (evenRing m hm) (exactAlternatingClosed m kappa tau)
        (evenPeriodWord m) =
      exactAlternatingClosed m kappa tau := by
  change runSchedule (P_partialSealSweepProtocol OverlayNoGoPsi kappa tau)
      (evenRing m hm) (liftMacroConfig kappa tau (alternatingSealed m))
      (evenPeriodWord m) =
    liftMacroConfig kappa tau (alternatingSealed m)
  calc
    _ = liftMacroConfig kappa tau
        (runSchedule sealMacroProtocol (evenRing m hm)
          (alternatingSealed m) (evenPeriodWord m)) :=
      liftMacroConfig_runSchedule kappa tau (evenRing m hm)
        (alternatingSealed m) (evenPeriodWord m)
    _ = _ := congrArg (liftMacroConfig kappa tau)
      (run_evenPeriodWord_eq m hm)

/-- Main exact-carrier counterfamily.  The physical carrier parameters
`kappa` and `tau` are arbitrary; `psi` is the explicit value two used by the
closed leader/follower witnesses.  For every even size `2 * m >= 4`, the
displayed all-closed source has a periodic weakly edge-fair exact execution
that retains at least two output leaders forever. -/
theorem all_even_sizes_exact_counterexecution :
    ∀ m : Nat, ∀ hm : 2 ≤ m, ∀ kappa tau : Nat,
      ∃ schedule : Nat → Fin (2 * m),
      ∃ execution : Nat →
          (P_partialSealSweepProtocol OverlayNoGoPsi kappa tau).Configuration
            (2 * m),
        execution 0 = exactAlternatingClosed m kappa tau ∧
        SealSweepAllClosed (execution 0) ∧
        WeakEdgeFairEven m schedule ∧
        (∀ t, (P_partialSealSweepProtocol OverlayNoGoPsi kappa tau).step
          (evenRing m (by omega)) (execution t) (schedule t) =
            execution (t + 1)) ∧
        (∀ t, execution (t + 2 * m) = execution t) ∧
        (∀ t, HasTwoLeaderOutputs
          (P_partialSealSweepProtocol OverlayNoGoPsi kappa tau)
          isLeaderOutput (execution t)) ∧
        (∀ t, ¬ PopulationProtocol.IsSafe
          (P_partialSealSweepProtocol OverlayNoGoPsi kappa tau)
          (evenRing m (by omega)) (execution t) isLeaderOutput) ∧
        runSchedule (P_partialSealSweepProtocol OverlayNoGoPsi kappa tau)
          (evenRing m (by omega)) (exactAlternatingClosed m kappa tau)
          (evenPeriodWord m) = exactAlternatingClosed m kappa tau := by
  intro m hm kappa tau
  have hmpos : 0 < m := by omega
  refine ⟨evenPeriodicSchedule m hmpos,
    exactPeriodicExecution m hmpos kappa tau,
    exactPeriodicExecution_initial m hmpos kappa tau, ?_,
    evenPeriodicSchedule_fair m hmpos,
    exactPeriodicExecution_step m hmpos kappa tau,
    exactPeriodicExecution_periodic m hmpos kappa tau,
    exactPeriodicExecution_hasTwo m hm kappa tau,
    exactPeriodicExecution_not_isSafe m hm kappa tau,
    exact_run_evenPeriodWord_eq m hmpos kappa tau⟩
  rw [exactPeriodicExecution_initial]
  exact exactAlternatingClosed_allClosed m kappa tau

end PPartialSealSweepConcurrentCounterfamilySol
end PPLLCompleteMultiLeaderCleanup
