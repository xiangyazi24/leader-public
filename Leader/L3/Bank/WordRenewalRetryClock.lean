import Leader.L3.Bank.WordRenewalRetry

/-!
R10 W projected clock without the hfail premise.

The only use of `BankWordRenewalAttemptFailure` in the projected-clock
chain of BankWordRenewalClose.lean is the four-block cost from a fresh
cut (`bankWordEpochFreshCutFourCostOfFailure`).  That cost now holds
unconditionally (`bankWordRenewalFreshFourCostHolds`), so the chain is
re-run here with the fresh four-cost.  `BankWordRenewalAttemptFailure`
itself (every hard-valid post-S1 state, hard kernel) is NOT claimed:
a hard-valid state after a hard S1 that erased the worker cannot
complete before its next genuine S6 (worker launch happens only at I0,
i.e. at the retry), so a three-quarter retry bound is not expected at
such states.  The renewal argument needs the bound only at fresh seeds.
-/

namespace L3.RenewalReferenceClock

open Classical
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

set_option autoImplicit false
set_option Elab.async false

/-- From any genuinely fresh cut the epoch process reaches the causal
worker-completion receipt within four renewal blocks, with no hfail
premise.  Consumer: `bankWordEpochCompletionFiveCostHolds`. -/
theorem bankWordEpochFreshCutFourCostHolds {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hs : BankWordSerializerRootClass ring hbank root s)
    (z : BankWordEpochState n)
    (hfresh : BankWordEpochFreshCut ring root s z)
    (T : Nat) :
    costNumerator (bankWordEpochNext ring root)
      BankWordRenewalCompleted z T ≤
        n ^ T * (4 * bankWordRenewalBlock n) := by
  obtain ⟨seed, heq⟩ := hfresh
  have hcost := bankWordRenewalFreshFourCostHolds
    ring hn hbank root s hs seed T
  have hmap := costNumerator_map_eq
    (bankWordRenewalNext ring root s)
    (bankWordEpochNext ring root)
    (fun v : BankWordRenewalPostSOne ring root s => v.1)
    (by intro v e; rfl)
    BankWordRenewalCompleted T seed.1
  rw [hmap] at hcost
  rw [heq] at hcost
  exact hcost

/-- A worker-completion receipt is hit within five blocks from the
represented projected W entrance: one block to the first genuine
launch (a fresh cut) and four from it, with no hfail premise.
Consumer: `bankWordProjectedClockOfCompletionBridge`. -/
theorem bankWordEpochCompletionFiveCostHolds {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hs : BankWordSerializerRootClass ring hbank root s)
    (T : Nat) :
    costNumerator (bankWordEpochNext ring root)
      BankWordRenewalCompleted
      (bankWordEpochStart s) T ≤
      n ^ T *
        ((440 * ceilLogTwo (ceilLogTwo n) + 275) * n ^ 2) := by
  have hinit : BankWordEpochReachable ring root s
      (bankWordEpochStart s) := ⟨[], rfl⟩
  have hnot :
      ¬ BankWordEpochWorkerLaunched (bankWordEpochStart s) := by
    intro h
    obtain ⟨w, hw⟩ := h
    change (none : Option (WWorkerTrail n)) = some w at hw
    cases hw
  have hfirst : ∀ U,
      costNumerator (bankWordEpochNext ring root)
        (fun z => BankWordEpochFreshCut ring root s z ∨
          BankWordRenewalCompleted z)
        (bankWordEpochStart s) U ≤
        n ^ U * bankWordRenewalBlock n := by
    intro U
    have hentr := costNumerator_entrance_le_on
      (bankWordEpochNext ring root)
      (BankWordEpochReachable ring root s)
      BankWordEpochWorkerLaunched
      (fun z => BankWordEpochFreshCut ring root s z ∨
        BankWordRenewalCompleted z)
      (fun z hz e => bankWordEpochReachableNext ring root s z hz e)
      (fun z hz hnotz e hlaunched =>
        Or.inl (bankWordEpochFreshCutOfFirstLaunch
          ring hn hbank root s hs z hz e hnotz hlaunched))
      U (bankWordEpochStart s) hinit hnot
    have hworker := bankWordEpochPostSOneWorkerClockHolds
      ring hn hbank root s hs
    have hlaunch := bankWordProjectedOneEpochCostOfWorkerClock
      ring hn hbank root s hs hworker U
    have hcoeff :
        8 * ceilLogTwo (ceilLogTwo n) + 5 =
          bankWordRenewalLease n + 1 := by
      unfold bankWordRenewalLease
      omega
    rw [hcoeff] at hlaunch
    change costNumerator (bankWordEpochNext ring root)
      BankWordEpochWorkerLaunched (bankWordEpochStart s) U ≤
      n ^ U * bankWordRenewalBlock n at hlaunch
    exact Nat.le_trans hentr hlaunch
  have hsecond : ∀ z : BankWordEpochState n,
      BankWordEpochReachable ring root s z →
      BankWordEpochFreshCut ring root s z →
      ∀ U, costNumerator (bankWordEpochNext ring root)
        BankWordRenewalCompleted z U ≤
        n ^ U * (4 * bankWordRenewalBlock n) := by
    intro z _ hfresh U
    exact bankWordEpochFreshCutFourCostHolds
      ring hn hbank root s hs z hfresh U
  have hstage := costNumerator_stage_le_on
    (bankWordEpochNext ring root)
    (BankWordEpochReachable ring root s)
    (BankWordEpochFreshCut ring root s)
    BankWordRenewalCompleted
    (fun z hz e => bankWordEpochReachableNext ring root s z hz e)
    (bankWordEpochStart s) hinit
    (bankWordRenewalBlock n) (4 * bankWordRenewalBlock n)
    hfirst hsecond T
  have hbudget :
      bankWordRenewalBlock n + 4 * bankWordRenewalBlock n =
        5 * bankWordRenewalBlock n := by
    calc
      bankWordRenewalBlock n + 4 * bankWordRenewalBlock n =
          (1 + 4) * bankWordRenewalBlock n := by
        rw [Nat.add_mul, Nat.one_mul]
      _ = 5 * bankWordRenewalBlock n := rfl
  calc
    costNumerator (bankWordEpochNext ring root)
        BankWordRenewalCompleted (bankWordEpochStart s) T ≤
      n ^ T *
        (bankWordRenewalBlock n + 4 * bankWordRenewalBlock n) :=
      hstage
    _ = n ^ T * (5 * bankWordRenewalBlock n) :=
      congrArg (fun b : Nat => n ^ T * b) hbudget
    _ = n ^ T *
        ((440 * ceilLogTwo (ceilLogTwo n) + 275) * n ^ 2) := by
      rw [bankWordRenewalFiveCoefficient]

/-- The R10 W projected clock with the completion bridge as its ONLY
premise: if every reachable causal completion is a projected target,
the original phiW first-hit clock meets the (440t+275)n² budget.
Consumer: BankWordProjectedClock in the R10 W stage of repair.tex. -/
theorem bankWordProjectedClockOfCompletionBridge {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hcompletion : ∀ root : Fin n,
      ∀ s : Fin n → ProjW (compileAdvice (ceilLogTwo n)),
        BankWordSerializerRootClass ring hbank root s →
        ∀ z : BankWordEpochState n,
          BankWordEpochReachable ring root s z →
          BankWordRenewalCompleted z →
          BankWordProjectedTarget ring z.2.1) :
    BankWordProjectedClock ring hbank := by
  intro z hz T
  obtain ⟨root, hs, _⟩ :=
    bankWordPreparedProjectedSerializerRoot ring hbank z hz
  have hcompletionCost := bankWordEpochCompletionFiveCostHolds
    ring hn hbank root (piW z.val.1) hs T
  have hmono := costNumerator_target_mono_on
    (bankWordEpochNext ring root)
    (BankWordEpochReachable ring root (piW z.val.1))
    BankWordRenewalCompleted
    (fun q : BankWordEpochState n =>
      BankWordProjectedTarget ring q.2.1)
    (fun q hq e =>
      bankWordEpochReachableNext
        ring root (piW z.val.1) q hq e)
    (fun q hq hcomplete =>
      hcompletion root (piW z.val.1) hs q hq hcomplete)
    T (bankWordEpochStart (piW z.val.1)) ⟨[], rfl⟩
  have hmap := costNumerator_map_eq
    (bankWordEpochNext ring root)
    (phiW ring)
    (fun q : BankWordEpochState n => q.2.1)
    (by intro q e; exact bankWordEpochPhysicalNext ring root q e)
    (BankWordProjectedTarget ring)
    T (bankWordEpochStart (piW z.val.1))
  rw [hmap] at hmono
  exact Nat.le_trans hmono hcompletionCost

/-- Five-block fresh completion bound with no hfail premise.
Consumer: R10 W worker-completion segment after a genuine S6. -/
theorem bankWordRenewalFreshFiveCostHolds {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hs : BankWordSerializerRootClass ring hbank root s)
    (seed : BankWordRenewalFreshSeed ring root s)
    (T : Nat) :
    costNumerator (bankWordRenewalNext ring root s)
      (fun v : BankWordRenewalPostSOne ring root s =>
        BankWordRenewalCompleted v.1)
      seed.1 T ≤ n ^ T *
        ((440 * ceilLogTwo (ceilLogTwo n) + 275) * n ^ 2) :=
  bankWordRenewalFreshFiveCostHoldsOfFailure ring hn hbank root s hs
    (bankWordRenewalFreshRetryEstimate ring hn hbank root s hs) seed T

/-- Five-block completion bound at the actual successor of a genuine
S6, with no hfail premise.  Consumer: composing the first genuine
acceptance and fresh worker completion on the R10 W scheduler. -/
theorem bankWordRenewalFiveCostAtGenuineSuccessorHolds {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hs : BankWordSerializerRootClass ring hbank root s)
    (pre : BankWordRenewalPostSOne ring root s)
    (e : Fin n)
    (hg : bankWordRenewalGenuine ring root pre.1 e)
    (T : Nat) :
    costNumerator (bankWordRenewalNext ring root s)
      (fun v : BankWordRenewalPostSOne ring root s =>
        BankWordRenewalCompleted v.1)
      (bankWordRenewalNext ring root s pre e) T ≤ n ^ T *
        ((440 * ceilLogTwo (ceilLogTwo n) + 275) * n ^ 2) :=
  bankWordRenewalFiveCostAtGenuineSuccessor ring hn hbank root s hs
    (bankWordRenewalFreshRetryEstimate ring hn hbank root s hs) pre e hg T

/-- Four-block completion bound at the actual successor of a genuine
S6, with no hfail premise.  Consumer: the 1B + 4B handoff of the
R10 W same-word clock. -/
theorem bankWordRenewalFourCostAtGenuineSuccessorHolds {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hs : BankWordSerializerRootClass ring hbank root s)
    (pre : BankWordRenewalPostSOne ring root s)
    (e : Fin n)
    (hg : bankWordRenewalGenuine ring root pre.1 e)
    (T : Nat) :
    costNumerator (bankWordRenewalNext ring root s)
      (fun v : BankWordRenewalPostSOne ring root s =>
        BankWordRenewalCompleted v.1)
      (bankWordRenewalNext ring root s pre e) T ≤
        n ^ T * (4 * bankWordRenewalBlock n) := by
  obtain ⟨seed, hseed⟩ :=
    bankWordRenewalFreshSeedAfterGenuine ring root s pre e hg
  have hc := bankWordRenewalFreshFourCostHolds
    ring hn hbank root s hs seed T
  rw [hseed] at hc
  exact hc

end L3.RenewalReferenceClock

#print axioms L3.RenewalReferenceClock.bankWordEpochFreshCutFourCostHolds
#print axioms L3.RenewalReferenceClock.bankWordEpochCompletionFiveCostHolds
#print axioms L3.RenewalReferenceClock.bankWordProjectedClockOfCompletionBridge
#print axioms L3.RenewalReferenceClock.bankWordRenewalFreshFiveCostHolds
#print axioms L3.RenewalReferenceClock.bankWordRenewalFiveCostAtGenuineSuccessorHolds
#print axioms L3.RenewalReferenceClock.bankWordRenewalFourCostAtGenuineSuccessorHolds
