import Leader.L3.Bank.WordRenewalFailure

/-!
Fresh genuine hard-entry renewal, on the original projected W chain.

Proved here: the fresh seed (a selected genuine hard S6), the
same-word simulation of the fresh retry kernel, the actual hard-S1
dispatch, and the first-H prefix transfer for the worker and
serializer nominated-hit events.  Not proved here: the pathwise
serializer/worker frontier implications, hence the three-quarter
retry estimate; the five-block bound is conditional on that estimate
and on the attempt cost (repair.tex, R10a renewal paragraph).
-/

namespace L3.RenewalReferenceClock

open Classical
open L3.Prob
open L3.GrantDrainEntrance
open PPL.Convergence.LDLocal
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

set_option autoImplicit false
set_option Elab.async false

/-- A seed carries the actual selected preceding genuine hard S6.
Consumer: the uniform-renewal seed quantifier in
ProbRenewal.costNumerator_renewal_le. -/
abbrev BankWordRenewalFreshSeed {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n))) :=
  { z : BankWordRenewalPostSOne ring root s //
    BankWordRenewalFreshHardEntry ring root s z }

/-- Every selected genuine hard S6 supplies the fresh seed for the
actual successor, without constructing a counterfactual restart.
Consumer: retry_valid of bankWordRenewalFreshKernel. -/
theorem bankWordRenewalFreshAfterGenuine {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (z : BankWordRenewalPostSOne ring root s) (e : Fin n)
    (hg : bankWordRenewalGenuine ring root z.1 e) :
    BankWordRenewalFreshHardEntry ring root s
      (bankWordRenewalNext ring root s z e) := by
  exact ⟨z, e, hg, rfl⟩

/-- The fresh step uses exactly one original scheduler edge.
Completion has priority over a genuine hard acceptance; only a
genuine hard acceptance returns a fresh retry seed. -/
noncomputable def bankWordRenewalFreshStep {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (z : BankWordRenewalPostSOne ring root s)
    (e : Fin n) :
    AttemptNode (BankWordRenewalPostSOne ring root s)
      (BankWordRenewalFreshSeed ring root s) :=
  if BankWordRenewalCompleted
      (bankWordRenewalNext ring root s z e).1 then .success
  else if hg : bankWordRenewalGenuine ring root z.1 e then
    .retry ⟨bankWordRenewalNext ring root s z e,
      bankWordRenewalFreshAfterGenuine ring root s z e hg⟩
  else .active (bankWordRenewalNext ring root s z e)

/-- The seed predicate is freshness, not arbitrary hard validity.
The retry destination contains its own genuine-acceptance witness.
Consumer: ProbRenewal's valid-closed retry recurrence. -/
noncomputable def bankWordRenewalFreshKernel {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n))) :
    RetryKernel (BankWordRenewalPostSOne ring root s)
      (BankWordRenewalFreshSeed ring root s) n := {
  start := fun z => z.1
  step := bankWordRenewalFreshStep ring root s
  valid := fun z => BankWordRenewalFreshHardEntry ring root s z.1
  retry_valid := by
    intro z e dest h
    exact dest.2
}

/-- The actual root W trajectory is never restarted or spliced;
comparison is equality of the post-S1 physical epoch states.
Consumer: costNumerator_renewal_le for the fresh kernel. -/
theorem bankWordRenewalFreshSimulation {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n))) :
    L3.Prob.RetrySimulation
      (bankWordRenewalFreshKernel ring root s)
      (bankWordRenewalNext ring root s)
      (fun z : BankWordRenewalPostSOne ring root s =>
        BankWordRenewalCompleted z.1)
      (fun x y : BankWordRenewalPostSOne ring root s =>
        x = y) := by
  intro x y hxy _ e
  cases hxy
  by_cases hd : BankWordRenewalCompleted
      (bankWordRenewalNext ring root s x e).1
  · simp [bankWordRenewalFreshKernel,
      bankWordRenewalFreshStep, hd]
  · by_cases hg : bankWordRenewalGenuine ring root x.1 e
    · simp [bankWordRenewalFreshKernel,
        bankWordRenewalFreshStep, hd, hg]
    · simp [bankWordRenewalFreshKernel,
        bankWordRenewalFreshStep, hd, hg]

/-- A genuine retry returns to the actual reloaded epoch, so the
per-epoch soft counters and pending bit are zero at that cut.
Consumer: the intended serializer-lap genealogy. -/
theorem bankWordRenewalFreshRetryReset {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (z : BankWordRenewalPostSOne ring root s)
    (e : Fin n)
    (hg : bankWordRenewalGenuine ring root z.1 e) :
    (bankWordHardEpochLedger ring root
      (bankWordRenewalNext ring root s z e).1).softStarts = 0 ∧
    (bankWordHardEpochLedger ring root
      (bankWordRenewalNext ring root s z e).1).softFinishes = 0 ∧
    (bankWordHardEpochLedger ring root
      (bankWordRenewalNext ring root s z e).1).pendingSoft = false ∧
    bankWordRenewalHardValid ring root
      (bankWordRenewalNext ring root s z e).1 := by
  exact bankWordRenewalFreshHardFields ring root s
    (bankWordRenewalNext ring root s z e)
    (bankWordRenewalFreshAfterGenuine ring root s z e hg)

/-- A real serializer S1 (including a hard S1) is NOT the
ticketed S6 retry event.  If that step has not completed the
worker, the fresh attempt remains active and continues on its
actual physical successor.  Consumer: the first-H interruption
partition; the interruption clock must be separate from retry. -/
theorem bankWordRenewalFreshSOneContinues {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (z : BankWordRenewalPostSOne ring root s) (e : Fin n)
    (hrow :
      (bankWordEpochSelectedReceipt ring z.1 e).serializer.row =
        "S1")
    (hno : ¬ BankWordRenewalCompleted
      (bankWordRenewalNext ring root s z e).1) :
    bankWordRenewalFreshStep ring root s z e =
      .active (bankWordRenewalNext ring root s z e) := by
  have hg := bankWordRenewalHardStartNotGenuine
    ring root z.1 e hrow
  simp [bankWordRenewalFreshStep, hno, hg]

/-- An observer-based candidate for the worker's next productive
edge.  PREFIX, SUM and READY move outward from the current host;
BACK moves into the current host.  No global productivity claim
is inferred from this local nomination. -/
noncomputable def bankWordRenewalFreshWorkerNomination {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (z : BankWordRenewalPostSOne ring root s) : Fin n :=
  match (bankWordHardEpochLedger ring root z.1).worker with
  | none => root
  | some w =>
    match w.phase with
    | .backRun => ring.leftNeighbor w.host
    | .prefixRun => w.host
    | .sumRun => w.host
    | .readyRun => w.host

/-- A real recorded BACK worker nominates its incoming edge.
Consumer: the worker nominated-hit lower tail, once uninterrupted
progress is established from the physical rows. -/
theorem bankWordRenewalFreshWorkerBackNomination {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (z : BankWordRenewalPostSOne ring root s)
    (w : WWorkerTrail n)
    (hw : (bankWordHardEpochLedger ring root z.1).worker = some w)
    (hphase : w.phase = .backRun) :
    bankWordRenewalFreshWorkerNomination ring root s z =
      ring.leftNeighbor w.host := by
  simp [bankWordRenewalFreshWorkerNomination, hw, hphase]

/-- Count constant cylinder weights directly in the repository's
uniform-word enumerator. -/
private theorem bankWordRenewalFreshScheduleConstant
    (n T c : Nat) :
    L3.Prob.scheduleSum n T
      (fun _ : List (Fin n) => c) = n ^ T * c := by
  change FixedSpanRenewalPayload.wordSum n T
    (fun _ : List (Fin n) => c) = n ^ T * c
  rw [← FixedSpanRenewalPayload.rawWord_sum n T
    (fun _ : List (Fin n) => c)]
  exact ofFn_sum_const _ _

private theorem bankWordRenewalFreshScheduleSucc {n : Nat}
    (T : Nat) (f : List (Fin n) → Nat) :
    L3.Prob.scheduleSum n (T + 1) f =
      (List.ofFn (fun e : Fin n =>
        L3.Prob.scheduleSum n T (fun w => f (e :: w)))).sum :=
  FixedSpanRenewalPayload.wordSum_succ n T f

/-- A first-H cylinder event has exactly n^K extensions.
The event is arbitrary, so this lemma also covers the concrete
serializer and worker nominated-hit predicates.  Consumer:
the full-T first-H word-count transfer for the renewal split. -/
theorem bankWordRenewalFreshPrefixCount {n : Nat}
    (H K : Nat) (event : List (Fin n) → Nat) :
    L3.Prob.scheduleSum n (H + K)
      (fun word => event (word.take H)) =
    n ^ K * L3.Prob.scheduleSum n H event := by
  induction H generalizing event with
  | zero =>
      have hfun :
          (fun word : List (Fin n) => event (word.take 0)) =
          (fun _ : List (Fin n) => event []) := by
        funext word
        simp
      rw [Nat.zero_add, hfun]
      calc
        L3.Prob.scheduleSum n K
            (fun _ : List (Fin n) => event []) =
            n ^ K * event [] :=
          bankWordRenewalFreshScheduleConstant n K (event [])
        _ = n ^ K * L3.Prob.scheduleSum n 0 event := by
          simp [L3.Prob.scheduleSum,
            FixedSpanRenewalPayload.wordSum, allSchedules]
  | succ H ih =>
      have hlen : (H + 1) + K = (H + K) + 1 := by omega
      calc
        L3.Prob.scheduleSum n ((H + 1) + K)
            (fun word => event (word.take (H + 1))) =
            L3.Prob.scheduleSum n ((H + K) + 1)
              (fun word => event (word.take (H + 1))) := by
              rw [hlen]
        _ = (List.ofFn (fun e : Fin n =>
              L3.Prob.scheduleSum n (H + K)
                (fun w => event ((e :: w).take (H + 1))))).sum :=
              bankWordRenewalFreshScheduleSucc (H + K) _
        _ = (List.ofFn (fun e : Fin n =>
              n ^ K * L3.Prob.scheduleSum n H
                (fun w => event (e :: w)))).sum := by
              apply ofFn_sum_eq
              intro e
              have htake :
                  (fun w : List (Fin n) =>
                    event ((e :: w).take (H + 1))) =
                  (fun w => event (e :: w.take H)) := by
                    funext w
                    rfl
              rw [htake]
              exact ih (fun w => event (e :: w))
        _ = n ^ K * (List.ofFn (fun e : Fin n =>
              L3.Prob.scheduleSum n H
                (fun w => event (e :: w)))).sum := by
              rw [ofFn_sum_mul_left]
        _ = n ^ K * L3.Prob.scheduleSum n (H + 1) event := by
              rw [bankWordRenewalFreshScheduleSucc]

/-- Physical worker short-hit event transferred from H to H+K,
with the SAME state-dependent nomination and actual W next.
Consumer: bankWordRenewalWorkerNominationHalf. -/
theorem bankWordRenewalFreshWorkerPrefixCount {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (z : BankWordRenewalPostSOne ring root s)
    (chosen : BankWordRenewalPostSOne ring root s → Fin n)
    (K : Nat) :
    L3.Prob.scheduleSum n (bankWordRenewalHorizon n + K)
      (fun word =>
        if grantDrainLabelHits (bankWordRenewalNext ring root s)
            chosen z (word.take (bankWordRenewalHorizon n)) <
            bankWordRenewalWorkerQuota n * n then 1 else 0) =
    n ^ K * L3.Prob.scheduleSum n (bankWordRenewalHorizon n)
      (fun word =>
        if grantDrainLabelHits (bankWordRenewalNext ring root s)
            chosen z word < bankWordRenewalWorkerQuota n * n
        then 1 else 0) := by
  exact bankWordRenewalFreshPrefixCount
    (bankWordRenewalHorizon n) K
    (fun word =>
      if grantDrainLabelHits (bankWordRenewalNext ring root s)
          chosen z word < bankWordRenewalWorkerQuota n * n
      then 1 else 0)

/-- Physical serializer long-hit event likewise depends only
on the first H letters.  This does not assume that a suitable
serializer frontier nomination has already been proved.
Consumer: bankUpperBankBandInterruptionQuarter. -/
theorem bankWordRenewalFreshSerializerPrefixCount {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (z : BankWordRenewalPostSOne ring root s)
    (chosen : BankWordRenewalPostSOne ring root s → Fin n)
    (K : Nat) :
    L3.Prob.scheduleSum n (bankWordRenewalHorizon n + K)
      (fun word =>
        if bankWordRenewalLease n * (n - 1) ≤
          grantDrainLabelHits (bankWordRenewalNext ring root s)
            chosen z (word.take (bankWordRenewalHorizon n))
        then 1 else 0) =
    n ^ K * L3.Prob.scheduleSum n (bankWordRenewalHorizon n)
      (fun word =>
        if bankWordRenewalLease n * (n - 1) ≤
          grantDrainLabelHits (bankWordRenewalNext ring root s)
            chosen z word then 1 else 0) := by
  exact bankWordRenewalFreshPrefixCount
    (bankWordRenewalHorizon n) K
    (fun word =>
      if bankWordRenewalLease n * (n - 1) ≤
        grantDrainLabelHits (bankWordRenewalNext ring root s)
          chosen z word then 1 else 0)

/-- The attempt-cost input is now quantified only over genuinely
fresh hard-acceptance seeds, not arbitrary old hardValid states. -/
def BankWordRenewalFreshAttemptCost {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n))) : Prop :=
  ∀ seed : BankWordRenewalFreshSeed ring root s, ∀ T,
    costNumerator
      (L3.Prob.attemptStepper
        (bankWordRenewalFreshKernel ring root s))
      (fun a => L3.Prob.attemptGood a ∨ L3.Prob.attemptFail a)
      (.active seed.1) T ≤ n ^ T * bankWordRenewalBlock n

/-- Conditional five-block physical completion bound, obtained
from the existing same-word renewal theorem.  The failure
hypothesis is the still-open three-quarter retry estimate for
the fresh kernel, not a claimed consequence of the prefix lemmas.
Consumer: R10a 5B completion line of repair.tex. -/
theorem bankWordRenewalFreshFiveCostOfBounds {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hcost : BankWordRenewalFreshAttemptCost ring root s)
    (hfail : ∀ seed : BankWordRenewalFreshSeed ring root s,
      ∀ T, 4 * retryCount (bankWordRenewalFreshKernel ring root s)
        (.active seed.1) T ≤ 3 * n ^ T)
    (seed : BankWordRenewalFreshSeed ring root s)
    (T : Nat) :
    costNumerator (bankWordRenewalNext ring root s)
      (fun v : BankWordRenewalPostSOne ring root s =>
        BankWordRenewalCompleted v.1)
      seed.1 T ≤ n ^ T * (5 * bankWordRenewalBlock n) := by
  have hc : ∀ a : BankWordRenewalFreshSeed ring root s,
      (bankWordRenewalFreshKernel ring root s).valid a →
      ∀ t, costNumerator
        (L3.Prob.attemptStepper
          (bankWordRenewalFreshKernel ring root s))
        (fun v => L3.Prob.attemptGood v ∨
          L3.Prob.attemptFail v)
        (.active ((bankWordRenewalFreshKernel ring root s).start a))
        t ≤ n ^ t * bankWordRenewalBlock n := by
    intro a _ t
    exact hcost a t
  have hf : ∀ a : BankWordRenewalFreshSeed ring root s,
      (bankWordRenewalFreshKernel ring root s).valid a →
      ∀ t, 4 * retryCount (bankWordRenewalFreshKernel ring root s)
        (.active ((bankWordRenewalFreshKernel ring root s).start a))
        t ≤ 3 * n ^ t := by
    intro a _ t
    exact hfail a t
  have h := L3.Prob.costNumerator_renewal_le
    (bankWordRenewalNext ring root s)
    (fun v : BankWordRenewalPostSOne ring root s =>
      BankWordRenewalCompleted v.1)
    (bankWordRenewalFreshKernel ring root s)
    (fun x y : BankWordRenewalPostSOne ring root s => x = y)
    (bankWordRenewalFreshSimulation ring root s)
    (bankWordRenewalBlock n) 3 4
    (by decide : 3 < (4 : Nat))
    hc hf seed.1 seed seed.2 rfl T
  rw [bankWordQuarterRetryCeiling] at h
  have hfour :
      4 * bankWordRenewalBlock n ≤
        5 * bankWordRenewalBlock n :=
    Nat.mul_le_mul_right _ (by decide : 4 ≤ (5 : Nat))
  exact Nat.le_trans h (Nat.mul_le_mul_left (n ^ T) hfour)

end L3.RenewalReferenceClock

#print axioms L3.RenewalReferenceClock.bankWordRenewalFreshAfterGenuine
#print axioms L3.RenewalReferenceClock.bankWordRenewalFreshSimulation
#print axioms L3.RenewalReferenceClock.bankWordRenewalFreshRetryReset
#print axioms L3.RenewalReferenceClock.bankWordRenewalFreshSOneContinues
#print axioms L3.RenewalReferenceClock.bankWordRenewalFreshPrefixCount
#print axioms L3.RenewalReferenceClock.bankWordRenewalFreshFiveCostOfBounds
#print axioms L3.RenewalReferenceClock.bankWordRenewalFreshAfterGenuine
#print axioms L3.RenewalReferenceClock.bankWordRenewalFreshSimulation
#print axioms L3.RenewalReferenceClock.bankWordRenewalFreshRetryReset
#print axioms L3.RenewalReferenceClock.bankWordRenewalFreshSOneContinues
#print axioms L3.RenewalReferenceClock.bankWordRenewalFreshWorkerBackNomination
#print axioms L3.RenewalReferenceClock.bankWordRenewalFreshPrefixCount
#print axioms L3.RenewalReferenceClock.bankWordRenewalFreshWorkerPrefixCount
#print axioms L3.RenewalReferenceClock.bankWordRenewalFreshSerializerPrefixCount
#print axioms L3.RenewalReferenceClock.bankWordRenewalFreshFiveCostOfBounds
