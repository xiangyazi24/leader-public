import Leader.L3.Bank.RepairWord
import Leader.L3.Grant.DrainLabelTail

/-!
R10a: genuine hard-epoch renewal on the original W epoch
scheduler.

The paper's success in repair.tex 1054-1084 is a completed
worker. BankWordEpochWorkerLaunched is only the earlier launch.
The two stopping predicates must NOT be interchanged.

The retry kernel and simulation below are real same-word
constructions. Neither hcost nor hfail is yet discharged:
the serializer-cycle and upper-binomial-tail inputs are open.
-/

namespace L3.RenewalReferenceClock

open Classical
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting
open PPL.Convergence.LDLocal
open L3.Prob

set_option autoImplicit false
set_option Elab.async false

def bankWordRenewalLease (n : Nat) : Nat :=
  8 * ceilLogTwo (ceilLogTwo n) + 4

def bankWordRenewalWorkerQuota (n : Nat) : Nat :=
  2 * ceilLogTwo (ceilLogTwo n) + 1

def bankWordRenewalHorizon (n : Nat) : Nat :=
  2 * bankWordRenewalWorkerQuota n * n ^ 2

def bankWordRenewalBlock (n : Nat) : Nat :=
  11 * (bankWordRenewalLease n + 1) * n ^ 2

/-- L=4C. -/
private theorem bankWordRenewalLeaseFourQuota (n : Nat) :
    bankWordRenewalLease n =
      4 * bankWordRenewalWorkerQuota n := by
  unfold bankWordRenewalLease bankWordRenewalWorkerQuota
  omega

/-- 5B=(440t+275)n², already present abstractly in BankRepairWord. -/
theorem bankWordRenewalFiveCoefficient (n : Nat) :
    5 * bankWordRenewalBlock n =
      (440 * ceilLogTwo (ceilLogTwo n) + 275) * n ^ 2 := by
  change
    5 * (11 * ((8 * ceilLogTwo (ceilLogTwo n) + 4) + 1) *
      n ^ 2) =
      (440 * ceilLogTwo (ceilLogTwo n) + 275) * n ^ 2
  exact bankWordEpochFiveCoefficient (ceilLogTwo (ceilLogTwo n)) n

/-- All physical states in this type are real reachable S1 cuts. -/
abbrev BankWordRenewalPostSOne {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n))) :=
  { z : BankWordEpochState n //
      BankWordEpochReachable ring root s z ∧
        BankWordEpochSOneReached z }

/-- A genuine worker completion, not mere launch. -/
def BankWordRenewalCompleted {n : Nat}
    (z : BankWordEpochState n) : Prop :=
  ∃ receipt : WCompletionReceipt n,
    z.2.2.completion = some receipt

noncomputable def bankWordRenewalNext {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (z : BankWordRenewalPostSOne ring root s)
    (e : Fin n) : BankWordRenewalPostSOne ring root s :=
  ⟨bankWordEpochNext ring root z.1 e,
    bankWordEpochReachableNext ring root s z.1 z.2.1 e,
    bankWordEpochSOneReachedNext ring root z.1 z.2.2 e⟩

/-- Ticketed hard S6, using the historical ledger and OLD pair. -/
def bankWordRenewalGenuine {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (z : BankWordEpochState n) (e : Fin n) : Prop :=
  bankWordHardEpochGenuine ring root
    (bankWordEpochSelectedReceipt ring z e)
    (bankWordHardEpochLedger ring root z) = true

/-- Epoch seeds must actually be inside a hard acceptance epoch. -/
def bankWordRenewalHardValid {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (z : BankWordEpochState n) : Prop :=
  bankWordHardEpochActive
    (bankWordHardEpochLedger ring root z) = true

/-- This part of renewal is already proved in the source:
a genuine hard acceptance reloads and starts another valid epoch. -/
theorem bankWordRenewalHardValidNext {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (z : BankWordEpochState n) (e : Fin n)
    (hg : bankWordRenewalGenuine ring root z e) :
    bankWordRenewalHardValid ring root
      (bankWordEpochNext ring root z e) := by
  obtain ⟨hcount, _, _, _, hdone, _⟩ :=
    bankWordHardEpochSelectedGenuineResetAndLease ring root z e hg
  unfold bankWordRenewalHardValid bankWordHardEpochActive
  rw [hcount, hdone]
  simp

/-- An attempt ends at a completion or the next genuine hard
acceptance. A failed attempt retains the ACTUAL survivor. -/
noncomputable def bankWordRenewalHardStep {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (z : BankWordRenewalPostSOne ring root s) (e : Fin n) :
    AttemptNode (BankWordRenewalPostSOne ring root s)
      (BankWordRenewalPostSOne ring root s) :=
  if BankWordRenewalCompleted
      (bankWordRenewalNext ring root s z e).1 then .success
  else if bankWordRenewalGenuine ring root z.1 e then
    .retry (bankWordRenewalNext ring root s z e)
  else .active (bankWordRenewalNext ring root s z e)

/-- The retry constructor is not an abstract existence premise:
every attempt consumes the same Fin n letter as bankWordEpochNext. -/
noncomputable def bankWordRenewalHardKernel {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n))) :
    RetryKernel (BankWordRenewalPostSOne ring root s)
      (BankWordRenewalPostSOne ring root s) n := {
  start := fun z => z
  step := bankWordRenewalHardStep ring root s
  valid := fun z => bankWordRenewalHardValid ring root z.1
  retry_valid := by
    intro z e dest h
    by_cases hd : BankWordRenewalCompleted
        (bankWordRenewalNext ring root s z e).1
    · simp [bankWordRenewalHardStep, hd] at h
    · by_cases hg : bankWordRenewalGenuine ring root z.1 e
      · have heq :
            bankWordRenewalNext ring root s z e = dest := by
          simpa [bankWordRenewalHardStep, hd, hg] using h
        rw [← heq]
        exact bankWordRenewalHardValidNext ring root z.1 e hg
      · simp [bankWordRenewalHardStep, hd, hg] at h
}

/-- The one-word RetrySimulation of the genuine hard kernel.
Rel is equality, not a simulated independently restarted chain. -/
theorem bankWordRenewalHardSimulation {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n))) :
    L3.Prob.RetrySimulation
      (bankWordRenewalHardKernel ring root s)
      (bankWordRenewalNext ring root s)
      (fun z : BankWordRenewalPostSOne ring root s =>
        BankWordRenewalCompleted z.1)
      (fun x y : BankWordRenewalPostSOne ring root s => x = y) := by
  intro x y hxy _ e
  cases hxy
  by_cases hd : BankWordRenewalCompleted
      (bankWordRenewalNext ring root s x e).1
  · simp [bankWordRenewalHardKernel,
      bankWordRenewalHardStep, hd]
  · by_cases hg : bankWordRenewalGenuine ring root x.1 e
    · simp [bankWordRenewalHardKernel,
        bankWordRenewalHardStep, hd, hg]
    · simp [bankWordRenewalHardKernel,
        bankWordRenewalHardStep, hd, hg]

/-- OPEN serializer start/completion subclocks, paper
repair.tex 1042-1050. Only the S1 first-hit clock and the
hard-acceptance root cleanup are already proved in the source.
The following full-cycle estimates are NOT proved. -/
def BankWordRenewalSerializerSubclocks {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n))) : Prop :=
  (∀ z : BankWordRenewalPostSOne ring root s,
    (z.1.2.1 root).ser.cert = .IDLE →
    ∀ T, costNumerator (bankWordRenewalNext ring root s)
      (fun v => (v.1.2.1 root).ser.cert = .RUNNING)
      z T ≤ n ^ T * (5 * n ^ 2 + 3 * n)) ∧
  (∀ z : BankWordRenewalPostSOne ring root s,
    (z.1.2.1 root).ser.cert = .RUNNING →
    ∀ T, costNumerator (bankWordRenewalNext ring root s)
      (fun v => (v.1.2.1 root).ser.cert = .IDLE)
      z T ≤ n ^ T * (5 * n ^ 2))

/-- OPEN initial <= B wait for the first genuine hard S6.
This is different from each hard-to-hard retry interval. -/
def BankWordRenewalInitialHardCost {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n))) : Prop :=
  ∀ z : BankWordRenewalPostSOne ring root s, ∀ T,
    costNumerator (bankWordRenewalNext ring root s)
      (fun v => 0 <
        (bankWordHardEpochLedger ring root v.1).hardEpochs)
      z T ≤ n ^ T * bankWordRenewalBlock n

/-- OPEN uniform attempt cost hcost: the serializer intervals
must be counted using at most L soft laps since the LAST hard
acceptance, not since S1. -/
def BankWordRenewalAttemptCost {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n))) : Prop :=
  ∀ z : BankWordRenewalPostSOne ring root s,
    bankWordRenewalHardValid ring root z.1 → ∀ T,
    costNumerator
      (L3.Prob.attemptStepper
        (bankWordRenewalHardKernel ring root s))
      (fun a => L3.Prob.attemptGood a ∨ L3.Prob.attemptFail a)
      (.active z) T ≤ n ^ T * bankWordRenewalBlock n

/-- OPEN exact nominated frontier condition from repair.tex
1054-1074. A retry (next hard acceptance) requires L(n-1)
adaptively nominated hits before worker completion. -/
def BankWordRenewalFrontierQuota {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n))) : Prop :=
  ∃ chosen : BankWordRenewalPostSOne ring root s → Fin n,
    ∀ z : BankWordRenewalPostSOne ring root s,
      bankWordRenewalHardValid ring root z.1 →
      ∀ word : List (Fin n),
        L3.Prob.retryFirstWord
          (bankWordRenewalHardKernel ring root s)
          (.active z) word = 1 →
        bankWordRenewalLease n * (n - 1) ≤
          L3.GrantDrainEntrance.grantDrainLabelHits
            (bankWordRenewalNext ring root s) chosen z word

/-- OPEN upper exponential-moment certificate, on the SAME
predictable nominated letter: P[Bin(H,1/n)>=Q] <=
((n+1)/n)^H / 2^Q, written without division.
The corresponding word-to-retry implication is separately open. -/
def BankWordRenewalUpperTailCertificate (n : Nat) : Prop :=
  2 ^ (bankWordRenewalLease n * (n - 1)) *
    (n ^ bankWordRenewalHorizon n -
      L3.GrantDrainEntrance.grantDrainLabelBinomialShort
        n (bankWordRenewalHorizon n)
        (bankWordRenewalLease n * (n - 1))) ≤
    (n + 1) ^ bankWordRenewalHorizon n

/-- OPEN hfail: Markov for uninterrupted worker (>1/2
completion by H) plus the upper-binomial bound (<1/4
interruption by H), combined on the same scheduler words.
Nothing in the two imported lower-tail lemmas proves this. -/
def BankWordRenewalAttemptFailure {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n))) : Prop :=
  ∀ z : BankWordRenewalPostSOne ring root s,
    bankWordRenewalHardValid ring root z.1 → ∀ T,
    4 * retryCount (bankWordRenewalHardKernel ring root s)
      (.active z) T ≤ 3 * n ^ T

private theorem bankWordRenewalFourLeFive (B : Nat) :
    4 * B ≤ 5 * B := by
  omega

/-- A genuine conditional 5B completion bound, using the
existing finite-word renewal lemma. This theorem does not
claim the open serializer/Markov/binomial premises. -/
theorem bankWordRenewalHardFiveCostOfBounds {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hcost : BankWordRenewalAttemptCost ring root s)
    (hfail : BankWordRenewalAttemptFailure ring root s)
    (z : BankWordRenewalPostSOne ring root s)
    (hz : bankWordRenewalHardValid ring root z.1) (T : Nat) :
    costNumerator (bankWordRenewalNext ring root s)
      (fun v : BankWordRenewalPostSOne ring root s =>
        BankWordRenewalCompleted v.1) z T ≤
      n ^ T * (5 * bankWordRenewalBlock n) := by
  have h := L3.Prob.costNumerator_renewal_le
    (bankWordRenewalNext ring root s)
    (fun v : BankWordRenewalPostSOne ring root s =>
      BankWordRenewalCompleted v.1)
    (bankWordRenewalHardKernel ring root s)
    (fun x y : BankWordRenewalPostSOne ring root s => x = y)
    (bankWordRenewalHardSimulation ring root s)
    (bankWordRenewalBlock n) 3 4
    (by decide : 3 < (4 : Nat))
    hcost hfail z z hz rfl T
  rw [bankWordQuarterRetryCeiling] at h
  exact Nat.le_trans h
    (Nat.mul_le_mul_left (n ^ T)
      (bankWordRenewalFourLeFive (bankWordRenewalBlock n)))

/-- Conditional expected first completion at 5B from an
already genuine hard epoch. This is NOT YET the post-S1
first-LAUNCH clock BankWordEpochPostSOneWorkerClock. -/
theorem bankWordRenewalHardFiveExpectedOfBounds {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hn : 0 < n)
    (hcost : BankWordRenewalAttemptCost ring root s)
    (hfail : BankWordRenewalAttemptFailure ring root s)
    (z : BankWordRenewalPostSOne ring root s)
    (hz : bankWordRenewalHardValid ring root z.1) :
    UniformFirstHit.ExpectedHittingTimeAtMost
      (bankWordRenewalNext ring root s)
      (fun v : BankWordRenewalPostSOne ring root s =>
        BankWordRenewalCompleted v.1)
      z ((5 * bankWordRenewalBlock n : Nat) : Rat) := by
  apply (UniformFirstHit.expectedHittingTimeAtMost_iff_cost
    (bankWordRenewalNext ring root s)
    (fun v : BankWordRenewalPostSOne ring root s =>
      BankWordRenewalCompleted v.1)
    hn z (5 * bankWordRenewalBlock n)).2
  intro T
  exact bankWordRenewalHardFiveCostOfBounds
    ring root s hcost hfail z hz T

end L3.RenewalReferenceClock

#print axioms L3.RenewalReferenceClock.bankWordRenewalFiveCoefficient
#print axioms L3.RenewalReferenceClock.bankWordRenewalHardValidNext
#print axioms L3.RenewalReferenceClock.bankWordRenewalHardSimulation
#print axioms L3.RenewalReferenceClock.bankWordRenewalHardFiveCostOfBounds
#print axioms L3.RenewalReferenceClock.bankWordRenewalHardFiveExpectedOfBounds
