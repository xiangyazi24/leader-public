import Leader.L3.Bank.WordRenewal
import Leader.L3.BinomialUpperTail

/-!
R10a hard-epoch renewal: exact binomial interface and literal
early hard-start observer row.

The numerical upper and lower tails are proved. The causal
lap-frontier and hypothetical uninterrupted-worker bridges
are not established and BankWordRenewalAttemptFailure is not
claimed. See repair.tex 1054--1084.
-/

namespace L3.RenewalReferenceClock

open L3.GrantDrainEntrance
open L3.Prob
open PPL.Convergence.LDLocal
open Classical

set_option autoImplicit false
set_option Elab.async false

/-- The exact upper-tail certificate already is the imported
binomial moment at the epoch H,Q. Consumer: R10a case (a). -/
theorem bankWordRenewalUpperCertificate
    (n : Nat) (hn : 0 < n) :
    BankWordRenewalUpperTailCertificate n := by
  exact L3.BinomialUpperTail.grantDrainLabelBinomialUpperMoment
    n (bankWordRenewalHorizon n)
    (bankWordRenewalLease n * (n - 1)) hn

/-- A valid hard epoch may have already spent some of its
soft-lap budget. The actual hard acceptance resets BOTH
soft counters, the pending flag, and the workerDone flag.
This identifies the proper start cut for the paper's L laps. -/
def BankWordRenewalFreshHardEntry {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (z : BankWordRenewalPostSOne ring root s) : Prop :=
  ∃ pre : BankWordRenewalPostSOne ring root s,
    ∃ e : Fin n,
      bankWordRenewalGenuine ring root pre.1 e ∧
      bankWordRenewalNext ring root s pre e = z

/-- Actual reset fields of a newly accepted hard epoch.
Consumer: the per-hard-epoch serializer-lap genealogy,
not a cumulative ledger since the first S1. -/
theorem bankWordRenewalFreshHardFields {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (z : BankWordRenewalPostSOne ring root s)
    (hfresh : BankWordRenewalFreshHardEntry ring root s z) :
    (bankWordHardEpochLedger ring root z.1).softStarts = 0 ∧
    (bankWordHardEpochLedger ring root z.1).softFinishes = 0 ∧
    (bankWordHardEpochLedger ring root z.1).pendingSoft = false ∧
    bankWordRenewalHardValid ring root z.1 := by
  obtain ⟨pre, e, hgen, heq⟩ := hfresh
  have hreset :=
    bankWordHardEpochSelectedGenuineResetAndLease
      ring root pre.1 e hgen
  obtain ⟨_, hstarts, hfinishes, hpending, _, _⟩ := hreset
  have hvalid := bankWordRenewalHardValidNext
    ring root pre.1 e hgen
  rw [← heq]
  exact ⟨hstarts, hfinishes, hpending, hvalid⟩

/-- One actual old-pair S1 serializer row cannot also be a
genuine S6 acceptance. This distinguishes hard START from the
later retry event of the existing RetryKernel. -/
theorem bankWordRenewalHardStartNotGenuine {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (z : BankWordEpochState n) (e : Fin n)
    (hSOne :
      (bankWordEpochSelectedReceipt ring z e).serializer.row =
        "S1") :
    ¬ bankWordRenewalGenuine ring root z e := by
  intro hgen
  have hflags := bankWordHardEpochSelectedGenuineOwnerFlags
    ring root z e hgen
  have hsix := hflags.2.1
  rw [hSOne] at hsix
  exact absurd hsix (by decide)

/-- Literal Target.wWorkerReceiptStep row.
On SI I1 with hardS1, the OLD worker witness is destroyed
before a genuine S6 acceptance and no completion is emitted.
This is NOT an uninterrupted-worker history theorem. -/
theorem bankWordRenewalHardSOneErasesWorker
    {n : Nat} {c : Compiled}
    (root edge dest : Fin n) (clock : Nat)
    (x y : ProjW c)
    (w : WWorkerTrail n)
    (accept : Option WValidationTicket)
    (hIone : (workerW x y).row = "I1")
    (hhard : (serW x y).hard.hardS1 = true) :
    wWorkerReceiptStep root edge dest clock x y
      accept (some w) = (none, none) := by
  simp [wWorkerReceiptStep, hIone, hhard]



/-- Exact binomial lower-half bound from the installed
lower weighted estimate and its 2n-block decay. The opaque
T,Q lemma is instantiated only after the two source facts. -/
private theorem bankWordRenewalBinomialHalf
    (n T Q : Nat) (hn : 0 < n)
    (hlength : 2 * n * Q ≤ T) :
    2 * grantDrainLabelBinomialShort n T Q ≤ n ^ T := by
  have hweighted :=
    grantDrainLabelBinomialWeighted n T Q hn
  have hdecay :=
    grantDrainLabelTailDecay n T Q hn hlength
  have htotal := Nat.le_trans hweighted hdecay
  have hscaled :
      2 ^ T * (2 * grantDrainLabelBinomialShort n T Q) ≤
        2 ^ T * n ^ T := by
    calc
      2 ^ T * (2 * grantDrainLabelBinomialShort n T Q) =
          2 ^ (T + 1) * grantDrainLabelBinomialShort n T Q := by
            rw [Nat.pow_succ]
            simp only [Nat.mul_assoc]
      _ ≤ (2 * n) ^ T := htotal
      _ = 2 ^ T * n ^ T := Nat.mul_pow 2 n T
  exact Nat.le_of_mul_le_mul_left hscaled
    (Nat.pow_pos (by decide : 0 < (2 : Nat)))

/-- Paper 1061--1074: on the ACTUAL epoch chain, for any
predictable worker nomination, the event 'fewer than Cn
nominated hits in H=2Cn² letters' has mass at most 1/2.
This does not assert that an actual worker exists or survives. -/
theorem bankWordRenewalWorkerNominationHalf {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (z : BankWordRenewalPostSOne ring root s)
    (chosen : BankWordRenewalPostSOne ring root s → Fin n)
    (hn : 0 < n) :
    2 * L3.Prob.scheduleSum n (bankWordRenewalHorizon n)
      (fun word =>
        if grantDrainLabelHits (bankWordRenewalNext ring root s)
            chosen z word < bankWordRenewalWorkerQuota n * n
        then 1 else 0) ≤
      n ^ bankWordRenewalHorizon n := by
  have hlength :
      2 * n * (bankWordRenewalWorkerQuota n * n) ≤
        bankWordRenewalHorizon n := by
    have heq :
        2 * n * (bankWordRenewalWorkerQuota n * n) =
          2 * bankWordRenewalWorkerQuota n * n ^ 2 := by
      rw [Nat.pow_two]
      simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    rw [heq]
    exact Nat.le_refl _
  have hmass := bankWordRenewalBinomialHalf
    n (bankWordRenewalHorizon n)
    (bankWordRenewalWorkerQuota n * n) hn hlength
  rw [grantDrainLabelBinomialLaw
    (bankWordRenewalNext ring root s)
    chosen z (bankWordRenewalHorizon n)
    (bankWordRenewalWorkerQuota n * n) hn]
  exact hmass

end L3.RenewalReferenceClock

#print axioms L3.RenewalReferenceClock.bankWordRenewalUpperCertificate
#print axioms L3.RenewalReferenceClock.bankWordRenewalFreshHardFields
#print axioms L3.RenewalReferenceClock.bankWordRenewalHardStartNotGenuine
#print axioms L3.RenewalReferenceClock.bankWordRenewalHardSOneErasesWorker
#print axioms L3.RenewalReferenceClock.bankWordRenewalWorkerNominationHalf
#print axioms L3.RenewalReferenceClock.bankWordRenewalUpperCertificate
#print axioms L3.RenewalReferenceClock.bankWordRenewalFreshHardFields
#print axioms L3.RenewalReferenceClock.bankWordRenewalHardStartNotGenuine
#print axioms L3.RenewalReferenceClock.bankWordRenewalHardSOneErasesWorker
#print axioms L3.RenewalReferenceClock.bankWordRenewalWorkerNominationHalf
