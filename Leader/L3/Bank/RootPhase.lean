import Leader.L3.Bank.ComparatorExclusive

/-!
BANK-PHASE: real BANK-reference root/comparator phase certificate.

The real reachable
preservation and phase-to-comparator bridge are OPEN Props below.
No unconditional BANK-PHASE, BankComparatorLiveRows or
ReferenceRetryCoverage theorem is asserted.

Literal exception: CWAIT + CL0 -> ARMED without any RR sweep.
-/

namespace L3.BankRootPhase

open L3
open L3.HeadlineRenewal
open L3.RenewalReferenceClock
open L3.BankComparatorExclusive
open L3.BankCounterRows
open L3.BankHeadThreshold
open L3.BankRetryCoverage
open Classical

set_option autoImplicit false
set_option Elab.async false

/-- BANK-PHASE candidate, restricted to a *completed-origin*
comparator worker. Arbitrary inherited tokens at the seed cannot
satisfy an unconditional physical-token palette.

CWAIT has one comparator token and a complete numbered window;
RESET tolerates obsolete comparator tokens; RWAIT has a newer,
authenticated RR pending frontier strictly behind the survivor.
No global no-RL assertion is postulated, since multiple reset
frontiers can coexist until their priority is proved. -/
def BankRootPhaseInv {n : Nat}
    (ring : DirectedRing n)
    (r : RenewalBankReference n) : Prop :=
  ∀ (o : RenewalBankOrigin n) (i : Fin n)
    (p : RenewalBankPayload n),
    BankComparatorOriginWorker ring r o i p →
    1 ≤ (r.1 i).pack.val ∧
    (r.1 i).pack.val ≤ (compileAdvice (ceilLogTwo n)).b ∧
    (((r.1 o.root).mode = .CWAIT ∧
      Counter.Complete ring r.1 o.root ∧
      (∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
        BankTrialLiveComparisonToken
          (r.1 (Counter.site ring o.root (j.val + 1))).tok →
        Counter.site ring o.root (j.val + 1) = i)) ∨
     (r.1 o.root).mode = .RESET ∨
     ((r.1 o.root).mode = .RWAIT ∧
       ∃ (j : Nat) (rho : RenewalBankReceipt n),
         1 ≤ j ∧ j < (r.1 i).pack.val ∧
         rho.root = o.root ∧
         o.service < rho.service ∧
         (r.1 (Counter.site ring o.root j)).tok = .RR ∧
         (r.2.sites (Counter.site ring o.root j)).worker =
           .pending rho))

/-- Initial genuine BANK observer has no completed-origin
payload worker. This uses the actual empty birth log. -/
private theorem bankRootPhaseNoCompletedWorkerAtStart {n : Nat}
    (ring : DirectedRing n)
    (hn : 2 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring)
    (o : RenewalBankOrigin n) (i : Fin n)
    (p : RenewalBankPayload n)
    (hw : ((renewalBankStart ring seed).2.sites i).worker =
      .payload p)
    (ho : p.origin = some o) : False := by
  have hi := rbReceiptInvBankWordOfInv
    ring hn seed hbank ([] : List (Fin n))
  have hlocal :
      p ∈ rbSiteLivePayloads
        ((renewalBankStart ring seed).2.sites i) := by
    simp [rbSiteLivePayloads, hw]
  have hglobal := rbReceiptSiteLiveGlobal
    (renewalBankStart ring seed).2 i p hlocal
  have hbirth :
      o ∈ rbBirths ring (renewalBankStart ring seed)
        ([] : List (Fin n)) :=
    ((hi.payload p hglobal).2 o ho).1
  simp [rbBirths] at hbirth

/-- Genuine start, not an arbitrary timestamp-valid ghost. -/
theorem bankRootPhaseInvStart {n : Nat}
    (ring : DirectedRing n)
    (hn : 2 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) :
    BankRootPhaseInv ring (renewalBankStart ring seed) := by
  intro o i p hcomparator
  exact False.elim
    (bankRootPhaseNoCompletedWorkerAtStart
      ring hn hbank seed o i p
      hcomparator.1 hcomparator.2.1)

/-- The current comparator case carries all PACK geometry. -/
theorem bankRootPhaseCurrentComplete {n : Nat}
    (ring : DirectedRing n)
    (r : RenewalBankReference n)
    (hphase : BankRootPhaseInv ring r)
    (o : RenewalBankOrigin n) (i : Fin n)
    (p : RenewalBankPayload n)
    (hworker : BankComparatorOriginWorker ring r o i p)
    (hmode : (r.1 o.root).mode = .CWAIT) :
    Counter.Complete ring r.1 o.root := by
  obtain ⟨_, _, hcases⟩ := hphase o i p hworker
  rcases hcases with hcurrent | hreset | hwaiting
  · exact hcurrent.2.1
  · rw [hmode] at hreset
    cases hreset
  · have hw := hwaiting.1
    rw [hmode] at hw
    cases hw

/-- Current complete interval excludes a foreign role-zero
ARMED source at any positive protected digit. -/
theorem bankRootPhaseNoForeignArmedDigit {n : Nat}
    (ring : DirectedRing n)
    (r : RenewalBankReference n)
    (hphase : BankRootPhaseInv ring r)
    (o : RenewalBankOrigin n) (i : Fin n)
    (p : RenewalBankPayload n)
    (hworker : BankComparatorOriginWorker ring r o i p)
    (hmode : (r.1 o.root).mode = .CWAIT)
    (j : Nat) (hj : 1 ≤ j)
    (htop : j ≤ (compileAdvice (ceilLogTwo n)).b) :
    ¬ ((r.1 (Counter.site ring o.root j)).pack.val = 0 ∧
       (r.1 (Counter.site ring o.root j)).mode = .ARMED) := by
  exact bankComparatorCompleteNoArmedDigit
    ring r.1 o.root
    (bankRootPhaseCurrentComplete ring r hphase o i p
      hworker hmode) j hj htop

/-- Actual RESET launch overwrites the OLD responder worker
with a pending receipt, before any return-token test. -/
theorem bankRootPhaseResetLaunchPending {n : Nat}
    (c : Compiled) (m : RenewalBankMemory n)
    (e dest : Fin n) (x y : Agent c)
    (hb : 0 < c.b)
    (hx : x.pack.val = 0) (hy : y.pack.val = 1)
    (hg : x.grant = false) (hm : x.mode = .RESET) :
    (renewalBankPairMemory c m e dest x y).2.worker =
      .pending { service := m.service, root := e } := by
  have hrow := rbResetLaunchMemoryExact
    c m e dest x y hb hx hy hg hm
  exact congrArg
    (fun z : RenewalBankSite n × RenewalBankSite n =>
      z.2.worker) hrow

/-- Hence the old comparator payload at digit one is erased. -/
theorem bankRootPhaseResetLaunchDestErased {n : Nat}
    (c : Compiled) (m : RenewalBankMemory n)
    (e dest : Fin n) (x y : Agent c)
    (hb : 0 < c.b)
    (hx : x.pack.val = 0) (hy : y.pack.val = 1)
    (hg : x.grant = false) (hm : x.mode = .RESET)
    (p : RenewalBankPayload n) :
    (renewalBankPairMemory c m e dest x y).2.worker ≠
      .payload p := by
  rw [bankRootPhaseResetLaunchPending
    c m e dest x y hb hx hy hg hm]
  intro h
  cases h

/-- Important correction: a successful CL0 return directly
rearms a CWAIT root without passing through RWAIT + RL. -/
theorem bankRootPhaseClZeroRearms
    (b : Nat) (theta : Nat → Bool)
    (x y : BankCell)
    (hb : 1 ≤ b)
    (hx : x.role = 0) (hy : y.role = 1)
    (hg : x.grant = false)
    (hm : x.mode = .CWAIT) (ht : y.tok = .CL0) :
    (bankPair x y 1 b theta).1.mode = .ARMED := by
  simp [bankPair, hx, hy, hg, hm, ht,
    hb, isRetTok, isWaitMode, Id.run_pure, Id.run_bind]

/-- The corresponding observer consumes the returning CL0
worker and promotes its payload into the root controller. -/
theorem bankRootPhaseClZeroReturnMemory {n : Nat}
    (c : Compiled) (m : RenewalBankMemory n)
    (e dest : Fin n) (x y : Agent c)
    (hb : 0 < c.b)
    (hx : x.pack.val = 0) (hy : y.pack.val = 1)
    (hg : x.grant = false)
    (hm : x.mode = .CWAIT) (ht : y.tok = .CL0) :
    (renewalBankPairMemory c m e dest x y).2.worker =
      .empty := by
  have hrow := rbMatchedReturnMemoryExact
    c m e dest x y hb hx hy hg (Or.inr ⟨hm, ht⟩)
  exact congrArg
    (fun z : RenewalBankSite n × RenewalBankSite n =>
      z.2.worker) hrow

/-- RR has priority over a destination CR1. This is only
the physical selected-edge overwrite, not the whole sweep. -/
theorem bankRootPhaseRROverwritesCR
    (b : Nat) (theta : Nat → Bool)
    (x y : BankCell)
    (hx : 1 ≤ x.role) (hlt : x.role < b)
    (hy : y.role = x.role + 1)
    (hrr : x.tok = .RR) (hcr : y.tok = .CR1) :
    (bankPair x y y.role b theta).2.tok = .RR := by
  have hzero : x.role ≠ 0 := by omega
  have htop : x.role ≠ b := by omega
  have hnext : y.role ≠ 0 := by omega
  have hhigh : y.role ≤ b := by omega
  have hle : x.role ≤ b := by omega
  have hpost : packNext x.role y.role b = y.role := by
    rw [hy]
    simp [packNext, hlt]
  simp [bankPair, hx, hlt, hy, hrr, hcr,
    hzero, htop, hnext, hhigh, hle, hpost,
    Id.run_pure, Id.run_bind]

end L3.BankRootPhase
#print axioms L3.BankRootPhase.bankRootPhaseInvStart
#print axioms L3.BankRootPhase.bankRootPhaseCurrentComplete
#print axioms L3.BankRootPhase.bankRootPhaseNoForeignArmedDigit
#print axioms L3.BankRootPhase.bankRootPhaseResetLaunchPending
#print axioms L3.BankRootPhase.bankRootPhaseRROverwritesCR
