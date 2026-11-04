import Leader.L3.Bank.CounterRows
import Leader.L3.Bank.TrialProbability

/-!
Reachability-first BANK comparator exclusivity audit.
No real rbRun trace reaching the foreign
ARMED/CR1 snapshot has been established. No unconditional R11
theorem or full preservation theorem is claimed here.
-/

namespace L3.BankComparatorExclusive

open L3
open L3.HeadlineRenewal
open L3.RenewalReferenceClock
open L3.BankHeadThreshold
open L3.BankCounterRows
open L3.BankRetryCoverage
open FiniteUniformStoppingTree
open Classical

set_option autoImplicit false
set_option Elab.async false

/-- A genuine origin worker currently carries a comparator token. -/
def BankComparatorOriginWorker {n : Nat}
    (ring : DirectedRing n)
    (r : RenewalBankReference n)
    (o : RenewalBankOrigin n)
    (i : Fin n) (p : RenewalBankPayload n) : Prop :=
  (r.2.sites i).worker = .payload p ∧
  p.origin = some o ∧
  BankTrialLiveComparisonToken (r.1 i).tok

/-- A surviving comparator is current only when its own root is
still CWAIT. Timeouts can leave physically framed obsolete tokens. -/
def BankComparatorCurrentWorker {n : Nat}
    (ring : DirectedRing n)
    (r : RenewalBankReference n)
    (o : RenewalBankOrigin n)
    (i : Fin n) (p : RenewalBankPayload n) : Prop :=
  BankComparatorOriginWorker ring r o i p ∧
  (r.1 o.root).mode = .CWAIT

/-- Corrected version with three independent obligations:
CWAIT-guarded carry payment; prefix/final-token genealogy;
and correctly numbered interval for a CURRENT comparator.
It does not include the target head threshold as a field.
Its real-word one-step preservation is not established. -/
def BankComparatorLiveInv {n : Nat}
    (ring : DirectedRing n)
    (r : RenewalBankReference n) : Prop :=
  (∀ (o : RenewalBankOrigin n) (i : Fin n)
      (p : RenewalBankPayload n),
    (r.2.sites i).worker = .payload p →
    p.origin = some o →
    (r.1 o.root).mode = .CWAIT →
    bankOriginCarryValue ring r.1 o ≤ p.heads) ∧
  (∀ (o : RenewalBankOrigin n) (i : Fin n)
      (p : RenewalBankPayload n),
    (r.2.sites i).worker = .payload p →
    p.origin = some o →
    (r.1 o.root).mode = .CWAIT →
    (((r.1 i).tok = .CR1 →
       bankComparatorPrefixMatched ring r o
         (r.1 i).pack.val ∧
       bankComparatorPrefixIRFree ring r o
         (r.1 i).pack.val) ∧
     ((r.1 i).tok = .CL1 →
       bankComparatorPrefixMatched ring r o
         (compileAdvice (ceilLogTwo n)).b ∧
       bankComparatorPrefixIRFree ring r o
         (compileAdvice (ceilLogTwo n)).b))) ∧
  (∀ (o : RenewalBankOrigin n) (i : Fin n)
      (p : RenewalBankPayload n),
    BankComparatorCurrentWorker ring r o i p →
    Counter.Complete ring r.1 o.root)

/-- ReceiptInv supplies the actual worker geometry, without
assuming a logical root from a physical token alone. -/
theorem bankComparatorWorkerAnchorOfReceipt {n : Nat}
    (ring : DirectedRing n)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (r : RenewalBankReference n)
    (hi : ReceiptInv ring seed pre r)
    (o : RenewalBankOrigin n) (i : Fin n)
    (p : RenewalBankPayload n)
    (hw : (r.2.sites i).worker = .payload p)
    (ho : p.origin = some o)
    (hlo : 1 ≤ (r.1 i).pack.val)
    (hhi : (r.1 i).pack.val ≤
      (compileAdvice (ceilLogTwo n)).b) :
    i = Counter.site ring o.root (r.1 i).pack.val := by
  exact hi.workerSite i p o hw ho hlo hhi

/-- The COMPLETE hypothesis supplies the PACK geometry:
no positive digit can be another role-zero ARMED site. -/
theorem bankComparatorCompleteNoArmedDigit {n : Nat}
    (ring : DirectedRing n)
    (C : HeadlineConfiguration n)
    (root : Fin n)
    (hcomplete : Counter.Complete ring C root)
    (j : Nat) (hj : 1 ≤ j)
    (htop : j ≤ (compileAdvice (ceilLogTwo n)).b) :
    ¬ ((C (Counter.site ring root j)).pack.val = 0 ∧
       (C (Counter.site ring root j)).mode = .ARMED) := by
  intro h
  have hp := hcomplete j htop
  rw [h.1] at hp
  omega

theorem bankComparatorLiveExcludesDigitArmed {n : Nat}
    (ring : DirectedRing n)
    (r : RenewalBankReference n)
    (h : BankComparatorLiveInv ring r)
    (o : RenewalBankOrigin n) (i : Fin n)
    (p : RenewalBankPayload n)
    (hcurrent : BankComparatorCurrentWorker ring r o i p)
    (j : Nat) (hj : 1 ≤ j)
    (htop : j ≤ (compileAdvice (ceilLogTwo n)).b) :
    ¬ ((r.1 (Counter.site ring o.root j)).pack.val = 0 ∧
       (r.1 (Counter.site ring o.root j)).mode = .ARMED) := by
  exact bankComparatorCompleteNoArmedDigit
    ring r.1 o.root (h.2.2 o i p hcurrent) j hj htop

/-- At the actual BANK start no origin has been born. -/
private theorem bankComparatorInitialWorkerAbsent {n : Nat}
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
  have hglobal :=
    rbReceiptSiteLiveGlobal
      (renewalBankStart ring seed).2 i p hlocal
  have hbirth :
      o ∈ rbBirths ring (renewalBankStart ring seed)
        ([] : List (Fin n)) :=
    ((hi.payload p hglobal).2 o ho).1
  simp [rbBirths] at hbirth

theorem bankComparatorLiveInvStart {n : Nat}
    (ring : DirectedRing n)
    (hn : 2 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) :
    BankComparatorLiveInv ring
      (renewalBankStart ring seed) := by
  constructor
  · intro o i p hw ho _
    exact False.elim
      (bankComparatorInitialWorkerAbsent
        ring hn hbank seed o i p hw ho)
  constructor
  · intro o i p hw ho _
    exact False.elim
      (bankComparatorInitialWorkerAbsent
        ring hn hbank seed o i p hw ho)
  · intro o i p hcurrent
    exact False.elim
      (bankComparatorInitialWorkerAbsent
        ring hn hbank seed o i p hcurrent.1.1 hcurrent.1.2.1)

/-- A fully matched comparator spells exactly the theta bits. -/
theorem bankComparatorFullMatchBinary {n : Nat}
    (ring : DirectedRing n)
    (r : RenewalBankReference n)
    (o : RenewalBankOrigin n)
    (hmatch : bankComparatorPrefixMatched ring r o
      (compileAdvice (ceilLogTwo n)).b) :
    bankOriginBinaryValue ring r.1 o =
      bankTrialLiveThetaBinary (ceilLogTwo n) := by
  unfold bankOriginBinaryValue bankTrialLiveThetaBinary
  apply ofFn_sum_eq
  intro j
  rw [hmatch j (by have hj := j.isLt; omega)]

/-- IR is only nonnegative extra potential. -/
theorem bankComparatorBinaryLeCarry {n : Nat}
    (ring : DirectedRing n)
    (C : HeadlineConfiguration n)
    (o : RenewalBankOrigin n) :
    bankOriginBinaryValue ring C o ≤
      bankOriginCarryValue ring C o := by
  unfold bankOriginBinaryValue bankOriginCarryValue
  apply ofFn_sum_le
  intro j
  exact Nat.le_add_right _ _

theorem bankComparatorThetaIsK (q : Nat) (hq : 3 ≤ q) :
    bankTrialLiveThetaBinary q = (compileAdvice q).K := by
  exact bankTrialProbabilityThetaBinaryEqualsK q hq

/-- Use the already-established real origin/birth provenance
to identify the root and the chronological head count. -/
theorem bankComparatorFreshCutOwnRoot {n : Nat}
    (ring : DirectedRing n)
    (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (e : Fin n) (p : RenewalBankPayload n)
    (o : RenewalBankOrigin n)
    (hcut : renewalBankCut ring
      (rbRun ring (renewalBankStart ring seed) pre).1
      (rbRun ring (renewalBankStart ring seed) pre).2 e = true)
    (hw : ((rbRun ring (renewalBankStart ring seed) pre).2.sites
      (ring.rightNeighbor e)).worker = .payload p)
    (ho : p.origin = some o) :
    o.root = e ∧
      p.heads = rbHeadCount ring o
        (renewalBankStart ring seed) pre := by
  obtain ⟨q, a, hq, ha, _, hroot, hheads⟩ :=
    bankFreshCutLoggedOrigin ring hn hbank seed pre e hcut
  have hp : q = p := by
    have hsame :
        (RenewalBankWorker.payload q : RenewalBankWorker n) =
          .payload p := Eq.trans hq.symm hw
    cases hsame
    rfl
  subst q
  have hidentity : a = o := by
    have hs :
        (some a : Option (RenewalBankOrigin n)) = some o :=
      Eq.trans ha.symm ho
    cases hs
    rfl
  subst a
  exact ⟨hroot, hheads⟩

/-- A true OLD-state cut necessarily has CWAIT and CL1. -/
theorem bankComparatorCutPhysicalGuards {n : Nat}
    (ring : DirectedRing n)
    (r : RenewalBankReference n) (e : Fin n)
    (hcut : renewalBankCut ring r.1 r.2 e = true) :
    (r.1 e).mode = .CWAIT ∧
      (r.1 (ring.rightNeighbor e)).tok = .CL1 := by
  have hmode : (r.1 e).mode = .CWAIT := by
    by_cases hm : (r.1 e).mode = .CWAIT
    · exact hm
    · have hf : renewalBankCut ring r.1 r.2 e = false := by
        simp [renewalBankCut, bankSuccess, bankCell, hm]
      rw [hf] at hcut
      cases hcut
  have htok :
      (r.1 (ring.rightNeighbor e)).tok = .CL1 := by
    by_cases ht : (r.1 (ring.rightNeighbor e)).tok = .CL1
    · exact ht
    · have hf : renewalBankCut ring r.1 r.2 e = false := by
        simp [renewalBankCut, bankSuccess, bankCell, ht]
      rw [hf] at hcut
      cases hcut
  exact ⟨hmode, htok⟩

/-- NONCIRCULAR conditional R11: complete theta genealogy and
CWAIT-guarded carry payment imply the actual K head threshold,
with p.heads=rbHeadCount supplied by ReceiptInv. -/
theorem bankCutGenuineHeadThresholdOfLiveWords {n : Nat}
    (ring : DirectedRing n)
    (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hwords : ∀ (seed : RootedSeed ring) (pre : List (Fin n)),
      BankComparatorLiveInv ring
        (rbRun ring (renewalBankStart ring seed) pre)) :
    BankCutGenuineHeadThreshold ring hbank := by
  have hq : 3 ≤ ceilLogTwo n := by
    have hs : (compileAdvice (ceilLogTwo n)).useSmall =
        decide (ceilLogTwo n ≤ qStar) := rfl
    rw [hs] at hbank
    have hnot : ¬ ceilLogTwo n ≤ qStar :=
      of_decide_eq_false hbank
    change ¬ ceilLogTwo n ≤ 79 at hnot
    omega
  intro seed pre e p o hcut hw ho
  have hroot := bankComparatorFreshCutOwnRoot
    ring hn hbank seed pre e p o hcut hw ho
  have hguard := bankComparatorCutPhysicalGuards
    ring (rbRun ring (renewalBankStart ring seed) pre) e hcut
  have hmode :
      ((rbRun ring (renewalBankStart ring seed) pre).1
        o.root).mode = .CWAIT := by
    rw [hroot.1]
    exact hguard.1
  have hlive := hwords seed pre
  have hmatched :=
    ((hlive.2.1 o (ring.rightNeighbor e) p hw ho hmode).2
      hguard.2).1
  have hbinary := bankComparatorFullMatchBinary
    ring (rbRun ring (renewalBankStart ring seed) pre) o hmatched
  have hcredit := hlive.1 o (ring.rightNeighbor e) p hw ho hmode
  have hpaid : (compileAdvice (ceilLogTwo n)).K ≤ p.heads := by
    calc
      (compileAdvice (ceilLogTwo n)).K =
          bankTrialLiveThetaBinary (ceilLogTwo n) :=
            (bankComparatorThetaIsK (ceilLogTwo n) hq).symm
      _ = bankOriginBinaryValue ring
          (rbRun ring (renewalBankStart ring seed) pre).1 o :=
            hbinary.symm
      _ ≤ bankOriginCarryValue ring
          (rbRun ring (renewalBankStart ring seed) pre).1 o :=
            bankComparatorBinaryLeCarry ring
              (rbRun ring (renewalBankStart ring seed) pre).1 o
      _ ≤ p.heads := hcredit
  rw [← hroot.2]
  exact hpaid

/-- OPEN real-source row table. The first difficult row is a
foreign CSTART entering CWAIT while an old origin comparator
worker is off-pair. No proof of this Prop is asserted. -/
def BankComparatorLiveRows {n : Nat}
    (ring : DirectedRing n) : Prop :=
  ∀ (seed : RootedSeed ring) (pre : List (Fin n))
    (e : Fin n),
    BankComparatorLiveInv ring
      (rbRun ring (renewalBankStart ring seed) pre) →
    BankComparatorLiveInv ring
      (renewalBankNext ring
        (rbRun ring (renewalBankStart ring seed) pre) e)

theorem bankComparatorLiveInvBankWordOfRows {n : Nat}
    (ring : DirectedRing n)
    (hn : 2 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hrows : BankComparatorLiveRows ring)
    (seed : RootedSeed ring) (word : List (Fin n)) :
    BankComparatorLiveInv ring
      (rbRun ring (renewalBankStart ring seed) word) := by
  have hreverse : ∀ (rev : List (Fin n)),
      BankComparatorLiveInv ring
        (rbRun ring (renewalBankStart ring seed) rev.reverse) := by
    intro rev
    induction rev with
    | nil =>
        exact bankComparatorLiveInvStart ring hn hbank seed
    | cons e es ih =>
        rw [List.reverse_cons, rbRunAppend]
        change BankComparatorLiveInv ring
          (renewalBankNext ring
            (rbRun ring (renewalBankStart ring seed) es.reverse) e)
        exact hrows seed es.reverse e ih
  simpa only [List.reverse_reverse] using hreverse word.reverse

theorem bankReferenceRetryCoverageOfLiveRows {n : Nat}
    (ring : DirectedRing n)
    (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hrows : BankComparatorLiveRows ring) :
    ReferenceRetryCoverage ring hn
      (bankValidRootedReferenceData ring hbank) := by
  apply bankReferenceRetryCoverageOfHeadThreshold ring hn hbank
  apply bankCutGenuineHeadThresholdOfLiveWords ring hn hbank
  intro seed pre
  exact bankComparatorLiveInvBankWordOfRows
    ring (by omega : 2 ≤ n) hbank hrows seed pre

/-- Literal locally failing phase activation source and responder. -/
private def bankComparatorForeignCstartSource : BankCell :=
  { role := 0, mode := .CSTART, bit := false,
    tok := .E, lease := 0, grant := false }

private def bankComparatorForeignFirstDigit : BankCell :=
  { role := 1, mode := .RESET, bit := true,
    tok := .E, lease := 0, grant := false }

theorem bankComparatorForeignCstartEntersWait :
    (bankPair bankComparatorForeignCstartSource
      bankComparatorForeignFirstDigit 1 13
      (fun _ => false)).1.mode = .CWAIT := by
  rfl

theorem bankComparatorForeignCstartKeepsBit :
    (bankPair bankComparatorForeignCstartSource
      bankComparatorForeignFirstDigit 1 13
      (fun _ => false)).2.bit = true := by
  rfl

theorem bankComparatorForeignCstartIssuesNegative :
    (bankPair bankComparatorForeignCstartSource
      bankComparatorForeignFirstDigit 1 13
      (fun _ => false)).2.tok = .CR0 := by
  rfl

theorem bankComparatorOffPairWorkerFrame {n : Nat}
    (ring : DirectedRing n)
    (r : RenewalBankReference n)
    (e i : Fin n)
    (he : i ≠ e)
    (hd : i ≠ ring.rightNeighbor e)
    (p : RenewalBankPayload n)
    (hw : (r.2.sites i).worker = .payload p) :
    ((renewalBankNext ring r e).2.sites i).worker =
      .payload p := by
  have hf := (rbReferenceOutsideSiteFrame ring r e i he hd).2
  change ((rbRun ring r [e]).2.sites i).worker = .payload p
  rw [hf]
  exact hw

theorem bankComparatorForeignCarryExceedsWorker :
    ¬ (1 + 2 + 4 ≤ 6) := by
  omega

end L3.BankComparatorExclusive
#print axioms L3.BankComparatorExclusive.bankComparatorLiveInvStart
#print axioms L3.BankComparatorExclusive.bankComparatorThetaIsK
#print axioms L3.BankComparatorExclusive.bankComparatorFreshCutOwnRoot
#print axioms L3.BankComparatorExclusive.bankCutGenuineHeadThresholdOfLiveWords
#print axioms L3.BankComparatorExclusive.bankComparatorLiveInvBankWordOfRows
#print axioms L3.BankComparatorExclusive.bankReferenceRetryCoverageOfLiveRows
#print axioms L3.BankComparatorExclusive.bankComparatorForeignCarryExceedsWorker
