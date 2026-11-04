import Leader.L3.Bank.RetryCoverage

/-!
BANK reference counter-value head-threshold audit.
The full incident-row premise below
is an OPEN Prop. No unconditional R11 proof is claimed.
-/

namespace L3.BankHeadThreshold

open L3
open L3.HeadlineRenewal
open L3.RenewalReferenceClock
open L3.BankRetryCoverage
open Classical

set_option autoImplicit false
set_option Elab.async false

/-- Protected binary value for the actual origin-root window. -/
def bankOriginBinaryValue {n : Nat}
    (ring : DirectedRing n)
    (C : HeadlineConfiguration n)
    (o : RenewalBankOrigin n) : Nat :=
  (List.ofFn (fun j : Fin (compileAdvice (ceilLogTwo n)).b =>
    if (C (Counter.site ring o.root (j.val + 1))).bit
    then 2 ^ j.val else 0)).sum

/-- Carry-aware physical value: a pending IR at digit j+1 has
weight 2^(j+1), including a transient top-slot IR. -/
def bankOriginCarryValue {n : Nat}
    (ring : DirectedRing n)
    (C : HeadlineConfiguration n)
    (o : RenewalBankOrigin n) : Nat :=
  (List.ofFn (fun j : Fin (compileAdvice (ceilLogTwo n)).b =>
    (if (C (Counter.site ring o.root (j.val + 1))).bit
     then 2 ^ j.val else 0) +
    (if (C (Counter.site ring o.root (j.val + 1))).tok = .IR
     then 2 ^ (j.val + 1) else 0))).sum

/-- Proposed origin-indexed BANK invariant. The first conjunct
is a carry ledger: each genuine carrier has paid all physical
credit. The second is comparator credit: an actual fresh-payer
cut with this origin must be backed by at least K physical credit.

The second conjunct requires authenticated CR/CL genealogy;
it does NOT follow from the first conjunct in arbitrary states. -/
def BankOriginCounterValueInv {n : Nat}
    (ring : DirectedRing n)
    (r : RenewalBankReference n)
    (o : RenewalBankOrigin n) : Prop :=
  (∀ (i : Fin n) (p : RenewalBankPayload n),
    ((r.2.sites i).worker = .payload p ∨
      (r.2.sites i).controller = .active p) →
    p.origin = some o →
    bankOriginCarryValue ring r.1 o ≤ p.heads) ∧
  (∀ (e : Fin n) (p : RenewalBankPayload n),
    renewalBankCut ring r.1 r.2 e = true →
    (r.2.sites (ring.rightNeighbor e)).worker = .payload p →
    p.origin = some o →
    (compileAdvice (ceilLogTwo n)).K ≤
      bankOriginCarryValue ring r.1 o)

/-- One Prop on the literal reference, indexed by completed origins. -/
def BankReferenceCounterValueInv {n : Nat}
    (ring : DirectedRing n) (r : RenewalBankReference n) : Prop :=
  ∀ (o : RenewalBankOrigin n), BankOriginCounterValueInv ring r o

/-- Genuine start has no completed origin: authentic birth list
is empty. This uses ReceiptInv, not a fabricated ghost state. -/
private theorem bankInitialCompletedOriginImpossible {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring)
    (i : Fin n) (p : RenewalBankPayload n)
    (o : RenewalBankOrigin n)
    (hcarrier :
      ((renewalBankStart ring seed).2.sites i).worker = .payload p ∨
      ((renewalBankStart ring seed).2.sites i).controller = .active p)
    (ho : p.origin = some o) : False := by
  have hi := rbReceiptInvBankWordOfInv
    ring hn seed hbank ([] : List (Fin n))
  have hlocal :
      p ∈ rbSiteLivePayloads
        ((renewalBankStart ring seed).2.sites i) := by
    rcases hcarrier with hw | hc
    · simp [rbSiteLivePayloads, hw]
    · simp [rbSiteLivePayloads, hc]
  have hglobal := rbReceiptSiteLiveGlobal
    (renewalBankStart ring seed).2 i p hlocal
  have hborn :
      o ∈ rbBirths ring (renewalBankStart ring seed)
        ([] : List (Fin n)) :=
    ((hi.payload p hglobal).2 o ho).1
  simp [rbBirths] at hborn

/-- Actual reference's initial state satisfies both clauses
vacuously, even if physical inherited RR/RL symbols exist. -/
theorem bankReferenceCounterValueInvStart {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) :
    BankReferenceCounterValueInv ring
      (renewalBankStart ring seed) := by
  intro o
  constructor
  · intro i p hcarrier ho
    exact False.elim
      (bankInitialCompletedOriginImpossible
        ring hn hbank seed i p o hcarrier ho)
  · intro e p _ hworker ho
    exact False.elim
      (bankInitialCompletedOriginImpossible
        ring hn hbank seed (ring.rightNeighbor e)
        p o (Or.inl hworker) ho)

/-- Proved actual renewalBankNext OUTSIDE-window counter frame,
including IR potential. -/
theorem bankOriginCarryValueOutsideFrame {n : Nat}
    (ring : DirectedRing n)
    (r : RenewalBankReference n)
    (o : RenewalBankOrigin n) (e : Fin n)
    (hout : Counter.OutsideSites (ceilLogTwo n)
      ring o.root e) :
    bankOriginCarryValue ring (renewalBankNext ring r e).1 o =
      bankOriginCarryValue ring r.1 o := by
  unfold bankOriginCarryValue
  apply FiniteUniformStoppingTree.ofFn_sum_eq
  intro j
  have hf :=
    (rbResetFrontierOutsideIntervalFrame ring r e
      ({ service := 0, root := o.root } : RenewalBankReceipt n)
      hout (j.val + 1)
      (by have hj := j.isLt; omega)).1
  rw [hf]

/-- Proved actual renewalBankNext OUTSIDE-window worker frame. -/
theorem bankOriginWorkerOutsideFrame {n : Nat}
    (ring : DirectedRing n)
    (r : RenewalBankReference n)
    (o : RenewalBankOrigin n) (e : Fin n)
    (hout : Counter.OutsideSites (ceilLogTwo n)
      ring o.root e)
    (j : Nat) (hj : j ≤ (compileAdvice (ceilLogTwo n)).b)
    (p : RenewalBankPayload n)
    (hw :
      (r.2.sites (Counter.site ring o.root j)).worker =
        .payload p) :
    ((renewalBankNext ring r e).2.sites
      (Counter.site ring o.root j)).worker = .payload p := by
  have hf :=
    (rbResetFrontierOutsideIntervalFrame ring r e
      ({ service := 0, root := o.root } : RenewalBankReceipt n)
      hout j hj).2
  rw [hf]
  exact hw

/-- Both numeric and provenance sides of the outside worker row. -/
theorem bankOriginOutsideWorkerCredit {n : Nat}
    (ring : DirectedRing n)
    (r : RenewalBankReference n)
    (o : RenewalBankOrigin n) (e : Fin n)
    (hout : Counter.OutsideSites (ceilLogTwo n)
      ring o.root e)
    (j : Nat) (hj : j ≤ (compileAdvice (ceilLogTwo n)).b)
    (p : RenewalBankPayload n)
    (hw :
      (r.2.sites (Counter.site ring o.root j)).worker =
        .payload p)
    (hcredit : bankOriginCarryValue ring r.1 o ≤ p.heads) :
    ((renewalBankNext ring r e).2.sites
      (Counter.site ring o.root j)).worker = .payload p ∧
    bankOriginCarryValue ring (renewalBankNext ring r e).1 o ≤
      p.heads := by
  constructor
  · exact bankOriginWorkerOutsideFrame
      ring r o e hout j hj p hw
  · rw [bankOriginCarryValueOutsideFrame ring r o e hout]
    exact hcredit

/-- Actual observer ARMED-head update, conditional on the
still-missing physical root-row carry-delta inequality. -/
theorem bankOriginHeadCreditStep {n : Nat}
    (p : RenewalBankPayload n)
    (o : RenewalBankOrigin n)
    (before after : Nat)
    (ho : p.origin = some o)
    (hcredit : before ≤ p.heads)
    (hdelta : after ≤ before + 1) :
    after ≤ (renewalBankHead p).heads := by
  have hnew :
      (renewalBankHead p).heads = p.heads + 1 := by
    simp [renewalBankHead, ho]
  rw [hnew]
  omega

/-- The CL0/AL ordinary observer return adds waiting atoms
but preserves its worker's head count exactly. -/
theorem bankOriginReturnedCredit {n : Nat}
    (c : RenewalBankController n) (w : RenewalBankWorker n)
    (i : Fin n) (p : RenewalBankPayload n) (credit : Nat)
    (hw : w = .payload p) (hcredit : credit ≤ p.heads) :
    credit ≤ (renewalBankReturned c w i).heads := by
  simpa [renewalBankReturned, renewalBankWorkerPayload, hw]
    using hcredit

/-- OPEN full edge table, restricted to reachable BANK words.
The outside, observer-head and return rows above do not prove
this entire Prop. Root-incident carry and comparator token
genealogy remain missing. -/
def BankReferenceCounterRows {n : Nat}
    (ring : DirectedRing n) : Prop :=
  ∀ (seed : RootedSeed ring) (pre : List (Fin n))
    (e : Fin n),
    BankReferenceCounterValueInv ring
      (rbRun ring (renewalBankStart ring seed) pre) →
    BankReferenceCounterValueInv ring
      (renewalBankNext ring
        (rbRun ring (renewalBankStart ring seed) pre) e)

/-- Conditional induction over the literal historical word. -/
theorem bankReferenceCounterValueInvBankWordOfRows {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hrows : BankReferenceCounterRows ring)
    (seed : RootedSeed ring) (word : List (Fin n)) :
    BankReferenceCounterValueInv ring
      (rbRun ring (renewalBankStart ring seed) word) := by
  have hreverse :
      ∀ (rev : List (Fin n)),
        BankReferenceCounterValueInv ring
          (rbRun ring (renewalBankStart ring seed) rev.reverse) := by
    intro rev
    induction rev with
    | nil =>
        exact bankReferenceCounterValueInvStart
          ring hn hbank seed
    | cons e es ih =>
        rw [List.reverse_cons, rbRunAppend]
        change BankReferenceCounterValueInv ring
          (renewalBankNext ring
            (rbRun ring (renewalBankStart ring seed) es.reverse) e)
        exact hrows seed es.reverse e ih
  simpa only [List.reverse_reverse] using hreverse word.reverse

/-- R11 follows once both fields hold for all real BANK prefixes.
The final conversion from heads to rbHeadCount is ReceiptInv. -/
theorem bankCutGenuineHeadThresholdOfCounterValue {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hwords : ∀ (seed : RootedSeed ring) (pre : List (Fin n)),
      BankReferenceCounterValueInv ring
        (rbRun ring (renewalBankStart ring seed) pre)) :
    BankCutGenuineHeadThreshold ring hbank := by
  intro seed pre e p o hcut hworker horigin
  have hc := hwords seed pre o
  have hcredit :
      bankOriginCarryValue ring
        (rbRun ring (renewalBankStart ring seed) pre).1 o ≤
          p.heads :=
    hc.1 (ring.rightNeighbor e) p (Or.inl hworker) horigin
  have hcompare :
      (compileAdvice (ceilLogTwo n)).K ≤
        bankOriginCarryValue ring
          (rbRun ring (renewalBankStart ring seed) pre).1 o :=
    hc.2 e p hcut hworker horigin
  have hpaid :
      (compileAdvice (ceilLogTwo n)).K ≤ p.heads :=
    Nat.le_trans hcompare hcredit
  have hi := rbReceiptInvBankWordOfInv
    ring (by omega : 2 ≤ n) seed hbank pre
  have hlocal :
      p ∈ rbSiteLivePayloads
        ((rbRun ring (renewalBankStart ring seed) pre).2.sites
          (ring.rightNeighbor e)) := by
    simp [rbSiteLivePayloads, hworker]
  have hglobal := rbReceiptSiteLiveGlobal
    (rbRun ring (renewalBankStart ring seed) pre).2
    (ring.rightNeighbor e) p hlocal
  have hcount :
      p.heads =
        rbHeadCount ring o (renewalBankStart ring seed) pre :=
    ((hi.payload p hglobal).2 o horigin).2.2.2.2.2
  rw [← hcount]
  exact hpaid

/-- A conditional one-premise interface for the remaining rows. -/
theorem bankCutGenuineHeadThresholdOfRows {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hrows : BankReferenceCounterRows ring) :
    BankCutGenuineHeadThreshold ring hbank := by
  apply bankCutGenuineHeadThresholdOfCounterValue ring hn hbank
  intro seed pre
  exact bankReferenceCounterValueInvBankWordOfRows
    ring (by omega : 2 ≤ n) hbank hrows seed pre

/-- Conditional transport to the preexisting BANK retry theorem. -/
theorem bankReferenceRetryCoverageOfCounterRows {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hrows : BankReferenceCounterRows ring) :
    ReferenceRetryCoverage ring hn
      (bankValidRootedReferenceData ring hbank) := by
  exact bankReferenceRetryCoverageOfHeadThreshold
    ring hn hbank
    (bankCutGenuineHeadThresholdOfRows ring hn hbank hrows)

end L3.BankHeadThreshold

#print axioms L3.BankHeadThreshold.bankReferenceCounterValueInvStart
#print axioms L3.BankHeadThreshold.bankOriginHeadCreditStep
#print axioms L3.BankHeadThreshold.bankReferenceCounterValueInvBankWordOfRows
#print axioms L3.BankHeadThreshold.bankCutGenuineHeadThresholdOfRows
#print axioms L3.BankHeadThreshold.bankReferenceRetryCoverageOfCounterRows
