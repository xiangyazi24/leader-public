import Leader.L3.Bank.InheritedEdgeRows
import Leader.L3.RenewalReferenceClockInFlightRows

/-!
For the nonarmed BANK rows.

The old witness is excluded by the two worker-shape
hypotheses: a physical RL must have a pending or payload ghost.

The general-b first-match weighted two-cell inequality is
specified below as BankInheritedNonarmedCellRows. It is NOT
proved here. This module proves the reachable in-flight shape,
two-step geometry, masked score projection, scalar RR forward
price and incoming ARMED escrow, and the conditional reduction
from the cell inequality to the local A and edge A predicates.

No unconditional local-row or edge-row claim is made.
-/

namespace L3.RenewalReferenceClock

open L3.HeadlineRenewal
open FiniteUniformStoppingTree
open Classical

set_option autoImplicit false
set_option Elab.async false

/-- The in-flight invariant really does hold at every reachable
BANK reference state. No row hypothesis is left open here. -/
theorem bankInheritedReachableInFlightAligned
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank)
    (hz : BankInheritedReachable ring hbank z) :
    BankInFlightAligned ring z.val := by
  obtain ⟨_, seed, pre, hrep⟩ := hz
  rw [hrep]
  exact bankInFlightAlignedWord ring hn seed hbank pre

/-- A step's source, responder, and third PACK site are distinct
for a ring of size at least five. -/
theorem bankInheritedSecondNeighborDistinct
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (e : Fin n) :
    ring.rightNeighbor (ring.rightNeighbor e) ≠ e := by
  intro heq
  have hv := congrArg Fin.val heq
  change (((e.val + 1) % n + 1) % n) = e.val at hv
  have he := e.isLt
  by_cases hlast : e.val + 1 = n
  · rw [hlast, Nat.mod_self, Nat.zero_add,
      Nat.mod_eq_of_lt (by omega : 1 < n)] at hv
    omega
  · have hfirst : e.val + 1 < n := by omega
    rw [Nat.mod_eq_of_lt hfirst] at hv
    by_cases hpenultimate : e.val + 1 + 1 = n
    · rw [hpenultimate, Nat.mod_self] at hv
      omega
    · have hsecond : e.val + 1 + 1 < n := by omega
      rw [Nat.mod_eq_of_lt hsecond] at hv
      omega

/-- A masked BANK step changes only req/grant. Its inherited
site weight cannot observe either bit. -/
theorem bankInheritedSiteWeightForgetTokens
    {n : Nat} (c : Compiled) (x : Agent c)
    (k : Nat) (s : RenewalBankSite n) :
    bankInheritedSiteWeight c (renewalForgetTokens x) k s =
      bankInheritedSiteWeight c x k s := by
  rfl

/-- Shared physical matching fact for both masked cut outcomes:
the source score is the unsuppressed source score if its ghost
and look-ahead PACK are held fixed. -/
theorem bankInheritedMaskedSourceWeight
    {n : Nat} (c : Compiled) (cut : Bool)
    (x y : Agent c) (k : Nat) (s : RenewalBankSite n) :
    bankInheritedSiteWeight c
        (renewalMaskedPair c cut x y).1 k s =
      bankInheritedSiteWeight c
        (transition c x y).1 k s := by
  have hframe := (renewalMaskedPairFrames c cut x y).1
  have hweight := congrArg
    (fun a : Agent c => bankInheritedSiteWeight c a k s) hframe
  simpa only [bankInheritedSiteWeightForgetTokens] using hweight

theorem bankInheritedMaskedResponderWeight
    {n : Nat} (c : Compiled) (cut : Bool)
    (x y : Agent c) (k : Nat) (s : RenewalBankSite n) :
    bankInheritedSiteWeight c
        (renewalMaskedPair c cut x y).2 k s =
      bankInheritedSiteWeight c
        (transition c x y).2 k s := by
  have hframe := (renewalMaskedPairFrames c cut x y).2
  have hweight := congrArg
    (fun a : Agent c => bankInheritedSiteWeight c a k s) hframe
  simpa only [bankInheritedSiteWeightForgetTokens] using hweight

theorem bankInheritedMaskedResponderPack
    (c : Compiled) (cut : Bool) (x y : Agent c) :
    (renewalMaskedPair c cut x y).2.pack =
      (transition c x y).2.pack := by
  have hframe := (renewalMaskedPairFrames c cut x y).2
  have hp := congrArg (fun a : Agent c => a.pack) hframe
  change (renewalMaskedPair c cut x y).2.pack =
    (transition c x y).2.pack at hp
  exact hp

/-- RR can advance through a correctly aligned role without
increasing inherited atom price even if its new neighbour PACK
requires a fresh repair credit. The slack is at least one. -/
theorem bankInheritedRRForwardPriceLe
    (b j k : Nat) (hj : j < b) :
    bankInheritedWorkerPrice b .RR (j + 1) k + 1 ≤
      bankInheritedWorkerPrice b .RR j (j + 1) := by
  have hrepair :=
    bankInheritedRRRepairCreditLe b (j + 1) k .RR
  have hfixed :
      bankInheritedRRRepairCredit b j (j + 1) .RR = 0 := by
    have hp : packNext j (j + 1) b = j + 1 := by
      simp [packNext, hj]
    simp [bankInheritedRRRepairCredit, hp]
  unfold bankInheritedWorkerPrice
  simp only [bankInheritedWorkerBasePrice,
    bankInheritedWorkerPhasePrice]
  rw [hfixed]
  omega

/-- The responder's old ARMED atom can pay its incoming escrow,
with one full unit of margin per nonempty stock. -/
theorem bankInheritedIncomingArmedEscrowStrict
    (b n atoms : Nat) (hpositive : 0 < atoms) :
    n * (bankInheritedArmedPrice b - 1) * atoms + n ≤
      n * bankInheritedArmedPrice b * atoms := by
  have hcoef :
      bankInheritedArmedPrice b - 1 + 1 =
        bankInheritedArmedPrice b := by
    unfold bankInheritedArmedPrice bankInheritedWorkerCap
    omega
  have hone : 1 ≤ atoms := by omega
  have hscale : n ≤ n * atoms := by
    simpa using Nat.mul_le_mul_left n hone
  calc
    n * (bankInheritedArmedPrice b - 1) * atoms + n ≤
        n * (bankInheritedArmedPrice b - 1) * atoms +
          n * atoms := Nat.add_le_add_left hscale _
    _ = (n * (bankInheritedArmedPrice b - 1) + n) *
          atoms := by rw [Nat.add_mul]
    _ = n * ((bankInheritedArmedPrice b - 1) + 1) *
          atoms := by rw [Nat.mul_add]; simp
    _ = n * bankInheritedArmedPrice b * atoms := by
      rw [hcoef]

theorem bankInheritedIncomingArmedEscrowLe
    (b n atoms : Nat) :
    n * (bankInheritedArmedPrice b - 1) * atoms ≤
      n * bankInheritedArmedPrice b * atoms := by
  have hsub :
      bankInheritedArmedPrice b - 1 ≤
        bankInheritedArmedPrice b := Nat.sub_le _ _
  exact Nat.mul_le_mul_right atoms
    (Nat.mul_le_mul_left n hsub)

/-- The old responder's active inherited payload covers its
non-strict escrow, independent of the look-ahead PACK. -/
theorem bankInheritedArmedResponderWeightCoversEscrow
    {n : Nat} (c : Compiled) (x : Agent c)
    (p : RenewalBankPayload n) (k : Nat)
    (hm : x.mode = .ARMED) :
    n * (bankInheritedArmedPrice c.b - 1) * p.atoms.length ≤
      bankInheritedSiteWeight c x k
        { worker := .empty, controller := .active p } := by
  have hs := bankInheritedIncomingArmedEscrowLe
    c.b n p.atoms.length
  simpa [bankInheritedSiteWeight, hm] using hs

/-- Literal OLD site indicator; it agrees definitionally with
bankInheritedArmedAtoms on the actual reference. -/
def bankInheritedCellArmedAtoms
    {n : Nat} {c : Compiled}
    (x : Agent c) (s : RenewalBankSite n) : Nat :=
  if x.pack.val = 0 ∧ x.mode = .ARMED then
    bankInheritedControllerAtomCount s.controller
  else 0

def bankInheritedCellEscrow
    {n : Nat} (c : Compiled)
    (x : Agent c) (s : RenewalBankSite n) : Nat :=
  n * (bankInheritedArmedPrice c.b - 1) *
    bankInheritedCellArmedAtoms x s

/-- OLD scores: source sees OLD responder PACK; responder sees
the unchanged third-site PACK. -/
def bankInheritedCellPairBefore
    {n : Nat} (c : Compiled)
    (m : RenewalBankMemory n) (e dest : Fin n)
    (x y : Agent c) (k : Nat) : Nat :=
  bankInheritedSiteWeight c x y.pack.val (m.sites e) +
    bankInheritedSiteWeight c y k (m.sites dest)

/-- NEW scores use the *literal* masked physical pair and ghost
observer in the same order; the third-site PACK is unchanged. -/
def bankInheritedCellPairAfter
    {n : Nat} (c : Compiled)
    (m : RenewalBankMemory n) (e dest : Fin n)
    (x y : Agent c) (k : Nat) (cut : Bool) : Nat :=
  bankInheritedSiteWeight c
      (renewalMaskedPair c cut x y).1
      (renewalMaskedPair c cut x y).2.pack.val
      (renewalBankPairMemory c m e dest x y).1 +
    bankInheritedSiteWeight c
      (renewalMaskedPair c cut x y).2 k
      (renewalBankPairMemory c m e dest x y).2

/-- Exact missing general-b branch census, now restricted to
physically shaped ghosts. A proof of this Prop must split the
changed/roles/grant/RESET/return/ARMED/CSTART/interior branches,
not assume a bound on an unrelated abstract pair.

This is a DEFINITION, not a theorem or an axiom. -/
def BankInheritedNonarmedCellRows (b : Nat) : Prop :=
  ∀ {n : Nat} (c : Compiled),
    c.b = b → c.useSmall = false →
    ∀ (m : RenewalBankMemory n) (e dest : Fin n),
      e ≠ dest →
    ∀ (x y : Agent c) (k : Nat) (cut : Bool),
      bankInFlightControllerShape
          x.pack.val x.mode (m.sites e).controller →
      bankInFlightWorkerShape
          x.tok (m.sites e).worker →
      bankInFlightControllerShape
          y.pack.val y.mode (m.sites dest).controller →
      bankInFlightWorkerShape
          y.tok (m.sites dest).worker →
      bankInheritedCellArmedAtoms x (m.sites e) = 0 →
      bankInheritedCellPairAfter c m e dest x y k cut +
        bankInheritedCellEscrow c y (m.sites dest) ≤
      bankInheritedCellPairBefore c m e dest x y k

/-- From a genuine general-b cell bound to the reachable
two-score BANK nonarmed row. Reachability supplies all four
site-shape hypotheses. No independent row assumption is used. -/
theorem bankInheritedNonarmedLocalRowsOfCellRows
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hcell : BankInheritedNonarmedCellRows
      (compileAdvice (ceilLogTwo n)).b) :
    BankInheritedNonarmedLocalRows ring hbank := by
  intro z hz _ e hsource
  have htwo : 2 ≤ n := by omega
  have hdistinct : e ≠ ring.rightNeighbor e :=
    (Counter.resetRootPortDistinct ring e htwo).symm
  have halign := bankInheritedReachableInFlightAligned
    ring hn hbank z hz
  have hpair := rbReferenceSelectedPairFrame
    ring htwo z.val e
  have hthirdNeSource :
      ring.rightNeighbor (ring.rightNeighbor e) ≠ e :=
    bankInheritedSecondNeighborDistinct ring hn e
  have hthirdNeResponder :
      ring.rightNeighbor (ring.rightNeighbor e) ≠
        ring.rightNeighbor e :=
    Counter.resetRootPortDistinct
      ring (ring.rightNeighbor e) htwo
  have hthird := (rbReferenceOutsideSiteFrame
    ring z.val e
      (ring.rightNeighbor (ring.rightNeighbor e))
      hthirdNeSource hthirdNeResponder).1
  have hsourceCell :
      bankInheritedCellArmedAtoms
        (z.val.1 e) (z.val.2.sites e) = 0 := by
    exact hsource
  have hcellbound := hcell
    (compileAdvice (ceilLogTwo n)) rfl hbank
    z.val.2 e (ring.rightNeighbor e) hdistinct
    (z.val.1 e) (z.val.1 (ring.rightNeighbor e))
    (z.val.1
      (ring.rightNeighbor (ring.rightNeighbor e))).pack.val
    (renewalBankCut ring z.val.1 z.val.2 e)
    (halign e).1 (halign e).2
    (halign (ring.rightNeighbor e)).1
    (halign (ring.rightNeighbor e)).2
    hsourceCell
  have hafter :
      bankInheritedScore ring hbank
          ((bankValidRootedReferenceData ring hbank).referenceNext
            z e) e +
        bankInheritedScore ring hbank
          ((bankValidRootedReferenceData ring hbank).referenceNext
            z e) (ring.rightNeighbor e) =
      bankInheritedCellPairAfter
        (compileAdvice (ceilLogTwo n))
        z.val.2 e (ring.rightNeighbor e)
        (z.val.1 e) (z.val.1 (ring.rightNeighbor e))
        (z.val.1
          (ring.rightNeighbor (ring.rightNeighbor e))).pack.val
        (renewalBankCut ring z.val.1 z.val.2 e) := by
    change
      bankInheritedSiteWeight (compileAdvice (ceilLogTwo n))
          ((rbRun ring z.val [e]).1 e)
          ((rbRun ring z.val [e]).1
            (ring.rightNeighbor e)).pack.val
          ((rbRun ring z.val [e]).2.sites e) +
        bankInheritedSiteWeight (compileAdvice (ceilLogTwo n))
          ((rbRun ring z.val [e]).1 (ring.rightNeighbor e))
          ((rbRun ring z.val [e]).1
            (ring.rightNeighbor (ring.rightNeighbor e))).pack.val
          ((rbRun ring z.val [e]).2.sites
            (ring.rightNeighbor e)) = _
    rw [hpair.1, hpair.2.1, hpair.2.2.1,
      hpair.2.2.2,
      congrArg (fun a : Agent (compileAdvice (ceilLogTwo n)) =>
        a.pack.val) hthird]
    rfl
  have hbefore :
      bankInheritedScore ring hbank z e +
        bankInheritedScore ring hbank z
          (ring.rightNeighbor e) =
      bankInheritedCellPairBefore
        (compileAdvice (ceilLogTwo n))
        z.val.2 e (ring.rightNeighbor e)
        (z.val.1 e) (z.val.1 (ring.rightNeighbor e))
        (z.val.1
          (ring.rightNeighbor (ring.rightNeighbor e))).pack.val := by
    rfl
  have hescrow :
      bankInheritedArmedEscrow ring hbank z
        (ring.rightNeighbor e) =
      bankInheritedCellEscrow
        (compileAdvice (ceilLogTwo n))
        (z.val.1 (ring.rightNeighbor e))
        (z.val.2.sites (ring.rightNeighbor e)) := by
    rfl
  have hzero :=
    bankInheritedArmedEscrowZero ring hbank z e hsource
  rw [hafter, hescrow, hbefore, hzero]
  simpa only [Nat.add_zero] using hcellbound

/-- The global two-score balance closes (A)
once the shaped general-b cell census has been established. -/
theorem bankInheritedNonarmedEdgeRowsOfCellRows
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hcell : BankInheritedNonarmedCellRows
      (compileAdvice (ceilLogTwo n)).b) :
    BankInheritedNonarmedEdgeRows ring hbank := by
  exact bankInheritedNonarmedEdgeRowsOfLocal
    ring hn hbank
    (bankInheritedNonarmedLocalRowsOfCellRows
      ring hn hbank hcell)

end L3.RenewalReferenceClock

#print axioms L3.RenewalReferenceClock.bankInheritedReachableInFlightAligned
#print axioms L3.RenewalReferenceClock.bankInheritedRRForwardPriceLe
#print axioms L3.RenewalReferenceClock.bankInheritedNonarmedLocalRowsOfCellRows
#print axioms L3.RenewalReferenceClock.bankInheritedNonarmedEdgeRowsOfCellRows
