import Leader.L3.Bank.InheritedCellRows

/-!
R7 (B): the inherited ARMED-root BANK rows.

Both conjuncts of BankInheritedArmedLocalRows come from the shaped
cell core bankInheritedCellCore of BankInheritedCellRows:

  after + n*A*armedY <= before + escrowX.

Outgoing: escrowY = n*(A-1)*armedY <= n*A*armedY. Incoming: an
inherited ARMED responder root has armedY >= 1, and
n*(A-1)*armedY + n <= n*A*armedY. The cell Prop below is stated in
the style of BankInheritedNonarmedCellRows (same pair scores and
escrow), without the nonarmed source hypothesis.
-/

namespace L3.RenewalReferenceClock

open L3.HeadlineRenewal
open FiniteUniformStoppingTree
open Classical

set_option autoImplicit false
set_option Elab.async false

/-- Cell rows for (B): the escrow-adjusted pair row holds for every
shaped OLD pair (nonnegative outgoing drift), and an inherited
ARMED responder root makes it strict by n (incoming margin). -/
def BankInheritedArmedCellRows (b : Nat) : Prop :=
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
      (bankInheritedCellPairAfter c m e dest x y k cut +
          bankInheritedCellEscrow c y (m.sites dest) ≤
        bankInheritedCellPairBefore c m e dest x y k +
          bankInheritedCellEscrow c x (m.sites e)) ∧
      (0 < bankInheritedCellArmedAtoms y (m.sites dest) →
        bankInheritedCellPairAfter c m e dest x y k cut +
            bankInheritedCellEscrow c y (m.sites dest) + n ≤
          bankInheritedCellPairBefore c m e dest x y k +
            bankInheritedCellEscrow c x (m.sites e))

theorem bankInheritedArmedCellRowsHolds (b : Nat) :
    BankInheritedArmedCellRows b := by
  intro n c _hcb hs m e dest _hne x y k cut hcx _hwx _hcy hwy
  have h := bankInheritedCellCore c hs m e dest x y k cut hcx hwy
  have hey : bankInheritedCellEscrow c y (m.sites dest) ≤
      n * bankInheritedArmedPrice c.b *
        bankInheritedCellArmedAtoms y (m.sites dest) := by
    unfold bankInheritedCellEscrow
    exact Nat.mul_le_mul_right _
      (Nat.mul_le_mul_left n (Nat.sub_le _ _))
  refine ⟨by omega, ?_⟩
  intro hpos
  have hstrict := bankInheritedIncomingArmedEscrowStrict
    c.b n (bankInheritedCellArmedAtoms y (m.sites dest)) hpos
  have hesc : bankInheritedCellEscrow c y (m.sites dest) =
      n * (bankInheritedArmedPrice c.b - 1) *
        bankInheritedCellArmedAtoms y (m.sites dest) := rfl
  omega

/-- The literal selected-pair instantiation, shared by both B rows:
the reference successor's two scores, the OLD scores, and both
escrows, as the cell quantities at the selected edge. -/
theorem bankInheritedArmedPairInstance
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank)
    (hz : BankInheritedReachable ring hbank z) (e : Fin n) :
    (bankInheritedScore ring hbank
          ((bankValidRootedReferenceData ring hbank).referenceNext
            z e) e +
        bankInheritedScore ring hbank
          ((bankValidRootedReferenceData ring hbank).referenceNext
            z e) (ring.rightNeighbor e) +
        bankInheritedArmedEscrow ring hbank z
          (ring.rightNeighbor e) ≤
      bankInheritedScore ring hbank z e +
        bankInheritedScore ring hbank z (ring.rightNeighbor e) +
        bankInheritedArmedEscrow ring hbank z e) ∧
    (0 < bankInheritedArmedAtoms ring hbank z
        (ring.rightNeighbor e) →
      bankInheritedScore ring hbank
          ((bankValidRootedReferenceData ring hbank).referenceNext
            z e) e +
        bankInheritedScore ring hbank
          ((bankValidRootedReferenceData ring hbank).referenceNext
            z e) (ring.rightNeighbor e) +
        bankInheritedArmedEscrow ring hbank z
          (ring.rightNeighbor e) + n ≤
      bankInheritedScore ring hbank z e +
        bankInheritedScore ring hbank z (ring.rightNeighbor e) +
        bankInheritedArmedEscrow ring hbank z e) := by
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
  have hcell := bankInheritedArmedCellRowsHolds
    (compileAdvice (ceilLogTwo n)).b
    (compileAdvice (ceilLogTwo n)) rfl hbank
    z.val.2 e (ring.rightNeighbor e) hdistinct
    (z.val.1 e) (z.val.1 (ring.rightNeighbor e))
    (z.val.1
      (ring.rightNeighbor (ring.rightNeighbor e))).pack.val
    (renewalBankCut ring z.val.1 z.val.2 e)
    (halign e).1 (halign e).2
    (halign (ring.rightNeighbor e)).1
    (halign (ring.rightNeighbor e)).2
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
  have hescrowY :
      bankInheritedArmedEscrow ring hbank z
        (ring.rightNeighbor e) =
      bankInheritedCellEscrow
        (compileAdvice (ceilLogTwo n))
        (z.val.1 (ring.rightNeighbor e))
        (z.val.2.sites (ring.rightNeighbor e)) := by
    rfl
  have hescrowX :
      bankInheritedArmedEscrow ring hbank z e =
      bankInheritedCellEscrow
        (compileAdvice (ceilLogTwo n))
        (z.val.1 e) (z.val.2.sites e) := by
    rfl
  have hatoms :
      bankInheritedArmedAtoms ring hbank z (ring.rightNeighbor e) =
      bankInheritedCellArmedAtoms
        (z.val.1 (ring.rightNeighbor e))
        (z.val.2.sites (ring.rightNeighbor e)) := by
    rfl
  rw [hafter, hescrowY, hbefore, hescrowX, hatoms]
  exact hcell

/-- (B) local rows, unconditionally at reachable BANK states. -/
theorem bankInheritedArmedLocalRowsHolds
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) :
    BankInheritedArmedLocalRows ring hbank := by
  constructor
  · intro z hz _ e _
    exact (bankInheritedArmedPairInstance ring hn hbank z hz e).1
  · intro z hz _ r e he harm
    subst he
    exact (bankInheritedArmedPairInstance ring hn hbank z hz e).2 harm

/-- (B) at the edge level, unconditionally. -/
theorem bankInheritedArmedEdgeRowsHolds
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) :
    BankInheritedArmedEdgeRows ring hbank :=
  bankInheritedArmedEdgeRowsOfLocal ring hn hbank
    (bankInheritedArmedLocalRowsHolds ring hn hbank)

/-- The R7 retirement stage now depends on the progress
alternative C alone: A and B are discharged. -/
theorem bankInheritedRetirementStageOfProgress
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hprogress : BankInheritedProgressAlternative ring hbank) :
    StageInheritedAuthorityExtinction
      (bankValidRootedReferenceData ring hbank).referenceNext
      (BankInheritedRootedStart ring hbank)
      (fun z => headlineRooted ring z.val.1 ∧
        InheritedAuthorityExtinct ring hbank z)
      (ceilLogTwo n) :=
  bankInheritedRetirementStageOfLocalRowsAndProgress ring hn hbank
    (bankInheritedNonarmedLocalRowsHolds ring hn hbank)
    (bankInheritedArmedLocalRowsHolds ring hn hbank)
    hprogress

end L3.RenewalReferenceClock

#print axioms L3.RenewalReferenceClock.bankInheritedArmedCellRowsHolds
#print axioms L3.RenewalReferenceClock.bankInheritedArmedPairInstance
#print axioms L3.RenewalReferenceClock.bankInheritedArmedLocalRowsHolds
#print axioms L3.RenewalReferenceClock.bankInheritedArmedEdgeRowsHolds
#print axioms L3.RenewalReferenceClock.bankInheritedRetirementStageOfProgress
