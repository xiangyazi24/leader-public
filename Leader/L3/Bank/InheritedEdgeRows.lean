import Leader.L3.Bank.InheritedDrift

/-!
Exact local score balance for the BANK inherited potential.
The SOURCE PACK is preserved on every selected edge. Consequently
even the predecessor's RR repair-credit read is unchanged, and
only the selected source and responder score summands can change.
The responder's NEW worker price may read the untouched site e+2.

The genuine general-b (A)/(B) branch census remains an explicit
local row obligation; this module does not assert either unproved
row family as unconditional.
-/

namespace L3.RenewalReferenceClock

open L3.HeadlineRenewal
open FiniteUniformStoppingTree
open Classical

set_option autoImplicit false
set_option Elab.async false

/-- One summand in the actual inherited potential. -/
def bankInheritedScore {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank)
    (i : Fin n) : Nat :=
  bankInheritedSiteWeight
    (compileAdvice (ceilLogTwo n))
    (z.val.1 i)
    (z.val.1 (ring.rightNeighbor i)).pack.val
    (z.val.2.sites i)

theorem bankInheritedPotentialScoreSum {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank) :
    bankInheritedPotential ring hbank z =
      (List.ofFn (bankInheritedScore ring hbank z)).sum := rfl

/-- Modular right successor is injective. -/
private theorem bankInheritedSuccessorInjective {n : Nat}
    (ring : DirectedRing n) (i j : Fin n)
    (h : ring.rightNeighbor i = ring.rightNeighbor j) :
    i = j := by
  apply Fin.ext
  have hv := congrArg Fin.val h
  change (i.val + 1) % n = (j.val + 1) % n at hv
  have hi := i.isLt
  have hj := j.isLt
  by_cases he : i.val + 1 = n
  · by_cases hf : j.val + 1 = n
    · omega
    · have hsmall : j.val + 1 < n := by omega
      rw [he, Nat.mod_self, Nat.mod_eq_of_lt hsmall] at hv
      omega
  · have hsmall : i.val + 1 < n := by omega
    by_cases hf : j.val + 1 = n
    · rw [Nat.mod_eq_of_lt hsmall, hf, Nat.mod_self] at hv
      omega
    · have hsmall' : j.val + 1 < n := by omega
      rw [Nat.mod_eq_of_lt hsmall,
        Nat.mod_eq_of_lt hsmall'] at hv
      omega

/-- One changed Fin-index: no Finset, only List.ofFn. -/
private theorem bankInheritedScoreBalanceOne :
    ∀ (n : Nat) (f g : Fin n → Nat) (j : Fin n),
      (∀ i : Fin n, i ≠ j → f i = g i) →
      (List.ofFn f).sum + g j =
        (List.ofFn g).sum + f j := by
  intro n
  induction n with
  | zero =>
      intro f g j _
      exact Fin.elim0 j
  | succ n ih =>
      intro f g j hother
      rw [List.ofFn_succ, List.sum_cons,
        List.ofFn_succ, List.sum_cons]
      by_cases hj : j = 0
      · subst j
        have htail :
            (List.ofFn (fun i : Fin n => f i.succ)).sum =
              (List.ofFn (fun i : Fin n => g i.succ)).sum := by
          apply ofFn_sum_eq
          intro i
          apply hother i.succ
          intro hbad
          have hv := congrArg Fin.val hbad
          simp at hv
        rw [htail]
        omega
      · have hjpos : 0 < j.val := by
          have hjne : j.val ≠ 0 := by
            intro hz
            apply hj
            apply Fin.ext
            simpa using hz
          omega
        have hjbound : j.val < n + 1 := j.isLt
        obtain ⟨jpred, hjpred⟩ :
            ∃ k : Fin n, k.val = j.val - 1 :=
          ⟨⟨j.val - 1, by omega⟩, rfl⟩
        have hsucc : jpred.succ = j := by
          apply Fin.ext
          rw [Fin.val_succ, hjpred]
          omega
        have hhead : f 0 = g 0 :=
          hother 0 (Ne.symm hj)
        have htail := ih
          (fun i : Fin n => f i.succ)
          (fun i : Fin n => g i.succ)
          jpred
          (by
            intro i hi
            apply hother i.succ
            intro hbad
            apply hi
            apply Fin.ext
            have hv := congrArg Fin.val hbad
            change i.val + 1 = j.val at hv
            rw [hjpred]
            omega)
        rw [hsucc] at htail
        omega

/-- Two changed indices, a subtraction-free score balance. -/
private theorem bankInheritedScoreBalanceTwo
    {n : Nat} (f g : Fin n → Nat)
    (a b : Fin n) (hab : a ≠ b)
    (hother : ∀ i : Fin n, i ≠ a → i ≠ b → f i = g i) :
    (List.ofFn f).sum + g a + g b =
      (List.ofFn g).sum + f a + f b := by
  have ha :
      (List.ofFn (fun i : Fin n =>
        if i = a then f i else g i)).sum + g a =
      (List.ofFn g).sum + f a := by
    have h := bankInheritedScoreBalanceOne n
      (fun i : Fin n => if i = a then f i else g i)
      g a (by intro i hi; simp [hi])
    simpa using h
  have hb :
      (List.ofFn f).sum + g b =
      (List.ofFn (fun i : Fin n =>
        if i = a then f i else g i)).sum + f b := by
    have h := bankInheritedScoreBalanceOne n
      f (fun i : Fin n =>
        if i = a then f i else g i)
      b (by
        intro i hib
        by_cases hia : i = a
        · subst i
          simp
        · simp [hia, hother i hia hib])
    simpa [Ne.symm hab] using h
  omega

/-- The source PACK cannot change on an OLD selected BANK edge. -/
theorem bankInheritedSourcePackFrame
    {n : Nat} (ring : DirectedRing n) (hn : 2 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank) (e : Fin n) :
    (((bankValidRootedReferenceData ring hbank).referenceNext
        z e).val.1 e).pack.val = (z.val.1 e).pack.val := by
  have h := (rbBankReferencePairPack ring hn z.val e).1
  change (((renewalBankNext ring z.val e).1 e).pack.val) =
    (z.val.1 e).pack.val
  exact h

/-- Even an inherited worker immediately to the LEFT of e has
unchanged score: its neighbour PACK e remains unchanged. -/
theorem bankInheritedScoreOutsidePair
    {n : Nat} (ring : DirectedRing n) (hn : 2 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank) (e i : Fin n)
    (he : i ≠ e)
    (hd : i ≠ ring.rightNeighbor e) :
    bankInheritedScore ring hbank
        ((bankValidRootedReferenceData ring hbank).referenceNext
          z e) i =
      bankInheritedScore ring hbank z i := by
  have hsite := rbReferenceOutsideSiteFrame
    ring z.val e i he hd
  have hnotDest :
      ring.rightNeighbor i ≠ ring.rightNeighbor e := by
    intro h
    exact he (bankInheritedSuccessorInjective ring i e h)
  have hrole :
      (((bankValidRootedReferenceData ring hbank).referenceNext
          z e).val.1 (ring.rightNeighbor i)).pack.val =
        (z.val.1 (ring.rightNeighbor i)).pack.val := by
    by_cases hin : ring.rightNeighbor i = e
    · rw [hin]
      exact bankInheritedSourcePackFrame ring hn hbank z e
    · have hr := (rbReferenceOutsideSiteFrame ring z.val e
        (ring.rightNeighbor i) hin hnotDest).1
      change ((renewalBankNext ring z.val e).1
          (ring.rightNeighbor i)) =
        z.val.1 (ring.rightNeighbor i) at hr
      exact congrArg (fun a => a.pack.val) hr
  have hp :
      ((bankValidRootedReferenceData ring hbank).referenceNext
        z e).val.1 i = z.val.1 i := by
    change ((renewalBankNext ring z.val e).1 i) = _
    exact hsite.1
  have hg :
      ((bankValidRootedReferenceData ring hbank).referenceNext
        z e).val.2.sites i = z.val.2.sites i := by
    change ((renewalBankNext ring z.val e).2.sites i) = _
    exact hsite.2
  unfold bankInheritedScore
  rw [hp, hg, hrole]

/-- Exact two-score balance. Its second score may read the
unchanged e+2 PACK, but no other score summand changes. -/
theorem bankInheritedPotentialTwoSiteBalance
    {n : Nat} (ring : DirectedRing n) (hn : 2 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank) (e : Fin n) :
    bankInheritedPotential ring hbank
        ((bankValidRootedReferenceData ring hbank).referenceNext
          z e) +
      bankInheritedScore ring hbank z e +
      bankInheritedScore ring hbank z (ring.rightNeighbor e) =
    bankInheritedPotential ring hbank z +
      bankInheritedScore ring hbank
        ((bankValidRootedReferenceData ring hbank).referenceNext
          z e) e +
      bankInheritedScore ring hbank
        ((bankValidRootedReferenceData ring hbank).referenceNext
          z e) (ring.rightNeighbor e) := by
  have hdist : e ≠ ring.rightNeighbor e :=
    (Counter.resetRootPortDistinct ring e hn).symm
  have hsum := bankInheritedScoreBalanceTwo
    (fun i => bankInheritedScore ring hbank
      ((bankValidRootedReferenceData ring hbank).referenceNext
        z e) i)
    (bankInheritedScore ring hbank z)
    e (ring.rightNeighbor e) hdist
    (by
      intro i hi hj
      exact bankInheritedScoreOutsidePair
        ring hn hbank z e i hi hj)
  simpa only [bankInheritedPotentialScoreSum] using hsum

/-- The requested three-summand balance. The first summand is
the (unchanged) predecessor score; the two-site identity is
strictly stronger. The predecessor port equality is recorded
to make the geometry explicit. -/
theorem bankInheritedPotentialThreeSiteBalance
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank)
    (e pred : Fin n)
    (_hpred : ring.rightNeighbor pred = e)
    (hpredNe : pred ≠ e)
    (hpredOther : pred ≠ ring.rightNeighbor e) :
    bankInheritedPotential ring hbank
        ((bankValidRootedReferenceData ring hbank).referenceNext
          z e) +
      bankInheritedScore ring hbank z pred +
      bankInheritedScore ring hbank z e +
      bankInheritedScore ring hbank z (ring.rightNeighbor e) =
    bankInheritedPotential ring hbank z +
      bankInheritedScore ring hbank
        ((bankValidRootedReferenceData ring hbank).referenceNext
          z e) pred +
      bankInheritedScore ring hbank
        ((bankValidRootedReferenceData ring hbank).referenceNext
          z e) e +
      bankInheritedScore ring hbank
        ((bankValidRootedReferenceData ring hbank).referenceNext
          z e) (ring.rightNeighbor e) := by
  have hframe := bankInheritedScoreOutsidePair ring
    (by omega : 2 ≤ n) hbank z e pred hpredNe hpredOther
  have hpair := bankInheritedPotentialTwoSiteBalance
    ring (by omega : 2 ≤ n) hbank z e
  omega

/-- The local A row predicate, with ONLY the two score summands
which actually change. This is an exact, finite BANK two-site
row obligation, not an assumed global potential drift. -/
def BankInheritedNonarmedLocalRows
    {n : Nat} (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) :
    Prop :=
  ∀ (z : BankReferenceState ring hbank),
    BankInheritedReachable ring hbank z →
    bankInheritedStateAtomCount ring hbank z ≠ 0 →
    ∀ e : Fin n,
      bankInheritedArmedAtoms ring hbank z e = 0 →
      bankInheritedScore ring hbank
          ((bankValidRootedReferenceData ring hbank).referenceNext
            z e) e +
        bankInheritedScore ring hbank
          ((bankValidRootedReferenceData ring hbank).referenceNext
            z e) (ring.rightNeighbor e) +
        bankInheritedArmedEscrow ring hbank z
          (ring.rightNeighbor e) ≤
      bankInheritedScore ring hbank z e +
        bankInheritedScore ring hbank z (ring.rightNeighbor e) +
        bankInheritedArmedEscrow ring hbank z e

/-- Local B: outgoing ARMED nonnegative adjusted drift and
incoming ARMED strict margin. Both use the OLD selected edge.
The second clause explicitly carries the predecessor e with
rightNeighbor e = r, so it covers shared ARMED edges. -/
def BankInheritedArmedLocalRows
    {n : Nat} (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) :
    Prop :=
  (∀ (z : BankReferenceState ring hbank),
    BankInheritedReachable ring hbank z →
    bankInheritedStateAtomCount ring hbank z ≠ 0 →
    ∀ e : Fin n,
      0 < bankInheritedArmedAtoms ring hbank z e →
        bankInheritedScore ring hbank
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
  (∀ (z : BankReferenceState ring hbank),
    BankInheritedReachable ring hbank z →
    bankInheritedStateAtomCount ring hbank z ≠ 0 →
    ∀ (r e : Fin n),
      ring.rightNeighbor e = r →
      0 < bankInheritedArmedAtoms ring hbank z r →
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
          bankInheritedArmedEscrow ring hbank z e)

/-- A follows exactly from the local, two-score non-ARMED BANK
case census. The local row obligation is not yet discharged. -/
theorem bankInheritedNonarmedEdgeRowsOfLocal
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hloc : BankInheritedNonarmedLocalRows ring hbank) :
    BankInheritedNonarmedEdgeRows ring hbank := by
  intro z hz ha e hnot
  have hb := bankInheritedPotentialTwoSiteBalance
    ring (by omega : 2 ≤ n) hbank z e
  have hl := hloc z hz ha e hnot
  omega

/-- Outgoing ARMED inequality from the local pair census. -/
theorem bankInheritedArmedOutgoingOfLocal
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hloc : BankInheritedArmedLocalRows ring hbank)
    (z : BankReferenceState ring hbank)
    (hz : BankInheritedReachable ring hbank z)
    (ha : bankInheritedStateAtomCount ring hbank z ≠ 0)
    (e : Fin n)
    (harm : 0 < bankInheritedArmedAtoms ring hbank z e) :
    bankInheritedPotential ring hbank
        ((bankValidRootedReferenceData ring hbank).referenceNext
          z e) +
      bankInheritedArmedEscrow ring hbank z
        (ring.rightNeighbor e) ≤
      bankInheritedPotential ring hbank z +
        bankInheritedArmedEscrow ring hbank z e := by
  have hb := bankInheritedPotentialTwoSiteBalance
    ring (by omega : 2 ≤ n) hbank z e
  have hl := hloc.1 z hz ha e harm
  omega

/-- Incoming ARMED margin from the selected responder pair. -/
theorem bankInheritedArmedIncomingOfLocal
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hloc : BankInheritedArmedLocalRows ring hbank)
    (z : BankReferenceState ring hbank)
    (hz : BankInheritedReachable ring hbank z)
    (ha : bankInheritedStateAtomCount ring hbank z ≠ 0)
    (r e : Fin n)
    (he : ring.rightNeighbor e = r)
    (harm : 0 < bankInheritedArmedAtoms ring hbank z r) :
    bankInheritedPotential ring hbank
        ((bankValidRootedReferenceData ring hbank).referenceNext
          z e) +
      bankInheritedArmedEscrow ring hbank z
        (ring.rightNeighbor e) + n ≤
      bankInheritedPotential ring hbank z +
        bankInheritedArmedEscrow ring hbank z e := by
  have hb := bankInheritedPotentialTwoSiteBalance
    ring (by omega : 2 ≤ n) hbank z e
  have hl := hloc.2 z hz ha r e he harm
  omega

/-- Every ring site has its actual incoming scheduler edge. -/
private theorem bankInheritedPredecessorRight
    {n : Nat} (ring : DirectedRing n) (i : Fin n) :
    ring.rightNeighbor (ring.leftNeighbor i) = i := by
  apply Fin.ext
  simp only [DirectedRing.leftNeighbor, DirectedRing.rightNeighbor]
  by_cases hi : i.val = 0
  · rw [hi]
    have hlt : n - 1 < n := by omega
    rw [Nat.zero_add, Nat.mod_eq_of_lt hlt]
    have hs : n - 1 + 1 = n := by omega
    rw [hs, Nat.mod_self]
  · have heq : i.val + n - 1 = n + (i.val - 1) := by omega
    rw [heq, add_self_mod,
      Nat.mod_eq_of_lt (by omega : i.val - 1 < n)]
    have hs : i.val - 1 + 1 = i.val := by omega
    rw [hs, Nat.mod_eq_of_lt i.isLt]

/-- Both actual B conjuncts follow from the OLD selected-pair
local inequalities; shared ARMED roots require no edge matching. -/
theorem bankInheritedArmedEdgeRowsOfLocal
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hloc : BankInheritedArmedLocalRows ring hbank) :
    BankInheritedArmedEdgeRows ring hbank := by
  constructor
  · intro z hz ha e harm
    exact bankInheritedArmedOutgoingOfLocal
      ring hn hbank hloc z hz ha e harm
  · intro z hz ha r harm
    refine ⟨ring.leftNeighbor r,
      bankInheritedPredecessorRight ring r, ?_⟩
    exact bankInheritedArmedIncomingOfLocal ring hn hbank
      hloc z hz ha r (ring.leftNeighbor r)
      (bankInheritedPredecessorRight ring r) harm

/-- GENERAL b: an RR forward source encountering the wrong
responder PACK pays one unit of look-ahead repair credit. -/
theorem bankInheritedResetRepairWorkerStrict
    (b j neighborRole : Nat)
    (hj : j < b) (hbad : neighborRole ≠ j + 1) :
    bankInheritedWorkerPrice b .RR j (j + 1) + 1 =
      bankInheritedWorkerPrice b .RR j neighborRole := by
  obtain ⟨hbefore, hafter⟩ :=
    bankInheritedRRRepairCreditDischarged
      b j neighborRole hj hbad
  unfold bankInheritedWorkerPrice
  rw [hbefore, hafter]

/-- GENERAL b: one incoming tick of an inherited waiting
controller pays exactly n, if its old lease exceeds one. This
is the independent lease component, not the full mixed pair row. -/
theorem bankInheritedWaitingLeaseTickStrict
    (b n lease : Nat) (hlease : 1 < lease) :
    n * (bankInheritedComparisonPrice b +
      (lease - 1) + 1) + n =
    n * (bankInheritedComparisonPrice b + lease + 1) := by
  have hs : bankInheritedComparisonPrice b + (lease - 1) + 1 =
      bankInheritedComparisonPrice b + lease := by omega
  rw [hs]
  exact (Nat.mul_succ n _).symm

/-- Conditional R7 producer from the exact, falsifiable local
A and B row obligations plus the separately studied progress C.
It is intentionally NOT a theorem with only C as input, since
the general-b A/B branch classification has not been discharged. -/
theorem bankInheritedRetirementStageOfLocalRowsAndProgress
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hnonarmed : BankInheritedNonarmedLocalRows ring hbank)
    (harmed : BankInheritedArmedLocalRows ring hbank)
    (hprogress : BankInheritedProgressAlternative ring hbank) :
    StageInheritedAuthorityExtinction
      (bankValidRootedReferenceData ring hbank).referenceNext
      (BankInheritedRootedStart ring hbank)
      (fun z => headlineRooted ring z.val.1 ∧
        InheritedAuthorityExtinct ring hbank z)
      (ceilLogTwo n) := by
  exact bankInheritedRetirementStageOfEdgeRows
    ring hn hbank
    (bankInheritedNonarmedEdgeRowsOfLocal
      ring hn hbank hnonarmed)
    (bankInheritedArmedEdgeRowsOfLocal
      ring hn hbank harmed)
    hprogress

end L3.RenewalReferenceClock

#print axioms L3.RenewalReferenceClock.bankInheritedPotentialTwoSiteBalance
#print axioms L3.RenewalReferenceClock.bankInheritedNonarmedEdgeRowsOfLocal
#print axioms L3.RenewalReferenceClock.bankInheritedArmedEdgeRowsOfLocal
#print axioms L3.RenewalReferenceClock.bankInheritedRetirementStageOfLocalRowsAndProgress
