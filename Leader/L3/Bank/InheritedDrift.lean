import Leader.L3.Bank.InheritedPotential

/-!
R7 inherited-edge Bellman reduction.

This file does NOT assert A/B's literal row census, and does NOT
assert C's authentication/unreachability. The local obligations
are falsifiable predicates on the real BANK reference step.

A single root-specific escrow avoids double-counting the shared
scheduler edge of two adjacent inherited ARMED roots. The escrow
rotates around the directed ring and cancels in the full edge sum.
-/

namespace L3.RenewalReferenceClock

open L3.HeadlineRenewal
open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree
open Classical

set_option autoImplicit false
set_option Elab.async false

/-- Number of inherited atoms held by a physical role-zero
ARMED controller at this OLD reference state. -/
def bankInheritedArmedAtoms {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank) (i : Fin n) : Nat :=
  if (z.val.1 i).pack.val = 0 ∧
      (z.val.1 i).mode = .ARMED then
    bankInheritedControllerAtomCount (z.val.2.sites i).controller
  else 0

/-- An inherited ARMED atom worth A*n releases a conservative
(A-1)*n escrow on its incoming edge. The unused n pays one
scheduler step. This is an OLD-state credit, not extra ghost data. -/
def bankInheritedArmedEscrow {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank) (i : Fin n) : Nat :=
  n * (bankInheritedArmedPrice
        (compileAdvice (ceilLogTwo n)).b - 1) *
      bankInheritedArmedAtoms ring hbank z i

theorem bankInheritedArmedEscrowZero
    {n : Nat} (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank) (i : Fin n)
    (hzero : bankInheritedArmedAtoms ring hbank z i = 0) :
    bankInheritedArmedEscrow ring hbank z i = 0 := by
  simp [bankInheritedArmedEscrow, hzero]

/-- Hardest ARMED outgoing branch: inherited IR worker launched
at role one has phase price 3*b, on top of B=A+2D.
The original controller's incoming deletion pays for it. -/
theorem bankInheritedArmedWorkScalarBound (b : Nat) :
    1 + bankInheritedComparisonPrice b + 3 * b ≤
      2 * bankInheritedArmedPrice b := by
  unfold bankInheritedComparisonPrice
    bankInheritedArmedPrice bankInheritedWorkerCap
  omega

/-- The ARMED idle increment changes active mode to CSTART
while retaining the same inherited atom list. -/
theorem bankInheritedArmedIdleScalarBound (b : Nat) :
    1 + bankInheritedComparisonPrice b ≤
      2 * bankInheritedArmedPrice b := by
  unfold bankInheritedComparisonPrice
    bankInheritedArmedPrice bankInheritedWorkerCap
  omega

/-- Incoming erasure of an ARMED controller pays its escrow
and one additional per-atom unit, without any probability lemma. -/
theorem bankInheritedArmedIncomingScalarBound (b : Nat) :
    1 + (bankInheritedArmedPrice b - 1) ≤
      bankInheritedArmedPrice b := by
  unfold bankInheritedArmedPrice bankInheritedWorkerCap
  omega

/-- (A) strengthened by the responder's inherited-ARMED erasure.
This is the exact OLD-state local row inequality needed when
the selected edge is NOT sourced by an inherited ARMED controller.
The ordinary raw A inequality follows immediately. The proof
from renewalBankPairMemory's branch census is still open. -/
def BankInheritedNonarmedEdgeRows {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) :
    Prop :=
  ∀ z : BankReferenceState ring hbank,
    BankInheritedReachable ring hbank z →
      bankInheritedStateAtomCount ring hbank z ≠ 0 →
      ∀ e : Fin n,
        bankInheritedArmedAtoms ring hbank z e = 0 →
          bankInheritedPotential ring hbank
              ((bankValidRootedReferenceData ring hbank).referenceNext
                z e) +
            bankInheritedArmedEscrow ring hbank z
              (ring.rightNeighbor e) ≤
          bankInheritedPotential ring hbank z +
            bankInheritedArmedEscrow ring hbank z e

/-- (B) outgoing ARMED edge budget and incoming ARMED margin.
The second conjunct deliberately asks for the actual predecessor
edge; no disjoint pairing of multiple adjacent roots is assumed.
This is a concrete row-family obligation, not yet a theorem. -/
def BankInheritedArmedEdgeRows {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) :
    Prop :=
  (∀ z : BankReferenceState ring hbank,
    BankInheritedReachable ring hbank z →
      bankInheritedStateAtomCount ring hbank z ≠ 0 →
      ∀ e : Fin n,
        0 < bankInheritedArmedAtoms ring hbank z e →
          bankInheritedPotential ring hbank
              ((bankValidRootedReferenceData ring hbank).referenceNext
                z e) +
            bankInheritedArmedEscrow ring hbank z
              (ring.rightNeighbor e) ≤
          bankInheritedPotential ring hbank z +
            bankInheritedArmedEscrow ring hbank z e) ∧
  (∀ z : BankReferenceState ring hbank,
    BankInheritedReachable ring hbank z →
      bankInheritedStateAtomCount ring hbank z ≠ 0 →
      ∀ r : Fin n,
        0 < bankInheritedArmedAtoms ring hbank z r →
          ∃ e : Fin n, ring.rightNeighbor e = r ∧
            bankInheritedPotential ring hbank
                ((bankValidRootedReferenceData ring hbank).referenceNext
                  z e) +
              bankInheritedArmedEscrow ring hbank z
                (ring.rightNeighbor e) + n ≤
            bankInheritedPotential ring hbank z +
              bankInheritedArmedEscrow ring hbank z e)

/-- (C) the exact still-open progress/authentication statement.
Without an inherited ARMED controller, some inherited worker or
waiting/CSTART controller must have a strictly paying edge.
The zero-atom return-token CSTART stall is the explicit residual.
This is a Prop, NOT a proved reachability assertion. -/
def BankInheritedProgressAlternative {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) :
    Prop :=
  ∀ z : BankReferenceState ring hbank,
    BankInheritedReachable ring hbank z →
      bankInheritedStateAtomCount ring hbank z ≠ 0 →
      (∃ e : Fin n,
        bankInheritedPotential ring hbank
            ((bankValidRootedReferenceData ring hbank).referenceNext
              z e) + n ≤
          bankInheritedPotential ring hbank z) ∨
      (∃ r : Fin n,
        0 < bankInheritedArmedAtoms ring hbank z r)

/-- Actual A on a non-ARMED source, conditional only on the
stronger responder-erasure row census above. -/
theorem bankInheritedNonarmedRawDropOfRows
    {n : Nat} (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hrows : BankInheritedNonarmedEdgeRows ring hbank)
    (z : BankReferenceState ring hbank)
    (hz : BankInheritedReachable ring hbank z)
    (hatoms : bankInheritedStateAtomCount ring hbank z ≠ 0)
    (e : Fin n)
    (hsource : bankInheritedArmedAtoms ring hbank z e = 0) :
    bankInheritedPotential ring hbank
        ((bankValidRootedReferenceData ring hbank).referenceNext
          z e) ≤
      bankInheritedPotential ring hbank z := by
  have hrow := hrows z hz hatoms e hsource
  rw [bankInheritedArmedEscrowZero
    ring hbank z e hsource] at hrow
  omega

/-- Clockwise rotation is a permutation of Fin n. Proof copied
in its public Nat-sum form, using only the core list API. -/
private theorem bankInheritedEscrowRotation {n : Nat}
    (ring : DirectedRing n) (f : Fin n → Nat) :
    (List.ofFn (fun e : Fin n =>
      f (ring.rightNeighbor e))).sum =
    (List.ofFn f).sum := by
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero
    (Nat.ne_of_gt ring.hn)
  subst n
  rw [show List.ofFn
      (fun e : Fin (k + 1) => f (ring.rightNeighbor e)) =
    (List.ofFn (fun i : Fin k =>
      f (ring.rightNeighbor i.castSucc))) ++
      [f (ring.rightNeighbor (Fin.last k))] from
    List.ofFn_succ_last]
  rw [List.sum_append, List.sum_cons, List.sum_nil,
    Nat.add_zero, List.ofFn_succ, List.sum_cons]
  have hlast : ring.rightNeighbor (Fin.last k) = 0 := by
    apply Fin.ext
    simp [DirectedRing.rightNeighbor]
  have hsucc : ∀ i : Fin k,
      ring.rightNeighbor i.castSucc = i.succ := by
    intro i
    apply Fin.ext
    simp [DirectedRing.rightNeighbor,
      Nat.mod_eq_of_lt (by omega : i.val + 1 < k + 1)]
  rw [hlast]
  have hf :
      (fun i : Fin k => f (ring.rightNeighbor i.castSucc)) =
        (fun i : Fin k => f i.succ) := by
    funext i
    rw [hsucc]
  rw [hf]
  omega

/-- Exactly one scheduler edge has the chosen indicator. -/
private theorem bankInheritedEdgeSpike (n : Nat) :
    ∀ (chosen : Fin n) (v : Nat),
      (List.ofFn (fun e : Fin n =>
        if e = chosen then v else 0)).sum = v := by
  induction n with
  | zero =>
      intro chosen
      exact Fin.elim0 chosen
  | succ n ih =>
      intro chosen v
      refine Fin.cases ?_ ?_ chosen
      · rw [List.ofFn_succ, List.sum_cons]
        have ht :
            (List.ofFn (fun i : Fin n =>
              if i.succ = (0 : Fin (n + 1)) then v else 0)).sum = 0 := by
          have hh := ofFn_sum_eq
            (fun i : Fin n =>
              if i.succ = (0 : Fin (n + 1)) then v else 0)
            (fun _ : Fin n => 0)
            (by
              intro i
              have hn : i.succ ≠ (0 : Fin (n + 1)) := by
                intro he
                have hv := congrArg Fin.val he
                change i.val + 1 = 0 at hv
                omega
              rw [if_neg hn])
          simpa only [ofFn_sum_const, Nat.mul_zero] using hh
        simp [ht]
      · intro chosen
        rw [List.ofFn_succ, List.sum_cons]
        have hn : (0 : Fin (n + 1)) ≠ chosen.succ := by
          intro he
          have hv := congrArg Fin.val he
          change 0 = chosen.val + 1 at hv
          omega
        rw [if_neg hn, Nat.zero_add]
        have hh := ofFn_sum_eq
          (fun i : Fin n => if i.succ = chosen.succ then v else 0)
          (fun i : Fin n => if i = chosen then v else 0)
          (by intro i; simp only [Fin.succ_inj])
        rw [hh]
        exact ih chosen v

/-- From A's and B's concrete row laws, every edge satisfies
a nonnegative *adjusted* drift, with ARMED escrow telescoping. -/
private theorem bankInheritedEscrowEveryEdge
    {n : Nat} (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hA : BankInheritedNonarmedEdgeRows ring hbank)
    (hB : BankInheritedArmedEdgeRows ring hbank)
    (z : BankReferenceState ring hbank)
    (hz : BankInheritedReachable ring hbank z)
    (hatoms : bankInheritedStateAtomCount ring hbank z ≠ 0)
    (e : Fin n) :
    bankInheritedPotential ring hbank
        ((bankValidRootedReferenceData ring hbank).referenceNext z e) +
      bankInheritedArmedEscrow ring hbank z
        (ring.rightNeighbor e) ≤
      bankInheritedPotential ring hbank z +
        bankInheritedArmedEscrow ring hbank z e := by
  by_cases hzero : bankInheritedArmedAtoms ring hbank z e = 0
  · exact hA z hz hatoms e hzero
  · have hpositive :
        0 < bankInheritedArmedAtoms ring hbank z e := by
      omega
    exact hB.1 z hz hatoms e hpositive

/-- C plus the ARMED incoming margin yields ONE nominated edge
paying an extra n beyond the escrow flow. The non-ARMED case
uses the zero-escrow clause and C's raw paying edge. -/
private theorem bankInheritedEscrowNominated
    {n : Nat} (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hB : BankInheritedArmedEdgeRows ring hbank)
    (hC : BankInheritedProgressAlternative ring hbank)
    (z : BankReferenceState ring hbank)
    (hz : BankInheritedReachable ring hbank z)
    (hatoms : bankInheritedStateAtomCount ring hbank z ≠ 0) :
    ∃ chosen : Fin n,
      bankInheritedPotential ring hbank
          ((bankValidRootedReferenceData ring hbank).referenceNext
            z chosen) +
        bankInheritedArmedEscrow ring hbank z
          (ring.rightNeighbor chosen) + n ≤
      bankInheritedPotential ring hbank z +
        bankInheritedArmedEscrow ring hbank z chosen := by
  by_cases harm :
      ∃ r : Fin n,
        0 < bankInheritedArmedAtoms ring hbank z r
  · obtain ⟨r, hr⟩ := harm
    obtain ⟨chosen, _, hmargin⟩ :=
      hB.2 z hz hatoms r hr
    exact ⟨chosen, hmargin⟩
  · have hzero : ∀ i : Fin n,
        bankInheritedArmedAtoms ring hbank z i = 0 := by
      intro i
      by_cases h : bankInheritedArmedAtoms ring hbank z i = 0
      · exact h
      · have hp :
          0 < bankInheritedArmedAtoms ring hbank z i := by
          omega
        exact False.elim (harm ⟨i, hp⟩)
    rcases hC z hz hatoms with hpay | hfound
    · obtain ⟨chosen, hpay⟩ := hpay
      have hs :=
        bankInheritedArmedEscrowZero ring hbank z
          chosen (hzero chosen)
      have ht :=
        bankInheritedArmedEscrowZero ring hbank z
          (ring.rightNeighbor chosen)
          (hzero (ring.rightNeighbor chosen))
      refine ⟨chosen, ?_⟩
      simpa only [hs, ht, Nat.add_zero,
        Nat.zero_add] using hpay
    · exact False.elim (harm hfound)

/-- The promised *global* A+B+C ⇒ Bellman reduction, including
adjacent inherited ARMED roots. There is no edge matching and
therefore no shared-edge double assignment. -/
theorem bankInheritedBellmanOfEdgeRows
    {n : Nat} (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hA : BankInheritedNonarmedEdgeRows ring hbank)
    (hB : BankInheritedArmedEdgeRows ring hbank)
    (hC : BankInheritedProgressAlternative ring hbank)
    (z : BankReferenceState ring hbank)
    (hz : BankInheritedReachable ring hbank z)
    (hatoms : bankInheritedStateAtomCount ring hbank z ≠ 0) :
    n + (List.ofFn (fun e : Fin n =>
      bankInheritedPotential ring hbank
        ((bankValidRootedReferenceData ring hbank).referenceNext
          z e))).sum ≤
      n * bankInheritedPotential ring hbank z := by
  obtain ⟨chosen, hchosen⟩ :=
    bankInheritedEscrowNominated
      ring hbank hB hC z hz hatoms
  have hrow (e : Fin n) :
      bankInheritedPotential ring hbank
          ((bankValidRootedReferenceData ring hbank).referenceNext
            z e) +
        bankInheritedArmedEscrow ring hbank z
          (ring.rightNeighbor e) +
        (if e = chosen then n else 0) ≤
      bankInheritedPotential ring hbank z +
        bankInheritedArmedEscrow ring hbank z e := by
    by_cases he : e = chosen
    · subst e
      simpa using hchosen
    · have hbase := bankInheritedEscrowEveryEdge
        ring hbank hA hB z hz hatoms e
      simpa [he] using hbase
  have hsum :=
    ofFn_sum_le
      (fun e : Fin n =>
        bankInheritedPotential ring hbank
            ((bankValidRootedReferenceData ring hbank).referenceNext
              z e) +
          bankInheritedArmedEscrow ring hbank z
            (ring.rightNeighbor e) +
          (if e = chosen then n else 0))
      (fun e : Fin n =>
        bankInheritedPotential ring hbank z +
          bankInheritedArmedEscrow ring hbank z e)
      hrow
  simp only [ofFn_sum_add, ofFn_sum_const] at hsum
  rw [bankInheritedEscrowRotation ring
    (bankInheritedArmedEscrow ring hbank z)] at hsum
  rw [bankInheritedEdgeSpike n chosen n] at hsum
  omega

/-- Conditional R7 stage producer from the three explicit
row obligations. Reuses the merged reachable/zero-atom
infrastructure and its proven first-hit cost interface. -/
theorem bankInheritedRetirementStageOfEdgeRows
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hA : BankInheritedNonarmedEdgeRows ring hbank)
    (hB : BankInheritedArmedEdgeRows ring hbank)
    (hC : BankInheritedProgressAlternative ring hbank) :
    StageInheritedAuthorityExtinction
      (bankValidRootedReferenceData ring hbank).referenceNext
      (BankInheritedRootedStart ring hbank)
      (fun z => headlineRooted ring z.val.1 ∧
        InheritedAuthorityExtinct ring hbank z)
      (ceilLogTwo n) := by
  intro z hz
  obtain ⟨seed, _, hstart⟩ := hz
  have hreach : BankInheritedReachable ring hbank z := by
    rw [hstart]
    exact bankInheritedReachableStart ring hbank seed
  apply (UniformFirstHit.expectedHittingTimeAtMost_iff_cost
    (bankValidRootedReferenceData ring hbank).referenceNext
    (fun u => headlineRooted ring u.val.1 ∧
      InheritedAuthorityExtinct ring hbank u)
    ring.hn z
    (headlineInheritedRate (ceilLogTwo n) * n ^ 2)).2
  intro T
  have hcompare :=
    L3.Counter.resetClockCostLeOfStoppedSimulation
      (bankValidRootedReferenceData ring hbank).referenceNext
      (bankValidRootedReferenceData ring hbank).referenceNext
      (fun u => headlineRooted ring u.val.1 ∧
        InheritedAuthorityExtinct ring hbank u)
      (fun u => bankInheritedStateAtomCount ring hbank u = 0)
      (fun u v => u = v ∧ BankInheritedReachable ring hbank u)
      (fun u v huv hzero => by
        rcases huv with ⟨rfl, hu⟩
        obtain ⟨s, pre, hrep⟩ := hu.2
        exact ⟨hu.1,
          bankInheritedZeroExtinct
            ring hn hbank s pre u hrep hzero⟩)
      (fun u v e huv _ _ => by
        rcases huv with ⟨rfl, hu⟩
        exact ⟨rfl, bankInheritedReachableStep
          ring hn hbank u hu e⟩)
      z z ⟨rfl, hreach⟩ T
  have hpotential :=
    L3.Prob.costNumerator_le_of_potential_on
      (bankValidRootedReferenceData ring hbank).referenceNext
      (fun u => bankInheritedStateAtomCount ring hbank u = 0)
      (BankInheritedReachable ring hbank)
      (bankInheritedPotential ring hbank)
      (fun u hu _ e =>
        bankInheritedReachableStep ring hn hbank u hu e)
      (fun u hu hnonzero =>
        bankInheritedBellmanOfEdgeRows
          ring hbank hA hB hC u hu hnonzero)
      z hreach T
  have hstartBound :
      bankInheritedPotential ring hbank z ≤
        (116 * (compileAdvice (ceilLogTwo n)).b + 232) * n ^ 2 := by
    rw [hstart]
    exact bankInheritedPotentialStartLe ring hbank seed
  have hcost :=
    Nat.le_trans hcompare
      (Nat.le_trans hpotential
        (Nat.mul_le_mul_left (n ^ T) hstartBound))
  rw [bankInheritedHeadlineRateBankEq
    (ceilLogTwo n) hbank]
  exact hcost

end L3.RenewalReferenceClock

#print axioms L3.RenewalReferenceClock.bankInheritedArmedWorkScalarBound
#print axioms L3.RenewalReferenceClock.bankInheritedBellmanOfEdgeRows
#print axioms L3.RenewalReferenceClock.bankInheritedRetirementStageOfEdgeRows
