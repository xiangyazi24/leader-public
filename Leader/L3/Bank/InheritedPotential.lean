import Leader.L3.Bank.InheritedRate
import Leader.L3.RenewalGrantStage

/-!
R7 repair-aware inherited-atom potential.

The RR repair credit reads the right neighbour's physical PACK.
An inherited RR moving to that neighbour acquires a new credit
depending on a third physical PACK site. The finite census therefore
does not justify an old-two-site-fields-only formula for Delta_e.

The independent-per-label site condition is refuted by a CSTART blocker. A nominated payable-site ledger is specified, not proved.
-/

namespace L3.RenewalReferenceClock

open L3.HeadlineRenewal
open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree
open Classical

set_option autoImplicit false
set_option Elab.async false

def bankInheritedWorkerCap (b : Nat) : Nat := 4 * b + 4
def bankInheritedWaitingCap (b : Nat) : Nat := 13 * (b + 2)

def bankInheritedArmedPrice (b : Nat) : Nat :=
  4 * bankInheritedWorkerCap b + 4

def bankInheritedComparisonPrice (b : Nat) : Nat :=
  bankInheritedArmedPrice b + 2 * bankInheritedWorkerCap b

def bankInheritedWorkerPhasePrice (b : Nat)
    (tok : BTok) (role : Nat) : Nat :=
  match tok with
  | .RR | .IR | .CR0 | .CR1 => 2 * (b - role) + b + 2
  | .RL | .AL | .CL0 | .CL1 => min role b + 1
  | .E => 0

def bankInheritedWorkerBasePrice (b : Nat) (tok : BTok) : Nat :=
  match tok with
  | .IR | .AL => bankInheritedComparisonPrice b
  | .CL1 | .E => 0
  | _ => bankInheritedArmedPrice b

/-- Unit credit for an inherited reset worker which needs to
repair the right neighbour's PACK role before advancing. -/
def bankInheritedRRRepairCredit
    (b role neighborRole : Nat) (tok : BTok) : Nat :=
  if tok = .RR ∧ packNext role neighborRole b ≠ neighborRole
  then 1 else 0

theorem bankInheritedRRRepairCreditLe
    (b role neighborRole : Nat) (tok : BTok) :
    bankInheritedRRRepairCredit b role neighborRole tok ≤ 1 := by
  unfold bankInheritedRRRepairCredit
  split <;> omega

def bankInheritedWorkerPrice
    (b : Nat) (tok : BTok)
    (role neighborRole : Nat) : Nat :=
  bankInheritedWorkerBasePrice b tok +
    bankInheritedWorkerPhasePrice b tok role +
      bankInheritedRRRepairCredit b role neighborRole tok

theorem bankInheritedWorkerPhasePriceLe
    (b : Nat) (tok : BTok) (role : Nat) :
    bankInheritedWorkerPhasePrice b tok role ≤
      bankInheritedWorkerCap b := by
  have hm : min role b ≤ b := Nat.min_le_right role b
  cases tok <;>
    simp [bankInheritedWorkerPhasePrice,
      bankInheritedWorkerCap] <;>
    omega

theorem bankInheritedWorkerPriceLe
    (b : Nat) (tok : BTok) (role neighborRole : Nat) :
    bankInheritedWorkerPrice b tok role neighborRole ≤
      bankInheritedComparisonPrice b +
        bankInheritedWorkerCap b + 1 := by
  have hphase := bankInheritedWorkerPhasePriceLe b tok role
  have hrepair :=
    bankInheritedRRRepairCreditLe b role neighborRole tok
  have hbase :
      bankInheritedWorkerBasePrice b tok ≤
        bankInheritedComparisonPrice b := by
    cases tok <;>
      simp [bankInheritedWorkerBasePrice,
        bankInheritedComparisonPrice,
        bankInheritedArmedPrice, bankInheritedWorkerCap] <;>
      omega
  unfold bankInheritedWorkerPrice
  omega

/-- This weight is zero when there are no inherited atoms on a
site, regardless of a fresh origin or pending reset receipt. -/
def bankInheritedSiteWeight {n : Nat}
    (c : Compiled) (x : Agent c)
    (neighborRole : Nat)
    (s : RenewalBankSite n) : Nat :=
  (match s.worker with
   | .payload p =>
       n * bankInheritedWorkerPrice c.b
         x.tok x.pack.val neighborRole * p.atoms.length
   | _ => 0) +
  (match s.controller with
   | .active p =>
       n * (if x.mode = .ARMED then
         bankInheritedArmedPrice c.b
         else bankInheritedComparisonPrice c.b) *
           p.atoms.length
   | .waiting atoms =>
       n * (bankInheritedComparisonPrice c.b +
         x.lease.val + 1) * atoms.length
   | .empty => 0)

/-- The literal BANK reference potential, not a history witness. -/
def bankInheritedPotential {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank) : Nat :=
  (List.ofFn (fun i : Fin n =>
    bankInheritedSiteWeight
      (compileAdvice (ceilLogTwo n))
      (z.val.1 i)
      (z.val.1 (ring.rightNeighbor i)).pack.val
      (z.val.2.sites i))).sum

private theorem bankInheritedPriceMulLe
    (n a upper stock : Nat)
    (ha : a ≤ upper) (hstock : stock ≤ 1) :
    n * a * stock ≤ n * upper := by
  calc
    n * a * stock ≤ n * a * 1 :=
      Nat.mul_le_mul_left (n * a) hstock
    _ = n * a := by simp
    _ ≤ n * upper := Nat.mul_le_mul_left n ha

/-! Generic stock bounds are split before specializing to the large
HeadlineConfiguration term, avoiding WHNF blowups. -/
private theorem bankInheritedSimpleWeightArithmetic
    (n a d l : Nat) :
    n * (a + d + 1) + n * (a + l + 1) =
      n * (2 * a + d + l + 2) := by
  rw [← Nat.mul_add]
  congr 1
  omega

private theorem bankInheritedWorkerWeightGeneric
    {n : Nat} (c : Compiled) (x : Agent c)
    (neighborRole : Nat) :
    ∀ w : RenewalBankWorker n,
      bankInheritedWorkerAtomCount w ≤ 1 →
      (match w with
       | .payload p =>
           n * bankInheritedWorkerPrice c.b x.tok
             x.pack.val neighborRole * p.atoms.length
       | _ => 0) ≤
      n * (bankInheritedComparisonPrice c.b +
        bankInheritedWorkerCap c.b + 1) := by
  intro w
  cases w with
  | empty =>
      intro _
      exact Nat.zero_le _
  | pending receipt =>
      intro _
      exact Nat.zero_le _
  | payload p =>
      intro h
      change p.atoms.length ≤ 1 at h
      exact bankInheritedPriceMulLe n _ _ p.atoms.length
        (bankInheritedWorkerPriceLe c.b x.tok
          x.pack.val neighborRole) h

private theorem bankInheritedControllerWeightGeneric
    {n : Nat} (c : Compiled) (x : Agent c)
    (hlease : x.lease.val ≤ bankInheritedWaitingCap c.b) :
    ∀ v : RenewalBankController n,
      bankInheritedControllerAtomCount v ≤ 1 →
      (match v with
       | .active p =>
           n * (if x.mode = .ARMED then
             bankInheritedArmedPrice c.b
             else bankInheritedComparisonPrice c.b) * p.atoms.length
       | .waiting xs =>
           n * (bankInheritedComparisonPrice c.b +
             x.lease.val + 1) * xs.length
       | .empty => 0) ≤
      n * (bankInheritedComparisonPrice c.b +
        bankInheritedWaitingCap c.b + 1) := by
  intro v
  cases v with
  | empty =>
      intro _
      exact Nat.zero_le _
  | active p =>
      intro h
      change p.atoms.length ≤ 1 at h
      have hp :
          (if x.mode = .ARMED then bankInheritedArmedPrice c.b
            else bankInheritedComparisonPrice c.b) ≤
          bankInheritedComparisonPrice c.b +
            bankInheritedWaitingCap c.b + 1 := by
        split
        · unfold bankInheritedComparisonPrice
          omega
        · omega
      exact bankInheritedPriceMulLe n _ _ p.atoms.length hp h
  | waiting xs =>
      intro h
      change xs.length ≤ 1 at h
      have hp :
          bankInheritedComparisonPrice c.b +
            x.lease.val + 1 ≤
          bankInheritedComparisonPrice c.b +
            bankInheritedWaitingCap c.b + 1 := by
        omega
      exact bankInheritedPriceMulLe n _ _ xs.length hp h

private theorem bankInheritedGenericSiteWeightLe
    {n : Nat} (c : Compiled) (x : Agent c)
    (neighborRole : Nat) (site : RenewalBankSite n)
    (hw : bankInheritedWorkerAtomCount site.worker ≤ 1)
    (hc : bankInheritedControllerAtomCount site.controller ≤ 1)
    (hl : x.lease.val ≤ bankInheritedWaitingCap c.b) :
    bankInheritedSiteWeight c x neighborRole site ≤
      n * (2 * bankInheritedComparisonPrice c.b +
        bankInheritedWorkerCap c.b +
        bankInheritedWaitingCap c.b + 2) := by
  have hwa := bankInheritedWorkerWeightGeneric
    c x neighborRole site.worker hw
  have hca := bankInheritedControllerWeightGeneric
    c x hl site.controller hc
  unfold bankInheritedSiteWeight
  have ha := Nat.add_le_add hwa hca
  have he := bankInheritedSimpleWeightArithmetic n
    (bankInheritedComparisonPrice c.b)
    (bankInheritedWorkerCap c.b)
    (bankInheritedWaitingCap c.b)
  rw [he] at ha
  exact ha

private theorem bankInheritedInitialWorkerStock
    {n : Nat} (C : HeadlineConfiguration n) (i : Fin n) :
    bankInheritedWorkerAtomCount
      (renewalBankInitialSite C i).worker ≤ 1 := by
  by_cases ht : (C i).tok = .E
  · simp [renewalBankInitialSite, ht,
      bankInheritedWorkerAtomCount]
  · simp [renewalBankInitialSite, ht,
      bankInheritedWorkerAtomCount,
      bankInheritedPayloadAtomCount,
      renewalBankEntrancePayload]

private theorem bankInheritedInitialControllerStock
    {n : Nat} (C : HeadlineConfiguration n) (i : Fin n) :
    bankInheritedControllerAtomCount
      (renewalBankInitialSite C i).controller ≤ 1 := by
  by_cases hrole : (C i).pack.val = 0
  · cases hm : (C i).mode <;>
      simp [renewalBankInitialSite, hrole, hm,
        bankInheritedControllerAtomCount,
        bankInheritedPayloadAtomCount,
        renewalBankEntrancePayload]
  · simp [renewalBankInitialSite, hrole,
      bankInheritedControllerAtomCount]

/-- Explicitly type the two separate match expressions BEFORE
combining their inequalities: the old calc-by-underscore failed
to unify these with dependent case-elimination proof terms. -/
theorem bankInheritedPotentialStartLe
    {n : Nat} (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) :
    bankInheritedPotential ring hbank
        ((bankValidRootedReferenceData ring hbank).referenceStart seed) ≤
      (116 * (compileAdvice (ceilLogTwo n)).b + 232) * n ^ 2 := by
  change
    (List.ofFn (fun i : Fin n =>
      bankInheritedSiteWeight
        (compileAdvice (ceilLogTwo n))
        (seed.val i)
        (seed.val (ring.rightNeighbor i)).pack.val
        (renewalBankInitialSite seed.val i))).sum ≤
      (116 * (compileAdvice (ceilLogTwo n)).b + 232) * n ^ 2
  have hsum :=
    ofFn_sum_le
      (fun i : Fin n =>
        bankInheritedSiteWeight
          (compileAdvice (ceilLogTwo n))
          (seed.val i)
          (seed.val (ring.rightNeighbor i)).pack.val
          (renewalBankInitialSite seed.val i))
      (fun _ : Fin n =>
        n * (2 * bankInheritedComparisonPrice
          (compileAdvice (ceilLogTwo n)).b +
          bankInheritedWorkerCap (compileAdvice (ceilLogTwo n)).b +
          bankInheritedWaitingCap (compileAdvice (ceilLogTwo n)).b +
          2))
      (fun i =>
        bankInheritedGenericSiteWeightLe
          (compileAdvice (ceilLogTwo n))
          (seed.val i)
          (seed.val (ring.rightNeighbor i)).pack.val
          (renewalBankInitialSite seed.val i)
          (bankInheritedInitialWorkerStock seed.val i)
          (bankInheritedInitialControllerStock seed.val i)
          (by
            have hlease := (seed.val i).lease.isLt
            change (seed.val i).lease.val <
              bankInheritedWaitingCap
                (compileAdvice (ceilLogTwo n)).b + 1 at hlease
            omega))
  rw [ofFn_sum_const] at hsum
  have hcoeff :
      2 * bankInheritedComparisonPrice
          (compileAdvice (ceilLogTwo n)).b +
        bankInheritedWorkerCap (compileAdvice (ceilLogTwo n)).b +
        bankInheritedWaitingCap (compileAdvice (ceilLogTwo n)).b +
        2 ≤
      116 * (compileAdvice (ceilLogTwo n)).b + 232 := by
    unfold bankInheritedComparisonPrice bankInheritedArmedPrice
      bankInheritedWorkerCap bankInheritedWaitingCap
    omega
  calc
    (List.ofFn (fun i : Fin n =>
      bankInheritedSiteWeight
        (compileAdvice (ceilLogTwo n))
        (seed.val i)
        (seed.val (ring.rightNeighbor i)).pack.val
        (renewalBankInitialSite seed.val i))).sum ≤
      n * (n *
        (2 * bankInheritedComparisonPrice
          (compileAdvice (ceilLogTwo n)).b +
          bankInheritedWorkerCap (compileAdvice (ceilLogTwo n)).b +
          bankInheritedWaitingCap (compileAdvice (ceilLogTwo n)).b +
          2)) :=
      hsum
    _ = (2 * bankInheritedComparisonPrice
          (compileAdvice (ceilLogTwo n)).b +
        bankInheritedWorkerCap (compileAdvice (ceilLogTwo n)).b +
        bankInheritedWaitingCap (compileAdvice (ceilLogTwo n)).b + 2) *
          n ^ 2 := by
      simp only [Nat.pow_two, Nat.mul_assoc,
        Nat.mul_comm, Nat.mul_left_comm]
    _ ≤ (116 * (compileAdvice (ceilLogTwo n)).b + 232) *
          n ^ 2 :=
      Nat.mul_le_mul_right (n ^ 2) hcoeff


/- A directly checkable part of the physical repair subcase:
an RR at role j<b facing a mismatched neighbour has one unit
of repair debt; after that neighbour's PACK is set to j+1 the
debt is zero, without moving or duplicating the worker atom. -/
/-- A mismatched RR forward interaction pays one unit of repair
credit by fixing the next PACK role; no old atom is copied. -/
theorem bankInheritedRRRepairCreditDischarged
    (b j neighborRole : Nat)
    (hj : j < b) (hbad : neighborRole ≠ j + 1) :
    bankInheritedRRRepairCredit b j neighborRole .RR = 1 ∧
    bankInheritedRRRepairCredit b j (j + 1) .RR = 0 := by
  have hbadRev : j + 1 ≠ neighborRole := Ne.symm hbad
  have hp : packNext j neighborRole b = j + 1 := by
    simp [packNext, hj]
  have hgood : packNext j (j + 1) b = j + 1 := by
    simp [packNext, hj]
  constructor
  · simp [bankInheritedRRRepairCredit, hp, hbadRev]
  · simp [bankInheritedRRRepairCredit, hgood]

def BankInheritedReachable {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank) : Prop :=
  headlineRooted ring z.val.1 ∧
    ∃ seed : RootedSeed ring, ∃ pre : List (Fin n),
      z.val = rbRun ring (renewalBankStart ring seed) pre

theorem bankInheritedReachableStart {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) :
    BankInheritedReachable ring hbank
      ((bankValidRootedReferenceData ring hbank).referenceStart seed) := by
  constructor
  · change headlineRooted ring seed.val
    exact seed.property
  · exact ⟨seed, [], rfl⟩

theorem bankInheritedReachableStep {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank)
    (hz : BankInheritedReachable ring hbank z)
    (e : Fin n) :
    BankInheritedReachable ring hbank
      ((bankValidRootedReferenceData ring hbank).referenceNext z e) := by
  constructor
  · exact bankReferenceRootedStep ring hn hbank z e hz.1
  · obtain ⟨seed, pre, hrep⟩ := hz.2
    exact ⟨seed, pre ++ [e],
      bankInheritedReferenceStepReplay
        ring hbank seed pre z hrep e⟩

/-- The R7 consumer's start-only rooted class; the potential need
not have a uniform cap on arbitrarily late reachable states. -/
def BankInheritedRootedStart {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank) : Prop :=
  ∃ seed : RootedSeed ring,
    ¬ headlineGeneratedTarget ring seed.val ∧
      z = (bankValidRootedReferenceData ring hbank).referenceStart seed

/- The finite LOCAL drift interface. One involution matches each
armed outgoing edge with its incoming erasure; all other edges
may be fixed points. Every paired TWO-EDGE inequality is on the
actual BANK reference successor, not an invented ghost step.
The nominated edge pays n in that pair. The reindexing equality
is stated explicitly as an elementary combinatorial side
condition (provable for any involution via its Fin equivalence).

Crucially this does not existentially postulate a potential or the
Bellman inequality: bankInheritedPotential was defined above,
and every row of this Prop is independently falsifiable by a
single literal old BANK reference state. -/
/-!
The stronger user-proposed condition "every old inherited label at i
pays n from its own incoming+outgoing services" is refuted at the
initial CSTART/AL window. The
corrected cost currency permits an inherited blocking return worker
to pay the root's obstructed service via a cross-label attribution.

The four local functions below are EXPLICIT PARAMETERS to a row
census: the unproved work is to define them by the actual BANK
transition and prove these per-edge, per-site obligations. This is
not an existentially chosen potential or a claimed R7 producer.
-/

/-- Positive and negative halves of an outgoing attributed change. -/
def bankInheritedOutChange {n : Nat}
    (paid debt : Fin n → Nat) (i : Fin n) : Int :=
  (paid i : Int) - (debt i : Int)

/-- Positive and negative halves of an incoming attributed change. -/
def bankInheritedInChange {n : Nat}
    (paid debt : Fin n → Nat) (i : Fin n) : Int :=
  (paid i : Int) - (debt i : Int)

/-- Corrected local signed attribution interface.
Each scheduler edge changes Phi by the given double-entry record;
a single nominated *paying site* pays n, and no other site goes
net negative. The two incoming reindex equations are finite ring
identities, not probabilistic assumptions.

The out/in functions are parameters to be computed from the literal
old pair, including the deletion of mismatched inherited return
workers. This differs from the false per-old-label demand. -/
def BankInheritedSiteDrift {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (outPaid inPaid outDebt inDebt :
      BankReferenceState ring hbank → Fin n → Nat) : Prop :=
  ∀ z : BankReferenceState ring hbank,
    BankInheritedReachable ring hbank z →
    bankInheritedStateAtomCount ring hbank z ≠ 0 →
    ∃ nominated : Fin n,
      (∀ e : Fin n,
        bankInheritedPotential ring hbank
            ((bankValidRootedReferenceData ring hbank).referenceNext z e) +
          outPaid z e + inPaid z (ring.rightNeighbor e) =
        bankInheritedPotential ring hbank z +
          outDebt z e + inDebt z (ring.rightNeighbor e)) ∧
      (∀ i : Fin n,
        outDebt z i + inDebt z i +
          (if i = nominated then n else 0) ≤
        outPaid z i + inPaid z i) ∧
      (List.ofFn (fun e : Fin n =>
        inPaid z (ring.rightNeighbor e))).sum =
        (List.ofFn (inPaid z)).sum ∧
      (List.ofFn (fun e : Fin n =>
        inDebt z (ring.rightNeighbor e))).sum =
        (List.ofFn (inDebt z)).sum

/-- Scalar Int identity: keep omega away from the compiled BANK
potential by treating its values as opaque natural numbers. -/
private theorem bankInheritedIntAttributionArithmetic
    (old new outPay inPay outDebt inDebt : Nat)
    (hrow : new + outPay + inPay =
      old + outDebt + inDebt) :
    (old : Int) - (new : Int) =
      ((outPay : Int) - (outDebt : Int)) +
        ((inPay : Int) - (inDebt : Int)) := by
  omega

/-- Exact Int edge identity, conditional on the supplied literal
Nat row equality; the actual attribution producer remains open. -/
theorem bankInheritedEdgeAttributionIdentity
    {n : Nat} (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (outPaid inPaid outDebt inDebt :
      BankReferenceState ring hbank → Fin n → Nat)
    (z : BankReferenceState ring hbank) (e : Fin n)
    (hrow :
      bankInheritedPotential ring hbank
          ((bankValidRootedReferenceData ring hbank).referenceNext z e) +
        outPaid z e + inPaid z (ring.rightNeighbor e) =
      bankInheritedPotential ring hbank z +
        outDebt z e + inDebt z (ring.rightNeighbor e)) :
    (bankInheritedPotential ring hbank z : Int) -
      (bankInheritedPotential ring hbank
        ((bankValidRootedReferenceData ring hbank).referenceNext z e) : Int) =
      bankInheritedOutChange (outPaid z) (outDebt z) e +
        bankInheritedInChange (inPaid z) (inDebt z)
          (ring.rightNeighbor e) := by
  exact bankInheritedIntAttributionArithmetic
    (bankInheritedPotential ring hbank z)
    (bankInheritedPotential ring hbank
      ((bankValidRootedReferenceData ring hbank).referenceNext z e))
    (outPaid z e) (inPaid z (ring.rightNeighbor e))
    (outDebt z e) (inDebt z (ring.rightNeighbor e))
    hrow

private theorem bankInheritedOneSpike (n : Nat) :
    ∀ (a : Fin n) (v : Nat),
      (List.ofFn (fun e : Fin n =>
        if e = a then v else 0)).sum = v := by
  induction n with
  | zero =>
      intro a
      exact Fin.elim0 a
  | succ n ih =>
      intro a v
      refine Fin.cases ?_ ?_ a
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
      · intro a
        rw [List.ofFn_succ, List.sum_cons]
        have hn : (0 : Fin (n + 1)) ≠ a.succ := by
          intro he
          have hv := congrArg Fin.val he
          change 0 = a.val + 1 at hv
          omega
        rw [if_neg hn, Nat.zero_add]
        have hh := ofFn_sum_eq
          (fun i : Fin n => if i.succ = a.succ then v else 0)
          (fun i : Fin n => if i = a then v else 0)
          (by intro i; simp only [Fin.succ_inj])
        rw [hh]
        exact ih a v

/- A complete finite pair-census (if supplied) implies the
global Bellman inequality by summing matched edges twice. -/
/-- The global Bellman inequality is the sum of the actual edge
balances and one nominated site's net positive contribution.
No edge involution and no unstated independence are required. -/
theorem bankInheritedPotentialBellmanOfLocalDrift
    {n : Nat} (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (outPaid inPaid outDebt inDebt :
      BankReferenceState ring hbank → Fin n → Nat)
    (hlocal : BankInheritedSiteDrift
      ring hbank outPaid inPaid outDebt inDebt)
    (z : BankReferenceState ring hbank)
    (hz : BankInheritedReachable ring hbank z)
    (hzero : bankInheritedStateAtomCount ring hbank z ≠ 0) :
    n + (List.ofFn (fun e : Fin n =>
      bankInheritedPotential ring hbank
        ((bankValidRootedReferenceData ring hbank).referenceNext z e))).sum ≤
      n * bankInheritedPotential ring hbank z := by
  obtain ⟨nominated, hrow, hbudget, hpaid, hdebt⟩ :=
    hlocal z hz hzero
  have hsumRow := ofFn_sum_eq
    (fun e : Fin n =>
      bankInheritedPotential ring hbank
        ((bankValidRootedReferenceData ring hbank).referenceNext z e) +
      outPaid z e + inPaid z (ring.rightNeighbor e))
    (fun e : Fin n =>
      bankInheritedPotential ring hbank z +
      outDebt z e + inDebt z (ring.rightNeighbor e))
    hrow
  simp only [ofFn_sum_add, ofFn_sum_const] at hsumRow
  rw [hpaid, hdebt] at hsumRow
  have hsite := ofFn_sum_le
    (fun i : Fin n =>
      outDebt z i + inDebt z i +
        (if i = nominated then n else 0))
    (fun i : Fin n => outPaid z i + inPaid z i)
    hbudget
  simp only [ofFn_sum_add] at hsite
  rw [bankInheritedOneSpike n nominated n] at hsite
  omega

theorem bankInheritedRetirementStageOfLocalDrift
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (outPaid inPaid outDebt inDebt :
      BankReferenceState ring hbank → Fin n → Nat)
    (hlocal : BankInheritedSiteDrift
      ring hbank outPaid inPaid outDebt inDebt) :
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
        bankInheritedPotentialBellmanOfLocalDrift
          ring hbank outPaid inPaid outDebt inDebt
          hlocal u hu hnonzero)
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


#print axioms L3.RenewalReferenceClock.bankInheritedPotentialStartLe
#print axioms L3.RenewalReferenceClock.bankInheritedPotentialBellmanOfLocalDrift
#print axioms L3.RenewalReferenceClock.bankInheritedRetirementStageOfLocalDrift
