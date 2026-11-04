import Leader.Wu.Seal.SweepProtocol

/-!
# Weak-fair concurrency obstruction for deterministic anonymous ring protocols

The serialized seal sweep has an exact length-`n` escape, but weak edge
fairness does not force serialization: it admits paired competing copies of
the same local computation.  This is not a missing transition case of that
particular overlay.

For an arbitrary deterministic anonymous protocol, repeat any three-site word
twice on a six-site ring.  The weakly fair periodic edge word

`0, 3, 1, 4, 2, 5`

executes the two copies of each base edge consecutively.  After every complete
block the word is again a double cover.  A double cover can never have exactly
one leader output.  Hence no intermediate point of this execution is safe:
every intermediate point can reach a later non-unique block boundary.

The protocol is universally quantified, so its state may already contain the
seal bit, one additional bit, any other fixed finite tag, or even values whose
type was chosen for the six-site instance.  `Configuration 3` below is only a
convenient seed for a period-three six-site word and a virtual quotient
calculation; no three-site correctness specification is assumed.  Thus the
argument also covers one `Q₆`/transition₆ member of an `n`-indexed family.
Arbitrary initialization permits the repeated word in every case.  Escaping
this obstruction therefore requires either a stronger scheduler condition, a
restriction on admissible initial configurations (for example, nonduplicable
immutable identifiers), or a symmetry-breaking resource not represented by
deterministic anonymous current-state transitions.  This file makes no claim
about such stronger models and does not weaken the accepted serialized escape
theorem.
-/

namespace PPLLCompleteMultiLeaderCleanup
namespace PPartialSealSweepConcurrencyNoGoSol

open PPLLResearchFormulation
open PPLLStaticDoubleCoverNoGo
open PPartialSealSweepOverlaySol
open PPartialMinimalLockStaleCounterexampleSol
open PPartialDynamicSweepLockSol
open PPartialDynamicSweepResetSol

set_option autoImplicit false

/-! ## Fixed rings, the double cover, and copy exchange -/

abbrev ringThree : DirectedRing 3 := ⟨by omega⟩

abbrev ringSix : DirectedRing 6 := ⟨by omega⟩

/-- Repeat a three-site word at offsets zero and three. -/
def periodThreeLift (P : PopulationProtocol)
    (C : P.Configuration 3) : P.Configuration 6 :=
  doubleCoverConfig P (by omega : 3 > 0) C

private theorem finSix_cases (i : Fin 6) :
    i = (0 : Fin 6) ∨ i = (1 : Fin 6) ∨ i = (2 : Fin 6) ∨
      i = (3 : Fin 6) ∨ i = (4 : Fin 6) ∨ i = (5 : Fin 6) := by
  by_cases h0 : i.val = 0
  · left
    exact Fin.ext h0
  by_cases h1 : i.val = 1
  · right
    left
    exact Fin.ext h1
  by_cases h2 : i.val = 2
  · right
    right
    left
    exact Fin.ext h2
  by_cases h3 : i.val = 3
  · right
    right
    right
    left
    exact Fin.ext h3
  by_cases h4 : i.val = 4
  · right
    right
    right
    right
    left
    exact Fin.ext h4
  · right
    right
    right
    right
    right
    apply Fin.ext
    omega

/-- Exchange the two period-three copies. -/
def toggleCopy (i : Fin 6) : Fin 6 :=
  ⟨(i.val + 3) % 6, Nat.mod_lt _ (by omega)⟩

theorem toggleCopy_ne (i : Fin 6) : toggleCopy i ≠ i := by
  rcases finSix_cases i with rfl | rfl | rfl | rfl | rfl | rfl <;>
    decide

theorem periodThreeLift_toggleCopy
    (P : PopulationProtocol) (C : P.Configuration 3) (i : Fin 6) :
    periodThreeLift P C (toggleCopy i) = periodThreeLift P C i := by
  rcases finSix_cases i with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rfl

/-- Copy symmetry itself rules out a unique leader, without a counting
argument and without assuming that either copy currently contains a leader. -/
theorem periodThreeLift_not_unique
    (P : PopulationProtocol) (isLeader : P.Y → Bool)
    (C : P.Configuration 3) :
    ¬ UniqueLeaderOutput P 6 (periodThreeLift P C) isLeader := by
  rintro ⟨root, hroot, honly⟩
  have hother :
      isLeader (P.output (periodThreeLift P C (toggleCopy root))) = true := by
    rw [periodThreeLift_toggleCopy]
    exact hroot
  exact toggleCopy_ne root (honly (toggleCopy root) hother)

/-! ## Paired execution of each base edge -/

/-- One round of the virtual three-site computation. -/
def baseRound (P : PopulationProtocol) (C : P.Configuration 3) :
    P.Configuration 3 :=
  runSchedule P ringThree C [0, 1, 2]

theorem paired_zero_steps
    (P : PopulationProtocol) (C : P.Configuration 3) :
    P.step ringSix (P.step ringSix (periodThreeLift P C) 0) 3 =
      periodThreeLift P (P.step ringThree C 0) := by
  funext i
  rcases finSix_cases i with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rfl

theorem paired_one_steps
    (P : PopulationProtocol) (C : P.Configuration 3) :
    P.step ringSix (P.step ringSix (periodThreeLift P C) 1) 4 =
      periodThreeLift P (P.step ringThree C 1) := by
  funext i
  rcases finSix_cases i with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rfl

/-- This includes the two wrap edges: base edge two updates `(2,0)`, while
the copied edges two and five update `(2,3)` and `(5,0)` respectively. -/
theorem paired_two_wrap_steps
    (P : PopulationProtocol) (C : P.Configuration 3) :
    P.step ringSix (P.step ringSix (periodThreeLift P C) 2) 5 =
      periodThreeLift P (P.step ringThree C 2) := by
  funext i
  rcases finSix_cases i with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rfl

/-- The literal paired block. -/
def pairedWord : List (Fin 6) := [0, 3, 1, 4, 2, 5]

theorem pairedWord_length : pairedWord.length = 6 := by
  rfl

/-- A complete paired block restores copy symmetry and performs exactly one
virtual round on the underlying three-site word. -/
theorem run_pairedWord_periodThreeLift
    (P : PopulationProtocol) (C : P.Configuration 3) :
    runSchedule P ringSix (periodThreeLift P C) pairedWord =
      periodThreeLift P (baseRound P C) := by
  change
    P.step ringSix
      (P.step ringSix
        (P.step ringSix
          (P.step ringSix
            (P.step ringSix
              (P.step ringSix (periodThreeLift P C) 0) 3) 1) 4) 2) 5 =
      periodThreeLift P
        (P.step ringThree
          (P.step ringThree (P.step ringThree C 0) 1) 2)
  rw [paired_zero_steps, paired_one_steps, paired_two_wrap_steps]

/-! ## A weakly fair infinite schedule -/

/-- Every directed edge is selected after every cutoff. -/
def WeakEdgeFair (schedule : Nat → Fin 6) : Prop :=
  ∀ e : Fin 6, ∀ t : Nat,
    ∃ u : Nat, t ≤ u ∧ schedule u = e

def pairedSchedule (t : Nat) : Fin 6 :=
  match t % 6 with
  | 0 => 0
  | 1 => 3
  | 2 => 1
  | 3 => 4
  | 4 => 2
  | _ => 5

private theorem pairedSchedule_phase_zero (q : Nat) :
    pairedSchedule (6 * q + 0) = (0 : Fin 6) := by
  apply Fin.ext
  simp [pairedSchedule]

private theorem pairedSchedule_phase_one (q : Nat) :
    pairedSchedule (6 * q + 1) = (3 : Fin 6) := by
  apply Fin.ext
  have hm : (6 * q + 1) % 6 = 1 := by omega
  simp [pairedSchedule, hm]

private theorem pairedSchedule_phase_two (q : Nat) :
    pairedSchedule (6 * q + 2) = (1 : Fin 6) := by
  apply Fin.ext
  have hm : (6 * q + 2) % 6 = 2 := by omega
  simp [pairedSchedule, hm]

private theorem pairedSchedule_phase_three (q : Nat) :
    pairedSchedule (6 * q + 3) = (4 : Fin 6) := by
  apply Fin.ext
  have hm : (6 * q + 3) % 6 = 3 := by omega
  simp [pairedSchedule, hm]

private theorem pairedSchedule_phase_four (q : Nat) :
    pairedSchedule (6 * q + 4) = (2 : Fin 6) := by
  apply Fin.ext
  have hm : (6 * q + 4) % 6 = 4 := by omega
  simp [pairedSchedule, hm]

private theorem pairedSchedule_phase_five (q : Nat) :
    pairedSchedule (6 * q + 5) = (5 : Fin 6) := by
  apply Fin.ext
  have hm : (6 * q + 5) % 6 = 5 := by omega
  simp [pairedSchedule, hm]

theorem pairedSchedule_weakEdgeFair : WeakEdgeFair pairedSchedule := by
  intro e t
  rcases finSix_cases e with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨6 * t + 0, by omega, pairedSchedule_phase_zero t⟩
  · exact ⟨6 * t + 2, by omega, pairedSchedule_phase_two t⟩
  · exact ⟨6 * t + 4, by omega, pairedSchedule_phase_four t⟩
  · exact ⟨6 * t + 1, by omega, pairedSchedule_phase_one t⟩
  · exact ⟨6 * t + 3, by omega, pairedSchedule_phase_three t⟩
  · exact ⟨6 * t + 5, by omega, pairedSchedule_phase_five t⟩

/-! ## The actual execution and recurring symmetric boundaries -/

def iterateBaseRound (P : PopulationProtocol) (C : P.Configuration 3) :
    Nat → P.Configuration 3
  | 0 => C
  | q + 1 => baseRound P (iterateBaseRound P C q)

/-- The actual trajectory generated by `pairedSchedule`; no state sequence is
postulated independently of the executable transition. -/
def pairedExecution (P : PopulationProtocol) (C : P.Configuration 3) :
    Nat → P.Configuration 6
  | 0 => periodThreeLift P C
  | t + 1 => P.step ringSix (pairedExecution P C t) (pairedSchedule t)

theorem pairedExecution_initial
    (P : PopulationProtocol) (C : P.Configuration 3) :
    pairedExecution P C 0 = periodThreeLift P C := by
  rfl

theorem pairedExecution_step
    (P : PopulationProtocol) (C : P.Configuration 3) (t : Nat) :
    P.step ringSix (pairedExecution P C t) (pairedSchedule t) =
      pairedExecution P C (t + 1) := by
  rfl

theorem pairedExecution_block_boundary
    (P : PopulationProtocol) (C : P.Configuration 3) (q : Nat) :
    pairedExecution P C (6 * q) =
      periodThreeLift P (iterateBaseRound P C q) := by
  induction q with
  | zero => rfl
  | succ q ih =>
      rw [Nat.mul_succ]
      change
        P.step ringSix
          (P.step ringSix
            (P.step ringSix
              (P.step ringSix
                (P.step ringSix
                  (P.step ringSix (pairedExecution P C (6 * q))
                    (pairedSchedule (6 * q + 0)))
                  (pairedSchedule (6 * q + 1)))
                (pairedSchedule (6 * q + 2)))
              (pairedSchedule (6 * q + 3)))
            (pairedSchedule (6 * q + 4)))
          (pairedSchedule (6 * q + 5)) =
        periodThreeLift P (baseRound P (iterateBaseRound P C q))
      rw [pairedSchedule_phase_zero, pairedSchedule_phase_one,
        pairedSchedule_phase_two, pairedSchedule_phase_three,
        pairedSchedule_phase_four, pairedSchedule_phase_five, ih]
      exact run_pairedWord_periodThreeLift P (iterateBaseRound P C q)

/-! ## Every point has a reachable non-unique future -/

theorem pairedExecution_reachable_add
    (P : PopulationProtocol) (C : P.Configuration 3)
    (t k : Nat) :
    PopulationProtocol.Reachable P ringSix
      (pairedExecution P C t) (pairedExecution P C (t + k)) := by
  induction k with
  | zero =>
      exact PopulationProtocol.Reachable.refl (pairedExecution P C t)
  | succ k ih =>
      rw [Nat.add_succ]
      exact PopulationProtocol.Reachable.step
        (pairedExecution P C t)
        (pairedExecution P C (t + k))
        (pairedExecution P C (t + k + 1))
        ih
        ⟨pairedSchedule (t + k),
          (pairedExecution_step P C (t + k)).symm⟩

theorem pairedExecution_reachable_forward
    (P : PopulationProtocol) (C : P.Configuration 3)
    {t u : Nat} (htu : t ≤ u) :
    PopulationProtocol.Reachable P ringSix
      (pairedExecution P C t) (pairedExecution P C u) := by
  have hreach := pairedExecution_reachable_add P C t (u - t)
  have heq : t + (u - t) = u := by omega
  rw [heq] at hreach
  exact hreach

theorem pairedExecution_boundary_not_unique
    (P : PopulationProtocol) (isLeader : P.Y → Bool)
    (C : P.Configuration 3) (q : Nat) :
    ¬ UniqueLeaderOutput P 6
      (pairedExecution P C (6 * q)) isLeader := by
  rw [pairedExecution_block_boundary]
  exact periodThreeLift_not_unique P isLeader (iterateBaseRound P C q)

/-- Every point of the weakly fair execution fails Definition-1 safety.  The
state at that point need not itself be symmetric: its safety would be closed
under reachability, while the later block boundary is symmetric and
non-unique. -/
theorem pairedExecution_not_isSafe
    (P : PopulationProtocol) (isLeader : P.Y → Bool)
    (C : P.Configuration 3) (t : Nat) :
    ¬ PopulationProtocol.IsSafe P ringSix
      (pairedExecution P C t) isLeader := by
  intro hsafe
  let u := 6 * (t + 1)
  have htu : t ≤ u := by
    dsimp [u]
    omega
  have hreach : PopulationProtocol.Reachable P ringSix
      (pairedExecution P C t) (pairedExecution P C u) :=
    pairedExecution_reachable_forward P C htu
  have hfuture : PopulationProtocol.IsSafe P ringSix
      (pairedExecution P C u) isLeader :=
    (isSafe_closed P ringSix isLeader).reachable hsafe hreach
  have hboundary :
      ¬ UniqueLeaderOutput P 6 (pairedExecution P C u) isLeader := by
    change ¬ UniqueLeaderOutput P 6
      (pairedExecution P C (6 * (t + 1))) isLeader
    exact pairedExecution_boundary_not_unique P isLeader C (t + 1)
  exact hboundary hfuture.1

/-! ## Protocol-independent capstone and the exact overlay instance -/

/-- For every protocol and supplied three-site seed, construct a concrete
six-site initialization and weakly fair execution which never becomes safe.
The carrier and transition are completely arbitrary in this theorem; the
following nonempty-carrier corollary states the universal no-go directly. -/
theorem exists_weakEdgeFair_execution_never_safe
    (P : PopulationProtocol) (isLeader : P.Y → Bool)
    (C : P.Configuration 3) :
    ∃ schedule : Nat → Fin 6,
      ∃ execution : Nat → P.Configuration 6,
        execution 0 = periodThreeLift P C ∧
        WeakEdgeFair schedule ∧
        (∀ t, P.step ringSix (execution t) (schedule t) =
          execution (t + 1)) ∧
        (∀ q, ¬ UniqueLeaderOutput P 6 (execution (6 * q)) isLeader) ∧
        (∀ t, ¬ PopulationProtocol.IsSafe P ringSix
          (execution t) isLeader) := by
  exact ⟨pairedSchedule, pairedExecution P C,
    pairedExecution_initial P C, pairedSchedule_weakEdgeFair,
    pairedExecution_step P C,
    pairedExecution_boundary_not_unique P isLeader C,
    pairedExecution_not_isSafe P isLeader C⟩

/-- The exact universal weak-fair convergence property refuted below.  It
quantifies arbitrary initial configurations and actual executable trajectories;
no provenance restriction on initialized tags is built into the definition. -/
def EveryWeakEdgeFairExecutionStabilizes
    (P : PopulationProtocol) (isLeader : P.Y → Bool) : Prop :=
  ∀ initial : P.Configuration 6,
    ∀ schedule : Nat → Fin 6,
      ∀ execution : Nat → P.Configuration 6,
        execution 0 = initial →
        WeakEdgeFair schedule →
        (∀ t, P.step ringSix (execution t) (schedule t) =
          execution (t + 1)) →
        ∃ t, PopulationProtocol.IsSafe P ringSix
          (execution t) isLeader

/-- Formal universal no-go.  Nonemptiness is the only carrier premise needed
to construct an initial word.  It is automatically satisfied by every
executable protocol instance in this project. -/
theorem no_deterministicAnonymous_everyWeakFair_stabilization
    (P : PopulationProtocol) (isLeader : P.Y → Bool)
    [Nonempty P.Q] :
    ¬ EveryWeakEdgeFairExecutionStabilizes P isLeader := by
  intro hconverges
  rcases (inferInstance : Nonempty P.Q) with ⟨q⟩
  let C : P.Configuration 3 := fun _ => q
  have heventual := hconverges
    (periodThreeLift P C) pairedSchedule (pairedExecution P C)
    (pairedExecution_initial P C)
    pairedSchedule_weakEdgeFair
    (pairedExecution_step P C)
  rcases heventual with ⟨t, hsafe⟩
  exact pairedExecution_not_isSafe P isLeader C t hsafe

/-! ### The exact all-sealed separated overlay start -/

abbrev OverlayNoGoPsi : Nat := 2

def overlaySeparatedLeaderState (kappa tau : Nat) :
    SealSweepState OverlayNoGoPsi kappa tau :=
  ((staleLeaderPhysical kappa tau, true), true)

def overlaySeparatedFollowerState (kappa tau : Nat) :
    SealSweepState OverlayNoGoPsi kappa tau :=
  (clearMinimalLockLeader (staleLeaderPhysical kappa tau, true), true)

@[simp] theorem overlaySeparatedLeaderState_leader (kappa tau : Nat) :
    sweepLockLeader (overlaySeparatedLeaderState kappa tau) = true := by
  rfl

@[simp] theorem overlaySeparatedFollowerState_leader (kappa tau : Nat) :
    sweepLockLeader (overlaySeparatedFollowerState kappa tau) = false := by
  rfl

@[simp] theorem overlaySeparatedLeaderState_closed (kappa tau : Nat) :
    (overlaySeparatedLeaderState kappa tau).2 = true := by
  rfl

@[simp] theorem overlaySeparatedFollowerState_closed (kappa tau : Nat) :
    (overlaySeparatedFollowerState kappa tau).2 = true := by
  rfl

/-- Base word `L,F,F`; its double cover is the separated word
`L,F,F,L,F,F`. -/
def overlaySeparatedBase (kappa tau : Nat) :
    (P_partialSealSweepProtocol OverlayNoGoPsi kappa tau).Configuration 3 :=
  fun i =>
    match i.val with
    | 0 => overlaySeparatedLeaderState kappa tau
    | _ => overlaySeparatedFollowerState kappa tau

def overlaySeparatedDouble (kappa tau : Nat) :
    (P_partialSealSweepProtocol OverlayNoGoPsi kappa tau).Configuration 6 :=
  periodThreeLift (P_partialSealSweepProtocol OverlayNoGoPsi kappa tau)
    (overlaySeparatedBase kappa tau)

@[simp] theorem overlaySeparatedDouble_zero (kappa tau : Nat) :
    overlaySeparatedDouble kappa tau 0 =
      overlaySeparatedLeaderState kappa tau := by
  rfl

@[simp] theorem overlaySeparatedDouble_one (kappa tau : Nat) :
    overlaySeparatedDouble kappa tau 1 =
      overlaySeparatedFollowerState kappa tau := by
  rfl

@[simp] theorem overlaySeparatedDouble_two (kappa tau : Nat) :
    overlaySeparatedDouble kappa tau 2 =
      overlaySeparatedFollowerState kappa tau := by
  rfl

@[simp] theorem overlaySeparatedDouble_three (kappa tau : Nat) :
    overlaySeparatedDouble kappa tau 3 =
      overlaySeparatedLeaderState kappa tau := by
  rfl

@[simp] theorem overlaySeparatedDouble_four (kappa tau : Nat) :
    overlaySeparatedDouble kappa tau 4 =
      overlaySeparatedFollowerState kappa tau := by
  rfl

@[simp] theorem overlaySeparatedDouble_five (kappa tau : Nat) :
    overlaySeparatedDouble kappa tau 5 =
      overlaySeparatedFollowerState kappa tau := by
  rfl

theorem overlaySeparatedDouble_allClosed (kappa tau : Nat) :
    SealSweepAllClosed (overlaySeparatedDouble kappa tau) := by
  intro i
  rcases finSix_cases i with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rfl

theorem overlaySeparatedDouble_noAdjacent (kappa tau : Nat) :
    SweepResetNoAdjacentLeaders ringSix
      (overlaySeparatedDouble kappa tau) := by
  intro e
  rcases finSix_cases e with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [show ringSix.rightNeighbor (0 : Fin 6) = (1 : Fin 6) by rfl]
    simp
  · rw [show ringSix.rightNeighbor (1 : Fin 6) = (2 : Fin 6) by rfl]
    simp
  · rw [show ringSix.rightNeighbor (2 : Fin 6) = (3 : Fin 6) by rfl]
    simp
  · rw [show ringSix.rightNeighbor (3 : Fin 6) = (4 : Fin 6) by rfl]
    simp
  · rw [show ringSix.rightNeighbor (4 : Fin 6) = (5 : Fin 6) by rfl]
    simp
  · rw [show ringSix.rightNeighbor (5 : Fin 6) = (0 : Fin 6) by rfl]
    simp

theorem overlaySeparatedDouble_hasTwo (kappa tau : Nat) :
    HasTwoLeaderOutputs
      (P_partialSealSweepProtocol OverlayNoGoPsi kappa tau)
      isLeaderOutput (overlaySeparatedDouble kappa tau) := by
  refine ⟨0, 3, by decide, ?_, ?_⟩ <;>
    rfl

theorem overlaySeparatedDouble_isSeparatedStart (kappa tau : Nat) :
    SealSweepSeparatedStart ringSix
      (overlaySeparatedDouble kappa tau) := by
  exact ⟨overlaySeparatedDouble_allClosed kappa tau,
    overlaySeparatedDouble_noAdjacent kappa tau,
    overlaySeparatedDouble_hasTwo kappa tau⟩

/-- The same explicit start exhibits both sides of the concurrency gap: the
accepted serialized word reaches the singleton kernel in exactly six steps,
while another weakly fair execution never reaches a safe point. -/
theorem overlaySeparatedDouble_serialized_and_weakFair_gap
    (kappa tau : Nat) :
    let P := P_partialSealSweepProtocol OverlayNoGoPsi kappa tau
    let C := overlaySeparatedDouble kappa tau
    SealSweepSeparatedStart ringSix C ∧
      (∃ seed : Fin 6,
        let word := clockwiseEdgeSchedule ringSix seed 6
        let D := runLocalSchedule ringSix P_partialSealSweep C word
        word.length = 6 ∧
          PopulationProtocol.Reachable P ringSix C D ∧
          SealSweepAllClosed D ∧
          UniqueLeaderOutput P 6 D isLeaderOutput ∧
          PopulationProtocol.IsSafe P ringSix D isLeaderOutput) ∧
      (∃ schedule : Nat → Fin 6,
        ∃ execution : Nat → P.Configuration 6,
          execution 0 = C ∧
          WeakEdgeFair schedule ∧
          (∀ t, P.step ringSix (execution t) (schedule t) =
            execution (t + 1)) ∧
          (∀ q, ¬ UniqueLeaderOutput P 6
            (execution (6 * q)) isLeaderOutput) ∧
          (∀ t, ¬ PopulationProtocol.IsSafe P ringSix
            (execution t) isLeaderOutput)) := by
  dsimp only
  let P := P_partialSealSweepProtocol OverlayNoGoPsi kappa tau
  let B := overlaySeparatedBase kappa tau
  let C := overlaySeparatedDouble kappa tau
  have hstart : SealSweepSeparatedStart ringSix C :=
    overlaySeparatedDouble_isSeparatedStart kappa tau
  have hserialized := separatedStart_serialized_escape ringSix C hstart
  rcases hserialized with
    ⟨seed, hlength, hreach, hclosed, hunique⟩
  refine ⟨hstart, ⟨seed, hlength, hreach, hclosed, hunique, ?_⟩, ?_⟩
  · exact allClosedUnique_isSafe ringSix _ hclosed hunique
  have hbad := exists_weakEdgeFair_execution_never_safe
    P isLeaderOutput B
  simpa [P, B, C, overlaySeparatedDouble] using hbad

/-- The accepted no-new-state seal-sweep overlay is an immediate instance.
This theorem does not alter its all-schedule singleton kernel or its exact
serialized escape; it proves that neither this transition nor any deterministic
anonymous transition replacement can add the requested every-weak-fair-
schedule convergence guarantee. -/
theorem sealSweepOverlay_has_weakFair_nonstabilizing_execution
    (psi kappa tau : Nat)
    (C : (P_partialSealSweepProtocol psi kappa tau).Configuration 3) :
    ∃ schedule : Nat → Fin 6,
      ∃ execution : Nat →
          (P_partialSealSweepProtocol psi kappa tau).Configuration 6,
        execution 0 = periodThreeLift
          (P_partialSealSweepProtocol psi kappa tau) C ∧
        WeakEdgeFair schedule ∧
        (∀ t,
          (P_partialSealSweepProtocol psi kappa tau).step
              ringSix (execution t) (schedule t) =
              execution (t + 1)) ∧
        (∀ q, ¬ UniqueLeaderOutput
          (P_partialSealSweepProtocol psi kappa tau)
            6 (execution (6 * q)) isLeaderOutput) ∧
        (∀ t, ¬ PopulationProtocol.IsSafe
          (P_partialSealSweepProtocol psi kappa tau)
            ringSix (execution t) isLeaderOutput) := by
  exact exists_weakEdgeFair_execution_never_safe
    (P_partialSealSweepProtocol psi kappa tau) isLeaderOutput C

end PPartialSealSweepConcurrencyNoGoSol
end PPLLCompleteMultiLeaderCleanup
