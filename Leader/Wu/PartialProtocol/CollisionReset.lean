import Leader.Wu.PartialProtocol.SweepLock

/-!
# Collision reset for the dynamic sweep lock

The accepted factor-four sweep repairs every false-phase double cover, but its
all-sealed branch is identity.  The smallest further source-shaped change is a
priority collision branch with no new state: when both selected endpoints are
physical leaders, retain the initiator, clear the responder leader, and seal
both.  Every noncollision pair executes the accepted dynamic sweep verbatim.

This branch breaks the accepted two-agent stale-lock trap for every arbitrary
initial assignment of the outer seal bit.  The endpoint pair is non-self on
the two-agent ring, so one interaction leaves exactly one leader and both
endpoints sealed.

The existing all-sealed unique-leader kernel remains a fixed point.  On a
nontrivial ring, no edge of a unique-leader configuration has two leader
endpoints; on the one-agent self-edge, left-biased step semantics retains the
initiator output even though the unused responder result is cleared.

The result is deliberately local.  An all-sealed multi-leader configuration
with no adjacent leader pair is still fixed, because every selected edge is a
noncollision and delegates to the accepted sealed identity branch.  The file
states and proves that residual class explicitly; it does not claim arbitrary-
state or arbitrary-multileader convergence.  State cost remains exactly factor
four over physical `P_partial` state.
-/

namespace PPLLCompleteMultiLeaderCleanup
namespace PPartialDynamicSweepResetSol

open PPLL PPLLResearchFormulation
  PPLLNoCheckBirthConditionTwoGeometry
open PPartialMinimalLockRepairSol
open PPartialMinimalLockStaleCounterexampleSol
open PPartialDynamicSweepLockSol
open PPartialStaticDoubleCoverSol
open PPLLStaticDoubleCoverNoGo

set_option autoImplicit false

variable {n psi kappa tau : Nat}

/-! ## Minimal no-new-state transition -/

/-- The repair uses exactly the accepted factor-four carrier. -/
abbrev SweepResetState (psi kappa tau : Nat) :=
  SweepLockState psi kappa tau

abbrev SweepResetConfig (n psi kappa tau : Nat) :=
  Fin n → SweepResetState psi kappa tau

/-- Exact local event newly handled by this file. -/
def sweepResetCollision
    (l r : SweepResetState psi kappa tau) : Bool :=
  sweepLockLeader l && sweepLockLeader r

/-- Priority adjacent-leader reset, followed by exact delegation to the
accepted dynamic sweep on every other input pair. -/
def P_partialSweepReset
    (hpsi : psi > 0) (kappa tau : Nat)
    (l r : SweepResetState psi kappa tau) :
    SweepResetState psi kappa tau × SweepResetState psi kappa tau :=
  if sweepResetCollision l r then
    ((l.1, true), (clearMinimalLockLeader r.1, true))
  else
    P_partialSweepLock hpsi kappa tau l r

/-- Packaged protocol with the same output map and carrier as the accepted
dynamic sweep. -/
def P_partialSweepResetProtocol
    (hpsi : psi > 0) (kappa tau : Nat) : PopulationProtocol where
  Q := SweepResetState psi kappa tau
  Y := LeaderOutput
  transition := P_partialSweepReset hpsi kappa tau
  output := fun s =>
    if sweepLockLeader s then LeaderOutput.leader
    else LeaderOutput.follower

/-- Output is literally unchanged from the accepted dynamic sweep protocol. -/
theorem sweepReset_output_eq_sweepLock
    (hpsi : psi > 0) (kappa tau : Nat)
    (u : SweepResetState psi kappa tau) :
    (P_partialSweepResetProtocol hpsi kappa tau).output u =
      (P_partialSweepLockProtocol hpsi kappa tau).output u := by
  rfl

/-- Every noncollision pair delegates exactly. -/
theorem P_partialSweepReset_of_noCollision
    (hpsi : psi > 0) (kappa tau : Nat)
    (l r : SweepResetState psi kappa tau)
    (hcollision : sweepResetCollision l r = false) :
    P_partialSweepReset hpsi kappa tau l r =
      P_partialSweepLock hpsi kappa tau l r := by
  simp [P_partialSweepReset, hcollision]

/-- The new collision branch is independent of both arbitrary seal inputs. -/
theorem P_partialSweepReset_of_twoLeaders
    (hpsi : psi > 0) (kappa tau : Nat)
    (l r : SweepResetState psi kappa tau)
    (hl : sweepLockLeader l = true)
    (hr : sweepLockLeader r = true) :
    P_partialSweepReset hpsi kappa tau l r =
      ((l.1, true), (clearMinimalLockLeader r.1, true)) := by
  simp [P_partialSweepReset, sweepResetCollision, hl, hr]

/-- The bounded physical domain remains closed in both branches. -/
theorem P_partialSweepReset_output_inProtocolDomain
    (hpsi : psi > 0) (kappa tau : Nat)
    (l r : SweepResetState psi kappa tau) :
    let q := P_partialSweepReset hpsi kappa tau l r
    q.1.1.1.core.erase.core.inProtocolDomain kappa ∧
      q.2.1.1.core.erase.core.inProtocolDomain kappa := by
  let q := P_partialSweepReset hpsi kappa tau l r
  exact ⟨q.1.1.1.core.core.erase_inProtocolDomain,
    q.2.1.1.core.core.erase_inProtocolDomain⟩

/-! ## The existing unique-leader kernel is untouched -/

/-- Same operational kernel, stated against the new protocol output map. -/
def SweepResetLegit
    (hpsi : psi > 0) (kappa tau : Nat)
    (C : SweepResetConfig n psi kappa tau) : Prop :=
  SweepLockAllSealed C ∧
    UniqueLeaderOutput
      (P_partialSweepResetProtocol hpsi kappa tau)
      n C isLeaderOutput

private theorem leaderOutput_of_sweepLeader_true
    (hpsi : psi > 0) (kappa tau : Nat)
    (u : SweepResetState psi kappa tau)
    (hu : sweepLockLeader u = true) :
    isLeaderOutput
      ((P_partialSweepResetProtocol hpsi kappa tau).output u) = true := by
  change isLeaderOutput
    (if sweepLockLeader u then LeaderOutput.leader
      else LeaderOutput.follower) = true
  rw [hu]
  rfl

/-- A sealed noncollision pair remains exact identity. -/
theorem P_partialSweepReset_eq_self_of_sealed_noCollision
    (hpsi : psi > 0) (kappa tau : Nat)
    (l r : SweepResetState psi kappa tau)
    (hl : l.2 = true) (hr : r.2 = true)
    (hcollision : sweepResetCollision l r = false) :
    P_partialSweepReset hpsi kappa tau l r = (l, r) := by
  rw [P_partialSweepReset_of_noCollision
    hpsi kappa tau l r hcollision]
  exact P_partialSweepLock_eq_self_of_sealed
    hpsi kappa tau l r hl hr

/-- Every exact step from the old all-sealed unique-output kernel is identity.
The one-agent case uses the left-biased self-edge explicitly. -/
theorem P_partialSweepReset_step_eq_of_legit
    (hpsi : psi > 0) (kappa tau : Nat)
    (ring : DirectedRing n)
    (C : SweepResetConfig n psi kappa tau)
    (hC : SweepResetLegit hpsi kappa tau C)
    (e : Fin n) :
    (P_partialSweepResetProtocol hpsi kappa tau).step ring C e = C := by
  by_cases hn1 : n = 1
  · subst n
    funext i
    have he : e = (0 : Fin 1) := Subsingleton.elim _ _
    have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
    subst e
    subst i
    have hsealed := hC.1 (0 : Fin 1)
    cases hleader : sweepLockLeader (C 0) <;>
      simp [PopulationProtocol.step, P_partialSweepResetProtocol,
        P_partialSweepReset, sweepResetCollision,
        P_partialSweepLock, sweepLockTrigger, hsealed, hleader] <;>
      exact Prod.ext rfl hsealed.symm
  · obtain ⟨root, hroot, honly⟩ := hC.2
    have hnpos : 0 < n := Nat.zero_lt_of_lt root.isLt
    have hn2 : 1 < n := by omega
    let j := ring.rightNeighbor e
    have hje : j ≠ e := rightNeighbor_ne_self_of_one_lt ring hn2 e
    have hnotBoth : ¬(sweepLockLeader (C e) = true ∧
        sweepLockLeader (C j) = true) := by
      rintro ⟨he, hj⟩
      have heroot : e = root := honly e
        (leaderOutput_of_sweepLeader_true hpsi kappa tau (C e) he)
      have hjroot : j = root := honly j
        (leaderOutput_of_sweepLeader_true hpsi kappa tau (C j) hj)
      exact hje (hjroot.trans heroot.symm)
    have hcollision : sweepResetCollision (C e) (C j) = false := by
      cases he : sweepLockLeader (C e) with
      | false => simp [sweepResetCollision, he]
      | true =>
          cases hj : sweepLockLeader (C j) with
          | false => simp [sweepResetCollision, he, hj]
          | true => exact (hnotBoth ⟨he, hj⟩).elim
    have hpair : P_partialSweepReset hpsi kappa tau (C e) (C j) =
        (C e, C j) :=
      P_partialSweepReset_eq_self_of_sealed_noCollision
        hpsi kappa tau (C e) (C j)
        (hC.1 e) (hC.1 j) hcollision
    funext i
    by_cases hie : i = e
    · subst i
      simp [PopulationProtocol.step, P_partialSweepResetProtocol,
        j, hpair]
    · by_cases hij : i = j
      · subst i
        simp [PopulationProtocol.step, P_partialSweepResetProtocol,
          j, hie, hpair]
      · simp [PopulationProtocol.step, P_partialSweepResetProtocol,
          j, hie, hij]

/-- The old kernel remains closed. -/
theorem sweepResetLegit_closed
    (hpsi : psi > 0) (kappa tau : Nat)
    (ring : DirectedRing n) :
    PopulationProtocol.ClosedPred
      (P_partialSweepResetProtocol hpsi kappa tau) ring
      (SweepResetLegit hpsi kappa tau) := by
  intro C hC D hstep
  obtain ⟨e, rfl⟩ := hstep
  rw [P_partialSweepReset_step_eq_of_legit
    hpsi kappa tau ring C hC e]
  exact hC

/-- Pointwise outputs remain fixed in the kernel. -/
theorem sweepResetLegit_stepOutputPreserving
    (hpsi : psi > 0) (kappa tau : Nat)
    (ring : DirectedRing n) :
    StepOutputPreservingOn
      (P_partialSweepResetProtocol hpsi kappa tau) ring
      (SweepResetLegit hpsi kappa tau) := by
  intro C hC D hstep i
  obtain ⟨e, rfl⟩ := hstep
  rw [P_partialSweepReset_step_eq_of_legit
    hpsi kappa tau ring C hC e]

/-- The same canonical all-sealed one-leader witness inhabits the new kernel. -/
theorem sweepResetLegit_inhabited
    (hpsi : psi > 0) (kappa tau : Nat)
    (ring : DirectedRing n) :
    SweepResetLegit hpsi kappa tau
      (sweepLockWitness (n := n) hpsi kappa tau) := by
  have hold := sweepLockLegit_inhabited hpsi kappa tau ring
  constructor
  · exact hold.1
  · obtain ⟨leader, hleader, honly⟩ := hold.2
    refine ⟨leader, ?_, ?_⟩
    · have hout := congrArg isLeaderOutput
        (sweepReset_output_eq_sweepLock hpsi kappa tau
          (sweepLockWitness (n := n) hpsi kappa tau leader))
      exact hout.trans hleader
    · intro j hj
      apply honly j
      have hout := congrArg isLeaderOutput
        (sweepReset_output_eq_sweepLock hpsi kappa tau
          (sweepLockWitness (n := n) hpsi kappa tau j))
      exact hout.symm.trans hj

/-- Kernel membership still implies Definition-1 safety. -/
theorem sweepResetLegit_isSafe
    (hpsi : psi > 0) (kappa tau : Nat)
    (ring : DirectedRing n)
    {C : SweepResetConfig n psi kappa tau}
    (hC : SweepResetLegit hpsi kappa tau C) :
    PopulationProtocol.IsSafe
      (P_partialSweepResetProtocol hpsi kappa tau)
      ring C isLeaderOutput := by
  exact isSafe_of_operational_legitimacy
    (P_partialSweepResetProtocol hpsi kappa tau)
    ring isLeaderOutput
    (SweepResetLegit hpsi kappa tau)
    (sweepResetLegit_closed hpsi kappa tau ring)
    (fun _ h => h.2)
    (sweepResetLegit_stepOutputPreserving hpsi kappa tau ring)
    hC

/-! ## Arbitrary-seal escape from the accepted adjacent trap -/

abbrev SweepResetAuditPsi : Nat := 2

private theorem sweepResetAuditHPsi : SweepResetAuditPsi > 0 := by
  decide

private def sweepResetRingTwo : DirectedRing 2 :=
  ⟨by omega⟩

private theorem finTwo_eq_zero_or_one (i : Fin 2) :
    i = (0 : Fin 2) ∨ i = (1 : Fin 2) := by
  have hi := i.isLt
  by_cases hz : i.val = 0
  · left
    exact Fin.ext hz
  · right
    apply Fin.ext
    omega

@[simp] private theorem sweepResetRingTwo_right_zero :
    sweepResetRingTwo.rightNeighbor (0 : Fin 2) = (1 : Fin 2) := by
  rfl

/-- The accepted two physical leaders, with completely arbitrary outer seal
initialization. -/
def arbitrarySealAdjacentTrap
    (kappa tau : Nat) (sealBits : Fin 2 → Bool) :
    SweepResetConfig 2 SweepResetAuditPsi kappa tau :=
  fun i => (staleLockedDoubleLeaderConfig kappa tau i, sealBits i)

theorem arbitrarySealAdjacentTrap_leader
    (kappa tau : Nat) (sealBits : Fin 2 → Bool) (i : Fin 2) :
    sweepLockLeader (arbitrarySealAdjacentTrap kappa tau sealBits i) = true := by
  exact staleLockedDoubleLeader_leader kappa tau i

/-- One selected edge invokes the collision branch independently of both seal
values. -/
theorem arbitrarySealAdjacentTrap_pair
    (kappa tau : Nat) (sealBits : Fin 2 → Bool) :
    P_partialSweepReset sweepResetAuditHPsi kappa tau
        (arbitrarySealAdjacentTrap kappa tau sealBits 0)
        (arbitrarySealAdjacentTrap kappa tau sealBits 1) =
      (((arbitrarySealAdjacentTrap kappa tau sealBits 0).1, true),
        (clearMinimalLockLeader
          (arbitrarySealAdjacentTrap kappa tau sealBits 1).1, true)) := by
  exact P_partialSweepReset_of_twoLeaders
    sweepResetAuditHPsi kappa tau _ _
    (arbitrarySealAdjacentTrap_leader kappa tau sealBits 0)
    (arbitrarySealAdjacentTrap_leader kappa tau sealBits 1)

/-- Exact endpoint after the one-edge collision reset. -/
def arbitrarySealAdjacentAfter
    (kappa tau : Nat) (sealBits : Fin 2 → Bool) :
    SweepResetConfig 2 SweepResetAuditPsi kappa tau :=
  (P_partialSweepResetProtocol sweepResetAuditHPsi kappa tau).step
    sweepResetRingTwo
    (arbitrarySealAdjacentTrap kappa tau sealBits) 0

theorem arbitrarySealAdjacentAfter_zero
    (kappa tau : Nat) (sealBits : Fin 2 → Bool) :
    arbitrarySealAdjacentAfter kappa tau sealBits 0 =
      ((arbitrarySealAdjacentTrap kappa tau sealBits 0).1, true) := by
  simp [arbitrarySealAdjacentAfter, PopulationProtocol.step,
    P_partialSweepResetProtocol, arbitrarySealAdjacentTrap_pair]

theorem arbitrarySealAdjacentAfter_one
    (kappa tau : Nat) (sealBits : Fin 2 → Bool) :
    arbitrarySealAdjacentAfter kappa tau sealBits 1 =
      (clearMinimalLockLeader
        (arbitrarySealAdjacentTrap kappa tau sealBits 1).1, true) := by
  simp [arbitrarySealAdjacentAfter, PopulationProtocol.step,
    P_partialSweepResetProtocol, arbitrarySealAdjacentTrap_pair]

/-- Every arbitrary seal assignment reaches the closed one-leader kernel in
one actual interaction. -/
theorem arbitrarySealAdjacentTrap_oneStep_escape
    (kappa tau : Nat) (sealBits : Fin 2 → Bool) :
    HasTwoLeaderOutputs
        (P_partialSweepResetProtocol sweepResetAuditHPsi kappa tau)
        isLeaderOutput
        (arbitrarySealAdjacentTrap kappa tau sealBits) ∧
      PopulationProtocol.Reachable
        (P_partialSweepResetProtocol sweepResetAuditHPsi kappa tau)
        sweepResetRingTwo
        (arbitrarySealAdjacentTrap kappa tau sealBits)
        (arbitrarySealAdjacentAfter kappa tau sealBits) ∧
      SweepResetLegit sweepResetAuditHPsi kappa tau
        (arbitrarySealAdjacentAfter kappa tau sealBits) := by
  constructor
  · refine ⟨0, 1, ?_, ?_, ?_⟩
    · intro h
      have hv := congrArg Fin.val h
      omega
    · exact leaderOutput_of_sweepLeader_true
        sweepResetAuditHPsi kappa tau _
        (arbitrarySealAdjacentTrap_leader kappa tau sealBits 0)
    · exact leaderOutput_of_sweepLeader_true
        sweepResetAuditHPsi kappa tau _
        (arbitrarySealAdjacentTrap_leader kappa tau sealBits 1)
  constructor
  · exact PopulationProtocol.OneStep.to_reachable ⟨0, rfl⟩
  constructor
  · intro i
    rcases finTwo_eq_zero_or_one i with rfl | rfl
    · exact congrArg (fun u => u.2)
        (arbitrarySealAdjacentAfter_zero kappa tau sealBits)
    · exact congrArg (fun u => u.2)
        (arbitrarySealAdjacentAfter_one kappa tau sealBits)
  · refine ⟨0, ?_, ?_⟩
    · have hzero := arbitrarySealAdjacentAfter_zero kappa tau sealBits
      have hleader : sweepLockLeader
          (arbitrarySealAdjacentAfter kappa tau sealBits 0) = true := by
        rw [hzero]
        exact arbitrarySealAdjacentTrap_leader kappa tau sealBits 0
      exact leaderOutput_of_sweepLeader_true
        sweepResetAuditHPsi kappa tau _ hleader
    · intro i hi
      rcases finTwo_eq_zero_or_one i with rfl | rfl
      · rfl
      · have hone := arbitrarySealAdjacentAfter_one kappa tau sealBits
        have hleader : sweepLockLeader
            (arbitrarySealAdjacentAfter kappa tau sealBits 1) = false := by
          rw [hone]
          rfl
        change isLeaderOutput
          (if sweepLockLeader
              (arbitrarySealAdjacentAfter kappa tau sealBits 1)
            then LeaderOutput.leader else LeaderOutput.follower) = true at hi
        simp [hleader, isLeaderOutput] at hi

/-! ## Exact residual: separated sealed leaders are still fixed -/

/-- No selected directed edge currently has two leader endpoints. -/
def SweepResetNoAdjacentLeaders
    (ring : DirectedRing n)
    (C : SweepResetConfig n psi kappa tau) : Prop :=
  ∀ e : Fin n,
    ¬(sweepLockLeader (C e) = true ∧
      sweepLockLeader (C (ring.rightNeighbor e)) = true)

/-- Every all-sealed configuration with no adjacent leader collision remains a
fixed point.  Hence the new branch does not solve separated multi-leader
cleanup. -/
theorem P_partialSweepReset_step_eq_of_allSealed_noAdjacent
    (hpsi : psi > 0) (kappa tau : Nat)
    (ring : DirectedRing n)
    (C : SweepResetConfig n psi kappa tau)
    (hsealed : SweepLockAllSealed C)
    (hnoAdjacent : SweepResetNoAdjacentLeaders ring C)
    (e : Fin n) :
    (P_partialSweepResetProtocol hpsi kappa tau).step ring C e = C := by
  let j := ring.rightNeighbor e
  have hcollision : sweepResetCollision (C e) (C j) = false := by
    cases he : sweepLockLeader (C e) with
    | false => simp [sweepResetCollision, he]
    | true =>
        cases hj : sweepLockLeader (C j) with
        | false => simp [sweepResetCollision, he, hj]
        | true => exact (hnoAdjacent e ⟨he, by simpa [j] using hj⟩).elim
  have hpair : P_partialSweepReset hpsi kappa tau (C e) (C j) =
      (C e, C j) :=
    P_partialSweepReset_eq_self_of_sealed_noCollision
      hpsi kappa tau (C e) (C j)
      (hsealed e) (hsealed j) hcollision
  funext i
  by_cases hie : i = e
  · subst i
    simp [PopulationProtocol.step, P_partialSweepResetProtocol, j, hpair]
  · by_cases hij : i = j
    · subst i
      simp [PopulationProtocol.step, P_partialSweepResetProtocol,
        j, hie, hpair]
    · simp [PopulationProtocol.step, P_partialSweepResetProtocol,
        j, hie, hij]

/-! ## Exact unchanged state factor -/

/-- The collision reset reuses the accepted exhaustive carrier certificate. -/
def sweepResetStateCertificate (psi kappa tau : Nat) :
    ExhaustiveList (SweepResetState psi kappa tau) :=
  sweepLockStateCertificate psi kappa tau

/-- No state is added: the exact factor remains four over physical
`P_partial`. -/
theorem sweepResetStateCertificate_values_length
    (psi kappa tau : Nat) :
    (sweepResetStateCertificate psi kappa tau).values.length =
      ((2 * (PPLLFinite.boundedAgentState psi kappa).values.length) *
        (tau + 1)) * 4 := by
  exact sweepLockStateCertificate_values_length psi kappa tau

end PPartialDynamicSweepResetSol
end PPLLCompleteMultiLeaderCleanup
