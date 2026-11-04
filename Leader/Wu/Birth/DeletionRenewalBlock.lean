import Leader.Wu.Birth.InterleavedDrainBound
import Leader.Wu.Birth.ResetDrainParallel


set_option autoImplicit false
set_option Elab.async false
set_option pp.structureInstances false


namespace BirthB1DeletionRenewalBlock


open FiniteUniformStoppingTree FixedSpanRenewalPayload
open PPLL PPLLResearchFormulation PPLLWallSweepFiniteCleanup
open BirthShortDoneTerminalDeletionRank
open BirthShortDoneTerminalB1EntranceR2
open BirthB1ResetFreeEntranceMass BirthB1ReacquireReentryMass


variable {n psi kappa tau : Nat}


abbrev FC (n psi kappa tau : Nat) :=
  BirthPhaseWait2BlockProgress.FC n psi kappa tau


/-- The scheduler edge whose responder is the prepared-deletion site. -/
def deletionServiceEdge (ring : DirectedRing n) (victim : Fin n) : Fin n :=
  ring.leftNeighbor victim


theorem deletionServiceEdge_responder
    (ring : DirectedRing n) (victim : Fin n) :
    ring.rightNeighbor (deletionServiceEdge ring victim) = victim := by
  exact rightNeighbor_leftNeighbor_wall ring victim


private theorem currentStep2_eq_localStep
    (hpsi : 0 < psi) (h2 : 2 <= psi)
    (ring : DirectedRing n) (C : FC n psi kappa tau) (e : Fin n) :
    BirthPhaseWait2BlockProgress.currentStep2 hpsi h2 ring C e =
      localStep ring
        (BirthShortDoneTerminalHost.row hpsi (by decide : 0 < 2) h2) C e := by
  simpa [BirthPhaseWait2BlockProgress.currentStep2,
    BirthShortDoneTerminalConsumer.step,
    BirthShortDoneTerminalConsumer.protocol] using
    (PPLLResearchFormulation.localStep_eq_protocol_step
      (BirthShortDoneTerminalConsumer.protocol
        hpsi (by decide : 0 < 2) h2 kappa tau) ring C e).symm


/-- One service of the current prepared deletion strictly lowers the physical
comparison-path rank. -/
theorem deletionServiceEdge_decreases
    (hpsi : 0 < psi) (h2 : 2 <= psi)
    (ring : DirectedRing n) (hn : 1 < n)
    (C : FC n psi kappa tau) (victim : Fin n)
    (hactive : CurrentPreparedDeletionActive hpsi (C victim)) :
    comparisonPathCount
        (BirthPhaseWait2BlockProgress.currentStep2 hpsi h2 ring C
          (deletionServiceEdge ring victim)) <
      comparisonPathCount C := by
  have ha : CurrentPreparedDeletionActive hpsi
      (C (ring.rightNeighbor (deletionServiceEdge ring victim))) := by
    rw [deletionServiceEdge_responder ring victim]
    exact hactive
  rw [currentStep2_eq_localStep hpsi h2 ring C
    (deletionServiceEdge ring victim)]
  exact localStep_prepared_responder_delete_count_lt
    hpsi (by decide : 0 < 2) h2 ring hn C
      (deletionServiceEdge ring victim) ha


/-- Three-port certificate used by the conservative raw scheduler race.
`a` is the productive incoming service edge; `b` is the outgoing edge of the
tracked victim.  `c` is any further distinct designated interference port. -/
structure DeletionServicePorts
    (ring : DirectedRing n) (victim : Fin n) where
  ports : ThreePortSerialCount.Ports n
  productive : ports.a = deletionServiceEdge ring victim
  outgoing : ports.b = victim


/-- The productive port in the counting certificate is the real strict-rank
service edge. -/
theorem productivePort_decreases
    (hpsi : 0 < psi) (h2 : 2 <= psi)
    (ring : DirectedRing n) (hn : 1 < n)
    (C : FC n psi kappa tau) (victim : Fin n)
    (P : DeletionServicePorts ring victim)
    (hactive : CurrentPreparedDeletionActive hpsi (C victim)) :
    comparisonPathCount
        (BirthPhaseWait2BlockProgress.currentStep2 hpsi h2 ring C P.ports.a) <
      comparisonPathCount C := by
  rw [P.productive]
  exact deletionServiceEdge_decreases hpsi h2 ring hn C victim hactive


/-- Raw 2n-block success indicator for the conservative deletion-service race. -/
def deletionProductiveBit {n : Nat} {ring : DirectedRing n} {victim : Fin n}
    (P : DeletionServicePorts ring victim) (u : List (Fin n)) : Nat :=
  BirthB1ResetDrainParallel.protectedProductiveBit P.ports u


/-- Per-deletion renewal block: the designated service port has uniform
mass at least 1/4, in division-free form. -/
theorem oneDeletionProductiveBlockMass
    {n : Nat} {ring : DirectedRing n} {victim : Fin n}
    (P : DeletionServicePorts ring victim) (hn : 3 <= n) :
    n ^ (2 * n) <=
      4 * FixedSpanRenewalPayload.wordSum n (2 * n)
        (deletionProductiveBit P) := by
  exact BirthB1ResetDrainParallel.oneResetProductiveBlockMass P.ports hn


/-- K consecutive 2n-blocks miss the productive service with the same
quarter-success geometric tail as the reset block. -/
theorem oneDeletionProductiveBlocksGeometric
    {n : Nat} {ring : DirectedRing n} {victim : Fin n}
    (P : DeletionServicePorts ring victim) (hn : 3 <= n) (blocks : Nat) :
    4 ^ blocks *
        activeCount
          (BirthB1ResetDrainParallel.protectedBlockStep P.ports)
          (.active ()) blocks <=
      3 ^ blocks * n ^ ((2 * n) * blocks) := by
  exact BirthB1ResetDrainParallel.oneResetProductiveBlocksGeometric
    P.ports hn blocks


/-- There are at most n strict deletion-service rank levels. -/
theorem deletionStages_le_n (C : FC n psi kappa tau) :
    comparisonPathCount C <= n :=
  comparisonPathCount_le C


/-- At most n productive deletion services are union-charged. -/
abbrev deletionDrainUnionTerms (n : Nat) : Nat := n


/-- Reuse the reset proof's dyadic amplification margin. -/
abbrev deletionDrainRounds (n power : Nat) : Nat :=
  BirthB1ResetDrainParallel.resetDrainRounds n power


abbrev deletionDrainBlocks (n power : Nat) : Nat :=
  BirthB1ResetDrainParallel.resetDrainBlocks n power


/-- n deletion services, K blocks/service, 2n raw letters/block:
O(n^2 log n) for fixed `power`. -/
abbrev deletionDrainParallelL (n power : Nat) : Nat :=
  n * deletionDrainBlocks n power * (2 * n)


/-- Failure means no physical leader appeared and a prepared deletion remains. -/
noncomputable def DeletionDrainFailureBit
    (hpsi : 0 < psi) (h2 : 2 <= psi) (ring : DirectedRing n)
    (C : FC n psi kappa tau) (u : List (Fin n)) : Nat := by
  classical
  let D := prefixEndpoint hpsi h2 ring C u
  exact if HasPhysicalLeader D \/ CurrentNoPreparedDeletion hpsi D then 0 else 1


/-- Division-free all-deletion tail, at the same semantic-composition boundary
as `ResetDrainParallelBound`. -/
def DeletionDrainParallelBound
    (hpsi : 0 < psi) (h2 : 2 <= psi)
    (kappa tau : Nat) (ring : DirectedRing n) (power : Nat) : Prop :=
  4 <= n -> psi <= n -> forall C : FC n psi kappa tau,
    Leaderless C ->
      n ^ power *
          FixedSpanRenewalPayload.wordSum n (deletionDrainParallelL n power)
            (DeletionDrainFailureBit hpsi h2 ring C) <=
        n ^ deletionDrainParallelL n power


end BirthB1DeletionRenewalBlock


#print axioms BirthB1DeletionRenewalBlock.deletionServiceEdge_decreases
#print axioms BirthB1DeletionRenewalBlock.productivePort_decreases
#print axioms BirthB1DeletionRenewalBlock.oneDeletionProductiveBlockMass
#print axioms BirthB1DeletionRenewalBlock.oneDeletionProductiveBlocksGeometric
#print axioms BirthB1DeletionRenewalBlock.DeletionDrainParallelBound
