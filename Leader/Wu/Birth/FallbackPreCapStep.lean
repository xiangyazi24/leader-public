import Leader.Wu.Birth.ReacquirePhaseMass
import Leader.Wu.Birth.ShortDoneTerminalPassiveLocalTripleRotation

set_option autoImplicit false
set_option Elab.async false
set_option pp.structureInstances false

namespace BirthB4FallbackPreCapStep

open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
  PPLLExpiringComparisonRepair PPLLLeaderCreationCleanupRepair
  PPLLWallSweepFinite
open BirthWaitPassive BirthSigMoveDisposalRepair
open BirthShortDoneTerminalPassiveR4
open BirthShortDoneTerminalPassiveLocal3
open BirthShortDoneTerminalPassiveLocal3Rotation
open PPLLAuthorizedComparisonRepair

abbrev FC (n psi kappa tau : Nat) :=
  BirthPhaseWait2BlockProgress.FC n psi kappa tau

private theorem hpsi4 : 0 < 4 := by decide
private theorem h2 : 2 <= 4 := by decide
private def ring4 : DirectedRing 4 := ⟨by decide⟩
private def anchor4 : Fin 4 := 0
private def boundaryEdge4 : Fin 4 := 3

private def regs (lab : Fin 4) (hh cc : Bool) : Registers 4 where
  label := lab
  h := hh
  carry := cc
  reset := false
  count := 0
  wait := true
  bit := false
  phase := false
  writer := .none

private def sourceRaw (i : Fin 4) : AgentState 4 :=
  if i = 0 then cell (regs 0 false true)
  else if i = 1 then cell (regs 1 true false)
  else if i = 2 then cell (regs 2 false false)
  else cell (regs 0 false false)

private theorem sourceRaw_domain (i : Fin 4) :
    (sourceRaw i).inProtocolDomain 1 := by
  by_cases h0 : i = 0
  · subst i
    simp [sourceRaw, regs, AgentState.inProtocolDomain, cell]
  by_cases h1 : i = 1
  · subst i
    simp [sourceRaw, regs, AgentState.inProtocolDomain, cell]
  by_cases h2i : i = 2
  · subst i
    simp [sourceRaw, regs, AgentState.inProtocolDomain, cell]
  · simp [sourceRaw, h0, h1, h2i, regs,
      AgentState.inProtocolDomain, cell]

private def sourcePack (i : Fin 4) : ExpiringAgentState 4 1 0 :=
  ⟨⟨BoundedAgentState.ofDomain
      (sourceRaw i) (sourceRaw_domain i), false⟩, 0⟩
private def sourceC : FC 4 4 1 0 := fun i => sourcePack i

private def afterBoundary : FC 4 4 1 0 :=
  BirthPhaseWait2BlockProgress.currentStep2
    hpsi4 h2 ring4 sourceC boundaryEdge4
private def afterRuler : FC 4 4 1 0 :=
  BirthPhaseWait2BlockProgress.currentStep2
    hpsi4 h2 ring4 afterBoundary anchor4
private def afterOutside : FC 4 4 1 0 :=
  BirthPhaseWait2BlockProgress.currentStep2
    hpsi4 h2 ring4 afterRuler (2 : Fin 4)
private def badC : FC 4 4 1 0 :=
  BirthPhaseWait2BlockProgress.currentStep2
    hpsi4 h2 ring4 afterOutside boundaryEdge4

/-- The exact prepared pair seen by the ordinary branch of the current host. -/
private def badPrepared : AuthorizedAgentState 4 × AuthorizedAgentState 4 :=
  let l := normalizeDeletion
    (prepareExpiringDisposal hpsi4 (badC anchor4)).core.erase
  let r := normalizeDeletion
    (prepareExpiringDisposal hpsi4
      (badC (ring4.rightNeighbor anchor4))).core.erase
  (l, r)

/-- The actual P-prime cut immediately before shortened WAIT. -/
private def badPprime : AuthorizedAgentState 4 × AuthorizedAgentState 4 :=
  authorizedPPsiLeaderResetProbeWall hpsi4 badPrepared.1 badPrepared.2

private def badWait : AgentState 4 × AgentState 4 :=
  BirthShortWaitTerminalEntryRepair.waitWidthEntry
    hpsi4 (by decide) h2 1 badPprime.1.core badPprime.2.core

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
/-- The tracked count entering the disputed row is zero. -/
theorem bad_count_before_decide :
    BirthPhaseWait2BlockProgress.shortCountAt ring4 anchor4 badC = 0 := by
  decide

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
/-- The raw target really classifies this row as pre-cap. -/
theorem bad_row_preCap_decide :
    RowPreCap2 hpsi4 h2 1 ring4 badC anchor4 := by
  unfold RowPreCap2 RowCap2
  decide

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
/-- The missing ingredient is on the initiator: P-prime reaches WAIT with no
carry token, so the terminal responder cannot increment on this row. -/
theorem bad_pprime_initiator_carry_decide :
    badPprime.1.core.carry = false := by
  decide

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
theorem bad_wait_count_decide : badWait.2.count = 0 := by
  decide

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
/-- The complete currentStep2 also leaves the tracked count at zero. -/
theorem bad_count_after_decide :
    BirthPhaseWait2BlockProgress.shortCountAt ring4 anchor4
      (BirthPhaseWait2BlockProgress.currentStep2
        hpsi4 h2 ring4 badC anchor4) = 0 := by
  decide

/-- Thus this closed fixture satisfies, rather than violates, the desired
sub-cap conclusion.  It provides no refutation of FallbackPreCapStepSubCap. -/
theorem bad_fixture_stays_subcap :
    BirthPhaseWait2BlockProgress.shortCountAt ring4 anchor4
      (BirthPhaseWait2BlockProgress.currentStep2
        hpsi4 h2 ring4 badC anchor4) < 1 := by
  rw [bad_count_after_decide]
  decide

end BirthB4FallbackPreCapStep

#print axioms BirthB4FallbackPreCapStep.bad_count_before_decide
#print axioms BirthB4FallbackPreCapStep.bad_row_preCap_decide
#print axioms BirthB4FallbackPreCapStep.bad_pprime_initiator_carry_decide
#print axioms BirthB4FallbackPreCapStep.bad_wait_count_decide
#print axioms BirthB4FallbackPreCapStep.bad_count_after_decide
#print axioms BirthB4FallbackPreCapStep.bad_fixture_stays_subcap
