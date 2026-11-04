import Leader.Wu.Birth.FallbackPreCapStep

set_option autoImplicit false
set_option Elab.async false
set_option pp.structureInstances false

namespace BirthB4FallbackCarryInvariant

open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
  PPLLExpiringComparisonRepair PPLLLeaderCreationCleanupRepair
  PPLLWallSweepFinite PPLLAuthorizedComparisonRepair
open BirthWaitPassive BirthSigMoveDisposalRepair BirthShortWait
open BirthShortDoneTerminalPassiveR4
open BirthShortDoneTerminalPassiveLocal3
open BirthShortDoneTerminalPassiveLocal3Rotation

abbrev FC (n psi kappa tau : Nat) :=
  BirthPhaseWait2BlockProgress.FC n psi kappa tau

def preparedAt {n psi kappa tau : Nat} (hpsi : 0 < psi)
    (ring : DirectedRing n) (C : FC n psi kappa tau) (e : Fin n) :
    AuthorizedAgentState psi × AuthorizedAgentState psi :=
  let l := prepareExpiringDisposal hpsi (C e)
  let r := prepareExpiringDisposal hpsi (C (ring.rightNeighbor e))
  (normalizeDeletion l.core.erase, normalizeDeletion r.core.erase)

def pprimeAt {n psi kappa tau : Nat} (hpsi : 0 < psi)
    (ring : DirectedRing n) (C : FC n psi kappa tau) (e : Fin n) :
    AuthorizedAgentState psi × AuthorizedAgentState psi :=
  let q := preparedAt hpsi ring C e
  authorizedPPsiLeaderResetProbeWall hpsi q.1 q.2

def TerminalRelabelAt {n psi kappa tau : Nat}
    (hpsi : 0 < psi) (h2 : 2 <= psi) (ring : DirectedRing n)
    (C : FC n psi kappa tau) (e : Fin n) : Prop :=
  let q := preparedAt hpsi ring C e
  let p := pprimeAt hpsi ring C e
  deletionActive q.2 = false ∧ deletionActive q.1 = false ∧
    q.2.core.label ≠ p.2.core.label ∧
    p.2.core.label = widthTerminal (by decide : 0 < 2) h2

def FallbackCarryInvariant {n psi : Nat}
    (hpsi : 0 < psi) (h2 : 2 <= psi) (hn : 4 <= n)
    (kappa tau : Nat) (ring : DirectedRing n) (anchor : Fin n) : Prop :=
  ∀ C : FC n psi kappa tau,
    BirthPhaseWait2BlockProgress.BoundaryRecoveryReachable
      hpsi h2 hn kappa tau ring anchor C ->
    BirthPhaseWait2BlockProgress.shortCountAt ring anchor C < kappa ->
    RowPreCap2 hpsi h2 kappa ring C anchor ->
    TerminalRelabelAt hpsi h2 ring C anchor ->
    (pprimeAt hpsi ring C anchor).1.core.carry = false

private theorem hpsi4 : 0 < 4 := by decide
private theorem h2 : 2 <= 4 := by decide
private theorem hn4 : 4 <= 4 := by decide
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

/-- The outside predecessor starts at label 1 with phase already high.
This prevents the first crossing from leaving a probe there. -/
private def sourceRaw (i : Fin 4) : AgentState 4 :=
  if i = 0 then cell (regs 0 false true)
  else if i = 1 then cell (regs 1 true false)
  else if i = 2 then cell (regs 2 false false)
  else { cell (regs 1 false false) with phase := true }

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

private theorem source_carrier :
    BirthPhaseWait2BlockProgress.Carrier
      hpsi4 h2 hn4 ring4 anchor4 sourceC := by
  unfold BirthPhaseWait2BlockProgress.Carrier
    BirthPhaseWait2BlockProgress.LocalCarrier
    BirthPhaseWait2Transfer.LocalWait2Carrier
  constructor
  · refine {
      pass0 := (by simp only [Passive, Metadata, InertWriter]; decide), pass1 := (by simp only [Passive, Metadata, InertWriter]; decide),
      pass2 := (by simp only [Passive, Metadata, InertWriter]; decide),
      lab0 := by decide, lab1 := by decide, lab2 := by decide }
  · decide

private theorem source_boundary_preCap :
    RowPreCap2 hpsi4 h2 1 ring4 sourceC boundaryEdge4 := by
  unfold RowPreCap2 RowCap2
  decide

private theorem source_boundary :
    BirthPhaseWait2Transfer.LocalWait2BoundaryNow
      hn4 ring4 anchor4 boundaryEdge4 := by
  unfold BirthPhaseWait2Transfer.LocalWait2BoundaryNow
    SafeLine3EdgeAt SafeLine3Edge
  decide

private def tail4 : List (Fin 4) :=
  [anchor4, (2 : Fin 4), boundaryEdge4]

private def badC : FC 4 4 1 0 :=
  tail4.foldl
    (BirthPhaseWait2BlockProgress.currentStep2 hpsi4 h2 ring4)
    (BirthPhaseWait2BlockProgress.currentStep2
      hpsi4 h2 ring4 sourceC boundaryEdge4)

theorem badC_reachable :
    BirthPhaseWait2BlockProgress.BoundaryRecoveryReachable
      hpsi4 h2 hn4 1 0 ring4 anchor4 badC := by
  exact ⟨sourceC, boundaryEdge4, tail4, source_carrier,
    source_boundary_preCap, source_boundary, rfl⟩

private def badPprime : AuthorizedAgentState 4 × AuthorizedAgentState 4 :=
  pprimeAt hpsi4 ring4 badC anchor4

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
theorem bad_subcap_decide :
    BirthPhaseWait2BlockProgress.shortCountAt ring4 anchor4 badC < 1 := by
  decide

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
theorem bad_row_preCap_decide :
    RowPreCap2 hpsi4 h2 1 ring4 badC anchor4 := by
  unfold RowPreCap2 RowCap2
  decide

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
theorem bad_terminal_relabel_decide :
    TerminalRelabelAt hpsi4 h2 ring4 badC anchor4 := by
  unfold TerminalRelabelAt pprimeAt preparedAt
  decide

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
theorem bad_carry_decide : badPprime.1.core.carry = true := by
  decide

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
theorem bad_wait_count_decide :
    (BirthShortWaitTerminalEntryRepair.waitWidthEntry
      hpsi4 (by decide) h2 1 badPprime.1.core badPprime.2.core).2.count = 1 := by
  decide

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
theorem fallbackCarryInvariant_false :
    ¬ FallbackCarryInvariant hpsi4 h2 hn4 1 0 ring4 anchor4 := by
  intro h
  have hc := h badC badC_reachable bad_subcap_decide
    bad_row_preCap_decide bad_terminal_relabel_decide
  have hb : (pprimeAt hpsi4 ring4 badC anchor4).fst.core.carry = true := by
    decide
  exact Bool.noConfusion (hb.symm.trans hc)

#print axioms badC_reachable
#print axioms bad_terminal_relabel_decide
#print axioms bad_wait_count_decide
#print axioms fallbackCarryInvariant_false

end BirthB4FallbackCarryInvariant
