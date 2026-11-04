import Leader.Wu.Birth.ShortDoneTerminalOrdinaryLabel
import Leader.Wu.Birth.WaitPassiveHost

namespace BirthShortDoneTerminalOrdinaryLabelR1Audit

open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
  PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
  PPLLLeaderCreationCleanupRepair PPLLWallSweepRepair PPLLWallSweepFinite
  PPLLWallSweepPreCheckResetRepair
open BirthSigMoveDisposalRepair BirthWaitPassive
open BirthShortDoneTerminalOrdinaryLabelR1

set_option autoImplicit false
set_option pp.structureInstances false
set_option Elab.async false

private theorem hpsi2 : 0 < 2 := by decide
private theorem hwidth2 : 0 < 2 := by decide
private theorem hle2 : 2 <= 2 := by decide
private theorem hn5 : 1 < 5 := by decide

/-- Literal finite ring and the last physical scheduler site. -/
def auditRing5 : DirectedRing 5 := ⟨by decide⟩
def auditEdge4 : Fin 5 := ⟨4, by decide⟩

/-- The selected scheduler edge is the physical wrap edge 4 -> 0. -/
theorem auditEdge4_wrap :
    auditRing5.rightNeighbor auditEdge4 = (0 : Fin 5) := by
  decide

/-- Touched follower record.  Phase is already true, so the mismatched
P-prime row repairs the responder label without launching a left probe. -/
private def mismatchRegs : Registers 2 where
  label := 1
  h := false
  carry := false
  reset := false
  count := 0
  wait := true
  bit := false
  phase := true
  writer := .none

/-- Quiet outside record.  Outside sites are irrelevant to the one-edge
interface, but are filled with finite physical states. -/
private def quietRegs : Registers 2 where
  label := 0
  h := false
  carry := false
  reset := false
  count := 0
  wait := true
  bit := false
  phase := true
  writer := .none

/-- Physical sites 4 and 0 deliberately both carry label 1. -/
def auditRaw (i : Fin 5) : AgentState 2 :=
  if i.val = 4 then cell mismatchRegs
  else if i.val = 0 then cell mismatchRegs
  else cell quietRegs

private theorem auditRaw_domain (i : Fin 5) :
    (auditRaw i).inProtocolDomain 0 := by
  simp [auditRaw, mismatchRegs, quietRegs,
    AgentState.inProtocolDomain, cell]

private def auditPack (i : Fin 5) : ExpiringAgentState 2 0 0 :=
  ⟨⟨BoundedAgentState.ofDomain (auditRaw i) (auditRaw_domain i), false⟩, 0⟩

def auditSource : Fin 5 -> ExpiringAgentState 2 0 0 :=
  fun i => auditPack i

@[simp] private theorem raw_auditSource (i : Fin 5) :
    BirthWaitPassive.raw (auditSource i) = auditRaw i := by
  simp [auditSource, auditPack, BirthWaitPassive.raw,
    BoundedAgentState.erase_ofDomain]

/-- The complete finite source is literally leaderless, not merely the
selected pair. -/
theorem source_leaderless :
    BirthShortDoneTerminalFirstHit.Leaderless auditSource := by
  intro i
  change (BirthWaitPassive.raw (auditSource i)).leader = false
  rw [raw_auditSource]
  simp [auditRaw, cell]

/-- Exact touched input labels before preparation. -/
theorem source_left_label_one :
    (auditSource auditEdge4).core.core.label = (1 : Fin 2) := by
  change (BirthWaitPassive.raw (auditSource auditEdge4)).label = (1 : Fin 2)
  rw [raw_auditSource]
  rfl

theorem source_right_label_one :
    (auditSource (auditRing5.rightNeighbor auditEdge4)).core.core.label =
      (1 : Fin 2) := by
  rw [auditEdge4_wrap]
  change (BirthWaitPassive.raw (auditSource (0 : Fin 5))).label = (1 : Fin 2)
  rw [raw_auditSource]
  simp [auditRaw, mismatchRegs, cell]

/-- Genuine P-prime barrier geometry on the chosen physical edge: 1 -> 1 is
not the required psi=2 successor relation 1 -> 0. -/
theorem source_wrap_label_mismatch :
    (auditSource (auditRing5.rightNeighbor auditEdge4)).core.core.label ≠
      ⟨((auditSource auditEdge4).core.core.label.val + 1) % 2,
        Nat.mod_lt _ hpsi2⟩ := by
  rw [source_left_label_one, source_right_label_one]
  decide

/-! ## Exact disposal preparation and current ordinary priority -/

private theorem prepared_left_erasure :
    (prepareExpiringDisposal hpsi2 (auditSource auditEdge4)).core.erase =
      ⟨cell mismatchRegs, false⟩ := by
  have hraw : BirthWaitPassive.raw (auditSource auditEdge4) =
      cell mismatchRegs := by
    rw [raw_auditSource]
    rfl
  have h := BirthWaitPassive.prepared_erasure
    hpsi2 (auditSource auditEdge4) mismatchRegs hraw
  simpa [auditSource, auditPack] using h

private theorem prepared_right_erasure :
    (prepareExpiringDisposal hpsi2
      (auditSource (auditRing5.rightNeighbor auditEdge4))).core.erase =
      ⟨cell mismatchRegs, false⟩ := by
  rw [auditEdge4_wrap]
  have hraw : BirthWaitPassive.raw (auditSource (0 : Fin 5)) =
      cell mismatchRegs := by
    rw [raw_auditSource]
    simp [auditRaw]
  have h := BirthWaitPassive.prepared_erasure
    hpsi2 (auditSource (0 : Fin 5)) mismatchRegs hraw
  simpa [auditSource, auditPack] using h

private def preparedLeft : AuthorizedAgentState 2 :=
  normalizeDeletion
    (prepareExpiringDisposal hpsi2 (auditSource auditEdge4)).core.erase

private def preparedRight : AuthorizedAgentState 2 :=
  normalizeDeletion
    (prepareExpiringDisposal hpsi2
      (auditSource (auditRing5.rightNeighbor auditEdge4))).core.erase

private theorem preparedLeft_exact :
    preparedLeft = ⟨cell mismatchRegs, false⟩ := by
  unfold preparedLeft
  rw [prepared_left_erasure]
  exact normalize_cell mismatchRegs false

private theorem preparedRight_exact :
    preparedRight = ⟨cell mismatchRegs, false⟩ := by
  unfold preparedRight
  rw [prepared_right_erasure]
  exact normalize_cell mismatchRegs false

/-- These are the literal two tests that select the current ordinary branch,
in the host's actual responder-first / initiator-second order. -/
theorem prepared_normalized_guards_false :
    deletionActive preparedRight = false ∧
      deletionActive preparedLeft = false := by
  rw [preparedRight_exact, preparedLeft_exact]
  exact ⟨active_cell mismatchRegs false, active_cell mismatchRegs false⟩

/-- Public premise, derived from the two exact current guards above. -/
theorem source_prepared_ordinary_open :
    PreparedOrdinaryOpen hpsi2
      (auditSource auditEdge4)
      (auditSource (auditRing5.rightNeighbor auditEdge4)) := by
  change deletionActive preparedRight = false ∧
    deletionActive preparedLeft = false
  exact prepared_normalized_guards_false

/-! ## Stage calculation: P-prime is not the full physical conclusion -/

private def pprimeStage : AuthorizedAgentState 2 × AuthorizedAgentState 2 :=
  authorizedPPsiLeaderResetProbeWall hpsi2 preparedLeft preparedRight

/-- Closed calculation at the actual reset-aware P-prime stage.  The input
mismatch 1 -> 1 is repaired to 1 -> 0 and neither P-prime output is a leader.
This theorem says nothing by itself about later CHECK or finalPhysical. -/
theorem pprime_stage_repairs_mismatch_without_stage_leader :
    pprimeStage.1.core.leader = false ∧
      pprimeStage.2.core.leader = false ∧
      pprimeStage.1.core.label = (1 : Fin 2) ∧
      pprimeStage.2.core.label = (0 : Fin 2) := by
  unfold pprimeStage
  rw [preparedLeft_exact, preparedRight_exact]
  decide

/-! ## Current metadata event and complete physical successor -/

set_option maxRecDepth 32768 in
set_option maxHeartbeats 16000000 in
/-- This is the current terminal observer's computed metadata birth bit.
No no-birth proposition is supplied to the theorem. -/
theorem wrap_birthEvent_false :
    BirthShortDoneTerminalObserver.birthEvent hpsi2 hwidth2 hle2
      (auditSource auditEdge4)
      (auditSource (auditRing5.rightNeighbor auditEdge4)) = false := by
  rw [auditEdge4_wrap]
  decide

/-- The literal current population-protocol successor on scheduler edge 4. -/
def wrapStep : Fin 5 -> ExpiringAgentState 2 0 0 :=
  BirthShortDoneTerminalConsumer.step hpsi2 hwidth2 hle2
    auditRing5 auditSource auditEdge4

/-- The computed false metadata event, together with the actual leaderless
input, implies that the completed consumer successor after finalPhysical is
leaderless.  This is the physical statement, not the earlier P-prime fact. -/
theorem wrapStep_leaderless :
    BirthShortDoneTerminalFirstHit.Leaderless wrapStep := by
  simpa [wrapStep] using
    (BirthShortDoneTerminalFirstHit.step_leaderless_of_no_birth
      hpsi2 hwidth2 hle2 auditRing5 auditSource auditEdge4
      source_leaderless wrap_birthEvent_false)

private theorem wrapStep_left_eq_row :
    wrapStep auditEdge4 =
      (BirthShortDoneTerminalHost.row hpsi2 hwidth2 hle2
        (auditSource auditEdge4)
        (auditSource (auditRing5.rightNeighbor auditEdge4))).1 := by
  simp [wrapStep, BirthShortDoneTerminalConsumer.step,
    PopulationProtocol.step, BirthShortDoneTerminalConsumer.protocol, updatePair]

private theorem wrapStep_right_eq_row :
    wrapStep (auditRing5.rightNeighbor auditEdge4) =
      (BirthShortDoneTerminalHost.row hpsi2 hwidth2 hle2
        (auditSource auditEdge4)
        (auditSource (auditRing5.rightNeighbor auditEdge4))).2 := by
  have hne := rightNeighbor_ne_self_of_one_lt auditRing5 hn5 auditEdge4
  simp [wrapStep, BirthShortDoneTerminalConsumer.step,
    PopulationProtocol.step, BirthShortDoneTerminalConsumer.protocol,
    updatePair, hne]

/-- Compute the two current full-host labels from the closed no-birth event,
not from a desired postcondition premise. -/
theorem current_full_row_labels :
    let q := BirthShortDoneTerminalHost.row hpsi2 hwidth2 hle2
      (auditSource auditEdge4)
      (auditSource (auditRing5.rightNeighbor auditEdge4))
    q.1.core.core.label = (1 : Fin 2) ∧
      q.2.core.core.label = (0 : Fin 2) := by
  have h := ordinary_row_labels_of_no_birth hpsi2 hwidth2 hle2
    (auditSource auditEdge4)
    (auditSource (auditRing5.rightNeighbor auditEdge4))
    (source_leaderless auditEdge4)
    (source_leaderless (auditRing5.rightNeighbor auditEdge4))
    source_prepared_ordinary_open wrap_birthEvent_false
  dsimp only at h ⊢
  refine ⟨h.1.trans source_left_label_one, h.2.trans ?_⟩
  rw [source_left_label_one]
  decide

/-- The two leader bits below are read from the *completed* current row. -/
theorem current_full_row_leaders_false :
    let q := BirthShortDoneTerminalHost.row hpsi2 hwidth2 hle2
      (auditSource auditEdge4)
      (auditSource (auditRing5.rightNeighbor auditEdge4))
    q.1.core.core.leader = false ∧ q.2.core.core.leader = false := by
  have hL := wrapStep_leaderless auditEdge4
  have hR := wrapStep_leaderless (auditRing5.rightNeighbor auditEdge4)
  rw [wrapStep_left_eq_row] at hL
  rw [wrapStep_right_eq_row] at hR
  exact ⟨hL, hR⟩

/-- Exact requested observed successor of the actual current full host on the
physical wrap pair.  This statement is after metadata normalization,
newborn initialization, collision, and K2 `finalPhysical`. -/
theorem current_full_host_successor_observation :
    let q := BirthShortDoneTerminalHost.row hpsi2 hwidth2 hle2
      (auditSource auditEdge4)
      (auditSource (auditRing5.rightNeighbor auditEdge4))
    q.1.core.core.leader = false ∧
      q.2.core.core.leader = false ∧
      q.1.core.core.label = (1 : Fin 2) ∧
      q.2.core.core.label = (0 : Fin 2) := by
  have hl := current_full_row_leaders_false
  have hq := current_full_row_labels
  dsimp only at hl hq ⊢
  exact ⟨hl.1, hl.2, hq.1, hq.2⟩

/-! ## Public-interface nonvacuity -/

/-- Specialize the public disjunction to this closed finite source.
Its physical-birth alternative is impossible because the same computed
`birthEvent = false` has already yielded literal `Leaderless` for the actual
successor.  Therefore the public theorem genuinely returns its ordinary
successor-label branch here. -/
theorem public_interface_takes_ordinary_branch :
    let D := BirthShortDoneTerminalConsumer.step hpsi2 hwidth2 hle2
      auditRing5 auditSource auditEdge4
    BirthShortDoneTerminalFirstHit.Leaderless D ∧
      (D auditEdge4).core.core.label =
        (auditSource auditEdge4).core.core.label ∧
      (D (auditRing5.rightNeighbor auditEdge4)).core.core.label =
        ⟨((auditSource auditEdge4).core.core.label.val + 1) % 2,
          Nat.mod_lt _ hpsi2⟩ := by
  have hpub := ordinary_edge_label_or_physical_birth
    hpsi2 hwidth2 hle2 hn5 auditRing5 auditSource auditEdge4
    source_leaderless source_prepared_ordinary_open
  dsimp only at hpub ⊢
  have hz : BirthShortDoneTerminalFirstHit.Leaderless
      (BirthShortDoneTerminalConsumer.step hpsi2 hwidth2 hle2
        auditRing5 auditSource auditEdge4) := by
    simpa [wrapStep] using wrapStep_leaderless
  rcases hpub with hborn | hquiet
  · rcases hborn with ⟨i, hi⟩
    have hf := hz i
    rw [hf] at hi
    cases hi
  · exact hquiet

/-- Concrete numerical rendering of the same public branch: on physical
4 -> 0 the current full successor is still leaderless and the touched labels
are exactly 1 -> 0. -/
theorem public_interface_concrete_wrap :
    let D := BirthShortDoneTerminalConsumer.step hpsi2 hwidth2 hle2
      auditRing5 auditSource auditEdge4
    BirthShortDoneTerminalFirstHit.Leaderless D ∧
      (D auditEdge4).core.core.label = (1 : Fin 2) ∧
      (D (auditRing5.rightNeighbor auditEdge4)).core.core.label =
        (0 : Fin 2) := by
  have h := public_interface_takes_ordinary_branch
  dsimp only at h ⊢
  refine ⟨h.1, h.2.1.trans source_left_label_one, h.2.2.trans ?_⟩
  rw [source_left_label_one]
  decide

#print axioms BirthShortDoneTerminalOrdinaryLabelR1Audit.prepared_normalized_guards_false
#print axioms BirthShortDoneTerminalOrdinaryLabelR1Audit.pprime_stage_repairs_mismatch_without_stage_leader
#print axioms BirthShortDoneTerminalOrdinaryLabelR1Audit.wrap_birthEvent_false
#print axioms BirthShortDoneTerminalOrdinaryLabelR1Audit.current_full_host_successor_observation
#print axioms BirthShortDoneTerminalOrdinaryLabelR1Audit.public_interface_takes_ordinary_branch
#print axioms BirthShortDoneTerminalOrdinaryLabelR1Audit.public_interface_concrete_wrap

end BirthShortDoneTerminalOrdinaryLabelR1Audit
