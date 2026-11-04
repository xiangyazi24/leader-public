import Leader.Wu.Birth.FallbackCarryInvariant
import Leader.Wu.Birth.ShortWait
import Leader.Wu.Birth.ShortWaitTerminalEntryRepair
import Leader.Wu.Birth.ShortDoneTerminalEntryCut
import Leader.Wu.Elimination.MultiLeaderCleanup

set_option autoImplicit false
set_option Elab.async false
set_option pp.structureInstances false

namespace BirthB4ResetBackedInvariant

open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
  PPLLExpiringComparisonRepair PPLLLeaderCreationCleanupRepair
  PPLLWallSweepFinite PPLLAuthorizedComparisonRepair
open BirthWaitPassive BirthSigMoveDisposalRepair
open BirthShortDoneTerminalPassiveR4
open BirthShortDoneTerminalPassiveLocal3
open BirthShortDoneTerminalPassiveLocal3Rotation
open BirthB4FallbackCarryInvariant

abbrev FC (n psi kappa tau : Nat) :=
  BirthPhaseWait2BlockProgress.FC n psi kappa tau

private theorem h4 : 0 < 4 := by decide
private theorem h24 : 2 <= 4 := by decide
private theorem h2 : 0 < 2 := by decide
private theorem h22 : 2 <= 2 := by decide
private theorem hn4 : 4 <= 4 := by decide
private def ring4 : DirectedRing 4 := ⟨by decide⟩
private def anchor : Fin 4 := 0
private def boundary : Fin 4 := 3
private theorem right0 : ring4.rightNeighbor anchor = (1 : Fin 4) := by decide
private theorem right1 :
    ring4.rightNeighbor (ring4.rightNeighbor anchor) = (2 : Fin 4) := by decide

private def regs4 (lab : Fin 4) (hh cc : Bool) : Registers 4 where
  label := lab; h := hh; carry := cc; reset := false; count := 0
  wait := true; bit := false; phase := false; writer := .none

private def raw4 (i : Fin 4) : AgentState 4 :=
  if i = 0 then cell (regs4 0 false true)
  else if i = 1 then cell (regs4 1 true false)
  else if i = 2 then cell (regs4 2 false false)
  else { cell (regs4 1 false false) with phase := true }

private theorem raw4_domain (i : Fin 4) : (raw4 i).inProtocolDomain 1 := by
  by_cases h0 : i = 0
  · subst i; simp [raw4, regs4, AgentState.inProtocolDomain, cell]
  by_cases h1 : i = 1
  · subst i; simp [raw4, regs4, AgentState.inProtocolDomain, cell]
  by_cases h2i : i = 2
  · subst i; simp [raw4, regs4, AgentState.inProtocolDomain, cell]
  · simp [raw4, h0, h1, h2i, regs4, AgentState.inProtocolDomain, cell]

private def pack4 (i : Fin 4) : ExpiringAgentState 4 1 0 :=
  ⟨⟨BoundedAgentState.ofDomain (raw4 i) (raw4_domain i), false⟩, 0⟩
private def source4 : FC 4 4 1 0 := fun i => pack4 i
private def bad4 : FC 4 4 1 0 :=
  [anchor, (2 : Fin 4), boundary].foldl
    (BirthPhaseWait2BlockProgress.currentStep2 h4 h24 ring4)
    (BirthPhaseWait2BlockProgress.currentStep2 h4 h24 ring4 source4 boundary)

private def p4 := pprimeAt h4 ring4 bad4 anchor
private def w4 := BirthShortWaitTerminalEntryRepair.waitWidthEntry
  h4 h2 h24 1 p4.1.core p4.2.core
private def q4 := preparedAt h4 ring4 bad4 anchor
private def c4 := BirthShortDoneTerminalEntryCut.doneThroughCheckEntryWidth
  h4 h2 h24 1 q4.1 q4.2
private def d4 := authorizedDisappear h4 c4.1 c4.2
private def a4 := PPLLCompleteMultiLeaderCleanup.authorizedCompareSigActionOne
  h4 d4.1 d4.2
private def s4 := BirthShortWait.suppressPrefix a4.1.core a4.2.core
private def z4 := BirthShortWait.shortCountReset h2 h24 s4.1 s4.2

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
theorem bad_suppress_prefix_trigger_decide :
    s4.2.count = 1 ∧ s4.2.label = BirthShortWait.widthTerminal h2 h24 ∧
      s4.2.reset_cmd = true := by decide

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
theorem bad_shortCountReset_exact_decide :
    z4 = (s4.1, { s4.2 with count := 0 }) := by decide

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
theorem bad_reset_backed_absorption_decide :
    p4.2.core.count < w4.2.count ∧
      s4.2.label = BirthShortWait.widthTerminal h2 h24 ∧
      s4.2.reset_cmd = true ∧ z4.2.count = 0 := by decide

/-- Generic reset-backing schema.  The strict-increment trigger is one instance;
B4 only needs the cap-threatening trigger. -/
def ResetBackedRowInvariant {n psi : Nat}
    (hpsi : 0 < psi) (h2le : 2 <= psi) (hn : 4 <= n)
    (kappa tau : Nat) (ring : DirectedRing n) (a : Fin n)
    (trigger : Nat → Nat → Prop) : Prop :=
  ∀ C : FC n psi kappa tau,
    BirthPhaseWait2BlockProgress.BoundaryRecoveryReachable
      hpsi h2le hn kappa tau ring a C →
    BirthPhaseWait2BlockProgress.shortCountAt ring a C < kappa →
    RowPreCap2 hpsi h2le kappa ring C a →
    let p := pprimeAt hpsi ring C a
    let w := BirthShortWaitTerminalEntryRepair.waitWidthEntry
      hpsi (by decide : 0 < 2) h2le kappa p.1.core p.2.core
    let q := preparedAt hpsi ring C a
    let c := BirthShortDoneTerminalEntryCut.doneThroughCheckEntryWidth
      hpsi (by decide : 0 < 2) h2le kappa q.1 q.2
    let d := authorizedDisappear hpsi c.1 c.2
    let x := PPLLCompleteMultiLeaderCleanup.authorizedCompareSigActionOne
      hpsi d.1 d.2
    let s := BirthShortWait.suppressPrefix x.1.core x.2.core
    let z := BirthShortWait.shortCountReset (by decide : 0 < 2) h2le s.1 s.2
    trigger p.2.core.count w.2.count →
      s.2.label = BirthShortWait.widthTerminal (by decide : 0 < 2) h2le ∧
      s.2.reset_cmd = true ∧ z.2.count = 0

abbrev ResetBackedSameRowInvariant {n psi : Nat}
    (hpsi : 0 < psi) (h2le : 2 <= psi) (hn : 4 <= n)
    (kappa tau : Nat) (ring : DirectedRing n) (a : Fin n) : Prop :=
  ResetBackedRowInvariant hpsi h2le hn kappa tau ring a
    (fun before after => before < after)

abbrev CapThreateningResetBackedInvariant {n psi : Nat}
    (hpsi : 0 < psi) (h2le : 2 <= psi) (hn : 4 <= n)
    (kappa tau : Nat) (ring : DirectedRing n) (a : Fin n) : Prop :=
  ResetBackedRowInvariant hpsi h2le hn kappa tau ring a
    (fun _ after => after = kappa)

private def regs2 (lab : Fin 2) (hh cc : Bool) : Registers 2 where
  label := lab; h := hh; carry := cc; reset := false; count := 0
  wait := true; bit := false; phase := false; writer := .none

private def raw2 (i : Fin 4) : AgentState 2 :=
  if i = 0 then cell (regs2 0 false true)
  else if i = 1 then cell (regs2 1 true false)
  else if i = 2 then cell (regs2 0 false false)
  else cell (regs2 1 false false)

private theorem raw2_domain (i : Fin 4) : (raw2 i).inProtocolDomain 2 := by
  have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  rcases hi with rfl | rfl | rfl | rfl <;>
    simp [raw2, regs2, AgentState.inProtocolDomain, cell]

private def pack2 (i : Fin 4) : ExpiringAgentState 2 2 0 :=
  ⟨⟨BoundedAgentState.ofDomain (raw2 i) (raw2_domain i), false⟩, 0⟩
private def source2 : FC 4 2 2 0 := fun i => pack2 i
@[simp] private theorem raw_source2 (i : Fin 4) : raw (source2 i) = raw2 i := by
  simp [source2, pack2, raw, BoundedAgentState.erase_ofDomain]
private theorem source2_count :
    BirthPhaseWait2BlockProgress.shortCountAt ring4 anchor source2 = 0 := by decide

private theorem source2_carrier :
    BirthPhaseWait2BlockProgress.Carrier h2 h22 hn4 ring4 anchor source2 := by
  unfold BirthPhaseWait2BlockProgress.Carrier
    BirthPhaseWait2BlockProgress.LocalCarrier
    BirthPhaseWait2Transfer.LocalWait2Carrier
  constructor
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [anchor, raw2, regs2, Passive, InertWriter, Metadata,
        BirthWaitPassive.registers, BirthWaitPassive.cell]
    · rw [right0]; simp [raw2, regs2, Passive, InertWriter, Metadata,
        BirthWaitPassive.registers, BirthWaitPassive.cell]
    · rw [right1]; simp [raw2, regs2, Passive, InertWriter, Metadata,
        BirthWaitPassive.registers, BirthWaitPassive.cell]
    · simp [anchor, raw2, regs2, BirthWaitPassive.cell]
    · rw [right0]; simp [raw2, regs2, BirthWaitPassive.cell]
    · rw [right1]; simp [raw2, regs2, BirthWaitPassive.cell]
  · rw [source2_count]; decide

private theorem source2_boundary_preCap :
    RowPreCap2 h2 h22 2 ring4 source2 boundary := by
  unfold RowPreCap2 RowCap2
  decide
private theorem source2_boundary :
    BirthPhaseWait2Transfer.LocalWait2BoundaryNow hn4 ring4 anchor boundary := by
  unfold BirthPhaseWait2Transfer.LocalWait2BoundaryNow SafeLine3EdgeAt SafeLine3Edge
  decide

private def counterC : FC 4 2 2 0 :=
  BirthPhaseWait2BlockProgress.currentStep2 h2 h22 ring4 source2 boundary

theorem counter_reachable :
    BirthPhaseWait2BlockProgress.BoundaryRecoveryReachable
      h2 h22 hn4 2 0 ring4 anchor counterC := by
  exact ⟨source2, boundary, [], source2_carrier,
    source2_boundary_preCap, source2_boundary, rfl⟩

private def cp := pprimeAt h2 ring4 counterC anchor
private def cw := BirthShortWaitTerminalEntryRepair.waitWidthEntry
  h2 h2 h22 2 cp.1.core cp.2.core
private def cq := preparedAt h2 ring4 counterC anchor
private def cc := BirthShortDoneTerminalEntryCut.doneThroughCheckEntryWidth
  h2 h2 h22 2 cq.1 cq.2
private def cd := authorizedDisappear h2 cc.1 cc.2
private def ca := PPLLCompleteMultiLeaderCleanup.authorizedCompareSigActionOne
  h2 cd.1 cd.2
private def cs := BirthShortWait.suppressPrefix ca.1.core ca.2.core
private def cz := BirthShortWait.shortCountReset h2 h22 cs.1 cs.2

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
theorem counter_checked_decide :
    BirthPhaseWait2BlockProgress.shortCountAt ring4 anchor counterC < 2 ∧
    RowPreCap2 h2 h22 2 ring4 counterC anchor ∧
    cp.2.core.count = 0 ∧ cw.2.count = 1 ∧
    cs.2.label = BirthShortWait.widthTerminal h2 h22 ∧ cs.2.reset_cmd = false ∧
    cz.2.count = 1 ∧
    BirthPhaseWait2BlockProgress.shortCountAt ring4 anchor
      (BirthPhaseWait2BlockProgress.currentStep2 h2 h22 ring4 counterC anchor) = 1 := by
  unfold RowPreCap2 RowCap2
  decide

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
theorem resetBackedSameRowInvariant_false :
    ¬ ResetBackedSameRowInvariant h2 h22 hn4 2 0 ring4 anchor := by
  intro h
  unfold ResetBackedSameRowInvariant ResetBackedRowInvariant at h
  have hinc : cp.2.core.count < cw.2.count := by
    rw [counter_checked_decide.2.2.1, counter_checked_decide.2.2.2.1]
    decide
  have ho := h counterC counter_reachable counter_checked_decide.1
    counter_checked_decide.2.1 hinc
  have hr := ho.2.1
  change cs.2.reset_cmd = true at hr
  have hf : cs.2.reset_cmd = false :=
    counter_checked_decide.2.2.2.2.2.1
  have hbad : true = false := hr.symm.trans hf
  exact Bool.noConfusion hbad

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
theorem counter_not_cap_threatening_decide : cw.2.count < 2 := by decide

theorem counter_step_stays_subcap_decide :
    BirthPhaseWait2BlockProgress.shortCountAt ring4 anchor
      (BirthPhaseWait2BlockProgress.currentStep2 h2 h22 ring4 counterC anchor) < 2 := by
  rw [counter_checked_decide.2.2.2.2.2.2.2]
  decide

#print axioms bad_suppress_prefix_trigger_decide
#print axioms bad_shortCountReset_exact_decide
#print axioms bad_reset_backed_absorption_decide
#print axioms counter_reachable
#print axioms counter_checked_decide
#print axioms resetBackedSameRowInvariant_false
#print axioms counter_not_cap_threatening_decide
#print axioms counter_step_stays_subcap_decide

end BirthB4ResetBackedInvariant
