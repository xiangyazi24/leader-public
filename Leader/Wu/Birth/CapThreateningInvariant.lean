import Leader.Wu.Birth.FallbackCarryInvariant

set_option autoImplicit false
set_option Elab.async false
set_option pp.structureInstances false

namespace BirthB4CapThreateningInvariant

open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
  PPLLExpiringComparisonRepair PPLLLeaderCreationCleanupRepair
  PPLLWallSweepFinite PPLLAuthorizedComparisonRepair
open BirthWaitPassive BirthSigMoveDisposalRepair BirthShortWait
open BirthShortDoneTerminalPassiveR4
  BirthShortDoneTerminalPassiveLocal3
  BirthShortDoneTerminalPassiveLocal3Rotation
open BirthB4FallbackCarryInvariant

abbrev FC (n psi kappa tau : Nat) :=
  BirthPhaseWait2BlockProgress.FC n psi kappa tau

private theorem h4 : 0 < 4 := by decide
private theorem h24 : 2 <= 4 := by decide
private theorem hTwo : 0 < 2 := by decide
private theorem hn4 : 4 <= 4 := by decide
private def ring4 : DirectedRing 4 := ⟨by decide⟩
private def anchor : Fin 4 := 0
private def boundary : Fin 4 := 3

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
  else { cell (regs 1 false false) with phase := true }

private theorem sourceRaw_domain (i : Fin 4) :
    (sourceRaw i).inProtocolDomain 1 := by
  by_cases h0 : i = 0
  · subst i; simp [sourceRaw, regs, AgentState.inProtocolDomain, cell]
  by_cases h1 : i = 1
  · subst i; simp [sourceRaw, regs, AgentState.inProtocolDomain, cell]
  by_cases h2i : i = 2
  · subst i; simp [sourceRaw, regs, AgentState.inProtocolDomain, cell]
  · simp [sourceRaw, h0, h1, h2i, regs,
      AgentState.inProtocolDomain, cell]

private def sourcePack (i : Fin 4) : ExpiringAgentState 4 1 0 :=
  ⟨⟨BoundedAgentState.ofDomain (sourceRaw i) (sourceRaw_domain i), false⟩, 0⟩
private def sourceC : FC 4 4 1 0 := fun i => sourcePack i

private theorem source_carrier :
    BirthPhaseWait2BlockProgress.Carrier h4 h24 hn4 ring4 anchor sourceC := by
  unfold BirthPhaseWait2BlockProgress.Carrier
    BirthPhaseWait2BlockProgress.LocalCarrier
    BirthPhaseWait2Transfer.LocalWait2Carrier
  constructor
  · refine {
      pass0 := (by simp only [Passive, Metadata, InertWriter]; decide),
      pass1 := (by simp only [Passive, Metadata, InertWriter]; decide),
      pass2 := (by simp only [Passive, Metadata, InertWriter]; decide),
      lab0 := by decide, lab1 := by decide, lab2 := by decide }
  · decide

private theorem source_boundary_preCap :
    RowPreCap2 h4 h24 1 ring4 sourceC boundary := by
  unfold RowPreCap2 RowCap2
  decide

private theorem source_boundary :
    BirthPhaseWait2Transfer.LocalWait2BoundaryNow hn4 ring4 anchor boundary := by
  unfold BirthPhaseWait2Transfer.LocalWait2BoundaryNow
    SafeLine3EdgeAt SafeLine3Edge
  decide

private def tail : List (Fin 4) := [anchor, (2 : Fin 4), boundary]
private def capC : FC 4 4 1 0 :=
  tail.foldl (BirthPhaseWait2BlockProgress.currentStep2 h4 h24 ring4)
    (BirthPhaseWait2BlockProgress.currentStep2 h4 h24 ring4 sourceC boundary)

theorem capC_reachable :
    BirthPhaseWait2BlockProgress.BoundaryRecoveryReachable
      h4 h24 hn4 1 0 ring4 anchor capC := by
  exact ⟨sourceC, boundary, tail, source_carrier,
    source_boundary_preCap, source_boundary, rfl⟩

private def p := pprimeAt h4 ring4 capC anchor
private def w := BirthShortWaitTerminalEntryRepair.waitWidthEntry
  h4 hTwo h24 1 p.1.core p.2.core
private def q := preparedAt h4 ring4 capC anchor
private def c := BirthShortDoneTerminalEntryCut.doneThroughCheckEntryWidth
  h4 hTwo h24 1 q.1 q.2
private def d := authorizedDisappear h4 c.1 c.2
private def x := PPLLCompleteMultiLeaderCleanup.authorizedCompareSigActionOne
  h4 d.1 d.2
private def s := suppressPrefix x.1.core x.2.core
private def z := shortCountReset hTwo h24 s.1 s.2

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
private theorem hsub :
    BirthPhaseWait2BlockProgress.shortCountAt ring4 anchor capC < 1 := by decide
set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
private theorem hpre : RowPreCap2 h4 h24 1 ring4 capC anchor := by
  unfold RowPreCap2 RowCap2
  decide
set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
private theorem hp0 : p.2.core.count = 0 := by decide
set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
private theorem hw1 : w.2.count = 1 := by decide
set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
private theorem hslabel : s.2.label = widthTerminal hTwo h24 := by decide
set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
private theorem hsreset : s.2.reset_cmd = true := by decide
set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
private theorem hz0 : z.2.count = 0 := by decide
set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
private theorem hstep0 :
    BirthPhaseWait2BlockProgress.shortCountAt ring4 anchor
      (BirthPhaseWait2BlockProgress.currentStep2 h4 h24 ring4 capC anchor) = 0 := by
  decide

/-- The certified recovery endpoint really reaches the cap, but that cap hit is
reset-backed and is absorbed in the same physical row. -/
theorem reachable_cap_hit_is_reset_backed :
    BirthPhaseWait2BlockProgress.BoundaryRecoveryReachable
        h4 h24 hn4 1 0 ring4 anchor capC ∧
    BirthPhaseWait2BlockProgress.shortCountAt ring4 anchor capC < 1 ∧
    RowPreCap2 h4 h24 1 ring4 capC anchor ∧
    p.2.core.count = 0 ∧ w.2.count = 1 ∧
    s.2.label = widthTerminal hTwo h24 ∧ s.2.reset_cmd = true ∧
    z.2.count = 0 ∧
    BirthPhaseWait2BlockProgress.shortCountAt ring4 anchor
      (BirthPhaseWait2BlockProgress.currentStep2 h4 h24 ring4 capC anchor) = 0 := by
  exact ⟨capC_reachable, hsub, hpre, hp0, hw1,
    hslabel, hsreset, hz0, hstep0⟩

/-- Scoped no-go: on the verified reachable cap-hit endpoint, the two clauses
needed by the proposed counterexample cannot coexist. -/
theorem cap_hit_and_reset_free_incompatible :
    ¬ (w.2.count = 1 ∧ s.2.reset_cmd = false) := by
  intro h
  exact Bool.noConfusion (hsreset.symm.trans h.2)

#print axioms capC_reachable
#print axioms reachable_cap_hit_is_reset_backed
#print axioms cap_hit_and_reset_free_incompatible

end BirthB4CapThreateningInvariant
