import Leader.Wu.Birth.IncreaseOrCapPhysicalFire


set_option autoImplicit false
set_option Elab.async false
set_option pp.structureInstances false


namespace BirthPhaseB3SurvivingCrossing


open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
  PPLLExpiringComparisonRepair
open BirthWaitPassive BirthShortWait BirthShortWaitProjection
open BirthShortDoneTerminalPassiveR4
open BirthShortDoneTerminalPassiveLocal3
open BirthShortDoneTerminalPassiveLocal3Rotation


variable {n psi kappa tau : Nat}


abbrev FC (n psi kappa tau : Nat) :=
  BirthPhaseWait2BlockProgress.FC n psi kappa tau


/-- The other internal edge, `rightNeighbor anchor`, is also safe. -/
private theorem right_anchor_is_safe
    (hn : 4 <= n) (ring : DirectedRing n) (anchor : Fin n) :
    SafeLine3EdgeAt hn ring anchor (ring.rightNeighbor anchor) := by
  unfold SafeLine3EdgeAt SafeLine3Edge
  have h := congrArg (unrotateIndex ring anchor)
    (rotateIndex_p1 hn ring anchor)
  have hp :
      unrotateIndex ring anchor (ring.rightNeighbor anchor) = p1 hn := by
    simpa only [unrotateIndex_rotateIndex] using h.symm
  rw [hp]
  constructor
  · intro he
    have hv := congrArg Fin.val he
    change 1 = 2 at hv
    omega
  · intro he
    have hv := congrArg Fin.val he
    change 1 = n - 1 at hv
    omega


/-- Every Local3 crossing misses the tracked p1 site at both endpoints.
Consequently `shortCountAt` is exactly framed, with no carrier hypothesis. -/
theorem crossing_shortCount_frame
    (hpsi : 0 < psi) (h2 : 2 <= psi) (hn : 4 <= n)
    (ring : DirectedRing n) (anchor : Fin n)
    (C : FC n psi kappa tau) (e : Fin n)
    (hboundary : BirthPhaseWait2Transfer.LocalWait2BoundaryNow
      hn ring anchor e) :
    BirthPhaseWait2BlockProgress.shortCountAt ring anchor C =
      BirthPhaseWait2BlockProgress.shortCountAt ring anchor
        (BirthPhaseWait2BlockProgress.currentStep2 hpsi h2 ring C e) := by
  have hb := hboundary
  unfold BirthPhaseWait2Transfer.LocalWait2BoundaryNow at hb
  have he0 : e ≠ anchor := by
    intro he
    subst e
    exact hb (BirthPhaseB3BridgeStageA.anchor_is_safe hn ring anchor)
  have he1 : e ≠ ring.rightNeighbor anchor := by
    intro he
    subst e
    exact hb (right_anchor_is_safe hn ring anchor)
  have hf := BirthPhaseB3NoBoundarySurvival.other_edge_count_frame
    (kappa := kappa) (tau := tau)
    hpsi h2 ring anchor e C he0 he1
  have hs := BirthPhaseWait2BlockProgress.hostStep_eq_currentStep2
    hpsi h2 ring C e
  rw [hs] at hf
  exact hf


/-- The missing fourth row case: a crossing is executed, but the successor is
still a genuine active Carrier.  This is a raw-seed restart point. -/
def SurvivingCrossingRow
    (hpsi : 0 < psi) (h2 : 2 <= psi) (hn : 4 <= n)
    (kappa tau : Nat) (ring : DirectedRing n) (anchor : Fin n)
    (C : FC n psi kappa tau) (e : Fin n) : Prop :=
  BirthPhaseWait2BlockProgress.Carrier hpsi h2 hn ring anchor C /\
    RowPreCap2 hpsi h2 kappa ring C e /\
    BirthPhaseWait2Transfer.LocalWait2BoundaryNow hn ring anchor e /\
    BirthPhaseWait2BlockProgress.Carrier hpsi h2 hn ring anchor
      (BirthPhaseWait2BlockProgress.currentStep2 hpsi h2 ring C e)


/-- Literal-word version to append as the fourth `CarrierDirtyCaseCoverage`
disjunct. -/
def SurvivingCrossingWithin
    (hpsi : 0 < psi) (h2 : 2 <= psi) (hn : 4 <= n)
    (kappa tau : Nat) (ring : DirectedRing n) (anchor : Fin n)
    (C : FC n psi kappa tau) (u : List (Fin n)) : Prop :=
  exists pre e post,
    u = pre ++ (e :: post) /\
      SurvivingCrossingRow hpsi h2 hn kappa tau ring anchor
        (pre.foldl
          (BirthPhaseWait2BlockProgress.currentStep2 hpsi h2 ring) C) e


/-! ## Smallest literal counterexample -/


private theorem hpsi2 : 0 < (2 : Nat) := by decide
private theorem h2 : (2 : Nat) <= 2 := by decide
private theorem hn4 : (4 : Nat) <= 4 := by decide


private def ring4 : DirectedRing 4 := ⟨by decide⟩
private def anchor4 : Fin 4 := 0
private def incomingEdge4 : Fin 4 := 3


private theorem right0 :
    ring4.rightNeighbor anchor4 = (1 : Fin 4) := by
  decide


private theorem right1 :
    ring4.rightNeighbor (ring4.rightNeighbor anchor4) = (2 : Fin 4) := by
  decide


private def regs (label : Fin 2) (h : Bool) : Registers 2 where
  label := label
  h := h
  carry := false
  reset := false
  count := 0
  wait := true
  bit := false
  phase := false
  writer := .none


/-- Local3 is `(0,1,0)` and site 3 is the aligned incoming predecessor.
Only the root `h_field` is true. -/
private def sourceRaw (i : Fin 4) : AgentState 2 :=
  if i = 0 then cell (regs 0 true)
  else if i = 1 then cell (regs 1 false)
  else if i = 2 then cell (regs 0 false)
  else cell (regs 1 false)


private theorem sourceRaw_domain (i : Fin 4) :
    (sourceRaw i).inProtocolDomain 2 := by
  have hi : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 := by omega
  rcases hi with rfl | rfl | rfl | rfl <;>
    simp [sourceRaw, regs, AgentState.inProtocolDomain, cell]


private def sourcePack (i : Fin 4) : ExpiringAgentState 2 2 0 :=
  ⟨⟨BoundedAgentState.ofDomain (sourceRaw i) (sourceRaw_domain i), false⟩, 0⟩


private def sourceC : FC 4 2 2 0 := fun i => sourcePack i


@[simp] private theorem raw_sourceC (i : Fin 4) :
    raw (sourceC i) = sourceRaw i := by
  simp [sourceC, sourcePack, raw, BoundedAgentState.erase_ofDomain]


private theorem source_count :
    BirthPhaseWait2BlockProgress.shortCountAt
      ring4 anchor4 sourceC = 0 := by
  decide


private theorem source_carrier :
    BirthPhaseWait2BlockProgress.Carrier
      hpsi2 h2 hn4 ring4 anchor4 sourceC := by
  unfold BirthPhaseWait2BlockProgress.Carrier
    BirthPhaseWait2BlockProgress.LocalCarrier
    BirthPhaseWait2Transfer.LocalWait2Carrier
  constructor
  · refine { pass0 := ?_, pass1 := ?_, pass2 := ?_, lab0 := ?_, lab1 := ?_, lab2 := ?_ }
    · simp [anchor4, sourceRaw, regs, Passive, InertWriter, Metadata,
        BirthWaitPassive.registers, BirthWaitPassive.cell]
    · rw [right0]
      simp [sourceRaw, regs, Passive, InertWriter, Metadata,
        BirthWaitPassive.registers, BirthWaitPassive.cell]
    · rw [right1]
      simp [sourceRaw, regs, Passive, InertWriter, Metadata,
        BirthWaitPassive.registers, BirthWaitPassive.cell]
    · simp [anchor4, sourceRaw, regs, BirthWaitPassive.cell]
    · rw [right0]
      simp [sourceRaw, regs, BirthWaitPassive.cell]
    · rw [right1]
      simp [sourceRaw, regs, BirthWaitPassive.cell]
  · rw [source_count]
    decide


private theorem source_preCap :
    RowPreCap2 hpsi2 h2 2 ring4 sourceC incomingEdge4 := by
  unfold RowPreCap2 RowCap2
  decide


private theorem source_boundary :
    BirthPhaseWait2Transfer.LocalWait2BoundaryNow
      hn4 ring4 anchor4 incomingEdge4 := by
  unfold BirthPhaseWait2Transfer.LocalWait2BoundaryNow
    SafeLine3EdgeAt SafeLine3Edge
  decide


private def afterCross : FC 4 2 2 0 :=
  BirthPhaseWait2BlockProgress.currentStep2
    hpsi2 h2 ring4 sourceC incomingEdge4


private theorem afterCross_p1 :
    afterCross (ring4.rightNeighbor anchor4) =
      sourceC (ring4.rightNeighbor anchor4) := by
  simpa [afterCross, BirthPhaseWait2BlockProgress.currentStep2] using
    (BirthShortDoneTerminalConsumer.step_other
      hpsi2 (by decide : 0 < 2) h2 ring4 sourceC incomingEdge4
      (ring4.rightNeighbor anchor4) (by decide) (by decide))


private theorem afterCross_p2 :
    afterCross (ring4.rightNeighbor (ring4.rightNeighbor anchor4)) =
      sourceC (ring4.rightNeighbor (ring4.rightNeighbor anchor4)) := by
  simpa [afterCross, BirthPhaseWait2BlockProgress.currentStep2] using
    (BirthShortDoneTerminalConsumer.step_other
      hpsi2 (by decide : 0 < 2) h2 ring4 sourceC incomingEdge4
      (ring4.rightNeighbor (ring4.rightNeighbor anchor4))
      (by decide) (by decide))


set_option maxHeartbeats 0 in
set_option maxRecDepth 262144 in
/-- The boundary row really survives as a Carrier. -/
private theorem after_carrier :
    BirthPhaseWait2BlockProgress.Carrier
      hpsi2 h2 hn4 ring4 anchor4 afterCross := by
  have hsource := source_carrier.1
  unfold BirthPhaseWait2BlockProgress.LocalCarrier
    BirthPhaseWait2Transfer.LocalWait2Carrier at hsource
  unfold BirthPhaseWait2BlockProgress.Carrier
    BirthPhaseWait2BlockProgress.LocalCarrier
    BirthPhaseWait2Transfer.LocalWait2Carrier
  constructor
  · refine { pass0 := ?_, pass1 := ?_, pass2 := ?_, lab0 := ?_, lab1 := ?_, lab2 := ?_ }
    · unfold Passive InertWriter Metadata
      decide
    · rw [afterCross_p1]
      exact hsource.pass1
    · rw [afterCross_p2]
      exact hsource.pass2
    · decide
    · rw [afterCross_p1]
      exact hsource.lab1
    · rw [afterCross_p2]
      exact hsource.lab2
  · have hf := crossing_shortCount_frame
      hpsi2 h2 hn4 ring4 anchor4 sourceC incomingEdge4 source_boundary
    unfold afterCross
    rw [← hf]
    exact source_carrier.2


theorem literal_surviving_crossing :
    SurvivingCrossingRow
      hpsi2 h2 hn4 2 0 ring4 anchor4 sourceC incomingEdge4 := by
  exact ⟨source_carrier, source_preCap, source_boundary, after_carrier⟩


/-- The tracked count does not merely fail to drop: it is exactly framed. -/
theorem literal_crossing_count_frame :
    BirthPhaseWait2BlockProgress.shortCountAt ring4 anchor4 sourceC =
      BirthPhaseWait2BlockProgress.shortCountAt ring4 anchor4 afterCross := by
  exact crossing_shortCount_frame
    hpsi2 h2 hn4 ring4 anchor4 sourceC incomingEdge4 source_boundary


private def sourceX :
    BirthPhaseB3DirtySuccess.CarrierState
      (kappa := 2) (tau := 0) hpsi2 h2 hn4 ring4 anchor4 :=
  ⟨sourceC, source_carrier⟩


private def rawSeed : Fin 4 -> AgentState 2 :=
  BirthPhaseB3DirtySuccess.projectedSeed
    hpsi2 h2 hn4 ring4 anchor4 sourceX


private def rawAfterCross : Fin 4 -> AgentState 2 :=
  BirthWaitClockMass.RawRing.rawRun
    (w := 2) (n := 4) (by decide : 2 < 4) (by decide : 2 <= 2)
    2 rawSeed [unrotateIndex ring4 anchor4 incomingEdge4]


theorem raw_crossing_is_rootIncoming :
    unrotateIndex ring4 anchor4 incomingEdge4 =
      BirthWaitClockMass.RawRing.rootIncoming
        (w := 2) (n := 4) (by decide : 2 < 4) := by
  decide


/-- The two endpoint keys agree at the seed. -/
theorem endpoint_keys_synced_before :
    (WaitKey.ofState (raw (sourceC anchor4)),
      WaitKey.ofState (raw (sourceC (ring4.rightNeighbor anchor4)))) =
    (WaitKey.ofState (rawSeed (p0 hn4)),
      WaitKey.ofState (rawSeed (p1 hn4))) := by
  decide


set_option maxHeartbeats 0 in
set_option maxRecDepth 262144 in
/-- Diagnostic for the mismatch: physical root is false, raw root is true. -/
theorem surviving_crossing_root_h_mismatch :
    (raw (afterCross anchor4)).h_field = false /\
      (rawAfterCross (p0 hn4)).h_field = true := by
  decide


set_option maxHeartbeats 0 in
set_option maxRecDepth 262144 in
/-- The same surviving crossing destroys the projected endpoint WaitKey pair.
At `psi = 2`, `WaitKey_of_waitPrefixProject` makes these literal physical keys
identical to their width-two projected keys. -/
theorem surviving_crossing_desynchronizes_keys :
    (WaitKey.ofState (raw (afterCross anchor4)),
      WaitKey.ofState
        (raw (afterCross (ring4.rightNeighbor anchor4)))) !=
    (WaitKey.ofState (rawAfterCross (p0 hn4)),
      WaitKey.ofState (rawAfterCross (p1 hn4))) := by
  decide


/-- The literal one-letter word inhabits exactly the proposed fourth case. -/
theorem literal_surviving_crossing_within :
    SurvivingCrossingWithin
      hpsi2 h2 hn4 2 0 ring4 anchor4 sourceC [incomingEdge4] := by
  unfold SurvivingCrossingWithin
  refine ⟨[], incomingEdge4, [], by simp, ?_⟩
  simpa using literal_surviving_crossing


#print axioms crossing_shortCount_frame
#print axioms literal_surviving_crossing
#print axioms surviving_crossing_desynchronizes_keys
#print axioms literal_surviving_crossing_within


end BirthPhaseB3SurvivingCrossing
