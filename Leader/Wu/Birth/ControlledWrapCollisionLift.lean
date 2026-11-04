import Leader.Wu.Birth.ControlledWrapDest


namespace BirthB1ControlledWrapCollisionLift


open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
open PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
open BirthWaitPassive BirthShortWait
open BirthB1ControlledWrap BirthB1ControlledWrapCanonical
open BirthB1ControlledWrapDest BirthB1RightDrainProducer
open Q11632RightDrainCollar
open BirthShortDoneTerminalB1EntranceR2
open BirthShortDoneTerminalPassiveR1
open BirthShortDoneTerminalPassiveR4


set_option autoImplicit false
set_option Elab.async false
set_option pp.structureInstances false


private theorem hTwo : 0 < 2 := by decide
private theorem hTwoLe : 2 <= 2 := by decide
private def ring4 : DirectedRing 4 := ⟨by decide⟩


abbrev C4 := BirthB1ControlledWrapDest.FC 4 2 2 0


private theorem fin4_cases (i : Fin 4) :
    i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by
  omega


private def regs (label : Fin 2) : Registers 2 where
  label := label
  h := false
  carry := false
  reset := false
  count := 0
  wait := true
  bit := false
  phase := false
  writer := .none


/-- Distance-zero state except that the maximal predecessor deliberately has
    label zero instead of the missing closing-edge label one. -/
private def badRaw (i : Fin 4) : AgentState 2 :=
  if i = 0 then { cell (regs 0) with echo := true }
  else if i = 1 then cell (regs 1)
  else if i = 2 then cell (regs 0)
  else { cell (regs 0) with reset_cmd := true }


private theorem badRaw_domain (i : Fin 4) :
    (badRaw i).inProtocolDomain 2 := by
  rcases fin4_cases i with rfl | rfl | rfl | rfl <;>
    simp [badRaw, regs, AgentState.inProtocolDomain,
      BirthWaitPassive.cell]


private def badC : C4 := fun i =>
  ⟨⟨BoundedAgentState.ofDomain (badRaw i) (badRaw_domain i), false⟩, 0⟩


private def badEdge : Fin 4 :=
  drainSite ring4 (0 : Fin 4) 1


private def badL := badC badEdge
private def badR := badC (ring4.rightNeighbor badEdge)


private theorem bad_drain_quiescent :
    DrainQuiescent (clearResetScar (raw badL)) := by
  unfold DrainQuiescent clearResetScar
  unfold BirthWaitPassive.Metadata BirthWaitPassive.InertWriter
  decide


private theorem bad_right_passive :
    Passive (clearEchoScar (raw badR)) := by
  unfold BirthWaitPassive.Passive clearEchoScar
  unfold BirthWaitPassive.Metadata BirthWaitPassive.InertWriter
  decide


private theorem bad_open_pair :
    PreparedOrdinaryOpen hTwo badL badR := by
  unfold BirthShortDoneTerminalB1EntranceR2.PreparedOrdinaryOpen
  dsimp only
  decide


private theorem bad_row_preCap :
    RowPreCap2 hTwo hTwoLe 2 ring4 badC badEdge := by
  unfold BirthShortDoneTerminalPassiveR4.RowPreCap2
    BirthShortDoneTerminalPassiveR4.RowCap2
  dsimp only
  decide


private theorem bad_preCap_pair :
    PreCapEntry2 hTwo hTwoLe 2 (raw badL) (raw badR) := by
  have h :=
    (BirthShortDoneTerminalPassiveR4.rowPreCap2_iff
      hTwo hTwoLe 2 0 ring4 badC badEdge).mp bad_row_preCap
  simpa [badL, badR] using h


/-- Every hypothesis of the pair leaf holds (with propositional
    inequality spelling for the old ASCII `!=`). -/
theorem bad_local_inputs :
    DrainQuiescent (clearResetScar (raw badL)) ∧
    (raw badL).reset_cmd = true ∧
    Passive (clearEchoScar (raw badR)) ∧
    (raw badR).echo = true ∧
    (raw badR).label ≠ widthTerminal hTwo hTwoLe ∧
    PreparedOrdinaryOpen hTwo badL badR ∧
    PreCapEntry2 hTwo hTwoLe 2 (raw badL) (raw badR) := by
  exact ⟨bad_drain_quiescent, by decide,
    bad_right_passive, by decide, by decide,
    bad_open_pair, bad_preCap_pair⟩


private def badLocalQ :=
  BirthShortDoneTerminalHost.row hTwo hTwo hTwoLe badL badR


set_option maxHeartbeats 200000000 in
set_option maxRecDepth 65536 in
/-- P-prime runs before SUPPRESS and repairs `0 -> 0` into `0 -> 1`.
    Hence the exact label-frame conclusion is false. -/
theorem bad_local_row_relabels_anchor :
    (raw badLocalQ.2).label ≠ (raw badR).label := by
  decide


/-- Consequently the exact conjunction promised by the leaf fails. -/
theorem bad_local_not_q11768_conclusion :
    ¬ (DrainQuiescent (raw badLocalQ.1) ∧
      Passive (raw badLocalQ.2) ∧
      (raw badLocalQ.1).reset_cmd = false ∧
      (raw badLocalQ.1).echo = false ∧
      (raw badLocalQ.2).reset_cmd = false ∧
      (raw badLocalQ.2).echo = false ∧
      (raw badLocalQ.1).label = (raw badL).label ∧
      (raw badLocalQ.2).label = (raw badR).label) := by
  intro h
  rcases h with ⟨_, _, _, _, _, _, _, hlabel⟩
  exact bad_local_row_relabels_anchor hlabel


private theorem bad_front :
    ResetFrontAt ring4 badC badC (0 : Fin 4) 1 := by
  refine ⟨by decide, by decide, ?_, ?_⟩
  · intro j hj
    have hj0 : j = 0 := by omega
    subst j
    decide
  · intro _ hj hle
    omega


private theorem bad_unique :
    UniqueProtectedEchoAt ring4 badC (0 : Fin 4) 0 := by
  refine ⟨by decide, by decide, ?_⟩
  intro q hq hne
  have hc : q = 0 ∨ q = 1 ∨ q = 2 := by omega
  rcases hc with rfl | rfl | rfl
  · exact (hne rfl).elim
  · decide
  · decide


private theorem bad_old_invariant :
    ControlledWrapInvariant hTwo ring4 badC badC
      (0 : Fin 4) 1 0 1 := by
  refine ⟨by decide, by decide, by decide, by decide,
    ?_, ?_, bad_front, bad_unique, ?_, ?_⟩
  · intro i
    rcases fin4_cases i with rfl | rfl | rfl | rfl <;> decide
  · unfold TripleLabels
    decide
  · intro q hgt hle
    have hc : q = 1 ∨ q = 2 := by omega
    rcases hc with rfl | rfl <;>
      unfold Passive Metadata InertWriter <;> decide
  · intro _ hk hlt
    omega


private theorem bad_destinations :
    ProtectedDestinationsCanonical ring4 badC (0 : Fin 4) 0 := by
  intro q hq _
  have hq0 : q = 0 := by omega
  subst q
  unfold clearEchoScar Passive Metadata InertWriter
  decide


private theorem bad_reset_canonical :
    CanonicalActiveReset ring4 badC (0 : Fin 4) 1 := by
  unfold CanonicalActiveReset clearResetScar
  unfold DrainQuiescent Metadata InertWriter
  decide


/-- The full current R6 distance-zero invariant permits this bad closing label. -/
theorem bad_collision_invariant :
    ControlledWrapInvariantDest hTwo ring4 badC badC
      (0 : Fin 4) 1 0 :=
  ⟨bad_old_invariant, bad_destinations, bad_reset_canonical⟩


private theorem bad_open :
    PreparedOrdinaryOpen hTwo
      (badC badEdge) (badC (ring4.rightNeighbor badEdge)) := by
  simpa [badL, badR] using bad_open_pair


private theorem bad_preCap :
    RowPreCap2 hTwo hTwoLe 2 ring4 badC badEdge := by
  exact bad_row_preCap


private def badD : C4 :=
  BirthShortDoneTerminalConsumer.step
    hTwo hTwo hTwoLe ring4 badC badEdge


set_option maxHeartbeats 200000000 in
set_option maxRecDepth 65536 in
private theorem badD_no_leader : ¬ HasLeader badD := by
  intro h
  rcases h with ⟨i, hi⟩
  rcases fin4_cases i with rfl | rfl | rfl | rfl <;>
    exact absurd hi (by decide)


set_option maxHeartbeats 200000000 in
set_option maxRecDepth 65536 in
private theorem badD_not_triple :
    ¬ TripleLabels hTwo ring4 badD (0 : Fin 4) := by
  unfold TripleLabels
  decide


/-- The requested global collision statement also fails for the same reason. -/
theorem controlledWrapDestCollisionConsumerStepStatement_false :
    ¬ ControlledWrapDestCollisionConsumerStepStatement
      (kappa := 2) (tau := 0) hTwo hTwoLe ring4 := by
  intro h
  have hout := h badC badC (0 : Fin 4) 1
    bad_collision_invariant bad_open bad_preCap
  rcases hout with hleader | hgood
  · exact badD_no_leader hleader
  · exact badD_not_triple hgood.2.1


/-- Minimal corrected local interface.  Alignment keeps P-prime from relabeling
    the anchor; full-ruler nonterminality is exactly the hypothesis consumed by
    `suppress_echo_collision_row`. -/
def FullTerminalRow2ResetEchoCollisionAlignedPreCapStatement : Prop :=
  ∀ (psi kappa tau : Nat) (hpsi : 0 < psi) (h2 : 2 <= psi)
      (l r : ExpiringAgentState psi kappa tau),
    DrainQuiescent (clearResetScar (raw l)) ->
    (raw l).reset_cmd = true ->
    Passive (clearEchoScar (raw r)) ->
    (raw r).echo = true ->
    (raw r).label =
      ⟨((raw l).label.val + 1) % psi, Nat.mod_lt _ hpsi⟩ ->
    (raw r).label ≠ (⟨psi - 1, by omega⟩ : Fin psi) ->
    PreparedOrdinaryOpen hpsi l r ->
    PreCapEntry2 hpsi h2 kappa (raw l) (raw r) ->
    let q := BirthShortDoneTerminalHost.row
      hpsi (by decide : 0 < 2) h2 l r
    DrainQuiescent (raw q.1) ∧
      Passive (raw q.2) ∧
      (raw q.1).reset_cmd = false ∧
      (raw q.1).echo = false ∧
      (raw q.2).reset_cmd = false ∧
      (raw q.2).echo = false ∧
      (raw q.1).label = (raw l).label ∧
      (raw q.2).label = (raw r).label


#print axioms BirthB1ControlledWrapCollisionLift.bad_local_inputs
#print axioms BirthB1ControlledWrapCollisionLift.bad_local_row_relabels_anchor
#print axioms BirthB1ControlledWrapCollisionLift.bad_collision_invariant
#print axioms BirthB1ControlledWrapCollisionLift.controlledWrapDestCollisionConsumerStepStatement_false


end BirthB1ControlledWrapCollisionLift
