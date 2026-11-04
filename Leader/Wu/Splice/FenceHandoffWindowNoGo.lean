import Leader.Wu.Splice.FenceHandoffTable

set_option autoImplicit false
set_option Elab.async false
set_option pp.structureInstances false

namespace B9SpliceV10bWindowLaw

open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
  PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
open PPLLLeaderCreationCleanupRepair
  PPLLNoCheckBirthConditionTwoPhysical PPLLNoCheckBirthConditionTwoProtocol
open BirthSigMoveDisposalRepair BirthShortDoneTerminalBirthSources
  Q11593SpliceControllerDesign
open B9SpliceControllerR1Table B9SpliceControllerR1TableV2
  B9SpliceControllerR1TableV3 B9SpliceControllerR1TableV4
  B9SpliceControllerR1TableV6 B9SpliceControllerR1TableV7
  B9SpliceControllerR1TableV8 B9SpliceControllerR1TableV9
  B9SpliceControllerR1TableV10b

variable {n psi width kappa tau : Nat}

private instance instDecidablePreparedDanger
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (C : R1ConfigV6 n psi kappa tau) (e : Fin n) :
    Decidable (PreparedDangerAt hpsi ring (projectV6 C) e) := by
  unfold PreparedDangerAt PreparedBarrierAt projectV6
  dsimp only
  unfold isBarrier
  infer_instance

private instance instDecidableProtectedSpliceEdge
    (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau) (e : Fin n) :
    Decidable (ProtectedSpliceEdgeV7 ring C e) := by
  unfold ProtectedSpliceEdgeV7 R1ProtectedSpliceEdgeV3
    HostFenceShapeV7 ReservedFrontHoldGuard projectV6
  dsimp only
  infer_instance

private instance instDecidableTicketShape
    (u : R1AgentStateV6 psi kappa tau) : Decidable (TicketShapeV7 u) := by
  unfold TicketShapeV7 HostFenceShapeV7 ReservedFrontHoldGuard
  infer_instance

private instance instDecidableProvenanceSafe
    (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau) :
    Decidable (ProvenanceSafeV7 ring C) := by
  unfold ProvenanceSafeV7
  infer_instance

private instance instDecidableSpliceSafe
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (C : R1ConfigV6 n psi kappa tau) : Decidable (SpliceSafeV7 hpsi ring C) := by
  unfold SpliceSafeV7
  infer_instance

private instance instDecidableRolesClear
    (C : R1ConfigV6 n psi kappa tau) : Decidable (RolesClearV7 C) := by
  unfold RolesClearV7
  infer_instance

private instance instDecidableLiveAlong
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau)
    (es : List (Fin n)) : Decidable (LiveAlongV10b hpsi hwidth hle ring C es) :=
  match es with
  | [] => instDecidableSpliceSafe hpsi ring C
  | e :: es =>
      letI : Decidable (LiveAlongV10b hpsi hwidth hle ring
          (stepV10b hpsi hwidth hle ring C e) es) :=
        instDecidableLiveAlong hpsi hwidth hle ring
          (stepV10b hpsi hwidth hle ring C e) es
      instDecidableAnd

private theorem hOne : 0 < 1 := by decide
private theorem hThree : 0 < 3 := by decide
private theorem hLe : 1 <= 1 := by decide
private def ring3 : DirectedRing 3 := ⟨hThree⟩
private def peace1 : PeaceView 1 :=
  { leader := false, label := 0, shield := false, bullet := 0, signal_B := 0 }
private def rawL : AgentState 1 := PeaceView.toState peace1
private def rawR : AgentState 1 := { PeaceView.toState peace1 with write_state := .depart }
private theorem rawLDomain : rawL.inProtocolDomain 1 := by
  simp [rawL, peace1, PeaceView.toState, AgentState.inProtocolDomain]
private theorem rawRDomain : rawR.inProtocolDomain 1 := by
  simp [rawR, peace1, PeaceView.toState, AgentState.inProtocolDomain]
private def topStall : Fin 2 := ⟨1, by decide⟩
private def expL : ExpiringAgentState 1 1 1 :=
  ⟨⟨BoundedAgentState.ofDomain rawL rawLDomain, false⟩, topStall⟩
private def expR : ExpiringAgentState 1 1 1 :=
  ⟨⟨BoundedAgentState.ofDomain rawR rawRDomain, false⟩, topStall⟩
private def neutralCarrier (b : ExpiringAgentState 1 1 1) : R1AgentStateV4 1 1 1 :=
  { splice := { base := b, spliceRole := .none }, repairPending := false }
private def neutralL : R1AgentStateV6 1 1 1 := liftAgentV6 (neutralCarrier expL)
private def neutralR : R1AgentStateV6 1 1 1 := liftAgentV6 (neutralCarrier expR)
private def blocker : R1AgentStateV6 1 1 1 :=
  setControlV6 (liftAgentV6 (neutralCarrier expL)) .predecessorArmed false
private def S0 : R1ConfigV6 3 1 1 1 := fun i =>
  if i = (0 : Fin 3) then neutralL else if i = (1 : Fin 3) then neutralR else blocker
private def S1 : R1ConfigV6 3 1 1 1 := stepV10b hOne hOne hLe ring3 S0 0
private def S2 : R1ConfigV6 3 1 1 1 := stepV10b hOne hOne hLe ring3 S1 0
private def S3 : R1ConfigV6 3 1 1 1 := stepV10b hOne hOne hLe ring3 S2 0
private def window3 : List (Fin 3) := [0, 0, 0]

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
private theorem liveWindow3 : LiveAlongV10b hOne hOne hLe ring3 S0 window3 := by decide

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
theorem timerPeriodTwoFromStartFails : S2 (1 : Fin 3) ≠ S0 (1 : Fin 3) := by decide

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
theorem timerPeriodTwoAfterFirst : S3 = S1 := by
  funext i
  have hv : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 := by omega
  rcases hv with h | h | h
  · have hi : i = (0 : Fin 3) := Fin.ext h
    subst i
    decide
  · have hi : i = (1 : Fin 3) := Fin.ext h
    subst i
    decide
  · have hi : i = (2 : Fin 3) := Fin.ext h
    subst i
    decide

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
private theorem flat01 : controllerPotentialV6 S1 = controllerPotentialV6 S0 := by decide
set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
private theorem flat12 : controllerPotentialV6 S2 = controllerPotentialV6 S1 := by decide
private theorem flat23 : controllerPotentialV6 S3 = controllerPotentialV6 S2 := by
  rw [timerPeriodTwoAfterFirst]
  exact flat12.symm
private theorem notClear0 : ¬ RolesClearV7 S0 := by decide
set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
private theorem notClear1 : ¬ RolesClearV7 S1 := by decide
set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
private theorem notClear2 : ¬ RolesClearV7 S2 := by decide
private theorem notClear3 : ¬ RolesClearV7 S3 := by
  rw [timerPeriodTwoAfterFirst]
  exact notClear1

private theorem dropPrefixCases
    (pre post : List (Fin 3)) (e : Fin 3)
    (h : window3 = pre ++ e :: post) :
    (pre = [] ∧ e = 0) ∨ (pre = [0] ∧ e = 0) ∨ (pre = [0, 0] ∧ e = 0) := by
  cases pre with
  | nil => simp_all [window3]
  | cons a as =>
      cases as with
      | nil =>
          simp_all [window3]
          rcases h with ⟨rfl, rfl, -⟩
          rfl
      | cons b bs =>
          cases bs with
          | nil =>
              simp_all [window3]
              rcases h with ⟨rfl, rfl, rfl, -⟩
              exact ⟨rfl, rfl⟩
          | cons c cs => simp_all [window3]

private theorem clearPrefixCases
    (pre post : List (Fin 3)) (h : window3 = pre ++ post) :
    pre = [] ∨ pre = [0] ∨ pre = [0, 0] ∨ pre = [0, 0, 0] := by
  cases pre with
  | nil => simp_all [window3]
  | cons a as =>
      cases as with
      | nil => simp_all [window3]
      | cons b bs =>
          cases bs with
          | nil =>
              simp_all [window3]
              rcases h with ⟨rfl, rfl, -⟩
              rfl
          | cons c cs =>
              cases cs with
              | nil =>
                  simp_all [window3]
                  rcases h with ⟨rfl, rfl, rfl, -⟩
                  exact ⟨rfl, rfl⟩
              | cons d ds => simp_all [window3]

/-- V10bWindowDrainOrEnd is false already on the smallest admitted ring. -/
theorem not_V10bWindowDrainOrEnd :
    ¬ V10bWindowDrainOrEnd (kappa := 1) (tau := 1) hOne hOne hLe ring3 := by
  intro hwindow
  have hout := hwindow (Nat.le_refl 3) S0 window3 (by decide) liveWindow3
  rcases hout with hdrop | hclear
  · rcases hdrop with ⟨pre, e, post, hsplit, hlt⟩
    rcases dropPrefixCases pre post e hsplit with h0 | h1 | h2
    · rcases h0 with ⟨rfl, rfl⟩
      change controllerPotentialV6 S1 < controllerPotentialV6 S0 at hlt
      rw [flat01] at hlt
      exact Nat.lt_irrefl _ hlt
    · rcases h1 with ⟨rfl, rfl⟩
      change controllerPotentialV6 S2 < controllerPotentialV6 S1 at hlt
      rw [flat12] at hlt
      exact Nat.lt_irrefl _ hlt
    · rcases h2 with ⟨rfl, rfl⟩
      change controllerPotentialV6 S3 < controllerPotentialV6 S2 at hlt
      rw [flat23] at hlt
      exact Nat.lt_irrefl _ hlt
  · rcases hclear with ⟨pre, post, hsplit, hc⟩
    rcases clearPrefixCases pre post hsplit with h0 | h1 | h2 | h3
    · subst pre; change RolesClearV7 S0 at hc; exact notClear0 hc
    · subst pre; change RolesClearV7 S1 at hc; exact notClear1 hc
    · subst pre; change RolesClearV7 S2 at hc; exact notClear2 hc
    · subst pre; change RolesClearV7 S3 at hc; exact notClear3 hc

end B9SpliceV10bWindowLaw

#print axioms B9SpliceV10bWindowLaw.timerPeriodTwoFromStartFails
#print axioms B9SpliceV10bWindowLaw.timerPeriodTwoAfterFirst
#print axioms B9SpliceV10bWindowLaw.not_V10bWindowDrainOrEnd
