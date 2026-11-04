import Leader.Wu.Splice.FenceHandoffWindowNoGo


set_option autoImplicit false
set_option Elab.async false
set_option pp.structureInstances false


namespace B9SpliceV10cLiveness


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


def SameExceptStall (u v : R1AgentStateV6 psi kappa tau) : Prop :=
  u.carrier.splice.base.core = v.carrier.splice.base.core /\
  role u.carrier = role v.carrier /\
  u.carrier.repairPending = v.carrier.repairPending /\
  u.acquireTicket = v.acquireTicket


def ZeroRefreshOnlyGuardV10c
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (l r : R1AgentStateV6 psi kappa tau) : Prop :=
  let q := rowV10b hpsi hwidth hle l r
  q = ordinaryHostWriteV7 hpsi hwidth hle l r /\
  l.carrier.splice.base.stall.val = 0 /\
  r.carrier.splice.base.stall.val = 0 /\
  SameExceptStall q.1 l /\ SameExceptStall q.2 r


private instance instDecidableZeroRefreshOnlyGuardV10c
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (l r : R1AgentStateV6 psi kappa tau) :
    Decidable (ZeroRefreshOnlyGuardV10c hpsi hwidth hle l r) := by
  unfold ZeroRefreshOnlyGuardV10c SameExceptStall
  dsimp only
  infer_instance


def rowV10c
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (l r : R1AgentStateV6 psi kappa tau) :=
  if ZeroRefreshOnlyGuardV10c hpsi hwidth hle l r then (l, r)
  else rowV10b hpsi hwidth hle l r


def stepV10c
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau) (e : Fin n) :=
  let j := ring.rightNeighbor e
  if j = e then C else
    let q := rowV10c hpsi hwidth hle (C e) (C j)
    fun i => if i = e then q.1 else if i = j then q.2 else C i


private instance instDecidableRolesClear
    (C : R1ConfigV6 n psi kappa tau) : Decidable (RolesClearV7 C) := by
  unfold RolesClearV7
  infer_instance


/-- Candidate (a): every nonstutter service drops V6 potential or ends. -/
def PotentialDropOrEndV10c
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (ring : DirectedRing n) : Prop :=
  forall (C : R1ConfigV6 n psi kappa tau) e,
      (exists i, stepV10c hpsi hwidth hle ring C e i != C i) ->
    controllerPotentialV6 (stepV10c hpsi hwidth hle ring C e) <
      controllerPotentialV6 C \/
    RolesClearV7 (stepV10c hpsi hwidth hle ring C e)


/-- Structural half of (b); the counting layer supplies the constant mass. -/
def SchedulerServiceV10c
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau) : Prop :=
  exists e i, stepV10c hpsi hwidth hle ring C e i != C i


/-- What timer consumers may use on the guarded branch. -/
theorem guarded_stall_frame
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (l r : R1AgentStateV6 psi kappa tau)
    (hg : ZeroRefreshOnlyGuardV10c hpsi hwidth hle l r) :
    (rowV10c hpsi hwidth hle l r).1.carrier.splice.base.stall =
        l.carrier.splice.base.stall /\
    (rowV10c hpsi hwidth hle l r).2.carrier.splice.base.stall =
        r.carrier.splice.base.stall := by
  simp [rowV10c, hg]


/-- V10c has V10b's factor 16; the V6 potential itself is bounded by 8*n. -/
theorem potential_le_factor_mul (C : R1ConfigV6 n psi kappa tau) :
    controllerPotentialV6 C <= 16 * n := by
  have h := controllerPotentialV6_le_eight_mul C
  omega


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
private def neutralL := liftAgentV6 (neutralCarrier expL)
private def neutralR := liftAgentV6 (neutralCarrier expR)
private def blocker : R1AgentStateV6 1 1 1 :=
  setControlV6 (liftAgentV6 (neutralCarrier expL)) .predecessorArmed false
private def C30 : R1ConfigV6 3 1 1 1 := fun i =>
  if i = (0 : Fin 3) then neutralL else if i = (1 : Fin 3) then neutralR else blocker
private def C31 := stepV10c hOne hOne hLe ring3 C30 0
private def C32 := stepV10c hOne hOne hLe ring3 C31 0
private def C33 := stepV10c hOne hOne hLe ring3 C32 0
private def q31 := rowV10b hOne hOne hLe (C31 0) (C31 1)


def Same3 (C D : R1ConfigV6 3 1 1 1) : Prop :=
  C 0 = D 0 /\ C 1 = D 1 /\ C 2 = D 2


set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
/-- The failed V10c guard is the physical-core clause, not controller state. -/
theorem edge0_actual :
    q31 = ordinaryHostWriteV7 hOne hOne hLe (C31 0) (C31 1) /\
    (C31 0).carrier.splice.base.stall.val = 0 /\
    (C31 1).carrier.splice.base.stall.val = 0 /\
    ¬ ZeroRefreshOnlyGuardV10c hOne hOne hLe (C31 0) (C31 1) /\
    ¬ (SameExceptStall q31.1 (C31 0) /\ SameExceptStall q31.2 (C31 1)) /\
    role q31.1.carrier = role (C31 0).carrier /\
    role q31.2.carrier = role (C31 1).carrier /\
    q31.1.carrier.repairPending = (C31 0).carrier.repairPending /\
    q31.2.carrier.repairPending = (C31 1).carrier.repairPending /\
    q31.1.acquireTicket = (C31 0).acquireTicket /\
    q31.2.acquireTicket = (C31 1).acquireTicket /\
    (q31.1.carrier.splice.base.core != (C31 0).carrier.splice.base.core \/
      q31.2.carrier.splice.base.core != (C31 1).carrier.splice.base.core) /\
    q31.1.carrier.splice.base.stall.val = 1 /\
    q31.2.carrier.splice.base.stall.val = 1 := by
  try simp only [ZeroRefreshOnlyGuardV10c, SameExceptStall, Same3]
  decide


set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
/-- Edge 0 is a genuine flat period-two orbit after the first service. -/
theorem edge0_flat_cycle :
    ¬ Same3 C32 C31 /\ Same3 C33 C31 /\
    controllerPotentialV6 C32 = controllerPotentialV6 C31 /\
    controllerPotentialV6 C33 = controllerPotentialV6 C32 := by
  try simp only [ZeroRefreshOnlyGuardV10c, SameExceptStall, Same3]
  decide


set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
/-- Part (b) does hold on both live states: edge 2 is the predecessor scrub. -/
theorem cycle_scheduler_service :
    SchedulerServiceV10c hOne hOne hLe ring3 C31 /\
    SchedulerServiceV10c hOne hOne hLe ring3 C32 := by
  constructor
  · exact ⟨2, 2, by decide⟩
  · exact ⟨2, 2, by decide⟩


set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
/-- The first half of the two-cycle directly refutes candidate (a). -/
theorem edge0_flat_nonstutter :
    (exists i, C32 i != C31 i) /\
    controllerPotentialV6 C32 = controllerPotentialV6 C31 /\
    ¬ RolesClearV7 C32 := by
  try simp only [ZeroRefreshOnlyGuardV10c, SameExceptStall, Same3]
  decide


theorem not_potentialDropOrEndV10c :
    ¬ PotentialDropOrEndV10c (kappa := 1) (tau := 1) hOne hOne hLe ring3 := by
  intro h
  have hc := edge0_flat_nonstutter
  have hx := h C31 0 hc.1
  change controllerPotentialV6 C32 < controllerPotentialV6 C31 \/ RolesClearV7 C32 at hx
  rcases hx with hp | he
  · rw [hc.2.1] at hp
    exact Nat.lt_irrefl _ hp
  · exact hc.2.2 he


end B9SpliceV10cLiveness


#print axioms B9SpliceV10cLiveness.guarded_stall_frame
#print axioms B9SpliceV10cLiveness.potential_le_factor_mul
#print axioms B9SpliceV10cLiveness.edge0_actual
#print axioms B9SpliceV10cLiveness.edge0_flat_cycle
#print axioms B9SpliceV10cLiveness.cycle_scheduler_service
#print axioms B9SpliceV10cLiveness.not_potentialDropOrEndV10c
