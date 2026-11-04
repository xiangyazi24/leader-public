import Leader.Wu.Splice.ZeroRefreshBlockMass
import Leader.Wu.Birth.DrainCoupling
import Leader.Wu.Splice.MovingFrontLeaderlessCycles

set_option autoImplicit false
set_option Elab.async false
set_option pp.structureInstances false

namespace B9SpliceLiveSelector

open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
open Q11593SpliceControllerDesign
open B9SpliceControllerR1Table B9SpliceControllerR1TableV2
  B9SpliceControllerR1TableV3 B9SpliceControllerR1TableV6
  B9SpliceControllerR1TableV7 B9SpliceControllerR1TableV8
  B9SpliceControllerR1TableV9 B9SpliceControllerR1TableV10b
open B9SpliceV10cLiveness B9SpliceBlockDrainMass
open FiniteUniformStoppingTree

variable {n psi kappa tau : Nat}

private instance instDecidableHostFenceShape
    (u : R1AgentStateV6 psi kappa tau) :
    Decidable (HostFenceShapeV7 u) := by
  unfold HostFenceShapeV7
  infer_instance

private instance instDecidableTicketShape
    (u : R1AgentStateV6 psi kappa tau) :
    Decidable (TicketShapeV7 u) := by
  unfold TicketShapeV7 HostFenceShapeV7 ReservedFrontHoldGuard
  infer_instance

private instance instDecidablePreparedDanger
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (C : R1ConfigV6 n psi kappa tau) (e : Fin n) :
    Decidable (PreparedDangerAt hpsi ring (projectV6 C) e) := by
  unfold PreparedDangerAt PreparedBarrierAt projectV6
  dsimp only
  unfold isBarrier
  infer_instance

private instance instDecidableProtected
    (ring : DirectedRing n)
    (C : R1ConfigV6 n psi kappa tau) (e : Fin n) :
    Decidable (ProtectedSpliceEdgeV7 ring C e) := by
  unfold ProtectedSpliceEdgeV7 R1ProtectedSpliceEdgeV3
    HostFenceShapeV7 ReservedFrontHoldGuard projectV6
  dsimp only
  infer_instance

private instance instDecidableProvenance
    (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau) :
    Decidable (ProvenanceSafeV7 ring C) := by
  unfold ProvenanceSafeV7
  infer_instance

private instance instDecidableSpliceSafe
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (C : R1ConfigV6 n psi kappa tau) :
    Decidable (SpliceSafeV7 hpsi ring C) := by
  unfold SpliceSafeV7
  infer_instance

private instance instDecidableRolesClear
    (C : R1ConfigV6 n psi kappa tau) :
    Decidable (RolesClearV7 C) := by
  unfold RolesClearV7
  infer_instance

private theorem hOne : 0 < 1 := by decide
private theorem hTwo : 0 < 2 := by decide
private theorem hOneTwo : 1 <= 2 := by decide
private theorem hFour : 0 < 4 := by decide
private def ring4 : DirectedRing 4 := ⟨hFour⟩

private def neutral0 : R1AgentStateV6 2 0 0 :=
  liftAgentV6
    (B9SpliceR2AttackRerun.xcell false 0 false .none false)

private def front0 : R1AgentStateV6 2 0 0 :=
  liftAgentV6
    (B9SpliceR2AttackRerun.xcell false 0 false .front true)

private def front1 : R1AgentStateV6 2 0 0 :=
  liftAgentV6
    (B9SpliceR2AttackRerun.xcell false 1 false .front true)

/-- Alternating physical labels eliminate prepared danger.  The three
non-neutral sites are unticketed reserved fronts. -/
def badC : R1ConfigV6 4 2 0 0 := fun i =>
  if i = (0 : Fin 4) then neutral0
  else if i = (1 : Fin 4) then front1
  else if i = (2 : Fin 4) then front0
  else front1

/-- Edges 0,1,2 see an orphan reserved front on the right; edge 3 is itself a
reserved-front HOLD. -/
theorem bad_hold_census :
    OrphanReservedFrontGuardV3 (badC 0).carrier (badC 1).carrier ∧
    OrphanReservedFrontGuardV3 (badC 1).carrier (badC 2).carrier ∧
    OrphanReservedFrontGuardV3 (badC 2).carrier (badC 3).carrier ∧
    ReservedFrontHoldGuard (badC 3).carrier := by
  decide

theorem bad_safe : SpliceSafeV7 hTwo ring4 badC := by
  decide

theorem bad_not_clear : ¬ RolesClearV7 badC := by
  decide

theorem bad_live : LiveNonClearV10c hTwo ring4 badC :=
  ⟨bad_safe, bad_not_clear⟩

set_option maxRecDepth 8000 in
/-- Every scheduler edge is a literal V10c stutter. -/
theorem bad_all_services_stutter :
    ∀ e i : Fin 4,
      stepV10c hTwo hOne hOneTwo ring4 badC e i = badC i := by
  decide

/-- Hence no edge has the requested controller drop-or-end property. -/
theorem bad_no_productive_edge :
    ∀ e : Fin 4,
      ¬ ControllerProductiveServiceV10c
        hTwo hOne hOneTwo ring4 badC e := by
  intro e hprod
  have heq : stepV10c hTwo hOne hOneTwo ring4 badC e = badC :=
    funext (bad_all_services_stutter e)
  change
    controllerPotentialV6 (stepV10c hTwo hOne hOneTwo ring4 badC e) <
        controllerPotentialV6 badC ∨
      RolesClearV7 (stepV10c hTwo hOne hOneTwo ring4 badC e)
    at hprod
  rcases hprod with hdrop | hclear
  · rw [heq] at hdrop
    exact Nat.lt_irrefl _ hdrop
  · rw [heq] at hclear
    exact bad_not_clear hclear

/-- The requested global selector statement is therefore false already at
n=4, psi=2, width=1, kappa=tau=0. -/
theorem no_general_live_selector :
    ¬ (∀ C : R1ConfigV6 4 2 0 0,
      LiveNonClearV10c hTwo ring4 C →
      ∃ e : Fin 4,
        ControllerProductiveServiceV10c
          hTwo hOne hOneTwo ring4 C e) := by
  intro h
  obtain ⟨e, he⟩ := h badC bad_live
  exact bad_no_productive_edge e he

/-- In particular, no adapter can satisfy the productive-service clause that
the (now deleted) one-service block bridge asserted, at these parameters. -/
theorem no_bridge_service_clause
    (A : BirthB1DrainCoupling.PortBlockAdapter (R1ConfigV6 4 2 0 0) 4) :
    ¬ (∀ C, LiveNonClearV10c hTwo ring4 C →
      ControllerProductiveServiceV10c
        hTwo hOne hOneTwo ring4 C (A.ports C).a) := by
  intro h
  exact bad_no_productive_edge (A.ports badC).a (h badC bad_live)

#print axioms B9SpliceLiveSelector.bad_hold_census
#print axioms B9SpliceLiveSelector.bad_safe
#print axioms B9SpliceLiveSelector.bad_all_services_stutter
#print axioms B9SpliceLiveSelector.bad_no_productive_edge
#print axioms B9SpliceLiveSelector.no_general_live_selector
#print axioms B9SpliceLiveSelector.no_bridge_service_clause

end B9SpliceLiveSelector
