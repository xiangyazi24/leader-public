import Leader.Wu.Splice.PhysicalHoldTable

set_option autoImplicit false

/-! Pair census for V10e safety: every adjacent control-shape pair on the physical cores of the
n = 3 handoff fixture (cells 0 and 1, labels 0,0; cell 2 keeps its fixture core, label 1).  For
every SpliceSafeV7 start we check SpliceSafeV7 after each of the three services of stepV10e. -/

namespace B9V10eGlobalK3Census

open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation Q11593SpliceControllerDesign
open B9SpliceControllerR1Table B9SpliceControllerR1TableV2 B9SpliceControllerR1TableV3
  B9SpliceControllerR1TableV6 B9SpliceControllerR1TableV7 B9SpliceControllerR1TableV8
  B9SpliceControllerR1TableV9 B9SpliceControllerR1TableV10b B9SpliceV10cLiveness
  B9SpliceBlockDrainMass B9SpliceTableV10d B9SpliceTableV10e

private theorem hOne : 0 < 1 := by decide
private theorem hTwo : 0 < 2 := by decide
private theorem hThree : 0 < 3 := by decide
private theorem hOneTwo : 1 <= 2 := by decide
private def ring3 : DirectedRing 3 := ⟨hThree⟩

private instance instDecidableHostFenceShape (u : R1AgentStateV6 2 1 1) :
    Decidable (HostFenceShapeV7 u) := by unfold HostFenceShapeV7; infer_instance
private instance instDecidableTicketShape (u : R1AgentStateV6 2 1 1) :
    Decidable (TicketShapeV7 u) := by
  unfold TicketShapeV7 HostFenceShapeV7 ReservedFrontHoldGuard; infer_instance
private instance instDecidablePreparedDanger (C : R1ConfigV6 3 2 1 1) (e : Fin 3) :
    Decidable (PreparedDangerAt hTwo ring3 (projectV6 C) e) := by
  unfold PreparedDangerAt PreparedBarrierAt projectV6; dsimp only; unfold isBarrier; infer_instance
private instance instDecidableProtected (C : R1ConfigV6 3 2 1 1) (e : Fin 3) :
    Decidable (ProtectedSpliceEdgeV7 ring3 C e) := by
  unfold ProtectedSpliceEdgeV7 R1ProtectedSpliceEdgeV3 HostFenceShapeV7 ReservedFrontHoldGuard projectV6
  dsimp only; infer_instance
private instance instDecidableProvenance (C : R1ConfigV6 3 2 1 1) :
    Decidable (ProvenanceSafeV7 ring3 C) := by unfold ProvenanceSafeV7; infer_instance
private instance instDecidableSpliceSafe (C : R1ConfigV6 3 2 1 1) :
    Decidable (SpliceSafeV7 hTwo ring3 C) := by unfold SpliceSafeV7; infer_instance

private def base (i : Fin 3) : R1AgentStateV6 2 1 1 := clearTicketV6 (q11874StartV10b i)

private def mk (b : R1AgentStateV6 2 1 1) (r : SpliceRole) (p : Bool) : R1AgentStateV6 2 1 1 :=
  ⟨setControl b.carrier r p, false⟩

private def shapesOn (b : R1AgentStateV6 2 1 1) : List (R1AgentStateV6 2 1 1) :=
  [mk b .none false, setTicketV6 (mk b .none false) true, mk b .none true,
   mk b .front false, mk b .front true, setTicketV6 (mk b .front true) true, setTicketV6 (mk b .front false) true,
   mk b .predecessorArmed false, mk b .predecessorArmed true, setTicketV6 (mk b .predecessorArmed true) true,
   mk b .victimArmed false, mk b .victimArmed true, setTicketV6 (mk b .victimArmed true) true]

private def shapes : List (String × R1AgentStateV6 2 1 1) :=
  (shapesOn (base 0)).map (fun u => ("c0", u)) ++ (shapesOn (base 1)).map (fun u => ("c1", u))

private def pair (u v : R1AgentStateV6 2 1 1) : R1ConfigV6 3 2 1 1 := fun i =>
  if i = (0 : Fin 3) then u else if i = (1 : Fin 3) then v else base 2

private def tag (c : String) (u : R1AgentStateV6 2 1 1) : String :=
  s!"{c}:{repr (role u.carrier)}/{u.carrier.repairPending}/{u.acquireTicket}"

private def step (C : R1ConfigV6 3 2 1 1) (e : Fin 3) : R1ConfigV6 3 2 1 1 :=
  stepV10e hTwo hOne hOneTwo ring3 C e

private def thirds : List (String × R1AgentStateV6 2 1 1) :=
  [("c2:front/true/false", mk (base 2) .front true),
   ("c2:pred/true/false", mk (base 2) .predecessorArmed true),
   ("c2:victim/true/false", mk (base 2) .victimArmed true),
   ("c2:pred/false/false", mk (base 2) .predecessorArmed false),
   ("c2:fence", setTicketV6 (mk (base 2) .none false) true)]

private def triple (u v w : R1AgentStateV6 2 1 1) : R1ConfigV6 3 2 1 1 := fun i =>
  if i = (0 : Fin 3) then u else if i = (1 : Fin 3) then v else w

/-- Garbage measure: two per non-neutral role, one per pending bit, one per ticket. -/
private def measure (C : R1ConfigV6 3 2 1 1) : Nat := controllerPotentialV6 C

private def physicalAt (C : R1ConfigV6 3 2 1 1) (e : Fin 3) : Bool :=
  let D := step C e
  let q := BirthShortDoneTerminalHost.row hTwo hOne hOneTwo (C e).carrier.splice.base (C (ring3.rightNeighbor e)).carrier.splice.base
  decide ((D e).carrier.splice.base = q.1) && decide ((D (ring3.rightNeighbor e)).carrier.splice.base = q.2)

private def rolesClear (C : R1ConfigV6 3 2 1 1) : Bool := decide (measure C = 0)

private def progressWithin3 (C : R1ConfigV6 3 2 1 1) (e : Fin 3) : Bool :=
  let m0 := measure C
  let C1 := step C e; let C2 := step C1 e; let C3 := step C2 e
  physicalAt C e || decide (measure C1 < m0) || physicalAt C1 e || decide (measure C2 < m0) ||
  physicalAt C2 e || decide (measure C3 < m0)

-- safe, leaderless, non-clear triples with NO edge making progress within three of its own services

-- the all-fence ring: progress within three on edge 0?
private def fence0 : R1AgentStateV6 2 1 1 := setTicketV6 (mk (base 0) .none false) true

end B9V10eGlobalK3Census
