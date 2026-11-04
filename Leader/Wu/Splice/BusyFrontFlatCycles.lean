import Leader.Wu.Splice.BusyFrontStrictRankNoGo


set_option autoImplicit false
set_option Elab.async false
set_option pp.structureInstances false


namespace B9SpliceV9RankRedesign


open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
  PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
open PPLLLeaderCreationCleanupRepair BirthSigMoveDisposalRepair
  BirthShortDoneTerminalBirthSources Q11593SpliceControllerDesign
open B9SpliceControllerR1Table B9SpliceControllerR1TableV2
  B9SpliceControllerR1TableV3 B9SpliceControllerR1TableV4
  B9SpliceControllerR1TableV6 B9SpliceControllerR1TableV7
  B9SpliceControllerR1TableV8 B9SpliceControllerR1TableV9
  B9SpliceV9StrictRank


variable {n psi width kappa tau : Nat}


private instance instDecidableHostFenceShape
    (u : R1AgentStateV6 psi kappa tau) : Decidable (HostFenceShapeV7 u) := by
  unfold HostFenceShapeV7
  infer_instance


private instance instDecidableTicketShape
    (u : R1AgentStateV6 psi kappa tau) : Decidable (TicketShapeV7 u) := by
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


private instance instDecidableProtectedSpliceEdge
    (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau) (e : Fin n) :
    Decidable (ProtectedSpliceEdgeV7 ring C e) := by
  unfold ProtectedSpliceEdgeV7 R1ProtectedSpliceEdgeV3
    HostFenceShapeV7 ReservedFrontHoldGuard projectV6
  dsimp only
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


private theorem hOne : 0 < 1 := by decide
private theorem hTwo : 0 < 2 := by decide
private theorem hThree : 0 < 3 := by decide
private theorem hOneTwo : 1 <= 2 := by decide
private theorem hOneThree : 1 <= 3 := by decide
private theorem hTwoLe : 2 <= 2 := by decide
private def ring2 : DirectedRing 2 := ⟨hTwo⟩
private def ring3 : DirectedRing 3 := ⟨hThree⟩


def runV9Word
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (ring : DirectedRing n) :
    R1ConfigV6 n psi kappa tau -> List (Fin n) -> R1ConfigV6 n psi kappa tau
  | C, [] => C
  | C, e :: es =>
      runV9Word hpsi hwidth hle ring
        (stepV9 hpsi hwidth hle ring C e) es


def LiveAlongV9
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (ring : DirectedRing n) :
    R1ConfigV6 n psi kappa tau -> List (Fin n) -> Prop
  | C, [] => SpliceSafeV7 hpsi ring C
  | C, e :: es =>
      SpliceSafeV7 hpsi ring C /\
      (exists i, stepV9 hpsi hwidth hle ring C e i != C i) /\
      LiveAlongV9 hpsi hwidth hle ring
        (stepV9 hpsi hwidth hle ring C e) es


def AdvanceAlongV9
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (ring : DirectedRing n) :
    R1ConfigV6 n psi kappa tau -> List (Fin n) -> Prop
  | _, [] => True
  | C, e :: es =>
      rowV9 hpsi hwidth hle (C e) (C (ring.rightNeighbor e)) =
        hostFenceLeftAdvanceWriteV7 hpsi
          (C e) (C (ring.rightNeighbor e)) /\
      AdvanceAlongV9 hpsi hwidth hle ring
        (stepV9 hpsi hwidth hle ring C e) es


private instance instDecidableLiveAlongV9
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau)
    (es : List (Fin n)) :
    Decidable (LiveAlongV9 hpsi hwidth hle ring C es) :=
  match es with
  | [] => instDecidableSpliceSafe hpsi ring C
  | e :: es =>
      letI : Decidable
          (LiveAlongV9 hpsi hwidth hle ring
            (stepV9 hpsi hwidth hle ring C e) es) :=
        instDecidableLiveAlongV9 hpsi hwidth hle ring
          (stepV9 hpsi hwidth hle ring C e) es
      instDecidableAnd


private instance instDecidableAdvanceAlongV9
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau)
    (es : List (Fin n)) :
    Decidable (AdvanceAlongV9 hpsi hwidth hle ring C es) :=
  match es with
  | [] => isTrue trivial
  | e :: es =>
      letI : Decidable
          (AdvanceAlongV9 hpsi hwidth hle ring
            (stepV9 hpsi hwidth hle ring C e) es) :=
        instDecidableAdvanceAlongV9 hpsi hwidth hle ring
          (stepV9 hpsi hwidth hle ring C e) es
      instDecidableAnd


def cycle2Word : List (Fin 2) := [0, 1, 0, 1, 0, 1]


theorem advanceFlat_cycle2 :
    LiveAlongV9 hThree hOne hOneThree ring2 advanceFlatStart cycle2Word /\
    AdvanceAlongV9 hThree hOne hOneThree ring2 advanceFlatStart cycle2Word /\
    (forall i, runV9Word hThree hOne hOneThree ring2
      advanceFlatStart cycle2Word i = advanceFlatStart i) := by
  decide


private def zeroCell3 : R1AgentStateV6 2 1 1 :=
  clearControlV6 (q11703StartV7 (1 : Fin 3))


private def oneCell3 : R1AgentStateV6 2 1 1 :=
  clearControlV6 (q11703StartV7 (2 : Fin 3))


def advanceFlatStart3 : R1ConfigV6 3 2 1 1 := fun i =>
  if i = (0 : Fin 3) then setTicketV6 zeroCell3 true
  else if i = (1 : Fin 3) then zeroCell3
  else oneCell3


def advanceFlatAfter3 : R1ConfigV6 3 2 1 1 :=
  stepV9 hTwo hOne hOneTwo ring3 advanceFlatStart3 (0 : Fin 3)


def cycle3Word : List (Fin 3) := [0, 1, 2, 0, 1, 2]


theorem advanceFlat3_first_rank_equal :
    compositeRankV9 hTwo ring3 advanceFlatAfter3 =
      compositeRankV9 hTwo ring3 advanceFlatStart3 := by
  decide


theorem advanceFlat_cycle3 :
    LiveAlongV9 hTwo hOne hOneTwo ring3 advanceFlatStart3 cycle3Word /\
    AdvanceAlongV9 hTwo hOne hOneTwo ring3 advanceFlatStart3 cycle3Word /\
    (forall i, runV9Word hTwo hOne hOneTwo ring3
      advanceFlatStart3 cycle3Word i = advanceFlatStart3 i) := by
  decide


set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
theorem q11703_first_advance_local_drop :
    compositeRankV9 hTwo ring3 q11703Fence1V8 <
      compositeRankV9 hTwo ring3 q11703ArmedAfterV8 := by
  decide


/-- Constant-state V10 candidate: consume the host fence and hand the same
barrier to the already-ranked V6 predecessor/front controller. -/
def hostFenceHandoffWriteV10
    (l r : R1AgentStateV6 psi kappa tau) :
    R1AgentStateV6 psi kappa tau × R1AgentStateV6 psi kappa tau :=
  (setControlV6 l .predecessorArmed false,
    setControlV6 r .front false)


/-- Exact n >= 3 strict-rank obligation, parameterized by any proposed rank. -/
def V9StrictRank3
    (R : R1ConfigV6 n psi kappa tau -> Nat)
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (ring : DirectedRing n) : Prop :=
  3 <= n ->
  forall C, SpliceSafeV7 hpsi ring C ->
    forall e : Fin n,
      (exists i, stepV9 hpsi hwidth hle ring C e i != C i) ->
      R (stepV9 hpsi hwidth hle ring C e) < R C


private theorem rankDropsAlong
    (R : R1ConfigV6 n psi kappa tau -> Nat)
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (ring : DirectedRing n)
    (hR : forall C, SpliceSafeV7 hpsi ring C -> forall e : Fin n,
      (exists i, stepV9 hpsi hwidth hle ring C e i != C i) ->
      R (stepV9 hpsi hwidth hle ring C e) < R C) :
    forall C es, LiveAlongV9 hpsi hwidth hle ring C es -> es != [] ->
      R (runV9Word hpsi hwidth hle ring C es) < R C := by
  intro C es
  induction es generalizing C with
  | nil =>
      intro _ hne
      exact ((bne_iff_ne.mp hne) rfl).elim
  | cons e es ih =>
      intro hlive _
      rcases hlive with ⟨hsafe, hchange, htail⟩
      have hfirst := hR C hsafe e hchange
      by_cases hz : es = []
      · subst es
        simpa [runV9Word] using hfirst
      · have hrest := ih
          (C := stepV9 hpsi hwidth hle ring C e) htail
          (bne_iff_ne.mpr hz)
        exact Nat.lt_trans hrest hfirst


theorem no_V9StrictRank3_on_ring3
    (R : R1ConfigV6 3 2 1 1 -> Nat) :
    ¬ V9StrictRank3 R hTwo hOne hOneTwo ring3 := by
  intro h
  have hlocal := h (show 3 <= 3 by decide)
  have hdrop := rankDropsAlong (R := R)
    hTwo hOne hOneTwo ring3 hlocal
    advanceFlatStart3 cycle3Word advanceFlat_cycle3.1 (by decide)
  have hcycle : runV9Word hTwo hOne hOneTwo ring3
      advanceFlatStart3 cycle3Word = advanceFlatStart3 :=
    funext advanceFlat_cycle3.2.2
  rw [hcycle] at hdrop
  exact Nat.lt_irrefl _ hdrop


/-- Weaker lifetime contract: among any n safe non-stuttering services,
either one service strictly drains V6 potential or the splice transaction
has reached the fully clear controller state at some prefix. -/
def V9WindowDrainOrEnd
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (ring : DirectedRing n) : Prop :=
  3 <= n -> forall C es, es.length = n ->
    LiveAlongV9 (kappa := kappa) (tau := tau)
      hpsi hwidth hle ring C es ->
    (exists pre e post,
      es = pre ++ e :: post /\
      controllerPotentialV6
        (stepV9 hpsi hwidth hle ring
          (runV9Word hpsi hwidth hle ring C pre) e) <
        controllerPotentialV6
          (runV9Word hpsi hwidth hle ring C pre)) \/
    (exists pre post,
      es = pre ++ post /\
      RolesClearV7 (runV9Word hpsi hwidth hle ring C pre))


private def advanceFlatTurn3 : R1ConfigV6 3 2 1 1 :=
  runV9Word hTwo hOne hOneTwo ring3 advanceFlatStart3 [0, 1, 2]


theorem advanceFlat3_first_turn_v6_flat :
    controllerPotentialV6 advanceFlatStart3 = 1 /\
    controllerPotentialV6
      (runV9Word hTwo hOne hOneTwo ring3 advanceFlatStart3 [0]) = 1 /\
    controllerPotentialV6
      (runV9Word hTwo hOne hOneTwo ring3 advanceFlatStart3 [0, 1]) = 1 /\
    controllerPotentialV6 advanceFlatTurn3 = 1 /\
    (advanceFlatTurn3 (0 : Fin 3)).acquireTicket = true := by
  decide


end B9SpliceV9RankRedesign


#print axioms B9SpliceV9RankRedesign.advanceFlat_cycle2
#print axioms B9SpliceV9RankRedesign.advanceFlat3_first_rank_equal
#print axioms B9SpliceV9RankRedesign.advanceFlat_cycle3
#print axioms B9SpliceV9RankRedesign.q11703_first_advance_local_drop
#print axioms B9SpliceV9RankRedesign.no_V9StrictRank3_on_ring3
#print axioms B9SpliceV9RankRedesign.advanceFlat3_first_turn_v6_flat
