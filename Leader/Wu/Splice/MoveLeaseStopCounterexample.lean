import Leader.Wu.Splice.MoveLeaseTable

set_option autoImplicit false
set_option Elab.async false
set_option pp.structureInstances false

namespace B9SpliceControllerV3Safety

open PPLL PPLLDomain PPLLResearchFormulation
  PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
  PPLLLeaderCreationCleanupRepair
open BirthSigMoveDisposalRepair
  BirthShortDoneTerminalBirthSources
open Q11593SpliceControllerDesign
open B9SpliceControllerR1Table
open B9SpliceControllerR1TableV2
open B9SpliceControllerR1TableV3

variable {n psi width kappa tau : Nat}

/-! ## 1. The V3 safety invariant

`safeAlongV3` checks `SpliceSafeR1V3` at every configuration on a concrete
word.  The first definition below merely gives that per-configuration
predicate a local name.  The next two definitions state the corresponding
arbitrary-word reachability invariant. -/

def V3SafetyInvariant
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (C : R1ConfigV3 n psi kappa tau) : Prop :=
  SpliceSafeR1V3 hpsi ring C


def V3Reachable
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (ring : DirectedRing n)
    (C0 C : R1ConfigV3 n psi kappa tau) : Prop :=
  exists word : List (Fin n),
    List.foldl
      (fun D e => stepV3 hpsi hwidth hle ring D e)
      C0 word = C


def V3ReachableSafety
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (ring : DirectedRing n)
    (C0 : R1ConfigV3 n psi kappa tau) : Prop :=
  forall C,
    V3Reachable hpsi hwidth hle ring C0 C ->
      V3SafetyInvariant hpsi ring C


/-! ## 2. DELETE is exactly the V2 transition -/

private theorem delete_row_v3_eq_v2
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (l r : R1AgentStateV3 psi kappa tau)
    (hguard : DeleteGuard hpsi hwidth hle l r) :
    rowV3 hpsi hwidth hle l r = rowV2 hpsi hwidth hle l r := by
  have hg := hguard
  rcases hg with ⟨hl, _hr, _hlp, _hrp, _hdelete⟩
  have hA : ¬ ArmAGuard hpsi hwidth hle l r := by
    intro ha
    have hn := ha.1
    rw [hl] at hn
    cases hn
  have hB : ¬ ArmBGuard l r := by
    intro hb
    have hn := hb.1
    rw [hl] at hn
    cases hn
  simp [rowV3, rowV2, hA, hB, hguard]


theorem stepV3_eq_stepV2_of_delete
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (ring : DirectedRing n) (C : R1ConfigV3 n psi kappa tau) (e : Fin n)
    (hguard : DeleteGuard hpsi hwidth hle
      (C e) (C (ring.rightNeighbor e))) :
    stepV3 hpsi hwidth hle ring C e =
      stepV2 hpsi hwidth hle ring C e := by
  funext i
  by_cases hself : ring.rightNeighbor e = e
  · simp [stepV3, stepV2, hself]
  · have hrow := delete_row_v3_eq_v2 hpsi hwidth hle
      (C e) (C (ring.rightNeighbor e)) hguard
    simp [stepV3, stepV2, hself, hrow]


/-- The certified V2 DELETE preservation theorem applies verbatim to a DELETE
executed by the V3 step function, because that executable step is equal to V2.
This theorem intentionally transports the V2 invariant; it does not assert a
global equivalence between `SpliceSafeR1V2` and `SpliceSafeR1V3`. -/
theorem delete_preserves_spliceSafeR1V2_for_stepV3
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (ring : DirectedRing n) (C : R1ConfigV3 n psi kappa tau) (e : Fin n)
    (hsafe : SpliceSafeR1V2 hpsi ring C)
    (hguard : DeleteGuard hpsi hwidth hle
      (C e) (C (ring.rightNeighbor e))) :
    SpliceSafeR1V2 hpsi ring
      (stepV3 hpsi hwidth hle ring C e) := by
  rw [stepV3_eq_stepV2_of_delete
    hpsi hwidth hle ring C e hguard]
  exact B9SpliceControllerR1TableV2.delete_preserves_spliceSafeR1V2
    hpsi hwidth hle ring C e hsafe hguard


/-! ## 3. MOVE-STOP counterexample

This is the first changed move rule, so the audit stops
here once the closed `decide` fixture refutes preservation.

The two physical followers have labels 0 and 1 modulo 3.  Thus 0 -> 1 is
aligned, while 1 -> 0 is a barrier.  Before STOP, the reverse barrier is
protected solely by the left `front,true`.  STOP clears both controls and
leaves the physical labels unchanged. -/

private theorem hOne : 0 < 1 := by decide
private theorem hOneThree : 1 <= 3 := by decide
private theorem hTwo : 0 < 2 := by decide
private theorem hThree : 0 < 3 := by decide

private def ring2 : DirectedRing 2 := ⟨hTwo⟩

/-- Minimal neutral physical follower at modulus 3. -/
private def raw3 (label : Fin 3) : AgentState 3 :=
  { leader := false
    probe := false
    phase := false
    bit := false
    wait := true
    state := .none
    path := .bot
    reset := false
    carry := false
    count := 0
    label := label
    h_field := false
    path2 := none
    path3 := none
    path4 := none
    path5 := none
    p := false
    p_carry := false
    reset_cmd := false
    echo := false
    signal_B := 0
    bullet := 0
    shield := true
    write_state := .none
    write := .none
    last := false
    last_set := false
    last_unset := false
    b_carry := false
    gen_ws := false
    ws_echo := false
    signal_ws := false }

private theorem raw3_domain (label : Fin 3) :
    (raw3 label).inProtocolDomain 0 := by
  simp [raw3, AgentState.inProtocolDomain]

private def cell3 (label : Fin 3) : ExpiringAgentState 3 0 0 :=
  ⟨⟨BoundedAgentState.ofDomain
      (raw3 label) (raw3_domain label), false⟩, 0⟩

private def x3
    (label : Fin 3) (r : SpliceRole) (pending : Bool) :
    R1AgentStateV3 3 0 0 :=
  { splice :=
      { base := cell3 label
        spliceRole := r }
    repairPending := pending }

/-- Clockwise on the two-ring:

0 = follower label 0, predecessorArmed,false
1 = follower label 1, front,true

The served edge 0 -> 1 is aligned.  The reverse edge 1 -> 0 is a barrier. -/
private def moveStopStart : R1ConfigV3 2 3 0 0 := fun i =>
  if i = 0 then x3 0 .predecessorArmed false
  else x3 1 .front true

private def moveStopAfter : R1ConfigV3 2 3 0 0 :=
  stepV3 hThree hOne hOneThree ring2 moveStopStart (0 : Fin 2)

/-! Closed finite deciders used only by the counterexample fixture. -/

private instance q11668DecidablePreparedDangerAtLocal
    {n psi kappa tau : Nat}
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (C : R1ConfigV3 n psi kappa tau) (e : Fin n) :
    Decidable (PreparedDangerAt hpsi ring C e) := by
  unfold PreparedDangerAt PreparedBarrierAt
  dsimp only
  unfold isBarrier
  infer_instance

private instance q11668DecidableR1ProtectedSpliceEdgeV3Local
    {n psi kappa tau : Nat}
    (ring : DirectedRing n) (C : R1ConfigV3 n psi kappa tau)
    (e : Fin n) :
    Decidable (R1ProtectedSpliceEdgeV3 ring C e) := by
  unfold R1ProtectedSpliceEdgeV3 ReservedFrontHoldGuard
  dsimp only
  infer_instance

private instance q11668DecidableSpliceSafeR1V3Local
    {n psi kappa tau : Nat}
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (C : R1ConfigV3 n psi kappa tau) :
    Decidable (SpliceSafeR1V3 hpsi ring C) := by
  unfold SpliceSafeR1V3
  infer_instance

private instance q11668DecidableMoveStopGuardV3Local
    {psi kappa tau : Nat}
    (hpsi : 0 < psi)
    (l r : R1AgentStateV3 psi kappa tau) :
    Decidable (MoveStopGuardV3 hpsi l r) := by
  unfold MoveStopGuardV3 ReservedFrontHoldGuard LocalPreparedBarrier
  dsimp only
  unfold isBarrier
  infer_instance

/-- Smallest non-self-edge V3 STOP failure.

The fixture checks all of the important facts at once:
* the start configuration satisfies V3 safety;
* the literal V3 STOP guard is enabled on 0 -> 1;
* the selected row is exactly STOP's two-control clear;
* after the step, reverse edge 1 -> 0 is still a prepared danger;
* that danger is no longer V3-protected;
* hence the post-state is not `SpliceSafeR1V3`. -/
theorem moveStop_v3_counterexample :
    SpliceSafeR1V3 hThree ring2 moveStopStart /\
    MoveStopGuardV3 hThree
      (moveStopStart (0 : Fin 2))
      (moveStopStart (ring2.rightNeighbor (0 : Fin 2))) /\
    rowV3 hThree hOne hOneThree
      (moveStopStart (0 : Fin 2))
      (moveStopStart (ring2.rightNeighbor (0 : Fin 2))) =
        (clearControl (moveStopStart (0 : Fin 2)),
          clearControl
            (moveStopStart (ring2.rightNeighbor (0 : Fin 2)))) /\
    PreparedDangerAt hThree ring2 moveStopAfter (1 : Fin 2) /\
    ¬ R1ProtectedSpliceEdgeV3 ring2 moveStopAfter (1 : Fin 2) /\
    ¬ SpliceSafeR1V3 hThree ring2 moveStopAfter := by
  decide

end B9SpliceControllerV3Safety

#print axioms B9SpliceControllerV3Safety.stepV3_eq_stepV2_of_delete
#print axioms B9SpliceControllerV3Safety.delete_preserves_spliceSafeR1V2_for_stepV3
#print axioms B9SpliceControllerV3Safety.moveStop_v3_counterexample
