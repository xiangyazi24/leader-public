import Leader.Wu.Splice.FollowerStopTable

set_option autoImplicit false
set_option Elab.async false
set_option pp.structureInstances false

namespace B9SpliceControllerV4Safety

open PPLL PPLLDomain PPLLResearchFormulation
  PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
  PPLLLeaderCreationCleanupRepair
open BirthSigMoveDisposalRepair
  BirthShortDoneTerminalBirthSources
open Q11593SpliceControllerDesign
open B9SpliceControllerR1Table
open B9SpliceControllerR1TableV2
open B9SpliceControllerR1TableV3
open B9SpliceControllerV3Safety
open B9SpliceControllerR1TableV4

variable {n psi width kappa tau : Nat}

/-! ## Closed decidability support -/

private instance instDecidableArmAGuard
    {psi width kappa tau : Nat}
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (l r : R1AgentStateV4 psi kappa tau) :
    Decidable (ArmAGuard hpsi hwidth hle l r) := by
  unfold ArmAGuard LeftDeletionCandidate
  infer_instance

private instance instDecidableArmBGuard
    {psi kappa tau : Nat}
    (l r : R1AgentStateV4 psi kappa tau) :
    Decidable (ArmBGuard l r) := by
  unfold ArmBGuard
  infer_instance

private instance instDecidableDeleteGuard
    {psi width kappa tau : Nat}
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (l r : R1AgentStateV4 psi kappa tau) :
    Decidable (DeleteGuard hpsi hwidth hle l r) := by
  unfold DeleteGuard LeftDeletionCandidate
  infer_instance

private instance instDecidablePendingHoldGuard
    {psi width kappa tau : Nat}
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (l r : R1AgentStateV4 psi kappa tau) :
    Decidable (PendingHoldGuard hpsi hwidth hle l r) := by
  unfold PendingHoldGuard LeftDeletionCandidate
  infer_instance

private instance instDecidablePendingAbortGuard
    {psi width kappa tau : Nat}
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (l r : R1AgentStateV4 psi kappa tau) :
    Decidable (PendingAbortGuard hpsi hwidth hle l r) := by
  unfold PendingAbortGuard LeftDeletionCandidate
  infer_instance

private instance instDecidableMoveCommitGuard
    {psi kappa tau : Nat}
    (l r : R1AgentStateV4 psi kappa tau) :
    Decidable (MoveCommitGuard l r) := by
  unfold MoveCommitGuard
  infer_instance

private instance instDecidableMoveStopGuardV3
    {psi kappa tau : Nat}
    (hpsi : 0 < psi)
    (l r : R1AgentStateV4 psi kappa tau) :
    Decidable (MoveStopGuardV3 hpsi l r) := by
  unfold MoveStopGuardV3 ReservedFrontHoldGuard LocalPreparedBarrier
  dsimp only
  unfold isBarrier
  infer_instance

private instance instDecidableMoveSeekGuardV3
    {psi kappa tau : Nat}
    (hpsi : 0 < psi)
    (l r : R1AgentStateV4 psi kappa tau) :
    Decidable (MoveSeekGuardV3 hpsi l r) := by
  unfold MoveSeekGuardV3 ReservedFrontHoldGuard LocalPreparedBarrier
  dsimp only
  unfold isBarrier
  infer_instance

private instance instDecidablePreparedDangerAt
    {n psi kappa tau : Nat}
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (C : R1ConfigV4 n psi kappa tau) (e : Fin n) :
    Decidable (PreparedDangerAt hpsi ring C e) := by
  unfold PreparedDangerAt PreparedBarrierAt
  dsimp only
  unfold isBarrier
  infer_instance

private instance instDecidableProtectedV3
    {n psi kappa tau : Nat}
    (ring : DirectedRing n) (C : R1ConfigV4 n psi kappa tau)
    (e : Fin n) :
    Decidable (R1ProtectedSpliceEdgeV3 ring C e) := by
  unfold R1ProtectedSpliceEdgeV3 ReservedFrontHoldGuard
  dsimp only
  infer_instance

private instance instDecidableSafeV3
    {n psi kappa tau : Nat}
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (C : R1ConfigV4 n psi kappa tau) :
    Decidable (SpliceSafeR1V3 hpsi ring C) := by
  unfold SpliceSafeR1V3
  infer_instance

private instance instDecidablePPrimeBarrierBirthGuard
    {psi : Nat} (hpsi : 0 < psi)
    (l r : AuthorizedAgentState psi) :
    Decidable (PPrimeBarrierBirthGuard hpsi l r) := by
  unfold PPrimeBarrierBirthGuard isBarrier
  infer_instance

private instance instDecidableAmendedPPrimeV3
    {n psi kappa tau : Nat}
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (C : R1ConfigV4 n psi kappa tau) (e : Fin n) :
    Decidable (R1AmendedPPrimeAtV3 hpsi ring C e) := by
  unfold R1AmendedPPrimeAtV3
  dsimp only
  infer_instance

private instance instDecidableSourceFreeV3
    {n psi kappa tau : Nat}
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (C : R1ConfigV4 n psi kappa tau) :
    Decidable (R1SourceFreeV3 hpsi ring C) := by
  unfold R1SourceFreeV3
  infer_instance

private instance instDecidableLeaderlessV3
    {n : Nat} (C : R1ConfigV4 n 2 0 0) :
    Decidable (LeaderlessV3 C) := by
  unfold LeaderlessV3
  infer_instance

private instance instDecidableRolesClearV3
    {n : Nat} (C : R1ConfigV4 n 2 0 0) :
    Decidable (RolesClearV3 C) := by
  unfold RolesClearV3
  infer_instance

/-! ## Literal V4 MOVE-SEEK selection -/

/-- Exactly the branch conditions saying that V4 falls through STOP and all
V3 predecessors of MOVE-SEEK, then selects MOVE-SEEK. -/
def MoveSeekSelectedV4
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (l r : R1AgentStateV4 psi kappa tau) : Prop :=
  ¬ ArmAGuard hpsi hwidth hle l r /\
  ¬ ArmBGuard l r /\
  ¬ DeleteGuard hpsi hwidth hle l r /\
  ¬ PendingHoldGuard hpsi hwidth hle l r /\
  ¬ PendingAbortGuard hpsi hwidth hle l r /\
  ¬ MoveCommitGuard l r /\
  ¬ MoveStopGuardV3 hpsi l r /\
  MoveSeekGuardV3 hpsi l r

private instance instDecidableMoveSeekSelectedV4
    {psi width kappa tau : Nat}
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (l r : R1AgentStateV4 psi kappa tau) :
    Decidable (MoveSeekSelectedV4 hpsi hwidth hle l r) := by
  unfold MoveSeekSelectedV4
  infer_instance

/-! ## First failure: MOVE-SEEK -/

private theorem hOne : 0 < 1 := by decide
private theorem hTwo : 0 < 2 := by decide
private theorem hThree : 0 < 3 := by decide
private theorem hFour : 0 < 4 := by decide
private theorem hFive : 0 < 5 := by decide
private theorem hOneTwo : 1 <= 2 := by decide
private theorem hOneThree : 1 <= 3 := by decide
private theorem hTwoLe : 2 <= 2 := by decide
private theorem hTwoThree : 2 <= 3 := by decide

private def ring2 : DirectedRing 2 := ⟨hTwo⟩
private def ring3 : DirectedRing 3 := ⟨hThree⟩
private def ring4 : DirectedRing 4 := ⟨hFour⟩
private def ring5 : DirectedRing 5 := ⟨hFive⟩

/-- Smallest MOVE-SEEK obstruction.  Both directed physical edges are barriers:
`0 -> 0` modulo two expects responder label one. -/
def seekStart2 : R1ConfigV4 2 2 0 0 := fun i =>
  if i = 0 then
    B9SpliceR2AttackRerun.xcell
      false 0 false .predecessorArmed false
  else
    B9SpliceR2AttackRerun.xcell
      false 0 false .front true

def seekAfter2V4 : R1ConfigV4 2 2 0 0 :=
  stepV4 hTwo hOne hOneTwo ring2 seekStart2 (0 : Fin 2)

/-- V4 reaches the unchanged V3 SEEK write, and that write exposes the reverse
barrier by consuming its only `front,true` certificate. -/
theorem moveSeek_v4_counterexample :
    SpliceSafeR1V3 hTwo ring2 seekStart2 /\
    MoveSeekSelectedV4 hTwo hOne hOneTwo
      (seekStart2 (0 : Fin 2)) (seekStart2 (1 : Fin 2)) /\
    rowV4 hTwo hOne hOneTwo
      (seekStart2 (0 : Fin 2)) (seekStart2 (1 : Fin 2)) =
      (seekStart2 (0 : Fin 2),
        setControl (seekStart2 (1 : Fin 2)) .victimArmed true) /\
    PreparedDangerAt hTwo ring2 seekAfter2V4 (1 : Fin 2) /\
    ¬ R1ProtectedSpliceEdgeV3 ring2 seekAfter2V4 (1 : Fin 2) /\
    ¬ SpliceSafeR1V3 hTwo ring2 seekAfter2V4 := by
  decide

/-! ## Smallest factor-8 rule-only repair: SEEK becomes HOLD -/

/-- This wrapper changes exactly a selected MOVE-SEEK row.  Every other V4 row,
including the repaired STOP, is byte-for-byte delegated to `rowV4`. -/
def rowV4SeekHold
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (l r : R1AgentStateV4 psi kappa tau) :
    R1AgentStateV4 psi kappa tau × R1AgentStateV4 psi kappa tau :=
  if MoveSeekSelectedV4 hpsi hwidth hle l r then (l, r)
  else rowV4 hpsi hwidth hle l r

def stepV4SeekHold
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (ring : DirectedRing n) (C : R1ConfigV4 n psi kappa tau)
    (e : Fin n) : R1ConfigV4 n psi kappa tau :=
  let j := ring.rightNeighbor e
  if j = e then C
  else
    let q := rowV4SeekHold hpsi hwidth hle (C e) (C j)
    fun i =>
      if i = e then q.1
      else if i = j then q.2
      else C i

/-- No state is added: the rule-only repair still has the existing factor 8. -/
def controllerStateFactorV4SeekHold : Nat := controllerStateFactorV4

theorem controllerStateFactorV4SeekHold_eq :
    controllerStateFactorV4SeekHold = 8 := by
  decide

private theorem moveSeekSelected_ne
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (ring : DirectedRing n) (C : R1ConfigV4 n psi kappa tau) (e : Fin n)
    (hsel : MoveSeekSelectedV4 hpsi hwidth hle
      (C e) (C (ring.rightNeighbor e))) :
    ring.rightNeighbor e ≠ e := by
  rcases hsel with ⟨_, _, _, _, _, _, _, hg⟩
  rcases hg with ⟨hlRole, _hlPending, hreserved, _hbarrier⟩
  unfold ReservedFrontHoldGuard at hreserved
  rcases hreserved with ⟨hrRole, _hrPending⟩
  intro hs
  rw [hs] at hrRole
  have hbad :
      SpliceRole.predecessorArmed = SpliceRole.front :=
    hlRole.symm.trans hrRole
  cases hbad

/-- On a selected SEEK the repaired rule is literally a configuration stutter. -/
theorem stepV4SeekHold_eq_self_of_moveSeek
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (ring : DirectedRing n) (C : R1ConfigV4 n psi kappa tau) (e : Fin n)
    (hsel : MoveSeekSelectedV4 hpsi hwidth hle
      (C e) (C (ring.rightNeighbor e))) :
    stepV4SeekHold hpsi hwidth hle ring C e = C := by
  have hne := moveSeekSelected_ne hpsi hwidth hle ring C e hsel
  funext i
  by_cases hi : i = e
  · subst i
    simp [stepV4SeekHold, hne, rowV4SeekHold, hsel]
  · by_cases hj : i = ring.rightNeighbor e
    · subst i
      simp [stepV4SeekHold, hne, rowV4SeekHold, hsel]
    · simp [stepV4SeekHold, hne, rowV4SeekHold, hsel, hi, hj]

/-- The smallest rule-only repair restores generic V3 safety for MOVE-SEEK by
identity. -/
theorem moveSeekHold_preserves_spliceSafeR1V3
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (ring : DirectedRing n) (C : R1ConfigV4 n psi kappa tau) (e : Fin n)
    (hsafe : SpliceSafeR1V3 hpsi ring C)
    (hsel : MoveSeekSelectedV4 hpsi hwidth hle
      (C e) (C (ring.rightNeighbor e))) :
    SpliceSafeR1V3 hpsi ring
      (stepV4SeekHold hpsi hwidth hle ring C e) := by
  rw [stepV4SeekHold_eq_self_of_moveSeek
    hpsi hwidth hle ring C e hsel]
  exact hsafe

private def seekAfter2Hold : R1ConfigV4 2 2 0 0 :=
  stepV4SeekHold hTwo hOne hOneTwo ring2 seekStart2 (0 : Fin 2)

theorem moveSeek_counterexample_repaired_by_hold :
    (forall i, seekAfter2Hold i = seekStart2 i) /\
    SpliceSafeR1V3 hTwo ring2 seekAfter2Hold := by
  decide

/-! ## Replay helpers for the changed table -/

def serveSeekHold {n : Nat}
    (ring : DirectedRing n)
    (C : R1ConfigV4 n 2 0 0) (e : Fin n) :
    R1ConfigV4 n 2 0 0 :=
  stepV4SeekHold hTwo hTwo hTwoLe ring C e

def runSeekHold {n : Nat}
    (ring : DirectedRing n)
    (C : R1ConfigV4 n 2 0 0)
    (word : List (Fin n)) : R1ConfigV4 n 2 0 0 :=
  List.foldl (fun D e => serveSeekHold ring D e) C word

def safeAlongSeekHold {n : Nat} (ring : DirectedRing n) :
    R1ConfigV4 n 2 0 0 -> List (Fin n) -> Bool
  | C, [] => decide (SpliceSafeR1V3 hTwo ring C)
  | C, e :: es =>
      decide (SpliceSafeR1V3 hTwo ring C) &&
        safeAlongSeekHold ring (serveSeekHold ring C e) es

def sourceFreeAlongSeekHold {n : Nat} (ring : DirectedRing n) :
    R1ConfigV4 n 2 0 0 -> List (Fin n) -> Bool
  | C, [] => decide (R1SourceFreeV3 hTwo ring C)
  | C, e :: es =>
      decide (R1SourceFreeV3 hTwo ring C) &&
        sourceFreeAlongSeekHold ring (serveSeekHold ring C e) es

/-! ## STOP fixture rechecks -/

private def raw3
    (leader : Bool) (label : Fin 3) : AgentState 3 :=
  { leader := leader
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

private theorem raw3_domain0 (leader : Bool) (label : Fin 3) :
    (raw3 leader label).inProtocolDomain 0 := by
  simp [raw3, AgentState.inProtocolDomain]

private theorem raw3_domain3 (leader : Bool) (label : Fin 3) :
    (raw3 leader label).inProtocolDomain 3 := by
  simp [raw3, AgentState.inProtocolDomain]

private def cell3_0
    (leader : Bool) (label : Fin 3) : ExpiringAgentState 3 0 0 :=
  ⟨⟨BoundedAgentState.ofDomain
      (raw3 leader label) (raw3_domain0 leader label), false⟩, 0⟩

private def x3_0
    (leader : Bool) (label : Fin 3)
    (r : SpliceRole) (pending : Bool) : R1AgentStateV4 3 0 0 :=
  { splice := { base := cell3_0 leader label, spliceRole := r }
    repairPending := pending }

private def stopStart2 : R1ConfigV4 2 3 0 0 := fun i =>
  if i = 0 then x3_0 false 0 .predecessorArmed false
  else x3_0 false 1 .front true

private def stopAfter2Hold : R1ConfigV4 2 3 0 0 :=
  stepV4SeekHold hThree hOne hOneThree ring2 stopStart2 (0 : Fin 2)

private def cell3_3_48
    (leader : Bool) (label : Fin 3) : ExpiringAgentState 3 3 48 :=
  ⟨⟨BoundedAgentState.ofDomain
      (raw3 leader label) (raw3_domain3 leader label), false⟩, 0⟩

private def x3_3_48
    (leader : Bool) (label : Fin 3)
    (r : SpliceRole) (pending : Bool) : R1AgentStateV4 3 3 48 :=
  { splice := { base := cell3_3_48 leader label, spliceRole := r }
    repairPending := pending }

private def protocolStopStart4 : R1ConfigV4 4 3 3 48 := fun i =>
  if i = 0 then x3_3_48 false 0 .predecessorArmed false
  else if i = 1 then x3_3_48 false 1 .front true
  else if i = 2 then x3_3_48 false 1 .none false
  else x3_3_48 true 0 .none false

private def protocolStopAfter4Hold : R1ConfigV4 4 3 3 48 :=
  stepV4SeekHold hThree hTwo hTwoThree ring4
    protocolStopStart4 (0 : Fin 4)

/-- Both V4 STOP repairs are unchanged by the SEEK-only edit. -/
theorem v4_stop_fixtures_rechecked :
    SpliceSafeR1V3 hThree ring2 stopStart2 /\
    MoveStopGuardV3 hThree (stopStart2 0) (stopStart2 1) /\
    ReservedFrontHoldGuard (stopAfter2Hold 1) /\
    SpliceSafeR1V3 hThree ring2 stopAfter2Hold /\
    Q11497FeasibilityAudit.psiChoice 4 = 3 /\
    Q11497FeasibilityAudit.widthChoice = 2 /\
    Q11497FeasibilityAudit.kappaChoice 4 = 3 /\
    Q11497FeasibilityAudit.tauChoice 4 = 48 /\
    SpliceSafeR1V3 hThree ring4 protocolStopStart4 /\
    SpliceSafeR1V3 hThree ring4 protocolStopAfter4Hold /\
    ReservedFrontHoldGuard (protocolStopAfter4Hold 1) /\
    PreparedDangerAt hThree ring4 protocolStopAfter4Hold 1 /\
    R1ProtectedSpliceEdgeV3 ring4 protocolStopAfter4Hold 1 := by
  decide

/-! ## Existing V4 replay fixtures -/

private def q11592ArmedHold : R1ConfigV4 4 2 0 0 :=
  serveSeekHold ring4 B9SpliceR2AttackRerun.q11592Start4 1

private def q11592ReplayHold : R1ConfigV4 4 2 0 0 :=
  serveSeekHold ring4 q11592ArmedHold 1

private def followerOldFirstHold : R1ConfigV4 5 2 0 0 :=
  serveSeekHold ring5 B9SpliceR2AttackRerun.followerStart5 0

private def stagedArmedHold : R1ConfigV4 3 2 0 0 :=
  serveSeekHold ring3 B9SpliceR2AttackRerun.stagedStart3 1

private def stagedFinalHold : R1ConfigV4 3 2 0 0 :=
  runSeekHold ring3 B9SpliceR2AttackRerun.stagedStart3
    B9SpliceR2AttackRerun.starvationWord3

set_option maxRecDepth 65536 in
/-- The three leaderless drains, same-edge replay, old unreserved follower mark,
and staged-deletion replay are byte-for-byte unchanged.  Each equality is a
closed `decide` check against the current V4 fixture output. -/
theorem unchanged_v4_fixtures_rechecked :
    (forall i,
      runSeekHold ring3 B9SpliceR2AttackRerun.loop3Start
          B9SpliceControllerR1TableV4.loop3DrainPrefixV4 i =
        B9SpliceControllerR1TableV4.runV4 ring3
          B9SpliceR2AttackRerun.loop3Start
          B9SpliceControllerR1TableV4.loop3DrainPrefixV4 i) /\
    (forall i,
      runSeekHold ring4 B9SpliceR2AttackRerun.loop4Start
          B9SpliceControllerR1TableV4.loop4DrainWordV4 i =
        B9SpliceControllerR1TableV4.runV4 ring4
          B9SpliceR2AttackRerun.loop4Start
          B9SpliceControllerR1TableV4.loop4DrainWordV4 i) /\
    (forall i,
      runSeekHold ring5 B9SpliceR2AttackRerun.loop5Start
          B9SpliceControllerR1TableV4.loop5DrainPrefixV4 i =
        B9SpliceControllerR1TableV4.runV4 ring5
          B9SpliceR2AttackRerun.loop5Start
          B9SpliceControllerR1TableV4.loop5DrainPrefixV4 i) /\
    (forall i,
      q11592ArmedHold i =
        B9SpliceControllerR1TableV4.q11592Armed4V4 i) /\
    (forall i,
      q11592ReplayHold i =
        B9SpliceControllerR1TableV4.q11592Replay4V4 i) /\
    (forall i,
      followerOldFirstHold i =
        B9SpliceControllerR1TableV4.followerOldFirstV4 i) /\
    (forall i,
      stagedArmedHold i =
        B9SpliceControllerR1TableV4.stagedArmed3V4 i) /\
    (forall i,
      stagedFinalHold i =
        B9SpliceControllerR1TableV4.starvationFinal3V4 i) := by
  decide

/-! ## The one replay regression: authenticated SEEK chain -/

private def followerAfterHold : R1ConfigV4 5 2 0 0 :=
  runSeekHold ring5
    B9SpliceControllerR1TableV3.followerStart5V3
    B9SpliceControllerR1TableV3.followerWord5V3

/-- The hold repair keeps safety/source-freedom on this particular word, but it
necessarily destroys the old SEEK -> ACQUIRE -> COMMIT progress receipt.  The
subsequent incoming orphan scrubs clear sites 2 and 3 instead. -/
theorem follower_authenticated_v4_fixture_regresses :
    safeAlongSeekHold ring5
      B9SpliceControllerR1TableV3.followerStart5V3
      B9SpliceControllerR1TableV3.followerWord5V3 = true /\
    sourceFreeAlongSeekHold ring5
      B9SpliceControllerR1TableV3.followerStart5V3
      B9SpliceControllerR1TableV3.followerWord5V3 = true /\
    role (followerAfterHold 0) = .predecessorArmed /\
    (followerAfterHold 0).repairPending = false /\
    role (followerAfterHold 1) = .front /\
    (followerAfterHold 1).repairPending = true /\
    role (followerAfterHold 2) = .none /\
    (followerAfterHold 2).repairPending = false /\
    role (followerAfterHold 3) = .none /\
    (followerAfterHold 3).repairPending = false /\
    (followerAfterHold 2).splice.base.core.core.probe = true /\
    ¬ (role (followerAfterHold 2) = .predecessorArmed /\
       (followerAfterHold 2).repairPending = false /\
       role (followerAfterHold 3) = .front /\
       (followerAfterHold 3).repairPending = true /\
       (followerAfterHold 2).splice.base.core.core.probe = false) := by
  decide

end B9SpliceControllerV4Safety

#print axioms B9SpliceControllerV4Safety.moveSeek_v4_counterexample
#print axioms B9SpliceControllerV4Safety.controllerStateFactorV4SeekHold_eq
#print axioms B9SpliceControllerV4Safety.stepV4SeekHold_eq_self_of_moveSeek
#print axioms B9SpliceControllerV4Safety.moveSeekHold_preserves_spliceSafeR1V3
#print axioms B9SpliceControllerV4Safety.moveSeek_counterexample_repaired_by_hold
#print axioms B9SpliceControllerV4Safety.v4_stop_fixtures_rechecked
#print axioms B9SpliceControllerV4Safety.unchanged_v4_fixtures_rechecked
#print axioms B9SpliceControllerV4Safety.follower_authenticated_v4_fixture_regresses
