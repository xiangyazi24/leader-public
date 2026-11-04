import Leader.Wu.Splice.FollowerStopSeekHold

set_option autoImplicit false
set_option Elab.async false
set_option pp.structureInstances false

namespace B9SpliceControllerR1TableV5

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
open B9SpliceControllerV4Safety

variable {n psi width kappa tau : Nat}

abbrev R1AgentStateV5 (psi kappa tau : Nat) :=
  R1AgentStateV4 psi kappa tau

abbrev R1ConfigV5 (n psi kappa tau : Nat) :=
  R1ConfigV4 n psi kappa tau

private instance q11689DecidableMoveSeekGuardV3
    {psi kappa tau : Nat}
    (hpsi : 0 < psi)
    (l r : R1AgentStateV5 psi kappa tau) :
    Decidable (MoveSeekGuardV3 hpsi l r) := by
  unfold MoveSeekGuardV3 ReservedFrontHoldGuard LocalPreparedBarrier
  dsimp only
  unfold isBarrier
  infer_instance

/-- Suggested v5 ACQUIRE: the current front and its right reservation are both
retained `front,true` until an aligned front/front service consumes the left
front into the pending-predecessor state.  This uses no extra state. -/
def MoveAcquireFrontGuardV5
    (hpsi : 0 < psi)
    (l r : R1AgentStateV5 psi kappa tau) : Prop :=
  ReservedFrontHoldGuard l /\
  l.splice.base.core.core.leader = false /\
  ReservedFrontHoldGuard r /\
  r.splice.base.core.core.leader = false /\
  ¬ LocalPreparedBarrier hpsi l r

private instance q11689DecidableMoveAcquireFrontGuardV5
    {psi kappa tau : Nat}
    (hpsi : 0 < psi)
    (l r : R1AgentStateV5 psi kappa tau) :
    Decidable (MoveAcquireFrontGuardV5 hpsi l r) := by
  unfold MoveAcquireFrontGuardV5 ReservedFrontHoldGuard LocalPreparedBarrier
  dsimp only
  unfold isBarrier
  infer_instance

/-- v5 changes only SEEK and the new aligned-front ACQUIRE.

ACQUIRE has priority over the inherited orphan-reserved-front scrub.  SEEK is
an exact hold.  Every other branch is literally v4. -/
def rowV5
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (l r : R1AgentStateV5 psi kappa tau) :
    R1AgentStateV5 psi kappa tau × R1AgentStateV5 psi kappa tau :=
  if MoveAcquireFrontGuardV5 hpsi l r then
    (setControl l .predecessorArmed true, r)
  else if MoveSeekGuardV3 hpsi l r then
    (l, r)
  else
    rowV4 hpsi hwidth hle l r

/-- Ring lift, preserving v4's fail-closed singleton convention. -/
def stepV5
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (ring : DirectedRing n) (C : R1ConfigV5 n psi kappa tau)
    (e : Fin n) : R1ConfigV5 n psi kappa tau :=
  let j := ring.rightNeighbor e
  if j = e then C
  else
    let q := rowV5 hpsi hwidth hle (C e) (C j)
    fun i =>
      if i = e then q.1
      else if i = j then q.2
      else C i

/-- No field is added by the diagnostic v5 candidate. -/
def controllerStateFactorV5 : Nat := controllerStateFactorV4

theorem controllerStateFactorV5_eq : controllerStateFactorV5 = 8 := by
  simpa [controllerStateFactorV5] using controllerStateFactorV4_eq

private theorem frontAcquire_not_of_moveSeek
    (hpsi : 0 < psi)
    (l r : R1AgentStateV5 psi kappa tau)
    (hseek : MoveSeekGuardV3 hpsi l r) :
    ¬ MoveAcquireFrontGuardV5 hpsi l r := by
  intro hacq
  have hpred : role l = .predecessorArmed := hseek.1
  have hfront : role l = .front := by
    exact hacq.1.1
  rw [hpred] at hfront
  cases hfront

/-- The repair: SEEK itself consumes no certificate. -/
theorem moveSeek_rowV5_stutters
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (l r : R1AgentStateV5 psi kappa tau)
    (hseek : MoveSeekGuardV3 hpsi l r) :
    rowV5 hpsi hwidth hle l r = (l, r) := by
  have hna := frontAcquire_not_of_moveSeek hpsi l r hseek
  simp [rowV5, hna, hseek]

/-- Exact local write selected by the new aligned front/front acquisition. -/
theorem moveAcquireFront_rowV5
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (l r : R1AgentStateV5 psi kappa tau)
    (hacq : MoveAcquireFrontGuardV5 hpsi l r) :
    rowV5 hpsi hwidth hle l r =
      (setControl l .predecessorArmed true, r) := by
  simp [rowV5, hacq]

/-! ## Closed decidability used by the finite census -/

private instance q11689DecidablePreparedDangerAt
    {n psi kappa tau : Nat}
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (C : R1ConfigV5 n psi kappa tau) (e : Fin n) :
    Decidable (PreparedDangerAt hpsi ring C e) := by
  unfold PreparedDangerAt PreparedBarrierAt
  dsimp only
  unfold isBarrier
  infer_instance

private instance q11689DecidableR1ProtectedSpliceEdgeV3
    {n psi kappa tau : Nat}
    (ring : DirectedRing n) (C : R1ConfigV5 n psi kappa tau)
    (e : Fin n) :
    Decidable (R1ProtectedSpliceEdgeV3 ring C e) := by
  unfold R1ProtectedSpliceEdgeV3 ReservedFrontHoldGuard
  dsimp only
  infer_instance

private instance q11689DecidableSpliceSafeR1V3
    {n psi kappa tau : Nat}
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (C : R1ConfigV5 n psi kappa tau) :
    Decidable (SpliceSafeR1V3 hpsi ring C) := by
  unfold SpliceSafeR1V3
  infer_instance

private instance q11689DecidablePPrimeBarrierBirthGuard
    {psi : Nat} (hpsi : 0 < psi)
    (l r : AuthorizedAgentState psi) :
    Decidable (PPrimeBarrierBirthGuard hpsi l r) := by
  unfold PPrimeBarrierBirthGuard isBarrier
  infer_instance

private instance q11689DecidableR1AmendedPPrimeAtV3
    {n psi kappa tau : Nat}
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (C : R1ConfigV5 n psi kappa tau) (e : Fin n) :
    Decidable (R1AmendedPPrimeAtV3 hpsi ring C e) := by
  unfold R1AmendedPPrimeAtV3
  dsimp only
  infer_instance

private instance q11689DecidableR1SourceFreeV3
    {n psi kappa tau : Nat}
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (C : R1ConfigV5 n psi kappa tau) :
    Decidable (R1SourceFreeV3 hpsi ring C) := by
  unfold R1SourceFreeV3
  infer_instance

private instance q11689DecidableLeaderlessV3
    {n : Nat} (C : R1ConfigV5 n 2 0 0) :
    Decidable (LeaderlessV3 C) := by
  unfold LeaderlessV3
  infer_instance

private instance q11689DecidableRolesClearV3
    {n : Nat} (C : R1ConfigV5 n 2 0 0) :
    Decidable (RolesClearV3 C) := by
  unfold RolesClearV3
  infer_instance

/-! ## Closed finite helpers -/

private theorem hOne : 0 < 1 := by decide
private theorem hTwo : 0 < 2 := by decide
private theorem hThree : 0 < 3 := by decide
private theorem hFour : 0 < 4 := by decide
private theorem hFive : 0 < 5 := by decide
private theorem hOneTwo : 1 <= 2 := by decide
private theorem hOneThree : 1 <= 3 := by decide
private theorem hTwoLe : 2 <= 2 := by decide

private def ring2 : DirectedRing 2 := ⟨hTwo⟩
private def ring3 : DirectedRing 3 := ⟨hThree⟩
private def ring4 : DirectedRing 4 := ⟨hFour⟩
private def ring5 : DirectedRing 5 := ⟨hFive⟩

def serveV5 {n : Nat}
    (ring : DirectedRing n)
    (C : R1ConfigV5 n 2 0 0) (e : Fin n) :
    R1ConfigV5 n 2 0 0 :=
  stepV5 hTwo hTwo hTwoLe ring C e

def runV5 {n : Nat}
    (ring : DirectedRing n)
    (C : R1ConfigV5 n 2 0 0)
    (word : List (Fin n)) : R1ConfigV5 n 2 0 0 :=
  List.foldl (fun D e => serveV5 ring D e) C word

def safeAlongV5 {n : Nat} (ring : DirectedRing n) :
    R1ConfigV5 n 2 0 0 -> List (Fin n) -> Bool
  | C, [] => decide (SpliceSafeR1V3 hTwo ring C)
  | C, e :: es =>
      decide (SpliceSafeR1V3 hTwo ring C) &&
        safeAlongV5 ring (serveV5 ring C e) es

def sourceFreeAlongV5 {n : Nat} (ring : DirectedRing n) :
    R1ConfigV5 n 2 0 0 -> List (Fin n) -> Bool
  | C, [] => decide (R1SourceFreeV3 hTwo ring C)
  | C, e :: es =>
      decide (R1SourceFreeV3 hTwo ring C) &&
        sourceFreeAlongV5 ring (serveV5 ring C e) es

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

private def cell3
    (leader : Bool) (label : Fin 3) : ExpiringAgentState 3 0 0 :=
  ⟨⟨BoundedAgentState.ofDomain
      (raw3 leader label) (raw3_domain0 leader label), false⟩, 0⟩

private def x3
    (leader : Bool) (label : Fin 3)
    (r : SpliceRole) (pending : Bool) : R1AgentStateV5 3 0 0 :=
  { splice := { base := cell3 leader label, spliceRole := r }
    repairPending := pending }

/-! ## MOVE-STOP and SEEK witnesses -/

private def q11668Start2V5 : R1ConfigV5 2 3 0 0 := fun i =>
  if i = 0 then x3 false 0 .predecessorArmed false
  else x3 false 1 .front true

private def q11668After2V5 : R1ConfigV5 2 3 0 0 :=
  stepV5 hThree hOne hOneThree ring2 q11668Start2V5 (0 : Fin 2)

theorem q11668_moveStop_rechecked_v5 :
    SpliceSafeR1V3 hThree ring2 q11668Start2V5 /\
    MoveStopGuardV3 hThree
      (q11668Start2V5 (0 : Fin 2))
      (q11668Start2V5 (1 : Fin 2)) /\
    role (q11668After2V5 (0 : Fin 2)) = .none /\
    ReservedFrontHoldGuard (q11668After2V5 (1 : Fin 2)) /\
    SpliceSafeR1V3 hThree ring2 q11668After2V5 := by
  decide

private def q11681After2V5 : R1ConfigV5 2 2 0 0 :=
  stepV5 hTwo hOne hOneTwo ring2
    B9SpliceControllerV4Safety.seekStart2 (0 : Fin 2)

theorem q11681_moveSeek_rechecked_v5 :
    SpliceSafeR1V3 hTwo ring2 B9SpliceControllerV4Safety.seekStart2 /\
    MoveSeekGuardV3 hTwo
      (B9SpliceControllerV4Safety.seekStart2 (0 : Fin 2))
      (B9SpliceControllerV4Safety.seekStart2 (1 : Fin 2)) /\
    (forall i, q11681After2V5 i =
      B9SpliceControllerV4Safety.seekStart2 i) /\
    SpliceSafeR1V3 hTwo ring2 q11681After2V5 := by
  decide

/-! ## Four safety counterexamples from the complete rule census -/

/-- The served pair is an aligned `front,true -> front,true`, but site 1 is
also the required backing front of the pending predecessor at site 0. -/
def frontAcquireBackedStart3 : R1ConfigV5 3 2 0 0 := fun i =>
  if i = 0 then
    B9SpliceR2AttackRerun.xcell true 0 false .predecessorArmed true
  else if i = 1 then
    B9SpliceR2AttackRerun.xcell false 0 false .front true
  else
    B9SpliceR2AttackRerun.xcell false 1 false .front true

def frontAcquireBackedAfter3 : R1ConfigV5 3 2 0 0 :=
  serveV5 ring3 frontAcquireBackedStart3 (1 : Fin 3)

theorem frontAcquire_breaks_spliceSafeR1V3 :
    SpliceSafeR1V3 hTwo ring3 frontAcquireBackedStart3 /\
    MoveAcquireFrontGuardV5 hTwo
      (frontAcquireBackedStart3 (1 : Fin 3))
      (frontAcquireBackedStart3 (2 : Fin 3)) /\
    role (frontAcquireBackedAfter3 (1 : Fin 3)) = .predecessorArmed /\
    (frontAcquireBackedAfter3 (1 : Fin 3)).repairPending = true /\
    ¬ SpliceSafeR1V3 hTwo ring3 frontAcquireBackedAfter3 := by
  decide

/-- `0 -> 1` is the unique prepared barrier.  Its only certificate is that the
right endpoint is a pending predecessor; PendingOwnerAbort deletes it. -/
def pendingOwnerAbortStart3 : R1ConfigV5 3 2 0 0 := fun i =>
  if i = 0 then
    B9SpliceR2AttackRerun.xcell false 0 false .none false
  else if i = 1 then
    B9SpliceR2AttackRerun.xcell false 0 false .predecessorArmed true
  else
    B9SpliceR2AttackRerun.xcell false 1 false .front true

def pendingOwnerAbortAfter3 : R1ConfigV5 3 2 0 0 :=
  serveV5 ring3 pendingOwnerAbortStart3 (0 : Fin 3)

theorem pendingOwnerAbort_breaks_spliceSafeR1V3 :
    SpliceSafeR1V3 hTwo ring3 pendingOwnerAbortStart3 /\
    PendingOwnerAbortGuardV3
      (pendingOwnerAbortStart3 (0 : Fin 3))
      (pendingOwnerAbortStart3 (1 : Fin 3)) /\
    ¬ SpliceSafeR1V3 hTwo ring3 pendingOwnerAbortAfter3 := by
  decide

/-- At psi=3, edge `0 -> 1` is a barrier while the reverse edge is aligned.
The victim,true on site 1 is the only certificate of the barrier. -/
def moveAcquireAbortStart2 : R1ConfigV5 2 3 0 0 := fun i =>
  if i = 0 then x3 false 0 .predecessorArmed false
  else x3 false 2 .victimArmed true

def moveAcquireAbortAfter2 : R1ConfigV5 2 3 0 0 :=
  stepV5 hThree hOne hOneThree ring2 moveAcquireAbortStart2 (1 : Fin 2)

theorem moveAcquireAbort_breaks_spliceSafeR1V3 :
    SpliceSafeR1V3 hThree ring2 moveAcquireAbortStart2 /\
    MoveAcquireAbortGuardV3
      (moveAcquireAbortStart2 (1 : Fin 2))
      (moveAcquireAbortStart2 (0 : Fin 2)) /\
    ¬ SpliceSafeR1V3 hThree ring2 moveAcquireAbortAfter2 := by
  decide

/-- Forward edge is aligned; the reverse edge is a barrier protected solely by
the left `front,true`.  The inherited orphan scrub removes that certificate. -/
def orphanReservedFrontStart2 : R1ConfigV5 2 3 0 0 := fun i =>
  if i = 0 then x3 false 0 .none false
  else x3 false 1 .front true

def orphanReservedFrontAfter2 : R1ConfigV5 2 3 0 0 :=
  stepV5 hThree hOne hOneThree ring2 orphanReservedFrontStart2 (0 : Fin 2)

theorem orphanReservedFront_breaks_spliceSafeR1V3 :
    SpliceSafeR1V3 hThree ring2 orphanReservedFrontStart2 /\
    OrphanReservedFrontGuardV3
      (orphanReservedFrontStart2 (0 : Fin 2))
      (orphanReservedFrontStart2 (1 : Fin 2)) /\
    ¬ SpliceSafeR1V3 hThree ring2 orphanReservedFrontAfter2 := by
  decide

/-! ## Requested v4 fixture reruns -/

private def drain3 : List (Fin 3) := [0, 1, 0]
private def drain4 : List (Fin 4) := [0, 2, 0, 2]
private def drain5 : List (Fin 5) := [0, 1, 0]

theorem three_leaderless_drains_rechecked_v5 :
    LeaderlessV3 B9SpliceR2AttackRerun.loop3Start /\
    RolesClearV3 (runV5 ring3 B9SpliceR2AttackRerun.loop3Start drain3) /\
    LeaderlessV3 B9SpliceR2AttackRerun.loop4Start /\
    RolesClearV3 (runV5 ring4 B9SpliceR2AttackRerun.loop4Start drain4) /\
    LeaderlessV3 B9SpliceR2AttackRerun.loop5Start /\
    RolesClearV3 (runV5 ring5 B9SpliceR2AttackRerun.loop5Start drain5) := by
  decide

private def q11592Armed4V5 : R1ConfigV5 4 2 0 0 :=
  serveV5 ring4 B9SpliceR2AttackRerun.q11592Start4 (1 : Fin 4)

private def q11592Replay4V5 : R1ConfigV5 4 2 0 0 :=
  serveV5 ring4 q11592Armed4V5 (1 : Fin 4)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
theorem q11592_attack_rechecked_v5 :
    PendingHoldGuard hTwo hTwo hTwoLe
      (q11592Armed4V5 (1 : Fin 4))
      (q11592Armed4V5 (2 : Fin 4)) /\
    SpliceSafeR1V3 hTwo ring4 q11592Armed4V5 /\
    (forall i, q11592Replay4V5 i = q11592Armed4V5 i) := by
  decide

private def followerOldFirstV5 : R1ConfigV5 5 2 0 0 :=
  serveV5 ring5 B9SpliceR2AttackRerun.followerStart5 (0 : Fin 5)

theorem old_follower_attack_rechecked_v5 :
    role (followerOldFirstV5 (0 : Fin 5)) = .predecessorArmed /\
    role (followerOldFirstV5 (1 : Fin 5)) = .none := by
  decide

private def followerAfterSeekV5 : R1ConfigV5 5 2 0 0 :=
  serveV5 ring5 B9SpliceControllerR1TableV3.followerStart5V3 (0 : Fin 5)

private def followerAfterAcquireV5 : R1ConfigV5 5 2 0 0 :=
  serveV5 ring5 followerAfterSeekV5 (1 : Fin 5)

def followerAfter5V5 : R1ConfigV5 5 2 0 0 :=
  runV5 ring5 B9SpliceControllerR1TableV3.followerStart5V3
    B9SpliceControllerR1TableV3.followerWord5V3

theorem authenticated_follower_chain_progresses_v5 :
    (forall i, followerAfterSeekV5 i =
      B9SpliceControllerR1TableV3.followerStart5V3 i) /\
    MoveAcquireFrontGuardV5 hTwo
      (followerAfterSeekV5 (1 : Fin 5))
      (followerAfterSeekV5 (2 : Fin 5)) /\
    role (followerAfterAcquireV5 (1 : Fin 5)) = .predecessorArmed /\
    (followerAfterAcquireV5 (1 : Fin 5)).repairPending = true /\
    safeAlongV5 ring5 B9SpliceControllerR1TableV3.followerStart5V3
      B9SpliceControllerR1TableV3.followerWord5V3 = true /\
    sourceFreeAlongV5 ring5 B9SpliceControllerR1TableV3.followerStart5V3
      B9SpliceControllerR1TableV3.followerWord5V3 = true /\
    role (followerAfter5V5 (2 : Fin 5)) = .predecessorArmed /\
    (followerAfter5V5 (2 : Fin 5)).repairPending = false /\
    ReservedFrontHoldGuard (followerAfter5V5 (3 : Fin 5)) /\
    (followerAfter5V5 (2 : Fin 5)).splice.base.core.core.probe = false := by
  decide

private def stagedArmed3V5 : R1ConfigV5 3 2 0 0 :=
  serveV5 ring3 B9SpliceR2AttackRerun.stagedStart3 (1 : Fin 3)

private def starvationFinal3V5 : R1ConfigV5 3 2 0 0 :=
  runV5 ring3 B9SpliceR2AttackRerun.stagedStart3
    B9SpliceR2AttackRerun.starvationWord3

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
theorem staged_deletion_attack_rechecked_v5 :
    (forall i,
      serveV5 ring3 stagedArmed3V5 (2 : Fin 3) i = stagedArmed3V5 i) /\
    (forall i,
      serveV5 ring3 stagedArmed3V5 (1 : Fin 3) i = stagedArmed3V5 i) /\
    safeAlongV5 ring3 B9SpliceR2AttackRerun.stagedStart3
      B9SpliceR2AttackRerun.starvationWord3 = true /\
    RolesClearV3 starvationFinal3V5 /\
    (starvationFinal3V5 (1 : Fin 3)).splice.base.core.core.leader = false /\
    (starvationFinal3V5 (2 : Fin 3)).splice.base.core.core.leader = true := by
  decide

/-! ## Explicit per-rule census metadata -/

inductive V5Rule where
  | armA | armB | deleteStage | pendingHold | pendingAbort
  | moveCommit | moveStop | moveSeek | moveSeekHold
  | pendingOwnerAbort | pendingOwnerHold
  | moveAcquireFront | moveAcquireLegacy | moveAcquireAbort
  | orphanReservedFront | reservedFrontHold
  | victimRightScrub | victimLeftScrub | frontRightScrub
  | malformedLeftPending | malformedRightPending
  | predecessorLeftScrub | leftFrontHold | markedHold | ordinaryHost
  deriving DecidableEq, Repr

inductive SafetyStatusV5 where
  | preserves
  | counterexample
  | physicalFrameOnly
  deriving DecidableEq, Repr

/-- Audit classification.  `physicalFrameOnly` records exactly the final host
branch for which the imported source proves controller framing but not a generic
`SpliceSafeR1V3` closure theorem from the bare V3 predicate. -/
def safetyStatusV5 : V5Rule -> SafetyStatusV5
  | .pendingOwnerAbort
  | .moveAcquireFront
  | .moveAcquireAbort
  | .orphanReservedFront => .counterexample
  | .ordinaryHost => .physicalFrameOnly
  | _ => .preserves

theorem safety_census_statuses_v5 :
    safetyStatusV5 .moveSeek = .preserves /\
    safetyStatusV5 .moveStop = .preserves /\
    safetyStatusV5 .moveAcquireFront = .counterexample /\
    safetyStatusV5 .pendingOwnerAbort = .counterexample /\
    safetyStatusV5 .moveAcquireAbort = .counterexample /\
    safetyStatusV5 .orphanReservedFront = .counterexample /\
    safetyStatusV5 .ordinaryHost = .physicalFrameOnly := by
  decide

/-! ## Potential on the v5 writes -/

/-- Weight function of the potential. -/
def controllerWeightV5
    (u : R1AgentStateV5 psi kappa tau) : Nat :=
  match role u, u.repairPending with
  | .none, false => 0
  | .none, true => 1
  | .predecessorArmed, false => 1
  | .predecessorArmed, true => 2
  | .victimArmed, false => 1
  | .victimArmed, true => 3
  | .front, false => 1
  | .front, true => 4

def pairPotentialV5
    (l r : R1AgentStateV5 psi kappa tau) : Nat :=
  controllerWeightV5 l + controllerWeightV5 r

theorem moveAcquireFront_write_drop_two
    (hpsi : 0 < psi)
    (l r : R1AgentStateV5 psi kappa tau)
    (h : MoveAcquireFrontGuardV5 hpsi l r) :
    pairPotentialV5 (setControl l .predecessorArmed true) r + 2 =
      pairPotentialV5 l r := by
  rcases h with ⟨hl, _hllead, _hr, _hrlead, _⟩
  unfold ReservedFrontHoldGuard at hl
  rcases hl with ⟨hlr, hlp⟩
  have hbefore : controllerWeightV5 l = 4 := by
    simp [controllerWeightV5, hlr, hlp]
  have hafter :
      controllerWeightV5 (setControl l .predecessorArmed true) = 2 := by
    simp [controllerWeightV5, setControl, role]
  have hlocal :
      controllerWeightV5 (setControl l .predecessorArmed true) + 2 =
        controllerWeightV5 l := by
    calc
      controllerWeightV5 (setControl l .predecessorArmed true) + 2 =
          2 + 2 := by rw [hafter]
      _ = 4 := rfl
      _ = controllerWeightV5 l := hbefore.symm
  change
    (controllerWeightV5 (setControl l .predecessorArmed true) +
        controllerWeightV5 r) + 2 =
      controllerWeightV5 l + controllerWeightV5 r
  calc
    (controllerWeightV5 (setControl l .predecessorArmed true) +
        controllerWeightV5 r) + 2 =
        controllerWeightV5 (setControl l .predecessorArmed true) +
          (controllerWeightV5 r + 2) := by
            rw [Nat.add_assoc]
    _ = controllerWeightV5 (setControl l .predecessorArmed true) +
          (2 + controllerWeightV5 r) := by
            rw [Nat.add_comm (controllerWeightV5 r) 2]
    _ = (controllerWeightV5 (setControl l .predecessorArmed true) + 2) +
          controllerWeightV5 r := by
            rw [← Nat.add_assoc]
    _ = controllerWeightV5 l + controllerWeightV5 r := by
          rw [hlocal]

theorem moveStopFollower_write_drop_one
    (hpsi : 0 < psi)
    (l r : R1AgentStateV5 psi kappa tau)
    (h : MoveStopGuardV3 hpsi l r) :
    pairPotentialV5 (clearControl l) r + 1 = pairPotentialV5 l r := by
  rcases h with ⟨hlr, hlp, _hr, _⟩
  have hbefore : controllerWeightV5 l = 1 := by
    simp [controllerWeightV5, hlr, hlp]
  have hafter : controllerWeightV5 (clearControl l) = 0 := by
    simp [controllerWeightV5, clearControl, setControl, role]
  have hlocal :
      controllerWeightV5 (clearControl l) + 1 = controllerWeightV5 l := by
    calc
      controllerWeightV5 (clearControl l) + 1 = 0 + 1 := by
        rw [hafter]
      _ = 1 := rfl
      _ = controllerWeightV5 l := hbefore.symm
  change
    (controllerWeightV5 (clearControl l) + controllerWeightV5 r) + 1 =
      controllerWeightV5 l + controllerWeightV5 r
  calc
    (controllerWeightV5 (clearControl l) + controllerWeightV5 r) + 1 =
        controllerWeightV5 (clearControl l) +
          (controllerWeightV5 r + 1) := by
            rw [Nat.add_assoc]
    _ = controllerWeightV5 (clearControl l) +
          (1 + controllerWeightV5 r) := by
            rw [Nat.add_comm (controllerWeightV5 r) 1]
    _ = (controllerWeightV5 (clearControl l) + 1) +
          controllerWeightV5 r := by
            rw [← Nat.add_assoc]
    _ = controllerWeightV5 l + controllerWeightV5 r := by
          rw [hlocal]

theorem pendingOwnerAbort_write_drop
    (l r : R1AgentStateV5 psi kappa tau)
    (h : PendingOwnerAbortGuardV3 l r) :
    pairPotentialV5 l (clearControl r) < pairPotentialV5 l r := by
  rcases h with ⟨hrr, hrp, _⟩
  have hbefore : controllerWeightV5 r = 2 := by
    simp [controllerWeightV5, hrr, hrp]
  have hafter : controllerWeightV5 (clearControl r) = 0 := by
    simp [controllerWeightV5, clearControl, setControl, role]
  have hlocal :
      controllerWeightV5 (clearControl r) < controllerWeightV5 r := by
    calc
      controllerWeightV5 (clearControl r) = 0 := hafter
      _ < 2 := by decide
      _ = controllerWeightV5 r := hbefore.symm
  simpa [pairPotentialV5] using
    Nat.add_lt_add_left hlocal (controllerWeightV5 l)

theorem moveAcquireAbort_write_drop
    (l r : R1AgentStateV5 psi kappa tau)
    (h : MoveAcquireAbortGuardV3 l r) :
    pairPotentialV5 (clearControl l) r < pairPotentialV5 l r := by
  rcases h with ⟨hlr, hlp, _hlFollower, _⟩
  have hbefore : controllerWeightV5 l = 3 := by
    simp [controllerWeightV5, hlr, hlp]
  have hafter : controllerWeightV5 (clearControl l) = 0 := by
    simp [controllerWeightV5, clearControl, setControl, role]
  have hlocal :
      controllerWeightV5 (clearControl l) < controllerWeightV5 l := by
    calc
      controllerWeightV5 (clearControl l) = 0 := hafter
      _ < 3 := by decide
      _ = controllerWeightV5 l := hbefore.symm
  simpa [pairPotentialV5] using
    Nat.add_lt_add_right hlocal (controllerWeightV5 r)

theorem orphanReservedFront_write_drop
    (l r : R1AgentStateV5 psi kappa tau)
    (h : OrphanReservedFrontGuardV3 l r) :
    pairPotentialV5 l (clearControl r) < pairPotentialV5 l r := by
  rcases h with ⟨hr, _⟩
  unfold ReservedFrontHoldGuard at hr
  rcases hr with ⟨hrr, hrp⟩
  have hbefore : controllerWeightV5 r = 4 := by
    simp [controllerWeightV5, hrr, hrp]
  have hafter : controllerWeightV5 (clearControl r) = 0 := by
    simp [controllerWeightV5, clearControl, setControl, role]
  have hlocal :
      controllerWeightV5 (clearControl r) < controllerWeightV5 r := by
    calc
      controllerWeightV5 (clearControl r) = 0 := hafter
      _ < 4 := by decide
      _ = controllerWeightV5 r := hbefore.symm
  simpa [pairPotentialV5] using
    Nat.add_lt_add_left hlocal (controllerWeightV5 l)

end B9SpliceControllerR1TableV5

#print axioms B9SpliceControllerR1TableV5.controllerStateFactorV5_eq
#print axioms B9SpliceControllerR1TableV5.moveSeek_rowV5_stutters
#print axioms B9SpliceControllerR1TableV5.moveAcquireFront_rowV5
#print axioms B9SpliceControllerR1TableV5.q11668_moveStop_rechecked_v5
#print axioms B9SpliceControllerR1TableV5.q11681_moveSeek_rechecked_v5
#print axioms B9SpliceControllerR1TableV5.frontAcquire_breaks_spliceSafeR1V3
#print axioms B9SpliceControllerR1TableV5.pendingOwnerAbort_breaks_spliceSafeR1V3
#print axioms B9SpliceControllerR1TableV5.moveAcquireAbort_breaks_spliceSafeR1V3
#print axioms B9SpliceControllerR1TableV5.orphanReservedFront_breaks_spliceSafeR1V3
#print axioms B9SpliceControllerR1TableV5.three_leaderless_drains_rechecked_v5
#print axioms B9SpliceControllerR1TableV5.q11592_attack_rechecked_v5
#print axioms B9SpliceControllerR1TableV5.old_follower_attack_rechecked_v5
#print axioms B9SpliceControllerR1TableV5.authenticated_follower_chain_progresses_v5
#print axioms B9SpliceControllerR1TableV5.staged_deletion_attack_rechecked_v5
#print axioms B9SpliceControllerR1TableV5.safety_census_statuses_v5
#print axioms B9SpliceControllerR1TableV5.moveAcquireFront_write_drop_two
#print axioms B9SpliceControllerR1TableV5.moveStopFollower_write_drop_one
#print axioms B9SpliceControllerR1TableV5.pendingOwnerAbort_write_drop
#print axioms B9SpliceControllerR1TableV5.moveAcquireAbort_write_drop
#print axioms B9SpliceControllerR1TableV5.orphanReservedFront_write_drop
