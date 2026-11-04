import Leader.Wu.Splice.MovingFrontTable
import Leader.Wu.Splice.RulerDeletionCounterexample

set_option autoImplicit false
set_option Elab.async false
set_option pp.structureInstances false

namespace B9SpliceR2AttackRerun

open PPLL PPLLDomain PPLLResearchFormulation
  PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
  PPLLLeaderCreationCleanupRepair
open BirthSigMoveDisposalRepair
  BirthShortDoneTerminalBirthSources
open Q11593SpliceControllerDesign
open B9SpliceControllerR1Table

private theorem hTwo : 0 < 2 := by decide
private theorem hTwoLe : 2 <= 2 := by decide
private theorem hThree : 0 < 3 := by decide
private theorem hFour : 0 < 4 := by decide
private theorem hFive : 0 < 5 := by decide

abbrev E := ExpiringAgentState 2 0 0
abbrev X := R1AgentState 2 0 0

/-- Neutral finite physical cell; only leader, label and probe vary. -/
def rawCell
    (leader : Bool) (label : Fin 2) (probe : Bool) : AgentState 2 :=
  { BirthShortDoneTerminalPositiveWitness.raw probe with
    leader := leader
    label := label }

private theorem rawCell_domain
    (leader : Bool) (label : Fin 2) (probe : Bool) :
    (rawCell leader label probe).inProtocolDomain 0 := by
  simp [rawCell, BirthShortDoneTerminalPositiveWitness.raw,
    AgentState.inProtocolDomain]

def cell
    (leader : Bool) (label : Fin 2) (probe : Bool) : E :=
  ⟨⟨BoundedAgentState.ofDomain
      (rawCell leader label probe)
      (rawCell_domain leader label probe), false⟩, 0⟩

def xcell
    (leader : Bool) (label : Fin 2) (probe : Bool)
    (r : SpliceRole) (pending : Bool) : X :=
  { splice :=
      { base := cell leader label probe
        spliceRole := r }
    repairPending := pending }

def neutralR1 (b : E) : X :=
  { splice := { base := b, spliceRole := .none }
    repairPending := false }

private def ring3 : DirectedRing 3 := ⟨hThree⟩
private def ring4 : DirectedRing 4 := ⟨hFour⟩
private def ring5 : DirectedRing 5 := ⟨hFive⟩

def serve {n : Nat}
    (ring : DirectedRing n)
    (C : R1Config n 2 0 0) (e : Fin n) :
    R1Config n 2 0 0 :=
  step hTwo hTwo hTwoLe ring C e

def run {n : Nat}
    (ring : DirectedRing n)
    (C : R1Config n 2 0 0)
    (word : List (Fin n)) : R1Config n 2 0 0 :=
  List.foldl (fun D e => serve ring D e) C word

def R1Leaderless {n : Nat} (C : R1Config n 2 0 0) : Prop :=
  forall i, (C i).splice.base.core.core.leader = false

def RolesClearR1 {n : Nat} (C : R1Config n 2 0 0) : Prop :=
  forall i, role (C i) = .none /\ (C i).repairPending = false

/-! Closed finite deciders used only by the attack fixtures. -/

private instance instDecidablePreparedDangerAtLocal
    {n psi kappa tau : Nat}
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (C : R1Config n psi kappa tau) (e : Fin n) :
    Decidable (PreparedDangerAt hpsi ring C e) := by
  unfold PreparedDangerAt PreparedBarrierAt
  dsimp only
  unfold isBarrier
  infer_instance

private instance instDecidableR1ProtectedSpliceEdgeLocal
    {n psi kappa tau : Nat}
    (ring : DirectedRing n) (C : R1Config n psi kappa tau)
    (e : Fin n) :
    Decidable (R1ProtectedSpliceEdge ring C e) := by
  unfold R1ProtectedSpliceEdge
  dsimp only
  infer_instance

private instance instDecidableSpliceSafeR1Local
    {n psi kappa tau : Nat}
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (C : R1Config n psi kappa tau) :
    Decidable (SpliceSafeR1 hpsi ring C) := by
  unfold SpliceSafeR1
  infer_instance

private instance instDecidableR1LeaderlessLocal
    {n : Nat} (C : R1Config n 2 0 0) :
    Decidable (R1Leaderless C) := by
  unfold R1Leaderless
  infer_instance

private instance instDecidableRolesClearR1Local
    {n : Nat} (C : R1Config n 2 0 0) :
    Decidable (RolesClearR1 C) := by
  unfold RolesClearR1
  infer_instance

private instance instDecidableLeftDeletionCandidateLocal
    {psi width kappa tau : Nat}
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (l r : SpliceAgentState psi kappa tau) :
    Decidable (LeftDeletionCandidate hpsi hwidth hle l r) := by
  unfold LeftDeletionCandidate
  infer_instance

private instance instDecidablePendingHoldGuardLocal
    {psi width kappa tau : Nat}
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (l r : R1AgentState psi kappa tau) :
    Decidable (PendingHoldGuard hpsi hwidth hle l r) := by
  unfold PendingHoldGuard LeftDeletionCandidate
  infer_instance

private instance instDecidablePPrimeBarrierBirthGuardLocal
    {psi : Nat} (hpsi : 0 < psi)
    (l r : AuthorizedAgentState psi) :
    Decidable (PPrimeBarrierBirthGuard hpsi l r) := by
  unfold PPrimeBarrierBirthGuard
  unfold isBarrier
  infer_instance

/-- R1 version of the amended P-prime source: all three R1-owned moving
shapes count as protected, not only the predecessorArmed -> front. -/
def R1AmendedPPrimeAt
    {n psi kappa tau : Nat}
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (C : R1Config n psi kappa tau) (e : Fin n) : Prop :=
  let l0 := preparedR1 hpsi (C e)
  let r0 := preparedR1 hpsi (C (ring.rightNeighbor e))
  PPrimeBarrierBirthGuard hpsi l0 r0 /\
    ¬ R1ProtectedSpliceEdge ring C e

private instance instDecidableR1AmendedPPrimeAtLocal
    {n psi kappa tau : Nat}
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (C : R1Config n psi kappa tau) (e : Fin n) :
    Decidable (R1AmendedPPrimeAt hpsi ring C e) := by
  unfold R1AmendedPPrimeAt
  dsimp only
  infer_instance

def R1SourceFree
    {n psi kappa tau : Nat}
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (C : R1Config n psi kappa tau) : Prop :=
  forall e, ¬ R1AmendedPPrimeAt hpsi ring C e

private instance instDecidableR1SourceFreeLocal
    {n psi kappa tau : Nat}
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (C : R1Config n psi kappa tau) :
    Decidable (R1SourceFree hpsi ring C) := by
  unfold R1SourceFree
  infer_instance

/-- Boolean trace checkers keep the closed certificates compact. -/
def leaderlessAlongB {n : Nat} (ring : DirectedRing n) :
    R1Config n 2 0 0 -> List (Fin n) -> Bool
  | C, [] => decide (R1Leaderless C)
  | C, e :: es =>
      decide (R1Leaderless C) &&
        leaderlessAlongB ring (serve ring C e) es

def safeAlongB {n : Nat} (ring : DirectedRing n) :
    R1Config n 2 0 0 -> List (Fin n) -> Bool
  | C, [] => decide (SpliceSafeR1 hTwo ring C)
  | C, e :: es =>
      decide (SpliceSafeR1 hTwo ring C) &&
        safeAlongB ring (serve ring C e) es

def sourceFreeAlongB {n : Nat} (ring : DirectedRing n) :
    R1Config n 2 0 0 -> List (Fin n) -> Bool
  | C, [] => decide (R1SourceFree hTwo ring C)
  | C, e :: es =>
      decide (R1SourceFree hTwo ring C) &&
        sourceFreeAlongB ring (serve ring C e) es

/-! ## Attack 1: leaderless drain -- FAIL -/

/-- One owned defect on the odd 3-ring. -/
def loop3Start : R1Config 3 2 0 0 := fun i =>
  if i = 0 then xcell false 0 false .predecessorArmed false
  else if i = 1 then xcell false 0 false .front false
  else xcell false 1 false .none false

/-- One lap moves the defect once around the ring and complements labels;
two fair laps return the entire state. -/
def loop3Lap : List (Fin 3) :=
  [0, 1, 0, 1, 2, 1, 2, 0, 2]

def loop3Word : List (Fin 3) := loop3Lap ++ loop3Lap

theorem leaderless_cycle3 :
    safeAlongB ring3 loop3Start loop3Word = true /\
    leaderlessAlongB ring3 loop3Start loop3Word = true /\
    (0 : Fin 3) ∈ loop3Word /\
    (1 : Fin 3) ∈ loop3Word /\
    (2 : Fin 3) ∈ loop3Word /\
    (forall i,
      run ring3 loop3Start loop3Word i = loop3Start i) := by
  decide

/-- Two owned barriers on the 4-ring. -/
def loop4Start : R1Config 4 2 0 0 := fun i =>
  if i = 0 then xcell false 0 false .predecessorArmed false
  else if i = 1 then xcell false 0 false .front false
  else if i = 2 then xcell false 1 false .predecessorArmed false
  else xcell false 1 false .front false

/-- After both predecessor/front barriers execute MOVE-SEEK, the requests face
busy predecessor targets. -/
def loop4Dead : R1Config 4 2 0 0 :=
  serve ring4 (serve ring4 loop4Start (0 : Fin 4)) (2 : Fin 4)

theorem leaderless_deadlock4 :
    safeAlongB ring4 loop4Start [(0 : Fin 4), (2 : Fin 4)] = true /\
    R1Leaderless loop4Dead /\
    SpliceSafeR1 hTwo ring4 loop4Dead /\
    (forall e i,
      serve ring4 loop4Dead e i = loop4Dead i) := by
  decide

/-- One owned defect on the odd 5-ring. -/
def loop5Start : R1Config 5 2 0 0 := fun i =>
  if i = 0 then xcell false 0 false .predecessorArmed false
  else if i = 1 then xcell false 0 false .front false
  else if i = 2 then xcell false 1 false .none false
  else if i = 3 then xcell false 0 false .none false
  else xcell false 1 false .none false

def loop5Lap : List (Fin 5) :=
  [0, 1, 0, 1, 2, 1, 2, 3, 2, 3, 4, 3, 4, 0, 4]

def loop5Word : List (Fin 5) := loop5Lap ++ loop5Lap

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
theorem leaderless_cycle5 :
    safeAlongB ring5 loop5Start loop5Word = true /\
    leaderlessAlongB ring5 loop5Start loop5Word = true /\
    (0 : Fin 5) ∈ loop5Word /\
    (1 : Fin 5) ∈ loop5Word /\
    (2 : Fin 5) ∈ loop5Word /\
    (3 : Fin 5) ∈ loop5Word /\
    (4 : Fin 5) ∈ loop5Word /\
    (forall i,
      run ring5 loop5Start loop5Word i = loop5Start i) := by
  decide

/-! ## Attack 2: same-edge replay -- SURVIVES -/

/-- Literal same-edge-replay physical fixture, with controller-neutral R1 state. -/
def q11592Start4 : R1Config 4 2 0 0 := fun i =>
  neutralR1 (B9RulerDeletionCounterexample.start i)

def q11592Armed4 : R1Config 4 2 0 0 :=
  serve ring4 q11592Start4 (1 : Fin 4)

def q11592Replay4 : R1Config 4 2 0 0 :=
  serve ring4 q11592Armed4 (1 : Fin 4)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
theorem q11592_pending_hold_replay :
    role (q11592Armed4 (1 : Fin 4)) = .victimArmed /\
    role (q11592Armed4 (2 : Fin 4)) = .front /\
    PendingHoldGuard hTwo hTwo hTwoLe
      (q11592Armed4 (1 : Fin 4))
      (q11592Armed4 (2 : Fin 4)) /\
    SpliceSafeR1 hTwo ring4 q11592Armed4 /\
    (forall i, q11592Replay4 i = q11592Armed4 i) := by
  decide

/-! ## Attack 3: follower anchor -- SURVIVES -/

/-- Exact follower-anchor geometry, lifted to R1. -/
def followerStart5 : R1Config 5 2 0 0 := fun i =>
  if i = 0 then xcell false 1 false .predecessorArmed false
  else if i = 1 then xcell false 1 false .front false
  else if i = 2 then xcell false 0 true .front false
  else if i = 3 then xcell false 1 false .none false
  else xcell true 0 false .none false

/-- MOVE-SEEK, MOVE-ACQUIRE, MOVE-COMMIT twice. -/
def followerWord5 : List (Fin 5) :=
  [0, 1, 0, 1, 2, 1]

def followerAfter5 : R1Config 5 2 0 0 :=
  run ring5 followerStart5 followerWord5

theorem follower_anchor_moving_front_safe :
    safeAlongB ring5 followerStart5 followerWord5 = true /\
    sourceFreeAlongB ring5 followerStart5 followerWord5 = true /\
    role (followerAfter5 (2 : Fin 5)) = .predecessorArmed /\
    (followerAfter5 (2 : Fin 5)).repairPending = false /\
    role (followerAfter5 (3 : Fin 5)) = .front /\
    (followerAfter5 (2 : Fin 5)).splice.base.core.core.probe = false := by
  decide

/-! ## Attack 4: staged deletion arm/scrub starvation -- SURVIVES -/

/-- Same local deletion pair as in Attack 2, on the smallest ring where every
scheduler edge touches the staged component. -/
def stagedStart3 : R1Config 3 2 0 0 := fun i =>
  if i = 0 then xcell false 0 false .none false
  else xcell true 0 false .none false

def stagedArmed3 : R1Config 3 2 0 0 :=
  serve ring3 stagedStart3 (1 : Fin 3)

/-- ARM-A; two attempted scrub/replay alternations; fair predecessor service;
DELETE; one harmless left-front service; MOVE-COMMIT; MOVE-STOP. -/
def starvationWord3 : List (Fin 3) :=
  [1, 2, 1, 2, 0, 1, 2, 0, 1]

def starvationFinal3 : R1Config 3 2 0 0 :=
  run ring3 stagedStart3 starvationWord3

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
theorem staged_deletion_not_arm_scrub_starved :
    (forall i,
      serve ring3 stagedArmed3 (2 : Fin 3) i = stagedArmed3 i) /\
    (forall i,
      serve ring3 stagedArmed3 (1 : Fin 3) i = stagedArmed3 i) /\
    (0 : Fin 3) ∈ starvationWord3 /\
    (1 : Fin 3) ∈ starvationWord3 /\
    (2 : Fin 3) ∈ starvationWord3 /\
    safeAlongB ring3 stagedStart3 starvationWord3 = true /\
    RolesClearR1 starvationFinal3 /\
    (starvationFinal3 (1 : Fin 3)).splice.base.core.core.leader = false /\
    (starvationFinal3 (2 : Fin 3)).splice.base.core.core.leader = true := by
  decide

end B9SpliceR2AttackRerun

#print axioms B9SpliceR2AttackRerun.leaderless_cycle3
#print axioms B9SpliceR2AttackRerun.leaderless_deadlock4
#print axioms B9SpliceR2AttackRerun.leaderless_cycle5
#print axioms B9SpliceR2AttackRerun.q11592_pending_hold_replay
#print axioms B9SpliceR2AttackRerun.follower_anchor_moving_front_safe
#print axioms B9SpliceR2AttackRerun.staged_deletion_not_arm_scrub_starved
