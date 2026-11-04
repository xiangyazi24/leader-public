import Leader.Wu.Splice.Controller
import Leader.Wu.Birth.ShortDoneTerminalPositiveWitness


namespace Q11605SpliceControllerAttack


open PPLL PPLLDomain PPLLResearchFormulation
  PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
  PPLLLeaderCreationCleanupRepair
open BirthSigMoveDisposalRepair
  BirthShortDoneTerminalBirthSources
open Q11593SpliceControllerDesign


set_option autoImplicit false
set_option Elab.async false
set_option pp.structureInstances false


private theorem hTwo : 0 < 2 := by decide
private theorem hTwoLe : 2 <= 2 := by decide
private theorem hFour : 0 < 4 := by decide
private theorem hFive : 0 < 5 := by decide


abbrev E := ExpiringAgentState 2 0 0
abbrev X := SpliceAgentState 2 0 0


/-- Neutral finite cell; only leader, label, and probe vary. -/
def rawCell (leader : Bool) (label : Fin 2) (probe : Bool) : AgentState 2 :=
  { BirthShortDoneTerminalPositiveWitness.raw probe with
    leader := leader
    label := label }


private theorem rawCell_domain
    (leader : Bool) (label : Fin 2) (probe : Bool) :
    (rawCell leader label probe).inProtocolDomain 0 := by
  simp [rawCell, BirthShortDoneTerminalPositiveWitness.raw,
    AgentState.inProtocolDomain]


def cell (leader : Bool) (label : Fin 2) (probe : Bool) : E :=
  ⟨⟨BoundedAgentState.ofDomain
      (rawCell leader label probe)
      (rawCell_domain leader label probe), false⟩, 0⟩


def xcell
    (leader : Bool) (label : Fin 2) (probe : Bool)
    (role : SpliceRole) : X :=
  ⟨cell leader label probe, role⟩


/-! ## ARM-A fallthrough census -/


def ring4 : DirectedRing 4 := ⟨hFour⟩


/-- Physical picture of the ARM-A fallthrough. -/
def start4 : Fin 4 -> E := fun i =>
  if i = 0 then cell false 0 false
  else if i = 1 then cell true 0 false
  else if i = 2 then cell true 0 false
  else cell false 1 false


def startX4 : SpliceConfig 4 2 0 0 := fun i =>
  ⟨start4 i, .none⟩


def oldRow (l r : X) : E × E :=
  BirthShortDoneTerminalHost.row hTwo hTwo hTwoLe l.base r.base


/-- These are the syntactic guards of the controller.  The fifth scrub rule,
leader-side abort, is handled in the prose: on the pending edge below its
canonical victim/front pair is still present, so the canonical-priority
condition says it is not an abort. -/
def ArmAGuard (l r : X) : Prop :=
  l.spliceRole = .none ∧
  r.spliceRole = .none ∧
  LeftDeletionCandidate hTwo hTwo hTwoLe l r


def ArmBGuard (l r : X) : Prop :=
  l.spliceRole = .none ∧
  r.spliceRole = .victimArmed ∧
  r.base.core.core.leader = true


def DeleteGuard (l r : X) : Prop :=
  l.spliceRole = .front ∧
  r.spliceRole = .front ∧
  LeftDeletionCandidate hTwo hTwo hTwoLe l r


def AdvanceGuard (l r : X) : Prop :=
  l.spliceRole = .predecessorArmed ∧
  r.spliceRole = .front ∧
  r.base.core.core.leader = false


def CanonicalFinishGuard (l r : X) : Prop :=
  l.spliceRole = .front ∧
  r.spliceRole = .front ∧
  l.base.core.core.leader = false


def StaleVictimGuard (l r : X) : Prop :=
  l.spliceRole = .victimArmed ∧
  ¬ (r.spliceRole = .front ∧
      LeftDeletionCandidate hTwo hTwo hTwoLe l r)


def OrphanPredecessorGuard (l r : X) : Prop :=
  l.spliceRole = .predecessorArmed ∧
  r.spliceRole ≠ .front


def UnownedFollowerFrontGuard (l r : X) : Prop :=
  r.spliceRole = .front ∧
  l.spliceRole ≠ .predecessorArmed ∧
  r.base.core.core.leader = false


def FrontFrontLeaderlessGuard (l r : X) : Prop :=
  l.spliceRole = .front ∧
  r.spliceRole = .front ∧
  l.base.core.core.leader = false ∧
  r.base.core.core.leader = false


def PendingCanonical (l r : X) : Prop :=
  l.spliceRole = .victimArmed ∧
  r.spliceRole = .front ∧
  LeftDeletionCandidate hTwo hTwo hTwoLe l r


/-! ## Decidable support for the finite attack certificates -/


/-- `LeftDeletionCandidate` is just two Boolean equalities once exposed. -/
private instance q11605DecidableLeftDeletionCandidate
    {psi width kappa tau : Nat}
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (l r : SpliceAgentState psi kappa tau) :
    Decidable (LeftDeletionCandidate hpsi hwidth hle l r) := by
  unfold LeftDeletionCandidate
  infer_instance


/-- Prepared barrierhood reduces to a follower Boolean and a finite-label
inequality. -/
private instance q11605DecidablePreparedBarrierAt
    {n psi kappa tau : Nat}
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (C : SpliceConfig n psi kappa tau) (e : Fin n) :
    Decidable (PreparedBarrierAt hpsi ring C e) := by
  unfold PreparedBarrierAt
  dsimp only
  unfold isBarrier
  infer_instance


private instance q11605DecidableProtectedSpliceEdge
    {n psi kappa tau : Nat}
    (ring : DirectedRing n) (C : SpliceConfig n psi kappa tau)
    (e : Fin n) :
    Decidable (ProtectedSpliceEdge ring C e) := by
  unfold ProtectedSpliceEdge
  infer_instance


/-- The source guard contains only Boolean/finite-field tests and barrierhood. -/
private instance q11605DecidablePPrimeBarrierBirthGuard
    {psi : Nat} (hpsi : 0 < psi)
    (l r : AuthorizedAgentState psi) :
    Decidable (PPrimeBarrierBirthGuard hpsi l r) := by
  unfold PPrimeBarrierBirthGuard
  unfold isBarrier
  infer_instance


/-- The standard `Fin n` forall decider closes the only quantified wrapper. -/
private instance q11605DecidableSpliceSafe
    {n psi kappa tau : Nat}
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (C : SpliceConfig n psi kappa tau) :
    Decidable (SpliceSafe hpsi ring C) := by
  unfold SpliceSafe
  infer_instance


private instance q11605DecidableSplicePPrimeBarrierBirthGuardAt
    {n psi kappa tau : Nat}
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (C : SpliceConfig n psi kappa tau) (e : Fin n) :
    Decidable (SplicePPrimeBarrierBirthGuardAt hpsi ring C e) := by
  unfold SplicePPrimeBarrierBirthGuardAt
  dsimp only
  infer_instance


private instance q11605DecidableArmAGuard (l r : X) :
    Decidable (ArmAGuard l r) := by
  unfold ArmAGuard
  infer_instance


private instance q11605DecidableArmBGuard (l r : X) :
    Decidable (ArmBGuard l r) := by
  unfold ArmBGuard
  infer_instance


private instance q11605DecidableDeleteGuard (l r : X) :
    Decidable (DeleteGuard l r) := by
  unfold DeleteGuard
  infer_instance


private instance q11605DecidableAdvanceGuard (l r : X) :
    Decidable (AdvanceGuard l r) := by
  unfold AdvanceGuard
  infer_instance


private instance q11605DecidableCanonicalFinishGuard (l r : X) :
    Decidable (CanonicalFinishGuard l r) := by
  unfold CanonicalFinishGuard
  infer_instance


private instance q11605DecidableStaleVictimGuard (l r : X) :
    Decidable (StaleVictimGuard l r) := by
  unfold StaleVictimGuard
  infer_instance


private instance q11605DecidableOrphanPredecessorGuard (l r : X) :
    Decidable (OrphanPredecessorGuard l r) := by
  unfold OrphanPredecessorGuard
  infer_instance


private instance q11605DecidableUnownedFollowerFrontGuard (l r : X) :
    Decidable (UnownedFollowerFrontGuard l r) := by
  unfold UnownedFollowerFrontGuard
  infer_instance


private instance q11605DecidableFrontFrontLeaderlessGuard (l r : X) :
    Decidable (FrontFrontLeaderlessGuard l r) := by
  unfold FrontFrontLeaderlessGuard
  infer_instance


private instance q11605DecidablePendingCanonical (l r : X) :
    Decidable (PendingCanonical l r) := by
  unfold PendingCanonical
  infer_instance


def armA (l r : X) : X × X :=
  ({ l with spliceRole := .victimArmed },
   { r with spliceRole := .front })


def armed12 : X × X := armA (startX4 1) (startX4 2)


def afterArmA : SpliceConfig 4 2 0 0 := fun i =>
  if i = 1 then armed12.1
  else if i = 2 then armed12.2
  else startX4 i


/-- The ordinary fallback exactly frames the roles. -/
def ordinaryLift (l r : X) : X × X :=
  let q := oldRow l r
  ({ l with base := q.1 }, { r with base := q.2 })


def fallen12 : X × X := ordinaryLift (afterArmA 1) (afterArmA 2)


def afterFallthrough : SpliceConfig 4 2 0 0 := fun i =>
  if i = 1 then fallen12.1
  else if i = 2 then fallen12.2
  else afterArmA i


set_option maxHeartbeats 50000000 in
set_option maxRecDepth 32768 in
/-- Closed guard census for the exact same-edge replay after ARM-A, followed by
what the §10 ordinary fallback does to the physical pair. -/
theorem q11592_armA_same_edge_fallthrough :
    ArmAGuard (startX4 1) (startX4 2) ∧
    PendingCanonical (afterArmA 1) (afterArmA 2) ∧
    ¬ ArmAGuard (afterArmA 1) (afterArmA 2) ∧
    ¬ ArmBGuard (afterArmA 1) (afterArmA 2) ∧
    ¬ DeleteGuard (afterArmA 1) (afterArmA 2) ∧
    ¬ AdvanceGuard (afterArmA 1) (afterArmA 2) ∧
    ¬ CanonicalFinishGuard (afterArmA 1) (afterArmA 2) ∧
    ¬ StaleVictimGuard (afterArmA 1) (afterArmA 2) ∧
    ¬ OrphanPredecessorGuard (afterArmA 1) (afterArmA 2) ∧
    ¬ UnownedFollowerFrontGuard (afterArmA 1) (afterArmA 2) ∧
    ¬ FrontFrontLeaderlessGuard (afterArmA 1) (afterArmA 2) ∧
    (afterFallthrough 1).base.core.core.leader = false ∧
    (afterFallthrough 2).base.core.core.leader = true ∧
    PreparedBarrierAt hTwo ring4 afterFallthrough 0 ∧
    ¬ ProtectedSpliceEdge ring4 afterFallthrough 0 ∧
    ¬ SpliceSafe hTwo ring4 afterFallthrough := by
  decide


/-! ## Follower-anchor ADVANCE counterexample -/


def ring5 : DirectedRing 5 := ⟨hFive⟩


/--
Before ADVANCE:
  0: follower label 1, predecessorArmed
  1: follower label 1, front
  2: follower label 0, front, probe=true
  3: follower label 1, none
  4: leader   label 0, none


The only follower barrier is 0 -> 1 and it is owned.
-/
def advanceBefore : SpliceConfig 5 2 0 0 := fun i =>
  if i = 0 then xcell false 1 false .predecessorArmed
  else if i = 1 then xcell false 1 false .front
  else if i = 2 then xcell false 0 true .front
  else if i = 3 then xcell false 1 false .none
  else xcell true 0 false .none


/-- Literal ADVANCE update on the pair (p,v). -/
def advancePair (p v : X) : X × X :=
  let next : Fin 2 :=
    ⟨(p.base.core.core.label.val + 1) % 2, Nat.mod_lt _ hTwo⟩
  let vBase : E :=
    { v.base with
      core := { v.base.core with
        core := { v.base.core.core with
          label := next,
          probe := false,
          phase := false } } }
  ({ p with spliceRole := .none },
   { v with base := vBase, spliceRole := .front })


def advanced01 : X × X :=
  advancePair (advanceBefore 0) (advanceBefore 1)


def advanceAfter : SpliceConfig 5 2 0 0 := fun i =>
  if i = 0 then advanced01.1
  else if i = 1 then advanced01.2
  else advanceBefore i


/-- Literal canonical FINISH on the original (v,s) edge: roles clear,
bases frame. -/
def finishAfter : SpliceConfig 5 2 0 0 := fun i =>
  if i = 1 then { advanceAfter i with spliceRole := .none }
  else if i = 2 then { advanceAfter i with spliceRole := .none }
  else advanceAfter i


/-- The generalized follower-anchor case refutes both proposed preservation
obligations.  ADVANCE moves the barrier from 0->1 to 1->2; because site 2 has
a live probe, the exact amended P-prime source is true.  Canonical FINISH then
clears the roles without changing that source. -/
theorem follower_anchor_advance_exposes_pprime :
    SpliceSafe hTwo ring5 advanceBefore ∧
    AdvanceGuard (advanceBefore 0) (advanceBefore 1) ∧
    PreparedBarrierAt hTwo ring5 advanceAfter 1 ∧
    ¬ ProtectedSpliceEdge ring5 advanceAfter 1 ∧
    ¬ SpliceSafe hTwo ring5 advanceAfter ∧
    SplicePPrimeBarrierBirthGuardAt hTwo ring5 advanceAfter 1 ∧
    CanonicalFinishGuard (advanceAfter 1) (advanceAfter 2) ∧
    SplicePPrimeBarrierBirthGuardAt hTwo ring5 finishAfter 1 := by
  decide


end Q11605SpliceControllerAttack


#print axioms Q11605SpliceControllerAttack.q11592_armA_same_edge_fallthrough
#print axioms Q11605SpliceControllerAttack.follower_anchor_advance_exposes_pprime
