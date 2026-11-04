import Leader.Wu.Birth.PreparedRulerBlocksPPrime
import Leader.Wu.Elimination.BirthDispatcherCollision

set_option autoImplicit false

namespace Q11593SpliceControllerDesign

open PPLL PPLLResearchFormulation
  PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
open PPLLLeaderCreationCleanupRepair
open BirthSigMoveDisposalRepair
  BirthShortDoneTerminalBirthSources
  BirthPhaseCohortDesign

variable {n psi width kappa tau : Nat}

/-- Constant-size local controller for one staged deletion splice. -/
inductive SpliceRole where
  | none
  | predecessorArmed
  | victimArmed
  | front
  deriving DecidableEq, Repr

/-- Additive outer carrier: the current physical state is untouched. -/
structure SpliceAgentState (psi kappa tau : Nat) where
  base : ExpiringAgentState psi kappa tau
  spliceRole : SpliceRole
  deriving DecidableEq, Repr

abbrev SpliceConfig (n psi kappa tau : Nat) :=
  Fin n -> SpliceAgentState psi kappa tau

/-- Exact prepared state inspected by the current P-prime source guard. -/
def prepared
    (hpsi : 0 < psi) (u : SpliceAgentState psi kappa tau) :
    AuthorizedAgentState psi :=
  normalizeDeletion (prepareExpiringDisposal hpsi u.base).core.erase

/-- The only role pair that owns an exceptional follower barrier. -/
def ProtectedSpliceEdge
    (ring : DirectedRing n)
    (C : SpliceConfig n psi kappa tau) (e : Fin n) : Prop :=
  (C e).spliceRole = .predecessorArmed /\
    (C (ring.rightNeighbor e)).spliceRole = .front

/-- The exact prepared geometric danger relevant to P-prime. -/
def PreparedBarrierAt
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (C : SpliceConfig n psi kappa tau) (e : Fin n) : Prop :=
  let l0 := prepared hpsi (C e)
  let r0 := prepared hpsi (C (ring.rightNeighbor e))
  r0.core.leader = false /\ isBarrier hpsi l0.core r0.core

/-- Global safety invariant: every prepared follower barrier has local splice
ownership.  This deliberately does not assert that every role is genuine. -/
def SpliceSafe
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (C : SpliceConfig n psi kappa tau) : Prop :=
  forall e, PreparedBarrierAt hpsi ring C e ->
    ProtectedSpliceEdge ring C e

/-- P-prime source predicate for the amended consumer.  A barrier owned by the
splice controller is consumed by `advance`, not by ordinary P-prime. -/
def SplicePPrimeBarrierBirthGuardAt
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (C : SpliceConfig n psi kappa tau) (e : Fin n) : Prop :=
  let l0 := prepared hpsi (C e)
  let r0 := prepared hpsi (C (ring.rightNeighbor e))
  PPrimeBarrierBirthGuard hpsi l0 r0 /\
    ¬ ProtectedSpliceEdge ring C e

/-- Immediate static half of the design: `SpliceSafe` excludes every amended
P-prime source. -/
theorem spliceSafe_blocks_amended_pprime
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (C : SpliceConfig n psi kappa tau)
    (hsafe : SpliceSafe hpsi ring C) :
    forall e, ¬ SplicePPrimeBarrierBirthGuardAt hpsi ring C e := by
  intro e hbirth
  unfold SplicePPrimeBarrierBirthGuardAt at hbirth
  dsimp only at hbirth
  rcases hbirth with ⟨hguard, hunowned⟩
  have hbarrier : PreparedBarrierAt hpsi ring C e := by
    unfold PreparedBarrierAt
    dsimp only
    unfold PPrimeBarrierBirthGuard at hguard
    exact ⟨hguard.2.1, hguard.2.2.2.2⟩
  exact hunowned (hsafe e hbarrier)

/-- Literal role-clear state used to hand execution back to the old consumer. -/
def RolesClear (C : SpliceConfig n psi kappa tau) : Prop :=
  forall i, (C i).spliceRole = .none

/-- In a role-clear configuration no edge is spuriously splice-owned. -/
theorem rolesClear_not_protected
    (ring : DirectedRing n) (C : SpliceConfig n psi kappa tau)
    (hclear : RolesClear C) (e : Fin n) :
    ¬ ProtectedSpliceEdge ring C e := by
  intro h
  have hp := h.1
  rw [hclear e] at hp
  cases hp

/-- Physical leaderlessness for the extended carrier. -/
def SpliceLeaderless (C : SpliceConfig n psi kappa tau) : Prop :=
  forall i, (C i).base.core.core.leader = false

/-- Prospective current-host left-leader deletion.  R2 should stage every such
row, with `collisionRow_of_both` as the first regression. -/
def LeftDeletionCandidate
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (l r : SpliceAgentState psi kappa tau) : Prop :=
  l.base.core.core.leader = true /\
    (BirthShortDoneTerminalHost.row
      hpsi hwidth hle l.base r.base).1.core.core.leader = false

/-- No genuine deletion-arm seed can be created while the physical
configuration is leaderless. -/
theorem leaderless_no_leftDeletionCandidate
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (C : SpliceConfig n psi kappa tau)
    (hzero : SpliceLeaderless C) (ring : DirectedRing n) (e : Fin n) :
    ¬ LeftDeletionCandidate hpsi hwidth hle
      (C e) (C (ring.rightNeighbor e)) := by
  intro h
  have hz := hzero e
  have ht := h.1
  have hbad : false = true := hz.symm.trans ht
  cases hbad

end Q11593SpliceControllerDesign

#print axioms Q11593SpliceControllerDesign.spliceSafe_blocks_amended_pprime
#print axioms Q11593SpliceControllerDesign.rolesClear_not_protected
#print axioms Q11593SpliceControllerDesign.leaderless_no_leftDeletionCandidate
