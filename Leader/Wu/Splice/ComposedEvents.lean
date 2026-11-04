import Leader.Wu.Splice.PhysicalHoldProjectionLetter
import Leader.Wu.Birth.ShortDoneTerminalPassiveFirstCap
import Leader.Wu.Birth.ShortDoneTerminalObserver
import Leader.Wu.Birth.WidthTwoWaitBlockProgress


set_option autoImplicit false


namespace B9SpliceComposedEvents


open PPLL PPLLDomain PPLLResearchFormulation PPLLExpiringComparisonRepair
open Q11593SpliceControllerDesign B9SpliceControllerR1Table
  B9SpliceControllerR1TableV6 B9SpliceControllerR1TableV7
  B9SpliceTableV10e B9SpliceV10eTransparency
  B9SpliceV10ePhysicalIsB7Step B9SpliceV10eProjection
  B9SpliceV10eWordProjection B9SpliceV10eProjectionLetter


variable {n psi width kappa tau : Nat}


/-
Source interfaces checked on main:
* projection_trichotomy:
  Leader/Wu/Splice/PhysicalHoldProjection.lean:1-150
* physical_of_hostStep, letterOf, projWord:
  Leader/Wu/Splice/PhysicalHoldProjectionLetter.lean:1-360
* serveWord and LeaderlessAlong:
  Leader/Wu/Splice/PhysicalHoldWordProjection.lean:1-220
* MoveCommitGuard:
  Leader/Wu/Splice/MovingFrontTable.lean:175-210
* RowCap2:
  Leader/Wu/Birth/ShortDoneTerminalPassiveFirstCap.lean:70-105
* birthEvent:
  Leader/Wu/Birth/ShortDoneTerminalObserver.lean:20-45
* shortCountAt:
  Leader/Wu/Birth/WidthTwoWaitBlockProgress.lean:30-85
-/


/-- A width-two cap that is actually executed by the composed V10e service. -/
def ActualCapAt
    (hpsi : 0 < psi) (h2 : 2 <= psi)
    (ring : DirectedRing n)
    (C : R1ConfigV6 n psi kappa tau) (e : Fin n) : Prop :=
  PhysicalServiceAt hpsi (by decide : 0 < 2) h2 ring C
      (stepV10e hpsi (by decide : 0 < 2) h2 ring C e) e /\
    BirthShortDoneTerminalPassiveR4.RowCap2
      hpsi h2 kappa ring (physicalProj C) e


/-- A physical birth row that is actually executed by the composed V10e service. -/
def ActualBirthAt
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (ring : DirectedRing n)
    (C : R1ConfigV6 n psi kappa tau) (e : Fin n) : Prop :=
  PhysicalServiceAt hpsi hwidth hle ring C
      (stepV10e hpsi hwidth hle ring C e) e /\
    BirthShortDoneTerminalObserver.birthEvent hpsi hwidth hle
      (physicalProj C e) (physicalProj C (ring.rightNeighbor e)) = true


/-- Existing V10e leaderless-along-word predicate, exposed under the composed-event name. -/
abbrev LeaderlessAlongV10e
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (ring : DirectedRing n) :
    List (Fin n) -> R1ConfigV6 n psi kappa tau -> Prop :=
  B9SpliceV10eWordProjection.LeaderlessAlong hpsi hwidth hle ring


/-- No victim role remains, and every predecessor is settled. -/
def ShapeClear (C : R1ConfigV6 n psi kappa tau) : Prop :=
  (forall i, role (C i).carrier ≠ .victimArmed) /\
  (forall i, role (C i).carrier = .predecessorArmed ->
    (C i).carrier.repairPending = false)


/-- If the service is neither physical nor MOVE-COMMIT, its physical projection stutters. -/
theorem stutter_frame
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau) (e : Fin n)
    (hne : ring.rightNeighbor e ≠ e)
    (hlead : forall i,
      (C i).carrier.splice.base.core.core.leader = false)
    (hS : SpliceSafeV7 hpsi ring C)
    (hnphys : ¬ (PhysicalServiceAt hpsi hwidth hle ring C
      (stepV10e hpsi hwidth hle ring C e) e))
    (hncommit : ¬ (MoveCommitGuard
      (C e).carrier (C (ring.rightNeighbor e)).carrier)) :
    physicalProj (stepV10e hpsi hwidth hle ring C e) = physicalProj C := by
  rcases projection_trichotomy hpsi hwidth hle ring C e hne hlead hS with
    hstutter | hhost | hcommit
  · exact hstutter
  · have hp : PhysicalServiceAt hpsi hwidth hle ring C
        (stepV10e hpsi hwidth hle ring C e) e :=
      physical_of_hostStep hpsi hwidth hle ring C
        (stepV10e hpsi hwidth hle ring C e) e hne hhost
    exact (hnphys hp).elim
  · exact (hncommit hcommit.1).elim


/-- ShapeClear excludes MOVE-COMMIT because that row requires a pending predecessor on the right. -/
theorem noCommit_of_shapeClear
    (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau) (e : Fin n)
    (hclear : ShapeClear C) :
    ¬ (MoveCommitGuard (C e).carrier (C (ring.rightNeighbor e)).carrier) := by
  intro hcommit
  unfold ShapeClear at hclear
  unfold MoveCommitGuard at hcommit
  rcases hcommit with ⟨_hlrole, _hlpending, hrrole, hrpending, _hrleader⟩
  have hfalse : (C (ring.rightNeighbor e)).carrier.repairPending = false :=
    hclear.2 (ring.rightNeighbor e) hrrole
  have hbad : (false : Bool) = true := hfalse.symm.trans hrpending
  cases hbad


/-- On ShapeClear, a leaderless safe V10e service projects only to stutter or one B7 host step. -/
theorem leaderless_stutter_projects
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau) (e : Fin n)
    (hclear : ShapeClear C)
    (hlead : forall i,
      (C i).carrier.splice.base.core.core.leader = false)
    (hS : SpliceSafeV7 hpsi ring C)
    (hne : ring.rightNeighbor e ≠ e) :
    physicalProj (stepV10e hpsi hwidth hle ring C e) = physicalProj C \/
      physicalProj (stepV10e hpsi hwidth hle ring C e) =
        BirthShortDoneTerminalConsumer.step hpsi hwidth hle ring
          (physicalProj C) e := by
  rcases projection_trichotomy hpsi hwidth hle ring C e hne hlead hS with
    hstutter | hhost | hcommit
  · exact Or.inl hstutter
  · exact Or.inr hhost
  · exact (noCommit_of_shapeClear ring C e hclear hcommit.1).elim


/-- A projection stutter preserves the B5 tracked short count. -/
theorem shortCountAt_stutter
    (ring : DirectedRing n) (anchor : Fin n)
    (C D : R1ConfigV6 n psi kappa tau)
    (hproj : physicalProj D = physicalProj C) :
    BirthPhaseWait2BlockProgress.shortCountAt ring anchor (physicalProj D) =
      BirthPhaseWait2BlockProgress.shortCountAt ring anchor (physicalProj C) := by
  rw [hproj]


end B9SpliceComposedEvents
