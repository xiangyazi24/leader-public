import Leader.Wu.Elimination.LDSinkTwoGapPhysPortSpec

set_option autoImplicit false

open FiniteUniformStoppingTree PredictableRenewalOverlap
open PPLLRepair LDSinkGapCleanup LDTwoGapFrame
open LDSinkTwoGapEpochKernel LDSinkTwoGapNoResetKernel LDSinkTwoGapAttemptCells
open LDSinkTwoGapEntrance LDSinkTwoGapDeletion LDSinkTwoGapDeletionWired
open LDSinkTwoGapReachInvariant LDSinkTwoGapRestartClosure
open CleanBoundaryDecision
open LDSinkTwoGapWiredInstance
open LDSinkTwoGapPhysPortSpecInstance

namespace LDSinkTwoGapRacePortDischarge

noncomputable section

variable {n psi : Nat}

/-- Exact local pre-FIRE data sufficient for the staged MOVE branch to delete
its left/initiator leader.  The last two clauses are precisely the guards that
prevent FIRE from shielding the victim or overwriting the live bullet. -/
def LocalDeleteReady (l r : AgentState psi) : Prop :=
  r.bullet = ⟨2, by omega⟩ ∧
  l.shield = false ∧
  l.leader = true ∧
  l.signal_B ≠ ⟨1, by omega⟩ ∧
  ¬ (r.leader = true ∧ r.signal_B = ⟨1, by omega⟩)

/-- The corresponding frame-local state predicate.  Turning this into
`NoResetSuccess` additionally needs the verified ring orientation saying that event
`F.attack.pos 0` presents positions 0 and 1 to the local transition. -/
def DeletionReady (F : TwoGapFrame n) (b : AState n psi) : Prop :=
  LocalDeleteReady
    (b.conf (F.attack.pos 0))
    (b.conf (F.attack.pos 1))

/-- Physical core: FIRE leaves the decisive fields alone, MOVE clears the
left leader, and SIGNAL cannot restore the left leader bit. -/
theorem staged_deletes_left
    (hpsi : psi > 0) (l r : AgentState psi)
    (hready : LocalDeleteReady l r) :
    (eliminateLeadersNoCollisionStaged hpsi l r).1.leader = false := by
  rcases hready with
    ⟨hbullet, hshield, hleader, hleftSignal, hrightFire⟩
  have hleftFire :
      ¬ (l.leader = true ∧ l.signal_B = ⟨1, by omega⟩) := by
    intro h
    exact hleftSignal h.2
  have hval : r.bullet.val = 2 := congrArg Fin.val hbullet
  have hpos : r.bullet.val > 0 := by
    omega
  have houter : r.bullet.val > 0 ∧ l.leader = true :=
    ⟨hpos, hleader⟩
  have hinner :
      r.bullet = ⟨2, by omega⟩ ∧ l.shield = false :=
    ⟨hbullet, hshield⟩
  unfold eliminateLeadersNoCollisionStaged
  dsimp only
  unfold eliminateLeadersNoCollisionFire
  dsimp only
  rw [if_neg hleftFire, if_neg hrightFire]
  unfold eliminateLeadersNoCollisionMove
  rw [if_pos houter, if_pos hinner]
  unfold eliminateLeadersNoCollisionSignal
  rfl

/-- Minimum remaining semantic statement.  `firstGood` is data because it
changes the inductively generated `SecondSupport`; the only proof field says
that every actually supported second-stage state has some successful edge. -/
structure ImmediateSuccessResidual
    (hpsi : psi > 0) (F : TwoGapFrame n) where
  firstGood : AState n psi → Fin n
  exists_success : ∀ b : AState n psi,
    SecondSupport hpsi F firstGood b →
      ∃ e : Fin n,
        NoResetSuccess F (attemptStepConf hpsi F b e)

/-- Select the successful edge on supported states.  Outside `SecondSupport`
the value is irrelevant to `RacePortResidual.success`, so use the already
proved frame port `port0` as a total fallback. -/
noncomputable def chosenSecondGood
    (hpsi : psi > 0) (F : TwoGapFrame n)
    (H : ImmediateSuccessResidual hpsi F)
    (b : AState n psi) : Fin n := by
  classical
  exact if hs : SecondSupport hpsi F H.firstGood b then
    Classical.choose (H.exists_success b hs)
  else
    port0 F

theorem chosenSecondGood_success
    (hpsi : psi > 0) (F : TwoGapFrame n)
    (H : ImmediateSuccessResidual hpsi F)
    (b : AState n psi)
    (hsupport : SecondSupport hpsi F H.firstGood b) :
    NoResetSuccess F
      (attemptStepConf hpsi F b (chosenSecondGood hpsi F H b)) := by
  classical
  unfold chosenSecondGood
  rw [dif_pos hsupport]
  exact Classical.choose_spec (H.exists_success b hsupport)

/-- The original three-field residual follows mechanically from the
existential one-step theorem. -/
noncomputable def racePortResidual
    (hpsi : psi > 0) (F : TwoGapFrame n)
    (H : ImmediateSuccessResidual hpsi F) :
    RacePortResidual hpsi F where
  firstGood := H.firstGood
  secondGood := chosenSecondGood hpsi F H
  success := by
    intro b hsupport
    exact chosenSecondGood_success hpsi F H b hsupport

/-- Conditional capstone with the minimum remaining physical statement made
explicit.  An unconditional theorem requires an instance of
`ImmediateSuccessResidual`; none is fabricated here. -/
theorem wired_gapPair_of_immediateSuccess
    (hpsi : psi > 0) (F : TwoGapFrame n)
    (H : ImmediateSuccessResidual hpsi F) :
    WiredResidualGapPair hpsi F
      (physD hpsi F
        (physPortSpec hpsi F (racePortResidual hpsi F H)))
      (ready hpsi F)
      (Rel hpsi F
        (physPortSpec hpsi F (racePortResidual hpsi F H))) := by
  exact wired_gapPair_of_racePort hpsi F (racePortResidual hpsi F H)

end

end LDSinkTwoGapRacePortDischarge

#print axioms LDSinkTwoGapRacePortDischarge.staged_deletes_left
#print axioms LDSinkTwoGapRacePortDischarge.chosenSecondGood_success
#print axioms LDSinkTwoGapRacePortDischarge.wired_gapPair_of_immediateSuccess
