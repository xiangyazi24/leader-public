import Leader.Wu.Birth.FirstBirthCohort
import Leader.Wu.Birth.ShortDoneTerminalCheckInputSources
import Leader.Wu.Birth.ShortDoneTerminalFirstHit
import Leader.Wu.Birth.ShortDoneTerminalFixedSite
import Leader.Wu.Birth.DisposalRouteInvariant
import Leader.Wu.Birth.ReleaseTerminalInvariant
import Leader.Wu.Comparison.HistoryCompare
import Leader.Wu.Birth.ShortDoneTerminalCheckInputNonvacuity
import Leader.Wu.Birth.ShortDoneTerminalCheckInputProducerWitness


namespace BirthPhaseCohortDesign


open PPLL PPLLResearchFormulation
  PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
  PPLLLeaderCreationCleanupRepair PPLLPathStallComparisonRepair
  PPLLComparisonHistory LDSinkBoundedKernel
open BirthSigMoveDisposalRepair
  BirthShortDoneTerminalEntryCut
  BirthShortDoneTerminalBirthSources
  BirthShortDoneTerminalCheckInputSources
  BirthDisposalRouteInvariant BirthReleaseTerminalInvariant


set_option autoImplicit false


variable {n psi kappa tau : Nat}


/-! ## Concrete finite two-birth witness

The witness uses `n = 4`, `psi = 2`, `width = 2`, `kappa = 2`, and `tau = 16`.
Its two physical endpoint records are the tracked current-TerminalHost positive
CHECK input from `BirthShortDoneTerminalCheckInputNonvacuity`; the four-site
configuration contains two disjoint copies of that pair, at edges `0 -> 1` and
`2 -> 3`.  The first row therefore cannot alter the second pair. -/


def secondBirthWitnessRing : DirectedRing 4 := ⟨by decide⟩


/-- Concrete left endpoint record, with `psi = 2`, `kappa = 2`, `tau = 16`. -/
def secondBirthWitnessLeft : ExpiringAgentState 2 2 16 :=
  BirthShortDoneTerminalCheckInputNonvacuity.actualL


/-- Concrete right endpoint record, with `psi = 2`, `kappa = 2`, `tau = 16`. -/
def secondBirthWitnessRight : ExpiringAgentState 2 2 16 :=
  BirthShortDoneTerminalCheckInputNonvacuity.actualR


/-- Two disjoint copies of the concrete positive pair. -/
def secondBirthWitnessConfig (i : Fin 4) : ExpiringAgentState 2 2 16 :=
  if i.val % 2 = 0 then secondBirthWitnessLeft
  else secondBirthWitnessRight


/-- Actual successor after the first scheduled birth edge `0 -> 1`. -/
def secondBirthWitnessAfterFirst : FC 4 2 2 16 :=
  BirthShortDoneTerminalConsumer.step
    (by decide : 0 < 2) (by decide : 0 < 2) (Nat.le_refl 2)
    secondBirthWitnessRing secondBirthWitnessConfig (0 : Fin 4)


private theorem secondBirthWitness_right_zero :
    secondBirthWitnessRing.rightNeighbor (0 : Fin 4) = (1 : Fin 4) := by
  decide


private theorem secondBirthWitness_right_two :
    secondBirthWitnessRing.rightNeighbor (2 : Fin 4) = (3 : Fin 4) := by
  decide


/-! Reduce only the two-bit parity discriminator.  The selected
`ExpiringAgentState` branch is deliberately left opaque. -/


private theorem secondBirthWitness_config_even
    (i : Fin 4) (h : i.val % 2 = 0) :
    secondBirthWitnessConfig i = secondBirthWitnessLeft := by
  simp only [secondBirthWitnessConfig, if_pos h]


private theorem secondBirthWitness_config_odd
    (i : Fin 4) (h : i.val % 2 ≠ 0) :
    secondBirthWitnessConfig i = secondBirthWitnessRight := by
  simp only [secondBirthWitnessConfig, if_neg h]


private theorem secondBirthWitness_config_zero :
    secondBirthWitnessConfig (0 : Fin 4) = secondBirthWitnessLeft := by
  exact secondBirthWitness_config_even (0 : Fin 4) (by decide)


private theorem secondBirthWitness_config_one :
    secondBirthWitnessConfig (1 : Fin 4) = secondBirthWitnessRight := by
  exact secondBirthWitness_config_odd (1 : Fin 4) (by decide)


private theorem secondBirthWitness_config_two :
    secondBirthWitnessConfig (2 : Fin 4) = secondBirthWitnessLeft := by
  exact secondBirthWitness_config_even (2 : Fin 4) (by decide)


private theorem secondBirthWitness_config_three :
    secondBirthWitnessConfig (3 : Fin 4) = secondBirthWitnessRight := by
  exact secondBirthWitness_config_odd (3 : Fin 4) (by decide)


/-! The follower facts are taken from the already-compiled concrete-pair
interface.  Only the one-layer fixture aliases are unfolded. -/


private theorem secondBirthWitness_left_follower :
    secondBirthWitnessLeft.core.core.leader = false := by
  have hp :=
    BirthShortDoneTerminalCheckInputNonvacuity.actual_pair_and_prepared_premises
  simpa only [secondBirthWitnessLeft] using hp.1


private theorem secondBirthWitness_right_follower :
    secondBirthWitnessRight.core.core.leader = false := by
  have hp :=
    BirthShortDoneTerminalCheckInputNonvacuity.actual_pair_and_prepared_premises
  simpa only [secondBirthWitnessRight] using hp.2.1


private theorem secondBirthWitness_pair_followers :
    secondBirthWitnessLeft.core.core.leader = false /\
      secondBirthWitnessRight.core.core.leader = false := by
  exact ⟨secondBirthWitness_left_follower,
    secondBirthWitness_right_follower⟩


/-- Use the already-proved per-edge producer.  In particular this proof does
not reconstruct or evaluate the concrete TerminalHost pre-CHECK cut. -/
private theorem secondBirthWitness_pair_birth :
    BirthShortDoneTerminalObserver.birthEvent
      (by decide : 0 < 2) (by decide : 0 < 2) (Nat.le_refl 2)
      secondBirthWitnessLeft secondBirthWitnessRight = true := by
  simpa only [secondBirthWitnessLeft, secondBirthWitnessRight] using
    BirthShortDoneTerminalCheckInputProducerAudit.actual_pair_birth_through_captured_match_producer


private theorem secondBirthWitness_initial_leaderless :
    BirthShortDoneTerminalFirstHit.Leaderless secondBirthWitnessConfig := by
  intro i
  by_cases h : i.val % 2 = 0
  · simpa only [secondBirthWitnessConfig, if_pos h] using
      secondBirthWitness_left_follower
  · simpa only [secondBirthWitnessConfig, if_neg h] using
      secondBirthWitness_right_follower


private theorem secondBirthWitness_first_event :
    BirthShortDoneTerminalObserver.birthEvent
      (by decide : 0 < 2) (by decide : 0 < 2) (Nat.le_refl 2)
      (secondBirthWitnessConfig (0 : Fin 4))
      (secondBirthWitnessConfig
        (secondBirthWitnessRing.rightNeighbor (0 : Fin 4))) = true := by
  rw [secondBirthWitness_right_zero,
    secondBirthWitness_config_zero, secondBirthWitness_config_one]
  exact secondBirthWitness_pair_birth


private theorem secondBirthWitness_first_birth :
    FirstBirthAt
      (by decide : 0 < 2) (Nat.le_refl 2)
      secondBirthWitnessRing secondBirthWitnessConfig [] (0 : Fin 4) := by
  unfold FirstBirthAt
  constructor
  · trivial
  · dsimp only [run]
    exact secondBirthWitness_first_event


/-! Reduce only the outer population-protocol site selector.  This is the same
proof shape used by the already-compiled `terminal_step_left` and
`terminal_step_right` helpers in `BirthShortDoneTerminalBirthPhysical.lean`.
The TerminalHost row itself is not unfolded. -/


private theorem secondBirthWitness_step_left :
    BirthShortDoneTerminalConsumer.step
      (by decide : 0 < 2) (by decide : 0 < 2) (Nat.le_refl 2)
      secondBirthWitnessRing secondBirthWitnessConfig
      (0 : Fin 4) (0 : Fin 4) =
    (BirthShortDoneTerminalHost.row
      (by decide : 0 < 2) (by decide : 0 < 2) (Nat.le_refl 2)
      (secondBirthWitnessConfig (0 : Fin 4))
      (secondBirthWitnessConfig
        (secondBirthWitnessRing.rightNeighbor (0 : Fin 4)))).1 := by
  simp only [BirthShortDoneTerminalConsumer.step,
    PopulationProtocol.step, BirthShortDoneTerminalConsumer.protocol,
    updatePair, if_true]


private theorem secondBirthWitness_right_zero_ne :
    secondBirthWitnessRing.rightNeighbor (0 : Fin 4) ≠ (0 : Fin 4) := by
  rw [secondBirthWitness_right_zero]
  decide


private theorem secondBirthWitness_step_right :
    BirthShortDoneTerminalConsumer.step
      (by decide : 0 < 2) (by decide : 0 < 2) (Nat.le_refl 2)
      secondBirthWitnessRing secondBirthWitnessConfig
      (0 : Fin 4)
      (secondBirthWitnessRing.rightNeighbor (0 : Fin 4)) =
    (BirthShortDoneTerminalHost.row
      (by decide : 0 < 2) (by decide : 0 < 2) (Nat.le_refl 2)
      (secondBirthWitnessConfig (0 : Fin 4))
      (secondBirthWitnessConfig
        (secondBirthWitnessRing.rightNeighbor (0 : Fin 4)))).2 := by
  simp only [BirthShortDoneTerminalConsumer.step,
    PopulationProtocol.step, BirthShortDoneTerminalConsumer.protocol,
    updatePair, if_neg secondBirthWitness_right_zero_ne, if_true]


private theorem secondBirthWitness_after_first_zero :
    secondBirthWitnessAfterFirst (0 : Fin 4) =
      (BirthShortDoneTerminalHost.row
        (by decide : 0 < 2) (by decide : 0 < 2) (Nat.le_refl 2)
        secondBirthWitnessLeft secondBirthWitnessRight).1 := by
  unfold secondBirthWitnessAfterFirst
  rw [secondBirthWitness_step_left, secondBirthWitness_right_zero,
    secondBirthWitness_config_zero, secondBirthWitness_config_one]


private theorem secondBirthWitness_after_first_one :
    secondBirthWitnessAfterFirst (1 : Fin 4) =
      (BirthShortDoneTerminalHost.row
        (by decide : 0 < 2) (by decide : 0 < 2) (Nat.le_refl 2)
        secondBirthWitnessLeft secondBirthWitnessRight).2 := by
  unfold secondBirthWitnessAfterFirst
  calc
    BirthShortDoneTerminalConsumer.step
        (by decide : 0 < 2) (by decide : 0 < 2) (Nat.le_refl 2)
        secondBirthWitnessRing secondBirthWitnessConfig
        (0 : Fin 4) (1 : Fin 4) =
      BirthShortDoneTerminalConsumer.step
        (by decide : 0 < 2) (by decide : 0 < 2) (Nat.le_refl 2)
        secondBirthWitnessRing secondBirthWitnessConfig
        (0 : Fin 4)
        (secondBirthWitnessRing.rightNeighbor (0 : Fin 4)) := by
          rw [secondBirthWitness_right_zero]
    _ =
      (BirthShortDoneTerminalHost.row
        (by decide : 0 < 2) (by decide : 0 < 2) (Nat.le_refl 2)
        (secondBirthWitnessConfig (0 : Fin 4))
        (secondBirthWitnessConfig
          (secondBirthWitnessRing.rightNeighbor (0 : Fin 4)))).2 :=
      secondBirthWitness_step_right
    _ =
      (BirthShortDoneTerminalHost.row
        (by decide : 0 < 2) (by decide : 0 < 2) (Nat.le_refl 2)
        secondBirthWitnessLeft secondBirthWitnessRight).2 := by
          rw [secondBirthWitness_right_zero,
            secondBirthWitness_config_zero, secondBirthWitness_config_one]


/-- Physical leader existence is obtained from the established event-to-row
interface; the concrete row is never evaluated. -/
private theorem secondBirthWitness_first_row_has_leader :
    (BirthShortDoneTerminalHost.row
      (by decide : 0 < 2) (by decide : 0 < 2) (Nat.le_refl 2)
      secondBirthWitnessLeft secondBirthWitnessRight).1.core.core.leader = true \/
    (BirthShortDoneTerminalHost.row
      (by decide : 0 < 2) (by decide : 0 < 2) (Nat.le_refl 2)
      secondBirthWitnessLeft secondBirthWitnessRight).2.core.core.leader = true := by
  exact
    BirthShortDoneTerminalBirthPhysical.birthEvent_true_row_has_physical_leader
      (by decide : 0 < 2) (by decide : 0 < 2) (Nat.le_refl 2)
      secondBirthWitnessLeft secondBirthWitnessRight
      secondBirthWitness_pair_birth


private theorem secondBirthWitness_after_first_has_leader :
    exists i : Fin 4,
      (secondBirthWitnessAfterFirst i).core.core.leader = true := by
  rcases secondBirthWitness_first_row_has_leader with hL | hR
  · refine ⟨(0 : Fin 4), ?_⟩
    rw [secondBirthWitness_after_first_zero]
    exact hL
  · refine ⟨(1 : Fin 4), ?_⟩
    rw [secondBirthWitness_after_first_one]
    exact hR


/-- Site 2 is untouched by edge 0.  The only reduction after `step_other` is
the tiny fixture lookup `config 2 = actualL`. -/
private theorem secondBirthWitness_after_first_two :
    secondBirthWitnessAfterFirst (2 : Fin 4) = secondBirthWitnessLeft := by
  unfold secondBirthWitnessAfterFirst
  calc
    BirthShortDoneTerminalConsumer.step
        (by decide : 0 < 2) (by decide : 0 < 2) (Nat.le_refl 2)
        secondBirthWitnessRing secondBirthWitnessConfig
        (0 : Fin 4) (2 : Fin 4) =
      secondBirthWitnessConfig (2 : Fin 4) :=
        BirthShortDoneTerminalConsumer.step_other
          (by decide : 0 < 2) (by decide : 0 < 2) (Nat.le_refl 2)
          secondBirthWitnessRing secondBirthWitnessConfig
          (0 : Fin 4) (2 : Fin 4)
          (by decide)
          (by
            rw [secondBirthWitness_right_zero]
            decide)
    _ = secondBirthWitnessLeft := secondBirthWitness_config_two


/-- Site 3 is likewise untouched by edge 0. -/
private theorem secondBirthWitness_after_first_three :
    secondBirthWitnessAfterFirst (3 : Fin 4) = secondBirthWitnessRight := by
  unfold secondBirthWitnessAfterFirst
  calc
    BirthShortDoneTerminalConsumer.step
        (by decide : 0 < 2) (by decide : 0 < 2) (Nat.le_refl 2)
        secondBirthWitnessRing secondBirthWitnessConfig
        (0 : Fin 4) (3 : Fin 4) =
      secondBirthWitnessConfig (3 : Fin 4) :=
        BirthShortDoneTerminalConsumer.step_other
          (by decide : 0 < 2) (by decide : 0 < 2) (Nat.le_refl 2)
          secondBirthWitnessRing secondBirthWitnessConfig
          (0 : Fin 4) (3 : Fin 4)
          (by decide)
          (by
            rw [secondBirthWitness_right_zero]
            decide)
    _ = secondBirthWitnessRight := secondBirthWitness_config_three


private theorem secondBirthWitness_after_first_pair_followers :
    (secondBirthWitnessAfterFirst (2 : Fin 4)).core.core.leader = false /\
      (secondBirthWitnessAfterFirst (3 : Fin 4)).core.core.leader = false := by
  rw [secondBirthWitness_after_first_two,
    secondBirthWitness_after_first_three]
  exact secondBirthWitness_pair_followers


/-- Reuse the same established per-edge birth theorem after the two
`step_other` equalities identify edge 2's pair literally with
`actualL, actualR`. -/
private theorem secondBirthWitness_second_birth :
    BirthShortDoneTerminalObserver.birthEvent
      (by decide : 0 < 2) (by decide : 0 < 2) (Nat.le_refl 2)
      (secondBirthWitnessAfterFirst (2 : Fin 4))
      (secondBirthWitnessAfterFirst
        (secondBirthWitnessRing.rightNeighbor (2 : Fin 4))) = true := by
  rw [secondBirthWitness_right_two,
    secondBirthWitness_after_first_two,
    secondBirthWitness_after_first_three]
  exact secondBirthWitness_pair_birth


private theorem secondBirthWitness_not_quarantined :
    ¬ PostBirthSourceQuarantine
      (by decide : 0 < 2) (Nat.le_refl 2)
      secondBirthWitnessRing secondBirthWitnessConfig (0 : Fin 4) := by
  intro hq
  have hf :=
    postBirthSourceQuarantine_no_birth
      (by decide : 0 < 2) (Nat.le_refl 2)
      secondBirthWitnessRing secondBirthWitnessConfig
      (0 : Fin 4) (2 : Fin 4) hq
  have hf' :
      BirthShortDoneTerminalObserver.birthEvent
        (by decide : 0 < 2) (by decide : 0 < 2) (Nat.le_refl 2)
        (secondBirthWitnessAfterFirst (2 : Fin 4))
        (secondBirthWitnessAfterFirst
          (secondBirthWitnessRing.rightNeighbor (2 : Fin 4))) = false := by
    simpa only [secondBirthWitnessAfterFirst] using hf
  have hbad : true = false :=
    secondBirthWitness_second_birth.symm.trans hf'
  cases hbad


/-- Concrete failure of the unsupported B8 sanitation claim.  The initial
four-site configuration is leaderless.  Edge `0 -> 1` is its first scheduled
birth and produces a physical leader.  Because edge `2 -> 3` is disjoint, its
complete records are unchanged and remain followers; nevertheless its exact
current TerminalHost `birthEvent` is still true.  Hence the actual successor
fails `PostBirthSourceQuarantine`, and a second birth is possible without that
extra premise. -/
theorem second_birth_after_first_without_quarantine :
    BirthShortDoneTerminalFirstHit.Leaderless secondBirthWitnessConfig /\
    FirstBirthAt
      (by decide : 0 < 2) (Nat.le_refl 2)
      secondBirthWitnessRing secondBirthWitnessConfig [] (0 : Fin 4) /\
    (exists i : Fin 4,
      (secondBirthWitnessAfterFirst i).core.core.leader = true) /\
    (0 : Fin 4) ≠ (2 : Fin 4) /\
    ¬ PostBirthSourceQuarantine
      (by decide : 0 < 2) (Nat.le_refl 2)
      secondBirthWitnessRing secondBirthWitnessConfig (0 : Fin 4) /\
    (secondBirthWitnessAfterFirst (2 : Fin 4)).core.core.leader = false /\
    (secondBirthWitnessAfterFirst (3 : Fin 4)).core.core.leader = false /\
    BirthShortDoneTerminalObserver.birthEvent
      (by decide : 0 < 2) (by decide : 0 < 2) (Nat.le_refl 2)
      (secondBirthWitnessAfterFirst (2 : Fin 4))
      (secondBirthWitnessAfterFirst
        (secondBirthWitnessRing.rightNeighbor (2 : Fin 4))) = true := by
  constructor
  · exact secondBirthWitness_initial_leaderless
  constructor
  · exact secondBirthWitness_first_birth
  constructor
  · exact secondBirthWitness_after_first_has_leader
  constructor
  · decide
  constructor
  · exact secondBirthWitness_not_quarantined
  constructor
  · exact secondBirthWitness_after_first_pair_followers.1
  constructor
  · exact secondBirthWitness_after_first_pair_followers.2
  · exact secondBirthWitness_second_birth


end BirthPhaseCohortDesign


#print axioms BirthPhaseCohortDesign.second_birth_after_first_without_quarantine
