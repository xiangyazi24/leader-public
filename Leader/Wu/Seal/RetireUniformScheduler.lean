import Leader.Wu.Scheduler.ClosedDomainAmplification
import Leader.Wu.Seal.RetireRepair

/-!
# Exact iid-scheduler bounds and restart audit for the retire protocol

The deterministic R89 landing theorem gives one favorable word of length at
most `2 * n - 2` from every all-closed start on a nontrivial ring.  Combined
with the exact finite-scheduler counting machinery of R87, this yields an
unconditional one-block failure numerator `n^(2*n-2) - 1`, and hence at least
one stabilizing schedule, for every such start.

Repeated-block amplification does not apply to the reachability closure of
the all-closed class.  On four agents, two disjoint follower/follower births
retire every site while creating two leaders.  The resulting all-retired
configuration is an identity trap, so no bounded restart producer exists on
that closed descendant domain.  The counterexample below records the exact
two-edge trace and its persistent failure of Definition-1 safety.
-/

namespace PPLLCompleteMultiLeaderCleanup
namespace PPartialSealRetireUniformSchedulerSol

open PPLL PPLLResearchFormulation PPLLTraceConvergence
open PPLLSchedulerBlocks
open PPLLClosedDomainSchedulerAmplificationSol
open PPartialMinimalLockRepairSol
open PPartialMinimalLockStaleCounterexampleSol
open PPartialDynamicSweepLockSol
open PPartialDynamicSweepResetSol
open PPartialSealSweepOverlaySol
open PPartialSealSweepZeroLeaderRepairSol

set_option autoImplicit false

variable {n psi kappa tau : Nat}

/-! ## One exact iid block from every all-closed start -/

/-- Classical Boolean view of genuine Definition-1 safety for the retiring
transition.  It is used only for finite schedule counting. -/
noncomputable def sealRetireIsSafeTest
    (ring : DirectedRing n)
    (C : SealSweepConfig n psi kappa tau) : Bool := by
  classical
  exact if PopulationProtocol.IsSafe
      (P_partialSealRetireProtocol psi kappa tau) ring C isLeaderOutput
    then true else false

/-- The Boolean test is equivalent to semantic safety. -/
theorem sealRetireIsSafeTest_spec
    (ring : DirectedRing n)
    (C : SealSweepConfig n psi kappa tau) :
    sealRetireIsSafeTest ring C = true ↔
      PopulationProtocol.IsSafe
        (P_partialSealRetireProtocol psi kappa tau) ring C
        isLeaderOutput := by
  classical
  simp [sealRetireIsSafeTest]

/-- R89 supplies the bounded favorable word required by the exact scheduler
counting theorem, uniformly over all all-closed starts when `n > 1`. -/
theorem allClosedNontrivial_boundedSafeProducer
    (ring : DirectedRing n) (hn : 1 < n) :
    BoundedSafeScheduleProducer ring P_partialSealRetire
      SealSweepAllClosed
      (fun C => PopulationProtocol.IsSafe
        (P_partialSealRetireProtocol psi kappa tau) ring C
        isLeaderOutput)
      (2 * n - 2) := by
  intro C hclosed _hnotSafe
  obtain ⟨word, hlength, _hreach, hsafe⟩ :=
    sealRetire_allClosed_reaches_isSafe_nontrivial
      ring hn C hclosed
  exact ⟨word, hlength, hsafe⟩

/-- Every all-closed `n > 1` start has at most `n^(2*n-2)-1` failing
length-`2*n-2` iid edge schedules. -/
theorem allClosedNontrivial_oneBlockSSLEOn
    (ring : DirectedRing n) (hn : 1 < n) :
    UniformFiniteHorizonSSLEOn
      (P_partialSealRetireProtocol psi kappa tau) ring isLeaderOutput
      SealSweepAllClosed
      (2 * n - 2) (n ^ (2 * n - 2) - 1) := by
  apply uniformFinitePhase_isSafe_to_SSLEOn
  exact boundedSafeProducer_oneBlockPhase
    ring P_partialSealRetire
    SealSweepAllClosed
    (fun C => PopulationProtocol.IsSafe
      (P_partialSealRetireProtocol psi kappa tau) ring C
      isLeaderOutput)
    (sealRetireIsSafeTest ring)
    (sealRetireIsSafeTest_spec ring)
    (2 * n - 2)
    (allClosedNontrivial_boundedSafeProducer ring hn)

/-- Direct one-block failure-numerator form. -/
theorem allClosedNontrivial_oneBlock_failureCount_le
    (ring : DirectedRing n) (hn : 1 < n)
    (C : SealSweepConfig n psi kappa tau)
    (hclosed : SealSweepAllClosed C) :
    (allSchedules n (2 * n - 2)).length -
        stabilizingScheduleCount
          (P_partialSealRetireProtocol psi kappa tau) ring
          isLeaderOutput C (2 * n - 2) ≤
      n ^ (2 * n - 2) - 1 := by
  have hbound :=
    allClosedNontrivial_oneBlockSSLEOn ring hn C hclosed
  omega

/-- Equivalent favorable-count lower bound: at least one exact iid block is
stabilizing from every authorized start. -/
theorem allClosedNontrivial_oneBlock_stabilizingScheduleCount_one_le
    (ring : DirectedRing n) (hn : 1 < n)
    (C : SealSweepConfig n psi kappa tau)
    (hclosed : SealSweepAllClosed C) :
    1 ≤ stabilizingScheduleCount
      (P_partialSealRetireProtocol psi kappa tau) ring
      isLeaderOutput C (2 * n - 2) := by
  have hbound :=
    allClosedNontrivial_oneBlockSSLEOn ring hn C hclosed
  rw [allSchedules_length] at hbound
  have htotal : 0 < n ^ (2 * n - 2) := Nat.pow_pos ring.hn
  omega

/-! ## Reachability closure and the failed restart premise -/

/-- The actual reachability closure of the all-closed initialization class. -/
def SealRetireAllClosedDescendant
    (ring : DirectedRing n)
    (D : SealSweepConfig n psi kappa tau) : Prop :=
  ∃ C : SealSweepConfig n psi kappa tau,
    SealSweepAllClosed C ∧
      PopulationProtocol.Reachable
        (P_partialSealRetireProtocol psi kappa tau) ring C D

/-- Every all-closed start belongs to its descendant domain. -/
theorem allClosed_mem_allClosedDescendant
    (ring : DirectedRing n)
    (C : SealSweepConfig n psi kappa tau)
    (hclosed : SealSweepAllClosed C) :
    SealRetireAllClosedDescendant ring C := by
  exact ⟨C, hclosed,
    @PopulationProtocol.Reachable.refl n
      (P_partialSealRetireProtocol psi kappa tau) ring C⟩

/-- The descendant domain is closed under every retiring interaction. -/
theorem allClosedDescendant_localStepClosed
    (ring : DirectedRing n) :
    LocalStepClosed ring
      (P_partialSealRetire (psi := psi) (kappa := kappa) (tau := tau))
      (SealRetireAllClosedDescendant
        (psi := psi) (kappa := kappa) (tau := tau) ring) := by
  intro D hD e
  obtain ⟨C, hclosed, hreach⟩ := hD
  refine ⟨C, hclosed, hreach.trans ?_⟩
  apply PopulationProtocol.OneStep.to_reachable
  refine ⟨e, ?_⟩
  exact localStep_eq_protocol_step
    (P_partialSealRetireProtocol psi kappa tau) ring D e

/-! ### A two-edge four-agent all-retired bad trace -/

/-- A four-agent ring supporting two disjoint retiring births. -/
abbrev retireRingFour : DirectedRing 4 := ⟨by omega⟩

/-- A closed follower on the accepted factor-four carrier. -/
def retireClosedFollowerState (kappa tau : Nat) :
    SealSweepState StalePsi kappa tau :=
  (clearMinimalLockLeader (staleLeaderPhysical kappa tau, true), true)

/-- The same physical follower after retirement. -/
def retireOpenFollowerState (kappa tau : Nat) :
    SealSweepState StalePsi kappa tau :=
  (clearMinimalLockLeader (staleLeaderPhysical kappa tau, true), false)

/-- The leader born at the left endpoint of a follower/follower retirement. -/
def retireOpenLeaderState (kappa tau : Nat) :
    SealSweepState StalePsi kappa tau :=
  (setMinimalLockLeader
    (clearMinimalLockLeader (staleLeaderPhysical kappa tau, true)), false)

@[simp] theorem retireClosedFollowerState_follower
    (kappa tau : Nat) :
    sweepLockLeader (retireClosedFollowerState kappa tau) = false := by
  rfl

@[simp] theorem retireClosedFollowerState_closed
    (kappa tau : Nat) :
    (retireClosedFollowerState kappa tau).2 = true := by
  rfl

@[simp] theorem retireOpenFollowerState_follower
    (kappa tau : Nat) :
    sweepLockLeader (retireOpenFollowerState kappa tau) = false := by
  rfl

@[simp] theorem retireOpenFollowerState_open
    (kappa tau : Nat) :
    (retireOpenFollowerState kappa tau).2 = false := by
  rfl

@[simp] theorem retireOpenLeaderState_leader
    (kappa tau : Nat) :
    sweepLockLeader (retireOpenLeaderState kappa tau) = true := by
  rfl

@[simp] theorem retireOpenLeaderState_open
    (kappa tau : Nat) :
    (retireOpenLeaderState kappa tau).2 = false := by
  rfl

/-- The concrete closed follower pair takes the new birth branch. -/
theorem retireClosedFollower_pair_birth (kappa tau : Nat) :
    P_partialSealRetire
        (retireClosedFollowerState kappa tau)
        (retireClosedFollowerState kappa tau) =
      (retireOpenLeaderState kappa tau,
        retireOpenFollowerState kappa tau) := by
  exact P_partialSealRetire_birth _ _ rfl rfl rfl rfl

/-- Four identical closed followers. -/
def retireFourClosedFollowers (kappa tau : Nat) :
    SealSweepConfig 4 StalePsi kappa tau :=
  fun _ => retireClosedFollowerState kappa tau

/-- The first disjoint birth is on edge zero. -/
def retireFourAfterFirstBirth (kappa tau : Nat) :
    SealSweepConfig 4 StalePsi kappa tau :=
  localStep retireRingFour P_partialSealRetire
    (retireFourClosedFollowers kappa tau) (0 : Fin 4)

/-- The second disjoint birth is on edge two. -/
def retireFourOpenBad (kappa tau : Nat) :
    SealSweepConfig 4 StalePsi kappa tau :=
  localStep retireRingFour P_partialSealRetire
    (retireFourAfterFirstBirth kappa tau) (2 : Fin 4)

/-- Exact two-edge bad word. -/
def retireFourBadWord : DetSchedule 4 :=
  [(0 : Fin 4), (2 : Fin 4)]

private theorem finFour_cases (i : Fin 4) :
    i = (0 : Fin 4) ∨ i = (1 : Fin 4) ∨
      i = (2 : Fin 4) ∨ i = (3 : Fin 4) := by
  by_cases h0 : i.val = 0
  · left
    exact Fin.ext h0
  by_cases h1 : i.val = 1
  · right
    left
    exact Fin.ext h1
  by_cases h2 : i.val = 2
  · right
    right
    left
    exact Fin.ext h2
  · right
    right
    right
    apply Fin.ext
    omega

@[simp] theorem retireFourBadWord_length :
    retireFourBadWord.length = 2 := by
  rfl

theorem retireFourClosedFollowers_allClosed (kappa tau : Nat) :
    SealSweepAllClosed (retireFourClosedFollowers kappa tau) := by
  intro i
  rfl

theorem retireFourClosedFollowers_not_allOpen (kappa tau : Nat) :
    ¬ SealRetireAllOpen (retireFourClosedFollowers kappa tau) := by
  intro hopen
  have hzero := hopen (0 : Fin 4)
  change true = false at hzero
  contradiction

@[simp] theorem retireFourAfterFirstBirth_zero (kappa tau : Nat) :
    retireFourAfterFirstBirth kappa tau (0 : Fin 4) =
      retireOpenLeaderState kappa tau := by
  change
    (P_partialSealRetire
      (retireClosedFollowerState kappa tau)
      (retireClosedFollowerState kappa tau)).1 = _
  rw [retireClosedFollower_pair_birth]

@[simp] theorem retireFourAfterFirstBirth_one (kappa tau : Nat) :
    retireFourAfterFirstBirth kappa tau (1 : Fin 4) =
      retireOpenFollowerState kappa tau := by
  change
    (P_partialSealRetire
      (retireClosedFollowerState kappa tau)
      (retireClosedFollowerState kappa tau)).2 = _
  rw [retireClosedFollower_pair_birth]

@[simp] theorem retireFourAfterFirstBirth_two (kappa tau : Nat) :
    retireFourAfterFirstBirth kappa tau (2 : Fin 4) =
      retireClosedFollowerState kappa tau := by
  rfl

@[simp] theorem retireFourAfterFirstBirth_three (kappa tau : Nat) :
    retireFourAfterFirstBirth kappa tau (3 : Fin 4) =
      retireClosedFollowerState kappa tau := by
  rfl

/-- After one edge the opposite pair is still closed, so two interactions
are genuinely needed for this trace to enter the all-retired region. -/
theorem retireFourAfterFirstBirth_not_allOpen (kappa tau : Nat) :
    ¬ SealRetireAllOpen (retireFourAfterFirstBirth kappa tau) := by
  intro hopen
  have htwo := hopen (2 : Fin 4)
  simp at htwo

@[simp] theorem retireFourOpenBad_zero (kappa tau : Nat) :
    retireFourOpenBad kappa tau (0 : Fin 4) =
      retireOpenLeaderState kappa tau := by
  rfl

@[simp] theorem retireFourOpenBad_one (kappa tau : Nat) :
    retireFourOpenBad kappa tau (1 : Fin 4) =
      retireOpenFollowerState kappa tau := by
  rfl

@[simp] theorem retireFourOpenBad_two (kappa tau : Nat) :
    retireFourOpenBad kappa tau (2 : Fin 4) =
      retireOpenLeaderState kappa tau := by
  change
    (P_partialSealRetire
      (retireClosedFollowerState kappa tau)
      (retireClosedFollowerState kappa tau)).1 = _
  rw [retireClosedFollower_pair_birth]

@[simp] theorem retireFourOpenBad_three (kappa tau : Nat) :
    retireFourOpenBad kappa tau (3 : Fin 4) =
      retireOpenFollowerState kappa tau := by
  change
    (P_partialSealRetire
      (retireClosedFollowerState kappa tau)
      (retireClosedFollowerState kappa tau)).2 = _
  rw [retireClosedFollower_pair_birth]

/-- Both disjoint births have fired, so every site is retired. -/
theorem retireFourOpenBad_allOpen (kappa tau : Nat) :
    SealRetireAllOpen (retireFourOpenBad kappa tau) := by
  intro i
  rcases finFour_cases i with rfl | rfl | rfl | rfl <;>
    rfl

@[simp] theorem retireFourOpenBad_zero_leader (kappa tau : Nat) :
    sweepLockLeader (retireFourOpenBad kappa tau (0 : Fin 4)) = true := by
  rfl

@[simp] theorem retireFourOpenBad_two_leader (kappa tau : Nat) :
    sweepLockLeader (retireFourOpenBad kappa tau (2 : Fin 4)) = true := by
  rfl

/-- The terminal trace endpoint has two distinct leader outputs. -/
theorem retireFourOpenBad_not_unique (kappa tau : Nat) :
    ¬ UniqueLeaderOutput
      (P_partialSealRetireProtocol StalePsi kappa tau) 4
      (retireFourOpenBad kappa tau) isLeaderOutput := by
  rintro ⟨root, _hroot, honly⟩
  have hzero : isLeaderOutput
      ((P_partialSealRetireProtocol StalePsi kappa tau).output
        (retireFourOpenBad kappa tau (0 : Fin 4))) = true := by
    rw [sealRetire_isLeaderOutput_iff]
    exact retireFourOpenBad_zero_leader kappa tau
  have htwo : isLeaderOutput
      ((P_partialSealRetireProtocol StalePsi kappa tau).output
        (retireFourOpenBad kappa tau (2 : Fin 4))) = true := by
    rw [sealRetire_isLeaderOutput_iff]
    exact retireFourOpenBad_two_leader kappa tau
  have h02 : (0 : Fin 4) = (2 : Fin 4) :=
    (honly 0 hzero).trans (honly 2 htwo).symm
  exact (by decide : (0 : Fin 4) ≠ (2 : Fin 4)) h02

/-- The concrete list executes exactly the two displayed births. -/
theorem retireFourBadWord_run (kappa tau : Nat) :
    runLocalSchedule retireRingFour P_partialSealRetire
        (retireFourClosedFollowers kappa tau) retireFourBadWord =
      retireFourOpenBad kappa tau := by
  rfl

/-- Complete shortest-prefix certificate for the displayed trace: neither
the source nor its one-edge prefix is all retired, while the two-edge endpoint
is all retired and has non-unique output. -/
theorem retireFour_twoEdge_openBad_trace (kappa tau : Nat) :
    retireFourBadWord.length = 2 ∧
      SealSweepAllClosed (retireFourClosedFollowers kappa tau) ∧
      ¬ SealRetireAllOpen (retireFourClosedFollowers kappa tau) ∧
      ¬ SealRetireAllOpen (retireFourAfterFirstBirth kappa tau) ∧
      runLocalSchedule retireRingFour P_partialSealRetire
          (retireFourClosedFollowers kappa tau) retireFourBadWord =
        retireFourOpenBad kappa tau ∧
      SealRetireAllOpen (retireFourOpenBad kappa tau) ∧
      ¬ UniqueLeaderOutput
        (P_partialSealRetireProtocol StalePsi kappa tau) 4
        (retireFourOpenBad kappa tau) isLeaderOutput := by
  exact ⟨retireFourBadWord_length,
    retireFourClosedFollowers_allClosed kappa tau,
    retireFourClosedFollowers_not_allOpen kappa tau,
    retireFourAfterFirstBirth_not_allOpen kappa tau,
    retireFourBadWord_run kappa tau,
    retireFourOpenBad_allOpen kappa tau,
    retireFourOpenBad_not_unique kappa tau⟩

/-- The two-edge bad endpoint is reachable from an authorized all-closed
start. -/
theorem retireFourOpenBad_reachable (kappa tau : Nat) :
    PopulationProtocol.Reachable
      (P_partialSealRetireProtocol StalePsi kappa tau) retireRingFour
      (retireFourClosedFollowers kappa tau)
      (retireFourOpenBad kappa tau) := by
  rw [← retireFourBadWord_run]
  exact P_partialSealRetire_runLocalSchedule_reachable
    retireRingFour (retireFourClosedFollowers kappa tau)
    retireFourBadWord

/-- Consequently the bad endpoint lies in the closed descendant domain. -/
theorem retireFourOpenBad_mem_descendant (kappa tau : Nat) :
    SealRetireAllClosedDescendant retireRingFour
      (retireFourOpenBad kappa tau) := by
  exact ⟨retireFourClosedFollowers kappa tau,
    retireFourClosedFollowers_allClosed kappa tau,
    retireFourOpenBad_reachable kappa tau⟩

/-- Every state reachable from the bad endpoint fails semantic safety. -/
theorem retireFourOpenBad_no_reachable_isSafe
    (kappa tau : Nat)
    (D : SealSweepConfig 4 StalePsi kappa tau)
    (hreach : PopulationProtocol.Reachable
      (P_partialSealRetireProtocol StalePsi kappa tau) retireRingFour
      (retireFourOpenBad kappa tau) D) :
    ¬ PopulationProtocol.IsSafe
      (P_partialSealRetireProtocol StalePsi kappa tau) retireRingFour D
      isLeaderOutput := by
  exact sealRetire_allOpen_no_reachable_isSafe_of_not_unique
    retireRingFour (retireFourOpenBad kappa tau) D
    (retireFourOpenBad_allOpen kappa tau)
    (retireFourOpenBad_not_unique kappa tau) hreach

/-- The exact restartability premise needed by R87 fails on the genuine
reachability closure, for every proposed finite block length. -/
theorem no_allClosedDescendant_boundedSafeProducer_four
    (kappa tau L : Nat) :
    ¬ BoundedSafeScheduleProducer retireRingFour P_partialSealRetire
      (SealRetireAllClosedDescendant retireRingFour)
      (fun C => PopulationProtocol.IsSafe
        (P_partialSealRetireProtocol StalePsi kappa tau) retireRingFour C
        isLeaderOutput)
      L := by
  intro hproducer
  have hnotSafe : ¬ PopulationProtocol.IsSafe
      (P_partialSealRetireProtocol StalePsi kappa tau) retireRingFour
      (retireFourOpenBad kappa tau) isLeaderOutput := by
    exact retireFourOpenBad_no_reachable_isSafe kappa tau
      (retireFourOpenBad kappa tau)
      (@PopulationProtocol.Reachable.refl 4
        (P_partialSealRetireProtocol StalePsi kappa tau)
        retireRingFour (retireFourOpenBad kappa tau))
  obtain ⟨word, _hlength, hsafe⟩ := hproducer
    (retireFourOpenBad kappa tau)
    (retireFourOpenBad_mem_descendant kappa tau)
    hnotSafe
  have hreach := P_partialSealRetire_runLocalSchedule_reachable
    retireRingFour (retireFourOpenBad kappa tau) word
  exact (retireFourOpenBad_no_reachable_isSafe kappa tau
    (runLocalSchedule retireRingFour P_partialSealRetire
      (retireFourOpenBad kappa tau) word) hreach) hsafe

end PPartialSealRetireUniformSchedulerSol
end PPLLCompleteMultiLeaderCleanup
