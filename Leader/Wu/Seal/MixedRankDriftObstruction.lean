import Leader.Wu.Seal.MixedAmplification
import Leader.Wu.Seal.ConcurrentCounterfamily

/-!
# Exact leader monotonicity and the mixed-rank drift obstruction

The R91/R93 deterministic normalizer uses
`sealSweepMixedRank = openLeaderCount * n + openGap`.  That rank is useful for
constructing one favorable word, but it is not a one-step Lyapunov function
for the iid uniform scheduler: an ordinary launch can raise it, and the exact
even counterfamily repeatedly raises it and resets it while preserving the
number of output leaders.

This module isolates the quantity that *is* monotone under every exact R82
interaction.  Output leaders are never created, either locally or along a
reachable execution.  On the positive descendant domain, semantic safety is
therefore equivalent to the total output-leader count being one.  This reduces
the remaining iid complexity problem exactly to a leader-coalescence hitting
time, while the counterfamily below rules out a direct drift proof using the
existing mixed normalization rank.

No claim is made here that the coalescence hitting time is superpolynomial.
The obstruction is deliberately narrower: the current rank can have an
unbounded upward excursion with no decrease in the monotone leader count, and
the excursion/reset cycle is an exact execution of the factor-four overlay.
-/

namespace PPLLCompleteMultiLeaderCleanup
namespace PPartialSealSweepIidDriftObstructionSol

open PPLL PPLLResearchFormulation
open PPLLStaticDoubleCoverNoGo
open PPartialDynamicSweepLockSol
open PPartialSealSweepOverlaySol
open PPartialSealSweepPositiveLandingSol
open PPartialSealSweepUniformSchedulerSol
open PPartialSealSweepMixedNormalizerSol
open PPartialSealSweepIidComplexitySol
open PPartialSealSweepConcurrencyNoGoSol
open PPartialSealSweepConcurrentCounterfamilySol
open SealSweepConcurrentCycleSol
open SealSweepConcurrentCycleSol.SealMacroState
open SealSweepConcurrentCounterfamilySol

set_option autoImplicit false

variable {n psi kappa tau : Nat}

/-! ## Exact output-leader monotonicity -/

/-- The overlay never changes the physical leader bit of the initiator. -/
theorem sealSweep_pair_leftLeader_eq
    (l r : SealSweepState psi kappa tau) :
    sweepLockLeader (P_partialSealSweep l r).1 = sweepLockLeader l := by
  cases hl : sweepLockLeader l <;>
    cases hlc : l.2 <;>
    cases hr : sweepLockLeader r <;>
    cases hrc : r.2
  all_goals
    simp only [sweepLockLeader] at hl hr
    simp [P_partialSealSweep, sweepLockLeader, hl, hlc, hr, hrc]

/-- A responder that is a leader after an overlay interaction was already a
leader before that interaction.  In particular, the overlay has no birth
branch. -/
theorem sealSweep_pair_rightLeader_backward
    (l r : SealSweepState psi kappa tau)
    (hafter : sweepLockLeader (P_partialSealSweep l r).2 = true) :
    sweepLockLeader r = true := by
  cases hl : sweepLockLeader l <;>
    cases hlc : l.2 <;>
    cases hr : sweepLockLeader r <;>
    cases hrc : r.2
  all_goals
    simp only [sweepLockLeader] at hl hr
    simp [P_partialSealSweep, sweepLockLeader, hl, hlc, hr, hrc] at hafter ⊢

/-- Pointwise backward survival of leader output through one exact local
interaction. -/
theorem sealSweep_localStep_leader_backward
    (ring : DirectedRing n)
    (C : SealSweepConfig n psi kappa tau) (e i : Fin n)
    (hafter : sweepLockLeader
      (localStep ring P_partialSealSweep C e i) = true) :
    sweepLockLeader (C i) = true := by
  let j := ring.rightNeighbor e
  by_cases hie : i = e
  · subst i
    have hleft : sweepLockLeader
        (P_partialSealSweep (C e) (C j)).1 = true := by
      simpa [localStep, j] using hafter
    exact (sealSweep_pair_leftLeader_eq (C e) (C j)).symm.trans hleft
  · by_cases hij : i = j
    · subst i
      have hright : sweepLockLeader
          (P_partialSealSweep (C e) (C j)).2 = true := by
        simpa [localStep, j, hie] using hafter
      exact sealSweep_pair_rightLeader_backward (C e) (C j) hright
    · simpa [localStep, j, hie, hij] using hafter

private theorem finBoolCount_mono {m : Nat}
    (before after : Fin m → Bool)
    (hmono : ∀ i : Fin m, after i = true → before i = true) :
    (List.ofFn (fun i => if after i then 1 else 0)).sum ≤
      (List.ofFn (fun i => if before i then 1 else 0)).sum := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [List.ofFn_succ, List.ofFn_succ,
        List.sum_cons, List.sum_cons]
      have htail := ih
        (fun i : Fin m => before i.succ)
        (fun i : Fin m => after i.succ)
        (fun i hi => hmono i.succ hi)
      have hhead : (if after 0 then 1 else 0) ≤
          (if before 0 then 1 else 0) := by
        cases ha : after 0
        · simp
        · have hb := hmono 0 ha
          simp [hb]
      exact Nat.add_le_add hhead htail

/-- The exact output-leader count is nonincreasing under every scheduler
choice. -/
theorem sealSweepLeaderCount_localStep_le
    (ring : DirectedRing n)
    (C : SealSweepConfig n psi kappa tau) (e : Fin n) :
    sealSweepLeaderCount
        (localStep ring P_partialSealSweep C e) ≤
      sealSweepLeaderCount C := by
  unfold sealSweepLeaderCount
  exact finBoolCount_mono
    (fun i => sweepLockLeader (C i))
    (fun i => sweepLockLeader
      (localStep ring P_partialSealSweep C e i))
    (fun i hi => sealSweep_localStep_leader_backward ring C e i hi)

/-- Pointwise leader output can only disappear along an arbitrary reachable
exact execution. -/
theorem sealSweep_reachable_leader_backward
    (ring : DirectedRing n)
    {C D : SealSweepConfig n psi kappa tau}
    (hreach : PopulationProtocol.Reachable
      (P_partialSealSweepProtocol psi kappa tau) ring C D)
    (i : Fin n)
    (hafter : sweepLockLeader (D i) = true) :
    sweepLockLeader (C i) = true := by
  let SurvivesBackward : SealSweepConfig n psi kappa tau → Prop :=
    fun X => ∀ j : Fin n, sweepLockLeader (X j) = true →
      sweepLockLeader (C j) = true
  have hclosed : PopulationProtocol.ClosedPred
      (P_partialSealSweepProtocol psi kappa tau) ring
      SurvivesBackward := by
    intro X hX Y hstep
    obtain ⟨e, rfl⟩ := hstep
    intro j hj
    apply hX j
    exact sealSweep_localStep_leader_backward ring X e j hj
  have hC : SurvivesBackward C := by
    intro j hj
    exact hj
  exact (hclosed.reachable hC hreach) i hafter

/-- Consequently the exact output-leader count is nonincreasing along every
reachable execution. -/
theorem sealSweepLeaderCount_reachable_le
    (ring : DirectedRing n)
    {C D : SealSweepConfig n psi kappa tau}
    (hreach : PopulationProtocol.Reachable
      (P_partialSealSweepProtocol psi kappa tau) ring C D) :
    sealSweepLeaderCount D ≤ sealSweepLeaderCount C := by
  unfold sealSweepLeaderCount
  exact finBoolCount_mono
    (fun i => sweepLockLeader (C i))
    (fun i => sweepLockLeader (D i))
    (fun i hi => sealSweep_reachable_leader_backward ring hreach i hi)

/-! ## Safety is exactly coalescence to one leader -/

private theorem sealSweep_output_eq_of_leader_eq
    (u v : SealSweepState psi kappa tau)
    (h : sweepLockLeader u = sweepLockLeader v) :
    (P_partialSealSweepProtocol psi kappa tau).output u =
      (P_partialSealSweepProtocol psi kappa tau).output v := by
  change (if sweepLockLeader u then LeaderOutput.leader
      else LeaderOutput.follower) =
    (if sweepLockLeader v then LeaderOutput.leader
      else LeaderOutput.follower)
  rw [h]

/-- On the positive reachable domain, count one already implies genuine
Definition-1 safety.  The proof does not use the deterministic normalizer:
future positivity supplies a surviving leader, while pointwise backward
survival prevents that leader from moving to a new site. -/
theorem positiveDescendant_leaderCount_one_isSafe
    (ring : DirectedRing n)
    (C : SealSweepConfig n psi kappa tau)
    (hdesc : SealSweepPositiveDescendant ring C)
    (hone : sealSweepLeaderCount C = 1) :
    PopulationProtocol.IsSafe
      (P_partialSealSweepProtocol psi kappa tau) ring C
      isLeaderOutput := by
  have hCunique : UniqueLeaderOutput
      (P_partialSealSweepProtocol psi kappa tau) n C isLeaderOutput :=
    (sealSweep_unique_iff_leaderCount_eq_one C).2 hone
  refine ⟨hCunique, ?_⟩
  intro D hreach i
  obtain ⟨source, hsource, hsourceC⟩ := hdesc
  have hdescD : SealSweepPositiveDescendant ring D :=
    ⟨source, hsource, hsourceC.trans hreach⟩
  have hDhasLeader : SealSweepHasLeader D :=
    (positiveDescendant_balanced_hasLeader ring D hdescD).2
  have hDpositive : 0 < sealSweepLeaderCount D :=
    (sealSweep_hasLeader_iff_leaderCount_pos D).1 hDhasLeader
  have hDle : sealSweepLeaderCount D ≤ sealSweepLeaderCount C :=
    sealSweepLeaderCount_reachable_le ring hreach
  have hDone : sealSweepLeaderCount D = 1 := by omega
  have hDunique : UniqueLeaderOutput
      (P_partialSealSweepProtocol psi kappa tau) n D isLeaderOutput :=
    (sealSweep_unique_iff_leaderCount_eq_one D).2 hDone
  have hleaderEq : sweepLockLeader (D i) = sweepLockLeader (C i) := by
    cases hCi : sweepLockLeader (C i) with
    | false =>
        cases hDi : sweepLockLeader (D i) with
        | false => rfl
        | true =>
            have hback := sealSweep_reachable_leader_backward
              ring hreach i hDi
            rw [hCi] at hback
            contradiction
    | true =>
        cases hDi : sweepLockLeader (D i) with
        | true => rfl
        | false =>
            obtain ⟨root, hrootOut, honlyD⟩ := hDunique
            have hrootD : sweepLockLeader (D root) = true :=
              (sealSweep_isLeaderOutput_iff (D root)).1 hrootOut
            have hrootC : sweepLockLeader (C root) = true :=
              sealSweep_reachable_leader_backward ring hreach root hrootD
            obtain ⟨croot, hcrootOut, honlyC⟩ := hCunique
            have hiOut : isLeaderOutput
                ((P_partialSealSweepProtocol psi kappa tau).output (C i)) =
                true :=
              (sealSweep_isLeaderOutput_iff (C i)).2 hCi
            have hrootOutC : isLeaderOutput
                ((P_partialSealSweepProtocol psi kappa tau).output (C root)) =
                true :=
              (sealSweep_isLeaderOutput_iff (C root)).2 hrootC
            have hiEq : i = croot := honlyC i hiOut
            have hrootEq : root = croot := honlyC root hrootOutC
            have hir : i = root := hiEq.trans hrootEq.symm
            have hDiTrue : sweepLockLeader (D i) = true := by
              rw [hir]
              exact hrootD
            rw [hDi] at hDiTrue
            contradiction
  exact sealSweep_output_eq_of_leader_eq (D i) (C i) hleaderEq

/-- Exact reduction of semantic safety to the monotone coalescence target on
`SealSweepPositiveDescendant`. -/
theorem positiveDescendant_isSafe_iff_leaderCount_eq_one
    (ring : DirectedRing n)
    (C : SealSweepConfig n psi kappa tau)
    (hdesc : SealSweepPositiveDescendant ring C) :
    PopulationProtocol.IsSafe
        (P_partialSealSweepProtocol psi kappa tau) ring C
        isLeaderOutput ↔
      sealSweepLeaderCount C = 1 := by
  constructor
  · intro hsafe
    exact (sealSweep_unique_iff_leaderCount_eq_one C).1 hsafe.1
  · exact positiveDescendant_leaderCount_one_isSafe ring C hdesc

/-! ## The current mixed rank has exact unbounded excursions -/

/-- Every all-closed configuration has mixed normalization rank zero. -/
theorem sealSweepMixedRank_eq_zero_of_allClosed
    (ring : DirectedRing n)
    (C : SealSweepConfig n psi kappa tau)
    (hclosed : SealSweepAllClosed C) :
    sealSweepMixedRank ring C = 0 := by
  have hcount : sealSweepOpenLeaderCount C = 0 := by
    apply Nat.eq_zero_of_not_pos
    intro hpos
    obtain ⟨i, hiLeader, hiOpen⟩ :=
      (openLeaderCount_pos_iff C).1 hpos
    rw [hclosed i] at hiOpen
    contradiction
  have hnone : ¬ ∃ d, SealSweepOpenGapWitness ring C d := by
    rintro ⟨d, probe, anchor, hprobeLeader, hprobeOpen,
      hanchorLeader, hanchorOpen, hdpos, hdlt, hcw⟩
    rw [hclosed probe] at hprobeOpen
    contradiction
  have hgap : sealSweepOpenGap ring C = 0 := by
    classical
    simp [sealSweepOpenGap, hnone]
  unfold sealSweepMixedRank
  rw [hcount, hgap]
  simp

/-- In every balanced genuinely mixed state the rank is already larger than
the population size.  This lower bound is enough to expose an unbounded launch
excursion; no exact evaluation of the noncomputable minimum is needed. -/
theorem sealSweepMixedRank_gt_population_of_balanced_not_allClosed
    (ring : DirectedRing n)
    (C : SealSweepConfig n psi kappa tau)
    (hbalanced : SealSweepOpenBalanced C)
    (hnotClosed : ¬ SealSweepAllClosed C) :
    n < sealSweepMixedRank ring C := by
  have hcount :=
    (balanced_not_allClosed_openCounts_pos C hbalanced hnotClosed).1
  have hgap :=
    (sealSweepOpenGap_pos_lt ring C hbalanced hnotClosed).1
  have hmul : n ≤ sealSweepOpenLeaderCount C * n := by
    have hone : 1 ≤ sealSweepOpenLeaderCount C := by omega
    simpa using Nat.mul_le_mul_right n hone
  unfold sealSweepMixedRank
  omega

/-- Exact all-open midpoint of the even activation/closure cycle. -/
def exactAlternatingOpen (m kappa tau : Nat) :
    (P_partialSealSweepProtocol OverlayNoGoPsi kappa tau).Configuration
      (2 * m) :=
  liftMacroConfig kappa tau (alternatingUnsealed m)

theorem exactAlternatingOpen_not_allClosed
    (m : Nat) (hm : 0 < m) (kappa tau : Nat) :
    ¬ SealSweepAllClosed (exactAlternatingOpen m kappa tau) := by
  intro hclosed
  let i : Fin (2 * m) := ⟨0, by omega⟩
  have hi := hclosed i
  change (embedSealMacro kappa tau (alternatingUnsealed m i)).2 = true at hi
  rw [embedSealMacro_closed, alternatingUnsealed_pointwise] at hi
  simp [i, sealMacroSealed] at hi

theorem exactAlternatingClosed_positive
    (m : Nat) (hm : 0 < m) (kappa tau : Nat) :
    SealSweepAllClosedPositive (exactAlternatingClosed m kappa tau) := by
  refine ⟨exactAlternatingClosed_allClosed m kappa tau, ?_⟩
  apply (sealSweep_hasLeader_iff_leaderCount_pos _).1
  let i : Fin (2 * m) := ⟨0, by omega⟩
  refine ⟨i, ?_⟩
  rw [exactAlternatingClosed_pointwise]
  simp [i, exactLS]

/-- The first half of the exact period reaches the all-open midpoint. -/
theorem exact_run_evenWord_eq_open
    (m : Nat) (hm : 0 < m) (kappa tau : Nat) :
    runSchedule (P_partialSealSweepProtocol OverlayNoGoPsi kappa tau)
        (evenRing m hm) (exactAlternatingClosed m kappa tau)
        (evenWord m) =
      exactAlternatingOpen m kappa tau := by
  change runSchedule (P_partialSealSweepProtocol OverlayNoGoPsi kappa tau)
      (evenRing m hm) (liftMacroConfig kappa tau (alternatingSealed m))
      (evenWord m) =
    liftMacroConfig kappa tau (alternatingUnsealed m)
  calc
    _ = liftMacroConfig kappa tau
        (runSchedule sealMacroProtocol (evenRing m hm)
          (alternatingSealed m) (evenWord m)) :=
      liftMacroConfig_runSchedule kappa tau (evenRing m hm)
        (alternatingSealed m) (evenWord m)
    _ = _ := congrArg (liftMacroConfig kappa tau)
      (run_evenPrefixWord m m hm (by omega))

/-- The second half of the exact period resets the all-open midpoint to the
all-closed source. -/
theorem exact_run_oddWord_eq_closed
    (m : Nat) (hm : 0 < m) (kappa tau : Nat) :
    runSchedule (P_partialSealSweepProtocol OverlayNoGoPsi kappa tau)
        (evenRing m hm) (exactAlternatingOpen m kappa tau)
        (oddWord m) =
      exactAlternatingClosed m kappa tau := by
  change runSchedule (P_partialSealSweepProtocol OverlayNoGoPsi kappa tau)
      (evenRing m hm) (liftMacroConfig kappa tau (alternatingUnsealed m))
      (oddWord m) =
    liftMacroConfig kappa tau (alternatingSealed m)
  rw [liftMacroConfig_runSchedule]
  rw [show runSchedule sealMacroProtocol (evenRing m hm)
      (alternatingUnsealed m) (oddWord m) = closureConfig m m by
        exact run_oddPrefixWord m m hm (by omega)]
  rw [closureConfig_full_eq_sealed]

private theorem sealSweep_runSchedule_append
    {q : Nat} (P : PopulationProtocol) (ring : DirectedRing q)
    (C : P.Configuration q) (xs ys : List (Fin q)) :
    runSchedule P ring C (xs ++ ys) =
      runSchedule P ring (runSchedule P ring C xs) ys := by
  induction xs generalizing C with
  | nil => rfl
  | cons e rest ih =>
      simp only [List.cons_append, runSchedule]
      exact ih (P.step ring C e)

/-- One complete exact overlay period returns to the same positive all-closed
configuration. -/
theorem exact_run_evenPeriodWord_eq_closed
    (m : Nat) (hm : 0 < m) (kappa tau : Nat) :
    runSchedule (P_partialSealSweepProtocol OverlayNoGoPsi kappa tau)
        (evenRing m hm) (exactAlternatingClosed m kappa tau)
        (evenPeriodWord m) =
      exactAlternatingClosed m kappa tau := by
  rw [evenPeriodWord, sealSweep_runSchedule_append]
  rw [exact_run_evenWord_eq_open m hm kappa tau]
  exact exact_run_oddWord_eq_closed m hm kappa tau

/-- `cycles` copies of the exact period.  This is an actual word in the iid
uniform scheduler's finite sample space, rather than an abstract reachability
witness. -/
def exactRepeatedPeriodWord (m : Nat) : Nat → List (Fin (2 * m))
  | 0 => []
  | cycles + 1 =>
      exactRepeatedPeriodWord m cycles ++ evenPeriodWord m

theorem exactRepeatedPeriodWord_length (m cycles : Nat) :
    (exactRepeatedPeriodWord m cycles).length = cycles * (2 * m) := by
  induction cycles with
  | zero => simp [exactRepeatedPeriodWord]
  | succ cycles ih =>
      simp [exactRepeatedPeriodWord, ih, evenPeriodWord_length,
        Nat.succ_mul]

theorem exactRepeatedPeriodWord_mem_allSchedules
    (m cycles : Nat) :
    exactRepeatedPeriodWord m cycles ∈
      allSchedules (2 * m) (cycles * (2 * m)) := by
  exact mem_allSchedules_of_length
    (2 * m) (cycles * (2 * m)) (exactRepeatedPeriodWord m cycles)
    (exactRepeatedPeriodWord_length m cycles)

/-- The reset is repeatable an arbitrary prescribed number of times. -/
theorem exact_run_repeatedPeriodWord_eq_closed
    (m cycles : Nat) (hm : 0 < m) (kappa tau : Nat) :
    runSchedule (P_partialSealSweepProtocol OverlayNoGoPsi kappa tau)
        (evenRing m hm) (exactAlternatingClosed m kappa tau)
        (exactRepeatedPeriodWord m cycles) =
      exactAlternatingClosed m kappa tau := by
  induction cycles with
  | zero => rfl
  | succ cycles ih =>
      rw [exactRepeatedPeriodWord, sealSweep_runSchedule_append]
      rw [ih]
      exact exact_run_evenPeriodWord_eq_closed m hm kappa tau

/-- After any prescribed number of complete resets, the next even half-period
again reaches the same high-rank all-open midpoint. -/
theorem exact_run_repeatedPeriods_then_even_eq_open
    (m cycles : Nat) (hm : 0 < m) (kappa tau : Nat) :
    runSchedule (P_partialSealSweepProtocol OverlayNoGoPsi kappa tau)
        (evenRing m hm) (exactAlternatingClosed m kappa tau)
        (exactRepeatedPeriodWord m cycles ++ evenWord m) =
      exactAlternatingOpen m kappa tau := by
  rw [sealSweep_runSchedule_append]
  rw [exact_run_repeatedPeriodWord_eq_closed m cycles hm kappa tau]
  exact exact_run_evenWord_eq_open m hm kappa tau

/-- The all-open midpoint is an actual positive descendant. -/
theorem exactAlternatingOpen_positiveDescendant
    (m : Nat) (hm : 0 < m) (kappa tau : Nat) :
    SealSweepPositiveDescendant (evenRing m hm)
      (exactAlternatingOpen m kappa tau) := by
  refine ⟨exactAlternatingClosed m kappa tau,
    exactAlternatingClosed_positive m hm kappa tau, ?_⟩
  have hreach := runSchedule_reachable
    (P_partialSealSweepProtocol OverlayNoGoPsi kappa tau)
    (evenRing m hm) (exactAlternatingClosed m kappa tau) (evenWord m)
  rw [exact_run_evenWord_eq_open m hm kappa tau] at hreach
  exact hreach

/-- The complete exact cycle preserves the output-leader count, even though
the mixed rank makes a large excursion. -/
theorem exactAlternatingOpen_leaderCount_eq_closed
    (m : Nat) (hm : 0 < m) (kappa tau : Nat) :
    sealSweepLeaderCount (exactAlternatingOpen m kappa tau) =
      sealSweepLeaderCount (exactAlternatingClosed m kappa tau) := by
  have hforward : PopulationProtocol.Reachable
      (P_partialSealSweepProtocol OverlayNoGoPsi kappa tau)
      (evenRing m hm) (exactAlternatingClosed m kappa tau)
      (exactAlternatingOpen m kappa tau) := by
    have hreach := runSchedule_reachable
      (P_partialSealSweepProtocol OverlayNoGoPsi kappa tau)
      (evenRing m hm) (exactAlternatingClosed m kappa tau) (evenWord m)
    rw [exact_run_evenWord_eq_open m hm kappa tau] at hreach
    exact hreach
  have hbackward : PopulationProtocol.Reachable
      (P_partialSealSweepProtocol OverlayNoGoPsi kappa tau)
      (evenRing m hm) (exactAlternatingOpen m kappa tau)
      (exactAlternatingClosed m kappa tau) := by
    have hreach := runSchedule_reachable
      (P_partialSealSweepProtocol OverlayNoGoPsi kappa tau)
      (evenRing m hm) (exactAlternatingOpen m kappa tau) (oddWord m)
    rw [exact_run_oddWord_eq_closed m hm kappa tau] at hreach
    exact hreach
  have hle := sealSweepLeaderCount_reachable_le
    (evenRing m hm) hforward
  have hge := sealSweepLeaderCount_reachable_le
    (evenRing m hm) hbackward
  omega

/-- Exact scalable rank excursion/reset obstruction.  For every even size
`2*m`, the all-closed positive source has rank zero; after the first half of
the accepted periodic word the rank is larger than `2*m`, although the leader
count is unchanged; the second half resets exactly to the source. -/
theorem exact_even_rank_excursion_and_reset
    (m : Nat) (hm : 2 ≤ m) (kappa tau : Nat) :
    let ring := evenRing m (by omega)
    let C := exactAlternatingClosed m kappa tau
    let D := exactAlternatingOpen m kappa tau
    SealSweepPositiveDescendant ring D ∧
      ¬ PopulationProtocol.IsSafe
        (P_partialSealSweepProtocol OverlayNoGoPsi kappa tau)
        ring D isLeaderOutput ∧
      sealSweepLeaderCount D = sealSweepLeaderCount C ∧
      sealSweepMixedRank ring C = 0 ∧
      2 * m < sealSweepMixedRank ring D ∧
      runSchedule (P_partialSealSweepProtocol OverlayNoGoPsi kappa tau)
        ring C (evenWord m) = D ∧
      runSchedule (P_partialSealSweepProtocol OverlayNoGoPsi kappa tau)
        ring D (oddWord m) = C := by
  dsimp only
  have hmpos : 0 < m := by omega
  have hdesc := exactAlternatingOpen_positiveDescendant
    m hmpos kappa tau
  have hbalanced :=
    (positiveDescendant_balanced_hasLeader
      (evenRing m hmpos) (exactAlternatingOpen m kappa tau) hdesc).1
  have hnotClosed := exactAlternatingOpen_not_allClosed
    m hmpos kappa tau
  refine ⟨hdesc, ?_,
    exactAlternatingOpen_leaderCount_eq_closed m hmpos kappa tau,
    sealSweepMixedRank_eq_zero_of_allClosed
      (evenRing m hmpos) (exactAlternatingClosed m kappa tau)
      (exactAlternatingClosed_allClosed m kappa tau),
    sealSweepMixedRank_gt_population_of_balanced_not_allClosed
      (evenRing m hmpos) (exactAlternatingOpen m kappa tau)
      hbalanced hnotClosed,
    exact_run_evenWord_eq_open m hmpos kappa tau,
    exact_run_oddWord_eq_closed m hmpos kappa tau⟩
  intro hsafe
  have hmacro : EvenHasTwoLeaders m (alternatingUnsealed m) := by
    simpa [alternatingUnsealed] using activationConfig_hasTwo m m hm
  have htwo := liftMacroConfig_hasTwo kappa tau m hmacro
  exact (hasTwoLeaders_not_unique
    (P_partialSealSweepProtocol OverlayNoGoPsi kappa tau)
    isLeaderOutput htwo) hsafe.1

end PPartialSealSweepIidDriftObstructionSol
end PPLLCompleteMultiLeaderCleanup
