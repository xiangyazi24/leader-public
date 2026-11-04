import Leader.Wu.WallSweep.PreCheckNoFire
import Leader.Wu.Birth.PpsiLeaderCreationRepair

/-!
# Concrete clockwise retry attempts

This module lifts the exact two-endpoint no-fire contract to the finite ring.
Before the wrap, every source-covered interaction preserves the unique
unshielded label-zero leader and the retry boundary.  The local pointwise
frame is the bridge used by both clean-prefix propagation and canonical
first-blocker rank descent.
-/

namespace PPLLWallSweepClockwiseAttempt

open PPLL PPLLResearchFormulation PPLLExpiringComparisonRepair
  PPLLAuthorizedComparisonRepair
  PPLLWallSweepRepair PPLLWallSweepSchedule
  PPLLWallSweepFiniteCleanup PPLLWallSweepPreCheckResetRepair
  PPLLWallSweepPreCheckResetContracts PPLLWallSweepEchoRank
  PPLLWallSweepClockwiseScheduler PPLLWallSweepUnshieldedRetry
  PPLLWallSweepRestartableGeneric
  PPLLWallSweepPreCheckNoFire PPLLNoCheckBirthConditionTwoGeometry
  PPLLNoCheckBirthConditionTwoKernel PPLLLeaderCreationCleanupRepair
  PPLLPpsiLeaderCreationSchedule
  PPLLNoCheckBirthPhysicalConditionOne
  PPLLWriteSeqRelocation PPLLWriteSeqPersistenceRegression
  PPLLWallSweepNormalResetContract

variable {n psi kappa tau : Nat}

/-- The moving reset source at a physical prefix: initially it is the
designated leader, and afterwards it is the current clockwise frontier. -/
def ClockwiseSourceAt
    (ring : DirectedRing n) (leader : Fin n)
    (C : EConfig n psi kappa tau) (steps : Nat) : Prop :=
  (steps = 0 ∧ (C leader).core.erase.core.leader = true) ∨
    (0 < steps ∧
      (C (groupOffset ring leader steps)).core.erase.core.reset_cmd = true)

/-- Comparison neutrality is required only on the prefix already visited by
the moving reset; echoes behind this frontier remain unrestricted. -/
def VisitedPrefixNeutral
    (ring : DirectedRing n) (leader : Fin n)
    (C : EConfig n psi kappa tau) (steps : Nat) : Prop :=
  ∀ k, k ≤ steps → 0 < steps →
    ComparisonNeutral
      (C (groupOffset ring leader k)).core.erase.core

/-- Strictly ahead vertices retain their complete initial state.  This is the
source of the next responder's original echo bit in a failed attempt. -/
def UntouchedAhead
    (ring : DirectedRing n) (leader : Fin n)
    (base current : EConfig n psi kappa tau) (steps : Nat) : Prop :=
  ∀ k, steps < k → k < n →
    current (groupOffset ring leader k) =
      base (groupOffset ring leader k)

private theorem groupOffset_zero_eq
    (ring : DirectedRing n) (leader : Fin n) :
    groupOffset ring leader 0 = leader := by
  apply Fin.ext
  simp [groupOffset, Nat.mod_eq_of_lt leader.isLt]

private theorem deletionActive_false_of_neutral
    (u : ExpiringAgentState psi kappa tau)
    (h : ComparisonNeutral u.core.erase.core) :
    deletionActive u.core.erase = false := by
  simp [deletionActive, pathPresent, h.1, h.2.1]

/-- Equality of the active pair lifts to equality of the complete local
configuration step. -/
private theorem localStep_eq_of_pair_eq
    {Q : Type} (ring : DirectedRing n) (T U : Q → Q → Q × Q)
    (C : Fin n → Q) (e : Fin n)
    (hpair : T (C e) (C (ring.rightNeighbor e)) =
      U (C e) (C (ring.rightNeighbor e))) :
    localStep ring T C e = localStep ring U C e := by
  funext i
  simp [localStep, hpair]

/-- Repeating one edge twice leaves every site outside that edge exactly
unchanged. -/
private theorem runLocalSchedule_two_same_off_edge
    {Q : Type} (ring : DirectedRing n) (T : Q → Q → Q × Q)
    (C : Fin n → Q) (e i : Fin n)
    (hie : i ≠ e) (hij : i ≠ ring.rightNeighbor e) :
    runLocalSchedule ring T C [e, e] i = C i := by
  simp [runLocalSchedule, localStep, hie, hij]

/-! ## Pointwise lifting of one non-wrap source step -/

/-- A complete global frame for one non-wrap source-covered interaction.
Pointwise field equalities preserve exact leader uniqueness and stable labels;
the endpoint reset equation distinguishes advance from blocker collision. -/
structure ClockwiseSourceStepFrame
    (hpsi : psi > 0) (ring : DirectedRing n) (leader : Fin n)
    (C D : EConfig n psi kappa tau) (steps : Nat) : Prop where
  ready : ClockwiseRetryReady hpsi ring leader D
  leader_eq : ∀ i, (D i).core.erase.core.leader =
    (C i).core.erase.core.leader
  label_eq : ∀ i, (D i).core.erase.core.label =
    (C i).core.erase.core.label
  shield_eq : ∀ i, (D i).core.erase.core.shield =
    (C i).core.erase.core.shield
  bullets_zero : ∀ i,
    (D i).core.erase.core.bullet = ⟨0, by omega⟩
  off_edge : ∀ i,
    i ≠ groupOffset ring leader steps →
    i ≠ groupOffset ring leader (steps + 1) → D i = C i
  left_neutral : ComparisonNeutral
    (D (groupOffset ring leader steps)).core.erase.core
  right_neutral : ComparisonNeutral
    (D (groupOffset ring leader (steps + 1))).core.erase.core
  left_signal_eq :
    (D (groupOffset ring leader steps)).core.erase.core.signal_B =
      (C (groupOffset ring leader steps)).core.erase.core.signal_B
  right_signal_one_of_source :
    ((C (groupOffset ring leader steps)).core.erase.core.leader = true ∨
      (C (groupOffset ring leader steps)).core.erase.core.signal_B =
        ⟨1, by omega⟩) →
      (D (groupOffset ring leader (steps + 1))).core.erase.core.signal_B =
        ⟨1, by omega⟩
  left_reset_false :
    (D (groupOffset ring leader steps)).core.erase.core.reset_cmd = false
  right_reset_exact :
    (D (groupOffset ring leader (steps + 1))).core.erase.core.reset_cmd =
      !(C (groupOffset ring leader (steps + 1))).core.erase.core.echo
  right_echo_false :
    (D (groupOffset ring leader (steps + 1))).core.erase.core.echo = false
  left_echo_exact :
    (D (groupOffset ring leader steps)).core.erase.core.echo =
      if (C (groupOffset ring leader steps)).core.erase.core.leader = true
      then false
      else if
        (C (groupOffset ring leader (steps + 1))).core.erase.core.label =
          ⟨psi - 1, by omega⟩
      then true
      else (C (groupOffset ring leader steps)).core.erase.core.echo

/-- Rooted counterpart of the non-wrap source frame.  It retains the paper's
`noFreeBarrier` geometry instead of adding the false all-edge cyclic-label
premise at the predecessor-to-leader closing edge. -/
structure RootedClockwiseSourceStepFrame
    (hpsi : psi > 0) (ring : DirectedRing n) (leader : Fin n)
    (C D : EConfig n psi kappa tau) (steps : Nat) : Prop where
  ready : RootedClockwiseRetryReady hpsi ring leader D
  leader_eq : ∀ i, (D i).core.erase.core.leader =
    (C i).core.erase.core.leader
  label_eq : ∀ i, (D i).core.erase.core.label =
    (C i).core.erase.core.label
  shield_eq : ∀ i, (D i).core.erase.core.shield =
    (C i).core.erase.core.shield
  bullets_zero : ∀ i,
    (D i).core.erase.core.bullet = ⟨0, by omega⟩
  off_edge : ∀ i,
    i ≠ groupOffset ring leader steps →
    i ≠ groupOffset ring leader (steps + 1) → D i = C i
  left_neutral : ComparisonNeutral
    (D (groupOffset ring leader steps)).core.erase.core
  right_neutral : ComparisonNeutral
    (D (groupOffset ring leader (steps + 1))).core.erase.core
  left_signal_eq :
    (D (groupOffset ring leader steps)).core.erase.core.signal_B =
      (C (groupOffset ring leader steps)).core.erase.core.signal_B
  right_signal_one_of_source :
    ((C (groupOffset ring leader steps)).core.erase.core.leader = true ∨
      (C (groupOffset ring leader steps)).core.erase.core.signal_B =
        ⟨1, by omega⟩) →
      (D (groupOffset ring leader (steps + 1))).core.erase.core.signal_B =
        ⟨1, by omega⟩
  left_reset_false :
    (D (groupOffset ring leader steps)).core.erase.core.reset_cmd = false
  right_reset_exact :
    (D (groupOffset ring leader (steps + 1))).core.erase.core.reset_cmd =
      !(C (groupOffset ring leader (steps + 1))).core.erase.core.echo
  right_echo_false :
    (D (groupOffset ring leader (steps + 1))).core.erase.core.echo = false
  left_echo_exact :
    (D (groupOffset ring leader steps)).core.erase.core.echo =
      if (C (groupOffset ring leader steps)).core.erase.core.leader = true
      then false
      else if
        (C (groupOffset ring leader (steps + 1))).core.erase.core.label =
          ⟨psi - 1, by omega⟩
      then true
      else (C (groupOffset ring leader steps)).core.erase.core.echo

/-- A false responder echo advances the reset to that responder. -/
theorem ClockwiseSourceStepFrame.right_reset_true_of_echo_false
    {hpsi : psi > 0} {ring : DirectedRing n} {leader : Fin n}
    {C D : EConfig n psi kappa tau} {steps : Nat}
    (h : ClockwiseSourceStepFrame hpsi ring leader C D steps)
    (hecho :
      (C (groupOffset ring leader (steps + 1))).core.erase.core.echo =
        false) :
    (D (groupOffset ring leader (steps + 1))).core.erase.core.reset_cmd =
      true := by
  simpa [hecho] using h.right_reset_exact

/-- A true responder echo consumes the reset at the canonical blocker. -/
theorem ClockwiseSourceStepFrame.right_reset_false_of_echo_true
    {hpsi : psi > 0} {ring : DirectedRing n} {leader : Fin n}
    {C D : EConfig n psi kappa tau} {steps : Nat}
    (h : ClockwiseSourceStepFrame hpsi ring leader C D steps)
    (hecho :
      (C (groupOffset ring leader (steps + 1))).core.erase.core.echo =
        true) :
    (D (groupOffset ring leader (steps + 1))).core.erase.core.reset_cmd =
      false := by
  simpa [hecho] using h.right_reset_exact

set_option maxHeartbeats 1000000 in
/-- One non-wrap source step preserves the complete retry boundary.  The
proof applies the local protocol theorem once and then separates the two
endpoints from all off-edge vertices. -/
theorem clockwiseRetryReady_step_source
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (leader : Fin n) (C : EConfig n psi kappa tau)
    (steps : Nat) (hnonwrap : steps < n - 1)
    (hready : ClockwiseRetryReady hpsi ring leader C)
    (hsource : ClockwiseSourceAt ring leader C steps) :
    let D := localStep ring
      (wallSweepPreCheckResetPathStallTransition hpsi kappa tau)
      C (groupOffset ring leader steps)
    ClockwiseSourceStepFrame hpsi ring leader C D steps := by
  let T := wallSweepPreCheckResetPathStallTransition hpsi kappa tau
  let e := groupOffset ring leader steps
  let j := groupOffset ring leader (steps + 1)
  let q := T (C e) (C j)
  let D := localStep ring T C e
  have heBound : steps < n := by omega
  have hjBound : steps + 1 < n := by omega
  have hneighbor : ring.rightNeighbor e = j :=
    rightNeighbor_groupOffset ring leader steps
  have hene : e ≠ j := by
    rw [← hneighbor]
    exact Ne.symm (rightNeighbor_ne_self_of_one_lt ring hn e)
  have heLeader : steps = 0 → e = leader := by
    intro hs
    subst steps
    exact groupOffset_zero_eq ring leader
  have heNotLeader : 0 < steps → e ≠ leader := by
    intro hs heq
    have hne := groupOffset_ne_of_lt ring leader heBound
      (by omega : 0 < n) (by omega : steps ≠ 0)
    exact hne (heq.trans (groupOffset_zero_eq ring leader).symm)
  have hjNotLeader : j ≠ leader := by
    intro heq
    have hne := groupOffset_ne_of_lt ring leader hjBound
      (by omega : 0 < n) (by omega : steps + 1 ≠ 0)
    exact hne (heq.trans (groupOffset_zero_eq ring leader).symm)
  have hopen : WallPriorityOpen (C e) (C j) := by
    simpa [hneighbor] using
      WallPriorityOpen.of_noActiveDeletion C hready.no_active ring e
  have hsourceLocal :
      (C e).core.erase.core.leader = true ∨
        (C e).core.erase.core.reset_cmd = true := by
    rcases hsource with hzero | hpos
    · left
      rw [heLeader hzero.1]
      exact hzero.2
    · exact .inr hpos.2
  have hleftFire : LeaderFireDisabled (C e).core.erase.core := by
    by_cases hs : steps = 0
    · right
      rw [heLeader hs]
      exact hready.leader_signal_zero
    · left
      exact hready.unique_leader e (heNotLeader (by omega))
  have hrightFollower : (C j).core.erase.core.leader = false :=
    hready.unique_leader j hjNotLeader
  have hlocal : SourceCoveredNoFireOutput hpsi (C e) (C j) q := by
    exact wallSweepPreCheckResetPathStall_source_noFire
      hpsi (C e) (C j) hopen
      (by simpa [hneighbor] using hready.stable_labels e)
      hsourceLocal hleftFire hrightFollower
      (hready.bullets_zero e) (hready.bullets_zero j)
  have hleft : D e = q.1 := by
    simp [D, q, localStep, hneighbor]
  have hright : D j = q.2 := by
    simp [D, q, localStep, hneighbor, Ne.symm hene]
  have hoff : ∀ i, i ≠ e → i ≠ j → D i = C i := by
    intro i hie hij
    simp [D, localStep, hie, hneighbor, hij]
  have hleaderAt : ∀ i, (D i).core.erase.core.leader =
      (C i).core.erase.core.leader := by
    intro i
    by_cases hie : i = e
    · subst i
      rw [hleft]
      exact hlocal.left_leader
    · by_cases hij : i = j
      · subst i
        rw [hright]
        exact hlocal.right_leader
      · rw [hoff i hie hij]
  have hlabelAt : ∀ i, (D i).core.erase.core.label =
      (C i).core.erase.core.label := by
    intro i
    by_cases hie : i = e
    · subst i
      rw [hleft]
      exact hlocal.left_label
    · by_cases hij : i = j
      · subst i
        rw [hright]
        exact hlocal.right_label
      · rw [hoff i hie hij]
  have hshieldAt : ∀ i, (D i).core.erase.core.shield =
      (C i).core.erase.core.shield := by
    intro i
    by_cases hie : i = e
    · subst i
      rw [hleft]
      exact hlocal.left_shield
    · by_cases hij : i = j
      · subst i
        rw [hright]
        exact hlocal.right_shield
      · rw [hoff i hie hij]
  have hbulletAt : ∀ i,
      (D i).core.erase.core.bullet = ⟨0, by omega⟩ := by
    intro i
    by_cases hie : i = e
    · subst i
      rw [hleft]
      exact hlocal.left_bullet_zero
    · by_cases hij : i = j
      · subst i
        rw [hright]
        exact hlocal.right_bullet_zero
      · rw [hoff i hie hij]
        exact hready.bullets_zero i
  have hleaderSignal :
      (D leader).core.erase.core.signal_B = ⟨0, by omega⟩ := by
    by_cases hs : steps = 0
    · have heq := heLeader hs
      have hDLeader : D leader = q.1 := by
        rw [← heq]
        exact hleft
      rw [hDLeader]
      exact hlocal.left_signal.trans (by
        rw [heq]
        exact hready.leader_signal_zero)
    · have hsame := hoff leader
        (Ne.symm (heNotLeader (by omega))) (Ne.symm hjNotLeader)
      rw [hsame]
      exact hready.leader_signal_zero
  have hnoActiveD : NoActiveDeletion D := by
    intro i
    by_cases hie : i = e
    · subst i
      rw [hleft]
      exact deletionActive_false_of_neutral q.1 hlocal.left_neutral
    · by_cases hij : i = j
      · subst i
        rw [hright]
        exact deletionActive_false_of_neutral q.2 hlocal.right_neutral
      · rw [hoff i hie hij]
        exact hready.no_active i
  have hreadyD : ClockwiseRetryReady hpsi ring leader D := by
    refine {
      leader_alive := ?_
      leader_zero := ?_
      unique_leader := ?_
      no_free_barrier := ?_
      leader_unshielded := ?_
      bullets_zero := hbulletAt
      leader_signal_zero := hleaderSignal
      stable_labels := ?_
      no_active := hnoActiveD
    }
    · rw [hleaderAt leader]
      exact hready.leader_alive
    · rw [hlabelAt leader]
      exact hready.leader_zero
    · intro i hi
      rw [hleaderAt i]
      exact hready.unique_leader i hi
    · intro i
      dsimp only
      intro hbarrier
      have hstableD :
          (D (ring.rightNeighbor i)).core.erase.core.label =
            ⟨((D i).core.erase.core.label.val + 1) % psi,
              Nat.mod_lt _ hpsi⟩ := by
        simpa only [hlabelAt (ring.rightNeighbor i), hlabelAt i] using
          hready.stable_labels i
      exact (hbarrier hstableD).elim
    · rw [hshieldAt leader]
      exact hready.leader_unshielded
    · intro i
      rw [hlabelAt (ring.rightNeighbor i), hlabelAt i]
      exact hready.stable_labels i
  change ClockwiseSourceStepFrame hpsi ring leader C D steps
  exact {
    ready := hreadyD
    leader_eq := hleaderAt
    label_eq := hlabelAt
    shield_eq := hshieldAt
    bullets_zero := hbulletAt
    off_edge := hoff
    left_neutral := by rw [hleft]; exact hlocal.left_neutral
    right_neutral := by rw [hright]; exact hlocal.right_neutral
    left_signal_eq := by rw [hleft]; exact hlocal.left_signal
    right_signal_one_of_source := by
      intro hsourceSignal
      rw [hright]
      exact hlocal.right_signal_one_of_source hsourceSignal
    left_reset_false := by rw [hleft]; exact hlocal.left_reset_false
    right_reset_exact := by rw [hright]; exact hlocal.right_reset_exact
    right_echo_false := by rw [hright]; exact hlocal.right_echo_false
    left_echo_exact := by rw [hleft]; exact hlocal.left_echo_exact
  }

set_option maxHeartbeats 1000000 in
/-- One non-wrap source step of the leader-sink repair preserves the rooted
retry boundary.  Local successor alignment comes from `noFreeBarrier` because
the responder is not the designated leader. -/
theorem rootedClockwiseRetryReady_step_source
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (leader : Fin n) (C : EConfig n psi kappa tau)
    (steps : Nat) (hnonwrap : steps < n - 1)
    (hready : RootedClockwiseRetryReady hpsi ring leader C)
    (hsource : ClockwiseSourceAt ring leader C steps) :
    let D := localStep ring
      (wallSweepPreCheckResetLeaderSinkPathStallTransition hpsi kappa tau)
      C (groupOffset ring leader steps)
    RootedClockwiseSourceStepFrame hpsi ring leader C D steps := by
  let T := wallSweepPreCheckResetLeaderSinkPathStallTransition
    hpsi kappa tau
  let e := groupOffset ring leader steps
  let j := groupOffset ring leader (steps + 1)
  let q := T (C e) (C j)
  let D := localStep ring T C e
  have heBound : steps < n := by omega
  have hjBound : steps + 1 < n := by omega
  have hneighbor : ring.rightNeighbor e = j :=
    rightNeighbor_groupOffset ring leader steps
  have hene : e ≠ j := by
    rw [← hneighbor]
    exact Ne.symm (rightNeighbor_ne_self_of_one_lt ring hn e)
  have heLeader : steps = 0 → e = leader := by
    intro hs
    subst steps
    exact groupOffset_zero_eq ring leader
  have heNotLeader : 0 < steps → e ≠ leader := by
    intro hs heq
    have hne := groupOffset_ne_of_lt ring leader heBound
      (by omega : 0 < n) (by omega : steps ≠ 0)
    exact hne (heq.trans (groupOffset_zero_eq ring leader).symm)
  have hjNotLeader : j ≠ leader := by
    intro heq
    have hne := groupOffset_ne_of_lt ring leader hjBound
      (by omega : 0 < n) (by omega : steps + 1 ≠ 0)
    exact hne (heq.trans (groupOffset_zero_eq ring leader).symm)
  have hopen : WallPriorityOpen (C e) (C j) := by
    simpa [hneighbor] using
      WallPriorityOpen.of_noActiveDeletion C hready.no_active ring e
  have hsourceLocal :
      (C e).core.erase.core.leader = true ∨
        (C e).core.erase.core.reset_cmd = true := by
    rcases hsource with hzero | hpos
    · left
      rw [heLeader hzero.1]
      exact hzero.2
    · exact .inr hpos.2
  have hleftFire : LeaderFireDisabled (C e).core.erase.core := by
    by_cases hs : steps = 0
    · right
      rw [heLeader hs]
      exact hready.leader_signal_zero
    · left
      exact hready.unique_leader e (heNotLeader (by omega))
  have hrightFollower : (C j).core.erase.core.leader = false :=
    hready.unique_leader j hjNotLeader
  have hrightNotLeader : ring.rightNeighbor e ≠ leader := by
    rw [hneighbor]
    exact hjNotLeader
  have halign : (C j).core.erase.core.label =
      ⟨((C e).core.erase.core.label.val + 1) % psi,
        Nat.mod_lt _ hpsi⟩ := by
    simpa only [hneighbor] using
      hready.successor_label_of_right_ne e hrightNotLeader
  have hlocal : SourceCoveredNoFireOutput hpsi (C e) (C j) q := by
    exact wallSweepPreCheckResetLeaderSinkPathStall_source_noFire
      hpsi (C e) (C j) hopen halign hsourceLocal hleftFire
        hrightFollower (hready.bullets_zero e) (hready.bullets_zero j)
  have hleft : D e = q.1 := by
    simp [D, q, localStep, hneighbor]
  have hright : D j = q.2 := by
    simp [D, q, localStep, hneighbor, Ne.symm hene]
  have hoff : ∀ i, i ≠ e → i ≠ j → D i = C i := by
    intro i hie hij
    simp [D, localStep, hie, hneighbor, hij]
  have hleaderAt : ∀ i, (D i).core.erase.core.leader =
      (C i).core.erase.core.leader := by
    intro i
    by_cases hie : i = e
    · subst i
      rw [hleft]
      exact hlocal.left_leader
    · by_cases hij : i = j
      · subst i
        rw [hright]
        exact hlocal.right_leader
      · rw [hoff i hie hij]
  have hlabelAt : ∀ i, (D i).core.erase.core.label =
      (C i).core.erase.core.label := by
    intro i
    by_cases hie : i = e
    · subst i
      rw [hleft]
      exact hlocal.left_label
    · by_cases hij : i = j
      · subst i
        rw [hright]
        exact hlocal.right_label
      · rw [hoff i hie hij]
  have hshieldAt : ∀ i, (D i).core.erase.core.shield =
      (C i).core.erase.core.shield := by
    intro i
    by_cases hie : i = e
    · subst i
      rw [hleft]
      exact hlocal.left_shield
    · by_cases hij : i = j
      · subst i
        rw [hright]
        exact hlocal.right_shield
      · rw [hoff i hie hij]
  have hbulletAt : ∀ i,
      (D i).core.erase.core.bullet = ⟨0, by omega⟩ := by
    intro i
    by_cases hie : i = e
    · subst i
      rw [hleft]
      exact hlocal.left_bullet_zero
    · by_cases hij : i = j
      · subst i
        rw [hright]
        exact hlocal.right_bullet_zero
      · rw [hoff i hie hij]
        exact hready.bullets_zero i
  have hleaderSignal :
      (D leader).core.erase.core.signal_B = ⟨0, by omega⟩ := by
    by_cases hs : steps = 0
    · have heq := heLeader hs
      have hDLeader : D leader = q.1 := by
        rw [← heq]
        exact hleft
      rw [hDLeader]
      exact hlocal.left_signal.trans (by
        rw [heq]
        exact hready.leader_signal_zero)
    · have hsame := hoff leader
        (Ne.symm (heNotLeader (by omega))) (Ne.symm hjNotLeader)
      rw [hsame]
      exact hready.leader_signal_zero
  have hnoActiveD : NoActiveDeletion D := by
    intro i
    by_cases hie : i = e
    · subst i
      rw [hleft]
      exact deletionActive_false_of_neutral q.1 hlocal.left_neutral
    · by_cases hij : i = j
      · subst i
        rw [hright]
        exact deletionActive_false_of_neutral q.2 hlocal.right_neutral
      · rw [hoff i hie hij]
        exact hready.no_active i
  have hreadyD : RootedClockwiseRetryReady hpsi ring leader D := by
    refine {
      leader_alive := ?_
      leader_zero := ?_
      unique_leader := ?_
      no_free_barrier := ?_
      leader_unshielded := ?_
      bullets_zero := hbulletAt
      leader_signal_zero := hleaderSignal
      no_active := hnoActiveD
    }
    · rw [hleaderAt leader]
      exact hready.leader_alive
    · rw [hlabelAt leader]
      exact hready.leader_zero
    · intro i hi
      rw [hleaderAt i]
      exact hready.unique_leader i hi
    · intro i
      dsimp only
      intro hbarrierD
      have hbarrierC : isBarrier hpsi
          (C i).core.erase.core
          (C (ring.rightNeighbor i)).core.erase.core := by
        intro halignC
        apply hbarrierD
        apply Fin.ext
        have hright := congrArg Fin.val
          (hlabelAt (ring.rightNeighbor i))
        have hleftLabel := congrArg Fin.val (hlabelAt i)
        have halignVal := congrArg Fin.val halignC
        dsimp only at halignVal ⊢
        calc
          (D (ring.rightNeighbor i)).core.erase.core.label.val =
              (C (ring.rightNeighbor i)).core.erase.core.label.val := hright
          _ = ((C i).core.erase.core.label.val + 1) % psi := halignVal
          _ = ((D i).core.erase.core.label.val + 1) % psi := by
            rw [hleftLabel]
      exact (hleaderAt (ring.rightNeighbor i)).trans
        (hready.no_free_barrier i hbarrierC)
    · rw [hshieldAt leader]
      exact hready.leader_unshielded
  change RootedClockwiseSourceStepFrame hpsi ring leader C D steps
  exact {
    ready := hreadyD
    leader_eq := hleaderAt
    label_eq := hlabelAt
    shield_eq := hshieldAt
    bullets_zero := hbulletAt
    off_edge := hoff
    left_neutral := by rw [hleft]; exact hlocal.left_neutral
    right_neutral := by rw [hright]; exact hlocal.right_neutral
    left_signal_eq := by rw [hleft]; exact hlocal.left_signal
    right_signal_one_of_source := by
      intro hsourceSignal
      rw [hright]
      exact hlocal.right_signal_one_of_source hsourceSignal
    left_reset_false := by rw [hleft]; exact hlocal.left_reset_false
    right_reset_exact := by rw [hright]; exact hlocal.right_reset_exact
    right_echo_false := by rw [hright]; exact hlocal.right_echo_false
    left_echo_exact := by rw [hleft]; exact hlocal.left_echo_exact
  }

/-! ## Canonical first-blocker prefix -/

private theorem visitedPrefixNeutral_succ
    (ring : DirectedRing n) (leader : Fin n)
    (C D : EConfig n psi kappa tau) (steps : Nat)
    (hnext : steps + 1 < n)
    (hvisited : VisitedPrefixNeutral ring leader C steps)
    (hleft : ComparisonNeutral
      (D (groupOffset ring leader steps)).core.erase.core)
    (hright : ComparisonNeutral
      (D (groupOffset ring leader (steps + 1))).core.erase.core)
    (hoff : ∀ i,
      i ≠ groupOffset ring leader steps →
      i ≠ groupOffset ring leader (steps + 1) → D i = C i) :
    VisitedPrefixNeutral ring leader D (steps + 1) := by
  intro k hk _
  by_cases hrightIndex : k = steps + 1
  · subst k
    exact hright
  · by_cases hleftIndex : k = steps
    · subst k
      exact hleft
    · have hklt : k < steps := by omega
      have hkBound : k < n := by omega
      have hstepsBound : steps < n := by omega
      have hke : groupOffset ring leader k ≠
          groupOffset ring leader steps := by
        apply groupOffset_ne_of_lt ring leader hkBound hstepsBound
        omega
      have hkj : groupOffset ring leader k ≠
          groupOffset ring leader (steps + 1) := by
        apply groupOffset_ne_of_lt ring leader hkBound hnext
        omega
      rw [hoff _ hke hkj]
      exact hvisited k (by omega) (by omega)

private theorem untouchedAhead_succ
    (ring : DirectedRing n) (leader : Fin n)
    (base C D : EConfig n psi kappa tau) (steps : Nat)
    (hnext : steps + 1 < n)
    (hahead : UntouchedAhead ring leader base C steps)
    (hoff : ∀ i,
      i ≠ groupOffset ring leader steps →
      i ≠ groupOffset ring leader (steps + 1) → D i = C i) :
    UntouchedAhead ring leader base D (steps + 1) := by
  intro k hk hkn
  have hstepsBound : steps < n := by omega
  have hke : groupOffset ring leader k ≠
      groupOffset ring leader steps := by
    apply groupOffset_ne_of_lt ring leader hkn hstepsBound
    omega
  have hkj : groupOffset ring leader k ≠
      groupOffset ring leader (steps + 1) := by
    apply groupOffset_ne_of_lt ring leader hkn hnext
    omega
  rw [hoff _ hke hkj]
  exact hahead k (by omega) hkn

/-- State reached while approaching a fixed canonical blocker.  Only the
visited comparison prefix is normalized; the strictly higher suffix remains
bit-for-bit equal to the attempt input. -/
structure ClockwiseApproachState
    (hpsi : psi > 0) (ring : DirectedRing n) (leader : Fin n)
    (base current : EConfig n psi kappa tau)
    (t : Fin (n - 1)) (steps : Nat) : Prop where
  steps_le : steps ≤ t.val
  ready : ClockwiseRetryReady hpsi ring leader current
  source : ClockwiseSourceAt ring leader current steps
  visited_neutral : VisitedPrefixNeutral ring leader current steps
  untouched_ahead : UntouchedAhead ring leader base current steps

set_option maxHeartbeats 1000000 in
/-- A clean responder below the blocker advances the reset and extends both
the neutral prefix and the complete untouched suffix. -/
theorem ClockwiseApproachState.step_clean
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (leader : Fin n) (base current : EConfig n psi kappa tau)
    (t : Fin (n - 1)) (steps : Nat)
    (hstate : ClockwiseApproachState
      hpsi ring leader base current t steps)
    (hclear : ∀ i : Fin (n - 1), i.val < t.val →
      (base (groupOffset ring leader (i.val + 1))).core.erase.core.echo =
        false)
    (hlt : steps < t.val) :
    let D := localStep ring
      (wallSweepPreCheckResetPathStallTransition hpsi kappa tau)
      current (groupOffset ring leader steps)
    ClockwiseApproachState hpsi ring leader base D t (steps + 1) := by
  let D := localStep ring
    (wallSweepPreCheckResetPathStallTransition hpsi kappa tau)
    current (groupOffset ring leader steps)
  have hnonwrap : steps < n - 1 := by omega
  have hnext : steps + 1 < n := by omega
  have hbaseEcho :
      (base (groupOffset ring leader (steps + 1))).core.erase.core.echo =
        false := by
    have h := hclear ⟨steps, by omega⟩ (by simp; exact hlt)
    simpa using h
  have hcurrentEq :=
    hstate.untouched_ahead (steps + 1) (by omega) hnext
  have hcurrentEcho :
      (current (groupOffset ring leader (steps + 1))).core.erase.core.echo =
        false := by
    rw [hcurrentEq]
    exact hbaseEcho
  have hstep := clockwiseRetryReady_step_source
    hpsi ring hn leader current steps hnonwrap hstate.ready hstate.source
  change ClockwiseSourceStepFrame
    hpsi ring leader current D steps at hstep
  have hreset :
      (D (groupOffset ring leader (steps + 1))).core.erase.core.reset_cmd =
        true :=
    hstep.right_reset_true_of_echo_false hcurrentEcho
  change ClockwiseApproachState
    hpsi ring leader base D t (steps + 1)
  exact {
    steps_le := by omega
    ready := hstep.ready
    source := .inr ⟨by omega, hreset⟩
    visited_neutral := visitedPrefixNeutral_succ
      ring leader current D steps hnext hstate.visited_neutral
      hstep.left_neutral hstep.right_neutral hstep.off_edge
    untouched_ahead := untouchedAhead_succ
      ring leader base current D steps hnext
      hstate.untouched_ahead hstep.off_edge
  }

/-- Induction along the clean prefix below a fixed blocker. -/
theorem firstBlockerApproach_reaches
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (leader : Fin n) (C : EConfig n psi kappa tau)
    (hready : ClockwiseRetryReady hpsi ring leader C)
    (t : Fin (n - 1))
    (hclear : ∀ i : Fin (n - 1), i.val < t.val →
      (C (groupOffset ring leader (i.val + 1))).core.erase.core.echo =
        false)
    (steps : Nat) (hsteps : steps ≤ t.val) :
    ClockwiseApproachState hpsi ring leader C
      (clockwiseAttemptConfig
        (wallSweepPreCheckResetPathStallTransition hpsi kappa tau)
        ring leader C steps)
      t steps := by
  induction steps with
  | zero =>
      change ClockwiseApproachState hpsi ring leader C C t 0
      exact {
        steps_le := by omega
        ready := hready
        source := .inl ⟨rfl, hready.leader_alive⟩
        visited_neutral := by intro k hk hpos; omega
        untouched_ahead := by intro k hk hkn; rfl
      }
  | succ steps ih =>
      have hprev := ih (by omega)
      have hnext := ClockwiseApproachState.step_clean
        hpsi ring hn leader C
        (clockwiseAttemptConfig
          (wallSweepPreCheckResetPathStallTransition hpsi kappa tau)
          ring leader C steps)
        t steps hprev hclear (by omega)
      change ClockwiseApproachState hpsi ring leader C
        (clockwiseAttemptConfig
          (wallSweepPreCheckResetPathStallTransition hpsi kappa tau)
          ring leader C (steps + 1))
        t (steps + 1)
      rw [clockwiseAttemptConfig_succ]
      exact hnext

/-! ## The collision edge and strict rank descent -/

/-- Exact endpoint immediately after consuming the first blocker.  The retry
boundary has already been reconstructed and all higher echo bits are framed. -/
structure ClockwiseFirstBlockerEndpoint
    (hpsi : psi > 0) (ring : DirectedRing n) (leader : Fin n)
    (base final : EConfig n psi kappa tau)
    (t : Fin (n - 1)) : Prop where
  ready : ClockwiseRetryReady hpsi ring leader final
  visited_neutral : VisitedPrefixNeutral ring leader final (t.val + 1)
  untouched_ahead : UntouchedAhead ring leader base final (t.val + 1)
  initiator_reset_false :
    (final (groupOffset ring leader t.val)).core.erase.core.reset_cmd = false
  blocker_reset_false :
    (final (groupOffset ring leader (t.val + 1))).core.erase.core.reset_cmd =
      false
  blocker_echo_false :
    (final (groupOffset ring leader (t.val + 1))).core.erase.core.echo = false
  higher_unchanged : ∀ s : Fin (n - 1), t.val < s.val →
    (final (groupOffset ring leader (s.val + 1))).core.erase.core.echo =
      (base (groupOffset ring leader (s.val + 1))).core.erase.core.echo

set_option maxHeartbeats 1000000 in
/-- The canonical blocker consumes the moving reset, clears its echo, and
returns a retry-ready state with every higher rank bit unchanged. -/
theorem firstBlockerAttempt_reaches
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (leader : Fin n) (C : EConfig n psi kappa tau)
    (hready : ClockwiseRetryReady hpsi ring leader C)
    (t : Fin (n - 1))
    (hpresent :
      (C (groupOffset ring leader (t.val + 1))).core.erase.core.echo = true)
    (hclear : ∀ i : Fin (n - 1), i.val < t.val →
      (C (groupOffset ring leader (i.val + 1))).core.erase.core.echo =
        false) :
    ClockwiseFirstBlockerEndpoint hpsi ring leader C
      (clockwiseAttemptConfig
        (wallSweepPreCheckResetPathStallTransition hpsi kappa tau)
        ring leader C (t.val + 1))
      t := by
  let T := wallSweepPreCheckResetPathStallTransition hpsi kappa tau
  let Ct := clockwiseAttemptConfig T ring leader C t.val
  let D := localStep ring T Ct (groupOffset ring leader t.val)
  have happ := firstBlockerApproach_reaches
    hpsi ring hn leader C hready t hclear t.val (by omega)
  change ClockwiseApproachState hpsi ring leader C Ct t t.val at happ
  have hstep := clockwiseRetryReady_step_source
    hpsi ring hn leader Ct t.val t.isLt happ.ready happ.source
  change ClockwiseSourceStepFrame hpsi ring leader Ct D t.val at hstep
  have hCtEq :=
    happ.untouched_ahead (t.val + 1) (by omega) (by omega)
  have hCtEcho :
      (Ct (groupOffset ring leader (t.val + 1))).core.erase.core.echo =
        true := by
    rw [hCtEq]
    exact hpresent
  have hvisited := visitedPrefixNeutral_succ
    ring leader Ct D t.val (by omega)
    happ.visited_neutral hstep.left_neutral hstep.right_neutral hstep.off_edge
  have hahead := untouchedAhead_succ
    ring leader C Ct D t.val (by omega)
    happ.untouched_ahead hstep.off_edge
  have hblockerReset :=
    hstep.right_reset_false_of_echo_true hCtEcho
  have hsucc :
      clockwiseAttemptConfig T ring leader C (t.val + 1) = D :=
    clockwiseAttemptConfig_succ T ring leader C t.val
  rw [hsucc]
  exact {
    ready := hstep.ready
    visited_neutral := hvisited
    untouched_ahead := hahead
    initiator_reset_false := hstep.left_reset_false
    blocker_reset_false := hblockerReset
    blocker_echo_false := hstep.right_echo_false
    higher_unchanged := by
      intro s hts
      have hstateEq := hahead (s.val + 1) (by omega) (by omega)
      exact congrArg
        (fun u : ExpiringAgentState psi kappa tau =>
          u.core.erase.core.echo)
        hstateEq
  }

/-- Every positive rank has a literal canonical first-blocker attempt that
returns retry readiness and strictly decreases the binary echo rank. -/
theorem preCheckReset_clockwiseFailedAttempt
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (leader : Fin n) (C : EConfig n psi kappa tau)
    (hready : ClockwiseRetryReady hpsi ring leader C)
    (hrank : clockwiseEchoRank ring leader C ≠ 0) :
    ClockwiseFailedAttempt
      (wallSweepPreCheckResetPathStallTransition hpsi kappa tau)
      ring leader (ClockwiseRetryReady hpsi ring leader) C := by
  obtain ⟨t, hcanonical, hpresent, hclear⟩ :=
    exists_firstClockwiseEcho_of_rank_ne_zero ring leader C hrank
  have hend := firstBlockerAttempt_reaches
    hpsi ring hn leader C hready t hpresent hclear
  have heffect : FirstBlockerEffect ring leader C
      (clockwiseAttemptConfig
        (wallSweepPreCheckResetPathStallTransition hpsi kappa tau)
        ring leader C (t.val + 1))
      t := {
    blocker_present := hpresent
    blocker_cleared := hend.blocker_echo_false
    higher_unchanged := hend.higher_unchanged
  }
  exact ⟨t, hcanonical, hend.ready, heffect.rank_lt⟩

/-! ## Rooted first-blocker attempts -/

/-- Rooted approach state for the clean prefix below a fixed blocker. -/
structure RootedClockwiseApproachState
    (hpsi : psi > 0) (ring : DirectedRing n) (leader : Fin n)
    (base current : EConfig n psi kappa tau)
    (t : Fin (n - 1)) (steps : Nat) : Prop where
  steps_le : steps ≤ t.val
  ready : RootedClockwiseRetryReady hpsi ring leader current
  source : ClockwiseSourceAt ring leader current steps
  visited_neutral : VisitedPrefixNeutral ring leader current steps
  untouched_ahead : UntouchedAhead ring leader base current steps

set_option maxHeartbeats 1000000 in
/-- A clean responder below the blocker advances the rooted repair's reset
source without touching the higher echo suffix. -/
theorem RootedClockwiseApproachState.step_clean
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (leader : Fin n) (base current : EConfig n psi kappa tau)
    (t : Fin (n - 1)) (steps : Nat)
    (hstate : RootedClockwiseApproachState
      hpsi ring leader base current t steps)
    (hclear : ∀ i : Fin (n - 1), i.val < t.val →
      (base (groupOffset ring leader (i.val + 1))).core.erase.core.echo =
        false)
    (hlt : steps < t.val) :
    let D := localStep ring
      (wallSweepPreCheckResetLeaderSinkPathStallTransition hpsi kappa tau)
      current (groupOffset ring leader steps)
    RootedClockwiseApproachState
      hpsi ring leader base D t (steps + 1) := by
  let D := localStep ring
    (wallSweepPreCheckResetLeaderSinkPathStallTransition hpsi kappa tau)
    current (groupOffset ring leader steps)
  have hnonwrap : steps < n - 1 := by omega
  have hnext : steps + 1 < n := by omega
  have hbaseEcho :
      (base (groupOffset ring leader (steps + 1))).core.erase.core.echo =
        false := by
    have h := hclear ⟨steps, by omega⟩ (by simp; exact hlt)
    simpa using h
  have hcurrentEq :=
    hstate.untouched_ahead (steps + 1) (by omega) hnext
  have hcurrentEcho :
      (current (groupOffset ring leader (steps + 1))).core.erase.core.echo =
        false := by
    rw [hcurrentEq]
    exact hbaseEcho
  have hstep := rootedClockwiseRetryReady_step_source
    hpsi ring hn leader current steps hnonwrap hstate.ready hstate.source
  change RootedClockwiseSourceStepFrame
    hpsi ring leader current D steps at hstep
  have hreset :
      (D (groupOffset ring leader (steps + 1))).core.erase.core.reset_cmd =
        true := by
    simpa [hcurrentEcho] using hstep.right_reset_exact
  change RootedClockwiseApproachState
    hpsi ring leader base D t (steps + 1)
  exact {
    steps_le := by omega
    ready := hstep.ready
    source := .inr ⟨by omega, hreset⟩
    visited_neutral := visitedPrefixNeutral_succ
      ring leader current D steps hnext hstate.visited_neutral
      hstep.left_neutral hstep.right_neutral hstep.off_edge
    untouched_ahead := untouchedAhead_succ
      ring leader base current D steps hnext
      hstate.untouched_ahead hstep.off_edge
  }

/-- Induction along the rooted clean prefix below a fixed blocker. -/
theorem rootedFirstBlockerApproach_reaches
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (leader : Fin n) (C : EConfig n psi kappa tau)
    (hready : RootedClockwiseRetryReady hpsi ring leader C)
    (t : Fin (n - 1))
    (hclear : ∀ i : Fin (n - 1), i.val < t.val →
      (C (groupOffset ring leader (i.val + 1))).core.erase.core.echo =
        false)
    (steps : Nat) (hsteps : steps ≤ t.val) :
    RootedClockwiseApproachState hpsi ring leader C
      (clockwiseAttemptConfig
        (wallSweepPreCheckResetLeaderSinkPathStallTransition
          hpsi kappa tau)
        ring leader C steps)
      t steps := by
  induction steps with
  | zero =>
      change RootedClockwiseApproachState hpsi ring leader C C t 0
      exact {
        steps_le := by omega
        ready := hready
        source := .inl ⟨rfl, hready.leader_alive⟩
        visited_neutral := by intro k hk hpos; omega
        untouched_ahead := by intro k hk hkn; rfl
      }
  | succ steps ih =>
      have hprev := ih (by omega)
      have hnext := RootedClockwiseApproachState.step_clean
        hpsi ring hn leader C
        (clockwiseAttemptConfig
          (wallSweepPreCheckResetLeaderSinkPathStallTransition
            hpsi kappa tau)
          ring leader C steps)
        t steps hprev hclear (by omega)
      change RootedClockwiseApproachState hpsi ring leader C
        (clockwiseAttemptConfig
          (wallSweepPreCheckResetLeaderSinkPathStallTransition
            hpsi kappa tau)
          ring leader C (steps + 1))
        t (steps + 1)
      rw [clockwiseAttemptConfig_succ]
      exact hnext

/-- Rooted endpoint immediately after consuming the canonical blocker. -/
structure RootedClockwiseFirstBlockerEndpoint
    (hpsi : psi > 0) (ring : DirectedRing n) (leader : Fin n)
    (base final : EConfig n psi kappa tau)
    (t : Fin (n - 1)) : Prop where
  ready : RootedClockwiseRetryReady hpsi ring leader final
  visited_neutral : VisitedPrefixNeutral ring leader final (t.val + 1)
  untouched_ahead : UntouchedAhead ring leader base final (t.val + 1)
  initiator_reset_false :
    (final (groupOffset ring leader t.val)).core.erase.core.reset_cmd = false
  blocker_reset_false :
    (final (groupOffset ring leader (t.val + 1))).core.erase.core.reset_cmd =
      false
  blocker_echo_false :
    (final (groupOffset ring leader (t.val + 1))).core.erase.core.echo = false
  higher_unchanged : ∀ s : Fin (n - 1), t.val < s.val →
    (final (groupOffset ring leader (s.val + 1))).core.erase.core.echo =
      (base (groupOffset ring leader (s.val + 1))).core.erase.core.echo

set_option maxHeartbeats 1000000 in
/-- The rooted canonical blocker consumes the reset, clears its echo, and
returns the same paper-faithful retry boundary. -/
theorem rootedFirstBlockerAttempt_reaches
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (leader : Fin n) (C : EConfig n psi kappa tau)
    (hready : RootedClockwiseRetryReady hpsi ring leader C)
    (t : Fin (n - 1))
    (hpresent :
      (C (groupOffset ring leader (t.val + 1))).core.erase.core.echo = true)
    (hclear : ∀ i : Fin (n - 1), i.val < t.val →
      (C (groupOffset ring leader (i.val + 1))).core.erase.core.echo =
        false) :
    RootedClockwiseFirstBlockerEndpoint hpsi ring leader C
      (clockwiseAttemptConfig
        (wallSweepPreCheckResetLeaderSinkPathStallTransition
          hpsi kappa tau)
        ring leader C (t.val + 1))
      t := by
  let T := wallSweepPreCheckResetLeaderSinkPathStallTransition
    hpsi kappa tau
  let Ct := clockwiseAttemptConfig T ring leader C t.val
  let D := localStep ring T Ct (groupOffset ring leader t.val)
  have happ := rootedFirstBlockerApproach_reaches
    hpsi ring hn leader C hready t hclear t.val (by omega)
  change RootedClockwiseApproachState
    hpsi ring leader C Ct t t.val at happ
  have hstep := rootedClockwiseRetryReady_step_source
    hpsi ring hn leader Ct t.val t.isLt happ.ready happ.source
  change RootedClockwiseSourceStepFrame
    hpsi ring leader Ct D t.val at hstep
  have hCtEq :=
    happ.untouched_ahead (t.val + 1) (by omega) (by omega)
  have hCtEcho :
      (Ct (groupOffset ring leader (t.val + 1))).core.erase.core.echo =
        true := by
    rw [hCtEq]
    exact hpresent
  have hvisited := visitedPrefixNeutral_succ
    ring leader Ct D t.val (by omega)
    happ.visited_neutral hstep.left_neutral hstep.right_neutral hstep.off_edge
  have hahead := untouchedAhead_succ
    ring leader C Ct D t.val (by omega)
    happ.untouched_ahead hstep.off_edge
  have hblockerReset :
      (D (groupOffset ring leader (t.val + 1))).core.erase.core.reset_cmd =
        false := by
    simpa [hCtEcho] using hstep.right_reset_exact
  have hsucc :
      clockwiseAttemptConfig T ring leader C (t.val + 1) = D :=
    clockwiseAttemptConfig_succ T ring leader C t.val
  rw [hsucc]
  exact {
    ready := hstep.ready
    visited_neutral := hvisited
    untouched_ahead := hahead
    initiator_reset_false := hstep.left_reset_false
    blocker_reset_false := hblockerReset
    blocker_echo_false := hstep.right_echo_false
    higher_unchanged := by
      intro s hts
      have hstateEq := hahead (s.val + 1) (by omega) (by omega)
      exact congrArg
        (fun u : ExpiringAgentState psi kappa tau =>
          u.core.erase.core.echo)
        hstateEq
  }

/-- Every positive echo rank has a rooted literal first-blocker attempt that
strictly decreases the same binary rank. -/
theorem preCheckResetLeaderSink_rootedClockwiseFailedAttempt
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (leader : Fin n) (C : EConfig n psi kappa tau)
    (hready : RootedClockwiseRetryReady hpsi ring leader C)
    (hrank : clockwiseEchoRank ring leader C ≠ 0) :
    ClockwiseFailedAttempt
      (wallSweepPreCheckResetLeaderSinkPathStallTransition hpsi kappa tau)
      ring leader (RootedClockwiseRetryReady hpsi ring leader) C := by
  obtain ⟨t, hcanonical, hpresent, hclear⟩ :=
    exists_firstClockwiseEcho_of_rank_ne_zero ring leader C hrank
  have hend := rootedFirstBlockerAttempt_reaches
    hpsi ring hn leader C hready t hpresent hclear
  have heffect : FirstBlockerEffect ring leader C
      (clockwiseAttemptConfig
        (wallSweepPreCheckResetLeaderSinkPathStallTransition
          hpsi kappa tau)
        ring leader C (t.val + 1))
      t := {
    blocker_present := hpresent
    blocker_cleared := hend.blocker_echo_false
    higher_unchanged := hend.higher_unchanged
  }
  exact ⟨t, hcanonical, hend.ready, heffect.rank_lt⟩

/-- The nonzero-rank half of the abstract attempt contract is now concrete;
only a chosen zero-rank endpoint theorem remains to instantiate the full
scheduler. -/
theorem preCheckResetClockwiseAttemptContract_of_zero_rank
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (leader : Fin n) (Done : EConfig n psi kappa tau → Prop)
    (hzero : ∀ C,
      ClockwiseRetryReady hpsi ring leader C →
      clockwiseEchoRank ring leader C = 0 →
      Done (clockwiseAttemptConfig
        (wallSweepPreCheckResetPathStallTransition hpsi kappa tau)
        ring leader C n)) :
    ClockwiseAttemptContract
      (wallSweepPreCheckResetPathStallTransition hpsi kappa tau)
      ring hn leader (ClockwiseRetryReady hpsi ring leader) Done where
  failed := by
    intro C hready hrank
    exact preCheckReset_clockwiseFailedAttempt
      hpsi ring hn leader C hready hrank
  zero_rank := hzero

/-! ## Correct zero-rank full pass -/

/-- Rank zero means every physical follower strictly clockwise from the
designated leader has echo false in the input configuration. -/
theorem follower_echo_false_of_clockwiseEchoRank_eq_zero
    (ring : DirectedRing n) (leader : Fin n)
    (C : EConfig n psi kappa tau)
    (hzero : clockwiseEchoRank ring leader C = 0) :
    ∀ k, 0 < k → k < n →
      (C (groupOffset ring leader k)).core.erase.core.echo = false := by
  have hall := (binaryRank_eq_zero_iff
    (clockwiseFollowerEchoBits ring leader C)).mp hzero
  intro k hk hkn
  let i : Fin (n - 1) := ⟨k - 1, by omega⟩
  have hi := hall i
  change
    (C (groupOffset ring leader (i.val + 1))).core.erase.core.echo =
      false at hi
  have hindex : i.val + 1 = k := by
    dsimp only [i]
    omega
  rwa [hindex] at hi

/-- Prefix invariant for the zero-rank pass.  Retry readiness is retained up
to the final wrap, all initial follower echoes strictly ahead remain false,
and the first edge permanently clears the designated leader's echo. -/
structure ClockwiseZeroPrefixState
    (hpsi : psi > 0) (ring : DirectedRing n) (leader : Fin n)
    (base current : EConfig n psi kappa tau) (steps : Nat) : Prop where
  steps_le : steps ≤ n - 1
  ready : ClockwiseRetryReady hpsi ring leader current
  source : ClockwiseSourceAt ring leader current steps
  visited_neutral : VisitedPrefixNeutral ring leader current steps
  untouched_ahead : UntouchedAhead ring leader base current steps
  leader_echo_false : 0 < steps →
    (current leader).core.erase.core.echo = false
  frontier_signal_one : 0 < steps → steps < n →
    (current (groupOffset ring leader steps)).core.erase.core.signal_B =
      ⟨1, by omega⟩
  reset_behind : ∀ k, k < steps →
    (current (groupOffset ring leader k)).core.erase.core.reset_cmd = false

set_option maxHeartbeats 1000000 in
/-- One non-wrap zero-rank edge advances the reset across a false original
echo while preserving the prefix invariant. -/
theorem ClockwiseZeroPrefixState.step
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (leader : Fin n) (base current : EConfig n psi kappa tau)
    (steps : Nat)
    (hstate : ClockwiseZeroPrefixState
      hpsi ring leader base current steps)
    (hzero : clockwiseEchoRank ring leader base = 0)
    (hlt : steps < n - 1) :
    let D := localStep ring
      (wallSweepPreCheckResetPathStallTransition hpsi kappa tau)
      current (groupOffset ring leader steps)
    ClockwiseZeroPrefixState
      hpsi ring leader base D (steps + 1) := by
  let D := localStep ring
    (wallSweepPreCheckResetPathStallTransition hpsi kappa tau)
    current (groupOffset ring leader steps)
  have hnext : steps + 1 < n := by omega
  have hbaseEcho :
      (base (groupOffset ring leader (steps + 1))).core.erase.core.echo =
        false :=
    follower_echo_false_of_clockwiseEchoRank_eq_zero
      ring leader base hzero (steps + 1) (by omega) hnext
  have hcurrentEq :=
    hstate.untouched_ahead (steps + 1) (by omega) hnext
  have hcurrentEcho :
      (current (groupOffset ring leader (steps + 1))).core.erase.core.echo =
        false := by
    rw [hcurrentEq]
    exact hbaseEcho
  have hstep := clockwiseRetryReady_step_source
    hpsi ring hn leader current steps hlt hstate.ready hstate.source
  change ClockwiseSourceStepFrame
    hpsi ring leader current D steps at hstep
  have hreset := hstep.right_reset_true_of_echo_false hcurrentEcho
  have hsignalSource :
      (current (groupOffset ring leader steps)).core.erase.core.leader = true ∨
      (current (groupOffset ring leader steps)).core.erase.core.signal_B =
        ⟨1, by omega⟩ := by
    by_cases hs : steps = 0
    · left
      rw [hs, groupOffset_zero_eq]
      exact hstate.ready.leader_alive
    · right
      exact hstate.frontier_signal_one (by omega) (by omega)
  have hrightSignal :=
    hstep.right_signal_one_of_source hsignalSource
  have hleaderEcho : (D leader).core.erase.core.echo = false := by
    by_cases hs : steps = 0
    · have heq : groupOffset ring leader steps = leader := by
        rw [hs]
        exact groupOffset_zero_eq ring leader
      have hout := hstep.left_echo_exact
      rw [heq] at hout
      simpa [hstate.ready.leader_alive] using hout
    · have heBound : steps < n := by omega
      have hjBound : steps + 1 < n := by omega
      have heNotLeader : groupOffset ring leader steps ≠ leader := by
        have hne := groupOffset_ne_of_lt ring leader heBound
          (by omega : 0 < n) (by omega : steps ≠ 0)
        exact fun heq =>
          hne (heq.trans (groupOffset_zero_eq ring leader).symm)
      have hjNotLeader :
          groupOffset ring leader (steps + 1) ≠ leader := by
        have hne := groupOffset_ne_of_lt ring leader hjBound
          (by omega : 0 < n) (by omega : steps + 1 ≠ 0)
        exact fun heq =>
          hne (heq.trans (groupOffset_zero_eq ring leader).symm)
      rw [hstep.off_edge leader (Ne.symm heNotLeader)
        (Ne.symm hjNotLeader)]
      exact hstate.leader_echo_false (by omega)
  change ClockwiseZeroPrefixState
    hpsi ring leader base D (steps + 1)
  exact {
    steps_le := by omega
    ready := hstep.ready
    source := .inr ⟨by omega, hreset⟩
    visited_neutral := visitedPrefixNeutral_succ
      ring leader current D steps hnext hstate.visited_neutral
      hstep.left_neutral hstep.right_neutral hstep.off_edge
    untouched_ahead := untouchedAhead_succ
      ring leader base current D steps hnext
      hstate.untouched_ahead hstep.off_edge
    leader_echo_false := fun _ => hleaderEcho
    frontier_signal_one := fun _ _ => hrightSignal
    reset_behind := by
      intro k hk
      by_cases hks : k = steps
      · subst k
        exact hstep.left_reset_false
      · have hklt : k < steps := by omega
        have hkBound : k < n := by omega
        have hstepsBound : steps < n := by omega
        have hke : groupOffset ring leader k ≠
            groupOffset ring leader steps := by
          apply groupOffset_ne_of_lt ring leader hkBound hstepsBound
          omega
        have hkj : groupOffset ring leader k ≠
            groupOffset ring leader (steps + 1) := by
          apply groupOffset_ne_of_lt ring leader hkBound hnext
          omega
        rw [hstep.off_edge _ hke hkj]
        exact hstate.reset_behind k hklt
  }

/-- Every prefix ending immediately before the wrap satisfies the exact
zero-rank retry invariant. -/
theorem clockwiseZeroPrefix_reaches
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (leader : Fin n) (C : EConfig n psi kappa tau)
    (hready : ClockwiseRetryReady hpsi ring leader C)
    (hzero : clockwiseEchoRank ring leader C = 0)
    (steps : Nat) (hsteps : steps ≤ n - 1) :
    ClockwiseZeroPrefixState hpsi ring leader C
      (clockwiseAttemptConfig
        (wallSweepPreCheckResetPathStallTransition hpsi kappa tau)
        ring leader C steps)
      steps := by
  induction steps with
  | zero =>
      change ClockwiseZeroPrefixState hpsi ring leader C C 0
      exact {
        steps_le := by omega
        ready := hready
        source := .inl ⟨rfl, hready.leader_alive⟩
        visited_neutral := by intro k hk hpos; omega
        untouched_ahead := by intro k hk hkn; rfl
        leader_echo_false := by intro hpos; omega
        frontier_signal_one := by intro hpos; omega
        reset_behind := by intro k hk; omega
      }
  | succ steps ih =>
      have hprev := ih (by omega)
      have hnext := ClockwiseZeroPrefixState.step
        hpsi ring hn leader C
        (clockwiseAttemptConfig
          (wallSweepPreCheckResetPathStallTransition hpsi kappa tau)
          ring leader C steps)
        steps hprev hzero (by omega)
      change ClockwiseZeroPrefixState hpsi ring leader C
        (clockwiseAttemptConfig
          (wallSweepPreCheckResetPathStallTransition hpsi kappa tau)
          ring leader C (steps + 1))
        (steps + 1)
      rw [clockwiseAttemptConfig_succ]
      exact hnext

/-- Rooted zero-rank prefix invariant for the leader-sink repair. -/
structure RootedClockwiseZeroPrefixState
    (hpsi : psi > 0) (ring : DirectedRing n) (leader : Fin n)
    (base current : EConfig n psi kappa tau) (steps : Nat) : Prop where
  steps_le : steps ≤ n - 1
  ready : RootedClockwiseRetryReady hpsi ring leader current
  source : ClockwiseSourceAt ring leader current steps
  visited_neutral : VisitedPrefixNeutral ring leader current steps
  untouched_ahead : UntouchedAhead ring leader base current steps
  leader_echo_false : 0 < steps →
    (current leader).core.erase.core.echo = false
  frontier_signal_one : 0 < steps → steps < n →
    (current (groupOffset ring leader steps)).core.erase.core.signal_B =
      ⟨1, by omega⟩
  reset_behind : ∀ k, k < steps →
    (current (groupOffset ring leader k)).core.erase.core.reset_cmd = false

set_option maxHeartbeats 1000000 in
/-- One non-wrap rooted zero-rank edge advances the reset and signal while
preserving the paper-faithful geometry. -/
theorem RootedClockwiseZeroPrefixState.step
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (leader : Fin n) (base current : EConfig n psi kappa tau)
    (steps : Nat)
    (hstate : RootedClockwiseZeroPrefixState
      hpsi ring leader base current steps)
    (hzero : clockwiseEchoRank ring leader base = 0)
    (hlt : steps < n - 1) :
    let D := localStep ring
      (wallSweepPreCheckResetLeaderSinkPathStallTransition hpsi kappa tau)
      current (groupOffset ring leader steps)
    RootedClockwiseZeroPrefixState
      hpsi ring leader base D (steps + 1) := by
  let D := localStep ring
    (wallSweepPreCheckResetLeaderSinkPathStallTransition hpsi kappa tau)
    current (groupOffset ring leader steps)
  have hnext : steps + 1 < n := by omega
  have hbaseEcho :
      (base (groupOffset ring leader (steps + 1))).core.erase.core.echo =
        false :=
    follower_echo_false_of_clockwiseEchoRank_eq_zero
      ring leader base hzero (steps + 1) (by omega) hnext
  have hcurrentEq :=
    hstate.untouched_ahead (steps + 1) (by omega) hnext
  have hcurrentEcho :
      (current (groupOffset ring leader (steps + 1))).core.erase.core.echo =
        false := by
    rw [hcurrentEq]
    exact hbaseEcho
  have hstep := rootedClockwiseRetryReady_step_source
    hpsi ring hn leader current steps hlt hstate.ready hstate.source
  change RootedClockwiseSourceStepFrame
    hpsi ring leader current D steps at hstep
  have hreset :
      (D (groupOffset ring leader (steps + 1))).core.erase.core.reset_cmd =
        true := by
    simpa [hcurrentEcho] using hstep.right_reset_exact
  have hsignalSource :
      (current (groupOffset ring leader steps)).core.erase.core.leader = true ∨
      (current (groupOffset ring leader steps)).core.erase.core.signal_B =
        ⟨1, by omega⟩ := by
    by_cases hs : steps = 0
    · left
      rw [hs, groupOffset_zero_eq]
      exact hstate.ready.leader_alive
    · right
      exact hstate.frontier_signal_one (by omega) (by omega)
  have hrightSignal := hstep.right_signal_one_of_source hsignalSource
  have hleaderEcho : (D leader).core.erase.core.echo = false := by
    by_cases hs : steps = 0
    · have heq : groupOffset ring leader steps = leader := by
        rw [hs]
        exact groupOffset_zero_eq ring leader
      have hout := hstep.left_echo_exact
      rw [heq] at hout
      simpa [hstate.ready.leader_alive] using hout
    · have heBound : steps < n := by omega
      have hjBound : steps + 1 < n := by omega
      have heNotLeader : groupOffset ring leader steps ≠ leader := by
        have hne := groupOffset_ne_of_lt ring leader heBound
          (by omega : 0 < n) (by omega : steps ≠ 0)
        exact fun heq =>
          hne (heq.trans (groupOffset_zero_eq ring leader).symm)
      have hjNotLeader :
          groupOffset ring leader (steps + 1) ≠ leader := by
        have hne := groupOffset_ne_of_lt ring leader hjBound
          (by omega : 0 < n) (by omega : steps + 1 ≠ 0)
        exact fun heq =>
          hne (heq.trans (groupOffset_zero_eq ring leader).symm)
      rw [hstep.off_edge leader (Ne.symm heNotLeader)
        (Ne.symm hjNotLeader)]
      exact hstate.leader_echo_false (by omega)
  change RootedClockwiseZeroPrefixState
    hpsi ring leader base D (steps + 1)
  exact {
    steps_le := by omega
    ready := hstep.ready
    source := .inr ⟨by omega, hreset⟩
    visited_neutral := visitedPrefixNeutral_succ
      ring leader current D steps hnext hstate.visited_neutral
      hstep.left_neutral hstep.right_neutral hstep.off_edge
    untouched_ahead := untouchedAhead_succ
      ring leader base current D steps hnext
      hstate.untouched_ahead hstep.off_edge
    leader_echo_false := fun _ => hleaderEcho
    frontier_signal_one := fun _ _ => hrightSignal
    reset_behind := by
      intro k hk
      by_cases hks : k = steps
      · subst k
        exact hstep.left_reset_false
      · have hklt : k < steps := by omega
        have hkBound : k < n := by omega
        have hstepsBound : steps < n := by omega
        have hke : groupOffset ring leader k ≠
            groupOffset ring leader steps := by
          apply groupOffset_ne_of_lt ring leader hkBound hstepsBound
          omega
        have hkj : groupOffset ring leader k ≠
            groupOffset ring leader (steps + 1) := by
          apply groupOffset_ne_of_lt ring leader hkBound hnext
          omega
        rw [hstep.off_edge _ hke hkj]
        exact hstate.reset_behind k hklt
  }

/-- Every rooted zero-rank prefix ending immediately before the closing edge
satisfies the exact moving-source invariant. -/
theorem rootedClockwiseZeroPrefix_reaches
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (leader : Fin n) (C : EConfig n psi kappa tau)
    (hready : RootedClockwiseRetryReady hpsi ring leader C)
    (hzero : clockwiseEchoRank ring leader C = 0)
    (steps : Nat) (hsteps : steps ≤ n - 1) :
    RootedClockwiseZeroPrefixState hpsi ring leader C
      (clockwiseAttemptConfig
        (wallSweepPreCheckResetLeaderSinkPathStallTransition hpsi kappa tau)
        ring leader C steps)
      steps := by
  induction steps with
  | zero =>
      change RootedClockwiseZeroPrefixState hpsi ring leader C C 0
      exact {
        steps_le := by omega
        ready := hready
        source := .inl ⟨rfl, hready.leader_alive⟩
        visited_neutral := by intro k hk hpos; omega
        untouched_ahead := by intro k hk hkn; rfl
        leader_echo_false := by intro hpos; omega
        frontier_signal_one := by intro hpos; omega
        reset_behind := by intro k hk; omega
      }
  | succ steps ih =>
      have hprev := ih (by omega)
      have hnext := RootedClockwiseZeroPrefixState.step
        hpsi ring hn leader C
        (clockwiseAttemptConfig
          (wallSweepPreCheckResetLeaderSinkPathStallTransition
            hpsi kappa tau)
          ring leader C steps)
        steps hprev hzero (by omega)
      change RootedClockwiseZeroPrefixState hpsi ring leader C
        (clockwiseAttemptConfig
          (wallSweepPreCheckResetLeaderSinkPathStallTransition
            hpsi kappa tau)
          ring leader C (steps + 1))
        (steps + 1)
      rw [clockwiseAttemptConfig_succ]
      exact hnext

private theorem groupOffset_n_eq
    (ring : DirectedRing n) (leader : Fin n) :
    groupOffset ring leader n = leader := by
  apply Fin.ext
  simp [groupOffset, Nat.add_mod_right, Nat.mod_eq_of_lt leader.isLt]

set_option maxHeartbeats 1000000 in
/-- At rank zero the literal `n`-edge clockwise word reaches the sharp wrap
endpoint.  The propagated absence signal and reset token return to the
leader, while every follower has relinquished reset.  No follower-echo or
final-rank assertion is made. -/
theorem preCheckReset_zeroRank_fullPass_exact
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (leader : Fin n) (C : EConfig n psi kappa tau)
    (hready : ClockwiseRetryReady hpsi ring leader C)
    (hzero : clockwiseEchoRank ring leader C = 0) :
    ClockwiseRetryDoneExact hpsi ring leader
      (clockwiseAttemptConfig
        (wallSweepPreCheckResetPathStallTransition hpsi kappa tau)
        ring leader C n) := by
  let T := wallSweepPreCheckResetPathStallTransition hpsi kappa tau
  let pre := clockwiseAttemptConfig T ring leader C (n - 1)
  let e := groupOffset ring leader (n - 1)
  let j := groupOffset ring leader n
  let q := T (pre e) (pre j)
  let D := localStep ring T pre e
  have hpre := clockwiseZeroPrefix_reaches
    hpsi ring hn leader C hready hzero (n - 1) (by omega)
  change ClockwiseZeroPrefixState hpsi ring leader C pre (n - 1) at hpre
  have heBound : n - 1 < n := by omega
  have hneighbor : ring.rightNeighbor e = j := by
    have hnEq : n - 1 + 1 = n := by omega
    simpa only [e, j, hnEq] using
      rightNeighbor_groupOffset ring leader (n - 1)
  have hjLeader : j = leader := groupOffset_n_eq ring leader
  have heNotLeader : e ≠ leader := by
    have hne := groupOffset_ne_of_lt ring leader heBound
      (by omega : 0 < n) (by omega : n - 1 ≠ 0)
    exact fun heq => hne (heq.trans (groupOffset_zero_eq ring leader).symm)
  have hene : e ≠ j := by
    rw [hjLeader]
    exact heNotLeader
  have hopen : WallPriorityOpen (pre e) (pre j) := by
    simpa [hneighbor] using
      WallPriorityOpen.of_noActiveDeletion pre hpre.ready.no_active ring e
  have hsource : (pre e).core.erase.core.leader = true ∨
      (pre e).core.erase.core.reset_cmd = true := by
    rcases hpre.source with hzeroSource | hresetSource
    · omega
    · exact .inr hresetSource.2
  have hleftFire : LeaderFireDisabled (pre e).core.erase.core :=
    .inl (hpre.ready.unique_leader e heNotLeader)
  have hrightFire : LeaderFireDisabled (pre j).core.erase.core := by
    right
    rw [hjLeader]
    exact hpre.ready.leader_signal_zero
  have hrightZero : (pre j).core.erase.core.leader = true →
      (pre j).core.erase.core.label = ⟨0, hpsi⟩ := by
    intro _
    rw [hjLeader]
    exact hpre.ready.leader_zero
  have hlocal : SourceCoveredNoFireOutput hpsi (pre e) (pre j) q := by
    exact wallSweepPreCheckResetPathStall_source_noFire_zeroResponder
      hpsi (pre e) (pre j) hopen
      (by simpa [hneighbor] using hpre.ready.stable_labels e)
      hsource hleftFire hrightFire hrightZero
      (hpre.ready.bullets_zero e) (hpre.ready.bullets_zero j)
  have hsignalSource :
      (pre e).core.erase.core.leader = true ∨
      (pre e).core.erase.core.signal_B = ⟨1, by omega⟩ := by
    right
    exact hpre.frontier_signal_one (by omega) heBound
  have hrightSignalOne : q.2.core.erase.core.signal_B =
      ⟨1, by omega⟩ :=
    hlocal.right_signal_one_of_source hsignalSource
  have hpreLeaderEcho : (pre j).core.erase.core.echo = false := by
    rw [hjLeader]
    exact hpre.leader_echo_false (by omega)
  have hrightResetTrue : q.2.core.erase.core.reset_cmd = true := by
    have h := hlocal.right_reset_exact
    rw [hpreLeaderEcho] at h
    simpa using h
  have hleft : D e = q.1 := by
    simp [D, q, localStep, hneighbor]
  have hright : D j = q.2 := by
    simp [D, q, localStep, hneighbor, Ne.symm hene]
  have hoff : ∀ i, i ≠ e → i ≠ j → D i = pre i := by
    intro i hie hij
    simp [D, localStep, hie, hneighbor, hij]
  have hleaderAt : ∀ i, (D i).core.erase.core.leader =
      (pre i).core.erase.core.leader := by
    intro i
    by_cases hie : i = e
    · subst i; rw [hleft]; exact hlocal.left_leader
    · by_cases hij : i = j
      · subst i; rw [hright]; exact hlocal.right_leader
      · rw [hoff i hie hij]
  have hlabelAt : ∀ i, (D i).core.erase.core.label =
      (pre i).core.erase.core.label := by
    intro i
    by_cases hie : i = e
    · subst i; rw [hleft]; exact hlocal.left_label
    · by_cases hij : i = j
      · subst i; rw [hright]; exact hlocal.right_label
      · rw [hoff i hie hij]
  have hshieldAt : ∀ i, (D i).core.erase.core.shield =
      (pre i).core.erase.core.shield := by
    intro i
    by_cases hie : i = e
    · subst i; rw [hleft]; exact hlocal.left_shield
    · by_cases hij : i = j
      · subst i; rw [hright]; exact hlocal.right_shield
      · rw [hoff i hie hij]
  have hbulletAt : ∀ i,
      (D i).core.erase.core.bullet = ⟨0, by omega⟩ := by
    intro i
    by_cases hie : i = e
    · subst i; rw [hleft]; exact hlocal.left_bullet_zero
    · by_cases hij : i = j
      · subst i; rw [hright]; exact hlocal.right_bullet_zero
      · rw [hoff i hie hij]
        exact hpre.ready.bullets_zero i
  have hpreNeutral : ∀ i, ComparisonNeutral
      (pre i).core.erase.core := by
    intro i
    let k := cwDist ring leader i
    have hkBound : k < n := cwDist_lt ring leader i
    have hpos : groupOffset ring leader k = i := by
      simpa [groupOffset, cwPos] using cwPos_cwDist ring leader i
    rw [← hpos]
    exact hpre.visited_neutral k (by omega) (by omega)
  have hneutralD : ∀ i, ComparisonNeutral
      (D i).core.erase.core := by
    intro i
    by_cases hie : i = e
    · subst i; rw [hleft]; exact hlocal.left_neutral
    · by_cases hij : i = j
      · subst i; rw [hright]; exact hlocal.right_neutral
      · rw [hoff i hie hij]
        exact hpreNeutral i
  have hfollowerReset : ∀ i, i ≠ leader →
      (D i).core.erase.core.reset_cmd = false := by
    intro i hi
    by_cases hie : i = e
    · subst i
      rw [hleft]
      exact hlocal.left_reset_false
    · have hij : i ≠ j := by
        rw [hjLeader]
        exact hi
      rw [hoff i hie hij]
      let k := cwDist ring leader i
      have hkBound : k < n := cwDist_lt ring leader i
      have hpos : groupOffset ring leader k = i := by
        simpa [groupOffset, cwPos] using cwPos_cwDist ring leader i
      have hkPos : 0 < k := by
        have hkNe : k ≠ 0 := by
          intro hkZero
          apply hi
          rw [← hpos, hkZero]
          exact groupOffset_zero_eq ring leader
        omega
      have hkLast : k ≠ n - 1 := by
        intro hk
        apply hie
        rw [← hpos, hk]
      have hkBehind : k < n - 1 := by omega
      rw [← hpos]
      exact hpre.reset_behind k hkBehind
  have hsucc : clockwiseAttemptConfig T ring leader C n = D := by
    have hs := clockwiseAttemptConfig_succ T ring leader C (n - 1)
    have hnEq : n - 1 + 1 = n := by omega
    rw [hnEq] at hs
    exact hs
  rw [hsucc]
  exact {
    stable_labels := by
      intro i
      rw [hlabelAt (ring.rightNeighbor i), hlabelAt i]
      exact hpre.ready.stable_labels i
    leader_alive := by
      rw [hleaderAt leader]
      exact hpre.ready.leader_alive
    leader_zero := by
      rw [hlabelAt leader]
      exact hpre.ready.leader_zero
    unique_leader := by
      intro i hi
      rw [hleaderAt i]
      exact hpre.ready.unique_leader i hi
    leader_unshielded := by
      rw [hshieldAt leader]
      exact hpre.ready.leader_unshielded
    bullets_zero := hbulletAt
    comparison_neutral := hneutralD
    leader_signal_one := by
      rw [← hjLeader, hright]
      exact hrightSignalOne
    leader_reset_true := by
      rw [← hjLeader, hright]
      exact hrightResetTrue
    follower_reset_false := hfollowerReset
    leader_echo_false := by
      rw [← hjLeader, hright]
      exact hlocal.right_echo_false
  }

/-- Weak scheduler-facing projection of the sharp zero-pass endpoint. -/
theorem preCheckReset_zeroRank_fullPass
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (leader : Fin n) (C : EConfig n psi kappa tau)
    (hready : ClockwiseRetryReady hpsi ring leader C)
    (hzero : clockwiseEchoRank ring leader C = 0) :
    ClockwiseRetryDone hpsi ring leader
      (clockwiseAttemptConfig
        (wallSweepPreCheckResetPathStallTransition hpsi kappa tau)
        ring leader C n) :=
  (preCheckReset_zeroRank_fullPass_exact
    hpsi ring hn leader C hready hzero).toClockwiseRetryDone

/-- Concrete source-level attempt contract for the corrected pre-CHECK reset
transition. -/
theorem preCheckResetClockwiseAttemptContract
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (leader : Fin n) :
    ClockwiseAttemptContract
      (wallSweepPreCheckResetPathStallTransition hpsi kappa tau)
      ring hn leader (ClockwiseRetryReady hpsi ring leader)
        (ClockwiseRetryDone hpsi ring leader) :=
  preCheckResetClockwiseAttemptContract_of_zero_rank
    hpsi ring hn leader (ClockwiseRetryDone hpsi ring leader)
      (preCheckReset_zeroRank_fullPass hpsi ring hn leader)

/-- Sharp concrete attempt contract retaining the returned signal/reset fields
needed by the terminal shield edge. -/
theorem preCheckResetClockwiseAttemptContractExact
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (leader : Fin n) :
    ClockwiseAttemptContract
      (wallSweepPreCheckResetPathStallTransition hpsi kappa tau)
      ring hn leader (ClockwiseRetryReady hpsi ring leader)
        (ClockwiseRetryDoneExact hpsi ring leader) :=
  preCheckResetClockwiseAttemptContract_of_zero_rank
    hpsi ring hn leader (ClockwiseRetryDoneExact hpsi ring leader)
      (preCheckReset_zeroRank_fullPass_exact hpsi ring hn leader)

/-! ## Operational scheduler consequences -/

/-- From a retry-ready state, a literal deterministic schedule reaches the
correct zero-rank endpoint within the binary-rank budget. -/
theorem exists_preCheckResetClockwiseRetrySchedule
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (leader : Fin n) (C : EConfig n psi kappa tau)
    (hready : ClockwiseRetryReady hpsi ring leader C) :
    ∃ (word : DetSchedule n) (D : EConfig n psi kappa tau),
      D = runLocalSchedule ring
        (wallSweepPreCheckResetPathStallTransition hpsi kappa tau)
        C word ∧
      word.length ≤ n + (n - 1) * clockwiseEchoRank ring leader C ∧
      ClockwiseRetryDone hpsi ring leader D := by
  exact exists_clockwiseRetrySchedule
    (wallSweepPreCheckResetPathStallTransition hpsi kappa tau)
    ring hn leader (ClockwiseRetryReady hpsi ring leader)
      (ClockwiseRetryDone hpsi ring leader)
      (preCheckResetClockwiseAttemptContract hpsi ring hn leader)
      C hready

/-- The same rank scheduler with the sharp zero-pass endpoint retained. -/
theorem exists_preCheckResetClockwiseRetryScheduleExact
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (leader : Fin n) (C : EConfig n psi kappa tau)
    (hready : ClockwiseRetryReady hpsi ring leader C) :
    ∃ (word : DetSchedule n) (D : EConfig n psi kappa tau),
      D = runLocalSchedule ring
        (wallSweepPreCheckResetPathStallTransition hpsi kappa tau)
        C word ∧
      word.length ≤ n + (n - 1) * clockwiseEchoRank ring leader C ∧
      ClockwiseRetryDoneExact hpsi ring leader D := by
  exact exists_clockwiseRetrySchedule
    (wallSweepPreCheckResetPathStallTransition hpsi kappa tau)
    ring hn leader (ClockwiseRetryReady hpsi ring leader)
      (ClockwiseRetryDoneExact hpsi ring leader)
      (preCheckResetClockwiseAttemptContractExact hpsi ring hn leader)
      C hready

/-- From the weaker seed boundary, one deletion drain followed by rank retry
reaches the corrected endpoint with the one-time path-mass charge. -/
theorem exists_preCheckResetClockwiseRetrySchedule_after_oneDrain
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (leader : Fin n) (C : EConfig n psi kappa tau)
    (hseed : UnshieldedRetrySeed hpsi ring leader C) :
    ∃ (actual : DetSchedule n) (D : EConfig n psi kappa tau),
      D = runLocalSchedule ring
        (wallSweepPreCheckResetPathStallTransition hpsi kappa tau)
        C actual ∧
      actual.length ≤ comparisonPathCount C + n +
        (n - 1) * clockwiseEchoRank ring leader C ∧
      ClockwiseRetryDone hpsi ring leader D := by
  exact exists_clockwiseRetrySchedule_after_oneDrain
    (wallSweepPreCheckResetPathStallTransition hpsi kappa tau)
    ring hn leader (UnshieldedRetrySeed hpsi ring leader)
      (ClockwiseRetryReady hpsi ring leader)
      (ClockwiseRetryDone hpsi ring leader)
      (preCheckResetClockwiseAttemptContract hpsi ring hn leader)
      (preCheckResetOneDrainContract hpsi ring hn leader)
      C hseed

/-- One deletion drain followed by rank retry reaches the sharp zero-pass
endpoint without adding any recursive path-mass charge. -/
theorem exists_preCheckResetClockwiseRetryScheduleExact_after_oneDrain
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (leader : Fin n) (C : EConfig n psi kappa tau)
    (hseed : UnshieldedRetrySeed hpsi ring leader C) :
    ∃ (actual : DetSchedule n) (D : EConfig n psi kappa tau),
      D = runLocalSchedule ring
        (wallSweepPreCheckResetPathStallTransition hpsi kappa tau)
        C actual ∧
      actual.length ≤ comparisonPathCount C + n +
        (n - 1) * clockwiseEchoRank ring leader C ∧
      ClockwiseRetryDoneExact hpsi ring leader D := by
  exact exists_clockwiseRetrySchedule_after_oneDrain
    (wallSweepPreCheckResetPathStallTransition hpsi kappa tau)
    ring hn leader (UnshieldedRetrySeed hpsi ring leader)
      (ClockwiseRetryReady hpsi ring leader)
      (ClockwiseRetryDoneExact hpsi ring leader)
      (preCheckResetClockwiseAttemptContractExact hpsi ring hn leader)
      (preCheckResetOneDrainContract hpsi ring hn leader)
      C hseed

/-! ## Reset-aware self-normalizing follower step -/

/-- One unit for every physical endpoint currently carrying a reset command.
This is the outer rank used to separate leaderless reset drainage from the
later rooted echo/signal scheduler. -/
def resetCommandMass (u : AgentState psi) : Nat :=
  if u.reset_cmd = true then 1 else 0

/-- Number of reset commands in a complete physical configuration. -/
def resetCommandCount (C : EConfig n psi kappa tau) : Nat :=
  (List.ofFn (fun i : Fin n =>
    resetCommandMass (C i).core.erase.core)).sum

/-- A leaderless reset token after a finite clockwise prefix.  The state is
deliberately independent of label alignment: it records only the facts needed
to keep moving the token until either a blocking echo consumes it or a later
label pass manufactures such an echo. -/
structure LeaderlessResetAdvanceState
    (hpsi : psi > 0) (ring : DirectedRing n) (root : Fin n)
    (base current : EConfig n psi kappa tau) (steps : Nat) : Prop where
  steps_le : steps ≤ n
  no_active : NoActiveDeletion current
  leaderless : PPLLPpsiLeaderCreationSchedule.RawLeaderless
    (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig current)
  source_reset :
    (current (groupOffset ring root steps)).core.erase.core.reset_cmd = true
  source_label :
    (current (groupOffset ring root steps)).core.erase.core.label =
      ⟨((base root).core.erase.core.label.val + steps) % psi,
        Nat.mod_lt _ hpsi⟩
  predecessor_echo_of_source_last : 0 < steps →
    (current (groupOffset ring root steps)).core.erase.core.label =
      ⟨psi - 1, by omega⟩ →
    (current (groupOffset ring root (steps - 1))).core.erase.core.echo = true
  reset_count_le : resetCommandCount current ≤ resetCommandCount base
  bullet_count_le :
    PPLLPpsiLeaderCreationRepair.bulletTwoCount current ≤
      PPLLPpsiLeaderCreationRepair.bulletTwoCount base
  untouched_ahead : ∀ k, steps < k → k < n →
    current (groupOffset ring root k) = base (groupOffset ring root k)

/-- Global lift of the exact R55 pair certificate.  This frame deliberately
tracks only facts that hold without a stable-label, bullet, signal, shield, or
write-carrier premise. -/
structure ResetAwareFollowerGlobalStepFrame
    (hpsi : psi > 0) (ring : DirectedRing n)
    (C D : EConfig n psi kappa tau) (e : Fin n) : Prop where
  normalized : ExpiringResetFollowerNormalizedOutput hpsi
    (C e, C (ring.rightNeighbor e))
    (D e, D (ring.rightNeighbor e))
  leader_eq : ∀ i,
    (D i).core.erase.core.leader = (C i).core.erase.core.leader
  off_edge : ∀ i, i ≠ e → i ≠ ring.rightNeighbor e → D i = C i
  no_active : NoActiveDeletion D

set_option maxHeartbeats 2000000 in
/-- One priority-open follower/reset/follower interaction under the complete
reset-aware transition self-normalizes its edge and preserves every leader bit
and global deletion inactivity. -/
theorem resetAwareFollower_localStep_normalizes
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (C : EConfig n psi kappa tau) (e : Fin n)
    (hnoActive : NoActiveDeletion C)
    (hlFollower : (C e).core.erase.core.leader = false)
    (hlReset : (C e).core.erase.core.reset_cmd = true)
    (hrFollower :
      (C (ring.rightNeighbor e)).core.erase.core.leader = false) :
    let D := localStep ring
      (wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
        hpsi kappa tau) C e
    ResetAwareFollowerGlobalStepFrame hpsi ring C D e := by
  let j := ring.rightNeighbor e
  let T := wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
    hpsi kappa tau
  let q := T (C e) (C j)
  let D := localStep ring T C e
  have hene : e ≠ j :=
    Ne.symm (rightNeighbor_ne_self_of_one_lt ring hn e)
  have hopen : WallPriorityOpen (C e) (C j) := by
    simpa [j] using
      WallPriorityOpen.of_noActiveDeletion C hnoActive ring e
  obtain ⟨output, houtput, hnormalized⟩ :=
    wallSweepResetProbePreCheckResetLeaderSinkPathStall_exists_reset_follower_normalization
      hpsi (C e) (C j) hopen hlFollower hlReset
        (by simpa [j] using hrFollower)
  change output = q at houtput
  have hleft : D e = q.1 := by
    simp [D, q, T, localStep, j]
  have hright : D j = q.2 := by
    simp [D, q, T, localStep, j, Ne.symm hene]
  have hoff : ∀ i, i ≠ e → i ≠ j → D i = C i := by
    intro i hie hij
    simp [D, T, localStep, j, hie, hij]
  have hpair : ExpiringResetFollowerNormalizedOutput hpsi
      (C e, C j) (D e, D j) := by
    rw [hleft, hright, ← houtput]
    exact hnormalized
  have hleaderAt : ∀ i,
      (D i).core.erase.core.leader = (C i).core.erase.core.leader := by
    intro i
    by_cases hie : i = e
    · subst i
      rw [hpair.left_follower, hlFollower]
    · by_cases hij : i = j
      · subst i
        rw [hpair.right_follower]
        simpa [j] using hrFollower
      · rw [hoff i hie hij]
  have hnoActiveD : NoActiveDeletion D := by
    intro i
    by_cases hie : i = e
    · subst i
      exact deletionActive_false_of_neutral
        (D e) hpair.control.left_neutral
    · by_cases hij : i = j
      · subst i
        exact deletionActive_false_of_neutral
          (D j) hpair.control.right_neutral
      · rw [hoff i hie hij]
        exact hnoActive i
  change ResetAwareFollowerGlobalStepFrame hpsi ring C D e
  exact {
    normalized := by simpa [j] using hpair
    leader_eq := hleaderAt
    off_edge := by simpa [j] using hoff
    no_active := hnoActiveD }

set_option maxHeartbeats 1000000 in
/-- One reset-aware interaction initiated by a zero-signal leader cannot
increase the global number of live bullets.  Only the scheduled pair can
change, and the physical pair contract supplies its local inequality. -/
theorem resetAwareLeader_signalZero_localStep_bulletTwoCount_le
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (C : EConfig n psi kappa tau) (e : Fin n)
    (hnoActive : NoActiveDeletion C)
    (hlLeader : (C e).core.erase.core.leader = true)
    (hlSignalZero :
      (C e).core.erase.core.signal_B = ⟨0, by omega⟩) :
    let D := localStep ring
      (wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
        hpsi kappa tau) C e
    PPLLPpsiLeaderCreationRepair.bulletTwoCount D ≤
      PPLLPpsiLeaderCreationRepair.bulletTwoCount C := by
  let j := ring.rightNeighbor e
  have hje : j ≠ e := rightNeighbor_ne_self_of_one_lt ring hn e
  let T := wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
    hpsi kappa tau
  let q := T (C e) (C j)
  let D := localStep ring T C e
  have hopen : WallPriorityOpen (C e) (C j) := by
    simpa [j] using
      WallPriorityOpen.of_noActiveDeletion C hnoActive ring e
  have hlocal :
      bulletTwoPairMass q.1.core.erase.core q.2.core.erase.core ≤
        bulletTwoPairMass (C e).core.erase.core (C j).core.erase.core := by
    exact
      (wallSweepResetProbePreCheckResetLeaderSinkPathStall_priority_open_left_leader_signal_zero_bulletTwoPair
        hpsi (C e) (C j) hopen hlLeader hlSignalZero).le
  unfold PPLLPpsiLeaderCreationRepair.bulletTwoCount
  apply PPLLPpsiLeaderCreationRepair.sum_ofFn_le_of_pair_le
    (fun i => bulletTwoMass (D i).core.erase.core)
    (fun i => bulletTwoMass (C i).core.erase.core)
    e j (Ne.symm hje)
  · simpa [D, q, T, localStep, j, hje, bulletTwoPairMass] using hlocal
  · intro i hie hij
    simp [D, localStep, T, j, hie, hij]

set_option maxHeartbeats 1000000 in
/-- An arbitrary-signal leader source can create at most one new live bullet:
the initiator contributes at most one unit, while every live responder output
must already have been live at the input responder. -/
theorem resetAwareLeader_localStep_bulletTwoCount_le_add_one
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (C : EConfig n psi kappa tau) (e : Fin n)
    (hnoActive : NoActiveDeletion C)
    (hlLeader : (C e).core.erase.core.leader = true) :
    let D := localStep ring
      (wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
        hpsi kappa tau) C e
    PPLLPpsiLeaderCreationRepair.bulletTwoCount D ≤
      PPLLPpsiLeaderCreationRepair.bulletTwoCount C + 1 := by
  let j := ring.rightNeighbor e
  have hje : j ≠ e := rightNeighbor_ne_self_of_one_lt ring hn e
  let Tnew :=
    wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
      hpsi kappa tau
  let Told := wallSweepPreCheckResetLeaderSinkPathStallTransition
    hpsi kappa tau
  let qnew := Tnew (C e) (C j)
  let qold := Told (C e) (C j)
  let D := localStep ring Tnew C e
  have hopen : WallPriorityOpen (C e) (C j) := by
    simpa [j] using
      WallPriorityOpen.of_noActiveDeletion C hnoActive ring e
  have hpair : qnew = qold := by
    simpa [qnew, qold, Tnew, Told, j] using
      (wallSweepResetProbePreCheckResetLeaderSinkPathStall_eq_of_left_leader
        hpsi kappa tau (C e) (C j) hlLeader)
  have hleftLe :
      bulletTwoMass qnew.1.core.erase.core ≤ 1 :=
    PPLLPpsiLeaderCreationRepair.bulletTwoMass_le_one
      qnew.1.core.erase.core
  have hrightLe :
      bulletTwoMass qnew.2.core.erase.core ≤
        bulletTwoMass (C j).core.erase.core := by
    by_cases houtLive :
        qnew.2.core.erase.core.bullet = ⟨2, by omega⟩
    · have holdLive :
          qold.2.core.erase.core.bullet = ⟨2, by omega⟩ := by
        rw [← hpair]
        exact houtLive
      have hinLive :=
        wallSweepPreCheckResetLeaderSinkPathStall_priority_open_responder_live_origin
          hpsi (C e) (C j) hopen holdLive
      unfold bulletTwoMass
      rw [if_pos houtLive, if_pos hinLive]
      omega
    · unfold bulletTwoMass
      rw [if_neg houtLive]
      omega
  have hlocal :
      bulletTwoPairMass qnew.1.core.erase.core qnew.2.core.erase.core ≤
        bulletTwoPairMass (C e).core.erase.core (C j).core.erase.core + 1 := by
    unfold bulletTwoPairMass
    omega
  unfold PPLLPpsiLeaderCreationRepair.bulletTwoCount
  apply PPLLPpsiLeaderCreationRepair.sum_ofFn_le_add_one_of_pair_le_add_one
    (fun i => bulletTwoMass (D i).core.erase.core)
    (fun i => bulletTwoMass (C i).core.erase.core)
    e j (Ne.symm hje)
  · simpa [D, qnew, Tnew, localStep, j, hje,
      bulletTwoPairMass] using hlocal
  · intro i hie hij
    simp [D, localStep, Tnew, j, hie, hij]

/-- Every reset-aware step sourced by the named leader clears that leader's
absence signal.  This supplies the zero-signal premise needed by a replay of
the same edge. -/
theorem resetAwareLeader_localStep_signal_zero
    (hpsi : psi > 0) (ring : DirectedRing n)
    (C : EConfig n psi kappa tau) (e : Fin n)
    (hnoActive : NoActiveDeletion C)
    (hlLeader : (C e).core.erase.core.leader = true) :
    let D := localStep ring
      (wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
        hpsi kappa tau) C e
    (D e).core.erase.core.signal_B = ⟨0, by omega⟩ := by
  let j := ring.rightNeighbor e
  let T := wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
    hpsi kappa tau
  let q := T (C e) (C j)
  let D := localStep ring T C e
  have hopen : WallPriorityOpen (C e) (C j) := by
    simpa [j] using
      WallPriorityOpen.of_noActiveDeletion C hnoActive ring e
  have hlocal :=
    wallSweepResetProbePreCheckResetLeaderSinkPathStall_priority_open_left_signal_zero_of_left_leader
      hpsi (C e) (C j) hopen hlLeader
  change q.1.core.erase.core.signal_B = ⟨0, by omega⟩ at hlocal
  simpa [D, q, T, localStep] using hlocal

set_option maxHeartbeats 1000000 in
/-- A reset-aware step sourced by an existing leader preserves global deletion
inactivity.  The rooted source-cleanup contract makes both touched endpoints
comparison-neutral, and every other site is framed exactly. -/
theorem resetAwareLeader_localStep_noActive
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (C : EConfig n psi kappa tau) (e : Fin n)
    (hnoActive : NoActiveDeletion C)
    (hlLeader : (C e).core.erase.core.leader = true) :
    let D := localStep ring
      (wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
        hpsi kappa tau) C e
    NoActiveDeletion D := by
  let j := ring.rightNeighbor e
  have hje : j ≠ e := rightNeighbor_ne_self_of_one_lt ring hn e
  have hopen : WallPriorityOpen (C e) (C j) := by
    simpa [j] using
      WallPriorityOpen.of_noActiveDeletion C hnoActive ring e
  let Tnew :=
    wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
      hpsi kappa tau
  let Told := wallSweepPreCheckResetLeaderSinkPathStallTransition
    hpsi kappa tau
  let Dnew := localStep ring Tnew C e
  let Dold := localStep ring Told C e
  have hpair : Tnew (C e) (C j) = Told (C e) (C j) := by
    simpa [Tnew, Told, j] using
      (wallSweepResetProbePreCheckResetLeaderSinkPathStall_eq_of_left_leader
        hpsi kappa tau (C e) (C j) hlLeader)
  have hD : Dnew = Dold :=
    localStep_eq_of_pair_eq ring Tnew Told C e
      (by simpa [j] using hpair)
  have hcleanup :=
    wallSweepPreCheckResetLeaderSinkPathStall_priority_open_leader_source_cleanup
      hpsi (C e) (C j) hopen hlLeader
  have hleftNeutral : ComparisonNeutral
      (Dold e).core.erase.core := by
    simpa [Dold, Told, j, localStep] using hcleanup.1
  have hrightNeutral : ComparisonNeutral
      (Dold j).core.erase.core := by
    simpa [Dold, Told, j, localStep, hje] using hcleanup.2.1
  have hnoActiveOld : NoActiveDeletion Dold := by
    intro i
    by_cases hie : i = e
    · subst i
      exact deletionActive_false_of_neutral (Dold e) hleftNeutral
    · by_cases hij : i = j
      · subst i
        exact deletionActive_false_of_neutral (Dold j) hrightNeutral
      · have hsame : Dold i = C i := by
          simp [Dold, Told, localStep, j, hie, hij]
        rw [hsame]
        exact hnoActive i
  change NoActiveDeletion Dnew
  rw [hD]
  exact hnoActiveOld

/-- A reset-aware step sourced by an existing leader frames that leader's
physical label. -/
theorem resetAwareLeader_localStep_label_eq
    (hpsi : psi > 0) (ring : DirectedRing n)
    (C : EConfig n psi kappa tau) (e : Fin n)
    (hnoActive : NoActiveDeletion C)
    (hlLeader : (C e).core.erase.core.leader = true)
    (hrFollower :
      (C (ring.rightNeighbor e)).core.erase.core.leader = false) :
    let D := localStep ring
      (wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
        hpsi kappa tau) C e
    (D e).core.erase.core.label = (C e).core.erase.core.label := by
  let j := ring.rightNeighbor e
  let T := wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
    hpsi kappa tau
  let D := localStep ring T C e
  have hopen : WallPriorityOpen (C e) (C j) := by
    simpa [j] using
      WallPriorityOpen.of_noActiveDeletion C hnoActive ring e
  have hlabels :=
    wallSweepResetProbePreCheckResetLeaderSinkPathStall_source_follower_labels
      hpsi (C e) (C j) hopen (.inl hlLeader)
        (by simpa [j] using hrFollower)
  have hleft : D e = (T (C e) (C j)).1 := by
    simp [D, T, localStep, j]
  change (D e).core.erase.core.label = (C e).core.erase.core.label
  rw [hleft]
  exact hlabels.1

set_option maxHeartbeats 1000000 in
/-- A reset-aware interaction from a shielded leader to a follower preserves
the complete initiator anchor.  The integrated transition agrees with the
rooted leader-sink transition on a leader source, and the rooted physical
contract carries both the leader and shield fields through expiry. -/
theorem resetAwareLeader_localStep_initiator_anchor
    (hpsi : psi > 0) (ring : DirectedRing n)
    (C : EConfig n psi kappa tau) (e : Fin n)
    (hnoActive : NoActiveDeletion C)
    (hanchor : InitiatorAnchor (C e).core.erase.core)
    (hrFollower :
      (C (ring.rightNeighbor e)).core.erase.core.leader = false) :
    let D := localStep ring
      (wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
        hpsi kappa tau) C e
    InitiatorAnchor (D e).core.erase.core := by
  let j := ring.rightNeighbor e
  let T := wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
    hpsi kappa tau
  let D := localStep ring T C e
  have hopen : WallPriorityOpen (C e) (C j) := by
    simpa [j] using
      WallPriorityOpen.of_noActiveDeletion C hnoActive ring e
  have hroot :=
    wallSweepPreCheckResetLeaderSinkPathStall_priority_open_initiator_anchor_of_responder_follower
      hpsi (C e) (C j) hopen hanchor (by simpa [j] using hrFollower)
  have hintegrated : InitiatorAnchor
      (T (C e) (C j)).1.core.erase.core := by
    change InitiatorAnchor
      (wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
        hpsi kappa tau (C e) (C j)).1.core.erase.core
    rw [wallSweepResetProbePreCheckResetLeaderSinkPathStall_eq_of_left_leader
      hpsi kappa tau (C e) (C j) hanchor.1]
    exact hroot
  simpa [D, T, localStep, j] using hintegrated

set_option maxHeartbeats 1000000 in
/-- The same source-covered leader interaction keeps its responder a
follower.  This is the endpoint fact needed to replay the anchor contract on
the same edge. -/
theorem resetAwareLeader_localStep_right_follower
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (C : EConfig n psi kappa tau) (e : Fin n)
    (hnoActive : NoActiveDeletion C)
    (hlLeader : (C e).core.erase.core.leader = true)
    (hrFollower :
      (C (ring.rightNeighbor e)).core.erase.core.leader = false) :
    let D := localStep ring
      (wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
        hpsi kappa tau) C e
    (D (ring.rightNeighbor e)).core.erase.core.leader = false := by
  let j := ring.rightNeighbor e
  let T := wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
    hpsi kappa tau
  let D := localStep ring T C e
  have hje : j ≠ e := rightNeighbor_ne_self_of_one_lt ring hn e
  have hopen : WallPriorityOpen (C e) (C j) := by
    simpa [j] using
      WallPriorityOpen.of_noActiveDeletion C hnoActive ring e
  have hroot :=
    wallSweepPreCheckResetLeaderSinkPathStall_priority_open_responder_follower_of_initiator_leader
      hpsi (C e) (C j) hopen hlLeader (by simpa [j] using hrFollower)
  have hintegrated :
      (T (C e) (C j)).2.core.erase.core.leader = false := by
    change
      (wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
        hpsi kappa tau (C e) (C j)).2.core.erase.core.leader = false
    rw [wallSweepResetProbePreCheckResetLeaderSinkPathStall_eq_of_left_leader
      hpsi kappa tau (C e) (C j) hlLeader]
    exact hroot
  simpa [D, T, localStep, j, hje] using hintegrated

set_option maxHeartbeats 2000000 in
/-- One reset-aware leader edge with source signal one reaches a protected
label-zero leader without requiring input label alignment.  The local fire
contract supplies the anchor; uniqueness is lifted by the exact local-step
frame. -/
theorem resetAwareLeader_signalOne_localStep_protected
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (C : EConfig n psi kappa tau) (leader : Fin n)
    (hnoActive : NoActiveDeletion C)
    (hunique : hasUniqueLeader n
      (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig C))
    (hleader : (C leader).core.erase.core.leader = true)
    (hzero : (C leader).core.erase.core.label = ⟨0, hpsi⟩)
    (hsignal : (C leader).core.erase.core.signal_B = ⟨1, by omega⟩)
    (hrFollower :
      (C (ring.rightNeighbor leader)).core.erase.core.leader = false) :
    let D := localStep ring
      (wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
        hpsi kappa tau) C leader
    NoActiveDeletion D ∧
      hasUniqueLeader n
        (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig D) ∧
      PPLLWallSweepRestartableProtected.ProtectedLeaderAt
        hpsi D leader := by
  let j := ring.rightNeighbor leader
  let T := wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
    hpsi kappa tau
  let D := localStep ring T C leader
  have hje : j ≠ leader :=
    rightNeighbor_ne_self_of_one_lt ring hn leader
  have hopen : WallPriorityOpen (C leader) (C j) := by
    simpa [j] using
      WallPriorityOpen.of_noActiveDeletion C hnoActive ring leader
  have hpairAnchor :=
    wallSweepResetProbePreCheckResetLeaderSinkPathStall_priority_open_initiator_anchor_of_signal_one
      hpsi (C leader) (C j) hopen hleader hsignal
        (by simpa [j] using hrFollower)
  change InitiatorAnchor
    (T (C leader) (C j)).1.core.erase.core at hpairAnchor
  have hanchorD : InitiatorAnchor (D leader).core.erase.core := by
    simpa [D, T, localStep, j] using hpairAnchor
  have hnoActiveD : NoActiveDeletion D :=
    resetAwareLeader_localStep_noActive
      hpsi ring hn C leader hnoActive hleader
  have hrightFollowerD :
      (D j).core.erase.core.leader = false := by
    simpa [j] using
      (resetAwareLeader_localStep_right_follower
        hpsi ring hn C leader hnoActive hleader hrFollower)
  obtain ⟨only, honlyLeader, honly⟩ := hunique
  have hleaderOnly : leader = only := by
    apply honly leader
    change (C leader).core.erase.core.leader = true
    exact hleader
  have huniqueD : hasUniqueLeader n
      (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig D) := by
    refine ⟨leader, hanchorD.1, ?_⟩
    intro i hi
    by_cases hie : i = leader
    · exact hie
    · by_cases hij : i = j
      · subst i
        change (D j).core.erase.core.leader = true at hi
        rw [hrightFollowerD] at hi
        contradiction
      · have hsame : D i = C i := by
          simp [D, T, localStep, j, hie, hij]
        have hiC : (C i).core.erase.core.leader = true := by
          change (D i).core.erase.core.leader = true at hi
          rwa [hsame] at hi
        exact (honly i hiC).trans hleaderOnly.symm
  have hlabelD := resetAwareLeader_localStep_label_eq
    hpsi ring C leader hnoActive hleader hrFollower
  change (D leader).core.erase.core.label =
    (C leader).core.erase.core.label at hlabelD
  exact ⟨hnoActiveD, huniqueD,
    ⟨hanchorD, hlabelD.trans hzero⟩⟩

set_option maxHeartbeats 2000000 in
/-- One reset-aware attempt of a unique leader against a live follower has
the exact retry dichotomy used by the outer scheduler.  If the leader
survives, the live responder remains present and therefore the output leader
is shielded.  Otherwise the configuration is leaderless and the global live
count decreases strictly. -/
theorem resetAwareLeader_liveResponder_attempt
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (C : EConfig n psi kappa tau) (leader : Fin n)
    (hnoActive : NoActiveDeletion C)
    (hunique : hasUniqueLeader n
      (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig C))
    (hleader : (C leader).core.erase.core.leader = true)
    (hrLive :
      (C (ring.rightNeighbor leader)).core.erase.core.bullet =
        ⟨2, by omega⟩) :
    let D := localStep ring
      (wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
        hpsi kappa tau) C leader
    NoActiveDeletion D ∧
      (D leader).core.erase.core.label =
        (C leader).core.erase.core.label ∧
      (D leader).core.erase.core.signal_B = ⟨0, by omega⟩ ∧
      ((hasUniqueLeader n
          (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig D) ∧
          (D leader).core.erase.core.leader = true ∧
          (D leader).core.erase.core.shield = true ∧
          (D (ring.rightNeighbor leader)).core.erase.core.bullet =
            ⟨2, by omega⟩) ∨
        (RawLeaderless
            (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig D) ∧
          PPLLPpsiLeaderCreationRepair.bulletTwoCount D <
            PPLLPpsiLeaderCreationRepair.bulletTwoCount C)) := by
  let j := ring.rightNeighbor leader
  have hje : j ≠ leader :=
    rightNeighbor_ne_self_of_one_lt ring hn leader
  have hjFollower : (C j).core.erase.core.leader = false := by
    obtain ⟨only, _honlyLeader, honly⟩ := hunique
    cases hj : (C j).core.erase.core.leader with
    | false => rfl
    | true =>
        have hjOnly : j = only := by
          apply honly j
          change (C j).core.erase.core.isLeader
          change (C j).core.erase.core.leader = true
          exact hj
        have hleaderOnly : leader = only := by
          apply honly leader
          change (C leader).core.erase.core.isLeader
          change (C leader).core.erase.core.leader = true
          exact hleader
        exact False.elim (hje (hjOnly.trans hleaderOnly.symm))
  have hopen : WallPriorityOpen (C leader) (C j) := by
    simpa [j] using
      WallPriorityOpen.of_noActiveDeletion C hnoActive ring leader
  let Tnew :=
    wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
      hpsi kappa tau
  let Told := wallSweepPreCheckResetLeaderSinkPathStallTransition
    hpsi kappa tau
  let Dnew := localStep ring Tnew C leader
  let Dold := localStep ring Told C leader
  have hpair : Tnew (C leader) (C j) =
      Told (C leader) (C j) := by
    simpa [Tnew, Told, j] using
      (wallSweepResetProbePreCheckResetLeaderSinkPathStall_eq_of_left_leader
        hpsi kappa tau (C leader) (C j) hleader)
  have hD : Dnew = Dold :=
    localStep_eq_of_pair_eq ring Tnew Told C leader
      (by simpa [j] using hpair)
  have hnoActiveD : NoActiveDeletion Dnew :=
    resetAwareLeader_localStep_noActive
      hpsi ring hn C leader hnoActive hleader
  have hlabelD : (Dnew leader).core.erase.core.label =
      (C leader).core.erase.core.label :=
    resetAwareLeader_localStep_label_eq
      hpsi ring C leader hnoActive hleader (by simpa [j] using hjFollower)
  have hsignalD : (Dnew leader).core.erase.core.signal_B =
      ⟨0, by omega⟩ :=
    resetAwareLeader_localStep_signal_zero
      hpsi ring C leader hnoActive hleader
  have hcycle :=
    PPLLPpsiLeaderCreationRepair.localStepLeaderSink_unique_initiator_survives_or_leaderless_rank_lt
      hpsi kappa tau ring hn C leader hunique hleader
        (by simpa [j] using hopen)
  change
    (hasUniqueLeader n
        (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig Dold) ∧
      (Dold leader).core.erase.core.leader = true) ∨
    (RawLeaderless
        (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig Dold) ∧
      PPLLPpsiLeaderCreationRepair.bulletTwoCount Dold <
        PPLLPpsiLeaderCreationRepair.bulletTwoCount C) at hcycle
  refine ⟨hnoActiveD, hlabelD, hsignalD, ?_⟩
  rcases hcycle with hsurvives | hleaderless
  · have huniqueD : hasUniqueLeader n
        (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig Dnew) := by
      rw [hD]
      exact hsurvives.1
    have hleaderD : (Dnew leader).core.erase.core.leader = true := by
      rw [hD]
      exact hsurvives.2
    have hpairLeader :
        (Tnew (C leader) (C j)).1.core.erase.core.leader = true := by
      simpa [Dnew, Tnew, j, localStep] using hleaderD
    have hrightLivePair :=
      wallSweepResetProbePreCheckResetLeaderSinkPathStall_priority_open_survivor_preserves_responder_live
        hpsi (C leader) (C j) hopen hleader hjFollower
          (by simpa [j] using hrLive) hpairLeader
    have hrightLiveD : (Dnew j).core.erase.core.bullet =
        ⟨2, by omega⟩ := by
      simpa [Dnew, Tnew, j, localStep, hje] using hrightLivePair
    have hrightLiveOld : (Dold j).core.erase.core.bullet =
        ⟨2, by omega⟩ := by
      rw [← hD]
      exact hrightLiveD
    have hpairLeaderOld :
        (Told (C leader) (C j)).1.core.erase.core.leader = true := by
      simpa [Dold, Told, j, localStep] using hsurvives.2
    have hsafePair :=
      wallSweepPreCheckResetLeaderSinkPathStall_priority_open_survivor_safe
        hpsi (C leader) (C j) hopen hleader hjFollower hpairLeaderOld
    have hshieldD : (Dnew leader).core.erase.core.shield = true := by
      have hrightLiveOldPair :
          (Told (C leader) (C j)).2.core.erase.core.bullet =
            ⟨2, by omega⟩ := by
        simpa [Dold, Told, j, localStep, hje] using hrightLiveOld
      have hshieldPair := hsafePair hrightLiveOldPair
      rw [hD]
      simpa [Dold, Told, j, localStep] using hshieldPair
    exact .inl ⟨huniqueD, hleaderD, hshieldD,
      by simpa [j] using hrightLiveD⟩
  · right
    constructor
    · change RawLeaderless
        (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig Dnew)
      rw [hD]
      exact hleaderless.1
    · change PPLLPpsiLeaderCreationRepair.bulletTwoCount Dnew <
        PPLLPpsiLeaderCreationRepair.bulletTwoCount C
      rw [hD]
      exact hleaderless.2

set_option maxHeartbeats 2000000 in
/-- A live-responder leader attempt exposes the exact normalized endpoint on
the survivor branch.  The live responder is retained explicitly; it is the
reason the normalized endpoint's collision-safety field yields a shielded
leader rather than live-bullet cleanup. -/
theorem resetAwareLeader_liveResponder_normalized_or_leaderless
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (C : EConfig n psi kappa tau) (leader : Fin n)
    (hnoActive : NoActiveDeletion C)
    (hunique : hasUniqueLeader n
      (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig C))
    (hleader : (C leader).core.erase.core.leader = true)
    (hrLive :
      (C (ring.rightNeighbor leader)).core.erase.core.bullet =
        ⟨2, by omega⟩) :
    let D := localStep ring
      (wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
        hpsi kappa tau) C leader
    NoActiveDeletion D ∧
      (D leader).core.erase.core.label =
        (C leader).core.erase.core.label ∧
      (D leader).core.erase.core.signal_B = ⟨0, by omega⟩ ∧
      ((PPLLPpsiLeaderCreationRepair.NormalizedOutgoingUniqueLeaderAt
          hpsi ring D leader ∧
          (D (ring.rightNeighbor leader)).core.erase.core.bullet =
            ⟨2, by omega⟩) ∨
        (RawLeaderless
            (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig D) ∧
          PPLLPpsiLeaderCreationRepair.bulletTwoCount D <
            PPLLPpsiLeaderCreationRepair.bulletTwoCount C)) := by
  let j := ring.rightNeighbor leader
  have hje : j ≠ leader :=
    rightNeighbor_ne_self_of_one_lt ring hn leader
  have hjFollower : (C j).core.erase.core.leader = false := by
    obtain ⟨only, _honlyLeader, honly⟩ := hunique
    cases hj : (C j).core.erase.core.leader with
    | false => rfl
    | true =>
        have hjOnly : j = only := by
          apply honly j
          change (C j).core.erase.core.isLeader
          change (C j).core.erase.core.leader = true
          exact hj
        have hleaderOnly : leader = only := by
          apply honly leader
          change (C leader).core.erase.core.isLeader
          change (C leader).core.erase.core.leader = true
          exact hleader
        exact False.elim (hje (hjOnly.trans hleaderOnly.symm))
  let Tnew :=
    wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
      hpsi kappa tau
  let Told := wallSweepPreCheckResetLeaderSinkPathStallTransition
    hpsi kappa tau
  let Dnew := localStep ring Tnew C leader
  let Dold := localStep ring Told C leader
  have hpair : Tnew (C leader) (C j) =
      Told (C leader) (C j) := by
    simpa [Tnew, Told, j] using
      (wallSweepResetProbePreCheckResetLeaderSinkPathStall_eq_of_left_leader
        hpsi kappa tau (C leader) (C j) hleader)
  have hD : Dnew = Dold :=
    localStep_eq_of_pair_eq ring Tnew Told C leader
      (by simpa [j] using hpair)
  have hattempt := resetAwareLeader_liveResponder_attempt
    hpsi ring hn C leader hnoActive hunique hleader hrLive
  change NoActiveDeletion Dnew ∧
      (Dnew leader).core.erase.core.label =
        (C leader).core.erase.core.label ∧
      (Dnew leader).core.erase.core.signal_B = ⟨0, by omega⟩ ∧
      ((hasUniqueLeader n
          (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig Dnew) ∧
          (Dnew leader).core.erase.core.leader = true ∧
          (Dnew leader).core.erase.core.shield = true ∧
          (Dnew j).core.erase.core.bullet = ⟨2, by omega⟩) ∨
        (RawLeaderless
            (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig Dnew) ∧
          PPLLPpsiLeaderCreationRepair.bulletTwoCount Dnew <
            PPLLPpsiLeaderCreationRepair.bulletTwoCount C)) at hattempt
  refine ⟨hattempt.1, hattempt.2.1, hattempt.2.2.1, ?_⟩
  rcases hattempt.2.2.2 with hsurvives | hleaderless
  · have houtOld : (Dold leader).core.erase.core.leader = true := by
      rw [← hD]
      exact hsurvives.2.1
    have hnormalOld :=
      PPLLPpsiLeaderCreationRepair.leaderStep_survivor_to_normalizedOutgoingUniqueLeaderAt
        hpsi ring hn C leader hnoActive hunique hleader
          (by simpa [j] using hjFollower)
          (by simpa [Dold, Told] using houtOld)
    change PPLLPpsiLeaderCreationRepair.NormalizedOutgoingUniqueLeaderAt
      hpsi ring Dold leader at hnormalOld
    have hnormalNew :
        PPLLPpsiLeaderCreationRepair.NormalizedOutgoingUniqueLeaderAt
          hpsi ring Dnew leader := by
      rw [hD]
      exact hnormalOld
    exact .inl ⟨hnormalNew, by simpa [j] using hsurvives.2.2.2⟩
  · exact .inr hleaderless

set_option maxHeartbeats 3000000 in
/-- From a live immediate responder, the actual integrated leader edge either
dies with strict global live-count descent after one interaction, or two
interactions establish an authenticated reset frontier while retaining the
same live responder.  In the latter branch the frontier safety implication
therefore certifies the surviving leader's shield. -/
theorem resetAwareLeader_liveResponder_frontier_or_leaderless
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (C : EConfig n psi kappa tau) (leader : Fin n)
    (hnoActive : NoActiveDeletion C)
    (hunique : hasUniqueLeader n
      (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig C))
    (hleader : (C leader).core.erase.core.leader = true)
    (hrLive :
      (C (ring.rightNeighbor leader)).core.erase.core.bullet =
        ⟨2, by omega⟩) :
    let T :=
      wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
        hpsi kappa tau
    let D := localStep ring T C leader
    let E := localStep ring T D leader
    ((PPLLPpsiLeaderCreationRepair.OutgoingResetFrontierUniqueLeaderAt
          hpsi ring E leader ∧
        (E (ring.rightNeighbor leader)).core.erase.core.bullet =
          ⟨2, by omega⟩ ∧
        (E leader).core.erase.core.label =
          (C leader).core.erase.core.label ∧
        (E leader).core.erase.core.signal_B = ⟨0, by omega⟩) ∨
      (RawLeaderless
          (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig D) ∧
        PPLLPpsiLeaderCreationRepair.bulletTwoCount D <
          PPLLPpsiLeaderCreationRepair.bulletTwoCount C)) := by
  let j := ring.rightNeighbor leader
  have hje : j ≠ leader :=
    rightNeighbor_ne_self_of_one_lt ring hn leader
  let Tnew :=
    wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
      hpsi kappa tau
  let Told := wallSweepPreCheckResetLeaderSinkPathStallTransition
    hpsi kappa tau
  let Dnew := localStep ring Tnew C leader
  have hfirst := resetAwareLeader_liveResponder_normalized_or_leaderless
    hpsi ring hn C leader hnoActive hunique hleader hrLive
  change NoActiveDeletion Dnew ∧
      (Dnew leader).core.erase.core.label =
        (C leader).core.erase.core.label ∧
      (Dnew leader).core.erase.core.signal_B = ⟨0, by omega⟩ ∧
      ((PPLLPpsiLeaderCreationRepair.NormalizedOutgoingUniqueLeaderAt
          hpsi ring Dnew leader ∧
          (Dnew j).core.erase.core.bullet = ⟨2, by omega⟩) ∨
        (RawLeaderless
            (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig Dnew) ∧
          PPLLPpsiLeaderCreationRepair.bulletTwoCount Dnew <
            PPLLPpsiLeaderCreationRepair.bulletTwoCount C)) at hfirst
  rcases hfirst.2.2.2 with hnormalized | hleaderless
  · left
    have hnormalFields := hnormalized.1
    obtain ⟨hnoActiveD, _huniqueD, hleaderD, hjFollowerD,
        _halignedD, _hleftProbeD, _hrightProbeD,
        _hleftNeutralD, _hrightNeutralD, _hleftResetD,
        _hleftEchoD, _hrightEchoD, _hsafeD⟩ := hnormalFields
    let Enew := localStep ring Tnew Dnew leader
    let Eold := localStep ring Told Dnew leader
    have hpair : Tnew (Dnew leader) (Dnew j) =
        Told (Dnew leader) (Dnew j) := by
      simpa [Tnew, Told, j] using
        (wallSweepResetProbePreCheckResetLeaderSinkPathStall_eq_of_left_leader
          hpsi kappa tau (Dnew leader) (Dnew j) hleaderD)
    have hE : Enew = Eold :=
      localStep_eq_of_pair_eq ring Tnew Told Dnew leader
        (by simpa [j] using hpair)
    have hfrontierOld :=
      PPLLPpsiLeaderCreationRepair.normalizedOutgoingUniqueLeaderAt_replay_reset_handoff
        hpsi ring hn Dnew leader hnormalized.1
    change PPLLPpsiLeaderCreationRepair.OutgoingResetFrontierUniqueLeaderAt
      hpsi ring Eold leader at hfrontierOld
    have hfrontierNew :
        PPLLPpsiLeaderCreationRepair.OutgoingResetFrontierUniqueLeaderAt
          hpsi ring Enew leader := by
      rw [hE]
      exact hfrontierOld
    have hopenD : WallPriorityOpen (Dnew leader) (Dnew j) := by
      simpa [j] using
        WallPriorityOpen.of_noActiveDeletion Dnew hnoActiveD ring leader
    have houtLeaderPair :
        (Tnew (Dnew leader) (Dnew j)).1.core.erase.core.leader = true := by
      have houtLeader : (Enew leader).core.erase.core.leader = true :=
        hfrontierNew.2.2.1
      simpa [Enew, Tnew, j, localStep] using houtLeader
    have hrightLivePair :=
      wallSweepResetProbePreCheckResetLeaderSinkPathStall_priority_open_survivor_preserves_responder_live
        hpsi (Dnew leader) (Dnew j) hopenD hleaderD
          (by simpa [j] using hjFollowerD)
          (by simpa [j] using hnormalized.2) houtLeaderPair
    have hrightLiveE : (Enew j).core.erase.core.bullet =
        ⟨2, by omega⟩ := by
      simpa [Enew, Tnew, j, localStep, hje] using hrightLivePair
    have hlabelE : (Enew leader).core.erase.core.label =
        (C leader).core.erase.core.label := by
      have hlabelSecond := resetAwareLeader_localStep_label_eq
        hpsi ring Dnew leader hnoActiveD hleaderD
          (by simpa [j] using hjFollowerD)
      change (Enew leader).core.erase.core.label =
        (Dnew leader).core.erase.core.label at hlabelSecond
      exact hlabelSecond.trans hfirst.2.1
    have hsignalE : (Enew leader).core.erase.core.signal_B =
        ⟨0, by omega⟩ :=
      resetAwareLeader_localStep_signal_zero
        hpsi ring Dnew leader hnoActiveD hleaderD
    exact ⟨hfrontierNew, by simpa [j] using hrightLiveE,
      hlabelE, hsignalE⟩
  · exact .inr hleaderless

set_option maxHeartbeats 1000000 in
/-- One reset-aware follower/reset/follower step cannot increase the global
number of live bullets.  The local pair inequality is lifted by exact framing
of every site outside the scheduled edge. -/
theorem resetAwareFollower_localStep_bulletTwoCount_le
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (C : EConfig n psi kappa tau) (e : Fin n)
    (hnoActive : NoActiveDeletion C)
    (hlFollower : (C e).core.erase.core.leader = false)
    (hlReset : (C e).core.erase.core.reset_cmd = true)
    (hrFollower :
      (C (ring.rightNeighbor e)).core.erase.core.leader = false) :
    let D := localStep ring
      (wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
        hpsi kappa tau) C e
    PPLLPpsiLeaderCreationRepair.bulletTwoCount D ≤
      PPLLPpsiLeaderCreationRepair.bulletTwoCount C := by
  let j := ring.rightNeighbor e
  have hje : j ≠ e := rightNeighbor_ne_self_of_one_lt ring hn e
  let T := wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
    hpsi kappa tau
  let q := T (C e) (C j)
  let D := localStep ring T C e
  have hopen : WallPriorityOpen (C e) (C j) := by
    simpa [j] using
      WallPriorityOpen.of_noActiveDeletion C hnoActive ring e
  have hlocal :
      bulletTwoPairMass q.1.core.erase.core q.2.core.erase.core ≤
        bulletTwoPairMass (C e).core.erase.core (C j).core.erase.core := by
    exact
      (wallSweepResetProbePreCheckResetLeaderSinkPathStall_priority_open_reset_follower_bulletTwoPair
        hpsi (C e) (C j) hopen hlFollower hlReset
          (by simpa [j] using hrFollower)).le
  unfold PPLLPpsiLeaderCreationRepair.bulletTwoCount
  apply PPLLPpsiLeaderCreationRepair.sum_ofFn_le_of_pair_le
    (fun i => bulletTwoMass (D i).core.erase.core)
    (fun i => bulletTwoMass (C i).core.erase.core)
    e j (Ne.symm hje)
  · simpa [D, q, T, localStep, j, hje, bulletTwoPairMass] using hlocal
  · intro i hie hij
    simp [D, localStep, T, j, hie, hij]

set_option maxHeartbeats 1000000 in
/-- A live bullet at the responder of a reset-aware follower edge moves
exactly one edge counterclockwise and is cleared at its old site. -/
theorem resetAwareFollower_localStep_live_bullet_shifts_left
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (C : EConfig n psi kappa tau) (e : Fin n)
    (hnoActive : NoActiveDeletion C)
    (hlFollower : (C e).core.erase.core.leader = false)
    (hlReset : (C e).core.erase.core.reset_cmd = true)
    (hrFollower :
      (C (ring.rightNeighbor e)).core.erase.core.leader = false)
    (hrLive :
      (C (ring.rightNeighbor e)).core.erase.core.bullet = ⟨2, by omega⟩) :
    let D := localStep ring
      (wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
        hpsi kappa tau) C e
    (D e).core.erase.core.bullet = ⟨2, by omega⟩ ∧
      (D (ring.rightNeighbor e)).core.erase.core.bullet =
        ⟨0, by omega⟩ := by
  let j := ring.rightNeighbor e
  have hje : j ≠ e := rightNeighbor_ne_self_of_one_lt ring hn e
  let T := wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
    hpsi kappa tau
  let q := T (C e) (C j)
  let D := localStep ring T C e
  have hopen : WallPriorityOpen (C e) (C j) := by
    simpa [j] using
      WallPriorityOpen.of_noActiveDeletion C hnoActive ring e
  have hlocal :=
    wallSweepResetProbePreCheckResetLeaderSinkPathStall_priority_open_reset_follower_live_bullets
      hpsi (C e) (C j) hopen hlFollower hlReset
        (by simpa [j] using hrFollower) (by simpa [j] using hrLive)
  change q.1.core.erase.core.bullet = ⟨2, by omega⟩ ∧
      q.2.core.erase.core.bullet = ⟨0, by omega⟩ at hlocal
  simpa [D, q, T, localStep, j, hje] using hlocal


set_option maxHeartbeats 1000000 in
/-- Directional refinement of live-bullet mass nonincrease.  A reset-aware
follower step either strictly consumes a live bullet globally, or preserves
the global count while moving the responder bullet one edge left and clearing
its former site. -/
theorem resetAwareFollower_localStep_liveBullet_shift_or_count_lt
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (C : EConfig n psi kappa tau) (e : Fin n)
    (hnoActive : NoActiveDeletion C)
    (hlFollower : (C e).core.erase.core.leader = false)
    (hlReset : (C e).core.erase.core.reset_cmd = true)
    (hrFollower :
      (C (ring.rightNeighbor e)).core.erase.core.leader = false)
    (hrLive :
      (C (ring.rightNeighbor e)).core.erase.core.bullet = ⟨2, by omega⟩) :
    let D := localStep ring
      (wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
        hpsi kappa tau) C e
    PPLLPpsiLeaderCreationRepair.bulletTwoCount D <
        PPLLPpsiLeaderCreationRepair.bulletTwoCount C ∨
      ((D e).core.erase.core.bullet = ⟨2, by omega⟩ ∧
        (D (ring.rightNeighbor e)).core.erase.core.bullet ≠
          ⟨2, by omega⟩ ∧
        PPLLPpsiLeaderCreationRepair.bulletTwoCount D =
          PPLLPpsiLeaderCreationRepair.bulletTwoCount C) := by
  let D := localStep ring
    (wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
      hpsi kappa tau) C e
  have hle := resetAwareFollower_localStep_bulletTwoCount_le
    hpsi ring hn C e hnoActive hlFollower hlReset hrFollower
  have hshift := resetAwareFollower_localStep_live_bullet_shifts_left
    hpsi ring hn C e hnoActive hlFollower hlReset hrFollower hrLive
  change PPLLPpsiLeaderCreationRepair.bulletTwoCount D ≤
    PPLLPpsiLeaderCreationRepair.bulletTwoCount C at hle
  change (D e).core.erase.core.bullet = ⟨2, by omega⟩ ∧
    (D (ring.rightNeighbor e)).core.erase.core.bullet =
      ⟨0, by omega⟩ at hshift
  by_cases hlt : PPLLPpsiLeaderCreationRepair.bulletTwoCount D <
      PPLLPpsiLeaderCreationRepair.bulletTwoCount C
  · exact .inl hlt
  · right
    refine ⟨hshift.1, ?_, ?_⟩
    · rw [hshift.2]
      simp
    · change PPLLPpsiLeaderCreationRepair.bulletTwoCount D =
        PPLLPpsiLeaderCreationRepair.bulletTwoCount C
      exact Nat.le_antisymm hle (Nat.le_of_not_gt hlt)

/-- In particular, a reset-aware follower step preserves the zero-live-bullet
subspace exactly. -/
theorem resetAwareFollower_localStep_bulletTwoCount_eq_zero
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (C : EConfig n psi kappa tau) (e : Fin n)
    (hnoActive : NoActiveDeletion C)
    (hlFollower : (C e).core.erase.core.leader = false)
    (hlReset : (C e).core.erase.core.reset_cmd = true)
    (hrFollower :
      (C (ring.rightNeighbor e)).core.erase.core.leader = false)
    (hzero : PPLLPpsiLeaderCreationRepair.bulletTwoCount C = 0) :
    let D := localStep ring
      (wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
        hpsi kappa tau) C e
    PPLLPpsiLeaderCreationRepair.bulletTwoCount D = 0 := by
  have hle := resetAwareFollower_localStep_bulletTwoCount_le
    hpsi ring hn C e hnoActive hlFollower hlReset hrFollower
  omega

set_option maxHeartbeats 1000000 in
/-- A follower/reset/follower interaction never increases the global number
of reset commands.  The moving command clears the initiator and is installed
at the responder only when that responder did not carry a blocking echo. -/
theorem resetAwareFollower_localStep_resetCommandCount_le
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (C : EConfig n psi kappa tau) (e : Fin n)
    (hnoActive : NoActiveDeletion C)
    (hlFollower : (C e).core.erase.core.leader = false)
    (hlReset : (C e).core.erase.core.reset_cmd = true)
    (hrFollower :
      (C (ring.rightNeighbor e)).core.erase.core.leader = false) :
    let D := localStep ring
      (wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
        hpsi kappa tau) C e
    resetCommandCount D ≤ resetCommandCount C := by
  let j := ring.rightNeighbor e
  have hje : j ≠ e := rightNeighbor_ne_self_of_one_lt ring hn e
  let T := wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
    hpsi kappa tau
  let D := localStep ring T C e
  have hstep := resetAwareFollower_localStep_normalizes
    hpsi ring hn C e hnoActive hlFollower hlReset hrFollower
  change ResetAwareFollowerGlobalStepFrame hpsi ring C D e at hstep
  have hpair : ExpiringResetFollowerNormalizedOutput hpsi
      (C e, C j) (D e, D j) := by
    simpa [j] using hstep.normalized
  have hlocal :
      resetCommandMass (D e).core.erase.core +
          resetCommandMass (D j).core.erase.core ≤
        resetCommandMass (C e).core.erase.core +
          resetCommandMass (C j).core.erase.core := by
    unfold resetCommandMass
    rw [hpair.control.left_reset_false,
      hpair.control.right_reset_exact, hlReset]
    cases hrightReset : (C j).core.erase.core.reset_cmd <;>
      cases hrightEcho : (C j).core.erase.core.echo <;>
      simp [hrightReset, hrightEcho]
  unfold resetCommandCount
  apply PPLLPpsiLeaderCreationRepair.sum_ofFn_le_of_pair_le
    (fun i => resetCommandMass (D i).core.erase.core)
    (fun i => resetCommandMass (C i).core.erase.core)
    e j (Ne.symm hje) hlocal
  intro i hie hij
  have hframe := hstep.off_edge i hie
  rw [show ring.rightNeighbor e = j by rfl] at hframe
  rw [hframe hij]

set_option maxHeartbeats 1000000 in
/-- A blocking responder echo strictly consumes at least the moving reset
command, so the global reset-command count decreases. -/
theorem resetAwareFollower_localStep_resetCommandCount_lt_of_echo_true
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (C : EConfig n psi kappa tau) (e : Fin n)
    (hnoActive : NoActiveDeletion C)
    (hlFollower : (C e).core.erase.core.leader = false)
    (hlReset : (C e).core.erase.core.reset_cmd = true)
    (hrFollower :
      (C (ring.rightNeighbor e)).core.erase.core.leader = false)
    (hrEcho :
      (C (ring.rightNeighbor e)).core.erase.core.echo = true) :
    let D := localStep ring
      (wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
        hpsi kappa tau) C e
    resetCommandCount D < resetCommandCount C := by
  let j := ring.rightNeighbor e
  have hje : j ≠ e := rightNeighbor_ne_self_of_one_lt ring hn e
  let T := wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
    hpsi kappa tau
  let D := localStep ring T C e
  have hstep := resetAwareFollower_localStep_normalizes
    hpsi ring hn C e hnoActive hlFollower hlReset hrFollower
  change ResetAwareFollowerGlobalStepFrame hpsi ring C D e at hstep
  have hpair : ExpiringResetFollowerNormalizedOutput hpsi
      (C e, C j) (D e, D j) := by
    simpa [j] using hstep.normalized
  have hrEchoJ : (C j).core.erase.core.echo = true := by
    simpa [j] using hrEcho
  have hlocal :
      resetCommandMass (D e).core.erase.core +
          resetCommandMass (D j).core.erase.core <
        resetCommandMass (C e).core.erase.core +
          resetCommandMass (C j).core.erase.core := by
    unfold resetCommandMass
    rw [hpair.control.left_reset_false,
      hpair.control.right_reset_exact, hlReset, hrEchoJ]
    cases hrightReset : (C j).core.erase.core.reset_cmd <;>
      simp [hrightReset]
  unfold resetCommandCount
  apply PPLLPpsiLeaderCreationRepair.sum_ofFn_lt_of_pair_lt
    (fun i => resetCommandMass (D i).core.erase.core)
    (fun i => resetCommandMass (C i).core.erase.core)
    e j (Ne.symm hje) hlocal
  intro i hie hij
  have hframe := hstep.off_edge i hie
  rw [show ring.rightNeighbor e = j by rfl] at hframe
  rw [hframe hij]

/-- A reset token starts a leaderless clockwise advance at its own site. -/
theorem leaderlessResetAdvanceState_zero
    (hpsi : psi > 0) (ring : DirectedRing n)
    (root : Fin n) (C : EConfig n psi kappa tau)
    (hnoActive : NoActiveDeletion C)
    (hleaderless : PPLLPpsiLeaderCreationSchedule.RawLeaderless
      (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig C))
    (hreset : (C root).core.erase.core.reset_cmd = true) :
    LeaderlessResetAdvanceState hpsi ring root C C 0 := by
  exact {
    steps_le := Nat.zero_le _
    no_active := hnoActive
    leaderless := hleaderless
    source_reset := by simpa [groupOffset_zero_eq] using hreset
    source_label := by
      apply Fin.ext
      simp [groupOffset_zero_eq,
        Nat.mod_eq_of_lt (C root).core.erase.core.label.isLt]
    predecessor_echo_of_source_last := by intro h; omega
    reset_count_le := Nat.le_refl _
    bullet_count_le := Nat.le_refl _
    untouched_ahead := by intro k _ _; rfl
  }

set_option maxHeartbeats 1000000 in
/-- One more edge of a leaderless reset advance either strictly decreases the
global reset-command count, or moves a reset token to the next site while
preserving deletion freedom, leaderlessness, and the untouched suffix. -/
theorem LeaderlessResetAdvanceState.step_or_resetCommandCount_lt
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (root : Fin n) (base current : EConfig n psi kappa tau)
    (steps : Nat)
    (hstate : LeaderlessResetAdvanceState
      hpsi ring root base current steps)
    (hlt : steps < n) :
    let e := groupOffset ring root steps
    let D := localStep ring
      (wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
        hpsi kappa tau) current e
    NoActiveDeletion D ∧
      PPLLPpsiLeaderCreationSchedule.RawLeaderless
        (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig D) ∧
      PPLLPpsiLeaderCreationRepair.bulletTwoCount D ≤
        PPLLPpsiLeaderCreationRepair.bulletTwoCount base ∧
      (resetCommandCount D < resetCommandCount base ∨
        LeaderlessResetAdvanceState hpsi ring root base D (steps + 1)) := by
  let e := groupOffset ring root steps
  let j := groupOffset ring root (steps + 1)
  let T := wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
    hpsi kappa tau
  let D := localStep ring T current e
  have hneighbor : ring.rightNeighbor e = j := by
    simpa [e, j] using rightNeighbor_groupOffset ring root steps
  have heFollower : (current e).core.erase.core.leader = false :=
    hstate.leaderless e
  have hjFollower : (current j).core.erase.core.leader = false :=
    hstate.leaderless j
  have heReset : (current e).core.erase.core.reset_cmd = true := by
    simpa [e] using hstate.source_reset
  have hstep := resetAwareFollower_localStep_normalizes
    hpsi ring hn current e hstate.no_active heFollower heReset
      (by simpa [hneighbor] using hjFollower)
  change ResetAwareFollowerGlobalStepFrame hpsi ring current D e at hstep
  have hpair : ExpiringResetFollowerNormalizedOutput hpsi
      (current e, current j) (D e, D j) := by
    simpa [j, hneighbor] using hstep.normalized
  have hle := resetAwareFollower_localStep_resetCommandCount_le
    hpsi ring hn current e hstate.no_active heFollower heReset
      (by simpa [hneighbor] using hjFollower)
  change resetCommandCount D ≤ resetCommandCount current at hle
  have hbulletLe := resetAwareFollower_localStep_bulletTwoCount_le
    hpsi ring hn current e hstate.no_active heFollower heReset
      (by simpa [hneighbor] using hjFollower)
  change PPLLPpsiLeaderCreationRepair.bulletTwoCount D ≤
    PPLLPpsiLeaderCreationRepair.bulletTwoCount current at hbulletLe
  have hbulletBase : PPLLPpsiLeaderCreationRepair.bulletTwoCount D ≤
      PPLLPpsiLeaderCreationRepair.bulletTwoCount base :=
    Nat.le_trans hbulletLe hstate.bullet_count_le
  have hDLeaderless :
      PPLLPpsiLeaderCreationSchedule.RawLeaderless
        (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig D) := by
    intro i
    change (D i).core.erase.core.leader = false
    rw [hstep.leader_eq i]
    exact hstate.leaderless i
  refine ⟨hstep.no_active, hDLeaderless, hbulletBase, ?_⟩
  by_cases hdrop : resetCommandCount D < resetCommandCount current
  · exact Or.inl (Nat.lt_of_lt_of_le hdrop hstate.reset_count_le)
  · have hjEcho : (current j).core.erase.core.echo = false := by
      cases heq : (current j).core.erase.core.echo with
      | false => rfl
      | true =>
          have hstrict :=
            resetAwareFollower_localStep_resetCommandCount_lt_of_echo_true
              hpsi ring hn current e hstate.no_active heFollower heReset
                (by simpa [hneighbor] using hjFollower)
                (by simpa [hneighbor] using heq)
          change resetCommandCount D < resetCommandCount current at hstrict
          exact False.elim (hdrop hstrict)
    have hjReset : (D j).core.erase.core.reset_cmd = true := by
      simpa [hjEcho] using hpair.control.right_reset_exact
    have hjLabel : (D j).core.erase.core.label =
        ⟨((base root).core.erase.core.label.val + (steps + 1)) % psi,
          Nat.mod_lt _ hpsi⟩ := by
      have hsourceVal := congrArg Fin.val hstate.source_label
      calc
        (D j).core.erase.core.label =
            ⟨((current e).core.erase.core.label.val + 1) % psi,
              Nat.mod_lt _ hpsi⟩ := hpair.right_successor
        _ = ⟨((base root).core.erase.core.label.val + (steps + 1)) % psi,
              Nat.mod_lt _ hpsi⟩ := by
          apply Fin.ext
          change
            ((current (groupOffset ring root steps)).core.erase.core.label.val + 1) % psi =
              ((base root).core.erase.core.label.val + (steps + 1)) % psi
          rw [hsourceVal]
          simpa [Nat.add_assoc] using
            mod_add_one (base root).core.erase.core.label.val steps psi
    refine Or.inr {
      steps_le := by omega
      no_active := hstep.no_active
      leaderless := hDLeaderless
      source_reset := ?_
      source_label := ?_
      predecessor_echo_of_source_last := ?_
      reset_count_le := Nat.le_trans hle hstate.reset_count_le
      bullet_count_le := hbulletBase
      untouched_ahead := ?_
    }
    · simpa [j] using hjReset
    · simpa [j] using hjLabel
    · intro _ hlast
      have hleft := hpair.control.left_echo_exact
      rw [if_pos (by simpa [j] using hlast)] at hleft
      simpa [e] using hleft
    · intro k hk hkn
      have hkOld : steps < k := by omega
      have hke : groupOffset ring root k ≠ e := by
        apply groupOffset_ne_of_lt ring root hkn hlt
        omega
      have hkj : groupOffset ring root k ≠ j := by
        apply groupOffset_ne_of_lt ring root hkn (by omega)
        omega
      change D (groupOffset ring root k) = base (groupOffset ring root k)
      rw [hstep.off_edge (groupOffset ring root k) hke
        (by simpa [hneighbor] using hkj)]
      exact hstate.untouched_ahead k hkOld hkn

set_option maxHeartbeats 2000000 in
/-- A bounded clockwise prefix from a leaderless reset source stops as soon as
the global reset-command count falls.  If no fall occurs, the whole canonical
prefix is realized and a reset token remains at its endpoint. -/
theorem exists_leaderlessResetAdvanceSchedule
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (root : Fin n) (C : EConfig n psi kappa tau)
    (hnoActive : NoActiveDeletion C)
    (hleaderless : PPLLPpsiLeaderCreationSchedule.RawLeaderless
      (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig C))
    (hreset : (C root).core.erase.core.reset_cmd = true)
    (steps : Nat) (hsteps : steps ≤ n) :
    ∃ (word : DetSchedule n) (D : EConfig n psi kappa tau),
      D = runLocalSchedule ring
        (wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
          hpsi kappa tau) C word ∧
      word.length ≤ steps ∧
      NoActiveDeletion D ∧
      PPLLPpsiLeaderCreationSchedule.RawLeaderless
        (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig D) ∧
      PPLLPpsiLeaderCreationRepair.bulletTwoCount D ≤
        PPLLPpsiLeaderCreationRepair.bulletTwoCount C ∧
      (resetCommandCount D < resetCommandCount C ∨
        (word = resetSweepSchedule ring root steps ∧
          LeaderlessResetAdvanceState hpsi ring root C D steps)) := by
  let T := wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
    hpsi kappa tau
  induction steps with
  | zero =>
      exact ⟨[], C, rfl, by simp, hnoActive, hleaderless, Nat.le_refl _,
        Or.inr ⟨rfl,
        leaderlessResetAdvanceState_zero
          hpsi ring root C hnoActive hleaderless hreset⟩⟩
  | succ steps ih =>
      have hprevBound : steps ≤ n := by omega
      obtain ⟨word, D, hD, hwordLength, hDNoActive,
        hDLeaderless, hDCount, hout⟩ := ih hprevBound
      rcases hout with hdrop | ⟨hword, hstate⟩
      · exact ⟨word, D, hD, by omega, hDNoActive, hDLeaderless,
          hDCount, Or.inl hdrop⟩
      · have hlt : steps < n := by omega
        let e := groupOffset ring root steps
        let E := localStep ring T D e
        have hnext := hstate.step_or_resetCommandCount_lt
          hpsi ring hn root C D steps hlt
        change NoActiveDeletion E ∧
          PPLLPpsiLeaderCreationSchedule.RawLeaderless
            (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig E) ∧
          PPLLPpsiLeaderCreationRepair.bulletTwoCount E ≤
            PPLLPpsiLeaderCreationRepair.bulletTwoCount C ∧
          (resetCommandCount E < resetCommandCount C ∨
            LeaderlessResetAdvanceState hpsi ring root C E (steps + 1))
          at hnext
        obtain ⟨hENoActive, hELeaderless, hECount, hnext⟩ := hnext
        have hrun : E = runLocalSchedule ring T C
            (resetSweepSchedule ring root (steps + 1)) := by
          rw [resetSweepSchedule]
          calc
            E = runLocalSchedule ring T D [e] := rfl
            _ = runLocalSchedule ring T
                (runLocalSchedule ring T C word) [e] := by rw [← hD]
            _ = runLocalSchedule ring T C (word ++ [e]) :=
              (runLocalSchedule_append_generic ring T C word [e]).symm
            _ = runLocalSchedule ring T C
                (resetSweepSchedule ring root steps ++ [e]) := by rw [hword]
        rcases hnext with hdrop | hstateNext
        · exact ⟨resetSweepSchedule ring root (steps + 1), E, hrun,
            Nat.le_of_eq
              (PPLLWallSweepEchoDrain.resetSweepSchedule_length
                ring root (steps + 1)),
            hENoActive, hELeaderless, hECount,
            Or.inl hdrop⟩
        · exact ⟨resetSweepSchedule ring root (steps + 1), E, hrun,
            Nat.le_of_eq
              (PPLLWallSweepEchoDrain.resetSweepSchedule_length
                ring root (steps + 1)),
            hENoActive, hELeaderless, hECount,
            Or.inr ⟨rfl, hstateNext⟩⟩

/-- From any label, at most one label period of successor writes reaches the
last label.  The positive offset is used to make the moving reset leave an
echo immediately behind it. -/
private theorem exists_positive_step_to_last_label
    (hpsi : psi > 0) (a : Fin psi) :
    ∃ t, 0 < t ∧ t ≤ psi ∧ (a.val + t) % psi = psi - 1 := by
  by_cases hlast : a.val = psi - 1
  · refine ⟨psi, hpsi, Nat.le_refl _, ?_⟩
    rw [Nat.add_mod_right, Nat.mod_eq_of_lt a.isLt]
    exact hlast
  · let t := psi - 1 - a.val
    have ha : a.val < psi - 1 := by omega
    refine ⟨t, by dsimp [t]; omega, by dsimp [t]; omega, ?_⟩
    have hsum : a.val + t = psi - 1 := by simp [t]; omega
    rw [hsum, Nat.mod_eq_of_lt (by omega)]

set_option maxHeartbeats 2000000 in
/-- From a leaderless deletion-free configuration carrying a reset command,
the complete reset-aware transition has a finite schedule that strictly
decreases the global reset-command count while preserving both boundary
facts. -/
theorem exists_leaderlessResetCommandCount_lt_of_source
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (hpsiLe : psi ≤ n) (root : Fin n)
    (C : EConfig n psi kappa tau)
    (hnoActive : NoActiveDeletion C)
    (hleaderless : PPLLPpsiLeaderCreationSchedule.RawLeaderless
      (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig C))
    (hreset : (C root).core.erase.core.reset_cmd = true) :
    ∃ (word : DetSchedule n) (D : EConfig n psi kappa tau),
      D = runLocalSchedule ring
        (wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
          hpsi kappa tau) C word ∧
      NoActiveDeletion D ∧
      PPLLPpsiLeaderCreationSchedule.RawLeaderless
        (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig D) ∧
      PPLLPpsiLeaderCreationRepair.bulletTwoCount D ≤
        PPLLPpsiLeaderCreationRepair.bulletTwoCount C ∧
      resetCommandCount D < resetCommandCount C := by
  let T := wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
    hpsi kappa tau
  obtain ⟨t, htpos, htpsi, htlabel⟩ :=
    exists_positive_step_to_last_label
      hpsi (C root).core.erase.core.label
  have htn : t ≤ n := Nat.le_trans htpsi hpsiLe
  obtain ⟨word₁, M, hM, _hword₁Length, hMNoActive,
      hMLeaderless, hMCount, hout₁⟩ :=
    exists_leaderlessResetAdvanceSchedule
      hpsi ring hn root C hnoActive hleaderless hreset t htn
  rcases hout₁ with hdrop₁ | ⟨_hword₁, hstateM⟩
  · exact ⟨word₁, M, hM, hMNoActive, hMLeaderless, hMCount, hdrop₁⟩
  · have hMSourceLast :
        (M (groupOffset ring root t)).core.erase.core.label =
          ⟨psi - 1, by omega⟩ := by
      rw [hstateM.source_label]
      apply Fin.ext
      exact htlabel
    have hMPredecessorEcho :
        (M (groupOffset ring root (t - 1))).core.erase.core.echo = true :=
      hstateM.predecessor_echo_of_source_last htpos hMSourceLast
    let q := groupOffset ring root (t - 1)
    let p := groupOffset ring root t
    have hpRight : ring.rightNeighbor q = p := by
      have hnext := rightNeighbor_groupOffset ring root (t - 1)
      simpa [q, p, show t - 1 + 1 = t by omega] using hnext
    have htarget : groupOffset ring p (n - 1) = q := by
      rw [← hpRight]
      exact
        PPLLWallSweepRestartableProtected.groupOffset_rightNeighbor_last
          ring hn q
    have hMReset : (M p).core.erase.core.reset_cmd = true := by
      simpa [p] using hstateM.source_reset
    have hsecondBound : n - 2 ≤ n := by omega
    obtain ⟨word₂, N, hN, _hword₂Length, hNNoActive,
        hNLeaderless, hNCount, hout₂⟩ :=
      exists_leaderlessResetAdvanceSchedule
        hpsi ring hn p M hMNoActive hMLeaderless hMReset
          (n - 2) hsecondBound
    rcases hout₂ with hdrop₂ | ⟨_hword₂, hstateN⟩
    · refine ⟨word₁ ++ word₂, N, ?_, hNNoActive,
          hNLeaderless, Nat.le_trans hNCount hMCount, ?_⟩
      · calc
          N = runLocalSchedule ring T M word₂ := hN
          _ = runLocalSchedule ring T
              (runLocalSchedule ring T C word₁) word₂ := by rw [← hM]
          _ = runLocalSchedule ring T C (word₁ ++ word₂) :=
            (runLocalSchedule_append_generic ring T C word₁ word₂).symm
      · exact Nat.lt_of_lt_of_le hdrop₂ hstateM.reset_count_le
    · let e := groupOffset ring p (n - 2)
      let j := groupOffset ring p (n - 1)
      have hneighbor : ring.rightNeighbor e = j := by
        have hnext := rightNeighbor_groupOffset ring p (n - 2)
        simpa [e, j, show n - 2 + 1 = n - 1 by omega] using hnext
      have hjEcho : (N j).core.erase.core.echo = true := by
        have huntouched := hstateN.untouched_ahead (n - 1)
          (by omega) (by omega)
        change N j = M j at huntouched
        rw [huntouched]
        simpa [j, htarget, q] using hMPredecessorEcho
      have heFollower : (N e).core.erase.core.leader = false :=
        hstateN.leaderless e
      have hjFollower : (N j).core.erase.core.leader = false :=
        hstateN.leaderless j
      have heReset : (N e).core.erase.core.reset_cmd = true := by
        simpa [e] using hstateN.source_reset
      let E := localStep ring T N e
      have hstrict :=
        resetAwareFollower_localStep_resetCommandCount_lt_of_echo_true
          hpsi ring hn N e hstateN.no_active heFollower heReset
            (by simpa [hneighbor] using hjFollower)
            (by simpa [hneighbor] using hjEcho)
      change resetCommandCount E < resetCommandCount N at hstrict
      have hframe := resetAwareFollower_localStep_normalizes
        hpsi ring hn N e hstateN.no_active heFollower heReset
          (by simpa [hneighbor] using hjFollower)
      change ResetAwareFollowerGlobalStepFrame hpsi ring N E e at hframe
      have hELeaderless :
          PPLLPpsiLeaderCreationSchedule.RawLeaderless
            (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig E) := by
        intro i
        change (E i).core.erase.core.leader = false
        rw [hframe.leader_eq i]
        exact hstateN.leaderless i
      have hECountStep := resetAwareFollower_localStep_bulletTwoCount_le
        hpsi ring hn N e hstateN.no_active heFollower heReset
          (by simpa [hneighbor] using hjFollower)
      change PPLLPpsiLeaderCreationRepair.bulletTwoCount E ≤
        PPLLPpsiLeaderCreationRepair.bulletTwoCount N at hECountStep
      have hECount : PPLLPpsiLeaderCreationRepair.bulletTwoCount E ≤
          PPLLPpsiLeaderCreationRepair.bulletTwoCount C :=
        Nat.le_trans hECountStep (Nat.le_trans hNCount hMCount)
      refine ⟨word₁ ++ word₂ ++ [e], E, ?_, hframe.no_active,
        hELeaderless, hECount, ?_⟩
      · calc
          E = runLocalSchedule ring T N [e] := rfl
          _ = runLocalSchedule ring T
              (runLocalSchedule ring T M word₂) [e] := by rw [← hN]
          _ = runLocalSchedule ring T M (word₂ ++ [e]) :=
            (runLocalSchedule_append_generic ring T M word₂ [e]).symm
          _ = runLocalSchedule ring T
              (runLocalSchedule ring T C word₁) (word₂ ++ [e]) := by
                rw [← hM]
          _ = runLocalSchedule ring T C
              (word₁ ++ (word₂ ++ [e])) :=
            (runLocalSchedule_append_generic
              ring T C word₁ (word₂ ++ [e])).symm
          _ = runLocalSchedule ring T C (word₁ ++ word₂ ++ [e]) := by
            rw [List.append_assoc]
      · exact Nat.lt_of_lt_of_le hstrict
          (Nat.le_trans hstateN.reset_count_le hstateM.reset_count_le)

/-- A positive reset-command count exposes a physical reset source. -/
private theorem exists_reset_source_of_resetCommandCount_pos
    (C : EConfig n psi kappa tau)
    (hpos : 0 < resetCommandCount C) :
    ∃ i, (C i).core.erase.core.reset_cmd = true := by
  apply Classical.byContradiction
  intro hnone
  have hall : ∀ i, (C i).core.erase.core.reset_cmd = false := by
    intro i
    cases hi : (C i).core.erase.core.reset_cmd with
    | false => rfl
    | true => exact False.elim (hnone ⟨i, hi⟩)
  have hzero : resetCommandCount C = 0 := by
    simp only [resetCommandCount, resetCommandMass, hall, if_false]
    clear hpos hnone hall C
    induction n with
    | zero => rfl
    | succ n ih =>
        rw [List.ofFn_succ, List.sum_cons]
        simpa using ih
  omega

/-- Vanishing global reset count means that every physical endpoint is
reset-free. -/
theorem reset_false_of_resetCommandCount_eq_zero
    (C : EConfig n psi kappa tau)
    (hzero : resetCommandCount C = 0) :
    ∀ i, (C i).core.erase.core.reset_cmd = false := by
  induction n with
  | zero =>
      intro i
      exact Fin.elim0 i
  | succ n ih =>
      unfold resetCommandCount at hzero
      rw [List.ofFn_succ, List.sum_cons] at hzero
      have hhead : resetCommandMass (C 0).core.erase.core = 0 := by omega
      have htail :
          (List.ofFn (fun i : Fin n =>
            resetCommandMass (C i.succ).core.erase.core)).sum = 0 := by
        omega
      intro i
      by_cases hi : i = 0
      · subst i
        cases hreset : (C 0).core.erase.core.reset_cmd with
        | false => rfl
        | true =>
            unfold resetCommandMass at hhead
            simp [hreset] at hhead
      · have hipos : 0 < i.val := by
          have hval : i.val ≠ 0 := by
            intro hz
            apply hi
            apply Fin.ext
            simpa using hz
          omega
        let j : Fin n := ⟨i.val - 1, by omega⟩
        have hjsucc : j.succ = i := by
          apply Fin.ext
          simp [j]
          omega
        have htailZero :
            resetCommandCount (fun j : Fin n => C j.succ) = 0 := by
          unfold resetCommandCount
          exact htail
        rw [← hjsucc]
        exact ih (fun j : Fin n => C j.succ) htailZero j

/-- Repaired Algorithm 14 does not manufacture a reset command from a
follower initiator when both input endpoints are reset-free. -/
private theorem suppressSigResetKill_reset_free_of_follower
    (hpsi : psi > 0) (l r : AgentState psi)
    (hlFollower : l.leader = false)
    (hlReset : l.reset_cmd = false)
    (hrReset : r.reset_cmd = false) :
    let q := suppressSigResetKill hpsi l r
    q.1.reset_cmd = false ∧ q.2.reset_cmd = false := by
  simp [suppressSigResetKill, suppressSigStart, suppressSigMoveReset,
    resetKillComparison, clearComparisonSignal, suppressSigTerminal,
    suppressSigEcho, suppressSigFinish, hlFollower, hlReset, hrReset]

/-- Authorization reconciliation is transparent on the two physical reset
bits. -/
private theorem authorizedReconcile_reset_fields
    (f : AgentState psi → AgentState psi →
      AgentState psi × AgentState psi)
    (l r : AuthorizedAgentState psi) :
    let raw := f l.core r.core
    let out := authorizedReconcile f l r
    out.1.core.reset_cmd = raw.1.reset_cmd ∧
      out.2.core.reset_cmd = raw.2.reset_cmd := by
  exact ⟨rfl, rfl⟩

/-- The rooted post-suppression stages frame a reset-free output from the
reset-free follower input of repaired Algorithm 14. -/
private theorem authorizedLeaderSinkSuffix_reset_free_of_follower
    (hpsi : psi > 0) (l r : AuthorizedAgentState psi)
    (hlFollower : l.core.leader = false)
    (hlReset : l.core.reset_cmd = false)
    (hrReset : r.core.reset_cmd = false) :
    (authorizedPostSuppressLeaderSink hpsi
      (authorizedReconcile (suppressSigResetKill hpsi) l r).1
      (authorizedReconcile (suppressSigResetKill hpsi) l r).2).1.core.reset_cmd =
        false ∧
    (authorizedPostSuppressLeaderSink hpsi
      (authorizedReconcile (suppressSigResetKill hpsi) l r).1
      (authorizedReconcile (suppressSigResetKill hpsi) l r).2).2.core.reset_cmd =
        false := by
  let raw := suppressSigResetKill hpsi l.core r.core
  let after := authorizedReconcile (suppressSigResetKill hpsi) l r
  let tail := authorizedPostSuppressLeaderSink hpsi after.1 after.2
  have hraw := suppressSigResetKill_reset_free_of_follower
    hpsi l.core r.core hlFollower hlReset hrReset
  change raw.1.reset_cmd = false ∧ raw.2.reset_cmd = false at hraw
  have hafterFields := authorizedReconcile_reset_fields
    (suppressSigResetKill hpsi) l r
  have hafterReset : after.1.core.reset_cmd = false ∧
      after.2.core.reset_cmd = false :=
    ⟨hafterFields.1.trans hraw.1, hafterFields.2.trans hraw.2⟩
  have hpostFields := resetEcho_fields_of_pair_eq
    (authorizedPostSuppressLeaderSink_resetEchoPair
      hpsi after.1 after.2)
  change tail.1.core.reset_cmd = false ∧
    tail.2.core.reset_cmd = false
  exact ⟨hpostFields.1.trans hafterReset.1,
    hpostFields.2.2.1.trans hafterReset.2⟩

/-- Named one-layer expansion of the rooted normal tail. -/
private theorem wallSweepPreCheckResetLeaderSinkNormalTail_eq_explicit
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi) :
    wallSweepPreCheckResetLeaderSinkNormalTail hpsi kappa l r =
      let l₀ := normalizeDeletion l
      let r₀ := normalizeDeletion r
      let pre := wallSweepPreCheckResetBeforeSuppress hpsi kappa l₀ r₀
      let after := authorizedReconcile
        (suppressSigResetKill hpsi) pre.1 pre.2
      authorizedPostSuppressLeaderSink hpsi after.1 after.2 := by
  rfl

set_option maxHeartbeats 1000000 in
/-- The rooted post-CHECK tail therefore remains reset-free on a reset-free
follower source.  A responder birth may occur in this call, but it is not an
initiator reset source for the preceding Algorithm-14 stage. -/
theorem wallSweepPreCheckResetLeaderSinkNormalTail_reset_free_of_follower
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hlFollower : l.core.leader = false)
    (hlReset : l.core.reset_cmd = false)
    (hrReset : r.core.reset_cmd = false) :
    (wallSweepPreCheckResetLeaderSinkNormalTail
      hpsi kappa l r).1.core.reset_cmd = false ∧
    (wallSweepPreCheckResetLeaderSinkNormalTail
      hpsi kappa l r).2.core.reset_cmd = false := by
  let l₀ := normalizeDeletion l
  let r₀ := normalizeDeletion r
  let pre := wallSweepPreCheckResetBeforeSuppress hpsi kappa l₀ r₀
  have hl₀Follower : l₀.core.leader = false := by
    unfold l₀ normalizeDeletion
    split <;> simpa using hlFollower
  have hl₀Reset : l₀.core.reset_cmd = false := by
    unfold l₀ normalizeDeletion
    split <;> simpa using hlReset
  have hr₀Reset : r₀.core.reset_cmd = false := by
    unfold r₀ normalizeDeletion
    split <;> simpa using hrReset
  have hpreFrame := wallSweepPreCheckResetBeforeSuppress_resetEchoPair
    hpsi kappa l₀ r₀
  change authorizedResetEchoPair pre =
    authorizedResetEchoPair (l₀, r₀) at hpreFrame
  have hpreFields := resetEcho_fields_of_pair_eq hpreFrame
  have hpreFollower : pre.1.core.leader = false := by
    simpa only [pre] using
      (wallSweepPreCheckResetBeforeSuppress_initiator_leader_eq
        hpsi kappa l₀ r₀).trans hl₀Follower
  have hpreLeftReset : pre.1.core.reset_cmd = false :=
    hpreFields.1.trans hl₀Reset
  have hpreRightReset : pre.2.core.reset_cmd = false :=
    hpreFields.2.2.1.trans hr₀Reset
  have hsuffix := authorizedLeaderSinkSuffix_reset_free_of_follower
    hpsi pre.1 pre.2 hpreFollower hpreLeftReset hpreRightReset
  have hpreEq : pre =
      wallSweepPreCheckResetBeforeSuppress hpsi kappa l₀ r₀ := rfl
  have hl₀Eq : l₀ = normalizeDeletion l := rfl
  have hr₀Eq : r₀ = normalizeDeletion r := rfl
  rw [hpreEq, hl₀Eq, hr₀Eq] at hsuffix
  rw [wallSweepPreCheckResetLeaderSinkNormalTail_eq_explicit]
  exact hsuffix

/-- Birth bookkeeping changes only comparison-deletion metadata, not either
physical reset bit. -/
private theorem markLeaderBirth_reset_fields
    (born : Bool)
    (q : AuthorizedAgentState psi × AuthorizedAgentState psi) :
    (markLeaderBirth born q).1.core.reset_cmd = q.1.core.reset_cmd ∧
      (markLeaderBirth born q).2.core.reset_cmd = q.2.core.reset_cmd := by
  unfold markLeaderBirth markComparisonForDeletion
  repeat (first | constructor | rfl | split)

set_option maxHeartbeats 1000000 in
/-- A priority-open rooted interaction with a follower initiator preserves a
globally reset-free active pair, even when this is the decisive responder
birth edge. -/
theorem
    wallSweepPreCheckResetLeaderSinkAuthorized_priority_open_reset_free_of_follower
    (hpsi : psi > 0) (kappa : Nat)
    (l r : AuthorizedAgentState psi)
    (hopen : AuthorizedPriorityOpen l r)
    (hlFollower : l.core.leader = false)
    (hlReset : l.core.reset_cmd = false)
    (hrReset : r.core.reset_cmd = false) :
    let out := wallSweepPreCheckResetLeaderSinkAuthorizedTransition
      hpsi kappa l r
    out.1.core.reset_cmd = false ∧ out.2.core.reset_cmd = false := by
  let l₀ := normalizeDeletion l
  let r₀ := normalizeDeletion r
  let beforeCheck := wallSweepPreCheckResetBeforeCheck hpsi kappa l₀ r₀
  let afterCheck := wallSweepPreCheckResetAfterCheck hpsi kappa l₀ r₀
  let born := leaderBirthBeforeOrAtCheck l₀ r₀ beforeCheck afterCheck
  let tail := wallSweepPreCheckResetLeaderSinkNormalTail hpsi kappa l r
  let out := wallSweepPreCheckResetLeaderSinkAuthorizedTransition
    hpsi kappa l r
  have htail :=
    wallSweepPreCheckResetLeaderSinkNormalTail_reset_free_of_follower
      hpsi kappa l r hlFollower hlReset hrReset
  change tail.1.core.reset_cmd = false ∧
    tail.2.core.reset_cmd = false at htail
  have heq :=
    wallSweepPreCheckResetLeaderSinkAuthorizedTransition_eq_marked_normalTail
      hpsi kappa l r hopen
  change out = markLeaderBirth born tail at heq
  have hmark := markLeaderBirth_reset_fields born tail
  change out.1.core.reset_cmd = false ∧
    out.2.core.reset_cmd = false
  exact ⟨(congrArg
      (fun q : AuthorizedAgentState psi × AuthorizedAgentState psi =>
        q.1.core.reset_cmd) heq).trans (hmark.1.trans htail.1),
    (congrArg
      (fun q : AuthorizedAgentState psi × AuthorizedAgentState psi =>
        q.2.core.reset_cmd) heq).trans (hmark.2.trans htail.2)⟩

set_option maxHeartbeats 1000000 in
/-- Bounded reification and path expiration preserve the reset-free follower
contract on the physical rooted transition. -/
theorem
    wallSweepPreCheckResetLeaderSinkPathStall_priority_open_reset_free_of_follower
    (hpsi : psi > 0) (kappa tau : Nat)
    (l r : ExpiringAgentState psi kappa tau)
    (hopen : WallPriorityOpen l r)
    (hlFollower : l.core.erase.core.leader = false)
    (hlReset : l.core.erase.core.reset_cmd = false)
    (hrReset : r.core.erase.core.reset_cmd = false) :
    let out := wallSweepPreCheckResetLeaderSinkPathStallTransition
      hpsi kappa tau l r
    out.1.core.erase.core.reset_cmd = false ∧
      out.2.core.erase.core.reset_cmd = false := by
  let authorizedOut :=
    wallSweepPreCheckResetLeaderSinkAuthorizedTransition
      hpsi kappa l.core.erase r.core.erase
  let bounded := wallSweepPreCheckResetLeaderSinkBoundedTransition
    hpsi kappa l.core r.core
  let lBase : ExpiringAgentState psi kappa tau := ⟨bounded.1, l.stall⟩
  let rBase : ExpiringAgentState psi kappa tau := ⟨bounded.2, r.stall⟩
  have ha :=
    wallSweepPreCheckResetLeaderSinkAuthorized_priority_open_reset_free_of_follower
      hpsi kappa l.core.erase r.core.erase hopen hlFollower hlReset hrReset
  change authorizedOut.1.core.reset_cmd = false ∧
    authorizedOut.2.core.reset_cmd = false at ha
  have herase := erase_wallSweepPreCheckResetLeaderSinkBoundedTransition
    hpsi kappa l.core r.core
  have hleft := congrArg Prod.fst herase
  have hright := congrArg Prod.snd herase
  change bounded.1.erase = authorizedOut.1 at hleft
  change bounded.2.erase = authorizedOut.2 at hright
  have hbaseLeft : lBase.core.erase.core.reset_cmd = false := by
    change bounded.1.erase.core.reset_cmd = false
    rw [hleft]
    exact ha.1
  have hbaseRight : rBase.core.erase.core.reset_cmd = false := by
    change bounded.2.erase.core.reset_cmd = false
    rw [hright]
    exact ha.2
  have hleftFrame := deletionPriorityExpireOne_path_frame l lBase
  have hrightFrame := deletionPriorityExpireOne_path_frame r rBase
  rw [wallSweepPreCheckResetLeaderSinkPathStall_eq_expiryStages]
  exact ⟨hleftFrame.2.2.2.1.trans hbaseLeft,
    hrightFrame.2.2.2.1.trans hbaseRight⟩

/-- Pointwise absence of physical reset commands. -/
def ResetCommandFree (C : EConfig n psi kappa tau) : Prop :=
  ∀ i, (C i).core.erase.core.reset_cmd = false

/-- One local step of the birth-signal repair differs from the established
integrated step only in the new-leader absence signal.  The pointwise frame is
unconditional and therefore can be reused by both the first-leader producer
and all later rank arguments. -/
theorem localStep_birthSignalZero_frame
    (hpsi : psi > 0) (ring : DirectedRing n)
    (C : EConfig n psi kappa tau) (e : Fin n) :
    let oldD := localStep ring
      (wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
        hpsi kappa tau) C e
    let newD := localStep ring
      (wallSweepBirthSignalZeroPathStallTransition
        hpsi kappa tau) C e
    BirthSignalConfigFrame oldD newD := by
  let j := ring.rightNeighbor e
  let Told :=
    wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
      hpsi kappa tau
  let Tnew := wallSweepBirthSignalZeroPathStallTransition
    hpsi kappa tau
  let qold := Told (C e) (C j)
  let oldD := localStep ring Told C e
  let newD := localStep ring Tnew C e
  have hpair := initializeFollowerPairBirthSignals_frame
    (C e) (C j) qold
  change BirthSignalConfigFrame oldD newD
  intro i
  by_cases hie : i = e
  · subst i
    simpa [oldD, newD, Told, Tnew, qold,
      wallSweepBirthSignalZeroPathStallTransition, localStep, j] using hpair.1
  · by_cases hij : i = j
    · subst i
      simpa [oldD, newD, Told, Tnew, qold,
        wallSweepBirthSignalZeroPathStallTransition, localStep, j, hie] using
          hpair.2
    · have hold : oldD i = C i := by
        simp [oldD, Told, localStep, j, hie, hij]
      have hnew : newD i = C i := by
        simp [newD, Tnew, localStep, j, hie, hij]
      rw [hold, hnew]
      exact BirthSignalFrame.refl (C i)

theorem bulletTwoCount_eq_of_birthSignalConfigFrame
    {C D : EConfig n psi kappa tau}
    (h : BirthSignalConfigFrame C D) :
    PPLLPpsiLeaderCreationRepair.bulletTwoCount D =
      PPLLPpsiLeaderCreationRepair.bulletTwoCount C := by
  unfold PPLLPpsiLeaderCreationRepair.bulletTwoCount
  have hfun :
      (fun i => bulletTwoMass (D i).core.erase.core) =
        (fun i => bulletTwoMass (C i).core.erase.core) := by
    funext i
    unfold bulletTwoMass
    rw [(h i).bullet]
  rw [hfun]

theorem ppsiControlConfigFrame_of_birthSignalConfigFrame
    {C D : EConfig n psi kappa tau}
    (h : BirthSignalConfigFrame C D) :
    PPLLPpsiLeaderCreationRepair.PpsiControlConfigFrame C D := by
  intro i
  apply PPLLPpsiLeaderCreationRepair.PpsiControlView.ext
  · exact (h i).label
  · exact (h i).probe
  · exact (h i).phase

theorem rawLeaderless_iff_of_birthSignalConfigFrame
    {C D : EConfig n psi kappa tau}
    (h : BirthSignalConfigFrame C D) :
    PPLLPpsiLeaderCreationSchedule.RawLeaderless
        (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig D) ↔
      PPLLPpsiLeaderCreationSchedule.RawLeaderless
        (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig C) := by
  constructor <;> intro hleaderless i
  · exact (h i).leader.symm.trans (hleaderless i)
  · exact (h i).leader.trans (hleaderless i)

theorem resetCommandFree_iff_of_birthSignalConfigFrame
    {C D : EConfig n psi kappa tau}
    (h : BirthSignalConfigFrame C D) :
    ResetCommandFree D ↔ ResetCommandFree C := by
  constructor <;> intro hfree i
  · exact (h i).reset_cmd.symm.trans (hfree i)
  · exact (h i).reset_cmd.trans (hfree i)

theorem noActiveDeletion_iff_of_birthSignalConfigFrame
    {C D : EConfig n psi kappa tau}
    (h : BirthSignalConfigFrame C D) :
    NoActiveDeletion D ↔ NoActiveDeletion C := by
  constructor <;> intro hnoActive i
  · exact (h i).deletion_active.symm.trans (hnoActive i)
  · exact (h i).deletion_active.trans (hnoActive i)

theorem rawHasLeader_iff_of_birthSignalConfigFrame
    {C D : EConfig n psi kappa tau}
    (h : BirthSignalConfigFrame C D) :
    PPLLPpsiLeaderCreationSchedule.RawHasLeader
        (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig D) ↔
      PPLLPpsiLeaderCreationSchedule.RawHasLeader
        (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig C) := by
  constructor <;> rintro ⟨i, hi⟩
  · exact ⟨i, (h i).leader.symm.trans hi⟩
  · exact ⟨i, (h i).leader.trans hi⟩

theorem hasUniqueLeader_of_birthSignalConfigFrame
    {C D : EConfig n psi kappa tau}
    (h : BirthSignalConfigFrame C D)
    (hunique : hasUniqueLeader n
      (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig C)) :
    hasUniqueLeader n
      (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig D) := by
  obtain ⟨leader, hleader, honly⟩ := hunique
  refine ⟨leader, ?_, ?_⟩
  · change (D leader).core.erase.core.leader = true
    change (C leader).core.erase.core.leader = true at hleader
    exact (h leader).leader.trans hleader
  · intro i hi
    apply honly i
    change (C i).core.erase.core.leader = true
    change (D i).core.erase.core.leader = true at hi
    exact (h i).leader.symm.trans hi

/-- If the established integrated step remains globally leaderless, the
birth-signal wrapper is exactly the identity on that whole local step. -/
theorem localStep_birthSignalZero_eq_of_resetProbe_result_leaderless
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (C : EConfig n psi kappa tau) (e : Fin n)
    (hleaderless : PPLLPpsiLeaderCreationSchedule.RawLeaderless
      (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig
        (localStep ring
          (wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
            hpsi kappa tau) C e))) :
    localStep ring
        (wallSweepBirthSignalZeroPathStallTransition
          hpsi kappa tau) C e =
      localStep ring
        (wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
          hpsi kappa tau) C e := by
  let j := ring.rightNeighbor e
  have hje : j ≠ e := rightNeighbor_ne_self_of_one_lt ring hn e
  let Told :=
    wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
      hpsi kappa tau
  let Tnew := wallSweepBirthSignalZeroPathStallTransition
    hpsi kappa tau
  let Dold := localStep ring Told C e
  have hleft : (Told (C e) (C j)).1.core.erase.core.leader = false := by
    have := hleaderless e
    change (Dold e).core.erase.core.leader = false at this
    simpa [Dold, Told, localStep, j] using this
  have hright : (Told (C e) (C j)).2.core.erase.core.leader = false := by
    have := hleaderless j
    change (Dold j).core.erase.core.leader = false at this
    simpa [Dold, Told, localStep, j, hje] using this
  have hpair := wallSweepBirthSignalZeroPathStall_eq_of_output_followers
    hpsi kappa tau (C e) (C j) hleft hright
  exact localStep_eq_of_pair_eq ring Tnew Told C e (by simpa [Tnew, Told, j])

/-- Every leader created by one birth-signal-zero local step from a globally
leaderless input has zero absence signal. -/
theorem localStep_birthSignalZero_new_leader_signal_zero
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (C : EConfig n psi kappa tau) (e i : Fin n)
    (hleaderless : PPLLPpsiLeaderCreationSchedule.RawLeaderless
      (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig C))
    (hout :
      (localStep ring
        (wallSweepBirthSignalZeroPathStallTransition
          hpsi kappa tau) C e i).core.erase.core.leader = true) :
    (localStep ring
      (wallSweepBirthSignalZeroPathStallTransition
        hpsi kappa tau) C e i).core.erase.core.signal_B =
          ⟨0, by omega⟩ := by
  let j := ring.rightNeighbor e
  have hje : j ≠ e := rightNeighbor_ne_self_of_one_lt ring hn e
  let Told :=
    wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
      hpsi kappa tau
  let Tnew := wallSweepBirthSignalZeroPathStallTransition
    hpsi kappa tau
  have heFollower : (C e).core.erase.core.leader = false := hleaderless e
  have hjFollower : (C j).core.erase.core.leader = false := hleaderless j
  by_cases hie : i = e
  · subst i
    have holdLeader :
        (Told (C e) (C j)).1.core.erase.core.leader = true := by
      have hframe := localStep_birthSignalZero_frame hpsi ring C e
      have hnewLeader :
          (localStep ring Tnew C e e).core.erase.core.leader = true := by
        simpa [Tnew] using hout
      have hold := (hframe e).leader
      change (localStep ring Tnew C e e).core.erase.core.leader =
        (localStep ring Told C e e).core.erase.core.leader at hold
      have : (localStep ring Told C e e).core.erase.core.leader = true :=
        hold.symm.trans hnewLeader
      simpa [Told, localStep, j] using this
    simpa [Tnew, wallSweepBirthSignalZeroPathStallTransition, localStep, j]
      using wallSweepBirthSignalZeroPathStall_left_birth_signal_zero
        hpsi kappa tau (C e) (C j) heFollower hjFollower holdLeader
  · by_cases hij : i = j
    · subst i
      have holdLeader :
          (Told (C e) (C j)).2.core.erase.core.leader = true := by
        have hframe := localStep_birthSignalZero_frame hpsi ring C e
        have hnewLeader :
            (localStep ring Tnew C e j).core.erase.core.leader = true := by
          simpa [Tnew] using hout
        have hold := (hframe j).leader
        change (localStep ring Tnew C e j).core.erase.core.leader =
          (localStep ring Told C e j).core.erase.core.leader at hold
        have : (localStep ring Told C e j).core.erase.core.leader = true :=
          hold.symm.trans hnewLeader
        simpa [Told, localStep, j, hje] using this
      simpa [Tnew, wallSweepBirthSignalZeroPathStallTransition,
        localStep, j, hje] using
          wallSweepBirthSignalZeroPathStall_right_birth_signal_zero
            hpsi kappa tau (C e) (C j) heFollower hjFollower holdLeader
    · have hsame : localStep ring Tnew C e i = C i := by
        simp [Tnew, localStep, j, hie, hij]
      rw [hsame] at hout
      have hi := hleaderless i
      change (C i).core.erase.core.leader = false at hi
      rw [hi] at hout
      contradiction

theorem resetCommandFree_of_resetCommandCount_eq_zero
    (C : EConfig n psi kappa tau)
    (hzero : resetCommandCount C = 0) : ResetCommandFree C :=
  reset_false_of_resetCommandCount_eq_zero C hzero

/-- On a reset-free initiator, the complete integrated local step is exactly
the established rooted local step. -/
theorem localStep_resetProbe_eq_leaderSink_of_source_reset_false
    (hpsi : psi > 0) (ring : DirectedRing n)
    (C : EConfig n psi kappa tau) (e : Fin n)
    (hreset : (C e).core.erase.core.reset_cmd = false) :
    localStep ring
        (wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
          hpsi kappa tau) C e =
      localStep ring
        (wallSweepPreCheckResetLeaderSinkPathStallTransition
          hpsi kappa tau) C e := by
  unfold localStep
  dsimp only
  rw [wallSweepResetProbePreCheckResetLeaderSinkPathStall_eq_of_no_reset
    hpsi kappa tau (C e) (C (ring.rightNeighbor e)) hreset]

/-- The birth-signal wrapper is exactly inert on an active responder-deletion
edge.  If either input is already a leader this is immediate; otherwise the
established PeaceView frame shows that the old output is still two followers. -/
theorem localStep_birthSignalZero_eq_resetProbe_of_active_responder
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (C : EConfig n psi kappa tau) (e : Fin n)
    (hfree : ResetCommandFree C)
    (hactive : deletionActive
      (C (ring.rightNeighbor e)).core.erase = true) :
    localStep ring
        (wallSweepBirthSignalZeroPathStallTransition
          hpsi kappa tau) C e =
      localStep ring
        (wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
          hpsi kappa tau) C e := by
  let j := ring.rightNeighbor e
  have hje : j ≠ e := rightNeighbor_ne_self_of_one_lt ring hn e
  let Troot := wallSweepPreCheckResetLeaderSinkPathStallTransition
    hpsi kappa tau
  let Told :=
    wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
      hpsi kappa tau
  let Tnew := wallSweepBirthSignalZeroPathStallTransition
    hpsi kappa tau
  let Droot := localStep ring Troot C e
  let Dold := localStep ring Told C e
  have heq : Dold = Droot := by
    simpa [Dold, Droot, Told, Troot] using
      localStep_resetProbe_eq_leaderSink_of_source_reset_false
        hpsi ring C e (hfree e)
  have hpeaceRoot :=
    wallSweepPreCheckResetLeaderSink_active_edge_peaceView_frame
      hpsi ring hn C e hactive
  change PeaceViewConfigFrame C Droot at hpeaceRoot
  have hpeace : PeaceViewConfigFrame C Dold := by
    rw [heq]
    exact hpeaceRoot
  have hpair : Tnew (C e) (C j) = Told (C e) (C j) := by
    by_cases hl : (C e).core.erase.core.leader = true
    · simpa [Tnew, Told, j] using
        wallSweepBirthSignalZeroPathStall_eq_of_left_leader
          hpsi kappa tau (C e) (C j) hl
    · have hlFollower : (C e).core.erase.core.leader = false := by
        cases h : (C e).core.erase.core.leader with
        | false => rfl
        | true => exact False.elim (hl h)
      by_cases hr : (C j).core.erase.core.leader = true
      · simpa [Tnew, Told, j] using
          wallSweepBirthSignalZeroPathStall_eq_of_right_leader
            hpsi kappa tau (C e) (C j) hr
      · have hrFollower : (C j).core.erase.core.leader = false := by
          cases h : (C j).core.erase.core.leader with
          | false => rfl
          | true => exact False.elim (hr h)
        have holdLeft : (Told (C e) (C j)).1.core.erase.core.leader =
            false := by
          have hview := congrArg
            (fun v : PPLLNoCheckBirthConditionTwoPhysical.PeaceView psi =>
              v.leader) (hpeace e)
          change (Dold e).core.erase.core.leader =
            (C e).core.erase.core.leader at hview
          simpa [Dold, Told, localStep, j, hlFollower] using hview
        have holdRight : (Told (C e) (C j)).2.core.erase.core.leader =
            false := by
          have hview := congrArg
            (fun v : PPLLNoCheckBirthConditionTwoPhysical.PeaceView psi =>
              v.leader) (hpeace j)
          change (Dold j).core.erase.core.leader =
            (C j).core.erase.core.leader at hview
          simpa [Dold, Told, localStep, j, hje, hrFollower] using hview
        simpa [Tnew, Told, j] using
          wallSweepBirthSignalZeroPathStall_eq_of_output_followers
            hpsi kappa tau (C e) (C j) holdLeft holdRight
  exact localStep_eq_of_pair_eq ring Tnew Told C e
    (by simpa [Tnew, Told, j] using hpair)

/-- Uniform transport for scheduler steps that keep the same named unique
leader.  If the active pair touches that leader the wrapper is inert by its
input guard; otherwise uniqueness makes both old outputs followers. -/
theorem localStep_birthSignalZero_eq_resetProbe_of_fixed_unique_leader
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (C : EConfig n psi kappa tau) (e leader : Fin n)
    (hCLeader : (C leader).core.erase.core.leader = true)
    (hunique : hasUniqueLeader n
      (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig
        (localStep ring
          (wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
            hpsi kappa tau) C e)))
    (hDLeader :
      (localStep ring
        (wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
          hpsi kappa tau) C e leader).core.erase.core.leader = true) :
    localStep ring
        (wallSweepBirthSignalZeroPathStallTransition
          hpsi kappa tau) C e =
      localStep ring
        (wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
          hpsi kappa tau) C e := by
  let j := ring.rightNeighbor e
  have hje : j ≠ e := rightNeighbor_ne_self_of_one_lt ring hn e
  let Told :=
    wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
      hpsi kappa tau
  let Tnew := wallSweepBirthSignalZeroPathStallTransition
    hpsi kappa tau
  let Dold := localStep ring Told C e
  by_cases hel : e = leader
  · subst e
    have hpair := wallSweepBirthSignalZeroPathStall_eq_of_left_leader
      hpsi kappa tau (C leader) (C (ring.rightNeighbor leader)) hCLeader
    exact localStep_eq_of_pair_eq ring Tnew Told C leader
      (by simpa [Tnew, Told] using hpair)
  · by_cases hjl : j = leader
    · have hpair := wallSweepBirthSignalZeroPathStall_eq_of_right_leader
        hpsi kappa tau (C e) (C j) (by simpa [← hjl] using hCLeader)
      exact localStep_eq_of_pair_eq ring Tnew Told C e
        (by simpa [Tnew, Told, j] using hpair)
    · obtain ⟨only, _honlyLeader, honly⟩ := hunique
      have hleaderOnly : leader = only := by
        apply honly leader
        exact hDLeader
      have hDfollowers : ∀ i, i ≠ leader →
          (Dold i).core.erase.core.leader = false := by
        intro i hil
        cases hi : (Dold i).core.erase.core.leader with
        | false => rfl
        | true =>
            have hiOnly : i = only := by
              apply honly i
              exact hi
            exact False.elim (hil (hiOnly.trans hleaderOnly.symm))
      have holdLeft : (Told (C e) (C j)).1.core.erase.core.leader =
          false := by
        have := hDfollowers e hel
        simpa [Dold, Told, localStep, j] using this
      have holdRight : (Told (C e) (C j)).2.core.erase.core.leader =
          false := by
        have hjne : j ≠ leader := hjl
        have := hDfollowers j hjne
        simpa [Dold, Told, localStep, j, hje] using this
      have hpair := wallSweepBirthSignalZeroPathStall_eq_of_output_followers
        hpsi kappa tau (C e) (C j) holdLeft holdRight
      exact localStep_eq_of_pair_eq ring Tnew Told C e
        (by simpa [Tnew, Told, j] using hpair)

/-- A priority-open follower edge of the rooted transition preserves global
reset freedom. -/
theorem ResetCommandFree.localStep_leaderSink_of_priority_open_follower
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (C : EConfig n psi kappa tau) (e : Fin n)
    (hopen : WallPriorityOpen (C e) (C (ring.rightNeighbor e)))
    (hfree : ResetCommandFree C)
    (hfollower : (C e).core.erase.core.leader = false) :
    ResetCommandFree
      (localStep ring
        (wallSweepPreCheckResetLeaderSinkPathStallTransition
          hpsi kappa tau) C e) := by
  let j := ring.rightNeighbor e
  have hje : j ≠ e := rightNeighbor_ne_self_of_one_lt ring hn e
  let q := wallSweepPreCheckResetLeaderSinkPathStallTransition
    hpsi kappa tau (C e) (C j)
  have hpair :=
    wallSweepPreCheckResetLeaderSinkPathStall_priority_open_reset_free_of_follower
      hpsi kappa tau (C e) (C j) hopen hfollower (hfree e) (hfree j)
  change q.1.core.erase.core.reset_cmd = false ∧
    q.2.core.erase.core.reset_cmd = false at hpair
  intro i
  by_cases hie : i = e
  · subst i
    simpa [localStep, q, j] using hpair.1
  · by_cases hij : i = j
    · subst i
      simpa [localStep, q, j, hje] using hpair.2
    · simpa [localStep, hie, hij, j] using hfree i

set_option maxHeartbeats 2000000 in
/-- The integrated transition has its own canonical deletion drain on a
reset-free input.  Every inserted interrupt preserves the complete PeaceView,
the P-prime control shadow, and reset freedom. -/
theorem exists_resetProbeLeaderSinkDeletionDrain
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (C : EConfig n psi kappa tau) (hfree : ResetCommandFree C) :
    ∃ schedule : DetSchedule n,
      schedule.length ≤ comparisonPathCount C ∧
      (NoActiveDeletion C → schedule = []) ∧
      let D := runLocalSchedule ring
        (wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
          hpsi kappa tau) C schedule
      NoActiveDeletion D ∧
        PeaceViewConfigFrame C D ∧
        PPLLPpsiLeaderCreationRepair.PpsiControlConfigFrame C D ∧
        ResetCommandFree D := by
  generalize hk : comparisonPathCount C = k
  induction k using Nat.strongRecOn generalizing C with
  | ind k ih =>
      by_cases hnone : NoActiveDeletion C
      · exact ⟨[], by simp, fun _ => rfl, hnone,
          PeaceViewConfigFrame.refl C,
          PPLLPpsiLeaderCreationRepair.PpsiControlConfigFrame.refl C,
          hfree⟩
      · have hexists : ∃ j : Fin n,
            deletionActive (C j).core.erase = true := by
          apply Classical.byContradiction
          intro hnot
          apply hnone
          intro i
          cases hi : deletionActive (C i).core.erase with
          | false => rfl
          | true => exact False.elim (hnot ⟨i, hi⟩)
        obtain ⟨j, hj⟩ := hexists
        let e := ring.leftNeighbor j
        have hneighbor : ring.rightNeighbor e = j :=
          rightNeighbor_leftNeighbor_wall ring j
        let C₁ := localStep ring
          (wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
            hpsi kappa tau) C e
        have heqStep :=
          localStep_resetProbe_eq_leaderSink_of_source_reset_false
            hpsi ring C e (hfree e)
        change C₁ = localStep ring
          (wallSweepPreCheckResetLeaderSinkPathStallTransition
            hpsi kappa tau) C e at heqStep
        have hstep := wallSweepPreCheckResetLeaderSink_active_edge_decreases
          hpsi ring hn C e (by simpa [hneighbor] using hj)
        rw [← heqStep] at hstep
        change comparisonPathCount C₁ < comparisonPathCount C ∧
          ResetEchoConfigFrame C C₁ at hstep
        have hpeace :=
          wallSweepPreCheckResetLeaderSink_active_edge_peaceView_frame
            hpsi ring hn C e (by simpa [hneighbor] using hj)
        rw [← heqStep] at hpeace
        change PeaceViewConfigFrame C C₁ at hpeace
        have holdEq := localStep_leaderSink_eq_preCheckReset_of_active_host
          hpsi ring C e (by simpa [hneighbor] using hj)
        have hcontrol :=
          PPLLPpsiLeaderCreationRepair.wallSweepPreCheckResetPathStall_active_edge_ppsiControlFrame
            hpsi ring hn C e (by simpa [hneighbor] using hj)
        rw [← holdEq, ← heqStep] at hcontrol
        change PPLLPpsiLeaderCreationRepair.PpsiControlConfigFrame C C₁
          at hcontrol
        have hfree₁ : ResetCommandFree C₁ := by
          intro i
          exact (hstep.2 i).2.2.1.trans (hfree i)
        have hlt : comparisonPathCount C₁ < k := by
          rw [← hk]
          exact hstep.1
        obtain ⟨tail, htailLength, htailEmpty, htailNoActive,
          htailPeace, htailControl, htailFree⟩ :=
          ih (comparisonPathCount C₁) hlt C₁ hfree₁ rfl
        refine ⟨e :: tail, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · simp only [List.length_cons]
          omega
        · intro hC
          exact (hnone hC).elim
        · exact htailNoActive
        · exact hpeace.trans htailPeace
        · exact hcontrol.trans htailControl
        · exact htailFree

set_option maxHeartbeats 2000000 in
/-- The canonical deletion drain is unchanged by the birth-signal repair.
Every scheduled edge already has an active responder, so the repair wrapper is
pointwise inert throughout the drain. -/
theorem exists_birthSignalZeroDeletionDrain
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (C : EConfig n psi kappa tau) (hfree : ResetCommandFree C) :
    ∃ schedule : DetSchedule n,
      schedule.length ≤ comparisonPathCount C ∧
      (NoActiveDeletion C → schedule = []) ∧
      let D := runLocalSchedule ring
        (wallSweepBirthSignalZeroPathStallTransition
          hpsi kappa tau) C schedule
      NoActiveDeletion D ∧
        PeaceViewConfigFrame C D ∧
        PPLLPpsiLeaderCreationRepair.PpsiControlConfigFrame C D ∧
        ResetCommandFree D := by
  generalize hk : comparisonPathCount C = k
  induction k using Nat.strongRecOn generalizing C with
  | ind k ih =>
      by_cases hnone : NoActiveDeletion C
      · exact ⟨[], by simp, fun _ => rfl, hnone,
          PeaceViewConfigFrame.refl C,
          PPLLPpsiLeaderCreationRepair.PpsiControlConfigFrame.refl C,
          hfree⟩
      · have hexists : ∃ j : Fin n,
            deletionActive (C j).core.erase = true := by
          apply Classical.byContradiction
          intro hnot
          apply hnone
          intro i
          cases hi : deletionActive (C i).core.erase with
          | false => rfl
          | true => exact False.elim (hnot ⟨i, hi⟩)
        obtain ⟨j, hj⟩ := hexists
        let e := ring.leftNeighbor j
        have hneighbor : ring.rightNeighbor e = j :=
          rightNeighbor_leftNeighbor_wall ring j
        let C₁ := localStep ring
          (wallSweepBirthSignalZeroPathStallTransition
            hpsi kappa tau) C e
        have hnewEq :=
          localStep_birthSignalZero_eq_resetProbe_of_active_responder
            hpsi ring hn C e hfree (by simpa [hneighbor] using hj)
        have holdEq :=
          localStep_resetProbe_eq_leaderSink_of_source_reset_false
            hpsi ring C e (hfree e)
        have heqStep : C₁ = localStep ring
            (wallSweepPreCheckResetLeaderSinkPathStallTransition
              hpsi kappa tau) C e := by
          change localStep ring
              (wallSweepBirthSignalZeroPathStallTransition
                hpsi kappa tau) C e = _
          exact hnewEq.trans holdEq
        have hstep := wallSweepPreCheckResetLeaderSink_active_edge_decreases
          hpsi ring hn C e (by simpa [hneighbor] using hj)
        rw [← heqStep] at hstep
        change comparisonPathCount C₁ < comparisonPathCount C ∧
          ResetEchoConfigFrame C C₁ at hstep
        have hpeace :=
          wallSweepPreCheckResetLeaderSink_active_edge_peaceView_frame
            hpsi ring hn C e (by simpa [hneighbor] using hj)
        rw [← heqStep] at hpeace
        change PeaceViewConfigFrame C C₁ at hpeace
        have hrootEq := localStep_leaderSink_eq_preCheckReset_of_active_host
          hpsi ring C e (by simpa [hneighbor] using hj)
        have hcontrol :=
          PPLLPpsiLeaderCreationRepair.wallSweepPreCheckResetPathStall_active_edge_ppsiControlFrame
            hpsi ring hn C e (by simpa [hneighbor] using hj)
        rw [← hrootEq, ← heqStep] at hcontrol
        change PPLLPpsiLeaderCreationRepair.PpsiControlConfigFrame C C₁
          at hcontrol
        have hfree₁ : ResetCommandFree C₁ := by
          intro i
          exact (hstep.2 i).2.2.1.trans (hfree i)
        have hlt : comparisonPathCount C₁ < k := by
          rw [← hk]
          exact hstep.1
        obtain ⟨tail, htailLength, htailEmpty, htailNoActive,
          htailPeace, htailControl, htailFree⟩ :=
          ih (comparisonPathCount C₁) hlt C₁ hfree₁ rfl
        refine ⟨e :: tail, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · simp only [List.length_cons]
          omega
        · intro hC
          exact (hnone hC).elim
        · exact htailNoActive
        · exact hpeace.trans htailPeace
        · exact hcontrol.trans htailControl
        · exact htailFree

set_option maxHeartbeats 2000000 in
/-- A raw P-prime first-leader word can be simulated by the complete
reset-aware transition once the physical configuration is reset-free.  Each
intended raw edge is preceded by the integrated canonical deletion drain, and
the simulation stops at the first physical leader. -/
private theorem exists_stopped_unique_resetProbe_simulation
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (raw : Fin n → AgentState psi)
    (physical : EConfig n psi kappa tau)
    (hrefine :
      PPLLPpsiLeaderCreationRepair.PpsiControlConfigRefines raw physical)
    (hrawLeaderless :
      PPLLPpsiLeaderCreationSchedule.RawLeaderless raw)
    (hphysicalLeaderless :
      PPLLPpsiLeaderCreationSchedule.RawLeaderless
        (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig physical))
    (hfree : ResetCommandFree physical)
    (word : DetSchedule n)
    (hfinal : PPLLPpsiLeaderCreationSchedule.RawHasLeader
      (runLocalSchedule ring (pPsiLeaderProbeWall hpsi) raw word)) :
    ∃ actual : DetSchedule n,
      let D := runLocalSchedule ring
        (wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
          hpsi kappa tau) physical actual
      hasUniqueLeader n
          (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig D) ∧
        PPLLPpsiLeaderCreationRepair.bulletTwoCount D ≤
          PPLLPpsiLeaderCreationRepair.bulletTwoCount physical ∧
        ResetCommandFree D := by
  induction word generalizing raw physical with
  | nil =>
      simp only [runLocalSchedule] at hfinal
      obtain ⟨i, hi⟩ := hfinal
      rw [hrawLeaderless i] at hi
      contradiction
  | cons e rest ih =>
      obtain ⟨drain, _hdrainLength, _hdrainEmpty, hnoActive,
        hpeace, hcontrol, hfreeDrained⟩ :=
        exists_resetProbeLeaderSinkDeletionDrain
          hpsi ring hn physical hfree
      let drained := runLocalSchedule ring
        (wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
          hpsi kappa tau)
        physical drain
      change NoActiveDeletion drained at hnoActive
      change PeaceViewConfigFrame physical drained at hpeace
      change PPLLPpsiLeaderCreationRepair.PpsiControlConfigFrame
        physical drained at hcontrol
      change ResetCommandFree drained at hfreeDrained
      have hcountDrained :
          PPLLPpsiLeaderCreationRepair.bulletTwoCount drained =
            PPLLPpsiLeaderCreationRepair.bulletTwoCount physical :=
        PPLLPpsiLeaderCreationRepair.bulletTwoCount_eq_of_peaceViewConfigFrame
          hpeace
      have hrefineDrained :
          PPLLPpsiLeaderCreationRepair.PpsiControlConfigRefines raw drained :=
        hrefine.of_frame hcontrol
      have hphysicalDrainedLeaderless :
          PPLLPpsiLeaderCreationSchedule.RawLeaderless
            (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig drained) :=
        PPLLPpsiLeaderCreationRepair.eraseExpiringConfig_leaderless_of_peaceFrame
          hphysicalLeaderless hpeace
      have hopen : WallPriorityOpen
          (drained e) (drained (ring.rightNeighbor e)) :=
        WallPriorityOpen.of_noActiveDeletion drained hnoActive ring e
      let raw1 := localStep ring (pPsiLeaderProbeWall hpsi) raw e
      let old1 := localStep ring
        (wallSweepPreCheckResetLeaderSinkPathStallTransition
          hpsi kappa tau)
        drained e
      let physical1 := localStep ring
        (wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
          hpsi kappa tau)
        drained e
      have hstepEq : physical1 = old1 := by
        simpa [physical1, old1] using
          localStep_resetProbe_eq_leaderSink_of_source_reset_false
            hpsi ring drained e (hfreeDrained e)
      have hfreeOld1 : ResetCommandFree old1 := by
        simpa only [old1] using
          hfreeDrained.localStep_leaderSink_of_priority_open_follower
            hpsi ring hn drained e hopen (hphysicalDrainedLeaderless e)
      have hfreePhysical1 : ResetCommandFree physical1 := by
        rw [hstepEq]
        exact hfreeOld1
      have hcountOld1 :
          PPLLPpsiLeaderCreationRepair.bulletTwoCount old1 ≤
            PPLLPpsiLeaderCreationRepair.bulletTwoCount drained := by
        simpa only [old1] using
          PPLLPpsiLeaderCreationRepair.localStepLeaderSink_priority_open_left_follower_bulletTwoCount_le
            hpsi kappa tau ring hn drained e hopen
              (hphysicalDrainedLeaderless e)
      have hcountPhysical1 :
          PPLLPpsiLeaderCreationRepair.bulletTwoCount physical1 ≤
            PPLLPpsiLeaderCreationRepair.bulletTwoCount physical := by
        rw [hstepEq]
        exact Nat.le_trans hcountOld1 (Nat.le_of_eq hcountDrained)
      by_cases hbirth :
          (raw (ring.rightNeighbor e)).probe = true ∧
            isBarrier hpsi (raw e) (raw (ring.rightNeighbor e))
      · have hphysicalBirthOld :
            PPLLPpsiLeaderCreationSchedule.RawHasLeader
              (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig old1) := by
          simpa only [old1] using
            PPLLPpsiLeaderCreationRepair.raw_birth_edge_creates_physical_leaderSink
              hpsi kappa tau ring hn raw drained e hrefineDrained
                hphysicalDrainedLeaderless hopen hbirth.1 hbirth.2
        have hphysicalUniqueOld : hasUniqueLeader n
            (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig old1) := by
          simpa only [old1] using
            PPLLPpsiLeaderCreationRepair.localStepLeaderSink_first_physical_leader_unique
              hpsi ring hn drained e hopen hphysicalDrainedLeaderless
                hphysicalBirthOld
        have hphysicalUnique : hasUniqueLeader n
            (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig physical1) := by
          rw [hstepEq]
          exact hphysicalUniqueOld
        refine ⟨drain ++ [e], ?_⟩
        rw [runLocalSchedule_append_generic]
        simpa [drained, physical1, runLocalSchedule] using
          And.intro hphysicalUnique
            (And.intro hcountPhysical1 hfreePhysical1)
      · have hraw1Leaderless :
            PPLLPpsiLeaderCreationSchedule.RawLeaderless raw1 :=
          PPLLPpsiLeaderCreationRepair.rawLeaderless_localStep_pPsiLeaderProbeWall_of_not_birth
            hpsi ring hn raw e hrawLeaderless hbirth
        have hrefineOld1 :
            PPLLPpsiLeaderCreationRepair.PpsiControlConfigRefines raw1 old1 := by
          simpa only [raw1, old1] using
            PPLLPpsiLeaderCreationRepair.ppsiControlRefines_localStepLeaderSink_of_priority_open
              hpsi kappa tau ring hn raw drained e hrefineDrained
                hrawLeaderless hphysicalDrainedLeaderless hopen
        have hrefine1 :
            PPLLPpsiLeaderCreationRepair.PpsiControlConfigRefines
              raw1 physical1 := by
          rw [hstepEq]
          exact hrefineOld1
        by_cases hphysical1 :
            PPLLPpsiLeaderCreationSchedule.RawHasLeader
              (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig physical1)
        · have hphysicalOld1 :
              PPLLPpsiLeaderCreationSchedule.RawHasLeader
                (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig old1) := by
            rw [← hstepEq]
            exact hphysical1
          have hphysicalUniqueOld : hasUniqueLeader n
              (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig old1) := by
            simpa only [old1] using
              PPLLPpsiLeaderCreationRepair.localStepLeaderSink_first_physical_leader_unique
                hpsi ring hn drained e hopen hphysicalDrainedLeaderless
                  hphysicalOld1
          have hphysicalUnique : hasUniqueLeader n
              (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig physical1) := by
            rw [hstepEq]
            exact hphysicalUniqueOld
          refine ⟨drain ++ [e], ?_⟩
          rw [runLocalSchedule_append_generic]
          simpa [drained, physical1, runLocalSchedule] using
            And.intro hphysicalUnique
              (And.intro hcountPhysical1 hfreePhysical1)
        · have hphysical1Leaderless :
              PPLLPpsiLeaderCreationSchedule.RawLeaderless
                (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig physical1) :=
            PPLLPpsiLeaderCreationSchedule.RawLeaderless.of_not_hasLeader
              hphysical1
          have hfinal1 : PPLLPpsiLeaderCreationSchedule.RawHasLeader
              (runLocalSchedule ring (pPsiLeaderProbeWall hpsi)
                raw1 rest) := by
            simpa [raw1, runLocalSchedule] using hfinal
          obtain ⟨tail, htailUnique, htailCount, htailFree⟩ :=
            ih raw1 physical1 hrefine1 hraw1Leaderless
              hphysical1Leaderless hfreePhysical1 hfinal1
          refine ⟨drain ++ (e :: tail), ?_⟩
          rw [runLocalSchedule_append_generic]
          simpa [drained, physical1, runLocalSchedule] using
            And.intro htailUnique
              (And.intro (Nat.le_trans htailCount hcountPhysical1)
                htailFree)

set_option maxHeartbeats 2000000 in
/-- The first-leader simulation for the birth-signal repair.  Besides the
established uniqueness and nonexpansive live-bullet bound, it names the first
physical leader and proves that its absence signal is zero. -/
private theorem exists_stopped_unique_birthSignalZero_simulation
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (raw : Fin n → AgentState psi)
    (physical : EConfig n psi kappa tau)
    (hrefine :
      PPLLPpsiLeaderCreationRepair.PpsiControlConfigRefines raw physical)
    (hrawLeaderless :
      PPLLPpsiLeaderCreationSchedule.RawLeaderless raw)
    (hphysicalLeaderless :
      PPLLPpsiLeaderCreationSchedule.RawLeaderless
        (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig physical))
    (hfree : ResetCommandFree physical)
    (word : DetSchedule n)
    (hfinal : PPLLPpsiLeaderCreationSchedule.RawHasLeader
      (runLocalSchedule ring (pPsiLeaderProbeWall hpsi) raw word)) :
    ∃ (actual : DetSchedule n) (leader : Fin n),
      let D := runLocalSchedule ring
        (wallSweepBirthSignalZeroPathStallTransition
          hpsi kappa tau) physical actual
      hasUniqueLeader n
          (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig D) ∧
        (D leader).core.erase.core.leader = true ∧
        (D leader).core.erase.core.signal_B = ⟨0, by omega⟩ ∧
        PPLLPpsiLeaderCreationRepair.bulletTwoCount D ≤
          PPLLPpsiLeaderCreationRepair.bulletTwoCount physical ∧
        ResetCommandFree D := by
  induction word generalizing raw physical with
  | nil =>
      simp only [runLocalSchedule] at hfinal
      obtain ⟨i, hi⟩ := hfinal
      rw [hrawLeaderless i] at hi
      contradiction
  | cons e rest ih =>
      obtain ⟨drain, _hdrainLength, _hdrainEmpty, hnoActive,
        hpeace, hcontrol, hfreeDrained⟩ :=
        exists_birthSignalZeroDeletionDrain
          hpsi ring hn physical hfree
      let drained := runLocalSchedule ring
        (wallSweepBirthSignalZeroPathStallTransition
          hpsi kappa tau)
        physical drain
      change NoActiveDeletion drained at hnoActive
      change PeaceViewConfigFrame physical drained at hpeace
      change PPLLPpsiLeaderCreationRepair.PpsiControlConfigFrame
        physical drained at hcontrol
      change ResetCommandFree drained at hfreeDrained
      have hcountDrained :
          PPLLPpsiLeaderCreationRepair.bulletTwoCount drained =
            PPLLPpsiLeaderCreationRepair.bulletTwoCount physical :=
        PPLLPpsiLeaderCreationRepair.bulletTwoCount_eq_of_peaceViewConfigFrame
          hpeace
      have hrefineDrained :
          PPLLPpsiLeaderCreationRepair.PpsiControlConfigRefines raw drained :=
        hrefine.of_frame hcontrol
      have hphysicalDrainedLeaderless :
          PPLLPpsiLeaderCreationSchedule.RawLeaderless
            (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig drained) :=
        PPLLPpsiLeaderCreationRepair.eraseExpiringConfig_leaderless_of_peaceFrame
          hphysicalLeaderless hpeace
      have hopen : WallPriorityOpen
          (drained e) (drained (ring.rightNeighbor e)) :=
        WallPriorityOpen.of_noActiveDeletion drained hnoActive ring e
      let raw1 := localStep ring (pPsiLeaderProbeWall hpsi) raw e
      let old1 := localStep ring
        (wallSweepPreCheckResetLeaderSinkPathStallTransition
          hpsi kappa tau) drained e
      let reset1 := localStep ring
        (wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
          hpsi kappa tau) drained e
      let physical1 := localStep ring
        (wallSweepBirthSignalZeroPathStallTransition
          hpsi kappa tau) drained e
      have hresetEq : reset1 = old1 := by
        simpa [reset1, old1] using
          localStep_resetProbe_eq_leaderSink_of_source_reset_false
            hpsi ring drained e (hfreeDrained e)
      have hbirthFrameReset : BirthSignalConfigFrame reset1 physical1 := by
        simpa only [reset1, physical1] using
          localStep_birthSignalZero_frame hpsi ring drained e
      have hbirthFrameOld : BirthSignalConfigFrame old1 physical1 := by
        rw [← hresetEq]
        exact hbirthFrameReset
      have hfreeOld1 : ResetCommandFree old1 := by
        simpa only [old1] using
          hfreeDrained.localStep_leaderSink_of_priority_open_follower
            hpsi ring hn drained e hopen (hphysicalDrainedLeaderless e)
      have hfreeReset1 : ResetCommandFree reset1 := by
        rw [hresetEq]
        exact hfreeOld1
      have hfreePhysical1 : ResetCommandFree physical1 :=
        (resetCommandFree_iff_of_birthSignalConfigFrame
          hbirthFrameReset).2 hfreeReset1
      have hcountOld1 :
          PPLLPpsiLeaderCreationRepair.bulletTwoCount old1 ≤
            PPLLPpsiLeaderCreationRepair.bulletTwoCount drained := by
        simpa only [old1] using
          PPLLPpsiLeaderCreationRepair.localStepLeaderSink_priority_open_left_follower_bulletTwoCount_le
            hpsi kappa tau ring hn drained e hopen
              (hphysicalDrainedLeaderless e)
      have hcountPhysicalReset :
          PPLLPpsiLeaderCreationRepair.bulletTwoCount physical1 =
            PPLLPpsiLeaderCreationRepair.bulletTwoCount reset1 :=
        bulletTwoCount_eq_of_birthSignalConfigFrame hbirthFrameReset
      have hcountPhysical1 :
          PPLLPpsiLeaderCreationRepair.bulletTwoCount physical1 ≤
            PPLLPpsiLeaderCreationRepair.bulletTwoCount physical := by
        rw [hcountPhysicalReset, hresetEq]
        exact Nat.le_trans hcountOld1 (Nat.le_of_eq hcountDrained)
      by_cases hbirth :
          (raw (ring.rightNeighbor e)).probe = true ∧
            isBarrier hpsi (raw e) (raw (ring.rightNeighbor e))
      · have hphysicalBirthOld :
            PPLLPpsiLeaderCreationSchedule.RawHasLeader
              (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig old1) := by
          simpa only [old1] using
            PPLLPpsiLeaderCreationRepair.raw_birth_edge_creates_physical_leaderSink
              hpsi kappa tau ring hn raw drained e hrefineDrained
                hphysicalDrainedLeaderless hopen hbirth.1 hbirth.2
        have hphysicalUniqueOld : hasUniqueLeader n
            (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig old1) := by
          simpa only [old1] using
            PPLLPpsiLeaderCreationRepair.localStepLeaderSink_first_physical_leader_unique
              hpsi ring hn drained e hopen hphysicalDrainedLeaderless
                hphysicalBirthOld
        have hphysicalUnique : hasUniqueLeader n
            (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig physical1) :=
          hasUniqueLeader_of_birthSignalConfigFrame
            hbirthFrameOld hphysicalUniqueOld
        obtain ⟨leader, hleaderPhysical⟩ :=
          (rawHasLeader_iff_of_birthSignalConfigFrame
            hbirthFrameOld).2 hphysicalBirthOld
        have hleaderPhysicalCore :
            (physical1 leader).core.erase.core.leader = true := by
          exact hleaderPhysical
        have hsignalZero :
            (physical1 leader).core.erase.core.signal_B = ⟨0, by omega⟩ := by
          simpa only [physical1] using
            localStep_birthSignalZero_new_leader_signal_zero
              hpsi ring hn drained e leader hphysicalDrainedLeaderless
                hleaderPhysicalCore
        refine ⟨drain ++ [e], leader, ?_⟩
        rw [runLocalSchedule_append_generic]
        simpa [drained, physical1, runLocalSchedule] using
          And.intro hphysicalUnique
            (And.intro hleaderPhysicalCore
              (And.intro hsignalZero
                (And.intro hcountPhysical1 hfreePhysical1)))
      · have hraw1Leaderless :
            PPLLPpsiLeaderCreationSchedule.RawLeaderless raw1 :=
          PPLLPpsiLeaderCreationRepair.rawLeaderless_localStep_pPsiLeaderProbeWall_of_not_birth
            hpsi ring hn raw e hrawLeaderless hbirth
        have hrefineOld1 :
            PPLLPpsiLeaderCreationRepair.PpsiControlConfigRefines raw1 old1 := by
          simpa only [raw1, old1] using
            PPLLPpsiLeaderCreationRepair.ppsiControlRefines_localStepLeaderSink_of_priority_open
              hpsi kappa tau ring hn raw drained e hrefineDrained
                hrawLeaderless hphysicalDrainedLeaderless hopen
        have hcontrolFrame :
            PPLLPpsiLeaderCreationRepair.PpsiControlConfigFrame old1 physical1 :=
          ppsiControlConfigFrame_of_birthSignalConfigFrame hbirthFrameOld
        have hrefine1 :
            PPLLPpsiLeaderCreationRepair.PpsiControlConfigRefines
              raw1 physical1 :=
          hrefineOld1.of_frame hcontrolFrame
        by_cases hphysical1 :
            PPLLPpsiLeaderCreationSchedule.RawHasLeader
              (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig physical1)
        · have hphysicalOld1 :
              PPLLPpsiLeaderCreationSchedule.RawHasLeader
                (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig old1) :=
            (rawHasLeader_iff_of_birthSignalConfigFrame
              hbirthFrameOld).1 hphysical1
          have hphysicalUniqueOld : hasUniqueLeader n
              (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig old1) := by
            simpa only [old1] using
              PPLLPpsiLeaderCreationRepair.localStepLeaderSink_first_physical_leader_unique
                hpsi ring hn drained e hopen hphysicalDrainedLeaderless
                  hphysicalOld1
          have hphysicalUnique : hasUniqueLeader n
              (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig physical1) :=
            hasUniqueLeader_of_birthSignalConfigFrame
              hbirthFrameOld hphysicalUniqueOld
          obtain ⟨leader, hleaderPhysical⟩ := hphysical1
          have hleaderPhysicalCore :
              (physical1 leader).core.erase.core.leader = true := by
            exact hleaderPhysical
          have hsignalZero :
              (physical1 leader).core.erase.core.signal_B = ⟨0, by omega⟩ := by
            simpa only [physical1] using
              localStep_birthSignalZero_new_leader_signal_zero
                hpsi ring hn drained e leader hphysicalDrainedLeaderless
                  hleaderPhysicalCore
          refine ⟨drain ++ [e], leader, ?_⟩
          rw [runLocalSchedule_append_generic]
          simpa [drained, physical1, runLocalSchedule] using
            And.intro hphysicalUnique
              (And.intro hleaderPhysicalCore
                (And.intro hsignalZero
                  (And.intro hcountPhysical1 hfreePhysical1)))
        · have hphysical1Leaderless :
              PPLLPpsiLeaderCreationSchedule.RawLeaderless
                (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig physical1) :=
            PPLLPpsiLeaderCreationSchedule.RawLeaderless.of_not_hasLeader
              hphysical1
          have hfinal1 : PPLLPpsiLeaderCreationSchedule.RawHasLeader
              (runLocalSchedule ring (pPsiLeaderProbeWall hpsi)
                raw1 rest) := by
            simpa [raw1, runLocalSchedule] using hfinal
          obtain ⟨tail, leader, htailUnique, htailLeader, htailSignal,
              htailCount, htailFree⟩ :=
            ih raw1 physical1 hrefine1 hraw1Leaderless
              hphysical1Leaderless hfreePhysical1 hfinal1
          refine ⟨drain ++ (e :: tail), leader, ?_⟩
          rw [runLocalSchedule_append_generic]
          simpa [drained, physical1, runLocalSchedule] using
            And.intro htailUnique
              (And.intro htailLeader
                (And.intro htailSignal
                  (And.intro (Nat.le_trans htailCount hcountPhysical1)
                    htailFree)))

set_option maxHeartbeats 2000000 in
/-- The bounded leaderless reset sweep is unchanged by the birth-signal
repair.  At each induction step the established transition is leaderless, so
the repair wrapper is exactly inert on that local interaction. -/
theorem exists_birthSignalZeroLeaderlessResetAdvanceSchedule
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (root : Fin n) (C : EConfig n psi kappa tau)
    (hnoActive : NoActiveDeletion C)
    (hleaderless : PPLLPpsiLeaderCreationSchedule.RawLeaderless
      (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig C))
    (hreset : (C root).core.erase.core.reset_cmd = true)
    (steps : Nat) (hsteps : steps ≤ n) :
    ∃ (word : DetSchedule n) (D : EConfig n psi kappa tau),
      D = runLocalSchedule ring
        (wallSweepBirthSignalZeroPathStallTransition
          hpsi kappa tau) C word ∧
      word.length ≤ steps ∧
      NoActiveDeletion D ∧
      PPLLPpsiLeaderCreationSchedule.RawLeaderless
        (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig D) ∧
      PPLLPpsiLeaderCreationRepair.bulletTwoCount D ≤
        PPLLPpsiLeaderCreationRepair.bulletTwoCount C ∧
      (resetCommandCount D < resetCommandCount C ∨
        (word = resetSweepSchedule ring root steps ∧
          LeaderlessResetAdvanceState hpsi ring root C D steps)) := by
  let Told := wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
    hpsi kappa tau
  let Tnew := wallSweepBirthSignalZeroPathStallTransition
    hpsi kappa tau
  induction steps with
  | zero =>
      exact ⟨[], C, rfl, by simp, hnoActive, hleaderless, Nat.le_refl _,
        Or.inr ⟨rfl,
        leaderlessResetAdvanceState_zero
          hpsi ring root C hnoActive hleaderless hreset⟩⟩
  | succ steps ih =>
      have hprevBound : steps ≤ n := by omega
      obtain ⟨word, D, hD, hwordLength, hDNoActive,
        hDLeaderless, hDCount, hout⟩ := ih hprevBound
      rcases hout with hdrop | ⟨hword, hstate⟩
      · exact ⟨word, D, hD, by omega, hDNoActive, hDLeaderless,
          hDCount, Or.inl hdrop⟩
      · have hlt : steps < n := by omega
        let e := groupOffset ring root steps
        let oldE := localStep ring Told D e
        let E := localStep ring Tnew D e
        have hnext := hstate.step_or_resetCommandCount_lt
          hpsi ring hn root C D steps hlt
        change NoActiveDeletion oldE ∧
          PPLLPpsiLeaderCreationSchedule.RawLeaderless
            (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig oldE) ∧
          PPLLPpsiLeaderCreationRepair.bulletTwoCount oldE ≤
            PPLLPpsiLeaderCreationRepair.bulletTwoCount C ∧
          (resetCommandCount oldE < resetCommandCount C ∨
            LeaderlessResetAdvanceState hpsi ring root C oldE (steps + 1))
          at hnext
        obtain ⟨hOldNoActive, hOldLeaderless, hOldCount, hnext⟩ := hnext
        have heq : E = oldE := by
          change localStep ring
              (wallSweepBirthSignalZeroPathStallTransition
                hpsi kappa tau) D e =
            localStep ring
              (wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
                hpsi kappa tau) D e
          exact localStep_birthSignalZero_eq_of_resetProbe_result_leaderless
            hpsi ring hn D e hOldLeaderless
        rw [← heq] at hOldNoActive hOldLeaderless hOldCount hnext
        have hrun : E = runLocalSchedule ring Tnew C
            (resetSweepSchedule ring root (steps + 1)) := by
          rw [resetSweepSchedule]
          calc
            E = runLocalSchedule ring Tnew D [e] := rfl
            _ = runLocalSchedule ring Tnew
                (runLocalSchedule ring Tnew C word) [e] := by rw [← hD]
            _ = runLocalSchedule ring Tnew C (word ++ [e]) :=
              (runLocalSchedule_append_generic ring Tnew C word [e]).symm
            _ = runLocalSchedule ring Tnew C
                (resetSweepSchedule ring root steps ++ [e]) := by rw [hword]
        rcases hnext with hdrop | hstateNext
        · exact ⟨resetSweepSchedule ring root (steps + 1), E, hrun,
            Nat.le_of_eq
              (PPLLWallSweepEchoDrain.resetSweepSchedule_length
                ring root (steps + 1)),
            hOldNoActive, hOldLeaderless, hOldCount,
            Or.inl hdrop⟩
        · exact ⟨resetSweepSchedule ring root (steps + 1), E, hrun,
            Nat.le_of_eq
              (PPLLWallSweepEchoDrain.resetSweepSchedule_length
                ring root (steps + 1)),
            hOldNoActive, hOldLeaderless, hOldCount,
            Or.inr ⟨rfl, hstateNext⟩⟩

set_option maxHeartbeats 2000000 in
/-- One complete leaderless reset sweep strictly decreases the global reset
count under the birth-signal transition while preserving leaderlessness and
the live-bullet bound. -/
theorem exists_birthSignalZeroLeaderlessResetCommandCount_lt_of_source
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (hpsiLe : psi ≤ n) (root : Fin n)
    (C : EConfig n psi kappa tau)
    (hnoActive : NoActiveDeletion C)
    (hleaderless : PPLLPpsiLeaderCreationSchedule.RawLeaderless
      (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig C))
    (hreset : (C root).core.erase.core.reset_cmd = true) :
    ∃ (word : DetSchedule n) (D : EConfig n psi kappa tau),
      D = runLocalSchedule ring
        (wallSweepBirthSignalZeroPathStallTransition
          hpsi kappa tau) C word ∧
      NoActiveDeletion D ∧
      PPLLPpsiLeaderCreationSchedule.RawLeaderless
        (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig D) ∧
      PPLLPpsiLeaderCreationRepair.bulletTwoCount D ≤
        PPLLPpsiLeaderCreationRepair.bulletTwoCount C ∧
      resetCommandCount D < resetCommandCount C := by
  let Told := wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
    hpsi kappa tau
  let Tnew := wallSweepBirthSignalZeroPathStallTransition
    hpsi kappa tau
  obtain ⟨t, htpos, htpsi, htlabel⟩ :=
    exists_positive_step_to_last_label
      hpsi (C root).core.erase.core.label
  have htn : t ≤ n := Nat.le_trans htpsi hpsiLe
  obtain ⟨word₁, M, hM, _hword₁Length, hMNoActive,
      hMLeaderless, hMCount, hout₁⟩ :=
    exists_birthSignalZeroLeaderlessResetAdvanceSchedule
      hpsi ring hn root C hnoActive hleaderless hreset t htn
  rcases hout₁ with hdrop₁ | ⟨_hword₁, hstateM⟩
  · exact ⟨word₁, M, hM, hMNoActive, hMLeaderless, hMCount, hdrop₁⟩
  · have hMSourceLast :
        (M (groupOffset ring root t)).core.erase.core.label =
          ⟨psi - 1, by omega⟩ := by
      rw [hstateM.source_label]
      apply Fin.ext
      exact htlabel
    have hMPredecessorEcho :
        (M (groupOffset ring root (t - 1))).core.erase.core.echo = true :=
      hstateM.predecessor_echo_of_source_last htpos hMSourceLast
    let q := groupOffset ring root (t - 1)
    let p := groupOffset ring root t
    have hpRight : ring.rightNeighbor q = p := by
      have hnext := rightNeighbor_groupOffset ring root (t - 1)
      simpa [q, p, show t - 1 + 1 = t by omega] using hnext
    have htarget : groupOffset ring p (n - 1) = q := by
      rw [← hpRight]
      exact
        PPLLWallSweepRestartableProtected.groupOffset_rightNeighbor_last
          ring hn q
    have hMReset : (M p).core.erase.core.reset_cmd = true := by
      simpa [p] using hstateM.source_reset
    have hsecondBound : n - 2 ≤ n := by omega
    obtain ⟨word₂, N, hN, _hword₂Length, hNNoActive,
        hNLeaderless, hNCount, hout₂⟩ :=
      exists_birthSignalZeroLeaderlessResetAdvanceSchedule
        hpsi ring hn p M hMNoActive hMLeaderless hMReset
          (n - 2) hsecondBound
    rcases hout₂ with hdrop₂ | ⟨_hword₂, hstateN⟩
    · refine ⟨word₁ ++ word₂, N, ?_, hNNoActive,
          hNLeaderless, Nat.le_trans hNCount hMCount, ?_⟩
      · calc
          N = runLocalSchedule ring Tnew M word₂ := hN
          _ = runLocalSchedule ring Tnew
              (runLocalSchedule ring Tnew C word₁) word₂ := by rw [← hM]
          _ = runLocalSchedule ring Tnew C (word₁ ++ word₂) :=
            (runLocalSchedule_append_generic ring Tnew C word₁ word₂).symm
      · exact Nat.lt_of_lt_of_le hdrop₂ hstateM.reset_count_le
    · let e := groupOffset ring p (n - 2)
      let j := groupOffset ring p (n - 1)
      have hneighbor : ring.rightNeighbor e = j := by
        have hnext := rightNeighbor_groupOffset ring p (n - 2)
        simpa [e, j, show n - 2 + 1 = n - 1 by omega] using hnext
      have hjEcho : (N j).core.erase.core.echo = true := by
        have huntouched := hstateN.untouched_ahead (n - 1)
          (by omega) (by omega)
        change N j = M j at huntouched
        rw [huntouched]
        simpa [j, htarget, q] using hMPredecessorEcho
      have heFollower : (N e).core.erase.core.leader = false :=
        hstateN.leaderless e
      have hjFollower : (N j).core.erase.core.leader = false :=
        hstateN.leaderless j
      have heReset : (N e).core.erase.core.reset_cmd = true := by
        simpa [e] using hstateN.source_reset
      let oldE := localStep ring Told N e
      let E := localStep ring Tnew N e
      have hstrictOld :=
        resetAwareFollower_localStep_resetCommandCount_lt_of_echo_true
          hpsi ring hn N e hstateN.no_active heFollower heReset
            (by simpa [hneighbor] using hjFollower)
            (by simpa [hneighbor] using hjEcho)
      change resetCommandCount oldE < resetCommandCount N at hstrictOld
      have hframeOld := resetAwareFollower_localStep_normalizes
        hpsi ring hn N e hstateN.no_active heFollower heReset
          (by simpa [hneighbor] using hjFollower)
      change ResetAwareFollowerGlobalStepFrame hpsi ring N oldE e at hframeOld
      have hOldLeaderless :
          PPLLPpsiLeaderCreationSchedule.RawLeaderless
            (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig oldE) := by
        intro i
        change (oldE i).core.erase.core.leader = false
        rw [hframeOld.leader_eq i]
        exact hstateN.leaderless i
      have heq : E = oldE := by
        change localStep ring
              (wallSweepBirthSignalZeroPathStallTransition
                hpsi kappa tau) N e =
            localStep ring
              (wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
                hpsi kappa tau) N e
        exact localStep_birthSignalZero_eq_of_resetProbe_result_leaderless
          hpsi ring hn N e hOldLeaderless
      have hOldCountStep := resetAwareFollower_localStep_bulletTwoCount_le
        hpsi ring hn N e hstateN.no_active heFollower heReset
          (by simpa [hneighbor] using hjFollower)
      change PPLLPpsiLeaderCreationRepair.bulletTwoCount oldE ≤
        PPLLPpsiLeaderCreationRepair.bulletTwoCount N at hOldCountStep
      have hENoActive : NoActiveDeletion E := by
        rw [heq]
        exact hframeOld.no_active
      have hELeaderless :
          PPLLPpsiLeaderCreationSchedule.RawLeaderless
            (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig E) := by
        rw [heq]
        exact hOldLeaderless
      have hECountStep : PPLLPpsiLeaderCreationRepair.bulletTwoCount E ≤
          PPLLPpsiLeaderCreationRepair.bulletTwoCount N := by
        rw [heq]
        exact hOldCountStep
      have hECount : PPLLPpsiLeaderCreationRepair.bulletTwoCount E ≤
          PPLLPpsiLeaderCreationRepair.bulletTwoCount C :=
        Nat.le_trans hECountStep (Nat.le_trans hNCount hMCount)
      refine ⟨word₁ ++ word₂ ++ [e], E, ?_, hENoActive,
        hELeaderless, hECount, ?_⟩
      · calc
          E = runLocalSchedule ring Tnew N [e] := rfl
          _ = runLocalSchedule ring Tnew
              (runLocalSchedule ring Tnew M word₂) [e] := by rw [← hN]
          _ = runLocalSchedule ring Tnew M (word₂ ++ [e]) :=
            (runLocalSchedule_append_generic ring Tnew M word₂ [e]).symm
          _ = runLocalSchedule ring Tnew
              (runLocalSchedule ring Tnew C word₁) (word₂ ++ [e]) := by
                rw [← hM]
          _ = runLocalSchedule ring Tnew C
              (word₁ ++ (word₂ ++ [e])) :=
            (runLocalSchedule_append_generic
              ring Tnew C word₁ (word₂ ++ [e])).symm
          _ = runLocalSchedule ring Tnew C (word₁ ++ word₂ ++ [e]) := by
            rw [List.append_assoc]
      · have hstrict : resetCommandCount E < resetCommandCount N := by
          rw [heq]
          exact hstrictOld
        exact Nat.lt_of_lt_of_le hstrict
          (Nat.le_trans hstateN.reset_count_le hstateM.reset_count_le)

set_option maxHeartbeats 2000000 in
/-- Strong induction drains every reset command from a deletion-free
leaderless configuration under the birth-signal repair. -/
theorem exists_birthSignalZeroLeaderlessResetDrain
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (hpsiLe : psi ≤ n) (C : EConfig n psi kappa tau)
    (hnoActive : NoActiveDeletion C)
    (hleaderless : PPLLPpsiLeaderCreationSchedule.RawLeaderless
      (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig C)) :
    ∃ (word : DetSchedule n) (D : EConfig n psi kappa tau),
      D = runLocalSchedule ring
        (wallSweepBirthSignalZeroPathStallTransition
          hpsi kappa tau) C word ∧
      NoActiveDeletion D ∧
      PPLLPpsiLeaderCreationSchedule.RawLeaderless
        (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig D) ∧
      resetCommandCount D = 0 ∧
      PPLLPpsiLeaderCreationRepair.bulletTwoCount D ≤
        PPLLPpsiLeaderCreationRepair.bulletTwoCount C := by
  let T := wallSweepBirthSignalZeroPathStallTransition
    hpsi kappa tau
  let P : Nat → Prop := fun m =>
    ∀ C : EConfig n psi kappa tau,
      resetCommandCount C = m →
      NoActiveDeletion C →
      PPLLPpsiLeaderCreationSchedule.RawLeaderless
        (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig C) →
      ∃ (word : DetSchedule n) (D : EConfig n psi kappa tau),
        D = runLocalSchedule ring T C word ∧
        NoActiveDeletion D ∧
        PPLLPpsiLeaderCreationSchedule.RawLeaderless
          (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig D) ∧
        resetCommandCount D = 0 ∧
        PPLLPpsiLeaderCreationRepair.bulletTwoCount D ≤
          PPLLPpsiLeaderCreationRepair.bulletTwoCount C
  have hP : ∀ m, P m := by
    intro m
    induction m using Nat.strongRecOn with
    | ind m ih =>
        intro current hcount hcurrentNoActive hcurrentLeaderless
        by_cases hmzero : m = 0
        · exact ⟨[], current, rfl, hcurrentNoActive,
            hcurrentLeaderless, hcount.trans hmzero, Nat.le_refl _⟩
        · have hpos : 0 < resetCommandCount current := by omega
          obtain ⟨root, hreset⟩ :=
            exists_reset_source_of_resetCommandCount_pos current hpos
          obtain ⟨word₁, D, hD, hDNoActive, hDLeaderless,
              hDCount, hDlt⟩ :=
            exists_birthSignalZeroLeaderlessResetCommandCount_lt_of_source
              hpsi ring hn hpsiLe root current hcurrentNoActive
                hcurrentLeaderless hreset
          have hDltm : resetCommandCount D < m := by omega
          obtain ⟨word₂, E, hE, hENoActive, hELeaderless,
              hEzero, hECount⟩ :=
            ih (resetCommandCount D) hDltm D rfl hDNoActive hDLeaderless
          refine ⟨word₁ ++ word₂, E, ?_, hENoActive,
            hELeaderless, hEzero, Nat.le_trans hECount hDCount⟩
          calc
            E = runLocalSchedule ring T D word₂ := hE
            _ = runLocalSchedule ring T
                (runLocalSchedule ring T current word₁) word₂ := by
                  rw [← hD]
            _ = runLocalSchedule ring T current (word₁ ++ word₂) :=
              (runLocalSchedule_append_generic
                ring T current word₁ word₂).symm
  exact hP (resetCommandCount C) C rfl hnoActive hleaderless

/-- Nondivisibility now yields a unique first physical leader whose absence
signal is initialized to zero, from every deletion-free leaderless state of
the birth-signal repair. -/
theorem exists_birthSignalZero_hasUniqueLeader_of_not_dvd
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (hpsiLe : psi ≤ n) (hndvd : ¬ psi ∣ n)
    (C : EConfig n psi kappa tau)
    (hnoActive : NoActiveDeletion C)
    (hleaderless : PPLLPpsiLeaderCreationSchedule.RawLeaderless
      (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig C)) :
    ∃ (actual : DetSchedule n) (leader : Fin n),
      let D := runLocalSchedule ring
        (wallSweepBirthSignalZeroPathStallTransition
          hpsi kappa tau) C actual
      hasUniqueLeader n
          (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig D) ∧
        (D leader).core.erase.core.leader = true ∧
        (D leader).core.erase.core.signal_B = ⟨0, by omega⟩ ∧
        PPLLPpsiLeaderCreationRepair.bulletTwoCount D ≤
          PPLLPpsiLeaderCreationRepair.bulletTwoCount C ∧
        ResetCommandFree D := by
  obtain ⟨resetWord, D, hD, _hDNoActive, hDLeaderless,
      hDzero, hDCount⟩ :=
    exists_birthSignalZeroLeaderlessResetDrain
      hpsi ring hn hpsiLe C hnoActive hleaderless
  have hfreeD : ResetCommandFree D :=
    resetCommandFree_of_resetCommandCount_eq_zero D hDzero
  obtain ⟨rawWord, _hrawLength, hrawFinal⟩ :=
    PPLLPpsiLeaderCreationSchedule.exists_pPsiLeaderProbeWall_hasLeader_of_not_dvd
      hpsi ring hn hndvd
        (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig D)
  obtain ⟨actual, leader, hactualUnique, hactualLeader, hactualSignal,
      hactualCount, hactualFree⟩ :=
    exists_stopped_unique_birthSignalZero_simulation
      hpsi ring hn
        (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig D) D
        (fun _ => rfl) hDLeaderless hDLeaderless hfreeD
        rawWord hrawFinal
  refine ⟨resetWord ++ actual, leader, ?_⟩
  rw [runLocalSchedule_append_generic]
  rw [← hD]
  exact ⟨hactualUnique, hactualLeader, hactualSignal,
    Nat.le_trans hactualCount hDCount, hactualFree⟩

/-- Draining the comparison paths created around the first leader preserves
its zero signal and reaches the deletion-free regeneration boundary. -/
theorem
    exists_birthSignalZero_drainedUniqueLeader_bulletTwo_le_of_not_dvd
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (hpsiLe : psi ≤ n) (hndvd : ¬ psi ∣ n)
    (C : EConfig n psi kappa tau)
    (hnoActive : NoActiveDeletion C)
    (hleaderless : PPLLPpsiLeaderCreationSchedule.RawLeaderless
      (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig C)) :
    ∃ (actual : DetSchedule n) (leader : Fin n),
      let D := runLocalSchedule ring
        (wallSweepBirthSignalZeroPathStallTransition
          hpsi kappa tau) C actual
      NoActiveDeletion D ∧
        hasUniqueLeader n
          (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig D) ∧
        (D leader).core.erase.core.leader = true ∧
        (D leader).core.erase.core.signal_B = ⟨0, by omega⟩ ∧
        PPLLPpsiLeaderCreationRepair.bulletTwoCount D ≤
          PPLLPpsiLeaderCreationRepair.bulletTwoCount C ∧
        ResetCommandFree D := by
  obtain ⟨birth, leader, hbirthUnique, hbirthLeader, hbirthSignal,
      hbirthCount, hbirthFree⟩ :=
    exists_birthSignalZero_hasUniqueLeader_of_not_dvd
      hpsi ring hn hpsiLe hndvd C hnoActive hleaderless
  let T := wallSweepBirthSignalZeroPathStallTransition
    hpsi kappa tau
  let A := runLocalSchedule ring T C birth
  change hasUniqueLeader n
    (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig A) at hbirthUnique
  change (A leader).core.erase.core.leader = true at hbirthLeader
  change (A leader).core.erase.core.signal_B = ⟨0, by omega⟩ at hbirthSignal
  change PPLLPpsiLeaderCreationRepair.bulletTwoCount A ≤
    PPLLPpsiLeaderCreationRepair.bulletTwoCount C at hbirthCount
  change ResetCommandFree A at hbirthFree
  obtain ⟨drain, _hdrainLength, _hdrainEmpty, hnoActiveD,
      hpeace, _hcontrol, hfreeD⟩ :=
    exists_birthSignalZeroDeletionDrain hpsi ring hn A hbirthFree
  let D := runLocalSchedule ring T A drain
  change NoActiveDeletion D at hnoActiveD
  change PeaceViewConfigFrame A D at hpeace
  change ResetCommandFree D at hfreeD
  have huniqueD : hasUniqueLeader n
      (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig D) :=
    PPLLPpsiLeaderCreationRepair.hasUniqueLeader_of_peaceViewConfigFrame
      hpeace hbirthUnique
  have hleaderD : (D leader).core.erase.core.leader = true := by
    have hfield := congrArg
      (fun v : PPLLNoCheckBirthConditionTwoPhysical.PeaceView psi =>
        v.leader) (hpeace leader)
    exact hfield.trans hbirthLeader
  have hsignalD : (D leader).core.erase.core.signal_B = ⟨0, by omega⟩ := by
    have hfield := congrArg
      (fun v : PPLLNoCheckBirthConditionTwoPhysical.PeaceView psi =>
        v.signal_B) (hpeace leader)
    exact hfield.trans hbirthSignal
  have hcountD : PPLLPpsiLeaderCreationRepair.bulletTwoCount D ≤
      PPLLPpsiLeaderCreationRepair.bulletTwoCount C := by
    exact Nat.le_trans
      (Nat.le_of_eq
        (PPLLPpsiLeaderCreationRepair.bulletTwoCount_eq_of_peaceViewConfigFrame
          hpeace))
      hbirthCount
  refine ⟨birth ++ drain, leader, ?_⟩
  rw [runLocalSchedule_append_generic]
  simpa [A, D, T] using
    And.intro hnoActiveD
      (And.intro huniqueD
        (And.intro hleaderD
          (And.intro hsignalD (And.intro hcountD hfreeD))))

set_option maxHeartbeats 2000000 in
/-- Strong induction on the physical reset-command count drains every reset
from a deletion-free leaderless configuration under the complete reset-aware
transition. -/
theorem exists_leaderlessResetDrain
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (hpsiLe : psi ≤ n) (C : EConfig n psi kappa tau)
    (hnoActive : NoActiveDeletion C)
    (hleaderless : PPLLPpsiLeaderCreationSchedule.RawLeaderless
      (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig C)) :
    ∃ (word : DetSchedule n) (D : EConfig n psi kappa tau),
      D = runLocalSchedule ring
        (wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
          hpsi kappa tau) C word ∧
      NoActiveDeletion D ∧
      PPLLPpsiLeaderCreationSchedule.RawLeaderless
        (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig D) ∧
      resetCommandCount D = 0 ∧
      PPLLPpsiLeaderCreationRepair.bulletTwoCount D ≤
        PPLLPpsiLeaderCreationRepair.bulletTwoCount C := by
  let T := wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
    hpsi kappa tau
  let P : Nat → Prop := fun m =>
    ∀ C : EConfig n psi kappa tau,
      resetCommandCount C = m →
      NoActiveDeletion C →
      PPLLPpsiLeaderCreationSchedule.RawLeaderless
        (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig C) →
      ∃ (word : DetSchedule n) (D : EConfig n psi kappa tau),
        D = runLocalSchedule ring T C word ∧
        NoActiveDeletion D ∧
        PPLLPpsiLeaderCreationSchedule.RawLeaderless
          (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig D) ∧
        resetCommandCount D = 0 ∧
        PPLLPpsiLeaderCreationRepair.bulletTwoCount D ≤
          PPLLPpsiLeaderCreationRepair.bulletTwoCount C
  have hP : ∀ m, P m := by
    intro m
    induction m using Nat.strongRecOn with
    | ind m ih =>
        intro current hcount hcurrentNoActive hcurrentLeaderless
        by_cases hmzero : m = 0
        · exact ⟨[], current, rfl, hcurrentNoActive,
            hcurrentLeaderless, hcount.trans hmzero, Nat.le_refl _⟩
        · have hpos : 0 < resetCommandCount current := by omega
          obtain ⟨root, hreset⟩ :=
            exists_reset_source_of_resetCommandCount_pos current hpos
          obtain ⟨word₁, D, hD, hDNoActive, hDLeaderless,
              hDCount, hDlt⟩ :=
            exists_leaderlessResetCommandCount_lt_of_source
              hpsi ring hn hpsiLe root current hcurrentNoActive
                hcurrentLeaderless hreset
          have hDltm : resetCommandCount D < m := by omega
          obtain ⟨word₂, E, hE, hENoActive, hELeaderless,
              hEzero, hECount⟩ :=
            ih (resetCommandCount D) hDltm D rfl hDNoActive hDLeaderless
          refine ⟨word₁ ++ word₂, E, ?_, hENoActive,
            hELeaderless, hEzero, Nat.le_trans hECount hDCount⟩
          calc
            E = runLocalSchedule ring T D word₂ := hE
            _ = runLocalSchedule ring T
                (runLocalSchedule ring T current word₁) word₂ := by
                  rw [← hD]
            _ = runLocalSchedule ring T current (word₁ ++ word₂) :=
              (runLocalSchedule_append_generic
                ring T current word₁ word₂).symm
  exact hP (resetCommandCount C) C rfl hnoActive hleaderless

/-- Repaired nondivisible first-leader theorem for the complete reset-aware
transition.  From a deletion-free leaderless physical configuration, reset
commands are first drained; the raw P-prime producer is then simulated until
the first physical leader, which is unique. -/
theorem exists_resetProbeLeaderSink_hasUniqueLeader_of_not_dvd
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (hpsiLe : psi ≤ n) (hndvd : ¬ psi ∣ n)
    (C : EConfig n psi kappa tau)
    (hnoActive : NoActiveDeletion C)
    (hleaderless : PPLLPpsiLeaderCreationSchedule.RawLeaderless
      (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig C)) :
    ∃ actual : DetSchedule n,
      let D := runLocalSchedule ring
        (wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
          hpsi kappa tau) C actual
      hasUniqueLeader n
          (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig D) ∧
        PPLLPpsiLeaderCreationRepair.bulletTwoCount D ≤
          PPLLPpsiLeaderCreationRepair.bulletTwoCount C ∧
        ResetCommandFree D := by
  obtain ⟨resetWord, D, hD, _hDNoActive, hDLeaderless,
      hDzero, hDCount⟩ :=
    exists_leaderlessResetDrain
      hpsi ring hn hpsiLe C hnoActive hleaderless
  have hfreeD : ResetCommandFree D :=
    resetCommandFree_of_resetCommandCount_eq_zero D hDzero
  obtain ⟨rawWord, _hrawLength, hrawFinal⟩ :=
    PPLLPpsiLeaderCreationSchedule.exists_pPsiLeaderProbeWall_hasLeader_of_not_dvd
      hpsi ring hn hndvd
        (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig D)
  obtain ⟨actual, hactualUnique, hactualCount, hactualFree⟩ :=
    exists_stopped_unique_resetProbe_simulation
      hpsi ring hn
        (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig D) D
        (fun _ => rfl) hDLeaderless hDLeaderless hfreeD
        rawWord hrawFinal
  refine ⟨resetWord ++ actual, ?_⟩
  rw [runLocalSchedule_append_generic]
  rw [← hD]
  exact ⟨hactualUnique,
    Nat.le_trans hactualCount hDCount, hactualFree⟩

/-- The integrated first-leader producer followed by its own deletion drain
reaches the canonical regeneration boundary needed by the outer live-bullet
rank: deletion-free, reset-free, uniquely led, and nonincreasing in live
bullet mass. -/
theorem
    exists_resetProbeLeaderSink_drainedUniqueLeader_bulletTwo_le_of_not_dvd
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (hpsiLe : psi ≤ n) (hndvd : ¬ psi ∣ n)
    (C : EConfig n psi kappa tau)
    (hnoActive : NoActiveDeletion C)
    (hleaderless : PPLLPpsiLeaderCreationSchedule.RawLeaderless
      (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig C)) :
    ∃ (actual : DetSchedule n) (leader : Fin n),
      let D := runLocalSchedule ring
        (wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
          hpsi kappa tau) C actual
      NoActiveDeletion D ∧
        hasUniqueLeader n
          (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig D) ∧
        (D leader).core.erase.core.leader = true ∧
        PPLLPpsiLeaderCreationRepair.bulletTwoCount D ≤
          PPLLPpsiLeaderCreationRepair.bulletTwoCount C ∧
        ResetCommandFree D := by
  obtain ⟨birth, hbirthUnique, hbirthCount, hbirthFree⟩ :=
    exists_resetProbeLeaderSink_hasUniqueLeader_of_not_dvd
      hpsi ring hn hpsiLe hndvd C hnoActive hleaderless
  let A := runLocalSchedule ring
    (wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
      hpsi kappa tau) C birth
  change hasUniqueLeader n
    (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig A) at hbirthUnique
  change PPLLPpsiLeaderCreationRepair.bulletTwoCount A ≤
    PPLLPpsiLeaderCreationRepair.bulletTwoCount C at hbirthCount
  change ResetCommandFree A at hbirthFree
  obtain ⟨drain, _hdrainLength, _hdrainEmpty, hnoActiveD,
      hpeace, _hcontrol, hfreeD⟩ :=
    exists_resetProbeLeaderSinkDeletionDrain
      hpsi ring hn A hbirthFree
  let D := runLocalSchedule ring
    (wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
      hpsi kappa tau) A drain
  change NoActiveDeletion D at hnoActiveD
  change PeaceViewConfigFrame A D at hpeace
  change ResetCommandFree D at hfreeD
  have huniqueD : hasUniqueLeader n
      (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig D) :=
    PPLLPpsiLeaderCreationRepair.hasUniqueLeader_of_peaceViewConfigFrame
      hpeace hbirthUnique
  have hcountD : PPLLPpsiLeaderCreationRepair.bulletTwoCount D ≤
      PPLLPpsiLeaderCreationRepair.bulletTwoCount C := by
    exact Nat.le_trans
      (Nat.le_of_eq
        (PPLLPpsiLeaderCreationRepair.bulletTwoCount_eq_of_peaceViewConfigFrame
          hpeace))
      hbirthCount
  have huniqueKeep := huniqueD
  obtain ⟨leader, hleader, _honly⟩ := huniqueD
  change (D leader).core.erase.core.leader = true at hleader
  have hrun : D = runLocalSchedule ring
      (wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
        hpsi kappa tau) C (birth ++ drain) := by
    calc
      D = runLocalSchedule ring
          (wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
            hpsi kappa tau) A drain := rfl
      _ = runLocalSchedule ring
          (wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
            hpsi kappa tau)
          (runLocalSchedule ring
            (wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
              hpsi kappa tau) C birth) drain := rfl
      _ = runLocalSchedule ring
          (wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
            hpsi kappa tau) C (birth ++ drain) :=
        (runLocalSchedule_append_generic ring
          (wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
            hpsi kappa tau) C birth drain).symm
  refine ⟨birth ++ drain, leader, ?_⟩
  rw [← hrun]
  exact ⟨hnoActiveD, huniqueKeep, hleader, hcountD, hfreeD⟩

set_option maxHeartbeats 2000000 in
/-- One integrated outgoing-leader attempt either keeps the designated unique
leader, or regeneration from the resulting leaderless state reaches another
deletion-free unique leader at a strictly smaller global live-bullet count. -/
theorem resetProbeLeaderSink_retryStep_bulletTwo
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (hpsiLe : psi ≤ n) (hndvd : ¬ psi ∣ n)
    (C : EConfig n psi kappa tau) (leader : Fin n)
    (hnoActive : NoActiveDeletion C)
    (hunique : hasUniqueLeader n
      (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig C))
    (hleader : (C leader).core.erase.core.leader = true) :
    let C₁ := localStep ring
      (wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
        hpsi kappa tau) C leader
    (hasUniqueLeader n
        (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig C₁) ∧
      (C₁ leader).core.erase.core.leader = true) ∨
      ∃ (retry : DetSchedule n) (leader' : Fin n),
        let D := runLocalSchedule ring
          (wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
            hpsi kappa tau) C₁ retry
        NoActiveDeletion D ∧
          hasUniqueLeader n
            (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig D) ∧
          (D leader').core.erase.core.leader = true ∧
          PPLLPpsiLeaderCreationRepair.bulletTwoCount D <
            PPLLPpsiLeaderCreationRepair.bulletTwoCount C := by
  let j := ring.rightNeighbor leader
  let Tnew :=
    wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
      hpsi kappa tau
  let Told := wallSweepPreCheckResetLeaderSinkPathStallTransition
    hpsi kappa tau
  let C₁ := localStep ring Tnew C leader
  let C₀ := localStep ring Told C leader
  have hopen : WallPriorityOpen (C leader) (C j) := by
    simpa [j] using
      WallPriorityOpen.of_noActiveDeletion C hnoActive ring leader
  have hpair : Tnew (C leader) (C j) = Told (C leader) (C j) := by
    simpa [Tnew, Told, j] using
      (wallSweepResetProbePreCheckResetLeaderSinkPathStall_eq_of_left_leader
        hpsi kappa tau (C leader) (C j) hleader)
  have hstepEq : C₁ = C₀ :=
    localStep_eq_of_pair_eq ring Tnew Told C leader
      (by simpa [j] using hpair)
  have hnoActiveC₁ : NoActiveDeletion C₁ := by
    simpa only [C₁, Tnew] using
      resetAwareLeader_localStep_noActive
        hpsi ring hn C leader hnoActive hleader
  have hcycle :=
    PPLLPpsiLeaderCreationRepair.localStepLeaderSink_unique_initiator_survives_or_leaderless_rank_lt
      hpsi kappa tau ring hn C leader hunique hleader
        (by simpa [j] using hopen)
  change
    (hasUniqueLeader n
        (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig C₀) ∧
      (C₀ leader).core.erase.core.leader = true) ∨
    (PPLLPpsiLeaderCreationSchedule.RawLeaderless
        (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig C₀) ∧
      PPLLPpsiLeaderCreationRepair.bulletTwoCount C₀ <
        PPLLPpsiLeaderCreationRepair.bulletTwoCount C) at hcycle
  rcases hcycle with hsurvives | hleaderless
  · left
    change hasUniqueLeader n
        (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig C₁) ∧
      (C₁ leader).core.erase.core.leader = true
    rw [hstepEq]
    exact hsurvives
  · have hleaderlessC₁ : PPLLPpsiLeaderCreationSchedule.RawLeaderless
        (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig C₁) := by
      rw [hstepEq]
      exact hleaderless.1
    have hdropC₁ : PPLLPpsiLeaderCreationRepair.bulletTwoCount C₁ <
        PPLLPpsiLeaderCreationRepair.bulletTwoCount C := by
      rw [hstepEq]
      exact hleaderless.2
    obtain ⟨retry, leader', hnoActiveD, huniqueD, hleaderD,
        hcountD, _hfreeD⟩ :=
      exists_resetProbeLeaderSink_drainedUniqueLeader_bulletTwo_le_of_not_dvd
        hpsi ring hn hpsiLe hndvd C₁ hnoActiveC₁ hleaderlessC₁
    exact .inr ⟨retry, leader', hnoActiveD, huniqueD, hleaderD,
      Nat.lt_of_le_of_lt hcountD hdropC₁⟩

set_option maxHeartbeats 2000000 in
/-- With a zero signal at the designated leader, one repaired outgoing attempt
is nonexpansive if the leader survives.  If it dies, regeneration returns a
new zero-signal leader at a strictly smaller live-bullet count. -/
theorem birthSignalZero_retryStep_bulletTwo
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (hpsiLe : psi ≤ n) (hndvd : ¬ psi ∣ n)
    (C : EConfig n psi kappa tau) (leader : Fin n)
    (hnoActive : NoActiveDeletion C)
    (hunique : hasUniqueLeader n
      (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig C))
    (hleader : (C leader).core.erase.core.leader = true)
    (hsignal : (C leader).core.erase.core.signal_B = ⟨0, by omega⟩) :
    let C₁ := localStep ring
      (wallSweepBirthSignalZeroPathStallTransition
        hpsi kappa tau) C leader
    (hasUniqueLeader n
        (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig C₁) ∧
      (C₁ leader).core.erase.core.leader = true ∧
      (C₁ leader).core.erase.core.signal_B = ⟨0, by omega⟩ ∧
      PPLLPpsiLeaderCreationRepair.bulletTwoCount C₁ ≤
        PPLLPpsiLeaderCreationRepair.bulletTwoCount C) ∨
      ∃ (retry : DetSchedule n) (leader' : Fin n),
        let D := runLocalSchedule ring
          (wallSweepBirthSignalZeroPathStallTransition
            hpsi kappa tau) C₁ retry
        NoActiveDeletion D ∧
          hasUniqueLeader n
            (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig D) ∧
          (D leader').core.erase.core.leader = true ∧
          (D leader').core.erase.core.signal_B = ⟨0, by omega⟩ ∧
          PPLLPpsiLeaderCreationRepair.bulletTwoCount D <
            PPLLPpsiLeaderCreationRepair.bulletTwoCount C := by
  let j := ring.rightNeighbor leader
  let Tbirth := wallSweepBirthSignalZeroPathStallTransition
    hpsi kappa tau
  let Treset :=
    wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
      hpsi kappa tau
  let Troot := wallSweepPreCheckResetLeaderSinkPathStallTransition
    hpsi kappa tau
  let C₁ := localStep ring Tbirth C leader
  let Creset := localStep ring Treset C leader
  let C₀ := localStep ring Troot C leader
  have hpairBirth : Tbirth (C leader) (C j) =
      Treset (C leader) (C j) := by
    simpa [Tbirth, Treset, j] using
      wallSweepBirthSignalZeroPathStall_eq_of_left_leader
        hpsi kappa tau (C leader) (C j) hleader
  have hbirthEq : C₁ = Creset :=
    localStep_eq_of_pair_eq ring Tbirth Treset C leader
      (by simpa [j] using hpairBirth)
  have hpairRoot : Treset (C leader) (C j) =
      Troot (C leader) (C j) := by
    simpa [Treset, Troot, j] using
      wallSweepResetProbePreCheckResetLeaderSinkPathStall_eq_of_left_leader
        hpsi kappa tau (C leader) (C j) hleader
  have hresetEq : Creset = C₀ :=
    localStep_eq_of_pair_eq ring Treset Troot C leader
      (by simpa [j] using hpairRoot)
  have hstepEq : C₁ = C₀ := hbirthEq.trans hresetEq
  have hnoActiveCreset : NoActiveDeletion Creset := by
    simpa only [Creset, Treset] using
      resetAwareLeader_localStep_noActive
        hpsi ring hn C leader hnoActive hleader
  have hnoActiveC₁ : NoActiveDeletion C₁ := by
    rw [hbirthEq]
    exact hnoActiveCreset
  have hsignalCreset :
      (Creset leader).core.erase.core.signal_B = ⟨0, by omega⟩ := by
    simpa only [Creset, Treset] using
      resetAwareLeader_localStep_signal_zero
        hpsi ring C leader hnoActive hleader
  have hsignalC₁ :
      (C₁ leader).core.erase.core.signal_B = ⟨0, by omega⟩ := by
    rw [hbirthEq]
    exact hsignalCreset
  have hcountCreset := resetAwareLeader_signalZero_localStep_bulletTwoCount_le
    hpsi ring hn C leader hnoActive hleader hsignal
  change PPLLPpsiLeaderCreationRepair.bulletTwoCount Creset ≤
    PPLLPpsiLeaderCreationRepair.bulletTwoCount C at hcountCreset
  have hcountC₁ : PPLLPpsiLeaderCreationRepair.bulletTwoCount C₁ ≤
      PPLLPpsiLeaderCreationRepair.bulletTwoCount C := by
    rw [hbirthEq]
    exact hcountCreset
  have hopen : WallPriorityOpen (C leader) (C j) := by
    simpa [j] using
      WallPriorityOpen.of_noActiveDeletion C hnoActive ring leader
  have hcycle :=
    PPLLPpsiLeaderCreationRepair.localStepLeaderSink_unique_initiator_survives_or_leaderless_rank_lt
      hpsi kappa tau ring hn C leader hunique hleader
        (by simpa [j] using hopen)
  change
    (hasUniqueLeader n
        (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig C₀) ∧
      (C₀ leader).core.erase.core.leader = true) ∨
    (PPLLPpsiLeaderCreationSchedule.RawLeaderless
        (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig C₀) ∧
      PPLLPpsiLeaderCreationRepair.bulletTwoCount C₀ <
        PPLLPpsiLeaderCreationRepair.bulletTwoCount C) at hcycle
  rcases hcycle with hsurvives | hleaderless
  · left
    have hsurvivesC₁ : hasUniqueLeader n
          (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig C₁) ∧
        (C₁ leader).core.erase.core.leader = true := by
      rw [hstepEq]
      exact hsurvives
    exact ⟨hsurvivesC₁.1, hsurvivesC₁.2, hsignalC₁, hcountC₁⟩
  · have hleaderlessC₁ : PPLLPpsiLeaderCreationSchedule.RawLeaderless
        (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig C₁) := by
      rw [hstepEq]
      exact hleaderless.1
    have hdropC₁ : PPLLPpsiLeaderCreationRepair.bulletTwoCount C₁ <
        PPLLPpsiLeaderCreationRepair.bulletTwoCount C := by
      rw [hstepEq]
      exact hleaderless.2
    obtain ⟨retry, leader', hnoActiveD, huniqueD, hleaderD,
        hsignalD, hcountD, _hfreeD⟩ :=
      exists_birthSignalZero_drainedUniqueLeader_bulletTwo_le_of_not_dvd
        hpsi ring hn hpsiLe hndvd C₁ hnoActiveC₁ hleaderlessC₁
    exact .inr ⟨retry, leader', hnoActiveD, huniqueD, hleaderD,
      hsignalD, Nat.lt_of_le_of_lt hcountD hdropC₁⟩

/-- Terminal boundary of the integrated live-bullet retry: a deletion-free
unique leader whose next outgoing edge preserves that same leader. -/
def ResetProbeDrainedOutgoingLeaderSurvivor
    (hpsi : psi > 0) (ring : DirectedRing n)
    (C : EConfig n psi kappa tau) : Prop :=
  ∃ leader : Fin n,
    NoActiveDeletion C ∧
      hasUniqueLeader n
        (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig C) ∧
      (C leader).core.erase.core.leader = true ∧
      let D := localStep ring
        (wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
          hpsi kappa tau) C leader
      hasUniqueLeader n
          (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig D) ∧
        (D leader).core.erase.core.leader = true

/-- Outgoing-survivor boundary strengthened with the zero signal carried by
the designated leader in the birth-signal repair. -/
def BirthSignalZeroDrainedOutgoingLeaderSurvivor
    (hpsi : psi > 0) (ring : DirectedRing n)
    (C : EConfig n psi kappa tau) : Prop :=
  ∃ leader : Fin n,
    NoActiveDeletion C ∧
      hasUniqueLeader n
        (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig C) ∧
      (C leader).core.erase.core.leader = true ∧
      (C leader).core.erase.core.signal_B = ⟨0, by omega⟩ ∧
      let D := localStep ring
        (wallSweepBirthSignalZeroPathStallTransition
          hpsi kappa tau) C leader
      hasUniqueLeader n
          (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig D) ∧
        (D leader).core.erase.core.leader = true

set_option maxHeartbeats 2000000 in
private theorem
    exists_birthSignalZero_outgoingSurvivor_of_rank
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (hpsiLe : psi ≤ n) (hndvd : ¬ psi ∣ n) (rank : Nat)
    (C : EConfig n psi kappa tau) (leader : Fin n)
    (hnoActive : NoActiveDeletion C)
    (hunique : hasUniqueLeader n
      (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig C))
    (hleader : (C leader).core.erase.core.leader = true)
    (hsignal : (C leader).core.erase.core.signal_B = ⟨0, by omega⟩)
    (hrank : PPLLPpsiLeaderCreationRepair.bulletTwoCount C ≤ rank) :
    ∃ (actual : DetSchedule n) (D : EConfig n psi kappa tau),
      D = runLocalSchedule ring
        (wallSweepBirthSignalZeroPathStallTransition
          hpsi kappa tau) C actual ∧
      BirthSignalZeroDrainedOutgoingLeaderSurvivor hpsi ring D ∧
      PPLLPpsiLeaderCreationRepair.bulletTwoCount D ≤
        PPLLPpsiLeaderCreationRepair.bulletTwoCount C := by
  induction rank using Nat.strongRecOn generalizing C leader with
  | ind rank ih =>
      have hcycle := birthSignalZero_retryStep_bulletTwo
        hpsi ring hn hpsiLe hndvd C leader hnoActive hunique hleader hsignal
      let T := wallSweepBirthSignalZeroPathStallTransition
        hpsi kappa tau
      let C₁ := localStep ring T C leader
      change
        (hasUniqueLeader n
            (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig C₁) ∧
          (C₁ leader).core.erase.core.leader = true ∧
          (C₁ leader).core.erase.core.signal_B = ⟨0, by omega⟩ ∧
          PPLLPpsiLeaderCreationRepair.bulletTwoCount C₁ ≤
            PPLLPpsiLeaderCreationRepair.bulletTwoCount C) ∨
        ∃ (retry : DetSchedule n) (leader' : Fin n),
          let D := runLocalSchedule ring T C₁ retry
          NoActiveDeletion D ∧
            hasUniqueLeader n
              (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig D) ∧
            (D leader').core.erase.core.leader = true ∧
            (D leader').core.erase.core.signal_B = ⟨0, by omega⟩ ∧
            PPLLPpsiLeaderCreationRepair.bulletTwoCount D <
              PPLLPpsiLeaderCreationRepair.bulletTwoCount C at hcycle
      rcases hcycle with hsurvives | hretry
      · exact ⟨[], C, rfl,
          ⟨⟨leader, hnoActive, hunique, hleader, hsignal,
              hsurvives.1, hsurvives.2.1⟩,
            Nat.le_refl _⟩⟩
      · obtain ⟨retry, leader', hnoActiveD, huniqueD, hleaderD,
            hsignalD, hcountD⟩ := hretry
        let D := runLocalSchedule ring T C₁ retry
        change NoActiveDeletion D at hnoActiveD
        change hasUniqueLeader n
          (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig D) at huniqueD
        change (D leader').core.erase.core.leader = true at hleaderD
        change (D leader').core.erase.core.signal_B = ⟨0, by omega⟩ at hsignalD
        change PPLLPpsiLeaderCreationRepair.bulletTwoCount D <
          PPLLPpsiLeaderCreationRepair.bulletTwoCount C at hcountD
        have hlt : PPLLPpsiLeaderCreationRepair.bulletTwoCount D < rank :=
          Nat.lt_of_lt_of_le hcountD hrank
        obtain ⟨tail, E, hE, hterminal, hcountE⟩ :=
          ih (PPLLPpsiLeaderCreationRepair.bulletTwoCount D) hlt
            D leader' hnoActiveD huniqueD hleaderD hsignalD
              (Nat.le_refl _)
        let actual := [leader] ++ retry ++ tail
        refine ⟨actual, E, ?_, hterminal,
          Nat.le_trans hcountE (Nat.le_of_lt hcountD)⟩
        calc
          E = runLocalSchedule ring T D tail := hE
          _ = runLocalSchedule ring T
              (runLocalSchedule ring T C₁ retry) tail := by rfl
          _ = runLocalSchedule ring T C₁ (retry ++ tail) :=
            (runLocalSchedule_append_generic ring T C₁ retry tail).symm
          _ = runLocalSchedule ring T
              (runLocalSchedule ring T C [leader]) (retry ++ tail) := by rfl
          _ = runLocalSchedule ring T C
              ([leader] ++ (retry ++ tail)) :=
            (runLocalSchedule_append_generic
              ring T C [leader] (retry ++ tail)).symm
          _ = runLocalSchedule ring T C actual := by
            simp only [actual, List.append_assoc]

/-- The zero-signal live-bullet rank makes repeated leader death and
regeneration well founded without allowing a one-bullet increase. -/
theorem exists_birthSignalZero_outgoingSurvivor_of_not_dvd
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (hpsiLe : psi ≤ n) (hndvd : ¬ psi ∣ n)
    (C : EConfig n psi kappa tau) (leader : Fin n)
    (hnoActive : NoActiveDeletion C)
    (hunique : hasUniqueLeader n
      (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig C))
    (hleader : (C leader).core.erase.core.leader = true)
    (hsignal : (C leader).core.erase.core.signal_B = ⟨0, by omega⟩) :
    ∃ (actual : DetSchedule n) (D : EConfig n psi kappa tau),
      D = runLocalSchedule ring
        (wallSweepBirthSignalZeroPathStallTransition
          hpsi kappa tau) C actual ∧
      BirthSignalZeroDrainedOutgoingLeaderSurvivor hpsi ring D ∧
      PPLLPpsiLeaderCreationRepair.bulletTwoCount D ≤
        PPLLPpsiLeaderCreationRepair.bulletTwoCount C := by
  exact exists_birthSignalZero_outgoingSurvivor_of_rank
    hpsi ring hn hpsiLe hndvd
      (PPLLPpsiLeaderCreationRepair.bulletTwoCount C)
      C leader hnoActive hunique hleader hsignal (Nat.le_refl _)

/-- First-leader production followed by zero-signal retry reaches an outgoing
survivor from every deletion-free leaderless nondivisible input, with no
increase in live-bullet mass. -/
theorem
    exists_birthSignalZero_outgoingSurvivor_from_leaderless_of_not_dvd
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (hpsiLe : psi ≤ n) (hndvd : ¬ psi ∣ n)
    (C : EConfig n psi kappa tau)
    (hnoActive : NoActiveDeletion C)
    (hleaderless : PPLLPpsiLeaderCreationSchedule.RawLeaderless
      (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig C)) :
    ∃ (actual : DetSchedule n) (D : EConfig n psi kappa tau),
      D = runLocalSchedule ring
        (wallSweepBirthSignalZeroPathStallTransition
          hpsi kappa tau) C actual ∧
      BirthSignalZeroDrainedOutgoingLeaderSurvivor hpsi ring D ∧
      PPLLPpsiLeaderCreationRepair.bulletTwoCount D ≤
        PPLLPpsiLeaderCreationRepair.bulletTwoCount C := by
  obtain ⟨initial, leader, hnoActiveA, huniqueA, hleaderA,
      hsignalA, hcountA, _hfreeA⟩ :=
    exists_birthSignalZero_drainedUniqueLeader_bulletTwo_le_of_not_dvd
      hpsi ring hn hpsiLe hndvd C hnoActive hleaderless
  let T := wallSweepBirthSignalZeroPathStallTransition
    hpsi kappa tau
  let A := runLocalSchedule ring T C initial
  change NoActiveDeletion A at hnoActiveA
  change hasUniqueLeader n
    (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig A) at huniqueA
  change (A leader).core.erase.core.leader = true at hleaderA
  change (A leader).core.erase.core.signal_B = ⟨0, by omega⟩ at hsignalA
  obtain ⟨tail, D, hD, hterminal, hcountD⟩ :=
    exists_birthSignalZero_outgoingSurvivor_of_not_dvd
      hpsi ring hn hpsiLe hndvd A leader hnoActiveA huniqueA hleaderA
        hsignalA
  refine ⟨initial ++ tail, D, ?_, hterminal,
    Nat.le_trans hcountD hcountA⟩
  calc
    D = runLocalSchedule ring T A tail := hD
    _ = runLocalSchedule ring T
        (runLocalSchedule ring T C initial) tail := by rfl
    _ = runLocalSchedule ring T C (initial ++ tail) :=
      (runLocalSchedule_append_generic ring T C initial tail).symm

set_option maxHeartbeats 2000000 in
private theorem
    exists_resetProbeLeaderSink_outgoingSurvivor_of_rank
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (hpsiLe : psi ≤ n) (hndvd : ¬ psi ∣ n) (rank : Nat)
    (C : EConfig n psi kappa tau) (leader : Fin n)
    (hnoActive : NoActiveDeletion C)
    (hunique : hasUniqueLeader n
      (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig C))
    (hleader : (C leader).core.erase.core.leader = true)
    (hrank : PPLLPpsiLeaderCreationRepair.bulletTwoCount C ≤ rank) :
    ∃ (actual : DetSchedule n) (D : EConfig n psi kappa tau),
      D = runLocalSchedule ring
        (wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
          hpsi kappa tau) C actual ∧
      ResetProbeDrainedOutgoingLeaderSurvivor hpsi ring D ∧
      PPLLPpsiLeaderCreationRepair.bulletTwoCount D ≤
        PPLLPpsiLeaderCreationRepair.bulletTwoCount C := by
  induction rank using Nat.strongRecOn generalizing C leader with
  | ind rank ih =>
      have hcycle := resetProbeLeaderSink_retryStep_bulletTwo
        hpsi ring hn hpsiLe hndvd C leader hnoActive hunique hleader
      let T :=
        wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
          hpsi kappa tau
      let C₁ := localStep ring T C leader
      change
        (hasUniqueLeader n
            (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig C₁) ∧
          (C₁ leader).core.erase.core.leader = true) ∨
        ∃ (retry : DetSchedule n) (leader' : Fin n),
          let D := runLocalSchedule ring T C₁ retry
          NoActiveDeletion D ∧
            hasUniqueLeader n
              (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig D) ∧
            (D leader').core.erase.core.leader = true ∧
            PPLLPpsiLeaderCreationRepair.bulletTwoCount D <
              PPLLPpsiLeaderCreationRepair.bulletTwoCount C at hcycle
      rcases hcycle with hsurvives | hretry
      · exact ⟨[], C, rfl,
          ⟨⟨leader, hnoActive, hunique, hleader, hsurvives⟩,
            Nat.le_refl _⟩⟩
      · obtain ⟨retry, leader', hnoActiveD, huniqueD, hleaderD,
            hcountD⟩ := hretry
        let D := runLocalSchedule ring T C₁ retry
        change NoActiveDeletion D at hnoActiveD
        change hasUniqueLeader n
          (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig D) at huniqueD
        change (D leader').core.erase.core.leader = true at hleaderD
        change PPLLPpsiLeaderCreationRepair.bulletTwoCount D <
          PPLLPpsiLeaderCreationRepair.bulletTwoCount C at hcountD
        have hlt : PPLLPpsiLeaderCreationRepair.bulletTwoCount D < rank :=
          Nat.lt_of_lt_of_le hcountD hrank
        obtain ⟨tail, E, hE, hterminal, hcountE⟩ :=
          ih (PPLLPpsiLeaderCreationRepair.bulletTwoCount D) hlt
            D leader' hnoActiveD huniqueD hleaderD (Nat.le_refl _)
        let actual := [leader] ++ retry ++ tail
        refine ⟨actual, E, ?_, hterminal,
          Nat.le_trans hcountE (Nat.le_of_lt hcountD)⟩
        calc
          E = runLocalSchedule ring T D tail := hE
          _ = runLocalSchedule ring T
              (runLocalSchedule ring T C₁ retry) tail := by rfl
          _ = runLocalSchedule ring T C₁ (retry ++ tail) :=
            (runLocalSchedule_append_generic ring T C₁ retry tail).symm
          _ = runLocalSchedule ring T
              (runLocalSchedule ring T C [leader]) (retry ++ tail) := by rfl
          _ = runLocalSchedule ring T C
              ([leader] ++ (retry ++ tail)) :=
            (runLocalSchedule_append_generic
              ring T C [leader] (retry ++ tail)).symm
          _ = runLocalSchedule ring T C actual := by
            simp only [actual, List.append_assoc]

/-- The integrated global live-bullet rank makes repeated leader death and
regeneration well founded. -/
theorem exists_resetProbeLeaderSink_outgoingSurvivor_of_not_dvd
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (hpsiLe : psi ≤ n) (hndvd : ¬ psi ∣ n)
    (C : EConfig n psi kappa tau) (leader : Fin n)
    (hnoActive : NoActiveDeletion C)
    (hunique : hasUniqueLeader n
      (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig C))
    (hleader : (C leader).core.erase.core.leader = true) :
    ∃ (actual : DetSchedule n) (D : EConfig n psi kappa tau),
      D = runLocalSchedule ring
        (wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
          hpsi kappa tau) C actual ∧
      ResetProbeDrainedOutgoingLeaderSurvivor hpsi ring D ∧
      PPLLPpsiLeaderCreationRepair.bulletTwoCount D ≤
        PPLLPpsiLeaderCreationRepair.bulletTwoCount C := by
  exact exists_resetProbeLeaderSink_outgoingSurvivor_of_rank
    hpsi ring hn hpsiLe hndvd
      (PPLLPpsiLeaderCreationRepair.bulletTwoCount C)
      C leader hnoActive hunique hleader (Nat.le_refl _)

/-- Combining integrated first-leader production with the integrated
live-bullet retry reaches an outgoing survivor from every deletion-free
leaderless nondivisible input. -/
theorem
    exists_resetProbeLeaderSink_outgoingSurvivor_from_leaderless_of_not_dvd
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (hpsiLe : psi ≤ n) (hndvd : ¬ psi ∣ n)
    (C : EConfig n psi kappa tau)
    (hnoActive : NoActiveDeletion C)
    (hleaderless : PPLLPpsiLeaderCreationSchedule.RawLeaderless
      (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig C)) :
    ∃ (actual : DetSchedule n) (D : EConfig n psi kappa tau),
      D = runLocalSchedule ring
        (wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
          hpsi kappa tau) C actual ∧
      ResetProbeDrainedOutgoingLeaderSurvivor hpsi ring D ∧
      PPLLPpsiLeaderCreationRepair.bulletTwoCount D ≤
        PPLLPpsiLeaderCreationRepair.bulletTwoCount C := by
  obtain ⟨initial, leader, hnoActiveA, huniqueA, hleaderA,
      hcountA, _hfreeA⟩ :=
    exists_resetProbeLeaderSink_drainedUniqueLeader_bulletTwo_le_of_not_dvd
      hpsi ring hn hpsiLe hndvd C hnoActive hleaderless
  let T :=
    wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
      hpsi kappa tau
  let A := runLocalSchedule ring T C initial
  change NoActiveDeletion A at hnoActiveA
  change hasUniqueLeader n
    (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig A) at huniqueA
  change (A leader).core.erase.core.leader = true at hleaderA
  obtain ⟨tail, D, hD, hterminal, hcountD⟩ :=
    exists_resetProbeLeaderSink_outgoingSurvivor_of_not_dvd
      hpsi ring hn hpsiLe hndvd A leader hnoActiveA huniqueA hleaderA
  refine ⟨initial ++ tail, D, ?_, hterminal,
    Nat.le_trans hcountD hcountA⟩
  calc
    D = runLocalSchedule ring T A tail := hD
    _ = runLocalSchedule ring T
        (runLocalSchedule ring T C initial) tail := by rfl
    _ = runLocalSchedule ring T C (initial ++ tail) :=
      (runLocalSchedule_append_generic ring T C initial tail).symm

set_option maxHeartbeats 3000000 in
/-- The integrated leaderless producer, live-bullet survivor retry, one
surviving normalization edge, and one replay edge compose to the authenticated
reset frontier consumed by the reset-aware sweep.  The named leader signal is
zero at the returned frontier. -/
theorem
    exists_resetProbeLeaderSink_resetFrontier_from_leaderless_of_not_dvd
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (hpsiLe : psi ≤ n) (hndvd : ¬ psi ∣ n)
    (C : EConfig n psi kappa tau)
    (hnoActive : NoActiveDeletion C)
    (hleaderless : PPLLPpsiLeaderCreationSchedule.RawLeaderless
      (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig C)) :
    ∃ (actual : DetSchedule n) (D : EConfig n psi kappa tau)
        (leader : Fin n),
      D = runLocalSchedule ring
        (wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
          hpsi kappa tau) C actual ∧
      PPLLPpsiLeaderCreationRepair.OutgoingResetFrontierUniqueLeaderAt
        hpsi ring D leader ∧
      (D leader).core.erase.core.signal_B = ⟨0, by omega⟩ ∧
      PPLLPpsiLeaderCreationRepair.bulletTwoCount D ≤
        PPLLPpsiLeaderCreationRepair.bulletTwoCount C + 1 := by
  obtain ⟨pref, S, hS, hterminal, hcountS⟩ :=
    exists_resetProbeLeaderSink_outgoingSurvivor_from_leaderless_of_not_dvd
      hpsi ring hn hpsiLe hndvd C hnoActive hleaderless
  obtain ⟨leader, hnoActiveS, huniqueS, hleaderS,
      hnextUnique, hnextLeader⟩ := hterminal
  have huniqueKeep := huniqueS
  let j := ring.rightNeighbor leader
  have hje : j ≠ leader :=
    rightNeighbor_ne_self_of_one_lt ring hn leader
  obtain ⟨only, _honlyLeader, honly⟩ := huniqueS
  have hleaderOnly : leader = only := by
    apply honly leader
    change (S leader).core.erase.core.leader = true
    exact hleaderS
  have hjFollower : (S j).core.erase.core.leader = false := by
    cases hj : (S j).core.erase.core.leader with
    | false => rfl
    | true =>
        have hjOnly : j = only := by
          apply honly j
          change (S j).core.erase.core.leader = true
          exact hj
        exact False.elim (hje (hjOnly.trans hleaderOnly.symm))
  let Tnew :=
    wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
      hpsi kappa tau
  let Told := wallSweepPreCheckResetLeaderSinkPathStallTransition
    hpsi kappa tau
  let Nnew := localStep ring Tnew S leader
  let Nold := localStep ring Told S leader
  have hpairN : Tnew (S leader) (S j) = Told (S leader) (S j) := by
    simpa [Tnew, Told, j] using
      (wallSweepResetProbePreCheckResetLeaderSinkPathStall_eq_of_left_leader
        hpsi kappa tau (S leader) (S j) hleaderS)
  have hN : Nnew = Nold :=
    localStep_eq_of_pair_eq ring Tnew Told S leader
      (by simpa [j] using hpairN)
  change hasUniqueLeader n
    (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig Nnew) at hnextUnique
  change (Nnew leader).core.erase.core.leader = true at hnextLeader
  have hnextUniqueOld : hasUniqueLeader n
      (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig Nold) := by
    rw [← hN]
    exact hnextUnique
  have hnextLeaderOld :
      (Nold leader).core.erase.core.leader = true := by
    rw [← hN]
    exact hnextLeader
  have hnormalOld :=
    PPLLPpsiLeaderCreationRepair.leaderStep_survivor_to_normalizedOutgoingUniqueLeaderAt
      hpsi ring hn S leader hnoActiveS huniqueKeep hleaderS
        (by simpa [j] using hjFollower)
        (by simpa only [Nold, Told] using hnextLeaderOld)
  change PPLLPpsiLeaderCreationRepair.NormalizedOutgoingUniqueLeaderAt
    hpsi ring Nold leader at hnormalOld
  have hnormalNew :
      PPLLPpsiLeaderCreationRepair.NormalizedOutgoingUniqueLeaderAt
        hpsi ring Nnew leader := by
    rw [hN]
    exact hnormalOld
  have hcountN := resetAwareLeader_localStep_bulletTwoCount_le_add_one
    hpsi ring hn S leader hnoActiveS hleaderS
  change PPLLPpsiLeaderCreationRepair.bulletTwoCount Nnew ≤
    PPLLPpsiLeaderCreationRepair.bulletTwoCount S + 1 at hcountN
  have hleaderN : (Nnew leader).core.erase.core.leader = true :=
    hnormalNew.2.2.1
  have hsignalN : (Nnew leader).core.erase.core.signal_B =
      ⟨0, by omega⟩ := by
    simpa only [Nnew, Tnew] using
      resetAwareLeader_localStep_signal_zero
        hpsi ring S leader hnoActiveS hleaderS
  let Fnew := localStep ring Tnew Nnew leader
  let Fold := localStep ring Told Nnew leader
  have hpairF : Tnew (Nnew leader) (Nnew j) =
      Told (Nnew leader) (Nnew j) := by
    simpa [Tnew, Told, j] using
      (wallSweepResetProbePreCheckResetLeaderSinkPathStall_eq_of_left_leader
        hpsi kappa tau (Nnew leader) (Nnew j) hleaderN)
  have hF : Fnew = Fold :=
    localStep_eq_of_pair_eq ring Tnew Told Nnew leader
      (by simpa [j] using hpairF)
  have hfrontierOld :=
    PPLLPpsiLeaderCreationRepair.normalizedOutgoingUniqueLeaderAt_replay_reset_handoff
      hpsi ring hn Nnew leader hnormalNew
  change PPLLPpsiLeaderCreationRepair.OutgoingResetFrontierUniqueLeaderAt
    hpsi ring Fold leader at hfrontierOld
  have hfrontierNew :
      PPLLPpsiLeaderCreationRepair.OutgoingResetFrontierUniqueLeaderAt
        hpsi ring Fnew leader := by
    rw [hF]
    exact hfrontierOld
  have hsignalF : (Fnew leader).core.erase.core.signal_B =
      ⟨0, by omega⟩ := by
    simpa only [Fnew, Tnew] using
      resetAwareLeader_localStep_signal_zero
        hpsi ring Nnew leader hnormalNew.1 hleaderN
  have hcountF := resetAwareLeader_signalZero_localStep_bulletTwoCount_le
    hpsi ring hn Nnew leader hnormalNew.1 hleaderN hsignalN
  change PPLLPpsiLeaderCreationRepair.bulletTwoCount Fnew ≤
    PPLLPpsiLeaderCreationRepair.bulletTwoCount Nnew at hcountF
  have hcountFrontier :
      PPLLPpsiLeaderCreationRepair.bulletTwoCount Fnew ≤
        PPLLPpsiLeaderCreationRepair.bulletTwoCount C + 1 := by
    omega
  let actual := pref ++ [leader, leader]
  have hrun : Fnew = runLocalSchedule ring Tnew C actual := by
    calc
      Fnew = runLocalSchedule ring Tnew S [leader, leader] := rfl
      _ = runLocalSchedule ring Tnew
          (runLocalSchedule ring Tnew C pref) [leader, leader] := by rw [← hS]
      _ = runLocalSchedule ring Tnew C (pref ++ [leader, leader]) :=
        (runLocalSchedule_append_generic
          ring Tnew C pref [leader, leader]).symm
      _ = runLocalSchedule ring Tnew C actual := by rfl
  exact ⟨actual, Fnew, leader, hrun, hfrontierNew, hsignalF,
    hcountFrontier⟩

set_option maxHeartbeats 3000000 in
/-- The birth-signal repair removes the former one-bullet slack: first-leader
production, survivor retry, normalization, and replay reach the authenticated
reset frontier with live-bullet mass no larger than the leaderless input. -/
theorem
    exists_birthSignalZero_resetFrontier_from_leaderless_of_not_dvd
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (hpsiLe : psi ≤ n) (hndvd : ¬ psi ∣ n)
    (C : EConfig n psi kappa tau)
    (hnoActive : NoActiveDeletion C)
    (hleaderless : PPLLPpsiLeaderCreationSchedule.RawLeaderless
      (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig C)) :
    ∃ (actual : DetSchedule n) (D : EConfig n psi kappa tau)
        (leader : Fin n),
      D = runLocalSchedule ring
        (wallSweepBirthSignalZeroPathStallTransition
          hpsi kappa tau) C actual ∧
      PPLLPpsiLeaderCreationRepair.OutgoingResetFrontierUniqueLeaderAt
        hpsi ring D leader ∧
      (D leader).core.erase.core.signal_B = ⟨0, by omega⟩ ∧
      PPLLPpsiLeaderCreationRepair.bulletTwoCount D ≤
        PPLLPpsiLeaderCreationRepair.bulletTwoCount C := by
  obtain ⟨pref, S, hS, hterminal, hcountS⟩ :=
    exists_birthSignalZero_outgoingSurvivor_from_leaderless_of_not_dvd
      hpsi ring hn hpsiLe hndvd C hnoActive hleaderless
  obtain ⟨leader, hnoActiveS, huniqueS, hleaderS, hsignalS,
      hnextUnique, hnextLeader⟩ := hterminal
  have huniqueKeep := huniqueS
  let j := ring.rightNeighbor leader
  have hje : j ≠ leader :=
    rightNeighbor_ne_self_of_one_lt ring hn leader
  obtain ⟨only, _honlyLeader, honly⟩ := huniqueS
  have hleaderOnly : leader = only := by
    apply honly leader
    change (S leader).core.erase.core.leader = true
    exact hleaderS
  have hjFollower : (S j).core.erase.core.leader = false := by
    cases hj : (S j).core.erase.core.leader with
    | false => rfl
    | true =>
        have hjOnly : j = only := by
          apply honly j
          change (S j).core.erase.core.leader = true
          exact hj
        exact False.elim (hje (hjOnly.trans hleaderOnly.symm))
  let Tbirth := wallSweepBirthSignalZeroPathStallTransition
    hpsi kappa tau
  let Treset :=
    wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
      hpsi kappa tau
  let Troot := wallSweepPreCheckResetLeaderSinkPathStallTransition
    hpsi kappa tau
  let Nnew := localStep ring Tbirth S leader
  let Nreset := localStep ring Treset S leader
  let Nold := localStep ring Troot S leader
  have hpairNB : Tbirth (S leader) (S j) = Treset (S leader) (S j) := by
    simpa [Tbirth, Treset, j] using
      wallSweepBirthSignalZeroPathStall_eq_of_left_leader
        hpsi kappa tau (S leader) (S j) hleaderS
  have hNB : Nnew = Nreset :=
    localStep_eq_of_pair_eq ring Tbirth Treset S leader
      (by simpa [j] using hpairNB)
  have hpairNR : Treset (S leader) (S j) = Troot (S leader) (S j) := by
    simpa [Treset, Troot, j] using
      wallSweepResetProbePreCheckResetLeaderSinkPathStall_eq_of_left_leader
        hpsi kappa tau (S leader) (S j) hleaderS
  have hNR : Nreset = Nold :=
    localStep_eq_of_pair_eq ring Treset Troot S leader
      (by simpa [j] using hpairNR)
  have hN : Nnew = Nold := hNB.trans hNR
  change hasUniqueLeader n
    (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig Nnew) at hnextUnique
  change (Nnew leader).core.erase.core.leader = true at hnextLeader
  have hnextUniqueOld : hasUniqueLeader n
      (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig Nold) := by
    rw [← hN]
    exact hnextUnique
  have hnextLeaderOld : (Nold leader).core.erase.core.leader = true := by
    rw [← hN]
    exact hnextLeader
  have hnormalOld :=
    PPLLPpsiLeaderCreationRepair.leaderStep_survivor_to_normalizedOutgoingUniqueLeaderAt
      hpsi ring hn S leader hnoActiveS huniqueKeep hleaderS
        (by simpa [j] using hjFollower)
        (by simpa only [Nold, Troot] using hnextLeaderOld)
  change PPLLPpsiLeaderCreationRepair.NormalizedOutgoingUniqueLeaderAt
    hpsi ring Nold leader at hnormalOld
  have hnormalNew :
      PPLLPpsiLeaderCreationRepair.NormalizedOutgoingUniqueLeaderAt
        hpsi ring Nnew leader := by
    rw [hN]
    exact hnormalOld
  have hcountNreset := resetAwareLeader_signalZero_localStep_bulletTwoCount_le
    hpsi ring hn S leader hnoActiveS hleaderS hsignalS
  change PPLLPpsiLeaderCreationRepair.bulletTwoCount Nreset ≤
    PPLLPpsiLeaderCreationRepair.bulletTwoCount S at hcountNreset
  have hcountN : PPLLPpsiLeaderCreationRepair.bulletTwoCount Nnew ≤
      PPLLPpsiLeaderCreationRepair.bulletTwoCount S := by
    rw [hNB]
    exact hcountNreset
  have hleaderN : (Nnew leader).core.erase.core.leader = true :=
    hnormalNew.2.2.1
  have hsignalNreset : (Nreset leader).core.erase.core.signal_B =
      ⟨0, by omega⟩ := by
    simpa only [Nreset, Treset] using
      resetAwareLeader_localStep_signal_zero
        hpsi ring S leader hnoActiveS hleaderS
  have hsignalN : (Nnew leader).core.erase.core.signal_B =
      ⟨0, by omega⟩ := by
    rw [hNB]
    exact hsignalNreset
  let Fnew := localStep ring Tbirth Nnew leader
  let Freset := localStep ring Treset Nnew leader
  let Fold := localStep ring Troot Nnew leader
  have hpairFB : Tbirth (Nnew leader) (Nnew j) =
      Treset (Nnew leader) (Nnew j) := by
    simpa [Tbirth, Treset, j] using
      wallSweepBirthSignalZeroPathStall_eq_of_left_leader
        hpsi kappa tau (Nnew leader) (Nnew j) hleaderN
  have hFB : Fnew = Freset :=
    localStep_eq_of_pair_eq ring Tbirth Treset Nnew leader
      (by simpa [j] using hpairFB)
  have hpairFR : Treset (Nnew leader) (Nnew j) =
      Troot (Nnew leader) (Nnew j) := by
    simpa [Treset, Troot, j] using
      wallSweepResetProbePreCheckResetLeaderSinkPathStall_eq_of_left_leader
        hpsi kappa tau (Nnew leader) (Nnew j) hleaderN
  have hFR : Freset = Fold :=
    localStep_eq_of_pair_eq ring Treset Troot Nnew leader
      (by simpa [j] using hpairFR)
  have hF : Fnew = Fold := hFB.trans hFR
  have hfrontierOld :=
    PPLLPpsiLeaderCreationRepair.normalizedOutgoingUniqueLeaderAt_replay_reset_handoff
      hpsi ring hn Nnew leader hnormalNew
  change PPLLPpsiLeaderCreationRepair.OutgoingResetFrontierUniqueLeaderAt
    hpsi ring Fold leader at hfrontierOld
  have hfrontierNew :
      PPLLPpsiLeaderCreationRepair.OutgoingResetFrontierUniqueLeaderAt
        hpsi ring Fnew leader := by
    rw [hF]
    exact hfrontierOld
  have hsignalFreset : (Freset leader).core.erase.core.signal_B =
      ⟨0, by omega⟩ := by
    simpa only [Freset, Treset] using
      resetAwareLeader_localStep_signal_zero
        hpsi ring Nnew leader hnormalNew.1 hleaderN
  have hsignalF : (Fnew leader).core.erase.core.signal_B =
      ⟨0, by omega⟩ := by
    rw [hFB]
    exact hsignalFreset
  have hcountFreset := resetAwareLeader_signalZero_localStep_bulletTwoCount_le
    hpsi ring hn Nnew leader hnormalNew.1 hleaderN hsignalN
  change PPLLPpsiLeaderCreationRepair.bulletTwoCount Freset ≤
    PPLLPpsiLeaderCreationRepair.bulletTwoCount Nnew at hcountFreset
  have hcountF : PPLLPpsiLeaderCreationRepair.bulletTwoCount Fnew ≤
      PPLLPpsiLeaderCreationRepair.bulletTwoCount Nnew := by
    rw [hFB]
    exact hcountFreset
  have hcountFrontier :
      PPLLPpsiLeaderCreationRepair.bulletTwoCount Fnew ≤
        PPLLPpsiLeaderCreationRepair.bulletTwoCount C :=
    Nat.le_trans hcountF (Nat.le_trans hcountN hcountS)
  let actual := pref ++ [leader, leader]
  have hrun : Fnew = runLocalSchedule ring Tbirth C actual := by
    calc
      Fnew = runLocalSchedule ring Tbirth S [leader, leader] := rfl
      _ = runLocalSchedule ring Tbirth
          (runLocalSchedule ring Tbirth C pref) [leader, leader] := by rw [← hS]
      _ = runLocalSchedule ring Tbirth C (pref ++ [leader, leader]) :=
        (runLocalSchedule_append_generic
          ring Tbirth C pref [leader, leader]).symm
      _ = runLocalSchedule ring Tbirth C actual := by rfl
  exact ⟨actual, Fnew, leader, hrun, hfrontierNew, hsignalF,
    hcountFrontier⟩

set_option maxHeartbeats 1000000 in
/-- One priority-open edge whose responder is the unique nonzero-label leader
reroots that leader at the initiator.  The step preserves deletion inactivity
and every physical label, and live-bullet freedom is renamed from the old root
to the new one. -/
theorem reverseMigration_localStep_reroot
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (C : EConfig n psi kappa tau) (e : Fin n)
    (hnoActive : NoActiveDeletion C)
    (hunique : hasUniqueLeader n
      (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig C))
    (hrLeader :
      (C (ring.rightNeighbor e)).core.erase.core.leader = true)
    (hrNonzero :
      (C (ring.rightNeighbor e)).core.erase.core.label ≠ ⟨0, hpsi⟩)
    (hfree :
      PPLLPpsiLeaderCreationRepair.BulletTwoFreeAwayFrom
        C (ring.rightNeighbor e)) :
    let T :=
      wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
        hpsi kappa tau
    let D := localStep ring T C e
    NoActiveDeletion D ∧
      hasUniqueLeader n
        (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig D) ∧
      (D e).core.erase.core.leader = true ∧
      PPLLPpsiLeaderCreationRepair.BulletTwoFreeAwayFrom D e ∧
      ∀ i, (D i).core.erase.core.label =
        (C i).core.erase.core.label := by
  let j := ring.rightNeighbor e
  have hje : j ≠ e := rightNeighbor_ne_self_of_one_lt ring hn e
  let T :=
    wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
      hpsi kappa tau
  let q := T (C e) (C j)
  let D := localStep ring T C e
  have hrLeaderJ : (C j).core.erase.core.leader = true := by
    simpa [j] using hrLeader
  have hrNonzeroJ :
      (C j).core.erase.core.label ≠ ⟨0, hpsi⟩ := by
    simpa [j] using hrNonzero
  have hfreeJ :
      PPLLPpsiLeaderCreationRepair.BulletTwoFreeAwayFrom C j := by
    simpa [j] using hfree
  obtain ⟨root, _hroot, honly⟩ := hunique
  have hjUnique : j = root := by
    apply honly j
    change (C j).core.erase.core.leader = true
    exact hrLeaderJ
  have hotherFollower : ∀ i, i ≠ j →
      (C i).core.erase.core.leader = false := by
    intro i hij
    cases hi : (C i).core.erase.core.leader with
    | false => rfl
    | true =>
        have hiUnique : i = root := by
          apply honly i
          change (C i).core.erase.core.leader = true
          exact hi
        exact (hij (hiUnique.trans hjUnique.symm)).elim
  have hlFollower : (C e).core.erase.core.leader = false :=
    hotherFollower e (Ne.symm hje)
  have hopen : WallPriorityOpen (C e) (C j) := by
    simpa [j] using
      WallPriorityOpen.of_noActiveDeletion C hnoActive ring e
  have hpair :=
    wallSweepResetProbePreCheckResetLeaderSinkPathStall_priority_open_nonzero_responder_migration_frame
      hpsi (C e) (C j) hopen hlFollower hrLeaderJ hrNonzeroJ
  change q.1.core.erase.core.leader = true ∧
      q.2.core.erase.core.leader = false ∧
      q.1.core.erase.core.label = (C e).core.erase.core.label ∧
      q.2.core.erase.core.label = (C j).core.erase.core.label ∧
      ComparisonNeutral q.1.core.erase.core ∧
      ComparisonNeutral q.2.core.erase.core ∧
      q.2.core.erase.core.bullet ≠ ⟨2, by omega⟩ at hpair
  obtain ⟨hleftLeader, hrightFollower, hleftLabel, hrightLabel,
      hleftNeutral, hrightNeutral, hrightFree⟩ := hpair
  have hleft : D e = q.1 := by
    simp [D, q, T, localStep, j]
  have hright : D j = q.2 := by
    simp [D, q, T, localStep, j, hje]
  have hoff : ∀ i, i ≠ e → i ≠ j → D i = C i := by
    intro i hie hij
    simp [D, T, localStep, j, hie, hij]
  have hnoActiveD : NoActiveDeletion D := by
    intro i
    by_cases hie : i = e
    · subst i
      rw [hleft]
      exact deletionActive_false_of_neutral q.1 hleftNeutral
    · by_cases hij : i = j
      · subst i
        rw [hright]
        exact deletionActive_false_of_neutral q.2 hrightNeutral
      · rw [hoff i hie hij]
        exact hnoActive i
  have huniqueD : hasUniqueLeader n
      (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig D) := by
    refine ⟨e, ?_, ?_⟩
    · change (D e).core.erase.core.leader = true
      rw [hleft]
      exact hleftLeader
    · intro i hi
      by_cases hie : i = e
      · exact hie
      · have hiFollower : (D i).core.erase.core.leader = false := by
          by_cases hij : i = j
          · subst i
            rw [hright]
            exact hrightFollower
          · rw [hoff i hie hij]
            exact hotherFollower i hij
        change (D i).core.erase.core.leader = true at hi
        rw [hiFollower] at hi
        contradiction
  have hfreeD :
      PPLLPpsiLeaderCreationRepair.BulletTwoFreeAwayFrom D e := by
    intro i hie
    by_cases hij : i = j
    · subst i
      rw [hright]
      exact hrightFree
    · rw [hoff i hie hij]
      exact hfreeJ i hij
  have hlabels : ∀ i, (D i).core.erase.core.label =
      (C i).core.erase.core.label := by
    intro i
    by_cases hie : i = e
    · subst i
      rw [hleft]
      exact hleftLabel
    · by_cases hij : i = j
      · subst i
        rw [hright]
        exact hrightLabel
      · rw [hoff i hie hij]
  change NoActiveDeletion D ∧
    hasUniqueLeader n
      (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig D) ∧
    (D e).core.erase.core.leader = true ∧
    PPLLPpsiLeaderCreationRepair.BulletTwoFreeAwayFrom D e ∧
    ∀ i, (D i).core.erase.core.label =
      (C i).core.erase.core.label
  exact ⟨hnoActiveD, huniqueD, by rw [hleft]; exact hleftLeader,
    hfreeD, hlabels⟩

/-- Structural output of one unrestricted reverse-migration edge. -/
structure ReverseMigrationLocalFrame
    (ring : DirectedRing n) (C D : EConfig n psi kappa tau)
    (e : Fin n) : Prop where
  no_active : NoActiveDeletion D
  unique_leader : hasUniqueLeader n
    (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig D)
  new_root_alive : (D e).core.erase.core.leader = true
  old_root_follower :
    (D (ring.rightNeighbor e)).core.erase.core.leader = false
  old_root_not_live :
    (D (ring.rightNeighbor e)).core.erase.core.bullet ≠ ⟨2, by omega⟩
  labels_eq : ∀ i, (D i).core.erase.core.label =
    (C i).core.erase.core.label

set_option maxHeartbeats 2000000 in
/-- Reverse migration without the unrelated global live-bullet-freedom
premise.  The vacated root is a non-live follower, all labels are framed, and
deletion inactivity and unique leadership are preserved. -/
theorem reverseMigration_localStep_reroot_unrestricted
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (C : EConfig n psi kappa tau) (e : Fin n)
    (hnoActive : NoActiveDeletion C)
    (hunique : hasUniqueLeader n
      (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig C))
    (hrLeader :
      (C (ring.rightNeighbor e)).core.erase.core.leader = true)
    (hrNonzero :
      (C (ring.rightNeighbor e)).core.erase.core.label ≠ ⟨0, hpsi⟩) :
    let T :=
      wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
        hpsi kappa tau
    let D := localStep ring T C e
    ReverseMigrationLocalFrame ring C D e := by
  let j := ring.rightNeighbor e
  have hje : j ≠ e := rightNeighbor_ne_self_of_one_lt ring hn e
  let T :=
    wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
      hpsi kappa tau
  let q := T (C e) (C j)
  let D := localStep ring T C e
  have hrLeaderJ : (C j).core.erase.core.leader = true := by
    simpa [j] using hrLeader
  have hrNonzeroJ :
      (C j).core.erase.core.label ≠ ⟨0, hpsi⟩ := by
    simpa [j] using hrNonzero
  obtain ⟨root, _hroot, honly⟩ := hunique
  have hjUnique : j = root := by
    apply honly j
    change (C j).core.erase.core.leader = true
    exact hrLeaderJ
  have hotherFollower : ∀ i, i ≠ j →
      (C i).core.erase.core.leader = false := by
    intro i hij
    cases hi : (C i).core.erase.core.leader with
    | false => rfl
    | true =>
        have hiUnique : i = root := by
          apply honly i
          change (C i).core.erase.core.leader = true
          exact hi
        exact (hij (hiUnique.trans hjUnique.symm)).elim
  have hlFollower : (C e).core.erase.core.leader = false :=
    hotherFollower e (Ne.symm hje)
  have hopen : WallPriorityOpen (C e) (C j) := by
    simpa [j] using
      WallPriorityOpen.of_noActiveDeletion C hnoActive ring e
  have hpair :=
    wallSweepResetProbePreCheckResetLeaderSinkPathStall_priority_open_nonzero_responder_migration_frame
      hpsi (C e) (C j) hopen hlFollower hrLeaderJ hrNonzeroJ
  change q.1.core.erase.core.leader = true ∧
      q.2.core.erase.core.leader = false ∧
      q.1.core.erase.core.label = (C e).core.erase.core.label ∧
      q.2.core.erase.core.label = (C j).core.erase.core.label ∧
      ComparisonNeutral q.1.core.erase.core ∧
      ComparisonNeutral q.2.core.erase.core ∧
      q.2.core.erase.core.bullet ≠ ⟨2, by omega⟩ at hpair
  obtain ⟨hleftLeader, hrightFollower, hleftLabel, hrightLabel,
      hleftNeutral, hrightNeutral, hrightFree⟩ := hpair
  have hleft : D e = q.1 := by
    simp [D, q, T, localStep, j]
  have hright : D j = q.2 := by
    simp [D, q, T, localStep, j, hje]
  have hoff : ∀ i, i ≠ e → i ≠ j → D i = C i := by
    intro i hie hij
    simp [D, T, localStep, j, hie, hij]
  have hnoActiveD : NoActiveDeletion D := by
    intro i
    by_cases hie : i = e
    · subst i
      rw [hleft]
      exact deletionActive_false_of_neutral q.1 hleftNeutral
    · by_cases hij : i = j
      · subst i
        rw [hright]
        exact deletionActive_false_of_neutral q.2 hrightNeutral
      · rw [hoff i hie hij]
        exact hnoActive i
  have huniqueD : hasUniqueLeader n
      (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig D) := by
    refine ⟨e, ?_, ?_⟩
    · change (D e).core.erase.core.leader = true
      rw [hleft]
      exact hleftLeader
    · intro i hi
      by_cases hie : i = e
      · exact hie
      · have hiFollower : (D i).core.erase.core.leader = false := by
          by_cases hij : i = j
          · subst i
            rw [hright]
            exact hrightFollower
          · rw [hoff i hie hij]
            exact hotherFollower i hij
        change (D i).core.erase.core.leader = true at hi
        rw [hiFollower] at hi
        contradiction
  have hlabels : ∀ i, (D i).core.erase.core.label =
      (C i).core.erase.core.label := by
    intro i
    by_cases hie : i = e
    · subst i
      rw [hleft]
      exact hleftLabel
    · by_cases hij : i = j
      · subst i
        rw [hright]
        exact hrightLabel
      · rw [hoff i hie hij]
  change ReverseMigrationLocalFrame ring C D e
  exact {
    no_active := hnoActiveD
    unique_leader := huniqueD
    new_root_alive := by rw [hleft]; exact hleftLeader
    old_root_follower := by rw [hright]; exact hrightFollower
    old_root_not_live := by rw [hright]; exact hrightFree
    labels_eq := hlabels }

set_option maxHeartbeats 1000000 in
/-- The follower-initiated reverse-migration edge cannot increase global
live-bullet mass.  This rank projection is independent of the structural
reroot proof above. -/
theorem reverseMigration_localStep_bulletTwoCount_le
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (C : EConfig n psi kappa tau) (e : Fin n)
    (hnoActive : NoActiveDeletion C)
    (hunique : hasUniqueLeader n
      (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig C))
    (hrLeader :
      (C (ring.rightNeighbor e)).core.erase.core.leader = true) :
    let T :=
      wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
        hpsi kappa tau
    let D := localStep ring T C e
    PPLLPpsiLeaderCreationRepair.bulletTwoCount D ≤
      PPLLPpsiLeaderCreationRepair.bulletTwoCount C := by
  let j := ring.rightNeighbor e
  have hje : j ≠ e := rightNeighbor_ne_self_of_one_lt ring hn e
  let T :=
    wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
      hpsi kappa tau
  let Troot := wallSweepPreCheckResetLeaderSinkPathStallTransition
    hpsi kappa tau
  let q := T (C e) (C j)
  let D := localStep ring T C e
  obtain ⟨root, _hroot, honly⟩ := hunique
  have hjUnique : j = root := by
    apply honly j
    change (C j).core.erase.core.leader = true
    simpa [j] using hrLeader
  have hlFollower : (C e).core.erase.core.leader = false := by
    cases hi : (C e).core.erase.core.leader with
    | false => rfl
    | true =>
        have heUnique : e = root := by
          apply honly e
          change (C e).core.erase.core.leader = true
          exact hi
        exact (hje (hjUnique.trans heUnique.symm)).elim
  have hopen : WallPriorityOpen (C e) (C j) := by
    simpa [j] using
      WallPriorityOpen.of_noActiveDeletion C hnoActive ring e
  have hlocal :=
    wallSweepPreCheckResetLeaderSinkPathStall_priority_open_left_follower_bulletTwoPair
      hpsi (C e) (C j) hopen hlFollower
  have hpairEq : q = Troot (C e) (C j) := by
    simpa [q, T, Troot, j] using
      (wallSweepResetProbePreCheckResetLeaderSinkPathStall_eq_of_right_leader
        hpsi kappa tau (C e) (C j) (by simpa [j] using hrLeader))
  have hlocalLe :
      bulletTwoPairMass
          (Troot (C e) (C j)).1.core.erase.core
          (Troot (C e) (C j)).2.core.erase.core ≤
        bulletTwoPairMass (C e).core.erase.core (C j).core.erase.core :=
    hlocal.le
  have hlocalQ :
      bulletTwoPairMass q.1.core.erase.core q.2.core.erase.core ≤
        bulletTwoPairMass (C e).core.erase.core (C j).core.erase.core := by
    rw [hpairEq]
    exact hlocalLe
  have hleft : D e = q.1 := by
    simp [D, q, T, localStep, j]
  have hright : D j = q.2 := by
    simp [D, q, T, localStep, j, hje]
  change PPLLPpsiLeaderCreationRepair.bulletTwoCount D ≤
    PPLLPpsiLeaderCreationRepair.bulletTwoCount C
  unfold PPLLPpsiLeaderCreationRepair.bulletTwoCount
  apply PPLLPpsiLeaderCreationRepair.sum_ofFn_le_of_pair_le
    (fun i => bulletTwoMass (D i).core.erase.core)
    (fun i => bulletTwoMass (C i).core.erase.core)
    e j (Ne.symm hje)
  · simpa [hleft, hright, bulletTwoPairMass] using hlocalQ
  · intro i hie hij
    simp [D, T, localStep, j, hie, hij]

/-- Global invariant for the counterclockwise reverse-migration prefix.  After
`steps` interactions, the unique leader is at offset `n - steps`; the initial
physical labels remain an immutable reference for deciding whether the next
root is nonzero. -/
structure ReverseMigrationState
    (ring : DirectedRing n) (root : Fin n)
    (base current : EConfig n psi kappa tau) (steps : Nat) : Prop where
  steps_le : steps ≤ n
  no_active : NoActiveDeletion current
  unique_leader : hasUniqueLeader n
    (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig current)
  root_alive :
    (current (groupOffset ring root (n - steps))).core.erase.core.leader = true
  bullet_two_free :
    PPLLPpsiLeaderCreationRepair.BulletTwoFreeAwayFrom current
      (groupOffset ring root (n - steps))
  labels_eq : ∀ i, (current i).core.erase.core.label =
    (base i).core.erase.core.label

/-- The named initial leader is the zero-length reverse-migration state. -/
theorem reverseMigrationState_zero
    (ring : DirectedRing n) (root : Fin n)
    (C : EConfig n psi kappa tau)
    (hnoActive : NoActiveDeletion C)
    (hunique : hasUniqueLeader n
      (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig C))
    (hroot : (C root).core.erase.core.leader = true)
    (hfree : PPLLPpsiLeaderCreationRepair.BulletTwoFreeAwayFrom C root) :
    ReverseMigrationState ring root C C 0 := by
  refine ⟨by omega, hnoActive, hunique, ?_, ?_, fun _ => rfl⟩
  · simpa using hroot
  · simpa using hfree

set_option maxHeartbeats 1000000 in
/-- One more counterclockwise chase edge advances the reverse-migration
invariant whenever the current root's immutable base label is nonzero. -/
theorem ReverseMigrationState.step_of_root_nonzero
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (root : Fin n) (base current : EConfig n psi kappa tau)
    (steps : Nat)
    (hstate : ReverseMigrationState ring root base current steps)
    (hsteps : steps < n)
    (hnonzero :
      (base (groupOffset ring root (n - steps))).core.erase.core.label ≠
        ⟨0, hpsi⟩) :
    let e := groupOffset ring root (n - 1 - steps)
    let D := localStep ring
      (wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
        hpsi kappa tau) current e
    ReverseMigrationState ring root base D (steps + 1) := by
  let e := groupOffset ring root (n - 1 - steps)
  let T := wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
    hpsi kappa tau
  let D := localStep ring T current e
  have hindex : n - 1 - steps + 1 = n - steps := by omega
  have hneighbor : ring.rightNeighbor e =
      groupOffset ring root (n - steps) := by
    rw [show e = groupOffset ring root (n - 1 - steps) by rfl,
      rightNeighbor_groupOffset, hindex]
  have hrLeader :
      (current (ring.rightNeighbor e)).core.erase.core.leader = true := by
    rw [hneighbor]
    exact hstate.root_alive
  have hrNonzero :
      (current (ring.rightNeighbor e)).core.erase.core.label ≠
        ⟨0, hpsi⟩ := by
    rw [hneighbor]
    intro hzero
    exact hnonzero ((hstate.labels_eq _).symm.trans hzero)
  have hfree :
      PPLLPpsiLeaderCreationRepair.BulletTwoFreeAwayFrom current
        (ring.rightNeighbor e) := by
    rw [hneighbor]
    exact hstate.bullet_two_free
  have hstep := reverseMigration_localStep_reroot
    hpsi ring hn current e hstate.no_active hstate.unique_leader
      hrLeader hrNonzero hfree
  change NoActiveDeletion D ∧
      hasUniqueLeader n
        (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig D) ∧
      (D e).core.erase.core.leader = true ∧
      PPLLPpsiLeaderCreationRepair.BulletTwoFreeAwayFrom D e ∧
      ∀ i, (D i).core.erase.core.label =
        (current i).core.erase.core.label at hstep
  obtain ⟨hnoActiveD, huniqueD, hrootD, hfreeD, hlabelsD⟩ := hstep
  refine ⟨by omega, hnoActiveD, huniqueD, ?_, ?_, ?_⟩
  · simpa [e, show n - (steps + 1) = n - 1 - steps by omega] using hrootD
  · simpa [e, show n - (steps + 1) = n - 1 - steps by omega] using hfreeD
  · intro i
    exact (hlabelsD i).trans (hstate.labels_eq i)

set_option maxHeartbeats 1000000 in
/-- The standard counterclockwise chase word composes the local reroot theorem.
The premise mentions exactly the successive roots inspected by the prefix; it
does not require every label on the ring to be nonzero. -/
theorem pPsiProbeChasePrefix_reverseMigrationState
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (root : Fin n) (C : EConfig n psi kappa tau)
    (steps : Nat) (hsteps : steps ≤ n)
    (hnoActive : NoActiveDeletion C)
    (hunique : hasUniqueLeader n
      (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig C))
    (hroot : (C root).core.erase.core.leader = true)
    (hfree : PPLLPpsiLeaderCreationRepair.BulletTwoFreeAwayFrom C root)
    (hnonzero : ∀ s, s < steps →
      (C (groupOffset ring root (n - s))).core.erase.core.label ≠
        ⟨0, hpsi⟩) :
    let T :=
      wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
        hpsi kappa tau
    let D := runLocalSchedule ring T C
      (pPsiProbeChasePrefix ring root steps)
    ReverseMigrationState ring root C D steps := by
  induction steps with
  | zero =>
      simpa [pPsiProbeChasePrefix, runLocalSchedule] using
        (reverseMigrationState_zero ring root C hnoActive hunique hroot hfree)
  | succ steps ih =>
      let T :=
        wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
          hpsi kappa tau
      let current := runLocalSchedule ring T C
        (pPsiProbeChasePrefix ring root steps)
      have hprefix : ReverseMigrationState ring root C current steps := by
        exact ih (by omega) (fun s hs => hnonzero s (by omega))
      have hnext := hprefix.step_of_root_nonzero
        hpsi ring hn root C current steps (by omega)
          (hnonzero steps (by omega))
      simpa [T, current, pPsiProbeChasePrefix,
        runLocalSchedule_append_generic, runLocalSchedule] using hnext

set_option maxHeartbeats 1000000 in
/-- Birth-signal-transition form of one strict reverse-migration step.  The
active edge already contains the unique leader as its responder, so the birth
wrapper is inert and the established strict frame transports exactly. -/
theorem ReverseMigrationState.step_birthSignalZero_of_root_nonzero
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (root : Fin n) (base current : EConfig n psi kappa tau)
    (steps : Nat)
    (hstate : ReverseMigrationState ring root base current steps)
    (hsteps : steps < n)
    (hnonzero :
      (base (groupOffset ring root (n - steps))).core.erase.core.label ≠
        ⟨0, hpsi⟩) :
    let e := groupOffset ring root (n - 1 - steps)
    let D := localStep ring
      (wallSweepBirthSignalZeroPathStallTransition
        hpsi kappa tau) current e
    ReverseMigrationState ring root base D (steps + 1) := by
  let e := groupOffset ring root (n - 1 - steps)
  let Told :=
    wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
      hpsi kappa tau
  let Tnew := wallSweepBirthSignalZeroPathStallTransition
    hpsi kappa tau
  let Dold := localStep ring Told current e
  let Dnew := localStep ring Tnew current e
  have hold := hstate.step_of_root_nonzero
    hpsi ring hn root base current steps hsteps hnonzero
  change ReverseMigrationState ring root base Dold (steps + 1) at hold
  have hindex : n - 1 - steps + 1 = n - steps := by omega
  have hneighbor : ring.rightNeighbor e =
      groupOffset ring root (n - steps) := by
    rw [show e = groupOffset ring root (n - 1 - steps) by rfl,
      rightNeighbor_groupOffset, hindex]
  have hrightLeader :
      (current (ring.rightNeighbor e)).core.erase.core.leader = true := by
    rw [hneighbor]
    exact hstate.root_alive
  have heq : Dnew = Dold := by
    apply localStep_eq_of_pair_eq
    simpa [Tnew, Told] using
      wallSweepBirthSignalZeroPathStall_eq_of_right_leader
        hpsi kappa tau (current e)
          (current (ring.rightNeighbor e)) hrightLeader
  change ReverseMigrationState ring root base Dnew (steps + 1)
  rw [heq]
  exact hold

set_option maxHeartbeats 1000000 in
/-- The strict reverse-migration chase under the birth-signal transition. -/
theorem pPsiProbeChasePrefix_birthSignalZero_reverseMigrationState
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (root : Fin n) (C : EConfig n psi kappa tau)
    (steps : Nat) (hsteps : steps ≤ n)
    (hnoActive : NoActiveDeletion C)
    (hunique : hasUniqueLeader n
      (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig C))
    (hroot : (C root).core.erase.core.leader = true)
    (hfree : PPLLPpsiLeaderCreationRepair.BulletTwoFreeAwayFrom C root)
    (hnonzero : ∀ s, s < steps →
      (C (groupOffset ring root (n - s))).core.erase.core.label ≠
        ⟨0, hpsi⟩) :
    let T := wallSweepBirthSignalZeroPathStallTransition
      hpsi kappa tau
    let D := runLocalSchedule ring T C
      (pPsiProbeChasePrefix ring root steps)
    ReverseMigrationState ring root C D steps := by
  induction steps with
  | zero =>
      simpa [pPsiProbeChasePrefix, runLocalSchedule] using
        (reverseMigrationState_zero ring root C hnoActive hunique hroot hfree)
  | succ steps ih =>
      let T := wallSweepBirthSignalZeroPathStallTransition
        hpsi kappa tau
      let current := runLocalSchedule ring T C
        (pPsiProbeChasePrefix ring root steps)
      have hprefix : ReverseMigrationState ring root C current steps := by
        exact ih (by omega) (fun s hs => hnonzero s (by omega))
      have hnext := hprefix.step_birthSignalZero_of_root_nonzero
        hpsi ring hn root C current steps (by omega)
          (hnonzero steps (by omega))
      simpa [T, current, pPsiProbeChasePrefix,
        runLocalSchedule_append_generic, runLocalSchedule] using hnext

/-- Reverse-migration invariant for the live-aware lane.  It drops global
live-bullet freedom, retains a global nonincrease bound, and records that the
site vacated immediately clockwise of the new root is a non-live follower. -/
structure ReverseMigrationLooseState
    (ring : DirectedRing n) (root : Fin n)
    (base current : EConfig n psi kappa tau) (steps : Nat) : Prop where
  steps_le : steps ≤ n
  no_active : NoActiveDeletion current
  unique_leader : hasUniqueLeader n
    (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig current)
  root_alive :
    (current (groupOffset ring root (n - steps))).core.erase.core.leader = true
  right_follower : 0 < steps →
    (current (ring.rightNeighbor
      (groupOffset ring root (n - steps)))).core.erase.core.leader = false
  right_not_live : 0 < steps →
    (current (ring.rightNeighbor
      (groupOffset ring root (n - steps)))).core.erase.core.bullet ≠
        ⟨2, by omega⟩
  bullet_count_le :
    PPLLPpsiLeaderCreationRepair.bulletTwoCount current ≤
      PPLLPpsiLeaderCreationRepair.bulletTwoCount base
  labels_eq : ∀ i, (current i).core.erase.core.label =
    (base i).core.erase.core.label

/-- Zero steps form the initial loose reverse-migration state. -/
theorem reverseMigrationLooseState_zero
    (ring : DirectedRing n) (root : Fin n)
    (C : EConfig n psi kappa tau)
    (hnoActive : NoActiveDeletion C)
    (hunique : hasUniqueLeader n
      (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig C))
    (hroot : (C root).core.erase.core.leader = true) :
    ReverseMigrationLooseState ring root C C 0 := by
  refine {
    steps_le := by omega
    no_active := hnoActive
    unique_leader := hunique
    root_alive := by simpa using hroot
    right_follower := by omega
    right_not_live := by omega
    bullet_count_le := Nat.le_refl _
    labels_eq := fun _ => rfl }

set_option maxHeartbeats 2000000 in
/-- One counterclockwise chase step advances the loose migration invariant
when the current root's immutable base label is nonzero. -/
theorem ReverseMigrationLooseState.step_of_root_nonzero
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (root : Fin n) (base current : EConfig n psi kappa tau)
    (steps : Nat)
    (hstate : ReverseMigrationLooseState
      ring root base current steps)
    (hsteps : steps < n)
    (hnonzero :
      (base (groupOffset ring root (n - steps))).core.erase.core.label ≠
        ⟨0, hpsi⟩) :
    let e := groupOffset ring root (n - 1 - steps)
    let D := localStep ring
      (wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
        hpsi kappa tau) current e
    ReverseMigrationLooseState ring root base D (steps + 1) := by
  let e := groupOffset ring root (n - 1 - steps)
  let T := wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
    hpsi kappa tau
  let D := localStep ring T current e
  have hindex : n - 1 - steps + 1 = n - steps := by omega
  have hneighbor : ring.rightNeighbor e =
      groupOffset ring root (n - steps) := by
    rw [show e = groupOffset ring root (n - 1 - steps) by rfl,
      rightNeighbor_groupOffset, hindex]
  have hrLeader :
      (current (ring.rightNeighbor e)).core.erase.core.leader = true := by
    rw [hneighbor]
    exact hstate.root_alive
  have hrNonzero :
      (current (ring.rightNeighbor e)).core.erase.core.label ≠
        ⟨0, hpsi⟩ := by
    rw [hneighbor]
    intro hzero
    exact hnonzero ((hstate.labels_eq _).symm.trans hzero)
  have hframe := reverseMigration_localStep_reroot_unrestricted
    hpsi ring hn current e hstate.no_active hstate.unique_leader
      hrLeader hrNonzero
  change ReverseMigrationLocalFrame ring current D e at hframe
  have hcount := reverseMigration_localStep_bulletTwoCount_le
    hpsi ring hn current e hstate.no_active hstate.unique_leader hrLeader
  change PPLLPpsiLeaderCreationRepair.bulletTwoCount D ≤
    PPLLPpsiLeaderCreationRepair.bulletTwoCount current at hcount
  have hrootIndex : n - (steps + 1) = n - 1 - steps := by omega
  refine {
    steps_le := by omega
    no_active := hframe.no_active
    unique_leader := hframe.unique_leader
    root_alive := by simpa [e, hrootIndex] using hframe.new_root_alive
    right_follower := by
      intro _
      simpa [e, hrootIndex] using hframe.old_root_follower
    right_not_live := by
      intro _
      simpa [e, hrootIndex] using hframe.old_root_not_live
    bullet_count_le := Nat.le_trans hcount hstate.bullet_count_le
    labels_eq := by
      intro i
      exact (hframe.labels_eq i).trans (hstate.labels_eq i) }

/-- Birth-signal-transition form of one loose reverse-migration step.  The
active responder is the existing unique leader, so the wrapper is inert by
its right-input guard. -/
theorem ReverseMigrationLooseState.step_birthSignalZero_of_root_nonzero
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (root : Fin n) (base current : EConfig n psi kappa tau)
    (steps : Nat)
    (hstate : ReverseMigrationLooseState
      ring root base current steps)
    (hsteps : steps < n)
    (hnonzero :
      (base (groupOffset ring root (n - steps))).core.erase.core.label ≠
        ⟨0, hpsi⟩) :
    let e := groupOffset ring root (n - 1 - steps)
    let D := localStep ring
      (wallSweepBirthSignalZeroPathStallTransition
        hpsi kappa tau) current e
    ReverseMigrationLooseState ring root base D (steps + 1) := by
  let e := groupOffset ring root (n - 1 - steps)
  let Told :=
    wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
      hpsi kappa tau
  let Tnew := wallSweepBirthSignalZeroPathStallTransition
    hpsi kappa tau
  let Dold := localStep ring Told current e
  let Dnew := localStep ring Tnew current e
  have hindex : n - 1 - steps + 1 = n - steps := by omega
  have hneighbor : ring.rightNeighbor e =
      groupOffset ring root (n - steps) := by
    rw [show e = groupOffset ring root (n - 1 - steps) by rfl,
      rightNeighbor_groupOffset, hindex]
  have hrLeader :
      (current (ring.rightNeighbor e)).core.erase.core.leader = true := by
    rw [hneighbor]
    exact hstate.root_alive
  have heq : Dnew = Dold := by
    apply localStep_eq_of_pair_eq
    simpa [Tnew, Told] using
      wallSweepBirthSignalZeroPathStall_eq_of_right_leader
        hpsi kappa tau (current e)
          (current (ring.rightNeighbor e)) hrLeader
  have hold := hstate.step_of_root_nonzero
    hpsi ring hn root base current steps hsteps hnonzero
  change ReverseMigrationLooseState
    ring root base Dold (steps + 1) at hold
  change ReverseMigrationLooseState
    ring root base Dnew (steps + 1)
  rw [heq]
  exact hold

set_option maxHeartbeats 2000000 in
/-- The standard counterclockwise chase word composes the loose local frame. -/
theorem pPsiProbeChasePrefix_reverseMigrationLooseState
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (root : Fin n) (C : EConfig n psi kappa tau)
    (steps : Nat) (hsteps : steps ≤ n)
    (hnoActive : NoActiveDeletion C)
    (hunique : hasUniqueLeader n
      (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig C))
    (hroot : (C root).core.erase.core.leader = true)
    (hnonzero : ∀ s, s < steps →
      (C (groupOffset ring root (n - s))).core.erase.core.label ≠
        ⟨0, hpsi⟩) :
    let T :=
      wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
        hpsi kappa tau
    let D := runLocalSchedule ring T C
      (pPsiProbeChasePrefix ring root steps)
    ReverseMigrationLooseState ring root C D steps := by
  induction steps with
  | zero =>
      simpa [pPsiProbeChasePrefix, runLocalSchedule] using
        (reverseMigrationLooseState_zero ring root C
          hnoActive hunique hroot)
  | succ steps ih =>
      let T :=
        wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
          hpsi kappa tau
      let current := runLocalSchedule ring T C
        (pPsiProbeChasePrefix ring root steps)
      have hprefix : ReverseMigrationLooseState
          ring root C current steps := by
        exact ih (by omega) (fun s hs => hnonzero s (by omega))
      have hnext := hprefix.step_of_root_nonzero
        hpsi ring hn root C current steps (by omega)
          (hnonzero steps (by omega))
      simpa [T, current, pPsiProbeChasePrefix,
        runLocalSchedule_append_generic, runLocalSchedule] using hnext

/-- Birth-signal-transition form of the complete loose reverse-migration
prefix. -/
theorem pPsiProbeChasePrefix_birthSignalZero_reverseMigrationLooseState
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (root : Fin n) (C : EConfig n psi kappa tau)
    (steps : Nat) (hsteps : steps ≤ n)
    (hnoActive : NoActiveDeletion C)
    (hunique : hasUniqueLeader n
      (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig C))
    (hroot : (C root).core.erase.core.leader = true)
    (hnonzero : ∀ s, s < steps →
      (C (groupOffset ring root (n - s))).core.erase.core.label ≠
        ⟨0, hpsi⟩) :
    let T := wallSweepBirthSignalZeroPathStallTransition
      hpsi kappa tau
    let D := runLocalSchedule ring T C
      (pPsiProbeChasePrefix ring root steps)
    ReverseMigrationLooseState ring root C D steps := by
  induction steps with
  | zero =>
      simpa [pPsiProbeChasePrefix, runLocalSchedule] using
        (reverseMigrationLooseState_zero ring root C
          hnoActive hunique hroot)
  | succ steps ih =>
      let T := wallSweepBirthSignalZeroPathStallTransition
        hpsi kappa tau
      let current := runLocalSchedule ring T C
        (pPsiProbeChasePrefix ring root steps)
      have hprefix : ReverseMigrationLooseState
          ring root C current steps := by
        exact ih (by omega) (fun s hs => hnonzero s (by omega))
      have hnext := hprefix.step_birthSignalZero_of_root_nonzero
        hpsi ring hn root C current steps (by omega)
          (hnonzero steps (by omega))
      simpa [T, current, pPsiProbeChasePrefix,
        runLocalSchedule_append_generic, runLocalSchedule] using hnext

/-- Every inhabited bounded predicate on naturals has a greatest witness.
Keeping this elementary lemma local avoids adding a finite-set dependency to
the schedule layer. -/
private theorem exists_greatest_lt_of_exists
    (P : Nat → Prop) (bound : Nat)
    (hexists : ∃ k, k < bound ∧ P k) :
    ∃ k, k < bound ∧ P k ∧
      ∀ q, k < q → q < bound → ¬ P q := by
  induction bound with
  | zero =>
      obtain ⟨k, hk, _⟩ := hexists
      omega
  | succ bound ih =>
      classical
      by_cases hlast : P bound
      · exact ⟨bound, by omega, hlast, by omega⟩
      · have hearlier : ∃ k, k < bound ∧ P k := by
          obtain ⟨k, hk, hPk⟩ := hexists
          refine ⟨k, ?_, hPk⟩
          by_cases hkb : k < bound
          · exact hkb
          · have hkeq : k = bound := by omega
            subst k
            exact (hlast hPk).elim
        obtain ⟨k, hk, hPk, hmax⟩ := ih hearlier
        refine ⟨k, by omega, hPk, ?_⟩
        intro q hkq hq hPq
        by_cases hqb : q = bound
        · exact hlast (hqb ▸ hPq)
        · exact hmax q hkq (by omega) hPq

set_option maxHeartbeats 1000000 in
/-- If `k` is the greatest positive non-wrap zero-labelled offset, the reverse
chase stops there after `n-k` interactions.  This isolates the schedule theorem
from the still-separate modular-arithmetic proof that such a `k` exists in a
normalized prefix. -/
theorem reverseMigration_to_zero_of_greatest_offset
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (root : Fin n) (C : EConfig n psi kappa tau)
    (k : Nat) (hkpos : 0 < k) (hklt : k < n)
    (hnoActive : NoActiveDeletion C)
    (hunique : hasUniqueLeader n
      (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig C))
    (hroot : (C root).core.erase.core.leader = true)
    (hfree : PPLLPpsiLeaderCreationRepair.BulletTwoFreeAwayFrom C root)
    (hrootNonzero : (C root).core.erase.core.label ≠ ⟨0, hpsi⟩)
    (hzero :
      (C (groupOffset ring root k)).core.erase.core.label = ⟨0, hpsi⟩)
    (habove : ∀ q, k < q → q < n →
      (C (groupOffset ring root q)).core.erase.core.label ≠ ⟨0, hpsi⟩) :
    let T :=
      wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
        hpsi kappa tau
    let word := pPsiProbeChasePrefix ring root (n - k)
    let D := runLocalSchedule ring T C word
    word.length = n - k ∧
      NoActiveDeletion D ∧
      hasUniqueLeader n
        (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig D) ∧
      (D (groupOffset ring root k)).core.erase.core.leader = true ∧
      PPLLPpsiLeaderCreationRepair.BulletTwoFreeAwayFrom D
        (groupOffset ring root k) ∧
      (D (groupOffset ring root k)).core.erase.core.label = ⟨0, hpsi⟩ ∧
      ∀ i, (D i).core.erase.core.label =
        (C i).core.erase.core.label := by
  let T :=
    wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
      hpsi kappa tau
  let word := pPsiProbeChasePrefix ring root (n - k)
  let D := runLocalSchedule ring T C word
  have hnonzero : ∀ s, s < n - k →
      (C (groupOffset ring root (n - s))).core.erase.core.label ≠
        ⟨0, hpsi⟩ := by
    intro s hs
    by_cases hs0 : s = 0
    · subst s
      simpa using hrootNonzero
    · exact habove (n - s) (by omega) (by omega)
  have hstate := pPsiProbeChasePrefix_reverseMigrationState
    hpsi ring hn root C (n - k) (by omega) hnoActive hunique hroot hfree
      hnonzero
  change ReverseMigrationState ring root C D (n - k) at hstate
  have hrootIndex : n - (n - k) = k := by omega
  refine ⟨pPsiProbeChasePrefix_length ring root (n - k),
    hstate.no_active, hstate.unique_leader, ?_, ?_, ?_, hstate.labels_eq⟩
  · simpa [hrootIndex] using hstate.root_alive
  · simpa [hrootIndex] using hstate.bullet_two_free
  · exact (hstate.labels_eq (groupOffset ring root k)).trans hzero

set_option maxHeartbeats 1000000 in
/-- An existential positive zero-labelled offset is sufficient: choose its
greatest witness, then invoke the exact reverse-migration prefix theorem. -/
theorem reverseMigration_to_zero_of_exists_offset
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (root : Fin n) (C : EConfig n psi kappa tau)
    (hnoActive : NoActiveDeletion C)
    (hunique : hasUniqueLeader n
      (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig C))
    (hroot : (C root).core.erase.core.leader = true)
    (hfree : PPLLPpsiLeaderCreationRepair.BulletTwoFreeAwayFrom C root)
    (hrootNonzero : (C root).core.erase.core.label ≠ ⟨0, hpsi⟩)
    (hexists : ∃ k, 0 < k ∧ k < n ∧
      (C (groupOffset ring root k)).core.erase.core.label = ⟨0, hpsi⟩) :
    ∃ k, 0 < k ∧ k < n ∧
      let T :=
        wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
          hpsi kappa tau
      let word := pPsiProbeChasePrefix ring root (n - k)
      let D := runLocalSchedule ring T C word
      word.length = n - k ∧
        NoActiveDeletion D ∧
        hasUniqueLeader n
          (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig D) ∧
        (D (groupOffset ring root k)).core.erase.core.leader = true ∧
        PPLLPpsiLeaderCreationRepair.BulletTwoFreeAwayFrom D
          (groupOffset ring root k) ∧
        (D (groupOffset ring root k)).core.erase.core.label = ⟨0, hpsi⟩ ∧
        ∀ i, (D i).core.erase.core.label =
          (C i).core.erase.core.label := by
  have hbounded : ∃ k, k < n ∧
      (0 < k ∧
        (C (groupOffset ring root k)).core.erase.core.label =
          ⟨0, hpsi⟩) := by
    obtain ⟨k, hkpos, hklt, hzero⟩ := hexists
    exact ⟨k, hklt, hkpos, hzero⟩
  obtain ⟨k, hklt, ⟨hkpos, hzero⟩, hgreatest⟩ :=
    exists_greatest_lt_of_exists
      (fun q => 0 < q ∧
        (C (groupOffset ring root q)).core.erase.core.label =
          ⟨0, hpsi⟩) n hbounded
  have habove : ∀ q, k < q → q < n →
      (C (groupOffset ring root q)).core.erase.core.label ≠
        ⟨0, hpsi⟩ := by
    intro q hkq hq hqzero
    exact hgreatest q hkq hq ⟨by omega, hqzero⟩
  refine ⟨k, hkpos, hklt, ?_⟩
  exact reverseMigration_to_zero_of_greatest_offset
    hpsi ring hn root C k hkpos hklt hnoActive hunique hroot hfree
      hrootNonzero hzero habove

set_option maxHeartbeats 1000000 in
/-- Birth-signal-transition form.  If `k` is the greatest positive non-wrap zero-labelled offset, the reverse
chase stops there after `n-k` interactions.  This isolates the schedule theorem
from the still-separate modular-arithmetic proof that such a `k` exists in a
normalized prefix. -/
theorem reverseMigration_birthSignalZero_to_zero_of_greatest_offset
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (root : Fin n) (C : EConfig n psi kappa tau)
    (k : Nat) (hkpos : 0 < k) (hklt : k < n)
    (hnoActive : NoActiveDeletion C)
    (hunique : hasUniqueLeader n
      (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig C))
    (hroot : (C root).core.erase.core.leader = true)
    (hfree : PPLLPpsiLeaderCreationRepair.BulletTwoFreeAwayFrom C root)
    (hrootNonzero : (C root).core.erase.core.label ≠ ⟨0, hpsi⟩)
    (hzero :
      (C (groupOffset ring root k)).core.erase.core.label = ⟨0, hpsi⟩)
    (habove : ∀ q, k < q → q < n →
      (C (groupOffset ring root q)).core.erase.core.label ≠ ⟨0, hpsi⟩) :
    let T :=
      wallSweepBirthSignalZeroPathStallTransition
        hpsi kappa tau
    let word := pPsiProbeChasePrefix ring root (n - k)
    let D := runLocalSchedule ring T C word
    word.length = n - k ∧
      NoActiveDeletion D ∧
      hasUniqueLeader n
        (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig D) ∧
      (D (groupOffset ring root k)).core.erase.core.leader = true ∧
      PPLLPpsiLeaderCreationRepair.BulletTwoFreeAwayFrom D
        (groupOffset ring root k) ∧
      (D (groupOffset ring root k)).core.erase.core.label = ⟨0, hpsi⟩ ∧
      ∀ i, (D i).core.erase.core.label =
        (C i).core.erase.core.label := by
  let T :=
    wallSweepBirthSignalZeroPathStallTransition
      hpsi kappa tau
  let word := pPsiProbeChasePrefix ring root (n - k)
  let D := runLocalSchedule ring T C word
  have hnonzero : ∀ s, s < n - k →
      (C (groupOffset ring root (n - s))).core.erase.core.label ≠
        ⟨0, hpsi⟩ := by
    intro s hs
    by_cases hs0 : s = 0
    · subst s
      simpa using hrootNonzero
    · exact habove (n - s) (by omega) (by omega)
  have hstate := pPsiProbeChasePrefix_birthSignalZero_reverseMigrationState
    hpsi ring hn root C (n - k) (by omega) hnoActive hunique hroot hfree
      hnonzero
  change ReverseMigrationState ring root C D (n - k) at hstate
  have hrootIndex : n - (n - k) = k := by omega
  refine ⟨pPsiProbeChasePrefix_length ring root (n - k),
    hstate.no_active, hstate.unique_leader, ?_, ?_, ?_, hstate.labels_eq⟩
  · simpa [hrootIndex] using hstate.root_alive
  · simpa [hrootIndex] using hstate.bullet_two_free
  · exact (hstate.labels_eq (groupOffset ring root k)).trans hzero

set_option maxHeartbeats 1000000 in
/-- Birth-signal-transition form.  An existential positive zero-labelled offset is sufficient: choose its
greatest witness, then invoke the exact reverse-migration prefix theorem. -/
theorem reverseMigration_birthSignalZero_to_zero_of_exists_offset
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (root : Fin n) (C : EConfig n psi kappa tau)
    (hnoActive : NoActiveDeletion C)
    (hunique : hasUniqueLeader n
      (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig C))
    (hroot : (C root).core.erase.core.leader = true)
    (hfree : PPLLPpsiLeaderCreationRepair.BulletTwoFreeAwayFrom C root)
    (hrootNonzero : (C root).core.erase.core.label ≠ ⟨0, hpsi⟩)
    (hexists : ∃ k, 0 < k ∧ k < n ∧
      (C (groupOffset ring root k)).core.erase.core.label = ⟨0, hpsi⟩) :
    ∃ k, 0 < k ∧ k < n ∧
      let T :=
        wallSweepBirthSignalZeroPathStallTransition
          hpsi kappa tau
      let word := pPsiProbeChasePrefix ring root (n - k)
      let D := runLocalSchedule ring T C word
      word.length = n - k ∧
        NoActiveDeletion D ∧
        hasUniqueLeader n
          (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig D) ∧
        (D (groupOffset ring root k)).core.erase.core.leader = true ∧
        PPLLPpsiLeaderCreationRepair.BulletTwoFreeAwayFrom D
          (groupOffset ring root k) ∧
        (D (groupOffset ring root k)).core.erase.core.label = ⟨0, hpsi⟩ ∧
        ∀ i, (D i).core.erase.core.label =
          (C i).core.erase.core.label := by
  have hbounded : ∃ k, k < n ∧
      (0 < k ∧
        (C (groupOffset ring root k)).core.erase.core.label =
          ⟨0, hpsi⟩) := by
    obtain ⟨k, hkpos, hklt, hzero⟩ := hexists
    exact ⟨k, hklt, hkpos, hzero⟩
  obtain ⟨k, hklt, ⟨hkpos, hzero⟩, hgreatest⟩ :=
    exists_greatest_lt_of_exists
      (fun q => 0 < q ∧
        (C (groupOffset ring root q)).core.erase.core.label =
          ⟨0, hpsi⟩) n hbounded
  have habove : ∀ q, k < q → q < n →
      (C (groupOffset ring root q)).core.erase.core.label ≠
        ⟨0, hpsi⟩ := by
    intro q hkq hq hqzero
    exact hgreatest q hkq hq ⟨by omega, hqzero⟩
  refine ⟨k, hkpos, hklt, ?_⟩
  exact reverseMigration_birthSignalZero_to_zero_of_greatest_offset
    hpsi ring hn root C k hkpos hklt hnoActive hunique hroot hfree
      hrootNonzero hzero habove

set_option maxHeartbeats 1000000 in

/-- Live-aware reverse migration to the greatest positive zero-labelled
offset.  Unlike `reverseMigration_to_zero_of_greatest_offset`, this theorem
does not assume global live-bullet freedom.  It instead records the exact
vacated follower to the right of the new root and a global nonincrease bound
for the number of live bullets. -/
theorem reverseMigration_to_zero_unrestricted_of_greatest_offset
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (root : Fin n) (C : EConfig n psi kappa tau)
    (k : Nat) (hkpos : 0 < k) (hklt : k < n)
    (hnoActive : NoActiveDeletion C)
    (hunique : hasUniqueLeader n
      (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig C))
    (hroot : (C root).core.erase.core.leader = true)
    (hrootNonzero : (C root).core.erase.core.label ≠ ⟨0, hpsi⟩)
    (hzero :
      (C (groupOffset ring root k)).core.erase.core.label = ⟨0, hpsi⟩)
    (habove : ∀ q, k < q → q < n →
      (C (groupOffset ring root q)).core.erase.core.label ≠ ⟨0, hpsi⟩) :
    let T :=
      wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
        hpsi kappa tau
    let word := pPsiProbeChasePrefix ring root (n - k)
    let D := runLocalSchedule ring T C word
    word.length = n - k ∧
      NoActiveDeletion D ∧
      hasUniqueLeader n
        (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig D) ∧
      (D (groupOffset ring root k)).core.erase.core.leader = true ∧
      (D (ring.rightNeighbor
        (groupOffset ring root k))).core.erase.core.leader = false ∧
      (D (ring.rightNeighbor
        (groupOffset ring root k))).core.erase.core.bullet ≠
          ⟨2, by omega⟩ ∧
      PPLLPpsiLeaderCreationRepair.bulletTwoCount D ≤
        PPLLPpsiLeaderCreationRepair.bulletTwoCount C ∧
      (D (groupOffset ring root k)).core.erase.core.label = ⟨0, hpsi⟩ ∧
      ∀ i, (D i).core.erase.core.label =
        (C i).core.erase.core.label := by
  let T :=
    wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
      hpsi kappa tau
  let word := pPsiProbeChasePrefix ring root (n - k)
  let D := runLocalSchedule ring T C word
  have hnonzero : ∀ s, s < n - k →
      (C (groupOffset ring root (n - s))).core.erase.core.label ≠
        ⟨0, hpsi⟩ := by
    intro s hs
    by_cases hs0 : s = 0
    · subst s
      simpa using hrootNonzero
    · exact habove (n - s) (by omega) (by omega)
  have hstate := pPsiProbeChasePrefix_reverseMigrationLooseState
    hpsi ring hn root C (n - k) (by omega) hnoActive hunique hroot
      hnonzero
  change ReverseMigrationLooseState ring root C D (n - k) at hstate
  have hrootIndex : n - (n - k) = k := by omega
  refine ⟨pPsiProbeChasePrefix_length ring root (n - k),
    hstate.no_active, hstate.unique_leader, ?_, ?_, ?_,
    hstate.bullet_count_le, ?_, hstate.labels_eq⟩
  · simpa [hrootIndex] using hstate.root_alive
  · simpa [hrootIndex] using hstate.right_follower (by omega)
  · simpa [hrootIndex] using hstate.right_not_live (by omega)
  · exact (hstate.labels_eq (groupOffset ring root k)).trans hzero

set_option maxHeartbeats 1000000 in
/-- An existential positive zero-labelled offset suffices for unrestricted
reverse migration: choose the greatest such offset and apply the loose chase
theorem. -/
theorem reverseMigration_to_zero_unrestricted_of_exists_offset
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (root : Fin n) (C : EConfig n psi kappa tau)
    (hnoActive : NoActiveDeletion C)
    (hunique : hasUniqueLeader n
      (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig C))
    (hroot : (C root).core.erase.core.leader = true)
    (hrootNonzero : (C root).core.erase.core.label ≠ ⟨0, hpsi⟩)
    (hexists : ∃ k, 0 < k ∧ k < n ∧
      (C (groupOffset ring root k)).core.erase.core.label = ⟨0, hpsi⟩) :
    ∃ k, 0 < k ∧ k < n ∧
      let T :=
        wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
          hpsi kappa tau
      let word := pPsiProbeChasePrefix ring root (n - k)
      let D := runLocalSchedule ring T C word
      word.length = n - k ∧
        NoActiveDeletion D ∧
        hasUniqueLeader n
          (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig D) ∧
        (D (groupOffset ring root k)).core.erase.core.leader = true ∧
        (D (ring.rightNeighbor
          (groupOffset ring root k))).core.erase.core.leader = false ∧
        (D (ring.rightNeighbor
          (groupOffset ring root k))).core.erase.core.bullet ≠
            ⟨2, by omega⟩ ∧
        PPLLPpsiLeaderCreationRepair.bulletTwoCount D ≤
          PPLLPpsiLeaderCreationRepair.bulletTwoCount C ∧
        (D (groupOffset ring root k)).core.erase.core.label = ⟨0, hpsi⟩ ∧
        ∀ i, (D i).core.erase.core.label =
          (C i).core.erase.core.label := by
  have hbounded : ∃ k, k < n ∧
      (0 < k ∧
        (C (groupOffset ring root k)).core.erase.core.label =
          ⟨0, hpsi⟩) := by
    obtain ⟨k, hkpos, hklt, hzero⟩ := hexists
    exact ⟨k, hklt, hkpos, hzero⟩
  obtain ⟨k, hklt, ⟨hkpos, hzero⟩, hgreatest⟩ :=
    exists_greatest_lt_of_exists
      (fun q => 0 < q ∧
        (C (groupOffset ring root q)).core.erase.core.label =
          ⟨0, hpsi⟩) n hbounded
  have habove : ∀ q, k < q → q < n →
      (C (groupOffset ring root q)).core.erase.core.label ≠
        ⟨0, hpsi⟩ := by
    intro q hkq hq hqzero
    exact hgreatest q hkq hq ⟨by omega, hqzero⟩
  refine ⟨k, hkpos, hklt, ?_⟩
  exact reverseMigration_to_zero_unrestricted_of_greatest_offset
    hpsi ring hn root C k hkpos hklt hnoActive hunique hroot
      hrootNonzero hzero habove

set_option maxHeartbeats 1000000 in
/-- Birth-signal-transition form of unrestricted reverse migration to the
greatest positive zero-labelled offset. -/
theorem reverseMigration_birthSignalZero_to_zero_unrestricted_of_greatest_offset
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (root : Fin n) (C : EConfig n psi kappa tau)
    (k : Nat) (hkpos : 0 < k) (hklt : k < n)
    (hnoActive : NoActiveDeletion C)
    (hunique : hasUniqueLeader n
      (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig C))
    (hroot : (C root).core.erase.core.leader = true)
    (hrootNonzero : (C root).core.erase.core.label ≠ ⟨0, hpsi⟩)
    (hzero :
      (C (groupOffset ring root k)).core.erase.core.label = ⟨0, hpsi⟩)
    (habove : ∀ q, k < q → q < n →
      (C (groupOffset ring root q)).core.erase.core.label ≠ ⟨0, hpsi⟩) :
    let T := wallSweepBirthSignalZeroPathStallTransition
      hpsi kappa tau
    let word := pPsiProbeChasePrefix ring root (n - k)
    let D := runLocalSchedule ring T C word
    word.length = n - k ∧
      NoActiveDeletion D ∧
      hasUniqueLeader n
        (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig D) ∧
      (D (groupOffset ring root k)).core.erase.core.leader = true ∧
      (D (ring.rightNeighbor
        (groupOffset ring root k))).core.erase.core.leader = false ∧
      (D (ring.rightNeighbor
        (groupOffset ring root k))).core.erase.core.bullet ≠
          ⟨2, by omega⟩ ∧
      PPLLPpsiLeaderCreationRepair.bulletTwoCount D ≤
        PPLLPpsiLeaderCreationRepair.bulletTwoCount C ∧
      (D (groupOffset ring root k)).core.erase.core.label = ⟨0, hpsi⟩ ∧
      ∀ i, (D i).core.erase.core.label =
        (C i).core.erase.core.label := by
  let T := wallSweepBirthSignalZeroPathStallTransition
    hpsi kappa tau
  let word := pPsiProbeChasePrefix ring root (n - k)
  let D := runLocalSchedule ring T C word
  have hnonzero : ∀ s, s < n - k →
      (C (groupOffset ring root (n - s))).core.erase.core.label ≠
        ⟨0, hpsi⟩ := by
    intro s hs
    by_cases hs0 : s = 0
    · subst s
      simpa using hrootNonzero
    · exact habove (n - s) (by omega) (by omega)
  have hstate :=
    pPsiProbeChasePrefix_birthSignalZero_reverseMigrationLooseState
      hpsi ring hn root C (n - k) (by omega) hnoActive hunique hroot
        hnonzero
  change ReverseMigrationLooseState ring root C D (n - k) at hstate
  have hrootIndex : n - (n - k) = k := by omega
  refine ⟨pPsiProbeChasePrefix_length ring root (n - k),
    hstate.no_active, hstate.unique_leader, ?_, ?_, ?_,
    hstate.bullet_count_le, ?_, hstate.labels_eq⟩
  · simpa [hrootIndex] using hstate.root_alive
  · simpa [hrootIndex] using hstate.right_follower (by omega)
  · simpa [hrootIndex] using hstate.right_not_live (by omega)
  · exact (hstate.labels_eq (groupOffset ring root k)).trans hzero

set_option maxHeartbeats 1000000 in
/-- An existential positive zero-labelled offset suffices for birth-signal
unrestricted reverse migration. -/
theorem reverseMigration_birthSignalZero_to_zero_unrestricted_of_exists_offset
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (root : Fin n) (C : EConfig n psi kappa tau)
    (hnoActive : NoActiveDeletion C)
    (hunique : hasUniqueLeader n
      (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig C))
    (hroot : (C root).core.erase.core.leader = true)
    (hrootNonzero : (C root).core.erase.core.label ≠ ⟨0, hpsi⟩)
    (hexists : ∃ k, 0 < k ∧ k < n ∧
      (C (groupOffset ring root k)).core.erase.core.label = ⟨0, hpsi⟩) :
    ∃ k, 0 < k ∧ k < n ∧
      let T := wallSweepBirthSignalZeroPathStallTransition
        hpsi kappa tau
      let word := pPsiProbeChasePrefix ring root (n - k)
      let D := runLocalSchedule ring T C word
      word.length = n - k ∧
        NoActiveDeletion D ∧
        hasUniqueLeader n
          (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig D) ∧
        (D (groupOffset ring root k)).core.erase.core.leader = true ∧
        (D (ring.rightNeighbor
          (groupOffset ring root k))).core.erase.core.leader = false ∧
        (D (ring.rightNeighbor
          (groupOffset ring root k))).core.erase.core.bullet ≠
            ⟨2, by omega⟩ ∧
        PPLLPpsiLeaderCreationRepair.bulletTwoCount D ≤
          PPLLPpsiLeaderCreationRepair.bulletTwoCount C ∧
        (D (groupOffset ring root k)).core.erase.core.label = ⟨0, hpsi⟩ ∧
        ∀ i, (D i).core.erase.core.label =
          (C i).core.erase.core.label := by
  have hbounded : ∃ k, k < n ∧
      (0 < k ∧
        (C (groupOffset ring root k)).core.erase.core.label =
          ⟨0, hpsi⟩) := by
    obtain ⟨k, hkpos, hklt, hzero⟩ := hexists
    exact ⟨k, hklt, hkpos, hzero⟩
  obtain ⟨k, hklt, ⟨hkpos, hzero⟩, hgreatest⟩ :=
    exists_greatest_lt_of_exists
      (fun q => 0 < q ∧
        (C (groupOffset ring root q)).core.erase.core.label =
          ⟨0, hpsi⟩) n hbounded
  have habove : ∀ q, k < q → q < n →
      (C (groupOffset ring root q)).core.erase.core.label ≠
        ⟨0, hpsi⟩ := by
    intro q hkq hq hqzero
    exact hgreatest q hkq hq ⟨by omega, hqzero⟩
  refine ⟨k, hkpos, hklt, ?_⟩
  exact
    reverseMigration_birthSignalZero_to_zero_unrestricted_of_greatest_offset
      hpsi ring hn root C k hkpos hklt hnoActive hunique hroot
        hrootNonzero hzero habove

/-- A priority-open rooted step at the named leader preserves the invariant
that no other site carries a live bullet.  The only active non-leader output
is the responder, whose live-bullet origin is its own input. -/
theorem leaderSink_localStep_bulletTwoFreeAwayFrom
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (C : EConfig n psi kappa tau) (leader : Fin n)
    (hnoActive : NoActiveDeletion C)
    (hfree : PPLLPpsiLeaderCreationRepair.BulletTwoFreeAwayFrom C leader) :
    let D := localStep ring
      (wallSweepPreCheckResetLeaderSinkPathStallTransition
        hpsi kappa tau) C leader
    PPLLPpsiLeaderCreationRepair.BulletTwoFreeAwayFrom D leader := by
  let j := ring.rightNeighbor leader
  have hje : j ≠ leader :=
    rightNeighbor_ne_self_of_one_lt ring hn leader
  have hopen : WallPriorityOpen (C leader) (C j) := by
    simpa [j] using
      WallPriorityOpen.of_noActiveDeletion C hnoActive ring leader
  let T := wallSweepPreCheckResetLeaderSinkPathStallTransition
    hpsi kappa tau
  let D := localStep ring T C leader
  change PPLLPpsiLeaderCreationRepair.BulletTwoFreeAwayFrom D leader
  intro i hiLeader
  by_cases hij : i = j
  · subst i
    intro houtLive
    have hpairLive :
        (T (C leader) (C j)).2.core.erase.core.bullet =
          ⟨2, by omega⟩ := by
      simpa [D, localStep, j, hje] using houtLive
    have hinLive :=
      wallSweepPreCheckResetLeaderSinkPathStall_priority_open_responder_live_origin
        hpsi (C leader) (C j) hopen hpairLive
    exact hfree j hje hinLive
  · have hsame : D i = C i := by
      simp [D, T, localStep, j, hiLeader, hij]
    rw [hsame]
    exact hfree i hiLeader

/-- A priority-open rooted leader step preserves non-liveness of its immediate
follower.  The responder-live origin theorem rules out a fresh live bullet at
that site; no global follower-freedom premise is needed. -/
theorem leaderSink_localStep_right_not_live_of_right_not_live
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (C : EConfig n psi kappa tau) (leader : Fin n)
    (hnoActive : NoActiveDeletion C)
    (hrNotLive :
      (C (ring.rightNeighbor leader)).core.erase.core.bullet ≠
        ⟨2, by omega⟩) :
    let D := localStep ring
      (wallSweepPreCheckResetLeaderSinkPathStallTransition
        hpsi kappa tau) C leader
    (D (ring.rightNeighbor leader)).core.erase.core.bullet ≠
      ⟨2, by omega⟩ := by
  let j := ring.rightNeighbor leader
  have hje : j ≠ leader :=
    rightNeighbor_ne_self_of_one_lt ring hn leader
  have hopen : WallPriorityOpen (C leader) (C j) := by
    simpa [j] using
      WallPriorityOpen.of_noActiveDeletion C hnoActive ring leader
  let T := wallSweepPreCheckResetLeaderSinkPathStallTransition
    hpsi kappa tau
  let D := localStep ring T C leader
  change (D j).core.erase.core.bullet ≠ ⟨2, by omega⟩
  intro houtLive
  have hpairLive :
      (T (C leader) (C j)).2.core.erase.core.bullet =
        ⟨2, by omega⟩ := by
    simpa [D, T, localStep, j, hje] using houtLive
  have hinLive :=
    wallSweepPreCheckResetLeaderSinkPathStall_priority_open_responder_live_origin
      hpsi (C leader) (C j) hopen hpairLive
  exact hrNotLive (by simpa [j] using hinLive)

/-- A reset-aware follower interaction preserves live-bullet freedom away
from the named leader.  Both active endpoints are followers, their input pair
has zero live-bullet mass, and the complete transition cannot increase that
pair mass. -/
theorem resetAwareFollower_localStep_bulletTwoFreeAwayFrom
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (C : EConfig n psi kappa tau) (e leader : Fin n)
    (hnoActive : NoActiveDeletion C)
    (hlFollower : (C e).core.erase.core.leader = false)
    (hlReset : (C e).core.erase.core.reset_cmd = true)
    (hrFollower :
      (C (ring.rightNeighbor e)).core.erase.core.leader = false)
    (hfree : PPLLPpsiLeaderCreationRepair.BulletTwoFreeAwayFrom C leader)
    (heLeader : e ≠ leader)
    (hjLeader : ring.rightNeighbor e ≠ leader) :
    let D := localStep ring
      (wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
        hpsi kappa tau) C e
    PPLLPpsiLeaderCreationRepair.BulletTwoFreeAwayFrom D leader := by
  let j := ring.rightNeighbor e
  have hje : j ≠ e := rightNeighbor_ne_self_of_one_lt ring hn e
  let T := wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
    hpsi kappa tau
  let q := T (C e) (C j)
  let D := localStep ring T C e
  have hopen : WallPriorityOpen (C e) (C j) := by
    simpa [j] using
      WallPriorityOpen.of_noActiveDeletion C hnoActive ring e
  have hlocal :
      bulletTwoPairMass q.1.core.erase.core q.2.core.erase.core ≤
        bulletTwoPairMass (C e).core.erase.core (C j).core.erase.core := by
    exact
      (wallSweepResetProbePreCheckResetLeaderSinkPathStall_priority_open_reset_follower_bulletTwoPair
        hpsi (C e) (C j) hopen hlFollower hlReset
          (by simpa [j] using hrFollower)).le
  have heFree := hfree e heLeader
  have hjFree := hfree j (by simpa [j] using hjLeader)
  have hinputZero :
      bulletTwoPairMass (C e).core.erase.core (C j).core.erase.core = 0 := by
    unfold bulletTwoPairMass bulletTwoMass
    rw [if_neg heFree, if_neg hjFree]
  have houtputZero :
      bulletTwoPairMass q.1.core.erase.core q.2.core.erase.core = 0 := by
    rw [hinputZero] at hlocal
    omega
  have hleftMass : bulletTwoMass q.1.core.erase.core = 0 := by
    unfold bulletTwoPairMass at houtputZero
    omega
  have hrightMass : bulletTwoMass q.2.core.erase.core = 0 := by
    unfold bulletTwoPairMass at houtputZero
    omega
  have hleftFree :
      q.1.core.erase.core.bullet ≠ ⟨2, by omega⟩ := by
    intro hlive
    unfold bulletTwoMass at hleftMass
    rw [hlive] at hleftMass
    simp at hleftMass
  have hrightFree :
      q.2.core.erase.core.bullet ≠ ⟨2, by omega⟩ := by
    intro hlive
    unfold bulletTwoMass at hrightMass
    rw [hlive] at hrightMass
    simp at hrightMass
  change PPLLPpsiLeaderCreationRepair.BulletTwoFreeAwayFrom D leader
  intro i hiLeader
  by_cases hie : i = e
  · subst i
    simpa [D, q, T, localStep, j] using hleftFree
  · by_cases hij : i = j
    · subst i
      simpa [D, q, T, localStep, j, hje] using hrightFree
    · have hsame : D i = C i := by
        simp [D, T, localStep, j, hie, hij]
      rw [hsame]
      exact hfree i hiLeader

/-- Since the global step frames every physical leader bit, any unique leader
present before the follower-reset interaction remains unique afterwards. -/
theorem ResetAwareFollowerGlobalStepFrame.hasUniqueLeader
    {hpsi : psi > 0} {ring : DirectedRing n}
    {C D : EConfig n psi kappa tau} {e : Fin n}
    (hframe : ResetAwareFollowerGlobalStepFrame hpsi ring C D e)
    (hunique : hasUniqueLeader n (eraseExpiringConfig C)) :
    hasUniqueLeader n (eraseExpiringConfig D) := by
  obtain ⟨leader, hleader, honly⟩ := hunique
  refine ⟨leader, ?_, ?_⟩
  · change (D leader).core.erase.core.leader = true
    change (C leader).core.erase.core.leader = true at hleader
    exact (hframe.leader_eq leader).trans hleader
  · intro i hi
    apply honly i
    change (C i).core.erase.core.leader = true
    change (D i).core.erase.core.leader = true at hi
    exact (hframe.leader_eq i).symm.trans hi

/-- Successor alignment only on the clockwise prefix already crossed by the
authenticated reset.  Unlike `stable_labels`, this imposes no condition on
the untouched suffix or on the closing edge. -/
def NormalizedClockwisePrefix
    (hpsi : psi > 0) (ring : DirectedRing n) (leader : Fin n)
    (C : EConfig n psi kappa tau) (steps : Nat) : Prop :=
  ∀ k, k < steps →
    (C (groupOffset ring leader (k + 1))).core.erase.core.label =
      ⟨((C (groupOffset ring leader k)).core.erase.core.label.val + 1) %
          psi,
        Nat.mod_lt _ hpsi⟩

/-- Iterating the local successor equations identifies every label in a
normalized prefix with the root label plus its clockwise offset modulo
`psi`. -/
theorem NormalizedClockwisePrefix.label_eq_root_add_mod
    {hpsi : psi > 0} {ring : DirectedRing n} {leader : Fin n}
    {C : EConfig n psi kappa tau} {steps : Nat}
    (hprefix : NormalizedClockwisePrefix hpsi ring leader C steps)
    (k : Nat) (hk : k ≤ steps) :
    (C (groupOffset ring leader k)).core.erase.core.label =
      ⟨((C leader).core.erase.core.label.val + k) % psi,
        Nat.mod_lt _ hpsi⟩ := by
  induction k with
  | zero =>
      apply Fin.ext
      simp [groupOffset_zero_eq,
        Nat.mod_eq_of_lt (C leader).core.erase.core.label.isLt]
  | succ k ih =>
      have hstep := hprefix k (by omega)
      rw [hstep]
      apply Fin.ext
      have ihVal := congrArg Fin.val (ih (by omega))
      dsimp only at ihVal ⊢
      rw [ihVal, mod_add_one]
      congr 1

/-- A normalized prefix at least one full label period long contains a
positive zero-labelled offset whenever its root label is nonzero. -/
theorem NormalizedClockwisePrefix.exists_positive_zero_of_root_nonzero
    {hpsi : psi > 0} {ring : DirectedRing n} {leader : Fin n}
    {C : EConfig n psi kappa tau} {steps : Nat}
    (hprefix : NormalizedClockwisePrefix hpsi ring leader C steps)
    (hperiod : psi ≤ steps + 1)
    (hrootNonzero : (C leader).core.erase.core.label ≠ ⟨0, hpsi⟩) :
    ∃ k, 0 < k ∧ k ≤ steps ∧
      (C (groupOffset ring leader k)).core.erase.core.label = ⟨0, hpsi⟩ := by
  let a := (C leader).core.erase.core.label.val
  let k := psi - a
  have haLt : a < psi := (C leader).core.erase.core.label.isLt
  have haPos : 0 < a := by
    by_cases ha : a = 0
    · have hzeroFin : (C leader).core.erase.core.label = ⟨0, hpsi⟩ := by
        apply Fin.ext
        exact ha
      exact False.elim (hrootNonzero hzeroFin)
    · omega
  have hkPos : 0 < k := by omega
  have hkLt : k < psi := by omega
  have hkSteps : k ≤ steps := by omega
  have hsum : a + k = psi := by omega
  refine ⟨k, hkPos, hkSteps, ?_⟩
  calc
    (C (groupOffset ring leader k)).core.erase.core.label =
        ⟨(a + k) % psi, Nat.mod_lt _ hpsi⟩ := by
          simpa [a] using hprefix.label_eq_root_add_mod k hkSteps
    _ = ⟨0, hpsi⟩ := by
      apply Fin.ext
      simp [hsum]

/-- Positive non-wrap prefix state for the reset-aware traversal.  It starts
after the leader has handed reset to its first follower.  Remote protocol
carriers are intentionally absent from the invariant. -/
structure ResetAwareNormalizedPrefixState
    (hpsi : psi > 0) (ring : DirectedRing n) (leader : Fin n)
    (base current : EConfig n psi kappa tau) (steps : Nat) : Prop where
  steps_pos : 0 < steps
  steps_le : steps ≤ n - 1
  no_active : NoActiveDeletion current
  leader_alive : (current leader).core.erase.core.leader = true
  unique_leader : ∀ i, i ≠ leader →
    (current i).core.erase.core.leader = false
  frontier_reset :
    (current (groupOffset ring leader steps)).core.erase.core.reset_cmd = true
  normalized_prefix :
    NormalizedClockwisePrefix hpsi ring leader current steps
  visited_neutral : VisitedPrefixNeutral ring leader current steps
  untouched_ahead : UntouchedAhead ring leader base current steps
  reset_behind : ∀ k, k < steps →
    (current (groupOffset ring leader k)).core.erase.core.reset_cmd = false

set_option maxHeartbeats 3000000 in
/-- The nearest live-responder case of the reset sweep.  The follower step
moves the offset-two live bullet into the immediate follower.  The following
leader attempt then either leaves the unique leader alive and shielded, or
makes the configuration leaderless while strictly decreasing the original
global live count. -/
theorem ResetAwareNormalizedPrefixState.first_live_then_leader_attempt
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (leader : Fin n) (base current : EConfig n psi kappa tau)
    (hstate : ResetAwareNormalizedPrefixState
      hpsi ring leader base current 1)
    (hroom : 1 < n - 1)
    (hleaderSignalZero :
      (current leader).core.erase.core.signal_B = ⟨0, by omega⟩)
    (hrightLive :
      (current (groupOffset ring leader 2)).core.erase.core.bullet =
        ⟨2, by omega⟩) :
    let e := groupOffset ring leader 1
    let T :=
      wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
        hpsi kappa tau
    let C1 := localStep ring T current e
    let D := localStep ring T C1 leader
    (C1 e).core.erase.core.bullet = ⟨2, by omega⟩ ∧
      (C1 (groupOffset ring leader 2)).core.erase.core.bullet =
        ⟨0, by omega⟩ ∧
      NoActiveDeletion D ∧
      (D leader).core.erase.core.label =
        (current leader).core.erase.core.label ∧
      (D leader).core.erase.core.signal_B = ⟨0, by omega⟩ ∧
      ((hasUniqueLeader n
          (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig D) ∧
          (D leader).core.erase.core.leader = true ∧
          (D leader).core.erase.core.shield = true ∧
          (D (ring.rightNeighbor leader)).core.erase.core.bullet =
            ⟨2, by omega⟩ ∧
          PPLLPpsiLeaderCreationRepair.bulletTwoCount D ≤
            PPLLPpsiLeaderCreationRepair.bulletTwoCount current) ∨
        (RawLeaderless
            (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig D) ∧
          PPLLPpsiLeaderCreationRepair.bulletTwoCount D <
            PPLLPpsiLeaderCreationRepair.bulletTwoCount current)) := by
  let e := groupOffset ring leader 1
  let j := groupOffset ring leader 2
  let T :=
    wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
      hpsi kappa tau
  let C1 := localStep ring T current e
  let D := localStep ring T C1 leader
  have hnpos : 0 < n := by omega
  have heBound : 1 < n := by omega
  have hjBound : 2 < n := by omega
  have hneighbor : ring.rightNeighbor e = j := by
    simpa [e, j] using rightNeighbor_groupOffset ring leader 1
  have hfirst : ring.rightNeighbor leader = e := by
    have hnext := rightNeighbor_groupOffset ring leader 0
    rw [groupOffset_zero_eq] at hnext
    simpa [e] using hnext
  have heNotLeader : e ≠ leader := by
    have hne := groupOffset_ne_of_lt ring leader heBound hnpos (by omega)
    exact fun heq =>
      hne (heq.trans (groupOffset_zero_eq ring leader).symm)
  have hjNotLeader : j ≠ leader := by
    have hne := groupOffset_ne_of_lt ring leader hjBound hnpos (by omega)
    exact fun heq =>
      hne (heq.trans (groupOffset_zero_eq ring leader).symm)
  have hstep := resetAwareFollower_localStep_normalizes
    hpsi ring hn current e hstate.no_active
      (hstate.unique_leader e heNotLeader) hstate.frontier_reset
      (by rw [hneighbor]; exact hstate.unique_leader j hjNotLeader)
  change ResetAwareFollowerGlobalStepFrame hpsi ring current C1 e at hstep
  have hshift := resetAwareFollower_localStep_live_bullet_shifts_left
    hpsi ring hn current e hstate.no_active
      (hstate.unique_leader e heNotLeader) hstate.frontier_reset
      (by rw [hneighbor]; exact hstate.unique_leader j hjNotLeader)
      (by rw [hneighbor]; simpa [j] using hrightLive)
  change (C1 e).core.erase.core.bullet = ⟨2, by omega⟩ ∧
      (C1 (ring.rightNeighbor e)).core.erase.core.bullet =
        ⟨0, by omega⟩ at hshift
  have hrightZero : (C1 j).core.erase.core.bullet =
      ⟨0, by omega⟩ := by
    rw [← hneighbor]
    exact hshift.2
  have hleaderC1 : (C1 leader).core.erase.core.leader = true :=
    (hstep.leader_eq leader).trans hstate.leader_alive
  have huniqueC1 : hasUniqueLeader n
      (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig C1) := by
    refine ⟨leader, hleaderC1, ?_⟩
    intro i hi
    by_cases hie : i = leader
    · exact hie
    · change (C1 i).core.erase.core.leader = true at hi
      have hfalse := (hstep.leader_eq i).trans
        (hstate.unique_leader i hie)
      have hbad : (false : Bool) = true := hfalse.symm.trans hi
      exact (Bool.false_ne_true hbad).elim
  have hleaderOff : C1 leader = current leader :=
    hstep.off_edge leader (Ne.symm heNotLeader) (by
      rw [hneighbor]
      exact Ne.symm hjNotLeader)
  have hrightLiveC1 :
      (C1 (ring.rightNeighbor leader)).core.erase.core.bullet =
        ⟨2, by omega⟩ := by
    rw [hfirst]
    exact hshift.1
  have hattempt := resetAwareLeader_liveResponder_attempt
    hpsi ring hn C1 leader hstep.no_active huniqueC1 hleaderC1
      hrightLiveC1
  change NoActiveDeletion D ∧
      (D leader).core.erase.core.label =
        (C1 leader).core.erase.core.label ∧
      (D leader).core.erase.core.signal_B = ⟨0, by omega⟩ ∧
      ((hasUniqueLeader n
          (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig D) ∧
          (D leader).core.erase.core.leader = true ∧
          (D leader).core.erase.core.shield = true ∧
          (D (ring.rightNeighbor leader)).core.erase.core.bullet =
            ⟨2, by omega⟩) ∨
        (RawLeaderless
            (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig D) ∧
          PPLLPpsiLeaderCreationRepair.bulletTwoCount D <
            PPLLPpsiLeaderCreationRepair.bulletTwoCount C1)) at hattempt
  have hfirstCount := resetAwareFollower_localStep_bulletTwoCount_le
    hpsi ring hn current e hstate.no_active
      (hstate.unique_leader e heNotLeader) hstate.frontier_reset
      (by rw [hneighbor]; exact hstate.unique_leader j hjNotLeader)
  change PPLLPpsiLeaderCreationRepair.bulletTwoCount C1 ≤
    PPLLPpsiLeaderCreationRepair.bulletTwoCount current at hfirstCount
  have hleaderSignalC1 :
      (C1 leader).core.erase.core.signal_B = ⟨0, by omega⟩ := by
    rw [hleaderOff]
    exact hleaderSignalZero
  have hsecondCount := resetAwareLeader_signalZero_localStep_bulletTwoCount_le
    hpsi ring hn C1 leader hstep.no_active hleaderC1 hleaderSignalC1
  change PPLLPpsiLeaderCreationRepair.bulletTwoCount D ≤
    PPLLPpsiLeaderCreationRepair.bulletTwoCount C1 at hsecondCount
  have hbranch :
      (hasUniqueLeader n
          (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig D) ∧
          (D leader).core.erase.core.leader = true ∧
          (D leader).core.erase.core.shield = true ∧
          (D (ring.rightNeighbor leader)).core.erase.core.bullet =
            ⟨2, by omega⟩ ∧
          PPLLPpsiLeaderCreationRepair.bulletTwoCount D ≤
            PPLLPpsiLeaderCreationRepair.bulletTwoCount current) ∨
        (RawLeaderless
            (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig D) ∧
          PPLLPpsiLeaderCreationRepair.bulletTwoCount D <
            PPLLPpsiLeaderCreationRepair.bulletTwoCount current) := by
    rcases hattempt.2.2.2 with hsurvives | hleaderless
    · exact .inl ⟨hsurvives.1, hsurvives.2.1,
        hsurvives.2.2.1, hsurvives.2.2.2,
        Nat.le_trans hsecondCount hfirstCount⟩
    · exact .inr ⟨hleaderless.1,
        Nat.lt_of_lt_of_le hleaderless.2 hfirstCount⟩
  change (C1 e).core.erase.core.bullet = ⟨2, by omega⟩ ∧
    (C1 j).core.erase.core.bullet = ⟨0, by omega⟩ ∧
    NoActiveDeletion D ∧
    (D leader).core.erase.core.label =
      (current leader).core.erase.core.label ∧
    (D leader).core.erase.core.signal_B = ⟨0, by omega⟩ ∧
    ((hasUniqueLeader n
        (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig D) ∧
        (D leader).core.erase.core.leader = true ∧
        (D leader).core.erase.core.shield = true ∧
        (D (ring.rightNeighbor leader)).core.erase.core.bullet =
          ⟨2, by omega⟩ ∧
        PPLLPpsiLeaderCreationRepair.bulletTwoCount D ≤
          PPLLPpsiLeaderCreationRepair.bulletTwoCount current) ∨
      (RawLeaderless
          (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig D) ∧
        PPLLPpsiLeaderCreationRepair.bulletTwoCount D <
          PPLLPpsiLeaderCreationRepair.bulletTwoCount current))
  exact ⟨hshift.1, hrightZero, hattempt.1,
    hattempt.2.1.trans (congrArg
      (fun u : ExpiringAgentState psi kappa tau =>
        u.core.erase.core.label) hleaderOff),
    hattempt.2.2.1, hbranch⟩

/-- Round boundary for the recursive reset-aware scheduler.  The exact
frontier certificate retains the named leader and the first follower's false
echo; live bullets remain confined to that leader. -/
def ResetAwareRetryReady
    (hpsi : psi > 0) (ring : DirectedRing n) (leader : Fin n)
    (C : EConfig n psi kappa tau) : Prop :=
  PPLLPpsiLeaderCreationRepair.OutgoingResetFrontierUniqueLeaderAt
      hpsi ring C leader ∧
    PPLLPpsiLeaderCreationRepair.BulletTwoFreeAwayFrom C leader

/-- Weakened restart boundary for the live-bullet drainage lane.  It protects
only the next leader edge; remote live bullets are admitted and are ranked by
`clockwiseMobileLiveRank`.  The zero leader signal prevents a reseed from
creating an additional live bullet. -/
def ResetAwareLiveRetryReady
    (hpsi : psi > 0) (ring : DirectedRing n) (leader : Fin n)
    (C : EConfig n psi kappa tau) : Prop :=
  PPLLPpsiLeaderCreationRepair.OutgoingResetFrontierUniqueLeaderAt
      hpsi ring C leader ∧
    (C (ring.rightNeighbor leader)).core.erase.core.bullet ≠
      ⟨2, by omega⟩ ∧
    (C leader).core.erase.core.signal_B = ⟨0, by omega⟩

/-- Lexicographic rank for the last unshielded zero-root lane.  Remote live
bullets form the high digit and follower echoes form the low digit. -/
def clockwiseLiveEchoRetryRank
    (ring : DirectedRing n) (leader : Fin n)
    (C : EConfig n psi kappa tau) : Nat :=
  clockwiseMobileLiveRank ring leader C * 2 ^ (n - 1) +
    clockwiseEchoRank ring leader C

/-- A strict decrease of the mobile live rank decreases the combined rank,
regardless of the new follower-echo pattern. -/
theorem clockwiseLiveEchoRetryRank_lt_of_live_lt
    (ring : DirectedRing n) (leader : Fin n)
    (before after : EConfig n psi kappa tau)
    (hlive : clockwiseMobileLiveRank ring leader after <
      clockwiseMobileLiveRank ring leader before) :
    clockwiseLiveEchoRetryRank ring leader after <
      clockwiseLiveEchoRetryRank ring leader before := by
  have hechoAfter : clockwiseEchoRank ring leader after < 2 ^ (n - 1) :=
    binaryRank_lt_two_pow _
  have hsucc : clockwiseMobileLiveRank ring leader after + 1 ≤
      clockwiseMobileLiveRank ring leader before := by omega
  have hmul := Nat.mul_le_mul_right (2 ^ (n - 1)) hsucc
  unfold clockwiseLiveEchoRetryRank
  calc
    clockwiseMobileLiveRank ring leader after * 2 ^ (n - 1) +
          clockwiseEchoRank ring leader after <
        clockwiseMobileLiveRank ring leader after * 2 ^ (n - 1) +
          2 ^ (n - 1) := Nat.add_lt_add_left hechoAfter _
    _ = (clockwiseMobileLiveRank ring leader after + 1) *
          2 ^ (n - 1) := by simp [Nat.add_mul]
    _ ≤ clockwiseMobileLiveRank ring leader before *
          2 ^ (n - 1) := hmul
    _ ≤ clockwiseMobileLiveRank ring leader before * 2 ^ (n - 1) +
          clockwiseEchoRank ring leader before := by omega

/-- If the mobile live rank is unchanged and the echo rank decreases, the
combined retry rank decreases. -/
theorem clockwiseLiveEchoRetryRank_lt_of_live_le_echo_lt
    (ring : DirectedRing n) (leader : Fin n)
    (before after : EConfig n psi kappa tau)
    (hlive : clockwiseMobileLiveRank ring leader after ≤
      clockwiseMobileLiveRank ring leader before)
    (hecho : clockwiseEchoRank ring leader after <
      clockwiseEchoRank ring leader before) :
    clockwiseLiveEchoRetryRank ring leader after <
      clockwiseLiveEchoRetryRank ring leader before := by
  by_cases heq : clockwiseMobileLiveRank ring leader after =
      clockwiseMobileLiveRank ring leader before
  · unfold clockwiseLiveEchoRetryRank
    rw [heq]
    exact Nat.add_lt_add_left hecho _
  · exact clockwiseLiveEchoRetryRank_lt_of_live_lt
      ring leader before after (Nat.lt_of_le_of_ne hlive heq)

/-- Vanishing mobile-live rank closes the weakened retry boundary: the named
first follower is non-live by hypothesis, and every remaining follower is a
zero bit of the mobile rank. -/
theorem ResetAwareLiveRetryReady.toRetryReady_of_mobileLiveRank_eq_zero
    {hpsi : psi > 0} (ring : DirectedRing n) (leader : Fin n)
    (C : EConfig n psi kappa tau)
    (hready : ResetAwareLiveRetryReady hpsi ring leader C)
    (hzero : clockwiseMobileLiveRank ring leader C = 0) :
    ResetAwareRetryReady hpsi ring leader C := by
  obtain ⟨hfrontier, hfirstNotLive, _hsignal⟩ := hready
  refine ⟨hfrontier, ?_⟩
  have hall := (binaryRank_eq_zero_iff
    (clockwiseMobileLiveBits ring leader C)).mp hzero
  intro i hi
  let k := cwDist ring leader i
  have hkBound : k < n := cwDist_lt ring leader i
  have hpos : groupOffset ring leader k = i := by
    simpa [groupOffset, cwPos] using cwPos_cwDist ring leader i
  have hkPos : 0 < k := by
    have hkNe : k ≠ 0 := by
      intro hkZero
      apply hi
      rw [← hpos, hkZero]
      exact groupOffset_zero_eq ring leader
    omega
  by_cases hkOne : k = 1
  · rw [← hpos, hkOne]
    have hnext := rightNeighbor_groupOffset ring leader 0
    rw [groupOffset_zero_eq] at hnext
    rw [← hnext]
    exact hfirstNotLive
  · let t : Fin (n - 2) := ⟨k - 2, by omega⟩
    have ht := hall t
    have hindex : t.val + 2 = k := by
      dsimp only [t]
      omega
    intro hlive
    change
      (if
        (C (groupOffset ring leader (t.val + 2))).core.erase.core.bullet =
          ⟨2, by omega⟩ then true else false) = false at ht
    rw [hindex] at ht
    have hliveAt :
        (C (groupOffset ring leader k)).core.erase.core.bullet =
          ⟨2, by omega⟩ := by
      rwa [hpos]
    simp [hliveAt] at ht

/-- A positive mobile live rank has a canonical nearest live responder, and
every smaller mobile offset is non-live. -/
theorem exists_firstClockwiseMobileLive_of_rank_ne_zero
    (ring : DirectedRing n) (leader : Fin n)
    (C : EConfig n psi kappa tau)
    (hrank : clockwiseMobileLiveRank ring leader C ≠ 0) :
    ∃ t : Fin (n - 2),
      firstTrue? (clockwiseMobileLiveBits ring leader C) = some t ∧
      (C (groupOffset ring leader (t.val + 2))).core.erase.core.bullet =
        ⟨2, by omega⟩ ∧
      ∀ i : Fin (n - 2), i.val < t.val →
        (C (groupOffset ring leader (i.val + 2))).core.erase.core.bullet ≠
          ⟨2, by omega⟩ := by
  obtain ⟨t, hfirst, hpresent, hlower⟩ :=
    exists_firstTrue_of_binaryRank_ne_zero
      (clockwiseMobileLiveBits ring leader C) hrank
  refine ⟨t, hfirst, ?_, ?_⟩
  · simpa [clockwiseMobileLiveBits] using hpresent
  · intro i hi hlive
    have hfalse := hlower i hi
    simp [clockwiseMobileLiveBits, hlive] at hfalse

/-- No live bullet occurs on the positive clockwise prefix already crossed by
the moving reset frontier. -/
def VisitedPrefixLiveFree
    (ring : DirectedRing n) (leader : Fin n)
    (C : EConfig n psi kappa tau) (steps : Nat) : Prop :=
  ∀ k, 0 < k → k ≤ steps →
    (C (groupOffset ring leader k)).core.erase.core.bullet ≠
      ⟨2, by omega⟩

/-- Restart boundary after the nearest live responder has installed the
leader shield.  Unlike `ResetAwareLiveRetryReady`, the immediate follower is
intentionally live; the frontier's collision-safety field then certifies the
leader shield, while the zero source signal prevents later reseeds from
increasing live-bullet mass. -/
def ResetAwareShieldedLiveRetryReady
    (hpsi : psi > 0) (ring : DirectedRing n) (leader : Fin n)
    (C : EConfig n psi kappa tau) : Prop :=
  PPLLPpsiLeaderCreationRepair.OutgoingResetFrontierUniqueLeaderAt
      hpsi ring C leader ∧
    (C (ring.rightNeighbor leader)).core.erase.core.bullet =
      ⟨2, by omega⟩ ∧
    (C leader).core.erase.core.signal_B = ⟨0, by omega⟩

/-- Prefix-closed shielded restart boundary.  Unlike the live-specific
subtype above, this interface does not constrain the immediate follower's
bullet: follower motion can change that bullet while the rooted frontier,
leader shield, and zero source signal remain the recursive invariants. -/
def ResetAwareShieldedRetryReady
    (hpsi : psi > 0) (ring : DirectedRing n) (leader : Fin n)
    (C : EConfig n psi kappa tau) : Prop :=
  PPLLPpsiLeaderCreationRepair.OutgoingResetFrontierUniqueLeaderAt
      hpsi ring C leader ∧
    (C leader).core.erase.core.shield = true ∧
    (C leader).core.erase.core.signal_B = ⟨0, by omega⟩

/-- The shield is derived, not duplicated, in the shielded-live boundary: the
authenticated frontier already says that a live immediate follower implies
the named leader is shielded. -/
theorem ResetAwareShieldedLiveRetryReady.leader_shield
    {hpsi : psi > 0} {ring : DirectedRing n} {leader : Fin n}
    {C : EConfig n psi kappa tau}
    (hready : ResetAwareShieldedLiveRetryReady
      hpsi ring leader C) :
    (C leader).core.erase.core.shield = true := by
  obtain ⟨hfrontier, hrightLive, _hsignal⟩ := hready
  obtain ⟨_noActive, _hunique, _hleader, _hrightFollower,
      _haligned, _hleftProbe, _hrightProbe,
      _hleftNeutral, _hrightNeutral, _hleftReset, _hrightReset,
      _hleftEcho, _hrightEcho, hsafe⟩ := hfrontier
  exact hsafe hrightLive

/-- The live-specific boundary embeds into the prefix-closed shielded
boundary; collision safety supplies the omitted shield field. -/
theorem ResetAwareShieldedLiveRetryReady.toShielded
    {hpsi : psi > 0} {ring : DirectedRing n} {leader : Fin n}
    {C : EConfig n psi kappa tau}
    (hready : ResetAwareShieldedLiveRetryReady
      hpsi ring leader C) :
    ResetAwareShieldedRetryReady hpsi ring leader C := by
  exact ⟨hready.1, hready.leader_shield, hready.2.2⟩

/-- Signal-aware outer-round boundary.  The inner echo-rank scheduler needs
only `ResetAwareRetryReady`; repeated full rounds additionally track the
positive absence signal seeded at the first outgoing follower. -/
def ResetAwareSignalReady
    (hpsi : psi > 0) (ring : DirectedRing n) (leader : Fin n)
    (C : EConfig n psi kappa tau) : Prop :=
  ResetAwareRetryReady hpsi ring leader C ∧
    (C (ring.rightNeighbor leader)).core.erase.core.signal_B =
      ⟨1, by omega⟩

/-- Terminal scheduler state: one complete non-wrap normalized prefix has
been traversed while retaining follower live-bullet freedom. -/
def ResetAwareRetryDone
    (hpsi : psi > 0) (ring : DirectedRing n) (leader : Fin n)
    (C : EConfig n psi kappa tau) : Prop :=
  ∃ base : EConfig n psi kappa tau,
    ResetAwareNormalizedPrefixState hpsi ring leader base C (n - 1) ∧
      PPLLPpsiLeaderCreationRepair.BulletTwoFreeAwayFrom C leader

/-- Terminal boundary for the shielded lane.  The full normalized prefix is
retained, but live bullets are deliberately unrestricted; only the root
shield and zero source signal are carried to reverse migration. -/
def ResetAwareShieldedRetryDone
    (hpsi : psi > 0) (ring : DirectedRing n) (leader : Fin n)
    (C : EConfig n psi kappa tau) : Prop :=
  ∃ base : EConfig n psi kappa tau,
    ResetAwareNormalizedPrefixState hpsi ring leader base C (n - 1) ∧
      (C leader).core.erase.core.shield = true ∧
      (C leader).core.erase.core.signal_B = ⟨0, by omega⟩

/-- Common zero-root boundary after a completed shielded normalization and
optional reverse migration.  If the root itself was already zero then it
remains protected; otherwise reverse migration exposes a non-live follower
immediately to the right of the new root. -/
structure ResetAwareZeroRootArrival
    (hpsi : psi > 0) (ring : DirectedRing n) (root : Fin n)
    (C : EConfig n psi kappa tau) : Prop where
  no_active : NoActiveDeletion C
  unique_leader : hasUniqueLeader n
    (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig C)
  root_alive : (C root).core.erase.core.leader = true
  right_follower :
    (C (ring.rightNeighbor root)).core.erase.core.leader = false
  root_zero : (C root).core.erase.core.label = ⟨0, hpsi⟩
  protected_or_right_not_live :
    ((C root).core.erase.core.shield = true ∧
      (C root).core.erase.core.signal_B = ⟨0, by omega⟩) ∨
    (C (ring.rightNeighbor root)).core.erase.core.bullet ≠
      ⟨2, by omega⟩

set_option maxHeartbeats 1000000 in
/-- A completed normalized prefix of length at least one label period can move
any nonzero unique root backward to a zero-labelled offset.  The returned word
is a literal prefix of the standard counterclockwise chase and has length at
most `n - 1`. -/
theorem ResetAwareRetryDone.exists_reverseMigration_to_zero
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (leader : Fin n) (C : EConfig n psi kappa tau)
    (hdone : ResetAwareRetryDone hpsi ring leader C)
    (hpsiLe : psi ≤ n)
    (hrootNonzero : (C leader).core.erase.core.label ≠ ⟨0, hpsi⟩) :
    ∃ k, 0 < k ∧ k < n ∧
      let T :=
        wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
          hpsi kappa tau
      let word := pPsiProbeChasePrefix ring leader (n - k)
      let D := runLocalSchedule ring T C word
      word.length = n - k ∧
        NoActiveDeletion D ∧
        hasUniqueLeader n
          (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig D) ∧
        (D (groupOffset ring leader k)).core.erase.core.leader = true ∧
        PPLLPpsiLeaderCreationRepair.BulletTwoFreeAwayFrom D
          (groupOffset ring leader k) ∧
        (D (groupOffset ring leader k)).core.erase.core.label = ⟨0, hpsi⟩ ∧
        ∀ i, (D i).core.erase.core.label =
          (C i).core.erase.core.label := by
  obtain ⟨_base, hstate, hfree⟩ := hdone
  have hunique : hasUniqueLeader n
      (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig C) := by
    refine ⟨leader, hstate.leader_alive, ?_⟩
    intro i hi
    by_cases hie : i = leader
    · exact hie
    · have hiFollower := hstate.unique_leader i hie
      change (C i).core.erase.core.leader = true at hi
      rw [hiFollower] at hi
      contradiction
  have hperiod : psi ≤ (n - 1) + 1 := by omega
  obtain ⟨k, hkpos, hkle, hzero⟩ :=
    hstate.normalized_prefix.exists_positive_zero_of_root_nonzero
      hperiod hrootNonzero
  have hexists : ∃ k, 0 < k ∧ k < n ∧
      (C (groupOffset ring leader k)).core.erase.core.label =
        ⟨0, hpsi⟩ := ⟨k, hkpos, by omega, hzero⟩
  exact reverseMigration_to_zero_of_exists_offset
    hpsi ring hn leader C hstate.no_active hunique hstate.leader_alive
      hfree hrootNonzero hexists

set_option maxHeartbeats 1000000 in
/-- Full label-zero producer from the completed reset-aware prefix.  A root
already at label zero uses the empty word (`k = n`); otherwise the theorem
uses the greatest positive zero-labelled offset and the verified reverse
migration schedule. -/
theorem ResetAwareRetryDone.exists_reverseMigrationSchedule_to_zero
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (leader : Fin n) (C : EConfig n psi kappa tau)
    (hdone : ResetAwareRetryDone hpsi ring leader C)
    (hpsiLe : psi ≤ n) :
    ∃ k, 0 < k ∧ k ≤ n ∧
      let T :=
        wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
          hpsi kappa tau
      let word := pPsiProbeChasePrefix ring leader (n - k)
      let D := runLocalSchedule ring T C word
      word.length = n - k ∧
        NoActiveDeletion D ∧
        hasUniqueLeader n
          (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig D) ∧
        (D (groupOffset ring leader k)).core.erase.core.leader = true ∧
        PPLLPpsiLeaderCreationRepair.BulletTwoFreeAwayFrom D
          (groupOffset ring leader k) ∧
        (D (groupOffset ring leader k)).core.erase.core.label = ⟨0, hpsi⟩ ∧
        ∀ i, (D i).core.erase.core.label =
          (C i).core.erase.core.label := by
  by_cases hrootZero : (C leader).core.erase.core.label = ⟨0, hpsi⟩
  · obtain ⟨_base, hstate, hfree⟩ := hdone
    have hunique : hasUniqueLeader n
        (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig C) := by
      refine ⟨leader, hstate.leader_alive, ?_⟩
      intro i hi
      by_cases hie : i = leader
      · exact hie
      · have hiFollower := hstate.unique_leader i hie
        change (C i).core.erase.core.leader = true at hi
        rw [hiFollower] at hi
        contradiction
    refine ⟨n, by omega, Nat.le_refl n, ?_⟩
    simp only [Nat.sub_self, pPsiProbeChasePrefix, runLocalSchedule,
      List.length_nil]
    refine ⟨True.intro, hstate.no_active, hunique, ?_, ?_, ?_,
      fun _ => True.intro⟩
    · simpa using hstate.leader_alive
    · simpa using hfree
    · simpa using hrootZero
  · obtain ⟨k, hkpos, hklt, hresult⟩ :=
      hdone.exists_reverseMigration_to_zero
        hpsi ring hn leader C hpsiLe hrootZero
    exact ⟨k, hkpos, Nat.le_of_lt hklt, hresult⟩

set_option maxHeartbeats 1000000 in
/-- Birth-signal-transition form.  A completed normalized prefix of length at least one label period can move
any nonzero unique root backward to a zero-labelled offset.  The returned word
is a literal prefix of the standard counterclockwise chase and has length at
most `n - 1`. -/
theorem ResetAwareRetryDone.exists_birthSignalZero_reverseMigration_to_zero
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (leader : Fin n) (C : EConfig n psi kappa tau)
    (hdone : ResetAwareRetryDone hpsi ring leader C)
    (hpsiLe : psi ≤ n)
    (hrootNonzero : (C leader).core.erase.core.label ≠ ⟨0, hpsi⟩) :
    ∃ k, 0 < k ∧ k < n ∧
      let T :=
        wallSweepBirthSignalZeroPathStallTransition
          hpsi kappa tau
      let word := pPsiProbeChasePrefix ring leader (n - k)
      let D := runLocalSchedule ring T C word
      word.length = n - k ∧
        NoActiveDeletion D ∧
        hasUniqueLeader n
          (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig D) ∧
        (D (groupOffset ring leader k)).core.erase.core.leader = true ∧
        PPLLPpsiLeaderCreationRepair.BulletTwoFreeAwayFrom D
          (groupOffset ring leader k) ∧
        (D (groupOffset ring leader k)).core.erase.core.label = ⟨0, hpsi⟩ ∧
        ∀ i, (D i).core.erase.core.label =
          (C i).core.erase.core.label := by
  obtain ⟨_base, hstate, hfree⟩ := hdone
  have hunique : hasUniqueLeader n
      (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig C) := by
    refine ⟨leader, hstate.leader_alive, ?_⟩
    intro i hi
    by_cases hie : i = leader
    · exact hie
    · have hiFollower := hstate.unique_leader i hie
      change (C i).core.erase.core.leader = true at hi
      rw [hiFollower] at hi
      contradiction
  have hperiod : psi ≤ (n - 1) + 1 := by omega
  obtain ⟨k, hkpos, hkle, hzero⟩ :=
    hstate.normalized_prefix.exists_positive_zero_of_root_nonzero
      hperiod hrootNonzero
  have hexists : ∃ k, 0 < k ∧ k < n ∧
      (C (groupOffset ring leader k)).core.erase.core.label =
        ⟨0, hpsi⟩ := ⟨k, hkpos, by omega, hzero⟩
  exact reverseMigration_birthSignalZero_to_zero_of_exists_offset
    hpsi ring hn leader C hstate.no_active hunique hstate.leader_alive
      hfree hrootNonzero hexists

set_option maxHeartbeats 1000000 in
/-- Birth-signal-transition full label-zero producer from the completed reset-aware prefix.  A root
already at label zero uses the empty word (`k = n`); otherwise the theorem
uses the greatest positive zero-labelled offset and the verified reverse
migration schedule. -/
theorem ResetAwareRetryDone.exists_birthSignalZero_reverseMigrationSchedule_to_zero
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (leader : Fin n) (C : EConfig n psi kappa tau)
    (hdone : ResetAwareRetryDone hpsi ring leader C)
    (hpsiLe : psi ≤ n) :
    ∃ k, 0 < k ∧ k ≤ n ∧
      let T :=
        wallSweepBirthSignalZeroPathStallTransition
          hpsi kappa tau
      let word := pPsiProbeChasePrefix ring leader (n - k)
      let D := runLocalSchedule ring T C word
      word.length = n - k ∧
        NoActiveDeletion D ∧
        hasUniqueLeader n
          (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig D) ∧
        (D (groupOffset ring leader k)).core.erase.core.leader = true ∧
        PPLLPpsiLeaderCreationRepair.BulletTwoFreeAwayFrom D
          (groupOffset ring leader k) ∧
        (D (groupOffset ring leader k)).core.erase.core.label = ⟨0, hpsi⟩ ∧
        ∀ i, (D i).core.erase.core.label =
          (C i).core.erase.core.label := by
  by_cases hrootZero : (C leader).core.erase.core.label = ⟨0, hpsi⟩
  · obtain ⟨_base, hstate, hfree⟩ := hdone
    have hunique : hasUniqueLeader n
        (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig C) := by
      refine ⟨leader, hstate.leader_alive, ?_⟩
      intro i hi
      by_cases hie : i = leader
      · exact hie
      · have hiFollower := hstate.unique_leader i hie
        change (C i).core.erase.core.leader = true at hi
        rw [hiFollower] at hi
        contradiction
    refine ⟨n, by omega, Nat.le_refl n, ?_⟩
    simp only [Nat.sub_self, pPsiProbeChasePrefix, runLocalSchedule,
      List.length_nil]
    refine ⟨True.intro, hstate.no_active, hunique, ?_, ?_, ?_,
      fun _ => True.intro⟩
    · simpa using hstate.leader_alive
    · simpa using hfree
    · simpa using hrootZero
  · obtain ⟨k, hkpos, hklt, hresult⟩ :=
      hdone.exists_birthSignalZero_reverseMigration_to_zero
        hpsi ring hn leader C hpsiLe hrootZero
    exact ⟨k, hkpos, Nat.le_of_lt hklt, hresult⟩

/-- Exact fields established immediately before the closing
predecessor-to-leader edge.  This intentionally omits the four fields that the
current traversal does not establish: a zero leader label, a returned absence
signal, exact bullet values, and a shield value. -/
structure ResetAwareClosingCore
    (hpsi : psi > 0) (ring : DirectedRing n) (leader : Fin n)
    (C : EConfig n psi kappa tau) : Prop where
  no_active : NoActiveDeletion C
  leader_alive : (C leader).core.erase.core.leader = true
  unique_leader : ∀ i, i ≠ leader →
    (C i).core.erase.core.leader = false
  successor_label_of_right_ne : ∀ i,
    ring.rightNeighbor i ≠ leader →
      (C (ring.rightNeighbor i)).core.erase.core.label =
        ⟨((C i).core.erase.core.label.val + 1) % psi,
          Nat.mod_lt _ hpsi⟩
  no_free_barrier : noFreeBarrier hpsi ring
    (fun i => (C i).core.erase.core)
  comparison_neutral : ∀ i,
    ComparisonNeutral (C i).core.erase.core
  predecessor_reset :
    (C (groupOffset ring leader (n - 1))).core.erase.core.reset_cmd = true
  reset_false_off_predecessor : ∀ i,
    i ≠ groupOffset ring leader (n - 1) →
      (C i).core.erase.core.reset_cmd = false
  bullet_two_free_away :
    PPLLPpsiLeaderCreationRepair.BulletTwoFreeAwayFrom C leader

/-- Exact additional endpoint payload needed to turn the reset-aware
non-wrap completion into the rooted closing edge.  Separating it from
`ResetAwareClosingCore` records the current proof boundary: the rank scheduler
already establishes the structural core, while these endpoint payload facts
must be transported from a stronger retry invariant rather than inferred
from `ResetAwareRetryDone`. -/
structure ResetAwareRootedClosingReady
    (hpsi : psi > 0) (ring : DirectedRing n) (leader : Fin n)
    (C : EConfig n psi kappa tau) : Prop
    extends ResetAwareClosingCore hpsi ring leader C where
  leader_zero : (C leader).core.erase.core.label = ⟨0, hpsi⟩
  predecessor_signal_one :
    (C (groupOffset ring leader (n - 1))).core.erase.core.signal_B =
      ⟨1, by omega⟩

/-- Weak post-closing boundary consumed by the outgoing leader fire.  Reset,
echo, bullet, and pre-existing shield values are deliberately absent because
the fire proof uses only rooted geometry, comparison neutrality, and the
returned signal. -/
structure ResetAwareLeaderFireReady
    (hpsi : psi > 0) (ring : DirectedRing n) (leader : Fin n)
    (C : EConfig n psi kappa tau) : Prop
    extends RootedRetryGeometry hpsi ring leader C where
  comparison_neutral : ∀ i,
    ComparisonNeutral (C i).core.erase.core
  leader_signal_one :
    (C leader).core.erase.core.signal_B = ⟨1, by omega⟩

/-- A completed non-wrap retry prefix exposes exactly the structural closing
core above.  The proof uses clockwise distance only to enumerate the already
visited prefix; it adds no terminal signal, label-zero, bullet-zero, or shield
assumption. -/
theorem ResetAwareRetryDone.toClosingCore
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (leader : Fin n) (C : EConfig n psi kappa tau)
    (hdone : ResetAwareRetryDone hpsi ring leader C) :
    ResetAwareClosingCore hpsi ring leader C := by
  obtain ⟨_base, hstate, hfree⟩ := hdone
  have hsuccessor : ∀ i, ring.rightNeighbor i ≠ leader →
      (C (ring.rightNeighbor i)).core.erase.core.label =
        ⟨((C i).core.erase.core.label.val + 1) % psi,
          Nat.mod_lt _ hpsi⟩ := by
    intro i hright
    let k := cwDist ring leader i
    have hkBound : k < n := cwDist_lt ring leader i
    have hpos : groupOffset ring leader k = i := by
      simpa [groupOffset, cwPos] using cwPos_cwDist ring leader i
    have hkLast : k ≠ n - 1 := by
      intro hk
      apply hright
      rw [← hpos, hk, rightNeighbor_groupOffset]
      have hnEq : n - 1 + 1 = n := by omega
      rw [hnEq, groupOffset_n_eq]
    have hkPrefix : k < n - 1 := by omega
    rw [← hpos, rightNeighbor_groupOffset]
    exact hstate.normalized_prefix k hkPrefix
  exact {
    no_active := hstate.no_active
    leader_alive := hstate.leader_alive
    unique_leader := hstate.unique_leader
    successor_label_of_right_ne := hsuccessor
    no_free_barrier := by
      intro i
      dsimp only
      intro hbarrier
      by_cases hright : ring.rightNeighbor i = leader
      · rw [hright]
        exact hstate.leader_alive
      · exact (hbarrier (hsuccessor i hright)).elim
    comparison_neutral := by
      intro i
      let k := cwDist ring leader i
      have hkBound : k < n := cwDist_lt ring leader i
      have hpos : groupOffset ring leader k = i := by
        simpa [groupOffset, cwPos] using cwPos_cwDist ring leader i
      rw [← hpos]
      exact hstate.visited_neutral k (by omega) (by omega)
    predecessor_reset := hstate.frontier_reset
    reset_false_off_predecessor := by
      intro i hi
      let k := cwDist ring leader i
      have hkBound : k < n := cwDist_lt ring leader i
      have hpos : groupOffset ring leader k = i := by
        simpa [groupOffset, cwPos] using cwPos_cwDist ring leader i
      have hkLast : k ≠ n - 1 := by
        intro hk
        apply hi
        rw [← hpos, hk]
      rw [← hpos]
      exact hstate.reset_behind k (by omega)
    bullet_two_free_away := hfree }

/-- Directly reusing the old closing core after moving its leader is impossible
on a nondivisible ring.  Since reverse migration preserves labels, every old
non-wrap edge remains consecutive.  If the old root has become a follower and
the new configuration also had no free barrier, the old wrap edge would be
forced consecutive as well, contradicting `psi ∤ n`. -/
theorem noFreeBarrier_false_of_label_frame_and_old_root_follower
    (hpsi : psi > 0) (ring : DirectedRing n)
    (hndvd : ¬ psi ∣ n)
    (oldRoot : Fin n) (C D : EConfig n psi kappa tau)
    (hcore : ResetAwareClosingCore hpsi ring oldRoot C)
    (hlabels : ∀ i, (D i).core.erase.core.label =
      (C i).core.erase.core.label)
    (holdFollower : (D oldRoot).core.erase.core.leader = false) :
    ¬ noFreeBarrier hpsi ring (fun i => (D i).core.erase.core) := by
  intro hfree
  apply hndvd
  apply dvd_of_all_successor_labels hpsi ring
    (fun i => (D i).core.erase.core)
  intro i
  by_cases hright : ring.rightNeighbor i = oldRoot
  · apply successor_label_of_noFreeBarrier_of_right_not_leader
      hpsi ring (fun x => (D x).core.erase.core) hfree i
    change ¬ (D (ring.rightNeighbor i)).core.erase.core.leader = true
    rw [hright, holdFollower]
    simp
  · rw [hlabels (ring.rightNeighbor i), hlabels i]
    exact hcore.successor_label_of_right_ne i hright

/-- In particular, every nonempty reverse migration away from a nondivisible
closing root falsifies that root's no-free-barrier boundary.  A second
normalization pass (or another label-changing repair) is therefore mandatory
before the close/fire consumer can be reused. -/
theorem noFreeBarrier_false_of_nonempty_reverseMigration
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (hndvd : ¬ psi ∣ n)
    (oldRoot : Fin n) (C D : EConfig n psi kappa tau)
    (k : Nat) (hkpos : 0 < k) (hklt : k < n)
    (hcore : ResetAwareClosingCore hpsi ring oldRoot C)
    (hlabels : ∀ i, (D i).core.erase.core.label =
      (C i).core.erase.core.label)
    (hunique : hasUniqueLeader n
      (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig D))
    (hnewLeader :
      (D (groupOffset ring oldRoot k)).core.erase.core.leader = true) :
    ¬ noFreeBarrier hpsi ring (fun i => (D i).core.erase.core) := by
  have hnewNeZero : groupOffset ring oldRoot k ≠
      groupOffset ring oldRoot 0 :=
    groupOffset_ne_of_lt ring oldRoot hklt
      (by omega : 0 < n) (by omega : k ≠ 0)
  have hnewNe : groupOffset ring oldRoot k ≠ oldRoot := by
    intro hbad
    apply hnewNeZero
    rw [hbad, groupOffset_zero_eq]
  obtain ⟨onlyRoot, _honlyAlive, honly⟩ := hunique
  have hnewEq : groupOffset ring oldRoot k = onlyRoot := by
    apply honly
    exact hnewLeader
  have holdFollower : (D oldRoot).core.erase.core.leader = false := by
    cases hold : (D oldRoot).core.erase.core.leader with
    | false => rfl
    | true =>
        have holdEq : oldRoot = onlyRoot := by
          apply honly
          exact hold
        have hbad : groupOffset ring oldRoot k = oldRoot :=
          hnewEq.trans holdEq.symm
        exact (hnewNe hbad).elim
  exact noFreeBarrier_false_of_label_frame_and_old_root_follower
    hpsi ring hndvd oldRoot C D hcore hlabels holdFollower

/-- The authenticated outgoing reset frontier is exactly the length-one
normalized-prefix state. -/
theorem resetAwareNormalizedPrefixState_one
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (leader : Fin n) (C : EConfig n psi kappa tau)
    (hnoActive : NoActiveDeletion C)
    (hleader : (C leader).core.erase.core.leader = true)
    (hunique : ∀ i, i ≠ leader →
      (C i).core.erase.core.leader = false)
    (hrightLabel :
      (C (ring.rightNeighbor leader)).core.erase.core.label =
        ⟨((C leader).core.erase.core.label.val + 1) % psi,
          Nat.mod_lt _ hpsi⟩)
    (hleftNeutral : ComparisonNeutral (C leader).core.erase.core)
    (hrightNeutral : ComparisonNeutral
      (C (ring.rightNeighbor leader)).core.erase.core)
    (hleftReset : (C leader).core.erase.core.reset_cmd = false)
    (hrightReset :
      (C (ring.rightNeighbor leader)).core.erase.core.reset_cmd = true) :
    ResetAwareNormalizedPrefixState hpsi ring leader C C 1 := by
  have hoffsetZero : groupOffset ring leader 0 = leader :=
    groupOffset_zero_eq ring leader
  have hoffsetOne : groupOffset ring leader 1 =
      ring.rightNeighbor leader := by
    have hneighbor := rightNeighbor_groupOffset ring leader 0
    rw [hoffsetZero] at hneighbor
    simpa using hneighbor.symm
  exact {
    steps_pos := by omega
    steps_le := by omega
    no_active := hnoActive
    leader_alive := hleader
    unique_leader := hunique
    frontier_reset := by simpa [hoffsetOne] using hrightReset
    normalized_prefix := by
      intro k hk
      have hkzero : k = 0 := by omega
      subst k
      simpa [hoffsetZero, hoffsetOne] using hrightLabel
    visited_neutral := by
      intro k hk _
      by_cases hkzero : k = 0
      · subst k
        simpa [hoffsetZero] using hleftNeutral
      · have hkone : k = 1 := by omega
        subst k
        simpa [hoffsetOne] using hrightNeutral
    untouched_ahead := by
      intro k _ _
      rfl
    reset_behind := by
      intro k hk
      have hkzero : k = 0 := by omega
      subst k
      simpa [hoffsetZero] using hleftReset }

/-- The named reset-frontier certificate is exactly the data needed to start
a fresh length-one normalized prefix at that same leader. -/
theorem resetAwareNormalizedPrefixState_one_of_frontierAt
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (leader : Fin n) (C : EConfig n psi kappa tau)
    (hfrontier :
      PPLLPpsiLeaderCreationRepair.OutgoingResetFrontierUniqueLeaderAt
        hpsi ring C leader) :
    ResetAwareNormalizedPrefixState hpsi ring leader C C 1 := by
  obtain ⟨hnoActive, hunique, hleader, _hrightFollower,
      hrightLabel, _hleftProbe, _hrightProbe,
      hleftNeutral, hrightNeutral, hleftReset, hrightReset,
      _hleftEcho, _hrightEcho, _hsafe⟩ := hfrontier
  obtain ⟨only, _honlyLeader, honly⟩ := hunique
  have hleaderOnly : leader = only := by
    apply honly leader
    change (C leader).core.erase.core.leader = true
    exact hleader
  have hpointwise : ∀ i, i ≠ leader →
      (C i).core.erase.core.leader = false := by
    intro i hine
    cases hi : (C i).core.erase.core.leader with
    | false => rfl
    | true =>
        have hiOnly : i = only := by
          apply honly i
          change (C i).core.erase.core.leader = true
          exact hi
        exact (hine (hiOnly.trans hleaderOnly.symm)).elim
  exact resetAwareNormalizedPrefixState_one
    hpsi ring hn leader C hnoActive hleader hpointwise
      hrightLabel hleftNeutral hrightNeutral hleftReset hrightReset

set_option maxHeartbeats 2000000 in
/-- If the next untouched responder echo is false, one reset-aware follower
step grows the normalized prefix by one.  A true echo is excluded here because
that case consumes reset and belongs to the separate strict echo-rank retry
branch. -/
theorem ResetAwareNormalizedPrefixState.step_of_echo_false
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (leader : Fin n) (base current : EConfig n psi kappa tau)
    (steps : Nat)
    (hstate : ResetAwareNormalizedPrefixState
      hpsi ring leader base current steps)
    (hlt : steps < n - 1)
    (hrightEcho :
      (current (groupOffset ring leader (steps + 1))).core.erase.core.echo =
        false) :
    let D := localStep ring
      (wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
        hpsi kappa tau) current (groupOffset ring leader steps)
    ResetAwareNormalizedPrefixState
      hpsi ring leader base D (steps + 1) := by
  let e := groupOffset ring leader steps
  let j := groupOffset ring leader (steps + 1)
  let T := wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
    hpsi kappa tau
  let D := localStep ring T current e
  have hnpos : 0 < n := by omega
  have heBound : steps < n := by omega
  have hjBound : steps + 1 < n := by omega
  have hneighbor : ring.rightNeighbor e = j := by
    simpa [e, j] using rightNeighbor_groupOffset ring leader steps
  have heNotLeader : e ≠ leader := by
    have hne := groupOffset_ne_of_lt ring leader heBound
      hnpos (Nat.ne_of_gt hstate.steps_pos)
    exact fun heq =>
      hne (heq.trans (groupOffset_zero_eq ring leader).symm)
  have hjNotLeader : j ≠ leader := by
    have hne := groupOffset_ne_of_lt ring leader hjBound
      hnpos (Nat.ne_of_gt (Nat.zero_lt_succ steps))
    exact fun heq =>
      hne (heq.trans (groupOffset_zero_eq ring leader).symm)
  have hstep := resetAwareFollower_localStep_normalizes
    hpsi ring hn current e hstate.no_active
      (hstate.unique_leader e heNotLeader) hstate.frontier_reset
      (by rw [hneighbor]; exact hstate.unique_leader j hjNotLeader)
  change ResetAwareFollowerGlobalStepFrame hpsi ring current D e at hstep
  have hpair : ExpiringResetFollowerNormalizedOutput hpsi
      (current e, current j) (D e, D j) := by
    simpa [hneighbor] using hstep.normalized
  have hoff : ∀ i, i ≠ e → i ≠ j → D i = current i := by
    intro i hie hij
    apply hstep.off_edge i hie
    rwa [hneighbor]
  have hleaderAliveD : (D leader).core.erase.core.leader = true :=
    (hstep.leader_eq leader).trans hstate.leader_alive
  have huniqueD : ∀ i, i ≠ leader →
      (D i).core.erase.core.leader = false := by
    intro i hi
    exact (hstep.leader_eq i).trans (hstate.unique_leader i hi)
  have hfrontierReset :
      (D j).core.erase.core.reset_cmd = true := by
    simpa [j, hrightEcho] using hpair.control.right_reset_exact
  have hprefix :
      NormalizedClockwisePrefix hpsi ring leader D (steps + 1) := by
    intro k hk
    by_cases hnew : k = steps
    · subst k
      calc
        (D (groupOffset ring leader (steps + 1))).core.erase.core.label =
            ⟨((current (groupOffset ring leader steps)).core.erase.core.label.val + 1) %
                psi,
              Nat.mod_lt _ hpsi⟩ := by
          simpa [e, j] using hpair.right_successor
        _ = ⟨((D (groupOffset ring leader steps)).core.erase.core.label.val + 1) %
                psi,
              Nat.mod_lt _ hpsi⟩ := by
          rw [show (D (groupOffset ring leader steps)).core.erase.core.label =
              (current (groupOffset ring leader steps)).core.erase.core.label by
            simpa [e] using hpair.left_label]
    · have hkold : k < steps := by omega
      have hold := hstate.normalized_prefix k hkold
      have hkBound : k < n := by omega
      have hk1Bound : k + 1 < n := by omega
      have hke : groupOffset ring leader k ≠ e := by
        apply groupOffset_ne_of_lt ring leader hkBound heBound
        omega
      have hkj : groupOffset ring leader k ≠ j := by
        apply groupOffset_ne_of_lt ring leader hkBound hjBound
        omega
      by_cases hk1 : k + 1 = steps
      · have hleftFrame :
            (D (groupOffset ring leader (k + 1))).core.erase.core.label =
              (current (groupOffset ring leader (k + 1))).core.erase.core.label := by
          rw [hk1]
          simpa [e] using hpair.left_label
        have hkFrame := hstep.off_edge
          (groupOffset ring leader k) hke (by rwa [hneighbor])
        rw [hleftFrame]
        simpa only [hkFrame] using hold
      · have hk1e : groupOffset ring leader (k + 1) ≠ e := by
          apply groupOffset_ne_of_lt ring leader hk1Bound heBound
          omega
        have hk1j : groupOffset ring leader (k + 1) ≠ j := by
          apply groupOffset_ne_of_lt ring leader hk1Bound hjBound
          omega
        have hk1Frame := hoff _ hk1e hk1j
        have hkFrame := hoff _ hke hkj
        simpa only [hk1Frame, hkFrame] using hold
  have hvisited : VisitedPrefixNeutral ring leader D (steps + 1) :=
    visitedPrefixNeutral_succ ring leader current D steps hjBound
      hstate.visited_neutral hpair.control.left_neutral
      hpair.control.right_neutral (by simpa [e, j] using hoff)
  have hahead : UntouchedAhead ring leader base D (steps + 1) :=
    untouchedAhead_succ ring leader base current D steps hjBound
      hstate.untouched_ahead (by simpa [e, j] using hoff)
  have hresetBehind : ∀ k, k < steps + 1 →
      (D (groupOffset ring leader k)).core.erase.core.reset_cmd = false := by
    intro k hk
    by_cases hfront : k = steps
    · subst k
      simpa [e] using hpair.control.left_reset_false
    · have hkold : k < steps := by omega
      have hkBound : k < n := by omega
      have hke : groupOffset ring leader k ≠ e := by
        apply groupOffset_ne_of_lt ring leader hkBound heBound
        omega
      have hkj : groupOffset ring leader k ≠ j := by
        apply groupOffset_ne_of_lt ring leader hkBound hjBound
        omega
      rw [hoff _ hke hkj]
      exact hstate.reset_behind k hkold
  change ResetAwareNormalizedPrefixState
    hpsi ring leader base D (steps + 1)
  exact {
    steps_pos := by omega
    steps_le := by omega
    no_active := hstep.no_active
    leader_alive := hleaderAliveD
    unique_leader := huniqueD
    frontier_reset := by simpa [j] using hfrontierReset
    normalized_prefix := hprefix
    visited_neutral := hvisited
    untouched_ahead := hahead
    reset_behind := hresetBehind }

/-- Every non-wrap normalized follower step is a uniform B-step: the old
transition keeps the same named unique leader, hence the birth-signal wrapper
is exactly inert independently of the follower's echo or live-bullet fields. -/
theorem ResetAwareNormalizedPrefixState.localStep_birthSignalZero_eq_resetProbe
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (leader : Fin n) (base current : EConfig n psi kappa tau)
    (steps : Nat)
    (hstate : ResetAwareNormalizedPrefixState
      hpsi ring leader base current steps)
    (hlt : steps < n - 1) :
    localStep ring
        (wallSweepBirthSignalZeroPathStallTransition
          hpsi kappa tau) current (groupOffset ring leader steps) =
      localStep ring
        (wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
          hpsi kappa tau) current (groupOffset ring leader steps) := by
  let e := groupOffset ring leader steps
  let j := groupOffset ring leader (steps + 1)
  let Told :=
    wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
      hpsi kappa tau
  let Dold := localStep ring Told current e
  have hnpos : 0 < n := by omega
  have heBound : steps < n := by omega
  have hjBound : steps + 1 < n := by omega
  have hneighbor : ring.rightNeighbor e = j := by
    simpa [e, j] using rightNeighbor_groupOffset ring leader steps
  have heNotLeader : e ≠ leader := by
    have hne := groupOffset_ne_of_lt ring leader heBound
      hnpos (Nat.ne_of_gt hstate.steps_pos)
    exact fun heq =>
      hne (heq.trans (groupOffset_zero_eq ring leader).symm)
  have hjNotLeader : j ≠ leader := by
    have hne := groupOffset_ne_of_lt ring leader hjBound
      hnpos (Nat.ne_of_gt (Nat.zero_lt_succ steps))
    exact fun heq =>
      hne (heq.trans (groupOffset_zero_eq ring leader).symm)
  have hstep := resetAwareFollower_localStep_normalizes
    hpsi ring hn current e hstate.no_active
      (hstate.unique_leader e heNotLeader) hstate.frontier_reset
      (by rw [hneighbor]; exact hstate.unique_leader j hjNotLeader)
  change ResetAwareFollowerGlobalStepFrame hpsi ring current Dold e at hstep
  have hleaderD : (Dold leader).core.erase.core.leader = true :=
    (hstep.leader_eq leader).trans hstate.leader_alive
  have huniqueD : hasUniqueLeader n
      (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig Dold) := by
    refine ⟨leader, hleaderD, ?_⟩
    intro i hi
    by_cases hil : i = leader
    · exact hil
    · have hfalse := (hstep.leader_eq i).trans
          (hstate.unique_leader i hil)
      change (Dold i).core.erase.core.leader = true at hi
      rw [hfalse] at hi
      contradiction
  simpa only [Dold, Told, e] using
    localStep_birthSignalZero_eq_resetProbe_of_fixed_unique_leader
      hpsi ring hn current e leader hstate.leader_alive
        huniqueD hleaderD

/-- Birth-signal-transition form of the normalized follower step.  The old
step retains the same named unique leader, so the uniform one-step transport
proves exact equality before reusing the established prefix contract. -/
theorem ResetAwareNormalizedPrefixState.step_birthSignalZero_of_echo_false
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (leader : Fin n) (base current : EConfig n psi kappa tau)
    (steps : Nat)
    (hstate : ResetAwareNormalizedPrefixState
      hpsi ring leader base current steps)
    (hlt : steps < n - 1)
    (hrightEcho :
      (current (groupOffset ring leader (steps + 1))).core.erase.core.echo =
        false) :
    let D := localStep ring
      (wallSweepBirthSignalZeroPathStallTransition
        hpsi kappa tau) current (groupOffset ring leader steps)
    ResetAwareNormalizedPrefixState
      hpsi ring leader base D (steps + 1) := by
  let e := groupOffset ring leader steps
  let Told :=
    wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
      hpsi kappa tau
  let Tnew := wallSweepBirthSignalZeroPathStallTransition
    hpsi kappa tau
  let Dold := localStep ring Told current e
  let Dnew := localStep ring Tnew current e
  have hstateOld := hstate.step_of_echo_false
    hpsi ring hn leader base current steps hlt hrightEcho
  change ResetAwareNormalizedPrefixState
    hpsi ring leader base Dold (steps + 1) at hstateOld
  have huniqueOld : hasUniqueLeader n
      (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig Dold) := by
    refine ⟨leader, hstateOld.leader_alive, ?_⟩
    intro i hi
    by_cases hil : i = leader
    · exact hil
    · have hfalse := hstateOld.unique_leader i hil
      change (Dold i).core.erase.core.leader = true at hi
      rw [hfalse] at hi
      contradiction
  have heq : Dnew = Dold := by
    simpa only [Dnew, Dold, Tnew, Told, e] using
      localStep_birthSignalZero_eq_resetProbe_of_fixed_unique_leader
        hpsi ring hn current e leader hstate.leader_alive
          huniqueOld hstateOld.leader_alive
  change ResetAwareNormalizedPrefixState
    hpsi ring leader base Dnew (steps + 1)
  rw [heq]
  exact hstateOld

set_option maxHeartbeats 2000000 in
/-- Advance a normalized prefix across false base echoes without any global
live-bullet-freedom premise.  Every scheduled follower edge is away from the
root, so the complete root state is framed, while the global live count is
nonincreasing. -/
theorem
    ResetAwareNormalizedPrefixState.exists_advance_to_of_base_echo_false_unrestricted
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (leader : Fin n) (base current : EConfig n psi kappa tau)
    (steps target : Nat)
    (hstate : ResetAwareNormalizedPrefixState
      hpsi ring leader base current steps)
    (hsteps : steps ≤ target) (htarget : target ≤ n - 1)
    (hbaseEcho : ∀ k, steps < k → k ≤ target →
      (base (groupOffset ring leader k)).core.erase.core.echo = false) :
    ∃ (word : DetSchedule n) (D : EConfig n psi kappa tau),
      D = runLocalSchedule ring
        (wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
          hpsi kappa tau) current word ∧
      word.length = target - steps ∧
      ResetAwareNormalizedPrefixState
        hpsi ring leader base D target ∧
      D leader = current leader ∧
      PPLLPpsiLeaderCreationRepair.bulletTwoCount D ≤
        PPLLPpsiLeaderCreationRepair.bulletTwoCount current := by
  induction target generalizing current steps with
  | zero =>
      have hzero : steps = 0 := by omega
      exact (Nat.ne_of_gt hstate.steps_pos hzero).elim
  | succ target ih =>
      by_cases hdone : steps = target + 1
      · subst steps
        refine ⟨[], current, by simp [runLocalSchedule], by simp,
          hstate, rfl, Nat.le_refl _⟩
      · have hstepsPrev : steps ≤ target := by omega
        have htargetPrev : target ≤ n - 1 := by omega
        obtain ⟨word, M, hM, hwordLength, hstateM, hleaderM,
            hcountM⟩ :=
          ih (current := current) (steps := steps)
            hstate hstepsPrev htargetPrev (by
              intro k hk hkt
              exact hbaseEcho k hk (by omega))
        have htargetPos : 0 < target := hstateM.steps_pos
        have htargetLt : target < n - 1 := by omega
        have hnextEcho :
            (M (groupOffset ring leader (target + 1))).core.erase.core.echo =
              false := by
          rw [hstateM.untouched_ahead (target + 1)
            (by omega) (by omega)]
          exact hbaseEcho (target + 1) (by omega) (by omega)
        let e := groupOffset ring leader target
        let T :=
          wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
            hpsi kappa tau
        let D := localStep ring T M e
        have hstateD := hstateM.step_of_echo_false
          hpsi ring hn leader base M target htargetLt hnextEcho
        change ResetAwareNormalizedPrefixState
          hpsi ring leader base D (target + 1) at hstateD
        have heBound : target < n := by omega
        have hjBound : target + 1 < n := by omega
        have heNotLeader : e ≠ leader := by
          intro heq
          have hne := groupOffset_ne_of_lt ring leader heBound
            (by omega : 0 < n) (Nat.ne_of_gt htargetPos)
          exact hne (heq.trans (groupOffset_zero_eq ring leader).symm)
        have hjNotLeader :
            groupOffset ring leader (target + 1) ≠ leader := by
          intro heq
          have hne := groupOffset_ne_of_lt ring leader hjBound
            (by omega : 0 < n) (by omega : target + 1 ≠ 0)
          exact hne (heq.trans (groupOffset_zero_eq ring leader).symm)
        have hneighbor : ring.rightNeighbor e =
            groupOffset ring leader (target + 1) := by
          simpa [e] using rightNeighbor_groupOffset ring leader target
        have hrightFollower :
            (M (ring.rightNeighbor e)).core.erase.core.leader = false := by
          rw [hneighbor]
          exact hstateM.unique_leader
            (groupOffset ring leader (target + 1)) hjNotLeader
        have hleaderFrame : D leader = M leader := by
          simp [D, T, localStep, Ne.symm heNotLeader, hneighbor,
            Ne.symm hjNotLeader]
        have hcountStep := resetAwareFollower_localStep_bulletTwoCount_le
          hpsi ring hn M e hstateM.no_active
            (hstateM.unique_leader e heNotLeader) hstateM.frontier_reset
            hrightFollower
        change PPLLPpsiLeaderCreationRepair.bulletTwoCount D ≤
          PPLLPpsiLeaderCreationRepair.bulletTwoCount M at hcountStep
        refine ⟨word ++ [e], D, ?_, ?_, hstateD,
          hleaderFrame.trans hleaderM, Nat.le_trans hcountStep hcountM⟩
        · calc
            D = runLocalSchedule ring T M [e] := rfl
            _ = runLocalSchedule ring T
                (runLocalSchedule ring T current word) [e] := by rw [← hM]
            _ = runLocalSchedule ring T current (word ++ [e]) :=
              (runLocalSchedule_append_generic
                ring T current word [e]).symm
        · simp only [List.length_append, List.length_cons, List.length_nil]
          omega

set_option maxHeartbeats 2000000 in
/-- Birth-signal-transition lift of the unrestricted false-echo prefix
advance.  The only changed proof ingredient is the transported follower step;
the unconditional birth frame supplies the old live-count bound. -/
theorem
    ResetAwareNormalizedPrefixState.exists_birthSignalZero_advance_to_of_base_echo_false_unrestricted
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (leader : Fin n) (base current : EConfig n psi kappa tau)
    (steps target : Nat)
    (hstate : ResetAwareNormalizedPrefixState
      hpsi ring leader base current steps)
    (hsteps : steps ≤ target) (htarget : target ≤ n - 1)
    (hbaseEcho : ∀ k, steps < k → k ≤ target →
      (base (groupOffset ring leader k)).core.erase.core.echo = false) :
    ∃ (word : DetSchedule n) (D : EConfig n psi kappa tau),
      D = runLocalSchedule ring
        (wallSweepBirthSignalZeroPathStallTransition
          hpsi kappa tau) current word ∧
      word.length = target - steps ∧
      ResetAwareNormalizedPrefixState
        hpsi ring leader base D target ∧
      D leader = current leader ∧
      PPLLPpsiLeaderCreationRepair.bulletTwoCount D ≤
        PPLLPpsiLeaderCreationRepair.bulletTwoCount current := by
  induction target generalizing current steps with
  | zero =>
      have hzero : steps = 0 := by omega
      exact (Nat.ne_of_gt hstate.steps_pos hzero).elim
  | succ target ih =>
      by_cases hdone : steps = target + 1
      · subst steps
        refine ⟨[], current, by simp [runLocalSchedule], by simp,
          hstate, rfl, Nat.le_refl _⟩
      · have hstepsPrev : steps ≤ target := by omega
        have htargetPrev : target ≤ n - 1 := by omega
        obtain ⟨word, M, hM, hwordLength, hstateM, hleaderM,
            hcountM⟩ :=
          ih (current := current) (steps := steps)
            hstate hstepsPrev htargetPrev (by
              intro k hk hkt
              exact hbaseEcho k hk (by omega))
        have htargetPos : 0 < target := hstateM.steps_pos
        have htargetLt : target < n - 1 := by omega
        have hnextEcho :
            (M (groupOffset ring leader (target + 1))).core.erase.core.echo =
              false := by
          rw [hstateM.untouched_ahead (target + 1)
            (by omega) (by omega)]
          exact hbaseEcho (target + 1) (by omega) (by omega)
        let e := groupOffset ring leader target
        let Tnew := wallSweepBirthSignalZeroPathStallTransition
          hpsi kappa tau
        let Told :=
          wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
            hpsi kappa tau
        let D := localStep ring Tnew M e
        let Dold := localStep ring Told M e
        have hstateD := hstateM.step_birthSignalZero_of_echo_false
          hpsi ring hn leader base M target htargetLt hnextEcho
        change ResetAwareNormalizedPrefixState
          hpsi ring leader base D (target + 1) at hstateD
        have heBound : target < n := by omega
        have hjBound : target + 1 < n := by omega
        have heNotLeader : e ≠ leader := by
          intro heq
          have hne := groupOffset_ne_of_lt ring leader heBound
            (by omega : 0 < n) (Nat.ne_of_gt htargetPos)
          exact hne (heq.trans (groupOffset_zero_eq ring leader).symm)
        have hjNotLeader :
            groupOffset ring leader (target + 1) ≠ leader := by
          intro heq
          have hne := groupOffset_ne_of_lt ring leader hjBound
            (by omega : 0 < n) (by omega : target + 1 ≠ 0)
          exact hne (heq.trans (groupOffset_zero_eq ring leader).symm)
        have hneighbor : ring.rightNeighbor e =
            groupOffset ring leader (target + 1) := by
          simpa [e] using rightNeighbor_groupOffset ring leader target
        have hrightFollower :
            (M (ring.rightNeighbor e)).core.erase.core.leader = false := by
          rw [hneighbor]
          exact hstateM.unique_leader
            (groupOffset ring leader (target + 1)) hjNotLeader
        have hleaderFrame : D leader = M leader := by
          simp [D, Tnew, localStep, Ne.symm heNotLeader, hneighbor,
            Ne.symm hjNotLeader]
        have hcountOld := resetAwareFollower_localStep_bulletTwoCount_le
          hpsi ring hn M e hstateM.no_active
            (hstateM.unique_leader e heNotLeader) hstateM.frontier_reset
            hrightFollower
        change PPLLPpsiLeaderCreationRepair.bulletTwoCount Dold ≤
          PPLLPpsiLeaderCreationRepair.bulletTwoCount M at hcountOld
        have hbirthFrame : BirthSignalConfigFrame Dold D := by
          simpa only [Dold, D, Told, Tnew] using
            localStep_birthSignalZero_frame hpsi ring M e
        have hcountStep : PPLLPpsiLeaderCreationRepair.bulletTwoCount D ≤
            PPLLPpsiLeaderCreationRepair.bulletTwoCount M := by
          rw [bulletTwoCount_eq_of_birthSignalConfigFrame hbirthFrame]
          exact hcountOld
        refine ⟨word ++ [e], D, ?_, ?_, hstateD,
          hleaderFrame.trans hleaderM, Nat.le_trans hcountStep hcountM⟩
        · calc
            D = runLocalSchedule ring Tnew M [e] := rfl
            _ = runLocalSchedule ring Tnew
                (runLocalSchedule ring Tnew current word) [e] := by rw [← hM]
            _ = runLocalSchedule ring Tnew current (word ++ [e]) :=
              (runLocalSchedule_append_generic
                ring Tnew current word [e]).symm
        · simp only [List.length_append, List.length_cons, List.length_nil]
          omega

/-- Advance a normalized prefix to any later non-wrap target whose intervening
base echoes are false.  The returned word is literal and has exactly one edge
per newly crossed prefix position. -/
theorem ResetAwareNormalizedPrefixState.exists_advance_to_of_base_echo_false
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (leader : Fin n) (base current : EConfig n psi kappa tau)
    (steps target : Nat)
    (hstate : ResetAwareNormalizedPrefixState
      hpsi ring leader base current steps)
    (hfree :
      PPLLPpsiLeaderCreationRepair.BulletTwoFreeAwayFrom current leader)
    (hsteps : steps ≤ target) (htarget : target ≤ n - 1)
    (hbaseEcho : ∀ k, steps < k → k ≤ target →
      (base (groupOffset ring leader k)).core.erase.core.echo = false) :
    ∃ (word : DetSchedule n) (D : EConfig n psi kappa tau),
      D = runLocalSchedule ring
        (wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
          hpsi kappa tau) current word ∧
      word.length = target - steps ∧
      ResetAwareNormalizedPrefixState
        hpsi ring leader base D target ∧
      PPLLPpsiLeaderCreationRepair.BulletTwoFreeAwayFrom D leader ∧
      (D leader).core.erase.core.label =
        (current leader).core.erase.core.label := by
  induction target generalizing current steps with
  | zero =>
      have hzero : steps = 0 := by omega
      exact (Nat.ne_of_gt hstate.steps_pos hzero).elim
  | succ target ih =>
      by_cases hdone : steps = target + 1
      · subst steps
        refine ⟨[], current, by simp [runLocalSchedule], by simp,
          hstate, hfree, rfl⟩
      · have hstepsPrev : steps ≤ target := by omega
        have htargetPrev : target ≤ n - 1 := by omega
        obtain ⟨word, M, hM, hwordLength, hstateM, hfreeM,
            hleaderLabelM⟩ :=
          ih (current := current) (steps := steps)
            hstate hfree hstepsPrev htargetPrev (by
              intro k hk hkt
              exact hbaseEcho k hk (by omega))
        have htargetPos : 0 < target := hstateM.steps_pos
        have htargetLt : target < n - 1 := by omega
        have hnextEcho :
            (M (groupOffset ring leader (target + 1))).core.erase.core.echo =
              false := by
          rw [hstateM.untouched_ahead (target + 1)
            (by omega) (by omega)]
          exact hbaseEcho (target + 1) (by omega) (by omega)
        let e := groupOffset ring leader target
        let T :=
          wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
            hpsi kappa tau
        let D := localStep ring T M e
        have hstateD := hstateM.step_of_echo_false
          hpsi ring hn leader base M target htargetLt hnextEcho
        change ResetAwareNormalizedPrefixState
          hpsi ring leader base D (target + 1) at hstateD
        have heBound : target < n := by omega
        have hjBound : target + 1 < n := by omega
        have heNotLeader : e ≠ leader := by
          intro heq
          have hne := groupOffset_ne_of_lt ring leader heBound
            (by omega : 0 < n) (Nat.ne_of_gt htargetPos)
          exact hne (heq.trans (groupOffset_zero_eq ring leader).symm)
        have hjNotLeader : groupOffset ring leader (target + 1) ≠ leader := by
          intro heq
          have hne := groupOffset_ne_of_lt ring leader hjBound
            (by omega : 0 < n) (by omega : target + 1 ≠ 0)
          exact hne (heq.trans (groupOffset_zero_eq ring leader).symm)
        have hneighbor : ring.rightNeighbor e =
            groupOffset ring leader (target + 1) := by
          simpa [e] using rightNeighbor_groupOffset ring leader target
        have hrightFollower :
            (M (ring.rightNeighbor e)).core.erase.core.leader = false := by
          rw [hneighbor]
          exact hstateM.unique_leader
            (groupOffset ring leader (target + 1)) hjNotLeader
        have hfreeD := resetAwareFollower_localStep_bulletTwoFreeAwayFrom
          hpsi ring hn M e leader hstateM.no_active
            (hstateM.unique_leader e heNotLeader) hstateM.frontier_reset
            hrightFollower
            hfreeM heNotLeader (by simpa [hneighbor] using hjNotLeader)
        change PPLLPpsiLeaderCreationRepair.BulletTwoFreeAwayFrom
          D leader at hfreeD
        have hleaderFrame : D leader = M leader := by
          simp [D, T, localStep, Ne.symm heNotLeader, hneighbor,
            Ne.symm hjNotLeader]
        have hleaderLabelD : (D leader).core.erase.core.label =
            (current leader).core.erase.core.label :=
          (congrArg
            (fun u : ExpiringAgentState psi kappa tau =>
              u.core.erase.core.label) hleaderFrame).trans hleaderLabelM
        refine ⟨word ++ [e], D, ?_, ?_, hstateD, hfreeD,
          hleaderLabelD⟩
        · calc
            D = runLocalSchedule ring T M [e] := rfl
            _ = runLocalSchedule ring T
                (runLocalSchedule ring T current word) [e] := by rw [← hM]
            _ = runLocalSchedule ring T current (word ++ [e]) :=
              (runLocalSchedule_append_generic
                ring T current word [e]).symm
        · simp only [List.length_append, List.length_cons, List.length_nil]
          omega

/-- Birth-signal-transition lift of the live-free false-echo prefix. -/
theorem ResetAwareNormalizedPrefixState.exists_birthSignalZero_advance_to_of_base_echo_false
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (leader : Fin n) (base current : EConfig n psi kappa tau)
    (steps target : Nat)
    (hstate : ResetAwareNormalizedPrefixState
      hpsi ring leader base current steps)
    (hfree :
      PPLLPpsiLeaderCreationRepair.BulletTwoFreeAwayFrom current leader)
    (hsteps : steps ≤ target) (htarget : target ≤ n - 1)
    (hbaseEcho : ∀ k, steps < k → k ≤ target →
      (base (groupOffset ring leader k)).core.erase.core.echo = false) :
    ∃ (word : DetSchedule n) (D : EConfig n psi kappa tau),
      D = runLocalSchedule ring
        (wallSweepBirthSignalZeroPathStallTransition
          hpsi kappa tau) current word ∧
      word.length = target - steps ∧
      ResetAwareNormalizedPrefixState
        hpsi ring leader base D target ∧
      PPLLPpsiLeaderCreationRepair.BulletTwoFreeAwayFrom D leader ∧
      (D leader).core.erase.core.label =
        (current leader).core.erase.core.label := by
  induction target generalizing current steps with
  | zero =>
      have hzero : steps = 0 := by omega
      exact (Nat.ne_of_gt hstate.steps_pos hzero).elim
  | succ target ih =>
      by_cases hdone : steps = target + 1
      · subst steps
        refine ⟨[], current, by simp [runLocalSchedule], by simp,
          hstate, hfree, rfl⟩
      · have hstepsPrev : steps ≤ target := by omega
        have htargetPrev : target ≤ n - 1 := by omega
        obtain ⟨word, M, hM, hwordLength, hstateM, hfreeM,
            hleaderLabelM⟩ :=
          ih (current := current) (steps := steps)
            hstate hfree hstepsPrev htargetPrev (by
              intro k hk hkt
              exact hbaseEcho k hk (by omega))
        have htargetPos : 0 < target := hstateM.steps_pos
        have htargetLt : target < n - 1 := by omega
        have hnextEcho :
            (M (groupOffset ring leader (target + 1))).core.erase.core.echo =
              false := by
          rw [hstateM.untouched_ahead (target + 1)
            (by omega) (by omega)]
          exact hbaseEcho (target + 1) (by omega) (by omega)
        let e := groupOffset ring leader target
        let T :=
          wallSweepBirthSignalZeroPathStallTransition
            hpsi kappa tau
        let Told :=
          wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
            hpsi kappa tau
        let D := localStep ring T M e
        let Dold := localStep ring Told M e
        have heq : D = Dold := by
          simpa only [D, Dold, T, Told, e] using
            hstateM.localStep_birthSignalZero_eq_resetProbe
              hpsi ring hn leader base M target htargetLt
        have hstateD := hstateM.step_birthSignalZero_of_echo_false
          hpsi ring hn leader base M target htargetLt hnextEcho
        change ResetAwareNormalizedPrefixState
          hpsi ring leader base D (target + 1) at hstateD
        have heBound : target < n := by omega
        have hjBound : target + 1 < n := by omega
        have heNotLeader : e ≠ leader := by
          intro heq
          have hne := groupOffset_ne_of_lt ring leader heBound
            (by omega : 0 < n) (Nat.ne_of_gt htargetPos)
          exact hne (heq.trans (groupOffset_zero_eq ring leader).symm)
        have hjNotLeader : groupOffset ring leader (target + 1) ≠ leader := by
          intro heq
          have hne := groupOffset_ne_of_lt ring leader hjBound
            (by omega : 0 < n) (by omega : target + 1 ≠ 0)
          exact hne (heq.trans (groupOffset_zero_eq ring leader).symm)
        have hneighbor : ring.rightNeighbor e =
            groupOffset ring leader (target + 1) := by
          simpa [e] using rightNeighbor_groupOffset ring leader target
        have hrightFollower :
            (M (ring.rightNeighbor e)).core.erase.core.leader = false := by
          rw [hneighbor]
          exact hstateM.unique_leader
            (groupOffset ring leader (target + 1)) hjNotLeader
        have hfreeOld := resetAwareFollower_localStep_bulletTwoFreeAwayFrom
          hpsi ring hn M e leader hstateM.no_active
            (hstateM.unique_leader e heNotLeader) hstateM.frontier_reset
            hrightFollower
            hfreeM heNotLeader (by simpa [hneighbor] using hjNotLeader)
        change PPLLPpsiLeaderCreationRepair.BulletTwoFreeAwayFrom
          Dold leader at hfreeOld
        have hfreeD :
            PPLLPpsiLeaderCreationRepair.BulletTwoFreeAwayFrom D leader := by
          rw [heq]
          exact hfreeOld
        have hleaderFrame : D leader = M leader := by
          simp [D, T, localStep, Ne.symm heNotLeader, hneighbor,
            Ne.symm hjNotLeader]
        have hleaderLabelD : (D leader).core.erase.core.label =
            (current leader).core.erase.core.label :=
          (congrArg
            (fun u : ExpiringAgentState psi kappa tau =>
              u.core.erase.core.label) hleaderFrame).trans hleaderLabelM
        refine ⟨word ++ [e], D, ?_, ?_, hstateD, hfreeD,
          hleaderLabelD⟩
        · calc
            D = runLocalSchedule ring T M [e] := rfl
            _ = runLocalSchedule ring T
                (runLocalSchedule ring T current word) [e] := by rw [← hM]
            _ = runLocalSchedule ring T current (word ++ [e]) :=
              (runLocalSchedule_append_generic
                ring T current word [e]).symm
        · simp only [List.length_append, List.length_cons, List.length_nil]
          omega

set_option maxHeartbeats 2000000 in
/-- If the next responder echo is true, the actual reset-aware follower step
clears that blocker and frames every higher follower echo, so the established
binary clockwise rank strictly decreases. -/
theorem ResetAwareNormalizedPrefixState.rank_lt_of_echo_true
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (leader : Fin n) (base current : EConfig n psi kappa tau)
    (steps : Nat)
    (hstate : ResetAwareNormalizedPrefixState
      hpsi ring leader base current steps)
    (hlt : steps < n - 1)
    (hrightEcho :
      (current (groupOffset ring leader (steps + 1))).core.erase.core.echo =
        true) :
    let D := localStep ring
      (wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
        hpsi kappa tau) current (groupOffset ring leader steps)
    clockwiseEchoRank ring leader D <
      clockwiseEchoRank ring leader current := by
  let e := groupOffset ring leader steps
  let j := groupOffset ring leader (steps + 1)
  let T := wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
    hpsi kappa tau
  let D := localStep ring T current e
  have hnpos : 0 < n := by omega
  have heBound : steps < n := by omega
  have hjBound : steps + 1 < n := by omega
  have hneighbor : ring.rightNeighbor e = j := by
    simpa [e, j] using rightNeighbor_groupOffset ring leader steps
  have heNotLeader : e ≠ leader := by
    have hne := groupOffset_ne_of_lt ring leader heBound
      hnpos (Nat.ne_of_gt hstate.steps_pos)
    exact fun heq =>
      hne (heq.trans (groupOffset_zero_eq ring leader).symm)
  have hjNotLeader : j ≠ leader := by
    have hne := groupOffset_ne_of_lt ring leader hjBound
      hnpos (Nat.ne_of_gt (Nat.zero_lt_succ steps))
    exact fun heq =>
      hne (heq.trans (groupOffset_zero_eq ring leader).symm)
  have hstep := resetAwareFollower_localStep_normalizes
    hpsi ring hn current e hstate.no_active
      (hstate.unique_leader e heNotLeader) hstate.frontier_reset
      (by rw [hneighbor]; exact hstate.unique_leader j hjNotLeader)
  change ResetAwareFollowerGlobalStepFrame hpsi ring current D e at hstep
  have hpair : ExpiringResetFollowerNormalizedOutput hpsi
      (current e, current j) (D e, D j) := by
    simpa [hneighbor] using hstep.normalized
  have hoff : ∀ i, i ≠ e → i ≠ j → D i = current i := by
    intro i hie hij
    apply hstep.off_edge i hie
    rwa [hneighbor]
  let t : Fin (n - 1) := ⟨steps, hlt⟩
  have heffect : FirstBlockerEffect ring leader current D t := {
    blocker_present := by
      simpa [t, j] using hrightEcho
    blocker_cleared := by
      simpa [t, j] using hpair.control.right_echo_false
    higher_unchanged := by
      intro s hs
      have hsBound : s.val + 1 < n := by omega
      have hse : groupOffset ring leader (s.val + 1) ≠ e := by
        apply groupOffset_ne_of_lt ring leader hsBound heBound
        dsimp only [t] at hs
        omega
      have hsj : groupOffset ring leader (s.val + 1) ≠ j := by
        apply groupOffset_ne_of_lt ring leader hsBound hjBound
        dsimp only [t] at hs
        omega
      exact congrArg
        (fun u : ExpiringAgentState psi kappa tau =>
          u.core.erase.core.echo)
        (hoff (groupOffset ring leader (s.val + 1)) hse hsj) }
  exact heffect.rank_lt

set_option maxHeartbeats 1000000 in
/-- Exact global bullet frame for one reset-aware follower edge.  The
responder is cleared; a responder dummy is moved to the initiator, otherwise
the initiator bullet is framed; every site outside the active edge is framed. -/
theorem resetAwareFollower_localStep_bullets
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (C : EConfig n psi kappa tau) (e : Fin n)
    (hnoActive : NoActiveDeletion C)
    (heFollower : (C e).core.erase.core.leader = false)
    (heReset : (C e).core.erase.core.reset_cmd = true)
    (hjFollower :
      (C (ring.rightNeighbor e)).core.erase.core.leader = false)
    (hjNotLive :
      (C (ring.rightNeighbor e)).core.erase.core.bullet ≠
        ⟨2, by omega⟩) :
    let j := ring.rightNeighbor e
    let T :=
      wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
        hpsi kappa tau
    let D := localStep ring T C e
    (D e).core.erase.core.bullet =
        (if (C j).core.erase.core.bullet = ⟨1, by omega⟩ then
          ⟨1, by omega⟩ else (C e).core.erase.core.bullet) ∧
      (D j).core.erase.core.bullet = ⟨0, by omega⟩ ∧
      ∀ i, i ≠ e → i ≠ j →
        (D i).core.erase.core.bullet = (C i).core.erase.core.bullet := by
  let j := ring.rightNeighbor e
  let T := wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
    hpsi kappa tau
  let D := localStep ring T C e
  have hje : j ≠ e := rightNeighbor_ne_self_of_one_lt ring hn e
  have hopen : WallPriorityOpen (C e) (C j) := by
    simpa [j] using
      (WallPriorityOpen.of_noActiveDeletion C hnoActive ring e)
  have hpair :=
    wallSweepResetProbePreCheckResetLeaderSinkPathStall_priority_open_follower_bullets
      hpsi (C e) (C j) hopen heFollower heReset
        (by simpa [j] using hjFollower) (by simpa [j] using hjNotLive)
  change (T (C e) (C j)).1.core.erase.core.bullet =
        (if (C j).core.erase.core.bullet = ⟨1, by omega⟩ then
          ⟨1, by omega⟩ else (C e).core.erase.core.bullet) ∧
      (T (C e) (C j)).2.core.erase.core.bullet =
        ⟨0, by omega⟩ at hpair
  refine ⟨?_, ?_, ?_⟩
  · simpa [D, T, localStep, j] using hpair.1
  · simpa [D, T, localStep, j, hje] using hpair.2
  · intro i hie hij
    simp [D, T, localStep, j, hie, hij]

/-- One follower step extends live freedom of the visited prefix when the new
responder is non-live. -/
theorem ResetAwareNormalizedPrefixState.visitedLiveFree_step
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (leader : Fin n) (base current : EConfig n psi kappa tau)
    (steps : Nat)
    (hstate : ResetAwareNormalizedPrefixState
      hpsi ring leader base current steps)
    (hlt : steps < n - 1)
    (hvisited : VisitedPrefixLiveFree ring leader current steps)
    (hrightNotLive :
      (current (groupOffset ring leader (steps + 1))).core.erase.core.bullet ≠
        ⟨2, by omega⟩) :
    let e := groupOffset ring leader steps
    let D := localStep ring
      (wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
        hpsi kappa tau) current e
    VisitedPrefixLiveFree ring leader D (steps + 1) := by
  let e := groupOffset ring leader steps
  let j := groupOffset ring leader (steps + 1)
  let T := wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
    hpsi kappa tau
  let D := localStep ring T current e
  have hnpos : 0 < n := by omega
  have heBound : steps < n := by omega
  have hjBound : steps + 1 < n := by omega
  have hneighbor : ring.rightNeighbor e = j := by
    simpa [e, j] using rightNeighbor_groupOffset ring leader steps
  have heNotLeader : e ≠ leader := by
    have hne := groupOffset_ne_of_lt ring leader heBound hnpos
      (Nat.ne_of_gt hstate.steps_pos)
    exact fun heq => hne (heq.trans (groupOffset_zero_eq ring leader).symm)
  have hjNotLeader : j ≠ leader := by
    have hne := groupOffset_ne_of_lt ring leader hjBound hnpos (by omega)
    exact fun heq => hne (heq.trans (groupOffset_zero_eq ring leader).symm)
  have hframe := resetAwareFollower_localStep_bullets
    hpsi ring hn current e hstate.no_active
      (hstate.unique_leader e heNotLeader) hstate.frontier_reset
      (by rw [hneighbor]; exact hstate.unique_leader j hjNotLeader)
      (by simpa [hneighbor, j] using hrightNotLive)
  dsimp only at hframe
  rw [hneighbor] at hframe
  change (D e).core.erase.core.bullet =
        (if (current j).core.erase.core.bullet = ⟨1, by omega⟩ then
          ⟨1, by omega⟩ else (current e).core.erase.core.bullet) ∧
      (D j).core.erase.core.bullet = ⟨0, by omega⟩ ∧
      ∀ i, i ≠ e → i ≠ j →
        (D i).core.erase.core.bullet =
          (current i).core.erase.core.bullet at hframe
  have heNotLive : (current e).core.erase.core.bullet ≠
      ⟨2, by omega⟩ := by
    simpa [e] using hvisited steps hstate.steps_pos (Nat.le_refl steps)
  have hleftNotLive : (D e).core.erase.core.bullet ≠
      ⟨2, by omega⟩ := by
    rw [hframe.1]
    split
    · intro hbad
      have hval := congrArg Fin.val hbad
      simp at hval
    · exact heNotLive
  have hrightOutNotLive : (D j).core.erase.core.bullet ≠
      ⟨2, by omega⟩ := by
    rw [hframe.2.1]
    intro hbad
    have hval := congrArg Fin.val hbad
    simp at hval
  change VisitedPrefixLiveFree ring leader D (steps + 1)
  unfold VisitedPrefixLiveFree
  intro k hkpos hkle
  by_cases hkRight : k = steps + 1
  · subst k
    simpa [j] using hrightOutNotLive
  · have hkOld : k ≤ steps := by omega
    by_cases hkLeft : k = steps
    · subst k
      simpa [e] using hleftNotLive
    · have hkBound : k < n := by omega
      have hke : groupOffset ring leader k ≠ e := by
        apply groupOffset_ne_of_lt ring leader hkBound heBound
        omega
      have hkj : groupOffset ring leader k ≠ j := by
        apply groupOffset_ne_of_lt ring leader hkBound hjBound
        omega
      rw [hframe.2.2 _ hke hkj]
      exact hvisited k hkpos hkOld

set_option maxHeartbeats 2000000 in
/-- A follower step across two non-live prefix sites preserves the complete
mobile live bit-vector.  Dummy motion is permitted because the rank observes
only live value `2`. -/
theorem ResetAwareNormalizedPrefixState.mobileLiveRank_eq_of_responder_not_live
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (leader : Fin n) (base current : EConfig n psi kappa tau)
    (steps : Nat)
    (hstate : ResetAwareNormalizedPrefixState
      hpsi ring leader base current steps)
    (hlt : steps < n - 1)
    (hvisited : VisitedPrefixLiveFree ring leader current steps)
    (hrightNotLive :
      (current (groupOffset ring leader (steps + 1))).core.erase.core.bullet ≠
        ⟨2, by omega⟩) :
    let e := groupOffset ring leader steps
    let D := localStep ring
      (wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
        hpsi kappa tau) current e
    clockwiseMobileLiveRank ring leader D =
      clockwiseMobileLiveRank ring leader current := by
  let e := groupOffset ring leader steps
  let j := groupOffset ring leader (steps + 1)
  let T := wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
    hpsi kappa tau
  let D := localStep ring T current e
  have heBound : steps < n := by omega
  have hjBound : steps + 1 < n := by omega
  have hneighbor : ring.rightNeighbor e = j := by
    simpa [e, j] using rightNeighbor_groupOffset ring leader steps
  have hvisitedD := hstate.visitedLiveFree_step
    hpsi ring hn leader base current steps hlt hvisited hrightNotLive
  change VisitedPrefixLiveFree ring leader D (steps + 1) at hvisitedD
  apply congrArg binaryRank
  funext t
  simp only [clockwiseMobileLiveBits]
  let k := t.val + 2
  have hkPos : 0 < k := by omega
  have hkBound : k < n := by omega
  by_cases hkVisited : k ≤ steps + 1
  · have hbefore :
        (current (groupOffset ring leader k)).core.erase.core.bullet ≠
          ⟨2, by omega⟩ := by
      by_cases hkRight : k = steps + 1
      · simpa [hkRight] using hrightNotLive
      · exact hvisited k hkPos (by omega)
    have hafter := hvisitedD k hkPos hkVisited
    rw [if_neg (by simpa [k] using hafter),
      if_neg (by simpa [k] using hbefore)]
  · have hke : groupOffset ring leader k ≠ e := by
      apply groupOffset_ne_of_lt ring leader hkBound heBound
      omega
    have hkj : groupOffset ring leader k ≠ j := by
      apply groupOffset_ne_of_lt ring leader hkBound hjBound
      omega
    have hsame : D (groupOffset ring leader k) =
        current (groupOffset ring leader k) := by
      simp [D, T, localStep, e, hneighbor, j, hke, hkj]
    change
      (if (D (groupOffset ring leader k)).core.erase.core.bullet =
          ⟨2, by omega⟩ then true else false) =
        (if (current (groupOffset ring leader k)).core.erase.core.bullet =
          ⟨2, by omega⟩ then true else false)
    rw [hsame]

/-- If the crossed base prefix and the realized prefix are both non-live,
then advancing the reset frontier has not changed any bit of the mobile-live
rank.  Sites ahead of the frontier are framed by `untouched_ahead`. -/
theorem ResetAwareNormalizedPrefixState.mobileLiveRank_eq_base_of_visited_free
    {hpsi : psi > 0} (ring : DirectedRing n) (leader : Fin n)
    (base current : EConfig n psi kappa tau) (steps : Nat)
    (hstate : ResetAwareNormalizedPrefixState
      hpsi ring leader base current steps)
    (hvisited : VisitedPrefixLiveFree ring leader current steps)
    (hbaseNotLive : ∀ k, 1 < k → k ≤ steps →
      (base (groupOffset ring leader k)).core.erase.core.bullet ≠
        ⟨2, by omega⟩) :
    clockwiseMobileLiveRank ring leader current =
      clockwiseMobileLiveRank ring leader base := by
  apply congrArg binaryRank
  funext t
  simp only [clockwiseMobileLiveBits]
  let k := t.val + 2
  have hkPos : 0 < k := by omega
  have hkBound : k < n := by omega
  by_cases hkVisited : k ≤ steps
  · have hcurrent := hvisited k hkPos hkVisited
    have hbase := hbaseNotLive k (by omega) hkVisited
    rw [if_neg (by simpa [k] using hcurrent),
      if_neg (by simpa [k] using hbase)]
  · have hsame := hstate.untouched_ahead k (by omega) hkBound
    change
      (if (current (groupOffset ring leader k)).core.erase.core.bullet =
          ⟨2, by omega⟩ then true else false) =
        (if (base (groupOffset ring leader k)).core.erase.core.bullet =
          ⟨2, by omega⟩ then true else false)
    rw [hsame]

set_option maxHeartbeats 3000000 in
/-- Advance through a base interval containing neither echoes nor live
bullets.  In addition to the unrestricted prefix theorem, this version keeps
the whole visited positive prefix live-free. -/
theorem
    ResetAwareNormalizedPrefixState.exists_advance_to_of_base_event_free
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (leader : Fin n) (base current : EConfig n psi kappa tau)
    (steps target : Nat)
    (hstate : ResetAwareNormalizedPrefixState
      hpsi ring leader base current steps)
    (hvisited : VisitedPrefixLiveFree ring leader current steps)
    (hsteps : steps ≤ target) (htarget : target ≤ n - 1)
    (hbaseEcho : ∀ k, steps < k → k ≤ target →
      (base (groupOffset ring leader k)).core.erase.core.echo = false)
    (hbaseNotLive : ∀ k, steps < k → k ≤ target →
      (base (groupOffset ring leader k)).core.erase.core.bullet ≠
        ⟨2, by omega⟩) :
    ∃ (word : DetSchedule n) (D : EConfig n psi kappa tau),
      D = runLocalSchedule ring
        (wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
          hpsi kappa tau) current word ∧
      word.length = target - steps ∧
      ResetAwareNormalizedPrefixState
        hpsi ring leader base D target ∧
      VisitedPrefixLiveFree ring leader D target ∧
      D leader = current leader ∧
      PPLLPpsiLeaderCreationRepair.bulletTwoCount D ≤
        PPLLPpsiLeaderCreationRepair.bulletTwoCount current := by
  induction target generalizing current steps with
  | zero =>
      have hzero : steps = 0 := by omega
      exact (Nat.ne_of_gt hstate.steps_pos hzero).elim
  | succ target ih =>
      by_cases hdone : steps = target + 1
      · subst steps
        refine ⟨[], current, by simp [runLocalSchedule], by simp,
          hstate, hvisited, rfl, Nat.le_refl _⟩
      · have hstepsPrev : steps ≤ target := by omega
        have htargetPrev : target ≤ n - 1 := by omega
        obtain ⟨word, M, hM, hwordLength, hstateM, hvisitedM,
            hleaderM, hcountM⟩ :=
          ih (current := current) (steps := steps)
            hstate hvisited hstepsPrev htargetPrev
              (by
                intro k hk hkt
                exact hbaseEcho k hk (by omega))
              (by
                intro k hk hkt
                exact hbaseNotLive k hk (by omega))
        have htargetPos : 0 < target := hstateM.steps_pos
        have htargetLt : target < n - 1 := by omega
        have hnextEcho :
            (M (groupOffset ring leader (target + 1))).core.erase.core.echo =
              false := by
          rw [hstateM.untouched_ahead (target + 1)
            (by omega) (by omega)]
          exact hbaseEcho (target + 1) (by omega) (by omega)
        have hnextNotLive :
            (M (groupOffset ring leader (target + 1))).core.erase.core.bullet ≠
              ⟨2, by omega⟩ := by
          rw [hstateM.untouched_ahead (target + 1)
            (by omega) (by omega)]
          exact hbaseNotLive (target + 1) (by omega) (by omega)
        let e := groupOffset ring leader target
        let T :=
          wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
            hpsi kappa tau
        let D := localStep ring T M e
        have hstateD := hstateM.step_of_echo_false
          hpsi ring hn leader base M target htargetLt hnextEcho
        change ResetAwareNormalizedPrefixState
          hpsi ring leader base D (target + 1) at hstateD
        have hvisitedD := hstateM.visitedLiveFree_step
          hpsi ring hn leader base M target htargetLt hvisitedM hnextNotLive
        change VisitedPrefixLiveFree
          ring leader D (target + 1) at hvisitedD
        have heBound : target < n := by omega
        have hjBound : target + 1 < n := by omega
        have heNotLeader : e ≠ leader := by
          intro heq
          have hne := groupOffset_ne_of_lt ring leader heBound
            (by omega : 0 < n) (Nat.ne_of_gt htargetPos)
          exact hne (heq.trans (groupOffset_zero_eq ring leader).symm)
        have hjNotLeader :
            groupOffset ring leader (target + 1) ≠ leader := by
          intro heq
          have hne := groupOffset_ne_of_lt ring leader hjBound
            (by omega : 0 < n) (by omega : target + 1 ≠ 0)
          exact hne (heq.trans (groupOffset_zero_eq ring leader).symm)
        have hneighbor : ring.rightNeighbor e =
            groupOffset ring leader (target + 1) := by
          simpa [e] using rightNeighbor_groupOffset ring leader target
        have hrightFollower :
            (M (ring.rightNeighbor e)).core.erase.core.leader = false := by
          rw [hneighbor]
          exact hstateM.unique_leader _ hjNotLeader
        have hleaderFrame : D leader = M leader := by
          simp [D, T, localStep, Ne.symm heNotLeader, hneighbor,
            Ne.symm hjNotLeader]
        have hcountStep := resetAwareFollower_localStep_bulletTwoCount_le
          hpsi ring hn M e hstateM.no_active
            (hstateM.unique_leader e heNotLeader) hstateM.frontier_reset
            hrightFollower
        change PPLLPpsiLeaderCreationRepair.bulletTwoCount D ≤
          PPLLPpsiLeaderCreationRepair.bulletTwoCount M at hcountStep
        refine ⟨word ++ [e], D, ?_, ?_, hstateD, hvisitedD,
          hleaderFrame.trans hleaderM,
          Nat.le_trans hcountStep hcountM⟩
        · calc
            D = runLocalSchedule ring T M [e] := rfl
            _ = runLocalSchedule ring T
                (runLocalSchedule ring T current word) [e] := by rw [← hM]
            _ = runLocalSchedule ring T current (word ++ [e]) :=
              (runLocalSchedule_append_generic
                ring T current word [e]).symm
        · simp only [List.length_append, List.length_cons, List.length_nil]
          omega

set_option maxHeartbeats 3000000 in
/-- Birth-signal-transition lift of the event-free prefix traversal. -/
theorem
    ResetAwareNormalizedPrefixState.exists_birthSignalZero_advance_to_of_base_event_free
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (leader : Fin n) (base current : EConfig n psi kappa tau)
    (steps target : Nat)
    (hstate : ResetAwareNormalizedPrefixState
      hpsi ring leader base current steps)
    (hvisited : VisitedPrefixLiveFree ring leader current steps)
    (hsteps : steps ≤ target) (htarget : target ≤ n - 1)
    (hbaseEcho : ∀ k, steps < k → k ≤ target →
      (base (groupOffset ring leader k)).core.erase.core.echo = false)
    (hbaseNotLive : ∀ k, steps < k → k ≤ target →
      (base (groupOffset ring leader k)).core.erase.core.bullet ≠
        ⟨2, by omega⟩) :
    ∃ (word : DetSchedule n) (D : EConfig n psi kappa tau),
      D = runLocalSchedule ring
        (wallSweepBirthSignalZeroPathStallTransition
          hpsi kappa tau) current word ∧
      word.length = target - steps ∧
      ResetAwareNormalizedPrefixState
        hpsi ring leader base D target ∧
      VisitedPrefixLiveFree ring leader D target ∧
      D leader = current leader ∧
      PPLLPpsiLeaderCreationRepair.bulletTwoCount D ≤
        PPLLPpsiLeaderCreationRepair.bulletTwoCount current := by
  induction target generalizing current steps with
  | zero =>
      have hzero : steps = 0 := by omega
      exact (Nat.ne_of_gt hstate.steps_pos hzero).elim
  | succ target ih =>
      by_cases hdone : steps = target + 1
      · subst steps
        refine ⟨[], current, by simp [runLocalSchedule], by simp,
          hstate, hvisited, rfl, Nat.le_refl _⟩
      · have hstepsPrev : steps ≤ target := by omega
        have htargetPrev : target ≤ n - 1 := by omega
        obtain ⟨word, M, hM, hwordLength, hstateM, hvisitedM,
            hleaderM, hcountM⟩ :=
          ih (current := current) (steps := steps)
            hstate hvisited hstepsPrev htargetPrev
              (by
                intro k hk hkt
                exact hbaseEcho k hk (by omega))
              (by
                intro k hk hkt
                exact hbaseNotLive k hk (by omega))
        have htargetPos : 0 < target := hstateM.steps_pos
        have htargetLt : target < n - 1 := by omega
        have hnextEcho :
            (M (groupOffset ring leader (target + 1))).core.erase.core.echo =
              false := by
          rw [hstateM.untouched_ahead (target + 1)
            (by omega) (by omega)]
          exact hbaseEcho (target + 1) (by omega) (by omega)
        have hnextNotLive :
            (M (groupOffset ring leader (target + 1))).core.erase.core.bullet ≠
              ⟨2, by omega⟩ := by
          rw [hstateM.untouched_ahead (target + 1)
            (by omega) (by omega)]
          exact hbaseNotLive (target + 1) (by omega) (by omega)
        let e := groupOffset ring leader target
        let Tnew := wallSweepBirthSignalZeroPathStallTransition
          hpsi kappa tau
        let Told :=
          wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
            hpsi kappa tau
        let Dold := localStep ring Told M e
        let D := localStep ring Tnew M e
        have heq : D = Dold := by
          simpa only [D, Dold, Tnew, Told, e] using
            hstateM.localStep_birthSignalZero_eq_resetProbe
              hpsi ring hn leader base M target htargetLt
        have hstateD := hstateM.step_birthSignalZero_of_echo_false
          hpsi ring hn leader base M target htargetLt hnextEcho
        change ResetAwareNormalizedPrefixState
          hpsi ring leader base D (target + 1) at hstateD
        have hvisitedOld := hstateM.visitedLiveFree_step
          hpsi ring hn leader base M target htargetLt hvisitedM hnextNotLive
        change VisitedPrefixLiveFree
          ring leader Dold (target + 1) at hvisitedOld
        have hvisitedD : VisitedPrefixLiveFree
            ring leader D (target + 1) := by
          rw [heq]
          exact hvisitedOld
        have heBound : target < n := by omega
        have hjBound : target + 1 < n := by omega
        have heNotLeader : e ≠ leader := by
          intro heqLeader
          have hne := groupOffset_ne_of_lt ring leader heBound
            (by omega : 0 < n) (Nat.ne_of_gt htargetPos)
          exact hne (heqLeader.trans (groupOffset_zero_eq ring leader).symm)
        have hjNotLeader :
            groupOffset ring leader (target + 1) ≠ leader := by
          intro heqLeader
          have hne := groupOffset_ne_of_lt ring leader hjBound
            (by omega : 0 < n) (by omega : target + 1 ≠ 0)
          exact hne (heqLeader.trans (groupOffset_zero_eq ring leader).symm)
        have hneighbor : ring.rightNeighbor e =
            groupOffset ring leader (target + 1) := by
          simpa [e] using rightNeighbor_groupOffset ring leader target
        have hrightFollower :
            (M (ring.rightNeighbor e)).core.erase.core.leader = false := by
          rw [hneighbor]
          exact hstateM.unique_leader _ hjNotLeader
        have hleaderFrame : D leader = M leader := by
          simp [D, Tnew, localStep, Ne.symm heNotLeader, hneighbor,
            Ne.symm hjNotLeader]
        have hcountOld := resetAwareFollower_localStep_bulletTwoCount_le
          hpsi ring hn M e hstateM.no_active
            (hstateM.unique_leader e heNotLeader) hstateM.frontier_reset
            hrightFollower
        change PPLLPpsiLeaderCreationRepair.bulletTwoCount Dold ≤
          PPLLPpsiLeaderCreationRepair.bulletTwoCount M at hcountOld
        have hcountStep : PPLLPpsiLeaderCreationRepair.bulletTwoCount D ≤
            PPLLPpsiLeaderCreationRepair.bulletTwoCount M := by
          rw [heq]
          exact hcountOld
        refine ⟨word ++ [e], D, ?_, ?_, hstateD, hvisitedD,
          hleaderFrame.trans hleaderM, Nat.le_trans hcountStep hcountM⟩
        · calc
            D = runLocalSchedule ring Tnew M [e] := rfl
            _ = runLocalSchedule ring Tnew
                (runLocalSchedule ring Tnew current word) [e] := by rw [← hM]
            _ = runLocalSchedule ring Tnew current (word ++ [e]) :=
              (runLocalSchedule_append_generic
                ring Tnew current word [e]).symm
        · simp only [List.length_append, List.length_cons, List.length_nil]
          omega

set_option maxHeartbeats 2000000 in
/-- When a reset-aware follower step meets a responder dummy, the physical
transition clears that responder bullet and frames every higher clockwise
follower.  Hence the binary dummy rank strictly decreases, regardless of the
new lower-offset bullet pattern. -/
theorem ResetAwareNormalizedPrefixState.dummyRank_lt_of_responder_dummy
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (leader : Fin n) (base current : EConfig n psi kappa tau)
    (steps : Nat)
    (hstate : ResetAwareNormalizedPrefixState
      hpsi ring leader base current steps)
    (hlt : steps < n - 1)
    (hfree :
      PPLLPpsiLeaderCreationRepair.BulletTwoFreeAwayFrom current leader)
    (hrightDummy :
      (current (groupOffset ring leader (steps + 1))).core.erase.core.bullet =
        ⟨1, by omega⟩) :
    let D := localStep ring
      (wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
        hpsi kappa tau) current (groupOffset ring leader steps)
    clockwiseDummyRank ring leader D <
      clockwiseDummyRank ring leader current := by
  let e := groupOffset ring leader steps
  let j := groupOffset ring leader (steps + 1)
  let T := wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
    hpsi kappa tau
  let D := localStep ring T current e
  have hnpos : 0 < n := by omega
  have heBound : steps < n := by omega
  have hjBound : steps + 1 < n := by omega
  have hneighbor : ring.rightNeighbor e = j := by
    simpa [e, j] using rightNeighbor_groupOffset ring leader steps
  have hje : j ≠ e := by
    apply groupOffset_ne_of_lt ring leader hjBound heBound
    omega
  have heNotLeader : e ≠ leader := by
    have hne := groupOffset_ne_of_lt ring leader heBound
      hnpos (Nat.ne_of_gt hstate.steps_pos)
    exact fun heq =>
      hne (heq.trans (groupOffset_zero_eq ring leader).symm)
  have hjNotLeader : j ≠ leader := by
    have hne := groupOffset_ne_of_lt ring leader hjBound
      hnpos (Nat.ne_of_gt (Nat.zero_lt_succ steps))
    exact fun heq =>
      hne (heq.trans (groupOffset_zero_eq ring leader).symm)
  have heFollower :
      (current e).core.erase.core.leader = false :=
    hstate.unique_leader e heNotLeader
  have hjFollower :
      (current j).core.erase.core.leader = false :=
    hstate.unique_leader j hjNotLeader
  have hopen : WallPriorityOpen (current e) (current j) := by
    simpa [hneighbor] using
      (WallPriorityOpen.of_noActiveDeletion
        current hstate.no_active ring e)
  have hjNotLive :
      (current j).core.erase.core.bullet ≠ ⟨2, by omega⟩ :=
    hfree j hjNotLeader
  have hstep := resetAwareFollower_localStep_normalizes
    hpsi ring hn current e hstate.no_active heFollower
      hstate.frontier_reset (by simpa [hneighbor] using hjFollower)
  change ResetAwareFollowerGlobalStepFrame hpsi ring current D e at hstep
  have hbullets :=
    wallSweepResetProbePreCheckResetLeaderSinkPathStall_priority_open_follower_bullets
      hpsi (current e) (current j) hopen heFollower hstate.frontier_reset
        hjFollower hjNotLive
  change (T (current e) (current j)).1.core.erase.core.bullet =
        (if (current j).core.erase.core.bullet = ⟨1, by omega⟩ then
          ⟨1, by omega⟩ else (current e).core.erase.core.bullet) ∧
      (T (current e) (current j)).2.core.erase.core.bullet =
        ⟨0, by omega⟩ at hbullets
  have hDj : D j = (T (current e) (current j)).2 := by
    simp [D, T, localStep, hneighbor, hje]
  have hrightZero : (D j).core.erase.core.bullet =
      ⟨0, by omega⟩ := by
    rw [hDj]
    exact hbullets.2
  let t : Fin (n - 1) := ⟨steps, hlt⟩
  apply clockwiseDummyRank_lt_of_cleared_blocker
    ring leader current D t
  · dsimp only [t]
    simpa [j, hrightZero]
  · dsimp only [t]
    simpa [j] using hrightDummy
  · intro s hts
    have hsBound : s.val + 1 < n := by omega
    have hse : groupOffset ring leader (s.val + 1) ≠ e := by
      apply groupOffset_ne_of_lt ring leader hsBound heBound
      dsimp only [t] at hts
      omega
    have hsj : groupOffset ring leader (s.val + 1) ≠ j := by
      apply groupOffset_ne_of_lt ring leader hsBound hjBound
      dsimp only [t] at hts
      omega
    exact congrArg
      (fun u : ExpiringAgentState psi kappa tau =>
        u.core.erase.core.bullet)
      (hstep.off_edge (groupOffset ring leader (s.val + 1))
        hse (by rwa [hneighbor]))

set_option maxHeartbeats 2000000 in
/-- Every reset-aware follower step weakly decreases the binary dummy rank.
It is strict exactly when this proof observes a responder dummy; when the
responder bullet is zero, the exact global bullet frame gives rank equality. -/
theorem ResetAwareNormalizedPrefixState.dummyRank_le
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (leader : Fin n) (base current : EConfig n psi kappa tau)
    (steps : Nat)
    (hstate : ResetAwareNormalizedPrefixState
      hpsi ring leader base current steps)
    (hlt : steps < n - 1)
    (hfree :
      PPLLPpsiLeaderCreationRepair.BulletTwoFreeAwayFrom current leader) :
    let D := localStep ring
      (wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
        hpsi kappa tau) current (groupOffset ring leader steps)
    clockwiseDummyRank ring leader D ≤
      clockwiseDummyRank ring leader current := by
  let e := groupOffset ring leader steps
  let j := groupOffset ring leader (steps + 1)
  let T := wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
    hpsi kappa tau
  let D := localStep ring T current e
  have hnpos : 0 < n := by omega
  have heBound : steps < n := by omega
  have hjBound : steps + 1 < n := by omega
  have hneighbor : ring.rightNeighbor e = j := by
    simpa [e, j] using rightNeighbor_groupOffset ring leader steps
  have heNotLeader : e ≠ leader := by
    have hne := groupOffset_ne_of_lt ring leader heBound
      hnpos (Nat.ne_of_gt hstate.steps_pos)
    exact fun heq =>
      hne (heq.trans (groupOffset_zero_eq ring leader).symm)
  have hjNotLeader : j ≠ leader := by
    have hne := groupOffset_ne_of_lt ring leader hjBound
      hnpos (Nat.ne_of_gt (Nat.zero_lt_succ steps))
    exact fun heq =>
      hne (heq.trans (groupOffset_zero_eq ring leader).symm)
  have heFollower :
      (current e).core.erase.core.leader = false :=
    hstate.unique_leader e heNotLeader
  have hjFollower :
      (current j).core.erase.core.leader = false :=
    hstate.unique_leader j hjNotLeader
  have hjNotLive :
      (current j).core.erase.core.bullet ≠ ⟨2, by omega⟩ :=
    hfree j hjNotLeader
  by_cases hjDummy :
      (current j).core.erase.core.bullet = ⟨1, by omega⟩
  · exact Nat.le_of_lt
      (hstate.dummyRank_lt_of_responder_dummy
        hpsi ring hn leader base current steps hlt hfree
          (by simpa [j] using hjDummy))
  · have hjZero : (current j).core.erase.core.bullet =
        ⟨0, by omega⟩ := by
      have hval : (current j).core.erase.core.bullet.val = 0 ∨
          (current j).core.erase.core.bullet.val = 1 ∨
          (current j).core.erase.core.bullet.val = 2 := by
        omega
      rcases hval with hval | hval | hval
      · exact Fin.ext hval
      · exact (hjDummy (Fin.ext hval)).elim
      · exact (hjNotLive (Fin.ext hval)).elim
    have hframe := resetAwareFollower_localStep_bullets
      hpsi ring hn current e hstate.no_active heFollower
        hstate.frontier_reset (by simpa [hneighbor] using hjFollower)
        (by simpa [hneighbor] using hjNotLive)
    dsimp only at hframe
    rw [hneighbor] at hframe
    change (D e).core.erase.core.bullet =
          (if (current j).core.erase.core.bullet = ⟨1, by omega⟩ then
            ⟨1, by omega⟩ else (current e).core.erase.core.bullet) ∧
        (D j).core.erase.core.bullet = ⟨0, by omega⟩ ∧
        ∀ i, i ≠ e → i ≠ j →
          (D i).core.erase.core.bullet =
            (current i).core.erase.core.bullet at hframe
    rw [if_neg hjDummy] at hframe
    have hbullets : ∀ i,
        (D i).core.erase.core.bullet =
          (current i).core.erase.core.bullet := by
      intro i
      by_cases hie : i = e
      · subst i
        exact hframe.1
      · by_cases hij : i = j
        · subst i
          exact hframe.2.1.trans hjZero.symm
        · exact hframe.2.2 i hie hij
    have hrank : clockwiseDummyRank ring leader D =
        clockwiseDummyRank ring leader current := by
      apply congrArg binaryRank
      funext t
      simp only [clockwiseFollowerDummyBits]
      rw [hbullets]
    exact Nat.le_of_eq hrank

set_option maxHeartbeats 2000000 in
/-- A responder dummy encountered beyond the first outgoing follower strictly
decreases the restart-stable mobile dummy rank. -/
theorem ResetAwareNormalizedPrefixState.mobileDummyRank_lt_of_responder_dummy
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (leader : Fin n) (base current : EConfig n psi kappa tau)
    (steps : Nat)
    (hstate : ResetAwareNormalizedPrefixState
      hpsi ring leader base current steps)
    (hlt : steps < n - 1)
    (hfree :
      PPLLPpsiLeaderCreationRepair.BulletTwoFreeAwayFrom current leader)
    (hrightDummy :
      (current (groupOffset ring leader (steps + 1))).core.erase.core.bullet =
        ⟨1, by omega⟩) :
    let D := localStep ring
      (wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
        hpsi kappa tau) current (groupOffset ring leader steps)
    clockwiseMobileDummyRank ring leader D <
      clockwiseMobileDummyRank ring leader current := by
  let e := groupOffset ring leader steps
  let j := groupOffset ring leader (steps + 1)
  let T := wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
    hpsi kappa tau
  let D := localStep ring T current e
  have hnpos : 0 < n := by omega
  have hstepsPos : 0 < steps := hstate.steps_pos
  have heBound : steps < n := by omega
  have hjBound : steps + 1 < n := by omega
  have hneighbor : ring.rightNeighbor e = j := by
    simpa [e, j] using rightNeighbor_groupOffset ring leader steps
  have heNotLeader : e ≠ leader := by
    have hne := groupOffset_ne_of_lt ring leader heBound
      hnpos (Nat.ne_of_gt hstate.steps_pos)
    exact fun heq =>
      hne (heq.trans (groupOffset_zero_eq ring leader).symm)
  have hjNotLeader : j ≠ leader := by
    have hne := groupOffset_ne_of_lt ring leader hjBound
      hnpos (Nat.ne_of_gt (Nat.zero_lt_succ steps))
    exact fun heq =>
      hne (heq.trans (groupOffset_zero_eq ring leader).symm)
  have hframe := resetAwareFollower_localStep_bullets
    hpsi ring hn current e hstate.no_active
      (hstate.unique_leader e heNotLeader) hstate.frontier_reset
      (by rw [hneighbor]; exact hstate.unique_leader j hjNotLeader)
      (by rw [hneighbor]; exact hfree j hjNotLeader)
  dsimp only at hframe
  rw [hneighbor] at hframe
  change (D e).core.erase.core.bullet =
        (if (current j).core.erase.core.bullet = ⟨1, by omega⟩ then
          ⟨1, by omega⟩ else (current e).core.erase.core.bullet) ∧
      (D j).core.erase.core.bullet = ⟨0, by omega⟩ ∧
      ∀ i, i ≠ e → i ≠ j →
        (D i).core.erase.core.bullet =
          (current i).core.erase.core.bullet at hframe
  let t : Fin (n - 2) := ⟨steps - 1, by omega⟩
  apply clockwiseMobileDummyRank_lt_of_cleared_blocker
    ring leader current D t
  · dsimp only [t]
    have hindex : steps - 1 + 2 = steps + 1 := by omega
    rw [hindex]
    change (D j).core.erase.core.bullet ≠ ⟨1, by omega⟩
    rw [hframe.2.1]
    intro hbad
    have hval := congrArg Fin.val hbad
    simp at hval
  · dsimp only [t]
    have hindex : steps - 1 + 2 = steps + 1 := by omega
    rw [hindex]
    change (current j).core.erase.core.bullet = ⟨1, by omega⟩
    exact hrightDummy
  · intro s hts
    have hsBound : s.val + 2 < n := by omega
    have hse : groupOffset ring leader (s.val + 2) ≠ e := by
      apply groupOffset_ne_of_lt ring leader hsBound heBound
      dsimp only [t] at hts
      omega
    have hsj : groupOffset ring leader (s.val + 2) ≠ j := by
      apply groupOffset_ne_of_lt ring leader hsBound hjBound
      dsimp only [t] at hts
      omega
    exact hframe.2.2 _ hse hsj

set_option maxHeartbeats 2000000 in
/-- A live responder encountered beyond the immediate outgoing follower
strictly decreases the fixed-root mobile live-bullet rank.  The exact physical
step clears the responder, moves its bullet toward the root, and frames every
higher mobile offset. -/
theorem ResetAwareNormalizedPrefixState.mobileLiveRank_lt_of_responder_live
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (leader : Fin n) (base current : EConfig n psi kappa tau)
    (steps : Nat)
    (hstate : ResetAwareNormalizedPrefixState
      hpsi ring leader base current steps)
    (hlt : steps < n - 1)
    (hrightLive :
      (current (groupOffset ring leader (steps + 1))).core.erase.core.bullet =
        ⟨2, by omega⟩) :
    let D := localStep ring
      (wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
        hpsi kappa tau) current (groupOffset ring leader steps)
    clockwiseMobileLiveRank ring leader D <
      clockwiseMobileLiveRank ring leader current := by
  let e := groupOffset ring leader steps
  let j := groupOffset ring leader (steps + 1)
  let T := wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
    hpsi kappa tau
  let D := localStep ring T current e
  have hnpos : 0 < n := by omega
  have heBound : steps < n := by omega
  have hjBound : steps + 1 < n := by omega
  have hneighbor : ring.rightNeighbor e = j := by
    simpa [e, j] using rightNeighbor_groupOffset ring leader steps
  have heNotLeader : e ≠ leader := by
    have hne := groupOffset_ne_of_lt ring leader heBound
      hnpos (Nat.ne_of_gt hstate.steps_pos)
    exact fun heq =>
      hne (heq.trans (groupOffset_zero_eq ring leader).symm)
  have hjNotLeader : j ≠ leader := by
    have hne := groupOffset_ne_of_lt ring leader hjBound
      hnpos (Nat.ne_of_gt (Nat.zero_lt_succ steps))
    exact fun heq =>
      hne (heq.trans (groupOffset_zero_eq ring leader).symm)
  have heFollower := hstate.unique_leader e heNotLeader
  have hjFollower := hstate.unique_leader j hjNotLeader
  have hstep := resetAwareFollower_localStep_normalizes
    hpsi ring hn current e hstate.no_active heFollower
      hstate.frontier_reset (by simpa [hneighbor] using hjFollower)
  change ResetAwareFollowerGlobalStepFrame hpsi ring current D e at hstep
  have hshift := resetAwareFollower_localStep_live_bullet_shifts_left
    hpsi ring hn current e hstate.no_active heFollower
      hstate.frontier_reset (by simpa [hneighbor] using hjFollower)
      (by simpa [hneighbor] using hrightLive)
  change (D e).core.erase.core.bullet = ⟨2, by omega⟩ ∧
    (D (ring.rightNeighbor e)).core.erase.core.bullet =
      ⟨0, by omega⟩ at hshift
  rw [hneighbor] at hshift
  have hstepsPos : 0 < steps := hstate.steps_pos
  let t : Fin (n - 2) := ⟨steps - 1, by omega⟩
  apply clockwiseMobileLiveRank_lt_of_cleared_blocker
    ring leader current D t
  · dsimp only [t]
    have hindex : steps - 1 + 2 = steps + 1 := by omega
    rw [hindex]
    change (D j).core.erase.core.bullet ≠ ⟨2, by omega⟩
    rw [hshift.2]
    simp
  · dsimp only [t]
    have hindex : steps - 1 + 2 = steps + 1 := by omega
    rw [hindex]
    change (current j).core.erase.core.bullet = ⟨2, by omega⟩
    exact hrightLive
  · intro s hts
    have hsBound : s.val + 2 < n := by omega
    have hse : groupOffset ring leader (s.val + 2) ≠ e := by
      apply groupOffset_ne_of_lt ring leader hsBound heBound
      dsimp only [t] at hts
      omega
    have hsj : groupOffset ring leader (s.val + 2) ≠ j := by
      apply groupOffset_ne_of_lt ring leader hsBound hjBound
      dsimp only [t] at hts
      omega
    exact congrArg
      (fun u : ExpiringAgentState psi kappa tau =>
        u.core.erase.core.bullet)
      (hstep.off_edge (groupOffset ring leader (s.val + 2))
        hse (by rwa [hneighbor]))

set_option maxHeartbeats 2000000 in
/-- Every reset-aware follower step weakly decreases the mobile dummy rank.
The rank decreases strictly exactly on the responder-dummy branch. -/
theorem ResetAwareNormalizedPrefixState.mobileDummyRank_le
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (leader : Fin n) (base current : EConfig n psi kappa tau)
    (steps : Nat)
    (hstate : ResetAwareNormalizedPrefixState
      hpsi ring leader base current steps)
    (hlt : steps < n - 1)
    (hfree :
      PPLLPpsiLeaderCreationRepair.BulletTwoFreeAwayFrom current leader) :
    let D := localStep ring
      (wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
        hpsi kappa tau) current (groupOffset ring leader steps)
    clockwiseMobileDummyRank ring leader D ≤
      clockwiseMobileDummyRank ring leader current := by
  let e := groupOffset ring leader steps
  let j := groupOffset ring leader (steps + 1)
  let T := wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
    hpsi kappa tau
  let D := localStep ring T current e
  have hnpos : 0 < n := by omega
  have heBound : steps < n := by omega
  have hjBound : steps + 1 < n := by omega
  have hneighbor : ring.rightNeighbor e = j := by
    simpa [e, j] using rightNeighbor_groupOffset ring leader steps
  have heNotLeader : e ≠ leader := by
    have hne := groupOffset_ne_of_lt ring leader heBound
      hnpos (Nat.ne_of_gt hstate.steps_pos)
    exact fun heq =>
      hne (heq.trans (groupOffset_zero_eq ring leader).symm)
  have hjNotLeader : j ≠ leader := by
    have hne := groupOffset_ne_of_lt ring leader hjBound
      hnpos (Nat.ne_of_gt (Nat.zero_lt_succ steps))
    exact fun heq =>
      hne (heq.trans (groupOffset_zero_eq ring leader).symm)
  have hjNotLive :
      (current j).core.erase.core.bullet ≠ ⟨2, by omega⟩ :=
    hfree j hjNotLeader
  by_cases hjDummy :
      (current j).core.erase.core.bullet = ⟨1, by omega⟩
  · exact Nat.le_of_lt
      (hstate.mobileDummyRank_lt_of_responder_dummy
        hpsi ring hn leader base current steps hlt hfree
          (by simpa [j] using hjDummy))
  · have hjZero : (current j).core.erase.core.bullet =
        ⟨0, by omega⟩ := by
      have hval : (current j).core.erase.core.bullet.val = 0 ∨
          (current j).core.erase.core.bullet.val = 1 ∨
          (current j).core.erase.core.bullet.val = 2 := by
        omega
      rcases hval with hval | hval | hval
      · exact Fin.ext hval
      · exact (hjDummy (Fin.ext hval)).elim
      · exact (hjNotLive (Fin.ext hval)).elim
    have hframe := resetAwareFollower_localStep_bullets
      hpsi ring hn current e hstate.no_active
        (hstate.unique_leader e heNotLeader) hstate.frontier_reset
        (by rw [hneighbor]; exact hstate.unique_leader j hjNotLeader)
        (by simpa [hneighbor] using hjNotLive)
    dsimp only at hframe
    rw [hneighbor] at hframe
    change (D e).core.erase.core.bullet =
          (if (current j).core.erase.core.bullet = ⟨1, by omega⟩ then
            ⟨1, by omega⟩ else (current e).core.erase.core.bullet) ∧
        (D j).core.erase.core.bullet = ⟨0, by omega⟩ ∧
        ∀ i, i ≠ e → i ≠ j →
          (D i).core.erase.core.bullet =
            (current i).core.erase.core.bullet at hframe
    rw [if_neg hjDummy] at hframe
    have hbullets : ∀ i,
        (D i).core.erase.core.bullet =
          (current i).core.erase.core.bullet := by
      intro i
      by_cases hie : i = e
      · subst i
        exact hframe.1
      · by_cases hij : i = j
        · subst i
          exact hframe.2.1.trans hjZero.symm
        · exact hframe.2.2 i hie hij
    exact Nat.le_of_eq (clockwiseMobileDummyRank_eq_of_bullets
      ring leader current D (by
        intro k hk hkn
        exact hbullets (groupOffset ring leader k)))

set_option maxHeartbeats 2000000 in
/-- A positive signal at the reset frontier either reaches the next follower
or encounters a responder dummy, in which case the mobile dummy rank strictly
decreases. -/
theorem ResetAwareNormalizedPrefixState.next_signal_or_mobileDummyRank_lt
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (leader : Fin n) (base current : EConfig n psi kappa tau)
    (steps : Nat)
    (hstate : ResetAwareNormalizedPrefixState
      hpsi ring leader base current steps)
    (hlt : steps < n - 1)
    (hfree :
      PPLLPpsiLeaderCreationRepair.BulletTwoFreeAwayFrom current leader)
    (hfrontierSignal :
      (current (groupOffset ring leader steps)).core.erase.core.signal_B =
        ⟨1, by omega⟩) :
    let D := localStep ring
      (wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
        hpsi kappa tau) current (groupOffset ring leader steps)
    (D (groupOffset ring leader (steps + 1))).core.erase.core.signal_B =
        ⟨1, by omega⟩ ∨
      ((current (groupOffset ring leader (steps + 1))).core.erase.core.bullet =
          ⟨1, by omega⟩ ∧
        clockwiseMobileDummyRank ring leader D <
          clockwiseMobileDummyRank ring leader current) := by
  let e := groupOffset ring leader steps
  let j := groupOffset ring leader (steps + 1)
  let T := wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
    hpsi kappa tau
  let D := localStep ring T current e
  have hnpos : 0 < n := by omega
  have heBound : steps < n := by omega
  have hjBound : steps + 1 < n := by omega
  have hneighbor : ring.rightNeighbor e = j := by
    simpa [e, j] using rightNeighbor_groupOffset ring leader steps
  have hje : j ≠ e := by
    apply groupOffset_ne_of_lt ring leader hjBound heBound
    omega
  have heNotLeader : e ≠ leader := by
    have hne := groupOffset_ne_of_lt ring leader heBound
      hnpos (Nat.ne_of_gt hstate.steps_pos)
    exact fun heq =>
      hne (heq.trans (groupOffset_zero_eq ring leader).symm)
  have hjNotLeader : j ≠ leader := by
    have hne := groupOffset_ne_of_lt ring leader hjBound
      hnpos (Nat.ne_of_gt (Nat.zero_lt_succ steps))
    exact fun heq =>
      hne (heq.trans (groupOffset_zero_eq ring leader).symm)
  have heFollower := hstate.unique_leader e heNotLeader
  have hjFollower := hstate.unique_leader j hjNotLeader
  have hjNotLive := hfree j hjNotLeader
  have hopen : WallPriorityOpen (current e) (current j) := by
    simpa [hneighbor] using
      (WallPriorityOpen.of_noActiveDeletion current hstate.no_active ring e)
  have hprogress :=
    wallSweepResetProbePreCheckResetLeaderSinkPathStall_priority_open_signal_or_dummy_moves
      hpsi (current e) (current j) hopen heFollower hstate.frontier_reset
        hjFollower (by simpa [e] using hfrontierSignal) hjNotLive
  change (T (current e) (current j)).2.core.erase.core.signal_B =
        ⟨1, by omega⟩ ∨
      ((current j).core.erase.core.bullet = ⟨1, by omega⟩ ∧
        (T (current e) (current j)).1.core.erase.core.bullet =
          ⟨1, by omega⟩ ∧
        (T (current e) (current j)).2.core.erase.core.bullet =
          ⟨0, by omega⟩) at hprogress
  have hDj : D j = (T (current e) (current j)).2 := by
    simp [D, T, localStep, hneighbor, hje]
  rcases hprogress with hsignal | hdummy
  · apply Or.inl
    change (D j).core.erase.core.signal_B = ⟨1, by omega⟩
    rw [hDj]
    exact hsignal
  · have hrightDummy :
        (current (groupOffset ring leader (steps + 1))).core.erase.core.bullet =
          ⟨1, by omega⟩ := by
      simpa [j] using hdummy.1
    exact .inr ⟨hrightDummy,
      hstate.mobileDummyRank_lt_of_responder_dummy
        hpsi ring hn leader base current steps hlt hfree hrightDummy⟩

/-- Birth-signal-transition form of signal propagation across one normalized
follower edge. -/
theorem ResetAwareNormalizedPrefixState.next_birthSignalZero_signal_or_mobileDummyRank_lt
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (leader : Fin n) (base current : EConfig n psi kappa tau)
    (steps : Nat)
    (hstate : ResetAwareNormalizedPrefixState
      hpsi ring leader base current steps)
    (hlt : steps < n - 1)
    (hfree :
      PPLLPpsiLeaderCreationRepair.BulletTwoFreeAwayFrom current leader)
    (hfrontierSignal :
      (current (groupOffset ring leader steps)).core.erase.core.signal_B =
        ⟨1, by omega⟩) :
    let D := localStep ring
      (wallSweepBirthSignalZeroPathStallTransition
        hpsi kappa tau) current (groupOffset ring leader steps)
    (D (groupOffset ring leader (steps + 1))).core.erase.core.signal_B =
        ⟨1, by omega⟩ ∨
      ((current (groupOffset ring leader (steps + 1))).core.erase.core.bullet =
          ⟨1, by omega⟩ ∧
        clockwiseMobileDummyRank ring leader D <
          clockwiseMobileDummyRank ring leader current) := by
  have heq := hstate.localStep_birthSignalZero_eq_resetProbe
    hpsi ring hn leader base current steps hlt
  have hold := hstate.next_signal_or_mobileDummyRank_lt
    hpsi ring hn leader base current steps hlt hfree hfrontierSignal
  dsimp only at heq hold ⊢
  rw [heq]
  exact hold

/-- A birth-signal follower step preserves global live-bullet freedom and
weakly decreases the mobile-dummy rank.  Both conclusions transport through
the exact one-step equality with the established reset-probe transition. -/
theorem ResetAwareNormalizedPrefixState.step_birthSignalZero_free_and_mobileDummyRank_le
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (leader : Fin n) (base current : EConfig n psi kappa tau)
    (steps : Nat)
    (hstate : ResetAwareNormalizedPrefixState
      hpsi ring leader base current steps)
    (hlt : steps < n - 1)
    (hfree :
      PPLLPpsiLeaderCreationRepair.BulletTwoFreeAwayFrom current leader) :
    let D := localStep ring
      (wallSweepBirthSignalZeroPathStallTransition
        hpsi kappa tau) current (groupOffset ring leader steps)
    PPLLPpsiLeaderCreationRepair.BulletTwoFreeAwayFrom D leader ∧
      clockwiseMobileDummyRank ring leader D ≤
        clockwiseMobileDummyRank ring leader current := by
  let e := groupOffset ring leader steps
  let j := groupOffset ring leader (steps + 1)
  let Told :=
    wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
      hpsi kappa tau
  let Tnew := wallSweepBirthSignalZeroPathStallTransition
    hpsi kappa tau
  let Dold := localStep ring Told current e
  let Dnew := localStep ring Tnew current e
  have hnpos : 0 < n := by omega
  have heBound : steps < n := by omega
  have hjBound : steps + 1 < n := by omega
  have hneighbor : ring.rightNeighbor e = j := by
    simpa [e, j] using rightNeighbor_groupOffset ring leader steps
  have heNotLeader : e ≠ leader := by
    have hne := groupOffset_ne_of_lt ring leader heBound
      hnpos (Nat.ne_of_gt hstate.steps_pos)
    exact fun heq =>
      hne (heq.trans (groupOffset_zero_eq ring leader).symm)
  have hjNotLeader : j ≠ leader := by
    have hne := groupOffset_ne_of_lt ring leader hjBound
      hnpos (Nat.ne_of_gt (Nat.zero_lt_succ steps))
    exact fun heq =>
      hne (heq.trans (groupOffset_zero_eq ring leader).symm)
  have hrightFollower :
      (current (ring.rightNeighbor e)).core.erase.core.leader = false := by
    rw [hneighbor]
    exact hstate.unique_leader j hjNotLeader
  have hfreeOld := resetAwareFollower_localStep_bulletTwoFreeAwayFrom
    hpsi ring hn current e leader hstate.no_active
      (hstate.unique_leader e heNotLeader) hstate.frontier_reset
      hrightFollower hfree heNotLeader
      (by simpa [hneighbor] using hjNotLeader)
  change PPLLPpsiLeaderCreationRepair.BulletTwoFreeAwayFrom
    Dold leader at hfreeOld
  have hrankOld := hstate.mobileDummyRank_le
    hpsi ring hn leader base current steps hlt hfree
  change clockwiseMobileDummyRank ring leader Dold ≤
    clockwiseMobileDummyRank ring leader current at hrankOld
  have heq : Dnew = Dold := by
    simpa only [Dnew, Dold, Tnew, Told, e] using
      hstate.localStep_birthSignalZero_eq_resetProbe
        hpsi ring hn leader base current steps hlt
  change PPLLPpsiLeaderCreationRepair.BulletTwoFreeAwayFrom
      Dnew leader ∧
    clockwiseMobileDummyRank ring leader Dnew ≤
      clockwiseMobileDummyRank ring leader current
  rw [heq]
  exact ⟨hfreeOld, hrankOld⟩

/-- The two leader-edge interactions used for a reset restart frame every
mobile dummy bit.  Only the root and its first outgoing follower can change. -/
theorem two_step_reseed_mobileDummyRank_eq
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (leader : Fin n) (current : EConfig n psi kappa tau) :
    let T :=
      wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
        hpsi kappa tau
    let D := runLocalSchedule ring T current [leader, leader]
    clockwiseMobileDummyRank ring leader D =
      clockwiseMobileDummyRank ring leader current := by
  let T := wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
    hpsi kappa tau
  let D := runLocalSchedule ring T current [leader, leader]
  have hoffsetOne : groupOffset ring leader 1 =
      ring.rightNeighbor leader := by
    have hnext := rightNeighbor_groupOffset ring leader 0
    rw [groupOffset_zero_eq] at hnext
    simpa using hnext.symm
  apply clockwiseMobileDummyRank_eq_of_bullets
    ring leader current D
  intro k hkOne hkBound
  apply congrArg
    (fun u : ExpiringAgentState psi kappa tau =>
      u.core.erase.core.bullet)
  change runLocalSchedule ring T current [leader, leader]
      (groupOffset ring leader k) =
    current (groupOffset ring leader k)
  apply runLocalSchedule_two_same_off_edge
  · have hk0 : groupOffset ring leader k ≠
        groupOffset ring leader 0 := by
      apply groupOffset_ne_of_lt ring leader hkBound (by omega)
      omega
    simpa [groupOffset_zero_eq] using hk0
  · rw [← hoffsetOne]
    apply groupOffset_ne_of_lt ring leader hkBound (by omega)
    omega

set_option maxHeartbeats 2000000 in
/-- The two leader-edge restart interactions frame every mobile live-bullet
bit.  Only the named root and its immediate outgoing follower can change. -/
theorem two_step_reseed_mobileLiveRank_eq
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (leader : Fin n) (current : EConfig n psi kappa tau) :
    let T :=
      wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
        hpsi kappa tau
    let D := runLocalSchedule ring T current [leader, leader]
    clockwiseMobileLiveRank ring leader D =
      clockwiseMobileLiveRank ring leader current := by
  let T := wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
    hpsi kappa tau
  let D := runLocalSchedule ring T current [leader, leader]
  have hoffsetOne : groupOffset ring leader 1 =
      ring.rightNeighbor leader := by
    have hnext := rightNeighbor_groupOffset ring leader 0
    rw [groupOffset_zero_eq] at hnext
    simpa using hnext.symm
  apply clockwiseMobileLiveRank_eq_of_bullets
    ring leader current D
  intro k hkOne hkBound
  apply congrArg
    (fun u : ExpiringAgentState psi kappa tau =>
      u.core.erase.core.bullet)
  change runLocalSchedule ring T current [leader, leader]
      (groupOffset ring leader k) =
    current (groupOffset ring leader k)
  apply runLocalSchedule_two_same_off_edge
  · have hk0 : groupOffset ring leader k ≠
        groupOffset ring leader 0 := by
      apply groupOffset_ne_of_lt ring leader hkBound (by omega)
      omega
    simpa [groupOffset_zero_eq] using hk0
  · rw [← hoffsetOne]
    apply groupOffset_ne_of_lt ring leader hkBound (by omega)
    omega

/-- Appending the two leader reseed interactions still preserves the mobile
live rank, since those interactions touch only offsets zero and one. -/
theorem
    ResetAwareNormalizedPrefixState.follower_then_two_step_reseed_mobileLiveRank_eq_of_visited_free
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (leader : Fin n) (base current : EConfig n psi kappa tau)
    (steps : Nat)
    (hstate : ResetAwareNormalizedPrefixState
      hpsi ring leader base current steps)
    (hlt : steps < n - 1)
    (hvisited : VisitedPrefixLiveFree ring leader current steps)
    (hrightNotLive :
      (current (groupOffset ring leader (steps + 1))).core.erase.core.bullet ≠
        ⟨2, by omega⟩) :
    let e := groupOffset ring leader steps
    let T := wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
      hpsi kappa tau
    let D := runLocalSchedule ring T current [e, leader, leader]
    clockwiseMobileLiveRank ring leader D =
      clockwiseMobileLiveRank ring leader current := by
  let e := groupOffset ring leader steps
  let T := wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
    hpsi kappa tau
  let C1 := localStep ring T current e
  let D := runLocalSchedule ring T C1 [leader, leader]
  have hfirst := hstate.mobileLiveRank_eq_of_responder_not_live
    hpsi ring hn leader base current steps hlt hvisited hrightNotLive
  change clockwiseMobileLiveRank ring leader C1 =
    clockwiseMobileLiveRank ring leader current at hfirst
  have hreseed := two_step_reseed_mobileLiveRank_eq
    hpsi ring hn leader C1
  change clockwiseMobileLiveRank ring leader D =
    clockwiseMobileLiveRank ring leader C1 at hreseed
  change clockwiseMobileLiveRank ring leader
      (runLocalSchedule ring T current [e, leader, leader]) =
    clockwiseMobileLiveRank ring leader current
  change clockwiseMobileLiveRank ring leader D =
    clockwiseMobileLiveRank ring leader current
  exact hreseed.trans hfirst

set_option maxHeartbeats 2000000 in
/-- One reset-aware follower step followed by the standard two leader-edge
restart interactions weakly decreases the mobile dummy rank. -/
theorem ResetAwareNormalizedPrefixState.follower_then_two_step_reseed_mobileDummyRank_le
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (leader : Fin n) (base current : EConfig n psi kappa tau)
    (steps : Nat)
    (hstate : ResetAwareNormalizedPrefixState
      hpsi ring leader base current steps)
    (hlt : steps < n - 1)
    (hfree :
      PPLLPpsiLeaderCreationRepair.BulletTwoFreeAwayFrom current leader) :
    let e := groupOffset ring leader steps
    let T := wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
      hpsi kappa tau
    let D := runLocalSchedule ring T current [e, leader, leader]
    clockwiseMobileDummyRank ring leader D ≤
      clockwiseMobileDummyRank ring leader current := by
  let e := groupOffset ring leader steps
  let T := wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
    hpsi kappa tau
  let C1 := localStep ring T current e
  let D := runLocalSchedule ring T C1 [leader, leader]
  have hfirst := hstate.mobileDummyRank_le
    hpsi ring hn leader base current steps hlt hfree
  change clockwiseMobileDummyRank ring leader C1 ≤
      clockwiseMobileDummyRank ring leader current at hfirst
  have hreseed := two_step_reseed_mobileDummyRank_eq
    hpsi ring hn leader C1
  change clockwiseMobileDummyRank ring leader D =
      clockwiseMobileDummyRank ring leader C1 at hreseed
  change clockwiseMobileDummyRank ring leader
      (runLocalSchedule ring T current [e, leader, leader]) ≤
    clockwiseMobileDummyRank ring leader current
  change clockwiseMobileDummyRank ring leader D ≤
    clockwiseMobileDummyRank ring leader current
  exact Nat.le_trans (Nat.le_of_eq hreseed) hfirst

set_option maxHeartbeats 2000000 in
/-- On the responder-dummy branch, the same follower-plus-reseed word strictly
decreases the mobile dummy rank while retaining the original root. -/
theorem ResetAwareNormalizedPrefixState.follower_then_two_step_reseed_mobileDummyRank_lt
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (leader : Fin n) (base current : EConfig n psi kappa tau)
    (steps : Nat)
    (hstate : ResetAwareNormalizedPrefixState
      hpsi ring leader base current steps)
    (hlt : steps < n - 1)
    (hfree :
      PPLLPpsiLeaderCreationRepair.BulletTwoFreeAwayFrom current leader)
    (hrightDummy :
      (current (groupOffset ring leader (steps + 1))).core.erase.core.bullet =
        ⟨1, by omega⟩) :
    let e := groupOffset ring leader steps
    let T := wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
      hpsi kappa tau
    let D := runLocalSchedule ring T current [e, leader, leader]
    clockwiseMobileDummyRank ring leader D <
      clockwiseMobileDummyRank ring leader current := by
  let e := groupOffset ring leader steps
  let T := wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
    hpsi kappa tau
  let C1 := localStep ring T current e
  let D := runLocalSchedule ring T C1 [leader, leader]
  have hfirst := hstate.mobileDummyRank_lt_of_responder_dummy
    hpsi ring hn leader base current steps hlt hfree hrightDummy
  change clockwiseMobileDummyRank ring leader C1 <
      clockwiseMobileDummyRank ring leader current at hfirst
  have hreseed := two_step_reseed_mobileDummyRank_eq
    hpsi ring hn leader C1
  change clockwiseMobileDummyRank ring leader D =
      clockwiseMobileDummyRank ring leader C1 at hreseed
  change clockwiseMobileDummyRank ring leader
      (runLocalSchedule ring T current [e, leader, leader]) <
    clockwiseMobileDummyRank ring leader current
  change clockwiseMobileDummyRank ring leader D <
    clockwiseMobileDummyRank ring leader current
  exact hreseed.symm ▸ hfirst

set_option maxHeartbeats 2000000 in
/-- A live-bullet follower step followed by the standard two leader-edge
restart interactions strictly decreases the mobile live rank measured from
the same physical root.  Root survival is a separate scheduler premise. -/
theorem ResetAwareNormalizedPrefixState.follower_then_two_step_reseed_mobileLiveRank_lt
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (leader : Fin n) (base current : EConfig n psi kappa tau)
    (steps : Nat)
    (hstate : ResetAwareNormalizedPrefixState
      hpsi ring leader base current steps)
    (hlt : steps < n - 1)
    (hrightLive :
      (current (groupOffset ring leader (steps + 1))).core.erase.core.bullet =
        ⟨2, by omega⟩) :
    let e := groupOffset ring leader steps
    let T := wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
      hpsi kappa tau
    let D := runLocalSchedule ring T current [e, leader, leader]
    clockwiseMobileLiveRank ring leader D <
      clockwiseMobileLiveRank ring leader current := by
  let e := groupOffset ring leader steps
  let T := wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
    hpsi kappa tau
  let C1 := localStep ring T current e
  let D := runLocalSchedule ring T C1 [leader, leader]
  have hfirst := hstate.mobileLiveRank_lt_of_responder_live
    hpsi ring hn leader base current steps hlt hrightLive
  change clockwiseMobileLiveRank ring leader C1 <
      clockwiseMobileLiveRank ring leader current at hfirst
  have hreseed := two_step_reseed_mobileLiveRank_eq
    hpsi ring hn leader C1
  change clockwiseMobileLiveRank ring leader D =
      clockwiseMobileLiveRank ring leader C1 at hreseed
  change clockwiseMobileLiveRank ring leader
      (runLocalSchedule ring T current [e, leader, leader]) <
    clockwiseMobileLiveRank ring leader current
  change clockwiseMobileLiveRank ring leader D <
    clockwiseMobileLiveRank ring leader current
  exact hreseed.symm ▸ hfirst

set_option maxHeartbeats 2000000 in
/-- From the exact collision aftermath needed by the scheduler, two
interactions of the same named leader edge re-establish an authenticated reset
handoff.  The invariant needed for recursion is not global live-bullet
freedom: a live bullet may remain at the leader, but no follower can acquire
one. -/
theorem two_step_reseed_of_ready
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (leader : Fin n) (current : EConfig n psi kappa tau)
    (hnoActive : NoActiveDeletion current)
    (hunique : hasUniqueLeader n
      (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig current))
    (hleader : (current leader).core.erase.core.leader = true)
    (hjFollower :
      (current (ring.rightNeighbor leader)).core.erase.core.leader = false)
    (hfree :
      PPLLPpsiLeaderCreationRepair.BulletTwoFreeAwayFrom current leader) :
    let T :=
      wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
        hpsi kappa tau
    let D := runLocalSchedule ring T current [leader, leader]
    PPLLPpsiLeaderCreationRepair.OutgoingResetFrontierUniqueLeaderAt
        hpsi ring D leader ∧
      PPLLPpsiLeaderCreationRepair.BulletTwoFreeAwayFrom D leader := by
  let j := ring.rightNeighbor leader
  have hje : j ≠ leader :=
    rightNeighbor_ne_self_of_one_lt ring hn leader
  have hsafe :
      (current j).core.erase.core.bullet = ⟨2, by omega⟩ →
        (current leader).core.erase.core.shield = true :=
    PPLLPpsiLeaderCreationRepair.edge_safe_of_bulletTwoFreeAwayFrom
      current leader j hfree hje
  let Tnew :=
    wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
      hpsi kappa tau
  let Told := wallSweepPreCheckResetLeaderSinkPathStallTransition
    hpsi kappa tau
  let Dnew := localStep ring Tnew current leader
  let Dold := localStep ring Told current leader
  have hpairFirst :
      Tnew (current leader) (current j) =
        Told (current leader) (current j) := by
    simpa [Tnew, Told, j] using
      (wallSweepResetProbePreCheckResetLeaderSinkPathStall_eq_of_left_leader
        hpsi kappa tau (current leader) (current j) hleader)
  have hD : Dnew = Dold := by
    exact localStep_eq_of_pair_eq
      ring Tnew Told current leader (by simpa [j] using hpairFirst)
  have hnormalOld :=
    PPLLPpsiLeaderCreationRepair.leaderStep_to_normalizedOutgoingUniqueLeaderAt
      hpsi ring hn current leader hnoActive hunique
        hleader (by simpa [j] using hjFollower)
        (by simpa [j] using hsafe)
  change PPLLPpsiLeaderCreationRepair.NormalizedOutgoingUniqueLeaderAt
    hpsi ring Dold leader at hnormalOld
  have hnormalNew :
      PPLLPpsiLeaderCreationRepair.NormalizedOutgoingUniqueLeaderAt
        hpsi ring Dnew leader := by
    rw [hD]
    exact hnormalOld
  have hfreeOld := leaderSink_localStep_bulletTwoFreeAwayFrom
    hpsi ring hn current leader hnoActive hfree
  change PPLLPpsiLeaderCreationRepair.BulletTwoFreeAwayFrom
    Dold leader at hfreeOld
  have hfreeNew :
      PPLLPpsiLeaderCreationRepair.BulletTwoFreeAwayFrom
        Dnew leader := by
    rw [hD]
    exact hfreeOld
  have hnormalFields := hnormalNew
  obtain ⟨hnoActiveD, _huniqueD, hleaderD, _hjFollowerD,
      _halignedD, _hleftProbeD, _hrightProbeD,
      _hleftNeutralD, _hrightNeutralD, _hleftResetD,
      _hleftEchoD, _hrightEchoD, _hsafeD⟩ := hnormalFields
  let Enew := localStep ring Tnew Dnew leader
  let Eold := localStep ring Told Dnew leader
  have hpairSecond :
      Tnew (Dnew leader) (Dnew j) =
        Told (Dnew leader) (Dnew j) := by
    simpa [Tnew, Told, j] using
      (wallSweepResetProbePreCheckResetLeaderSinkPathStall_eq_of_left_leader
        hpsi kappa tau (Dnew leader) (Dnew j) hleaderD)
  have hE : Enew = Eold := by
    exact localStep_eq_of_pair_eq
      ring Tnew Told Dnew leader (by simpa [j] using hpairSecond)
  have hfrontierOld :=
    PPLLPpsiLeaderCreationRepair.normalizedOutgoingUniqueLeaderAt_replay_reset_handoff
      hpsi ring hn Dnew leader hnormalNew
  change PPLLPpsiLeaderCreationRepair.OutgoingResetFrontierUniqueLeaderAt
    hpsi ring Eold leader at hfrontierOld
  have hfrontierNew :
      PPLLPpsiLeaderCreationRepair.OutgoingResetFrontierUniqueLeaderAt
        hpsi ring Enew leader := by
    rw [hE]
    exact hfrontierOld
  have hfreeEOld := leaderSink_localStep_bulletTwoFreeAwayFrom
    hpsi ring hn Dnew leader hnoActiveD hfreeNew
  change PPLLPpsiLeaderCreationRepair.BulletTwoFreeAwayFrom
    Eold leader at hfreeEOld
  have hfreeENew :
      PPLLPpsiLeaderCreationRepair.BulletTwoFreeAwayFrom
        Enew leader := by
    rw [hE]
    exact hfreeEOld
  simpa [Tnew, Dnew, Enew, runLocalSchedule] using
    And.intro hfrontierNew hfreeENew

set_option maxHeartbeats 2000000 in
/-- Two interactions of the named leader edge rebuild the reset frontier when
only the immediate follower is known non-live.  Remote live bullets are
untouched by this structural theorem; the output immediate follower remains
non-live by responder-origin exactness. -/
theorem two_step_reseed_frontier_of_firstFollower_free
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (leader : Fin n) (current : EConfig n psi kappa tau)
    (hnoActive : NoActiveDeletion current)
    (hunique : hasUniqueLeader n
      (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig current))
    (hleader : (current leader).core.erase.core.leader = true)
    (hjFollower :
      (current (ring.rightNeighbor leader)).core.erase.core.leader = false)
    (hjNotLive :
      (current (ring.rightNeighbor leader)).core.erase.core.bullet ≠
        ⟨2, by omega⟩) :
    let T :=
      wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
        hpsi kappa tau
    let D := runLocalSchedule ring T current [leader, leader]
    PPLLPpsiLeaderCreationRepair.OutgoingResetFrontierUniqueLeaderAt
        hpsi ring D leader ∧
      (D (ring.rightNeighbor leader)).core.erase.core.bullet ≠
        ⟨2, by omega⟩ ∧
      (D leader).core.erase.core.signal_B = ⟨0, by omega⟩ := by
  let j := ring.rightNeighbor leader
  have hje : j ≠ leader :=
    rightNeighbor_ne_self_of_one_lt ring hn leader
  have hsafe :
      (current j).core.erase.core.bullet = ⟨2, by omega⟩ →
        (current leader).core.erase.core.shield = true := by
    intro hlive
    exact (hjNotLive (by simpa [j] using hlive)).elim
  let Tnew :=
    wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
      hpsi kappa tau
  let Told := wallSweepPreCheckResetLeaderSinkPathStallTransition
    hpsi kappa tau
  let Dnew := localStep ring Tnew current leader
  let Dold := localStep ring Told current leader
  have hpairFirst :
      Tnew (current leader) (current j) =
        Told (current leader) (current j) := by
    simpa [Tnew, Told, j] using
      (wallSweepResetProbePreCheckResetLeaderSinkPathStall_eq_of_left_leader
        hpsi kappa tau (current leader) (current j) hleader)
  have hD : Dnew = Dold :=
    localStep_eq_of_pair_eq ring Tnew Told current leader
      (by simpa [j] using hpairFirst)
  have hnormalOld :=
    PPLLPpsiLeaderCreationRepair.leaderStep_to_normalizedOutgoingUniqueLeaderAt
      hpsi ring hn current leader hnoActive hunique hleader
        (by simpa [j] using hjFollower) (by simpa [j] using hsafe)
  change PPLLPpsiLeaderCreationRepair.NormalizedOutgoingUniqueLeaderAt
    hpsi ring Dold leader at hnormalOld
  have hnormalNew :
      PPLLPpsiLeaderCreationRepair.NormalizedOutgoingUniqueLeaderAt
        hpsi ring Dnew leader := by
    rw [hD]
    exact hnormalOld
  have hfirstFreeOld :=
    leaderSink_localStep_right_not_live_of_right_not_live
      hpsi ring hn current leader hnoActive hjNotLive
  change (Dold j).core.erase.core.bullet ≠ ⟨2, by omega⟩ at hfirstFreeOld
  have hfirstFreeNew :
      (Dnew j).core.erase.core.bullet ≠ ⟨2, by omega⟩ := by
    rw [hD]
    exact hfirstFreeOld
  have hnormalFields := hnormalNew
  obtain ⟨hnoActiveD, _huniqueD, hleaderD, _hjFollowerD,
      _halignedD, _hleftProbeD, _hrightProbeD,
      _hleftNeutralD, _hrightNeutralD, _hleftResetD,
      _hleftEchoD, _hrightEchoD, _hsafeD⟩ := hnormalFields
  let Enew := localStep ring Tnew Dnew leader
  let Eold := localStep ring Told Dnew leader
  have hpairSecond :
      Tnew (Dnew leader) (Dnew j) =
        Told (Dnew leader) (Dnew j) := by
    simpa [Tnew, Told, j] using
      (wallSweepResetProbePreCheckResetLeaderSinkPathStall_eq_of_left_leader
        hpsi kappa tau (Dnew leader) (Dnew j) hleaderD)
  have hE : Enew = Eold :=
    localStep_eq_of_pair_eq ring Tnew Told Dnew leader
      (by simpa [j] using hpairSecond)
  have hfrontierOld :=
    PPLLPpsiLeaderCreationRepair.normalizedOutgoingUniqueLeaderAt_replay_reset_handoff
      hpsi ring hn Dnew leader hnormalNew
  change PPLLPpsiLeaderCreationRepair.OutgoingResetFrontierUniqueLeaderAt
    hpsi ring Eold leader at hfrontierOld
  have hfrontierNew :
      PPLLPpsiLeaderCreationRepair.OutgoingResetFrontierUniqueLeaderAt
        hpsi ring Enew leader := by
    rw [hE]
    exact hfrontierOld
  have hsecondFreeOld :=
    leaderSink_localStep_right_not_live_of_right_not_live
      hpsi ring hn Dnew leader hnoActiveD (by simpa [j] using hfirstFreeNew)
  change (Eold j).core.erase.core.bullet ≠ ⟨2, by omega⟩ at hsecondFreeOld
  have hsecondFreeNew :
      (Enew j).core.erase.core.bullet ≠ ⟨2, by omega⟩ := by
    rw [hE]
    exact hsecondFreeOld
  have hsignalNew :
      (Enew leader).core.erase.core.signal_B = ⟨0, by omega⟩ := by
    exact resetAwareLeader_localStep_signal_zero
      hpsi ring Dnew leader hnoActiveD hleaderD
  simpa [Tnew, Dnew, Enew, runLocalSchedule, j] using
    And.intro hfrontierNew (And.intro hsecondFreeNew hsignalNew)

set_option maxHeartbeats 2000000 in
/-- Two named-leader interactions rebuild the authenticated frontier when the
immediate follower is live but the leader is already shielded.  The death
branch of `resetAwareLeader_liveResponder_frontier_or_leaderless` is excluded
by the shield, and the live responder remains parked at the first follower. -/
theorem two_step_reseed_shieldedLiveRetryReady_of_firstFollower_live
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (leader : Fin n) (current : EConfig n psi kappa tau)
    (hnoActive : NoActiveDeletion current)
    (hunique : hasUniqueLeader n
      (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig current))
    (hleader : (current leader).core.erase.core.leader = true)
    (hjFollower :
      (current (ring.rightNeighbor leader)).core.erase.core.leader = false)
    (hjLive :
      (current (ring.rightNeighbor leader)).core.erase.core.bullet =
        ⟨2, by omega⟩)
    (hleaderShield :
      (current leader).core.erase.core.shield = true) :
    let T :=
      wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
        hpsi kappa tau
    ResetAwareShieldedLiveRetryReady hpsi ring leader
      (runLocalSchedule ring T current [leader, leader]) := by
  let j := ring.rightNeighbor leader
  let T :=
    wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
      hpsi kappa tau
  let D := localStep ring T current leader
  let E := localStep ring T D leader
  have hopen : WallPriorityOpen (current leader) (current j) := by
    simpa [j] using
      WallPriorityOpen.of_noActiveDeletion current hnoActive ring leader
  have hsafe :
      (current j).core.erase.core.bullet = ⟨2, by omega⟩ →
        (current leader).core.erase.core.shield = true := by
    intro _
    exact hleaderShield
  have hsurvivesOld :=
    wallSweepPreCheckResetLeaderSinkPathStall_priority_open_initiator_survives_of_safe
      hpsi (current leader) (current j) hopen hleader
        (by simpa [j] using hjFollower) hsafe
  have hsurvivesPair :
      (T (current leader) (current j)).1.core.erase.core.leader = true := by
    change
      (wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
        hpsi kappa tau (current leader) (current j)).1.core.erase.core.leader =
          true
    rw [wallSweepResetProbePreCheckResetLeaderSinkPathStall_eq_of_left_leader
      hpsi kappa tau (current leader) (current j) hleader]
    exact hsurvivesOld
  have hsurvivesD : (D leader).core.erase.core.leader = true := by
    simpa [D, T, j, localStep] using hsurvivesPair
  have hcycle := resetAwareLeader_liveResponder_frontier_or_leaderless
    hpsi ring hn current leader hnoActive hunique hleader hjLive
  change
    ((PPLLPpsiLeaderCreationRepair.OutgoingResetFrontierUniqueLeaderAt
          hpsi ring E leader ∧
        (E j).core.erase.core.bullet = ⟨2, by omega⟩ ∧
        (E leader).core.erase.core.label =
          (current leader).core.erase.core.label ∧
        (E leader).core.erase.core.signal_B = ⟨0, by omega⟩) ∨
      (RawLeaderless
          (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig D) ∧
        PPLLPpsiLeaderCreationRepair.bulletTwoCount D <
          PPLLPpsiLeaderCreationRepair.bulletTwoCount current)) at hcycle
  rcases hcycle with hfrontier | hleaderless
  · change ResetAwareShieldedLiveRetryReady hpsi ring leader
      (runLocalSchedule ring T current [leader, leader])
    simpa [ResetAwareShieldedLiveRetryReady, T, D, E,
      runLocalSchedule, j] using
      And.intro hfrontier.1
        (And.intro hfrontier.2.1 hfrontier.2.2.2)
  · have hfalse := hleaderless.1 leader
    change (D leader).core.erase.core.leader = false at hfalse
    rw [hsurvivesD] at hfalse
    contradiction

set_option maxHeartbeats 2000000 in
/-- Two same-leader reseed interactions cannot increase global live-bullet
mass when the leader is shielded and its source signal is already zero.  The
shield guarantees that the first interaction retains the leader, and that
interaction supplies the zero source signal needed by the second. -/
theorem two_step_reseed_bulletTwoCount_le_of_shielded_signal_zero
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (leader : Fin n) (current : EConfig n psi kappa tau)
    (hnoActive : NoActiveDeletion current)
    (hleader : (current leader).core.erase.core.leader = true)
    (hjFollower :
      (current (ring.rightNeighbor leader)).core.erase.core.leader = false)
    (hleaderShield : (current leader).core.erase.core.shield = true)
    (hleaderSignalZero :
      (current leader).core.erase.core.signal_B = ⟨0, by omega⟩) :
    let T :=
      wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
        hpsi kappa tau
    PPLLPpsiLeaderCreationRepair.bulletTwoCount
        (runLocalSchedule ring T current [leader, leader]) ≤
      PPLLPpsiLeaderCreationRepair.bulletTwoCount current := by
  let j := ring.rightNeighbor leader
  let T :=
    wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
      hpsi kappa tau
  let D := localStep ring T current leader
  let E := localStep ring T D leader
  have hopen : WallPriorityOpen (current leader) (current j) := by
    simpa [j] using
      WallPriorityOpen.of_noActiveDeletion current hnoActive ring leader
  have hsafe :
      (current j).core.erase.core.bullet = ⟨2, by omega⟩ →
        (current leader).core.erase.core.shield = true := by
    intro _
    exact hleaderShield
  have hsurvivesOld :=
    wallSweepPreCheckResetLeaderSinkPathStall_priority_open_initiator_survives_of_safe
      hpsi (current leader) (current j) hopen hleader
        (by simpa [j] using hjFollower) hsafe
  have hsurvivesPair :
      (T (current leader) (current j)).1.core.erase.core.leader = true := by
    change
      (wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
        hpsi kappa tau (current leader) (current j)).1.core.erase.core.leader =
          true
    rw [wallSweepResetProbePreCheckResetLeaderSinkPathStall_eq_of_left_leader
      hpsi kappa tau (current leader) (current j) hleader]
    exact hsurvivesOld
  have hleaderD : (D leader).core.erase.core.leader = true := by
    simpa [D, T, j, localStep] using hsurvivesPair
  have hfirstLe := resetAwareLeader_signalZero_localStep_bulletTwoCount_le
    hpsi ring hn current leader hnoActive hleader hleaderSignalZero
  change PPLLPpsiLeaderCreationRepair.bulletTwoCount D ≤
    PPLLPpsiLeaderCreationRepair.bulletTwoCount current at hfirstLe
  have hnoActiveD := resetAwareLeader_localStep_noActive
    hpsi ring hn current leader hnoActive hleader
  change NoActiveDeletion D at hnoActiveD
  have hsignalD := resetAwareLeader_localStep_signal_zero
    hpsi ring current leader hnoActive hleader
  change (D leader).core.erase.core.signal_B = ⟨0, by omega⟩ at hsignalD
  have hsecondLe := resetAwareLeader_signalZero_localStep_bulletTwoCount_le
    hpsi ring hn D leader hnoActiveD hleaderD hsignalD
  change PPLLPpsiLeaderCreationRepair.bulletTwoCount E ≤
    PPLLPpsiLeaderCreationRepair.bulletTwoCount D at hsecondLe
  change PPLLPpsiLeaderCreationRepair.bulletTwoCount
      (runLocalSchedule ring T current [leader, leader]) ≤
    PPLLPpsiLeaderCreationRepair.bulletTwoCount current
  simpa [T, D, E, runLocalSchedule] using
    Nat.le_trans hsecondLe hfirstLe

set_option maxHeartbeats 2000000 in
/-- Replaying the named leader edge twice preserves a shielded initiator.
The first interaction preserves global deletion inactivity and leaves the
responder a follower, so the same anchor contract applies to the replay. -/
theorem two_step_reseed_initiator_anchor
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (leader : Fin n) (current : EConfig n psi kappa tau)
    (hnoActive : NoActiveDeletion current)
    (hanchor : InitiatorAnchor
      (current leader).core.erase.core)
    (hjFollower :
      (current (ring.rightNeighbor leader)).core.erase.core.leader = false) :
    let T :=
      wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
        hpsi kappa tau
    InitiatorAnchor
      ((runLocalSchedule ring T current [leader, leader]) leader).core.erase.core := by
  let T := wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
    hpsi kappa tau
  let D := localStep ring T current leader
  let E := localStep ring T D leader
  have hanchorD := resetAwareLeader_localStep_initiator_anchor
    hpsi ring current leader hnoActive hanchor hjFollower
  change InitiatorAnchor (D leader).core.erase.core at hanchorD
  have hnoActiveD := resetAwareLeader_localStep_noActive
    hpsi ring hn current leader hnoActive hanchor.1
  change NoActiveDeletion D at hnoActiveD
  have hjFollowerD := resetAwareLeader_localStep_right_follower
    hpsi ring hn current leader hnoActive hanchor.1 hjFollower
  change
    (D (ring.rightNeighbor leader)).core.erase.core.leader = false at hjFollowerD
  have hanchorE := resetAwareLeader_localStep_initiator_anchor
    hpsi ring D leader hnoActiveD hanchorD hjFollowerD
  change InitiatorAnchor (E leader).core.erase.core at hanchorE
  simpa [T, D, E, runLocalSchedule] using hanchorE

set_option maxHeartbeats 2000000 in
/-- The same two-edge shielded replay frames the named leader's label without
requiring any global live-bullet-freedom premise. -/
theorem two_step_reseed_leader_label_of_anchor
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (leader : Fin n) (current : EConfig n psi kappa tau)
    (hnoActive : NoActiveDeletion current)
    (hanchor : InitiatorAnchor
      (current leader).core.erase.core)
    (hjFollower :
      (current (ring.rightNeighbor leader)).core.erase.core.leader = false) :
    let T :=
      wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
        hpsi kappa tau
    ((runLocalSchedule ring T current [leader, leader])
      leader).core.erase.core.label =
        (current leader).core.erase.core.label := by
  let T := wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
    hpsi kappa tau
  let D := localStep ring T current leader
  let E := localStep ring T D leader
  have hlabelD := resetAwareLeader_localStep_label_eq
    hpsi ring current leader hnoActive hanchor.1 hjFollower
  change (D leader).core.erase.core.label =
    (current leader).core.erase.core.label at hlabelD
  have hanchorD := resetAwareLeader_localStep_initiator_anchor
    hpsi ring current leader hnoActive hanchor hjFollower
  change InitiatorAnchor (D leader).core.erase.core at hanchorD
  have hnoActiveD := resetAwareLeader_localStep_noActive
    hpsi ring hn current leader hnoActive hanchor.1
  change NoActiveDeletion D at hnoActiveD
  have hjFollowerD := resetAwareLeader_localStep_right_follower
    hpsi ring hn current leader hnoActive hanchor.1 hjFollower
  change
    (D (ring.rightNeighbor leader)).core.erase.core.leader = false at hjFollowerD
  have hlabelE := resetAwareLeader_localStep_label_eq
    hpsi ring D leader hnoActiveD hanchorD.1 hjFollowerD
  change (E leader).core.erase.core.label =
    (D leader).core.erase.core.label at hlabelE
  simpa [T, D, E, runLocalSchedule] using hlabelE.trans hlabelD

/-- The shielded-live boundary is closed by the same two-edge leader reseed
word used after every follower collision. -/
theorem ResetAwareShieldedLiveRetryReady.two_step_reseed
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (leader : Fin n) (current : EConfig n psi kappa tau)
    (hready : ResetAwareShieldedLiveRetryReady
      hpsi ring leader current) :
    let T :=
      wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
        hpsi kappa tau
    ResetAwareShieldedLiveRetryReady hpsi ring leader
      (runLocalSchedule ring T current [leader, leader]) := by
  have hshield := hready.leader_shield
  obtain ⟨hfrontier, hrightLive, _hsignal⟩ := hready
  obtain ⟨hnoActive, hunique, hleader, hrightFollower,
      _haligned, _hleftProbe, _hrightProbe,
      _hleftNeutral, _hrightNeutral, _hleftReset, _hrightReset,
      _hleftEcho, _hrightEcho, _hsafe⟩ := hfrontier
  exact two_step_reseed_shieldedLiveRetryReady_of_firstFollower_live
    hpsi ring hn leader current hnoActive hunique hleader
      hrightFollower hrightLive hshield

/-- The shielded-live boundary's two-edge reseed is also globally
live-bullet-mass nonincreasing. -/
theorem ResetAwareShieldedLiveRetryReady.two_step_reseed_bulletTwoCount_le
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (leader : Fin n) (current : EConfig n psi kappa tau)
    (hready : ResetAwareShieldedLiveRetryReady
      hpsi ring leader current) :
    let T :=
      wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
        hpsi kappa tau
    PPLLPpsiLeaderCreationRepair.bulletTwoCount
        (runLocalSchedule ring T current [leader, leader]) ≤
      PPLLPpsiLeaderCreationRepair.bulletTwoCount current := by
  have hshield := hready.leader_shield
  obtain ⟨hfrontier, _hrightLive, hsignal⟩ := hready
  obtain ⟨hnoActive, _hunique, hleader, hrightFollower,
      _haligned, _hleftProbe, _hrightProbe,
      _hleftNeutral, _hrightNeutral, _hleftReset, _hrightReset,
      _hleftEcho, _hrightEcho, _hsafe⟩ := hfrontier
  exact two_step_reseed_bulletTwoCount_le_of_shielded_signal_zero
    hpsi ring hn leader current hnoActive hleader hrightFollower
      hshield hsignal

/-- Scheduler-facing packaging of the weakened two-step reseed. -/
theorem two_step_reseed_liveRetryReady_of_firstFollower_free
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (leader : Fin n) (current : EConfig n psi kappa tau)
    (hnoActive : NoActiveDeletion current)
    (hunique : hasUniqueLeader n
      (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig current))
    (hleader : (current leader).core.erase.core.leader = true)
    (hjFollower :
      (current (ring.rightNeighbor leader)).core.erase.core.leader = false)
    (hjNotLive :
      (current (ring.rightNeighbor leader)).core.erase.core.bullet ≠
        ⟨2, by omega⟩) :
    let T :=
      wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
        hpsi kappa tau
    let D := runLocalSchedule ring T current [leader, leader]
    ResetAwareLiveRetryReady hpsi ring leader D := by
  simpa [ResetAwareLiveRetryReady] using
    two_step_reseed_frontier_of_firstFollower_free
      hpsi ring hn leader current hnoActive hunique hleader
        hjFollower hjNotLive

set_option maxHeartbeats 2000000 in
/-- If the named leader starts the weakened two-step reseed with a zero
absence signal, the complete reseed cannot increase the global live-bullet
count.  The first interaction preserves the leader and clears its signal;
the second interaction therefore satisfies the same zero-signal bound. -/
theorem two_step_reseed_bulletTwoCount_le_of_firstFollower_free_signal_zero
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (leader : Fin n) (current : EConfig n psi kappa tau)
    (hnoActive : NoActiveDeletion current)
    (hunique : hasUniqueLeader n
      (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig current))
    (hleader : (current leader).core.erase.core.leader = true)
    (hleaderSignalZero :
      (current leader).core.erase.core.signal_B = ⟨0, by omega⟩)
    (hjFollower :
      (current (ring.rightNeighbor leader)).core.erase.core.leader = false)
    (hjNotLive :
      (current (ring.rightNeighbor leader)).core.erase.core.bullet ≠
        ⟨2, by omega⟩) :
    let T :=
      wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
        hpsi kappa tau
    let D := runLocalSchedule ring T current [leader, leader]
    PPLLPpsiLeaderCreationRepair.bulletTwoCount D ≤
      PPLLPpsiLeaderCreationRepair.bulletTwoCount current := by
  let j := ring.rightNeighbor leader
  have hsafe :
      (current j).core.erase.core.bullet = ⟨2, by omega⟩ →
        (current leader).core.erase.core.shield = true := by
    intro hlive
    exact (hjNotLive (by simpa [j] using hlive)).elim
  let Tnew :=
    wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
      hpsi kappa tau
  let Told := wallSweepPreCheckResetLeaderSinkPathStallTransition
    hpsi kappa tau
  let Dnew := localStep ring Tnew current leader
  let Dold := localStep ring Told current leader
  have hpairFirst :
      Tnew (current leader) (current j) =
        Told (current leader) (current j) := by
    simpa [Tnew, Told, j] using
      (wallSweepResetProbePreCheckResetLeaderSinkPathStall_eq_of_left_leader
        hpsi kappa tau (current leader) (current j) hleader)
  have hD : Dnew = Dold :=
    localStep_eq_of_pair_eq ring Tnew Told current leader
      (by simpa [j] using hpairFirst)
  have hnormalOld :=
    PPLLPpsiLeaderCreationRepair.leaderStep_to_normalizedOutgoingUniqueLeaderAt
      hpsi ring hn current leader hnoActive hunique hleader
        (by simpa [j] using hjFollower) (by simpa [j] using hsafe)
  change PPLLPpsiLeaderCreationRepair.NormalizedOutgoingUniqueLeaderAt
    hpsi ring Dold leader at hnormalOld
  have hnormalNew :
      PPLLPpsiLeaderCreationRepair.NormalizedOutgoingUniqueLeaderAt
        hpsi ring Dnew leader := by
    rw [hD]
    exact hnormalOld
  obtain ⟨hnoActiveD, _huniqueD, hleaderD, _hjFollowerD,
      _halignedD, _hleftProbeD, _hrightProbeD,
      _hleftNeutralD, _hrightNeutralD, _hleftResetD,
      _hleftEchoD, _hrightEchoD, _hsafeD⟩ := hnormalNew
  have hfirstLe :
      PPLLPpsiLeaderCreationRepair.bulletTwoCount Dnew ≤
        PPLLPpsiLeaderCreationRepair.bulletTwoCount current := by
    exact resetAwareLeader_signalZero_localStep_bulletTwoCount_le
      hpsi ring hn current leader hnoActive hleader hleaderSignalZero
  have hsignalD :
      (Dnew leader).core.erase.core.signal_B = ⟨0, by omega⟩ := by
    exact resetAwareLeader_localStep_signal_zero
      hpsi ring current leader hnoActive hleader
  let Enew := localStep ring Tnew Dnew leader
  have hsecondLe :
      PPLLPpsiLeaderCreationRepair.bulletTwoCount Enew ≤
        PPLLPpsiLeaderCreationRepair.bulletTwoCount Dnew := by
    exact resetAwareLeader_signalZero_localStep_bulletTwoCount_le
      hpsi ring hn Dnew leader hnoActiveD hleaderD hsignalD
  have htotal :
      PPLLPpsiLeaderCreationRepair.bulletTwoCount Enew ≤
        PPLLPpsiLeaderCreationRepair.bulletTwoCount current :=
    Nat.le_trans hsecondLe hfirstLe
  simpa [Tnew, Dnew, Enew, runLocalSchedule] using htotal

set_option maxHeartbeats 2000000 in
/-- Two interactions from any unique shielded leader to its follower build
the prefix-closed shielded frontier.  The immediate follower is split only to
choose the existing frontier reconstruction theorem; anchor preservation is
uniform across both bullet cases. -/
theorem two_step_reseed_shieldedRetryReady_of_source_follower
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (leader : Fin n) (current : EConfig n psi kappa tau)
    (hnoActive : NoActiveDeletion current)
    (hunique : hasUniqueLeader n
      (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig current))
    (hanchor : InitiatorAnchor
      (current leader).core.erase.core)
    (hrightFollower :
      (current (ring.rightNeighbor leader)).core.erase.core.leader = false) :
    let T :=
      wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
        hpsi kappa tau
    ResetAwareShieldedRetryReady hpsi ring leader
      (runLocalSchedule ring T current [leader, leader]) := by
  let T := wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
    hpsi kappa tau
  let E := runLocalSchedule ring T current [leader, leader]
  have hanchorE := two_step_reseed_initiator_anchor
    hpsi ring hn leader current hnoActive hanchor hrightFollower
  change InitiatorAnchor (E leader).core.erase.core at hanchorE
  have hstruct :
      PPLLPpsiLeaderCreationRepair.OutgoingResetFrontierUniqueLeaderAt
          hpsi ring E leader ∧
        (E leader).core.erase.core.signal_B = ⟨0, by omega⟩ := by
    by_cases hrightLive :
        (current (ring.rightNeighbor leader)).core.erase.core.bullet =
          ⟨2, by omega⟩
    · have hlive :=
        two_step_reseed_shieldedLiveRetryReady_of_firstFollower_live
          hpsi ring hn leader current hnoActive hunique hanchor.1
            hrightFollower hrightLive hanchor.2
      change ResetAwareShieldedLiveRetryReady
        hpsi ring leader E at hlive
      exact ⟨hlive.1, hlive.2.2⟩
    · have hfree := two_step_reseed_frontier_of_firstFollower_free
        hpsi ring hn leader current hnoActive hunique hanchor.1
          hrightFollower hrightLive
      change
        PPLLPpsiLeaderCreationRepair.OutgoingResetFrontierUniqueLeaderAt
            hpsi ring E leader ∧
          (E (ring.rightNeighbor leader)).core.erase.core.bullet ≠
            ⟨2, by omega⟩ ∧
          (E leader).core.erase.core.signal_B = ⟨0, by omega⟩ at hfree
      exact ⟨hfree.1, hfree.2.2⟩
  change ResetAwareShieldedRetryReady hpsi ring leader
    (runLocalSchedule ring T current [leader, leader])
  change ResetAwareShieldedRetryReady hpsi ring leader E
  exact ⟨hstruct.1, hanchorE.2, hstruct.2⟩

/-- The prefix-closed shielded boundary is therefore closed by the same
two-edge word. -/
theorem ResetAwareShieldedRetryReady.two_step_reseed
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (leader : Fin n) (current : EConfig n psi kappa tau)
    (hready : ResetAwareShieldedRetryReady
      hpsi ring leader current) :
    let T :=
      wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
        hpsi kappa tau
    ResetAwareShieldedRetryReady hpsi ring leader
      (runLocalSchedule ring T current [leader, leader]) := by
  obtain ⟨hfrontier, hshield, _hsignal⟩ := hready
  obtain ⟨hnoActive, hunique, hleader, hrightFollower,
      _haligned, _hleftProbe, _hrightProbe,
      _hleftNeutral, _hrightNeutral, _hleftReset, _hrightReset,
      _hleftEcho, _hrightEcho, _hsafe⟩ := hfrontier
  exact two_step_reseed_shieldedRetryReady_of_source_follower
    hpsi ring hn leader current hnoActive hunique ⟨hleader, hshield⟩
      hrightFollower

/-- The same closed shielded round is globally live-bullet-mass
nonincreasing. -/
theorem ResetAwareShieldedRetryReady.two_step_reseed_bulletTwoCount_le
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (leader : Fin n) (current : EConfig n psi kappa tau)
    (hready : ResetAwareShieldedRetryReady
      hpsi ring leader current) :
    let T :=
      wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
        hpsi kappa tau
    PPLLPpsiLeaderCreationRepair.bulletTwoCount
        (runLocalSchedule ring T current [leader, leader]) ≤
      PPLLPpsiLeaderCreationRepair.bulletTwoCount current := by
  obtain ⟨hfrontier, hshield, hsignal⟩ := hready
  obtain ⟨hnoActive, _hunique, hleader, hrightFollower,
      _haligned, _hleftProbe, _hrightProbe,
      _hleftNeutral, _hrightNeutral, _hleftReset, _hrightReset,
      _hleftEcho, _hrightEcho, _hsafe⟩ := hfrontier
  exact two_step_reseed_bulletTwoCount_le_of_shielded_signal_zero
    hpsi ring hn leader current hnoActive hleader hrightFollower
      hshield hsignal

/-- Once the named initiator is already a leader, the birth-signal wrapper is
inert throughout the two-edge reseed.  The first old step preserves the
initiator anchor, so the same input guard applies to the replay. -/
theorem runLocalSchedule_birthSignalZero_two_reseed_eq
    (hpsi : psi > 0) (ring : DirectedRing n)
    (leader : Fin n) (current : EConfig n psi kappa tau)
    (hnoActive : NoActiveDeletion current)
    (hanchor : InitiatorAnchor
      (current leader).core.erase.core)
    (hrightFollower :
      (current (ring.rightNeighbor leader)).core.erase.core.leader = false) :
    runLocalSchedule ring
        (wallSweepBirthSignalZeroPathStallTransition
          hpsi kappa tau) current [leader, leader] =
      runLocalSchedule ring
        (wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
          hpsi kappa tau) current [leader, leader] := by
  let Told :=
    wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
      hpsi kappa tau
  let Tnew := wallSweepBirthSignalZeroPathStallTransition
    hpsi kappa tau
  let Dold := localStep ring Told current leader
  have hfirst : localStep ring Tnew current leader = Dold := by
    apply localStep_eq_of_pair_eq
    simpa [Tnew, Told] using
      wallSweepBirthSignalZeroPathStall_eq_of_left_leader
        hpsi kappa tau (current leader)
          (current (ring.rightNeighbor leader)) hanchor.1
  have hanchorD := resetAwareLeader_localStep_initiator_anchor
    hpsi ring current leader hnoActive hanchor hrightFollower
  change InitiatorAnchor (Dold leader).core.erase.core at hanchorD
  have hsecond : localStep ring Tnew Dold leader =
      localStep ring Told Dold leader := by
    apply localStep_eq_of_pair_eq
    simpa [Tnew, Told] using
      wallSweepBirthSignalZeroPathStall_eq_of_left_leader
        hpsi kappa tau (Dold leader)
          (Dold (ring.rightNeighbor leader)) hanchorD.1
  simpa [Tnew, Told, Dold, runLocalSchedule, hfirst] using hsecond

set_option maxHeartbeats 3000000 in
/-- A true-echo follower collision followed by the shielded two-edge replay
returns to the prefix-closed shielded frontier.  It strictly consumes the
canonical echo blocker and never increases global live-bullet mass. -/
theorem ResetAwareNormalizedPrefixState.collision_then_shielded_retry
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (leader : Fin n) (base current : EConfig n psi kappa tau)
    (steps : Nat)
    (hstate : ResetAwareNormalizedPrefixState
      hpsi ring leader base current steps)
    (hlt : steps < n - 1)
    (hrightEcho :
      (current (groupOffset ring leader (steps + 1))).core.erase.core.echo =
        true)
    (hrootShield : (current leader).core.erase.core.shield = true)
    (hrootSignalZero :
      (current leader).core.erase.core.signal_B = ⟨0, by omega⟩) :
    let e := groupOffset ring leader steps
    let T := wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
      hpsi kappa tau
    let D := runLocalSchedule ring T current [e, leader, leader]
    FirstBlockerEffect ring leader current D ⟨steps, hlt⟩ ∧
      ResetAwareShieldedRetryReady hpsi ring leader D ∧
      (D leader).core.erase.core.label =
        (current leader).core.erase.core.label ∧
      PPLLPpsiLeaderCreationRepair.bulletTwoCount D ≤
        PPLLPpsiLeaderCreationRepair.bulletTwoCount current := by
  let e := groupOffset ring leader steps
  let j := groupOffset ring leader (steps + 1)
  let T := wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
    hpsi kappa tau
  let C1 := localStep ring T current e
  let D := runLocalSchedule ring T C1 [leader, leader]
  have hnpos : 0 < n := by omega
  have heBound : steps < n := by omega
  have hjBound : steps + 1 < n := by omega
  have hneighbor : ring.rightNeighbor e = j := by
    simpa [e, j] using rightNeighbor_groupOffset ring leader steps
  have heNotLeader : e ≠ leader := by
    have hne := groupOffset_ne_of_lt ring leader heBound
      hnpos (Nat.ne_of_gt hstate.steps_pos)
    exact fun heq =>
      hne (heq.trans (groupOffset_zero_eq ring leader).symm)
  have hjNotLeader : j ≠ leader := by
    have hne := groupOffset_ne_of_lt ring leader hjBound
      hnpos (Nat.ne_of_gt (Nat.zero_lt_succ steps))
    exact fun heq =>
      hne (heq.trans (groupOffset_zero_eq ring leader).symm)
  have hstep := resetAwareFollower_localStep_normalizes
    hpsi ring hn current e hstate.no_active
      (hstate.unique_leader e heNotLeader) hstate.frontier_reset
      (by rw [hneighbor]; exact hstate.unique_leader j hjNotLeader)
  change ResetAwareFollowerGlobalStepFrame hpsi ring current C1 e at hstep
  have hleaderC1 : (C1 leader).core.erase.core.leader = true :=
    (hstep.leader_eq leader).trans hstate.leader_alive
  have hfirstNe : ring.rightNeighbor leader ≠ leader :=
    rightNeighbor_ne_self_of_one_lt ring hn leader
  have hfirstFollowerC1 :
      (C1 (ring.rightNeighbor leader)).core.erase.core.leader = false :=
    (hstep.leader_eq (ring.rightNeighbor leader)).trans
      (hstate.unique_leader (ring.rightNeighbor leader) hfirstNe)
  have huniqueC1 : hasUniqueLeader n
      (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig C1) := by
    refine ⟨leader, hleaderC1, ?_⟩
    intro i hi
    by_cases hine : i = leader
    · exact hine
    · change (C1 i).core.erase.core.leader = true at hi
      have hfalse := (hstep.leader_eq i).trans
        (hstate.unique_leader i hine)
      have hbad : (false : Bool) = true := hfalse.symm.trans hi
      exact (Bool.false_ne_true hbad).elim
  have hleaderOff : C1 leader = current leader :=
    hstep.off_edge leader (Ne.symm heNotLeader) (by
      rw [hneighbor]
      exact Ne.symm hjNotLeader)
  have hanchorC1 : InitiatorAnchor (C1 leader).core.erase.core := by
    rw [hleaderOff]
    exact ⟨hstate.leader_alive, hrootShield⟩
  have hsignalC1 :
      (C1 leader).core.erase.core.signal_B = ⟨0, by omega⟩ := by
    rw [hleaderOff]
    exact hrootSignalZero
  have hready := two_step_reseed_shieldedRetryReady_of_source_follower
    hpsi ring hn leader C1 hstep.no_active huniqueC1 hanchorC1
      hfirstFollowerC1
  change ResetAwareShieldedRetryReady hpsi ring leader D at hready
  have hlabel := two_step_reseed_leader_label_of_anchor
    hpsi ring hn leader C1 hstep.no_active hanchorC1 hfirstFollowerC1
  change (D leader).core.erase.core.label =
    (C1 leader).core.erase.core.label at hlabel
  have hlabelCurrent : (D leader).core.erase.core.label =
      (current leader).core.erase.core.label :=
    hlabel.trans (congrArg
      (fun u : ExpiringAgentState psi kappa tau =>
        u.core.erase.core.label) hleaderOff)
  have hfirstCount := resetAwareFollower_localStep_bulletTwoCount_le
    hpsi ring hn current e hstate.no_active
      (hstate.unique_leader e heNotLeader) hstate.frontier_reset
      (by rw [hneighbor]; exact hstate.unique_leader j hjNotLeader)
  change PPLLPpsiLeaderCreationRepair.bulletTwoCount C1 ≤
    PPLLPpsiLeaderCreationRepair.bulletTwoCount current at hfirstCount
  have hsecondCount :=
    two_step_reseed_bulletTwoCount_le_of_shielded_signal_zero
      hpsi ring hn leader C1 hstep.no_active hleaderC1
        hfirstFollowerC1 hanchorC1.2 hsignalC1
  change PPLLPpsiLeaderCreationRepair.bulletTwoCount D ≤
    PPLLPpsiLeaderCreationRepair.bulletTwoCount C1 at hsecondCount
  have htotalCount : PPLLPpsiLeaderCreationRepair.bulletTwoCount D ≤
      PPLLPpsiLeaderCreationRepair.bulletTwoCount current :=
    Nat.le_trans hsecondCount hfirstCount
  have hoffsetOne : groupOffset ring leader 1 =
      ring.rightNeighbor leader := by
    have hnext := rightNeighbor_groupOffset ring leader 0
    rw [groupOffset_zero_eq] at hnext
    simpa using hnext.symm
  have hoffTwo : ∀ k, 1 < k → k < n →
      D (groupOffset ring leader k) =
        C1 (groupOffset ring leader k) := by
    intro k hkOne hkBound
    apply runLocalSchedule_two_same_off_edge
    · have hk0 : groupOffset ring leader k ≠
          groupOffset ring leader 0 := by
        apply groupOffset_ne_of_lt ring leader hkBound (by omega)
        omega
      simpa [groupOffset_zero_eq] using hk0
    · rw [← hoffsetOne]
      apply groupOffset_ne_of_lt ring leader hkBound (by omega)
      omega
  have hpair : ExpiringResetFollowerNormalizedOutput hpsi
      (current e, current j) (C1 e, C1 j) := by
    simpa [hneighbor] using hstep.normalized
  let t : Fin (n - 1) := ⟨steps, hlt⟩
  have hstepsOne : 1 < steps + 1 :=
    Nat.succ_lt_succ hstate.steps_pos
  have hblockerAfterFirst :
      D (groupOffset ring leader (steps + 1)) =
        C1 (groupOffset ring leader (steps + 1)) :=
    hoffTwo (steps + 1) hstepsOne hjBound
  have heffect : FirstBlockerEffect ring leader current D t := {
    blocker_present := by
      simpa [t, j] using hrightEcho
    blocker_cleared := by
      rw [hblockerAfterFirst]
      simpa [t, j] using hpair.control.right_echo_false
    higher_unchanged := by
      intro s hs
      have hsBound : s.val + 1 < n := by omega
      have hse : groupOffset ring leader (s.val + 1) ≠ e := by
        apply groupOffset_ne_of_lt ring leader hsBound heBound
        dsimp only [t] at hs
        omega
      have hsj : groupOffset ring leader (s.val + 1) ≠ j := by
        apply groupOffset_ne_of_lt ring leader hsBound hjBound
        dsimp only [t] at hs
        omega
      rw [hoffTwo (s.val + 1) (by
        dsimp only [t] at hs
        omega) hsBound]
      exact congrArg
        (fun u : ExpiringAgentState psi kappa tau =>
          u.core.erase.core.echo)
        (hstep.off_edge (groupOffset ring leader (s.val + 1))
          hse (by rwa [hneighbor])) }
  simpa [e, T, C1, D, runLocalSchedule] using
    And.intro heffect
      (And.intro hready (And.intro hlabelCurrent htotalCount))

set_option maxHeartbeats 3000000 in
/-- Birth-signal-transition form of the canonical blocker collision.  The
follower collision keeps the same named unique leader, and the two-edge
reseed is guarded by that existing leader, so the complete three-edge word is
definitionally the already verified old consumer word. -/
theorem ResetAwareNormalizedPrefixState.collision_then_birthSignalZero_shielded_retry
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (leader : Fin n) (base current : EConfig n psi kappa tau)
    (steps : Nat)
    (hstate : ResetAwareNormalizedPrefixState
      hpsi ring leader base current steps)
    (hlt : steps < n - 1)
    (hrightEcho :
      (current (groupOffset ring leader (steps + 1))).core.erase.core.echo =
        true)
    (hrootShield : (current leader).core.erase.core.shield = true)
    (hrootSignalZero :
      (current leader).core.erase.core.signal_B = ⟨0, by omega⟩) :
    let e := groupOffset ring leader steps
    let T := wallSweepBirthSignalZeroPathStallTransition
      hpsi kappa tau
    let D := runLocalSchedule ring T current [e, leader, leader]
    FirstBlockerEffect ring leader current D ⟨steps, hlt⟩ ∧
      ResetAwareShieldedRetryReady hpsi ring leader D ∧
      (D leader).core.erase.core.label =
        (current leader).core.erase.core.label ∧
      PPLLPpsiLeaderCreationRepair.bulletTwoCount D ≤
        PPLLPpsiLeaderCreationRepair.bulletTwoCount current := by
  let e := groupOffset ring leader steps
  let Told :=
    wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
      hpsi kappa tau
  let Tnew := wallSweepBirthSignalZeroPathStallTransition
    hpsi kappa tau
  let C1old := localStep ring Told current e
  let C1new := localStep ring Tnew current e
  have hnpos : 0 < n := by omega
  have heBound : steps < n := by omega
  have hjBound : steps + 1 < n := by omega
  have heNotLeader : e ≠ leader := by
    have hne := groupOffset_ne_of_lt ring leader heBound
      hnpos (Nat.ne_of_gt hstate.steps_pos)
    exact fun heq =>
      hne (heq.trans (groupOffset_zero_eq ring leader).symm)
  have hjNotLeader : groupOffset ring leader (steps + 1) ≠ leader := by
    have hne := groupOffset_ne_of_lt ring leader hjBound
      hnpos (Nat.ne_of_gt (Nat.zero_lt_succ steps))
    exact fun heq =>
      hne (heq.trans (groupOffset_zero_eq ring leader).symm)
  have hstep := resetAwareFollower_localStep_normalizes
    hpsi ring hn current e hstate.no_active
      (hstate.unique_leader e heNotLeader) hstate.frontier_reset
      (by
        rw [rightNeighbor_groupOffset ring leader steps]
        exact hstate.unique_leader
          (groupOffset ring leader (steps + 1)) hjNotLeader)
  change ResetAwareFollowerGlobalStepFrame hpsi ring current C1old e at hstep
  have huniqueC1 : hasUniqueLeader n
      (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig C1old) := by
    refine ⟨leader, ?_, ?_⟩
    · exact (hstep.leader_eq leader).trans hstate.leader_alive
    · intro i hi
      by_cases hil : i = leader
      · exact hil
      · have hfalse := (hstep.leader_eq i).trans
          (hstate.unique_leader i hil)
        change (C1old i).core.erase.core.leader = true at hi
        rw [hfalse] at hi
        contradiction
  have hleaderC1 : (C1old leader).core.erase.core.leader = true :=
    (hstep.leader_eq leader).trans hstate.leader_alive
  have hfirst : C1new = C1old := by
    simpa only [C1new, C1old, Tnew, Told, e] using
      localStep_birthSignalZero_eq_resetProbe_of_fixed_unique_leader
        hpsi ring hn current e leader hstate.leader_alive
          huniqueC1 hleaderC1
  have hfirstNe : ring.rightNeighbor leader ≠ leader :=
    rightNeighbor_ne_self_of_one_lt ring hn leader
  have hrightFollowerC1 :
      (C1old (ring.rightNeighbor leader)).core.erase.core.leader = false :=
    (hstep.leader_eq (ring.rightNeighbor leader)).trans
      (hstate.unique_leader (ring.rightNeighbor leader) hfirstNe)
  have hleaderOff : C1old leader = current leader :=
    hstep.off_edge leader (Ne.symm heNotLeader) (by
      rw [rightNeighbor_groupOffset ring leader steps]
      exact Ne.symm hjNotLeader)
  have hanchorC1 : InitiatorAnchor (C1old leader).core.erase.core := by
    rw [hleaderOff]
    exact ⟨hstate.leader_alive, hrootShield⟩
  have hreseed := runLocalSchedule_birthSignalZero_two_reseed_eq
    hpsi ring leader C1old hstep.no_active hanchorC1 hrightFollowerC1
  have hwordEq :
      runLocalSchedule ring Tnew current [e, leader, leader] =
        runLocalSchedule ring Told current [e, leader, leader] := by
    change runLocalSchedule ring Tnew C1new [leader, leader] =
      runLocalSchedule ring Told C1old [leader, leader]
    rw [hfirst]
    exact hreseed
  have hold := hstate.collision_then_shielded_retry
    hpsi ring hn leader base current steps hlt hrightEcho
      hrootShield hrootSignalZero
  let Dnew := runLocalSchedule ring Tnew current [e, leader, leader]
  let Dold := runLocalSchedule ring Told current [e, leader, leader]
  change FirstBlockerEffect ring leader current Dnew ⟨steps, hlt⟩ ∧
    ResetAwareShieldedRetryReady hpsi ring leader Dnew ∧
    (Dnew leader).core.erase.core.label =
      (current leader).core.erase.core.label ∧
    PPLLPpsiLeaderCreationRepair.bulletTwoCount Dnew ≤
      PPLLPpsiLeaderCreationRepair.bulletTwoCount current
  change FirstBlockerEffect ring leader current Dold ⟨steps, hlt⟩ ∧
    ResetAwareShieldedRetryReady hpsi ring leader Dold ∧
    (Dold leader).core.erase.core.label =
      (current leader).core.erase.core.label ∧
    PPLLPpsiLeaderCreationRepair.bulletTwoCount Dold ≤
      PPLLPpsiLeaderCreationRepair.bulletTwoCount current at hold
  have hD : Dnew = Dold := by
    simpa only [Dnew, Dold] using hwordEq
  rw [hD]
  exact hold

set_option maxHeartbeats 3000000 in
/-- At echo rank zero the shielded lane traverses the complete non-wrap
prefix without any live-bullet-freedom premise. -/
theorem resetAwareShieldedRetry_zero_round
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (leader : Fin n) (C : EConfig n psi kappa tau)
    (hready : ResetAwareShieldedRetryReady hpsi ring leader C)
    (hzero : clockwiseEchoRank ring leader C = 0) :
    ∃ (word : DetSchedule n) (D : EConfig n psi kappa tau),
      D = runLocalSchedule ring
        (wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
          hpsi kappa tau) C word ∧
      ResetAwareShieldedRetryDone hpsi ring leader D ∧
      (D leader).core.erase.core.label =
        (C leader).core.erase.core.label ∧
      PPLLPpsiLeaderCreationRepair.bulletTwoCount D ≤
        PPLLPpsiLeaderCreationRepair.bulletTwoCount C := by
  obtain ⟨hfrontier, hshield, hsignal⟩ := hready
  have hstateOne := resetAwareNormalizedPrefixState_one_of_frontierAt
    hpsi ring hn leader C hfrontier
  have hbaseEcho : ∀ k, 1 < k → k ≤ n - 1 →
      (C (groupOffset ring leader k)).core.erase.core.echo = false := by
    intro k hk hkn
    exact follower_echo_false_of_clockwiseEchoRank_eq_zero
      ring leader C hzero k (by omega) (by omega)
  obtain ⟨word, D, hD, _hwordLength, hstateD, hrootD, hcountD⟩ :=
    hstateOne.exists_advance_to_of_base_echo_false_unrestricted
      hpsi ring hn leader C C 1 (n - 1) (by omega) (by omega)
        hbaseEcho
  have hshieldD : (D leader).core.erase.core.shield = true := by
    rw [hrootD]
    exact hshield
  have hsignalD :
      (D leader).core.erase.core.signal_B = ⟨0, by omega⟩ := by
    rw [hrootD]
    exact hsignal
  have hlabelD : (D leader).core.erase.core.label =
      (C leader).core.erase.core.label :=
    congrArg
      (fun u : ExpiringAgentState psi kappa tau =>
        u.core.erase.core.label) hrootD
  exact ⟨word, D, hD, ⟨C, hstateD, hshieldD, hsignalD⟩,
    hlabelD, hcountD⟩

set_option maxHeartbeats 3000000 in
/-- Birth-signal-transition form of the zero-echo shielded traversal. -/
theorem resetAwareShieldedRetry_birthSignalZero_zero_round
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (leader : Fin n) (C : EConfig n psi kappa tau)
    (hready : ResetAwareShieldedRetryReady hpsi ring leader C)
    (hzero : clockwiseEchoRank ring leader C = 0) :
    ∃ (word : DetSchedule n) (D : EConfig n psi kappa tau),
      D = runLocalSchedule ring
        (wallSweepBirthSignalZeroPathStallTransition
          hpsi kappa tau) C word ∧
      ResetAwareShieldedRetryDone hpsi ring leader D ∧
      (D leader).core.erase.core.label =
        (C leader).core.erase.core.label ∧
      PPLLPpsiLeaderCreationRepair.bulletTwoCount D ≤
        PPLLPpsiLeaderCreationRepair.bulletTwoCount C := by
  obtain ⟨hfrontier, hshield, hsignal⟩ := hready
  have hstateOne := resetAwareNormalizedPrefixState_one_of_frontierAt
    hpsi ring hn leader C hfrontier
  have hbaseEcho : ∀ k, 1 < k → k ≤ n - 1 →
      (C (groupOffset ring leader k)).core.erase.core.echo = false := by
    intro k hk hkn
    exact follower_echo_false_of_clockwiseEchoRank_eq_zero
      ring leader C hzero k (by omega) (by omega)
  obtain ⟨word, D, hD, _hwordLength, hstateD, hrootD, hcountD⟩ :=
    hstateOne.exists_birthSignalZero_advance_to_of_base_echo_false_unrestricted
      hpsi ring hn leader C C 1 (n - 1) (by omega) (by omega)
        hbaseEcho
  have hshieldD : (D leader).core.erase.core.shield = true := by
    rw [hrootD]
    exact hshield
  have hsignalD :
      (D leader).core.erase.core.signal_B = ⟨0, by omega⟩ := by
    rw [hrootD]
    exact hsignal
  have hlabelD : (D leader).core.erase.core.label =
      (C leader).core.erase.core.label :=
    congrArg
      (fun u : ExpiringAgentState psi kappa tau =>
        u.core.erase.core.label) hrootD
  exact ⟨word, D, hD, ⟨C, hstateD, hshieldD, hsignalD⟩,
    hlabelD, hcountD⟩

set_option maxHeartbeats 4000000 in
/-- At positive echo rank, advance to the canonical first blocker, clear it,
and replay the shielded leader edge.  The result is another shielded frontier
with strictly smaller echo rank and nonincreasing live-bullet mass. -/
theorem resetAwareShieldedRetry_positive_round
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (leader : Fin n) (C : EConfig n psi kappa tau)
    (hready : ResetAwareShieldedRetryReady hpsi ring leader C)
    (hrank : clockwiseEchoRank ring leader C ≠ 0) :
    ∃ (word : DetSchedule n) (D : EConfig n psi kappa tau),
      D = runLocalSchedule ring
        (wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
          hpsi kappa tau) C word ∧
      ResetAwareShieldedRetryReady hpsi ring leader D ∧
      (D leader).core.erase.core.label =
        (C leader).core.erase.core.label ∧
      clockwiseEchoRank ring leader D <
        clockwiseEchoRank ring leader C ∧
      PPLLPpsiLeaderCreationRepair.bulletTwoCount D ≤
        PPLLPpsiLeaderCreationRepair.bulletTwoCount C := by
  obtain ⟨hfrontier, hshield, hsignal⟩ := hready
  have hstateOne := resetAwareNormalizedPrefixState_one_of_frontierAt
    hpsi ring hn leader C hfrontier
  obtain ⟨_noActive, _hunique, _hleader, _hrightFollower,
      _hrightLabel, _hleftProbe, _hrightProbe,
      _hleftNeutral, _hrightNeutral, _hleftReset, _hrightReset,
      _hleftEcho, hrightEchoFalse, _hsafe⟩ := hfrontier
  obtain ⟨t, _hcanonical, hpresent, hlower⟩ :=
    exists_firstClockwiseEcho_of_rank_ne_zero ring leader C hrank
  have hoffsetOne : groupOffset ring leader 1 =
      ring.rightNeighbor leader := by
    have hnext := rightNeighbor_groupOffset ring leader 0
    rw [groupOffset_zero_eq] at hnext
    simpa using hnext.symm
  have htPos : 0 < t.val := by
    by_cases htZero : t.val = 0
    · have hpresentFirst :
          (C (groupOffset ring leader 1)).core.erase.core.echo = true := by
        simpa [htZero] using hpresent
      have hfalseFirst :
          (C (groupOffset ring leader 1)).core.erase.core.echo = false := by
        simpa [hoffsetOne] using hrightEchoFalse
      rw [hfalseFirst] at hpresentFirst
      contradiction
    · omega
  have hbaseEcho : ∀ k, 1 < k → k ≤ t.val →
      (C (groupOffset ring leader k)).core.erase.core.echo = false := by
    intro k hk hkt
    let i : Fin (n - 1) := ⟨k - 1, by omega⟩
    have hi := hlower i (by
      dsimp only [i]
      omega)
    have hindex : i.val + 1 = k := by
      dsimp only [i]
      omega
    simpa [hindex] using hi
  obtain ⟨pref, M, hM, _hprefLength, hstateM, hrootM, hcountM⟩ :=
    hstateOne.exists_advance_to_of_base_echo_false_unrestricted
      hpsi ring hn leader C C 1 t.val (by omega) (by omega) hbaseEcho
  have hblockerM :
      (M (groupOffset ring leader (t.val + 1))).core.erase.core.echo =
        true := by
    rw [hstateM.untouched_ahead (t.val + 1) (by omega) (by omega)]
    exact hpresent
  have hshieldM : (M leader).core.erase.core.shield = true := by
    rw [hrootM]
    exact hshield
  have hsignalM :
      (M leader).core.erase.core.signal_B = ⟨0, by omega⟩ := by
    rw [hrootM]
    exact hsignal
  let T := wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
    hpsi kappa tau
  let suffix : DetSchedule n :=
    [groupOffset ring leader t.val, leader, leader]
  let D := runLocalSchedule ring T M suffix
  have hcollision : FirstBlockerEffect ring leader M D t ∧
      ResetAwareShieldedRetryReady hpsi ring leader D ∧
      (D leader).core.erase.core.label =
        (M leader).core.erase.core.label ∧
      PPLLPpsiLeaderCreationRepair.bulletTwoCount D ≤
        PPLLPpsiLeaderCreationRepair.bulletTwoCount M := by
    simpa [T, suffix, D] using
      hstateM.collision_then_shielded_retry
        hpsi ring hn leader C M t.val t.isLt hblockerM
          hshieldM hsignalM
  have heffect : FirstBlockerEffect ring leader C D t := {
    blocker_present := hpresent
    blocker_cleared := hcollision.1.blocker_cleared
    higher_unchanged := by
      intro s hts
      rw [hcollision.1.higher_unchanged s hts]
      have hsite := hstateM.untouched_ahead (s.val + 1)
        (by omega) (by omega)
      exact congrArg
        (fun u : ExpiringAgentState psi kappa tau =>
          u.core.erase.core.echo) hsite }
  let word := pref ++ suffix
  refine ⟨word, D, ?_, hcollision.2.1,
    hcollision.2.2.1.trans (congrArg
      (fun u : ExpiringAgentState psi kappa tau =>
        u.core.erase.core.label) hrootM),
    heffect.rank_lt, Nat.le_trans hcollision.2.2.2 hcountM⟩
  calc
    D = runLocalSchedule ring T M suffix := rfl
    _ = runLocalSchedule ring T
        (runLocalSchedule ring T C pref) suffix := by rw [← hM]
    _ = runLocalSchedule ring T C (pref ++ suffix) :=
      (runLocalSchedule_append_generic ring T C pref suffix).symm
    _ = runLocalSchedule ring T C word := by rfl

set_option maxHeartbeats 4000000 in
/-- Birth-signal-transition form of the positive echo-rank round. -/
theorem resetAwareShieldedRetry_birthSignalZero_positive_round
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (leader : Fin n) (C : EConfig n psi kappa tau)
    (hready : ResetAwareShieldedRetryReady hpsi ring leader C)
    (hrank : clockwiseEchoRank ring leader C ≠ 0) :
    ∃ (word : DetSchedule n) (D : EConfig n psi kappa tau),
      D = runLocalSchedule ring
        (wallSweepBirthSignalZeroPathStallTransition
          hpsi kappa tau) C word ∧
      ResetAwareShieldedRetryReady hpsi ring leader D ∧
      (D leader).core.erase.core.label =
        (C leader).core.erase.core.label ∧
      clockwiseEchoRank ring leader D <
        clockwiseEchoRank ring leader C ∧
      PPLLPpsiLeaderCreationRepair.bulletTwoCount D ≤
        PPLLPpsiLeaderCreationRepair.bulletTwoCount C := by
  obtain ⟨hfrontier, hshield, hsignal⟩ := hready
  have hstateOne := resetAwareNormalizedPrefixState_one_of_frontierAt
    hpsi ring hn leader C hfrontier
  obtain ⟨_noActive, _hunique, _hleader, _hrightFollower,
      _hrightLabel, _hleftProbe, _hrightProbe,
      _hleftNeutral, _hrightNeutral, _hleftReset, _hrightReset,
      _hleftEcho, hrightEchoFalse, _hsafe⟩ := hfrontier
  obtain ⟨t, _hcanonical, hpresent, hlower⟩ :=
    exists_firstClockwiseEcho_of_rank_ne_zero ring leader C hrank
  have hoffsetOne : groupOffset ring leader 1 =
      ring.rightNeighbor leader := by
    have hnext := rightNeighbor_groupOffset ring leader 0
    rw [groupOffset_zero_eq] at hnext
    simpa using hnext.symm
  have htPos : 0 < t.val := by
    by_cases htZero : t.val = 0
    · have hpresentFirst :
          (C (groupOffset ring leader 1)).core.erase.core.echo = true := by
        simpa [htZero] using hpresent
      have hfalseFirst :
          (C (groupOffset ring leader 1)).core.erase.core.echo = false := by
        simpa [hoffsetOne] using hrightEchoFalse
      rw [hfalseFirst] at hpresentFirst
      contradiction
    · omega
  have hbaseEcho : ∀ k, 1 < k → k ≤ t.val →
      (C (groupOffset ring leader k)).core.erase.core.echo = false := by
    intro k hk hkt
    let i : Fin (n - 1) := ⟨k - 1, by omega⟩
    have hi := hlower i (by
      dsimp only [i]
      omega)
    have hindex : i.val + 1 = k := by
      dsimp only [i]
      omega
    simpa [hindex] using hi
  obtain ⟨pref, M, hM, _hprefLength, hstateM, hrootM, hcountM⟩ :=
    hstateOne.exists_birthSignalZero_advance_to_of_base_echo_false_unrestricted
      hpsi ring hn leader C C 1 t.val (by omega) (by omega) hbaseEcho
  have hblockerM :
      (M (groupOffset ring leader (t.val + 1))).core.erase.core.echo =
        true := by
    rw [hstateM.untouched_ahead (t.val + 1) (by omega) (by omega)]
    exact hpresent
  have hshieldM : (M leader).core.erase.core.shield = true := by
    rw [hrootM]
    exact hshield
  have hsignalM :
      (M leader).core.erase.core.signal_B = ⟨0, by omega⟩ := by
    rw [hrootM]
    exact hsignal
  let T := wallSweepBirthSignalZeroPathStallTransition
    hpsi kappa tau
  let suffix : DetSchedule n :=
    [groupOffset ring leader t.val, leader, leader]
  let D := runLocalSchedule ring T M suffix
  have hcollision : FirstBlockerEffect ring leader M D t ∧
      ResetAwareShieldedRetryReady hpsi ring leader D ∧
      (D leader).core.erase.core.label =
        (M leader).core.erase.core.label ∧
      PPLLPpsiLeaderCreationRepair.bulletTwoCount D ≤
        PPLLPpsiLeaderCreationRepair.bulletTwoCount M := by
    simpa [T, suffix, D] using
      hstateM.collision_then_birthSignalZero_shielded_retry
        hpsi ring hn leader C M t.val t.isLt hblockerM
          hshieldM hsignalM
  have heffect : FirstBlockerEffect ring leader C D t := {
    blocker_present := hpresent
    blocker_cleared := hcollision.1.blocker_cleared
    higher_unchanged := by
      intro s hts
      rw [hcollision.1.higher_unchanged s hts]
      have hsite := hstateM.untouched_ahead (s.val + 1)
        (by omega) (by omega)
      exact congrArg
        (fun u : ExpiringAgentState psi kappa tau =>
          u.core.erase.core.echo) hsite }
  let word := pref ++ suffix
  refine ⟨word, D, ?_, hcollision.2.1,
    hcollision.2.2.1.trans (congrArg
      (fun u : ExpiringAgentState psi kappa tau =>
        u.core.erase.core.label) hrootM),
    heffect.rank_lt, Nat.le_trans hcollision.2.2.2 hcountM⟩
  calc
    D = runLocalSchedule ring T M suffix := rfl
    _ = runLocalSchedule ring T
        (runLocalSchedule ring T C pref) suffix := by rw [← hM]
    _ = runLocalSchedule ring T C (pref ++ suffix) :=
      (runLocalSchedule_append_generic ring T C pref suffix).symm
    _ = runLocalSchedule ring T C word := by rfl

set_option maxHeartbeats 4000000 in
/-- Strong induction on the echo rank completes the shielded prefix.  Every
recursive round preserves the same root label and composes the global
live-bullet nonincrease bound. -/
theorem exists_resetAwareShieldedRetrySchedule_of_rank
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (leader : Fin n) (rank : Nat) (C : EConfig n psi kappa tau)
    (hready : ResetAwareShieldedRetryReady hpsi ring leader C)
    (hrank : clockwiseEchoRank ring leader C = rank) :
    ∃ (word : DetSchedule n) (D : EConfig n psi kappa tau),
      D = runLocalSchedule ring
        (wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
          hpsi kappa tau) C word ∧
      ResetAwareShieldedRetryDone hpsi ring leader D ∧
      (D leader).core.erase.core.label =
        (C leader).core.erase.core.label ∧
      PPLLPpsiLeaderCreationRepair.bulletTwoCount D ≤
        PPLLPpsiLeaderCreationRepair.bulletTwoCount C := by
  revert C
  induction rank using Nat.strongRecOn with
  | ind rank ih =>
      intro C hready hrank
      by_cases hechoZero : clockwiseEchoRank ring leader C = 0
      · exact resetAwareShieldedRetry_zero_round
          hpsi ring hn leader C hready hechoZero
      · obtain ⟨pref, C1, hC1, hreadyC1, hroundLabel,
            hdrop, hroundCount⟩ :=
          resetAwareShieldedRetry_positive_round
            hpsi ring hn leader C hready hechoZero
        have hlt : clockwiseEchoRank ring leader C1 < rank := by
          calc
            clockwiseEchoRank ring leader C1 <
                clockwiseEchoRank ring leader C := hdrop
            _ = rank := hrank
        obtain ⟨tail, D, hD, hdone, htailLabel, htailCount⟩ :=
          ih (clockwiseEchoRank ring leader C1) hlt
            C1 hreadyC1 rfl
        let T :=
          wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
            hpsi kappa tau
        let word := pref ++ tail
        refine ⟨word, D, ?_, hdone,
          htailLabel.trans hroundLabel,
          Nat.le_trans htailCount hroundCount⟩
        calc
          D = runLocalSchedule ring T C1 tail := hD
          _ = runLocalSchedule ring T
              (runLocalSchedule ring T C pref) tail := by rw [← hC1]
          _ = runLocalSchedule ring T C (pref ++ tail) :=
            (runLocalSchedule_append_generic ring T C pref tail).symm
          _ = runLocalSchedule ring T C word := by rfl

/-- Scheduler-facing shielded completion theorem. -/
theorem exists_resetAwareShieldedRetrySchedule
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (leader : Fin n) (C : EConfig n psi kappa tau)
    (hready : ResetAwareShieldedRetryReady hpsi ring leader C) :
    ∃ (word : DetSchedule n) (D : EConfig n psi kappa tau),
      D = runLocalSchedule ring
        (wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
          hpsi kappa tau) C word ∧
      ResetAwareShieldedRetryDone hpsi ring leader D ∧
      (D leader).core.erase.core.label =
        (C leader).core.erase.core.label ∧
      PPLLPpsiLeaderCreationRepair.bulletTwoCount D ≤
        PPLLPpsiLeaderCreationRepair.bulletTwoCount C := by
  exact exists_resetAwareShieldedRetrySchedule_of_rank
    hpsi ring hn leader (clockwiseEchoRank ring leader C) C hready rfl

set_option maxHeartbeats 4000000 in
/-- Birth-signal-transition completion of the shielded prefix, by the same
strict echo-rank induction as the old consumer. -/
theorem exists_resetAwareShieldedRetryBirthSignalZeroSchedule_of_rank
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (leader : Fin n) (rank : Nat) (C : EConfig n psi kappa tau)
    (hready : ResetAwareShieldedRetryReady hpsi ring leader C)
    (hrank : clockwiseEchoRank ring leader C = rank) :
    ∃ (word : DetSchedule n) (D : EConfig n psi kappa tau),
      D = runLocalSchedule ring
        (wallSweepBirthSignalZeroPathStallTransition
          hpsi kappa tau) C word ∧
      ResetAwareShieldedRetryDone hpsi ring leader D ∧
      (D leader).core.erase.core.label =
        (C leader).core.erase.core.label ∧
      PPLLPpsiLeaderCreationRepair.bulletTwoCount D ≤
        PPLLPpsiLeaderCreationRepair.bulletTwoCount C := by
  revert C
  induction rank using Nat.strongRecOn with
  | ind rank ih =>
      intro C hready hrank
      by_cases hechoZero : clockwiseEchoRank ring leader C = 0
      · exact resetAwareShieldedRetry_birthSignalZero_zero_round
          hpsi ring hn leader C hready hechoZero
      · obtain ⟨pref, C1, hC1, hreadyC1, hroundLabel,
            hdrop, hroundCount⟩ :=
          resetAwareShieldedRetry_birthSignalZero_positive_round
            hpsi ring hn leader C hready hechoZero
        have hlt : clockwiseEchoRank ring leader C1 < rank := by
          calc
            clockwiseEchoRank ring leader C1 <
                clockwiseEchoRank ring leader C := hdrop
            _ = rank := hrank
        obtain ⟨tail, D, hD, hdone, htailLabel, htailCount⟩ :=
          ih (clockwiseEchoRank ring leader C1) hlt
            C1 hreadyC1 rfl
        let T := wallSweepBirthSignalZeroPathStallTransition
          hpsi kappa tau
        let word := pref ++ tail
        refine ⟨word, D, ?_, hdone,
          htailLabel.trans hroundLabel,
          Nat.le_trans htailCount hroundCount⟩
        calc
          D = runLocalSchedule ring T C1 tail := hD
          _ = runLocalSchedule ring T
              (runLocalSchedule ring T C pref) tail := by rw [← hC1]
          _ = runLocalSchedule ring T C (pref ++ tail) :=
            (runLocalSchedule_append_generic ring T C pref tail).symm
          _ = runLocalSchedule ring T C word := by rfl

/-- Scheduler-facing birth-signal completion theorem for the shielded lane. -/
theorem exists_resetAwareShieldedRetryBirthSignalZeroSchedule
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (leader : Fin n) (C : EConfig n psi kappa tau)
    (hready : ResetAwareShieldedRetryReady hpsi ring leader C) :
    ∃ (word : DetSchedule n) (D : EConfig n psi kappa tau),
      D = runLocalSchedule ring
        (wallSweepBirthSignalZeroPathStallTransition
          hpsi kappa tau) C word ∧
      ResetAwareShieldedRetryDone hpsi ring leader D ∧
      (D leader).core.erase.core.label =
        (C leader).core.erase.core.label ∧
      PPLLPpsiLeaderCreationRepair.bulletTwoCount D ≤
        PPLLPpsiLeaderCreationRepair.bulletTwoCount C := by
  exact exists_resetAwareShieldedRetryBirthSignalZeroSchedule_of_rank
    hpsi ring hn leader (clockwiseEchoRank ring leader C) C hready rfl

set_option maxHeartbeats 2000000 in
/-- A completed shielded prefix reaches a zero-labelled root without assuming
global live-bullet freedom.  The empty migration keeps the already protected
root; every nonempty migration exposes the vacated old root as a non-live
follower.  Labels are framed and global live-bullet mass does not increase. -/
theorem ResetAwareShieldedRetryDone.exists_zeroRootArrival
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (leader : Fin n) (C : EConfig n psi kappa tau)
    (hdone : ResetAwareShieldedRetryDone hpsi ring leader C)
    (hpsiLe : psi ≤ n) :
    ∃ k, 0 < k ∧ k ≤ n ∧
      let newRoot := groupOffset ring leader k
      let T :=
        wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
          hpsi kappa tau
      let word := pPsiProbeChasePrefix ring leader (n - k)
      let D := runLocalSchedule ring T C word
      word.length = n - k ∧
        ResetAwareZeroRootArrival hpsi ring newRoot D ∧
        PPLLPpsiLeaderCreationRepair.bulletTwoCount D ≤
          PPLLPpsiLeaderCreationRepair.bulletTwoCount C ∧
        ∀ i, (D i).core.erase.core.label =
          (C i).core.erase.core.label := by
  obtain ⟨_base, hstate, hshield, hsignal⟩ := hdone
  have hunique : hasUniqueLeader n
      (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig C) := by
    refine ⟨leader, hstate.leader_alive, ?_⟩
    intro i hi
    by_cases hie : i = leader
    · exact hie
    · have hiFollower := hstate.unique_leader i hie
      change (C i).core.erase.core.leader = true at hi
      rw [hiFollower] at hi
      contradiction
  by_cases hrootZero :
      (C leader).core.erase.core.label = ⟨0, hpsi⟩
  · have hrightNe : ring.rightNeighbor leader ≠ leader :=
      rightNeighbor_ne_self_of_one_lt ring hn leader
    have hrightFollower :
        (C (ring.rightNeighbor leader)).core.erase.core.leader = false :=
      hstate.unique_leader (ring.rightNeighbor leader) hrightNe
    have harrival : ResetAwareZeroRootArrival
        hpsi ring leader C := {
      no_active := hstate.no_active
      unique_leader := hunique
      root_alive := hstate.leader_alive
      right_follower := hrightFollower
      root_zero := hrootZero
      protected_or_right_not_live := Or.inl ⟨hshield, hsignal⟩ }
    refine ⟨n, by omega, Nat.le_refl n, ?_⟩
    simp only [Nat.sub_self, pPsiProbeChasePrefix, runLocalSchedule,
      List.length_nil]
    refine ⟨True.intro, ?_, Nat.le_refl _, fun _ => True.intro⟩
    simpa [groupOffset_n_eq] using harrival
  · have hperiod : psi ≤ (n - 1) + 1 := by omega
    obtain ⟨k, hkpos, hkle, hzero⟩ :=
      hstate.normalized_prefix.exists_positive_zero_of_root_nonzero
        hperiod hrootZero
    have hexists : ∃ k, 0 < k ∧ k < n ∧
        (C (groupOffset ring leader k)).core.erase.core.label =
          ⟨0, hpsi⟩ := ⟨k, hkpos, by omega, hzero⟩
    obtain ⟨k, hkpos, hklt, hresult⟩ :=
      reverseMigration_to_zero_unrestricted_of_exists_offset
        hpsi ring hn leader C hstate.no_active hunique
          hstate.leader_alive hrootZero hexists
    let newRoot := groupOffset ring leader k
    let T :=
      wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
        hpsi kappa tau
    let word := pPsiProbeChasePrefix ring leader (n - k)
    let D := runLocalSchedule ring T C word
    change word.length = n - k ∧
        NoActiveDeletion D ∧
        hasUniqueLeader n
          (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig D) ∧
        (D newRoot).core.erase.core.leader = true ∧
        (D (ring.rightNeighbor newRoot)).core.erase.core.leader = false ∧
        (D (ring.rightNeighbor newRoot)).core.erase.core.bullet ≠
          ⟨2, by omega⟩ ∧
        PPLLPpsiLeaderCreationRepair.bulletTwoCount D ≤
          PPLLPpsiLeaderCreationRepair.bulletTwoCount C ∧
        (D newRoot).core.erase.core.label = ⟨0, hpsi⟩ ∧
        ∀ i, (D i).core.erase.core.label =
          (C i).core.erase.core.label at hresult
    obtain ⟨hlength, hnoActiveD, huniqueD, hrootD,
        hrightFollowerD, hrightNotLiveD, hcountD, hzeroD,
        hlabelsD⟩ := hresult
    have harrival : ResetAwareZeroRootArrival
        hpsi ring newRoot D := {
      no_active := hnoActiveD
      unique_leader := huniqueD
      root_alive := hrootD
      right_follower := hrightFollowerD
      root_zero := hzeroD
      protected_or_right_not_live := Or.inr hrightNotLiveD }
    exact ⟨k, hkpos, Nat.le_of_lt hklt, hlength,
      harrival, hcountD, hlabelsD⟩

set_option maxHeartbeats 2000000 in
/-- Birth-signal-transition form of the completed shielded-prefix migration
to a zero-labelled root. -/
theorem ResetAwareShieldedRetryDone.exists_birthSignalZero_zeroRootArrival
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (leader : Fin n) (C : EConfig n psi kappa tau)
    (hdone : ResetAwareShieldedRetryDone hpsi ring leader C)
    (hpsiLe : psi ≤ n) :
    ∃ k, 0 < k ∧ k ≤ n ∧
      let newRoot := groupOffset ring leader k
      let T := wallSweepBirthSignalZeroPathStallTransition
        hpsi kappa tau
      let word := pPsiProbeChasePrefix ring leader (n - k)
      let D := runLocalSchedule ring T C word
      word.length = n - k ∧
        ResetAwareZeroRootArrival hpsi ring newRoot D ∧
        PPLLPpsiLeaderCreationRepair.bulletTwoCount D ≤
          PPLLPpsiLeaderCreationRepair.bulletTwoCount C ∧
        ∀ i, (D i).core.erase.core.label =
          (C i).core.erase.core.label := by
  obtain ⟨_base, hstate, hshield, hsignal⟩ := hdone
  have hunique : hasUniqueLeader n
      (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig C) := by
    refine ⟨leader, hstate.leader_alive, ?_⟩
    intro i hi
    by_cases hie : i = leader
    · exact hie
    · have hiFollower := hstate.unique_leader i hie
      change (C i).core.erase.core.leader = true at hi
      rw [hiFollower] at hi
      contradiction
  by_cases hrootZero :
      (C leader).core.erase.core.label = ⟨0, hpsi⟩
  · have hrightNe : ring.rightNeighbor leader ≠ leader :=
      rightNeighbor_ne_self_of_one_lt ring hn leader
    have hrightFollower :
        (C (ring.rightNeighbor leader)).core.erase.core.leader = false :=
      hstate.unique_leader (ring.rightNeighbor leader) hrightNe
    have harrival : ResetAwareZeroRootArrival
        hpsi ring leader C := {
      no_active := hstate.no_active
      unique_leader := hunique
      root_alive := hstate.leader_alive
      right_follower := hrightFollower
      root_zero := hrootZero
      protected_or_right_not_live := Or.inl ⟨hshield, hsignal⟩ }
    refine ⟨n, by omega, Nat.le_refl n, ?_⟩
    simp only [Nat.sub_self, pPsiProbeChasePrefix, runLocalSchedule,
      List.length_nil]
    refine ⟨True.intro, ?_, Nat.le_refl _, fun _ => True.intro⟩
    simpa [groupOffset_n_eq] using harrival
  · have hperiod : psi ≤ (n - 1) + 1 := by omega
    obtain ⟨k, hkpos, hkle, hzero⟩ :=
      hstate.normalized_prefix.exists_positive_zero_of_root_nonzero
        hperiod hrootZero
    have hexists : ∃ k, 0 < k ∧ k < n ∧
        (C (groupOffset ring leader k)).core.erase.core.label =
          ⟨0, hpsi⟩ := ⟨k, hkpos, by omega, hzero⟩
    obtain ⟨k, hkpos, hklt, hresult⟩ :=
      reverseMigration_birthSignalZero_to_zero_unrestricted_of_exists_offset
        hpsi ring hn leader C hstate.no_active hunique
          hstate.leader_alive hrootZero hexists
    let newRoot := groupOffset ring leader k
    let T := wallSweepBirthSignalZeroPathStallTransition
      hpsi kappa tau
    let word := pPsiProbeChasePrefix ring leader (n - k)
    let D := runLocalSchedule ring T C word
    change word.length = n - k ∧
        NoActiveDeletion D ∧
        hasUniqueLeader n
          (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig D) ∧
        (D newRoot).core.erase.core.leader = true ∧
        (D (ring.rightNeighbor newRoot)).core.erase.core.leader = false ∧
        (D (ring.rightNeighbor newRoot)).core.erase.core.bullet ≠
          ⟨2, by omega⟩ ∧
        PPLLPpsiLeaderCreationRepair.bulletTwoCount D ≤
          PPLLPpsiLeaderCreationRepair.bulletTwoCount C ∧
        (D newRoot).core.erase.core.label = ⟨0, hpsi⟩ ∧
        ∀ i, (D i).core.erase.core.label =
          (C i).core.erase.core.label at hresult
    obtain ⟨hlength, hnoActiveD, huniqueD, hrootD,
        hrightFollowerD, hrightNotLiveD, hcountD, hzeroD,
        hlabelsD⟩ := hresult
    have harrival : ResetAwareZeroRootArrival
        hpsi ring newRoot D := {
      no_active := hnoActiveD
      unique_leader := huniqueD
      root_alive := hrootD
      right_follower := hrightFollowerD
      root_zero := hzeroD
      protected_or_right_not_live := Or.inr hrightNotLiveD }
    exact ⟨k, hkpos, Nat.le_of_lt hklt, hlength,
      harrival, hcountD, hlabelsD⟩

set_option maxHeartbeats 2000000 in
/-- End-to-end shielded normalization and optional reverse migration.  From a
shielded restart frontier it constructs one literal schedule to a zero-root
arrival, with global live-bullet mass bounded by the input configuration. -/
theorem exists_resetAwareShieldedZeroRootArrivalSchedule
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (hpsiLe : psi ≤ n)
    (leader : Fin n) (C : EConfig n psi kappa tau)
    (hready : ResetAwareShieldedRetryReady hpsi ring leader C) :
    ∃ (word : DetSchedule n) (D : EConfig n psi kappa tau)
      (newRoot : Fin n),
      D = runLocalSchedule ring
        (wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
          hpsi kappa tau) C word ∧
      ResetAwareZeroRootArrival hpsi ring newRoot D ∧
      PPLLPpsiLeaderCreationRepair.bulletTwoCount D ≤
        PPLLPpsiLeaderCreationRepair.bulletTwoCount C := by
  let T :=
    wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
      hpsi kappa tau
  obtain ⟨pref, M, hM, hdone, _hrootLabel, hcountM⟩ :=
    exists_resetAwareShieldedRetrySchedule
      hpsi ring hn leader C hready
  obtain ⟨k, _hkpos, _hkle, harrival⟩ :=
    hdone.exists_zeroRootArrival hpsi ring hn leader M hpsiLe
  let newRoot := groupOffset ring leader k
  let reverseWord := pPsiProbeChasePrefix ring leader (n - k)
  let D := runLocalSchedule ring T M reverseWord
  change reverseWord.length = n - k ∧
      ResetAwareZeroRootArrival hpsi ring newRoot D ∧
      PPLLPpsiLeaderCreationRepair.bulletTwoCount D ≤
        PPLLPpsiLeaderCreationRepair.bulletTwoCount M ∧
      ∀ i, (D i).core.erase.core.label =
        (M i).core.erase.core.label at harrival
  let word := pref ++ reverseWord
  refine ⟨word, D, newRoot, ?_, harrival.2.1,
    Nat.le_trans harrival.2.2.1 hcountM⟩
  calc
    D = runLocalSchedule ring T M reverseWord := rfl
    _ = runLocalSchedule ring T
        (runLocalSchedule ring T C pref) reverseWord := by rw [← hM]
    _ = runLocalSchedule ring T C (pref ++ reverseWord) :=
      (runLocalSchedule_append_generic ring T C pref reverseWord).symm
    _ = runLocalSchedule ring T C word := by rfl

/-- End-to-end birth-signal shielded normalization and optional reverse
migration to a zero-labelled root. -/
theorem exists_resetAwareShieldedBirthSignalZeroRootArrivalSchedule
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (hpsiLe : psi ≤ n)
    (leader : Fin n) (C : EConfig n psi kappa tau)
    (hready : ResetAwareShieldedRetryReady hpsi ring leader C) :
    ∃ (word : DetSchedule n) (D : EConfig n psi kappa tau)
      (newRoot : Fin n),
      D = runLocalSchedule ring
        (wallSweepBirthSignalZeroPathStallTransition
          hpsi kappa tau) C word ∧
      ResetAwareZeroRootArrival hpsi ring newRoot D ∧
      PPLLPpsiLeaderCreationRepair.bulletTwoCount D ≤
        PPLLPpsiLeaderCreationRepair.bulletTwoCount C := by
  let T := wallSweepBirthSignalZeroPathStallTransition
    hpsi kappa tau
  obtain ⟨pref, M, hM, hdone, _hrootLabel, hcountM⟩ :=
    exists_resetAwareShieldedRetryBirthSignalZeroSchedule
      hpsi ring hn leader C hready
  obtain ⟨k, _hkpos, _hkle, harrival⟩ :=
    hdone.exists_birthSignalZero_zeroRootArrival
      hpsi ring hn leader M hpsiLe
  let newRoot := groupOffset ring leader k
  let reverseWord := pPsiProbeChasePrefix ring leader (n - k)
  let D := runLocalSchedule ring T M reverseWord
  change reverseWord.length = n - k ∧
      ResetAwareZeroRootArrival hpsi ring newRoot D ∧
      PPLLPpsiLeaderCreationRepair.bulletTwoCount D ≤
        PPLLPpsiLeaderCreationRepair.bulletTwoCount M ∧
      ∀ i, (D i).core.erase.core.label =
        (M i).core.erase.core.label at harrival
  let word := pref ++ reverseWord
  refine ⟨word, D, newRoot, ?_, harrival.2.1,
    Nat.le_trans harrival.2.2.1 hcountM⟩
  calc
    D = runLocalSchedule ring T M reverseWord := rfl
    _ = runLocalSchedule ring T
        (runLocalSchedule ring T C pref) reverseWord := by rw [← hM]
    _ = runLocalSchedule ring T C (pref ++ reverseWord) :=
      (runLocalSchedule_append_generic ring T C pref reverseWord).symm
    _ = runLocalSchedule ring T C word := by rfl

/-- Exact three-way split at the migrated zero root.  A shielded root is
already protected.  Otherwise the migration has exposed a non-live follower,
and the two-valued source signal is either ready to fire or ready for the
live-aware reseed. -/
theorem ResetAwareZeroRootArrival.protected_or_signal_one_or_zero
    {hpsi : psi > 0} {ring : DirectedRing n} {root : Fin n}
    {C : EConfig n psi kappa tau}
    (harrival : ResetAwareZeroRootArrival hpsi ring root C) :
    PPLLWallSweepRestartableProtected.ProtectedLeaderAt hpsi C root ∨
      (((C root).core.erase.core.signal_B = ⟨1, by omega⟩ ∧
          (C (ring.rightNeighbor root)).core.erase.core.bullet ≠
            ⟨2, by omega⟩) ∨
        ((C root).core.erase.core.signal_B = ⟨0, by omega⟩ ∧
          (C (ring.rightNeighbor root)).core.erase.core.bullet ≠
            ⟨2, by omega⟩)) := by
  by_cases hshield : (C root).core.erase.core.shield = true
  · exact Or.inl ⟨⟨harrival.root_alive, hshield⟩, harrival.root_zero⟩
  · have hrightNotLive :
        (C (ring.rightNeighbor root)).core.erase.core.bullet ≠
          ⟨2, by omega⟩ := by
      rcases harrival.protected_or_right_not_live with hprotected | hfree
      · exact (hshield hprotected.1).elim
      · exact hfree
    rcases (C root).core.erase.core.signal_B with ⟨v, hv⟩
    have hval : v = 0 ∨ v = 1 := by omega
    rcases hval with rfl | rfl
    · exact Or.inr (Or.inr ⟨rfl, hrightNotLive⟩)
    · exact Or.inr (Or.inl ⟨rfl, hrightNotLive⟩)

set_option maxHeartbeats 2000000 in
/-- The weakened two-step reseed also frames the named leader's label when
only the immediate follower is known non-live. -/
theorem two_step_reseed_leader_label_of_firstFollower_free
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (leader : Fin n) (current : EConfig n psi kappa tau)
    (hnoActive : NoActiveDeletion current)
    (hunique : hasUniqueLeader n
      (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig current))
    (hleader : (current leader).core.erase.core.leader = true)
    (hjFollower :
      (current (ring.rightNeighbor leader)).core.erase.core.leader = false)
    (hjNotLive :
      (current (ring.rightNeighbor leader)).core.erase.core.bullet ≠
        ⟨2, by omega⟩) :
    let T :=
      wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
        hpsi kappa tau
    let D := runLocalSchedule ring T current [leader, leader]
    (D leader).core.erase.core.label =
      (current leader).core.erase.core.label := by
  let j := ring.rightNeighbor leader
  let T :=
    wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
      hpsi kappa tau
  let Troot := wallSweepPreCheckResetLeaderSinkPathStallTransition
    hpsi kappa tau
  let D := localStep ring T current leader
  let Droot := localStep ring Troot current leader
  have hpair : T (current leader) (current j) =
      Troot (current leader) (current j) := by
    simpa [T, Troot, j] using
      (wallSweepResetProbePreCheckResetLeaderSinkPathStall_eq_of_left_leader
        hpsi kappa tau (current leader) (current j) hleader)
  have hD : D = Droot :=
    localStep_eq_of_pair_eq ring T Troot current leader
      (by simpa [j] using hpair)
  have hopen : WallPriorityOpen (current leader) (current j) :=
    WallPriorityOpen.of_noActiveDeletion current hnoActive ring leader
  have hfirstPair :=
    wallSweepResetProbePreCheckResetLeaderSinkPathStall_source_follower_labels
      hpsi (current leader) (current j) hopen (.inl hleader)
        (by simpa [j] using hjFollower)
  have hDLeader : D leader = (T (current leader) (current j)).1 := by
    simp [D, T, localStep, j]
  have hfirstLabel : (D leader).core.erase.core.label =
      (current leader).core.erase.core.label := by
    rw [hDLeader]
    exact hfirstPair.1
  have hsafe :
      (current j).core.erase.core.bullet = ⟨2, by omega⟩ →
        (current leader).core.erase.core.shield = true := by
    intro hlive
    exact (hjNotLive (by simpa [j] using hlive)).elim
  have hnormalRoot :=
    PPLLPpsiLeaderCreationRepair.leaderStep_to_normalizedOutgoingUniqueLeaderAt
      hpsi ring hn current leader hnoActive hunique hleader
        (by simpa [j] using hjFollower) (by simpa [j] using hsafe)
  change PPLLPpsiLeaderCreationRepair.NormalizedOutgoingUniqueLeaderAt
    hpsi ring Droot leader at hnormalRoot
  have hnormal :
      PPLLPpsiLeaderCreationRepair.NormalizedOutgoingUniqueLeaderAt
        hpsi ring D leader := by
    rw [hD]
    exact hnormalRoot
  obtain ⟨hnoActiveD, _huniqueD, hleaderD, hjFollowerD,
      _halignedD, _hleftProbeD, _hrightProbeD,
      _hleftNeutralD, _hrightNeutralD, _hleftResetD,
      _hleftEchoD, _hrightEchoD, _hsafeD⟩ := hnormal
  let E := localStep ring T D leader
  have hopenD : WallPriorityOpen (D leader) (D j) :=
    WallPriorityOpen.of_noActiveDeletion D hnoActiveD ring leader
  have hsecondPair :=
    wallSweepResetProbePreCheckResetLeaderSinkPathStall_source_follower_labels
      hpsi (D leader) (D j) hopenD (.inl hleaderD)
        (by simpa [j] using hjFollowerD)
  have hELeader : E leader = (T (D leader) (D j)).1 := by
    simp [E, T, localStep, j]
  have hsecondLabel : (E leader).core.erase.core.label =
      (D leader).core.erase.core.label := by
    rw [hELeader]
    exact hsecondPair.1
  simpa [T, D, E, runLocalSchedule] using
    hsecondLabel.trans hfirstLabel

/-- The birth-signal wrapper is inert across a safe two-edge leader replay.
Safety gives the established normalized first output, in particular survival
of the named leader needed to guard the second interaction. -/
theorem runLocalSchedule_birthSignalZero_two_leader_eq_of_safe
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (leader : Fin n) (current : EConfig n psi kappa tau)
    (hnoActive : NoActiveDeletion current)
    (hunique : hasUniqueLeader n
      (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig current))
    (hleader : (current leader).core.erase.core.leader = true)
    (hrightFollower :
      (current (ring.rightNeighbor leader)).core.erase.core.leader = false)
    (hsafe :
      (current (ring.rightNeighbor leader)).core.erase.core.bullet =
          ⟨2, by omega⟩ →
        (current leader).core.erase.core.shield = true) :
    runLocalSchedule ring
        (wallSweepBirthSignalZeroPathStallTransition
          hpsi kappa tau) current [leader, leader] =
      runLocalSchedule ring
        (wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
          hpsi kappa tau) current [leader, leader] := by
  let Troot := wallSweepPreCheckResetLeaderSinkPathStallTransition
    hpsi kappa tau
  let Told :=
    wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
      hpsi kappa tau
  let Tnew := wallSweepBirthSignalZeroPathStallTransition
    hpsi kappa tau
  let Droot := localStep ring Troot current leader
  let Dold := localStep ring Told current leader
  have hfirst : localStep ring Tnew current leader = Dold := by
    apply localStep_eq_of_pair_eq
    simpa [Tnew, Told] using
      wallSweepBirthSignalZeroPathStall_eq_of_left_leader
        hpsi kappa tau (current leader)
          (current (ring.rightNeighbor leader)) hleader
  have hrootEq : Dold = Droot := by
    apply localStep_eq_of_pair_eq
    simpa [Told, Troot] using
      wallSweepResetProbePreCheckResetLeaderSinkPathStall_eq_of_left_leader
        hpsi kappa tau (current leader)
          (current (ring.rightNeighbor leader)) hleader
  have hnormalRoot :=
    PPLLPpsiLeaderCreationRepair.leaderStep_to_normalizedOutgoingUniqueLeaderAt
      hpsi ring hn current leader hnoActive hunique hleader
        hrightFollower hsafe
  change PPLLPpsiLeaderCreationRepair.NormalizedOutgoingUniqueLeaderAt
    hpsi ring Droot leader at hnormalRoot
  have hnormalOld :
      PPLLPpsiLeaderCreationRepair.NormalizedOutgoingUniqueLeaderAt
        hpsi ring Dold leader := by
    rw [hrootEq]
    exact hnormalRoot
  have hleaderD : (Dold leader).core.erase.core.leader = true :=
    hnormalOld.2.2.1
  have hsecond : localStep ring Tnew Dold leader =
      localStep ring Told Dold leader := by
    apply localStep_eq_of_pair_eq
    simpa [Tnew, Told] using
      wallSweepBirthSignalZeroPathStall_eq_of_left_leader
        hpsi kappa tau (Dold leader)
          (Dold (ring.rightNeighbor leader)) hleaderD
  simpa [Tnew, Told, Dold, runLocalSchedule, hfirst] using hsecond

/-- A shielded, zero-signal leader replay therefore closes the same restart
boundary and preserves the old nonincrease bound under the birth transition. -/
theorem two_step_birthSignalZero_reseed_shieldedRetryReady_of_source_follower
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (leader : Fin n) (current : EConfig n psi kappa tau)
    (hnoActive : NoActiveDeletion current)
    (hunique : hasUniqueLeader n
      (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig current))
    (hanchor : InitiatorAnchor
      (current leader).core.erase.core)
    (hrightFollower :
      (current (ring.rightNeighbor leader)).core.erase.core.leader = false)
    (hsignal :
      (current leader).core.erase.core.signal_B = ⟨0, by omega⟩) :
    let D := runLocalSchedule ring
      (wallSweepBirthSignalZeroPathStallTransition
        hpsi kappa tau) current [leader, leader]
    ResetAwareShieldedRetryReady hpsi ring leader D ∧
      PPLLPpsiLeaderCreationRepair.bulletTwoCount D ≤
        PPLLPpsiLeaderCreationRepair.bulletTwoCount current := by
  let Told :=
    wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
      hpsi kappa tau
  let Tnew := wallSweepBirthSignalZeroPathStallTransition
    hpsi kappa tau
  let Dold := runLocalSchedule ring Told current [leader, leader]
  let Dnew := runLocalSchedule ring Tnew current [leader, leader]
  have heq : Dnew = Dold := by
    simpa only [Dnew, Dold, Tnew, Told] using
      runLocalSchedule_birthSignalZero_two_reseed_eq
        hpsi ring leader current hnoActive hanchor hrightFollower
  have hready := two_step_reseed_shieldedRetryReady_of_source_follower
    hpsi ring hn leader current hnoActive hunique hanchor hrightFollower
  change ResetAwareShieldedRetryReady hpsi ring leader Dold at hready
  have hcount :=
    two_step_reseed_bulletTwoCount_le_of_shielded_signal_zero
      hpsi ring hn leader current hnoActive hanchor.1 hrightFollower
        hanchor.2 hsignal
  change PPLLPpsiLeaderCreationRepair.bulletTwoCount Dold ≤
    PPLLPpsiLeaderCreationRepair.bulletTwoCount current at hcount
  change ResetAwareShieldedRetryReady hpsi ring leader Dnew ∧
    PPLLPpsiLeaderCreationRepair.bulletTwoCount Dnew ≤
      PPLLPpsiLeaderCreationRepair.bulletTwoCount current
  rw [heq]
  exact ⟨hready, hcount⟩

/-- A normalized follower B-step followed by one named leader A-step has the
same literal execution under the birth-signal and old reset-probe
transitions. -/
theorem ResetAwareNormalizedPrefixState.run_birthSignalZero_follower_then_leader_eq
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (leader : Fin n) (base current : EConfig n psi kappa tau)
    (steps : Nat)
    (hstate : ResetAwareNormalizedPrefixState
      hpsi ring leader base current steps)
    (hlt : steps < n - 1) :
    let e := groupOffset ring leader steps
    runLocalSchedule ring
        (wallSweepBirthSignalZeroPathStallTransition
          hpsi kappa tau) current [e, leader] =
      runLocalSchedule ring
        (wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
          hpsi kappa tau) current [e, leader] := by
  let e := groupOffset ring leader steps
  let Told :=
    wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
      hpsi kappa tau
  let Tnew := wallSweepBirthSignalZeroPathStallTransition
    hpsi kappa tau
  let C1old := localStep ring Told current e
  let C1new := localStep ring Tnew current e
  have hfirst : C1new = C1old := by
    simpa only [C1new, C1old, Tnew, Told, e] using
      hstate.localStep_birthSignalZero_eq_resetProbe
        hpsi ring hn leader base current steps hlt
  have hnpos : 0 < n := by omega
  have heBound : steps < n := by omega
  have hjBound : steps + 1 < n := by omega
  have heNotLeader : e ≠ leader := by
    have hne := groupOffset_ne_of_lt ring leader heBound
      hnpos (Nat.ne_of_gt hstate.steps_pos)
    exact fun heq =>
      hne (heq.trans (groupOffset_zero_eq ring leader).symm)
  have hjNotLeader : groupOffset ring leader (steps + 1) ≠ leader := by
    have hne := groupOffset_ne_of_lt ring leader hjBound
      hnpos (Nat.ne_of_gt (Nat.zero_lt_succ steps))
    exact fun heq =>
      hne (heq.trans (groupOffset_zero_eq ring leader).symm)
  have hneighbor : ring.rightNeighbor e =
      groupOffset ring leader (steps + 1) := by
    simpa [e] using rightNeighbor_groupOffset ring leader steps
  have hstep := resetAwareFollower_localStep_normalizes
    hpsi ring hn current e hstate.no_active
      (hstate.unique_leader e heNotLeader) hstate.frontier_reset
      (by rw [hneighbor]; exact hstate.unique_leader _ hjNotLeader)
  change ResetAwareFollowerGlobalStepFrame
    hpsi ring current C1old e at hstep
  have hleaderC1 : (C1old leader).core.erase.core.leader = true :=
    (hstep.leader_eq leader).trans hstate.leader_alive
  have hsecond : localStep ring Tnew C1old leader =
      localStep ring Told C1old leader := by
    apply localStep_eq_of_pair_eq
    simpa [Tnew, Told] using
      wallSweepBirthSignalZeroPathStall_eq_of_left_leader
        hpsi kappa tau (C1old leader)
          (C1old (ring.rightNeighbor leader)) hleaderC1
  change localStep ring Tnew C1new leader =
    localStep ring Told C1old leader
  rw [hfirst]
  exact hsecond

/-- The corresponding B,A,A word is exact whenever the old follower output
makes the subsequent two-edge leader replay safe. -/
theorem ResetAwareNormalizedPrefixState.run_birthSignalZero_follower_then_two_leader_eq_of_safe
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (leader : Fin n) (base current : EConfig n psi kappa tau)
    (steps : Nat)
    (hstate : ResetAwareNormalizedPrefixState
      hpsi ring leader base current steps)
    (hlt : steps < n - 1)
    (hsafe :
      let e := groupOffset ring leader steps
      let C1 := localStep ring
        (wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
          hpsi kappa tau) current e
      (C1 (ring.rightNeighbor leader)).core.erase.core.bullet =
          ⟨2, by omega⟩ →
        (C1 leader).core.erase.core.shield = true) :
    let e := groupOffset ring leader steps
    runLocalSchedule ring
        (wallSweepBirthSignalZeroPathStallTransition
          hpsi kappa tau) current [e, leader, leader] =
      runLocalSchedule ring
        (wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
          hpsi kappa tau) current [e, leader, leader] := by
  let e := groupOffset ring leader steps
  let Told :=
    wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
      hpsi kappa tau
  let Tnew := wallSweepBirthSignalZeroPathStallTransition
    hpsi kappa tau
  let C1old := localStep ring Told current e
  let C1new := localStep ring Tnew current e
  have hfirst : C1new = C1old := by
    simpa only [C1new, C1old, Tnew, Told, e] using
      hstate.localStep_birthSignalZero_eq_resetProbe
        hpsi ring hn leader base current steps hlt
  have hnpos : 0 < n := by omega
  have heBound : steps < n := by omega
  have hjBound : steps + 1 < n := by omega
  have heNotLeader : e ≠ leader := by
    have hne := groupOffset_ne_of_lt ring leader heBound
      hnpos (Nat.ne_of_gt hstate.steps_pos)
    exact fun heq =>
      hne (heq.trans (groupOffset_zero_eq ring leader).symm)
  have hjNotLeader : groupOffset ring leader (steps + 1) ≠ leader := by
    have hne := groupOffset_ne_of_lt ring leader hjBound
      hnpos (Nat.ne_of_gt (Nat.zero_lt_succ steps))
    exact fun heq =>
      hne (heq.trans (groupOffset_zero_eq ring leader).symm)
  have hneighbor : ring.rightNeighbor e =
      groupOffset ring leader (steps + 1) := by
    simpa [e] using rightNeighbor_groupOffset ring leader steps
  have hstep := resetAwareFollower_localStep_normalizes
    hpsi ring hn current e hstate.no_active
      (hstate.unique_leader e heNotLeader) hstate.frontier_reset
      (by rw [hneighbor]; exact hstate.unique_leader _ hjNotLeader)
  change ResetAwareFollowerGlobalStepFrame
    hpsi ring current C1old e at hstep
  have hleaderC1 : (C1old leader).core.erase.core.leader = true :=
    (hstep.leader_eq leader).trans hstate.leader_alive
  have huniqueC1 : hasUniqueLeader n
      (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig C1old) := by
    refine ⟨leader, hleaderC1, ?_⟩
    intro i hi
    by_cases hil : i = leader
    · exact hil
    · have hfalse := (hstep.leader_eq i).trans
          (hstate.unique_leader i hil)
      change (C1old i).core.erase.core.leader = true at hi
      rw [hfalse] at hi
      contradiction
  have hfirstNe : ring.rightNeighbor leader ≠ leader :=
    rightNeighbor_ne_self_of_one_lt ring hn leader
  have hrightFollowerC1 :
      (C1old (ring.rightNeighbor leader)).core.erase.core.leader = false :=
    (hstep.leader_eq (ring.rightNeighbor leader)).trans
      (hstate.unique_leader (ring.rightNeighbor leader) hfirstNe)
  have hreseed := runLocalSchedule_birthSignalZero_two_leader_eq_of_safe
    hpsi ring hn leader C1old hstep.no_active huniqueC1 hleaderC1
      hrightFollowerC1 (by simpa [C1old, Told, e] using hsafe)
  change runLocalSchedule ring Tnew C1new [leader, leader] =
    runLocalSchedule ring Told C1old [leader, leader]
  rw [hfirst]
  exact hreseed

/-- The B,A,A transport is automatically safe under global live-bullet
freedom: the old follower step preserves that invariant, so the following
leader replay cannot meet an unshielded live follower. -/
theorem ResetAwareNormalizedPrefixState.run_birthSignalZero_follower_then_two_leader_eq_of_bulletTwoFree
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (leader : Fin n) (base current : EConfig n psi kappa tau)
    (steps : Nat)
    (hstate : ResetAwareNormalizedPrefixState
      hpsi ring leader base current steps)
    (hlt : steps < n - 1)
    (hfree :
      PPLLPpsiLeaderCreationRepair.BulletTwoFreeAwayFrom current leader) :
    let e := groupOffset ring leader steps
    runLocalSchedule ring
        (wallSweepBirthSignalZeroPathStallTransition
          hpsi kappa tau) current [e, leader, leader] =
      runLocalSchedule ring
        (wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
          hpsi kappa tau) current [e, leader, leader] := by
  let e := groupOffset ring leader steps
  let j := groupOffset ring leader (steps + 1)
  let Told :=
    wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
      hpsi kappa tau
  let C1old := localStep ring Told current e
  have hnpos : 0 < n := by omega
  have heBound : steps < n := by omega
  have hjBound : steps + 1 < n := by omega
  have hneighbor : ring.rightNeighbor e = j := by
    simpa [e, j] using rightNeighbor_groupOffset ring leader steps
  have heNotLeader : e ≠ leader := by
    have hne := groupOffset_ne_of_lt ring leader heBound
      hnpos (Nat.ne_of_gt hstate.steps_pos)
    exact fun heq =>
      hne (heq.trans (groupOffset_zero_eq ring leader).symm)
  have hjNotLeader : j ≠ leader := by
    have hne := groupOffset_ne_of_lt ring leader hjBound
      hnpos (Nat.ne_of_gt (Nat.zero_lt_succ steps))
    exact fun heq =>
      hne (heq.trans (groupOffset_zero_eq ring leader).symm)
  have hrightFollower :
      (current (ring.rightNeighbor e)).core.erase.core.leader = false := by
    rw [hneighbor]
    exact hstate.unique_leader j hjNotLeader
  have hfreeC1 := resetAwareFollower_localStep_bulletTwoFreeAwayFrom
    hpsi ring hn current e leader hstate.no_active
      (hstate.unique_leader e heNotLeader) hstate.frontier_reset
      hrightFollower hfree heNotLeader
      (by simpa [hneighbor] using hjNotLeader)
  change PPLLPpsiLeaderCreationRepair.BulletTwoFreeAwayFrom
    C1old leader at hfreeC1
  have hfirstNe : ring.rightNeighbor leader ≠ leader :=
    rightNeighbor_ne_self_of_one_lt ring hn leader
  have hsafe :
      (C1old (ring.rightNeighbor leader)).core.erase.core.bullet =
          ⟨2, by omega⟩ →
        (C1old leader).core.erase.core.shield = true := by
    intro hlive
    exact (hfreeC1 (ring.rightNeighbor leader) hfirstNe hlive).elim
  exact hstate.run_birthSignalZero_follower_then_two_leader_eq_of_safe
    hpsi ring hn leader base current steps hlt
      (by simpa [e, Told, C1old] using hsafe)

/-- Two birth-signal leader-edge interactions rebuild a shielded frontier and
do not increase live-bullet mass.  Shielding makes the replay safety premise
immediate, so both conclusions are exact transports of the established
two-edge repair. -/
theorem two_step_reseed_birthSignalZero_shieldedRetryReady_and_count_le_of_source_follower
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (leader : Fin n) (current : EConfig n psi kappa tau)
    (hnoActive : NoActiveDeletion current)
    (hunique : hasUniqueLeader n
      (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig current))
    (hanchor : InitiatorAnchor (current leader).core.erase.core)
    (hrightFollower :
      (current (ring.rightNeighbor leader)).core.erase.core.leader = false)
    (hleaderSignalZero :
      (current leader).core.erase.core.signal_B = ⟨0, by omega⟩) :
    let T := wallSweepBirthSignalZeroPathStallTransition
      hpsi kappa tau
    let D := runLocalSchedule ring T current [leader, leader]
    ResetAwareShieldedRetryReady hpsi ring leader D ∧
      PPLLPpsiLeaderCreationRepair.bulletTwoCount D ≤
        PPLLPpsiLeaderCreationRepair.bulletTwoCount current := by
  have heq := runLocalSchedule_birthSignalZero_two_leader_eq_of_safe
    hpsi ring hn leader current hnoActive hunique hanchor.1
      hrightFollower (fun _ => hanchor.2)
  have hready := two_step_reseed_shieldedRetryReady_of_source_follower
    hpsi ring hn leader current hnoActive hunique hanchor hrightFollower
  have hcount := two_step_reseed_bulletTwoCount_le_of_shielded_signal_zero
    hpsi ring hn leader current hnoActive hanchor.1 hrightFollower
      hanchor.2 hleaderSignalZero
  dsimp only at heq hready hcount ⊢
  rw [heq]
  exact ⟨hready, hcount⟩

set_option maxHeartbeats 3000000 in
/-- Birth-signal-transition form of the nearest-live B,A attempt. -/
theorem ResetAwareNormalizedPrefixState.first_live_then_birthSignalZero_leader_attempt
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (leader : Fin n) (base current : EConfig n psi kappa tau)
    (hstate : ResetAwareNormalizedPrefixState
      hpsi ring leader base current 1)
    (hroom : 1 < n - 1)
    (hleaderSignalZero :
      (current leader).core.erase.core.signal_B = ⟨0, by omega⟩)
    (hrightLive :
      (current (groupOffset ring leader 2)).core.erase.core.bullet =
        ⟨2, by omega⟩) :
    let e := groupOffset ring leader 1
    let T := wallSweepBirthSignalZeroPathStallTransition
      hpsi kappa tau
    let C1 := localStep ring T current e
    let D := localStep ring T C1 leader
    (C1 e).core.erase.core.bullet = ⟨2, by omega⟩ ∧
      (C1 (groupOffset ring leader 2)).core.erase.core.bullet =
        ⟨0, by omega⟩ ∧
      NoActiveDeletion D ∧
      (D leader).core.erase.core.label =
        (current leader).core.erase.core.label ∧
      (D leader).core.erase.core.signal_B = ⟨0, by omega⟩ ∧
      ((hasUniqueLeader n
          (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig D) ∧
          (D leader).core.erase.core.leader = true ∧
          (D leader).core.erase.core.shield = true ∧
          (D (ring.rightNeighbor leader)).core.erase.core.bullet =
            ⟨2, by omega⟩ ∧
          PPLLPpsiLeaderCreationRepair.bulletTwoCount D ≤
            PPLLPpsiLeaderCreationRepair.bulletTwoCount current) ∨
        (RawLeaderless
            (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig D) ∧
          PPLLPpsiLeaderCreationRepair.bulletTwoCount D <
            PPLLPpsiLeaderCreationRepair.bulletTwoCount current)) := by
  let e := groupOffset ring leader 1
  let Told :=
    wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
      hpsi kappa tau
  let Tnew := wallSweepBirthSignalZeroPathStallTransition
    hpsi kappa tau
  let C1old := localStep ring Told current e
  let C1new := localStep ring Tnew current e
  let Dold := localStep ring Told C1old leader
  let Dnew := localStep ring Tnew C1new leader
  have hC1 : C1new = C1old := by
    simpa only [C1new, C1old, Tnew, Told, e] using
      hstate.localStep_birthSignalZero_eq_resetProbe
        hpsi ring hn leader base current 1 hroom
  have hD : Dnew = Dold := by
    simpa only [Dnew, Dold, C1new, C1old, Tnew, Told, e,
      runLocalSchedule] using
      hstate.run_birthSignalZero_follower_then_leader_eq
        hpsi ring hn leader base current 1 hroom
  have hold := hstate.first_live_then_leader_attempt
    hpsi ring hn leader base current hroom hleaderSignalZero hrightLive
  change (C1old e).core.erase.core.bullet = ⟨2, by omega⟩ ∧
      (C1old (groupOffset ring leader 2)).core.erase.core.bullet =
        ⟨0, by omega⟩ ∧
      NoActiveDeletion Dold ∧
      (Dold leader).core.erase.core.label =
        (current leader).core.erase.core.label ∧
      (Dold leader).core.erase.core.signal_B = ⟨0, by omega⟩ ∧
      ((hasUniqueLeader n
          (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig Dold) ∧
          (Dold leader).core.erase.core.leader = true ∧
          (Dold leader).core.erase.core.shield = true ∧
          (Dold (ring.rightNeighbor leader)).core.erase.core.bullet =
            ⟨2, by omega⟩ ∧
          PPLLPpsiLeaderCreationRepair.bulletTwoCount Dold ≤
            PPLLPpsiLeaderCreationRepair.bulletTwoCount current) ∨
        (RawLeaderless
            (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig Dold) ∧
          PPLLPpsiLeaderCreationRepair.bulletTwoCount Dold <
            PPLLPpsiLeaderCreationRepair.bulletTwoCount current)) at hold
  change (C1new e).core.erase.core.bullet = ⟨2, by omega⟩ ∧
      (C1new (groupOffset ring leader 2)).core.erase.core.bullet =
        ⟨0, by omega⟩ ∧
      NoActiveDeletion Dnew ∧
      (Dnew leader).core.erase.core.label =
        (current leader).core.erase.core.label ∧
      (Dnew leader).core.erase.core.signal_B = ⟨0, by omega⟩ ∧
      ((hasUniqueLeader n
          (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig Dnew) ∧
          (Dnew leader).core.erase.core.leader = true ∧
          (Dnew leader).core.erase.core.shield = true ∧
          (Dnew (ring.rightNeighbor leader)).core.erase.core.bullet =
            ⟨2, by omega⟩ ∧
          PPLLPpsiLeaderCreationRepair.bulletTwoCount Dnew ≤
            PPLLPpsiLeaderCreationRepair.bulletTwoCount current) ∨
        (RawLeaderless
            (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig Dnew) ∧
          PPLLPpsiLeaderCreationRepair.bulletTwoCount Dnew <
            PPLLPpsiLeaderCreationRepair.bulletTwoCount current))
  rw [hC1, hD]
  exact hold

set_option maxHeartbeats 2000000 in
/-- The unshielded zero-signal branch of a zero-root arrival takes two leader
interactions to the live-aware restart boundary.  The root label is preserved
and global live-bullet mass does not increase. -/
theorem ResetAwareZeroRootArrival.two_step_liveRetryReady_of_signal_zero
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (root : Fin n) (C : EConfig n psi kappa tau)
    (harrival : ResetAwareZeroRootArrival hpsi ring root C)
    (hsignal : (C root).core.erase.core.signal_B = ⟨0, by omega⟩)
    (hrightNotLive :
      (C (ring.rightNeighbor root)).core.erase.core.bullet ≠
        ⟨2, by omega⟩) :
    let T :=
      wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
        hpsi kappa tau
    let D := runLocalSchedule ring T C [root, root]
    ResetAwareLiveRetryReady hpsi ring root D ∧
      (D root).core.erase.core.label = ⟨0, hpsi⟩ ∧
      PPLLPpsiLeaderCreationRepair.bulletTwoCount D ≤
        PPLLPpsiLeaderCreationRepair.bulletTwoCount C := by
  have hready := two_step_reseed_liveRetryReady_of_firstFollower_free
    hpsi ring hn root C harrival.no_active harrival.unique_leader
      harrival.root_alive harrival.right_follower hrightNotLive
  have hlabel := two_step_reseed_leader_label_of_firstFollower_free
    hpsi ring hn root C harrival.no_active harrival.unique_leader
      harrival.root_alive harrival.right_follower hrightNotLive
  have hcount :=
    two_step_reseed_bulletTwoCount_le_of_firstFollower_free_signal_zero
      hpsi ring hn root C harrival.no_active harrival.unique_leader
        harrival.root_alive hsignal harrival.right_follower hrightNotLive
  exact ⟨hready, hlabel.trans harrival.root_zero, hcount⟩

/-- Birth-signal-transition form of the zero-signal two-edge dispatch. -/
theorem ResetAwareZeroRootArrival.two_step_birthSignalZero_liveRetryReady_of_signal_zero
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (root : Fin n) (C : EConfig n psi kappa tau)
    (harrival : ResetAwareZeroRootArrival hpsi ring root C)
    (hsignal : (C root).core.erase.core.signal_B = ⟨0, by omega⟩)
    (hrightNotLive :
      (C (ring.rightNeighbor root)).core.erase.core.bullet ≠
        ⟨2, by omega⟩) :
    let T := wallSweepBirthSignalZeroPathStallTransition
      hpsi kappa tau
    let D := runLocalSchedule ring T C [root, root]
    ResetAwareLiveRetryReady hpsi ring root D ∧
      (D root).core.erase.core.label = ⟨0, hpsi⟩ ∧
      PPLLPpsiLeaderCreationRepair.bulletTwoCount D ≤
        PPLLPpsiLeaderCreationRepair.bulletTwoCount C := by
  let Told :=
    wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
      hpsi kappa tau
  let Tnew := wallSweepBirthSignalZeroPathStallTransition
    hpsi kappa tau
  let Dold := runLocalSchedule ring Told C [root, root]
  let Dnew := runLocalSchedule ring Tnew C [root, root]
  have hsafe :
      (C (ring.rightNeighbor root)).core.erase.core.bullet =
          ⟨2, by omega⟩ →
        (C root).core.erase.core.shield = true := by
    intro hlive
    exact (hrightNotLive hlive).elim
  have heq : Dnew = Dold := by
    simpa only [Dnew, Dold, Tnew, Told] using
      runLocalSchedule_birthSignalZero_two_leader_eq_of_safe
        hpsi ring hn root C harrival.no_active harrival.unique_leader
          harrival.root_alive harrival.right_follower hsafe
  have hold := harrival.two_step_liveRetryReady_of_signal_zero
    hpsi ring hn root C hsignal hrightNotLive
  change ResetAwareLiveRetryReady hpsi ring root Dold ∧
      (Dold root).core.erase.core.label = ⟨0, hpsi⟩ ∧
      PPLLPpsiLeaderCreationRepair.bulletTwoCount Dold ≤
        PPLLPpsiLeaderCreationRepair.bulletTwoCount C at hold
  change ResetAwareLiveRetryReady hpsi ring root Dnew ∧
      (Dnew root).core.erase.core.label = ⟨0, hpsi⟩ ∧
      PPLLPpsiLeaderCreationRepair.bulletTwoCount Dnew ≤
        PPLLPpsiLeaderCreationRepair.bulletTwoCount C
  rw [heq]
  exact hold

/-- The signal-one branch of a zero-root arrival fires in one interaction and
reaches a protected unique leader.  No live-bullet count bound is asserted on
this branch because firing may create a fresh live bullet. -/
theorem ResetAwareZeroRootArrival.signalOne_step_protected
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (root : Fin n) (C : EConfig n psi kappa tau)
    (harrival : ResetAwareZeroRootArrival hpsi ring root C)
    (hsignal : (C root).core.erase.core.signal_B = ⟨1, by omega⟩) :
    let D := localStep ring
      (wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
        hpsi kappa tau) C root
    NoActiveDeletion D ∧
      hasUniqueLeader n
        (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig D) ∧
      PPLLWallSweepRestartableProtected.ProtectedLeaderAt
        hpsi D root := by
  exact resetAwareLeader_signalOne_localStep_protected
    hpsi ring hn C root harrival.no_active harrival.unique_leader
      harrival.root_alive harrival.root_zero hsignal
        harrival.right_follower

/-- Birth-signal-transition form of the signal-one protected dispatch. -/
theorem ResetAwareZeroRootArrival.signalOne_birthSignalZero_step_protected
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (root : Fin n) (C : EConfig n psi kappa tau)
    (harrival : ResetAwareZeroRootArrival hpsi ring root C)
    (hsignal : (C root).core.erase.core.signal_B = ⟨1, by omega⟩) :
    let D := localStep ring
      (wallSweepBirthSignalZeroPathStallTransition
        hpsi kappa tau) C root
    NoActiveDeletion D ∧
      hasUniqueLeader n
        (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig D) ∧
      PPLLWallSweepRestartableProtected.ProtectedLeaderAt
        hpsi D root := by
  let Told :=
    wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
      hpsi kappa tau
  let Tnew := wallSweepBirthSignalZeroPathStallTransition
    hpsi kappa tau
  let Dold := localStep ring Told C root
  let Dnew := localStep ring Tnew C root
  have heq : Dnew = Dold := by
    apply localStep_eq_of_pair_eq
    simpa [Tnew, Told] using
      wallSweepBirthSignalZeroPathStall_eq_of_left_leader
        hpsi kappa tau (C root)
          (C (ring.rightNeighbor root)) harrival.root_alive
  have hold := harrival.signalOne_step_protected
    hpsi ring hn root C hsignal
  change NoActiveDeletion Dold ∧
      hasUniqueLeader n
        (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig Dold) ∧
      PPLLWallSweepRestartableProtected.ProtectedLeaderAt
        hpsi Dold root at hold
  change NoActiveDeletion Dnew ∧
      hasUniqueLeader n
        (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig Dnew) ∧
      PPLLWallSweepRestartableProtected.ProtectedLeaderAt
        hpsi Dnew root
  rw [heq]
  exact hold

set_option maxHeartbeats 2000000 in
/-- A zero-root arrival needs at most two leader interactions to expose the
next real proof boundary: a protected leader, or a zero-labelled live-aware
retry frontier with nonincreasing global live-bullet mass. -/
theorem ResetAwareZeroRootArrival.exists_protected_or_liveRetryReady
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (root : Fin n) (C : EConfig n psi kappa tau)
    (harrival : ResetAwareZeroRootArrival hpsi ring root C) :
    ∃ (word : DetSchedule n) (D : EConfig n psi kappa tau),
      D = runLocalSchedule ring
        (wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
          hpsi kappa tau) C word ∧
      (PPLLWallSweepRestartableProtected.ProtectedLeaderAt hpsi D root ∨
        (ResetAwareLiveRetryReady hpsi ring root D ∧
          (D root).core.erase.core.label = ⟨0, hpsi⟩ ∧
          PPLLPpsiLeaderCreationRepair.bulletTwoCount D ≤
            PPLLPpsiLeaderCreationRepair.bulletTwoCount C)) := by
  let T :=
    wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
      hpsi kappa tau
  rcases harrival.protected_or_signal_one_or_zero with
      hprotected | hsignalOne | hsignalZero
  · exact ⟨[], C, rfl, Or.inl hprotected⟩
  · let D := localStep ring T C root
    have hfire := harrival.signalOne_step_protected
      hpsi ring hn root C hsignalOne.1
    change NoActiveDeletion D ∧
        hasUniqueLeader n
          (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig D) ∧
        PPLLWallSweepRestartableProtected.ProtectedLeaderAt
          hpsi D root at hfire
    exact ⟨[root], D, rfl, Or.inl hfire.2.2⟩
  · let D := runLocalSchedule ring T C [root, root]
    have hretry := harrival.two_step_liveRetryReady_of_signal_zero
      hpsi ring hn root C hsignalZero.1 hsignalZero.2
    change ResetAwareLiveRetryReady hpsi ring root D ∧
        (D root).core.erase.core.label = ⟨0, hpsi⟩ ∧
        PPLLPpsiLeaderCreationRepair.bulletTwoCount D ≤
          PPLLPpsiLeaderCreationRepair.bulletTwoCount C at hretry
    exact ⟨[root, root], D, rfl, Or.inr hretry⟩

set_option maxHeartbeats 2000000 in
/-- Birth-signal-transition dispatch from a zero-root arrival. -/
theorem ResetAwareZeroRootArrival.exists_birthSignalZero_protected_or_liveRetryReady
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (root : Fin n) (C : EConfig n psi kappa tau)
    (harrival : ResetAwareZeroRootArrival hpsi ring root C) :
    ∃ (word : DetSchedule n) (D : EConfig n psi kappa tau),
      D = runLocalSchedule ring
        (wallSweepBirthSignalZeroPathStallTransition
          hpsi kappa tau) C word ∧
      (PPLLWallSweepRestartableProtected.ProtectedLeaderAt hpsi D root ∨
        (ResetAwareLiveRetryReady hpsi ring root D ∧
          (D root).core.erase.core.label = ⟨0, hpsi⟩ ∧
          PPLLPpsiLeaderCreationRepair.bulletTwoCount D ≤
            PPLLPpsiLeaderCreationRepair.bulletTwoCount C)) := by
  let T := wallSweepBirthSignalZeroPathStallTransition
    hpsi kappa tau
  rcases harrival.protected_or_signal_one_or_zero with
      hprotected | hsignalOne | hsignalZero
  · exact ⟨[], C, rfl, Or.inl hprotected⟩
  · let D := localStep ring T C root
    have hfire := harrival.signalOne_birthSignalZero_step_protected
      hpsi ring hn root C hsignalOne.1
    change NoActiveDeletion D ∧
        hasUniqueLeader n
          (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig D) ∧
        PPLLWallSweepRestartableProtected.ProtectedLeaderAt
          hpsi D root at hfire
    exact ⟨[root], D, rfl, Or.inl hfire.2.2⟩
  · let D := runLocalSchedule ring T C [root, root]
    have hretry :=
      harrival.two_step_birthSignalZero_liveRetryReady_of_signal_zero
        hpsi ring hn root C hsignalZero.1 hsignalZero.2
    change ResetAwareLiveRetryReady hpsi ring root D ∧
        (D root).core.erase.core.label = ⟨0, hpsi⟩ ∧
        PPLLPpsiLeaderCreationRepair.bulletTwoCount D ≤
          PPLLPpsiLeaderCreationRepair.bulletTwoCount C at hretry
    exact ⟨[root, root], D, rfl, Or.inr hretry⟩

set_option maxHeartbeats 3000000 in
/-- The complete pre-migration shielded scheduler, reverse migration, and
zero-root dispatch compose into one literal schedule.  Its only unresolved
branch is the explicitly named zero-labelled live-aware retry frontier. -/
theorem exists_resetAwareShieldedProtectedOrLiveRetrySchedule
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (hpsiLe : psi ≤ n)
    (leader : Fin n) (C : EConfig n psi kappa tau)
    (hready : ResetAwareShieldedRetryReady hpsi ring leader C) :
    ∃ (word : DetSchedule n) (D : EConfig n psi kappa tau)
      (newRoot : Fin n),
      D = runLocalSchedule ring
        (wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
          hpsi kappa tau) C word ∧
      (PPLLWallSweepRestartableProtected.ProtectedLeaderAt
          hpsi D newRoot ∨
        (ResetAwareLiveRetryReady hpsi ring newRoot D ∧
          (D newRoot).core.erase.core.label = ⟨0, hpsi⟩ ∧
          PPLLPpsiLeaderCreationRepair.bulletTwoCount D ≤
            PPLLPpsiLeaderCreationRepair.bulletTwoCount C)) := by
  let T :=
    wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
      hpsi kappa tau
  obtain ⟨pref, M, newRoot, hM, harrival, hcountM⟩ :=
    exists_resetAwareShieldedZeroRootArrivalSchedule
      hpsi ring hn hpsiLe leader C hready
  obtain ⟨tail, D, hD, hout⟩ :=
    harrival.exists_protected_or_liveRetryReady
      hpsi ring hn newRoot M
  let word := pref ++ tail
  refine ⟨word, D, newRoot, ?_, ?_⟩
  · calc
      D = runLocalSchedule ring T M tail := hD
      _ = runLocalSchedule ring T
          (runLocalSchedule ring T C pref) tail := by rw [← hM]
      _ = runLocalSchedule ring T C (pref ++ tail) :=
        (runLocalSchedule_append_generic ring T C pref tail).symm
      _ = runLocalSchedule ring T C word := by rfl
  · rcases hout with hprotected | hlive
    · exact Or.inl hprotected
    · exact Or.inr ⟨hlive.1, hlive.2.1,
        Nat.le_trans hlive.2.2 hcountM⟩

set_option maxHeartbeats 3000000 in
/-- Birth-signal-transition composition of shielded normalization, reverse
migration, and zero-root dispatch. -/
theorem exists_resetAwareShieldedBirthSignalZeroProtectedOrLiveRetrySchedule
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (hpsiLe : psi ≤ n)
    (leader : Fin n) (C : EConfig n psi kappa tau)
    (hready : ResetAwareShieldedRetryReady hpsi ring leader C) :
    ∃ (word : DetSchedule n) (D : EConfig n psi kappa tau)
      (newRoot : Fin n),
      D = runLocalSchedule ring
        (wallSweepBirthSignalZeroPathStallTransition
          hpsi kappa tau) C word ∧
      (PPLLWallSweepRestartableProtected.ProtectedLeaderAt
          hpsi D newRoot ∨
        (ResetAwareLiveRetryReady hpsi ring newRoot D ∧
          (D newRoot).core.erase.core.label = ⟨0, hpsi⟩ ∧
          PPLLPpsiLeaderCreationRepair.bulletTwoCount D ≤
            PPLLPpsiLeaderCreationRepair.bulletTwoCount C)) := by
  let T := wallSweepBirthSignalZeroPathStallTransition
    hpsi kappa tau
  obtain ⟨pref, M, newRoot, hM, harrival, hcountM⟩ :=
    exists_resetAwareShieldedBirthSignalZeroRootArrivalSchedule
      hpsi ring hn hpsiLe leader C hready
  obtain ⟨tail, D, hD, hout⟩ :=
    harrival.exists_birthSignalZero_protected_or_liveRetryReady
      hpsi ring hn newRoot M
  let word := pref ++ tail
  refine ⟨word, D, newRoot, ?_, ?_⟩
  · calc
      D = runLocalSchedule ring T M tail := hD
      _ = runLocalSchedule ring T
          (runLocalSchedule ring T C pref) tail := by rw [← hM]
      _ = runLocalSchedule ring T C (pref ++ tail) :=
        (runLocalSchedule_append_generic ring T C pref tail).symm
      _ = runLocalSchedule ring T C word := by rfl
  · rcases hout with hprotected | hlive
    · exact Or.inl hprotected
    · exact Or.inr ⟨hlive.1, hlive.2.1,
        Nat.le_trans hlive.2.2 hcountM⟩

set_option maxHeartbeats 3000000 in
/-- When a live responder is strictly beyond the immediate follower, the
follower step moves that bullet toward the root without exposing the leader
edge.  Two interactions at the unchanged named leader then rebuild the weak
live-retry boundary.  The global live count does not increase, while the
fixed-root mobile live rank decreases strictly. -/
theorem ResetAwareNormalizedPrefixState.far_live_then_two_step_reseed
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (leader : Fin n) (base current : EConfig n psi kappa tau)
    (steps : Nat)
    (hstate : ResetAwareNormalizedPrefixState
      hpsi ring leader base current steps)
    (hlt : steps < n - 1)
    (hfar : 1 < steps)
    (hfirstNotLive :
      (current (ring.rightNeighbor leader)).core.erase.core.bullet ≠
        ⟨2, by omega⟩)
    (hleaderSignalZero :
      (current leader).core.erase.core.signal_B = ⟨0, by omega⟩)
    (hrightLive :
      (current (groupOffset ring leader (steps + 1))).core.erase.core.bullet =
        ⟨2, by omega⟩) :
    let e := groupOffset ring leader steps
    let T := wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
      hpsi kappa tau
    let D := runLocalSchedule ring T current [e, leader, leader]
    ResetAwareLiveRetryReady hpsi ring leader D ∧
      (D leader).core.erase.core.label =
        (current leader).core.erase.core.label ∧
      PPLLPpsiLeaderCreationRepair.bulletTwoCount D ≤
        PPLLPpsiLeaderCreationRepair.bulletTwoCount current ∧
      clockwiseMobileLiveRank ring leader D <
        clockwiseMobileLiveRank ring leader current := by
  let e := groupOffset ring leader steps
  let j := groupOffset ring leader (steps + 1)
  let first := ring.rightNeighbor leader
  let T := wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
    hpsi kappa tau
  let C1 := localStep ring T current e
  let D := runLocalSchedule ring T C1 [leader, leader]
  have hnpos : 0 < n := by omega
  have heBound : steps < n := by omega
  have hjBound : steps + 1 < n := by omega
  have hneighbor : ring.rightNeighbor e = j := by
    simpa [e, j] using rightNeighbor_groupOffset ring leader steps
  have hfirstOffset : first = groupOffset ring leader 1 := by
    have hnext := rightNeighbor_groupOffset ring leader 0
    rw [groupOffset_zero_eq] at hnext
    simpa [first] using hnext
  have heNotLeader : e ≠ leader := by
    have hne := groupOffset_ne_of_lt ring leader heBound
      hnpos (Nat.ne_of_gt hstate.steps_pos)
    exact fun heq =>
      hne (heq.trans (groupOffset_zero_eq ring leader).symm)
  have hjNotLeader : j ≠ leader := by
    have hne := groupOffset_ne_of_lt ring leader hjBound
      hnpos (Nat.ne_of_gt (Nat.zero_lt_succ steps))
    exact fun heq =>
      hne (heq.trans (groupOffset_zero_eq ring leader).symm)
  have hfirstNe : first ≠ leader :=
    rightNeighbor_ne_self_of_one_lt ring hn leader
  have hfirstNeE : first ≠ e := by
    rw [hfirstOffset]
    apply groupOffset_ne_of_lt ring leader (by omega) heBound
    omega
  have hfirstNeJ : first ≠ j := by
    rw [hfirstOffset]
    apply groupOffset_ne_of_lt ring leader (by omega) hjBound
    omega
  have hstep := resetAwareFollower_localStep_normalizes
    hpsi ring hn current e hstate.no_active
      (hstate.unique_leader e heNotLeader) hstate.frontier_reset
      (by rw [hneighbor]; exact hstate.unique_leader j hjNotLeader)
  change ResetAwareFollowerGlobalStepFrame hpsi ring current C1 e at hstep
  have hleaderC1 : (C1 leader).core.erase.core.leader = true :=
    (hstep.leader_eq leader).trans hstate.leader_alive
  have hfirstFollowerC1 :
      (C1 first).core.erase.core.leader = false :=
    (hstep.leader_eq first).trans
      (hstate.unique_leader first hfirstNe)
  have huniqueC1 : hasUniqueLeader n
      (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig C1) := by
    refine ⟨leader, hleaderC1, ?_⟩
    intro i hi
    by_cases hie : i = leader
    · exact hie
    · change (C1 i).core.erase.core.leader = true at hi
      have hfalse := (hstep.leader_eq i).trans
        (hstate.unique_leader i hie)
      have hbad : (false : Bool) = true := hfalse.symm.trans hi
      exact (Bool.false_ne_true hbad).elim
  have hfirstOff : C1 first = current first :=
    hstep.off_edge first hfirstNeE (by
      rw [hneighbor]
      exact hfirstNeJ)
  have hfirstNotLiveC1 :
      (C1 first).core.erase.core.bullet ≠ ⟨2, by omega⟩ := by
    rw [hfirstOff]
    simpa [first] using hfirstNotLive
  have hleaderOff : C1 leader = current leader :=
    hstep.off_edge leader (Ne.symm heNotLeader) (by
      rw [hneighbor]
      exact Ne.symm hjNotLeader)
  have hleaderSignalZeroC1 :
      (C1 leader).core.erase.core.signal_B = ⟨0, by omega⟩ := by
    rw [hleaderOff]
    exact hleaderSignalZero
  have hready := two_step_reseed_liveRetryReady_of_firstFollower_free
    hpsi ring hn leader C1 hstep.no_active huniqueC1 hleaderC1
      (by simpa [first] using hfirstFollowerC1)
      (by simpa [first] using hfirstNotLiveC1)
  change ResetAwareLiveRetryReady hpsi ring leader D at hready
  have hlabel := two_step_reseed_leader_label_of_firstFollower_free
    hpsi ring hn leader C1 hstep.no_active huniqueC1 hleaderC1
      (by simpa [first] using hfirstFollowerC1)
      (by simpa [first] using hfirstNotLiveC1)
  change (D leader).core.erase.core.label =
    (C1 leader).core.erase.core.label at hlabel
  have hfirstCount := resetAwareFollower_localStep_bulletTwoCount_le
    hpsi ring hn current e hstate.no_active
      (hstate.unique_leader e heNotLeader) hstate.frontier_reset
      (by rw [hneighbor]; exact hstate.unique_leader j hjNotLeader)
  change PPLLPpsiLeaderCreationRepair.bulletTwoCount C1 ≤
    PPLLPpsiLeaderCreationRepair.bulletTwoCount current at hfirstCount
  have hsecondCount :=
    two_step_reseed_bulletTwoCount_le_of_firstFollower_free_signal_zero
      hpsi ring hn leader C1 hstep.no_active huniqueC1 hleaderC1
        hleaderSignalZeroC1
        (by simpa [first] using hfirstFollowerC1)
        (by simpa [first] using hfirstNotLiveC1)
  change PPLLPpsiLeaderCreationRepair.bulletTwoCount D ≤
    PPLLPpsiLeaderCreationRepair.bulletTwoCount C1 at hsecondCount
  have htotalCount :
      PPLLPpsiLeaderCreationRepair.bulletTwoCount D ≤
        PPLLPpsiLeaderCreationRepair.bulletTwoCount current :=
    Nat.le_trans hsecondCount hfirstCount
  have hrank := hstate.follower_then_two_step_reseed_mobileLiveRank_lt
    hpsi ring hn leader base current steps hlt hrightLive
  change clockwiseMobileLiveRank ring leader D <
    clockwiseMobileLiveRank ring leader current at hrank
  change ResetAwareLiveRetryReady hpsi ring leader
      (runLocalSchedule ring T current [e, leader, leader]) ∧
    ((runLocalSchedule ring T current [e, leader, leader]) leader).core.erase.core.label =
      (current leader).core.erase.core.label ∧
    PPLLPpsiLeaderCreationRepair.bulletTwoCount
        (runLocalSchedule ring T current [e, leader, leader]) ≤
      PPLLPpsiLeaderCreationRepair.bulletTwoCount current ∧
    clockwiseMobileLiveRank ring leader
        (runLocalSchedule ring T current [e, leader, leader]) <
      clockwiseMobileLiveRank ring leader current
  change ResetAwareLiveRetryReady hpsi ring leader D ∧
    (D leader).core.erase.core.label =
      (current leader).core.erase.core.label ∧
    PPLLPpsiLeaderCreationRepair.bulletTwoCount D ≤
      PPLLPpsiLeaderCreationRepair.bulletTwoCount current ∧
    clockwiseMobileLiveRank ring leader D <
      clockwiseMobileLiveRank ring leader current
  exact ⟨hready,
    hlabel.trans (congrArg
      (fun u : ExpiringAgentState psi kappa tau =>
        u.core.erase.core.label) hleaderOff),
    htotalCount, hrank⟩

set_option maxHeartbeats 3000000 in
/-- Birth-signal-transition form of the far-live B,A,A descent. -/
theorem ResetAwareNormalizedPrefixState.far_live_then_birthSignalZero_two_step_reseed
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (leader : Fin n) (base current : EConfig n psi kappa tau)
    (steps : Nat)
    (hstate : ResetAwareNormalizedPrefixState
      hpsi ring leader base current steps)
    (hlt : steps < n - 1)
    (hfar : 1 < steps)
    (hfirstNotLive :
      (current (ring.rightNeighbor leader)).core.erase.core.bullet ≠
        ⟨2, by omega⟩)
    (hleaderSignalZero :
      (current leader).core.erase.core.signal_B = ⟨0, by omega⟩)
    (hrightLive :
      (current (groupOffset ring leader (steps + 1))).core.erase.core.bullet =
        ⟨2, by omega⟩) :
    let e := groupOffset ring leader steps
    let T := wallSweepBirthSignalZeroPathStallTransition
      hpsi kappa tau
    let D := runLocalSchedule ring T current [e, leader, leader]
    ResetAwareLiveRetryReady hpsi ring leader D ∧
      (D leader).core.erase.core.label =
        (current leader).core.erase.core.label ∧
      PPLLPpsiLeaderCreationRepair.bulletTwoCount D ≤
        PPLLPpsiLeaderCreationRepair.bulletTwoCount current ∧
      clockwiseMobileLiveRank ring leader D <
        clockwiseMobileLiveRank ring leader current := by
  let e := groupOffset ring leader steps
  let j := groupOffset ring leader (steps + 1)
  let first := ring.rightNeighbor leader
  let Told :=
    wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
      hpsi kappa tau
  let Tnew := wallSweepBirthSignalZeroPathStallTransition
    hpsi kappa tau
  let C1old := localStep ring Told current e
  let Dold := runLocalSchedule ring Told current [e, leader, leader]
  let Dnew := runLocalSchedule ring Tnew current [e, leader, leader]
  have hneighbor : ring.rightNeighbor e = j := by
    simpa [e, j] using rightNeighbor_groupOffset ring leader steps
  have hfirstOffset : first = groupOffset ring leader 1 := by
    have hnext := rightNeighbor_groupOffset ring leader 0
    rw [groupOffset_zero_eq] at hnext
    simpa [first] using hnext
  have hfirstNeE : first ≠ e := by
    rw [hfirstOffset]
    apply groupOffset_ne_of_lt ring leader (by omega) (by omega)
    omega
  have hfirstNeJ : first ≠ j := by
    rw [hfirstOffset]
    apply groupOffset_ne_of_lt ring leader (by omega) (by omega)
    omega
  have hfirstOff : C1old first = current first := by
    simp [C1old, Told, localStep, hneighbor, first, j,
      hfirstNeE, hfirstNeJ]
  have hsafe :
      (C1old (ring.rightNeighbor leader)).core.erase.core.bullet =
          ⟨2, by omega⟩ →
        (C1old leader).core.erase.core.shield = true := by
    intro hlive
    exact (hfirstNotLive (by
      change (current first).core.erase.core.bullet = ⟨2, by omega⟩
      rw [← hfirstOff]
      simpa [first] using hlive)).elim
  have hD : Dnew = Dold := by
    simpa only [Dnew, Dold, Tnew, Told, e, C1old] using
      hstate.run_birthSignalZero_follower_then_two_leader_eq_of_safe
        hpsi ring hn leader base current steps hlt hsafe
  have hold := hstate.far_live_then_two_step_reseed
    hpsi ring hn leader base current steps hlt hfar hfirstNotLive
      hleaderSignalZero hrightLive
  change ResetAwareLiveRetryReady hpsi ring leader Dold ∧
      (Dold leader).core.erase.core.label =
        (current leader).core.erase.core.label ∧
      PPLLPpsiLeaderCreationRepair.bulletTwoCount Dold ≤
        PPLLPpsiLeaderCreationRepair.bulletTwoCount current ∧
      clockwiseMobileLiveRank ring leader Dold <
        clockwiseMobileLiveRank ring leader current at hold
  change ResetAwareLiveRetryReady hpsi ring leader Dnew ∧
      (Dnew leader).core.erase.core.label =
        (current leader).core.erase.core.label ∧
      PPLLPpsiLeaderCreationRepair.bulletTwoCount Dnew ≤
        PPLLPpsiLeaderCreationRepair.bulletTwoCount current ∧
      clockwiseMobileLiveRank ring leader Dnew <
        clockwiseMobileLiveRank ring leader current
  rw [hD]
  exact hold

set_option maxHeartbeats 3000000 in
/-- A true-echo collision whose responder is not live can be replayed through
the two root interactions into the live-aware retry frontier.  The echo rank
strictly decreases through the recorded blocker effect, while the mobile-live
rank is unchanged and global live mass does not increase. -/
theorem ResetAwareNormalizedPrefixState.collision_then_liveRetryReady
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (leader : Fin n) (base current : EConfig n psi kappa tau)
    (steps : Nat)
    (hstate : ResetAwareNormalizedPrefixState
      hpsi ring leader base current steps)
    (hlt : steps < n - 1)
    (hvisited : VisitedPrefixLiveFree ring leader current steps)
    (hrightEcho :
      (current (groupOffset ring leader (steps + 1))).core.erase.core.echo =
        true)
    (hrightNotLive :
      (current (groupOffset ring leader (steps + 1))).core.erase.core.bullet ≠
        ⟨2, by omega⟩)
    (hrootSignalZero :
      (current leader).core.erase.core.signal_B = ⟨0, by omega⟩) :
    let e := groupOffset ring leader steps
    let T := wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
      hpsi kappa tau
    let D := runLocalSchedule ring T current [e, leader, leader]
    FirstBlockerEffect ring leader current D ⟨steps, hlt⟩ ∧
      ResetAwareLiveRetryReady hpsi ring leader D ∧
      (D leader).core.erase.core.label =
        (current leader).core.erase.core.label ∧
      PPLLPpsiLeaderCreationRepair.bulletTwoCount D ≤
        PPLLPpsiLeaderCreationRepair.bulletTwoCount current ∧
      clockwiseMobileLiveRank ring leader D =
        clockwiseMobileLiveRank ring leader current := by
  let e := groupOffset ring leader steps
  let j := groupOffset ring leader (steps + 1)
  let first := ring.rightNeighbor leader
  let T := wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
    hpsi kappa tau
  let C1 := localStep ring T current e
  let D := runLocalSchedule ring T C1 [leader, leader]
  have hnpos : 0 < n := by omega
  have heBound : steps < n := by omega
  have hjBound : steps + 1 < n := by omega
  have hneighbor : ring.rightNeighbor e = j := by
    simpa [e, j] using rightNeighbor_groupOffset ring leader steps
  have hfirstOffset : first = groupOffset ring leader 1 := by
    have hnext := rightNeighbor_groupOffset ring leader 0
    rw [groupOffset_zero_eq] at hnext
    simpa [first] using hnext
  have heNotLeader : e ≠ leader := by
    have hne := groupOffset_ne_of_lt ring leader heBound
      hnpos (Nat.ne_of_gt hstate.steps_pos)
    exact fun heq =>
      hne (heq.trans (groupOffset_zero_eq ring leader).symm)
  have hjNotLeader : j ≠ leader := by
    have hne := groupOffset_ne_of_lt ring leader hjBound
      hnpos (Nat.ne_of_gt (Nat.zero_lt_succ steps))
    exact fun heq =>
      hne (heq.trans (groupOffset_zero_eq ring leader).symm)
  have hstep := resetAwareFollower_localStep_normalizes
    hpsi ring hn current e hstate.no_active
      (hstate.unique_leader e heNotLeader) hstate.frontier_reset
      (by rw [hneighbor]; exact hstate.unique_leader j hjNotLeader)
  change ResetAwareFollowerGlobalStepFrame hpsi ring current C1 e at hstep
  have hvisitedC1 := hstate.visitedLiveFree_step
    hpsi ring hn leader base current steps hlt hvisited hrightNotLive
  change VisitedPrefixLiveFree ring leader C1 (steps + 1) at hvisitedC1
  have hfirstNotLiveC1 :
      (C1 first).core.erase.core.bullet ≠ ⟨2, by omega⟩ := by
    rw [hfirstOffset]
    exact hvisitedC1 1 (by omega) (by omega)
  have hleaderC1 : (C1 leader).core.erase.core.leader = true :=
    (hstep.leader_eq leader).trans hstate.leader_alive
  have hfirstNe : first ≠ leader :=
    rightNeighbor_ne_self_of_one_lt ring hn leader
  have hfirstFollowerC1 :
      (C1 first).core.erase.core.leader = false :=
    (hstep.leader_eq first).trans
      (hstate.unique_leader first hfirstNe)
  have huniqueC1 : hasUniqueLeader n
      (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig C1) := by
    refine ⟨leader, hleaderC1, ?_⟩
    intro i hi
    by_cases hine : i = leader
    · exact hine
    · change (C1 i).core.erase.core.leader = true at hi
      have hfalse := (hstep.leader_eq i).trans
        (hstate.unique_leader i hine)
      have hbad : (false : Bool) = true := hfalse.symm.trans hi
      exact (Bool.false_ne_true hbad).elim
  have hleaderOff : C1 leader = current leader :=
    hstep.off_edge leader (Ne.symm heNotLeader) (by
      rw [hneighbor]
      exact Ne.symm hjNotLeader)
  have hsignalC1 :
      (C1 leader).core.erase.core.signal_B = ⟨0, by omega⟩ := by
    rw [hleaderOff]
    exact hrootSignalZero
  have hready := two_step_reseed_liveRetryReady_of_firstFollower_free
    hpsi ring hn leader C1 hstep.no_active huniqueC1 hleaderC1
      (by simpa [first] using hfirstFollowerC1)
      (by simpa [first] using hfirstNotLiveC1)
  change ResetAwareLiveRetryReady hpsi ring leader D at hready
  have hlabel := two_step_reseed_leader_label_of_firstFollower_free
    hpsi ring hn leader C1 hstep.no_active huniqueC1 hleaderC1
      (by simpa [first] using hfirstFollowerC1)
      (by simpa [first] using hfirstNotLiveC1)
  change (D leader).core.erase.core.label =
    (C1 leader).core.erase.core.label at hlabel
  have hfirstCount := resetAwareFollower_localStep_bulletTwoCount_le
    hpsi ring hn current e hstate.no_active
      (hstate.unique_leader e heNotLeader) hstate.frontier_reset
      (by rw [hneighbor]; exact hstate.unique_leader j hjNotLeader)
  change PPLLPpsiLeaderCreationRepair.bulletTwoCount C1 ≤
    PPLLPpsiLeaderCreationRepair.bulletTwoCount current at hfirstCount
  have hsecondCount :=
    two_step_reseed_bulletTwoCount_le_of_firstFollower_free_signal_zero
      hpsi ring hn leader C1 hstep.no_active huniqueC1 hleaderC1
        hsignalC1
        (by simpa [first] using hfirstFollowerC1)
        (by simpa [first] using hfirstNotLiveC1)
  change PPLLPpsiLeaderCreationRepair.bulletTwoCount D ≤
    PPLLPpsiLeaderCreationRepair.bulletTwoCount C1 at hsecondCount
  have htotalCount : PPLLPpsiLeaderCreationRepair.bulletTwoCount D ≤
      PPLLPpsiLeaderCreationRepair.bulletTwoCount current :=
    Nat.le_trans hsecondCount hfirstCount
  have hmobile :=
    hstate.follower_then_two_step_reseed_mobileLiveRank_eq_of_visited_free
      hpsi ring hn leader base current steps hlt hvisited hrightNotLive
  change clockwiseMobileLiveRank ring leader D =
    clockwiseMobileLiveRank ring leader current at hmobile
  have hoffsetOne : groupOffset ring leader 1 = first := by
    simpa [first] using hfirstOffset.symm
  have hoffTwo : ∀ k, 1 < k → k < n →
      D (groupOffset ring leader k) =
        C1 (groupOffset ring leader k) := by
    intro k hkOne hkBound
    apply runLocalSchedule_two_same_off_edge
    · have hk0 : groupOffset ring leader k ≠
          groupOffset ring leader 0 := by
        apply groupOffset_ne_of_lt ring leader hkBound (by omega)
        omega
      simpa [groupOffset_zero_eq] using hk0
    · change groupOffset ring leader k ≠
        groupOffset ring leader 1
      apply groupOffset_ne_of_lt ring leader hkBound (by omega)
      omega
  have hpair : ExpiringResetFollowerNormalizedOutput hpsi
      (current e, current j) (C1 e, C1 j) := by
    simpa [hneighbor] using hstep.normalized
  let t : Fin (n - 1) := ⟨steps, hlt⟩
  have hstepsOne : 1 < steps + 1 :=
    Nat.succ_lt_succ hstate.steps_pos
  have hblockerAfterFirst :
      D (groupOffset ring leader (steps + 1)) =
        C1 (groupOffset ring leader (steps + 1)) :=
    hoffTwo (steps + 1) hstepsOne hjBound
  have heffect : FirstBlockerEffect ring leader current D t := {
    blocker_present := by
      simpa [t, j] using hrightEcho
    blocker_cleared := by
      rw [hblockerAfterFirst]
      simpa [t, j] using hpair.control.right_echo_false
    higher_unchanged := by
      intro s hs
      have hsBound : s.val + 1 < n := by omega
      have hse : groupOffset ring leader (s.val + 1) ≠ e := by
        apply groupOffset_ne_of_lt ring leader hsBound heBound
        dsimp only [t] at hs
        omega
      have hsj : groupOffset ring leader (s.val + 1) ≠ j := by
        apply groupOffset_ne_of_lt ring leader hsBound hjBound
        dsimp only [t] at hs
        omega
      rw [hoffTwo (s.val + 1) (by
        dsimp only [t] at hs
        omega) hsBound]
      exact congrArg
        (fun u : ExpiringAgentState psi kappa tau =>
          u.core.erase.core.echo)
        (hstep.off_edge (groupOffset ring leader (s.val + 1))
          hse (by rwa [hneighbor])) }
  simpa [e, T, C1, D, runLocalSchedule] using
    And.intro heffect (And.intro hready
      (And.intro
        (hlabel.trans (congrArg
          (fun u : ExpiringAgentState psi kappa tau =>
            u.core.erase.core.label) hleaderOff))
        (And.intro htotalCount hmobile)))

set_option maxHeartbeats 3000000 in
/-- Birth-signal-transition form of the non-live echo collision B,A,A word. -/
theorem ResetAwareNormalizedPrefixState.collision_then_birthSignalZero_liveRetryReady
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (leader : Fin n) (base current : EConfig n psi kappa tau)
    (steps : Nat)
    (hstate : ResetAwareNormalizedPrefixState
      hpsi ring leader base current steps)
    (hlt : steps < n - 1)
    (hvisited : VisitedPrefixLiveFree ring leader current steps)
    (hrightEcho :
      (current (groupOffset ring leader (steps + 1))).core.erase.core.echo =
        true)
    (hrightNotLive :
      (current (groupOffset ring leader (steps + 1))).core.erase.core.bullet ≠
        ⟨2, by omega⟩)
    (hrootSignalZero :
      (current leader).core.erase.core.signal_B = ⟨0, by omega⟩) :
    let e := groupOffset ring leader steps
    let T := wallSweepBirthSignalZeroPathStallTransition
      hpsi kappa tau
    let D := runLocalSchedule ring T current [e, leader, leader]
    FirstBlockerEffect ring leader current D ⟨steps, hlt⟩ ∧
      ResetAwareLiveRetryReady hpsi ring leader D ∧
      (D leader).core.erase.core.label =
        (current leader).core.erase.core.label ∧
      PPLLPpsiLeaderCreationRepair.bulletTwoCount D ≤
        PPLLPpsiLeaderCreationRepair.bulletTwoCount current ∧
      clockwiseMobileLiveRank ring leader D =
        clockwiseMobileLiveRank ring leader current := by
  let e := groupOffset ring leader steps
  let Told :=
    wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
      hpsi kappa tau
  let Tnew := wallSweepBirthSignalZeroPathStallTransition
    hpsi kappa tau
  let C1old := localStep ring Told current e
  let Dold := runLocalSchedule ring Told current [e, leader, leader]
  let Dnew := runLocalSchedule ring Tnew current [e, leader, leader]
  have hvisitedC1 := hstate.visitedLiveFree_step
    hpsi ring hn leader base current steps hlt hvisited hrightNotLive
  change VisitedPrefixLiveFree ring leader C1old (steps + 1) at hvisitedC1
  have hfirstNotLive :
      (C1old (ring.rightNeighbor leader)).core.erase.core.bullet ≠
        ⟨2, by omega⟩ := by
    have hoffsetOne : groupOffset ring leader 1 =
        ring.rightNeighbor leader := by
      have hnext := rightNeighbor_groupOffset ring leader 0
      rw [groupOffset_zero_eq] at hnext
      simpa using hnext.symm
    rw [← hoffsetOne]
    exact hvisitedC1 1 (by omega) (by omega)
  have hsafe :
      (C1old (ring.rightNeighbor leader)).core.erase.core.bullet =
          ⟨2, by omega⟩ →
        (C1old leader).core.erase.core.shield = true := by
    intro hlive
    exact (hfirstNotLive hlive).elim
  have hD : Dnew = Dold := by
    simpa only [Dnew, Dold, Tnew, Told, e, C1old] using
      hstate.run_birthSignalZero_follower_then_two_leader_eq_of_safe
        hpsi ring hn leader base current steps hlt hsafe
  have hold := hstate.collision_then_liveRetryReady
    hpsi ring hn leader base current steps hlt hvisited hrightEcho
      hrightNotLive hrootSignalZero
  change FirstBlockerEffect ring leader current Dold ⟨steps, hlt⟩ ∧
      ResetAwareLiveRetryReady hpsi ring leader Dold ∧
      (Dold leader).core.erase.core.label =
        (current leader).core.erase.core.label ∧
      PPLLPpsiLeaderCreationRepair.bulletTwoCount Dold ≤
        PPLLPpsiLeaderCreationRepair.bulletTwoCount current ∧
      clockwiseMobileLiveRank ring leader Dold =
        clockwiseMobileLiveRank ring leader current at hold
  change FirstBlockerEffect ring leader current Dnew ⟨steps, hlt⟩ ∧
      ResetAwareLiveRetryReady hpsi ring leader Dnew ∧
      (Dnew leader).core.erase.core.label =
        (current leader).core.erase.core.label ∧
      PPLLPpsiLeaderCreationRepair.bulletTwoCount Dnew ≤
        PPLLPpsiLeaderCreationRepair.bulletTwoCount current ∧
      clockwiseMobileLiveRank ring leader Dnew =
        clockwiseMobileLiveRank ring leader current
  rw [hD]
  exact hold

set_option maxHeartbeats 4000000 in
/-- Advance to the nearest mobile live responder through an event-free
prefix.  At offset two the actual leader interaction either protects the
zero root or deletes it with a strict live-count drop.  Farther away, the
three-edge replay returns to the same zero-labelled retry boundary at a
strictly smaller combined live/echo rank. -/
theorem resetAwareLiveRetry_live_event_round
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (leader : Fin n) (C : EConfig n psi kappa tau)
    (hready : ResetAwareLiveRetryReady hpsi ring leader C)
    (hrootZero : (C leader).core.erase.core.label = ⟨0, hpsi⟩)
    (t : Fin (n - 2))
    (hpresent :
      (C (groupOffset ring leader (t.val + 2))).core.erase.core.bullet =
        ⟨2, by omega⟩)
    (hlower : ∀ i : Fin (n - 2), i.val < t.val →
      (C (groupOffset ring leader (i.val + 2))).core.erase.core.bullet ≠
        ⟨2, by omega⟩)
    (hbaseEcho : ∀ k, 1 < k → k ≤ t.val + 1 →
      (C (groupOffset ring leader k)).core.erase.core.echo = false) :
    ∃ (word : DetSchedule n) (D : EConfig n psi kappa tau),
      D = runLocalSchedule ring
        (wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
          hpsi kappa tau) C word ∧
      (PPLLWallSweepRestartableProtected.ProtectedLeaderAt
          hpsi D leader ∨
        (RawLeaderless
            (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig D) ∧
          PPLLPpsiLeaderCreationRepair.bulletTwoCount D <
            PPLLPpsiLeaderCreationRepair.bulletTwoCount C) ∨
        (ResetAwareLiveRetryReady hpsi ring leader D ∧
          (D leader).core.erase.core.label = ⟨0, hpsi⟩ ∧
          clockwiseLiveEchoRetryRank ring leader D <
            clockwiseLiveEchoRetryRank ring leader C ∧
          PPLLPpsiLeaderCreationRepair.bulletTwoCount D ≤
            PPLLPpsiLeaderCreationRepair.bulletTwoCount C)) := by
  obtain ⟨hfrontier, hfirstNotLive, hsignal⟩ := hready
  have hstateOne := resetAwareNormalizedPrefixState_one_of_frontierAt
    hpsi ring hn leader C hfrontier
  have hoffsetOne : groupOffset ring leader 1 =
      ring.rightNeighbor leader := by
    have hnext := rightNeighbor_groupOffset ring leader 0
    rw [groupOffset_zero_eq] at hnext
    simpa using hnext.symm
  have hvisitedOne : VisitedPrefixLiveFree ring leader C 1 := by
    intro k hk hkle
    have hkOne : k = 1 := by omega
    subst k
    rw [hoffsetOne]
    exact hfirstNotLive
  have hbaseNotLive : ∀ k, 1 < k → k ≤ t.val + 1 →
      (C (groupOffset ring leader k)).core.erase.core.bullet ≠
        ⟨2, by omega⟩ := by
    intro k hk hkt
    let i : Fin (n - 2) := ⟨k - 2, by omega⟩
    have hi := hlower i (by
      dsimp only [i]
      omega)
    have hindex : i.val + 2 = k := by
      dsimp only [i]
      omega
    simpa [hindex] using hi
  obtain ⟨pref, M, hM, _hprefLength, hstateM, hvisitedM,
      hrootM, hcountM⟩ :=
    hstateOne.exists_advance_to_of_base_event_free
      hpsi ring hn leader C C 1 (t.val + 1) hvisitedOne
        (by omega) (by omega) hbaseEcho hbaseNotLive
  have hrightLiveM :
      (M (groupOffset ring leader (t.val + 2))).core.erase.core.bullet =
        ⟨2, by omega⟩ := by
    rw [hstateM.untouched_ahead (t.val + 2) (by omega) (by omega)]
    exact hpresent
  have hfirstNotLiveM :
      (M (ring.rightNeighbor leader)).core.erase.core.bullet ≠
        ⟨2, by omega⟩ := by
    rw [← hoffsetOne]
    exact hvisitedM 1 (by omega) (by omega)
  have hsignalM :
      (M leader).core.erase.core.signal_B = ⟨0, by omega⟩ := by
    rw [hrootM]
    exact hsignal
  have hmobileM :=
    hstateM.mobileLiveRank_eq_base_of_visited_free
      ring leader C M (t.val + 1) hvisitedM hbaseNotLive
  let T := wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
    hpsi kappa tau
  by_cases htZero : t.val = 0
  · have hstateAtOne : ResetAwareNormalizedPrefixState
        hpsi ring leader C M 1 := by
      simpa [htZero] using hstateM
    have hrightAtTwo :
        (M (groupOffset ring leader 2)).core.erase.core.bullet =
          ⟨2, by omega⟩ := by
      simpa [htZero] using hrightLiveM
    let e := groupOffset ring leader 1
    let suffix : DetSchedule n := [e, leader]
    let D := runLocalSchedule ring T M suffix
    have hattempt := hstateAtOne.first_live_then_leader_attempt
      hpsi ring hn leader C M (by omega) hsignalM hrightAtTwo
    change
      (localStep ring T M e e).core.erase.core.bullet = ⟨2, by omega⟩ ∧
      (localStep ring T M e (groupOffset ring leader 2)).core.erase.core.bullet =
        ⟨0, by omega⟩ ∧
      NoActiveDeletion D ∧
      (D leader).core.erase.core.label =
        (M leader).core.erase.core.label ∧
      (D leader).core.erase.core.signal_B = ⟨0, by omega⟩ ∧
      ((hasUniqueLeader n
          (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig D) ∧
          (D leader).core.erase.core.leader = true ∧
          (D leader).core.erase.core.shield = true ∧
          (D (ring.rightNeighbor leader)).core.erase.core.bullet =
            ⟨2, by omega⟩ ∧
          PPLLPpsiLeaderCreationRepair.bulletTwoCount D ≤
            PPLLPpsiLeaderCreationRepair.bulletTwoCount M) ∨
        (RawLeaderless
            (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig D) ∧
          PPLLPpsiLeaderCreationRepair.bulletTwoCount D <
            PPLLPpsiLeaderCreationRepair.bulletTwoCount M)) at hattempt
    rcases hattempt with
      ⟨_hleftLive, _hrightZero, _hnoActive, hlabel, _hsignalD,
        hsurvives | hleaderless⟩
    · let word := pref ++ suffix
      refine ⟨word, D, ?_, Or.inl ?_⟩
      · calc
          D = runLocalSchedule ring T M suffix := rfl
          _ = runLocalSchedule ring T
              (runLocalSchedule ring T C pref) suffix := by rw [← hM]
          _ = runLocalSchedule ring T C (pref ++ suffix) :=
            (runLocalSchedule_append_generic ring T C pref suffix).symm
          _ = runLocalSchedule ring T C word := by rfl
      · exact ⟨⟨hsurvives.2.1, hsurvives.2.2.1⟩,
          hlabel.trans (congrArg
            (fun u : ExpiringAgentState psi kappa tau =>
              u.core.erase.core.label) hrootM) |>.trans hrootZero⟩
    · let word := pref ++ suffix
      refine ⟨word, D, ?_, Or.inr (Or.inl ⟨hleaderless.1, ?_⟩)⟩
      · calc
          D = runLocalSchedule ring T M suffix := rfl
          _ = runLocalSchedule ring T
              (runLocalSchedule ring T C pref) suffix := by rw [← hM]
          _ = runLocalSchedule ring T C (pref ++ suffix) :=
            (runLocalSchedule_append_generic ring T C pref suffix).symm
          _ = runLocalSchedule ring T C word := by rfl
      · exact Nat.lt_of_lt_of_le hleaderless.2 hcountM
  · have htPos : 0 < t.val := by omega
    let e := groupOffset ring leader (t.val + 1)
    let suffix : DetSchedule n := [e, leader, leader]
    let D := runLocalSchedule ring T M suffix
    have hretry := hstateM.far_live_then_two_step_reseed
      hpsi ring hn leader C M (t.val + 1) (by omega) (by omega)
        hfirstNotLiveM hsignalM hrightLiveM
    change ResetAwareLiveRetryReady hpsi ring leader D ∧
      (D leader).core.erase.core.label =
        (M leader).core.erase.core.label ∧
      PPLLPpsiLeaderCreationRepair.bulletTwoCount D ≤
        PPLLPpsiLeaderCreationRepair.bulletTwoCount M ∧
      clockwiseMobileLiveRank ring leader D <
        clockwiseMobileLiveRank ring leader M at hretry
    have hliveDC : clockwiseMobileLiveRank ring leader D <
        clockwiseMobileLiveRank ring leader C := by
      rw [← hmobileM]
      exact hretry.2.2.2
    have hcombined := clockwiseLiveEchoRetryRank_lt_of_live_lt
      ring leader C D hliveDC
    let word := pref ++ suffix
    refine ⟨word, D, ?_, Or.inr (Or.inr
      ⟨hretry.1, ?_, hcombined,
        Nat.le_trans hretry.2.2.1 hcountM⟩)⟩
    · calc
        D = runLocalSchedule ring T M suffix := rfl
        _ = runLocalSchedule ring T
            (runLocalSchedule ring T C pref) suffix := by rw [← hM]
        _ = runLocalSchedule ring T C (pref ++ suffix) :=
          (runLocalSchedule_append_generic ring T C pref suffix).symm
        _ = runLocalSchedule ring T C word := by rfl
    · exact hretry.2.1.trans (congrArg
        (fun u : ExpiringAgentState psi kappa tau =>
          u.core.erase.core.label) hrootM) |>.trans hrootZero

set_option maxHeartbeats 4000000 in
/-- Birth-signal-transition form of the nearest-live event round. -/
theorem resetAwareLiveRetry_birthSignalZero_live_event_round
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (leader : Fin n) (C : EConfig n psi kappa tau)
    (hready : ResetAwareLiveRetryReady hpsi ring leader C)
    (hrootZero : (C leader).core.erase.core.label = ⟨0, hpsi⟩)
    (t : Fin (n - 2))
    (hpresent :
      (C (groupOffset ring leader (t.val + 2))).core.erase.core.bullet =
        ⟨2, by omega⟩)
    (hlower : ∀ i : Fin (n - 2), i.val < t.val →
      (C (groupOffset ring leader (i.val + 2))).core.erase.core.bullet ≠
        ⟨2, by omega⟩)
    (hbaseEcho : ∀ k, 1 < k → k ≤ t.val + 1 →
      (C (groupOffset ring leader k)).core.erase.core.echo = false) :
    ∃ (word : DetSchedule n) (D : EConfig n psi kappa tau),
      D = runLocalSchedule ring
        (wallSweepBirthSignalZeroPathStallTransition
          hpsi kappa tau) C word ∧
      (PPLLWallSweepRestartableProtected.ProtectedLeaderAt
          hpsi D leader ∨
        (NoActiveDeletion D ∧
          RawLeaderless
            (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig D) ∧
          PPLLPpsiLeaderCreationRepair.bulletTwoCount D <
            PPLLPpsiLeaderCreationRepair.bulletTwoCount C) ∨
        (ResetAwareLiveRetryReady hpsi ring leader D ∧
          (D leader).core.erase.core.label = ⟨0, hpsi⟩ ∧
          clockwiseLiveEchoRetryRank ring leader D <
            clockwiseLiveEchoRetryRank ring leader C ∧
          PPLLPpsiLeaderCreationRepair.bulletTwoCount D ≤
            PPLLPpsiLeaderCreationRepair.bulletTwoCount C)) := by
  obtain ⟨hfrontier, hfirstNotLive, hsignal⟩ := hready
  have hstateOne := resetAwareNormalizedPrefixState_one_of_frontierAt
    hpsi ring hn leader C hfrontier
  have hoffsetOne : groupOffset ring leader 1 =
      ring.rightNeighbor leader := by
    have hnext := rightNeighbor_groupOffset ring leader 0
    rw [groupOffset_zero_eq] at hnext
    simpa using hnext.symm
  have hvisitedOne : VisitedPrefixLiveFree ring leader C 1 := by
    intro k hk hkle
    have hkOne : k = 1 := by omega
    subst k
    rw [hoffsetOne]
    exact hfirstNotLive
  have hbaseNotLive : ∀ k, 1 < k → k ≤ t.val + 1 →
      (C (groupOffset ring leader k)).core.erase.core.bullet ≠
        ⟨2, by omega⟩ := by
    intro k hk hkt
    let i : Fin (n - 2) := ⟨k - 2, by omega⟩
    have hi := hlower i (by
      dsimp only [i]
      omega)
    have hindex : i.val + 2 = k := by
      dsimp only [i]
      omega
    simpa [hindex] using hi
  obtain ⟨pref, M, hM, _hprefLength, hstateM, hvisitedM,
      hrootM, hcountM⟩ :=
    hstateOne.exists_birthSignalZero_advance_to_of_base_event_free
      hpsi ring hn leader C C 1 (t.val + 1) hvisitedOne
        (by omega) (by omega) hbaseEcho hbaseNotLive
  have hrightLiveM :
      (M (groupOffset ring leader (t.val + 2))).core.erase.core.bullet =
        ⟨2, by omega⟩ := by
    rw [hstateM.untouched_ahead (t.val + 2) (by omega) (by omega)]
    exact hpresent
  have hfirstNotLiveM :
      (M (ring.rightNeighbor leader)).core.erase.core.bullet ≠
        ⟨2, by omega⟩ := by
    rw [← hoffsetOne]
    exact hvisitedM 1 (by omega) (by omega)
  have hsignalM :
      (M leader).core.erase.core.signal_B = ⟨0, by omega⟩ := by
    rw [hrootM]
    exact hsignal
  have hmobileM :=
    hstateM.mobileLiveRank_eq_base_of_visited_free
      ring leader C M (t.val + 1) hvisitedM hbaseNotLive
  let T := wallSweepBirthSignalZeroPathStallTransition
    hpsi kappa tau
  by_cases htZero : t.val = 0
  · have hstateAtOne : ResetAwareNormalizedPrefixState
        hpsi ring leader C M 1 := by
      simpa [htZero] using hstateM
    have hrightAtTwo :
        (M (groupOffset ring leader 2)).core.erase.core.bullet =
          ⟨2, by omega⟩ := by
      simpa [htZero] using hrightLiveM
    let e := groupOffset ring leader 1
    let suffix : DetSchedule n := [e, leader]
    let D := runLocalSchedule ring T M suffix
    have hattempt := hstateAtOne.first_live_then_birthSignalZero_leader_attempt
      hpsi ring hn leader C M (by omega) hsignalM hrightAtTwo
    change
      (localStep ring T M e e).core.erase.core.bullet = ⟨2, by omega⟩ ∧
      (localStep ring T M e (groupOffset ring leader 2)).core.erase.core.bullet =
        ⟨0, by omega⟩ ∧
      NoActiveDeletion D ∧
      (D leader).core.erase.core.label =
        (M leader).core.erase.core.label ∧
      (D leader).core.erase.core.signal_B = ⟨0, by omega⟩ ∧
      ((hasUniqueLeader n
          (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig D) ∧
          (D leader).core.erase.core.leader = true ∧
          (D leader).core.erase.core.shield = true ∧
          (D (ring.rightNeighbor leader)).core.erase.core.bullet =
            ⟨2, by omega⟩ ∧
          PPLLPpsiLeaderCreationRepair.bulletTwoCount D ≤
            PPLLPpsiLeaderCreationRepair.bulletTwoCount M) ∨
        (RawLeaderless
            (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig D) ∧
          PPLLPpsiLeaderCreationRepair.bulletTwoCount D <
            PPLLPpsiLeaderCreationRepair.bulletTwoCount M)) at hattempt
    rcases hattempt with
      ⟨_hleftLive, _hrightZero, hnoActiveD, hlabel, _hsignalD,
        hsurvives | hleaderless⟩
    · let word := pref ++ suffix
      refine ⟨word, D, ?_, Or.inl ?_⟩
      · calc
          D = runLocalSchedule ring T M suffix := rfl
          _ = runLocalSchedule ring T
              (runLocalSchedule ring T C pref) suffix := by rw [← hM]
          _ = runLocalSchedule ring T C (pref ++ suffix) :=
            (runLocalSchedule_append_generic ring T C pref suffix).symm
          _ = runLocalSchedule ring T C word := by rfl
      · exact ⟨⟨hsurvives.2.1, hsurvives.2.2.1⟩,
          hlabel.trans (congrArg
            (fun u : ExpiringAgentState psi kappa tau =>
              u.core.erase.core.label) hrootM) |>.trans hrootZero⟩
    · let word := pref ++ suffix
      refine ⟨word, D, ?_, Or.inr (Or.inl
        ⟨hnoActiveD, hleaderless.1, ?_⟩)⟩
      · calc
          D = runLocalSchedule ring T M suffix := rfl
          _ = runLocalSchedule ring T
              (runLocalSchedule ring T C pref) suffix := by rw [← hM]
          _ = runLocalSchedule ring T C (pref ++ suffix) :=
            (runLocalSchedule_append_generic ring T C pref suffix).symm
          _ = runLocalSchedule ring T C word := by rfl
      · exact Nat.lt_of_lt_of_le hleaderless.2 hcountM
  · have htPos : 0 < t.val := by omega
    let e := groupOffset ring leader (t.val + 1)
    let suffix : DetSchedule n := [e, leader, leader]
    let D := runLocalSchedule ring T M suffix
    have hretry := hstateM.far_live_then_birthSignalZero_two_step_reseed
      hpsi ring hn leader C M (t.val + 1) (by omega) (by omega)
        hfirstNotLiveM hsignalM hrightLiveM
    change ResetAwareLiveRetryReady hpsi ring leader D ∧
      (D leader).core.erase.core.label =
        (M leader).core.erase.core.label ∧
      PPLLPpsiLeaderCreationRepair.bulletTwoCount D ≤
        PPLLPpsiLeaderCreationRepair.bulletTwoCount M ∧
      clockwiseMobileLiveRank ring leader D <
        clockwiseMobileLiveRank ring leader M at hretry
    have hliveDC : clockwiseMobileLiveRank ring leader D <
        clockwiseMobileLiveRank ring leader C := by
      rw [← hmobileM]
      exact hretry.2.2.2
    have hcombined := clockwiseLiveEchoRetryRank_lt_of_live_lt
      ring leader C D hliveDC
    let word := pref ++ suffix
    refine ⟨word, D, ?_, Or.inr (Or.inr
      ⟨hretry.1, ?_, hcombined,
        Nat.le_trans hretry.2.2.1 hcountM⟩)⟩
    · calc
        D = runLocalSchedule ring T M suffix := rfl
        _ = runLocalSchedule ring T
            (runLocalSchedule ring T C pref) suffix := by rw [← hM]
        _ = runLocalSchedule ring T C (pref ++ suffix) :=
          (runLocalSchedule_append_generic ring T C pref suffix).symm
        _ = runLocalSchedule ring T C word := by rfl
    · exact hretry.2.1.trans (congrArg
        (fun u : ExpiringAgentState psi kappa tau =>
          u.core.erase.core.label) hrootM) |>.trans hrootZero
set_option maxHeartbeats 4000000 in
/-- If the nearest echo lies strictly before the nearest mobile live bullet,
advance to it through a live-free prefix, consume it, and replay the root
edge.  The mobile-live rank is fixed while the echo digit drops strictly. -/
theorem resetAwareLiveRetry_echo_event_round
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (leader : Fin n) (C : EConfig n psi kappa tau)
    (hready : ResetAwareLiveRetryReady hpsi ring leader C)
    (hrootZero : (C leader).core.erase.core.label = ⟨0, hpsi⟩)
    (t : Fin (n - 1))
    (hpresent :
      (C (groupOffset ring leader (t.val + 1))).core.erase.core.echo = true)
    (hlower : ∀ i : Fin (n - 1), i.val < t.val →
      (C (groupOffset ring leader (i.val + 1))).core.erase.core.echo = false)
    (hbaseNotLive : ∀ k, 1 < k → k ≤ t.val + 1 →
      (C (groupOffset ring leader k)).core.erase.core.bullet ≠
        ⟨2, by omega⟩) :
    ∃ (word : DetSchedule n) (D : EConfig n psi kappa tau),
      D = runLocalSchedule ring
        (wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
          hpsi kappa tau) C word ∧
      ResetAwareLiveRetryReady hpsi ring leader D ∧
      (D leader).core.erase.core.label = ⟨0, hpsi⟩ ∧
      clockwiseLiveEchoRetryRank ring leader D <
        clockwiseLiveEchoRetryRank ring leader C ∧
      PPLLPpsiLeaderCreationRepair.bulletTwoCount D ≤
        PPLLPpsiLeaderCreationRepair.bulletTwoCount C := by
  obtain ⟨hfrontier, hfirstNotLive, hsignal⟩ := hready
  have hstateOne := resetAwareNormalizedPrefixState_one_of_frontierAt
    hpsi ring hn leader C hfrontier
  obtain ⟨_noActive, _hunique, _hleader, _hrightFollower,
      _hrightLabel, _hleftProbe, _hrightProbe,
      _hleftNeutral, _hrightNeutral, _hleftReset, _hrightReset,
      _hleftEcho, hrightEchoFalse, _hsafe⟩ := hfrontier
  have hoffsetOne : groupOffset ring leader 1 =
      ring.rightNeighbor leader := by
    have hnext := rightNeighbor_groupOffset ring leader 0
    rw [groupOffset_zero_eq] at hnext
    simpa using hnext.symm
  have htPos : 0 < t.val := by
    by_cases htZero : t.val = 0
    · have hpresentFirst :
          (C (groupOffset ring leader 1)).core.erase.core.echo = true := by
        simpa [htZero] using hpresent
      have hfalseFirst :
          (C (groupOffset ring leader 1)).core.erase.core.echo = false := by
        rw [hoffsetOne]
        exact hrightEchoFalse
      rw [hfalseFirst] at hpresentFirst
      contradiction
    · omega
  have hvisitedOne : VisitedPrefixLiveFree ring leader C 1 := by
    intro k hk hkle
    have hkOne : k = 1 := by omega
    subst k
    rw [hoffsetOne]
    exact hfirstNotLive
  have hbaseEcho : ∀ k, 1 < k → k ≤ t.val →
      (C (groupOffset ring leader k)).core.erase.core.echo = false := by
    intro k hk hkt
    let i : Fin (n - 1) := ⟨k - 1, by omega⟩
    have hi := hlower i (by
      dsimp only [i]
      omega)
    have hindex : i.val + 1 = k := by
      dsimp only [i]
      omega
    simpa [hindex] using hi
  have hbaseNotLivePrefix : ∀ k, 1 < k → k ≤ t.val →
      (C (groupOffset ring leader k)).core.erase.core.bullet ≠
        ⟨2, by omega⟩ := by
    intro k hk hkt
    exact hbaseNotLive k hk (by omega)
  obtain ⟨pref, M, hM, _hprefLength, hstateM, hvisitedM,
      hrootM, hcountM⟩ :=
    hstateOne.exists_advance_to_of_base_event_free
      hpsi ring hn leader C C 1 t.val hvisitedOne
        (by omega) (by omega) hbaseEcho hbaseNotLivePrefix
  have hblockerM :
      (M (groupOffset ring leader (t.val + 1))).core.erase.core.echo =
        true := by
    rw [hstateM.untouched_ahead (t.val + 1) (by omega) (by omega)]
    exact hpresent
  have hrightNotLiveM :
      (M (groupOffset ring leader (t.val + 1))).core.erase.core.bullet ≠
        ⟨2, by omega⟩ := by
    rw [hstateM.untouched_ahead (t.val + 1) (by omega) (by omega)]
    exact hbaseNotLive (t.val + 1) (by omega) (by omega)
  have hsignalM :
      (M leader).core.erase.core.signal_B = ⟨0, by omega⟩ := by
    rw [hrootM]
    exact hsignal
  have hmobileM :=
    hstateM.mobileLiveRank_eq_base_of_visited_free
      ring leader C M t.val hvisitedM hbaseNotLivePrefix
  let T := wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
    hpsi kappa tau
  let suffix : DetSchedule n :=
    [groupOffset ring leader t.val, leader, leader]
  let D := runLocalSchedule ring T M suffix
  have hcollision : FirstBlockerEffect ring leader M D t ∧
      ResetAwareLiveRetryReady hpsi ring leader D ∧
      (D leader).core.erase.core.label =
        (M leader).core.erase.core.label ∧
      PPLLPpsiLeaderCreationRepair.bulletTwoCount D ≤
        PPLLPpsiLeaderCreationRepair.bulletTwoCount M ∧
      clockwiseMobileLiveRank ring leader D =
        clockwiseMobileLiveRank ring leader M := by
    simpa [T, suffix, D] using
      hstateM.collision_then_liveRetryReady
        hpsi ring hn leader C M t.val t.isLt hvisitedM
          hblockerM hrightNotLiveM hsignalM
  have heffect : FirstBlockerEffect ring leader C D t := {
    blocker_present := hpresent
    blocker_cleared := hcollision.1.blocker_cleared
    higher_unchanged := by
      intro s hts
      rw [hcollision.1.higher_unchanged s hts]
      have hsite := hstateM.untouched_ahead (s.val + 1)
        (by omega) (by omega)
      exact congrArg
        (fun u : ExpiringAgentState psi kappa tau =>
          u.core.erase.core.echo) hsite }
  have hmobileDC : clockwiseMobileLiveRank ring leader D =
      clockwiseMobileLiveRank ring leader C :=
    hcollision.2.2.2.2.trans hmobileM
  have hcombined := clockwiseLiveEchoRetryRank_lt_of_live_le_echo_lt
    ring leader C D (by omega) heffect.rank_lt
  let word := pref ++ suffix
  refine ⟨word, D, ?_, hcollision.2.1, ?_, hcombined,
    Nat.le_trans hcollision.2.2.2.1 hcountM⟩
  · calc
      D = runLocalSchedule ring T M suffix := rfl
      _ = runLocalSchedule ring T
          (runLocalSchedule ring T C pref) suffix := by rw [← hM]
      _ = runLocalSchedule ring T C (pref ++ suffix) :=
        (runLocalSchedule_append_generic ring T C pref suffix).symm
      _ = runLocalSchedule ring T C word := by rfl
  · exact hcollision.2.2.1.trans (congrArg
      (fun u : ExpiringAgentState psi kappa tau =>
        u.core.erase.core.label) hrootM) |>.trans hrootZero

set_option maxHeartbeats 4000000 in
/-- Birth-signal-transition form of the nearest-echo event round. -/
theorem resetAwareLiveRetry_birthSignalZero_echo_event_round
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (leader : Fin n) (C : EConfig n psi kappa tau)
    (hready : ResetAwareLiveRetryReady hpsi ring leader C)
    (hrootZero : (C leader).core.erase.core.label = ⟨0, hpsi⟩)
    (t : Fin (n - 1))
    (hpresent :
      (C (groupOffset ring leader (t.val + 1))).core.erase.core.echo = true)
    (hlower : ∀ i : Fin (n - 1), i.val < t.val →
      (C (groupOffset ring leader (i.val + 1))).core.erase.core.echo = false)
    (hbaseNotLive : ∀ k, 1 < k → k ≤ t.val + 1 →
      (C (groupOffset ring leader k)).core.erase.core.bullet ≠
        ⟨2, by omega⟩) :
    ∃ (word : DetSchedule n) (D : EConfig n psi kappa tau),
      D = runLocalSchedule ring
        (wallSweepBirthSignalZeroPathStallTransition
          hpsi kappa tau) C word ∧
      ResetAwareLiveRetryReady hpsi ring leader D ∧
      (D leader).core.erase.core.label = ⟨0, hpsi⟩ ∧
      clockwiseLiveEchoRetryRank ring leader D <
        clockwiseLiveEchoRetryRank ring leader C ∧
      PPLLPpsiLeaderCreationRepair.bulletTwoCount D ≤
        PPLLPpsiLeaderCreationRepair.bulletTwoCount C := by
  obtain ⟨hfrontier, hfirstNotLive, hsignal⟩ := hready
  have hstateOne := resetAwareNormalizedPrefixState_one_of_frontierAt
    hpsi ring hn leader C hfrontier
  obtain ⟨_noActive, _hunique, _hleader, _hrightFollower,
      _hrightLabel, _hleftProbe, _hrightProbe,
      _hleftNeutral, _hrightNeutral, _hleftReset, _hrightReset,
      _hleftEcho, hrightEchoFalse, _hsafe⟩ := hfrontier
  have hoffsetOne : groupOffset ring leader 1 =
      ring.rightNeighbor leader := by
    have hnext := rightNeighbor_groupOffset ring leader 0
    rw [groupOffset_zero_eq] at hnext
    simpa using hnext.symm
  have htPos : 0 < t.val := by
    by_cases htZero : t.val = 0
    · have hpresentFirst :
          (C (groupOffset ring leader 1)).core.erase.core.echo = true := by
        simpa [htZero] using hpresent
      have hfalseFirst :
          (C (groupOffset ring leader 1)).core.erase.core.echo = false := by
        rw [hoffsetOne]
        exact hrightEchoFalse
      rw [hfalseFirst] at hpresentFirst
      contradiction
    · omega
  have hvisitedOne : VisitedPrefixLiveFree ring leader C 1 := by
    intro k hk hkle
    have hkOne : k = 1 := by omega
    subst k
    rw [hoffsetOne]
    exact hfirstNotLive
  have hbaseEcho : ∀ k, 1 < k → k ≤ t.val →
      (C (groupOffset ring leader k)).core.erase.core.echo = false := by
    intro k hk hkt
    let i : Fin (n - 1) := ⟨k - 1, by omega⟩
    have hi := hlower i (by
      dsimp only [i]
      omega)
    have hindex : i.val + 1 = k := by
      dsimp only [i]
      omega
    simpa [hindex] using hi
  have hbaseNotLivePrefix : ∀ k, 1 < k → k ≤ t.val →
      (C (groupOffset ring leader k)).core.erase.core.bullet ≠
        ⟨2, by omega⟩ := by
    intro k hk hkt
    exact hbaseNotLive k hk (by omega)
  obtain ⟨pref, M, hM, _hprefLength, hstateM, hvisitedM,
      hrootM, hcountM⟩ :=
    hstateOne.exists_birthSignalZero_advance_to_of_base_event_free
      hpsi ring hn leader C C 1 t.val hvisitedOne
        (by omega) (by omega) hbaseEcho hbaseNotLivePrefix
  have hblockerM :
      (M (groupOffset ring leader (t.val + 1))).core.erase.core.echo =
        true := by
    rw [hstateM.untouched_ahead (t.val + 1) (by omega) (by omega)]
    exact hpresent
  have hrightNotLiveM :
      (M (groupOffset ring leader (t.val + 1))).core.erase.core.bullet ≠
        ⟨2, by omega⟩ := by
    rw [hstateM.untouched_ahead (t.val + 1) (by omega) (by omega)]
    exact hbaseNotLive (t.val + 1) (by omega) (by omega)
  have hsignalM :
      (M leader).core.erase.core.signal_B = ⟨0, by omega⟩ := by
    rw [hrootM]
    exact hsignal
  have hmobileM :=
    hstateM.mobileLiveRank_eq_base_of_visited_free
      ring leader C M t.val hvisitedM hbaseNotLivePrefix
  let T := wallSweepBirthSignalZeroPathStallTransition
    hpsi kappa tau
  let suffix : DetSchedule n :=
    [groupOffset ring leader t.val, leader, leader]
  let D := runLocalSchedule ring T M suffix
  have hcollision : FirstBlockerEffect ring leader M D t ∧
      ResetAwareLiveRetryReady hpsi ring leader D ∧
      (D leader).core.erase.core.label =
        (M leader).core.erase.core.label ∧
      PPLLPpsiLeaderCreationRepair.bulletTwoCount D ≤
        PPLLPpsiLeaderCreationRepair.bulletTwoCount M ∧
      clockwiseMobileLiveRank ring leader D =
        clockwiseMobileLiveRank ring leader M := by
    simpa [T, suffix, D] using
      hstateM.collision_then_birthSignalZero_liveRetryReady
        hpsi ring hn leader C M t.val t.isLt hvisitedM
          hblockerM hrightNotLiveM hsignalM
  have heffect : FirstBlockerEffect ring leader C D t := {
    blocker_present := hpresent
    blocker_cleared := hcollision.1.blocker_cleared
    higher_unchanged := by
      intro s hts
      rw [hcollision.1.higher_unchanged s hts]
      have hsite := hstateM.untouched_ahead (s.val + 1)
        (by omega) (by omega)
      exact congrArg
        (fun u : ExpiringAgentState psi kappa tau =>
          u.core.erase.core.echo) hsite }
  have hmobileDC : clockwiseMobileLiveRank ring leader D =
      clockwiseMobileLiveRank ring leader C :=
    hcollision.2.2.2.2.trans hmobileM
  have hcombined := clockwiseLiveEchoRetryRank_lt_of_live_le_echo_lt
    ring leader C D (by omega) heffect.rank_lt
  let word := pref ++ suffix
  refine ⟨word, D, ?_, hcollision.2.1, ?_, hcombined,
    Nat.le_trans hcollision.2.2.2.1 hcountM⟩
  · calc
      D = runLocalSchedule ring T M suffix := rfl
      _ = runLocalSchedule ring T
          (runLocalSchedule ring T C pref) suffix := by rw [← hM]
      _ = runLocalSchedule ring T C (pref ++ suffix) :=
        (runLocalSchedule_append_generic ring T C pref suffix).symm
      _ = runLocalSchedule ring T C word := by rfl
  · exact hcollision.2.2.1.trans (congrArg
      (fun u : ExpiringAgentState psi kappa tau =>
        u.core.erase.core.label) hrootM) |>.trans hrootZero

set_option maxHeartbeats 3000000 in
/-- A positive mobile-live rank has one concrete descending round.  The
nearest live and echo events are compared by physical offset; ties go to the
live branch because the echo collision contract requires a non-live
responder. -/
theorem resetAwareLiveRetry_positive_round
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (leader : Fin n) (C : EConfig n psi kappa tau)
    (hready : ResetAwareLiveRetryReady hpsi ring leader C)
    (hrootZero : (C leader).core.erase.core.label = ⟨0, hpsi⟩)
    (hliveRank : clockwiseMobileLiveRank ring leader C ≠ 0) :
    ∃ (word : DetSchedule n) (D : EConfig n psi kappa tau),
      D = runLocalSchedule ring
        (wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
          hpsi kappa tau) C word ∧
      (PPLLWallSweepRestartableProtected.ProtectedLeaderAt
          hpsi D leader ∨
        (RawLeaderless
            (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig D) ∧
          PPLLPpsiLeaderCreationRepair.bulletTwoCount D <
            PPLLPpsiLeaderCreationRepair.bulletTwoCount C) ∨
        (ResetAwareLiveRetryReady hpsi ring leader D ∧
          (D leader).core.erase.core.label = ⟨0, hpsi⟩ ∧
          clockwiseLiveEchoRetryRank ring leader D <
            clockwiseLiveEchoRetryRank ring leader C ∧
          PPLLPpsiLeaderCreationRepair.bulletTwoCount D ≤
            PPLLPpsiLeaderCreationRepair.bulletTwoCount C)) := by
  obtain ⟨live, _hliveCanonical, hlivePresent, hliveLower⟩ :=
    exists_firstClockwiseMobileLive_of_rank_ne_zero
      ring leader C hliveRank
  by_cases hechoZero : clockwiseEchoRank ring leader C = 0
  · have hbaseEcho : ∀ k, 1 < k → k ≤ live.val + 1 →
        (C (groupOffset ring leader k)).core.erase.core.echo = false := by
      intro k hk hklive
      exact follower_echo_false_of_clockwiseEchoRank_eq_zero
        ring leader C hechoZero k (by omega) (by omega)
    exact resetAwareLiveRetry_live_event_round
      hpsi ring hn leader C hready hrootZero live
        hlivePresent hliveLower hbaseEcho
  · obtain ⟨echo, _hechoCanonical, hechoPresent, hechoLower⟩ :=
      exists_firstClockwiseEcho_of_rank_ne_zero
        ring leader C hechoZero
    by_cases hliveFirst : live.val + 1 ≤ echo.val
    · have hbaseEcho : ∀ k, 1 < k → k ≤ live.val + 1 →
          (C (groupOffset ring leader k)).core.erase.core.echo = false := by
        intro k hk hklive
        let i : Fin (n - 1) := ⟨k - 1, by omega⟩
        have hi := hechoLower i (by
          dsimp only [i]
          omega)
        have hindex : i.val + 1 = k := by
          dsimp only [i]
          omega
        simpa [hindex] using hi
      exact resetAwareLiveRetry_live_event_round
        hpsi ring hn leader C hready hrootZero live
          hlivePresent hliveLower hbaseEcho
    · have hechoFirst : echo.val < live.val + 1 := by omega
      have hbaseNotLive : ∀ k, 1 < k → k ≤ echo.val + 1 →
          (C (groupOffset ring leader k)).core.erase.core.bullet ≠
            ⟨2, by omega⟩ := by
        intro k hk hkecho
        let i : Fin (n - 2) := ⟨k - 2, by omega⟩
        have hi := hliveLower i (by
          dsimp only [i]
          omega)
        have hindex : i.val + 2 = k := by
          dsimp only [i]
          omega
        simpa [hindex] using hi
      obtain ⟨word, D, hD, hreadyD, hzeroD, hdrop, hcount⟩ :=
        resetAwareLiveRetry_echo_event_round
          hpsi ring hn leader C hready hrootZero echo
            hechoPresent hechoLower hbaseNotLive
      exact ⟨word, D, hD,
        Or.inr (Or.inr ⟨hreadyD, hzeroD, hdrop, hcount⟩)⟩

set_option maxHeartbeats 3000000 in
/-- Birth-signal-transition form of one positive combined-rank round. -/
theorem resetAwareLiveRetry_birthSignalZero_positive_round
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (leader : Fin n) (C : EConfig n psi kappa tau)
    (hready : ResetAwareLiveRetryReady hpsi ring leader C)
    (hrootZero : (C leader).core.erase.core.label = ⟨0, hpsi⟩)
    (hliveRank : clockwiseMobileLiveRank ring leader C ≠ 0) :
    ∃ (word : DetSchedule n) (D : EConfig n psi kappa tau),
      D = runLocalSchedule ring
        (wallSweepBirthSignalZeroPathStallTransition
          hpsi kappa tau) C word ∧
      (PPLLWallSweepRestartableProtected.ProtectedLeaderAt
          hpsi D leader ∨
        (NoActiveDeletion D ∧
          RawLeaderless
            (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig D) ∧
          PPLLPpsiLeaderCreationRepair.bulletTwoCount D <
            PPLLPpsiLeaderCreationRepair.bulletTwoCount C) ∨
        (ResetAwareLiveRetryReady hpsi ring leader D ∧
          (D leader).core.erase.core.label = ⟨0, hpsi⟩ ∧
          clockwiseLiveEchoRetryRank ring leader D <
            clockwiseLiveEchoRetryRank ring leader C ∧
          PPLLPpsiLeaderCreationRepair.bulletTwoCount D ≤
            PPLLPpsiLeaderCreationRepair.bulletTwoCount C)) := by
  obtain ⟨live, _hliveCanonical, hlivePresent, hliveLower⟩ :=
    exists_firstClockwiseMobileLive_of_rank_ne_zero
      ring leader C hliveRank
  by_cases hechoZero : clockwiseEchoRank ring leader C = 0
  · have hbaseEcho : ∀ k, 1 < k → k ≤ live.val + 1 →
        (C (groupOffset ring leader k)).core.erase.core.echo = false := by
      intro k hk hklive
      exact follower_echo_false_of_clockwiseEchoRank_eq_zero
        ring leader C hechoZero k (by omega) (by omega)
    exact resetAwareLiveRetry_birthSignalZero_live_event_round
      hpsi ring hn leader C hready hrootZero live
        hlivePresent hliveLower hbaseEcho
  · obtain ⟨echo, _hechoCanonical, hechoPresent, hechoLower⟩ :=
      exists_firstClockwiseEcho_of_rank_ne_zero
        ring leader C hechoZero
    by_cases hliveFirst : live.val + 1 ≤ echo.val
    · have hbaseEcho : ∀ k, 1 < k → k ≤ live.val + 1 →
          (C (groupOffset ring leader k)).core.erase.core.echo = false := by
        intro k hk hklive
        let i : Fin (n - 1) := ⟨k - 1, by omega⟩
        have hi := hechoLower i (by
          dsimp only [i]
          omega)
        have hindex : i.val + 1 = k := by
          dsimp only [i]
          omega
        simpa [hindex] using hi
      exact resetAwareLiveRetry_birthSignalZero_live_event_round
        hpsi ring hn leader C hready hrootZero live
          hlivePresent hliveLower hbaseEcho
    · have hechoFirst : echo.val < live.val + 1 := by omega
      have hbaseNotLive : ∀ k, 1 < k → k ≤ echo.val + 1 →
          (C (groupOffset ring leader k)).core.erase.core.bullet ≠
            ⟨2, by omega⟩ := by
        intro k hk hkecho
        let i : Fin (n - 2) := ⟨k - 2, by omega⟩
        have hi := hliveLower i (by
          dsimp only [i]
          omega)
        have hindex : i.val + 2 = k := by
          dsimp only [i]
          omega
        simpa [hindex] using hi
      obtain ⟨word, D, hD, hreadyD, hzeroD, hdrop, hcount⟩ :=
        resetAwareLiveRetry_birthSignalZero_echo_event_round
          hpsi ring hn leader C hready hrootZero echo
            hechoPresent hechoLower hbaseNotLive
      exact ⟨word, D, hD,
        Or.inr (Or.inr ⟨hreadyD, hzeroD, hdrop, hcount⟩)⟩

set_option maxHeartbeats 4000000 in
/-- Strong induction on the combined mobile-live/echo rank closes the last
zero-root lane.  The endpoint is protected, leaderless with a strict global
live-count decrease, or globally follower-live-free and ready for the rooted
closing scheduler. -/
theorem exists_resetAwareLiveRetrySchedule_of_rank
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (leader : Fin n) (rank : Nat) (C : EConfig n psi kappa tau)
    (hready : ResetAwareLiveRetryReady hpsi ring leader C)
    (hrootZero : (C leader).core.erase.core.label = ⟨0, hpsi⟩)
    (hrank : clockwiseLiveEchoRetryRank ring leader C = rank) :
    ∃ (word : DetSchedule n) (D : EConfig n psi kappa tau),
      D = runLocalSchedule ring
        (wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
          hpsi kappa tau) C word ∧
      (PPLLWallSweepRestartableProtected.ProtectedLeaderAt
          hpsi D leader ∨
        (RawLeaderless
            (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig D) ∧
          PPLLPpsiLeaderCreationRepair.bulletTwoCount D <
            PPLLPpsiLeaderCreationRepair.bulletTwoCount C) ∨
        (ResetAwareRetryReady hpsi ring leader D ∧
          (D leader).core.erase.core.label = ⟨0, hpsi⟩ ∧
          PPLLPpsiLeaderCreationRepair.bulletTwoCount D ≤
            PPLLPpsiLeaderCreationRepair.bulletTwoCount C)) := by
  revert C
  induction rank using Nat.strongRecOn with
  | ind rank ih =>
      intro C hready hrootZero hrank
      by_cases hliveZero : clockwiseMobileLiveRank ring leader C = 0
      · exact ⟨[], C, by simp [runLocalSchedule],
          Or.inr (Or.inr
            ⟨hready.toRetryReady_of_mobileLiveRank_eq_zero
                ring leader C hliveZero,
              hrootZero, Nat.le_refl _⟩)⟩
      · obtain ⟨pref, C1, hC1, hout⟩ :=
          resetAwareLiveRetry_positive_round
            hpsi ring hn leader C hready hrootZero hliveZero
        rcases hout with hprotected | hleaderless | hretry
        · exact ⟨pref, C1, hC1, Or.inl hprotected⟩
        · exact ⟨pref, C1, hC1, Or.inr (Or.inl hleaderless)⟩
        · have hlt : clockwiseLiveEchoRetryRank ring leader C1 < rank := by
            calc
              clockwiseLiveEchoRetryRank ring leader C1 <
                  clockwiseLiveEchoRetryRank ring leader C := hretry.2.2.1
              _ = rank := hrank
          obtain ⟨tail, D, hD, htail⟩ :=
            ih (clockwiseLiveEchoRetryRank ring leader C1) hlt
              C1 hretry.1 hretry.2.1 rfl
          let T :=
            wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
              hpsi kappa tau
          let word := pref ++ tail
          refine ⟨word, D, ?_, ?_⟩
          · calc
              D = runLocalSchedule ring T C1 tail := hD
              _ = runLocalSchedule ring T
                  (runLocalSchedule ring T C pref) tail := by rw [← hC1]
              _ = runLocalSchedule ring T C (pref ++ tail) :=
                (runLocalSchedule_append_generic ring T C pref tail).symm
              _ = runLocalSchedule ring T C word := by rfl
          · rcases htail with hprotected | hleaderless | hdone
            · exact Or.inl hprotected
            · exact Or.inr (Or.inl ⟨hleaderless.1,
                Nat.lt_of_lt_of_le hleaderless.2 hretry.2.2.2⟩)
            · exact Or.inr (Or.inr ⟨hdone.1, hdone.2.1,
                Nat.le_trans hdone.2.2 hretry.2.2.2⟩)

/-- Public form of the live-aware retry scheduler at the configuration's
actual combined rank. -/
theorem exists_resetAwareLiveRetrySchedule
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (leader : Fin n) (C : EConfig n psi kappa tau)
    (hready : ResetAwareLiveRetryReady hpsi ring leader C)
    (hrootZero : (C leader).core.erase.core.label = ⟨0, hpsi⟩) :
    ∃ (word : DetSchedule n) (D : EConfig n psi kappa tau),
      D = runLocalSchedule ring
        (wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
          hpsi kappa tau) C word ∧
      (PPLLWallSweepRestartableProtected.ProtectedLeaderAt
          hpsi D leader ∨
        (RawLeaderless
            (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig D) ∧
          PPLLPpsiLeaderCreationRepair.bulletTwoCount D <
            PPLLPpsiLeaderCreationRepair.bulletTwoCount C) ∨
        (ResetAwareRetryReady hpsi ring leader D ∧
          (D leader).core.erase.core.label = ⟨0, hpsi⟩ ∧
          PPLLPpsiLeaderCreationRepair.bulletTwoCount D ≤
            PPLLPpsiLeaderCreationRepair.bulletTwoCount C)) := by
  exact exists_resetAwareLiveRetrySchedule_of_rank
    hpsi ring hn leader (clockwiseLiveEchoRetryRank ring leader C)
      C hready hrootZero rfl

set_option maxHeartbeats 4000000 in
/-- Birth-signal-transition strong induction and scheduler for the zero-root live lane. -/
theorem exists_resetAwareLiveRetryBirthSignalZeroSchedule_of_rank
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (leader : Fin n) (rank : Nat) (C : EConfig n psi kappa tau)
    (hready : ResetAwareLiveRetryReady hpsi ring leader C)
    (hrootZero : (C leader).core.erase.core.label = ⟨0, hpsi⟩)
    (hrank : clockwiseLiveEchoRetryRank ring leader C = rank) :
    ∃ (word : DetSchedule n) (D : EConfig n psi kappa tau),
      D = runLocalSchedule ring
        (wallSweepBirthSignalZeroPathStallTransition
          hpsi kappa tau) C word ∧
      (PPLLWallSweepRestartableProtected.ProtectedLeaderAt
          hpsi D leader ∨
        (NoActiveDeletion D ∧
          RawLeaderless
            (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig D) ∧
          PPLLPpsiLeaderCreationRepair.bulletTwoCount D <
            PPLLPpsiLeaderCreationRepair.bulletTwoCount C) ∨
        (ResetAwareRetryReady hpsi ring leader D ∧
          (D leader).core.erase.core.label = ⟨0, hpsi⟩ ∧
          PPLLPpsiLeaderCreationRepair.bulletTwoCount D ≤
            PPLLPpsiLeaderCreationRepair.bulletTwoCount C)) := by
  revert C
  induction rank using Nat.strongRecOn with
  | ind rank ih =>
      intro C hready hrootZero hrank
      by_cases hliveZero : clockwiseMobileLiveRank ring leader C = 0
      · exact ⟨[], C, by simp [runLocalSchedule],
          Or.inr (Or.inr
            ⟨hready.toRetryReady_of_mobileLiveRank_eq_zero
                ring leader C hliveZero,
              hrootZero, Nat.le_refl _⟩)⟩
      · obtain ⟨pref, C1, hC1, hout⟩ :=
          resetAwareLiveRetry_birthSignalZero_positive_round
            hpsi ring hn leader C hready hrootZero hliveZero
        rcases hout with hprotected | hleaderless | hretry
        · exact ⟨pref, C1, hC1, Or.inl hprotected⟩
        · exact ⟨pref, C1, hC1, Or.inr (Or.inl hleaderless)⟩
        · have hlt : clockwiseLiveEchoRetryRank ring leader C1 < rank := by
            calc
              clockwiseLiveEchoRetryRank ring leader C1 <
                  clockwiseLiveEchoRetryRank ring leader C := hretry.2.2.1
              _ = rank := hrank
          obtain ⟨tail, D, hD, htail⟩ :=
            ih (clockwiseLiveEchoRetryRank ring leader C1) hlt
              C1 hretry.1 hretry.2.1 rfl
          let T :=
            wallSweepBirthSignalZeroPathStallTransition
              hpsi kappa tau
          let word := pref ++ tail
          refine ⟨word, D, ?_, ?_⟩
          · calc
              D = runLocalSchedule ring T C1 tail := hD
              _ = runLocalSchedule ring T
                  (runLocalSchedule ring T C pref) tail := by rw [← hC1]
              _ = runLocalSchedule ring T C (pref ++ tail) :=
                (runLocalSchedule_append_generic ring T C pref tail).symm
              _ = runLocalSchedule ring T C word := by rfl
          · rcases htail with hprotected | hleaderless | hdone
            · exact Or.inl hprotected
            · exact Or.inr (Or.inl ⟨hleaderless.1,
                hleaderless.2.1,
                Nat.lt_of_lt_of_le hleaderless.2.2 hretry.2.2.2⟩)
            · exact Or.inr (Or.inr ⟨hdone.1, hdone.2.1,
                Nat.le_trans hdone.2.2 hretry.2.2.2⟩)

/-- Public form of the live-aware retry scheduler at the configuration's
actual combined rank. -/
theorem exists_resetAwareLiveRetryBirthSignalZeroSchedule
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (leader : Fin n) (C : EConfig n psi kappa tau)
    (hready : ResetAwareLiveRetryReady hpsi ring leader C)
    (hrootZero : (C leader).core.erase.core.label = ⟨0, hpsi⟩) :
    ∃ (word : DetSchedule n) (D : EConfig n psi kappa tau),
      D = runLocalSchedule ring
        (wallSweepBirthSignalZeroPathStallTransition
          hpsi kappa tau) C word ∧
      (PPLLWallSweepRestartableProtected.ProtectedLeaderAt
          hpsi D leader ∨
        (NoActiveDeletion D ∧
          RawLeaderless
            (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig D) ∧
          PPLLPpsiLeaderCreationRepair.bulletTwoCount D <
            PPLLPpsiLeaderCreationRepair.bulletTwoCount C) ∨
        (ResetAwareRetryReady hpsi ring leader D ∧
          (D leader).core.erase.core.label = ⟨0, hpsi⟩ ∧
          PPLLPpsiLeaderCreationRepair.bulletTwoCount D ≤
            PPLLPpsiLeaderCreationRepair.bulletTwoCount C)) := by
  exact exists_resetAwareLiveRetryBirthSignalZeroSchedule_of_rank
    hpsi ring hn leader (clockwiseLiveEchoRetryRank ring leader C)
      C hready hrootZero rfl

set_option maxHeartbeats 5000000 in
/-- Label-independent live-event round for the integrated repair lane.  A
nearest live responder either deletes the unique leader with a strict global
live-count drop, or installs a shield and closes the rooted frontier after two
same-leader reseeds.  A farther live responder strictly lowers the combined
mobile-live/echo rank. -/
theorem resetAwareLiveRetry_live_event_round_to_shielded
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (leader : Fin n) (C : EConfig n psi kappa tau)
    (hready : ResetAwareLiveRetryReady hpsi ring leader C)
    (t : Fin (n - 2))
    (hpresent :
      (C (groupOffset ring leader (t.val + 2))).core.erase.core.bullet =
        ⟨2, by omega⟩)
    (hlower : ∀ i : Fin (n - 2), i.val < t.val →
      (C (groupOffset ring leader (i.val + 2))).core.erase.core.bullet ≠
        ⟨2, by omega⟩)
    (hbaseEcho : ∀ k, 1 < k → k ≤ t.val + 1 →
      (C (groupOffset ring leader k)).core.erase.core.echo = false) :
    ∃ (word : DetSchedule n) (D : EConfig n psi kappa tau),
      D = runLocalSchedule ring
        (wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
          hpsi kappa tau) C word ∧
      ((ResetAwareShieldedRetryReady hpsi ring leader D ∧
          PPLLPpsiLeaderCreationRepair.bulletTwoCount D ≤
            PPLLPpsiLeaderCreationRepair.bulletTwoCount C) ∨
        (RawLeaderless
            (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig D) ∧
          PPLLPpsiLeaderCreationRepair.bulletTwoCount D <
            PPLLPpsiLeaderCreationRepair.bulletTwoCount C) ∨
        (ResetAwareLiveRetryReady hpsi ring leader D ∧
          clockwiseLiveEchoRetryRank ring leader D <
            clockwiseLiveEchoRetryRank ring leader C ∧
          PPLLPpsiLeaderCreationRepair.bulletTwoCount D ≤
            PPLLPpsiLeaderCreationRepair.bulletTwoCount C)) := by
  obtain ⟨hfrontier, hfirstNotLive, hsignal⟩ := hready
  have hstateOne := resetAwareNormalizedPrefixState_one_of_frontierAt
    hpsi ring hn leader C hfrontier
  have hoffsetOne : groupOffset ring leader 1 =
      ring.rightNeighbor leader := by
    have hnext := rightNeighbor_groupOffset ring leader 0
    rw [groupOffset_zero_eq] at hnext
    simpa using hnext.symm
  have hvisitedOne : VisitedPrefixLiveFree ring leader C 1 := by
    intro k hk hkle
    have hkOne : k = 1 := by omega
    subst k
    rw [hoffsetOne]
    exact hfirstNotLive
  have hbaseNotLive : ∀ k, 1 < k → k ≤ t.val + 1 →
      (C (groupOffset ring leader k)).core.erase.core.bullet ≠
        ⟨2, by omega⟩ := by
    intro k hk hkt
    let i : Fin (n - 2) := ⟨k - 2, by omega⟩
    have hi := hlower i (by
      dsimp only [i]
      omega)
    have hindex : i.val + 2 = k := by
      dsimp only [i]
      omega
    simpa [hindex] using hi
  obtain ⟨pref, M, hM, _hprefLength, hstateM, hvisitedM,
      hrootM, hcountM⟩ :=
    hstateOne.exists_advance_to_of_base_event_free
      hpsi ring hn leader C C 1 (t.val + 1) hvisitedOne
        (by omega) (by omega) hbaseEcho hbaseNotLive
  have hrightLiveM :
      (M (groupOffset ring leader (t.val + 2))).core.erase.core.bullet =
        ⟨2, by omega⟩ := by
    rw [hstateM.untouched_ahead (t.val + 2) (by omega) (by omega)]
    exact hpresent
  have hfirstNotLiveM :
      (M (ring.rightNeighbor leader)).core.erase.core.bullet ≠
        ⟨2, by omega⟩ := by
    rw [← hoffsetOne]
    exact hvisitedM 1 (by omega) (by omega)
  have hsignalM :
      (M leader).core.erase.core.signal_B = ⟨0, by omega⟩ := by
    rw [hrootM]
    exact hsignal
  have hmobileM :=
    hstateM.mobileLiveRank_eq_base_of_visited_free
      ring leader C M (t.val + 1) hvisitedM hbaseNotLive
  let T := wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
    hpsi kappa tau
  by_cases htZero : t.val = 0
  · have hstateAtOne : ResetAwareNormalizedPrefixState
        hpsi ring leader C M 1 := by
      simpa [htZero] using hstateM
    have hrightAtTwo :
        (M (groupOffset ring leader 2)).core.erase.core.bullet =
          ⟨2, by omega⟩ := by
      simpa [htZero] using hrightLiveM
    let e := groupOffset ring leader 1
    let suffix : DetSchedule n := [e, leader]
    let D := runLocalSchedule ring T M suffix
    have hattempt := hstateAtOne.first_live_then_leader_attempt
      hpsi ring hn leader C M (by omega) hsignalM hrightAtTwo
    change
      (localStep ring T M e e).core.erase.core.bullet = ⟨2, by omega⟩ ∧
      (localStep ring T M e (groupOffset ring leader 2)).core.erase.core.bullet =
        ⟨0, by omega⟩ ∧
      NoActiveDeletion D ∧
      (D leader).core.erase.core.label =
        (M leader).core.erase.core.label ∧
      (D leader).core.erase.core.signal_B = ⟨0, by omega⟩ ∧
      ((hasUniqueLeader n
          (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig D) ∧
          (D leader).core.erase.core.leader = true ∧
          (D leader).core.erase.core.shield = true ∧
          (D (ring.rightNeighbor leader)).core.erase.core.bullet =
            ⟨2, by omega⟩ ∧
          PPLLPpsiLeaderCreationRepair.bulletTwoCount D ≤
            PPLLPpsiLeaderCreationRepair.bulletTwoCount M) ∨
        (RawLeaderless
            (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig D) ∧
          PPLLPpsiLeaderCreationRepair.bulletTwoCount D <
            PPLLPpsiLeaderCreationRepair.bulletTwoCount M)) at hattempt
    rcases hattempt with
      ⟨_hleftLive, _hrightZero, hnoActiveD, _hlabel, hsignalD,
        hsurvives | hleaderless⟩
    · have hrightNe : ring.rightNeighbor leader ≠ leader :=
        rightNeighbor_ne_self_of_one_lt ring hn leader
      have hrightFollowerD :
          (D (ring.rightNeighbor leader)).core.erase.core.leader = false := by
        by_cases hfalse :
            (D (ring.rightNeighbor leader)).core.erase.core.leader = false
        · exact hfalse
        · have htrue :
              (D (ring.rightNeighbor leader)).core.erase.core.leader = true :=
            by
              cases hvalue :
                  (D (ring.rightNeighbor leader)).core.erase.core.leader <;>
                simp_all
          obtain ⟨owner, howner, honly⟩ := hsurvives.1
          have hleaderOwner := honly leader hsurvives.2.1
          have hrightOwner := honly (ring.rightNeighbor leader) htrue
          exact (hrightNe (hrightOwner.trans hleaderOwner.symm)).elim
      let replay : DetSchedule n := [leader, leader]
      let E := runLocalSchedule ring T D replay
      have hshielded :=
        two_step_reseed_shieldedRetryReady_of_source_follower
          hpsi ring hn leader D hnoActiveD hsurvives.1
            ⟨hsurvives.2.1, hsurvives.2.2.1⟩ hrightFollowerD
      change ResetAwareShieldedRetryReady hpsi ring leader E at hshielded
      have hreseedCount :=
        two_step_reseed_bulletTwoCount_le_of_shielded_signal_zero
          hpsi ring hn leader D hnoActiveD hsurvives.2.1
            hrightFollowerD hsurvives.2.2.1 hsignalD
      change PPLLPpsiLeaderCreationRepair.bulletTwoCount E ≤
        PPLLPpsiLeaderCreationRepair.bulletTwoCount D at hreseedCount
      let word := pref ++ (suffix ++ replay)
      refine ⟨word, E, ?_, Or.inl
        ⟨hshielded, Nat.le_trans hreseedCount
          (Nat.le_trans hsurvives.2.2.2.2 hcountM)⟩⟩
      calc
        E = runLocalSchedule ring T D replay := rfl
        _ = runLocalSchedule ring T
            (runLocalSchedule ring T M suffix) replay := by rfl
        _ = runLocalSchedule ring T M (suffix ++ replay) :=
          (runLocalSchedule_append_generic ring T M suffix replay).symm
        _ = runLocalSchedule ring T
            (runLocalSchedule ring T C pref) (suffix ++ replay) := by
              rw [← hM]
        _ = runLocalSchedule ring T C (pref ++ (suffix ++ replay)) :=
          (runLocalSchedule_append_generic ring T C pref
            (suffix ++ replay)).symm
        _ = runLocalSchedule ring T C word := by rfl
    · let word := pref ++ suffix
      refine ⟨word, D, ?_, Or.inr (Or.inl ⟨hleaderless.1, ?_⟩)⟩
      · calc
          D = runLocalSchedule ring T M suffix := rfl
          _ = runLocalSchedule ring T
              (runLocalSchedule ring T C pref) suffix := by rw [← hM]
          _ = runLocalSchedule ring T C (pref ++ suffix) :=
            (runLocalSchedule_append_generic ring T C pref suffix).symm
          _ = runLocalSchedule ring T C word := by rfl
      · exact Nat.lt_of_lt_of_le hleaderless.2 hcountM
  · have htPos : 0 < t.val := by omega
    let e := groupOffset ring leader (t.val + 1)
    let suffix : DetSchedule n := [e, leader, leader]
    let D := runLocalSchedule ring T M suffix
    have hretry := hstateM.far_live_then_two_step_reseed
      hpsi ring hn leader C M (t.val + 1) (by omega) (by omega)
        hfirstNotLiveM hsignalM hrightLiveM
    change ResetAwareLiveRetryReady hpsi ring leader D ∧
      (D leader).core.erase.core.label =
        (M leader).core.erase.core.label ∧
      PPLLPpsiLeaderCreationRepair.bulletTwoCount D ≤
        PPLLPpsiLeaderCreationRepair.bulletTwoCount M ∧
      clockwiseMobileLiveRank ring leader D <
        clockwiseMobileLiveRank ring leader M at hretry
    have hliveDC : clockwiseMobileLiveRank ring leader D <
        clockwiseMobileLiveRank ring leader C := by
      rw [← hmobileM]
      exact hretry.2.2.2
    have hcombined := clockwiseLiveEchoRetryRank_lt_of_live_lt
      ring leader C D hliveDC
    let word := pref ++ suffix
    refine ⟨word, D, ?_, Or.inr (Or.inr
      ⟨hretry.1, hcombined,
        Nat.le_trans hretry.2.2.1 hcountM⟩)⟩
    calc
      D = runLocalSchedule ring T M suffix := rfl
      _ = runLocalSchedule ring T
          (runLocalSchedule ring T C pref) suffix := by rw [← hM]
      _ = runLocalSchedule ring T C (pref ++ suffix) :=
        (runLocalSchedule_append_generic ring T C pref suffix).symm
      _ = runLocalSchedule ring T C word := by rfl

set_option maxHeartbeats 4000000 in
/-- Label-independent echo-event round.  The nearest echo strictly lowers the
echo digit while the mobile-live digit is fixed; the rooted physical label is
irrelevant to this descent. -/
theorem resetAwareLiveRetry_echo_event_round_general
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (leader : Fin n) (C : EConfig n psi kappa tau)
    (hready : ResetAwareLiveRetryReady hpsi ring leader C)
    (t : Fin (n - 1))
    (hpresent :
      (C (groupOffset ring leader (t.val + 1))).core.erase.core.echo = true)
    (hlower : ∀ i : Fin (n - 1), i.val < t.val →
      (C (groupOffset ring leader (i.val + 1))).core.erase.core.echo = false)
    (hbaseNotLive : ∀ k, 1 < k → k ≤ t.val + 1 →
      (C (groupOffset ring leader k)).core.erase.core.bullet ≠
        ⟨2, by omega⟩) :
    ∃ (word : DetSchedule n) (D : EConfig n psi kappa tau),
      D = runLocalSchedule ring
        (wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
          hpsi kappa tau) C word ∧
      ResetAwareLiveRetryReady hpsi ring leader D ∧
      clockwiseLiveEchoRetryRank ring leader D <
        clockwiseLiveEchoRetryRank ring leader C ∧
      PPLLPpsiLeaderCreationRepair.bulletTwoCount D ≤
        PPLLPpsiLeaderCreationRepair.bulletTwoCount C := by
  obtain ⟨hfrontier, hfirstNotLive, hsignal⟩ := hready
  have hstateOne := resetAwareNormalizedPrefixState_one_of_frontierAt
    hpsi ring hn leader C hfrontier
  obtain ⟨_noActive, _hunique, _hleader, _hrightFollower,
      _hrightLabel, _hleftProbe, _hrightProbe,
      _hleftNeutral, _hrightNeutral, _hleftReset, _hrightReset,
      _hleftEcho, hrightEchoFalse, _hsafe⟩ := hfrontier
  have hoffsetOne : groupOffset ring leader 1 =
      ring.rightNeighbor leader := by
    have hnext := rightNeighbor_groupOffset ring leader 0
    rw [groupOffset_zero_eq] at hnext
    simpa using hnext.symm
  have htPos : 0 < t.val := by
    by_cases htZero : t.val = 0
    · have hpresentFirst :
          (C (groupOffset ring leader 1)).core.erase.core.echo = true := by
        simpa [htZero] using hpresent
      have hfalseFirst :
          (C (groupOffset ring leader 1)).core.erase.core.echo = false := by
        rw [hoffsetOne]
        exact hrightEchoFalse
      rw [hfalseFirst] at hpresentFirst
      contradiction
    · omega
  have hvisitedOne : VisitedPrefixLiveFree ring leader C 1 := by
    intro k hk hkle
    have hkOne : k = 1 := by omega
    subst k
    rw [hoffsetOne]
    exact hfirstNotLive
  have hbaseEcho : ∀ k, 1 < k → k ≤ t.val →
      (C (groupOffset ring leader k)).core.erase.core.echo = false := by
    intro k hk hkt
    let i : Fin (n - 1) := ⟨k - 1, by omega⟩
    have hi := hlower i (by
      dsimp only [i]
      omega)
    have hindex : i.val + 1 = k := by
      dsimp only [i]
      omega
    simpa [hindex] using hi
  have hbaseNotLivePrefix : ∀ k, 1 < k → k ≤ t.val →
      (C (groupOffset ring leader k)).core.erase.core.bullet ≠
        ⟨2, by omega⟩ := by
    intro k hk hkt
    exact hbaseNotLive k hk (by omega)
  obtain ⟨pref, M, hM, _hprefLength, hstateM, hvisitedM,
      hrootM, hcountM⟩ :=
    hstateOne.exists_advance_to_of_base_event_free
      hpsi ring hn leader C C 1 t.val hvisitedOne
        (by omega) (by omega) hbaseEcho hbaseNotLivePrefix
  have hblockerM :
      (M (groupOffset ring leader (t.val + 1))).core.erase.core.echo =
        true := by
    rw [hstateM.untouched_ahead (t.val + 1) (by omega) (by omega)]
    exact hpresent
  have hrightNotLiveM :
      (M (groupOffset ring leader (t.val + 1))).core.erase.core.bullet ≠
        ⟨2, by omega⟩ := by
    rw [hstateM.untouched_ahead (t.val + 1) (by omega) (by omega)]
    exact hbaseNotLive (t.val + 1) (by omega) (by omega)
  have hsignalM :
      (M leader).core.erase.core.signal_B = ⟨0, by omega⟩ := by
    rw [hrootM]
    exact hsignal
  have hmobileM :=
    hstateM.mobileLiveRank_eq_base_of_visited_free
      ring leader C M t.val hvisitedM hbaseNotLivePrefix
  let T := wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
    hpsi kappa tau
  let suffix : DetSchedule n :=
    [groupOffset ring leader t.val, leader, leader]
  let D := runLocalSchedule ring T M suffix
  have hcollision : FirstBlockerEffect ring leader M D t ∧
      ResetAwareLiveRetryReady hpsi ring leader D ∧
      (D leader).core.erase.core.label =
        (M leader).core.erase.core.label ∧
      PPLLPpsiLeaderCreationRepair.bulletTwoCount D ≤
        PPLLPpsiLeaderCreationRepair.bulletTwoCount M ∧
      clockwiseMobileLiveRank ring leader D =
        clockwiseMobileLiveRank ring leader M := by
    simpa [T, suffix, D] using
      hstateM.collision_then_liveRetryReady
        hpsi ring hn leader C M t.val t.isLt hvisitedM
          hblockerM hrightNotLiveM hsignalM
  have heffect : FirstBlockerEffect ring leader C D t := {
    blocker_present := hpresent
    blocker_cleared := hcollision.1.blocker_cleared
    higher_unchanged := by
      intro s hts
      rw [hcollision.1.higher_unchanged s hts]
      have hsite := hstateM.untouched_ahead (s.val + 1)
        (by omega) (by omega)
      exact congrArg
        (fun u : ExpiringAgentState psi kappa tau =>
          u.core.erase.core.echo) hsite }
  have hmobileDC : clockwiseMobileLiveRank ring leader D =
      clockwiseMobileLiveRank ring leader C :=
    hcollision.2.2.2.2.trans hmobileM
  have hcombined := clockwiseLiveEchoRetryRank_lt_of_live_le_echo_lt
    ring leader C D (by omega) heffect.rank_lt
  let word := pref ++ suffix
  refine ⟨word, D, ?_, hcollision.2.1, hcombined,
    Nat.le_trans hcollision.2.2.2.1 hcountM⟩
  calc
    D = runLocalSchedule ring T M suffix := rfl
    _ = runLocalSchedule ring T
        (runLocalSchedule ring T C pref) suffix := by rw [← hM]
    _ = runLocalSchedule ring T C (pref ++ suffix) :=
      (runLocalSchedule_append_generic ring T C pref suffix).symm
    _ = runLocalSchedule ring T C word := by rfl

set_option maxHeartbeats 3000000 in
/-- Every positive mobile-live rank admits one label-independent descending
round.  Physical offset chooses between the nearest live and echo events;
ties go to the live branch. -/
theorem resetAwareLiveRetry_positive_round_to_shielded
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (leader : Fin n) (C : EConfig n psi kappa tau)
    (hready : ResetAwareLiveRetryReady hpsi ring leader C)
    (hliveRank : clockwiseMobileLiveRank ring leader C ≠ 0) :
    ∃ (word : DetSchedule n) (D : EConfig n psi kappa tau),
      D = runLocalSchedule ring
        (wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
          hpsi kappa tau) C word ∧
      ((ResetAwareShieldedRetryReady hpsi ring leader D ∧
          PPLLPpsiLeaderCreationRepair.bulletTwoCount D ≤
            PPLLPpsiLeaderCreationRepair.bulletTwoCount C) ∨
        (RawLeaderless
            (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig D) ∧
          PPLLPpsiLeaderCreationRepair.bulletTwoCount D <
            PPLLPpsiLeaderCreationRepair.bulletTwoCount C) ∨
        (ResetAwareLiveRetryReady hpsi ring leader D ∧
          clockwiseLiveEchoRetryRank ring leader D <
            clockwiseLiveEchoRetryRank ring leader C ∧
          PPLLPpsiLeaderCreationRepair.bulletTwoCount D ≤
            PPLLPpsiLeaderCreationRepair.bulletTwoCount C)) := by
  obtain ⟨live, _hliveCanonical, hlivePresent, hliveLower⟩ :=
    exists_firstClockwiseMobileLive_of_rank_ne_zero
      ring leader C hliveRank
  by_cases hechoZero : clockwiseEchoRank ring leader C = 0
  · have hbaseEcho : ∀ k, 1 < k → k ≤ live.val + 1 →
        (C (groupOffset ring leader k)).core.erase.core.echo = false := by
      intro k hk hklive
      exact follower_echo_false_of_clockwiseEchoRank_eq_zero
        ring leader C hechoZero k (by omega) (by omega)
    exact resetAwareLiveRetry_live_event_round_to_shielded
      hpsi ring hn leader C hready live
        hlivePresent hliveLower hbaseEcho
  · obtain ⟨echo, _hechoCanonical, hechoPresent, hechoLower⟩ :=
      exists_firstClockwiseEcho_of_rank_ne_zero
        ring leader C hechoZero
    by_cases hliveFirst : live.val + 1 ≤ echo.val
    · have hbaseEcho : ∀ k, 1 < k → k ≤ live.val + 1 →
          (C (groupOffset ring leader k)).core.erase.core.echo = false := by
        intro k hk hklive
        let i : Fin (n - 1) := ⟨k - 1, by omega⟩
        have hi := hechoLower i (by
          dsimp only [i]
          omega)
        have hindex : i.val + 1 = k := by
          dsimp only [i]
          omega
        simpa [hindex] using hi
      exact resetAwareLiveRetry_live_event_round_to_shielded
        hpsi ring hn leader C hready live
          hlivePresent hliveLower hbaseEcho
    · have hechoFirst : echo.val < live.val + 1 := by omega
      have hbaseNotLive : ∀ k, 1 < k → k ≤ echo.val + 1 →
          (C (groupOffset ring leader k)).core.erase.core.bullet ≠
            ⟨2, by omega⟩ := by
        intro k hk hkecho
        let i : Fin (n - 2) := ⟨k - 2, by omega⟩
        have hi := hliveLower i (by
          dsimp only [i]
          omega)
        have hindex : i.val + 2 = k := by
          dsimp only [i]
          omega
        simpa [hindex] using hi
      obtain ⟨word, D, hD, hreadyD, hdrop, hcount⟩ :=
        resetAwareLiveRetry_echo_event_round_general
          hpsi ring hn leader C hready echo
            hechoPresent hechoLower hbaseNotLive
      exact ⟨word, D, hD,
        Or.inr (Or.inr ⟨hreadyD, hdrop, hcount⟩)⟩

set_option maxHeartbeats 5000000 in
/-- Strong induction on the combined mobile-live/echo rank, with no root-label
premise.  The endpoint is a shielded rooted frontier, a strict global
live-count deletion, or a globally follower-live-free retry frontier. -/
theorem exists_resetAwareLiveRetryToShieldedSchedule_of_rank
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (leader : Fin n) (rank : Nat) (C : EConfig n psi kappa tau)
    (hready : ResetAwareLiveRetryReady hpsi ring leader C)
    (hrank : clockwiseLiveEchoRetryRank ring leader C = rank) :
    ∃ (word : DetSchedule n) (D : EConfig n psi kappa tau),
      D = runLocalSchedule ring
        (wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
          hpsi kappa tau) C word ∧
      ((ResetAwareShieldedRetryReady hpsi ring leader D ∧
          PPLLPpsiLeaderCreationRepair.bulletTwoCount D ≤
            PPLLPpsiLeaderCreationRepair.bulletTwoCount C) ∨
        (RawLeaderless
            (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig D) ∧
          PPLLPpsiLeaderCreationRepair.bulletTwoCount D <
            PPLLPpsiLeaderCreationRepair.bulletTwoCount C) ∨
        (ResetAwareRetryReady hpsi ring leader D ∧
          PPLLPpsiLeaderCreationRepair.bulletTwoCount D ≤
            PPLLPpsiLeaderCreationRepair.bulletTwoCount C)) := by
  revert C
  induction rank using Nat.strongRecOn with
  | ind rank ih =>
      intro C hready hrank
      by_cases hliveZero : clockwiseMobileLiveRank ring leader C = 0
      · exact ⟨[], C, by simp [runLocalSchedule],
          Or.inr (Or.inr
            ⟨hready.toRetryReady_of_mobileLiveRank_eq_zero
                ring leader C hliveZero,
              Nat.le_refl _⟩)⟩
      · obtain ⟨pref, C1, hC1, hout⟩ :=
          resetAwareLiveRetry_positive_round_to_shielded
            hpsi ring hn leader C hready hliveZero
        rcases hout with hshielded | hleaderless | hretry
        · exact ⟨pref, C1, hC1, Or.inl hshielded⟩
        · exact ⟨pref, C1, hC1, Or.inr (Or.inl hleaderless)⟩
        · have hlt : clockwiseLiveEchoRetryRank ring leader C1 < rank := by
            calc
              clockwiseLiveEchoRetryRank ring leader C1 <
                  clockwiseLiveEchoRetryRank ring leader C := hretry.2.1
              _ = rank := hrank
          obtain ⟨tail, D, hD, htail⟩ :=
            ih (clockwiseLiveEchoRetryRank ring leader C1) hlt
              C1 hretry.1 rfl
          let T :=
            wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
              hpsi kappa tau
          let word := pref ++ tail
          refine ⟨word, D, ?_, ?_⟩
          · calc
              D = runLocalSchedule ring T C1 tail := hD
              _ = runLocalSchedule ring T
                  (runLocalSchedule ring T C pref) tail := by rw [← hC1]
              _ = runLocalSchedule ring T C (pref ++ tail) :=
                (runLocalSchedule_append_generic ring T C pref tail).symm
              _ = runLocalSchedule ring T C word := by rfl
          · rcases htail with hshielded | hleaderless | hdone
            · exact Or.inl ⟨hshielded.1,
                Nat.le_trans hshielded.2 hretry.2.2⟩
            · exact Or.inr (Or.inl ⟨hleaderless.1,
                Nat.lt_of_lt_of_le hleaderless.2 hretry.2.2⟩)
            · exact Or.inr (Or.inr ⟨hdone.1,
                Nat.le_trans hdone.2 hretry.2.2⟩)

/-- Public label-independent live-aware scheduler at the configuration's
actual combined rank. -/
theorem exists_resetAwareLiveRetryToShieldedSchedule
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (leader : Fin n) (C : EConfig n psi kappa tau)
    (hready : ResetAwareLiveRetryReady hpsi ring leader C) :
    ∃ (word : DetSchedule n) (D : EConfig n psi kappa tau),
      D = runLocalSchedule ring
        (wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
          hpsi kappa tau) C word ∧
      ((ResetAwareShieldedRetryReady hpsi ring leader D ∧
          PPLLPpsiLeaderCreationRepair.bulletTwoCount D ≤
            PPLLPpsiLeaderCreationRepair.bulletTwoCount C) ∨
        (RawLeaderless
            (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig D) ∧
          PPLLPpsiLeaderCreationRepair.bulletTwoCount D <
            PPLLPpsiLeaderCreationRepair.bulletTwoCount C) ∨
        (ResetAwareRetryReady hpsi ring leader D ∧
          PPLLPpsiLeaderCreationRepair.bulletTwoCount D ≤
            PPLLPpsiLeaderCreationRepair.bulletTwoCount C)) := by
  exact exists_resetAwareLiveRetryToShieldedSchedule_of_rank
    hpsi ring hn leader (clockwiseLiveEchoRetryRank ring leader C)
      C hready rfl

set_option maxHeartbeats 5000000 in
/-- Birth-signal-transition label-independent live-event round for the integrated repair lane.  A
nearest live responder either deletes the unique leader with a strict global
live-count drop, or installs a shield and closes the rooted frontier after two
same-leader reseeds.  A farther live responder strictly lowers the combined
mobile-live/echo rank. -/
theorem resetAwareLiveRetry_birthSignalZero_live_event_round_to_shielded
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (leader : Fin n) (C : EConfig n psi kappa tau)
    (hready : ResetAwareLiveRetryReady hpsi ring leader C)
    (t : Fin (n - 2))
    (hpresent :
      (C (groupOffset ring leader (t.val + 2))).core.erase.core.bullet =
        ⟨2, by omega⟩)
    (hlower : ∀ i : Fin (n - 2), i.val < t.val →
      (C (groupOffset ring leader (i.val + 2))).core.erase.core.bullet ≠
        ⟨2, by omega⟩)
    (hbaseEcho : ∀ k, 1 < k → k ≤ t.val + 1 →
      (C (groupOffset ring leader k)).core.erase.core.echo = false) :
    ∃ (word : DetSchedule n) (D : EConfig n psi kappa tau),
      D = runLocalSchedule ring
        (wallSweepBirthSignalZeroPathStallTransition
          hpsi kappa tau) C word ∧
      ((ResetAwareShieldedRetryReady hpsi ring leader D ∧
          PPLLPpsiLeaderCreationRepair.bulletTwoCount D ≤
            PPLLPpsiLeaderCreationRepair.bulletTwoCount C) ∨
        (NoActiveDeletion D ∧
          RawLeaderless
            (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig D) ∧
          PPLLPpsiLeaderCreationRepair.bulletTwoCount D <
            PPLLPpsiLeaderCreationRepair.bulletTwoCount C) ∨
        (ResetAwareLiveRetryReady hpsi ring leader D ∧
          clockwiseLiveEchoRetryRank ring leader D <
            clockwiseLiveEchoRetryRank ring leader C ∧
          PPLLPpsiLeaderCreationRepair.bulletTwoCount D ≤
            PPLLPpsiLeaderCreationRepair.bulletTwoCount C)) := by
  obtain ⟨hfrontier, hfirstNotLive, hsignal⟩ := hready
  have hstateOne := resetAwareNormalizedPrefixState_one_of_frontierAt
    hpsi ring hn leader C hfrontier
  have hoffsetOne : groupOffset ring leader 1 =
      ring.rightNeighbor leader := by
    have hnext := rightNeighbor_groupOffset ring leader 0
    rw [groupOffset_zero_eq] at hnext
    simpa using hnext.symm
  have hvisitedOne : VisitedPrefixLiveFree ring leader C 1 := by
    intro k hk hkle
    have hkOne : k = 1 := by omega
    subst k
    rw [hoffsetOne]
    exact hfirstNotLive
  have hbaseNotLive : ∀ k, 1 < k → k ≤ t.val + 1 →
      (C (groupOffset ring leader k)).core.erase.core.bullet ≠
        ⟨2, by omega⟩ := by
    intro k hk hkt
    let i : Fin (n - 2) := ⟨k - 2, by omega⟩
    have hi := hlower i (by
      dsimp only [i]
      omega)
    have hindex : i.val + 2 = k := by
      dsimp only [i]
      omega
    simpa [hindex] using hi
  obtain ⟨pref, M, hM, _hprefLength, hstateM, hvisitedM,
      hrootM, hcountM⟩ :=
    hstateOne.exists_birthSignalZero_advance_to_of_base_event_free
      hpsi ring hn leader C C 1 (t.val + 1) hvisitedOne
        (by omega) (by omega) hbaseEcho hbaseNotLive
  have hrightLiveM :
      (M (groupOffset ring leader (t.val + 2))).core.erase.core.bullet =
        ⟨2, by omega⟩ := by
    rw [hstateM.untouched_ahead (t.val + 2) (by omega) (by omega)]
    exact hpresent
  have hfirstNotLiveM :
      (M (ring.rightNeighbor leader)).core.erase.core.bullet ≠
        ⟨2, by omega⟩ := by
    rw [← hoffsetOne]
    exact hvisitedM 1 (by omega) (by omega)
  have hsignalM :
      (M leader).core.erase.core.signal_B = ⟨0, by omega⟩ := by
    rw [hrootM]
    exact hsignal
  have hmobileM :=
    hstateM.mobileLiveRank_eq_base_of_visited_free
      ring leader C M (t.val + 1) hvisitedM hbaseNotLive
  let T := wallSweepBirthSignalZeroPathStallTransition
    hpsi kappa tau
  by_cases htZero : t.val = 0
  · have hstateAtOne : ResetAwareNormalizedPrefixState
        hpsi ring leader C M 1 := by
      simpa [htZero] using hstateM
    have hrightAtTwo :
        (M (groupOffset ring leader 2)).core.erase.core.bullet =
          ⟨2, by omega⟩ := by
      simpa [htZero] using hrightLiveM
    let e := groupOffset ring leader 1
    let suffix : DetSchedule n := [e, leader]
    let D := runLocalSchedule ring T M suffix
    have hattempt := hstateAtOne.first_live_then_birthSignalZero_leader_attempt
      hpsi ring hn leader C M (by omega) hsignalM hrightAtTwo
    change
      (localStep ring T M e e).core.erase.core.bullet = ⟨2, by omega⟩ ∧
      (localStep ring T M e (groupOffset ring leader 2)).core.erase.core.bullet =
        ⟨0, by omega⟩ ∧
      NoActiveDeletion D ∧
      (D leader).core.erase.core.label =
        (M leader).core.erase.core.label ∧
      (D leader).core.erase.core.signal_B = ⟨0, by omega⟩ ∧
      ((hasUniqueLeader n
          (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig D) ∧
          (D leader).core.erase.core.leader = true ∧
          (D leader).core.erase.core.shield = true ∧
          (D (ring.rightNeighbor leader)).core.erase.core.bullet =
            ⟨2, by omega⟩ ∧
          PPLLPpsiLeaderCreationRepair.bulletTwoCount D ≤
            PPLLPpsiLeaderCreationRepair.bulletTwoCount M) ∨
        (RawLeaderless
            (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig D) ∧
          PPLLPpsiLeaderCreationRepair.bulletTwoCount D <
            PPLLPpsiLeaderCreationRepair.bulletTwoCount M)) at hattempt
    rcases hattempt with
      ⟨_hleftLive, _hrightZero, hnoActiveD, _hlabel, hsignalD,
        hsurvives | hleaderless⟩
    · have hrightNe : ring.rightNeighbor leader ≠ leader :=
        rightNeighbor_ne_self_of_one_lt ring hn leader
      have hrightFollowerD :
          (D (ring.rightNeighbor leader)).core.erase.core.leader = false := by
        by_cases hfalse :
            (D (ring.rightNeighbor leader)).core.erase.core.leader = false
        · exact hfalse
        · have htrue :
              (D (ring.rightNeighbor leader)).core.erase.core.leader = true :=
            by
              cases hvalue :
                  (D (ring.rightNeighbor leader)).core.erase.core.leader <;>
                simp_all
          obtain ⟨owner, howner, honly⟩ := hsurvives.1
          have hleaderOwner := honly leader hsurvives.2.1
          have hrightOwner := honly (ring.rightNeighbor leader) htrue
          exact (hrightNe (hrightOwner.trans hleaderOwner.symm)).elim
      let replay : DetSchedule n := [leader, leader]
      let E := runLocalSchedule ring T D replay
      have hreseed :=
        two_step_reseed_birthSignalZero_shieldedRetryReady_and_count_le_of_source_follower
          hpsi ring hn leader D hnoActiveD hsurvives.1
            ⟨hsurvives.2.1, hsurvives.2.2.1⟩ hrightFollowerD hsignalD
      change ResetAwareShieldedRetryReady hpsi ring leader E ∧
          PPLLPpsiLeaderCreationRepair.bulletTwoCount E ≤
            PPLLPpsiLeaderCreationRepair.bulletTwoCount D at hreseed
      let word := pref ++ (suffix ++ replay)
      refine ⟨word, E, ?_, Or.inl
        ⟨hreseed.1, Nat.le_trans hreseed.2
          (Nat.le_trans hsurvives.2.2.2.2 hcountM)⟩⟩
      calc
        E = runLocalSchedule ring T D replay := rfl
        _ = runLocalSchedule ring T
            (runLocalSchedule ring T M suffix) replay := by rfl
        _ = runLocalSchedule ring T M (suffix ++ replay) :=
          (runLocalSchedule_append_generic ring T M suffix replay).symm
        _ = runLocalSchedule ring T
            (runLocalSchedule ring T C pref) (suffix ++ replay) := by
              rw [← hM]
        _ = runLocalSchedule ring T C (pref ++ (suffix ++ replay)) :=
          (runLocalSchedule_append_generic ring T C pref
            (suffix ++ replay)).symm
        _ = runLocalSchedule ring T C word := by rfl
    · let word := pref ++ suffix
      refine ⟨word, D, ?_, Or.inr (Or.inl
        ⟨hnoActiveD, hleaderless.1, ?_⟩)⟩
      · calc
          D = runLocalSchedule ring T M suffix := rfl
          _ = runLocalSchedule ring T
              (runLocalSchedule ring T C pref) suffix := by rw [← hM]
          _ = runLocalSchedule ring T C (pref ++ suffix) :=
            (runLocalSchedule_append_generic ring T C pref suffix).symm
          _ = runLocalSchedule ring T C word := by rfl
      · exact Nat.lt_of_lt_of_le hleaderless.2 hcountM
  · have htPos : 0 < t.val := by omega
    let e := groupOffset ring leader (t.val + 1)
    let suffix : DetSchedule n := [e, leader, leader]
    let D := runLocalSchedule ring T M suffix
    have hretry := hstateM.far_live_then_birthSignalZero_two_step_reseed
      hpsi ring hn leader C M (t.val + 1) (by omega) (by omega)
        hfirstNotLiveM hsignalM hrightLiveM
    change ResetAwareLiveRetryReady hpsi ring leader D ∧
      (D leader).core.erase.core.label =
        (M leader).core.erase.core.label ∧
      PPLLPpsiLeaderCreationRepair.bulletTwoCount D ≤
        PPLLPpsiLeaderCreationRepair.bulletTwoCount M ∧
      clockwiseMobileLiveRank ring leader D <
        clockwiseMobileLiveRank ring leader M at hretry
    have hliveDC : clockwiseMobileLiveRank ring leader D <
        clockwiseMobileLiveRank ring leader C := by
      rw [← hmobileM]
      exact hretry.2.2.2
    have hcombined := clockwiseLiveEchoRetryRank_lt_of_live_lt
      ring leader C D hliveDC
    let word := pref ++ suffix
    refine ⟨word, D, ?_, Or.inr (Or.inr
      ⟨hretry.1, hcombined,
        Nat.le_trans hretry.2.2.1 hcountM⟩)⟩
    calc
      D = runLocalSchedule ring T M suffix := rfl
      _ = runLocalSchedule ring T
          (runLocalSchedule ring T C pref) suffix := by rw [← hM]
      _ = runLocalSchedule ring T C (pref ++ suffix) :=
        (runLocalSchedule_append_generic ring T C pref suffix).symm
      _ = runLocalSchedule ring T C word := by rfl

set_option maxHeartbeats 4000000 in
/-- Birth-signal-transition label-independent echo-event round.  The nearest echo strictly lowers the
echo digit while the mobile-live digit is fixed; the rooted physical label is
irrelevant to this descent. -/
theorem resetAwareLiveRetry_birthSignalZero_echo_event_round_general
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (leader : Fin n) (C : EConfig n psi kappa tau)
    (hready : ResetAwareLiveRetryReady hpsi ring leader C)
    (t : Fin (n - 1))
    (hpresent :
      (C (groupOffset ring leader (t.val + 1))).core.erase.core.echo = true)
    (hlower : ∀ i : Fin (n - 1), i.val < t.val →
      (C (groupOffset ring leader (i.val + 1))).core.erase.core.echo = false)
    (hbaseNotLive : ∀ k, 1 < k → k ≤ t.val + 1 →
      (C (groupOffset ring leader k)).core.erase.core.bullet ≠
        ⟨2, by omega⟩) :
    ∃ (word : DetSchedule n) (D : EConfig n psi kappa tau),
      D = runLocalSchedule ring
        (wallSweepBirthSignalZeroPathStallTransition
          hpsi kappa tau) C word ∧
      ResetAwareLiveRetryReady hpsi ring leader D ∧
      clockwiseLiveEchoRetryRank ring leader D <
        clockwiseLiveEchoRetryRank ring leader C ∧
      PPLLPpsiLeaderCreationRepair.bulletTwoCount D ≤
        PPLLPpsiLeaderCreationRepair.bulletTwoCount C := by
  obtain ⟨hfrontier, hfirstNotLive, hsignal⟩ := hready
  have hstateOne := resetAwareNormalizedPrefixState_one_of_frontierAt
    hpsi ring hn leader C hfrontier
  obtain ⟨_noActive, _hunique, _hleader, _hrightFollower,
      _hrightLabel, _hleftProbe, _hrightProbe,
      _hleftNeutral, _hrightNeutral, _hleftReset, _hrightReset,
      _hleftEcho, hrightEchoFalse, _hsafe⟩ := hfrontier
  have hoffsetOne : groupOffset ring leader 1 =
      ring.rightNeighbor leader := by
    have hnext := rightNeighbor_groupOffset ring leader 0
    rw [groupOffset_zero_eq] at hnext
    simpa using hnext.symm
  have htPos : 0 < t.val := by
    by_cases htZero : t.val = 0
    · have hpresentFirst :
          (C (groupOffset ring leader 1)).core.erase.core.echo = true := by
        simpa [htZero] using hpresent
      have hfalseFirst :
          (C (groupOffset ring leader 1)).core.erase.core.echo = false := by
        rw [hoffsetOne]
        exact hrightEchoFalse
      rw [hfalseFirst] at hpresentFirst
      contradiction
    · omega
  have hvisitedOne : VisitedPrefixLiveFree ring leader C 1 := by
    intro k hk hkle
    have hkOne : k = 1 := by omega
    subst k
    rw [hoffsetOne]
    exact hfirstNotLive
  have hbaseEcho : ∀ k, 1 < k → k ≤ t.val →
      (C (groupOffset ring leader k)).core.erase.core.echo = false := by
    intro k hk hkt
    let i : Fin (n - 1) := ⟨k - 1, by omega⟩
    have hi := hlower i (by
      dsimp only [i]
      omega)
    have hindex : i.val + 1 = k := by
      dsimp only [i]
      omega
    simpa [hindex] using hi
  have hbaseNotLivePrefix : ∀ k, 1 < k → k ≤ t.val →
      (C (groupOffset ring leader k)).core.erase.core.bullet ≠
        ⟨2, by omega⟩ := by
    intro k hk hkt
    exact hbaseNotLive k hk (by omega)
  obtain ⟨pref, M, hM, _hprefLength, hstateM, hvisitedM,
      hrootM, hcountM⟩ :=
    hstateOne.exists_birthSignalZero_advance_to_of_base_event_free
      hpsi ring hn leader C C 1 t.val hvisitedOne
        (by omega) (by omega) hbaseEcho hbaseNotLivePrefix
  have hblockerM :
      (M (groupOffset ring leader (t.val + 1))).core.erase.core.echo =
        true := by
    rw [hstateM.untouched_ahead (t.val + 1) (by omega) (by omega)]
    exact hpresent
  have hrightNotLiveM :
      (M (groupOffset ring leader (t.val + 1))).core.erase.core.bullet ≠
        ⟨2, by omega⟩ := by
    rw [hstateM.untouched_ahead (t.val + 1) (by omega) (by omega)]
    exact hbaseNotLive (t.val + 1) (by omega) (by omega)
  have hsignalM :
      (M leader).core.erase.core.signal_B = ⟨0, by omega⟩ := by
    rw [hrootM]
    exact hsignal
  have hmobileM :=
    hstateM.mobileLiveRank_eq_base_of_visited_free
      ring leader C M t.val hvisitedM hbaseNotLivePrefix
  let T := wallSweepBirthSignalZeroPathStallTransition
    hpsi kappa tau
  let suffix : DetSchedule n :=
    [groupOffset ring leader t.val, leader, leader]
  let D := runLocalSchedule ring T M suffix
  have hcollision : FirstBlockerEffect ring leader M D t ∧
      ResetAwareLiveRetryReady hpsi ring leader D ∧
      (D leader).core.erase.core.label =
        (M leader).core.erase.core.label ∧
      PPLLPpsiLeaderCreationRepair.bulletTwoCount D ≤
        PPLLPpsiLeaderCreationRepair.bulletTwoCount M ∧
      clockwiseMobileLiveRank ring leader D =
        clockwiseMobileLiveRank ring leader M := by
    simpa [T, suffix, D] using
      hstateM.collision_then_birthSignalZero_liveRetryReady
        hpsi ring hn leader C M t.val t.isLt hvisitedM
          hblockerM hrightNotLiveM hsignalM
  have heffect : FirstBlockerEffect ring leader C D t := {
    blocker_present := hpresent
    blocker_cleared := hcollision.1.blocker_cleared
    higher_unchanged := by
      intro s hts
      rw [hcollision.1.higher_unchanged s hts]
      have hsite := hstateM.untouched_ahead (s.val + 1)
        (by omega) (by omega)
      exact congrArg
        (fun u : ExpiringAgentState psi kappa tau =>
          u.core.erase.core.echo) hsite }
  have hmobileDC : clockwiseMobileLiveRank ring leader D =
      clockwiseMobileLiveRank ring leader C :=
    hcollision.2.2.2.2.trans hmobileM
  have hcombined := clockwiseLiveEchoRetryRank_lt_of_live_le_echo_lt
    ring leader C D (by omega) heffect.rank_lt
  let word := pref ++ suffix
  refine ⟨word, D, ?_, hcollision.2.1, hcombined,
    Nat.le_trans hcollision.2.2.2.1 hcountM⟩
  calc
    D = runLocalSchedule ring T M suffix := rfl
    _ = runLocalSchedule ring T
        (runLocalSchedule ring T C pref) suffix := by rw [← hM]
    _ = runLocalSchedule ring T C (pref ++ suffix) :=
      (runLocalSchedule_append_generic ring T C pref suffix).symm
    _ = runLocalSchedule ring T C word := by rfl

set_option maxHeartbeats 3000000 in
/-- Under the birth-signal transition, every positive mobile-live rank admits one label-independent descending
round.  Physical offset chooses between the nearest live and echo events;
ties go to the live branch. -/
theorem resetAwareLiveRetry_birthSignalZero_positive_round_to_shielded
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (leader : Fin n) (C : EConfig n psi kappa tau)
    (hready : ResetAwareLiveRetryReady hpsi ring leader C)
    (hliveRank : clockwiseMobileLiveRank ring leader C ≠ 0) :
    ∃ (word : DetSchedule n) (D : EConfig n psi kappa tau),
      D = runLocalSchedule ring
        (wallSweepBirthSignalZeroPathStallTransition
          hpsi kappa tau) C word ∧
      ((ResetAwareShieldedRetryReady hpsi ring leader D ∧
          PPLLPpsiLeaderCreationRepair.bulletTwoCount D ≤
            PPLLPpsiLeaderCreationRepair.bulletTwoCount C) ∨
        (NoActiveDeletion D ∧
          RawLeaderless
            (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig D) ∧
          PPLLPpsiLeaderCreationRepair.bulletTwoCount D <
            PPLLPpsiLeaderCreationRepair.bulletTwoCount C) ∨
        (ResetAwareLiveRetryReady hpsi ring leader D ∧
          clockwiseLiveEchoRetryRank ring leader D <
            clockwiseLiveEchoRetryRank ring leader C ∧
          PPLLPpsiLeaderCreationRepair.bulletTwoCount D ≤
            PPLLPpsiLeaderCreationRepair.bulletTwoCount C)) := by
  obtain ⟨live, _hliveCanonical, hlivePresent, hliveLower⟩ :=
    exists_firstClockwiseMobileLive_of_rank_ne_zero
      ring leader C hliveRank
  by_cases hechoZero : clockwiseEchoRank ring leader C = 0
  · have hbaseEcho : ∀ k, 1 < k → k ≤ live.val + 1 →
        (C (groupOffset ring leader k)).core.erase.core.echo = false := by
      intro k hk hklive
      exact follower_echo_false_of_clockwiseEchoRank_eq_zero
        ring leader C hechoZero k (by omega) (by omega)
    exact resetAwareLiveRetry_birthSignalZero_live_event_round_to_shielded
      hpsi ring hn leader C hready live
        hlivePresent hliveLower hbaseEcho
  · obtain ⟨echo, _hechoCanonical, hechoPresent, hechoLower⟩ :=
      exists_firstClockwiseEcho_of_rank_ne_zero
        ring leader C hechoZero
    by_cases hliveFirst : live.val + 1 ≤ echo.val
    · have hbaseEcho : ∀ k, 1 < k → k ≤ live.val + 1 →
          (C (groupOffset ring leader k)).core.erase.core.echo = false := by
        intro k hk hklive
        let i : Fin (n - 1) := ⟨k - 1, by omega⟩
        have hi := hechoLower i (by
          dsimp only [i]
          omega)
        have hindex : i.val + 1 = k := by
          dsimp only [i]
          omega
        simpa [hindex] using hi
      exact resetAwareLiveRetry_birthSignalZero_live_event_round_to_shielded
        hpsi ring hn leader C hready live
          hlivePresent hliveLower hbaseEcho
    · have hechoFirst : echo.val < live.val + 1 := by omega
      have hbaseNotLive : ∀ k, 1 < k → k ≤ echo.val + 1 →
          (C (groupOffset ring leader k)).core.erase.core.bullet ≠
            ⟨2, by omega⟩ := by
        intro k hk hkecho
        let i : Fin (n - 2) := ⟨k - 2, by omega⟩
        have hi := hliveLower i (by
          dsimp only [i]
          omega)
        have hindex : i.val + 2 = k := by
          dsimp only [i]
          omega
        simpa [hindex] using hi
      obtain ⟨word, D, hD, hreadyD, hdrop, hcount⟩ :=
        resetAwareLiveRetry_birthSignalZero_echo_event_round_general
          hpsi ring hn leader C hready echo
            hechoPresent hechoLower hbaseNotLive
      exact ⟨word, D, hD,
        Or.inr (Or.inr ⟨hreadyD, hdrop, hcount⟩)⟩

set_option maxHeartbeats 5000000 in
/-- Birth-signal-transition strong induction on the combined mobile-live/echo rank, with no root-label
premise.  The endpoint is a shielded rooted frontier, a strict global
live-count deletion, or a globally follower-live-free retry frontier. -/
theorem exists_resetAwareLiveRetryBirthSignalZeroToShieldedSchedule_of_rank
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (leader : Fin n) (rank : Nat) (C : EConfig n psi kappa tau)
    (hready : ResetAwareLiveRetryReady hpsi ring leader C)
    (hrank : clockwiseLiveEchoRetryRank ring leader C = rank) :
    ∃ (word : DetSchedule n) (D : EConfig n psi kappa tau),
      D = runLocalSchedule ring
        (wallSweepBirthSignalZeroPathStallTransition
          hpsi kappa tau) C word ∧
      ((ResetAwareShieldedRetryReady hpsi ring leader D ∧
          PPLLPpsiLeaderCreationRepair.bulletTwoCount D ≤
            PPLLPpsiLeaderCreationRepair.bulletTwoCount C) ∨
        (NoActiveDeletion D ∧
          RawLeaderless
            (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig D) ∧
          PPLLPpsiLeaderCreationRepair.bulletTwoCount D <
            PPLLPpsiLeaderCreationRepair.bulletTwoCount C) ∨
        (ResetAwareRetryReady hpsi ring leader D ∧
          PPLLPpsiLeaderCreationRepair.bulletTwoCount D ≤
            PPLLPpsiLeaderCreationRepair.bulletTwoCount C)) := by
  revert C
  induction rank using Nat.strongRecOn with
  | ind rank ih =>
      intro C hready hrank
      by_cases hliveZero : clockwiseMobileLiveRank ring leader C = 0
      · exact ⟨[], C, by simp [runLocalSchedule],
          Or.inr (Or.inr
            ⟨hready.toRetryReady_of_mobileLiveRank_eq_zero
                ring leader C hliveZero,
              Nat.le_refl _⟩)⟩
      · obtain ⟨pref, C1, hC1, hout⟩ :=
          resetAwareLiveRetry_birthSignalZero_positive_round_to_shielded
            hpsi ring hn leader C hready hliveZero
        rcases hout with hshielded | hleaderless | hretry
        · exact ⟨pref, C1, hC1, Or.inl hshielded⟩
        · exact ⟨pref, C1, hC1, Or.inr (Or.inl hleaderless)⟩
        · have hlt : clockwiseLiveEchoRetryRank ring leader C1 < rank := by
            calc
              clockwiseLiveEchoRetryRank ring leader C1 <
                  clockwiseLiveEchoRetryRank ring leader C := hretry.2.1
              _ = rank := hrank
          obtain ⟨tail, D, hD, htail⟩ :=
            ih (clockwiseLiveEchoRetryRank ring leader C1) hlt
              C1 hretry.1 rfl
          let T :=
            wallSweepBirthSignalZeroPathStallTransition
              hpsi kappa tau
          let word := pref ++ tail
          refine ⟨word, D, ?_, ?_⟩
          · calc
              D = runLocalSchedule ring T C1 tail := hD
              _ = runLocalSchedule ring T
                  (runLocalSchedule ring T C pref) tail := by rw [← hC1]
              _ = runLocalSchedule ring T C (pref ++ tail) :=
                (runLocalSchedule_append_generic ring T C pref tail).symm
              _ = runLocalSchedule ring T C word := by rfl
          · rcases htail with hshielded | hleaderless | hdone
            · exact Or.inl ⟨hshielded.1,
                Nat.le_trans hshielded.2 hretry.2.2⟩
            · exact Or.inr (Or.inl ⟨hleaderless.1,
                hleaderless.2.1,
                Nat.lt_of_lt_of_le hleaderless.2.2 hretry.2.2⟩)
            · exact Or.inr (Or.inr ⟨hdone.1,
                Nat.le_trans hdone.2 hretry.2.2⟩)

/-- Public birth-signal-transition label-independent live-aware scheduler at the configuration's
actual combined rank. -/
theorem exists_resetAwareLiveRetryBirthSignalZeroToShieldedSchedule
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (leader : Fin n) (C : EConfig n psi kappa tau)
    (hready : ResetAwareLiveRetryReady hpsi ring leader C) :
    ∃ (word : DetSchedule n) (D : EConfig n psi kappa tau),
      D = runLocalSchedule ring
        (wallSweepBirthSignalZeroPathStallTransition
          hpsi kappa tau) C word ∧
      ((ResetAwareShieldedRetryReady hpsi ring leader D ∧
          PPLLPpsiLeaderCreationRepair.bulletTwoCount D ≤
            PPLLPpsiLeaderCreationRepair.bulletTwoCount C) ∨
        (NoActiveDeletion D ∧
          RawLeaderless
            (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig D) ∧
          PPLLPpsiLeaderCreationRepair.bulletTwoCount D <
            PPLLPpsiLeaderCreationRepair.bulletTwoCount C) ∨
        (ResetAwareRetryReady hpsi ring leader D ∧
          PPLLPpsiLeaderCreationRepair.bulletTwoCount D ≤
            PPLLPpsiLeaderCreationRepair.bulletTwoCount C)) := by
  exact exists_resetAwareLiveRetryBirthSignalZeroToShieldedSchedule_of_rank
    hpsi ring hn leader (clockwiseLiveEchoRetryRank ring leader C)
      C hready rfl

set_option maxHeartbeats 3000000 in
/-- The far-live descent also closes after the nearest-live branch has parked
a live bullet at the first follower and installed the leader shield.  The
remote live responder still moves strictly toward the root; the first live
follower and shield are off the moving follower edge, and the two leader
reseeds reconstruct `ResetAwareShieldedLiveRetryReady` without increasing the
global live count. -/
theorem ResetAwareNormalizedPrefixState.far_live_then_two_step_reseed_shielded
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (leader : Fin n) (base current : EConfig n psi kappa tau)
    (steps : Nat)
    (hstate : ResetAwareNormalizedPrefixState
      hpsi ring leader base current steps)
    (hlt : steps < n - 1)
    (hfar : 1 < steps)
    (hfirstLive :
      (current (ring.rightNeighbor leader)).core.erase.core.bullet =
        ⟨2, by omega⟩)
    (hleaderShield : (current leader).core.erase.core.shield = true)
    (hleaderSignalZero :
      (current leader).core.erase.core.signal_B = ⟨0, by omega⟩)
    (hrightLive :
      (current (groupOffset ring leader (steps + 1))).core.erase.core.bullet =
        ⟨2, by omega⟩) :
    let e := groupOffset ring leader steps
    let T := wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
      hpsi kappa tau
    let D := runLocalSchedule ring T current [e, leader, leader]
    ResetAwareShieldedLiveRetryReady hpsi ring leader D ∧
      PPLLPpsiLeaderCreationRepair.bulletTwoCount D ≤
        PPLLPpsiLeaderCreationRepair.bulletTwoCount current ∧
      clockwiseMobileLiveRank ring leader D <
        clockwiseMobileLiveRank ring leader current := by
  let e := groupOffset ring leader steps
  let j := groupOffset ring leader (steps + 1)
  let first := ring.rightNeighbor leader
  let T := wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
    hpsi kappa tau
  let C1 := localStep ring T current e
  let D := runLocalSchedule ring T C1 [leader, leader]
  have hnpos : 0 < n := by omega
  have heBound : steps < n := by omega
  have hjBound : steps + 1 < n := by omega
  have hneighbor : ring.rightNeighbor e = j := by
    simpa [e, j] using rightNeighbor_groupOffset ring leader steps
  have hfirstOffset : first = groupOffset ring leader 1 := by
    have hnext := rightNeighbor_groupOffset ring leader 0
    rw [groupOffset_zero_eq] at hnext
    simpa [first] using hnext
  have heNotLeader : e ≠ leader := by
    have hne := groupOffset_ne_of_lt ring leader heBound
      hnpos (Nat.ne_of_gt hstate.steps_pos)
    exact fun heq =>
      hne (heq.trans (groupOffset_zero_eq ring leader).symm)
  have hjNotLeader : j ≠ leader := by
    have hne := groupOffset_ne_of_lt ring leader hjBound
      hnpos (Nat.ne_of_gt (Nat.zero_lt_succ steps))
    exact fun heq =>
      hne (heq.trans (groupOffset_zero_eq ring leader).symm)
  have hfirstNe : first ≠ leader :=
    rightNeighbor_ne_self_of_one_lt ring hn leader
  have hfirstNeE : first ≠ e := by
    rw [hfirstOffset]
    apply groupOffset_ne_of_lt ring leader (by omega) heBound
    omega
  have hfirstNeJ : first ≠ j := by
    rw [hfirstOffset]
    apply groupOffset_ne_of_lt ring leader (by omega) hjBound
    omega
  have hstep := resetAwareFollower_localStep_normalizes
    hpsi ring hn current e hstate.no_active
      (hstate.unique_leader e heNotLeader) hstate.frontier_reset
      (by rw [hneighbor]; exact hstate.unique_leader j hjNotLeader)
  change ResetAwareFollowerGlobalStepFrame hpsi ring current C1 e at hstep
  have hleaderC1 : (C1 leader).core.erase.core.leader = true :=
    (hstep.leader_eq leader).trans hstate.leader_alive
  have hfirstFollowerC1 :
      (C1 first).core.erase.core.leader = false :=
    (hstep.leader_eq first).trans
      (hstate.unique_leader first hfirstNe)
  have huniqueC1 : hasUniqueLeader n
      (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig C1) := by
    refine ⟨leader, hleaderC1, ?_⟩
    intro i hi
    by_cases hie : i = leader
    · exact hie
    · change (C1 i).core.erase.core.leader = true at hi
      have hfalse := (hstep.leader_eq i).trans
        (hstate.unique_leader i hie)
      have hbad : (false : Bool) = true := hfalse.symm.trans hi
      exact (Bool.false_ne_true hbad).elim
  have hfirstOff : C1 first = current first :=
    hstep.off_edge first hfirstNeE (by
      rw [hneighbor]
      exact hfirstNeJ)
  have hfirstLiveC1 :
      (C1 first).core.erase.core.bullet = ⟨2, by omega⟩ := by
    rw [hfirstOff]
    simpa [first] using hfirstLive
  have hleaderOff : C1 leader = current leader :=
    hstep.off_edge leader (Ne.symm heNotLeader) (by
      rw [hneighbor]
      exact Ne.symm hjNotLeader)
  have hleaderShieldC1 :
      (C1 leader).core.erase.core.shield = true := by
    rw [hleaderOff]
    exact hleaderShield
  have hleaderSignalZeroC1 :
      (C1 leader).core.erase.core.signal_B = ⟨0, by omega⟩ := by
    rw [hleaderOff]
    exact hleaderSignalZero
  have hready :=
    two_step_reseed_shieldedLiveRetryReady_of_firstFollower_live
      hpsi ring hn leader C1 hstep.no_active huniqueC1 hleaderC1
        (by simpa [first] using hfirstFollowerC1)
        (by simpa [first] using hfirstLiveC1) hleaderShieldC1
  change ResetAwareShieldedLiveRetryReady hpsi ring leader D at hready
  have hfirstCount := resetAwareFollower_localStep_bulletTwoCount_le
    hpsi ring hn current e hstate.no_active
      (hstate.unique_leader e heNotLeader) hstate.frontier_reset
      (by rw [hneighbor]; exact hstate.unique_leader j hjNotLeader)
  change PPLLPpsiLeaderCreationRepair.bulletTwoCount C1 ≤
    PPLLPpsiLeaderCreationRepair.bulletTwoCount current at hfirstCount
  have hsecondCount :=
    two_step_reseed_bulletTwoCount_le_of_shielded_signal_zero
      hpsi ring hn leader C1 hstep.no_active hleaderC1
        (by simpa [first] using hfirstFollowerC1)
        hleaderShieldC1 hleaderSignalZeroC1
  change PPLLPpsiLeaderCreationRepair.bulletTwoCount D ≤
    PPLLPpsiLeaderCreationRepair.bulletTwoCount C1 at hsecondCount
  have htotalCount :
      PPLLPpsiLeaderCreationRepair.bulletTwoCount D ≤
        PPLLPpsiLeaderCreationRepair.bulletTwoCount current :=
    Nat.le_trans hsecondCount hfirstCount
  have hrank := hstate.follower_then_two_step_reseed_mobileLiveRank_lt
    hpsi ring hn leader base current steps hlt hrightLive
  change clockwiseMobileLiveRank ring leader D <
    clockwiseMobileLiveRank ring leader current at hrank
  change ResetAwareShieldedLiveRetryReady hpsi ring leader
      (runLocalSchedule ring T current [e, leader, leader]) ∧
    PPLLPpsiLeaderCreationRepair.bulletTwoCount
        (runLocalSchedule ring T current [e, leader, leader]) ≤
      PPLLPpsiLeaderCreationRepair.bulletTwoCount current ∧
    clockwiseMobileLiveRank ring leader
        (runLocalSchedule ring T current [e, leader, leader]) <
      clockwiseMobileLiveRank ring leader current
  change ResetAwareShieldedLiveRetryReady hpsi ring leader D ∧
    PPLLPpsiLeaderCreationRepair.bulletTwoCount D ≤
      PPLLPpsiLeaderCreationRepair.bulletTwoCount current ∧
    clockwiseMobileLiveRank ring leader D <
      clockwiseMobileLiveRank ring leader current
  exact ⟨hready, htotalCount, hrank⟩

set_option maxHeartbeats 2000000 in
/-- The second interaction of the two-step leader reseed writes the positive
absence signal at the outgoing follower.  This payload is not part of the
structural retry-ready interface, so it is exposed separately for the outer
signal-aware scheduler. -/
theorem two_step_reseed_right_signal_one
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (leader : Fin n) (current : EConfig n psi kappa tau)
    (hnoActive : NoActiveDeletion current)
    (hunique : hasUniqueLeader n
      (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig current))
    (hleader : (current leader).core.erase.core.leader = true)
    (hjFollower :
      (current (ring.rightNeighbor leader)).core.erase.core.leader = false)
    (hfree :
      PPLLPpsiLeaderCreationRepair.BulletTwoFreeAwayFrom current leader) :
    let T :=
      wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
        hpsi kappa tau
    let D := runLocalSchedule ring T current [leader, leader]
    (D (ring.rightNeighbor leader)).core.erase.core.signal_B =
      ⟨1, by omega⟩ := by
  let j := ring.rightNeighbor leader
  have hje : j ≠ leader :=
    rightNeighbor_ne_self_of_one_lt ring hn leader
  have hsafe :
      (current j).core.erase.core.bullet = ⟨2, by omega⟩ →
        (current leader).core.erase.core.shield = true :=
    PPLLPpsiLeaderCreationRepair.edge_safe_of_bulletTwoFreeAwayFrom
      current leader j hfree hje
  let Tnew :=
    wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
      hpsi kappa tau
  let Told := wallSweepPreCheckResetLeaderSinkPathStallTransition
    hpsi kappa tau
  let Dnew := localStep ring Tnew current leader
  let Dold := localStep ring Told current leader
  have hpairFirst :
      Tnew (current leader) (current j) =
        Told (current leader) (current j) := by
    simpa [Tnew, Told, j] using
      (wallSweepResetProbePreCheckResetLeaderSinkPathStall_eq_of_left_leader
        hpsi kappa tau (current leader) (current j) hleader)
  have hD : Dnew = Dold :=
    localStep_eq_of_pair_eq ring Tnew Told current leader
      (by simpa [j] using hpairFirst)
  have hnormalOld :=
    PPLLPpsiLeaderCreationRepair.leaderStep_to_normalizedOutgoingUniqueLeaderAt
      hpsi ring hn current leader hnoActive hunique hleader
        (by simpa [j] using hjFollower) (by simpa [j] using hsafe)
  change PPLLPpsiLeaderCreationRepair.NormalizedOutgoingUniqueLeaderAt
    hpsi ring Dold leader at hnormalOld
  have hnormalNew :
      PPLLPpsiLeaderCreationRepair.NormalizedOutgoingUniqueLeaderAt
        hpsi ring Dnew leader := by
    rw [hD]
    exact hnormalOld
  have hfreeOld := leaderSink_localStep_bulletTwoFreeAwayFrom
    hpsi ring hn current leader hnoActive hfree
  change PPLLPpsiLeaderCreationRepair.BulletTwoFreeAwayFrom
    Dold leader at hfreeOld
  have hfreeNew :
      PPLLPpsiLeaderCreationRepair.BulletTwoFreeAwayFrom
        Dnew leader := by
    rw [hD]
    exact hfreeOld
  obtain ⟨hnoActiveD, _huniqueD, hleaderD, hjFollowerD,
      _halignedD, _hleftProbeD, _hrightProbeD,
      _hleftNeutralD, _hrightNeutralD, _hleftResetD,
      _hleftEchoD, _hrightEchoD, _hsafeD⟩ := hnormalNew
  have hopenD : WallPriorityOpen (Dnew leader) (Dnew j) :=
    WallPriorityOpen.of_noActiveDeletion Dnew hnoActiveD ring leader
  have hjNotLive :
      (Dnew j).core.erase.core.bullet ≠ ⟨2, by omega⟩ :=
    hfreeNew j hje
  have hsignal :=
    wallSweepResetProbePreCheckResetLeaderSinkPathStall_priority_open_right_signal_one_of_left_leader_not_live
      hpsi (Dnew leader) (Dnew j) hopenD hleaderD
        (by simpa [j] using hjFollowerD) hjNotLive
  let Enew := localStep ring Tnew Dnew leader
  have hright : Enew j = (Tnew (Dnew leader) (Dnew j)).2 := by
    simp [Enew, Tnew, localStep, j, hje]
  have hsignalE : (Enew j).core.erase.core.signal_B =
      ⟨1, by omega⟩ := by
    rw [hright]
    exact hsignal
  simpa [Tnew, Dnew, Enew, runLocalSchedule, j] using hsignalE

set_option maxHeartbeats 2000000 in
/-- The two leader-edge interactions used to reseed a reset frontier frame the
named leader's physical label.  This is kept separate from the frontier
structure because the existing retry scheduler does not otherwise constrain
the leader label. -/
theorem two_step_reseed_leader_label
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (leader : Fin n) (current : EConfig n psi kappa tau)
    (hnoActive : NoActiveDeletion current)
    (hunique : hasUniqueLeader n
      (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig current))
    (hleader : (current leader).core.erase.core.leader = true)
    (hjFollower :
      (current (ring.rightNeighbor leader)).core.erase.core.leader = false)
    (hfree :
      PPLLPpsiLeaderCreationRepair.BulletTwoFreeAwayFrom current leader) :
    let T :=
      wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
        hpsi kappa tau
    let D := runLocalSchedule ring T current [leader, leader]
    (D leader).core.erase.core.label =
      (current leader).core.erase.core.label := by
  let j := ring.rightNeighbor leader
  have hje : j ≠ leader :=
    rightNeighbor_ne_self_of_one_lt ring hn leader
  have hsafe :
      (current j).core.erase.core.bullet = ⟨2, by omega⟩ →
        (current leader).core.erase.core.shield = true :=
    PPLLPpsiLeaderCreationRepair.edge_safe_of_bulletTwoFreeAwayFrom
      current leader j hfree hje
  let T :=
    wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
      hpsi kappa tau
  let Troot := wallSweepPreCheckResetLeaderSinkPathStallTransition
    hpsi kappa tau
  let D := localStep ring T current leader
  let Droot := localStep ring Troot current leader
  have hpair : T (current leader) (current j) =
      Troot (current leader) (current j) := by
    simpa [T, Troot, j] using
      (wallSweepResetProbePreCheckResetLeaderSinkPathStall_eq_of_left_leader
        hpsi kappa tau (current leader) (current j) hleader)
  have hD : D = Droot :=
    localStep_eq_of_pair_eq ring T Troot current leader
      (by simpa [j] using hpair)
  have hopen : WallPriorityOpen (current leader) (current j) :=
    WallPriorityOpen.of_noActiveDeletion current hnoActive ring leader
  have hfirstPair :=
    wallSweepResetProbePreCheckResetLeaderSinkPathStall_source_follower_labels
      hpsi (current leader) (current j) hopen (.inl hleader)
        (by simpa [j] using hjFollower)
  have hDLeader : D leader =
      (T (current leader) (current j)).1 := by
    simp [D, T, localStep, j]
  have hfirstLabel : (D leader).core.erase.core.label =
      (current leader).core.erase.core.label := by
    rw [hDLeader]
    exact hfirstPair.1
  have hnormalRoot :=
    PPLLPpsiLeaderCreationRepair.leaderStep_to_normalizedOutgoingUniqueLeaderAt
      hpsi ring hn current leader hnoActive hunique hleader
        (by simpa [j] using hjFollower) (by simpa [j] using hsafe)
  change PPLLPpsiLeaderCreationRepair.NormalizedOutgoingUniqueLeaderAt
    hpsi ring Droot leader at hnormalRoot
  have hnormal :
      PPLLPpsiLeaderCreationRepair.NormalizedOutgoingUniqueLeaderAt
        hpsi ring D leader := by
    rw [hD]
    exact hnormalRoot
  obtain ⟨hnoActiveD, _huniqueD, hleaderD, hjFollowerD,
      _halignedD, _hleftProbeD, _hrightProbeD,
      _hleftNeutralD, _hrightNeutralD, _hleftResetD,
      _hleftEchoD, _hrightEchoD, _hsafeD⟩ := hnormal
  let E := localStep ring T D leader
  have hopenD : WallPriorityOpen (D leader) (D j) :=
    WallPriorityOpen.of_noActiveDeletion D hnoActiveD ring leader
  have hsecondPair :=
    wallSweepResetProbePreCheckResetLeaderSinkPathStall_source_follower_labels
      hpsi (D leader) (D j) hopenD (.inl hleaderD)
        (by simpa [j] using hjFollowerD)
  have hELeader : E leader = (T (D leader) (D j)).1 := by
    simp [E, T, localStep, j]
  have hsecondLabel : (E leader).core.erase.core.label =
      (D leader).core.erase.core.label := by
    rw [hELeader]
    exact hsecondPair.1
  simpa [T, D, E, runLocalSchedule] using
    hsecondLabel.trans hfirstLabel

set_option maxHeartbeats 3000000 in
/-- Any reset-aware follower step can be followed by two interactions at the
same named leader to restart the signal-aware boundary.  The restart preserves
the leader label and weakly decreases the mobile dummy rank. -/
theorem ResetAwareNormalizedPrefixState.follower_then_signal_reseed
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (leader : Fin n) (base current : EConfig n psi kappa tau)
    (steps : Nat)
    (hstate : ResetAwareNormalizedPrefixState
      hpsi ring leader base current steps)
    (hlt : steps < n - 1)
    (hfree :
      PPLLPpsiLeaderCreationRepair.BulletTwoFreeAwayFrom current leader) :
    let e := groupOffset ring leader steps
    let T := wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
      hpsi kappa tau
    let D := runLocalSchedule ring T current [e, leader, leader]
    ResetAwareSignalReady hpsi ring leader D ∧
      (D leader).core.erase.core.label =
        (current leader).core.erase.core.label ∧
      clockwiseMobileDummyRank ring leader D ≤
        clockwiseMobileDummyRank ring leader current := by
  let e := groupOffset ring leader steps
  let j := groupOffset ring leader (steps + 1)
  let T := wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
    hpsi kappa tau
  let C1 := localStep ring T current e
  let D := runLocalSchedule ring T C1 [leader, leader]
  have hnpos : 0 < n := by omega
  have heBound : steps < n := by omega
  have hjBound : steps + 1 < n := by omega
  have hneighbor : ring.rightNeighbor e = j := by
    simpa [e, j] using rightNeighbor_groupOffset ring leader steps
  have heNotLeader : e ≠ leader := by
    have hne := groupOffset_ne_of_lt ring leader heBound
      hnpos (Nat.ne_of_gt hstate.steps_pos)
    exact fun heq =>
      hne (heq.trans (groupOffset_zero_eq ring leader).symm)
  have hjNotLeader : j ≠ leader := by
    have hne := groupOffset_ne_of_lt ring leader hjBound
      hnpos (Nat.ne_of_gt (Nat.zero_lt_succ steps))
    exact fun heq =>
      hne (heq.trans (groupOffset_zero_eq ring leader).symm)
  have hstep := resetAwareFollower_localStep_normalizes
    hpsi ring hn current e hstate.no_active
      (hstate.unique_leader e heNotLeader) hstate.frontier_reset
      (by rw [hneighbor]; exact hstate.unique_leader j hjNotLeader)
  change ResetAwareFollowerGlobalStepFrame hpsi ring current C1 e at hstep
  have hfreeC1 := resetAwareFollower_localStep_bulletTwoFreeAwayFrom
    hpsi ring hn current e leader hstate.no_active
      (hstate.unique_leader e heNotLeader) hstate.frontier_reset
      (by rw [hneighbor]; exact hstate.unique_leader j hjNotLeader)
      hfree heNotLeader (by simpa [hneighbor] using hjNotLeader)
  change PPLLPpsiLeaderCreationRepair.BulletTwoFreeAwayFrom
    C1 leader at hfreeC1
  have hleaderC1 : (C1 leader).core.erase.core.leader = true :=
    (hstep.leader_eq leader).trans hstate.leader_alive
  have hfirstNe : ring.rightNeighbor leader ≠ leader :=
    rightNeighbor_ne_self_of_one_lt ring hn leader
  have hfirstFollowerC1 :
      (C1 (ring.rightNeighbor leader)).core.erase.core.leader = false :=
    (hstep.leader_eq (ring.rightNeighbor leader)).trans
      (hstate.unique_leader (ring.rightNeighbor leader) hfirstNe)
  have huniqueC1 : hasUniqueLeader n
      (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig C1) := by
    refine ⟨leader, hleaderC1, ?_⟩
    intro i hi
    by_cases hie : i = leader
    · exact hie
    · change (C1 i).core.erase.core.leader = true at hi
      have hfalse := (hstep.leader_eq i).trans
        (hstate.unique_leader i hie)
      have hbad : (false : Bool) = true := hfalse.symm.trans hi
      exact (Bool.false_ne_true hbad).elim
  have hready := two_step_reseed_of_ready
    hpsi ring hn leader C1 hstep.no_active huniqueC1
      hleaderC1 hfirstFollowerC1 hfreeC1
  change ResetAwareRetryReady hpsi ring leader D at hready
  have hsignal := two_step_reseed_right_signal_one
    hpsi ring hn leader C1 hstep.no_active huniqueC1
      hleaderC1 hfirstFollowerC1 hfreeC1
  change (D (ring.rightNeighbor leader)).core.erase.core.signal_B =
    ⟨1, by omega⟩ at hsignal
  have hlabel := two_step_reseed_leader_label
    hpsi ring hn leader C1 hstep.no_active huniqueC1
      hleaderC1 hfirstFollowerC1 hfreeC1
  change (D leader).core.erase.core.label =
      (C1 leader).core.erase.core.label at hlabel
  have hleaderOff : C1 leader = current leader :=
    hstep.off_edge leader (Ne.symm heNotLeader) (by
      rw [hneighbor]
      exact Ne.symm hjNotLeader)
  have hrank := hstate.follower_then_two_step_reseed_mobileDummyRank_le
    hpsi ring hn leader base current steps hlt hfree
  change clockwiseMobileDummyRank ring leader D ≤
      clockwiseMobileDummyRank ring leader current at hrank
  change ResetAwareSignalReady hpsi ring leader
      (runLocalSchedule ring T current [e, leader, leader]) ∧
    ((runLocalSchedule ring T current [e, leader, leader]) leader).core.erase.core.label =
      (current leader).core.erase.core.label ∧
    clockwiseMobileDummyRank ring leader
        (runLocalSchedule ring T current [e, leader, leader]) ≤
      clockwiseMobileDummyRank ring leader current
  change ResetAwareSignalReady hpsi ring leader D ∧
    (D leader).core.erase.core.label =
      (current leader).core.erase.core.label ∧
    clockwiseMobileDummyRank ring leader D ≤
      clockwiseMobileDummyRank ring leader current
  exact ⟨⟨hready, hsignal⟩,
    hlabel.trans (congrArg
      (fun u : ExpiringAgentState psi kappa tau =>
        u.core.erase.core.label) hleaderOff),
    hrank⟩

set_option maxHeartbeats 2000000 in
/-- If the follower responder is a dummy, the signal reseed above returns to
the same root at a strictly smaller mobile dummy rank. -/
theorem ResetAwareNormalizedPrefixState.follower_dummy_then_signal_reseed
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (leader : Fin n) (base current : EConfig n psi kappa tau)
    (steps : Nat)
    (hstate : ResetAwareNormalizedPrefixState
      hpsi ring leader base current steps)
    (hlt : steps < n - 1)
    (hfree :
      PPLLPpsiLeaderCreationRepair.BulletTwoFreeAwayFrom current leader)
    (hrightDummy :
      (current (groupOffset ring leader (steps + 1))).core.erase.core.bullet =
        ⟨1, by omega⟩) :
    let e := groupOffset ring leader steps
    let T := wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
      hpsi kappa tau
    let D := runLocalSchedule ring T current [e, leader, leader]
    ResetAwareSignalReady hpsi ring leader D ∧
      (D leader).core.erase.core.label =
        (current leader).core.erase.core.label ∧
      clockwiseMobileDummyRank ring leader D <
        clockwiseMobileDummyRank ring leader current := by
  have hbase := hstate.follower_then_signal_reseed
    hpsi ring hn leader base current steps hlt hfree
  have hstrict := hstate.follower_then_two_step_reseed_mobileDummyRank_lt
    hpsi ring hn leader base current steps hlt hfree hrightDummy
  dsimp only at hbase hstrict ⊢
  exact ⟨hbase.1, hbase.2.1, hstrict⟩

set_option maxHeartbeats 2000000 in
/-- Birth-signal-transition form of the follower-plus-signal reseed word. -/
theorem ResetAwareNormalizedPrefixState.follower_then_birthSignalZero_signal_reseed
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (leader : Fin n) (base current : EConfig n psi kappa tau)
    (steps : Nat)
    (hstate : ResetAwareNormalizedPrefixState
      hpsi ring leader base current steps)
    (hlt : steps < n - 1)
    (hfree :
      PPLLPpsiLeaderCreationRepair.BulletTwoFreeAwayFrom current leader) :
    let e := groupOffset ring leader steps
    let T := wallSweepBirthSignalZeroPathStallTransition
      hpsi kappa tau
    let D := runLocalSchedule ring T current [e, leader, leader]
    ResetAwareSignalReady hpsi ring leader D ∧
      (D leader).core.erase.core.label =
        (current leader).core.erase.core.label ∧
      clockwiseMobileDummyRank ring leader D ≤
        clockwiseMobileDummyRank ring leader current := by
  have heq := hstate.run_birthSignalZero_follower_then_two_leader_eq_of_bulletTwoFree
    hpsi ring hn leader base current steps hlt hfree
  have hold := hstate.follower_then_signal_reseed
    hpsi ring hn leader base current steps hlt hfree
  dsimp only at heq hold ⊢
  rw [heq]
  exact hold

set_option maxHeartbeats 2000000 in
/-- On a responder dummy, the birth-signal follower-plus-reseed word returns
signal-ready at a strictly smaller mobile-dummy rank. -/
theorem ResetAwareNormalizedPrefixState.follower_dummy_then_birthSignalZero_signal_reseed
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (leader : Fin n) (base current : EConfig n psi kappa tau)
    (steps : Nat)
    (hstate : ResetAwareNormalizedPrefixState
      hpsi ring leader base current steps)
    (hlt : steps < n - 1)
    (hfree :
      PPLLPpsiLeaderCreationRepair.BulletTwoFreeAwayFrom current leader)
    (hrightDummy :
      (current (groupOffset ring leader (steps + 1))).core.erase.core.bullet =
        ⟨1, by omega⟩) :
    let e := groupOffset ring leader steps
    let T := wallSweepBirthSignalZeroPathStallTransition
      hpsi kappa tau
    let D := runLocalSchedule ring T current [e, leader, leader]
    ResetAwareSignalReady hpsi ring leader D ∧
      (D leader).core.erase.core.label =
        (current leader).core.erase.core.label ∧
      clockwiseMobileDummyRank ring leader D <
        clockwiseMobileDummyRank ring leader current := by
  have heq := hstate.run_birthSignalZero_follower_then_two_leader_eq_of_bulletTwoFree
    hpsi ring hn leader base current steps hlt hfree
  have hold := hstate.follower_dummy_then_signal_reseed
    hpsi ring hn leader base current steps hlt hfree hrightDummy
  dsimp only at heq hold ⊢
  rw [heq]
  exact hold

set_option maxHeartbeats 2000000 in
/-- Any named unique zero-labelled root with follower live-bullet freedom can
be reauthenticated in two interactions at its outgoing edge.  This is the
bridge needed after reverse migration before a second normalization pass. -/
theorem zeroRoot_two_step_reseed
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (root : Fin n) (C : EConfig n psi kappa tau)
    (hnoActive : NoActiveDeletion C)
    (hunique : hasUniqueLeader n
      (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig C))
    (hroot : (C root).core.erase.core.leader = true)
    (hfree : PPLLPpsiLeaderCreationRepair.BulletTwoFreeAwayFrom C root)
    (hzero : (C root).core.erase.core.label = ⟨0, hpsi⟩) :
    let T :=
      wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
        hpsi kappa tau
    let D := runLocalSchedule ring T C [root, root]
    ResetAwareRetryReady hpsi ring root D ∧
      (D root).core.erase.core.label = ⟨0, hpsi⟩ := by
  have hrightNe : ring.rightNeighbor root ≠ root :=
    rightNeighbor_ne_self_of_one_lt ring hn root
  have huniqueFields := hunique
  obtain ⟨onlyRoot, _honlyAlive, honly⟩ := huniqueFields
  have hrootEq : root = onlyRoot := by
    apply honly
    exact hroot
  have hrightFollower :
      (C (ring.rightNeighbor root)).core.erase.core.leader = false := by
    cases hr : (C (ring.rightNeighbor root)).core.erase.core.leader with
    | false => rfl
    | true =>
        have hrightEq : ring.rightNeighbor root = onlyRoot := by
          apply honly
          exact hr
        have hbad : ring.rightNeighbor root = root :=
          hrightEq.trans hrootEq.symm
        exact (hrightNe hbad).elim
  have hready := two_step_reseed_of_ready
    hpsi ring hn root C hnoActive hunique hroot hrightFollower hfree
  have hlabel := two_step_reseed_leader_label
    hpsi ring hn root C hnoActive hunique hroot hrightFollower hfree
  exact ⟨hready, hlabel.trans hzero⟩

set_option maxHeartbeats 2000000 in
/-- The zero-root reseed establishes the stronger outer-round boundary: the
structural reset frontier, preserved zero root label, and a positive signal
at the first outgoing follower all hold simultaneously. -/
theorem zeroRoot_two_step_reseed_signalReady
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (root : Fin n) (C : EConfig n psi kappa tau)
    (hnoActive : NoActiveDeletion C)
    (hunique : hasUniqueLeader n
      (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig C))
    (hroot : (C root).core.erase.core.leader = true)
    (hfree : PPLLPpsiLeaderCreationRepair.BulletTwoFreeAwayFrom C root)
    (hzero : (C root).core.erase.core.label = ⟨0, hpsi⟩) :
    let T :=
      wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
        hpsi kappa tau
    let D := runLocalSchedule ring T C [root, root]
    ResetAwareSignalReady hpsi ring root D ∧
      (D root).core.erase.core.label = ⟨0, hpsi⟩ := by
  have hrightNe : ring.rightNeighbor root ≠ root :=
    rightNeighbor_ne_self_of_one_lt ring hn root
  have huniqueFields := hunique
  obtain ⟨onlyRoot, _honlyAlive, honly⟩ := huniqueFields
  have hrootEq : root = onlyRoot := by
    apply honly
    exact hroot
  have hrightFollower :
      (C (ring.rightNeighbor root)).core.erase.core.leader = false := by
    cases hr : (C (ring.rightNeighbor root)).core.erase.core.leader with
    | false => rfl
    | true =>
        have hrightEq : ring.rightNeighbor root = onlyRoot := by
          apply honly
          exact hr
        have hbad : ring.rightNeighbor root = root :=
          hrightEq.trans hrootEq.symm
        exact (hrightNe hbad).elim
  have hbase := zeroRoot_two_step_reseed
    hpsi ring hn root C hnoActive hunique hroot hfree hzero
  have hsignal := two_step_reseed_right_signal_one
    hpsi ring hn root C hnoActive hunique hroot hrightFollower hfree
  exact ⟨⟨hbase.1, hsignal⟩, hbase.2⟩

set_option maxHeartbeats 2000000 in
/-- Birth-signal-transition form of the two-edge zero-root reseed. -/
theorem zeroRoot_birthSignalZero_two_step_reseed
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (root : Fin n) (C : EConfig n psi kappa tau)
    (hnoActive : NoActiveDeletion C)
    (hunique : hasUniqueLeader n
      (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig C))
    (hroot : (C root).core.erase.core.leader = true)
    (hfree : PPLLPpsiLeaderCreationRepair.BulletTwoFreeAwayFrom C root)
    (hzero : (C root).core.erase.core.label = ⟨0, hpsi⟩) :
    let T := wallSweepBirthSignalZeroPathStallTransition
      hpsi kappa tau
    let D := runLocalSchedule ring T C [root, root]
    ResetAwareRetryReady hpsi ring root D ∧
      (D root).core.erase.core.label = ⟨0, hpsi⟩ := by
  have hrightNe : ring.rightNeighbor root ≠ root :=
    rightNeighbor_ne_self_of_one_lt ring hn root
  have huniqueFields := hunique
  obtain ⟨onlyRoot, _honlyAlive, honly⟩ := huniqueFields
  have hrootEq : root = onlyRoot := honly root hroot
  have hrightFollower :
      (C (ring.rightNeighbor root)).core.erase.core.leader = false := by
    cases hr : (C (ring.rightNeighbor root)).core.erase.core.leader with
    | false => rfl
    | true =>
        have hrightEq : ring.rightNeighbor root = onlyRoot :=
          honly (ring.rightNeighbor root) hr
        exact (hrightNe (hrightEq.trans hrootEq.symm)).elim
  have hsafe :
      (C (ring.rightNeighbor root)).core.erase.core.bullet =
          ⟨2, by omega⟩ →
        (C root).core.erase.core.shield = true :=
    PPLLPpsiLeaderCreationRepair.edge_safe_of_bulletTwoFreeAwayFrom
      C root (ring.rightNeighbor root) hfree hrightNe
  have heq := runLocalSchedule_birthSignalZero_two_leader_eq_of_safe
    hpsi ring hn root C hnoActive hunique hroot hrightFollower hsafe
  have hold := zeroRoot_two_step_reseed
    hpsi ring hn root C hnoActive hunique hroot hfree hzero
  dsimp only at heq hold ⊢
  rw [heq]
  exact hold

set_option maxHeartbeats 2000000 in
/-- Birth-signal-transition form of the signal-aware zero-root reseed. -/
theorem zeroRoot_birthSignalZero_two_step_reseed_signalReady
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (root : Fin n) (C : EConfig n psi kappa tau)
    (hnoActive : NoActiveDeletion C)
    (hunique : hasUniqueLeader n
      (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig C))
    (hroot : (C root).core.erase.core.leader = true)
    (hfree : PPLLPpsiLeaderCreationRepair.BulletTwoFreeAwayFrom C root)
    (hzero : (C root).core.erase.core.label = ⟨0, hpsi⟩) :
    let T := wallSweepBirthSignalZeroPathStallTransition
      hpsi kappa tau
    let D := runLocalSchedule ring T C [root, root]
    ResetAwareSignalReady hpsi ring root D ∧
      (D root).core.erase.core.label = ⟨0, hpsi⟩ := by
  have hrightNe : ring.rightNeighbor root ≠ root :=
    rightNeighbor_ne_self_of_one_lt ring hn root
  have huniqueFields := hunique
  obtain ⟨onlyRoot, _honlyAlive, honly⟩ := huniqueFields
  have hrootEq : root = onlyRoot := honly root hroot
  have hrightFollower :
      (C (ring.rightNeighbor root)).core.erase.core.leader = false := by
    cases hr : (C (ring.rightNeighbor root)).core.erase.core.leader with
    | false => rfl
    | true =>
        have hrightEq : ring.rightNeighbor root = onlyRoot :=
          honly (ring.rightNeighbor root) hr
        exact (hrightNe (hrightEq.trans hrootEq.symm)).elim
  have hsafe :
      (C (ring.rightNeighbor root)).core.erase.core.bullet =
          ⟨2, by omega⟩ →
        (C root).core.erase.core.shield = true :=
    PPLLPpsiLeaderCreationRepair.edge_safe_of_bulletTwoFreeAwayFrom
      C root (ring.rightNeighbor root) hfree hrightNe
  have heq := runLocalSchedule_birthSignalZero_two_leader_eq_of_safe
    hpsi ring hn root C hnoActive hunique hroot hrightFollower hsafe
  have hold := zeroRoot_two_step_reseed_signalReady
    hpsi ring hn root C hnoActive hunique hroot hfree hzero
  dsimp only at heq hold ⊢
  rw [heq]
  exact hold

set_option maxHeartbeats 2000000 in
/-- A completed first normalization, the greatest-zero reverse suffix, and two
leader-edge interactions compose to a fresh authenticated frontier rooted at
the zero-labelled leader.  The additional word after the first normalization
has length at most `n+1`. -/
theorem ResetAwareRetryDone.exists_zeroRoot_reseed
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (leader : Fin n) (C : EConfig n psi kappa tau)
    (hdone : ResetAwareRetryDone hpsi ring leader C)
    (hpsiLe : psi ≤ n) :
    ∃ k, 0 < k ∧ k ≤ n ∧
      let newRoot := groupOffset ring leader k
      let T :=
        wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
          hpsi kappa tau
      let reverseWord := pPsiProbeChasePrefix ring leader (n - k)
      let word := reverseWord ++ [newRoot, newRoot]
      let D := runLocalSchedule ring T C word
      word.length ≤ n + 1 ∧
        ResetAwareRetryReady hpsi ring newRoot D ∧
        (D newRoot).core.erase.core.label = ⟨0, hpsi⟩ := by
  obtain ⟨k, hkpos, hkle, hresult⟩ :=
    hdone.exists_reverseMigrationSchedule_to_zero
      hpsi ring hn leader C hpsiLe
  let newRoot := groupOffset ring leader k
  let T :=
    wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
      hpsi kappa tau
  let reverseWord := pPsiProbeChasePrefix ring leader (n - k)
  let M := runLocalSchedule ring T C reverseWord
  change reverseWord.length = n - k ∧
      NoActiveDeletion M ∧
      hasUniqueLeader n
        (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig M) ∧
      (M newRoot).core.erase.core.leader = true ∧
      PPLLPpsiLeaderCreationRepair.BulletTwoFreeAwayFrom M newRoot ∧
      (M newRoot).core.erase.core.label = ⟨0, hpsi⟩ ∧
      ∀ i, (M i).core.erase.core.label =
        (C i).core.erase.core.label at hresult
  obtain ⟨hlength, hnoActive, hunique, hroot, hfree, hzero, _hlabels⟩ :=
    hresult
  have hreseed := zeroRoot_two_step_reseed
    hpsi ring hn newRoot M hnoActive hunique hroot hfree hzero
  let D := runLocalSchedule ring T M [newRoot, newRoot]
  change ResetAwareRetryReady hpsi ring newRoot D ∧
      (D newRoot).core.erase.core.label = ⟨0, hpsi⟩ at hreseed
  refine ⟨k, hkpos, hkle, ?_⟩
  change (reverseWord ++ [newRoot, newRoot]).length ≤ n + 1 ∧
      ResetAwareRetryReady hpsi ring newRoot
        (runLocalSchedule ring T C
          (reverseWord ++ [newRoot, newRoot])) ∧
      ((runLocalSchedule ring T C
        (reverseWord ++ [newRoot, newRoot])) newRoot).core.erase.core.label =
          ⟨0, hpsi⟩
  rw [runLocalSchedule_append_generic]
  change (reverseWord ++ [newRoot, newRoot]).length ≤ n + 1 ∧
      ResetAwareRetryReady hpsi ring newRoot D ∧
      (D newRoot).core.erase.core.label = ⟨0, hpsi⟩
  refine ⟨?_, hreseed⟩
  simp only [List.length_append, List.length_cons, List.length_nil]
  rw [hlength]
  omega

set_option maxHeartbeats 2000000 in
/-- The same greatest-zero migration and two-step reseed establish the
signal-aware outer-round boundary.  The returned literal schedule has the
same `n+1` bound as the structural reseed theorem. -/
theorem ResetAwareRetryDone.exists_zeroRoot_signalReady
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (leader : Fin n) (C : EConfig n psi kappa tau)
    (hdone : ResetAwareRetryDone hpsi ring leader C)
    (hpsiLe : psi ≤ n) :
    ∃ k, 0 < k ∧ k ≤ n ∧
      let newRoot := groupOffset ring leader k
      let T :=
        wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
          hpsi kappa tau
      let reverseWord := pPsiProbeChasePrefix ring leader (n - k)
      let word := reverseWord ++ [newRoot, newRoot]
      let D := runLocalSchedule ring T C word
      word.length ≤ n + 1 ∧
        ResetAwareSignalReady hpsi ring newRoot D ∧
        (D newRoot).core.erase.core.label = ⟨0, hpsi⟩ := by
  obtain ⟨k, hkpos, hkle, hresult⟩ :=
    hdone.exists_reverseMigrationSchedule_to_zero
      hpsi ring hn leader C hpsiLe
  let newRoot := groupOffset ring leader k
  let T :=
    wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
      hpsi kappa tau
  let reverseWord := pPsiProbeChasePrefix ring leader (n - k)
  let M := runLocalSchedule ring T C reverseWord
  change reverseWord.length = n - k ∧
      NoActiveDeletion M ∧
      hasUniqueLeader n
        (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig M) ∧
      (M newRoot).core.erase.core.leader = true ∧
      PPLLPpsiLeaderCreationRepair.BulletTwoFreeAwayFrom M newRoot ∧
      (M newRoot).core.erase.core.label = ⟨0, hpsi⟩ ∧
      ∀ i, (M i).core.erase.core.label =
        (C i).core.erase.core.label at hresult
  obtain ⟨hlength, hnoActive, hunique, hroot, hfree, hzero, _hlabels⟩ :=
    hresult
  have hreseed := zeroRoot_two_step_reseed_signalReady
    hpsi ring hn newRoot M hnoActive hunique hroot hfree hzero
  let D := runLocalSchedule ring T M [newRoot, newRoot]
  change ResetAwareSignalReady hpsi ring newRoot D ∧
      (D newRoot).core.erase.core.label = ⟨0, hpsi⟩ at hreseed
  refine ⟨k, hkpos, hkle, ?_⟩
  change (reverseWord ++ [newRoot, newRoot]).length ≤ n + 1 ∧
      ResetAwareSignalReady hpsi ring newRoot
        (runLocalSchedule ring T C
          (reverseWord ++ [newRoot, newRoot])) ∧
      ((runLocalSchedule ring T C
        (reverseWord ++ [newRoot, newRoot])) newRoot).core.erase.core.label =
          ⟨0, hpsi⟩
  rw [runLocalSchedule_append_generic]
  change (reverseWord ++ [newRoot, newRoot]).length ≤ n + 1 ∧
      ResetAwareSignalReady hpsi ring newRoot D ∧
      (D newRoot).core.erase.core.label = ⟨0, hpsi⟩
  refine ⟨?_, hreseed⟩
  simp only [List.length_append, List.length_cons, List.length_nil]
  rw [hlength]
  omega

set_option maxHeartbeats 2000000 in
/-- Birth-signal-transition form.  A completed first normalization, the greatest-zero reverse suffix, and two
leader-edge interactions compose to a fresh authenticated frontier rooted at
the zero-labelled leader.  The additional word after the first normalization
has length at most `n+1`. -/
theorem ResetAwareRetryDone.exists_birthSignalZero_zeroRoot_reseed
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (leader : Fin n) (C : EConfig n psi kappa tau)
    (hdone : ResetAwareRetryDone hpsi ring leader C)
    (hpsiLe : psi ≤ n) :
    ∃ k, 0 < k ∧ k ≤ n ∧
      let newRoot := groupOffset ring leader k
      let T :=
        wallSweepBirthSignalZeroPathStallTransition
          hpsi kappa tau
      let reverseWord := pPsiProbeChasePrefix ring leader (n - k)
      let word := reverseWord ++ [newRoot, newRoot]
      let D := runLocalSchedule ring T C word
      word.length ≤ n + 1 ∧
        ResetAwareRetryReady hpsi ring newRoot D ∧
        (D newRoot).core.erase.core.label = ⟨0, hpsi⟩ := by
  obtain ⟨k, hkpos, hkle, hresult⟩ :=
    hdone.exists_birthSignalZero_reverseMigrationSchedule_to_zero
      hpsi ring hn leader C hpsiLe
  let newRoot := groupOffset ring leader k
  let T :=
    wallSweepBirthSignalZeroPathStallTransition
      hpsi kappa tau
  let reverseWord := pPsiProbeChasePrefix ring leader (n - k)
  let M := runLocalSchedule ring T C reverseWord
  change reverseWord.length = n - k ∧
      NoActiveDeletion M ∧
      hasUniqueLeader n
        (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig M) ∧
      (M newRoot).core.erase.core.leader = true ∧
      PPLLPpsiLeaderCreationRepair.BulletTwoFreeAwayFrom M newRoot ∧
      (M newRoot).core.erase.core.label = ⟨0, hpsi⟩ ∧
      ∀ i, (M i).core.erase.core.label =
        (C i).core.erase.core.label at hresult
  obtain ⟨hlength, hnoActive, hunique, hroot, hfree, hzero, _hlabels⟩ :=
    hresult
  have hreseed := zeroRoot_birthSignalZero_two_step_reseed
    hpsi ring hn newRoot M hnoActive hunique hroot hfree hzero
  let D := runLocalSchedule ring T M [newRoot, newRoot]
  change ResetAwareRetryReady hpsi ring newRoot D ∧
      (D newRoot).core.erase.core.label = ⟨0, hpsi⟩ at hreseed
  refine ⟨k, hkpos, hkle, ?_⟩
  change (reverseWord ++ [newRoot, newRoot]).length ≤ n + 1 ∧
      ResetAwareRetryReady hpsi ring newRoot
        (runLocalSchedule ring T C
          (reverseWord ++ [newRoot, newRoot])) ∧
      ((runLocalSchedule ring T C
        (reverseWord ++ [newRoot, newRoot])) newRoot).core.erase.core.label =
          ⟨0, hpsi⟩
  rw [runLocalSchedule_append_generic]
  change (reverseWord ++ [newRoot, newRoot]).length ≤ n + 1 ∧
      ResetAwareRetryReady hpsi ring newRoot D ∧
      (D newRoot).core.erase.core.label = ⟨0, hpsi⟩
  refine ⟨?_, hreseed⟩
  simp only [List.length_append, List.length_cons, List.length_nil]
  rw [hlength]
  omega

set_option maxHeartbeats 2000000 in
/-- Birth-signal-transition form.  The same greatest-zero migration and two-step reseed establish the
signal-aware outer-round boundary.  The returned literal schedule has the
same `n+1` bound as the structural reseed theorem. -/
theorem ResetAwareRetryDone.exists_birthSignalZero_zeroRoot_signalReady
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (leader : Fin n) (C : EConfig n psi kappa tau)
    (hdone : ResetAwareRetryDone hpsi ring leader C)
    (hpsiLe : psi ≤ n) :
    ∃ k, 0 < k ∧ k ≤ n ∧
      let newRoot := groupOffset ring leader k
      let T :=
        wallSweepBirthSignalZeroPathStallTransition
          hpsi kappa tau
      let reverseWord := pPsiProbeChasePrefix ring leader (n - k)
      let word := reverseWord ++ [newRoot, newRoot]
      let D := runLocalSchedule ring T C word
      word.length ≤ n + 1 ∧
        ResetAwareSignalReady hpsi ring newRoot D ∧
        (D newRoot).core.erase.core.label = ⟨0, hpsi⟩ := by
  obtain ⟨k, hkpos, hkle, hresult⟩ :=
    hdone.exists_birthSignalZero_reverseMigrationSchedule_to_zero
      hpsi ring hn leader C hpsiLe
  let newRoot := groupOffset ring leader k
  let T :=
    wallSweepBirthSignalZeroPathStallTransition
      hpsi kappa tau
  let reverseWord := pPsiProbeChasePrefix ring leader (n - k)
  let M := runLocalSchedule ring T C reverseWord
  change reverseWord.length = n - k ∧
      NoActiveDeletion M ∧
      hasUniqueLeader n
        (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig M) ∧
      (M newRoot).core.erase.core.leader = true ∧
      PPLLPpsiLeaderCreationRepair.BulletTwoFreeAwayFrom M newRoot ∧
      (M newRoot).core.erase.core.label = ⟨0, hpsi⟩ ∧
      ∀ i, (M i).core.erase.core.label =
        (C i).core.erase.core.label at hresult
  obtain ⟨hlength, hnoActive, hunique, hroot, hfree, hzero, _hlabels⟩ :=
    hresult
  have hreseed := zeroRoot_birthSignalZero_two_step_reseed_signalReady
    hpsi ring hn newRoot M hnoActive hunique hroot hfree hzero
  let D := runLocalSchedule ring T M [newRoot, newRoot]
  change ResetAwareSignalReady hpsi ring newRoot D ∧
      (D newRoot).core.erase.core.label = ⟨0, hpsi⟩ at hreseed
  refine ⟨k, hkpos, hkle, ?_⟩
  change (reverseWord ++ [newRoot, newRoot]).length ≤ n + 1 ∧
      ResetAwareSignalReady hpsi ring newRoot
        (runLocalSchedule ring T C
          (reverseWord ++ [newRoot, newRoot])) ∧
      ((runLocalSchedule ring T C
        (reverseWord ++ [newRoot, newRoot])) newRoot).core.erase.core.label =
          ⟨0, hpsi⟩
  rw [runLocalSchedule_append_generic]
  change (reverseWord ++ [newRoot, newRoot]).length ≤ n + 1 ∧
      ResetAwareSignalReady hpsi ring newRoot D ∧
      (D newRoot).core.erase.core.label = ⟨0, hpsi⟩
  refine ⟨?_, hreseed⟩
  simp only [List.length_append, List.length_cons, List.length_nil]
  rw [hlength]
  omega

set_option maxHeartbeats 4000000 in
/-- Traverse a false-echo prefix while carrying the absence signal.  The
traversal either reaches the requested frontier with weakly smaller mobile
dummy rank, or stops at the first responder dummy, reseeds the same root, and
returns signal-ready at strictly smaller mobile rank. -/
theorem ResetAwareNormalizedPrefixState.exists_signal_advance_to_of_base_echo_false
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (leader : Fin n) (base current : EConfig n psi kappa tau)
    (steps target : Nat)
    (hstate : ResetAwareNormalizedPrefixState
      hpsi ring leader base current steps)
    (hfree :
      PPLLPpsiLeaderCreationRepair.BulletTwoFreeAwayFrom current leader)
    (hfrontierSignal :
      (current (groupOffset ring leader steps)).core.erase.core.signal_B =
        ⟨1, by omega⟩)
    (hsteps : steps ≤ target) (htarget : target ≤ n - 1)
    (hbaseEcho : ∀ k, steps < k → k ≤ target →
      (base (groupOffset ring leader k)).core.erase.core.echo = false) :
    ∃ (word : DetSchedule n) (D : EConfig n psi kappa tau),
      D = runLocalSchedule ring
        (wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
          hpsi kappa tau) current word ∧
      (D leader).core.erase.core.label =
        (current leader).core.erase.core.label ∧
      ((ResetAwareNormalizedPrefixState
            hpsi ring leader base D target ∧
          PPLLPpsiLeaderCreationRepair.BulletTwoFreeAwayFrom D leader ∧
          (D (groupOffset ring leader target)).core.erase.core.signal_B =
            ⟨1, by omega⟩ ∧
          clockwiseMobileDummyRank ring leader D ≤
            clockwiseMobileDummyRank ring leader current) ∨
        (ResetAwareSignalReady hpsi ring leader D ∧
          clockwiseMobileDummyRank ring leader D <
            clockwiseMobileDummyRank ring leader current)) := by
  induction target generalizing current steps with
  | zero =>
      have hzero : steps = 0 := by omega
      exact (Nat.ne_of_gt hstate.steps_pos hzero).elim
  | succ target ih =>
      by_cases hdone : steps = target + 1
      · subst steps
        refine ⟨[], current, by simp [runLocalSchedule], rfl, Or.inl ?_⟩
        exact ⟨hstate, hfree, hfrontierSignal, Nat.le_refl _⟩
      · have hstepsPrev : steps ≤ target := by omega
        have htargetPrev : target ≤ n - 1 := by omega
        obtain ⟨word, M, hM, hleaderLabelM, houtM⟩ :=
          ih (current := current) (steps := steps)
            hstate hfree hfrontierSignal hstepsPrev htargetPrev (by
              intro k hk hkt
              exact hbaseEcho k hk (by omega))
        rcases houtM with hadvance | habort
        · obtain ⟨hstateM, hfreeM, hsignalM, hrankM⟩ := hadvance
          have htargetPos : 0 < target := hstateM.steps_pos
          have htargetLt : target < n - 1 := by omega
          have hnextEcho :
              (M (groupOffset ring leader (target + 1))).core.erase.core.echo =
                false := by
            rw [hstateM.untouched_ahead (target + 1)
              (by omega) (by omega)]
            exact hbaseEcho (target + 1) (by omega) (by omega)
          let e := groupOffset ring leader target
          let T :=
            wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
              hpsi kappa tau
          let D := localStep ring T M e
          have hprogress := hstateM.next_signal_or_mobileDummyRank_lt
            hpsi ring hn leader base M target htargetLt hfreeM hsignalM
          change
            (D (groupOffset ring leader (target + 1))).core.erase.core.signal_B =
                ⟨1, by omega⟩ ∨
              ((M (groupOffset ring leader (target + 1))).core.erase.core.bullet =
                  ⟨1, by omega⟩ ∧
                clockwiseMobileDummyRank ring leader D <
                  clockwiseMobileDummyRank ring leader M) at hprogress
          rcases hprogress with hsignalD | hdummy
          · have hstateD := hstateM.step_of_echo_false
              hpsi ring hn leader base M target htargetLt hnextEcho
            change ResetAwareNormalizedPrefixState
              hpsi ring leader base D (target + 1) at hstateD
            have heBound : target < n := by omega
            have hjBound : target + 1 < n := by omega
            have heNotLeader : e ≠ leader := by
              intro heq
              have hne := groupOffset_ne_of_lt ring leader heBound
                (by omega : 0 < n) (Nat.ne_of_gt htargetPos)
              exact hne (heq.trans (groupOffset_zero_eq ring leader).symm)
            have hjNotLeader :
                groupOffset ring leader (target + 1) ≠ leader := by
              intro heq
              have hne := groupOffset_ne_of_lt ring leader hjBound
                (by omega : 0 < n) (by omega : target + 1 ≠ 0)
              exact hne (heq.trans (groupOffset_zero_eq ring leader).symm)
            have hneighbor : ring.rightNeighbor e =
                groupOffset ring leader (target + 1) := by
              simpa [e] using rightNeighbor_groupOffset ring leader target
            have hrightFollower :
                (M (ring.rightNeighbor e)).core.erase.core.leader = false := by
              rw [hneighbor]
              exact hstateM.unique_leader _ hjNotLeader
            have hfreeD := resetAwareFollower_localStep_bulletTwoFreeAwayFrom
              hpsi ring hn M e leader hstateM.no_active
                (hstateM.unique_leader e heNotLeader) hstateM.frontier_reset
                hrightFollower hfreeM heNotLeader
                (by simpa [hneighbor] using hjNotLeader)
            change PPLLPpsiLeaderCreationRepair.BulletTwoFreeAwayFrom
              D leader at hfreeD
            have hleaderFrame : D leader = M leader := by
              simp [D, T, localStep, Ne.symm heNotLeader, hneighbor,
                Ne.symm hjNotLeader]
            have hleaderLabelD :
                (D leader).core.erase.core.label =
                  (current leader).core.erase.core.label :=
              (congrArg
                (fun u : ExpiringAgentState psi kappa tau =>
                  u.core.erase.core.label) hleaderFrame).trans hleaderLabelM
            have hrankStep := hstateM.mobileDummyRank_le
              hpsi ring hn leader base M target htargetLt hfreeM
            change clockwiseMobileDummyRank ring leader D ≤
                clockwiseMobileDummyRank ring leader M at hrankStep
            refine ⟨word ++ [e], D, ?_, hleaderLabelD, Or.inl ?_⟩
            · calc
                D = runLocalSchedule ring T M [e] := rfl
                _ = runLocalSchedule ring T
                    (runLocalSchedule ring T current word) [e] := by rw [← hM]
                _ = runLocalSchedule ring T current (word ++ [e]) :=
                  (runLocalSchedule_append_generic
                    ring T current word [e]).symm
            · exact ⟨hstateD, hfreeD, hsignalD,
                Nat.le_trans hrankStep hrankM⟩
          · obtain ⟨hrightDummy, _hlocalDrop⟩ := hdummy
            have hreseed := hstateM.follower_dummy_then_signal_reseed
              hpsi ring hn leader base M target htargetLt hfreeM hrightDummy
            let F := runLocalSchedule ring T M [e, leader, leader]
            change ResetAwareSignalReady hpsi ring leader F ∧
                (F leader).core.erase.core.label =
                  (M leader).core.erase.core.label ∧
                clockwiseMobileDummyRank ring leader F <
                  clockwiseMobileDummyRank ring leader M at hreseed
            refine ⟨word ++ [e, leader, leader], F, ?_, ?_, Or.inr ?_⟩
            · calc
                F = runLocalSchedule ring T M [e, leader, leader] := rfl
                _ = runLocalSchedule ring T
                    (runLocalSchedule ring T current word)
                      [e, leader, leader] := by rw [← hM]
                _ = runLocalSchedule ring T current
                    (word ++ [e, leader, leader]) :=
                  (runLocalSchedule_append_generic ring T current word
                    [e, leader, leader]).symm
            · exact hreseed.2.1.trans hleaderLabelM
            · exact ⟨hreseed.1,
                Nat.lt_of_lt_of_le hreseed.2.2 hrankM⟩
        · exact ⟨word, M, hM, hleaderLabelM, Or.inr habort⟩

set_option maxHeartbeats 4000000 in
/-- Under the birth-signal transition, traverse a false-echo prefix while carrying the absence signal.  The
traversal either reaches the requested frontier with weakly smaller mobile
dummy rank, or stops at the first responder dummy, reseeds the same root, and
returns signal-ready at strictly smaller mobile rank. -/
theorem ResetAwareNormalizedPrefixState.exists_birthSignalZero_signal_advance_to_of_base_echo_false
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (leader : Fin n) (base current : EConfig n psi kappa tau)
    (steps target : Nat)
    (hstate : ResetAwareNormalizedPrefixState
      hpsi ring leader base current steps)
    (hfree :
      PPLLPpsiLeaderCreationRepair.BulletTwoFreeAwayFrom current leader)
    (hfrontierSignal :
      (current (groupOffset ring leader steps)).core.erase.core.signal_B =
        ⟨1, by omega⟩)
    (hsteps : steps ≤ target) (htarget : target ≤ n - 1)
    (hbaseEcho : ∀ k, steps < k → k ≤ target →
      (base (groupOffset ring leader k)).core.erase.core.echo = false) :
    ∃ (word : DetSchedule n) (D : EConfig n psi kappa tau),
      D = runLocalSchedule ring
        (wallSweepBirthSignalZeroPathStallTransition
          hpsi kappa tau) current word ∧
      (D leader).core.erase.core.label =
        (current leader).core.erase.core.label ∧
      ((ResetAwareNormalizedPrefixState
            hpsi ring leader base D target ∧
          PPLLPpsiLeaderCreationRepair.BulletTwoFreeAwayFrom D leader ∧
          (D (groupOffset ring leader target)).core.erase.core.signal_B =
            ⟨1, by omega⟩ ∧
          clockwiseMobileDummyRank ring leader D ≤
            clockwiseMobileDummyRank ring leader current) ∨
        (ResetAwareSignalReady hpsi ring leader D ∧
          clockwiseMobileDummyRank ring leader D <
            clockwiseMobileDummyRank ring leader current)) := by
  induction target generalizing current steps with
  | zero =>
      have hzero : steps = 0 := by omega
      exact (Nat.ne_of_gt hstate.steps_pos hzero).elim
  | succ target ih =>
      by_cases hdone : steps = target + 1
      · subst steps
        refine ⟨[], current, by simp [runLocalSchedule], rfl, Or.inl ?_⟩
        exact ⟨hstate, hfree, hfrontierSignal, Nat.le_refl _⟩
      · have hstepsPrev : steps ≤ target := by omega
        have htargetPrev : target ≤ n - 1 := by omega
        obtain ⟨word, M, hM, hleaderLabelM, houtM⟩ :=
          ih (current := current) (steps := steps)
            hstate hfree hfrontierSignal hstepsPrev htargetPrev (by
              intro k hk hkt
              exact hbaseEcho k hk (by omega))
        rcases houtM with hadvance | habort
        · obtain ⟨hstateM, hfreeM, hsignalM, hrankM⟩ := hadvance
          have htargetPos : 0 < target := hstateM.steps_pos
          have htargetLt : target < n - 1 := by omega
          have hnextEcho :
              (M (groupOffset ring leader (target + 1))).core.erase.core.echo =
                false := by
            rw [hstateM.untouched_ahead (target + 1)
              (by omega) (by omega)]
            exact hbaseEcho (target + 1) (by omega) (by omega)
          let e := groupOffset ring leader target
          let T :=
            wallSweepBirthSignalZeroPathStallTransition
              hpsi kappa tau
          let D := localStep ring T M e
          have hprogress := hstateM.next_birthSignalZero_signal_or_mobileDummyRank_lt
            hpsi ring hn leader base M target htargetLt hfreeM hsignalM
          change
            (D (groupOffset ring leader (target + 1))).core.erase.core.signal_B =
                ⟨1, by omega⟩ ∨
              ((M (groupOffset ring leader (target + 1))).core.erase.core.bullet =
                  ⟨1, by omega⟩ ∧
                clockwiseMobileDummyRank ring leader D <
                  clockwiseMobileDummyRank ring leader M) at hprogress
          rcases hprogress with hsignalD | hdummy
          · have hstateD := hstateM.step_birthSignalZero_of_echo_false
              hpsi ring hn leader base M target htargetLt hnextEcho
            change ResetAwareNormalizedPrefixState
              hpsi ring leader base D (target + 1) at hstateD
            have heBound : target < n := by omega
            have hjBound : target + 1 < n := by omega
            have heNotLeader : e ≠ leader := by
              intro heq
              have hne := groupOffset_ne_of_lt ring leader heBound
                (by omega : 0 < n) (Nat.ne_of_gt htargetPos)
              exact hne (heq.trans (groupOffset_zero_eq ring leader).symm)
            have hjNotLeader :
                groupOffset ring leader (target + 1) ≠ leader := by
              intro heq
              have hne := groupOffset_ne_of_lt ring leader hjBound
                (by omega : 0 < n) (by omega : target + 1 ≠ 0)
              exact hne (heq.trans (groupOffset_zero_eq ring leader).symm)
            have hneighbor : ring.rightNeighbor e =
                groupOffset ring leader (target + 1) := by
              simpa [e] using rightNeighbor_groupOffset ring leader target
            have hstepFrame :=
              hstateM.step_birthSignalZero_free_and_mobileDummyRank_le
                hpsi ring hn leader base M target htargetLt hfreeM
            change PPLLPpsiLeaderCreationRepair.BulletTwoFreeAwayFrom
                  D leader ∧
                clockwiseMobileDummyRank ring leader D ≤
                  clockwiseMobileDummyRank ring leader M at hstepFrame
            have hfreeD := hstepFrame.1
            have hleaderFrame : D leader = M leader := by
              simp [D, T, localStep, Ne.symm heNotLeader, hneighbor,
                Ne.symm hjNotLeader]
            have hleaderLabelD :
                (D leader).core.erase.core.label =
                  (current leader).core.erase.core.label :=
              (congrArg
                (fun u : ExpiringAgentState psi kappa tau =>
                  u.core.erase.core.label) hleaderFrame).trans hleaderLabelM
            have hrankStep := hstepFrame.2
            refine ⟨word ++ [e], D, ?_, hleaderLabelD, Or.inl ?_⟩
            · calc
                D = runLocalSchedule ring T M [e] := rfl
                _ = runLocalSchedule ring T
                    (runLocalSchedule ring T current word) [e] := by rw [← hM]
                _ = runLocalSchedule ring T current (word ++ [e]) :=
                  (runLocalSchedule_append_generic
                    ring T current word [e]).symm
            · exact ⟨hstateD, hfreeD, hsignalD,
                Nat.le_trans hrankStep hrankM⟩
          · obtain ⟨hrightDummy, _hlocalDrop⟩ := hdummy
            have hreseed := hstateM.follower_dummy_then_birthSignalZero_signal_reseed
              hpsi ring hn leader base M target htargetLt hfreeM hrightDummy
            let F := runLocalSchedule ring T M [e, leader, leader]
            change ResetAwareSignalReady hpsi ring leader F ∧
                (F leader).core.erase.core.label =
                  (M leader).core.erase.core.label ∧
                clockwiseMobileDummyRank ring leader F <
                  clockwiseMobileDummyRank ring leader M at hreseed
            refine ⟨word ++ [e, leader, leader], F, ?_, ?_, Or.inr ?_⟩
            · calc
                F = runLocalSchedule ring T M [e, leader, leader] := rfl
                _ = runLocalSchedule ring T
                    (runLocalSchedule ring T current word)
                      [e, leader, leader] := by rw [← hM]
                _ = runLocalSchedule ring T current
                    (word ++ [e, leader, leader]) :=
                  (runLocalSchedule_append_generic ring T current word
                    [e, leader, leader]).symm
            · exact hreseed.2.1.trans hleaderLabelM
            · exact ⟨hreseed.1,
                Nat.lt_of_lt_of_le hreseed.2.2 hrankM⟩
        · exact ⟨word, M, hM, hleaderLabelM, Or.inr habort⟩

set_option maxHeartbeats 3000000 in
/-- At echo rank zero, a signal-aware retry either reaches the predecessor and
completes the normalized closing core, or encounters a dummy and restarts the
same root at strictly smaller combined retry rank. -/
theorem resetAwareSignalRetry_zero_round
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (leader : Fin n) (C : EConfig n psi kappa tau)
    (hready : ResetAwareSignalReady hpsi ring leader C)
    (hzero : clockwiseEchoRank ring leader C = 0) :
    ∃ (word : DetSchedule n) (D : EConfig n psi kappa tau),
      D = runLocalSchedule ring
        (wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
          hpsi kappa tau) C word ∧
      (D leader).core.erase.core.label =
        (C leader).core.erase.core.label ∧
      ((ResetAwareRetryDone hpsi ring leader D ∧
          (D (groupOffset ring leader (n - 1))).core.erase.core.signal_B =
            ⟨1, by omega⟩) ∨
        (ResetAwareSignalReady hpsi ring leader D ∧
          clockwiseSignalRetryRank ring leader D <
            clockwiseSignalRetryRank ring leader C)) := by
  obtain ⟨⟨hfrontier, hfree⟩, hfirstSignal⟩ := hready
  have hstateOne := resetAwareNormalizedPrefixState_one_of_frontierAt
    hpsi ring hn leader C hfrontier
  have hoffsetOne : groupOffset ring leader 1 =
      ring.rightNeighbor leader := by
    have hnext := rightNeighbor_groupOffset ring leader 0
    rw [groupOffset_zero_eq] at hnext
    simpa using hnext.symm
  have hsignalOne :
      (C (groupOffset ring leader 1)).core.erase.core.signal_B =
        ⟨1, by omega⟩ := by
    rw [hoffsetOne]
    exact hfirstSignal
  have hbaseEcho : ∀ k, 1 < k → k ≤ n - 1 →
      (C (groupOffset ring leader k)).core.erase.core.echo = false := by
    intro k hk hkn
    exact follower_echo_false_of_clockwiseEchoRank_eq_zero
      ring leader C hzero k (by omega) (by omega)
  obtain ⟨word, D, hD, hleaderLabel, hout⟩ :=
    hstateOne.exists_signal_advance_to_of_base_echo_false
      hpsi ring hn leader C C 1 (n - 1) hfree hsignalOne
        (by omega) (by omega) hbaseEcho
  refine ⟨word, D, hD, hleaderLabel, ?_⟩
  rcases hout with hadvance | habort
  · exact Or.inl ⟨⟨C, hadvance.1, hadvance.2.1⟩,
      hadvance.2.2.1⟩
  · exact Or.inr ⟨habort.1,
      clockwiseSignalRetryRank_lt_of_mobile_lt
        ring leader C D habort.2⟩

set_option maxHeartbeats 3000000 in
/-- Under the birth-signal transition, at echo rank zero, a signal-aware retry either reaches the predecessor and
completes the normalized closing core, or encounters a dummy and restarts the
same root at strictly smaller combined retry rank. -/
theorem resetAwareSignalRetry_birthSignalZero_zero_round
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (leader : Fin n) (C : EConfig n psi kappa tau)
    (hready : ResetAwareSignalReady hpsi ring leader C)
    (hzero : clockwiseEchoRank ring leader C = 0) :
    ∃ (word : DetSchedule n) (D : EConfig n psi kappa tau),
      D = runLocalSchedule ring
        (wallSweepBirthSignalZeroPathStallTransition
          hpsi kappa tau) C word ∧
      (D leader).core.erase.core.label =
        (C leader).core.erase.core.label ∧
      ((ResetAwareRetryDone hpsi ring leader D ∧
          (D (groupOffset ring leader (n - 1))).core.erase.core.signal_B =
            ⟨1, by omega⟩) ∨
        (ResetAwareSignalReady hpsi ring leader D ∧
          clockwiseSignalRetryRank ring leader D <
            clockwiseSignalRetryRank ring leader C)) := by
  obtain ⟨⟨hfrontier, hfree⟩, hfirstSignal⟩ := hready
  have hstateOne := resetAwareNormalizedPrefixState_one_of_frontierAt
    hpsi ring hn leader C hfrontier
  have hoffsetOne : groupOffset ring leader 1 =
      ring.rightNeighbor leader := by
    have hnext := rightNeighbor_groupOffset ring leader 0
    rw [groupOffset_zero_eq] at hnext
    simpa using hnext.symm
  have hsignalOne :
      (C (groupOffset ring leader 1)).core.erase.core.signal_B =
        ⟨1, by omega⟩ := by
    rw [hoffsetOne]
    exact hfirstSignal
  have hbaseEcho : ∀ k, 1 < k → k ≤ n - 1 →
      (C (groupOffset ring leader k)).core.erase.core.echo = false := by
    intro k hk hkn
    exact follower_echo_false_of_clockwiseEchoRank_eq_zero
      ring leader C hzero k (by omega) (by omega)
  obtain ⟨word, D, hD, hleaderLabel, hout⟩ :=
    hstateOne.exists_birthSignalZero_signal_advance_to_of_base_echo_false
      hpsi ring hn leader C C 1 (n - 1) hfree hsignalOne
        (by omega) (by omega) hbaseEcho
  refine ⟨word, D, hD, hleaderLabel, ?_⟩
  rcases hout with hadvance | habort
  · exact Or.inl ⟨⟨C, hadvance.1, hadvance.2.1⟩,
      hadvance.2.2.1⟩
  · exact Or.inr ⟨habort.1,
      clockwiseSignalRetryRank_lt_of_mobile_lt
        ring leader C D habort.2⟩

set_option maxHeartbeats 2000000 in
/-- A true-echo collision followed by two interactions at the same physical
leader edge produces a fresh authenticated reset frontier.  This is the
actual restart word used after the collision, not a reseed of the
pre-collision state. -/
theorem ResetAwareNormalizedPrefixState.collision_then_two_step_reseed
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (leader : Fin n) (base current : EConfig n psi kappa tau)
    (steps : Nat)
    (hstate : ResetAwareNormalizedPrefixState
      hpsi ring leader base current steps)
    (hlt : steps < n - 1)
    (hrightEcho :
      (current (groupOffset ring leader (steps + 1))).core.erase.core.echo =
        true)
    (hfree :
      PPLLPpsiLeaderCreationRepair.BulletTwoFreeAwayFrom current leader) :
    let e := groupOffset ring leader steps
    let T :=
      wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
        hpsi kappa tau
    let D := runLocalSchedule ring T current [e, leader, leader]
    FirstBlockerEffect ring leader current D ⟨steps, hlt⟩ ∧
      PPLLPpsiLeaderCreationRepair.OutgoingResetFrontierUniqueLeaderAt
          hpsi ring D leader ∧
        PPLLPpsiLeaderCreationRepair.BulletTwoFreeAwayFrom D leader ∧
        (D leader).core.erase.core.label =
          (current leader).core.erase.core.label := by
  let e := groupOffset ring leader steps
  let j := groupOffset ring leader (steps + 1)
  let T :=
    wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
      hpsi kappa tau
  let C1 := localStep ring T current e
  have hnpos : 0 < n := by omega
  have heBound : steps < n := by omega
  have hjBound : steps + 1 < n := by omega
  have hneighbor : ring.rightNeighbor e = j := by
    simpa [e, j] using rightNeighbor_groupOffset ring leader steps
  have heNotLeader : e ≠ leader := by
    have hne := groupOffset_ne_of_lt ring leader heBound
      hnpos (Nat.ne_of_gt hstate.steps_pos)
    exact fun heq =>
      hne (heq.trans (groupOffset_zero_eq ring leader).symm)
  have hjNotLeader : j ≠ leader := by
    have hne := groupOffset_ne_of_lt ring leader hjBound
      hnpos (Nat.ne_of_gt (Nat.zero_lt_succ steps))
    exact fun heq =>
      hne (heq.trans (groupOffset_zero_eq ring leader).symm)
  have hstep := resetAwareFollower_localStep_normalizes
    hpsi ring hn current e hstate.no_active
      (hstate.unique_leader e heNotLeader) hstate.frontier_reset
      (by rw [hneighbor]; exact hstate.unique_leader j hjNotLeader)
  change ResetAwareFollowerGlobalStepFrame hpsi ring current C1 e at hstep
  have hfreeC1 := resetAwareFollower_localStep_bulletTwoFreeAwayFrom
    hpsi ring hn current e leader hstate.no_active
      (hstate.unique_leader e heNotLeader) hstate.frontier_reset
      (by rw [hneighbor]; exact hstate.unique_leader j hjNotLeader)
      hfree heNotLeader (by simpa [hneighbor] using hjNotLeader)
  change PPLLPpsiLeaderCreationRepair.BulletTwoFreeAwayFrom
    C1 leader at hfreeC1
  have hleaderC1 : (C1 leader).core.erase.core.leader = true :=
    (hstep.leader_eq leader).trans hstate.leader_alive
  have hfirstNe : ring.rightNeighbor leader ≠ leader :=
    rightNeighbor_ne_self_of_one_lt ring hn leader
  have hfirstFollowerC1 :
      (C1 (ring.rightNeighbor leader)).core.erase.core.leader = false :=
    (hstep.leader_eq (ring.rightNeighbor leader)).trans
      (hstate.unique_leader (ring.rightNeighbor leader) hfirstNe)
  have huniqueC1 : hasUniqueLeader n
      (PPLLPpsiLeaderCreationRepair.eraseExpiringConfig C1) := by
    refine ⟨leader, ?_, ?_⟩
    · change (C1 leader).core.erase.core.leader = true
      exact hleaderC1
    · intro i hi
      by_cases hine : i = leader
      · exact hine
      · change (C1 i).core.erase.core.leader = true at hi
        have hfalse := (hstep.leader_eq i).trans
          (hstate.unique_leader i hine)
        have hbad : (false : Bool) = true := hfalse.symm.trans hi
        exact (Bool.false_ne_true hbad).elim
  have hreseed := two_step_reseed_of_ready
    hpsi ring hn leader C1 hstep.no_active huniqueC1
      hleaderC1 hfirstFollowerC1 hfreeC1
  have hreseedLabel := two_step_reseed_leader_label
    hpsi ring hn leader C1 hstep.no_active huniqueC1
      hleaderC1 hfirstFollowerC1 hfreeC1
  let F := runLocalSchedule ring T C1 [leader, leader]
  have hleaderOff : C1 leader = current leader :=
    hstep.off_edge leader (Ne.symm heNotLeader) (by
      rw [hneighbor]
      exact Ne.symm hjNotLeader)
  have hleaderLabel : (F leader).core.erase.core.label =
      (current leader).core.erase.core.label :=
    hreseedLabel.trans (congrArg
      (fun u : ExpiringAgentState psi kappa tau =>
        u.core.erase.core.label) hleaderOff)
  have hoffsetOne : groupOffset ring leader 1 =
      ring.rightNeighbor leader := by
    have hnext := rightNeighbor_groupOffset ring leader 0
    rw [groupOffset_zero_eq] at hnext
    simpa using hnext.symm
  have hoffTwo : ∀ k, 1 < k → k < n →
      F (groupOffset ring leader k) =
        C1 (groupOffset ring leader k) := by
    intro k hkOne hkBound
    apply runLocalSchedule_two_same_off_edge
    · have hk0 : groupOffset ring leader k ≠
          groupOffset ring leader 0 := by
        apply groupOffset_ne_of_lt ring leader hkBound (by omega)
        omega
      simpa [groupOffset_zero_eq] using hk0
    · rw [← hoffsetOne]
      apply groupOffset_ne_of_lt ring leader hkBound (by omega)
      omega
  have hpair : ExpiringResetFollowerNormalizedOutput hpsi
      (current e, current j) (C1 e, C1 j) := by
    simpa [hneighbor] using hstep.normalized
  let t : Fin (n - 1) := ⟨steps, hlt⟩
  have hstepsOne : 1 < steps + 1 :=
    Nat.succ_lt_succ hstate.steps_pos
  have hblockerAfterFirst :
      F (groupOffset ring leader (steps + 1)) =
        C1 (groupOffset ring leader (steps + 1)) :=
    hoffTwo (steps + 1) hstepsOne hjBound
  have heffect : FirstBlockerEffect ring leader current F t := {
    blocker_present := by
      simpa [t, j] using hrightEcho
    blocker_cleared := by
      rw [hblockerAfterFirst]
      simpa [t, j] using hpair.control.right_echo_false
    higher_unchanged := by
      intro s hs
      have hsBound : s.val + 1 < n := by omega
      have hse : groupOffset ring leader (s.val + 1) ≠ e := by
        apply groupOffset_ne_of_lt ring leader hsBound heBound
        dsimp only [t] at hs
        omega
      have hsj : groupOffset ring leader (s.val + 1) ≠ j := by
        apply groupOffset_ne_of_lt ring leader hsBound hjBound
        dsimp only [t] at hs
        omega
      rw [hoffTwo (s.val + 1) (by
        dsimp only [t] at hs
        omega) hsBound]
      exact congrArg
        (fun u : ExpiringAgentState psi kappa tau =>
          u.core.erase.core.echo)
        (hstep.off_edge (groupOffset ring leader (s.val + 1))
          hse (by rwa [hneighbor])) }
  simpa [e, T, C1, F, runLocalSchedule] using
    And.intro heffect (And.intro hreseed.1
      (And.intro hreseed.2 hleaderLabel))

set_option maxHeartbeats 2000000 in
/-- Birth-signal-transition form of the live-free collision restart word. -/
theorem ResetAwareNormalizedPrefixState.collision_then_birthSignalZero_two_step_reseed
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (leader : Fin n) (base current : EConfig n psi kappa tau)
    (steps : Nat)
    (hstate : ResetAwareNormalizedPrefixState
      hpsi ring leader base current steps)
    (hlt : steps < n - 1)
    (hrightEcho :
      (current (groupOffset ring leader (steps + 1))).core.erase.core.echo =
        true)
    (hfree :
      PPLLPpsiLeaderCreationRepair.BulletTwoFreeAwayFrom current leader) :
    let e := groupOffset ring leader steps
    let T := wallSweepBirthSignalZeroPathStallTransition
      hpsi kappa tau
    let D := runLocalSchedule ring T current [e, leader, leader]
    FirstBlockerEffect ring leader current D ⟨steps, hlt⟩ ∧
      PPLLPpsiLeaderCreationRepair.OutgoingResetFrontierUniqueLeaderAt
          hpsi ring D leader ∧
        PPLLPpsiLeaderCreationRepair.BulletTwoFreeAwayFrom D leader ∧
        (D leader).core.erase.core.label =
          (current leader).core.erase.core.label := by
  let e := groupOffset ring leader steps
  let j := groupOffset ring leader (steps + 1)
  let Told :=
    wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
      hpsi kappa tau
  let Tnew := wallSweepBirthSignalZeroPathStallTransition
    hpsi kappa tau
  let C1old := localStep ring Told current e
  let Dold := runLocalSchedule ring Told current [e, leader, leader]
  let Dnew := runLocalSchedule ring Tnew current [e, leader, leader]
  have hnpos : 0 < n := by omega
  have heBound : steps < n := by omega
  have hjBound : steps + 1 < n := by omega
  have hneighbor : ring.rightNeighbor e = j := by
    simpa [e, j] using rightNeighbor_groupOffset ring leader steps
  have heNotLeader : e ≠ leader := by
    have hne := groupOffset_ne_of_lt ring leader heBound
      hnpos (Nat.ne_of_gt hstate.steps_pos)
    exact fun heq =>
      hne (heq.trans (groupOffset_zero_eq ring leader).symm)
  have hjNotLeader : j ≠ leader := by
    have hne := groupOffset_ne_of_lt ring leader hjBound
      hnpos (Nat.ne_of_gt (Nat.zero_lt_succ steps))
    exact fun heq =>
      hne (heq.trans (groupOffset_zero_eq ring leader).symm)
  have hrightFollower :
      (current (ring.rightNeighbor e)).core.erase.core.leader = false := by
    rw [hneighbor]
    exact hstate.unique_leader j hjNotLeader
  have hfreeC1 := resetAwareFollower_localStep_bulletTwoFreeAwayFrom
    hpsi ring hn current e leader hstate.no_active
      (hstate.unique_leader e heNotLeader) hstate.frontier_reset
      hrightFollower hfree heNotLeader
      (by simpa [hneighbor] using hjNotLeader)
  change PPLLPpsiLeaderCreationRepair.BulletTwoFreeAwayFrom
    C1old leader at hfreeC1
  have hfirstNe : ring.rightNeighbor leader ≠ leader :=
    rightNeighbor_ne_self_of_one_lt ring hn leader
  have hsafe :
      (C1old (ring.rightNeighbor leader)).core.erase.core.bullet =
          ⟨2, by omega⟩ →
        (C1old leader).core.erase.core.shield = true := by
    intro hlive
    exact (hfreeC1 (ring.rightNeighbor leader) hfirstNe hlive).elim
  have hD : Dnew = Dold := by
    simpa only [Dnew, Dold, Tnew, Told, e, C1old] using
      hstate.run_birthSignalZero_follower_then_two_leader_eq_of_safe
        hpsi ring hn leader base current steps hlt hsafe
  have hold := hstate.collision_then_two_step_reseed
    hpsi ring hn leader base current steps hlt hrightEcho hfree
  change FirstBlockerEffect ring leader current Dold ⟨steps, hlt⟩ ∧
      PPLLPpsiLeaderCreationRepair.OutgoingResetFrontierUniqueLeaderAt
          hpsi ring Dold leader ∧
        PPLLPpsiLeaderCreationRepair.BulletTwoFreeAwayFrom Dold leader ∧
        (Dold leader).core.erase.core.label =
          (current leader).core.erase.core.label at hold
  change FirstBlockerEffect ring leader current Dnew ⟨steps, hlt⟩ ∧
      PPLLPpsiLeaderCreationRepair.OutgoingResetFrontierUniqueLeaderAt
          hpsi ring Dnew leader ∧
        PPLLPpsiLeaderCreationRepair.BulletTwoFreeAwayFrom Dnew leader ∧
        (Dnew leader).core.erase.core.label =
          (current leader).core.erase.core.label
  rw [hD]
  exact hold

/-- Scheduler-facing form of collision restart: the three-edge retry word
returns to the exact length-one prefix invariant, retaining live-bullet
freedom at every follower. -/
theorem ResetAwareNormalizedPrefixState.collision_then_restart_state_one
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (leader : Fin n) (base current : EConfig n psi kappa tau)
    (steps : Nat)
    (hstate : ResetAwareNormalizedPrefixState
      hpsi ring leader base current steps)
    (hlt : steps < n - 1)
    (hrightEcho :
      (current (groupOffset ring leader (steps + 1))).core.erase.core.echo =
        true)
    (hfree :
      PPLLPpsiLeaderCreationRepair.BulletTwoFreeAwayFrom current leader) :
    let e := groupOffset ring leader steps
    let T :=
      wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
        hpsi kappa tau
    let D := runLocalSchedule ring T current [e, leader, leader]
    ResetAwareNormalizedPrefixState hpsi ring leader D D 1 ∧
      PPLLPpsiLeaderCreationRepair.BulletTwoFreeAwayFrom D leader := by
  have hreseed :=
    ResetAwareNormalizedPrefixState.collision_then_two_step_reseed
      hpsi ring hn leader base current steps hstate hlt hrightEcho hfree
  dsimp only at hreseed ⊢
  exact ⟨resetAwareNormalizedPrefixState_one_of_frontierAt
      hpsi ring hn leader _ hreseed.2.1,
    hreseed.2.2.1⟩

set_option maxHeartbeats 4000000 in
/-- A signal-aware round at positive echo rank either encounters an earlier
dummy or consumes the canonical first echo blocker.  In both cases it returns
to the same root with a fresh signal-aware frontier and strictly smaller
combined retry rank. -/
theorem resetAwareSignalRetry_positive_echo_round
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (leader : Fin n) (C : EConfig n psi kappa tau)
    (hready : ResetAwareSignalReady hpsi ring leader C)
    (hrank : clockwiseEchoRank ring leader C ≠ 0) :
    ∃ (word : DetSchedule n) (D : EConfig n psi kappa tau),
      D = runLocalSchedule ring
        (wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
          hpsi kappa tau) C word ∧
      ResetAwareSignalReady hpsi ring leader D ∧
      (D leader).core.erase.core.label =
        (C leader).core.erase.core.label ∧
      clockwiseSignalRetryRank ring leader D <
        clockwiseSignalRetryRank ring leader C := by
  obtain ⟨⟨hfrontier, hfree⟩, hfirstSignal⟩ := hready
  have hstateOne := resetAwareNormalizedPrefixState_one_of_frontierAt
    hpsi ring hn leader C hfrontier
  obtain ⟨_noActive, _hunique, _hleader, _hrightFollower,
      _hrightLabel, _hleftProbe, _hrightProbe,
      _hleftNeutral, _hrightNeutral, _hleftReset, _hrightReset,
      _hleftEcho, hrightEchoFalse, _hsafe⟩ := hfrontier
  obtain ⟨t, _hcanonical, hpresent, hlower⟩ :=
    exists_firstClockwiseEcho_of_rank_ne_zero ring leader C hrank
  have hoffsetOne : groupOffset ring leader 1 =
      ring.rightNeighbor leader := by
    have hnext := rightNeighbor_groupOffset ring leader 0
    rw [groupOffset_zero_eq] at hnext
    simpa using hnext.symm
  have hsignalOne :
      (C (groupOffset ring leader 1)).core.erase.core.signal_B =
        ⟨1, by omega⟩ := by
    rw [hoffsetOne]
    exact hfirstSignal
  have htPos : 0 < t.val := by
    by_cases htZero : t.val = 0
    · have hpresentFirst :
          (C (groupOffset ring leader 1)).core.erase.core.echo = true := by
        simpa [htZero] using hpresent
      have hfalseFirst :
          (C (groupOffset ring leader 1)).core.erase.core.echo = false := by
        simpa [hoffsetOne] using hrightEchoFalse
      rw [hfalseFirst] at hpresentFirst
      contradiction
    · omega
  have hbaseEcho : ∀ k, 1 < k → k ≤ t.val →
      (C (groupOffset ring leader k)).core.erase.core.echo = false := by
    intro k hk hkt
    let i : Fin (n - 1) := ⟨k - 1, by omega⟩
    have hi := hlower i (by
      dsimp only [i]
      omega)
    have hindex : i.val + 1 = k := by
      dsimp only [i]
      omega
    simpa [hindex] using hi
  obtain ⟨pref, M, hM, hleaderLabelM, houtM⟩ :=
    hstateOne.exists_signal_advance_to_of_base_echo_false
      hpsi ring hn leader C C 1 t.val hfree hsignalOne
        (by omega) (by omega) hbaseEcho
  rcases houtM with hadvance | habort
  · obtain ⟨hstateM, hfreeM, _hsignalM, hmobileM⟩ := hadvance
    have hblockerM :
        (M (groupOffset ring leader (t.val + 1))).core.erase.core.echo =
          true := by
      rw [hstateM.untouched_ahead (t.val + 1) (by omega) (by omega)]
      exact hpresent
    let T :=
      wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
        hpsi kappa tau
    let suffix : DetSchedule n :=
      [groupOffset ring leader t.val, leader, leader]
    let D := runLocalSchedule ring T M suffix
    have hcollision : FirstBlockerEffect ring leader M D t ∧
        PPLLPpsiLeaderCreationRepair.OutgoingResetFrontierUniqueLeaderAt
            hpsi ring D leader ∧
          PPLLPpsiLeaderCreationRepair.BulletTwoFreeAwayFrom D leader ∧
          (D leader).core.erase.core.label =
            (M leader).core.erase.core.label := by
      simpa [T, suffix, D] using
        hstateM.collision_then_two_step_reseed
          hpsi ring hn leader C M t.val t.isLt hblockerM hfreeM
    have heffect : FirstBlockerEffect ring leader C D t := {
      blocker_present := hpresent
      blocker_cleared := hcollision.1.blocker_cleared
      higher_unchanged := by
        intro s hts
        rw [hcollision.1.higher_unchanged s hts]
        have hsite := hstateM.untouched_ahead (s.val + 1)
          (by omega) (by omega)
        exact congrArg
          (fun u : ExpiringAgentState psi kappa tau =>
            u.core.erase.core.echo) hsite }
    have hsignalReseed := hstateM.follower_then_signal_reseed
      hpsi ring hn leader C M t.val t.isLt hfreeM
    change ResetAwareSignalReady hpsi ring leader D ∧
        (D leader).core.erase.core.label =
          (M leader).core.erase.core.label ∧
        clockwiseMobileDummyRank ring leader D ≤
          clockwiseMobileDummyRank ring leader M at hsignalReseed
    have hmobileDC : clockwiseMobileDummyRank ring leader D ≤
        clockwiseMobileDummyRank ring leader C :=
      Nat.le_trans hsignalReseed.2.2 hmobileM
    have hcombined := clockwiseSignalRetryRank_lt_of_mobile_le_echo_lt
      ring leader C D hmobileDC heffect.rank_lt
    let word := pref ++ suffix
    refine ⟨word, D, ?_, hsignalReseed.1,
      hsignalReseed.2.1.trans hleaderLabelM, hcombined⟩
    calc
      D = runLocalSchedule ring T M suffix := rfl
      _ = runLocalSchedule ring T
          (runLocalSchedule ring T C pref) suffix := by rw [← hM]
      _ = runLocalSchedule ring T C (pref ++ suffix) :=
        (runLocalSchedule_append_generic ring T C pref suffix).symm
      _ = runLocalSchedule ring T C word := by rfl
  · exact ⟨pref, M, hM, habort.1, hleaderLabelM,
      clockwiseSignalRetryRank_lt_of_mobile_lt
        ring leader C M habort.2⟩

set_option maxHeartbeats 4000000 in
/-- Strong induction on the combined echo/mobile rank turns a signal-aware
zero-labelled root into the exact rooted closing boundary.  Every recursive
call keeps the same physical root. -/
theorem exists_resetAwareRootedClosingSchedule_of_signalRank
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (leader : Fin n) (rank : Nat) (C : EConfig n psi kappa tau)
    (hready : ResetAwareSignalReady hpsi ring leader C)
    (hzero : (C leader).core.erase.core.label = ⟨0, hpsi⟩)
    (hrank : clockwiseSignalRetryRank ring leader C = rank) :
    ∃ (word : DetSchedule n) (D : EConfig n psi kappa tau),
      D = runLocalSchedule ring
        (wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
          hpsi kappa tau) C word ∧
      ResetAwareRootedClosingReady hpsi ring leader D := by
  revert C
  induction rank using Nat.strongRecOn with
  | ind rank ih =>
      intro C hready hzero hrank
      by_cases hechoZero : clockwiseEchoRank ring leader C = 0
      · obtain ⟨pref, C1, hC1, hroundLabel, hout⟩ :=
          resetAwareSignalRetry_zero_round
            hpsi ring hn leader C hready hechoZero
        rcases hout with hdone | hretry
        · have hrooted : ResetAwareRootedClosingReady
              hpsi ring leader C1 := {
            toResetAwareClosingCore :=
              hdone.1.toClosingCore hpsi ring hn leader C1
            leader_zero := hroundLabel.trans hzero
            predecessor_signal_one := hdone.2 }
          exact ⟨pref, C1, hC1, hrooted⟩
        · have hlt : clockwiseSignalRetryRank ring leader C1 < rank := by
            calc
              clockwiseSignalRetryRank ring leader C1 <
                  clockwiseSignalRetryRank ring leader C := hretry.2
              _ = rank := hrank
          have hzeroC1 : (C1 leader).core.erase.core.label =
              ⟨0, hpsi⟩ := hroundLabel.trans hzero
          obtain ⟨tail, D, hD, hrooted⟩ :=
            ih (clockwiseSignalRetryRank ring leader C1) hlt
              C1 hretry.1 hzeroC1 rfl
          let T :=
            wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
              hpsi kappa tau
          let word := pref ++ tail
          refine ⟨word, D, ?_, hrooted⟩
          calc
            D = runLocalSchedule ring T C1 tail := hD
            _ = runLocalSchedule ring T
                (runLocalSchedule ring T C pref) tail := by rw [← hC1]
            _ = runLocalSchedule ring T C (pref ++ tail) :=
              (runLocalSchedule_append_generic ring T C pref tail).symm
            _ = runLocalSchedule ring T C word := by rfl
      · obtain ⟨pref, C1, hC1, hreadyC1, hroundLabel, hdrop⟩ :=
          resetAwareSignalRetry_positive_echo_round
            hpsi ring hn leader C hready hechoZero
        have hlt : clockwiseSignalRetryRank ring leader C1 < rank := by
          calc
            clockwiseSignalRetryRank ring leader C1 <
                clockwiseSignalRetryRank ring leader C := hdrop
            _ = rank := hrank
        have hzeroC1 : (C1 leader).core.erase.core.label =
            ⟨0, hpsi⟩ := hroundLabel.trans hzero
        obtain ⟨tail, D, hD, hrooted⟩ :=
          ih (clockwiseSignalRetryRank ring leader C1) hlt
            C1 hreadyC1 hzeroC1 rfl
        let T :=
          wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
            hpsi kappa tau
        let word := pref ++ tail
        refine ⟨word, D, ?_, hrooted⟩
        calc
          D = runLocalSchedule ring T C1 tail := hD
          _ = runLocalSchedule ring T
              (runLocalSchedule ring T C pref) tail := by rw [← hC1]
          _ = runLocalSchedule ring T C (pref ++ tail) :=
            (runLocalSchedule_append_generic ring T C pref tail).symm
          _ = runLocalSchedule ring T C word := by rfl

/-- Public signal-aware scheduler at the configuration's actual combined
retry rank. -/
theorem exists_resetAwareRootedClosingSchedule
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (leader : Fin n) (C : EConfig n psi kappa tau)
    (hready : ResetAwareSignalReady hpsi ring leader C)
    (hzero : (C leader).core.erase.core.label = ⟨0, hpsi⟩) :
    ∃ (word : DetSchedule n) (D : EConfig n psi kappa tau),
      D = runLocalSchedule ring
        (wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
          hpsi kappa tau) C word ∧
      ResetAwareRootedClosingReady hpsi ring leader D := by
  exact exists_resetAwareRootedClosingSchedule_of_signalRank
    hpsi ring hn leader (clockwiseSignalRetryRank ring leader C)
      C hready hzero rfl

set_option maxHeartbeats 4000000 in
/-- Under the birth-signal transition, a signal-aware round at positive echo rank either encounters an earlier
dummy or consumes the canonical first echo blocker.  In both cases it returns
to the same root with a fresh signal-aware frontier and strictly smaller
combined retry rank. -/
theorem resetAwareSignalRetry_birthSignalZero_positive_echo_round
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (leader : Fin n) (C : EConfig n psi kappa tau)
    (hready : ResetAwareSignalReady hpsi ring leader C)
    (hrank : clockwiseEchoRank ring leader C ≠ 0) :
    ∃ (word : DetSchedule n) (D : EConfig n psi kappa tau),
      D = runLocalSchedule ring
        (wallSweepBirthSignalZeroPathStallTransition
          hpsi kappa tau) C word ∧
      ResetAwareSignalReady hpsi ring leader D ∧
      (D leader).core.erase.core.label =
        (C leader).core.erase.core.label ∧
      clockwiseSignalRetryRank ring leader D <
        clockwiseSignalRetryRank ring leader C := by
  obtain ⟨⟨hfrontier, hfree⟩, hfirstSignal⟩ := hready
  have hstateOne := resetAwareNormalizedPrefixState_one_of_frontierAt
    hpsi ring hn leader C hfrontier
  obtain ⟨_noActive, _hunique, _hleader, _hrightFollower,
      _hrightLabel, _hleftProbe, _hrightProbe,
      _hleftNeutral, _hrightNeutral, _hleftReset, _hrightReset,
      _hleftEcho, hrightEchoFalse, _hsafe⟩ := hfrontier
  obtain ⟨t, _hcanonical, hpresent, hlower⟩ :=
    exists_firstClockwiseEcho_of_rank_ne_zero ring leader C hrank
  have hoffsetOne : groupOffset ring leader 1 =
      ring.rightNeighbor leader := by
    have hnext := rightNeighbor_groupOffset ring leader 0
    rw [groupOffset_zero_eq] at hnext
    simpa using hnext.symm
  have hsignalOne :
      (C (groupOffset ring leader 1)).core.erase.core.signal_B =
        ⟨1, by omega⟩ := by
    rw [hoffsetOne]
    exact hfirstSignal
  have htPos : 0 < t.val := by
    by_cases htZero : t.val = 0
    · have hpresentFirst :
          (C (groupOffset ring leader 1)).core.erase.core.echo = true := by
        simpa [htZero] using hpresent
      have hfalseFirst :
          (C (groupOffset ring leader 1)).core.erase.core.echo = false := by
        simpa [hoffsetOne] using hrightEchoFalse
      rw [hfalseFirst] at hpresentFirst
      contradiction
    · omega
  have hbaseEcho : ∀ k, 1 < k → k ≤ t.val →
      (C (groupOffset ring leader k)).core.erase.core.echo = false := by
    intro k hk hkt
    let i : Fin (n - 1) := ⟨k - 1, by omega⟩
    have hi := hlower i (by
      dsimp only [i]
      omega)
    have hindex : i.val + 1 = k := by
      dsimp only [i]
      omega
    simpa [hindex] using hi
  obtain ⟨pref, M, hM, hleaderLabelM, houtM⟩ :=
    hstateOne.exists_birthSignalZero_signal_advance_to_of_base_echo_false
      hpsi ring hn leader C C 1 t.val hfree hsignalOne
        (by omega) (by omega) hbaseEcho
  rcases houtM with hadvance | habort
  · obtain ⟨hstateM, hfreeM, _hsignalM, hmobileM⟩ := hadvance
    have hblockerM :
        (M (groupOffset ring leader (t.val + 1))).core.erase.core.echo =
          true := by
      rw [hstateM.untouched_ahead (t.val + 1) (by omega) (by omega)]
      exact hpresent
    let T :=
      wallSweepBirthSignalZeroPathStallTransition
        hpsi kappa tau
    let suffix : DetSchedule n :=
      [groupOffset ring leader t.val, leader, leader]
    let D := runLocalSchedule ring T M suffix
    have hcollision : FirstBlockerEffect ring leader M D t ∧
        PPLLPpsiLeaderCreationRepair.OutgoingResetFrontierUniqueLeaderAt
            hpsi ring D leader ∧
          PPLLPpsiLeaderCreationRepair.BulletTwoFreeAwayFrom D leader ∧
          (D leader).core.erase.core.label =
            (M leader).core.erase.core.label := by
      simpa [T, suffix, D] using
        hstateM.collision_then_birthSignalZero_two_step_reseed
          hpsi ring hn leader C M t.val t.isLt hblockerM hfreeM
    have heffect : FirstBlockerEffect ring leader C D t := {
      blocker_present := hpresent
      blocker_cleared := hcollision.1.blocker_cleared
      higher_unchanged := by
        intro s hts
        rw [hcollision.1.higher_unchanged s hts]
        have hsite := hstateM.untouched_ahead (s.val + 1)
          (by omega) (by omega)
        exact congrArg
          (fun u : ExpiringAgentState psi kappa tau =>
            u.core.erase.core.echo) hsite }
    have hsignalReseed := hstateM.follower_then_birthSignalZero_signal_reseed
      hpsi ring hn leader C M t.val t.isLt hfreeM
    change ResetAwareSignalReady hpsi ring leader D ∧
        (D leader).core.erase.core.label =
          (M leader).core.erase.core.label ∧
        clockwiseMobileDummyRank ring leader D ≤
          clockwiseMobileDummyRank ring leader M at hsignalReseed
    have hmobileDC : clockwiseMobileDummyRank ring leader D ≤
        clockwiseMobileDummyRank ring leader C :=
      Nat.le_trans hsignalReseed.2.2 hmobileM
    have hcombined := clockwiseSignalRetryRank_lt_of_mobile_le_echo_lt
      ring leader C D hmobileDC heffect.rank_lt
    let word := pref ++ suffix
    refine ⟨word, D, ?_, hsignalReseed.1,
      hsignalReseed.2.1.trans hleaderLabelM, hcombined⟩
    calc
      D = runLocalSchedule ring T M suffix := rfl
      _ = runLocalSchedule ring T
          (runLocalSchedule ring T C pref) suffix := by rw [← hM]
      _ = runLocalSchedule ring T C (pref ++ suffix) :=
        (runLocalSchedule_append_generic ring T C pref suffix).symm
      _ = runLocalSchedule ring T C word := by rfl
  · exact ⟨pref, M, hM, habort.1, hleaderLabelM,
      clockwiseSignalRetryRank_lt_of_mobile_lt
        ring leader C M habort.2⟩

set_option maxHeartbeats 4000000 in
/-- Birth-signal-transition strong induction on the combined echo/mobile rank turns a signal-aware
zero-labelled root into the exact rooted closing boundary.  Every recursive
call keeps the same physical root. -/
theorem exists_resetAwareRootedBirthSignalZeroClosingSchedule_of_signalRank
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (leader : Fin n) (rank : Nat) (C : EConfig n psi kappa tau)
    (hready : ResetAwareSignalReady hpsi ring leader C)
    (hzero : (C leader).core.erase.core.label = ⟨0, hpsi⟩)
    (hrank : clockwiseSignalRetryRank ring leader C = rank) :
    ∃ (word : DetSchedule n) (D : EConfig n psi kappa tau),
      D = runLocalSchedule ring
        (wallSweepBirthSignalZeroPathStallTransition
          hpsi kappa tau) C word ∧
      ResetAwareRootedClosingReady hpsi ring leader D := by
  revert C
  induction rank using Nat.strongRecOn with
  | ind rank ih =>
      intro C hready hzero hrank
      by_cases hechoZero : clockwiseEchoRank ring leader C = 0
      · obtain ⟨pref, C1, hC1, hroundLabel, hout⟩ :=
          resetAwareSignalRetry_birthSignalZero_zero_round
            hpsi ring hn leader C hready hechoZero
        rcases hout with hdone | hretry
        · have hrooted : ResetAwareRootedClosingReady
              hpsi ring leader C1 := {
            toResetAwareClosingCore :=
              hdone.1.toClosingCore hpsi ring hn leader C1
            leader_zero := hroundLabel.trans hzero
            predecessor_signal_one := hdone.2 }
          exact ⟨pref, C1, hC1, hrooted⟩
        · have hlt : clockwiseSignalRetryRank ring leader C1 < rank := by
            calc
              clockwiseSignalRetryRank ring leader C1 <
                  clockwiseSignalRetryRank ring leader C := hretry.2
              _ = rank := hrank
          have hzeroC1 : (C1 leader).core.erase.core.label =
              ⟨0, hpsi⟩ := hroundLabel.trans hzero
          obtain ⟨tail, D, hD, hrooted⟩ :=
            ih (clockwiseSignalRetryRank ring leader C1) hlt
              C1 hretry.1 hzeroC1 rfl
          let T :=
            wallSweepBirthSignalZeroPathStallTransition
              hpsi kappa tau
          let word := pref ++ tail
          refine ⟨word, D, ?_, hrooted⟩
          calc
            D = runLocalSchedule ring T C1 tail := hD
            _ = runLocalSchedule ring T
                (runLocalSchedule ring T C pref) tail := by rw [← hC1]
            _ = runLocalSchedule ring T C (pref ++ tail) :=
              (runLocalSchedule_append_generic ring T C pref tail).symm
            _ = runLocalSchedule ring T C word := by rfl
      · obtain ⟨pref, C1, hC1, hreadyC1, hroundLabel, hdrop⟩ :=
          resetAwareSignalRetry_birthSignalZero_positive_echo_round
            hpsi ring hn leader C hready hechoZero
        have hlt : clockwiseSignalRetryRank ring leader C1 < rank := by
          calc
            clockwiseSignalRetryRank ring leader C1 <
                clockwiseSignalRetryRank ring leader C := hdrop
            _ = rank := hrank
        have hzeroC1 : (C1 leader).core.erase.core.label =
            ⟨0, hpsi⟩ := hroundLabel.trans hzero
        obtain ⟨tail, D, hD, hrooted⟩ :=
          ih (clockwiseSignalRetryRank ring leader C1) hlt
            C1 hreadyC1 hzeroC1 rfl
        let T :=
          wallSweepBirthSignalZeroPathStallTransition
            hpsi kappa tau
        let word := pref ++ tail
        refine ⟨word, D, ?_, hrooted⟩
        calc
          D = runLocalSchedule ring T C1 tail := hD
          _ = runLocalSchedule ring T
              (runLocalSchedule ring T C pref) tail := by rw [← hC1]
          _ = runLocalSchedule ring T C (pref ++ tail) :=
            (runLocalSchedule_append_generic ring T C pref tail).symm
          _ = runLocalSchedule ring T C word := by rfl

/-- Public birth-signal-transition signal-aware scheduler at the configuration's actual combined
retry rank. -/
theorem exists_resetAwareRootedBirthSignalZeroClosingSchedule
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (leader : Fin n) (C : EConfig n psi kappa tau)
    (hready : ResetAwareSignalReady hpsi ring leader C)
    (hzero : (C leader).core.erase.core.label = ⟨0, hpsi⟩) :
    ∃ (word : DetSchedule n) (D : EConfig n psi kappa tau),
      D = runLocalSchedule ring
        (wallSweepBirthSignalZeroPathStallTransition
          hpsi kappa tau) C word ∧
      ResetAwareRootedClosingReady hpsi ring leader D := by
  exact exists_resetAwareRootedBirthSignalZeroClosingSchedule_of_signalRank
    hpsi ring hn leader (clockwiseSignalRetryRank ring leader C)
      C hready hzero rfl

set_option maxHeartbeats 3000000 in
/-- One positive-rank reset-aware round follows the canonical first blocker,
consumes it, and uses two named leader interactions to restart at a strictly
smaller follower-echo rank.  The returned schedule is literal; its prefix
crosses only the lower false echoes certified by `firstTrue?`. -/
theorem resetAwareRetry_failed_round
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (leader : Fin n) (C : EConfig n psi kappa tau)
    (hready : ResetAwareRetryReady hpsi ring leader C)
    (hrank : clockwiseEchoRank ring leader C ≠ 0) :
    ∃ (t : Fin (n - 1)) (word : DetSchedule n)
      (D : EConfig n psi kappa tau),
      firstTrue? (clockwiseFollowerEchoBits ring leader C) = some t ∧
      D = runLocalSchedule ring
        (wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
          hpsi kappa tau) C word ∧
      word.length ≤ n ∧
      ResetAwareRetryReady hpsi ring leader D ∧
      clockwiseEchoRank ring leader D <
        clockwiseEchoRank ring leader C ∧
      (D leader).core.erase.core.label =
        (C leader).core.erase.core.label := by
  obtain ⟨hfrontier, hfree⟩ := hready
  have hstateOne := resetAwareNormalizedPrefixState_one_of_frontierAt
    hpsi ring hn leader C hfrontier
  obtain ⟨_hnoActive, _hunique, _hleader, _hrightFollower,
      _hrightLabel, _hleftProbe, _hrightProbe,
      _hleftNeutral, _hrightNeutral, _hleftReset, _hrightReset,
      _hleftEcho, hrightEchoFalse, _hsafe⟩ := hfrontier
  obtain ⟨t, hcanonical, hpresent, hlower⟩ :=
    exists_firstClockwiseEcho_of_rank_ne_zero ring leader C hrank
  have hoffsetOne : groupOffset ring leader 1 =
      ring.rightNeighbor leader := by
    have hnext := rightNeighbor_groupOffset ring leader 0
    rw [groupOffset_zero_eq] at hnext
    simpa using hnext.symm
  have htPos : 0 < t.val := by
    by_cases htZero : t.val = 0
    · have hpresentFirst :
          (C (groupOffset ring leader 1)).core.erase.core.echo = true := by
        simpa [htZero] using hpresent
      have hfalseFirst :
          (C (groupOffset ring leader 1)).core.erase.core.echo = false := by
        simpa [hoffsetOne] using hrightEchoFalse
      rw [hfalseFirst] at hpresentFirst
      contradiction
    · omega
  have hbaseEcho : ∀ k, 1 < k → k ≤ t.val →
      (C (groupOffset ring leader k)).core.erase.core.echo = false := by
    intro k hk hkt
    let i : Fin (n - 1) := ⟨k - 1, by omega⟩
    have hi := hlower i (by
      dsimp only [i]
      omega)
    have hindex : i.val + 1 = k := by
      dsimp only [i]
      omega
    simpa [hindex] using hi
  obtain ⟨pref, M, hM, hprefLength, hstateM, hfreeM,
      hleaderLabelM⟩ :=
    ResetAwareNormalizedPrefixState.exists_advance_to_of_base_echo_false
      hpsi ring hn leader C C 1 t.val hstateOne hfree
        (by omega) (by omega) hbaseEcho
  have hblockerM :
      (M (groupOffset ring leader (t.val + 1))).core.erase.core.echo =
        true := by
    rw [hstateM.untouched_ahead (t.val + 1) (by omega) (by omega)]
    exact hpresent
  let T :=
    wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
      hpsi kappa tau
  let suffix : DetSchedule n :=
    [groupOffset ring leader t.val, leader, leader]
  let D := runLocalSchedule ring T M suffix
  have hcollision :
      FirstBlockerEffect ring leader M D t ∧
        PPLLPpsiLeaderCreationRepair.OutgoingResetFrontierUniqueLeaderAt
            hpsi ring D leader ∧
          PPLLPpsiLeaderCreationRepair.BulletTwoFreeAwayFrom D leader ∧
          (D leader).core.erase.core.label =
            (M leader).core.erase.core.label := by
    simpa [T, suffix, D] using
      ResetAwareNormalizedPrefixState.collision_then_two_step_reseed
        hpsi ring hn leader C M t.val hstateM t.isLt hblockerM hfreeM
  have heffect : FirstBlockerEffect ring leader C D t := {
    blocker_present := hpresent
    blocker_cleared := hcollision.1.blocker_cleared
    higher_unchanged := by
      intro s hts
      rw [hcollision.1.higher_unchanged s hts]
      have hsite := hstateM.untouched_ahead (s.val + 1)
        (by omega) (by omega)
      exact congrArg
        (fun u : ExpiringAgentState psi kappa tau =>
          u.core.erase.core.echo) hsite }
  let word := pref ++ suffix
  refine ⟨t, word, D, hcanonical, ?_, ?_,
    ⟨hcollision.2.1, hcollision.2.2.1⟩, heffect.rank_lt,
    hcollision.2.2.2.trans hleaderLabelM⟩
  · calc
      D = runLocalSchedule ring T M suffix := rfl
      _ = runLocalSchedule ring T
          (runLocalSchedule ring T C pref) suffix := by rw [← hM]
      _ = runLocalSchedule ring T C (pref ++ suffix) :=
        (runLocalSchedule_append_generic ring T C pref suffix).symm
      _ = runLocalSchedule ring T C word := by rfl
  · simp only [word, suffix, List.length_append, List.length_cons,
      List.length_nil]
    omega

set_option maxHeartbeats 2000000 in
/-- At rank zero every untouched follower echo is false, so the authenticated
frontier crosses the entire remaining non-wrap prefix without a collision.
This is the terminal branch of the reset-aware rank recursion. -/
theorem resetAwareRetry_zero_round
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (leader : Fin n) (C : EConfig n psi kappa tau)
    (hready : ResetAwareRetryReady hpsi ring leader C)
    (hzero : clockwiseEchoRank ring leader C = 0) :
    ∃ (word : DetSchedule n) (D : EConfig n psi kappa tau),
      D = runLocalSchedule ring
        (wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
          hpsi kappa tau) C word ∧
      word.length = n - 2 ∧
      ResetAwareRetryDone hpsi ring leader D ∧
      (D leader).core.erase.core.label =
        (C leader).core.erase.core.label := by
  obtain ⟨hfrontier, hfree⟩ := hready
  have hstateOne := resetAwareNormalizedPrefixState_one_of_frontierAt
    hpsi ring hn leader C hfrontier
  have hbaseEcho : ∀ k, 1 < k → k ≤ n - 1 →
      (C (groupOffset ring leader k)).core.erase.core.echo = false := by
    intro k hk hkn
    exact follower_echo_false_of_clockwiseEchoRank_eq_zero
      ring leader C hzero k (by omega) (by omega)
  obtain ⟨word, D, hD, hwordLength, hstateD, hfreeD,
      hleaderLabelD⟩ :=
    ResetAwareNormalizedPrefixState.exists_advance_to_of_base_echo_false
      hpsi ring hn leader C C 1 (n - 1) hstateOne hfree
        (by omega) (by omega) hbaseEcho
  refine ⟨word, D, hD, ?_, ⟨C, hstateD, hfreeD⟩,
    hleaderLabelD⟩
  omega

set_option maxHeartbeats 3000000 in
/-- Strong induction on the actual follower-echo rank constructs a complete
literal reset-aware retry schedule.  Each failed round costs at most `n`
interactions and strictly decreases rank; the terminal pass costs `n - 2`. -/
theorem exists_resetAwareRetrySchedule_of_rank
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (leader : Fin n) (rank : Nat) (C : EConfig n psi kappa tau)
    (hready : ResetAwareRetryReady hpsi ring leader C)
    (hrank : clockwiseEchoRank ring leader C = rank) :
    ∃ (word : DetSchedule n) (D : EConfig n psi kappa tau),
      D = runLocalSchedule ring
        (wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
          hpsi kappa tau) C word ∧
      word.length ≤ n * rank + (n - 2) ∧
      ResetAwareRetryDone hpsi ring leader D ∧
      (D leader).core.erase.core.label =
        (C leader).core.erase.core.label := by
  revert C
  induction rank using Nat.strongRecOn with
  | ind rank ih =>
      intro C hready hrank
      by_cases hz : rank = 0
      · have hzero : clockwiseEchoRank ring leader C = 0 :=
          hrank.trans hz
        obtain ⟨word, D, hD, hwordLength, hdone,
            hleaderLabel⟩ :=
          resetAwareRetry_zero_round
            hpsi ring hn leader C hready hzero
        refine ⟨word, D, hD, ?_, hdone, hleaderLabel⟩
        rw [hwordLength, hz]
        simp
      · have hactualNe : clockwiseEchoRank ring leader C ≠ 0 := by
          intro hzero
          apply hz
          exact hrank.symm.trans hzero
        obtain ⟨_t, pref, C1, _hcanonical, hC1, hprefLength,
            hready1, hdrop, hroundLabel⟩ :=
          resetAwareRetry_failed_round
            hpsi ring hn leader C hready hactualNe
        have hlt : clockwiseEchoRank ring leader C1 < rank := by
          calc
            clockwiseEchoRank ring leader C1 <
                clockwiseEchoRank ring leader C := hdrop
            _ = rank := hrank
        obtain ⟨tail, D, hD, htailLength, hdone,
            htailLabel⟩ :=
          ih (clockwiseEchoRank ring leader C1) hlt C1 hready1 rfl
        let T :=
          wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
            hpsi kappa tau
        let word := pref ++ tail
        refine ⟨word, D, ?_, ?_, hdone,
          htailLabel.trans hroundLabel⟩
        · calc
            D = runLocalSchedule ring T C1 tail := hD
            _ = runLocalSchedule ring T
                (runLocalSchedule ring T C pref) tail := by rw [← hC1]
            _ = runLocalSchedule ring T C (pref ++ tail) :=
              (runLocalSchedule_append_generic ring T C pref tail).symm
            _ = runLocalSchedule ring T C word := by rfl
        · have hsuccRank :
              clockwiseEchoRank ring leader C1 + 1 ≤ rank := by omega
          have hmul :
              n * (clockwiseEchoRank ring leader C1 + 1) ≤ n * rank :=
            Nat.mul_le_mul_left n hsuccRank
          simp only [word, List.length_append]
          calc
            pref.length + tail.length ≤
                n + (n * clockwiseEchoRank ring leader C1 + (n - 2)) :=
              Nat.add_le_add hprefLength htailLength
            _ = n * (clockwiseEchoRank ring leader C1 + 1) + (n - 2) := by
              rw [Nat.mul_add, Nat.mul_one]
              omega
            _ ≤ n * rank + (n - 2) :=
              Nat.add_le_add_right hmul (n - 2)

/-- Public reset-aware scheduler at the configuration's actual echo rank. -/
theorem exists_resetAwareRetrySchedule
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (leader : Fin n) (C : EConfig n psi kappa tau)
    (hready : ResetAwareRetryReady hpsi ring leader C) :
    ∃ (word : DetSchedule n) (D : EConfig n psi kappa tau),
      D = runLocalSchedule ring
        (wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
          hpsi kappa tau) C word ∧
      word.length ≤
        n * clockwiseEchoRank ring leader C + (n - 2) ∧
      ResetAwareRetryDone hpsi ring leader D ∧
      (D leader).core.erase.core.label =
        (C leader).core.erase.core.label := by
  exact exists_resetAwareRetrySchedule_of_rank
    hpsi ring hn leader (clockwiseEchoRank ring leader C) C hready rfl

set_option maxHeartbeats 3000000 in
/-- Birth-signal-transition form of one positive-rank reset-aware round follows the canonical first blocker,
consumes it, and uses two named leader interactions to restart at a strictly
smaller follower-echo rank.  The returned schedule is literal; its prefix
crosses only the lower false echoes certified by `firstTrue?`. -/
theorem resetAwareRetry_birthSignalZero_failed_round
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (leader : Fin n) (C : EConfig n psi kappa tau)
    (hready : ResetAwareRetryReady hpsi ring leader C)
    (hrank : clockwiseEchoRank ring leader C ≠ 0) :
    ∃ (t : Fin (n - 1)) (word : DetSchedule n)
      (D : EConfig n psi kappa tau),
      firstTrue? (clockwiseFollowerEchoBits ring leader C) = some t ∧
      D = runLocalSchedule ring
        (wallSweepBirthSignalZeroPathStallTransition
          hpsi kappa tau) C word ∧
      word.length ≤ n ∧
      ResetAwareRetryReady hpsi ring leader D ∧
      clockwiseEchoRank ring leader D <
        clockwiseEchoRank ring leader C ∧
      (D leader).core.erase.core.label =
        (C leader).core.erase.core.label := by
  obtain ⟨hfrontier, hfree⟩ := hready
  have hstateOne := resetAwareNormalizedPrefixState_one_of_frontierAt
    hpsi ring hn leader C hfrontier
  obtain ⟨_hnoActive, _hunique, _hleader, _hrightFollower,
      _hrightLabel, _hleftProbe, _hrightProbe,
      _hleftNeutral, _hrightNeutral, _hleftReset, _hrightReset,
      _hleftEcho, hrightEchoFalse, _hsafe⟩ := hfrontier
  obtain ⟨t, hcanonical, hpresent, hlower⟩ :=
    exists_firstClockwiseEcho_of_rank_ne_zero ring leader C hrank
  have hoffsetOne : groupOffset ring leader 1 =
      ring.rightNeighbor leader := by
    have hnext := rightNeighbor_groupOffset ring leader 0
    rw [groupOffset_zero_eq] at hnext
    simpa using hnext.symm
  have htPos : 0 < t.val := by
    by_cases htZero : t.val = 0
    · have hpresentFirst :
          (C (groupOffset ring leader 1)).core.erase.core.echo = true := by
        simpa [htZero] using hpresent
      have hfalseFirst :
          (C (groupOffset ring leader 1)).core.erase.core.echo = false := by
        simpa [hoffsetOne] using hrightEchoFalse
      rw [hfalseFirst] at hpresentFirst
      contradiction
    · omega
  have hbaseEcho : ∀ k, 1 < k → k ≤ t.val →
      (C (groupOffset ring leader k)).core.erase.core.echo = false := by
    intro k hk hkt
    let i : Fin (n - 1) := ⟨k - 1, by omega⟩
    have hi := hlower i (by
      dsimp only [i]
      omega)
    have hindex : i.val + 1 = k := by
      dsimp only [i]
      omega
    simpa [hindex] using hi
  obtain ⟨pref, M, hM, hprefLength, hstateM, hfreeM,
      hleaderLabelM⟩ :=
    ResetAwareNormalizedPrefixState.exists_birthSignalZero_advance_to_of_base_echo_false
      hpsi ring hn leader C C 1 t.val hstateOne hfree
        (by omega) (by omega) hbaseEcho
  have hblockerM :
      (M (groupOffset ring leader (t.val + 1))).core.erase.core.echo =
        true := by
    rw [hstateM.untouched_ahead (t.val + 1) (by omega) (by omega)]
    exact hpresent
  let T :=
    wallSweepBirthSignalZeroPathStallTransition
      hpsi kappa tau
  let suffix : DetSchedule n :=
    [groupOffset ring leader t.val, leader, leader]
  let D := runLocalSchedule ring T M suffix
  have hcollision :
      FirstBlockerEffect ring leader M D t ∧
        PPLLPpsiLeaderCreationRepair.OutgoingResetFrontierUniqueLeaderAt
            hpsi ring D leader ∧
          PPLLPpsiLeaderCreationRepair.BulletTwoFreeAwayFrom D leader ∧
          (D leader).core.erase.core.label =
            (M leader).core.erase.core.label := by
    simpa [T, suffix, D] using
      ResetAwareNormalizedPrefixState.collision_then_birthSignalZero_two_step_reseed
        hpsi ring hn leader C M t.val hstateM t.isLt hblockerM hfreeM
  have heffect : FirstBlockerEffect ring leader C D t := {
    blocker_present := hpresent
    blocker_cleared := hcollision.1.blocker_cleared
    higher_unchanged := by
      intro s hts
      rw [hcollision.1.higher_unchanged s hts]
      have hsite := hstateM.untouched_ahead (s.val + 1)
        (by omega) (by omega)
      exact congrArg
        (fun u : ExpiringAgentState psi kappa tau =>
          u.core.erase.core.echo) hsite }
  let word := pref ++ suffix
  refine ⟨t, word, D, hcanonical, ?_, ?_,
    ⟨hcollision.2.1, hcollision.2.2.1⟩, heffect.rank_lt,
    hcollision.2.2.2.trans hleaderLabelM⟩
  · calc
      D = runLocalSchedule ring T M suffix := rfl
      _ = runLocalSchedule ring T
          (runLocalSchedule ring T C pref) suffix := by rw [← hM]
      _ = runLocalSchedule ring T C (pref ++ suffix) :=
        (runLocalSchedule_append_generic ring T C pref suffix).symm
      _ = runLocalSchedule ring T C word := by rfl
  · simp only [word, suffix, List.length_append, List.length_cons,
      List.length_nil]
    omega

set_option maxHeartbeats 2000000 in
/-- Birth-signal-transition form of the rank-zero terminal follower pass.\nAt rank zero every untouched follower echo is false, so the authenticated
frontier crosses the entire remaining non-wrap prefix without a collision.
This is the terminal branch of the reset-aware rank recursion. -/
theorem resetAwareRetry_birthSignalZero_zero_round
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (leader : Fin n) (C : EConfig n psi kappa tau)
    (hready : ResetAwareRetryReady hpsi ring leader C)
    (hzero : clockwiseEchoRank ring leader C = 0) :
    ∃ (word : DetSchedule n) (D : EConfig n psi kappa tau),
      D = runLocalSchedule ring
        (wallSweepBirthSignalZeroPathStallTransition
          hpsi kappa tau) C word ∧
      word.length = n - 2 ∧
      ResetAwareRetryDone hpsi ring leader D ∧
      (D leader).core.erase.core.label =
        (C leader).core.erase.core.label := by
  obtain ⟨hfrontier, hfree⟩ := hready
  have hstateOne := resetAwareNormalizedPrefixState_one_of_frontierAt
    hpsi ring hn leader C hfrontier
  have hbaseEcho : ∀ k, 1 < k → k ≤ n - 1 →
      (C (groupOffset ring leader k)).core.erase.core.echo = false := by
    intro k hk hkn
    exact follower_echo_false_of_clockwiseEchoRank_eq_zero
      ring leader C hzero k (by omega) (by omega)
  obtain ⟨word, D, hD, hwordLength, hstateD, hfreeD,
      hleaderLabelD⟩ :=
    ResetAwareNormalizedPrefixState.exists_birthSignalZero_advance_to_of_base_echo_false
      hpsi ring hn leader C C 1 (n - 1) hstateOne hfree
        (by omega) (by omega) hbaseEcho
  refine ⟨word, D, hD, ?_, ⟨C, hstateD, hfreeD⟩,
    hleaderLabelD⟩
  omega

set_option maxHeartbeats 3000000 in
/-- Birth-signal-transition strong induction on the follower-echo rank\nconstructs a complete
literal reset-aware retry schedule.  Each failed round costs at most `n`
interactions and strictly decreases rank; the terminal pass costs `n - 2`. -/
theorem exists_resetAwareRetryBirthSignalZeroSchedule_of_rank
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (leader : Fin n) (rank : Nat) (C : EConfig n psi kappa tau)
    (hready : ResetAwareRetryReady hpsi ring leader C)
    (hrank : clockwiseEchoRank ring leader C = rank) :
    ∃ (word : DetSchedule n) (D : EConfig n psi kappa tau),
      D = runLocalSchedule ring
        (wallSweepBirthSignalZeroPathStallTransition
          hpsi kappa tau) C word ∧
      word.length ≤ n * rank + (n - 2) ∧
      ResetAwareRetryDone hpsi ring leader D ∧
      (D leader).core.erase.core.label =
        (C leader).core.erase.core.label := by
  revert C
  induction rank using Nat.strongRecOn with
  | ind rank ih =>
      intro C hready hrank
      by_cases hz : rank = 0
      · have hzero : clockwiseEchoRank ring leader C = 0 :=
          hrank.trans hz
        obtain ⟨word, D, hD, hwordLength, hdone,
            hleaderLabel⟩ :=
          resetAwareRetry_birthSignalZero_zero_round
            hpsi ring hn leader C hready hzero
        refine ⟨word, D, hD, ?_, hdone, hleaderLabel⟩
        rw [hwordLength, hz]
        simp
      · have hactualNe : clockwiseEchoRank ring leader C ≠ 0 := by
          intro hzero
          apply hz
          exact hrank.symm.trans hzero
        obtain ⟨_t, pref, C1, _hcanonical, hC1, hprefLength,
            hready1, hdrop, hroundLabel⟩ :=
          resetAwareRetry_birthSignalZero_failed_round
            hpsi ring hn leader C hready hactualNe
        have hlt : clockwiseEchoRank ring leader C1 < rank := by
          calc
            clockwiseEchoRank ring leader C1 <
                clockwiseEchoRank ring leader C := hdrop
            _ = rank := hrank
        obtain ⟨tail, D, hD, htailLength, hdone,
            htailLabel⟩ :=
          ih (clockwiseEchoRank ring leader C1) hlt C1 hready1 rfl
        let T :=
          wallSweepBirthSignalZeroPathStallTransition
            hpsi kappa tau
        let word := pref ++ tail
        refine ⟨word, D, ?_, ?_, hdone,
          htailLabel.trans hroundLabel⟩
        · calc
            D = runLocalSchedule ring T C1 tail := hD
            _ = runLocalSchedule ring T
                (runLocalSchedule ring T C pref) tail := by rw [← hC1]
            _ = runLocalSchedule ring T C (pref ++ tail) :=
              (runLocalSchedule_append_generic ring T C pref tail).symm
            _ = runLocalSchedule ring T C word := by rfl
        · have hsuccRank :
              clockwiseEchoRank ring leader C1 + 1 ≤ rank := by omega
          have hmul :
              n * (clockwiseEchoRank ring leader C1 + 1) ≤ n * rank :=
            Nat.mul_le_mul_left n hsuccRank
          simp only [word, List.length_append]
          calc
            pref.length + tail.length ≤
                n + (n * clockwiseEchoRank ring leader C1 + (n - 2)) :=
              Nat.add_le_add hprefLength htailLength
            _ = n * (clockwiseEchoRank ring leader C1 + 1) + (n - 2) := by
              rw [Nat.mul_add, Nat.mul_one]
              omega
            _ ≤ n * rank + (n - 2) :=
              Nat.add_le_add_right hmul (n - 2)

/-- Public birth-signal-transition reset-aware scheduler at the configuration's actual echo rank. -/
theorem exists_resetAwareRetryBirthSignalZeroSchedule
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (leader : Fin n) (C : EConfig n psi kappa tau)
    (hready : ResetAwareRetryReady hpsi ring leader C) :
    ∃ (word : DetSchedule n) (D : EConfig n psi kappa tau),
      D = runLocalSchedule ring
        (wallSweepBirthSignalZeroPathStallTransition
          hpsi kappa tau) C word ∧
      word.length ≤
        n * clockwiseEchoRank ring leader C + (n - 2) ∧
      ResetAwareRetryDone hpsi ring leader D ∧
      (D leader).core.erase.core.label =
        (C leader).core.erase.core.label := by
  exact exists_resetAwareRetryBirthSignalZeroSchedule_of_rank
    hpsi ring hn leader (clockwiseEchoRank ring leader C) C hready rfl

/-- Public scheduler endpoint stated directly as the exact closing core.  This
is the strongest closing-edge interface currently derived without importing
leader-label, signal, bullet-zero, or shield hypotheses. -/
theorem exists_resetAwareClosingCoreSchedule
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (leader : Fin n) (C : EConfig n psi kappa tau)
    (hready : ResetAwareRetryReady hpsi ring leader C) :
    ∃ (word : DetSchedule n) (D : EConfig n psi kappa tau),
      D = runLocalSchedule ring
        (wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
          hpsi kappa tau) C word ∧
      word.length ≤
        n * clockwiseEchoRank ring leader C + (n - 2) ∧
      ResetAwareClosingCore hpsi ring leader D ∧
      (D leader).core.erase.core.label =
        (C leader).core.erase.core.label := by
  obtain ⟨word, D, hD, hlength, hdone, hleaderLabel⟩ :=
    exists_resetAwareRetrySchedule hpsi ring hn leader C hready
  exact ⟨word, D, hD, hlength,
    ResetAwareRetryDone.toClosingCore hpsi ring hn leader D hdone,
    hleaderLabel⟩

set_option maxHeartbeats 4000000 in
/-- A structural retry boundary first completes one normalization, migrates
to a zero-labelled root, seeds the positive absence signal, and then runs the
well-founded signal scheduler to the exact rooted closing boundary.  The
physical root may change only during the one-time reverse migration; every
subsequent retry keeps the returned `newRoot` fixed. -/
theorem exists_resetAwareRootedClosingRepairSchedule
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (hpsiLe : psi ≤ n)
    (leader : Fin n) (C : EConfig n psi kappa tau)
    (hready : ResetAwareRetryReady hpsi ring leader C) :
    ∃ (word : DetSchedule n) (D : EConfig n psi kappa tau)
      (newRoot : Fin n),
      D = runLocalSchedule ring
        (wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
          hpsi kappa tau) C word ∧
      ResetAwareRootedClosingReady hpsi ring newRoot D := by
  let T :=
    wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
      hpsi kappa tau
  obtain ⟨first, M, hM, _hfirstLength, hdone, _hfirstLabel⟩ :=
    exists_resetAwareRetrySchedule hpsi ring hn leader C hready
  obtain ⟨k, _hkpos, _hkle, hseed⟩ :=
    hdone.exists_zeroRoot_signalReady
      hpsi ring hn leader M hpsiLe
  let newRoot := groupOffset ring leader k
  let reverseWord := pPsiProbeChasePrefix ring leader (n - k)
  let seedWord := reverseWord ++ [newRoot, newRoot]
  let S := runLocalSchedule ring T M seedWord
  change seedWord.length ≤ n + 1 ∧
      ResetAwareSignalReady hpsi ring newRoot S ∧
      (S newRoot).core.erase.core.label = ⟨0, hpsi⟩ at hseed
  obtain ⟨_hseedLength, hsignal, hzero⟩ := hseed
  obtain ⟨tail, D, hD, hrooted⟩ :=
    exists_resetAwareRootedClosingSchedule
      hpsi ring hn newRoot S hsignal hzero
  let word := first ++ seedWord ++ tail
  refine ⟨word, D, newRoot, ?_, hrooted⟩
  calc
    D = runLocalSchedule ring T S tail := hD
    _ = runLocalSchedule ring T
        (runLocalSchedule ring T M seedWord) tail := by rfl
    _ = runLocalSchedule ring T M (seedWord ++ tail) :=
      (runLocalSchedule_append_generic ring T M seedWord tail).symm
    _ = runLocalSchedule ring T
        (runLocalSchedule ring T C first) (seedWord ++ tail) := by
          rw [← hM]
    _ = runLocalSchedule ring T C (first ++ (seedWord ++ tail)) :=
      (runLocalSchedule_append_generic ring T C first
        (seedWord ++ tail)).symm
    _ = runLocalSchedule ring T C word := by
      simp only [word, List.append_assoc]

set_option maxHeartbeats 4000000 in
/-- Under the birth-signal transition, a structural retry boundary first completes one normalization, migrates
to a zero-labelled root, seeds the positive absence signal, and then runs the
well-founded signal scheduler to the exact rooted closing boundary.  The
physical root may change only during the one-time reverse migration; every
subsequent retry keeps the returned `newRoot` fixed. -/
theorem exists_resetAwareRootedBirthSignalZeroClosingRepairSchedule
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (hpsiLe : psi ≤ n)
    (leader : Fin n) (C : EConfig n psi kappa tau)
    (hready : ResetAwareRetryReady hpsi ring leader C) :
    ∃ (word : DetSchedule n) (D : EConfig n psi kappa tau)
      (newRoot : Fin n),
      D = runLocalSchedule ring
        (wallSweepBirthSignalZeroPathStallTransition
          hpsi kappa tau) C word ∧
      ResetAwareRootedClosingReady hpsi ring newRoot D := by
  let T :=
    wallSweepBirthSignalZeroPathStallTransition
      hpsi kappa tau
  obtain ⟨first, M, hM, _hfirstLength, hdone, _hfirstLabel⟩ :=
    exists_resetAwareRetryBirthSignalZeroSchedule hpsi ring hn leader C hready
  obtain ⟨k, _hkpos, _hkle, hseed⟩ :=
    hdone.exists_birthSignalZero_zeroRoot_signalReady
      hpsi ring hn leader M hpsiLe
  let newRoot := groupOffset ring leader k
  let reverseWord := pPsiProbeChasePrefix ring leader (n - k)
  let seedWord := reverseWord ++ [newRoot, newRoot]
  let S := runLocalSchedule ring T M seedWord
  change seedWord.length ≤ n + 1 ∧
      ResetAwareSignalReady hpsi ring newRoot S ∧
      (S newRoot).core.erase.core.label = ⟨0, hpsi⟩ at hseed
  obtain ⟨_hseedLength, hsignal, hzero⟩ := hseed
  obtain ⟨tail, D, hD, hrooted⟩ :=
    exists_resetAwareRootedBirthSignalZeroClosingSchedule
      hpsi ring hn newRoot S hsignal hzero
  let word := first ++ seedWord ++ tail
  refine ⟨word, D, newRoot, ?_, hrooted⟩
  calc
    D = runLocalSchedule ring T S tail := hD
    _ = runLocalSchedule ring T
        (runLocalSchedule ring T M seedWord) tail := by rfl
    _ = runLocalSchedule ring T M (seedWord ++ tail) :=
      (runLocalSchedule_append_generic ring T M seedWord tail).symm
    _ = runLocalSchedule ring T
        (runLocalSchedule ring T C first) (seedWord ++ tail) := by
          rw [← hM]
    _ = runLocalSchedule ring T C (first ++ (seedWord ++ tail)) :=
      (runLocalSchedule_append_generic ring T C first
        (seedWord ++ tail)).symm
    _ = runLocalSchedule ring T C word := by
      simp only [word, List.append_assoc]

set_option maxHeartbeats 3000000 in
/-- The zero-root reseed can run the verified retry scheduler a second time.
This restores the complete closing geometry relative to the new root while
preserving its zero label.  Only the predecessor absence signal is omitted. -/
theorem ResetAwareRetryDone.exists_zeroRoot_secondNormalization
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (leader : Fin n) (C : EConfig n psi kappa tau)
    (hdone : ResetAwareRetryDone hpsi ring leader C)
    (hpsiLe : psi ≤ n) :
    ∃ k, 0 < k ∧ k ≤ n ∧
      let newRoot := groupOffset ring leader k
      let T :=
        wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
          hpsi kappa tau
      let reverseWord := pPsiProbeChasePrefix ring leader (n - k)
      let seedWord := reverseWord ++ [newRoot, newRoot]
      let M := runLocalSchedule ring T C seedWord
      ∃ (tail : DetSchedule n) (D : EConfig n psi kappa tau),
        D = runLocalSchedule ring T C (seedWord ++ tail) ∧
        seedWord.length ≤ n + 1 ∧
        tail.length ≤
          n * clockwiseEchoRank ring newRoot M + (n - 2) ∧
        ResetAwareClosingCore hpsi ring newRoot D ∧
        (D newRoot).core.erase.core.label = ⟨0, hpsi⟩ := by
  obtain ⟨k, hkpos, hkle, hseed⟩ :=
    hdone.exists_zeroRoot_reseed hpsi ring hn leader C hpsiLe
  let newRoot := groupOffset ring leader k
  let T :=
    wallSweepResetProbePreCheckResetLeaderSinkPathStallTransition
      hpsi kappa tau
  let reverseWord := pPsiProbeChasePrefix ring leader (n - k)
  let seedWord := reverseWord ++ [newRoot, newRoot]
  let M := runLocalSchedule ring T C seedWord
  change seedWord.length ≤ n + 1 ∧
      ResetAwareRetryReady hpsi ring newRoot M ∧
      (M newRoot).core.erase.core.label = ⟨0, hpsi⟩ at hseed
  obtain ⟨hseedLength, hreadyM, hzeroM⟩ := hseed
  obtain ⟨tail, D, hD, htailLength, hcoreD, hlabelD⟩ :=
    exists_resetAwareClosingCoreSchedule hpsi ring hn newRoot M hreadyM
  have hzeroD : (D newRoot).core.erase.core.label = ⟨0, hpsi⟩ :=
    hlabelD.trans hzeroM
  refine ⟨k, hkpos, hkle, tail, D, ?_, hseedLength,
    htailLength, hcoreD, hzeroD⟩
  calc
    D = runLocalSchedule ring T M tail := hD
    _ = runLocalSchedule ring T
        (runLocalSchedule ring T C seedWord) tail := by rfl
    _ = runLocalSchedule ring T C (seedWord ++ tail) :=
      (runLocalSchedule_append_generic ring T C seedWord tail).symm

end PPLLWallSweepClockwiseAttempt
