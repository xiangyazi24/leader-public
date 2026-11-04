import Leader.Wu.WallSweep.ShieldCircuit

/-!
# Full-wall absence-signal shield circuit

This module lifts the isolated arbitrary-ring circuit to the complete finite
wall transition.  The phase invariant combines the absence-signal frontier
with Algorithm 14's moving reset token.  Global comparison neutrality makes
every intended edge priority-open, structurally supplies the real-CHECK frame,
and ensures that no deletion interrupt is present.
-/

namespace PPLLWallSweepShieldCircuitFull

open PPLL PPLLRepair PPLLResearchFormulation
  PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
  PPLLLeaderCreationCleanupRepair PPLLWallSweepRepair
  PPLLWallSweepFinite PPLLWallSweepFiniteCleanup
  PPLLWallSweepNormalResetContract PPLLWallSweepShieldCircuit
  PPLLWallSweepSchedule PPLLWriteSeqRelocation
  PPLLWriteSeqPersistenceRegression
  PPLLNoCheckBirthConditionTwoGeometry

variable {n psi kappa tau : Nat}

/-- State after `steps` complete-wall propagation edges.  Besides the isolated
signal frontier, every comparison carrier is neutral, reset sits at the current
frontier once the leader has seeded it, and every not-yet-visited responder has
zero echo. -/
structure WallShieldPropagationState (hpsi : psi > 0)
    (ring : DirectedRing n) (leader : Fin n)
    (C : Fin n → ExpiringAgentState psi kappa tau) (steps : Nat) : Prop where
  steps_le : steps ≤ n
  stable_labels : ∀ i,
    (C (ring.rightNeighbor i)).core.erase.core.label =
      ⟨((C i).core.erase.core.label.val + 1) % psi,
        Nat.mod_lt _ hpsi⟩
  leader_alive : (C leader).core.erase.core.leader = true
  leader_zero : (C leader).core.erase.core.label = ⟨0, hpsi⟩
  unique_leader : ∀ i, i ≠ leader →
    (C i).core.erase.core.leader = false
  comparison_neutral : ∀ i, ComparisonNeutral (C i).core.erase.core
  bullets_zero : ∀ i, (C i).core.erase.core.bullet = ⟨0, by omega⟩
  visited_signal : ∀ k, 0 < k → k ≤ steps → k < n →
    (C (groupOffset ring leader k)).core.erase.core.signal_B =
      ⟨1, by omega⟩
  ahead_zero : ∀ k, steps < k → k < n →
    (C (groupOffset ring leader k)).core.erase.core.signal_B =
      ⟨0, by omega⟩
  leader_signal_zero : steps < n →
    (C leader).core.erase.core.signal_B = ⟨0, by omega⟩
  leader_signal_one : steps = n →
    (C leader).core.erase.core.signal_B = ⟨1, by omega⟩
  reset_frontier : 0 < steps →
    (C (groupOffset ring leader steps)).core.erase.core.reset_cmd = true
  ahead_echo_zero : ∀ k, steps < k → k < n →
    (C (groupOffset ring leader k)).core.erase.core.echo = false
  leader_echo_zero : (C leader).core.erase.core.echo = false

/-- A neutral, echo-free, unique label-zero leader configuration is the zero
frontier of the complete-wall circuit. -/
theorem wallShieldPropagationState_zero
    (hpsi : psi > 0) (ring : DirectedRing n) (leader : Fin n)
    (C : Fin n → ExpiringAgentState psi kappa tau)
    (hstable : ∀ i,
      (C (ring.rightNeighbor i)).core.erase.core.label =
        ⟨((C i).core.erase.core.label.val + 1) % psi,
          Nat.mod_lt _ hpsi⟩)
    (hleader : (C leader).core.erase.core.leader = true)
    (hzero : (C leader).core.erase.core.label = ⟨0, hpsi⟩)
    (hunique : ∀ i, i ≠ leader →
      (C i).core.erase.core.leader = false)
    (hneutral : ∀ i, ComparisonNeutral (C i).core.erase.core)
    (hbullets : ∀ i, (C i).core.erase.core.bullet = ⟨0, by omega⟩)
    (hsignals : ∀ i, (C i).core.erase.core.signal_B = ⟨0, by omega⟩)
    (hecho : ∀ i, (C i).core.erase.core.echo = false) :
    WallShieldPropagationState hpsi ring leader C 0 := by
  refine ⟨by omega, hstable, hleader, hzero, hunique, hneutral,
    hbullets, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k hk
    omega
  · intro k _ hk
    exact hsignals _
  · intro _
    exact hsignals leader
  · intro h
    have hn := ring.hn
    omega
  · intro h
    omega
  · intro k _ _
    exact hecho _
  · exact hecho leader

private theorem groupOffset_zero_eq
    (ring : DirectedRing n) (leader : Fin n) :
    groupOffset ring leader 0 = leader := by
  apply Fin.ext
  simp [groupOffset, Nat.mod_eq_of_lt leader.isLt]

private theorem groupOffset_n_eq
    (ring : DirectedRing n) (leader : Fin n) :
    groupOffset ring leader n = leader := by
  apply Fin.ext
  simp [groupOffset, Nat.add_mod_right, Nat.mod_eq_of_lt leader.isLt]

private theorem noActiveDeletion_of_neutral
    (C : Fin n → ExpiringAgentState psi kappa tau)
    (hneutral : ∀ i, ComparisonNeutral (C i).core.erase.core) :
    NoActiveDeletion C := by
  intro i
  have h := hneutral i
  simp [deletionActive, pathPresent, h.1, h.2.1]

/-! ## One complete-wall propagation edge -/

/-- One intended full-wall edge advances the absence signal and the reset
frontier together.  Neutrality opens the ordinary branch and produces the
real-CHECK frame, so no deletion retry or finite enumeration is needed. -/
theorem WallShieldPropagationState.step
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (leader : Fin n)
    (C : Fin n → ExpiringAgentState psi kappa tau) (steps : Nat)
    (hstate : WallShieldPropagationState hpsi ring leader C steps)
    (hnext : steps + 1 ≤ n) :
    let e := groupOffset ring leader steps
    let D := localStep ring
      (wallSweepPathStallTransition hpsi kappa tau) C e
    WallShieldPropagationState hpsi ring leader D (steps + 1) := by
  let e := groupOffset ring leader steps
  let j := groupOffset ring leader (steps + 1)
  have hsteps : steps < n := by omega
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
    have hne := groupOffset_ne_of_lt ring leader hsteps
      (by omega : 0 < n) (by omega : steps ≠ 0)
    exact hne (heq.trans (groupOffset_zero_eq ring leader).symm)
  have hjLeader : steps + 1 = n → j = leader := by
    intro hs
    change groupOffset ring leader (steps + 1) = leader
    rw [hs]
    exact groupOffset_n_eq ring leader
  have hjNotLeader : steps + 1 < n → j ≠ leader := by
    intro hjBound hjEq
    have hne := groupOffset_ne_of_lt ring leader hjBound
      (by omega : 0 < n) (by omega : steps + 1 ≠ 0)
    exact hne (hjEq.trans (groupOffset_zero_eq ring leader).symm)
  have hnoActive : NoActiveDeletion C :=
    noActiveDeletion_of_neutral C hstate.comparison_neutral
  have hopen : WallPriorityOpen (C e) (C j) := by
    simpa [hneighbor] using
      WallPriorityOpen.of_noActiveDeletion C hnoActive ring e
  have hresponderZero :
      (C j).core.erase.core.leader = true →
        (C j).core.erase.core.label = ⟨0, hpsi⟩ := by
    intro hj
    by_cases hjEq : j = leader
    · rw [hjEq]
      exact hstate.leader_zero
    · have hf := hstate.unique_leader j hjEq
      rw [hf] at hj
      contradiction
  have hframe : WallPeaceEdgeFrame hpsi kappa
      (C e).core.erase (C j).core.erase :=
    WallPeaceEdgeFrame.of_aligned_neutral hpsi kappa
      (C e).core.erase (C j).core.erase
      (by simpa [hneighbor] using hstate.stable_labels e)
      (hstate.comparison_neutral e) (hstate.comparison_neutral j)
      hresponderZero
  have hsource : (C e).core.erase.core.leader = true ∨
      (C e).core.erase.core.signal_B = ⟨1, by omega⟩ := by
    by_cases hs : steps = 0
    · left
      rw [heLeader hs]
      exact hstate.leader_alive
    · right
      exact hstate.visited_signal steps (by omega) (by omega) hsteps
  have hjSignal : (C j).core.erase.core.signal_B = ⟨0, by omega⟩ := by
    by_cases hlast : steps + 1 = n
    · rw [hjLeader hlast]
      exact hstate.leader_signal_zero hsteps
    · exact hstate.ahead_zero (steps + 1) (by omega) (by omega)
  have hnoFire : (C e).core.erase.core.leader = false ∨
      (C e).core.erase.core.signal_B = ⟨0, by omega⟩ := by
    by_cases hs : steps = 0
    · right
      rw [heLeader hs]
      exact hstate.leader_signal_zero hsteps
    · left
      exact hstate.unique_leader e (heNotLeader (by omega))
  have hjEcho : (C j).core.erase.core.echo = false := by
    by_cases hlast : steps + 1 = n
    · rw [hjLeader hlast]
      exact hstate.leader_echo_zero
    · exact hstate.ahead_echo_zero (steps + 1) (by omega) (by omega)
  let q := wallSweepPathStallTransition hpsi kappa tau (C e) (C j)
  have hlocal := wallSweepPathStall_priority_open_idle_propagation_frame
    hpsi (C e) (C j) hopen hframe hnoFire
      (hstate.bullets_zero e) (hstate.bullets_zero j) hjSignal
  have hprop := wallSweepPathStall_priority_open_signal_propagates
    hpsi (C e) (C j) hopen hframe
      (by simpa [hneighbor] using hstate.stable_labels e)
      (hstate.bullets_zero j) hjSignal hsource
  have hneutralPair : ComparisonNeutral q.1.core.erase.core ∧
      ComparisonNeutral q.2.core.erase.core := by
    by_cases hs : steps = 0
    · have hseed := wallSweepPathStall_priority_open_leader_seed_handoff
        hpsi (C e) (C j) hopen hframe
        (by rw [heLeader hs]; exact hstate.leader_alive) hjEcho
      exact ⟨hseed.1, hseed.2.1⟩
    · have hlReset := hstate.reset_frontier (by omega)
      have hreset := wallSweepPathStall_priority_open_reset_handoff
        hpsi (C e) (C j) hopen hlReset hjEcho
      exact ⟨hreset.1, hreset.2.1⟩
  have hrightReset : q.2.core.erase.core.reset_cmd = true := by
    by_cases hs : steps = 0
    · exact (wallSweepPathStall_priority_open_leader_seed_handoff
        hpsi (C e) (C j) hopen hframe
        (by rw [heLeader hs]; exact hstate.leader_alive) hjEcho).2.2.2.2
    · exact (wallSweepPathStall_priority_open_reset_handoff
        hpsi (C e) (C j) hopen
        (hstate.reset_frontier (by omega)) hjEcho).2.2.2
  have hrightEcho : q.2.core.erase.core.echo = false :=
    wallSweepPathStall_priority_open_responder_echo_false
      hpsi (C e) (C j) hopen
  have hleftEchoZero : steps = 0 → q.1.core.erase.core.echo = false := by
    intro hs
    exact (wallSweepPathStall_priority_open_leader_seed_handoff
      hpsi (C e) (C j) hopen hframe
      (by rw [heLeader hs]; exact hstate.leader_alive) hjEcho).2.2.1
  let D := localStep ring
    (wallSweepPathStallTransition hpsi kappa tau) C e
  have hleft : D e = q.1 := by
    simp [D, q, localStep, hneighbor]
  have hright : D j = q.2 := by
    simp [D, q, localStep, hneighbor, Ne.symm hene]
  rcases hlocal with ⟨hLL, hRL, hLLabel, hRLabel, _, _, hLB, hRB,
    hLSignal⟩
  have hleaderAt : ∀ i, (D i).core.erase.core.leader =
      (C i).core.erase.core.leader := by
    intro i
    by_cases hie : i = e
    · subst i
      rw [hleft]
      exact hLL
    · by_cases hij : i = j
      · subst i
        rw [hright]
        exact hRL
      · simp [D, localStep, hie, hneighbor, hij]
  have hlabelAt : ∀ i, (D i).core.erase.core.label =
      (C i).core.erase.core.label := by
    intro i
    by_cases hie : i = e
    · subst i
      rw [hleft]
      exact hLLabel
    · by_cases hij : i = j
      · subst i
        rw [hright]
        exact hRLabel
      · simp [D, localStep, hie, hneighbor, hij]
  have hbulletAt : ∀ i, (D i).core.erase.core.bullet = ⟨0, by omega⟩ := by
    intro i
    by_cases hie : i = e
    · subst i
      rw [hleft]
      exact hLB
    · by_cases hij : i = j
      · subst i
        rw [hright]
        exact hRB
      · have hsame : D i = C i := by
          simp [D, localStep, hie, hneighbor, hij]
        rw [hsame]
        exact hstate.bullets_zero i
  have hneutralAt : ∀ i, ComparisonNeutral (D i).core.erase.core := by
    intro i
    by_cases hie : i = e
    · subst i
      rw [hleft]
      exact hneutralPair.1
    · by_cases hij : i = j
      · subst i
        rw [hright]
        exact hneutralPair.2
      · have hsame : D i = C i := by
          simp [D, localStep, hie, hneighbor, hij]
        rw [hsame]
        exact hstate.comparison_neutral i
  have hsignalOther : ∀ i, i ≠ j →
      (D i).core.erase.core.signal_B = (C i).core.erase.core.signal_B := by
    intro i hij
    by_cases hie : i = e
    · subst i
      rw [hleft]
      exact hLSignal
    · simp [D, localStep, hie, hneighbor, hij]
  refine ⟨hnext, ?_, ?_, ?_, ?_, hneutralAt, hbulletAt,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    rw [hlabelAt, hlabelAt]
    exact hstate.stable_labels i
  · rw [hleaderAt]
    exact hstate.leader_alive
  · rw [hlabelAt]
    exact hstate.leader_zero
  · intro i hi
    rw [hleaderAt]
    exact hstate.unique_leader i hi
  · intro k hkPos hkVisited hkBound
    by_cases hk : k = steps + 1
    · subst k
      change (D j).core.erase.core.signal_B = ⟨1, by omega⟩
      rw [hright]
      exact hprop
    · have hkj : groupOffset ring leader k ≠ j := by
        by_cases hlast : steps + 1 = n
        · rw [hjLeader hlast]
          have hne := groupOffset_ne_of_lt ring leader hkBound
            (by omega : 0 < n) (by omega : k ≠ 0)
          exact fun heq => hne
            (heq.trans (groupOffset_zero_eq ring leader).symm)
        · apply groupOffset_ne_of_lt ring leader hkBound
            (by omega : steps + 1 < n)
          exact hk
      rw [hsignalOther _ hkj]
      exact hstate.visited_signal k hkPos (by omega) hkBound
  · intro k hkAhead hkBound
    have hkj : groupOffset ring leader k ≠ j := by
      apply groupOffset_ne_of_lt ring leader hkBound
        (by omega : steps + 1 < n)
      omega
    rw [hsignalOther _ hkj]
    exact hstate.ahead_zero k (by omega) hkBound
  · intro hbefore
    have hjNot : j ≠ leader := hjNotLeader (by omega)
    rw [hsignalOther leader (Ne.symm hjNot)]
    exact hstate.leader_signal_zero hsteps
  · intro hdone
    have hjEq : j = leader := hjLeader hdone
    change (D leader).core.erase.core.signal_B = ⟨1, by omega⟩
    rw [← hjEq, hright]
    exact hprop
  · intro _
    change (D j).core.erase.core.reset_cmd = true
    rw [hright]
    exact hrightReset
  · intro k hkAhead hkBound
    have hke : groupOffset ring leader k ≠ e := by
      apply groupOffset_ne_of_lt ring leader hkBound hsteps
      omega
    have hkj : groupOffset ring leader k ≠ j := by
      apply groupOffset_ne_of_lt ring leader hkBound
        (by omega : steps + 1 < n)
      omega
    have hsame : D (groupOffset ring leader k) =
        C (groupOffset ring leader k) := by
      simp [D, localStep, hke, hneighbor, hkj]
    exact (congrArg (fun s => s.core.erase.core.echo) hsame).trans
      (hstate.ahead_echo_zero k (by omega) hkBound)
  · by_cases hs : steps = 0
    · have hDLeader : D leader = q.1 :=
        (congrArg D (heLeader hs).symm).trans hleft
      exact (congrArg (fun s => s.core.erase.core.echo) hDLeader).trans
        (hleftEchoZero hs)
    · by_cases hlast : steps + 1 = n
      · have hDLeader : D leader = q.2 :=
          (congrArg D (hjLeader hlast).symm).trans hright
        exact (congrArg (fun s => s.core.erase.core.echo) hDLeader).trans
          hrightEcho
      · have hle : leader ≠ e := Ne.symm (heNotLeader (by omega))
        have hlj : leader ≠ j := Ne.symm (hjNotLeader (by omega))
        have hsame : D leader = C leader := by
          simp [D, localStep, hle, hneighbor, hlj]
        exact (congrArg (fun s => s.core.erase.core.echo) hsame).trans
          hstate.leader_echo_zero

private theorem runLocalSchedule_append
    {Q : Type} (ring : DirectedRing n) (T : Q → Q → Q × Q)
    (C : Fin n → Q) (a b : DetSchedule n) :
    runLocalSchedule ring T C (a ++ b) =
      runLocalSchedule ring T (runLocalSchedule ring T C a) b := by
  induction a generalizing C with
  | nil => rfl
  | cons e rest ih =>
      simp only [List.cons_append, runLocalSchedule]
      exact ih _

/-- Every prefix of the clockwise schedule realizes the combined signal/reset
invariant under the complete finite wall transition. -/
theorem wallShieldPropagationSchedule_reaches
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (leader : Fin n)
    (C : Fin n → ExpiringAgentState psi kappa tau)
    (hstable : ∀ i,
      (C (ring.rightNeighbor i)).core.erase.core.label =
        ⟨((C i).core.erase.core.label.val + 1) % psi,
          Nat.mod_lt _ hpsi⟩)
    (hleader : (C leader).core.erase.core.leader = true)
    (hzero : (C leader).core.erase.core.label = ⟨0, hpsi⟩)
    (hunique : ∀ i, i ≠ leader →
      (C i).core.erase.core.leader = false)
    (hneutral : ∀ i, ComparisonNeutral (C i).core.erase.core)
    (hbullets : ∀ i, (C i).core.erase.core.bullet = ⟨0, by omega⟩)
    (hsignals : ∀ i, (C i).core.erase.core.signal_B = ⟨0, by omega⟩)
    (hecho : ∀ i, (C i).core.erase.core.echo = false)
    (steps : Nat) (hsteps : steps ≤ n) :
    let D := runLocalSchedule ring
      (wallSweepPathStallTransition hpsi kappa tau) C
      (resetSweepSchedule ring leader steps)
    WallShieldPropagationState hpsi ring leader D steps := by
  induction steps with
  | zero =>
      exact wallShieldPropagationState_zero hpsi ring leader C hstable
        hleader hzero hunique hneutral hbullets hsignals hecho
  | succ steps ih =>
      have hprev : steps ≤ n := by omega
      let C0 := runLocalSchedule ring
        (wallSweepPathStallTransition hpsi kappa tau) C
        (resetSweepSchedule ring leader steps)
      have hstate : WallShieldPropagationState
          hpsi ring leader C0 steps := ih hprev
      have hstep := hstate.step hpsi ring hn leader C0 steps hsteps
      rw [resetSweepSchedule, runLocalSchedule_append]
      exact hstep

/-- **Full-wall shield circuit.**  From a neutral, echo-free unique label-zero
leader state, the actual complete finite wall schedule circulates the absence
signal, returns it to the leader, fires the shield, and leaves every comparison
carrier neutral.  Real CHECK remains enabled throughout. -/
theorem wallShieldCircuit_establishes_anchor
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (leader : Fin n)
    (C : Fin n → ExpiringAgentState psi kappa tau)
    (hstable : ∀ i,
      (C (ring.rightNeighbor i)).core.erase.core.label =
        ⟨((C i).core.erase.core.label.val + 1) % psi,
          Nat.mod_lt _ hpsi⟩)
    (hleader : (C leader).core.erase.core.leader = true)
    (hzero : (C leader).core.erase.core.label = ⟨0, hpsi⟩)
    (hunique : ∀ i, i ≠ leader →
      (C i).core.erase.core.leader = false)
    (hneutral : ∀ i, ComparisonNeutral (C i).core.erase.core)
    (hbullets : ∀ i, (C i).core.erase.core.bullet = ⟨0, by omega⟩)
    (hsignals : ∀ i, (C i).core.erase.core.signal_B = ⟨0, by omega⟩)
    (hecho : ∀ i, (C i).core.erase.core.echo = false) :
    let word := resetSweepSchedule ring leader n ++ [leader]
    let D := runLocalSchedule ring
      (wallSweepPathStallTransition hpsi kappa tau) C word
    (D leader).core.erase.core.leader = true ∧
      (D leader).core.erase.core.shield = true ∧
      (D leader).core.erase.core.label = ⟨0, hpsi⟩ ∧
      (D leader).core.erase.core.signal_B = ⟨0, by omega⟩ ∧
      ∀ i, ComparisonNeutral (D i).core.erase.core := by
  let C0 := runLocalSchedule ring
    (wallSweepPathStallTransition hpsi kappa tau) C
    (resetSweepSchedule ring leader n)
  have hstate := wallShieldPropagationSchedule_reaches hpsi ring hn leader C
    hstable hleader hzero hunique hneutral hbullets hsignals hecho n (by omega)
  change WallShieldPropagationState hpsi ring leader C0 n at hstate
  let j := ring.rightNeighbor leader
  have hje : j ≠ leader :=
    rightNeighbor_ne_self_of_one_lt ring hn leader
  have hnoActive : NoActiveDeletion C0 :=
    noActiveDeletion_of_neutral C0 hstate.comparison_neutral
  have hopen : WallPriorityOpen (C0 leader) (C0 j) := by
    simpa [j] using
      WallPriorityOpen.of_noActiveDeletion C0 hnoActive ring leader
  have hresponderZero :
      (C0 j).core.erase.core.leader = true →
        (C0 j).core.erase.core.label = ⟨0, hpsi⟩ := by
    intro hj
    have hf := hstate.unique_leader j hje
    rw [hf] at hj
    contradiction
  have hframe : WallPeaceEdgeFrame hpsi kappa
      (C0 leader).core.erase (C0 j).core.erase :=
    WallPeaceEdgeFrame.of_aligned_neutral hpsi kappa
      (C0 leader).core.erase (C0 j).core.erase
      (by simpa [j] using hstate.stable_labels leader)
      (hstate.comparison_neutral leader) (hstate.comparison_neutral j)
      hresponderZero
  let q := wallSweepPathStallTransition hpsi kappa tau
    (C0 leader) (C0 j)
  have hfire := wallSweepPathStall_priority_open_leader_fire_neutral_anchor
    hpsi (C0 leader) (C0 j) hopen hframe hstate.leader_alive
      hstate.leader_zero (hstate.leader_signal_one rfl)
  let D := localStep ring
    (wallSweepPathStallTransition hpsi kappa tau) C0 leader
  have hleft : D leader = q.1 := by
    simp [D, q, localStep, j]
  have hright : D j = q.2 := by
    simp [D, q, localStep, j, hje]
  have hneutralD : ∀ i, ComparisonNeutral (D i).core.erase.core := by
    intro i
    by_cases hi : i = leader
    · subst i
      rw [hleft]
      exact hfire.1
    · by_cases hij : i = j
      · subst i
        rw [hright]
        exact hfire.2.1
      · have hsame : D i = C0 i := by
          simp [D, localStep, hi, j, hij]
        rw [hsame]
        exact hstate.comparison_neutral i
  dsimp only
  rw [runLocalSchedule_append]
  change (D leader).core.erase.core.leader = true ∧
    (D leader).core.erase.core.shield = true ∧
    (D leader).core.erase.core.label = ⟨0, hpsi⟩ ∧
    (D leader).core.erase.core.signal_B = ⟨0, by omega⟩ ∧
    ∀ i, ComparisonNeutral (D i).core.erase.core
  rw [hleft]
  exact ⟨hfire.2.2.1, hfire.2.2.2.1, hfire.2.2.2.2.1,
    hfire.2.2.2.2.2, hneutralD⟩

end PPLLWallSweepShieldCircuitFull
