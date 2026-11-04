import Leader.Wu.WallSweep.NormalResetContract

/-!
# Protected restartable wall cleanup

The existing restart relation records deletion-free boundaries and reset/echo
frames.  The protected cleanup proof also needs the two facts supplied by the
canonical deletion-drain construction: shields are framed, and an already
deletion-free input chooses the empty drain.  This module is proof-only; it
adds no protocol state and does not alter the finite wall transition.
-/

namespace PPLLWallSweepRestartableProtected

variable {n psi kappa tau : Nat}

open PPLL PPLLResearchFormulation PPLLExpiringComparisonRepair
  PPLLPathStallComparisonRepair PPLLLeaderCreationCleanupRepair
  PPLLWallSweepRepair PPLLWallSweepFinite PPLLWallSweepFiniteCleanup
  PPLLWallSweepNormalResetContract PPLLWallSweepSchedule
  PPLLWallSweepEchoDrain PPLLWriteSeqRelocation
  PPLLWriteSeqPersistenceRegression
  PPLLNoCheckBirthConditionTwoGeometry

/-- Restartable execution using the canonical shield-framing deletion drain. -/
def ProtectedRestartableWallExecution (hpsi : psi > 0) (kappa tau : Nat)
    (ring : DirectedRing n) (C : Fin n → ExpiringAgentState psi kappa tau) :
    DetSchedule n → DetSchedule n →
      (Fin n → ExpiringAgentState psi kappa tau) → Prop
  | [], actual, D =>
      ∃ drain : DetSchedule n,
        actual = drain ∧
        D = runLocalSchedule ring
          (wallSweepPathStallTransition hpsi kappa tau) C drain ∧
        drain.length ≤ comparisonPathCount C ∧
        (NoActiveDeletion C → drain = []) ∧
        NoActiveDeletion D ∧ ResetEchoConfigFrame C D ∧
        ShieldConfigFrame C D
  | e :: rest, actual, D =>
      ∃ (drain : DetSchedule n)
        (C0 C1 : Fin n → ExpiringAgentState psi kappa tau)
        (tail : DetSchedule n),
        actual = drain ++ [e] ++ tail ∧
        C0 = runLocalSchedule ring
          (wallSweepPathStallTransition hpsi kappa tau) C drain ∧
        drain.length ≤ comparisonPathCount C ∧
        (NoActiveDeletion C → drain = []) ∧
        NoActiveDeletion C0 ∧ ResetEchoConfigFrame C C0 ∧
        ShieldConfigFrame C C0 ∧
        C1 = localStep ring
          (wallSweepPathStallTransition hpsi kappa tau) C0 e ∧
        ProtectedRestartableWallExecution hpsi kappa tau
          ring C1 rest tail D

/-- Forgetting the two protected drain facts recovers the maintained
restartable execution certificate. -/
theorem ProtectedRestartableWallExecution.toRestartable
    (hpsi : psi > 0) (ring : DirectedRing n)
    (C : Fin n → ExpiringAgentState psi kappa tau)
    (word actual : DetSchedule n)
    (D : Fin n → ExpiringAgentState psi kappa tau)
    (h : ProtectedRestartableWallExecution hpsi kappa tau
      ring C word actual D) :
    RestartableWallExecution hpsi kappa tau ring C word actual D := by
  induction word generalizing C actual with
  | nil =>
      rcases h with ⟨drain, hactual, hD, hlength, _, hnoActive,
        hframe, _⟩
      exact ⟨drain, hactual, hD, hlength, hnoActive, hframe⟩
  | cons e rest ih =>
      rcases h with ⟨drain, C0, C1, tail, hactual, hC0, hlength,
        _, hnoActive, hframe, _, hC1, htail⟩
      exact ⟨drain, C0, C1, tail, hactual, hC0, hlength,
        hnoActive, hframe, hC1, ih C1 tail htail⟩

/-- Every logical word has a canonical protected restartable execution with
the same global length bound as the maintained restart relation. -/
theorem exists_protectedRestartableWallCleanupSchedule
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (C : Fin n → ExpiringAgentState psi kappa tau)
    (word : DetSchedule n) :
    ∃ (actual : DetSchedule n)
      (D : Fin n → ExpiringAgentState psi kappa tau),
      ProtectedRestartableWallExecution hpsi kappa tau
        ring C word actual D ∧
      actual.length ≤
        word.length * (n + 1) + comparisonPathCount C := by
  induction word generalizing C with
  | nil =>
      obtain ⟨drain, hlength, hempty, hnoActive, hframe, hshield⟩ :=
        exists_wallSweepDeletionDrain_cleanupFrame hpsi ring hn C
      let D := runLocalSchedule ring
        (wallSweepPathStallTransition hpsi kappa tau) C drain
      change NoActiveDeletion D at hnoActive
      change ResetEchoConfigFrame C D at hframe
      change ShieldConfigFrame C D at hshield
      refine ⟨drain, D, ?_, ?_⟩
      · exact ⟨drain, rfl, rfl, hlength, hempty,
          hnoActive, hframe, hshield⟩
      · simpa using hlength
  | cons e rest ih =>
      obtain ⟨drain, hlength, hempty, hnoActive, hframe, hshield⟩ :=
        exists_wallSweepDeletionDrain_cleanupFrame hpsi ring hn C
      let C0 := runLocalSchedule ring
        (wallSweepPathStallTransition hpsi kappa tau) C drain
      change NoActiveDeletion C0 at hnoActive
      change ResetEchoConfigFrame C C0 at hframe
      change ShieldConfigFrame C C0 at hshield
      let C1 := localStep ring
        (wallSweepPathStallTransition hpsi kappa tau) C0 e
      obtain ⟨tail, D, htail, htailLength⟩ := ih C1
      let actual := drain ++ [e] ++ tail
      refine ⟨actual, D, ?_, ?_⟩
      · exact ⟨drain, C0, C1, tail, rfl, rfl, hlength,
          hempty, hnoActive, hframe, hshield, rfl, htail⟩
      · have hcount := comparisonPathCount_le C1
        unfold actual
        simp only [List.length_append, List.length_cons, List.length_nil]
        rw [Nat.succ_mul]
        omega

/-! ## Logical execution without a nonempty final drain -/

/-- One logical edge: canonical deletion drain followed by the intended edge. -/
def ProtectedWallStep (hpsi : psi > 0) (kappa tau : Nat)
    (ring : DirectedRing n) (C : Fin n → ExpiringAgentState psi kappa tau)
    (e : Fin n) (segment : DetSchedule n)
    (D : Fin n → ExpiringAgentState psi kappa tau) : Prop :=
  ∃ (drain : DetSchedule n)
    (C0 : Fin n → ExpiringAgentState psi kappa tau),
    segment = drain ++ [e] ∧
    C0 = runLocalSchedule ring
      (wallSweepPathStallTransition hpsi kappa tau) C drain ∧
    drain.length ≤ comparisonPathCount C ∧
    (NoActiveDeletion C → drain = []) ∧
    NoActiveDeletion C0 ∧ ResetEchoConfigFrame C C0 ∧
    ShieldConfigFrame C C0 ∧
    D = localStep ring
      (wallSweepPathStallTransition hpsi kappa tau) C0 e

/-- A logical word execution concatenates protected logical steps.  Empty
words are exact identity, leaving final drain insertion to the consumer. -/
def ProtectedLogicalExecution (hpsi : psi > 0) (kappa tau : Nat)
    (ring : DirectedRing n) (C : Fin n → ExpiringAgentState psi kappa tau) :
    DetSchedule n → DetSchedule n →
      (Fin n → ExpiringAgentState psi kappa tau) → Prop
  | [], actual, D => actual = [] ∧ D = C
  | e :: rest, actual, D =>
      ∃ (segment tail : DetSchedule n)
        (C1 : Fin n → ExpiringAgentState psi kappa tau),
        actual = segment ++ tail ∧
        ProtectedWallStep hpsi kappa tau ring C e segment C1 ∧
        ProtectedLogicalExecution hpsi kappa tau ring C1 rest tail D

theorem exists_protectedWallStep
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (C : Fin n → ExpiringAgentState psi kappa tau) (e : Fin n) :
    ∃ (segment : DetSchedule n)
      (D : Fin n → ExpiringAgentState psi kappa tau),
      ProtectedWallStep hpsi kappa tau ring C e segment D := by
  obtain ⟨drain, hlength, hempty, hnoActive, hframe, hshield⟩ :=
    exists_wallSweepDeletionDrain_cleanupFrame hpsi ring hn C
  let C0 := runLocalSchedule ring
    (wallSweepPathStallTransition hpsi kappa tau) C drain
  let D := localStep ring
    (wallSweepPathStallTransition hpsi kappa tau) C0 e
  exact ⟨drain ++ [e], D, drain, C0, rfl, rfl, hlength,
    hempty, hnoActive, hframe, hshield, rfl⟩

theorem exists_protectedLogicalExecution
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (C : Fin n → ExpiringAgentState psi kappa tau)
    (word : DetSchedule n) :
    ∃ (actual : DetSchedule n)
      (D : Fin n → ExpiringAgentState psi kappa tau),
      ProtectedLogicalExecution hpsi kappa tau ring C word actual D := by
  induction word generalizing C with
  | nil => exact ⟨[], C, rfl, rfl⟩
  | cons e rest ih =>
      obtain ⟨segment, C1, hstep⟩ :=
        exists_protectedWallStep hpsi ring hn C e
      obtain ⟨tail, D, htail⟩ := ih C1
      exact ⟨segment ++ tail, D, segment, tail, C1,
        rfl, hstep, htail⟩

/-- Protected logical executions compose over word and physical schedule
concatenation. -/
theorem ProtectedLogicalExecution.append
    (hpsi : psi > 0) (ring : DirectedRing n)
    (C M D : Fin n → ExpiringAgentState psi kappa tau)
    (w1 w2 a1 a2 : DetSchedule n)
    (h1 : ProtectedLogicalExecution hpsi kappa tau ring C w1 a1 M)
    (h2 : ProtectedLogicalExecution hpsi kappa tau ring M w2 a2 D) :
    ProtectedLogicalExecution hpsi kappa tau ring C
      (w1 ++ w2) (a1 ++ a2) D := by
  induction w1 generalizing C a1 with
  | nil =>
      rcases h1 with ⟨ha1, hM⟩
      subst a1
      subst M
      simpa using h2
  | cons e rest ih =>
      rcases h1 with ⟨segment, tail, C1, ha1, hstep, htail⟩
      subst a1
      refine ⟨segment, tail ++ a2, C1, ?_, hstep, ?_⟩
      · simp [List.append_assoc]
      · exact ih C1 tail htail

/-- If the logical endpoint is deletion-free, the canonical final drain is
empty and the logical execution is already a maintained restartable execution. -/
theorem ProtectedLogicalExecution.toProtectedRestartable_of_noActive
    (hpsi : psi > 0) (ring : DirectedRing n)
    (C : Fin n → ExpiringAgentState psi kappa tau)
    (word actual : DetSchedule n)
    (D : Fin n → ExpiringAgentState psi kappa tau)
    (h : ProtectedLogicalExecution hpsi kappa tau ring C word actual D)
    (hD : NoActiveDeletion D) :
    ProtectedRestartableWallExecution hpsi kappa tau
      ring C word actual D := by
  induction word generalizing C actual with
  | nil =>
      rcases h with ⟨hactual, hEq⟩
      subst actual
      subst D
      exact ⟨[], rfl, rfl, by simp, fun _ => rfl, hD,
        fun i => ResetEchoFrame.refl (C i), ShieldConfigFrame.refl C⟩
  | cons e rest ih =>
      rcases h with ⟨segment, tail, C1, hactual, hstep, htail⟩
      rcases hstep with ⟨drain, C0, hsegment, hC0, hlength,
        hempty, hnoActive, hframe, hshield, hC1⟩
      subst segment
      subst actual
      refine ⟨drain, C0, C1, tail, ?_, hC0, hlength, hempty,
        hnoActive, hframe, hshield, hC1, ?_⟩
      · simp [List.append_assoc]
      · exact ih C1 tail htail

/-- The canonical logical execution satisfies the same restart length bound. -/
theorem ProtectedLogicalExecution.length_le
    (hpsi : psi > 0) (ring : DirectedRing n)
    (C : Fin n → ExpiringAgentState psi kappa tau)
    (word actual : DetSchedule n)
    (D : Fin n → ExpiringAgentState psi kappa tau)
    (h : ProtectedLogicalExecution hpsi kappa tau ring C word actual D) :
    actual.length ≤ word.length * (n + 1) + comparisonPathCount C := by
  induction word generalizing C actual with
  | nil =>
      rcases h with ⟨hactual, _⟩
      subst actual
      simp
  | cons e rest ih =>
      rcases h with ⟨segment, tail, C1, hactual, hstep, htail⟩
      rcases hstep with ⟨drain, C0, hsegment, _, hlength, _, _, _, _, _⟩
      subst segment
      subst actual
      have htailLength := ih C1 tail htail
      have hcount := comparisonPathCount_le C1
      simp only [List.length_append, List.length_cons, List.length_nil]
      rw [Nat.succ_mul]
      omega

/-! ## Reverse echo-drain semantics -/

def ProtectedLeaderAt (hpsi : psi > 0)
    (C : Fin n → ExpiringAgentState psi kappa tau) (leader : Fin n) : Prop :=
  InitiatorAnchor (C leader).core.erase.core ∧
    (C leader).core.erase.core.label = ⟨0, hpsi⟩

def ProtectedEchoDrainState (hpsi : psi > 0)
    (ring : DirectedRing n) (leader : Fin n)
    (current : Fin n → ExpiringAgentState psi kappa tau)
    (steps : Nat) : Prop :=
  steps ≤ n - 1 ∧ ProtectedLeaderAt hpsi current leader ∧
    (∀ k, n - 1 - steps < k → k < n →
      (current (groupOffset ring leader k)).core.erase.core.echo = false) ∧
    (steps = n - 1 → (current leader).core.erase.core.echo = false)

private theorem ProtectedLeaderAt.of_cleanup_frames
    (hpsi : psi > 0)
    {C D : Fin n → ExpiringAgentState psi kappa tau}
    (leader : Fin n) (h : ProtectedLeaderAt hpsi C leader)
    (hreset : ResetEchoConfigFrame C D)
    (hshield : ShieldConfigFrame C D) :
    ProtectedLeaderAt hpsi D leader := by
  unfold ProtectedLeaderAt at h ⊢
  exact ⟨⟨(hreset leader).1.trans h.1.1,
      (hshield leader).trans h.1.2⟩,
    (hreset leader).2.1.trans h.2⟩

private theorem echo_false_of_reset_frame
    {C D : Fin n → ExpiringAgentState psi kappa tau}
    (hframe : ResetEchoConfigFrame C D) (i : Fin n)
    (h : (C i).core.erase.core.echo = false) :
    (D i).core.erase.core.echo = false :=
  (hframe i).2.2.2.1.trans h

theorem protectedEchoDrainState_zero
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (leader : Fin n) (C : Fin n → ExpiringAgentState psi kappa tau)
    (hanchor : ProtectedLeaderAt hpsi C leader) :
    ProtectedEchoDrainState hpsi ring leader C 0 := by
  refine ⟨by omega, hanchor, ?_, ?_⟩
  · intro k hk hkn
    omega
  · intro h
    omega

theorem ProtectedEchoDrainState.step
    {steps : Nat} (hpsi : psi > 0)
    (ring : DirectedRing n) (hn : 1 < n) (leader : Fin n)
    (current D : Fin n → ExpiringAgentState psi kappa tau)
    (segment : DetSchedule n)
    (hstate : ProtectedEchoDrainState hpsi ring leader current steps)
    (hnext : steps + 1 ≤ n - 1)
    (hstep : ProtectedWallStep hpsi kappa tau ring current
      (groupOffset ring leader (n - 2 - steps)) segment D) :
    ProtectedEchoDrainState hpsi ring leader D (steps + 1) := by
  rcases hstep with ⟨drain, C0, _, hC0, _, _, hnoActive,
    hframe, hshield, hD⟩
  have hstate0 : ProtectedEchoDrainState hpsi ring leader C0 steps := by
    refine ⟨hstate.1,
      ProtectedLeaderAt.of_cleanup_frames hpsi leader hstate.2.1
        hframe hshield, ?_, ?_⟩
    · intro k hk hkn
      exact echo_false_of_reset_frame hframe _
        (hstate.2.2.1 k hk hkn)
    · intro hdone
      exact echo_false_of_reset_frame hframe leader
        (hstate.2.2.2 hdone)
  subst D
  let eOffset := n - 2 - steps
  let jOffset := n - 1 - steps
  have heBound : eOffset < n := by omega
  have hjBound : jOffset < n := by omega
  have hsucc : eOffset + 1 = jOffset := by omega
  let e := groupOffset ring leader eOffset
  let j := groupOffset ring leader jOffset
  have hneighbor : ring.rightNeighbor e = j := by
    rw [show e = groupOffset ring leader eOffset by rfl,
      rightNeighbor_groupOffset, hsucc]
  have hene : e ≠ j := by
    apply groupOffset_ne_of_lt ring leader heBound hjBound
    omega
  have hjLeader : j ≠ leader := by
    intro hj
    have hzero : groupOffset ring leader 0 = leader := by
      apply Fin.ext
      simp [groupOffset, Nat.mod_eq_of_lt leader.isLt]
    have := groupOffset_ne_of_lt ring leader hjBound (by omega : 0 < n)
      (by omega : jOffset ≠ 0)
    exact this (hj.trans hzero.symm)
  have hopen : WallPriorityOpen (C0 e) (C0 j) := by
    simpa [hneighbor] using
      WallPriorityOpen.of_noActiveDeletion C0 hnoActive ring e
  let q := wallSweepPathStallTransition hpsi kappa tau (C0 e) (C0 j)
  have hrightEcho : q.2.core.erase.core.echo = false :=
    wallSweepPathStall_priority_open_responder_echo_false
      hpsi (C0 e) (C0 j) hopen
  let next := localStep ring
    (wallSweepPathStallTransition hpsi kappa tau) C0 e
  have hje : j ≠ e := Ne.symm hene
  have hleft : next e = q.1 := by
    simp [next, q, localStep, hneighbor]
  have hright : next j = q.2 := by
    simp [next, q, localStep, hneighbor, hje]
  change ProtectedEchoDrainState hpsi ring leader next (steps + 1)
  refine ⟨hnext, ?_, ?_, ?_⟩
  · by_cases heLeader : e = leader
    · have hnextLeader : next leader = q.1 := by
        rw [← heLeader]
        exact hleft
      unfold ProtectedLeaderAt
      rw [hnextLeader]
      refine ⟨wallSweepPathStallTransition_initiator_anchor
          hpsi (C0 e) (C0 j) (by simpa [heLeader] using hstate0.2.1.1),
        ?_⟩
      exact (wallSweepPathStall_priority_open_initiator_label_eq
        hpsi (C0 e) (C0 j) hopen).trans
          (by simpa [heLeader] using hstate0.2.1.2)
    · have hsame : next leader = C0 leader := by
        simp [next, localStep, Ne.symm heLeader, hneighbor,
          Ne.symm hjLeader]
      unfold ProtectedLeaderAt
      rw [hsame]
      exact hstate0.2.1
  · intro k hkLower hkBound
    by_cases hkNew : k = jOffset
    · subst k
      rw [hright]
      exact hrightEcho
    · have hkOld : n - 1 - steps < k := by omega
      have hke : groupOffset ring leader k ≠ e := by
        apply groupOffset_ne_of_lt ring leader hkBound heBound
        omega
      have hkj : groupOffset ring leader k ≠ j := by
        apply groupOffset_ne_of_lt ring leader hkBound hjBound hkNew
      have hsame : next (groupOffset ring leader k) =
          C0 (groupOffset ring leader k) := by
        simp [next, localStep, hke, hneighbor, hkj]
      rw [hsame]
      exact hstate0.2.2.1 k hkOld hkBound
  · intro hdone
    have heZero : eOffset = 0 := by omega
    have heLeader : e = leader := by
      apply Fin.ext
      simp [e, eOffset, heZero, groupOffset,
        Nat.mod_eq_of_lt leader.isLt]
    have hanchorE : InitiatorAnchor (C0 e).core.erase.core := by
      rw [heLeader]
      exact hstate0.2.1.1
    have hleftEcho := wallSweepPathStall_priority_open_initiator_echo_false
      hpsi (C0 e) (C0 j) hopen hanchorE
    rw [← heLeader, hleft]
    exact hleftEcho

theorem exists_protectedEchoDrainSchedule_reaches
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (leader : Fin n) (C : Fin n → ExpiringAgentState psi kappa tau)
    (hanchor : ProtectedLeaderAt hpsi C leader)
    (steps : Nat) (hsteps : steps ≤ n - 1) :
    ∃ (actual : DetSchedule n)
      (D : Fin n → ExpiringAgentState psi kappa tau),
      ProtectedLogicalExecution hpsi kappa tau ring C
        (echoDrainSchedule ring leader steps) actual D ∧
      ProtectedEchoDrainState hpsi ring leader D steps := by
  induction steps with
  | zero =>
      exact ⟨[], C, ⟨rfl, rfl⟩,
        protectedEchoDrainState_zero hpsi ring hn leader C hanchor⟩
  | succ steps ih =>
      have hprev : steps ≤ n - 1 := by omega
      obtain ⟨actual0, C0, hexec0, hstate0⟩ := ih hprev
      let e := groupOffset ring leader (n - 2 - steps)
      obtain ⟨segment, C1, hstep⟩ :=
        exists_protectedWallStep hpsi ring hn C0 e
      have hone : ProtectedLogicalExecution hpsi kappa tau ring C0
          [e] segment C1 := by
        exact ⟨segment, [], C1, by simp, hstep, rfl, rfl⟩
      have hexec := ProtectedLogicalExecution.append hpsi ring
        C C0 C1 (echoDrainSchedule ring leader steps) [e]
        actual0 segment hexec0 hone
      have hstate1 := ProtectedEchoDrainState.step hpsi ring hn leader
        C0 C1 segment hstate0 hsteps hstep
      rw [echoDrainSchedule]
      exact ⟨actual0 ++ segment, C1, hexec, hstate1⟩

theorem exists_protectedEchoDrainSchedule_clears_all
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (leader : Fin n) (C : Fin n → ExpiringAgentState psi kappa tau)
    (hanchor : ProtectedLeaderAt hpsi C leader) :
    ∃ (actual : DetSchedule n)
      (D : Fin n → ExpiringAgentState psi kappa tau),
      ProtectedLogicalExecution hpsi kappa tau ring C
        (echoDrainSchedule ring leader (n - 1)) actual D ∧
      (∀ i, (D i).core.erase.core.echo = false) ∧
      ProtectedLeaderAt hpsi D leader := by
  obtain ⟨actual, D, hexec, hstate⟩ :=
    exists_protectedEchoDrainSchedule_reaches
      hpsi ring hn leader C hanchor (n - 1) (by omega)
  refine ⟨actual, D, hexec, ?_, hstate.2.1⟩
  intro i
  let k := cwDist ring leader i
  have hkBound : k < n := cwDist_lt ring leader i
  have hpos : groupOffset ring leader k = i := by
    simpa [groupOffset, cwPos] using cwPos_cwDist ring leader i
  rw [← hpos]
  by_cases hkZero : k = 0
  · rw [hkZero]
    change (D (groupOffset ring leader 0)).core.erase.core.echo = false
    rw [show groupOffset ring leader 0 = leader by
      apply Fin.ext
      simp [groupOffset, Nat.mod_eq_of_lt leader.isLt]]
    exact hstate.2.2.2 rfl
  · exact hstate.2.2.1 k (by omega) hkBound

private theorem deletionActive_false_of_neutral
    (u : ExpiringAgentState psi kappa tau)
    (h : ComparisonNeutral u.core.erase.core) :
    deletionActive u.core.erase = false := by
  simp [deletionActive, pathPresent, h.2.1]

theorem exists_protectedLeaderReseedSchedule
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (leader : Fin n) (C : Fin n → ExpiringAgentState psi kappa tau)
    (hanchor : ProtectedLeaderAt hpsi C leader) :
    ∃ (actual : DetSchedule n)
      (D : Fin n → ExpiringAgentState psi kappa tau),
      ProtectedLogicalExecution hpsi kappa tau ring C
        (leaderReseedSchedule ring leader) actual D ∧
      (∀ i, (D i).core.erase.core.echo = false) ∧
      (D (ring.rightNeighbor leader)).core.erase.core.reset_cmd = true ∧
      ComparisonNeutral
        (D (ring.rightNeighbor leader)).core.erase.core ∧
      ProtectedLeaderAt hpsi D leader ∧ NoActiveDeletion D := by
  obtain ⟨actual0, drained, hexec0, hecho, hdrainedAnchor⟩ :=
    exists_protectedEchoDrainSchedule_clears_all
      hpsi ring hn leader C hanchor
  obtain ⟨segment, seeded, hstep⟩ :=
    exists_protectedWallStep hpsi ring hn drained leader
  rcases hstep with ⟨drain, C0, hsegment, hC0, hlength, hempty, hnoActive,
    hframe, hshield, hseeded⟩
  have hecho0 : ∀ i, (C0 i).core.erase.core.echo = false := by
    intro i
    exact echo_false_of_reset_frame hframe i (hecho i)
  have hanchor0 : ProtectedLeaderAt hpsi C0 leader :=
    ProtectedLeaderAt.of_cleanup_frames hpsi leader hdrainedAnchor
      hframe hshield
  let j := ring.rightNeighbor leader
  have hne : j ≠ leader := rightNeighbor_ne_self_of_one_lt ring hn leader
  have hopen : WallPriorityOpen (C0 leader) (C0 j) :=
    WallPriorityOpen.of_noActiveDeletion C0 hnoActive ring leader
  let q := wallSweepPathStallTransition hpsi kappa tau
    (C0 leader) (C0 j)
  have hcontrol := wallSweepPathStall_priority_open_leader_reseed
    hpsi (C0 leader) (C0 j) hopen hanchor0.1 (hecho0 j)
  have hneutral := wallSweepPathStall_priority_open_leader_reseed_neutral
    hpsi (C0 leader) (C0 j) hopen hanchor0.1 (hecho0 j)
  have hlocalAnchor := wallSweepPathStallTransition_initiator_anchor
    hpsi (C0 leader) (C0 j) hanchor0.1
  have hlocalLabel := wallSweepPathStall_priority_open_initiator_label_eq
    hpsi (C0 leader) (C0 j) hopen
  let next := localStep ring
    (wallSweepPathStallTransition hpsi kappa tau) C0 leader
  have hleft : next leader = q.1 := by
    simp [next, q, localStep, j]
  have hright : next j = q.2 := by
    simp [next, q, localStep, j, hne]
  have hechoNext : ∀ i, (next i).core.erase.core.echo = false := by
    intro i
    by_cases hil : i = leader
    · subst i
      rw [hleft]
      exact hcontrol.1
    · by_cases hir : i = j
      · subst i
        rw [hright]
        exact hcontrol.2.1
      · have hsame : next i = C0 i := by
          simp [next, localStep, hil, j, hir]
        rw [hsame]
        exact hecho0 i
  have hresetNext : (next j).core.erase.core.reset_cmd = true := by
    rw [hright]
    exact hcontrol.2.2
  have hanchorNext : ProtectedLeaderAt hpsi next leader := by
    unfold ProtectedLeaderAt
    rw [hleft]
    exact ⟨hlocalAnchor, hlocalLabel.trans hanchor0.2⟩
  have hnoActiveNext : NoActiveDeletion next := by
    intro i
    by_cases hil : i = leader
    · subst i
      rw [hleft]
      exact deletionActive_false_of_neutral q.1 hneutral.1
    · by_cases hir : i = j
      · subst i
        rw [hright]
        exact deletionActive_false_of_neutral q.2 hneutral.2
      · have hsame : next i = C0 i := by
          simp [next, localStep, hil, j, hir]
        rw [hsame]
        exact hnoActive i
  have hnext : seeded = next := by
    exact hseeded
  have hone : ProtectedLogicalExecution hpsi kappa tau ring drained
      [leader] segment seeded := by
    exact ⟨segment, [], seeded, by simp, ⟨drain, C0, hsegment,
      hC0, hlength, hempty, hnoActive, hframe, hshield,
      hseeded⟩, rfl, rfl⟩
  have hexec := ProtectedLogicalExecution.append hpsi ring
    C drained seeded (echoDrainSchedule ring leader (n - 1)) [leader]
    actual0 segment hexec0 hone
  rw [leaderReseedSchedule]
  refine ⟨actual0 ++ segment, seeded, hexec, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    rw [hnext]
    exact hechoNext i
  · rw [hnext]
    exact hresetNext
  · rw [hnext, hright]
    exact hneutral.2
  · rw [hnext]
    exact hanchorNext
  · rw [hnext]
    exact hnoActiveNext

/-! ## Reset-sweep semantics after reseed -/

theorem groupOffset_rightNeighbor_last
    (ring : DirectedRing n) (hn : 1 < n) (leader : Fin n) :
    groupOffset ring (ring.rightNeighbor leader) (n - 1) = leader := by
  apply Fin.ext
  simp only [groupOffset, DirectedRing.rightNeighbor]
  by_cases hnext : leader.val + 1 < n
  · rw [Nat.mod_eq_of_lt hnext]
    have heq : leader.val + 1 + (n - 1) = leader.val + n := by omega
    rw [heq, Nat.add_mod_right, Nat.mod_eq_of_lt leader.isLt]
  · have heq : leader.val + 1 = n := by omega
    rw [heq, Nat.mod_self, Nat.zero_add,
      Nat.mod_eq_of_lt (by omega : n - 1 < n)]
    omega

structure ProtectedResetSweepState (hpsi : psi > 0)
    (ring : DirectedRing n) (leader start : Fin n)
    (initial current : Fin n → ExpiringAgentState psi kappa tau)
    (steps : Nat) : Prop where
  step_lt : steps < n
  noActive : NoActiveDeletion current
  token_reset :
    (current (groupOffset ring start steps)).core.erase.core.reset_cmd = true
  token_neutral :
    ComparisonNeutral
      (current (groupOffset ring start steps)).core.erase.core
  visited : ∀ k, k < steps →
    ComparisonNeutral (current (groupOffset ring start k)).core.erase.core
  ahead : ∀ k, steps < k → k < n →
    current (groupOffset ring start k) = initial (groupOffset ring start k)
  leader_alive : (current leader).core.erase.core.leader = true
  leader_zero_before_final : steps < n - 1 →
    (current leader).core.erase.core.label = ⟨0, hpsi⟩

theorem protectedResetSweepState_zero
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (leader : Fin n) (C : Fin n → ExpiringAgentState psi kappa tau)
    (hnoActive : NoActiveDeletion C)
    (hreset : (C (ring.rightNeighbor leader)).core.erase.core.reset_cmd = true)
    (hneutral : ComparisonNeutral
      (C (ring.rightNeighbor leader)).core.erase.core)
    (hanchor : ProtectedLeaderAt hpsi C leader) :
    ProtectedResetSweepState hpsi ring leader
      (ring.rightNeighbor leader) C C 0 := by
  refine ⟨by omega, hnoActive, ?_, ?_, ?_, ?_, hanchor.1.1, ?_⟩
  · simpa [groupOffset, Nat.mod_eq_of_lt
      (ring.rightNeighbor leader).isLt] using hreset
  · simpa [groupOffset, Nat.mod_eq_of_lt
      (ring.rightNeighbor leader).isLt] using hneutral
  · intro k hk
    omega
  · intro k hk hkn
    rfl
  · intro _
    exact hanchor.2

theorem ProtectedResetSweepState.step
    {steps : Nat} (hpsi : psi > 0)
    (ring : DirectedRing n) (hn : 1 < n) (leader : Fin n)
    (initial current D : Fin n → ExpiringAgentState psi kappa tau)
    (segment : DetSchedule n)
    (hstate : ProtectedResetSweepState hpsi ring leader
      (ring.rightNeighbor leader) initial current steps)
    (hnext : steps + 1 < n)
    (hecho : ∀ i, (initial i).core.erase.core.echo = false)
    (hstep : ProtectedWallStep hpsi kappa tau ring current
      (groupOffset ring (ring.rightNeighbor leader) steps) segment D) :
    ProtectedResetSweepState hpsi ring leader
      (ring.rightNeighbor leader) initial D (steps + 1) := by
  rcases hstep with ⟨drain, C0, _, hC0, _, hempty, _, _, _, hD⟩
  have hdrain : drain = [] := hempty hstate.noActive
  subst drain
  simp [runLocalSchedule] at hC0
  subst C0
  subst D
  let start := ring.rightNeighbor leader
  let e := groupOffset ring start steps
  let j := groupOffset ring start (steps + 1)
  have hneighbor : ring.rightNeighbor e = j :=
    rightNeighbor_groupOffset ring start steps
  have hene : e ≠ j := by
    apply groupOffset_ne_of_lt ring start hstate.step_lt hnext
    omega
  have hjUntouched := hstate.ahead (steps + 1) (by omega) hnext
  have hjEcho : (current j).core.erase.core.echo = false := by
    rw [hjUntouched]
    exact hecho j
  have hopen := WallPriorityOpen.of_noActiveDeletion
    current hstate.noActive ring e
  change WallPriorityOpen (current e) (current (ring.rightNeighbor e)) at hopen
  rw [hneighbor] at hopen
  have hlocal := wallSweepPathStall_priority_open_reset_handoff
    hpsi (current e) (current j) hopen hstate.token_reset hjEcho
  let q := wallSweepPathStallTransition hpsi kappa tau
    (current e) (current j)
  change ComparisonNeutral q.1.core.erase.core ∧
    ComparisonNeutral q.2.core.erase.core ∧
    q.1.core.erase.core.reset_cmd = false ∧
    q.2.core.erase.core.reset_cmd = true at hlocal
  let next := localStep ring
    (wallSweepPathStallTransition hpsi kappa tau) current e
  have hje : j ≠ e := Ne.symm hene
  have hleft : next e = q.1 := by
    simp [next, q, localStep, hneighbor]
  have hright : next j = q.2 := by
    simp [next, q, localStep, hneighbor, hje]
  have hlast : groupOffset ring start (n - 1) = leader :=
    groupOffset_rightNeighbor_last ring hn leader
  have heLeader : e ≠ leader := by
    intro heq
    have hne := groupOffset_ne_of_lt ring start hstate.step_lt
      (by omega : n - 1 < n) (by omega : steps ≠ n - 1)
    exact hne (heq.trans hlast.symm)
  have hnoActiveNext : NoActiveDeletion next := by
    intro i
    by_cases hie : i = e
    · subst i
      rw [hleft]
      exact deletionActive_false_of_neutral q.1 hlocal.1
    · by_cases hij : i = j
      · subst i
        rw [hright]
        exact deletionActive_false_of_neutral q.2 hlocal.2.1
      · have hsame : next i = current i := by
          simp [next, localStep, hie, hneighbor, hij]
        rw [hsame]
        exact hstate.noActive i
  change ProtectedResetSweepState hpsi ring leader start
    initial next (steps + 1)
  refine ⟨hnext, hnoActiveNext, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show groupOffset ring start (steps + 1) = j by rfl, hright]
    exact hlocal.2.2.2
  · rw [show groupOffset ring start (steps + 1) = j by rfl, hright]
    exact hlocal.2.1
  · intro k hk
    by_cases hlastStep : k = steps
    · subst k
      rw [show groupOffset ring start steps = e by rfl, hleft]
      exact hlocal.1
    · have hkOld : k < steps := by omega
      have hke : groupOffset ring start k ≠ e := by
        apply groupOffset_ne_of_lt ring start <;> omega
      have hkj : groupOffset ring start k ≠ j := by
        apply groupOffset_ne_of_lt ring start <;> omega
      have hsame : next (groupOffset ring start k) =
          current (groupOffset ring start k) := by
        simp [next, localStep, hke, hneighbor, hkj]
      rw [hsame]
      exact hstate.visited k hkOld
  · intro k hkAhead hkRange
    have hke : groupOffset ring start k ≠ e := by
      apply groupOffset_ne_of_lt ring start <;> omega
    have hkj : groupOffset ring start k ≠ j := by
      apply groupOffset_ne_of_lt ring start <;> omega
    have hsame : next (groupOffset ring start k) =
        current (groupOffset ring start k) := by
      simp [next, localStep, hke, hneighbor, hkj]
    rw [hsame, hstate.ahead k (by omega) hkRange]
  · by_cases hjLeader : j = leader
    · have hlabel : (current j).core.erase.core.label = ⟨0, hpsi⟩ := by
        rw [hjLeader]
        exact hstate.leader_zero_before_final (by omega)
      have hleaderJ : (current j).core.erase.core.leader = true := by
        rw [hjLeader]
        exact hstate.leader_alive
      have hsurvive := wallSweepPathStallTransition_responder_zero_survives
        hpsi (current e) (current j) ⟨hleaderJ, hlabel⟩
      rw [← hjLeader, hright]
      exact hsurvive
    · have hsame : next leader = current leader := by
        simp [next, localStep, Ne.symm heLeader, hneighbor,
          Ne.symm hjLeader]
      rw [hsame]
      exact hstate.leader_alive
  · intro hbeforeFinal
    have hjLeader : j ≠ leader := by
      intro hj
      have hne := groupOffset_ne_of_lt ring start hnext
        (by omega : n - 1 < n) (by omega : steps + 1 ≠ n - 1)
      exact hne (hj.trans hlast.symm)
    have hsame : next leader = current leader := by
      simp [next, localStep, Ne.symm heLeader, hneighbor,
        Ne.symm hjLeader]
    rw [hsame]
    exact hstate.leader_zero_before_final (by omega)

theorem exists_protectedResetSweepSchedule_reaches
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (leader : Fin n) (C : Fin n → ExpiringAgentState psi kappa tau)
    (hnoActive : NoActiveDeletion C)
    (hreset : (C (ring.rightNeighbor leader)).core.erase.core.reset_cmd = true)
    (hneutral : ComparisonNeutral
      (C (ring.rightNeighbor leader)).core.erase.core)
    (hecho : ∀ i, (C i).core.erase.core.echo = false)
    (hanchor : ProtectedLeaderAt hpsi C leader)
    (steps : Nat) (hsteps : steps ≤ n - 1) :
    ∃ (actual : DetSchedule n)
      (D : Fin n → ExpiringAgentState psi kappa tau),
      ProtectedLogicalExecution hpsi kappa tau ring C
        (resetSweepSchedule ring (ring.rightNeighbor leader) steps) actual D ∧
      ProtectedResetSweepState hpsi ring leader
        (ring.rightNeighbor leader) C D steps := by
  induction steps with
  | zero =>
      exact ⟨[], C, ⟨rfl, rfl⟩,
        protectedResetSweepState_zero hpsi ring hn leader C
          hnoActive hreset hneutral hanchor⟩
  | succ steps ih =>
      have hprev : steps ≤ n - 1 := by omega
      obtain ⟨actual0, C0, hexec0, hstate0⟩ := ih hprev
      let e := groupOffset ring (ring.rightNeighbor leader) steps
      obtain ⟨segment, C1, hstep⟩ :=
        exists_protectedWallStep hpsi ring hn C0 e
      have hone : ProtectedLogicalExecution hpsi kappa tau ring C0
          [e] segment C1 := by
        exact ⟨segment, [], C1, by simp, hstep, rfl, rfl⟩
      have hexec := ProtectedLogicalExecution.append hpsi ring
        C C0 C1 (resetSweepSchedule ring (ring.rightNeighbor leader) steps)
        [e] actual0 segment hexec0 hone
      have hstate1 := ProtectedResetSweepState.step hpsi ring hn leader
        C C0 C1 segment hstate0 (by omega) hecho hstep
      rw [resetSweepSchedule]
      exact ⟨actual0 ++ segment, C1, hexec, hstate1⟩

theorem exists_protectedResetSweepSchedule_clears_all
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (leader : Fin n) (C : Fin n → ExpiringAgentState psi kappa tau)
    (hnoActive : NoActiveDeletion C)
    (hreset : (C (ring.rightNeighbor leader)).core.erase.core.reset_cmd = true)
    (hneutral : ComparisonNeutral
      (C (ring.rightNeighbor leader)).core.erase.core)
    (hecho : ∀ i, (C i).core.erase.core.echo = false)
    (hanchor : ProtectedLeaderAt hpsi C leader) :
    ∃ (actual : DetSchedule n)
      (D : Fin n → ExpiringAgentState psi kappa tau),
      ProtectedLogicalExecution hpsi kappa tau ring C
        (resetSweepSchedule ring (ring.rightNeighbor leader) (n - 1))
        actual D ∧
      (∀ i, ComparisonNeutral (D i).core.erase.core) ∧
      (D leader).core.erase.core.leader = true ∧ NoActiveDeletion D := by
  obtain ⟨actual, D, hexec, hstate⟩ :=
    exists_protectedResetSweepSchedule_reaches hpsi ring hn leader C
      hnoActive hreset hneutral hecho hanchor (n - 1) (by omega)
  refine ⟨actual, D, hexec, ?_, hstate.leader_alive, hstate.noActive⟩
  intro i
  let start := ring.rightNeighbor leader
  let k := cwDist ring start i
  have hkBound : k < n := cwDist_lt ring start i
  have hpos : groupOffset ring start k = i := by
    simpa [groupOffset, cwPos] using cwPos_cwDist ring start i
  rw [← hpos]
  by_cases hlast : k = n - 1
  · rw [hlast]
    simpa [start] using hstate.token_neutral
  · exact hstate.visited k (by omega)

/-! ## Complete protected restartable cleanup -/

/-- The full `2n-1` logical cleanup word has a restartable complete-wall
execution that preserves the designated leader and clears every comparison
carrier. -/
theorem exists_restartableLeaderDrainReseedResetSweep_clears_all
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (leader : Fin n) (C : Fin n → ExpiringAgentState psi kappa tau)
    (hanchor : ProtectedLeaderAt hpsi C leader) :
    ∃ (actual : DetSchedule n)
      (D : Fin n → ExpiringAgentState psi kappa tau),
      RestartableWallExecution hpsi kappa tau ring C
        (leaderDrainReseedResetSweep ring leader) actual D ∧
      actual.length ≤
        (2 * n - 1) * (n + 1) + comparisonPathCount C ∧
      (D leader).core.erase.core.leader = true ∧
      ∀ i, ComparisonNeutral (D i).core.erase.core := by
  obtain ⟨actual0, seeded, hseedExec, hecho, hreset, hneutral,
    hseedAnchor, hseedNoActive⟩ :=
    exists_protectedLeaderReseedSchedule hpsi ring hn leader C hanchor
  obtain ⟨actual1, D, hresetExec, hclean, hleader, hDNoActive⟩ :=
    exists_protectedResetSweepSchedule_clears_all hpsi ring hn leader
      seeded hseedNoActive hreset hneutral hecho hseedAnchor
  have hexec := ProtectedLogicalExecution.append hpsi ring
    C seeded D (leaderReseedSchedule ring leader)
    (resetSweepSchedule ring (ring.rightNeighbor leader) (n - 1))
    actual0 actual1 hseedExec hresetExec
  have hword : leaderReseedSchedule ring leader ++
      resetSweepSchedule ring (ring.rightNeighbor leader) (n - 1) =
      leaderDrainReseedResetSweep ring leader := by
    rfl
  rw [hword] at hexec
  have hprotected :=
    ProtectedLogicalExecution.toProtectedRestartable_of_noActive
      hpsi ring C (leaderDrainReseedResetSweep ring leader)
      (actual0 ++ actual1) D hexec hDNoActive
  have hrestart := hprotected.toRestartable hpsi ring C
    (leaderDrainReseedResetSweep ring leader) (actual0 ++ actual1) D
  have hlength := ProtectedLogicalExecution.length_le hpsi ring C
    (leaderDrainReseedResetSweep ring leader) (actual0 ++ actual1) D hexec
  rw [leaderDrainReseedResetSweep_length ring leader] at hlength
  exact ⟨actual0 ++ actual1, D, hrestart, hlength, hleader, hclean⟩

end PPLLWallSweepRestartableProtected
