import Leader.Wu.WallSweep.RestartableProtected
import Leader.Wu.WallSweep.PreCheckResetContractsDrain

/-!
# Transition-generic protected wall cleanup

The protected reverse-echo-drain, leader-reseed, and clockwise reset-sweep
argument depends on a small local transition contract, not on the internal
definition of one wall.  This module states that contract explicitly and
provides exact restartable execution relations for any transition satisfying
it.  The first new instance is the pre-CHECK reset repair.

The resulting theorem has the same deliberately limited signature as the
earlier protected cleanup: one designated shielded label-zero leader survives
and every comparison carrier is neutral.  It does not assert uniqueness or
clean bullets, signals, resets, echoes, or write carriers.
-/

namespace PPLLWallSweepRestartableGeneric

variable {n psi kappa tau : Nat}

open PPLL PPLLResearchFormulation PPLLExpiringComparisonRepair
  PPLLPathStallComparisonRepair PPLLLeaderCreationCleanupRepair
  PPLLWallSweepRepair PPLLWallSweepFinite PPLLWallSweepFiniteCleanup
  PPLLWallSweepNormalResetContract PPLLWallSweepSchedule
  PPLLWallSweepEchoDrain PPLLWallSweepRestartableProtected
  PPLLWallSweepPreCheckResetRepair PPLLWallSweepPreCheckResetContracts
  PPLLWriteSeqRelocation PPLLWriteSeqPersistenceRegression
  PPLLNoCheckBirthConditionTwoGeometry

/-- Pair transition on the existing finite authorization-plus-stall carrier. -/
abbrev ExpiringTransition (psi kappa tau : Nat) :=
  ExpiringAgentState psi kappa tau →
    ExpiringAgentState psi kappa tau →
      ExpiringAgentState psi kappa tau ×
        ExpiringAgentState psi kappa tau

/-- Exact local interface consumed by the protected cleanup scheduler. -/
structure ProtectedCleanupContract
    (hpsi : psi > 0) (T : ExpiringTransition psi kappa tau) : Prop where
  deletion_drain : ∀ {n : Nat} (ring : DirectedRing n), 1 < n →
    ∀ C : Fin n → ExpiringAgentState psi kappa tau,
      ∃ drain : DetSchedule n,
        drain.length ≤ comparisonPathCount C ∧
        (NoActiveDeletion C → drain = []) ∧
        let D := runLocalSchedule ring T C drain
        NoActiveDeletion D ∧ ResetEchoConfigFrame C D ∧
          ShieldConfigFrame C D
  priority_open_responder_echo_false : ∀ l r,
    WallPriorityOpen l r → (T l r).2.core.erase.core.echo = false
  priority_open_protected_initiator : ∀ l r,
    WallPriorityOpen l r → InitiatorAnchor l.core.erase.core →
      InitiatorAnchor (T l r).1.core.erase.core ∧
        (T l r).1.core.erase.core.label = l.core.erase.core.label ∧
        (T l r).1.core.erase.core.echo = false
  priority_open_leader_reseed : ∀ l r,
    WallPriorityOpen l r → InitiatorAnchor l.core.erase.core →
    r.core.erase.core.echo = false →
      ComparisonNeutral (T l r).1.core.erase.core ∧
        ComparisonNeutral (T l r).2.core.erase.core ∧
        (T l r).2.core.erase.core.reset_cmd = true
  priority_open_reset_handoff : ∀ l r,
    WallPriorityOpen l r → l.core.erase.core.reset_cmd = true →
    r.core.erase.core.echo = false →
      ComparisonNeutral (T l r).1.core.erase.core ∧
        ComparisonNeutral (T l r).2.core.erase.core ∧
        (T l r).1.core.erase.core.reset_cmd = false ∧
        (T l r).2.core.erase.core.reset_cmd = true
  priority_open_responder_zero_survives : ∀ l r,
    WallPriorityOpen l r → l.core.erase.core.reset_cmd = true →
    ResponderZeroAnchor hpsi r.core.erase.core →
      (T l r).2.core.erase.core.leader = true

/-- The proved pre-CHECK local contracts assemble into the generic scheduler
interface without any additional protocol assumption. -/
theorem preCheckResetProtectedCleanupContract
    (hpsi : psi > 0) :
    ProtectedCleanupContract hpsi
      (wallSweepPreCheckResetPathStallTransition hpsi kappa tau) where
  deletion_drain := by
    intro n ring hn C
    exact exists_wallSweepPreCheckResetDeletionDrain_cleanupFrame
      hpsi ring hn C
  priority_open_responder_echo_false := by
    intro l r hopen
    exact wallSweepPreCheckResetPathStall_priority_open_responder_echo_false
      hpsi l r hopen
  priority_open_protected_initiator := by
    intro l r hopen hanchor
    exact ⟨
      wallSweepPreCheckResetPathStall_priority_open_initiator_anchor
        hpsi l r hopen hanchor,
      (wallSweepPreCheckResetPathStall_priority_open_label_of_anchor
        hpsi l r hopen hanchor).exact_eq,
      wallSweepPreCheckResetPathStall_priority_open_initiator_echo_false
        hpsi l r hopen hanchor⟩
  priority_open_leader_reseed := by
    intro l r hopen hanchor hecho
    have hn :=
      wallSweepPreCheckResetPathStall_priority_open_leader_reseed_neutral
        hpsi l r hopen hanchor hecho
    have hc := wallSweepPreCheckResetPathStall_priority_open_leader_reseed
      hpsi l r hopen hanchor hecho
    exact ⟨hn.1, hn.2, hc.2.2⟩
  priority_open_reset_handoff := by
    intro l r hopen hreset hecho
    exact wallSweepPreCheckResetPathStall_reset_handoff
      hpsi l r hopen hreset hecho
  priority_open_responder_zero_survives := by
    intro l r hopen hreset hzero
    exact wallSweepPreCheckResetPathStall_priority_open_responder_zero_survives
      hpsi l r hopen hreset hzero

/-! ## Generic restartable execution certificates -/

/-- A flattened physical schedule executes a logical word under `T`, inserting
the contract's canonical deletion drain before every intended edge. -/
def RestartableExecutionFor
    (T : ExpiringTransition psi kappa tau)
    (ring : DirectedRing n)
    (C : Fin n → ExpiringAgentState psi kappa tau) :
    DetSchedule n → DetSchedule n →
      (Fin n → ExpiringAgentState psi kappa tau) → Prop
  | [], actual, D =>
      ∃ drain : DetSchedule n,
        actual = drain ∧
        D = runLocalSchedule ring T C drain ∧
        drain.length ≤ comparisonPathCount C ∧
        NoActiveDeletion D ∧ ResetEchoConfigFrame C D
  | e :: rest, actual, D =>
      ∃ (drain : DetSchedule n)
        (C0 C1 : Fin n → ExpiringAgentState psi kappa tau)
        (tail : DetSchedule n),
        actual = drain ++ [e] ++ tail ∧
        C0 = runLocalSchedule ring T C drain ∧
        drain.length ≤ comparisonPathCount C ∧
        NoActiveDeletion C0 ∧ ResetEchoConfigFrame C C0 ∧
        C1 = localStep ring T C0 e ∧
        RestartableExecutionFor T ring C1 rest tail D

/-- One protected logical edge is a canonical drain followed by the intended
edge.  The empty-drain clause is recorded for reset-sweep synchronization. -/
def ProtectedWallStepFor
    (T : ExpiringTransition psi kappa tau)
    (ring : DirectedRing n)
    (C : Fin n → ExpiringAgentState psi kappa tau)
    (e : Fin n) (segment : DetSchedule n)
    (D : Fin n → ExpiringAgentState psi kappa tau) : Prop :=
  ∃ (drain : DetSchedule n)
    (C0 : Fin n → ExpiringAgentState psi kappa tau),
    segment = drain ++ [e] ∧
    C0 = runLocalSchedule ring T C drain ∧
    drain.length ≤ comparisonPathCount C ∧
    (NoActiveDeletion C → drain = []) ∧
    NoActiveDeletion C0 ∧ ResetEchoConfigFrame C C0 ∧
    ShieldConfigFrame C C0 ∧
    D = localStep ring T C0 e

/-- A logical word concatenates protected steps; the empty word is identity. -/
def ProtectedLogicalExecutionFor
    (T : ExpiringTransition psi kappa tau)
    (ring : DirectedRing n)
    (C : Fin n → ExpiringAgentState psi kappa tau) :
    DetSchedule n → DetSchedule n →
      (Fin n → ExpiringAgentState psi kappa tau) → Prop
  | [], actual, D => actual = [] ∧ D = C
  | e :: rest, actual, D =>
      ∃ (segment tail : DetSchedule n)
        (C1 : Fin n → ExpiringAgentState psi kappa tau),
        actual = segment ++ tail ∧
        ProtectedWallStepFor T ring C e segment C1 ∧
        ProtectedLogicalExecutionFor T ring C1 rest tail D

/-- The contract constructs one protected logical edge. -/
theorem existsProtectedWallStepFor
    (hpsi : psi > 0) (T : ExpiringTransition psi kappa tau)
    (K : ProtectedCleanupContract hpsi T)
    (ring : DirectedRing n) (hn : 1 < n)
    (C : Fin n → ExpiringAgentState psi kappa tau) (e : Fin n) :
    ∃ (segment : DetSchedule n)
      (D : Fin n → ExpiringAgentState psi kappa tau),
      ProtectedWallStepFor T ring C e segment D := by
  obtain ⟨drain, hlength, hempty, hnoActive, hframe, hshield⟩ :=
    K.deletion_drain ring hn C
  let C0 := runLocalSchedule ring T C drain
  let D := localStep ring T C0 e
  exact ⟨drain ++ [e], D, drain, C0, rfl, rfl, hlength,
    hempty, hnoActive, hframe, hshield, rfl⟩

/-- Every finite logical word has a protected flattened execution. -/
theorem existsProtectedLogicalExecutionFor
    (hpsi : psi > 0) (T : ExpiringTransition psi kappa tau)
    (K : ProtectedCleanupContract hpsi T)
    (ring : DirectedRing n) (hn : 1 < n)
    (C : Fin n → ExpiringAgentState psi kappa tau)
    (word : DetSchedule n) :
    ∃ (actual : DetSchedule n)
      (D : Fin n → ExpiringAgentState psi kappa tau),
      ProtectedLogicalExecutionFor T ring C word actual D := by
  induction word generalizing C with
  | nil => exact ⟨[], C, rfl, rfl⟩
  | cons e rest ih =>
      obtain ⟨segment, C1, hstep⟩ :=
        existsProtectedWallStepFor hpsi T K ring hn C e
      obtain ⟨tail, D, htail⟩ := ih C1
      exact ⟨segment ++ tail, D, segment, tail, C1,
        rfl, hstep, htail⟩

/-- Generic protected logical executions compose. -/
theorem ProtectedLogicalExecutionFor.append
    (T : ExpiringTransition psi kappa tau)
    (ring : DirectedRing n)
    (C M D : Fin n → ExpiringAgentState psi kappa tau)
    (w1 w2 a1 a2 : DetSchedule n)
    (h1 : ProtectedLogicalExecutionFor T ring C w1 a1 M)
    (h2 : ProtectedLogicalExecutionFor T ring M w2 a2 D) :
    ProtectedLogicalExecutionFor T ring C (w1 ++ w2) (a1 ++ a2) D := by
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

/-- If its endpoint is deletion-free, a protected logical execution is already
an exact restartable execution with no final drain. -/
theorem ProtectedLogicalExecutionFor.toRestartable_of_noActive
    (T : ExpiringTransition psi kappa tau)
    (ring : DirectedRing n)
    (C : Fin n → ExpiringAgentState psi kappa tau)
    (word actual : DetSchedule n)
    (D : Fin n → ExpiringAgentState psi kappa tau)
    (h : ProtectedLogicalExecutionFor T ring C word actual D)
    (hD : NoActiveDeletion D) :
    RestartableExecutionFor T ring C word actual D := by
  induction word generalizing C actual with
  | nil =>
      rcases h with ⟨hactual, hEq⟩
      subst actual
      subst D
      exact ⟨[], rfl, rfl, by simp, hD,
        fun i => ResetEchoFrame.refl (C i)⟩
  | cons e rest ih =>
      rcases h with ⟨segment, tail, C1, hactual, hstep, htail⟩
      rcases hstep with ⟨drain, C0, hsegment, hC0, hlength,
        _, hnoActive, hframe, _, hC1⟩
      subst segment
      subst actual
      refine ⟨drain, C0, C1, tail, ?_, hC0, hlength,
        hnoActive, hframe, hC1, ?_⟩
      · simp [List.append_assoc]
      · exact ih C1 tail htail

/-- Generic protected executions satisfy the same `n+1`-per-logical-edge
length bound. -/
theorem ProtectedLogicalExecutionFor.length_le
    (T : ExpiringTransition psi kappa tau)
    (ring : DirectedRing n)
    (C : Fin n → ExpiringAgentState psi kappa tau)
    (word actual : DetSchedule n)
    (D : Fin n → ExpiringAgentState psi kappa tau)
    (h : ProtectedLogicalExecutionFor T ring C word actual D) :
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

theorem runLocalSchedule_append_generic
    {Q : Type} (ring : DirectedRing n) (T : Q → Q → Q × Q)
    (C : Fin n → Q) (s t : DetSchedule n) :
    runLocalSchedule ring T C (s ++ t) =
      runLocalSchedule ring T (runLocalSchedule ring T C s) t := by
  induction s generalizing C with
  | nil => rfl
  | cons e rest ih =>
      simp only [List.cons_append, runLocalSchedule]
      exact ih _

/-- A restartable certificate denotes the literal flattened execution of `T`. -/
theorem RestartableExecutionFor.runLocalSchedule_eq
    (T : ExpiringTransition psi kappa tau)
    (ring : DirectedRing n)
    (C : Fin n → ExpiringAgentState psi kappa tau)
    (word actual : DetSchedule n)
    (D : Fin n → ExpiringAgentState psi kappa tau)
    (h : RestartableExecutionFor T ring C word actual D) :
    D = runLocalSchedule ring T C actual := by
  induction word generalizing C actual with
  | nil =>
      rcases h with ⟨drain, hactual, hD, _, _, _⟩
      subst actual
      exact hD
  | cons e rest ih =>
      rcases h with ⟨drain, C0, C1, tail, hactual, hC0, _, _, _, hC1,
        htail⟩
      subst actual
      calc
        D = runLocalSchedule ring T C1 tail := ih C1 tail htail
        _ = runLocalSchedule ring T (localStep ring T C0 e) tail := by
          rw [← hC1]
        _ = runLocalSchedule ring T C0 ([e] ++ tail) := rfl
        _ = runLocalSchedule ring T (runLocalSchedule ring T C drain)
            ([e] ++ tail) := by rw [← hC0]
        _ = runLocalSchedule ring T C (drain ++ ([e] ++ tail)) :=
          (runLocalSchedule_append_generic ring T C drain
            ([e] ++ tail)).symm
        _ = runLocalSchedule ring T C (drain ++ [e] ++ tail) := by
          simp [List.append_assoc]

/-! ## Generic reverse echo drain -/

private theorem ProtectedLeaderAt.of_generic_cleanup_frames
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

private theorem echo_false_of_generic_reset_frame
    {C D : Fin n → ExpiringAgentState psi kappa tau}
    (hframe : ResetEchoConfigFrame C D) (i : Fin n)
    (h : (C i).core.erase.core.echo = false) :
    (D i).core.erase.core.echo = false :=
  (hframe i).2.2.2.1.trans h

/-- One generic protected reverse edge extends the echo-free suffix. -/
theorem ProtectedEchoDrainState.stepFor
    {steps : Nat} (hpsi : psi > 0)
    (T : ExpiringTransition psi kappa tau)
    (K : ProtectedCleanupContract hpsi T)
    (ring : DirectedRing n) (hn : 1 < n) (leader : Fin n)
    (current D : Fin n → ExpiringAgentState psi kappa tau)
    (segment : DetSchedule n)
    (hstate : ProtectedEchoDrainState hpsi ring leader current steps)
    (hnext : steps + 1 ≤ n - 1)
    (hstep : ProtectedWallStepFor T ring current
      (groupOffset ring leader (n - 2 - steps)) segment D) :
    ProtectedEchoDrainState hpsi ring leader D (steps + 1) := by
  rcases hstep with ⟨drain, C0, _, hC0, _, _, hnoActive,
    hframe, hshield, hD⟩
  have hstate0 : ProtectedEchoDrainState hpsi ring leader C0 steps := by
    refine ⟨hstate.1,
      ProtectedLeaderAt.of_generic_cleanup_frames hpsi leader hstate.2.1
        hframe hshield, ?_, ?_⟩
    · intro k hk hkn
      exact echo_false_of_generic_reset_frame hframe _
        (hstate.2.2.1 k hk hkn)
    · intro hdone
      exact echo_false_of_generic_reset_frame hframe leader
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
    have hne := groupOffset_ne_of_lt ring leader hjBound
      (by omega : 0 < n) (by omega : jOffset ≠ 0)
    exact hne (hj.trans hzero.symm)
  have hopen : WallPriorityOpen (C0 e) (C0 j) := by
    simpa [hneighbor] using
      WallPriorityOpen.of_noActiveDeletion C0 hnoActive ring e
  let q := T (C0 e) (C0 j)
  have hrightEcho : q.2.core.erase.core.echo = false :=
    K.priority_open_responder_echo_false (C0 e) (C0 j) hopen
  let next := localStep ring T C0 e
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
      have hlocal := K.priority_open_protected_initiator
        (C0 e) (C0 j) hopen (by simpa [heLeader] using hstate0.2.1.1)
      unfold ProtectedLeaderAt
      rw [hnextLeader]
      exact ⟨hlocal.1, hlocal.2.1.trans
        (by simpa [heLeader] using hstate0.2.1.2)⟩
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
    have hlocal := K.priority_open_protected_initiator
      (C0 e) (C0 j) hopen (by
        rw [heLeader]
        exact hstate0.2.1.1)
    rw [← heLeader, hleft]
    exact hlocal.2.2

/-- Every prefix of the reverse word has a generic protected execution and the
same echo-drain invariant. -/
theorem existsProtectedEchoDrainSchedule_reachesFor
    (hpsi : psi > 0) (T : ExpiringTransition psi kappa tau)
    (K : ProtectedCleanupContract hpsi T)
    (ring : DirectedRing n) (hn : 1 < n)
    (leader : Fin n) (C : Fin n → ExpiringAgentState psi kappa tau)
    (hanchor : ProtectedLeaderAt hpsi C leader)
    (steps : Nat) (hsteps : steps ≤ n - 1) :
    ∃ (actual : DetSchedule n)
      (D : Fin n → ExpiringAgentState psi kappa tau),
      ProtectedLogicalExecutionFor T ring C
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
        existsProtectedWallStepFor hpsi T K ring hn C0 e
      have hone : ProtectedLogicalExecutionFor T ring C0
          [e] segment C1 :=
        ⟨segment, [], C1, by simp, hstep, rfl, rfl⟩
      have hexec := ProtectedLogicalExecutionFor.append T ring
        C C0 C1 (echoDrainSchedule ring leader steps) [e]
        actual0 segment hexec0 hone
      have hstate1 := ProtectedEchoDrainState.stepFor hpsi T K ring hn
        leader C0 C1 segment hstate0 hsteps hstep
      rw [echoDrainSchedule]
      exact ⟨actual0 ++ segment, C1, hexec, hstate1⟩

/-- The full generic reverse schedule clears every echo while preserving the
designated protected leader. -/
theorem existsProtectedEchoDrainSchedule_clears_allFor
    (hpsi : psi > 0) (T : ExpiringTransition psi kappa tau)
    (K : ProtectedCleanupContract hpsi T)
    (ring : DirectedRing n) (hn : 1 < n)
    (leader : Fin n) (C : Fin n → ExpiringAgentState psi kappa tau)
    (hanchor : ProtectedLeaderAt hpsi C leader) :
    ∃ (actual : DetSchedule n)
      (D : Fin n → ExpiringAgentState psi kappa tau),
      ProtectedLogicalExecutionFor T ring C
        (echoDrainSchedule ring leader (n - 1)) actual D ∧
      (∀ i, (D i).core.erase.core.echo = false) ∧
      ProtectedLeaderAt hpsi D leader := by
  obtain ⟨actual, D, hexec, hstate⟩ :=
    existsProtectedEchoDrainSchedule_reachesFor
      hpsi T K ring hn leader C hanchor (n - 1) (by omega)
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

private theorem deletionActive_false_of_generic_neutral
    (u : ExpiringAgentState psi kappa tau)
    (h : ComparisonNeutral u.core.erase.core) :
    deletionActive u.core.erase = false := by
  simp [deletionActive, pathPresent, h.2.1]

/-! ## Generic leader reseed -/

/-- Reverse drain followed by the designated leader edge establishes an
echo-free neutral reset seed for any contracted transition. -/
theorem existsProtectedLeaderReseedScheduleFor
    (hpsi : psi > 0) (T : ExpiringTransition psi kappa tau)
    (K : ProtectedCleanupContract hpsi T)
    (ring : DirectedRing n) (hn : 1 < n)
    (leader : Fin n) (C : Fin n → ExpiringAgentState psi kappa tau)
    (hanchor : ProtectedLeaderAt hpsi C leader) :
    ∃ (actual : DetSchedule n)
      (D : Fin n → ExpiringAgentState psi kappa tau),
      ProtectedLogicalExecutionFor T ring C
        (leaderReseedSchedule ring leader) actual D ∧
      (∀ i, (D i).core.erase.core.echo = false) ∧
      (D (ring.rightNeighbor leader)).core.erase.core.reset_cmd = true ∧
      ComparisonNeutral
        (D (ring.rightNeighbor leader)).core.erase.core ∧
      ProtectedLeaderAt hpsi D leader ∧ NoActiveDeletion D := by
  obtain ⟨actual0, drained, hexec0, hecho, hdrainedAnchor⟩ :=
    existsProtectedEchoDrainSchedule_clears_allFor
      hpsi T K ring hn leader C hanchor
  obtain ⟨segment, seeded, hstep⟩ :=
    existsProtectedWallStepFor hpsi T K ring hn drained leader
  rcases hstep with ⟨drain, C0, hsegment, hC0, hlength, hempty,
    hnoActive, hframe, hshield, hseeded⟩
  have hecho0 : ∀ i, (C0 i).core.erase.core.echo = false := by
    intro i
    exact echo_false_of_generic_reset_frame hframe i (hecho i)
  have hanchor0 : ProtectedLeaderAt hpsi C0 leader :=
    ProtectedLeaderAt.of_generic_cleanup_frames hpsi leader
      hdrainedAnchor hframe hshield
  let j := ring.rightNeighbor leader
  have hne : j ≠ leader := rightNeighbor_ne_self_of_one_lt ring hn leader
  have hopen : WallPriorityOpen (C0 leader) (C0 j) :=
    WallPriorityOpen.of_noActiveDeletion C0 hnoActive ring leader
  let q := T (C0 leader) (C0 j)
  have hprotected := K.priority_open_protected_initiator
    (C0 leader) (C0 j) hopen hanchor0.1
  have hrightEcho := K.priority_open_responder_echo_false
    (C0 leader) (C0 j) hopen
  have hseed := K.priority_open_leader_reseed
    (C0 leader) (C0 j) hopen hanchor0.1 (hecho0 j)
  let next := localStep ring T C0 leader
  have hleft : next leader = q.1 := by
    simp [next, q, localStep, j]
  have hright : next j = q.2 := by
    simp [next, q, localStep, j, hne]
  have hechoNext : ∀ i, (next i).core.erase.core.echo = false := by
    intro i
    by_cases hil : i = leader
    · subst i
      rw [hleft]
      exact hprotected.2.2
    · by_cases hir : i = j
      · subst i
        rw [hright]
        exact hrightEcho
      · have hsame : next i = C0 i := by
          simp [next, localStep, hil, j, hir]
        rw [hsame]
        exact hecho0 i
  have hresetNext : (next j).core.erase.core.reset_cmd = true := by
    rw [hright]
    exact hseed.2.2
  have hneutralNext : ComparisonNeutral (next j).core.erase.core := by
    rw [hright]
    exact hseed.2.1
  have hanchorNext : ProtectedLeaderAt hpsi next leader := by
    unfold ProtectedLeaderAt
    rw [hleft]
    exact ⟨hprotected.1, hprotected.2.1.trans hanchor0.2⟩
  have hnoActiveNext : NoActiveDeletion next := by
    intro i
    by_cases hil : i = leader
    · subst i
      rw [hleft]
      exact deletionActive_false_of_generic_neutral q.1 hseed.1
    · by_cases hir : i = j
      · subst i
        rw [hright]
        exact deletionActive_false_of_generic_neutral q.2 hseed.2.1
      · have hsame : next i = C0 i := by
          simp [next, localStep, hil, j, hir]
        rw [hsame]
        exact hnoActive i
  have hnext : seeded = next := hseeded
  have hone : ProtectedLogicalExecutionFor T ring drained
      [leader] segment seeded :=
    ⟨segment, [], seeded, by simp,
      ⟨drain, C0, hsegment, hC0, hlength, hempty,
        hnoActive, hframe, hshield, hseeded⟩,
      rfl, rfl⟩
  have hexec := ProtectedLogicalExecutionFor.append T ring
    C drained seeded (echoDrainSchedule ring leader (n - 1)) [leader]
    actual0 segment hexec0 hone
  rw [leaderReseedSchedule]
  refine ⟨actual0 ++ segment, seeded, hexec, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    rw [hnext]
    exact hechoNext i
  · rw [hnext]
    exact hresetNext
  · rw [hnext]
    exact hneutralNext
  · rw [hnext]
    exact hanchorNext
  · rw [hnext]
    exact hnoActiveNext

/-! ## Generic clockwise reset sweep -/

/-- One intended reset edge advances the transition-independent reset-sweep
state under the local contract. -/
theorem ProtectedResetSweepState.stepFor
    {steps : Nat} (hpsi : psi > 0)
    (T : ExpiringTransition psi kappa tau)
    (K : ProtectedCleanupContract hpsi T)
    (ring : DirectedRing n) (hn : 1 < n) (leader : Fin n)
    (initial current D : Fin n → ExpiringAgentState psi kappa tau)
    (segment : DetSchedule n)
    (hstate : ProtectedResetSweepState hpsi ring leader
      (ring.rightNeighbor leader) initial current steps)
    (hnext : steps + 1 < n)
    (hecho : ∀ i, (initial i).core.erase.core.echo = false)
    (hstep : ProtectedWallStepFor T ring current
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
  have hlocal := K.priority_open_reset_handoff
    (current e) (current j) hopen hstate.token_reset hjEcho
  let q := T (current e) (current j)
  let next := localStep ring T current e
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
      exact deletionActive_false_of_generic_neutral q.1 hlocal.1
    · by_cases hij : i = j
      · subst i
        rw [hright]
        exact deletionActive_false_of_generic_neutral q.2 hlocal.2.1
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
      have hsurvive := K.priority_open_responder_zero_survives
        (current e) (current j) hopen hstate.token_reset
          ⟨hleaderJ, hlabel⟩
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

/-- Every reset-sweep prefix has a generic protected execution. -/
theorem existsProtectedResetSweepSchedule_reachesFor
    (hpsi : psi > 0) (T : ExpiringTransition psi kappa tau)
    (K : ProtectedCleanupContract hpsi T)
    (ring : DirectedRing n) (hn : 1 < n)
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
      ProtectedLogicalExecutionFor T ring C
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
        existsProtectedWallStepFor hpsi T K ring hn C0 e
      have hone : ProtectedLogicalExecutionFor T ring C0
          [e] segment C1 :=
        ⟨segment, [], C1, by simp, hstep, rfl, rfl⟩
      have hexec := ProtectedLogicalExecutionFor.append T ring
        C C0 C1 (resetSweepSchedule ring (ring.rightNeighbor leader) steps)
        [e] actual0 segment hexec0 hone
      have hstate1 := ProtectedResetSweepState.stepFor hpsi T K ring hn
        leader C C0 C1 segment hstate0 (by omega) hecho hstep
      rw [resetSweepSchedule]
      exact ⟨actual0 ++ segment, C1, hexec, hstate1⟩

/-- The full generic reset sweep clears every comparison carrier and preserves
the designated leader. -/
theorem existsProtectedResetSweepSchedule_clears_allFor
    (hpsi : psi > 0) (T : ExpiringTransition psi kappa tau)
    (K : ProtectedCleanupContract hpsi T)
    (ring : DirectedRing n) (hn : 1 < n)
    (leader : Fin n) (C : Fin n → ExpiringAgentState psi kappa tau)
    (hnoActive : NoActiveDeletion C)
    (hreset : (C (ring.rightNeighbor leader)).core.erase.core.reset_cmd = true)
    (hneutral : ComparisonNeutral
      (C (ring.rightNeighbor leader)).core.erase.core)
    (hecho : ∀ i, (C i).core.erase.core.echo = false)
    (hanchor : ProtectedLeaderAt hpsi C leader) :
    ∃ (actual : DetSchedule n)
      (D : Fin n → ExpiringAgentState psi kappa tau),
      ProtectedLogicalExecutionFor T ring C
        (resetSweepSchedule ring (ring.rightNeighbor leader) (n - 1))
        actual D ∧
      (∀ i, ComparisonNeutral (D i).core.erase.core) ∧
      (D leader).core.erase.core.leader = true ∧ NoActiveDeletion D := by
  obtain ⟨actual, D, hexec, hstate⟩ :=
    existsProtectedResetSweepSchedule_reachesFor hpsi T K ring hn leader C
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

/-! ## Generic capstone and pre-CHECK instance -/

/-- The full `2n-1` protected logical word works for every transition
satisfying the local cleanup contract. -/
theorem exists_restartableLeaderDrainReseedResetSweep_of_contract
    (hpsi : psi > 0) (T : ExpiringTransition psi kappa tau)
    (K : ProtectedCleanupContract hpsi T)
    (ring : DirectedRing n) (hn : 1 < n)
    (leader : Fin n) (C : Fin n → ExpiringAgentState psi kappa tau)
    (hanchor : ProtectedLeaderAt hpsi C leader) :
    ∃ (actual : DetSchedule n)
      (D : Fin n → ExpiringAgentState psi kappa tau),
      RestartableExecutionFor T ring C
        (leaderDrainReseedResetSweep ring leader) actual D ∧
      actual.length ≤
        (2 * n - 1) * (n + 1) + comparisonPathCount C ∧
      (D leader).core.erase.core.leader = true ∧
      ∀ i, ComparisonNeutral (D i).core.erase.core := by
  obtain ⟨actual0, seeded, hseedExec, hecho, hreset, hneutral,
    hseedAnchor, hseedNoActive⟩ :=
    existsProtectedLeaderReseedScheduleFor
      hpsi T K ring hn leader C hanchor
  obtain ⟨actual1, D, hresetExec, hclean, hleader, hDNoActive⟩ :=
    existsProtectedResetSweepSchedule_clears_allFor
      hpsi T K ring hn leader seeded hseedNoActive hreset hneutral
        hecho hseedAnchor
  have hexec := ProtectedLogicalExecutionFor.append T ring
    C seeded D (leaderReseedSchedule ring leader)
    (resetSweepSchedule ring (ring.rightNeighbor leader) (n - 1))
    actual0 actual1 hseedExec hresetExec
  have hword : leaderReseedSchedule ring leader ++
      resetSweepSchedule ring (ring.rightNeighbor leader) (n - 1) =
      leaderDrainReseedResetSweep ring leader := by
    rfl
  rw [hword] at hexec
  have hrestart := ProtectedLogicalExecutionFor.toRestartable_of_noActive
    T ring C (leaderDrainReseedResetSweep ring leader)
      (actual0 ++ actual1) D hexec hDNoActive
  have hlength := ProtectedLogicalExecutionFor.length_le T ring C
    (leaderDrainReseedResetSweep ring leader)
      (actual0 ++ actual1) D hexec
  rw [leaderDrainReseedResetSweep_length ring leader] at hlength
  exact ⟨actual0 ++ actual1, D, hrestart, hlength, hleader, hclean⟩

/-- The corrected pre-CHECK transition inherits the complete shielded
restartable comparison cleanup theorem.  This preserves only the designated
leader and global comparison neutrality; it does not assert uniqueness. -/
theorem exists_restartablePreCheckResetLeaderDrainReseedResetSweep_clears_all
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (leader : Fin n) (C : Fin n → ExpiringAgentState psi kappa tau)
    (hanchor : ProtectedLeaderAt hpsi C leader) :
    ∃ (actual : DetSchedule n)
      (D : Fin n → ExpiringAgentState psi kappa tau),
      RestartableExecutionFor
        (wallSweepPreCheckResetPathStallTransition hpsi kappa tau)
        ring C (leaderDrainReseedResetSweep ring leader) actual D ∧
      actual.length ≤
        (2 * n - 1) * (n + 1) + comparisonPathCount C ∧
      (D leader).core.erase.core.leader = true ∧
      ∀ i, ComparisonNeutral (D i).core.erase.core := by
  exact exists_restartableLeaderDrainReseedResetSweep_of_contract
    hpsi (wallSweepPreCheckResetPathStallTransition hpsi kappa tau)
      (preCheckResetProtectedCleanupContract hpsi)
      ring hn leader C hanchor

end PPLLWallSweepRestartableGeneric
