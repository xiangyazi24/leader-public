import Leader.Wu.WallSweep.EchoDrain

/-!
# Deterministic first-leader schedules for the barrier/probe kernel

The paper's first-leader phase needs a returning probe, not merely the static
existence of a barrier.  This source-kernel module isolates that mechanism for
the nondivisible branch.  It uses only the source-faithful follower/follower
behavior of `P'_psi`: a clockwise normalization pass either exposes a probe,
or a probe moving counterclockwise meets one of the unavoidable barriers.
-/

namespace PPLLPpsiLeaderCreationSchedule

open PPLL PPLLResearchFormulation PPLLWallSweepRepair
  PPLLWallSweepSchedule PPLLWallSweepEchoDrain
  PPLLNoCheckBirthConditionTwoGeometry
  PPLLWriteSeqPersistenceRegression PPLLWriteSeqRelocation

variable {n psi : Nat}

/-! ## Schedule words and raw target predicates -/

/-- One full clockwise pass followed by the first edge once more.  The final
retry is needed when the wrap interaction changes the root label and leaves
that root in phase zero. -/
def pPsiProbeSeedSchedule (ring : DirectedRing n) (root : Fin n) :
    DetSchedule n :=
  resetSweepSchedule ring root (n + 1)

/-- Prefix of the counterclockwise chase: at stage `steps` the scheduled
initiators are the offsets `n-1, n-2, ..., n-steps`. -/
def pPsiProbeChasePrefix (ring : DirectedRing n) (p : Fin n) :
    Nat → DetSchedule n
  | 0 => []
  | steps + 1 =>
      pPsiProbeChasePrefix ring p steps ++
        [groupOffset ring p (n - 1 - steps)]

/-- Every edge in counterclockwise order, starting with the edge entering the
current probe carrier. -/
def pPsiProbeChaseSchedule (ring : DirectedRing n) (p : Fin n) :
    DetSchedule n :=
  pPsiProbeChasePrefix ring p n

theorem pPsiProbeSeedSchedule_length (ring : DirectedRing n)
    (root : Fin n) :
    (pPsiProbeSeedSchedule ring root).length = n + 1 := by
  exact resetSweepSchedule_length ring root (n + 1)

theorem pPsiProbeChasePrefix_length (ring : DirectedRing n)
    (p : Fin n) (steps : Nat) :
    (pPsiProbeChasePrefix ring p steps).length = steps := by
  induction steps with
  | zero => rfl
  | succ steps ih => simp [pPsiProbeChasePrefix, ih]

theorem pPsiProbeChaseSchedule_length (ring : DirectedRing n)
    (p : Fin n) :
    (pPsiProbeChaseSchedule ring p).length = n := by
  exact pPsiProbeChasePrefix_length ring p n

/-- A raw P-prime configuration already contains a leader. -/
def RawHasLeader (C : Fin n → AgentState psi) : Prop :=
  ∃ i, (C i).leader = true

/-- A raw P-prime configuration contains a probe carrier. -/
def RawHasProbe (C : Fin n → AgentState psi) : Prop :=
  ∃ i, (C i).probe = true

/-- No agent currently carries the named Boolean control bit. -/
def RawLeaderless (C : Fin n → AgentState psi) : Prop :=
  ∀ i, (C i).leader = false

/-- No agent currently carries a probe. -/
def RawProbeless (C : Fin n → AgentState psi) : Prop :=
  ∀ i, (C i).probe = false

/-- Pointwise equality of the label projection. -/
def RawLabelFrame (C D : Fin n → AgentState psi) : Prop :=
  ∀ i, (D i).label = (C i).label

theorem RawLeaderless.of_not_hasLeader {C : Fin n → AgentState psi}
    (h : ¬ RawHasLeader C) : RawLeaderless C := by
  intro i
  cases hi : (C i).leader with
  | false => rfl
  | true => exact False.elim (h ⟨i, hi⟩)

theorem RawProbeless.of_not_hasProbe {C : Fin n → AgentState psi}
    (h : ¬ RawHasProbe C) : RawProbeless C := by
  intro i
  cases hi : (C i).probe with
  | false => rfl
  | true => exact False.elim (h ⟨i, hi⟩)

/-! ## Local barrier/probe equations -/

/-- P-prime never changes the initiator label, including across the prose
leader/probe wall. -/
theorem pPsiLeaderProbeWall_initiator_label
    (hpsi : psi > 0) (l r : AgentState psi) :
    (pPsiLeaderProbeWall hpsi l r).1.label = l.label := by
  simp [pPsiLeaderProbeWall, pPsi]

/-- With two followers and no responder probe, one P-prime interaction makes
the responder label the successor of the initiator label. -/
theorem pPsiLeaderProbeWall_responder_label_of_no_probe
    (hpsi : psi > 0) (l r : AgentState psi)
    (hl : l.leader = false) (hr : r.leader = false)
    (hp : r.probe = false) :
    (pPsiLeaderProbeWall hpsi l r).2.label =
      ⟨(l.label.val + 1) % psi, Nat.mod_lt _ hpsi⟩ := by
  rw [pPsiLeaderProbeWall_eq_pPsi_of_no_leaders hpsi l r hl hr]
  by_cases hbarrier :
      r.label ≠ ⟨(l.label.val + 1) % psi, Nat.mod_lt _ hpsi⟩
  · simp [pPsi, hbarrier, hp, hr]
  · have haligned := Decidable.not_not.mp hbarrier
    simpa [pPsi, hbarrier, hp] using haligned

/-- With two follower inputs, a follower responder after P-prime is necessarily
aligned with the unchanged initiator label.  The only follower/follower branch
that can leave a barrier uncorrected is exactly the branch that creates the
responder leader. -/
theorem pPsiLeaderProbeWall_responder_aligned_of_followers_of_output_follower
    (hpsi : psi > 0) (l r : AgentState psi)
    (hl : l.leader = false) (hr : r.leader = false)
    (hout : (pPsiLeaderProbeWall hpsi l r).2.leader = false) :
    (pPsiLeaderProbeWall hpsi l r).2.label =
      ⟨(l.label.val + 1) % psi, Nat.mod_lt _ hpsi⟩ := by
  rw [pPsiLeaderProbeWall_eq_pPsi_of_no_leaders hpsi l r hl hr]
  rw [pPsiLeaderProbeWall_eq_pPsi_of_no_leaders hpsi l r hl hr] at hout
  by_cases hbarrier : r.label ≠
      ⟨(l.label.val + 1) % psi, Nat.mod_lt _ hpsi⟩
  · by_cases hprobe : r.probe = true
    · simp [pPsi, hbarrier, hprobe] at hout
    · have hprobeFalse : r.probe = false := by
        cases hp : r.probe <;> simp_all
      simp [pPsi, hbarrier, hprobeFalse, hr]
  · simpa [pPsi, hbarrier] using Decidable.not_not.mp hbarrier

/-- With two follower inputs, every responder leader created by P-prime is the
barrier/probe birth and therefore has label zero. -/
theorem pPsiLeaderProbeWall_responder_label_zero_of_followers_of_output_leader
    (hpsi : psi > 0) (l r : AgentState psi)
    (hl : l.leader = false) (hr : r.leader = false)
    (hout : (pPsiLeaderProbeWall hpsi l r).2.leader = true) :
    (pPsiLeaderProbeWall hpsi l r).2.label = ⟨0, hpsi⟩ := by
  rw [pPsiLeaderProbeWall_eq_pPsi_of_no_leaders hpsi l r hl hr]
  rw [pPsiLeaderProbeWall_eq_pPsi_of_no_leaders hpsi l r hl hr] at hout
  have horigin := PPLLVerify.pPsi_new_responder_leader_requires_probe_barrier
    hpsi l r hout hr
  unfold isBarrier at horigin
  simp [pPsi, horigin.1, horigin.2]

/-- A barrier whose follower initiator is in phase zero immediately creates a
probe at that initiator when the responder has no probe. -/
theorem pPsiLeaderProbeWall_barrier_phase_zero_creates_probe
    (hpsi : psi > 0) (l r : AgentState psi)
    (hl : l.leader = false) (hr : r.leader = false)
    (hp : r.probe = false) (hphase : l.phase = false)
    (hbarrier : isBarrier hpsi l r) :
    (pPsiLeaderProbeWall hpsi l r).1.probe = true := by
  rw [pPsiLeaderProbeWall_eq_pPsi_of_no_leaders hpsi l r hl hr]
  unfold isBarrier at hbarrier
  simp [pPsi, hbarrier, hp, hphase, hl]

/-- A follower responder on a barrier is returned in phase zero whenever it
does not already carry the leader-producing probe. -/
theorem pPsiLeaderProbeWall_barrier_responder_phase_zero
    (hpsi : psi > 0) (l r : AgentState psi)
    (hl : l.leader = false) (hr : r.leader = false)
    (hp : r.probe = false) (hbarrier : isBarrier hpsi l r) :
    (pPsiLeaderProbeWall hpsi l r).2.phase = false := by
  rw [pPsiLeaderProbeWall_eq_pPsi_of_no_leaders hpsi l r hl hr]
  unfold isBarrier at hbarrier
  simp [pPsi, hbarrier, hp, hr]

/-- On an aligned follower/follower edge, a responder probe moves exactly one
position counterclockwise without changing either label. -/
theorem pPsiLeaderProbeWall_aligned_probe_moves_left
    (hpsi : psi > 0) (l r : AgentState psi)
    (hl : l.leader = false) (hr : r.leader = false)
    (haligned : r.label =
      ⟨(l.label.val + 1) % psi, Nat.mod_lt _ hpsi⟩)
    (hprobe : r.probe = true) :
    (pPsiLeaderProbeWall hpsi l r).1.probe = true ∧
      (pPsiLeaderProbeWall hpsi l r).2.probe = false ∧
      (pPsiLeaderProbeWall hpsi l r).1.label = l.label ∧
      (pPsiLeaderProbeWall hpsi l r).2.label = r.label := by
  rw [pPsiLeaderProbeWall_eq_pPsi_of_no_leaders hpsi l r hl hr]
  simp [pPsi, haligned, hprobe]

/-- Moving a probe on an aligned follower edge does not create either endpoint
leader. -/
theorem pPsiLeaderProbeWall_aligned_probe_leaders_false
    (hpsi : psi > 0) (l r : AgentState psi)
    (hl : l.leader = false) (hr : r.leader = false)
    (haligned : r.label =
      ⟨(l.label.val + 1) % psi, Nat.mod_lt _ hpsi⟩)
    (hprobe : r.probe = true) :
    (pPsiLeaderProbeWall hpsi l r).1.leader = false ∧
      (pPsiLeaderProbeWall hpsi l r).2.leader = false := by
  rw [pPsiLeaderProbeWall_eq_pPsi_of_no_leaders hpsi l r hl hr]
  simp [pPsi, haligned, hprobe, hl, hr]

/-- Follower/follower P-prime interactions cannot create a leader unless a
responder probe meets a barrier. -/
theorem pPsiLeaderProbeWall_leaders_false_of_no_responder_probe
    (hpsi : psi > 0) (l r : AgentState psi)
    (hl : l.leader = false) (hr : r.leader = false)
    (hp : r.probe = false) :
    (pPsiLeaderProbeWall hpsi l r).1.leader = false ∧
      (pPsiLeaderProbeWall hpsi l r).2.leader = false := by
  rw [pPsiLeaderProbeWall_eq_pPsi_of_no_leaders hpsi l r hl hr]
  simp [pPsi, hp, hl, hr]

/-- Existing leaders survive the barrier/probe kernel on either endpoint. -/
theorem pPsiLeaderProbeWall_initiator_leader_of_true
    (hpsi : psi > 0) (l r : AgentState psi)
    (hl : l.leader = true) :
    (pPsiLeaderProbeWall hpsi l r).1.leader = true := by
  simp [pPsiLeaderProbeWall, pPsi, hl]

theorem pPsiLeaderProbeWall_responder_leader_of_true
    (hpsi : psi > 0) (l r : AgentState psi)
    (hr : r.leader = true) :
    (pPsiLeaderProbeWall hpsi l r).2.leader = true := by
  simp [pPsiLeaderProbeWall, pPsi, hr]

/-- A local P-prime step preserves the existence of any old leader. -/
theorem RawHasLeader.localStep_pPsiLeaderProbeWall
    (hpsi : psi > 0) (ring : DirectedRing n)
    {C : Fin n → AgentState psi} (e : Fin n)
    (h : RawHasLeader C) :
    RawHasLeader
      (localStep ring (pPsiLeaderProbeWall hpsi) C e) := by
  obtain ⟨i, hi⟩ := h
  by_cases hie : i = e
  · subst i
    refine ⟨e, ?_⟩
    simp only [PPLLResearchFormulation.localStep, if_pos]
    exact pPsiLeaderProbeWall_initiator_leader_of_true
      hpsi (C e) (C (ring.rightNeighbor e)) hi
  · by_cases hij : i = ring.rightNeighbor e
    · subst i
      refine ⟨ring.rightNeighbor e, ?_⟩
      simp only [PPLLResearchFormulation.localStep, hie, if_false, if_true]
      exact pPsiLeaderProbeWall_responder_leader_of_true
        hpsi (C e) (C (ring.rightNeighbor e)) hi
    · refine ⟨i, ?_⟩
      simpa only [PPLLResearchFormulation.localStep, hie, hij,
        if_false] using hi

/-- Taking a whole number of ring offsets returns to the starting position. -/
@[simp] theorem groupOffset_period (ring : DirectedRing n) (p : Fin n) :
    groupOffset ring p n = p := by
  apply Fin.ext
  simp [groupOffset, Nat.mod_eq_of_lt p.isLt]

/-! ## Counterclockwise probe chase -/

/-- The original label edges already crossed by a counterclockwise chase.
After `steps` interactions these are precisely the offsets from `n-steps` to
`n-1`. -/
def RawAlignedSuffix (hpsi : psi > 0) (ring : DirectedRing n)
    (p : Fin n) (C : Fin n → AgentState psi) (steps : Nat) : Prop :=
  ∀ k, n - steps ≤ k → k < n →
    (C (groupOffset ring p (k + 1))).label =
      ⟨((C (groupOffset ring p k)).label.val + 1) % psi,
        Nat.mod_lt _ hpsi⟩

/-- Chase invariant.  Either a leader has already appeared, or the original
labels are unchanged, the probe is at the next responder, and every edge
crossed so far was aligned. -/
structure ProbeChaseState (hpsi : psi > 0) (ring : DirectedRing n)
    (p : Fin n) (initial current : Fin n → AgentState psi)
    (steps : Nat) : Prop where
  steps_le : steps ≤ n
  progress : RawHasLeader current ∨
    (RawLeaderless current ∧
      RawLabelFrame initial current ∧
      (current (groupOffset ring p (n - steps))).probe = true ∧
      RawAlignedSuffix hpsi ring p initial steps)

/-- A probe carrier in a leaderless configuration initializes the reverse
chase before any edge is crossed. -/
theorem ProbeChaseState.zero
    (hpsi : psi > 0) (ring : DirectedRing n) (p : Fin n)
    (C : Fin n → AgentState psi)
    (hleaderless : RawLeaderless C) (hprobe : (C p).probe = true) :
    ProbeChaseState hpsi ring p C C 0 := by
  refine ⟨by omega, Or.inr ⟨hleaderless, ?_, ?_, ?_⟩⟩
  · intro i
    rfl
  · simpa using hprobe
  · intro k hlo hhi
    omega

/-- One reverse edge either creates a leader at a probed barrier or moves the
probe left while extending the aligned suffix by one edge. -/
theorem ProbeChaseState.step
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (p : Fin n) (initial current : Fin n → AgentState psi)
    (steps : Nat)
    (hstate : ProbeChaseState hpsi ring p initial current steps)
    (hnext : steps < n) :
    let e := groupOffset ring p (n - 1 - steps)
    let D := localStep ring (pPsiLeaderProbeWall hpsi) current e
    ProbeChaseState hpsi ring p initial D (steps + 1) := by
  let e := groupOffset ring p (n - 1 - steps)
  let j := groupOffset ring p (n - steps)
  have hneighbor : ring.rightNeighbor e = j := by
    rw [show e = groupOffset ring p (n - 1 - steps) by rfl,
      rightNeighbor_groupOffset]
    congr 1
    omega
  have hje : j ≠ e := by
    rw [← hneighbor]
    exact rightNeighbor_ne_self_of_one_lt ring hn e
  let q := pPsiLeaderProbeWall hpsi (current e) (current j)
  let D := localStep ring (pPsiLeaderProbeWall hpsi) current e
  change ProbeChaseState hpsi ring p initial D (steps + 1)
  refine ⟨by omega, ?_⟩
  rcases hstate.progress with hleader | hrun
  · exact Or.inl (hleader.localStep_pPsiLeaderProbeWall hpsi ring e)
  · rcases hrun with ⟨hleaderless, hlabels, hprobe, halignedOld⟩
    have hjProbe : (current j).probe = true := by
      simpa [j] using hprobe
    have heFollower : (current e).leader = false := hleaderless e
    have hjFollower : (current j).leader = false := hleaderless j
    by_cases hbarrier : isBarrier hpsi (current e) (current j)
    · have hbirth : q.2.leader = true := by
        exact pPsiLeaderProbeWall_preserves_barrier_birth
          hpsi (current e) (current j) heFollower hjFollower
            hjProbe hbarrier
      refine Or.inl ⟨j, ?_⟩
      simp [D, q, PPLLResearchFormulation.localStep, hneighbor, hje]
      exact hbirth
    · have haligned : (current j).label =
          ⟨((current e).label.val + 1) % psi,
            Nat.mod_lt _ hpsi⟩ :=
        Decidable.not_not.mp hbarrier
      have hmove := pPsiLeaderProbeWall_aligned_probe_moves_left
        hpsi (current e) (current j) heFollower hjFollower
          haligned hjProbe
      have hleaders := pPsiLeaderProbeWall_aligned_probe_leaders_false
        hpsi (current e) (current j) heFollower hjFollower
          haligned hjProbe
      refine Or.inr ⟨?_, ?_, ?_, ?_⟩
      · intro i
        by_cases hie : i = e
        · subst i
          simp [D, q, PPLLResearchFormulation.localStep]
          rw [hneighbor]
          exact hleaders.1
        · by_cases hij : i = j
          · subst i
            simp [D, q, PPLLResearchFormulation.localStep,
              hneighbor, hje]
            exact hleaders.2
          · simpa [D, PPLLResearchFormulation.localStep,
              hie, hneighbor, hij] using hleaderless i
      · intro i
        by_cases hie : i = e
        · subst i
          simp [D, q, PPLLResearchFormulation.localStep]
          rw [hneighbor]
          exact hmove.2.2.1.trans (hlabels e)
        · by_cases hij : i = j
          · subst i
            simp [D, q, PPLLResearchFormulation.localStep,
              hneighbor, hje]
            exact hmove.2.2.2.trans (hlabels j)
          · simpa [D, PPLLResearchFormulation.localStep,
              hie, hneighbor, hij] using hlabels i
      · have hePos : groupOffset ring p (n - (steps + 1)) = e := by
          congr 1
          omega
        rw [hePos]
        simp [D, q, PPLLResearchFormulation.localStep]
        rw [hneighbor]
        exact hmove.1
      · intro k hkLower hkUpper
        by_cases hkNew : k = n - 1 - steps
        · subst k
          have heq : groupOffset ring p (n - 1 - steps) = e := rfl
          have hjeq : groupOffset ring p (n - 1 - steps + 1) = j := by
            change groupOffset ring p (n - 1 - steps + 1) =
              groupOffset ring p (n - steps)
            congr 1
            omega
          have halignedInitial : (initial j).label =
              ⟨((initial e).label.val + 1) % psi,
                Nat.mod_lt _ hpsi⟩ := by
            simpa only [hlabels e, hlabels j] using haligned
          simpa only [heq, hjeq] using halignedInitial
        · apply halignedOld k
          · omega
          · exact hkUpper

private theorem runLocalSchedule_append
    {Q : Type} (ring : DirectedRing n) (T : Q → Q → Q × Q)
    (C : Fin n → Q) (s t : DetSchedule n) :
    runLocalSchedule ring T C (s ++ t) =
      runLocalSchedule ring T (runLocalSchedule ring T C s) t := by
  induction s generalizing C with
  | nil => rfl
  | cons e rest ih =>
      simp only [List.cons_append, runLocalSchedule]
      exact ih _

/-- Every bounded reverse prefix realizes the corresponding chase invariant. -/
theorem pPsiProbeChasePrefix_state
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (C : Fin n → AgentState psi) (p : Fin n)
    (hleaderless : RawLeaderless C) (hprobe : (C p).probe = true)
    (steps : Nat) (hsteps : steps ≤ n) :
    ProbeChaseState hpsi ring p C
      (runLocalSchedule ring (pPsiLeaderProbeWall hpsi) C
        (pPsiProbeChasePrefix ring p steps)) steps := by
  induction steps with
  | zero =>
      simpa [pPsiProbeChasePrefix, runLocalSchedule] using
        ProbeChaseState.zero hpsi ring p C hleaderless hprobe
  | succ steps ih =>
      have hlt : steps < n := by omega
      have hprev := ih (by omega)
      rw [pPsiProbeChasePrefix, runLocalSchedule_append]
      simp only [runLocalSchedule]
      exact ProbeChaseState.step hpsi ring hn p C _ steps hprev hlt

/-- On a nondivisible ring, a probe in any leaderless raw configuration meets
an unavoidable barrier within one reverse circuit and creates a leader. -/
theorem pPsiProbeChaseSchedule_creates_leader
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (hndvd : ¬ psi ∣ n) (C : Fin n → AgentState psi)
    (p : Fin n) (hleaderless : RawLeaderless C)
    (hprobe : (C p).probe = true) :
    RawHasLeader
      (runLocalSchedule ring (pPsiLeaderProbeWall hpsi) C
        (pPsiProbeChaseSchedule ring p)) := by
  have hstate := pPsiProbeChasePrefix_state hpsi ring hn C p
    hleaderless hprobe n (by omega)
  change ProbeChaseState hpsi ring p C
    (runLocalSchedule ring (pPsiLeaderProbeWall hpsi) C
      (pPsiProbeChaseSchedule ring p)) n at hstate
  rcases hstate.progress with hleader | hrun
  · exact hleader
  · rcases hrun with ⟨_leaderless, _labels, _probe, haligned⟩
    have hall : ∀ i : Fin n,
        (C (ring.rightNeighbor i)).label =
          ⟨((C i).label.val + 1) % psi, Nat.mod_lt _ hpsi⟩ := by
      intro i
      let k := cwDist ring p i
      have hk : k < n := cwDist_lt ring p i
      have hpos : groupOffset ring p k = i := by
        simpa [groupOffset, cwPos] using cwPos_cwDist ring p i
      have hedge := haligned k (by omega) hk
      rw [← hpos, rightNeighbor_groupOffset]
      exact hedge
    exact False.elim
      (hndvd (dvd_of_all_successor_labels hpsi ring C hall))

/-! ## Clockwise probe seed -/

/-- The label spine normalized by the first `steps` clockwise interactions.
Only non-wrap prefixes are used, so later interactions do not revisit a
normalized responder. -/
def RawAlignedPrefix (hpsi : psi > 0) (ring : DirectedRing n)
    (root : Fin n) (C : Fin n → AgentState psi) (steps : Nat) : Prop :=
  ∀ k, k < steps →
    (C (groupOffset ring root (k + 1))).label =
      ⟨((C (groupOffset ring root k)).label.val + 1) % psi,
        Nat.mod_lt _ hpsi⟩

/-- If every edge except one is aligned on a nondivisible ring, the remaining
edge is necessarily a barrier. -/
theorem barrier_of_not_dvd_of_other_edges_aligned
    (hpsi : psi > 0) (ring : DirectedRing n) (hndvd : ¬ psi ∣ n)
    (C : Fin n → AgentState psi) (target : Fin n)
    (hother : ∀ i, i ≠ target →
      (C (ring.rightNeighbor i)).label =
        ⟨((C i).label.val + 1) % psi, Nat.mod_lt _ hpsi⟩) :
    isBarrier hpsi (C target) (C (ring.rightNeighbor target)) := by
  apply Classical.byContradiction
  intro hnot
  have htarget : (C (ring.rightNeighbor target)).label =
      ⟨((C target).label.val + 1) % psi,
        Nat.mod_lt _ hpsi⟩ := Decidable.not_not.mp hnot
  apply hndvd
  apply dvd_of_all_successor_labels hpsi ring C
  intro i
  by_cases hit : i = target
  · subst i
    exact htarget
  · exact hother i hit

/-- One non-wrap interaction extends the normalized label spine.  Earlier
edges remain aligned because the only possibly changed label belongs to the
new responder. -/
theorem rawAlignedPrefix_step
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (root : Fin n) (C : Fin n → AgentState psi) (steps : Nat)
    (hsteps : steps + 1 < n)
    (hleaderless : RawLeaderless C) (hprobeless : RawProbeless C)
    (haligned : RawAlignedPrefix hpsi ring root C steps) :
    let e := groupOffset ring root steps
    let D := localStep ring (pPsiLeaderProbeWall hpsi) C e
    RawAlignedPrefix hpsi ring root D (steps + 1) := by
  let e := groupOffset ring root steps
  let j := groupOffset ring root (steps + 1)
  have hneighbor : ring.rightNeighbor e = j := by
    exact rightNeighbor_groupOffset ring root steps
  have hje : j ≠ e := by
    rw [← hneighbor]
    exact rightNeighbor_ne_self_of_one_lt ring hn e
  let q := pPsiLeaderProbeWall hpsi (C e) (C j)
  let D := localStep ring (pPsiLeaderProbeWall hpsi) C e
  have hrightLabel : q.2.label =
      ⟨((C e).label.val + 1) % psi, Nat.mod_lt _ hpsi⟩ :=
    pPsiLeaderProbeWall_responder_label_of_no_probe
      hpsi (C e) (C j) (hleaderless e) (hleaderless j)
        (hprobeless j)
  have hframe : ∀ i, i ≠ j → (D i).label = (C i).label := by
    intro i hij
    by_cases hie : i = e
    · subst i
      simp [D, q, PPLLResearchFormulation.localStep]
      rw [hneighbor]
      exact pPsiLeaderProbeWall_initiator_label hpsi (C e) (C j)
    · simpa [D, PPLLResearchFormulation.localStep, hie,
        hneighbor, hij]
  change RawAlignedPrefix hpsi ring root D (steps + 1)
  intro k hk
  by_cases hnew : k = steps
  · subst k
    have heq : groupOffset ring root steps = e := rfl
    have hjeq : groupOffset ring root (steps + 1) = j := rfl
    have hleftLabel : (D e).label = (C e).label := hframe e hje.symm
    have hright : (D j).label = q.2.label := by
      simp [D, q, PPLLResearchFormulation.localStep, hneighbor, hje]
    have hnewAligned : (D j).label =
        ⟨((D e).label.val + 1) % psi, Nat.mod_lt _ hpsi⟩ := by
      calc
        (D j).label = q.2.label := hright
        _ = ⟨((C e).label.val + 1) % psi,
              Nat.mod_lt _ hpsi⟩ := hrightLabel
        _ = ⟨((D e).label.val + 1) % psi,
              Nat.mod_lt _ hpsi⟩ := by
                simpa only [hleftLabel]
    simpa only [heq, hjeq] using hnewAligned
  · have hkOld : k < steps := by omega
    have hkBound : k < n := by omega
    have hksBound : k + 1 < n := by omega
    have hkNe : groupOffset ring root k ≠ j := by
      apply groupOffset_ne_of_lt ring root hkBound hsteps
      omega
    have hksNe : groupOffset ring root (k + 1) ≠ j := by
      apply groupOffset_ne_of_lt ring root hksBound hsteps
      omega
    have hold := haligned k hkOld
    have hleftFrame := hframe (groupOffset ring root k) hkNe
    have hrightFrame := hframe (groupOffset ring root (k + 1)) hksNe
    simpa only [hleftFrame, hrightFrame] using hold

/-- Every non-wrap clockwise prefix either has already produced a leader or
probe, or ends leaderless/probeless with a normalized label spine.  The first
alternative records the successful prefix itself, so no persistence premise
is hidden in the statement. -/
theorem pPsiProbeSeedPrefix_outcome
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (root : Fin n) (C : Fin n → AgentState psi)
    (steps : Nat) (hsteps : steps < n) :
    (∃ word : DetSchedule n,
      word.length ≤ steps ∧
      (let D := runLocalSchedule ring (pPsiLeaderProbeWall hpsi) C word;
       RawHasLeader D ∨ RawHasProbe D)) ∨
    (let D := runLocalSchedule ring (pPsiLeaderProbeWall hpsi) C
        (resetSweepSchedule ring root steps);
      RawLeaderless D ∧ RawProbeless D ∧
        RawAlignedPrefix hpsi ring root D steps) := by
  induction steps with
  | zero =>
      by_cases hleader : RawHasLeader C
      · refine Or.inl ⟨[], by simp, ?_⟩
        change RawHasLeader C ∨ RawHasProbe C
        exact Or.inl hleader
      · by_cases hprobe : RawHasProbe C
        · refine Or.inl ⟨[], by simp, ?_⟩
          change RawHasLeader C ∨ RawHasProbe C
          exact Or.inr hprobe
        · refine Or.inr ?_
          simp only [resetSweepSchedule, runLocalSchedule]
          exact ⟨RawLeaderless.of_not_hasLeader hleader,
            RawProbeless.of_not_hasProbe hprobe,
            by intro k hk; omega⟩
  | succ steps ih =>
      have hprevBound : steps < n := by omega
      rcases ih hprevBound with hfound | hquiet
      · exact Or.inl ⟨hfound.choose, by omega, hfound.choose_spec.2⟩
      · let M := runLocalSchedule ring (pPsiLeaderProbeWall hpsi) C
          (resetSweepSchedule ring root steps)
        have hquietM : RawLeaderless M ∧ RawProbeless M ∧
            RawAlignedPrefix hpsi ring root M steps := by
          simpa [M] using hquiet
        let e := groupOffset ring root steps
        let D := localStep ring (pPsiLeaderProbeWall hpsi) M e
        have hrunD : runLocalSchedule ring (pPsiLeaderProbeWall hpsi) C
            (resetSweepSchedule ring root (steps + 1)) = D := by
          simp [resetSweepSchedule, runLocalSchedule_append, M, D, e]
          rfl
        by_cases hleaderD : RawHasLeader D
        · refine Or.inl ⟨resetSweepSchedule ring root (steps + 1),
            ?_, ?_⟩
          · rw [resetSweepSchedule_length]
            omega
          · rw [hrunD]
            exact Or.inl hleaderD
        · by_cases hprobeD : RawHasProbe D
          · refine Or.inl ⟨resetSweepSchedule ring root (steps + 1),
              ?_, ?_⟩
            · rw [resetSweepSchedule_length]
              omega
            · rw [hrunD]
              exact Or.inr hprobeD
          · refine Or.inr ?_
            rw [hrunD]
            exact ⟨RawLeaderless.of_not_hasLeader hleaderD,
              RawProbeless.of_not_hasProbe hprobeD,
              rawAlignedPrefix_step hpsi ring hn root M steps hsteps
                hquietM.1 hquietM.2.1 hquietM.2.2⟩

/-- On a nondivisible ring, at most one full clockwise pass plus the root edge
produces either a leader or a probe from an arbitrary raw configuration. -/
theorem exists_pPsiProbeSeed_leader_or_probe_of_not_dvd
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (hndvd : ¬ psi ∣ n) (C : Fin n → AgentState psi) :
    ∃ word : DetSchedule n,
      word.length ≤ n + 1 ∧
      let D := runLocalSchedule ring (pPsiLeaderProbeWall hpsi) C word
      RawHasLeader D ∨ RawHasProbe D := by
  let root : Fin n := ⟨0, by omega⟩
  have hprefix := pPsiProbeSeedPrefix_outcome hpsi ring hn root C
    (n - 1) (by omega)
  rcases hprefix with hfound | hquiet
  · exact ⟨hfound.choose, by omega, hfound.choose_spec.2⟩
  · let seedWord := resetSweepSchedule ring root (n - 1)
    let M := runLocalSchedule ring (pPsiLeaderProbeWall hpsi) C seedWord
    have hquietM : RawLeaderless M ∧ RawProbeless M ∧
        RawAlignedPrefix hpsi ring root M (n - 1) := by
      simpa [seedWord, M] using hquiet
    let last := groupOffset ring root (n - 1)
    have hneighborLast : ring.rightNeighbor last = root := by
      rw [show last = groupOffset ring root (n - 1) by rfl,
        rightNeighbor_groupOffset]
      calc
        groupOffset ring root (n - 1 + 1) =
            groupOffset ring root n := by congr 1 <;> omega
        _ = root := groupOffset_period ring root
    have hrootLast : root ≠ last := by
      intro h
      have hself : ring.rightNeighbor last = last := by
        rw [hneighborLast, h]
      exact (rightNeighbor_ne_self_of_one_lt ring hn last) hself
    have hclosing : isBarrier hpsi (M last) (M root) := by
      rw [← hneighborLast]
      apply barrier_of_not_dvd_of_other_edges_aligned
        hpsi ring hndvd M last
      intro i hiLast
      let k := cwDist ring root i
      have hk : k < n := cwDist_lt ring root i
      have hpos : groupOffset ring root k = i := by
        simpa [groupOffset, cwPos] using cwPos_cwDist ring root i
      have hkPrefix : k < n - 1 := by
        have hkNe : k ≠ n - 1 := by
          intro hkeq
          apply hiLast
          rw [← hpos, hkeq]
        omega
      have hedge := hquietM.2.2 k hkPrefix
      rw [← hpos, rightNeighbor_groupOffset]
      exact hedge
    let qWrap := pPsiLeaderProbeWall hpsi (M last) (M root)
    let D := localStep ring (pPsiLeaderProbeWall hpsi) M last
    have hrunD : runLocalSchedule ring (pPsiLeaderProbeWall hpsi) C
        (resetSweepSchedule ring root n) = D := by
      have hnshape : n - 1 + 1 = n := by omega
      have hschedEq : resetSweepSchedule ring root (n - 1 + 1) =
          resetSweepSchedule ring root n :=
        congrArg (resetSweepSchedule ring root) hnshape
      rw [← hschedEq, resetSweepSchedule]
      rw [runLocalSchedule_append]
      simp only [runLocalSchedule]
      change localStep ring (pPsiLeaderProbeWall hpsi) M last = D
      rfl
    by_cases hleaderD : RawHasLeader D
    · refine ⟨resetSweepSchedule ring root n, ?_, ?_⟩
      · rw [resetSweepSchedule_length]
        omega
      · rw [hrunD]
        exact Or.inl hleaderD
    · by_cases hprobeD : RawHasProbe D
      · refine ⟨resetSweepSchedule ring root n, ?_, ?_⟩
        · rw [resetSweepSchedule_length]
          omega
        · rw [hrunD]
          exact Or.inr hprobeD
      · have hleaderlessD := RawLeaderless.of_not_hasLeader hleaderD
        have hprobelessD := RawProbeless.of_not_hasProbe hprobeD
        have hwrapLeftLabel : qWrap.1.label = (M last).label :=
          pPsiLeaderProbeWall_initiator_label hpsi (M last) (M root)
        have hwrapRightLabel : qWrap.2.label =
            ⟨((M last).label.val + 1) % psi,
              Nat.mod_lt _ hpsi⟩ :=
          pPsiLeaderProbeWall_responder_label_of_no_probe
            hpsi (M last) (M root) (hquietM.1 last)
              (hquietM.1 root) (hquietM.2.1 root)
        have hDLast : D last = qWrap.1 := by
          simp [D, qWrap, PPLLResearchFormulation.localStep]
          rw [hneighborLast]
        have hDRoot : D root = qWrap.2 := by
          simp [D, qWrap, PPLLResearchFormulation.localStep,
            hneighborLast, hrootLast]
        have hclosingAlignedD : (D root).label =
            ⟨((D last).label.val + 1) % psi,
              Nat.mod_lt _ hpsi⟩ := by
          have hlastLabel : (D last).label = (M last).label := by
            rw [hDLast]
            exact hwrapLeftLabel
          rw [hDRoot]
          simpa only [hlastLabel] using hwrapRightLabel
        have hrootPhase : (D root).phase = false := by
          rw [hDRoot]
          exact pPsiLeaderProbeWall_barrier_responder_phase_zero
            hpsi (M last) (M root) (hquietM.1 last)
              (hquietM.1 root) (hquietM.2.1 root) hclosing
        have hlabelFrameExceptRoot : ∀ i, i ≠ root →
            (D i).label = (M i).label := by
          intro i hiRoot
          by_cases hiLast : i = last
          · subst i
            exact (congrArg AgentState.label hDLast).trans hwrapLeftLabel
          · simpa [D, PPLLResearchFormulation.localStep, hiLast,
              hneighborLast, hiRoot]
        have hrootBarrier : isBarrier hpsi (D root)
            (D (ring.rightNeighbor root)) := by
          apply barrier_of_not_dvd_of_other_edges_aligned
            hpsi ring hndvd D root
          intro i hiRoot
          let k := cwDist ring root i
          have hk : k < n := cwDist_lt ring root i
          have hpos : groupOffset ring root k = i := by
            simpa [groupOffset, cwPos] using cwPos_cwDist ring root i
          have hkPos : 0 < k := by
            have hkNe : k ≠ 0 := by
              intro hkZero
              apply hiRoot
              rw [← hpos, hkZero]
              apply Fin.ext
              exact Nat.mod_eq_of_lt root.isLt
            omega
          by_cases hkLast : k = n - 1
          · have hiLast : i = last := by
              rw [← hpos, hkLast]
            rw [hiLast, hneighborLast]
            exact hclosingAlignedD
          · have hkPrefix : k < n - 1 := by omega
            have hedge := hquietM.2.2 k hkPrefix
            have hleftFrame :
                (D (groupOffset ring root k)).label =
                  (M (groupOffset ring root k)).label := by
              apply hlabelFrameExceptRoot
              apply groupOffset_ne_of_lt ring root hk (by omega : 0 < n)
              omega
            have hrightFrame :
                (D (groupOffset ring root (k + 1))).label =
                  (M (groupOffset ring root (k + 1))).label := by
              apply hlabelFrameExceptRoot
              apply groupOffset_ne_of_lt ring root (by omega)
                (by omega : 0 < n)
              omega
            rw [← hpos, rightNeighbor_groupOffset]
            simpa only [hleftFrame, hrightFrame] using hedge
        let qRoot := pPsiLeaderProbeWall hpsi
          (D root) (D (ring.rightNeighbor root))
        let E := localStep ring (pPsiLeaderProbeWall hpsi) D root
        have hrootProbe : qRoot.1.probe = true :=
          pPsiLeaderProbeWall_barrier_phase_zero_creates_probe
            hpsi (D root) (D (ring.rightNeighbor root))
              (hleaderlessD root) (hleaderlessD (ring.rightNeighbor root))
              (hprobelessD (ring.rightNeighbor root)) hrootPhase hrootBarrier
        have hrunE : runLocalSchedule ring (pPsiLeaderProbeWall hpsi) C
            (pPsiProbeSeedSchedule ring root) = E := by
          change runLocalSchedule ring (pPsiLeaderProbeWall hpsi) C
            (resetSweepSchedule ring root (n + 1)) = E
          rw [resetSweepSchedule, runLocalSchedule_append]
          simp only [runLocalSchedule]
          rw [hrunD]
          rw [groupOffset_period]
        refine ⟨pPsiProbeSeedSchedule ring root, ?_, ?_⟩
        · rw [pPsiProbeSeedSchedule_length]
          omega
        · rw [hrunE]
          exact Or.inr ⟨root, by
            simp [E, qRoot, PPLLResearchFormulation.localStep]
            exact hrootProbe⟩

/-! ## Source-kernel first-leader capstone -/

/-- The nondivisible P-prime branch has a deterministic first-leader word of
length at most `2n+1`.  The proof first seeds a leader or probe, then, only if
needed, sends the probe once counterclockwise around the ring. -/
theorem exists_pPsiLeaderProbeWall_hasLeader_of_not_dvd
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (hndvd : ¬ psi ∣ n) (C : Fin n → AgentState psi) :
    ∃ word : DetSchedule n,
      word.length ≤ 2 * n + 1 ∧
      RawHasLeader
        (runLocalSchedule ring (pPsiLeaderProbeWall hpsi) C word) := by
  obtain ⟨seed, hseedLength, hseed⟩ :=
    exists_pPsiProbeSeed_leader_or_probe_of_not_dvd
      hpsi ring hn hndvd C
  let S := runLocalSchedule ring (pPsiLeaderProbeWall hpsi) C seed
  have hseedS : RawHasLeader S ∨ RawHasProbe S := by
    simpa [S] using hseed
  rcases hseedS with hleaderS | hprobeS
  · refine ⟨seed, ?_, hleaderS⟩
    omega
  · by_cases hleaderS : RawHasLeader S
    · refine ⟨seed, ?_, hleaderS⟩
      omega
    · obtain ⟨p, hp⟩ := hprobeS
      let chase := pPsiProbeChaseSchedule ring p
      have hchase : RawHasLeader
          (runLocalSchedule ring (pPsiLeaderProbeWall hpsi) S chase) :=
        pPsiProbeChaseSchedule_creates_leader hpsi ring hn hndvd S p
          (RawLeaderless.of_not_hasLeader hleaderS) hp
      refine ⟨seed ++ chase, ?_, ?_⟩
      · rw [List.length_append]
        have hchaseLength : chase.length = n := by
          exact pPsiProbeChaseSchedule_length ring p
        rw [hchaseLength]
        omega
      · rw [runLocalSchedule_append]
        exact hchase

end PPLLPpsiLeaderCreationSchedule
