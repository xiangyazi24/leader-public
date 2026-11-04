import Leader.Wu.Birth.PpsiLeaderCreationSchedule

/-!
# Divisible P-prime label geometry

A non-wrapping clockwise sweep processes the edges

`root -> root+1, ..., root+(n-2) -> root+(n-1)`.

At every processed edge, literal P-prime either creates a responder leader or
makes that responder's label the successor of the unchanged initiator label.
Consequently a stopped prefix either already has a leader or has an aligned
prefix.  When `psi | n`, an aligned prefix of length `n-1` also forces the
unprocessed closing edge into the root to be aligned.
-/

namespace PPLLPpsiLabelGeometry

open PPLL PPLLResearchFormulation PPLLWallSweepRepair
  PPLLPpsiLeaderCreationSchedule
  PPLLNoCheckBirthConditionTwoGeometry
  PPLLWriteSeqPersistenceRegression PPLLWriteSeqRelocation

variable {n psi : Nat}

/-! ## Target geometry and schedule words -/

/-- Every directed edge has the cyclic successor label. -/
def AllSuccessorLabels (hpsi : psi > 0) (ring : DirectedRing n)
    (C : Fin n -> AgentState psi) : Prop :=
  forall i,
    (C (ring.rightNeighbor i)).label =
      ⟨((C i).label.val + 1) % psi, Nat.mod_lt _ hpsi⟩

/-- The first `steps` clockwise edges beginning at `root`, written directly as
an `ofFn` word.  This prefix object lets the scheduler stop at the first birth.
-/
def labelSweepPrefixSchedule (ring : DirectedRing n) (root : Fin n)
    (steps : Nat) : DetSchedule n :=
  List.ofFn (fun i : Fin steps => groupOffset ring root i.val)

/-- The requested complete non-wrapping clockwise word. -/
def labelSweepSchedule (ring : DirectedRing n) (root : Fin n) :
    DetSchedule n :=
  List.ofFn
    (fun i : Fin (n - 1) => groupOffset ring root i.val)

@[simp] theorem labelSweepPrefixSchedule_length
    (ring : DirectedRing n) (root : Fin n) (steps : Nat) :
    (labelSweepPrefixSchedule ring root steps).length = steps := by
  simp [labelSweepPrefixSchedule]

@[simp] theorem labelSweepSchedule_length
    (ring : DirectedRing n) (root : Fin n) :
    (labelSweepSchedule ring root).length = n - 1 := by
  simp [labelSweepSchedule]

@[simp] theorem labelSweepSchedule_eq_prefix
    (ring : DirectedRing n) (root : Fin n) :
    labelSweepSchedule ring root =
      labelSweepPrefixSchedule ring root (n - 1) := by
  rfl

/-- Expose one additional edge at the end of an `ofFn` prefix. -/
theorem labelSweepPrefixSchedule_succ
    (ring : DirectedRing n) (root : Fin n) (steps : Nat) :
    labelSweepPrefixSchedule ring root (steps + 1) =
      labelSweepPrefixSchedule ring root steps ++
        [groupOffset ring root steps] := by
  unfold labelSweepPrefixSchedule
  exact
    (show
      List.ofFn
          (fun i : Fin (steps + 1) => groupOffset ring root i.val) =
        List.ofFn (fun i : Fin steps => groupOffset ring root i.val) ++
          [groupOffset ring root steps]
      from List.ofFn_succ_last)

private theorem runLocalSchedule_append_labelSweep
    {Q : Type} (ring : DirectedRing n) (T : Q -> Q -> Q × Q)
    (C : Fin n -> Q) (left right : DetSchedule n) :
    runLocalSchedule ring T C (left ++ right) =
      runLocalSchedule ring T
        (runLocalSchedule ring T C left) right := by
  induction left generalizing C with
  | nil => rfl
  | cons e rest ih =>
      simp only [List.cons_append, runLocalSchedule]
      exact ih _

private theorem groupOffset_zero_eq
    (ring : DirectedRing n) (root : Fin n) :
    groupOffset ring root 0 = root := by
  apply Fin.ext
  simp [groupOffset, Nat.mod_eq_of_lt root.isLt]

/-! ## Exact local P-prime behavior -/

/-- Exact barrier dichotomy on follower inputs.

The phrase "reset the responder to zero" applies only to the probe-birth
branch.  In the nonbirth branch the responder is aligned and its *phase* is
reset to zero. -/
theorem pPsi_barrier_birth_or_align
    (hpsi : psi > 0) (l r : AgentState psi)
    (hl : l.leader = false) (hr : r.leader = false)
    (hbarrier : isBarrier hpsi l r) :
    let q := pPsi hpsi l r
    (q.2.leader = true ∧ q.2.label = ⟨0, hpsi⟩) ∨
      (q.2.leader = false ∧
        q.2.label =
          ⟨(l.label.val + 1) % psi, Nat.mod_lt _ hpsi⟩ ∧
        q.2.phase = false) := by
  unfold isBarrier at hbarrier
  cases hp : r.probe <;>
    simp [pPsi, hbarrier, hp, hl, hr]

/-- Literal P-prime never changes the initiator label. -/
private theorem pPsi_initiator_label
    (hpsi : psi > 0) (l r : AgentState psi) :
    (pPsi hpsi l r).1.label = l.label := by
  exact PPLLVerify.pPsi_initiator_label_eq hpsi l r

/-- On follower inputs, the only way the P-prime responder can fail to leave
with the successor label is to leave as the newly born leader.  No probeless
premise is required. -/
private theorem pPsi_responder_aligned_of_followers_of_output_follower
    (hpsi : psi > 0) (l r : AgentState psi)
    (hl : l.leader = false) (hr : r.leader = false)
    (hout : (pPsi hpsi l r).2.leader = false) :
    (pPsi hpsi l r).2.label =
      ⟨(l.label.val + 1) % psi, Nat.mod_lt _ hpsi⟩ := by
  rw [← pPsiLeaderProbeWall_eq_pPsi_of_no_leaders
    hpsi l r hl hr] at hout ⊢
  exact
    pPsiLeaderProbeWall_responder_aligned_of_followers_of_output_follower
      hpsi l r hl hr hout

/-! ## The unprocessed-suffix induction -/

/-- One non-wrap sweep edge either creates the first leader or extends the
already aligned prefix by one edge.

After `steps` successful interactions, edges `0, ..., steps-1` are aligned.
The next interaction processes edge `steps`; if no leader is born, edges
`0, ..., steps` are aligned.  A repaired barrier also leaves the new frontier
agent in phase zero by `pPsi_barrier_birth_or_align`; it does not generally
leave that agent at label zero. -/
theorem rawAlignedPrefix_step_or_leader
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (root : Fin n) (C : Fin n -> AgentState psi) (steps : Nat)
    (hsteps : steps + 1 < n)
    (hleaderless : RawLeaderless C)
    (haligned : RawAlignedPrefix hpsi ring root C steps) :
    let e := groupOffset ring root steps
    let D := localStep ring (pPsi hpsi) C e
    RawHasLeader D ∨
      (RawLeaderless D ∧
        RawAlignedPrefix hpsi ring root D (steps + 1)) := by
  let e := groupOffset ring root steps
  let j := groupOffset ring root (steps + 1)
  have hneighbor : ring.rightNeighbor e = j := by
    exact rightNeighbor_groupOffset ring root steps
  have hje : j ≠ e := by
    rw [← hneighbor]
    exact rightNeighbor_ne_self_of_one_lt ring hn e
  let q := pPsi hpsi (C e) (C j)
  let D := localStep ring (pPsi hpsi) C e
  change RawHasLeader D ∨
    (RawLeaderless D ∧
      RawAlignedPrefix hpsi ring root D (steps + 1))
  by_cases hleaderD : RawHasLeader D
  · exact Or.inl hleaderD
  · have hleaderlessD : RawLeaderless D :=
      RawLeaderless.of_not_hasLeader hleaderD
    have hright : D j = q.2 := by
      simp [D, q, PPLLResearchFormulation.localStep, hneighbor, hje]
    have hqFollower : q.2.leader = false := by
      rw [← hright]
      exact hleaderlessD j
    have hrightLabel : q.2.label =
        ⟨((C e).label.val + 1) % psi, Nat.mod_lt _ hpsi⟩ :=
      pPsi_responder_aligned_of_followers_of_output_follower
        hpsi (C e) (C j) (hleaderless e) (hleaderless j) hqFollower
    have hframe : forall i, i ≠ j -> (D i).label = (C i).label := by
      intro i hij
      by_cases hie : i = e
      · subst i
        simp [D, q, PPLLResearchFormulation.localStep]
        rw [hneighbor]
        exact pPsi_initiator_label hpsi (C e) (C j)
      · simpa [D, PPLLResearchFormulation.localStep, hie,
          hneighbor, hij]
    refine Or.inr ⟨hleaderlessD, ?_⟩
    intro k hk
    by_cases hnew : k = steps
    · subst k
      have heq : groupOffset ring root steps = e := rfl
      have hjeq : groupOffset ring root (steps + 1) = j := rfl
      have hleftLabel : (D e).label = (C e).label :=
        hframe e hje.symm
      have hrightEq : (D j).label = q.2.label :=
        congrArg AgentState.label hright
      have hnewAligned : (D j).label =
          ⟨((D e).label.val + 1) % psi,
            Nat.mod_lt _ hpsi⟩ := by
        calc
          (D j).label = q.2.label := hrightEq
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
      have hrightFrame :=
        hframe (groupOffset ring root (k + 1)) hksNe
      simpa only [hleftFrame, hrightFrame] using hold

/-- Every bounded clockwise prefix has a stopped outcome.  The first branch
returns the exact successful prefix; the second branch has consumed exactly
`steps` units of the unprocessed-suffix rank. -/
theorem stopped_labelSweepPrefix_outcome
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (root : Fin n) (C : Fin n -> AgentState psi)
    (hleaderless : RawLeaderless C)
    (steps : Nat) (hsteps : steps < n) :
    (exists t, t <= steps ∧
      RawHasLeader
        (runLocalSchedule ring (pPsi hpsi) C
          (labelSweepPrefixSchedule ring root t))) ∨
    (let D := runLocalSchedule ring (pPsi hpsi) C
        (labelSweepPrefixSchedule ring root steps);
      RawLeaderless D ∧
        RawAlignedPrefix hpsi ring root D steps) := by
  induction steps with
  | zero =>
      refine Or.inr ?_
      simpa [labelSweepPrefixSchedule, runLocalSchedule] using
        (show RawLeaderless C ∧
            RawAlignedPrefix hpsi ring root C 0 from
          ⟨hleaderless, by intro k hk; omega⟩)
  | succ steps ih =>
      have hprevBound : steps < n := by omega
      rcases ih hprevBound with hfound | hquiet
      · exact Or.inl
          ⟨hfound.choose, by omega, hfound.choose_spec.2⟩
      · let M := runLocalSchedule ring (pPsi hpsi) C
          (labelSweepPrefixSchedule ring root steps)
        have hquietM : RawLeaderless M ∧
            RawAlignedPrefix hpsi ring root M steps := by
          simpa [M] using hquiet
        let e := groupOffset ring root steps
        let D := localStep ring (pPsi hpsi) M e
        have hrunD : runLocalSchedule ring (pPsi hpsi) C
            (labelSweepPrefixSchedule ring root (steps + 1)) = D := by
          rw [labelSweepPrefixSchedule_succ,
            runLocalSchedule_append_labelSweep]
          rfl
        have hlocal := rawAlignedPrefix_step_or_leader
          hpsi ring hn root M steps (by omega) hquietM.1 hquietM.2
        change RawHasLeader D ∨
          (RawLeaderless D ∧
            RawAlignedPrefix hpsi ring root D (steps + 1)) at hlocal
        rcases hlocal with hleaderD | hquietD
        · refine Or.inl ⟨steps + 1, by omega, ?_⟩
          rw [hrunD]
          exact hleaderD
        · refine Or.inr ?_
          rw [hrunD]
          exact hquietD

/-! ## Closing the one unprocessed edge -/

/-- Labels along an aligned open prefix have the expected affine form. -/
private theorem rawAlignedPrefix_label_formula
    (hpsi : psi > 0) (ring : DirectedRing n) (root : Fin n)
    (C : Fin n -> AgentState psi) (steps : Nat)
    (haligned : RawAlignedPrefix hpsi ring root C steps) :
    forall k, k <= steps ->
      (C (groupOffset ring root k)).label.val =
        ((C root).label.val + k) % psi := by
  intro k
  induction k with
  | zero =>
      intro _
      rw [groupOffset_zero_eq]
      simpa using (Nat.mod_eq_of_lt (C root).label.isLt).symm
  | succ k ih =>
      intro hk
      have hklt : k < steps := by omega
      have hedge := haligned k hklt
      have hv := congrArg Fin.val hedge
      change
        (C (groupOffset ring root (k + 1))).label.val =
          ((C (groupOffset ring root k)).label.val + 1) % psi at hv
      have ihk := ih (by omega)
      rw [ihk] at hv
      calc
        (C (groupOffset ring root (k + 1))).label.val =
            (((C root).label.val + k) % psi + 1) % psi := hv
        _ = ((C root).label.val + (k + 1)) % psi := by
          simpa [Nat.add_assoc] using
            mod_add_one (C root).label.val k psi

/-- Divisibility closes the predecessor-to-root edge after the first `n-1`
edges have been aligned. -/
private theorem rawAlignedPrefix_closing_edge
    (hpsi : psi > 0) (ring : DirectedRing n) (root : Fin n)
    (C : Fin n -> AgentState psi)
    (hdiv : psi ∣ n)
    (haligned : RawAlignedPrefix hpsi ring root C (n - 1)) :
    (C root).label =
      ⟨((C (groupOffset ring root (n - 1))).label.val + 1) % psi,
        Nat.mod_lt _ hpsi⟩ := by
  have hnpos : 0 < n := ring.hn
  have hlast := rawAlignedPrefix_label_formula
    hpsi ring root C (n - 1) haligned (n - 1) (by omega)
  have hnmod : n % psi = 0 :=
    Nat.dvd_iff_mod_eq_zero.mp hdiv
  have hcycle : ((C root).label.val + n) % psi =
      (C root).label.val := by
    calc
      ((C root).label.val + n) % psi =
          ((C root).label.val % psi + n % psi) % psi :=
        Nat.add_mod _ _ _
      _ = ((C root).label.val + 0) % psi := by
        rw [Nat.mod_eq_of_lt (C root).label.isLt, hnmod]
      _ = (C root).label.val := by
        simpa using Nat.mod_eq_of_lt (C root).label.isLt
  have hstep := mod_add_one (C root).label.val (n - 1) psi
  have hadd : (C root).label.val + (n - 1) + 1 =
      (C root).label.val + n := by omega
  rw [hadd] at hstep
  apply Fin.ext
  change (C root).label.val =
    ((C (groupOffset ring root (n - 1))).label.val + 1) % psi
  rw [hlast]
  exact (hstep.trans hcycle).symm

/-- The aligned open chain plus `psi | n` gives cyclic successor labels on
all physical edges. -/
theorem allSuccessorLabels_of_rawAlignedPrefix
    (hpsi : psi > 0) (ring : DirectedRing n) (root : Fin n)
    (C : Fin n -> AgentState psi)
    (hdiv : psi ∣ n)
    (haligned : RawAlignedPrefix hpsi ring root C (n - 1)) :
    AllSuccessorLabels hpsi ring C := by
  have hnpos : 0 < n := ring.hn
  have hclosing := rawAlignedPrefix_closing_edge
    hpsi ring root C hdiv haligned
  have hlastNeighbor :
      ring.rightNeighbor (groupOffset ring root (n - 1)) = root := by
    rw [rightNeighbor_groupOffset]
    have hpred : n - 1 + 1 = n := by omega
    rw [hpred, groupOffset_period]
  intro i
  let k := cwDist ring root i
  have hk : k < n := cwDist_lt ring root i
  have hpos : groupOffset ring root k = i := by
    simpa [groupOffset, cwPos] using cwPos_cwDist ring root i
  by_cases hlast : k = n - 1
  · have hiLast : i = groupOffset ring root (n - 1) := by
      rw [← hpos, hlast]
    rw [hiLast, hlastNeighbor]
    exact hclosing
  · have hkPrefix : k < n - 1 := by omega
    have hedge := haligned k hkPrefix
    rw [← hpos, rightNeighbor_groupOffset]
    exact hedge

/-! ## Divisible stopped-sweep capstone -/

/-- Rooted strengthened form: the successful word is a prefix of the requested
clockwise word and has length at most `n-1`. -/
theorem exists_stopped_labelSweep_or_leader_from_root
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (hdiv : psi ∣ n) (root : Fin n)
    (C : Fin n -> AgentState psi)
    (hleaderless : RawLeaderless C) :
    exists (word : DetSchedule n) (D : Fin n -> AgentState psi),
      word.length <= n - 1 ∧
      D = runLocalSchedule ring (pPsi hpsi) C word ∧
      (RawHasLeader D ∨ AllSuccessorLabels hpsi ring D) := by
  have hout := stopped_labelSweepPrefix_outcome
    hpsi ring hn root C hleaderless (n - 1) (by omega)
  rcases hout with hfound | hquiet
  · obtain ⟨t, ht, hleader⟩ := hfound
    let word := labelSweepPrefixSchedule ring root t
    let D := runLocalSchedule ring (pPsi hpsi) C word
    refine ⟨word, D, ?_, rfl, Or.inl ?_⟩
    · simpa [word, labelSweepPrefixSchedule] using ht
    · simpa [D, word] using hleader
  · let word := labelSweepSchedule ring root
    let D := runLocalSchedule ring (pPsi hpsi) C word
    have hquietD : RawLeaderless D ∧
        RawAlignedPrefix hpsi ring root D (n - 1) := by
      simpa [D, word, labelSweepSchedule,
        labelSweepPrefixSchedule] using hquiet
    refine ⟨word, D, ?_, rfl, Or.inr ?_⟩
    · simp [word, labelSweepSchedule]
    · exact allSuccessorLabels_of_rawAlignedPrefix
        hpsi ring root D hdiv hquietD.2

/-- Requested unrooted presentation.  The witness chooses physical index zero
as the sweep root.  The explicit `hdiv` premise is indispensable. -/
theorem exists_stopped_labelSweep_or_leader
    (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (hdiv : psi ∣ n)
    (C : Fin n -> AgentState psi)
    (hleaderless : RawLeaderless C) :
    exists (word : DetSchedule n) (D : Fin n -> AgentState psi),
      D = runLocalSchedule ring (pPsi hpsi) C word ∧
      (RawHasLeader D ∨ AllSuccessorLabels hpsi ring D) := by
  let root : Fin n := ⟨0, by omega⟩
  obtain ⟨word, D, _hlength, hD, hout⟩ :=
    exists_stopped_labelSweep_or_leader_from_root
      hpsi ring hn hdiv root C hleaderless
  exact ⟨word, D, hD, hout⟩

end PPLLPpsiLabelGeometry
