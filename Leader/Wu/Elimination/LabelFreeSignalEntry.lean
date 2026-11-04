import Leader.Wu.Elimination.AdjacentLeaderPeaceful

/-!
# Finite entry into signal order on the actual separated physical layout

The row is the frozen `LabelFreeElimination.step`. The layout is derived from
the actual leader bits. All ranks, stopping tags, and layout witnesses are
audit data; no physical field or scheduler symbol is added.
-/

namespace LabelFreeSignalEntry

open PPLLRepair LDSinkGapCleanup LDSinkKernelC LDSinkProtectedAbsorption
open PPLLNoCheckBirthConditionTwoPhysical PPLLNoCheckBirthConditionTwoGeometry
open PPLLNoCheckBirthOutputLegitimacy PPLLNoCheckBirthConditionTwoProtocol
open K2OutputSafety K2GlobalGapClosure K2CyclicLayout
open StateBoundUnifiedCell LabelFreeElimination FiniteUniformStoppingTree

set_option autoImplicit false

variable {n ψ κ k : Nat}

/-- A nonzero bullet has a positive signal weakly clockwise before or at
its actual next leader. Index zero belongs to the preceding gap. -/
def BadAt (G : GapFrame n) (C : Fin n → AgentState ψ) (i : Nat) : Prop :=
  1 ≤ i ∧ i ≤ G.d ∧ (C (G.pos i)).bullet ≠ 0 ∧
    ∃ j, i ≤ j ∧ j ≤ G.d ∧ (C (G.pos j)).signal_B = 1

noncomputable def badTop (G : GapFrame n) (C : Fin n → AgentState ψ) : Nat := by
  classical
  exact topIdx (fun i => decide (BadAt G C i)) G.d

theorem badTop_le (G : GapFrame n) (C : Fin n → AgentState ψ) :
    badTop G C ≤ G.d := topIdx_le _ _

theorem badAt_le_top (G : GapFrame n) (C : Fin n → AgentState ψ)
    {i : Nat} (hi : BadAt G C i) : i ≤ badTop G C := by
  classical
  exact topIdx_ge _ _ _ hi.2.1 (by simpa using hi)

theorem badTop_bad (G : GapFrame n) (C : Fin n → AgentState ψ)
    (h : 0 < badTop G C) : BadAt G C (badTop G C) := by
  classical
  exact of_decide_eq_true (topIdx_holds _ _ h)

theorem badTop_le_of (G : GapFrame n) (C : Fin n → AgentState ψ) (t : Nat)
    (h : ∀ i, BadAt G C i → i ≤ t) : badTop G C ≤ t := by
  classical
  apply topIdx_le_of
  intro i hit _
  simp only [decide_eq_false_iff_not]
  intro hi
  exact Nat.not_le_of_lt hit (h i hi)

theorem badTop_zero_iff (G : GapFrame n) (C : Fin n → AgentState ψ) :
    badTop G C = 0 ↔ GapSignalBelowBullets G C := by
  constructor
  · intro hz i j hi hid hb hij hjd
    rcases fin2_cases (C (G.pos j)).signal_B with hs | hs
    · exact hs
    · have hh := badAt_le_top G C ⟨hi, hid, hb, j, hij, hjd, hs⟩
      omega
  · intro h
    apply Nat.eq_zero_of_le_zero
    apply badTop_le_of
    intro i hi
    obtain ⟨hi1, hid, hb, j, hij, hjd, hs⟩ := hi
    have hz := h i j hi1 hid hb hij hjd
    rw [hz] at hs
    cases hs

/-! The following facts concern the actual local row at modulus one. -/

/-- Local bookkeeping facts, proved below for the concrete kernel. -/
structure EntryRowFacts (l r : AgentState 1) (q : AgentState 1 × AgentState 1) : Prop where
  signal_left : q.1.signal_B = 1 → l.signal_B = 1
  signal_right : q.2.signal_B = 1 →
    l.signal_B = 1 ∨ r.signal_B = 1 ∨ l.leader = true
  clear_follower : l.leader = false → q.2.bullet = 0
  clear_victim : l.leader = true → r.leader = false → q.1.leader = true →
    q.2.bullet = 0
  fire_left_zero : l.leader = true → q.1.signal_B = 0
  fire_right_zero : l.leader = false → r.leader = true → r.signal_B = 1 →
    q.1.signal_B = 0 ∧ q.2.signal_B = 0
  idle_left : l.leader = false → ¬ (r.leader = true ∧ r.signal_B = 1) →
    r.bullet = 0 → q.1.bullet = l.bullet
  move_left : l.leader = false → ¬ (r.leader = true ∧ r.signal_B = 1) →
    r.bullet ≠ 0 → q.1.signal_B = 0 ∧ q.2.signal_B = r.signal_B



set_option synthInstance.maxSize 512 in
private instance (l r : AgentState 1) (q : AgentState 1 × AgentState 1) :
    Decidable (EntryRowFacts l r q) :=
  decidable_of_iff ((q.1.signal_B = 1 → l.signal_B = 1) ∧
    (q.2.signal_B = 1 →
    l.signal_B = 1 ∨ r.signal_B = 1 ∨ l.leader = true) ∧
    (l.leader = false → q.2.bullet = 0) ∧
    (l.leader = true → r.leader = false → q.1.leader = true →
    q.2.bullet = 0) ∧
    (l.leader = true → q.1.signal_B = 0) ∧
    (l.leader = false → r.leader = true → r.signal_B = 1 →
    q.1.signal_B = 0 ∧ q.2.signal_B = 0) ∧
    (l.leader = false → ¬ (r.leader = true ∧ r.signal_B = 1) →
    r.bullet = 0 → q.1.bullet = l.bullet) ∧
    (l.leader = false → ¬ (r.leader = true ∧ r.signal_B = 1) →
    r.bullet ≠ 0 → q.1.signal_B = 0 ∧ q.2.signal_B = r.signal_B))
    ⟨(fun h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2⟩),
      (fun h => ⟨h.signal_left, h.signal_right, h.clear_follower, h.clear_victim, h.fire_left_zero, h.fire_right_zero, h.idle_left, h.move_left⟩)⟩

private theorem entryRowFacts_finite (ll ls rl rs : Bool) (lb rb : Fin 3)
    (lz rz : Fin 2) :
    let l := PeaceView.toState (ψ := 1) ⟨ll, 0, ls, lb, lz⟩
    let r := PeaceView.toState (ψ := 1) ⟨rl, 0, rs, rb, rz⟩
    EntryRowFacts l r (sinkKernelC (by decide) l r) := by
  revert ll ls rl rs lb rb lz rz
  decide +kernel

/-- No signal-order or post-state safety premise is used in this row audit. -/
theorem entryRowFacts (l r : AgentState 1) :
    EntryRowFacts l r (sinkKernelC (by decide) l r) := by
  have h := entryRowFacts_finite l.leader l.shield r.leader r.shield
    l.bullet r.bullet l.signal_B r.signal_B
  have he := signal_kernel (by decide) l r (Or.inl (Subsingleton.elim _ _))
  change (signalView (sinkKernelC (by decide) l r).1,
    signalView (sinkKernelC (by decide) l r).2) =
      sinkKernelC (by decide) (signalView l) (signalView r) at he
  change EntryRowFacts (signalView l) (signalView r)
    (sinkKernelC (by decide) (signalView l) (signalView r)) at h
  rw [← he] at h
  exact ⟨h.signal_left, h.signal_right, h.clear_follower, h.clear_victim,
    h.fire_left_zero, h.fire_right_zero, h.idle_left, h.move_left⟩


private theorem step_left (G : GapFrame n) (C : Fin n → AgentState 1) (t : Nat) :
    rawStep (by decide) G.ring C (G.pos t) (G.pos t) =
      (sinkKernelC (by decide) (C (G.pos t)) (C (G.pos (t + 1)))).1 := by
  simp [rawStep, updatePair, GapFrame.rightNeighbor_pos]

private theorem step_right (G : GapFrame n) (C : Fin n → AgentState 1)
    (t : Nat) (ht : t + 1 < n) :
    rawStep (by decide) G.ring C (G.pos t) (G.pos (t + 1)) =
      (sinkKernelC (by decide) (C (G.pos t)) (C (G.pos (t + 1)))).2 := by
  have hne := G.pos_ne ht (by omega) (show t + 1 ≠ t by omega)
  simp [rawStep, updatePair, GapFrame.rightNeighbor_pos, hne]

private theorem incoming (G : GapFrame n) (i : Nat) (hi : 1 ≤ i) :
    G.ring.rightNeighbor (G.pos (i - 1)) = G.pos i := by
  rw [GapFrame.rightNeighbor_pos, Nat.sub_add_cancel hi]

private theorem step_other (G : GapFrame n) (C : Fin n → AgentState 1)
    (e : Fin n) (i : Nat) (hi : 1 ≤ i)
    (hl : e ≠ G.pos i) (hr : e ≠ G.pos (i - 1)) :
    rawStep (by decide) G.ring C e (G.pos i) = C (G.pos i) := by
  apply updatePair_other
  · exact Ne.symm hl
  · intro h
    apply hr
    apply rightNeighbor_injective G.ring
    rw [incoming G i hi]
    exact h.symm

/-- A positive new signal inside the fixed frame has a positive old source
at the same cell or its predecessor; only the victim can supply a leader bit. -/
theorem signal_origin (G : GapFrame n) (C : Fin n → AgentState 1)
    (hI : GapInteriorFollowers G C) (e : Fin n) (j : Nat)
    (hj1 : 1 ≤ j) (hjd : j ≤ G.d)
    (hs : (rawStep (by decide) G.ring C e (G.pos j)).signal_B = 1) :
    (C (G.pos j)).signal_B = 1 ∨
    (1 < j ∧ e = G.pos (j - 1) ∧ (C (G.pos (j - 1))).signal_B = 1) ∨
    (j = 1 ∧ e = G.pos 0) := by
  by_cases hl : e = G.pos j
  · subst e
    rw [step_left] at hs
    exact Or.inl ((entryRowFacts _ _).signal_left hs)
  · by_cases hr : e = G.pos (j - 1)
    · subst e
      have heq : j - 1 + 1 = j := Nat.sub_add_cancel hj1
      have hrow := step_right G C (j - 1) (by have := G.hdn; omega)
      rw [heq] at hrow
      rw [hrow] at hs
      rcases (entryRowFacts _ _).signal_right hs with hs | hs | hs
      · by_cases hj : j = 1
        · exact Or.inr (Or.inr ⟨hj, by simp only [hj, Nat.sub_self]⟩)
        · exact Or.inr (Or.inl ⟨by omega, rfl, hs⟩)
      · exact Or.inl hs
      · by_cases hj : j = 1
        · exact Or.inr (Or.inr ⟨hj, by simp only [hj, Nat.sub_self]⟩)
        · have hf := hI (j - 1) (by omega) (by omega)
          rw [hf] at hs
          cases hs
    · rw [step_other G C e j hj1 hl hr] at hs
      exact Or.inl hs

private theorem signal_witness_back (G : GapFrame n) (C : Fin n → AgentState 1)
    (hI : GapInteriorFollowers G C) (e : Fin n) (i j : Nat)
    (hi : 1 ≤ i) (hij : i ≤ j) (hjd : j ≤ G.d)
    (he : e ≠ G.pos (i - 1))
    (hs : (rawStep (by decide) G.ring C e (G.pos j)).signal_B = 1) :
    ∃ s, i ≤ s ∧ s ≤ G.d ∧ (C (G.pos s)).signal_B = 1 := by
  rcases signal_origin G C hI e j (by omega) hjd hs with hs | ⟨_, heq, hs⟩ | ⟨hj, heq⟩
  · exact ⟨j, hij, hjd, hs⟩
  · have hne : i ≠ j := by intro h; subst j; exact he heq
    exact ⟨j - 1, by omega, by omega, hs⟩
  · have hi1 : i = 1 := by omega
    exact (he (by rw [hi1]; exact heq)).elim

/-- On a nondeleting gap edge, the responder contains no bullet afterwards.
This includes the actual protected absorption and dummy sink at the victim. -/
theorem responder_empty (G : GapFrame n) (C : Fin n → AgentState 1)
    (hE : GapEndpointsPresent G C) (hI : GapInteriorFollowers G C)
    (i : Nat) (hi : 1 ≤ i) (hid : i ≤ G.d)
    (hkeep : ¬ EndpointDeleted G
      (rawStep (by decide) G.ring C (G.pos (i - 1)))) :
    (rawStep (by decide) G.ring C (G.pos (i - 1)) (G.pos i)).bullet = 0 := by
  have heq : i - 1 + 1 = i := Nat.sub_add_cancel hi
  have hrow := step_right G C (i - 1) (by have := G.hdn; omega)
  rw [heq] at hrow
  rw [hrow]
  by_cases hi1 : i = 1
  · subst i
    have hlive : (rawStep (by decide) G.ring C (G.pos 0) (G.pos 0)).leader = true := by
      cases hl : (rawStep (by decide) G.ring C (G.pos 0) (G.pos 0)).leader
      · exact (hkeep (Or.inl hl)).elim
      · rfl
    rw [step_left] at hlive
    exact (entryRowFacts _ _).clear_victim hE.1 (hI 1 (by omega) G.hd) hlive
  · exact (entryRowFacts _ _).clear_follower (hI (i - 1) (by omega) (by omega))

/-- Every bad output bullet comes from an old bad bullet at the same site or
one site to its right. Fresh FIRE bullets cannot supply the second case.
This statement is confined to the old, nondeleting physical gap. -/
theorem badAt_step_origin (G : GapFrame n) (C : Fin n → AgentState 1)
    (hE : GapEndpointsPresent G C) (hI : GapInteriorFollowers G C)
    (e : Fin n) (hkeep : ¬ EndpointDeleted G (rawStep (by decide) G.ring C e))
    (i : Nat) (hbad : BadAt G (rawStep (by decide) G.ring C e) i) :
    BadAt G C i ∨ (i < G.d ∧ e = G.pos i ∧ BadAt G C (i + 1)) := by
  obtain ⟨hi, hid, hb, j, hij, hjd, hs⟩ := hbad
  have hin : i < n := Nat.lt_of_le_of_lt hid G.hdn
  have hnot : e ≠ G.pos (i - 1) := by
    intro he
    subst e
    exact hb (responder_empty G C hE hI i hi hid hkeep)
  by_cases he : e = G.pos i
  · subst e
    by_cases hid' : i = G.d
    · have hj : j = i := by omega
      subst j
      rw [step_left] at hs
      have hz := (entryRowFacts (C (G.pos i)) (C (G.pos (i + 1)))).fire_left_zero
        (by rw [hid']; exact hE.2)
      rw [hz] at hs
      cases hs
    · have hit : i < G.d := by omega
      have hl := hI i hi hit
      have hleft := step_left G C i
      have hright := step_right G C i (by have := G.hdn; omega)
      by_cases hf : (C (G.pos (i + 1))).leader = true ∧
          (C (G.pos (i + 1))).signal_B = 1
      · have hlast : i + 1 = G.d := by
          apply Classical.byContradiction
          intro hh
          have hfol := hI (i + 1) (by omega) (by omega)
          rw [hfol] at hf
          cases hf.1
        have hz := (entryRowFacts _ _).fire_right_zero hl hf.1 hf.2
        have hj : j = i ∨ j = i + 1 := by omega
        rcases hj with hj | hj
        · rw [hj, hleft, hz.1] at hs
          cases hs
        · rw [hj, hright, hz.2] at hs
          cases hs
      · by_cases hrb : (C (G.pos (i + 1))).bullet = 0
        · have hb' : (C (G.pos i)).bullet ≠ 0 := by
            rw [hleft, (entryRowFacts _ _).idle_left hl hf hrb] at hb
            exact hb
          exact Or.inl ⟨hi, hid, hb', signal_witness_back G C hI _ i j hi hij hjd hnot hs⟩
        · have hz := (entryRowFacts _ _).move_left hl hf hrb
          have hjne : j ≠ i := by
            intro hj
            rw [hj, hleft, hz.1] at hs
            cases hs
          apply Or.inr
          refine ⟨hit, rfl, by omega, by omega, hrb, j, by omega, hjd, ?_⟩
          by_cases hj : j = i + 1
          · rw [hj, hright, hz.2] at hs
            simpa [hj] using hs
          · rw [step_other G C (G.pos i) j (by omega)
                (G.pos_ne hin (by have := G.hdn; omega) (by omega))
                (G.pos_ne hin (by have := G.hdn; omega) (by omega))] at hs
            exact hs
  · have hb' : (C (G.pos i)).bullet ≠ 0 := by
      rw [step_other G C e i hi he hnot] at hb
      exact hb
    exact Or.inl ⟨hi, hid, hb', signal_witness_back G C hI e i j hi hij hjd hnot hs⟩


/-- Every edge is nonincreasing until an actual endpoint deletion. -/
theorem badTop_step_le (G : GapFrame n) (C : Fin n → AgentState 1)
    (hE : GapEndpointsPresent G C) (hI : GapInteriorFollowers G C)
    (e : Fin n) (hkeep : ¬ EndpointDeleted G (rawStep (by decide) G.ring C e)) :
    badTop G (rawStep (by decide) G.ring C e) ≤ badTop G C := by
  apply badTop_le_of
  intro i hi
  rcases badAt_step_origin G C hE hI e hkeep i hi with hh | ⟨_, _, hh⟩
  · exact badAt_le_top G C hh
  · have := badAt_le_top G C hh
    omega

/-- The actual predecessor edge of the greatest bad bullet strictly lowers
its rank, unless that very successor already deletes a gap endpoint. -/
theorem badTop_target (G : GapFrame n) (C : Fin n → AgentState 1)
    (hE : GapEndpointsPresent G C) (hI : GapInteriorFollowers G C)
    (hp : 0 < badTop G C) :
    EndpointDeleted G (rawStep (by decide) G.ring C (G.pos (badTop G C - 1))) ∨
      badTop G (rawStep (by decide) G.ring C (G.pos (badTop G C - 1))) < badTop G C := by
  classical
  by_cases hd : EndpointDeleted G
      (rawStep (by decide) G.ring C (G.pos (badTop G C - 1)))
  · exact Or.inl hd
  · apply Or.inr
    have hle := badTop_step_le G C hE hI _ hd
    have ht := badTop_le G C
    have hh := badTop_le_of G
      (rawStep (by decide) G.ring C (G.pos (badTop G C - 1))) (badTop G C - 1)
      (fun i hi => by
        rcases badAt_step_origin G C hE hI _ hd i hi with hi' | ⟨hid, he, _⟩
        · have hil := badAt_le_top G C hi'
          have hne : i ≠ badTop G C := by
            intro heq
            subst i
            exact hi.2.2.1 (responder_empty G C hE hI _ hp ht hd)
          omega
        · have heq := G.pos_inj (by have := G.hdn; omega)
            (by have := G.hdn; omega) he
          omega)
    omega

/-- Only the real count and physical nonadjacency are required for entry. -/
structure SeparatedClass (ring : DirectedRing n) (k : Nat)
    (C : Fin n → UCell ψ κ) : Prop where
  two : 2 ≤ k
  count : K2FiniteProgress.count C = k
  separated : Separated ring (physicalConfig C)

/-- The existing cyclic-layout constructor is fed the sorted actual leaders.
No gap enumeration, signal order, or label arithmetic is an input field. -/
def layout (ring : DirectedRing n) (C : Fin n → UCell ψ κ)
    (hC : SeparatedClass ring k C) : CyclicLayout n k :=
  enumerationLayout ring (physicalConfig C) (leaderAt (physicalConfig C) hC.count)
    hC.two (leaderAt_strict _ hC.count) (leaderAt_leader _ hC.count) hC.separated

theorem layout_real (ring : DirectedRing n) (C : Fin n → UCell ψ κ)
    (hC : SeparatedClass ring k C) (i : Fin k) :
    GapEndpointsPresent ((layout ring C hC).gap i) (physicalConfig C) ∧
      GapInteriorFollowers ((layout ring C hC).gap i) (physicalConfig C) := by
  constructor
  · change ((physicalConfig C) (arcPos ring (leaderAt _ hC.count i) 0)).leader = true ∧
      ((physicalConfig C) (arcPos ring (leaderAt _ hC.count i)
        (gapDistance (leaderAt _ hC.count) i))).leader = true
    rw [arcPos_zero, arcPos_distance ring _ (leaderAt_strict _ hC.count) i]
    exact ⟨leaderAt_leader _ hC.count i, leaderAt_leader _ hC.count _⟩
  · intro t ht htd
    change ((physicalConfig C) (arcPos ring (leaderAt _ hC.count i) t)).leader = false
    cases hl : ((physicalConfig C) (arcPos ring (leaderAt _ hC.count i) t)).leader
    · rfl
    · obtain ⟨j, hj⟩ := leaderAt_complete (physicalConfig C) hC.count _ hl
      exact (arcPos_interior_ne ring _ (leaderAt_strict _ hC.count)
        i j t ht htd hj.symm).elim

private theorem pos_zero (G : GapFrame n) : G.pos 0 = G.low := by
  apply Fin.ext
  simp [GapFrame.pos, Nat.mod_eq_of_lt G.low.isLt]

/-- Two genuine next-leader frames with the same left endpoint coincide.
This proves coverage for *every* physical frame, not only the sorted list. -/
theorem frame_unique {σ : Nat} (G H : GapFrame n) (C : Fin n → AgentState σ)
    (hG : GapEndpointsPresent G C) (hGI : GapInteriorFollowers G C)
    (hH : GapEndpointsPresent H C) (hHI : GapInteriorFollowers H C)
    (hl : G.low = H.low) : G = H := by
  have hpos : ∀ t, G.pos t = H.pos t := by
    intro t
    apply Fin.ext
    change (G.low.val + t) % n = (H.low.val + t) % n
    rw [hl]
  have hd : G.d = H.d := by
    rcases Nat.lt_trichotomy G.d H.d with h | h | h
    · have hf := hHI G.d (by have := G.hd; omega) h
      rw [← hpos] at hf
      rw [hG.2] at hf
      cases hf
    · exact h
    · have hf := hGI H.d (by have := H.hd; omega) h
      rw [hpos, hH.2] at hf
      cases hf
  cases G with
  | mk gr gl gd gh gn =>
    cases H with
    | mk hr hl' hd' hh hn =>
      dsimp only at hl hd
      subst hl'
      subst hd'
      have he : gr = hr := by cases gr; cases hr; rfl
      cases he
      rfl

theorem layout_covers (ring : DirectedRing n) (C : Fin n → UCell ψ κ)
    (hC : SeparatedClass ring k C) (G : GapFrame n)
    (hE : GapEndpointsPresent G (physicalConfig C))
    (hI : GapInteriorFollowers G (physicalConfig C)) :
    ∃ i : Fin k, G = (layout ring C hC).gap i := by
  obtain ⟨i, hi⟩ := leaderAt_complete (physicalConfig C) hC.count (G.pos 0) hE.1
  refine ⟨i, frame_unique G _ (physicalConfig C) hE hI
    (layout_real ring C hC i).1 (layout_real ring C hC i).2 ?_⟩
  change G.low = leaderAt _ hC.count i
  rw [hi, pos_zero]

noncomputable def signalDisorder (L : CyclicLayout n k) (C : Fin n → UCell ψ κ) : Nat :=
  (List.ofFn (fun i => badTop (L.gap i) (physicalConfig C))).sum

theorem signalDisorder_le (L : CyclicLayout n k) (C : Fin n → UCell ψ κ) :
    signalDisorder L C ≤ n := by
  have h := FiniteUniformStoppingTree.ofFn_sum_le
    (fun i => badTop (L.gap i) (physicalConfig C)) (fun i => (L.gap i).d)
    (fun i => badTop_le _ _)
  rwa [L.mass] at h


/-- Equality of actual leader bits; this is an audit relation, not a cell field. -/
def SameLeaders (C D : Fin n → UCell ψ κ) : Prop :=
  ∀ i, (D i).legacy.leader = (C i).legacy.leader

theorem sameLeaders_count (C D : Fin n → UCell ψ κ) (h : SameLeaders C D) :
    K2FiniteProgress.count D = K2FiniteProgress.count C := by
  apply FiniteUniformStoppingTree.ofFn_sum_eq
  intro i
  change (if (D i).legacy.leader then 1 else 0) =
    (if (C i).legacy.leader then 1 else 0)
  rw [h i]

theorem sameLeaders_shape (C D : Fin n → UCell ψ κ) (h : SameLeaders C D)
    (G : GapFrame n) (hE : GapEndpointsPresent G (physicalConfig C))
    (hI : GapInteriorFollowers G (physicalConfig C)) :
    GapEndpointsPresent G (physicalConfig D) ∧ GapInteriorFollowers G (physicalConfig D) :=
  ⟨⟨(h _).trans hE.1, (h _).trans hE.2⟩, fun t ht htd => (h _).trans (hI t ht htd)⟩

theorem sameLeaders_separated (ring : DirectedRing n) (C D : Fin n → UCell ψ κ)
    (h : SameLeaders C D) (hs : Separated ring (physicalConfig C)) :
    Separated ring (physicalConfig D) :=
  fun i hi => (h _).trans (hs i ((h i).symm.trans hi))

/-- Absence of a real count drop forces equality of every old leader bit.
The premise is a decidable deletion test, not a gap or safety invariant. -/
theorem sameLeaders_step (hψ : 0 < ψ) (ring : DirectedRing n)
    (C : Fin n → UCell ψ κ) (e : Fin n)
    (hd : ¬ K2FiniteProgress.count (LabelFreeElimination.step hψ ring C e) <
      K2FiniteProgress.count C) :
    SameLeaders C (LabelFreeElimination.step hψ ring C e) := by
  have hc := rawStep_layout_cases (by decide) ring (observe C) e
  rw [← observe_step hψ ring C e] at hc
  rcases hc with hc | ⟨hp, hdel, _⟩
  · exact hc
  · have hdel' : (rawStep (by decide) ring (observe C) e e).leader = false := by
      rw [← observe_step hψ ring C e]
      exact hdel
    have hh := physical_count_drop (by decide) ring (observe C) e hp hdel'
    rw [← observe_step hψ ring C e] at hh
    change K2FiniteProgress.count (LabelFreeElimination.step hψ ring C e) + 1 =
      K2FiniteProgress.count C at hh
    exact (hd (by omega)).elim

private theorem no_endpoint_deleted (C D : Fin n → UCell ψ κ)
    (h : SameLeaders C D) (G : GapFrame n)
    (hE : GapEndpointsPresent G (physicalConfig C)) :
    ¬ EndpointDeleted G (physicalConfig D) := by
  change (C (G.pos 0)).legacy.leader = true ∧
    (C (G.pos G.d)).legacy.leader = true at hE
  rintro (hd | hd)
  · change (D (G.pos 0)).legacy.leader = false at hd
    rw [h, hE.1] at hd
    cases hd
  · change (D (G.pos G.d)).legacy.leader = false at hd
    rw [h, hE.2] at hd
    cases hd

private theorem sum_indicator {m : Nat} (e : Fin m) :
    (List.ofFn (fun i : Fin m => if i = e then 1 else 0)).sum = 1 := by
  induction m with
  | zero => exact Fin.elim0 e
  | succ m ih =>
    have hz : ∀ i : Fin m, i.succ ≠ (0 : Fin (m + 1)) := by
      intro i h
      have hv := congrArg Fin.val h
      change i.val + 1 = 0 at hv
      omega
    refine Fin.cases ?_ (fun j => ?_) e
    · simp [List.ofFn_succ, hz, FiniteUniformStoppingTree.ofFn_sum_const]
    · rw [List.ofFn_succ, List.sum_cons]
      have hh : (0 : Fin (m + 1)) ≠ j.succ := fun h => hz j h.symm
      simpa [hh] using ih j

private theorem term_le_sum {m : Nat} (f : Fin m → Nat) (i : Fin m) :
    f i ≤ (List.ofFn f).sum := by
  induction m with
  | zero => exact Fin.elim0 i
  | succ m ih =>
    rw [List.ofFn_succ, List.sum_cons]
    refine Fin.cases ?_ (fun j => ?_) i
    · omega
    · have hh := ih (fun j => f j.succ) j
      omega

private theorem sum_zero_iff {m : Nat} (f : Fin m → Nat) :
    (List.ofFn f).sum = 0 ↔ ∀ i, f i = 0 := by
  constructor
  · intro h i
    have := term_le_sum f i
    omega
  · intro h
    have he := FiniteUniformStoppingTree.ofFn_sum_eq f (fun _ => 0) h
    simpa [FiniteUniformStoppingTree.ofFn_sum_const] using he

/-- Zero rank is precisely the existing physical global signal class while
the initial physical leader layout is retained. -/
theorem signalDisorder_zero_iff (ring : DirectedRing n) (C D : Fin n → UCell ψ κ)
    (hC : SeparatedClass ring k C) (h : SameLeaders C D) :
    signalDisorder (layout ring C hC) D = 0 ↔ SignalGlobal ring D := by
  rw [signalDisorder, sum_zero_iff, signalGlobal_iff]
  constructor
  · intro hz
    refine ⟨sameLeaders_separated ring C D h hC.separated, ?_⟩
    intro G hE hI
    have hh := sameLeaders_shape D C (fun i => (h i).symm) G hE hI
    obtain ⟨i, rfl⟩ := layout_covers ring C hC G hh.1 hh.2
    exact (badTop_zero_iff _ _).mp (hz i)
  · intro hD i
    apply (badTop_zero_iff _ _).mpr
    have hi := layout_real ring C hC i
    have hh := sameLeaders_shape C D h _ hi.1 hi.2
    exact hD.2 _ hh.1 hh.2

/-- The sum over the derived, fixed layout is nonincreasing on every
nondeleting successor. No global merge is included in this statement. -/
theorem signalDisorder_step_le (hψ : 0 < ψ) (ring : DirectedRing n)
    (C D : Fin n → UCell ψ κ) (hC : SeparatedClass ring k C)
    (h : SameLeaders C D) (e : Fin n)
    (hd : ¬ K2FiniteProgress.count (LabelFreeElimination.step hψ ring D e) <
      K2FiniteProgress.count D) :
    signalDisorder (layout ring C hC) (LabelFreeElimination.step hψ ring D e) ≤
      signalDisorder (layout ring C hC) D := by
  have hkeep := sameLeaders_step hψ ring D e hd
  apply FiniteUniformStoppingTree.ofFn_sum_le
  intro i
  let G := (layout ring C hC).gap i
  have hG := sameLeaders_shape C D h G (layout_real ring C hC i).1
    (layout_real ring C hC i).2
  have hn := no_endpoint_deleted D _ hkeep G hG.1
  have hr : ring = G.ring := by cases ring; cases G.ring; rfl
  change badTop G (observe (LabelFreeElimination.step hψ ring D e)) ≤ badTop G (observe D)
  change ¬ EndpointDeleted G (observe (LabelFreeElimination.step hψ ring D e)) at hn
  rw [observe_step, hr] at hn ⊢
  exact badTop_step_le G (observe D) hG.1 hG.2 e hn

/-- A positive disorder supplies one actual scheduler edge with strict total
rank descent or actual count deletion on that very successor. -/
theorem signalDisorder_target (hψ : 0 < ψ) (ring : DirectedRing n)
    (C D : Fin n → UCell ψ κ) (hC : SeparatedClass ring k C)
    (h : SameLeaders C D) (hp : 0 < signalDisorder (layout ring C hC) D) :
    ∃ e : Fin n,
      K2FiniteProgress.count (LabelFreeElimination.step hψ ring D e) < K2FiniteProgress.count D ∨
      signalDisorder (layout ring C hC) (LabelFreeElimination.step hψ ring D e) <
        signalDisorder (layout ring C hC) D := by
  classical
  have hex : ∃ i, 0 < badTop ((layout ring C hC).gap i) (physicalConfig D) := by
    apply Classical.byContradiction
    intro hn
    have hz : ∀ i, badTop ((layout ring C hC).gap i) (physicalConfig D) = 0 := by
      intro i
      have hh : ¬ 0 < badTop ((layout ring C hC).gap i) (physicalConfig D) :=
        fun hi => hn ⟨i, hi⟩
      omega
    have hh := (sum_zero_iff _).mpr hz
    change signalDisorder (layout ring C hC) D = 0 at hh
    omega
  obtain ⟨i, hi⟩ := hex
  let G := (layout ring C hC).gap i
  let e := G.pos (badTop G (physicalConfig D) - 1)
  refine ⟨e, ?_⟩
  by_cases hd : K2FiniteProgress.count (LabelFreeElimination.step hψ ring D e) <
      K2FiniteProgress.count D
  · exact Or.inl hd
  · apply Or.inr
    have hkeep := sameLeaders_step hψ ring D e hd
    have hall : ∀ j,
        badTop ((layout ring C hC).gap j) (physicalConfig (LabelFreeElimination.step hψ ring D e)) ≤
          badTop ((layout ring C hC).gap j) (physicalConfig D) := by
      intro j
      let H := (layout ring C hC).gap j
      have hH := sameLeaders_shape C D h H (layout_real ring C hC j).1
        (layout_real ring C hC j).2
      have hn := no_endpoint_deleted D _ hkeep H hH.1
      have hr : ring = H.ring := by cases ring; cases H.ring; rfl
      change badTop H (observe (LabelFreeElimination.step hψ ring D e)) ≤ badTop H (observe D)
      change ¬ EndpointDeleted H (observe (LabelFreeElimination.step hψ ring D e)) at hn
      rw [observe_step, hr] at hn ⊢
      exact badTop_step_le H (observe D) hH.1 hH.2 e hn
    have hstrict : badTop G (physicalConfig (LabelFreeElimination.step hψ ring D e)) <
        badTop G (physicalConfig D) := by
      have hG := sameLeaders_shape C D h G (layout_real ring C hC i).1
        (layout_real ring C hC i).2
      have hn := no_endpoint_deleted D _ hkeep G hG.1
      have hr : ring = G.ring := by cases ring; cases G.ring; rfl
      change badTop G (observe (LabelFreeElimination.step hψ ring D e)) < badTop G (observe D)
      change ¬ EndpointDeleted G (observe (LabelFreeElimination.step hψ ring D e)) at hn
      rw [observe_step, hr] at hn ⊢
      exact (badTop_target G (observe D) hG.1 hG.2 hi).resolve_left hn
    have hh := FiniteUniformStoppingTree.ofFn_sum_le
      (fun j => badTop ((layout ring C hC).gap j)
        (physicalConfig (LabelFreeElimination.step hψ ring D e)) + if j = i then 1 else 0)
      (fun j => badTop ((layout ring C hC).gap j) (physicalConfig D)) (fun j => by
        by_cases hj : j = i
        · subst j
          rw [if_pos (Eq.refl i)]
          exact hstrict
        · simp only [if_neg hj, Nat.add_zero]
          exact hall j)
    rw [FiniteUniformStoppingTree.ofFn_sum_add, sum_indicator] at hh
    exact hh


/-! ## The actual stopped process, with retained physical terminal payloads -/

inductive EntryOutcome (S : Type) where
  | deleted : S → EntryOutcome S
  | ordered : S → EntryOutcome S
  | retry : S → EntryOutcome S

def EntryOutcome.payload {S : Type} : EntryOutcome S → S
  | .deleted D | .ordered D | .retry D => D

def EntryOutcome.node {S : Type} : EntryOutcome S → StopNode S
  | .deleted _ | .ordered _ => .success
  | .retry D => .active D

noncomputable section

/-- One real physical edge followed by an audit classification. Deletion
has priority even when the same successor is also signal ordered. -/
def entryOutcome (hψ : 0 < ψ) (ring : DirectedRing n)
    (C₀ C : Fin n → UCell ψ κ) (e : Fin n) : EntryOutcome (Fin n → UCell ψ κ) := by
  classical
  let D := LabelFreeElimination.step hψ ring C e
  exact if K2FiniteProgress.count D < K2FiniteProgress.count C₀ then .deleted D
    else if SignalGlobal ring D then .ordered D else .retry D

def entryStep (hψ : 0 < ψ) (ring : DirectedRing n)
    (C₀ C : Fin n → UCell ψ κ) (e : Fin n) : StopNode (Fin n → UCell ψ κ) :=
  (entryOutcome hψ ring C₀ C e).node

/-- A state already in the requested class costs zero interactions. -/
def initialOutcome (ring : DirectedRing n) (C₀ : Fin n → UCell ψ κ) :
    EntryOutcome (Fin n → UCell ψ κ) := by
  classical
  exact if SignalGlobal ring C₀ then .ordered C₀ else .retry C₀

def initialNode (ring : DirectedRing n) (C₀ : Fin n → UCell ψ κ) :
    StopNode (Fin n → UCell ψ κ) := (initialOutcome ring C₀).node

theorem entryOutcome_payload (hψ : 0 < ψ) (ring : DirectedRing n)
    (C₀ C : Fin n → UCell ψ κ) (e : Fin n) :
    (entryOutcome hψ ring C₀ C e).payload = LabelFreeElimination.step hψ ring C e := by
  classical
  unfold entryOutcome
  dsimp only
  split <;> (try split) <;> rfl

theorem entryOutcome_deletion_priority (hψ : 0 < ψ) (ring : DirectedRing n)
    (C₀ C : Fin n → UCell ψ κ) (e : Fin n)
    (hd : K2FiniteProgress.count (LabelFreeElimination.step hψ ring C e) <
      K2FiniteProgress.count C₀) :
    entryOutcome hψ ring C₀ C e = .deleted (LabelFreeElimination.step hψ ring C e) := by
  simp only [entryOutcome, if_pos hd]

theorem entryOutcome_correct (hψ : 0 < ψ) (ring : DirectedRing n)
    (C₀ C : Fin n → UCell ψ κ) (e : Fin n) :
    match entryOutcome hψ ring C₀ C e with
    | .deleted D => K2FiniteProgress.count D < K2FiniteProgress.count C₀
    | .ordered D => SignalGlobal ring D
    | .retry D => ¬ K2FiniteProgress.count D < K2FiniteProgress.count C₀ ∧
        ¬ SignalGlobal ring D := by
  classical
  by_cases hd : K2FiniteProgress.count (LabelFreeElimination.step hψ ring C e) < K2FiniteProgress.count C₀
  · simpa only [entryOutcome, if_pos hd] using hd
  · by_cases hg : SignalGlobal ring (LabelFreeElimination.step hψ ring C e)
    · simpa only [entryOutcome, if_neg hd, if_pos hg] using hg
    · simpa only [entryOutcome, if_neg hd, if_neg hg] using And.intro hd hg

/-- Only proof data restrict active audit nodes. The tree below is proved
exactly equal to the tree on the full physical carrier. -/
def AuditState (ring : DirectedRing n) (C₀ : Fin n → UCell ψ κ) :=
  { C : Fin n → UCell ψ κ // SameLeaders C₀ C ∧ ¬ SignalGlobal ring C }

def auditStep (hψ : 0 < ψ) (ring : DirectedRing n) (C₀ : Fin n → UCell ψ κ)
    (s : AuditState ring C₀) (e : Fin n) : StopNode (AuditState ring C₀) := by
  classical
  let D := LabelFreeElimination.step hψ ring s.val e
  exact if hd : K2FiniteProgress.count D < K2FiniteProgress.count C₀ then .success
    else if hg : SignalGlobal ring D then .success
    else .active ⟨D, (by
      have hc := sameLeaders_count C₀ s.val s.property.1
      have hkeep := sameLeaders_step hψ ring s.val e (by rw [hc]; exact hd)
      exact ⟨fun i => (hkeep i).trans (s.property.1 i), hg⟩)⟩

def auditInitial (ring : DirectedRing n) (C₀ : Fin n → UCell ψ κ) :
    StopNode (AuditState ring C₀) := by
  classical
  exact if h : SignalGlobal ring C₀ then .success
    else .active ⟨C₀, (fun _ => rfl), h⟩

def forgetAudit (ring : DirectedRing n) (C₀ : Fin n → UCell ψ κ) :
    StopNode (AuditState ring C₀) → StopNode (Fin n → UCell ψ κ)
  | .active s => .active s.val
  | .success => .success
  | .failure => .failure

theorem forget_auditStep (hψ : 0 < ψ) (ring : DirectedRing n)
    (C₀ : Fin n → UCell ψ κ) (s : AuditState ring C₀) (e : Fin n) :
    forgetAudit ring C₀ (auditStep hψ ring C₀ s e) = entryStep hψ ring C₀ s.val e := by
  classical
  unfold auditStep entryStep entryOutcome
  dsimp only
  split <;> (try split) <;> rfl

theorem forget_auditInitial (ring : DirectedRing n) (C₀ : Fin n → UCell ψ κ) :
    forgetAudit ring C₀ (auditInitial ring C₀) = initialNode ring C₀ := by
  classical
  unfold auditInitial initialNode initialOutcome
  split <;> rfl

theorem forget_stepNode (hψ : 0 < ψ) (ring : DirectedRing n)
    (C₀ : Fin n → UCell ψ κ) (x : StopNode (AuditState ring C₀)) (e : Fin n) :
    forgetAudit ring C₀ (stepNode (auditStep hψ ring C₀) x e) =
      stepNode (entryStep hψ ring C₀) (forgetAudit ring C₀ x) e := by
  cases x with
  | active s => exact forget_auditStep hψ ring C₀ s e
  | success => rfl
  | failure => rfl

/-- Exact n-branch tree simulation at every depth and for every leaf weight.
The raw edge and the physical active successor are identical. -/
theorem audit_treeWeight (hψ : 0 < ψ) (ring : DirectedRing n)
    (C₀ : Fin n → UCell ψ κ) (w : StopNode (Fin n → UCell ψ κ) → Nat)
    (x : StopNode (AuditState ring C₀)) (T : Nat) :
    treeWeight (auditStep hψ ring C₀) (fun y => w (forgetAudit ring C₀ y)) x T =
      treeWeight (entryStep hψ ring C₀) w (forgetAudit ring C₀ x) T := by
  induction T generalizing x with
  | zero => rfl
  | succ T ih =>
    simp only [treeWeight]
    apply FiniteUniformStoppingTree.ofFn_sum_eq
    intro e
    rw [ih, forget_stepNode]

theorem audit_cost (hψ : 0 < ψ) (ring : DirectedRing n)
    (C₀ : Fin n → UCell ψ κ) (x : StopNode (AuditState ring C₀)) (T : Nat) :
    truncatedActiveCostNumerator (auditStep hψ ring C₀) x T =
      truncatedActiveCostNumerator (entryStep hψ ring C₀) (forgetAudit ring C₀ x) T := by
  induction T generalizing x with
  | zero => rfl
  | succ T ih =>
    cases x with
    | success => rfl
    | failure => rfl
    | active s =>
      simp only [truncatedActiveCostNumerator, forgetAudit]
      apply congrArg (fun z => n ^ (T + 1) + z)
      apply FiniteUniformStoppingTree.ofFn_sum_eq
      intro e
      rw [ih, forget_auditStep]

def entryPotential (ring : DirectedRing n) (C₀ : Fin n → UCell ψ κ)
    (hC : SeparatedClass ring k C₀) : StopNode (AuditState ring C₀) → Nat
  | .active s => n * signalDisorder (layout ring C₀ hC) s.val
  | .success | .failure => 0

private theorem audit_rank_positive (ring : DirectedRing n)
    (C₀ : Fin n → UCell ψ κ) (hC : SeparatedClass ring k C₀)
    (s : AuditState ring C₀) : 0 < signalDisorder (layout ring C₀ hC) s.val := by
  have hh : signalDisorder (layout ring C₀ hC) s.val ≠ 0 :=
    fun hz => s.property.2 ((signalDisorder_zero_iff ring C₀ s.val hC s.property.1).mp hz)
  omega

private theorem audit_potential_le (hψ : 0 < ψ) (ring : DirectedRing n)
    (C₀ : Fin n → UCell ψ κ) (hC : SeparatedClass ring k C₀)
    (s : AuditState ring C₀) (e : Fin n) :
    entryPotential ring C₀ hC (auditStep hψ ring C₀ s e) ≤
      entryPotential ring C₀ hC (.active s) := by
  classical
  unfold auditStep
  dsimp only
  split
  · exact Nat.zero_le _
  · rename_i hd
    split
    · exact Nat.zero_le _
    · apply Nat.mul_le_mul_left n
      exact signalDisorder_step_le hψ ring C₀ s.val hC s.property.1 e
        (by rw [sameLeaders_count C₀ s.val s.property.1]; exact hd)

private theorem audit_potential_target (hψ : 0 < ψ) (ring : DirectedRing n)
    (C₀ : Fin n → UCell ψ κ) (hC : SeparatedClass ring k C₀)
    (s : AuditState ring C₀) :
    ∃ e : Fin n, entryPotential ring C₀ hC (auditStep hψ ring C₀ s e) + n ≤
      entryPotential ring C₀ hC (.active s) := by
  classical
  have hp := audit_rank_positive ring C₀ hC s
  obtain ⟨e, he⟩ := signalDisorder_target hψ ring C₀ s.val hC s.property.1 hp
  refine ⟨e, ?_⟩
  have hn : n ≤ n * signalDisorder (layout ring C₀ hC) s.val := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left n hp
  unfold auditStep
  dsimp only
  split
  · simpa only [entryPotential, Nat.zero_add] using hn
  · rename_i hd
    split
    · simpa only [entryPotential, Nat.zero_add] using hn
    · have hnd : ¬ K2FiniteProgress.count (LabelFreeElimination.step hψ ring s.val e) <
          K2FiniteProgress.count s.val := by
        rw [sameLeaders_count C₀ s.val s.property.1]
        exact hd
      have hs := he.resolve_left hnd
      have hh := Nat.mul_le_mul_left n hs
      simpa only [entryPotential, Nat.mul_succ] using hh

/-- The Bellman row is derived from the proved actual target edge. It is
not an input assumption or a field of the separated entry class. -/
theorem entry_super (hψ : 0 < ψ) (ring : DirectedRing n)
    (C₀ : Fin n → UCell ψ κ) (hC : SeparatedClass ring k C₀) :
    NatBellmanSuperSolution (auditStep hψ ring C₀) 1 (entryPotential ring C₀ hC) := by
  classical
  refine ⟨rfl, rfl, ?_⟩
  intro s
  obtain ⟨e, he⟩ := audit_potential_target hψ ring C₀ hC s
  have hh := FiniteUniformStoppingTree.ofFn_sum_le
    (fun j => entryPotential ring C₀ hC (auditStep hψ ring C₀ s j) +
      n * (if j = e then 1 else 0))
    (fun _ : Fin n => entryPotential ring C₀ hC (.active s)) (fun j => by
      by_cases hj : j = e
      · subst j
        simpa using he
      · simp only [if_neg hj, Nat.mul_zero, Nat.add_zero]
        exact audit_potential_le hψ ring C₀ hC s j)
  rw [FiniteUniformStoppingTree.ofFn_sum_add, FiniteUniformStoppingTree.ofFn_sum_mul_left,
    sum_indicator, Nat.mul_one, FiniteUniformStoppingTree.ofFn_sum_const] at hh
  change 1 * n + _ ≤ _
  omega

theorem entry_truncated_cost (hψ : 0 < ψ) (hn : 1 < n) (ring : DirectedRing n)
    (C₀ : Fin n → UCell ψ κ) (hC : SeparatedClass ring k C₀) (T : Nat) :
    truncatedActiveCostNumerator (entryStep hψ ring C₀) (initialNode ring C₀) T ≤
      n ^ T * (n * n) := by
  have hpos : 0 < n := by omega
  have hh := truncatedActiveCostNumerator_mul_le_of_natSuperSolution
    (auditStep hψ ring C₀) 1 (entryPotential ring C₀ hC) (entry_super hψ ring C₀ hC)
    (auditInitial ring C₀) T
  rw [audit_cost, forget_auditInitial, Nat.one_mul] at hh
  apply Nat.le_trans hh
  apply Nat.mul_le_mul_left
  unfold auditInitial
  split
  · exact Nat.zero_le _
  · exact Nat.mul_le_mul_left n (signalDisorder_le _ C₀)


private theorem entry_failure_active (hψ : 0 < ψ) (ring : DirectedRing n)
    (C₀ C : Fin n → UCell ψ κ) (T : Nat) :
    failureCount (entryStep hψ ring C₀) (.active C) T = 0 := by
  classical
  induction T generalizing C with
  | zero => rfl
  | succ T ih =>
    change (List.ofFn (fun e => treeWeight (entryStep hψ ring C₀) failureWeight
      (entryStep hψ ring C₀ C e) T)).sum = 0
    have hh := FiniteUniformStoppingTree.ofFn_sum_eq
      (fun e => treeWeight (entryStep hψ ring C₀) failureWeight (entryStep hψ ring C₀ C e) T)
      (fun _ : Fin n => 0) (fun e => by
        unfold entryStep entryOutcome
        dsimp only
        split
        · simp only [EntryOutcome.node, treeWeight_success, failureWeight, Nat.mul_zero]
        · split
          · simp only [EntryOutcome.node, treeWeight_success, failureWeight, Nat.mul_zero]
          · exact ih _)
    simpa only [FiniteUniformStoppingTree.ofFn_sum_const, Nat.mul_zero] using hh

theorem entry_failureCount (hψ : 0 < ψ) (ring : DirectedRing n)
    (C₀ : Fin n → UCell ψ κ) (T : Nat) :
    failureCount (entryStep hψ ring C₀) (initialNode ring C₀) T = 0 := by
  classical
  unfold initialNode initialOutcome
  split
  · simp only [EntryOutcome.node, failureCount, treeWeight_success, failureWeight, Nat.mul_zero]
  · exact entry_failure_active hψ ring C₀ C₀ T

/-- At least half of the original raw words stop by 2*n², at SignalGlobal
or an actual physical count deletion. The tree has its original n edges. -/
theorem entry_half_mass (hψ : 0 < ψ) (hn : 1 < n) (ring : DirectedRing n)
    (C₀ : Fin n → UCell ψ κ) (hC : SeparatedClass ring k C₀) :
    n ^ (2 * (n * n)) ≤
      2 * successCount (entryStep hψ ring C₀) (initialNode ring C₀) (2 * (n * n)) := by
  have hc := entry_truncated_cost hψ hn ring C₀ hC (2 * (n * n))
  have hpos : 0 < 2 * (n * n) := Nat.mul_pos (by decide) (Nat.mul_pos ring.hn ring.hn)
  have ht := two_mul_activeCount_le_pow_of_scaled_cost
    (entryStep hψ ring C₀) (initialNode ring C₀) (den := 1) (num := n * n)
    hpos (by decide) (by simpa only [Nat.one_mul, Nat.mul_comm] using hc)
    (by simp only [Nat.mul_one, Nat.le_refl])
  have hp := node_count_partition (entryStep hψ ring C₀) (initialNode ring C₀) (2 * (n * n))
  rw [entry_failureCount] at hp
  omega

/-- The success event is physical entry or physical deletion, not safety. -/
def EntryReached (ring : DirectedRing n) (C₀ D : Fin n → UCell ψ κ) : Prop :=
  SignalGlobal ring D ∨ K2FiniteProgress.count D < K2FiniteProgress.count C₀

theorem entryReached_step (hψ : 0 < ψ) (ring : DirectedRing n)
    (C₀ D : Fin n → UCell ψ κ) (h : EntryReached ring C₀ D) (e : Fin n) :
    EntryReached ring C₀ (LabelFreeElimination.step hψ ring D e) := by
  rcases h with h | h
  · exact Or.inl (signalGlobal_step hψ ring D h e)
  · exact Or.inr (Nat.lt_of_le_of_lt (K2FiniteProgress.step_count_nonincrease hψ ring D e) h)

def EntryTracks (ring : DirectedRing n) (C₀ : Fin n → UCell ψ κ) :
    StopNode (Fin n → UCell ψ κ) → (Fin n → UCell ψ κ) → Prop
  | .active C, D => C = D
  | .success, D => EntryReached ring C₀ D
  | .failure, _ => False

theorem entry_tracks_initial (ring : DirectedRing n) (C₀ : Fin n → UCell ψ κ) :
    EntryTracks ring C₀ (initialNode ring C₀) C₀ := by
  classical
  unfold initialNode initialOutcome
  split
  · exact Or.inl (by assumption)
  · rfl

theorem entry_tracks_step (hψ : 0 < ψ) (ring : DirectedRing n)
    (C₀ D : Fin n → UCell ψ κ) (x : StopNode (Fin n → UCell ψ κ))
    (h : EntryTracks ring C₀ x D) (e : Fin n) :
    EntryTracks ring C₀ (stepNode (entryStep hψ ring C₀) x e)
      (LabelFreeElimination.step hψ ring D e) := by
  classical
  cases x with
  | failure => exact h.elim
  | success => exact entryReached_step hψ ring C₀ D h e
  | active C =>
    change C = D at h
    subst C
    change EntryTracks ring C₀ (entryStep hψ ring C₀ D e) _
    unfold entryStep entryOutcome
    dsimp only
    split
    · exact Or.inr (by assumption)
    · split
      · exact Or.inl (by assumption)
      · rfl

/-- The same full raw word tracks the real unstopped execution. Both kinds
of success persist under physical terminal padding. -/
theorem entry_tracks_word (hψ : 0 < ψ) (ring : DirectedRing n)
    (C₀ D : Fin n → UCell ψ κ) (x : StopNode (Fin n → UCell ψ κ))
    (h : EntryTracks ring C₀ x D) (es : List (Fin n)) :
    EntryTracks ring C₀ (ControlledSchedulerMass.runWord (entryStep hψ ring C₀) x es)
      (LDSinkBoundedKernel.run (LabelFreeElimination.step hψ ring) D es) := by
  induction es generalizing D x with
  | nil => exact h
  | cons e es ih => exact ih _ _ (entry_tracks_step hψ ring C₀ D x h e)

theorem entry_successful_word (hψ : 0 < ψ) (ring : DirectedRing n)
    (C₀ : Fin n → UCell ψ κ) (es : List (Fin n))
    (hs : ControlledSchedulerMass.runWord (entryStep hψ ring C₀) (initialNode ring C₀) es = .success) :
    EntryReached ring C₀ (LDSinkBoundedKernel.run (LabelFreeElimination.step hψ ring) C₀ es) := by
  have hh := entry_tracks_word hψ ring C₀ C₀ (initialNode ring C₀) (entry_tracks_initial ring C₀) es
  rw [hs] at hh
  exact hh

def retainedStep (hψ : 0 < ψ) (ring : DirectedRing n) (C₀ : Fin n → UCell ψ κ) :
    EntryOutcome (Fin n → UCell ψ κ) → Fin n → EntryOutcome (Fin n → UCell ψ κ)
  | .retry C, e => entryOutcome hψ ring C₀ C e
  | .ordered C, _ => .ordered C
  | .deleted C, _ => .deleted C

def retainedRun (hψ : 0 < ψ) (ring : DirectedRing n) (C₀ : Fin n → UCell ψ κ)
    (q : EntryOutcome (Fin n → UCell ψ κ)) (es : List (Fin n)) : EntryOutcome (Fin n → UCell ψ κ) :=
  LDSinkBoundedKernel.run (retainedStep hψ ring C₀) q es

theorem retainedStep_node (hψ : 0 < ψ) (ring : DirectedRing n)
    (C₀ : Fin n → UCell ψ κ) (q : EntryOutcome (Fin n → UCell ψ κ)) (e : Fin n) :
    (retainedStep hψ ring C₀ q e).node = stepNode (entryStep hψ ring C₀) q.node e := by
  cases q <;> rfl

/-- Retaining the first terminal successor changes none of the stopped
words counted by the original tree. -/
theorem retainedRun_node (hψ : 0 < ψ) (ring : DirectedRing n)
    (C₀ : Fin n → UCell ψ κ) (q : EntryOutcome (Fin n → UCell ψ κ)) (es : List (Fin n)) :
    (retainedRun hψ ring C₀ q es).node =
      ControlledSchedulerMass.runWord (entryStep hψ ring C₀) q.node es := by
  induction es generalizing q with
  | nil => rfl
  | cons e es ih =>
    change (retainedRun hψ ring C₀ (retainedStep hψ ring C₀ q e) es).node = _
    rw [ih, retainedStep_node]
    rfl

theorem entryOutcome_frame (hψ : 0 < ψ) (ring : DirectedRing n)
    (C₀ C : Fin n → UCell ψ κ) (e i : Fin n) :
    putSignals ((entryOutcome hψ ring C₀ C e).payload i) (observeCell (C i)) = C i := by
  rw [entryOutcome_payload]
  exact step_frame hψ ring C e i

/-- Agreement with the repaired adjacent row is used only under actual
physical separation, which is part of the entry domain. -/
theorem entry_separated_agreement (hψ : 0 < ψ) (ring : DirectedRing n)
    (C : Fin n → UCell ψ κ) (hC : SeparatedClass ring k C) (es : List (Fin n)) :
    LDSinkBoundedKernel.run (AdjacentLeaderElimination.step hψ ring) C es =
      LDSinkBoundedKernel.run (LabelFreeElimination.step hψ ring) C es := by
  exact AdjacentLeaderElimination.separated_run_eq_old hψ ring C hC.separated es

end


/-! ## Exact merged rank, without a signal-order assumption -/

open LDTwoGapFrame

private theorem attack_offset (F : TwoGapFrame n) (i : Nat) (hi : F.recovery.d ≤ i) :
    F.attack.pos (i - F.recovery.d) = (merged F).pos i := by
  rw [attack_pos_merged, Nat.add_sub_cancel' hi]

theorem badAt_merge_right (F : TwoGapFrame n) (C : Fin n → AgentState ψ)
    (i : Nat) (hi : F.recovery.d < i) :
    BadAt (merged F) C i ↔ BadAt F.attack C (i - F.recovery.d) := by
  constructor
  · rintro ⟨hi1, hid, hb, j, hij, hjd, hs⟩
    change i ≤ F.recovery.d + F.attack.d at hid
    change j ≤ F.recovery.d + F.attack.d at hjd
    refine ⟨by omega, by omega, ?_, j - F.recovery.d, by omega, by omega, ?_⟩
    · rwa [attack_offset F i (by omega)]
    · rwa [attack_offset F j (by omega)]
  · rintro ⟨_, hid, hb, j, hij, hjd, hs⟩
    refine ⟨by omega, by change i ≤ F.recovery.d + F.attack.d; omega, ?_,
      F.recovery.d + j, by omega, by change F.recovery.d + j ≤ F.recovery.d + F.attack.d; omega, ?_⟩
    · rwa [attack_offset F i (by omega)] at hb
    · rwa [← attack_pos_merged]

private theorem badAt_merge_left (F : TwoGapFrame n) (C : Fin n → AgentState ψ)
    (i : Nat) (hi : BadAt F.recovery C i) : BadAt (merged F) C i := by
  obtain ⟨hi1, hid, hb, j, hij, hjd, hs⟩ := hi
  exact ⟨hi1, by change i ≤ F.recovery.d + F.attack.d; omega, hb,
    j, hij, by change j ≤ F.recovery.d + F.attack.d; omega, hs⟩

/-- Exact concatenation formula on the existing merged physical frame.
A positive signal in the right piece makes *every* nonzero bullet in the
left piece bad; a right-piece bad bullet acquires the left length as offset. -/
theorem badTop_merged (F : TwoGapFrame n) (C : Fin n → AgentState ψ) :
    badTop (merged F) C =
      max (if signalTop F.attack C = 0 then badTop F.recovery C else bulletTop F.recovery C)
        (if badTop F.attack C = 0 then 0 else F.recovery.d + badTop F.attack C) := by
  classical
  apply Nat.le_antisymm
  · apply badTop_le_of
    intro i hi
    by_cases hil : i ≤ F.recovery.d
    · apply Nat.le_trans (m := if signalTop F.attack C = 0 then badTop F.recovery C else bulletTop F.recovery C)
        ?_ (Nat.le_max_left _ _)
      by_cases hz : signalTop F.attack C = 0
      · rw [if_pos hz]
        apply badAt_le_top
        obtain ⟨hi1, _, hb, j, hij, hjd, hs⟩ := hi
        have hjl : j ≤ F.recovery.d := by
          apply Classical.byContradiction
          intro hnj
          have ht := signalTop_ge_of F.attack C (j := j - F.recovery.d)
            (by change j ≤ F.recovery.d + F.attack.d at hjd; omega)
            (by rw [attack_offset F j (by omega)]; exact hs)
          omega
        exact ⟨hi1, hil, hb, j, hij, hjl, hs⟩
      · rw [if_neg hz]
        exact bulletTop_ge_of F.recovery C hil hi.2.2.1
    · have ha := (badAt_merge_right F C i (by omega)).mp hi
      have hh := badAt_le_top F.attack C ha
      have hn : badTop F.attack C ≠ 0 := by have := ha.1; omega
      apply Nat.le_trans (m := if badTop F.attack C = 0 then 0 else F.recovery.d + badTop F.attack C)
        ?_ (Nat.le_max_right _ _)
      rw [if_neg hn]
      omega
  · apply Nat.max_le.mpr
    constructor
    · by_cases hz : signalTop F.attack C = 0
      · rw [if_pos hz]
        by_cases hb : badTop F.recovery C = 0
        · rw [hb]; exact Nat.zero_le _
        · exact badAt_le_top _ _ (badAt_merge_left F C _ (badTop_bad _ _ (by omega)))
      · rw [if_neg hz]
        by_cases hb : bulletTop F.recovery C = 0
        · rw [hb]; exact Nat.zero_le _
        · apply badAt_le_top
          have hbt := bulletTop_le F.recovery C
          have hst := signalTop_le F.attack C
          refine ⟨by omega, by change bulletTop F.recovery C ≤ F.recovery.d + F.attack.d; omega,
            bulletTop_ne_zero F.recovery C (by omega),
            F.recovery.d + signalTop F.attack C, by omega,
            by change F.recovery.d + signalTop F.attack C ≤ F.recovery.d + F.attack.d; omega, ?_⟩
          rw [← attack_pos_merged]
          exact signalTop_one_at F.attack C (by omega)
    · by_cases hb : badTop F.attack C = 0
      · rw [if_pos hb]; exact Nat.zero_le _
      · rw [if_neg hb]
        apply badAt_le_top
        apply (badAt_merge_right F C _ (by omega)).mpr
        simpa only [Nat.add_sub_cancel_left] using badTop_bad F.attack C (by omega)

/-- Without an incoming-signal assumption the literal deletion still only
changes the source leader bit and the incoming bullet from live to dummy. -/
theorem kernel_delete_arbitrary_signal (l r : AgentState 1)
    (hl : l.leader = true) (hr : r.leader = false)
    (hd : (sinkKernelC (by decide) l r).1.leader = false) :
    sinkKernelC (by decide) l r = ({l with leader := false}, {r with bullet := 1}) := by
  obtain ⟨hsh, hsl, hb⟩ := (kernel_delete_iff (by decide) l r hl hr).mp hd
  rcases fin2_cases r.signal_B with hs | hs
  · exact kernel_delete_row (by decide) l r hl hr hd hs
  · simp [sinkKernelC, eliminateLeadersNoCollisionFire, absorbProtectedMove,
      eliminateLeadersNoCollisionZeroLeaderEgressMove, eliminateLeadersNoCollisionSignalLeaderSink,
      dummyBulletSink, hl, hr, hsh, hsl, hb, hs]
    intro _
    rfl

/-- Deletion preserves all signals and the predicate "bullet is nonzero".
The nondeleting rank lemma excludes this row because its nearest-leader
frame changes, not because the frozen-frame BadAt values change. -/
theorem deletion_preserves_badAt (G H : GapFrame n) (C : Fin n → AgentState 1)
    (hE : GapEndpointsPresent H C) (hI : GapInteriorFollowers H C)
    (hd : (rawStep (by decide) H.ring C (H.pos 0) (H.pos 0)).leader = false) (i : Nat) :
    BadAt G (rawStep (by decide) H.ring C (H.pos 0)) i ↔ BadAt G C i := by
  have hf := hI 1 (by omega) (by have := H.hd; omega)
  have hd' : (sinkKernelC (by decide) (C (H.pos 0)) (C (H.pos 1))).1.leader = false := by
    simpa only [step_left, Nat.zero_add] using hd
  have hk := kernel_delete_arbitrary_signal (C (H.pos 0)) (C (H.pos 1)) hE.1 hf hd'
  have hb := ((kernel_delete_iff (by decide) _ _ hE.1 hf).mp hd').2.2
  have hsig : ∀ x, (rawStep (by decide) H.ring C (H.pos 0) x).signal_B = (C x).signal_B := by
    intro x
    simp only [rawStep, GapFrame.rightNeighbor_pos, Nat.zero_add, hk, updatePair]
    split <;> (try split) <;> (first | rfl | (rename_i hx; subst x; rfl))
  have hzero : ∀ x, (rawStep (by decide) H.ring C (H.pos 0) x).bullet ≠ 0 ↔ (C x).bullet ≠ 0 := by
    intro x
    simp only [rawStep, GapFrame.rightNeighbor_pos, Nat.zero_add, hk, updatePair]
    split
    · rename_i hx
      subst x
      rfl
    · split
      · rename_i hx
        subst x
        rw [hb]
        change (1 : Fin 3) ≠ 0 ↔ (2 : Fin 3) ≠ 0
        decide
      · rfl
  simp only [BadAt, hsig, hzero]

theorem deletion_badTop (G H : GapFrame n) (C : Fin n → AgentState 1)
    (hE : GapEndpointsPresent H C) (hI : GapInteriorFollowers H C)
    (hd : (rawStep (by decide) H.ring C (H.pos 0) (H.pos 0)).leader = false) :
    badTop G (rawStep (by decide) H.ring C (H.pos 0)) = badTop G C := by
  classical
  unfold badTop
  apply topIdx_congr
  intro i _ _
  have hh := propext (deletion_preserves_badAt G H C hE hI hd i)
  simp only [hh]

/-- Exact actual deletion-merge rank in terms of the *pre-step* two pieces.
The maximum can exceed the sum of their old badTop values. This identity
does not assert an amortized bound across repeated leader deletions. -/
theorem deletion_merge_badTop (hψ : 0 < ψ) (F : TwoGapFrame n)
    (C : Fin n → UCell ψ κ)
    (hE : GapEndpointsPresent F.attack (physicalConfig C))
    (hI : GapInteriorFollowers F.attack (physicalConfig C))
    (hd : (LabelFreeElimination.step hψ F.attack.ring C (F.attack.pos 0) (F.attack.pos 0)).legacy.leader = false) :
    badTop (merged F) (physicalConfig (LabelFreeElimination.step hψ F.attack.ring C (F.attack.pos 0))) =
      max (if signalTop F.attack (physicalConfig C) = 0 then badTop F.recovery (physicalConfig C)
        else bulletTop F.recovery (physicalConfig C))
        (if badTop F.attack (physicalConfig C) = 0 then 0 else F.recovery.d + badTop F.attack (physicalConfig C)) := by
  have hd' : (rawStep (by decide) F.attack.ring (observe C) (F.attack.pos 0) (F.attack.pos 0)).leader = false := by
    rw [← observe_step hψ F.attack.ring C (F.attack.pos 0)]
    exact hd
  change badTop (merged F) (observe (LabelFreeElimination.step hψ F.attack.ring C (F.attack.pos 0))) = _
  rw [observe_step, deletion_badTop (merged F) F.attack (observe C) hE hI hd']
  exact badTop_merged F (physicalConfig C)


/-- The concatenated frame really is the next-leader gap after deletion.
Only old endpoint/interior geometry and the actual deleted source are used. -/
theorem merged_shape_after_deletion (hψ : 0 < ψ) (F : TwoGapFrame n)
    (C : Fin n → UCell ψ κ)
    (hrE : GapEndpointsPresent F.recovery (physicalConfig C))
    (hrI : GapInteriorFollowers F.recovery (physicalConfig C))
    (haE : GapEndpointsPresent F.attack (physicalConfig C))
    (haI : GapInteriorFollowers F.attack (physicalConfig C))
    (hd : (LabelFreeElimination.step hψ F.attack.ring C (F.attack.pos 0) (F.attack.pos 0)).legacy.leader = false) :
    GapEndpointsPresent (merged F)
      (physicalConfig (LabelFreeElimination.step hψ F.attack.ring C (F.attack.pos 0))) ∧
    GapInteriorFollowers (merged F)
      (physicalConfig (LabelFreeElimination.step hψ F.attack.ring C (F.attack.pos 0))) := by
  let D := LabelFreeElimination.step hψ F.attack.ring C (F.attack.pos 0)
  have he : F.attack.pos 0 = (merged F).pos F.recovery.d := by
    simpa only [Nat.add_zero] using attack_pos_merged F 0
  have hlead : ∀ i, i ≠ F.attack.pos 0 → (D i).legacy.leader = (C i).legacy.leader := by
    intro i hi
    have hh := rawStep_leader_away (by decide) F.attack.ring (observe C) (F.attack.pos 0) i hi
    rw [← observe_step hψ F.attack.ring C (F.attack.pos 0)] at hh
    exact hh
  have hfol := K2FiniteProgress.step_noNew hψ F.attack.ring C (F.attack.pos 0)
  have hn := F.length_lt
  have hrd := F.recovery.hd
  have had := F.attack.hd
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · change (D ((merged F).pos 0)).legacy.leader = true
    rw [hlead _ (by rw [he]; exact (merged F).pos_ne (by omega) (by omega) (by omega))]
    exact hrE.1
  · change (D ((merged F).pos (F.recovery.d + F.attack.d))).legacy.leader = true
    rw [← attack_pos_merged]
    rw [hlead _ (F.attack.pos_ne (by omega) (by omega) (by omega))]
    exact haE.2
  · intro t ht htd
    change t < F.recovery.d + F.attack.d at htd
    by_cases htl : t < F.recovery.d
    · exact hfol _ (hrI t ht htl)
    · by_cases hte : t = F.recovery.d
      · subst t
        change (D ((merged F).pos F.recovery.d)).legacy.leader = false
        rw [← he]
        exact hd
      · change (D ((merged F).pos t)).legacy.leader = false
        rw [← attack_offset F t (by omega)]
        exact hfol _ (haI (t - F.recovery.d) (by omega) (by omega))

theorem entry_carrier_bound (hψ : 0 < ψ) (hκ : ψ ≤ κ + 1) :
    (LabelFreeElimination.protocol hψ κ).Q = UCell ψ κ ∧
      (allUCell ψ κ).length ≤ 4862332800 * 61931520000000 * (κ + 1) ^ 8 :=
  ⟨rfl, LabelFreeElimination.state_bound hψ hκ⟩

namespace DirtyEntryExample

def seed (i : Fin 5) : UCell 2 1 :=
  let old := LabelFreeElimination.NondivisibleExample.seed5 i
  { old with legacy := {old.legacy with
      bullet := if i = 3 then 1 else 0
      signal_B := if i = 4 then 1 else 0} }

theorem ring5 : DirectedRing 5 := ⟨by decide⟩
def gap : GapFrame 5 := ⟨ring5, 2, 3, by decide, by decide⟩

theorem separated : SeparatedClass ring5 2 seed := by
  refine ⟨by decide, by decide, ?_⟩
  unfold Separated
  decide

theorem gap_real : GapEndpointsPresent gap (physicalConfig seed) ∧
    GapInteriorFollowers gap (physicalConfig seed) := by
  constructor
  · unfold GapEndpointsPresent
    decide
  · intro i hi hid
    change i < 3 at hid
    have hh : i = 1 ∨ i = 2 := by omega
    rcases hh with rfl | rfl <;> decide

theorem bad : BadAt gap (physicalConfig seed) 1 :=
  ⟨by decide, by decide, by decide, 2, by decide, by decide, by decide⟩

theorem not_global : ¬ SignalGlobal ring5 seed := by
  intro hg
  have hh := ((signalGlobal_iff ring5 seed).mp hg).2 gap gap_real.1 gap_real.2
    1 2 (by decide) (by decide) bad.2.2.1 (by decide) (by decide)
  change (1 : Fin 2) = 0 at hh
  cases hh

theorem actual_ordered : SignalGlobal ring5 (LabelFreeElimination.step (by decide) ring5 seed 2) := by
  apply (signalGlobal_iff _ _).mpr
  constructor
  · unfold Separated
    decide
  · have hb : ∀ i, (LabelFreeElimination.step (by decide) ring5 seed 2 i).legacy.bullet = 0 := by decide
    intro G _ _ i _ _ _ hbullet
    exact (hbullet (hb _)).elim

theorem actual_ordered_payload :
    entryOutcome (by decide) ring5 seed seed 2 =
      .ordered (LabelFreeElimination.step (by decide) ring5 seed 2) := by
  have hd : ¬ K2FiniteProgress.count (LabelFreeElimination.step (by decide) ring5 seed 2) <
      K2FiniteProgress.count seed := by decide
  simp only [entryOutcome, if_neg hd, if_pos actual_ordered]

theorem nondivisible_and_half_mass : ¬ 2 ∣ 5 ∧
    5 ^ (2 * (5 * 5)) ≤ 2 * successCount (entryStep (by decide) ring5 seed)
      (initialNode ring5 seed) (2 * (5 * 5)) :=
  ⟨by decide, entry_half_mass (by decide) (by decide) ring5 seed separated⟩

end DirtyEntryExample

namespace ActualMergeExample

theorem ring7 : DirectedRing 7 := ⟨by decide⟩
def frame : TwoGapFrame 7 :=
  ⟨⟨ring7, 0, 2, by decide, by decide⟩,
    ⟨ring7, 2, 2, by decide, by decide⟩, by decide, by decide⟩

def seed (i : Fin 7) : UCell 2 1 :=
  { legacy := { boundedCanonical (by decide) 1 i with
      label := 1
      leader := decide (i = 0 ∨ i = 2 ∨ i = 4)
      shield := false
      signal_B := if i = 3 then 1 else 0
      bullet := if i = 1 then 1 else if i = 3 then 2 else 0 }
    control := (finiteCut 0).control }

theorem separated : SeparatedClass ring7 3 seed := by
  refine ⟨by decide, by decide, ?_⟩
  unfold Separated
  decide

theorem frames_real :
    (GapEndpointsPresent frame.recovery (physicalConfig seed) ∧
      GapInteriorFollowers frame.recovery (physicalConfig seed)) ∧
    (GapEndpointsPresent frame.attack (physicalConfig seed) ∧
      GapInteriorFollowers frame.attack (physicalConfig seed)) := by
  constructor <;> constructor
  · unfold GapEndpointsPresent
    decide
  · intro i hi hid
    change i < 2 at hid
    have hh : i = 1 := by omega
    subst i
    decide
  · unfold GapEndpointsPresent
    decide
  · intro i hi hid
    change i < 2 at hid
    have hh : i = 1 := by omega
    subst i
    decide

theorem old_ranks : badTop frame.recovery (physicalConfig seed) = 0 ∧
    badTop frame.attack (physicalConfig seed) = 1 ∧
    bulletTop frame.recovery (physicalConfig seed) = 1 ∧
    signalTop frame.attack (physicalConfig seed) = 1 := by
  refine ⟨?_, ?_, by decide, by decide⟩
  · apply (badTop_zero_iff _ _).mpr
    intro i j hi _ _ hij hjd
    change j ≤ 2 at hjd
    have hh : j = 1 ∨ j = 2 := by omega
    rcases hh with rfl | rfl <;> decide
  · apply Nat.le_antisymm
    · apply badTop_le_of
      intro i hi
      have hid : i ≤ 2 := hi.2.1
      by_cases he : i = 2
      · subst i
        exact (hi.2.2.1 (by decide)).elim
      · omega
    · exact badAt_le_top _ _ ⟨by decide, by decide, by decide, 1, by decide, by decide, by decide⟩

theorem actual_deletes :
    (LabelFreeElimination.step (by decide) ring7 seed 2 2).legacy.leader = false ∧
    K2FiniteProgress.count (LabelFreeElimination.step (by decide) ring7 seed 2) = 2 := by decide

theorem rank_increases_on_merge :
    badTop (merged frame) (physicalConfig (LabelFreeElimination.step (by decide) ring7 seed 2)) = 3 ∧
    badTop frame.recovery (physicalConfig seed) + badTop frame.attack (physicalConfig seed) = 1 := by
  constructor
  · have hh := deletion_merge_badTop (by decide) frame seed frames_real.2.1 frames_real.2.2 actual_deletes.1
    rw [old_ranks.2.2.2, old_ranks.1, old_ranks.2.1, old_ranks.2.2.1] at hh
    exact hh
  · rw [old_ranks.1, old_ranks.2.1]

theorem actual_merged_frame :
    GapEndpointsPresent (merged frame) (physicalConfig (LabelFreeElimination.step (by decide) ring7 seed 2)) ∧
    GapInteriorFollowers (merged frame) (physicalConfig (LabelFreeElimination.step (by decide) ring7 seed 2)) :=
  merged_shape_after_deletion (by decide) frame seed frames_real.1.1 frames_real.1.2
    frames_real.2.1 frames_real.2.2 actual_deletes.1

end ActualMergeExample

end LabelFreeSignalEntry
