import Leader.Wu.Elimination.SinkTwoGapReachInvariant
import Leader.Wu.Elimination.OutputSafety
import Leader.Wu.Elimination.GapOwnershipArcs
import Leader.Core.MinimalTripleChoice

/-!
Physical gap closure for the actual `sinkKernelC` row.  The coordinates and
signal order below are the existing `GapFrame` and `GapInvariant`; all layout
data are proof-only.  In particular, no merge or closure law is a record field.
-/

namespace K2GlobalGapClosure

open PPLLRepair LDSinkGapCleanup LDSinkKernelC LDSinkProtectedAbsorption
  LDTwoGapFrame LDSinkTwoGapEpochSuccessor LDSinkTwoGapReachInvariant
  K2OutputSafety

set_option autoImplicit false
set_option pp.structureInstances false

variable {n ψ : Nat}

/-! ## Exact local deletion row -/

/-- A leader with a follower on its right is deleted exactly when the old
shield and signal are zero and that follower has a live bullet.  FIRE runs
first, so a positive old signal prevents deletion by restoring the shield. -/
theorem kernel_delete_iff (hψ : 0 < ψ) (l r : AgentState ψ)
    (hl : l.leader = true) (hr : r.leader = false) :
    (sinkKernelC hψ l r).1.leader = false ↔
      l.shield = false ∧ l.signal_B = 0 ∧ r.bullet = 2 := by
  rcases fin2_cases l.signal_B with hs | hs <;>
    cases hsh : l.shield <;>
    rcases fin3_cases r.bullet with hb | hb | hb <;>
    simp [sinkKernelC, eliminateLeadersNoCollisionFire,
      absorbProtectedMove, eliminateLeadersNoCollisionZeroLeaderEgressMove,
      eliminateLeadersNoCollisionSignalLeaderSink, dummyBulletSink,
      hl, hr, hs, hsh, hb]

/-- In an invariant gap the incoming live bullet has signal zero.  The actual
deletion row therefore changes exactly the leader bit and the bullet value;
all other fields, including the initiator's pre-existing bullet, are framed. -/
theorem kernel_delete_row (hψ : 0 < ψ) (l r : AgentState ψ)
    (hl : l.leader = true) (hr : r.leader = false)
    (hd : (sinkKernelC hψ l r).1.leader = false)
    (hsr : r.signal_B = 0) :
    sinkKernelC hψ l r =
      ({ l with leader := false }, { r with bullet := 1 }) := by
  obtain ⟨hsh, hsl, hb⟩ := (kernel_delete_iff hψ l r hl hr).mp hd
  simp [sinkKernelC, eliminateLeadersNoCollisionFire,
    absorbProtectedMove, eliminateLeadersNoCollisionZeroLeaderEgressMove,
    eliminateLeadersNoCollisionSignalLeaderSink, dummyBulletSink,
    hl, hr, hsh, hsl, hb, hsr]
  intro _
  rfl

/-! ## Ring-only framing and monotonicity -/

/-- The raw K2 update agrees with every existing frame-indexed presentation:
`DirectedRing n` has only a positivity proof and no variable geometry. -/
theorem rawStep_eq_frame (hψ : 0 < ψ) (ring : DirectedRing n)
    (G : GapFrame n) (C : Fin n → AgentState ψ) (e : Fin n) :
    rawStep hψ ring C e = sinkStepC hψ G C e := by
  have hr : ring = G.ring := by cases ring; cases G.ring; rfl
  cases hr
  rfl

/-- Every actual K2 row preserves every pre-existing follower, with no
alignment, spacing, shielding, bullet, or reachability premise. -/
theorem rawStep_follower (hψ : 0 < ψ) (ring : DirectedRing n)
    (C : Fin n → AgentState ψ) (e i : Fin n) (hi : (C i).leader = false) :
    (rawStep hψ ring C e i).leader = false := by
  by_cases hL : i = e
  · subst i
    simpa [rawStep, updatePair] using
      kernelC_left_follower hψ (C e) (C (ring.rightNeighbor e)) hi
  · by_cases hR : i = ring.rightNeighbor e
    · subst i
      simpa [rawStep, updatePair, hL] using
        (kernelC_right_leader_eq hψ (C e) (C (ring.rightNeighbor e))).trans hi
    · simpa [rawStep, updatePair, hL, hR] using hi

/-- Only the initiator can lose its leader bit; in particular the row cannot
delete two distinct leaders. -/
theorem rawStep_leader_away (hψ : 0 < ψ) (ring : DirectedRing n)
    (C : Fin n → AgentState ψ) (e i : Fin n) (hi : i ≠ e) :
    (rawStep hψ ring C e i).leader = (C i).leader := by
  by_cases hR : i = ring.rightNeighbor e
  · subst i
    simpa [rawStep, updatePair, hi] using
      kernelC_right_leader_eq hψ (C e) (C (ring.rightNeighbor e))
  · simp [rawStep, updatePair, hi, hR]

private theorem step_at_left (hψ : 0 < ψ) (G : GapFrame n)
    (C : Fin n → AgentState ψ) (t : Nat) :
    sinkStepC hψ G C (G.pos t) (G.pos t) =
      (sinkKernelC hψ (C (G.pos t)) (C (G.pos (t + 1)))).1 := by
  simp [sinkStepC, updatePair, GapFrame.rightNeighbor_pos]

private theorem step_at_right (hψ : 0 < ψ) (G : GapFrame n)
    (C : Fin n → AgentState ψ) (t : Nat) (ht : t + 1 < n) :
    sinkStepC hψ G C (G.pos t) (G.pos (t + 1)) =
      (sinkKernelC hψ (C (G.pos t)) (C (G.pos (t + 1)))).2 := by
  have hh := G.pos_ne ht (by omega) (show t + 1 ≠ t by omega)
  simp [sinkStepC, updatePair, GapFrame.rightNeighbor_pos, hh]

private theorem step_at_other (hψ : 0 < ψ) (G : GapFrame n)
    (C : Fin n → AgentState ψ) (t i : Nat) (ht : t < n) (hi : i < n)
    (hne : i ≠ t) (hnext : i ≠ (t + 1) % n) :
    sinkStepC hψ G C (G.pos t) (G.pos i) = C (G.pos i) := by
  apply sinkStepC_other
  · exact G.pos_ne hi ht hne
  · rw [GapFrame.rightNeighbor_pos]
    exact G.pos_ne_mod hi hnext

/-! ## Actual clean-boundary rows -/

private theorem kernel_zero_followers (hψ : 0 < ψ) (l r : AgentState ψ)
    (hr : r.leader = false) (hrb : r.bullet = 0) :
    (sinkKernelC hψ l r).2.bullet = 0 := by
  rcases fin2_cases l.signal_B with hs | hs <;>
    cases hl : l.leader <;>
    simp [sinkKernelC, eliminateLeadersNoCollisionFire,
      absorbProtectedMove, eliminateLeadersNoCollisionZeroLeaderEgressMove,
      eliminateLeadersNoCollisionSignalLeaderSink, dummyBulletSink,
      hl, hr, hs, hrb]
  all_goals split <;> rfl

private theorem kernel_idle_left (hψ : 0 < ψ) (l r : AgentState ψ)
    (hl : l.leader = false) (hr : r.leader = false) (hrb : r.bullet = 0) :
    (sinkKernelC hψ l r).1 = l := by
  simp [sinkKernelC, eliminateLeadersNoCollisionFire,
    absorbProtectedMove, eliminateLeadersNoCollisionZeroLeaderEgressMove,
    eliminateLeadersNoCollisionSignalLeaderSink, dummyBulletSink, hl, hr, hrb]

private theorem kernel_clean_right_fire (hψ : 0 < ψ) (l r : AgentState ψ)
    (hl : l.leader = false) (hr : r.leader = true) (hrs : r.signal_B = 1)
    (ha : r.label = nextLabel hψ l) :
    (sinkKernelC hψ l r).1.signal_B = 0 ∧
      (sinkKernelC hψ l r).2.signal_B = 0 ∧
      (sinkKernelC hψ l r).2.bullet = 0 := by
  simp [sinkKernelC, eliminateLeadersNoCollisionFire,
    absorbProtectedMove, eliminateLeadersNoCollisionZeroLeaderEgressMove,
    eliminateLeadersNoCollisionSignalLeaderSink, dummyBulletSink,
    hl, hr, hrs, show r.label = ⟨(l.label.val + 1) % ψ, Nat.mod_lt _ hψ⟩ from ha]
  rfl

private theorem kernel_clean_left_fire (hψ : 0 < ψ) (l r : AgentState ψ)
    (hl : l.leader = true) (hls : l.signal_B = 1) :
    (sinkKernelC hψ l r).1.signal_B = 0 := by
  rcases fin2_cases r.signal_B with hs | hs <;>
    cases hr : r.leader <;>
    rcases fin3_cases r.bullet with hb | hb | hb <;>
    simp [sinkKernelC, eliminateLeadersNoCollisionFire,
      absorbProtectedMove, eliminateLeadersNoCollisionZeroLeaderEgressMove,
      eliminateLeadersNoCollisionSignalLeaderSink, dummyBulletSink,
      hl, hls, hr, hs, hb]

/-- A clean gap can create a bullet only at its shooter or the shooter's
immediate predecessor.  The literal FIRE/MOVE/SIGNAL rows set the necessary
suffix signals to zero in both cases.  The bound `2 ≤ d` is used at the
responder-fire edge, whose initiator must be a follower. -/
theorem clean_signal_step (hψ : 0 < ψ) (G : GapFrame n)
    (C : Fin n → AgentState ψ) (hi : GapInvariant hψ G C)
    (hc : CleanReady G C) (e : Fin n) :
    GapSignalBelowBullets G (sinkStepC hψ G C e) := by
  have hd := G.hd
  have hdn := G.hdn
  obtain ⟨hs, hb⟩ := hc
  have he : e = G.pos (G.off e) := (G.pos_off e).symm
  have htn := G.off_lt e
  rw [he]
  generalize G.off e = t at *
  intro i j hi1 hid hbi hij hjd
  have hit : i < n := by omega
  have hjn : j < n := by omega
  by_cases htd : t < G.d
  · have htn : t < n := by omega
    have hresp : (sinkStepC hψ G C (G.pos t) (G.pos (t + 1))).bullet = 0 := by
      rw [step_at_right hψ G C t (by omega)]
      by_cases htend : t + 1 = G.d
      · have hr := kernel_clean_right_fire hψ (C (G.pos t)) (C (G.pos (t + 1)))
          (hi.2.1 t (by omega) htd) (by simpa [htend] using hi.1.2)
          (by simpa [htend] using hs) (hi.2.2.1 t htd)
        exact hr.2.2
      · exact kernel_zero_followers hψ _ _
          (hi.2.1 (t + 1) (by omega) (by omega)) (hb (t + 1) (by omega) (by omega))
    have hie : i = t := by
      apply Classical.byContradiction
      intro hne
      by_cases hn : i = t + 1
      · subst i
        exact hbi hresp
      · have hout := step_at_other hψ G C t i htn hit hne (by simpa [Nat.mod_eq_of_lt (show t + 1 < n by omega)] using hn)
        exact hbi (by rw [hout]; exact hb i hi1 hid)
    subst i
    have htend : t + 1 = G.d := by
      apply Classical.byContradiction
      intro hne
      have hr := hi.2.1 (t + 1) (by omega) (by omega)
      have hl := hi.2.1 t hi1 htd
      have hz := kernel_idle_left hψ (C (G.pos t)) (C (G.pos (t + 1))) hl hr
        (hb (t + 1) (by omega) (by omega))
      exact hbi (by rw [step_at_left, hz]; exact hb t hi1 hid)
    have hfire := kernel_clean_right_fire hψ (C (G.pos t)) (C (G.pos (t + 1)))
      (hi.2.1 t hi1 htd) (by simpa [htend] using hi.1.2)
      (by simpa [htend] using hs) (hi.2.2.1 t htd)
    have hj : j = t ∨ j = t + 1 := by omega
    rcases hj with rfl | rfl
    · rw [step_at_left]; exact hfire.1
    · rw [step_at_right hψ G C t (by omega)]; exact hfire.2.1
  · by_cases hteq : t = G.d
    · subst t
      have hie : i = G.d := by
        apply Classical.byContradiction
        intro hne
        have hn : i ≠ (G.d + 1) % n := by
          by_cases hh : G.d + 1 < n
          · rw [Nat.mod_eq_of_lt hh]; omega
          · have hh : G.d + 1 = n := by omega
            rw [hh, Nat.mod_self]; omega
        have hout := step_at_other hψ G C G.d i hdn hit hne hn
        exact hbi (by rw [hout]; exact hb i hi1 hid)
      have hj : j = G.d := by omega
      rw [hj, step_at_left]
      exact kernel_clean_left_fire hψ _ _ hi.1.2 hs
    · have hn : i ≠ (t + 1) % n := by
        by_cases hh : t + 1 < n
        · rw [Nat.mod_eq_of_lt hh]; omega
        · have hh : t + 1 = n := by omega
          rw [hh, Nat.mod_self]; omega
      have hout := step_at_other hψ G C t i htn hit (by omega) hn
      exact (hbi (by rw [hout]; exact hb i hi1 hid)).elim

/-! ## Unconditional ordinary-row gap closure -/

/-- The old continuation theorem excluded clean pre-states.  The literal
clean-boundary calculation above removes that restriction entirely. -/
theorem gap_step (hψ : 0 < ψ) (G : GapFrame n)
    (C : Fin n → AgentState ψ) (hi : GapInvariant hψ G C)
    (e : Fin n) (hd : ¬ EndpointDeleted G (sinkStepC hψ G C e)) :
    GapInvariant hψ G (sinkStepC hψ G C e) := by
  classical
  by_cases hc : CleanReady G C
  · obtain ⟨hends, hfollowers, hlabels⟩ :=
      gapShape_step_of_invariant_not_deleted hψ G C e hi hd
    exact ⟨hends, hfollowers, hlabels, clean_signal_step hψ G C hi hc e⟩
  · apply gapInvariant_step_of_not_endpointDeleted hψ G C e hi _ hd
    rintro (hclean | hdeleted)
    · exact hc hclean
    · rcases hdeleted with h | h
      · exact Bool.noConfusion (hi.1.1.symm.trans h)
      · exact Bool.noConfusion (hi.1.2.symm.trans h)

/-! ## Physical merge splicing -/

/-- Delete the shared endpoint of two adjacent physical gaps and retain
their full concatenated arc.  The strict length bound is exactly the one
already stored in `TwoGapFrame`, and therefore allows a remaining third
leader outside the arc, including the transition from three leaders to two. -/
def merged (F : TwoGapFrame n) : GapFrame n where
  ring := F.recovery.ring
  low := F.recovery.low
  d := F.recovery.d + F.attack.d
  hd := by have := F.recovery.hd; omega
  hdn := F.length_lt

@[simp] theorem merged_pos (F : TwoGapFrame n) (t : Nat) :
    (merged F).pos t = F.recovery.pos t := rfl

theorem attack_pos_merged (F : TwoGapFrame n) (t : Nat) :
    F.attack.pos t = (merged F).pos (F.recovery.d + t) :=
  F.attack_pos_eq_recovery_offset t

private theorem pos_zero (G : GapFrame n) : G.pos 0 = G.low := by
  apply Fin.ext
  simp [GapFrame.pos, Nat.mod_eq_of_lt G.low.isLt]

/-- The deletion edge has the literal two-cell post-state, with a zero-signal
suffix throughout the attack gap.  No restriction is placed on bullets in
the recovery gap or anywhere else on the ring. -/
theorem deletion_shape (hψ : 0 < ψ) (F : TwoGapFrame n)
    (C : Fin n → AgentState ψ) (ha : GapInvariant hψ F.attack C)
    (hd : (sinkStepC hψ F.attack C (F.attack.pos 0) (F.attack.pos 0)).leader = false) :
    sinkStepC hψ F.attack C (F.attack.pos 0) =
      updatePair C (F.attack.pos 0) (F.attack.pos 1)
        ({ C (F.attack.pos 0) with leader := false },
         { C (F.attack.pos 1) with bullet := 1 }) ∧
    (∀ j, 1 ≤ j → j ≤ F.attack.d → (C (F.attack.pos j)).signal_B = 0) := by
  have hf := ha.2.1 1 (by omega) (by have := F.attack.hd; omega)
  have hk : (sinkKernelC hψ (C (F.attack.pos 0)) (C (F.attack.pos 1))).1.leader = false := by
    simpa only [step_at_left, Nat.zero_add] using hd
  have hb := ((kernel_delete_iff hψ _ _ ha.1.1 hf).mp hk).2.2
  have htail : ∀ j, 1 ≤ j → j ≤ F.attack.d →
      (C (F.attack.pos j)).signal_B = 0 := by
    intro j hj hjd
    exact ha.2.2.2 1 j (by omega) (by have := F.attack.hd; omega)
      (by rw [hb]; decide) hj hjd
  have hrow := kernel_delete_row hψ _ _ ha.1.1 hf hk
    (htail 1 (by omega) (by have := F.attack.hd; omega))
  constructor
  · unfold sinkStepC
    rw [GapFrame.rightNeighbor_pos]
    simpa only [Nat.zero_add, hrow]
  · exact htail

/-- Actual K2 deletion preserves the same signal-order invariant on the
merged physical gap.  The proof splices the old recovery order to the zero
attack suffix forced by the killing live bullet, and derives every changed
field from `sinkKernelC`.  No merge-validity or closure premise is carried. -/
theorem merge_after_deletion (hψ : 0 < ψ) (F : TwoGapFrame n)
    (C : Fin n → AgentState ψ)
    (hr : GapInvariant hψ F.recovery C) (ha : GapInvariant hψ F.attack C)
    (hd : (sinkStepC hψ F.attack C (F.attack.pos 0) (F.attack.pos 0)).leader = false) :
    GapInvariant hψ (merged F) (sinkStepC hψ F.attack C (F.attack.pos 0)) := by
  let D := sinkStepC hψ F.attack C (F.attack.pos 0)
  obtain ⟨hrow, htail⟩ := deletion_shape hψ F C ha hd
  have hsig : ∀ i, (D i).signal_B = (C i).signal_B := by
    intro i
    dsimp [D]
    rw [hrow]
    simp only [updatePair]
    split <;> (try split) <;> rename_i hh <;> simp only [hh]
  have hbullet : ∀ i, i ≠ F.attack.pos 1 → (D i).bullet = (C i).bullet := by
    intro i hh
    dsimp [D]
    rw [hrow]
    simp only [updatePair, if_neg hh]
    split <;> rename_i hh0 <;> simp only [hh0]
  have hlead : ∀ i, i ≠ F.attack.pos 0 → (D i).leader = (C i).leader := by
    intro i hh
    exact rawStep_leader_away hψ F.attack.ring C (F.attack.pos 0) i hh
  have he : F.attack.pos 0 = (merged F).pos F.recovery.d := by
    simpa only [Nat.add_zero] using attack_pos_merged F 0
  have hn := F.length_lt
  have hdr := F.recovery.hd
  have hda := F.attack.hd
  have hbeforeLabels : GapLabelAligned hψ (merged F) C := by
    intro t ht
    change t < F.recovery.d + F.attack.d at ht
    by_cases htr : t < F.recovery.d
    · exact hr.2.2.1 t htr
    · have hta : t - F.recovery.d < F.attack.d := by omega
      have hh := ha.2.2.1 (t - F.recovery.d) hta
      rw [attack_pos_merged, attack_pos_merged] at hh
      have h0 : F.recovery.d + (t - F.recovery.d) = t := by omega
      have h1 : F.recovery.d + (t - F.recovery.d + 1) = t + 1 := by omega
      simpa only [h0, h1] using hh
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · change (D ((merged F).pos 0)).leader = true
    rw [hlead _ (by rw [he]; exact (merged F).pos_ne (by omega) (by omega) (by omega))]
    exact hr.1.1
  · change (D ((merged F).pos (F.recovery.d + F.attack.d))).leader = true
    rw [← attack_pos_merged]
    rw [hlead _ (F.attack.pos_ne (by have := F.attack.hdn; omega)
      (by omega) (by omega))]
    exact ha.1.2
  · intro t ht htd
    change t < F.recovery.d + F.attack.d at htd
    by_cases htr : t < F.recovery.d
    · exact sinkStepC_follower_preserved hψ F.attack C (F.attack.pos 0) _
        (hr.2.1 t ht htr)
    · by_cases hte : t = F.recovery.d
      · subst t
        change (D ((merged F).pos F.recovery.d)).leader = false
        rw [← he]
        exact hd
      · have hta : 1 ≤ t - F.recovery.d ∧ t - F.recovery.d < F.attack.d := by omega
        have hpos : (merged F).pos t = F.attack.pos (t - F.recovery.d) := by
          rw [attack_pos_merged]
          congr 1
          omega
        rw [hpos]
        exact sinkStepC_follower_preserved hψ F.attack C (F.attack.pos 0) _
          (ha.2.1 _ hta.1 hta.2)
  · exact gapLabelAligned_step hψ (merged F) C (F.attack.pos 0) hbeforeLabels
  · intro i j hi1 hid hbi hij hjd
    change (D ((merged F).pos j)).signal_B = 0
    rw [hsig]
    change j ≤ F.recovery.d + F.attack.d at hjd
    by_cases hjr : j ≤ F.recovery.d
    · have hiR : i ≤ F.recovery.d := by omega
      have hneq : (merged F).pos i ≠ F.attack.pos 1 := by
        rw [attack_pos_merged]
        exact (merged F).pos_ne (by omega) (by omega) (by omega)
      have hib : (C (F.recovery.pos i)).bullet ≠ 0 := by
        intro hz
        apply hbi
        exact (hbullet _ hneq).trans hz
      exact hr.2.2.2 i j hi1 hiR hib hij hjr
    · have hja : 1 ≤ j - F.recovery.d ∧ j - F.recovery.d ≤ F.attack.d := by omega
      have hh := htail (j - F.recovery.d) hja.1 hja.2
      rw [attack_pos_merged] at hh
      have hj : F.recovery.d + (j - F.recovery.d) = j := by omega
      simpa only [hj] using hh

/-! ## Actual leader sets and global invariant -/

/-- The physical leader count is the sum of the actual `AgentState.leader`
bits.  This definition contains no controller or ghost count. -/
def physicalLeaderCount (C : Fin n → AgentState ψ) : Nat :=
  (List.ofFn (fun i => if (C i).leader then 1 else 0)).sum

private theorem sum_single (e : Fin n) :
    (List.ofFn (fun i : Fin n => if i = e then 1 else 0)).sum = 1 := by
  induction n with
  | zero => exact Fin.elim0 e
  | succ n ih =>
    have hz : ∀ i : Fin n, i.succ ≠ (0 : Fin (n + 1)) := by
      intro i hh
      have hval := congrArg Fin.val hh
      change i.val + 1 = 0 at hval
      omega
    refine Fin.cases ?_ (fun j => ?_) e
    · simp [List.ofFn_succ, hz, FiniteUniformStoppingTree.ofFn_sum_const]
    · rw [List.ofFn_succ, List.sum_cons]
      have hh : (0 : Fin (n + 1)) ≠ j.succ := fun h => hz j h.symm
      simpa [hh] using ih j

/-- Every actual K2 edge either preserves every leader bit or removes just
its real leader initiator.  This is independent of the global gap invariant. -/
theorem rawStep_layout_cases (hψ : 0 < ψ) (ring : DirectedRing n)
    (C : Fin n → AgentState ψ) (e : Fin n) :
    (∀ i, (rawStep hψ ring C e i).leader = (C i).leader) ∨
      ((C e).leader = true ∧ (rawStep hψ ring C e e).leader = false ∧
        ∀ i, i ≠ e → (rawStep hψ ring C e i).leader = (C i).leader) := by
  by_cases he : (rawStep hψ ring C e e).leader = (C e).leader
  · left
    intro i
    by_cases hie : i = e
    · simpa [hie] using he
    · exact rawStep_leader_away hψ ring C e i hie
  · right
    have hpre : (C e).leader = true := by
      cases hh : (C e).leader
      · exact (he ((rawStep_follower hψ ring C e e hh).trans hh.symm)).elim
      · rfl
    have hpost : (rawStep hψ ring C e e).leader = false := by
      cases hh : (rawStep hψ ring C e e).leader
      · rfl
      · exact (he (hh.trans hpre.symm)).elim
    exact ⟨hpre, hpost, rawStep_leader_away hψ ring C e⟩

/-- A real deletion lowers the physical count by exactly one, for arbitrary
K2 input rows.  There are no gap or output-safety assumptions. -/
theorem physical_count_drop (hψ : 0 < ψ) (ring : DirectedRing n)
    (C : Fin n → AgentState ψ) (e : Fin n)
    (hp : (C e).leader = true)
    (hd : (rawStep hψ ring C e e).leader = false) :
    physicalLeaderCount (rawStep hψ ring C e) + 1 = physicalLeaderCount C := by
  have heq : (fun i => if (C i).leader then 1 else 0) =
      (fun i => (if (rawStep hψ ring C e i).leader then 1 else 0) +
        (if i = e then 1 else 0)) := by
    funext i
    by_cases hie : i = e
    · subst i; simp [hp, hd]
    · rw [rawStep_leader_away hψ ring C e i hie]
      simp [hie]
  unfold physicalLeaderCount
  rw [heq, FiniteUniformStoppingTree.ofFn_sum_add, sum_single]

/-- The actual number of leaders never increases under any K2 row. -/
theorem physical_count_nonincrease (hψ : 0 < ψ) (ring : DirectedRing n)
    (C : Fin n → AgentState ψ) (e : Fin n) :
    physicalLeaderCount (rawStep hψ ring C e) ≤ physicalLeaderCount C := by
  apply FiniteUniformStoppingTree.ofFn_sum_le
  intro i
  cases hc : (C i).leader
  · rw [rawStep_follower hψ ring C e i hc]
    simp
  · cases (rawStep hψ ring C e i).leader <;> decide

/-- Nonadjacent physical leaders.  Since no row creates leaders, this spacing
condition can only improve.  In particular every consecutive cyclic gap
between two distinct leaders has distance at least two. -/
def Separated (ring : DirectedRing n) (C : Fin n → AgentState ψ) : Prop :=
  ∀ i, (C i).leader = true → (C (ring.rightNeighbor i)).leader = false

/-- A global class defined entirely by the real configuration.  Every
consecutive physical gap has the same signal-order condition used by the
cleanup theorems, and every physical edge is label aligned.  There is no
assumed step closure, merger, selected pair, or unique-shot restriction. -/
structure GlobalInvariant (hψ : 0 < ψ) (ring : DirectedRing n)
    (C : Fin n → AgentState ψ) : Prop where
  separated : Separated ring C
  labels : CyclicLabels hψ ring C
  signal : ∀ G : GapFrame n,
    GapEndpointsPresent G C → GapInteriorFollowers G C → GapSignalBelowBullets G C

/-- A count-indexed slice of the global class.  Count two is retained as the
terminal slice for a three-to-two leader deletion. -/
def GlobalClass (hψ : 0 < ψ) (ring : DirectedRing n) (k : Nat)
    (C : Fin n → AgentState ψ) : Prop :=
  2 ≤ k ∧ physicalLeaderCount C = k ∧ GlobalInvariant hψ ring C

/-- The fully aligned global class has an explicit arithmetic domain:
its original label modulus divides the ring size.  No all-modulus entrance
theorem is asserted by the physical closure result. -/
theorem global_requires_dvd (hψ : 0 < ψ) (ring : DirectedRing n)
    (C : Fin n → AgentState ψ) (hC : GlobalInvariant hψ ring C) : ψ ∣ n :=
  cyclicLabels_requires_dvd hψ ring C hC.labels

theorem global_gap (hψ : 0 < ψ) (ring : DirectedRing n)
    (C : Fin n → AgentState ψ) (hC : GlobalInvariant hψ ring C)
    (G : GapFrame n) (he : GapEndpointsPresent G C) (hi : GapInteriorFollowers G C) :
    GapInvariant hψ G C := by
  refine ⟨he, hi, ?_, hC.signal G he hi⟩
  intro t _
  have hh := hC.labels (G.pos t)
  have hr : ring = G.ring := by cases ring; cases G.ring; rfl
  rw [hr, GapFrame.rightNeighbor_pos] at hh
  exact hh

private theorem rawStep_leader_source (hψ : 0 < ψ) (ring : DirectedRing n)
    (C : Fin n → AgentState ψ) (e i : Fin n)
    (hi : (rawStep hψ ring C e i).leader = true) : (C i).leader = true := by
  cases hc : (C i).leader
  · have hh := rawStep_follower hψ ring C e i hc
    exact Bool.noConfusion (hh.symm.trans hi)
  · rfl

/-- Split an actual post-deletion gap at the old leader's clockwise offset.
Both pieces use the existing `GapFrame`, with its genuine distance bounds. -/
def splitFrame (G : GapFrame n) (t : Nat) (ht : 2 ≤ t) (hs : 2 ≤ G.d - t) :
    TwoGapFrame n where
  recovery := ⟨G.ring, G.low, t, ht, by have := G.hdn; omega⟩
  attack := ⟨G.ring, G.pos t, G.d - t, hs, by have := G.hdn; omega⟩
  shared := by simp only [pos_zero]; rfl
  length_lt := by dsimp; have := G.hdn; omega

@[simp] theorem splitFrame_recovery_pos (G : GapFrame n) (t : Nat)
    (ht : 2 ≤ t) (hs : 2 ≤ G.d - t) (j : Nat) :
    (splitFrame G t ht hs).recovery.pos j = G.pos j := rfl

theorem splitFrame_attack_pos (G : GapFrame n) (t : Nat)
    (ht : 2 ≤ t) (hs : 2 ≤ G.d - t) (j : Nat) :
    (splitFrame G t ht hs).attack.pos j = G.pos (t + j) :=
  (splitFrame G t ht hs).attack_pos_eq_recovery_offset j

@[simp] theorem merged_splitFrame (G : GapFrame n) (t : Nat)
    (ht : 2 ≤ t) (hs : 2 ≤ G.d - t) :
    merged (splitFrame G t ht hs) = G := by
  have hsum : t + (G.d - t) = G.d := by omega
  cases G
  simp only [splitFrame, merged] at *
  simp only [hsum]

/-- The global signal invariant survives every actual K2 edge.  A new
consecutive gap either already had the same leader-free interior or contains
the uniquely deleted leader.  The latter case is split at its actual offset
and discharged by `merge_after_deletion`. -/
theorem global_step (hψ : 0 < ψ) (ring : DirectedRing n)
    (C : Fin n → AgentState ψ) (hC : GlobalInvariant hψ ring C) (e : Fin n) :
    GlobalInvariant hψ ring (rawStep hψ ring C e) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i hi
    exact rawStep_follower hψ ring C e _
      (hC.separated i (rawStep_leader_source hψ ring C e i hi))
  · intro i
    simpa only [rawStep_label] using hC.labels i
  · intro G he hi
    have hring : ring = G.ring := by cases ring; cases G.ring; rfl
    have hpreEnds : GapEndpointsPresent G C :=
      ⟨rawStep_leader_source hψ ring C e _ he.1,
        rawStep_leader_source hψ ring C e _ he.2⟩
    have hnot : ¬ EndpointDeleted G (sinkStepC hψ G C e) := by
      rw [← rawStep_eq_frame hψ ring G]
      rintro (hh | hh)
      · exact Bool.noConfusion (he.1.symm.trans hh)
      · exact Bool.noConfusion (he.2.symm.trans hh)
    have oldGap : GapInteriorFollowers G C →
        GapSignalBelowBullets G (rawStep hψ ring C e) := by
      intro hf
      have hh := gap_step hψ G C (global_gap hψ ring C hC G hpreEnds hf) e hnot
      simpa only [← rawStep_eq_frame hψ ring G] using hh.2.2.2
    rcases rawStep_layout_cases hψ ring C e with hsame | ⟨hle, hdel, haway⟩
    · apply oldGap
      intro t ht htd
      rw [← hsame]
      exact hi t ht htd
    · let t := G.off e
      have htn : t < n := G.off_lt e
      have hpos : G.pos t = e := G.pos_off e
      have hne : ∀ s, s < n → s ≠ t → G.pos s ≠ e := by
        intro s hsn hst
        rw [← hpos]
        exact G.pos_ne hsn htn hst
      by_cases htInside : 0 < t ∧ t < G.d
      · have ht2 : 2 ≤ t := by
          apply Classical.byContradiction
          intro hh
          have ht1 : t = 1 := by omega
          have hz := hC.separated (G.pos 0) hpreEnds.1
          rw [hring, GapFrame.rightNeighbor_pos, Nat.zero_add, ← ht1, hpos] at hz
          exact Bool.noConfusion (hz.symm.trans hle)
        have hs2 : 2 ≤ G.d - t := by
          apply Classical.byContradiction
          intro hh
          have hd1 : t + 1 = G.d := by omega
          have hz := hC.separated e hle
          rw [hring, ← hpos, GapFrame.rightNeighbor_pos, hd1] at hz
          exact Bool.noConfusion (hz.symm.trans hpreEnds.2)
        let F := splitFrame G t ht2 hs2
        have hFzero : F.attack.pos 0 = e := by
          rw [splitFrame_attack_pos]
          simpa only [Nat.add_zero] using hpos
        have hFend : F.attack.pos F.attack.d = G.pos G.d := by
          rw [splitFrame_attack_pos]
          change G.pos (t + (G.d - t)) = G.pos G.d
          congr 1
          omega
        have hrecEnds : GapEndpointsPresent F.recovery C := by
          constructor
          · exact hpreEnds.1
          · change (C (G.pos t)).leader = true
            rw [hpos]
            exact hle
        have hrecFollowers : GapInteriorFollowers F.recovery C := by
          intro s hs hst
          have hsg : s < G.d := by change s < t at hst; omega
          have hh := haway (G.pos s) (hne s (by have := G.hdn; omega)
            (by change s < t at hst; omega))
          exact hh.symm.trans (hi s hs hsg)
        have hattEnds : GapEndpointsPresent F.attack C := by
          constructor
          · simpa only [hFzero] using hle
          · simpa only [hFend] using hpreEnds.2
        have hattFollowers : GapInteriorFollowers F.attack C := by
          intro s hs hsd
          change s < G.d - t at hsd
          rw [splitFrame_attack_pos]
          have hh := haway (G.pos (t + s))
            (hne (t + s) (by have := G.hdn; omega) (by omega))
          exact hh.symm.trans (hi (t + s) (by omega) (by omega))
        have hrec := global_gap hψ ring C hC F.recovery hrecEnds hrecFollowers
        have hatt := global_gap hψ ring C hC F.attack hattEnds hattFollowers
        have hstep : sinkStepC hψ F.attack C (F.attack.pos 0) = rawStep hψ ring C e := by
          rw [hFzero, ← rawStep_eq_frame hψ ring F.attack]
        have hdelete : (sinkStepC hψ F.attack C (F.attack.pos 0) (F.attack.pos 0)).leader = false := by
          rw [hstep, hFzero]
          exact hdel
        have hm := merge_after_deletion hψ F C hrec hatt hdelete
        have hMG : merged F = G := merged_splitFrame G t ht2 hs2
        simpa only [hMG, hstep] using hm.2.2.2
      · apply oldGap
        intro s hs hsd
        have hh := haway (G.pos s)
          (hne s (by have := G.hdn; omega) (by omega))
        exact hh.symm.trans (hi s hs hsd)

/-- After a row at three or more leaders, the same physical global class is
available with either the unchanged count or exactly one fewer leader. -/
theorem global_class_step (hψ : 0 < ψ) (ring : DirectedRing n) (k : Nat)
    (C : Fin n → AgentState ψ) (hk : 3 ≤ k) (hC : GlobalClass hψ ring k C)
    (e : Fin n) :
    (GlobalClass hψ ring k (rawStep hψ ring C e) ∧
      ∀ i, (rawStep hψ ring C e i).leader = (C i).leader) ∨
    (GlobalClass hψ ring (k - 1) (rawStep hψ ring C e) ∧
      (C e).leader = true ∧ (rawStep hψ ring C e e).leader = false) := by
  have hG := global_step hψ ring C hC.2.2 e
  rcases rawStep_layout_cases hψ ring C e with hsame | ⟨hp, hd, _⟩
  · left
    refine ⟨⟨hC.1, ?_, hG⟩, hsame⟩
    have hh : physicalLeaderCount (rawStep hψ ring C e) = physicalLeaderCount C := by
      unfold physicalLeaderCount
      congr 2
      funext i
      rw [hsame]
    exact hh.trans hC.2.1
  · right
    have hc := physical_count_drop hψ ring C e hp hd
    rw [hC.2.1] at hc
    exact ⟨⟨by omega, by omega, hG⟩, hp, hd⟩

/-- Three-to-two is the terminal count branch.  Both surviving cyclic gaps
still satisfy the actual gap invariant; no three-leader frame is asserted
after this step. -/
theorem three_to_two (hψ : 0 < ψ) (ring : DirectedRing n)
    (C : Fin n → AgentState ψ) (hC : GlobalClass hψ ring 3 C) (e : Fin n)
    (hp : (C e).leader = true) (hd : (rawStep hψ ring C e e).leader = false) :
    GlobalClass hψ ring 2 (rawStep hψ ring C e) := by
  have hc := physical_count_drop hψ ring C e hp hd
  rw [hC.2.1] at hc
  exact ⟨by decide, by omega, global_step hψ ring C hC.2.2 e⟩

/-- At four or more leaders a deletion leaves at least three, with the same
actual invariant ready for any subsequent physical gap selection. -/
theorem four_or_more_deletion (hψ : 0 < ψ) (ring : DirectedRing n)
    (k : Nat) (hk : 4 ≤ k) (C : Fin n → AgentState ψ)
    (hC : GlobalClass hψ ring k C) (e : Fin n)
    (hp : (C e).leader = true) (hd : (rawStep hψ ring C e e).leader = false) :
    3 ≤ k - 1 ∧ GlobalClass hψ ring (k - 1) (rawStep hψ ring C e) := by
  have hc := physical_count_drop hψ ring C e hp hd
  rw [hC.2.1] at hc
  exact ⟨by omega, ⟨by omega, by omega, global_step hψ ring C hC.2.2 e⟩⟩

/-! ## Pair interface and concrete nonemptiness -/

/-- Every newly selected pair of actual consecutive gaps is the repository's
real `GapPair`, for every existing ghost phase.  Selection changes neither
the configuration nor the protocol's state carrier. -/
theorem selected_gapPair (hψ : 0 < ψ) (ring : DirectedRing n)
    (C : Fin n → AgentState ψ) (hC : GlobalInvariant hψ ring C)
    (F : TwoGapFrame n)
    (hrE : GapEndpointsPresent F.recovery C)
    (hrI : GapInteriorFollowers F.recovery C)
    (haE : GapEndpointsPresent F.attack C)
    (haI : GapInteriorFollowers F.attack C)
    (phase : LDSinkTwoGapNoResetKernel.APhase) :
    GapPair hψ F ⟨C, phase⟩ :=
  ⟨global_gap hψ ring C hC F.recovery hrE hrI,
    global_gap hψ ring C hC F.attack haE haI⟩

/-- A cyclic enumeration of the physical gaps.  These are only geometric
facts: consecutive endpoints agree and the actual gap lengths sum to the
ring size.  Validity in a configuration is supplied separately by the
ordinary endpoint/interior predicates, never by a closure or merger field. -/
structure CyclicLayout (n k : Nat) where
  gap : Fin k → GapFrame n
  shared : ∀ i, (gap i).pos (gap i).d =
    (gap (MinimalTripleChoice.cyclicSucc i)).pos 0
  mass : (List.ofFn (fun i => (gap i).d)).sum = n

/-- Finite averaging selects genuine adjacent physical gaps, with the exact
`GapPair` invariant and span at most `2n/k` (in division-free form).  For
`k ≥ 3` the averaging inequality itself proves the strict sub-ring length
needed by `TwoGapFrame`.  The cyclic enumeration is ghost input only. -/
theorem select_short_pair (hψ : 0 < ψ) (ring : DirectedRing n)
    (k : Nat) (hk : 3 ≤ k) (C : Fin n → AgentState ψ)
    (hC : GlobalInvariant hψ ring C) (L : CyclicLayout n k)
    (hE : ∀ i, GapEndpointsPresent (L.gap i) C)
    (hI : ∀ i, GapInteriorFollowers (L.gap i) C) :
    ∃ F : TwoGapFrame n,
      k * (F.recovery.d + F.attack.d) ≤ 2 * n ∧
      ∀ phase : LDSinkTwoGapNoResetKernel.APhase, GapPair hψ F ⟨C, phase⟩ := by
  obtain ⟨i, hi⟩ := MinimalTripleChoice.minimalTripleChoice hk
    (fun i => (L.gap i).d) (Nat.le_of_eq L.mass)
  have hspan : (L.gap i).d + (L.gap (MinimalTripleChoice.cyclicSucc i)).d < n := by
    have hlow := Nat.mul_le_mul_right
      ((L.gap i).d + (L.gap (MinimalTripleChoice.cyclicSucc i)).d) hk
    have hn := ring.hn
    omega
  let F : TwoGapFrame n :=
    ⟨L.gap i, L.gap (MinimalTripleChoice.cyclicSucc i), L.shared i, hspan⟩
  exact ⟨F, hi, fun phase => selected_gapPair hψ ring C hC F
    (hE i) (hI i) (hE _) (hI _) phase⟩

/-- Signal-zero states produce the global order for arbitrary other bullets
and auxiliary fields.  This gives a broad, explicit producer for the class. -/
theorem global_of_signals_zero (hψ : 0 < ψ) (ring : DirectedRing n)
    (C : Fin n → AgentState ψ) (hsep : Separated ring C)
    (hlabel : CyclicLabels hψ ring C) (hs : ∀ i, (C i).signal_B = 0) :
    GlobalInvariant hψ ring C := by
  refine ⟨hsep, hlabel, ?_⟩
  intro G _ _ i j _ _ _ _ _
  exact hs _

/-- Four nonadjacent leaders and arbitrary simultaneous incoming live
bullets on an eight-site ring.  This witnesses the physical class, including
real deletions, without a unique-live-shot premise. -/
def seed8 (i : Fin 8) : AgentState 1 :=
  { PPLLNoCheckBirthOutputLegitimacy.outputCore (by decide) i with
    leader := decide (i.val % 2 = 0)
    shield := false
    signal_B := 0
    bullet := if i.val % 2 = 0 then 0 else 2 }

theorem seed8_class : GlobalClass (by decide) ⟨by decide⟩ 4 seed8 := by
  refine ⟨by decide, by decide, ?_⟩
  refine ⟨?_, cyclicLabels_one _ _, ?_⟩
  · unfold Separated
    decide
  · intro G _ _ i j _ _ _ _ _
    rfl

/-- This actual edge realizes the four-to-three branch with no initialization
or reachability assumption added to the invariant. -/
theorem seed8_three :
    GlobalClass (by decide) ⟨by decide⟩ 3
      (rawStep (by decide) ⟨by decide⟩ seed8 6) := by
  exact (four_or_more_deletion (by decide) ⟨by decide⟩ 4 (by decide)
    seed8 seed8_class 6 (by decide) (by decide)).2

/-- A second real deletion realizes the separately handled three-to-two
case.  All other live bullets remain governed by the same global invariant. -/
theorem seed8_two :
    GlobalClass (by decide) ⟨by decide⟩ 2
      (rawStep (by decide) ⟨by decide⟩
        (rawStep (by decide) ⟨by decide⟩ seed8 6) 4) := by
  exact three_to_two (by decide) ⟨by decide⟩ _ seed8_three 4 (by decide) (by decide)

/-- The actual cyclic layout after the first example deletion: lengths
two, two, and four, with the length-four gap crossing the removed leader. -/
def seed8_after_layout : CyclicLayout 8 3 where
  gap := fun i =>
    if i = 0 then ⟨⟨by decide⟩, 0, 2, by decide, by decide⟩
    else if i = 1 then ⟨⟨by decide⟩, 2, 2, by decide, by decide⟩
    else ⟨⟨by decide⟩, 4, 4, by decide, by decide⟩
  shared := by decide
  mass := by decide

/-- The freshly enumerated post-deletion gaps have their real endpoints
and follower interiors.  The example contains several live bullets. -/
theorem seed8_after_layout_real :
    (∀ i, GapEndpointsPresent (seed8_after_layout.gap i)
      (rawStep (by decide) ⟨by decide⟩ seed8 6)) ∧
    (∀ i, GapInteriorFollowers (seed8_after_layout.gap i)
      (rawStep (by decide) ⟨by decide⟩ seed8 6)) := by
  constructor
  · unfold GapEndpointsPresent
    decide
  · have hd : ∀ i, (seed8_after_layout.gap i).d ≤ 4 := by decide
    have hh : ∀ i : Fin 3, ∀ t : Fin 4,
        1 ≤ t.val → t.val < (seed8_after_layout.gap i).d →
        (rawStep (by decide) ⟨by decide⟩ seed8 6
          ((seed8_after_layout.gap i).pos t.val)).leader = false := by decide
    intro i t ht htd
    exact hh i ⟨t, by have := hd i; omega⟩ ht htd

/-- A checked fresh short-pair selection after an actual deletion, for every
ghost phase, witnesses that the selection interface is nonempty. -/
theorem seed8_reselection :
    ∃ F : TwoGapFrame 8,
      3 * (F.recovery.d + F.attack.d) ≤ 16 ∧
      ∀ phase : LDSinkTwoGapNoResetKernel.APhase,
        GapPair (by decide) F
          ⟨rawStep (by decide) ⟨by decide⟩ seed8 6, phase⟩ := by
  exact select_short_pair (by decide) ⟨by decide⟩ 3 (by decide) _
    seed8_three.2.2 seed8_after_layout seed8_after_layout_real.1 seed8_after_layout_real.2

end K2GlobalGapClosure
