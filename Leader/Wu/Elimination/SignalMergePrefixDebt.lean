import Leader.Wu.Elimination.SignalMergeWash
import Leader.Wu.Elimination.LabelFreeSignalEntry

/-!
# Old prefix disorder through actual post-merge suffix service

The artificial cut is a follower site after deletion. No endpoint-leader
assumption is imposed at that cut. Ordinary raw K2 rows cannot increase the
greatest bad bullet restricted to this prefix. Therefore the independently
proved right-sector service leaves exactly the old left-prefix debt, unless
another real endpoint deletion changes the frame again.
-/

namespace SignalMergePrefixDebt

open PPLLRepair LDSinkGapCleanup LDSinkKernelC LDSinkProtectedAbsorption
  LDTwoGapFrame LDSinkBoundedKernel LDSinkTwoGapEpochSuccessor K2GlobalGapClosure LabelFreeSignalEntry
  SignalMergeWash FiniteUniformStoppingTree

set_option autoImplicit false

variable {n : Nat}

/-- A violation with both witnesses in the retained left prefix. -/
def PrefixBadAt (G : GapFrame n) (cut : Nat) (C : Config n) (i : Nat) : Prop :=
  1 ≤ i ∧ i ≤ cut ∧ (C (G.pos i)).bullet ≠ 0 ∧
    ∃ j, i ≤ j ∧ j ≤ cut ∧ (C (G.pos j)).signal_B = 1

def PrefixDebt (G : GapFrame n) (cut : Nat) (C : Config n) (A : Nat) : Prop :=
  ∀ i, PrefixBadAt G cut C i → i ≤ A

private theorem left_row (G : GapFrame n) (C : Config n) (t : Nat) :
    post G C (G.pos t) (G.pos t) =
      (sinkKernelC (by decide) (C (G.pos t)) (C (G.pos (t + 1)))).1 := by
  simp [post, sinkStepC, updatePair, GapFrame.rightNeighbor_pos]

private theorem right_row (G : GapFrame n) (C : Config n) (t : Nat) (ht : t + 1 < n) :
    post G C (G.pos t) (G.pos (t + 1)) =
      (sinkKernelC (by decide) (C (G.pos t)) (C (G.pos (t + 1)))).2 := by
  have hn := G.pos_ne ht (by omega) (show t + 1 ≠ t by omega)
  simp [post, sinkStepC, updatePair, GapFrame.rightNeighbor_pos, hn]

private theorem other_row (G : GapFrame n) (C : Config n)
    (e : Fin n) (i : Nat) (hi : 1 ≤ i)
    (hl : e ≠ G.pos i) (hr : e ≠ G.pos (i - 1)) : post G C e (G.pos i) = C (G.pos i) := by
  apply sinkStepC_other
  · exact Ne.symm hl
  · intro h
    apply hr
    apply PPLLNoCheckBirthConditionTwoGeometry.rightNeighbor_injective G.ring
    rw [GapFrame.rightNeighbor_pos, Nat.sub_add_cancel hi]
    exact h.symm

private theorem prefix_signal_witness (G : GapFrame n) (cut : Nat) (hcut : cut < G.d)
    (C : Config n) (hi : GapInteriorFollowers G C) (e : Fin n) (i j : Nat)
    (hi1 : 1 ≤ i) (hij : i ≤ j) (hjc : j ≤ cut) (he : e ≠ G.pos (i - 1))
    (hs : (post G C e (G.pos j)).signal_B = 1) :
    ∃ s, i ≤ s ∧ s ≤ cut ∧ (C (G.pos s)).signal_B = 1 := by
  rcases signal_origin G C hi e j (by omega) (by omega) hs with
    hs | ⟨_, heq, hs⟩ | ⟨hj, heq⟩
  · exact ⟨j, hij, hjc, hs⟩
  · have hn : i ≠ j := by intro h; subst j; exact he heq
    exact ⟨j - 1, by omega, by omega, hs⟩
  · have h1 : i = 1 := by omega
    exact (he (by rw [h1]; exact heq)).elim

/-- Every bad output bullet in the prefix comes from an old bad bullet
at the same site or its next prefix site. A bullet entering across the cut
has a cleared signal at the cut and cannot create a prefix violation. -/
theorem prefix_bad_origin (G : GapFrame n) (cut : Nat) (hcut : cut < G.d)
    (C : Config n) (hg : GapShape G C) (e : Fin n)
    (hkeep : ¬ EndpointDeleted G (post G C e)) (i : Nat)
    (hbad : PrefixBadAt G cut (post G C e) i) :
    PrefixBadAt G cut C i ∨ (i < cut ∧ e = G.pos i ∧ PrefixBadAt G cut C (i + 1)) := by
  obtain ⟨hi, hic, hb, j, hij, hjc, hs⟩ := hbad
  have hid : i < G.d := by omega
  have hin : i < n := Nat.lt_trans hid G.hdn
  have hnot : e ≠ G.pos (i - 1) := by
    intro he
    subst e
    exact hb (responder_empty G C hg.1 hg.2 i hi (by omega) hkeep)
  by_cases he : e = G.pos i
  · subst e
    have hl := hg.2 i hi hid
    have hleft := left_row G C i
    have hright := right_row G C i (by have := G.hdn; omega)
    by_cases hf : (C (G.pos (i + 1))).leader = true ∧ (C (G.pos (i + 1))).signal_B = 1
    · have hlast : i + 1 = G.d := by
        apply Classical.byContradiction
        intro hh
        have hfol := hg.2 (i + 1) (by omega) (by omega)
        rw [hfol] at hf
        cases hf.1
      have hz := (entryRowFacts _ _).fire_right_zero hl hf.1 hf.2
      have hj : j = i := by omega
      rw [hj, hleft, hz.1] at hs
      cases hs
    · by_cases hrb : (C (G.pos (i + 1))).bullet = 0
      · have hb' : (C (G.pos i)).bullet ≠ 0 := by
          rw [hleft, (entryRowFacts _ _).idle_left hl hf hrb] at hb
          exact hb
        exact Or.inl ⟨hi, hic, hb',
          prefix_signal_witness G cut hcut C hg.2 _ i j hi hij hjc hnot hs⟩
      · have hz := (entryRowFacts _ _).move_left hl hf hrb
        have hjne : j ≠ i := by
          intro hj
          rw [hj, hleft, hz.1] at hs
          cases hs
        refine Or.inr ⟨by omega, rfl, by omega, by omega, hrb, j, by omega, hjc, ?_⟩
        by_cases hj : j = i + 1
        · rw [hj, hright, hz.2] at hs
          simpa only [hj] using hs
        · rw [other_row G C (G.pos i) j (by omega)
            (G.pos_ne hin (by have := G.hdn; omega) (by omega))
            (G.pos_ne hin (by have := G.hdn; omega) (by omega))] at hs
          exact hs
  · have hb' : (C (G.pos i)).bullet ≠ 0 := by
      rw [other_row G C e i hi he hnot] at hb
      exact hb
    exact Or.inl ⟨hi, hic, hb',
      prefix_signal_witness G cut hcut C hg.2 e i j hi hij hjc hnot hs⟩

/-- The debt predicate is closed at a follower cut, on every nondeleting
original edge. It is a statement about the current fields only. -/
theorem prefix_debt_step (G : GapFrame n) (cut : Nat) (hcut : cut < G.d)
    (C : Config n) (hg : GapShape G C) (A : Nat) (hA : PrefixDebt G cut C A)
    (e : Fin n) (hkeep : ¬ EndpointDeleted G (post G C e)) :
    PrefixDebt G cut (post G C e) A := by
  intro i hi
  rcases prefix_bad_origin G cut hcut C hg e hkeep i hi with hi | ⟨_, _, hi⟩
  · exact hA i hi
  · have hh := hA (i + 1) hi
    omega

theorem endpointDeleted_step (G : GapFrame n) (C : Config n) (e : Fin n)
    (hC : EndpointDeleted G C) : EndpointDeleted G (post G C e) := by
  rcases hC with hl | hr
  · exact Or.inl (sinkStepC_follower_preserved (by decide) G C e _ hl)
  · exact Or.inr (sinkStepC_follower_preserved (by decide) G C e _ hr)

theorem endpointDeleted_run (G : GapFrame n) (C : Config n) (es : List (Fin n))
    (hC : EndpointDeleted G C) : EndpointDeleted G (run (post G) C es) := by
  induction es generalizing C with
  | nil => exact hC
  | cons e es ih => exact ih _ (endpointDeleted_step G C e hC)

/-- A final surviving endpoint pair supplies every intermediate geometric
premise: original K2 rows cannot recreate a deleted leader. -/
theorem prefix_debt_run (G : GapFrame n) (cut : Nat) (hcut : cut < G.d)
    (C : Config n) (hg : GapShape G C) (A : Nat) (hA : PrefixDebt G cut C A)
    (es : List (Fin n)) (hkeep : ¬ EndpointDeleted G (run (post G) C es)) :
    PrefixDebt G cut (run (post G) C es) A := by
  induction es generalizing C with
  | nil => exact hA
  | cons e es ih =>
      have hd : ¬ EndpointDeleted G (post G C e) :=
        fun h => hkeep (endpointDeleted_run G (post G C e) es h)
      exact ih (post G C e) (gapShape_step G C hg e hd)
        (prefix_debt_step G cut hcut C hg A hA e hd) hkeep

/-- Once the suffix is actually clear, every remaining whole-gap violation
belongs to the old prefix and is bounded by that prefix's retained debt. -/
theorem cleared_badTop_le_prefix (G : GapFrame n) (cut : Nat) (C : Config n)
    (A : Nat) (hA : PrefixDebt G cut C A) (hc : RightClear G cut C) : badTop G C ≤ A := by
  apply badTop_le_of
  intro i hi
  obtain ⟨hi1, hid, hb, j, hij, hjd, hs⟩ := hi
  have hjc : j ≤ cut := by
    by_cases hjc : j ≤ cut
    · exact hjc
    · have hz := hc j (by omega) hjd
      rw [hz] at hs
      cases hs
  exact hA i ⟨hi1, by omega, hb, j, hij, hjc, hs⟩

/-- Actual shared-leader deletion does not change old left-prefix debt.
The old right gap may have arbitrary signal and bullet disorder. -/
theorem deletion_prefix_debt (F : TwoGapFrame n) (C : Config n)
    (hg : GapShape F.attack C)
    (hd : (post F.attack C (F.attack.pos 0) (F.attack.pos 0)).leader = false) :
    PrefixDebt (merged F) F.recovery.d (post F.attack C (F.attack.pos 0))
      (badTop F.recovery C) := by
  intro i hi
  have hb : BadAt F.recovery (post F.attack C (F.attack.pos 0)) i := by
    simpa only [PrefixBadAt, BadAt, merged_pos] using hi
  exact badAt_le_top F.recovery C
    ((deletion_preserves_badAt F.recovery F.attack C hg.1 hg.2 hd i).mp hb)

open LabelFreeElimination StateBoundUnifiedCell K2OutputSafety

variable {ψ κ : Nat}

private theorem actual_post_prefix (hψ : 0 < ψ) (F : TwoGapFrame n)
    (C : Fin n → UCell ψ κ) (ha : GapShape F.attack (observe C))
    (hd : (LabelFreeElimination.step hψ F.attack.ring C (F.attack.pos 0)
      (F.attack.pos 0)).legacy.leader = false) :
    PrefixDebt (merged F) F.recovery.d
      (observe (LabelFreeElimination.step hψ F.attack.ring C (F.attack.pos 0)))
      (badTop F.recovery (observe C)) := by
  have hd' : (post F.attack (observe C) (F.attack.pos 0) (F.attack.pos 0)).leader = false := by
    change (rawStep (by decide) F.attack.ring (observe C) (F.attack.pos 0)
      (F.attack.pos 0)).leader = false
    rw [← observe_step hψ F.attack.ring C (F.attack.pos 0)]
    exact hd
  rw [observe_step]
  exact deletion_prefix_debt F (observe C) ha hd'

/-- The suffix half-mass producer specialized to an actual deletion
successor. Its clock is `2*n*(2*b+1)` even when the old left gap is dirty. -/
theorem actual_merge_suffix_half (hψ : 0 < ψ) (F : TwoGapFrame n)
    (C : Fin n → UCell ψ κ) (hr : GapShape F.recovery (observe C))
    (ha : GapShape F.attack (observe C))
    (hd : (LabelFreeElimination.step hψ F.attack.ring C (F.attack.pos 0)
      (F.attack.pos 0)).legacy.leader = false) :
    n ^ (2 * n * (2 * F.attack.d + 1)) ≤
      2 * successCount (rawWashStep (merged F) F.recovery.d)
        (rawWashStart (merged F) F.recovery.d
          (observe (LabelFreeElimination.step hψ F.attack.ring C (F.attack.pos 0))))
        (2 * n * (2 * F.attack.d + 1)) := by
  have hg : GapShape (merged F)
      (observe (LabelFreeElimination.step hψ F.attack.ring C (F.attack.pos 0))) :=
    merged_shape_after_deletion hψ F C hr.1 hr.2 ha.1 ha.2 hd
  have hh := right_clear_half (merged F) F.recovery.d F.recovery.hd _ hg
  have hclock : (merged F).d - F.recovery.d = F.attack.d := by
    change F.recovery.d + F.attack.d - F.recovery.d = F.attack.d
    omega
  rw [hclock] at hh
  exact hh

theorem actual_merge_suffix_cost (hψ : 0 < ψ) (F : TwoGapFrame n)
    (C : Fin n → UCell ψ κ) (hr : GapShape F.recovery (observe C))
    (ha : GapShape F.attack (observe C))
    (hd : (LabelFreeElimination.step hψ F.attack.ring C (F.attack.pos 0)
      (F.attack.pos 0)).legacy.leader = false) (T : Nat) :
    truncatedActiveCostNumerator (rawWashStep (merged F) F.recovery.d)
      (rawWashStart (merged F) F.recovery.d
        (observe (LabelFreeElimination.step hψ F.attack.ring C (F.attack.pos 0)))) T ≤
      n ^ T * (n * (2 * F.attack.d + 1)) := by
  have hg : GapShape (merged F)
      (observe (LabelFreeElimination.step hψ F.attack.ring C (F.attack.pos 0))) :=
    merged_shape_after_deletion hψ F C hr.1 hr.2 ha.1 ha.2 hd
  have hh := right_clear_truncated_cost (merged F) F.recovery.d F.recovery.hd _ hg T
  have hclock : (merged F).d - F.recovery.d = F.attack.d := by
    change F.recovery.d + F.attack.d - F.recovery.d = F.attack.d
    omega
  rw [hclock] at hh
  exact hh

/-- Each successful original word reaches an actual same-word prefix with
either a further physical endpoint deletion, or a clear right sector and
whole-gap badTop at most the pre-deletion left badTop. No left-order
assumption and no restarted global cost budget is hidden in this result. -/
theorem actual_merge_suffix_residual (hψ : 0 < ψ) (F : TwoGapFrame n)
    (C : Fin n → UCell ψ κ) (hr : GapShape F.recovery (observe C))
    (ha : GapShape F.attack (observe C))
    (hd : (LabelFreeElimination.step hψ F.attack.ring C (F.attack.pos 0)
      (F.attack.pos 0)).legacy.leader = false)
    (es : List (Fin n))
    (hs : run (stepNode (rawWashStep (merged F) F.recovery.d))
      (rawWashStart (merged F) F.recovery.d
        (observe (LabelFreeElimination.step hψ F.attack.ring C (F.attack.pos 0)))) es = .success) :
    ∃ pre suf, es = pre ++ suf ∧
      let D := run (LabelFreeElimination.step hψ (merged F).ring)
        (LabelFreeElimination.step hψ F.attack.ring C (F.attack.pos 0)) pre
      EndpointDeleted (merged F) (observe D) ∨
        (RightClear (merged F) F.recovery.d (observe D) ∧
          badTop (merged F) (observe D) ≤ badTop F.recovery (observe C)) := by
  let D := LabelFreeElimination.step hψ F.attack.ring C (F.attack.pos 0)
  have hg : GapShape (merged F) (observe D) :=
    merged_shape_after_deletion hψ F C hr.1 hr.2 ha.1 ha.2 hd
  have hp := actual_post_prefix hψ F C ha hd
  obtain ⟨pre, suf, he, hdone⟩ := physical_wash_success_prefix hψ (merged F)
    F.recovery.d D es hs
  refine ⟨pre, suf, he, ?_⟩
  dsimp only
  by_cases hdel : EndpointDeleted (merged F)
      (observe (run (LabelFreeElimination.step hψ (merged F).ring) D pre))
  · exact Or.inl hdel
  · have hclear : RightClear (merged F) F.recovery.d
        (observe (run (LabelFreeElimination.step hψ (merged F).ring) D pre)) := by
      rcases hdone with hh | hh
      · exact (hdel hh).elim
      · exact hh
    refine Or.inr ⟨hclear, ?_⟩
    apply cleared_badTop_le_prefix _ _ _ _ _ hclear
    rw [observe_run] at hdel ⊢
    exact prefix_debt_run (merged F) F.recovery.d
      (by change F.recovery.d < F.recovery.d + F.attack.d; have := F.attack.hd; omega)
      (observe D) hg _ hp pre hdel

/-- If the old left piece is ordered, the same right-side service reaches
whole-gap order. The old right piece remains completely unrestricted. -/
theorem ordered_left_merge_suffix_order (hψ : 0 < ψ) (F : TwoGapFrame n)
    (C : Fin n → UCell ψ κ) (hr : GapShape F.recovery (observe C))
    (ha : GapShape F.attack (observe C))
    (ho : GapSignalBelowBullets F.recovery (observe C))
    (hd : (LabelFreeElimination.step hψ F.attack.ring C (F.attack.pos 0)
      (F.attack.pos 0)).legacy.leader = false)
    (es : List (Fin n))
    (hs : run (stepNode (rawWashStep (merged F) F.recovery.d))
      (rawWashStart (merged F) F.recovery.d
        (observe (LabelFreeElimination.step hψ F.attack.ring C (F.attack.pos 0)))) es = .success) :
    ∃ pre suf, es = pre ++ suf ∧
      let D := run (LabelFreeElimination.step hψ (merged F).ring)
        (LabelFreeElimination.step hψ F.attack.ring C (F.attack.pos 0)) pre
      EndpointDeleted (merged F) (observe D) ∨ GapSignalBelowBullets (merged F) (observe D) := by
  obtain ⟨pre, suf, hw, hp⟩ := actual_merge_suffix_residual hψ F C hr ha hd es hs
  refine ⟨pre, suf, hw, ?_⟩
  dsimp only at hp ⊢
  rcases hp with hdel | ⟨_, hb⟩
  · exact Or.inl hdel
  · have hz := (badTop_zero_iff F.recovery (observe C)).mpr ho
    rw [hz] at hb
    exact Or.inr ((badTop_zero_iff _ _).mp (Nat.eq_zero_of_le_zero hb))

namespace Witness

/-- The same eight-site pattern on the actual finite carrier. -/
def seed (i : Fin 8) : UCell 1 0 :=
  { legacy := { boundedCanonical (by decide) 0 i with
      leader := (witnessPre i).leader, shield := (witnessPre i).shield,
      bullet := (witnessPre i).bullet, signal_B := (witnessPre i).signal_B }
    control := (finiteCut 0).control }

def afterDeletion : Fin 8 → UCell 1 0 :=
  LabelFreeElimination.step (by decide) witnessFrame.attack.ring seed (witnessFrame.attack.pos 0)

theorem geometry : GapShape witnessFrame.recovery (observe seed) ∧
    GapShape witnessFrame.attack (observe seed) := by
  constructor
  · refine ⟨⟨by decide, by decide⟩, ?_⟩
    intro t ht htd
    change t < 4 at htd
    have he : t = 1 ∨ t = 2 ∨ t = 3 := by omega
    rcases he with rfl | rfl | rfl <;> decide
  · refine ⟨⟨by decide, by decide⟩, ?_⟩
    intro t ht htd
    change t < 2 at htd
    have he : t = 1 := by omega
    subst t
    decide

theorem deleted : (afterDeletion (witnessFrame.attack.pos 0)).legacy.leader = false := by decide

theorem old_left_dirty : BadAt witnessFrame.recovery (observe seed) 1 :=
  ⟨by decide, by decide, by decide, 2, by decide, by decide, by decide⟩

theorem successor_not_done : ¬ WashDone (merged witnessFrame) 4 (observe afterDeletion) := by
  rintro ((hl | hr) | hz)
  · exact (by decide : (observe afterDeletion ((merged witnessFrame).pos 0)).leader ≠ false) hl
  · exact (by decide : (observe afterDeletion ((merged witnessFrame).pos 6)).leader ≠ false) hr
  · have hh := hz 5 (by decide) (by decide)
    exact (by decide : (observe afterDeletion ((merged witnessFrame).pos 5)).signal_B ≠ 0) hh

theorem half : 8 ^ 80 ≤
    2 * successCount (rawWashStep (merged witnessFrame) 4) (.active (observe afterDeletion)) 80 := by
  have hh := actual_merge_suffix_half (by decide) witnessFrame seed geometry.1 geometry.2 deleted
  have ht : 2 * 8 * (2 * witnessFrame.attack.d + 1) = 80 := rfl
  rw [ht] at hh
  have hr : witnessFrame.recovery.d = 4 := rfl
  have he : LabelFreeElimination.step (by decide) witnessFrame.attack.ring seed
      (witnessFrame.attack.pos 0) = afterDeletion := rfl
  rw [hr, he] at hh
  rw [rawWashStart, if_neg successor_not_done] at hh
  exact hh

/-- Two literal right-side interactions really clear that sector while
the old left violation persists. Thus the residual debt is necessary. -/
theorem two_edges_clear_with_old_debt :
    let D := run (LabelFreeElimination.step (by decide) (merged witnessFrame).ring)
      afterDeletion [5, 5]
    RightClear (merged witnessFrame) 4 (observe D) ∧
      ¬ GapSignalBelowBullets (merged witnessFrame) (observe D) := by
  dsimp only
  constructor
  · intro j hj hjd
    change j ≤ 6 at hjd
    have he : j = 5 ∨ j = 6 := by omega
    rcases he with rfl | rfl <;> decide
  · intro ho
    have hh := ho 1 2 (by decide) (by decide) (by decide) (by decide) (by decide)
    exact (by decide : (observe (run (LabelFreeElimination.step (by decide)
      (merged witnessFrame).ring) afterDeletion [5, 5]) ((merged witnessFrame).pos 2)).signal_B ≠ 0) hh

end Witness

end SignalMergePrefixDebt

#print axioms SignalMergePrefixDebt.prefix_bad_origin
#print axioms SignalMergePrefixDebt.prefix_debt_step
#print axioms SignalMergePrefixDebt.prefix_debt_run
#print axioms SignalMergePrefixDebt.cleared_badTop_le_prefix
#print axioms SignalMergePrefixDebt.deletion_prefix_debt
#print axioms SignalMergePrefixDebt.actual_merge_suffix_half
#print axioms SignalMergePrefixDebt.actual_merge_suffix_cost
#print axioms SignalMergePrefixDebt.actual_merge_suffix_residual
#print axioms SignalMergePrefixDebt.ordered_left_merge_suffix_order
#print axioms SignalMergePrefixDebt.Witness.old_left_dirty
#print axioms SignalMergePrefixDebt.Witness.successor_not_done
#print axioms SignalMergePrefixDebt.Witness.half
#print axioms SignalMergePrefixDebt.Witness.two_edges_clear_with_old_debt
