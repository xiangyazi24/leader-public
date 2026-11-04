import Leader.L3.Top.SuffixBridge
import Leader.L3.Top.OldMarkStep
import Leader.L3.Top.ClockCuts

/-!
# Q7: the serial suffix of the pending inputs at a pinned state

The labelled window invariant `LInv` (flagged pending inputs sit left of every obstacle, and read
right to left are a suffix of the accepted queue) holds along every word from the audit start,
for every time `τ`, as long as the exports after `τ` carry operands.  At a state that extends a
permanent first-tail cut and has no old pending input, this gives the serial suffix of the
pending inputs (`consecutivePendingSuffix_of_inv`): the suffix is derived from the history and
need not be carried.

Consumer: `Leader/L3/Top/SuffixFinalMobile.lean`.
-/

namespace L3
namespace MarkedCells

open Classical

set_option autoImplicit false

/-- An export after `τ` is a comparison export of the audit, later than `τ`.

Consumer: `exportsAfter_early`, `suffix_of_pinned`. -/
theorem mem_exportsAfter {n : Nat} (s : Fin n) (Z : TopFixedTraceState n) (τ : Nat)
    (ex : DigitExport (compileAdvice (ceilLogTwo n)) n)
    (h : ex ∈ topClockConcreteExportsAfter s Z τ) : ex ∈ cmpEx Z.1.2 ∧ τ < ex.time := by
  unfold topClockConcreteExportsAfter at h
  rw [List.mem_filter] at h
  obtain ⟨h1, h2⟩ := h
  refine ⟨h1, ?_⟩
  by_cases hc : τ < ex.time ∧ ex.source = certSite s (topClockSpan n - 1) ∧
      ex.destination = certSite s (topClockSpan n)
  · exact hc.1
  · rw [if_neg hc] at h2
    exact absurd h2 (by simp)

/-- No export is later than a clock that has not reached it.

Consumer: `linv_early`. -/
theorem exportsAfter_early {n : Nat} (s : Fin n) (Z : TopFixedTraceState n) (τ : Nat)
    (hlin : Lin Z.1.2) (hc : Z.1.2.clock ≤ τ) : topClockConcreteExportsAfter s Z τ = [] := by
  rcases hl : topClockConcreteExportsAfter s Z τ with _ | ⟨ex, rest⟩
  · rfl
  · exfalso
    have hm : ex ∈ topClockConcreteExportsAfter s Z τ := by rw [hl]; simp
    obtain ⟨h1, h2⟩ := mem_exportsAfter s Z τ ex hm
    have := (hlin.tEx ex h1).1
    omega

/-- The reading of a window without flags is empty.

Consumer: `linv_early`. -/
theorem ordLab_noflags {α : Type} (o : Nat → Bool) (ℓ : Nat → α) (h : ∀ j, o j = false) :
    ∀ m, ordLab o ℓ m = [] := by
  intro m
  induction m with
  | zero => rfl
  | succ m ih => simp [ordLab, h m, ih]

/-- **Before the clock reaches `τ` the labelled window invariant is trivial.**

Consumer: `linv_word`. -/
theorem linv_early {n : Nat} (s : Fin n) (Z : TopFixedTraceState n) (τ : Nat)
    (hlin : Lin Z.1.2) (hc : Z.1.2.clock ≤ τ) :
    LInv (topClockSpan n) (paQ s Z τ) (cellOf s Z) (paFlag s Z τ) (paLab s Z) := by
  have hE := exportsAfter_early s Z τ hlin hc
  have hQ : paQ s Z τ = [] := by
    unfold paQ
    rw [hE]
    rfl
  have hF : ∀ j, paFlag s Z τ j = false := by
    intro j
    cases h : paFlag s Z τ j
    · rfl
    · exfalso
      obtain ⟨_, _, hp⟩ := (paFlag_iff s Z τ j).1 h
      obtain ⟨ex, hex, _⟩ := hp
      rw [hE] at hex
      exact absurd hex (by simp)
  refine ⟨?_, ?_, 0, ?_, ?_⟩
  · intro j _ hj
    rw [hF j] at hj
    exact absurd hj (by decide)
  · intro j i _ _ hj
    rw [hF j] at hj
    exact absurd hj (by decide)
  · rw [hQ]
    exact Nat.le_refl _
  · rw [ordLab_noflags _ _ hF, hQ]
    rfl

/-- Exports after `τ` are never lost along a word.

Consumer: `linv_word`. -/
theorem exportsAfter_fold_mono {n : Nat} (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (s : Fin n) (τ : Nat) :
    ∀ (w : List (Fin n)) (Z : TopFixedTraceState n)
      (ex : DigitExport (compileAdvice (ceilLogTwo n)) n),
      ex ∈ topClockConcreteExportsAfter s Z τ →
        ex ∈ topClockConcreteExportsAfter s (w.foldl (topFixedTraceNext ring C) Z) τ := by
  intro w
  induction w with
  | nil => intro Z ex h; exact h
  | cons e rest ih =>
    intro Z ex h
    simp only [List.foldl_cons]
    apply ih
    obtain ⟨extra, hl, _⟩ := exportsAfter_next ring C s Z e τ
    rw [hl]
    exact List.mem_append_left _ h

/-- The labelled window invariant along a word.

Consumer: `linv_reached`. -/
theorem linv_word {n : Nat} (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (s : Fin n) (hg : WinGeo ring C s) (τ : Nat) :
    ∀ (w : List (Fin n)) (Z : TopFixedTraceState n), topClockReached ring C Z →
      LInv (topClockSpan n) (paQ s Z τ) (cellOf s Z) (paFlag s Z τ) (paLab s Z) →
      (∀ ex ∈ topClockConcreteExportsAfter s (w.foldl (topFixedTraceNext ring C) Z) τ,
        ex.operand ≠ none) →
      LInv (topClockSpan n) (paQ s (w.foldl (topFixedTraceNext ring C) Z) τ)
        (cellOf s (w.foldl (topFixedTraceNext ring C) Z))
        (paFlag s (w.foldl (topFixedTraceNext ring C) Z) τ)
        (paLab s (w.foldl (topFixedTraceNext ring C) Z)) := by
  have hn2 : 2 ≤ n := by have := hg.hn; omega
  intro w
  induction w with
  | nil => intro Z _ h _; exact h
  | cons e rest ih =>
    intro Z hreach h hnone
    simp only [List.foldl_cons] at hnone ⊢
    have hn1 : ∀ ex ∈ topClockConcreteExportsAfter s (topFixedTraceNext ring C Z e) τ,
        ex.operand ≠ none :=
      fun ex hex => hnone ex (exportsAfter_fold_mono ring C s τ rest _ ex hex)
    have hreach' := topClockReachedNext ring C Z e hreach
    apply ih _ hreach' _ hnone
    by_cases hτ : τ ≤ Z.1.2.clock
    · exact linv_step ring C s hg τ Z hreach hτ e hn1 h
    · have hc : (topFixedTraceNext ring C Z e).1.2.clock ≤ τ := by
        have : (topFixedTraceNext ring C Z e).1.2.clock = Z.1.2.clock + 1 := by
          simp [topFixedTraceNext, digitAuditStep]
        omega
      exact linv_early s _ τ (lin_reached ring C hn2 _ hreach') hc

/-- **The labelled window invariant at every reached state** whose exports after `τ` carry
operands.

Consumer: `suffix_of_pinned`. -/
theorem linv_reached {n : Nat} (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (s : Fin n) (hg : WinGeo ring C s) (τ : Nat) (Y : TopFixedTraceState n)
    (hreach : topClockReached ring C Y)
    (hnone : ∀ ex ∈ topClockConcreteExportsAfter s Y τ, ex.operand ≠ none) :
    LInv (topClockSpan n) (paQ s Y τ) (cellOf s Y) (paFlag s Y τ) (paLab s Y) := by
  have h0 : topClockReached ring C
      (((C, digitAuditInitial (piD C)), []) : TopFixedTraceState n) := by
    unfold topClockReached
    rfl
  have hlin0 : Lin (digitAuditInitial (piD C)) := lin_initial _
  have hearly := linv_early s (((C, digitAuditInitial (piD C)), []) : TopFixedTraceState n) τ
    hlin0 (Nat.zero_le _)
  have hY : Y = Y.2.foldl (topFixedTraceNext ring C)
      (((C, digitAuditInitial (piD C)), []) : TopFixedTraceState n) := hreach
  obtain ⟨w, hw⟩ : ∃ w : List (Fin n), Y = w.foldl (topFixedTraceNext ring C)
      (((C, digitAuditInitial (piD C)), []) : TopFixedTraceState n) := ⟨Y.2, hY⟩
  subst hw
  exact linv_word ring C s hg τ w _ h0 hearly hnone

/-! ### No old pending input is permanent -/

/-- No old pending input is the vanishing of every old flag.

Consumer: `noOld_next`. -/
theorem noOld_iff_flags {n : Nat} (s : Fin n) (Z : TopFixedTraceState n) (τ : Nat) :
    topClockNoOldPending s Z τ ↔ ∀ j, oldFlag s τ Z j = false := by
  constructor
  · intro h j
    cases hf : oldFlag s τ Z j
    · rfl
    · exfalso
      obtain ⟨hj, hP, hnp⟩ := (oldFlag_iff s τ Z j).1 hf
      exact hnp (h ⟨j, hj⟩ hP)
  · intro h j hP
    by_cases hpost : topClockPostAnchor s Z τ (topClockConcreteInputAtom s Z j)
    · exact hpost
    · exfalso
      have hfl : oldFlag s τ Z j.val = true := by
        rw [oldFlag_iff]
        exact ⟨j.isLt, hP, hpost⟩
      rw [h j.val] at hfl
      exact absurd hfl (by decide)

/-- **No old pending input is preserved by every edge** of a reached state.  Pending inputs of
the next state are the old pending inputs, moved, or the accepted packet, whose atom is the
operand of the export recorded in the same service.

Consumer: `topClockFinalMobilePhase_final_holds`. -/
theorem noOld_next {n : Nat} (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (s : Fin n) (hg : WinGeo ring C s) (τ : Nat) (Y : TopFixedTraceState n)
    (hreach : topClockReached ring C Y) (hτ : τ ≤ Y.1.2.clock) (e : Fin n)
    (h : topClockNoOldPending s Y τ) :
    topClockNoOldPending s (topFixedTraceNext ring C Y e) τ := by
  have hall : ∀ j, oldFlag s τ Y j = false := (noOld_iff_flags s Y τ).1 h
  apply (noOld_iff_flags s _ τ).2
  intro j
  cases hj : oldFlag s τ (topFixedTraceNext ring C Y e) j
  · rfl
  · exfalso
    have hjr := oldFlag_lt s τ _ j hj
    by_cases ha : ∃ p, p < topClockSpan n ∧ e = winSite s p
    · obtain ⟨p, hp, rfl⟩ := ha
      have h1 := old_next_window ring C s hg τ Y hreach p hp j hjr hj
      unfold flagsAt at h1
      by_cases hp1 : p + 1 < topClockSpan n
      · rw [if_pos hp1] at h1
        unfold flagsEdge at h1
        simp [hall, oldX, oldY] at h1
      · rw [if_neg hp1] at h1
        unfold flagsTerm at h1
        simp [hall, oldX] at h1
    · by_cases hb : e = certSite s (topClockSpan n - 1)
      · have h1 := old_next_port ring C s hg τ Y hreach hτ e hb _ rfl j hjr hj
        unfold flagsPort at h1
        simp [hall, oldX] at h1
      · have h1 := old_next_frame ring C s hg τ Y e ha hb j hjr hj
        rw [hall j] at h1
        exact absurd h1 (by decide)

/-! ### The suffix at a pinned state -/

/-- Pairwise distinct-or-empty operands without empty ones are distinct.

Consumer: `suffix_of_pinned`. -/
theorem nodup_of_pairwise_some {α : Type} (l : List (Option α))
    (h : l.Pairwise (fun a b => a ≠ b ∨ a = none)) (hn : ∀ a ∈ l, a ≠ none) : l.Nodup := by
  induction l with
  | nil => exact List.nodup_nil
  | cons a rest ih =>
    rw [List.pairwise_cons] at h
    rw [List.nodup_cons]
    refine ⟨?_, ih h.2 (fun b hb => hn b (List.mem_cons_of_mem _ hb))⟩
    intro hmem
    rcases h.1 a hmem with hne | hnn
    · exact hne rfl
    · exact hn a (by simp) hnn

/-- **The serial suffix at a pinned state.**  A state that extends a permanent first-tail cut and
has no pending input that is old with respect to the clock of the cut has the serial suffix of its
pending inputs: the labelled window invariant, read with the anchor of the cut, and the
distinctness of the exported operands (`Lin`).

Consumer: `topClockFinalMobilePhase_final_holds`. -/
theorem suffix_of_pinned {n : Nat} (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (s : Fin n) (hg : WinGeo ring C s) (Y0 Y : TopFixedTraceState n)
    (hcut : topFreshTailPermanentCut ring C s Y0) (hY : MarkedFrom ring C Y0 Y)
    (hold : topClockNoOldPending s Y Y0.1.2.clock) :
    topClockConcreteConsecutivePendingSuffix s Y := by
  have hn2 : 2 ≤ n := by have := hg.hn; omega
  have hreach := markedFrom_reached ring C Y0 Y hY
  obtain ⟨hreach0, _, anchor, hanchor, htime, hfuture⟩ := hcut
  obtain ⟨w, hw⟩ := hY
  have hanchorY : topClockConcreteTailAnchor s Y anchor := by
    rw [hw, topFixedTraceRunAppendWord ring C Y0.2 w, ← hreach0]
    exact topClockTailAnchorWord ring C s anchor w Y0 hanchor
  have hpure : topClockConcretePureStream s Y anchor := by
    rw [hw]
    exact hfuture w
  have hnone : ∀ ex ∈ topClockConcreteExportsAfter s Y anchor.time, ex.operand ≠ none := by
    intro ex hex
    obtain ⟨i, hi, hexi⟩ := List.getElem_of_mem hex
    obtain ⟨sample, _, _, _, _, hop, _, _⟩ := hpure ⟨i, hi⟩
    intro hnn
    have h1 : (topClockConcreteExportAt s Y anchor.time ⟨i, hi⟩).operand = none := by
      show (topClockConcreteExportsAfter s Y anchor.time)[i].operand = none
      rw [hexi]
      exact hnn
    rw [hop] at h1
    exact absurd h1 (by simp)
  have hlin := lin_reached ring C hn2 Y hreach
  have hnd : ((topClockConcreteExportsAfter s Y anchor.time).map (fun ex => ex.operand)).Nodup := by
    have hsub : (topClockConcreteExportsAfter s Y anchor.time).Sublist (cmpEx Y.1.2) :=
      List.filter_sublist
    have hpw := List.Pairwise.sublist (hsub.map (fun ex => ex.operand)) hlin.nodup
    apply nodup_of_pairwise_some _ hpw
    intro a ha
    rw [List.mem_map] at ha
    obtain ⟨ex, hex, rfl⟩ := ha
    exact hnone ex hex
  have hlinv := linv_reached ring C s hg anchor.time Y hreach hnone
  have hold' : topClockNoOldPending s Y anchor.time := by
    rw [htime]
    exact hold
  exact consecutivePendingSuffix_of_inv s Y anchor hanchorY hpure hlinv hold' hnd

end MarkedCells
end L3

#print axioms L3.MarkedCells.linv_reached
#print axioms L3.MarkedCells.noOld_next
#print axioms L3.MarkedCells.suffix_of_pinned
