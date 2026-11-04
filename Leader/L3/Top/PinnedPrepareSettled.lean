import Leader.L3.Top.PinnedPrepareBridge
import Leader.L3.Top.SuffixLinv

/-!
# Q7 (preparation, lemma 1): the settled registers keep their serial order

The labelled window invariant of `TopSuffixLinv` flags the PENDING registers whose atom was
accepted after the anchor.  A pending input that settles leaves that reading.  The invariant
`PuInv` of `TopPinnedPrepareCells` flags every pending or settled register with a post-anchor
atom; while the window holds no erasure front and no live carry, the labels of these registers
read right to left are a suffix `Q.drop k` of the exports after the anchor.  In particular
settled registers hold consecutive serials, and the oldest pending serial follows the newest
settled one.

* `pulinv_step` : one letter of a reached state keeps the invariant, or creates a front or a
  live carry (`pu_born_edge`, `pu_born_term`);
* `pulinv_word` : the invariant along a word whose states are all front-free and carry-free;
* `pulinv_of_noS` : the invariant at a reached state without settled registers (for instance a
  pending-only state), from the pending labelled window `linv_reached`.

Consumer: `Leader/L3/TopPinnedPrepareCert.lean`, `Leader/L3/Top/PinnedPrepareAlign.lean`.
-/

namespace L3
namespace MarkedCells

open Classical

set_option autoImplicit false
set_option linter.unusedSimpArgs false

/-- The pending-or-settled labelled window invariant of a state.

Consumer: `pulinv_step`, `pulinv_word`. -/
def PuLinv {n : Nat} (s : Fin n) (Y : TopFixedTraceState n) (τ : Nat) : Prop :=
  PuInv (topClockSpan n) (paQ s Y τ) (cellOf s Y) (paFlagSettled s Y τ) (paLabSettled s Y)

/-- The invariant of a state that agrees with an abstract window satisfying it.

Consumer: `pulinv_step`. -/
theorem pulinv_of_agree {n : Nat} (s : Fin n) (Z : TopFixedTraceState n) (τ : Nat)
    (c' : Nat → Cell) (o' : Nat → Bool) (ℓ' : Nat → PaLabel n) (Q' : List (PaLabel n))
    (hag : PuAgree s Z τ c' o' ℓ' Q') (h : PuInv (topClockSpan n) Q' c' o' ℓ') :
    PuLinv s Z τ := by
  obtain ⟨hc, hf, hl, hq⟩ := hag
  obtain ⟨hfree, hI, k, hk, hlist⟩ := h
  refine ⟨?_, ?_, k, ?_, ?_⟩
  · intro j hj
    rw [hc j hj]
    exact hfree j hj
  · intro j hj hoj
    rw [hf j hj] at hoj
    rw [hc j hj]
    exact hI j hj hoj
  · rw [hq]; exact hk
  · rw [hq, ← hlist]
    exact ordLab_congr _ _ _ _ _ (fun j hj => hf j hj)
      (fun j hj hoj => hl j hj (by rw [← hf j hj]; exact hoj))

/-- **One letter of a reached state keeps the pending-or-settled invariant or creates an
obstacle**: if the next state has no front and no live carry in the window, the invariant holds
there.

Consumer: `pulinv_word`. -/
theorem pulinv_step {n : Nat} (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (s : Fin n) (hg : WinGeo ring C s) (τ : Nat) (Y : TopFixedTraceState n)
    (hreach : topClockReached ring C Y) (hτ : τ ≤ Y.1.2.clock) (e : Fin n)
    (hnone : ∀ ex ∈ topClockConcreteExportsAfter s (topFixedTraceNext ring C Y e) τ,
      ex.operand ≠ none)
    (hfree : puFree (topClockSpan n) (cellOf s (topFixedTraceNext ring C Y e)))
    (h : PuLinv s Y τ) :
    PuLinv s (topFixedTraceNext ring C Y e) τ := by
  obtain ⟨c', o', ℓ', Q', hst, hag⟩ := bridge_step_settled ring C s hg τ Y hreach hτ e hnone
  have hr3 := span_ge_three hg.hn
  have hfree' : puFree (topClockSpan n) c' := fun j hj => by
    rw [← hag.1 j hj]; exact hfree j hj
  exact pulinv_of_agree s _ τ c' o' ℓ' Q' hag (pu_step_inv _ (by omega) _ _ _ _ _ _ _ _ h hst hfree')

/-- Every state reached after `i` letters of the word is front-free and carry-free in the window.

Consumer: `pulinv_word`. -/
def FreeRun {n : Nat} (ring : DirectedRing n) (C : HeadlineConfiguration n) (s : Fin n)
    (Z : TopFixedTraceState n) (w : List (Fin n)) : Prop :=
  ∀ i, i ≤ w.length →
    puFree (topClockSpan n) (cellOf s ((w.take i).foldl (topFixedTraceNext ring C) Z))

/-- **The pending-or-settled invariant along a word** whose states keep the window front-free and
carry-free, as long as the exports after the anchor carry operands.

Consumer: `pulinv_reached`. -/
theorem pulinv_word {n : Nat} (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (s : Fin n) (hg : WinGeo ring C s) (τ : Nat) :
    ∀ (w : List (Fin n)) (Z : TopFixedTraceState n), topClockReached ring C Z →
      τ ≤ Z.1.2.clock → PuLinv s Z τ → FreeRun ring C s Z w →
      (∀ ex ∈ topClockConcreteExportsAfter s (w.foldl (topFixedTraceNext ring C) Z) τ,
        ex.operand ≠ none) →
      PuLinv s (w.foldl (topFixedTraceNext ring C) Z) τ := by
  intro w
  induction w with
  | nil => intro Z _ _ h _ _; exact h
  | cons e rest ih =>
    intro Z hreach hτ h hfr hnone
    simp only [List.foldl_cons] at hnone ⊢
    have hn1 : ∀ ex ∈ topClockConcreteExportsAfter s (topFixedTraceNext ring C Z e) τ,
        ex.operand ≠ none :=
      fun ex hex => hnone ex (exportsAfter_fold_mono ring C s τ rest _ ex hex)
    have hreach' := topClockReachedNext ring C Z e hreach
    have hfree1 : puFree (topClockSpan n) (cellOf s (topFixedTraceNext ring C Z e)) := by
      have := hfr 1 (by simp)
      simpa using this
    have hclock : Z.1.2.clock ≤ (topFixedTraceNext ring C Z e).1.2.clock := by
      have : (topFixedTraceNext ring C Z e).1.2.clock = Z.1.2.clock + 1 := by
        simp [topFixedTraceNext, digitAuditStep]
      omega
    apply ih _ hreach' (by omega) (pulinv_step ring C s hg τ Z hreach hτ e hn1 hfree1 h) _ hnone
    intro i hi
    have := hfr (i + 1) (by simp; omega)
    simpa using this

/-- Without settled registers the window flags of the two labelled windows coincide.

Consumer: `pulinv_of_noS`. -/
theorem paFlagSettled_of_noS {n : Nat} (s : Fin n) (Y : TopFixedTraceState n) (τ : Nat)
    (hnoS : ∀ j, j < topClockSpan n → (cellOf s Y j).i.isS = false) (j : Nat) :
    paFlagSettled s Y τ j = paFlag s Y τ j := by
  apply Bool.eq_iff_iff.2
  rw [paFlagSettled_iff, paFlag_iff]
  constructor
  · rintro ⟨hj, hne, hp⟩
    refine ⟨hj, ?_, hp⟩
    have h1 := cell_nonE_iff s Y j
    have h2 := cell_isP_iff s Y j
    have h3 := hnoS j hj
    unfold puNonE at h1
    rw [h3, Bool.or_false, h2] at h1
    rw [← h1] at hne
    exact hne.symm ▸ rfl
  · rintro ⟨hj, hP, hp⟩
    refine ⟨hj, ?_, hp⟩
    unfold tokNonE
    rw [hP]; rfl

/-- **The invariant at a state without settled registers**: a reached state whose window is
front-free, carry-free and settled-free, and whose exports after the anchor carry operands.

Consumer: `Leader/L3/Top/PinnedPrepareAlign.lean`. -/
theorem pulinv_of_noS {n : Nat} (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (s : Fin n) (hg : WinGeo ring C s) (τ : Nat) (Y : TopFixedTraceState n)
    (hreach : topClockReached ring C Y)
    (hnone : ∀ ex ∈ topClockConcreteExportsAfter s Y τ, ex.operand ≠ none)
    (hfree : puFree (topClockSpan n) (cellOf s Y))
    (hnoS : ∀ j, j < topClockSpan n → (cellOf s Y j).i.isS = false) :
    PuLinv s Y τ := by
  obtain ⟨_, _, k, hk, hlist⟩ := linv_reached ring C s hg τ Y hreach hnone
  have hF : ∀ j, j < topClockSpan n → paFlagSettled s Y τ j = paFlag s Y τ j :=
    fun j _ => paFlagSettled_of_noS s Y τ hnoS j
  refine ⟨hfree, ?_, k, hk, ?_⟩
  · intro j hj hoj
    obtain ⟨_, hne, _⟩ := (paFlagSettled_iff s Y τ j).1 hoj
    rw [cell_nonE_iff]
    exact hne
  · rw [← hlist]
    apply ordLab_congr
    · intro j hj; exact hF j hj
    · intro j hj hoj
      have hP : (Y.1.1 (winSite s j)).qIn.isP = true := by
        have := ((paFlag_iff s Y τ j).1 (by rw [← hF j hj]; exact hoj)).2.1
        exact this
      unfold paLabSettled paLab
      cases hq : (Y.1.1 (winSite s j)).qIn <;> simp [hq, InTok.isP, puTok] at hP ⊢

end MarkedCells
end L3

#print axioms L3.MarkedCells.pulinv_step
#print axioms L3.MarkedCells.pulinv_word
#print axioms L3.MarkedCells.pulinv_of_noS
