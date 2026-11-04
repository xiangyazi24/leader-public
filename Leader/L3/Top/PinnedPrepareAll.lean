import Leader.L3.Top.PinnedPrepareSettled

/-!
# Q7 (preparation, lemma 1): every pending or settled register of the run is flagged

In a run from a state whose pending inputs are all post-anchor (`topClockNoOldPending`) and that
has no settled register, every pending or settled register stays flagged: a flagged input keeps
its flag when it moves or settles, and the accepted packet is flagged at once.  Hence the
reading of the flagged registers is the reading of ALL pending or settled registers
(`PuAll`), and the labelled window invariant `PuInv` becomes a statement about the whole window.

* `pu_pair_all` : on a window edge, a pending or settled output comes from a pending or settled
  input of the edge;
* `pu_step_all` : `PuAll` is inductive along `PuStep` while the window stays front-free and
  carry-free;
* `pulinv_all_word` : the same along a word, with the invariant `PuLinv`;
* `pulinv_all_of_noS` : the initial state.

Consumer: `Leader/L3/Top/PinnedPrepareAlign.lean`.
-/

namespace L3
namespace MarkedCells

open Classical

set_option autoImplicit false
set_option linter.unusedSimpArgs false

/-- Every pending or settled register is flagged.

Consumer: `pu_step_all`. -/
def PuAll (r : Nat) (c : Nat → Cell) (o : Nat → Bool) : Prop :=
  ∀ j, j < r → puNonE (c j).i = true → o j = true

/-- On a front-free, carry-free window edge that creates no obstacle, a pending or settled
output comes from a pending or settled input of the edge.

Consumer: `pu_step_all`. -/
theorem pu_pair_all (b : Bool) (x y : Cell)
    (hx : x.c = .off ∧ x.i ≠ .x) (hy : y.c = .off ∧ y.i ≠ .x)
    (hnb : ¬ (x.i = .st ∨ (b = true ∧ x.i.isS = true))) :
    (puNonE (pair b false x y).1.i = true → puNonE x.i = true) ∧
    (puNonE (pair b false x y).2.i = true →
      puNonE y.i = true ∨ (puNonE x.i = true ∧ puNonE y.i = false)) := by
  rcases x with ⟨xi, xk⟩
  rcases y with ⟨yi, yk⟩
  obtain ⟨hxk, hxx⟩ := hx
  obtain ⟨hyk, hyx⟩ := hy
  simp only at hxk hxx hyk hyx hnb
  subst hxk hyk
  cases xi <;> cases yi <;> cases b <;>
    simp (config := { decide := true })
      [pair, inSlots, carries, puNonE, Inp.isP, Inp.isS] at hxx hyx hnb ⊢

/-- The terminal edge: a pending or settled output comes from a pending or settled input.

Consumer: `pu_step_all`. -/
theorem pu_pair_all_term (x : Cell) (hx : x.c = .off ∧ x.i ≠ .x) (hnb : x.i ≠ .st) :
    puNonE (pair false true x { i := .e, c := .off }).1.i = true → puNonE x.i = true := by
  rcases x with ⟨xi, xk⟩
  obtain ⟨hxk, hxx⟩ := hx
  simp only at hxk hxx hnb
  subst hxk
  cases xi <;>
    simp (config := { decide := true })
      [pair, inSlots, carries, puNonE, Inp.isP, Inp.isS] at hxx hnb ⊢

/-- **`PuAll` is inductive along the abstract steps** that stay front-free and carry-free.

Consumer: `pulinv_all_word`. -/
theorem pu_step_all {α : Type} (r : Nat) (hr : 2 ≤ r) (Q Q' : List α) (c c' : Nat → Cell)
    (o o' : Nat → Bool) (ℓ ℓ' : Nat → α) (h : PuInv r Q c o ℓ) (hall : PuAll r c o)
    (hst : PuStep r c o ℓ Q c' o' ℓ' Q') (hfree : puFree r c') : PuAll r c' o' := by
  cases hst with
  | frame => exact hall
  | edge p hp =>
    have hnb : ¬ PuBorn p (c p) := fun hb => pu_born_edge r p hp c h.1 hb hfree
    have hnb' : ¬ ((c p).i = .st ∨ (decide (p = 0) = true ∧ (c p).i.isS = true)) := by
      intro h'
      apply hnb
      unfold PuBorn
      rcases h' with h' | ⟨h1, h2⟩
      · exact Or.inl h'
      · exact Or.inr ⟨by simpa using h1, h2⟩
    have hpl := pu_pair_all (decide (p = 0)) (c p) (c (p + 1)) (h.1 p (by omega))
      (h.1 (p + 1) hp) hnb'
    intro j hj hne
    by_cases hjp : j = p
    · subst hjp
      simp only [setTwo, if_true] at hne
      have hx := hall j hj (hpl.1 hne)
      simp only [puFlagsEdge, if_true]
      simp [hx, hne]
    · by_cases hjq : j = p + 1
      · subst hjq
        simp only [setTwo, if_neg hjp, if_true] at hne
        simp only [puFlagsEdge, if_neg hjp, if_true]
        rcases hpl.2 hne with hy | ⟨hx, hy⟩
        · have := hall (p + 1) hj hy
          simp [this, hne]
        · have := hall p (by omega) hx
          simp [this, hne, hy]
      · simp only [setTwo, if_neg hjp, if_neg hjq] at hne
        simp only [puFlagsEdge, if_neg hjp, if_neg hjq]
        exact hall j hj hne
  | term =>
    have hnb : (c (r - 1)).i ≠ .st := fun hb => pu_born_term r hr c h.1 hb hfree
    have hpl := pu_pair_all_term (c (r - 1)) (h.1 (r - 1) (by omega)) hnb
    intro j hj hne
    by_cases hjp : j = r - 1
    · subst hjp
      simp only [setOne, if_true] at hne
      have hx := hall (r - 1) hj (hpl hne)
      simp only [puFlagsTerm, if_true]
      simp [hx, hne]
    · simp only [setOne, if_neg hjp] at hne
      simp only [puFlagsTerm, if_neg hjp]
      exact hall j hj hne
  | clean =>
    have hc : portClean (c 0) = c 0 := pu_port_clean _ (h.1 0 (by omega)).1
    intro j hj hne
    by_cases hj0 : j = 0
    · subst hj0
      simp only [setOne, if_true, hc] at hne
      simp [hc, hall 0 hj hne, hne]
    · simp only [setOne, if_neg hj0] at hne
      simp only [if_neg hj0]
      exact hall j hj hne
  | accept t a h0 =>
    intro j hj hne
    by_cases hj0 : j = 0
    · subst hj0; simp
    · simp only [setOne, if_neg hj0] at hne
      simp only [if_neg hj0]
      exact hall j hj hne

/-- Every pending or settled register of the window is flagged.

Consumer: `pulinv_all_step`. -/
def PuAllAt {n : Nat} (s : Fin n) (Y : TopFixedTraceState n) (τ : Nat) : Prop :=
  PuAll (topClockSpan n) (cellOf s Y) (paFlagSettled s Y τ)

/-- **One letter keeps `PuAll`** when the next window is front-free and carry-free.

Consumer: `pulinv_all_word`. -/
theorem pulinv_all_step {n : Nat} (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (s : Fin n) (hg : WinGeo ring C s) (τ : Nat) (Y : TopFixedTraceState n)
    (hreach : topClockReached ring C Y) (hτ : τ ≤ Y.1.2.clock) (e : Fin n)
    (hnone : ∀ ex ∈ topClockConcreteExportsAfter s (topFixedTraceNext ring C Y e) τ,
      ex.operand ≠ none)
    (hfree : puFree (topClockSpan n) (cellOf s (topFixedTraceNext ring C Y e)))
    (h : PuLinv s Y τ) (hall : PuAllAt s Y τ) :
    PuAllAt s (topFixedTraceNext ring C Y e) τ := by
  obtain ⟨c', o', ℓ', Q', hst, hag⟩ := bridge_step_settled ring C s hg τ Y hreach hτ e hnone
  have hr3 := span_ge_three hg.hn
  obtain ⟨hc, hf, _, _⟩ := hag
  have hfree' : puFree (topClockSpan n) c' := fun j hj => by
    rw [← hc j hj]; exact hfree j hj
  have hall' : PuAll (topClockSpan n) (cellOf s Y) (paFlagSettled s Y τ) := hall
  have hst' := pu_step_all _ (by omega) _ _ _ _ _ _ _ _ h hall' hst hfree'
  intro j hj hne
  rw [hf j hj]
  apply hst' j hj
  rw [← hc j hj]
  exact hne

/-- **The pending-or-settled invariant and `PuAll` along a word** whose states keep the window
front-free and carry-free.

Consumer: `Leader/L3/Top/PinnedPrepareAlign.lean`. -/
theorem pulinv_all_word {n : Nat} (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (s : Fin n) (hg : WinGeo ring C s) (τ : Nat) :
    ∀ (w : List (Fin n)) (Z : TopFixedTraceState n), topClockReached ring C Z →
      τ ≤ Z.1.2.clock → PuLinv s Z τ → PuAllAt s Z τ → FreeRun ring C s Z w →
      (∀ ex ∈ topClockConcreteExportsAfter s (w.foldl (topFixedTraceNext ring C) Z) τ,
        ex.operand ≠ none) →
      PuLinv s (w.foldl (topFixedTraceNext ring C) Z) τ ∧
        PuAllAt s (w.foldl (topFixedTraceNext ring C) Z) τ := by
  intro w
  induction w with
  | nil => intro Z _ _ h ha _ _; exact ⟨h, ha⟩
  | cons e rest ih =>
    intro Z hreach hτ h ha hfr hnone
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
    apply ih _ hreach' (by omega) (pulinv_step ring C s hg τ Z hreach hτ e hn1 hfree1 h)
      (pulinv_all_step ring C s hg τ Z hreach hτ e hn1 hfree1 h ha) _ hnone
    intro i hi
    have := hfr (i + 1) (by simp; omega)
    simpa using this

/-- **`PuAll` at a state without settled registers whose pending inputs are all post-anchor.**

Consumer: `Leader/L3/Top/PinnedPrepareAlign.lean`. -/
theorem pulinv_all_of_noS {n : Nat} (s : Fin n) (Y : TopFixedTraceState n) (τ : Nat)
    (hold : topClockNoOldPending s Y τ)
    (hnoS : ∀ j, j < topClockSpan n → (cellOf s Y j).i.isS = false) :
    PuAllAt s Y τ := by
  intro j hj hne
  rw [cell_nonE_iff] at hne
  have hP : (Y.1.1 (winSite s j)).qIn.isP = true := by
    have h1 := cell_nonE_iff s Y j
    have h2 := cell_isP_iff s Y j
    have h3 := hnoS j hj
    unfold puNonE at h1
    rw [h3, Bool.or_false, h2] at h1
    rw [h1]
    exact hne
  rw [paFlagSettled_iff]
  refine ⟨hj, hne, ?_⟩
  have := hold ⟨j, hj⟩ (by unfold topClockConcreteInputAt; exact hP)
  exact this

end MarkedCells
end L3

#print axioms L3.MarkedCells.pu_step_all
#print axioms L3.MarkedCells.pulinv_all_word
#print axioms L3.MarkedCells.pulinv_all_of_noS
