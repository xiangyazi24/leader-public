import Leader.L3.Top.PinnedCarryCells

/-!
# Q7 (P.12 preparation): the carry sweep on the physical trace and its first-hit cost

Every edge of a reached state whose window is aligned, or carries a host, keeps the window in the
same family; the host moves exactly on its own edge.  Hence the window is cleared by the retiring
carry within `n * (r + 1)` expected interactions.

Consumer: the aligned-completion half of `TopClockFavourablePhase` (not yet proved).
-/

namespace L3
namespace MarkedCells

open Classical
set_option autoImplicit false
set_option linter.unusedSimpArgs false

/-- The window is aligned, carries a host, or has been cleared.

Consumer: `carry_cost`. -/
def CarryFamily (r : Nat) (cells : Nat → Cell) : Prop :=
  AlignShape r cells ∨ (∃ k, CarryShape r k cells) ∨ CarryDone r cells

/-- A cell family with the host at the border register only at the host.

Consumer: `carry_phi_carry`. -/
theorem carryShape_unique (r k k' : Nat) (cells : Nat → Cell) (h : CarryShape r k cells)
    (h' : CarryShape r k' cells) : k = k' := by
  rcases Nat.lt_trichotomy k k' with hlt | heq | hgt
  · exfalso
    have h1 := h.2.2.1
    have h2 := h'.2.1 k hlt
    rw [h1] at h2
    obtain ⟨_, h3⟩ := h2
    exact absurd h3 (by decide)
  · exact heq
  · exfalso
    have h1 := h'.2.2.1
    have h2 := h.2.1 k' hgt
    rw [h1] at h2
    obtain ⟨_, h3⟩ := h2
    exact absurd h3 (by decide)

/-- An aligned window is not a host window.

Consumer: `carry_phi_carry`. -/
theorem align_not_carry (r k : Nat) (cells : Nat → Cell) (h : AlignShape r cells)
    (h' : CarryShape r k cells) : False := by
  by_cases hk : k = 0
  · subst hk
    have h1 := h'.2.2.1
    rw [h.2.1] at h1
    exact absurd h1 (by decide)
  · have := h'.2.1 0 (by omega)
    rw [h.2.1] at this
    obtain ⟨h3, _⟩ := this
    simp [Inp.isP] at h3

/-- A cleared window is not aligned.

Consumer: `carry_phi_align`. -/
theorem align_not_done (r : Nat) (cells : Nat → Cell) (h : AlignShape r cells)
    (h' : CarryDone r cells) : False := by
  have := h' 0 (by have := h.1; omega)
  rw [h.2.1] at this
  obtain ⟨h3, _⟩ := this
  simp [Inp.isP] at h3

/-- A host window is not cleared.

Consumer: `carry_phi_carry`. -/
theorem carry_not_done (r k : Nat) (cells : Nat → Cell) (h : CarryShape r k cells)
    (h' : CarryDone r cells) : False := by
  have := h' k h.1
  rw [h.2.2.1] at this
  exact absurd this.2 (by decide)

/-- A reached state whose window is in the carry family.

Consumer: `carry_cost`. -/
def CarryInv {n : Nat} (ring : DirectedRing n) (C : HeadlineConfiguration n) (s : Fin n)
    (Y : TopFixedTraceState n) : Prop :=
  topClockReached ring C Y ∧ CarryFamily (topClockSpan n) (cellOf s Y)

/-- The potential: one launch, then one service per register.

Consumer: `carry_cost`. -/
noncomputable def carryPhi {n : Nat} (s : Fin n) (Y : TopFixedTraceState n) : Nat :=
  if AlignShape (topClockSpan n) (cellOf s Y) then topClockSpan n + 1
  else if h : ∃ k, CarryShape (topClockSpan n) k (cellOf s Y) then
    topClockSpan n - Classical.choose h
  else 0

/-- The potential on an aligned window.

Consumer: `carry_cost`. -/
theorem carry_phi_align {n : Nat} (s : Fin n) (Y : TopFixedTraceState n)
    (h : AlignShape (topClockSpan n) (cellOf s Y)) : carryPhi s Y = topClockSpan n + 1 := by
  unfold carryPhi; rw [if_pos h]

/-- The potential on a host window.

Consumer: `carry_cost`. -/
theorem carry_phi_carry {n : Nat} (s : Fin n) (Y : TopFixedTraceState n) (k : Nat)
    (h : CarryShape (topClockSpan n) k (cellOf s Y)) : carryPhi s Y = topClockSpan n - k := by
  unfold carryPhi
  have hna : ¬ AlignShape (topClockSpan n) (cellOf s Y) := fun ha => align_not_carry _ _ _ ha h
  rw [if_neg hna]
  have hex : ∃ k, CarryShape (topClockSpan n) k (cellOf s Y) := ⟨k, h⟩
  rw [dif_pos hex]
  rw [carryShape_unique _ _ k _ (Classical.choose_spec hex) h]

/-- The potential on a cleared window.

Consumer: `carry_cost`. -/
theorem carry_phi_done {n : Nat} (s : Fin n) (Y : TopFixedTraceState n)
    (h : CarryDone (topClockSpan n) (cellOf s Y)) : carryPhi s Y = 0 := by
  unfold carryPhi
  have hna : ¬ AlignShape (topClockSpan n) (cellOf s Y) := fun ha => align_not_done _ _ ha h
  rw [if_neg hna]
  have hnc : ¬ ∃ k, CarryShape (topClockSpan n) k (cellOf s Y) :=
    fun ⟨k, hk⟩ => carry_not_done _ _ _ hk h
  rw [dif_neg hnc]

/-- The aligned shape only reads the window.

Consumer: `carry_next_align`. -/
theorem align_congr (r : Nat) (cells cells' : Nat → Cell)
    (h : ∀ j, j < r → cells' j = cells j) (hS : AlignShape r cells) : AlignShape r cells' := by
  obtain ⟨h1, h2, h3⟩ := hS
  refine ⟨h1, ?_, ?_⟩
  · rw [h 0 (by omega)]; exact h2
  · intro j hj hj0; rw [h j hj]; exact h3 j hj hj0

/-- The host shape only reads the window.

Consumer: `carry_next_carry`. -/
theorem carry_congr (r k : Nat) (cells cells' : Nat → Cell)
    (h : ∀ j, j < r → cells' j = cells j) (hS : CarryShape r k cells) :
    CarryShape r k cells' := by
  obtain ⟨h1, h2, h3, h4⟩ := hS
  refine ⟨h1, ?_, ?_, ?_⟩
  · intro j hj; rw [h j (by omega)]; exact h2 j hj
  · rw [h k h1]; exact h3
  · intro j hj hjk; rw [h j hj]; exact h4 j hj hjk

/-- **Every edge keeps an aligned window aligned, except the border edge, which launches.**

Consumer: `carry_cost`. -/
theorem carry_next_align {n : Nat} (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (s : Fin n) (hg : WinGeo ring C s) (Z : TopFixedTraceState n)
    (hreach : topClockReached ring C Z) (hA : AlignShape (topClockSpan n) (cellOf s Z))
    (e : Fin n) :
    (e = winSite s 0 → CarryShape (topClockSpan n) 0 (cellOf s (topFixedTraceNext ring C Z e))) ∧
    (e ≠ winSite s 0 → AlignShape (topClockSpan n) (cellOf s (topFixedTraceNext ring C Z e))) := by
  have hr3 := span_ge_three hg.hn
  by_cases hw : ∃ p, p < topClockSpan n ∧ e = winSite s p
  · obtain ⟨p, hp, rfl⟩ := hw
    have hedge := carry_align_edge (topClockSpan n) (cellOf s Z) hA p hp
    have hiff : (winSite s p = winSite s 0) ↔ p = 0 := by
      constructor
      · intro h3; exact winSite_inj hg.hn s p 0 (by omega) (by omega) h3
      · intro h3; rw [h3]
    refine ⟨fun h3 => ?_, fun h3 => ?_⟩
    · exact carry_congr _ _ _ _ (fun j hj => link_window ring C s Z hg hreach p hp j hj)
        (hedge.1 (hiff.1 h3))
    · exact align_congr _ _ _ (fun j hj => link_window ring C s Z hg hreach p hp j hj)
        (hedge.2 (fun h4 => h3 (hiff.2 h4)))
  · have hne : e ≠ winSite s 0 := fun h3 => hw ⟨0, by omega, h3⟩
    refine ⟨fun h3 => absurd h3 hne, fun _ => ?_⟩
    rcases link_shape ring C s Z hg hreach e hw with hag | hag | ⟨t, hag⟩
    · exact align_congr _ _ _ hag hA
    · exact align_congr _ _ _ hag
        (align_setOne _ _ _ hA (by
          unfold portClean; rw [if_pos (by rw [hA.2.1]), hA.2.1]))
    · exact align_congr _ _ _ hag
        (align_setOne _ _ _ hA (by
          unfold portAccept; rw [if_neg (by rw [hA.2.1]; decide)]))

/-- **Every edge keeps a host window in shape; the host moves exactly on its own edge.**

Consumer: `carry_cost`. -/
theorem carry_next_carry {n : Nat} (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (s : Fin n) (hg : WinGeo ring C s) (Z : TopFixedTraceState n)
    (hreach : topClockReached ring C Z) (k : Nat)
    (hS : CarryShape (topClockSpan n) k (cellOf s Z)) (e : Fin n) :
    (e = winSite s k → k + 1 < topClockSpan n →
      CarryShape (topClockSpan n) (k + 1) (cellOf s (topFixedTraceNext ring C Z e))) ∧
    (e = winSite s k → ¬ k + 1 < topClockSpan n →
      CarryDone (topClockSpan n) (cellOf s (topFixedTraceNext ring C Z e))) ∧
    (e ≠ winSite s k →
      CarryShape (topClockSpan n) k (cellOf s (topFixedTraceNext ring C Z e))) := by
  have hr3 := span_ge_three hg.hn
  have hk := hS.1
  by_cases hw : ∃ p, p < topClockSpan n ∧ e = winSite s p
  · obtain ⟨p, hp, rfl⟩ := hw
    have hedge := carry_edge (topClockSpan n) k (cellOf s Z) hS p hp
    have hiff : (winSite s p = winSite s k) ↔ p = k := by
      constructor
      · intro h3; exact winSite_inj hg.hn s p k (by omega) (by omega) h3
      · intro h3; rw [h3]
    refine ⟨fun h3 h4 => ?_, fun h3 h4 => ?_, fun h3 => ?_⟩
    · exact carry_congr _ _ _ _ (fun j hj => link_window ring C s Z hg hreach p hp j hj)
        (hedge.1 (hiff.1 h3) h4)
    · intro j hj
      rw [link_window ring C s Z hg hreach p hp j hj]
      exact hedge.2.1 (hiff.1 h3) h4 j hj
    · exact carry_congr _ _ _ _ (fun j hj => link_window ring C s Z hg hreach p hp j hj)
        (hedge.2.2 (fun h4 => h3 (hiff.2 h4)))
  · have hne : e ≠ winSite s k := fun h3 => hw ⟨k, hk, h3⟩
    refine ⟨fun h3 => absurd h3 hne, fun h3 => absurd h3 hne, fun _ => ?_⟩
    have h0 : ∀ c : Cell, (0 < k → LeftCell c) → (k = 0 → c = cellOf s Z 0) →
        CarryShape (topClockSpan n) k (setOne (cellOf s Z) 0 c) :=
      fun c hc1 hc2 => carry_setOne _ _ _ c hS ⟨hc1, hc2⟩
    rcases link_shape ring C s Z hg hreach e hw with hag | hag | ⟨t, hag⟩
    · exact carry_congr _ _ _ _ hag hS
    · refine carry_congr _ _ _ _ hag (h0 _ (fun h3 => portClean_left _ (hS.2.1 0 h3)) ?_)
      intro hk0
      subst hk0
      have := hS.2.2.1
      unfold portClean
      rw [this]
      rfl
    · refine carry_congr _ _ _ _ hag (h0 _ (fun h3 => portAccept_left t _ (hS.2.1 0 h3)) ?_)
      intro hk0
      subst hk0
      have := hS.2.2.1
      unfold portAccept
      rw [this]
      rw [if_neg (by decide)]

end MarkedCells
end L3

#print axioms L3.MarkedCells.carry_next_align
#print axioms L3.MarkedCells.carry_next_carry
