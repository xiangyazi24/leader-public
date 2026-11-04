import Leader.L3.Top.SettledColour

/-!
# Q7 (P.6): the cover invariant is inductive over every window edge

Consumer: `Leader/L3/Top/SettledCover.lean`.
-/

namespace L3
namespace MarkedCells

open Classical

set_option autoImplicit false

/-- A step creates no inherited carry.

Consumer: `cover_step_machine`. -/
theorem noInh_step (r : Nat) (cells cells' : Nat → Cell) (hni : NoInh r cells)
    (h : Step r cells cells') : NoInh r cells' := by
  cases h with
  | frame => exact hni
  | edge p hp =>
      intro j hj
      have h1 := hni p (by omega)
      have h2 := hni (p + 1) hp
      have := pair_noinh (decide (p = 0)) false (cells p) (cells (p + 1)) h1 h2
      by_cases hjp : j = p
      · subst hjp; simpa [setTwo] using this.1
      · by_cases hjp1 : j = p + 1
        · subst hjp1; simpa [setTwo, hjp] using this.2
        · simpa [setTwo, hjp, hjp1] using hni j hj
  | term =>
      intro j hj
      by_cases hjr : j = r - 1
      · subst hjr
        have := pair_noinh false true (cells (r - 1)) { i := .e, c := .off }
          (hni (r - 1) hj) (by decide)
        simpa [setOne] using this.1
      · simpa [setOne, hjr] using hni j hj
  | clean =>
      intro j hj
      by_cases hj0 : j = 0
      · subst hj0
        have := hni 0 hj
        simp only [setOne, if_true, portClean]
        split <;> simp_all
      · simpa [setOne, hj0] using hni j hj
  | accept t =>
      intro j hj
      by_cases hj0 : j = 0
      · subst hj0
        have := hni 0 hj
        simp only [setOne, if_true, portAccept]
        split <;> simp_all
      · simpa [setOne, hj0] using hni j hj

/-- The cover invariant is preserved by the edge at register `p`.

Consumer: `cover_step_machine`. -/
theorem cover_edge (r p : Nat) (hp : p + 1 < r) (cells : Nat → Cell) (d : Nat → Prop)
    (hinv : Inv r cells) (hni : NoInh r cells) (hcov : Cover r cells d) :
    Cover r
      (setTwo cells p (pair (decide (p = 0)) false (cells p) (cells (p + 1))).1
        (pair (decide (p = 0)) false (cells p) (cells (p + 1))).2)
      (colourGen r cells
        (setTwo cells p (pair (decide (p = 0)) false (cells p) (cells (p + 1))).1
          (pair (decide (p = 0)) false (cells p) (cells (p + 1))).2) d (some p)) := by
  have hxh : (cells p).c ≠ .off → (cells p).i = .e := fun h => host_empty hinv hni (by omega) h
  have hyh : (cells (p + 1)).c ≠ .off → (cells (p + 1)).i = .e :=
    fun h => host_empty hinv hni hp h
  generalize hA : (pair (decide (p = 0)) false (cells p) (cells (p + 1))).1 = a
  generalize hB : (pair (decide (p = 0)) false (cells p) (cells (p + 1))).2 = b
  intro u hu
  obtain ⟨hur, hS', hS, hdm⟩ := hu
  have hbd : decide (p = 0) = true → decide (d p) = false := by
    intro h
    have hp0 : p = 0 := by simpa using h
    subst hp0
    by_cases hd0 : d 0
    · exact absurd (hcov 0 hd0).1 (by omega)
    · simp [hd0]
  -- the left neighbour is unchanged
  have unchanged : ∀ w, w ≠ p → w ≠ p + 1 → w < r →
      ((cells w).i = .x ∨ d w) →
      ((setTwo cells p a b w).i = .x ∨ colourGen r cells (setTwo cells p a b) d (some p) w) := by
    intro w hw1 hw2 hwr hleft
    simp only [setTwo, if_neg hw1, if_neg hw2]
    rcases hleft with h | h
    · exact Or.inl h
    · right
      exact ⟨hwr, by simpa [setTwo, hw1, hw2] using (hcov w h).2.1, (hcov w h).2.1, Or.inl h⟩
  rcases hdm with hdu | hnew
  · obtain ⟨hu0, _, hleft⟩ := hcov u hdu
    refine ⟨hu0, hS', ?_⟩
    by_cases hw1 : u - 1 = p
    · have hu1 : u = p + 1 := by omega
      subst hu1
      rw [hw1] at hleft ⊢
      have key := pair_left_source (decide (p = 0)) (cells p) (cells (p + 1))
        (decide (d p)) hxh hyh
        (by intro h; exact (hcov p (by simpa using h)).2.1)
        (by rcases hleft with h | h
            · exact Or.inl h
            · exact Or.inr (by simpa using h))
        hbd
        (hcov _ hdu).2.1
        (by rw [hB]; simpa [setTwo, hB] using hS')
      rw [hA] at key
      simp only [decide_eq_true_eq] at key
      simp only [setTwo, if_true]
      rcases key with h | ⟨h1, h2, h3⟩
      · exact Or.inl h
      · right
        exact ⟨by omega, by simpa [setTwo] using h1, h2, Or.inl h3⟩
    · by_cases hw2 : u - 1 = p + 1
      · have hu2 : u = p + 2 := by omega
        subst hu2
        rw [hw2] at hleft ⊢
        have key := pair_left_responder (decide (p = 0)) (cells p) (cells (p + 1))
          (decide (d p)) (decide (d (p + 1))) hxh hyh
          (by intro h; exact (hcov p (by simpa using h)).2.1)
          (by intro h; exact (hcov (p + 1) (by simpa using h)).2.1)
          (by rcases hleft with h | h
              · exact Or.inl h
              · exact Or.inr (by simpa using h))
          (by intro h
              have := (hcov (p + 1) (by simpa using h)).2.2
              rcases this with h' | h'
              · exact Or.inl h'
              · exact Or.inr (by simpa using h'))
        rw [hB] at key
        simp only [decide_eq_true_eq] at key
        simp only [setTwo, if_neg (show p + 1 ≠ p by omega), if_true]
        rcases key with h | ⟨h1, h2, h3⟩
        · exact Or.inl h
        · right
          exact ⟨by omega, by simpa [setTwo, show p + 1 ≠ p by omega] using h1, h2,
            Or.inl h3⟩
      · exact unchanged (u - 1) hw1 hw2 (by omega) hleft
  · -- newly doomed
    unfold dooms at hnew
    rcases hnew with ⟨hEA, hnd, hpu, hact⟩ | ⟨hEB, hnd, hpu, hact⟩
    · refine ⟨by omega, hS', ?_⟩
      have hb0 : decide (p = 0) = false := by
        have := hEA.2.2; simp [this]
      have hxa : a.i = .x := by
        rw [← hA]
        exact pair_event_a _ _ _ _ hEA.1 hEA.2.1 hb0
      by_cases hw : u - 1 = p
      · rw [hw]
        left
        simp only [setTwo, if_true]
        exact hxa
      · right
        have hw' : p < u - 1 := by omega
        have hya : b = cells (p + 1) := by
          rw [← hB]
          apply pair_event_a_y _ _ _ hEA.1 hEA.2.1 hb0
          by_cases hc : (cells (p + 1)).c = .off
          · exact hc
          · exfalso
            have := hyh hc
            have hs := (hact.2 (p + 1) (by omega) (by omega)).1
            rw [this] at hs
            exact absurd hs (by simp [Inp.isS])
        refine ⟨by omega, ?_, (hact.2 (u - 1) (by omega) (by omega)).1, Or.inr ?_⟩
        · by_cases hw2 : u - 1 = p + 1
          · rw [hw2]
            simp only [setTwo, if_neg (show p + 1 ≠ p by omega), if_true]
            rw [hya]
            exact (hact.2 (p + 1) (by omega) (by omega)).1
          · have := (hact.2 (u - 1) (by omega) (by omega)).1
            simpa [setTwo, show u - 1 ≠ p by omega, hw2] using this
        · left
          exact ⟨hEA, hnd, hw', ⟨by omega, fun m hm1 hm2 => hact.2 m hm1 (by omega)⟩⟩
    · refine ⟨by omega, hS', ?_⟩
      have hxb : b.i = .x := by
        rw [← hB]
        exact pair_event_b _ _ _ hEB.1 hEB.2.1 hEB.2.2.2.1 hEB.2.2.2.2
      by_cases hw : u - 1 = p + 1
      · rw [hw]
        left
        simp only [setTwo, if_neg (show p + 1 ≠ p by omega), if_true]
        exact hxb
      · right
        have hw' : p + 1 < u - 1 := by omega
        refine ⟨by omega, ?_, (hact.2 (u - 1) (by omega) (by omega)).1, Or.inr ?_⟩
        · have := (hact.2 (u - 1) (by omega) (by omega)).1
          simpa [setTwo, show u - 1 ≠ p by omega, hw] using this
        · right
          exact ⟨hEB, hnd, hw', ⟨by omega, fun m hm1 hm2 => hact.2 m hm1 (by omega)⟩⟩

/-- The cover invariant is preserved by the terminal edge.

Consumer: `cover_edge_step`. -/
theorem cover_term (r : Nat) (hr : 2 ≤ r) (cells : Nat → Cell) (d : Nat → Prop)
    (hcov : Cover r cells d) :
    Cover r
      (setOne cells (r - 1) (pair false true (cells (r - 1)) { i := .e, c := .off }).1)
      (colourGen r cells
        (setOne cells (r - 1) (pair false true (cells (r - 1)) { i := .e, c := .off }).1) d
        (some (r - 1))) := by
  intro u hu
  obtain ⟨hur, hS', hS, hdm⟩ := hu
  have hdu : d u := by
    rcases hdm with h | h
    · exact h
    · unfold dooms at h
      rcases h with ⟨_, _, h2, _⟩ | ⟨_, _, h2, _⟩ <;> omega
  obtain ⟨hu0, _, hleft⟩ := hcov u hdu
  refine ⟨hu0, hS', ?_⟩
  have hw : u - 1 ≠ r - 1 := by omega
  simp only [setOne, if_neg hw]
  rcases hleft with h | h
  · exact Or.inl h
  · right
    exact ⟨by omega, by simpa [setOne, hw] using (hcov _ h).2.1, (hcov _ h).2.1, Or.inl h⟩

/-- The cover invariant is preserved by the edge of register `p`.

Consumer: `cover_step_machine`. -/
theorem cover_edge_step (r p : Nat) (hr : 2 ≤ r) (hp : p < r) (cells : Nat → Cell)
    (d : Nat → Prop) (hinv : Inv r cells) (hni : NoInh r cells) (hcov : Cover r cells d) :
    Cover r (edgeStep r cells p) (colourGen r cells (edgeStep r cells p) d (some p)) := by
  unfold edgeStep
  by_cases h : p + 1 < r
  · rw [if_pos h]
    exact cover_edge r p h cells d hinv hni hcov
  · rw [if_neg h]
    have hpe : p = r - 1 := by omega
    subst hpe
    exact cover_term r hr cells d hcov

/-- The cover invariant is preserved by the frame, port cleanup and port acceptance.

Consumer: `cover_step_machine`. -/
theorem cover_port (r : Nat) (hr : 2 ≤ r) (cells cells' : Nat → Cell) (d : Nat → Prop)
    (hinv : Inv r cells) (hni : NoInh r cells) (hcov : Cover r cells d)
    (h : cells' = cells ∨ cells' = setOne cells 0 (portClean (cells 0)) ∨
      ∃ t, cells' = setOne cells 0 (portAccept t (cells 0))) :
    Cover r cells' (colourGen r cells cells' d none) := by
  intro u hu
  obtain ⟨hur, hS', hS, hdm⟩ := hu
  have hdu : d u := by
    rcases hdm with h | h
    · exact h
    · exact absurd h (by simp [dooms])
  obtain ⟨hu0, _, hleft⟩ := hcov u hdu
  refine ⟨hu0, hS', ?_⟩
  have hsame : ∀ w, w ≠ 0 → cells' w = cells w := by
    intro w hw
    rcases h with h | h | ⟨t, h⟩
    · rw [h]
    · rw [h]; simp [setOne, hw]
    · rw [h]; simp [setOne, hw]
  by_cases hw : u - 1 = 0
  · have hx : (cells 0).i = .x := by
      rcases hleft with h | h
      · rw [hw] at h; exact h
      · rw [hw] at h; exact absurd (hcov 0 h).1 (by omega)
    have hc : (cells 0).c = .off := by
      by_cases hcc : (cells 0).c = .off
      · exact hcc
      · have := host_empty hinv hni (by omega) hcc
        rw [hx] at this; exact absurd this (by decide)
    left
    rw [hw]
    rcases h with h | h | ⟨t, h⟩
    · rw [h]; exact hx
    · rw [h]
      simp only [setOne, if_true, portClean, hc, if_true]
      exact hx
    · rw [h]
      simp only [setOne, if_true, portAccept]
      have : ¬ (cells 0 = { i := .e, c := .off }) := by
        intro h0; rw [h0] at hx; exact absurd hx (by decide)
      rw [if_neg this]
      exact hx
  · rcases hleft with h | h
    · left
      rw [hsame _ hw]; exact h
    · right
      refine ⟨by omega, ?_, (hcov _ h).2.1, Or.inl h⟩
      rw [hsame _ hw]; exact (hcov _ h).2.1

end MarkedCells
end L3

#print axioms L3.MarkedCells.cover_edge_step
#print axioms L3.MarkedCells.cover_port
#print axioms L3.MarkedCells.noInh_step
