import Leader.L3.Top.SettledPotentialPairs

/-!
# Q7 (P.8--P.10): the nominated window edge of a front-free window

In a front-free window with a settled input there is a window edge, or the terminal edge, whose
result has no front and strictly lowers the charge or the measure `Gv` -- except when the
window is waiting for a packet: no live carry, nothing pending, and an empty border register.

Consumer: `Leader/L3/Top/SettledPotentialStep.lean`.
-/

namespace L3
namespace MarkedCells

set_option autoImplicit false
set_option linter.unusedSimpArgs false

/-- The result of the window edge `p`.

Consumer: `nominate_pure`. -/
def EdgeRes (r p : Nat) (cells : Nat → Cell) : Nat → Cell :=
  setTwo cells p (pair (decide (p = 0)) false (cells p) (cells (p + 1))).1
    (pair (decide (p = 0)) false (cells p) (cells (p + 1))).2

/-- The result of the terminal edge.

Consumer: `nominate_pure`. -/
def TermRes (r : Nat) (cells : Nat → Cell) : Nat → Cell :=
  setOne cells (r - 1) (pair false true (cells (r - 1)) { i := .e, c := .off }).1

/-- Editing two registers to non-fronts keeps the window front-free.

Consumer: `nominate_pure`. -/
theorem nx_setTwo (r p : Nat) (cells : Nat → Cell) (h : ∀ k, k < r → (cells k).i ≠ .x)
    (X Y : Cell) (hX : X.i ≠ .x) (hY : Y.i ≠ .x) :
    ∀ k, k < r → (setTwo cells p X Y k).i ≠ .x := by
  intro k hk
  unfold setTwo
  by_cases h1 : k = p
  · simp [h1, hX]
  · by_cases h2 : k = p + 1
    · simp [h2, hY]
    · simp [h1, h2]; exact h k hk

/-- A cell with an empty input and no carry.

Consumer: `nominate_pure`. -/
theorem cell_eq_of (c : Cell) (hi : c.i = .e) (hc : c.c = .off) : c = { i := .e, c := .off } := by
  rcases c with ⟨a, b⟩; simp_all

/-- A live-carry cell is the fresh empty cell.

Consumer: `nominate_pure`. -/
theorem cell_fresh_of (c : Cell) (hi : c.i = .e) (hc : c.c = .fresh) :
    c = { i := .e, c := .fresh } := by
  rcases c with ⟨a, b⟩; simp_all

/-- **The nominated edge of a front-free window.**

Consumer: `Leader/L3/Top/SettledPotentialStep.lean`. -/
theorem nominate_pure (r : Nat) (cells : Nat → Cell) (h : FEnv r cells) (hr : 2 ≤ r) :
    (∃ p, p + 1 < r ∧ (∀ k, k < r → (EdgeRes r p cells k).i ≠ .x) ∧
      (At r (EdgeRes r p cells) < At r cells ∨
        Gv r (EdgeRes r p cells) + 1 ≤ Gv r cells)) ∨
    ((∀ k, k < r → (TermRes r cells k).i ≠ .x) ∧
      Gv r (TermRes r cells) + 1 ≤ Gv r cells) ∨
    (cells 0 = { i := .e, c := .off } ∧ ¬ ConsAt r cells) := by
  by_cases hh : hpOf r cells < r
  · -- a live carry
    have hcj := hp_hit hh
    have hxj : cells (hpOf r cells) = { i := .e, c := .fresh } := by
      rcases h.host hh with h1 | ⟨h1, h2⟩
      · exact absurd h1 hcj
      · exact cell_fresh_of _ h1 h2
    by_cases hj1 : hpOf r cells + 1 < r
    · have hyc : (cells (hpOf r cells + 1)).c = .off := by
        apply Classical.byContradiction
        intro hne
        have := h.uniq hj1 hh hne hcj
        omega
      by_cases hs : (cells (hpOf r cells + 1)).i.isS = true
      · left
        refine ⟨hpOf r cells, hj1, ?_, ?_⟩
        · unfold EdgeRes
          rw [hxj, pair_adv_eq _ _ hs hyc]
          dsimp only
          exact nx_setTwo r _ cells h.nx _ _ (by simp) (by simp)
        · have hg := gv_adv r _ cells h hj1 hxj hs hyc
          unfold EdgeRes
          rw [hxj, pair_adv_eq _ _ hs hyc]
          dsimp only
          rcases hg.2 with hg | ⟨_, hg⟩
          · exact Or.inl hg
          · exact Or.inr (by omega)
      · left
        have hs' : (cells (hpOf r cells + 1)).i.isS = false := by simpa using hs
        have hyx := h.nx _ hj1
        refine ⟨hpOf r cells, hj1, ?_, ?_⟩
        · unfold EdgeRes
          rw [hxj, pair_death_eq _ _ hs' hyc hyx]
          dsimp only
          exact nx_setTwo r _ cells h.nx _ _ (by simp) hyx
        · unfold EdgeRes
          rw [hxj, pair_death_eq _ _ hs' hyc hyx]
          dsimp only
          have := gv_death r (hpOf r cells) cells
            (setTwo cells (hpOf r cells) { i := .e, c := .off } (cells (hpOf r cells + 1)))
            h hh hxj (by simp [setTwo]) (fun k hk => by
              unfold setTwo
              by_cases k2 : k = hpOf r cells + 1
              · simp [hk, k2]
              · simp [hk, k2]) (fun _ => hs')
          exact Or.inr (by omega)
    · -- the carry sits on the last register: the terminal edge
      right; left
      have hjr : hpOf r cells = r - 1 := by omega
      have e1 : TermRes r cells = setOne cells (hpOf r cells) { i := .e, c := .off } := by
        unfold TermRes
        rw [← hjr, hxj]
        rfl
      refine ⟨?_, ?_⟩
      · rw [e1]
        intro k hk
        unfold setOne
        by_cases k1 : k = hpOf r cells
        · simp [k1]
        · simp [k1]; exact h.nx k hk
      · rw [e1]
        have := gv_death r (hpOf r cells) cells (setOne cells (hpOf r cells) { i := .e, c := .off })
          h hh hxj (by simp [setOne]) (fun k hk => by simp [setOne, hk]) (fun hh' => by omega)
        omega
  · -- no live carry
    have hnc : ∀ k, k < r → (cells k).c = .off := by
      intro k hk
      apply Classical.byContradiction
      intro hne
      exact hh ((firstS_lt_iff _ r).2 ⟨k, hk, by simpa using hne⟩)
    have hncons : ¬ ConsAt r cells := fun hc => hh hc.1
    by_cases h0 : (cells 0).i.isS = true
    · left
      have hp1 : 0 + 1 < r := by omega
      have hy0 := hnc 1 (by omega)
      have hyx := h.nx 1 (by omega)
      have hpl := pair_launch_eq (cells 0) (cells 1) h0 (hnc 0 (by omega)) hy0 hyx
      have e1 : EdgeRes r 0 cells = setTwo cells 0 { i := .e, c := .fresh } (cells 1) := by
        unfold EdgeRes
        have : pair (decide (0 = 0)) false (cells 0) (cells (0 + 1)) =
            pair true false (cells 0) (cells 1) := rfl
        rw [this, hpl]
      refine ⟨0, hp1, ?_, ?_⟩
      · rw [e1]
        exact nx_setTwo r _ cells h.nx _ _ (by simp) hyx
      · rw [e1]
        have hg := gv_launch r cells h (by omega) h0 (hnc 0 (by omega))
        rcases hg.2 with hg | ⟨_, hg⟩
        · exact Or.inl hg
        · exact Or.inr (by omega)
    · by_cases hpend : ∃ k, k < r ∧ (cells k).i.isP = true
      · left
        obtain ⟨q, hq, hPq, hlast⟩ := exists_last (fun k => (cells k).i.isP = true) r hpend
        have hqfs := h.pend_lt hq h.fs_lt hPq (Or.inl h.fs_settled)
        have hfl := h.fs_lt
        have hq1 : q + 1 < r := by omega
        have hy := hnc (q + 1) hq1
        have hyx := h.nx (q + 1) hq1
        have hyP : (cells (q + 1)).i.isP = false := by
          have := hlast (q + 1) (by omega) hq1
          simpa using this
        have hxc := hnc q hq
        by_cases hS : (cells (q + 1)).i.isS = true
        · obtain ⟨e2, e1', e3⟩ := pair_settle_eq (decide (q = 0)) (cells q) (cells (q + 1)) hPq hxc hS hy
          refine ⟨q, hq1, ?_, ?_⟩
          · unfold EdgeRes
            rw [e2]
            apply nx_setTwo r _ cells h.nx _ _ ?_ hyx
            intro hx
            rw [hx] at e1'; exact absurd e1' (by simp [Inp.isS])
          · unfold EdgeRes
            rw [e2]
            have := gv_settle r q cells h hq1 _ hPq hxc hS hy e1' e3
            exact Or.inr (by omega)
        · have hS' : (cells (q + 1)).i.isS = false := by simpa using hS
          have hye : (cells (q + 1)).i = .e := by
            rcases hci : (cells (q + 1)).i <;> simp_all [Inp.isS, Inp.isP]
          have hyc := cell_eq_of _ hye hy
          refine ⟨q, hq1, ?_, ?_⟩
          · unfold EdgeRes
            rw [hyc, pair_move_eq _ _ hPq hxc]
            dsimp only
            exact nx_setTwo r _ cells h.nx _ _ (by simp) (h.nx q (by omega))
          · unfold EdgeRes
            rw [hyc, pair_move_eq _ _ hPq hxc]
            dsimp only
            have := (gv_move r q cells h hq1 hPq hxc hyc).2 hncons
            exact Or.inr (by omega)
      · right; right
        refine ⟨?_, hncons⟩
        have hP0 : (cells 0).i.isP = false := by
          apply Classical.byContradiction
          intro hh'
          exact hpend ⟨0, by omega, by simpa using hh'⟩
        have hS0 : (cells 0).i.isS = false := by simpa using h0
        have hx0 := h.nx 0 (by omega)
        have hi : (cells 0).i = .e := by
          rcases hci : (cells 0).i <;> simp_all [Inp.isS, Inp.isP]
        exact cell_eq_of _ hi (hnc 0 (by omega))

end MarkedCells
end L3

#print axioms L3.MarkedCells.nominate_pure
