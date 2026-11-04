import Leader.L3.Top.PinnedStep

/-!
# Q7 (P.8--P.10): the measure along a carry advance and a carry launch

Consumer: `Leader/L3/Top/SettledPotentialStep.lean`.
-/

namespace L3
namespace MarkedCells

set_option autoImplicit false
set_option linter.unusedSimpArgs false

/-- **A live carry advances through a settled site.**  While the carry keeps consuming, the
measure falls by one; when the consumed site was the last of its run, the charge falls.

Consumer: `Leader/L3/Top/SettledPotentialStep.lean`. -/
theorem gv_adv (r p : Nat) (cells : Nat → Cell) (h : FEnv r cells) (hp : p + 1 < r)
    (hx : cells p = { i := .e, c := .fresh }) (hy : (cells (p + 1)).i.isS = true)
    (hyc : (cells (p + 1)).c = .off) :
    ConsAt r cells ∧
    (At r (setTwo cells p { i := .e, c := .off } { i := .e, c := .fresh }) < At r cells ∨
      (ConsAt r (setTwo cells p { i := .e, c := .off } { i := .e, c := .fresh }) ∧
        Gv r (setTwo cells p { i := .e, c := .off } { i := .e, c := .fresh }) + 1 =
          Gv r cells)) := by
  generalize hc' : setTwo cells p { i := .e, c := .off } { i := .e, c := .fresh } = cells'
  have hout : ∀ k, k ≠ p → k ≠ p + 1 → cells' k = cells k := by
    intro k h1 h2; rw [← hc']; simp [setTwo, h1, h2]
  have h0 : cells' p = { i := .e, c := .off } := by rw [← hc']; simp [setTwo]
  have h1 : cells' (p + 1) = { i := .e, c := .fresh } := by rw [← hc']; simp [setTwo]
  have hcp : (cells p).c ≠ .off := by rw [hx]; simp
  have hH : hpOf r cells = p := hp_eq h (by omega) hcp
  have hcons : ConsAt r cells := by
    unfold ConsAt
    rw [hH]
    exact ⟨by omega, hp, hy⟩
  refine ⟨hcons, ?_⟩
  have hH' : hpOf r cells' = p + 1 := by
    unfold hpOf
    apply firstS_eq _ r (p + 1) hp (by rw [h1]; simp)
    intro k hk
    by_cases k1 : k = p
    · subst k1; rw [h0]; simp
    · rw [hout k k1 (by omega)]
      have := hp_before (r := r) (cells := cells) (k := k) (by rw [hH]; omega)
      simp [this]
  by_cases hc2 : p + 2 < r ∧ (cells (p + 2)).i.isS = true
  · right
    have hcons' : ConsAt r cells' := by
      unfold ConsAt
      rw [hH']
      refine ⟨hp, hc2.1, ?_⟩
      rw [hout (p + 1 + 1) (by omega) (by omega)]
      exact hc2.2
    refine ⟨hcons', ?_⟩
    rw [Gv_cons r cells' hcons', Gv_cons r cells hcons, hH', hH]
    omega
  · left
    apply at_lt_single r (p + 1) cells cells' hp hy (by rw [h1]; rfl)
    · intro m hm hmr
      by_cases k1 : m = p
      · subst k1; rw [h0, hx]
      · rw [hout m k1 hm]
    · intro hq
      have : ¬ (cells (p + 2)).i.isS = true := fun hh => hc2 ⟨hq, hh⟩
      simpa using this

/-- **A carry is launched from a settled border site.**  If the next site is settled the
launched carry consumes and the measure falls by one; otherwise the charge falls.

Consumer: `Leader/L3/Top/SettledPotentialStep.lean`. -/
theorem gv_launch (r : Nat) (cells : Nat → Cell) (h : FEnv r cells) (hr : 1 < r)
    (hx : (cells 0).i.isS = true) (hxc : (cells 0).c = .off) :
    ¬ ConsAt r cells ∧
    (At r (setTwo cells 0 { i := .e, c := .fresh } (cells 1)) < At r cells ∨
      (ConsAt r (setTwo cells 0 { i := .e, c := .fresh } (cells 1)) ∧
        Gv r (setTwo cells 0 { i := .e, c := .fresh } (cells 1)) + 1 = Gv r cells)) := by
  generalize hc' : setTwo cells 0 { i := .e, c := .fresh } (cells 1) = cells'
  have hout : ∀ k, k ≠ 0 → cells' k = cells k := by
    intro k h1
    rw [← hc']
    by_cases h2 : k = 0 + 1
    · subst h2; simp [setTwo]
    · simp [setTwo, h1, h2]
  have h0 : cells' 0 = { i := .e, c := .fresh } := by rw [← hc']; simp [setTwo]
  have hnc : ∀ k, k < r → (cells k).c = .off := by
    intro k hk
    apply Classical.byContradiction
    intro hne
    by_cases k0 : k = 0
    · subst k0; exact hne hxc
    · have h3 := h.left hk hne (i := 0) (by omega)
      rcases h3 with h3 | h3
      · rw [h3] at hx; exact absurd hx (by simp [Inp.isS])
      · rw [isS_not_isP hx] at h3; exact absurd h3 (by simp)
  have hHp : ¬ hpOf r cells < r := by rw [hp_none hnc]; omega
  have hncons : ¬ ConsAt r cells := fun hh => hHp hh.1
  refine ⟨hncons, ?_⟩
  have hfs : fsOf r cells = 0 := by
    unfold fsOf
    exact firstS_eq _ r 0 (by omega) hx (fun k hk => by omega)
  have hH' : hpOf r cells' = 0 := by
    unfold hpOf
    apply firstS_eq _ r 0 (by omega) (by rw [h0]; simp)
    intro k hk; omega
  by_cases hc2 : (cells' 1).i.isS = true
  · right
    have hcons' : ConsAt r cells' := by
      unfold ConsAt
      rw [hH']
      exact ⟨by omega, hr, hc2⟩
    refine ⟨hcons', ?_⟩
    rw [Gv_cons r cells' hcons', Gv_free r cells hHp, hH']
    unfold FT
    rw [hfs, if_pos (by omega)]
    simp [wsum]
  · left
    apply at_lt_single r 0 cells cells' (by omega) hx (by rw [h0]; rfl)
    · intro m hm hmr
      rw [hout m hm]
    · intro hq
      have h1 : cells' 1 = cells 1 := hout 1 (by omega)
      rw [← h1]
      simpa using hc2

end MarkedCells
end L3

#print axioms L3.MarkedCells.gv_adv
#print axioms L3.MarkedCells.gv_launch
