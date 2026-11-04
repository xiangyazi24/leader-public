import Leader.L3.Top.SettledPotentialAdv

/-!
# Q7 (P.8--P.10): the measure along one window edge of a front-free window

For every window edge `p` whose result has no front, either the charge of the settled sites
falls, or the measure `Gv` does not rise and a consuming carry keeps consuming.

Consumer: `Leader/L3/Top/SettledPotentialStep.lean`.
-/

namespace L3
namespace MarkedCells

set_option autoImplicit false
set_option linter.unusedSimpArgs false

/-- The measure only reads the carry site and the next site.

Consumer: `edge_gv`. -/
theorem consAt_same (r : Nat) (cells cells' : Nat → Cell)
    (hH : hpOf r cells' = hpOf r cells)
    (hn : hpOf r cells < r → hpOf r cells + 1 < r →
      (cells' (hpOf r cells + 1)).i.isS = (cells (hpOf r cells + 1)).i.isS) :
    ConsAt r cells → ConsAt r cells' := by
  intro hc
  unfold ConsAt at hc ⊢
  rw [hH]
  exact ⟨hc.1, hc.2.1, by rw [hn hc.1 hc.2.1]; exact hc.2.2⟩

/-- A settled site right of a pending packet excludes every live carry.

Consumer: `edge_gv`. -/
theorem nohost_of_settle (r p : Nat) (cells : Nat → Cell) (h : FEnv r cells) (hp : p + 1 < r)
    (hx : (cells p).i.isP = true) (hy : (cells (p + 1)).i.isS = true)
    (hyc : (cells (p + 1)).c = .off) : ∀ k, k < r → (cells k).c = .off := by
  intro k hk
  apply Classical.byContradiction
  intro hne
  have h1' := h.pend_lt (by omega) hk hx (Or.inr hne)
  have h2' : k ≠ p + 1 := fun hh => by rw [hh] at hne; exact hne hyc
  have h3 := h.left hk hne (i := p + 1) (by omega)
  rcases h3 with h3 | h3
  · rw [h3] at hy; exact absurd hy (by simp [Inp.isS])
  · rw [isS_not_isP hy] at h3; exact absurd h3 (by simp)

/-- The terminal edge of a front-free window: nothing, or a live carry retires, or a pending
packet is at the terminal.

Consumer: `term_gv`. -/
theorem term_shape (x : Cell) (hx : x.c = .off ∨ (x.i = .e ∧ x.c = .fresh)) (hxi : x.i ≠ .x)
    (hf : (pair false true x { i := .e, c := .off }).1.i ≠ .x) :
    (pair false true x { i := .e, c := .off }).1 = x ∨
    (x = { i := .e, c := .fresh } ∧
      (pair false true x { i := .e, c := .off }).1 = { i := .e, c := .off }) ∨
    x.i.isP = true := by
  rcases x with ⟨xi, xc⟩
  cases xi <;> cases xc <;>
    simp (config := { decide := true }) [pair, inSlots, carries, Inp.isP, Inp.isS] at hx hxi hf ⊢

/-- **The terminal edge.**

Consumer: `Leader/L3/Top/SettledPotentialStep.lean`. -/
theorem term_gv (r : Nat) (cells : Nat → Cell) (h : FEnv r cells) (hr : 1 ≤ r)
    (hnx' : ∀ k, k < r →
      (setOne cells (r - 1) (pair false true (cells (r - 1)) { i := .e, c := .off }).1 k).i ≠ .x) :
    (setOne cells (r - 1) (pair false true (cells (r - 1)) { i := .e, c := .off }).1 = cells) ∨
    (Gv r (setOne cells (r - 1) (pair false true (cells (r - 1)) { i := .e, c := .off }).1) + 1
        = Gv r cells ∧ ¬ ConsAt r cells) := by
  have hxh := h.host (k := r - 1) (by omega)
  have hxi := h.nx (r - 1) (by omega)
  have hf : (pair false true (cells (r - 1)) { i := .e, c := .off }).1.i ≠ .x := by
    have := hnx' (r - 1) (by omega)
    simpa [setOne] using this
  rcases term_shape _ hxh hxi hf with h1 | ⟨h1, h2⟩ | h3
  · left
    funext k
    unfold setOne
    by_cases hk : k = r - 1
    · subst hk; simp [h1]
    · simp [hk]
  · right
    have hlt : r - 1 < r := by omega
    have hx' : setOne cells (r - 1) (pair false true (cells (r - 1)) { i := .e, c := .off }).1
        (r - 1) = { i := .e, c := .off } := by
      simp [setOne, h2]
    have hGv := gv_death r (r - 1) cells
      (setOne cells (r - 1) (pair false true (cells (r - 1)) { i := .e, c := .off }).1)
      h hlt h1 hx' (fun k hk => by simp [setOne, hk]) (fun hh => by omega)
    refine ⟨hGv, ?_⟩
    intro hc
    have hcp : (cells (r - 1)).c ≠ .off := by rw [h1]; simp
    have hH := hp_eq h hlt hcp
    have := hc.2.1
    rw [hH] at this
    omega
  · exfalso
    have hp := h.pend_lt (p := r - 1) (j := fsOf r cells) (by omega) h.fs_lt h3 (Or.inl h.fs_settled)
    have := h.fs_lt
    omega

/-- **One window edge of a front-free window.**  Either the charge of the settled sites falls,
or the measure does not rise and a consuming carry keeps consuming.

Consumer: `Leader/L3/Top/SettledPotentialStep.lean`. -/
theorem edge_gv (r p : Nat) (cells : Nat → Cell) (h : FEnv r cells) (hp : p + 1 < r)
    (hnx' : ∀ k, k < r →
      (setTwo cells p (pair (decide (p = 0)) false (cells p) (cells (p + 1))).1
        (pair (decide (p = 0)) false (cells p) (cells (p + 1))).2 k).i ≠ .x) :
    At r (setTwo cells p (pair (decide (p = 0)) false (cells p) (cells (p + 1))).1
        (pair (decide (p = 0)) false (cells p) (cells (p + 1))).2) < At r cells ∨
    (Gv r (setTwo cells p (pair (decide (p = 0)) false (cells p) (cells (p + 1))).1
        (pair (decide (p = 0)) false (cells p) (cells (p + 1))).2) ≤ Gv r cells ∧
      (ConsAt r cells → ConsAt r (setTwo cells p
        (pair (decide (p = 0)) false (cells p) (cells (p + 1))).1
        (pair (decide (p = 0)) false (cells p) (cells (p + 1))).2))) := by
  have hxh := h.host (k := p) (by omega)
  have hyh := h.host (k := p + 1) hp
  have hxi := h.nx p (by omega)
  have hyi := h.nx (p + 1) hp
  have hf1 : (pair (decide (p = 0)) false (cells p) (cells (p + 1))).1.i ≠ .x := by
    have := hnx' p (by omega); simpa [setTwo] using this
  have hf2 : (pair (decide (p = 0)) false (cells p) (cells (p + 1))).2.i ≠ .x := by
    have := hnx' (p + 1) hp; simpa [setTwo] using this
  have hsh := pair_shape (decide (p = 0)) (cells p) (cells (p + 1)) hxh hyh hxi hyi hf1 hf2
  generalize hpr : pair (decide (p = 0)) false (cells p) (cells (p + 1)) = pr at hsh ⊢
  rcases hsh with ⟨h1, h2⟩ | ⟨hP, hc, hy, h1, h2⟩ | ⟨hP, hc, hS, hsc, h1, h1c, h2⟩ |
    ⟨hx, hS, h1, h2⟩ | ⟨hx, hS, hsc, h1, h2⟩ | ⟨hb, hS, hsc, h1, h2⟩
  · -- frame
    right
    have : setTwo cells p pr.1 pr.2 = cells := by
      funext k
      unfold setTwo
      by_cases k1 : k = p
      · subst k1; simp [h1]
      · by_cases k2 : k = p + 1
        · subst k2; simp [h2]
        · simp [k1, k2]
    rw [this]
    exact ⟨Nat.le_refl _, fun hh => hh⟩
  · -- move
    right
    have hmv := gv_move r p cells h hp hP hc hy
    have e1 : setTwo cells p pr.1 pr.2 =
        setTwo cells p { i := .e, c := .off } { i := (cells p).i, c := .off } := by rw [h1, h2]
    rw [e1]
    have hy' : cells (p + 1) = { i := .e, c := .off } := hy
    have hob : ∀ j, j < r → ((cells j).i.isS = true ∨ (cells j).c ≠ .off) → p < j :=
      fun j hj hh => h.pend_lt (by omega) hj hP hh
    refine ⟨?_, ?_⟩
    · by_cases hcc : ConsAt r cells
      · rw [hmv.1 hcc]; exact Nat.le_refl _
      · have := hmv.2 hcc; omega
    · intro hcc
      apply consAt_same r cells _ _ _ hcc
      · unfold hpOf
        apply firstS_congr
        intro k hk
        by_cases k1 : k = p
        · subst k1; simp [setTwo, hc]
        · by_cases k2 : k = p + 1
          · subst k2; simp [setTwo, hy']
          · simp [setTwo, k1, k2]
      · intro hlt _
        have h1' := hp_hit hlt
        have h2' := hob _ hlt (Or.inr h1')
        have h3' : hpOf r cells ≠ p + 1 := fun hh => by
          rw [hh, hy'] at h1'; exact h1' rfl
        simp [setTwo]
        rw [if_neg (by omega), if_neg (by omega)]
  · -- settle
    right
    have hnc := nohost_of_settle r p cells h hp hP hS hsc
    have hHp : ¬ hpOf r cells < r := by rw [hp_none hnc]; omega
    have e1 : setTwo cells p pr.1 pr.2 = setTwo cells p pr.1 (cells (p + 1)) := by rw [h2]
    rw [e1]
    have := gv_settle r p cells h hp pr.1 hP hc hS hsc h1 h1c
    exact ⟨by omega, fun hh => absurd hh.1 hHp⟩
  · -- retirement
    right
    have hlt : p < r := by omega
    have e1 : setTwo cells p pr.1 pr.2 = setTwo cells p { i := .e, c := .off } (cells (p + 1)) := by
      rw [h1, h2]
    rw [e1]
    have := gv_death r p cells (setTwo cells p { i := .e, c := .off } (cells (p + 1))) h hlt hx
      (by simp [setTwo]) (fun k hk => by simp [setTwo, hk]
        <;> (by_cases k2 : k = p + 1 <;> simp [k2]))
      (fun _ => hS)
    refine ⟨by omega, ?_⟩
    intro hc
    exfalso
    have hcp : (cells p).c ≠ .off := by rw [hx]; simp
    have hH := hp_eq h hlt hcp
    obtain ⟨_, _, h3⟩ := hc
    rw [hH] at h3
    rw [hS] at h3
    exact absurd h3 (by simp)
  · -- advance
    have hyc : (cells (p + 1)).c = .off := hsc
    have hS' : (cells (p + 1)).i.isS = true := hS
    have e1 : setTwo cells p pr.1 pr.2 =
        setTwo cells p { i := .e, c := .off } { i := .e, c := .fresh } := by rw [h1, h2]
    rw [e1]
    obtain ⟨_, hh⟩ := gv_adv r p cells h hp hx hS' hyc
    rcases hh with hh | ⟨hc, he⟩
    · exact Or.inl hh
    · exact Or.inr ⟨by omega, fun _ => hc⟩
  · -- launch
    have hp0 : p = 0 := by simpa using hb
    subst hp0
    have hx0 : (cells 0).c = .off := hsc
    have e1 : setTwo cells 0 pr.1 pr.2 = setTwo cells 0 { i := .e, c := .fresh } (cells 1) := by
      rw [h1, h2]
    rw [e1]
    obtain ⟨hnc, hh⟩ := gv_launch r cells h (by omega) hS hx0
    rcases hh with hh | ⟨hc, he⟩
    · exact Or.inl hh
    · exact Or.inr ⟨by omega, fun hh => absurd hh hnc⟩

end MarkedCells
end L3

#print axioms L3.MarkedCells.edge_gv
#print axioms L3.MarkedCells.term_gv
