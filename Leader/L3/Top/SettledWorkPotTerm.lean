import Leader.L3.Top.SettledWorkPotEdge

/-!
# Q7 (P.7): the terminal edge and the port: the charge falls or the front debt does not rise

Consumer: `Leader/L3/Top/SettledWorkPotTrace.lean`.
-/

namespace L3
namespace MarkedCells

open Classical

set_option autoImplicit false
set_option linter.unusedSimpArgs false

/-- Front count after editing one register.

Consumer: `term_pot`. -/
theorem Xn_one (r : Nat) (cells : Nat → Cell) (p : Nat) (hp : p + 1 ≤ r) (a : Cell) :
    Xn r (setOne cells p a) + fr (cells p) = Xn r cells + fr a := by
  have := cnt_edit_one (fun k => decide ((cells k).i = .x))
    (fun k => decide ((setOne cells p a k).i = .x)) p
    (by intro j h1; simp [setOne, h1]) r hp
  unfold Xn
  simp only [setOne, if_true, fr] at this ⊢
  simp at this ⊢
  omega

/-- **The terminal edge: the charge falls, or the front debt does not rise.**

Consumer: `Leader/L3/Top/SettledWorkPotTrace.lean`. -/
theorem term_pot (r : Nat) (cells : Nat → Cell) (d : Nat → Prop) (p : Nat)
    (hp : p + 1 = r) (hp0 : p ≠ 0) (hinv : Inv r cells) (hni : NoInh r cells)
    (hbar : Barrier r cells) (hex : ∃ j, j < r ∧ (cells j).i.isS = true) :
    charge r (act r (setOne cells p (pair false true (cells p) { i := .e, c := .off }).1)
      (colourGen r cells (setOne cells p
        (pair false true (cells p) { i := .e, c := .off }).1) d (some p))) <
    charge r (act r cells d) ∨
    Mn r (setOne cells p (pair false true (cells p) { i := .e, c := .off }).1)
      (colourGen r cells (setOne cells p
        (pair false true (cells p) { i := .e, c := .off }).1) d (some p)) ≤
    Mn r cells d := by
  have hx : (cells p).c ≠ .off → (cells p).i = .e := fun h =>
    host_empty hinv hni (by omega) h
  have pat := pair_pat false true (cells p) { i := .e, c := .off } hx
    (by intro h; exact absurd rfl h) (by simp)
  have hf := pair_front false true (cells p) { i := .e, c := .off } hx
    (by intro h; exact absurd rfl h) (by simp)
  generalize hpr : pair false true (cells p) { i := .e, c := .off } = pr at pat hf ⊢
  have hX := Xn_one r cells p (by omega) pr.1
  have hfy : fr ({ i := .e, c := .off } : Cell) = 0 := by simp [fr]
  simp [hfy] at hf
  have hXle1 : Xn r (setOne cells p pr.1) ≤ Xn r cells + 1 := by
    by_cases hE : (cells p).i = .st ∧ (cells p).c = .off
    · rw [if_pos hE] at hf; omega
    · rw [if_neg hE] at hf; omega
  have hS' : ∀ k, (setOne cells p pr.1 k).i.isS =
      if k = p then pr.1.i.isS else (cells k).i.isS := by
    intro k
    unfold setOne
    by_cases h1 : k = p
    · simp [h1]
    · simp [h1]
  have hSp : (setOne cells p pr.1 p).i.isS = pr.1.i.isS := by rw [hS']; simp
  have hSo : ∀ k, k ≠ p → (setOne cells p pr.1 k).i.isS = (cells k).i.isS := by
    intro k h1; rw [hS']; simp [h1]
  have hnB : ¬ EventB r cells p := by
    rintro ⟨_, _, h3, _⟩; omega
  rcases pat with ⟨e1, e2, hnA, _⟩ | ⟨ht, _⟩ | ⟨ht, _⟩ | ⟨hxst, hxc, hb, hx'S, _⟩ |
    ⟨hb, _⟩ | ⟨hxP, hx'S, _, hcond⟩
  · right
    have hnE : ¬ ((cells p).i = .st ∧ (cells p).c = .off) := by
      rintro ⟨h1, h2⟩; exact hnA ⟨h1, h2, rfl⟩
    refine mn_le_of r cells _ d (some p) ?_ ?_
    · apply dooms_none r cells d p _ hnB
      rintro ⟨h1, h2, _⟩
      exact hnA ⟨h2, h1, rfl⟩
    · rw [if_neg hnE] at hf; omega
  · exact absurd ht (by simp)
  · exact absurd ht (by simp)
  · have hEA : EventA cells p := ⟨hxc, hxst, hp0⟩
    have hxS : (cells p).i.isS = true := by rw [hxst]; rfl
    have hS2 : ∀ k, (setOne cells p pr.1 k).i.isS = true → (cells k).i.isS = true := by
      intro k hk
      by_cases h1 : k = p
      · subst h1; rw [hSp, hx'S] at hk; exact absurd hk (by simp)
      · rw [hSo k h1] at hk; exact hk
    have hS1' : ∀ k, k ≠ p → act r cells d k = true →
        (setOne cells p pr.1 k).i.isS = true := by
      intro k hk hact
      obtain ⟨_, hk2, _⟩ := (act_iff r cells d k).1 hact
      rw [hSo k hk]; exact hk2
    by_cases ha : act r cells d p = true
    · left
      obtain ⟨_, _, hpd⟩ := (act_iff r cells d p).1 ha
      refine act_cut_case_lt r cells _ d (some p) p ha hS1' hS2 ?_ ?_ ?_
      · rw [hSp]; exact hx'S
      · intro m hm hA
        unfold dooms
        exact Or.inl ⟨hEA, hpd, hm, hA⟩
      · intro m h
        unfold dooms at h
        rcases h with ⟨_, _, h3, h4⟩ | ⟨hB, _⟩
        · exact ⟨h3, h4⟩
        · exact absurd hB hnB
    · right
      have hd : d p := by
        by_cases hd : d p
        · exact hd
        · exact absurd ((act_iff r cells d p).2 ⟨by omega, hxS, hd⟩) ha
      have hnd : ∀ m, ¬ dooms r cells d (some p) m := by
        intro m h
        unfold dooms at h
        rcases h with ⟨_, h2, _⟩ | ⟨hB, _⟩
        · exact h2 hd
        · exact hnB hB
      refine mn_le_of_front r cells _ d (some p) hnd p (by omega) hd ?_ hXle1
      rintro ⟨_, h2, _⟩
      rw [hSp, hx'S] at h2; exact absurd h2 (by simp)
  · exact absurd hb (by simp)
  · exfalso
    obtain ⟨j, hj, hjS⟩ := hex
    have hob : obC (cells j) = true := by simp [obC, hjS]
    have := hbar p j (by omega) hj hxP hob
    omega

/-- A step that creates no front and dooms nothing does not raise the debt.

Consumer: `Leader/L3/Top/SettledWorkPotTrace.lean`. -/
theorem port_pot (r : Nat) (cells cells' : Nat → Cell) (d : Nat → Prop)
    (hX : ∀ k, (cells' k).i = .x → (cells k).i = .x) :
    Mn r cells' (colourGen r cells cells' d none) ≤ Mn r cells d :=
  mn_le_of r cells cells' d none (fun m h => h)
    (cnt_mono _ _ (fun k hk => by simpa using hX k (by simpa using hk)) r)

end MarkedCells
end L3

#print axioms L3.MarkedCells.term_pot
