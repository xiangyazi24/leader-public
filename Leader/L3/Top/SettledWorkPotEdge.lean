import Leader.L3.Top.SettledWorkPot

/-!
# Q7 (P.7): one window edge: the charge falls or the front debt does not rise

Consumer: `Leader/L3/Top/SettledWorkPotTrace.lean`.
-/

namespace L3
namespace MarkedCells

open Classical

set_option autoImplicit false
set_option linter.unusedSimpArgs false

/-- Number of doomed registers.

Consumer: `edge_pot`. -/
noncomputable def Dn (r : Nat) (d : Nat → Prop) : Nat := cnt (fun k => decide (d k)) r

/-- Number of erasure fronts.

Consumer: `edge_pot`. -/
def Xn (r : Nat) (cells : Nat → Cell) : Nat := cnt (fun k => decide ((cells k).i = .x)) r

/-- The front debt `M = 2 D + X`.

Consumer: `edge_pot`. -/
noncomputable def Mn (r : Nat) (cells : Nat → Cell) (d : Nat → Prop) : Nat :=
  2 * Dn r d + Xn r cells

/-- Fewer doomed registers when the doomed set shrinks.

Consumer: `edge_pot`. -/
theorem Dn_le (r : Nat) (d d' : Nat → Prop) (h : ∀ k, d' k → d k) : Dn r d' ≤ Dn r d :=
  cnt_mono _ _ (fun k hk => by simpa using h k (by simpa using hk)) r

/-- Strictly fewer doomed registers when one is removed.

Consumer: `edge_pot`. -/
theorem Dn_lt (r : Nat) (d d' : Nat → Prop) (h : ∀ k, d' k → d k) (q : Nat) (hq : q < r)
    (hd : d q) (hd' : ¬ d' q) : Dn r d' + 1 ≤ Dn r d :=
  cnt_lt _ _ (fun k hk => by simpa using h k (by simpa using hk)) q (by simpa using hd)
    (by simpa using hd') r hq

/-- Nothing doomed: the new doomed set is inside the old one.

Consumer: `edge_pot`. -/
theorem colourGen_sub (r : Nat) (cells cells' : Nat → Cell) (d : Nat → Prop)
    (po : Option Nat) (hnd : ∀ m, ¬ dooms r cells d po m) :
    ∀ k, colourGen r cells cells' d po k → d k := by
  rintro k ⟨_, _, _, h | h⟩
  · exact h
  · exact absurd h (hnd k)

/-- Nothing is doomed and the fronts do not increase: the debt does not rise.

Consumer: `edge_pot`. -/
theorem mn_le_of (r : Nat) (cells cells' : Nat → Cell) (d : Nat → Prop) (po : Option Nat)
    (hnd : ∀ m, ¬ dooms r cells d po m) (hX : Xn r cells' ≤ Xn r cells) :
    Mn r cells' (colourGen r cells cells' d po) ≤ Mn r cells d := by
  have := Dn_le r d _ (colourGen_sub r cells cells' d po hnd)
  unfold Mn; omega

/-- Nothing is newly doomed, one doomed register loses its colour, and at most one front is
created: the debt does not rise.

Consumer: `edge_pot`. -/
theorem mn_le_of_front (r : Nat) (cells cells' : Nat → Cell) (d : Nat → Prop)
    (po : Option Nat) (hnd : ∀ m, ¬ dooms r cells d po m) (q : Nat) (hq : q < r) (hdq : d q)
    (hdq' : ¬ colourGen r cells cells' d po q) (hX : Xn r cells' ≤ Xn r cells + 1) :
    Mn r cells' (colourGen r cells cells' d po) ≤ Mn r cells d := by
  have := Dn_lt r d _ (colourGen_sub r cells cells' d po hnd) q hq hdq hdq'
  unfold Mn; omega

/-- Front count after editing two adjacent registers.

Consumer: `edge_pot`. -/
theorem Xn_two (r : Nat) (cells : Nat → Cell) (p : Nat) (hp : p + 1 < r) (a b : Cell) :
    Xn r (setTwo cells p a b) + fr (cells p) + fr (cells (p + 1)) =
      Xn r cells + fr a + fr b := by
  have := cnt_edit (fun k => decide ((cells k).i = .x))
    (fun k => decide ((setTwo cells p a b k).i = .x)) p
    (by intro j h1 h2; simp [setTwo, h1, h2]) r (by omega)
  unfold Xn
  simp only [setTwo, if_true, fr] at this ⊢
  have e1 : (p + 1 = p) = False := by simp
  simp [e1] at this ⊢
  omega

/-- **One window edge: the charge falls, or the front debt does not rise.**

Consumer: `Leader/L3/Top/SettledWorkPotTrace.lean`. -/
theorem edge_pot (r : Nat) (cells : Nat → Cell) (d : Nat → Prop) (p : Nat)
    (hp : p + 1 < r) (hinv : Inv r cells) (hni : NoInh r cells) :
    charge r (act r (setTwo cells p (pair (decide (p = 0)) false (cells p) (cells (p + 1))).1
        (pair (decide (p = 0)) false (cells p) (cells (p + 1))).2)
      (colourGen r cells (setTwo cells p
        (pair (decide (p = 0)) false (cells p) (cells (p + 1))).1
        (pair (decide (p = 0)) false (cells p) (cells (p + 1))).2) d (some p))) <
    charge r (act r cells d) ∨
    Mn r (setTwo cells p (pair (decide (p = 0)) false (cells p) (cells (p + 1))).1
        (pair (decide (p = 0)) false (cells p) (cells (p + 1))).2)
      (colourGen r cells (setTwo cells p
        (pair (decide (p = 0)) false (cells p) (cells (p + 1))).1
        (pair (decide (p = 0)) false (cells p) (cells (p + 1))).2) d (some p)) ≤
    Mn r cells d := by
  have hx : (cells p).c ≠ .off → (cells p).i = .e := fun h =>
    host_empty hinv hni (by omega) h
  have hy : (cells (p + 1)).c ≠ .off → (cells (p + 1)).i = .e := fun h =>
    host_empty hinv hni hp h
  have pat := pair_pat (decide (p = 0)) false (cells p) (cells (p + 1)) hx hy (by simp)
  have hf := pair_front (decide (p = 0)) false (cells p) (cells (p + 1)) hx hy (by simp)
  simp only [if_true] at hf
  generalize hpr : pair (decide (p = 0)) false (cells p) (cells (p + 1)) = pr at pat hf ⊢
  have hX := Xn_two r cells p hp pr.1 pr.2
  have hXle1 : Xn r (setTwo cells p pr.1 pr.2) ≤ Xn r cells + 1 := by
    by_cases hE : (cells p).i = .st ∧ (cells p).c = .off ∧ decide (p = 0) = false
    · rw [if_pos hE] at hf; omega
    · rw [if_neg hE] at hf; omega
  have hXle0 : ¬ ((cells p).i = .st ∧ (cells p).c = .off ∧ decide (p = 0) = false) →
      Xn r (setTwo cells p pr.1 pr.2) ≤ Xn r cells := by
    intro hE
    rw [if_neg hE] at hf; omega
  have hS' : ∀ k, (setTwo cells p pr.1 pr.2 k).i.isS =
      if k = p then pr.1.i.isS else if k = p + 1 then pr.2.i.isS else (cells k).i.isS := by
    intro k
    unfold setTwo
    by_cases h1 : k = p
    · simp [h1]
    · by_cases h2 : k = p + 1
      · simp [h1, h2]
      · simp [h1, h2]
  have hSp : (setTwo cells p pr.1 pr.2 p).i.isS = pr.1.i.isS := by rw [hS']; simp
  have hSq : (setTwo cells p pr.1 pr.2 (p + 1)).i.isS = pr.2.i.isS := by rw [hS']; simp
  have hSo : ∀ k, k ≠ p → k ≠ p + 1 →
      (setTwo cells p pr.1 pr.2 k).i.isS = (cells k).i.isS := by
    intro k h1 h2; rw [hS']; simp [h1, h2]
  rcases pat with ⟨e1, e2, hnA, hnB⟩ | ⟨ht, hxS, hx'S, hyS, hy'S, hyc, hxc⟩ |
    ⟨ht, hxS, hx'S, hyS, hy'S, hyc, hxc, hxx⟩ | ⟨hxst, hxc, hb, hx'S, hy'S⟩ |
    ⟨hb, ht, hxc, hxS, hx'S, hy'S⟩ | ⟨hxP, hx'S, hy'S, hcond⟩
  · right
    refine mn_le_of r cells _ d (some p) ?_ (hXle0 hnA)
    apply dooms_none
    · rintro ⟨h1, h2, h3⟩
      exact hnA ⟨h2, h1, by simpa using h3⟩
    · rintro ⟨h1, h2, h3, h4, h5⟩
      exact hnB ⟨h2, h1, h4, h5, rfl⟩
  · right
    have hxe : (cells p).i = .e := hx hxc
    have hnd := dooms_none r cells d p
      (by rintro ⟨_, h2, _⟩; rw [hxe] at h2; cases h2)
      (by rintro ⟨_, h2, _⟩; rw [hxe] at h2; cases h2)
    refine mn_le_of r cells _ d (some p) hnd (hXle0 ?_)
    rintro ⟨h1, _, _⟩; rw [hxe] at h1; cases h1
  · have hnA : ¬ EventA cells p := by
      rintro ⟨_, h2, _⟩; rw [hxx] at h2; cases h2
    have hS2 : ∀ k, (setTwo cells p pr.1 pr.2 k).i.isS = true → (cells k).i.isS = true := by
      intro k hk
      by_cases h1 : k = p
      · subst h1; rw [hSp, hx'S] at hk; exact absurd hk (by simp)
      · by_cases h2 : k = p + 1
        · subst h2; rw [hSq, hy'S] at hk; exact absurd hk (by simp)
        · rw [hSo k h1 h2] at hk; exact hk
    by_cases ha : act r cells d (p + 1) = true
    · left
      obtain ⟨_, hyS', hyd⟩ := (act_iff r cells d (p + 1)).1 ha
      refine act_cut_case_lt r cells _ d (some p) (p + 1) ha ?_ hS2 ?_ ?_ ?_
      · intro k hk hact
        obtain ⟨_, hk2, _⟩ := (act_iff r cells d k).1 hact
        by_cases h1 : k = p
        · subst h1; rw [hxS] at hk2; exact absurd hk2 (by simp)
        · rw [hSo k h1 hk]; exact hk2
      · rw [hSq]; exact hy'S
      · intro m hm hA
        unfold dooms
        exact Or.inr ⟨⟨hxc, hxx, hp, hyS', hyc⟩, hyd, hm, hA⟩
      · intro m h
        unfold dooms at h
        rcases h with ⟨hA, _⟩ | ⟨_, _, h3, h4⟩
        · exact absurd hA hnA
        · exact ⟨h3, h4⟩
    · right
      have hd : d (p + 1) := by
        by_cases hd : d (p + 1)
        · exact hd
        · exact absurd ((act_iff r cells d (p + 1)).2 ⟨hp, hyS, hd⟩) ha
      refine mn_le_of r cells _ d (some p) ?_ (hXle0 ?_)
      · intro m h
        unfold dooms at h
        rcases h with ⟨hA, _⟩ | ⟨_, h2, _⟩
        · exact hnA hA
        · exact h2 hd
      · rintro ⟨h1, _, _⟩; rw [hxx] at h1; cases h1
  · have hp0 : p ≠ 0 := by simpa using hb
    have hEA : EventA cells p := ⟨hxc, hxst, hp0⟩
    have hnB : ¬ EventB r cells p := by
      rintro ⟨_, h2, _⟩; rw [hxst] at h2; cases h2
    have hxS : (cells p).i.isS = true := by rw [hxst]; rfl
    have hS2 : ∀ k, (setTwo cells p pr.1 pr.2 k).i.isS = true → (cells k).i.isS = true := by
      intro k hk
      by_cases h1 : k = p
      · subst h1; rw [hSp, hx'S] at hk; exact absurd hk (by simp)
      · by_cases h2 : k = p + 1
        · subst h2; rw [hSq, hy'S] at hk; exact hk
        · rw [hSo k h1 h2] at hk; exact hk
    have hS1' : ∀ k, k ≠ p → act r cells d k = true →
        (setTwo cells p pr.1 pr.2 k).i.isS = true := by
      intro k hk hact
      obtain ⟨_, hk2, _⟩ := (act_iff r cells d k).1 hact
      by_cases h2 : k = p + 1
      · subst h2; rw [hSq, hy'S]; exact hk2
      · rw [hSo k hk h2]; exact hk2
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
  · right
    have hp0 : p = 0 := by simpa using hb
    have hnA : ¬ EventA cells p := by
      rintro ⟨_, _, h3⟩; exact h3 hp0
    have hnB : ¬ EventB r cells p := by
      rintro ⟨_, h2, _⟩
      have := (isS_facts _ hxS).2.1
      exact this h2
    refine mn_le_of r cells _ d (some p) (dooms_none r cells d p hnA hnB) (hXle0 ?_)
    rintro ⟨_, _, h3⟩; rw [hb] at h3; cases h3
  · right
    obtain ⟨hxst, hxx, hxS⟩ := isP_facts _ hxP
    have hnA : ¬ EventA cells p := by
      rintro ⟨_, h2, _⟩; exact hxst h2
    have hnB : ¬ EventB r cells p := by
      rintro ⟨_, h2, _⟩; exact hxx h2
    exact mn_le_of r cells _ d (some p) (dooms_none r cells d p hnA hnB)
      (hXle0 (by rintro ⟨h1, _, _⟩; exact hxst h1))

end MarkedCells
end L3

#print axioms L3.MarkedCells.edge_pot
