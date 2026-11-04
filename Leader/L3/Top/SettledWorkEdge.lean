import Leader.L3.Top.SettledWorkStep

/-!
# Q7 (P.6): one window edge does not raise the charge of the active set

For an edge `p -> p + 1` of the abstract window with the fresh-carry invariants, no inherited
carry and the front cover, the charge of the active settled registers after the edge and
the colour step is at most the charge before.

Consumer: `Leader/L3/Top/SettledWorkTerm.lean` (the same for the terminal edge and the port).
-/

namespace L3
namespace MarkedCells

set_option autoImplicit false
set_option linter.unusedSimpArgs false

/-- No register is doomed when neither event fires.

Consumer: `edge_charge`. -/
theorem dooms_none (r : Nat) (cells : Nat → Cell) (d : Nat → Prop) (p : Nat)
    (hA : ¬ EventA cells p) (hB : ¬ EventB r cells p) :
    ∀ m, ¬ dooms r cells d (some p) m := by
  intro m h
  unfold dooms at h
  rcases h with h | h
  · exact hA h.1
  · exact hB h.1

/-- A pending input is neither a tail-settled input nor a front, nor settled.

Consumer: `edge_charge`. -/
theorem isP_facts (i : Inp) (h : i.isP = true) : i ≠ .st ∧ i ≠ .x ∧ i.isS = false := by
  cases i <;> simp [Inp.isP, Inp.isS] at h ⊢

/-- A settled input is not pending, not empty and not a front.

Consumer: `edge_charge`. -/
theorem isS_facts (i : Inp) (h : i.isS = true) : i ≠ .e ∧ i ≠ .x ∧ i.isP = false := by
  cases i <;> simp [Inp.isP, Inp.isS] at h ⊢

/-- **One window edge does not raise the charge.**

Consumer: `Leader/L3/Top/SettledWorkTerm.lean`. -/
theorem edge_charge (r : Nat) (cells : Nat → Cell) (d : Nat → Prop) (p : Nat)
    (hp : p + 1 < r) (hinv : Inv r cells) (hni : NoInh r cells) (hcov : Cover r cells d) :
    charge r (act r (setTwo cells p (pair (decide (p = 0)) false (cells p) (cells (p + 1))).1
        (pair (decide (p = 0)) false (cells p) (cells (p + 1))).2)
      (colourGen r cells (setTwo cells p
        (pair (decide (p = 0)) false (cells p) (cells (p + 1))).1
        (pair (decide (p = 0)) false (cells p) (cells (p + 1))).2) d (some p))) ≤
    charge r (act r cells d) := by
  have hx : (cells p).c ≠ .off → (cells p).i = .e := fun h =>
    host_empty hinv hni (by omega) h
  have hy : (cells (p + 1)).c ≠ .off → (cells (p + 1)).i = .e := fun h =>
    host_empty hinv hni hp h
  have pat := pair_pat (decide (p = 0)) false (cells p) (cells (p + 1)) hx hy (by simp)
  generalize hpr : pair (decide (p = 0)) false (cells p) (cells (p + 1)) = pr at pat ⊢
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
  · -- nothing changes
    refine act_same_case r cells _ d (some p) ?_ ?_ ?_
    · intro k hk
      obtain ⟨_, hk2, _⟩ := (act_iff r cells d k).1 hk
      by_cases h1 : k = p
      · subst h1; rw [hSp, e1]; exact hk2
      · by_cases h2 : k = p + 1
        · subst h2; rw [hSq, e2]; exact hk2
        · rw [hSo k h1 h2]; exact hk2
    · intro k hk
      by_cases h1 : k = p
      · subst h1; rw [hSp, e1] at hk; exact hk
      · by_cases h2 : k = p + 1
        · subst h2; rw [hSq, e2] at hk; exact hk
        · rw [hSo k h1 h2] at hk; exact hk
    · apply dooms_none
      · rintro ⟨h1, h2, h3⟩
        exact hnA ⟨h2, h1, by simpa using h3⟩
      · rintro ⟨h1, h2, h3, h4, h5⟩
        exact hnB ⟨h2, h1, h4, h5, rfl⟩
  · -- a carry advances and consumes the right register
    have hxe : (cells p).i = .e := hx hxc
    have hnd := dooms_none r cells d p
      (by rintro ⟨_, h2, _⟩; rw [hxe] at h2; cases h2)
      (by rintro ⟨_, h2, _⟩; rw [hxe] at h2; cases h2)
    have hS2 : ∀ k, (setTwo cells p pr.1 pr.2 k).i.isS = true → (cells k).i.isS = true := by
      intro k hk
      by_cases h1 : k = p
      · subst h1; rw [hSp, hx'S] at hk; exact absurd hk (by simp)
      · by_cases h2 : k = p + 1
        · subst h2; rw [hSq, hy'S] at hk; exact absurd hk (by simp)
        · rw [hSo k h1 h2] at hk; exact hk
    by_cases ha : act r cells d (p + 1) = true
    · refine act_drop_case r cells _ d (some p) (p + 1) ha ?_ ?_ hS2 ?_ hnd
      · intro j hj
        have : j = p := by omega
        subst this
        cases h : act r cells d j
        · rfl
        · have := ((act_iff r cells d j).1 h).2.1
          rw [hxS] at this; exact absurd this (by simp)
      · intro k hk hact
        obtain ⟨_, hk2, _⟩ := (act_iff r cells d k).1 hact
        by_cases h1 : k = p
        · subst h1; rw [hxS] at hk2; exact absurd hk2 (by simp)
        · rw [hSo k h1 hk]; exact hk2
      · rw [hSq]; exact hy'S
    · refine act_same_case r cells _ d (some p) ?_ hS2 hnd
      intro k hk
      obtain ⟨_, hk2, _⟩ := (act_iff r cells d k).1 hk
      by_cases h1 : k = p
      · subst h1; rw [hxS] at hk2; exact absurd hk2 (by simp)
      · by_cases h2 : k = p + 1
        · subst h2; exact absurd hk ha
        · rw [hSo k h1 h2]; exact hk2
  · -- a front advances into the right register
    have hnA : ¬ EventA cells p := by
      rintro ⟨_, h2, _⟩; rw [hxx] at h2; cases h2
    have hS2 : ∀ k, (setTwo cells p pr.1 pr.2 k).i.isS = true → (cells k).i.isS = true := by
      intro k hk
      by_cases h1 : k = p
      · subst h1; rw [hSp, hx'S] at hk; exact absurd hk (by simp)
      · by_cases h2 : k = p + 1
        · subst h2; rw [hSq, hy'S] at hk; exact absurd hk (by simp)
        · rw [hSo k h1 h2] at hk; exact hk
    by_cases ha : act r cells d (p + 1) = true
    · obtain ⟨_, hyS', hyd⟩ := (act_iff r cells d (p + 1)).1 ha
      refine act_cut_case r cells _ d (some p) (p + 1) ha ?_ hS2 ?_ ?_ ?_
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
    · have hd : d (p + 1) := by
        by_cases hd : d (p + 1)
        · exact hd
        · exact absurd ((act_iff r cells d (p + 1)).2 ⟨hp, hyS, hd⟩) ha
      refine act_same_case r cells _ d (some p) ?_ hS2 ?_
      · intro k hk
        obtain ⟨_, hk2, _⟩ := (act_iff r cells d k).1 hk
        by_cases h1 : k = p
        · subst h1; rw [hxS] at hk2; exact absurd hk2 (by simp)
        · by_cases h2 : k = p + 1
          · subst h2; exact absurd hk ha
          · rw [hSo k h1 h2]; exact hk2
      · intro m h
        unfold dooms at h
        rcases h with ⟨hA, _⟩ | ⟨_, h2, _⟩
        · exact hnA hA
        · exact h2 hd
  · -- the non-border settled tail turns into a front
    have hp0 : p ≠ 0 := by simpa using hb
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
    · obtain ⟨_, _, hpd⟩ := (act_iff r cells d p).1 ha
      refine act_cut_case r cells _ d (some p) p ha hS1' hS2 ?_ ?_ ?_
      · rw [hSp]; exact hx'S
      · intro m hm hA
        unfold dooms
        exact Or.inl ⟨hEA, hpd, hm, hA⟩
      · intro m h
        unfold dooms at h
        rcases h with ⟨_, _, h3, h4⟩ | ⟨hB, _⟩
        · exact ⟨h3, h4⟩
        · exact absurd hB hnB
    · have hd : d p := by
        by_cases hd : d p
        · exact hd
        · exact absurd ((act_iff r cells d p).2 ⟨by omega, hxS, hd⟩) ha
      refine act_same_case r cells _ d (some p) ?_ hS2 ?_
      · intro k hk
        by_cases h1 : k = p
        · subst h1; exact absurd hk ha
        · exact hS1' k h1 hk
      · intro m h
        unfold dooms at h
        rcases h with ⟨_, h2, _⟩ | ⟨hB, _⟩
        · exact h2 hd
        · exact hnB hB
  · -- border launch of a carry consumes the settled border operand
    have hp0 : p = 0 := by simpa using hb
    have hnA : ¬ EventA cells p := by
      rintro ⟨_, _, h3⟩; exact h3 hp0
    have hnB : ¬ EventB r cells p := by
      rintro ⟨_, h2, _⟩
      have := (isS_facts _ hxS).2.1
      exact this h2
    have hnd := dooms_none r cells d p hnA hnB
    have hS2 : ∀ k, (setTwo cells p pr.1 pr.2 k).i.isS = true → (cells k).i.isS = true := by
      intro k hk
      by_cases h1 : k = p
      · subst h1; rw [hSp, hx'S] at hk; exact absurd hk (by simp)
      · by_cases h2 : k = p + 1
        · subst h2; rw [hSq, hy'S] at hk; exact hk
        · rw [hSo k h1 h2] at hk; exact hk
    have ha : act r cells d p = true := by
      refine (act_iff r cells d p).2 ⟨by omega, hxS, fun hd => ?_⟩
      have := (hcov p hd).1
      omega
    refine act_drop_case r cells _ d (some p) p ha ?_ ?_ hS2 ?_ hnd
    · intro j hj; omega
    · intro k hk hact
      obtain ⟨_, hk2, _⟩ := (act_iff r cells d k).1 hact
      by_cases h2 : k = p + 1
      · subst h2; rw [hSq, hy'S]; exact hk2
      · rw [hSo k hk h2]; exact hk2
    · rw [hSp]; exact hx'S
  · -- a pending packet settles directly left of a settled register
    obtain ⟨hxst, hxx, hxS⟩ := isP_facts _ hxP
    have hyS : (cells (p + 1)).i.isS = true := by
      rcases hcond with h | ⟨h, _⟩
      · exact absurd h (by simp)
      · exact h
    have hnA : ¬ EventA cells p := by
      rintro ⟨_, h2, _⟩; exact hxst h2
    have hnB : ¬ EventB r cells p := by
      rintro ⟨_, h2, _⟩; exact hxx h2
    have hnd := dooms_none r cells d p hnA hnB
    have hnd1 : ¬ d (p + 1) := by
      intro hd
      obtain ⟨_, _, h3⟩ := hcov (p + 1) hd
      have e : p + 1 - 1 = p := by omega
      rw [e] at h3
      rcases h3 with h3 | h3
      · exact hxx h3
      · have := (hcov p h3).2.1
        rw [hxS] at this; exact absurd this (by simp)
    have hnext : act r cells d (p + 1) = true := (act_iff r cells d (p + 1)).2 ⟨hp, hyS, hnd1⟩
    refine act_add_case r cells _ d (some p) p (by omega) hxS ?_ hnext ?_ ?_ hnd
    · rw [hSp]; exact hx'S
    · intro k hk
      obtain ⟨_, hk2, _⟩ := (act_iff r cells d k).1 hk
      by_cases h1 : k = p
      · subst h1; rw [hxS] at hk2; exact absurd hk2 (by simp)
      · by_cases h2 : k = p + 1
        · subst h2; rw [hSq, hy'S]; exact hk2
        · rw [hSo k h1 h2]; exact hk2
    · intro k hk1 hk
      by_cases h2 : k = p + 1
      · subst h2; rw [hSq, hy'S] at hk; exact hk
      · rw [hSo k hk1 h2] at hk; exact hk

end MarkedCells
end L3

#print axioms L3.MarkedCells.edge_charge
