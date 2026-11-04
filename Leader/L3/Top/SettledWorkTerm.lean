import Leader.L3.Top.SettledWorkEdge
import Leader.L3.Top.MarkedGood

/-!
# Q7 (P.6): the terminal edge and the port do not raise the charge

The terminal edge of the window (register `r - 1`, partner absent), the port cleanup and the
port acceptance act on the abstract window.  With a settled input present and the moving
barrier, none of them raises the charge of the active set.  The terminal edge is the place
where a terminal reseed would raise it; the barrier excludes that.

Consumer: `Leader/L3/Top/SettledWorkTrace.lean`.
-/

namespace L3
namespace MarkedCells

set_option autoImplicit false
set_option linter.unusedSimpArgs false

/-- **The terminal edge does not raise the charge** (a settled input is present, the moving
barrier holds).

Consumer: `Leader/L3/Top/SettledWorkTrace.lean`. -/
theorem term_charge (r : Nat) (cells : Nat → Cell) (d : Nat → Prop) (p : Nat)
    (hp : p + 1 = r) (hp0 : p ≠ 0) (hinv : Inv r cells) (hni : NoInh r cells)
    (hbar : Barrier r cells)
    (hex : ∃ j, j < r ∧ (cells j).i.isS = true) :
    charge r (act r (setOne cells p (pair false true (cells p) { i := .e, c := .off }).1)
      (colourGen r cells (setOne cells p
        (pair false true (cells p) { i := .e, c := .off }).1) d (some p))) ≤
    charge r (act r cells d) := by
  have hx : (cells p).c ≠ .off → (cells p).i = .e := fun h =>
    host_empty hinv hni (by omega) h
  have pat := pair_pat false true (cells p) { i := .e, c := .off } hx (by intro h; exact absurd rfl h)
    (by simp)
  generalize hpr : pair false true (cells p) { i := .e, c := .off } = pr at pat ⊢
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
  · -- nothing changes
    refine act_same_case r cells _ d (some p) ?_ ?_ ?_
    · intro k hk
      obtain ⟨_, hk2, _⟩ := (act_iff r cells d k).1 hk
      by_cases h1 : k = p
      · subst h1; rw [hSp, e1]; exact hk2
      · rw [hSo k h1]; exact hk2
    · intro k hk
      by_cases h1 : k = p
      · subst h1; rw [hSp, e1] at hk; exact hk
      · rw [hSo k h1] at hk; exact hk
    · apply dooms_none r cells d p _ hnB
      rintro ⟨h1, h2, _⟩
      exact hnA ⟨h2, h1, rfl⟩
  · exact absurd ht (by simp)
  · exact absurd ht (by simp)
  · -- the terminal tail turns into a front
    have hEA : EventA cells p := ⟨hxc, hxst, hp0⟩
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
  · exact absurd hb (by simp)
  · -- a terminal reseed is excluded by the barrier
    exfalso
    obtain ⟨j, hj, hjS⟩ := hex
    have hob : obC (cells j) = true := by simp [obC, hjS]
    have := hbar p j (by omega) hj hxP hob
    omega

/-- A port step (cleanup or acceptance of a packet) does not raise the charge.

Consumer: `Leader/L3/Top/SettledWorkTrace.lean`. -/
theorem port_charge (r : Nat) (hr : 2 ≤ r) (cells cells' : Nat → Cell) (d : Nat → Prop)
    (hinv : Inv r cells) (hni : NoInh r cells)
    (hst : cells' = setOne cells 0 (portClean (cells 0)) ∨
      ∃ t, cells' = setOne cells 0 (portAccept t (cells 0))) :
    charge r (act r cells' (colourGen r cells cells' d none)) ≤ charge r (act r cells d) := by
  have hnd : ∀ m, ¬ dooms r cells d none m := by intro m h; exact h
  have hh : (cells 0).c ≠ .off → (cells 0).i = .e := fun h => host_empty hinv hni (by omega) h
  refine act_same_case r cells cells' d none ?_ ?_ hnd
  · intro k hk
    obtain ⟨_, hk2, _⟩ := (act_iff r cells d k).1 hk
    rcases hst with h | ⟨t, h⟩
    · subst h
      unfold setOne
      by_cases h1 : k = 0
      · subst h1
        simp only [if_true]
        unfold portClean
        by_cases hc : (cells 0).c = .off
        · simp [hc, hk2]
        · have := hh hc
          rw [this] at hk2; exact absurd hk2 (by simp [Inp.isS])
      · simp [h1, hk2]
    · subst h
      unfold setOne
      by_cases h1 : k = 0
      · subst h1
        simp only [if_true]
        unfold portAccept
        by_cases hc : cells 0 = { i := .e, c := .off }
        · rw [hc] at hk2; exact absurd hk2 (by simp [Inp.isS])
        · simp [hc, hk2]
      · simp [h1, hk2]
  · intro k hk
    rcases hst with h | ⟨t, h⟩
    · subst h
      unfold setOne at hk
      by_cases h1 : k = 0
      · subst h1
        simp only [if_true] at hk
        unfold portClean at hk
        by_cases hc : (cells 0).c = .off
        · simp [hc] at hk; exact hk
        · simp [hc, Inp.isS] at hk
      · simp [h1] at hk; exact hk
    · subst h
      unfold setOne at hk
      by_cases h1 : k = 0
      · subst h1
        simp only [if_true] at hk
        unfold portAccept at hk
        by_cases hc : cells 0 = { i := .e, c := .off }
        · rw [if_pos hc] at hk
          split at hk <;> simp [Inp.isS] at hk
        · rw [if_neg hc] at hk; exact hk
      · simp [h1] at hk; exact hk

end MarkedCells
end L3

#print axioms L3.MarkedCells.term_charge
#print axioms L3.MarkedCells.port_charge
