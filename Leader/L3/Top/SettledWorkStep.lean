import Leader.L3.Top.SettledWorkCharge
import Leader.L3.Top.SettledWorkPair

/-!
# Q7 (P.6): the active sets of the colouring and the shapes of their change

`act` is the set of active settled registers of a coloured window.  This module shows
that for each shape of change of one step (nothing changes; a run is cut from a site on;
the left end of a run is consumed; a site is added to the left of a run) the charge of
the active set does not rise.

Consumer: `Leader/L3/Top/SettledWorkStep.lean` (`edge_charge`).
-/

namespace L3
namespace MarkedCells

set_option autoImplicit false
set_option linter.unusedSimpArgs false

open Classical in
/-- The active settled registers of a window: settled and not doomed.

Consumer: `act_iff`. -/
noncomputable def act (r : Nat) (cells : Nat → Cell) (d : Nat → Prop) : Nat → Bool :=
  fun k => decide (k < r ∧ (cells k).i.isS = true ∧ ¬ d k)

/-- Membership in the active set.

Consumer: `act_cut_case`. -/
theorem act_iff (r : Nat) (cells : Nat → Cell) (d : Nat → Prop) (k : Nat) :
    act r cells d k = true ↔ k < r ∧ (cells k).i.isS = true ∧ ¬ d k := by
  unfold act; simp

/-- No active register beyond the window.

Consumer: `act_cut_case`. -/
theorem act_bd (r : Nat) (cells : Nat → Cell) (d : Nat → Prop) (m : Nat) (h : r ≤ m) :
    act r cells d m = false := by
  cases hh : act r cells d m
  · rfl
  · have := (act_iff r cells d m).1 hh; omega

/-- Membership in the active set after a colour step.

Consumer: `act_cut_case`. -/
theorem act_next_iff (r : Nat) (cells cells' : Nat → Cell) (d : Nat → Prop)
    (po : Option Nat) (k : Nat) :
    act r cells' (colourGen r cells cells' d po) k = true ↔
      k < r ∧ (cells' k).i.isS = true ∧
        ((cells k).i.isS = false ∨ (¬ d k ∧ ¬ dooms r cells d po k)) := by
  rw [act_iff]
  unfold colourGen
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, h2, ?_⟩
    cases hs : (cells k).i.isS
    · exact Or.inl rfl
    · right
      refine ⟨fun hd => h3 ⟨h1, h2, hs, Or.inl hd⟩, fun hd => h3 ⟨h1, h2, hs, Or.inr hd⟩⟩
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, h2, ?_⟩
    rintro ⟨_, _, hs, hd⟩
    rcases h3 with h3 | ⟨h3, h4⟩
    · rw [hs] at h3; exact absurd h3 (by simp)
    · rcases hd with hd | hd
      · exact h3 hd
      · exact h4 hd

/-- Nothing changes in the active set: active registers stay settled, no register becomes
settled, nothing is doomed.

Consumer: `edge_charge`. -/
theorem act_same_case (r : Nat) (cells cells' : Nat → Cell) (d : Nat → Prop)
    (po : Option Nat)
    (hS1 : ∀ k, act r cells d k = true → (cells' k).i.isS = true)
    (hS2 : ∀ k, (cells' k).i.isS = true → (cells k).i.isS = true)
    (hnd : ∀ m, ¬ dooms r cells d po m) :
    charge r (act r cells' (colourGen r cells cells' d po)) ≤ charge r (act r cells d) := by
  have : act r cells' (colourGen r cells cells' d po) = act r cells d := by
    funext k
    cases h1 : act r cells d k
    · cases h2 : act r cells' (colourGen r cells cells' d po) k
      · rfl
      · obtain ⟨hk, hk1, hk2⟩ := (act_next_iff r cells cells' d po k).1 h2
        have hk1' := hS2 k hk1
        rcases hk2 with hk2 | ⟨hk2, _⟩
        · rw [hk1'] at hk2; exact absurd hk2 (by simp)
        · have := (act_iff r cells d k).2 ⟨hk, hk1', hk2⟩
          rw [h1] at this; exact absurd this (by simp)
    · obtain ⟨hk, hk1, hk2⟩ := (act_iff r cells d k).1 h1
      exact (act_next_iff r cells cells' d po k).2
        ⟨hk, hS1 k h1, Or.inr ⟨hk2, hnd k⟩⟩
  rw [this]; exact Nat.le_refl _

/-- The left end `s` of an active run is consumed, nothing else changes.

Consumer: `edge_charge`. -/
theorem act_drop_case (r : Nat) (cells cells' : Nat → Cell) (d : Nat → Prop)
    (po : Option Nat) (s : Nat) (hs : act r cells d s = true)
    (hleft : ∀ j, j + 1 = s → act r cells d j = false)
    (hS1 : ∀ k, k ≠ s → act r cells d k = true → (cells' k).i.isS = true)
    (hS2 : ∀ k, (cells' k).i.isS = true → (cells k).i.isS = true)
    (hs' : (cells' s).i.isS = false)
    (hnd : ∀ m, ¬ dooms r cells d po m) :
    charge r (act r cells' (colourGen r cells cells' d po)) ≤ charge r (act r cells d) := by
  obtain ⟨hsr, _, _⟩ := (act_iff r cells d s).1 hs
  refine charge_drop_left (act r cells d) (act r cells' (colourGen r cells cells' d po)) s hs
    ?_ hleft ?_ r (by omega)
  · cases h : act r cells' (colourGen r cells cells' d po) s
    · rfl
    · have := ((act_next_iff r cells cells' d po s).1 h).2.1
      rw [hs'] at this; exact absurd this (by simp)
  · intro m hm
    cases h1 : act r cells d m
    · cases h2 : act r cells' (colourGen r cells cells' d po) m
      · rfl
      · obtain ⟨hk, hk1, hk2⟩ := (act_next_iff r cells cells' d po m).1 h2
        have hk1' := hS2 m hk1
        rcases hk2 with hk2 | ⟨hk2, _⟩
        · rw [hk1'] at hk2; exact absurd hk2 (by simp)
        · have := (act_iff r cells d m).2 ⟨hk, hk1', hk2⟩
          rw [h1] at this; exact absurd this (by simp)
    · obtain ⟨hk, hk1, hk2⟩ := (act_iff r cells d m).1 h1
      exact (act_next_iff r cells cells' d po m).2
        ⟨hk, hS1 m hm h1, Or.inr ⟨hk2, hnd m⟩⟩

/-- A new settled register `s` appears directly left of an active register.

Consumer: `edge_charge`. -/
theorem act_add_case (r : Nat) (cells cells' : Nat → Cell) (d : Nat → Prop)
    (po : Option Nat) (s : Nat) (hsr : s < r) (hs : (cells s).i.isS = false)
    (hs' : (cells' s).i.isS = true) (hnext : act r cells d (s + 1) = true)
    (hS1 : ∀ k, act r cells d k = true → (cells' k).i.isS = true)
    (hS2 : ∀ k, k ≠ s → (cells' k).i.isS = true → (cells k).i.isS = true)
    (hnd : ∀ m, ¬ dooms r cells d po m) :
    charge r (act r cells' (colourGen r cells cells' d po)) ≤ charge r (act r cells d) := by
  have hnr := (act_iff r cells d (s + 1)).1 hnext
  refine charge_add_left (act r cells d) (act r cells' (colourGen r cells cells' d po)) s
    ?_ ?_ hnext ?_ r (by omega)
  · cases h : act r cells d s
    · rfl
    · have := ((act_iff r cells d s).1 h).2.1
      rw [hs] at this; exact absurd this (by simp)
  · exact (act_next_iff r cells cells' d po s).2 ⟨hsr, hs', Or.inl hs⟩
  · intro m hm
    cases h1 : act r cells d m
    · cases h2 : act r cells' (colourGen r cells cells' d po) m
      · rfl
      · obtain ⟨hk, hk1, hk2⟩ := (act_next_iff r cells cells' d po m).1 h2
        have hk1' := hS2 m hm hk1
        rcases hk2 with hk2 | ⟨hk2, _⟩
        · rw [hk1'] at hk2; exact absurd hk2 (by simp)
        · have := (act_iff r cells d m).2 ⟨hk, hk1', hk2⟩
          rw [h1] at this; exact absurd this (by simp)
    · obtain ⟨hk, hk1, hk2⟩ := (act_iff r cells d m).1 h1
      exact (act_next_iff r cells cells' d po m).2
        ⟨hk, hS1 m h1, Or.inr ⟨hk2, hnd m⟩⟩

/-- The active run from `s` on is cut: `s` stops being settled and exactly the later
members of its run are doomed.

Consumer: `edge_charge`. -/
theorem act_cut_case_lt (r : Nat) (cells cells' : Nat → Cell) (d : Nat → Prop)
    (po : Option Nat) (s : Nat) (hs : act r cells d s = true)
    (hS1 : ∀ k, k ≠ s → act r cells d k = true → (cells' k).i.isS = true)
    (hS2 : ∀ k, (cells' k).i.isS = true → (cells k).i.isS = true)
    (hs' : (cells' s).i.isS = false)
    (hdoom : ∀ m, s < m → ActiveFrom cells d s m → dooms r cells d po m)
    (hnodoom : ∀ m, dooms r cells d po m → s < m ∧ ActiveFrom cells d s m) :
    charge r (act r cells' (colourGen r cells cells' d po)) < charge r (act r cells d) := by
  obtain ⟨hsr, _, _⟩ := (act_iff r cells d s).1 hs
  have hrunA : ∀ m, s < m → m < r →
      (∀ j, s ≤ j → j ≤ m → act r cells d j = true) → ActiveFrom cells d s m := by
    intro m hm _ hall
    refine ⟨by omega, fun j hj1 hj2 => ?_⟩
    obtain ⟨_, h2, h3⟩ := (act_iff r cells d j).1 (hall j hj1 hj2)
    exact ⟨h2, h3⟩
  have hrunB : ∀ m, m < r → ActiveFrom cells d s m →
      ∀ j, s ≤ j → j ≤ m → act r cells d j = true := by
    intro m hm hA j hj1 hj2
    obtain ⟨h2, h3⟩ := hA.2 j hj1 hj2
    exact (act_iff r cells d j).2 ⟨by omega, h2, h3⟩
  refine charge_cut_gen_lt r (act r cells d) (act r cells' (colourGen r cells cells' d po)) s
    (act_bd r cells d) hs hsr ?_ ?_ ?_ ?_
  · -- before `s` nothing changes
    intro m hm
    cases h1 : act r cells d m
    · cases h2 : act r cells' (colourGen r cells cells' d po) m
      · rfl
      · obtain ⟨hk, hk1, hk2⟩ := (act_next_iff r cells cells' d po m).1 h2
        have hk1' := hS2 m hk1
        rcases hk2 with hk2 | ⟨hk2, _⟩
        · rw [hk1'] at hk2; exact absurd hk2 (by simp)
        · have := (act_iff r cells d m).2 ⟨hk, hk1', hk2⟩
          rw [h1] at this; exact absurd this (by simp)
    · obtain ⟨hk, hk1, hk2⟩ := (act_iff r cells d m).1 h1
      exact (act_next_iff r cells cells' d po m).2
        ⟨hk, hS1 m (by omega) h1, Or.inr ⟨hk2, fun hd => by
          have := (hnodoom m hd).1; omega⟩⟩
  · cases h : act r cells' (colourGen r cells cells' d po) s
    · rfl
    · have := ((act_next_iff r cells cells' d po s).1 h).2.1
      rw [hs'] at this; exact absurd this (by simp)
  · -- later members of the run are doomed
    intro m hm hall
    have hmr : m < r := ((act_iff r cells d m).1 (hall m (by omega) (Nat.le_refl _))).1
    have hA := hrunA m hm hmr hall
    cases h : act r cells' (colourGen r cells cells' d po) m
    · rfl
    · obtain ⟨_, _, hk2⟩ := (act_next_iff r cells cells' d po m).1 h
      obtain ⟨_, hm2, _⟩ := (act_iff r cells d m).1 (hall m (by omega) (Nat.le_refl _))
      rcases hk2 with hk2 | ⟨_, hk3⟩
      · rw [hm2] at hk2; exact absurd hk2 (by simp)
      · exact absurd (hdoom m hm hA) hk3
  · -- outside the run nothing changes
    intro m hm hnrun
    cases h1 : act r cells d m
    · cases h2 : act r cells' (colourGen r cells cells' d po) m
      · rfl
      · obtain ⟨hk, hk1, hk2⟩ := (act_next_iff r cells cells' d po m).1 h2
        have hk1' := hS2 m hk1
        rcases hk2 with hk2 | ⟨hk2, _⟩
        · rw [hk1'] at hk2; exact absurd hk2 (by simp)
        · have := (act_iff r cells d m).2 ⟨hk, hk1', hk2⟩
          rw [h1] at this; exact absurd this (by simp)
    · obtain ⟨hk, hk1, hk2⟩ := (act_iff r cells d m).1 h1
      exact (act_next_iff r cells cells' d po m).2
        ⟨hk, hS1 m (by omega) h1, Or.inr ⟨hk2, fun hd => by
          exact hnrun (hrunB m hk (hnodoom m hd).2)⟩⟩

/-- Cutting an active run does not raise the charge.

Consumer: `edge_charge`. -/
theorem act_cut_case (r : Nat) (cells cells' : Nat → Cell) (d : Nat → Prop)
    (po : Option Nat) (s : Nat) (hs : act r cells d s = true)
    (hS1 : ∀ k, k ≠ s → act r cells d k = true → (cells' k).i.isS = true)
    (hS2 : ∀ k, (cells' k).i.isS = true → (cells k).i.isS = true)
    (hs' : (cells' s).i.isS = false)
    (hdoom : ∀ m, s < m → ActiveFrom cells d s m → dooms r cells d po m)
    (hnodoom : ∀ m, dooms r cells d po m → s < m ∧ ActiveFrom cells d s m) :
    charge r (act r cells' (colourGen r cells cells' d po)) ≤ charge r (act r cells d) :=
  Nat.le_of_lt (act_cut_case_lt r cells cells' d po s hs hS1 hS2 hs' hdoom hnodoom)

end MarkedCells
end L3
