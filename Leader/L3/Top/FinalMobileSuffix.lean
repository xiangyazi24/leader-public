import Leader.L3.Top.FinalMobileFlags

/-!
# Q7: reading a labelled window as an export suffix

If the flagged registers of a labelled window, read right to left, are the labels of
`L.drop k` for a list `L` of exports, then every flagged register is the label of an export of
index at least `k`, every export of index at least `k` labels a flagged register, and two
flagged registers with the same label key are the same register when the keys of `L` are
distinct.  These are the three clauses of the consecutive pending suffix.

Consumer: `Leader/L3/Top/FinalMobileLabels.lean`.
-/

namespace L3
namespace MarkedCells

set_option autoImplicit false

/-- Membership in the reading of a window.

Consumer: `extract_suffix`. -/
theorem mem_ordLab {α : Type} (o : Nat → Bool) (ℓ : Nat → α) :
    ∀ m x, x ∈ ordLab o ℓ m ↔ ∃ j, j < m ∧ o j = true ∧ ℓ j = x := by
  intro m
  induction m with
  | zero => intro x; simp [ordLab]
  | succ m ih =>
    intro x
    simp only [ordLab, List.mem_append]
    constructor
    · rintro (h | h)
      · by_cases hm : o m = true
        · rw [if_pos hm] at h
          simp only [List.mem_singleton] at h
          exact ⟨m, by omega, hm, h.symm⟩
        · rw [if_neg hm] at h
          simp at h
      · obtain ⟨j, hj, hoj, hl⟩ := (ih x).1 h
        exact ⟨j, by omega, hoj, hl⟩
    · rintro ⟨j, hj, hoj, hl⟩
      by_cases hjm : j = m
      · subst hjm
        left
        rw [if_pos hoj]
        simp [hl]
      · right
        exact (ih x).2 ⟨j, by omega, hoj, hl⟩

/-- Distinct keys read from a window belong to distinct registers.

Consumer: `extract_suffix_inj`. -/
theorem ordLab_inj {α β : Type} (o : Nat → Bool) (ℓ : Nat → α) (g : α → β) :
    ∀ m, ((ordLab o ℓ m).map g).Nodup → ∀ i j, i < m → j < m → o i = true → o j = true →
      g (ℓ i) = g (ℓ j) → i = j := by
  intro m
  induction m with
  | zero => intro _ i j hi; omega
  | succ m ih =>
    intro hnd i j hi hj hoi hoj hg
    by_cases hom : o m = true
    · have hl : ordLab o ℓ (m + 1) = ℓ m :: ordLab o ℓ m := by
        simp only [ordLab, if_pos hom]; rfl
      rw [hl] at hnd
      simp only [List.map_cons, List.nodup_cons] at hnd
      by_cases him : i = m
      · by_cases hjm : j = m
        · omega
        · exfalso
          apply hnd.1
          rw [List.mem_map]
          refine ⟨ℓ j, (mem_ordLab o ℓ m _).2 ⟨j, by omega, hoj, rfl⟩, ?_⟩
          rw [← hg, him]
      · by_cases hjm : j = m
        · exfalso
          apply hnd.1
          rw [List.mem_map]
          refine ⟨ℓ i, (mem_ordLab o ℓ m _).2 ⟨i, by omega, hoi, rfl⟩, ?_⟩
          rw [hg, hjm]
        · exact ih hnd.2 i j (by omega) (by omega) hoi hoj hg
    · have hl : ordLab o ℓ (m + 1) = ordLab o ℓ m := by
        simp only [ordLab, if_neg hom, List.nil_append]
      rw [hl] at hnd
      have him : i ≠ m := by
        intro h; subst h; exact hom hoi
      have hjm : j ≠ m := by
        intro h; subst h; exact hom hoj
      exact ih hnd _ _ (by omega) (by omega) hoi hoj hg

/-- **A window read as an export suffix.**

Consumer: `Leader/L3/Top/FinalMobileLabels.lean`. -/
theorem extract_suffix {E α : Type} (r : Nat) (o : Nat → Bool) (ℓ : Nat → α) (L : List E)
    (f : E → α) (k : Nat) (h : ordLab o ℓ r = (L.map f).drop k) :
    (∀ j, j < r → o j = true → ∃ i, ∃ hi : i < L.length, k ≤ i ∧ ℓ j = f L[i]) ∧
    (∀ i, ∀ hi : i < L.length, k ≤ i → ∃ j, j < r ∧ o j = true ∧ ℓ j = f L[i]) := by
  constructor
  · intro j hj hoj
    have hmem : ℓ j ∈ ordLab o ℓ r := (mem_ordLab o ℓ r _).2 ⟨j, hj, hoj, rfl⟩
    rw [h] at hmem
    obtain ⟨j', hm, hj'⟩ := List.mem_drop_iff_getElem.1 hmem
    have hlen : k + j' < L.length := by
      have := hm
      simp only [List.length_map] at this
      omega
    refine ⟨k + j', hlen, by omega, ?_⟩
    rw [← hj']
    simp
  · intro i hi hki
    have hmem : f L[i] ∈ (L.map f).drop k := by
      rw [List.mem_drop_iff_getElem]
      refine ⟨i - k, by simp; omega, ?_⟩
      have : k + (i - k) = i := by omega
      simp [this]
    rw [← h] at hmem
    exact (mem_ordLab o ℓ r _).1 hmem |>.imp fun j hj => ⟨hj.1, hj.2.1, hj.2.2⟩

/-- **Distinct export keys give injectivity of the flagged labels.**

Consumer: `Leader/L3/Top/FinalMobileLabels.lean`. -/
theorem extract_suffix_inj {E α β : Type} (r : Nat) (o : Nat → Bool) (ℓ : Nat → α) (L : List E)
    (f : E → α) (g : α → β) (k : Nat) (h : ordLab o ℓ r = (L.map f).drop k)
    (hnd : (L.map (fun e => g (f e))).Nodup) :
    ∀ i j, i < r → j < r → o i = true → o j = true → g (ℓ i) = g (ℓ j) → i = j := by
  apply ordLab_inj o ℓ g r
  rw [h, List.map_drop, List.map_map]
  exact List.Nodup.sublist (List.drop_sublist _ _) hnd

end MarkedCells
end L3

#print axioms L3.MarkedCells.extract_suffix
#print axioms L3.MarkedCells.extract_suffix_inj
