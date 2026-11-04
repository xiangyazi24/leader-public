import Std.Tactic

/-!
# Peak-safe relabeling with two ordered palettes

This file isolates the combinatorial overflow-recovery idea for structural
leader-birth suppression.  Normal labels lie below `base`.  A rebuild label
`base + value` is therefore larger than every normal label.  Installing target
labels from high levels to low levels, and later removing the rebuild palette
from low levels to high levels, preserves the pairwise peak condition at every
intermediate selection.

The selection predicates below describe an arbitrary prefix inside one level,
so the theorem does not assume that all cells of a distributed round change
atomically.  It still does not provide the physical traversal, authentication,
or service bound.
-/

/-- Indexed form of the pairwise peak property. -/
def IndexedPeakSafe {n : Nat} (word : Fin n -> Nat) : Prop :=
  forall i j : Fin n, i.val < j.val -> word i = word j ->
    exists k : Fin n,
      i.val < k.val /\ k.val < j.val /\ word i < word k

/-- Select positions from `target` into the upper palette, leaving all other
positions at their `source` labels. -/
def paletteMix {n : Nat} (base : Nat)
    (source target : Fin n -> Nat) (selected : Fin n -> Prop)
    [DecidablePred selected] : Fin n -> Nat :=
  fun i => if selected i then base + target i else source i

/-- During the installation pass, every selected target level must bring all
strictly higher target levels with it.  Positions at one equal level may be
selected in any order. -/
theorem paletteMix_install_peak_safe {n base : Nat}
    (source target : Fin n -> Nat) (selected : Fin n -> Prop)
    [DecidablePred selected]
    (source_safe : IndexedPeakSafe source)
    (target_safe : IndexedPeakSafe target)
    (source_lt : forall i, source i < base)
    (selected_up : forall i k, selected i -> target i < target k -> selected k) :
    IndexedPeakSafe (paletteMix base source target selected) := by
  intro i j hij heq
  by_cases hi : selected i <;> by_cases hj : selected j
  · have target_eq : target i = target j := by
      simp only [paletteMix, if_pos hi, if_pos hj] at heq
      omega
    obtain ⟨k, hik, hkj, hpeak⟩ := target_safe i j hij target_eq
    have hk : selected k := selected_up i k hi hpeak
    refine ⟨k, hik, hkj, ?_⟩
    simp only [paletteMix, if_pos hi, if_pos hk]
    omega
  · simp only [paletteMix, if_pos hi, if_neg hj] at heq
    have := source_lt j
    omega
  · simp only [paletteMix, if_neg hi, if_pos hj] at heq
    have := source_lt i
    omega
  · have source_eq : source i = source j := by
      simpa only [paletteMix, if_neg hi, if_neg hj] using heq
    obtain ⟨k, hik, hkj, hpeak⟩ := source_safe i j hij source_eq
    refine ⟨k, hik, hkj, ?_⟩
    by_cases hk : selected k
    · simp only [paletteMix, if_neg hi, if_pos hk]
      have := source_lt i
      omega
    · simpa only [paletteMix, if_neg hi, if_neg hk] using hpeak

/-- During the return pass, `selected` denotes positions still in the upper
palette.  They retain every strictly higher target level.  Equivalently,
conversion proceeds from low target levels to high target levels, with
arbitrary order inside one equal level. -/
theorem paletteMix_remove_peak_safe {n base : Nat}
    (target : Fin n -> Nat) (selected : Fin n -> Prop)
    [DecidablePred selected]
    (target_safe : IndexedPeakSafe target)
    (target_lt : forall i, target i < base)
    (selected_up : forall i k,
      selected i -> target i < target k -> selected k) :
    IndexedPeakSafe (paletteMix base target target selected) :=
  paletteMix_install_peak_safe target target selected target_safe target_safe
    target_lt selected_up

/-- A complete high-to-low installation threshold is a valid intermediate
selection. -/
theorem paletteMix_install_threshold {n base threshold : Nat}
    (source target : Fin n -> Nat)
    (source_safe : IndexedPeakSafe source)
    (target_safe : IndexedPeakSafe target)
    (source_lt : forall i, source i < base) :
    IndexedPeakSafe
      (paletteMix base source target (fun i => threshold <= target i)) := by
  apply paletteMix_install_peak_safe source target
    (fun i => threshold <= target i) source_safe target_safe source_lt
  intro i k hi hlt
  omega

/-- A complete low-to-high removal threshold is a valid intermediate
selection. -/
theorem paletteMix_remove_threshold {n base threshold : Nat}
    (target : Fin n -> Nat)
    (target_safe : IndexedPeakSafe target)
    (target_lt : forall i, target i < base) :
    IndexedPeakSafe
      (paletteMix base target target (fun i => threshold <= target i)) := by
  apply paletteMix_remove_peak_safe target
    (fun i => threshold <= target i) target_safe target_lt
  intro i k hi hlt
  omega

#print axioms paletteMix_install_peak_safe
#print axioms paletteMix_remove_peak_safe
#print axioms paletteMix_install_threshold
#print axioms paletteMix_remove_threshold
