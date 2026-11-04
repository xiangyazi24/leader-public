import Leader.L3.Width.DigitQuietStepGlue
import Leader.L3.Width.DigitQuietStepReport
import Leader.L3.Width.DigitQuietStepArith

/-!
# The quiet class: positions, leaders, markers and blocks

* `digitSite_inj`: `digitSite` is injective on `[0, n)`;
* `leader_at`, `marker_at`: the leader flag and the marker (`beta`) of the site at position `q` of a
  state of the class;
* `block_complete`: a block `first + j R` with `first + (j + 1) R < n` is a complete value block;
* `block_digit`: the digit relation of a pair of complete blocks (`values_digitwise`) in position form.

Consumer: `WidthDigitQuietStepPairs`.
-/

namespace L3.DigitQuiet

open L3
open L3.AcceptedReceipts

set_option autoImplicit false

variable {c : Compiled} {n : Nat}

/-- `digitSite` is injective on `[0, n)`.  Consumer: `leader_at`, the pair closure. -/
theorem digitSite_inj (ring : DirectedRing n) (root : Fin n) {p q : Nat} (hp : p < n) (hq : q < n)
    (h : digitSite ring root p = digitSite ring root q) : p = q := by
  have h1 := congrArg Fin.val h
  rw [RenewalReferenceClock.bankRepairDigitSiteVal, RenewalReferenceClock.bankRepairDigitSiteVal] at h1
  have hr := root.isLt
  have hn : 0 < n := by omega
  -- (root + p) % n = (root + q) % n with p, q < n
  rcases Nat.lt_or_ge (root.val + p) n with a | a <;> rcases Nat.lt_or_ge (root.val + q) n with b | b
  · rw [Nat.mod_eq_of_lt a, Nat.mod_eq_of_lt b] at h1; omega
  · rw [Nat.mod_eq_of_lt a, Nat.mod_eq_sub_mod b, Nat.mod_eq_of_lt (by omega)] at h1; omega
  · rw [Nat.mod_eq_sub_mod a, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt b] at h1; omega
  · rw [Nat.mod_eq_sub_mod a, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_sub_mod b,
      Nat.mod_eq_of_lt (by omega)] at h1; omega

/-- The leader flag of the site at position `q` of a state of the class.  Consumer: the pair
closure. -/
theorem leader_at (ring : DirectedRing n) (root : Fin n) (first : Nat) (S : Fin n → ProjD c)
    (hQ : WidthDigitQuiet ring root first S) {q : Nat} (hq : q < n) :
    (S (digitSite ring root q)).word.native.l = decide (q = 0) := by
  have h := hQ.rootFixed (digitSite ring root q)
  by_cases h0 : q = 0
  · subst h0
    have := h.mpr rfl
    simp [this]
  · have : ¬ (digitSite ring root q = root) := by
      intro he
      have : digitSite ring root q = digitSite ring root 0 := he
      exact h0 (digitSite_inj ring root hq (by omega) this)
    cases hl : (S (digitSite ring root q)).word.native.l
    · simp [h0]
    · exact absurd (h.mp hl) this

/-- The marker of the site at position `q`, `0 < q < n`.  Consumer: the pair closure. -/
theorem marker_at (ring : DirectedRing n) (root : Fin n) (first : Nat) (S : Fin n → ProjD c)
    (hQ : WidthDigitQuiet ring root first S) {q : Nat} (h0 : 0 < q) (hq : q < n) :
    (S (digitSite ring root q)).word.beta =
      decide (first ≤ q ∧ (q - first) % digitSpan c = 0) := by
  have h := hQ.layout.2.2 q h0 hq
  cases hb : (S (digitSite ring root q)).word.beta
  · rw [hb] at h
    simp only [Bool.false_eq_true, false_iff] at h
    simp [h]
  · rw [hb] at h
    simp only [true_iff] at h
    simp [h]

/-- **A block of the layout is a complete value block.**  Consumer: the digit hypothesis of the fin
letter of the pair closure. -/
theorem block_complete (ring : DirectedRing n) (root : Fin n) (first : Nat) (S : Fin n → ProjD c)
    (hQ : WidthDigitQuiet ring root first S) (hR : 0 < digitSpan c) (j : Nat)
    (hj : first + (j + 1) * digitSpan c < n) :
    completeValueBlock ring root (digitValueView S) (first + j * digitSpan c) := by
  have e1 : (j + 1) * digitSpan c = j * digitSpan c + digitSpan c := by rw [Nat.add_mul]; omega
  have hf := hQ.layout.1
  have hjn : first + j * digitSpan c < n := by omega
  have hbeta : ∀ i, i < n → 0 < i → ((digitValueView S (digitSite ring root i)).1 = true ↔
      (first ≤ i ∧ (i - first) % digitSpan c = 0)) := fun i hi h0 => hQ.layout.2.2 i h0 hi
  refine ⟨⟨⟨by omega, hjn, ?_⟩, by omega, by omega, fun hlt => ?_, fun k hk1 hk2 => ?_⟩, by omega⟩
  · have e3 : digitSpan c * j = j * digitSpan c := Nat.mul_comm _ _
    exact (hbeta _ hjn (by omega)).mpr ⟨by omega, by
      rw [show first + j * digitSpan c - first = digitSpan c * j by omega]
      exact Nat.mul_mod_right _ _⟩
  · have e3 : digitSpan c * j = j * digitSpan c := Nat.mul_comm _ _
    have e4 : digitSpan c * (j + 1) = digitSpan c * j + digitSpan c := Nat.mul_succ _ _
    exact (hbeta _ hlt (by omega)).mpr ⟨by omega, by
      rw [show first + j * digitSpan c + digitSpan c - first = digitSpan c * (j + 1) by omega]
      exact Nat.mul_mod_right _ _⟩
  · have e3 : digitSpan c * j = j * digitSpan c := Nat.mul_comm _ _
    have hne : ¬ (first ≤ k ∧ (k - first) % digitSpan c = 0) := by
      rintro ⟨-, hm⟩
      have : k - first = digitSpan c * j + (k - (first + j * digitSpan c)) := by
        omega
      rw [this, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)] at hm
      omega
    cases hb : (digitValueView S (digitSite ring root k)).1
    · rfl
    · exact absurd ((hbeta k (by omega) (by omega)).mp hb) hne

end L3.DigitQuiet
