/-!
# Q7 (P.6): the settled-component charge, combinatorial core

For an active-site predicate `a : Nat → Bool` the charge is the sum over maximal active
components `[lo, b]` of `b + 1`; it is computed as the sum over right endpoints `k`
(`a k` and not `a (k+1)`) of `k + 1`.

This module is pure.  It proves that the three local changes of an active set that the
paper uses never raise the charge:

* `charge_cut`: remove a terminal part `[k, b]` of a component (an erasure front at `k`
  dooms the rest of the run, or a carry consumes the last members);
* `charge_drop_left`: remove the left endpoint of a component (a carry consumes it);
* `charge_add_left`: add a new left endpoint next to an active site (a pending packet
  settles to the left of a run; if it merges two components the charge falls).

What is not here: the connection to the cells and the colouring (`colourGen`), the invariants
that exclude a fresh terminal seed, and P.7--P.10.

Consumer: `Leader/L3/TopSettledWork.lean` (not yet written): P.6 monotonicity of `A`.
-/

namespace L3
namespace MarkedCells

set_option autoImplicit false

/-- The charge of the active set `a` on the first `r` sites: the sum of `k + 1` over the
right endpoints `k < r` of active components.

Consumer: `charge_cut`. -/
def charge : Nat → (Nat → Bool) → Nat
  | 0, _ => 0
  | k + 1, a => charge k a + (if a k && !a (k + 1) then k + 1 else 0)

/-- One step of the charge.

Consumer: `charge_cut`. -/
theorem charge_succ (k : Nat) (a : Nat → Bool) :
    charge (k + 1) a = charge k a + (if a k && !a (k + 1) then k + 1 else 0) := rfl

/-- The charge of a prefix depends only on the values up to its length.

Consumer: `charge_cut`. -/
theorem charge_congr (a a' : Nat → Bool) :
    ∀ k, (∀ m, m ≤ k → a m = a' m) → charge k a = charge k a'
  | 0, _ => rfl
  | k + 1, h => by
      simp only [charge]
      rw [charge_congr a a' k (fun m hm => h m (by omega)), h k (by omega), h (k + 1) (by omega)]

/-- Extending the prefix beyond sites where both sets agree adds the same amount.

Consumer: `charge_cut`. -/
theorem charge_same_tail (a a' : Nat → Bool) (b : Nat)
    (hout : ∀ m, b < m → a' m = a m) (h0 : charge (b + 1) a' ≤ charge (b + 1) a) :
    ∀ r, b + 1 ≤ r → charge r a' ≤ charge r a := by
  intro r
  induction r with
  | zero => intro h; omega
  | succ r ih =>
      intro hr
      by_cases hrb : b + 1 ≤ r
      · have := ih hrb
        simp only [charge]
        rw [hout r (by omega), hout (r + 1) (by omega)]
        omega
      · have : r + 1 = b + 1 := by omega
        rw [this]; exact h0

/-- Strict version of `charge_same_tail`.

Consumer: `charge_cut_lt`. -/
theorem charge_same_tail_lt (a a' : Nat → Bool) (b : Nat)
    (hout : ∀ m, b < m → a' m = a m) (h0 : charge (b + 1) a' < charge (b + 1) a) :
    ∀ r, b + 1 ≤ r → charge r a' < charge r a := by
  intro r
  induction r with
  | zero => intro h; omega
  | succ r ih =>
      intro hr
      by_cases hrb : b + 1 ≤ r
      · have := ih hrb
        simp only [charge]
        rw [hout r (by omega), hout (r + 1) (by omega)]
        omega
      · have : r + 1 = b + 1 := by omega
        rw [this]; exact h0

/-- Removing a terminal part `[k, b]` of an active component strictly lowers the charge.

Consumer: `charge_cut_gen_lt`. -/
theorem charge_cut_lt (a a' : Nat → Bool) (k b : Nat) (hkb : k ≤ b)
    (hin : ∀ m, k ≤ m → m ≤ b → a m = true ∧ a' m = false)
    (hout : ∀ m, m < k ∨ b < m → a' m = a m) (hend : a (b + 1) = false) :
    ∀ r, b + 1 ≤ r → charge r a' < charge r a := by
  -- the removed interval contributes nothing to `a'`
  have h1 : ∀ d, k + d ≤ b + 1 → charge (k + d) a' = charge k a' := by
    intro d
    induction d with
    | zero => intro _; rfl
    | succ d ih =>
        intro hj
        have hjb : k + d ≤ b := by omega
        have e : k + (d + 1) = (k + d) + 1 := rfl
        rw [e, charge_succ, ih (by omega), (hin (k + d) (by omega) hjb).2]
        simp
  -- the removed interval contributes `b + 1` to `a`
  have h2 : ∀ d, k + d ≤ b → charge (k + d + 1) a =
      charge k a + (if k + d = b then b + 1 else 0) := by
    intro d
    induction d with
    | zero =>
        intro hj
        simp only [Nat.add_zero]
        rw [charge_succ]
        have hk := (hin k (Nat.le_refl k) hj).1
        by_cases hkb' : k = b
        · subst hkb'
          simp [hk, hend]
        · have : a (k + 1) = true := (hin (k + 1) (by omega) (by omega)).1
          simp [hk, this, hkb']
    | succ d ih =>
        intro hj
        have := ih (by omega)
        have e : k + (d + 1) = (k + d) + 1 := rfl
        rw [e, charge_succ, this]
        have hj1 := (hin (k + d + 1) (by omega) (by omega)).1
        by_cases hjb : k + d + 1 = b
        · have hne : k + d ≠ b := by omega
          have he : a (k + d + 1 + 1) = false := by rw [hjb]; exact hend
          have hb : a b = true := hjb ▸ hj1
          simp [hne, hjb, hb, hend]
        · have hne : k + d ≠ b := by omega
          have : a (k + d + 1 + 1) = true := (hin (k + d + 1 + 1) (by omega) (by omega)).1
          simp [hj1, this, hne, hjb]
  have hk0 : charge k a' ≤ charge k a + k := by
    cases k with
    | zero => simp [charge]
    | succ k' =>
        simp only [charge]
        have e1 := charge_congr a' a k' (fun m hm => hout m (Or.inl (by omega)))
        rw [e1]
        have hk := (hin (k' + 1) (Nat.le_refl _) hkb).2
        by_cases ha : a k' = true
        · simp [hk, hout k' (Or.inl (by omega)), ha]
        · have ha' : a k' = false := by simpa using ha
          simp [hout k' (Or.inl (by omega)), ha']
  have hmain : charge (b + 1) a' < charge (b + 1) a := by
    have e1 := h1 (b + 1 - k) (by omega)
    have e2 := h2 (b - k) (by omega)
    have q1 : k + (b + 1 - k) = b + 1 := by omega
    have q2 : k + (b - k) = b := by omega
    rw [q1] at e1
    rw [q2] at e2
    rw [e1, e2]
    simp
    omega
  exact charge_same_tail_lt a a' b (fun m hm => hout m (Or.inr hm)) hmain

/-- Removing a terminal part `[k, b]` of an active component does not raise the charge.

Consumer: `Leader/L3/TopSettledWork.lean` (front dooms the rest of a run). -/
theorem charge_cut (a a' : Nat → Bool) (k b : Nat) (hkb : k ≤ b)
    (hin : ∀ m, k ≤ m → m ≤ b → a m = true ∧ a' m = false)
    (hout : ∀ m, m < k ∨ b < m → a' m = a m) (hend : a (b + 1) = false) :
    ∀ r, b + 1 ≤ r → charge r a' ≤ charge r a :=
  fun r hr => Nat.le_of_lt (charge_cut_lt a a' k b hkb hin hout hend r hr)

/-- Removing the left endpoint of an active component does not raise the charge.

Consumer: `Leader/L3/TopSettledWork.lean` (a carry consumes the leftmost member). -/
theorem charge_drop_left (a a' : Nat → Bool) (k : Nat)
    (hk : a k = true) (hk' : a' k = false)
    (hleft : ∀ j, j + 1 = k → a j = false)
    (hout : ∀ m, m ≠ k → a' m = a m) :
    ∀ r, k + 1 ≤ r → charge r a' ≤ charge r a := by
  have hbase : charge (k + 1) a' ≤ charge (k + 1) a := by
    have hkk : charge k a' = charge k a := by
      cases k with
      | zero => rfl
      | succ k' =>
          simp only [charge]
          have e1 := charge_congr a' a k' (fun m hm => hout m (by omega))
          have hl := hleft k' rfl
          rw [e1, hout k' (by omega), hl]
          simp
    simp only [charge]
    rw [hkk]
    simp [hk']
  intro r
  induction r with
  | zero => intro h; omega
  | succ r ih =>
      intro hr
      by_cases hrb : k + 1 ≤ r
      · have := ih hrb
        simp only [charge]
        rw [hout r (by omega), hout (r + 1) (by omega)]
        omega
      · have : r + 1 = k + 1 := by omega
        rw [this]; exact hbase

/-- Adding a new left endpoint `k` in front of an active site does not raise the charge
(if `k - 1` is also active the two components merge and the charge falls).

Consumer: `Leader/L3/TopSettledWork.lean` (a pending packet settles to the left of a run). -/
theorem charge_add_left (a a' : Nat → Bool) (k : Nat)
    (hk : a k = false) (hk' : a' k = true) (hnext : a (k + 1) = true)
    (hout : ∀ m, m ≠ k → a' m = a m) :
    ∀ r, k + 1 ≤ r → charge r a' ≤ charge r a := by
  have hbase : charge (k + 1) a' ≤ charge (k + 1) a := by
    have hkk : charge k a' ≤ charge k a := by
      cases k with
      | zero => simp [charge]
      | succ k' =>
          simp only [charge]
          have e1 := charge_congr a' a k' (fun m hm => hout m (by omega))
          rw [e1, hk']
          simp
    have hk1 : a' (k + 1) = true := by rw [hout (k + 1) (by omega)]; exact hnext
    rw [charge_succ, charge_succ]
    simp [hk', hk, hnext, hk1]
    omega
  intro r
  induction r with
  | zero => intro h; omega
  | succ r ih =>
      intro hr
      by_cases hrb : k + 1 ≤ r
      · have := ih hrb
        simp only [charge]
        rw [hout r (by omega), hout (r + 1) (by omega)]
        omega
      · have : r + 1 = k + 1 := by omega
        rw [this]; exact hbase

/-- The contiguous run of active sites starting at an active site has a right end.

Consumer: `charge_cut_gen`. -/
theorem run_end (r : Nat) (a : Nat → Bool) (hbd : ∀ m, r ≤ m → a m = false) :
    ∀ n k, a k = true → r - k ≤ n →
      ∃ b, k ≤ b ∧ (∀ j, k ≤ j → j ≤ b → a j = true) ∧ a (b + 1) = false := by
  intro n
  induction n with
  | zero =>
      intro k hk hn
      have := hbd k (by omega)
      simp [this] at hk
  | succ n ih =>
      intro k hk hn
      by_cases h1 : a (k + 1) = true
      · obtain ⟨b, hb1, hb2, hb3⟩ := ih (k + 1) h1 (by
          by_cases hkr : r ≤ k
          · have := hbd k hkr; simp [this] at hk
          · omega)
        refine ⟨b, by omega, ?_, hb3⟩
        intro j hj1 hj2
        by_cases hjk : j = k
        · subst hjk; exact hk
        · exact hb2 j (by omega) hj2
      · refine ⟨k, Nat.le_refl _, ?_, by simpa using h1⟩
        intro j hj1 hj2
        have : j = k := by omega
        subst this; exact hk

/-- Cutting a whole right part of a run: the site `k` and every later site of its run
become inactive, everything else is unchanged.

Consumer: `Leader/L3/Top/SettledWorkStep.lean`. -/
theorem charge_cut_gen_lt (r : Nat) (a a' : Nat → Bool) (k : Nat)
    (hbd : ∀ m, r ≤ m → a m = false) (hk : a k = true) (hkr : k < r)
    (h1 : ∀ m, m < k → a' m = a m) (h2 : a' k = false)
    (h3 : ∀ m, k < m → (∀ j, k ≤ j → j ≤ m → a j = true) → a' m = false)
    (h4 : ∀ m, k < m → ¬ (∀ j, k ≤ j → j ≤ m → a j = true) → a' m = a m) :
    charge r a' < charge r a := by
  obtain ⟨b, hkb, hrun, hend⟩ := run_end r a hbd (r - k) k hk (Nat.le_refl _)
  have hbr : b + 1 ≤ r := by
    by_cases hcon : b + 1 ≤ r
    · exact hcon
    · have h5 := hbd b (by omega)
      have h6 := hrun b hkb (Nat.le_refl _)
      rw [h5] at h6
      exact absurd h6 (by simp)
  refine charge_cut_lt a a' k b hkb ?_ ?_ hend r hbr
  · intro m hm1 hm2
    refine ⟨hrun m hm1 hm2, ?_⟩
    by_cases hmk : m = k
    · subst hmk; exact h2
    · exact h3 m (by omega) (fun j hj1 hj2 => hrun j hj1 (by omega))
  · intro m hm
    rcases hm with hm | hm
    · exact h1 m hm
    · apply h4 m (by omega)
      intro hall
      have := hall (b + 1) (by omega) (by omega)
      simp_all

/-- Cutting a whole right part of a run does not raise the charge.

Consumer: `Leader/L3/Top/SettledWorkStep.lean`. -/
theorem charge_cut_gen (r : Nat) (a a' : Nat → Bool) (k : Nat)
    (hbd : ∀ m, r ≤ m → a m = false) (hk : a k = true) (hkr : k < r)
    (h1 : ∀ m, m < k → a' m = a m) (h2 : a' k = false)
    (h3 : ∀ m, k < m → (∀ j, k ≤ j → j ≤ m → a j = true) → a' m = false)
    (h4 : ∀ m, k < m → ¬ (∀ j, k ≤ j → j ≤ m → a j = true) → a' m = a m) :
    charge r a' ≤ charge r a :=
  Nat.le_of_lt (charge_cut_gen_lt r a a' k hbd hk hkr h1 h2 h3 h4)

end MarkedCells
end L3

#print axioms L3.MarkedCells.charge_cut_gen
#print axioms L3.MarkedCells.charge_cut
#print axioms L3.MarkedCells.charge_drop_left
#print axioms L3.MarkedCells.charge_add_left
