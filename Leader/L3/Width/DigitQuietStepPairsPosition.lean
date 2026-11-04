import Leader.L3.Width.DigitQuietStepPairsPipeFin
import Leader.L3.Width.DigitQuietStepPairsJunction

/-!
# One letter at an arbitrary position keeps the pair predicate of a pair of the layout

`pq_after_letter` is the case analysis on the position `p` of the letter relative to the pair
`(first + j R, first + (j + 1) R)`: off the pair (`pq_congr`), at the entry cell (`laneRow_entry_out`),
the pipe letters inside the source block, the junction (DEL) letter, the fin letters inside the
target block and the terminal letter.  It is stated on arbitrary view functions `V`, `V'` related by
the letter, so that the machine only enters through the glue lemmas.

Consumer: `WidthDigitQuietStepPairs` (`QuietPairs` under a letter).
-/

namespace L3.DigitQuiet

open L3

set_option autoImplicit false

variable {c : Compiled}

/-- The marker value of a cell of a block of the layout.  Consumer: `pq_after_letter`. -/
theorem decide_block (R first j h : Nat) (hR : 0 < R) (hh : h < R) :
    decide (first ≤ first + j * R + h ∧ (first + j * R + h - first) % R = 0) = decide (h = 0) := by
  have e : first + j * R + h - first = R * j + h := by rw [Nat.mul_comm R j]; omega
  rw [e, Nat.mul_add_mod, Nat.mod_eq_of_lt hh]
  by_cases h0 : h = 0 <;> simp [h0]

/-- **One letter keeps the pair predicate of a pair of the layout.**  Consumer:
`WidthDigitQuietStepPairs`. -/
theorem pq_after_letter (lane : DigitLane) (R first n j : Nat) (hR : 2 ≤ R) (hf : 2 ≤ first)
    (hjn : first + (j + 2) * R < n) (V V' : Nat → DigitLaneView c) (Dp : Nat → Fin c.topA)
    (p : Nat) (hp : p < n)
    (hL : ∀ q, q < n → (V q).leader = decide (q = 0))
    (hM : ∀ q, 0 < q → q < n → (V q).marker = decide (first ≤ q ∧ (q - first) % R = 0))
    (hS : ∀ h, h < R → (V (first + j * R + h)).digit = Dp h)
    (hT : ∀ h, h < R → ((V (first + (j + 1) * R + h)).digit).val =
      ((Dp h).val + (if carryInto Dp h then 1 else 0)) % c.topA)
    (hother : ∀ q, 0 < q → q < n → q ≠ p → q ≠ p + 1 → V' q = V q)
    (hleft : p + 1 < n → V' p = (laneRow lane (V p) (V (p + 1))).1)
    (hright : p + 1 < n → V' (p + 1) = (laneRow lane (V p) (V (p + 1))).2) :
    PQ R (fun h => V (first + j * R + h)) (fun h => V (first + (j + 1) * R + h)) Dp →
      PQ R (fun h => V' (first + j * R + h)) (fun h => V' (first + (j + 1) * R + h)) Dp := by
  intro hpq
  have e1 : (j + 1) * R = j * R + R := by rw [Nat.add_mul]; omega
  have e2 : (j + 2) * R = j * R + R + R := by rw [Nat.add_mul]; omega
  have hRpos : 0 < R := by omega
  -- the cells of the pair
  have hlead : ∀ q, 0 < q → q < n → (V q).leader = false := fun q h0 hq => by
    rw [hL q hq]; simp; omega
  have hmarkSrc : ∀ h, h < R → (V (first + j * R + h)).marker = decide (h = 0) := by
    intro h hh
    rw [hM _ (by omega) (by omega)]; exact decide_block R first j h hRpos hh
  have hmarkTgt : ∀ h, h < R → (V (first + (j + 1) * R + h)).marker = decide (h = 0) := by
    intro h hh
    rw [hM _ (by omega) (by omega), e1]
    have := decide_block R first (j + 1) h hRpos hh
    rw [e1] at this
    exact this
  have hmarkEnd : (V (first + (j + 2) * R)).marker = true := by
    rw [hM _ (by omega) hjn]
    have : first + (j + 2) * R - first = R * (j + 2) := by rw [Nat.mul_comm R]; omega
    simp only [decide_eq_true_eq]
    exact ⟨by omega, by rw [this]; exact Nat.mul_mod_right _ _⟩
  -- case analysis on the position of the letter
  by_cases c1 : p + 1 < first + j * R
  · -- strictly left of the pair
    refine (pq_congr R _ _ _ _ Dp ?_ ?_).mp hpq
    · intro q hq; rw [hother _ (by omega) (by omega) (by omega) (by omega)]
    · intro q hq
      rw [hother _ (by omega) (by omega) (by omega) (by omega)]
      exact ⟨rfl, rfl, rfl, rfl⟩
  by_cases c2 : p + 1 = first + j * R
  · -- the entry letter: the right cell is the source delimiter, whose out slot is kept
    have hr := hright (by omega)
    have hl0 : (V p).leader = false := hlead p (by omega) (by omega)
    have hl1 : (V (p + 1)).leader = false := hlead (p + 1) (by omega) (by omega)
    have hm1 : (V (p + 1)).marker = true := by
      have := hmarkSrc 0 (by omega)
      rw [← c2] at this
      simpa using this
    have hout := laneRow_entry_out lane (V p) (V (p + 1)) hl0 hl1 hm1
    refine (pq_congr R _ _ _ _ Dp ?_ ?_).mp hpq
    · intro q hq
      by_cases hq0 : q = 0
      · subst hq0
        have : first + j * R + 0 = p + 1 := by omega
        simp only [this, hr]
        exact hout.symm
      · rw [hother _ (by omega) (by omega) (by omega) (by omega)]
    · intro q hq
      rw [hother _ (by omega) (by omega) (by omega) (by omega)]
      exact ⟨rfl, rfl, rfl, rfl⟩
  by_cases c3 : p + 1 < first + j * R + R
  · -- a pipe letter inside the source block
    obtain ⟨h, hh⟩ : ∃ h, p = first + j * R + h := ⟨p - (first + j * R), by omega⟩
    have hhR : h + 1 < R := by omega
    refine (pq_eq_target R (fun q => V' (first + j * R + q)) (fun q => V (first + (j + 1) * R + q))
      (fun q => V' (first + (j + 1) * R + q)) Dp (fun q hq => ?_)).mp ?_
    · exact (hother _ (by omega) (by omega) (by omega) (by omega)).symm
    refine pq_pipe lane R (fun q => V (first + j * R + q)) (fun q => V' (first + j * R + q))
      (fun q => V (first + (j + 1) * R + q)) Dp h hhR ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hpq
    · exact hlead _ (by omega) (by omega)
    · exact hlead _ (by omega) (by omega)
    · exact hmarkSrc h (by omega)
    · rw [show (V (first + j * R + (h + 1))).marker = decide (h + 1 = 0) from
        hmarkSrc (h + 1) hhR]; simp
    · exact hS h (by omega)
    · have e : first + j * R + (h + 1) = p + 1 := by omega
      show V' (first + j * R + h) = (laneRow lane (V (first + j * R + h))
        (V (first + j * R + (h + 1)))).1
      rw [e, ← hh]; exact hleft (by omega)
    · have e : first + j * R + (h + 1) = p + 1 := by omega
      show V' (first + j * R + (h + 1)) = (laneRow lane (V (first + j * R + h))
        (V (first + j * R + (h + 1)))).2
      rw [e, ← hh]; exact hright (by omega)
    · intro q hq h1 h2
      show V' (first + j * R + q) = V (first + j * R + q)
      exact hother _ (by omega) (by omega) (by omega) (by omega)
  by_cases c4 : p + 1 = first + j * R + R
  · -- the junction letter
    have hpR : p = first + j * R + (R - 1) := by omega
    have hr := hright (by omega)
    have hl := hleft (by omega)
    have hp1 : p + 1 = first + (j + 1) * R + 0 := by omega
    refine pq_del lane R hR (fun q => V (first + j * R + q)) (fun q => V' (first + j * R + q))
      (fun q => V (first + (j + 1) * R + q)) (fun q => V' (first + (j + 1) * R + q)) Dp
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hpq
    · exact hlead _ (by omega) (by omega)
    · exact hlead _ (by omega) (by omega)
    · rw [hmarkSrc (R - 1) (by omega)]; simp; omega
    · rw [hmarkTgt 0 (by omega)]; simp
    · exact hS (R - 1) (by omega)
    · have e : first + (j + 1) * R + 0 = p + 1 := by omega
      show V' (first + j * R + (R - 1)) = (laneRow lane (V (first + j * R + (R - 1)))
        (V (first + (j + 1) * R + 0))).1
      rw [e, ← hpR]; exact hl
    · have e : first + (j + 1) * R + 0 = p + 1 := by omega
      show V' (first + (j + 1) * R + 0) = (laneRow lane (V (first + j * R + (R - 1)))
        (V (first + (j + 1) * R + 0))).2
      rw [e, ← hpR]; exact hr
    · intro q hq
      show V' (first + j * R + q) = V (first + j * R + q)
      exact hother _ (by omega) (by omega) (by omega) (by omega)
    · intro q h0 hq
      show V' (first + (j + 1) * R + q) = V (first + (j + 1) * R + q)
      exact hother _ (by omega) (by omega) (by omega) (by omega)
  by_cases c5 : p + 1 < first + (j + 1) * R + R
  · -- a fin letter inside the target block
    obtain ⟨h, hh⟩ : ∃ h, p = first + (j + 1) * R + h := ⟨p - (first + (j + 1) * R), by omega⟩
    have hhR : h + 1 < R := by omega
    refine (pq_eq_source R (fun q => V (first + j * R + q)) (fun q => V' (first + j * R + q))
      (fun q => V' (first + (j + 1) * R + q)) Dp (fun q hq => ?_)).mp ?_
    · exact (hother _ (by omega) (by omega) (by omega) (by omega)).symm
    refine pq_fin lane R (fun q => V (first + j * R + q)) (fun q => V (first + (j + 1) * R + q))
      (fun q => V' (first + (j + 1) * R + q)) Dp h hhR ?_ ?_ ?_ ?_ (hT h (by omega))
      (hT (h + 1) hhR) ?_ ?_ ?_ hpq
    · exact hlead _ (by omega) (by omega)
    · exact hlead _ (by omega) (by omega)
    · exact hmarkTgt h (by omega)
    · rw [show (V (first + (j + 1) * R + (h + 1))).marker = decide (h + 1 = 0) from
        hmarkTgt (h + 1) hhR]; simp
    · have e : first + (j + 1) * R + (h + 1) = p + 1 := by omega
      show V' (first + (j + 1) * R + h) = (laneRow lane (V (first + (j + 1) * R + h))
        (V (first + (j + 1) * R + (h + 1)))).1
      rw [e, ← hh]; exact hleft (by omega)
    · have e : first + (j + 1) * R + (h + 1) = p + 1 := by omega
      show V' (first + (j + 1) * R + (h + 1)) = (laneRow lane (V (first + (j + 1) * R + h))
        (V (first + (j + 1) * R + (h + 1)))).2
      rw [e, ← hh]; exact hright (by omega)
    · intro q hq h1 h2
      show V' (first + (j + 1) * R + q) = V (first + (j + 1) * R + q)
      exact hother _ (by omega) (by omega) (by omega) (by omega)
  by_cases c6 : p + 1 = first + (j + 1) * R + R
  · -- the terminal letter: the right cell is the next delimiter
    have hpR : p = first + (j + 1) * R + (R - 1) := by omega
    have hl := hleft (by omega)
    have hr := hright (by omega)
    refine (pq_eq_source R (fun q => V (first + j * R + q)) (fun q => V' (first + j * R + q))
      (fun q => V' (first + (j + 1) * R + q)) Dp (fun q hq => ?_)).mp ?_
    · exact (hother _ (by omega) (by omega) (by omega) (by omega)).symm
    refine pq_term lane R hR (fun q => V (first + j * R + q)) (fun q => V (first + (j + 1) * R + q))
      (fun q => V' (first + (j + 1) * R + q)) Dp (V (p + 1)) ?_ ?_ ?_ ?_ ?_ ?_ hpq
    · exact hlead _ (by omega) (by omega)
    · exact hlead _ (by omega) (by omega)
    · rw [hmarkTgt (R - 1) (by omega)]; simp; omega
    · have : p + 1 = first + (j + 2) * R := by omega
      rw [this]; exact hmarkEnd
    · show V' (first + (j + 1) * R + (R - 1)) = (laneRow lane (V (first + (j + 1) * R + (R - 1)))
        (V (p + 1))).1
      rw [← hpR]; exact hl
    · intro q hq
      show V' (first + (j + 1) * R + q) = V (first + (j + 1) * R + q)
      exact hother _ (by omega) (by omega) (by omega) (by omega)
  · -- right of the pair: nothing in the pair changes
    refine (pq_congr R _ _ _ _ Dp ?_ ?_).mp hpq
    · intro q hq; rw [hother _ (by omega) (by omega) (by omega) (by omega)]
    · intro q hq
      rw [hother _ (by omega) (by omega) (by omega) (by omega)]
      exact ⟨rfl, rfl, rfl, rfl⟩

end L3.DigitQuiet

#print axioms L3.DigitQuiet.pq_after_letter
