
import Leader.L4.Height.OverrunChain

namespace L4.Height

open L4.Compiler.Native
open Classical

/-!
# Display deadline counting bound

Paper map:

* `display_depth_budget` is the numerical estimate for the cap-plus-one
  depth `h ≤ m + 233 + 32 * (2^19 * m)` from the reserved frontier.
* `display_deadline_quarter` is the missing-display (missQuarter) estimate
  at the paper deadline `2^29 * L * m`. The three-predecessor recursion and
  uniform conditional service moment are exactly the inputs to
  `clock_mean` (paper Lemma `lem:clock`). Its truncated mean is converted
  by `overrun_of_mean` into the inclusive quarter-tail count.
* The `literal_deadline_split` / raw display split supplies the other
  deterministic half: four times the bad-display count is bounded by the
  total number of words plus four times the missed-cap-plus-one count.
  This module proves that second count is at most one quarter of all words.

The module deliberately leaves the raw suppliers of `hRec`, `hZero`,
`hDepth`, and especially `hMiss` to the physical chart/replay argument.
In the application, `hMiss` is the deterministic implication from an H6 owner whose
lift is at most cap to failure to hit cap+1 by the deadline. The same
historical start, opening, and trace-count witness must be used in the split
and in that implication.

This is an analytic module only. It does not prove raw-row conformance,
historical grant coherence, or the whole G9 composition.
-/

/-- The logarithm of the sixteen-way depth factor is at most four bits
per level. -/
private theorem display_log2_sixteen_pow_le (h : Nat) :
    Nat.log2 (16 ^ h) ≤ 4 * h := by
  have hpow : ∀ j : Nat, 16 ^ j = 2 ^ (4 * j) := by
    intro j
    induction j with
    | zero => decide
    | succ j ih =>
        calc
          16 ^ (j + 1) = 16 ^ j * 16 := Nat.pow_succ 16 j
          _ = 2 ^ (4 * j) * 16 := by rw [ih]
          _ = 2 ^ (4 * j + 4) := by
            rw [Nat.pow_add]
          _ = 2 ^ (4 * (j + 1)) :=
            congrArg (fun q : Nat => 2 ^ q) (by omega)
  have hpos : 0 < 16 ^ h := Nat.pow_pos (by decide)
  have hlt : 16 ^ h < 2 ^ (4 * h + 1) := by
    rw [hpow, Nat.pow_succ]
    have hp : 0 < 2 ^ (4 * h) := Nat.pow_pos (by decide)
    omega
  have hlog : Nat.log2 (16 ^ h) < 4 * h + 1 :=
    (Nat.log2_lt (Nat.ne_of_gt hpos)).2 hlt
  omega

/-- Every member of a list is below its zero-default maximum. -/
private theorem display_le_foldMax (xs : List Nat) (a : Nat)
    (ha : a ∈ xs) : a ≤ Depth.foldMax xs := by
  induction xs with
  | nil =>
      simp at ha
  | cons b bs ih =>
      simp only [List.mem_cons] at ha
      simp only [Depth.foldMax, List.foldr_cons]
      rcases ha with rfl | htail
      · exact Nat.le_max_left _ _
      · exact Nat.le_trans (ih htail) (Nat.le_max_right _ _)

/-- Every site's depth time is bounded by the maximum over the ring. -/
private theorem display_le_clockMaximum {n m : Nat}
    (T : Thru.Word n → Fin m → Nat → Nat)
    (h : Nat) (u : Thru.Word n) (i : Fin m) :
    T u i h ≤ clockMaximum T h u := by
  unfold clockMaximum
  apply display_le_foldMax
  exact List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩

/-- The cap-plus-one depth used by the physical display argument fits the
logarithmic mean coefficient in the clock estimate. -/
theorem display_depth_budget {m h : Nat} (hm : 0 < m)
    (hDepth : h ≤ m + 233 + 32 * (2 ^ 19 * m)) :
    Nat.log2 (m * 3 ^ h) + Nat.log2 (16 ^ h) + 4 ≤ 2 ^ 27 * m := by
  have hpow : 32 * 2 ^ 19 = 2 ^ 24 := by decide
  have hDepth' : h ≤ m + 233 + 2 ^ 24 * m := by
    calc
      h ≤ m + 233 + 32 * (2 ^ 19 * m) := hDepth
      _ = m + 233 + (32 * 2 ^ 19) * m := by
        rw [← Nat.mul_assoc 32 (2 ^ 19) m]
      _ = m + 233 + 2 ^ 24 * m := by rw [hpow]
  have hmLog : Nat.log2 m ≤ m := log2_le_self m (by omega)
  have hthreePos : 1 ≤ 3 ^ h := by
    have hp : 0 < 3 ^ h := Nat.pow_pos (by decide)
    omega
  have hprod := repair_log2_mul_le m (3 ^ h) (by omega) hthreePos
  have hthree := repair_log2_three_pow_le h
  have hsixteen := display_log2_sixteen_pow_le h
  have hlog : Nat.log2 (m * 3 ^ h) ≤ m + 2 * h + 1 := by
    omega
  have hsum :
      Nat.log2 (m * 3 ^ h) + Nat.log2 (16 ^ h) + 4 ≤
        m + 6 * h + 5 := by
    omega
  have hpow24 : 2 ^ 24 = 16777216 := by decide
  have hlin :
      m + 6 * (m + 233 + 2 ^ 24 * m) + 5 ≤
        (6 * 2 ^ 24 + 1410) * m := by
    rw [hpow24]
    omega
  have h6 : 6 * h ≤ 6 * (m + 233 + 2 ^ 24 * m) :=
    Nat.mul_le_mul_left 6 hDepth'
  have hlinear :
      m + 6 * h + 5 ≤ (6 * 2 ^ 24 + 1410) * m := by
    omega
  have hcoeff : 6 * 2 ^ 24 + 1410 ≤ 2 ^ 27 := by
    rw [hpow24]
    decide
  have hfinal :
      (6 * 2 ^ 24 + 1410) * m ≤ 2 ^ 27 * m :=
    Nat.mul_le_mul_right m hcoeff
  exact Nat.le_trans hsum (Nat.le_trans hlinear hfinal)

/-- A uniform service moment and the three-predecessor recursion give a
quarter bound for words on which the cap-plus-one depth is still missed at
the inclusive deadline. A hit exactly at the last letter is intentionally
included in the dominating upper event. -/
theorem display_deadline_quarter {α : Type} {n m : Nat} (hm : 0 < m)
    (next : α → Fin n → α) (x : α)
    (served : Fin m → α → Prop) (L h : Nat)
    (T : List (Fin n) → Fin m → Nat → Nat)
    (miss : List (Fin n) → Prop)
    (hL : 1 ≤ L)
    (hMoment : ∀ i y, Thru.MomentAt next (served i) L y)
    (hRec : ∀ u i d, T u i (d + 1) ≤
      serviceTime next x served u i
        (max (max (T u (left hm i) d) (T u i d)) (T u (right hm i) d)))
    (hZero : ∀ u j, T u j 0 ≤ 0)
    (hDepth : h ≤ m + 233 + 32 * (2 ^ 19 * m))
    (hMiss : ∀ u, u.length = 2 ^ 29 * L * m → miss u →
      ∃ i, u.length ≤ T u i h) :
    4 * wordSum (fun u => if miss u then 1 else 0) (2 ^ 29 * L * m)
      ≤ n ^ (2 ^ 29 * L * m) := by
  classical
  let X : Thru.Word n → Nat := fun u => clockMaximum T h u
  let K : Nat := L * (2 ^ 27 * m)
  let d : Nat := 2 ^ 29 * L * m
  have hBudget := display_depth_budget hm hDepth
  have hMean : ∀ t : Nat,
      wordSum (fun u => Nat.min (X u) t) t ≤ K * n ^ t := by
    intro t
    have hClock := clock_mean hm next x served L hL hMoment T hRec hZero h t
    have hClockWord :
        wordSum (fun u => Nat.min (clockMaximum T h u) t) t ≤
          L * (Nat.log2 (m * 3 ^ h) + Nat.log2 (16 ^ h) + 4) * n ^ t := by
      rw [repair_wordSum_eq_thru
        (fun u => Nat.min (clockMaximum T h u) t) t]
      exact hClock
    change wordSum (fun u => Nat.min (clockMaximum T h u) t) t ≤ K * n ^ t
    calc
      wordSum (fun u => Nat.min (clockMaximum T h u) t) t ≤
          L * (Nat.log2 (m * 3 ^ h) + Nat.log2 (16 ^ h) + 4) * n ^ t :=
        hClockWord
      _ ≤ K * n ^ t := by
        dsimp [K]
        exact Nat.mul_le_mul_right (n ^ t)
          (Nat.mul_le_mul_left L hBudget)
  have hTwo : 0 < 2 ^ 29 := by decide
  have hLpos : 0 < L := by omega
  have hTwoL : 0 < 2 ^ 29 * L := Nat.mul_pos hTwo hLpos
  have hd : 0 < d := by
    dsimp [d]
    exact Nat.mul_pos hTwoL hm
  have hKD : 4 * K ≤ d := by
    dsimp [K, d]
    have hcoeff : 4 * 2 ^ 27 ≤ 2 ^ 29 := by decide
    have hscaled := Nat.mul_le_mul_right (L * m) hcoeff
    calc
      4 * (L * (2 ^ 27 * m)) = (4 * 2 ^ 27) * (L * m) := by ac_rfl
      _ ≤ 2 ^ 29 * (L * m) := hscaled
      _ = 2 ^ 29 * L * m := by ac_rfl
  have hOverrun :
      4 * wordSum (fun u => if d ≤ X u then 1 else 0) d ≤ n ^ d :=
    overrun_of_mean X K d hd hKD hMean
  have hDominates : ∀ u, u.length = d →
      (if miss u then 1 else 0) ≤ (if d ≤ X u then 1 else 0) := by
    intro u hu
    by_cases hmss : miss u
    · have hlen : u.length = d := hu
      obtain ⟨i, hi⟩ := hMiss u (by simpa [d] using hu) hmss
      have hi' : d ≤ T u i h := by
        simpa [hlen] using hi
      have hX : d ≤ X u :=
        Nat.le_trans hi' (display_le_clockMaximum T h u i)
      simp [hmss, hX]
    · simp [hmss]
  have hCount :
      wordSum (fun u => if miss u then 1 else 0) d ≤
        wordSum (fun u => if d ≤ X u then 1 else 0) d :=
    repair_wordSum_mono_length
      (fun u => if miss u then 1 else 0)
      (fun u => if d ≤ X u then 1 else 0) d hDominates
  have hFinal :
      4 * wordSum (fun u => if miss u then 1 else 0) d ≤ n ^ d :=
    Nat.le_trans (Nat.mul_le_mul_left 4 hCount) hOverrun
  simpa [d] using hFinal

#print axioms display_depth_budget
#print axioms display_deadline_quarter

end L4.Height


