import Leader.L4.Height.Core

namespace L4.Height.Counting

/-- The `Nat` indicator of a Boolean event. -/
def indicator (b : Bool) : Nat := if b then 1 else 0

/-! Small core-only lemmas for sums of `List.ofFn`. -/

private theorem ofFn_sum_congr :
    ∀ {n : Nat} (f g : Fin n → Nat),
      (∀ i, f i = g i) →
      (List.ofFn f).sum = (List.ofFn g).sum := by
  intro n
  induction n with
  | zero =>
      intro f g h
      simp
  | succ n ih =>
      intro f g h
      simp only [List.ofFn_succ, List.sum_cons]
      rw [h 0]
      exact congrArg (fun z => g 0 + z)
        (ih (fun i => f i.succ) (fun i => g i.succ)
          (fun i => h i.succ))

private theorem ofFn_sum_le :
    ∀ {n : Nat} (f g : Fin n → Nat),
      (∀ i, f i ≤ g i) →
      (List.ofFn f).sum ≤ (List.ofFn g).sum := by
  intro n
  induction n with
  | zero =>
      intro f g h
      simp
  | succ n ih =>
      intro f g h
      simp only [List.ofFn_succ, List.sum_cons]
      exact Nat.add_le_add (h 0)
        (ih (fun i => f i.succ) (fun i => g i.succ)
          (fun i => h i.succ))

private theorem ofFn_sum_add :
    ∀ {n : Nat} (f g : Fin n → Nat),
      (List.ofFn (fun i => f i + g i)).sum =
        (List.ofFn f).sum + (List.ofFn g).sum := by
  intro n
  induction n with
  | zero =>
      intro f g
      simp
  | succ n ih =>
      intro f g
      simp only [List.ofFn_succ, List.sum_cons]
      rw [ih (fun i => f i.succ) (fun i => g i.succ)]
      ac_rfl

private theorem ofFn_sum_mul_left :
    ∀ {n : Nat} (c : Nat) (f : Fin n → Nat),
      (List.ofFn (fun i => c * f i)).sum =
        c * (List.ofFn f).sum := by
  intro n
  induction n with
  | zero =>
      intro c f
      simp
  | succ n ih =>
      intro c f
      simp only [List.ofFn_succ, List.sum_cons]
      rw [ih c (fun i => f i.succ), Nat.mul_add]

private theorem ofFn_sum_mul_right :
    ∀ {n : Nat} (f : Fin n → Nat) (c : Nat),
      (List.ofFn (fun i => f i * c)).sum =
        (List.ofFn f).sum * c := by
  intro n
  induction n with
  | zero =>
      intro f c
      simp
  | succ n ih =>
      intro f c
      simp only [List.ofFn_succ, List.sum_cons]
      rw [ih (fun i => f i.succ) c, Nat.add_mul]

private theorem ofFn_sum_const (n c : Nat) :
    (List.ofFn (fun _ : Fin n => c)).sum = n * c := by
  induction n with
  | zero => simp
  | succ n ih =>
      simp only [List.ofFn_succ, List.sum_cons, ih, Nat.succ_mul]
      ac_rfl

/-- Sum a function over all words of a fixed length. -/
def wordSum {n : Nat} (f : List (Fin n) → Nat) : Nat → Nat
  | 0 => f []
  | k + 1 =>
      (List.ofFn (fun e : Fin n =>
        wordSum (fun v => f (e :: v)) k)).sum

/-- Monotonicity of the uniform word sum. -/
theorem wordSum_mono {n : Nat} (f g : List (Fin n) → Nat) :
    (∀ u, f u ≤ g u) → ∀ k, wordSum f k ≤ wordSum g k := by
  intro h k
  induction k generalizing f g with
  | zero => exact h []
  | succ k ih =>
      simp only [wordSum]
      apply ofFn_sum_le
      intro e
      apply ih
      intro v
      exact h (e :: v)

/-- Additivity of the uniform word sum. -/
theorem wordSum_add_fun {n : Nat}
    (f g : List (Fin n) → Nat) (k : Nat) :
    wordSum (fun u => f u + g u) k = wordSum f k + wordSum g k := by
  induction k generalizing f g with
  | zero => rfl
  | succ k ih =>
      simp only [wordSum]
      calc
        (List.ofFn (fun e : Fin n =>
            wordSum (fun v => f (e :: v) + g (e :: v)) k)).sum =
            (List.ofFn (fun e : Fin n =>
              wordSum (fun v => f (e :: v)) k +
                wordSum (fun v => g (e :: v)) k)).sum := by
              apply ofFn_sum_congr
              intro e
              exact ih (fun v => f (e :: v)) (fun v => g (e :: v))
        _ = (List.ofFn (fun e : Fin n =>
              wordSum (fun v => f (e :: v)) k)).sum +
            (List.ofFn (fun e : Fin n =>
              wordSum (fun v => g (e :: v)) k)).sum :=
              ofFn_sum_add _ _

/-- A constant factor can be pulled through the uniform word sum. -/
theorem wordSum_mul_left {n : Nat} (c : Nat)
    (f : List (Fin n) → Nat) (k : Nat) :
    wordSum (fun u => c * f u) k = c * wordSum f k := by
  induction k generalizing f with
  | zero => rfl
  | succ k ih =>
      simp only [wordSum]
      calc
        (List.ofFn (fun e : Fin n =>
            wordSum (fun v => c * f (e :: v)) k)).sum =
            (List.ofFn (fun e : Fin n =>
              c * wordSum (fun v => f (e :: v)) k)).sum := by
              apply ofFn_sum_congr
              intro e
              exact ih (fun v => f (e :: v))
        _ = c * (List.ofFn (fun e : Fin n =>
              wordSum (fun v => f (e :: v)) k)).sum :=
              ofFn_sum_mul_left c _

/-- There are exactly `n^k` words of length `k`. -/
theorem wordSum_const_one {n : Nat} (k : Nat) :
    wordSum (fun _ : List (Fin n) => 1) k = n ^ k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      simp only [wordSum]
      calc
        (List.ofFn (fun _ : Fin n =>
            wordSum (fun _ : List (Fin n) => 1) k)).sum =
            (List.ofFn (fun _ : Fin n => n ^ k)).sum := by
              apply ofFn_sum_congr
              intro e
              exact ih
        _ = n * n ^ k := ofFn_sum_const n (n ^ k)
        _ = n ^ (k + 1) := by
              rw [Nat.pow_succ]
              ac_rfl

/-- Constant functions sum to the constant times the number of words. -/
theorem wordSum_const {n : Nat} (c k : Nat) :
    wordSum (fun _ : List (Fin n) => c) k = c * n ^ k := by
  calc
    wordSum (fun _ : List (Fin n) => c) k =
        wordSum (fun _ : List (Fin n) => c * 1) k := by
          apply congrArg (fun f : List (Fin n) → Nat => wordSum f k)
          funext u
          exact (Nat.mul_one c).symm
    _ = c * wordSum (fun _ : List (Fin n) => 1) k :=
      wordSum_mul_left c (fun _ : List (Fin n) => 1) k
    _ = c * n ^ k := by rw [wordSum_const_one]

private def finSum {n : Nat} (f : Fin n → Nat) : Nat :=
  (List.ofFn f).sum

private theorem finSum_succ {n : Nat} (f : Fin (n + 1) → Nat) :
    finSum f = f 0 + finSum (fun i : Fin n => f i.succ) := by
  simp only [finSum, List.ofFn_succ, List.sum_cons]

private theorem finSum_ext {n : Nat} (f g : Fin n → Nat)
    (h : ∀ i, f i = g i) : finSum f = finSum g := by
  unfold finSum
  exact ofFn_sum_congr f g h

private theorem finSum_zero {n : Nat} :
    finSum (fun _ : Fin n => 0) = 0 := by
  unfold finSum
  simpa using ofFn_sum_const n 0

private theorem finSum_const_one {n : Nat} :
    finSum (fun _ : Fin n => 1) = n := by
  unfold finSum
  simpa using ofFn_sum_const n 1

private theorem finSum_mul_right {n : Nat}
    (f : Fin n → Nat) (c : Nat) :
    finSum (fun i => f i * c) = finSum f * c := by
  unfold finSum
  exact ofFn_sum_mul_right f c

private theorem finSum_cast {a b : Nat} (h : a = b)
    (f : Fin b → Nat) :
    finSum (fun i : Fin a => f (Fin.cast h i)) = finSum f := by
  cases h
  apply finSum_ext
  intro i
  rfl

private theorem powTwoSplit (m : Nat) :
    2 ^ m + 2 ^ m = 2 ^ (m + 1) := by
  rw [Nat.pow_succ]
  omega

private def lowerLetter {m : Nat}
    (e : Fin (2 ^ m)) : Fin (2 ^ (m + 1)) :=
  Fin.cast (powTwoSplit m)
    (e.castLE (Nat.le_add_right (2 ^ m) (2 ^ m)))

private def upperLetter {m : Nat}
    (e : Fin (2 ^ m)) : Fin (2 ^ (m + 1)) :=
  Fin.cast (powTwoSplit m) (e.natAdd (2 ^ m))

private theorem finSum_pow_two_split (m : Nat)
    (f : Fin (2 ^ (m + 1)) → Nat) :
    finSum f =
      finSum (fun e : Fin (2 ^ m) => f (lowerLetter e)) +
      finSum (fun e : Fin (2 ^ m) => f (upperLetter e)) := by
  calc
    finSum f =
        finSum (fun z : Fin (2 ^ m + 2 ^ m) =>
          f (Fin.cast (powTwoSplit m) z)) :=
            (finSum_cast (powTwoSplit m) f).symm
    _ = finSum (fun e : Fin (2 ^ m) => f (lowerLetter e)) +
        finSum (fun e : Fin (2 ^ m) => f (upperLetter e)) := by
          unfold finSum
          rw [List.ofFn_add, List.sum_append]
          rfl

private theorem bitsOf_lower_small {m : Nat}
    (e : Fin (2 ^ m)) (i : Fin (m + 1)) (hi : i.val < m) :
    bitsOf (lowerLetter e) i = bitsOf e ⟨i.val, hi⟩ := by
  rfl

private theorem bitsOf_lower_top {m : Nat}
    (e : Fin (2 ^ m)) (i : Fin (m + 1)) (hi : ¬ i.val < m) :
    bitsOf (lowerLetter e) i = false := by
  have heq : i.val = m := by omega
  change e.val.testBit i.val = false
  rw [heq]
  exact Nat.testBit_lt_two_pow e.isLt

private theorem bitsOf_upper_small {m : Nat}
    (e : Fin (2 ^ m)) (i : Fin (m + 1)) (hi : i.val < m) :
    bitsOf (upperLetter e) i = bitsOf e ⟨i.val, hi⟩ := by
  change (2 ^ m + e.val).testBit i.val = e.val.testBit i.val
  exact Nat.testBit_two_pow_add_gt hi e.val

private theorem bitsOf_upper_top {m : Nat}
    (e : Fin (2 ^ m)) (i : Fin (m + 1)) (hi : ¬ i.val < m) :
    bitsOf (upperLetter e) i = true := by
  have heq : i.val = m := by omega
  change (2 ^ m + e.val).testBit i.val = true
  rw [heq, Nat.testBit_two_pow_add_eq]
  rw [Nat.testBit_lt_two_pow e.isLt]
  rfl

abbrev LetterRequirement (m : Nat) := Fin m × Bool

private def letterKey {m : Nat} (q : LetterRequirement m) : Nat :=
  q.1.val

/-- No bit index occurs twice in a one-letter prescription. -/
def LetterDistinct {m : Nat} (qs : List (LetterRequirement m)) : Prop :=
  (qs.map letterKey).Nodup

/-- A letter satisfies all prescribed bit values. -/
def letterPrescribed {m : Nat}
    (qs : List (LetterRequirement m)) (e : Fin (2 ^ m)) : Bool :=
  qs.all (fun q => decide (bitsOf e q.1 = q.2))

/-- Number of letters satisfying a one-letter prescription. -/
def letterCount {m : Nat} (qs : List (LetterRequirement m)) : Nat :=
  finSum (fun e : Fin (2 ^ m) => indicator (letterPrescribed qs e))

private def lowerLetterRequirements {m : Nat} :
    List (LetterRequirement (m + 1)) → List (LetterRequirement m)
  | [] => []
  | q :: qs =>
      if h : q.1.val < m then
        (⟨q.1.val, h⟩, q.2) :: lowerLetterRequirements qs
      else
        lowerLetterRequirements qs

private def topLetterValues {m : Nat} :
    List (LetterRequirement (m + 1)) → List Bool
  | [] => []
  | q :: qs =>
      if q.1.val < m then
        topLetterValues qs
      else
        q.2 :: topLetterValues qs

private def topSatisfied (b : Bool) (vs : List Bool) : Bool :=
  vs.all (fun v => decide (b = v))

private theorem bool_and_assoc_reverse (a b c : Bool) :
    (a && (b && c)) = ((a && b) && c) := by
  cases a <;> cases b <;> cases c <;> rfl

private theorem bool_and_rotate (a b c : Bool) :
    (a && (b && c)) = (b && (a && c)) := by
  cases a <;> cases b <;> cases c <;> rfl

private theorem letter_split_length {m : Nat}
    (qs : List (LetterRequirement (m + 1))) :
    (lowerLetterRequirements qs).length +
      (topLetterValues qs).length = qs.length := by
  induction qs with
  | nil => rfl
  | cons q qs ih =>
      by_cases h : q.1.val < m
      · simp only [lowerLetterRequirements, dif_pos h,
          topLetterValues, if_pos h, List.length_cons]
        omega
      · simp only [lowerLetterRequirements, dif_neg h,
          topLetterValues, if_neg h, List.length_cons]
        omega

private theorem lower_letter_key_origin {m : Nat}
    {qs : List (LetterRequirement (m + 1))} {j : Nat}
    (hj : j ∈ (lowerLetterRequirements qs).map letterKey) :
    ∃ q ∈ qs, q.1.val < m ∧ q.1.val = j := by
  induction qs with
  | nil =>
      simp [lowerLetterRequirements] at hj
  | cons q qs ih =>
      by_cases h : q.1.val < m
      · have hj' :
            j = letterKey (⟨q.1.val, h⟩, q.2) ∨
              j ∈ (lowerLetterRequirements qs).map letterKey := by
          simpa only [lowerLetterRequirements, dif_pos h,
            List.map_cons, List.mem_cons] using hj
        rcases hj' with hhead | htail
        · refine ⟨q, List.mem_cons_self, h, ?_⟩
          simpa only [letterKey] using hhead.symm
        · obtain ⟨q', hq', hsmall, hval⟩ := ih htail
          exact ⟨q', List.mem_cons_of_mem q hq', hsmall, hval⟩
      · have htail :
            j ∈ (lowerLetterRequirements qs).map letterKey := by
          simpa only [lowerLetterRequirements, dif_neg h] using hj
        obtain ⟨q', hq', hsmall, hval⟩ := ih htail
        exact ⟨q', List.mem_cons_of_mem q hq', hsmall, hval⟩

private theorem top_letter_origin {m : Nat}
    {qs : List (LetterRequirement (m + 1))} {b : Bool}
    (hb : b ∈ topLetterValues qs) :
    ∃ q ∈ qs, ¬ q.1.val < m ∧ q.2 = b := by
  induction qs with
  | nil =>
      simp [topLetterValues] at hb
  | cons q qs ih =>
      by_cases h : q.1.val < m
      · have htail : b ∈ topLetterValues qs := by
          simpa only [topLetterValues, if_pos h] using hb
        obtain ⟨q', hq', hlarge, hval⟩ := ih htail
        exact ⟨q', List.mem_cons_of_mem q hq', hlarge, hval⟩
      · have hb' : b = q.2 ∨ b ∈ topLetterValues qs := by
          simpa only [topLetterValues, if_neg h, List.mem_cons] using hb
        rcases hb' with hhead | htail
        · exact ⟨q, List.mem_cons_self, h, hhead.symm⟩
        · obtain ⟨q', hq', hlarge, hval⟩ := ih htail
          exact ⟨q', List.mem_cons_of_mem q hq', hlarge, hval⟩

private theorem lower_letter_distinct {m : Nat}
    (qs : List (LetterRequirement (m + 1)))
    (hd : LetterDistinct qs) :
    LetterDistinct (lowerLetterRequirements qs) := by
  induction qs with
  | nil => simp [LetterDistinct, lowerLetterRequirements]
  | cons q qs ih =>
      unfold LetterDistinct at hd ⊢
      simp only [List.map_cons] at hd
      have hnot := (List.nodup_cons.mp hd).1
      have htail := (List.nodup_cons.mp hd).2
      have htailDistinct : LetterDistinct qs := htail
      by_cases h : q.1.val < m
      · simp only [lowerLetterRequirements, dif_pos h, List.map_cons]
        apply List.nodup_cons.mpr
        constructor
        · intro hj
          obtain ⟨q', hq', hsmall, hval⟩ :=
            lower_letter_key_origin hj
          apply hnot
          apply List.mem_map.mpr
          refine ⟨q', hq', ?_⟩
          simp only [letterKey] at hval ⊢
          exact hval
        · exact ih htailDistinct
      · simp only [lowerLetterRequirements, dif_neg h]
        exact ih htailDistinct

private theorem top_letter_values_length_le_one {m : Nat}
    (qs : List (LetterRequirement (m + 1)))
    (hd : LetterDistinct qs) :
    (topLetterValues qs).length ≤ 1 := by
  induction qs with
  | nil => simp [topLetterValues]
  | cons q qs ih =>
      unfold LetterDistinct at hd
      simp only [List.map_cons] at hd
      have hnot := (List.nodup_cons.mp hd).1
      have htail := (List.nodup_cons.mp hd).2
      have htailDistinct : LetterDistinct qs := htail
      by_cases h : q.1.val < m
      · simp only [topLetterValues, if_pos h]
        exact ih htailDistinct
      · have hempty : topLetterValues qs = [] := by
          cases ht : topLetterValues qs with
          | nil => rfl
          | cons b bs =>
              have hb : b ∈ topLetterValues qs := by
                rw [ht]
                exact List.mem_cons_self
              obtain ⟨q', hq', hlarge, hval⟩ := top_letter_origin hb
              have hsite : q'.1.val = q.1.val := by
                have hq := q.1.isLt
                have hq' := q'.1.isLt
                omega
              exfalso
              apply hnot
              apply List.mem_map.mpr
              refine ⟨q', hq', ?_⟩
              simp only [letterKey]
              exact hsite
        simp only [topLetterValues, if_neg h, hempty,
          List.length_cons, List.length_nil]
        omega

private theorem letterPrescribed_lower {m : Nat}
    (qs : List (LetterRequirement (m + 1)))
    (e : Fin (2 ^ m)) :
    letterPrescribed qs (lowerLetter e) =
      (letterPrescribed (lowerLetterRequirements qs) e &&
        topSatisfied false (topLetterValues qs)) := by
  induction qs with
  | nil => rfl
  | cons q qs ih =>
      by_cases h : q.1.val < m
      · have hb := bitsOf_lower_small e q.1 h
        simp only [lowerLetterRequirements, dif_pos h,
          topLetterValues, if_pos h]
        change
          (decide (bitsOf (lowerLetter e) q.1 = q.2) &&
            letterPrescribed qs (lowerLetter e)) =
          ((decide (bitsOf e ⟨q.1.val, h⟩ = q.2) &&
            letterPrescribed (lowerLetterRequirements qs) e) &&
            topSatisfied false (topLetterValues qs))
        rw [hb, ih]
        exact bool_and_assoc_reverse _ _ _
      · have hb := bitsOf_lower_top e q.1 h
        simp only [lowerLetterRequirements, dif_neg h,
          topLetterValues, if_neg h]
        change
          (decide (bitsOf (lowerLetter e) q.1 = q.2) &&
            letterPrescribed qs (lowerLetter e)) =
          (letterPrescribed (lowerLetterRequirements qs) e &&
            (decide (false = q.2) &&
              topSatisfied false (topLetterValues qs)))
        rw [hb, ih]
        exact bool_and_rotate _ _ _

private theorem letterPrescribed_upper {m : Nat}
    (qs : List (LetterRequirement (m + 1)))
    (e : Fin (2 ^ m)) :
    letterPrescribed qs (upperLetter e) =
      (letterPrescribed (lowerLetterRequirements qs) e &&
        topSatisfied true (topLetterValues qs)) := by
  induction qs with
  | nil => rfl
  | cons q qs ih =>
      by_cases h : q.1.val < m
      · have hb := bitsOf_upper_small e q.1 h
        simp only [lowerLetterRequirements, dif_pos h,
          topLetterValues, if_pos h]
        change
          (decide (bitsOf (upperLetter e) q.1 = q.2) &&
            letterPrescribed qs (upperLetter e)) =
          ((decide (bitsOf e ⟨q.1.val, h⟩ = q.2) &&
            letterPrescribed (lowerLetterRequirements qs) e) &&
            topSatisfied true (topLetterValues qs))
        rw [hb, ih]
        exact bool_and_assoc_reverse _ _ _
      · have hb := bitsOf_upper_top e q.1 h
        simp only [lowerLetterRequirements, dif_neg h,
          topLetterValues, if_neg h]
        change
          (decide (bitsOf (upperLetter e) q.1 = q.2) &&
            letterPrescribed qs (upperLetter e)) =
          (letterPrescribed (lowerLetterRequirements qs) e &&
            (decide (true = q.2) &&
              topSatisfied true (topLetterValues qs)))
        rw [hb, ih]
        exact bool_and_rotate _ _ _

private theorem letterCount_split {m : Nat}
    (qs : List (LetterRequirement (m + 1))) :
    letterCount qs =
      finSum (fun e : Fin (2 ^ m) =>
        indicator
          (letterPrescribed (lowerLetterRequirements qs) e &&
            topSatisfied false (topLetterValues qs))) +
      finSum (fun e : Fin (2 ^ m) =>
        indicator
          (letterPrescribed (lowerLetterRequirements qs) e &&
            topSatisfied true (topLetterValues qs))) := by
  unfold letterCount
  rw [finSum_pow_two_split]
  simp only [letterPrescribed_lower, letterPrescribed_upper]

/-- `K` distinct prescribed bits of one `m`-bit letter have weight `2^-K`. -/
theorem one_letter_prescribed_count :
    ∀ {m : Nat} (qs : List (LetterRequirement m)),
      LetterDistinct qs →
      2 ^ qs.length * letterCount qs = 2 ^ m := by
  intro m
  induction m with
  | zero =>
      intro qs hd
      cases qs with
      | nil =>
          simp [letterCount, letterPrescribed, indicator,
            finSum_const_one]
      | cons q qs =>
          exact Fin.elim0 q.1
  | succ m ih =>
      intro qs hd
      let lower := lowerLetterRequirements qs
      have hlower : LetterDistinct lower :=
        lower_letter_distinct qs hd
      have hind := ih lower hlower
      have hlen := letter_split_length qs
      change lower.length + (topLetterValues qs).length = qs.length at hlen
      have htopBound := top_letter_values_length_le_one qs hd
      have hsplit := letterCount_split qs
      cases htop : topLetterValues qs with
      | nil =>
          have hqLen : qs.length = lower.length := by
            rw [htop] at hlen
            simp only [List.length_nil, Nat.add_zero] at hlen
            exact hlen.symm
          have hcount :
              letterCount qs = letterCount lower + letterCount lower := by
            rw [htop] at hsplit
            have hfalse : topSatisfied false [] = true := rfl
            have htrue : topSatisfied true [] = true := rfl
            rw [hfalse, htrue] at hsplit
            simp only [Bool.and_true] at hsplit
            change letterCount qs = letterCount lower + letterCount lower at hsplit
            exact hsplit
          rw [hqLen, hcount]
          calc
            2 ^ lower.length *
                (letterCount lower + letterCount lower) =
                (2 ^ lower.length * letterCount lower) * 2 := by
                  rw [Nat.mul_add, Nat.mul_two]
            _ = 2 ^ m * 2 := by rw [hind]
            _ = 2 ^ (m + 1) := by rw [Nat.pow_succ]
      | cons b rest =>
          cases rest with
          | nil =>
              have hqLen : qs.length = lower.length + 1 := by
                rw [htop] at hlen
                simp only [List.length_cons, List.length_nil] at hlen
                exact hlen.symm
              have hcount : letterCount qs = letterCount lower := by
                rw [htop] at hsplit
                cases b <;>
                  simpa [lower, topSatisfied, letterCount, indicator,
                    finSum_zero] using hsplit
              rw [hqLen, hcount]
              calc
                2 ^ (lower.length + 1) * letterCount lower =
                    (2 ^ lower.length * letterCount lower) * 2 := by
                      rw [Nat.pow_succ]
                      ac_rfl
                _ = 2 ^ m * 2 := by rw [hind]
                _ = 2 ^ (m + 1) := by rw [Nat.pow_succ]
          | cons b' rest =>
              have htwo : 2 ≤ (topLetterValues qs).length := by
                rw [htop]
                simp
              omega

/-- A prescribed source coordinate: round, site, and desired value. -/
structure BitRequirement (m : Nat) where
  round : Nat
  site : Fin m
  value : Bool
deriving DecidableEq, Repr

private def requirementKey {m : Nat} (p : BitRequirement m) : Nat × Nat :=
  (p.round, p.site.val)

/-- No `(round, site)` pair occurs twice. -/
def RequirementsDistinct {m : Nat}
    (ps : List (BitRequirement m)) : Prop :=
  (ps.map requirementKey).Nodup

/-- Every prescribed round lies in the word. -/
def RequirementsInRange {m : Nat}
    (w : Nat) (ps : List (BitRequirement m)) : Prop :=
  ∀ p, p ∈ ps → p.round < w

private def listAt? {α : Type} : List α → Nat → Option α
  | [], _ => none
  | x :: _, 0 => some x
  | _ :: xs, k + 1 => listAt? xs k

private def requirementHolds {m : Nat}
    (p : BitRequirement m) (u : List (Fin (2 ^ m))) : Bool :=
  match listAt? u p.round with
  | none => false
  | some e => decide (bitsOf e p.site = p.value)

private theorem requirementHolds_cons_zero {m : Nat}
    (p : BitRequirement m) (e : Fin (2 ^ m))
    (u : List (Fin (2 ^ m))) (h : p.round = 0) :
    requirementHolds p (e :: u) =
      decide (bitsOf e p.site = p.value) := by
  unfold requirementHolds
  rw [h]
  rfl

private theorem requirementHolds_cons_succ {m r : Nat}
    (p : BitRequirement m) (e : Fin (2 ^ m))
    (u : List (Fin (2 ^ m))) (h : p.round = r + 1) :
    requirementHolds p (e :: u) =
      requirementHolds
        { round := r, site := p.site, value := p.value } u := by
  unfold requirementHolds
  rw [h]
  rfl

/-- A word satisfies all prescribed coordinates. -/
def prescribed {m : Nat}
    (ps : List (BitRequirement m))
    (u : List (Fin (2 ^ m))) : Bool :=
  ps.all (fun p => requirementHolds p u)

private def firstLetterRequirements {m : Nat} :
    List (BitRequirement m) → List (LetterRequirement m)
  | [] => []
  | p :: ps =>
      match p.round with
      | 0 => (p.site, p.value) :: firstLetterRequirements ps
      | _ + 1 => firstLetterRequirements ps

private def laterRequirements {m : Nat} :
    List (BitRequirement m) → List (BitRequirement m)
  | [] => []
  | p :: ps =>
      match p.round with
      | 0 => laterRequirements ps
      | r + 1 =>
          { round := r, site := p.site, value := p.value } ::
            laterRequirements ps

private theorem requirements_split_length {m : Nat}
    (ps : List (BitRequirement m)) :
    (firstLetterRequirements ps).length +
      (laterRequirements ps).length = ps.length := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
      cases hround : p.round with
      | zero =>
          simp only [firstLetterRequirements, laterRequirements, hround,
            List.length_cons]
          omega
      | succ r =>
          simp only [firstLetterRequirements, laterRequirements, hround,
            List.length_cons]
          omega

private theorem first_key_origin {m : Nat}
    {ps : List (BitRequirement m)} {j : Nat}
    (hj : j ∈ (firstLetterRequirements ps).map letterKey) :
    ∃ p ∈ ps, p.round = 0 ∧ p.site.val = j := by
  induction ps with
  | nil =>
      simp [firstLetterRequirements] at hj
  | cons p ps ih =>
      cases hround : p.round with
      | zero =>
          have hj' :
              j = letterKey (p.site, p.value) ∨
                j ∈ (firstLetterRequirements ps).map letterKey := by
            simpa only [firstLetterRequirements, hround, List.map_cons,
              List.mem_cons] using hj
          rcases hj' with hhead | htail
          · refine ⟨p, List.mem_cons_self, hround, ?_⟩
            simpa only [letterKey] using hhead.symm
          · obtain ⟨q, hq, hz, hs⟩ := ih htail
            exact ⟨q, List.mem_cons_of_mem p hq, hz, hs⟩
      | succ r =>
          have htail :
              j ∈ (firstLetterRequirements ps).map letterKey := by
            simpa only [firstLetterRequirements, hround] using hj
          obtain ⟨q, hq, hz, hs⟩ := ih htail
          exact ⟨q, List.mem_cons_of_mem p hq, hz, hs⟩

private theorem later_key_origin {m : Nat}
    {ps : List (BitRequirement m)} {key : Nat × Nat}
    (hk : key ∈ (laterRequirements ps).map requirementKey) :
    ∃ p ∈ ps, 0 < p.round ∧
      (p.round - 1, p.site.val) = key := by
  induction ps with
  | nil =>
      simp [laterRequirements] at hk
  | cons p ps ih =>
      cases hround : p.round with
      | zero =>
          have htail :
              key ∈ (laterRequirements ps).map requirementKey := by
            simpa only [laterRequirements, hround] using hk
          obtain ⟨q, hq, hpos, hkey⟩ := ih htail
          exact ⟨q, List.mem_cons_of_mem p hq, hpos, hkey⟩
      | succ r =>
          have hk' :
              key = requirementKey
                { round := r, site := p.site, value := p.value } ∨
              key ∈ (laterRequirements ps).map requirementKey := by
            simpa only [laterRequirements, hround, List.map_cons,
              List.mem_cons] using hk
          rcases hk' with hhead | htail
          · refine ⟨p, List.mem_cons_self, by omega, ?_⟩
            rw [hround]
            have hr : r + 1 - 1 = r := by omega
            rw [hr]
            simpa only [requirementKey] using hhead.symm
          · obtain ⟨q, hq, hpos, hkey⟩ := ih htail
            exact ⟨q, List.mem_cons_of_mem p hq, hpos, hkey⟩

private theorem first_requirements_distinct {m : Nat}
    (ps : List (BitRequirement m))
    (hd : RequirementsDistinct ps) :
    LetterDistinct (firstLetterRequirements ps) := by
  induction ps with
  | nil => simp [RequirementsDistinct, LetterDistinct,
      firstLetterRequirements]
  | cons p ps ih =>
      unfold RequirementsDistinct at hd
      simp only [List.map_cons] at hd
      have hnot := (List.nodup_cons.mp hd).1
      have htail := (List.nodup_cons.mp hd).2
      have htailDistinct : RequirementsDistinct ps := htail
      cases hround : p.round with
      | zero =>
          unfold LetterDistinct
          simp only [firstLetterRequirements, hround, List.map_cons]
          apply List.nodup_cons.mpr
          constructor
          · intro hj
            obtain ⟨q, hq, hz, hs⟩ := first_key_origin hj
            apply hnot
            apply List.mem_map.mpr
            refine ⟨q, hq, ?_⟩
            show requirementKey q = requirementKey p
            unfold requirementKey
            apply Prod.ext
            · change q.round = p.round
              exact hz.trans hround.symm
            · change q.site.val = p.site.val
              exact hs
          · exact ih htailDistinct
      | succ r =>
          simp only [firstLetterRequirements, hround]
          exact ih htailDistinct

private theorem later_requirements_distinct {m : Nat}
    (ps : List (BitRequirement m))
    (hd : RequirementsDistinct ps) :
    RequirementsDistinct (laterRequirements ps) := by
  induction ps with
  | nil => simp [RequirementsDistinct, laterRequirements]
  | cons p ps ih =>
      unfold RequirementsDistinct at hd
      simp only [List.map_cons] at hd
      have hnot := (List.nodup_cons.mp hd).1
      have htail := (List.nodup_cons.mp hd).2
      have htailDistinct : RequirementsDistinct ps := htail
      cases hround : p.round with
      | zero =>
          unfold RequirementsDistinct
          simp only [laterRequirements, hround]
          exact ih htailDistinct
      | succ r =>
          unfold RequirementsDistinct
          simp only [laterRequirements, hround, List.map_cons]
          apply List.nodup_cons.mpr
          constructor
          · intro hmem
            change (r, p.site.val) ∈
              (laterRequirements ps).map requirementKey at hmem
            obtain ⟨q, hq, hpos, hkey⟩ := later_key_origin hmem
            have hsub : q.round - 1 = r := congrArg Prod.fst hkey
            have hsite : q.site.val = p.site.val := congrArg Prod.snd hkey
            have hroundEq : q.round = r + 1 := by omega
            apply hnot
            apply List.mem_map.mpr
            refine ⟨q, hq, ?_⟩
            show requirementKey q = requirementKey p
            unfold requirementKey
            apply Prod.ext
            · change q.round = p.round
              exact hroundEq.trans hround.symm
            · change q.site.val = p.site.val
              exact hsite
          · exact ih htailDistinct

private theorem later_requirements_in_range {m w : Nat}
    {ps : List (BitRequirement m)}
    (hrange : RequirementsInRange (w + 1) ps) :
    RequirementsInRange w (laterRequirements ps) := by
  intro q hq
  have hmem : requirementKey q ∈
      (laterRequirements ps).map requirementKey :=
    List.mem_map.mpr ⟨q, hq, rfl⟩
  obtain ⟨p, hp, hpos, hkey⟩ := later_key_origin hmem
  have hsub := congrArg Prod.fst hkey
  simp only [requirementKey] at hsub
  have hpw := hrange p hp
  omega

private theorem requirements_in_range_zero_nil {m : Nat}
    {ps : List (BitRequirement m)}
    (hrange : RequirementsInRange 0 ps) : ps = [] := by
  cases ps with
  | nil => rfl
  | cons p ps =>
      have hp := hrange p List.mem_cons_self
      omega

private theorem prescribed_cons {m : Nat}
    (ps : List (BitRequirement m))
    (e : Fin (2 ^ m)) (u : List (Fin (2 ^ m))) :
    prescribed ps (e :: u) =
      (letterPrescribed (firstLetterRequirements ps) e &&
        prescribed (laterRequirements ps) u) := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
      cases hround : p.round with
      | zero =>
          simp only [firstLetterRequirements, laterRequirements, hround]
          change
            (requirementHolds p (e :: u) && prescribed ps (e :: u)) =
            ((decide (bitsOf e p.site = p.value) &&
              letterPrescribed (firstLetterRequirements ps) e) &&
              prescribed (laterRequirements ps) u)
          rw [requirementHolds_cons_zero p e u hround, ih]
          exact bool_and_assoc_reverse _ _ _
      | succ r =>
          simp only [firstLetterRequirements, laterRequirements, hround]
          change
            (requirementHolds p (e :: u) && prescribed ps (e :: u)) =
            (letterPrescribed (firstLetterRequirements ps) e &&
              (requirementHolds
                  { round := r, site := p.site, value := p.value } u &&
                prescribed (laterRequirements ps) u))
          rw [requirementHolds_cons_succ p e u hround, ih]
          exact bool_and_rotate _ _ _

private theorem indicator_and (a b : Bool) :
    indicator (a && b) = indicator a * indicator b := by
  cases a <;> cases b <;> rfl

private theorem wordSum_prescribed_succ {m w : Nat}
    (ps : List (BitRequirement m)) :
    wordSum (fun u => indicator (prescribed ps u)) (w + 1) =
      letterCount (firstLetterRequirements ps) *
        wordSum (fun u => indicator (prescribed (laterRequirements ps) u)) w := by
  have hinner (e : Fin (2 ^ m)) :
      wordSum (fun v => indicator (prescribed ps (e :: v))) w =
        indicator (letterPrescribed (firstLetterRequirements ps) e) *
          wordSum
            (fun v => indicator (prescribed (laterRequirements ps) v)) w := by
    calc
      wordSum (fun v => indicator (prescribed ps (e :: v))) w =
          wordSum
            (fun v => indicator
              (letterPrescribed (firstLetterRequirements ps) e &&
                prescribed (laterRequirements ps) v)) w := by
            apply congrArg
              (fun f : List (Fin (2 ^ m)) → Nat => wordSum f w)
            funext v
            rw [prescribed_cons]
      _ = wordSum
            (fun v =>
              indicator (letterPrescribed (firstLetterRequirements ps) e) *
                indicator (prescribed (laterRequirements ps) v)) w := by
            apply congrArg
              (fun f : List (Fin (2 ^ m)) → Nat => wordSum f w)
            funext v
            exact indicator_and _ _
      _ = indicator (letterPrescribed (firstLetterRequirements ps) e) *
            wordSum
              (fun v => indicator (prescribed (laterRequirements ps) v)) w :=
            wordSum_mul_left _ _ _
  simp only [wordSum]
  change
    finSum (fun e : Fin (2 ^ m) =>
      wordSum (fun v => indicator (prescribed ps (e :: v))) w) = _
  calc
    finSum (fun e : Fin (2 ^ m) =>
      wordSum (fun v => indicator (prescribed ps (e :: v))) w) =
        finSum (fun e : Fin (2 ^ m) =>
          indicator (letterPrescribed (firstLetterRequirements ps) e) *
            wordSum
              (fun v => indicator (prescribed (laterRequirements ps) v)) w) := by
          apply finSum_ext
          intro e
          exact hinner e
    _ = finSum (fun e : Fin (2 ^ m) =>
          indicator (letterPrescribed (firstLetterRequirements ps) e)) *
            wordSum
              (fun v => indicator (prescribed (laterRequirements ps) v)) w :=
          finSum_mul_right _ _
    _ = letterCount (firstLetterRequirements ps) *
            wordSum
              (fun v => indicator (prescribed (laterRequirements ps) v)) w := rfl

/-- Distinct prescribed coordinates in a word have exact weight `2^-K`. -/
theorem prescribed_count {m w : Nat}
    (ps : List (BitRequirement m))
    (hrange : RequirementsInRange w ps)
    (hdist : RequirementsDistinct ps) :
    2 ^ ps.length *
        wordSum (fun u => indicator (prescribed ps u)) w =
      (2 ^ m) ^ w := by
  induction w generalizing ps with
  | zero =>
      have hnil := requirements_in_range_zero_nil hrange
      subst ps
      simp [wordSum, prescribed, indicator]
  | succ w ih =>
      let first := firstLetterRequirements ps
      let later := laterRequirements ps
      have hfirstDistinct : LetterDistinct first :=
        first_requirements_distinct ps hdist
      have hlaterDistinct : RequirementsDistinct later :=
        later_requirements_distinct ps hdist
      have hlaterRange : RequirementsInRange w later :=
        later_requirements_in_range hrange
      have hfirst := one_letter_prescribed_count first hfirstDistinct
      have hlater := ih later hlaterRange hlaterDistinct
      have hlen := requirements_split_length ps
      change first.length + later.length = ps.length at hlen
      have hfactor := wordSum_prescribed_succ (w := w) ps
      change
        wordSum (fun u => indicator (prescribed ps u)) (w + 1) =
          letterCount first *
            wordSum (fun u => indicator (prescribed later u)) w at hfactor
      calc
        2 ^ ps.length *
            wordSum (fun u => indicator (prescribed ps u)) (w + 1) =
            2 ^ (first.length + later.length) *
              (letterCount first *
                wordSum (fun u => indicator (prescribed later u)) w) := by
                  rw [hlen, hfactor]
        _ = (2 ^ first.length * letterCount first) *
              (2 ^ later.length *
                wordSum (fun u => indicator (prescribed later u)) w) := by
                  rw [Nat.pow_add]
                  ac_rfl
        _ = (2 ^ m) * ((2 ^ m) ^ w) := by rw [hfirst, hlater]
        _ = (2 ^ m) ^ (w + 1) := by
              rw [Nat.pow_succ]
              ac_rfl

/-- Number of members of a finite family of Boolean events holding at `x`. -/
def eventCount {F : Nat} {α : Type}
    (events : Fin F → α → Bool) (x : α) : Nat :=
  finSum (fun j : Fin F => indicator (events j x))

private theorem eventCount_succ {F : Nat} {α : Type}
    (events : Fin (F + 1) → α → Bool) (x : α) :
    eventCount events x =
      indicator (events 0 x) +
        eventCount (fun j : Fin F => events j.succ) x := by
  unfold eventCount
  exact finSum_succ _

/-- Linearity over a finite family; no independence or disjointness is used. -/
theorem disjoint_events_mean {m w F : Nat}
    (events : Fin F → List (Fin (2 ^ m)) → Bool)
    (heach : ∀ j,
      (2 ^ m) ^ w ≤
        16 * wordSum (fun u => indicator (events j u)) w) :
    F * (2 ^ m) ^ w ≤
      16 * wordSum (fun u => eventCount events u) w := by
  induction F with
  | zero =>
      simp [eventCount, finSum, wordSum_const]
  | succ F ih =>
      let tail : Fin F → List (Fin (2 ^ m)) → Bool :=
        fun j => events j.succ
      have hzero := heach (0 : Fin (F + 1))
      have htail : ∀ j,
          (2 ^ m) ^ w ≤
            16 * wordSum (fun u => indicator (tail j u)) w := by
        intro j
        exact heach j.succ
      have hind := ih tail htail
      have hdecomp :
          wordSum (fun u => eventCount events u) w =
            wordSum (fun u => indicator (events 0 u)) w +
              wordSum (fun u => eventCount tail u) w := by
        calc
          wordSum (fun u => eventCount events u) w =
              wordSum
                (fun u => indicator (events 0 u) + eventCount tail u) w := by
                  apply congrArg
                    (fun f : List (Fin (2 ^ m)) → Nat => wordSum f w)
                  funext u
                  exact eventCount_succ events u
          _ = wordSum (fun u => indicator (events 0 u)) w +
                wordSum (fun u => eventCount tail u) w :=
                wordSum_add_fun _ _ _
      rw [Nat.succ_mul, hdecomp, Nat.mul_add]
      simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
        Nat.add_le_add hzero hind

/-- Four fixed distinct coordinates per comparison force the advertised
`1/16` lower bound for any containing loss event. -/
theorem four_bit_loss_mean {m w F : Nat}
    (pos : Fin F → List (BitRequirement m))
    (loss : Fin F → List (Fin (2 ^ m)) → Bool)
    (hlen : ∀ j, (pos j).length = 4)
    (hrange : ∀ j, RequirementsInRange w (pos j))
    (hdist : ∀ j, RequirementsDistinct (pos j))
    (hcontained : ∀ j u,
      prescribed (pos j) u = true → loss j u = true) :
    F * (2 ^ m) ^ w ≤
      16 * wordSum (fun u => eventCount loss u) w := by
  apply disjoint_events_mean loss
  intro j
  have hprescribed := prescribed_count (pos j) (hrange j) (hdist j)
  have hmono :
      wordSum (fun u => indicator (prescribed (pos j) u)) w ≤
        wordSum (fun u => indicator (loss j u)) w := by
    apply wordSum_mono
    intro u
    cases hp : prescribed (pos j) u with
    | false => simp [indicator, hp]
    | true =>
        have hl := hcontained j u hp
        simp [indicator, hp, hl]
  have hexact :
      16 * wordSum (fun u => indicator (prescribed (pos j) u)) w =
        (2 ^ m) ^ w := by
    simpa [hlen j] using hprescribed
  calc
    (2 ^ m) ^ w =
        16 * wordSum (fun u => indicator (prescribed (pos j) u)) w :=
      hexact.symm
    _ ≤ 16 * wordSum (fun u => indicator (loss j u)) w :=
      Nat.mul_le_mul_left 16 hmono

end L4.Height.Counting
