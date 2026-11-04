import Leader.Wu.Scheduler.OrderedWordScheduler


set_option autoImplicit false


namespace PPL.Probability


/-- Public P_PL name for the repository's exact fixed-word miss numerator. -/
abbrev fixedWordMissCount {n : Nat}
    (word : DetSchedule n) (horizon : Nat) : Nat :=
  PPLLOrderedWordScheduler.orderedWordMissCount word horizon


/-- A DetSchedule n is literally the edge-index list consumed by
PopulationProtocol.step.  This bridge is only semantic plumbing; the fixed-word
probability bound itself is protocol-independent. -/
def runPopulationSchedule (P : PopulationProtocol) {n : Nat}
    (ring : DirectedRing n) :
    P.Configuration n → DetSchedule n → P.Configuration n
  | C, [] => C
  | C, e :: rest =>
      runPopulationSchedule P ring (P.step ring C e) rest


/-- Lemma-1 wrapper at the repository's exact horizon
H = 2*n*(word.length + K). -/
theorem fixedWordMissCount_mul_twoPow_le_at_horizon {n : Nat}
    (word : DetSchedule n) (K : Nat) :
    let horizon := 2 * n * (word.length + K)
    fixedWordMissCount word horizon * 2 ^ K ≤ n ^ horizon := by
  exact
    PPLLOrderedWordScheduler.orderedWordMissCount_mul_twoPow_le_at_horizon
      word K


/-- Explicit-length Lemma-1 wrapper.  This is the form intended for later
P_PL modules that name the paper word length L. -/
theorem fixedWordMissCount_mul_twoPow_le_of_length {n : Nat}
    (word : DetSchedule n) (L K : Nat)
    (hlength : word.length = L) :
    let horizon := 2 * n * (L + K)
    fixedWordMissCount word horizon * 2 ^ K ≤ n ^ horizon := by
  exact
    PPLLOrderedWordScheduler.orderedWordMissCount_mul_twoPow_le_of_length
      word L K hlength


/-! ## Exact schedule splitting for concatenation -/


private theorem allSchedules_add_raw (n a b : Nat) :
    allSchedules n (a + b) =
      (allSchedules n a).flatMap (fun pre =>
        (allSchedules n b).map (fun suf => pre ++ suf)) := by
  induction b with
  | zero =>
      simp [allSchedules]
  | succ b ih =>
      rw [Nat.add_succ, allSchedules, ih]
      simp only [allSchedules, List.flatMap_assoc, List.map_flatMap,
        List.flatMap_map]
      congr
      funext pre
      congr
      funext suf
      rw [List.map_ofFn]
      congr 1
      funext e
      simp [List.append_assoc]


private theorem sublist_under_prefix
    {A : Type} (pre : List A) {small large : List A}
    (h : small.Sublist large) :
    small.Sublist (pre ++ large) := by
  induction pre with
  | nil =>
      simpa
  | cons x pre ih =>
      simp only [List.cons_append]
      exact List.Sublist.cons x ih


private theorem sublist_append
    {A : Type} {l1 l2 r1 r2 : List A}
    (h1 : l1.Sublist r1) (h2 : l2.Sublist r2) :
    (l1 ++ l2).Sublist (r1 ++ r2) := by
  induction h1 with
  | slnil =>
      simpa only [List.nil_append] using h2
  | @cons l1 r1 x h ih =>
      simp only [List.cons_append]
      exact List.Sublist.cons x ih
  | @cons_cons l1 r1 x h ih =>
      simp only [List.cons_append]
      exact List.Sublist.cons_cons x ih


private def wordMisses {n : Nat}
    (word schedule : DetSchedule n) : Bool :=
  decide (¬word.Sublist schedule)


private theorem countP_mono
    {A : Type} (xs : List A) (p q : A → Bool)
    (hpq : ∀ x, p x = true → q x = true) :
    xs.countP p ≤ xs.countP q := by
  induction xs with
  | nil =>
      simp
  | cons x xs ih =>
      rw [List.countP_cons, List.countP_cons]
      have htail := ih
      cases hp : p x with
      | false =>
          cases hq : q x <;> simp [hp, hq] <;> omega
      | true =>
          have hqx : q x = true := hpq x hp
          simp [hp, hqx]
          omega


private theorem sum_map_le
    {A : Type} (xs : List A) (f g : A → Nat)
    (hfg : ∀ x, x ∈ xs → f x ≤ g x) :
    (xs.map f).sum ≤ (xs.map g).sum := by
  induction xs with
  | nil =>
      simp
  | cons x xs ih =>
      rw [List.map_cons, List.sum_cons, List.map_cons, List.sum_cons]
      exact Nat.add_le_add
        (hfg x (by simp))
        (ih (fun y hy => hfg y (by simp [hy])))


private theorem sum_if_le_count_mul_add_length_mul
    {A : Type} (xs : List A) (p : A → Bool)
    (u v : Nat) :
    (xs.map (fun x => if p x then u else v)).sum ≤
      xs.countP p * u + xs.length * v := by
  induction xs with
  | nil =>
      simp
  | cons x xs ih =>
      rw [List.map_cons, List.sum_cons, List.countP_cons,
        List.length_cons]
      cases hp : p x <;>
        simp [hp, Nat.succ_mul] at * <;>
        omega


private theorem concat_child_miss_le {n H2 : Nat}
    (w1 w2 pre : DetSchedule n) :
    ((allSchedules n H2).map (fun suf => pre ++ suf)).countP
        (wordMisses (w1 ++ w2)) ≤
      if wordMisses w1 pre then n ^ H2
      else fixedWordMissCount w2 H2 := by
  rw [List.countP_map]
  simp only [Function.comp_def]
  by_cases hpre : w1.Sublist pre
  · have hmiss : wordMisses w1 pre = false := by
      simp [wordMisses, hpre]
    rw [hmiss]
    simp only [Bool.false_eq_true, if_false]
    change
      (allSchedules n H2).countP
          (fun suf => wordMisses (w1 ++ w2) (pre ++ suf)) ≤
        (allSchedules n H2).countP (wordMisses w2)
    apply countP_mono
    intro suf hbad
    by_cases hsuf : w2.Sublist suf
    · have hall :
          (w1 ++ w2).Sublist (pre ++ suf) :=
        sublist_append hpre hsuf
      have hfalse :
          wordMisses (w1 ++ w2) (pre ++ suf) = false := by
        simp [wordMisses, hall]
      rw [hfalse] at hbad
      contradiction
    · simp [wordMisses, hsuf]
  · have hmiss : wordMisses w1 pre = true := by
      simp [wordMisses, hpre]
    rw [hmiss]
    simp only [if_true]
    calc
      (allSchedules n H2).countP
          (fun suf => wordMisses (w1 ++ w2) (pre ++ suf)) ≤
          (allSchedules n H2).length :=
        List.countP_le_length
      _ = n ^ H2 := allSchedules_length n H2


/-- Nat union bound for a concatenated prescribed word.  If the first word
occurs inside the first block and the second word occurs inside the second
block, their concatenation occurs in the concatenated schedule. -/
theorem fixedWordMissCount_append_le {n H1 H2 : Nat}
    (w1 w2 : DetSchedule n) :
    fixedWordMissCount (w1 ++ w2) (H1 + H2) ≤
      fixedWordMissCount w1 H1 * n ^ H2 +
        n ^ H1 * fixedWordMissCount w2 H2 := by
  change
    (allSchedules n (H1 + H2)).countP
        (wordMisses (w1 ++ w2)) ≤ _
  rw [allSchedules_add_raw, List.countP_flatMap]
  change
    ((allSchedules n H1).map
      (fun pre =>
        ((allSchedules n H2).map
          (fun suf => pre ++ suf)).countP
            (wordMisses (w1 ++ w2)))).sum ≤ _
  have hpoint :
      ∀ pre ∈ allSchedules n H1,
        ((allSchedules n H2).map
          (fun suf => pre ++ suf)).countP
            (wordMisses (w1 ++ w2)) ≤
          if wordMisses w1 pre then n ^ H2
          else fixedWordMissCount w2 H2 := by
    intro pre hpre
    exact concat_child_miss_le w1 w2 pre
  calc
    ((allSchedules n H1).map
      (fun pre =>
        ((allSchedules n H2).map
          (fun suf => pre ++ suf)).countP
            (wordMisses (w1 ++ w2)))).sum ≤
        ((allSchedules n H1).map
          (fun pre =>
            if wordMisses w1 pre then n ^ H2
            else fixedWordMissCount w2 H2)).sum :=
      sum_map_le _ _ _ hpoint
    _ ≤ (allSchedules n H1).countP (wordMisses w1) * n ^ H2 +
        (allSchedules n H1).length *
          fixedWordMissCount w2 H2 :=
      sum_if_le_count_mul_add_length_mul
        (allSchedules n H1) (wordMisses w1)
        (n ^ H2) (fixedWordMissCount w2 H2)
    _ = fixedWordMissCount w1 H1 * n ^ H2 +
        n ^ H1 * fixedWordMissCount w2 H2 := by
      rw [allSchedules_length]
      rfl


/-- The same concatenation union bound after multiplying by a common 2^K
scale.  The right side is literally the sum of the two scaled miss budgets,
padded by the size of the opposite block. -/
theorem fixedWordMissCount_append_mul_twoPow_le
    {n H1 H2 : Nat} (w1 w2 : DetSchedule n) (K : Nat) :
    fixedWordMissCount (w1 ++ w2) (H1 + H2) * 2 ^ K ≤
      (fixedWordMissCount w1 H1 * 2 ^ K) * n ^ H2 +
        n ^ H1 * (fixedWordMissCount w2 H2 * 2 ^ K) := by
  have h :=
    Nat.mul_le_mul_right (2 ^ K)
      (fixedWordMissCount_append_le
        (H1 := H1) (H2 := H2) w1 w2)
  calc
    fixedWordMissCount (w1 ++ w2) (H1 + H2) * 2 ^ K ≤
        (fixedWordMissCount w1 H1 * n ^ H2 +
          n ^ H1 * fixedWordMissCount w2 H2) * 2 ^ K := h
    _ = (fixedWordMissCount w1 H1 * 2 ^ K) * n ^ H2 +
        n ^ H1 * (fixedWordMissCount w2 H2 * 2 ^ K) := by
      rw [Nat.add_mul]
      ac_rfl


/-- Plug arbitrary scaled bounds B1 and B2 into the Nat union bound. -/
theorem fixedWordMissCount_append_mul_twoPow_le_of_bounds
    {n H1 H2 : Nat} (w1 w2 : DetSchedule n)
    (K B1 B2 : Nat)
    (h1 : fixedWordMissCount w1 H1 * 2 ^ K ≤ B1)
    (h2 : fixedWordMissCount w2 H2 * 2 ^ K ≤ B2) :
    fixedWordMissCount (w1 ++ w2) (H1 + H2) * 2 ^ K ≤
      B1 * n ^ H2 + n ^ H1 * B2 := by
  exact Nat.le_trans
    (fixedWordMissCount_append_mul_twoPow_le w1 w2 K)
    (Nat.add_le_add
      (Nat.mul_le_mul_right (n ^ H2) h1)
      (Nat.mul_le_mul_left (n ^ H1) h2))


/-- In particular, two n^-K block bounds give a factor-2 union bound at the
concatenated horizon. -/
theorem fixedWordMissCount_append_mul_twoPow_le_two
    {n H1 H2 : Nat} (w1 w2 : DetSchedule n) (K : Nat)
    (h1 : fixedWordMissCount w1 H1 * 2 ^ K ≤ n ^ H1)
    (h2 : fixedWordMissCount w2 H2 * 2 ^ K ≤ n ^ H2) :
    fixedWordMissCount (w1 ++ w2) (H1 + H2) * 2 ^ K ≤
      2 * n ^ (H1 + H2) := by
  have h :=
    fixedWordMissCount_append_mul_twoPow_le_of_bounds
      w1 w2 K (n ^ H1) (n ^ H2) h1 h2
  calc
    _ ≤ n ^ H1 * n ^ H2 + n ^ H1 * n ^ H2 := h
    _ = 2 * n ^ (H1 + H2) := by
      rw [Nat.pow_add]
      omega


end PPL.Probability

#print axioms PPL.Probability.fixedWordMissCount_mul_twoPow_le_at_horizon
#print axioms PPL.Probability.fixedWordMissCount_mul_twoPow_le_of_length
#print axioms PPL.Probability.fixedWordMissCount_append_le
#print axioms PPL.Probability.fixedWordMissCount_append_mul_twoPow_le_two
