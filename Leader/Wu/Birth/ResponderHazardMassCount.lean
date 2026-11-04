import Leader.Wu.Birth.ResponderHazardMassArithmetic
import Leader.Wu.Scheduler.RepeatedBlocks

/-! Exact counts in the actual `allSchedules` uniform enumeration. Neither
independence nor a fair-stream hypothesis is an input. -/

set_option autoImplicit false

namespace BirthResponderHazardMassCount

open FiniteUniformStoppingTree PPLLSchedulerBlocks BirthResponderHazardMassArithmetic

variable {n : Nat}

private theorem sum_if_count {A : Type} (xs : List A) (p : A → Bool) (c : Nat) :
    (xs.map (fun x => if p x then c else 0)).sum = xs.countP p * c := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      rw [List.map_cons, List.sum_cons, List.countP_cons, ih]
      cases p x <;> simp [Nat.add_mul, Nat.add_comm]

private theorem countP_eq_sum_indicator {A : Type} (xs : List A) (p : A → Bool) :
    xs.countP p = (xs.map (fun x => if p x then 1 else 0)).sum := by
  simpa only [Nat.mul_one] using (sum_if_count xs p 1).symm

/-- Product counting of every allowed letter, preserving multiplicity in
`allSchedules` instead of replacing it by a set of words. -/
theorem all_allowed_count (p : Fin n → Bool) (T : Nat) :
    (allSchedules n T).countP (fun w => w.all p) =
      ((List.ofFn (fun e : Fin n => e)).countP p) ^ T := by
  induction T with
  | zero => simp [allSchedules]
  | succ T ih =>
      rw [allSchedules, List.countP_flatMap]
      have he : ∀ w : DetSchedule n,
          (List.ofFn (fun e : Fin n => w ++ [e])).countP (fun u => u.all p) =
            if w.all p then (List.ofFn (fun e : Fin n => e)).countP p else 0 := by
        intro w
        have hmap : List.ofFn (fun e : Fin n => w ++ [e]) =
            (List.ofFn (fun e : Fin n => e)).map (fun e => w ++ [e]) := by
          rw [List.map_ofFn]
          rfl
        rw [hmap, List.countP_map]
        simp only [Function.comp_def, List.all_append, List.all_cons, List.all_nil, Bool.and_true]
        cases w.all p <;> simp
      have hsum :
          ((allSchedules n T).map (fun w =>
            (List.ofFn (fun e : Fin n => w ++ [e])).countP (fun u => u.all p))).sum =
          ((allSchedules n T).map (fun w => if w.all p then
            (List.ofFn (fun e : Fin n => e)).countP p else 0)).sum := by
        apply congrArg List.sum
        apply List.map_congr_left
        intro w _
        exact he w
      change ((allSchedules n T).map (fun w =>
        (List.ofFn (fun e : Fin n => w ++ [e])).countP (fun u => u.all p))).sum = _
      rw [hsum, sum_if_count, ih, Nat.pow_succ]

private theorem nodup_ofFn_injective {k : Nat} {A : Type}
    (f : Fin k → A) (hf : Function.Injective f) : (List.ofFn f).Nodup := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [List.ofFn_succ, List.nodup_cons]
      constructor
      · intro hm
        obtain ⟨i, hi⟩ := List.mem_ofFn.mp hm
        have h := hf hi
        cases h
      · exact ih (fun i => f i.succ) (fun i j h => Fin.succ_inj.mp (hf h))

def allowOne (b e : Fin n) : Bool := decide (e ≠ b)
def allowTwo (a b e : Fin n) : Bool := decide (e ≠ a ∧ e ≠ b)

private theorem symbol_counts (a b : Fin n) (hab : a ≠ b) (hn : 2 ≤ n) :
    (List.ofFn (fun e : Fin n => e)).countP (allowOne b) = n - 1 ∧
      (List.ofFn (fun e : Fin n => e)).countP (allowTwo a b) = n - 2 := by
  have hd := nodup_ofFn_injective (fun e : Fin n => e) Function.injective_id
  have ha := List.mem_ofFn.mpr (show ∃ e : Fin n, e = a from ⟨a, rfl⟩)
  have hb := List.mem_ofFn.mpr (show ∃ e : Fin n, e = b from ⟨b, rfl⟩)
  constructor
  · rw [countP_eq_sum_indicator]
    have h := sum_two_exceptions (List.ofFn (fun e : Fin n => e)) a b
      (fun e => if allowOne b e then 1 else 0) 1 hd ha hb hab (by
        intro e _ _ heb
        simp [allowOne, heb])
    simpa [allowOne, hab, Nat.add_comm, show 1 + (n - 2) = n - 1 by omega] using h
  · rw [countP_eq_sum_indicator]
    have h := sum_two_exceptions (List.ofFn (fun e : Fin n => e)) a b
      (fun e => if allowTwo a b e then 1 else 0) 1 hd ha hb hab (by
        intro e _ hea heb
        simp [allowTwo, hea, heb])
    simpa [allowTwo] using h

/-- Every letter avoids the outgoing edge; at least one is the incoming edge. -/
def blockGood (a b : Fin n) (w : DetSchedule n) : Bool :=
  w.all (allowOne b) && !(w.all (allowOne a))

private theorem all_two (a b : Fin n) (w : DetSchedule n) :
    w.all (allowTwo a b) = (w.all (allowOne b) && w.all (allowOne a)) := by
  induction w with
  | nil => rfl
  | cons e es ih =>
      simp only [List.all_cons, allowTwo, allowOne, Bool.decide_and, ih]
      ac_rfl

private theorem count_partition {A : Type} (xs : List A) (p q : A → Bool) :
    xs.countP (fun x => p x && !q x) + xs.countP (fun x => p x && q x) = xs.countP p := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.countP_cons]
      cases p x <;> cases q x <;> simp <;> omega

/-- A partition identity proves the subtraction is genuine: the two
nonnegative classes add to the complete outgoing-avoiding count. -/
theorem good_block_partition (a b : Fin n) (hab : a ≠ b) (hn : 2 ≤ n) (T : Nat) :
    (allSchedules n T).countP (blockGood a b) + (n - 2) ^ T = (n - 1) ^ T := by
  have hp := count_partition (allSchedules n T)
    (fun w => w.all (allowOne b)) (fun w => w.all (allowOne a))
  have hs := symbol_counts a b hab hn
  have htwo : (fun w : DetSchedule n => w.all (allowOne b) && w.all (allowOne a)) =
      (fun w => w.all (allowTwo a b)) := by
    funext w
    exact (all_two a b w).symm
  rw [htwo, all_allowed_count, all_allowed_count, hs.1, hs.2] at hp
  exact hp

theorem good_block_count (a b : Fin n) (hab : a ≠ b) (hn : 2 ≤ n) :
    (allSchedules n n).countP (blockGood a b) = blockNumerator n := by
  have hp := good_block_partition a b hab hn n
  unfold blockNumerator
  omega

/-- Consecutive fixed-length tests on a whole raw word, including its exact
end at block zero. This does not restart the physical process. -/
def cylinder (length : Nat) (good : DetSchedule n → Bool) : Nat → DetSchedule n → Bool
  | 0, w => w.isEmpty
  | blocks + 1, w => good (w.take length) && cylinder length good blocks (w.drop length)

theorem cylinder_append (length blocks : Nat) (good : DetSchedule n → Bool)
    (pre suf : DetSchedule n) (hp : pre.length = length) :
    cylinder length good (blocks + 1) (pre ++ suf) =
      (good pre && cylinder length good blocks suf) := by
  simp only [cylinder, ← hp, List.take_left, List.drop_left]

/-- The finite Cartesian product gives the exact power count. -/
theorem cylinder_count (length blocks : Nat) (good : DetSchedule n → Bool) :
    (allSchedules n (length * blocks)).countP (cylinder length good blocks) =
      ((allSchedules n length).countP good) ^ blocks := by
  induction blocks with
  | zero => simp [cylinder, allSchedules]
  | succ blocks ih =>
      rw [show length * (blocks + 1) = length + length * blocks by rw [Nat.mul_succ, Nat.add_comm],
        allSchedules_add, List.countP_flatMap]
      have hmap :
          ((allSchedules n length).map (fun pre =>
            ((allSchedules n (length * blocks)).map (fun suf => pre ++ suf)).countP
              (cylinder length good (blocks + 1)))).sum =
          ((allSchedules n length).map (fun pre => if good pre then
            (allSchedules n (length * blocks)).countP (cylinder length good blocks) else 0)).sum := by
        apply congrArg List.sum
        apply List.map_congr_left
        intro pre hpre
        rw [List.countP_map]
        have hp := allSchedules_schedule_length n length pre hpre
        have hf : (fun suf : DetSchedule n => cylinder length good (blocks + 1) (pre ++ suf)) =
            (fun suf => good pre && cylinder length good blocks suf) := by
          funext suf
          exact cylinder_append length blocks good pre suf hp
        change (allSchedules n (length * blocks)).countP
          (fun suf => cylinder length good (blocks + 1) (pre ++ suf)) = _
        rw [hf]
        cases good pre <;> simp
      change ((allSchedules n length).map (fun pre =>
        ((allSchedules n (length * blocks)).map (fun suf => pre ++ suf)).countP
          (cylinder length good (blocks + 1)))).sum = _
      rw [hmap, sum_if_count, ih, Nat.pow_succ]
      exact Nat.mul_comm _ _

theorem good_cylinder_count (a b : Fin n) (hab : a ≠ b) (hn : 2 ≤ n) (blocks : Nat) :
    (allSchedules n (n * blocks)).countP (cylinder n (blockGood a b) blocks) =
      blockNumerator n ^ blocks := by
  rw [cylinder_count, good_block_count a b hab hn]

theorem good_cylinder_mass (a b : Fin n) (hab : a ≠ b) (hn : 2 ≤ n) (blocks : Nat) :
    n ^ (n * blocks) ≤ 8 ^ blocks *
      (allSchedules n (n * blocks)).countP (cylinder n (blockGood a b) blocks) := by
  rw [good_cylinder_count a b hab hn blocks]
  exact repeated_block_eighth n blocks hn

end BirthResponderHazardMassCount

#print axioms BirthResponderHazardMassCount.good_block_partition
#print axioms BirthResponderHazardMassCount.good_block_count
#print axioms BirthResponderHazardMassCount.good_cylinder_count
#print axioms BirthResponderHazardMassCount.good_cylinder_mass
