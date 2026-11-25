import Leader.L4.Height.Core

namespace L4.Height

namespace Thru

open scoped Classical

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 12000000

noncomputable section

abbrev Word (n : Nat) := List (Fin n)

/-- Sum a natural-valued function over all scheduler words of length `k`. -/
def wordSum {n : Nat} (f : Word n → Nat) : Nat → Nat
  | 0 => f []
  | k + 1 =>
      (List.ofFn (fun e : Fin n =>
        wordSum (fun v => f (e :: v)) k)).sum

private theorem ofFn_sum_congr {n : Nat} (f g : Fin n → Nat)
    (h : ∀ e, f e = g e) :
    (List.ofFn f).sum = (List.ofFn g).sum := by
  induction n with
  | zero =>
      simp [List.ofFn_zero]
  | succ n ih =>
      rw [List.ofFn_succ, List.ofFn_succ,
        List.sum_cons, List.sum_cons]
      rw [h 0]
      have ht := ih
        (fun e : Fin n => f e.succ)
        (fun e : Fin n => g e.succ)
        (fun e => h e.succ)
      rw [ht]

theorem ofFn_sum_le {n : Nat} (f g : Fin n → Nat)
    (h : ∀ e, f e ≤ g e) :
    (List.ofFn f).sum ≤ (List.ofFn g).sum := by
  induction n with
  | zero =>
      simp [List.ofFn_zero]
  | succ n ih =>
      rw [List.ofFn_succ, List.ofFn_succ,
        List.sum_cons, List.sum_cons]
      have ht := ih
        (fun e : Fin n => f e.succ)
        (fun e : Fin n => g e.succ)
        (fun e => h e.succ)
      exact Nat.add_le_add (h 0) ht

private theorem ofFn_sum_add {n : Nat} (f g : Fin n → Nat) :
    (List.ofFn (fun e => f e + g e)).sum =
      (List.ofFn f).sum + (List.ofFn g).sum := by
  induction n with
  | zero =>
      simp [List.ofFn_zero]
  | succ n ih =>
      rw [List.ofFn_succ, List.ofFn_succ, List.ofFn_succ,
        List.sum_cons, List.sum_cons, List.sum_cons]
      have ht := ih
        (fun e : Fin n => f e.succ)
        (fun e : Fin n => g e.succ)
      rw [ht]
      omega

private theorem ofFn_sum_const (n c : Nat) :
    (List.ofFn (fun _ : Fin n => c)).sum = n * c := by
  induction n with
  | zero =>
      simp [List.ofFn_zero]
  | succ n ih =>
      rw [List.ofFn_succ, List.sum_cons, ih]
      simp only [Nat.add_mul, Nat.one_mul]
      omega

theorem ofFn_sum_mul_left {n : Nat} (c : Nat) (f : Fin n → Nat) :
    (List.ofFn (fun e => c * f e)).sum =
      c * (List.ofFn f).sum := by
  induction n with
  | zero =>
      simp [List.ofFn_zero]
  | succ n ih =>
      rw [List.ofFn_succ, List.ofFn_succ,
        List.sum_cons, List.sum_cons]
      rw [ih]
      rw [Nat.mul_add]

theorem wordSum_mono {n : Nat} (f g : Word n → Nat) :
    (∀ w, f w ≤ g w) → ∀ k, wordSum f k ≤ wordSum g k := by
  intro h k
  induction k generalizing f g with
  | zero =>
      exact h []
  | succ k ih =>
      simp only [wordSum]
      apply ofFn_sum_le
      intro e
      apply ih
      intro v
      exact h (e :: v)

theorem wordSum_congr {n : Nat} (f g : Word n → Nat)
    (h : ∀ w, f w = g w) (k : Nat) :
    wordSum f k = wordSum g k := by
  apply Nat.le_antisymm
  · exact wordSum_mono f g (fun w => Nat.le_of_eq (h w)) k
  · exact wordSum_mono g f (fun w => Nat.le_of_eq (h w).symm) k

theorem wordSum_congr_length {n : Nat} (f g : Word n → Nat) :
    ∀ k, (∀ w, w.length = k → f w = g w) →
      wordSum f k = wordSum g k := by
  intro k
  induction k generalizing f g with
  | zero =>
      intro h
      simp only [wordSum]
      exact h [] rfl
  | succ k ih =>
      intro h
      simp only [wordSum]
      apply ofFn_sum_congr
      intro e
      apply ih
      intro w hw
      apply h (e :: w)
      simp only [List.length_cons]
      omega

theorem wordSum_add_fun {n : Nat}
    (f g : Word n → Nat) (k : Nat) :
    wordSum (fun w => f w + g w) k =
      wordSum f k + wordSum g k := by
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
                  exact ih
                    (fun v => f (e :: v))
                    (fun v => g (e :: v))
        _ =
            (List.ofFn (fun e : Fin n =>
              wordSum (fun v => f (e :: v)) k)).sum +
            (List.ofFn (fun e : Fin n =>
              wordSum (fun v => g (e :: v)) k)).sum :=
              ofFn_sum_add _ _

theorem wordSum_mul_left {n : Nat} (c : Nat)
    (f : Word n → Nat) (k : Nat) :
    wordSum (fun w => c * f w) k = c * wordSum f k := by
  induction k generalizing f with
  | zero =>
      simp [wordSum]
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
        _ = c *
            (List.ofFn (fun e : Fin n =>
              wordSum (fun v => f (e :: v)) k)).sum :=
              ofFn_sum_mul_left _ _

theorem wordSum_const_one {n : Nat} (k : Nat) :
    wordSum (fun _ : Word n => 1) k = n ^ k := by
  induction k with
  | zero =>
      rfl
  | succ k ih =>
      simp only [wordSum]
      calc
        (List.ofFn (fun _ : Fin n =>
            wordSum (fun _ : Word n => 1) k)).sum =
            (List.ofFn (fun _ : Fin n => n ^ k)).sum := by
              apply ofFn_sum_congr
              intro e
              exact ih
        _ = n * n ^ k := ofFn_sum_const n (n ^ k)
        _ = n ^ (k + 1) := by
              rw [Nat.pow_succ]
              exact Nat.mul_comm _ _

theorem wordSum_const {n : Nat} (c k : Nat) :
    wordSum (fun _ : Word n => c) k = c * n ^ k := by
  calc
    wordSum (fun _ : Word n => c) k =
        wordSum (fun _ : Word n => c * 1) k := by
          apply wordSum_congr
          intro u
          simp
    _ = c * wordSum (fun _ : Word n => 1) k :=
      wordSum_mul_left c (fun _ : Word n => 1) k
    _ = c * n ^ k := by rw [wordSum_const_one]

theorem list_sum_map_le {β : Type} (xs : List β)
    (f : β → Nat) (B : Nat)
    (h : ∀ x, x ∈ xs → f x ≤ B) :
    (xs.map f).sum ≤ xs.length * B := by
  induction xs with
  | nil =>
      simp
  | cons x xs ih =>
      have hx : f x ≤ B := h x (by simp)
      have htail : (xs.map f).sum ≤ xs.length * B := by
        apply ih
        intro y hy
        exact h y (by simp [hy])
      calc
        ((x :: xs).map f).sum = f x + (xs.map f).sum := by
          rw [List.map_cons, List.sum_cons]
        _ ≤ B + xs.length * B := Nat.add_le_add hx htail
        _ = (x :: xs).length * B := by
          simp only [List.length_cons, Nat.add_mul, Nat.one_mul]
          omega

/-- Execute a scheduler word. -/
def runWord {α : Type} {n : Nat}
    (next : α → Fin n → α) : α → Word n → α
  | x, [] => x
  | x, e :: u => runWord next (next x e) u

/-- Letters consumed before first seeing `A`; if no hit is seen, use
all available letters. The current state is tested before a letter. -/
def wait {α : Type} {n : Nat}
    (next : α → Fin n → α) (A : α → Prop) :
    α → Word n → Nat
  | _, [] => 0
  | x, e :: u =>
      if A x then 0 else Nat.succ (wait next A (next x e) u)

theorem wait_of_hit {α : Type} {n : Nat}
    (next : α → Fin n → α) (A : α → Prop)
    (x : α) (hx : A x) (u : Word n) :
    wait next A x u = 0 := by
  cases u with
  | nil => rfl
  | cons e u =>
      simp only [wait, if_pos hx]

theorem wait_cons_of_not {α : Type} {n : Nat}
    (next : α → Fin n → α) (A : α → Prop)
    (x : α) (hx : ¬ A x) (e : Fin n) (u : Word n) :
    wait next A x (e :: u) =
      Nat.succ (wait next A (next x e) u) := by
  simp only [wait, if_neg hx]

theorem wait_le_length {α : Type} {n : Nat}
    (next : α → Fin n → α) (A : α → Prop) :
    ∀ x u, wait next A x u ≤ u.length := by
  intro x u
  induction u generalizing x with
  | nil =>
      exact Nat.le_refl _
  | cons e u ih =>
      by_cases hx : A x
      · rw [wait_of_hit next A x hx]
        exact Nat.zero_le _
      · rw [wait_cons_of_not next A x hx e u]
        simp only [List.length_cons]
        exact Nat.succ_le_succ (ih (next x e))

private def seqWaitFuel {α : Type} {n : Nat}
    (next : α → Fin n → α) :
    Nat → List (α → Prop) → α → Word n → Nat
  | 0, _, _, _ => 0
  | _ + 1, [], _, _ => 0
  | _ + 1, _ :: _, _, [] => 0
  | fuel + 1, A :: As, x, e :: u =>
      if A x then
        seqWaitFuel next fuel As x (e :: u)
      else
        1 + seqWaitFuel next fuel (A :: As) (next x e) u

/-- Elapsed time for successive stopping queries. A hit consumes no
letter; a miss consumes one letter and keeps the current query. -/
def seqWait {α : Type} {n : Nat}
    (next : α → Fin n → α)
    (queries : List (α → Prop)) (x : α) (u : Word n) : Nat :=
  seqWaitFuel next (queries.length + u.length) queries x u

private theorem seqWaitFuel_no_queries {α : Type} {n : Nat}
    (next : α → Fin n → α) :
    ∀ fuel x u, seqWaitFuel next fuel [] x u = 0 := by
  intro fuel x u
  cases fuel <;> rfl

private theorem seqWaitFuel_empty_word {α : Type} {n : Nat}
    (next : α → Fin n → α) :
    ∀ fuel queries x, seqWaitFuel next fuel queries x [] = 0 := by
  intro fuel queries x
  cases fuel with
  | zero => rfl
  | succ fuel =>
      cases queries <;> rfl

private theorem seqWait_no_queries {α : Type} {n : Nat}
    (next : α → Fin n → α) (x : α) (u : Word n) :
    seqWait next [] x u = 0 := by
  unfold seqWait
  exact seqWaitFuel_no_queries next _ _ _

theorem seqWait_nil {α : Type} {n : Nat}
    (next : α → Fin n → α)
    (queries : List (α → Prop)) (x : α) :
    seqWait next queries x [] = 0 := by
  unfold seqWait
  exact seqWaitFuel_empty_word next _ _ _

theorem seqWait_cons_of_hit {α : Type} {n : Nat}
    (next : α → Fin n → α) (A : α → Prop)
    (As : List (α → Prop)) (x : α) (hx : A x)
    (u : Word n) :
    seqWait next (A :: As) x u = seqWait next As x u := by
  cases u with
  | nil =>
      calc
        seqWait next (A :: As) x [] = 0 :=
          seqWait_nil next (A :: As) x
        _ = seqWait next As x [] :=
          (seqWait_nil next As x).symm
  | cons e u =>
      unfold seqWait
      have hfuel :
          (A :: As).length + (e :: u).length =
            As.length + (e :: u).length + 1 := by
        simp only [List.length_cons]
        omega
      rw [hfuel]
      simp only [seqWaitFuel, if_pos hx]

theorem seqWait_cons_step {α : Type} {n : Nat}
    (next : α → Fin n → α) (A : α → Prop)
    (As : List (α → Prop)) (x : α) (hx : ¬ A x)
    (e : Fin n) (u : Word n) :
    seqWait next (A :: As) x (e :: u) =
      1 + seqWait next (A :: As) (next x e) u := by
  unfold seqWait
  have hfuel :
      (A :: As).length + (e :: u).length =
        (A :: As).length + u.length + 1 := by
    simp only [List.length_cons]
    omega
  rw [hfuel]
  simp only [seqWaitFuel, if_neg hx]

theorem seqWait_single {α : Type} {n : Nat}
    (next : α → Fin n → α) (A : α → Prop)
    (x : α) (u : Word n) :
    seqWait next [A] x u = wait next A x u := by
  induction u generalizing x with
  | nil =>
      rw [seqWait_nil]
      rfl
  | cons e u ih =>
      by_cases hx : A x
      · calc
          seqWait next [A] x (e :: u) =
              seqWait next [] x (e :: u) :=
                seqWait_cons_of_hit next A [] x hx (e :: u)
          _ = 0 := seqWait_no_queries next x (e :: u)
          _ = wait next A x (e :: u) :=
                (wait_of_hit next A x hx (e :: u)).symm
      · rw [seqWait_cons_step next A [] x hx e u]
        rw [wait_cons_of_not next A x hx e u]
        rw [ih (next x e)]
        omega

theorem seqWait_le_length {α : Type} {n : Nat}
    (next : α → Fin n → α) :
    ∀ queries x u, seqWait next queries x u ≤ u.length := by
  intro queries
  induction queries with
  | nil =>
      intro x u
      rw [seqWait_no_queries]
      exact Nat.zero_le _
  | cons A As ih =>
      intro x u
      induction u generalizing x with
      | nil =>
          rw [seqWait_nil]
          exact Nat.zero_le _
      | cons e u ihu =>
          by_cases hx : A x
          · rw [seqWait_cons_of_hit next A As x hx (e :: u)]
            exact ih x (e :: u)
          · rw [seqWait_cons_step next A As x hx e u]
            have ht := ihu (next x e)
            simp only [List.length_cons]
            omega

/-- The requested truncated base-two moment hypothesis. -/
def MomentAt {α : Type} {n : Nat}
    (next : α → Fin n → α) (A : α → Prop)
    (L : Nat) (x : α) : Prop :=
  ∀ t, wordSum
      (fun u => 2 ^ (Nat.min (wait next A x u) t / L)) t
    ≤ 2 * n ^ t

theorem momentAt_raw {α : Type} {n : Nat}
    (next : α → Fin n → α) (A : α → Prop)
    (L : Nat) (x : α) (h : MomentAt next A L x)
    (t : Nat) :
    wordSum (fun u => 2 ^ (wait next A x u / L)) t
      ≤ 2 * n ^ t := by
  have heq :
      wordSum (fun u => 2 ^ (wait next A x u / L)) t =
      wordSum
        (fun u => 2 ^ (Nat.min (wait next A x u) t / L)) t := by
    apply wordSum_congr_length
    intro u hu
    have hw := wait_le_length next A x u
    have hwt : wait next A x u ≤ t := by
      simpa [hu] using hw
    have hm : Nat.min (wait next A x u) t =
        wait next A x u := Nat.min_eq_left hwt
    exact congrArg (fun q => 2 ^ (q / L)) hm.symm
  rw [heq]
  exact h t

theorem seqMoment_trunc_eq_raw {α : Type} {n : Nat}
    (next : α → Fin n → α)
    (queries : List (α → Prop)) (L t : Nat) (x : α) :
    wordSum
        (fun u => 2 ^ (Nat.min (seqWait next queries x u) t / L)) t
      =
    wordSum (fun u => 2 ^ (seqWait next queries x u / L)) t := by
  apply wordSum_congr_length
  intro u hu
  have hs := seqWait_le_length next queries x u
  have hst : seqWait next queries x u ≤ t := by
    simpa [hu] using hs
  have hm : Nat.min (seqWait next queries x u) t =
      seqWait next queries x u := Nat.min_eq_left hst
  exact congrArg (fun q => 2 ^ (q / L)) hm

/-- Floor division is subadditive up to one carry. -/
theorem div_add_le (a b L : Nat) (hL : 1 ≤ L) :
    (a + b) / L ≤ a / L + b / L + 1 := by
  have hpos : 0 < L := by omega
  rw [Nat.add_div hpos]
  split <;> omega

theorem two_pow_floor_add (a b L : Nat) (hL : 1 ≤ L) :
    2 ^ ((a + b) / L) ≤
      2 * (2 ^ (a / L) * 2 ^ (b / L)) := by
  have hp := Nat.pow_le_pow_right
    (by omega : 0 < (2 : Nat)) (div_add_le a b L hL)
  calc
    2 ^ ((a + b) / L)
        ≤ 2 ^ (a / L + b / L + 1) := hp
    _ = 2 * (2 ^ (a / L) * 2 ^ (b / L)) := by
      simp only [Nat.pow_add, Nat.pow_one]
      ac_rfl

/-- Product integrand obtained by splitting at the first `A` hit.
`k` is elapsed time accumulated before entering this state. -/
def splitCost {α : Type} {n : Nat}
    (next : α → Fin n → α) (A : α → Prop)
    (As : List (α → Prop)) (L : Nat) :
    Nat → α → Word n → Nat
  | k, x, [] =>
      if A x then
        2 ^ (k / L) * 2 ^ (seqWait next As x [] / L)
      else 2 ^ (k / L)
  | k, x, e :: u =>
      if A x then
        2 ^ (k / L) * 2 ^ (seqWait next As x (e :: u) / L)
      else
        splitCost next A As L (k + 1) (next x e) u

theorem splitCost_of_hit {α : Type} {n : Nat}
    (next : α → Fin n → α) (A : α → Prop)
    (As : List (α → Prop)) (L k : Nat)
    (x : α) (hx : A x) (u : Word n) :
    splitCost next A As L k x u =
      2 ^ (k / L) * 2 ^ (seqWait next As x u / L) := by
  cases u with
  | nil =>
      simp only [splitCost, if_pos hx]
  | cons e u =>
      simp only [splitCost, if_pos hx]

theorem splitCost_nil_of_not {α : Type} {n : Nat}
    (next : α → Fin n → α) (A : α → Prop)
    (As : List (α → Prop)) (L k : Nat)
    (x : α) (hx : ¬ A x) :
    splitCost next A As L k x [] = 2 ^ (k / L) := by
  simp only [splitCost, if_neg hx]

theorem splitCost_cons_of_not {α : Type} {n : Nat}
    (next : α → Fin n → α) (A : α → Prop)
    (As : List (α → Prop)) (L k : Nat)
    (x : α) (hx : ¬ A x) (e : Fin n) (u : Word n) :
    splitCost next A As L k x (e :: u) =
      splitCost next A As L (k + 1) (next x e) u := by
  simp only [splitCost, if_neg hx]

/-- Prefix partition / strong-Markov counting lemma. -/
theorem splitCost_sum_le {α : Type} {n : Nat}
    (next : α → Fin n → α) (A : α → Prop)
    (As : List (α → Prop)) (L C : Nat)
    (hTail : ∀ y r,
      wordSum (fun u => 2 ^ (seqWait next As y u / L)) r
        ≤ C * n ^ r)
    (hC : 1 ≤ C) :
    ∀ k x t,
      wordSum (splitCost next A As L k x) t ≤
        C * wordSum
          (fun u => 2 ^ ((k + wait next A x u) / L)) t := by
  intro k x t
  induction t generalizing k x with
  | zero =>
      by_cases hx : A x
      · have hc := Nat.mul_le_mul_right (2 ^ (k / L)) hC
        simpa [wordSum, splitCost, hx, wait, seqWait_nil,
          Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hc
      · have hc := Nat.mul_le_mul_right (2 ^ (k / L)) hC
        simpa [wordSum, splitCost, hx, wait,
          Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hc
  | succ t ih =>
      by_cases hx : A x
      · have hleft :
          wordSum (splitCost next A As L k x) (t + 1) =
            2 ^ (k / L) *
              wordSum
                (fun u => 2 ^ (seqWait next As x u / L)) (t + 1) := by
          calc
            wordSum (splitCost next A As L k x) (t + 1) =
                wordSum
                  (fun u => 2 ^ (k / L) *
                    2 ^ (seqWait next As x u / L)) (t + 1) := by
                      apply wordSum_congr
                      intro u
                      exact splitCost_of_hit next A As L k x hx u
            _ = 2 ^ (k / L) *
                  wordSum
                    (fun u => 2 ^ (seqWait next As x u / L)) (t + 1) :=
                wordSum_mul_left _ _ _
        have hright :
          wordSum
              (fun u => 2 ^ ((k + wait next A x u) / L)) (t + 1) =
            2 ^ (k / L) * n ^ (t + 1) := by
          calc
            wordSum
                (fun u => 2 ^ ((k + wait next A x u) / L)) (t + 1) =
                wordSum (fun _ : Word n => 2 ^ (k / L)) (t + 1) := by
                    apply wordSum_congr
                    intro u
                    rw [wait_of_hit next A x hx u]
                    simp only [Nat.add_zero]
            _ = 2 ^ (k / L) * n ^ (t + 1) :=
                wordSum_const _ _
        rw [hleft, hright]
        have ht := hTail x (t + 1)
        calc
          2 ^ (k / L) *
              wordSum (fun u => 2 ^ (seqWait next As x u / L)) (t + 1)
              ≤ 2 ^ (k / L) * (C * n ^ (t + 1)) :=
                Nat.mul_le_mul_left _ ht
          _ = C * (2 ^ (k / L) * n ^ (t + 1)) := by
                ac_rfl
      · have hleft :
          wordSum (splitCost next A As L k x) (t + 1) =
            (List.ofFn (fun e : Fin n =>
              wordSum
                (splitCost next A As L (k + 1) (next x e)) t)).sum := by
          simp only [wordSum]
          apply ofFn_sum_congr
          intro e
          apply wordSum_congr
          intro u
          exact splitCost_cons_of_not next A As L k x hx e u
        have hright :
          wordSum
              (fun u => 2 ^ ((k + wait next A x u) / L)) (t + 1) =
            (List.ofFn (fun e : Fin n =>
              wordSum
                (fun u =>
                  2 ^ (((k + 1) + wait next A (next x e) u) / L)) t)).sum := by
          simp only [wordSum]
          apply ofFn_sum_congr
          intro e
          apply wordSum_congr
          intro u
          rw [wait_cons_of_not next A x hx e u]
          have ha :
              k + Nat.succ (wait next A (next x e) u) =
                (k + 1) + wait next A (next x e) u := by
            omega
          rw [ha]
        rw [hleft, hright]
        calc
          (List.ofFn (fun e : Fin n =>
              wordSum
                (splitCost next A As L (k + 1) (next x e)) t)).sum
              ≤
            (List.ofFn (fun e : Fin n =>
              C * wordSum
                (fun u =>
                  2 ^ (((k + 1) + wait next A (next x e) u) / L)) t)).sum := by
                  apply ofFn_sum_le
                  intro e
                  exact ih (k + 1) (next x e)
          _ = C *
              (List.ofFn (fun e : Fin n =>
                wordSum
                  (fun u =>
                    2 ^ (((k + 1) + wait next A (next x e) u) / L)) t)).sum :=
              ofFn_sum_mul_left _ _

/-- Rounding the elapsed prefix and suffix separately costs one factor `2`. -/
theorem seqExp_le_splitCost {α : Type} {n : Nat}
    (next : α → Fin n → α) (A : α → Prop)
    (As : List (α → Prop)) (L : Nat) (hL : 1 ≤ L) :
    ∀ k x u,
      2 ^ ((k + seqWait next (A :: As) x u) / L) ≤
        2 * splitCost next A As L k x u := by
  intro k x u
  induction u generalizing k x with
  | nil =>
      by_cases hx : A x
      · simpa [splitCost, hx, seqWait_nil] using
          (two_pow_floor_add k 0 L hL)
      · simpa [splitCost, hx, seqWait_nil] using
          (two_pow_floor_add k 0 L hL)
  | cons e u ih =>
      by_cases hx : A x
      · rw [seqWait_cons_of_hit next A As x hx (e :: u)]
        rw [splitCost_of_hit next A As L k x hx (e :: u)]
        exact two_pow_floor_add k (seqWait next As x (e :: u)) L hL
      · rw [seqWait_cons_step next A As x hx e u]
        rw [splitCost_cons_of_not next A As L k x hx e u]
        have hi := ih (k + 1) (next x e)
        simpa [Nat.add_assoc] using hi

/-- General successive-query bound. The constant `4` per query consists
of the one-query factor `2` and one floor-division carry factor `2`. -/
theorem moment_queries_raw {α : Type} {n : Nat}
    (next : α → Fin n → α) (L : Nat) (hL : 1 ≤ L)
    (queries : List (α → Prop))
    (hMoment : ∀ A, A ∈ queries → ∀ x, MomentAt next A L x) :
    ∀ x t,
      wordSum (fun u => 2 ^ (seqWait next queries x u / L)) t
        ≤ 4 ^ queries.length * n ^ t := by
  induction queries with
  | nil =>
      intro x t
      have heq :
          wordSum (fun u => 2 ^ (seqWait next [] x u / L)) t =
            wordSum (fun _ : Word n => 1) t := by
        apply wordSum_congr
        intro u
        rw [seqWait_no_queries]
        simp
      rw [heq, wordSum_const_one]
      simp
  | cons A As ih =>
      intro x t
      have hMomentTail :
          ∀ B, B ∈ As → ∀ y, MomentAt next B L y := by
        intro B hB y
        exact hMoment B (by simp [hB]) y
      have hTail : ∀ y r,
          wordSum (fun u => 2 ^ (seqWait next As y u / L)) r
            ≤ 4 ^ As.length * n ^ r :=
        ih hMomentTail
      have hCpos : 0 < 4 ^ As.length :=
        Nat.pow_pos (by omega)
      have hC : 1 ≤ 4 ^ As.length := by omega
      have hsplit := splitCost_sum_le next A As L
        (4 ^ As.length) hTail hC 0 x t
      have hsplit' :
          wordSum (splitCost next A As L 0 x) t ≤
            4 ^ As.length *
              wordSum (fun u => 2 ^ (wait next A x u / L)) t := by
        simpa using hsplit
      have hpoint : ∀ u,
          2 ^ (seqWait next (A :: As) x u / L) ≤
            2 * splitCost next A As L 0 x u := by
        intro u
        simpa using
          (seqExp_le_splitCost next A As L hL 0 x u)
      have hpref :
          wordSum (fun u => 2 ^ (seqWait next (A :: As) x u / L)) t
            ≤ 2 * wordSum (splitCost next A As L 0 x) t := by
        calc
          wordSum
              (fun u => 2 ^ (seqWait next (A :: As) x u / L)) t
              ≤ wordSum
                  (fun u => 2 * splitCost next A As L 0 x u) t :=
                wordSum_mono _ _ hpoint t
          _ = 2 * wordSum (splitCost next A As L 0 x) t :=
                wordSum_mul_left _ _ _
      have hfirst := momentAt_raw next A L x
        (hMoment A (by simp) x) t
      calc
        wordSum (fun u => 2 ^ (seqWait next (A :: As) x u / L)) t
            ≤ 2 * wordSum (splitCost next A As L 0 x) t := hpref
        _ ≤ 2 * (4 ^ As.length *
              wordSum (fun u => 2 ^ (wait next A x u / L)) t) :=
            Nat.mul_le_mul_left 2 hsplit'
        _ ≤ 2 * (4 ^ As.length * (2 * n ^ t)) :=
            Nat.mul_le_mul_left 2
              (Nat.mul_le_mul_left (4 ^ As.length) hfirst)
        _ = 4 ^ (A :: As).length * n ^ t := by
            simp only [List.length_cons, Nat.pow_succ]
            rw [show (4 : Nat) = 2 * 2 by decide]
            ac_rfl

theorem moment_queries {α : Type} {n : Nat}
    (next : α → Fin n → α) (L : Nat) (hL : 1 ≤ L)
    (queries : List (α → Prop))
    (hMoment : ∀ A, A ∈ queries → ∀ x, MomentAt next A L x)
    (x : α) (t : Nat) :
    wordSum
        (fun u => 2 ^ (Nat.min (seqWait next queries x u) t / L)) t
      ≤ 4 ^ queries.length * n ^ t := by
  rw [seqMoment_trunc_eq_raw next queries L t x]
  exact moment_queries_raw next L hL queries hMoment x t

/-- Two successive queries: `2 * 2 * 2 = 8`, where the third factor
is the floor-division carry. -/
theorem moment_seq {α : Type} {n : Nat}
    (next : α → Fin n → α) (Aone Atwo : α → Prop)
    (L : Nat) (hL : 1 ≤ L)
    (hOne : ∀ x, MomentAt next Aone L x)
    (hTwo : ∀ x, MomentAt next Atwo L x)
    (x : α) (t : Nat) :
    wordSum
        (fun u =>
          2 ^ (Nat.min (seqWait next [Aone, Atwo] x u) t / L)) t
      ≤ 8 * n ^ t := by
  have hTail : ∀ y r,
      wordSum
          (fun u => 2 ^ (seqWait next [Atwo] y u / L)) r
        ≤ 2 * n ^ r := by
    intro y r
    simpa [seqWait_single] using
      (momentAt_raw next Atwo L y (hTwo y) r)
  have hsplit := splitCost_sum_le next Aone [Atwo] L 2
    hTail (by omega) 0 x t
  have hsplit' :
      wordSum (splitCost next Aone [Atwo] L 0 x) t ≤
        2 * wordSum (fun u => 2 ^ (wait next Aone x u / L)) t := by
    simpa using hsplit
  have hpoint : ∀ u,
      2 ^ (seqWait next [Aone, Atwo] x u / L) ≤
        2 * splitCost next Aone [Atwo] L 0 x u := by
    intro u
    simpa using
      (seqExp_le_splitCost next Aone [Atwo] L hL 0 x u)
  have hpref :
      wordSum
          (fun u => 2 ^ (seqWait next [Aone, Atwo] x u / L)) t
        ≤ 2 * wordSum (splitCost next Aone [Atwo] L 0 x) t := by
    calc
      wordSum
          (fun u => 2 ^ (seqWait next [Aone, Atwo] x u / L)) t
          ≤ wordSum
              (fun u => 2 * splitCost next Aone [Atwo] L 0 x u) t :=
            wordSum_mono _ _ hpoint t
      _ = 2 * wordSum (splitCost next Aone [Atwo] L 0 x) t :=
            wordSum_mul_left _ _ _
  have hfirst := momentAt_raw next Aone L x (hOne x) t
  have hraw :
      wordSum
          (fun u => 2 ^ (seqWait next [Aone, Atwo] x u / L)) t
        ≤ 8 * n ^ t := by
    calc
      wordSum
          (fun u => 2 ^ (seqWait next [Aone, Atwo] x u / L)) t
          ≤ 2 * wordSum (splitCost next Aone [Atwo] L 0 x) t := hpref
      _ ≤ 2 * (2 *
            wordSum (fun u => 2 ^ (wait next Aone x u / L)) t) :=
          Nat.mul_le_mul_left 2 hsplit'
      _ ≤ 2 * (2 * (2 * n ^ t)) :=
          Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left 2 hfirst)
      _ = 8 * n ^ t := by
          rw [show (8 : Nat) = 2 * 2 * 2 by decide]
          ac_rfl
  rw [seqMoment_trunc_eq_raw next [Aone, Atwo] L t x]
  exact hraw

/-- Pointwise maximum of a nonempty family of waiting-time functions. -/
def maxWait {n : Nat} : List (Word n → Nat) → Word n → Nat
  | [], _ => 0
  | W :: Ws, u => Nat.max (W u) (maxWait Ws u)

/-- Sum of the individual truncated exponential integrands. -/
def momentSum {n : Nat} :
    List (Word n → Nat) → Nat → Nat → Word n → Nat
  | [], _, _, _ => 0
  | W :: Ws, L, t, u =>
      2 ^ (Nat.min (W u) t / L) + momentSum Ws L t u

theorem maxExp_le_momentSum {n : Nat}
    (Ws : List (Word n → Nat)) (hne : Ws ≠ [])
    (L t : Nat) (u : Word n) :
    2 ^ (Nat.min (maxWait Ws u) t / L) ≤ momentSum Ws L t u := by
  induction Ws with
  | nil =>
      exact False.elim (hne rfl)
  | cons W Ws ih =>
      cases Ws with
      | nil =>
          simp [maxWait, momentSum]
      | cons V Vs =>
          have htail := ih (by simp)
          by_cases hw : W u ≤ maxWait (V :: Vs) u
          · have hmax :
                Nat.max (W u) (maxWait (V :: Vs) u) =
                  maxWait (V :: Vs) u :=
              Nat.max_eq_right hw
            change
              2 ^ (Nat.min
                (Nat.max (W u) (maxWait (V :: Vs) u)) t / L) ≤
                2 ^ (Nat.min (W u) t / L) +
                  momentSum (V :: Vs) L t u
            calc
              2 ^ (Nat.min
                  (Nat.max (W u) (maxWait (V :: Vs) u)) t / L) =
                  2 ^ (Nat.min (maxWait (V :: Vs) u) t / L) := by
                    exact congrArg
                      (fun z => 2 ^ (Nat.min z t / L)) hmax
              _ ≤ momentSum (V :: Vs) L t u := htail
              _ ≤ 2 ^ (Nat.min (W u) t / L) +
                    momentSum (V :: Vs) L t u :=
                  Nat.le_add_left _ _
          · have hw' : maxWait (V :: Vs) u ≤ W u := by omega
            have hmax :
                Nat.max (W u) (maxWait (V :: Vs) u) = W u :=
              Nat.max_eq_left hw'
            change
              2 ^ (Nat.min
                (Nat.max (W u) (maxWait (V :: Vs) u)) t / L) ≤
                2 ^ (Nat.min (W u) t / L) +
                  momentSum (V :: Vs) L t u
            calc
              2 ^ (Nat.min
                  (Nat.max (W u) (maxWait (V :: Vs) u)) t / L) =
                  2 ^ (Nat.min (W u) t / L) := by
                    exact congrArg
                      (fun z => 2 ^ (Nat.min z t / L)) hmax
              _ ≤ 2 ^ (Nat.min (W u) t / L) +
                    momentSum (V :: Vs) L t u :=
                  Nat.le_add_right _ _

theorem wordSum_momentSum {n : Nat}
    (Ws : List (Word n → Nat)) (L cut horizon : Nat) :
    wordSum (momentSum Ws L cut) horizon =
      (Ws.map (fun W =>
        wordSum (fun u => 2 ^ (Nat.min (W u) cut / L)) horizon)).sum := by
  induction Ws with
  | nil =>
      simpa [momentSum] using
        (wordSum_const (n := n) 0 horizon)
  | cons W Ws ih =>
      simp only [momentSum, List.map_cons, List.sum_cons]
      rw [wordSum_add_fun, ih]

theorem max_moment_bound {n : Nat}
    (Ws : List (Word n → Nat)) (hne : Ws ≠ [])
    (L M t : Nat)
    (hEach : ∀ W, W ∈ Ws →
      wordSum (fun u => 2 ^ (Nat.min (W u) t / L)) t
        ≤ M * n ^ t) :
    wordSum
        (fun u => 2 ^ (Nat.min (maxWait Ws u) t / L)) t
      ≤ Ws.length * (M * n ^ t) := by
  have hp :
      wordSum
          (fun u => 2 ^ (Nat.min (maxWait Ws u) t / L)) t
        ≤ wordSum (momentSum Ws L t) t :=
    wordSum_mono _ _
      (fun u => maxExp_le_momentSum Ws hne L t u) t
  rw [wordSum_momentSum] at hp
  have hs :
      (Ws.map (fun W =>
        wordSum (fun u => 2 ^ (Nat.min (W u) t / L)) t)).sum
        ≤ Ws.length * (M * n ^ t) := by
    apply list_sum_map_le
    intro W hW
    exact hEach W hW
  exact Nat.le_trans hp hs

theorem self_le_two_pow (d : Nat) : d ≤ 2 ^ d := by
  induction d with
  | zero =>
      simp
  | succ d ih =>
      have hp0 : 0 < 2 ^ d := Nat.pow_pos (by omega)
      have hp : 1 ≤ 2 ^ d := by omega
      rw [Nat.pow_succ, Nat.mul_two]
      exact Nat.add_le_add ih hp

/-- Elementary inequality `2^a q ≤ 2^a a + 2^q`. -/
theorem scaled_index_le (a q : Nat) :
    2 ^ a * q ≤ 2 ^ a * a + 2 ^ q := by
  by_cases hq : q ≤ a
  · have hm := Nat.mul_le_mul_left (2 ^ a) hq
    exact Nat.le_trans hm (Nat.le_add_right _ _)
  · have haq : a < q := Nat.lt_of_not_ge hq
    have hexp : a + (q - a) = q := by omega
    have hd := self_le_two_pow (q - a)
    have hm := Nat.mul_le_mul_left (2 ^ a) hd
    calc
      2 ^ a * q = 2 ^ a * (a + (q - a)) := by rw [hexp]
      _ = 2 ^ a * a + 2 ^ a * (q - a) := by rw [Nat.mul_add]
      _ ≤ 2 ^ a * a + 2 ^ a * 2 ^ (q - a) :=
            Nat.add_le_add_left hm _
      _ = 2 ^ a * a + 2 ^ (a + (q - a)) := by
            rw [Nat.pow_add]
      _ = 2 ^ a * a + 2 ^ q := by rw [hexp]

theorem quotient_cover (z L : Nat) (hL : 1 ≤ L) :
    z ≤ L * (z / L + 1) := by
  have hpos : 0 < L := by omega
  have hdiv := Nat.mod_add_div z L
  have hmod := Nat.mod_lt z hpos
  calc
    z = z % L + L * (z / L) := hdiv.symm
    _ ≤ L + L * (z / L) :=
      Nat.add_le_add_right (Nat.le_of_lt hmod) _
    _ = L * (z / L + 1) := by
      rw [Nat.mul_add, Nat.mul_one]
      ac_rfl

/-- Deterministic exponential-to-linear inequality. -/
theorem scaled_value_le (z L a : Nat) (hL : 1 ≤ L) :
    2 ^ a * z ≤
      L * (2 ^ a * (a + 1) + 2 ^ (z / L)) := by
  have hz := quotient_cover z L hL
  have hzscaled := Nat.mul_le_mul_left (2 ^ a) hz
  have hq := scaled_index_le a (z / L)
  have hq' :
      2 ^ a * (z / L + 1) ≤
        2 ^ a * (a + 1) + 2 ^ (z / L) := by
    calc
      2 ^ a * (z / L + 1) =
          2 ^ a * (z / L) + 2 ^ a := by
            rw [Nat.mul_add, Nat.mul_one]
      _ ≤ (2 ^ a * a + 2 ^ (z / L)) + 2 ^ a :=
            Nat.add_le_add_right hq _
      _ = 2 ^ a * (a + 1) + 2 ^ (z / L) := by
            rw [Nat.mul_add, Nat.mul_one]
            ac_rfl
  calc
    2 ^ a * z
        ≤ 2 ^ a * (L * (z / L + 1)) := hzscaled
    _ = L * (2 ^ a * (z / L + 1)) := by ac_rfl
    _ ≤ L * (2 ^ a * (a + 1) + 2 ^ (z / L)) :=
      Nat.mul_le_mul_left L hq'

/-- If the exponential moment is at most `2^a`, then the counting
mean is at most `L(a+2)`. -/
theorem mean_of_moment {n : Nat}
    (Z : Word n → Nat) (L a horizon : Nat) (hL : 1 ≤ L)
    (hMoment :
      wordSum (fun u => 2 ^ (Z u / L)) horizon
        ≤ 2 ^ a * n ^ horizon) :
    wordSum Z horizon ≤ L * (a + 2) * n ^ horizon := by
  have hp : ∀ u,
      2 ^ a * Z u ≤
        L * (2 ^ a * (a + 1) + 2 ^ (Z u / L)) := by
    intro u
    exact scaled_value_le (Z u) L a hL
  have hs :
      2 ^ a * wordSum Z horizon ≤
        L * (2 ^ a * (a + 1) * n ^ horizon +
          wordSum (fun u => 2 ^ (Z u / L)) horizon) := by
    calc
      2 ^ a * wordSum Z horizon =
          wordSum (fun u => 2 ^ a * Z u) horizon :=
              (wordSum_mul_left _ _ _).symm
      _ ≤ wordSum
            (fun u =>
              L * (2 ^ a * (a + 1) + 2 ^ (Z u / L))) horizon :=
          wordSum_mono _ _ hp horizon
      _ = L * wordSum
            (fun u => 2 ^ a * (a + 1) + 2 ^ (Z u / L)) horizon :=
          wordSum_mul_left _ _ _
      _ = L *
            (wordSum (fun _ : Word n => 2 ^ a * (a + 1)) horizon +
              wordSum (fun u => 2 ^ (Z u / L)) horizon) := by
          rw [wordSum_add_fun]
      _ = L * (2 ^ a * (a + 1) * n ^ horizon +
            wordSum (fun u => 2 ^ (Z u / L)) horizon) := by
          rw [wordSum_const]
  have hcoef :
      2 ^ a * (a + 1) + 2 ^ a =
        2 ^ a * (a + 2) := by
    calc
      2 ^ a * (a + 1) + 2 ^ a =
          2 ^ a * (a + 1) + 2 ^ a * 1 := by
            rw [Nat.mul_one]
      _ = 2 ^ a * ((a + 1) + 1) :=
            (Nat.mul_add (2 ^ a) (a + 1) 1).symm
      _ = 2 ^ a * (a + 2) := by
            have ha : (a + 1) + 1 = a + 2 := by omega
            rw [ha]
  have halg :
      L * (2 ^ a * (a + 1) * n ^ horizon +
          2 ^ a * n ^ horizon) =
        2 ^ a * (L * (a + 2) * n ^ horizon) := by
    calc
      L * (2 ^ a * (a + 1) * n ^ horizon +
          2 ^ a * n ^ horizon) =
          L * ((2 ^ a * (a + 1) + 2 ^ a) * n ^ horizon) := by
            rw [Nat.add_mul]
      _ = L * ((2 ^ a * (a + 2)) * n ^ horizon) := by
            rw [hcoef]
      _ = 2 ^ a * (L * (a + 2) * n ^ horizon) := by ac_rfl
  have hs' :
      2 ^ a * wordSum Z horizon ≤
        2 ^ a * (L * (a + 2) * n ^ horizon) := by
    calc
      2 ^ a * wordSum Z horizon
          ≤ L * (2 ^ a * (a + 1) * n ^ horizon +
              wordSum (fun u => 2 ^ (Z u / L)) horizon) := hs
      _ ≤ L * (2 ^ a * (a + 1) * n ^ horizon +
              2 ^ a * n ^ horizon) :=
          Nat.mul_le_mul_left L
            (Nat.add_le_add_left hMoment _)
      _ = 2 ^ a * (L * (a + 2) * n ^ horizon) := halg
  exact Nat.le_of_mul_le_mul_left hs'
    (Nat.two_pow_pos a)

/-- Mean of the truncated maximum. The additive constant is `4`:
two bits cover `N*M`, and two more come from `mean_of_moment`. -/
theorem mean_max {n : Nat}
    (Ws : List (Word n → Nat)) (N M L t : Nat)
    (hLength : Ws.length = N)
    (hN : 1 ≤ N) (hM : 1 ≤ M) (hL : 1 ≤ L)
    (hEach : ∀ W, W ∈ Ws →
      wordSum (fun u => 2 ^ (Nat.min (W u) t / L)) t
        ≤ M * n ^ t) :
    wordSum (fun u => Nat.min (maxWait Ws u) t) t ≤
      L * (Nat.log2 N + Nat.log2 M + 4) * n ^ t := by
  have hne : Ws ≠ [] := by
    intro he
    rw [he] at hLength
    simp at hLength
    omega
  have hmax := max_moment_bound Ws hne L M t hEach
  have hmax' :
      wordSum
          (fun u => 2 ^ (Nat.min (maxWait Ws u) t / L)) t
        ≤ N * M * n ^ t := by
    calc
      wordSum
          (fun u => 2 ^ (Nat.min (maxWait Ws u) t / L)) t
          ≤ Ws.length * (M * n ^ t) := hmax
      _ = N * M * n ^ t := by
          rw [hLength]
          ac_rfl
  let a := (Nat.log2 N + 1) + (Nat.log2 M + 1)
  have hNzero : N ≠ 0 := by omega
  have hMzero : M ≠ 0 := by omega
  have hNpow : N ≤ 2 ^ (Nat.log2 N + 1) := by
    exact Nat.le_of_lt ((Nat.log2_eq_iff hNzero).1 rfl).2
  have hMpow : M ≤ 2 ^ (Nat.log2 M + 1) := by
    exact Nat.le_of_lt ((Nat.log2_eq_iff hMzero).1 rfl).2
  have hNM : N * M ≤ 2 ^ a := by
    calc
      N * M
          ≤ 2 ^ (Nat.log2 N + 1) *
              2 ^ (Nat.log2 M + 1) :=
            Nat.mul_le_mul hNpow hMpow
      _ = 2 ^ a := by
            dsimp [a]
            rw [← Nat.pow_add]
  have hexp :
      wordSum
          (fun u => 2 ^ (Nat.min (maxWait Ws u) t / L)) t
        ≤ 2 ^ a * n ^ t := by
    exact Nat.le_trans hmax'
      (Nat.mul_le_mul_right (n ^ t) hNM)
  have hmean := mean_of_moment
    (fun u => Nat.min (maxWait Ws u) t) L a t hL hexp
  have ha : a + 2 = Nat.log2 N + Nat.log2 M + 4 := by
    dsimp [a]
    omega
  rw [ha] at hmean
  exact hmean

/-- The three choices `-1,0,+1` are represented by `Fin 3`. -/
theorem step_path_count (h : Nat) :
    wordSum (n := 3) (fun _ : Word 3 => 1) h = 3 ^ h :=
  wordSum_const_one h

/-- `m` initial sites and `3^h` step words give exactly `m*3^h`
rooted paths. -/
def rootedPathCount (m h : Nat) : Nat :=
  m * wordSum (n := 3) (fun _ : Word 3 => 1) h

theorem rooted_path_count (m h : Nat) :
    rootedPathCount m h = m * 3 ^ h := by
  unfold rootedPathCount
  rw [step_path_count]

theorem path_family_bound (N m h : Nat)
    (hBound : N ≤ rootedPathCount m h) :
    N ≤ m * 3 ^ h := by
  rw [rooted_path_count] at hBound
  exact hBound

#print axioms moment_seq
#print axioms moment_queries
#print axioms mean_max
#print axioms step_path_count
#print axioms rooted_path_count

end

end Thru

end L4.Height
