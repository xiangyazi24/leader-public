import Leader.L4.Height.Critical
import Leader.L4.Height.Throughput

namespace L4.Height

open Classical

set_option maxRecDepth 8192
set_option maxHeartbeats 20000000

noncomputable section

private theorem ofFn_sum_eq_clock {n : Nat}
    (f g : Fin n → Nat) (h : ∀ i, f i = g i) :
    (List.ofFn f).sum = (List.ofFn g).sum := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.ofFn_succ, List.ofFn_succ,
        List.sum_cons, List.sum_cons, h 0]
      exact congrArg (g 0 + ·)
        (ih (fun i => f i.succ) (fun i => g i.succ)
          (fun i => h i.succ))

private theorem ofFn_sum_const_clock (n c : Nat) :
    (List.ofFn (fun _ : Fin n => c)).sum = n * c := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.ofFn_succ, List.sum_cons, ih, Nat.succ_mul]
      exact Nat.add_comm _ _

private theorem take_add_clock {β : Type}
    (u : List β) (a b : Nat) :
    u.take (a + b) = u.take a ++ (u.drop a).take b := by
  induction a generalizing u with
  | zero => simp
  | succ a ih =>
      cases u with
      | nil => simp
      | cons e u =>
          simp only [Nat.succ_add, List.take_succ_cons,
            List.drop_succ_cons, List.cons_append]
          exact congrArg (List.cons e) (ih u)

private theorem drop_add_clock {β : Type}
    (u : List β) (a b : Nat) :
    u.drop (a + b) = (u.drop a).drop b := by
  induction a generalizing u with
  | zero => simp
  | succ a ih =>
      cases u with
      | nil => simp
      | cons e u =>
          simp only [Nat.succ_add, List.drop_succ_cons]
          exact ih u

private theorem thru_runWord_append
    {α : Type} {n : Nat}
    (next : α → Fin n → α) (x : α)
    (u v : Thru.Word n) :
    Thru.runWord next x (u ++ v) =
      Thru.runWord next (Thru.runWord next x u) v := by
  induction u generalizing x with
  | nil => rfl
  | cons e u ih =>
      simp only [List.cons_append, Thru.runWord]
      exact ih (next x e)

private theorem runAt_add_clock
    {α : Type} {n : Nat}
    (next : α → Fin n → α) (x : α)
    (u : Thru.Word n) (a b : Nat) :
    Thru.runWord next x (u.take (a + b)) =
      Thru.runWord next
        (Thru.runWord next x (u.take a))
        ((u.drop a).take b) := by
  rw [take_add_clock, thru_runWord_append]

/-- One compulsory scheduler letter, followed by the first publication
visible to the ordinary waiting operator. On an exhausted word the
compulsory step is retained as the one-step sentinel. -/
noncomputable def strictDelay {α : Type} {n : Nat}
    (next : α → Fin n → α) (A : α → Prop)
    (x : α) (u : Thru.Word n) : Nat :=
  1 + Thru.wait next A
    (Thru.runWord next x (u.take 1)) (u.drop 1)

/-- Absolute first-service upper time used by the lifted recursion. -/
noncomputable def serviceTime {α : Type} {n m : Nat}
    (next : α → Fin n → α) (x : α)
    (served : Fin m → α → Prop) (u : Thru.Word n)
    (i : Fin m) (t : Nat) : Nat :=
  t + strictDelay next (served i)
    (Thru.runWord next x (u.take t)) (u.drop t)

theorem serviceTime_eq_requested {α : Type} {n m : Nat}
    (next : α → Fin n → α) (x : α)
    (served : Fin m → α → Prop) (u : Thru.Word n)
    (i : Fin m) (t : Nat) :
    serviceTime next x served u i t =
      t + 1 +
        Thru.wait next (served i)
          (Thru.runWord next x (u.take (t + 1)))
          (u.drop (t + 1)) := by
  unfold serviceTime strictDelay
  have hr := runAt_add_clock next x u t 1
  have hd := drop_add_clock u t 1
  rw [hr, hd]
  omega

theorem serviceTime_after {α : Type} {n m : Nat}
    (next : α → Fin n → α) (x : α)
    (served : Fin m → α → Prop) (u : Thru.Word n) :
    ∀ i t, t < serviceTime next x served u i t := by
  intro i t
  unfold serviceTime strictDelay
  omega

private theorem strictDelay_step {α : Type} {n : Nat}
    (next : α → Fin n → α) (A : α → Prop)
    (x : α) (u : Thru.Word n) :
    strictDelay next A x u ≤
      1 + strictDelay next A
        (Thru.runWord next x (u.take 1)) (u.drop 1) := by
  cases u with
  | nil =>
      simp [strictDelay, Thru.runWord, Thru.wait]
  | cons e u =>
      cases u with
      | nil =>
          simp [strictDelay, Thru.runWord, Thru.wait]
      | cons f v =>
          by_cases h : A (next x e)
          · simp [strictDelay, Thru.runWord, Thru.wait, h]
          · simp [strictDelay, Thru.runWord, Thru.wait, h]
            omega

private theorem serviceTime_succ {α : Type} {n m : Nat}
    (next : α → Fin n → α) (x : α)
    (served : Fin m → α → Prop) (u : Thru.Word n)
    (i : Fin m) (t : Nat) :
    serviceTime next x served u i t ≤
      serviceTime next x served u i (t + 1) := by
  let y := Thru.runWord next x (u.take t)
  let v := u.drop t
  have hs := strictDelay_step next (served i) y v
  have hr :
      Thru.runWord next x (u.take (t + 1)) =
        Thru.runWord next y (v.take 1) := by
    simpa only [y, v] using runAt_add_clock next x u t 1
  have hd : u.drop (t + 1) = v.drop 1 := by
    simpa only [v] using drop_add_clock u t 1
  change
    t + strictDelay next (served i) y v ≤
      (t + 1) + strictDelay next (served i)
        (Thru.runWord next x (u.take (t + 1)))
        (u.drop (t + 1))
  rw [hr, hd]
  have ha := Nat.add_le_add_left hs t
  simpa [Nat.add_assoc] using ha

theorem serviceTime_mono {α : Type} {n m : Nat}
    (next : α → Fin n → α) (x : α)
    (served : Fin m → α → Prop) (u : Thru.Word n) :
    ∀ i t t', t ≤ t' →
      serviceTime next x served u i t ≤
        serviceTime next x served u i t' := by
  intro i t t' htt
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le htt
  induction d with
  | zero => simp
  | succ d ih =>
      have htd : t ≤ t + d := by omega
      have ih' := ih htd
      exact Nat.le_trans ih' (by
        have hs := serviceTime_succ next x served u i (t + d)
        simpa [Nat.add_assoc] using hs)

/-- Execute one ordinary query and then an arbitrary continuation. -/
noncomputable def queryCompose {α : Type} {n : Nat}
    (next : α → Fin n → α) (A : α → Prop)
    (tail : α → Thru.Word n → Nat) :
    α → Thru.Word n → Nat
  | x, [] => tail x []
  | x, e :: u =>
      if A x then tail x (e :: u)
      else 1 + queryCompose next A tail (next x e) u

theorem queryCompose_eq_wait_tail {α : Type} {n : Nat}
    (next : α → Fin n → α) (A : α → Prop)
    (tail : α → Thru.Word n → Nat) :
    ∀ x u,
      queryCompose next A tail x u =
        Thru.wait next A x u +
          tail
            (Thru.runWord next x
              (u.take (Thru.wait next A x u)))
            (u.drop (Thru.wait next A x u)) := by
  intro x u
  induction u generalizing x with
  | nil =>
      simp [queryCompose, Thru.wait, Thru.runWord]
  | cons e u ih =>
      by_cases hx : A x
      · simp [queryCompose, Thru.wait, Thru.runWord, hx]
      · simp only [queryCompose, Thru.wait, hx, if_false]
        rw [ih (next x e)]
        simp only [List.take_succ_cons, List.drop_succ_cons,
          Thru.runWord]
        omega

/-- Successive strictly-later queries. -/
noncomputable def strictSeq {α : Type} {n : Nat}
    (next : α → Fin n → α) :
    List (α → Prop) → α → Thru.Word n → Nat
  | [], _, _ => 0
  | A :: As, x, [] => 1 + strictSeq next As x []
  | A :: As, x, e :: u =>
      1 + queryCompose next A (strictSeq next As) (next x e) u

theorem strictSeq_cons_formula {α : Type} {n : Nat}
    (next : α → Fin n → α) (A : α → Prop)
    (As : List (α → Prop)) (x : α) (u : Thru.Word n) :
    strictSeq next (A :: As) x u =
      strictDelay next A x u +
        strictSeq next As
          (Thru.runWord next x
            (u.take (strictDelay next A x u)))
          (u.drop (strictDelay next A x u)) := by
  cases u with
  | nil =>
      simp [strictSeq, strictDelay, Thru.runWord, Thru.wait]
  | cons e u =>
      let w := Thru.wait next A (next x e) u
      have hq := queryCompose_eq_wait_tail next A
        (strictSeq next As) (next x e) u
      have hd : strictDelay next A x (e :: u) = 1 + w := by
        simp [strictDelay, Thru.runWord, w]
      simp only [strictSeq]
      rw [hq]
      simp only [hd]
      have hw : 1 + w = Nat.succ w := by omega
      simp only [hw, List.take_succ_cons, List.drop_succ_cons,
        Thru.runWord, w]
      omega

/-- Exponential split cost for an ordinary query followed by an arbitrary
continuation. -/
noncomputable def tailSplitCost {α : Type} {n : Nat}
    (next : α → Fin n → α) (A : α → Prop)
    (tail : α → Thru.Word n → Nat) (L : Nat) :
    Nat → α → Thru.Word n → Nat
  | k, x, [] => 2 ^ (k / L) * 2 ^ (tail x [] / L)
  | k, x, e :: u =>
      if A x then 2 ^ (k / L) * 2 ^ (tail x (e :: u) / L)
      else tailSplitCost next A tail L (k + 1) (next x e) u

private theorem tailSplitCost_sum_le {α : Type} {n : Nat}
    (next : α → Fin n → α) (A : α → Prop)
    (tail : α → Thru.Word n → Nat) (L C : Nat)
    (hTail : ∀ y r,
      Thru.wordSum (fun u => 2 ^ (tail y u / L)) r ≤
        C * n ^ r) :
    ∀ k x t,
      Thru.wordSum (tailSplitCost next A tail L k x) t ≤
        C * Thru.wordSum
          (fun u => 2 ^ ((k + Thru.wait next A x u) / L)) t := by
  intro k x t
  induction t generalizing k x with
  | zero =>
      have ht := hTail x 0
      simp only [Thru.wordSum, Nat.pow_zero, Nat.mul_one] at ht ⊢
      calc
        2 ^ (k / L) * 2 ^ (tail x [] / L) ≤
            2 ^ (k / L) * C := Nat.mul_le_mul_left _ ht
        _ = C * 2 ^ (k / L) := Nat.mul_comm _ _
  | succ t ih =>
      by_cases hx : A x
      · have hleft :
          Thru.wordSum (tailSplitCost next A tail L k x) (t + 1) =
            2 ^ (k / L) *
              Thru.wordSum (fun u => 2 ^ (tail x u / L)) (t + 1) := by
          calc
            Thru.wordSum (tailSplitCost next A tail L k x) (t + 1) =
                Thru.wordSum
                  (fun u => 2 ^ (k / L) * 2 ^ (tail x u / L))
                  (t + 1) := by
                    apply Thru.wordSum_congr
                    intro u
                    cases u with
                    | nil => rfl
                    | cons e u => simp [tailSplitCost, hx]
            _ = 2 ^ (k / L) *
                Thru.wordSum (fun u => 2 ^ (tail x u / L)) (t + 1) :=
              Thru.wordSum_mul_left _ _ _
        have hright :
          Thru.wordSum
              (fun u => 2 ^ ((k + Thru.wait next A x u) / L))
              (t + 1) =
            2 ^ (k / L) * n ^ (t + 1) := by
          calc
            Thru.wordSum
                (fun u => 2 ^ ((k + Thru.wait next A x u) / L))
                (t + 1) =
              Thru.wordSum (fun _ : Thru.Word n => 2 ^ (k / L))
                (t + 1) := by
                  apply Thru.wordSum_congr
                  intro u
                  rw [Thru.wait_of_hit next A x hx u]
                  simp
            _ = 2 ^ (k / L) * n ^ (t + 1) :=
              Thru.wordSum_const _ _
        rw [hleft, hright]
        have ht := hTail x (t + 1)
        calc
          2 ^ (k / L) *
              Thru.wordSum (fun u => 2 ^ (tail x u / L)) (t + 1) ≤
            2 ^ (k / L) * (C * n ^ (t + 1)) :=
              Nat.mul_le_mul_left _ ht
          _ = C * (2 ^ (k / L) * n ^ (t + 1)) := by ac_rfl
      · have hleft :
          Thru.wordSum (tailSplitCost next A tail L k x) (t + 1) =
            (List.ofFn (fun e : Fin n =>
              Thru.wordSum
                (tailSplitCost next A tail L (k + 1) (next x e)) t)).sum := by
          simp only [Thru.wordSum]
          apply ofFn_sum_eq_clock
          intro e
          apply Thru.wordSum_congr
          intro u
          simp [tailSplitCost, hx]
        have hright :
          Thru.wordSum
              (fun u => 2 ^ ((k + Thru.wait next A x u) / L))
              (t + 1) =
            (List.ofFn (fun e : Fin n =>
              Thru.wordSum
                (fun u =>
                  2 ^ (((k + 1) +
                    Thru.wait next A (next x e) u) / L)) t)).sum := by
          simp only [Thru.wordSum]
          apply ofFn_sum_eq_clock
          intro e
          apply Thru.wordSum_congr
          intro u
          rw [Thru.wait_cons_of_not next A x hx e u]
          congr 2
          omega
        rw [hleft, hright]
        calc
          (List.ofFn (fun e : Fin n =>
              Thru.wordSum
                (tailSplitCost next A tail L (k + 1) (next x e)) t)).sum ≤
            (List.ofFn (fun e : Fin n =>
              C * Thru.wordSum
                (fun u =>
                  2 ^ (((k + 1) +
                    Thru.wait next A (next x e) u) / L)) t)).sum := by
              apply Thru.ofFn_sum_le
              intro e
              exact ih (k + 1) (next x e)
          _ = C *
              (List.ofFn (fun e : Fin n =>
                Thru.wordSum
                  (fun u =>
                    2 ^ (((k + 1) +
                      Thru.wait next A (next x e) u) / L)) t)).sum :=
            Thru.ofFn_sum_mul_left _ _

private theorem queryCompose_exp_le_split {α : Type} {n : Nat}
    (next : α → Fin n → α) (A : α → Prop)
    (tail : α → Thru.Word n → Nat) (L : Nat) (hL : 1 ≤ L) :
    ∀ k x u,
      2 ^ ((k + queryCompose next A tail x u) / L) ≤
        2 * tailSplitCost next A tail L k x u := by
  intro k x u
  induction u generalizing k x with
  | nil =>
      simpa [queryCompose, tailSplitCost] using
        (Thru.two_pow_floor_add k (tail x []) L hL)
  | cons e u ih =>
      by_cases hx : A x
      · simpa [queryCompose, tailSplitCost, hx] using
          (Thru.two_pow_floor_add k (tail x (e :: u)) L hL)
      · have hi := ih (k + 1) (next x e)
        simpa [queryCompose, tailSplitCost, hx, Nat.add_assoc] using hi

private theorem queryCompose_moment_raw {α : Type} {n : Nat}
    (next : α → Fin n → α) (A : α → Prop)
    (tail : α → Thru.Word n → Nat)
    (L C : Nat) (hL : 1 ≤ L)
    (hTail : ∀ y r,
      Thru.wordSum (fun u => 2 ^ (tail y u / L)) r ≤
        C * n ^ r)
    (hMoment : ∀ y, Thru.MomentAt next A L y) :
    ∀ x t,
      Thru.wordSum
          (fun u => 2 ^ (queryCompose next A tail x u / L)) t ≤
        4 * C * n ^ t := by
  intro x t
  have hs := tailSplitCost_sum_le next A tail L C hTail 0 x t
  have hs' :
      Thru.wordSum (tailSplitCost next A tail L 0 x) t ≤
        C * Thru.wordSum
          (fun u => 2 ^ (Thru.wait next A x u / L)) t := by
    simpa using hs
  have hp : ∀ u,
      2 ^ (queryCompose next A tail x u / L) ≤
        2 * tailSplitCost next A tail L 0 x u := by
    intro u
    simpa using queryCompose_exp_le_split next A tail L hL 0 x u
  have hpref :
      Thru.wordSum
          (fun u => 2 ^ (queryCompose next A tail x u / L)) t ≤
        2 * Thru.wordSum (tailSplitCost next A tail L 0 x) t := by
    calc
      Thru.wordSum
          (fun u => 2 ^ (queryCompose next A tail x u / L)) t ≤
        Thru.wordSum
          (fun u => 2 * tailSplitCost next A tail L 0 x u) t :=
            Thru.wordSum_mono _ _ hp t
      _ = 2 * Thru.wordSum (tailSplitCost next A tail L 0 x) t :=
        Thru.wordSum_mul_left _ _ _
  have hfirst := Thru.momentAt_raw next A L x (hMoment x) t
  calc
    Thru.wordSum
        (fun u => 2 ^ (queryCompose next A tail x u / L)) t ≤
      2 * Thru.wordSum (tailSplitCost next A tail L 0 x) t := hpref
    _ ≤ 2 * (C *
        Thru.wordSum (fun u => 2 ^ (Thru.wait next A x u / L)) t) :=
      Nat.mul_le_mul_left 2 hs'
    _ ≤ 2 * (C * (2 * n ^ t)) :=
      Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left C hfirst)
    _ = (2 * 2) * C * n ^ t := by ac_rfl
    _ = 4 * C * n ^ t := by rfl

private theorem one_plus_exp_le_four (q L : Nat) (hL : 1 ≤ L) :
    2 ^ ((1 + q) / L) ≤ 4 * 2 ^ (q / L) := by
  have hsplit := Thru.two_pow_floor_add 1 q L hL
  have hdiv : 1 / L ≤ 1 := Nat.div_le_self 1 L
  have hp : 2 ^ (1 / L) ≤ 2 := by
    simpa using Nat.pow_le_pow_right (by omega : 0 < (2 : Nat)) hdiv
  calc
    2 ^ ((1 + q) / L) ≤
        2 * (2 ^ (1 / L) * 2 ^ (q / L)) := hsplit
    _ ≤ 2 * (2 * 2 ^ (q / L)) :=
      Nat.mul_le_mul_left 2 (Nat.mul_le_mul_right _ hp)
    _ = (2 * 2) * 2 ^ (q / L) :=
      (Nat.mul_assoc 2 2 (2 ^ (q / L))).symm
    _ = 4 * 2 ^ (q / L) := by rfl

theorem strictSeq_moment_raw {α : Type} {n : Nat}
    (next : α → Fin n → α) (L : Nat) (hL : 1 ≤ L)
    (queries : List (α → Prop))
    (hMoment : ∀ A, A ∈ queries → ∀ x,
      Thru.MomentAt next A L x) :
    ∀ x t,
      Thru.wordSum
          (fun u => 2 ^ (strictSeq next queries x u / L)) t ≤
        16 ^ queries.length * n ^ t := by
  induction queries with
  | nil =>
      intro x t
      simpa [strictSeq] using
        (Nat.le_of_eq (Thru.wordSum_const_one (n := n) t))
  | cons A As ih =>
      intro x t
      have hMomentTail : ∀ B, B ∈ As → ∀ y,
          Thru.MomentAt next B L y := by
        intro B hB y
        exact hMoment B (by simp [hB]) y
      have hTail : ∀ y r,
          Thru.wordSum
              (fun u => 2 ^ (strictSeq next As y u / L)) r ≤
            16 ^ As.length * n ^ r := ih hMomentTail
      have hQuery : ∀ y r,
          Thru.wordSum
              (fun u => 2 ^
                (queryCompose next A (strictSeq next As) y u / L)) r ≤
            4 * (16 ^ As.length) * n ^ r :=
        queryCompose_moment_raw next A (strictSeq next As)
          L (16 ^ As.length) hL hTail
          (fun y => hMoment A (by simp) y)
      cases t with
      | zero =>
          have ht := hTail x 0
          simp only [Thru.wordSum, Nat.pow_zero, Nat.mul_one] at ht ⊢
          have hp := one_plus_exp_le_four
            (strictSeq next As x []) L hL
          calc
            2 ^ ((1 + strictSeq next As x []) / L) ≤
                4 * 2 ^ (strictSeq next As x [] / L) := hp
            _ ≤ 4 * 16 ^ As.length := Nat.mul_le_mul_left 4 ht
            _ ≤ 16 * 16 ^ As.length :=
              Nat.mul_le_mul_right (16 ^ As.length) (by decide : 4 ≤ 16)
            _ = 16 ^ (A :: As).length := by
              simp only [List.length_cons, Nat.pow_succ]
              ac_rfl
      | succ t =>
          simp only [Thru.wordSum]
          calc
            (List.ofFn (fun e : Fin n =>
              Thru.wordSum
                (fun v =>
                  2 ^ (strictSeq next (A :: As) x (e :: v) / L)) t)).sum ≤
              (List.ofFn (fun _ : Fin n =>
                16 * (16 ^ As.length * n ^ t))).sum := by
                  apply Thru.ofFn_sum_le
                  intro e
                  have hp : ∀ v,
                      2 ^ (strictSeq next (A :: As) x (e :: v) / L) ≤
                        4 * 2 ^
                          (queryCompose next A (strictSeq next As)
                            (next x e) v / L) := by
                    intro v
                    simpa only [strictSeq] using
                      one_plus_exp_le_four
                        (queryCompose next A (strictSeq next As)
                          (next x e) v) L hL
                  calc
                    Thru.wordSum
                        (fun v =>
                          2 ^ (strictSeq next (A :: As) x (e :: v) / L)) t ≤
                      Thru.wordSum
                        (fun v => 4 * 2 ^
                          (queryCompose next A (strictSeq next As)
                            (next x e) v / L)) t :=
                        Thru.wordSum_mono _ _ hp t
                    _ = 4 * Thru.wordSum
                        (fun v => 2 ^
                          (queryCompose next A (strictSeq next As)
                            (next x e) v / L)) t :=
                      Thru.wordSum_mul_left _ _ _
                    _ ≤ 4 * (4 * 16 ^ As.length * n ^ t) :=
                      Nat.mul_le_mul_left 4 (hQuery (next x e) t)
                    _ = (4 * 4) * (16 ^ As.length * n ^ t) := by ac_rfl
                    _ = 16 * (16 ^ As.length * n ^ t) := by rfl
            _ = n * (16 * (16 ^ As.length * n ^ t)) :=
              ofFn_sum_const_clock n _
            _ = 16 ^ (A :: As).length * n ^ (t + 1) := by
              simp only [List.length_cons, Nat.pow_succ]
              ac_rfl

theorem strictSeq_moment {α : Type} {n : Nat}
    (next : α → Fin n → α) (L : Nat) (hL : 1 ≤ L)
    (queries : List (α → Prop))
    (hMoment : ∀ A, A ∈ queries → ∀ x,
      Thru.MomentAt next A L x)
    (x : α) (t : Nat) :
    Thru.wordSum
        (fun u => 2 ^ (Nat.min (strictSeq next queries x u) t / L)) t ≤
      16 ^ queries.length * n ^ t := by
  calc
    Thru.wordSum
        (fun u => 2 ^ (Nat.min (strictSeq next queries x u) t / L)) t ≤
      Thru.wordSum
        (fun u => 2 ^ (strictSeq next queries x u / L)) t := by
          apply Thru.wordSum_mono
          intro u
          have hm : Nat.min (strictSeq next queries x u) t ≤
              strictSeq next queries x u := Nat.min_le_left _ _
          have hd :
              Nat.min (strictSeq next queries x u) t / L ≤
                strictSeq next queries x u / L :=
            Nat.div_le_div_right (c := L) hm
          exact Nat.pow_le_pow_right (by omega : 0 < (2 : Nat)) hd
    _ ≤ 16 ^ queries.length * n ^ t :=
      strictSeq_moment_raw next L hL queries hMoment x t

/-- Chronological sites queried by a critical path. -/
def pathSitesChrono {m : Nat} (hm : 0 < m) :
    Fin m → List (Fin 3) → List (Fin m)
  | _, [] => []
  | i, d :: ds =>
      pathSitesChrono hm (Depth.move hm i d) ds ++ [i]

def pathQueries {α : Type} {m : Nat} (hm : 0 < m)
    (served : Fin m → α → Prop) (i : Fin m)
    (ds : List (Fin 3)) : List (α → Prop) :=
  (pathSitesChrono hm i ds).map served

theorem pathSitesChrono_length {m : Nat} (hm : 0 < m)
    (i : Fin m) (ds : List (Fin 3)) :
    (pathSitesChrono hm i ds).length = ds.length := by
  induction ds generalizing i with
  | nil => rfl
  | cons d ds ih =>
      simp only [pathSitesChrono, List.length_append, ih,
        List.length_cons, List.length_nil, Nat.zero_add]

theorem pathQueries_length {α : Type} {m : Nat} (hm : 0 < m)
    (served : Fin m → α → Prop) (i : Fin m)
    (ds : List (Fin 3)) :
    (pathQueries hm served i ds).length = ds.length := by
  unfold pathQueries
  rw [List.length_map, pathSitesChrono_length]

/-- Apply site service functions in chronological order. -/
def timeFold {m : Nat} (S : Fin m → Nat → Nat) :
    Nat → List (Fin m) → Nat
  | t, [] => t
  | t, i :: is => timeFold S (S i t) is

private theorem timeFold_append {m : Nat}
    (S : Fin m → Nat → Nat) :
    ∀ t xs ys,
      timeFold S t (xs ++ ys) =
        timeFold S (timeFold S t xs) ys := by
  intro t xs
  induction xs generalizing t with
  | nil => intro ys; rfl
  | cons i is ih =>
      intro ys
      simp only [List.cons_append, timeFold]
      exact ih (S i t) ys

private theorem seqTime_eq_timeFold {m : Nat} (hm : 0 < m)
    (S : Fin m → Nat → Nat) (t0 : Nat) :
    ∀ i ds,
      Depth.seqTime hm S t0 i ds =
        timeFold S t0 (pathSitesChrono hm i ds) := by
  intro i ds
  induction ds generalizing i with
  | nil => rfl
  | cons d ds ih =>
      simp only [Depth.seqTime, pathSitesChrono]
      rw [timeFold_append, ih]
      rfl

private theorem timeFold_serviceTime
    {α : Type} {n m : Nat}
    (next : α → Fin n → α) (x : α)
    (served : Fin m → α → Prop) (u : Thru.Word n) :
    ∀ sites t,
      timeFold (serviceTime next x served u) t sites =
        t + strictSeq next (sites.map served)
          (Thru.runWord next x (u.take t)) (u.drop t) := by
  intro sites
  induction sites with
  | nil =>
      intro t
      simp [timeFold, strictSeq]
  | cons i is ih =>
      intro t
      simp only [timeFold, List.map_cons]
      rw [ih]
      let y := Thru.runWord next x (u.take t)
      let v := u.drop t
      let d := strictDelay next (served i) y v
      have hS : serviceTime next x served u i t = t + d := by rfl
      rw [hS]
      have hr := runAt_add_clock next x u t d
      have hd := drop_add_clock u t d
      rw [hr, hd]
      change
        (t + d) + strictSeq next (is.map served)
            (Thru.runWord next y (v.take d)) (v.drop d) =
          t + strictSeq next (served i :: is.map served) y v
      rw [strictSeq_cons_formula]
      simp only [d]
      omega

theorem seqTime_serviceTime_eq_strictSeq
    {α : Type} {n m : Nat} (hm : 0 < m)
    (next : α → Fin n → α) (x : α)
    (served : Fin m → α → Prop) (u : Thru.Word n)
    (i : Fin m) (ds : List (Fin 3)) :
    Depth.seqTime hm (serviceTime next x served u) 0 i ds =
      strictSeq next (pathQueries hm served i ds) x u := by
  rw [seqTime_eq_timeFold]
  rw [timeFold_serviceTime]
  simp [pathQueries, Thru.runWord]

private theorem allSteps_member_length {h : Nat}
    (ds : List (Fin 3)) (hd : ds ∈ Depth.allSteps h) :
    ds.length = h := by
  induction h generalizing ds with
  | zero =>
      simp [Depth.allSteps] at hd
      subst ds
      rfl
  | succ h ih =>
      simp only [Depth.allSteps, List.mem_append] at hd
      rcases hd with hleft | hrest
      · obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hleft
        simp only [List.length_cons, ih r hr]
      · rcases hrest with hmid | hright
        · obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hmid
          simp only [List.length_cons, ih r hr]
        · obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hright
          simp only [List.length_cons, ih r hr]

/-- All endpoint/path critical-time functions. -/
noncomputable def criticalFunctions
    {α : Type} {n m : Nat} (hm : 0 < m)
    (next : α → Fin n → α) (x : α)
    (served : Fin m → α → Prop) (h : Nat) :
    List (Thru.Word n → Nat) :=
  (List.finRange m).flatMap (fun i =>
    (Depth.allSteps h).map (fun ds => fun u =>
      Depth.seqTime hm (serviceTime next x served u) 0 i ds))

private theorem flatMap_length_clock {β γ : Type}
    (xs : List β) (f : β → List γ) (r : Nat)
    (hf : ∀ y, y ∈ xs → (f y).length = r) :
    (xs.flatMap f).length = xs.length * r := by
  induction xs with
  | nil => simp
  | cons y ys ih =>
      simp only [List.flatMap_cons, List.length_append,
        List.length_cons]
      rw [hf y (by simp)]
      rw [ih (by
        intro z hz
        exact hf z (by simp [hz]))]
      rw [Nat.add_mul, Nat.one_mul]
      exact Nat.add_comm _ _

theorem criticalFunctions_length
    {α : Type} {n m : Nat} (hm : 0 < m)
    (next : α → Fin n → α) (x : α)
    (served : Fin m → α → Prop) (h : Nat) :
    (criticalFunctions hm next x served h).length = m * 3 ^ h := by
  unfold criticalFunctions
  rw [flatMap_length_clock _ _ (3 ^ h) (by
    intro i hi
    simp only [List.length_map, Depth.allSteps_length])]
  simp only [List.length_finRange]

theorem criticalFunctions_moment
    {α : Type} {n m : Nat} (hm : 0 < m)
    (next : α → Fin n → α) (x : α)
    (served : Fin m → α → Prop) (L : Nat) (hL : 1 ≤ L)
    (hMoment : ∀ i y, Thru.MomentAt next (served i) L y)
    (h t : Nat) (W : Thru.Word n → Nat)
    (hW : W ∈ criticalFunctions hm next x served h) :
    Thru.wordSum (fun u => 2 ^ (Nat.min (W u) t / L)) t ≤
      16 ^ h * n ^ t := by
  unfold criticalFunctions at hW
  rw [List.mem_flatMap] at hW
  obtain ⟨i, hi, hWi⟩ := hW
  obtain ⟨ds, hds, rfl⟩ := List.mem_map.mp hWi
  have hlen := allSteps_member_length ds hds
  have hQueries : ∀ A, A ∈ pathQueries hm served i ds → ∀ y,
      Thru.MomentAt next A L y := by
    intro A hA y
    unfold pathQueries at hA
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hA
    exact hMoment j y
  have hs := strictSeq_moment next L hL
    (pathQueries hm served i ds) hQueries x t
  calc
    Thru.wordSum
        (fun u => 2 ^
          (Nat.min
            (Depth.seqTime hm (serviceTime next x served u) 0 i ds) t / L)) t =
      Thru.wordSum
        (fun u => 2 ^
          (Nat.min (strictSeq next (pathQueries hm served i ds) x u) t / L)) t := by
            apply Thru.wordSum_congr
            intro u
            rw [seqTime_serviceTime_eq_strictSeq]
    _ ≤ 16 ^ (pathQueries hm served i ds).length * n ^ t := hs
    _ = 16 ^ h * n ^ t := by
      rw [pathQueries_length, hlen]

private theorem le_maxWait_of_mem {n : Nat}
    (W : Thru.Word n → Nat) :
    ∀ Ws, W ∈ Ws → ∀ u, W u ≤ Thru.maxWait Ws u := by
  intro Ws hW u
  induction Ws with
  | nil => cases hW
  | cons V Vs ih =>
      simp only [List.mem_cons] at hW
      simp only [Thru.maxWait]
      rcases hW with rfl | htail
      · exact Nat.le_max_left _ _
      · exact Nat.le_trans (ih htail) (Nat.le_max_right _ _)

private theorem foldMax_le_of_all_clock
    (xs : List Nat) (B : Nat)
    (h : ∀ z, z ∈ xs → z ≤ B) :
    Depth.foldMax xs ≤ B := by
  induction xs with
  | nil => exact Nat.zero_le _
  | cons z zs ih =>
      simp only [Depth.foldMax, List.foldr_cons]
      apply (Nat.max_le).mpr
      constructor
      · exact h z (by simp)
      · apply ih
        intro q hq
        exact h q (by simp [hq])

private theorem criticalMaximum_le_maxWait
    {α : Type} {n m : Nat} (hm : 0 < m)
    (next : α → Fin n → α) (x : α)
    (served : Fin m → α → Prop) (h : Nat)
    (u : Thru.Word n) (i : Fin m) :
    Depth.criticalMaximum hm (serviceTime next x served u) 0 h i ≤
      Thru.maxWait (criticalFunctions hm next x served h) u := by
  unfold Depth.criticalMaximum Depth.criticalTimes
  apply foldMax_le_of_all_clock
  intro z hz
  obtain ⟨ds, hds, rfl⟩ := List.mem_map.mp hz
  apply le_maxWait_of_mem
    (fun v => Depth.seqTime hm (serviceTime next x served v) 0 i ds)
  · unfold criticalFunctions
    rw [List.mem_flatMap]
    refine ⟨i, List.mem_finRange i, ?_⟩
    exact List.mem_map.mpr ⟨ds, hds, rfl⟩

/-- Maximum lifted level over all sites. -/
def clockMaximum {n m : Nat}
    (T : Thru.Word n → Fin m → Nat → Nat)
    (h : Nat) (u : Thru.Word n) : Nat :=
  Depth.foldMax ((List.finRange m).map (fun i => T u i h))

private theorem min_mono_clock (a b cut : Nat) (h : a ≤ b) :
    Nat.min a cut ≤ Nat.min b cut := by
  apply Nat.le_min.mpr
  constructor
  · exact Nat.le_trans (Nat.min_le_left a cut) h
  · exact Nat.min_le_right a cut

private theorem clockMaximum_le_critical
    {α : Type} {n m : Nat} (hm : 0 < m)
    (next : α → Fin n → α) (x : α)
    (served : Fin m → α → Prop)
    (T : Thru.Word n → Fin m → Nat → Nat)
    (hrec : ∀ u i ℓ,
      T u i (ℓ + 1) ≤
        serviceTime next x served u i
          (max (max (T u (left hm i) ℓ) (T u i ℓ))
            (T u (right hm i) ℓ)))
    (hfloor : ∀ u j, T u j 0 ≤ 0)
    (h : Nat) (u : Thru.Word n) :
    clockMaximum T h u ≤
      Thru.maxWait (criticalFunctions hm next x served h) u := by
  unfold clockMaximum
  apply foldMax_le_of_all_clock
  intro z hz
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hz
  have hc := Depth.critical_bound hm
    (serviceTime next x served u) (T u) 0
    (serviceTime_after next x served u)
    (serviceTime_mono next x served u)
    (hrec u) (hfloor u) h i
  exact Nat.le_trans hc
    (criticalMaximum_le_maxWait hm next x served h u i)

/-- Counting-form conditional mean bound for reaching lifted depth `h`. -/
theorem clock_mean
    {α : Type} {n m : Nat} (hm : 0 < m)
    (next : α → Fin n → α) (x : α)
    (served : Fin m → α → Prop)
    (L : Nat) (hL : 1 ≤ L)
    (hMoment : ∀ i y, Thru.MomentAt next (served i) L y)
    (T : Thru.Word n → Fin m → Nat → Nat)
    (hrec : ∀ u i ℓ,
      T u i (ℓ + 1) ≤
        serviceTime next x served u i
          (max (max (T u (left hm i) ℓ) (T u i ℓ))
            (T u (right hm i) ℓ)))
    (hfloor : ∀ u j, T u j 0 ≤ 0)
    (h t : Nat) :
    Thru.wordSum (fun u => Nat.min (clockMaximum T h u) t) t ≤
      L * (Nat.log2 (m * 3 ^ h) + Nat.log2 (16 ^ h) + 4) * n ^ t := by
  let Ws := criticalFunctions hm next x served h
  have hLength : Ws.length = m * 3 ^ h := by
    simpa only [Ws] using criticalFunctions_length hm next x served h
  have hN : 1 ≤ m * 3 ^ h := by
    have hp : 0 < 3 ^ h := Nat.pow_pos (by decide)
    exact Nat.succ_le_of_lt (Nat.mul_pos hm hp)
  have hM : 1 ≤ 16 ^ h := by
    exact Nat.succ_le_of_lt (Nat.pow_pos (by decide))
  have hEach : ∀ W, W ∈ Ws →
      Thru.wordSum (fun u => 2 ^ (Nat.min (W u) t / L)) t ≤
        16 ^ h * n ^ t := by
    intro W hW
    exact criticalFunctions_moment hm next x served L hL hMoment
      h t W (by simpa only [Ws] using hW)
  have hmean := Thru.mean_max Ws
    (m * 3 ^ h) (16 ^ h) L t
    hLength hN hM hL hEach
  have hpoint : ∀ u,
      Nat.min (clockMaximum T h u) t ≤
        Nat.min (Thru.maxWait Ws u) t := by
    intro u
    apply min_mono_clock
    simpa only [Ws] using
      clockMaximum_le_critical hm next x served T hrec hfloor h u
  exact Nat.le_trans
    (Thru.wordSum_mono
      (fun u => Nat.min (clockMaximum T h u) t)
      (fun u => Nat.min (Thru.maxWait Ws u) t)
      hpoint t)
    hmean

end

end L4.Height
