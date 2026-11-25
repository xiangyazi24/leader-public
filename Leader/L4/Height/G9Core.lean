import Leader.L4.Height.ChainRepair
import Leader.Wu.Elimination.ArbitraryInputMissAccounting

/-!
# Publication service on the original scheduler

The finite-word form of the fixed-layout service argument in
paper's Lemma `service`. A positive-step publication probability
uniform over the current states gives the moment used by clock repair.
The physical row proof supplies that probability on the custody subtype.
-/

namespace L4.Height.RawService

open Classical
open K2ArbitraryElimination.FiniteAccounting (miss miss_zero repeat_miss)
open LeaderCountDyadicTail (half_life_contraction)

set_option autoImplicit false

noncomputable section

variable {α : Type} {n : Nat}

/-- Every visit to `A` after consuming a mark sets the service witness. -/
def publicationStep (next : α → Fin n → α) (A : α → Prop)
    (y : α × Bool) (e : Fin n) : α × Bool :=
  (next y.1 e, y.2 || decide (A (next y.1 e)))

private def done (y : α × Bool) : Prop := y.2 = true

private theorem done_closed (next : α → Fin n → α) (A : α → Prop) :
    ∀ y e, done y → done (publicationStep next A y e) := by
  intro y e hy
  change y.2 = true at hy
  simp [done, publicationStep, hy]

/-- The mass of words with a publication on a positive prefix, including
an identity publication with the same clock record. -/
def publicationMass (next : α → Fin n → α) (A : α → Prop)
    (x : α) (t : Nat) : Nat :=
  LeaderCountDyadicTail.wordSum (publicationStep next A)
    (fun y => if done y then 1 else 0) (x, false) t

private def missMass (next : α → Fin n → α) (A : α → Prop)
    (x : α) (t : Nat) : Nat :=
  LeaderCountDyadicTail.wordSum (publicationStep next A) (miss done) (x, false) t

private theorem mass_partition (next : α → Fin n → α) (A : α → Prop)
    (x : α) (t : Nat) :
    publicationMass next A x t + missMass next A x t = n ^ t := by
  unfold publicationMass missMass
  rw [← LeaderCountDyadicTail.wordSum_add]
  have hf : (fun y : α × Bool => (if done y then 1 else 0) + miss done y) =
      (fun _ => 1) := by
    funext y
    by_cases h : done y <;> simp [miss, h]
  rw [hf, LeaderCountDyadicTail.wordSum_const, Nat.mul_one]

/-- A success fraction of at least `1/d` in `H` marks gives a dyadic
tail in blocks of `d * H` marks by restarting at actual endpoints. -/
private theorem publication_miss_tail (next : α → Fin n → α) (A : α → Prop)
    (H d : Nat) (hd : 1 ≤ d)
    (hmass : ∀ x, n ^ H ≤ d * publicationMass next A x H)
    (x : α) (j : Nat) :
    2 ^ j * missMass next A x (j * (d * H)) ≤ n ^ (j * (d * H)) := by
  let step := publicationStep next A
  have hblock : ∀ y : α × Bool, True →
      d * LeaderCountDyadicTail.wordSum step (miss done) y H ≤
        (d - 1) * n ^ H * miss done y := by
    intro y _
    rcases y with ⟨x, b⟩
    cases b with
    | false =>
        have hsum := mass_partition next A x H
        have hd_eq : (d - 1) + 1 = d := by omega
        have hsplit : d * publicationMass next A x H + d * missMass next A x H =
            (d - 1) * n ^ H + n ^ H := by
          calc
            _ = d * n ^ H := by rw [← Nat.mul_add, hsum]
            _ = ((d - 1) + 1) * n ^ H := congrArg (fun v => v * n ^ H) hd_eq.symm
            _ = _ := by rw [Nat.add_mul, Nat.one_mul]
        change d * missMass next A x H ≤ (d - 1) * n ^ H * miss done (x, false)
        have hnone : ¬ done (x, false) := by simp [done]
        simp only [miss, if_neg hnone, Nat.mul_one]
        have h := hmass x
        omega
    | true =>
        have hy : done (x, true) := rfl
        rw [miss_zero step done (done_closed next A) (x, true) hy H]
        simp [miss, hy]
  have hhalf : ∀ y : α × Bool, True →
      2 * LeaderCountDyadicTail.wordSum step (miss done) y (d * H) ≤ n ^ (d * H) := by
    intro y _
    have h := half_life_contraction step (fun _ => True)
      (fun _ _ _ => True.intro) (miss done) H d hd hblock y True.intro
    have hw := K2ArbitraryElimination.FiniteAccounting.miss_le_one done y
    calc
      _ ≤ n ^ (d * H) * miss done y := h
      _ ≤ n ^ (d * H) * 1 := Nat.mul_le_mul_left _ hw
      _ = n ^ (d * H) := Nat.mul_one _
  exact repeat_miss step done (fun _ => True) (fun _ _ _ => True.intro)
    (done_closed next A) (d * H) 2 hhalf (x, false) True.intro j

private theorem endpoint_sum {β : Type} (next : β → Fin n → β)
    (f : β → Nat) (x : β) (t : Nat) :
    LeaderCountDyadicTail.wordSum next f x t =
      Thru.wordSum (fun u => f (Thru.runWord next x u)) t := by
  induction t generalizing x with
  | zero => rfl
  | succ t ih =>
      simp only [LeaderCountDyadicTail.wordSum_succ, Thru.wordSum, Thru.runWord]
      exact FiniteUniformStoppingTree.ofFn_sum_eq _ _ (fun e => ih (next x e))

/-- A publication witnessed by a nonempty prefix of the original word. -/
def hasPublication (next : α → Fin n → α) (A : α → Prop)
    (x : α) (u : Thru.Word n) : Prop :=
  ∃ j, 0 < j ∧ j ≤ u.length ∧ A (Thru.runWord next x (u.take j))

private theorem hasPublication_cons (next : α → Fin n → α) (A : α → Prop)
    (x : α) (e : Fin n) (u : Thru.Word n) :
    hasPublication next A x (e :: u) ↔
      A (next x e) ∨ hasPublication next A (next x e) u := by
  constructor
  · rintro ⟨j, hj, hlen, hA⟩
    cases j with
    | zero => omega
    | succ j =>
        cases j with
        | zero =>
            exact Or.inl hA
        | succ j =>
            have hle : j + 1 ≤ u.length := by
              simp only [List.length_cons] at hlen
              omega
            exact Or.inr ⟨j + 1, by omega, hle, by
              simpa only [List.take_succ_cons, Thru.runWord] using hA⟩
  · rintro (hA | ⟨j, hj, hlen, hA⟩)
    · exact ⟨1, by decide, by simp, hA⟩
    · have hle : j + 1 ≤ (e :: u).length := Nat.succ_le_succ hlen
      exact ⟨j + 1, by omega, hle, by
        simpa only [List.take_succ_cons, Thru.runWord] using hA⟩

private theorem publication_run_iff (next : α → Fin n → α) (A : α → Prop)
    (x : α) (b : Bool) (u : Thru.Word n) :
    done (Thru.runWord (publicationStep next A) (x, b) u) ↔
      b = true ∨ hasPublication next A x u := by
  induction u generalizing x b with
  | nil =>
      have hf : ¬ hasPublication next A x [] := by
        rintro ⟨j, hj, hlen, _⟩
        simp only [List.length_nil] at hlen
        omega
      simp [done, Thru.runWord, hf]
  | cons e u ih =>
      rw [Thru.runWord]
      change done (Thru.runWord (publicationStep next A)
          (next x e, b || decide (A (next x e))) u) ↔
        b = true ∨ hasPublication next A x (e :: u)
      rw [ih, hasPublication_cons]
      simp only [Bool.or_eq_true, decide_eq_true_eq, or_assoc]

/-- Count exactly the raw words with at least one noninitial service. -/
theorem publicationMass_eq_prefix (next : α → Fin n → α) (A : α → Prop)
    (x : α) (t : Nat) :
    publicationMass next A x t =
      Thru.wordSum (fun u => if hasPublication next A x u then 1 else 0) t := by
  unfold publicationMass
  rw [endpoint_sum]
  apply Thru.wordSum_congr
  intro u
  have he := publication_run_iff next A x false u
  simp only [Bool.false_eq_true, false_or] at he
  by_cases h : hasPublication next A x u
  · simp [h, he.mpr h]
  · have hmiss : ¬ done (Thru.runWord (publicationStep next A) (x, false) u) :=
      fun hp => h (he.mp hp)
    simp [h, hmiss]

private theorem prefix_sum (f : Thru.Word n → Nat) (k s : Nat) :
    Thru.wordSum (fun u => f (u.take k)) (k + s) =
      n ^ s * Thru.wordSum f k := by
  induction k generalizing f with
  | zero => simp [Thru.wordSum_const, Thru.wordSum, Nat.mul_comm]
  | succ k ih =>
      simp only [Nat.succ_add, Thru.wordSum, List.take_succ_cons]
      rw [← Thru.ofFn_sum_mul_left]
      exact FiniteUniformStoppingTree.ofFn_sum_eq _ _
        (fun e => ih (fun u => f (e :: u)))

private theorem no_hit_before_wait (next : α → Fin n → α) (A : α → Prop)
    (x : α) (u : Thru.Word n) (k : Nat)
    (h : k < Thru.wait next A x u) :
    (Thru.runWord (publicationStep next A) (x, false) (u.take k)).2 = false := by
  induction u generalizing x k with
  | nil => simp [Thru.wait] at h
  | cons e u ih =>
      cases k with
      | zero => rfl
      | succ k =>
          have hx : ¬ A x := by
            intro hx
            rw [Thru.wait_of_hit next A x hx] at h
            omega
          rw [Thru.wait_cons_of_not next A x hx e u] at h
          have hk : k < Thru.wait next A (next x e) u := by omega
          have he : ¬ A (next x e) := by
            intro he
            rw [Thru.wait_of_hit next A (next x e) he] at hk
            omega
          simpa [List.take_succ_cons, Thru.runWord, publicationStep, he] using
            ih (next x e) k hk

private theorem wait_suffix_tail (next : α → Fin n → α) (A : α → Prop)
    (x : α) (t k s : Nat) (hk : k ≤ t) (hs : k < s) :
    Thru.wordSum (fun u => if s ≤ Thru.wait next A x u then 1 else 0) t ≤
      n ^ (t - k) * missMass next A x k := by
  let f (v : Thru.Word n) :=
    miss done (Thru.runWord (publicationStep next A) (x, false) v)
  have hsum := prefix_sum f k (t - k)
  rw [Nat.add_sub_of_le hk] at hsum
  have heq : Thru.wordSum f k = missMass next A x k :=
    (endpoint_sum (publicationStep next A) (miss done) (x, false) k).symm
  rw [← heq, ← hsum]
  apply Thru.wordSum_mono
  intro u
  by_cases h : s ≤ Thru.wait next A x u
  · have hnone := no_hit_before_wait next A x u k (Nat.lt_of_lt_of_le hs h)
    simp [h, f, miss, done, hnone]
  · simp [h]

private theorem wait_moment_of_tail (next : α → Fin n → α) (A : α → Prop)
    (L : Nat) (hL : 0 < L) (x : α)
    (htail : ∀ t q, 0 < q →
      4 ^ q * Thru.wordSum (fun u => if q * L ≤ Thru.wait next A x u then 1 else 0) t
        ≤ n ^ t) :
    Thru.MomentAt next A L x := by
  intro t
  let z (u : Thru.Word n) := Nat.min (Thru.wait next A x u) t / L
  let w (q : Nat) (u : Thru.Word n) := 2 ^ Nat.min q (z u)
  let ind (q : Nat) (u : Thru.Word n) := if q ≤ z u then 1 else 0
  let mass (q : Nat) := Thru.wordSum (w q) t
  let tail (q : Nat) := Thru.wordSum (ind q) t
  have hscaled (q : Nat) (hq : 0 < q) : 4 ^ q * tail q ≤ n ^ t := by
    apply Nat.le_trans (Nat.mul_le_mul_left (4 ^ q) ?_) (htail t q hq)
    apply Thru.wordSum_mono
    intro u
    by_cases hu : q ≤ z u
    · have hcut : q * L ≤ Nat.min (Thru.wait next A x u) t :=
        (Nat.le_div_iff_mul_le hL).1 hu
      have hw := Nat.le_trans hcut (Nat.min_le_left (Thru.wait next A x u) t)
      simp [ind, hu, hw]
    · simp [ind, hu]
  have hstep (q : Nat) : mass (q + 1) ≤ mass q + 2 ^ q * tail (q + 1) := by
    unfold mass tail
    rw [← Thru.wordSum_mul_left, ← Thru.wordSum_add_fun]
    apply Thru.wordSum_mono
    intro u
    by_cases hu : q + 1 ≤ z u
    · have hq : q ≤ z u := by omega
      simp only [w, ind, Nat.min_eq_left hu, Nat.min_eq_left hq, if_pos hu,
        Nat.mul_one, Nat.pow_succ, Nat.mul_two, Nat.le_refl]
    · have hq : z u ≤ q := by omega
      have hq' : z u ≤ q + 1 := by omega
      simp only [w, ind, Nat.min_eq_right hq, Nat.min_eq_right hq', if_neg hu,
        Nat.mul_zero, Nat.add_zero, Nat.le_refl]
  have hbudget (q : Nat) : 2 ^ q * mass q + n ^ t ≤ 2 ^ q * (2 * n ^ t) := by
    induction q with
    | zero =>
        have hz : mass 0 = n ^ t := by
          simpa [mass, w] using (Thru.wordSum_const_one (n := n) t)
        simp [hz, Nat.two_mul]
    | succ q ih =>
        have hpow : 2 ^ q ≤ 2 ^ (q + 1) :=
          Nat.pow_le_pow_right (by decide) (by omega)
        have hmul : 2 ^ (q + 1) * (2 ^ q * tail (q + 1)) ≤ n ^ t := by
          calc
            2 ^ (q + 1) * (2 ^ q * tail (q + 1)) ≤
                2 ^ (q + 1) * (2 ^ (q + 1) * tail (q + 1)) :=
              Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hpow)
            _ = 4 ^ (q + 1) * tail (q + 1) := by
              rw [← Nat.mul_assoc, ← Nat.mul_pow]
            _ ≤ n ^ t := hscaled (q + 1) (by omega)
        have hdouble (v : Nat) : 2 ^ (q + 1) * v = 2 * (2 ^ q * v) := by
          rw [Nat.pow_succ]
          ac_rfl
        calc
          2 ^ (q + 1) * mass (q + 1) + n ^ t ≤
              2 ^ (q + 1) * (mass q + 2 ^ q * tail (q + 1)) + n ^ t :=
            Nat.add_le_add_right (Nat.mul_le_mul_left _ (hstep q)) _
          _ = 2 * (2 ^ q * mass q) + 2 ^ (q + 1) * (2 ^ q * tail (q + 1)) + n ^ t := by
            rw [Nat.mul_add, hdouble (mass q)]
          _ ≤ 2 * (2 ^ q * (2 * n ^ t)) := by omega
          _ = 2 ^ (q + 1) * (2 * n ^ t) := (hdouble _).symm
  have hlast : mass t ≤ 2 * n ^ t :=
    Nat.le_of_mul_le_mul_left
      (Nat.le_trans (Nat.le_add_right _ _) (hbudget t)) (Nat.two_pow_pos t)
  have hexact : Thru.wordSum (fun u => 2 ^ z u) t = mass t := by
    apply Thru.wordSum_congr
    intro u
    have hz : z u ≤ t := Nat.le_trans (Nat.div_le_self _ _) (Nat.min_le_right _ _)
    simp [w, Nat.min_eq_right hz]
  exact Nat.le_trans (Nat.le_of_eq hexact) hlast

/-- A uniform physical block success bound gives the clock-repair moment.
At the threshold `j * L`, a sufficient publication test uses the first
`2 * j * d * H` raw marks, strictly before the threshold. -/
theorem publication_moment_of_block (next : α → Fin n → α) (A : α → Prop)
    (H d L : Nat) (hH : 1 ≤ H) (hd : 1 ≤ d) (hL : 4 * (d * H) ≤ L)
    (hmass : ∀ x, n ^ H ≤ d * publicationMass next A x H) (x : α) :
    Thru.MomentAt next A L x := by
  have hpos : 0 < d * H := Nat.mul_pos (by omega) (by omega)
  apply wait_moment_of_tail next A L (by omega) x
  intro t j hj
  let k := (2 * j) * (d * H)
  have hk : k < j * L := by
    have hsmall : 2 * (d * H) < L := by omega
    calc
      k = j * (2 * (d * H)) := by dsimp [k]; ac_rfl
      _ < j * L := Nat.mul_lt_mul_of_pos_left hsmall hj
  by_cases hkt : k ≤ t
  · have hw := wait_suffix_tail next A x t k (j * L) hkt hk
    have htail := publication_miss_tail next A H d hd hmass x (2 * j)
    have hpow : 2 ^ (2 * j) = 4 ^ j := by
      rw [Nat.pow_mul]
    change 2 ^ (2 * j) * missMass next A x k ≤ n ^ k at htail
    rw [hpow] at htail
    calc
      4 ^ j *
          Thru.wordSum (fun u => if j * L ≤ Thru.wait next A x u then 1 else 0) t ≤
            4 ^ j * (n ^ (t - k) * missMass next A x k) := Nat.mul_le_mul_left _ hw
      _ = n ^ (t - k) * (4 ^ j * missMass next A x k) := by ac_rfl
      _ ≤ n ^ (t - k) * n ^ k := Nat.mul_le_mul_left _ htail
      _ = n ^ t := by rw [← Nat.pow_add, Nat.add_comm (t-k), Nat.add_sub_of_le hkt]
  · have hz :
        Thru.wordSum (fun u => if j * L ≤ Thru.wait next A x u then 1 else 0) t = 0 := by
      calc
        _ = Thru.wordSum (fun _ : Thru.Word n => 0) t := by
          apply Thru.wordSum_congr_length
          intro u hu
          have hl := Thru.wait_le_length next A x u
          have hs : ¬ j * L ≤ Thru.wait next A x u := by omega
          simp [hs]
        _ = 0 := by rw [Thru.wordSum_const, Nat.zero_mul]
    simp [hz]

end

end L4.Height.RawService

