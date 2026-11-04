-- core only

set_option autoImplicit false

namespace MinimalTripleChoice

/-- Cyclic successor on `Fin m`. -/
def cyclicSucc {m : Nat} (i : Fin m) : Fin m := by
  exact ⟨(i.val + 1) % m, Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le i.val) i.isLt)⟩

private theorem sum_map_add {α : Type} (xs : List α)
    (f g : α → Nat) :
    (xs.map (fun x => f x + g x)).sum =
      (xs.map f).sum + (xs.map g).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [ih]
      omega

private theorem sum_ofFn_add {m : Nat} (f g : Fin m → Nat) :
    (List.ofFn (fun i => f i + g i)).sum =
      (List.ofFn f).sum + (List.ofFn g).sum := by
  simpa only [List.map_ofFn, Function.comp_def] using
    sum_map_add (List.ofFn (fun i : Fin m => i)) f g

private theorem sum_map_mul_left {α : Type} (xs : List α)
    (c : Nat) (f : α → Nat) :
    (xs.map (fun x => c * f x)).sum = c * (xs.map f).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [ih, Nat.mul_add]

private theorem sum_ofFn_mul_left {m : Nat} (c : Nat)
    (f : Fin m → Nat) :
    (List.ofFn (fun i => c * f i)).sum = c * (List.ofFn f).sum := by
  simpa only [List.map_ofFn, Function.comp_def] using
    sum_map_mul_left (List.ofFn (fun i : Fin m => i)) c f

/-- Cyclic successor is a permutation of `Fin m`, hence preserves a sum. -/
private theorem sum_ofFn_cyclicSucc {m : Nat} (hm : 0 < m)
    (f : Fin m → Nat) :
    (List.ofFn (fun i => f (cyclicSucc i))).sum =
      (List.ofFn f).sum := by
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero
    (Nat.ne_of_gt hm)
  subst m
  rw [show List.ofFn (fun e : Fin (k + 1) => f (cyclicSucc e)) =
    (List.ofFn (fun i : Fin k =>
      f (cyclicSucc i.castSucc))) ++
      [f (cyclicSucc (Fin.last k))] from List.ofFn_succ_last]
  rw [List.sum_append, List.sum_cons, List.sum_nil, Nat.add_zero,
    List.ofFn_succ, List.sum_cons]
  have hlast : cyclicSucc (Fin.last k) = (0 : Fin (k + 1)) := by
    apply Fin.ext
    simp [cyclicSucc]
  have hsucc : ∀ i : Fin k,
      cyclicSucc i.castSucc = i.succ := by
    intro i
    apply Fin.ext
    simp [cyclicSucc,
      Nat.mod_eq_of_lt (by omega : i.val + 1 < k + 1)]
  rw [hlast]
  have hfun :
      (fun i : Fin k => f (cyclicSucc i.castSucc)) =
        (fun i : Fin k => f i.succ) := by
    funext i
    rw [hsucc]
  rw [hfun]
  omega

/-- The span of the consecutive triple whose left gap has index `i`. -/
def pairSpan {m : Nat} (d : Fin m → Nat) (i : Fin m) : Nat :=
  d i + d (cyclicSucc i)

/-- Every cyclic gap occurs in exactly two consecutive two-gap spans. -/
theorem cyclicPairSpan_sum {m : Nat} (hm : 0 < m)
    (d : Fin m → Nat) :
    (List.ofFn (pairSpan d)).sum = 2 * (List.ofFn d).sum := by
  change (List.ofFn (fun i => d i + d (cyclicSucc i))).sum =
    2 * (List.ofFn d).sum
  rw [sum_ofFn_add, sum_ofFn_cyclicSucc hm d]
  omega

/-- If every list entry is strictly above `B`, its sum is at least
`length * (B+1)`. -/
private theorem length_mul_succ_le_sum_of_all_gt
    (xs : List Nat) (B : Nat)
    (hall : ∀ x, x ∈ xs → B < x) :
    xs.length * (B + 1) <= xs.sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      have hx : B + 1 <= x := by
        have := hall x (by simp)
        omega
      have htail : ∀ y, y ∈ xs → B < y := by
        intro y hy
        exact hall y (by simp [hy])
      have hrest := ih htail
      calc
        (x :: xs).length * (B + 1) =
            xs.length * (B + 1) + (B + 1) := by
              simp only [List.length_cons, Nat.add_mul, Nat.one_mul]
        _ <= xs.sum + x := Nat.add_le_add hrest hx
        _ = (x :: xs).sum := by
          simp only [List.sum_cons]
          omega

/-- Division-free finite averaging: one value is at most `B/m`. -/
private theorem exists_scaled_le_of_sum_le
    {m B : Nat} (hm : 0 < m) (f : Fin m → Nat)
    (hsum : (List.ofFn f).sum <= B) :
    ∃ i : Fin m, m * f i <= B := by
  apply Classical.byContradiction
  intro hnone
  have hall : ∀ i : Fin m, B < m * f i := by
    intro i
    have hnot : ¬m * f i <= B := by
      intro hle
      exact hnone ⟨i, hle⟩
    omega
  have hbig := length_mul_succ_le_sum_of_all_gt
    (List.ofFn (fun i : Fin m => m * f i)) B (by
      intro x hx
      simp only [List.mem_ofFn] at hx
      obtain ⟨i, hi⟩ := hx
      subst x
      exact hall i)
  have hscaled :
      (List.ofFn (fun i : Fin m => m * f i)).sum =
        m * (List.ofFn f).sum :=
    sum_ofFn_mul_left m f
  have hlen :
      (List.ofFn (fun i : Fin m => m * f i)).length = m := by
    simp
  rw [hlen, hscaled] at hbig
  have hsum_scaled :
      m * (List.ofFn f).sum <= m * B :=
    Nat.mul_le_mul_left m hsum
  have hstrict : m * B < m * (B + 1) := by
    rw [Nat.mul_add, Nat.mul_one]
    omega
  omega

/-- Pigeonhole choice for two consecutive cyclic gaps.
The assumption `3 <= m` is the protocol's consecutive-triple regime. -/
theorem minimalTripleChoice
    {m n : Nat} (hm3 : 3 <= m)
    (d : Fin m → Nat)
    (hmass : (List.ofFn d).sum <= n) :
    ∃ i : Fin m,
      m * (d i + d (cyclicSucc i)) <= 2 * n := by
  have hm : 0 < m := by omega
  have hpairs : (List.ofFn (pairSpan d)).sum <= 2 * n := by
    rw [cyclicPairSpan_sum hm d]
    exact Nat.mul_le_mul_left 2 hmass
  have hex := exists_scaled_le_of_sum_le hm (pairSpan d) hpairs
  simpa [pairSpan] using hex

/-- Charge a selected span at a fixed cost per unit length. -/
def totalCharge (costPerUnit span : Nat) : Nat :=
  costPerUnit * span

/-- Multiplying the minimal-span inequality by a per-unit cost preserves the
same division-free averaging bound. -/
theorem minimalTripleCharge
    {m n costPerUnit : Nat} (hm3 : 3 <= m)
    (d : Fin m → Nat)
    (hmass : (List.ofFn d).sum <= n) :
    ∃ i : Fin m,
      m * totalCharge costPerUnit
          (d i + d (cyclicSucc i)) <=
        2 * n * costPerUnit := by
  rcases minimalTripleChoice hm3 d hmass with ⟨i, hi⟩
  refine ⟨i, ?_⟩
  have hc := Nat.mul_le_mul_left costPerUnit hi
  simpa [totalCharge, Nat.mul_assoc, Nat.mul_comm,
    Nat.mul_left_comm] using hc

#print axioms cyclicPairSpan_sum
#print axioms minimalTripleChoice
#print axioms minimalTripleCharge

end MinimalTripleChoice
