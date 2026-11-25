import Leader.L4.Height.CapRepair

namespace L4.Height

open L4.Height.Recover.Chain
open Classical
open L4.Compiler.Native


/-- Core-only cardinality of a decidable subset of the finite alphabet. -/
def countFin {n : Nat} (p : Fin n → Bool) : Nat :=
  ((List.ofFn (fun e : Fin n => e)).filter p).length

/-- A served-site predicate at the successor state is exactly the
corresponding action-site test at the predecessor state. -/
theorem served_next_iff
    {α : Type} {n m B M : Nat} {hm : 0 < m}
    (C : ClockChain α n m B M hm)
    (x : α) (e : Fin n) (i : Fin m) :
    C.served i (C.next x e) ↔
      (C.act x e).map Prod.fst = some i := by
  change C.lastAct (C.next x e) = some i ↔
    (C.act x e).map Prod.fst = some i
  rw [C.last_next]

/-- At threshold jL there are j disjoint groups of L-1 required misses
among the jL-1 transitions. The other j-1 misses can be bounded by one
after normalization. -/
private theorem block_ratio {d n L : Nat} (hd : d ≤ n) (hpos : 0 < L)
    (hL : 4 * d ^ (L - 1) ≤ n ^ (L - 1)) (j : Nat) (hj : 0 < j) :
    4 ^ j * d ^ (j * L - 1) ≤ n ^ (j * L - 1) := by
  have hexp : j * L - 1 = (L - 1) * j + (j - 1) := by
    cases L with
    | zero => omega
    | succ l =>
      rw [Nat.mul_succ]
      simp only [Nat.add_sub_cancel]
      rw [Nat.mul_comm l j]
      omega
  rw [hexp, Nat.pow_add, Nat.pow_add, Nat.pow_mul, Nat.pow_mul,
    ← Nat.mul_assoc, ← Nat.mul_pow]
  exact Nat.mul_le_mul (Nat.pow_le_pow_left hL j)
    (Nat.pow_le_pow_left hd (j - 1))

open scoped Classical

private theorem geomMissWeight {n k : Nat} (p : Fin n → Bool)
    (hk : k ≤ countFin p) (b : Nat) :
    (List.ofFn (fun e => if p e then 0 else b)).sum ≤ (n-k)*b := by
  let es := List.ofFn (fun e : Fin n => e)
  have partition (l : List (Fin n)) :
      (l.filter (fun e => !(p e))).length + (l.filter p).length = l.length := by
    induction l with
    | nil => rfl
    | cons e l ih => cases hp : p e <;> simp [hp] <;> omega
  have weight (l : List (Fin n)) :
      (l.map (fun e => if p e then 0 else b)).sum =
        (l.filter (fun e => !(p e))).length * b := by
    induction l with
    | nil => simp
    | cons e l ih => cases hp : p e <;> simp [hp, ih, Nat.add_mul, Nat.add_comm]
  have hpart := partition es
  have hlen : es.length = n := by simp [es]
  change k ≤ (es.filter p).length at hk
  have hmiss : (es.filter (fun e => !(p e))).length ≤ n - k := by omega
  have hw := weight es
  simp only [es, List.map_ofFn, Function.comp_def] at hw
  rw [hw]
  exact Nat.mul_le_mul_right b hmiss

/-- Only the first `s - 1` successor tests can shorten a wait below `s`. -/
theorem tail_count {α : Type} {n k : Nat} (next : α → Fin n → α) (A : α → Prop)
    (hk : ∀ x, ¬ A x → k ≤ countFin (fun e => decide (A (next x e))))
    (x : α) (t s : Nat) (hs : 1 ≤ s) :
    Thru.wordSum (fun u => if s ≤ Thru.wait next A x u then 1 else 0) t * n ^ (s - 1) ≤
      (n-k) ^ (s-1) * n ^ t := by
  classical
  let T (y : α) (t r : Nat) :=
    Thru.wordSum (fun u => if r + 1 ≤ Thru.wait next A y u then 1 else 0) t
  have hit (y : α) (hy : A y) (t r : Nat) : T y t r = 0 := by
    calc
      T y t r = Thru.wordSum (fun _ : Thru.Word n => 0) t := by
        apply Thru.wordSum_congr
        intro u
        simp [Thru.wait_of_hit next A y hy u]
      _ = 0 := by simp [Thru.wordSum_const]
  have bound : ∀ (r : Nat) (y : α) (t : Nat),
      T y t r * n ^ r ≤ (n-k) ^ r * n ^ t := by
    intro r
    induction r with
    | zero =>
      intro y t
      simp only [Nat.pow_zero, Nat.mul_one, Nat.one_mul]
      calc
        T y t 0 ≤ Thru.wordSum (fun _ : Thru.Word n => 1) t := by
          apply Thru.wordSum_mono
          intro u
          split <;> decide
        _ = n ^ t := Thru.wordSum_const_one t
    | succ r ih =>
      intro y t
      cases t with
      | zero => simp [T, Thru.wordSum, Thru.wait]
      | succ t =>
        by_cases hy : A y
        · rw [hit y hy]; simp
        · have hsplit : T y (t+1) (r+1) =
              (List.ofFn (fun e : Fin n => T (next y e) t r)).sum := by
            apply congrArg (fun f : Fin n → Nat => (List.ofFn f).sum)
            funext e
            apply Thru.wordSum_congr
            intro u
            simp only [Thru.wait_cons_of_not next A y hy e u, Nat.succ_le_succ_iff]
          let b := (n-k)^r * n^t
          let p (e : Fin n) := decide (A (next y e))
          have hsum : (List.ofFn (fun e : Fin n => n^r * T (next y e) t r)).sum ≤
              (n-k)*b := by
            refine Nat.le_trans (Thru.ofFn_sum_le _ (fun e => if p e then 0 else b) ?_) ?_
            · intro e
              by_cases he : A (next y e)
              · simp [p, he, hit _ he]
              · simpa [p, he, b, Nat.mul_comm] using ih (next y e) t
            · exact geomMissWeight p (hk y hy) b
          calc
            T y (t+1) (r+1) * n^(r+1) =
                (List.ofFn (fun e : Fin n => n^r * T (next y e) t r)).sum * n := by
                  rw [hsplit, Thru.ofFn_sum_mul_left, Nat.pow_succ]; ac_rfl
            _ ≤ ((n-k)*b)*n := Nat.mul_le_mul_right n hsum
            _ = (n-k)^(r+1) * n^(t+1) := by
              dsimp only [b]
              simp only [Nat.pow_succ]
              ac_rfl
  cases s with
  | zero => omega
  | succ r => simpa [T] using bound r x t
private theorem geometric_layers {α : Type} {n L : Nat}
    (next : α → Fin n → α) (A : α → Prop) (x : α) (t : Nat)
    (hpos : 0 < L)
    (hblock : ∀ j : Nat, 0 < j →
      4 ^ j * Thru.wordSum
        (fun u => if j * L ≤ Thru.wait next A x u then 1 else 0) t ≤ n ^ t) :
    Thru.wordSum (fun u => 2 ^ (Nat.min (Thru.wait next A x u) t / L)) t ≤
      2 * n ^ t := by
  let exponent (u : Thru.Word n) := Nat.min (Thru.wait next A x u) t / L
  let weight (q : Nat) (u : Thru.Word n) := 2 ^ Nat.min q (exponent u)
  let indicator (j : Nat) (u : Thru.Word n) : Nat :=
    if j * L ≤ Thru.wait next A x u then 1 else 0
  let mass (q : Nat) := Thru.wordSum (weight q) t
  let tail (j : Nat) := Thru.wordSum (indicator j) t
  have step (q : Nat) : mass (q+1) ≤ mass q + 2 ^ q * tail (q+1) := by
    calc
      mass (q+1) ≤ Thru.wordSum
          (fun u => weight q u + 2 ^ q * indicator (q+1) u) t := by
        apply Thru.wordSum_mono
        intro u
        by_cases h : q+1 ≤ exponent u
        · have hq : q ≤ exponent u := by omega
          have hcut : (q+1)*L ≤ Nat.min (Thru.wait next A x u) t :=
            (Nat.le_div_iff_mul_le hpos).1 h
          have hw := Nat.le_trans hcut (Nat.min_le_left _ _)
          simp only [weight, Nat.min_eq_left h, Nat.min_eq_left hq,
            indicator, if_pos hw, Nat.mul_one, Nat.pow_succ, Nat.mul_two] <;>
            exact Nat.le_refl _
        · have hq : exponent u ≤ q := by omega
          have hsucc : exponent u ≤ q+1 := by omega
          simp only [weight, Nat.min_eq_right hq, Nat.min_eq_right hsucc]
          exact Nat.le_add_right _ _
      _ = mass q + 2 ^ q * tail (q+1) := by
        rw [Thru.wordSum_add_fun, Thru.wordSum_mul_left]
  have square (q : Nat) : 2 ^ q * 2 ^ q = 4 ^ q := by
    induction q with
    | zero => rfl
    | succ q ih =>
      simp only [Nat.pow_succ]
      rw [← ih]
      change 2 ^ q * 2 * (2 ^ q * 2) = 2 ^ q * 2 ^ q * (2 * 2)
      ac_rfl
  -- The first q layers add at most (1 - 2^(-q))/2 times the total word count.
  have scaled (q : Nat) :
      2 ^ q * (2 * mass q) + n ^ t ≤ 2 ^ q * (3 * n ^ t) := by
    induction q with
    | zero =>
      have hz : mass 0 = n ^ t := by
        simpa [mass, weight] using (Thru.wordSum_const_one (n := n) t)
      simp only [hz, Nat.pow_zero, Nat.one_mul]
      omega
    | succ q ih =>
      have hb : 4 ^ (q+1) * tail (q+1) ≤ n ^ t := hblock _ (by omega)
      have hd : 2 ^ (q+1) * (2 * (2 ^ q * tail (q+1))) =
          4 ^ (q+1) * tail (q+1) := by
        simp only [Nat.pow_succ]
        rw [← square q]
        change (2 ^ q * 2) * (2 * (2 ^ q * tail (q+1))) =
          (2 ^ q * 2 ^ q * (2 * 2)) * tail (q+1)
        ac_rfl
      rw [← hd] at hb
      have double (v : Nat) : 2 ^ (q+1) * v = 2 * (2 ^ q * v) := by
        rw [Nat.pow_succ]
        ac_rfl
      calc
        2 ^ (q+1) * (2 * mass (q+1)) + n ^ t ≤
            2 ^ (q+1) * (2 * (mass q + 2 ^ q * tail (q+1))) + n ^ t :=
          Nat.add_le_add_right (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left 2 (step q))) _
        _ = 2 * (2 ^ q * (2 * mass q)) +
              2 ^ (q+1) * (2 * (2 ^ q * tail (q+1))) + n ^ t := by
          rw [Nat.mul_add 2 (mass q), Nat.mul_add, double (2 * mass q)]
        _ ≤ 2 * (2 ^ q * (3 * n ^ t)) := by omega
        _ = 2 ^ (q+1) * (3 * n ^ t) := (double _).symm
  have hf := scaled t
  have hthree : 2 * mass t ≤ 3 * n ^ t :=
    Nat.le_of_mul_le_mul_left (Nat.le_trans (Nat.le_add_right _ _) hf)
      (Nat.two_pow_pos t)
  have hsame : Thru.wordSum (fun u => 2 ^ (exponent u)) t = mass t := by
    apply Thru.wordSum_congr
    intro u
    have hu : exponent u ≤ t :=
      Nat.le_trans (Nat.div_le_self _ _) (Nat.min_le_right _ _)
    simp only [weight, Nat.min_eq_right hu]
  exact Nat.le_trans (Nat.le_of_eq hsame) (by omega)
private theorem length_pos_of_ratio {d n L : Nat}
    (hL : 4 * d ^ (L - 1) ≤ n ^ (L - 1)) : 0 < L := by
  cases L with
  | zero => simp at hL
  | succ l => exact Nat.zero_lt_succ l

/-- Uniform service at k letters per unserved state gives the truncated
moment once the survival fraction over L-1 transitions is at most 1/4. -/
theorem moment_of_geometric {α : Type} {n k L : Nat}
    (next : α → Fin n → α) (A : α → Prop) (hn : 0 < n)
    (hk : ∀ x, ¬ A x → k ≤ countFin (fun e => decide (A (next x e))))
    (hL : 4 * (n - k) ^ (L - 1) ≤ n ^ (L - 1)) :
    ∀ x, Thru.MomentAt next A L x := by
  intro x t
  have hpos := length_pos_of_ratio hL
  apply geometric_layers next A x t hpos
  intro j hj
  let s := j * L
  let c := Thru.wordSum (fun u => if s ≤ Thru.wait next A x u then 1 else 0) t
  have ht : c * n ^ (s - 1) ≤ (n - k) ^ (s - 1) * n ^ t :=
    tail_count next A hk x t s (Nat.mul_pos hj hpos)
  have hb : 4 ^ j * (n - k) ^ (s - 1) ≤ n ^ (s - 1) :=
    block_ratio (Nat.sub_le n k) hpos hL j hj
  change 4 ^ j * c ≤ n ^ t
  apply Nat.le_of_mul_le_mul_right _ (Nat.pow_pos hn : 0 < n ^ (s - 1))
  calc
    4 ^ j * c * n ^ (s - 1) = 4 ^ j * (c * n ^ (s - 1)) := Nat.mul_assoc _ _ _
    _ ≤ 4 ^ j * ((n - k) ^ (s - 1) * n ^ t) := Nat.mul_le_mul_left _ ht
    _ = (4 ^ j * (n - k) ^ (s - 1)) * n ^ t := (Nat.mul_assoc _ _ _).symm
    _ ≤ n ^ (s - 1) * n ^ t := Nat.mul_le_mul_right _ hb
    _ = n ^ t * n ^ (s - 1) := Nat.mul_comm _ _

/-- A lower bound on action letters gives the same lower bound on
successors whose most recent action served the specified site. -/
theorem served_moment {α : Type} {n m B M k L : Nat} {hm : 0 < m}
    (C : ClockChain α n m B M hm) (hn : 0 < n)
    (hservice : ∀ x i, k ≤ countFin (fun e => decide ((C.act x e).map Prod.fst = some i)))
    (hL : 4 * (n - k) ^ (L - 1) ≤ n ^ (L - 1)) :
    ∀ i y, Thru.MomentAt C.next (C.served i) L y := by
  intro i
  apply moment_of_geometric C.next (C.served i) hn _ hL
  intro x _
  simpa only [served_next_iff] using hservice x i

/-- Clock repair with its service moments derived from action counts. -/
theorem clock_repair_geometric {α : Type} {n m B M k L : Nat} {hm : 0 < m}
    (C : ClockChain α n m B M hm)
    (hM : Recover.StageTwo.ClockParams M) (hdiam : m / 2 < M / 2)
    (hn : 0 < n)
    (hservice : ∀ x i, k ≤ countFin (fun e => decide ((C.act x e).map Prod.fst = some i)))
    (hL : 4 * (n - k) ^ (L - 1) ≤ n ^ (L - 1)) :
    ∀ x, Recover.StageTwo.WellFormed M (C.cfg x) →
      IIDExpectedHittingTimeAtMost C.next (LgSet C) x (17 * L * m) :=
  clock_repair C hM hdiam (length_pos_of_ratio hL) hm (served_moment C hn hservice hL)

end L4.Height

