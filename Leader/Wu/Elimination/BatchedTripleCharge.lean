-- core only
set_option autoImplicit false


namespace RoundBatchingCharge


/-! ## One-round accounting -/


/-- A charged consecutive triple.  `arcA` and `arcB` are abstract Nat labels
for its two internal ring arcs; `a` and `b` are their gap lengths. -/
structure Triple where
  arcA : Nat
  arcB : Nat
  a : Nat
  b : Nat
  deriving DecidableEq, Repr


def Triple.mass (g : Triple) : Nat := g.a + g.b


def Triple.arcs (g : Triple) : List Nat := [g.arcA, g.arcB]


/-- An accounting round.  Geometry is reduced to two certificates:
all charged arc labels are distinct, and their total charged mass is at most n. -/
structure Round (n : Nat) where
  triples : List Triple
  arcDisjoint : (triples.flatMap Triple.arcs).Nodup
  massBound : (triples.map Triple.mass).sum <= n


/-- The checked local form used by the accounting layer. -/
def EpisodeCostBound (C n : Nat) (cost : Triple -> Nat) : Prop :=
  forall g, cost g <= C * n * g.mass


private theorem sum_map_le_pointwise {A : Type}
    (xs : List A) (f g : A -> Nat)
    (h : forall x, f x <= g x) :
    (xs.map f).sum <= (xs.map g).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simp only [List.map_cons, List.sum_cons]
      exact Nat.add_le_add (h x) ih


private theorem sum_map_mul_left {A : Type}
    (K : Nat) (f : A -> Nat) (xs : List A) :
    (xs.map (fun x => K * f x)).sum = K * (xs.map f).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simp only [List.map_cons, List.sum_cons, ih, Nat.mul_add]


def roundSumCost {n : Nat} (r : Round n) (cost : Triple -> Nat) : Nat :=
  (r.triples.map cost).sum


theorem roundSumCost_le_mass
    {C n : Nat} (r : Round n) (cost : Triple -> Nat)
    (hcost : EpisodeCostBound C n cost) :
    roundSumCost r cost <=
      C * n * (r.triples.map Triple.mass).sum := by
  calc
    roundSumCost r cost = (r.triples.map cost).sum := rfl
    _ <= (r.triples.map (fun g => C * n * g.mass)).sum :=
      sum_map_le_pointwise r.triples cost
        (fun g => C * n * g.mass) hcost
    _ = (C * n) * (r.triples.map Triple.mass).sum :=
      sum_map_mul_left (C * n) Triple.mass r.triples


/-- Sum form: one arc-disjoint round costs at most `C*n*n`. -/
theorem roundSumCost_le_ring
    {C n : Nat} (r : Round n) (cost : Triple -> Nat)
    (hcost : EpisodeCostBound C n cost) :
    roundSumCost r cost <= C * n * n := by
  exact Nat.le_trans (roundSumCost_le_mass r cost hcost)
    (Nat.mul_le_mul_left (C * n) r.massBound)


/-- Maximum of a list, with zero for the empty list. -/
def listMax : List Nat -> Nat
  | [] => 0
  | x :: xs => max x (listMax xs)


private theorem listMax_map_le_scaled {A : Type}
    (xs : List A) (f g : A -> Nat) (K : Nat)
    (h : forall x, f x <= K * g x) :
    listMax (xs.map f) <= K * listMax (xs.map g) := by
  induction xs with
  | nil => simp [listMax]
  | cons x xs ih =>
      simp only [List.map_cons, listMax]
      have hx :
          f x <= K * max (g x) (listMax (xs.map g)) :=
        Nat.le_trans (h x)
          (Nat.mul_le_mul_left K (Nat.le_max_left _ _))
      have ht :
          listMax (xs.map f) <=
            K * max (g x) (listMax (xs.map g)) :=
        Nat.le_trans ih
          (Nat.mul_le_mul_left K (Nat.le_max_right _ _))
      exact (Nat.max_le).2 (And.intro hx ht)


private theorem listMax_le_sum (xs : List Nat) :
    listMax xs <= xs.sum := by
  induction xs with
  | nil => simp [listMax]
  | cons x xs ih =>
      simp only [listMax, List.sum_cons]
      apply (Nat.max_le).2
      constructor
      · omega
      · omega


def roundMaxCost {n : Nat} (r : Round n) (cost : Triple -> Nat) : Nat :=
  listMax (r.triples.map cost)


def roundMaxMass {n : Nat} (r : Round n) : Nat :=
  listMax (r.triples.map Triple.mass)


/-- Max form for the Nat-valued per-episode cost proxies. -/
theorem roundMaxCost_le_maxMass
    {C n : Nat} (r : Round n) (cost : Triple -> Nat)
    (hcost : EpisodeCostBound C n cost) :
    roundMaxCost r cost <= C * n * roundMaxMass r := by
  simpa [roundMaxCost, roundMaxMass] using
    (listMax_map_le_scaled r.triples cost Triple.mass (C * n) hcost)


/-- In particular the maximum individual proxy is also at most `C*n*n`. -/
theorem roundMaxCost_le_ring
    {C n : Nat} (r : Round n) (cost : Triple -> Nat)
    (hcost : EpisodeCostBound C n cost) :
    roundMaxCost r cost <= C * n * n := by
  have hmaxMass : roundMaxMass r <= n :=
    Nat.le_trans
      (by
        simpa [roundMaxMass] using
          (listMax_le_sum (r.triples.map Triple.mass)))
      r.massBound
  exact Nat.le_trans (roundMaxCost_le_maxMass r cost hcost)
    (Nat.mul_le_mul_left (C * n) hmaxMass)


/-- The max proxy and the sum proxy are genuinely different quantities. -/
theorem roundMaxCost_le_sumCost
    {n : Nat} (r : Round n) (cost : Triple -> Nat) :
    roundMaxCost r cost <= roundSumCost r cost := by
  simpa [roundMaxCost, roundSumCost] using
    (listMax_le_sum (r.triples.map cost))


/-! ## Exact integer effect of floor(L/3) triple batching -/


/-- Delete one leader from each of `floor(L/3)` vertex-disjoint triples. -/
def afterTripleBatch (L : Nat) : Nat := L - L / 3


/-- The exact rounded contraction supplied by ordinary triple batching. -/
theorem afterTripleBatch_rounding (L : Nat) :
    3 * afterTripleBatch L <= 2 * L + 2 := by
  unfold afterTripleBatch
  omega


/-- The stronger recurrence requested below is ¬ a consequence of batching. -/
theorem afterTripleBatch_strong_counterexample :
    ¬ (3 * afterTripleBatch 4 <= 2 * 4) := by
  unfold afterTripleBatch
  omega


/-- The excess number of leaders above two contracts by the clean 2/3 factor. -/
theorem afterTripleBatch_excess_shrink (L : Nat) :
    3 * (afterTripleBatch L - 2) <= 2 * (L - 2) := by
  unfold afterTripleBatch
  omega


/-! ## Finite round sums -/


private theorem ofFn_sum_le {k : Nat} (f g : Fin k -> Nat)
    (hfg : forall i, f i <= g i) :
    (List.ofFn f).sum <= (List.ofFn g).sum := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [List.ofFn_succ, List.sum_cons, List.ofFn_succ, List.sum_cons]
      exact Nat.add_le_add (hfg 0)
        (ih (fun i => f i.succ) (fun i => g i.succ)
          (fun i => hfg i.succ))


private theorem ofFn_sum_const (k c : Nat) :
    (List.ofFn (fun _ : Fin k => c)).sum = k * c := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [List.ofFn_succ, List.sum_cons, ih, Nat.succ_mul]
      exact Nat.add_comm _ _


/-- `k` abstract rounds, each carrying its own certified batch and local costs.
`shrink` is deliberately a hypothesis: it is stronger than floor-third batching
when integer rounding is present. -/
structure Rounds (n C k : Nat) where
  batch : Fin k -> Round n
  cost : (i : Fin k) -> Triple -> Nat
  episodeCost : forall i, EpisodeCostBound C n (cost i)
  leaders : Nat -> Nat
  shrink : forall r, r < k ->
    3 * leaders (r + 1) <= 2 * leaders r


namespace Rounds


def totalCost {n C k : Nat} (rs : Rounds n C k) : Nat :=
  (List.ofFn (fun i : Fin k =>
    roundSumCost (rs.batch i) (rs.cost i))).sum


/-- Summing the certified round costs gives `k * (C*n*n)`. -/
theorem totalCost_le
    {n C k : Nat} (rs : Rounds n C k) :
    totalCost rs <= k * (C * n * n) := by
  unfold totalCost
  calc
    (List.ofFn (fun i : Fin k =>
      roundSumCost (rs.batch i) (rs.cost i))).sum
        <= (List.ofFn (fun _ : Fin k => C * n * n)).sum := by
          apply ofFn_sum_le
          intro i
          exact roundSumCost_le_ring
            (rs.batch i) (rs.cost i) (rs.episodeCost i)
    _ = k * (C * n * n) := ofFn_sum_const k (C * n * n)


/-- Explicit constant-times-`n^2`-times-number-of-rounds form. -/
theorem totalCost_le_square_times_rounds
    {n C k : Nat} (rs : Rounds n C k) :
    totalCost rs <= C * n ^ 2 * k := by
  calc
    totalCost rs <= k * (C * n * n) := totalCost_le rs
    _ = C * n ^ 2 * k := by
      simp only [Nat.pow_succ, Nat.pow_zero]
      ac_rfl


private theorem geometric_prefix
    (leaders : Nat -> Nat) (k : Nat)
    (hshrink : forall r, r < k ->
      3 * leaders (r + 1) <= 2 * leaders r) :
    3 ^ k * leaders k <= 2 ^ k * leaders 0 := by
  revert hshrink
  induction k with
  | zero =>
      intro hshrink
      simp
  | succ k ih =>
      intro hshrink
      have hprefix : forall r, r < k ->
          3 * leaders (r + 1) <= 2 * leaders r := by
        intro r hr
        exact hshrink r (by omega)
      have hih := ih hprefix
      have hstep : 3 * leaders (k + 1) <= 2 * leaders k :=
        hshrink k (by omega)
      calc
        3 ^ (k + 1) * leaders (k + 1)
            = 3 ^ k * (3 * leaders (k + 1)) := by
              rw [Nat.pow_succ]
              ac_rfl
        _ <= 3 ^ k * (2 * leaders k) :=
          Nat.mul_le_mul_left (3 ^ k) hstep
        _ = 2 * (3 ^ k * leaders k) := by
          ac_rfl
        _ <= 2 * (2 ^ k * leaders 0) :=
          Nat.mul_le_mul_left 2 hih
        _ = 2 ^ (k + 1) * leaders 0 := by
          rw [Nat.pow_succ]
          ac_rfl


/-- Iterating the requested strong recurrence. -/
theorem leader_geometric
    {n C k : Nat} (rs : Rounds n C k) :
    3 ^ k * rs.leaders k <= 2 ^ k * rs.leaders 0 :=
  geometric_prefix rs.leaders k rs.shrink


/-- Log-free Nat certificate for a terminal round count.
Positivity is necessary: `L_k <= 1` alone would allow `L_k = 0`. -/
theorem round_count_certificate
    {n C k : Nat} (rs : Rounds n C k)
    (initialBound : rs.leaders 0 <= n)
    (terminal : rs.leaders k <= 1)
    (positive : 1 <= rs.leaders k) :
    3 ^ k * 1 <= 2 ^ k * n := by
  have hend : rs.leaders k = 1 := by omega
  have hgeo := leader_geometric rs
  rw [hend] at hgeo
  exact Nat.le_trans hgeo
    (Nat.mul_le_mul_left (2 ^ k) initialBound)


/-- The two requested conclusions packaged together. -/
theorem terminal_summary
    {n C k : Nat} (rs : Rounds n C k)
    (initialBound : rs.leaders 0 <= n)
    (terminal : rs.leaders k <= 1)
    (positive : 1 <= rs.leaders k) :
    totalCost rs <= C * n ^ 2 * k  ∧ 
      3 ^ k * 1 <= 2 ^ k * n :=
  And.intro (totalCost_le_square_times_rounds rs)
    (round_count_certificate rs initialBound terminal positive)


end Rounds


/-! ## Explicit serial merge obstruction -/


/-- Triangular numbers, used only to make the closed-form computation explicit. -/
def triangular : Nat -> Nat
  | 0 => 0
  | n + 1 => triangular n + (n + 1)


theorem two_mul_triangular (n : Nat) :
    2 * triangular n = n * (n + 1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      calc
        2 * triangular (n + 1)
            = 2 * (triangular n + (n + 1)) := by rfl
        _ = 2 * triangular n + 2 * (n + 1) := by
          rw [Nat.mul_add]
        _ = n * (n + 1) + 2 * (n + 1) := by
          rw [ih]
        _ = (n + 1) * ((n + 1) + 1) := by
          simp [Nat.succ_mul, Nat.mul_succ]
          <;> omega


theorem triangular_eq (n : Nat) :
    triangular n = n * (n + 1) / 2 := by
  have h := two_mul_triangular n
  calc
    triangular n = (2 * triangular n) / 2 := by omega
    _ = (n * (n + 1)) / 2 := by rw [h]


/-- `2+3+...+n`, with the natural convention that the value is zero at n=0,1. -/
def sumGapCharges (n : Nat) : Nat := triangular n - 1


theorem sumGapCharges_eq (n : Nat) :
    sumGapCharges n = n * (n + 1) / 2 - 1 := by
  unfold sumGapCharges
  rw [triangular_eq]


/-- Chronological growing-gap family with `m` episodes:
`(1,1),(2,1),...,(m,1)`, hence charges `2,3,...,m+1`.
The arc labels are dummy here because this is a serial obstruction, ¬ a Round. -/
def mergeGaps : Nat -> List Triple
  | 0 => []
  | m + 1 =>
      mergeGaps m ++
        [{ arcA := 0, arcB := 0, a := m + 1, b := 1 }]


def mergeGapMass (m : Nat) : Nat :=
  ((mergeGaps m).map Triple.mass).sum


theorem mergeGaps_length (m : Nat) :
    (mergeGaps m).length = m := by
  induction m with
  | zero => rfl
  | succ m ih =>
      simp [mergeGaps, ih]


theorem mergeGapMass_succ (m : Nat) :
    mergeGapMass (m + 1) = mergeGapMass m + (m + 2) := by
  simp [mergeGapMass, mergeGaps, Triple.mass, List.sum_append]


theorem mergeGapMass_add_one (m : Nat) :
    mergeGapMass m + 1 = triangular (m + 1) := by
  induction m with
  | zero => simp [mergeGapMass, mergeGaps, triangular]
  | succ m ih =>
      calc
        mergeGapMass (m + 1) + 1
            = (mergeGapMass m + (m + 2)) + 1 := by
              rw [mergeGapMass_succ]
        _ = (mergeGapMass m + 1) + (m + 2) := by omega
        _ = triangular (m + 1) + (m + 2) := by rw [ih]
        _ = triangular ((m + 1) + 1) := by rfl


theorem mergeGapMass_eq_sumGapCharges (m : Nat) :
    mergeGapMass m = sumGapCharges (m + 1) := by
  have h := mergeGapMass_add_one m
  unfold sumGapCharges
  omega


/-- For `n` initial unit gaps there are `n-1` serial episodes. -/
theorem adversarial_merge_episode_count (n : Nat) :
    (mergeGaps (n - 1)).length = n - 1 :=
  mergeGaps_length (n - 1)


/-- Exact negative computation: the serial family charges `2+...+n`. -/
theorem adversarial_merge_exact (n : Nat) (hn : 1 <= n) :
    ((mergeGaps (n - 1)).map Triple.mass).sum =
      n * (n + 1) / 2 - 1 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  have h := mergeGapMass_eq_sumGapCharges m
  rw [sumGapCharges_eq] at h
  simpa [mergeGapMass] using h


end RoundBatchingCharge

#print axioms RoundBatchingCharge.roundSumCost_le_mass
#print axioms RoundBatchingCharge.roundSumCost_le_ring
#print axioms RoundBatchingCharge.roundMaxCost_le_maxMass
#print axioms RoundBatchingCharge.roundMaxCost_le_ring
#print axioms RoundBatchingCharge.roundMaxCost_le_sumCost
#print axioms RoundBatchingCharge.afterTripleBatch_rounding
#print axioms RoundBatchingCharge.afterTripleBatch_strong_counterexample
#print axioms RoundBatchingCharge.afterTripleBatch_excess_shrink
#print axioms RoundBatchingCharge.Rounds.totalCost_le
#print axioms RoundBatchingCharge.Rounds.totalCost_le_square_times_rounds
#print axioms RoundBatchingCharge.Rounds.leader_geometric
#print axioms RoundBatchingCharge.Rounds.round_count_certificate
#print axioms RoundBatchingCharge.Rounds.terminal_summary
#print axioms RoundBatchingCharge.two_mul_triangular
#print axioms RoundBatchingCharge.triangular_eq
#print axioms RoundBatchingCharge.sumGapCharges_eq
#print axioms RoundBatchingCharge.mergeGaps_length
#print axioms RoundBatchingCharge.mergeGapMass_succ
#print axioms RoundBatchingCharge.mergeGapMass_add_one
#print axioms RoundBatchingCharge.mergeGapMass_eq_sumGapCharges
#print axioms RoundBatchingCharge.adversarial_merge_episode_count
#print axioms RoundBatchingCharge.adversarial_merge_exact
