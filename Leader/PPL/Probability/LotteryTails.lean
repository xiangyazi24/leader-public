import Leader.PPL.Probability.LotteryCounts

set_option autoImplicit false

namespace PPL.Probability

/-!
Finite-word exponential-moment reduction for the P_PL lottery tails.
The weights are integers, so the reduction uses no rational probabilities.
The two global moment estimates remain separate from the exact parser facts.
-/

/-- Exact Nat-valued finite-word sum from any parser state. -/
def lotteryNatWordSum
    (k : Nat) (s : LotteryState) (T : Nat)
    (w : LotteryState -> Nat) : Nat :=
  ((allHTWords T).map (fun word => w (lotteryRun k s word))).sum

/-- Closed recurrence for the same Nat-valued word sum. -/
def lotteryNatDP (k : Nat) (w : LotteryState -> Nat) :
    Nat -> LotteryState -> Nat
  | 0, s => w s
  | T + 1, s =>
      lotteryNatDP k w T (lotteryStep k s false) +
        lotteryNatDP k w T (lotteryStep k s true)

theorem lotteryNatWordSum_succ
    (k T : Nat) (s : LotteryState) (w : LotteryState -> Nat) :
    lotteryNatWordSum k s (T + 1) w =
      lotteryNatWordSum k (lotteryStep k s false) T w +
        lotteryNatWordSum k (lotteryStep k s true) T w := by
  unfold lotteryNatWordSum
  rw [allHTWords, List.map_append, List.sum_append,
    List.map_map, List.map_map]
  simp only [Function.comp_def, lotteryRun]

theorem lotteryNatWordSum_eq_dp
    (k T : Nat) (s : LotteryState) (w : LotteryState -> Nat) :
    lotteryNatWordSum k s T w = lotteryNatDP k w T s := by
  induction T generalizing s with
  | zero =>
      simp only [lotteryNatWordSum, allHTWords, List.map_cons,
        List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero,
        lotteryRun, lotteryNatDP]
  | succ T ih =>
      rw [lotteryNatWordSum_succ, lotteryNatDP, ih, ih]

/-- Upper-tail moment: each word is weighted by 2 to the number of wins. -/
def lotteryUpperMoment (k T : Nat) : Nat :=
  lotteryNatWordSum k lotteryFresh T (fun s => 2 ^ s.wins)

/-- Lower-tail moment: the shifted inverse weight is kept in Nat. -/
def lotteryLowerMoment (k T M : Nat) : Nat :=
  lotteryNatWordSum k lotteryFresh T
    (fun s => 2 ^ (T + M - s.wins))

theorem lotteryUpperMoment_eq_dp (k T : Nat) :
    lotteryUpperMoment k T =
      lotteryNatDP k (fun s => 2 ^ s.wins) T lotteryFresh := by
  exact lotteryNatWordSum_eq_dp k T lotteryFresh (fun s => 2 ^ s.wins)

theorem lotteryLowerMoment_eq_dp (k T M : Nat) :
    lotteryLowerMoment k T M =
      lotteryNatDP k (fun s => 2 ^ (T + M - s.wins)) T lotteryFresh := by
  exact lotteryNatWordSum_eq_dp k T lotteryFresh
    (fun s => 2 ^ (T + M - s.wins))

/-- The remaining two numerical estimates are on weighted sums over all
binary words, rather than on the selected tail events. -/
def LotteryTailMomentArithmetic : Prop :=
  forall k c : Nat, 1 <= k -> 1 <= c ->
    2 ^ (c * k) *
        lotteryNatDP k (fun s => 2 ^ s.wins)
          (lotteryL7Horizon k c) lotteryFresh <=
      2 ^ (lotteryL7Horizon k c + lotteryTarget k c) ∧
    2 ^ (c * k) *
        lotteryNatDP k
          (fun s => 2 ^ (lotteryL8Horizon k c + lotteryTarget k c - s.wins))
          (lotteryL8Horizon k c) lotteryFresh <=
      2 ^ (lotteryL8Horizon k c + lotteryL8Horizon k c)

private theorem countP_mul_le_sum
    {A : Type} (xs : List A) (p : A -> Bool) (w : A -> Nat) (d : Nat)
    (hw : forall x, p x = true -> d <= w x) :
    xs.countP p * d <= (xs.map w).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      rw [List.countP_cons, List.map_cons, List.sum_cons]
      cases hp : p x with
      | false =>
          simp
          omega
      | true =>
          have hx := hw x hp
          simp [Nat.succ_mul]
          omega

/-- Nat version of the upper-tail exponential Markov estimate. -/
theorem lotteryAtLeast_mul_twoPow_le_upperMoment
    (k T M : Nat) :
    lotteryAtLeastWordCount k 0 T M * 2 ^ M <=
      lotteryUpperMoment k T := by
  unfold lotteryAtLeastWordCount lotteryPredWordCount lotteryUpperMoment
  apply countP_mul_le_sum
  intro w hw
  simp only [decide_eq_true_eq] at hw
  simp only [show lotteryOffset 0 = lotteryFresh from rfl] at hw
  exact Nat.pow_le_pow_right (by omega) hw

/-- Nat version of the lower-tail exponential Markov estimate. -/
theorem lotteryAtMost_mul_twoPow_le_lowerMoment
    (k T M : Nat) :
    lotteryAtMostWordCount k 0 T M * 2 ^ T <=
      lotteryLowerMoment k T M := by
  unfold lotteryAtMostWordCount lotteryPredWordCount lotteryLowerMoment
  apply countP_mul_le_sum
  intro w hw
  simp only [decide_eq_true_eq] at hw
  simp only [show lotteryOffset 0 = lotteryFresh from rfl] at hw
  exact Nat.pow_le_pow_right (by omega) (by omega)

/-- The moment estimates imply both literal binary-word inequalities. -/
theorem lotteryCountArithmetic_of_moments
    (hm : LotteryTailMomentArithmetic) :
    LotteryCountArithmetic := by
  intro k c hk hc
  rcases hm k c hk hc with ⟨h7, h8⟩
  constructor
  · unfold LotteryL7Arithmetic
    have hmarkov :=
      lotteryAtLeast_mul_twoPow_le_upperMoment
        k (lotteryL7Horizon k c) (lotteryTarget k c)
    rw [lotteryUpperMoment_eq_dp] at hmarkov
    have hscaled := Nat.mul_le_mul_left (2 ^ (c * k)) hmarkov
    have hchain := Nat.le_trans hscaled h7
    have hcancel :
        2 ^ (lotteryTarget k c) *
            (2 ^ (c * k) *
              lotteryAtLeastDP k 0
                (lotteryL7Horizon k c) (lotteryTarget k c)) <=
          2 ^ (lotteryTarget k c) *
            2 ^ (lotteryL7Horizon k c) := by
      calc
        _ = 2 ^ (c * k) *
            (lotteryAtLeastWordCount k 0
              (lotteryL7Horizon k c) (lotteryTarget k c) *
                2 ^ (lotteryTarget k c)) := by
                  rw [lotteryAtLeastWordCount_eq_dp]
                  ac_rfl
        _ <= 2 ^ (lotteryL7Horizon k c + lotteryTarget k c) := hchain
        _ = _ := by rw [Nat.pow_add]; ac_rfl
    exact Nat.le_of_mul_le_mul_left hcancel (Nat.pow_pos (by omega))
  · unfold LotteryL8Arithmetic
    have hmarkov :=
      lotteryAtMost_mul_twoPow_le_lowerMoment
        k (lotteryL8Horizon k c) (lotteryTarget k c)
    rw [lotteryLowerMoment_eq_dp] at hmarkov
    have hscaled := Nat.mul_le_mul_left (2 ^ (c * k)) hmarkov
    have hchain := Nat.le_trans hscaled h8
    have hcancel :
        2 ^ (lotteryL8Horizon k c) *
            (2 ^ (c * k) *
              lotteryAtMostDP k 0
                (lotteryL8Horizon k c) (lotteryTarget k c)) <=
          2 ^ (lotteryL8Horizon k c) *
            2 ^ (lotteryL8Horizon k c) := by
      calc
        _ = 2 ^ (c * k) *
            (lotteryAtMostWordCount k 0
              (lotteryL8Horizon k c) (lotteryTarget k c) *
                2 ^ (lotteryL8Horizon k c)) := by
                  rw [lotteryAtMostWordCount_eq_dp]
                  ac_rfl
        _ <= 2 ^ (lotteryL8Horizon k c + lotteryL8Horizon k c) := hchain
        _ = _ := by rw [Nat.pow_add]
    exact Nat.le_of_mul_le_mul_left hcancel (Nat.pow_pos (by omega))

theorem lotteryCountBounds_of_moments
    (hm : LotteryTailMomentArithmetic) :
    LotteryCountBounds :=
  lotteryCountBounds_of_arithmetic (lotteryCountArithmetic_of_moments hm)

#print axioms lotteryNatWordSum_succ
#print axioms lotteryNatWordSum_eq_dp
#print axioms lotteryUpperMoment_eq_dp
#print axioms lotteryLowerMoment_eq_dp
#print axioms countP_mul_le_sum
#print axioms lotteryAtLeast_mul_twoPow_le_upperMoment
#print axioms lotteryAtMost_mul_twoPow_le_lowerMoment
#print axioms lotteryCountArithmetic_of_moments
#print axioms lotteryCountBounds_of_moments

end PPL.Probability
