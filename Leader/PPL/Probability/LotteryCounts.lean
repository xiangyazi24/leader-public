import Leader.PPL.Probability.RawCounts

set_option autoImplicit false

namespace PPL.Probability

/-!
Exact finite-word lottery parser for P_PL Algorithm 4.

Convention:
* true  = H = the tracked agent is responder to its left neighbor;
* false = T = the tracked agent is initiator to its right neighbor.

A T closes a losing round and resets the current head run.
The kth consecutive H closes a winning round and resets the run.
A final nonempty H-run that has not reached k closes no round.
-/

structure LotteryState where
  headRun : Nat
  wins : Nat
  rounds : Nat
  deriving DecidableEq, Repr

def lotteryFresh : LotteryState :=
  { headRun := 0, wins := 0, rounds := 0 }

def lotteryOffset (h : Nat) : LotteryState :=
  { headRun := h, wins := 0, rounds := 0 }

def lotteryStep (k : Nat) (s : LotteryState) (head : Bool) :
    LotteryState :=
  if head then
    if k <= s.headRun + 1 then
      { headRun := 0, wins := s.wins + 1, rounds := s.rounds + 1 }
    else
      { s with headRun := s.headRun + 1 }
  else
    { headRun := 0, wins := s.wins, rounds := s.rounds + 1 }

def lotteryRun (k : Nat) (s : LotteryState) :
    List Bool -> LotteryState
  | [] => s
  | b :: w => lotteryRun k (lotteryStep k s b) w

/-- All H/T words of exact length T.  T is listed first, then H. -/
def allHTWords : Nat -> List (List Bool)
  | 0 => [[]]
  | T + 1 =>
      (allHTWords T).map (fun w => false :: w) ++
        (allHTWords T).map (fun w => true :: w)

theorem allHTWords_length (T : Nat) :
    (allHTWords T).length = 2 ^ T := by
  induction T with
  | zero => rfl
  | succ T ih =>
      simp [allHTWords, ih, Nat.pow_succ]
      omega

/-- Exact word count for an arbitrary Boolean predicate on the final parser
state. -/
def lotteryPredWordCount
    (k : Nat) (s : LotteryState) (T : Nat)
    (p : LotteryState -> Bool) : Nat :=
  (allHTWords T).countP (fun w => p (lotteryRun k s w))

/-- Closed recurrence for the same count. -/
def lotteryPredDP (k : Nat) (p : LotteryState -> Bool) :
    Nat -> LotteryState -> Nat
  | 0, s => if p s then 1 else 0
  | T + 1, s =>
      lotteryPredDP k p T (lotteryStep k s false) +
        lotteryPredDP k p T (lotteryStep k s true)

theorem lotteryPredWordCount_succ
    (k T : Nat) (s : LotteryState) (p : LotteryState -> Bool) :
    lotteryPredWordCount k s (T + 1) p =
      lotteryPredWordCount k (lotteryStep k s false) T p +
        lotteryPredWordCount k (lotteryStep k s true) T p := by
  unfold lotteryPredWordCount
  rw [allHTWords, List.countP_append, List.countP_map, List.countP_map]
  simp only [Function.comp_def, lotteryRun]

theorem lotteryPredWordCount_eq_dp
    (k T : Nat) (s : LotteryState) (p : LotteryState -> Bool) :
    lotteryPredWordCount k s T p =
      lotteryPredDP k p T s := by
  induction T generalizing s with
  | zero =>
      simp only [lotteryPredWordCount, allHTWords, lotteryRun,
        List.countP_cons, List.countP_nil, Nat.zero_add, lotteryPredDP]
      rfl
  | succ T ih =>
      rw [lotteryPredWordCount_succ, lotteryPredDP, ih, ih]

/-- Exact count for one complete parser outcome. -/
def lotteryOutcomeCount
    (k : Nat) (s : LotteryState) (T : Nat)
    (target : LotteryState) : Nat :=
  lotteryPredWordCount k s T (fun u => decide (u = target))

/-- The same exact outcome count, in closed recurrence form. -/
def lotteryOutcomeDP
    (k : Nat) (s : LotteryState) (T : Nat)
    (target : LotteryState) : Nat :=
  lotteryPredDP k (fun u => decide (u = target)) T s

theorem lotteryOutcomeCount_eq_dp
    (k : Nat) (s : LotteryState) (T : Nat)
    (target : LotteryState) :
    lotteryOutcomeCount k s T target =
      lotteryOutcomeDP k s T target := by
  exact lotteryPredWordCount_eq_dp
    k T s (fun u => decide (u = target))

def lotteryAtLeastWordCount
    (k h T M : Nat) : Nat :=
  lotteryPredWordCount k (lotteryOffset h) T
    (fun s => decide (M <= s.wins))

def lotteryAtMostWordCount
    (k h T M : Nat) : Nat :=
  lotteryPredWordCount k (lotteryOffset h) T
    (fun s => decide (s.wins <= M))

def lotteryAtLeastDP
    (k h T M : Nat) : Nat :=
  lotteryPredDP k (fun s => decide (M <= s.wins)) T
    (lotteryOffset h)

def lotteryAtMostDP
    (k h T M : Nat) : Nat :=
  lotteryPredDP k (fun s => decide (s.wins <= M)) T
    (lotteryOffset h)

theorem lotteryAtLeastWordCount_eq_dp
    (k h T M : Nat) :
    lotteryAtLeastWordCount k h T M =
      lotteryAtLeastDP k h T M := by
  exact lotteryPredWordCount_eq_dp
    k T (lotteryOffset h) (fun s => decide (M <= s.wins))

theorem lotteryAtMostWordCount_eq_dp
    (k h T M : Nat) :
    lotteryAtMostWordCount k h T M =
      lotteryAtMostDP k h T M := by
  exact lotteryPredWordCount_eq_dp
    k T (lotteryOffset h) (fun s => decide (s.wins <= M))

/-! Paper Lemmas 7 and 8, exact Nat interfaces. -/

def lotteryL7Horizon (k c : Nat) : Nat :=
  4 * c * k * 2 ^ k

def lotteryL8Horizon (k c : Nat) : Nat :=
  64 * c * k * 2 ^ k

def lotteryTarget (k c : Nat) : Nat :=
  8 * c * k

/-- Pure arithmetic leaf for Lemma 7 after the parser/count equivalence has
been discharged.  Bad means wins >= 8*c*k. -/
def LotteryL7Arithmetic (k c : Nat) : Prop :=
  2 ^ (c * k) *
      lotteryAtLeastDP k 0
        (lotteryL7Horizon k c) (lotteryTarget k c) <=
    2 ^ lotteryL7Horizon k c

/-- Pure arithmetic leaf for Lemma 8 after the parser/count equivalence has
been discharged.  Bad means wins <= 8*c*k, matching the paper's strict
good event wins > 8*c*k. -/
def LotteryL8Arithmetic (k c : Nat) : Prop :=
  2 ^ (c * k) *
      lotteryAtMostDP k 0
        (lotteryL8Horizon k c) (lotteryTarget k c) <=
    2 ^ lotteryL8Horizon k c

/-- The only remaining arithmetic interface in this file. -/
def LotteryCountArithmetic : Prop :=
  forall k c : Nat, 1 <= k -> 1 <= c ->
    LotteryL7Arithmetic k c ∧ LotteryL8Arithmetic k c

/-- Frozen open-node statement in literal binary-word counting form. -/
def LotteryCountBounds : Prop :=
  forall k c : Nat, 1 <= k -> 1 <= c ->
    (2 ^ (c * k) *
        lotteryAtLeastWordCount k 0
          (lotteryL7Horizon k c) (lotteryTarget k c) <=
      2 ^ lotteryL7Horizon k c) ∧
    (2 ^ (c * k) *
        lotteryAtMostWordCount k 0
          (lotteryL8Horizon k c) (lotteryTarget k c) <=
      2 ^ lotteryL8Horizon k c)

theorem lotteryCountBounds_of_arithmetic
    (h : LotteryCountArithmetic) :
    LotteryCountBounds := by
  intro k c hk hc
  rcases h k c hk hc with ⟨h7, h8⟩
  unfold LotteryL7Arithmetic at h7
  unfold LotteryL8Arithmetic at h8
  constructor
  · rw [lotteryAtLeastWordCount_eq_dp]
    exact h7
  · rw [lotteryAtMostWordCount_eq_dp]
    exact h8

/-! Arbitrary initial hits: one partial head-run offset. -/

/-- Coupling invariant between the fresh parser a and an offset parser b.
Either they have equal wins and b is farther through the current head run,
or b has exactly one extra win and a is farther through the current run. -/
def LotteryOffsetRel (a b : LotteryState) : Prop :=
  (b.wins = a.wins ∧ a.headRun <= b.headRun) ∨
    (b.wins = a.wins + 1 ∧ b.headRun <= a.headRun)

private theorem lotteryOffsetRel_step
    (k : Nat) {a b : LotteryState}
    (h : LotteryOffsetRel a b) (x : Bool) :
    LotteryOffsetRel (lotteryStep k a x) (lotteryStep k b x) := by
  unfold LotteryOffsetRel at h ⊢
  rcases h with h | h
  · rcases h with ⟨hw, hr⟩
    cases x with
    | false =>
        left
        constructor
        · simpa [lotteryStep] using hw
        · simp [lotteryStep]
    | true =>
        by_cases ha : k <= a.headRun + 1
        · have hb : k <= b.headRun + 1 := by omega
          left
          constructor
          · simp [lotteryStep, ha, hb]
            omega
          · simp [lotteryStep, ha, hb]
        · by_cases hb : k <= b.headRun + 1
          · right
            constructor
            · simp [lotteryStep, ha, hb]
              omega
            · simp [lotteryStep, ha, hb]
          · left
            constructor
            · simp [lotteryStep, ha, hb]
              omega
            · simp [lotteryStep, ha, hb]
              omega
  · rcases h with ⟨hw, hr⟩
    cases x with
    | false =>
        right
        constructor
        · simpa [lotteryStep] using hw
        · simp [lotteryStep]
    | true =>
        by_cases hb : k <= b.headRun + 1
        · have ha : k <= a.headRun + 1 := by omega
          right
          constructor
          · simp [lotteryStep, ha, hb]
            omega
          · simp [lotteryStep, ha, hb]
        · by_cases ha : k <= a.headRun + 1
          · left
            constructor
            · simp [lotteryStep, ha, hb]
              omega
            · simp [lotteryStep, ha, hb]
          · right
            constructor
            · simp [lotteryStep, ha, hb]
              omega
            · simp [lotteryStep, ha, hb]
              omega

private theorem lotteryOffsetRel_start (h : Nat) :
    LotteryOffsetRel lotteryFresh (lotteryOffset h) := by
  left
  constructor <;> simp [lotteryFresh, lotteryOffset]

private theorem lotteryOffsetRel_run
    (k : Nat) {a b : LotteryState}
    (h : LotteryOffsetRel a b) (word : List Bool) :
    LotteryOffsetRel (lotteryRun k a word) (lotteryRun k b word) := by
  induction word generalizing a b with
  | nil =>
      simpa [lotteryRun] using h
  | cons x xs ih =>
      simp only [lotteryRun]
      apply ih
      exact lotteryOffsetRel_step k h x

/-- Starting from arbitrary hits can add at most one lottery win and can
never reduce the number of wins, compared with hits=0 on the same H/T word. -/
theorem lotteryHeadOffset_pointwise
    (k h : Nat) (word : List Bool) :
    (lotteryRun k lotteryFresh word).wins <=
        (lotteryRun k (lotteryOffset h) word).wins ∧
      (lotteryRun k (lotteryOffset h) word).wins <=
        (lotteryRun k lotteryFresh word).wins + 1 := by
  have hr :=
    lotteryOffsetRel_run k (lotteryOffsetRel_start h) word
  unfold LotteryOffsetRel at hr
  rcases hr with h0 | h1
  · rcases h0 with ⟨hw, _⟩
    omega
  · rcases h1 with ⟨hw, _⟩
    omega

private theorem countP_mono
    {A : Type} (xs : List A) (p q : A -> Bool)
    (hpq : forall x, p x = true -> q x = true) :
    xs.countP p <= xs.countP q := by
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

/-- A partial initial head run can only help a lower-tail event: if the
offset parser still has at most M wins, then the fresh parser does too. -/
theorem lotteryOffsetAtMost_le_fresh
    (k h T M : Nat) :
    lotteryAtMostWordCount k h T M <=
      lotteryAtMostWordCount k 0 T M := by
  unfold lotteryAtMostWordCount
  apply countP_mono
  intro w hw
  simp only [decide_eq_true_eq] at hw ⊢
  simp only [show lotteryOffset 0 = lotteryFresh from rfl] at hw ⊢
  have hb := lotteryHeadOffset_pointwise k h w
  omega

/-- If the offset parser has at least M+1 wins, the fresh parser has at
least M wins.  This is the one-win head-offset loss. -/
theorem lotteryOffsetAtLeast_succ_le_fresh
    (k h T M : Nat) :
    lotteryAtLeastWordCount k h T (M + 1) <=
      lotteryAtLeastWordCount k 0 T M := by
  unfold lotteryAtLeastWordCount
  apply countP_mono
  intro w hw
  simp only [decide_eq_true_eq] at hw ⊢
  simp only [show lotteryOffset 0 = lotteryFresh from rfl] at hw ⊢
  have hb := lotteryHeadOffset_pointwise k h w
  omega

/-- Conversely, every fresh-parser high-win word is also a high-win word
from an arbitrary nonnegative initial head offset. -/
theorem lotteryFreshAtLeast_le_offset
    (k h T M : Nat) :
    lotteryAtLeastWordCount k 0 T M <=
      lotteryAtLeastWordCount k h T M := by
  unfold lotteryAtLeastWordCount
  apply countP_mono
  intro w hw
  simp only [decide_eq_true_eq] at hw ⊢
  simp only [show lotteryOffset 0 = lotteryFresh from rfl] at hw ⊢
  have hb := lotteryHeadOffset_pointwise k h w
  omega

/-- Frozen arbitrary-hits interface.  The hypotheses 1<=k and h<=k are the
literal State-domain hypotheses; the proved pointwise coupling is stronger. -/
def WLGHeadOffsetBounds : Prop :=
  forall k h T M : Nat, 1 <= k -> h <= k ->
    lotteryAtMostWordCount k h T M <=
        lotteryAtMostWordCount k 0 T M ∧
      lotteryAtLeastWordCount k h T (M + 1) <=
        lotteryAtLeastWordCount k 0 T M ∧
      lotteryAtLeastWordCount k 0 T M <=
        lotteryAtLeastWordCount k h T M

theorem wlgHeadOffsetBounds :
    WLGHeadOffsetBounds := by
  intro k h T M hk hh
  exact ⟨
    lotteryOffsetAtMost_le_fresh k h T M,
    ⟨
      lotteryOffsetAtLeast_succ_le_fresh k h T M,
      lotteryFreshAtLeast_le_offset k h T M
    ⟩
  ⟩

#print axioms allHTWords_length
#print axioms lotteryPredWordCount_succ
#print axioms lotteryPredWordCount_eq_dp
#print axioms lotteryOutcomeCount_eq_dp
#print axioms lotteryAtLeastWordCount_eq_dp
#print axioms lotteryAtMostWordCount_eq_dp
#print axioms lotteryCountBounds_of_arithmetic
#print axioms lotteryOffsetRel_step
#print axioms lotteryOffsetRel_start
#print axioms lotteryOffsetRel_run
#print axioms lotteryHeadOffset_pointwise
#print axioms countP_mono
#print axioms lotteryOffsetAtMost_le_fresh
#print axioms lotteryOffsetAtLeast_succ_le_fresh
#print axioms lotteryFreshAtLeast_le_offset
#print axioms wlgHeadOffsetBounds

end PPL.Probability
