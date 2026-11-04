import Leader.Wu.Scheduler.Probability

/-!
# Fixed ordered-word bounds for the uniform scheduler

This module counts schedules that fail to contain one fixed prescribed word
as an ordered subsequence.  The word is static: its next requested edge is
determined only by the unmatched suffix, never by the evolving protocol
state.

The counting proof uses an augmented greedy score.  While the prescribed word
is unfinished, the unique score-incrementing edge is its next symbol.  After
completion, a fixed fallback edge remains score-incrementing.  Consequently
every scheduler-tree node has one child that preserves the dyadic weight and
`n - 1` children that double it, including nodes below a completed match.  The
total weight at horizon `H` is therefore exactly `(2*n - 1)^H`.  On failing
schedules the augmented score is still the ordinary greedy progress, which
gives the required upper bound without assigning capped progress to completed
paths.
-/

namespace PPLLOrderedWordScheduler

set_option autoImplicit false

/-! ## Augmented greedy matching -/

/-- State of the fixed-word greedy matcher.  `pending` is the unmatched suffix;
`score` also continues to count occurrences of a fixed fallback edge after the
word has completed. -/
structure GreedyWordState (n : Nat) where
  pending : DetSchedule n
  score : Nat

/-- The unique edge that increments the augmented score at the next step. -/
def GreedyWordState.expected {n : Nat}
    (fallback : Fin n) (st : GreedyWordState n) : Fin n :=
  match st.pending with
  | [] => fallback
  | e :: _ => e

/-- One greedy matcher step.  A matching edge consumes one requested symbol;
after completion the fallback edge increments only the auxiliary score. -/
def greedyWordStep {n : Nat} (fallback : Fin n)
    (st : GreedyWordState n) (fired : Fin n) : GreedyWordState n :=
  if fired = st.expected fallback then
    { pending := match st.pending with
        | [] => []
        | _ :: rest => rest
      score := st.score + 1 }
  else st

/-- Run the augmented matcher from an arbitrary state. -/
def greedyWordRunFrom {n : Nat} (fallback : Fin n) :
    GreedyWordState n -> DetSchedule n -> GreedyWordState n
  | st, [] => st
  | st, e :: rest =>
      greedyWordRunFrom fallback (greedyWordStep fallback st e) rest

/-- Run the matcher on a prescribed word, starting with score zero. -/
def greedyWordRun {n : Nat} (fallback : Fin n)
    (word schedule : DetSchedule n) : GreedyWordState n :=
  greedyWordRunFrom fallback { pending := word, score := 0 } schedule

/-- Running concatenated schedules is sequential matcher execution. -/
theorem greedyWordRunFrom_append {n : Nat} (fallback : Fin n)
    (st : GreedyWordState n) (first second : DetSchedule n) :
    greedyWordRunFrom fallback st (first ++ second) =
      greedyWordRunFrom fallback
        (greedyWordRunFrom fallback st first) second := by
  induction first generalizing st with
  | nil => rfl
  | cons e rest ih =>
      simp only [List.cons_append, greedyWordRunFrom]
      exact ih _

private theorem greedyWordStep_score_le {n : Nat} (fallback : Fin n)
    (st : GreedyWordState n) (fired : Fin n) :
    (greedyWordStep fallback st fired).score <= st.score + 1 := by
  unfold greedyWordStep
  split <;> simp

/-- The augmented score grows by at most one per scheduled edge. -/
theorem greedyWordRunFrom_score_le {n : Nat} (fallback : Fin n)
    (st : GreedyWordState n) (schedule : DetSchedule n) :
    (greedyWordRunFrom fallback st schedule).score <=
      st.score + schedule.length := by
  induction schedule generalizing st with
  | nil => simp [greedyWordRunFrom]
  | cons fired rest ih =>
      have htail := ih (greedyWordStep fallback st fired)
      have hstep := greedyWordStep_score_le fallback st fired
      simp only [greedyWordRunFrom, List.length_cons]
      omega

/-- Starting from an empty pending word, the pending word remains empty. -/
theorem greedyWordRunFrom_pending_nil {n : Nat} (fallback : Fin n)
    (st : GreedyWordState n) (schedule : DetSchedule n)
    (hst : st.pending = []) :
    (greedyWordRunFrom fallback st schedule).pending = [] := by
  induction schedule generalizing st with
  | nil => exact hst
  | cons fired rest ih =>
      apply ih
      by_cases hfire : fired = fallback <;>
        simp [greedyWordStep, GreedyWordState.expected, hst, hfire]

private theorem greedyWordStep_balance_of_pending_ne_nil {n : Nat}
    (fallback : Fin n) (st : GreedyWordState n) (fired : Fin n)
    (hst : st.pending ≠ []) :
    (greedyWordStep fallback st fired).score +
        (greedyWordStep fallback st fired).pending.length =
      st.score + st.pending.length := by
  cases hpending : st.pending with
  | nil => exact False.elim (hst hpending)
  | cons requested rest =>
      by_cases hfire : fired = requested
      · simp [greedyWordStep, GreedyWordState.expected, hpending, hfire]
        omega
      · simp [greedyWordStep, GreedyWordState.expected, hpending, hfire]

/-- Until completion, score plus remaining word length is invariant.  The
final nonemptiness premise excludes precisely the post-completion fallback
scoring regime. -/
theorem greedyWordRunFrom_balance_of_final_nonempty {n : Nat}
    (fallback : Fin n) (st : GreedyWordState n)
    (schedule : DetSchedule n)
    (hfinal :
      (greedyWordRunFrom fallback st schedule).pending ≠ []) :
    (greedyWordRunFrom fallback st schedule).score +
        (greedyWordRunFrom fallback st schedule).pending.length =
      st.score + st.pending.length := by
  induction schedule generalizing st with
  | nil => rfl
  | cons fired rest ih =>
      have htail := ih (greedyWordStep fallback st fired) hfinal
      have hst : st.pending ≠ [] := by
        intro hnil
        exact hfinal (greedyWordRunFrom_pending_nil fallback st
          (fired :: rest) hnil)
      exact htail.trans
        (greedyWordStep_balance_of_pending_ne_nil fallback st fired hst)

/-- Every failed match has augmented score strictly below the prescribed word
length; on such paths the augmented score is ordinary greedy progress. -/
theorem greedyWordRun_score_lt_word_length_of_pending_nonempty {n : Nat}
    (fallback : Fin n) (word schedule : DetSchedule n)
    (hfail : (greedyWordRun fallback word schedule).pending ≠ []) :
    (greedyWordRun fallback word schedule).score < word.length := by
  have hbalance := greedyWordRunFrom_balance_of_final_nonempty fallback
    ({ pending := word, score := 0 } : GreedyWordState n) schedule hfail
  have hbalance' : (greedyWordRun fallback word schedule).score +
      (greedyWordRun fallback word schedule).pending.length =
      word.length := by
    simpa [greedyWordRun] using hbalance
  have hpos : 0 < (greedyWordRun fallback word schedule).pending.length :=
    List.length_pos_iff.mpr hfail
  omega

/-- Greedy completion witnesses that the fixed word occurs as an ordered
subsequence of the schedule. -/
theorem greedyWordRunFrom_done_sublist {n : Nat} (fallback : Fin n)
    (word schedule : DetSchedule n) (initialScore : Nat)
    (hdone :
      (greedyWordRunFrom fallback
        { pending := word, score := initialScore } schedule).pending = []) :
    word.Sublist schedule := by
  induction schedule generalizing word initialScore with
  | nil =>
      simp only [greedyWordRunFrom] at hdone
      have hword : word = [] := hdone
      subst word
      exact List.Sublist.slnil
  | cons fired rest ih =>
      cases word with
      | nil => exact List.nil_sublist _
      | cons requested pending =>
          by_cases hfire : fired = requested
          · subst fired
            have htail : pending.Sublist rest := by
              apply ih (initialScore := initialScore + 1)
              simpa [greedyWordRunFrom, greedyWordStep,
                GreedyWordState.expected] using hdone
            exact List.Sublist.cons_cons requested htail
          · have htail : (requested :: pending).Sublist rest := by
              apply ih (initialScore := initialScore)
              simpa [greedyWordRunFrom, greedyWordStep,
                GreedyWordState.expected, hfire] using hdone
            exact List.Sublist.cons fired htail

/-- Public completion-to-subsequence bridge for a zero-score matcher run. -/
theorem greedyWordRun_done_sublist {n : Nat} (fallback : Fin n)
    (word schedule : DetSchedule n)
    (hdone : (greedyWordRun fallback word schedule).pending = []) :
    word.Sublist schedule := by
  exact greedyWordRunFrom_done_sublist fallback word schedule 0 hdone

/-- Conversely, every ordered-subsequence witness is found by the greedy
matcher.  Together with `greedyWordRun_done_sublist`, this identifies the
operational matcher with `List.Sublist`. -/
theorem greedyWordRunFrom_done_of_sublist {n : Nat} (fallback : Fin n)
    (word schedule : DetSchedule n) (initialScore : Nat)
    (hsub : word.Sublist schedule) :
    (greedyWordRunFrom fallback
      { pending := word, score := initialScore } schedule).pending = [] := by
  induction schedule generalizing word initialScore with
  | nil =>
      have hlength : word.length <= 0 := by simpa using hsub.length_le
      have hword : word = [] :=
        List.eq_nil_of_length_eq_zero (by omega)
      subst word
      rfl
  | cons fired rest ih =>
      cases word with
      | nil =>
          apply greedyWordRunFrom_pending_nil fallback
            ({ pending := [], score := initialScore } : GreedyWordState n)
            (fired :: rest)
          rfl
      | cons requested pending =>
          by_cases hfire : fired = requested
          · have htail : pending.Sublist rest := by
              rcases List.sublist_cons_iff.mp hsub with hskip | ⟨tail, heq, ht⟩
              · exact (List.sublist_cons_self requested pending).trans hskip
              · cases heq
                exact ht
            simp only [greedyWordRunFrom]
            rw [show greedyWordStep fallback
                { pending := requested :: pending, score := initialScore }
                fired =
                ({ pending := pending, score := initialScore + 1 } :
                  GreedyWordState n) by
              simp [greedyWordStep, GreedyWordState.expected, hfire]]
            exact ih pending (initialScore + 1) htail
          · have htail : (requested :: pending).Sublist rest := by
              rcases List.sublist_cons_iff.mp hsub with hskip | ⟨tail, heq, _⟩
              · exact hskip
              · have hhead : requested = fired := by
                  exact List.cons.inj heq |>.1
                exact False.elim (hfire hhead.symm)
            simp only [greedyWordRunFrom]
            rw [show greedyWordStep fallback
                { pending := requested :: pending, score := initialScore }
                fired =
                ({ pending := requested :: pending, score := initialScore } :
                  GreedyWordState n) by
              simp [greedyWordStep, GreedyWordState.expected, hfire]]
            exact ih (requested :: pending) initialScore htail

/-- Greedy completion is equivalent to occurrence of the prescribed word as
an ordered subsequence. -/
theorem greedyWordRun_done_iff_sublist {n : Nat} (fallback : Fin n)
    (word schedule : DetSchedule n) :
    (greedyWordRun fallback word schedule).pending = [] ↔
      word.Sublist schedule := by
  constructor
  · exact greedyWordRun_done_sublist fallback word schedule
  · intro hsub
    exact greedyWordRunFrom_done_of_sublist fallback word schedule 0 hsub

/-! ## Exact augmented dyadic weight -/

/-- Dyadic weight of one scheduler word at a fixed horizon. -/
def greedyWordWeight {n : Nat} (fallback : Fin n)
    (word : DetSchedule n) (horizon : Nat) (schedule : DetSchedule n) : Nat :=
  2 ^ (horizon - (greedyWordRun fallback word schedule).score)

/-- Sum of augmented dyadic weights over the exact uniform scheduler list. -/
def greedyWordWeightedTotal {n : Nat} (fallback : Fin n)
    (word : DetSchedule n) (horizon : Nat) : Nat :=
  ((allSchedules n horizon).map
    (greedyWordWeight fallback word horizon)).sum

private theorem nodup_ofFn_of_injective {n : Nat} {alpha : Type}
    (f : Fin n -> alpha) (hf : Function.Injective f) :
    (List.ofFn f).Nodup := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.ofFn_succ, List.nodup_cons]
      constructor
      · intro hmem
        rw [List.mem_ofFn] at hmem
        obtain ⟨i, hi⟩ := hmem
        have h := hf hi
        cases h
      · apply ih
        intro i j hij
        exact Fin.succ_inj.mp (hf hij)

private theorem sum_map_const {alpha : Type} (xs : List alpha) (c : Nat) :
    (xs.map fun _ => c).sum = xs.length * c := by
  induction xs with
  | nil => simp
  | cons _ xs ih =>
      rw [List.map_cons, List.sum_cons, ih, List.length_cons]
      simp only [Nat.succ_mul]
      omega

private theorem pred_mul (length c : Nat) (hlength : 0 < length) :
    c + (length - 1) * c = length * c := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero
    (by omega : length ≠ 0)
  simp [Nat.succ_mul, Nat.add_comm]

private theorem sum_one_exception
    {alpha : Type}
    [BEq alpha] [LawfulBEq alpha]
    (xs : List alpha) (a : alpha) (f : alpha -> Nat) (c : Nat)
    (hnodup : xs.Nodup) (ha : a ∈ xs)
    (hother : forall z, z ∈ xs -> z ≠ a -> f z = c) :
    (xs.map f).sum = f a + (xs.length - 1) * c := by
  induction xs with
  | nil => simp at ha
  | cons x xs ih =>
      rw [List.nodup_cons] at hnodup
      by_cases hxa : x = a
      · subst x
        have hall : xs.map f = xs.map (fun _ => c) := by
          apply List.map_congr_left
          intro z hz
          exact hother z (by simp [hz])
            (by intro q; subst z; exact hnodup.1 hz)
        rw [List.map_cons, List.sum_cons, hall, sum_map_const]
        simp
      · have hat : a ∈ xs := by
          rcases List.mem_cons.mp ha with hax | hat
          · exact absurd hax.symm hxa
          · exact hat
        have hot : forall z, z ∈ xs -> z ≠ a -> f z = c := by
          intro z hz
          exact hother z (by simp [hz])
        have hi := ih hnodup.2 hat hot
        have hx : f x = c := hother x (by simp) hxa
        rw [List.map_cons, List.sum_cons, hx, hi, List.length_cons]
        have hpos : 0 < xs.length :=
          List.length_pos_iff.mpr (List.ne_nil_of_mem hat)
        have hc := pred_mul xs.length c hpos
        have hsub : xs.length + 1 - 1 = xs.length := by omega
        rw [hsub]
        omega

private theorem sum_map_flatMap {alpha beta : Type} (xs : List alpha)
    (children : alpha -> List beta) (value : beta -> Nat) :
    ((xs.flatMap children).map value).sum =
      (xs.map (fun x => ((children x).map value).sum)).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih, List.sum_append]

private theorem sum_map_mul_left {alpha : Type} (xs : List alpha)
    (c : Nat) (f : alpha -> Nat) :
    (xs.map (fun x => c * f x)).sum = c * (xs.map f).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih, Nat.mul_add]

private theorem greedyWordStep_score {n : Nat} (fallback : Fin n)
    (st : GreedyWordState n) (fired : Fin n) :
    (greedyWordStep fallback st fired).score =
      if fired = st.expected fallback then st.score + 1 else st.score := by
  by_cases h : fired = st.expected fallback <;>
    simp [greedyWordStep, h]

private theorem greedyWordWeight_append_singleton {n : Nat}
    (fallback : Fin n) (word pre : DetSchedule n)
    (horizon : Nat) (hlen : pre.length = horizon) (fired : Fin n) :
    greedyWordWeight fallback word (horizon + 1) (pre ++ [fired]) =
      if fired = (greedyWordRun fallback word pre).expected fallback then
        greedyWordWeight fallback word horizon pre
      else 2 * greedyWordWeight fallback word horizon pre := by
  have hscore : (greedyWordRun fallback word pre).score <= horizon := by
    have h := greedyWordRunFrom_score_le fallback
      ({ pending := word, score := 0 } : GreedyWordState n) pre
    simpa [greedyWordRun, hlen] using h
  have hscore' : (greedyWordRunFrom fallback
      { pending := word, score := 0 } pre).score <= horizon := by
    simpa [greedyWordRun] using hscore
  rw [greedyWordWeight, greedyWordWeight, greedyWordRun,
    greedyWordRun, greedyWordRunFrom_append]
  simp only [greedyWordRunFrom]
  rw [greedyWordStep_score]
  by_cases hfire :
      fired = (greedyWordRunFrom fallback
        { pending := word, score := 0 } pre).expected fallback
  · rw [if_pos hfire, if_pos hfire]
    congr 1
    omega
  · rw [if_neg hfire, if_neg hfire]
    have hexp : horizon + 1 -
          (greedyWordRunFrom fallback
          { pending := word, score := 0 } pre).score =
        (horizon -
          (greedyWordRunFrom fallback
            { pending := word, score := 0 } pre).score) + 1 := by
      omega
    rw [hexp, Nat.pow_succ]
    omega

private theorem greedyWord_childWeight_sum {n : Nat}
    (fallback : Fin n) (word pre : DetSchedule n)
    (horizon : Nat) (hlen : pre.length = horizon) :
    (List.ofFn (fun fired : Fin n =>
      greedyWordWeight fallback word (horizon + 1)
        (pre ++ [fired]))).sum =
      (2 * n - 1) * greedyWordWeight fallback word horizon pre := by
  let expected := (greedyWordRun fallback word pre).expected fallback
  let oldWeight := greedyWordWeight fallback word horizon pre
  let child := fun fired : Fin n =>
    greedyWordWeight fallback word (horizon + 1) (pre ++ [fired])
  have hnodup : (List.ofFn (fun i : Fin n => i)).Nodup := by
    apply nodup_ofFn_of_injective
    intro i j hij
    exact hij
  have hmem : expected ∈ List.ofFn (fun i : Fin n => i) := by
    rw [List.mem_ofFn]
    exact ⟨expected, rfl⟩
  have hother : forall fired,
      fired ∈ List.ofFn (fun i : Fin n => i) -> fired ≠ expected ->
      child fired = 2 * oldWeight := by
    intro fired _ hne
    simpa [child, oldWeight, expected, hne] using
      greedyWordWeight_append_singleton fallback word pre horizon hlen fired
  have hsum := sum_one_exception
    (List.ofFn (fun i : Fin n => i)) expected child (2 * oldWeight)
    hnodup hmem hother
  have hexpected : child expected = oldWeight := by
    simpa [child, oldWeight, expected] using
      greedyWordWeight_append_singleton fallback word pre horizon hlen expected
  have hn : 0 < n := Fin.pos_iff_nonempty.mpr ⟨fallback⟩
  have hcoefficient : 2 * n - 1 = 1 + 2 * (n - 1) := by omega
  have hsum' : (List.ofFn child).sum =
      oldWeight + (n - 1) * (2 * oldWeight) := by
    rw [List.map_ofFn] at hsum
    simp only [List.length_ofFn] at hsum
    have hchildcomp : child ∘ (fun i : Fin n => i) = child := by
      funext i
      rfl
    rw [hchildcomp] at hsum
    simpa only [hexpected] using hsum
  change (List.ofFn child).sum = (2 * n - 1) * oldWeight
  rw [hsum', hcoefficient, Nat.add_mul, Nat.one_mul]
  ac_rfl

/-- The augmented total satisfies the exact one-step recurrence. -/
theorem greedyWordWeightedTotal_succ {n : Nat} (fallback : Fin n)
    (word : DetSchedule n) (horizon : Nat) :
    greedyWordWeightedTotal fallback word (horizon + 1) =
      (2 * n - 1) * greedyWordWeightedTotal fallback word horizon := by
  unfold greedyWordWeightedTotal
  rw [allSchedules, sum_map_flatMap]
  have hchildren :
      ((allSchedules n horizon).map (fun pre =>
        ((List.ofFn (fun fired : Fin n => pre ++ [fired])).map
          (greedyWordWeight fallback word (horizon + 1))).sum)).sum =
      ((allSchedules n horizon).map (fun pre =>
        (2 * n - 1) * greedyWordWeight fallback word horizon pre)).sum := by
    apply congrArg List.sum
    apply List.map_congr_left
    intro pre hpre
    rw [List.map_ofFn]
    exact greedyWord_childWeight_sum fallback word pre horizon
      (allSchedules_schedule_length n horizon pre hpre)
  rw [hchildren, sum_map_mul_left]

/-- Exact augmented weight identity.  The fallback edge is essential after
word completion; using capped ordinary progress would make this equality
false. -/
theorem greedyWordWeightedTotal_eq {n : Nat} (fallback : Fin n)
    (word : DetSchedule n) (horizon : Nat) :
    greedyWordWeightedTotal fallback word horizon = (2 * n - 1) ^ horizon := by
  induction horizon with
  | zero =>
      simp [greedyWordWeightedTotal, allSchedules, greedyWordWeight,
        greedyWordRun, greedyWordRunFrom]
  | succ horizon ih =>
      rw [show horizon + 1 = Nat.succ horizon by rfl,
        greedyWordWeightedTotal_succ, ih, Nat.pow_succ]
      exact Nat.mul_comm _ _

/-! ## Failure count and its dyadic bound -/

/-- Boolean failure test for the fixed greedy matcher. -/
def greedyWordMiss {n : Nat} (fallback : Fin n)
    (word schedule : DetSchedule n) : Bool :=
  match (greedyWordRun fallback word schedule).pending with
  | [] => false
  | _ :: _ => true

/-- The Boolean miss test is exactly ordered-subsequence failure. -/
theorem greedyWordMiss_iff_not_sublist {n : Nat} (fallback : Fin n)
    (word schedule : DetSchedule n) :
    greedyWordMiss fallback word schedule = true ↔
      ¬word.Sublist schedule := by
  rw [← greedyWordRun_done_iff_sublist fallback word schedule]
  cases hpending : (greedyWordRun fallback word schedule).pending with
  | nil => simp [greedyWordMiss, hpending]
  | cons requested pending => simp [greedyWordMiss, hpending]

/-- Number, with exact scheduler multiplicity, of length-`horizon` words that
fail to complete the prescribed ordered word. -/
def greedyWordMissCount {n : Nat} (fallback : Fin n)
    (word : DetSchedule n) (horizon : Nat) : Nat :=
  (allSchedules n horizon).countP (greedyWordMiss fallback word)

/-- Canonical, fallback-free count of scheduler words that do not contain the
fixed prescribed word as an ordered subsequence. -/
def orderedWordMissCount {n : Nat}
    (word : DetSchedule n) (horizon : Nat) : Nat :=
  (allSchedules n horizon).countP
    (fun schedule => decide (¬word.Sublist schedule))

/-- The operational miss count is the literal count of scheduler words for
which the prescribed word is not a `List.Sublist`. -/
theorem greedyWordMissCount_eq_countP_not_sublist {n : Nat}
    (fallback : Fin n) (word : DetSchedule n) (horizon : Nat) :
    greedyWordMissCount fallback word horizon =
      (allSchedules n horizon).countP
        (fun schedule => decide (¬word.Sublist schedule)) := by
  unfold greedyWordMissCount
  apply congrArg (fun predicate => (allSchedules n horizon).countP predicate)
  funext schedule
  apply Bool.eq_iff_iff.mpr
  exact (greedyWordMiss_iff_not_sublist fallback word schedule).trans
    decide_eq_true_iff.symm

/-- The augmented implementation computes the canonical fixed-word miss
count; in particular, its post-completion fallback choice cannot affect the
failure event. -/
theorem greedyWordMissCount_eq_orderedWordMissCount {n : Nat}
    (fallback : Fin n) (word : DetSchedule n) (horizon : Nat) :
    greedyWordMissCount fallback word horizon =
      orderedWordMissCount word horizon := by
  exact greedyWordMissCount_eq_countP_not_sublist fallback word horizon

private theorem countP_mul_le_sum {alpha : Type}
    (xs : List alpha) (p : alpha -> Bool)
    (weight : alpha -> Nat) (scale : Nat)
    (hweight : forall x, x ∈ xs -> p x = true -> scale <= weight x) :
    xs.countP p * scale <= (xs.map weight).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      have htail : forall y, y ∈ xs -> p y = true -> scale <= weight y := by
        intro y hy
        exact hweight y (by simp [hy])
      have hi := ih htail
      rw [List.countP_cons, List.map_cons, List.sum_cons]
      cases hp : p x with
      | false =>
          exact Nat.le_trans (by simpa [hp] using hi) (Nat.le_add_left _ _)
      | true =>
          have hx := hweight x (by simp) hp
          simpa [hp, Nat.add_mul, Nat.add_comm] using Nat.add_le_add hi hx

private theorem two_pow_mono {a b : Nat} (hab : a <= b) :
    2 ^ a <= 2 ^ b := by
  induction b generalizing a with
  | zero =>
      have ha : a = 0 := by omega
      subst a
      exact Nat.le_refl _
  | succ b ih =>
      by_cases ha : a = b + 1
      · subst a
        exact Nat.le_refl _
      · have hab' : a <= b := by omega
        have hprev := ih hab'
        rw [Nat.pow_succ]
        omega

/-- Weighted failure inequality at an arbitrary horizon containing the word
length. -/
theorem greedyWordMissCount_mul_twoPow_le_weightedTotal {n : Nat}
    (fallback : Fin n) (word : DetSchedule n) (horizon : Nat)
    (hlength : word.length <= horizon) :
    greedyWordMissCount fallback word horizon *
        2 ^ (horizon - word.length) <=
      greedyWordWeightedTotal fallback word horizon := by
  unfold greedyWordMissCount greedyWordWeightedTotal
  apply countP_mul_le_sum
  intro schedule hschedule hmiss
  have hfail : (greedyWordRun fallback word schedule).pending ≠ [] := by
    intro hnil
    simp [greedyWordMiss, hnil] at hmiss
  have hscorelt :=
    greedyWordRun_score_lt_word_length_of_pending_nonempty
      fallback word schedule hfail
  have hscore : (greedyWordRun fallback word schedule).score <= word.length :=
    Nat.le_of_lt hscorelt
  have hexponent : horizon - word.length <=
      horizon - (greedyWordRun fallback word schedule).score := by
    omega
  exact two_pow_mono hexponent

/-- The elementary weighted scheduler bound before specializing the horizon. -/
theorem greedyWordMissCount_mul_twoPow_le {n : Nat}
    (fallback : Fin n) (word : DetSchedule n) (horizon : Nat)
    (hlength : word.length <= horizon) :
    greedyWordMissCount fallback word horizon *
        2 ^ (horizon - word.length) <=
      (2 * n - 1) ^ horizon := by
  rw [← greedyWordWeightedTotal_eq fallback word horizon]
  exact greedyWordMissCount_mul_twoPow_le_weightedTotal
    fallback word horizon hlength

/-! ## The fixed horizon `2*n*(L+K)` -/

/-- The first two terms in the binomial expansion give an entirely natural-
number lower bound.  This local induction avoids importing an analytic
inequality for the later scheduler estimate. -/
private theorem pow_first_two_terms_le (a k : Nat) :
    a ^ (k + 1) + (k + 1) * a ^ k <= (a + 1) ^ (k + 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hmul := Nat.mul_le_mul_right (a + 1) ih
      have hlow :
          a ^ (k + 2) + (k + 2) * a ^ (k + 1) <=
            (a ^ (k + 1) + (k + 1) * a ^ k) * (a + 1) := by
        rw [show a ^ (k + 2) = a ^ (k + 1) * a by
          simpa [Nat.add_assoc] using (Nat.pow_succ a (k + 1)),
          Nat.pow_succ]
        grind
      have hchain := Nat.le_trans hlow hmul
      simpa [Nat.add_assoc, Nat.pow_succ] using hchain

/-- One block of `2*n` iid choices loses at least one factor two when the
distinguished symbol is avoided.  This is the integer form of
`2*(1-1/(2n))^(2n) <= 1`. -/
theorem two_mul_pred_pow_two_mul_le (n : Nat) (hn : 0 < n) :
    2 * (2 * n - 1) ^ (2 * n) <= (2 * n) ^ (2 * n) := by
  let a := 2 * n - 1
  have ha : a + 1 = 2 * n := by
    dsimp [a]
    omega
  have hbinomial := pow_first_two_terms_le a a
  have hsecond : a ^ (a + 1) <= (a + 1) * a ^ a := by
    rw [Nat.pow_succ]
    have haa : a <= a + 1 := by omega
    have hmul := Nat.mul_le_mul_right (a ^ a) haa
    simpa [Nat.mul_comm] using hmul
  have hdouble : 2 * a ^ (a + 1) <=
      a ^ (a + 1) + (a + 1) * a ^ a := by
    calc
      2 * a ^ (a + 1) =
          a ^ (a + 1) + a ^ (a + 1) := by omega
      _ <= a ^ (a + 1) + (a + 1) * a ^ a :=
        Nat.add_le_add_left hsecond _
  have hchain := Nat.le_trans hdouble hbinomial
  simpa [ha] using hchain

/-- Raising the preceding `2*n`-step block estimate through `rounds` blocks.
The right side is expanded as `(2*n)^H = 2^H*n^H` for later cancellation. -/
theorem twoPow_mul_predPow_le_twoPow_mul_pow (n rounds : Nat)
    (hn : 0 < n) :
    2 ^ rounds * (2 * n - 1) ^ ((2 * n) * rounds) <=
      2 ^ ((2 * n) * rounds) * n ^ ((2 * n) * rounds) := by
  have hpow := Nat.pow_le_pow_left
    (two_mul_pred_pow_two_mul_le n hn) rounds
  calc
    2 ^ rounds * (2 * n - 1) ^ ((2 * n) * rounds) =
        (2 * (2 * n - 1) ^ (2 * n)) ^ rounds := by
          simp only [Nat.mul_pow, Nat.pow_mul]
    _ <= ((2 * n) ^ (2 * n)) ^ rounds := hpow
    _ = (2 * n) ^ ((2 * n) * rounds) :=
      (Nat.pow_mul (2 * n) (2 * n) rounds).symm
    _ = 2 ^ ((2 * n) * rounds) * n ^ ((2 * n) * rounds) := by
      rw [Nat.mul_pow]

/-- Main prescribed-word scheduler theorem.  At horizon
`H = 2*n*(word.length + K)`, at most a `2^-K` fraction of the exact `n^H`
uniform scheduler words fail the static greedy ordered-subsequence match.  The
statement is division-free: multiplying the failure numerator by `2^K` stays
below the exact scheduler-space cardinality. -/
theorem greedyWordMissCount_mul_twoPow_le_at_horizon {n : Nat}
    (fallback : Fin n) (word : DetSchedule n) (K : Nat) :
    let horizon := 2 * n * (word.length + K)
    greedyWordMissCount fallback word horizon * 2 ^ K <= n ^ horizon := by
  let rounds := word.length + K
  let horizon := 2 * n * rounds
  dsimp only
  have hn : 0 < n := Fin.pos_iff_nonempty.mpr ⟨fallback⟩
  have hfactor : 1 <= 2 * n := by omega
  have hrounds : word.length <= rounds := by
    simp [rounds]
  have hscale : rounds <= (2 * n) * rounds := by
    have hmul := Nat.mul_le_mul_right rounds hfactor
    simpa using hmul
  have hlength : word.length <= horizon :=
    Nat.le_trans hrounds hscale
  have hmiss := greedyWordMissCount_mul_twoPow_le
    fallback word horizon hlength
  have hraised := twoPow_mul_predPow_le_twoPow_mul_pow n rounds hn
  have hscaled := Nat.mul_le_mul_left (2 ^ rounds) hmiss
  have htoFull :
      2 ^ rounds *
          (greedyWordMissCount fallback word horizon *
            2 ^ (horizon - word.length)) <=
        2 ^ horizon * n ^ horizon := by
    exact Nat.le_trans hscaled (by simpa [horizon] using hraised)
  have hexponent : rounds + (horizon - word.length) = horizon + K := by
    dsimp [rounds]
    omega
  have hleft :
      2 ^ rounds *
          (greedyWordMissCount fallback word horizon *
            2 ^ (horizon - word.length)) =
        2 ^ horizon *
          (greedyWordMissCount fallback word horizon * 2 ^ K) := by
    calc
      2 ^ rounds *
          (greedyWordMissCount fallback word horizon *
            2 ^ (horizon - word.length)) =
          greedyWordMissCount fallback word horizon *
            (2 ^ rounds * 2 ^ (horizon - word.length)) := by
              ac_rfl
      _ = greedyWordMissCount fallback word horizon *
          2 ^ (rounds + (horizon - word.length)) := by
            rw [← Nat.pow_add]
      _ = greedyWordMissCount fallback word horizon *
          2 ^ (horizon + K) := by rw [hexponent]
      _ = 2 ^ horizon *
          (greedyWordMissCount fallback word horizon * 2 ^ K) := by
            rw [Nat.pow_add]
            ac_rfl
  rw [hleft] at htoFull
  exact Nat.le_of_mul_le_mul_left htoFull (Nat.pow_pos (by omega))

/-- Quotient form of the main theorem. -/
theorem greedyWordMissCount_le_div_at_horizon {n : Nat}
    (fallback : Fin n) (word : DetSchedule n) (K : Nat) :
    let horizon := 2 * n * (word.length + K)
    greedyWordMissCount fallback word horizon <= n ^ horizon / 2 ^ K := by
  let horizon := 2 * n * (word.length + K)
  dsimp only
  apply (Nat.le_div_iff_mul_le (Nat.pow_pos (by omega))).2
  exact greedyWordMissCount_mul_twoPow_le_at_horizon fallback word K

/-- The same quotient bound written directly against the repository's exact
uniform scheduler-list cardinality. -/
theorem greedyWordMissCount_le_scheduleSpace_div_at_horizon {n : Nat}
    (fallback : Fin n) (word : DetSchedule n) (K : Nat) :
    let horizon := 2 * n * (word.length + K)
    greedyWordMissCount fallback word horizon <=
      (allSchedules n horizon).length / 2 ^ K := by
  simpa only [allSchedules_length] using
    greedyWordMissCount_le_div_at_horizon fallback word K

/-- Fallback-free form of the main division-free theorem.  It also covers the
degenerate alphabet `n = 0`, where every typed prescribed word is empty and
the miss count is zero. -/
theorem orderedWordMissCount_mul_twoPow_le_at_horizon {n : Nat}
    (word : DetSchedule n) (K : Nat) :
    let horizon := 2 * n * (word.length + K)
    orderedWordMissCount word horizon * 2 ^ K <= n ^ horizon := by
  cases n with
  | zero =>
      cases word with
      | nil => simp [orderedWordMissCount, allSchedules]
      | cons impossible _ => exact Fin.elim0 impossible
  | succ n =>
      let fallback : Fin (n + 1) := ⟨0, by omega⟩
      let horizon := 2 * (n + 1) * (word.length + K)
      dsimp only
      rw [← greedyWordMissCount_eq_orderedWordMissCount
        fallback word horizon]
      exact greedyWordMissCount_mul_twoPow_le_at_horizon fallback word K

/-- Fallback-free natural-division form of the fixed-word theorem. -/
theorem orderedWordMissCount_le_div_at_horizon {n : Nat}
    (word : DetSchedule n) (K : Nat) :
    let horizon := 2 * n * (word.length + K)
    orderedWordMissCount word horizon <= n ^ horizon / 2 ^ K := by
  let horizon := 2 * n * (word.length + K)
  dsimp only
  apply (Nat.le_div_iff_mul_le (Nat.pow_pos (by omega))).2
  exact orderedWordMissCount_mul_twoPow_le_at_horizon word K

/-- Exact uniform-list version of the fallback-free quotient bound. -/
theorem orderedWordMissCount_le_scheduleSpace_div_at_horizon {n : Nat}
    (word : DetSchedule n) (K : Nat) :
    let horizon := 2 * n * (word.length + K)
    orderedWordMissCount word horizon <=
      (allSchedules n horizon).length / 2 ^ K := by
  simpa only [allSchedules_length] using
    orderedWordMissCount_le_div_at_horizon word K

/-- Explicit-length wrapper matching the common presentation with a named
prescribed-word length `L`. -/
theorem orderedWordMissCount_mul_twoPow_le_of_length {n : Nat}
    (word : DetSchedule n) (L K : Nat) (hlength : word.length = L) :
    let horizon := 2 * n * (L + K)
    orderedWordMissCount word horizon * 2 ^ K <= n ^ horizon := by
  subst L
  exact orderedWordMissCount_mul_twoPow_le_at_horizon word K

/-- Exact uniform-scheduler quotient bound with an explicit word length. -/
theorem orderedWordMissCount_le_scheduleSpace_div_of_length {n : Nat}
    (word : DetSchedule n) (L K : Nat) (hlength : word.length = L) :
    let horizon := 2 * n * (L + K)
    orderedWordMissCount word horizon <=
      (allSchedules n horizon).length / 2 ^ K := by
  subst L
  exact orderedWordMissCount_le_scheduleSpace_div_at_horizon word K

end PPLLOrderedWordScheduler
