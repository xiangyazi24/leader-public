import Leader.Core.Basic

/-!
# Finite action-tree bounds for predictable stopped trials

This module contains the scheduler-counting core needed by adaptive two-edge
trials.  It deliberately avoids measure theory.  An inactive state is frozen,
so `liveTree` counts exact scheduler words whose stopped endpoint is still
active.  A unit lower drift of the complete `n`-child potential sum then pays
for the entire weighted survival tree.
-/

namespace PredictableTrialFiniteTree

set_option autoImplicit false

private theorem sum_ofFn_eq
    {n : Nat} (f g : Fin n → Nat) (hfg : ∀ i, f i = g i) :
    (List.ofFn f).sum = (List.ofFn g).sum := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.ofFn_succ, List.sum_cons,
        List.ofFn_succ, List.sum_cons, hfg 0]
      exact congrArg (g 0 + ·)
        (ih (fun i => f i.succ) (fun i => g i.succ)
          (fun i => hfg i.succ))

private theorem sum_ofFn_le
    {n : Nat} (f g : Fin n → Nat) (hfg : ∀ i, f i ≤ g i) :
    (List.ofFn f).sum ≤ (List.ofFn g).sum := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.ofFn_succ, List.sum_cons,
        List.ofFn_succ, List.sum_cons]
      exact Nat.add_le_add (hfg 0)
        (ih (fun i => f i.succ) (fun i => g i.succ)
          (fun i => hfg i.succ))

private theorem sum_ofFn_add {n : Nat} (f g : Fin n → Nat) :
    (List.ofFn (fun i => f i + g i)).sum =
      (List.ofFn f).sum + (List.ofFn g).sum := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.ofFn_succ, List.sum_cons,
        List.ofFn_succ, List.sum_cons,
        List.ofFn_succ, List.sum_cons, ih]
      omega

private theorem sum_ofFn_mul_left {n : Nat} (a : Nat) (f : Fin n → Nat) :
    (List.ofFn (fun i => a * f i)).sum =
      a * (List.ofFn f).sum := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.ofFn_succ, List.sum_cons,
        List.ofFn_succ, List.sum_cons, ih, Nat.mul_add]

private theorem sum_ofFn_const (n c : Nat) :
    (List.ofFn (fun _ : Fin n => c)).sum = n * c := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.ofFn_succ, List.sum_cons, ih, Nat.succ_mul]
      exact Nat.add_comm _ _

/-- Freeze an inactive trial; otherwise execute the selected child. -/
def stoppedNext {S : Type} {n : Nat} (active : S → Bool)
    (next : S → Fin n → S) (s : S) (e : Fin n) : S :=
  if active s then next s e else s

/-- Sum of a natural-valued observable over the complete stopped scheduler
tree of the given depth. -/
def actionTreeTotal {S : Type} {n : Nat} (active : S → Bool)
    (next : S → Fin n → S) (value : S → Nat) : S → Nat → Nat
  | s, 0 => value s
  | s, t + 1 =>
      (List.ofFn (fun e => actionTreeTotal active next value
        (stoppedNext active next s e) t)).sum

/-- Number of exact scheduler words whose stopped endpoint remains active. -/
def liveTree {S : Type} {n : Nat} (active : S → Bool)
    (next : S → Fin n → S) : S → Nat → Nat
  | s, 0 => if active s then 1 else 0
  | s, t + 1 =>
      (List.ofFn (fun e => liveTree active next
        (stoppedNext active next s e) t)).sum

/-- Weighted finite survival sum.  At depth `t` this is
`sum_{j<t} n^(t-1-j) * liveTree s j`, without division. -/
def weightedLiveTotal {S : Type} {n : Nat} (active : S → Bool)
    (next : S → Fin n → S) (s : S) : Nat → Nat
  | 0 => 0
  | t + 1 => n * weightedLiveTotal active next s t +
      liveTree active next s t

theorem actionTreeTotal_succ_of_inactive
    {S : Type} {n : Nat} (active : S → Bool)
    (next : S → Fin n → S) (value : S → Nat)
    (s : S) (t : Nat) (hs : active s = false) :
    actionTreeTotal active next value s (t + 1) =
      n * actionTreeTotal active next value s t := by
  rw [actionTreeTotal]
  have hstop : ∀ e : Fin n, stoppedNext active next s e = s := by
    intro e
    simp [stoppedNext, hs]
  calc
    (List.ofFn (fun e => actionTreeTotal active next value
        (stoppedNext active next s e) t)).sum =
        (List.ofFn (fun _ : Fin n =>
          actionTreeTotal active next value s t)).sum := by
            apply sum_ofFn_eq
            intro e
            rw [hstop e]
    _ = n * actionTreeTotal active next value s t :=
      sum_ofFn_const n _

theorem liveTree_eq_zero_of_inactive
    {S : Type} {n : Nat} (active : S → Bool)
    (next : S → Fin n → S) (s : S)
    (hs : active s = false) :
    ∀ t, liveTree active next s t = 0 := by
  intro t
  induction t with
  | zero => simp [liveTree, hs]
  | succ t ih =>
      rw [liveTree]
      calc
        (List.ofFn (fun e => liveTree active next
            (stoppedNext active next s e) t)).sum =
            (List.ofFn (fun _ : Fin n =>
              liveTree active next s t)).sum := by
                apply sum_ofFn_eq
                intro e
                simp [stoppedNext, hs]
        _ = n * liveTree active next s t := sum_ofFn_const n _
        _ = 0 := by rw [ih, Nat.mul_zero]

/-- A uniform state bound lifts to the complete stopped action tree. -/
theorem actionTreeTotal_le
    {S : Type} {n B : Nat} (active : S → Bool)
    (next : S → Fin n → S) (value : S → Nat)
    (hbound : ∀ s, value s ≤ B) :
    ∀ s t, actionTreeTotal active next value s t ≤ n ^ t * B := by
  intro s t
  induction t generalizing s with
  | zero => simpa [actionTreeTotal] using hbound s
  | succ t ih =>
      rw [actionTreeTotal]
      calc
        (List.ofFn (fun e => actionTreeTotal active next value
            (stoppedNext active next s e) t)).sum ≤
            (List.ofFn (fun _ : Fin n => n ^ t * B)).sum := by
              apply sum_ofFn_le
              intro e
              exact ih (stoppedNext active next s e)
        _ = n * (n ^ t * B) := sum_ofFn_const n _
        _ = n ^ (t + 1) * B := by
          simp [Nat.pow_succ, Nat.mul_comm, Nat.mul_left_comm]

/-- Pointwise domination lifts through every stopped scheduler tree. -/
theorem actionTreeTotal_mono
    {S : Type} {n : Nat} (active : S → Bool)
    (next : S → Fin n → S) (value upper : S → Nat)
    (hle : ∀ s, value s ≤ upper s) :
    ∀ s t, actionTreeTotal active next value s t ≤
      actionTreeTotal active next upper s t := by
  intro s t
  induction t generalizing s with
  | zero => simpa [actionTreeTotal] using hle s
  | succ t ih =>
      simp only [actionTreeTotal]
      apply sum_ofFn_le
      intro e
      exact ih (stoppedNext active next s e)

/-- Scaling the leaf observable scales its complete action-tree sum. -/
theorem actionTreeTotal_mul_left
    {S : Type} {n : Nat} (active : S → Bool)
    (next : S → Fin n → S) (a : Nat) (value : S → Nat) :
    ∀ s t,
      actionTreeTotal active next (fun x => a * value x) s t =
        a * actionTreeTotal active next value s t := by
  intro s t
  induction t generalizing s with
  | zero => rfl
  | succ t ih =>
      simp only [actionTreeTotal]
      calc
        (List.ofFn (fun e => actionTreeTotal active next
            (fun x => a * value x) (stoppedNext active next s e) t)).sum =
            (List.ofFn (fun e => a * actionTreeTotal active next value
              (stoppedNext active next s e) t)).sum := by
                apply sum_ofFn_eq
                intro e
                exact ih (stoppedNext active next s e)
        _ = a * (List.ofFn (fun e => actionTreeTotal active next value
              (stoppedNext active next s e) t)).sum :=
          sum_ofFn_mul_left a _

/-- A one-step nonincreasing weight remains nonincreasing over every complete
stopped scheduler tree. -/
theorem actionTreeTotal_supermartingale
    {S : Type} {n : Nat} (active : S → Bool)
    (next : S → Fin n → S) (weight : S → Nat)
    (hstep : ∀ s,
      (List.ofFn (fun e => weight (stoppedNext active next s e))).sum ≤
        n * weight s) :
    ∀ s t, actionTreeTotal active next weight s t ≤ n ^ t * weight s := by
  intro s t
  induction t generalizing s with
  | zero => simp [actionTreeTotal]
  | succ t ih =>
      rw [actionTreeTotal]
      calc
        (List.ofFn (fun e => actionTreeTotal active next weight
            (stoppedNext active next s e) t)).sum ≤
            (List.ofFn (fun e => n ^ t *
              weight (stoppedNext active next s e))).sum := by
                apply sum_ofFn_le
                intro e
                exact ih (stoppedNext active next s e)
        _ = n ^ t * (List.ofFn (fun e =>
              weight (stoppedNext active next s e))).sum :=
          sum_ofFn_mul_left _ _
        _ ≤ n ^ t * (n * weight s) := Nat.mul_le_mul_left _ (hstep s)
        _ = n ^ (t + 1) * weight s := by
          rw [Nat.pow_succ]
          exact (Nat.mul_assoc (n ^ t) n (weight s)).symm

/-- Exact number of stopped scheduler words whose endpoint satisfies `bad`. -/
def badEndpointCount {S : Type} {n : Nat} (active bad : S → Bool)
    (next : S → Fin n → S) (s : S) (t : Nat) : Nat :=
  actionTreeTotal active next (fun x => if bad x then 1 else 0) s t

/-- A supermartingale weight that pays at least `W` on every bad endpoint gives
the division-free finite-horizon failure bound
`W * badCount <= n^t * weight(start)`. -/
theorem badEndpointCount_weight_bound
    {S : Type} {n W : Nat} (active bad : S → Bool)
    (next : S → Fin n → S) (weight : S → Nat)
    (hstep : ∀ s,
      (List.ofFn (fun e => weight (stoppedNext active next s e))).sum ≤
        n * weight s)
    (hbad : ∀ s, bad s = true → W ≤ weight s)
    (s : S) (t : Nat) :
    W * badEndpointCount active bad next s t ≤ n ^ t * weight s := by
  let indicator : S → Nat := fun x => if bad x then 1 else 0
  have hpay : ∀ x, W * indicator x ≤ weight x := by
    intro x
    cases hx : bad x
    · simp [indicator, hx]
    · simpa [indicator, hx] using hbad x hx
  have hmono := actionTreeTotal_mono active next
    (fun x => W * indicator x) weight hpay s t
  have hscale := actionTreeTotal_mul_left active next W indicator s t
  have hsuper := actionTreeTotal_supermartingale active next weight hstep s t
  unfold badEndpointCount
  change W * actionTreeTotal active next indicator s t ≤ n ^ t * weight s
  rw [← hscale]
  exact Nat.le_trans hmono hsuper

/-- A unit lower drift in the complete child sum charges every live prefix. -/
theorem actionTreeTotal_drift
    {S : Type} {n : Nat} (active : S → Bool)
    (next : S → Fin n → S) (value : S → Nat)
    (hdrift : ∀ s, active s = true →
      n * value s + 1 ≤ (List.ofFn (fun e => value (next s e))).sum) :
    ∀ s t,
      n * actionTreeTotal active next value s t +
          liveTree active next s t ≤
        actionTreeTotal active next value s (t + 1) := by
  intro s t
  induction t generalizing s with
  | zero =>
      cases hs : active s
      ·
        simp [actionTreeTotal, liveTree, stoppedNext, hs,
          sum_ofFn_const]
      · simpa [actionTreeTotal, liveTree, stoppedNext, hs] using hdrift s hs
  | succ t ih =>
      cases hs : active s
      · rw [liveTree_eq_zero_of_inactive active next s hs (t + 1),
          actionTreeTotal_succ_of_inactive active next value s (t + 1) hs]
        exact Nat.le_refl _
      · simp only [actionTreeTotal, liveTree]
        have hchildren := sum_ofFn_le
          (fun e => n * actionTreeTotal active next value
              (stoppedNext active next s e) t +
            liveTree active next (stoppedNext active next s e) t)
          (fun e => actionTreeTotal active next value
            (stoppedNext active next s e) (t + 1))
          (fun e => ih (stoppedNext active next s e))
        rw [sum_ofFn_add, sum_ofFn_mul_left] at hchildren
        exact hchildren

/-- The potential telescope charges the complete weighted survival sum. -/
theorem actionTree_telescope
    {S : Type} {n : Nat} (active : S → Bool)
    (next : S → Fin n → S) (value : S → Nat)
    (hdrift : ∀ s, active s = true →
      n * value s + 1 ≤ (List.ofFn (fun e => value (next s e))).sum)
    (s : S) (t : Nat) :
    n ^ t * value s + weightedLiveTotal active next s t ≤
      actionTreeTotal active next value s t := by
  induction t with
  | zero => simp [weightedLiveTotal, actionTreeTotal]
  | succ t ih =>
      have hscaled := Nat.mul_le_mul_left n ih
      have hstep := actionTreeTotal_drift active next value hdrift s t
      rw [weightedLiveTotal, Nat.pow_succ]
      calc
        n ^ t * n * value s +
            (n * weightedLiveTotal active next s t +
              liveTree active next s t) =
            n * (n ^ t * value s +
              weightedLiveTotal active next s t) +
              liveTree active next s t := by
                simp [Nat.mul_add, Nat.mul_comm,
                  Nat.mul_left_comm, Nat.add_assoc]
        _ ≤ n * actionTreeTotal active next value s t +
              liveTree active next s t :=
            Nat.add_le_add_right hscaled _
        _ ≤ actionTreeTotal active next value s (t + 1) := by
          exact hstep

/-- Division-free truncated-duration budget.  After normalization by `n^t`,
the weighted survival sum is at most `B - value s`. -/
theorem weightedLiveTotal_budget
    {S : Type} {n B : Nat} (active : S → Bool)
    (next : S → Fin n → S) (value : S → Nat)
    (hbound : ∀ s, value s ≤ B)
    (hdrift : ∀ s, active s = true →
      n * value s + 1 ≤ (List.ofFn (fun e => value (next s e))).sum)
    (s : S) (t : Nat) :
    n ^ t * value s + weightedLiveTotal active next s t ≤
      n ^ t * B := by
  exact Nat.le_trans (actionTree_telescope active next value hdrift s t)
    (actionTreeTotal_le active next value hbound s t)

/-- Survival counts grow by at most the `n` scheduler extensions of each live
prefix. -/
theorem liveTree_succ_le_mul
    {S : Type} {n : Nat} (active : S → Bool)
    (next : S → Fin n → S) (s : S) :
    ∀ t, liveTree active next s (t + 1) ≤
      n * liveTree active next s t := by
  intro t
  induction t generalizing s with
  | zero =>
      cases hs : active s
      · rw [liveTree_eq_zero_of_inactive active next s hs 0,
          liveTree_eq_zero_of_inactive active next s hs 1]
        simp
      · simp only [liveTree, stoppedNext, hs, if_true]
        have hchildren := sum_ofFn_le
          (fun e => if active (next s e) then 1 else 0)
          (fun _ : Fin n => 1) (by
            intro e
            split <;> simp)
        rw [sum_ofFn_const] at hchildren
        exact hchildren
  | succ t ih =>
      cases hs : active s
      · rw [liveTree_eq_zero_of_inactive active next s hs (t + 1),
          liveTree_eq_zero_of_inactive active next s hs (t + 2)]
        simp
      · simp only [liveTree, stoppedNext, hs, if_true]
        have hchildren := sum_ofFn_le
          (fun e => liveTree active next (next s e) (t + 1))
          (fun e => n * liveTree active next (next s e) t)
          (fun e => ih (next s e))
        rw [sum_ofFn_mul_left] at hchildren
        exact hchildren

/-- The depth-`t` live count occurs at least `t+1` times in the weighted
survival sum at depth `t+1`. -/
theorem liveTree_mul_time_le_weighted
    {S : Type} {n : Nat} (active : S → Bool)
    (next : S → Fin n → S) (s : S) (t : Nat) :
    (t + 1) * liveTree active next s t ≤
      weightedLiveTotal active next s (t + 1) := by
  induction t with
  | zero => simp [weightedLiveTotal]
  | succ t ih =>
      have hmono := liveTree_succ_le_mul active next s t
      have hmonoScaled := Nat.mul_le_mul_left (t + 1) hmono
      have hihScaled := Nat.mul_le_mul_left n ih
      rw [weightedLiveTotal]
      grind

/-- Finite-horizon tail budget obtained from bounded stopped drift. -/
theorem liveTree_tail_budget
    {S : Type} {n B : Nat} (active : S → Bool)
    (next : S → Fin n → S) (value : S → Nat)
    (hbound : ∀ s, value s ≤ B)
    (hdrift : ∀ s, active s = true →
      n * value s + 1 ≤ (List.ofFn (fun e => value (next s e))).sum)
    (s : S) (t : Nat) :
    n ^ (t + 1) * value s +
        (t + 1) * liveTree active next s t ≤
      n ^ (t + 1) * B := by
  have hlive := liveTree_mul_time_le_weighted active next s t
  have hbudget := weightedLiveTotal_budget active next value hbound hdrift
    s (t + 1)
  exact Nat.le_trans (Nat.add_le_add_left hlive _) hbudget

end PredictableTrialFiniteTree
