import Leader.L4.OpenQueue
import Leader.L4.Statement

/-!
# Predictable queue compensation under IID directed-edge marks

All currents are scaled by five. The denominator at a horizon of t marks
is n^t, so the finite-horizon statements use only exact integer arithmetic.
-/

namespace L4.BarrierIID

/-- All-edge sum for a function of the next mark, before that mark is drawn. -/
def edgeSum {n : Nat} (f : Fin n → Int) : Int := (List.ofFn f).sum

private theorem edgeSum_succ {n : Nat} (f : Fin (n+1) → Int) :
    edgeSum f = f 0 + edgeSum (fun i : Fin n => f i.succ) := by
  simp [edgeSum, List.ofFn_succ, List.sum_cons]

private theorem edgeSum_congr {n : Nat} (f g : Fin n → Int) (h : ∀ e, f e = g e) :
    edgeSum f = edgeSum g :=
  congrArg edgeSum (funext h)

private theorem edgeSum_zero (n : Nat) : edgeSum (fun _ : Fin n => 0) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [edgeSum_succ, ih]; rfl

private theorem edgeSum_add {n : Nat} (f g : Fin n → Int) :
    edgeSum (fun e => f e + g e) = edgeSum f + edgeSum g := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [edgeSum_succ, edgeSum_succ f, edgeSum_succ g, ih]
    omega

private theorem edgeSum_scale {n : Nat} (a : Int) (f : Fin n → Int) :
    edgeSum (fun e => a * f e) = a * edgeSum f := by
  induction n with
  | zero => simp [edgeSum]
  | succ n ih => rw [edgeSum_succ, edgeSum_succ f, ih, Int.mul_add]

private theorem edgeSum_mono {n : Nat} (f g : Fin n → Int) (h : ∀ e, f e ≤ g e) :
    edgeSum f ≤ edgeSum g := by
  induction n with
  | zero => exact Int.le_refl 0
  | succ n ih =>
    rw [edgeSum_succ f, edgeSum_succ g]
    exact Int.add_le_add (h 0) (ih _ _ (fun e => h e.succ))

private theorem edgeSum_sub {n : Nat} (f g : Fin n → Int) :
    edgeSum (fun e => f e - g e) = edgeSum f - edgeSum g := by
  have h := edgeSum_add (fun e => f e - g e) g
  have h' : edgeSum (fun e => (f e - g e) + g e) = edgeSum f :=
    edgeSum_congr _ _ (fun e => by omega)
  omega

/-- A nominated edge contributes its weight exactly once to the sum. -/
theorem edgeSum_selector {n : Nat} (i : Fin n) (a : Int) :
    edgeSum (fun e => if e = i then a else 0) = a := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · rw [edgeSum_succ]
      have h : edgeSum (fun e : Fin n => if e.succ = (0 : Fin (n+1)) then a else 0) = 0 :=
        (edgeSum_congr _ _ (fun e => if_neg (Fin.succ_ne_zero e))).trans (edgeSum_zero n)
      rw [h]
      simp
    · rw [edgeSum_succ]
      have h : edgeSum (fun e : Fin n => if e.succ = j.succ then a else 0)
          = edgeSum (fun e : Fin n => if e = j then a else 0) :=
        edgeSum_congr _ _ (fun e => by simp)
      rw [h, ih]
      rw [if_neg (Ne.symm (Fin.succ_ne_zero j)), Int.zero_add]

/-- The predictably chosen three queue bonds must be genuinely distinct. -/
structure QueueBonds (n : Nat) where
  inject : Fin n
  transfer : Fin n
  outlet : Fin n
  inject_ne_transfer : inject ≠ transfer
  inject_ne_outlet : inject ≠ outlet
  transfer_ne_outlet : transfer ≠ outlet

/-- Assign the three nominated queue actions to physical edge selections. -/
def QueueBonds.bond {n : Nat} (b : QueueBonds n) (e : Fin n) : OpenQueue.Bond :=
  if e = b.inject then .inject
  else if e = b.transfer then .transfer
  else if e = b.outlet then .outlet
  else .other

/-- The realized scaled queue current, zero outside a long tenure. -/
def queueMark {n : Nat} (active : Option (QueueBonds n × OpenQueue.StockPair))
    (e : Fin n) : Int :=
  match active with
  | none => 0
  | some (b,q) => OpenQueue.scaledIncrement q (b.bond e)

/-- Active conditional mean (2/(5n)), represented by its scaled numerator 2. -/
theorem queueMark_sum_active {n : Nat} (b : QueueBonds n) (q : OpenQueue.StockPair) :
    edgeSum (queueMark (some (b,q))) = 2 := by
  let pick := fun (i : Fin n) (a : Int) (e : Fin n) => if e = i then a else 0
  let a := OpenQueue.scaledIncrement q .inject
  let d := OpenQueue.scaledIncrement q .transfer
  let c := OpenQueue.scaledIncrement q .outlet
  calc
    edgeSum (queueMark (some (b,q))) =
        edgeSum (fun e => (pick b.inject a e + pick b.transfer d e) + pick b.outlet c e) := by
      apply edgeSum_congr
      intro e
      by_cases h₁ : e = b.inject
      · subst e
        simp [pick, queueMark, QueueBonds.bond, b.inject_ne_transfer, b.inject_ne_outlet, a]
      · by_cases h₂ : e = b.transfer
        · subst e
          simp [pick, queueMark, QueueBonds.bond, h₁, b.transfer_ne_outlet, d]
        · by_cases h₃ : e = b.outlet
          · subst e
            simp [pick, queueMark, QueueBonds.bond, h₁, h₂, c]
          · simp [pick, queueMark, QueueBonds.bond, h₁, h₂, h₃, OpenQueue.scaledIncrement_other]
    _ = a + d + c := by rw [edgeSum_add, edgeSum_add]; simp only [pick, edgeSum_selector]
    _ = 2 := OpenQueue.three_bond_sum q

/-- The scaled drift of the tagged front: five for the nominated outgoing
mark, less the compensated queue current. The outgoing edge need not be
disjoint from the three queue edges. -/
def driftMark {n : Nat} (out : Fin n)
    (active : Option (QueueBonds n × OpenQueue.StockPair)) (e : Fin n) : Int :=
  (if e = out then 5 else 0) - queueMark active e

/-- Exact predictable mean for the scaled drift: 3/n on a long tenure,
5/n otherwise. This equality is taken before seeing the next IID mark. -/
theorem driftMark_sum {n : Nat} (out : Fin n)
    (active : Option (QueueBonds n × OpenQueue.StockPair)) :
    edgeSum (driftMark out active) = if active.isSome then 3 else 5 := by
  unfold driftMark
  rw [edgeSum_sub, edgeSum_selector]
  cases active with
  | none => rw [show edgeSum (queueMark (none : Option (QueueBonds n × OpenQueue.StockPair))) = 0
      from edgeSum_zero n]
            change (5 : Int) - 0 = 5
            decide
  | some b =>
    rcases b with ⟨b,q⟩
    rw [queueMark_sum_active b q]
    change (5 : Int) - 2 = 3
    decide

/-- Summed compensation of an adapted, stopped process over all raw
length-t edge words. An augmented state may include the full prefix,
so selectors and STOP need only be predictable, not memoryless. -/
noncomputable def stoppedDriftNumerator {α : Type} {n : Nat}
    (next : α → Fin n → α) (stop : α → Prop) (inc : α → Fin n → Int) :
    Nat → α → Int
  | 0, _ => 0
  | t+1, x => by
      classical
      exact if stop x then 0 else
        (n : Int)^t * edgeSum (inc x) +
          edgeSum (fun e => stoppedDriftNumerator next stop inc t (next x e))

private theorem edgeSum_natCast {n : Nat} (a : Fin n → Nat) :
    edgeSum (fun e => (a e : Int)) = ((List.ofFn a).sum : Int) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [edgeSum_succ, List.ofFn_succ, List.sum_cons, ih]
    simp

/-- Generic finite-horizon optional-drift estimate. A uniform sum of at least
k at every live prefix yields at least k/n per truncated pre-stop step.
Both sides here are cleared of denominators. -/
theorem stoppedDrift_lower {α : Type} {n : Nat}
    (next : α → Fin n → α) (stop : α → Prop) (inc : α → Fin n → Int)
    (k : Int) (hlive : ∀ x, ¬ stop x → k ≤ edgeSum (inc x)) (t : Nat) (x : α) :
    k * (iidHitCost next stop t x : Int) ≤
      (n : Int) * stoppedDriftNumerator next stop inc t x := by
  classical
  induction t generalizing x with
  | zero => simp [iidHitCost, stoppedDriftNumerator]
  | succ t ih =>
    by_cases hs : stop x
    · simp [iidHitCost, stoppedDriftNumerator, hs]
    · simp only [iidHitCost, stoppedDriftNumerator, hs, if_false, Int.natCast_add, Int.natCast_pow]
      rw [← edgeSum_natCast, Int.mul_add, Int.mul_add]
      apply Int.add_le_add
      · rw [Int.pow_succ]
        have h := Int.mul_le_mul_of_nonneg_left (hlive x hs)
          (show 0 ≤ (n : Int)^t from Int.pow_nonneg (Int.natCast_nonneg n))
        have h' := Int.mul_le_mul_of_nonneg_left h (Int.natCast_nonneg n)
        simpa only [Int.mul_assoc, Int.mul_left_comm, Int.mul_comm] using h'
      · rw [← edgeSum_scale k (fun e => (iidHitCost next stop t (next x e) : Int)),
            ← edgeSum_scale (n : Int) (fun e => stoppedDriftNumerator next stop inc t (next x e))]
        exact edgeSum_mono _ _ (fun e => ih (next x e))

/-- Apply the optional-drift estimate to the minimum 3/n scaled
instantaneous drift of a live tagged front. -/
theorem stopped_tagged_drift_lower {α : Type} {n : Nat}
    (next : α → Fin n → α) (stop : α → Prop) (out : α → Fin n)
    (queue : α → Option (QueueBonds n × OpenQueue.StockPair)) (t : Nat) (x : α) :
    3 * (iidHitCost next stop t x : Int) ≤
      (n : Int) * stoppedDriftNumerator next stop (fun x => driftMark (out x) (queue x)) t x := by
  apply stoppedDrift_lower
  intro x _
  rw [driftMark_sum]
  cases queue x
  · change (3 : Int) ≤ 5; decide
  · change (3 : Int) ≤ 3; decide

private theorem edgeSum_const (n : Nat) (a : Int) :
    edgeSum (fun _ : Fin n => a) = (n : Int) * a := by
  induction n with
  | zero => simp [edgeSum]
  | succ n ih =>
    rw [edgeSum_succ, ih]
    simp [Int.natCast_succ, Int.add_mul, Int.add_comm]

/-- A nonnegative reserve which pays the current mark until stopping bounds
the finite-word stopped-drift numerator. The reserve need only exist on the
invariant of states reached before the first stopping mark and at its endpoint. -/
theorem stoppedDrift_upper_of_reserve {α : Type} {n : Nat}
    (next : α → Fin n → α) (stop : α → Prop) (inc : α → Fin n → Int)
    (good : α → Prop) (reserve : α → Int)
    (hnonneg : ∀ x, good x → 0 ≤ reserve x)
    (hgood : ∀ x e, good x → ¬ stop x → good (next x e))
    (hpay : ∀ x e, good x → ¬ stop x → inc x e + reserve (next x e) ≤ reserve x)
    (t : Nat) (x : α) (hx : good x) :
    stoppedDriftNumerator next stop inc t x ≤ (n : Int)^t * reserve x := by
  classical
  induction t generalizing x with
  | zero => simpa [stoppedDriftNumerator] using hnonneg x hx
  | succ t ih =>
    by_cases hs : stop x
    · simp only [stoppedDriftNumerator, hs, if_true]
      exact Int.mul_nonneg (Int.pow_nonneg (Int.natCast_nonneg n)) (hnonneg x hx)
    · let a := (n : Int)^t
      have ha : 0 ≤ a := Int.pow_nonneg (Int.natCast_nonneg n)
      have hsum := edgeSum_mono
        (fun e => a * inc x e + stoppedDriftNumerator next stop inc t (next x e))
        (fun _ => a * reserve x) (fun e => by
          calc
            _ ≤ a * inc x e + a * reserve (next x e) :=
              Int.add_le_add_left (ih _ (hgood x e hx hs)) _
            _ = a * (inc x e + reserve (next x e)) := (Int.mul_add ..).symm
            _ ≤ a * reserve x := Int.mul_le_mul_of_nonneg_left (hpay x e hx hs) ha)
      rw [edgeSum_add, edgeSum_scale, edgeSum_const] at hsum
      simpa [stoppedDriftNumerator, hs, a, Int.pow_succ, Int.mul_assoc, Int.mul_left_comm,
        Int.mul_comm] using hsum

/-- On every mark the compensated current is nonnegative, so the scaled
tagged drift overshoots its pre-mark value by at most five. -/
theorem driftMark_le_five {n : Nat} (out e : Fin n)
    (active : Option (QueueBonds n × OpenQueue.StockPair)) :
    driftMark out active e ≤ 5 := by
  have hinc (q : OpenQueue.StockPair) (bond : OpenQueue.Bond) :
      0 ≤ OpenQueue.scaledIncrement q bond := by
    rcases q with ⟨a,c⟩
    cases bond <;> cases a <;> cases c <;> decide
  have hq : 0 ≤ queueMark active e := by
    cases active with
    | none => exact Int.le_refl 0
    | some w =>
      rcases w with ⟨b,q⟩
      exact hinc q (b.bond e)
  unfold driftMark
  split <;> omega

/-- Conditional one-tag extinction bound from a pathwise live debt cap.
The predictable front and queue selectors are represented in state; the
state may carry the full history, including the accumulated scaled debt.
The final mark is included: its overshoot is at most 5 scaled units.
For fresh debt zero and cap 120*n, it suffices to choose a natural bound B
with 3*B ≥ n*(120*n+5). This proves no bound on the maximum over tags. -/
theorem singleTag_expected_of_live_debt {α : Type} {n : Nat} (_hn : 0 < n)
    (next : α → Fin n → α) (stop : α → Prop)
    (out : α → Fin n) (queue : α → Option (QueueBonds n × OpenQueue.StockPair))
    (reached : α → Prop) (debt : α → Int) (cap : Int)
    (hstep : ∀ x e, reached x → ¬ stop x → reached (next x e))
    (hliveCap : ∀ x, reached x → ¬ stop x → debt x ≤ cap)
    (hdebt : ∀ x e, reached x → ¬ stop x →
      debt (next x e) = debt x + driftMark (out x) (queue x) e)
    (x : α) (hx : reached x) (B : Nat)
    (hbudget : (n : Int) * (cap + 5 - debt x) ≤ 3 * (B : Int)) :
    IIDExpectedHittingTimeAtMost next stop x B := by
  intro t
  by_cases hs : stop x
  · rw [iidHitCost_of_target _ _ _ hs]
    omega
  · let good := fun y => reached y ∧ debt y ≤ cap + 5
    let reserve := fun y => cap + 5 - debt y
    let inc := fun y e => driftMark (out y) (queue y) e
    have hh : good x := ⟨hx, by have := hliveCap x hx hs; omega⟩
    have hupper := stoppedDrift_upper_of_reserve next stop inc good reserve
      (fun y hy => by have h := hy.2; change 0 ≤ cap + 5 - debt y; omega)
      (fun y e hy hstop => by
        refine ⟨hstep y e hy.1 hstop, ?_⟩
        rw [hdebt y e hy.1 hstop]
        have := hliveCap y hy.1 hstop
        have := driftMark_le_five (out y) e (queue y)
        omega)
      (fun y e hy hstop => by
        change inc y e + (cap + 5 - debt (next y e)) ≤ cap + 5 - debt y
        rw [hdebt y e hy.1 hstop]
        change inc y e + (cap + 5 - (debt y + inc y e)) ≤ _
        omega)
      t x hh
    have hpos : 0 ≤ (n : Int)^t := Int.pow_nonneg (Int.natCast_nonneg n)
    have hh := calc
      3 * (iidHitCost next stop t x : Int)
          ≤ (n : Int) * stoppedDriftNumerator next stop inc t x :=
            stopped_tagged_drift_lower next stop out queue t x
      _ ≤ (n : Int) * ((n : Int)^t * reserve x) :=
            Int.mul_le_mul_of_nonneg_left hupper (Int.natCast_nonneg n)
      _ = (n : Int)^t * ((n : Int) * (cap + 5 - debt x)) := by
            simp [reserve, Int.mul_left_comm]
      _ ≤ (n : Int)^t * (3 * (B : Int)) := Int.mul_le_mul_of_nonneg_left hbudget hpos
      _ = 3 * ((B * n^t : Nat) : Int) := by
            simp [Int.natCast_mul, Int.natCast_pow, Int.mul_assoc, Int.mul_comm]
    have hcast := Int.le_of_mul_le_mul_left hh (by decide : (0 : Int) < 3)
    exact_mod_cast hcast

end L4.BarrierIID

#print axioms L4.BarrierIID.queueMark_sum_active
#print axioms L4.BarrierIID.driftMark_sum
#print axioms L4.BarrierIID.stoppedDrift_lower
#print axioms L4.BarrierIID.stopped_tagged_drift_lower
#print axioms L4.BarrierIID.stoppedDrift_upper_of_reserve
#print axioms L4.BarrierIID.driftMark_le_five
#print axioms L4.BarrierIID.singleTag_expected_of_live_debt
