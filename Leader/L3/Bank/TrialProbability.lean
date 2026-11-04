import Leader.L3.Bank.TrialLocal

/-!
Local BANK trial probability.

The physical BANK
and observer transitions are not modified.

The watchdog arithmetic is proved below, independently of the
compiled-spatial-q wrapper already available as
Counter.resetColdWatchdogAll.

The full local win-mass upper estimate is left as a named Prop
until the CLEAN-start, all-word head-decision authentication and
recovery no-win obligations have been proved. The lower target
is also only a Prop. Neither is an axiom or a theorem.
-/

namespace L3

set_option autoImplicit false
set_option Elab.async false

/-- Numerator of 1024 times the C.4 watchdog error U_b.
The expression is deliberately cross-multiplied in Nat. -/
def bankTrialProbabilityBadNumerator (b : Nat) : Nat :=
  1024 * (2 ^ (b + 1) + 1) *
    2 ^ (2 * b + 2) * 4 ^ (11 * b + 24)

/-- Positive denominator of the C.4 watchdog error. -/
def bankTrialProbabilityBadDenominator (b : Nat) : Nat :=
  5 ^ (11 * b + 24)

/-- The paper's b=17 strict base inequality, checked as a
closed natural-number inequality rather than by division. -/
private theorem bankTrialProbabilityBadBase :
    bankTrialProbabilityBadNumerator 17 <
      bankTrialProbabilityBadDenominator 17 := by
  have hbase :
      1024 * (2 ^ 18 + 1) * 2 ^ 36 * 4 ^ 211 + 1 ≤
        5 ^ 211 := Nat.le_of_ble_eq_true rfl
  change 1024 * (2 ^ 18 + 1) * 2 ^ 36 * 4 ^ 211 <
    5 ^ 211
  omega

/-- The constant strict contraction for the ratio:
8 * (4/5)^11 < 1. This is a small closed check. -/
private theorem bankTrialProbabilityRatioConstant :
    8 * 4 ^ 11 < 5 ^ 11 := by
  have hsmall : 8 * 4 ^ 11 + 1 ≤ 5 ^ 11 :=
    Nat.le_of_ble_eq_true rfl
  omega

/-- The strict ratio in C.4, before cross-multiplying
the old numerator and denominator. -/
private theorem bankTrialProbabilityRatio (b : Nat) :
    4 * (2 ^ (b + 2) + 1) * 4 ^ 11 <
      (2 ^ (b + 1) + 1) * 5 ^ 11 := by
  have hpow :
      2 ^ (b + 2) = 2 * 2 ^ (b + 1) := by
    rw [show b + 2 = (b + 1) + 1 by omega, Nat.pow_succ]
    ac_rfl
  have hcoef :
      4 * (2 ^ (b + 2) + 1) ≤
        8 * (2 ^ (b + 1) + 1) := by
    rw [hpow]
    omega
  have hpositive : 0 < 2 ^ (b + 1) + 1 := by omega
  calc
    4 * (2 ^ (b + 2) + 1) * 4 ^ 11 ≤
        (8 * (2 ^ (b + 1) + 1)) * 4 ^ 11 :=
      Nat.mul_le_mul_right (4 ^ 11) hcoef
    _ = (8 * 4 ^ 11) * (2 ^ (b + 1) + 1) := by
      ac_rfl
    _ < 5 ^ 11 * (2 ^ (b + 1) + 1) :=
      Nat.mul_lt_mul_of_pos_right
        bankTrialProbabilityRatioConstant hpositive
    _ = (2 ^ (b + 1) + 1) * 5 ^ 11 := by
      ac_rfl

/-- One induction step using the 4 * 4^11 multiplier on
the old 2^(2b+2) and 4^(11b+24) factors. -/
private theorem bankTrialProbabilityBadStep (b : Nat)
    (hb : bankTrialProbabilityBadNumerator b <
      bankTrialProbabilityBadDenominator b) :
    bankTrialProbabilityBadNumerator (b + 1) <
      bankTrialProbabilityBadDenominator (b + 1) := by
  have htwo :
      2 ^ (2 * (b + 1) + 2) =
        2 ^ (2 * b + 2) * 4 := by
    rw [show 2 * (b + 1) + 2 = (2 * b + 2) + 2 by omega,
      Nat.pow_add]
  have hfour :
      4 ^ (11 * (b + 1) + 24) =
        4 ^ (11 * b + 24) * 4 ^ 11 := by
    rw [show 11 * (b + 1) + 24 =
      (11 * b + 24) + 11 by omega, Nat.pow_add]
  have hfive :
      5 ^ (11 * (b + 1) + 24) =
        5 ^ (11 * b + 24) * 5 ^ 11 := by
    rw [show 11 * (b + 1) + 24 =
      (11 * b + 24) + 11 by omega, Nat.pow_add]
  calc
    bankTrialProbabilityBadNumerator (b + 1) =
        (1024 * 2 ^ (2 * b + 2) * 4 ^ (11 * b + 24)) *
          (4 * (2 ^ (b + 2) + 1) * 4 ^ 11) := by
      unfold bankTrialProbabilityBadNumerator
      rw [htwo, hfour]
      ac_rfl
    _ ≤ (1024 * 2 ^ (2 * b + 2) * 4 ^ (11 * b + 24)) *
          ((2 ^ (b + 1) + 1) * 5 ^ 11) :=
      Nat.mul_le_mul_left _
        (Nat.le_of_lt (bankTrialProbabilityRatio b))
    _ = bankTrialProbabilityBadNumerator b * 5 ^ 11 := by
      unfold bankTrialProbabilityBadNumerator
      ac_rfl
    _ < bankTrialProbabilityBadDenominator b * 5 ^ 11 :=
      Nat.mul_lt_mul_of_pos_right hb
        (Nat.pow_pos (by omega))
    _ = bankTrialProbabilityBadDenominator (b + 1) := by
      unfold bankTrialProbabilityBadDenominator
      rw [hfive]

/-- Paper C.4--C.5: U_b < 1/1024 for every b >= 17,
with no division or subtraction of unsigned expressions. -/
theorem bankTrialProbabilityBadAll (b : Nat) (hb : 17 ≤ b) :
    bankTrialProbabilityBadNumerator b <
      bankTrialProbabilityBadDenominator b := by
  obtain ⟨k, hk⟩ : ∃ k : Nat, b = 17 + k :=
    ⟨b - 17, by omega⟩
  subst hk
  clear hb
  induction k with
  | zero =>
      exact bankTrialProbabilityBadBase
  | succ k ih =>
      have hstep := bankTrialProbabilityBadStep (17 + k) ih
      simpa only [Nat.add_succ] using hstep

/-- The requested explicit cross-multiplied Nat inequality. -/
theorem bankTrialProbabilityWatchdogTiny (b : Nat)
    (hb : 17 ≤ b) :
    1024 * (2 ^ (b + 1) + 1) *
        2 ^ (2 * b + 2) * 4 ^ (11 * b + 24) <
      5 ^ (11 * b + 24) := by
  exact bankTrialProbabilityBadAll b hb

/-- The finite-horizon numerator of the local observer's
absorbing WON event over the original n-edge scheduler.
It is NOT an independent two-edge scheduler. -/
noncomputable def bankTrialProbabilityWinMass {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (T : Nat) : Nat :=
  Prob.scheduleSum n T (fun w =>
    if (bankTrialLocalRun ring root w
        (bankTrialLocalStart S)).phase = .won then 1 else 0)

/-- UNPROVED TARGET, not an axiom or theorem.
Paper C.4 upper bound: every CLEAN-start observer win must
be certified by K successive outgoing ARMED HEAD decisions.
The missing local proof must authenticate all reachable LIVE
worker returns and exclude a recovery-mode OLD success that
does not belong to those K decisions. -/
def BankTrialProbabilityUpperTarget {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b) : Prop :=
  (compileAdvice q).useSmall = false →
  2 * (compileAdvice q).bankLeaseCap ≤ n →
  BankTrialLocalClean q S →
  ∀ T : Nat,
    2 ^ (compileAdvice q).K *
      bankTrialProbabilityWinMass ring root S T ≤ n ^ T

/-- UNPROVED TARGET, not an axiom or theorem.
Paper C.5 lower probability with theta = 1023/1024.
It is expressed as EXISTENCE of a finite horizon, not as a
positive lower bound at every T (which fails at T=0).

Needed input: a uniform adapted worker watchdog at actual
postservice RESET/IWAIT/CWAIT origins, at most 2K+1 origins,
and the authenticated all-K-head -> genuine CL1 success
bridge on the same edge tape, including the CWAIT return
and the recovery-to-Clean stopping semantics.
The arithmetic theorem above supplies only U_b < 1/1024. -/
def BankTrialProbabilityThetaLowerTarget {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b) : Prop :=
  (compileAdvice q).useSmall = false →
  2 * (compileAdvice q).bankLeaseCap ≤ n →
  (compileAdvice q).K < 2 ^ (compileAdvice q).b →
  BankTrialLocalClean q S →
  ∃ T : Nat,
    1023 * n ^ T ≤
      1024 * 2 ^ (compileAdvice q).K *
        bankTrialProbabilityWinMass ring root S T

end L3

namespace L3

open Classical
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

set_option autoImplicit false
set_option Elab.async false

/-!
Adapted ARMED-gate counting, recovery continuation mass,
and a CLEAN-reachable obstruction to the ungated SMALL recursion.
The LIVE winning-word authentication is not asserted.
-/

private theorem bankTrialProbabilitySumFlatMap {A B : Type}
    (xs : List A) (ys : A → List B) (f : B → Nat) :
    ((xs.flatMap ys).map f).sum =
      (xs.map (fun x => ((ys x).map f).sum)).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [ih]

private theorem bankTrialProbabilitySumSwap {A : Type} {n : Nat}
    (xs : List A) (f : A → Fin n → Nat) :
    (xs.map (fun x => (List.ofFn (f x)).sum)).sum =
      (List.ofFn (fun e => (xs.map (fun x => f x e)).sum)).sum := by
  induction xs with
  | nil => simp [ofFn_sum_const]
  | cons x xs ih =>
      simp only [List.map_cons, List.sum_cons, ih]
      rw [ofFn_sum_add]

/-- The empty original-clock word. -/
theorem bankTrialProbabilityScheduleSumZero (n : Nat)
    (f : List (Fin n) → Nat) :
    Prob.scheduleSum n 0 f = f [] := by
  change ((allSchedules n 0).map (fun u => f u.reverse)).sum = f []
  rfl

/-- First-letter decomposition, with the scheduleSum reversal
accounted for rather than silently changing the tape convention. -/
theorem bankTrialProbabilityScheduleSumFirst (n T : Nat)
    (f : List (Fin n) → Nat) :
    Prob.scheduleSum n (T + 1) f =
      (List.ofFn (fun e : Fin n =>
        Prob.scheduleSum n T (fun w => f (e :: w)))).sum := by
  change ((allSchedules n (T + 1)).map
      (fun u => f u.reverse)).sum =
    (List.ofFn (fun e : Fin n =>
      ((allSchedules n T).map
        (fun u => f (e :: u.reverse))).sum)).sum
  simp only [allSchedules, bankTrialProbabilitySumFlatMap,
    List.map_ofFn, Function.comp_def, List.reverse_append,
    List.reverse_cons, List.reverse_nil, List.nil_append,
    List.singleton_append]
  exact bankTrialProbabilitySumSwap _ _

theorem bankTrialProbabilityScheduleSumConst (n T c : Nat) :
    Prob.scheduleSum n T (fun _ => c) = n ^ T * c := by
  induction T with
  | zero =>
      rw [bankTrialProbabilityScheduleSumZero]
      simp
  | succ T ih =>
      rw [bankTrialProbabilityScheduleSumFirst]
      change (List.ofFn (fun _ : Fin n =>
          Prob.scheduleSum n T (fun _ => c))).sum =
        n ^ (T + 1) * c
      rw [ofFn_sum_const, ih, Nat.pow_succ]
      ac_rfl

theorem bankTrialProbabilityScheduleSumMono (n T : Nat) :
    ∀ (f g : List (Fin n) → Nat),
      (∀ w, f w ≤ g w) →
      Prob.scheduleSum n T f ≤ Prob.scheduleSum n T g := by
  induction T with
  | zero =>
      intro f g h
      rw [bankTrialProbabilityScheduleSumZero,
        bankTrialProbabilityScheduleSumZero]
      exact h []
  | succ T ih =>
      intro f g h
      rw [bankTrialProbabilityScheduleSumFirst,
        bankTrialProbabilityScheduleSumFirst]
      exact ofFn_sum_le _ _
        (fun e => ih _ _ (fun w => h (e :: w)))

private theorem bankTrialProbabilityRightAfterLeft {n : Nat}
    (ring : DirectedRing n) (i : Fin n) :
    ring.rightNeighbor (ring.leftNeighbor i) = i := by
  apply Fin.ext
  change (((i.val + n - 1) % n + 1) % n) = i.val
  rw [Nat.mod_add_mod]
  have heq : i.val + n - 1 + 1 = i.val + n := by omega
  rw [heq, Nat.add_mod]
  simp [Nat.mod_eq_of_lt i.isLt]

private theorem bankTrialProbabilityLeftAfterRight {n : Nat}
    (ring : DirectedRing n) (i : Fin n) :
    ring.leftNeighbor (ring.rightNeighbor i) = i := by
  apply Fin.ext
  change (((i.val + 1) % n + n - 1) % n) = i.val
  have heq :
      (i.val + 1) % n + n - 1 =
        (i.val + 1) % n + (n - 1) := by
    have hn := ring.hn
    omega
  rw [heq, Nat.mod_add_mod]
  have heq' : i.val + 1 + (n - 1) = i.val + n := by
    have hn := ring.hn
    omega
  rw [heq', Nat.add_mod]
  simp [Nat.mod_eq_of_lt i.isLt]

private theorem bankTrialProbabilityIncomingIffLeft {n : Nat}
    (ring : DirectedRing n) (root e : Fin n) :
    ring.rightNeighbor e = root ↔ e = ring.leftNeighbor root := by
  constructor
  · intro h
    calc
      e = ring.leftNeighbor (ring.rightNeighbor e) :=
        (bankTrialProbabilityLeftAfterRight ring e).symm
      _ = ring.leftNeighbor root := congrArg ring.leftNeighbor h
  · intro h
    rw [h]
    exact bankTrialProbabilityRightAfterLeft ring root

private theorem bankTrialProbabilityPortsDistinct {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n) (root : Fin n) :
    root ≠ ring.leftNeighbor root := by
  have h := Counter.resetRootPortDistinct
    ring (ring.leftNeighbor root) hn
  rw [bankTrialProbabilityRightAfterLeft] at h
  exact h

private theorem bankTrialProbabilitySumSwapSingle :
    ∀ {m : Nat} (f g : Fin m → Nat) (i : Fin m),
      (∀ j, j ≠ i → f j = g j) →
      (List.ofFn f).sum + g i =
        (List.ofFn g).sum + f i := by
  intro m
  induction m with
  | zero =>
      intro f g i h
      exact Fin.elim0 i
  | succ m ih =>
      intro f g i h
      rw [List.ofFn_succ, List.sum_cons,
        List.ofFn_succ, List.sum_cons]
      by_cases hi : i = 0
      · subst i
        have ht :
            (List.ofFn (fun j : Fin m => f j.succ)).sum =
              (List.ofFn (fun j : Fin m => g j.succ)).sum := by
          apply ofFn_sum_eq
          intro j
          apply h
          intro hz
          have hv := congrArg Fin.val hz
          change j.val + 1 = 0 at hv
          omega
        rw [ht]
        omega
      · have hiZero : i.val ≠ 0 := by
          intro hz
          exact hi (Fin.ext hz)
        obtain ⟨j, hjv⟩ :
            ∃ j : Fin m, j.val = i.val - 1 :=
          ⟨⟨i.val - 1, by omega⟩, rfl⟩
        have hj : j.succ = i := by
          apply Fin.ext
          change j.val + 1 = i.val
          rw [hjv]
          omega
        have hmatch : ∀ a : Fin m, a ≠ j →
            f a.succ = g a.succ := by
          intro a ha
          apply h
          intro hz
          apply ha
          apply Fin.ext
          have hv := congrArg Fin.val hz
          have hv' := congrArg Fin.val hj
          change a.val + 1 = i.val at hv
          change j.val + 1 = i.val at hv'
          omega
        have ht := ih
          (fun a : Fin m => f a.succ)
          (fun a : Fin m => g a.succ) j hmatch
        have hzero := h 0 (Ne.symm hi)
        simp only [hj] at ht
        omega

/-- The compensating zero incoming branch is indispensable:
2C + 0 + (n-2)C = nC. -/
private theorem bankTrialProbabilityTwoPortSum {n : Nat}
    (a b : Fin n) (hab : a ≠ b) (C : Nat) :
    (List.ofFn (fun e : Fin n =>
      if e = a then 2 * C else if e = b then 0 else C)).sum =
        n * C := by
  have hfirst := bankTrialProbabilitySumSwapSingle
    (fun _ : Fin n => C)
    (fun e : Fin n => if e = a then 2 * C else C) a
    (by intro e he; simp [he])
  have hsecond := bankTrialProbabilitySumSwapSingle
    (fun e : Fin n => if e = a then 2 * C else C)
    (fun e : Fin n =>
      if e = a then 2 * C else if e = b then 0 else C) b
    (by intro e he; by_cases ha : e = a <;> simp [ha, he])
  have hba : b ≠ a := Ne.symm hab
  have hfirst' :
      (List.ofFn (fun _ : Fin n => C)).sum + 2 * C =
        (List.ofFn (fun e : Fin n =>
          if e = a then 2 * C else C)).sum + C := by
    simpa only [if_pos rfl, if_true, ↓reduceIte] using hfirst
  have hsecond' :
      (List.ofFn (fun e : Fin n =>
        if e = a then 2 * C else C)).sum =
        (List.ofFn (fun e : Fin n =>
          if e = a then 2 * C else if e = b then 0 else C)).sum + C := by
    simpa [hba] using hsecond
  have hconstant :
      (List.ofFn (fun _ : Fin n => C)).sum = n * C :=
    ofFn_sum_const n C
  rw [hconstant] at hfirst'
  omega

/-- The gate is evaluated at the actual OLD observer state. -/
def BankTrialProbabilityArmedGate {q : Nat}
    (z : BankTrialLocalState q) : Prop :=
  (∃ begun : Bool, z.phase = .live begun) ∧
    (z.bank.fields ⟨0, by omega⟩).1 = .ARMED

/-- An adapted k-head event. At a closed gate all letters retain
k, but still update the actual observer state. At an open gate,
outgoing consumes one decision and incoming fails the event.
Reaching k=0 succeeds regardless of later letters. -/
noncomputable def bankTrialProbabilityHeadEvent {n q : Nat}
    (ring : DirectedRing n) (root : Fin n) :
    List (Fin n) → Nat → BankTrialLocalState q → Prop
  | [], k, _ => k = 0
  | _ :: _, 0, _ => True
  | e :: w, k + 1, z =>
      if BankTrialProbabilityArmedGate z then
        if e = root then
          bankTrialProbabilityHeadEvent ring root w k
            (bankTrialLocalNext ring root z e)
        else if ring.rightNeighbor e = root then False
        else
          bankTrialProbabilityHeadEvent ring root w (k + 1)
            (bankTrialLocalNext ring root z e)
      else
        bankTrialProbabilityHeadEvent ring root w (k + 1)
          (bankTrialLocalNext ring root z e)

/-- The gated event mass is not defined to be the observer win
mass. Their containment requires LIVE head authentication. -/
noncomputable def bankTrialProbabilityHeadMass {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (z : BankTrialLocalState q) (k T : Nat) : Nat :=
  Prob.scheduleSum n T (fun w =>
    if bankTrialProbabilityHeadEvent ring root w k z then 1 else 0)

theorem bankTrialProbabilityHeadMassZero {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (z : BankTrialLocalState q) (T : Nat) :
    bankTrialProbabilityHeadMass ring root z 0 T = n ^ T := by
  have hw : (fun w : List (Fin n) =>
      if bankTrialProbabilityHeadEvent ring root w 0 z
      then 1 else 0) = (fun _ => 1) := by
    funext w
    cases w <;> simp [bankTrialProbabilityHeadEvent]
  unfold bankTrialProbabilityHeadMass
  rw [hw]
  simpa only [Nat.mul_one] using
    bankTrialProbabilityScheduleSumConst n T 1

/-- Exact first-letter recursion. In particular the busy-state
branch is NOT the SMALL incoming-zero branch. -/
theorem bankTrialProbabilityHeadMassSucc {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (z : BankTrialLocalState q) (k T : Nat) :
    bankTrialProbabilityHeadMass ring root z (k + 1) (T + 1) =
      (List.ofFn (fun e : Fin n =>
        if BankTrialProbabilityArmedGate z then
          if e = root then
            bankTrialProbabilityHeadMass ring root
              (bankTrialLocalNext ring root z e) k T
          else if ring.rightNeighbor e = root then 0
          else
            bankTrialProbabilityHeadMass ring root
              (bankTrialLocalNext ring root z e) (k + 1) T
        else
          bankTrialProbabilityHeadMass ring root
            (bankTrialLocalNext ring root z e) (k + 1) T)).sum := by
  unfold bankTrialProbabilityHeadMass
  rw [bankTrialProbabilityScheduleSumFirst]
  apply ofFn_sum_eq
  intro e
  by_cases hg : BankTrialProbabilityArmedGate z
  · by_cases he : e = root
    · simp [bankTrialProbabilityHeadEvent, hg, he]
    · by_cases hi : ring.rightNeighbor e = root
      · have hz :
            Prob.scheduleSum n T (fun _ : List (Fin n) => 0) = 0 := by
          rw [bankTrialProbabilityScheduleSumConst]
          exact Nat.mul_zero _
        simpa [bankTrialProbabilityHeadEvent, hg, he, hi] using hz
      · simp [bankTrialProbabilityHeadEvent, hg, he, hi]
  · simp [bankTrialProbabilityHeadEvent, hg]

/-- Original-clock bound, uniformly over ALL observer states and
all budgets. This theorem concerns the gated event, not yet WON. -/
theorem bankTrialProbabilityHeadMassBound {n q : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n) (root : Fin n) :
    ∀ (T k : Nat) (z : BankTrialLocalState q),
      2 ^ k * bankTrialProbabilityHeadMass ring root z k T ≤
        n ^ T := by
  intro T
  induction T with
  | zero =>
      intro k z
      cases k with
      | zero =>
          rw [bankTrialProbabilityHeadMassZero]
          simp
      | succ k =>
          have hz :
              bankTrialProbabilityHeadMass ring root z (k + 1) 0 =
                0 := by
            unfold bankTrialProbabilityHeadMass
            rw [bankTrialProbabilityScheduleSumZero]
            simp [bankTrialProbabilityHeadEvent]
          rw [hz]
          simp
  | succ T ih =>
      intro k z
      cases k with
      | zero =>
          rw [bankTrialProbabilityHeadMassZero]
          simp
      | succ k =>
          by_cases hg : BankTrialProbabilityArmedGate z
          · have hpair : ∀ e : Fin n,
                2 ^ (k + 1) *
                  (if e = root then
                    bankTrialProbabilityHeadMass ring root
                      (bankTrialLocalNext ring root z e) k T
                   else if ring.rightNeighbor e = root then 0
                   else
                    bankTrialProbabilityHeadMass ring root
                      (bankTrialLocalNext ring root z e) (k + 1) T) ≤
                (if e = root then 2 * n ^ T
                 else if e = ring.leftNeighbor root then 0
                 else n ^ T) := by
              intro e
              by_cases he : e = root
              · simp only [if_pos he]
                calc
                  2 ^ (k + 1) *
                      bankTrialProbabilityHeadMass ring root
                        (bankTrialLocalNext ring root z e) k T =
                      2 * (2 ^ k *
                        bankTrialProbabilityHeadMass ring root
                          (bankTrialLocalNext ring root z e) k T) := by
                    rw [Nat.pow_succ]
                    ac_rfl
                  _ ≤ 2 * n ^ T := Nat.mul_le_mul_left 2
                    (ih k (bankTrialLocalNext ring root z e))
              · by_cases hl : e = ring.leftNeighbor root
                · have hi : ring.rightNeighbor e = root :=
                    (bankTrialProbabilityIncomingIffLeft
                      ring root e).mpr hl
                  have hleftNe : ring.leftNeighbor root ≠ root :=
                    Ne.symm (bankTrialProbabilityPortsDistinct ring hn root)
                  have hleftIncoming :
                      ring.rightNeighbor (ring.leftNeighbor root) = root :=
                    bankTrialProbabilityRightAfterLeft ring root
                  rw [hl]
                  simp only [if_neg hleftNe, if_pos hleftIncoming,
                    if_pos rfl, Nat.mul_zero, Nat.zero_le]
                · have hi : ring.rightNeighbor e ≠ root := by
                    intro h
                    exact hl
                      ((bankTrialProbabilityIncomingIffLeft
                        ring root e).mp h)
                  simpa [he, hi, hl] using
                    ih (k + 1) (bankTrialLocalNext ring root z e)
            calc
              2 ^ (k + 1) *
                  bankTrialProbabilityHeadMass ring root z
                    (k + 1) (T + 1) =
                  (List.ofFn (fun e : Fin n =>
                    2 ^ (k + 1) *
                      (if e = root then
                        bankTrialProbabilityHeadMass ring root
                          (bankTrialLocalNext ring root z e) k T
                       else if ring.rightNeighbor e = root then 0
                       else
                        bankTrialProbabilityHeadMass ring root
                          (bankTrialLocalNext ring root z e)
                          (k + 1) T))).sum := by
                rw [bankTrialProbabilityHeadMassSucc]
                simp only [if_pos hg]
                exact (ofFn_sum_mul_left (2 ^ (k + 1)) _).symm
              _ ≤ (List.ofFn (fun e : Fin n =>
                    if e = root then 2 * n ^ T
                    else if e = ring.leftNeighbor root then 0
                    else n ^ T)).sum := ofFn_sum_le _ _ hpair
              _ = n * n ^ T := bankTrialProbabilityTwoPortSum
                root (ring.leftNeighbor root)
                (bankTrialProbabilityPortsDistinct ring hn root)
                (n ^ T)
              _ = n ^ (T + 1) := by
                rw [Nat.pow_succ]
                exact Nat.mul_comm n (n ^ T)
          · calc
              2 ^ (k + 1) *
                  bankTrialProbabilityHeadMass ring root z
                    (k + 1) (T + 1) =
                  (List.ofFn (fun e : Fin n =>
                    2 ^ (k + 1) *
                      bankTrialProbabilityHeadMass ring root
                        (bankTrialLocalNext ring root z e)
                        (k + 1) T)).sum := by
                rw [bankTrialProbabilityHeadMassSucc]
                simp only [if_neg hg]
                exact (ofFn_sum_mul_left (2 ^ (k + 1)) _).symm
              _ ≤ (List.ofFn (fun _ : Fin n => n ^ T)).sum :=
                ofFn_sum_le _ _
                  (fun e => ih (k + 1) (bankTrialLocalNext ring root z e))
              _ = n * n ^ T := ofFn_sum_const n (n ^ T)
              _ = n ^ (T + 1) := by
                rw [Nat.pow_succ]
                exact Nat.mul_comm n (n ^ T)

/-- Conditional transfer only. The premise is a deterministic
winning-word authentication, not a probability estimate. No proof
of this premise for all CLEAN-start LIVE words is supplied here. -/
theorem bankTrialProbabilityUpperOfHeadAuthentication {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hauth : (compileAdvice q).useSmall = false →
      2 * (compileAdvice q).bankLeaseCap ≤ n →
      BankTrialLocalClean q S →
      ∀ w : List (Fin n),
        (bankTrialLocalRun ring root w
          (bankTrialLocalStart S)).phase = .won →
        bankTrialProbabilityHeadEvent ring root w
          (compileAdvice q).K (bankTrialLocalStart S)) :
    BankTrialProbabilityUpperTarget ring root S := by
  intro hsp hlarge hclean T
  have hcap : 1 ≤ (compileAdvice q).bankLeaseCap := by
    change 1 ≤ 13 * ((compileAdvice q).b + 2)
    omega
  have hn : 2 ≤ n := by omega
  have hmass : bankTrialProbabilityWinMass ring root S T ≤
      bankTrialProbabilityHeadMass ring root
        (bankTrialLocalStart S) (compileAdvice q).K T := by
    unfold bankTrialProbabilityWinMass bankTrialProbabilityHeadMass
    apply bankTrialProbabilityScheduleSumMono n T
    intro w
    by_cases hw : (bankTrialLocalRun ring root w
        (bankTrialLocalStart S)).phase = .won
    · have hh := hauth hsp hlarge hclean w hw
      simp [hw, hh]
    · simp [hw]
  exact Nat.le_trans
    (Nat.mul_le_mul_left (2 ^ (compileAdvice q).K) hmass)
    (bankTrialProbabilityHeadMassBound ring hn root
      T (compileAdvice q).K (bankTrialLocalStart S))

/-- Actual WON mass from an arbitrary observer cut, distinct from
the adapted head-event mass. -/
noncomputable def bankTrialProbabilityStateWinMass {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (z : BankTrialLocalState q) (T : Nat) : Nat :=
  Prob.scheduleSum n T (fun w =>
    if (bankTrialLocalRun ring root w z).phase = .won then 1 else 0)

/-- Unconditional first-letter recursion for the actual observer. -/
theorem bankTrialProbabilityStateWinMassFirst {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (z : BankTrialLocalState q) (T : Nat) :
    bankTrialProbabilityStateWinMass ring root z (T + 1) =
      (List.ofFn (fun e : Fin n =>
        bankTrialProbabilityStateWinMass ring root
          (bankTrialLocalNext ring root z e) T)).sum := by
  unfold bankTrialProbabilityStateWinMass
  rw [bankTrialProbabilityScheduleSumFirst]
  rfl

/-- RecoveryNoWin iterated over an arbitrary continuation. A
CLEAN exit is LOST and absorbing; otherwise the reachable RECOVERY
witness is extended by the current letter. -/
theorem bankTrialProbabilityRecoverySuffixNotWon {n q : Nat}
    (ring : DirectedRing n) (root : Fin n) (hn : 2 ≤ n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S) :
    ∀ (v pre : List (Fin n))
      (B : GrantBankReference.BankLocalReference
        (compileAdvice q).b),
      bankTrialLocalRun ring root pre (bankTrialLocalStart S) =
        ⟨B, .recovery⟩ →
      (bankTrialLocalRun ring root v
        (⟨B, .recovery⟩ : BankTrialLocalState q)).phase ≠ .won := by
  intro v
  induction v with
  | nil =>
      intro pre B hrun hwon
      cases hwon
  | cons e es ih =>
      intro pre B hrun
      have hf := bankTrialLocalRecoveryNoWin
        ring root hn S hclean pre B hrun e
      by_cases hc : BankTrialLocalClean q
          (GrantBankReference.bankLocalReferenceStepClamped
            ring root B e)
      · have he := bankTrialLocalRecoveryCleanLoss ring root e B hc
        have ht : bankTrialLocalTerminal
            (⟨GrantBankReference.bankLocalReferenceStepClamped
              ring root B e, .lost⟩ : BankTrialLocalState q) :=
          Or.inr rfl
        change (bankTrialLocalRun ring root es
          (bankTrialLocalNext ring root
            (⟨B, .recovery⟩ : BankTrialLocalState q) e)).phase ≠ .won
        rw [he, bankTrialLocalRunTerminalAbsorbs ring root es _ ht]
        intro hwon
        cases hwon
      · have he : bankTrialLocalNext ring root
            (⟨B, .recovery⟩ : BankTrialLocalState q) e =
            ⟨GrantBankReference.bankLocalReferenceStepClamped
              ring root B e, .recovery⟩ := by
          simp [bankTrialLocalNext, hf, hc]
        have hlong : bankTrialLocalRun ring root
            (pre ++ [e]) (bankTrialLocalStart S) =
            ⟨GrantBankReference.bankLocalReferenceStepClamped
              ring root B e, .recovery⟩ := by
          rw [bankTrialLocalRunAppend, hrun]
          exact he
        change (bankTrialLocalRun ring root es
          (bankTrialLocalNext ring root
            (⟨B, .recovery⟩ : BankTrialLocalState q) e)).phase ≠ .won
        rw [he]
        exact ih (pre ++ [e])
          (GrantBankReference.bankLocalReferenceStepClamped
            ring root B e) hlong

/-- The actual continuation mass of a reachable recovery cut is
zero at every finite horizon, not merely on its next letter. -/
theorem bankTrialProbabilityRecoveryWinMassZero {n q : Nat}
    (ring : DirectedRing n) (root : Fin n) (hn : 2 ≤ n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S)
    (pre : List (Fin n))
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hrun : bankTrialLocalRun ring root pre
      (bankTrialLocalStart S) = ⟨B, .recovery⟩)
    (T : Nat) :
    bankTrialProbabilityStateWinMass ring root
      (⟨B, .recovery⟩ : BankTrialLocalState q) T = 0 := by
  have hw : (fun w : List (Fin n) =>
      if (bankTrialLocalRun ring root w
        (⟨B, .recovery⟩ : BankTrialLocalState q)).phase = .won
      then 1 else 0) = (fun _ => 0) := by
    funext w
    exact if_neg (bankTrialProbabilityRecoverySuffixNotWon
      ring root hn S hclean w pre B hrun)
  unfold bankTrialProbabilityStateWinMass
  rw [hw, bankTrialProbabilityScheduleSumConst]
  exact Nat.mul_zero _

/-- The literal first-head row from a zero first digit enters
CSTART, not an ARMED decision state. -/
private theorem bankTrialProbabilityRawCleanHeadMode
    (b : Nat) (theta : Nat → Bool) (x y : BankCell)
    (hb : 1 ≤ b) (hx : x.role = 0) (hy : y.role = 1)
    (hg : x.grant = false) (hm : x.mode = .ARMED)
    (ht : y.tok = .E) (hbit : y.bit = false) :
    (bankPair x y 1 b theta).1.mode = .CSTART := by
  simp [bankPair, hx, hy, hg, hm, ht, hbit, hb,
    isRetTok, isWaitMode, Id.run]
  all_goals rfl

/-- An incident LIVE service whose post-bank is unlatched and
CSTART remains LIVE, with the begun flag true. -/
theorem bankTrialProbabilityLiveCStartNext {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b) (begun : Bool)
    (hf : (GrantBankReference.bankLocalReferenceStepClamped
      ring root B e).success = false)
    (hm : ((GrantBankReference.bankLocalReferenceStepClamped
      ring root B e).fields ⟨0, by omega⟩).1 = .CSTART)
    (hi : e = root ∨ ring.rightNeighbor e = root) :
    bankTrialLocalNext ring root
      (⟨B, .live begun⟩ : BankTrialLocalState q) e =
      ⟨GrantBankReference.bankLocalReferenceStepClamped
        ring root B e, .live true⟩ := by
  have hc : ¬ BankTrialLocalClean q
      (GrantBankReference.bankLocalReferenceStepClamped
        ring root B e) := by
    intro h
    have ha := h.2.1
    rw [hm] at ha
    cases ha
  have hmZero : ((GrantBankReference.bankLocalReferenceStepClamped
      ring root B e).fields (0 : Fin ((compileAdvice q).b + 1))).1 =
      .CSTART := hm
  simp [bankTrialLocalNext, hf, hc, hm, hmZero, hi]

/-- From every CLEAN seed, the first outgoing root head reaches
an unlatched LIVE CSTART cut. -/
theorem bankTrialProbabilityCleanHeadCStart {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S) :
    (GrantBankReference.bankLocalReferenceStepClamped
      ring root S root).success = false ∧
    ((GrantBankReference.bankLocalReferenceStepClamped
      ring root S root).fields ⟨0, by omega⟩).1 = .CSTART ∧
    bankTrialLocalNext ring root (bankTrialLocalStart S) root =
      ⟨GrantBankReference.bankLocalReferenceStepClamped
        ring root S root, .live true⟩ := by
  have hb : 1 ≤ (compileAdvice q).b := by
    change 1 ≤ (compileAdvice q).s + 11
    omega
  have hfirst := hclean.2.2.1 1 (Nat.le_refl _) hb
  have hrow := bankTrialProbabilityRawCleanHeadMode
    (compileAdvice q).b (compileAdvice q).theta
    (GrantBankReference.bankLocalReferenceCell S ⟨0, by omega⟩)
    (GrantBankReference.bankLocalReferenceCell S
      ⟨1, Nat.lt_succ_of_le hb⟩)
    hb rfl rfl rfl hclean.2.1 hfirst.2 hfirst.1
  have hs : Counter.Support q ring root root :=
    Or.inr ⟨0, Nat.zero_le _, rfl⟩
  have hm : ((GrantBankReference.bankLocalReferenceStepClamped
      ring root S root).fields ⟨0, by omega⟩).1 = .CSTART := by
    rw [bankTrialLocalStepField ring root root S hs hclean.1,
      bankTrialLocalFieldRootOutgoing ring root S]
    change (GrantBankReference.bankLocalReferenceInternalPair q S
      ⟨0, by change 0 < (compileAdvice q).s + 11; omega⟩).1.mode =
      .CSTART
    exact hrow
  have hnot : (S.fields ⟨0, by omega⟩).1 ≠ .CWAIT := by
    rw [hclean.2.1]
    intro h
    cases h
  have hf := bankTrialLocalUnlatchedNonCWaitNoWin
    ring root root S hclean.1 hnot
  exact ⟨hf, hm, bankTrialProbabilityLiveCStartNext
    ring root root S false hf hm (Or.inl rfl)⟩

/-- Explicit exceptional class: incoming at CSTART does NOT reset
the root. The unary incoming map clears its root token but leaves
its mode CSTART, independent of other selected logical slots. -/
theorem bankTrialProbabilityIncomingCStartMode {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hf : B.success = false)
    (hm : (B.fields ⟨0, by omega⟩).1 = .CSTART)
    (hne : e ≠ root) (hin : ring.rightNeighbor e = root) :
    ((GrantBankReference.bankLocalReferenceStepClamped
      ring root B e).fields ⟨0, by omega⟩).1 = .CSTART := by
  have hb : 1 < (compileAdvice q).b := by
    change 1 < (compileAdvice q).s + 11
    omega
  have hx : ¬ (0 < (compileAdvice q).b ∧
      e = Counter.site ring root 0) := by
    intro h
    exact hne (by simpa only [Counter.site] using h.2)
  have hy : ¬ (0 < (0 : Nat) ∧
      e = Counter.site ring root (0 - 1)) := by
    intro h
    have hz : (0 : Nat) < 0 := h.1
    omega
  have ht : ¬ ((0 : Nat) = (compileAdvice q).b ∧
      e = Counter.site ring root (compileAdvice q).b) := by
    intro h
    omega
  rw [bankTrialLocalStepField ring root e B (Or.inl hin) hf,
    bankTrialLocalSelectedIncoming ring root e B
      ⟨0, by omega⟩ hx hy ht ⟨rfl, hin⟩]
  change (GrantBankReference.incomingRootBankMap
    (GrantBankReference.bankLocalReferenceCell B
      ⟨0, by omega⟩)).mode = .CSTART
  have hcell : (GrantBankReference.bankLocalReferenceCell B
      ⟨0, by omega⟩).mode = .CSTART := hm
  have hzero :
      (0 : Fin ((compileAdvice q).b + 1)) =
        ⟨0, by omega⟩ := Fin.ext (by simp)
  have hcellZero :
      (GrantBankReference.bankLocalReferenceCell B
        (0 : Fin ((compileAdvice q).b + 1))).mode = .CSTART := by
    rw [hzero]
    exact hcell
  rw [← hzero]
  cases hmode :
      (GrantBankReference.bankLocalReferenceCell B
        (0 : Fin ((compileAdvice q).b + 1))).mode <;>
    simp [GrantBankReference.incomingRootBankMap,
      hmode, isWaitMode] at hcellZero ⊢

/-- The exceptional incoming CSTART row is LIVE, not RECOVERY,
LOST, or a new ARMED-head decision. -/
theorem bankTrialProbabilityIncomingCStartLive {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hf : B.success = false)
    (hm : (B.fields ⟨0, by omega⟩).1 = .CSTART)
    (hne : e ≠ root) (hin : ring.rightNeighbor e = root) :
    ((GrantBankReference.bankLocalReferenceStepClamped
      ring root B e).fields ⟨0, by omega⟩).1 = .CSTART ∧
    bankTrialLocalNext ring root
      (⟨B, .live true⟩ : BankTrialLocalState q) e =
      ⟨GrantBankReference.bankLocalReferenceStepClamped
        ring root B e, .live true⟩ := by
  have hm' := bankTrialProbabilityIncomingCStartMode
    ring root e B hf hm hne hin
  have hf' := bankTrialLocalUnlatchedNonrootNoWin
    ring root e B hf hne
  exact ⟨hm', bankTrialProbabilityLiveCStartNext
    ring root e B true hf' hm' (Or.inr hin)⟩

/-- CLEAN-reachable witness to the failure of the ungated
incoming-is-terminal rule: the word [root,incoming] is still LIVE. -/
theorem bankTrialProbabilityCleanHeadIncomingLive {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S)
    (hne : e ≠ root) (hin : ring.rightNeighbor e = root) :
    (bankTrialLocalRun ring root [root, e]
      (bankTrialLocalStart S)).phase = .live true := by
  have hhead := bankTrialProbabilityCleanHeadCStart
    ring root S hclean
  have hinc := bankTrialProbabilityIncomingCStartLive
    ring root e
    (GrantBankReference.bankLocalReferenceStepClamped
      ring root S root) hhead.1 hhead.2.1 hne hin
  change (bankTrialLocalNext ring root
    (bankTrialLocalNext ring root (bankTrialLocalStart S) root) e).phase =
    .live true
  rw [hhead.2.2, hinc.2]

/-- The two-letter witness is genuinely nonterminal. This does
not claim that a particular continuation is winning. -/
theorem bankTrialProbabilityCleanHeadIncomingNotTerminal {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S)
    (hne : e ≠ root) (hin : ring.rightNeighbor e = root) :
    ¬ bankTrialLocalTerminal
      (bankTrialLocalRun ring root [root, e] (bankTrialLocalStart S)) := by
  intro ht
  have hp := bankTrialProbabilityCleanHeadIncomingLive
    ring root e S hclean hne hin
  rcases ht with hw | hl
  · rw [hp] at hw
    cases hw
  · rw [hp] at hl
    cases hl

/-- This is the LIVE acceptance row requiring the still-missing
head-count provenance. It is NOT a claim that arbitrary such
snapshots are reachable from CLEAN. RecoveryNoWin does not apply
to a LIVE CWAIT/CL1 snapshot. -/
theorem bankTrialProbabilityLiveReturnWon {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b) (begun : Bool)
    (hf : B.success = false)
    (hm : (B.fields ⟨0, by omega⟩).1 = .CWAIT)
    (ht : (B.fields
      ⟨1, by change 1 < (compileAdvice q).s + 11 + 1; omega⟩).2.2.1 = .CL1) :
    (bankTrialLocalNext ring root
      (⟨B, .live begun⟩ : BankTrialLocalState q) root).phase = .won := by
  have hevent : GrantBankReference.bankLocalReferenceSuccessEvent
      ring root B root = true := by
    unfold GrantBankReference.bankLocalReferenceSuccessEvent
    rw [if_pos rfl]
    change bankSuccess
      (GrantBankReference.bankLocalReferenceCell B ⟨0, by omega⟩)
      (GrantBankReference.bankLocalReferenceCell B
        ⟨1, by change 1 < (compileAdvice q).s + 11 + 1; omega⟩)
      1 (compileAdvice q).b = true
    simp [bankSuccess, GrantBankReference.bankLocalReferenceCell, ht]
    have hzero :
        (0 : Fin ((compileAdvice q).b + 1)) =
          ⟨0, by omega⟩ := Fin.ext (by simp)
    rw [hzero]
    exact hm
  have hs : Counter.Support q ring root root :=
    Or.inr ⟨0, Nat.zero_le _, rfl⟩
  have hsuccess : (GrantBankReference.bankLocalReferenceStepClamped
      ring root B root).success = true := by
    simp [GrantBankReference.bankLocalReferenceStepClamped,
      hs, hf, hevent]
  simp [bankTrialLocalNext, hsuccess]

end L3

namespace L3

set_option autoImplicit false
set_option Elab.async false

/-!
Necessary OLD success and ARMED-incoming tail barriers.
These facts do NOT close the missing K-head provenance.
The unconditional upper bound is deliberately not asserted.
-/

/-- An unlatched LIVE observer can first enter WON only on a
root outgoing service with the literal old CWAIT/CL1 acceptance
guard. In particular an incoming root service cannot win. -/
theorem bankTrialProbabilityLiveWonRequiresOldGuard {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b) (begun : Bool)
    (hf : B.success = false)
    (hw : (bankTrialLocalNext ring root
      (⟨B, .live begun⟩ : BankTrialLocalState q) e).phase = .won) :
    e = root ∧
    (B.fields ⟨0, by omega⟩).1 = .CWAIT ∧
    (B.fields
      ⟨1, by change 1 < (compileAdvice q).s + 11 + 1; omega⟩).2.2.1 = .CL1 := by
  have hsuccess :
      (GrantBankReference.bankLocalReferenceStepClamped
        ring root B e).success = true := by
    cases hs : (GrantBankReference.bankLocalReferenceStepClamped
        ring root B e).success with
    | true => rfl
    | false =>
        by_cases hclean :
            BankTrialLocalClean q
              (GrantBankReference.bankLocalReferenceStepClamped
                ring root B e) ∧
            (begun = true ∨ e = root ∨ ring.rightNeighbor e = root)
        · simp [bankTrialLocalNext, hs, hclean] at hw
        · by_cases hreset :
            ((GrantBankReference.bankLocalReferenceStepClamped
              ring root B e).fields
              (0 : Fin ((compileAdvice q).b + 1))).1 = .RESET
          · simp [bankTrialLocalNext, hs, hclean, hreset] at hw
          · simp [bankTrialLocalNext, hs, hclean, hreset] at hw
  have hroot : e = root := by
    by_cases he : e = root
    · exact he
    · have hfalse := bankTrialLocalUnlatchedNonrootNoWin
        ring root e B hf he
      rw [hfalse] at hsuccess
      cases hsuccess
  have hmode : (B.fields ⟨0, by omega⟩).1 = .CWAIT := by
    by_cases hm : (B.fields ⟨0, by omega⟩).1 = .CWAIT
    · exact hm
    · have hfalse := bankTrialLocalUnlatchedNonCWaitNoWin
        ring root e B hf hm
      rw [hfalse] at hsuccess
      cases hsuccess
  subst e
  have hs : Counter.Support q ring root root :=
    Or.inr ⟨0, Nat.zero_le _, rfl⟩
  have hevent :
      GrantBankReference.bankLocalReferenceSuccessEvent
        ring root B root = true := by
    simpa [GrantBankReference.bankLocalReferenceStepClamped,
      hs, hf] using hsuccess
  have htok :
      (B.fields
        ⟨1, by change 1 < (compileAdvice q).s + 11 + 1; omega⟩).2.2.1 =
        .CL1 := by
    by_cases ht :
        (B.fields
          ⟨1, by change 1 < (compileAdvice q).s + 11 + 1; omega⟩).2.2.1 =
          .CL1
    · exact ht
    · have hfalseEvent :
          GrantBankReference.bankLocalReferenceSuccessEvent
            ring root B root = false := by
        unfold GrantBankReference.bankLocalReferenceSuccessEvent
        rw [if_pos rfl]
        change bankSuccess
          (GrantBankReference.bankLocalReferenceCell B
            ⟨0, by omega⟩)
          (GrantBankReference.bankLocalReferenceCell B
            ⟨1, by change 1 < (compileAdvice q).s + 11 + 1; omega⟩)
          1 (compileAdvice q).b = false
        simp [bankSuccess, GrantBankReference.bankLocalReferenceCell, ht]
      rw [hfalseEvent] at hevent
      cases hevent
  exact ⟨rfl, hmode, htok⟩

/-- The incoming boundary map sends an unlatched ARMED root to
RESET, even if the physical letter also selects other logical
sites. This is a local-reference statement. -/
theorem bankTrialProbabilityIncomingArmedRootReset {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hf : B.success = false)
    (hm : (B.fields ⟨0, by omega⟩).1 = .ARMED)
    (hne : e ≠ root)
    (hin : ring.rightNeighbor e = root) :
    ((GrantBankReference.bankLocalReferenceStepClamped
      ring root B e).fields ⟨0, by omega⟩).1 = .RESET := by
  have hb : 1 < (compileAdvice q).b := by
    change 1 < (compileAdvice q).s + 11
    omega
  have hx : ¬ (0 < (compileAdvice q).b ∧
      e = Counter.site ring root 0) := by
    intro h
    exact hne (by simpa only [Counter.site] using h.2)
  have hy : ¬ (0 < (0 : Nat) ∧
      e = Counter.site ring root (0 - 1)) := by
    intro h
    omega
  have ht : ¬ ((0 : Nat) = (compileAdvice q).b ∧
      e = Counter.site ring root (compileAdvice q).b) := by
    intro h
    omega
  rw [bankTrialLocalStepField ring root e B (Or.inl hin) hf,
    bankTrialLocalSelectedIncoming ring root e B
      ⟨0, by omega⟩ hx hy ht ⟨rfl, hin⟩]
  change (GrantBankReference.incomingRootBankMap
    (GrantBankReference.bankLocalReferenceCell B
      ⟨0, by omega⟩)).mode = .RESET
  have hcell : (GrantBankReference.bankLocalReferenceCell B
      ⟨0, by omega⟩).mode = .ARMED := hm
  have hzero :
      (0 : Fin ((compileAdvice q).b + 1)) =
        ⟨0, by omega⟩ := Fin.ext (by simp)
  have hcellZero :
      (GrantBankReference.bankLocalReferenceCell B
        (0 : Fin ((compileAdvice q).b + 1))).mode = .ARMED := by
    rw [hzero]
    exact hcell
  rw [← hzero]
  cases hmode :
      (GrantBankReference.bankLocalReferenceCell B
        (0 : Fin ((compileAdvice q).b + 1))).mode <;>
    simp [GrantBankReference.incomingRootBankMap,
      hmode, isWaitMode] at hcellZero ⊢

/-- An incoming scheduler letter at a still-LIVE, unlatched
ARMED root enters RECOVERY rather than preserving an ARMED gate.
The recovery certificate rules subsequently prevent success. -/
theorem bankTrialProbabilityIncomingArmedEntersRecovery {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b) (begun : Bool)
    (hf : B.success = false)
    (hm : (B.fields ⟨0, by omega⟩).1 = .ARMED)
    (hne : e ≠ root)
    (hin : ring.rightNeighbor e = root) :
    bankTrialLocalNext ring root
      (⟨B, .live begun⟩ : BankTrialLocalState q) e =
        ⟨GrantBankReference.bankLocalReferenceStepClamped
          ring root B e, .recovery⟩ := by
  have hfalse := bankTrialLocalUnlatchedNonrootNoWin
    ring root e B hf hne
  have hreset := bankTrialProbabilityIncomingArmedRootReset
    ring root e B hf hm hne hin
  have hnotclean :
      ¬ BankTrialLocalClean q
        (GrantBankReference.bankLocalReferenceStepClamped
          ring root B e) := by
    intro hc
    have hmode := hc.2.1
    rw [hreset] at hmode
    cases hmode
  have hguard :
      ¬ (BankTrialLocalClean q
            (GrantBankReference.bankLocalReferenceStepClamped
              ring root B e) ∧
          (begun = true ∨ e = root ∨ ring.rightNeighbor e = root)) := by
    intro h
    exact hnotclean h.1
  have hzero :
      (0 : Fin ((compileAdvice q).b + 1)) =
        ⟨0, by omega⟩ := Fin.ext (by simp)
  have hresetZero :
      ((GrantBankReference.bankLocalReferenceStepClamped
        ring root B e).fields
          (0 : Fin ((compileAdvice q).b + 1))).1 = .RESET := by
    rw [hzero]
    exact hreset
  simp [bankTrialLocalNext, hfalse, hguard, hresetZero]

/-- The incoming ARMED tail can never be followed by a winning
continuation of the same clean-start observer, once its LIVE
prefix and false old latch are authenticated. -/
theorem bankTrialProbabilityIncomingArmedNoWinSuffix {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n) (hn : 2 ≤ n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S)
    (pre suffix : List (Fin n))
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b) (begun : Bool)
    (hrun : bankTrialLocalRun ring root pre
      (bankTrialLocalStart S) = ⟨B, .live begun⟩)
    (hf : B.success = false)
    (hm : (B.fields ⟨0, by omega⟩).1 = .ARMED)
    (hne : e ≠ root)
    (hin : ring.rightNeighbor e = root) :
    (bankTrialLocalRun ring root (pre ++ e :: suffix)
      (bankTrialLocalStart S)).phase ≠ .won := by
  have hnext := bankTrialProbabilityIncomingArmedEntersRecovery
    ring root e B begun hf hm hne hin
  have hrec :
      bankTrialLocalRun ring root (pre ++ [e])
        (bankTrialLocalStart S) =
        ⟨GrantBankReference.bankLocalReferenceStepClamped
          ring root B e, .recovery⟩ := by
    rw [bankTrialLocalRunAppend, hrun]
    exact hnext
  have hnever :=
    bankTrialProbabilityRecoverySuffixNotWon ring root hn S hclean
      suffix (pre ++ [e])
      (GrantBankReference.bankLocalReferenceStepClamped ring root B e)
      hrec
  have hword :
      pre ++ e :: suffix = (pre ++ [e]) ++ suffix := by
    simp [List.append_assoc]
  rw [hword, bankTrialLocalRunAppend, hrec]
  exact hnever

end L3


/-!
Adapted LIVE-ARMED head census for the original local
BANK observer.

Each counted head reads the OLD local phase and root mode;
every physical edge updates the local observer. A forwarded IR
may change higher digits on a supported NONROOT edge. Thus a
numeric invariant requires an in-flight carry credit, not a
claim that all nonroot edges frame BANK digits.
-/

namespace L3

open Classical
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

set_option autoImplicit false
set_option Elab.async false

def bankTrialLiveBinaryValue {q : Nat}
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b) : Nat :=
  (List.ofFn (fun j : Fin (compileAdvice q).b =>
    if (B.fields ⟨j.val + 1, by omega⟩).2.1
    then 2 ^ j.val else 0)).sum

/-- All digit bits start zero at the installed CLEAN entrance. -/
theorem bankTrialLiveBinaryClean {q : Nat}
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S) :
    bankTrialLiveBinaryValue S = 0 := by
  have hzero : ∀ j : Fin (compileAdvice q).b,
      (S.fields ⟨j.val + 1, by omega⟩).2.1 = false := by
    intro j
    exact (hclean.2.2.1 (j.val + 1)
      (by omega : 1 ≤ j.val + 1)
      (by omega : j.val + 1 ≤ (compileAdvice q).b)).1
  unfold bankTrialLiveBinaryValue
  calc
    (List.ofFn (fun j : Fin (compileAdvice q).b =>
      if (S.fields ⟨j.val + 1, by omega⟩).2.1
      then 2 ^ j.val else 0)).sum =
        (List.ofFn (fun _ : Fin (compileAdvice q).b => 0)).sum := by
          apply ofFn_sum_eq
          intro j
          rw [hzero j]
          rfl
    _ = 0 := by
      rw [ofFn_sum_const]
      exact Nat.mul_zero _

/-- Count OLD LIVE ARMED outgoing root decisions on the SAME
chronological Fin n edge word, retaining the full next observer. -/
noncomputable def bankTrialLiveHeadCount {n q : Nat}
    (ring : DirectedRing n) (root : Fin n) :
    List (Fin n) → BankTrialLocalState q → Nat
  | [], _ => 0
  | e :: tail, z =>
      (if BankTrialProbabilityArmedGate z ∧ e = root
        then 1 else 0) +
      bankTrialLiveHeadCount ring root tail
        (bankTrialLocalNext ring root z e)

/-- A sufficient no-ARMED-incoming condition; unlike the
head-event it checks even after the required K heads. -/
def BankTrialNoArmedIncoming {n q : Nat}
    (ring : DirectedRing n) (root : Fin n) :
    List (Fin n) → BankTrialLocalState q → Prop
  | [], _ => True
  | e :: tail, z =>
      (BankTrialProbabilityArmedGate z →
        e = root ∨ ring.rightNeighbor e ≠ root) ∧
      BankTrialNoArmedIncoming ring root tail
        (bankTrialLocalNext ring root z e)

/-- Pure gate counting, independent of the BANK numeric counter.
The necessary missing step is to authenticate the hypotheses
from a genuine CLEAN-start WIN. -/
theorem bankTrialHeadEventOfCount {n q : Nat}
    (ring : DirectedRing n) (root : Fin n) :
    ∀ (word : List (Fin n)) (k : Nat)
      (z : BankTrialLocalState q),
      BankTrialNoArmedIncoming ring root word z →
      k ≤ bankTrialLiveHeadCount ring root word z →
      bankTrialProbabilityHeadEvent ring root word k z := by
  intro word
  induction word with
  | nil =>
      intro k z _ hcount
      change k = 0
      change k ≤ 0 at hcount
      omega
  | cons e tail ih =>
      intro k z hno hcount
      cases k with
      | zero =>
          change True
          exact True.intro
      | succ k =>
          have htail :
              BankTrialNoArmedIncoming ring root tail
                (bankTrialLocalNext ring root z e) := hno.2
          by_cases hgate : BankTrialProbabilityArmedGate z
          · by_cases hroot : e = root
            · have hbound :
                  k ≤ bankTrialLiveHeadCount ring root tail
                    (bankTrialLocalNext ring root z e) := by
                have hc :
                    k + 1 ≤ 1 +
                      bankTrialLiveHeadCount ring root tail
                        (bankTrialLocalNext ring root z e) := by
                  simpa [bankTrialLiveHeadCount, hgate, hroot]
                    using hcount
                omega
              have hh := ih k
                (bankTrialLocalNext ring root z e) htail hbound
              simpa only [bankTrialProbabilityHeadEvent,
                if_pos hgate, if_pos hroot] using hh
            · have hnon : ring.rightNeighbor e ≠ root := by
                rcases hno.1 hgate with h | h
                · exact False.elim (hroot h)
                · exact h
              have hbound :
                  k + 1 ≤ bankTrialLiveHeadCount ring root tail
                    (bankTrialLocalNext ring root z e) := by
                simpa [bankTrialLiveHeadCount, hgate, hroot]
                  using hcount
              have hh := ih (k + 1)
                (bankTrialLocalNext ring root z e) htail hbound
              simpa only [bankTrialProbabilityHeadEvent,
                if_pos hgate, if_neg hroot, if_neg hnon] using hh
          · have hbound :
                k + 1 ≤ bankTrialLiveHeadCount ring root tail
                  (bankTrialLocalNext ring root z e) := by
              simpa [bankTrialLiveHeadCount, hgate] using hcount
            have hh := ih (k + 1)
              (bankTrialLocalNext ring root z e) htail hbound
            simpa only [bankTrialProbabilityHeadEvent,
              if_neg hgate] using hh


/-- LIVE numeric-plus-comparator invariant. The first conjunct
counts the actual binary digit value. The second demands that
a LIVE OLD CWAIT/CL1 success has K legitimate ARMED heads.
The second needs the real IR/AL/CR/CL provenance, not merely
the existence of completion-looking private BANK bytes. -/
def BankTrialLiveHeadCount {q : Nat}
    (z : BankTrialLocalState q) (heads : Nat) : Prop :=
  (∀ begun : Bool, z.phase = .live begun →
    bankTrialLiveBinaryValue z.bank ≤ heads) ∧
  (∀ begun : Bool, z.phase = .live begun →
    (z.bank.fields ⟨0, by omega⟩).1 = .CWAIT →
    (z.bank.fields
      ⟨1, by change 1 < (compileAdvice q).s + 11 + 1; omega⟩).2.2.1 =
        .CL1 →
    (compileAdvice q).K ≤ heads)

/-- The two LIVE clauses hold at a true CLEAN entrance. -/
theorem bankTrialLiveHeadCountStart {q : Nat}
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S) :
    BankTrialLiveHeadCount (bankTrialLocalStart S) 0 := by
  constructor
  · intro begun _
    change bankTrialLiveBinaryValue S ≤ 0
    rw [bankTrialLiveBinaryClean S hclean]
    exact Nat.le_refl 0
  · intro begun _ hmode _
    change (S.fields ⟨0, by omega⟩).1 = .CWAIT at hmode
    rw [hclean.2.1] at hmode
    cases hmode

theorem bankTrialLiveCleanArmedGate {q : Nat}
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S) :
    BankTrialProbabilityArmedGate (bankTrialLocalStart S) := by
  exact ⟨⟨false, rfl⟩, hclean.2.1⟩

theorem bankTrialLiveFirstHeadCount {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S) :
    bankTrialLiveHeadCount ring root [root]
      (bankTrialLocalStart S) = 1 := by
  have hg := bankTrialLiveCleanArmedGate S hclean
  simp [bankTrialLiveHeadCount, hg]

/-- A first ARMED head on the initial zero first digit is
paid once and enters LIVE CSTART, not immediate success. -/
theorem bankTrialLiveFirstHeadCStart {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S) :
    (bankTrialLocalRun ring root [root]
      (bankTrialLocalStart S)).phase = .live true ∧
    bankTrialLiveHeadCount ring root [root]
      (bankTrialLocalStart S) = 1 := by
  have hrow := bankTrialProbabilityCleanHeadCStart
    ring root S hclean
  constructor
  · change (bankTrialLocalNext ring root
      (bankTrialLocalStart S) root).phase = .live true
    rw [hrow.2.2]
  · exact bankTrialLiveFirstHeadCount ring root S hclean

/-- Genuinely UNSUPPORTED edges frame the full local BANK array.
The root-incident and supported internal IR services are NOT
covered by this result. -/
theorem bankTrialLiveOutsideBankFrame {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b) (begun : Bool)
    (hout : ¬ Counter.Support q ring root e) :
    (bankTrialLocalNext ring root
      (⟨B, .live begun⟩ : BankTrialLocalState q) e).bank = B := by
  exact (bankTrialLocalNextLiveBank ring root e B begun).trans
    (bankTrialLocalStepOutside ring root e B hout)

/-- An actual incoming root at a still-clean initial ARMED
gate enters recovery and cannot win on any later suffix. -/
theorem bankTrialLiveInitialIncomingNoWin {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n) (hn : 2 ≤ n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S)
    (hne : e ≠ root)
    (hin : ring.rightNeighbor e = root)
    (suffix : List (Fin n)) :
    (bankTrialLocalRun ring root (e :: suffix)
      (bankTrialLocalStart S)).phase ≠ .won := by
  have hnone : bankTrialLocalRun ring root []
      (bankTrialLocalStart S) =
      ⟨S, .live false⟩ := rfl
  exact bankTrialProbabilityIncomingArmedNoWinSuffix
    ring root e hn S hclean [] suffix S false
    hnone hclean.1 hclean.2.1 hne hin

/-- Precisely the missing CLEAN-reachable one-edge induction:
supported IR forward and AL return can change digit bits
without paying another root head. The stronger pending-carry
credit, and true comparator genealogy, must be supplied here. -/
def BankTrialLiveHeadCountStep {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b) : Prop :=
  ∀ (pre : List (Fin n)) (e : Fin n),
    BankTrialLiveHeadCount
      (bankTrialLocalRun ring root pre (bankTrialLocalStart S))
      (bankTrialLiveHeadCount ring root pre
        (bankTrialLocalStart S)) →
    BankTrialLiveHeadCount
      (bankTrialLocalRun ring root (pre ++ [e])
        (bankTrialLocalStart S))
      (bankTrialLiveHeadCount ring root (pre ++ [e])
        (bankTrialLocalStart S))

/-- The actual induction on chronological prefixes, conditional
only on the precisely stated missing per-edge row assertion. -/
theorem bankTrialLiveHeadCountOnWordsOfStep {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S)
    (hstep : BankTrialLiveHeadCountStep ring root S) :
    ∀ word : List (Fin n),
      BankTrialLiveHeadCount
        (bankTrialLocalRun ring root word (bankTrialLocalStart S))
        (bankTrialLiveHeadCount ring root word
          (bankTrialLocalStart S)) := by
  have hreverse : ∀ rev : List (Fin n),
      BankTrialLiveHeadCount
        (bankTrialLocalRun ring root rev.reverse
          (bankTrialLocalStart S))
        (bankTrialLiveHeadCount ring root rev.reverse
          (bankTrialLocalStart S)) := by
    intro rev
    induction rev with
    | nil =>
        exact bankTrialLiveHeadCountStart S hclean
    | cons e rev ih =>
        rw [List.reverse_cons]
        exact hstep rev.reverse e ih
  intro word
  have h := hreverse word.reverse
  simpa only [List.reverse_reverse] using h


/-- The remaining CLEAN-reachable winning-word ledger.
It requires at least K genuinely counted heads and excludes
an incoming root service at an open ARMED gate. This is a
named UNPROVED Prop, not an assertion of G11 authentication. -/
def BankTrialLiveWinningLedger {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b) : Prop :=
  (compileAdvice q).useSmall = false →
  2 * (compileAdvice q).bankLeaseCap ≤ n →
  BankTrialLocalClean q S →
  ∀ word : List (Fin n),
    (bankTrialLocalRun ring root word
      (bankTrialLocalStart S)).phase = .won →
    (compileAdvice q).K ≤
      bankTrialLiveHeadCount ring root word
        (bankTrialLocalStart S) ∧
    BankTrialNoArmedIncoming ring root word
      (bankTrialLocalStart S)

/-- The winning-ledger statement implies exactly the deterministic
hauth input of the existing G11 probability upper lemma. -/
theorem bankTrialHeadAuthenticationOfWinningLedger {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hledger : BankTrialLiveWinningLedger ring root S) :
    (compileAdvice q).useSmall = false →
    2 * (compileAdvice q).bankLeaseCap ≤ n →
    BankTrialLocalClean q S →
    ∀ word : List (Fin n),
      (bankTrialLocalRun ring root word
        (bankTrialLocalStart S)).phase = .won →
      bankTrialProbabilityHeadEvent ring root word
        (compileAdvice q).K (bankTrialLocalStart S) := by
  intro hsp hlarge hclean word hw
  have hc := hledger hsp hlarge hclean word hw
  exact bankTrialHeadEventOfCount ring root word
    (compileAdvice q).K (bankTrialLocalStart S)
    hc.2 hc.1

/-- G11's probability bound follows CONDITIONALLY from that
unproved distributed-counter and comparison-provenance ledger.
The unconditional target is not declared proved here. -/
theorem bankTrialProbabilityUpperOfWinningLedger {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hledger : BankTrialLiveWinningLedger ring root S) :
    BankTrialProbabilityUpperTarget ring root S := by
  exact bankTrialProbabilityUpperOfHeadAuthentication
    ring root S
    (bankTrialHeadAuthenticationOfWinningLedger
      ring root S hledger)

end L3
/-!
A carry-aware LIVE ledger.
The all-row and comparator-provenance predicates below
are explicitly UNPROVED obligations, never axioms or theorems.
-/

namespace L3

open Classical
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

set_option autoImplicit false
set_option Elab.async false

/-- The digit at protected slot j+1 has weight 2^j.
An IR at that slot intends to write slot j+2, and therefore
has weight 2^(j+1). AL is an acknowledgment, not an
additional numerical carry. RR/CR/CL do not create bank credit. -/
def bankTrialLiveSlotPotential (j : Nat)
    (bit : Bool) (tok : BTok) : Nat :=
  (if bit then 2 ^ j else 0) +
    (if tok = .IR then 2 ^ (j + 1) else 0)

/-- Actual bounded protected BANK digits plus *in-flight* IR.
The top-slot IR is included with weight 2^b, even though it
will be erased at the next top service. This over-approximation
makes the top-boundary step a decrease, not a false frame.
No root-mode, CSTART, CR, or AL numeric credit is added:
their required provenance is recorded separately below. -/
def bankTrialLiveCarryValue {q : Nat}
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b) : Nat :=
  (List.ofFn (fun j : Fin (compileAdvice q).b =>
    bankTrialLiveSlotPotential j.val
      (B.fields ⟨j.val + 1, by omega⟩).2.1
      (B.fields ⟨j.val + 1, by omega⟩).2.2.1)).sum

/-- Projecting away the nonnegative IR credit never increases
the potential. This is the bridge to the earlier binary bound. -/
theorem bankTrialLiveBinaryLeCarry {q : Nat}
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b) :
    bankTrialLiveBinaryValue B ≤ bankTrialLiveCarryValue B := by
  unfold bankTrialLiveBinaryValue bankTrialLiveCarryValue
    bankTrialLiveSlotPotential
  apply ofFn_sum_le
  intro j
  omega

/-- All protected bits and IR tokens are empty at CLEAN. -/
theorem bankTrialLiveCarryClean {q : Nat}
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S) :
    bankTrialLiveCarryValue S = 0 := by
  have hzero : ∀ j : Fin (compileAdvice q).b,
      bankTrialLiveSlotPotential j.val
        (S.fields ⟨j.val + 1, by omega⟩).2.1
        (S.fields ⟨j.val + 1, by omega⟩).2.2.1 = 0 := by
    intro j
    have hz := hclean.2.2.1 (j.val + 1)
      (by omega : 1 ≤ j.val + 1)
      (by omega : j.val + 1 ≤ (compileAdvice q).b)
    simp [bankTrialLiveSlotPotential, hz.1, hz.2]
  unfold bankTrialLiveCarryValue
  calc
    (List.ofFn (fun j : Fin (compileAdvice q).b =>
      bankTrialLiveSlotPotential j.val
        (S.fields ⟨j.val + 1, by omega⟩).2.1
        (S.fields ⟨j.val + 1, by omega⟩).2.2.1)).sum =
        (List.ofFn (fun _ : Fin (compileAdvice q).b => 0)).sum := by
          apply ofFn_sum_eq
          exact hzero
    _ = 0 := by
      rw [ofFn_sum_const]
      exact Nat.mul_zero _

/-- The two literal ARMED outgoing branches, in their common
digit-one arithmetic: a zero bit becomes one; a one bit becomes
zero and launches a 2-weight IR. Each spends exactly one head. -/
theorem bankTrialLiveRootHeadArithmetic (bit : Bool) :
    bankTrialLiveSlotPotential 0 (!bit)
      (if bit then BTok.IR else BTok.E) =
    bankTrialLiveSlotPotential 0 bit .E + 1 := by
  cases bit <;> simp [bankTrialLiveSlotPotential]

/-- The literal IR-forward row's arithmetic for slots j+1 and
j+2. In the no-collision row, the source IR is erased; the next
bit flips; the new token is IR on an old-one bit, AL on zero.
The equality includes BOTH old source and destination credits.
It does not claim that all nonroot services frame bits. -/
theorem bankTrialLiveIRForwardArithmetic
    (j : Nat) (sourceBit destBit : Bool) :
    bankTrialLiveSlotPotential j sourceBit .E +
      bankTrialLiveSlotPotential (j + 1) (!destBit)
        (if destBit then BTok.IR else BTok.AL) =
    bankTrialLiveSlotPotential j sourceBit .IR +
      bankTrialLiveSlotPotential (j + 1) destBit .E := by
  have hpow : 2 ^ (j + 2) = 2 * 2 ^ (j + 1) := by
    rw [show j + 2 = (j + 1) + 1 by omega, Nat.pow_succ]
    omega
  cases sourceBit <;> cases destBit <;>
    simp [bankTrialLiveSlotPotential, hpow] <;> omega

/-- Erasing an IR at the top never raises its slot credit. -/
theorem bankTrialLiveTopEraseArithmetic
    (j : Nat) (bit : Bool) (tok : BTok) :
    bankTrialLiveSlotPotential j bit
        (if tok = .IR then .E else tok) ≤
      bankTrialLiveSlotPotential j bit tok := by
  by_cases ht : tok = .IR
  · simp [bankTrialLiveSlotPotential, ht] <;> omega
  · simp [bankTrialLiveSlotPotential, ht] <;> omega

/-- The physical Fin-lease clamp changes neither bit nor token,
so it cannot invalidate any of the arithmetic identities above. -/
theorem bankTrialLiveClampBitToken
    (q : Nat) (z : BankCell) :
    (GrantBankReference.bankLocalReferenceClampedQuad q z).2.1 =
      z.bit ∧
    (GrantBankReference.bankLocalReferenceClampedQuad q z).2.2.1 =
      z.tok := by
  constructor <;> rfl

/-- Incoming-root modifies the root's mode, token and lease,
but not its (unweighted) root bit. -/
theorem bankTrialLiveIncomingPreservesBit
    (z : BankCell) :
    (GrantBankReference.incomingRootBankMap z).bit = z.bit := by
  unfold GrantBankReference.incomingRootBankMap
  split
  · rfl
  · split
    · split <;> rfl
    · rfl

/-- Equality-free LIVE invariant; no arbitrary LIVE scratch
is assumed to be reachable from CLEAN. The head budget counts
OLD-LIVE/ARMED root outgoing services as in the earlier head count. -/
def BankTrialLiveCarryLedger {q : Nat}
    (z : BankTrialLocalState q) (heads : Nat) : Prop :=
  ∀ begun : Bool, z.phase = .live begun →
    bankTrialLiveCarryValue z.bank ≤ heads

theorem bankTrialLiveCarryLedgerStart {q : Nat}
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S) :
    BankTrialLiveCarryLedger (bankTrialLocalStart S) 0 := by
  intro begun _
  change bankTrialLiveCarryValue S ≤ 0
  rw [bankTrialLiveCarryClean S hclean]
  exact Nat.le_refl 0

/-- Unsupported letters are genuine full-BANK frames and cannot
be counted as outgoing root heads. This does not apply to
SUPPORTED nonroot IR-forward edges. -/
theorem bankTrialLiveCarryUnsupportedRow {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b) (begun : Bool)
    (hout : ¬ Counter.Support q ring root e) :
    bankTrialLiveCarryValue
      (bankTrialLocalNext ring root
        (⟨B, .live begun⟩ : BankTrialLocalState q) e).bank =
      bankTrialLiveCarryValue B ∧
    bankTrialLiveHeadCount ring root [e]
      (⟨B, .live begun⟩ : BankTrialLocalState q) = 0 := by
  classical
  have hne : e ≠ root := by
    intro he
    subst e
    apply hout
    exact Or.inr ⟨0, Nat.zero_le _, rfl⟩
  constructor
  · exact congrArg bankTrialLiveCarryValue
      (bankTrialLiveOutsideBankFrame ring root e B begun hout)
  · simp [bankTrialLiveHeadCount, hne]

/-- UNPROVED all-row arithmetic obligation, expressed on the
EXACT clamped reference (including the independent boundary
tests and the top-to-root seam). The only allowed increase is
the one OLD ARMED root outgoing head. In the spatial regime
2*bankLeaseCap <= n, selected protected sites do not alias.
The abstract arithmetic lemmas above do not by themselves
prove this global pointwise List.ofFn-sum inequality. -/
def BankTrialLiveCarryRawRowBound {n q : Nat}
    (ring : DirectedRing n) (root : Fin n) : Prop :=
  ∀ (B : GrantBankReference.BankLocalReference
        (compileAdvice q).b) (e : Fin n),
    bankTrialLiveCarryValue
      (GrantBankReference.bankLocalReferenceStepClamped
        ring root B e) ≤
      bankTrialLiveCarryValue B +
        (if (B.fields ⟨0, by omega⟩).1 = .ARMED ∧ e = root
         then 1 else 0)

/-- The row bound implies the corresponding LIVE-phase closure.
For RECOVERY/WON/LOST the observer never reenters LIVE. -/
theorem bankTrialLiveCarryRowStepOfRaw {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hrow : BankTrialLiveCarryRawRowBound (q := q) ring root) :
    ∀ (z : BankTrialLocalState q) (heads : Nat) (e : Fin n),
      BankTrialLiveCarryLedger z heads →
      BankTrialLiveCarryLedger
        (bankTrialLocalNext ring root z e)
        (heads +
          (if BankTrialProbabilityArmedGate z ∧ e = root
           then 1 else 0)) := by
  classical
  intro z heads e hledger
  cases z with
  | mk B phase =>
    cases phase with
    | live begun =>
        intro nextBegun _
        have hbase : bankTrialLiveCarryValue B ≤ heads :=
          hledger begun rfl
        have hbank := bankTrialLocalNextLiveBank
          ring root e B begun
        change bankTrialLiveCarryValue
            (bankTrialLocalNext ring root
              (⟨B, .live begun⟩ : BankTrialLocalState q) e).bank ≤
          heads +
            (if BankTrialProbabilityArmedGate
              (⟨B, .live begun⟩ : BankTrialLocalState q) ∧
                e = root then 1 else 0)
        rw [hbank]
        have hdelta :
            (if (B.fields ⟨0, by omega⟩).1 = .ARMED ∧
              e = root then 1 else 0) =
            (if BankTrialProbabilityArmedGate
              (⟨B, .live begun⟩ : BankTrialLocalState q) ∧
                e = root then 1 else 0) := by
          by_cases hm : (B.fields ⟨0, by omega⟩).1 = .ARMED
          · have hg : BankTrialProbabilityArmedGate
                (⟨B, .live begun⟩ : BankTrialLocalState q) :=
              ⟨⟨begun, rfl⟩, hm⟩
            by_cases he : e = root
            · rw [if_pos ⟨hm, he⟩, if_pos ⟨hg, he⟩]
            · rw [if_neg (fun h => he h.2), if_neg (fun h => he h.2)]
          · have hg : ¬ BankTrialProbabilityArmedGate
                (⟨B, .live begun⟩ : BankTrialLocalState q) := by
              intro h
              exact hm h.2
            rw [if_neg (fun h => hm h.1), if_neg (fun h => hg h.1)]
        rw [← hdelta]
        exact Nat.le_trans (hrow B e)
          (Nat.add_le_add_right hbase _)
    | recovery =>
        intro nextBegun hphase
        simp [bankTrialLocalNext] at hphase <;>
          (repeat' split at hphase) <;> cases hphase
    | won =>
        intro nextBegun hphase
        simp [bankTrialLocalNext] at hphase
    | lost =>
        intro nextBegun hphase
        simp [bankTrialLocalNext] at hphase

/-- Full chronological induction of the carry invariant, under
the explicit all-row obligation. Unlike the original
numeric-only step, this transports the stronger IR credit. -/
theorem bankTrialLiveCarryAllWordsOfRawRows {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hrow : BankTrialLiveCarryRawRowBound (q := q) ring root) :
    ∀ (word : List (Fin n)) (z : BankTrialLocalState q)
      (heads : Nat),
      BankTrialLiveCarryLedger z heads →
      BankTrialLiveCarryLedger
        (bankTrialLocalRun ring root word z)
        (heads + bankTrialLiveHeadCount ring root word z) := by
  classical
  intro word
  induction word with
  | nil =>
      intro z heads hledger
      simpa [bankTrialLocalRun, bankTrialLiveHeadCount] using hledger
  | cons e tail ih =>
      intro z heads hledger
      have hnext := bankTrialLiveCarryRowStepOfRaw
        ring root hrow z heads e hledger
      have hrest := ih (bankTrialLocalNext ring root z e)
        (heads + (if BankTrialProbabilityArmedGate z ∧
          e = root then 1 else 0)) hnext
      change BankTrialLiveCarryLedger
        (bankTrialLocalRun ring root tail
          (bankTrialLocalNext ring root z e))
        (heads + ((if BankTrialProbabilityArmedGate z ∧
          e = root then 1 else 0) +
          bankTrialLiveHeadCount ring root tail
            (bankTrialLocalNext ring root z e)))
      simpa only [Nat.add_assoc] using hrest

theorem bankTrialLiveCarryCleanWordsOfRawRows {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S)
    (hrow : BankTrialLiveCarryRawRowBound (q := q) ring root)
    (word : List (Fin n)) :
    BankTrialLiveCarryLedger
      (bankTrialLocalRun ring root word (bankTrialLocalStart S))
      (bankTrialLiveHeadCount ring root word
        (bankTrialLocalStart S)) := by
  have h := bankTrialLiveCarryAllWordsOfRawRows
    ring root hrow word (bankTrialLocalStart S) 0
    (bankTrialLiveCarryLedgerStart S hclean)
  simpa using h

/-- UNPROVED independent comparison provenance:
a LIVE old CWAIT/CL1 acceptance must certify at least K units
of the carry-aware value at that cut. This does NOT follow
merely from Phi <= heads for arbitrary local observer scratch;
in particular a forged CL1 can be present with every bit zero.
For CLEAN-reachable states a true token genealogy/frozen
comparison lemma is still required. -/
def BankTrialLiveComparatorCredit {q : Nat}
    (z : BankTrialLocalState q) : Prop :=
  ∀ begun : Bool, z.phase = .live begun →
    (z.bank.fields ⟨0, by omega⟩).1 = .CWAIT →
    (z.bank.fields
      ⟨1, by change 1 < (compileAdvice q).s + 11 + 1; omega⟩).2.2.1 =
        .CL1 →
    (compileAdvice q).K ≤ bankTrialLiveCarryValue z.bank

theorem bankTrialLiveComparatorCreditStart {q : Nat}
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S) :
    BankTrialLiveComparatorCredit (bankTrialLocalStart S) := by
  intro begun _ hm _
  change (S.fields ⟨0, by omega⟩).1 = .CWAIT at hm
  rw [hclean.2.1] at hm
  cases hm

/-- Numeric carry ledger plus independently authenticated
comparison provenance implies BOTH original LIVE clauses. -/
theorem bankTrialLiveHeadCountOfCarryComparator {q : Nat}
    (z : BankTrialLocalState q) (heads : Nat)
    (hledger : BankTrialLiveCarryLedger z heads)
    (hcmp : BankTrialLiveComparatorCredit z) :
    BankTrialLiveHeadCount z heads := by
  constructor
  · intro begun hlive
    exact Nat.le_trans (bankTrialLiveBinaryLeCarry z.bank)
      (hledger begun hlive)
  · intro begun hlive hm ht
    exact Nat.le_trans (hcmp begun hlive hm ht)
      (hledger begun hlive)

/-- Conditional all-prefix strengthening of the earlier original
head-count invariant. Comparison credit must be provided for
each genuine observer prefix; the raw numeric row proof alone
cannot supply it. -/
theorem bankTrialLiveHeadCountWordsOfCarryComparator {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S)
    (hrow : BankTrialLiveCarryRawRowBound (q := q) ring root)
    (hcmp : ∀ word : List (Fin n),
      BankTrialLiveComparatorCredit
        (bankTrialLocalRun ring root word (bankTrialLocalStart S)))
    (word : List (Fin n)) :
    BankTrialLiveHeadCount
      (bankTrialLocalRun ring root word (bankTrialLocalStart S))
      (bankTrialLiveHeadCount ring root word
        (bankTrialLocalStart S)) := by
  exact bankTrialLiveHeadCountOfCarryComparator
    (bankTrialLocalRun ring root word (bankTrialLocalStart S))
    (bankTrialLiveHeadCount ring root word
      (bankTrialLocalStart S))
    (bankTrialLiveCarryCleanWordsOfRawRows
      ring root S hclean hrow word)
    (hcmp word)

/-- The earlier named Step follows from the stronger all-prefix
carry and comparison obligations. The old Step premise is not
strong enough to reconstruct in-flight IR credit by itself. -/
theorem bankTrialLiveHeadCountStepOfCarryComparator {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S)
    (hrow : BankTrialLiveCarryRawRowBound (q := q) ring root)
    (hcmp : ∀ word : List (Fin n),
      BankTrialLiveComparatorCredit
        (bankTrialLocalRun ring root word (bankTrialLocalStart S))) :
    BankTrialLiveHeadCountStep ring root S := by
  intro pre e _
  exact bankTrialLiveHeadCountWordsOfCarryComparator
    ring root S hclean hrow hcmp (pre ++ [e])

/-- The HEAD census is additive across an arbitrary chronological
cut. This counts OLD gates correctly on the suffix's actual state. -/
theorem bankTrialLiveHeadCountAppend {n q : Nat}
    (ring : DirectedRing n) (root : Fin n) :
    ∀ (pre suffix : List (Fin n)) (z : BankTrialLocalState q),
      bankTrialLiveHeadCount ring root (pre ++ suffix) z =
        bankTrialLiveHeadCount ring root pre z +
          bankTrialLiveHeadCount ring root suffix
            (bankTrialLocalRun ring root pre z) := by
  classical
  intro pre
  induction pre with
  | nil =>
      intro suffix z
      simp [bankTrialLiveHeadCount, bankTrialLocalRun]
  | cons e pre ih =>
      intro suffix z
      change
        (if BankTrialProbabilityArmedGate z ∧ e = root then 1 else 0) +
          bankTrialLiveHeadCount ring root (pre ++ suffix)
            (bankTrialLocalNext ring root z e) =
        ((if BankTrialProbabilityArmedGate z ∧ e = root then 1 else 0) +
          bankTrialLiveHeadCount ring root pre
            (bankTrialLocalNext ring root z e)) +
          bankTrialLiveHeadCount ring root suffix
            (bankTrialLocalRun ring root pre
              (bankTrialLocalNext ring root z e))
      rw [ih]
      omega

/-- UNPROVED first-WON predecessor trace, explicitly separate
from numeric accounting: recovery cannot win and a genuine first
LIVE win must use the OLD CWAIT/CL1 root guard. -/
def BankTrialLiveWinGuardTrace {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b) : Prop :=
  ∀ word : List (Fin n),
    (bankTrialLocalRun ring root word
      (bankTrialLocalStart S)).phase = .won →
    ∃ (pre suffix : List (Fin n))
      (B : GrantBankReference.BankLocalReference
        (compileAdvice q).b) (begun : Bool),
      word = pre ++ root :: suffix ∧
      bankTrialLocalRun ring root pre (bankTrialLocalStart S) =
        ⟨B, .live begun⟩ ∧
      (B.fields ⟨0, by omega⟩).1 = .CWAIT ∧
      (B.fields
        ⟨1, by change 1 < (compileAdvice q).s + 11 + 1; omega⟩).2.2.1 =
          .CL1

/-- Conditional transfer to the earlier winning ledger.
NoArmedIncoming on winning words is another distinct necessary
authentication obligation; neither it nor the trace is obtained
from the numeric carry inequality. -/
theorem bankTrialLiveWinningLedgerOfCarryTrace {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hrow : BankTrialLiveCarryRawRowBound (q := q) ring root)
    (hcmp : ∀ word : List (Fin n),
      BankTrialLiveComparatorCredit
        (bankTrialLocalRun ring root word (bankTrialLocalStart S)))
    (htrace : BankTrialLiveWinGuardTrace ring root S)
    (hno : ∀ word : List (Fin n),
      (bankTrialLocalRun ring root word
        (bankTrialLocalStart S)).phase = .won →
      BankTrialNoArmedIncoming ring root word
        (bankTrialLocalStart S)) :
    BankTrialLiveWinningLedger ring root S := by
  intro _ _ hclean word hw
  obtain ⟨pre, suffix, B, begun, hword, hpre, hm, ht⟩ :=
    htrace word hw
  have hprefix := bankTrialLiveHeadCountWordsOfCarryComparator
    ring root S hclean hrow hcmp pre
  rw [hpre] at hprefix
  have hK :
      (compileAdvice q).K ≤
        bankTrialLiveHeadCount ring root pre
          (bankTrialLocalStart S) :=
    hprefix.2 begun rfl hm ht
  have hmono :
      bankTrialLiveHeadCount ring root pre
          (bankTrialLocalStart S) ≤
        bankTrialLiveHeadCount ring root word
          (bankTrialLocalStart S) := by
    rw [hword, bankTrialLiveHeadCountAppend]
    omega
  exact ⟨Nat.le_trans hK hmono, hno word hw⟩

end L3

/-!
Structural carry-row audit.
The five pointwise
selector theorems below are exact compositions of existing
BankTrialLocal field equations. The complete List.ofFn-sum
assembly of BankTrialLiveCarryRawRowBound is NOT asserted.
-/

namespace L3

open Classical
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

set_option autoImplicit false
set_option Elab.async false

/-- An already latched local BANK reference is a full frame,
including every protected bit and token, on every edge. -/
theorem bankTrialLiveCarryLatchedRawFrame {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hlatch : B.success = true) :
    GrantBankReference.bankLocalReferenceStepClamped
      ring root B e = B := by
  classical
  simp [GrantBankReference.bankLocalReferenceStepClamped, hlatch]

theorem bankTrialLiveCarryLatchedValue {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hlatch : B.success = true) :
    bankTrialLiveCarryValue
      (GrantBankReference.bankLocalReferenceStepClamped
        ring root B e) = bankTrialLiveCarryValue B := by
  rw [bankTrialLiveCarryLatchedRawFrame ring root e B hlatch]

/-- The selector's FIRST branch, lifted from the field expression
to the actual stopped, clamped reference. -/
theorem bankTrialLiveCarrySourceSelected {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hs : Counter.Support q ring root e)
    (hf : B.success = false)
    (i : Fin ((compileAdvice q).b + 1))
    (hx : i.val < (compileAdvice q).b ∧
      e = Counter.site ring root i.val) :
    (GrantBankReference.bankLocalReferenceStepClamped
      ring root B e).fields i =
    GrantBankReference.bankLocalReferenceClampedQuad q
      ((GrantBankReference.bankLocalReferenceInternalPair q B
        ⟨i.val, hx.1⟩).1) := by
  rw [bankTrialLocalStepField ring root e B hs hf i]
  exact bankTrialLocalSelectedSource ring root e B i hx

/-- The responder branch requires failure of the earlier source
guard, even if the physical ring is short. -/
theorem bankTrialLiveCarryResponderSelected {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hs : Counter.Support q ring root e)
    (hf : B.success = false)
    (i : Fin ((compileAdvice q).b + 1))
    (hx : ¬ (i.val < (compileAdvice q).b ∧
      e = Counter.site ring root i.val))
    (hy : 0 < i.val ∧
      e = Counter.site ring root (i.val - 1)) :
    (GrantBankReference.bankLocalReferenceStepClamped
      ring root B e).fields i =
    GrantBankReference.bankLocalReferenceClampedQuad q
      ((GrantBankReference.bankLocalReferenceInternalPair q B
        ⟨i.val - 1, by omega⟩).2) := by
  rw [bankTrialLocalStepField ring root e B hs hf i]
  exact bankTrialLocalSelectedResponder ring root e B i hx hy

/-- Top boundary is a separate unary source row after the first
two selectors have failed. -/
theorem bankTrialLiveCarryTopSelected {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hs : Counter.Support q ring root e)
    (hf : B.success = false)
    (i : Fin ((compileAdvice q).b + 1))
    (hx : ¬ (i.val < (compileAdvice q).b ∧
      e = Counter.site ring root i.val))
    (hy : ¬ (0 < i.val ∧
      e = Counter.site ring root (i.val - 1)))
    (ht : i.val = (compileAdvice q).b ∧
      e = Counter.site ring root (compileAdvice q).b) :
    (GrantBankReference.bankLocalReferenceStepClamped
      ring root B e).fields i =
    GrantBankReference.bankLocalReferenceClampedQuad q
      (GrantBankReference.topBoundaryBankMap
        (GrantBankReference.bankLocalReferenceCell B i)) := by
  rw [bankTrialLocalStepField ring root e B hs hf i]
  exact bankTrialLocalSelectedTop ring root e B i hx hy ht

/-- Incoming-root is the fourth guard; it touches the root slot
(which contributes no term to Phi) but may share a scheduler
letter with a top boundary if the ring is too short. -/
theorem bankTrialLiveCarryIncomingSelected {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hs : Counter.Support q ring root e)
    (hf : B.success = false)
    (i : Fin ((compileAdvice q).b + 1))
    (hx : ¬ (i.val < (compileAdvice q).b ∧
      e = Counter.site ring root i.val))
    (hy : ¬ (0 < i.val ∧
      e = Counter.site ring root (i.val - 1)))
    (ht : ¬ (i.val = (compileAdvice q).b ∧
      e = Counter.site ring root (compileAdvice q).b))
    (hr : i.val = 0 ∧ ring.rightNeighbor e = root) :
    (GrantBankReference.bankLocalReferenceStepClamped
      ring root B e).fields i =
    GrantBankReference.bankLocalReferenceClampedQuad q
      (GrantBankReference.incomingRootBankMap
        (GrantBankReference.bankLocalReferenceCell B i)) := by
  rw [bankTrialLocalStepField ring root e B hs hf i]
  exact bankTrialLocalSelectedIncoming ring root e B i
    hx hy ht hr

/-- Frame is justified only when ALL four selector guards fail.
In particular "nonroot scheduler letter" does not imply frame. -/
theorem bankTrialLiveCarryUnselectedField {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hs : Counter.Support q ring root e)
    (hf : B.success = false)
    (i : Fin ((compileAdvice q).b + 1))
    (hx : ¬ (i.val < (compileAdvice q).b ∧
      e = Counter.site ring root i.val))
    (hy : ¬ (0 < i.val ∧
      e = Counter.site ring root (i.val - 1)))
    (ht : ¬ (i.val = (compileAdvice q).b ∧
      e = Counter.site ring root (compileAdvice q).b))
    (hr : ¬ (i.val = 0 ∧ ring.rightNeighbor e = root)) :
    (GrantBankReference.bankLocalReferenceStepClamped
      ring root B e).fields i = B.fields i := by
  rw [bankTrialLocalStepField ring root e B hs hf i]
  exact bankTrialLocalSelectedFrame ring root e B i
    hx hy ht hr

/-- On an unsupported edge the complete clamped BANK reference,
not merely its scalar potential, is unchanged. -/
theorem bankTrialLiveCarryUnsupportedRawFrame {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hout : ¬ Counter.Support q ring root e) :
    GrantBankReference.bankLocalReferenceStepClamped
      ring root B e = B := by
  exact bankTrialLocalStepOutside ring root e B hout

/-- Top IR erasure is nonincreasing in Phi, including physical
lease clamping. Only the touched token is case-split. -/
theorem bankTrialLiveTopClampedPotential
    (q j : Nat) (z : BankCell) :
    bankTrialLiveSlotPotential j
      (GrantBankReference.bankLocalReferenceClampedQuad q
        (GrantBankReference.topBoundaryBankMap z)).2.1
      (GrantBankReference.bankLocalReferenceClampedQuad q
        (GrantBankReference.topBoundaryBankMap z)).2.2.1 ≤
    bankTrialLiveSlotPotential j z.bit z.tok := by
  have hc := bankTrialLiveClampBitToken q
    (GrantBankReference.topBoundaryBankMap z)
  rw [hc.1, hc.2]
  by_cases hir : z.tok = .IR
  · simp [GrantBankReference.topBoundaryBankMap,
      bankTrialLiveSlotPotential, hir] <;> omega
  · simp [GrantBankReference.topBoundaryBankMap,
      bankTrialLiveSlotPotential, hir] <;> omega

/-!
The following two local-pair bounds are preserved as named,
explicitly UNPROVED Props. The old nested token/bit/mode case
expansions exceeded the time budget; no claim of their
truth is made here. The global sum theorem remains open.
-/

/-- OPEN Prop for the exact two-cell root BANK owner. An ARMED
root should pay at most one unit, but the whole bankPair row
inequality is deliberately not asserted as a theorem. -/
def bankTrialLiveRootPairPotentialBound
    (b : Nat) (theta : Nat → Bool)
    (x y : BankCell) : Prop :=
  1 < b →
  x.role = 0 →
  y.role = 1 →
  x.grant = false →
  bankTrialLiveSlotPotential 0
      (bankPair x y 1 b theta).2.bit
      (bankPair x y 1 b theta).2.tok ≤
    bankTrialLiveSlotPotential 0 y.bit y.tok +
      (if x.mode = .ARMED then 1 else 0)

/-- OPEN Prop for the nonroot BANK pair. An in-flight IR should
pay for the next bit flip; collision and top cases still require
a cheap symbolic owner proof, not a combinatorial simp blast. -/
def bankTrialLiveNonrootPairPotentialBound
    (j b : Nat) (theta : Nat → Bool)
    (x y : BankCell) : Prop :=
  j + 2 ≤ b →
  x.role = j + 1 →
  y.role = j + 2 →
  bankTrialLiveSlotPotential j
      (bankPair x y (j + 2) b theta).1.bit
      (bankPair x y (j + 2) b theta).1.tok +
    bankTrialLiveSlotPotential (j + 1)
      (bankPair x y (j + 2) b theta).2.bit
      (bankPair x y (j + 2) b theta).2.tok ≤
  bankTrialLiveSlotPotential j x.bit x.tok +
    bankTrialLiveSlotPotential (j + 1) y.bit y.tok

/-- The top comparison turn is the single primitive generator
of a new CL1 token from a CR1 token for b>=2. A leftward CL1
forward row merely propagates an existing CL1; the root consumes
CL1 on its OLD CWAIT success guard. -/
theorem bankTrialLiveTopCRCreatesCL
    (b : Nat) (theta : Nat → Bool)
    (x y : BankCell)
    (hb : 2 ≤ b)
    (hx : x.role = b - 1) (hy : y.role = b)
    (htx : x.tok = .E) (hty : y.tok = .CR1) :
    (bankPair x y b b theta).1.tok = .CL1 ∧
    (bankPair x y b b theta).2.tok = .E := by
  have hpos : 1 ≤ b - 1 := by omega
  have hlt : b - 1 < b := by omega
  have hsucc : b - 1 + 1 = b := by omega
  have hbpos : 0 < b := by omega
  have hb0 : b ≠ 0 := by omega
  have hb10 : b - 1 ≠ 0 := by omega
  have hbne : b - 1 ≠ b := by omega
  simp [bankPair, hx, hy, htx, hty, hpos, hlt, hsucc, hbpos,
    hb0, hb10, hbne, Id.run_pure, Id.run_bind]

/-- Binary value of the exact literal theta word (low b bits
of the K comparator). Its equality to K requires K < 2^b,
which is not smuggled into this definition. -/
def bankTrialLiveThetaBinary (q : Nat) : Nat :=
  (List.ofFn (fun j : Fin (compileAdvice q).b =>
    if (compileAdvice q).theta j.val then 2 ^ j.val else 0)).sum

/-- If all digits match theta, their actual binary value is
the weight of theta; the possibly nonzero IR credits can only
increase the carry-aware Phi. -/
theorem bankTrialLiveThetaMatchValue {q : Nat}
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hmatch : ∀ j : Fin (compileAdvice q).b,
      (B.fields ⟨j.val + 1, by omega⟩).2.1 =
        (compileAdvice q).theta j.val) :
    bankTrialLiveThetaBinary q ≤ bankTrialLiveCarryValue B := by
  have hbinary :
      bankTrialLiveBinaryValue B = bankTrialLiveThetaBinary q := by
    unfold bankTrialLiveBinaryValue bankTrialLiveThetaBinary
    apply ofFn_sum_eq
    intro j
    rw [hmatch j]
  rw [← hbinary]
  exact bankTrialLiveBinaryLeCarry B

/-- A token-location genealogy in the exact protected fields:
CR1 at digit j+1 certifies that *all bits through that digit*
were checked and equal theta, whereas CL1 at any digit certifies
that the entire b-bit word was checked. These assertions require
writer/worker exclusion during CR/CL travel for one-edge closure.
Their arbitrary-snapshot form is intentionally NOT asserted. -/
def BankTrialLiveComparisonGenealogy {q : Nat}
    (z : BankTrialLocalState q) : Prop :=
  ∀ begun : Bool, z.phase = .live begun →
    (∀ j : Fin (compileAdvice q).b,
      (z.bank.fields ⟨j.val + 1, by omega⟩).2.2.1 = .CR1 →
      ∀ k : Fin (compileAdvice q).b, k.val ≤ j.val →
        (z.bank.fields ⟨k.val + 1, by omega⟩).2.1 =
          (compileAdvice q).theta k.val) ∧
    (∀ j : Fin (compileAdvice q).b,
      (z.bank.fields ⟨j.val + 1, by omega⟩).2.2.1 = .CL1 →
      ∀ k : Fin (compileAdvice q).b,
        (z.bank.fields ⟨k.val + 1, by omega⟩).2.1 =
          (compileAdvice q).theta k.val)

/-- No CR1 or CL1 is initially present in the CLEAN word. -/
theorem bankTrialLiveComparisonGenealogyStart {q : Nat}
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S) :
    BankTrialLiveComparisonGenealogy (bankTrialLocalStart S) := by
  intro begun _
  constructor
  · intro j ht
    have he : (S.fields ⟨j.val + 1, by omega⟩).2.2.1 = .E :=
      (hclean.2.2.1 (j.val + 1)
        (by omega : 1 ≤ j.val + 1)
        (by omega : j.val + 1 ≤ (compileAdvice q).b)).2
    cases (he.symm.trans ht)
  · intro j ht
    have he : (S.fields ⟨j.val + 1, by omega⟩).2.2.1 = .E :=
      (hclean.2.2.1 (j.val + 1)
        (by omega : 1 ≤ j.val + 1)
        (by omega : j.val + 1 ≤ (compileAdvice q).b)).2
    cases (he.symm.trans ht)

/-- An authenticated CL1 at digit one supplies the actual
comparator credit, provided the low-b theta value covers K.
This is the formal bridge from token genealogy to the
separate comparator predicate, not from Phi<=heads alone. -/
theorem bankTrialLiveComparatorCreditOfGenealogy {q : Nat}
    (z : BankTrialLocalState q)
    (hgenealogy : BankTrialLiveComparisonGenealogy z)
    (htheta : (compileAdvice q).K ≤ bankTrialLiveThetaBinary q) :
    BankTrialLiveComparatorCredit z := by
  intro begun hlive _ ht
  have hbits : ∀ k : Fin (compileAdvice q).b,
      (z.bank.fields ⟨k.val + 1, by omega⟩).2.1 =
        (compileAdvice q).theta k.val :=
    (hgenealogy begun hlive).2
      ⟨0, by change 0 < (compileAdvice q).s + 11; omega⟩ ht
  exact Nat.le_trans htheta
    (bankTrialLiveThetaMatchValue z.bank hbits)

/-- The remaining comparison-trace row induction: CR1 advances
only if the destination equals theta; top CR1 turns into CL1;
CL1 travels left without new digit writers; loss/recovery
removes the LIVE obligation. This is an OPEN Prop, not a theorem.
The numeric carry-row invariant alone cannot establish it. -/
def BankTrialLiveComparisonGenealogyStep {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b) : Prop :=
  ∀ (pre : List (Fin n)) (e : Fin n),
    BankTrialLiveComparisonGenealogy
      (bankTrialLocalRun ring root pre (bankTrialLocalStart S)) →
    BankTrialLiveComparisonGenealogy
      (bankTrialLocalRun ring root (pre ++ [e])
        (bankTrialLocalStart S))

/-- Conditional prefix induction; the proof deliberately makes
the remaining stateful genealogy step explicit. -/
theorem bankTrialLiveComparisonGenealogyWordsOfStep {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S)
    (hstep : BankTrialLiveComparisonGenealogyStep ring root S) :
    ∀ word : List (Fin n),
      BankTrialLiveComparisonGenealogy
        (bankTrialLocalRun ring root word (bankTrialLocalStart S)) := by
  have hreverse : ∀ rev : List (Fin n),
      BankTrialLiveComparisonGenealogy
        (bankTrialLocalRun ring root rev.reverse
          (bankTrialLocalStart S)) := by
    intro rev
    induction rev with
    | nil =>
        exact bankTrialLiveComparisonGenealogyStart S hclean
    | cons e rev ih =>
        rw [List.reverse_cons]
        exact hstep rev.reverse e ih
  intro word
  have h := hreverse word.reverse
  simpa only [List.reverse_reverse] using h

/-- This combines a full CLEAN-reachable comparison genealogy
with theta's arithmetic coverage. A proof of the raw all-row
potential bound alone is insufficient to discharge it. -/
theorem bankTrialLiveComparatorCreditWordsOfGenealogy {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S)
    (hstep : BankTrialLiveComparisonGenealogyStep ring root S)
    (htheta : (compileAdvice q).K ≤ bankTrialLiveThetaBinary q) :
    ∀ word : List (Fin n),
      BankTrialLiveComparatorCredit
        (bankTrialLocalRun ring root word (bankTrialLocalStart S)) := by
  intro word
  exact bankTrialLiveComparatorCreditOfGenealogy
    (bankTrialLocalRun ring root word (bankTrialLocalStart S))
    (bankTrialLiveComparisonGenealogyWordsOfStep
      ring root S hclean hstep word) htheta

end L3

/-!
LIVE comparison-wave lock and adversarial counterexample.

CWAIT blocks a *new* root ARMED head, but does not erase
old IR, RR, or RL elsewhere. Therefore the
CR1/CL1 genealogy is not inductive on arbitrary LIVE
scratch; CLEAN reachability needs a single-worker stage lock.
-/

namespace L3

set_option autoImplicit false
set_option Elab.async false

def bankTrialLiveWaveToken {q : Nat}
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (j : Fin (compileAdvice q).b) : BTok :=
  (B.fields ⟨j.val + 1, by omega⟩).2.2.1

def bankTrialLiveWaveBit {q : Nat}
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (j : Fin (compileAdvice q).b) : Bool :=
  (B.fields ⟨j.val + 1, by omega⟩).2.1

def bankTrialLiveWaveRootMode {q : Nat}
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b) : Mode :=
  (B.fields ⟨0, by omega⟩).1

def BankTrialLiveComparisonToken (t : BTok) : Prop :=
  t = .CR0 ∨ t = .CR1 ∨ t = .CL0 ∨ t = .CL1

/-- Stage-indexed single worker plus exact checked-bit ancestry.
CWAIT allows only CR/CL, IWAIT only IR/AL, RWAIT only
RR/RL, and ARMED/CSTART only E. An active CR1/CL1 is
unique and its root is CWAIT. This is strictly stronger
than the comparison-genealogy predicate. -/
structure BankTrialLiveWaveCertificate (q : Nat)
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b) : Prop where
  cwaitTokens :
    ∀ j : Fin (compileAdvice q).b,
      bankTrialLiveWaveRootMode B = .CWAIT →
      bankTrialLiveWaveToken B j = .E ∨
        BankTrialLiveComparisonToken (bankTrialLiveWaveToken B j)
  iwaitTokens :
    ∀ j : Fin (compileAdvice q).b,
      bankTrialLiveWaveRootMode B = .IWAIT →
      bankTrialLiveWaveToken B j = .E ∨
        bankTrialLiveWaveToken B j = .IR ∨
        bankTrialLiveWaveToken B j = .AL
  headClear :
    ∀ j : Fin (compileAdvice q).b,
      (bankTrialLiveWaveRootMode B = .ARMED ∨
        bankTrialLiveWaveRootMode B = .CSTART) →
      bankTrialLiveWaveToken B j = .E
  resetTokens :
    ∀ j : Fin (compileAdvice q).b,
      bankTrialLiveWaveRootMode B = .RWAIT →
      bankTrialLiveWaveToken B j = .E ∨
        bankTrialLiveWaveToken B j = .RR ∨
        bankTrialLiveWaveToken B j = .RL
  uniqueWorker :
    ∀ i j : Fin (compileAdvice q).b,
      bankTrialLiveWaveToken B i ≠ .E →
      bankTrialLiveWaveToken B j ≠ .E → i = j
  comparisonMode :
    ∀ j : Fin (compileAdvice q).b,
      (bankTrialLiveWaveToken B j = .CR1 ∨
        bankTrialLiveWaveToken B j = .CL1) →
      bankTrialLiveWaveRootMode B = .CWAIT
  crPrefix :
    ∀ j : Fin (compileAdvice q).b,
      bankTrialLiveWaveToken B j = .CR1 →
      ∀ k : Fin (compileAdvice q).b, k.val ≤ j.val →
        bankTrialLiveWaveBit B k =
          (compileAdvice q).theta k.val
  clAll :
    ∀ j : Fin (compileAdvice q).b,
      bankTrialLiveWaveToken B j = .CL1 →
      ∀ k : Fin (compileAdvice q).b,
        bankTrialLiveWaveBit B k =
          (compileAdvice q).theta k.val

def BankTrialLiveLockedGenealogy {q : Nat}
    (z : BankTrialLocalState q) : Prop :=
  ∀ begun : Bool, z.phase = .live begun →
    BankTrialLiveWaveCertificate q z.bank

/-- CLEAN gives the empty-worker locked base, including
both comparison directions' (vacuous) genealogy. -/
theorem bankTrialLiveWaveCertificateClean {q : Nat}
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S) :
    BankTrialLiveWaveCertificate q S := by
  have hempty : ∀ j : Fin (compileAdvice q).b,
      bankTrialLiveWaveToken S j = .E := by
    intro j
    exact (hclean.2.2.1 (j.val + 1)
      (by omega : 1 ≤ j.val + 1)
      (by omega : j.val + 1 ≤ (compileAdvice q).b)).2
  have hmode : bankTrialLiveWaveRootMode S = .ARMED :=
    hclean.2.1
  refine {
    cwaitTokens := ?_,
    iwaitTokens := ?_,
    headClear := ?_,
    resetTokens := ?_,
    uniqueWorker := ?_,
    comparisonMode := ?_,
    crPrefix := ?_,
    clAll := ?_
  }
  · intro j hm
    rw [hmode] at hm
    cases hm
  · intro j hm
    rw [hmode] at hm
    cases hm
  · intro j _
    exact hempty j
  · intro j hm
    rw [hmode] at hm
    cases hm
  · intro i j hi _
    rw [hempty i] at hi
    exact False.elim (hi rfl)
  · intro j ht
    rcases ht with ht | ht
    · rw [hempty j] at ht
      cases ht
    · rw [hempty j] at ht
      cases ht
  · intro j ht
    rw [hempty j] at ht
    cases ht
  · intro j ht
    rw [hempty j] at ht
    cases ht

theorem bankTrialLiveLockedGenealogyStart {q : Nat}
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S) :
    BankTrialLiveLockedGenealogy (bankTrialLocalStart S) := by
  intro begun _
  exact bankTrialLiveWaveCertificateClean S hclean

/-- The lock implies exactly the original
CR1-prefix and CL1-whole-word predicate. -/
theorem bankTrialLiveGenealogyOfLocked {q : Nat}
    (z : BankTrialLocalState q)
    (hlock : BankTrialLiveLockedGenealogy z) :
    BankTrialLiveComparisonGenealogy z := by
  intro begun hlive
  have hc := hlock begun hlive
  exact ⟨hc.crPrefix, hc.clAll⟩

theorem bankTrialLiveWaveCWaitNoWriters {q : Nat}
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hc : BankTrialLiveWaveCertificate q B)
    (hm : bankTrialLiveWaveRootMode B = .CWAIT)
    (j : Fin (compileAdvice q).b) :
    bankTrialLiveWaveToken B j ≠ .IR ∧
    bankTrialLiveWaveToken B j ≠ .RR ∧
    bankTrialLiveWaveToken B j ≠ .RL := by
  rcases hc.cwaitTokens j hm with he | hcomp
  · rw [he]
    simp
  · rcases hcomp with ht | ht | ht | ht <;>
      rw [ht] <;> simp

theorem bankTrialLiveWaveWorkerUnique {q : Nat}
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hc : BankTrialLiveWaveCertificate q B)
    (i j : Fin (compileAdvice q).b)
    (hi : bankTrialLiveWaveToken B i ≠ .E)
    (hj : bankTrialLiveWaveToken B j ≠ .E) :
    i = j :=
  hc.uniqueWorker i j hi hj

/-- Literal Base.bankPair comparison advance; only two token
fields are constrained and no whole-state enumeration occurs. -/
theorem bankTrialLiveRawCRForward
    (b : Nat) (theta : Nat → Bool)
    (x y : BankCell)
    (hx : 1 ≤ x.role) (hlt : x.role < b)
    (hy : y.role = x.role + 1)
    (htx : x.tok = .CR1) (hty : y.tok = .E) :
    (bankPair x y y.role b theta).1.tok = .E ∧
    (bankPair x y y.role b theta).2.tok =
      (if y.bit == theta (y.role - 1) then .CR1 else .CR0) ∧
    (bankPair x y y.role b theta).1.bit = x.bit ∧
    (bankPair x y y.role b theta).2.bit = y.bit := by
  have hxn : x.role ≠ 0 := by omega
  have hyn : y.role ≠ 0 := by omega
  have hxnotTop : x.role ≠ b := by omega
  have hxb : x.role ≤ b := by omega
  have hyb : y.role ≤ b := by omega
  have hypos : 1 ≤ y.role := by omega
  simp [bankPair, hx, hlt, hy, htx, hty,
    hxn, hyn, hxnotTop, hxb, hyb, hypos,
    Id.run_pure, Id.run_bind]

/-- Literal CL1 return: token moves one slot left without
touching the corresponding two protected bits. -/
theorem bankTrialLiveRawCLReturn
    (b : Nat) (theta : Nat → Bool)
    (x y : BankCell)
    (hx : 1 ≤ x.role) (hlt : x.role < b)
    (hy : y.role = x.role + 1)
    (htx : x.tok = .E) (hty : y.tok = .CL1) :
    (bankPair x y y.role b theta).1.tok = .CL1 ∧
    (bankPair x y y.role b theta).2.tok = .E ∧
    (bankPair x y y.role b theta).1.bit = x.bit ∧
    (bankPair x y y.role b theta).2.bit = y.bit := by
  have hxn : x.role ≠ 0 := by omega
  have hyn : y.role ≠ 0 := by omega
  have hxnotTop : x.role ≠ b := by omega
  have hxb : x.role ≤ b := by omega
  have hyb : y.role ≤ b := by omega
  have hypos : 1 ≤ y.role := by omega
  have hnb : ¬ b < x.role + 1 := by omega
  simp [bankPair, hx, hlt, hy, htx, hty,
    hxn, hyn, hxnotTop, hxb, hyb, hypos, hnb,
    Id.run_pure, Id.run_bind]

/-- Outgoing root in CWAIT does not create a fresh digit bit
write. This cannot erase an old IR at an unrelated site. -/
theorem bankTrialLiveRawCWaitBitFrame
    (b : Nat) (theta : Nat → Bool)
    (x y : BankCell)
    (hb : 1 < b)
    (hx : x.role = 0) (hy : y.role = 1)
    (hg : x.grant = false) (hm : x.mode = .CWAIT) :
    (bankPair x y 1 b theta).2.bit = y.bit := by
  have hbon : 1 ≤ b := by omega
  have hnot : b ≠ 1 := by omega
  simp [bankPair, hx, hy, hg, hm, hbon, hnot,
    isRetTok, isWaitMode, Id.run_pure, Id.run_bind] <;>
    (repeat' split) <;> rfl

theorem bankTrialLiveTopMapNoIR
    (z : BankCell) (hno : z.tok ≠ .IR) :
    (GrantBankReference.topBoundaryBankMap z).tok = z.tok := by
  simp [GrantBankReference.topBoundaryBankMap, hno]

theorem bankTrialLiveIncomingCWaitMode
    (z : BankCell)
    (hm : z.mode = .CWAIT) (hl : 1 < z.lease) :
    (GrantBankReference.incomingRootBankMap z).mode = .CWAIT := by
  simp [GrantBankReference.incomingRootBankMap,
    hm, hl, isWaitMode]

/-- Old internal IR flips a destination bit even when some
other CR1 still advertises that bit as checked. -/
theorem bankTrialLiveRawIRFlipBit
    (b : Nat) (theta : Nat → Bool)
    (x y : BankCell)
    (hx : 1 ≤ x.role) (hlt : x.role < b)
    (hy : y.role = x.role + 1)
    (htx : x.tok = .IR) (hty : y.tok = .E) :
    (bankPair x y y.role b theta).2.bit = !y.bit := by
  have hxn : x.role ≠ 0 := by omega
  have hyn : y.role ≠ 0 := by omega
  have hxnotTop : x.role ≠ b := by omega
  have hxb : x.role ≤ b := by omega
  have hyb : y.role ≤ b := by omega
  have hypos : 1 ≤ y.role := by omega
  simp [bankPair, hx, hlt, hy, htx, hty,
    hxn, hyn, hxnotTop, hxb, hyb, hypos,
    Id.run_pure, Id.run_bind]

theorem bankTrialLiveRawIRBreaksMatch
    (b : Nat) (theta : Nat → Bool)
    (x y : BankCell)
    (hx : 1 ≤ x.role) (hlt : x.role < b)
    (hy : y.role = x.role + 1)
    (htx : x.tok = .IR) (hty : y.tok = .E)
    (hmatch : y.bit = theta (y.role - 1)) :
    (bankPair x y y.role b theta).2.bit ≠
      theta (y.role - 1) := by
  rw [bankTrialLiveRawIRFlipBit b theta x y
    hx hlt hy htx hty, hmatch]
  cases hval : theta (y.role - 1) <;> simp

theorem bankTrialLiveCRPrefixExtend {q : Nat}
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (j : Fin (compileAdvice q).b)
    (hj : j.val + 1 < (compileAdvice q).b)
    (hprevious : ∀ k : Fin (compileAdvice q).b,
      k.val ≤ j.val →
      bankTrialLiveWaveBit B k = (compileAdvice q).theta k.val)
    (hnext :
      bankTrialLiveWaveBit B ⟨j.val + 1, hj⟩ =
        (compileAdvice q).theta (j.val + 1)) :
    ∀ k : Fin (compileAdvice q).b,
      k.val ≤ j.val + 1 →
      bankTrialLiveWaveBit B k =
        (compileAdvice q).theta k.val := by
  intro k hk
  by_cases heq : k.val = j.val + 1
  · have hindex : k = ⟨j.val + 1, hj⟩ := Fin.ext heq
    rw [hindex]
    exact hnext
  · exact hprevious k (by omega)

theorem bankTrialLiveTopPrefixIsFull {q : Nat}
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hprefix : ∀ k : Fin (compileAdvice q).b,
      k.val ≤ (compileAdvice q).b - 1 →
      bankTrialLiveWaveBit B k =
        (compileAdvice q).theta k.val) :
    ∀ k : Fin (compileAdvice q).b,
      bankTrialLiveWaveBit B k =
        (compileAdvice q).theta k.val := by
  intro k
  exact hprefix k (by have hk := k.isLt; omega)

/-- A single physical scheduler letter evaluated on the OLD
LIVE reference. This is the exact local edge-class obligation. -/
def BankTrialLiveWaveLiveEdgeRow {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n) : Prop :=
  ∀ (B : GrantBankReference.BankLocalReference
        (compileAdvice q).b) (begun : Bool),
    BankTrialLiveWaveCertificate q B →
    ∀ nextBegun : Bool,
      (bankTrialLocalNext ring root
        (⟨B, .live begun⟩ : BankTrialLocalState q) e).phase =
          .live nextBegun →
      BankTrialLiveWaveCertificate q
        (bankTrialLocalNext ring root
          (⟨B, .live begun⟩ : BankTrialLocalState q) e).bank

/-- Truly unsupported edges frame every protected digit. -/
theorem bankTrialLiveWaveLiveEdgeOutside {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (hout : ¬ Counter.Support q ring root e) :
    BankTrialLiveWaveLiveEdgeRow (q := q) ring root e := by
  intro B begun hcert nextBegun _
  change BankTrialLiveWaveCertificate q
    (bankTrialLocalNext ring root
      (⟨B, .live begun⟩ : BankTrialLocalState q) e).bank
  rw [bankTrialLiveOutsideBankFrame ring root e B begun hout]
  exact hcert

/-- Old latched success frames the whole stopped BANK record. -/
theorem bankTrialLiveWaveLiveEdgeLatched {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b) (begun : Bool)
    (hlatch : B.success = true)
    (hcert : BankTrialLiveWaveCertificate q B)
    (nextBegun : Bool)
    (hlive : (bankTrialLocalNext ring root
      (⟨B, .live begun⟩ : BankTrialLocalState q) e).phase =
        .live nextBegun) :
    BankTrialLiveWaveCertificate q
      (bankTrialLocalNext ring root
        (⟨B, .live begun⟩ : BankTrialLocalState q) e).bank := by
  have hbank := bankTrialLocalNextLiveBank
    ring root e B begun
  rw [hbank, bankTrialLiveCarryLatchedRawFrame
    ring root e B hlatch]
  exact hcert

/-!
The four supported-row closures below are OPEN Props.
The proof of their exact bankLocalReferenceStepClamped
geometry, no-alias and worker progress is not supplied here.
No unconditional G11 theorem is inferred from them.
-/
def BankTrialLiveWaveRootOutgoingRows {n q : Nat}
    (ring : DirectedRing n) (root : Fin n) : Prop :=
  BankTrialLiveWaveLiveEdgeRow (q := q) ring root root

def BankTrialLiveWaveInteriorRows {n q : Nat}
    (ring : DirectedRing n) (root : Fin n) : Prop :=
  ∀ j : Fin (compileAdvice q).b, 0 < j.val →
    BankTrialLiveWaveLiveEdgeRow (q := q) ring root
      (Counter.site ring root j.val)

def BankTrialLiveWaveTopRows {n q : Nat}
    (ring : DirectedRing n) (root : Fin n) : Prop :=
  BankTrialLiveWaveLiveEdgeRow (q := q) ring root
    (Counter.site ring root (compileAdvice q).b)

def BankTrialLiveWaveIncomingRows {n q : Nat}
    (ring : DirectedRing n) (root : Fin n) : Prop :=
  ∀ e : Fin n, ring.rightNeighbor e = root →
    BankTrialLiveWaveLiveEdgeRow (q := q) ring root e

/-- Exact root/interior/top/incoming/outside geometry,
conditional on the four genuine supported source rows. -/
theorem bankTrialLiveWaveRowsOfClasses {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hroot : BankTrialLiveWaveRootOutgoingRows (q := q) ring root)
    (hinterior : BankTrialLiveWaveInteriorRows (q := q) ring root)
    (htop : BankTrialLiveWaveTopRows (q := q) ring root)
    (hincoming : BankTrialLiveWaveIncomingRows (q := q) ring root) :
    ∀ e : Fin n,
      BankTrialLiveWaveLiveEdgeRow (q := q) ring root e := by
  intro e
  rcases Counter.resetTrialEdgeGeometry (q := q)
      ring root e with hsource | hin | hout
  · obtain ⟨j, hj, he⟩ := hsource
    by_cases htopj : j = (compileAdvice q).b
    · subst j
      rw [he]
      exact htop
    · by_cases hz : j = 0
      · subst j
        change e = root at he
        rw [he]
        exact hroot
      · have hjfin : j < (compileAdvice q).b := by omega
        rw [he]
        exact hinterior ⟨j, hjfin⟩ (Nat.pos_of_ne_zero hz)
  · exact hincoming e hin
  · have houtside : ¬ Counter.Support q ring root e := by
      intro hs
      rcases hs with hinc | ⟨j, hj, he⟩
      · have hp := (hout 0 (by omega)).2
        change ring.rightNeighbor e ≠ root at hp
        exact hp hinc
      · exact (hout j hj).1 he
    exact bankTrialLiveWaveLiveEdgeOutside ring root e houtside

theorem bankTrialLiveLockedNextOfRows {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (hrows : ∀ f : Fin n,
      BankTrialLiveWaveLiveEdgeRow (q := q) ring root f)
    (z : BankTrialLocalState q)
    (hlock : BankTrialLiveLockedGenealogy z) :
    BankTrialLiveLockedGenealogy
      (bankTrialLocalNext ring root z e) := by
  cases z with
  | mk B phase =>
    cases phase with
    | live begun =>
        intro nextBegun hnext
        exact hrows e B begun (hlock begun rfl)
          nextBegun hnext
    | recovery =>
        intro nextBegun hnext
        simp [bankTrialLocalNext] at hnext <;>
          (repeat' split at hnext) <;> cases hnext
    | won =>
        intro nextBegun hnext
        simp [bankTrialLocalNext] at hnext
    | lost =>
        intro nextBegun hnext
        simp [bankTrialLocalNext] at hnext

theorem bankTrialLiveLockedRunOfRows {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hrows : ∀ e : Fin n,
      BankTrialLiveWaveLiveEdgeRow (q := q) ring root e) :
    ∀ (word : List (Fin n)) (z : BankTrialLocalState q),
      BankTrialLiveLockedGenealogy z →
      BankTrialLiveLockedGenealogy
        (bankTrialLocalRun ring root word z) := by
  intro word
  induction word with
  | nil =>
      intro z hlock
      exact hlock
  | cons e es ih =>
      intro z hlock
      change BankTrialLiveLockedGenealogy
        (bankTrialLocalRun ring root es
          (bankTrialLocalNext ring root z e))
      exact ih _ (bankTrialLiveLockedNextOfRows
        ring root e hrows z hlock)

theorem bankTrialLiveGenealogyWordsOfWaveRows {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S)
    (hroot : BankTrialLiveWaveRootOutgoingRows (q := q) ring root)
    (hinterior : BankTrialLiveWaveInteriorRows (q := q) ring root)
    (htop : BankTrialLiveWaveTopRows (q := q) ring root)
    (hincoming : BankTrialLiveWaveIncomingRows (q := q) ring root)
    (word : List (Fin n)) :
    BankTrialLiveComparisonGenealogy
      (bankTrialLocalRun ring root word
        (bankTrialLocalStart S)) := by
  have hrows := bankTrialLiveWaveRowsOfClasses
    ring root hroot hinterior htop hincoming
  have hlock := bankTrialLiveLockedRunOfRows
    ring root hrows word (bankTrialLocalStart S)
    (bankTrialLiveLockedGenealogyStart S hclean)
  exact bankTrialLiveGenealogyOfLocked _ hlock

theorem bankTrialLiveComparatorCreditWordsOfWaveRows {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S)
    (hroot : BankTrialLiveWaveRootOutgoingRows (q := q) ring root)
    (hinterior : BankTrialLiveWaveInteriorRows (q := q) ring root)
    (htop : BankTrialLiveWaveTopRows (q := q) ring root)
    (hincoming : BankTrialLiveWaveIncomingRows (q := q) ring root)
    (htheta : (compileAdvice q).K ≤ bankTrialLiveThetaBinary q) :
    ∀ word : List (Fin n),
      BankTrialLiveComparatorCredit
        (bankTrialLocalRun ring root word
          (bankTrialLocalStart S)) := by
  intro word
  exact bankTrialLiveComparatorCreditOfGenealogy
    (bankTrialLocalRun ring root word (bankTrialLocalStart S))
    (bankTrialLiveGenealogyWordsOfWaveRows
      ring root S hclean hroot hinterior htop hincoming word)
    htheta

end L3

/-!
First supported row audit and exact two-slot alias obstruction.

BankTrialLiveWaveInteriorRows is quantified over ALL ring sizes
and arbitrary LIVE banks. It is not a theorem as written.
For n=2, site(root,2)=root. With an old LIVE root in RESET
and one old IR at digit 3, this physical edge both:
  (a) runs root RESET -> RWAIT and installs RR at digit 1;
  (b) frames the old IR at digit 3 in the selected 2->3 pair.
The successor is LIVE, but has two nonempty workers.
No CLEAN reachability is asserted for this old snapshot.

This is the first failing requested edge class. No proof of
InteriorRows/TopRows/IncomingRows/RootOutgoingRows is asserted.
-/

namespace L3

set_option autoImplicit false
set_option Elab.async false

/-- The smallest directed ring with distinct physical endpoints. -/
private def bankTrialLiveAliasRing : DirectedRing 2 :=
  ⟨by decide⟩

private def bankTrialLiveAliasRoot : Fin 2 := 0

/-- All digit bits are false; the ONLY old worker is IR
at logical digit 3. The root is RESET, success is unlatched.
This is legal local BANK scratch and has a LIVE phase, but
is not claimed reachable from CLEAN. -/
private def bankTrialLiveAliasReference :
    GrantBankReference.BankLocalReference (compileAdvice 0).b :=
  { fields := fun i =>
      (.RESET, false, if i.val = 3 then .IR else .E, 0),
    success := false }

private noncomputable def bankTrialLiveAliasPostBank :
    GrantBankReference.BankLocalReference (compileAdvice 0).b :=
  GrantBankReference.bankLocalReferenceStepClamped
    bankTrialLiveAliasRing bankTrialLiveAliasRoot
    bankTrialLiveAliasReference bankTrialLiveAliasRoot

/-- Offset 2 aliases the root on the two-agent ring.
Hence the "interior" j=2 clause is actually the physical
root-outgoing letter. -/
theorem bankTrialLiveAliasSiteCoincidence :
    Counter.site bankTrialLiveAliasRing bankTrialLiveAliasRoot 2 =
      bankTrialLiveAliasRoot := by
  rfl

/-- One old worker at digit 3, no other digit token. -/
private theorem bankTrialLiveAliasOldToken
    (j : Fin (compileAdvice 0).b) :
    bankTrialLiveWaveToken bankTrialLiveAliasReference j =
      (if j.val = 2 then .IR else .E) := by
  by_cases hj : j.val = 2
  · have hv : j.val + 1 = 3 := by omega
    simp [bankTrialLiveWaveToken,
      bankTrialLiveAliasReference, hj, hv]
  · have hv : j.val + 1 ≠ 3 := by omega
    simp [bankTrialLiveWaveToken,
      bankTrialLiveAliasReference, hj, hv]

/-- The old state satisfies ALL eight fields of the
lock predicate: RESET has no stage-specific worker restriction,
and the one IR trivially satisfies uniqueWorker. -/
theorem bankTrialLiveAliasCertificate :
    BankTrialLiveWaveCertificate 0 bankTrialLiveAliasReference := by
  have hm :
      bankTrialLiveWaveRootMode bankTrialLiveAliasReference =
        .RESET := rfl
  refine {
    cwaitTokens := ?_,
    iwaitTokens := ?_,
    headClear := ?_,
    resetTokens := ?_,
    uniqueWorker := ?_,
    comparisonMode := ?_,
    crPrefix := ?_,
    clAll := ?_
  }
  · intro j h
    rw [hm] at h
    cases h
  · intro j h
    rw [hm] at h
    cases h
  · intro j h
    rcases h with h | h <;> rw [hm] at h <;> cases h
  · intro j h
    rw [hm] at h
    cases h
  · intro i j hi hj
    rw [bankTrialLiveAliasOldToken] at hi hj
    by_cases hfirst : i.val = 2
    · by_cases hsecond : j.val = 2
      · exact Fin.ext (by omega)
      · simp [hsecond] at hj
    · simp [hfirst] at hi
  · intro j h
    rw [bankTrialLiveAliasOldToken] at h
    by_cases hj : j.val = 2
    · simp [hj] at h
    · simp [hj] at h
  · intro j h
    rw [bankTrialLiveAliasOldToken] at h
    by_cases hj : j.val = 2
    · simp [hj] at h
    · simp [hj] at h
  · intro j h
    rw [bankTrialLiveAliasOldToken] at h
    by_cases hj : j.val = 2
    · simp [hj] at h
    · simp [hj] at h

/-- The two literal, SMALL closed bankPair calculations.
Pair 0->1 launches RR; pair 2->3 leaves its old IR at 3.
No full-state enumeration or polynomial-size simplifier split. -/
private theorem bankTrialLiveAliasPairRows :
    (GrantBankReference.bankLocalReferenceInternalPair 0
      bankTrialLiveAliasReference
      ⟨0, by decide⟩).1.mode = .RWAIT ∧
    (GrantBankReference.bankLocalReferenceInternalPair 0
      bankTrialLiveAliasReference
      ⟨0, by decide⟩).2.tok = .RR ∧
    (GrantBankReference.bankLocalReferenceInternalPair 0
      bankTrialLiveAliasReference
      ⟨2, by decide⟩).2.tok = .IR := by
  constructor
  · rfl
  constructor
  · rfl
  · rfl

/-- The clamped pointwise selector executes these independent
pair projections on one physical letter: new root RWAIT,
new RR at digit 1, and retained IR at digit 3. -/
theorem bankTrialLiveAliasPostRows :
    (bankTrialLiveAliasPostBank.fields ⟨0, by decide⟩).1 =
      .RWAIT ∧
    (bankTrialLiveAliasPostBank.fields ⟨1, by decide⟩).2.2.1 =
      .RR ∧
    (bankTrialLiveAliasPostBank.fields ⟨3, by decide⟩).2.2.1 =
      .IR := by
  have hs : Counter.Support 0 bankTrialLiveAliasRing
      bankTrialLiveAliasRoot bankTrialLiveAliasRoot :=
    Or.inr ⟨0, by decide, rfl⟩
  have hf : bankTrialLiveAliasReference.success = false := rfl
  have hp := bankTrialLiveAliasPairRows
  unfold bankTrialLiveAliasPostBank
  constructor
  · rw [bankTrialLocalStepField bankTrialLiveAliasRing
        bankTrialLiveAliasRoot bankTrialLiveAliasRoot
        bankTrialLiveAliasReference hs hf,
      bankTrialLocalFieldRootOutgoing bankTrialLiveAliasRing
        bankTrialLiveAliasRoot bankTrialLiveAliasReference]
    change (GrantBankReference.bankLocalReferenceInternalPair 0
      bankTrialLiveAliasReference ⟨0, by decide⟩).1.mode =
        .RWAIT
    exact hp.1
  constructor
  · rw [bankTrialLocalStepField bankTrialLiveAliasRing
        bankTrialLiveAliasRoot bankTrialLiveAliasRoot
        bankTrialLiveAliasReference hs hf,
      bankTrialLocalFieldOneOutgoing bankTrialLiveAliasRing
        bankTrialLiveAliasRoot (by decide)
        bankTrialLiveAliasReference]
    change (GrantBankReference.bankLocalReferenceInternalPair 0
      bankTrialLiveAliasReference ⟨0, by decide⟩).2.tok =
        .RR
    exact hp.2.1
  · have hx :
        ¬ (3 < (compileAdvice 0).b ∧
          bankTrialLiveAliasRoot =
            Counter.site bankTrialLiveAliasRing
              bankTrialLiveAliasRoot 3) := by
        decide +kernel
    have hy :
        0 < (3 : Nat) ∧
          bankTrialLiveAliasRoot =
            Counter.site bankTrialLiveAliasRing
              bankTrialLiveAliasRoot (3 - 1) := by
        constructor
        · decide
        · rfl
    rw [bankTrialLiveCarryResponderSelected
      bankTrialLiveAliasRing bankTrialLiveAliasRoot
      bankTrialLiveAliasRoot bankTrialLiveAliasReference hs hf
      ⟨3, by decide⟩ hx hy]
    have hc := (bankTrialLiveClampBitToken 0
      ((GrantBankReference.bankLocalReferenceInternalPair 0
        bankTrialLiveAliasReference
        ⟨2, by decide⟩).2)).2
    exact hc.trans hp.2.2

/-- The old RESET state does not satisfy the old-state BANK
success guard, and the new RWAIT is neither CLEAN nor RESET.
Thus the next observer is still LIVE, not RECOVERY. -/
private theorem bankTrialLiveAliasPostNotLatched :
    bankTrialLiveAliasPostBank.success = false := by
  have hs : Counter.Support 0 bankTrialLiveAliasRing
      bankTrialLiveAliasRoot bankTrialLiveAliasRoot :=
    Or.inr ⟨0, by decide, rfl⟩
  simp [bankTrialLiveAliasPostBank,
    GrantBankReference.bankLocalReferenceStepClamped,
    hs, bankTrialLiveAliasReference,
    GrantBankReference.bankLocalReferenceSuccessEvent,
    GrantBankReference.bankLocalReferenceCell, bankSuccess]

theorem bankTrialLiveAliasNextLive :
    (bankTrialLocalNext bankTrialLiveAliasRing
      bankTrialLiveAliasRoot
      (⟨bankTrialLiveAliasReference, .live false⟩ :
        BankTrialLocalState 0) bankTrialLiveAliasRoot).phase =
      .live true := by
  classical
  have hroot := bankTrialLiveAliasPostRows.1
  have hnotclean :
      ¬ BankTrialLocalClean 0 bankTrialLiveAliasPostBank := by
    intro h
    have hm := h.2.1
    rw [hroot] at hm
    cases hm
  have hnotreset :
      (bankTrialLiveAliasPostBank.fields
        (0 : Fin ((compileAdvice 0).b + 1))).1 ≠ .RESET := by
    show (bankTrialLiveAliasPostBank.fields ⟨0, by decide⟩).1 ≠ .RESET
    rw [hroot]
    decide
  have hsuccess := bankTrialLiveAliasPostNotLatched
  unfold bankTrialLiveAliasPostBank at hsuccess hnotclean hnotreset
  simp [bankTrialLocalNext, hsuccess, hnotclean, hnotreset]

/-- The exact first requested interior-row obligation fails.
The offending observer slots are digit 1 (RR) and digit 3
(IR). Their indices 0 and 2 in Fin b cannot be equal, in
contradiction to the uniqueWorker clause. -/
theorem bankTrialLiveInteriorRowsAliasObstruction :
    ¬ BankTrialLiveWaveInteriorRows (q := 0)
      bankTrialLiveAliasRing bankTrialLiveAliasRoot := by
  intro hrows
  have hselected : BankTrialLiveWaveLiveEdgeRow (q := 0)
      bankTrialLiveAliasRing bankTrialLiveAliasRoot
      bankTrialLiveAliasRoot := by
    have h := hrows ⟨2, by decide⟩ (by decide)
    rw [bankTrialLiveAliasSiteCoincidence] at h
    exact h
  have hpost : BankTrialLiveWaveCertificate 0
      (bankTrialLocalNext bankTrialLiveAliasRing
        bankTrialLiveAliasRoot
        (⟨bankTrialLiveAliasReference, .live false⟩ :
          BankTrialLocalState 0) bankTrialLiveAliasRoot).bank :=
    hselected bankTrialLiveAliasReference false
      bankTrialLiveAliasCertificate true bankTrialLiveAliasNextLive
  have hbank :
      (bankTrialLocalNext bankTrialLiveAliasRing
        bankTrialLiveAliasRoot
        (⟨bankTrialLiveAliasReference, .live false⟩ :
          BankTrialLocalState 0) bankTrialLiveAliasRoot).bank =
        bankTrialLiveAliasPostBank :=
    bankTrialLocalNextLiveBank bankTrialLiveAliasRing
      bankTrialLiveAliasRoot bankTrialLiveAliasRoot
      bankTrialLiveAliasReference false
  have hfirst :
      bankTrialLiveWaveToken
        (bankTrialLocalNext bankTrialLiveAliasRing
          bankTrialLiveAliasRoot
          (⟨bankTrialLiveAliasReference, .live false⟩ :
            BankTrialLocalState 0) bankTrialLiveAliasRoot).bank
        ⟨0, by decide⟩ ≠ .E := by
    rw [hbank]
    change
      (bankTrialLiveAliasPostBank.fields
        ⟨1, by decide⟩).2.2.1 ≠ .E
    rw [bankTrialLiveAliasPostRows.2.1]
    decide
  have hthird :
      bankTrialLiveWaveToken
        (bankTrialLocalNext bankTrialLiveAliasRing
          bankTrialLiveAliasRoot
          (⟨bankTrialLiveAliasReference, .live false⟩ :
            BankTrialLocalState 0) bankTrialLiveAliasRoot).bank
        ⟨2, by decide⟩ ≠ .E := by
    rw [hbank]
    change
      (bankTrialLiveAliasPostBank.fields
        ⟨3, by decide⟩).2.2.1 ≠ .E
    rw [bankTrialLiveAliasPostRows.2.2]
    decide
  have hsame := hpost.uniqueWorker
    ⟨0, by decide⟩ ⟨2, by decide⟩ hfirst hthird
  have hval := congrArg Fin.val hsame
  change (0 : Nat) = 2 at hval
  omega

/-- Repair direction for LIVE-only invariants: an old RESET
root is excluded. This is necessary for the counterexample
above, though NOT sufficient by itself to prove the four
original unguarded supported-row statements on short rings. -/
def BankTrialLiveNoResetLocked {q : Nat}
    (z : BankTrialLocalState q) : Prop :=
  BankTrialLiveLockedGenealogy z ∧
    ∀ begun : Bool, z.phase = .live begun →
      bankTrialLiveWaveRootMode z.bank ≠ .RESET

theorem bankTrialLiveNoResetLockedStart {q : Nat}
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S) :
    BankTrialLiveNoResetLocked (bankTrialLocalStart S) := by
  constructor
  · exact bankTrialLiveLockedGenealogyStart S hclean
  · intro begun _ hreset
    change (S.fields ⟨0, by omega⟩).1 = .RESET at hreset
    rw [hclean.2.1] at hreset
    cases hreset

/-- Separate spatial non-alias requirement for a protected
window. The original row Props have no such assumption.
In the intended large-ring G11 regime it is implied by
the much stronger 2*bankLeaseCap <= n condition. -/
def BankTrialLiveWindowNonalias (n q : Nat) : Prop :=
  (compileAdvice q).b + 2 ≤ n

end L3

/-!
Corrected nonalias LIVE row interfaces and structural
interior selector.

The old four BankTrialLiveWave...Rows Props are retained:
their signatures are already used by earlier conditional theorems.
The new Window...Rows contracts require b+2<=n and the
no-RESET single-worker LIVE invariant. The complete interior
class is REDUCED to one explicitly OPEN two-slot owner Prop,
BankTrialLiveInteriorPairRows. No unconditional interior
worker closure or G11 authentication is claimed here.
-/

namespace L3

open Classical

set_option autoImplicit false
set_option Elab.async false

/-- G11's 2*Lambda<=n implies window nonalias, since
Lambda=13*(b+2). -/
theorem bankTrialWindowFromLeaseCap {n q : Nat}
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n) :
    BankTrialLiveWindowNonalias n q := by
  unfold BankTrialLiveWindowNonalias
  change 2 * (13 * ((compileAdvice q).b + 2)) ≤ n at hlarge
  omega

/-- Logical clockwise offset j has the literal modular
coordinate (root+j)%n. -/
private theorem bankTrialWindowSiteValue {n : Nat}
    (ring : DirectedRing n) (root : Fin n) :
    ∀ j : Nat,
      (Counter.site ring root j).val = (root.val + j) % n := by
  intro j
  induction j with
  | zero =>
      simp [Counter.site, Nat.mod_eq_of_lt root.isLt]
  | succ j ih =>
      change ((Counter.site ring root j).val + 1) % n =
        (root.val + (j + 1)) % n
      rw [ih, Nat.mod_add_mod]
      congr 1

/-- One subtraction is enough when a<2n. -/
private theorem bankTrialWindowOneWrap
    (n a : Nat) (hn : 0 < n) (hbound : a < 2 * n) :
    a % n = if a < n then a else a - n := by
  by_cases h : a < n
  · simp [h, Nat.mod_eq_of_lt h]
  · have hs : a - n < n := by omega
    have heq : a = (a - n) + n := by omega
    have hmod : a % n = a - n := by
      calc
        a % n = ((a - n) + n) % n := by rw [← heq]
        _ = (a - n) % n := by simp [Nat.add_mod]
        _ = a - n := Nat.mod_eq_of_lt hs
    simpa [h] using hmod

/-- Injectivity of the ring's cyclic site map within one round. -/
theorem bankTrialWindowSiteInjective {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (i j : Nat) (hi : i < n) (hj : j < n)
    (he : Counter.site ring root i =
      Counter.site ring root j) : i = j := by
  have hv := congrArg Fin.val he
  rw [bankTrialWindowSiteValue ring root i,
    bankTrialWindowSiteValue ring root j] at hv
  have ha := bankTrialWindowOneWrap n (root.val + i)
    ring.hn (by have hr := root.isLt; omega)
  have hb := bankTrialWindowOneWrap n (root.val + j)
    ring.hn (by have hr := root.isLt; omega)
  rw [ha, hb] at hv
  by_cases hia : root.val + i < n
  · by_cases hjb : root.val + j < n
    · simp [hia, hjb] at hv
      omega
    · simp [hia, hjb] at hv
      omega
  · by_cases hjb : root.val + j < n
    · simp [hia, hjb] at hv
      omega
    · simp [hia, hjb] at hv
      omega

/-- b+2<=n makes the full interval of offsets 0,...,b+1
pairwise distinct (including its incoming/top seam). -/
theorem bankTrialWindowSitesDistinct {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hw : BankTrialLiveWindowNonalias n q)
    (i j : Nat)
    (hi : i ≤ (compileAdvice q).b + 1)
    (hj : j ≤ (compileAdvice q).b + 1)
    (he : Counter.site ring root i =
      Counter.site ring root j) : i = j := by
  exact bankTrialWindowSiteInjective ring root i j
    (by unfold BankTrialLiveWindowNonalias at hw; omega)
    (by unfold BankTrialLiveWindowNonalias at hw; omega)
    he

theorem bankTrialWindowInteriorNotRoot {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hw : BankTrialLiveWindowNonalias n q)
    (j : Fin (compileAdvice q).b) (hj : 0 < j.val) :
    Counter.site ring root j.val ≠ root := by
  intro h
  have he : Counter.site ring root j.val =
      Counter.site ring root 0 := h
  have hij := bankTrialWindowSitesDistinct ring root hw
    j.val 0 (by omega) (by omega) he
  omega

/-- At e=site(root,j), every i outside {j,j+1} is a
genuine frame. Check the source, responder, top and incoming
selector guards independently; no false general framing. -/
theorem bankTrialWindowInteriorFrame {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hw : BankTrialLiveWindowNonalias n q)
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hf : B.success = false)
    (j : Fin (compileAdvice q).b) (hj : 0 < j.val)
    (i : Fin ((compileAdvice q).b + 1))
    (hneSource : i.val ≠ j.val)
    (hneTarget : i.val ≠ j.val + 1) :
    (GrantBankReference.bankLocalReferenceStepClamped
      ring root B (Counter.site ring root j.val)).fields i =
      B.fields i := by
  have hs : Counter.Support q ring root
      (Counter.site ring root j.val) :=
    Or.inr ⟨j.val, by omega, rfl⟩
  refine bankTrialLiveCarryUnselectedField ring root
    (Counter.site ring root j.val) B hs hf i ?_ ?_ ?_ ?_
  · intro hx
    have hij := bankTrialWindowSitesDistinct ring root hw
      i.val j.val (by omega) (by omega) hx.2.symm
    exact hneSource hij
  · intro hy
    have hij := bankTrialWindowSitesDistinct ring root hw
      (i.val - 1) j.val (by omega) (by omega) hy.2.symm
    exact hneTarget (by omega)
  · intro ht
    have hjb := bankTrialWindowSitesDistinct ring root hw
      j.val (compileAdvice q).b (by omega) (by omega) ht.2
    omega
  · intro hr
    have hsite : Counter.site ring root (j.val + 1) =
        Counter.site ring root 0 := by
      change ring.rightNeighbor (Counter.site ring root j.val) =
        root
      exact hr.2
    have hzero := bankTrialWindowSitesDistinct ring root hw
      (j.val + 1) 0 (by omega) (by omega) hsite
    omega

/-- The selected source slot j is exactly bankPair.1. -/
theorem bankTrialWindowInteriorSource {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hf : B.success = false)
    (j : Fin (compileAdvice q).b) :
    (GrantBankReference.bankLocalReferenceStepClamped
      ring root B (Counter.site ring root j.val)).fields
        ⟨j.val, by omega⟩ =
    GrantBankReference.bankLocalReferenceClampedQuad q
      ((GrantBankReference.bankLocalReferenceInternalPair
        q B j).1) := by
  have hs : Counter.Support q ring root
      (Counter.site ring root j.val) :=
    Or.inr ⟨j.val, by omega, rfl⟩
  exact bankTrialLiveCarrySourceSelected ring root
    (Counter.site ring root j.val) B hs hf
    ⟨j.val, by omega⟩ ⟨j.isLt, rfl⟩

/-- The selected responder j+1 is exactly bankPair.2.
Nonalias excludes the earlier source-branch priority. -/
theorem bankTrialWindowInteriorResponder {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hw : BankTrialLiveWindowNonalias n q)
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hf : B.success = false)
    (j : Fin (compileAdvice q).b) :
    (GrantBankReference.bankLocalReferenceStepClamped
      ring root B (Counter.site ring root j.val)).fields
        ⟨j.val + 1, by omega⟩ =
    GrantBankReference.bankLocalReferenceClampedQuad q
      ((GrantBankReference.bankLocalReferenceInternalPair
        q B j).2) := by
  have hs : Counter.Support q ring root
      (Counter.site ring root j.val) :=
    Or.inr ⟨j.val, by omega, rfl⟩
  have hnsource :
      ¬ (j.val + 1 < (compileAdvice q).b ∧
        Counter.site ring root j.val =
          Counter.site ring root (j.val + 1)) := by
    intro h
    have hij := bankTrialWindowSitesDistinct ring root hw
      j.val (j.val + 1) (by omega) (by omega) h.2
    omega
  have htarget :
      0 < j.val + 1 ∧
        Counter.site ring root j.val =
          Counter.site ring root (j.val + 1 - 1) := by
    constructor
    · omega
    · have he : j.val + 1 - 1 = j.val := by omega
      rw [he]
  exact bankTrialLiveCarryResponderSelected ring root
    (Counter.site ring root j.val) B hs hf
    ⟨j.val + 1, by omega⟩ hnsource htarget

/-- The logical update of precisely two slots with the old
success latch. It has no ring, n or scheduler parameter. -/
noncomputable def bankTrialWindowInteriorPatch {q : Nat}
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (j : Fin (compileAdvice q).b) :
    GrantBankReference.BankLocalReference
      (compileAdvice q).b :=
  { fields := fun i =>
      if i.val = j.val then
        GrantBankReference.bankLocalReferenceClampedQuad q
          ((GrantBankReference.bankLocalReferenceInternalPair q B j).1)
      else if i.val = j.val + 1 then
        GrantBankReference.bankLocalReferenceClampedQuad q
          ((GrantBankReference.bankLocalReferenceInternalPair q B j).2)
      else B.fields i,
    success := B.success }

/-- Full exact fieldwise agreement of the stopped local reference
and the two-slot patch, with every other slot framed. -/
theorem bankTrialWindowInteriorFieldsEqPatch {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hw : BankTrialLiveWindowNonalias n q)
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hf : B.success = false)
    (j : Fin (compileAdvice q).b) (hj : 0 < j.val) :
    (GrantBankReference.bankLocalReferenceStepClamped
      ring root B (Counter.site ring root j.val)).fields =
        (bankTrialWindowInteriorPatch B j).fields := by
  funext i
  by_cases hi : i.val = j.val
  · have he : i = ⟨j.val, by omega⟩ := Fin.ext hi
    rw [he, bankTrialWindowInteriorSource ring root B hf j]
    simp [bankTrialWindowInteriorPatch]
  · by_cases hnext : i.val = j.val + 1
    · have he : i = ⟨j.val + 1, by omega⟩ := Fin.ext hnext
      rw [he, bankTrialWindowInteriorResponder
        ring root hw B hf j]
      have hne : j.val + 1 ≠ j.val := by omega
      simp [bankTrialWindowInteriorPatch, hne]
    · rw [bankTrialWindowInteriorFrame
        ring root hw B hf j hj i hi hnext]
      simp [bankTrialWindowInteriorPatch, hi, hnext]

/-- The checked-bit and token stage lock depends only on fields,
never on success. -/
theorem bankTrialWindowCertificateFieldsCongr {q : Nat}
    (A B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (heq : A.fields = B.fields)
    (hc : BankTrialLiveWaveCertificate q B) :
    BankTrialLiveWaveCertificate q A := by
  cases A with
  | mk fieldsA successA =>
    cases B with
    | mk fieldsB successB =>
      dsimp at heq
      subst fieldsB
      exact ⟨hc.1, hc.2, hc.3, hc.4, hc.5, hc.6, hc.7, hc.8⟩

/-- The old latch must be false if the new observer is LIVE. -/
theorem bankTrialWindowLiveOldNotLatched {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b) (begun nextBegun : Bool)
    (hnext : (bankTrialLocalNext ring root
      (⟨B, .live begun⟩ : BankTrialLocalState q) e).phase =
        .live nextBegun) :
    B.success = false := by
  cases hs : B.success with
  | false => rfl
  | true =>
      have hframe := bankTrialLiveCarryLatchedRawFrame
        ring root e B hs
      have hwon :
          (bankTrialLocalNext ring root
            (⟨B, .live begun⟩ : BankTrialLocalState q) e).phase =
            .won := by
        simp [bankTrialLocalNext, hframe, hs]
      rw [hwon] at hnext
      cases hnext

/-- Every proper nonaliased interior service frames root mode. -/
theorem bankTrialWindowInteriorRootModeFrame {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hw : BankTrialLiveWindowNonalias n q)
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hf : B.success = false)
    (j : Fin (compileAdvice q).b) (hj : 0 < j.val) :
    bankTrialLiveWaveRootMode
      (GrantBankReference.bankLocalReferenceStepClamped
        ring root B (Counter.site ring root j.val)) =
      bankTrialLiveWaveRootMode B := by
  change
    ((GrantBankReference.bankLocalReferenceStepClamped
      ring root B (Counter.site ring root j.val)).fields
        ⟨0, by omega⟩).1 =
      (B.fields ⟨0, by omega⟩).1
  rw [bankTrialWindowInteriorFrame
    ring root hw B hf j hj ⟨0, by omega⟩
    (Nat.ne_of_lt hj) (Nat.succ_ne_zero j.val).symm]

/-- Corrected LIVE row contract: b+2<=n and the OLD
no-RESET single-worker LIVE lock imply the SAME lock at a
LIVE successor. The original old row Props are retained. -/
def BankTrialLiveWindowLockedEdgeRow {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n) : Prop :=
  BankTrialLiveWindowNonalias n q →
  ∀ (B : GrantBankReference.BankLocalReference
        (compileAdvice q).b) (begun : Bool),
    BankTrialLiveNoResetLocked
      (⟨B, .live begun⟩ : BankTrialLocalState q) →
    ∀ nextBegun : Bool,
      (bankTrialLocalNext ring root
        (⟨B, .live begun⟩ : BankTrialLocalState q) e).phase =
          .live nextBegun →
      BankTrialLiveNoResetLocked
        (bankTrialLocalNext ring root
          (⟨B, .live begun⟩ : BankTrialLocalState q) e)

def BankTrialLiveWindowRootOutgoingRows {n q : Nat}
    (ring : DirectedRing n) (root : Fin n) : Prop :=
  BankTrialLiveWindowLockedEdgeRow (q := q) ring root root

def BankTrialLiveWindowInteriorRows {n q : Nat}
    (ring : DirectedRing n) (root : Fin n) : Prop :=
  ∀ j : Fin (compileAdvice q).b, 0 < j.val →
    BankTrialLiveWindowLockedEdgeRow (q := q) ring root
      (Counter.site ring root j.val)

def BankTrialLiveWindowTopRows {n q : Nat}
    (ring : DirectedRing n) (root : Fin n) : Prop :=
  BankTrialLiveWindowLockedEdgeRow (q := q) ring root
    (Counter.site ring root (compileAdvice q).b)

def BankTrialLiveWindowIncomingRows {n q : Nat}
    (ring : DirectedRing n) (root : Fin n) : Prop :=
  ∀ e : Fin n, ring.rightNeighbor e = root →
    BankTrialLiveWindowLockedEdgeRow (q := q) ring root e

/-- OPEN two-slot local-owner obligation. The outer scheduler,
the physical ring, aliasing and the frame have all been
eliminated, but the finite mode/token case split is not yet
proved. Leaving this as a Prop avoids a false claim of G11. -/
def BankTrialLiveInteriorPairRows (q : Nat) : Prop :=
  ∀ (B : GrantBankReference.BankLocalReference
        (compileAdvice q).b)
    (j : Fin (compileAdvice q).b),
    0 < j.val →
    BankTrialLiveWaveCertificate q B →
    bankTrialLiveWaveRootMode B ≠ .RESET →
    BankTrialLiveWaveCertificate q
      (bankTrialWindowInteriorPatch B j)

/-- The COMPLETE physical interior row class reduces to
that one OPEN two-cell invariant. This theorem is conditional. -/
theorem bankTrialWindowInteriorRowsOfPairRows {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hpair : BankTrialLiveInteriorPairRows q) :
    BankTrialLiveWindowInteriorRows (q := q) ring root := by
  intro j hj hw B begun hlock nextBegun hnext
  have hf := bankTrialWindowLiveOldNotLatched
    ring root (Counter.site ring root j.val)
    B begun nextBegun hnext
  have hbank := bankTrialLocalNextLiveBank ring root
    (Counter.site ring root j.val) B begun
  have hc : BankTrialLiveWaveCertificate q B :=
    hlock.1 begun rfl
  have hm : bankTrialLiveWaveRootMode B ≠ .RESET :=
    hlock.2 begun rfl
  have hpatch : BankTrialLiveWaveCertificate q
      (bankTrialWindowInteriorPatch B j) :=
    hpair B j hj hc hm
  have hfields := bankTrialWindowInteriorFieldsEqPatch
    ring root hw B hf j hj
  have hnew :
      BankTrialLiveWaveCertificate q
        (GrantBankReference.bankLocalReferenceStepClamped
          ring root B (Counter.site ring root j.val)) :=
    bankTrialWindowCertificateFieldsCongr
      (GrantBankReference.bankLocalReferenceStepClamped
        ring root B (Counter.site ring root j.val))
      (bankTrialWindowInteriorPatch B j) hfields hpatch
  have hrootFrame := bankTrialWindowInteriorRootModeFrame
    ring root hw B hf j hj
  constructor
  · intro phaseFlag _
    rw [hbank]
    exact hnew
  · intro phaseFlag _ hreset
    rw [hbank, hrootFrame] at hreset
    exact hm hreset

/-- Unsupported physical scheduler letters always frame the
corrected LIVE lock. -/
theorem bankTrialWindowOutsideLockedRow {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (hout : ¬ Counter.Support q ring root e) :
    BankTrialLiveWindowLockedEdgeRow (q := q)
      ring root e := by
  intro hw B begun hlock nextBegun _
  have hframe := bankTrialLiveOutsideBankFrame
    ring root e B begun hout
  constructor
  · intro phaseFlag _
    rw [hframe]
    exact hlock.1 begun rfl
  · intro phaseFlag _
    rw [hframe]
    exact hlock.2 begun rfl

/-- Original edge geometry, now with corrected nonalias and
no-RESET row-class contracts. -/
theorem bankTrialWindowRowsOfClasses {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hroot : BankTrialLiveWindowRootOutgoingRows
      (q := q) ring root)
    (hinterior : BankTrialLiveWindowInteriorRows
      (q := q) ring root)
    (htop : BankTrialLiveWindowTopRows
      (q := q) ring root)
    (hincoming : BankTrialLiveWindowIncomingRows
      (q := q) ring root) :
    ∀ e : Fin n,
      BankTrialLiveWindowLockedEdgeRow (q := q) ring root e := by
  intro e
  rcases Counter.resetTrialEdgeGeometry (q := q)
      ring root e with hsource | hin | hout
  · obtain ⟨j, hj, he⟩ := hsource
    by_cases htopj : j = (compileAdvice q).b
    · subst j
      rw [he]
      exact htop
    · by_cases hz : j = 0
      · subst j
        change e = root at he
        rw [he]
        exact hroot
      · have hjfin : j < (compileAdvice q).b := by omega
        rw [he]
        exact hinterior ⟨j, hjfin⟩ (Nat.pos_of_ne_zero hz)
  · exact hincoming e hin
  · have houtside : ¬ Counter.Support q ring root e := by
      intro hs
      rcases hs with hinc | ⟨j, hj, he⟩
      · have hp := (hout 0 (by omega)).2
        change ring.rightNeighbor e ≠ root at hp
        exact hp hinc
      · exact (hout j hj).1 he
    exact bankTrialWindowOutsideLockedRow ring root e houtside

/-- If every corrected class holds, any old terminal phase
remains non-LIVE; a genuinely LIVE successor inherits the
strengthened lock from its row class. -/
theorem bankTrialWindowLockedNextOfRows {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (hw : BankTrialLiveWindowNonalias n q)
    (hrows : ∀ f : Fin n,
      BankTrialLiveWindowLockedEdgeRow (q := q) ring root f)
    (z : BankTrialLocalState q)
    (hlock : BankTrialLiveNoResetLocked z) :
    BankTrialLiveNoResetLocked
      (bankTrialLocalNext ring root z e) := by
  cases z with
  | mk B phase =>
    cases phase with
    | live begun =>
        by_cases hl : ∃ b : Bool,
            (bankTrialLocalNext ring root
              (⟨B, .live begun⟩ : BankTrialLocalState q) e).phase =
              .live b
        · obtain ⟨b, hb⟩ := hl
          exact hrows e hw B begun hlock b hb
        · constructor
          · intro b hb
            exact False.elim (hl ⟨b, hb⟩)
          · intro b hb
            exact False.elim (hl ⟨b, hb⟩)
    | recovery =>
        constructor
        · intro b hb
          simp [bankTrialLocalNext] at hb <;>
            (repeat' split at hb) <;> cases hb
        · intro b hb
          simp [bankTrialLocalNext] at hb <;>
            (repeat' split at hb) <;> cases hb
    | won =>
        constructor
        · intro b hb
          simp [bankTrialLocalNext] at hb
        · intro b hb
          simp [bankTrialLocalNext] at hb
    | lost =>
        constructor
        · intro b hb
          simp [bankTrialLocalNext] at hb
        · intro b hb
          simp [bankTrialLocalNext] at hb

/-- True chronological induction over the original finite
scheduler word, conditional on the corrected row classes. -/
theorem bankTrialWindowLockedRunOfRows {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hw : BankTrialLiveWindowNonalias n q)
    (hrows : ∀ e : Fin n,
      BankTrialLiveWindowLockedEdgeRow (q := q) ring root e) :
    ∀ (word : List (Fin n)) (z : BankTrialLocalState q),
      BankTrialLiveNoResetLocked z →
      BankTrialLiveNoResetLocked
        (bankTrialLocalRun ring root word z) := by
  intro word
  induction word with
  | nil =>
      intro z hlock
      exact hlock
  | cons e es ih =>
      intro z hlock
      change BankTrialLiveNoResetLocked
        (bankTrialLocalRun ring root es
          (bankTrialLocalNext ring root z e))
      exact ih _ (bankTrialWindowLockedNextOfRows
        ring root e hw hrows z hlock)

/-- CLEAN-to-all-words induction with the corrected classes.
No claim is made without hroot/hinterior/htop/hincoming. -/
theorem bankTrialWindowLockedCleanWordsOfClasses {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hw : BankTrialLiveWindowNonalias n q)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S)
    (hroot : BankTrialLiveWindowRootOutgoingRows
      (q := q) ring root)
    (hinterior : BankTrialLiveWindowInteriorRows
      (q := q) ring root)
    (htop : BankTrialLiveWindowTopRows
      (q := q) ring root)
    (hincoming : BankTrialLiveWindowIncomingRows
      (q := q) ring root) :
    ∀ word : List (Fin n),
      BankTrialLiveNoResetLocked
        (bankTrialLocalRun ring root word (bankTrialLocalStart S)) := by
  have hrows := bankTrialWindowRowsOfClasses
    ring root hroot hinterior htop hincoming
  intro word
  exact bankTrialWindowLockedRunOfRows
    ring root hw hrows word (bankTrialLocalStart S)
    (bankTrialLiveNoResetLockedStart S hclean)

end L3

/-!
Two-slot BANK owner audit.

For j>0 and j<b, the one-worker row classification is:

old source RR -> right RR (destination bit cleared)
old top target RR -> left RL (source bit cleared)
old target RL -> left RL (source bit cleared)
old source IR -> destination bit flips, new IR or AL
old top target IR -> erased
old target AL -> left AL
old source CR0/CR1 -> right CR0, or CR1 if new bit matches
old top target CR0/CR1 -> left CL0/CL1
old target CL0/CL1 -> left CL0/CL1
any other lone worker -> held or erased
both old tokens E -> both new tokens E, bits unchanged.

CWAIT permits only comparison workers. Thus genuine comparison
rows do not write bits; CR1 extends the checked prefix, while
a top-turn CL1 inherits the entire checked word. This is the
mathematical route to the original eight clauses.

The remaining four local owner obligations below are OPEN Props.
The theorem BankTrialLiveInteriorPairRows has NOT been discharged;
the final composition is conditional on these obligations. The
proof candidates below do not contain any proof escape.
-/

namespace L3

set_option autoImplicit false
set_option Elab.async false

/-- The pair source field is exactly the first clamped output. -/
theorem bankTrialInteriorPatchSourceField {q : Nat}
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (j : Fin (compileAdvice q).b) :
    (bankTrialWindowInteriorPatch B j).fields
        ⟨j.val, by omega⟩ =
      GrantBankReference.bankLocalReferenceClampedQuad q
        ((GrantBankReference.bankLocalReferenceInternalPair
          q B j).1) := by
  simp [bankTrialWindowInteriorPatch]

/-- The pair target field is exactly the second clamped output. -/
theorem bankTrialInteriorPatchTargetField {q : Nat}
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (j : Fin (compileAdvice q).b) :
    (bankTrialWindowInteriorPatch B j).fields
        ⟨j.val + 1, by omega⟩ =
      GrantBankReference.bankLocalReferenceClampedQuad q
        ((GrantBankReference.bankLocalReferenceInternalPair
          q B j).2) := by
  have hne : j.val + 1 ≠ j.val := by omega
  simp [bankTrialWindowInteriorPatch, hne]

/-- All slots except the two touched slots are literal frames. -/
theorem bankTrialInteriorPatchFieldFrame {q : Nat}
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (j : Fin (compileAdvice q).b)
    (i : Fin ((compileAdvice q).b + 1))
    (hsource : i.val ≠ j.val)
    (htarget : i.val ≠ j.val + 1) :
    (bankTrialWindowInteriorPatch B j).fields i =
      B.fields i := by
  simp [bankTrialWindowInteriorPatch, hsource, htarget]

/-- In particular the nonroot patch cannot change root mode. -/
theorem bankTrialInteriorPatchRootMode {q : Nat}
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (j : Fin (compileAdvice q).b)
    (hj : 0 < j.val) :
    bankTrialLiveWaveRootMode
      (bankTrialWindowInteriorPatch B j) =
    bankTrialLiveWaveRootMode B := by
  change ((bankTrialWindowInteriorPatch B j).fields
    ⟨0, by omega⟩).1 = (B.fields ⟨0, by omega⟩).1
  exact congrArg (fun v : Mode × Bool × BTok × Nat => v.1)
    (bankTrialInteriorPatchFieldFrame B j
      ⟨0, by omega⟩ (Nat.ne_of_lt hj)
      (Nat.succ_ne_zero j.val).symm)

/-- Token indexing subtracts one from the physical digit slot. -/
theorem bankTrialInteriorPatchTokenFrame {q : Nat}
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (j k : Fin (compileAdvice q).b)
    (hsource : k.val + 1 ≠ j.val)
    (htarget : k.val + 1 ≠ j.val + 1) :
    bankTrialLiveWaveToken
      (bankTrialWindowInteriorPatch B j) k =
      bankTrialLiveWaveToken B k := by
  change ((bankTrialWindowInteriorPatch B j).fields
    ⟨k.val + 1, by omega⟩).2.2.1 =
    (B.fields ⟨k.val + 1, by omega⟩).2.2.1
  exact congrArg
    (fun v : Mode × Bool × BTok × Nat => v.2.2.1)
    (bankTrialInteriorPatchFieldFrame B j
      ⟨k.val + 1, by omega⟩ hsource htarget)

/-- Unselected bits are framed independently of their values. -/
theorem bankTrialInteriorPatchBitFrame {q : Nat}
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (j k : Fin (compileAdvice q).b)
    (hsource : k.val + 1 ≠ j.val)
    (htarget : k.val + 1 ≠ j.val + 1) :
    bankTrialLiveWaveBit
      (bankTrialWindowInteriorPatch B j) k =
      bankTrialLiveWaveBit B k := by
  change ((bankTrialWindowInteriorPatch B j).fields
    ⟨k.val + 1, by omega⟩).2.1 =
    (B.fields ⟨k.val + 1, by omega⟩).2.1
  exact congrArg
    (fun v : Mode × Bool × BTok × Nat => v.2.1)
    (bankTrialInteriorPatchFieldFrame B j
      ⟨k.val + 1, by omega⟩ hsource htarget)

/-- Under uniqueness, an old nonempty worker determines all
other old protected token slots to be E. -/
theorem bankTrialInteriorOldWorkerOthersEmpty {q : Nat}
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hc : BankTrialLiveWaveCertificate q B)
    (w i : Fin (compileAdvice q).b)
    (hw : bankTrialLiveWaveToken B w ≠ .E)
    (hi : i ≠ w) :
    bankTrialLiveWaveToken B i = .E := by
  by_cases he : bankTrialLiveWaveToken B i = .E
  · exact he
  · have hwi := hc.uniqueWorker w i hw he
    exact False.elim (hi hwi.symm)

/-- The literal E/E nonroot BANK row creates no token and
changes neither bit. One source token and one target token
are fixed; no whole-state case product is performed. -/
theorem bankTrialInteriorRawEmptyPair
    (b : Nat) (theta : Nat → Bool) (x y : BankCell)
    (hx : 1 ≤ x.role) (hlt : x.role < b)
    (hy : y.role = x.role + 1)
    (hxt : x.tok = .E) (hyt : y.tok = .E) :
    (bankPair x y y.role b theta).1.tok = .E ∧
    (bankPair x y y.role b theta).2.tok = .E ∧
    (bankPair x y y.role b theta).1.bit = x.bit ∧
    (bankPair x y y.role b theta).2.bit = y.bit := by
  have hxn : x.role ≠ 0 := by omega
  have hyn : y.role ≠ 0 := by omega
  have hxb : x.role ≤ b := by omega
  have hyb : y.role ≤ b := by omega
  have hypos : 1 ≤ y.role := by omega
  have hxnotTop : x.role ≠ b := by omega
  simp [bankPair, hx, hlt, hy, hxt, hyt, hxn, hyn,
    hxb, hyb, hypos, hxnotTop, Id.run_pure, Id.run_bind]

/-- First four stage clauses of the LIVE certificate, without
the unique worker or checked-bit ancestry clauses. -/
structure BankTrialInteriorStageFacts (q : Nat)
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b) : Prop where
  cwaitTokens :
    ∀ k : Fin (compileAdvice q).b,
      bankTrialLiveWaveRootMode B = .CWAIT →
      bankTrialLiveWaveToken B k = .E ∨
        BankTrialLiveComparisonToken (bankTrialLiveWaveToken B k)
  iwaitTokens :
    ∀ k : Fin (compileAdvice q).b,
      bankTrialLiveWaveRootMode B = .IWAIT →
      bankTrialLiveWaveToken B k = .E ∨
        bankTrialLiveWaveToken B k = .IR ∨
        bankTrialLiveWaveToken B k = .AL
  headClear :
    ∀ k : Fin (compileAdvice q).b,
      (bankTrialLiveWaveRootMode B = .ARMED ∨
        bankTrialLiveWaveRootMode B = .CSTART) →
      bankTrialLiveWaveToken B k = .E
  resetTokens :
    ∀ k : Fin (compileAdvice q).b,
      bankTrialLiveWaveRootMode B = .RWAIT →
      bankTrialLiveWaveToken B k = .E ∨
        bankTrialLiveWaveToken B k = .RR ∨
        bankTrialLiveWaveToken B k = .RL

theorem bankTrialInteriorStageFactsOfCertificate {q : Nat}
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hc : BankTrialLiveWaveCertificate q B) :
    BankTrialInteriorStageFacts q B := by
  exact ⟨hc.cwaitTokens, hc.iwaitTokens,
    hc.headClear, hc.resetTokens⟩

/-- The comparisonMode clause is redundant once the four
stage clauses hold and the root mode is not RESET. -/
theorem bankTrialInteriorComparisonModeOfStages {q : Nat}
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hs : BankTrialInteriorStageFacts q B)
    (hnr : bankTrialLiveWaveRootMode B ≠ .RESET) :
    ∀ k : Fin (compileAdvice q).b,
      (bankTrialLiveWaveToken B k = .CR1 ∨
        bankTrialLiveWaveToken B k = .CL1) →
      bankTrialLiveWaveRootMode B = .CWAIT := by
  intro k htoken
  cases hm : bankTrialLiveWaveRootMode B with
  | RESET =>
      exact False.elim (hnr hm)
  | RWAIT =>
      rcases hs.resetTokens k hm with ht | ht | ht
      all_goals
        rcases htoken with hw | hw
        · rw [ht] at hw
          cases hw
        · rw [ht] at hw
          cases hw
  | ARMED =>
      have ht := hs.headClear k (Or.inl hm)
      rcases htoken with hw | hw
      · rw [ht] at hw
        cases hw
      · rw [ht] at hw
        cases hw
  | IWAIT =>
      rcases hs.iwaitTokens k hm with ht | ht | ht
      all_goals
        rcases htoken with hw | hw
        · rw [ht] at hw
          cases hw
        · rw [ht] at hw
          cases hw
  | CSTART =>
      have ht := hs.headClear k (Or.inr hm)
      rcases htoken with hw | hw
      · rw [ht] at hw
        cases hw
      · rw [ht] at hw
        cases hw
  | CWAIT =>
      rfl

/-- The four still-open local owner obligations. Each one
has a specific local-mode/token or checked-bit meaning. -/
def BankTrialInteriorStagePreservation (q : Nat) : Prop :=
  ∀ (B : GrantBankReference.BankLocalReference
        (compileAdvice q).b)
    (j : Fin (compileAdvice q).b),
    0 < j.val →
    BankTrialLiveWaveCertificate q B →
    bankTrialLiveWaveRootMode B ≠ .RESET →
    BankTrialInteriorStageFacts q
      (bankTrialWindowInteriorPatch B j)

def BankTrialInteriorWorkerUniqueness (q : Nat) : Prop :=
  ∀ (B : GrantBankReference.BankLocalReference
        (compileAdvice q).b)
    (j : Fin (compileAdvice q).b),
    0 < j.val →
    BankTrialLiveWaveCertificate q B →
    bankTrialLiveWaveRootMode B ≠ .RESET →
    ∀ i k : Fin (compileAdvice q).b,
      bankTrialLiveWaveToken (bankTrialWindowInteriorPatch B j) i ≠ .E →
      bankTrialLiveWaveToken (bankTrialWindowInteriorPatch B j) k ≠ .E →
      i = k

def BankTrialInteriorCRPrefixPreservation (q : Nat) : Prop :=
  ∀ (B : GrantBankReference.BankLocalReference
        (compileAdvice q).b)
    (j : Fin (compileAdvice q).b),
    0 < j.val →
    BankTrialLiveWaveCertificate q B →
    bankTrialLiveWaveRootMode B ≠ .RESET →
    ∀ i : Fin (compileAdvice q).b,
      bankTrialLiveWaveToken (bankTrialWindowInteriorPatch B j) i =
        .CR1 →
      ∀ k : Fin (compileAdvice q).b, k.val ≤ i.val →
        bankTrialLiveWaveBit (bankTrialWindowInteriorPatch B j) k =
          (compileAdvice q).theta k.val

def BankTrialInteriorCLFullPreservation (q : Nat) : Prop :=
  ∀ (B : GrantBankReference.BankLocalReference
        (compileAdvice q).b)
    (j : Fin (compileAdvice q).b),
    0 < j.val →
    BankTrialLiveWaveCertificate q B →
    bankTrialLiveWaveRootMode B ≠ .RESET →
    ∀ i : Fin (compileAdvice q).b,
      bankTrialLiveWaveToken (bankTrialWindowInteriorPatch B j) i =
        .CL1 →
      ∀ k : Fin (compileAdvice q).b,
        bankTrialLiveWaveBit (bankTrialWindowInteriorPatch B j) k =
          (compileAdvice q).theta k.val

/-- Conditional assembly of all eight certificate clauses.
The fifth comparisonMode clause is discharged, not assumed.
This is deliberately not the unconditional BankTrialLiveInteriorPairRows. -/
theorem bankTrialInteriorPairRowsOfComponents (q : Nat)
    (hstage : BankTrialInteriorStagePreservation q)
    (hunique : BankTrialInteriorWorkerUniqueness q)
    (hcr : BankTrialInteriorCRPrefixPreservation q)
    (hcl : BankTrialInteriorCLFullPreservation q) :
    BankTrialLiveInteriorPairRows q := by
  intro B j hj hc hnr
  have hs := hstage B j hj hc hnr
  have hr := bankTrialInteriorPatchRootMode B j hj
  have hnnew :
      bankTrialLiveWaveRootMode
        (bankTrialWindowInteriorPatch B j) ≠ .RESET := by
    rw [hr]
    exact hnr
  refine {
    cwaitTokens := hs.cwaitTokens,
    iwaitTokens := hs.iwaitTokens,
    headClear := hs.headClear,
    resetTokens := hs.resetTokens,
    uniqueWorker := hunique B j hj hc hnr,
    comparisonMode :=
      bankTrialInteriorComparisonModeOfStages
        (bankTrialWindowInteriorPatch B j) hs hnnew,
    crPrefix := hcr B j hj hc hnr,
    clAll := hcl B j hj hc hnr
  }

/-- Subsequent G11 interior row and CLEAN-word transfers can
reuse the conditional theorem after these four premises
are discharged. -/
theorem bankTrialWindowInteriorRowsOfComponents {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hstage : BankTrialInteriorStagePreservation q)
    (hunique : BankTrialInteriorWorkerUniqueness q)
    (hcr : BankTrialInteriorCRPrefixPreservation q)
    (hcl : BankTrialInteriorCLFullPreservation q) :
    BankTrialLiveWindowInteriorRows (q := q) ring root := by
  exact bankTrialWindowInteriorRowsOfPairRows ring root
    (bankTrialInteriorPairRowsOfComponents q
      hstage hunique hcr hcl)

end L3


/-!
Literal interior BANK owner cases.

An old single-worker BANK pair can move its worker left or
right, keep it, or erase it; none of its ordinary first-match
branches duplicates it. In CWAIT the palette CR/CL does not
write bits, so CR1 and CL1 genealogy have the source-level
proof by the checked-prefix and full-word cases.

The following are proof candidates for individual literal rows.
The universal BankTrialLiveInteriorPairRows q is not falsely
asserted as a theorem. Its four component Props remain open
pending their full index-by-index Lean proofs.
-/

namespace L3

set_option autoImplicit false
set_option Elab.async false

private theorem bankTrialInteriorRoles
    (b : Nat) (x y : BankCell)
    (hx : 1 ≤ x.role) (hlt : x.role < b)
    (hy : y.role = x.role + 1) :
    x.role ≠ 0 ∧ x.role ≠ b ∧ y.role ≠ 0 ∧
    1 ≤ y.role ∧ y.role ≤ b ∧ x.role ≤ b := by
  omega

/-- An outgoing RR becomes the sole RR at the responder. -/
theorem bankTrialInteriorRRForward
    (b : Nat) (theta : Nat → Bool) (x y : BankCell)
    (hx : 1 ≤ x.role) (hlt : x.role < b)
    (hy : y.role = x.role + 1)
    (hxt : x.tok = .RR) (hyt : y.tok = .E) :
    (bankPair x y y.role b theta).1.tok = .E ∧
    (bankPair x y y.role b theta).2.tok = .RR ∧
    (bankPair x y y.role b theta).2.bit = false := by
  obtain ⟨hxn, hxTop, hyn, hyPos, hyLe, hxLe⟩ :=
    bankTrialInteriorRoles b x y hx hlt hy
  simp [bankPair, hx, hlt, hy, hxn, hxTop,
    hyn, hyPos, hyLe, hxLe, hxt, hyt,
    Id.run_pure, Id.run_bind]

/-- Outgoing IR flips the destination and issues only one
IR or AL token, depending on the OLD destination bit. -/
theorem bankTrialInteriorIRForward
    (b : Nat) (theta : Nat → Bool) (x y : BankCell)
    (hx : 1 ≤ x.role) (hlt : x.role < b)
    (hy : y.role = x.role + 1)
    (hxt : x.tok = .IR) (hyt : y.tok = .E) :
    (bankPair x y y.role b theta).1.tok = .E ∧
    (bankPair x y y.role b theta).2.tok =
      (if y.bit then .IR else .AL) ∧
    (bankPair x y y.role b theta).2.bit = !y.bit := by
  obtain ⟨hxn, hxTop, hyn, hyPos, hyLe, hxLe⟩ :=
    bankTrialInteriorRoles b x y hx hlt hy
  simp [bankPair, hx, hlt, hy, hxn, hxTop,
    hyn, hyPos, hyLe, hxLe, hxt, hyt,
    Id.run_pure, Id.run_bind]

/-- Failed CR0 moves right without writing either digit bit. -/
theorem bankTrialInteriorCRZeroForward
    (b : Nat) (theta : Nat → Bool) (x y : BankCell)
    (hx : 1 ≤ x.role) (hlt : x.role < b)
    (hy : y.role = x.role + 1)
    (hxt : x.tok = .CR0) (hyt : y.tok = .E) :
    (bankPair x y y.role b theta).1.tok = .E ∧
    (bankPair x y y.role b theta).1.bit = x.bit ∧
    (bankPair x y y.role b theta).2.tok = .CR0 ∧
    (bankPair x y y.role b theta).2.bit = y.bit := by
  obtain ⟨hxn, hxTop, hyn, hyPos, hyLe, hxLe⟩ :=
    bankTrialInteriorRoles b x y hx hlt hy
  simp [bankPair, hx, hlt, hy, hxn, hxTop,
    hyn, hyPos, hyLe, hxLe, hxt, hyt,
    Id.run_pure, Id.run_bind]

/-- The failed CR0 at the top turns to CL0, preserving bits. -/
theorem bankTrialInteriorCRZeroTop
    (b : Nat) (theta : Nat → Bool) (x y : BankCell)
    (hx : 1 ≤ x.role) (hlt : x.role < b)
    (hy : y.role = x.role + 1)
    (htop : y.role = b)
    (hxt : x.tok = .E) (hyt : y.tok = .CR0) :
    (bankPair x y y.role b theta).1.tok = .CL0 ∧
    (bankPair x y y.role b theta).1.bit = x.bit ∧
    (bankPair x y y.role b theta).2.tok = .E ∧
    (bankPair x y y.role b theta).2.bit = y.bit := by
  obtain ⟨hxn, hxTop, hyn, hyPos, hyLe, hxLe⟩ :=
    bankTrialInteriorRoles b x y hx hlt hy
  have hc1 : ¬ b < x.role + 1 := by omega
  have hc2 : x.role + 1 = b := by omega
  have hc3 : b ≠ 0 := by omega
  simp [bankPair, hc1, hc2, hc3, hx, hlt, hy, htop,
    hxn, hxTop, hyn, hyPos, hyLe, hxLe,
    hxt, hyt, Id.run_pure, Id.run_bind]

/-- CL0 goes left and preserves the two checked bits. -/
theorem bankTrialInteriorCLZeroReturn
    (b : Nat) (theta : Nat → Bool) (x y : BankCell)
    (hx : 1 ≤ x.role) (hlt : x.role < b)
    (hy : y.role = x.role + 1)
    (hxt : x.tok = .E) (hyt : y.tok = .CL0) :
    (bankPair x y y.role b theta).1.tok = .CL0 ∧
    (bankPair x y y.role b theta).1.bit = x.bit ∧
    (bankPair x y y.role b theta).2.tok = .E ∧
    (bankPair x y y.role b theta).2.bit = y.bit := by
  obtain ⟨hxn, hxTop, hyn, hyPos, hyLe, hxLe⟩ :=
    bankTrialInteriorRoles b x y hx hlt hy
  have hc1 : ¬ b < x.role + 1 := by omega
  simp [bankPair, hc1, hx, hlt, hy, hxn, hxTop,
    hyn, hyPos, hyLe, hxLe, hxt, hyt,
    Id.run_pure, Id.run_bind]

/-- AL goes left without changing either digit. -/
theorem bankTrialInteriorALReturn
    (b : Nat) (theta : Nat → Bool) (x y : BankCell)
    (hx : 1 ≤ x.role) (hlt : x.role < b)
    (hy : y.role = x.role + 1)
    (hxt : x.tok = .E) (hyt : y.tok = .AL) :
    (bankPair x y y.role b theta).1.tok = .AL ∧
    (bankPair x y y.role b theta).1.bit = x.bit ∧
    (bankPair x y y.role b theta).2.tok = .E ∧
    (bankPair x y y.role b theta).2.bit = y.bit := by
  obtain ⟨hxn, hxTop, hyn, hyPos, hyLe, hxLe⟩ :=
    bankTrialInteriorRoles b x y hx hlt hy
  have hc1 : ¬ b < x.role + 1 := by omega
  simp [bankPair, hc1, hx, hlt, hy, hxn, hxTop,
    hyn, hyPos, hyLe, hxLe, hxt, hyt,
    Id.run_pure, Id.run_bind]

/-- RL goes left and clears the source bit, without splitting. -/
theorem bankTrialInteriorRLReturn
    (b : Nat) (theta : Nat → Bool) (x y : BankCell)
    (hx : 1 ≤ x.role) (hlt : x.role < b)
    (hy : y.role = x.role + 1)
    (hxt : x.tok = .E) (hyt : y.tok = .RL) :
    (bankPair x y y.role b theta).1.tok = .RL ∧
    (bankPair x y y.role b theta).1.bit = false ∧
    (bankPair x y y.role b theta).2.tok = .E ∧
    (bankPair x y y.role b theta).2.bit = y.bit := by
  obtain ⟨hxn, hxTop, hyn, hyPos, hyLe, hxLe⟩ :=
    bankTrialInteriorRoles b x y hx hlt hy
  have hc1 : ¬ b < x.role + 1 := by omega
  simp [bankPair, hc1, hx, hlt, hy, hxn, hxTop,
    hyn, hyPos, hyLe, hxLe, hxt, hyt,
    Id.run_pure, Id.run_bind]

/-- The top responder's old IR is erased before interior
forwarding can inspect it. -/
theorem bankTrialInteriorTopIRAbsorbed
    (b : Nat) (theta : Nat → Bool) (x y : BankCell)
    (hx : 1 ≤ x.role) (hlt : x.role < b)
    (hy : y.role = x.role + 1)
    (htop : y.role = b)
    (hxt : x.tok = .E) (hyt : y.tok = .IR) :
    (bankPair x y y.role b theta).1.tok = .E ∧
    (bankPair x y y.role b theta).2.tok = .E ∧
    (bankPair x y y.role b theta).1.bit = x.bit ∧
    (bankPair x y y.role b theta).2.bit = y.bit := by
  obtain ⟨hxn, hxTop, hyn, hyPos, hyLe, hxLe⟩ :=
    bankTrialInteriorRoles b x y hx hlt hy
  have hc1 : ¬ b < x.role + 1 := by omega
  have hc2 : x.role + 1 = b := by omega
  have hc3 : b ≠ 0 := by omega
  simp [bankPair, hc1, hc2, hc3, hx, hlt, hy, htop,
    hxn, hxTop, hyn, hyPos, hyLe, hxLe,
    hxt, hyt, Id.run_pure, Id.run_bind]

/-- The old pair can have only one nonempty worker. Hence the
new pair has at least one E. Split on which side is initially
E and then only on the other token (never 9x9). -/
theorem bankTrialInteriorRawNoDoubleWorker
    (b : Nat) (theta : Nat → Bool) (x y : BankCell)
    (hx : 1 ≤ x.role) (hlt : x.role < b)
    (hy : y.role = x.role + 1)
    (hsolo : x.tok = .E ∨ y.tok = .E) :
    (bankPair x y y.role b theta).1.tok = .E ∨
    (bankPair x y y.role b theta).2.tok = .E := by
  obtain ⟨hxn, hxTop, hyn, hyPos, hyLe, hxLe⟩ :=
    bankTrialInteriorRoles b x y hx hlt hy
  rcases hsolo with he | he
  · cases ht : y.tok <;>
      simp [bankPair, hx, hlt, hy, hxn, hxTop,
        hyn, hyPos, hyLe, hxLe, he, ht,
        Id.run_pure, Id.run_bind] <;>
      (repeat' split) <;> simp
  · cases ht : x.tok <;>
      simp [bankPair, hx, hlt, hy, hxn, hxTop,
        hyn, hyPos, hyLe, hxLe, he, ht,
        Id.run_pure, Id.run_bind] <;>
      (repeat' split) <;> simp

/-- In CWAIT, only CR/CL tokens are possible, and with a
single worker the literal nonroot row writes neither bit.
There are at most five cases on either active token side. -/
theorem bankTrialInteriorRawComparisonBits
    (b : Nat) (theta : Nat → Bool) (x y : BankCell)
    (hx : 1 ≤ x.role) (hlt : x.role < b)
    (hy : y.role = x.role + 1)
    (hxs : x.tok = .E ∨ x.tok = .CR0 ∨
      x.tok = .CR1 ∨ x.tok = .CL0 ∨ x.tok = .CL1)
    (hys : y.tok = .E ∨ y.tok = .CR0 ∨
      y.tok = .CR1 ∨ y.tok = .CL0 ∨ y.tok = .CL1)
    (hsolo : x.tok = .E ∨ y.tok = .E) :
    (bankPair x y y.role b theta).1.bit = x.bit ∧
    (bankPair x y y.role b theta).2.bit = y.bit := by
  obtain ⟨hxn, hxTop, hyn, hyPos, hyLe, hxLe⟩ :=
    bankTrialInteriorRoles b x y hx hlt hy
  rcases hsolo with he | he
  · rcases hys with ht | ht | ht | ht | ht <;>
      simp [bankPair, hx, hlt, hy, hxn, hxTop,
        hyn, hyPos, hyLe, hxLe, he, ht,
        Id.run_pure, Id.run_bind] <;>
      (repeat' split) <;> simp
  · rcases hxs with ht | ht | ht | ht | ht <;>
      simp [bankPair, hx, hlt, hy, hxn, hxTop,
        hyn, hyPos, hyLe, hxLe, he, ht,
        Id.run_pure, Id.run_bind] <;>
      (repeat' split) <;> simp

end L3

/-!
Interior two-slot assembly.
This block introduces no additional named
Prop obligations and changes no physical or reference transition.
-/

namespace L3

set_option autoImplicit false
set_option Elab.async false

private abbrev bankTrialInteriorLeftCell {q : Nat}
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (j : Fin (compileAdvice q).b) : BankCell :=
  GrantBankReference.bankLocalReferenceCell B
    ⟨j.val, by omega⟩

private abbrev bankTrialInteriorRightCell {q : Nat}
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (j : Fin (compileAdvice q).b) : BankCell :=
  GrantBankReference.bankLocalReferenceCell B
    ⟨j.val + 1, by omega⟩

private def bankTrialInteriorLeftDigit {q : Nat}
    (j : Fin (compileAdvice q).b)
    (hj : 0 < j.val) : Fin (compileAdvice q).b :=
  ⟨j.val - 1, by omega⟩

private theorem bankTrialInteriorLeftDigitVal {q : Nat}
    (j : Fin (compileAdvice q).b)
    (hj : 0 < j.val) :
    (bankTrialInteriorLeftDigit j hj).val + 1 = j.val := by
  simp [bankTrialInteriorLeftDigit]
  omega

private theorem bankTrialInteriorCellRoles {q : Nat}
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (j : Fin (compileAdvice q).b)
    (hj : 0 < j.val) :
    1 ≤ (bankTrialInteriorLeftCell B j).role ∧
    (bankTrialInteriorLeftCell B j).role < (compileAdvice q).b ∧
    (bankTrialInteriorRightCell B j).role =
      (bankTrialInteriorLeftCell B j).role + 1 := by
  change 1 ≤ j.val ∧ j.val < (compileAdvice q).b ∧
    j.val + 1 = j.val + 1
  exact ⟨hj, j.isLt, rfl⟩

private theorem bankTrialInteriorOldLeftToken {q : Nat}
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (j : Fin (compileAdvice q).b) (hj : 0 < j.val) :
    (bankTrialInteriorLeftCell B j).tok =
      bankTrialLiveWaveToken B
        (bankTrialInteriorLeftDigit j hj) := by
  change (B.fields ⟨j.val, by omega⟩).2.2.1 =
    (B.fields ⟨(bankTrialInteriorLeftDigit j hj).val + 1,
      by omega⟩).2.2.1
  simp only [bankTrialInteriorLeftDigitVal j hj]

private theorem bankTrialInteriorOldRightToken {q : Nat}
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (j : Fin (compileAdvice q).b) :
    (bankTrialInteriorRightCell B j).tok =
      bankTrialLiveWaveToken B j := by
  rfl

private theorem bankTrialInteriorOldLeftBit {q : Nat}
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (j : Fin (compileAdvice q).b) (hj : 0 < j.val) :
    (bankTrialInteriorLeftCell B j).bit =
      bankTrialLiveWaveBit B
        (bankTrialInteriorLeftDigit j hj) := by
  change (B.fields ⟨j.val, by omega⟩).2.1 =
    (B.fields ⟨(bankTrialInteriorLeftDigit j hj).val + 1,
      by omega⟩).2.1
  simp only [bankTrialInteriorLeftDigitVal j hj]

private theorem bankTrialInteriorOldRightBit {q : Nat}
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (j : Fin (compileAdvice q).b) :
    (bankTrialInteriorRightCell B j).bit =
      bankTrialLiveWaveBit B j := by
  rfl

private theorem bankTrialInteriorNewLeftToken {q : Nat}
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (j : Fin (compileAdvice q).b) (hj : 0 < j.val) :
    bankTrialLiveWaveToken (bankTrialWindowInteriorPatch B j)
      (bankTrialInteriorLeftDigit j hj) =
        (GrantBankReference.bankLocalReferenceInternalPair
          q B j).1.tok := by
  change ((bankTrialWindowInteriorPatch B j).fields
    ⟨(bankTrialInteriorLeftDigit j hj).val + 1,
      by omega⟩).2.2.1 =
      (GrantBankReference.bankLocalReferenceInternalPair q B j).1.tok
  simp only [bankTrialInteriorLeftDigitVal j hj]
  rw [bankTrialInteriorPatchSourceField B j]
  rfl

private theorem bankTrialInteriorNewRightToken {q : Nat}
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (j : Fin (compileAdvice q).b) :
    bankTrialLiveWaveToken (bankTrialWindowInteriorPatch B j) j =
      (GrantBankReference.bankLocalReferenceInternalPair
        q B j).2.tok := by
  change ((bankTrialWindowInteriorPatch B j).fields
    ⟨j.val + 1, by omega⟩).2.2.1 =
      (GrantBankReference.bankLocalReferenceInternalPair q B j).2.tok
  rw [bankTrialInteriorPatchTargetField B j]
  rfl

private theorem bankTrialInteriorNewLeftBit {q : Nat}
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (j : Fin (compileAdvice q).b) (hj : 0 < j.val) :
    bankTrialLiveWaveBit (bankTrialWindowInteriorPatch B j)
      (bankTrialInteriorLeftDigit j hj) =
        (GrantBankReference.bankLocalReferenceInternalPair
          q B j).1.bit := by
  change ((bankTrialWindowInteriorPatch B j).fields
    ⟨(bankTrialInteriorLeftDigit j hj).val + 1,
      by omega⟩).2.1 =
      (GrantBankReference.bankLocalReferenceInternalPair q B j).1.bit
  simp only [bankTrialInteriorLeftDigitVal j hj]
  rw [bankTrialInteriorPatchSourceField B j]
  rfl

private theorem bankTrialInteriorNewRightBit {q : Nat}
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (j : Fin (compileAdvice q).b) :
    bankTrialLiveWaveBit (bankTrialWindowInteriorPatch B j) j =
      (GrantBankReference.bankLocalReferenceInternalPair
        q B j).2.bit := by
  change ((bankTrialWindowInteriorPatch B j).fields
    ⟨j.val + 1, by omega⟩).2.1 =
      (GrantBankReference.bankLocalReferenceInternalPair q B j).2.bit
  rw [bankTrialInteriorPatchTargetField B j]
  rfl

/-- Distinct physical digit slots cannot both hold the old
worker, regardless of the root stage. -/
private theorem bankTrialInteriorOldPairSolo {q : Nat}
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (j : Fin (compileAdvice q).b) (hj : 0 < j.val)
    (hc : BankTrialLiveWaveCertificate q B) :
    (bankTrialInteriorLeftCell B j).tok = .E ∨
      (bankTrialInteriorRightCell B j).tok = .E := by
  by_cases hl : (bankTrialInteriorLeftCell B j).tok = .E
  · exact Or.inl hl
  · by_cases hr : (bankTrialInteriorRightCell B j).tok = .E
    · exact Or.inr hr
    · have hleft :
        bankTrialLiveWaveToken B
          (bankTrialInteriorLeftDigit j hj) ≠ .E := by
        rw [← bankTrialInteriorOldLeftToken B j hj]
        exact hl
      have hright : bankTrialLiveWaveToken B j ≠ .E := by
        rw [← bankTrialInteriorOldRightToken B j]
        exact hr
      have heq := hc.uniqueWorker
        (bankTrialInteriorLeftDigit j hj) j hleft hright
      have hval := congrArg Fin.val heq
      have hs := bankTrialInteriorLeftDigitVal j hj
      omega

private theorem bankTrialInteriorOutsideIndices {q : Nat}
    (j : Fin (compileAdvice q).b) (hj : 0 < j.val)
    (i : Fin (compileAdvice q).b)
    (hout : ¬ (i = bankTrialInteriorLeftDigit j hj ∨ i = j)) :
    i.val + 1 ≠ j.val ∧ i.val + 1 ≠ j.val + 1 := by
  constructor
  · intro h
    apply hout
    left
    apply Fin.ext
    have hv := bankTrialInteriorLeftDigitVal j hj
    omega
  · intro h
    apply hout
    right
    apply Fin.ext
    omega

/-- A predicate on the tokens of the two raw outputs, plus
the untouched-frame predicate, covers every new digit. -/
private theorem bankTrialInteriorTokenCases {q : Nat}
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (j : Fin (compileAdvice q).b) (hj : 0 < j.val)
    (P : BTok → Prop)
    (hold : ∀ i : Fin (compileAdvice q).b,
      P (bankTrialLiveWaveToken B i))
    (hleft : P ((GrantBankReference.bankLocalReferenceInternalPair
      q B j).1.tok))
    (hright : P ((GrantBankReference.bankLocalReferenceInternalPair
      q B j).2.tok)) :
    ∀ i : Fin (compileAdvice q).b,
      P (bankTrialLiveWaveToken
        (bankTrialWindowInteriorPatch B j) i) := by
  intro i
  by_cases hl : i = bankTrialInteriorLeftDigit j hj
  · rw [hl, bankTrialInteriorNewLeftToken B j hj]
    exact hleft
  · by_cases hr : i = j
    · rw [hr, bankTrialInteriorNewRightToken B j]
      exact hright
    · have ho := bankTrialInteriorOutsideIndices j hj i
        (by intro h; rcases h with h | h; exact hl h; exact hr h)
      rw [bankTrialInteriorPatchTokenFrame B j i ho.1 ho.2]
      exact hold i

/-! Literal single-worker stage closure. Only the token on
the nonempty side is split; the other side is fixed to E. -/
private theorem bankTrialInteriorRawComparisonClosed
    (b : Nat) (theta : Nat → Bool) (x y : BankCell)
    (hx : 1 ≤ x.role) (hlt : x.role < b)
    (hy : y.role = x.role + 1)
    (hsolo : x.tok = .E ∨ y.tok = .E)
    (hxs : x.tok = .E ∨ BankTrialLiveComparisonToken x.tok)
    (hys : y.tok = .E ∨ BankTrialLiveComparisonToken y.tok) :
    ((bankPair x y y.role b theta).1.tok = .E ∨
      BankTrialLiveComparisonToken
        ((bankPair x y y.role b theta).1.tok)) ∧
    ((bankPair x y y.role b theta).2.tok = .E ∨
      BankTrialLiveComparisonToken
        ((bankPair x y y.role b theta).2.tok)) := by
  obtain ⟨hxn, hxTop, hyn, hyPos, hyLe, hxLe⟩ :=
    bankTrialInteriorRoles b x y hx hlt hy
  change x.tok = .E ∨ x.tok = .CR0 ∨ x.tok = .CR1 ∨
    x.tok = .CL0 ∨ x.tok = .CL1 at hxs
  change y.tok = .E ∨ y.tok = .CR0 ∨ y.tok = .CR1 ∨
    y.tok = .CL0 ∨ y.tok = .CL1 at hys
  rcases hsolo with he | he
  · rcases hys with ht | ht | ht | ht | ht <;>
      simp [BankTrialLiveComparisonToken, bankPair, hx, hlt,
        hy, hxn, hxTop, hyn, hyPos, hyLe, hxLe,
        he, ht, Id.run_pure, Id.run_bind] <;>
      (repeat' split) <;> simp [BankTrialLiveComparisonToken] <;>
      exact (Classical.em _).symm
  · rcases hxs with ht | ht | ht | ht | ht <;>
      simp [BankTrialLiveComparisonToken, bankPair, hx, hlt,
        hy, hxn, hxTop, hyn, hyPos, hyLe, hxLe,
        he, ht, Id.run_pure, Id.run_bind] <;>
      (repeat' split) <;> simp [BankTrialLiveComparisonToken] <;>
      exact (Classical.em _).symm

private theorem bankTrialInteriorRawIncrementClosed
    (b : Nat) (theta : Nat → Bool) (x y : BankCell)
    (hx : 1 ≤ x.role) (hlt : x.role < b)
    (hy : y.role = x.role + 1)
    (hsolo : x.tok = .E ∨ y.tok = .E)
    (hxs : x.tok = .E ∨ x.tok = .IR ∨ x.tok = .AL)
    (hys : y.tok = .E ∨ y.tok = .IR ∨ y.tok = .AL) :
    ((bankPair x y y.role b theta).1.tok = .E ∨
      (bankPair x y y.role b theta).1.tok = .IR ∨
      (bankPair x y y.role b theta).1.tok = .AL) ∧
    ((bankPair x y y.role b theta).2.tok = .E ∨
      (bankPair x y y.role b theta).2.tok = .IR ∨
      (bankPair x y y.role b theta).2.tok = .AL) := by
  obtain ⟨hxn, hxTop, hyn, hyPos, hyLe, hxLe⟩ :=
    bankTrialInteriorRoles b x y hx hlt hy
  rcases hsolo with he | he
  · rcases hys with ht | ht | ht <;>
      simp [bankPair, hx, hlt, hy, hxn, hxTop, hyn,
        hyPos, hyLe, hxLe, he, ht, Id.run_pure,
        Id.run_bind] <;> (repeat' split) <;> simp
  · rcases hxs with ht | ht | ht <;>
      simp [bankPair, hx, hlt, hy, hxn, hxTop, hyn,
        hyPos, hyLe, hxLe, he, ht, Id.run_pure,
        Id.run_bind] <;> (repeat' split) <;> simp

private theorem bankTrialInteriorRawResetClosed
    (b : Nat) (theta : Nat → Bool) (x y : BankCell)
    (hx : 1 ≤ x.role) (hlt : x.role < b)
    (hy : y.role = x.role + 1)
    (hsolo : x.tok = .E ∨ y.tok = .E)
    (hxs : x.tok = .E ∨ x.tok = .RR ∨ x.tok = .RL)
    (hys : y.tok = .E ∨ y.tok = .RR ∨ y.tok = .RL) :
    ((bankPair x y y.role b theta).1.tok = .E ∨
      (bankPair x y y.role b theta).1.tok = .RR ∨
      (bankPair x y y.role b theta).1.tok = .RL) ∧
    ((bankPair x y y.role b theta).2.tok = .E ∨
      (bankPair x y y.role b theta).2.tok = .RR ∨
      (bankPair x y y.role b theta).2.tok = .RL) := by
  obtain ⟨hxn, hxTop, hyn, hyPos, hyLe, hxLe⟩ :=
    bankTrialInteriorRoles b x y hx hlt hy
  rcases hsolo with he | he
  · rcases hys with ht | ht | ht <;>
      simp [bankPair, hx, hlt, hy, hxn, hxTop, hyn,
        hyPos, hyLe, hxLe, he, ht, Id.run_pure,
        Id.run_bind] <;> (repeat' split) <;> simp
  · rcases hxs with ht | ht | ht <;>
      simp [bankPair, hx, hlt, hy, hxn, hxTop, hyn,
        hyPos, hyLe, hxLe, he, ht, Id.run_pure,
        Id.run_bind] <;> (repeat' split) <;> simp

/-- First component: the stage palettes remain closed. -/
theorem bankTrialInteriorStagePreservation (q : Nat) :
    BankTrialInteriorStagePreservation q := by
  intro B j hj hc hnr
  have hsolo := bankTrialInteriorOldPairSolo B j hj hc
  have ⟨hx, hlt, hy⟩ := bankTrialInteriorCellRoles B j hj
  have hroot := bankTrialInteriorPatchRootMode B j hj
  refine {
    cwaitTokens := ?_,
    iwaitTokens := ?_,
    headClear := ?_,
    resetTokens := ?_
  }
  · intro i hm
    rw [hroot] at hm
    have hxs := hc.cwaitTokens
      (bankTrialInteriorLeftDigit j hj) hm
    have hys := hc.cwaitTokens j hm
    rw [← bankTrialInteriorOldLeftToken B j hj] at hxs
    rw [← bankTrialInteriorOldRightToken B j] at hys
    have hp := bankTrialInteriorRawComparisonClosed
      (compileAdvice q).b (compileAdvice q).theta
      (bankTrialInteriorLeftCell B j)
      (bankTrialInteriorRightCell B j)
      hx hlt hy hsolo hxs hys
    exact bankTrialInteriorTokenCases B j hj
      (fun t => t = .E ∨ BankTrialLiveComparisonToken t)
      (fun k => hc.cwaitTokens k hm) hp.1 hp.2 i
  · intro i hm
    rw [hroot] at hm
    have hxs := hc.iwaitTokens
      (bankTrialInteriorLeftDigit j hj) hm
    have hys := hc.iwaitTokens j hm
    rw [← bankTrialInteriorOldLeftToken B j hj] at hxs
    rw [← bankTrialInteriorOldRightToken B j] at hys
    have hp := bankTrialInteriorRawIncrementClosed
      (compileAdvice q).b (compileAdvice q).theta
      (bankTrialInteriorLeftCell B j)
      (bankTrialInteriorRightCell B j)
      hx hlt hy hsolo hxs hys
    exact bankTrialInteriorTokenCases B j hj
      (fun t => t = .E ∨ t = .IR ∨ t = .AL)
      (fun k => hc.iwaitTokens k hm) hp.1 hp.2 i
  · intro i hm
    rw [hroot] at hm
    have hold : ∀ k : Fin (compileAdvice q).b,
        bankTrialLiveWaveToken B k = .E :=
      fun k => hc.headClear k hm
    have hxs : (bankTrialInteriorLeftCell B j).tok = .E := by
      rw [bankTrialInteriorOldLeftToken B j hj]
      exact hold (bankTrialInteriorLeftDigit j hj)
    have hys : (bankTrialInteriorRightCell B j).tok = .E := by
      rw [bankTrialInteriorOldRightToken B j]
      exact hold j
    have hp := bankTrialInteriorRawEmptyPair
      (compileAdvice q).b (compileAdvice q).theta
      (bankTrialInteriorLeftCell B j)
      (bankTrialInteriorRightCell B j)
      hx hlt hy hxs hys
    exact bankTrialInteriorTokenCases B j hj
      (fun t => t = .E) hold hp.1 hp.2.1 i
  · intro i hm
    rw [hroot] at hm
    have hxs := hc.resetTokens
      (bankTrialInteriorLeftDigit j hj) hm
    have hys := hc.resetTokens j hm
    rw [← bankTrialInteriorOldLeftToken B j hj] at hxs
    rw [← bankTrialInteriorOldRightToken B j] at hys
    have hp := bankTrialInteriorRawResetClosed
      (compileAdvice q).b (compileAdvice q).theta
      (bankTrialInteriorLeftCell B j)
      (bankTrialInteriorRightCell B j)
      hx hlt hy hsolo hxs hys
    exact bankTrialInteriorTokenCases B j hj
      (fun t => t = .E ∨ t = .RR ∨ t = .RL)
      (fun k => hc.resetTokens k hm) hp.1 hp.2 i

/-- A nonempty output at one of the touched slots had an
old worker at one of the same two slots. -/
private theorem bankTrialInteriorPairOldWitness {q : Nat}
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (j : Fin (compileAdvice q).b) (hj : 0 < j.val)
    (hnew :
      (GrantBankReference.bankLocalReferenceInternalPair
        q B j).1.tok ≠ .E ∨
      (GrantBankReference.bankLocalReferenceInternalPair
        q B j).2.tok ≠ .E) :
    (bankTrialInteriorLeftCell B j).tok ≠ .E ∨
      (bankTrialInteriorRightCell B j).tok ≠ .E := by
  by_cases hxs : (bankTrialInteriorLeftCell B j).tok = .E
  · by_cases hys : (bankTrialInteriorRightCell B j).tok = .E
    · obtain ⟨hleft, hright, _, _⟩ :=
        bankTrialInteriorRawEmptyPair
          (compileAdvice q).b (compileAdvice q).theta
          (bankTrialInteriorLeftCell B j)
          (bankTrialInteriorRightCell B j)
          (bankTrialInteriorCellRoles B j hj).1
          (bankTrialInteriorCellRoles B j hj).2.1
          (bankTrialInteriorCellRoles B j hj).2.2
          hxs hys
      rcases hnew with h | h
      · exact False.elim (h hleft)
      · exact False.elim (h hright)
    · exact Or.inr hys
  · exact Or.inl hxs

private theorem bankTrialInteriorNewPairSolo {q : Nat}
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (j : Fin (compileAdvice q).b) (hj : 0 < j.val)
    (hc : BankTrialLiveWaveCertificate q B) :
    bankTrialLiveWaveToken (bankTrialWindowInteriorPatch B j)
      (bankTrialInteriorLeftDigit j hj) = .E ∨
    bankTrialLiveWaveToken (bankTrialWindowInteriorPatch B j)
      j = .E := by
  rw [bankTrialInteriorNewLeftToken B j hj,
    bankTrialInteriorNewRightToken B j]
  have hroles := bankTrialInteriorCellRoles B j hj
  exact bankTrialInteriorRawNoDoubleWorker
    (compileAdvice q).b (compileAdvice q).theta
    (bankTrialInteriorLeftCell B j)
    (bankTrialInteriorRightCell B j)
    hroles.1 hroles.2.1 hroles.2.2
    (bankTrialInteriorOldPairSolo B j hj hc)

/-- An untouched nonempty worker cannot coexist with a
new nonempty token on either touched slot. -/
private theorem bankTrialInteriorOutsideAgainstPair {q : Nat}
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (j : Fin (compileAdvice q).b) (hj : 0 < j.val)
    (hc : BankTrialLiveWaveCertificate q B)
    (i : Fin (compileAdvice q).b)
    (hout : ¬ (i = bankTrialInteriorLeftDigit j hj ∨ i = j))
    (hi : bankTrialLiveWaveToken
      (bankTrialWindowInteriorPatch B j) i ≠ .E)
    (hpair :
      bankTrialLiveWaveToken (bankTrialWindowInteriorPatch B j)
        (bankTrialInteriorLeftDigit j hj) ≠ .E ∨
      bankTrialLiveWaveToken (bankTrialWindowInteriorPatch B j)
        j ≠ .E) : False := by
  have houtside := bankTrialInteriorOutsideIndices j hj i hout
  have hframe := bankTrialInteriorPatchTokenFrame
    B j i houtside.1 houtside.2
  have hiold : bankTrialLiveWaveToken B i ≠ .E := by
    rw [hframe] at hi
    exact hi
  have hraw :
      (GrantBankReference.bankLocalReferenceInternalPair
        q B j).1.tok ≠ .E ∨
      (GrantBankReference.bankLocalReferenceInternalPair
        q B j).2.tok ≠ .E := by
    rcases hpair with hleft | hright
    · left
      rw [bankTrialInteriorNewLeftToken B j hj] at hleft
      exact hleft
    · right
      rw [bankTrialInteriorNewRightToken B j] at hright
      exact hright
  rcases bankTrialInteriorPairOldWitness B j hj hraw
      with hleft | hright
  · have hold : bankTrialLiveWaveToken B
        (bankTrialInteriorLeftDigit j hj) ≠ .E := by
      rw [← bankTrialInteriorOldLeftToken B j hj]
      exact hleft
    have heq := hc.uniqueWorker i
      (bankTrialInteriorLeftDigit j hj) hiold hold
    exact hout (Or.inl heq)
  · have hold : bankTrialLiveWaveToken B j ≠ .E := by
      rw [← bankTrialInteriorOldRightToken B j]
      exact hright
    have heq := hc.uniqueWorker i j hiold hold
    exact hout (Or.inr heq)

/-- Second component: frame, old uniqueness, and the literal
single-worker local owner show global new uniqueness. -/
theorem bankTrialInteriorWorkerUniqueness (q : Nat) :
    BankTrialInteriorWorkerUniqueness q := by
  intro B j hj hc hnr i k hi hk
  have hpair := bankTrialInteriorNewPairSolo B j hj hc
  by_cases hit : i = bankTrialInteriorLeftDigit j hj ∨ i = j
  · by_cases hkt : k = bankTrialInteriorLeftDigit j hj ∨ k = j
    · rcases hit with his | hit
      · rcases hkt with hks | hkt
        · exact his.trans hks.symm
        · have hleft :
            bankTrialLiveWaveToken
              (bankTrialWindowInteriorPatch B j)
              (bankTrialInteriorLeftDigit j hj) ≠ .E := by
              rw [← his]
              exact hi
          have hright :
            bankTrialLiveWaveToken
              (bankTrialWindowInteriorPatch B j) j ≠ .E := by
              exact fun he => hk (by rw [hkt]; exact he)
          rcases hpair with he | he
          · exact False.elim (hleft he)
          · exact False.elim (hright he)
      · rcases hkt with hks | hkt
        · have hleft :
            bankTrialLiveWaveToken
              (bankTrialWindowInteriorPatch B j)
              (bankTrialInteriorLeftDigit j hj) ≠ .E := by
              rw [← hks]
              exact hk
          have hright :
            bankTrialLiveWaveToken
              (bankTrialWindowInteriorPatch B j) j ≠ .E := by
              exact fun he => hi (by rw [hit]; exact he)
          rcases hpair with he | he
          · exact False.elim (hleft he)
          · exact False.elim (hright he)
        · exact hit.trans hkt.symm
    · have hp :
        bankTrialLiveWaveToken (bankTrialWindowInteriorPatch B j)
          (bankTrialInteriorLeftDigit j hj) ≠ .E ∨
        bankTrialLiveWaveToken (bankTrialWindowInteriorPatch B j)
          j ≠ .E := by
          rcases hit with his | hit
          · exact Or.inl (by rw [← his]; exact hi)
          · exact Or.inr (fun he => hi (by rw [hit]; exact he))
      exact False.elim
        (bankTrialInteriorOutsideAgainstPair B j hj hc
          k hkt hk hp)
  · by_cases hkt : k = bankTrialInteriorLeftDigit j hj ∨ k = j
    · have hp :
        bankTrialLiveWaveToken (bankTrialWindowInteriorPatch B j)
          (bankTrialInteriorLeftDigit j hj) ≠ .E ∨
        bankTrialLiveWaveToken (bankTrialWindowInteriorPatch B j)
          j ≠ .E := by
          rcases hkt with hks | hkt
          · exact Or.inl (by rw [← hks]; exact hk)
          · exact Or.inr (fun he => hk (by rw [hkt]; exact he))
      exact False.elim
        (bankTrialInteriorOutsideAgainstPair B j hj hc
          i hit hi hp)
    · have hio := bankTrialInteriorOutsideIndices j hj i hit
      have hko := bankTrialInteriorOutsideIndices j hj k hkt
      have hiold : bankTrialLiveWaveToken B i ≠ .E := by
        rw [bankTrialInteriorPatchTokenFrame
          B j i hio.1 hio.2] at hi
        exact hi
      have hkold : bankTrialLiveWaveToken B k ≠ .E := by
        rw [bankTrialInteriorPatchTokenFrame
          B j k hko.1 hko.2] at hk
        exact hk
      exact hc.uniqueWorker i k hiold hkold

/-- Bitwise conservation under CWAIT: the unique worker is
comparison-only; each touched bit is therefore a literal frame. -/
private theorem bankTrialInteriorComparisonBitsPreserved {q : Nat}
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (j : Fin (compileAdvice q).b) (hj : 0 < j.val)
    (hc : BankTrialLiveWaveCertificate q B)
    (hm : bankTrialLiveWaveRootMode B = .CWAIT) :
    ∀ k : Fin (compileAdvice q).b,
      bankTrialLiveWaveBit
        (bankTrialWindowInteriorPatch B j) k =
          bankTrialLiveWaveBit B k := by
  have hsolo := bankTrialInteriorOldPairSolo B j hj hc
  have ⟨hx, hlt, hy⟩ := bankTrialInteriorCellRoles B j hj
  have hxs := hc.cwaitTokens
    (bankTrialInteriorLeftDigit j hj) hm
  have hys := hc.cwaitTokens j hm
  rw [← bankTrialInteriorOldLeftToken B j hj] at hxs
  rw [← bankTrialInteriorOldRightToken B j] at hys
  have hxs' :
      (bankTrialInteriorLeftCell B j).tok = .E ∨
      (bankTrialInteriorLeftCell B j).tok = .CR0 ∨
      (bankTrialInteriorLeftCell B j).tok = .CR1 ∨
      (bankTrialInteriorLeftCell B j).tok = .CL0 ∨
      (bankTrialInteriorLeftCell B j).tok = .CL1 := by
    simpa only [BankTrialLiveComparisonToken] using hxs
  have hys' :
      (bankTrialInteriorRightCell B j).tok = .E ∨
      (bankTrialInteriorRightCell B j).tok = .CR0 ∨
      (bankTrialInteriorRightCell B j).tok = .CR1 ∨
      (bankTrialInteriorRightCell B j).tok = .CL0 ∨
      (bankTrialInteriorRightCell B j).tok = .CL1 := by
    simpa only [BankTrialLiveComparisonToken] using hys
  have hp := bankTrialInteriorRawComparisonBits
    (compileAdvice q).b (compileAdvice q).theta
    (bankTrialInteriorLeftCell B j)
    (bankTrialInteriorRightCell B j)
    hx hlt hy hxs' hys' hsolo
  intro k
  by_cases hl : k = bankTrialInteriorLeftDigit j hj
  · rw [hl, bankTrialInteriorNewLeftBit B j hj,
      ← bankTrialInteriorOldLeftBit B j hj]
    exact hp.1
  · by_cases hr : k = j
    · rw [hr, bankTrialInteriorNewRightBit B j,
        ← bankTrialInteriorOldRightBit B j]
      exact hp.2
    · have ho := bankTrialInteriorOutsideIndices j hj k
        (by intro h; rcases h with h | h; exact hl h; exact hr h)
      exact bankTrialInteriorPatchBitFrame B j k ho.1 ho.2

/-- Local genealogy rows. A CR1 is never output on the left;
a CL1 is never output on the right. -/
private theorem bankTrialInteriorRawLeftNotCR
    (b : Nat) (theta : Nat → Bool) (x y : BankCell)
    (hx : 1 ≤ x.role) (hlt : x.role < b)
    (hy : y.role = x.role + 1)
    (hsolo : x.tok = .E ∨ y.tok = .E) :
    (bankPair x y y.role b theta).1.tok ≠ .CR1 := by
  obtain ⟨hxn, hxTop, hyn, hyPos, hyLe, hxLe⟩ :=
    bankTrialInteriorRoles b x y hx hlt hy
  rcases hsolo with he | he
  · cases ht : y.tok <;>
      simp [bankPair, hx, hlt, hy, hxn, hxTop,
        hyn, hyPos, hyLe, hxLe, he, ht,
        Id.run_pure, Id.run_bind] <;>
      (repeat' split) <;> simp
  · cases ht : x.tok <;>
      simp [bankPair, hx, hlt, hy, hxn, hxTop,
        hyn, hyPos, hyLe, hxLe, he, ht,
        Id.run_pure, Id.run_bind] <;>
      (repeat' split) <;> simp

private theorem bankTrialInteriorRawRightNotCL
    (b : Nat) (theta : Nat → Bool) (x y : BankCell)
    (hx : 1 ≤ x.role) (hlt : x.role < b)
    (hy : y.role = x.role + 1)
    (hsolo : x.tok = .E ∨ y.tok = .E) :
    (bankPair x y y.role b theta).2.tok ≠ .CL1 := by
  obtain ⟨hxn, hxTop, hyn, hyPos, hyLe, hxLe⟩ :=
    bankTrialInteriorRoles b x y hx hlt hy
  rcases hsolo with he | he
  · cases ht : y.tok <;>
      simp [bankPair, hx, hlt, hy, hxn, hxTop,
        hyn, hyPos, hyLe, hxLe, he, ht,
        Id.run_pure, Id.run_bind] <;>
      (repeat' split) <;> simp
  · cases ht : x.tok <;>
      simp [bankPair, hx, hlt, hy, hxn, hxTop,
        hyn, hyPos, hyLe, hxLe, he, ht,
        Id.run_pure, Id.run_bind] <;>
      (repeat' split) <;> simp

/-- Right CR1 can only be an old right CR1, or an old left
CR1 passing the comparison test at the right digit. -/
private theorem bankTrialInteriorRawRightCRAncestor
    (b : Nat) (theta : Nat → Bool) (x y : BankCell)
    (hx : 1 ≤ x.role) (hlt : x.role < b)
    (hy : y.role = x.role + 1)
    (hsolo : x.tok = .E ∨ y.tok = .E)
    (hnew : (bankPair x y y.role b theta).2.tok = .CR1) :
    (x.tok = .CR1 ∧ y.bit = theta (y.role - 1)) ∨
      y.tok = .CR1 := by
  obtain ⟨hxn, hxTop, hyn, hyPos, hyLe, hxLe⟩ :=
    bankTrialInteriorRoles b x y hx hlt hy
  rcases hsolo with he | he
  · cases ht : y.tok <;>
      simp [bankPair, hx, hlt, hy, hxn, hxTop,
        hyn, hyPos, hyLe, hxLe, he, ht,
        Id.run_pure, Id.run_bind] at hnew ⊢ <;>
      (repeat' split at hnew) <;>
      simp [*] at hnew ⊢
  · cases ht : x.tok <;>
      simp [bankPair, hx, hlt, hy, hxn, hxTop,
        hyn, hyPos, hyLe, hxLe, he, ht,
        Id.run_pure, Id.run_bind] at hnew ⊢ <;>
      (repeat' split at hnew) <;>
      simp [*] at hnew ⊢

/-- Left CL1 is either inherited, returned from CL1, or
created from the last digit's old CR1. -/
private theorem bankTrialInteriorRawLeftCLAncestor
    (b : Nat) (theta : Nat → Bool) (x y : BankCell)
    (hx : 1 ≤ x.role) (hlt : x.role < b)
    (hy : y.role = x.role + 1)
    (hsolo : x.tok = .E ∨ y.tok = .E)
    (hnew : (bankPair x y y.role b theta).1.tok = .CL1) :
    x.tok = .CL1 ∨ y.tok = .CL1 ∨
      (y.tok = .CR1 ∧ y.role = b) := by
  obtain ⟨hxn, hxTop, hyn, hyPos, hyLe, hxLe⟩ :=
    bankTrialInteriorRoles b x y hx hlt hy
  rcases hsolo with he | he
  · cases ht : y.tok <;>
      simp [bankPair, hx, hlt, hy, hxn, hxTop,
        hyn, hyPos, hyLe, hxLe, he, ht,
        Id.run_pure, Id.run_bind] at hnew ⊢ <;>
      (repeat' split at hnew) <;>
      simp [*] at hnew ⊢
  · cases ht : x.tok <;>
      simp [bankPair, hx, hlt, hy, hxn, hxTop,
        hyn, hyPos, hyLe, hxLe, he, ht,
        Id.run_pure, Id.run_bind] at hnew ⊢ <;>
      (repeat' split at hnew) <;>
      simp [*] at hnew ⊢

/-- Third component: outside the pair the old CR1 prefix is
framed; at the right endpoint it is inherited or extended
by exactly the authenticated new comparison bit. -/
theorem bankTrialInteriorCRPrefixPreservation (q : Nat) :
    BankTrialInteriorCRPrefixPreservation q := by
  intro B j hj hc hnr i hnew k hk
  have hs := bankTrialInteriorStagePreservation q B j hj hc hnr
  have hroot := bankTrialInteriorPatchRootMode B j hj
  have hnnew :
      bankTrialLiveWaveRootMode
        (bankTrialWindowInteriorPatch B j) ≠ .RESET := by
    rw [hroot]
    exact hnr
  have hmNew := bankTrialInteriorComparisonModeOfStages
    (bankTrialWindowInteriorPatch B j) hs hnnew i (Or.inl hnew)
  have hm : bankTrialLiveWaveRootMode B = .CWAIT := by
    rw [hroot] at hmNew
    exact hmNew
  have hbits := bankTrialInteriorComparisonBitsPreserved
    B j hj hc hm k
  rw [hbits]
  have hroles := bankTrialInteriorCellRoles B j hj
  have hsolo := bankTrialInteriorOldPairSolo B j hj hc
  by_cases his : i = bankTrialInteriorLeftDigit j hj
  · rw [his, bankTrialInteriorNewLeftToken B j hj] at hnew
    have hfalse := bankTrialInteriorRawLeftNotCR
      (compileAdvice q).b (compileAdvice q).theta
      (bankTrialInteriorLeftCell B j)
      (bankTrialInteriorRightCell B j)
      hroles.1 hroles.2.1 hroles.2.2 hsolo
    exact False.elim (hfalse hnew)
  · by_cases hit : i = j
    · rw [hit, bankTrialInteriorNewRightToken B j] at hnew
      have hanc := bankTrialInteriorRawRightCRAncestor
        (compileAdvice q).b (compileAdvice q).theta
        (bankTrialInteriorLeftCell B j)
        (bankTrialInteriorRightCell B j)
        hroles.1 hroles.2.1 hroles.2.2 hsolo hnew
      rcases hanc with ⟨hleft, hmatch⟩ | hright
      · have hleftOld : bankTrialLiveWaveToken B
            (bankTrialInteriorLeftDigit j hj) = .CR1 := by
          rw [← bankTrialInteriorOldLeftToken B j hj]
          exact hleft
        by_cases hkl : k.val < j.val
        · exact hc.crPrefix (bankTrialInteriorLeftDigit j hj)
            hleftOld k (by
              have hv := bankTrialInteriorLeftDigitVal j hj
              omega)
        · have hkeq : k = j := Fin.ext (by
            have hval := congrArg Fin.val hit
            omega)
          rw [hkeq]
          have hpos :
              (bankTrialInteriorRightCell B j).role - 1 =
                j.val := by
            change j.val + 1 - 1 = j.val
            omega
          rw [← bankTrialInteriorOldRightBit B j]
          rw [hpos] at hmatch
          exact hmatch
      · have hrightOld : bankTrialLiveWaveToken B j = .CR1 := by
          rw [← bankTrialInteriorOldRightToken B j]
          exact hright
        have hk' : k.val ≤ j.val := by
          have hval := congrArg Fin.val hit
          omega
        exact hc.crPrefix j hrightOld k hk'
    · have ho := bankTrialInteriorOutsideIndices j hj i
        (by intro h; rcases h with h | h; exact his h; exact hit h)
      rw [bankTrialInteriorPatchTokenFrame
        B j i ho.1 ho.2] at hnew
      exact hc.crPrefix i hnew k hk

/-- Fourth component: the return token CL1 can only
inherit a full checked word or arise from a top CR1
whose checked prefix already contains every digit. -/
theorem bankTrialInteriorCLFullPreservation (q : Nat) :
    BankTrialInteriorCLFullPreservation q := by
  intro B j hj hc hnr i hnew k
  have hs := bankTrialInteriorStagePreservation q B j hj hc hnr
  have hroot := bankTrialInteriorPatchRootMode B j hj
  have hnnew :
      bankTrialLiveWaveRootMode
        (bankTrialWindowInteriorPatch B j) ≠ .RESET := by
    rw [hroot]
    exact hnr
  have hmNew := bankTrialInteriorComparisonModeOfStages
    (bankTrialWindowInteriorPatch B j) hs hnnew i (Or.inr hnew)
  have hm : bankTrialLiveWaveRootMode B = .CWAIT := by
    rw [hroot] at hmNew
    exact hmNew
  have hbits := bankTrialInteriorComparisonBitsPreserved
    B j hj hc hm k
  rw [hbits]
  have hroles := bankTrialInteriorCellRoles B j hj
  have hsolo := bankTrialInteriorOldPairSolo B j hj hc
  by_cases his : i = bankTrialInteriorLeftDigit j hj
  · rw [his, bankTrialInteriorNewLeftToken B j hj] at hnew
    have hanc := bankTrialInteriorRawLeftCLAncestor
      (compileAdvice q).b (compileAdvice q).theta
      (bankTrialInteriorLeftCell B j)
      (bankTrialInteriorRightCell B j)
      hroles.1 hroles.2.1 hroles.2.2 hsolo hnew
    rcases hanc with hleft | hright | ⟨hright, htop⟩
    · have hold : bankTrialLiveWaveToken B
          (bankTrialInteriorLeftDigit j hj) = .CL1 := by
        rw [← bankTrialInteriorOldLeftToken B j hj]
        exact hleft
      exact hc.clAll (bankTrialInteriorLeftDigit j hj) hold k
    · have hold : bankTrialLiveWaveToken B j = .CL1 := by
        rw [← bankTrialInteriorOldRightToken B j]
        exact hright
      exact hc.clAll j hold k
    · have hold : bankTrialLiveWaveToken B j = .CR1 := by
        rw [← bankTrialInteriorOldRightToken B j]
        exact hright
      have hlast : j.val + 1 = (compileAdvice q).b := by
        exact htop
      exact hc.crPrefix j hold k (by
        have hk := k.isLt
        omega)
  · by_cases hit : i = j
    · rw [hit, bankTrialInteriorNewRightToken B j] at hnew
      have hfalse := bankTrialInteriorRawRightNotCL
        (compileAdvice q).b (compileAdvice q).theta
        (bankTrialInteriorLeftCell B j)
        (bankTrialInteriorRightCell B j)
        hroles.1 hroles.2.1 hroles.2.2 hsolo
      exact False.elim (hfalse hnew)
    · have ho := bankTrialInteriorOutsideIndices j hj i
        (by intro h; rcases h with h | h; exact his h; exact hit h)
      rw [bankTrialInteriorPatchTokenFrame
        B j i ho.1 ho.2] at hnew
      exact hc.clAll i hnew k

/-- All eight interior certificate clauses, unconditional on any
additional named row Prop. -/
theorem bankTrialLiveInteriorPairRows (q : Nat) :
    BankTrialLiveInteriorPairRows q := by
  exact bankTrialInteriorPairRowsOfComponents q
    (bankTrialInteriorStagePreservation q)
    (bankTrialInteriorWorkerUniqueness q)
    (bankTrialInteriorCRPrefixPreservation q)
    (bankTrialInteriorCLFullPreservation q)

end L3

/-!
The three remaining G11 LIVE boundary edge classes.
-/

namespace L3

/-- The BANK width is positive (b = s + 11). -/
theorem bankTrialWindowWidthPos (q : Nat) :
    0 < (compileAdvice q).b := by
  change 0 < (compileAdvice q).s + 11
  omega

set_option autoImplicit false
set_option Elab.async false

/-- A successor reported as LIVE cannot have its updated root in
RESET: that branch of the observer is RECOVERY, not LIVE. -/
private theorem bankTrialWindowNextLiveNonreset {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b) (begun nextBegun : Bool)
    (hnext : (bankTrialLocalNext ring root
      (⟨B, .live begun⟩ : BankTrialLocalState q) e).phase =
        .live nextBegun) :
    bankTrialLiveWaveRootMode
      (GrantBankReference.bankLocalReferenceStepClamped
        ring root B e) ≠ .RESET := by
  classical
  intro hreset
  have hr :
      ((GrantBankReference.bankLocalReferenceStepClamped
        ring root B e).fields ⟨0, by have := bankTrialWindowWidthPos q; omega⟩).1 = .RESET :=
    hreset
  by_cases hwin :
      (GrantBankReference.bankLocalReferenceStepClamped
        ring root B e).success = true
  · simp [bankTrialLocalNext, hwin] at hnext
  · by_cases hclean :
        BankTrialLocalClean q
          (GrantBankReference.bankLocalReferenceStepClamped
            ring root B e) ∧
        (begun = true ∨ e = root ∨ ring.rightNeighbor e = root)
    · simp [bankTrialLocalNext, hwin, hclean] at hnext
    · have hzero : (0 : Fin ((compileAdvice q).b + 1)) =
          ⟨0, by have := bankTrialWindowWidthPos q; omega⟩ := Fin.ext rfl
      rw [← hzero] at hr
      simp [bankTrialLocalNext, hwin, hclean, hr] at hnext

/-- Replacing any token by E, without changing old nonempty
tokens, bit values, or root mode, preserves the complete
eight-field stage and comparison genealogy certificate. -/
private theorem bankTrialWindowCertificateErase {q : Nat}
    (A B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hc : BankTrialLiveWaveCertificate q B)
    (hmode : bankTrialLiveWaveRootMode A =
      bankTrialLiveWaveRootMode B)
    (hbits : ∀ i : Fin (compileAdvice q).b,
      bankTrialLiveWaveBit A i = bankTrialLiveWaveBit B i)
    (htokens : ∀ i : Fin (compileAdvice q).b,
      bankTrialLiveWaveToken A i ≠ .E →
        bankTrialLiveWaveToken A i = bankTrialLiveWaveToken B i) :
    BankTrialLiveWaveCertificate q A := by
  have hold : ∀ i : Fin (compileAdvice q).b,
      bankTrialLiveWaveToken A i ≠ .E →
        bankTrialLiveWaveToken B i ≠ .E := by
    intro i ha hb
    exact ha ((htokens i ha).trans hb)
  refine {
    cwaitTokens := ?_, iwaitTokens := ?_,
    headClear := ?_, resetTokens := ?_,
    uniqueWorker := ?_, comparisonMode := ?_,
    crPrefix := ?_, clAll := ?_
  }
  · intro i hm
    rw [hmode] at hm
    by_cases he : bankTrialLiveWaveToken A i = .E
    · exact Or.inl he
    · rw [htokens i he]
      exact hc.cwaitTokens i hm
  · intro i hm
    rw [hmode] at hm
    by_cases he : bankTrialLiveWaveToken A i = .E
    · exact Or.inl he
    · rw [htokens i he]
      exact hc.iwaitTokens i hm
  · intro i hm
    rw [hmode] at hm
    by_cases he : bankTrialLiveWaveToken A i = .E
    · exact he
    · have hb := hc.headClear i hm
      exact False.elim ((hold i he) hb)
  · intro i hm
    rw [hmode] at hm
    by_cases he : bankTrialLiveWaveToken A i = .E
    · exact Or.inl he
    · rw [htokens i he]
      exact hc.resetTokens i hm
  · intro i k hi hk
    exact hc.uniqueWorker i k (hold i hi) (hold k hk)
  · intro i ht
    have hi : bankTrialLiveWaveToken A i ≠ .E := by
      intro he
      rcases ht with h | h
      · rw [he] at h
        cases h
      · rw [he] at h
        cases h
    rw [htokens i hi] at ht
    rw [hmode]
    exact hc.comparisonMode i ht
  · intro i ht k hk
    have hi : bankTrialLiveWaveToken A i ≠ .E := by
      intro he
      rw [he] at ht
      cases ht
    rw [htokens i hi] at ht
    rw [hbits]
    exact hc.crPrefix i ht k hk
  · intro i ht k
    have hi : bankTrialLiveWaveToken A i ≠ .E := by
      intro he
      rw [he] at ht
      cases ht
    rw [htokens i hi] at ht
    rw [hbits]
    exact hc.clAll i ht k

/-- With no workers, every stage and comparison clause is trivial. -/
private theorem bankTrialWindowCertificateEmpty {q : Nat}
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hempty : ∀ i : Fin (compileAdvice q).b,
      bankTrialLiveWaveToken B i = .E) :
    BankTrialLiveWaveCertificate q B := by
  refine {
    cwaitTokens := ?_, iwaitTokens := ?_,
    headClear := ?_, resetTokens := ?_,
    uniqueWorker := ?_, comparisonMode := ?_,
    crPrefix := ?_, clAll := ?_
  }
  · intro i _
    exact Or.inl (hempty i)
  · intro i _
    exact Or.inl (hempty i)
  · intro i _
    exact hempty i
  · intro i _
    exact Or.inl (hempty i)
  · intro i k hi _
    exact False.elim (hi (hempty i))
  · intro i ht
    rcases ht with ht | ht
    · rw [hempty i] at ht
      cases ht
    · rw [hempty i] at ht
      cases ht
  · intro i ht
    rw [hempty i] at ht
    cases ht
  · intro i ht
    rw [hempty i] at ht
    cases ht

/-- A root with exactly one newly issued first-digit worker
has a certificate when the issued IR or CR token matches the
new head mode and its CR1 bit is authenticated. -/
private theorem bankTrialWindowCertificateFirstDigit {q : Nat}
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (htail : ∀ i : Fin (compileAdvice q).b,
      i ≠ ⟨0, by have := bankTrialWindowWidthPos q; omega⟩ →
        bankTrialLiveWaveToken B i = .E)
    (hkind :
      (bankTrialLiveWaveRootMode B = .IWAIT ∧
        bankTrialLiveWaveToken B ⟨0, by have := bankTrialWindowWidthPos q; omega⟩ = .IR) ∨
      (bankTrialLiveWaveRootMode B = .CWAIT ∧
        (bankTrialLiveWaveToken B ⟨0, by have := bankTrialWindowWidthPos q; omega⟩ = .CR0 ∨
          (bankTrialLiveWaveToken B ⟨0, by have := bankTrialWindowWidthPos q; omega⟩ = .CR1 ∧
           bankTrialLiveWaveBit B ⟨0, by have := bankTrialWindowWidthPos q; omega⟩ =
             (compileAdvice q).theta 0)))) :
    BankTrialLiveWaveCertificate q B := by
  have hother : ∀ i : Fin (compileAdvice q).b,
      i ≠ ⟨0, by have := bankTrialWindowWidthPos q; omega⟩ →
        bankTrialLiveWaveToken B i = .E := htail
  refine {
    cwaitTokens := ?_, iwaitTokens := ?_,
    headClear := ?_, resetTokens := ?_,
    uniqueWorker := ?_, comparisonMode := ?_,
    crPrefix := ?_, clAll := ?_
  }
  · intro i hm
    rcases hkind with ⟨hr, _⟩ | ⟨hr, ht⟩
    · rw [hr] at hm
      cases hm
    · by_cases hi : i = ⟨0, by have := bankTrialWindowWidthPos q; omega⟩
      · rw [hi]
        rcases ht with ht | ⟨ht, _⟩
        · exact Or.inr (Or.inl ht)
        · exact Or.inr (Or.inr (Or.inl ht))
      · exact Or.inl (hother i hi)
  · intro i hm
    rcases hkind with ⟨hr, ht⟩ | ⟨hr, _⟩
    · by_cases hi : i = ⟨0, by have := bankTrialWindowWidthPos q; omega⟩
      · rw [hi]
        exact Or.inr (Or.inl ht)
      · exact Or.inl (hother i hi)
    · rw [hr] at hm
      cases hm
  · intro i hm
    rcases hkind with ⟨hr, _⟩ | ⟨hr, _⟩
    · rcases hm with hm | hm
      · rw [hr] at hm
        cases hm
      · rw [hr] at hm
        cases hm
    · rcases hm with hm | hm
      · rw [hr] at hm
        cases hm
      · rw [hr] at hm
        cases hm
  · intro i hm
    rcases hkind with ⟨hr, _⟩ | ⟨hr, _⟩
    · rw [hr] at hm
      cases hm
    · rw [hr] at hm
      cases hm
  · intro i k hi hk
    by_cases hi0 : i = ⟨0, by have := bankTrialWindowWidthPos q; omega⟩
    · by_cases hk0 : k = ⟨0, by have := bankTrialWindowWidthPos q; omega⟩
      · exact hi0.trans hk0.symm
      · exact False.elim (hk (hother k hk0))
    · exact False.elim (hi (hother i hi0))
  · intro i ht
    by_cases hi : i = ⟨0, by have := bankTrialWindowWidthPos q; omega⟩
    · rw [hi] at ht
      rcases hkind with ⟨hr, htok⟩ | ⟨hr, _⟩
      · rw [htok] at ht
        rcases ht with ht | ht <;> cases ht
      · exact hr
    · rw [hother i hi] at ht
      rcases ht with ht | ht <;> cases ht
  · intro i ht k hk
    by_cases hi : i = ⟨0, by have := bankTrialWindowWidthPos q; omega⟩
    · rw [hi] at ht
      rcases hkind with ⟨hr, htok⟩ |
          ⟨hr, htok⟩
      · rw [htok] at ht
        cases ht
      · rcases htok with hzero | ⟨hone, hmatch⟩
        · rw [hzero] at ht
          cases ht
        · have hkbound : k.val ≤ 0 := by
            have hiv : i.val = 0 := congrArg Fin.val hi
            omega
          have hkval : k.val = 0 := by omega
          have hkzero : k = ⟨0, by have := bankTrialWindowWidthPos q; omega⟩ :=
            Fin.ext hkval
          rw [hkzero]
          exact hmatch
    · rw [hother i hi] at ht
      cases ht
  · intro i ht k
    by_cases hi : i = ⟨0, by have := bankTrialWindowWidthPos q; omega⟩
    · rw [hi] at ht
      rcases hkind with ⟨_, htok⟩ | ⟨_, htok⟩
      · rw [htok] at ht
        cases ht
      · rcases htok with hzero | ⟨hone, _⟩
        · rw [hzero] at ht
          cases ht
        · rw [hone] at ht
          cases ht
    · rw [hother i hi] at ht
      cases ht

/-- A unary top slot is the sole changed protected field. -/
private noncomputable def bankTrialWindowTopPatch {q : Nat}
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b) :
    GrantBankReference.BankLocalReference
      (compileAdvice q).b :=
  { fields := fun i =>
      if i.val = (compileAdvice q).b then
        GrantBankReference.bankLocalReferenceClampedQuad q
          (GrantBankReference.topBoundaryBankMap
            (GrantBankReference.bankLocalReferenceCell B i))
      else B.fields i,
    success := B.success }

/-- The predecessor of top is a valid digit-token index. -/
private def bankTrialWindowTopDigit (q : Nat) :
    Fin (compileAdvice q).b :=
  ⟨(compileAdvice q).b - 1, by
    change (compileAdvice q).b - 1 <
      (compileAdvice q).b
    have hb : 0 < (compileAdvice q).b := by
      change 0 < (compileAdvice q).s + 11
      omega
    omega⟩

private theorem bankTrialWindowTopDigitVal (q : Nat) :
    (bankTrialWindowTopDigit q).val + 1 =
      (compileAdvice q).b := by
  simp [bankTrialWindowTopDigit]
  have hb : 0 < (compileAdvice q).b := by
    change 0 < (compileAdvice q).s + 11
    omega
  omega

private theorem bankTrialWindowTopPatchRootMode {q : Nat}
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b) :
    bankTrialLiveWaveRootMode (bankTrialWindowTopPatch B) =
      bankTrialLiveWaveRootMode B := by
  have hb : ¬ 0 = (compileAdvice q).b := by
    exact Nat.ne_of_lt (bankTrialWindowWidthPos q)
  simp [bankTrialLiveWaveRootMode, bankTrialWindowTopPatch, hb]

private theorem bankTrialWindowTopPatchBits {q : Nat}
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b) :
    ∀ i : Fin (compileAdvice q).b,
      bankTrialLiveWaveBit (bankTrialWindowTopPatch B) i =
        bankTrialLiveWaveBit B i := by
  intro i
  by_cases ht : i.val + 1 = (compileAdvice q).b
  · change
      (if i.val + 1 = (compileAdvice q).b then
        (GrantBankReference.bankLocalReferenceClampedQuad q
          (GrantBankReference.topBoundaryBankMap
            (GrantBankReference.bankLocalReferenceCell B
              ⟨i.val + 1, by omega⟩))) else
        B.fields ⟨i.val + 1, by omega⟩).2.1 =
        (B.fields ⟨i.val + 1, by omega⟩).2.1
    simp [ht, GrantBankReference.bankLocalReferenceClampedQuad,
      GrantBankReference.bankAgentLeaseQuad, copyBank,
      GrantBankReference.topBoundaryBankMap,
      GrantBankReference.bankLocalReferenceCell]
  · simp [bankTrialLiveWaveBit, bankTrialWindowTopPatch, ht]

private theorem bankTrialWindowTopPatchTokens {q : Nat}
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b) :
    ∀ i : Fin (compileAdvice q).b,
      bankTrialLiveWaveToken (bankTrialWindowTopPatch B) i ≠ .E →
        bankTrialLiveWaveToken (bankTrialWindowTopPatch B) i =
          bankTrialLiveWaveToken B i := by
  intro i hn
  by_cases ht : i.val + 1 = (compileAdvice q).b
  · have hselected :
        bankTrialLiveWaveToken (bankTrialWindowTopPatch B) i =
          (GrantBankReference.topBoundaryBankMap
            (GrantBankReference.bankLocalReferenceCell B
              ⟨i.val + 1, by omega⟩)).tok := by
      dsimp [bankTrialLiveWaveToken, bankTrialWindowTopPatch]
      rw [if_pos ht]
      exact (bankTrialLocalClampedData q
        (GrantBankReference.topBoundaryBankMap
          (GrantBankReference.bankLocalReferenceCell B
            ⟨i.val + 1, by omega⟩))).2
    have hcell :
        (GrantBankReference.bankLocalReferenceCell B
          ⟨i.val + 1, by omega⟩).tok =
          bankTrialLiveWaveToken B i := rfl
    by_cases hIR : bankTrialLiveWaveToken B i = .IR
    · have hIRcell :
          (GrantBankReference.bankLocalReferenceCell B
            ⟨i.val + 1, by omega⟩).tok = .IR := by
        rw [hcell]
        exact hIR
      have hE :
          (GrantBankReference.topBoundaryBankMap
            (GrantBankReference.bankLocalReferenceCell B
              ⟨i.val + 1, by omega⟩)).tok = .E := by
        simp [GrantBankReference.topBoundaryBankMap, hIRcell]
      rw [hselected] at hn
      exact False.elim (hn hE)
    · have hnotIRcell :
          (GrantBankReference.bankLocalReferenceCell B
            ⟨i.val + 1, by omega⟩).tok ≠ .IR := by
        rw [hcell]
        exact hIR
      calc
        bankTrialLiveWaveToken (bankTrialWindowTopPatch B) i =
            (GrantBankReference.topBoundaryBankMap
              (GrantBankReference.bankLocalReferenceCell B
                ⟨i.val + 1, by omega⟩)).tok := hselected
        _ = (GrantBankReference.bankLocalReferenceCell B
              ⟨i.val + 1, by omega⟩).tok :=
              bankTrialLiveTopMapNoIR
                (GrantBankReference.bankLocalReferenceCell B
                  ⟨i.val + 1, by omega⟩) hnotIRcell
        _ = bankTrialLiveWaveToken B i := hcell
  · simp [bankTrialLiveWaveToken, bankTrialWindowTopPatch, ht]

/-- On a sufficiently long ring, top service cannot coincide
with any internal protected source, responder, or incoming-root
selector; only the unary top field is updated. -/
private theorem bankTrialWindowTopFieldsEqPatch {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hw : BankTrialLiveWindowNonalias n q)
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hf : B.success = false) :
    (GrantBankReference.bankLocalReferenceStepClamped
      ring root B (Counter.site ring root (compileAdvice q).b)).fields =
        (bankTrialWindowTopPatch B).fields := by
  funext i
  have hs : Counter.Support q ring root
      (Counter.site ring root (compileAdvice q).b) :=
    Or.inr ⟨(compileAdvice q).b, by omega, rfl⟩
  have hb : 1 < (compileAdvice q).b := by
    change 1 < (compileAdvice q).s + 11
    omega
  by_cases ht : i.val = (compileAdvice q).b
  · have hx : ¬ (i.val < (compileAdvice q).b ∧
        Counter.site ring root (compileAdvice q).b =
          Counter.site ring root i.val) := by
      intro h
      omega
    have hy : ¬ (0 < i.val ∧
        Counter.site ring root (compileAdvice q).b =
          Counter.site ring root (i.val - 1)) := by
      intro h
      have hv := bankTrialWindowSitesDistinct ring root hw
        (compileAdvice q).b (i.val - 1)
        (by omega) (by omega) h.2
      omega
    rw [bankTrialLiveCarryTopSelected ring root
      (Counter.site ring root (compileAdvice q).b) B hs hf
      i hx hy ⟨ht, rfl⟩]
    simp [bankTrialWindowTopPatch, ht]
  · have hx : ¬ (i.val < (compileAdvice q).b ∧
        Counter.site ring root (compileAdvice q).b =
          Counter.site ring root i.val) := by
      intro h
      have hv := bankTrialWindowSitesDistinct ring root hw
        (compileAdvice q).b i.val
        (by omega) (by omega) h.2
      exact ht hv.symm
    have hy : ¬ (0 < i.val ∧
        Counter.site ring root (compileAdvice q).b =
          Counter.site ring root (i.val - 1)) := by
      intro h
      have hv := bankTrialWindowSitesDistinct ring root hw
        (compileAdvice q).b (i.val - 1)
        (by omega) (by omega) h.2
      have hi := i.isLt
      omega
    have htop : ¬ (i.val = (compileAdvice q).b ∧
        Counter.site ring root (compileAdvice q).b =
          Counter.site ring root (compileAdvice q).b) := by
      intro h
      exact ht h.1
    have hin : ¬ (i.val = 0 ∧
        ring.rightNeighbor
          (Counter.site ring root (compileAdvice q).b) = root) := by
      intro h
      have he :
          Counter.site ring root ((compileAdvice q).b + 1) =
            Counter.site ring root 0 := by
        exact h.2
      have hv := bankTrialWindowSitesDistinct ring root hw
        ((compileAdvice q).b + 1) 0 (by omega) (by omega) he
      omega
    rw [bankTrialLiveCarryUnselectedField ring root
      (Counter.site ring root (compileAdvice q).b)
      B hs hf i hx hy htop hin]
    simp [bankTrialWindowTopPatch, ht]

/-- The top unary row can only erase an IR; this keeps all
certificate fields, and the root is a literal frame. -/
theorem bankTrialWindowTopRows {n q : Nat}
    (ring : DirectedRing n) (root : Fin n) :
    BankTrialLiveWindowTopRows (q := q) ring root := by
  intro hw B begun hlock nextBegun hnext
  have hf := bankTrialWindowLiveOldNotLatched
    ring root (Counter.site ring root (compileAdvice q).b)
    B begun nextBegun hnext
  have hc : BankTrialLiveWaveCertificate q B :=
    hlock.1 begun rfl
  have hm : bankTrialLiveWaveRootMode B ≠ .RESET :=
    hlock.2 begun rfl
  have hfields := bankTrialWindowTopFieldsEqPatch
    ring root hw B hf
  have hcert := bankTrialWindowCertificateErase
    (bankTrialWindowTopPatch B) B hc
    (bankTrialWindowTopPatchRootMode B)
    (bankTrialWindowTopPatchBits B)
    (bankTrialWindowTopPatchTokens B)
  have hnew := bankTrialWindowCertificateFieldsCongr
    (GrantBankReference.bankLocalReferenceStepClamped
      ring root B (Counter.site ring root (compileAdvice q).b))
    (bankTrialWindowTopPatch B) hfields hcert
  have hbank := bankTrialLocalNextLiveBank
    ring root (Counter.site ring root (compileAdvice q).b)
    B begun
  constructor
  · intro flag _
    rw [hbank]
    exact hnew
  · intro flag _ hreset
    rw [hbank] at hreset
    have hraw : bankTrialLiveWaveRootMode
        (GrantBankReference.bankLocalReferenceStepClamped
          ring root B (Counter.site ring root (compileAdvice q).b)) =
        bankTrialLiveWaveRootMode B := by
      change ((GrantBankReference.bankLocalReferenceStepClamped
        ring root B (Counter.site ring root (compileAdvice q).b)).fields
          ⟨0, by have := bankTrialWindowWidthPos q; omega⟩).1 = (B.fields ⟨0, by have := bankTrialWindowWidthPos q; omega⟩).1
      rw [show (GrantBankReference.bankLocalReferenceStepClamped
        ring root B (Counter.site ring root (compileAdvice q).b)).fields =
        (bankTrialWindowTopPatch B).fields from hfields]
      exact bankTrialWindowTopPatchRootMode B
    rw [hraw] at hreset
    exact hm hreset

/-- Incoming-root has only the root field; all protected digit
fields are untouched. -/
private noncomputable def bankTrialWindowIncomingPatch {q : Nat}
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b) :
    GrantBankReference.BankLocalReference
      (compileAdvice q).b :=
  { fields := fun i =>
      if i.val = 0 then
        GrantBankReference.bankLocalReferenceClampedQuad q
          (GrantBankReference.incomingRootBankMap
            (GrantBankReference.bankLocalReferenceCell B i))
      else B.fields i,
    success := B.success }

private theorem bankTrialWindowIncomingPatchDigitFrame {q : Nat}
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b) :
    ∀ i : Fin (compileAdvice q).b,
      bankTrialLiveWaveToken (bankTrialWindowIncomingPatch B) i =
        bankTrialLiveWaveToken B i ∧
      bankTrialLiveWaveBit (bankTrialWindowIncomingPatch B) i =
        bankTrialLiveWaveBit B i := by
  intro i
  simp [bankTrialLiveWaveToken, bankTrialLiveWaveBit,
    bankTrialWindowIncomingPatch, Nat.succ_ne_zero]

private theorem bankTrialWindowIncomingRawMode
    (z : BankCell) :
    (GrantBankReference.incomingRootBankMap z).mode =
        z.mode ∨
      (GrantBankReference.incomingRootBankMap z).mode =
        .RESET := by
  cases hm : z.mode <;>
    simp [GrantBankReference.incomingRootBankMap,
      hm, isWaitMode] <;>
    (repeat' split) <;> simp

private theorem bankTrialWindowIncomingPatchModeCases {q : Nat}
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b) :
    bankTrialLiveWaveRootMode (bankTrialWindowIncomingPatch B) =
      bankTrialLiveWaveRootMode B ∨
    bankTrialLiveWaveRootMode (bankTrialWindowIncomingPatch B) =
      .RESET := by
  have h := bankTrialWindowIncomingRawMode
    (GrantBankReference.bankLocalReferenceCell B ⟨0, by have := bankTrialWindowWidthPos q; omega⟩)
  change (GrantBankReference.incomingRootBankMap
      (GrantBankReference.bankLocalReferenceCell B
        ⟨0, by have := bankTrialWindowWidthPos q; omega⟩)).mode =
        (B.fields ⟨0, by have := bankTrialWindowWidthPos q; omega⟩).1 ∨
      (GrantBankReference.incomingRootBankMap
        (GrantBankReference.bankLocalReferenceCell B
          ⟨0, by have := bankTrialWindowWidthPos q; omega⟩)).mode = .RESET at h
  simpa [bankTrialLiveWaveRootMode,
    bankTrialWindowIncomingPatch,
    GrantBankReference.bankLocalReferenceClampedQuad,
    GrantBankReference.bankAgentLeaseQuad, copyBank] using h

/-- Incoming-root service cannot alias any of the protected
source/responder/top selectors when b+2 <= n. -/
private theorem bankTrialWindowIncomingFieldsEqPatch {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (hw : BankTrialLiveWindowNonalias n q)
    (hin : ring.rightNeighbor e = root)
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hf : B.success = false) :
    (GrantBankReference.bankLocalReferenceStepClamped
      ring root B e).fields =
        (bankTrialWindowIncomingPatch B).fields := by
  funext i
  have hs : Counter.Support q ring root e := Or.inl hin
  by_cases hz : i.val = 0
  · have hx : ¬ (i.val < (compileAdvice q).b ∧
        e = Counter.site ring root i.val) := by
      intro h
      have he : Counter.site ring root 1 =
          Counter.site ring root 0 := by
        have he0 : e = root := by
          simpa [Counter.site, hz] using h.2
        rw [he0] at hin
        exact hin
      have hv := bankTrialWindowSitesDistinct ring root hw
        1 0 (by omega) (by omega) he
      omega
    have hy : ¬ (0 < i.val ∧
        e = Counter.site ring root (i.val - 1)) := by
      intro h
      omega
    have ht : ¬ (i.val = (compileAdvice q).b ∧
        e = Counter.site ring root (compileAdvice q).b) := by
      intro h
      have hb : 0 < (compileAdvice q).b := by
        change 0 < (compileAdvice q).s + 11
        omega
      omega
    rw [bankTrialLiveCarryIncomingSelected ring root
      e B hs hf i hx hy ht ⟨hz, hin⟩]
    change GrantBankReference.bankLocalReferenceClampedQuad q
        (GrantBankReference.incomingRootBankMap
          (GrantBankReference.bankLocalReferenceCell B i)) =
      (if i.val = 0 then
        GrantBankReference.bankLocalReferenceClampedQuad q
          (GrantBankReference.incomingRootBankMap
            (GrantBankReference.bankLocalReferenceCell B i))
       else B.fields i)
    rw [if_pos hz]
  · have hx : ¬ (i.val < (compileAdvice q).b ∧
        e = Counter.site ring root i.val) := by
      intro h
      have he : Counter.site ring root (i.val + 1) =
          Counter.site ring root 0 := by
        change ring.rightNeighbor (Counter.site ring root i.val) =
          root
        rw [← h.2]
        exact hin
      have hv := bankTrialWindowSitesDistinct ring root hw
        (i.val + 1) 0 (by
          have hi := i.isLt
          omega) (by omega) he
      omega
    have hy : ¬ (0 < i.val ∧
        e = Counter.site ring root (i.val - 1)) := by
      intro h
      have he : Counter.site ring root i.val =
          Counter.site ring root 0 := by
        have hsuc : i.val - 1 + 1 = i.val := by omega
        rw [← hsuc]
        change ring.rightNeighbor
          (Counter.site ring root (i.val - 1)) = root
        rw [← h.2]
        exact hin
      have hv := bankTrialWindowSitesDistinct ring root hw
        i.val 0 (by omega) (by omega) he
      omega
    have ht : ¬ (i.val = (compileAdvice q).b ∧
        e = Counter.site ring root (compileAdvice q).b) := by
      intro h
      have he : Counter.site ring root ((compileAdvice q).b + 1) =
          Counter.site ring root 0 := by
        change ring.rightNeighbor
          (Counter.site ring root (compileAdvice q).b) = root
        rw [← h.2]
        exact hin
      have hv := bankTrialWindowSitesDistinct ring root hw
        ((compileAdvice q).b + 1) 0 (by omega) (by omega) he
      omega
    have hr : ¬ (i.val = 0 ∧ ring.rightNeighbor e = root) := by
      intro h
      exact hz h.1
    rw [bankTrialLiveCarryUnselectedField ring root
      e B hs hf i hx hy ht hr]
    change B.fields i =
      (if i.val = 0 then
        GrantBankReference.bankLocalReferenceClampedQuad q
          (GrantBankReference.incomingRootBankMap
            (GrantBankReference.bankLocalReferenceCell B i))
       else B.fields i)
    rw [if_neg hz]

/-- Incoming-root only decrements a waiting lease or replaces
the root mode by RESET; a LIVE successor therefore keeps the
old mode and the full old digit certificate. -/
theorem bankTrialWindowIncomingRows {n q : Nat}
    (ring : DirectedRing n) (root : Fin n) :
    BankTrialLiveWindowIncomingRows (q := q) ring root := by
  intro e hin hw B begun hlock nextBegun hnext
  have hf := bankTrialWindowLiveOldNotLatched
    ring root e B begun nextBegun hnext
  have hfields := bankTrialWindowIncomingFieldsEqPatch
    ring root e hw hin B hf
  have hnor := bankTrialWindowNextLiveNonreset
    ring root e B begun nextBegun hnext
  have hmode : bankTrialLiveWaveRootMode
      (bankTrialWindowIncomingPatch B) =
        bankTrialLiveWaveRootMode B := by
    rcases bankTrialWindowIncomingPatchModeCases B with hr | hr
    · exact hr
    · have hraw : bankTrialLiveWaveRootMode
          (GrantBankReference.bankLocalReferenceStepClamped
            ring root B e) = .RESET := by
        change ((GrantBankReference.bankLocalReferenceStepClamped
          ring root B e).fields ⟨0, by have := bankTrialWindowWidthPos q; omega⟩).1 = .RESET
        rw [hfields]
        exact hr
      exact False.elim (hnor hraw)
  have hc : BankTrialLiveWaveCertificate q B :=
    hlock.1 begun rfl
  have hcert := bankTrialWindowCertificateErase
    (bankTrialWindowIncomingPatch B) B hc hmode
    (fun i => (bankTrialWindowIncomingPatchDigitFrame B i).2)
    (fun i _ => (bankTrialWindowIncomingPatchDigitFrame B i).1)
  have hnew := bankTrialWindowCertificateFieldsCongr
    (GrantBankReference.bankLocalReferenceStepClamped
      ring root B e)
    (bankTrialWindowIncomingPatch B) hfields hcert
  have hbank := bankTrialLocalNextLiveBank ring root e B begun
  constructor
  · intro flag _
    rw [hbank]
    exact hnew
  · intro flag _ hreset
    rw [hbank] at hreset
    exact hnor hreset

/-- The logical root/first-digit BANK cells reconstructed from the
reference, with the exact old success latch ignored by the owner. -/
private abbrev bankTrialWindowRootCell {q : Nat}
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b) : BankCell :=
  GrantBankReference.bankLocalReferenceCell B ⟨0, by have := bankTrialWindowWidthPos q; omega⟩

private abbrev bankTrialWindowFirstCell {q : Nat}
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b) : BankCell :=
  GrantBankReference.bankLocalReferenceCell B
    ⟨1, by have := bankTrialWindowWidthPos q; omega⟩

private abbrev bankTrialWindowRootPair {q : Nat}
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b) : BankCell × BankCell :=
  GrantBankReference.bankLocalReferenceInternalPair q B
    ⟨0, by have := bankTrialWindowWidthPos q; omega⟩

/-- Two-slot root service patch; all digits past digit one are
literal frames. The first source is root0, not an interior. -/
private noncomputable def bankTrialWindowRootPatch {q : Nat}
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b) :
    GrantBankReference.BankLocalReference
      (compileAdvice q).b :=
  { fields := fun i =>
      if i.val = 0 then
        GrantBankReference.bankLocalReferenceClampedQuad q
          (bankTrialWindowRootPair B).1
      else if i.val = 1 then
        GrantBankReference.bankLocalReferenceClampedQuad q
          (bankTrialWindowRootPair B).2
      else B.fields i,
    success := B.success }

private theorem bankTrialWindowRootPatchMode {q : Nat}
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b) :
    bankTrialLiveWaveRootMode (bankTrialWindowRootPatch B) =
      (bankTrialWindowRootPair B).1.mode := by
  simp [bankTrialLiveWaveRootMode, bankTrialWindowRootPatch,
    GrantBankReference.bankLocalReferenceClampedQuad,
    GrantBankReference.bankAgentLeaseQuad, copyBank]

private theorem bankTrialWindowRootPatchFirstToken {q : Nat}
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b) :
    bankTrialLiveWaveToken (bankTrialWindowRootPatch B)
      ⟨0, by have := bankTrialWindowWidthPos q; omega⟩ =
        (bankTrialWindowRootPair B).2.tok := by
  simp [bankTrialLiveWaveToken, bankTrialWindowRootPatch,
    GrantBankReference.bankLocalReferenceClampedQuad,
    GrantBankReference.bankAgentLeaseQuad, copyBank]

private theorem bankTrialWindowRootPatchFirstBit {q : Nat}
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b) :
    bankTrialLiveWaveBit (bankTrialWindowRootPatch B)
      ⟨0, by have := bankTrialWindowWidthPos q; omega⟩ =
        (bankTrialWindowRootPair B).2.bit := by
  simp [bankTrialLiveWaveBit, bankTrialWindowRootPatch,
    GrantBankReference.bankLocalReferenceClampedQuad,
    GrantBankReference.bankAgentLeaseQuad, copyBank]

private theorem bankTrialWindowRootPatchTailToken {q : Nat}
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (i : Fin (compileAdvice q).b)
    (hi : i ≠ ⟨0, by have := bankTrialWindowWidthPos q; omega⟩) :
    bankTrialLiveWaveToken (bankTrialWindowRootPatch B) i =
      bankTrialLiveWaveToken B i := by
  have hiv : i.val ≠ 0 := by
    intro hz
    exact hi (Fin.ext hz)
  have hone : i.val + 1 ≠ 1 := by omega
  simp [bankTrialLiveWaveToken, bankTrialWindowRootPatch,
    hiv]

private theorem bankTrialWindowRootPatchTailBit {q : Nat}
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (i : Fin (compileAdvice q).b)
    (hi : i ≠ ⟨0, by have := bankTrialWindowWidthPos q; omega⟩) :
    bankTrialLiveWaveBit (bankTrialWindowRootPatch B) i =
      bankTrialLiveWaveBit B i := by
  have hiv : i.val ≠ 0 := by
    intro hz
    exact hi (Fin.ext hz)
  have hone : i.val + 1 ≠ 1 := by omega
  simp [bankTrialLiveWaveBit, bankTrialWindowRootPatch,
    hiv]

private theorem bankTrialWindowRootOldFirstToken {q : Nat}
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b) :
    (bankTrialWindowFirstCell B).tok =
      bankTrialLiveWaveToken B ⟨0, by have := bankTrialWindowWidthPos q; omega⟩ := by
  rfl

private theorem bankTrialWindowRootOldFirstBit {q : Nat}
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b) :
    (bankTrialWindowFirstCell B).bit =
      bankTrialLiveWaveBit B ⟨0, by have := bankTrialWindowWidthPos q; omega⟩ := by
  rfl

private theorem bankTrialWindowRootOldMode {q : Nat}
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b) :
    (bankTrialWindowRootCell B).mode =
      bankTrialLiveWaveRootMode B := by
  rfl

/-- Exhaustive *stage-restricted* BANK source owner rows. In the
same-mode branch the digit-one bit and token are unchanged.
If the head accepts a return, it empties digit one; the old
return worker was nonempty. An ARMED head may issue IR or
advance to CSTART, while CSTART issues an authenticated CR.
The remaining alternative is RESET, excluded at LIVE cuts.
No Cartesian product of arbitrary worker arrays is performed. -/
private theorem bankTrialWindowRawRootCases
    (b : Nat) (theta : Nat → Bool) (x y : BankCell)
    (hb : 1 < b) (hx : x.role = 0) (hy : y.role = 1)
    (hg : x.grant = false) (hnr : x.mode ≠ .RESET)
    (hhead : (x.mode = .ARMED ∨ x.mode = .CSTART) →
      y.tok = .E)
    (hrwait : x.mode = .RWAIT →
      y.tok = .E ∨ y.tok = .RR ∨ y.tok = .RL)
    (hiwait : x.mode = .IWAIT →
      y.tok = .E ∨ y.tok = .IR ∨ y.tok = .AL)
    (hcwait : x.mode = .CWAIT →
      y.tok = .E ∨ y.tok = .CR0 ∨ y.tok = .CR1 ∨
        y.tok = .CL0 ∨ y.tok = .CL1) :
    (((bankPair x y 1 b theta).1.mode = x.mode ∧
      (bankPair x y 1 b theta).2.tok = y.tok ∧
      (bankPair x y 1 b theta).2.bit = y.bit) ∨
     (((bankPair x y 1 b theta).1.mode = .ARMED ∨
       (bankPair x y 1 b theta).1.mode = .CSTART) ∧
      (bankPair x y 1 b theta).2.tok = .E ∧
      (y.tok ≠ .E ∨ x.mode = .ARMED)) ∨
     (x.mode = .ARMED ∧
      (bankPair x y 1 b theta).1.mode = .IWAIT ∧
      (bankPair x y 1 b theta).2.tok = .IR ∧
      (bankPair x y 1 b theta).2.bit = false) ∨
     (x.mode = .CSTART ∧
      (bankPair x y 1 b theta).1.mode = .CWAIT ∧
      ((bankPair x y 1 b theta).2.tok = .CR0 ∨
       ((bankPair x y 1 b theta).2.tok = .CR1 ∧
        (bankPair x y 1 b theta).2.bit = theta 0))) ∨
     (bankPair x y 1 b theta).1.mode = .RESET) := by
  have hb1 : 1 ≤ b := by omega
  have hbnot : b ≠ 1 := by omega
  cases hm : x.mode with
  | RESET =>
      exact False.elim (hnr hm)
  | RWAIT =>
      rcases hrwait hm with he | he | he <;>
        by_cases hl : 1 < x.lease <;>
        simp [bankPair, hx, hy, hg, hm, he, hb1,
          hbnot, hl, isRetTok, isWaitMode,
          Id.run_pure, Id.run_bind] <;>
        (repeat' split) <;> simp [*]
  | ARMED =>
      have he := hhead (Or.inl hm)
      cases hbit : y.bit <;>
        simp [bankPair, hx, hy, hg, hm, he, hbit,
          hb1, hbnot, isRetTok, isWaitMode,
          Id.run_pure, Id.run_bind] <;>
        (repeat' split) <;> simp [*]
  | IWAIT =>
      rcases hiwait hm with he | he | he <;>
        by_cases hl : 1 < x.lease <;>
        simp [bankPair, hx, hy, hg, hm, he, hb1,
          hbnot, hl, isRetTok, isWaitMode,
          Id.run_pure, Id.run_bind] <;>
        (repeat' split) <;> simp [*]
  | CSTART =>
      have he := hhead (Or.inr hm)
      cases hbit : y.bit <;>
        cases htheta : theta 0 <;>
        simp [bankPair, hx, hy, hg, hm, he, hbit,
          htheta, hb1, hbnot, isRetTok, isWaitMode,
          Id.run_pure, Id.run_bind] <;>
        (repeat' split) <;> simp [*]
  | CWAIT =>
      rcases hcwait hm with he | he | he | he | he <;>
        by_cases hl : 1 < x.lease <;>
        simp [bankPair, hx, hy, hg, hm, he, hb1,
          hbnot, hl, isRetTok, isWaitMode,
          Id.run_pure, Id.run_bind] <;>
        (repeat' split) <;> simp [*]

/-- The only digit altered on a root outgoing edge is digit one.
This is a statement about the literal clamped reference fields,
not the physical configuration's function representation. -/
private theorem bankTrialWindowRootFieldsEqPatch {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hw : BankTrialLiveWindowNonalias n q)
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hf : B.success = false) :
    (GrantBankReference.bankLocalReferenceStepClamped
      ring root B root).fields =
        (bankTrialWindowRootPatch B).fields := by
  funext i
  have hs : Counter.Support q ring root root :=
    Or.inr ⟨0, Nat.zero_le _, rfl⟩
  have hn : 2 ≤ n := by
    unfold BankTrialLiveWindowNonalias at hw
    omega
  by_cases hz : i.val = 0
  · have heq : i = ⟨0, by have := bankTrialWindowWidthPos q; omega⟩ := Fin.ext hz
    rw [heq, bankTrialLocalStepField ring root root B hs hf,
      bankTrialLocalFieldRootOutgoing ring root B]
    simp [bankTrialWindowRootPatch]
  · by_cases ho : i.val = 1
    · have heq : i = ⟨1, by omega⟩ := Fin.ext ho
      rw [heq, bankTrialLocalStepField ring root root B hs hf,
        bankTrialLocalFieldOneOutgoing ring root hn B]
      simp [bankTrialWindowRootPatch]
    · have hx : ¬ (i.val < (compileAdvice q).b ∧
          root = Counter.site ring root i.val) := by
        intro h
        have hv := bankTrialWindowSitesDistinct ring root hw
          0 i.val (by omega) (by omega) h.2
        omega
      have hy : ¬ (0 < i.val ∧
          root = Counter.site ring root (i.val - 1)) := by
        intro h
        have hv := bankTrialWindowSitesDistinct ring root hw
          0 (i.val - 1) (by omega) (by omega) h.2
        omega
      have ht : ¬ (i.val = (compileAdvice q).b ∧
          root = Counter.site ring root (compileAdvice q).b) := by
        intro h
        have hv := bankTrialWindowSitesDistinct ring root hw
          0 (compileAdvice q).b (by omega) (by omega) h.2
        have hb : 0 < (compileAdvice q).b := by
          change 0 < (compileAdvice q).s + 11
          omega
        omega
      have hr : ¬ (i.val = 0 ∧
          ring.rightNeighbor root = root) := by
        intro h
        exact hz h.1
      rw [bankTrialLiveCarryUnselectedField ring root root
        B hs hf i hx hy ht hr]
      change B.fields i =
        (if i.val = 0 then
          GrantBankReference.bankLocalReferenceClampedQuad q
            (bankTrialWindowRootPair B).1
         else if i.val = 1 then
          GrantBankReference.bankLocalReferenceClampedQuad q
            (bankTrialWindowRootPair B).2
         else B.fields i)
      rw [if_neg hz, if_neg ho]

/-- The literal root outgoing pair respects the full stage
certificate whenever its successor root is still not RESET. -/
private theorem bankTrialWindowRootPatchCertificate {q : Nat}
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hc : BankTrialLiveWaveCertificate q B)
    (hnr : bankTrialLiveWaveRootMode B ≠ .RESET)
    (hnewmode : bankTrialLiveWaveRootMode
      (bankTrialWindowRootPatch B) ≠ .RESET) :
    BankTrialLiveWaveCertificate q (bankTrialWindowRootPatch B) := by
  have hb : 1 < (compileAdvice q).b := by
    change 1 < (compileAdvice q).s + 11
    omega
  have hhead :
      ((bankTrialWindowRootCell B).mode = .ARMED ∨
       (bankTrialWindowRootCell B).mode = .CSTART) →
      (bankTrialWindowFirstCell B).tok = .E := by
    intro h
    exact hc.headClear ⟨0, by have := bankTrialWindowWidthPos q; omega⟩ h
  have hrwait :
      (bankTrialWindowRootCell B).mode = .RWAIT →
      (bankTrialWindowFirstCell B).tok = .E ∨
      (bankTrialWindowFirstCell B).tok = .RR ∨
      (bankTrialWindowFirstCell B).tok = .RL := by
    intro h
    exact hc.resetTokens ⟨0, by have := bankTrialWindowWidthPos q; omega⟩ h
  have hiwait :
      (bankTrialWindowRootCell B).mode = .IWAIT →
      (bankTrialWindowFirstCell B).tok = .E ∨
      (bankTrialWindowFirstCell B).tok = .IR ∨
      (bankTrialWindowFirstCell B).tok = .AL := by
    intro h
    exact hc.iwaitTokens ⟨0, by have := bankTrialWindowWidthPos q; omega⟩ h
  have hcwait :
      (bankTrialWindowRootCell B).mode = .CWAIT →
      (bankTrialWindowFirstCell B).tok = .E ∨
      (bankTrialWindowFirstCell B).tok = .CR0 ∨
      (bankTrialWindowFirstCell B).tok = .CR1 ∨
      (bankTrialWindowFirstCell B).tok = .CL0 ∨
      (bankTrialWindowFirstCell B).tok = .CL1 := by
    intro h
    change (bankTrialWindowFirstCell B).tok = .E ∨
      BankTrialLiveComparisonToken (bankTrialWindowFirstCell B).tok
    have hfirst := hc.cwaitTokens
      ⟨0, by have := bankTrialWindowWidthPos q; omega⟩ h
    rw [← bankTrialWindowRootOldFirstToken B] at hfirst
    exact hfirst
  have hcases := bankTrialWindowRawRootCases
    (compileAdvice q).b (compileAdvice q).theta
    (bankTrialWindowRootCell B) (bankTrialWindowFirstCell B)
    hb rfl rfl rfl (by exact hnr)
    hhead hrwait hiwait hcwait
  have hp :
      bankTrialWindowRootPair B =
        bankPair (bankTrialWindowRootCell B)
          (bankTrialWindowFirstCell B) 1
          (compileAdvice q).b (compileAdvice q).theta := rfl
  rw [← hp] at hcases
  rcases hcases with hsame | hdone | hIR | hCR | hreset
  · have hmode : bankTrialLiveWaveRootMode
        (bankTrialWindowRootPatch B) =
          bankTrialLiveWaveRootMode B := by
        rw [bankTrialWindowRootPatchMode, hsame.1]
        exact bankTrialWindowRootOldMode B
    have hbit : ∀ i : Fin (compileAdvice q).b,
        bankTrialLiveWaveBit (bankTrialWindowRootPatch B) i =
          bankTrialLiveWaveBit B i := by
      intro i
      by_cases hi : i = ⟨0, by have := bankTrialWindowWidthPos q; omega⟩
      · rw [hi, bankTrialWindowRootPatchFirstBit B,
          hsame.2.2]
        exact bankTrialWindowRootOldFirstBit B
      · exact bankTrialWindowRootPatchTailBit B i hi
    have htok : ∀ i : Fin (compileAdvice q).b,
        bankTrialLiveWaveToken (bankTrialWindowRootPatch B) i ≠ .E →
          bankTrialLiveWaveToken (bankTrialWindowRootPatch B) i =
            bankTrialLiveWaveToken B i := by
      intro i _
      by_cases hi : i = ⟨0, by have := bankTrialWindowWidthPos q; omega⟩
      · rw [hi, bankTrialWindowRootPatchFirstToken B,
          hsame.2.1]
        exact bankTrialWindowRootOldFirstToken B
      · exact bankTrialWindowRootPatchTailToken B i hi
    exact bankTrialWindowCertificateErase
      (bankTrialWindowRootPatch B) B hc hmode hbit htok
  · have hfirst : bankTrialLiveWaveToken
        (bankTrialWindowRootPatch B) ⟨0, by have := bankTrialWindowWidthPos q; omega⟩ = .E := by
      rw [bankTrialWindowRootPatchFirstToken]
      exact hdone.2.1
    have htail : ∀ i : Fin (compileAdvice q).b,
        i ≠ ⟨0, by have := bankTrialWindowWidthPos q; omega⟩ →
        bankTrialLiveWaveToken (bankTrialWindowRootPatch B) i =
          .E := by
      intro i hi
      rw [bankTrialWindowRootPatchTailToken B i hi]
      rcases hdone.2.2 with hworker | hheadMode
      · have hw : bankTrialLiveWaveToken B
            ⟨0, by have := bankTrialWindowWidthPos q; omega⟩ ≠ .E := by
          rw [← bankTrialWindowRootOldFirstToken B]
          exact hworker
        exact bankTrialInteriorOldWorkerOthersEmpty B hc
          ⟨0, by have := bankTrialWindowWidthPos q; omega⟩ i hw hi
      · have hm : bankTrialLiveWaveRootMode B = .ARMED := by
          rw [← bankTrialWindowRootOldMode B]
          exact hheadMode
        exact hc.headClear i (Or.inl hm)
    have hall : ∀ i : Fin (compileAdvice q).b,
        bankTrialLiveWaveToken (bankTrialWindowRootPatch B) i =
          .E := by
      intro i
      by_cases hi : i = ⟨0, by have := bankTrialWindowWidthPos q; omega⟩
      · rw [hi]
        exact hfirst
      · exact htail i hi
    exact bankTrialWindowCertificateEmpty
      (bankTrialWindowRootPatch B) hall
  · rcases hIR with ⟨hold, hroot, htok, hbit⟩
    have hmode : bankTrialLiveWaveRootMode
        (bankTrialWindowRootPatch B) = .IWAIT := by
      rw [bankTrialWindowRootPatchMode]
      exact hroot
    have hfirst : bankTrialLiveWaveToken
        (bankTrialWindowRootPatch B) ⟨0, by have := bankTrialWindowWidthPos q; omega⟩ = .IR := by
      rw [bankTrialWindowRootPatchFirstToken]
      exact htok
    have htail : ∀ i : Fin (compileAdvice q).b,
        i ≠ ⟨0, by have := bankTrialWindowWidthPos q; omega⟩ →
        bankTrialLiveWaveToken (bankTrialWindowRootPatch B) i =
          .E := by
      intro i hi
      rw [bankTrialWindowRootPatchTailToken B i hi]
      have hm : bankTrialLiveWaveRootMode B = .ARMED := by
        rw [← bankTrialWindowRootOldMode B]
        exact hold
      exact hc.headClear i (Or.inl hm)
    exact bankTrialWindowCertificateFirstDigit
      (bankTrialWindowRootPatch B) htail
      (Or.inl ⟨hmode, hfirst⟩)
  · rcases hCR with ⟨hold, hroot, htoken⟩
    have hmode : bankTrialLiveWaveRootMode
        (bankTrialWindowRootPatch B) = .CWAIT := by
      rw [bankTrialWindowRootPatchMode]
      exact hroot
    have hfirst : bankTrialLiveWaveToken
          (bankTrialWindowRootPatch B) ⟨0, by have := bankTrialWindowWidthPos q; omega⟩ = .CR0 ∨
        (bankTrialLiveWaveToken
          (bankTrialWindowRootPatch B) ⟨0, by have := bankTrialWindowWidthPos q; omega⟩ = .CR1 ∧
         bankTrialLiveWaveBit
          (bankTrialWindowRootPatch B) ⟨0, by have := bankTrialWindowWidthPos q; omega⟩ =
            (compileAdvice q).theta 0) := by
      rcases htoken with hzero | ⟨hone, hmatch⟩
      · exact Or.inl (by
          rw [bankTrialWindowRootPatchFirstToken B]
          exact hzero)
      · exact Or.inr ⟨(by
          rw [bankTrialWindowRootPatchFirstToken B]
          exact hone), (by
          rw [bankTrialWindowRootPatchFirstBit B]
          exact hmatch)⟩
    have htail : ∀ i : Fin (compileAdvice q).b,
        i ≠ ⟨0, by have := bankTrialWindowWidthPos q; omega⟩ →
        bankTrialLiveWaveToken (bankTrialWindowRootPatch B) i =
          .E := by
      intro i hi
      rw [bankTrialWindowRootPatchTailToken B i hi]
      have hm : bankTrialLiveWaveRootMode B = .CSTART := by
        rw [← bankTrialWindowRootOldMode B]
        exact hold
      exact hc.headClear i (Or.inr hm)
    exact bankTrialWindowCertificateFirstDigit
      (bankTrialWindowRootPatch B) htail
      (Or.inr ⟨hmode, hfirst⟩)
  · have hbad : bankTrialLiveWaveRootMode
        (bankTrialWindowRootPatch B) = .RESET := by
      rw [bankTrialWindowRootPatchMode]
      exact hreset
    exact False.elim (hnewmode hbad)

/-- Complete nonaliased root-outgoing LIVE row. Its proof
distinguishes same-stage frames, consumed returns, and the
two root-launched worker kinds. -/
theorem bankTrialWindowRootOutgoingRows {n q : Nat}
    (ring : DirectedRing n) (root : Fin n) :
    BankTrialLiveWindowRootOutgoingRows (q := q) ring root := by
  intro hw B begun hlock nextBegun hnext
  have hf := bankTrialWindowLiveOldNotLatched
    ring root root B begun nextBegun hnext
  have hfields := bankTrialWindowRootFieldsEqPatch
    ring root hw B hf
  have hnor := bankTrialWindowNextLiveNonreset
    ring root root B begun nextBegun hnext
  have hpNoReset : bankTrialLiveWaveRootMode
      (bankTrialWindowRootPatch B) ≠ .RESET := by
    intro hbad
    apply hnor
    change ((GrantBankReference.bankLocalReferenceStepClamped
      ring root B root).fields ⟨0, by have := bankTrialWindowWidthPos q; omega⟩).1 = .RESET
    rw [hfields]
    exact hbad
  have hc : BankTrialLiveWaveCertificate q B :=
    hlock.1 begun rfl
  have hm : bankTrialLiveWaveRootMode B ≠ .RESET :=
    hlock.2 begun rfl
  have hcert := bankTrialWindowRootPatchCertificate
    B hc hm hpNoReset
  have hnew := bankTrialWindowCertificateFieldsCongr
    (GrantBankReference.bankLocalReferenceStepClamped
      ring root B root) (bankTrialWindowRootPatch B)
    hfields hcert
  have hbank := bankTrialLocalNextLiveBank
    ring root root B begun
  constructor
  · intro flag _
    rw [hbank]
    exact hnew
  · intro flag _ hreset
    rw [hbank] at hreset
    exact hnor hreset

/-- The final G11b deterministic CLEAN-to-word invariant,
with all four corrected edge-row classes now supplied. -/
theorem bankTrialWindowLockedCleanWords {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hw : BankTrialLiveWindowNonalias n q)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S) :
    ∀ word : List (Fin n),
      BankTrialLiveNoResetLocked
        (bankTrialLocalRun ring root word
          (bankTrialLocalStart S)) := by
  exact bankTrialWindowLockedCleanWordsOfClasses
    ring root hw S hclean
    (bankTrialWindowRootOutgoingRows ring root)
    (bankTrialWindowInteriorRowsOfPairRows ring root
      (bankTrialLiveInteriorPairRows q))
    (bankTrialWindowTopRows ring root)
    (bankTrialWindowIncomingRows ring root)

end L3

/-!
G11c upper-bound authentication.
The new rows below are restricted to CLEAN-reachable locked states.
-/

namespace L3

open Classical

set_option autoImplicit false
set_option Elab.async false

/-- The published spatial size hypothesis implies precisely the
nonalias hypothesis of the locked word theorem. -/
theorem bankTrialProbabilityUpperWindow {n q : Nat}
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n) :
    BankTrialLiveWindowNonalias n q :=
  bankTrialWindowFromLeaseCap hlarge

/-- Only the genuine LOCKED LIVE clause is required for comparison
provenance; arbitrary forged CL1 snapshots are not used. -/
theorem bankTrialProbabilityLockedComparatorCredit {q : Nat}
    (z : BankTrialLocalState q)
    (hlock : BankTrialLiveNoResetLocked z)
    (htheta : (compileAdvice q).K ≤ bankTrialLiveThetaBinary q) :
    BankTrialLiveComparatorCredit z := by
  exact bankTrialLiveComparatorCreditOfGenealogy z
    (bankTrialLiveGenealogyOfLocked z hlock.1) htheta

theorem bankTrialProbabilityCleanWordsComparatorCredit {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hw : BankTrialLiveWindowNonalias n q)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S)
    (htheta : (compileAdvice q).K ≤ bankTrialLiveThetaBinary q) :
    ∀ word : List (Fin n),
      BankTrialLiveComparatorCredit
        (bankTrialLocalRun ring root word
          (bankTrialLocalStart S)) := by
  intro word
  exact bankTrialProbabilityLockedComparatorCredit
    (bankTrialLocalRun ring root word (bankTrialLocalStart S))
    (bankTrialWindowLockedCleanWords ring root hw S hclean word)
    htheta

/-- A postservice LIVE observer has not latched BANK success,
independently of its preceding observer phase. -/
private theorem bankTrialProbabilityNextLiveUnlatched {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (z : BankTrialLocalState q) (nextBegun : Bool)
    (hnext : (bankTrialLocalNext ring root z e).phase =
      .live nextBegun) :
    (bankTrialLocalNext ring root z e).bank.success = false := by
  cases z with
  | mk B phase =>
    cases phase with
    | live begun =>
      rw [bankTrialLocalNextLiveBank]
      cases hs : (GrantBankReference.bankLocalReferenceStepClamped
          ring root B e).success with
      | false => rfl
      | true =>
          simp [bankTrialLocalNext, hs] at hnext
    | recovery =>
      simp [bankTrialLocalNext] at hnext <;>
        (repeat' split at hnext) <;> cases hnext
    | won =>
      simp [bankTrialLocalNext] at hnext
    | lost =>
      simp [bankTrialLocalNext] at hnext

/-- A CLEAN-reachable LIVE cut cannot have a latched success.
This is distinct from the pre-LIVE false latch lemma. -/
theorem bankTrialProbabilityCleanLiveUnlatched {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S)
    (word : List (Fin n))
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b) (begun : Bool)
    (hrun : bankTrialLocalRun ring root word
      (bankTrialLocalStart S) = ⟨B, .live begun⟩) :
    B.success = false := by
  have hreverse : ∀ rev : List (Fin n),
      ∀ (C : GrantBankReference.BankLocalReference
        (compileAdvice q).b) (flag : Bool),
      bankTrialLocalRun ring root rev.reverse
        (bankTrialLocalStart S) = ⟨C, .live flag⟩ →
      C.success = false := by
    intro rev
    induction rev with
    | nil =>
        intro C flag h
        change (⟨S, .live false⟩ : BankTrialLocalState q) =
          ⟨C, .live flag⟩ at h
        cases h
        exact hclean.1
    | cons e rev ih =>
        intro C flag h
        rw [List.reverse_cons, bankTrialLocalRunAppend] at h
        change bankTrialLocalNext ring root
          (bankTrialLocalRun ring root rev.reverse
            (bankTrialLocalStart S)) e = ⟨C, .live flag⟩ at h
        have hp :
            (bankTrialLocalNext ring root
              (bankTrialLocalRun ring root rev.reverse
                (bankTrialLocalStart S)) e).phase = .live flag := by
          rw [h]
        have hf := bankTrialProbabilityNextLiveUnlatched
          ring root e
          (bankTrialLocalRun ring root rev.reverse
            (bankTrialLocalStart S)) flag hp
        rw [h] at hf
        exact hf
  have h := hreverse word.reverse B begun
  have hword :
      bankTrialLocalRun ring root word.reverse.reverse
        (bankTrialLocalStart S) = ⟨B, .live begun⟩ := by
    simpa only [List.reverse_reverse] using hrun
  exact h hword

/-- First-WON inversion on the actual chronological scheduler
word, with recovery and LOST excluded by their prior theorems. -/
theorem bankTrialProbabilityCleanWinGuardTrace {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hn : 2 ≤ n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S) :
    BankTrialLiveWinGuardTrace ring root S := by
  intro word hwon
  have hreverse : ∀ rev : List (Fin n),
      (bankTrialLocalRun ring root rev.reverse
        (bankTrialLocalStart S)).phase = .won →
      ∃ (pre suffix : List (Fin n))
        (B : GrantBankReference.BankLocalReference
          (compileAdvice q).b) (begun : Bool),
        rev.reverse = pre ++ root :: suffix ∧
        bankTrialLocalRun ring root pre (bankTrialLocalStart S) =
          ⟨B, .live begun⟩ ∧
        (B.fields ⟨0, by omega⟩).1 = .CWAIT ∧
        (B.fields
          ⟨1, by change 1 < (compileAdvice q).s + 11 + 1; omega⟩).2.2.1 =
            .CL1 := by
    intro rev
    induction rev with
    | nil =>
        intro h
        cases h
    | cons e rev ih =>
        intro hw
        have hlast :
            bankTrialLocalRun ring root (e :: rev).reverse
              (bankTrialLocalStart S) =
            bankTrialLocalNext ring root
              (bankTrialLocalRun ring root rev.reverse
                (bankTrialLocalStart S)) e := by
          rw [List.reverse_cons, bankTrialLocalRunAppend]
          rfl
        rw [hlast] at hw
        cases hpre : bankTrialLocalRun ring root rev.reverse
            (bankTrialLocalStart S) with
        | mk B phase =>
          cases phase with
          | live begun =>
            have hf := bankTrialProbabilityCleanLiveUnlatched
              ring root S hclean rev.reverse B begun hpre
            have hlastwon :
                (bankTrialLocalNext ring root
                  (⟨B, .live begun⟩ : BankTrialLocalState q) e).phase =
                    .won := by
              rw [← hpre]
              exact hw
            obtain ⟨he, hm, ht⟩ :=
              bankTrialProbabilityLiveWonRequiresOldGuard
                ring root e B begun hf hlastwon
            refine ⟨rev.reverse, [], B, begun, ?_, hpre, hm, ht⟩
            rw [List.reverse_cons, he]
          | recovery =>
            have hnever := bankTrialProbabilityRecoverySuffixNotWon
              ring root hn S hclean [e] rev.reverse B hpre
            have hlastwon :
                (bankTrialLocalRun ring root [e]
                  (⟨B, .recovery⟩ : BankTrialLocalState q)).phase =
                    .won := by
              change (bankTrialLocalNext ring root
                (⟨B, .recovery⟩ : BankTrialLocalState q) e).phase =
                  .won
              rw [← hpre]
              exact hw
            exact False.elim (hnever hlastwon)
          | won =>
            have hprefix :
                (bankTrialLocalRun ring root rev.reverse
                  (bankTrialLocalStart S)).phase = .won := by
              rw [hpre]
            obtain ⟨pre, suffix, C, flag, hword, hr, hm, ht⟩ :=
              ih hprefix
            refine ⟨pre, suffix ++ [e], C, flag, ?_, hr, hm, ht⟩
            rw [List.reverse_cons, hword]
            simp [List.append_assoc]
          | lost =>
            have hterminal :
                bankTrialLocalTerminal
                  (⟨B, .lost⟩ : BankTrialLocalState q) :=
              Or.inr rfl
            have hfix := bankTrialLocalTerminalAbsorbs
              ring root e (⟨B, .lost⟩ : BankTrialLocalState q)
              hterminal
            rw [hpre, hfix] at hw
            cases hw
  have h := hreverse word.reverse
  have hword :
      (bankTrialLocalRun ring root word.reverse.reverse
        (bankTrialLocalStart S)).phase = .won := by
    simpa only [List.reverse_reverse] using hwon
  simpa only [List.reverse_reverse] using h hword

/-- A successful word cannot contain an incoming physical root
letter at any still-open LIVE ARMED gate. -/
theorem bankTrialProbabilityCleanWinNoArmedIncoming {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hn : 2 ≤ n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S) :
    ∀ word : List (Fin n),
      (bankTrialLocalRun ring root word
        (bankTrialLocalStart S)).phase = .won →
      BankTrialNoArmedIncoming ring root word
        (bankTrialLocalStart S) := by
  have haux : ∀ suffix : List (Fin n),
      ∀ pre : List (Fin n),
      (bankTrialLocalRun ring root (pre ++ suffix)
        (bankTrialLocalStart S)).phase = .won →
      BankTrialNoArmedIncoming ring root suffix
        (bankTrialLocalRun ring root pre
          (bankTrialLocalStart S)) := by
    intro suffix
    induction suffix with
    | nil =>
        intro pre hw
        trivial
    | cons e suffix ih =>
        intro pre hw
        constructor
        · intro hg
          by_cases he : e = root
          · exact Or.inl he
          · by_cases hin : ring.rightNeighbor e = root
            · obtain ⟨⟨begun, hphase⟩, hmode⟩ := hg
              cases hstate : bankTrialLocalRun ring root pre
                  (bankTrialLocalStart S) with
              | mk B phase =>
                cases phase with
                | live flag =>
                    have hflags : flag = begun := by
                      rw [hstate] at hphase
                      cases hphase
                      rfl
                    subst flag
                    have hm : (B.fields ⟨0, by omega⟩).1 =
                        .ARMED := by
                      rw [hstate] at hmode
                      exact hmode
                    have hf := bankTrialProbabilityCleanLiveUnlatched
                      ring root S hclean pre B begun hstate
                    have hnever := bankTrialProbabilityIncomingArmedNoWinSuffix
                      ring root e hn S hclean pre suffix B begun
                      hstate hf hm he hin
                    exact False.elim (hnever hw)
                | recovery =>
                    rw [hstate] at hphase
                    cases hphase
                | won =>
                    rw [hstate] at hphase
                    cases hphase
                | lost =>
                    rw [hstate] at hphase
                    cases hphase
            · exact Or.inr hin
        · have hnext :
            (bankTrialLocalRun ring root ((pre ++ [e]) ++ suffix)
              (bankTrialLocalStart S)).phase = .won := by
            have heq : (pre ++ [e]) ++ suffix =
                pre ++ e :: suffix := by
              rw [List.append_assoc]
              rfl
            rw [heq]
            exact hw
          have ht := ih (pre ++ [e]) hnext
          rw [bankTrialLocalRunAppend] at ht
          change BankTrialNoArmedIncoming ring root suffix
            (bankTrialLocalNext ring root
              (bankTrialLocalRun ring root pre
                (bankTrialLocalStart S)) e) at ht
          exact ht
  intro word hw
  have h := haux word [] (by simpa using hw)
  simpa only [List.nil_append, bankTrialLocalRun] using h

end L3

/-!
Carry accounting: the existing sum-swap lemma gives a
constant-size way to combine local BANK cell inequalities.
-/

namespace L3

open Classical

set_option autoImplicit false
set_option Elab.async false

private def bankTrialProbabilityDigitPotential {q : Nat}
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (i : Fin (compileAdvice q).b) : Nat :=
  bankTrialLiveSlotPotential i.val
    (bankTrialLiveWaveBit B i) (bankTrialLiveWaveToken B i)

private theorem bankTrialProbabilityCarryAsSum {q : Nat}
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b) :
    bankTrialLiveCarryValue B =
      (List.ofFn (bankTrialProbabilityDigitPotential B)).sum := by
  rfl

/-- One slot can increase by d, provided all other slots are
literal frames. -/
private theorem bankTrialProbabilityOneSlotBudget {m : Nat}
    (f g : Fin m → Nat) (i : Fin m) (d : Nat)
    (hframe : ∀ j : Fin m, j ≠ i → f j = g j)
    (hlocal : f i ≤ g i + d) :
    (List.ofFn f).sum ≤ (List.ofFn g).sum + d := by
  have hswap := bankTrialProbabilitySumSwapSingle f g i hframe
  omega

/-- Two adjacent digits share a conserved carry even though
either digit's individual summand can increase. -/
private theorem bankTrialProbabilityTwoSlotBudget {m : Nat}
    (f g : Fin m → Nat) (i j : Fin m)
    (hij : i ≠ j)
    (hframe : ∀ k : Fin m, k ≠ i → k ≠ j → f k = g k)
    (hlocal : f i + f j ≤ g i + g j) :
    (List.ofFn f).sum ≤ (List.ofFn g).sum := by
  have hleft : ∀ k : Fin m, k ≠ i →
      f k = (if k = i then g i else f k) := by
    intro k hk
    rw [if_neg hk]
  have hright : ∀ k : Fin m, k ≠ j →
      (if k = i then g i else f k) = g k := by
    intro k hk
    by_cases hi : k = i
    · rw [if_pos hi]
      rw [hi]
    · rw [if_neg hi]
      exact hframe k hi hk
  have hs1 := bankTrialProbabilitySumSwapSingle f
    (fun k => if k = i then g i else f k) i hleft
  have hs2 := bankTrialProbabilitySumSwapSingle
    (fun k => if k = i then g i else f k) g j hright
  have hmid : (if i = i then g i else f i) = g i :=
    if_pos rfl
  have hother : (if j = i then g i else f j) = f j :=
    if_neg (Ne.symm hij)
  rw [hmid] at hs1
  rw [hother] at hs2
  omega

/-- One-digit inequality for the literal root BANK owner, given
the stage-restricted first-worker token palette. -/
private theorem bankTrialProbabilityRawRootBudget
    (b : Nat) (theta : Nat → Bool) (x y : BankCell)
    (hb : 1 < b) (hx : x.role = 0) (hy : y.role = 1)
    (hg : x.grant = false) (hnr : x.mode ≠ .RESET)
    (hhead : (x.mode = .ARMED ∨ x.mode = .CSTART) →
      y.tok = .E)
    (hrwait : x.mode = .RWAIT →
      y.tok = .E ∨ y.tok = .RR ∨ y.tok = .RL)
    (hiwait : x.mode = .IWAIT →
      y.tok = .E ∨ y.tok = .IR ∨ y.tok = .AL)
    (hcwait : x.mode = .CWAIT →
      y.tok = .E ∨ y.tok = .CR0 ∨ y.tok = .CR1 ∨
        y.tok = .CL0 ∨ y.tok = .CL1) :
    bankTrialLiveSlotPotential 0
      (bankPair x y 1 b theta).2.bit
      (bankPair x y 1 b theta).2.tok ≤
    bankTrialLiveSlotPotential 0 y.bit y.tok +
      (if x.mode = .ARMED then 1 else 0) := by
  have hb1 : 1 ≤ b := by omega
  have hnot : b ≠ 1 := by omega
  cases hm : x.mode with
  | RESET =>
      exact False.elim (hnr hm)
  | ARMED =>
      have ht := hhead (Or.inl hm)
      cases hbit : y.bit <;>
        simp [bankPair, hx, hy, hg, hm, ht, hbit, hb1, hnot,
          bankTrialLiveSlotPotential, isWaitMode, isRetTok,
          Id.run_pure, Id.run_bind] <;>
        (repeat' split) <;> simp [bankTrialLiveSlotPotential] <;> omega
  | CSTART =>
      have ht := hhead (Or.inr hm)
      cases hbit : y.bit <;>
        cases htheta : theta 0 <;>
          simp [bankPair, hx, hy, hg, hm, ht, hbit, htheta, hb1,
            hnot, bankTrialLiveSlotPotential, isWaitMode, isRetTok,
            Id.run_pure, Id.run_bind] <;>
          (repeat' split) <;> simp [bankTrialLiveSlotPotential] <;> omega
  | RWAIT =>
      rcases hrwait hm with ht | ht | ht <;>
        cases hbit : y.bit <;>
        simp [bankPair, hx, hy, hg, hm, ht, hbit, hb1, hnot,
          bankTrialLiveSlotPotential, isWaitMode, isRetTok,
          Id.run_pure, Id.run_bind] <;>
        (repeat' split) <;> simp [bankTrialLiveSlotPotential] <;> omega
  | IWAIT =>
      rcases hiwait hm with ht | ht | ht <;>
        cases hbit : y.bit <;>
        simp [bankPair, hx, hy, hg, hm, ht, hbit, hb1, hnot,
          bankTrialLiveSlotPotential, isWaitMode, isRetTok,
          Id.run_pure, Id.run_bind] <;>
        (repeat' split) <;> simp [bankTrialLiveSlotPotential] <;> omega
  | CWAIT =>
      rcases hcwait hm with ht | ht | ht | ht | ht <;>
        cases hbit : y.bit <;>
        simp [bankPair, hx, hy, hg, hm, ht, hbit, hb1, hnot,
          bankTrialLiveSlotPotential, isWaitMode, isRetTok,
          Id.run_pure, Id.run_bind] <;>
        (repeat' split) <;> simp [bankTrialLiveSlotPotential] <;> omega

/-! ## Nonroot BANK carry: token-side proof, without an omega case product

The only nonzero token credit is IR. For non-IR rows,
bankPair either frames each bit or clears it. The IR-forward
row uses the already-proved exact two-slot carry identity.
The top IR row removes credit, and the lower IR row frames it.
-/

/-- A bit that is held or cleared cannot gain binary weight. -/
private theorem bankTrialProbabilityBitPotentialLe
    (u v : Bool) (w : Nat)
    (h : u = false ∨ u = v) :
    (if u then w else 0) ≤ (if v then w else 0) := by
  rcases h with h | h
  · rw [h]
    exact Nat.zero_le _
  · rw [h]
    exact Nat.le_refl _

/-- A non-IR token has no extra credit. Only bit-clearing
monotonicity remains, independently at both sites. -/
private theorem bankTrialProbabilityNonIRPotentialLe
    (j : Nat) (x y u v : BankCell)
    (hx : x.tok ≠ .IR) (hy : y.tok ≠ .IR)
    (hu : u.tok ≠ .IR) (hv : v.tok ≠ .IR)
    (hux : u.bit = false ∨ u.bit = x.bit)
    (hvy : v.bit = false ∨ v.bit = y.bit) :
    bankTrialLiveSlotPotential j u.bit u.tok +
      bankTrialLiveSlotPotential (j + 1) v.bit v.tok ≤
    bankTrialLiveSlotPotential j x.bit x.tok +
      bankTrialLiveSlotPotential (j + 1) y.bit y.tok := by
  have hleft := bankTrialProbabilityBitPotentialLe
    u.bit x.bit (2 ^ j) hux
  have hright := bankTrialProbabilityBitPotentialLe
    v.bit y.bit (2 ^ (j + 1)) hvy
  have hsum := Nat.add_le_add hleft hright
  simpa [bankTrialLiveSlotPotential, hx, hy, hu, hv] using hsum

/-- Source E and non-IR target: handle RR/ RL turnarounds,
AL/CL returns, CR top turns, and literal frames as separate
small token cases. No arithmetic of powers occurs here. -/
private theorem bankTrialProbabilityNonIRLeftEmptyData
    (b : Nat) (theta : Nat → Bool) (x y : BankCell)
    (hx : 1 ≤ x.role) (hlt : x.role < b)
    (hy : y.role = x.role + 1)
    (hex : x.tok = .E) (hny : y.tok ≠ .IR) :
    (bankPair x y y.role b theta).1.tok ≠ .IR ∧
    (bankPair x y y.role b theta).2.tok ≠ .IR ∧
    ((bankPair x y y.role b theta).1.bit = false ∨
      (bankPair x y y.role b theta).1.bit = x.bit) ∧
    ((bankPair x y y.role b theta).2.bit = false ∨
      (bankPair x y y.role b theta).2.bit = y.bit) := by
  obtain ⟨hxn, hxTop, hyn, hyPos, hyLe, hxLe⟩ :=
    bankTrialInteriorRoles b x y hx hlt hy
  cases ht : y.tok with
  | E =>
      simp [bankPair, hx, hlt, hy, hxn, hxTop,
        hyn, hyPos, hyLe, hxLe, hex, ht,
        Id.run_pure, Id.run_bind] <;>
        (repeat' split) <;> simp
  | RR =>
      simp [bankPair, hx, hlt, hy, hxn, hxTop,
        hyn, hyPos, hyLe, hxLe, hex, ht,
        Id.run_pure, Id.run_bind] <;>
        (repeat' split) <;> simp
  | RL =>
      simp [bankPair, hx, hlt, hy, hxn, hxTop,
        hyn, hyPos, hyLe, hxLe, hex, ht,
        Id.run_pure, Id.run_bind] <;>
        (repeat' split) <;> simp
  | IR => exact False.elim (hny ht)
  | AL =>
      simp [bankPair, hx, hlt, hy, hxn, hxTop,
        hyn, hyPos, hyLe, hxLe, hex, ht,
        Id.run_pure, Id.run_bind] <;>
        (repeat' split) <;> simp
  | CR0 =>
      simp [bankPair, hx, hlt, hy, hxn, hxTop,
        hyn, hyPos, hyLe, hxLe, hex, ht,
        Id.run_pure, Id.run_bind] <;>
        (repeat' split) <;> simp
  | CR1 =>
      simp [bankPair, hx, hlt, hy, hxn, hxTop,
        hyn, hyPos, hyLe, hxLe, hex, ht,
        Id.run_pure, Id.run_bind] <;>
        (repeat' split) <;> simp
  | CL0 =>
      simp [bankPair, hx, hlt, hy, hxn, hxTop,
        hyn, hyPos, hyLe, hxLe, hex, ht,
        Id.run_pure, Id.run_bind] <;>
        (repeat' split) <;> simp
  | CL1 =>
      simp [bankPair, hx, hlt, hy, hxn, hxTop,
        hyn, hyPos, hyLe, hxLe, hex, ht,
        Id.run_pure, Id.run_bind] <;>
        (repeat' split) <;> simp

/-- Target E and non-IR source: handle RR propagation,
CR propagation, AL/RL/CL frames, and E/E separately. -/
private theorem bankTrialProbabilityNonIRRightEmptyData
    (b : Nat) (theta : Nat → Bool) (x y : BankCell)
    (hx : 1 ≤ x.role) (hlt : x.role < b)
    (hy : y.role = x.role + 1)
    (hey : y.tok = .E) (hnx : x.tok ≠ .IR) :
    (bankPair x y y.role b theta).1.tok ≠ .IR ∧
    (bankPair x y y.role b theta).2.tok ≠ .IR ∧
    ((bankPair x y y.role b theta).1.bit = false ∨
      (bankPair x y y.role b theta).1.bit = x.bit) ∧
    ((bankPair x y y.role b theta).2.bit = false ∨
      (bankPair x y y.role b theta).2.bit = y.bit) := by
  obtain ⟨hxn, hxTop, hyn, hyPos, hyLe, hxLe⟩ :=
    bankTrialInteriorRoles b x y hx hlt hy
  cases ht : x.tok with
  | E =>
      simp [bankPair, hx, hlt, hy, hxn, hxTop,
        hyn, hyPos, hyLe, hxLe, hey, ht,
        Id.run_pure, Id.run_bind] <;>
        (repeat' split) <;> simp
  | RR =>
      simp [bankPair, hx, hlt, hy, hxn, hxTop,
        hyn, hyPos, hyLe, hxLe, hey, ht,
        Id.run_pure, Id.run_bind] <;>
        (repeat' split) <;> simp
  | RL =>
      simp [bankPair, hx, hlt, hy, hxn, hxTop,
        hyn, hyPos, hyLe, hxLe, hey, ht,
        Id.run_pure, Id.run_bind] <;>
        (repeat' split) <;> simp
  | IR => exact False.elim (hnx ht)
  | AL =>
      simp [bankPair, hx, hlt, hy, hxn, hxTop,
        hyn, hyPos, hyLe, hxLe, hey, ht,
        Id.run_pure, Id.run_bind] <;>
        (repeat' split) <;> simp
  | CR0 =>
      simp [bankPair, hx, hlt, hy, hxn, hxTop,
        hyn, hyPos, hyLe, hxLe, hey, ht,
        Id.run_pure, Id.run_bind] <;>
        (repeat' split) <;> simp
  | CR1 =>
      simp [bankPair, hx, hlt, hy, hxn, hxTop,
        hyn, hyPos, hyLe, hxLe, hey, ht,
        Id.run_pure, Id.run_bind] <;>
        (repeat' split) <;> simp
  | CL0 =>
      simp [bankPair, hx, hlt, hy, hxn, hxTop,
        hyn, hyPos, hyLe, hxLe, hey, ht,
        Id.run_pure, Id.run_bind] <;>
        (repeat' split) <;> simp
  | CL1 =>
      simp [bankPair, hx, hlt, hy, hxn, hxTop,
        hyn, hyPos, hyLe, hxLe, hey, ht,
        Id.run_pure, Id.run_bind] <;>
        (repeat' split) <;> simp

/-- Structural token classification, assembled from the two
one-sided non-IR case tables. -/
private theorem bankTrialProbabilityNonIRPairData
    (b : Nat) (theta : Nat → Bool) (x y : BankCell)
    (hx : 1 ≤ x.role) (hlt : x.role < b)
    (hy : y.role = x.role + 1)
    (hsolo : x.tok = .E ∨ y.tok = .E)
    (hnx : x.tok ≠ .IR) (hny : y.tok ≠ .IR) :
    (bankPair x y y.role b theta).1.tok ≠ .IR ∧
    (bankPair x y y.role b theta).2.tok ≠ .IR ∧
    ((bankPair x y y.role b theta).1.bit = false ∨
      (bankPair x y y.role b theta).1.bit = x.bit) ∧
    ((bankPair x y y.role b theta).2.bit = false ∨
      (bankPair x y y.role b theta).2.bit = y.bit) := by
  rcases hsolo with hex | hey
  · exact bankTrialProbabilityNonIRLeftEmptyData
      b theta x y hx hlt hy hex hny
  · exact bankTrialProbabilityNonIRRightEmptyData
      b theta x y hx hlt hy hey hnx

/-- Source IR, destination E: the literal bankPair row
and the previously proved IR carry arithmetic give equality. -/
private theorem bankTrialProbabilitySourceIRBudget
    (j b : Nat) (theta : Nat → Bool) (x y : BankCell)
    (hx : 1 ≤ x.role) (hlt : x.role < b)
    (hy : y.role = x.role + 1)
    (hxt : x.tok = .IR) (hyt : y.tok = .E) :
    bankTrialLiveSlotPotential j
        (bankPair x y y.role b theta).1.bit
        (bankPair x y y.role b theta).1.tok +
      bankTrialLiveSlotPotential (j + 1)
        (bankPair x y y.role b theta).2.bit
        (bankPair x y y.role b theta).2.tok ≤
      bankTrialLiveSlotPotential j x.bit x.tok +
        bankTrialLiveSlotPotential (j + 1) y.bit y.tok := by
  obtain ⟨hxn, hxTop, hyn, hyPos, hyLe, hxLe⟩ :=
    bankTrialInteriorRoles b x y hx hlt hy
  have hxb :
      (bankPair x y y.role b theta).1.bit = x.bit := by
    simp [bankPair, hx, hlt, hy, hxn, hxTop,
      hyn, hyPos, hyLe, hxLe, hxt, hyt,
      Id.run_pure, Id.run_bind]
  have hrow := bankTrialInteriorIRForward
    b theta x y hx hlt hy hxt hyt
  rw [hxb, hrow.1, hrow.2.1, hrow.2.2, hxt, hyt]
  rw [bankTrialLiveIRForwardArithmetic j x.bit y.bit]
  all_goals exact Nat.le_refl _

/-- Target IR, source E: at the top the old IR is erased;
away from the top the pair is a literal frame. -/
private theorem bankTrialProbabilityTargetIRBudget
    (j b : Nat) (theta : Nat → Bool) (x y : BankCell)
    (hx : 1 ≤ x.role) (hlt : x.role < b)
    (hy : y.role = x.role + 1)
    (hxt : x.tok = .E) (hyt : y.tok = .IR) :
    bankTrialLiveSlotPotential j
        (bankPair x y y.role b theta).1.bit
        (bankPair x y y.role b theta).1.tok +
      bankTrialLiveSlotPotential (j + 1)
        (bankPair x y y.role b theta).2.bit
        (bankPair x y y.role b theta).2.tok ≤
      bankTrialLiveSlotPotential j x.bit x.tok +
        bankTrialLiveSlotPotential (j + 1) y.bit y.tok := by
  by_cases htop : y.role = b
  · have hrow := bankTrialInteriorTopIRAbsorbed
      b theta x y hx hlt hy htop hxt hyt
    rw [hrow.1, hrow.2.1, hrow.2.2.1,
      hrow.2.2.2, hxt, hyt]
    have hdrop :
        bankTrialLiveSlotPotential (j + 1) y.bit .E ≤
          bankTrialLiveSlotPotential (j + 1) y.bit .IR := by
      simp [bankTrialLiveSlotPotential] <;> omega
    exact Nat.add_le_add_left hdrop _
  · obtain ⟨hxn, hxTop, hyn, hyPos, hyLe, hxLe⟩ :=
      bankTrialInteriorRoles b x y hx hlt hy
    have hnb : ¬ b < x.role + 1 := by omega
    have hnb2 : ¬ b < y.role + 1 := by omega
    have htop' : ¬ x.role + 1 = b := by omega
    have hframe :
        (bankPair x y y.role b theta).1.tok = .E ∧
        (bankPair x y y.role b theta).2.tok = .IR ∧
        (bankPair x y y.role b theta).1.bit = x.bit ∧
        (bankPair x y y.role b theta).2.bit = y.bit := by
      simp [bankPair, hx, hlt, hy, hxn, hxTop,
        hyn, hyPos, hyLe, hxLe, htop, hnb, hnb2, htop',
        hxt, hyt, Id.run_pure, Id.run_bind]
    rw [hframe.1, hframe.2.1, hframe.2.2.1,
      hframe.2.2.2, hxt, hyt]
    exact Nat.le_refl _

/-- Complete nonroot carry inequality. There are three cases:
IR at the source, IR at the target, or no IR anywhere.
All other token kinds use the source-level data/frame lemma. -/
private theorem bankTrialProbabilityRawInteriorBudget
    (j b : Nat) (theta : Nat → Bool)
    (x y : BankCell)
    (hj : j + 2 ≤ b)
    (hx : x.role = j + 1) (hy : y.role = j + 2)
    (hsolo : x.tok = .E ∨ y.tok = .E) :
    bankTrialLiveSlotPotential j
        (bankPair x y (j + 2) b theta).1.bit
        (bankPair x y (j + 2) b theta).1.tok +
      bankTrialLiveSlotPotential (j + 1)
        (bankPair x y (j + 2) b theta).2.bit
        (bankPair x y (j + 2) b theta).2.tok ≤
      bankTrialLiveSlotPotential j x.bit x.tok +
        bankTrialLiveSlotPotential (j + 1) y.bit y.tok := by
  have hpos : 1 ≤ x.role := by omega
  have hlt : x.role < b := by omega
  have hsucc : y.role = x.role + 1 := by omega
  have hrole : y.role = j + 2 := hy
  have hp :
      bankPair x y (j + 2) b theta =
        bankPair x y y.role b theta := by
    rw [hrole]
  rw [hp]
  by_cases hsource : x.tok = .IR
  · have htarget : y.tok = .E := by
      rcases hsolo with hex | hey
      · rw [hsource] at hex
        cases hex
      · exact hey
    exact bankTrialProbabilitySourceIRBudget
      j b theta x y hpos hlt hsucc hsource htarget
  · by_cases htarget : y.tok = .IR
    · have hsourceE : x.tok = .E := by
        rcases hsolo with hex | hey
        · exact hex
        · rw [htarget] at hey
          cases hey
      exact bankTrialProbabilityTargetIRBudget
        j b theta x y hpos hlt hsucc hsourceE htarget
    · obtain ⟨hleft, hright, hbitx, hbity⟩ :=
        bankTrialProbabilityNonIRPairData
          b theta x y hpos hlt hsucc hsolo
          hsource htarget
      exact bankTrialProbabilityNonIRPotentialLe
        j x y (bankPair x y y.role b theta).1
          (bankPair x y y.role b theta).2
        hsource htarget hleft hright hbitx hbity

/-- Root-patch potential is paid for by exactly one OLD ARMED
head, with untouched higher digits framed. -/
private theorem bankTrialProbabilityRootPatchBudget {q : Nat}
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hc : BankTrialLiveWaveCertificate q B)
    (hnr : bankTrialLiveWaveRootMode B ≠ .RESET) :
    bankTrialLiveCarryValue (bankTrialWindowRootPatch B) ≤
      bankTrialLiveCarryValue B +
        (if bankTrialLiveWaveRootMode B = .ARMED then 1 else 0) := by
  have hb : 1 < (compileAdvice q).b := by
    change 1 < (compileAdvice q).s + 11
    omega
  have hhead : ((bankTrialWindowRootCell B).mode = .ARMED ∨
      (bankTrialWindowRootCell B).mode = .CSTART) →
      (bankTrialWindowFirstCell B).tok = .E := by
    intro hm
    exact hc.headClear ⟨0, by omega⟩ hm
  have hrwait : (bankTrialWindowRootCell B).mode = .RWAIT →
      (bankTrialWindowFirstCell B).tok = .E ∨
      (bankTrialWindowFirstCell B).tok = .RR ∨
      (bankTrialWindowFirstCell B).tok = .RL := by
    intro hm
    exact hc.resetTokens ⟨0, by omega⟩ hm
  have hiwait : (bankTrialWindowRootCell B).mode = .IWAIT →
      (bankTrialWindowFirstCell B).tok = .E ∨
      (bankTrialWindowFirstCell B).tok = .IR ∨
      (bankTrialWindowFirstCell B).tok = .AL := by
    intro hm
    exact hc.iwaitTokens ⟨0, by omega⟩ hm
  have hcwait : (bankTrialWindowRootCell B).mode = .CWAIT →
      (bankTrialWindowFirstCell B).tok = .E ∨
      (bankTrialWindowFirstCell B).tok = .CR0 ∨
      (bankTrialWindowFirstCell B).tok = .CR1 ∨
      (bankTrialWindowFirstCell B).tok = .CL0 ∨
      (bankTrialWindowFirstCell B).tok = .CL1 := by
    intro hm
    have h := hc.cwaitTokens ⟨0, by omega⟩ hm
    rw [← bankTrialWindowRootOldFirstToken B] at h
    exact h
  have hraw := bankTrialProbabilityRawRootBudget
    (compileAdvice q).b (compileAdvice q).theta
    (bankTrialWindowRootCell B) (bankTrialWindowFirstCell B)
    hb rfl rfl rfl hnr hhead hrwait hiwait hcwait
  rw [bankTrialWindowRootOldMode B] at hraw
  rw [bankTrialWindowRootOldFirstToken B,
      bankTrialWindowRootOldFirstBit B] at hraw
  have hfirst : bankTrialProbabilityDigitPotential
      (bankTrialWindowRootPatch B) ⟨0, by omega⟩ ≤
    bankTrialProbabilityDigitPotential B ⟨0, by omega⟩ +
      (if bankTrialLiveWaveRootMode B = .ARMED then 1 else 0) := by
    change bankTrialLiveSlotPotential 0
        (bankTrialLiveWaveBit (bankTrialWindowRootPatch B)
          ⟨0, by omega⟩)
        (bankTrialLiveWaveToken (bankTrialWindowRootPatch B)
          ⟨0, by omega⟩) ≤
      bankTrialLiveSlotPotential 0
        (bankTrialLiveWaveBit B ⟨0, by omega⟩)
        (bankTrialLiveWaveToken B ⟨0, by omega⟩) +
        (if bankTrialLiveWaveRootMode B = .ARMED then 1 else 0)
    rw [bankTrialWindowRootPatchFirstBit,
      bankTrialWindowRootPatchFirstToken]
    exact hraw
  have hframe : ∀ i : Fin (compileAdvice q).b,
      i ≠ ⟨0, by omega⟩ →
      bankTrialProbabilityDigitPotential (bankTrialWindowRootPatch B) i =
        bankTrialProbabilityDigitPotential B i := by
    intro i hi
    unfold bankTrialProbabilityDigitPotential
    rw [bankTrialWindowRootPatchTailBit B i hi,
      bankTrialWindowRootPatchTailToken B i hi]
  rw [bankTrialProbabilityCarryAsSum,
    bankTrialProbabilityCarryAsSum]
  exact bankTrialProbabilityOneSlotBudget
    (bankTrialProbabilityDigitPotential (bankTrialWindowRootPatch B))
    (bankTrialProbabilityDigitPotential B)
    ⟨0, by omega⟩
    (if bankTrialLiveWaveRootMode B = .ARMED then 1 else 0)
    hframe hfirst

/-- One proper interior service conserves the two-slot sum of
ordinary digit value plus IR credit. -/
private theorem bankTrialProbabilityInteriorPatchBudget {q : Nat}
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (j : Fin (compileAdvice q).b)
    (hj : 0 < j.val)
    (hc : BankTrialLiveWaveCertificate q B) :
    bankTrialLiveCarryValue (bankTrialWindowInteriorPatch B j) ≤
      bankTrialLiveCarryValue B := by
  have hsolo := bankTrialInteriorOldPairSolo B j hj hc
  have hpair := bankTrialProbabilityRawInteriorBudget
    (j.val - 1) (compileAdvice q).b (compileAdvice q).theta
    (bankTrialInteriorLeftCell B j)
    (bankTrialInteriorRightCell B j)
    (by have h := j.isLt; omega)
    (by change j.val = (j.val - 1) + 1; omega)
    (by change j.val + 1 = (j.val - 1) + 2; omega)
    hsolo
  have hlocal :
      bankTrialProbabilityDigitPotential
        (bankTrialWindowInteriorPatch B j)
          (bankTrialInteriorLeftDigit j hj) +
      bankTrialProbabilityDigitPotential
        (bankTrialWindowInteriorPatch B j) j ≤
      bankTrialProbabilityDigitPotential B
        (bankTrialInteriorLeftDigit j hj) +
      bankTrialProbabilityDigitPotential B j := by
    unfold bankTrialProbabilityDigitPotential
    rw [bankTrialInteriorNewLeftToken B j hj,
      bankTrialInteriorNewRightToken B j,
      bankTrialInteriorNewLeftBit B j hj,
      bankTrialInteriorNewRightBit B j,
      ← bankTrialInteriorOldLeftToken B j hj,
      ← bankTrialInteriorOldRightToken B j,
      ← bankTrialInteriorOldLeftBit B j hj,
      ← bankTrialInteriorOldRightBit B j]
    change bankTrialLiveSlotPotential (j.val - 1)
        (GrantBankReference.bankLocalReferenceInternalPair q B j).1.bit
        (GrantBankReference.bankLocalReferenceInternalPair q B j).1.tok +
      bankTrialLiveSlotPotential j.val
        (GrantBankReference.bankLocalReferenceInternalPair q B j).2.bit
        (GrantBankReference.bankLocalReferenceInternalPair q B j).2.tok ≤
      bankTrialLiveSlotPotential (j.val - 1)
        (bankTrialInteriorLeftCell B j).bit
        (bankTrialInteriorLeftCell B j).tok +
      bankTrialLiveSlotPotential j.val
        (bankTrialInteriorRightCell B j).bit
        (bankTrialInteriorRightCell B j).tok
    have hi : j.val - 1 + 1 = j.val := by omega
    have ho : j.val - 1 + 2 = j.val + 1 := by omega
    simpa only [hi, ho,
      GrantBankReference.bankLocalReferenceInternalPair,
      bankTrialInteriorLeftCell, bankTrialInteriorRightCell] using hpair
  have hne : bankTrialInteriorLeftDigit j hj ≠ j := by
    intro he
    have hv := congrArg Fin.val he
    change j.val - 1 = j.val at hv
    omega
  have hframe : ∀ k : Fin (compileAdvice q).b,
      k ≠ bankTrialInteriorLeftDigit j hj →
      k ≠ j →
      bankTrialProbabilityDigitPotential
        (bankTrialWindowInteriorPatch B j) k =
          bankTrialProbabilityDigitPotential B k := by
    intro k hl hr
    have hi := bankTrialInteriorOutsideIndices j hj k
      (by intro he; rcases he with he | he; exact hl he; exact hr he)
    unfold bankTrialProbabilityDigitPotential
    rw [bankTrialInteriorPatchBitFrame B j k hi.1 hi.2,
      bankTrialInteriorPatchTokenFrame B j k hi.1 hi.2]
  rw [bankTrialProbabilityCarryAsSum,
    bankTrialProbabilityCarryAsSum]
  exact bankTrialProbabilityTwoSlotBudget
    (bankTrialProbabilityDigitPotential
      (bankTrialWindowInteriorPatch B j))
    (bankTrialProbabilityDigitPotential B)
    (bankTrialInteriorLeftDigit j hj) j hne hframe hlocal

/-- The top unary erasure cannot increase any digit's
carry-aware contribution. -/
private theorem bankTrialProbabilityTopPatchBudget {q : Nat}
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b) :
    bankTrialLiveCarryValue (bankTrialWindowTopPatch B) ≤
      bankTrialLiveCarryValue B := by
  rw [bankTrialProbabilityCarryAsSum,
    bankTrialProbabilityCarryAsSum]
  apply FiniteUniformStoppingTree.ofFn_sum_le
  intro k
  by_cases ht : k.val + 1 = (compileAdvice q).b
  · have hbit :
        bankTrialLiveWaveBit (bankTrialWindowTopPatch B) k =
          (GrantBankReference.bankLocalReferenceClampedQuad q
            (GrantBankReference.topBoundaryBankMap
              (GrantBankReference.bankLocalReferenceCell B
                ⟨k.val + 1, by omega⟩))).2.1 := by
      simp [bankTrialLiveWaveBit, bankTrialWindowTopPatch, ht]
    have htok :
        bankTrialLiveWaveToken (bankTrialWindowTopPatch B) k =
          (GrantBankReference.bankLocalReferenceClampedQuad q
            (GrantBankReference.topBoundaryBankMap
              (GrantBankReference.bankLocalReferenceCell B
                ⟨k.val + 1, by omega⟩))).2.2.1 := by
      simp [bankTrialLiveWaveToken, bankTrialWindowTopPatch, ht]
    unfold bankTrialProbabilityDigitPotential
    rw [hbit, htok]
    exact bankTrialLiveTopClampedPotential q k.val
      (GrantBankReference.bankLocalReferenceCell B
        ⟨k.val + 1, by omega⟩)
  · unfold bankTrialProbabilityDigitPotential
    rw [bankTrialWindowTopPatchBits B k]
    have hf : bankTrialLiveWaveToken
        (bankTrialWindowTopPatch B) k =
          bankTrialLiveWaveToken B k := by
      simp [bankTrialLiveWaveToken, bankTrialWindowTopPatch, ht]
    rw [hf]
    all_goals exact Nat.le_refl _

/-- The incoming-root unary update has no weighted digit. -/
private theorem bankTrialProbabilityIncomingPatchBudget {q : Nat}
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b) :
    bankTrialLiveCarryValue (bankTrialWindowIncomingPatch B) =
      bankTrialLiveCarryValue B := by
  unfold bankTrialLiveCarryValue
  apply FiniteUniformStoppingTree.ofFn_sum_eq
  intro k
  have hframe := bankTrialWindowIncomingPatchDigitFrame B k
  change bankTrialLiveSlotPotential k.val
      (bankTrialLiveWaveBit (bankTrialWindowIncomingPatch B) k)
      (bankTrialLiveWaveToken (bankTrialWindowIncomingPatch B) k) =
    bankTrialLiveSlotPotential k.val
      (bankTrialLiveWaveBit B k)
      (bankTrialLiveWaveToken B k)
  rw [hframe.1, hframe.2]

end L3

/-!
The four physical BANK edge classes. This proof uses the same
nonalias geometry as G11b, but tracks weighted digit potential,
rather than stage and ancestry clauses.
-/

namespace L3

open Classical

set_option autoImplicit false
set_option Elab.async false

private theorem bankTrialProbabilityCarryFieldsCongr {q : Nat}
    (A B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hfields : A.fields = B.fields) :
    bankTrialLiveCarryValue A = bankTrialLiveCarryValue B := by
  unfold bankTrialLiveCarryValue
  simp only [hfields]

/-- Weighted row bound for the actual clamped reference under
the old LIVE certificate and spatial nonalias. This does not
assert the false ring-size-free raw row premise. -/
private theorem bankTrialProbabilityLockedRawRowBudget {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (hw : BankTrialLiveWindowNonalias n q)
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hc : BankTrialLiveWaveCertificate q B)
    (hnr : bankTrialLiveWaveRootMode B ≠ .RESET)
    (hf : B.success = false) :
    bankTrialLiveCarryValue
      (GrantBankReference.bankLocalReferenceStepClamped
        ring root B e) ≤
      bankTrialLiveCarryValue B +
        (if (B.fields ⟨0, by omega⟩).1 = .ARMED ∧ e = root
         then 1 else 0) := by
  rcases Counter.resetTrialEdgeGeometry (q := q)
      ring root e with hsource | hin | hout
  · obtain ⟨j, hj, he⟩ := hsource
    by_cases htop : j = (compileAdvice q).b
    · subst j
      have hfields := bankTrialWindowTopFieldsEqPatch
        ring root hw B hf
      have hvalue := bankTrialProbabilityCarryFieldsCongr
        (GrantBankReference.bankLocalReferenceStepClamped
          ring root B (Counter.site ring root (compileAdvice q).b))
        (bankTrialWindowTopPatch B) hfields
      have hneq : Counter.site ring root (compileAdvice q).b ≠ root := by
        intro h
        have heq : Counter.site ring root (compileAdvice q).b =
            Counter.site ring root 0 := h
        have hv := bankTrialWindowSitesDistinct ring root hw
          (compileAdvice q).b 0 (by omega) (by omega) heq
        have hb : 0 < (compileAdvice q).b := by
          change 0 < (compileAdvice q).s + 11
          omega
        omega
      rw [he, hvalue]
      have hnon : ¬ ((B.fields ⟨0, by omega⟩).1 = .ARMED ∧
          Counter.site ring root (compileAdvice q).b = root) := by
        intro h
        exact hneq h.2
      rw [if_neg hnon]
      exact bankTrialProbabilityTopPatchBudget B
    · by_cases hzero : j = 0
      · subst j
        have hfields := bankTrialWindowRootFieldsEqPatch
          ring root hw B hf
        have hvalue := bankTrialProbabilityCarryFieldsCongr
          (GrantBankReference.bankLocalReferenceStepClamped
            ring root B root) (bankTrialWindowRootPatch B) hfields
        have hroot := bankTrialProbabilityRootPatchBudget B hc hnr
        have hs0 : Counter.site ring root 0 = root := by
          simp [Counter.site]
        have hvalue' :
            bankTrialLiveCarryValue
              (GrantBankReference.bankLocalReferenceStepClamped
                ring root B (Counter.site ring root 0)) =
            bankTrialLiveCarryValue (bankTrialWindowRootPatch B) := by
          rw [hs0]
          exact hvalue
        rw [he, hvalue']
        change bankTrialLiveCarryValue (bankTrialWindowRootPatch B) ≤
          bankTrialLiveCarryValue B +
            (if bankTrialLiveWaveRootMode B = .ARMED ∧
               Counter.site ring root 0 = root then 1 else 0)
        have hdelta :
            (if bankTrialLiveWaveRootMode B = .ARMED ∧
              Counter.site ring root 0 = root then 1 else 0) =
            (if bankTrialLiveWaveRootMode B = .ARMED then 1 else 0) := by
          simp [Counter.site]
        rw [hdelta]
        exact hroot
      · have hlt : j < (compileAdvice q).b := by omega
        have hjpos : 0 < j := by omega
        have hfields := bankTrialWindowInteriorFieldsEqPatch
          ring root hw B hf ⟨j, hlt⟩ hjpos
        have hvalue := bankTrialProbabilityCarryFieldsCongr
          (GrantBankReference.bankLocalReferenceStepClamped
            ring root B (Counter.site ring root j))
          (bankTrialWindowInteriorPatch B ⟨j, hlt⟩) hfields
        have hneq := bankTrialWindowInteriorNotRoot ring root hw
          ⟨j, hlt⟩ hjpos
        rw [he, hvalue]
        have hnon : ¬ ((B.fields ⟨0, by omega⟩).1 = .ARMED ∧
            Counter.site ring root j = root) := by
          intro h
          exact hneq h.2
        rw [if_neg hnon]
        exact bankTrialProbabilityInteriorPatchBudget B
          ⟨j, hlt⟩ hjpos hc
  · have hfields := bankTrialWindowIncomingFieldsEqPatch
      ring root e hw hin B hf
    have hvalue := bankTrialProbabilityCarryFieldsCongr
      (GrantBankReference.bankLocalReferenceStepClamped
        ring root B e) (bankTrialWindowIncomingPatch B) hfields
    have hne : e ≠ root := by
      intro he
      subst e
      have hsite : Counter.site ring root 1 =
          Counter.site ring root 0 := hin
      have hv := bankTrialWindowSitesDistinct ring root hw
        1 0 (by omega) (by omega) hsite
      omega
    have hnon : ¬ ((B.fields ⟨0, by omega⟩).1 = .ARMED ∧
        e = root) := by
      intro h
      exact hne h.2
    rw [hvalue, if_neg hnon,
      bankTrialProbabilityIncomingPatchBudget B]
    all_goals exact Nat.le_add_right _ _
  · have houtside : ¬ Counter.Support q ring root e := by
      intro hs
      rcases hs with hs | ⟨j, hj, he⟩
      · exact (hout 0 (by omega)).2 hs
      · exact (hout j hj).1 he
    have heq := bankTrialLocalStepOutside ring root e B houtside
    rw [heq]
    have hne : e ≠ root := by
      intro he
      subst e
      apply houtside
      exact Or.inr ⟨0, Nat.zero_le _, rfl⟩
    have hnon : ¬ ((B.fields ⟨0, by omega⟩).1 = .ARMED ∧
        e = root) := by
      intro h
      exact hne h.2
    rw [if_neg hnon]
    exact Nat.le_refl _

/-- The budget is required only on an OLD LIVE locked state
whose actual successor is also LIVE. Terminal and recovery
states have no carry-ledger postcondition. -/
theorem bankTrialProbabilityLockedCarryLiveStep {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (hw : BankTrialLiveWindowNonalias n q)
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (begun nextBegun : Bool)
    (hlock : BankTrialLiveNoResetLocked
      (⟨B, .live begun⟩ : BankTrialLocalState q))
    (hnext : (bankTrialLocalNext ring root
      (⟨B, .live begun⟩ : BankTrialLocalState q) e).phase =
        .live nextBegun) :
    bankTrialLiveCarryValue
      (bankTrialLocalNext ring root
        (⟨B, .live begun⟩ : BankTrialLocalState q) e).bank ≤
    bankTrialLiveCarryValue B +
      (if BankTrialProbabilityArmedGate
          (⟨B, .live begun⟩ : BankTrialLocalState q) ∧
          e = root then 1 else 0) := by
  have hc : BankTrialLiveWaveCertificate q B :=
    hlock.1 begun rfl
  have hnr : bankTrialLiveWaveRootMode B ≠ .RESET :=
    hlock.2 begun rfl
  have hf := bankTrialWindowLiveOldNotLatched
    ring root e B begun nextBegun hnext
  have hr := bankTrialProbabilityLockedRawRowBudget
    ring root e hw B hc hnr hf
  have hbank := bankTrialLocalNextLiveBank ring root e B begun
  have hdelta :
      (if (B.fields ⟨0, by omega⟩).1 = .ARMED ∧
        e = root then 1 else 0) =
      (if BankTrialProbabilityArmedGate
        (⟨B, .live begun⟩ : BankTrialLocalState q) ∧
        e = root then 1 else 0) := by
    by_cases hm : (B.fields ⟨0, by omega⟩).1 = .ARMED
    · have hg : BankTrialProbabilityArmedGate
          (⟨B, .live begun⟩ : BankTrialLocalState q) :=
        ⟨⟨begun, rfl⟩, hm⟩
      by_cases he : e = root
      · rw [if_pos ⟨hm, he⟩, if_pos ⟨hg, he⟩]
      · rw [if_neg (fun h => he h.2), if_neg (fun h => he h.2)]
    · have hg : ¬ BankTrialProbabilityArmedGate
          (⟨B, .live begun⟩ : BankTrialLocalState q) := by
        intro h
        exact hm h.2
      rw [if_neg (fun h => hm h.1), if_neg (fun h => hg h.1)]
  rw [hbank, ← hdelta]
  exact hr

/-- A locked state and its carry budget evolve together.
The assertion for RECOVERY/WON/LOST is vacuous. -/
private theorem bankTrialProbabilityLockedCarryLedgerStep {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (hw : BankTrialLiveWindowNonalias n q)
    (z : BankTrialLocalState q) (heads : Nat)
    (hlock : BankTrialLiveNoResetLocked z)
    (hledger : BankTrialLiveCarryLedger z heads) :
    BankTrialLiveCarryLedger
      (bankTrialLocalNext ring root z e)
      (heads +
        (if BankTrialProbabilityArmedGate z ∧ e = root
         then 1 else 0)) := by
  cases z with
  | mk B phase =>
    cases phase with
    | live begun =>
      intro nextBegun hnext
      have hprev : bankTrialLiveCarryValue B ≤ heads :=
        hledger begun rfl
      have hstep := bankTrialProbabilityLockedCarryLiveStep
        ring root e hw B begun nextBegun hlock hnext
      exact Nat.le_trans hstep (Nat.add_le_add_right hprev _)
    | recovery =>
      intro nextBegun hnext
      simp [bankTrialLocalNext] at hnext <;>
        (repeat' split at hnext) <;> cases hnext
    | won =>
      intro nextBegun hnext
      simp [bankTrialLocalNext] at hnext
    | lost =>
      intro nextBegun hnext
      simp [bankTrialLocalNext] at hnext

/-- No arbitrary-B raw-row premise: the strengthened G11b lock
is transported simultaneously with the actual head budget. -/
theorem bankTrialProbabilityLockedCarryAllWords {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hw : BankTrialLiveWindowNonalias n q) :
    ∀ (word : List (Fin n)) (z : BankTrialLocalState q)
      (heads : Nat),
      BankTrialLiveNoResetLocked z →
      BankTrialLiveCarryLedger z heads →
      BankTrialLiveCarryLedger
        (bankTrialLocalRun ring root word z)
        (heads + bankTrialLiveHeadCount ring root word z) := by
  have hrows := bankTrialWindowRowsOfClasses ring root
    (bankTrialWindowRootOutgoingRows ring root)
    (bankTrialWindowInteriorRowsOfPairRows ring root
      (bankTrialLiveInteriorPairRows q))
    (bankTrialWindowTopRows ring root)
    (bankTrialWindowIncomingRows ring root)
  intro word
  induction word with
  | nil =>
      intro z heads hlock hledger
      simpa [bankTrialLocalRun, bankTrialLiveHeadCount] using hledger
  | cons e tail ih =>
      intro z heads hlock hledger
      have hnext := bankTrialProbabilityLockedCarryLedgerStep
        ring root e hw z heads hlock hledger
      have hnextLock := bankTrialWindowLockedNextOfRows
        ring root e hw hrows z hlock
      have htail := ih (bankTrialLocalNext ring root z e)
        (heads +
          (if BankTrialProbabilityArmedGate z ∧ e = root
           then 1 else 0)) hnextLock hnext
      change BankTrialLiveCarryLedger
        (bankTrialLocalRun ring root tail
          (bankTrialLocalNext ring root z e))
        (heads + ((if BankTrialProbabilityArmedGate z ∧
          e = root then 1 else 0) +
          bankTrialLiveHeadCount ring root tail
            (bankTrialLocalNext ring root z e)))
      simpa only [Nat.add_assoc] using htail

theorem bankTrialProbabilityLockedCarryCleanWords {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hw : BankTrialLiveWindowNonalias n q)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S) :
    ∀ word : List (Fin n),
      BankTrialLiveCarryLedger
        (bankTrialLocalRun ring root word
          (bankTrialLocalStart S))
        (bankTrialLiveHeadCount ring root word
          (bankTrialLocalStart S)) := by
  intro word
  have h := bankTrialProbabilityLockedCarryAllWords
    ring root hw word (bankTrialLocalStart S) 0
    (bankTrialLiveNoResetLockedStart S hclean)
    (bankTrialLiveCarryLedgerStart S hclean)
  simpa using h

end L3

/-!
Binary reconstruction of the compiled comparator. The theorem
uses the exact low-b bits, not a truncated numerical shortcut.
-/

namespace L3

open Classical

set_option autoImplicit false
set_option Elab.async false

/-- A finite binary expansion plus the omitted high quotient is
exactly its original natural number. -/
private theorem bankTrialProbabilityBinaryExpansion :
    ∀ b : Nat, ∀ m : Nat,
      (List.ofFn (fun i : Fin b =>
        if m / 2 ^ i.val % 2 == 1 then 2 ^ i.val else 0)).sum +
          (m / 2 ^ b) * 2 ^ b = m := by
  intro b
  induction b with
  | zero =>
      intro m
      simp
  | succ b ih =>
      intro m
      have hdiv (j : Nat) :
          m / 2 ^ (j + 1) = (m / 2) / 2 ^ j := by
        rw [Nat.div_div_eq_div_mul, Nat.pow_succ]
        ac_rfl
      have hpow (j : Nat) :
          2 ^ (j + 1) = 2 * 2 ^ j := by
        rw [Nat.pow_succ]
        omega
      have htail : ∀ i : Fin b,
          (if m / 2 ^ (i.val + 1) % 2 == 1
           then 2 ^ (i.val + 1) else 0) =
          2 * (if (m / 2) / 2 ^ i.val % 2 == 1
               then 2 ^ i.val else 0) := by
        intro i
        rw [hdiv i.val, hpow i.val]
        cases hbit : ((m / 2) / 2 ^ i.val % 2 == 1) <;>
          simp [hbit]
      have htailSum :
          (List.ofFn (fun i : Fin b =>
            if m / 2 ^ (i.val + 1) % 2 == 1
            then 2 ^ (i.val + 1) else 0)).sum =
          2 * (List.ofFn (fun i : Fin b =>
            if (m / 2) / 2 ^ i.val % 2 == 1
            then 2 ^ i.val else 0)).sum := by
        calc
          _ = (List.ofFn (fun i : Fin b =>
                2 * (if (m / 2) / 2 ^ i.val % 2 == 1
                     then 2 ^ i.val else 0))).sum := by
                  apply FiniteUniformStoppingTree.ofFn_sum_eq
                  exact htail
          _ = _ := FiniteUniformStoppingTree.ofFn_sum_mul_left 2 _
      have hsum :
          (List.ofFn (fun i : Fin (b + 1) =>
            if m / 2 ^ i.val % 2 == 1 then 2 ^ i.val else 0)).sum =
          (if m % 2 == 1 then 1 else 0) +
            2 * (List.ofFn (fun i : Fin b =>
              if (m / 2) / 2 ^ i.val % 2 == 1
              then 2 ^ i.val else 0)).sum := by
        rw [List.ofFn_succ, List.sum_cons]
        have hz : ((0 : Fin (b + 1)).val) = 0 := rfl
        simp only [hz, Nat.pow_zero, Nat.div_one]
        change (if m % 2 == 1 then 1 else 0) +
          (List.ofFn (fun i : Fin b =>
            if m / 2 ^ (i.val + 1) % 2 == 1
            then 2 ^ (i.val + 1) else 0)).sum = _
        rw [htailSum]
      have hhead : (if m % 2 == 1 then 1 else 0) = m % 2 := by
        have hlt : m % 2 < 2 :=
          Nat.mod_lt m (by omega)
        by_cases hz : m % 2 = 0
        · simp [hz]
        · have hone : m % 2 = 1 := by omega
          simp [hone]
      have hquot :
          m / 2 ^ (b + 1) = (m / 2) / 2 ^ b :=
        hdiv b
      have hmul :
          ((m / 2) / 2 ^ b) * (2 * 2 ^ b) =
            2 * (((m / 2) / 2 ^ b) * 2 ^ b) := by
        ac_rfl
      rw [hsum, hhead, hquot, hpow b, hmul,
        Nat.add_assoc, ← Nat.mul_add, ih (m / 2)]
      exact Nat.mod_add_div m 2

/-- The comparator's low b bits encode exactly K. This is used
only in the production range where K < 2^b is proved. -/
theorem bankTrialProbabilityThetaBinaryEqualsK (q : Nat)
    (h3 : 3 ≤ q) :
    bankTrialLiveThetaBinary q = (compileAdvice q).K := by
  have hbound : (compileAdvice q).K < 2 ^ (compileAdvice q).b := by
    have h := compileAdvice_K_lt_two_pow_b q h3
    omega
  have hquot :
      (compileAdvice q).K / 2 ^ (compileAdvice q).b = 0 :=
    Nat.div_eq_of_lt hbound
  have hbits := bankTrialProbabilityBinaryExpansion
    (compileAdvice q).b (compileAdvice q).K
  unfold bankTrialLiveThetaBinary
  change (List.ofFn (fun i : Fin (compileAdvice q).b =>
    if (compileAdvice q).K / 2 ^ i.val % 2 == 1
    then 2 ^ i.val else 0)).sum = (compileAdvice q).K
  rw [hquot] at hbits
  simpa using hbits

/-- The completed G11c win-mass upper estimate C.4, using a
bounded spatial window, the locked carry ledger, and the actual
root-acceptance trace on the original chronological edge word. -/
theorem bankTrialProbabilityUpperTarget {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b) :
    BankTrialProbabilityUpperTarget ring root S := by
  intro hsp hlarge hclean
  have hw : BankTrialLiveWindowNonalias n q :=
    bankTrialProbabilityUpperWindow hlarge
  have hn : 2 ≤ n := by
    unfold BankTrialLiveWindowNonalias at hw
    omega
  have hq : 3 ≤ q := by
    have hsmall : (compileAdvice q).useSmall =
        decide (q ≤ qStar) := rfl
    rw [hsmall] at hsp
    have hnot : ¬ q ≤ qStar := of_decide_eq_false hsp
    change ¬ q ≤ 79 at hnot
    omega
  have htheta : (compileAdvice q).K ≤ bankTrialLiveThetaBinary q := by
    rw [bankTrialProbabilityThetaBinaryEqualsK q hq]
    exact Nat.le_refl _
  have htrace := bankTrialProbabilityCleanWinGuardTrace
    ring root hn S hclean
  have hno := bankTrialProbabilityCleanWinNoArmedIncoming
    ring root hn S hclean
  have hledger : BankTrialLiveWinningLedger ring root S := by
    intro _ _ _ word hwin
    obtain ⟨pre, suffix, B, begun, hword, hpre, hm, ht⟩ :=
      htrace word hwin
    have hcredit := bankTrialProbabilityCleanWordsComparatorCredit
      ring root hw S hclean htheta pre
    rw [hpre] at hcredit
    have hcarry := bankTrialProbabilityLockedCarryCleanWords
      ring root hw S hclean pre
    rw [hpre] at hcarry
    have hk : (compileAdvice q).K ≤
        bankTrialLiveHeadCount ring root pre
          (bankTrialLocalStart S) := by
      exact Nat.le_trans (hcredit begun rfl hm ht)
        (hcarry begun rfl)
    have hmono :
        bankTrialLiveHeadCount ring root pre
          (bankTrialLocalStart S) ≤
        bankTrialLiveHeadCount ring root word
          (bankTrialLocalStart S) := by
      rw [hword, bankTrialLiveHeadCountAppend]
      omega
    exact ⟨Nat.le_trans hk hmono, hno word hwin⟩
  exact bankTrialProbabilityUpperOfWinningLedger
    ring root S hledger hsp hlarge hclean

end L3

/-!
A finite-word fair next-incident orientation on the
ORIGINAL Fin n IID scheduler, without changing its alphabet.

This theorem counts the first
physical root-incident letter, not the first successful worker
return. Its finite-horizon count equality is unconditional on
the unrelated letters and is valid at any authenticated ARMED
observer cut. The C.5 success lower target remains open.
-/

namespace L3

open Classical

set_option autoImplicit false
set_option Elab.async false

/-- The orientation of the first occurrence of either nominated
physical edge; none means neither port is seen in the word.
The first chosen edge is outgoing exactly for some true. -/
def bankTrialProbabilityFirstIncidentOrientation {n : Nat}
    (outgoing incoming : Fin n) :
    List (Fin n) → Option Bool
  | [] => none
  | e :: tail =>
      if e = outgoing then some true
      else if e = incoming then some false
      else bankTrialProbabilityFirstIncidentOrientation
        outgoing incoming tail

/-- Original-clock length-T mass of words whose first incident
edge has the selected orientation. Words with no incident
edge are counted on neither side. -/
noncomputable def bankTrialProbabilityFirstIncidentMass
    {n : Nat} (outgoing incoming : Fin n)
    (orientation : Bool) (T : Nat) : Nat :=
  Prob.scheduleSum n T (fun word =>
    if bankTrialProbabilityFirstIncidentOrientation
        outgoing incoming word = some orientation
    then 1 else 0)

/-- First-letter decomposition without altering the original
scheduler word. At an unrelated edge, recurse on the suffix.
An immediate occurrence of one port contributes exactly n^T
continuations. -/
private theorem bankTrialProbabilityFirstIncidentMassSucc
    {n : Nat} (outgoing incoming : Fin n)
    (orientation : Bool) (T : Nat) :
    bankTrialProbabilityFirstIncidentMass
        outgoing incoming orientation (T + 1) =
      (List.ofFn (fun e : Fin n =>
        if e = outgoing then
          (if orientation then n ^ T else 0)
        else if e = incoming then
          (if orientation then 0 else n ^ T)
        else bankTrialProbabilityFirstIncidentMass
          outgoing incoming orientation T)).sum := by
  unfold bankTrialProbabilityFirstIncidentMass
  rw [bankTrialProbabilityScheduleSumFirst]
  apply FiniteUniformStoppingTree.ofFn_sum_eq
  intro e
  by_cases ho : e = outgoing
  · cases orientation <;>
      simp [bankTrialProbabilityFirstIncidentOrientation,
        ho, bankTrialProbabilityScheduleSumConst]
  · by_cases hi : e = incoming
    · cases orientation <;>
        simp [bankTrialProbabilityFirstIncidentOrientation,
          ho, hi, bankTrialProbabilityScheduleSumConst] <;>
        (rw [← hi]; simp [ho])
    · simp only [bankTrialProbabilityFirstIncidentOrientation,
        if_neg ho, if_neg hi]

/-- Swapping the two exceptional summands in an otherwise
constant finite-port sum preserves the sum. This is an exact
Nat identity, not a ratio or measure-theoretic approximation. -/
private theorem bankTrialProbabilityTwoPortMassBalance
    {n : Nat} (outgoing incoming : Fin n)
    (hne : outgoing ≠ incoming) (hit rest : Nat) :
    (List.ofFn (fun e : Fin n =>
      if e = outgoing then hit
      else if e = incoming then 0 else rest)).sum =
    (List.ofFn (fun e : Fin n =>
      if e = outgoing then 0
      else if e = incoming then hit else rest)).sum := by
  have hhead := bankTrialProbabilitySumSwapSingle
    (fun e : Fin n =>
      if e = outgoing then hit
      else if e = incoming then 0 else rest)
    (fun e : Fin n =>
      if e = outgoing then 0
      else if e = incoming then 0 else rest)
    outgoing
    (by intro e he; simp [he])
  have htail := bankTrialProbabilitySumSwapSingle
    (fun e : Fin n =>
      if e = outgoing then 0
      else if e = incoming then 0 else rest)
    (fun e : Fin n =>
      if e = outgoing then 0
      else if e = incoming then hit else rest)
    incoming
    (by intro e he; by_cases ho : e = outgoing <;>
      simp [ho, he])
  have hne' : incoming ≠ outgoing := Ne.symm hne
  simp only [↓reduceIte, if_neg hne, if_neg hne'] at hhead htail
  omega

/-- Exact fair-bit law for the next physical service at either
of two distinct nominated edges. The horizon can be too short
to contain an incident edge; such words contribute to neither
side, so the equality holds without any limiting argument. -/
theorem bankTrialProbabilityFirstIncidentFair
    {n : Nat} (outgoing incoming : Fin n)
    (hne : outgoing ≠ incoming) (T : Nat) :
    bankTrialProbabilityFirstIncidentMass
      outgoing incoming true T =
    bankTrialProbabilityFirstIncidentMass
      outgoing incoming false T := by
  induction T with
  | zero =>
      simp [bankTrialProbabilityFirstIncidentMass,
        bankTrialProbabilityScheduleSumZero,
        bankTrialProbabilityFirstIncidentOrientation]
  | succ T ih =>
      rw [bankTrialProbabilityFirstIncidentMassSucc,
        bankTrialProbabilityFirstIncidentMassSucc]
      change
        (List.ofFn (fun e : Fin n =>
          if e = outgoing then n ^ T
          else if e = incoming then 0
          else bankTrialProbabilityFirstIncidentMass
            outgoing incoming true T)).sum =
        (List.ofFn (fun e : Fin n =>
          if e = outgoing then 0
          else if e = incoming then n ^ T
          else bankTrialProbabilityFirstIncidentMass
            outgoing incoming false T)).sum
      rw [ih]
      exact bankTrialProbabilityTwoPortMassBalance
        outgoing incoming hne (n ^ T)
        (bankTrialProbabilityFirstIncidentMass
          outgoing incoming false T)

/-- At a certified LIVE ARMED cut, the two incident ring-edge
names are the outgoing root and incoming predecessor.
The equality is about the NEXT incident edge label, not the
conditional probability of an eventual successful worker
history or a completed C.5 excursion. -/
theorem bankTrialProbabilityLockedArmedFirstIncidentFair
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (z : BankTrialLocalState q)
    (hlock : BankTrialLiveNoResetLocked z)
    (hgate : BankTrialProbabilityArmedGate z)
    (T : Nat) :
    bankTrialProbabilityFirstIncidentMass
      root (ring.leftNeighbor root) true T =
    bankTrialProbabilityFirstIncidentMass
      root (ring.leftNeighbor root) false T := by
  have hcap : 0 < (compileAdvice q).bankLeaseCap := by
    change 0 < 13 * ((compileAdvice q).b + 2)
    omega
  have hn : 2 ≤ n := by omega
  have hne := bankTrialProbabilityPortsDistinct
    ring hn root
  exact bankTrialProbabilityFirstIncidentFair
    root (ring.leftNeighbor root) hne T

/-- The strict C.1 union-margin arithmetic, specialized to the
large spatial branch. It is an arithmetic consequence of the
compiled width bound and does not assert an adapted origin
coupling or a successful observer excursion. -/
theorem bankTrialProbabilitySpatialWatchdogTiny (q : Nat)
    (hsp : (compileAdvice q).useSmall = false) :
    1024 * (2 ^ ((compileAdvice q).b + 1) + 1) *
        2 ^ (2 * (compileAdvice q).b + 2) *
        4 ^ (11 * (compileAdvice q).b + 24) <
      5 ^ (11 * (compileAdvice q).b + 24) := by
  exact bankTrialProbabilityWatchdogTiny
    (compileAdvice q).b
    (Counter.resetColdWatchdogSpatialWidth q hsp)

/-- Arithmetic portion of the at-most-(2K+1)-worker argument.
This does not prove that actual materialized worker histories
satisfy the corresponding cap. -/
theorem bankTrialProbabilityWorkerCapBelowPaper (q : Nat)
    (h3 : 3 ≤ q) :
    2 * (compileAdvice q).K + 1 <
      2 ^ ((compileAdvice q).b + 1) + 1 := by
  have hk := compileAdvice_K_lt_two_pow_b q h3
  have hp :
      2 ^ ((compileAdvice q).b + 1) =
        2 * 2 ^ (compileAdvice q).b := by
    rw [Nat.pow_succ]
    omega
  rw [hp]
  omega

end L3

/-!
Explicit designated-edge words for the C.5 deterministic
converse. These constructors count
all actual designated scheduler edges, including the extra visit
at the top CR-to-CL turn, and the returning root service.

This block establishes the word syntax and length bound, the
literal first-bit head/comparator launch rows, the real first
clean-head CSTART step, and the CWAIT/CL1 WON endpoint. It does
NOT claim that the whole chain is reachable from an arbitrary
clean seed at every intervening binary value: that needs
complete carried-bit/worker-position and comparison-progress
induction over all the listed selected edges.
-/

namespace L3

open Classical

set_option autoImplicit false
set_option Elab.async false

/-- Explicit outward services on protected digit edges
G_1, G_2, ..., G_t. G_0 is the physical root outgoing edge. -/
def bankTrialC5OutwardEdges {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (t : Nat) : List (Fin n) :=
  (List.range t).map (fun i => Counter.site ring root (i + 1))

/-- Explicit AL inward services G_t, ..., G_1.
An AL at digit t+1 must first return on G_t, so the return
list has t edges, not t-1. -/
def bankTrialC5InwardEdges {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (t : Nat) : List (Fin n) :=
  (bankTrialC5OutwardEdges ring root t).reverse

/-- If the binary word has t trailing 1 bits, this is the
designated increment cycle through CSTART:
- t = 0: outgoing head immediately writes the first 0 to 1;
- t > 0: outgoing head creates IR at digit 1, each G_i moves
  IR right until the first 0 flips, then AL returns along
  G_t,...,G_1, finally through the outgoing root edge G_0. -/
def bankTrialC5IncrementWord {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (t : Nat) : List (Fin n) :=
  if t = 0 then [root]
  else [root] ++ bankTrialC5OutwardEdges ring root t ++
    bankTrialC5InwardEdges ring root t ++ [root]

/-- The comparator starts with G_0, sends CR through
G_1,...,G_(b-1), turns CR to CL using G_(b-1) once more,
then returns CL on G_(b-2),...,G_1,G_0.

The extra top service is necessary: the first G_(b-1)
merely moves CR to digit b, and the second turns it. -/
def bankTrialC5ComparisonWord {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (b : Nat) : List (Fin n) :=
  [root] ++ bankTrialC5OutwardEdges ring root (b - 1) ++
    [Counter.site ring root (b - 1)] ++
    ((List.range (b - 1)).reverse.map
      (fun i => Counter.site ring root i))

/-- One fully designated HEAD-increment-comparison excursion.
The trailing-ones count must be the actual binary trailing run
for the current value; using an arbitrary count is *not*
claimed to yield a successful worker. -/
def bankTrialC5RoundWord {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (b t : Nat) : List (Fin n) :=
  bankTrialC5IncrementWord ring root t ++
    bankTrialC5ComparisonWord ring root b

/-- K rounds with per-value trailing-ones choices t(0),...,
t(K-1). The schedule is in chronological order. -/
def bankTrialC5Rounds {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (b : Nat) (trailing : Nat → Nat) :
    Nat → List (Fin n)
  | 0 => []
  | k + 1 =>
      bankTrialC5Rounds ring root b trailing k ++
        bankTrialC5RoundWord ring root b (trailing k)

theorem bankTrialC5OutwardLength {n : Nat}
    (ring : DirectedRing n) (root : Fin n) (t : Nat) :
    (bankTrialC5OutwardEdges ring root t).length = t := by
  simp [bankTrialC5OutwardEdges]

theorem bankTrialC5InwardLength {n : Nat}
    (ring : DirectedRing n) (root : Fin n) (t : Nat) :
    (bankTrialC5InwardEdges ring root t).length = t := by
  rw [bankTrialC5InwardEdges, List.length_reverse]
  exact bankTrialC5OutwardLength ring root t

/-- Exactly one head if t=0, otherwise a head, t outward
services, t AL-return edges, and the final root return. -/
theorem bankTrialC5IncrementLength {n : Nat}
    (ring : DirectedRing n) (root : Fin n) (t : Nat) :
    (bankTrialC5IncrementWord ring root t).length =
      if t = 0 then 1 else 2 * t + 2 := by
  by_cases ht : t = 0
  · subst t
    simp [bankTrialC5IncrementWord]
  · simp only [bankTrialC5IncrementWord, if_neg ht,
      List.length_append, List.length_cons,
      List.length_nil, bankTrialC5OutwardLength,
      bankTrialC5InwardLength]
    omega

/-- For b >= 1, comparison uses exactly 2b services. -/
theorem bankTrialC5ComparisonLength {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (b : Nat) (hb : 1 ≤ b) :
    (bankTrialC5ComparisonWord ring root b).length =
      2 * b := by
  simp [bankTrialC5ComparisonWord,
    bankTrialC5OutwardLength]
  omega

/-- At a carry value v with v+1 < 2^b, the actual trailing-one
run has length less than b. Under this side condition the
explicit designated round fits within the paper's generous
(2b+2)*2+1 slot budget. -/
theorem bankTrialC5RoundLengthBound {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (b t : Nat) (hb : 1 ≤ b) (ht : t < b) :
    (bankTrialC5RoundWord ring root b t).length ≤
      (2 * b + 2) * 2 + 1 := by
  rw [bankTrialC5RoundWord, List.length_append,
    bankTrialC5IncrementLength,
    bankTrialC5ComparisonLength ring root b hb]
  split <;> omega

/-- The full explicit K-round schedule meets precisely the
bound requested in C3, provided each actual trailing-one count
is less than the protected width. This is a pure word-length
theorem and asserts no terminal observer phase. -/
theorem bankTrialC5RoundsLengthBound {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (b K : Nat) (trailing : Nat → Nat)
    (hb : 1 ≤ b)
    (ht : ∀ i : Nat, i < K → trailing i < b) :
    (bankTrialC5Rounds ring root b trailing K).length ≤
      K * (2 * b + 2) * 2 + K := by
  have hmain :
      ∀ k : Nat,
      (∀ i : Nat, i < k → trailing i < b) →
      (bankTrialC5Rounds ring root b trailing k).length ≤
        k * ((2 * b + 2) * 2 + 1) := by
    intro k
    induction k with
    | zero =>
        intro _
        simp [bankTrialC5Rounds]
    | succ k ih =>
        intro hk
        have hshort : ∀ i : Nat, i < k →
            trailing i < b := by
          intro i hi
          exact hk i (by omega)
        have hprior := ih hshort
        have hlast := bankTrialC5RoundLengthBound
          ring root b (trailing k) hb (hk k (by omega))
        change (bankTrialC5Rounds ring root b trailing k ++
          bankTrialC5RoundWord ring root b (trailing k)).length ≤
            (k + 1) * ((2 * b + 2) * 2 + 1)
        rw [List.length_append]
        calc
          _ ≤ k * ((2 * b + 2) * 2 + 1) +
              ((2 * b + 2) * 2 + 1) :=
                Nat.add_le_add hprior hlast
          _ = (k + 1) * ((2 * b + 2) * 2 + 1) := by
            simp [Nat.succ_mul, Nat.add_comm]
  have hresult := hmain K ht
  exact Nat.le_trans hresult (Nat.le_of_eq (by
    rw [Nat.mul_add, Nat.mul_one, ← Nat.mul_assoc]))

/-- Literal outgoing head at an ARMED root and a zero first
digit: the first bit becomes 1, the root enters CSTART, and
no IR is created. This is the t=0 case of C1. -/
private theorem bankTrialC5RawHeadZero
    (b : Nat) (theta : Nat → Bool) (x y : BankCell)
    (hb : 1 ≤ b) (hx : x.role = 0) (hy : y.role = 1)
    (hg : x.grant = false) (hm : x.mode = .ARMED)
    (ht : y.tok = .E) (hbit : y.bit = false) :
    (bankPair x y 1 b theta).1.mode = .CSTART ∧
    (bankPair x y 1 b theta).2.bit = true ∧
    (bankPair x y 1 b theta).2.tok = .E := by
  simp [bankPair, hx, hy, hg, hm, ht, hbit,
    hb, isRetTok, isWaitMode, Id.run_pure, Id.run_bind]

/-- Literal outgoing head at an ARMED root and a one first
digit: the first bit becomes 0, IR is issued, and the root
waits in IWAIT with a fresh full lease. -/
private theorem bankTrialC5RawHeadOne
    (b : Nat) (theta : Nat → Bool) (x y : BankCell)
    (hb : 1 ≤ b) (hx : x.role = 0) (hy : y.role = 1)
    (hg : x.grant = false) (hm : x.mode = .ARMED)
    (ht : y.tok = .E) (hbit : y.bit = true) :
    (bankPair x y 1 b theta).1.mode = .IWAIT ∧
    (bankPair x y 1 b theta).2.bit = false ∧
    (bankPair x y 1 b theta).2.tok = .IR := by
  simp [bankPair, hx, hy, hg, hm, ht, hbit,
    hb, isRetTok, isWaitMode, Id.run_pure, Id.run_bind]

/-- CSTART launches the comparator's literal CR0 or CR1 at
digit 1. This is the source row of C2, before forwarding. -/
private theorem bankTrialC5RawComparisonLaunch
    (b : Nat) (theta : Nat → Bool) (x y : BankCell)
    (hb : 1 ≤ b) (hx : x.role = 0) (hy : y.role = 1)
    (hg : x.grant = false) (hm : x.mode = .CSTART)
    (ht : y.tok = .E) :
    (bankPair x y 1 b theta).1.mode = .CWAIT ∧
    (bankPair x y 1 b theta).2.tok =
      (if y.bit == theta 0 then .CR1 else .CR0) := by
  simp [bankPair, hx, hy, hg, hm, ht,
    hb, isRetTok, isWaitMode, Id.run_pure, Id.run_bind]

/-- A returning AL at the root, under the old IWAIT mode,
clears the first token and enters CSTART without writing
another digit. This is the endpoint after the inward AL word. -/
private theorem bankTrialC5RawALRootReturn
    (b : Nat) (theta : Nat → Bool) (x y : BankCell)
    (hb : 1 ≤ b) (hx : x.role = 0) (hy : y.role = 1)
    (hg : x.grant = false) (hm : x.mode = .IWAIT)
    (ht : y.tok = .AL) :
    (bankPair x y 1 b theta).1.mode = .CSTART ∧
    (bankPair x y 1 b theta).2.tok = .E := by
  simp [bankPair, hx, hy, hg, hm, ht,
    hb, isRetTok, isWaitMode, Id.run_pure, Id.run_bind]

/-- A failed equality comparison returns CL0. The root
consumes CL0 and rearms, leaving the protected digit bits
unchanged. When the nonzero carry is still below K, this
is the intended next HEAD gate. -/
private theorem bankTrialC5RawCLZeroRootReturn
    (b : Nat) (theta : Nat → Bool) (x y : BankCell)
    (hb : 1 ≤ b) (hx : x.role = 0) (hy : y.role = 1)
    (hg : x.grant = false) (hm : x.mode = .CWAIT)
    (ht : y.tok = .CL0) :
    (bankPair x y 1 b theta).1.mode = .ARMED ∧
    (bankPair x y 1 b theta).2.tok = .E ∧
    (bankPair x y 1 b theta).2.bit = y.bit := by
  simp [bankPair, hx, hy, hg, hm, ht,
    hb, isRetTok, isWaitMode, Id.run_pure, Id.run_bind]

/-- An actual CLEAN observer has the claimed t=0 first
increment, and therefore reaches LIVE CSTART after [root].
The general carry-propagation induction is not hidden in this
base case. -/
theorem bankTrialC5FirstCleanHeadCStart {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S) :
    (bankTrialLocalRun ring root
      (bankTrialC5IncrementWord ring root 0)
      (bankTrialLocalStart S)).phase = .live true := by
  change (bankTrialLocalNext ring root
    (bankTrialLocalStart S) root).phase = .live true
  rw [(bankTrialProbabilityCleanHeadCStart
    ring root S hclean).2.2]

/-- Once a genuine reachable LIVE CWAIT/CL1 root guard is
available, its *next* outgoing root service is WON. A longer
finite continuation cannot undo success. This is the exact
last local implication in C2/C3. -/
theorem bankTrialC5GuardedRootSuccess {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (pre suffix : List (Fin n))
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b) (begun : Bool)
    (hrun : bankTrialLocalRun ring root pre
      (bankTrialLocalStart S) = ⟨B, .live begun⟩)
    (hf : B.success = false)
    (hm : (B.fields ⟨0, by omega⟩).1 = .CWAIT)
    (ht : (B.fields
      ⟨1, by change 1 < (compileAdvice q).s + 11 + 1; omega⟩).2.2.1 =
        .CL1) :
    (bankTrialLocalRun ring root (pre ++ root :: suffix)
      (bankTrialLocalStart S)).phase = .won := by
  rw [bankTrialLocalRunAppend, hrun]
  have hwin := bankTrialProbabilityLiveReturnWon
    ring root B begun hf hm ht
  have hterminal : bankTrialLocalTerminal
      (bankTrialLocalNext ring root
        (⟨B, .live begun⟩ : BankTrialLocalState q) root) :=
    Or.inl hwin
  change (bankTrialLocalRun ring root suffix
    (bankTrialLocalNext ring root
      (⟨B, .live begun⟩ : BankTrialLocalState q) root)).phase = .won
  rw [bankTrialLocalRunTerminalAbsorbs ring root
    suffix (bankTrialLocalNext ring root
      (⟨B, .live begun⟩ : BankTrialLocalState q) root)
    hterminal]
  exact hwin

/-- Even the proposed deterministic concatenation remains
inside G11b's no-RESET locked LIVE envelope. This does not
assert that all individual workers complete or that WON occurs. -/
theorem bankTrialC5RoundsRemainLocked {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hclean : BankTrialLocalClean q S)
    (trailing : Nat → Nat) :
    BankTrialLiveNoResetLocked
      (bankTrialLocalRun ring root
        (bankTrialC5Rounds ring root
          (compileAdvice q).b trailing (compileAdvice q).K)
        (bankTrialLocalStart S)) := by
  exact bankTrialWindowLockedCleanWords
    ring root (bankTrialWindowFromLeaseCap hlarge) S hclean _

end L3

/-!
C1 carry-state induction -- counterexample to the *unlatched*
hypothesis-free formulation.

The previously requested claim from *any* LIVE, no-RESET locked
ARMED state at carry value v is false. BankTrialLiveNoResetLocked does
not require the reference success latch to be false, whereas
bankLocalReferenceStepClamped treats success=true as absorbing and
bankTrialLocalNext marks such a LIVE observer WON at its next service.

The witness below is intentionally Cartesian and is NOT asserted to
be reachable in LIVE from a CLEAN starting state. A correct C1
increment induction must assume B.success=false (or prove that
condition from a CLEAN-reachable LIVE history), and separately use
the nonalias condition. No increment theorem is asserted here.
-/

namespace L3

open Classical

set_option autoImplicit false
set_option Elab.async false

/-- A fully explicit clean-shaped ARMED bit array whose independent
success latch is already true. Unlike BankTrialLocalClean, its
success flag is intentionally nonzero. All b digit bits are zero
and all b digit worker tokens are E. -/
def bankTrialC5LatchedArmedZero (q : Nat) :
    GrantBankReference.BankLocalReference
      (compileAdvice q).b :=
  { fields := fun i =>
      (if i.val = 0 then Mode.ARMED else Mode.RESET,
        false, BTok.E, 0),
    success := true }

private theorem bankTrialC5LatchedArmedZeroRootMode
    (q : Nat) :
    bankTrialLiveWaveRootMode
      (bankTrialC5LatchedArmedZero q) = .ARMED := by
  rfl

theorem bankTrialC5LatchedArmedZeroNoWorker
    (q : Nat) :
    ∀ j : Fin (compileAdvice q).b,
      bankTrialLiveWaveToken
        (bankTrialC5LatchedArmedZero q) j = .E := by
  intro j
  rfl

private theorem bankTrialC5LatchedArmedZeroCertificate
    (q : Nat) :
    BankTrialLiveWaveCertificate q
      (bankTrialC5LatchedArmedZero q) := by
  have hempty := bankTrialC5LatchedArmedZeroNoWorker q
  have hmode := bankTrialC5LatchedArmedZeroRootMode q
  refine {
    cwaitTokens := ?_,
    iwaitTokens := ?_,
    headClear := ?_,
    resetTokens := ?_,
    uniqueWorker := ?_,
    comparisonMode := ?_,
    crPrefix := ?_,
    clAll := ?_
  }
  · intro j hm
    rw [hmode] at hm
    cases hm
  · intro j hm
    rw [hmode] at hm
    cases hm
  · intro j _
    exact hempty j
  · intro j hm
    rw [hmode] at hm
    cases hm
  · intro i j hi _
    rw [hempty i] at hi
    exact False.elim (hi rfl)
  · intro j ht
    rcases ht with hzero | hone
    · rw [hempty j] at hzero
      cases hzero
    · rw [hempty j] at hone
      cases hone
  · intro j ht
    rw [hempty j] at ht
    cases ht
  · intro j ht
    rw [hempty j] at ht
    cases ht

/-- The witness really satisfies the existing LIVE,
no-RESET, one-worker-at-most locked invariant. -/
theorem bankTrialC5LatchedArmedZeroLocked
    (q : Nat) :
    BankTrialLiveNoResetLocked
      (⟨bankTrialC5LatchedArmedZero q, .live false⟩ :
        BankTrialLocalState q) := by
  constructor
  · intro begun hlive
    exact bankTrialC5LatchedArmedZeroCertificate q
  · intro begun hlive
    rw [bankTrialC5LatchedArmedZeroRootMode q]
    intro hreset
    cases hreset

/-- The carry-aware value uses the exact same low-to-high
2^j window reading convention as bankTrialLiveThetaBinary.
With no IR tokens and all false digit bits its value is zero. -/
theorem bankTrialC5LatchedArmedZeroCarry
    (q : Nat) :
    bankTrialLiveCarryValue
      (bankTrialC5LatchedArmedZero q) = 0 := by
  unfold bankTrialLiveCarryValue
  have hzero :
      (List.ofFn (fun j : Fin (compileAdvice q).b =>
        bankTrialLiveSlotPotential j.val
          ((bankTrialC5LatchedArmedZero q).fields
            ⟨j.val + 1, by omega⟩).2.1
          ((bankTrialC5LatchedArmedZero q).fields
            ⟨j.val + 1, by omega⟩).2.2.1)).sum =
        (List.ofFn (fun _ : Fin (compileAdvice q).b =>
          (0 : Nat))).sum := by
    apply FiniteUniformStoppingTree.ofFn_sum_eq
    intro j
    simp [bankTrialLiveSlotPotential,
      bankTrialC5LatchedArmedZero]
  rw [hzero, FiniteUniformStoppingTree.ofFn_sum_const]
  exact Nat.mul_zero _

/-- The success latch is absorbing in the exact clamped
reference, even on an otherwise valid designated root edge. -/
private theorem bankTrialC5LatchedReferenceAbsorbs
    {n q : Nat} (ring : DirectedRing n) (root e : Fin n)
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hs : B.success = true) :
    GrantBankReference.bankLocalReferenceStepClamped
      ring root B e = B := by
  classical
  simp [GrantBankReference.bankLocalReferenceStepClamped, hs]

/-- The local observer tests success before the CLEAN and
root-RESET branches. Therefore LIVE plus a latched reference
goes immediately to WON, not to a new LIVE CSTART state. -/
theorem bankTrialC5LatchedLiveWon
    {n q : Nat} (ring : DirectedRing n) (root e : Fin n)
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b) (begun : Bool)
    (hs : B.success = true) :
    (bankTrialLocalNext ring root
      (⟨B, .live begun⟩ : BankTrialLocalState q) e).phase =
      .won := by
  have hframe :=
    bankTrialC5LatchedReferenceAbsorbs ring root e B hs
  simp [bankTrialLocalNext, hframe, hs]

/-- Exact C1 counterexample at the t=0 first service e=root.
The outgoing designated word is [root]; the locked ARMED
zero-carry state has its success latch set and becomes WON.
There is no root reset, timeout, worker collision, or carry.
This is an observer-latch counterexample, not a failure of
the bit-flip row from a genuine CLEAN-reachable unlatched cut. -/
theorem bankTrialC5LatchedZeroWordWon
    {n q : Nat} (ring : DirectedRing n) (root : Fin n) :
    (bankTrialLocalRun ring root
      (bankTrialC5IncrementWord ring root 0)
      (⟨bankTrialC5LatchedArmedZero q, .live false⟩ :
        BankTrialLocalState q)).phase = .won := by
  change (bankTrialLocalNext ring root
    (⟨bankTrialC5LatchedArmedZero q, .live false⟩ :
      BankTrialLocalState q) root).phase = .won
  exact bankTrialC5LatchedLiveWon ring root root
    (bankTrialC5LatchedArmedZero q) false rfl

/-- Hence the requested LIVE-CSTART endpoint is false for
this explicit state, even though it is locked and has carry v=0. -/
theorem bankTrialC5LatchedZeroWordNotLive
    {n q : Nat} (ring : DirectedRing n) (root : Fin n) :
    (bankTrialLocalRun ring root
      (bankTrialC5IncrementWord ring root 0)
      (⟨bankTrialC5LatchedArmedZero q, .live false⟩ :
        BankTrialLocalState q)).phase ≠ .live true := by
  rw [bankTrialC5LatchedZeroWordWon ring root]
  intro h
  cases h

end L3


/-! Unlatched ARMED C1. Full induction open. -/
namespace L3
open Classical
set_option autoImplicit false
set_option Elab.async false

def BankTrialC5ArmedStart (n q : Nat)
    (z : BankTrialLocalState q) : Prop :=
  BankTrialLiveWindowNonalias n q ∧
  BankTrialLiveNoResetLocked z ∧
  (∃ begun : Bool, z.phase = .live begun) ∧
  z.bank.success = false ∧
  bankTrialLiveWaveRootMode z.bank = .ARMED ∧
  (∀ j : Fin (compileAdvice q).b,
    bankTrialLiveWaveToken z.bank j = .E)

def BankTrialC5TrailingOnes {q : Nat}
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b) (t : Nat) : Prop :=
  t < (compileAdvice q).b ∧
  (∀ j : Fin (compileAdvice q).b,
    j.val < t → bankTrialLiveWaveBit B j = true) ∧
  (∀ j : Fin (compileAdvice q).b,
    j.val = t → bankTrialLiveWaveBit B j = false)

theorem bankTrialC5NoWorkerCarryBinary {q : Nat}
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hempty : ∀ j : Fin (compileAdvice q).b,
      bankTrialLiveWaveToken B j = .E) :
    bankTrialLiveCarryValue B = bankTrialLiveBinaryValue B := by
  unfold bankTrialLiveCarryValue bankTrialLiveBinaryValue
  apply FiniteUniformStoppingTree.ofFn_sum_eq
  intro j
  have ht := hempty j
  change (B.fields ⟨j.val + 1, by omega⟩).2.2.1 = .E at ht
  simp [bankTrialLiveSlotPotential, ht]

/-- For arbitrary locked starts, use the proved four-row
word theorem, not the CLEAN-only interface. -/
theorem bankTrialC5LockedArbitraryWord {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hw : BankTrialLiveWindowNonalias n q)
    (w : List (Fin n)) (z : BankTrialLocalState q)
    (hlock : BankTrialLiveNoResetLocked z) :
    BankTrialLiveNoResetLocked
      (bankTrialLocalRun ring root w z) := by
  exact bankTrialWindowLockedRunOfRows
    ring root hw
    (bankTrialWindowRowsOfClasses ring root
      (bankTrialWindowRootOutgoingRows ring root)
      (bankTrialWindowInteriorRowsOfPairRows ring root
        (bankTrialLiveInteriorPairRows q))
      (bankTrialWindowTopRows ring root)
      (bankTrialWindowIncomingRows ring root))
    w z hlock

/-- Remaining C1 statement: named Prop, NOT a theorem. -/
def BankTrialC5ArmedIncrementCorrect (n q : Nat)
    (ring : DirectedRing n) (root : Fin n) : Prop :=
  ∀ (z : BankTrialLocalState q) (t : Nat),
    BankTrialC5ArmedStart n q z →
    BankTrialC5TrailingOnes z.bank t →
    bankTrialLiveCarryValue z.bank + 1 < 2 ^ (compileAdvice q).b →
    ∃ begun : Bool,
      (bankTrialLocalRun ring root
        (bankTrialC5IncrementWord ring root t) z).phase =
          .live begun ∧
      bankTrialLiveWaveRootMode
        (bankTrialLocalRun ring root
          (bankTrialC5IncrementWord ring root t) z).bank =
          .CSTART ∧
      bankTrialLiveCarryValue
        (bankTrialLocalRun ring root
          (bankTrialC5IncrementWord ring root t) z).bank =
        bankTrialLiveCarryValue z.bank + 1 ∧
      (bankTrialLocalRun ring root
        (bankTrialC5IncrementWord ring root t) z).bank.success =
          false ∧
      BankTrialLiveNoResetLocked
        (bankTrialLocalRun ring root
          (bankTrialC5IncrementWord ring root t) z)

end L3

/-!
C1 on CLEAN-run prefixes.

This section proves selected IR/AL/empty-worker
reference rows and CLEAN-prefix locking. It does not assert the
as-yet-unproved complete increment induction.
-/

namespace L3

open Classical

set_option autoImplicit false
set_option Elab.async false

/-- The actual observer from one fixed CLEAN seed. -/
noncomputable def bankTrialC5CleanRun {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b) (w : List (Fin n)) :
    BankTrialLocalState q :=
  bankTrialLocalRun ring root w (bankTrialLocalStart S)

/-- No synthetic reset at the selected prefix. -/
theorem bankTrialC5CleanRunAppend {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (w suffix : List (Fin n)) :
    bankTrialC5CleanRun ring root S (w ++ suffix) =
      bankTrialLocalRun ring root suffix
        (bankTrialC5CleanRun ring root S w) := by
  unfold bankTrialC5CleanRun
  exact bankTrialLocalRunAppend ring root w suffix
    (bankTrialLocalStart S)

/-- The real CLEAN-origin lock holds at every extended prefix. -/
theorem bankTrialC5CleanPrefixLocked {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hw : BankTrialLiveWindowNonalias n q)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S)
    (w suffix : List (Fin n)) :
    BankTrialLiveNoResetLocked
      (bankTrialC5CleanRun ring root S (w ++ suffix)) := by
  exact bankTrialWindowLockedCleanWords
    ring root hw S hclean (w ++ suffix)

/-- Any LIVE CSTART endpoint of such a prefix has no worker. -/
theorem bankTrialC5CleanCStartTokensEmpty {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hw : BankTrialLiveWindowNonalias n q)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S)
    (w : List (Fin n)) (begun : Bool)
    (hlive : (bankTrialC5CleanRun ring root S w).phase =
      .live begun)
    (hmode : bankTrialLiveWaveRootMode
      (bankTrialC5CleanRun ring root S w).bank = .CSTART) :
    ∀ j : Fin (compileAdvice q).b,
      bankTrialLiveWaveToken
        (bankTrialC5CleanRun ring root S w).bank j = .E := by
  intro j
  have hlock := bankTrialWindowLockedCleanWords
    ring root hw S hclean w
  exact (hlock.1 begun hlive).headClear j (Or.inr hmode)

/-- Success cannot be set at an interior G_i, i>0. -/
theorem bankTrialC5NonrootSuccessFrame {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hf : B.success = false) (hne : e ≠ root) :
    (GrantBankReference.bankLocalReferenceStepClamped
      ring root B e).success = false := by
  classical
  unfold GrantBankReference.bankLocalReferenceStepClamped
  split
  · simp [hf, GrantBankReference.bankLocalReferenceSuccessEvent,
      hne]
  · exact hf

/-- Literal IR-forward, lifted from bankPair to the selected
clamped two-slot reference. The destination OLD bit decides
whether the unique worker remains IR or turns into AL. -/
theorem bankTrialC5SelectedIRForward {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hw : BankTrialLiveWindowNonalias n q)
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hf : B.success = false)
    (j : Fin (compileAdvice q).b) (hj : 0 < j.val)
    (hsrc : (B.fields ⟨j.val, by omega⟩).2.2.1 = .IR)
    (hdst : (B.fields ⟨j.val + 1, by omega⟩).2.2.1 = .E) :
    ((GrantBankReference.bankLocalReferenceStepClamped
      ring root B (Counter.site ring root j.val)).fields
        ⟨j.val, by omega⟩).2.2.1 = .E ∧
    ((GrantBankReference.bankLocalReferenceStepClamped
      ring root B (Counter.site ring root j.val)).fields
        ⟨j.val + 1, by omega⟩).2.2.1 =
        (if (B.fields ⟨j.val + 1, by omega⟩).2.1
         then .IR else .AL) ∧
    ((GrantBankReference.bankLocalReferenceStepClamped
      ring root B (Counter.site ring root j.val)).fields
        ⟨j.val + 1, by omega⟩).2.1 =
        !(B.fields ⟨j.val + 1, by omega⟩).2.1 := by
  have hrow := bankTrialInteriorIRForward
    (compileAdvice q).b (compileAdvice q).theta
    (GrantBankReference.bankLocalReferenceCell B
      ⟨j.val, by omega⟩)
    (GrantBankReference.bankLocalReferenceCell B
      ⟨j.val + 1, by omega⟩)
    (by change 1 ≤ j.val; omega)
    (by exact j.isLt) (by rfl)
    (by exact hsrc) (by exact hdst)
  constructor
  · rw [bankTrialWindowInteriorSource ring root B hf j]
    rw [(bankTrialLiveClampBitToken q
      ((GrantBankReference.bankLocalReferenceInternalPair q B j).1)).2]
    exact hrow.1
  constructor
  · rw [bankTrialWindowInteriorResponder ring root hw B hf j]
    rw [(bankTrialLiveClampBitToken q
      ((GrantBankReference.bankLocalReferenceInternalPair q B j).2)).2]
    exact hrow.2.1
  · rw [bankTrialWindowInteriorResponder ring root hw B hf j]
    rw [(bankTrialLiveClampBitToken q
      ((GrantBankReference.bankLocalReferenceInternalPair q B j).2)).1]
    exact hrow.2.2

/-- Literal reverse AL-return lifted to the same clamped
reference; both selected digit bits are unchanged. -/
theorem bankTrialC5SelectedALReturn {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hw : BankTrialLiveWindowNonalias n q)
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hf : B.success = false)
    (j : Fin (compileAdvice q).b) (hj : 0 < j.val)
    (hsrc : (B.fields ⟨j.val, by omega⟩).2.2.1 = .E)
    (hdst : (B.fields ⟨j.val + 1, by omega⟩).2.2.1 = .AL) :
    ((GrantBankReference.bankLocalReferenceStepClamped
      ring root B (Counter.site ring root j.val)).fields
        ⟨j.val, by omega⟩).2.2.1 = .AL ∧
    ((GrantBankReference.bankLocalReferenceStepClamped
      ring root B (Counter.site ring root j.val)).fields
        ⟨j.val + 1, by omega⟩).2.2.1 = .E ∧
    ((GrantBankReference.bankLocalReferenceStepClamped
      ring root B (Counter.site ring root j.val)).fields
        ⟨j.val, by omega⟩).2.1 =
        (B.fields ⟨j.val, by omega⟩).2.1 ∧
    ((GrantBankReference.bankLocalReferenceStepClamped
      ring root B (Counter.site ring root j.val)).fields
        ⟨j.val + 1, by omega⟩).2.1 =
        (B.fields ⟨j.val + 1, by omega⟩).2.1 := by
  have hrow := bankTrialInteriorALReturn
    (compileAdvice q).b (compileAdvice q).theta
    (GrantBankReference.bankLocalReferenceCell B
      ⟨j.val, by omega⟩)
    (GrantBankReference.bankLocalReferenceCell B
      ⟨j.val + 1, by omega⟩)
    (by change 1 ≤ j.val; omega)
    (by exact j.isLt) (by rfl)
    (by exact hsrc) (by exact hdst)
  constructor
  · rw [bankTrialWindowInteriorSource ring root B hf j]
    rw [(bankTrialLiveClampBitToken q
      ((GrantBankReference.bankLocalReferenceInternalPair q B j).1)).2]
    exact hrow.1
  constructor
  · rw [bankTrialWindowInteriorResponder ring root hw B hf j]
    rw [(bankTrialLiveClampBitToken q
      ((GrantBankReference.bankLocalReferenceInternalPair q B j).2)).2]
    exact hrow.2.2.1
  constructor
  · rw [bankTrialWindowInteriorSource ring root B hf j]
    rw [(bankTrialLiveClampBitToken q
      ((GrantBankReference.bankLocalReferenceInternalPair q B j).1)).1]
    exact hrow.2.1
  · rw [bankTrialWindowInteriorResponder ring root hw B hf j]
    rw [(bankTrialLiveClampBitToken q
      ((GrantBankReference.bankLocalReferenceInternalPair q B j).2)).1]
    exact hrow.2.2.2

/-- Correct replacement for a false full-record E/E frame:
only digit bits and token coordinates are preserved. -/
theorem bankTrialC5SelectedEmptyBitToken {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hw : BankTrialLiveWindowNonalias n q)
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hf : B.success = false)
    (j : Fin (compileAdvice q).b) (hj : 0 < j.val)
    (hsrc : (B.fields ⟨j.val, by omega⟩).2.2.1 = .E)
    (hdst : (B.fields ⟨j.val + 1, by omega⟩).2.2.1 = .E) :
    ((GrantBankReference.bankLocalReferenceStepClamped
      ring root B (Counter.site ring root j.val)).fields
        ⟨j.val, by omega⟩).2.1 =
        (B.fields ⟨j.val, by omega⟩).2.1 ∧
    ((GrantBankReference.bankLocalReferenceStepClamped
      ring root B (Counter.site ring root j.val)).fields
        ⟨j.val + 1, by omega⟩).2.1 =
        (B.fields ⟨j.val + 1, by omega⟩).2.1 ∧
    ((GrantBankReference.bankLocalReferenceStepClamped
      ring root B (Counter.site ring root j.val)).fields
        ⟨j.val, by omega⟩).2.2.1 = .E ∧
    ((GrantBankReference.bankLocalReferenceStepClamped
      ring root B (Counter.site ring root j.val)).fields
        ⟨j.val + 1, by omega⟩).2.2.1 = .E := by
  have hrow := bankTrialInteriorRawEmptyPair
    (compileAdvice q).b (compileAdvice q).theta
    (GrantBankReference.bankLocalReferenceCell B
      ⟨j.val, by omega⟩)
    (GrantBankReference.bankLocalReferenceCell B
      ⟨j.val + 1, by omega⟩)
    (by change 1 ≤ j.val; omega)
    (by exact j.isLt) (by rfl)
    (by exact hsrc) (by exact hdst)
  constructor
  · rw [bankTrialWindowInteriorSource ring root B hf j]
    rw [(bankTrialLiveClampBitToken q
      ((GrantBankReference.bankLocalReferenceInternalPair q B j).1)).1]
    exact hrow.2.2.1
  constructor
  · rw [bankTrialWindowInteriorResponder ring root hw B hf j]
    rw [(bankTrialLiveClampBitToken q
      ((GrantBankReference.bankLocalReferenceInternalPair q B j).2)).1]
    exact hrow.2.2.2
  constructor
  · rw [bankTrialWindowInteriorSource ring root B hf j]
    rw [(bankTrialLiveClampBitToken q
      ((GrantBankReference.bankLocalReferenceInternalPair q B j).1)).2]
    exact hrow.1
  · rw [bankTrialWindowInteriorResponder ring root hw B hf j]
    rw [(bankTrialLiveClampBitToken q
      ((GrantBankReference.bankLocalReferenceInternalPair q B j).2)).2]
    exact hrow.2.1

end L3

/-!
Corrected C1 outward IR induction on CLEAN-origin prefixes.

The terminal outward edge G_t is the first-zero crossing and creates
AL; the IR-stage induction is asserted only for i < t. This section
establishes the clamped one-edge stage transition and its conditional
induction from an authenticated post-head stage. The independent
post-head base, complete AL return and carry-sum completion remain
open: no full C1 theorem is claimed.
-/

namespace L3

open Classical

set_option autoImplicit false
set_option Elab.async false

/-- Wave index i refers to physical digit i+1; the designated
IR is at that digit after i outward edges following the head.
Thus digits 1,...,i+1 are cleared. -/
def BankTrialC5OutwardIRStage {q : Nat}
    (origin : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (i : Nat) (z : BankTrialLocalState q) : Prop :=
  (∃ begun : Bool, z.phase = .live begun) ∧
  z.bank.success = false ∧
  bankTrialLiveWaveRootMode z.bank = .IWAIT ∧
  i < (compileAdvice q).b ∧
  (∀ k : Fin (compileAdvice q).b,
    bankTrialLiveWaveToken z.bank k =
      if k.val = i then .IR else .E) ∧
  (∀ k : Fin (compileAdvice q).b,
    bankTrialLiveWaveBit z.bank k =
      if k.val ≤ i then false
      else bankTrialLiveWaveBit origin k)

/-- Literal P_i from the question, using the existing CLEAN run. -/
noncomputable def bankTrialC5OutwardPrefixRun {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (w : List (Fin n)) (t i : Nat) :
    BankTrialLocalState q :=
  bankTrialC5CleanRun ring root S
    (w ++ root ::
      (bankTrialC5OutwardEdges ring root t).take i)

/-- The (i+1)-st outward edge is precisely G_(i+1). -/
theorem bankTrialC5OutwardTakeSucc {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (t i : Nat) (hi : i < t) :
    (bankTrialC5OutwardEdges ring root t).take (i + 1) =
      (bankTrialC5OutwardEdges ring root t).take i ++
        [Counter.site ring root (i + 1)] := by
  rw [List.take_succ_eq_append_getElem (by
    rw [bankTrialC5OutwardLength]
    exact hi)]
  congr 1
  simp [bankTrialC5OutwardEdges]

/-- Exact chronological P_i recurrence on the real observer. -/
theorem bankTrialC5OutwardPrefixNext {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (w : List (Fin n))
    (t i : Nat) (hi : i < t) :
    bankTrialC5OutwardPrefixRun ring root S w t (i + 1) =
      bankTrialLocalNext ring root
        (bankTrialC5OutwardPrefixRun ring root S w t i)
        (Counter.site ring root (i + 1)) := by
  unfold bankTrialC5OutwardPrefixRun
  rw [bankTrialC5OutwardTakeSucc ring root t i hi]
  have hword :
      w ++ root ::
        ((bankTrialC5OutwardEdges ring root t).take i ++
          [Counter.site ring root (i + 1)]) =
      (w ++ root ::
        (bankTrialC5OutwardEdges ring root t).take i) ++
          [Counter.site ring root (i + 1)] := by
    simp [List.append_assoc]
  rw [hword, bankTrialC5CleanRunAppend]
  rfl

/-- Nonselected protected digit bits are genuine frames, even
when unrelated nonroot modes and leases are normalized. -/
theorem bankTrialC5InteriorOtherBitFrame {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hw : BankTrialLiveWindowNonalias n q)
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hf : B.success = false)
    (j : Fin (compileAdvice q).b) (hj : 0 < j.val)
    (k : Fin (compileAdvice q).b)
    (hsource : k.val + 1 ≠ j.val)
    (htarget : k.val + 1 ≠ j.val + 1) :
    bankTrialLiveWaveBit
      (GrantBankReference.bankLocalReferenceStepClamped
        ring root B (Counter.site ring root j.val)) k =
      bankTrialLiveWaveBit B k := by
  change
    ((GrantBankReference.bankLocalReferenceStepClamped
      ring root B (Counter.site ring root j.val)).fields
      ⟨k.val + 1, by omega⟩).2.1 =
    (B.fields ⟨k.val + 1, by omega⟩).2.1
  exact congrArg
    (fun x : Mode × Bool × BTok × Nat => x.2.1)
    (bankTrialWindowInteriorFrame ring root hw B hf j hj
      ⟨k.val + 1, by omega⟩ hsource htarget)

/-- The IR/E row leaves the source bit unchanged. -/
private theorem bankTrialC5RawIRSourceBit
    (b : Nat) (theta : Nat → Bool) (x y : BankCell)
    (hx : 1 ≤ x.role) (hlt : x.role < b)
    (hy : y.role = x.role + 1)
    (hxt : x.tok = .IR) (hyt : y.tok = .E) :
    (bankPair x y y.role b theta).1.bit = x.bit := by
  obtain ⟨hxn, hxTop, hyn, hyPos, hyLe, hxLe⟩ :=
    bankTrialInteriorRoles b x y hx hlt hy
  simp [bankPair, hx, hlt, hy, hxn, hxTop,
    hyn, hyPos, hyLe, hxLe, hxt, hyt,
    Id.run_pure, Id.run_bind]

/-- Lift the source-bit frame to the exact selected clamped edge. -/
theorem bankTrialC5SelectedIRSourceBit {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hf : B.success = false)
    (j : Fin (compileAdvice q).b) (hj : 0 < j.val)
    (hsrc : (B.fields ⟨j.val, by omega⟩).2.2.1 = .IR)
    (hdst : (B.fields ⟨j.val + 1, by omega⟩).2.2.1 = .E) :
    ((GrantBankReference.bankLocalReferenceStepClamped
      ring root B (Counter.site ring root j.val)).fields
        ⟨j.val, by omega⟩).2.1 =
      (B.fields ⟨j.val, by omega⟩).2.1 := by
  have hrow := bankTrialC5RawIRSourceBit
    (compileAdvice q).b (compileAdvice q).theta
    (GrantBankReference.bankLocalReferenceCell B
      ⟨j.val, by omega⟩)
    (GrantBankReference.bankLocalReferenceCell B
      ⟨j.val + 1, by omega⟩)
    (by change 1 ≤ j.val; omega) j.isLt rfl hsrc hdst
  rw [bankTrialWindowInteriorSource ring root B hf j]
  rw [(bankTrialLiveClampBitToken q
    ((GrantBankReference.bankLocalReferenceInternalPair
      q B j).1)).1]
  exact hrow

/-- Interior G_j preserves LIVE IWAIT when the old success
latch is false and the protected window is nonaliased. -/
theorem bankTrialC5InteriorIWaitLive {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hw : BankTrialLiveWindowNonalias n q)
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (begun : Bool) (hf : B.success = false)
    (j : Fin (compileAdvice q).b) (hj : 0 < j.val)
    (hm : bankTrialLiveWaveRootMode B = .IWAIT) :
    ∃ nextBegun : Bool,
      (bankTrialLocalNext ring root
        (⟨B, .live begun⟩ : BankTrialLocalState q)
        (Counter.site ring root j.val)).phase =
          .live nextBegun := by
  have hnonroot := bankTrialWindowInteriorNotRoot
    ring root hw j hj
  have hs := bankTrialC5NonrootSuccessFrame ring root
    (Counter.site ring root j.val) B hf hnonroot
  have hmode :
      ((GrantBankReference.bankLocalReferenceStepClamped
        ring root B (Counter.site ring root j.val)).fields
        ⟨0, by omega⟩).1 = .IWAIT := by
    change bankTrialLiveWaveRootMode
      (GrantBankReference.bankLocalReferenceStepClamped
        ring root B (Counter.site ring root j.val)) = .IWAIT
    rw [bankTrialWindowInteriorRootModeFrame
      ring root hw B hf j hj]
    exact hm
  have hnoclean :
      ¬ BankTrialLocalClean q
        (GrantBankReference.bankLocalReferenceStepClamped
          ring root B (Counter.site ring root j.val)) := by
    intro hc
    have ha := hc.2.1
    rw [hmode] at ha
    cases ha
  have hnreset :
      ((GrantBankReference.bankLocalReferenceStepClamped
        ring root B (Counter.site ring root j.val)).fields
        ⟨0, by omega⟩).1 ≠ .RESET := by
    rw [hmode]
    intro h
    cases h
  have hzero : (0 : Fin ((compileAdvice q).b + 1)) =
      ⟨0, by omega⟩ := Fin.ext rfl
  have hnresetZero :
      ((GrantBankReference.bankLocalReferenceStepClamped
        ring root B (Counter.site ring root j.val)).fields
        (0 : Fin ((compileAdvice q).b + 1))).1 ≠ .RESET := by
    rw [hzero]
    exact hnreset
  refine ⟨begun || decide
    (Counter.site ring root j.val = root ∨
      ring.rightNeighbor (Counter.site ring root j.val) = root),
    ?_⟩
  simp [bankTrialLocalNext, hs, hnoclean, hnresetZero]

/-- One complete state-level IR hop across an OLD one bit.
The successor lock certifies uniqueness; the frame and source
bit row transport all digit-bit equalities. -/
theorem bankTrialC5OutwardIROneStep {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hw : BankTrialLiveWindowNonalias n q)
    (origin B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (begun : Bool) (i : Nat)
    (hi : i + 1 < (compileAdvice q).b)
    (hstage : BankTrialC5OutwardIRStage origin i
      (⟨B, .live begun⟩ : BankTrialLocalState q))
    (hnextBit : bankTrialLiveWaveBit B
      ⟨i + 1, hi⟩ = true)
    (hnextLock : BankTrialLiveNoResetLocked
      (bankTrialLocalNext ring root
        (⟨B, .live begun⟩ : BankTrialLocalState q)
        (Counter.site ring root (i + 1)))) :
    BankTrialC5OutwardIRStage origin (i + 1)
      (bankTrialLocalNext ring root
        (⟨B, .live begun⟩ : BankTrialLocalState q)
        (Counter.site ring root (i + 1))) := by
  rcases hstage with ⟨_, hf, hm, _, htoks, hbits⟩
  have hsrc :
      (B.fields ⟨i + 1, by omega⟩).2.2.1 = .IR := by
    change bankTrialLiveWaveToken B ⟨i, by omega⟩ = .IR
    simpa using htoks ⟨i, by omega⟩
  have hdst :
      (B.fields ⟨i + 1 + 1, by omega⟩).2.2.1 = .E := by
    change bankTrialLiveWaveToken B ⟨i + 1, hi⟩ = .E
    have hne : i + 1 ≠ i := by omega
    simpa [hne] using htoks ⟨i + 1, hi⟩
  have hpos : 0 <
      (⟨i + 1, hi⟩ : Fin (compileAdvice q).b).val := by
    change 0 < i + 1
    omega
  have hnextBitRaw :
      (B.fields ⟨i + 1 + 1, by omega⟩).2.1 = true := hnextBit
  have hrow := bankTrialC5SelectedIRForward
    ring root hw B hf ⟨i + 1, hi⟩
    hpos hsrc hdst
  have hsourceBit := bankTrialC5SelectedIRSourceBit
    ring root B hf ⟨i + 1, hi⟩ hpos hsrc hdst
  have hs := bankTrialC5NonrootSuccessFrame ring root
    (Counter.site ring root (i + 1)) B hf
    (bankTrialWindowInteriorNotRoot ring root hw
      ⟨i + 1, hi⟩ hpos)
  have hmnext : bankTrialLiveWaveRootMode
      (GrantBankReference.bankLocalReferenceStepClamped
        ring root B (Counter.site ring root (i + 1))) =
        .IWAIT := by
    rw [bankTrialWindowInteriorRootModeFrame
      ring root hw B hf ⟨i + 1, hi⟩ hpos]
    exact hm
  obtain ⟨nextBegun, hphase⟩ :=
    bankTrialC5InteriorIWaitLive ring root hw B begun hf
      ⟨i + 1, hi⟩ hpos hm
  have hbank := bankTrialLocalNextLiveBank ring root
    (Counter.site ring root (i + 1)) B begun
  have htoken : bankTrialLiveWaveToken
      (GrantBankReference.bankLocalReferenceStepClamped
        ring root B (Counter.site ring root (i + 1)))
        ⟨i + 1, hi⟩ = .IR := by
    change
      ((GrantBankReference.bankLocalReferenceStepClamped
        ring root B (Counter.site ring root (i + 1))).fields
        ⟨i + 1 + 1, by omega⟩).2.2.1 = .IR
    rw [hrow.2.1, hnextBitRaw]
    rfl
  have hcert :
      BankTrialLiveWaveCertificate q
        (bankTrialLocalNext ring root
          (⟨B, .live begun⟩ : BankTrialLocalState q)
          (Counter.site ring root (i + 1))).bank :=
    hnextLock.1 nextBegun hphase
  refine ⟨⟨nextBegun, hphase⟩, ?_, ?_, hi, ?_, ?_⟩
  · rw [hbank]
    exact hs
  · rw [hbank]
    exact hmnext
  · intro k
    rw [hbank]
    by_cases hk : k.val = i + 1
    · have hkeq : k = ⟨i + 1, hi⟩ := Fin.ext hk
      rw [hkeq, if_pos rfl]
      exact htoken
    · rw [if_neg hk]
      have hnotE : bankTrialLiveWaveToken
          (GrantBankReference.bankLocalReferenceStepClamped
            ring root B (Counter.site ring root (i + 1)))
            ⟨i + 1, hi⟩ ≠ .E := by
        rw [htoken]
        intro h
        cases h
      have hotherIndex : k ≠ ⟨i + 1, hi⟩ := by
        intro he
        have hv := congrArg Fin.val he
        exact hk hv
      have hother := bankTrialInteriorOldWorkerOthersEmpty
        (bankTrialLocalNext ring root
          (⟨B, .live begun⟩ : BankTrialLocalState q)
          (Counter.site ring root (i + 1))).bank
        hcert ⟨i + 1, hi⟩ k
        (by rw [hbank]; exact hnotE) hotherIndex
      rw [hbank] at hother
      exact hother
  · intro k
    rw [hbank]
    by_cases ht : k.val = i + 1
    · have hkeq : k = ⟨i + 1, hi⟩ := Fin.ext ht
      rw [hkeq]
      have hnewbit : bankTrialLiveWaveBit
          (GrantBankReference.bankLocalReferenceStepClamped
            ring root B (Counter.site ring root (i + 1)))
            ⟨i + 1, hi⟩ = false := by
        change
          ((GrantBankReference.bankLocalReferenceStepClamped
            ring root B (Counter.site ring root (i + 1))).fields
            ⟨i + 1 + 1, by omega⟩).2.1 = false
        rw [hrow.2.2, hnextBitRaw]
        rfl
      simpa using hnewbit
    · by_cases hx : k.val = i
      · have hkeq : k = ⟨i, by omega⟩ := Fin.ext hx
        rw [hkeq]
        have hsrcbit : bankTrialLiveWaveBit
            (GrantBankReference.bankLocalReferenceStepClamped
              ring root B (Counter.site ring root (i + 1)))
              ⟨i, by omega⟩ = false := by
          change
            ((GrantBankReference.bankLocalReferenceStepClamped
              ring root B (Counter.site ring root (i + 1))).fields
              ⟨i + 1, by omega⟩).2.1 = false
          rw [hsourceBit]
          have hold := hbits ⟨i, by omega⟩
          have hle : (⟨i, by omega⟩ :
              Fin (compileAdvice q).b).val ≤ i := by
            change i ≤ i
            exact Nat.le_refl i
          rw [if_pos hle] at hold
          change (B.fields ⟨i + 1, by omega⟩).2.1 = false at hold
          exact hold
        simpa using hsrcbit
      · have hnoSource : k.val + 1 ≠
            (⟨i + 1, hi⟩ : Fin (compileAdvice q).b).val := by
          change k.val + 1 ≠ i + 1
          omega
        have hnoTarget : k.val + 1 ≠
            (⟨i + 1, hi⟩ : Fin (compileAdvice q).b).val + 1 := by
          change k.val + 1 ≠ i + 1 + 1
          omega
        have hframe := bankTrialC5InteriorOtherBitFrame
          ring root hw B hf ⟨i + 1, hi⟩ hpos k
          hnoSource hnoTarget
        rw [hframe, hbits k]
        by_cases hle : k.val ≤ i + 1
        · have hleold : k.val ≤ i := by omega
          simp [hle, hleold]
        · have hnotold : ¬ k.val ≤ i := by omega
          simp [hle, hnotold]

/-- The same one-edge lemma, accepting an arbitrary LIVE state
rather than demanding a synthetic constructor at the call site. -/
theorem bankTrialC5OutwardIROneStepState {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hw : BankTrialLiveWindowNonalias n q)
    (origin : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (i : Nat) (hi : i + 1 < (compileAdvice q).b)
    (z : BankTrialLocalState q)
    (hstage : BankTrialC5OutwardIRStage origin i z)
    (hnextBit : bankTrialLiveWaveBit z.bank
      ⟨i + 1, hi⟩ = true)
    (hnextLock : BankTrialLiveNoResetLocked
      (bankTrialLocalNext ring root z
        (Counter.site ring root (i + 1)))) :
    BankTrialC5OutwardIRStage origin (i + 1)
      (bankTrialLocalNext ring root z
        (Counter.site ring root (i + 1))) := by
  obtain ⟨begun, hphase⟩ := hstage.1
  cases z with
  | mk B phase =>
      change phase = .live begun at hphase
      cases hphase
      exact bankTrialC5OutwardIROneStep ring root hw origin B
        begun i hi hstage hnextBit hnextLock

/-- The actual IR-position induction along P_i, conditional
only on the independent ARMED root-head base. The lock at
each new state is derived from the true CLEAN seed. -/
theorem bankTrialC5CleanOutwardIRFromHead {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S)
    (w : List (Fin n)) (t : Nat)
    (htrail : BankTrialC5TrailingOnes
      (bankTrialC5CleanRun ring root S w).bank t)
    (hstart : BankTrialC5ArmedStart n q
      (bankTrialC5CleanRun ring root S w))
    (hhead : BankTrialC5OutwardIRStage
      (bankTrialC5CleanRun ring root S w).bank 0
      (bankTrialC5OutwardPrefixRun ring root S w t 0)) :
    ∀ i : Nat, i < t →
      BankTrialC5OutwardIRStage
        (bankTrialC5CleanRun ring root S w).bank i
        (bankTrialC5OutwardPrefixRun ring root S w t i) := by
  intro i
  induction i with
  | zero =>
      intro _
      exact hhead
  | succ i ih =>
      intro hit
      have hprev : i < t := by omega
      have hstage := ih hprev
      have hi : i + 1 < (compileAdvice q).b := by
        have hb := htrail.1
        omega
      have hnextBit : bankTrialLiveWaveBit
          (bankTrialC5OutwardPrefixRun ring root S w t i).bank
          ⟨i + 1, hi⟩ = true := by
        rw [hstage.2.2.2.2.2 ⟨i + 1, hi⟩]
        have hnot : ¬ i + 1 ≤ i := by omega
        rw [if_neg hnot]
        exact htrail.2.1 ⟨i + 1, hi⟩ hit
      have hw := hstart.1
      have hlock : BankTrialLiveNoResetLocked
          (bankTrialC5OutwardPrefixRun ring root S w t
            (i + 1)) := by
        exact bankTrialC5CleanPrefixLocked ring root hw
          S hclean w
          (root :: (bankTrialC5OutwardEdges ring root t).take
            (i + 1))
      rw [bankTrialC5OutwardPrefixNext ring root S w t i hprev]
        at hlock ⊢
      exact bankTrialC5OutwardIROneStepState
        ring root hw (bankTrialC5CleanRun ring root S w).bank
        i hi (bankTrialC5OutwardPrefixRun ring root S w t i)
        hstage hnextBit hlock

/-- The last G_t of the outward list crosses the first zero;
its selected destination becomes AL with bit true. -/
theorem bankTrialC5OutwardFirstZeroAL {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hw : BankTrialLiveWindowNonalias n q)
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hf : B.success = false)
    (t : Nat) (ht : 1 ≤ t ∧ t < (compileAdvice q).b)
    (hsrc : (B.fields ⟨t, by omega⟩).2.2.1 = .IR)
    (hdst : (B.fields ⟨t + 1, by omega⟩).2.2.1 = .E)
    (hzero : (B.fields ⟨t + 1, by omega⟩).2.1 = false) :
    ((GrantBankReference.bankLocalReferenceStepClamped
      ring root B (Counter.site ring root t)).fields
      ⟨t + 1, by omega⟩).2.2.1 = .AL ∧
    ((GrantBankReference.bankLocalReferenceStepClamped
      ring root B (Counter.site ring root t)).fields
      ⟨t + 1, by omega⟩).2.1 = true := by
  have hpos : 0 <
      (⟨t, ht.2⟩ : Fin (compileAdvice q).b).val := by
    change 0 < t
    exact ht.1
  have hrow := bankTrialC5SelectedIRForward
    ring root hw B hf ⟨t, ht.2⟩ hpos hsrc hdst
  constructor
  · simpa [hzero] using hrow.2.1
  · simpa [hzero] using hrow.2.2

end L3

/-!
C1 from a CLEAN-reachable, unlatched ARMED gate.
The designated root HEAD-to-IR base closes the earlier hhead
premise of bankTrialC5CleanOutwardIRFromHead.
-/
namespace L3
open Classical
set_option autoImplicit false
set_option Elab.async false

/-- An outgoing ARMED head with first bit one enters LIVE IWAIT. -/
private theorem bankTrialC5ArmedOneHeadLive {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (begun : Bool)
    (hf : B.success = false)
    (hold : bankTrialLiveWaveRootMode B = .ARMED)
    (hnew : bankTrialLiveWaveRootMode
      (GrantBankReference.bankLocalReferenceStepClamped
        ring root B root) = .IWAIT) :
    (bankTrialLocalNext ring root
      (⟨B, .live begun⟩ : BankTrialLocalState q) root).phase =
      .live true := by
  have hnotCWait :
      (B.fields ⟨0, by omega⟩).1 ≠ .CWAIT := by
    change bankTrialLiveWaveRootMode B ≠ .CWAIT
    rw [hold]
    intro h
    cases h
  have hs := bankTrialLocalUnlatchedNonCWaitNoWin
    ring root root B hf hnotCWait
  have hnotClean :
      ¬ BankTrialLocalClean q
        (GrantBankReference.bankLocalReferenceStepClamped
          ring root B root) := by
    intro hc
    have hmode := hc.2.1
    change bankTrialLiveWaveRootMode
      (GrantBankReference.bankLocalReferenceStepClamped
        ring root B root) = .ARMED at hmode
    rw [hnew] at hmode
    cases hmode
  have hmodeZero :
      ((GrantBankReference.bankLocalReferenceStepClamped
        ring root B root).fields
        (0 : Fin ((compileAdvice q).b + 1))).1 = .IWAIT := hnew
  simp [bankTrialLocalNext, hs, hnotClean, hmodeZero]

/-- The full post-head base: the sole IR sits at digit one,
its bit is zero, and every higher digit is unchanged. -/
theorem bankTrialC5ArmedHeadOneStage {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (z : BankTrialLocalState q)
    (hstart : BankTrialC5ArmedStart n q z)
    (hbit : bankTrialLiveWaveBit z.bank
      ⟨0, by have := bankTrialWindowWidthPos q; omega⟩ = true) :
    BankTrialC5OutwardIRStage z.bank 0
      (bankTrialLocalNext ring root z root) := by
  obtain ⟨hw, _, ⟨begun, hlive⟩, hf, hm, htok⟩ := hstart
  cases z with
  | mk B phase =>
      change phase = .live begun at hlive
      cases hlive
      have hb : 1 ≤ (compileAdvice q).b :=
        bankTrialWindowWidthPos q
      have hfirstToken :
          (bankTrialWindowFirstCell B).tok = .E := by
        change bankTrialLiveWaveToken B ⟨0, by omega⟩ = .E
        exact htok ⟨0, by omega⟩
      have hfirstBit :
          (bankTrialWindowFirstCell B).bit = true := hbit
      have hrootMode :
          (bankTrialWindowRootCell B).mode = .ARMED := hm
      have hraw := bankTrialC5RawHeadOne
        (compileAdvice q).b (compileAdvice q).theta
        (bankTrialWindowRootCell B)
        (bankTrialWindowFirstCell B)
        hb rfl rfl rfl hrootMode hfirstToken hfirstBit
      have hfields := bankTrialWindowRootFieldsEqPatch
        ring root hw B hf
      have hnewMode : bankTrialLiveWaveRootMode
          (GrantBankReference.bankLocalReferenceStepClamped
            ring root B root) = .IWAIT := by
        change
          ((GrantBankReference.bankLocalReferenceStepClamped
            ring root B root).fields ⟨0, by omega⟩).1 =
            .IWAIT
        rw [hfields]
        exact (bankTrialWindowRootPatchMode B).trans hraw.1
      have hnewToken : bankTrialLiveWaveToken
          (GrantBankReference.bankLocalReferenceStepClamped
            ring root B root) ⟨0, by omega⟩ = .IR := by
        change
          ((GrantBankReference.bankLocalReferenceStepClamped
            ring root B root).fields ⟨1, by omega⟩).2.2.1 =
            .IR
        rw [hfields]
        exact (bankTrialWindowRootPatchFirstToken B).trans
          hraw.2.2
      have hnewBit : bankTrialLiveWaveBit
          (GrantBankReference.bankLocalReferenceStepClamped
            ring root B root) ⟨0, by omega⟩ = false := by
        change
          ((GrantBankReference.bankLocalReferenceStepClamped
            ring root B root).fields ⟨1, by omega⟩).2.1 =
            false
        rw [hfields]
        exact (bankTrialWindowRootPatchFirstBit B).trans
          hraw.2.1
      have hnotCWait :
          (B.fields ⟨0, by omega⟩).1 ≠ .CWAIT := by
        change bankTrialLiveWaveRootMode B ≠ .CWAIT
        rw [hm]
        intro h
        cases h
      have hnewSuccess := bankTrialLocalUnlatchedNonCWaitNoWin
        ring root root B hf hnotCWait
      have hphase := bankTrialC5ArmedOneHeadLive
        ring root B begun hf hm hnewMode
      have hbank := bankTrialLocalNextLiveBank
        ring root root B begun
      refine ⟨⟨true, hphase⟩, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hbank]
        exact hnewSuccess
      · rw [hbank]
        exact hnewMode
      · exact bankTrialWindowWidthPos q
      · intro k
        rw [hbank]
        by_cases hk : k.val = 0
        · have heq : k = ⟨0, by omega⟩ := Fin.ext hk
          rw [heq, if_pos rfl]
          exact hnewToken
        · have hne : k ≠ ⟨0, by omega⟩ := by
            intro he
            have hv := congrArg Fin.val he
            exact hk hv
          have htail : bankTrialLiveWaveToken
              (GrantBankReference.bankLocalReferenceStepClamped
                ring root B root) k =
                bankTrialLiveWaveToken B k := by
            change
              ((GrantBankReference.bankLocalReferenceStepClamped
                ring root B root).fields ⟨k.val + 1, by omega⟩).2.2.1 =
              (B.fields ⟨k.val + 1, by omega⟩).2.2.1
            rw [hfields]
            exact bankTrialWindowRootPatchTailToken B k hne
          rw [if_neg hk, htail]
          exact htok k
      · intro k
        rw [hbank]
        by_cases hk : k.val = 0
        · have heq : k = ⟨0, by omega⟩ := Fin.ext hk
          rw [heq]
          simpa using hnewBit
        · have hne : k ≠ ⟨0, by omega⟩ := by
            intro he
            have hv := congrArg Fin.val he
            exact hk hv
          have htail : bankTrialLiveWaveBit
              (GrantBankReference.bankLocalReferenceStepClamped
                ring root B root) k =
                bankTrialLiveWaveBit B k := by
            change
              ((GrantBankReference.bankLocalReferenceStepClamped
                ring root B root).fields ⟨k.val + 1, by omega⟩).2.1 =
              (B.fields ⟨k.val + 1, by omega⟩).2.1
            rw [hfields]
            exact bankTrialWindowRootPatchTailBit B k hne
          have hnot : ¬ k.val ≤ 0 := by omega
          rw [if_neg hnot]
          exact htail

/-- Post-head base at any true CLEAN-origin ARMED prefix. -/
theorem bankTrialC5CleanHeadOneStage {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (w : List (Fin n)) (t : Nat)
    (hstart : BankTrialC5ArmedStart n q
      (bankTrialC5CleanRun ring root S w))
    (htrail : BankTrialC5TrailingOnes
      (bankTrialC5CleanRun ring root S w).bank t)
    (ht : 1 ≤ t) :
    BankTrialC5OutwardIRStage
      (bankTrialC5CleanRun ring root S w).bank 0
      (bankTrialC5OutwardPrefixRun ring root S w t 0) := by
  have hbit : bankTrialLiveWaveBit
      (bankTrialC5CleanRun ring root S w).bank
      ⟨0, by have := bankTrialWindowWidthPos q; omega⟩ =
      true := by
    exact htrail.2.1
      ⟨0, by have := bankTrialWindowWidthPos q; omega⟩
      (by change (0 : Nat) < t; omega)
  have hstep := bankTrialC5ArmedHeadOneStage
    ring root (bankTrialC5CleanRun ring root S w)
    hstart hbit
  change BankTrialC5OutwardIRStage
    (bankTrialC5CleanRun ring root S w).bank 0
    (bankTrialC5CleanRun ring root S
      (w ++ root ::
        (bankTrialC5OutwardEdges ring root t).take 0))
  simpa only [List.take_zero] using
    (show BankTrialC5OutwardIRStage
      (bankTrialC5CleanRun ring root S w).bank 0
      (bankTrialC5CleanRun ring root S (w ++ [root])) by
      rw [bankTrialC5CleanRunAppend]
      exact hstep)

/-- The full IR-only part of outward propagation, with hhead
discharged by the actual initial root service. -/
theorem bankTrialC5CleanOutwardIR {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S)
    (w : List (Fin n)) (t : Nat)
    (hstart : BankTrialC5ArmedStart n q
      (bankTrialC5CleanRun ring root S w))
    (htrail : BankTrialC5TrailingOnes
      (bankTrialC5CleanRun ring root S w).bank t)
    (ht : 1 ≤ t) :
    ∀ i : Nat, i < t →
      BankTrialC5OutwardIRStage
        (bankTrialC5CleanRun ring root S w).bank i
        (bankTrialC5OutwardPrefixRun ring root S w t i) := by
  exact bankTrialC5CleanOutwardIRFromHead
    ring root S hclean w t htrail hstart
    (bankTrialC5CleanHeadOneStage ring root S w t
      hstart htrail ht)

/-- On a designated inward G_j service carrying AL, the
entire protected binary digit array is a frame. -/
theorem bankTrialC5SelectedALAllBits {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hw : BankTrialLiveWindowNonalias n q)
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hf : B.success = false)
    (j : Fin (compileAdvice q).b) (hj : 0 < j.val)
    (hsrc : (B.fields ⟨j.val, by omega⟩).2.2.1 = .E)
    (hdst : (B.fields ⟨j.val + 1, by omega⟩).2.2.1 = .AL) :
    ∀ k : Fin (compileAdvice q).b,
      bankTrialLiveWaveBit
        (GrantBankReference.bankLocalReferenceStepClamped
          ring root B (Counter.site ring root j.val)) k =
        bankTrialLiveWaveBit B k := by
  have hrow := bankTrialC5SelectedALReturn
    ring root hw B hf j hj hsrc hdst
  intro k
  by_cases hs : k.val + 1 = j.val
  · change
      ((GrantBankReference.bankLocalReferenceStepClamped
        ring root B (Counter.site ring root j.val)).fields
        ⟨k.val + 1, by omega⟩).2.1 =
        (B.fields ⟨k.val + 1, by omega⟩).2.1
    have hk :
        (⟨k.val + 1, by omega⟩ :
          Fin ((compileAdvice q).b + 1)) =
        ⟨j.val, by omega⟩ := Fin.ext hs
    rw [hk]
    exact hrow.2.2.1
  · by_cases ht : k.val + 1 = j.val + 1
    · change
        ((GrantBankReference.bankLocalReferenceStepClamped
          ring root B (Counter.site ring root j.val)).fields
          ⟨k.val + 1, by omega⟩).2.1 =
          (B.fields ⟨k.val + 1, by omega⟩).2.1
      have hk :
          (⟨k.val + 1, by omega⟩ :
            Fin ((compileAdvice q).b + 1)) =
          ⟨j.val + 1, by omega⟩ := Fin.ext ht
      rw [hk]
      exact hrow.2.2.2
    · exact bankTrialC5InteriorOtherBitFrame
        ring root hw B hf j hj k hs ht

/-- The terminal outward G_t produces AL at protected wave
index t, sets that bit to one, and leaves lower bits zero. -/
def BankTrialC5ReturnALStage {q : Nat}
    (origin : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (t j : Nat) (z : BankTrialLocalState q) : Prop :=
  (∃ begun : Bool, z.phase = .live begun) ∧
  z.bank.success = false ∧
  bankTrialLiveWaveRootMode z.bank = .IWAIT ∧
  (j ≤ t ∧ t < (compileAdvice q).b) ∧
  (∀ k : Fin (compileAdvice q).b,
    bankTrialLiveWaveToken z.bank k =
      if k.val = j then .AL else .E) ∧
  (∀ k : Fin (compileAdvice q).b,
    bankTrialLiveWaveBit z.bank k =
      if k.val < t then false
      else if k.val = t then true
      else bankTrialLiveWaveBit origin k)

/-- One inward AL transport, j -> j-1; all protected bits are
unchanged, success remains false, and the root stays IWAIT.
The successor worker certificate comes from the real CLEAN
prefix rather than from an arbitrary forged local state. -/
theorem bankTrialC5ALReturnOneStep {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hw : BankTrialLiveWindowNonalias n q)
    (origin B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (t j : Nat) (begun : Bool)
    (hj : 0 < j)
    (hstage : BankTrialC5ReturnALStage origin t j
      (⟨B, .live begun⟩ : BankTrialLocalState q))
    (hnextLock : BankTrialLiveNoResetLocked
      (bankTrialLocalNext ring root
        (⟨B, .live begun⟩ : BankTrialLocalState q)
        (Counter.site ring root j))) :
    BankTrialC5ReturnALStage origin t (j - 1)
      (bankTrialLocalNext ring root
        (⟨B, .live begun⟩ : BankTrialLocalState q)
        (Counter.site ring root j)) := by
  rcases hstage with
    ⟨_, hf, hm, ⟨hjle, ht⟩, htoks, hbits⟩
  have hjbound : j < (compileAdvice q).b := by omega
  have hjminus : j - 1 < (compileAdvice q).b := by omega
  have hsrcTok : (B.fields ⟨j, by omega⟩).2.2.1 = .E := by
    have hnot : j - 1 ≠ j := by omega
    have h := htoks ⟨j - 1, hjminus⟩
    rw [if_neg hnot] at h
    change
      (B.fields ⟨j - 1 + 1, by omega⟩).2.2.1 = .E at h
    have hind :
        (⟨j - 1 + 1, by omega⟩ :
          Fin ((compileAdvice q).b + 1)) =
          ⟨j, by omega⟩ :=
      Fin.ext (by change j - 1 + 1 = j; omega)
    rw [hind] at h
    exact h
  have hdstTok :
      (B.fields ⟨j + 1, by omega⟩).2.2.1 = .AL := by
    change bankTrialLiveWaveToken B ⟨j, hjbound⟩ = .AL
    have h := htoks ⟨j, hjbound⟩
    simpa using h
  have hrow := bankTrialC5SelectedALReturn
    ring root hw B hf ⟨j, hjbound⟩
    (by change 0 < j; exact hj) hsrcTok hdstTok
  have hbitFrame := bankTrialC5SelectedALAllBits
    ring root hw B hf ⟨j, hjbound⟩
    (by change 0 < j; exact hj) hsrcTok hdstTok
  have hbank := bankTrialLocalNextLiveBank
    ring root (Counter.site ring root j) B begun
  have hs := bankTrialC5NonrootSuccessFrame ring root
    (Counter.site ring root j) B hf
    (bankTrialWindowInteriorNotRoot ring root hw
      ⟨j, hjbound⟩ (by change 0 < j; exact hj))
  have hmnext : bankTrialLiveWaveRootMode
      (GrantBankReference.bankLocalReferenceStepClamped
        ring root B (Counter.site ring root j)) = .IWAIT := by
    rw [bankTrialWindowInteriorRootModeFrame
      ring root hw B hf ⟨j, hjbound⟩ (by change 0 < j; exact hj)]
    exact hm
  obtain ⟨nextBegun, hphase⟩ :=
    bankTrialC5InteriorIWaitLive ring root hw B begun hf
      ⟨j, hjbound⟩ (by change 0 < j; exact hj) hm
  have hleftAL : bankTrialLiveWaveToken
      (GrantBankReference.bankLocalReferenceStepClamped
        ring root B (Counter.site ring root j))
        ⟨j - 1, hjminus⟩ = .AL := by
    change
      ((GrantBankReference.bankLocalReferenceStepClamped
        ring root B (Counter.site ring root j)).fields
        ⟨j - 1 + 1, by omega⟩).2.2.1 = .AL
    have hind :
        (⟨j - 1 + 1, by omega⟩ :
          Fin ((compileAdvice q).b + 1)) =
          ⟨j, by omega⟩ :=
      Fin.ext (by change j - 1 + 1 = j; omega)
    rw [hind]
    exact hrow.1
  have hcert : BankTrialLiveWaveCertificate q
      (bankTrialLocalNext ring root
        (⟨B, .live begun⟩ : BankTrialLocalState q)
        (Counter.site ring root j)).bank :=
    hnextLock.1 nextBegun hphase
  refine ⟨⟨nextBegun, hphase⟩, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hbank]
    exact hs
  · rw [hbank]
    exact hmnext
  · constructor
    · omega
    · exact ht
  · intro k
    rw [hbank]
    by_cases he : k.val = j - 1
    · have hk : k = ⟨j - 1, hjminus⟩ := Fin.ext he
      rw [hk, if_pos rfl]
      exact hleftAL
    · rw [if_neg he]
      have hleftNonempty : bankTrialLiveWaveToken
          (GrantBankReference.bankLocalReferenceStepClamped
            ring root B (Counter.site ring root j))
            ⟨j - 1, hjminus⟩ ≠ .E := by
        rw [hleftAL]
        intro h
        cases h
      have hk : k ≠ ⟨j - 1, hjminus⟩ := by
        intro eq
        have hv := congrArg Fin.val eq
        exact he hv
      have hother := bankTrialInteriorOldWorkerOthersEmpty
        (bankTrialLocalNext ring root
          (⟨B, .live begun⟩ : BankTrialLocalState q)
          (Counter.site ring root j)).bank
        hcert ⟨j - 1, hjminus⟩ k
        (by rw [hbank]; exact hleftNonempty) hk
      rw [hbank] at hother
      exact hother
  · intro k
    rw [hbank, hbitFrame k, hbits k]

/-- The wrapper allows an arbitrary actual LIVE state at the
current return index, without introducing a synthetic observer. -/
theorem bankTrialC5ALReturnOneStepState {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hw : BankTrialLiveWindowNonalias n q)
    (origin : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (t j : Nat) (z : BankTrialLocalState q)
    (hj : 0 < j)
    (hstage : BankTrialC5ReturnALStage origin t j z)
    (hnextLock : BankTrialLiveNoResetLocked
      (bankTrialLocalNext ring root z
        (Counter.site ring root j))) :
    BankTrialC5ReturnALStage origin t (j - 1)
      (bankTrialLocalNext ring root z
        (Counter.site ring root j)) := by
  obtain ⟨begun, hp⟩ := hstage.1
  cases z with
  | mk B phase =>
      change phase = .live begun at hp
      cases hp
      exact bankTrialC5ALReturnOneStep
        ring root hw origin B t j begun hj hstage hnextLock

/-- At the last outward G_t, an IR at wave index t-1
crosses the first zero, flips it to one, and produces AL
at wave index t. No extra flip edge is required. -/
theorem bankTrialC5FinalOutwardALStep {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hw : BankTrialLiveWindowNonalias n q)
    (origin B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (t : Nat) (begun : Bool)
    (ht : 1 ≤ t ∧ t < (compileAdvice q).b)
    (hstage : BankTrialC5OutwardIRStage origin (t - 1)
      (⟨B, .live begun⟩ : BankTrialLocalState q))
    (hzero : bankTrialLiveWaveBit origin
      ⟨t, ht.2⟩ = false)
    (hnextLock : BankTrialLiveNoResetLocked
      (bankTrialLocalNext ring root
        (⟨B, .live begun⟩ : BankTrialLocalState q)
        (Counter.site ring root t))) :
    BankTrialC5ReturnALStage origin t t
      (bankTrialLocalNext ring root
        (⟨B, .live begun⟩ : BankTrialLocalState q)
        (Counter.site ring root t)) := by
  rcases hstage with ⟨_, hf, hm, _, htoks, hbits⟩
  have hsrc : (B.fields ⟨t, by omega⟩).2.2.1 = .IR := by
    have h := htoks ⟨t - 1, by omega⟩
    have heq : t - 1 = t - 1 := rfl
    rw [if_pos heq] at h
    change (B.fields ⟨t - 1 + 1, by omega⟩).2.2.1 =
      .IR at h
    have hind :
        (⟨t - 1 + 1, by omega⟩ :
          Fin ((compileAdvice q).b + 1)) =
          ⟨t, by omega⟩ :=
      Fin.ext (by change t - 1 + 1 = t; omega)
    rw [hind] at h
    exact h
  have hdst : (B.fields ⟨t + 1, by omega⟩).2.2.1 = .E := by
    have h := htoks ⟨t, ht.2⟩
    have hne : t ≠ t - 1 := by omega
    rw [if_neg hne] at h
    exact h
  have holdDest : (B.fields ⟨t + 1, by omega⟩).2.1 =
      false := by
    have h := hbits ⟨t, ht.2⟩
    have hne : ¬ t ≤ t - 1 := by omega
    rw [if_neg hne] at h
    rw [hzero] at h
    exact h
  have hrow := bankTrialC5OutwardFirstZeroAL
    ring root hw B hf t ht hsrc hdst holdDest
  have hsourceBit := bankTrialC5SelectedIRSourceBit
    ring root B hf ⟨t, ht.2⟩
    (by change 0 < t; exact ht.1) hsrc hdst
  have hbank := bankTrialLocalNextLiveBank
    ring root (Counter.site ring root t) B begun
  have hs := bankTrialC5NonrootSuccessFrame ring root
    (Counter.site ring root t) B hf
    (bankTrialWindowInteriorNotRoot ring root hw
      ⟨t, ht.2⟩ (by change 0 < t; exact ht.1))
  have hmnew : bankTrialLiveWaveRootMode
      (GrantBankReference.bankLocalReferenceStepClamped
        ring root B (Counter.site ring root t)) = .IWAIT := by
    rw [bankTrialWindowInteriorRootModeFrame
      ring root hw B hf ⟨t, ht.2⟩
      (by change 0 < t; exact ht.1)]
    exact hm
  obtain ⟨nextBegun, hphase⟩ :=
    bankTrialC5InteriorIWaitLive ring root hw B begun hf
      ⟨t, ht.2⟩ (by change 0 < t; exact ht.1) hm
  have htoken : bankTrialLiveWaveToken
      (GrantBankReference.bankLocalReferenceStepClamped
        ring root B (Counter.site ring root t))
        ⟨t, ht.2⟩ = .AL := hrow.1
  have hcert : BankTrialLiveWaveCertificate q
      (bankTrialLocalNext ring root
        (⟨B, .live begun⟩ : BankTrialLocalState q)
        (Counter.site ring root t)).bank :=
    hnextLock.1 nextBegun hphase
  refine ⟨⟨nextBegun, hphase⟩, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hbank]
    exact hs
  · rw [hbank]
    exact hmnew
  · exact ⟨Nat.le_refl t, ht.2⟩
  · intro k
    rw [hbank]
    by_cases hk : k.val = t
    · have heq : k = ⟨t, ht.2⟩ := Fin.ext hk
      rw [heq, if_pos rfl]
      exact htoken
    · rw [if_neg hk]
      have hnotE : bankTrialLiveWaveToken
          (GrantBankReference.bankLocalReferenceStepClamped
            ring root B (Counter.site ring root t))
            ⟨t, ht.2⟩ ≠ .E := by
        rw [htoken]
        intro h
        cases h
      have hkneq : k ≠ ⟨t, ht.2⟩ := by
        intro he
        have hv := congrArg Fin.val he
        exact hk hv
      have hother := bankTrialInteriorOldWorkerOthersEmpty
        (bankTrialLocalNext ring root
          (⟨B, .live begun⟩ : BankTrialLocalState q)
          (Counter.site ring root t)).bank
        hcert ⟨t, ht.2⟩ k
        (by rw [hbank]; exact hnotE) hkneq
      rw [hbank] at hother
      exact hother
  · intro k
    rw [hbank]
    by_cases hk : k.val = t
    · have heq : k = ⟨t, ht.2⟩ := Fin.ext hk
      rw [heq]
      have hbit : bankTrialLiveWaveBit
          (GrantBankReference.bankLocalReferenceStepClamped
            ring root B (Counter.site ring root t))
            ⟨t, ht.2⟩ = true := hrow.2
      have hnt : ¬ t < t := Nat.lt_irrefl t
      simpa [hnt] using hbit
    · by_cases hsSource : k.val + 1 = t
      · have hraw : (B.fields ⟨t, by omega⟩).2.1 =
            false := by
          have hval : k.val = t - 1 := by omega
          have hkWave : k = ⟨t - 1, by omega⟩ :=
            Fin.ext hval
          have h := hbits k
          have hle : k.val ≤ t - 1 := by omega
          rw [if_pos hle] at h
          change (B.fields ⟨k.val + 1, by omega⟩).2.1 =
            false at h
          have heq :
              (⟨k.val + 1, by omega⟩ :
                Fin ((compileAdvice q).b + 1)) =
              ⟨t, by omega⟩ := Fin.ext hsSource
          rw [heq] at h
          exact h
        have hframe : bankTrialLiveWaveBit
            (GrantBankReference.bankLocalReferenceStepClamped
              ring root B (Counter.site ring root t)) k =
              bankTrialLiveWaveBit B k := by
          change
            ((GrantBankReference.bankLocalReferenceStepClamped
              ring root B (Counter.site ring root t)).fields
              ⟨k.val + 1, by omega⟩).2.1 =
            (B.fields ⟨k.val + 1, by omega⟩).2.1
          have heq :
              (⟨k.val + 1, by omega⟩ :
                Fin ((compileAdvice q).b + 1)) =
              ⟨t, by omega⟩ := Fin.ext hsSource
          rw [heq]
          exact hsourceBit
        have hless : k.val < t := by omega
        rw [hframe, hbits k, if_pos (by omega : k.val ≤ t - 1)]
        simp [hless]
      · have hframe := bankTrialC5InteriorOtherBitFrame
          ring root hw B hf ⟨t, ht.2⟩
          (by change 0 < t; exact ht.1) k
          hsSource (by change k.val + 1 ≠ t + 1; omega)
        rw [hframe, hbits k]
        by_cases hlt : k.val < t
        · have hle : k.val ≤ t - 1 := by omega
          simp [hlt, hle]
        · have hnotle : ¬ k.val ≤ t - 1 := by omega
          simp [hlt, hk, hnotle]

/-- The final crossing statement for any actual LIVE state. -/
theorem bankTrialC5FinalOutwardALStepState {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hw : BankTrialLiveWindowNonalias n q)
    (origin : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (t : Nat) (ht : 1 ≤ t ∧ t < (compileAdvice q).b)
    (z : BankTrialLocalState q)
    (hstage : BankTrialC5OutwardIRStage origin (t - 1) z)
    (hzero : bankTrialLiveWaveBit origin
      ⟨t, ht.2⟩ = false)
    (hnextLock : BankTrialLiveNoResetLocked
      (bankTrialLocalNext ring root z
        (Counter.site ring root t))) :
    BankTrialC5ReturnALStage origin t t
      (bankTrialLocalNext ring root z
        (Counter.site ring root t)) := by
  obtain ⟨begun, hp⟩ := hstage.1
  cases z with
  | mk B phase =>
      change phase = .live begun at hp
      cases hp
      exact bankTrialC5FinalOutwardALStep
        ring root hw origin B t begun ht hstage hzero hnextLock

/-- From a CLEAN prefix, the final G_t is the AL-producing
transition out of P_(t-1); the successor lock is obtained at
the exact extended scheduler word. -/
theorem bankTrialC5CleanOutwardAL {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S)
    (w : List (Fin n)) (t : Nat)
    (hstart : BankTrialC5ArmedStart n q
      (bankTrialC5CleanRun ring root S w))
    (htrail : BankTrialC5TrailingOnes
      (bankTrialC5CleanRun ring root S w).bank t)
    (ht : 1 ≤ t) :
    BankTrialC5ReturnALStage
      (bankTrialC5CleanRun ring root S w).bank t t
      (bankTrialC5OutwardPrefixRun ring root S w t t) := by
  have htt : 1 ≤ t ∧ t < (compileAdvice q).b :=
    ⟨ht, htrail.1⟩
  have hprev : t - 1 < t := by omega
  have hstage := bankTrialC5CleanOutwardIR
    ring root S hclean w t hstart htrail ht
    (t - 1) hprev
  have hzero := htrail.2.2 ⟨t, htrail.1⟩ rfl
  have hnextLock : BankTrialLiveNoResetLocked
      (bankTrialC5OutwardPrefixRun ring root S w t t) := by
    exact bankTrialC5CleanPrefixLocked ring root hstart.1
      S hclean w
      (root :: (bankTrialC5OutwardEdges ring root t).take t)
  have hnext := bankTrialC5OutwardPrefixNext
    ring root S w t (t - 1) hprev
  have hi : t - 1 + 1 = t := by omega
  rw [hi] at hnext
  rw [hnext] at hnextLock ⊢
  exact bankTrialC5FinalOutwardALStepState
    ring root hstart.1
    (bankTrialC5CleanRun ring root S w).bank
    t htt (bankTrialC5OutwardPrefixRun ring root S w t (t - 1))
    hstage hzero hnextLock

/-- The AL countdown word G_j,G_(j-1),...,G_1. -/
def bankTrialC5ReturnWord {n : Nat}
    (ring : DirectedRing n) (root : Fin n) :
    Nat → List (Fin n)
  | 0 => []
  | j + 1 =>
      Counter.site ring root (j + 1) ::
        bankTrialC5ReturnWord ring root j

/-- The original outward list appends G_(j+1) at its end. -/
theorem bankTrialC5OutwardSucc {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (j : Nat) :
    bankTrialC5OutwardEdges ring root (j + 1) =
      bankTrialC5OutwardEdges ring root j ++
        [Counter.site ring root (j + 1)] := by
  unfold bankTrialC5OutwardEdges
  have hr : List.range (j + 1) = List.range j ++ [j] := by
    simp only [List.range_eq_range', List.range'_1_concat,
      Nat.zero_add]
  rw [hr, List.map_append]
  rfl

/-- The recursive countdown is literally the already-defined
chronological inward AL word, not a new scheduler convention. -/
theorem bankTrialC5InwardIsReturnWord {n : Nat}
    (ring : DirectedRing n) (root : Fin n) :
    ∀ j : Nat,
      bankTrialC5InwardEdges ring root j =
        bankTrialC5ReturnWord ring root j := by
  intro j
  induction j with
  | zero =>
      rfl
  | succ j ih =>
      change
        (bankTrialC5OutwardEdges ring root (j + 1)).reverse =
          Counter.site ring root (j + 1) ::
            bankTrialC5ReturnWord ring root j
      rw [bankTrialC5OutwardSucc, List.reverse_append]
      change
        Counter.site ring root (j + 1) ::
          (bankTrialC5OutwardEdges ring root j).reverse =
        Counter.site ring root (j + 1) ::
          bankTrialC5ReturnWord ring root j
      have hrest :
          (bankTrialC5OutwardEdges ring root j).reverse =
            bankTrialC5ReturnWord ring root j := ih
      rw [hrest]

/-- Any single-AL return stage j descends to zero along its
entire countdown word. Locks for the successive observer
states are supplied at their actual suffixes. -/
theorem bankTrialC5ReturnWordDecreasesAL {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hw : BankTrialLiveWindowNonalias n q)
    (origin : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (t : Nat) :
    ∀ (j : Nat) (z : BankTrialLocalState q),
      BankTrialC5ReturnALStage origin t j z →
      (∀ suffix : List (Fin n),
        BankTrialLiveNoResetLocked
          (bankTrialLocalRun ring root suffix z)) →
      BankTrialC5ReturnALStage origin t 0
        (bankTrialLocalRun ring root
          (bankTrialC5ReturnWord ring root j) z) := by
  intro j
  induction j with
  | zero =>
      intro z hstage _
      change BankTrialC5ReturnALStage origin t 0 z
      exact hstage
  | succ j ih =>
      intro z hstage hlocks
      have hlockNext := hlocks
        [Counter.site ring root (j + 1)]
      change BankTrialLiveNoResetLocked
        (bankTrialLocalNext ring root z
          (Counter.site ring root (j + 1))) at hlockNext
      have hstep := bankTrialC5ALReturnOneStepState
        ring root hw origin t (j + 1) z
        (by omega) hstage hlockNext
      have hremaining :
          ∀ suffix : List (Fin n),
            BankTrialLiveNoResetLocked
              (bankTrialLocalRun ring root suffix
                (bankTrialLocalNext ring root z
                  (Counter.site ring root (j + 1)))) := by
        intro suffix
        exact hlocks (Counter.site ring root (j + 1) :: suffix)
      change BankTrialC5ReturnALStage origin t 0
        (bankTrialLocalRun ring root
          (bankTrialC5ReturnWord ring root j)
          (bankTrialLocalNext ring root z
            (Counter.site ring root (j + 1))))
      exact ih _ hstep hremaining

/-- From the genuine CLEAN seed and exact prefix P_t, the
entire installed inward word returns AL to digit one,
without changing the post-increment bit pattern. -/
theorem bankTrialC5CleanInwardAL {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S)
    (w : List (Fin n)) (t : Nat)
    (hstart : BankTrialC5ArmedStart n q
      (bankTrialC5CleanRun ring root S w))
    (htrail : BankTrialC5TrailingOnes
      (bankTrialC5CleanRun ring root S w).bank t)
    (ht : 1 ≤ t) :
    BankTrialC5ReturnALStage
      (bankTrialC5CleanRun ring root S w).bank t 0
      (bankTrialLocalRun ring root
        (bankTrialC5InwardEdges ring root t)
        (bankTrialC5OutwardPrefixRun ring root S w t t)) := by
  have hstage := bankTrialC5CleanOutwardAL
    ring root S hclean w t hstart htrail ht
  have hprefix :
      bankTrialC5OutwardPrefixRun ring root S w t t =
        bankTrialC5CleanRun ring root S
          (w ++ root :: bankTrialC5OutwardEdges ring root t) := by
    unfold bankTrialC5OutwardPrefixRun
    have hlen :
        (bankTrialC5OutwardEdges ring root t).length ≤ t := by
      rw [bankTrialC5OutwardLength]
      exact Nat.le_refl t
    rw [List.take_of_length_le hlen]
  have hlocks :
      ∀ suffix : List (Fin n),
        BankTrialLiveNoResetLocked
          (bankTrialLocalRun ring root suffix
            (bankTrialC5OutwardPrefixRun ring root S w t t)) := by
    intro suffix
    rw [hprefix, ← bankTrialC5CleanRunAppend]
    exact bankTrialWindowLockedCleanWords ring root
      hstart.1 S hclean
      ((w ++ root :: bankTrialC5OutwardEdges ring root t) ++
        suffix)
  rw [bankTrialC5InwardIsReturnWord]
  exact bankTrialC5ReturnWordDecreasesAL
    ring root hstart.1
    (bankTrialC5CleanRun ring root S w).bank
    t t (bankTrialC5OutwardPrefixRun ring root S w t t)
    hstage hlocks

/-- A LIVE CSTART endpoint with no workers and the exact
binary successor pattern of the original ARMED digits. -/
structure BankTrialC5IncrementedCStart {q : Nat}
    (origin : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (t : Nat) (z : BankTrialLocalState q) : Prop where
  live : ∃ begun : Bool, z.phase = .live begun
  unlatched : z.bank.success = false
  cstart : bankTrialLiveWaveRootMode z.bank = .CSTART
  empty : ∀ k : Fin (compileAdvice q).b,
    bankTrialLiveWaveToken z.bank k = .E
  bits : ∀ k : Fin (compileAdvice q).b,
    bankTrialLiveWaveBit z.bank k =
      if k.val < t then false
      else if k.val = t then true
      else bankTrialLiveWaveBit origin k

/-- Returning AL leaves its OLD first-digit bit intact. -/
private theorem bankTrialC5RawALRootReturnBit
    (b : Nat) (theta : Nat → Bool) (x y : BankCell)
    (hb : 1 ≤ b) (hx : x.role = 0) (hy : y.role = 1)
    (hg : x.grant = false) (hm : x.mode = .IWAIT)
    (ht : y.tok = .AL) :
    (bankPair x y 1 b theta).2.bit = y.bit := by
  simp [bankPair, hx, hy, hg, hm, ht, hb,
    isRetTok, isWaitMode, Id.run_pure, Id.run_bind]

/-- Root consumes AL at digit one, enters LIVE CSTART and
clears the final worker without changing any protected bit. -/
theorem bankTrialC5ALRootCStart {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hw : BankTrialLiveWindowNonalias n q)
    (origin B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (t : Nat) (begun : Bool)
    (hstage : BankTrialC5ReturnALStage origin t 0
      (⟨B, .live begun⟩ : BankTrialLocalState q)) :
    BankTrialC5IncrementedCStart origin t
      (bankTrialLocalNext ring root
        (⟨B, .live begun⟩ : BankTrialLocalState q) root) := by
  rcases hstage with ⟨_, hf, hm, _, htoks, hbits⟩
  have hb : 1 ≤ (compileAdvice q).b :=
    bankTrialWindowWidthPos q
  have hfirstAL :
      (bankTrialWindowFirstCell B).tok = .AL := by
    change bankTrialLiveWaveToken B ⟨0, by omega⟩ = .AL
    simpa using htoks ⟨0, by omega⟩
  have hrootMode :
      (bankTrialWindowRootCell B).mode = .IWAIT := hm
  have hraw := bankTrialC5RawALRootReturn
    (compileAdvice q).b (compileAdvice q).theta
    (bankTrialWindowRootCell B)
    (bankTrialWindowFirstCell B)
    hb rfl rfl rfl hrootMode hfirstAL
  have hrawBit := bankTrialC5RawALRootReturnBit
    (compileAdvice q).b (compileAdvice q).theta
    (bankTrialWindowRootCell B)
    (bankTrialWindowFirstCell B)
    hb rfl rfl rfl hrootMode hfirstAL
  have hfields := bankTrialWindowRootFieldsEqPatch
    ring root hw B hf
  have hmnew : bankTrialLiveWaveRootMode
      (GrantBankReference.bankLocalReferenceStepClamped
        ring root B root) = .CSTART := by
    change
      ((GrantBankReference.bankLocalReferenceStepClamped
        ring root B root).fields ⟨0, by omega⟩).1 = .CSTART
    rw [hfields]
    exact (bankTrialWindowRootPatchMode B).trans hraw.1
  have hfirstE : bankTrialLiveWaveToken
      (GrantBankReference.bankLocalReferenceStepClamped
        ring root B root) ⟨0, by omega⟩ = .E := by
    change
      ((GrantBankReference.bankLocalReferenceStepClamped
        ring root B root).fields ⟨1, by omega⟩).2.2.1 = .E
    rw [hfields]
    exact (bankTrialWindowRootPatchFirstToken B).trans hraw.2
  have hfirstBit : bankTrialLiveWaveBit
      (GrantBankReference.bankLocalReferenceStepClamped
        ring root B root) ⟨0, by omega⟩ =
      bankTrialLiveWaveBit B ⟨0, by omega⟩ := by
    change
      ((GrantBankReference.bankLocalReferenceStepClamped
        ring root B root).fields ⟨1, by omega⟩).2.1 =
      (B.fields ⟨1, by omega⟩).2.1
    rw [hfields]
    exact (bankTrialWindowRootPatchFirstBit B).trans
      (hrawBit.trans (bankTrialWindowRootOldFirstBit B))
  have hnotCWait :
      (B.fields ⟨0, by omega⟩).1 ≠ .CWAIT := by
    change bankTrialLiveWaveRootMode B ≠ .CWAIT
    rw [hm]
    intro h
    cases h
  have hfnew := bankTrialLocalUnlatchedNonCWaitNoWin
    ring root root B hf hnotCWait
  have hstep := bankTrialProbabilityLiveCStartNext
    ring root root B begun hfnew hmnew (Or.inl rfl)
  refine {
    live := ?_,
    unlatched := ?_,
    cstart := ?_,
    empty := ?_,
    bits := ?_
  }
  · rw [hstep]
    exact ⟨true, rfl⟩
  · rw [hstep]
    exact hfnew
  · rw [hstep]
    exact hmnew
  · intro k
    rw [hstep]
    by_cases hk : k.val = 0
    · have heq : k = ⟨0, by omega⟩ := Fin.ext hk
      rw [heq]
      exact hfirstE
    · have hne : k ≠ ⟨0, by omega⟩ := by
        intro he
        have hv := congrArg Fin.val he
        exact hk hv
      have hframe : bankTrialLiveWaveToken
          (GrantBankReference.bankLocalReferenceStepClamped
            ring root B root) k =
          bankTrialLiveWaveToken B k := by
        change
          ((GrantBankReference.bankLocalReferenceStepClamped
            ring root B root).fields ⟨k.val + 1, by omega⟩).2.2.1 =
          (B.fields ⟨k.val + 1, by omega⟩).2.2.1
        rw [hfields]
        exact bankTrialWindowRootPatchTailToken B k hne
      rw [hframe]
      have h := htoks k
      rw [if_neg hk] at h
      exact h
  · intro k
    rw [hstep]
    by_cases hk : k.val = 0
    · have heq : k = ⟨0, by omega⟩ := Fin.ext hk
      rw [heq, hfirstBit]
      exact hbits ⟨0, by omega⟩
    · have hne : k ≠ ⟨0, by omega⟩ := by
        intro he
        have hv := congrArg Fin.val he
        exact hk hv
      have hframe : bankTrialLiveWaveBit
          (GrantBankReference.bankLocalReferenceStepClamped
            ring root B root) k =
          bankTrialLiveWaveBit B k := by
        change
          ((GrantBankReference.bankLocalReferenceStepClamped
            ring root B root).fields ⟨k.val + 1, by omega⟩).2.1 =
          (B.fields ⟨k.val + 1, by omega⟩).2.1
        rw [hfields]
        exact bankTrialWindowRootPatchTailBit B k hne
      rw [hframe]
      exact hbits k

/-- Package a literal LIVE return stage before its root
service without changing the underlying observer state. -/
theorem bankTrialC5ALRootCStartState {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hw : BankTrialLiveWindowNonalias n q)
    (origin : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (t : Nat) (z : BankTrialLocalState q)
    (hstage : BankTrialC5ReturnALStage origin t 0 z) :
    BankTrialC5IncrementedCStart origin t
      (bankTrialLocalNext ring root z root) := by
  obtain ⟨begun, hp⟩ := hstage.1
  cases z with
  | mk B phase =>
      change phase = .live begun at hp
      cases hp
      exact bankTrialC5ALRootCStart
        ring root hw origin B t begun hstage

/-- A low-to-high finite binary reading, independent of the
reference's extra mode/token/lease fields. -/
def bankTrialC5BitValue (b : Nat) (f : Nat → Bool) : Nat :=
  (List.ofFn (fun k : Fin b =>
    if f k.val then 2 ^ k.val else 0)).sum

/-- Ordinary binary reading satisfies a head/tail recurrence. -/
theorem bankTrialC5BitValueSucc (b : Nat)
    (f : Nat → Bool) :
    bankTrialC5BitValue (b + 1) f =
      (if f 0 then 1 else 0) +
        2 * bankTrialC5BitValue b (fun j => f (j + 1)) := by
  have htail : ∀ i : Fin b,
      (if f (i.val + 1) then 2 ^ (i.val + 1) else 0) =
        2 * (if f (i.val + 1) then 2 ^ i.val else 0) := by
    intro i
    have hpow : 2 ^ (i.val + 1) = 2 * 2 ^ i.val := by
      rw [Nat.pow_succ]
      omega
    rw [hpow]
    cases hbit : f (i.val + 1) <;> simp [hbit]
  have hsum :
      (List.ofFn (fun i : Fin b =>
        if f (i.val + 1) then 2 ^ (i.val + 1) else 0)).sum =
      2 * (List.ofFn (fun i : Fin b =>
        if f (i.val + 1) then 2 ^ i.val else 0)).sum := by
    calc
      _ = (List.ofFn (fun i : Fin b =>
            2 * (if f (i.val + 1) then 2 ^ i.val else 0))).sum := by
              apply FiniteUniformStoppingTree.ofFn_sum_eq
              exact htail
      _ = _ := FiniteUniformStoppingTree.ofFn_sum_mul_left 2 _
  unfold bankTrialC5BitValue
  rw [List.ofFn_succ, List.sum_cons]
  change (if f 0 then 1 else 0) +
      (List.ofFn (fun i : Fin b =>
        if f (i.val + 1) then 2 ^ (i.val + 1) else 0)).sum =
    (if f 0 then 1 else 0) +
      2 * (List.ofFn (fun i : Fin b =>
        if f (i.val + 1) then 2 ^ i.val else 0)).sum
  rw [hsum]

/-- Exact binary carry at trailing run t, with no use of a
second inexact potential or phantom in-flight IR credit. -/
def bankTrialC5CarryBit (f : Nat → Bool)
    (t j : Nat) : Bool :=
  if j < t then false
  else if j = t then true
  else f j

theorem bankTrialC5BitValueCarry :
    ∀ (b t : Nat) (f : Nat → Bool),
      t < b →
      (∀ j : Nat, j < t → f j = true) →
      f t = false →
      bankTrialC5BitValue b (bankTrialC5CarryBit f t) =
        bankTrialC5BitValue b f + 1 := by
  intro b
  induction b with
  | zero =>
      intro t f ht _ _
      omega
  | succ b ih =>
      intro t f ht hones hzero
      cases t with
      | zero =>
          have hshift :
              (fun j => bankTrialC5CarryBit f 0 (j + 1)) =
                (fun j => f (j + 1)) := by
            funext j
            simp [bankTrialC5CarryBit]
          rw [bankTrialC5BitValueSucc,
            bankTrialC5BitValueSucc]
          rw [hshift]
          simp [bankTrialC5CarryBit, hzero] <;> omega
      | succ t =>
          have hzeroBit : f 0 = true := hones 0 (by omega)
          have htSmall : t < b := by omega
          have htailOnes :
              ∀ j : Nat, j < t → f (j + 1) = true := by
            intro j hj
            exact hones (j + 1) (by omega)
          have htailZero : f (t + 1) = false := hzero
          have hshift :
              (fun j => bankTrialC5CarryBit f (t + 1) (j + 1)) =
                (fun j => bankTrialC5CarryBit
                  (fun k => f (k + 1)) t j) := by
            funext j
            unfold bankTrialC5CarryBit
            by_cases hlt : j < t
            · have hlt' : j + 1 < t + 1 := by omega
              simp [hlt, hlt']
            · by_cases he : j = t
              · have hn : ¬ j + 1 < t + 1 := by omega
                have he' : j + 1 = t + 1 := by omega
                simp [hlt, he, hn, he']
              · have hn : ¬ j + 1 < t + 1 := by omega
                have he' : j + 1 ≠ t + 1 := by omega
                simp [hlt, he, hn, he']
          have htail := ih t (fun k => f (k + 1))
            htSmall htailOnes htailZero
          rw [bankTrialC5BitValueSucc,
            bankTrialC5BitValueSucc]
          rw [hshift, htail]
          have hhead :
              bankTrialC5CarryBit f (t + 1) 0 = false := by
            simp [bankTrialC5CarryBit]
          rw [hhead, hzeroBit]
          simp <;> omega

/-- Extend a finite reference's digit bits by false outside
its width, solely for the generic binary-carry lemma. -/
def bankTrialC5WindowBit {q : Nat}
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b) (j : Nat) : Bool :=
  if h : j < (compileAdvice q).b
  then bankTrialLiveWaveBit B ⟨j, h⟩
  else false

theorem bankTrialC5WindowBitAt {q : Nat}
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (j : Fin (compileAdvice q).b) :
    bankTrialC5WindowBit B j.val =
      bankTrialLiveWaveBit B j := by
  simp [bankTrialC5WindowBit, j.isLt]

theorem bankTrialC5BitValueWindow {q : Nat}
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b) :
    bankTrialC5BitValue (compileAdvice q).b
        (bankTrialC5WindowBit B) =
      bankTrialLiveBinaryValue B := by
  unfold bankTrialC5BitValue bankTrialLiveBinaryValue
  apply FiniteUniformStoppingTree.ofFn_sum_eq
  intro j
  rw [bankTrialC5WindowBitAt B j]
  rfl

/-- A finite successor bit pattern has exactly old binary
value plus one. All bounds are local to the protected width. -/
theorem bankTrialC5SuccessorBinary {q : Nat}
    (origin next : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (t : Nat)
    (htrail : BankTrialC5TrailingOnes origin t)
    (hbits : ∀ j : Fin (compileAdvice q).b,
      bankTrialLiveWaveBit next j =
        if j.val < t then false
        else if j.val = t then true
        else bankTrialLiveWaveBit origin j) :
    bankTrialLiveBinaryValue next =
      bankTrialLiveBinaryValue origin + 1 := by
  have hones :
      ∀ j : Nat, j < t →
        bankTrialC5WindowBit origin j = true := by
    intro j hj
    have htbound : t < (compileAdvice q).b := htrail.1
    have hb : j < (compileAdvice q).b := by omega
    have hbit := htrail.2.1 ⟨j, hb⟩ hj
    simpa [bankTrialC5WindowBit, hb] using hbit
  have hzero :
      bankTrialC5WindowBit origin t = false := by
    have hbit := htrail.2.2 ⟨t, htrail.1⟩ rfl
    simpa [bankTrialC5WindowBit, htrail.1] using hbit
  have hsum :
      bankTrialC5BitValue (compileAdvice q).b
          (bankTrialC5WindowBit next) =
        bankTrialC5BitValue (compileAdvice q).b
          (bankTrialC5CarryBit
            (bankTrialC5WindowBit origin) t) := by
    unfold bankTrialC5BitValue
    apply FiniteUniformStoppingTree.ofFn_sum_eq
    intro j
    rw [bankTrialC5WindowBitAt next j,
      hbits j]
    have horigin := bankTrialC5WindowBitAt origin j
    simp [bankTrialC5CarryBit, horigin]
  have hcarry := bankTrialC5BitValueCarry
    (compileAdvice q).b t (bankTrialC5WindowBit origin)
    htrail.1 hones hzero
  rw [← bankTrialC5BitValueWindow next,
      ← bankTrialC5BitValueWindow origin,
      hsum]
  exact hcarry

/-- At a LIVE CSTART endpoint with no outstanding worker,
the stored carry equals the original value plus one. -/
theorem bankTrialC5SuccessorCarry {q : Nat}
    (origin : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (z : BankTrialLocalState q)
    (t : Nat)
    (htrail : BankTrialC5TrailingOnes origin t)
    (hempty : ∀ j : Fin (compileAdvice q).b,
      bankTrialLiveWaveToken origin j = .E)
    (hfinal : BankTrialC5IncrementedCStart origin t z) :
    bankTrialLiveCarryValue z.bank =
      bankTrialLiveCarryValue origin + 1 := by
  rw [bankTrialC5NoWorkerCarryBinary z.bank hfinal.empty,
      bankTrialC5NoWorkerCarryBinary origin hempty]
  exact bankTrialC5SuccessorBinary
    origin z.bank t htrail hfinal.bits

/-- The t>0 C1 chronology is precisely HEAD, all outward
edges, all inward edges, and a final outgoing root return. -/
theorem bankTrialC5PositiveIncrementWord {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (t : Nat) (ht : 0 < t) :
    bankTrialC5IncrementWord ring root t =
      (root :: bankTrialC5OutwardEdges ring root t) ++
        (bankTrialC5InwardEdges ring root t ++ [root]) := by
  have hne : t ≠ 0 := by omega
  simp [bankTrialC5IncrementWord, hne, List.append_assoc]

/-- The final positive-trailing-count observer is literally
the root service following the complete return-AL word. -/
theorem bankTrialC5CleanPositiveCStart {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S)
    (w : List (Fin n)) (t : Nat)
    (hstart : BankTrialC5ArmedStart n q
      (bankTrialC5CleanRun ring root S w))
    (htrail : BankTrialC5TrailingOnes
      (bankTrialC5CleanRun ring root S w).bank t)
    (ht : 1 ≤ t) :
    BankTrialC5IncrementedCStart
      (bankTrialC5CleanRun ring root S w).bank t
      (bankTrialC5CleanRun ring root S
        (w ++ bankTrialC5IncrementWord ring root t)) := by
  have hreturned := bankTrialC5CleanInwardAL
    ring root S hclean w t hstart htrail ht
  have hroot := bankTrialC5ALRootCStartState
    ring root hstart.1
    (bankTrialC5CleanRun ring root S w).bank t
    (bankTrialLocalRun ring root
      (bankTrialC5InwardEdges ring root t)
      (bankTrialC5OutwardPrefixRun ring root S w t t))
    hreturned
  have hlength :
      (bankTrialC5OutwardEdges ring root t).length ≤ t := by
    rw [bankTrialC5OutwardLength]
    exact Nat.le_refl t
  have hp :
      bankTrialC5OutwardPrefixRun ring root S w t t =
      bankTrialLocalRun ring root
        (root :: bankTrialC5OutwardEdges ring root t)
        (bankTrialC5CleanRun ring root S w) := by
    unfold bankTrialC5OutwardPrefixRun
    rw [List.take_of_length_le hlength,
      bankTrialC5CleanRunAppend]
  unfold bankTrialC5CleanRun
  rw [bankTrialLocalRunAppend]
  rw [bankTrialC5PositiveIncrementWord ring root t (by omega)]
  unfold bankTrialC5CleanRun at hp
  rw [bankTrialLocalRunAppend, ← hp,
    bankTrialLocalRunAppend]
  change BankTrialC5IncrementedCStart
    (bankTrialLocalRun ring root w
      (bankTrialLocalStart S)).bank t
    (bankTrialLocalNext ring root
      (bankTrialLocalRun ring root
        (bankTrialC5InwardEdges ring root t)
        (bankTrialC5OutwardPrefixRun ring root S w t t))
      root)
  exact hroot

/-- Positive-t C1 with complete LIVE, CSTART, unlatched,
worker-empty, exact carry and CLEAN-origin lock conclusions. -/
theorem bankTrialC5CleanIncrementPositive {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S)
    (w : List (Fin n)) (t : Nat)
    (hstart : BankTrialC5ArmedStart n q
      (bankTrialC5CleanRun ring root S w))
    (htrail : BankTrialC5TrailingOnes
      (bankTrialC5CleanRun ring root S w).bank t)
    (ht : 1 ≤ t) :
    ∃ begun : Bool,
      (bankTrialC5CleanRun ring root S
        (w ++ bankTrialC5IncrementWord ring root t)).phase =
        .live begun ∧
      (bankTrialC5CleanRun ring root S
        (w ++ bankTrialC5IncrementWord ring root t)).bank.success =
        false ∧
      bankTrialLiveWaveRootMode
        (bankTrialC5CleanRun ring root S
          (w ++ bankTrialC5IncrementWord ring root t)).bank =
        .CSTART ∧
      (∀ k : Fin (compileAdvice q).b,
        bankTrialLiveWaveToken
          (bankTrialC5CleanRun ring root S
            (w ++ bankTrialC5IncrementWord ring root t)).bank k =
          .E) ∧
      bankTrialLiveCarryValue
        (bankTrialC5CleanRun ring root S
          (w ++ bankTrialC5IncrementWord ring root t)).bank =
        bankTrialLiveCarryValue
          (bankTrialC5CleanRun ring root S w).bank + 1 ∧
      BankTrialLiveNoResetLocked
        (bankTrialC5CleanRun ring root S
          (w ++ bankTrialC5IncrementWord ring root t)) := by
  have hfinal := bankTrialC5CleanPositiveCStart
    ring root S hclean w t hstart htrail ht
  obtain ⟨begun, hphase⟩ := hfinal.live
  refine ⟨begun, hphase, hfinal.unlatched,
    hfinal.cstart, hfinal.empty, ?_, ?_⟩
  · exact bankTrialC5SuccessorCarry
      (bankTrialC5CleanRun ring root S w).bank
      (bankTrialC5CleanRun ring root S
        (w ++ bankTrialC5IncrementWord ring root t))
      t htrail hstart.2.2.2.2.2 hfinal
  · exact bankTrialC5CleanPrefixLocked
      ring root hstart.1 S hclean w
      (bankTrialC5IncrementWord ring root t)

/-- At t=0 the old first bit is zero: one root service
sets it to one, leaves all workers empty, and enters CSTART. -/
theorem bankTrialC5ArmedHeadZeroCStart {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (z : BankTrialLocalState q)
    (hstart : BankTrialC5ArmedStart n q z)
    (hbit : bankTrialLiveWaveBit z.bank
      ⟨0, by have := bankTrialWindowWidthPos q; omega⟩ =
      false) :
    BankTrialC5IncrementedCStart z.bank 0
      (bankTrialLocalNext ring root z root) := by
  obtain ⟨hw, _, ⟨begun, hlive⟩, hf, hm, htok⟩ := hstart
  cases z with
  | mk B phase =>
      change phase = .live begun at hlive
      cases hlive
      have hb : 1 ≤ (compileAdvice q).b :=
        bankTrialWindowWidthPos q
      have hfirstToken :
          (bankTrialWindowFirstCell B).tok = .E := by
        change bankTrialLiveWaveToken B ⟨0, by omega⟩ = .E
        exact htok ⟨0, by omega⟩
      have hfirstBit :
          (bankTrialWindowFirstCell B).bit = false := hbit
      have hrootMode :
          (bankTrialWindowRootCell B).mode = .ARMED := hm
      have hraw := bankTrialC5RawHeadZero
        (compileAdvice q).b (compileAdvice q).theta
        (bankTrialWindowRootCell B)
        (bankTrialWindowFirstCell B)
        hb rfl rfl rfl hrootMode hfirstToken hfirstBit
      have hfields := bankTrialWindowRootFieldsEqPatch
        ring root hw B hf
      have hmnew : bankTrialLiveWaveRootMode
          (GrantBankReference.bankLocalReferenceStepClamped
            ring root B root) = .CSTART := by
        change
          ((GrantBankReference.bankLocalReferenceStepClamped
            ring root B root).fields ⟨0, by omega⟩).1 =
            .CSTART
        rw [hfields]
        exact (bankTrialWindowRootPatchMode B).trans hraw.1
      have hfirstNew : bankTrialLiveWaveToken
          (GrantBankReference.bankLocalReferenceStepClamped
            ring root B root) ⟨0, by omega⟩ = .E := by
        change
          ((GrantBankReference.bankLocalReferenceStepClamped
            ring root B root).fields ⟨1, by omega⟩).2.2.1 =
            .E
        rw [hfields]
        exact (bankTrialWindowRootPatchFirstToken B).trans
          hraw.2.2
      have hbitNew : bankTrialLiveWaveBit
          (GrantBankReference.bankLocalReferenceStepClamped
            ring root B root) ⟨0, by omega⟩ = true := by
        change
          ((GrantBankReference.bankLocalReferenceStepClamped
            ring root B root).fields ⟨1, by omega⟩).2.1 =
            true
        rw [hfields]
        exact (bankTrialWindowRootPatchFirstBit B).trans
          hraw.2.1
      have hnotCWait :
          (B.fields ⟨0, by omega⟩).1 ≠ .CWAIT := by
        change bankTrialLiveWaveRootMode B ≠ .CWAIT
        rw [hm]
        intro h
        cases h
      have hfnew := bankTrialLocalUnlatchedNonCWaitNoWin
        ring root root B hf hnotCWait
      have hstep := bankTrialProbabilityLiveCStartNext
        ring root root B begun hfnew hmnew (Or.inl rfl)
      refine {
        live := ?_,
        unlatched := ?_,
        cstart := ?_,
        empty := ?_,
        bits := ?_
      }
      · rw [hstep]
        exact ⟨true, rfl⟩
      · rw [hstep]
        exact hfnew
      · rw [hstep]
        exact hmnew
      · intro k
        rw [hstep]
        by_cases hk : k.val = 0
        · have heq : k = ⟨0, by omega⟩ := Fin.ext hk
          rw [heq]
          exact hfirstNew
        · have hne : k ≠ ⟨0, by omega⟩ := by
            intro he
            have hv := congrArg Fin.val he
            exact hk hv
          have hframe : bankTrialLiveWaveToken
              (GrantBankReference.bankLocalReferenceStepClamped
                ring root B root) k =
              bankTrialLiveWaveToken B k := by
            change
              ((GrantBankReference.bankLocalReferenceStepClamped
                ring root B root).fields ⟨k.val + 1, by omega⟩).2.2.1 =
              (B.fields ⟨k.val + 1, by omega⟩).2.2.1
            rw [hfields]
            exact bankTrialWindowRootPatchTailToken B k hne
          rw [hframe]
          exact htok k
      · intro k
        rw [hstep]
        by_cases hk : k.val = 0
        · have heq : k = ⟨0, by omega⟩ := Fin.ext hk
          rw [heq]
          simpa using hbitNew
        · have hne : k ≠ ⟨0, by omega⟩ := by
            intro he
            have hv := congrArg Fin.val he
            exact hk hv
          have hframe : bankTrialLiveWaveBit
              (GrantBankReference.bankLocalReferenceStepClamped
                ring root B root) k =
              bankTrialLiveWaveBit B k := by
            change
              ((GrantBankReference.bankLocalReferenceStepClamped
                ring root B root).fields ⟨k.val + 1, by omega⟩).2.1 =
              (B.fields ⟨k.val + 1, by omega⟩).2.1
            rw [hfields]
            exact bankTrialWindowRootPatchTailBit B k hne
          simp [hk]
          exact hframe

/-- The zero-trailing case is a one-letter CLEAN-origin run. -/
theorem bankTrialC5CleanZeroCStart {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (w : List (Fin n))
    (hstart : BankTrialC5ArmedStart n q
      (bankTrialC5CleanRun ring root S w))
    (htrail : BankTrialC5TrailingOnes
      (bankTrialC5CleanRun ring root S w).bank 0) :
    BankTrialC5IncrementedCStart
      (bankTrialC5CleanRun ring root S w).bank 0
      (bankTrialC5CleanRun ring root S
        (w ++ bankTrialC5IncrementWord ring root 0)) := by
  have hbit : bankTrialLiveWaveBit
      (bankTrialC5CleanRun ring root S w).bank
      ⟨0, by have := bankTrialWindowWidthPos q; omega⟩ =
      false := by
    exact htrail.2.2
      ⟨0, by have := bankTrialWindowWidthPos q; omega⟩ rfl
  have hstep := bankTrialC5ArmedHeadZeroCStart
    ring root (bankTrialC5CleanRun ring root S w)
    hstart hbit
  have hword : bankTrialC5IncrementWord ring root 0 =
      [root] := rfl
  rw [hword, bankTrialC5CleanRunAppend]
  exact hstep

/-- Full C1 increment from every certified CLEAN-reachable
ARMED prefix, including both t=0 and t>0. The theta advice
is fixed by compileAdvice and is never a mutable BANK field. -/
theorem bankTrialC5CleanIncrement {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S)
    (w : List (Fin n)) (t : Nat)
    (hstart : BankTrialC5ArmedStart n q
      (bankTrialC5CleanRun ring root S w))
    (htrail : BankTrialC5TrailingOnes
      (bankTrialC5CleanRun ring root S w).bank t)
    (hbound :
      bankTrialLiveCarryValue
        (bankTrialC5CleanRun ring root S w).bank + 1 <
        2 ^ (compileAdvice q).b) :
    ∃ begun : Bool,
      (bankTrialC5CleanRun ring root S
        (w ++ bankTrialC5IncrementWord ring root t)).phase =
        .live begun ∧
      (bankTrialC5CleanRun ring root S
        (w ++ bankTrialC5IncrementWord ring root t)).bank.success =
        false ∧
      bankTrialLiveWaveRootMode
        (bankTrialC5CleanRun ring root S
          (w ++ bankTrialC5IncrementWord ring root t)).bank =
        .CSTART ∧
      (∀ k : Fin (compileAdvice q).b,
        bankTrialLiveWaveToken
          (bankTrialC5CleanRun ring root S
            (w ++ bankTrialC5IncrementWord ring root t)).bank k =
          .E) ∧
      bankTrialLiveCarryValue
        (bankTrialC5CleanRun ring root S
          (w ++ bankTrialC5IncrementWord ring root t)).bank =
        bankTrialLiveCarryValue
          (bankTrialC5CleanRun ring root S w).bank + 1 ∧
      BankTrialLiveNoResetLocked
        (bankTrialC5CleanRun ring root S
          (w ++ bankTrialC5IncrementWord ring root t)) := by
  cases t with
  | zero =>
      have hfinal := bankTrialC5CleanZeroCStart
        ring root S w hstart htrail
      obtain ⟨begun, hphase⟩ := hfinal.live
      refine ⟨begun, hphase, hfinal.unlatched,
        hfinal.cstart, hfinal.empty, ?_, ?_⟩
      · exact bankTrialC5SuccessorCarry
          (bankTrialC5CleanRun ring root S w).bank
          (bankTrialC5CleanRun ring root S
            (w ++ bankTrialC5IncrementWord ring root 0))
          0 htrail hstart.2.2.2.2.2 hfinal
      · exact bankTrialC5CleanPrefixLocked
          ring root hstart.1 S hclean w
          (bankTrialC5IncrementWord ring root 0)
  | succ t =>
      exact bankTrialC5CleanIncrementPositive
        ring root S hclean w (t + 1) hstart htrail
        (by omega)

end L3

namespace L3

open Classical

set_option autoImplicit false
set_option Elab.async false

/-- C2 is supplied by the separate comparator proof.  This is a
proposition, not a theorem or an additional transition axiom. -/
def BankTrialC5ComparisonCorrect (n q : Nat)
    (ring : DirectedRing n) (root : Fin n) : Prop :=
  ∀ z : BankTrialLocalState q,
    BankTrialLiveWindowNonalias n q →
    2 ≤ (compileAdvice q).b →
    BankTrialLiveNoResetLocked z →
    (∃ begun : Bool, z.phase = .live begun) →
    z.bank.success = false →
    bankTrialLiveWaveRootMode z.bank = .CSTART →
    (∀ j : Fin (compileAdvice q).b,
      bankTrialLiveWaveToken z.bank j = .E) →
    0 < bankTrialLiveBinaryValue z.bank →
    if bankTrialLiveBinaryValue z.bank =
        bankTrialLiveThetaBinary q then
      (bankTrialLocalRun ring root
        (bankTrialC5ComparisonWord ring root
          (compileAdvice q).b) z).phase = .won
    else
      ∃ begun : Bool,
        (bankTrialLocalRun ring root
          (bankTrialC5ComparisonWord ring root
            (compileAdvice q).b) z).phase = .live begun ∧
        bankTrialLiveWaveRootMode
          (bankTrialLocalRun ring root
            (bankTrialC5ComparisonWord ring root
              (compileAdvice q).b) z).bank = .ARMED ∧
        (∀ j : Fin (compileAdvice q).b,
          bankTrialLiveWaveToken
            (bankTrialLocalRun ring root
              (bankTrialC5ComparisonWord ring root
                (compileAdvice q).b) z).bank j = .E) ∧
        (∀ j : Fin (compileAdvice q).b,
          bankTrialLiveWaveBit
            (bankTrialLocalRun ring root
              (bankTrialC5ComparisonWord ring root
                (compileAdvice q).b) z).bank j =
            bankTrialLiveWaveBit z.bank j) ∧
        (bankTrialLocalRun ring root
          (bankTrialC5ComparisonWord ring root
            (compileAdvice q).b) z).bank.success = false

/-- The number of trailing one bits, recursively removing an
odd low-order bit.  No unbounded search or Nat.find is used. -/
def bankTrialC5Trailing (k : Nat) : Nat :=
  if k % 2 = 0 then 0
  else bankTrialC5Trailing (k / 2) + 1
termination_by k
decreasing_by omega

/-- The trailing-one definition identifies all lower one bits,
the first zero bit, and bounds the corresponding power of two. -/
theorem bankTrialC5TrailingSpec :
    ∀ k : Nat,
      (∀ j : Nat, j < bankTrialC5Trailing k →
        k / 2 ^ j % 2 = 1) ∧
      k / 2 ^ bankTrialC5Trailing k % 2 = 0 ∧
      2 ^ bankTrialC5Trailing k ≤ k + 1 := by
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
      by_cases heven : k % 2 = 0
      · have ht : bankTrialC5Trailing k = 0 := by
          rw [bankTrialC5Trailing.eq_1]
          simp [heven]
        rw [ht]
        refine ⟨?_, ?_, ?_⟩
        · intro j hj
          omega
        · simpa using heven
        · simp
      · have hmod : k % 2 < 2 := Nat.mod_lt k (by omega)
        have hodd : k % 2 = 1 := by omega
        have hpos : 0 < k := by omega
        have hlt : k / 2 < k := by omega
        have hrec := ih (k / 2) hlt
        have ht :
            bankTrialC5Trailing k =
              bankTrialC5Trailing (k / 2) + 1 := by
          rw [bankTrialC5Trailing.eq_1]
          simp [heven]
        rw [ht]
        refine ⟨?_, ?_, ?_⟩
        · intro j hj
          cases j with
          | zero =>
              simpa using hodd
          | succ j =>
              have hjprev : j < bankTrialC5Trailing (k / 2) := by
                omega
              have hdiv :
                  k / 2 ^ (j + 1) = (k / 2) / 2 ^ j := by
                rw [Nat.div_div_eq_div_mul, Nat.pow_succ]
                ac_rfl
              rw [hdiv]
              exact hrec.1 j hjprev
        · have hdiv :
              k / 2 ^ (bankTrialC5Trailing (k / 2) + 1) =
                (k / 2) / 2 ^ bankTrialC5Trailing (k / 2) := by
            rw [Nat.div_div_eq_div_mul, Nat.pow_succ]
            ac_rfl
          rw [hdiv]
          exact hrec.2.1
        · have hpow :
              2 ^ (bankTrialC5Trailing (k / 2) + 1) =
                2 * 2 ^ bankTrialC5Trailing (k / 2) := by
            rw [Nat.pow_succ]
            omega
          have hsplit := Nat.mod_add_div k 2
          rw [hpow]
          omega

/-- Uniqueness of each digit in a finite low-to-high binary sum.
This avoids assuming the trailing-bit pattern from the schedule. -/
theorem bankTrialC5BitValueDigit :
    ∀ (b : Nat) (f : Nat → Bool) (j : Nat),
      j < b →
      f j =
        decide (bankTrialC5BitValue b f / 2 ^ j % 2 = 1) := by
  intro b
  induction b with
  | zero =>
      intro f j hj
      omega
  | succ b ih =>
      intro f j hj
      have hquot :
          bankTrialC5BitValue (b + 1) f / 2 =
            bankTrialC5BitValue b (fun i => f (i + 1)) := by
        rw [bankTrialC5BitValueSucc]
        cases hbit : f 0 <;> simp [hbit] <;> omega
      cases j with
      | zero =>
          have hmod :
              bankTrialC5BitValue (b + 1) f % 2 =
                (if f 0 then 1 else 0) := by
            rw [bankTrialC5BitValueSucc]
            cases hbit : f 0 <;> simp [hbit] <;> omega
          simp only [Nat.pow_zero, Nat.div_one]
          cases hbit : f 0 with
          | false =>
              have hz :
                  bankTrialC5BitValue (b + 1) f % 2 = 0 := by
                rw [hmod, hbit]
                rfl
              rw [hz]
              decide
          | true =>
              have ho :
                  bankTrialC5BitValue (b + 1) f % 2 = 1 := by
                rw [hmod, hbit]
                rfl
              rw [ho]
              decide
      | succ j =>
          have hrec := ih (fun i => f (i + 1)) j (by omega)
          have hdiv :
              bankTrialC5BitValue (b + 1) f / 2 ^ (j + 1) =
                (bankTrialC5BitValue (b + 1) f / 2) / 2 ^ j := by
            rw [Nat.div_div_eq_div_mul, Nat.pow_succ]
            ac_rfl
          calc
            f (j + 1) =
                decide
                  (bankTrialC5BitValue b (fun i => f (i + 1)) /
                    2 ^ j % 2 = 1) := hrec
            _ = decide
                  (bankTrialC5BitValue (b + 1) f /
                    2 ^ (j + 1) % 2 = 1) := by
              rw [← hquot, ← hdiv]

/-- A zero-worker word with binary value k has exactly the
actual trailing-one pattern of k, provided k+1 fits strictly
below the b-bit capacity. -/
theorem bankTrialC5TrailingFromBinary {q : Nat}
    (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (k : Nat)
    (hvalue : bankTrialLiveBinaryValue B = k)
    (hbound : k + 1 < 2 ^ (compileAdvice q).b) :
    BankTrialC5TrailingOnes B (bankTrialC5Trailing k) := by
  have hspec := bankTrialC5TrailingSpec k
  have ht :
      bankTrialC5Trailing k < (compileAdvice q).b := by
    by_cases hlt : bankTrialC5Trailing k < (compileAdvice q).b
    · exact hlt
    · have hle : (compileAdvice q).b ≤ bankTrialC5Trailing k := by
        omega
      have hpow : 2 ^ (compileAdvice q).b ≤
          2 ^ bankTrialC5Trailing k :=
        Nat.pow_le_pow_right (by omega) hle
      omega
  have hbit (j : Fin (compileAdvice q).b) :
      bankTrialLiveWaveBit B j =
        decide (k / 2 ^ j.val % 2 = 1) := by
    have hdigit := bankTrialC5BitValueDigit
      (compileAdvice q).b (bankTrialC5WindowBit B) j.val j.isLt
    rw [bankTrialC5BitValueWindow B, hvalue] at hdigit
    exact (bankTrialC5WindowBitAt B j).symm.trans hdigit
  refine ⟨ht, ?_, ?_⟩
  · intro j hj
    calc
      bankTrialLiveWaveBit B j =
          decide (k / 2 ^ j.val % 2 = 1) := hbit j
      _ = true := by
        rw [hspec.1 j.val hj]
        decide
  · intro j hj
    calc
      bankTrialLiveWaveBit B j =
          decide (k / 2 ^ j.val % 2 = 1) := hbit j
      _ = false := by
        rw [hj, hspec.2.1]
        decide

/-- Digitwise preservation by the comparator preserves the
numeric binary value.  No assumption on tokens is necessary. -/
theorem bankTrialC5BinaryFrame {q : Nat}
    (old new : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hbits : ∀ j : Fin (compileAdvice q).b,
      bankTrialLiveWaveBit new j = bankTrialLiveWaveBit old j) :
    bankTrialLiveBinaryValue new = bankTrialLiveBinaryValue old := by
  unfold bankTrialLiveBinaryValue
  apply FiniteUniformStoppingTree.ofFn_sum_eq
  intro j
  change
    (if bankTrialLiveWaveBit new j then 2 ^ j.val else 0) =
      (if bankTrialLiveWaveBit old j then 2 ^ j.val else 0)
  rw [hbits j]

/-- The induction certificate includes precisely the six
requested post-round facts, with no synthetic state updates. -/
def BankTrialC5ArmedAt (q : Nat)
    (z : BankTrialLocalState q) (k : Nat) : Prop :=
  ∃ begun : Bool,
    z.phase = .live begun ∧
    bankTrialLiveWaveRootMode z.bank = .ARMED ∧
    (∀ j : Fin (compileAdvice q).b,
      bankTrialLiveWaveToken z.bank j = .E) ∧
    bankTrialLiveBinaryValue z.bank = k ∧
    z.bank.success = false ∧
    BankTrialLiveNoResetLocked z

/-- The empty schedule is already an ARMED, zero-valued,
empty-worker and locked LIVE state at the genuine CLEAN seed. -/
theorem bankTrialC5SeedArmed {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hw : BankTrialLiveWindowNonalias n q)
    (hclean : BankTrialLocalClean q S) :
    BankTrialC5ArmedAt q
      (bankTrialC5CleanRun ring root S []) 0 := by
  change BankTrialC5ArmedAt q (bankTrialLocalStart S) 0
  refine ⟨false, rfl, hclean.2.1, ?_,
    bankTrialLiveBinaryClean S hclean, hclean.1, ?_⟩
  · intro j
    exact (hclean.2.2.1 (j.val + 1)
      (by omega) (by omega)).2
  · exact bankTrialWindowLockedCleanWords
      ring root hw S hclean []

/-- C3 induction, with the final comparator separated from
the strict-prefix case.  C2 is passed only as a hypothesis. -/
theorem bankTrialC5RoundsStatus {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hq : 3 ≤ q)
    (hw : BankTrialLiveWindowNonalias n q)
    (hb : 2 ≤ (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S)
    (hcomparison : BankTrialC5ComparisonCorrect n q ring root) :
    ∀ k : Nat, k ≤ (compileAdvice q).K →
      (k < (compileAdvice q).K →
        BankTrialC5ArmedAt q
          (bankTrialC5CleanRun ring root S
            (bankTrialC5Rounds ring root
              (compileAdvice q).b bankTrialC5Trailing k)) k) ∧
      (k = (compileAdvice q).K →
        (bankTrialC5CleanRun ring root S
          (bankTrialC5Rounds ring root
            (compileAdvice q).b bankTrialC5Trailing k)).phase =
          .won) := by
  have hKbound := compileAdvice_K_lt_two_pow_b q hq
  have htheta := bankTrialProbabilityThetaBinaryEqualsK q hq
  intro k
  induction k with
  | zero =>
      intro _
      constructor
      · intro _
        change BankTrialC5ArmedAt q
          (bankTrialC5CleanRun ring root S []) 0
        exact bankTrialC5SeedArmed ring root S hw hclean
      · intro hzero
        have hK : (compileAdvice q).K =
            2 * q + productionKappa q := rfl
        have hpos : 0 < (compileAdvice q).K := by omega
        omega
  | succ k ih =>
      intro hkle
      have hklt : k < (compileAdvice q).K := by omega
      have hprev := (ih (by omega)).1 hklt
      rcases hprev with
        ⟨begun, hphase, hmode, htokens, hvalue, hsuccess, hlocked⟩
      have hcarry :
          bankTrialLiveCarryValue
            (bankTrialC5CleanRun ring root S
              (bankTrialC5Rounds ring root
                (compileAdvice q).b bankTrialC5Trailing k)).bank =
              k := by
        rw [bankTrialC5NoWorkerCarryBinary _ htokens]
        exact hvalue
      have hstart :
          BankTrialC5ArmedStart n q
            (bankTrialC5CleanRun ring root S
              (bankTrialC5Rounds ring root
                (compileAdvice q).b bankTrialC5Trailing k)) :=
        ⟨hw, hlocked, ⟨begun, hphase⟩,
          hsuccess, hmode, htokens⟩
      have htrail :
          BankTrialC5TrailingOnes
            (bankTrialC5CleanRun ring root S
              (bankTrialC5Rounds ring root
                (compileAdvice q).b bankTrialC5Trailing k)).bank
            (bankTrialC5Trailing k) :=
        bankTrialC5TrailingFromBinary _ k hvalue (by omega)
      have hroom :
          bankTrialLiveCarryValue
            (bankTrialC5CleanRun ring root S
              (bankTrialC5Rounds ring root
                (compileAdvice q).b bankTrialC5Trailing k)).bank +
              1 < 2 ^ (compileAdvice q).b := by
        rw [hcarry]
        omega
      obtain ⟨afterBegun, afterPhase, afterSuccess,
        afterMode, afterTokens, afterCarry, afterLocked⟩ :=
        bankTrialC5CleanIncrement ring root S hclean
          (bankTrialC5Rounds ring root
            (compileAdvice q).b bankTrialC5Trailing k)
          (bankTrialC5Trailing k) hstart htrail hroom
      have afterValue :
          bankTrialLiveBinaryValue
            (bankTrialC5CleanRun ring root S
              (bankTrialC5Rounds ring root
                (compileAdvice q).b bankTrialC5Trailing k ++
                bankTrialC5IncrementWord ring root
                  (bankTrialC5Trailing k))).bank = k + 1 := by
        rw [← bankTrialC5NoWorkerCarryBinary _ afterTokens]
        rw [afterCarry, hcarry]
      have hpositive :
          0 < bankTrialLiveBinaryValue
            (bankTrialC5CleanRun ring root S
              (bankTrialC5Rounds ring root
                (compileAdvice q).b bankTrialC5Trailing k ++
                bankTrialC5IncrementWord ring root
                  (bankTrialC5Trailing k))).bank := by
        rw [afterValue]
        omega
      have hcomp := hcomparison
        (bankTrialC5CleanRun ring root S
          (bankTrialC5Rounds ring root
            (compileAdvice q).b bankTrialC5Trailing k ++
            bankTrialC5IncrementWord ring root
              (bankTrialC5Trailing k)))
        hw hb afterLocked ⟨afterBegun, afterPhase⟩
        afterSuccess afterMode afterTokens hpositive
      have hconcat :
          bankTrialC5Rounds ring root
            (compileAdvice q).b bankTrialC5Trailing (k + 1) =
          (bankTrialC5Rounds ring root
            (compileAdvice q).b bankTrialC5Trailing k ++
            bankTrialC5IncrementWord ring root
              (bankTrialC5Trailing k)) ++
            bankTrialC5ComparisonWord ring root
              (compileAdvice q).b := by
        change
          (bankTrialC5Rounds ring root
            (compileAdvice q).b bankTrialC5Trailing k ++
            (bankTrialC5IncrementWord ring root
              (bankTrialC5Trailing k) ++
              bankTrialC5ComparisonWord ring root
                (compileAdvice q).b)) = _
        exact (List.append_assoc _ _ _).symm
      have hround :
          bankTrialC5CleanRun ring root S
            (bankTrialC5Rounds ring root
              (compileAdvice q).b bankTrialC5Trailing (k + 1)) =
          bankTrialLocalRun ring root
            (bankTrialC5ComparisonWord ring root
              (compileAdvice q).b)
            (bankTrialC5CleanRun ring root S
              (bankTrialC5Rounds ring root
                (compileAdvice q).b bankTrialC5Trailing k ++
                bankTrialC5IncrementWord ring root
                  (bankTrialC5Trailing k))) := by
        rw [hconcat]
        exact bankTrialC5CleanRunAppend ring root S
          (bankTrialC5Rounds ring root
            (compileAdvice q).b bankTrialC5Trailing k ++
            bankTrialC5IncrementWord ring root
              (bankTrialC5Trailing k))
          (bankTrialC5ComparisonWord ring root
            (compileAdvice q).b)
      constructor
      · intro hstrict
        have hneq :
            bankTrialLiveBinaryValue
              (bankTrialC5CleanRun ring root S
                (bankTrialC5Rounds ring root
                  (compileAdvice q).b bankTrialC5Trailing k ++
                  bankTrialC5IncrementWord ring root
                    (bankTrialC5Trailing k))).bank ≠
                bankTrialLiveThetaBinary q := by
          rw [afterValue, htheta]
          omega
        rw [if_neg hneq] at hcomp
        obtain ⟨nextBegun, nextPhase, nextMode,
          nextTokens, nextBits, nextSuccess⟩ := hcomp
        have nextValue :
            bankTrialLiveBinaryValue
              (bankTrialLocalRun ring root
                (bankTrialC5ComparisonWord ring root
                  (compileAdvice q).b)
                (bankTrialC5CleanRun ring root S
                  (bankTrialC5Rounds ring root
                    (compileAdvice q).b bankTrialC5Trailing k ++
                    bankTrialC5IncrementWord ring root
                      (bankTrialC5Trailing k)))).bank =
                k + 1 := by
          exact (bankTrialC5BinaryFrame _ _ nextBits).trans
            afterValue
        have nextLocked :=
          bankTrialC5LockedArbitraryWord ring root hw
            (bankTrialC5ComparisonWord ring root
              (compileAdvice q).b)
            (bankTrialC5CleanRun ring root S
              (bankTrialC5Rounds ring root
                (compileAdvice q).b bankTrialC5Trailing k ++
                bankTrialC5IncrementWord ring root
                  (bankTrialC5Trailing k)))
            afterLocked
        rw [hround]
        exact ⟨nextBegun, nextPhase, nextMode,
          nextTokens, nextValue, nextSuccess, nextLocked⟩
      · intro hfinal
        have hmatch :
            bankTrialLiveBinaryValue
              (bankTrialC5CleanRun ring root S
                (bankTrialC5Rounds ring root
                  (compileAdvice q).b bankTrialC5Trailing k ++
                  bankTrialC5IncrementWord ring root
                    (bankTrialC5Trailing k))).bank =
                bankTrialLiveThetaBinary q := by
          rw [afterValue, htheta]
          exact hfinal
        rw [if_pos hmatch] at hcomp
        rw [hround]
        exact hcomp

/-- C3: every strict prefix of the K designated excursions ends
LIVE/ARMED, with zero worker tokens, value k, false success and
the inherited locked no-RESET certificate; the Kth reaches WON. -/
theorem bankTrialC5ConsecutiveArmedDecisions {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hq : 3 ≤ q)
    (hw : BankTrialLiveWindowNonalias n q)
    (hb : 2 ≤ (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S)
    (hcomparison : BankTrialC5ComparisonCorrect n q ring root) :
    (∀ k : Nat, k < (compileAdvice q).K →
      BankTrialC5ArmedAt q
        (bankTrialC5CleanRun ring root S
          (bankTrialC5Rounds ring root
            (compileAdvice q).b bankTrialC5Trailing k)) k) ∧
    (bankTrialC5CleanRun ring root S
      (bankTrialC5Rounds ring root
        (compileAdvice q).b bankTrialC5Trailing
        (compileAdvice q).K)).phase = .won := by
  constructor
  · intro k hk
    exact (bankTrialC5RoundsStatus ring root S
      hq hw hb hclean hcomparison k (by omega)).1 hk
  · exact (bankTrialC5RoundsStatus ring root S
      hq hw hb hclean hcomparison
      (compileAdvice q).K (by omega)).2 rfl

end L3
