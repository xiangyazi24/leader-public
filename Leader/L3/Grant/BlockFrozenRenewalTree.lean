import Leader.L3.Grant.BlockFrozenRenewalSums

namespace L3

open Classical
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

set_option autoImplicit false
set_option Elab.async false

/-! Kernel-generic stopped-tree lemmas of the G13 chain (copied from the
private declarations of BankTrialRenewal.lean). -/

/-- Survival THROUGH W selected letters: the initial state and
every state at elapsed times 1,...,W are nonterminal. This is
strictly the late/no-stop outcome, not a CLEAN first stop. -/
def grantBlockFrozenRenewalColdNoStopThrough
    {X : Type} {n : Nat}
    (next : X → Fin n → X) (target : X → Prop) :
    Nat → X → List (Fin n) → Prop
  | 0, z, _ => ¬ target z
  | _ + 1, _, [] => False
  | w + 1, z, e :: tail =>
      ¬ target z ∧
        grantBlockFrozenRenewalColdNoStopThrough next target
          w (next z e) tail

/-- The actual first-stop mass without an outcome label, truncated
at elapsed W, on the ORIGINAL horizon T. -/
noncomputable def grantBlockFrozenColdStopUnitMass
    {X : Type} {n : Nat}
    (next : X → Fin n → X)
    (stop : List (Fin n) → X → Bool)
    (T W : Nat) (pre : List (Fin n)) (z : X) : Nat :=
  ((Prob.firstStoppedPrefixes next stop T pre z).map
    (fun cut => if cut.length ≤ W then
      n ^ (T - cut.length) else 0)).sum

/-- Companion no-stop mass uses the censored prefix predicate.
The explicit length condition is important at arbitrary short tapes. -/
noncomputable def grantBlockFrozenColdNoStopUnitMass
    {X : Type} {n : Nat}
    (next : X → Fin n → X) (target : X → Prop)
    (z : X) (T W : Nat) : Nat :=
  Prob.scheduleSum n T (fun word =>
    if W ≤ word.length ∧
      grantBlockFrozenRenewalColdNoStopThrough next target W z word
    then 1 else 0)

/-- Finite flatMap sum, not a Finset or an independent scheduler. -/
theorem grantBlockFrozenColdFlatMapSum
    {U V : Type} (xs : List U) (ys : U → List V)
    (f : V → Nat) :
    ((xs.flatMap ys).map f).sum =
      (xs.map (fun a => ((ys a).map f).sum)).sum := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp [ih]

theorem grantBlockFrozenColdStopUnitAtRoot
    {X : Type} {n : Nat}
    (next : X → Fin n → X)
    (stop : List (Fin n) → X → Bool)
    (T W : Nat) (pre : List (Fin n)) (z : X)
    (hs : stop pre z = true) :
    grantBlockFrozenColdStopUnitMass next stop T W pre z =
      n ^ T := by
  unfold grantBlockFrozenColdStopUnitMass
  cases T with
  | zero => simp [Prob.firstStoppedPrefixes, hs]
  | succ t => simp [Prob.firstStoppedPrefixes, hs]

theorem grantBlockFrozenColdStopUnitZeroOfNonstop
    {X : Type} {n : Nat}
    (next : X → Fin n → X)
    (stop : List (Fin n) → X → Bool)
    (T : Nat) (pre : List (Fin n)) (z : X)
    (hs : stop pre z = false) :
    grantBlockFrozenColdStopUnitMass next stop T 0 pre z = 0 := by
  unfold grantBlockFrozenColdStopUnitMass
  cases T with
  | zero =>
      simp [Prob.firstStoppedPrefixes, hs]
  | succ t =>
      simp only [Prob.firstStoppedPrefixes, hs,
        Bool.false_eq_true, if_false]
      rw [grantBlockFrozenColdFlatMapSum]
      simp only [List.map_ofFn, Function.comp_def]
      have hzero (e : Fin n) :
          (((Prob.firstStoppedPrefixes next stop t
            (pre ++ [e]) (next z e)).map (List.cons e)).map
              (fun cut => if cut.length ≤ 0 then
                n ^ ((t + 1) - cut.length) else 0)).sum = 0 := by
        simp only [List.map_map, Function.comp_def]
        have hf :
            (fun u : List (Fin n) =>
              if (e :: u).length ≤ 0 then
                n ^ ((t + 1) - (e :: u).length) else 0) =
            (fun _ => 0) := by
          funext u
          have hnot : ¬ (e :: u).length ≤ 0 := by simp
          simp only [if_neg hnot]
        rw [hf]
        induction Prob.firstStoppedPrefixes next stop t
            (pre ++ [e]) (next z e) with
        | nil => rfl
        | cons u us ih =>
            simp only [List.map_cons, List.sum_cons, ih,
              Nat.zero_add]
      rw [ofFn_sum_eq _ (fun _ : Fin n => 0) hzero]
      simp only [ofFn_sum_const, Nat.mul_zero]

/-- An additional consumed source letter shifts both the remaining
horizon and the cutoff by one, without changing the suffix mass. -/
theorem grantBlockFrozenColdStopUnitStep
    {X : Type} {n : Nat}
    (next : X → Fin n → X)
    (stop : List (Fin n) → X → Bool)
    (T W : Nat) (pre : List (Fin n)) (z : X)
    (hs : stop pre z = false) :
    grantBlockFrozenColdStopUnitMass next stop
        (T + 1) (W + 1) pre z =
      (List.ofFn (fun e : Fin n =>
        grantBlockFrozenColdStopUnitMass next stop T W
          (pre ++ [e]) (next z e))).sum := by
  unfold grantBlockFrozenColdStopUnitMass
  simp only [Prob.firstStoppedPrefixes, hs,
    Bool.false_eq_true, if_false]
  rw [grantBlockFrozenColdFlatMapSum]
  simp only [List.map_ofFn]
  apply ofFn_sum_eq
  intro e
  simp only [List.map_map, Function.comp_def]
  have hfun :
      (fun u : List (Fin n) =>
        if (e :: u).length ≤ W + 1 then
          n ^ ((T + 1) - (e :: u).length) else 0) =
      (fun u : List (Fin n) =>
        if u.length ≤ W then n ^ (T - u.length) else 0) := by
    funext u
    by_cases hu : u.length ≤ W
    · have hc : (e :: u).length ≤ W + 1 := by
        simp only [List.length_cons]
        omega
      simp only [if_pos hc, if_pos hu]
      have hsub :
          (T + 1) - (e :: u).length = T - u.length := by
        simp only [List.length_cons]
        omega
      rw [hsub]
    · have hc : ¬ (e :: u).length ≤ W + 1 := by
        simp only [List.length_cons]
        omega
      simp only [if_neg hc, if_neg hu]
  rw [hfun]

theorem grantBlockFrozenColdNoStopUnitAtRoot
    {X : Type} {n : Nat}
    (next : X → Fin n → X) (target : X → Prop)
    (z : X) (T W : Nat) (htarget : target z) :
    grantBlockFrozenColdNoStopUnitMass next target z T W = 0 := by
  unfold grantBlockFrozenColdNoStopUnitMass
  have hf :
      (fun word : List (Fin n) =>
        if W ≤ word.length ∧
          grantBlockFrozenRenewalColdNoStopThrough next target W z word
        then 1 else 0) =
      (fun _ : List (Fin n) => 0) := by
    funext word
    cases W with
    | zero =>
        simp [grantBlockFrozenRenewalColdNoStopThrough, htarget]
    | succ w =>
        cases word with
        | nil => simp [grantBlockFrozenRenewalColdNoStopThrough]
        | cons e tail =>
            simp [grantBlockFrozenRenewalColdNoStopThrough, htarget]
  rw [hf, bankTrialProbabilityScheduleSumConst]
  simp

theorem grantBlockFrozenColdNoStopUnitZeroWindow
    {X : Type} {n : Nat}
    (next : X → Fin n → X) (target : X → Prop)
    (z : X) (T : Nat) (hn : ¬ target z) :
    grantBlockFrozenColdNoStopUnitMass next target z T 0 =
      n ^ T := by
  unfold grantBlockFrozenColdNoStopUnitMass
  have hf :
      (fun word : List (Fin n) =>
        if 0 ≤ word.length ∧
          grantBlockFrozenRenewalColdNoStopThrough next target 0 z word
        then 1 else 0) =
      (fun _ : List (Fin n) => 1) := by
    funext word
    simp [grantBlockFrozenRenewalColdNoStopThrough, hn]
  rw [hf, bankTrialProbabilityScheduleSumConst]
  simp

theorem grantBlockFrozenColdNoStopUnitStep
    {X : Type} {n : Nat}
    (next : X → Fin n → X) (target : X → Prop)
    (z : X) (T W : Nat) (hn : ¬ target z) :
    grantBlockFrozenColdNoStopUnitMass next target z
        (T + 1) (W + 1) =
      (List.ofFn (fun e : Fin n =>
        grantBlockFrozenColdNoStopUnitMass next target
          (next z e) T W)).sum := by
  unfold grantBlockFrozenColdNoStopUnitMass
  rw [bankTrialProbabilityScheduleSumFirst]
  apply ofFn_sum_eq
  intro e
  apply congrArg (Prob.scheduleSum n T)
  funext tail
  have hlen :
      (W + 1 ≤ (e :: tail).length) ↔ W ≤ tail.length := by
    simp only [List.length_cons]
    omega
  have hno :
      grantBlockFrozenRenewalColdNoStopThrough next target
          (W + 1) z (e :: tail) ↔
        grantBlockFrozenRenewalColdNoStopThrough next target
          W (next z e) tail := by
    change (¬ target z ∧
        grantBlockFrozenRenewalColdNoStopThrough next target
          W (next z e) tail) ↔ _
    simp [hn]
  have heq :
      (W + 1 ≤ (e :: tail).length ∧
        grantBlockFrozenRenewalColdNoStopThrough next target
          (W + 1) z (e :: tail)) =
      (W ≤ tail.length ∧
        grantBlockFrozenRenewalColdNoStopThrough next target
          W (next z e) tail) := by
    apply propext
    exact and_congr hlen hno
  by_cases hl :
      W + 1 ≤ (e :: tail).length ∧
        grantBlockFrozenRenewalColdNoStopThrough next target
          (W + 1) z (e :: tail)
  · have hr :
        W ≤ tail.length ∧
          grantBlockFrozenRenewalColdNoStopThrough next target
            W (next z e) tail := Eq.mp heq hl
    simp only [if_pos hl, if_pos hr]
  · have hr :
        ¬ (W ≤ tail.length ∧
          grantBlockFrozenRenewalColdNoStopThrough next target
            W (next z e) tail) := by
      intro h
      exact hl (Eq.mp heq.symm h)
    simp only [if_neg hl, if_neg hr]

/-- Exact stopped-tree partition with an arbitrary sound Boolean
terminal test. Every original length-T tape either first stops
by W or survives through W. No absorbing-state assumption,
independence or defect suppression is used. -/
theorem grantBlockFrozenColdGenericPrefixPartition
    {X : Type} {n : Nat}
    (next : X → Fin n → X)
    (stop : List (Fin n) → X → Bool)
    (target : X → Prop)
    (hreflect : ∀ pre z, stop pre z = true ↔ target z) :
    ∀ (T W : Nat) (pre : List (Fin n)) (z : X),
      W ≤ T →
      grantBlockFrozenColdStopUnitMass next stop T W pre z +
        grantBlockFrozenColdNoStopUnitMass next target z T W =
          n ^ T := by
  intro T
  induction T with
  | zero =>
      intro W pre z hWT
      have hW : W = 0 := by omega
      subst W
      cases hs : stop pre z with
      | true =>
          have ht : target z := (hreflect pre z).mp hs
          rw [grantBlockFrozenColdStopUnitAtRoot next stop
              0 0 pre z hs,
            grantBlockFrozenColdNoStopUnitAtRoot next target z 0 0 ht]
          simp
      | false =>
          have ht : ¬ target z := by
            intro h
            have htrue := (hreflect pre z).mpr h
            rw [hs] at htrue
            cases htrue
          rw [grantBlockFrozenColdStopUnitZeroOfNonstop next stop
              0 pre z hs,
            grantBlockFrozenColdNoStopUnitZeroWindow next target z 0 ht]
          simp
  | succ T ih =>
      intro W pre z hWT
      cases W with
      | zero =>
          cases hs : stop pre z with
          | true =>
              have ht : target z := (hreflect pre z).mp hs
              rw [grantBlockFrozenColdStopUnitAtRoot next stop
                  (T + 1) 0 pre z hs,
                grantBlockFrozenColdNoStopUnitAtRoot next target z
                  (T + 1) 0 ht]
              simp
          | false =>
              have ht : ¬ target z := by
                intro h
                have htrue := (hreflect pre z).mpr h
                rw [hs] at htrue
                cases htrue
              rw [grantBlockFrozenColdStopUnitZeroOfNonstop next stop
                  (T + 1) pre z hs,
                grantBlockFrozenColdNoStopUnitZeroWindow next target z
                  (T + 1) ht]
              simp
      | succ W =>
          have hW : W ≤ T := by omega
          cases hs : stop pre z with
          | true =>
              have ht : target z := (hreflect pre z).mp hs
              rw [grantBlockFrozenColdStopUnitAtRoot next stop
                  (T + 1) (W + 1) pre z hs,
                grantBlockFrozenColdNoStopUnitAtRoot next target z
                  (T + 1) (W + 1) ht]
              simp
          | false =>
              have ht : ¬ target z := by
                intro h
                have htrue := (hreflect pre z).mpr h
                rw [hs] at htrue
                cases htrue
              rw [grantBlockFrozenColdStopUnitStep next stop
                T W pre z hs,
                grantBlockFrozenColdNoStopUnitStep next target
                  z T W ht]
              calc
                (List.ofFn (fun e : Fin n =>
                    grantBlockFrozenColdStopUnitMass next stop T W
                      (pre ++ [e]) (next z e))).sum +
                  (List.ofFn (fun e : Fin n =>
                    grantBlockFrozenColdNoStopUnitMass next target
                      (next z e) T W)).sum =
                  (List.ofFn (fun e : Fin n =>
                    grantBlockFrozenColdStopUnitMass next stop T W
                        (pre ++ [e]) (next z e) +
                      grantBlockFrozenColdNoStopUnitMass next target
                        (next z e) T W)).sum := by
                    rw [ofFn_sum_add]
                _ = (List.ofFn (fun _ : Fin n => n ^ T)).sum := by
                    apply ofFn_sum_eq
                    intro e
                    exact ih W (pre ++ [e]) (next z e) hW
                _ = n ^ (T + 1) := by
                    rw [ofFn_sum_const]
                    simp only [Nat.mul_one, Nat.pow_succ,
                      Nat.mul_comm]

/-- Early first-stop cylinders weighted by the elapsed prefix length. -/
noncomputable def grantBlockFrozenColdEarlyLengthMass
    {X : Type} {n : Nat}
    (next : X → Fin n → X)
    (stop : List (Fin n) → X → Bool)
    (T W : Nat) (pre : List (Fin n)) (z : X) : Nat :=
  ((Prob.firstStoppedPrefixes next stop T pre z).map
    (fun cut => if cut.length ≤ W then
      cut.length * n ^ (T - cut.length) else 0)).sum

theorem grantBlockFrozenColdEarlyLengthZero
    {X : Type} {n : Nat}
    (next : X → Fin n → X)
    (stop : List (Fin n) → X → Bool)
    (T : Nat) (pre : List (Fin n)) (z : X) :
    grantBlockFrozenColdEarlyLengthMass next stop T 0 pre z = 0 := by
  unfold grantBlockFrozenColdEarlyLengthMass
  have hf :
      (fun cut : List (Fin n) =>
        if cut.length ≤ 0 then
          cut.length * n ^ (T - cut.length) else 0) =
      (fun _ : List (Fin n) => 0) := by
    funext cut
    cases cut with
    | nil => simp
    | cons e tail => simp
  rw [hf]
  induction Prob.firstStoppedPrefixes next stop T pre z with
  | nil => rfl
  | cons cut cuts ih =>
      simp only [List.map_cons, List.sum_cons, ih, Nat.zero_add]

theorem grantBlockFrozenColdEarlyLengthAtRoot
    {X : Type} {n : Nat}
    (next : X → Fin n → X)
    (stop : List (Fin n) → X → Bool)
    (T W : Nat) (pre : List (Fin n)) (z : X)
    (hs : stop pre z = true) :
    grantBlockFrozenColdEarlyLengthMass next stop T W pre z = 0 := by
  unfold grantBlockFrozenColdEarlyLengthMass
  cases T with
  | zero => simp [Prob.firstStoppedPrefixes, hs]
  | succ t => simp [Prob.firstStoppedPrefixes, hs]

theorem grantBlockFrozenColdEarlyLengthStep
    {X : Type} {n : Nat}
    (next : X → Fin n → X)
    (stop : List (Fin n) → X → Bool)
    (T W : Nat) (pre : List (Fin n)) (z : X)
    (hs : stop pre z = false) :
    grantBlockFrozenColdEarlyLengthMass next stop
        (T + 1) (W + 1) pre z =
      (List.ofFn (fun e : Fin n =>
        grantBlockFrozenColdStopUnitMass next stop T W
            (pre ++ [e]) (next z e) +
          grantBlockFrozenColdEarlyLengthMass next stop T W
            (pre ++ [e]) (next z e))).sum := by
  unfold grantBlockFrozenColdEarlyLengthMass
  simp only [Prob.firstStoppedPrefixes, hs,
    Bool.false_eq_true, if_false]
  rw [grantBlockFrozenColdFlatMapSum]
  simp only [List.map_ofFn, Function.comp_def]
  apply ofFn_sum_eq
  intro e
  have hpoint (u : List (Fin n)) :
      (if (e :: u).length ≤ W + 1 then
        (e :: u).length *
          n ^ ((T + 1) - (e :: u).length)
       else 0) =
      (if u.length ≤ W then n ^ (T - u.length) else 0) +
      (if u.length ≤ W then
        u.length * n ^ (T - u.length) else 0) := by
    by_cases hu : u.length ≤ W
    · have hc : (e :: u).length ≤ W + 1 := by
        simp only [List.length_cons]
        omega
      have hsub :
          (T + 1) - (e :: u).length = T - u.length := by
        simp only [List.length_cons]
        omega
      simp only [List.length_cons, if_pos hu]
      split
      · have hrem :
            T + 1 - (1 + u.length) = T - u.length := by omega
        have hremAlt :
            T + 1 - (u.length + 1) = T - u.length := by omega
        first
        | rw [hrem]
        | rw [hremAlt]
        simp only [Nat.add_mul, Nat.one_mul]
        omega
      · omega
    · have hc : ¬ (e :: u).length ≤ W + 1 := by
        simp only [List.length_cons]
        omega
      simp only [if_neg hc, if_neg hu, Nat.zero_add]
  calc
    (((Prob.firstStoppedPrefixes next stop T
        (pre ++ [e]) (next z e)).map (List.cons e)).map
        (fun cut => if cut.length ≤ W + 1 then
          cut.length * n ^ ((T + 1) - cut.length) else 0)).sum =
      ((Prob.firstStoppedPrefixes next stop T
        (pre ++ [e]) (next z e)).map
        (fun u =>
          (if u.length ≤ W then n ^ (T - u.length) else 0) +
          (if u.length ≤ W then
            u.length * n ^ (T - u.length) else 0))).sum := by
          simp only [List.map_map, Function.comp_def]
          apply congrArg List.sum
          apply List.map_congr_left
          intro u _
          exact hpoint u
    _ = grantBlockFrozenColdStopUnitMass next stop T W
          (pre ++ [e]) (next z e) +
        grantBlockFrozenColdEarlyLengthMass next stop T W
          (pre ++ [e]) (next z e) := by
          rw [grantBlockFrozenRenewalNatMapSumAdd]
          rfl

/-- Algebra with opaque Nat arguments, avoiding large-power omega. -/
theorem grantBlockFrozenColdOneServiceCostArithmetic
    (E U L C N W : Nat)
    (hpartition : U + L = N)
    (htail : E + W * L ≤ C) :
    (U + E) + (W + 1) * L ≤ N + C := by
  have hstep : (W + 1) * L = W * L + L := by
    rw [Nat.add_mul, Nat.one_mul]
  rw [hstep]
  omega

/-- The generic censored first-hit theorem: early cut-length mass
plus W times late/no-stop mass is ONE first-hit cost numerator. -/
theorem grantBlockFrozenColdJointFirstHitCost
    {X : Type} {n : Nat}
    (next : X → Fin n → X)
    (stop : List (Fin n) → X → Bool)
    (target : X → Prop)
    (hreflect : ∀ pre z, stop pre z = true ↔ target z) :
    ∀ (T W : Nat) (pre : List (Fin n)) (z : X),
      W ≤ T →
      grantBlockFrozenColdEarlyLengthMass next stop T W pre z +
        W * grantBlockFrozenColdNoStopUnitMass next target z T W ≤
      costNumerator next target z T := by
  intro T
  induction T with
  | zero =>
      intro W pre z hW
      have hzero : W = 0 := by omega
      subst W
      rw [grantBlockFrozenColdEarlyLengthZero]
      simp
  | succ T ih =>
      intro W pre z hW
      cases W with
      | zero =>
          rw [grantBlockFrozenColdEarlyLengthZero]
          simp
      | succ W =>
          have hsmall : W ≤ T := by omega
          by_cases ht : target z
          · have hs : stop pre z = true :=
              (hreflect pre z).mpr ht
            rw [grantBlockFrozenColdEarlyLengthAtRoot next stop
                (T + 1) (W + 1) pre z hs,
              grantBlockFrozenColdNoStopUnitAtRoot next target
                z (T + 1) (W + 1) ht,
              costNumerator_terminal next target z ht (T + 1)]
            simp
          · have hs : stop pre z = false := by
              cases hb : stop pre z with
              | false => rfl
              | true =>
                  exact False.elim (ht ((hreflect pre z).mp hb))
            rw [grantBlockFrozenColdEarlyLengthStep next stop
                T W pre z hs,
              grantBlockFrozenColdNoStopUnitStep next target
                z T W ht,
              costNumerator_succ next target z ht T]
            have hchild (e : Fin n) :
                grantBlockFrozenColdEarlyLengthMass next stop T W
                    (pre ++ [e]) (next z e) +
                  W * grantBlockFrozenColdNoStopUnitMass next target
                    (next z e) T W ≤
                costNumerator next target (next z e) T :=
              ih W (pre ++ [e]) (next z e) hsmall
            have hpartition (e : Fin n) :
                grantBlockFrozenColdStopUnitMass next stop T W
                    (pre ++ [e]) (next z e) +
                  grantBlockFrozenColdNoStopUnitMass next target
                    (next z e) T W = n ^ T :=
              grantBlockFrozenColdGenericPrefixPartition
                next stop target hreflect
                T W (pre ++ [e]) (next z e) hsmall
            have hpoint (e : Fin n) :
                (grantBlockFrozenColdStopUnitMass next stop T W
                    (pre ++ [e]) (next z e) +
                  grantBlockFrozenColdEarlyLengthMass next stop T W
                    (pre ++ [e]) (next z e)) +
                  (W + 1) *
                    grantBlockFrozenColdNoStopUnitMass next target
                      (next z e) T W ≤
                n ^ T +
                  costNumerator next target (next z e) T :=
              grantBlockFrozenColdOneServiceCostArithmetic
                (grantBlockFrozenColdEarlyLengthMass next stop T W
                  (pre ++ [e]) (next z e))
                (grantBlockFrozenColdStopUnitMass next stop T W
                  (pre ++ [e]) (next z e))
                (grantBlockFrozenColdNoStopUnitMass next target
                  (next z e) T W)
                (costNumerator next target (next z e) T)
                (n ^ T) W (hpartition e) (hchild e)
            have hsum := ofFn_sum_le
              (fun e : Fin n =>
                (grantBlockFrozenColdStopUnitMass next stop T W
                    (pre ++ [e]) (next z e) +
                  grantBlockFrozenColdEarlyLengthMass next stop T W
                    (pre ++ [e]) (next z e)) +
                  (W + 1) *
                    grantBlockFrozenColdNoStopUnitMass next target
                      (next z e) T W)
              (fun e : Fin n =>
                n ^ T + costNumerator next target (next z e) T)
              hpoint
            rw [ofFn_sum_add, ofFn_sum_add, ofFn_sum_mul_left,
              ofFn_sum_add, ofFn_sum_const, Nat.add_assoc] at hsum
            rw [ofFn_sum_add, Nat.pow_succ, Nat.mul_comm (n ^ T) n,
              Nat.add_assoc]
            exact hsum

/-- Finite-list arithmetic: a length charge and a scalar unit
charge are summed without a Finset. -/
theorem grantBlockFrozenColdListBudget
    {α : Type} (xs : List α) (a b c : α → Nat) (g : Nat)
    (h : ∀ z, z ∈ xs → a z ≤ b z + g * c z) :
    (xs.map a).sum ≤
      (xs.map b).sum + g * (xs.map c).sum := by
  induction xs with
  | nil =>
      simp
  | cons z zs ih =>
      have hz : a z ≤ b z + g * c z := h z (by simp)
      have ht : ∀ u, u ∈ zs → a u ≤ b u + g * c u := by
        intro u hu
        exact h u (by simp [hu])
      have hs := ih ht
      simp only [List.map_cons, List.sum_cons, Nat.mul_add]
      omega

/-- Pure arithmetic: the same c pays masked early length AND late
censored time. Products in this lemma are opaque natural numbers. -/
theorem grantBlockFrozenColdJointIndexArithmetic
    (P M E N g W Z c : Nat)
    (hclean : P * M ≤ E + N * g)
    (hjoint : E + W * Z ≤ N * c) :
    P * M + W * Z ≤ N * (c + g) := by
  have ha := Nat.add_le_add_right hclean (W * Z)
  have hb := Nat.add_le_add_right hjoint (N * g)
  rw [Nat.mul_add]
  omega

/-- A pointwise first-stop inequality lifts to the original
scheduler word, WITHOUT independence of prefix and outcome. -/
theorem grantBlockFrozenRenewalColdStoppedWeightedWord
    {X : Type} {n : Nat}
    (next : X → Fin n → X)
    (stop : List (Fin n) → X → Bool)
    (f g c : List (Fin n) → X → List (Fin n) → Nat)
    (W : Nat)
    (hrow : ∀ cut z suffix,
      W * f cut z suffix ≤ W * g cut z suffix +
        c cut z suffix) :
    ∀ (T : Nat) (pre : List (Fin n)) (z : X)
      (word : List (Fin n)),
      W * bankTrialSuccessNatStoppedWord next stop
        (fun cut z _ suffix => f cut z suffix) T pre z word ≤
      W * bankTrialSuccessNatStoppedWord next stop
        (fun cut z _ suffix => g cut z suffix) T pre z word +
      bankTrialSuccessNatStoppedWord next stop
        (fun cut z _ suffix => c cut z suffix) T pre z word := by
  intro T pre z word
  induction word generalizing T pre z with
  | nil =>
      cases hs : stop pre z with
      | true =>
          simpa [bankTrialSuccessNatStoppedWord, hs] using
            (hrow pre z [])
      | false =>
          simp [bankTrialSuccessNatStoppedWord, hs]
  | cons e tail ih =>
      cases hs : stop pre z with
      | true =>
          simpa [bankTrialSuccessNatStoppedWord, hs] using
            (hrow pre z (e :: tail))
      | false =>
          simp only [bankTrialSuccessNatStoppedWord, hs,
            Bool.false_eq_true, if_false]
          exact ih (T - 1) (pre ++ [e]) (next z e)

/-- Original Fin n schedule-sum lifting of the stopped-word bound. -/
theorem grantBlockFrozenRenewalColdStoppedWeightedSchedule
    {X : Type} {n : Nat}
    (next : X → Fin n → X)
    (stop : List (Fin n) → X → Bool)
    (f g c : List (Fin n) → X → List (Fin n) → Nat)
    (W T : Nat) (x : X)
    (hrow : ∀ cut z suffix,
      W * f cut z suffix ≤ W * g cut z suffix +
        c cut z suffix) :
    W * Prob.scheduleSum n T (fun word =>
      bankTrialSuccessNatStoppedWord next stop
        (fun cut z _ suffix => f cut z suffix) T [] x word) ≤
    W * Prob.scheduleSum n T (fun word =>
      bankTrialSuccessNatStoppedWord next stop
        (fun cut z _ suffix => g cut z suffix) T [] x word) +
    Prob.scheduleSum n T (fun word =>
      bankTrialSuccessNatStoppedWord next stop
        (fun cut z _ suffix => c cut z suffix) T [] x word) := by
  calc
    W * Prob.scheduleSum n T (fun word =>
        bankTrialSuccessNatStoppedWord next stop
          (fun cut z _ suffix => f cut z suffix) T [] x word) =
      Prob.scheduleSum n T (fun word =>
        W * bankTrialSuccessNatStoppedWord next stop
          (fun cut z _ suffix => f cut z suffix) T [] x word) :=
        (bankTrialSuccessScheduleSumScale n T W _).symm
    _ ≤ Prob.scheduleSum n T (fun word =>
        W * bankTrialSuccessNatStoppedWord next stop
          (fun cut z _ suffix => g cut z suffix) T [] x word +
        bankTrialSuccessNatStoppedWord next stop
          (fun cut z _ suffix => c cut z suffix) T [] x word) := by
        apply bankTrialProbabilityScheduleSumMono n T
        intro word
        exact grantBlockFrozenRenewalColdStoppedWeightedWord
          next stop f g c W hrow T [] x word
    _ = W * Prob.scheduleSum n T (fun word =>
        bankTrialSuccessNatStoppedWord next stop
          (fun cut z _ suffix => g cut z suffix) T [] x word) +
      Prob.scheduleSum n T (fun word =>
        bankTrialSuccessNatStoppedWord next stop
          (fun cut z _ suffix => c cut z suffix) T [] x word) := by
        rw [bankTrialC5ScheduleSumAdd,
          bankTrialSuccessScheduleSumScale]

/-- Stage sums respect pointwise equality restricted to j < H. -/
theorem grantBlockFrozenColdStageIndexCongr
    (f g : Nat → Nat) :
    ∀ H : Nat, (∀ j, j < H → f j = g j) →
      bankTrialSuccessStageIndexSum f H =
      bankTrialSuccessStageIndexSum g H := by
  intro H
  induction H with
  | zero =>
      intro _
      rfl
  | succ k ih =>
      intro h
      change bankTrialSuccessStageIndexSum f k + f k =
        bankTrialSuccessStageIndexSum g k + g k
      rw [ih (fun j hj => h j (by omega)), h k (by omega)]

theorem grantBlockFrozenColdStageListExchange
    {α : Type} (xs : List α) (F : Nat → α → Nat) :
    ∀ H : Nat,
      (xs.map (fun z =>
        bankTrialSuccessStageIndexSum (fun j => F j z) H)).sum =
      bankTrialSuccessStageIndexSum
        (fun j => (xs.map (F j)).sum) H := by
  intro H
  induction H with
  | zero =>
      change (xs.map (fun _ => 0)).sum = 0
      induction xs with
      | nil =>
          rfl
      | cons z zs ih =>
          simp only [List.map_cons, List.sum_cons, ih, Nat.zero_add]
  | succ k ih =>
      change
        (xs.map (fun z =>
          bankTrialSuccessStageIndexSum
              (fun j => F j z) k + F k z)).sum =
        bankTrialSuccessStageIndexSum
          (fun j => (xs.map (F j)).sum) k +
          (xs.map (F k)).sum
      rw [grantBlockFrozenRenewalNatMapSumAdd]
      exact congrArg
        (fun v => v + (xs.map (F k)).sum) ih

theorem grantBlockFrozenColdStageAdd
    (f g : Nat → Nat) :
    ∀ H : Nat,
      bankTrialSuccessStageIndexSum
        (fun j => f j + g j) H =
      bankTrialSuccessStageIndexSum f H +
        bankTrialSuccessStageIndexSum g H := by
  intro H
  induction H with
  | zero =>
      rfl
  | succ k ih =>
      change bankTrialSuccessStageIndexSum
          (fun j => f j + g j) k + (f k + g k) =
        (bankTrialSuccessStageIndexSum f k + f k) +
          (bankTrialSuccessStageIndexSum g k + g k)
      rw [ih]
      omega

/-- Additive stage sum, with the cold length multiplied ONLY by
the successful-index event. -/
theorem grantBlockFrozenColdMaskedStageSum
    (cold : Nat) (f g : Nat → Nat) :
    ∀ H : Nat,
      bankTrialSuccessStageIndexSum
        (fun j => cold * f j + g j) H =
      cold * bankTrialSuccessStageIndexSum f H +
        bankTrialSuccessStageIndexSum g H := by
  intro H
  induction H with
  | zero =>
      rfl
  | succ k ih =>
      change bankTrialSuccessStageIndexSum
          (fun j => cold * f j + g j) k +
            (cold * f k + g k) =
        cold * (bankTrialSuccessStageIndexSum f k + f k) +
          (bankTrialSuccessStageIndexSum g k + g k)
      rw [ih, Nat.mul_add]
      omega

/-- Entire remaining L1 combination reduces to six opaque Nat
hypotheses, including a ONE-unit GRANT window and a joint
late-plus-masked-CLEAN expense. This lemma has no theorem leaf. -/
theorem grantBlockFrozenColdWindowCompositionArithmetic
    (W P N den sumCoeff clean grant defect late
      cleanPattern proxy maskedCost charge H : Nat)
    (hpartition : N = clean + grant + defect + late)
    (hmass : clean * sumCoeff ≤ den * cleanPattern)
    (hgeom : sumCoeff ≤ den)
    (hlate : P * sumCoeff ≤ den * H)
    (hwindow :
      W * (cleanPattern + grant) ≤ W * proxy + maskedCost)
    (hcost :
      P * maskedCost + H * (W * late) ≤ N * charge) :
    W * P * N * sumCoeff ≤
      den * (W * P * (proxy + defect) + N * charge) := by
  have ha := Nat.mul_le_mul_left (W * P) hmass
  have hb := Nat.mul_le_mul_left (W * P)
    (Nat.mul_le_mul_left (grant + defect) hgeom)
  have hc := Nat.mul_le_mul_left (W * late) hlate
  have hfirst :
      W * P * N * sumCoeff ≤
      den * (W * P * (cleanPattern + grant + defect) +
        H * (W * late)) := by
    calc
      W * P * N * sumCoeff =
        W * P * (clean * sumCoeff) +
          W * P * ((grant + defect) * sumCoeff) +
          (W * late) * (P * sumCoeff) := by
            rw [hpartition]
            simp only [Nat.mul_add, Nat.add_mul,
              Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm,
              Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
      _ ≤ W * P * (den * cleanPattern) +
            W * P * ((grant + defect) * den) +
            (W * late) * (den * H) :=
              Nat.add_le_add (Nat.add_le_add ha hb) hc
      _ = den *
          (W * P * (cleanPattern + grant + defect) +
            H * (W * late)) := by
              simp only [Nat.mul_add, Nat.add_mul,
                Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm,
                Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  have hw := Nat.mul_le_mul_left P hwindow
  have hsecond :
      W * P * (cleanPattern + grant + defect) +
          H * (W * late) ≤
      W * P * (proxy + defect) +
          (P * maskedCost + H * (W * late)) := by
    calc
      W * P * (cleanPattern + grant + defect) +
          H * (W * late) =
        P * (W * (cleanPattern + grant)) +
          W * P * defect + H * (W * late) := by
            simp only [Nat.mul_add, Nat.add_mul,
              Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm,
              Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
      _ ≤ P * (W * proxy + maskedCost) +
            W * P * defect + H * (W * late) :=
              Nat.add_le_add_right
                (Nat.add_le_add_right hw (W * P * defect))
                (H * (W * late))
      _ = W * P * (proxy + defect) +
            (P * maskedCost + H * (W * late)) := by
              simp only [Nat.mul_add, Nat.add_mul,
                Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm,
                Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  have hthird :
      W * P * (cleanPattern + grant + defect) +
          H * (W * late) ≤
      W * P * (proxy + defect) + N * charge :=
    Nat.le_trans hsecond
      (Nat.add_le_add_left hcost _)
  exact Nat.le_trans hfirst
    (Nat.mul_le_mul_left den hthird)

theorem grantBlockFrozenColdScheduleZero (n T : Nat) :
    Prob.scheduleSum n T (fun _ => 0) = 0 := by
  simpa only [Nat.mul_zero] using
    bankTrialProbabilityScheduleSumConst n T 0

theorem grantBlockFrozenColdScheduleOne (n T : Nat) :
    Prob.scheduleSum n T (fun _ => 1) = n ^ T := by
  simpa only [Nat.mul_one] using
    bankTrialProbabilityScheduleSumConst n T 1

/-- Distribute a pointwise cutwise reward into its indexed
CLEAN and one-time terminal grant parts on a finite list. -/
theorem grantBlockFrozenColdListRewardConvolution
    {α : Type} (xs : List α)
    (f g : α → Nat) (A : Nat → α → Nat) (H : Nat)
    (h : ∀ z, z ∈ xs →
      f z = bankTrialSuccessStageIndexSum
        (fun j => A j z) H + g z) :
    (xs.map f).sum =
      bankTrialSuccessStageIndexSum
        (fun j => (xs.map (A j)).sum) H +
      (xs.map g).sum := by
  calc
    (xs.map f).sum =
      (xs.map (fun z =>
        bankTrialSuccessStageIndexSum
          (fun j => A j z) H + g z)).sum := by
        apply congrArg List.sum
        apply List.map_congr_left
        intro z hz
        exact h z hz
    _ = (xs.map (fun z =>
          bankTrialSuccessStageIndexSum
            (fun j => A j z) H)).sum + (xs.map g).sum :=
          grantBlockFrozenRenewalNatMapSumAdd _ _ _
    _ = _ := congrArg
      (fun v => v + (xs.map g).sum)
      (grantBlockFrozenColdStageListExchange xs A H)

theorem grantBlockFrozenColdListMaskedConvolution
    {α : Type} (xs : List α)
    (f : α → Nat) (A : Nat → α → Nat) (H : Nat)
    (h : ∀ z, z ∈ xs →
      f z = bankTrialSuccessStageIndexSum (fun j => A j z) H) :
    (xs.map f).sum =
      bankTrialSuccessStageIndexSum
        (fun j => (xs.map (A j)).sum) H := by
  calc
    (xs.map f).sum =
      (xs.map (fun z =>
        bankTrialSuccessStageIndexSum (fun j => A j z) H)).sum := by
        apply congrArg List.sum
        apply List.map_congr_left
        intro z hz
        exact h z hz
    _ = _ := grantBlockFrozenColdStageListExchange xs A H

def grantBlockFrozenColdLowerBase (n q L : Nat) : Nat :=
  1024 * (L * 2 ^ (compileAdvice q).K - L -
    2 ^ (compileAdvice q).K *
      ((8 * (compileAdvice q).b + 12) * n))

def grantBlockFrozenColdDenominatorBase (q L : Nat) : Nat :=
  1024 * (L * 2 ^ (compileAdvice q).K)

def grantBlockFrozenColdCoefficient
    (n q L H j : Nat) : Nat :=
  (grantBlockFrozenColdLowerBase n q L) ^ j * (1023 * L) *
    (grantBlockFrozenColdDenominatorBase q L) ^ (H - (j + 1))


theorem grantBlockFrozenRenewalPatternOneHot {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (L H : Nat) (word : List (Fin n)) :
    bankTrialSuccessStageIndexSum (fun j =>
      Prob.indicator (bankTrialRenewalPattern ring root S L j word)) H ≤
      1 := by
  have hstage (j : Nat)
      (hj : bankTrialRenewalPattern ring root S L j word = true) :
      true = true ∧
        j = (bankTrialRenewalRun ring root S word).failures.length := by
    have hp :
        (bankTrialRenewalRun ring root S word).observer.phase = .won ∧
        (bankTrialRenewalRun ring root S word).failures.length = j ∧
        (bankTrialRenewalRun ring root S word).failures.all
          (fun age => decide (age ≤ L)) = true ∧
        (bankTrialRenewalRun ring root S word).age ≤ L := by
      simpa only [bankTrialRenewalPattern, decide_eq_true_eq] using hj
    exact ⟨rfl, hp.2.1.symm⟩
  have hbound := bankTrialSuccessStageIndexSumIndicatorBound true
    (bankTrialRenewalRun ring root S word).failures.length H
    (fun j => bankTrialRenewalPattern ring root S L j word) hstage
  change bankTrialSuccessStageIndexSum (fun j =>
    Prob.indicator (bankTrialRenewalPattern ring root S L j word)) H ≤
    1 at hbound
  exact hbound

/-- A finite list decomposes into three named outcome sums if each
element has exactly one of those outcomes. Arithmetic is over
opaque naturals; no protocol powers are exposed to omega. -/
theorem grantBlockFrozenColdSumThree {α : Type}
    (xs : List α) (a b c total : α → Nat)
    (h : ∀ z, z ∈ xs →
      total z = a z + b z + c z) :
    (xs.map total).sum =
      (xs.map a).sum + (xs.map b).sum +
        (xs.map c).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      have hx := h x (by simp)
      have ht : ∀ z, z ∈ xs →
          total z = a z + b z + c z := by
        intro z hz
        exact h z (by simp [hz])
      have hsum := ih ht
      simp only [List.map_cons, List.sum_cons]
      rw [hx, hsum]
      omega

/-- Scalar inequalities over a finite list sum without Finset.
Both factors may be large symbolic naturals. -/
theorem grantBlockFrozenRenewalColdListMulSum
    {α : Type} (A B : α → Nat) (p q : Nat) :
    ∀ xs : List α,
      (∀ a, a ∈ xs → p * A a ≤ q * B a) →
      p * (xs.map A).sum ≤ q * (xs.map B).sum := by
  intro xs
  induction xs with
  | nil =>
      intro _
      simp
  | cons a xs ih =>
      intro h
      have ha : p * A a ≤ q * B a :=
        h a (by simp)
      have ht : ∀ b, b ∈ xs →
          p * A b ≤ q * B b := by
        intro b hb
        exact h b (by simp [hb])
      have hs := ih ht
      simpa only [List.map_cons, List.sum_cons, Nat.mul_add] using
        (Nat.add_le_add ha hs)

end L3
#print axioms L3.grantBlockFrozenColdGenericPrefixPartition
#print axioms L3.grantBlockFrozenColdJointFirstHitCost
#print axioms L3.grantBlockFrozenColdWindowCompositionArithmetic
