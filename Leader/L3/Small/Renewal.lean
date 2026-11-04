import Leader.L3.Headline.Renewal

/-!
SMALL renewal on the actual reference.

The fresh SMALL event is renewalSmallWin: K outgoing services before
the first incoming reset at the newly allocated root. Its scheduler
mass and rarity proof are deferred to a later round.

This file retains the deterministic two-port sum and the finite-advice
numerical certificate. Retry-to-origin coverage and the own-reference
generated-target clock remain separate obligations.
-/

namespace L3.SmallRenewal

open L3
open L3.HeadlineRenewal
open Classical
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

set_option autoImplicit false
set_option Elab.async false

/-! OLD SMALL cut and birth record. -/

/-- A genuine suppressed SMALL success has an OLD seen source
and an OLD physical SMALL success, not a newly written counter. -/
theorem smallOldCutDetector {n : Nat}
    (ring : DirectedRing n)
    (r : RenewalSmallReference n) (e : Fin n)
    (hcut : renewalSmallCut ring r.1 r.2 e = true) :
    r.2 e = true ∧
      (smallPair (r.1 e) (r.1 (ring.rightNeighbor e))
        (compileAdvice (ceilLogTwo n)).K).2.2 = true := by
  unfold renewalSmallCut at hcut
  simp only [Bool.and_eq_true] at hcut
  exact hcut

/-- Every selected service creates the recurring responder zero
origin even if the resulting reference state becomes terminal. -/
theorem smallResponderOriginMem {n : Nat}
    (ring : DirectedRing n)
    (r : RenewalSmallReference n) (e : Fin n) :
    ring.rightNeighbor e ∈ renewalSmallSpawn ring r e := by
  simp [renewalSmallSpawn]

/-- The optional source origin is created only on its one-time
invalid inherited-run sanitation row. -/
theorem smallExtraOriginMem {n : Nat}
    (ring : DirectedRing n)
    (r : RenewalSmallReference n) (e : Fin n)
    (he : renewalSmallExtra r.1 r.2 e = true) :
    e ∈ renewalSmallSpawn ring r e := by
  simp [renewalSmallSpawn, he]

/-- The SMALL carrier does not saturate on a genuine below-K
run increment in the production compiler branch. -/
theorem smallRunIncrementBelowCarrier
    (q : Nat) (hthree : 3 ≤ q)
    (hsmall : (compileAdvice q).useSmall = true)
    (j : Nat) (hj : j + 1 < (compileAdvice q).K) :
    j + 1 < kStar := by
  exact small_run_succ_lt q hthree hsmall j hj

/-! The two literal incident edges, without a third reset service. -/

private theorem smallRightAfterLeft {n : Nat}
    (ring : DirectedRing n) (i : Fin n) :
    ring.rightNeighbor (ring.leftNeighbor i) = i := by
  apply Fin.ext
  change (((i.val + n - 1) % n + 1) % n) = i.val
  rw [Nat.mod_add_mod]
  have heq : i.val + n - 1 + 1 = i.val + n := by omega
  rw [heq, Nat.add_mod]
  simp [Nat.mod_eq_of_lt i.isLt]

private theorem smallLeftAfterRight {n : Nat}
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

private theorem smallIncomingIffLeft {n : Nat}
    (ring : DirectedRing n) (root e : Fin n) :
    ring.rightNeighbor e = root ↔ e = ring.leftNeighbor root := by
  constructor
  · intro h
    calc
      e = ring.leftNeighbor (ring.rightNeighbor e) :=
        (smallLeftAfterRight ring e).symm
      _ = ring.leftNeighbor root := congrArg ring.leftNeighbor h
  · intro h
    rw [h]
    exact smallRightAfterLeft ring root

private theorem smallPortsDistinct {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (root : Fin n) :
    root ≠ ring.leftNeighbor root := by
  have h := Counter.resetRootPortDistinct
    ring (ring.leftNeighbor root) hn
  rw [smallRightAfterLeft] at h
  exact h

/-! Finite sum: one exceptional win edge and one loss edge. -/

private theorem smallSumSwapSingle :
    ∀ {m : Nat} (f g : Fin m → Nat) (i : Fin m),
      (∀ j, j ≠ i → f j = g j) →
      (List.ofFn f).sum + g i =
        (List.ofFn g).sum + f i := by
  intro m
  induction m with
  | zero =>
      intro f g i _
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
      · have hi0 : i.val ≠ 0 := by
          intro hzero
          apply hi
          exact Fin.ext hzero
        obtain ⟨j, hjv⟩ :
            ∃ j : Fin m, j.val = i.val - 1 :=
          ⟨⟨i.val - 1, by omega⟩, rfl⟩
        have hj : j.succ = i := by
          apply Fin.ext
          change j.val + 1 = i.val
          rw [hjv]
          omega
        have ht := ih
          (fun a : Fin m => f a.succ)
          (fun a : Fin m => g a.succ) j (by
            intro a ha
            apply h
            intro hz
            apply ha
            apply Fin.ext
            have hv := congrArg Fin.val hz
            have hv' := congrArg Fin.val hj
            simp at hv hv' ⊢
            omega)
        have hzero := h 0 (Ne.symm hi)
        simp only [hj] at ht
        omega

/-- 2C for the outgoing edge, zero for the incoming edge and
C for each unrelated edge have total exactly nC. -/
private theorem smallTwoPortSum {n : Nat}
    (a b : Fin n) (hab : a ≠ b) (C : Nat) :
    (List.ofFn (fun e : Fin n =>
      if e = a then 2 * C else if e = b then 0 else C)).sum =
        n * C := by
  have hfirst := smallSumSwapSingle
    (fun _ : Fin n => C)
    (fun e : Fin n => if e = a then 2 * C else C) a (by
      intro e he
      simp [he])
  have hsecond := smallSumSwapSingle
    (fun e : Fin n => if e = a then 2 * C else C)
    (fun e : Fin n =>
      if e = a then 2 * C else if e = b then 0 else C) b (by
      intro e he
      by_cases ha : e = a
      · simp [ha]
      · simp [ha, he])
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

/-! Exact integer SMALL margin and reserve. -/

/-- The real selected renewal ledger as a function of advice q,
to avoid carrying the population n through the finite certificate. -/
def smallReferenceRenewalAt (q : Nat) : Nat :=
  (if q ≤ 32 then headlineFiniteLedger q
   else headlineLargeLedger (ceilLogTwo q)).2.1

/-- Finite integer check for q=3..79, including the EXEC10
small s=6 and s=7 widths. No floating point estimates. -/
theorem smallReferenceNumericalCertificate (n : Nat)
    (hn : 5 ≤ n)
    (hsmall : (compileAdvice (ceilLogTwo n)).useSmall = true) :
    headlineReferenceRate (ceilLogTwo n) <
        2 ^ (compileAdvice (ceilLogTwo n)).kappa ∧
    headlineReferenceRate (ceilLogTwo n) *
        2 ^ (compileAdvice (ceilLogTwo n)).kappa *
        2 ^ ceilLogTwo n ≤
      ((2 ^ (compileAdvice (ceilLogTwo n)).kappa -
          headlineReferenceRate (ceilLogTwo n)) *
          2 ^ ceilLogTwo n - 1) * headlineRenewalRate n := by
  have hq : ceilLogTwo n < 80 := by
    have hs : decide (ceilLogTwo n ≤ qStar) = true := hsmall
    have hbound := of_decide_eq_true hs
    have hstar : qStar = 79 := rfl
    omega
  have hthree : 3 ≤ ceilLogTwo n :=
    ceilLogTwo_ge_three n hn
  have hfinite :
      ∀ i : Fin 80, 3 ≤ i.val →
        headlineReferenceRate i.val <
            2 ^ (compileAdvice i.val).kappa ∧
        headlineReferenceRate i.val *
            2 ^ (compileAdvice i.val).kappa *
            2 ^ i.val ≤
          ((2 ^ (compileAdvice i.val).kappa -
              headlineReferenceRate i.val) *
              2 ^ i.val - 1) *
            smallReferenceRenewalAt i.val := by
    decide +kernel
  have h := hfinite ⟨ceilLogTwo n, hq⟩ hthree
  change
    headlineReferenceRate (ceilLogTwo n) <
        2 ^ (compileAdvice (ceilLogTwo n)).kappa ∧
    headlineReferenceRate (ceilLogTwo n) *
        2 ^ (compileAdvice (ceilLogTwo n)).kappa *
        2 ^ ceilLogTwo n ≤
      ((2 ^ (compileAdvice (ceilLogTwo n)).kappa -
          headlineReferenceRate (ceilLogTwo n)) *
          2 ^ ceilLogTwo n - 1) *
        smallReferenceRenewalAt (ceilLogTwo n)
  exact h

end L3.SmallRenewal

/-!
Exact finite-word SMALL suffix mass.
The local scheduler-sum lemmas are reconstructed from the recursive
allSchedules enumeration; no FixedSpanRenewalPayload summation
theorem is invoked here.
-/

namespace L3.SmallRenewal

open L3
open L3.HeadlineRenewal
open Classical
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

/-! Rebuild the finite first-letter scheduler sum from its definition. -/

private theorem smallSumFlatMap {A B : Type}
    (xs : List A) (ys : A → List B) (f : B → Nat) :
    ((xs.flatMap ys).map f).sum =
      (xs.map (fun x => ((ys x).map f).sum)).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [ih]

private theorem smallSumSwap {A : Type} {n : Nat}
    (xs : List A) (f : A → Fin n → Nat) :
    (xs.map (fun x => (List.ofFn (f x)).sum)).sum =
      (List.ofFn (fun e => (xs.map (fun x => f x e)).sum)).sum := by
  induction xs with
  | nil => simp [ofFn_sum_const]
  | cons x xs ih =>
      simp only [List.map_cons, List.sum_cons, ih]
      rw [ofFn_sum_add]

private theorem smallScheduleSumZero (n : Nat)
    (f : List (Fin n) → Nat) :
    Prob.scheduleSum n 0 f = f [] := by
  change ((allSchedules n 0).map (fun u => f u.reverse)).sum = f []
  rfl

private theorem smallScheduleSumFirst (n T : Nat)
    (f : List (Fin n) → Nat) :
    Prob.scheduleSum n (T + 1) f =
      (List.ofFn (fun e : Fin n =>
        Prob.scheduleSum n T (fun w => f (e :: w)))).sum := by
  change ((allSchedules n (T + 1)).map
      (fun u => f u.reverse)).sum =
    (List.ofFn (fun e : Fin n =>
      ((allSchedules n T).map
        (fun u => f (e :: u.reverse))).sum)).sum
  simp only [allSchedules, smallSumFlatMap, List.map_ofFn,
    Function.comp_def, List.reverse_append, List.reverse_cons,
    List.reverse_nil, List.nil_append, List.singleton_append]
  exact smallSumSwap _ _

private theorem smallScheduleSumConst (n T c : Nat) :
    Prob.scheduleSum n T (fun _ => c) = n ^ T * c := by
  induction T with
  | zero =>
      rw [smallScheduleSumZero]
      simp
  | succ T ih =>
      rw [smallScheduleSumFirst]
      change (List.ofFn (fun _ : Fin n =>
          Prob.scheduleSum n T (fun _ => c))).sum =
        n ^ (T + 1) * c
      rw [ofFn_sum_const, ih, Nat.pow_succ]
      ac_rfl

/-! One newly created origin, measured on the original full-ring tape. -/

/-- The exact number of length-T scheduler words on which k
outgoing root services precede every incoming root reset. -/
def smallWinMass {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (k T : Nat) : Nat :=
  Prob.scheduleSum n T
    (fun word => Prob.indicator (renewalSmallWin ring root k word))

/-- With no outgoing services remaining, every word wins. -/
private theorem smallWinMassZero {n : Nat}
    (ring : DirectedRing n) (root : Fin n) (T : Nat) :
    smallWinMass ring root 0 T = n ^ T := by
  have hw : (fun word : List (Fin n) =>
      Prob.indicator (renewalSmallWin ring root 0 word)) =
      (fun _ => 1) := by
    funext word
    cases word <;> rfl
  unfold smallWinMass
  rw [hw]
  simpa only [Nat.mul_one] using smallScheduleSumConst n T 1

/-- First edge: outgoing decrements k; incoming fails; any
other edge stutters. Outgoing is tested before incoming. -/
private theorem smallWinMassSucc {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (k T : Nat) :
    smallWinMass ring root (k + 1) (T + 1) =
      (List.ofFn (fun e : Fin n =>
        if e = root then smallWinMass ring root k T
        else if ring.rightNeighbor e = root then 0
        else smallWinMass ring root (k + 1) T)).sum := by
  unfold smallWinMass
  rw [smallScheduleSumFirst]
  apply ofFn_sum_eq
  intro e
  by_cases he : e = root
  · simp [renewalSmallWin, he]
  · by_cases hi : ring.rightNeighbor e = root
    · have hzero :
          Prob.scheduleSum n T (fun _ : List (Fin n) => 0) = 0 := by
        rw [smallScheduleSumConst]
        simp
      simpa [renewalSmallWin, he, hi, Prob.indicator] using hzero
    · simp [renewalSmallWin, he, hi]

/-- The finite-horizon SMALL winning mass is at most 2^(-k)
of all original length-T ring words. -/
theorem smallWinMassBound {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (root : Fin n) :
    ∀ T k : Nat,
      2 ^ k * smallWinMass ring root k T ≤ n ^ T := by
  intro T
  induction T with
  | zero =>
      intro k
      cases k with
      | zero =>
          rw [smallWinMassZero]
          simp
      | succ k =>
          have hz : smallWinMass ring root (k + 1) 0 = 0 := by
            change Prob.scheduleSum n 0 (fun _ => 0) = 0
            rw [smallScheduleSumZero]
          rw [hz]
          simp
  | succ T ih =>
      intro k
      cases k with
      | zero =>
          rw [smallWinMassZero]
          simp
      | succ k =>
          have hports := smallPortsDistinct ring hn root
          have hpair :
              ∀ e : Fin n,
                2 ^ (k + 1) *
                  (if e = root then smallWinMass ring root k T
                   else if ring.rightNeighbor e = root then 0
                   else smallWinMass ring root (k + 1) T) ≤
                (if e = root then 2 * n ^ T
                 else if e = ring.leftNeighbor root then 0
                 else n ^ T) := by
            intro e
            by_cases he : e = root
            · simp only [if_pos he]
              calc
                2 ^ (k + 1) * smallWinMass ring root k T =
                    2 * (2 ^ k * smallWinMass ring root k T) := by
                      rw [Nat.pow_succ]
                      ac_rfl
                _ ≤ 2 * n ^ T := Nat.mul_le_mul_left 2 (ih k)
            · have hinc := smallIncomingIffLeft ring root e
              by_cases hl : e = ring.leftNeighbor root
              · have hi : ring.rightNeighbor e = root :=
                  hinc.mpr hl
                simp only [if_neg he, if_pos hi, if_pos hl, Nat.mul_zero,
                  Nat.le_refl]
              · have hi : ring.rightNeighbor e ≠ root := by
                  intro h
                  exact hl (hinc.mp h)
                simpa [he, hi, hl] using ih (k + 1)
          calc
            2 ^ (k + 1) * smallWinMass ring root (k + 1) (T + 1) =
                (List.ofFn (fun e : Fin n =>
                  2 ^ (k + 1) *
                    (if e = root then smallWinMass ring root k T
                     else if ring.rightNeighbor e = root then 0
                     else smallWinMass ring root (k + 1) T))).sum := by
                      rw [smallWinMassSucc]
                      exact (ofFn_sum_mul_left (2 ^ (k + 1)) _).symm
            _ ≤ (List.ofFn (fun e : Fin n =>
                  if e = root then 2 * n ^ T
                  else if e = ring.leftNeighbor root then 0
                  else n ^ T)).sum :=
                    ofFn_sum_le _ _ hpair
            _ = n * n ^ T :=
                  smallTwoPortSum root (ring.leftNeighbor root)
                    hports (n ^ T)
            _ = n ^ (T + 1) := by
                  rw [Nat.pow_succ]
                  exact Nat.mul_comm n (n ^ T)

/-- The missing SMALL suffix producer in HeadlineRenewal,
for every root and every finite original-clock horizon. -/
theorem smallReferenceSuffixBound {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n) :
    SmallReferenceSuffixBound ring := by
  intro root T
  change
    2 ^ (2 * ceilLogTwo n +
      (compileAdvice (ceilLogTwo n)).kappa) *
      smallWinMass ring root
        (compileAdvice (ceilLogTwo n)).K T ≤ n ^ T
  have htwo : 2 ≤ n := by omega
  have hbound := smallWinMassBound ring htwo root T
    (compileAdvice (ceilLogTwo n)).K
  have hK :
      (compileAdvice (ceilLogTwo n)).K =
        2 * ceilLogTwo n +
          (compileAdvice (ceilLogTwo n)).kappa := rfl
  rw [← hK]
  exact hbound

/-- The concrete SMALL origin rarity field (num=1). -/
theorem smallReferenceOriginRarity {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hsmall : (compileAdvice (ceilLogTwo n)).useSmall = true) :
    ReferenceOriginRarity ring
      (smallRootedReferenceData ring hsmall)
      (compileAdvice (ceilLogTwo n)).kappa := by
  intro r hstop e root hborn T
  change
    2 ^ (2 * ceilLogTwo n +
      (compileAdvice (ceilLogTwo n)).kappa) *
      Prob.scheduleSum n T
        (fun word => Prob.indicator
          (renewalSmallWin ring root
            (compileAdvice (ceilLogTwo n)).K word)) ≤
      1 * n ^ T
  simpa only [Nat.one_mul] using
    smallReferenceSuffixBound ring hn root T

end L3.SmallRenewal

/-!
Retry-first versus successful SMALL origin.

The only unproved source-history claim is SmallRunSourceWitness:
an OLD seen SMALL success must descend from a recorded zero origin
whose suffix contains its K outgoing wins before an incoming reset.
Everything else below is a finite-word reduction to this precise
claim, with the actual stopped reference and retry-first kernel.
-/

namespace L3.SmallRenewal

open L3
open L3.HeadlineRenewal
open Classical
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting
open PPL.Convergence.LDLocal (AttemptNode RetryKernel)

set_option autoImplicit false
set_option Elab.async false

/-- The reference after a finite physical edge prefix. -/
private def smallRefAfter {n : Nat} (ring : DirectedRing n) :
    RenewalSmallReference n → List (Fin n) → RenewalSmallReference n
  | r, [] => r
  | r, e :: w =>
      smallRefAfter ring (renewalSmallNext ring r e) w

/-- Stop was false at every cut through the given prefix,
including the cut at its end. -/
private def smallRefOpen {n : Nat} (ring : DirectedRing n) :
    RenewalSmallReference n → List (Fin n) → Prop
  | r, [] => ¬ renewalSmallStop ring r
  | r, e :: w =>
      ¬ renewalSmallStop ring r ∧
        smallRefOpen ring (renewalSmallNext ring r e) w

private theorem smallRefOpenPrefix {n : Nat}
    (ring : DirectedRing n) :
    ∀ (u v : List (Fin n)) (r : RenewalSmallReference n),
      smallRefOpen ring r (u ++ v) →
        smallRefOpen ring r u := by
  intro u
  induction u with
  | nil =>
      intro v r h
      cases v with
      | nil => exact h
      | cons e es => exact h.1
  | cons e es ih =>
      intro v r h
      exact ⟨h.1, ih v (renewalSmallNext ring r e) h.2⟩

/-- ONE OPEN SOURCE-ROW IMPLICATION, not an axiom or a theorem.

For an arbitrary legal initial SMALL Cartesian scratch, after
a target-free reference prefix, any OLD seen source whose SMALL
row succeeds must have a genuine preceding zero origin. That
origin is either the regular responder of an earlier edge or the
one-time invalid-source sanitation origin. Its actual intervening
edge suffix, including the current success service, contains K
outgoing edges before any incoming reset.

The witness explicitly records the earlier physical edge and the
exact reference state at which that origin was created. Nothing
about the future scheduler is assumed or conditioned on. -/
def SmallRunSourceWitness {n : Nat} (ring : DirectedRing n) : Prop :=
  ∀ (seed : RootedSeed ring) (u : List (Fin n)) (e : Fin n),
    smallRefOpen ring (renewalSmallStart ring seed) u →
    (smallRefAfter ring (renewalSmallStart ring seed) u).2 e = true →
    (smallPair
      ((smallRefAfter ring (renewalSmallStart ring seed) u).1 e)
      ((smallRefAfter ring (renewalSmallStart ring seed) u).1
        (ring.rightNeighbor e))
      (compileAdvice (ceilLogTwo n)).K).2.2 = true →
    ∃ (p : List (Fin n)) (f : Fin n) (tail : List (Fin n)),
      u = p ++ f :: tail ∧
      (e = ring.rightNeighbor f ∨
        (e = f ∧
          renewalSmallExtra
            (smallRefAfter ring (renewalSmallStart ring seed) p).1
            (smallRefAfter ring (renewalSmallStart ring seed) p).2
            f = true)) ∧
      renewalSmallWin ring e
        (compileAdvice (ceilLogTwo n)).K
        (tail ++ [e]) = true

/-- Once the K-head success event has occurred, arbitrary padding
does not invalidate it. -/
private theorem smallWinAppendTrue {n : Nat}
    (ring : DirectedRing n) (root : Fin n) :
    ∀ (u v : List (Fin n)) (k : Nat),
      renewalSmallWin ring root k u = true →
        renewalSmallWin ring root k (u ++ v) = true := by
  intro u
  induction u with
  | nil =>
      intro v k h
      cases k with
      | zero => cases v <;> rfl
      | succ k => cases h
  | cons e es ih =>
      intro v k h
      cases k with
      | zero => rfl
      | succ k =>
          by_cases he : e = root
          · simp only [List.cons_append, renewalSmallWin, if_pos he] at h ⊢
            exact ih v k h
          · by_cases hi : ring.rightNeighbor e = root
            · simp only [renewalSmallWin, if_neg he, if_pos hi] at h
              cases h
            · simp only [List.cons_append, renewalSmallWin, if_neg he,
                if_neg hi] at h ⊢
              exact ih v (k + 1) h

/-- A spawned member with a winning suffix contributes a positive
summand; other origins do not have to be disjoint or independent. -/
private theorem smallOriginListPositive {A : Type}
    (os : List A) (f : A → Bool) (a : A)
    (hmem : a ∈ os) (hwin : f a = true) :
    0 < (os.map (fun o => Prob.indicator (f o))).sum := by
  induction os with
  | nil => cases hmem
  | cons x xs ih =>
      rcases List.mem_cons.mp hmem with he | ht
      · subst x
        simp only [List.map_cons, List.sum_cons]
        have hh : Prob.indicator (f a) = 1 := by
          simp [Prob.indicator, hwin]
        omega
      · simp only [List.map_cons, List.sum_cons]
        have hh := ih ht
        omega

/-- If a live prefix contains an origin creation whose suffix
wins, the stopped successful-origin count of the whole word is
strictly positive. This is independent of the SMALL owner rows. -/
private theorem smallSuccessfulOrigin {n : Nat}
    (ring : DirectedRing n) (root : Fin n) :
    ∀ (u : List (Fin n)) (r : RenewalSmallReference n)
      (e : Fin n) (v : List (Fin n)),
      smallRefOpen ring r u →
      root ∈ renewalSmallSpawn ring (smallRefAfter ring r u) e →
      renewalSmallWin ring root
        (compileAdvice (ceilLogTwo n)).K v = true →
      0 < Prob.successfulOriginsWord
        (renewalSmallNext ring) (renewalSmallStop ring)
        (renewalSmallSpawn ring)
        (fun o w => renewalSmallWin ring o
          (compileAdvice (ceilLogTwo n)).K w)
        r (u ++ e :: v) := by
  intro u
  induction u with
  | nil =>
      intro r e v hopen hmem hwin
      have hh := smallOriginListPositive
        (renewalSmallSpawn ring r e)
        (fun o => renewalSmallWin ring o
          (compileAdvice (ceilLogTwo n)).K v)
        root hmem hwin
      change 0 < (if renewalSmallStop ring r then 0
        else ((renewalSmallSpawn ring r e).map
          (fun o => Prob.indicator (renewalSmallWin ring o
            (compileAdvice (ceilLogTwo n)).K v))).sum +
          Prob.successfulOriginsWord
            (renewalSmallNext ring) (renewalSmallStop ring)
            (renewalSmallSpawn ring)
            (fun o w => renewalSmallWin ring o
              (compileAdvice (ceilLogTwo n)).K w)
            (renewalSmallNext ring r e) v)
      rw [if_neg hopen]
      omega
  | cons f fs ih =>
      intro r e v hopen hmem hwin
      have hstop : ¬ renewalSmallStop ring r := hopen.1
      have htail :
          smallRefOpen ring (renewalSmallNext ring r f) fs :=
        hopen.2
      have hh := ih (renewalSmallNext ring r f) e v
        htail hmem hwin
      change 0 < (if renewalSmallStop ring r then 0
        else ((renewalSmallSpawn ring r f).map
          (fun o => Prob.indicator (renewalSmallWin ring o
            (compileAdvice (ceilLogTwo n)).K (fs ++ e :: v)))).sum +
          Prob.successfulOriginsWord
            (renewalSmallNext ring) (renewalSmallStop ring)
            (renewalSmallSpawn ring)
            (fun o w => renewalSmallWin ring o
              (compileAdvice (ceilLogTwo n)).K w)
            (renewalSmallNext ring r f) (fs ++ e :: v))
      rw [if_neg hstop]
      omega

/-- The concrete SMALL retry kernel, with only its existing proof memory. -/
private noncomputable def smallRetryKernel {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hsmall : (compileAdvice (ceilLogTwo n)).useSmall = true) :
    RetryKernel (RootedSeed ring × RenewalSmallMemory n)
      (RootedSeed ring) n :=
  referenceKernel ring hn (smallRootedReferenceData ring hsmall)

/-- A retry indicator is literally 0 or 1, not an arbitrary count. -/
private theorem smallRetryFirstLeOne {A Seed : Type} {n : Nat}
    (K : RetryKernel A Seed n) :
    ∀ (word : List (Fin n)) (z : AttemptNode A Seed),
      Prob.retryFirstWord K z word ≤ 1 := by
  intro word
  induction word with
  | nil =>
      intro z
      cases z <;> simp [Prob.retryFirstWord]
  | cons e es ih =>
      intro z
      cases z with
      | success => simp [Prob.retryFirstWord]
      | retry seed => simp [Prob.retryFirstWord]
      | active a =>
          change Prob.retryFirstWord K (K.step a e) es ≤ 1
          exact ih (K.step a e)

/-- The exact structural half of coverage. A retry-first event
has a first SMALL cut at some concrete service, with matching
physical/reference fields and a target-free earlier prefix. -/
private theorem smallRetryFirstHasCut {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hsmall : (compileAdvice (ceilLogTwo n)).useSmall = true) :
    ∀ (word : List (Fin n))
      (a : RootedSeed ring × RenewalSmallMemory n)
      (r : RenewalSmallReference n),
      r = (a.1.val, a.2) →
      ¬ renewalSmallStop ring r →
      Prob.retryFirstWord (smallRetryKernel ring hn hsmall)
        (.active a) word = 1 →
      ∃ (u : List (Fin n)) (e : Fin n) (v : List (Fin n)),
        word = u ++ e :: v ∧
        smallRefOpen ring r u ∧
        renewalSmallCut ring (smallRefAfter ring r u).1
          (smallRefAfter ring r u).2 e = true := by
  intro word
  induction word with
  | nil =>
      intro a r hre hnot hretry
      change (0 : Nat) = 1 at hretry
      cases hretry
  | cons e es ih =>
      intro a r hre hnot hretry
      change Prob.retryFirstWord
        (smallRetryKernel ring hn hsmall)
        ((smallRetryKernel ring hn hsmall).step a e) es = 1 at hretry
      cases hs : (smallRetryKernel ring hn hsmall).step a e with
      | success =>
          rw [hs] at hretry
          simp [Prob.retryFirstWord] at hretry
      | retry seed =>
          have hs' : rootedTrialStep ring hn
              (renewalSmallTrialAdvance ring)
              (renewalSmallTrialCut ring) a e = .retry seed := hs
          unfold rootedTrialStep at hs'
          split at hs'
          · cases hs'
          · rename_i hnext
            split at hs'
            · rename_i hcut
              have hc : renewalSmallCut ring r.1 r.2 e = true := by
                rw [hre]
                change renewalSmallTrialCut ring a e = true
                exact hcut
              exact ⟨[], e, es, rfl, hnot, hc⟩
            · cases hs'
      | active b =>
          rw [hs] at hretry
          have hs' : rootedTrialStep ring hn
              (renewalSmallTrialAdvance ring)
              (renewalSmallTrialCut ring) a e = .active b := hs
          unfold rootedTrialStep at hs'
          split at hs'
          · cases hs'
          · rename_i hnext
            split at hs'
            · cases hs'
            · rename_i hnocut
              cases hs'
              have hc : renewalSmallTrialCut ring a e = false := by
                cases htest : renewalSmallTrialCut ring a e with
                | false => rfl
                | true => exact False.elim (hnocut htest)
              have href :
                  renewalSmallNext ring r e =
                    ((rootedSuccessor ring hn a.1 e).val,
                      renewalSmallTrialAdvance ring a e) := by
                rw [hre]
                apply Prod.ext
                · exact renewalSmallPhysicalBeforeCut ring
                    (a.1.val, a.2) e hc
                · rfl
              have hstay :
                  ¬ renewalSmallStop ring
                    (renewalSmallNext ring r e) := by
                rw [href]
                exact hnext
              obtain ⟨u, f, v, hword, hopen, hcut⟩ :=
                ih (rootedSuccessor ring hn a.1 e,
                      renewalSmallTrialAdvance ring a e)
                  (renewalSmallNext ring r e)
                  href hstay hretry
              refine ⟨e :: u, f, v, ?_, ?_, ?_⟩
              · exact congrArg (List.cons e) hword
              · exact ⟨hnot, hopen⟩
              · exact hcut

/-- Conditional completion of ReferenceRetryCoverage. All
scheduler-word induction and stopped-origin accounting are
proved; only SmallRunSourceWitness remains as the exact local
source-history/lineage obligation. -/
theorem smallReferenceRetryCoverageOfSourceWitness {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hsmall : (compileAdvice (ceilLogTwo n)).useSmall = true)
    (hsource : SmallRunSourceWitness ring) :
    ReferenceRetryCoverage ring hn
      (smallRootedReferenceData ring hsmall) := by
  intro seed hnot word
  change Prob.retryFirstWord (smallRetryKernel ring hn hsmall)
      (.active (seed, renewalSmallInitialMemory ring seed)) word ≤
    Prob.originEventWord (renewalSmallNext ring) (renewalSmallStop ring)
      (renewalSmallSpawn ring)
      (fun o w => renewalSmallWin ring o
        (compileAdvice (ceilLogTwo n)).K w)
      (renewalSmallStart ring seed) word
  by_cases hz :
      Prob.retryFirstWord (smallRetryKernel ring hn hsmall)
        (.active (seed, renewalSmallInitialMemory ring seed)) word = 0
  · rw [hz]
    exact Nat.zero_le _
  · have hle :
        Prob.retryFirstWord (smallRetryKernel ring hn hsmall)
          (.active (seed, renewalSmallInitialMemory ring seed)) word ≤ 1 :=
      smallRetryFirstLeOne (smallRetryKernel ring hn hsmall)
        word _
    have hretry :
        Prob.retryFirstWord (smallRetryKernel ring hn hsmall)
          (.active (seed, renewalSmallInitialMemory ring seed)) word = 1 := by
      omega
    have hstart :
        ¬ renewalSmallStop ring (renewalSmallStart ring seed) := hnot
    obtain ⟨u, e, v, hword, hopen, hcut⟩ :=
      smallRetryFirstHasCut ring hn hsmall word
        (seed, renewalSmallInitialMemory ring seed)
        (renewalSmallStart ring seed) rfl hstart hretry
    have hdet := smallOldCutDetector ring
      (smallRefAfter ring (renewalSmallStart ring seed) u) e hcut
    obtain ⟨p, f, tail, hp, hbirth, hwin⟩ :=
      hsource seed u e hopen hdet.1 hdet.2
    have hpopen :
        smallRefOpen ring (renewalSmallStart ring seed) p := by
      have hfull :
          smallRefOpen ring (renewalSmallStart ring seed)
            (p ++ f :: tail) := by
        rw [← hp]
        exact hopen
      exact smallRefOpenPrefix ring p (f :: tail)
        (renewalSmallStart ring seed) hfull
    have hmem :
        e ∈ renewalSmallSpawn ring
          (smallRefAfter ring (renewalSmallStart ring seed) p) f := by
      rcases hbirth with hres | hsource
      · rw [hres]
        exact smallResponderOriginMem ring
          (smallRefAfter ring (renewalSmallStart ring seed) p) f
      · obtain ⟨he, hextra⟩ := hsource
        rw [he]
        exact smallExtraOriginMem ring
          (smallRefAfter ring (renewalSmallStart ring seed) p)
          f hextra
    have hwinLong :
        renewalSmallWin ring e (compileAdvice (ceilLogTwo n)).K
          (tail ++ e :: v) = true := by
      have hh := smallWinAppendTrue ring e
        (tail ++ [e]) v (compileAdvice (ceilLogTwo n)).K hwin
      simpa only [List.append_assoc, List.singleton_append] using hh
    have hpos := smallSuccessfulOrigin ring e p
      (renewalSmallStart ring seed) f (tail ++ e :: v)
      hpopen hmem hwinLong
    have hlist :
        u ++ e :: v = p ++ f :: (tail ++ e :: v) := by
      rw [hp]
      simp only [List.append_assoc, List.cons_append]
    have hpositive :
        0 < Prob.successfulOriginsWord
          (renewalSmallNext ring) (renewalSmallStop ring)
          (renewalSmallSpawn ring)
          (fun o w => renewalSmallWin ring o
            (compileAdvice (ceilLogTwo n)).K w)
          (renewalSmallStart ring seed) word := by
      rw [hword, hlist]
      exact hpos
    have hevent :
        Prob.originEventWord (renewalSmallNext ring)
          (renewalSmallStop ring) (renewalSmallSpawn ring)
          (fun o w => renewalSmallWin ring o
            (compileAdvice (ceilLogTwo n)).K w)
          (renewalSmallStart ring seed) word = 1 := by
      unfold Prob.originEventWord
      split
      · rename_i he
        omega
      · rfl
    rw [hretry, hevent]
    exact Nat.le_refl 1

end L3.SmallRenewal

/-!
Source-of-origin and race-trace bookkeeping.

The initial SMALL memory is false at every site, including sites
with arbitrary inherited RUN counters.  The first theorem isolates
every later true memory bit to a literal responder service or the
one-time invalid-source sanitation event.

The trace invariant below records the additional field-history
obligation needed for SmallRunSourceWitness.  Its base case and
the purely scheduler-word implication are proved.  The field-step
preservation of that invariant is NOT proved in this addendum.
-/

namespace L3.SmallRenewal

open L3
open L3.HeadlineRenewal
open Classical
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

set_option autoImplicit false
set_option Elab.async false

/-- Initial SMALL memory is false, regardless of inherited RUN. -/
theorem smallSeedMemoryFalse {n : Nat}
    (ring : DirectedRing n) (seed : RootedSeed ring)
    (site : Fin n) :
    (renewalSmallStart ring seed).2 site = false := by
  rfl

/-- An arbitrary initial memory may already be true.  Otherwise
each later true bit has a concrete first creating service.  This
statement is independent of the source SMALL-counter value. -/
private theorem smallSeenHasCreatingService {n : Nat}
    (ring : DirectedRing n) :
    ∀ (word : List (Fin n))
      (r : RenewalSmallReference n) (site : Fin n),
      (smallRefAfter ring r word).2 site = true →
      r.2 site = true ∨
      ∃ (p : List (Fin n)) (f : Fin n)
        (tail : List (Fin n)),
        word = p ++ f :: tail ∧
        (site = ring.rightNeighbor f ∨
          (site = f ∧
            renewalSmallExtra
              (smallRefAfter ring r p).1
              (smallRefAfter ring r p).2 f = true)) := by
  intro word
  induction word with
  | nil =>
      intro r site hseen
      exact Or.inl hseen
  | cons f fs ih =>
      intro r site hseen
      change
        (smallRefAfter ring (renewalSmallNext ring r f) fs).2
          site = true at hseen
      rcases ih (renewalSmallNext ring r f) site hseen with
        hprior | ⟨p, g, tail, hp, hb⟩
      · cases hs : r.2 site with
        | true =>
            exact Or.inl rfl
        | false =>
            have hm :
                (renewalSmallMemoryNext ring r.1 r.2 f) site =
                  true := hprior
            by_cases hf : site = f
            · subst site
              have hinvalid :
                  renewalSmallInvalid
                    (compileAdvice (ceilLogTwo n)).K
                    (r.1 f).small = true := by
                cases hi : renewalSmallInvalid
                    (compileAdvice (ceilLogTwo n)).K
                    (r.1 f).small with
                | false =>
                    simp [renewalSmallMemoryNext, hs, hi] at hm
                | true =>
                    rfl
              refine Or.inr ⟨[], f, fs, rfl, Or.inr ⟨rfl, ?_⟩⟩
              unfold renewalSmallExtra
              change (!(r.2 f) && renewalSmallInvalid
                (compileAdvice (ceilLogTwo n)).K (r.1 f).small) = true
              rw [hs, hinvalid]
              all_goals rfl
            · by_cases ht : site = ring.rightNeighbor f
              · exact Or.inr ⟨[], f, fs, rfl, Or.inl ht⟩
              · simp [renewalSmallMemoryNext, hf, ht, hs] at hm
      · refine Or.inr ⟨f :: p, g, tail, ?_, ?_⟩
        · rw [hp]
          rfl
        · exact hb

/-- Every true site bit from the genuine initial reference has
an earlier corresponding entry in renewalSmallSpawn.  Inherited
RUN values do not supply a true seen bit at the initial cut. -/
theorem smallSeedSeenHasOrigin {n : Nat}
    (ring : DirectedRing n) (seed : RootedSeed ring)
    (word : List (Fin n)) (site : Fin n)
    (hseen :
      (smallRefAfter ring (renewalSmallStart ring seed) word).2
        site = true) :
    ∃ (p : List (Fin n)) (f : Fin n)
      (tail : List (Fin n)),
      word = p ++ f :: tail ∧
      (site = ring.rightNeighbor f ∨
        (site = f ∧
          renewalSmallExtra
            (smallRefAfter ring (renewalSmallStart ring seed) p).1
            (smallRefAfter ring (renewalSmallStart ring seed) p).2
            f = true)) := by
  rcases smallSeenHasCreatingService ring word
      (renewalSmallStart ring seed) site hseen with
    hinherited | hcreated
  · have hf := smallSeedMemoryFalse ring seed site
    rw [hf] at hinherited
    cases hinherited
  · exact hcreated

/-- The number of outgoing services to one fixed root in a word. -/
private def smallTraceHeadCount {n : Nat}
    (site : Fin n) (word : List (Fin n)) : Nat :=
  (word.filter (fun e => decide (e = site))).length

/-- No *effective* incoming reset occurs on this suffix:
a self-edge (possible at n=1) is outgoing-priority, not loss. -/
private def smallTraceNoIncoming {n : Nat}
    (ring : DirectedRing n) (site : Fin n)
    (word : List (Fin n)) : Prop :=
  ∀ e : Fin n, e ∈ word → e ≠ site →
    ring.rightNeighbor e ≠ site

/-- Proposed run-field provenance invariant.  For every seen
site currently holding RUN j, find its latest genuine zero origin;
the following edge suffix has exactly j source services and no
effective incoming reset.  This is stronger than mere seen-origin
existence and is the remaining inductive field-step obligation. -/
def SmallSeenRunTrace {n : Nat}
    (ring : DirectedRing n) (seed : RootedSeed ring)
    (word : List (Fin n)) : Prop :=
  ∀ (site : Fin n) (j : Nat),
    (smallRefAfter ring (renewalSmallStart ring seed) word).2
      site = true →
    parseRun
      ((smallRefAfter ring (renewalSmallStart ring seed) word).1
        site).small = some j →
    ∃ (p : List (Fin n)) (f : Fin n)
      (tail : List (Fin n)),
      word = p ++ f :: tail ∧
      (site = ring.rightNeighbor f ∨
        (site = f ∧
          renewalSmallExtra
            (smallRefAfter ring (renewalSmallStart ring seed) p).1
            (smallRefAfter ring (renewalSmallStart ring seed) p).2
            f = true)) ∧
      smallTraceNoIncoming ring site tail ∧
      smallTraceHeadCount site tail = j

/-- Initial trace is vacuous, even for an inherited RUN(K-1). -/
theorem smallSeenRunTraceSeed {n : Nat}
    (ring : DirectedRing n) (seed : RootedSeed ring) :
    SmallSeenRunTrace ring seed [] := by
  intro site j hseen _
  have hf := smallSeedMemoryFalse ring seed site
  change (renewalSmallStart ring seed).2 site = true at hseen
  rw [hf] at hseen
  cases hseen

private theorem smallTraceNoIncomingTail {n : Nat}
    (ring : DirectedRing n) (site e : Fin n)
    (word : List (Fin n))
    (h : smallTraceNoIncoming ring site (e :: word)) :
    smallTraceNoIncoming ring site word := by
  intro f hf hneq
  exact h f (List.mem_cons_of_mem e hf) hneq

/-- Exact j-head/no-reset schedule suffix wins the j-head race. -/
private theorem smallTraceWins {n : Nat}
    (ring : DirectedRing n) (site : Fin n) :
    ∀ (word : List (Fin n)) (j : Nat),
      smallTraceNoIncoming ring site word →
      smallTraceHeadCount site word = j →
      renewalSmallWin ring site j word = true := by
  intro word
  induction word with
  | nil =>
      intro j _ hcount
      change 0 = j at hcount
      subst j
      rfl
  | cons e es ih =>
      intro j hno hcount
      have htail : smallTraceNoIncoming ring site es :=
        smallTraceNoIncomingTail ring site e es hno
      by_cases he : e = site
      · have hc :
            smallTraceHeadCount site (e :: es) =
              smallTraceHeadCount site es + 1 := by
          simp [smallTraceHeadCount, he, Nat.add_comm]
        cases j with
        | zero =>
            rw [hc] at hcount
            omega
        | succ j =>
            have htailCount : smallTraceHeadCount site es = j := by
              rw [hc] at hcount
              omega
            have hw := ih j htail htailCount
            simpa [renewalSmallWin, he] using hw
      · have hi : ring.rightNeighbor e ≠ site :=
          hno e (by simp) he
        have hc :
            smallTraceHeadCount site (e :: es) =
              smallTraceHeadCount site es := by
          simp [smallTraceHeadCount, he]
        have htailCount : smallTraceHeadCount site es = j := by
          rw [hc] at hcount
          exact hcount
        cases j with
        | zero =>
            rfl
        | succ j =>
            have hw := ih (j + 1) htail htailCount
            simpa [renewalSmallWin, he, hi] using hw

/-- Appending a real outgoing service does not introduce an
effective incoming reset, even on a one-site ring. -/
private theorem smallTraceNoIncomingLastHead {n : Nat}
    (ring : DirectedRing n) (site : Fin n)
    (word : List (Fin n))
    (h : smallTraceNoIncoming ring site word) :
    smallTraceNoIncoming ring site (word ++ [site]) := by
  intro e he hne
  have hcases : e ∈ word ∨ e = site := by
    simpa using (List.mem_append.mp he)
  rcases hcases with hword | hlast
  · exact h e hword hne
  · exact False.elim (hne hlast)

private theorem smallTraceHeadCountLastHead {n : Nat}
    (site : Fin n) (word : List (Fin n)) :
    smallTraceHeadCount site (word ++ [site]) =
      smallTraceHeadCount site word + 1 := by
  simp [smallTraceHeadCount, List.filter_append]

/-- Once the source's current j is paid by genuine outgoing
services since its origin, the success service makes j+1 heads. -/
theorem smallTraceWinOnSuccessEdge {n : Nat}
    (ring : DirectedRing n) (site : Fin n)
    (word : List (Fin n)) (j k : Nat)
    (hno : smallTraceNoIncoming ring site word)
    (hcount : smallTraceHeadCount site word = j)
    (hnext : j + 1 = k) :
    renewalSmallWin ring site k (word ++ [site]) = true := by
  apply smallTraceWins ring site (word ++ [site]) k
  · exact smallTraceNoIncomingLastHead ring site word hno
  · rw [smallTraceHeadCountLastHead, hcount]
    exact hnext

end L3.SmallRenewal

/-!
Exact one-edge SMALL source / responder geometry.

The raw smallPair row has a responder-zero output, but the
masked physical pair copies the SOURCE output at a self-edge.
The n=1 seam therefore refutes an unrestricted claim that the
physical responder site always contains RUN0.  The separation
lemmas below identify precisely the required n >= 2 premise.

This does not assert that the historical
SmallSeenRunTrace field-step invariant has been discharged.
-/

namespace L3.SmallRenewal

open L3
open L3.HeadlineRenewal
open Classical
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

set_option autoImplicit false
set_option Elab.async false

/-- The initiating site's physical MASKED update always chooses
the first endpoint, regardless of whether the incident sites
coincide. -/
private theorem smallMaskedSourceAt {n : Nat}
    (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (e : Fin n) (suppress : Bool) :
    renewalMaskedStep ring C e suppress e =
      (renewalMaskedPair (compileAdvice (ceilLogTwo n))
        suppress (C e) (C (ring.rightNeighbor e))).1 := by
  unfold renewalMaskedStep
  exact if_pos rfl

/-- The responder site's physical MASKED update chooses the
second endpoint ONLY when responder and initiator differ. -/
private theorem smallMaskedResponderAt {n : Nat}
    (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (e : Fin n) (suppress : Bool)
    (hdistinct : ring.rightNeighbor e ≠ e) :
    renewalMaskedStep ring C e suppress
        (ring.rightNeighbor e) =
      (renewalMaskedPair (compileAdvice (ceilLogTwo n))
        suppress (C e) (C (ring.rightNeighbor e))).2 := by
  exact (if_neg hdistinct).trans (if_pos rfl)

/-- A site outside both selected endpoints has the OLD complete
Agent record, not merely the SMALL field. -/
private theorem smallMaskedOtherAt {n : Nat}
    (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (e i : Fin n) (suppress : Bool)
    (hsource : i ≠ e)
    (htarget : i ≠ ring.rightNeighbor e) :
    renewalMaskedStep ring C e suppress i = C i := by
  exact (if_neg hsource).trans (if_neg htarget)

/-- A ring with one physical site has a self-edge. -/
private theorem smallOneSiteRightSelf
    (ring : DirectedRing 1) (e : Fin 1) :
    ring.rightNeighbor e = e := by
  apply Fin.ext
  change (e.val + 1) % 1 = e.val
  have hzero : e.val = 0 := by omega
  simp [hzero]

/-- In the actual n >= 2 setting, the responder output is
unambiguously the second endpoint; this is the geometry needed
when transporting the literal SMALL responder-zero row. -/
theorem smallDistinctResponderUsesSecond {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (C : HeadlineConfiguration n)
    (e : Fin n) (suppress : Bool) :
    renewalMaskedStep ring C e suppress
        (ring.rightNeighbor e) =
      (renewalMaskedPair (compileAdvice (ceilLogTwo n))
        suppress (C e) (C (ring.rightNeighbor e))).2 := by
  exact smallMaskedResponderAt ring C e suppress
    (Counter.resetRootPortDistinct ring e hn)

/-- The raw SMALL owner has a concrete source/responder contrast:
an OLD SPENT source stays SPENT, while the responder output is
RUN0.  This source-level row needs no assumption on the
responder's OLD SMALL scratch. -/
private theorem smallSpentPairRow
    (c : Compiled) (x y : Agent c)
    (hx : x.small = .SPENT) :
    (smallPair x y c.K).1 = .SPENT ∧
      (smallPair x y c.K).2.1 = smallRunZero := by
  constructor
  · cases hy : y.small <;>
      simp [smallPair, parseRun, hx, hy] <;>
      (repeat' split) <;> rfl
  · exact renewalSmallResponderZero c x y

/-- A source RUN j strictly below the success threshold
increments by exactly one on the raw SMALL row. -/
private theorem smallPairSourceBelow
    (c : Compiled) (x y : Agent c) (j : Nat)
    (hrun : parseRun x.small = some j)
    (hj : j + 1 < c.K) :
    (smallPair x y c.K).1 = smallRun (j + 1) := by
  have hnot : ¬ j ≥ c.K := by omega
  cases hy : parseRun y.small with
  | none =>
      simp [smallPair, hrun, hy, hnot, hj]
  | some v =>
      by_cases hv : v ≥ c.K
      · simp [smallPair, hrun, hy, hnot, hj, hv]
      · simp [smallPair, hrun, hy, hnot, hj, hv]

/-- A source RUN j with j+1=K spends its counter and creates
the OLD physical SMALL success bit, before any new memory bit. -/
private theorem smallPairSourceThreshold
    (c : Compiled) (x y : Agent c) (j : Nat)
    (hrun : parseRun x.small = some j)
    (hj : j + 1 = c.K) :
    (smallPair x y c.K).1 = .SPENT ∧
      (smallPair x y c.K).2.2 = true := by
  have hnot : ¬ j ≥ c.K := by omega
  have hlt : ¬ j + 1 < c.K := by omega
  cases hy : parseRun y.small with
  | none =>
      simp [smallPair, hrun, hy, hnot, hlt, hj]
  | some v =>
      by_cases hv : v ≥ c.K
      · simp [smallPair, hrun, hy, hnot, hlt, hj, hv]
      · simp [smallPair, hrun, hy, hnot, hlt, hj, hv]

/-- A source with inherited RUN j at or beyond K is sanitized
to RUN0 and cannot also count that service as a new head. -/
private theorem smallPairSourceSanitize
    (c : Compiled) (x y : Agent c) (j : Nat)
    (hrun : parseRun x.small = some j)
    (hj : c.K ≤ j) :
    (smallPair x y c.K).1 = smallRunZero := by
  cases hy : parseRun y.small with
  | none =>
      simp [smallPair, hrun, hy, hj]
  | some v =>
      by_cases hv : v ≥ c.K
      · simp [smallPair, hrun, hy, hj, hv]
      · simp [smallPair, hrun, hy, hj, hv]

end L3.SmallRenewal

/-!
SMALL projection through the actual full owner and a
reachable bound excluding seen RUN counters at or beyond K.

The physical/source projection is obtained from baseStep in the
production useSmall branch, then transported through transition,
assemble, and renewalMaskedPairFrames. No field is inferred from
an alternate scheduler or a headlinePhysicalNext rewrite.

The suffix-history preservation of SmallSeenRunTrace is a distinct
remaining lemma.
-/

namespace L3.SmallRenewal

open L3
open L3.HeadlineRenewal
open Classical
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

set_option autoImplicit false
set_option Elab.async false

/-- The literal SMALL branch of baseStep writes its two
endpoint SMALL fields from smallPair. Subsequent Base field
updates are on disjoint namespaces. -/
private theorem smallBaseStepFields (c : Compiled)
    (ev : CertEvent) (x y : Agent c)
    (hsmall : c.useSmall = true) :
    (baseStep c ev x y).1.small = (smallPair x y c.K).1 ∧
    (baseStep c ev x y).2.small = (smallPair x y c.K).2.1 := by
  constructor
  · simp [baseStep, hsmall, Agent.setNative,
      Agent.setCPriv] <;>
      repeat (first | rfl | split)
  · simp [baseStep, hsmall, Agent.setNative,
      Agent.setCPriv] <;>
      repeat (first | rfl | split)

/-- The full certificate and H/K assembly preserve both
SMALL fields of the literal Base step. -/
private theorem smallTransitionFields (c : Compiled)
    (x y : Agent c) (hsmall : c.useSmall = true) :
    (transition c x y).1.small = (smallPair x y c.K).1 ∧
    (transition c x y).2.small = (smallPair x y c.K).2.1 := by
  rcases hc : certificateStep c x y with ⟨cx, cy, ev⟩
  rcases hh : hKStep c x y with ⟨hx, hy⟩
  have hb := smallBaseStepFields c ev x y hsmall
  simpa [transition, hc, hh, assemble] using hb

/-- Masking a fresh grant changes req/grant only. The
SMALL pair is exactly the raw SMALL owner pair for either
choice of suppression. -/
private theorem smallMaskedPairFields (c : Compiled)
    (x y : Agent c) (suppress : Bool)
    (hsmall : c.useSmall = true) :
    (renewalMaskedPair c suppress x y).1.small =
        (smallPair x y c.K).1 ∧
    (renewalMaskedPair c suppress x y).2.small =
        (smallPair x y c.K).2.1 := by
  have hframe := renewalMaskedPairFrames c suppress x y
  have ht := smallTransitionFields c x y hsmall
  have hx : (renewalMaskedPair c suppress x y).1.small =
      (transition c x y).1.small := by
    have hh := congrArg (fun z : Agent c => z.small) hframe.1
    change (renewalMaskedPair c suppress x y).1.small =
      (transition c x y).1.small at hh
    exact hh
  have hy : (renewalMaskedPair c suppress x y).2.small =
      (transition c x y).2.small := by
    have hh := congrArg (fun z : Agent c => z.small) hframe.2
    change (renewalMaskedPair c suppress x y).2.small =
      (transition c x y).2.small at hh
    exact hh
  exact ⟨hx.trans ht.1, hy.trans ht.2⟩

/-- The actual physical source reads the first SMALL output.
The statement is for renewalSmallNext, not a freely rewritten
headlinePhysicalNext goal. -/
private theorem smallReferenceSourceField {n : Nat}
    (ring : DirectedRing n)
    (hsmall : (compileAdvice (ceilLogTwo n)).useSmall = true)
    (r : RenewalSmallReference n) (e : Fin n) :
    ((renewalSmallNext ring r e).1 e).small =
      (smallPair (r.1 e) (r.1 (ring.rightNeighbor e))
        (compileAdvice (ceilLogTwo n)).K).1 := by
  have hh := congrArg
    (fun z : Agent (compileAdvice (ceilLogTwo n)) => z.small)
    (smallMaskedSourceAt ring r.1 e
      (renewalSmallCut ring r.1 r.2 e))
  change ((renewalSmallNext ring r e).1 e).small =
    (renewalMaskedPair (compileAdvice (ceilLogTwo n))
      (renewalSmallCut ring r.1 r.2 e)
      (r.1 e) (r.1 (ring.rightNeighbor e))).1.small at hh
  exact hh.trans
    (smallMaskedPairFields (compileAdvice (ceilLogTwo n))
      (r.1 e) (r.1 (ring.rightNeighbor e))
      (renewalSmallCut ring r.1 r.2 e) hsmall).1

/-- For n >= 2 the responder is a separate physical site
and its SMALL field is the raw owner's reset RUN0. -/
theorem smallReferenceResponderZero {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (hsmall : (compileAdvice (ceilLogTwo n)).useSmall = true)
    (r : RenewalSmallReference n) (e : Fin n) :
    ((renewalSmallNext ring r e).1
      (ring.rightNeighbor e)).small = smallRunZero := by
  have hh := congrArg
    (fun z : Agent (compileAdvice (ceilLogTwo n)) => z.small)
    (smallDistinctResponderUsesSecond ring hn r.1 e
      (renewalSmallCut ring r.1 r.2 e))
  change ((renewalSmallNext ring r e).1
      (ring.rightNeighbor e)).small =
    (renewalMaskedPair (compileAdvice (ceilLogTwo n))
      (renewalSmallCut ring r.1 r.2 e)
      (r.1 e) (r.1 (ring.rightNeighbor e))).2.small at hh
  have hf := (smallMaskedPairFields
    (compileAdvice (ceilLogTwo n))
    (r.1 e) (r.1 (ring.rightNeighbor e))
    (renewalSmallCut ring r.1 r.2 e) hsmall).2
  exact (hh.trans hf).trans
    (renewalSmallResponderZero (compileAdvice (ceilLogTwo n))
      (r.1 e) (r.1 (ring.rightNeighbor e)))

/-- The selected owner and the proof memory both frame a site
outside the selected two physical endpoints. -/
private theorem smallReferenceOtherField {n : Nat}
    (ring : DirectedRing n)
    (r : RenewalSmallReference n)
    (e i : Fin n) (he : i ≠ e)
    (hy : i ≠ ring.rightNeighbor e) :
    ((renewalSmallNext ring r e).1 i).small =
      (r.1 i).small := by
  have hh := congrArg
    (fun z : Agent (compileAdvice (ceilLogTwo n)) => z.small)
    (smallMaskedOtherAt ring r.1 e i
      (renewalSmallCut ring r.1 r.2 e) he hy)
  change ((renewalSmallNext ring r e).1 i).small =
    (r.1 i).small at hh
  exact hh

private theorem smallReferenceOtherSeen {n : Nat}
    (ring : DirectedRing n) (r : RenewalSmallReference n)
    (e i : Fin n) (he : i ≠ e)
    (hy : i ≠ ring.rightNeighbor e) :
    (renewalSmallNext ring r e).2 i = r.2 i := by
  change renewalSmallMemoryNext ring r.1 r.2 e i = r.2 i
  simp [renewalSmallMemoryNext, he, hy]

/-- The OLD OFF source cannot acquire a RUN merely by being
the selected source; that row leaves its SMALL field OFF. -/
private theorem smallPairSourceOff (c : Compiled)
    (x y : Agent c) (hx : x.small = .OFF) :
    (smallPair x y c.K).1 = .OFF := by
  cases hy : y.small <;>
    simp [smallPair, parseRun, hx, hy] <;>
    (repeat' split) <;> rfl

/-- Raw source output RUN values are always strictly below K
in the production SMALL band, even from arbitrary inherited
Cartesian RUN scratch. The saturated inherited rows reset to
RUN0; the threshold row becomes SPENT. -/
private theorem smallPairSourceResultBelow
    (q : Nat) (hthree : 3 ≤ q)
    (hsmall : (compileAdvice q).useSmall = true)
    (x y : Agent (compileAdvice q)) (j : Nat)
    (hpost : parseRun
        (smallPair x y (compileAdvice q).K).1 = some j) :
    j < (compileAdvice q).K := by
  cases hx : x.small with
  | OFF =>
      have hf := smallPairSourceOff (compileAdvice q) x y hx
      rw [hf] at hpost
      cases hpost
  | SPENT =>
      have hf := (smallSpentPairRow (compileAdvice q) x y hx).1
      rw [hf] at hpost
      cases hpost
  | RUN v =>
      have hrun : parseRun x.small = some v.val := by
        simp [parseRun, hx]
      by_cases hb : v.val + 1 < (compileAdvice q).K
      · have hf := smallPairSourceBelow (compileAdvice q) x y
          v.val hrun hb
        rw [hf] at hpost
        have hcap := smallRunIncrementBelowCarrier
          q hthree hsmall v.val hb
        have hp : parseRun (smallRun (v.val + 1)) =
            some (v.val + 1) := by
          simp [smallRun, hcap, parseRun]
        rw [hp] at hpost
        cases hpost
        exact hb
      · by_cases heq : v.val + 1 = (compileAdvice q).K
        · have hf := (smallPairSourceThreshold
            (compileAdvice q) x y v.val hrun heq).1
          rw [hf] at hpost
          cases hpost
        · have hbig : (compileAdvice q).K ≤ v.val := by omega
          have hf := smallPairSourceSanitize
            (compileAdvice q) x y v.val hrun hbig
          rw [hf] at hpost
          change some 0 = some j at hpost
          cases hpost
          change 0 < 2 * q + (compileAdvice q).kappa
          omega

/-- The local reachable condition: any site with SMALL memory
and a RUN j has j < K. No condition is imposed on unseen,
possibly invalid inherited RUN scratch. -/
private def smallSeenRunBoundAt {n : Nat}
    (_ring : DirectedRing n) (r : RenewalSmallReference n) : Prop :=
  ∀ (site : Fin n) (j : Nat),
    r.2 site = true →
    parseRun (r.1 site).small = some j →
    j < (compileAdvice (ceilLogTwo n)).K

/-- A single literal reference service preserves the seen-RUN
upper bound. Updated endpoints get freshly bounded SMALL
values; all other sites frame both fields. -/
private theorem smallSeenRunBoundStep {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hsmall : (compileAdvice (ceilLogTwo n)).useSmall = true)
    (r : RenewalSmallReference n) (e : Fin n)
    (hbound : smallSeenRunBoundAt ring r) :
    smallSeenRunBoundAt ring (renewalSmallNext ring r e) := by
  intro site j hseen hrun
  by_cases hs : site = e
  · subst site
    have hf := smallReferenceSourceField ring hsmall r e
    rw [hf] at hrun
    have hthree : 3 ≤ ceilLogTwo n :=
      ceilLogTwo_ge_three n hn
    exact smallPairSourceResultBelow (ceilLogTwo n)
      hthree hsmall (r.1 e) (r.1 (ring.rightNeighbor e))
      j hrun
  · by_cases ht : site = ring.rightNeighbor e
    · subst site
      have hf := smallReferenceResponderZero ring
        (by omega : 2 ≤ n) hsmall r e
      rw [hf] at hrun
      change some 0 = some j at hrun
      cases hrun
      have hthree : 3 ≤ ceilLogTwo n :=
        ceilLogTwo_ge_three n hn
      change 0 < 2 * ceilLogTwo n +
        (compileAdvice (ceilLogTwo n)).kappa
      omega
    · have hf := smallReferenceOtherField ring r e site hs ht
      have hm := smallReferenceOtherSeen ring r e site hs ht
      rw [hf] at hrun
      rw [hm] at hseen
      exact hbound site j hseen hrun

/-- The local bound propagates along any original-clock
scheduler word, not just along prefixes of a special word. -/
private theorem smallSeenRunBoundWord {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hsmall : (compileAdvice (ceilLogTwo n)).useSmall = true) :
    ∀ (word : List (Fin n)) (r : RenewalSmallReference n),
      smallSeenRunBoundAt ring r →
        smallSeenRunBoundAt ring (smallRefAfter ring r word) := by
  intro word
  induction word with
  | nil =>
      intro r h
      exact h
  | cons e es ih =>
      intro r h
      change smallSeenRunBoundAt ring
        (smallRefAfter ring (renewalSmallNext ring r e) es)
      exact ih (renewalSmallNext ring r e)
        (smallSeenRunBoundStep ring hn hsmall r e h)

/-- The usable production SMALL bound from any physical rooted
Cartesian seed. It excludes a seen RUN j >= K at every reached
reference cut without assuming the initial inherited runs valid. -/
theorem smallSeenRunBound {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hsmall : (compileAdvice (ceilLogTwo n)).useSmall = true)
    (seed : RootedSeed ring) (word : List (Fin n))
    (site : Fin n) (j : Nat)
    (hseen :
      (smallRefAfter ring (renewalSmallStart ring seed) word).2
        site = true)
    (hrun : parseRun
      ((smallRefAfter ring (renewalSmallStart ring seed) word).1
        site).small = some j) :
    j < (compileAdvice (ceilLogTwo n)).K := by
  have hseed :
      smallSeenRunBoundAt ring (renewalSmallStart ring seed) := by
    intro i k hs _
    have hf := smallSeedMemoryFalse ring seed i
    rw [hf] at hs
    cases hs
  exact (smallSeenRunBoundWord ring hn hsmall
    word (renewalSmallStart ring seed) hseed)
    site j hseen hrun

/-- Exact snoc rule for the existing source-level reference.
This allows history witnesses to be extended by the last
selected edge without changing the word's clock. -/
private theorem smallRefAfterSnoc {n : Nat}
    (ring : DirectedRing n) :
    ∀ (u : List (Fin n)) (r : RenewalSmallReference n)
      (e : Fin n),
      smallRefAfter ring r (u ++ [e]) =
        renewalSmallNext ring (smallRefAfter ring r u) e := by
  intro u
  induction u with
  | nil =>
      intro r e
      rfl
  | cons f fs ih =>
      intro r e
      change
        smallRefAfter ring (renewalSmallNext ring r f)
          (fs ++ [e]) =
        renewalSmallNext ring
          (smallRefAfter ring (renewalSmallNext ring r f) fs) e
      exact ih (renewalSmallNext ring r f) e

/-- The physical reference suffix update of two fields outside
the selected pair is exact; the K-bound need not be re-established
from a historical origin in this branch. -/
private theorem smallTraceOtherFrame {n : Nat}
    (ring : DirectedRing n) (r : RenewalSmallReference n)
    (e site : Fin n)
    (he : site ≠ e)
    (hy : site ≠ ring.rightNeighbor e) :
    (renewalSmallNext ring r e).2 site = r.2 site ∧
    ((renewalSmallNext ring r e).1 site).small =
      (r.1 site).small := by
  exact ⟨smallReferenceOtherSeen ring r e site he hy,
    smallReferenceOtherField ring r e site he hy⟩

end L3.SmallRenewal

/-!
The SMALL seen-RUN origin trace, success shape, and
unconditional retry-first coverage for the actual SMALL reference.

This section uses the existing full-owner projection, inherited
run bound, and scheduler-word trace lemmas. No new protocol
transition, oracle, axiom, or extra import is introduced.
-/

namespace L3.SmallRenewal

open L3
open L3.HeadlineRenewal
open Classical
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

set_option autoImplicit false
set_option Elab.async false

/-- A nonincident edge neither adds a head nor adds an
incoming reset to a previously protected witness suffix. -/
private theorem smallTraceNoIncomingLastOther {n : Nat}
    (ring : DirectedRing n) (site e : Fin n)
    (tail : List (Fin n))
    (hno : smallTraceNoIncoming ring site tail)
    (he : e ≠ site)
    (hy : ring.rightNeighbor e ≠ site) :
    smallTraceNoIncoming ring site (tail ++ [e]) := by
  intro f hf hneq
  rcases List.mem_append.mp hf with hfirst | hlast
  · exact hno f hfirst hneq
  · have hfe : f = e := by simpa using hlast
    rw [hfe]
    exact hy

private theorem smallTraceHeadCountLastOther {n : Nat}
    (site e : Fin n) (tail : List (Fin n))
    (he : e ≠ site) :
    smallTraceHeadCount site (tail ++ [e]) =
      smallTraceHeadCount site tail := by
  simp [smallTraceHeadCount, List.filter_append, he]

/-- At the physical initiator the proof-side seen update
uses OLD seen and the exact OLD invalid-run sanitation test. -/
private theorem smallReferenceSourceSeen {n : Nat}
    (ring : DirectedRing n)
    (r : RenewalSmallReference n) (e : Fin n) :
    (renewalSmallNext ring r e).2 e =
      (r.2 e || renewalSmallInvalid
        (compileAdvice (ceilLogTwo n)).K (r.1 e).small) := by
  simp [renewalSmallNext, renewalSmallMemoryNext]

/-- One actual last-edge update preserves the entire witnessed
RUN count, with one of three geometrically exclusive sites:
source, responder, or nonincident. -/
theorem smallSeenRunTraceStep {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hsmall : (compileAdvice (ceilLogTwo n)).useSmall = true)
    (seed : RootedSeed ring) (u : List (Fin n))
    (e : Fin n)
    (htrace : SmallSeenRunTrace ring seed u) :
    SmallSeenRunTrace ring seed (u ++ [e]) := by
  intro site j hseen hrun
  rw [smallRefAfterSnoc ring u (renewalSmallStart ring seed) e] at hseen hrun
  by_cases hsource : site = e
  · subst site
    have hfield := smallReferenceSourceField ring hsmall
      (smallRefAfter ring (renewalSmallStart ring seed) u) e
    rw [hfield] at hrun
    cases hx :
      ((smallRefAfter ring (renewalSmallStart ring seed) u).1 e).small with
    | OFF =>
        have hoff := smallPairSourceOff
          (compileAdvice (ceilLogTwo n))
          ((smallRefAfter ring (renewalSmallStart ring seed) u).1 e)
          ((smallRefAfter ring (renewalSmallStart ring seed) u).1
            (ring.rightNeighbor e)) hx
        rw [hoff] at hrun
        cases hrun
    | SPENT =>
        have hspent := (smallSpentPairRow
          (compileAdvice (ceilLogTwo n))
          ((smallRefAfter ring (renewalSmallStart ring seed) u).1 e)
          ((smallRefAfter ring (renewalSmallStart ring seed) u).1
            (ring.rightNeighbor e)) hx).1
        rw [hspent] at hrun
        cases hrun
    | RUN v =>
        have hrunOld :
            parseRun
              ((smallRefAfter ring (renewalSmallStart ring seed) u).1
                e).small = some v.val := by
          simp [parseRun, hx]
        by_cases hbelow :
            v.val + 1 < (compileAdvice (ceilLogTwo n)).K
        · have hstep := smallPairSourceBelow
            (compileAdvice (ceilLogTwo n))
            ((smallRefAfter ring (renewalSmallStart ring seed) u).1 e)
            ((smallRefAfter ring (renewalSmallStart ring seed) u).1
              (ring.rightNeighbor e)) v.val hrunOld hbelow
          rw [hstep] at hrun
          have hthree : 3 ≤ ceilLogTwo n :=
            ceilLogTwo_ge_three n hn
          have hcap := smallRunIncrementBelowCarrier
            (ceilLogTwo n) hthree hsmall v.val hbelow
          have hdecode :
              parseRun (smallRun (v.val + 1)) =
                some (v.val + 1) := by
            simp [smallRun, hcap, parseRun]
          rw [hdecode] at hrun
          cases hrun
          have hnotinvalid :
              renewalSmallInvalid
                (compileAdvice (ceilLogTwo n)).K
                ((smallRefAfter ring (renewalSmallStart ring seed) u).1
                  e).small = false := by
            unfold renewalSmallInvalid
            rw [hrunOld]
            have hlt :
                ¬ (compileAdvice (ceilLogTwo n)).K ≤ v.val := by omega
            simp [hlt]
          have hseenOld :
              (smallRefAfter ring (renewalSmallStart ring seed) u).2
                e = true := by
            have hm := smallReferenceSourceSeen ring
              (smallRefAfter ring (renewalSmallStart ring seed) u) e
            rw [hm, hnotinvalid] at hseen
            simpa using hseen
          obtain ⟨p, f, tail, hword, hborn, hno, hcount⟩ :=
            htrace e v.val hseenOld hrunOld
          refine ⟨p, f, tail ++ [e], ?_, hborn, ?_, ?_⟩
          · rw [hword]
            simp only [List.append_assoc, List.cons_append]
          · exact smallTraceNoIncomingLastHead ring e tail hno
          · rw [smallTraceHeadCountLastHead, hcount]
        · by_cases hthreshold :
              v.val + 1 = (compileAdvice (ceilLogTwo n)).K
          · have hspent := (smallPairSourceThreshold
              (compileAdvice (ceilLogTwo n))
              ((smallRefAfter ring (renewalSmallStart ring seed) u).1 e)
              ((smallRefAfter ring (renewalSmallStart ring seed) u).1
                (ring.rightNeighbor e))
              v.val hrunOld hthreshold).1
            rw [hspent] at hrun
            cases hrun
          · have hbig :
                (compileAdvice (ceilLogTwo n)).K ≤ v.val := by omega
            have hsan := smallPairSourceSanitize
              (compileAdvice (ceilLogTwo n))
              ((smallRefAfter ring (renewalSmallStart ring seed) u).1 e)
              ((smallRefAfter ring (renewalSmallStart ring seed) u).1
                (ring.rightNeighbor e))
              v.val hrunOld hbig
            rw [hsan] at hrun
            change some 0 = some j at hrun
            cases hrun
            have hseenOld :
                (smallRefAfter ring (renewalSmallStart ring seed) u).2
                  e = false := by
              cases hs :
                  (smallRefAfter ring (renewalSmallStart ring seed) u).2
                    e with
              | false => rfl
              | true =>
                  have hb := smallSeenRunBound ring hn hsmall
                    seed u e v.val hs hrunOld
                  omega
            have hinvalid :
                renewalSmallInvalid
                  (compileAdvice (ceilLogTwo n)).K
                  ((smallRefAfter ring (renewalSmallStart ring seed) u).1
                    e).small = true := by
              unfold renewalSmallInvalid
              rw [hrunOld]
              simp [hbig]
            have hextra :
                renewalSmallExtra
                  (smallRefAfter ring (renewalSmallStart ring seed) u).1
                  (smallRefAfter ring (renewalSmallStart ring seed) u).2
                  e = true := by
              unfold renewalSmallExtra
              rw [hseenOld, hinvalid]
              rfl
            refine ⟨u, e, [], rfl, Or.inr ⟨rfl, hextra⟩, ?_, rfl⟩
            intro f hf _
            cases hf
  · by_cases htarget : site = ring.rightNeighbor e
    · subst site
      have hzero := smallReferenceResponderZero ring
        (by omega : 2 ≤ n) hsmall
        (smallRefAfter ring (renewalSmallStart ring seed) u) e
      rw [hzero] at hrun
      change some 0 = some j at hrun
      cases hrun
      refine ⟨u, e, [], rfl, Or.inl rfl, ?_, rfl⟩
      intro f hf _
      cases hf
    · have hframe := smallTraceOtherFrame ring
        (smallRefAfter ring (renewalSmallStart ring seed) u)
        e site hsource htarget
      rw [hframe.1] at hseen
      rw [hframe.2] at hrun
      obtain ⟨p, f, tail, hword, hborn, hno, hcount⟩ :=
        htrace site j hseen hrun
      refine ⟨p, f, tail ++ [e], ?_, hborn, ?_, ?_⟩
      · rw [hword]
        simp only [List.append_assoc, List.cons_append]
      · exact smallTraceNoIncomingLastOther ring site e tail
          hno (Ne.symm hsource) (Ne.symm htarget)
      · rw [smallTraceHeadCountLastOther site e tail
            (Ne.symm hsource), hcount]

/-- Forward preservation of the entire seen-RUN trace at every
actual scheduler prefix, starting at arbitrary legal Cartesian
private scratch with uniformly false proof-side memory. -/
theorem smallSeenRunTraceAll {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hsmall : (compileAdvice (ceilLogTwo n)).useSmall = true)
    (seed : RootedSeed ring) :
    ∀ word : List (Fin n), SmallSeenRunTrace ring seed word := by
  have hloop :
      ∀ (w u : List (Fin n)),
        SmallSeenRunTrace ring seed u →
          SmallSeenRunTrace ring seed (u ++ w) := by
    intro w
    induction w with
    | nil =>
        intro u hu
        simpa only [List.append_nil] using hu
    | cons e es ih =>
        intro u hu
        have ht := smallSeenRunTraceStep ring hn hsmall
          seed u e hu
        have hh := ih (u ++ [e]) ht
        have heq : (u ++ [e]) ++ es = u ++ e :: es := by
          simp only [List.append_assoc, List.singleton_append]
        rw [← heq]
        exact hh
  intro word
  have hh := hloop word [] (smallSeenRunTraceSeed ring seed)
  simpa only [List.nil_append] using hh

/-- The literal SMALL success bit can become true only from
an OLD source RUN j with exactly j+1=K. The responder's
OLD SMALL state is arbitrary. -/
private theorem smallPairSuccessShape
    (c : Compiled) (x y : Agent c)
    (hsuccess : (smallPair x y c.K).2.2 = true) :
    ∃ j : Nat, parseRun x.small = some j ∧ j + 1 = c.K := by
  cases hx : parseRun x.small with
  | none =>
      cases hy : parseRun y.small with
      | none => simp [smallPair, hx, hy] at hsuccess
      | some v =>
          by_cases hv : v ≥ c.K
          · simp [smallPair, hx, hy, hv] at hsuccess
          · simp [smallPair, hx, hy, hv] at hsuccess
  | some j =>
      by_cases hb : j ≥ c.K
      · cases hy : parseRun y.small with
        | none => simp [smallPair, hx, hy, hb] at hsuccess
        | some v =>
            by_cases hv : v ≥ c.K
            · simp [smallPair, hx, hy, hb, hv] at hsuccess
            · simp [smallPair, hx, hy, hb, hv] at hsuccess
      · by_cases hbelow : j + 1 < c.K
        · cases hy : parseRun y.small with
          | none => simp [smallPair, hx, hy, hb, hbelow] at hsuccess
          | some v =>
              by_cases hv : v ≥ c.K
              · simp [smallPair, hx, hy, hb, hbelow, hv] at hsuccess
              · simp [smallPair, hx, hy, hb, hbelow, hv] at hsuccess
        · by_cases heq : j + 1 = c.K
          · exact ⟨j, rfl, heq⟩
          · cases hy : parseRun y.small with
            | none =>
                simp [smallPair, hx, hy, hb, hbelow, heq] at hsuccess
            | some v =>
                by_cases hv : v ≥ c.K
                · simp [smallPair, hx, hy, hb, hbelow, heq, hv] at hsuccess
                · simp [smallPair, hx, hy, hb, hbelow, heq, hv] at hsuccess

/-- The formerly open source-history bill: an OLD seen source
succeeding at K heads descends from a literal post-cut zero
origin whose true physical edge suffix won the K-head race. -/
theorem smallRunSourceWitness {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hsmall : (compileAdvice (ceilLogTwo n)).useSmall = true) :
    SmallRunSourceWitness ring := by
  intro seed u e _ hseen hsuccess
  obtain ⟨j, hrun, hthreshold⟩ := smallPairSuccessShape
    (compileAdvice (ceilLogTwo n))
    ((smallRefAfter ring (renewalSmallStart ring seed) u).1 e)
    ((smallRefAfter ring (renewalSmallStart ring seed) u).1
      (ring.rightNeighbor e)) hsuccess
  obtain ⟨p, f, tail, hword, hbirth, hno, hcount⟩ :=
    (smallSeenRunTraceAll ring hn hsmall seed u)
      e j hseen hrun
  refine ⟨p, f, tail, hword, hbirth, ?_⟩
  exact smallTraceWinOnSuccessEdge ring e tail j
    (compileAdvice (ceilLogTwo n)).K hno hcount hthreshold

/-- Unconditional SMALL retry-first wordwise origin coverage.
No new generator, scheduler independence, or hidden history
assumption remains in this field of the concrete reference. -/
theorem smallReferenceRetryCoverage {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hsmall : (compileAdvice (ceilLogTwo n)).useSmall = true) :
    ReferenceRetryCoverage ring hn
      (smallRootedReferenceData ring hsmall) := by
  exact smallReferenceRetryCoverageOfSourceWitness ring hn hsmall
    (smallRunSourceWitness ring hn hsmall)

end L3.SmallRenewal

/-!
The literal SMALL seen-bit clearance clock and the exact
remaining stage interface for the own-reference generated hit.

No protocol
row, import, or existing statement is modified.

The only missing named proposition below is
SmallReferencePostSeenStageData. It records actual-reference
rootedness preservation and the four later Appendix F stages.
-/

namespace L3.SmallRenewal

open L3
open L3.HeadlineRenewal
open Classical
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

set_option autoImplicit false
set_option Elab.async false

/-- All sites have received their post-cut zero barrier, so no
inherited SMALL source history can remain unmarked. -/
def smallReferenceSeenComplete {n : Nat}
    (r : RenewalSmallReference n) : Prop :=
  ∀ site : Fin n, r.2 site = true

/-- At a state with an unseen site, nominate that site's literal
incoming edge. The arbitrary default is never used in a drop proof. -/
noncomputable def smallReferenceSeenChoice {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (r : RenewalSmallReference n) : Fin n :=
  if h : ∃ site : Fin n, r.2 site = false then
    ring.leftNeighbor (Classical.choose h)
  else
    ⟨0, by omega⟩

private theorem smallReferenceMissingSite {n : Nat}
    (r : RenewalSmallReference n)
    (hnot : ¬ smallReferenceSeenComplete r) :
    ∃ site : Fin n, r.2 site = false := by
  by_cases hex : ∃ site : Fin n, r.2 site = false
  · exact hex
  · have hall : smallReferenceSeenComplete r := by
      intro site
      cases hs : r.2 site with
      | false => exact False.elim (hex ⟨site, hs⟩)
      | true => rfl
    exact False.elim (hnot hall)

/-- The proof-side seen bit never goes from true back to false. -/
private theorem smallReferenceSeenPointwise {n : Nat}
    (ring : DirectedRing n)
    (r : RenewalSmallReference n) (e site : Fin n) :
    (if (renewalSmallNext ring r e).2 site then 0 else 1) ≤
      (if r.2 site then 0 else 1) := by
  by_cases he : site = e
  · subst site
    cases hs : r.2 e <;>
      cases hv :
        renewalSmallInvalid (compileAdvice (ceilLogTwo n)).K
          (r.1 e).small <;>
      simp [renewalSmallNext, renewalSmallMemoryNext, hs, hv]
  · by_cases hr : site = ring.rightNeighbor e
    · cases hs : r.2 site <;>
        simp [renewalSmallNext, renewalSmallMemoryNext, he, hr, hs]
      · split <;> omega
      · intro hport _
        exact False.elim (he (hr.trans hport))
    · simp [renewalSmallNext, renewalSmallMemoryNext, he, hr]

/-- A pointwise nonincrease plus one strict unit at a site gives
a unit drop in the full Fin-sum, without Finset or Nat subtraction
on the final inequality. -/
private theorem smallReferenceSumStrict {n : Nat}
    (f g : Fin n → Nat) (site : Fin n)
    (hmono : ∀ i, g i ≤ f i)
    (hstrict : g site + 1 ≤ f site) :
    (List.ofFn g).sum + 1 ≤ (List.ofFn f).sum := by
  have hpartial :
      (List.ofFn g).sum ≤
        (List.ofFn (fun i : Fin n =>
          if i = site then f site - 1 else f i)).sum := by
    apply ofFn_sum_le
    intro i
    by_cases hi : i = site
    · subst i
      simp only [if_pos rfl, if_true, ↓reduceIte]
      omega
    · simp only [if_neg hi]
      exact hmono i
  have hswap := smallSumSwapSingle f
    (fun i : Fin n => if i = site then f site - 1 else f i)
    site (by
      intro i hi
      simp only [if_neg hi])
  simp only [if_pos rfl, if_true, ↓reduceIte] at hswap
  omega

private theorem smallReferenceSeenNoninc {n : Nat}
    (ring : DirectedRing n)
    (r : RenewalSmallReference n) (e : Fin n) :
    renewalSmallRemaining (renewalSmallNext ring r e).2 ≤
      renewalSmallRemaining r.2 := by
  unfold renewalSmallRemaining
  exact ofFn_sum_le _ _
    (smallReferenceSeenPointwise ring r e)

/-- Incoming service to an unseen site strictly decreases the
literal number of unmarked sites. The two ports are distinct for
n ≥ 5, and responder memory is set to true on the same service. -/
private theorem smallReferenceSeenIncomingDrop {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (r : RenewalSmallReference n) (site : Fin n)
    (hfalse : r.2 site = false) :
    renewalSmallRemaining
        (renewalSmallNext ring r (ring.leftNeighbor site)).2 + 1 ≤
      renewalSmallRemaining r.2 := by
  have hdistinct : site ≠ ring.leftNeighbor site :=
    smallPortsDistinct ring (by omega : 2 ≤ n) site
  have hnew :
      (renewalSmallNext ring r (ring.leftNeighbor site)).2 site =
        true := by
    change renewalSmallMemoryNext ring r.1 r.2
      (ring.leftNeighbor site) site = true
    simp [renewalSmallMemoryNext, hdistinct,
      smallRightAfterLeft ring site]
  unfold renewalSmallRemaining
  refine smallReferenceSumStrict _ _ site ?_ ?_
  · intro i
    exact smallReferenceSeenPointwise ring r
      (ring.leftNeighbor site) i
  · rw [hnew, hfalse]
    decide

private theorem smallReferenceSeenChosenDrop {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (r : RenewalSmallReference n)
    (hnot : ¬ smallReferenceSeenComplete r) :
    renewalSmallRemaining
        (renewalSmallNext ring r
          (smallReferenceSeenChoice ring hn r)).2 + 1 ≤
      renewalSmallRemaining r.2 := by
  have hex := smallReferenceMissingSite r hnot
  have hchoice :
      smallReferenceSeenChoice ring hn r =
        ring.leftNeighbor (Classical.choose hex) := by
    simp [smallReferenceSeenChoice, hex]
  rw [hchoice]
  exact smallReferenceSeenIncomingDrop ring hn r
    (Classical.choose hex) (Classical.choose_spec hex)

private theorem smallReferenceSeenBound {n : Nat}
    (seen : RenewalSmallMemory n) :
    renewalSmallRemaining seen ≤ n := by
  unfold renewalSmallRemaining
  have hbound := ofFn_sum_le
    (fun i : Fin n => if seen i then 0 else 1)
    (fun _ : Fin n => 1) (by
      intro i
      cases hs : seen i <;> simp [hs])
  simpa only [ofFn_sum_const, Nat.mul_one] using hbound

/-- Unconditional one-stage SMALL clock. The natural potential is
the number of proof-side unseen sites; its chosen incoming edge
drops that number by one, and every other edge is nonincreasing.
Consequently this phase costs at most n², from ANY reference state. -/
theorem smallReferenceSeenClock {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n) :
    ∀ (r : RenewalSmallReference n) (T : Nat),
      costNumerator (renewalSmallNext ring)
        smallReferenceSeenComplete r T ≤ n ^ T * n ^ 2 := by
  have hclock := Prob.costNumerator_le_of_nominated_edge
    (renewalSmallNext ring)
    smallReferenceSeenComplete
    (fun r : RenewalSmallReference n =>
      renewalSmallRemaining r.2)
    (smallReferenceSeenChoice ring hn)
    (smallReferenceSeenChosenDrop ring hn)
    (by
      intro r _ e
      exact smallReferenceSeenNoninc ring r e)
  intro r T
  calc
    costNumerator (renewalSmallNext ring)
        smallReferenceSeenComplete r T ≤
      n ^ T * (n * renewalSmallRemaining r.2) := hclock r T
    _ ≤ n ^ T * (n * n) :=
      Nat.mul_le_mul_left (n ^ T)
        (Nat.mul_le_mul_left n (smallReferenceSeenBound r.2))
    _ = n ^ T * n ^ 2 := by
      rw [Nat.pow_two]

/-- A conjunction with an invariant has the same stopped cost as
its second conjunct, at every state already in that invariant. -/
private theorem smallReferenceInvariantConjunctionCost
    {S : Type} {n : Nat}
    (next : S → Fin n → S)
    (invariant target : S → Prop)
    (hclosed : ∀ x, invariant x → ∀ e, invariant (next x e)) :
    ∀ (T : Nat) (x : S), invariant x →
      costNumerator next
        (fun z => invariant z ∧ target z) x T =
      costNumerator next target x T := by
  intro T
  induction T with
  | zero =>
      intro x _
      simp only [costNumerator_zero]
  | succ T ih =>
      intro x hx
      by_cases ht : target x
      · rw [costNumerator_terminal next
          (fun z => invariant z ∧ target z) x
          (And.intro hx ht) (T + 1),
          costNumerator_terminal next target x ht (T + 1)]
      · have hnottarget : ¬ (invariant x ∧ target x) := by
          intro hh
          exact ht hh.2
        rw [costNumerator_succ next
          (fun z => invariant z ∧ target z) x hnottarget T,
          costNumerator_succ next target x ht T]
        congr 1
        apply ofFn_sum_eq
        intro e
        exact ih (next x e) (hclosed x hx e)

/-- SINGLE REMAINING INPUT for the exact SMALL reference clock:
(1) reference rootedness is preserved by the masked step;
(2) the four post-inherited Appendix F stages hold on that same
reference, with a rooted-and-seen cut for grant drainage.
In particular it does not postulate a generic Next or Stop. -/
def SmallReferencePostSeenStageData {n : Nat}
    (ring : DirectedRing n) : Prop :=
  (∀ r : RenewalSmallReference n,
    headlineRooted ring r.1 →
    ∀ e : Fin n,
      headlineRooted ring (renewalSmallNext ring r e).1) ∧
  ∃ (grantFree singleton prepared : RenewalSmallReference n → Prop),
    StageReferenceGrantDrain (renewalSmallNext ring)
      (fun r => headlineRooted ring r.1 ∧
        smallReferenceSeenComplete r) grantFree ∧
    StageReferenceSingleton (renewalSmallNext ring)
      grantFree singleton ∧
    StageReferencePreparation (renewalSmallNext ring)
      singleton prepared ∧
    StageReferenceGeneratedFinish (renewalSmallNext ring)
      prepared (renewalSmallStop ring)
      (headlineReferenceFinishRate (ceilLogTwo n))

/-- Given exactly the named actual-reference stage interface, the
full SMALL ReferenceClock follows, at the selected A, from every
non-target RootedSeed and for every finite scheduler horizon. -/
theorem smallReferenceClockOfStageData {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hsmall : (compileAdvice (ceilLogTwo n)).useSmall = true)
    (hdata : SmallReferencePostSeenStageData ring) :
    ReferenceClock ring (smallRootedReferenceData ring hsmall)
      (headlineReferenceRate (ceilLogTwo n)) := by
  obtain ⟨hrootclosed, grantFree, singleton, prepared,
    hDrain, hSingle, hPrep, hFinish⟩ := hdata
  have hrate : 1 ≤ headlineInheritedRate (ceilLogTwo n) := by
    unfold headlineInheritedRate
    split
    · omega
    · split
      · omega
      · omega
  have hOld : StageInheritedAuthorityExtinction
      (renewalSmallNext ring)
      (fun r : RenewalSmallReference n => headlineRooted ring r.1)
      (fun r : RenewalSmallReference n =>
        headlineRooted ring r.1 ∧ smallReferenceSeenComplete r)
      (ceilLogTwo n) := by
    intro r hroot
    apply (UniformFirstHit.expectedHittingTimeAtMost_iff_cost
      (renewalSmallNext ring)
      (fun z : RenewalSmallReference n =>
        headlineRooted ring z.1 ∧ smallReferenceSeenComplete z)
      (by omega : 0 < n) r
      (headlineInheritedRate (ceilLogTwo n) * n ^ 2)).2
    intro T
    have heq := smallReferenceInvariantConjunctionCost
      (renewalSmallNext ring)
      (fun z : RenewalSmallReference n => headlineRooted ring z.1)
      smallReferenceSeenComplete hrootclosed T r hroot
    rw [heq]
    calc
      costNumerator (renewalSmallNext ring)
          smallReferenceSeenComplete r T ≤ n ^ T * n ^ 2 :=
        smallReferenceSeenClock ring hn r T
      _ = n ^ T * (1 * n ^ 2) := by simp
      _ ≤ n ^ T *
          (headlineInheritedRate (ceilLogTwo n) * n ^ 2) :=
        Nat.mul_le_mul_left (n ^ T)
          (Nat.mul_le_mul_right (n ^ 2) hrate)
  have hthree : 3 ≤ ceilLogTwo n := ceilLogTwo_ge_three n hn
  have hstages := headlineReferenceStagesCompose
    (renewalSmallNext ring)
    (fun r : RenewalSmallReference n => headlineRooted ring r.1)
    (fun r : RenewalSmallReference n =>
      headlineRooted ring r.1 ∧ smallReferenceSeenComplete r)
    grantFree singleton prepared (renewalSmallStop ring)
    (ceilLogTwo n) hthree (by omega : 0 < n)
    hOld hDrain hSingle hPrep hFinish
  intro seed _ T
  change costNumerator (renewalSmallNext ring) (renewalSmallStop ring)
      (renewalSmallStart ring seed) T ≤
    n ^ T * (headlineReferenceRate (ceilLogTwo n) * n ^ 2)
  exact (UniformFirstHit.expectedHittingTimeAtMost_iff_cost
    (renewalSmallNext ring) (renewalSmallStop ring)
    (by omega : 0 < n) (renewalSmallStart ring seed)
    (headlineReferenceRate (ceilLogTwo n) * n ^ 2)).1
    (hstages (renewalSmallStart ring seed) seed.property) T

end L3.SmallRenewal

/-!
SMALL rootedness and actual-reference projected stage
interfaces.

The literal masked SMALL reference preserves the native projection
of every physical service. This proves unconditional rootedness
closure. Pure nativeE transport, in contrast, requires the
physical no-FIRE step and a closed reference class; these premises
are explicit in the projected singleton/preparation stage producers.

The four post-seen stage statements of SmallReferencePostSeenStageData
are NOT asserted by the projection frame alone.
-/

namespace L3.SmallRenewal

open L3
open L3.HeadlineRenewal
open Classical
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

set_option autoImplicit false
set_option Elab.async false

/-- The actual SMALL Cartesian reference, viewed through precisely
the physical native coordinates. -/
def smallReferenceNativeView {n : Nat}
    (r : RenewalSmallReference n) : TripleNativeState n :=
  nativeProjection r.1

/-- The SMALL success mask never modifies any native coordinate.
Unlike a nativeE step, this also allows a physical FIRE birth. -/
theorem smallReferenceNativeFrame {n : Nat}
    (ring : DirectedRing n) (r : RenewalSmallReference n)
    (e : Fin n) :
    smallReferenceNativeView (renewalSmallNext ring r e) =
      nativeProjection (headlinePhysicalNext ring r.1 e) := by
  change nativeProjection
      (renewalMaskedStep ring r.1 e
        (renewalSmallCut ring r.1 r.2 e)) =
    nativeProjection (headlinePhysicalNext ring r.1 e)
  exact renewalBankMaskedNativeFrame ring r.1 e
    (renewalSmallCut ring r.1 r.2 e)

/-- First conjunct of SmallReferencePostSeenStageData:
the true SMALL masked step preserves rootedness on arbitrary
Cartesian reference scratch, including all suppression branches. -/
theorem smallReferenceRootedStep {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (r : RenewalSmallReference n) (e : Fin n)
    (hroot : headlineRooted ring r.1) :
    headlineRooted ring (renewalSmallNext ring r e).1 := by
  have hphysical :=
    headlineStagesRootedStep ring hn r.1 e hroot
  have hprotected :
      Protected ring
        (smallReferenceNativeView (renewalSmallNext ring r e)) := by
    rw [smallReferenceNativeFrame ring r e]
    exact hphysical.1
  refine ⟨hprotected, ?_⟩
  obtain ⟨i, hi⟩ := hprotected.1
  exact ⟨i, hi⟩

theorem smallReferenceRootedClosed {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n) :
    ∀ r : RenewalSmallReference n,
      headlineRooted ring r.1 →
      ∀ e : Fin n,
        headlineRooted ring (renewalSmallNext ring r e).1 := by
  intro r hr e
  exact smallReferenceRootedStep ring hn r e hr

/-- Once every site has seen a fresh SMALL zero origin, the
one-bit post-cut barrier stays true on every future physical edge. -/
theorem smallReferenceSeenCompleteStep {n : Nat}
    (ring : DirectedRing n)
    (r : RenewalSmallReference n) (e : Fin n)
    (hseen : smallReferenceSeenComplete r) :
    smallReferenceSeenComplete (renewalSmallNext ring r e) := by
  intro site
  change renewalSmallMemoryNext ring r.1 r.2 e site = true
  by_cases hs : site = e
  · subst site
    simp [renewalSmallMemoryNext, hseen e]
  · by_cases hr : site = ring.rightNeighbor e
    · simp [renewalSmallMemoryNext, hs, hr, hseen e]
    · simp [renewalSmallMemoryNext, hs, hr, hseen site]

/-- A rooted post-seen cut is closed before attempting grant drain. -/
theorem smallReferenceRootedSeenClosed {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n) :
    ∀ r : RenewalSmallReference n,
      (headlineRooted ring r.1 ∧ smallReferenceSeenComplete r) →
      ∀ e : Fin n,
        headlineRooted ring (renewalSmallNext ring r e).1 ∧
          smallReferenceSeenComplete (renewalSmallNext ring r e) := by
  intro r hr e
  exact ⟨smallReferenceRootedStep ring hn r e hr.1,
    smallReferenceSeenCompleteStep ring r e hr.2⟩

/-- After the seen cut, the reference masks precisely every
OLD source success. This does not by itself eliminate OLD grants. -/
theorem smallReferenceSeenCutSuccess {n : Nat}
    (ring : DirectedRing n) (r : RenewalSmallReference n)
    (hseen : smallReferenceSeenComplete r) (e : Fin n) :
    renewalSmallCut ring r.1 r.2 e =
      (smallPair (r.1 e) (r.1 (ring.rightNeighbor e))
        (compileAdvice (ceilLogTwo n)).K).2.2 := by
  unfold renewalSmallCut
  rw [hseen e]
  rfl

/-- Physical no-FIRE transport is the *additional* premise
required to turn the masked native-frame into an exact nativeE
transition. It is not inferred from a mere seen bit. -/
theorem smallReferenceNativeStepOfPhysical {n : Nat}
    (ring : DirectedRing n) (r : RenewalSmallReference n)
    (e : Fin n)
    (hphysical :
      nativeProjection (headlinePhysicalNext ring r.1 e) =
        nativeE ring (smallReferenceNativeView r) e) :
    smallReferenceNativeView (renewalSmallNext ring r e) =
      nativeE ring (smallReferenceNativeView r) e := by
  exact (smallReferenceNativeFrame ring r e).trans hphysical

/-- The elementary nonterminal one-service cost recurrence,
duplicated locally because the renewalWordCostCons is private. -/
private theorem smallReferenceWordCostCons
    {S : Type} {n : Nat}
    (next : S → Fin n → S) (P : S → Prop) (x : S)
    (e : Fin n) (word : List (Fin n)) (hx : ¬ P x) :
    costWord next P x (e :: word) =
      1 + costWord next P (next x e) word := by
  classical
  simp only [costWord, K2FiniteSafeEliminationExpected.rawCost, if_neg hx]

/-- Exact wordwise nativeE transfer on the original SMALL reference,
conditional only on projected one-step equality and class closure. -/
theorem smallReferenceProjectedCostWord {n : Nat}
    (ring : DirectedRing n)
    (P : TripleNativeState n → Prop)
    (H : RenewalSmallReference n → Prop)
    (hstep : ∀ r, H r → ∀ e : Fin n,
      smallReferenceNativeView (renewalSmallNext ring r e) =
        nativeE ring (smallReferenceNativeView r) e)
    (hclosed : ∀ r, H r → ∀ e : Fin n,
      H (renewalSmallNext ring r e)) :
    ∀ word : List (Fin n),
      ∀ r : RenewalSmallReference n,
        H r →
        costWord (renewalSmallNext ring)
          (fun z => P (smallReferenceNativeView z)) r word =
        costWord (nativeE ring) P
          (smallReferenceNativeView r) word := by
  intro word
  induction word with
  | nil =>
      intro r _
      rfl
  | cons e tail ih =>
      intro r hr
      by_cases hp : P (smallReferenceNativeView r)
      · rw [costWord_terminal _ _ r hp (e :: tail),
          costWord_terminal _ _
            (smallReferenceNativeView r) hp (e :: tail)]
      · rw [smallReferenceWordCostCons _ _ r e tail hp,
          smallReferenceWordCostCons _ _
            (smallReferenceNativeView r) e tail hp]
        have htail := ih (renewalSmallNext ring r e)
          (hclosed r hr e)
        rw [hstep r hr e] at htail
        exact congrArg (fun v : Nat => 1 + v) htail

/-- Exact finite-horizon cost transfer uses the same IID Fin n
scheduler as the SMALL reference, not an alternate chain. -/
theorem smallReferenceProjectedCostNumerator {n : Nat}
    (ring : DirectedRing n)
    (P : TripleNativeState n → Prop)
    (H : RenewalSmallReference n → Prop)
    (hstep : ∀ r, H r → ∀ e : Fin n,
      smallReferenceNativeView (renewalSmallNext ring r e) =
        nativeE ring (smallReferenceNativeView r) e)
    (hclosed : ∀ r, H r → ∀ e : Fin n,
      H (renewalSmallNext ring r e))
    (r : RenewalSmallReference n) (hr : H r) (T : Nat) :
    costNumerator (renewalSmallNext ring)
      (fun z => P (smallReferenceNativeView z)) r T =
    costNumerator (nativeE ring) P
      (smallReferenceNativeView r) T := by
  change Prob.scheduleSum n T
      (costWord (renewalSmallNext ring)
        (fun z => P (smallReferenceNativeView z)) r) =
    Prob.scheduleSum n T
      (costWord (nativeE ring) P
        (smallReferenceNativeView r))
  have hwords :
      (costWord (renewalSmallNext ring)
        (fun z => P (smallReferenceNativeView z)) r) =
      (costWord (nativeE ring) P
        (smallReferenceNativeView r)) := by
    funext word
    exact smallReferenceProjectedCostWord
      ring P H hstep hclosed word r hr
  rw [hwords]

/-- SMALL-specific sigma_1 transfer. The native D.21
4917 n² bound and the actual closed nativeE projection are
separate hypotheses, not consequences of suppressing grants. -/
theorem smallReferenceProjectedSingletonStageOfNativeCost {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (P : TripleNativeState n → Prop)
    (H : RenewalSmallReference n → Prop)
    (hstep : ∀ r, H r → ∀ e : Fin n,
      smallReferenceNativeView (renewalSmallNext ring r e) =
        nativeE ring (smallReferenceNativeView r) e)
    (hclosed : ∀ r, H r → ∀ e : Fin n,
      H (renewalSmallNext ring r e))
    (hnative : ∀ r, H r → ∀ T,
      costNumerator (nativeE ring) P
        (smallReferenceNativeView r) T ≤
      n ^ T * (4917 * n ^ 2)) :
    StageReferenceSingleton (renewalSmallNext ring)
      H (fun z => P (smallReferenceNativeView z)) := by
  intro r hr
  apply (UniformFirstHit.expectedHittingTimeAtMost_iff_cost
    (renewalSmallNext ring)
    (fun z => P (smallReferenceNativeView z))
    (by omega : 0 < n) r (4917 * n ^ 2)).2
  intro T
  rw [smallReferenceProjectedCostNumerator
    ring P H hstep hclosed r hr T]
  exact hnative r hr T

/-- SMALL-specific sigma_p transfer, with the unrounded
doubled native H.1 cost premise and the required closed
nativeE projection. It asserts no decorated preparation yet. -/
theorem smallReferenceProjectedPreparationStageOfNativeDoubled
    {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (P : TripleNativeState n → Prop)
    (H : RenewalSmallReference n → Prop)
    (hstep : ∀ r, H r → ∀ e : Fin n,
      smallReferenceNativeView (renewalSmallNext ring r e) =
        nativeE ring (smallReferenceNativeView r) e)
    (hclosed : ∀ r, H r → ∀ e : Fin n,
      H (renewalSmallNext ring r e))
    (hnative : ∀ r, H r → ∀ T,
      2 * costNumerator (nativeE ring) P
        (smallReferenceNativeView r) T ≤
      n ^ T * (10 * n ^ 2 + n)) :
    StageReferencePreparation (renewalSmallNext ring)
      H (fun z => P (smallReferenceNativeView z)) := by
  intro r hr
  apply (UniformFirstHit.expectedHittingTimeAtMost_iff_cost
    (renewalSmallNext ring)
    (fun z => P (smallReferenceNativeView z))
    (by omega : 0 < n) r (6 * n ^ 2)).2
  intro T
  rw [smallReferenceProjectedCostNumerator
    ring P H hstep hclosed r hr T]
  exact renewalBankDoubledPreparationSix n T
    (costNumerator (nativeE ring) P
      (smallReferenceNativeView r) T)
    (by omega : 1 ≤ n) (hnative r hr T)

/-- The first conjunct no longer belongs in the unresolved bill.
Only the four genuine post-seen stage producers are parameters. -/
theorem smallReferencePostSeenStageDataOfStages {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (grantFree singleton prepared : RenewalSmallReference n → Prop)
    (hDrain : StageReferenceGrantDrain (renewalSmallNext ring)
      (fun r => headlineRooted ring r.1 ∧
        smallReferenceSeenComplete r) grantFree)
    (hSingle : StageReferenceSingleton (renewalSmallNext ring)
      grantFree singleton)
    (hPrep : StageReferencePreparation (renewalSmallNext ring)
      singleton prepared)
    (hFinish : StageReferenceGeneratedFinish (renewalSmallNext ring)
      prepared (renewalSmallStop ring)
      (headlineReferenceFinishRate (ceilLogTwo n))) :
    SmallReferencePostSeenStageData ring := by
  refine ⟨smallReferenceRootedClosed ring hn, ?_⟩
  exact ⟨grantFree, singleton, prepared,
    hDrain, hSingle, hPrep, hFinish⟩

end L3.SmallRenewal

/-!
The nativeE projection premise is audited exactly.

The SMALL mask leaves native fields equal to the PHYSICAL protocol
step, not necessarily to birth-free nativeE. Post-seen memory can
be all true independently of OLD request/grant. Consequently the
proposed unconditional rooted/seen nativeE step would imply the
same nativeE equality for EVERY rooted physical configuration,
including arbitrary Cartesian OLD tokens. No such unconditional
physical no-FIRE theorem is available from the imported prefix.

The 4917*n*n native singleton theorem is
L3.native_lift_native_singleton_cost in NativeLift.lean.
The 10*n^2+n doubled native preparation theorem is
L3.ReferencePreparationTrail.nativeSingletonPreparationDoubledCost
in ReferencePreparation.lean. Neither module is imported here.
-/

namespace L3.SmallRenewal

open L3
open L3.HeadlineRenewal
open Classical
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

set_option autoImplicit false
set_option Elab.async false

/-- Every physical Cartesian configuration admits an all-true
proof-side SMALL seen memory. The condition seenComplete alone
constrains no physical token, native, or private field. -/
theorem smallReferenceAnyPhysicalSeenComplete {n : Nat}
    (C : HeadlineConfiguration n) :
    ∃ r : RenewalSmallReference n,
      r.1 = C ∧ smallReferenceSeenComplete r := by
  refine ⟨(C, fun _ => true), rfl, ?_⟩
  intro site
  rfl

/-- No memory bit, not even a fully cleared seen barrier, affects
the native result of the very next masked SMALL service. -/
theorem smallReferenceNativeStepIgnoresMemory {n : Nat}
    (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (seen other : RenewalSmallMemory n) (e : Fin n) :
    smallReferenceNativeView
        (renewalSmallNext ring (C, seen) e) =
      smallReferenceNativeView
        (renewalSmallNext ring (C, other) e) := by
  rw [smallReferenceNativeFrame ring (C, seen) e,
    smallReferenceNativeFrame ring (C, other) e]

/-- At a literal edge, the desired nativeE equation is equivalent
to the same equation for the OLD physical headline service.
There is no stronger masked-step reduction. -/
theorem smallReferenceNativeEAtEdgeIffPhysical {n : Nat}
    (ring : DirectedRing n)
    (r : RenewalSmallReference n) (e : Fin n) :
    (smallReferenceNativeView (renewalSmallNext ring r e) =
       nativeE ring (smallReferenceNativeView r) e) ↔
    (nativeProjection (headlinePhysicalNext ring r.1 e) =
       nativeE ring (smallReferenceNativeView r) e) := by
  constructor
  · intro h
    rw [smallReferenceNativeFrame ring r e] at h
    exact h
  · intro h
    exact smallReferenceNativeStepOfPhysical ring r e h

/-- Crucial reduction: asserting a nativeE projection on ALL
rooted/seen-complete SMALL states is exactly as strong as
asserting that EVERY rooted physical service is birth-free.
An all-true memory can accompany any rooted Cartesian C. -/
theorem smallReferenceRootedSeenNativeEIffPhysicalRooted {n : Nat}
    (ring : DirectedRing n) :
    (∀ r : RenewalSmallReference n,
      (headlineRooted ring r.1 ∧ smallReferenceSeenComplete r) →
      ∀ e : Fin n,
        smallReferenceNativeView (renewalSmallNext ring r e) =
          nativeE ring (smallReferenceNativeView r) e) ↔
    (∀ C : HeadlineConfiguration n,
      headlineRooted ring C →
      ∀ e : Fin n,
        nativeProjection (headlinePhysicalNext ring C e) =
          nativeE ring (nativeProjection C) e) := by
  constructor
  · intro h C hroot e
    have hseen : smallReferenceSeenComplete
        ((C, fun _ => true) : RenewalSmallReference n) := by
      intro site
      rfl
    have hstep := h
      ((C, fun _ => true) : RenewalSmallReference n)
      ⟨hroot, hseen⟩ e
    rw [smallReferenceNativeFrame ring
      ((C, fun _ => true) : RenewalSmallReference n) e] at hstep
    exact hstep
  · intro h r hr e
    exact smallReferenceNativeStepOfPhysical ring r e
      (h r.1 hr.1 e)

/-- A pair of OLD grant-free endpoints disables every actual
F0/F1/F2 FIRE selector. No such grant-free assumption follows
merely from seenComplete or headlineRooted. -/
theorem smallReferencePairGrantFreeNoFire {n : Nat}
    (ring : DirectedRing n) (r : RenewalSmallReference n)
    (e : Fin n)
    (hx : (r.1 e).grant = false)
    (hy : (r.1 (ring.rightNeighbor e)).grant = false) :
    fireSelect (r.1 e) (r.1 (ring.rightNeighbor e))
      (certLiteralEPair (r.1 e).certNative
        (r.1 (ring.rightNeighbor e)).certNative).1
      (certLiteralEPair (r.1 e).certNative
        (r.1 (ring.rightNeighbor e)).certNative).2 = none := by
  simp [fireSelect, hx, hy]

end L3.SmallRenewal
