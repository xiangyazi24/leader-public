import Leader.L3.ColdDefectCrossing
import Leader.L3.Headline.Grant

/-!
# One-scheduler block-family accounting

The literal per-root C.16/C.11 proxy lower bound is combined on the
same n-letter finite scheduler using the exact first two
inclusion-exclusion terms. The pair-intersection mass remains VISIBLE.
Static disjointness of supported edges has no probabilistic
independence consequence in the existing imports.

No false independent-clock product or unproved pair bound is used.
-/

namespace L3

open Classical
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

set_option autoImplicit false
set_option Elab.async false

/-- A finite list of physically clean grant-free cold carriers;
each item retains its own genuine root. -/
abbrev GrantBlockFamilyMember {n : Nat} (ring : DirectedRing n) :=
  Sigma (fun root : Fin n =>
    Counter.ResetClockBankColdCarrier
      (q := ceilLogTwo n) ring root)

/-- The original scheduler's authentic cold-stopped proxy
indicator BEFORE converting it to Bool. -/
noncomputable def grantBlockFamilyProxyWord
    {n : Nat} (ring : DirectedRing n)
    (hsp : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (member : GrantBlockFamilyMember ring)
    (T W : Nat) (word : List (Fin n)) : Nat :=
  bankTrialSuccessNatStoppedWord
    (Counter.resetClockBankColdNext ring member.1 hsp)
    (bankTrialRenewalColdStop ring member.1)
    (fun cut z _ suffix =>
      bankTrialRenewalColdProxyWeight
        ring member.1 W cut z suffix)
    T [] (Counter.resetClockBankColdStart
      ring member.1 member.2) word

/-- The weight at one stopped leaf is zero or one.
The result makes NO assumption about duration or independence. -/
private theorem grantBlockFamilyProxyWeightBit
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (W : Nat) (cut : List (Fin n))
    (z : Counter.ResetClockBankColdState (q := q) ring root)
    (suffix : List (Fin n)) :
    bankTrialRenewalColdProxyWeight ring root
      W cut z suffix ≤ 1 := by
  unfold bankTrialRenewalColdProxyWeight
  split <;> try omega
  all_goals split <;> try omega
  all_goals split <;> try omega
  all_goals simp [Prob.indicator] <;> split <;> omega

/-- A stopped Nat observer preserves the zero/one range of its
terminal weight. A future word uses one scheduler, not a product. -/
private theorem grantBlockFamilyStoppedBit
    {X : Type} {n : Nat}
    (next : X → Fin n → X)
    (stop : List (Fin n) → X → Bool)
    (A : List (Fin n) → X → Nat → List (Fin n) → Nat)
    (hA : ∀ pre x t suffix, A pre x t suffix ≤ 1) :
    ∀ t pre x word,
      bankTrialSuccessNatStoppedWord
        next stop A t pre x word ≤ 1 := by
  intro t pre x word
  induction word generalizing t pre x with
  | nil =>
      change (if stop pre x then A pre x t [] else 0) ≤ 1
      split
      · exact hA pre x t []
      · omega
  | cons e rest ih =>
      change
        (if stop pre x then A pre x t (e :: rest)
         else bankTrialSuccessNatStoppedWord
           next stop A (t - 1) (pre ++ [e])
             (next x e) rest) ≤ 1
      split
      · exact hA pre x t (e :: rest)
      · exact ih (t - 1) (pre ++ [e]) (next x e)

/-- The particular root proxy is a genuine 0/1 word event. -/
private theorem grantBlockFamilyProxyWordBit
    {n : Nat} (ring : DirectedRing n)
    (hsp : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (member : GrantBlockFamilyMember ring)
    (T W : Nat) (word : List (Fin n)) :
    grantBlockFamilyProxyWord ring hsp member T W word ≤ 1 := by
  unfold grantBlockFamilyProxyWord
  exact grantBlockFamilyStoppedBit
    (Counter.resetClockBankColdNext ring member.1 hsp)
    (bankTrialRenewalColdStop ring member.1)
    (fun cut z _ suffix =>
      bankTrialRenewalColdProxyWeight
        ring member.1 W cut z suffix)
    (fun cut z _ suffix =>
      grantBlockFamilyProxyWeightBit
        ring member.1 W cut z suffix)
    T [] (Counter.resetClockBankColdStart
      ring member.1 member.2) word

/-- Explicit Boolean event for the SAME original scheduler word. -/
noncomputable def grantBlockFamilyProxyHit
    {n : Nat} (ring : DirectedRing n)
    (hsp : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (member : GrantBlockFamilyMember ring)
    (T W : Nat) (word : List (Fin n)) : Bool :=
  decide (0 < grantBlockFamilyProxyWord
    ring hsp member T W word)

private theorem grantBlockFamilyProxyHitIndicator
    {n : Nat} (ring : DirectedRing n)
    (hsp : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (member : GrantBlockFamilyMember ring)
    (T W : Nat) (word : List (Fin n)) :
    (if grantBlockFamilyProxyHit ring hsp member T W word
      then 1 else 0) =
    grantBlockFamilyProxyWord ring hsp member T W word := by
  have hBit :=
    grantBlockFamilyProxyWordBit
      ring hsp member T W word
  unfold grantBlockFamilyProxyHit
  by_cases hp :
      0 < grantBlockFamilyProxyWord ring hsp member T W word
  · simp [hp]
    omega
  · simp [hp]
    omega

/-- The event numerator is exactly the already merged C.16
cold proxy mass; there is no newly assumed event lower bound. -/
theorem grantBlockFamilyProxyMassEq
    {n : Nat} (ring : DirectedRing n)
    (hsp : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (member : GrantBlockFamilyMember ring)
    (T W : Nat) :
    Prob.scheduleSum n T (fun word =>
      if grantBlockFamilyProxyHit ring hsp member T W word
      then 1 else 0) =
    bankTrialRenewalColdProxyMass
      ring member.1 hsp member.2 T W := by
  change Prob.scheduleSum n T
    (fun word =>
      if grantBlockFamilyProxyHit ring hsp member T W word
      then 1 else 0) =
    Prob.scheduleSum n T
      (fun word => grantBlockFamilyProxyWord
        ring hsp member T W word)
  apply congrArg (Prob.scheduleSum n T)
  funext word
  exact grantBlockFamilyProxyHitIndicator
    ring hsp member T W word

/-- Number of root hits in one *shared* scheduler word. -/
def grantBlockFamilyHits {α : Type}
    (hit : α → Bool) : List α → Nat
  | [] => 0
  | x :: xs =>
      (if hit x then 1 else 0) +
        grantBlockFamilyHits hit xs

/-- Whether any root fires, before any probability manipulation. -/
def grantBlockFamilyAny {α : Type}
    (hit : α → Bool) : List α → Bool
  | [] => false
  | x :: xs => hit x || grantBlockFamilyAny hit xs

/-- Exact unordered two-root intersection count on a single word.
The list order avoids Finset and does not assume independent roots. -/
def grantBlockFamilyPairs {α : Type}
    (hit : α → Bool) : List α → Nat
  | [] => 0
  | x :: xs =>
      (if hit x then grantBlockFamilyHits hit xs else 0) +
        grantBlockFamilyPairs hit xs

/-- Inclusion-exclusion to second order, pointwise for EVERY word.
No probabilistic or disjoint-support assumption occurs here. -/
private theorem grantBlockFamilyBonferroniWord
    {α : Type} (hit : α → Bool) :
    ∀ family : List α,
      grantBlockFamilyHits hit family ≤
        (if grantBlockFamilyAny hit family then 1 else 0) +
          grantBlockFamilyPairs hit family := by
  intro family
  induction family with
  | nil =>
      exact Nat.zero_le _
  | cons x xs ih =>
      cases hx : hit x with
      | false =>
          simpa [grantBlockFamilyHits, grantBlockFamilyAny,
            grantBlockFamilyPairs, hx] using ih
      | true =>
          (simp [grantBlockFamilyHits, grantBlockFamilyAny,
            grantBlockFamilyPairs, hx]) <;> omega

private theorem grantBlockFamilyScheduleZero
    (n T : Nat) :
    Prob.scheduleSum n T (fun _ : List (Fin n) => 0) = 0 := by
  change FixedSpanRenewalPayload.wordSum n T
    (fun _ : List (Fin n) => 0) = 0
  rw [← FixedSpanRenewalPayload.rawWord_sum]
  simp only [ofFn_sum_const, Nat.mul_zero]

private theorem grantBlockFamilyScheduleAdd
    (n T : Nat)
    (f g : List (Fin n) → Nat) :
    Prob.scheduleSum n T (fun word => f word + g word) =
      Prob.scheduleSum n T f + Prob.scheduleSum n T g := by
  change FixedSpanRenewalPayload.wordSum n T
    (fun word => f word + g word) =
    FixedSpanRenewalPayload.wordSum n T f +
      FixedSpanRenewalPayload.wordSum n T g
  rw [← FixedSpanRenewalPayload.rawWord_sum,
    ← FixedSpanRenewalPayload.rawWord_sum,
    ← FixedSpanRenewalPayload.rawWord_sum]
  exact ofFn_sum_add _ _

/-- Exchange list-of-roots and original-word sums.
This is double counting, NOT a factorization of the event law. -/
private theorem grantBlockFamilyScheduleHitSum
    {α : Type} (n T : Nat)
    (family : List α)
    (hit : α → List (Fin n) → Bool) :
    Prob.scheduleSum n T (fun word =>
      grantBlockFamilyHits (fun x => hit x word) family) =
    (family.map (fun x =>
      Prob.scheduleSum n T
        (fun word => if hit x word then 1 else 0))).sum := by
  induction family with
  | nil =>
      change Prob.scheduleSum n T
        (fun _ : List (Fin n) => 0) = 0
      exact grantBlockFamilyScheduleZero n T
  | cons x xs ih =>
      change Prob.scheduleSum n T
        (fun word =>
          (if hit x word then 1 else 0) +
            grantBlockFamilyHits
              (fun r => hit r word) xs) =
        Prob.scheduleSum n T
          (fun word => if hit x word then 1 else 0) +
        (xs.map (fun r =>
          Prob.scheduleSum n T
            (fun word => if hit r word then 1 else 0))).sum
      rw [grantBlockFamilyScheduleAdd, ih]

/-- FINITE-WORD discrete Bonferroni inequality for an arbitrary
family, including strongly correlated events and repeated roots. -/
theorem grantBlockFamilyBonferroniMass
    {α : Type} (n T : Nat)
    (family : List α)
    (hit : α → List (Fin n) → Bool) :
    (family.map (fun x =>
      Prob.scheduleSum n T
        (fun word => if hit x word then 1 else 0))).sum ≤
    Prob.scheduleSum n T (fun word =>
      if grantBlockFamilyAny
        (fun x => hit x word) family then 1 else 0) +
    Prob.scheduleSum n T (fun word =>
      grantBlockFamilyPairs
        (fun x => hit x word) family) := by
  have hpoint (word : List (Fin n)) :
      grantBlockFamilyHits
        (fun x => hit x word) family ≤
        (if grantBlockFamilyAny
          (fun x => hit x word) family then 1 else 0) +
        grantBlockFamilyPairs
          (fun x => hit x word) family :=
    grantBlockFamilyBonferroniWord
      (fun x => hit x word) family
  have hmass :=
    Density.schedule_sum_mono T
      (fun word => grantBlockFamilyHits
        (fun x => hit x word) family)
      (fun word =>
        (if grantBlockFamilyAny
          (fun x => hit x word) family then 1 else 0) +
        grantBlockFamilyPairs
          (fun x => hit x word) family)
      hpoint
  rw [grantBlockFamilyScheduleHitSum,
    grantBlockFamilyScheduleAdd] at hmass
  exact hmass

/-- Family union and pair-intersection masses for precisely the
merged cold proxy event, on the SAME length-T word. -/
noncomputable def grantBlockFamilyUnionMass
    {n : Nat} (ring : DirectedRing n)
    (hsp : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (family : List (GrantBlockFamilyMember ring))
    (T W : Nat) : Nat :=
  Prob.scheduleSum n T (fun word =>
    if grantBlockFamilyAny
      (fun member => grantBlockFamilyProxyHit
        ring hsp member T W word) family
    then 1 else 0)

noncomputable def grantBlockFamilyPairMass
    {n : Nat} (ring : DirectedRing n)
    (hsp : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (family : List (GrantBlockFamilyMember ring))
    (T W : Nat) : Nat :=
  Prob.scheduleSum n T (fun word =>
    grantBlockFamilyPairs
      (fun member => grantBlockFamilyProxyHit
        ring hsp member T W word) family)

/-- Coefficient from the existing C.16 cold/defect theorem. -/
def grantBlockFamilyScale (n : Nat) : Nat :=
  104857600 * (8 * (compileAdvice (ceilLogTwo n)).b + 13) *
    n * 2 ^ (compileAdvice (ceilLogTwo n)).K

/-- The genuine, defect-subtracted one-root lower numerator.
This is a Nat subtraction; positivity is NOT silently assumed. -/
def grantBlockFamilyNet
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (W radius : Nat) : Nat :=
  51279921 * W * 8 ^ radius -
    grantBlockFamilyScale n *
      (Density.N (badSet ring C) * 3 ^ radius)

/-- Combine individual inequalities over a finite list without
opening any exponential term to the arithmetic tactic. -/
private theorem grantBlockFamilyListScaledSum
    {α : Type} (family : List α)
    (f : α → Nat) (A B : Nat)
    (h : ∀ x, x ∈ family → A ≤ B * f x) :
    family.length * A ≤ B * (family.map f).sum := by
  induction family with
  | nil =>
      simp
  | cons x xs ih =>
      have hx : A ≤ B * f x :=
        h x List.mem_cons_self
      have hrest :
          xs.length * A ≤ B * (xs.map f).sum :=
        ih (fun y hy => h y (List.mem_cons_of_mem x hy))
      simp only [List.length_cons, List.map_cons, List.sum_cons,
        Nat.succ_mul, Nat.mul_add]
      omega

/-- The ACTUAL per-root C.16/C.11 bounds, over one global
configuration and one uniform discrete scheduler, yield this
second-order union estimate. EVERY per-root stochastic input is
discharged by bankTrialRenewalColdProxyMassSparseLower.

The explicit pair mass is essential: no imported theorem bounds it
at the Mp scale, even when the supports are statically disjoint.
This is therefore NOT an unconditional order-M success bound. -/
theorem grantBlockFamilySuccessMassLower
    {n : Nat} (ring : DirectedRing n)
    (hn : 5 ≤ n)
    (hsp : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hw : BankTrialLiveWindowNonalias n (ceilLogTwo n))
    (hlarge :
      2 * (compileAdvice (ceilLogTwo n)).bankLeaseCap ≤ n)
    (C : HeadlineConfiguration n)
    (family : List (GrantBlockFamilyMember ring))
    (R L T W radius : Nat)
    (hradius : (256 * R) ^ 2 ≤ n ∧
      n < (256 * (R + 1)) ^ 2)
    (hW : W = R * n / 8)
    (hL : 1024 * bankTrialRenewalWonCutoffThreshold
      n (ceilLogTwo n) ≤ L)
    (hWT : W ≤ T)
    (hbudget :
      W + bankTrialRenewalIndexWindowCount
        n (ceilLogTwo n) W * L ≤ T)
    (hCommon :
      ∀ member, member ∈ family → member.2.val = C)
    (hBuffered :
      ∀ member, member ∈ family →
        HeadlineGrantBufferedCounter
          ring C radius member.1)
    (hCrossWindow : W ≤ radius * n / 8)
    (hSmall :
      grantBlockFamilyScale n *
        (Density.N (badSet ring C) * 3 ^ radius) ≤
        51279921 * W * 8 ^ radius) :
    family.length *
      (grantBlockFamilyNet ring C W radius * n ^ T) ≤
      (grantBlockFamilyScale n * 8 ^ radius) *
        (grantBlockFamilyUnionMass ring hsp family T W +
          grantBlockFamilyPairMass ring hsp family T W) := by
  have hOne :
      ∀ member, member ∈ family →
        grantBlockFamilyNet ring C W radius * n ^ T ≤
          (grantBlockFamilyScale n * 8 ^ radius) *
            Prob.scheduleSum n T (fun word =>
              if grantBlockFamilyProxyHit
                  ring hsp member T W word then 1 else 0) := by
    intro member hm
    have hbuf :
        HeadlineGrantBufferedCounter
          ring member.2.val radius member.1 := by
      rw [hCommon member hm]
      exact hBuffered member hm
    have hs :
        (104857600 *
          (8 * (compileAdvice (ceilLogTwo n)).b + 13) *
          n * 2 ^ (compileAdvice (ceilLogTwo n)).K) *
          (Density.N (badSet ring member.2.val) *
            3 ^ radius) ≤
          51279921 * W * 8 ^ radius := by
      change grantBlockFamilyScale n *
        (Density.N (badSet ring member.2.val) *
          3 ^ radius) ≤
        51279921 * W * 8 ^ radius
      rw [hCommon member hm]
      exact hSmall
    have hRaw := bankTrialRenewalColdProxyMassSparseLower
      hn ring member.1 hsp hw hlarge member.2
      R L T W radius hradius hW hL hWT hbudget
      hbuf hCrossWindow hs
    rw [hCommon member hm] at hRaw
    change
      grantBlockFamilyNet ring C W radius * n ^ T ≤
        (grantBlockFamilyScale n * 8 ^ radius) *
          bankTrialRenewalColdProxyMass
            ring member.1 hsp member.2 T W at hRaw
    rw [← grantBlockFamilyProxyMassEq
      ring hsp member T W] at hRaw
    exact hRaw
  have hlist :
      family.length *
        (grantBlockFamilyNet ring C W radius * n ^ T) ≤
        (grantBlockFamilyScale n * 8 ^ radius) *
          (family.map (fun member =>
            Prob.scheduleSum n T (fun word =>
              if grantBlockFamilyProxyHit
                ring hsp member T W word then 1 else 0))).sum :=
    grantBlockFamilyListScaledSum family
      (fun member => Prob.scheduleSum n T (fun word =>
        if grantBlockFamilyProxyHit
          ring hsp member T W word then 1 else 0))
      (grantBlockFamilyNet ring C W radius * n ^ T)
      (grantBlockFamilyScale n * 8 ^ radius) hOne
  have hBonf :
      (family.map (fun member =>
        Prob.scheduleSum n T (fun word =>
          if grantBlockFamilyProxyHit
            ring hsp member T W word then 1 else 0))).sum ≤
      grantBlockFamilyUnionMass ring hsp family T W +
        grantBlockFamilyPairMass ring hsp family T W := by
    change
      (family.map (fun member =>
        Prob.scheduleSum n T (fun word =>
          if grantBlockFamilyProxyHit
            ring hsp member T W word then 1 else 0))).sum ≤
      Prob.scheduleSum n T (fun word =>
        if grantBlockFamilyAny
          (fun member =>
            grantBlockFamilyProxyHit ring hsp member T W word)
          family then 1 else 0) +
      Prob.scheduleSum n T (fun word =>
        grantBlockFamilyPairs
          (fun member =>
            grantBlockFamilyProxyHit ring hsp member T W word)
          family)
    exact grantBlockFamilyBonferroniMass n T family
      (fun member word =>
        grantBlockFamilyProxyHit ring hsp member T W word)
  exact Nat.le_trans hlist
    (Nat.mul_le_mul_left
      (grantBlockFamilyScale n * 8 ^ radius) hBonf)

end L3

#print axioms L3.grantBlockFamilyBonferroniMass
#print axioms L3.grantBlockFamilyProxyMassEq
#print axioms L3.grantBlockFamilySuccessMassLower
