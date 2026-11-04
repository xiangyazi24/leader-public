import Leader.L3.Grant.BlockRenewal

/-!
Frozen-only G16 C.17 amplification audit.

Choice: R1 is the paper-faithful route. The required direct local
G13 marginal is not in the tree. The existing physical cold kernel
stops on a real grant (even with no frozen BANK success) or defect;
it is not the frozen local clamped kernel. The installed synchronization
of the regenerative BANK scanner with the clamped reference holds only
AFTER a clean start; it does not supply an arbitrary-scratch local C.3 clock.

Conditional on that precise missing local marginal, the theorem
below repairs the order-M family inequality: the coefficient is
4, independent of family length. It uses the installed frozen
negative-correlation theorem and one global G18 OR mass.

R2, in contrast, currently sums M copies of the identical
unindexed G18 first-hit indicator. The proved bound below makes
that remaining multiplicity explicit.
-/

namespace L3

open Classical
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

set_option autoImplicit false
set_option Elab.async false

/-! First failing producer, not a new assumption to the protocol.

G13 in BankTrialRenewal.lean proves a lower bound using the real
Counter.resetClockBankColdNext and the positive .grant proxy
branch. The frozen process here is the installed clamped BANK
reference starting from member.2.val's ORIGINAL scratch.
The following local-C.3/renewal bound has NOT been proved.

Source: spatial-counter.tex C.15--C.17 (roughly 607--735).
This precise producer is what a genuine R1 transfer must supply.
-/

def GrantBlockFrozenLocalColdClock
    {n : Nat} (ring : DirectedRing n)
    (member : GrantBlockFamilyMember ring)
    (R L T W : Nat) : Prop :=
  5 ≤ n →
  (compileAdvice (ceilLogTwo n)).useSmall = false →
  BankTrialLiveWindowNonalias n (ceilLogTwo n) →
  2 * (compileAdvice (ceilLogTwo n)).bankLeaseCap ≤ n →
  ((256 * R) ^ 2 ≤ n ∧ n < (256 * (R + 1)) ^ 2) →
  W = R * n / 8 →
  1024 * bankTrialRenewalWonCutoffThreshold
    n (ceilLogTwo n) ≤ L →
  W ≤ T →
  W + bankTrialRenewalIndexWindowCount
    n (ceilLogTwo n) W * L ≤ T →
  (51279921 * W) * n ^ T ≤
    grantBlockFamilyScale n *
      grantBlockFrozenProxyMass ring member T W

/-- An exact one-member scaled marginal, retaining the old
two-crossing truncated net coefficient. This deliberately
does not add a G18 mass. -/
def GrantBlockFrozenDirectMarginal
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n)
    (member : GrantBlockFamilyMember ring)
    (R T W : Nat) : Prop :=
  (((8 ^ R) * (51279921 * W) -
    2 * grantBlockFamilyScale n *
      (Density.N (badSet ring C) * 3 ^ R)) * n ^ T) ≤
    (grantBlockFamilyScale n * 8 ^ R) *
      grantBlockFrozenProxyMass ring member T W

/-- Conditional frozen marginal; the genuine missing step is
GrantBlockFrozenLocalColdClock, not any Bonferroni arithmetic. -/
theorem grantBlockFrozenDirectMarginalOfLocalClock
    {n : Nat} (ring : DirectedRing n)
    (member : GrantBlockFamilyMember ring)
    (C : HeadlineConfiguration n)
    (R L T W : Nat)
    (hn : 5 ≤ n)
    (hsp : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hw : BankTrialLiveWindowNonalias n (ceilLogTwo n))
    (hlarge :
      2 * (compileAdvice (ceilLogTwo n)).bankLeaseCap ≤ n)
    (hradius :
      (256 * R) ^ 2 ≤ n ∧ n < (256 * (R + 1)) ^ 2)
    (hW : W = R * n / 8)
    (hL : 1024 * bankTrialRenewalWonCutoffThreshold
      n (ceilLogTwo n) ≤ L)
    (hWT : W ≤ T)
    (hbudget :
      W + bankTrialRenewalIndexWindowCount
        n (ceilLogTwo n) W * L ≤ T)
    (hlocal : GrantBlockFrozenLocalColdClock
      ring member R L T W) :
    GrantBlockFrozenDirectMarginal
      ring C member R T W := by
  have hbase := hlocal hn hsp hw hlarge
    hradius hW hL hWT hbudget
  have hscale := Nat.mul_le_mul_left (8 ^ R) hbase
  change
    (((8 ^ R) * (51279921 * W) -
      2 * grantBlockFamilyScale n *
        (Density.N (badSet ring C) * 3 ^ R)) * n ^ T) ≤
      (grantBlockFamilyScale n * 8 ^ R) *
        grantBlockFrozenProxyMass ring member T W
  calc
    ((8 ^ R) * (51279921 * W) -
        2 * grantBlockFamilyScale n *
          (Density.N (badSet ring C) * 3 ^ R)) * n ^ T ≤
      ((8 ^ R) * (51279921 * W)) * n ^ T :=
        Nat.mul_le_mul_right (n ^ T) (Nat.sub_le _ _)
    _ = (8 ^ R) * ((51279921 * W) * n ^ T) := by
      simp only [Nat.mul_assoc]
    _ ≤ (8 ^ R) *
      (grantBlockFamilyScale n *
        grantBlockFrozenProxyMass ring member T W) := hscale
    _ = (grantBlockFamilyScale n * 8 ^ R) *
        grantBlockFrozenProxyMass ring member T W := by
      simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]

/-- Exchange the direct local marginal over a finite family.
There is no common G18 term in this induction. -/
private theorem grantBlockFrozenDirectFamilySum
    {α : Type} (family : List α)
    (f : α → Nat) (A B : Nat)
    (h : ∀ member, member ∈ family → A ≤ B * f member) :
    family.length * A ≤ B * (family.map f).sum := by
  induction family with
  | nil =>
      simp
  | cons x rest ih =>
      have hx : A ≤ B * f x :=
        h x List.mem_cons_self
      have ht : rest.length * A ≤
          B * (rest.map f).sum :=
        ih (fun y hy => h y (List.mem_cons_of_mem x hy))
      simp only [List.length_cons, List.map_cons, List.sum_cons,
        Nat.succ_mul, Nat.mul_add] at *
      omega

/-- One member's frozen marginal in event-mass form. -/
private theorem grantBlockFrozenDirectPerMember
    {n : Nat} (ring : DirectedRing n)
    (member : GrantBlockFamilyMember ring)
    (C : HeadlineConfiguration n)
    (R L T W : Nat)
    (hn : 5 ≤ n)
    (hsp : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hw : BankTrialLiveWindowNonalias n (ceilLogTwo n))
    (hlarge :
      2 * (compileAdvice (ceilLogTwo n)).bankLeaseCap ≤ n)
    (hradius :
      (256 * R) ^ 2 ≤ n ∧ n < (256 * (R + 1)) ^ 2)
    (hW : W = R * n / 8)
    (hL : 1024 * bankTrialRenewalWonCutoffThreshold
      n (ceilLogTwo n) ≤ L)
    (hWT : W ≤ T)
    (hbudget :
      W + bankTrialRenewalIndexWindowCount
        n (ceilLogTwo n) W * L ≤ T)
    (hlocal : GrantBlockFrozenLocalColdClock ring member R L T W) :
    (((8 ^ R) * (51279921 * W) -
      2 * grantBlockFamilyScale n *
        (Density.N (badSet ring C) * 3 ^ R)) *
      n ^ T) ≤
    (grantBlockFamilyScale n * 8 ^ R) *
      grantBlockEventMass n T
        (fun x word =>
          grantBlockFrozenProxyHit ring x (word.take W))
        member := by
  have hbound :=
    grantBlockFrozenDirectMarginalOfLocalClock
      ring member C R L T W hn hsp hw hlarge
      hradius hW hL hWT hbudget hlocal
  unfold GrantBlockFrozenDirectMarginal at hbound
  rw [grantBlockFrozenEventMassEq ring member T W]
  exact hbound

/-- The pair-union arithmetic with no common term. -/
private theorem grantBlockFrozenDirectUnionArith
    (N B A S U : Nat) (hsum : A ≤ B * S)
    (hunion : min N (2 * S) ≤ 4 * U) :
    min (B * N) (2 * A) ≤ 4 * B * U := by
  have h := grantBlockPairUnionArithmetic N B A S U 0
    (by rw [Nat.add_zero]; exact hsum) hunion
  rw [Nat.mul_zero, Nat.add_zero] at h
  exact h

/-- The frozen union is below the frozen-or-G18 mass, scaled. -/
private theorem grantBlockFrozenDirectUnionToTarget
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n)
    (family : List (GrantBlockFamilyMember ring))
    (T W B X : Nat)
    (h : X ≤ 4 * B *
      grantBlockEventUnion n T
        (fun member word =>
          grantBlockFrozenProxyHit ring member (word.take W))
        family) :
    X ≤ 4 * B * grantBlockFamilyFrozenOrG18Mass ring C family T W :=
  Nat.le_trans h (Nat.mul_le_mul_left (4 * B)
    (grantBlockFamilyFrozenUnionLeG18Target ring C family T W))

/-- The corrected C.17 **conditional** amplification.
With a frozen marginal, and the existing disjoint-support
negative correlation, the right coefficient is 4, NOT 4+2M.
All G18 credit remains a single global OR event. -/
theorem grantBlockFrozenDirectFamilyAmplification
    {n : Nat} (ring : DirectedRing n)
    (hn : 5 ≤ n)
    (hsp : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hw : BankTrialLiveWindowNonalias n (ceilLogTwo n))
    (hlarge :
      2 * (compileAdvice (ceilLogTwo n)).bankLeaseCap ≤ n)
    (C : HeadlineConfiguration n)
    (selected : List (Fin n))
    (hselected : ∀ root other : Fin n,
      root ∈ selected → other ∈ selected → root ≠ other →
      ∀ e : Fin n,
        ¬ (Counter.Support (ceilLogTwo n) ring root e ∧
          Counter.Support (ceilLogTwo n) ring other e))
    (family : List (GrantBlockFamilyMember ring))
    (hnodup : family.Nodup)
    (hfamily : ∀ member, member ∈ family →
      member.1 ∈ selected)
    (hrootDistinct : ∀ left, left ∈ family →
      ∀ right, right ∈ family → left ≠ right →
      left.1 ≠ right.1)
    (R L T W : Nat)
    (hradius :
      (256 * R) ^ 2 ≤ n ∧ n < (256 * (R + 1)) ^ 2)
    (hW : W = R * n / 8)
    (hL : 1024 * bankTrialRenewalWonCutoffThreshold
      n (ceilLogTwo n) ≤ L)
    (hWT : W ≤ T)
    (hbudget :
      W + bankTrialRenewalIndexWindowCount
        n (ceilLogTwo n) W * L ≤ T)
    (hlocal : ∀ member, member ∈ family →
      GrantBlockFrozenLocalColdClock
        ring member R L T W) :
    min
      ((grantBlockFamilyScale n * 8 ^ R) * n ^ T)
      (2 * (family.length *
        (((8 ^ R) * (51279921 * W) -
          2 * grantBlockFamilyScale n *
            (Density.N (badSet ring C) * 3 ^ R)) *
          n ^ T))) ≤
      4 * (grantBlockFamilyScale n * 8 ^ R) *
        grantBlockFamilyFrozenOrG18Mass
          ring C family T W := by
  have hper :
      ∀ member, member ∈ family →
        (((8 ^ R) * (51279921 * W) -
          2 * grantBlockFamilyScale n *
            (Density.N (badSet ring C) * 3 ^ R)) *
          n ^ T) ≤
        (grantBlockFamilyScale n * 8 ^ R) *
          grantBlockEventMass n T
            (fun x word =>
              grantBlockFrozenProxyHit ring x (word.take W))
            member := fun member hm =>
    grantBlockFrozenDirectPerMember ring member C R L T W
      hn hsp hw hlarge hradius hW hL hWT hbudget (hlocal member hm)
  have hsum := grantBlockFrozenDirectFamilySum
    family
    (grantBlockEventMass n T
      (fun member word =>
        grantBlockFrozenProxyHit ring member (word.take W)))
    (((8 ^ R) * (51279921 * W) -
      2 * grantBlockFamilyScale n *
        (Density.N (badSet ring C) * 3 ^ R)) * n ^ T)
    (grantBlockFamilyScale n * 8 ^ R) hper
  have hunion := grantBlockFamilyFrozenUnionLower
    ring (by omega : 0 < n) selected hselected family
    hnodup hfamily hrootDistinct T W hWT
  have hsingle := grantBlockFrozenDirectUnionArith
    (n ^ T) (grantBlockFamilyScale n * 8 ^ R)
    (family.length *
      (((8 ^ R) * (51279921 * W) -
        2 * grantBlockFamilyScale n *
          (Density.N (badSet ring C) * 3 ^ R)) * n ^ T))
    ((family.map (grantBlockEventMass n T
      (fun member word =>
        grantBlockFrozenProxyHit ring member
          (word.take W)))).sum)
    (grantBlockEventUnion n T
      (fun member word =>
        grantBlockFrozenProxyHit ring member (word.take W))
      family)
    hsum hunion
  exact grantBlockFrozenDirectUnionToTarget ring C family T W
    (grantBlockFamilyScale n * 8 ^ R)
    (min
      ((grantBlockFamilyScale n * 8 ^ R) * n ^ T)
      (2 * (family.length *
        (((8 ^ R) * (51279921 * W) -
          2 * grantBlockFamilyScale n *
            (Density.N (badSet ring C) * 3 ^ R)) *
          n ^ T)))) hsingle

/-! Explicit rational rate (numerator / denominator).
The truncated C.18 coefficient remains literal, with no
assertion that its positivity was discharged here. -/

def grantBlockFrozenDirectRateNumerator
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n)
    (M R W : Nat) : Nat :=
  min (grantBlockFamilyScale n * 8 ^ R)
    (2 * (M *
      ((8 ^ R) * (51279921 * W) -
        2 * grantBlockFamilyScale n *
          (Density.N (badSet ring C) * 3 ^ R))))

def grantBlockFrozenDirectRateDenominator
    (n R : Nat) : Nat :=
  4 * (grantBlockFamilyScale n * 8 ^ R)

/-- Factor a common scheduler denominator without expanding it. -/
private theorem grantBlockFrozenDirectMinFactor
    (a b N : Nat) :
    min (a * N) (b * N) = min a b * N := by
  by_cases h : a ≤ b
  · have hm := Nat.mul_le_mul_right N h
    rw [Nat.min_eq_left hm, Nat.min_eq_left h]
  · have hr : b ≤ a := by omega
    have hm := Nat.mul_le_mul_right N hr
    rw [Nat.min_eq_right hm, Nat.min_eq_right hr]

theorem grantBlockFrozenDirectExplicitRate
    {n : Nat} (ring : DirectedRing n)
    (hn : 5 ≤ n)
    (hsp : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hw : BankTrialLiveWindowNonalias n (ceilLogTwo n))
    (hlarge :
      2 * (compileAdvice (ceilLogTwo n)).bankLeaseCap ≤ n)
    (C : HeadlineConfiguration n)
    (selected : List (Fin n))
    (hselected : ∀ root other : Fin n,
      root ∈ selected → other ∈ selected → root ≠ other →
      ∀ e : Fin n,
        ¬ (Counter.Support (ceilLogTwo n) ring root e ∧
          Counter.Support (ceilLogTwo n) ring other e))
    (family : List (GrantBlockFamilyMember ring))
    (hnodup : family.Nodup)
    (hfamily : ∀ member, member ∈ family →
      member.1 ∈ selected)
    (hrootDistinct : ∀ left, left ∈ family →
      ∀ right, right ∈ family → left ≠ right →
      left.1 ≠ right.1)
    (R L T W : Nat)
    (hradius :
      (256 * R) ^ 2 ≤ n ∧ n < (256 * (R + 1)) ^ 2)
    (hW : W = R * n / 8)
    (hL : 1024 * bankTrialRenewalWonCutoffThreshold
      n (ceilLogTwo n) ≤ L)
    (hWT : W ≤ T)
    (hbudget :
      W + bankTrialRenewalIndexWindowCount
        n (ceilLogTwo n) W * L ≤ T)
    (hlocal : ∀ member, member ∈ family →
      GrantBlockFrozenLocalColdClock
        ring member R L T W) :
    grantBlockFrozenDirectRateNumerator
        ring C family.length R W * n ^ T ≤
      grantBlockFrozenDirectRateDenominator n R *
        grantBlockFamilyFrozenOrG18Mass
          ring C family T W := by
  have hmain := grantBlockFrozenDirectFamilyAmplification
    ring hn hsp hw hlarge C selected hselected family
    hnodup hfamily hrootDistinct R L T W
    hradius hW hL hWT hbudget hlocal
  have hfactor :
      min
        ((grantBlockFamilyScale n * 8 ^ R) * n ^ T)
        (2 * (family.length *
          (((8 ^ R) * (51279921 * W) -
            2 * grantBlockFamilyScale n *
              (Density.N (badSet ring C) * 3 ^ R)) *
            n ^ T))) =
      min (grantBlockFamilyScale n * 8 ^ R)
        (2 * (family.length *
          ((8 ^ R) * (51279921 * W) -
            2 * grantBlockFamilyScale n *
              (Density.N (badSet ring C) * 3 ^ R)))) *
        n ^ T := by
    calc
      _ = min
        ((grantBlockFamilyScale n * 8 ^ R) * n ^ T)
        ((2 * (family.length *
          ((8 ^ R) * (51279921 * W) -
            2 * grantBlockFamilyScale n *
              (Density.N (badSet ring C) * 3 ^ R)))) *
          n ^ T) := by
            simp only [Nat.mul_assoc]
      _ = _ := grantBlockFrozenDirectMinFactor
        (grantBlockFamilyScale n * 8 ^ R)
        (2 * (family.length *
          ((8 ^ R) * (51279921 * W) -
            2 * grantBlockFamilyScale n *
              (Density.N (badSet ring C) * 3 ^ R))))
        (n ^ T)
  rw [hfactor] at hmain
  change
    min (grantBlockFamilyScale n * 8 ^ R)
        (2 * (family.length *
          ((8 ^ R) * (51279921 * W) -
            2 * grantBlockFamilyScale n *
              (Density.N (badSet ring C) * 3 ^ R)))) *
      n ^ T ≤
    4 * (grantBlockFamilyScale n * 8 ^ R) *
      grantBlockFamilyFrozenOrG18Mass
        ring C family T W
  exact hmain

end L3
#print axioms L3.grantBlockFrozenDirectMarginalOfLocalClock
#print axioms L3.grantBlockFrozenDirectFamilyAmplification
#print axioms L3.grantBlockFrozenDirectExplicitRate
