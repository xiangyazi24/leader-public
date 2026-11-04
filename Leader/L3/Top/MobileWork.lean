import Leader.L3.LiveTopBlocks
import Leader.L3.RequestStage

/-!
Proof-side mobile TOP target work.

No protocol row is changed.
The active/doomed colors and accepted serials are proof-only
historical decorations: they cannot be recovered from bare qIn/qCarry.
This file supplies the current target functions, invariants, and
the elementary completed implications. The full colored first-match
row induction and P.7 word count remain unproved.
-/

namespace L3

set_option autoImplicit false
set_option Elab.async false

/-- Source marker is s; target marker is s+r. -/
def topMobileWidth (n : Nat) : Nat :=
  (compileAdvice (ceilLogTwo n)).rho

def topMobileSite {n : Nat} (s : Fin n) (r j : Nat) :
    Fin n :=
  certSite (certSite s r) j

def topMobileInput {n : Nat}
    (D : HeadlineConfiguration n) (s : Fin n)
    (r j : Nat) : InTok (compileAdvice (ceilLogTwo n)).topA :=
  (D (topMobileSite s r j)).qIn

def topMobileCarry {n : Nat}
    (D : HeadlineConfiguration n) (s : Fin n)
    (r j : Nat) : QCarry :=
  (D (topMobileSite s r j)).qCarry

def topMobileIsSettled {a : Nat} : InTok a → Bool
  | .S _ _ => true
  | _ => false

def topMobileIsPending {a : Nat} : InTok a → Bool
  | .P _ _ => true
  | _ => false

def topMobileIsFront {a : Nat} : InTok a → Bool
  | .X => true
  | _ => false

def topMobileIsTailSettled {a : Nat} : InTok a → Bool
  | .S _ true => true
  | _ => false

def topMobileIsLiveCarry : QCarry → Bool
  | .L _ _ => true
  | .OFF => false

def topMobileSettled {n : Nat}
    (D : HeadlineConfiguration n) (s : Fin n)
    (r j : Nat) : Bool :=
  topMobileIsSettled (topMobileInput D s r j)

def topMobilePending {n : Nat}
    (D : HeadlineConfiguration n) (s : Fin n)
    (r j : Nat) : Bool :=
  topMobileIsPending (topMobileInput D s r j)

def topMobileFront {n : Nat}
    (D : HeadlineConfiguration n) (s : Fin n)
    (r j : Nat) : Bool :=
  topMobileIsFront (topMobileInput D s r j)

def topMobileTailSettled {n : Nat}
    (D : HeadlineConfiguration n) (s : Fin n)
    (r j : Nat) : Bool :=
  topMobileIsTailSettled (topMobileInput D s r j)

def topMobileLiveCarry {n : Nat}
    (D : HeadlineConfiguration n) (s : Fin n)
    (r j : Nat) : Bool :=
  topMobileIsLiveCarry (topMobileCarry D s r j)

/-- Analytics, not physical Agent coordinates. -/
structure TopMobileColor where
  active : Nat → Bool
  serial : Nat → Option Nat
  accepted : Nat

def topMobileActive {n : Nat}
    (D : HeadlineConfiguration n) (s : Fin n)
    (r : Nat) (color : TopMobileColor) (j : Nat) : Bool :=
  if j < r then topMobileSettled D s r j && color.active j
  else false

def topMobileDoomed {n : Nat}
    (D : HeadlineConfiguration n) (s : Fin n)
    (r : Nat) (color : TopMobileColor) (j : Nat) : Bool :=
  if j < r then topMobileSettled D s r j && !(color.active j)
  else false

/-- A maximal active interval [a,b] is counted once, at b. -/
def topMobileRightCharge {n : Nat}
    (D : HeadlineConfiguration n) (s : Fin n)
    (r : Nat) (color : TopMobileColor) (j : Nat) : Nat :=
  if topMobileActive D s r color j &&
      !(topMobileActive D s r color (j + 1))
  then j + 1 else 0

/-- Paper P.6: sum of b+1 over active components. -/
def topMobileA {n : Nat}
    (D : HeadlineConfiguration n) (s : Fin n)
    (r : Nat) (color : TopMobileColor) : Nat :=
  ((List.range r).map
    (topMobileRightCharge D s r color)).sum

/-- Doomed settled count. -/
def topMobileD {n : Nat}
    (D : HeadlineConfiguration n) (s : Fin n)
    (r : Nat) (color : TopMobileColor) : Nat :=
  ((List.range r).filter
    (topMobileDoomed D s r color)).length

/-- Erasure-front count. -/
def topMobileX {n : Nat}
    (D : HeadlineConfiguration n) (s : Fin n)
    (r : Nat) : Nat :=
  ((List.range r).filter (topMobileFront D s r)).length

/-- Paper P.7: M = 2D + X. -/
def topMobileM {n : Nat}
    (D : HeadlineConfiguration n) (s : Fin n)
    (r : Nat) (color : TopMobileColor) : Nat :=
  2 * topMobileD D s r color + topMobileX D s r

/-- Unique generated carry location under invariant (ii). -/
def topMobileCarryHost {n : Nat}
    (D : HeadlineConfiguration n) (s : Fin n)
    (r : Nat) : Option Nat :=
  ((List.range r).filter (topMobileLiveCarry D s r)).head?

/-- Nonreseeding rank from the CURRENT target:
A=0 -> 0; no carry -> 1; carry facing S -> 0;
carry facing a gap/front -> 2. -/
def topMobileRho {n : Nat}
    (D : HeadlineConfiguration n) (s : Fin n)
    (r : Nat) (color : TopMobileColor) : Nat :=
  if topMobileA D s r color = 0 then 0
  else
    match topMobileCarryHost D s r with
    | none => 1
    | some j =>
        if topMobileSettled D s r (j + 1) then 0 else 2

/-- Required fixed-public, root-free complete target geometry. -/
def TopMobileFixedPair {n : Nat}
    (C D : HeadlineConfiguration n) (s : Fin n)
    (r : Nat) : Prop :=
  r = topMobileWidth n ∧
  HeadlineDigit.BadCompletePair C s ∧
  HeadlineDigit.SameCheckerPublic C D

/-- (i): pending packets lie left of all S, X and L. -/
def TopMobilePendingBarrier {n : Nat}
    (D : HeadlineConfiguration n) (s : Fin n)
    (r : Nat) : Prop :=
  ∀ i j : Nat, i < r → j < r →
    topMobilePending D s r i = true →
    (topMobileSettled D s r j = true ∨
      topMobileFront D s r j = true ∨
      topMobileLiveCarry D s r j = true) →
    i < j

/-- (i): pending serials form a consecutive accepted suffix,
newer serials physically farther left. -/
def TopMobilePendingSuffix {n : Nat}
    (D : HeadlineConfiguration n) (s : Fin n)
    (r : Nat) (color : TopMobileColor) : Prop :=
  ∃ first : Nat, first ≤ color.accepted ∧
    (∀ j : Nat, j < r →
      (topMobilePending D s r j = true ↔
        ∃ k : Nat, color.serial j = some k)) ∧
    (∀ j k : Nat, j < r → color.serial j = some k →
      first ≤ k ∧ k < color.accepted) ∧
    (∀ k : Nat, first ≤ k → k < color.accepted →
      ∃ j : Nat, j < r ∧
        topMobilePending D s r j = true ∧
        color.serial j = some k) ∧
    (∀ j k a : Nat, j < r → k < r →
      color.serial j = some a → color.serial k = some a →
      j = k) ∧
    (∀ j k a b : Nat, j < k → k < r →
      color.serial j = some a → color.serial k = some b →
      b < a)

/-- (ii): at most one L; its input is empty and every
earlier target input is E or P. -/
def TopMobileCarryExclusion {n : Nat}
    (D : HeadlineConfiguration n) (s : Fin n)
    (r : Nat) : Prop :=
  (∀ j : Nat, j < r →
    topMobileLiveCarry D s r j = true →
    topMobileInput D s r j = .E) ∧
  (∀ i j : Nat, i < r → j < r →
    topMobileLiveCarry D s r i = true →
    topMobileLiveCarry D s r j = true → i = j) ∧
  (∀ i j : Nat, i < r → j < i →
    topMobileLiveCarry D s r i = true →
    (topMobileInput D s r j = .E ∨
      topMobilePending D s r j = true))

/-- (iii): each maximal doomed S run has an X
immediately before its first site. -/
def TopMobileDoomedProtected {n : Nat}
    (D : HeadlineConfiguration n) (s : Fin n)
    (r : Nat) (color : TopMobileColor) : Prop :=
  ∀ j : Nat, j < r →
    topMobileDoomed D s r color j = true →
    (j = 0 ∨
      topMobileDoomed D s r color (j - 1) = false) →
    0 < j ∧ topMobileInput D s r (j - 1) = .X

def TopMobileAnySettled {n : Nat}
    (D : HeadlineConfiguration n) (s : Fin n)
    (r : Nat) : Prop :=
  ∃ j : Nat, j < r ∧ topMobileSettled D s r j = true

/-- Current-state part of (iv), terminal P is excluded
while any settled target input exists. -/
def TopMobileNoTerminalPending {n : Nat}
    (D : HeadlineConfiguration n) (s : Fin n)
    (r : Nat) : Prop :=
  TopMobileAnySettled D s r →
    topMobilePending D s r (r - 1) = false

def TopMobileInvariants {n : Nat}
    (D : HeadlineConfiguration n) (s : Fin n)
    (r : Nat) (color : TopMobileColor) : Prop :=
  TopMobilePendingBarrier D s r ∧
  TopMobilePendingSuffix D s r color ∧
  TopMobileCarryExclusion D s r ∧
  TopMobileDoomedProtected D s r color ∧
  TopMobileNoTerminalPending D s r

/-- Temporal part of (iv): until the first S-empty cut,
new S can only extend an OLD active run leftward;
no new terminal S is seeded. An actual row proof is pending. -/
def TopMobileNoReseedingStep {n : Nat}
    (D E : HeadlineConfiguration n) (s : Fin n)
    (r : Nat) (color : TopMobileColor) : Prop :=
  TopMobileAnySettled D s r →
    (topMobileSettled E s r (r - 1) = true →
      topMobileSettled D s r (r - 1) = true) ∧
    (∀ j : Nat, j < r →
      topMobileSettled D s r j = false →
      topMobileSettled E s r j = true →
      j + 1 < r ∧
        topMobileActive D s r color (j + 1) = true)

/-- The OLD and final checker fields defining a QC3 launch. -/
def TopMobileCarryLaunch {n : Nat}
    (D E : HeadlineConfiguration n) (s : Fin n)
    (r : Nat) (e : Fin n) : Prop :=
  e = topMobileSite s r 0 ∧
  topMobileLiveCarry D s r 0 = false ∧
  topMobileSettled D s r 0 = true ∧
  topMobileLiveCarry E s r 0 = true

/-- Candidate front contact seen at the OLD source.
Proving it effective still requires QI first-match guards. -/
def TopMobileFrontContact {n : Nat}
    (D E : HeadlineConfiguration n) (s : Fin n)
    (r : Nat) (e : Fin n) : Prop :=
  ∃ j : Nat, j < r ∧ e = topMobileSite s r j ∧
    ((topMobileFront D s r j = true ∧
        topMobileFront E s r j = false) ∨
     (0 < j ∧ topMobileTailSettled D s r j = true ∧
        topMobileFront E s r j = true))

/-- Outgoing live-carry service or new border launch. -/
def TopMobileCarryContact {n : Nat}
    (D E : HeadlineConfiguration n) (s : Fin n)
    (r : Nat) (e : Fin n) : Prop :=
  (∃ j : Nat, j < r ∧ e = topMobileSite s r j ∧
    topMobileLiveCarry D s r j = true) ∨
  TopMobileCarryLaunch D E s r e

/-- The fixed-public shadow does not change checker qIn. -/
theorem topMobileFixedInputFrame {n : Nat}
    (ring : DirectedRing n)
    (C D : HeadlineConfiguration n) (s : Fin n)
    (r j : Nat) (e : Fin n) :
    topMobileInput (topFixedPublicNext ring C D e) s r j =
      topMobileInput (headlinePhysicalNext ring D e) s r j := by
  rfl

/-- It does not change checker qCarry. -/
theorem topMobileFixedCarryFrame {n : Nat}
    (ring : DirectedRing n)
    (C D : HeadlineConfiguration n) (s : Fin n)
    (r j : Nat) (e : Fin n) :
    topMobileCarry (topFixedPublicNext ring C D e) s r j =
      topMobileCarry (headlinePhysicalNext ring D e) s r j := by
  rfl

/-- The rank takes values in {0,1,2}. -/
theorem topMobileRhoBound {n : Nat}
    (D : HeadlineConfiguration n) (s : Fin n)
    (r : Nat) (color : TopMobileColor) :
    topMobileRho D s r color ≤ 2 := by
  unfold topMobileRho
  split
  · omega
  · split
    · omega
    · split <;> omega

private theorem topMobileRightEndExists (a : Nat → Bool) :
    ∀ r : Nat, a 0 = true → a r = false →
      ∃ j : Nat, j < r ∧ a j = true ∧
        a (j + 1) = false := by
  intro r
  induction r with
  | zero =>
      intro hz hend
      rw [hz] at hend
      cases hend
  | succ r ih =>
      intro hz hend
      cases hlast : a r with
      | false =>
          obtain ⟨j, hj, ha, hb⟩ := ih hz hlast
          exact ⟨j, by omega, ha, hb⟩
      | true =>
          exact ⟨r, Nat.lt_succ_self r, hlast, hend⟩

private theorem topMobileSumMapPositive
    (f : Nat → Nat) (j : Nat) :
    ∀ xs : List Nat, j ∈ xs → 0 < f j →
      0 < (xs.map f).sum := by
  intro xs
  induction xs with
  | nil =>
      intro hj hp
      cases hj
  | cons x xs ih =>
      intro hj hp
      simp only [List.mem_cons] at hj
      cases hj with
      | inl he =>
          subst j
          simp only [List.map_cons, List.sum_cons]
          omega
      | inr he =>
          have hh := ih he hp
          simp only [List.map_cons, List.sum_cons]
          omega

/-- A component containing active border S has positive charge. -/
theorem topMobileAPositiveOfActiveBorder {n : Nat}
    (D : HeadlineConfiguration n) (s : Fin n)
    (r : Nat) (color : TopMobileColor)
    (hborder : topMobileActive D s r color 0 = true) :
    0 < topMobileA D s r color := by
  have hend : topMobileActive D s r color r = false := by
    simp [topMobileActive]
  obtain ⟨j, hj, ha, hb⟩ :=
    topMobileRightEndExists
      (topMobileActive D s r color) r hborder hend
  have hp : 0 < topMobileRightCharge D s r color j := by
    simp [topMobileRightCharge, ha, hb]
  exact topMobileSumMapPositive
    (topMobileRightCharge D s r color) j
    (List.range r) (List.mem_range.mpr hj) hp

/-- A doomed border S cannot have its mandatory left protector. -/
theorem topMobileBorderSettledActive {n : Nat}
    (D : HeadlineConfiguration n) (s : Fin n)
    (r : Nat) (color : TopMobileColor)
    (hr : 0 < r)
    (hprotect : TopMobileDoomedProtected D s r color)
    (hsettled : topMobileSettled D s r 0 = true) :
    color.active 0 = true := by
  cases hc : color.active 0 with
  | true =>
      rfl
  | false =>
      have hdoom : topMobileDoomed D s r color 0 = true := by
        simp [topMobileDoomed, hr, hsettled, hc]
      have hh := hprotect 0 hr hdoom (Or.inl rfl)
      omega

/-- No new QC3 border launch at A=0. This implication
uses the concrete OLD border S, (iii), and P.6 charge;
no private-data provenance is inferred. -/
theorem topMobileNoLaunchAtZero {n : Nat}
    (D E : HeadlineConfiguration n) (s : Fin n)
    (r : Nat) (color : TopMobileColor) (e : Fin n)
    (hr : 0 < r)
    (hprotect : TopMobileDoomedProtected D s r color)
    (hzero : topMobileA D s r color = 0) :
    ¬ TopMobileCarryLaunch D E s r e := by
  intro hlaunch
  have hsettled : topMobileSettled D s r 0 = true :=
    hlaunch.2.2.1
  have hcolor := topMobileBorderSettledActive
    D s r color hr hprotect hsettled
  have hactive : topMobileActive D s r color 0 = true := by
    simp [topMobileActive, hr, hsettled, hcolor]
  have hpositive := topMobileAPositiveOfActiveBorder
    D s r color hactive
  omega

/-- The purely algebraic rank at positive A without a carry. -/
theorem topMobileRhoNoCarry {n : Nat}
    (D : HeadlineConfiguration n) (s : Fin n)
    (r : Nat) (color : TopMobileColor)
    (hpositive : 0 < topMobileA D s r color)
    (hhost : topMobileCarryHost D s r = none) :
    topMobileRho D s r color = 1 := by
  simp [topMobileRho, Nat.ne_of_gt hpositive, hhost]

/-- The rank of a carry immediately facing S. -/
theorem topMobileRhoFacingSettled {n : Nat}
    (D : HeadlineConfiguration n) (s : Fin n)
    (r : Nat) (color : TopMobileColor) (j : Nat)
    (hpositive : 0 < topMobileA D s r color)
    (hhost : topMobileCarryHost D s r = some j)
    (hnext : topMobileSettled D s r (j + 1) = true) :
    topMobileRho D s r color = 0 := by
  simp [topMobileRho, Nat.ne_of_gt hpositive, hhost, hnext]

/-- If QC3 at fixed positive A has authenticated its
OLD no-carry and next-S effects, the rank changes 1 -> 0.
The missing literal QC3 premise is not proved here. -/
theorem topMobileRhoLaunchAlgebra {n : Nat}
    (D E : HeadlineConfiguration n) (s : Fin n)
    (r : Nat) (before after : TopMobileColor)
    (hpositive : 0 < topMobileA D s r before)
    (hfixed : topMobileA E s r after =
      topMobileA D s r before)
    (hbefore : topMobileCarryHost D s r = none)
    (hafter : topMobileCarryHost E s r = some 0)
    (hnext : topMobileSettled E s r 1 = true) :
    topMobileRho D s r before = 1 ∧
      topMobileRho E s r after = 0 := by
  refine ⟨topMobileRhoNoCarry D s r before hpositive hbefore, ?_⟩
  apply topMobileRhoFacingSettled E s r after 0
  · omega
  · exact hafter
  · exact hnext

private theorem topMobileFilterLengthLe
    (xs : List Nat) (pred : Nat → Bool) :
    (xs.filter pred).length ≤ xs.length := by
  induction xs with
  | nil =>
      simp
  | cons x xs ih =>
      cases hp : pred x with
      | false =>
          simp [List.filter_cons, hp] <;> omega
      | true =>
          simp [List.filter_cons, hp] <;> omega

/-- At most r doomed slots and r fronts; M <= 3r. -/
theorem topMobileMBound {n : Nat}
    (D : HeadlineConfiguration n) (s : Fin n)
    (r : Nat) (color : TopMobileColor) :
    topMobileM D s r color ≤ 3 * r := by
  have hd : topMobileD D s r color ≤ r := by
    have hh := topMobileFilterLengthLe
      (List.range r) (topMobileDoomed D s r color)
    simpa [topMobileD] using hh
  have hx : topMobileX D s r ≤ r := by
    have hh := topMobileFilterLengthLe
      (List.range r) (topMobileFront D s r)
    simpa [topMobileX] using hh
  unfold topMobileM
  omega

private theorem topMobileSumMapLe
    (f : Nat → Nat) (cap : Nat) :
    ∀ xs : List Nat,
      (∀ j : Nat, j ∈ xs → f j ≤ cap) →
      (xs.map f).sum ≤ xs.length * cap := by
  intro xs
  induction xs with
  | nil =>
      intro h
      simp
  | cons x xs ih =>
      intro h
      have hx : f x ≤ cap := h x (by simp)
      have hrest : ∀ j : Nat, j ∈ xs → f j ≤ cap := by
        intro j hj
        exact h j (by simp [hj])
      have hs := ih hrest
      simp only [List.map_cons, List.sum_cons, List.length_cons,
        Nat.succ_mul]
      omega

/-- P.6: A <= r*r, charging at most r per component end. -/
theorem topMobileABound {n : Nat}
    (D : HeadlineConfiguration n) (s : Fin n)
    (r : Nat) (color : TopMobileColor) :
    topMobileA D s r color ≤ r * r := by
  have ht : ∀ j : Nat, j ∈ List.range r →
      topMobileRightCharge D s r color j ≤ r := by
    intro j hj
    have hjr : j < r := List.mem_range.mp hj
    unfold topMobileRightCharge
    split <;> omega
  have hsum := topMobileSumMapLe
    (topMobileRightCharge D s r color) r
    (List.range r) ht
  simpa [topMobileA] using hsum

/-- Final P.7 arithmetic, conditional on the two real
front/carry budgets, which are NOT proved from TOP rows here. -/
theorem topMobileFiveWidthAccounting
    (r m fronts carries : Nat)
    (hdebt : m ≤ 3 * r)
    (hfronts : fronts ≤ m)
    (hcarries : carries ≤ 2 * r) :
    fronts + carries ≤ 5 * r := by
  omega

/-!
OPEN, NOT ASSERTED:
1. Authenticate the color/serial transition under every QI/QC
   first-match branch, including the post-eta entrance and the
   stop at first all-settled-empty or strict completion.
2. Show that at unchanged A, every actual selected edge has
   rho(new) <= rho(old), and a QC3 launch has the rank effects
   assumed by topMobileRhoLaunchAlgebra.
3. Show M(new) <= M(old) at unchanged A and every effective
   front contact strictly reduces M or A.
4. Bound actual carry careers by one incumbent plus one
   new QC3 launch, each with at most r outgoing contacts.
5. Count actual selected effective contacts along a word,
   prove front <= M_start and carry <= 2r, and apply
   topMobileFiveWidthAccounting to get (P.7).

Only end-cut shape invariants do NOT define the color-update
relation; treating the proof colors as arbitrary independent
recolorings would not be a valid literal-row proof.
-/

end L3


/-!
Proof-side color evolution.

The color ghost follows the SAME topFixedTraceNext selected edge,
without changing the machine, its public fields or DigitAudit.

The active/doomed and serial data are historical decorations,
not a function of the physical qIn/qCarry bytes alone.
This makes their one-step update explicit, but its preservation
from an authenticated post-eta entrance remains a row obligation.
-/

namespace L3
open K2ArbitraryElimination.FiniteAccounting

set_option autoImplicit false
set_option Elab.async false

/-- The physical incoming port edge is SOURCE offset r-1,
not target offset r-1. -/
def topMobilePortEdge {n : Nat} (s : Fin n) (r : Nat) :
    Fin n :=
  certSite s (r - 1)

/-- OLD D at the source terminal, OLD-empty target border,
and the NEW pending P: an observed genuine QO/QI port acceptance.
This test is performed on the actual selected edge. -/
def TopMobilePortAccepted {n : Nat}
    (D E : HeadlineConfiguration n) (s : Fin n)
    (r : Nat) (e : Fin n) : Prop :=
  e = topMobilePortEdge s r ∧
  topMobileInput D s r 0 = .E ∧
  topMobileCarry D s r 0 = .OFF ∧
  ∃ v : Fin (compileAdvice (ceilLogTwo n)).topA,
    ∃ tail : Bool,
      (D e).qOut = .D v tail ∧
      topMobileInput E s r 0 = .P v tail

/-- A new front X at k cuts the OLD active component at k:
either an active S-tail converted at k, or the OLD front
at k-1 advanced into an active OLD settled S at k.
The current edge is required to be the responsible source. -/
def TopMobileNewFrontCut {n : Nat}
    (D E : HeadlineConfiguration n) (s : Fin n)
    (r : Nat) (color : TopMobileColor)
    (e : Fin n) (k : Nat) : Prop :=
  0 < k ∧ k < r ∧
  topMobileActive D s r color k = true ∧
  topMobileFront E s r k = true ∧
  ((topMobileTailSettled D s r k = true ∧
      e = topMobileSite s r k) ∨
   (topMobileFront D s r (k - 1) = true ∧
      e = topMobileSite s r (k - 1)))

/-- Only the contiguous OLD active suffix to the right
of a freshly generated X becomes doomed. Do not color
across a physical gap or a different component. -/
def TopMobileDoomedByNewFront {n : Nat}
    (D E : HeadlineConfiguration n) (s : Fin n)
    (r : Nat) (color : TopMobileColor)
    (e : Fin n) (j : Nat) : Prop :=
  ∃ k : Nat,
    k < j ∧
    TopMobileNewFrontCut D E s r color e k ∧
    ∀ m : Nat, k < m → m ≤ j →
      topMobileActive D s r color m = true

/-- Ghost one-service transition, comparing the OLD and
poststep target slots.

Pending P: frame preserves serial; move inherits predecessor
serial; genuine port acceptance allocates the next serial;
settlement/deletion erases the pending label.

Settled S: OLD survivors retain their color unless a new
front cuts their contiguous OLD active component; new S
settled immediately before an OLD active run becomes active.
Consumption/erasure removes the color at that slot.

This is an analytic update on top of the actual QI/QC row.
The physical proof that every reached colored transition
is causally correct is NOT assumed or asserted below. -/
noncomputable def topMobileColorStep {n : Nat}
    (D E : HeadlineConfiguration n) (s : Fin n)
    (r : Nat) (color : TopMobileColor)
    (e : Fin n) : TopMobileColor := by
  classical
  exact
    { active := fun j =>
        if topMobileSettled E s r j then
          if topMobileSettled D s r j then
            if TopMobileDoomedByNewFront D E s r color e j then
              false
            else color.active j
          else topMobileActive D s r color (j + 1)
        else false
      serial := fun j =>
        if topMobilePending E s r j then
          if topMobilePending D s r j then
            color.serial j
          else if j = 0 then
            if TopMobilePortAccepted D E s r e then
              some color.accepted
            else none
          else if e = topMobileSite s r (j - 1) ∧
              topMobilePending D s r (j - 1) = true then
            color.serial (j - 1)
          else none
        else none
      accepted := color.accepted +
        if TopMobilePortAccepted D E s r e then 1 else 0 }

/-- TOP fixed-public trace paired with proof-only color. -/
abbrev TopMobileColoredTraceState (n : Nat) :=
  TopFixedTraceState n × TopMobileColor

/-- One original scheduler edge, exactly once, and then the
color update read from its OLD and poststep physical slots. -/
noncomputable def topMobileColoredTraceNext {n : Nat}
    (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (s : Fin n) (r : Nat)
    (Z : TopMobileColoredTraceState n)
    (e : Fin n) : TopMobileColoredTraceState n :=
  (topFixedTraceNext ring C Z.1 e,
    topMobileColorStep Z.1.1.1
      (topFixedTraceNext ring C Z.1 e).1.1
      s r Z.2 e)

/-- Keep the original physical/audit initial cut. -/
def topMobileColoredTraceStart {n : Nat}
    (C : HeadlineConfiguration n) (color : TopMobileColor) :
    TopMobileColoredTraceState n :=
  (((C, digitAuditInitial (piD C)), []), color)

/-- The original uniform Fin n word, without accelerated
support-only or independently resampled ghost edges. -/
noncomputable def topMobileColoredTraceRun {n : Nat}
    (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (s : Fin n) (r : Nat)
    (Z : TopMobileColoredTraceState n)
    (word : List (Fin n)) : TopMobileColoredTraceState n :=
  word.foldl (topMobileColoredTraceNext ring C s r) Z

/-- Exact one-step projection to RequestStage's TOP observer. -/
theorem topMobileColoredTraceProjection {n : Nat}
    (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (s : Fin n) (r : Nat)
    (Z : TopMobileColoredTraceState n) (e : Fin n) :
    (topMobileColoredTraceNext ring C s r Z e).1 =
      topFixedTraceNext ring C Z.1 e := by
  rfl

/-- Exact projection on every selected-edge word. -/
theorem topMobileColoredTraceRunProjection {n : Nat}
    (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (s : Fin n) (r : Nat)
    (word : List (Fin n))
    (Z : TopMobileColoredTraceState n) :
    (topMobileColoredTraceRun ring C s r Z word).1 =
      word.foldl (topFixedTraceNext ring C) Z.1 := by
  induction word generalizing Z with
  | nil =>
      rfl
  | cons e es ih =>
      change
        (topMobileColoredTraceRun ring C s r
          (topMobileColoredTraceNext ring C s r Z e) es).1 =
        es.foldl (topFixedTraceNext ring C)
          (topFixedTraceNext ring C Z.1 e)
      rw [ih]
      rfl

/-- Stopped costs transfer to the colored ghost:
the target is the PULLBACK of the same strict terminal,
not a relaxed or independently selected checker target. -/
theorem topMobileColoredCostLift {n : Nat}
    (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (s : Fin n) (r : Nat)
    (Z : TopMobileColoredTraceState n) (T : Nat) :
    costNumerator (topFixedTraceNext ring C)
        (topFixedStrictStop ring C s) Z.1 T ≤
      costNumerator (topMobileColoredTraceNext ring C s r)
        (fun F => topFixedStrictStop ring C s F.1) Z T := by
  exact Prob.costNumerator_ghost_target_le
    (topFixedTraceNext ring C)
    (topMobileColoredTraceNext ring C s r)
    (by intro F e; rfl)
    (topFixedStrictStop ring C s)
    (fun F => topFixedStrictStop ring C s F.1)
    (by intro F h; exact h)
    Z T

/-!
The following are finished GHOST-UPDATE algebra lemmas
conditional on the displayed OLD/poststep slot effects.
They are not substitutions for literal TOP first-match row
proofs establishing those effects in every reached state.
-/

/-- An unrelated edge or blocked offer cannot allocate a serial. -/
theorem topMobileColorAcceptedFrame {n : Nat}
    (D E : HeadlineConfiguration n) (s : Fin n)
    (r : Nat) (color : TopMobileColor) (e : Fin n)
    (hno : ¬ TopMobilePortAccepted D E s r e) :
    (topMobileColorStep D E s r color e).accepted =
      color.accepted := by
  classical
  simp [topMobileColorStep, hno]

/-- The actual accepted port packet allocates one new serial. -/
theorem topMobileColorAcceptedNew {n : Nat}
    (D E : HeadlineConfiguration n) (s : Fin n)
    (r : Nat) (color : TopMobileColor) (e : Fin n)
    (hyes : TopMobilePortAccepted D E s r e) :
    (topMobileColorStep D E s r color e).accepted =
      color.accepted + 1 := by
  classical
  simp [topMobileColorStep, hyes]

/-- OLD pending P that frames on this edge retains its serial. -/
theorem topMobileColorPendingFrame {n : Nat}
    (D E : HeadlineConfiguration n) (s : Fin n)
    (r : Nat) (color : TopMobileColor) (e : Fin n)
    (j : Nat)
    (hold : topMobilePending D s r j = true)
    (hnew : topMobilePending E s r j = true) :
    (topMobileColorStep D E s r color e).serial j =
      color.serial j := by
  classical
  simp [topMobileColorStep, hold, hnew]

/-- QI movement into an OLD nonpending input inherits the
serial at the OLD physical predecessor, never a new one. -/
theorem topMobileColorPendingMove {n : Nat}
    (D E : HeadlineConfiguration n) (s : Fin n)
    (r : Nat) (color : TopMobileColor) (e : Fin n)
    (j : Nat) (hj : 0 < j)
    (hold : topMobilePending D s r j = false)
    (hnew : topMobilePending E s r j = true)
    (he : e = topMobileSite s r (j - 1))
    (hsource : topMobilePending D s r (j - 1) = true) :
    (topMobileColorStep D E s r color e).serial j =
      color.serial (j - 1) := by
  classical
  simp [topMobileColorStep, hold, hnew,
    Nat.ne_of_gt hj, he, hsource]

/-- QO/QI accepted border P obtains the next new serial. -/
theorem topMobileColorPortSerial {n : Nat}
    (D E : HeadlineConfiguration n) (s : Fin n)
    (r : Nat) (color : TopMobileColor) (e : Fin n)
    (hold : topMobilePending D s r 0 = false)
    (hnew : topMobilePending E s r 0 = true)
    (haccept : TopMobilePortAccepted D E s r e) :
    (topMobileColorStep D E s r color e).serial 0 =
      some color.accepted := by
  classical
  simp [topMobileColorStep, hold, hnew, haccept]

/-- QI pending settlement or deletion erases the pending serial. -/
theorem topMobileColorPendingGone {n : Nat}
    (D E : HeadlineConfiguration n) (s : Fin n)
    (r : Nat) (color : TopMobileColor) (e : Fin n)
    (j : Nat)
    (hgone : topMobilePending E s r j = false) :
    (topMobileColorStep D E s r color e).serial j =
      none := by
  classical
  simp [topMobileColorStep, hgone]

/-- A P settling immediately before active S attaches to the
same OLD active component, not a new component at the right. -/
theorem topMobileColorSettles {n : Nat}
    (D E : HeadlineConfiguration n) (s : Fin n)
    (r : Nat) (color : TopMobileColor) (e : Fin n)
    (j : Nat)
    (hold : topMobileSettled D s r j = false)
    (hnew : topMobileSettled E s r j = true) :
    (topMobileColorStep D E s r color e).active j =
      topMobileActive D s r color (j + 1) := by
  classical
  simp [topMobileColorStep, hold, hnew]

/-- Unchanged settled input outside an advancing front's
OLD contiguous component retains its old activity color. -/
theorem topMobileColorSettledFrame {n : Nat}
    (D E : HeadlineConfiguration n) (s : Fin n)
    (r : Nat) (color : TopMobileColor) (e : Fin n)
    (j : Nat)
    (hold : topMobileSettled D s r j = true)
    (hnew : topMobileSettled E s r j = true)
    (hnot : ¬ TopMobileDoomedByNewFront
      D E s r color e j) :
    (topMobileColorStep D E s r color e).active j =
      color.active j := by
  classical
  simp [topMobileColorStep, hold, hnew, hnot]

/-- OLD active right suffix of a fresh front changes to doomed. -/
theorem topMobileColorDoomedByFront {n : Nat}
    (D E : HeadlineConfiguration n) (s : Fin n)
    (r : Nat) (color : TopMobileColor) (e : Fin n)
    (j : Nat)
    (hold : topMobileSettled D s r j = true)
    (hnew : topMobileSettled E s r j = true)
    (hcut : TopMobileDoomedByNewFront
      D E s r color e j) :
    (topMobileColorStep D E s r color e).active j =
      false := by
  classical
  simp [topMobileColorStep, hold, hnew, hcut]

/-- Consumed S (QC launch/advance, QI front clearing)
has no surviving active color. -/
theorem topMobileColorSettledGone {n : Nat}
    (D E : HeadlineConfiguration n) (s : Fin n)
    (r : Nat) (color : TopMobileColor) (e : Fin n)
    (j : Nat)
    (hgone : topMobileSettled E s r j = false) :
    (topMobileColorStep D E s r color e).active j =
      false := by
  classical
  simp [topMobileColorStep, hgone]

/-- OLD active tail conversion to X cuts the active suffix. -/
theorem topMobileColorTailConversionDooms {n : Nat}
    (D E : HeadlineConfiguration n) (s : Fin n)
    (r : Nat) (color : TopMobileColor) (e : Fin n)
    (k j : Nat)
    (hk : 0 < k) (hkr : k < r) (hkj : k < j)
    (hactive : topMobileActive D s r color k = true)
    (htail : topMobileTailSettled D s r k = true)
    (hfront : topMobileFront E s r k = true)
    (he : e = topMobileSite s r k)
    (hspan : ∀ m : Nat, k < m → m ≤ j →
      topMobileActive D s r color m = true)
    (hold : topMobileSettled D s r j = true)
    (hnew : topMobileSettled E s r j = true) :
    (topMobileColorStep D E s r color e).active j =
      false := by
  apply topMobileColorDoomedByFront
    D E s r color e j hold hnew
  exact ⟨k, hkj,
    ⟨hk, hkr, hactive, hfront, Or.inl ⟨htail, he⟩⟩,
    hspan⟩

/-- OLD X at k-1 advances into active S_k and dooms its
remaining contiguous OLD active suffix to the right. -/
theorem topMobileColorFrontAdvanceDooms {n : Nat}
    (D E : HeadlineConfiguration n) (s : Fin n)
    (r : Nat) (color : TopMobileColor) (e : Fin n)
    (k j : Nat)
    (hk : 0 < k) (hkr : k < r) (hkj : k < j)
    (hactive : topMobileActive D s r color k = true)
    (holdFront : topMobileFront D s r (k - 1) = true)
    (hfront : topMobileFront E s r k = true)
    (he : e = topMobileSite s r (k - 1))
    (hspan : ∀ m : Nat, k < m → m ≤ j →
      topMobileActive D s r color m = true)
    (hold : topMobileSettled D s r j = true)
    (hnew : topMobileSettled E s r j = true) :
    (topMobileColorStep D E s r color e).active j =
      false := by
  apply topMobileColorDoomedByFront
    D E s r color e j hold hnew
  exact ⟨k, hkj,
    ⟨hk, hkr, hactive, hfront,
      Or.inr ⟨holdFront, he⟩⟩,
    hspan⟩

/-!
OPEN: not asserted as theorems.

1. Authentication of the initial colored post-eta state, from
   the first true port-accepted tail and retirement of inherited
   moving qIn/qCarry lineages. Arbitrary Cartesian pre-eta
   scratch does not supply this color/serial certificate.

2. Each QI/QC first-match row's precise OLD/NEW slot effects,
   including carry-host cleanup, new X conversion, front
   movement/abort, QC3 launch, QC2 success/abort/retire,
   terminal P, port responder reservation and unrelated edges,
   and preservation of invariants (i)-(iv) under these steps.
   The existing HeadlineDigit.checkerPhysicalCarryAdvance
   and checkerPhysicalCarryLaunch prove only the carry field
   part of the necessary colored equations.

3. Rowwise descent at fixed A: rho(new) <= rho(old);
   a QC3 launch 1 -> 0; M(new) <= M(old);
   every effective front contact reduces M or A.
   The lemmas above prove ghost-coordinate effects when
   their OLD/new field premises are supplied. They do not
   themselves prove the protocol has those effects.

4. The stopped word count with at most one incumbent and
   one newly launched carry, <= 2r carry contacts, <= 3r
   front contacts, and P.7 <= 5r by
   topMobileFiveWidthAccounting.

The exact uncolored trace projection and cost lift do NOT
establish these still-open structural progress statements.
-/

end L3


/-!
Literal TOP pair-field audit.

The independent physical source and responder endpoint lemmas
below use the true protocol-step frame, not a definitional
identification of HeadlineConfiguration with Fin n -> Agent.

All checker QI/QC/QO guards refer to OLD fields. LIVE-TOP
alone reads the SI-resolved betas for its independent writer
lane; its QI/QC/QO checker guards still read OLD beta.

The actual post-eta color/history closure and full P.7
count are separate tasks and are not asserted.
-/

namespace L3

set_option autoImplicit false
set_option Elab.async false

/-- The exact OLD pair passed to CertRows.liveTopPair by
certificateStep, including the independent SI beta outputs.
The checker guards still read the original x/y beta fields. -/
def topMobileLiteralTopOwner {n : Nat}
    (ring : DirectedRing n)
    (D : HeadlineConfiguration n) (e : Fin n) :
    TopResult (compileAdvice (ceilLogTwo n)) :=
  let c := compileAdvice (ceilLogTwo n)
  let x := D e
  let y := D (ring.rightNeighbor e)
  let post := postEInfo x y
  let ser := serializerStep c x y post
  let si := siStep c x y post ser.hard
  liveTopPair c x y si.betaX si.betaY

/-- The physical source checker fields coincide with the
exact OLD TOP owner. There is no simplification of an
abstract HeadlineConfiguration into a function. -/
theorem topMobileLiteralSourceFields {n : Nat}
    (ring : DirectedRing n)
    (C D : HeadlineConfiguration n) (e : Fin n) :
    (topFixedPublicNext ring C D e e).qIn =
        (topMobileLiteralTopOwner ring D e).x.qIn ∧
    (topFixedPublicNext ring C D e e).qCarry =
        (topMobileLiteralTopOwner ring D e).x.qCarry ∧
    (topFixedPublicNext ring C D e e).qOut =
        (topMobileLiteralTopOwner ring D e).x.qOut := by
  have hsource := headlineRendezvousStepAtSource ring D e
  have hi := congrArg
    (fun a : Agent (compileAdvice (ceilLogTwo n)) => a.qIn) hsource
  have hc := congrArg
    (fun a : Agent (compileAdvice (ceilLogTwo n)) => a.qCarry) hsource
  have ho := congrArg
    (fun a : Agent (compileAdvice (ceilLogTwo n)) => a.qOut) hsource
  refine ⟨?_, ?_, ?_⟩
  · change ((headlinePhysicalNext ring D e) e).qIn = _
    exact hi
  · change ((headlinePhysicalNext ring D e) e).qCarry = _
    exact hc
  · change ((headlinePhysicalNext ring D e) e).qOut = _
    exact ho

/-- The analogous real responder fields. The physical
edge endpoints are distinct for n >= 2. -/
theorem topMobileLiteralResponderFields {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (C D : HeadlineConfiguration n) (e : Fin n) :
    (topFixedPublicNext ring C D e
       (ring.rightNeighbor e)).qIn =
        (topMobileLiteralTopOwner ring D e).y.qIn ∧
    (topFixedPublicNext ring C D e
       (ring.rightNeighbor e)).qCarry =
        (topMobileLiteralTopOwner ring D e).y.qCarry ∧
    (topFixedPublicNext ring C D e
       (ring.rightNeighbor e)).qOut =
        (topMobileLiteralTopOwner ring D e).y.qOut := by
  have hresponder :=
    headlineRendezvousStepAtResponder ring hn D e
  have hi := congrArg
    (fun a : Agent (compileAdvice (ceilLogTwo n)) => a.qIn)
    hresponder
  have hc := congrArg
    (fun a : Agent (compileAdvice (ceilLogTwo n)) => a.qCarry)
    hresponder
  have ho := congrArg
    (fun a : Agent (compileAdvice (ceilLogTwo n)) => a.qOut)
    hresponder
  refine ⟨?_, ?_, ?_⟩
  · change ((headlinePhysicalNext ring D e)
        (ring.rightNeighbor e)).qIn = _
    exact hi
  · change ((headlinePhysicalNext ring D e)
        (ring.rightNeighbor e)).qCarry = _
    exact hc
  · change ((headlinePhysicalNext ring D e)
        (ring.rightNeighbor e)).qOut = _
    exact ho

/-- All OTHER physical sites frame the three checker
private fields. The fixed-public step may restore l/u/beta/d,
so full-Agent equality with D i is not the right claim. -/
theorem topMobileLiteralAwayFields {n : Nat}
    (ring : DirectedRing n)
    (C D : HeadlineConfiguration n) (e i : Fin n)
    (he : i ≠ e) (hy : i ≠ ring.rightNeighbor e) :
    (topFixedPublicNext ring C D e i).qIn = (D i).qIn ∧
    (topFixedPublicNext ring C D e i).qCarry = (D i).qCarry ∧
    (topFixedPublicNext ring C D e i).qOut = (D i).qOut := by
  have haw := headlineRendezvousStepAway ring D e i he hy
  have hi := congrArg
    (fun a : Agent (compileAdvice (ceilLogTwo n)) => a.qIn) haw
  have hc := congrArg
    (fun a : Agent (compileAdvice (ceilLogTwo n)) => a.qCarry) haw
  have ho := congrArg
    (fun a : Agent (compileAdvice (ceilLogTwo n)) => a.qOut) haw
  refine ⟨?_, ?_, ?_⟩
  · change ((headlinePhysicalNext ring D e) i).qIn = (D i).qIn
    exact hi
  · change ((headlinePhysicalNext ring D e) i).qCarry = (D i).qCarry
    exact hc
  · change ((headlinePhysicalNext ring D e) i).qOut = (D i).qOut
    exact ho

/-! The following pure first-match QI branch lemmas return
BOTH updated endpoints. Their OLD guard hypotheses prevent
a higher-priority carry-host or root override. -/

/-- QI pending P moves into an OLD-empty internal target.
Neither P is cloned nor an old settled byte invented. -/
theorem topMobileOwnerQIPendingMove
    (c : Compiled) (x y : Agent c)
    (resolvedX resolvedY : Bool)
    (v : Fin c.topA) (tail : Bool)
    (hxl : x.l = false) (hyl : y.l = false)
    (hxc : x.qCarry = .OFF) (hyc : y.qCarry = .OFF)
    (hxi : x.qIn = .P v tail) (hyi : y.qIn = .E)
    (hyb : y.beta = false) :
    (liveTopPair c x y resolvedX resolvedY).x.qIn = .E ∧
    (liveTopPair c x y resolvedX resolvedY).y.qIn =
      .P v tail := by
  try simp only [liveTopPair_x_wIn, liveTopPair_y_wIn, liveTopPair_x_wCarry, liveTopPair_y_wCarry,
    liveTopPair_x_wOut, liveTopPair_y_wOut, liveTopPair_x_qIn, liveTopPair_y_qIn,
    liveTopPair_x_qCarry, liveTopPair_y_qCarry, liveTopPair_x_qOut, liveTopPair_y_qOut] at *
  simp [liveTopPair, liveTopWC, liveTopWI, liveTopWO, liveTopQC,
      liveTopQI, liveTopQO, hxl, hyl, hxc, hyc,
    hxi, hyi, hyb, topTerminal, topInternal,
    topBorder, QCarry.isOff, QCarry.isL,
    InTok.isP, InTok.isS, InTok.isX, InTok.isE,
    inT, inV]

/-- QI P settles immediately before an OLD settled
internal responder. The responder's OLD S is framed. -/
theorem topMobileOwnerQIPendingSettles
    (c : Compiled) (x y : Agent c)
    (resolvedX resolvedY : Bool)
    (v w : Fin c.topA) (tail nextTail : Bool)
    (hxl : x.l = false) (hyl : y.l = false)
    (hxc : x.qCarry = .OFF) (hyc : y.qCarry = .OFF)
    (hxi : x.qIn = .P v tail)
    (hyi : y.qIn = .S w nextTail)
    (hyb : y.beta = false) :
    (liveTopPair c x y resolvedX resolvedY).x.qIn =
      .S v tail ∧
    (liveTopPair c x y resolvedX resolvedY).y.qIn =
      .S w nextTail := by
  try simp only [liveTopPair_x_wIn, liveTopPair_y_wIn, liveTopPair_x_wCarry, liveTopPair_y_wCarry,
    liveTopPair_x_wOut, liveTopPair_y_wOut, liveTopPair_x_qIn, liveTopPair_y_qIn,
    liveTopPair_x_qCarry, liveTopPair_y_qCarry, liveTopPair_x_qOut, liveTopPair_y_qOut] at *
  simp [liveTopPair, liveTopWC, liveTopWI, liveTopWO, liveTopQC,
      liveTopQI, liveTopQO, hxl, hyl, hxc, hyc,
    hxi, hyi, hyb, topTerminal, topInternal,
    topBorder, QCarry.isOff, QCarry.isL,
    InTok.isP, InTok.isS, InTok.isX, InTok.isE,
    inT, inV]

/-- QI internal OLD nonborder tail becomes X, no
second X-advance microstep on the same selected edge.
This reuses the existing owner theorem. -/
theorem topMobileOwnerQITailConverts
    (c : Compiled) (x y : Agent c)
    (resolvedX resolvedY : Bool)
    (v : Fin c.topA)
    (hxl : x.l = false) (hyl : y.l = false)
    (hxb : x.beta = false) (hyb : y.beta = false)
    (hxc : x.qCarry = .OFF) (hyc : y.qCarry = .OFF)
    (hxi : x.qIn = .S v true) (hyi : y.qIn = .E) :
    (liveTopPair c x y resolvedX resolvedY).x.qIn = .X := by
  exact HeadlineDigit.checkerOwnerInternalTailBecomesX
    c x y resolvedX resolvedY v
    hxl hyl hxb hyb hxc hyc hxi hyi

/-- QI front X advances into an OLD internal S.
Its old source clears; its responder becomes X. -/
theorem topMobileOwnerQIFrontAdvances
    (c : Compiled) (x y : Agent c)
    (resolvedX resolvedY : Bool)
    (v : Fin c.topA) (tail : Bool)
    (hxl : x.l = false) (hyl : y.l = false)
    (hxc : x.qCarry = .OFF) (hyc : y.qCarry = .OFF)
    (hxi : x.qIn = .X) (hyi : y.qIn = .S v tail)
    (hyb : y.beta = false) :
    (liveTopPair c x y resolvedX resolvedY).x.qIn = .E ∧
    (liveTopPair c x y resolvedX resolvedY).y.qIn = .X := by
  try simp only [liveTopPair_x_wIn, liveTopPair_y_wIn, liveTopPair_x_wCarry, liveTopPair_y_wCarry,
    liveTopPair_x_wOut, liveTopPair_y_wOut, liveTopPair_x_qIn, liveTopPair_y_qIn,
    liveTopPair_x_qCarry, liveTopPair_y_qCarry, liveTopPair_x_qOut, liveTopPair_y_qOut] at *
  simp [liveTopPair, liveTopWC, liveTopWI, liveTopWO, liveTopQC,
      liveTopQI, liveTopQO, hxl, hyl, hxc, hyc,
    hxi, hyi, hyb, topInternal, topTerminal,
    QCarry.isOff, QCarry.isL, InTok.isX,
    InTok.isS, InTok.isP, inT]

/-- QI X reaching an empty internal responder retires
without conjuring a new settled input or a new front. -/
theorem topMobileOwnerQIFrontDies
    (c : Compiled) (x y : Agent c)
    (resolvedX resolvedY : Bool)
    (hxl : x.l = false) (hyl : y.l = false)
    (hxc : x.qCarry = .OFF) (hyc : y.qCarry = .OFF)
    (hxi : x.qIn = .X) (hyi : y.qIn = .E)
    (hyb : y.beta = false) :
    (liveTopPair c x y resolvedX resolvedY).x.qIn = .E ∧
    (liveTopPair c x y resolvedX resolvedY).y.qIn = .E := by
  try simp only [liveTopPair_x_wIn, liveTopPair_y_wIn, liveTopPair_x_wCarry, liveTopPair_y_wCarry,
    liveTopPair_x_wOut, liveTopPair_y_wOut, liveTopPair_x_qIn, liveTopPair_y_qIn,
    liveTopPair_x_qCarry, liveTopPair_y_qCarry, liveTopPair_x_qOut, liveTopPair_y_qOut] at *
  simp [liveTopPair, liveTopWC, liveTopWI, liveTopWO, liveTopQC,
      liveTopQI, liveTopQO, hxl, hyl, hxc, hyc,
    hxi, hyi, hyb, topInternal, topTerminal,
    QCarry.isOff, QCarry.isL, InTok.isX,
    InTok.isS, InTok.isP]

/-- QI front merger: old source X disappears, while
the already-present resident X remains at the target. -/
theorem topMobileOwnerQIFrontMerges
    (c : Compiled) (x y : Agent c)
    (resolvedX resolvedY : Bool)
    (hxl : x.l = false) (hyl : y.l = false)
    (hxc : x.qCarry = .OFF) (hyc : y.qCarry = .OFF)
    (hxi : x.qIn = .X) (hyi : y.qIn = .X)
    (hyb : y.beta = false) :
    (liveTopPair c x y resolvedX resolvedY).x.qIn = .E ∧
    (liveTopPair c x y resolvedX resolvedY).y.qIn = .X := by
  try simp only [liveTopPair_x_wIn, liveTopPair_y_wIn, liveTopPair_x_wCarry, liveTopPair_y_wCarry,
    liveTopPair_x_wOut, liveTopPair_y_wOut, liveTopPair_x_qIn, liveTopPair_y_qIn,
    liveTopPair_x_qCarry, liveTopPair_y_qCarry, liveTopPair_x_qOut, liveTopPair_y_qOut] at *
  simp [liveTopPair, liveTopWC, liveTopWI, liveTopWO, liveTopQC,
      liveTopQI, liveTopQO, hxl, hyl, hxc, hyc,
    hxi, hyi, hyb, topInternal, topTerminal,
    QCarry.isOff, QCarry.isL, InTok.isX,
    InTok.isS, InTok.isP]

/-- QI OLD carry-host cleanup wins over P settlement,
tail conversion, and all later input first-match rows. -/
theorem topMobileOwnerQICarryHostClears
    (c : Compiled) (x y : Agent c)
    (resolvedX resolvedY : Bool)
    (carry error : Bool)
    (hxl : x.l = false) (hyl : y.l = false)
    (hxc : x.qCarry = .L carry error)
    (hyc : y.qCarry = .OFF) (hyi : y.qIn = .E)
    (hyb : y.beta = false) :
    (liveTopPair c x y resolvedX resolvedY).x.qIn = .E := by
  try simp only [liveTopPair_x_wIn, liveTopPair_y_wIn, liveTopPair_x_wCarry, liveTopPair_y_wCarry,
    liveTopPair_x_wOut, liveTopPair_y_wOut, liveTopPair_x_qIn, liveTopPair_y_qIn,
    liveTopPair_x_qCarry, liveTopPair_y_qCarry, liveTopPair_x_qOut, liveTopPair_y_qOut] at *
  simp [liveTopPair, liveTopWC, liveTopWI, liveTopWO, liveTopQC,
      liveTopQI, liveTopQO, hxl, hyl, hxc, hyc,
    hyi, hyb, QCarry.isOff, QCarry.isL,
    InTok.isS, InTok.isX, InTok.isP,
    topTerminal, topInternal]

/-! QC always uses the OLD source carry and OLD destination S.
The checker carry-field lemmas are reused for its
new live values; the QI consumption must be shown separately. -/

/-- QC3: border settled S launches a carry and the
source QI slot is consumed into E on that same edge. -/
theorem topMobileOwnerQCLaunch
    (c : Compiled) (x y : Agent c)
    (resolvedX resolvedY : Bool)
    (v : Fin c.topA) (tail : Bool)
    (hxl : x.l = false) (hyl : y.l = false)
    (hxb : x.beta = true)
    (hxc : x.qCarry = .OFF)
    (hxi : x.qIn = .S v tail) :
    (liveTopPair c x y resolvedX resolvedY).x.qIn = .E ∧
    (liveTopPair c x y resolvedX resolvedY).x.qCarry =
      .L (HeadlineDigit.checkerCarryNext c (true, false)
        v x.d).1
        (HeadlineDigit.checkerCarryNext c (true, false)
        v x.d).2 := by
  try simp only [liveTopPair_x_wIn, liveTopPair_y_wIn, liveTopPair_x_wCarry, liveTopPair_y_wCarry,
    liveTopPair_x_wOut, liveTopPair_y_wOut, liveTopPair_x_qIn, liveTopPair_y_qIn,
    liveTopPair_x_qCarry, liveTopPair_y_qCarry, liveTopPair_x_qOut, liveTopPair_y_qOut] at *
  refine ⟨?_, ?_⟩
  · cases hyc : y.qCarry <;>
      simp [liveTopPair, liveTopWC, liveTopWI, liveTopWO, liveTopQC,
      liveTopQI, liveTopQO, hxl, hyl, hxb, hxc, hyc,
        hxi, QCarry.isOff, QCarry.isL,
        InTok.isS, InTok.isX, inT, topBorder] <;>
      (split <;> rfl)
  · exact HeadlineDigit.checkerOwnerCarryLaunch
      c x y resolvedX resolvedY tail v
      hxl hyl hxc hxi hxb

/-- QC2 success: the OLD L is cleared, the OLD S
at the responder is consumed, and one L moves right. -/
theorem topMobileOwnerQCAdvances
    (c : Compiled) (x y : Agent c)
    (resolvedX resolvedY carry error tail : Bool)
    (v : Fin c.topA)
    (hxl : x.l = false) (hyl : y.l = false)
    (hcy : y.qCarry = .OFF)
    (hcx : x.qCarry = .L carry error)
    (hyi : y.qIn = .S v tail)
    (hyb : y.beta = false) :
    (liveTopPair c x y resolvedX resolvedY).x.qIn = .E ∧
    (liveTopPair c x y resolvedX resolvedY).y.qIn = .E ∧
    (liveTopPair c x y resolvedX resolvedY).x.qCarry = .OFF ∧
    (liveTopPair c x y resolvedX resolvedY).y.qCarry =
      .L (HeadlineDigit.checkerCarryNext c (carry, error)
          v y.d).1
         (HeadlineDigit.checkerCarryNext c (carry, error)
          v y.d).2 := by
  try simp only [liveTopPair_x_wIn, liveTopPair_y_wIn, liveTopPair_x_wCarry, liveTopPair_y_wCarry,
    liveTopPair_x_wOut, liveTopPair_y_wOut, liveTopPair_x_qIn, liveTopPair_y_qIn,
    liveTopPair_x_qCarry, liveTopPair_y_qCarry, liveTopPair_x_qOut, liveTopPair_y_qOut] at *
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [liveTopPair, liveTopWC, liveTopWI, liveTopWO, liveTopQC,
      liveTopQI, liveTopQO, hxl, hyl, hcx, hcy,
      hyi, hyb, QCarry.isOff, QCarry.isL,
      InTok.isS, topTerminal]
  · simp [liveTopPair, liveTopWC, liveTopWI, liveTopWO, liveTopQC,
      liveTopQI, liveTopQO, hxl, hyl, hcx, hcy,
      hyi, hyb, QCarry.isOff, QCarry.isL,
      InTok.isS, topTerminal]
  · simp [liveTopPair, liveTopWC, liveTopWI, liveTopWO, liveTopQC,
      liveTopQI, liveTopQO, hxl, hyl, hcx, hcy,
      hyi, hyb, QCarry.isOff, QCarry.isL,
      InTok.isS, topTerminal]
  · exact HeadlineDigit.checkerOwnerCarryAdvance
      c x y resolvedX resolvedY carry error tail v
      hxl hyl hcx hcy hyi hyb

/-- QC2 abort when the old internal target input is E:
the source carry is retired and no new carry is spawned. -/
theorem topMobileOwnerQCAborts
    (c : Compiled) (x y : Agent c)
    (resolvedX resolvedY carry error : Bool)
    (hxl : x.l = false) (hyl : y.l = false)
    (hcx : x.qCarry = .L carry error)
    (hcy : y.qCarry = .OFF) (hyi : y.qIn = .E)
    (hyb : y.beta = false) :
    (liveTopPair c x y resolvedX resolvedY).x.qCarry = .OFF ∧
    (liveTopPair c x y resolvedX resolvedY).y.qCarry = .OFF ∧
    (liveTopPair c x y resolvedX resolvedY).x.qIn = .E := by
  try simp only [liveTopPair_x_wIn, liveTopPair_y_wIn, liveTopPair_x_wCarry, liveTopPair_y_wCarry,
    liveTopPair_x_wOut, liveTopPair_y_wOut, liveTopPair_x_qIn, liveTopPair_y_qIn,
    liveTopPair_x_qCarry, liveTopPair_y_qCarry, liveTopPair_x_qOut, liveTopPair_y_qOut] at *
  simp [liveTopPair, liveTopWC, liveTopWI, liveTopWO, liveTopQC,
      liveTopQI, liveTopQO, hxl, hyl, hcx, hcy,
    hyi, hyb, topTerminal, QCarry.isL,
    QCarry.isOff, InTok.isS, InTok.isE]

/-- QC2 terminal: an OLD border at the responder retires
the live carry, with no continuation into the next block.
Exclude unrelated QO offers to state an E-valued responder. -/
theorem topMobileOwnerQCRetires
    (c : Compiled) (x y : Agent c)
    (resolvedX resolvedY carry error : Bool)
    (hxl : x.l = false) (hyl : y.l = false)
    (hcx : x.qCarry = .L carry error)
    (hcy : y.qCarry = .OFF) (hyi : y.qIn = .E)
    (hyb : y.beta = true) (hqo : x.qOut = .E) :
    (liveTopPair c x y resolvedX resolvedY).x.qCarry = .OFF ∧
    (liveTopPair c x y resolvedX resolvedY).y.qCarry = .OFF ∧
    (liveTopPair c x y resolvedX resolvedY).x.qIn = .E ∧
    (liveTopPair c x y resolvedX resolvedY).y.qIn = .E := by
  try simp only [liveTopPair_x_wIn, liveTopPair_y_wIn, liveTopPair_x_wCarry, liveTopPair_y_wCarry,
    liveTopPair_x_wOut, liveTopPair_y_wOut, liveTopPair_x_qIn, liveTopPair_y_qIn,
    liveTopPair_x_qCarry, liveTopPair_y_qCarry, liveTopPair_x_qOut, liveTopPair_y_qOut] at *
  simp [liveTopPair, liveTopWC, liveTopWI, liveTopWO, liveTopQC,
      liveTopQI, liveTopQO, hxl, hyl, hcx, hcy,
    hyi, hyb, hqo, topTerminal, QCarry.isL,
    QCarry.isOff, InTok.isS, OutTok.isD]

/-! QO uses OLD qOut and OLD target beta, and cannot
materialize or move a second packet on the same service. -/

/-- QO port: an OLD D offered to a marker-border E,
with an OFF carry, creates exactly one target P.
Additional OLD-empty source input/carry assumptions keep
this owner subcase simple; they are not universal port guards. -/
theorem topMobileOwnerQOPortAccepts
    (c : Compiled) (x y : Agent c)
    (resolvedX resolvedY : Bool)
    (v : Fin c.topA) (tail : Bool)
    (hxl : x.l = false) (hyl : y.l = false)
    (hxi : x.qIn = .E) (hxc : x.qCarry = .OFF)
    (hyi : y.qIn = .E) (hyc : y.qCarry = .OFF)
    (hyb : y.beta = true)
    (hxo : x.qOut = .D v tail) :
    (liveTopPair c x y resolvedX resolvedY).y.qIn =
      .P v tail ∧
    (liveTopPair c x y resolvedX resolvedY).x.qOut =
      (if tail then .U else .E) ∧
    (liveTopPair c x y resolvedX resolvedY).y.qOut =
      y.qOut := by
  try simp only [liveTopPair_x_wIn, liveTopPair_y_wIn, liveTopPair_x_wCarry, liveTopPair_y_wCarry,
    liveTopPair_x_wOut, liveTopPair_y_wOut, liveTopPair_x_qIn, liveTopPair_y_qIn,
    liveTopPair_x_qCarry, liveTopPair_y_qCarry, liveTopPair_x_qOut, liveTopPair_y_qOut] at *
  simp [liveTopPair, liveTopWC, liveTopWI, liveTopWO, liveTopQC,
      liveTopQI, liveTopQO, hxl, hyl, hxi, hxc,
    hyi, hyc, hyb, hxo, QCarry.isOff,
    QCarry.isL, InTok.isS, InTok.isE,
    InTok.isX, InTok.isP, OutTok.isD,
    outT, outV, topTerminal]

/-- QO internal D movement into an OLD-empty output
slot; tail leaves U, nontail leaves E at source. -/
theorem topMobileOwnerQODataMoves
    (c : Compiled) (x y : Agent c)
    (resolvedX resolvedY : Bool)
    (v : Fin c.topA) (tail : Bool)
    (hxl : x.l = false) (hyl : y.l = false)
    (hxo : x.qOut = .D v tail) (hyo : y.qOut = .E)
    (hyb : y.beta = false) :
    (liveTopPair c x y resolvedX resolvedY).x.qOut =
      (if tail then .U else .E) ∧
    (liveTopPair c x y resolvedX resolvedY).y.qOut =
      .D v tail := by
  try simp only [liveTopPair_x_wIn, liveTopPair_y_wIn, liveTopPair_x_wCarry, liveTopPair_y_wCarry,
    liveTopPair_x_wOut, liveTopPair_y_wOut, liveTopPair_x_qIn, liveTopPair_y_qIn,
    liveTopPair_x_qCarry, liveTopPair_y_qCarry, liveTopPair_x_qOut, liveTopPair_y_qOut] at *
  simp [liveTopPair, liveTopWC, liveTopWI, liveTopWO, liveTopQC,
      liveTopQI, liveTopQO, hxl, hyl, hxo,
    hyo, hyb, OutTok.isD, OutTok.isE,
    outT, outV]

/-- QO unread source samples its own OLD digit and marker,
but cannot export that new D in the same service. -/
theorem topMobileOwnerQOUnreadSamples
    (c : Compiled) (x y : Agent c)
    (resolvedX resolvedY : Bool)
    (hxl : x.l = false) (hyl : y.l = false)
    (hxo : x.qOut = .U) :
    (liveTopPair c x y resolvedX resolvedY).x.qOut =
      .D x.d x.beta ∧
    (liveTopPair c x y resolvedX resolvedY).y.qOut =
      y.qOut := by
  try simp only [liveTopPair_x_wIn, liveTopPair_y_wIn, liveTopPair_x_wCarry, liveTopPair_y_wCarry,
    liveTopPair_x_wOut, liveTopPair_y_wOut, liveTopPair_x_qIn, liveTopPair_y_qIn,
    liveTopPair_x_qCarry, liveTopPair_y_qCarry, liveTopPair_x_qOut, liveTopPair_y_qOut] at *
  simp [liveTopPair, liveTopWC, liveTopWI, liveTopWO, liveTopQC,
      liveTopQI, liveTopQO, hxl, hyl,
    hxo, OutTok.isD, OutTok.isU]

/-- QO empty marker produces U, not an instantly exported D. -/
theorem topMobileOwnerQOMarkerBootstraps
    (c : Compiled) (x y : Agent c)
    (resolvedX resolvedY : Bool)
    (hxl : x.l = false) (hyl : y.l = false)
    (hxb : x.beta = true) (hxo : x.qOut = .E) :
    (liveTopPair c x y resolvedX resolvedY).x.qOut = .U ∧
    (liveTopPair c x y resolvedX resolvedY).y.qOut =
      y.qOut := by
  try simp only [liveTopPair_x_wIn, liveTopPair_y_wIn, liveTopPair_x_wCarry, liveTopPair_y_wCarry,
    liveTopPair_x_wOut, liveTopPair_y_wOut, liveTopPair_x_qIn, liveTopPair_y_qIn,
    liveTopPair_x_qCarry, liveTopPair_y_qCarry, liveTopPair_x_qOut, liveTopPair_y_qOut] at *
  simp [liveTopPair, liveTopWC, liveTopWI, liveTopWO, liveTopQC,
      liveTopQI, liveTopQO, hxl, hyl, hxb,
    hxo, OutTok.isD, OutTok.isU, OutTok.isE]

/-! The first two owner row families are now lifted back
to the real topFixedPublicNext pair. The same source/
responder projection works for each of the pure owner
QC and QO lemmas above; this does not replace the
as-yet-missing colored A/M/rho induction. -/

/-- Actual physical/fixed-public QI pending move,
including source deletion and responder arrival. -/
theorem topMobilePhysicalQIPendingMove {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (C D : HeadlineConfiguration n) (e : Fin n)
    (v : Fin (compileAdvice (ceilLogTwo n)).topA)
    (tail : Bool)
    (hxl : (D e).l = false)
    (hyl : (D (ring.rightNeighbor e)).l = false)
    (hxc : (D e).qCarry = .OFF)
    (hyc : (D (ring.rightNeighbor e)).qCarry = .OFF)
    (hxi : (D e).qIn = .P v tail)
    (hyi : (D (ring.rightNeighbor e)).qIn = .E)
    (hyb : (D (ring.rightNeighbor e)).beta = false) :
    (topFixedPublicNext ring C D e e).qIn = .E ∧
    (topFixedPublicNext ring C D e
      (ring.rightNeighbor e)).qIn = .P v tail := by
  have hrow :
      (topMobileLiteralTopOwner ring D e).x.qIn = .E ∧
      (topMobileLiteralTopOwner ring D e).y.qIn =
        .P v tail := by
    unfold topMobileLiteralTopOwner
    exact topMobileOwnerQIPendingMove _ _ _ _ _ v tail
      hxl hyl hxc hyc hxi hyi hyb
  have hx := topMobileLiteralSourceFields ring C D e
  have hy := topMobileLiteralResponderFields ring hn C D e
  exact ⟨hx.1.trans hrow.1, hy.1.trans hrow.2⟩

/-- Actual QI internal tail-to-X effect on the selected
target edge; reuse HeadlineDigit's owner theorem. -/
theorem topMobilePhysicalQITailConverts {n : Nat}
    (ring : DirectedRing n)
    (C D : HeadlineConfiguration n) (e : Fin n)
    (v : Fin (compileAdvice (ceilLogTwo n)).topA)
    (hxl : (D e).l = false)
    (hyl : (D (ring.rightNeighbor e)).l = false)
    (hxb : (D e).beta = false)
    (hyb : (D (ring.rightNeighbor e)).beta = false)
    (hxc : (D e).qCarry = .OFF)
    (hyc : (D (ring.rightNeighbor e)).qCarry = .OFF)
    (hxi : (D e).qIn = .S v true)
    (hyi : (D (ring.rightNeighbor e)).qIn = .E) :
    (topFixedPublicNext ring C D e e).qIn = .X := by
  have hrow :
      (topMobileLiteralTopOwner ring D e).x.qIn = .X := by
    unfold topMobileLiteralTopOwner
    exact HeadlineDigit.checkerOwnerInternalTailBecomesX
      _ _ _ _ _ v
      hxl hyl hxb hyb hxc hyc hxi hyi
  exact (topMobileLiteralSourceFields ring C D e).1.trans hrow

/-- Exact QC3 fresh carry field in the real fixed-public
shadow, with both OLD physical-root guards. -/
theorem topMobilePhysicalQCLaunch {n : Nat}
    (ring : DirectedRing n)
    (C D : HeadlineConfiguration n) (e : Fin n)
    (tail : Bool)
    (v : Fin (compileAdvice (ceilLogTwo n)).topA)
    (hxl : (D e).l = false)
    (hyl : (D (ring.rightNeighbor e)).l = false)
    (hxc : (D e).qCarry = .OFF)
    (hxi : (D e).qIn = .S v tail)
    (hmarker : (D e).beta = true) :
    (topFixedPublicNext ring C D e e).qCarry =
      .L (HeadlineDigit.checkerCarryNext
        (compileAdvice (ceilLogTwo n)) (true, false)
        v (D e).d).1
         (HeadlineDigit.checkerCarryNext
        (compileAdvice (ceilLogTwo n)) (true, false)
        v (D e).d).2 := by
  change ((headlinePhysicalNext ring D e) e).qCarry = _
  exact HeadlineDigit.checkerPhysicalCarryLaunch
    ring D e tail v hxl hyl hxc hxi hmarker

/-- Exact QC2 successful carry transfer in the real
fixed-public shadow, reading OLD settled responder. -/
theorem topMobilePhysicalQCAdvance {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (C D : HeadlineConfiguration n) (e : Fin n)
    (carry error tail : Bool)
    (v : Fin (compileAdvice (ceilLogTwo n)).topA)
    (hxl : (D e).l = false)
    (hyl : (D (ring.rightNeighbor e)).l = false)
    (hcx : (D e).qCarry = .L carry error)
    (hcy : (D (ring.rightNeighbor e)).qCarry = .OFF)
    (hyi : (D (ring.rightNeighbor e)).qIn = .S v tail)
    (hyb : (D (ring.rightNeighbor e)).beta = false) :
    (topFixedPublicNext ring C D e
      (ring.rightNeighbor e)).qCarry =
      .L (HeadlineDigit.checkerCarryNext
        (compileAdvice (ceilLogTwo n)) (carry, error)
        v (D (ring.rightNeighbor e)).d).1
         (HeadlineDigit.checkerCarryNext
        (compileAdvice (ceilLogTwo n)) (carry, error)
        v (D (ring.rightNeighbor e)).d).2 := by
  change ((headlinePhysicalNext ring D e)
    (ring.rightNeighbor e)).qCarry = _
  exact HeadlineDigit.checkerPhysicalCarryAdvance
    ring hn D e carry error tail v
    hxl hyl hcx hcy hyi hyb

/-- A QO source's OLD unread state sampling is a real
fixed-public field equation, not a fresh packet export. -/
theorem topMobilePhysicalQOUnreadSamples {n : Nat}
    (ring : DirectedRing n)
    (C D : HeadlineConfiguration n) (e : Fin n)
    (hxl : (D e).l = false)
    (hyl : (D (ring.rightNeighbor e)).l = false)
    (hu : (D e).qOut = .U) :
    (topFixedPublicNext ring C D e e).qOut =
      .D (D e).d (D e).beta := by
  have hrow :
      (topMobileLiteralTopOwner ring D e).x.qOut =
        .D (D e).d (D e).beta := by
    unfold topMobileLiteralTopOwner
    exact (topMobileOwnerQOUnreadSamples
      _ _ _ _ _ hxl hyl hu).1
  exact (topMobileLiteralSourceFields ring C D e).2.2.trans hrow

/-!
REMAINING:

The pure branch equations above are guarded OLD row
instances. For every selected edge they transfer to
the true physical state by topMobileLiteralSourceFields
and topMobileLiteralResponderFields; unrelated sites
frame by topMobileLiteralAwayFields.

The full OLD-first-match case partition, including
carry occupancy at *both* endpoints and the port's
responder claiming priority, still needs to be
assembled as a single exhaustive row classification
under the complete root-free target geometry.

Neither the color-update ghost nor these
field equations alone proves that the analytical
post-eta colors and accepted-serial suffix are
preserved by every row. Such a closure proof must
establish the necessary active-component facts and
non-overwriting of front/carry consumer gaps.

Accordingly the global unchanged-A inequalities
rho(new) <= rho(old), M(new) <= M(old), strict
effective-front descent, at-most-one-new-carry
nonreseeding, and the all-word P.7 5r contact count
remain NOT PROVED and are not declared here.
-/

end L3


/-!
First-match branch taxonomy and a non-exclusivity finding.

The QI and QO coordinates are processed independently in
CertRows.liveTopPair on the SAME selected edge. In particular,
a QI pending move and QO unread sample may occur together.
Consequently there is no sound global exclusive disjunction
"one QI or one QC or one QO branch" for the literal machine.

The product of separately prioritized local choices is the
appropriate exhaustive *guard* classification. It is not yet
an exhaustive proof of all resulting paired slot equations,
nor a proof of colored P.7 descent.
-/

namespace L3

set_option autoImplicit false
set_option Elab.async false

/-- Mutually exclusive outcomes of the OLD QC first-match
chain, not of the whole TOP owner. -/
inductive TopMobileQCBranch where
  | roots | retire | advance | abort | launch | frame
  deriving DecidableEq, Repr

/-- The literal QC priority: root reset, old carry
retirement/advance/abort, then border launch, then frame. -/
def topMobileQCBranch {c : Compiled}
    (x y : Agent c) : TopMobileQCBranch :=
  if x.l || y.l then .roots
  else if x.qCarry.isL then
    if topTerminal x y then .retire
    else if y.qCarry.isOff && y.qIn.isS then .advance
    else .abort
  else if topBorder x && x.qCarry.isOff &&
      x.qIn.isS && !y.l then .launch
  else .frame

/-- The source QI priority. The responder QI reservation
is a separate coordinate and must not be erased by this tag. -/
inductive TopMobileQISourceBranch where
  | roots | carryCleanup | tailConverts | frontActs
  | carryLaunchConsumes
  | pendingTerminalSettles | pendingTerminalDeletes
  | pendingMoves | pendingSettles | frame
  deriving DecidableEq, Repr

def topMobileQISourceBranch {c : Compiled}
    (x y : Agent c) : TopMobileQISourceBranch :=
  if x.l || y.l then .roots
  else if !x.qCarry.isOff then .carryCleanup
  else if x.qIn.isS && inT x.qIn && !x.beta then
    .tailConverts
  else if x.qIn.isX then .frontActs
  else if topBorder x && x.qCarry.isOff &&
      x.qIn.isS && !y.l then .carryLaunchConsumes
  else if x.qIn.isP then
    if topTerminal x y then
      if !inT x.qIn then .pendingTerminalSettles
      else if !x.beta then .pendingTerminalDeletes
      else .frame
    else if topInternal y && y.qIn.isE &&
        y.qCarry.isOff then .pendingMoves
    else if y.qIn.isS && y.qCarry.isOff then
      .pendingSettles
    else .frame
  else .frame

/-- The responder QI slot is independently claimed by
carry-host cleanup, incoming X, QC2, moving pending P,
or an accepted OLD D port offer, in that order. -/
inductive TopMobileQIResponderBranch where
  | roots | carryCleanup | frontAdvances
  | carryConsumes | pendingArrives | portAccepts | frame
  deriving DecidableEq, Repr

def topMobileQIResponderBranch {c : Compiled}
    (x y : Agent c) : TopMobileQIResponderBranch :=
  if x.l || y.l then .roots
  else if !y.qCarry.isOff then .carryCleanup
  else if x.qCarry.isOff && x.qIn.isX &&
      topInternal y && y.qIn.isS then .frontAdvances
  else if x.qCarry.isL && !topTerminal x y &&
      y.qCarry.isOff && y.qIn.isS then .carryConsumes
  else if x.qCarry.isOff && x.qIn.isP &&
      !topTerminal x y && topInternal y &&
      y.qIn.isE && y.qCarry.isOff then .pendingArrives
  else if x.qOut.isD && y.beta &&
      y.qIn.isE && y.qCarry.isOff then .portAccepts
  else .frame

/-- OLD QO priority: root reset, D port offered and
accepted/blocked, internal D move, U sampling, marker U
bootstrap, ordinary frame. QO may occur simultaneously
with a source or responder QI action. -/
inductive TopMobileQOBranch where
  | roots | portAccepts | portBlocks | dataMoves
  | unreadSamples | markerBootstraps | frame
  deriving DecidableEq, Repr

def topMobileQOBranch {c : Compiled}
    (x y : Agent c) : TopMobileQOBranch :=
  if x.l || y.l then .roots
  else if x.qOut.isD && y.beta then
    if y.qIn.isE && y.qCarry.isOff then .portAccepts
    else .portBlocks
  else if x.qOut.isD && !y.beta && y.qOut.isE then
    .dataMoves
  else if x.qOut.isU then .unreadSamples
  else if x.beta && x.qOut.isE && !x.l then
    .markerBootstraps
  else .frame

/-- A single physical service has a PRODUCT of checker
branch choices, not a globally exclusive sum of them. -/
structure TopMobileOwnerBranchProduct where
  sourceInput : TopMobileQISourceBranch
  responderInput : TopMobileQIResponderBranch
  carry : TopMobileQCBranch
  output : TopMobileQOBranch
  deriving DecidableEq, Repr

def topMobileOwnerBranchProduct {c : Compiled}
    (x y : Agent c) : TopMobileOwnerBranchProduct :=
  { sourceInput := topMobileQISourceBranch x y
    responderInput := topMobileQIResponderBranch x y
    carry := topMobileQCBranch x y
    output := topMobileQOBranch x y }


/-- The local QC guard chain is exhaustive. The theorem
is intentionally about the priority tag; its full TOP
field equations still require the literal row bridge. -/
theorem topMobileQCCovers {c : Compiled}
    (x y : Agent c) :
    topMobileQCBranch x y = .roots ∨
    topMobileQCBranch x y = .retire ∨
    topMobileQCBranch x y = .advance ∨
    topMobileQCBranch x y = .abort ∨
    topMobileQCBranch x y = .launch ∨
    topMobileQCBranch x y = .frame := by
  cases h : topMobileQCBranch x y <;> simp [h]

/-- The QO guard chain is likewise exhaustive independently. -/
theorem topMobileQOCovers {c : Compiled}
    (x y : Agent c) :
    topMobileQOBranch x y = .roots ∨
    topMobileQOBranch x y = .portAccepts ∨
    topMobileQOBranch x y = .portBlocks ∨
    topMobileQOBranch x y = .dataMoves ∨
    topMobileQOBranch x y = .unreadSamples ∨
    topMobileQOBranch x y = .markerBootstraps ∨
    topMobileQOBranch x y = .frame := by
  cases h : topMobileQOBranch x y <;> simp [h]

/-- The QI source guard chain, including the terminal
P subcases, has no missing source-priority outcome. -/
theorem topMobileQISourceCovers {c : Compiled}
    (x y : Agent c) :
    topMobileQISourceBranch x y = .roots ∨
    topMobileQISourceBranch x y = .carryCleanup ∨
    topMobileQISourceBranch x y = .tailConverts ∨
    topMobileQISourceBranch x y = .frontActs ∨
    topMobileQISourceBranch x y = .carryLaunchConsumes ∨
    topMobileQISourceBranch x y = .pendingTerminalSettles ∨
    topMobileQISourceBranch x y = .pendingTerminalDeletes ∨
    topMobileQISourceBranch x y = .pendingMoves ∨
    topMobileQISourceBranch x y = .pendingSettles ∨
    topMobileQISourceBranch x y = .frame := by
  cases h : topMobileQISourceBranch x y <;> simp [h]

/-- QI responder reservation has its own exhaustive
priority order, independent of source-side consumption. -/
theorem topMobileQIResponderCovers {c : Compiled}
    (x y : Agent c) :
    topMobileQIResponderBranch x y = .roots ∨
    topMobileQIResponderBranch x y = .carryCleanup ∨
    topMobileQIResponderBranch x y = .frontAdvances ∨
    topMobileQIResponderBranch x y = .carryConsumes ∨
    topMobileQIResponderBranch x y = .pendingArrives ∨
    topMobileQIResponderBranch x y = .portAccepts ∨
    topMobileQIResponderBranch x y = .frame := by
  cases h : topMobileQIResponderBranch x y <;> simp [h]

/-!
Literal counterinstance to cross-namespace exclusivity.

An OLD target marker x may carry an input P while its
separate qOut namespace is U. With y an internal follower,
OLD-empty/carry-free in QI, the same edge performs both
QI P_x -> P_y and QO U_x -> D_x.

This is an ordinary Cartesian target-block state. To
satisfy post-eta invariants (i)--(iv) at width r >= 3,
place an active settled S at offset 2, the pending P at
offset 0 (accepted serial 0), no X or generated L.
The next cut has pending P at offset 1 and the same S at
offset 2: A and M remain unchanged and rho remains 1.
Thus this is a counterexample to the requested GLOBAL
"exactly one QI/QC/QO branch", not to the rank descent.
-/

/-- Concrete OLD source in the two simultaneously enabled
row families. All other Agent coordinates remain blank. -/
def topMobileConcurrentSource (c : Compiled) : Agent c :=
  { Agent.blank c with
    l := false
    beta := true
    qIn := .P c.zeroDigit false
    qCarry := .OFF
    qOut := .U }

/-- Internal empty responder in the same original edge. -/
def topMobileConcurrentResponder (c : Compiled) : Agent c :=
  { Agent.blank c with
    l := false
    beta := false
    qIn := .E
    qCarry := .OFF
    qOut := .E }

/-- The two previously owner row lemmas apply at
once. The output D samples the OLD x.d and x.beta;
it is not the moved input P. -/
theorem topMobileConcurrentQIAndQO (c : Compiled)
    (resolvedX resolvedY : Bool) :
    (liveTopPair c
      (topMobileConcurrentSource c)
      (topMobileConcurrentResponder c)
      resolvedX resolvedY).x.qIn = .E ∧
    (liveTopPair c
      (topMobileConcurrentSource c)
      (topMobileConcurrentResponder c)
      resolvedX resolvedY).y.qIn =
        .P c.zeroDigit false ∧
    (liveTopPair c
      (topMobileConcurrentSource c)
      (topMobileConcurrentResponder c)
      resolvedX resolvedY).x.qOut =
        .D (topMobileConcurrentSource c).d
          (topMobileConcurrentSource c).beta ∧
    topMobileQISourceBranch
      (topMobileConcurrentSource c)
      (topMobileConcurrentResponder c) =
        .pendingMoves ∧
    topMobileQOBranch
      (topMobileConcurrentSource c)
      (topMobileConcurrentResponder c) =
        .unreadSamples := by
  have hqi := topMobileOwnerQIPendingMove c
    (topMobileConcurrentSource c)
    (topMobileConcurrentResponder c)
    resolvedX resolvedY c.zeroDigit false
    rfl rfl rfl rfl rfl rfl rfl
  have hqo := topMobileOwnerQOUnreadSamples c
    (topMobileConcurrentSource c)
    (topMobileConcurrentResponder c)
    resolvedX resolvedY rfl rfl rfl
  refine ⟨hqi.1, hqi.2, hqo.1, ?_, ?_⟩
  · rfl
  · rfl

/-- The original "one QI OR one QO branch" exclusivity
assertion is mathematically false for the literal owner.
The correct one-hot object is the product label above. -/
theorem topMobileCrossNamespaceExclusivityFalse
    (c : Compiled) :
    ¬ (∀ x y : Agent c,
        topMobileQISourceBranch x y = .pendingMoves →
        topMobileQOBranch x y ≠ .unreadSamples) := by
  intro hall
  have hsim := topMobileConcurrentQIAndQO c false false
  exact (hall (topMobileConcurrentSource c)
    (topMobileConcurrentResponder c) hsim.2.2.2.1)
    hsim.2.2.2.2

/-!
STOPPED PROOF OBLIGATIONS (not declared as theorems):

* Equate the priority product tags with the exact QI
  first-match flags and all resulting TWO-ENDPOINT slot
  equations of CertRows.liveTopPair. The earlier
  lemmas handle individual guarded subcases, not the full
  product (for example QI move and QO sample together).

* On a genuinely reached post-eta colored trace, prove
  TopMobileInvariants survives the complete product case,
  including the fresh serial, active/doomed updates, old
  front protection, carry consumer gap and S-empty stop.

* Then prove, at constant active component charge A,
  rho(new) <= rho(old) and M(new) <= M(old), strict
  decrease for effective fronts, the nonreseeding
  at-most-one-new-carry rule, and the P.7 5r word count.

The counterinstance above disproves only the exclusive
cross-namespace classifier. It does not identify a
row violating the correctly stated post-eta invariants
or refute the paper's P.7 quantitative conclusion.
-/

end L3


/-!
Simultaneous QI.pendingMoves and QO.unreadSamples,
ONE literal selected edge.
No global invariant-preservation theorem is assumed.
-/

namespace L3

set_option autoImplicit false
set_option Elab.async false

/-- All SIX new checker slots on the simultaneous QI/QO
branch product.  In particular source qOut samples OLD
x.d and OLD x.beta, not the just-moved input packet. -/
theorem topMobileOwnerPendingMovesUnreadSamples
    (c : Compiled) (x y : Agent c)
    (resolvedX resolvedY : Bool)
    (v : Fin c.topA) (tail : Bool)
    (hxl : x.l = false) (hyl : y.l = false)
    (hxc : x.qCarry = .OFF) (hyc : y.qCarry = .OFF)
    (hxi : x.qIn = .P v tail) (hyi : y.qIn = .E)
    (hyb : y.beta = false) (hxo : x.qOut = .U) :
    (liveTopPair c x y resolvedX resolvedY).x.qIn = .E ∧
    (liveTopPair c x y resolvedX resolvedY).x.qCarry = .OFF ∧
    (liveTopPair c x y resolvedX resolvedY).x.qOut =
      .D x.d x.beta ∧
    (liveTopPair c x y resolvedX resolvedY).y.qIn =
      .P v tail ∧
    (liveTopPair c x y resolvedX resolvedY).y.qCarry = .OFF ∧
    (liveTopPair c x y resolvedX resolvedY).y.qOut =
      y.qOut := by
  try simp only [liveTopPair_x_wIn, liveTopPair_y_wIn, liveTopPair_x_wCarry, liveTopPair_y_wCarry,
    liveTopPair_x_wOut, liveTopPair_y_wOut, liveTopPair_x_qIn, liveTopPair_y_qIn,
    liveTopPair_x_qCarry, liveTopPair_y_qCarry, liveTopPair_x_qOut, liveTopPair_y_qOut] at *
  have hqi := topMobileOwnerQIPendingMove
    c x y resolvedX resolvedY v tail
    hxl hyl hxc hyc hxi hyi hyb
  have hqo := topMobileOwnerQOUnreadSamples
    c x y resolvedX resolvedY hxl hyl hxo
  have hqc :
      (liveTopPair c x y resolvedX resolvedY).x.qCarry =
        .OFF ∧
      (liveTopPair c x y resolvedX resolvedY).y.qCarry =
        .OFF := by
    simp [liveTopPair, liveTopWC, liveTopWI, liveTopWO, liveTopQC,
      liveTopQI, liveTopQO, hxl, hyl, hxc, hyc, hxi, hyi,
      hyb, topBorder, topTerminal,
      QCarry.isOff, QCarry.isL, InTok.isS]
  exact ⟨hqi.1, hqc.1, hqo.1,
    hqi.2, hqc.2, hqo.2⟩

/-- Exact projection of the six-field product result on
one physical edge. Do not rewrite HeadlineConfiguration
to a Fin-to-Agent function. -/
theorem topMobilePhysicalPendingMovesUnreadSamples {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (C D : HeadlineConfiguration n) (e : Fin n)
    (v : Fin (compileAdvice (ceilLogTwo n)).topA)
    (tail : Bool)
    (hxl : (D e).l = false)
    (hyl : (D (ring.rightNeighbor e)).l = false)
    (hxc : (D e).qCarry = .OFF)
    (hyc : (D (ring.rightNeighbor e)).qCarry = .OFF)
    (hxi : (D e).qIn = .P v tail)
    (hyi : (D (ring.rightNeighbor e)).qIn = .E)
    (hyb : (D (ring.rightNeighbor e)).beta = false)
    (hxo : (D e).qOut = .U) :
    (topFixedPublicNext ring C D e e).qIn = .E ∧
    (topFixedPublicNext ring C D e e).qCarry = .OFF ∧
    (topFixedPublicNext ring C D e e).qOut =
      .D (D e).d (D e).beta ∧
    (topFixedPublicNext ring C D e
      (ring.rightNeighbor e)).qIn = .P v tail ∧
    (topFixedPublicNext ring C D e
      (ring.rightNeighbor e)).qCarry = .OFF ∧
    (topFixedPublicNext ring C D e
      (ring.rightNeighbor e)).qOut =
      (D (ring.rightNeighbor e)).qOut := by
  have hrow :
      (topMobileLiteralTopOwner ring D e).x.qIn = .E ∧
      (topMobileLiteralTopOwner ring D e).x.qCarry = .OFF ∧
      (topMobileLiteralTopOwner ring D e).x.qOut =
        .D (D e).d (D e).beta ∧
      (topMobileLiteralTopOwner ring D e).y.qIn =
        .P v tail ∧
      (topMobileLiteralTopOwner ring D e).y.qCarry = .OFF ∧
      (topMobileLiteralTopOwner ring D e).y.qOut =
        (D (ring.rightNeighbor e)).qOut := by
    unfold topMobileLiteralTopOwner
    exact topMobileOwnerPendingMovesUnreadSamples
      _ _ _ _ _ v tail
      hxl hyl hxc hyc hxi hyi hyb hxo
  obtain ⟨hix, hcx, hox, hiy, hcy, hoy⟩ := hrow
  have hx := topMobileLiteralSourceFields ring C D e
  have hy := topMobileLiteralResponderFields ring hn C D e
  exact ⟨hx.1.trans hix, hx.2.1.trans hcx,
    hx.2.2.trans hox, hy.1.trans hiy,
    hy.2.1.trans hcy, hy.2.2.trans hoy⟩

/-- The QO unread-sample coordinate does not mint a
serial.  The QI pending move transfers the previous
source serial into the responder; the source is emptied. -/
theorem topMobilePendingUnreadGhostTransport {n : Nat}
    (D E : HeadlineConfiguration n) (s : Fin n)
    (r : Nat) (color : TopMobileColor)
    (e : Fin n) (j : Nat)
    (he : e = topMobileSite s r j)
    (hsource : topMobilePending D s r j = true)
    (hold : topMobilePending D s r (j + 1) = false)
    (hnew : topMobilePending E s r (j + 1) = true)
    (hgone : topMobilePending E s r j = false)
    (hu : (D e).qOut = .U) :
    (topMobileColorStep D E s r color e).accepted =
      color.accepted ∧
    (topMobileColorStep D E s r color e).serial j =
      none ∧
    (topMobileColorStep D E s r color e).serial (j + 1) =
      color.serial j := by
  have hno : ¬ TopMobilePortAccepted D E s r e := by
    intro haccept
    obtain ⟨_, _, _, v, tail, hoffer, _⟩ := haccept
    rw [hu] at hoffer
    cases hoffer
  have he' :
      e = topMobileSite s r ((j + 1) - 1) := by
    simpa using he
  have hmove := topMobileColorPendingMove
    D E s r color e (j + 1)
    (Nat.succ_pos j) hold hnew he' hsource
  exact ⟨topMobileColorAcceptedFrame D E s r color e hno,
    topMobileColorPendingGone D E s r color e j hgone,
    hmove⟩

/-- Clause (iv) / no-terminal-pending is preserved on
a one-step internal P move when all other target input
positions and the settled predicate frame. The OLD
pending barrier excludes a surviving S if the destination
is the terminal target coordinate. -/
theorem topMobilePendingUnreadTerminalPreserved {n : Nat}
    (D E : HeadlineConfiguration n) (s : Fin n)
    (r j : Nat)
    (v : Fin (compileAdvice (ceilLogTwo n)).topA)
    (tail : Bool)
    (hj : j + 1 < r)
    (hsource : topMobileInput D s r j = .P v tail)
    (hdestination : topMobileInput D s r (j + 1) = .E)
    (hframe : ∀ k : Nat, k < r → k ≠ j →
      k ≠ j + 1 →
      topMobileInput E s r k = topMobileInput D s r k)
    (hsettled : ∀ k : Nat, k < r →
      topMobileSettled E s r k = topMobileSettled D s r k)
    (hbarrier : TopMobilePendingBarrier D s r)
    (hterminal : TopMobileNoTerminalPending D s r) :
    TopMobileNoTerminalPending E s r := by
  intro hAny
  obtain ⟨k, hkr, hsk⟩ := hAny
  have hskOld : topMobileSettled D s r k = true := by
    rw [hsettled k hkr] at hsk
    exact hsk
  have hAnyOld : TopMobileAnySettled D s r :=
    ⟨k, hkr, hskOld⟩
  have hOldTerminal := hterminal hAnyOld
  by_cases hlast : j + 1 = r - 1
  · have hsourcePending :
        topMobilePending D s r j = true := by
      simp [topMobilePending, topMobileIsPending, hsource]
    have hlt : j < k :=
      hbarrier j k (by omega) hkr
        hsourcePending (Or.inl hskOld)
    have hkneq : k ≠ j + 1 := by
      intro heq
      rw [heq] at hskOld
      simp [topMobileSettled, topMobileIsSettled,
        hdestination] at hskOld
    exfalso
    omega
  · have hterm : r - 1 < r := by omega
    have hneqSource : r - 1 ≠ j := by omega
    have hneqDestination : r - 1 ≠ j + 1 := by
      intro heq
      exact hlast heq.symm
    have hframeTerm :=
      hframe (r - 1) hterm hneqSource hneqDestination
    simpa [topMobilePending, hframeTerm] using hOldTerminal

end L3


/-!
Source-level obstruction to unconditional one-step
TopMobilePendingBarrier preservation.

The OLD barrier alone does not rule out a second public beta
border INSIDE the designated target block.  A selected edge
with OLD source qIn=S(v,false), qOut=D(v,false) and OLD
responder qIn=E, beta=true simultaneously frames that S and
accepts a fresh P at the responder.  The new P can therefore
lie to the RIGHT of a surviving S.  All fields are legal
Cartesian values.  No new import or existing statement is
changed.

IMPORTANT: this refutes a theorem assuming merely OLD
TopMobilePendingBarrier (even OLD five-clause invariants can
be arranged), not the strengthened claim with an explicit
TopMobileFixedPair/CompleteBlockPair hypothesis.  The latter
forbids an interior beta border, and remains a separate proof
obligation.
-/

namespace L3

set_option autoImplicit false
set_option Elab.async false

/-- Legal OLD source: settled QI packet and an independent
QO data offer.  Tail is false, so no S-to-X conversion. -/
def topMobileBarrierCounterSource (c : Compiled) : Agent c :=
  { Agent.blank c with
    l := false
    beta := false
    qIn := .S c.zeroDigit false
    qCarry := .OFF
    qOut := .D c.zeroDigit false }

/-- Legal OLD responder: empty input and carry, but a
public beta border.  Its OLD qOut is E. -/
def topMobileBarrierCounterResponder (c : Compiled) : Agent c :=
  { Agent.blank c with
    l := false
    beta := true
    qIn := .E
    qCarry := .OFF
    qOut := .E }

/-- One actual local Cartesian product tag refutes barrier
preservation without a fixed-block geometry premise.
The first four conjuncts identify the OLD guard product.
The last two are exact NEW QI slots of liveTopPair. -/
theorem topMobilePendingBarrierCounterword
    (c : Compiled) (resolvedX resolvedY : Bool) :
    topMobileQISourceBranch
      (topMobileBarrierCounterSource c)
      (topMobileBarrierCounterResponder c) = .frame ∧
    topMobileQIResponderBranch
      (topMobileBarrierCounterSource c)
      (topMobileBarrierCounterResponder c) = .portAccepts ∧
    topMobileQCBranch
      (topMobileBarrierCounterSource c)
      (topMobileBarrierCounterResponder c) = .frame ∧
    topMobileQOBranch
      (topMobileBarrierCounterSource c)
      (topMobileBarrierCounterResponder c) = .portAccepts ∧
    (liveTopPair c
      (topMobileBarrierCounterSource c)
      (topMobileBarrierCounterResponder c)
      resolvedX resolvedY).x.qIn =
        .S c.zeroDigit false ∧
    (liveTopPair c
      (topMobileBarrierCounterSource c)
      (topMobileBarrierCounterResponder c)
      resolvedX resolvedY).y.qIn =
        .P c.zeroDigit false := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

end L3

/-!
Fixed-public geometry and the pending-barrier row interface.

The OLD public certificate, not the evolving qIn/qOut/qCarry, fixes the
target marker: only offset zero can be a QO accepting responder.
An ordinary QI pending move goes to the clockwise next offset.

The final theorem below is CONDITIONAL on a precise three-part
combined-row origin certificate.  It is NOT the unconditional
topMobilePendingBarrierStep: the first-match product proof that every
fixed-public physical edge satisfies TopMobilePendingStepOrigins is
still missing, and no counterword satisfying TopMobileFixedPair
has been produced.  In particular no origin certificate is silently
asserted for arbitrary private checker scratch.
-/

namespace L3

set_option autoImplicit false
set_option Elab.async false

/-- A complete fixed-public pair cannot contain a target block longer
than the physical ring: otherwise the source marker recurs at the
interior source offset n. -/
theorem topMobileFixedWidthLeRing {n : Nat}
    (C D : HeadlineConfiguration n) (s : Fin n) (r : Nat)
    (hfixed : TopMobileFixedPair C D s r) :
    r ≤ n := by
  obtain ⟨hr, hbad, _⟩ := hfixed
  rw [hr]
  by_cases hle : topMobileWidth n ≤ n
  · exact hle
  · have hn : 0 < n := by
      have hs := s.isLt
      omega
    have hlt : n < topMobileWidth n := by omega
    have hint :
        certMarker (HeadlineDigit.publicWord C) (certSite s n) =
          false :=
      hbad.1.2.2.2.2.1
        (⟨n, hlt⟩ : Fin (topMobileWidth n)) hn
    rw [certSite_n s] at hint
    rw [hbad.1.1] at hint
    cases hint

/-- All designated target offsets are old-public leader-free,
including the cyclic self-pair where r=n. -/
theorem topMobileFixedTargetFollower {n : Nat}
    (C D : HeadlineConfiguration n) (s : Fin n) (r j : Nat)
    (hfixed : TopMobileFixedPair C D s r) (hj : j < r) :
    (D (topMobileSite s r j)).l = false := by
  obtain ⟨hr, hbad, hpub⟩ := hfixed
  have hsite : (C (certSite s (r + j))).l = false := by
    rw [hr]
    have hjwidth : j < topMobileWidth n := by omega
    have hbound : topMobileWidth n + j <
        2 * (compileAdvice (ceilLogTwo n)).rho + 1 := by
      change (compileAdvice (ceilLogTwo n)).rho + j <
        2 * (compileAdvice (ceilLogTwo n)).rho + 1
      change j < (compileAdvice (ceilLogTwo n)).rho at hjwidth
      omega
    exact hbad.1.2.2.2.1 ⟨topMobileWidth n + j, hbound⟩
  have htarget : (C (topMobileSite s r j)).l = false := by
    simpa only [topMobileSite, certSite_add] using hsite
  exact (hpub _).1.trans htarget

/-- The target border at offset zero has old beta=true. -/
theorem topMobileFixedTargetBorderBeta {n : Nat}
    (C D : HeadlineConfiguration n) (s : Fin n) (r : Nat)
    (hfixed : TopMobileFixedPair C D s r) :
    (D (topMobileSite s r 0)).beta = true := by
  obtain ⟨hr, hbad, hpub⟩ := hfixed
  have hmarker :
      (C (certSite s (topMobileWidth n))).beta = true :=
    hbad.1.2.1
  have htarget : (C (topMobileSite s r 0)).beta = true := by
    rw [hr]
    simpa only [topMobileSite, certSite_zero] using hmarker
  exact (hpub _).2.2.1.trans htarget

/-- Every strictly interior target offset has old beta=false. -/
theorem topMobileFixedTargetInteriorBeta {n : Nat}
    (C D : HeadlineConfiguration n) (s : Fin n) (r j : Nat)
    (hfixed : TopMobileFixedPair C D s r)
    (hjpos : 0 < j) (hj : j < r) :
    (D (topMobileSite s r j)).beta = false := by
  obtain ⟨hr, hbad, hpub⟩ := hfixed
  have hfin : j < topMobileWidth n := by omega
  have htarget : (C (topMobileSite s r j)).beta = false := by
    rw [hr]
    exact hbad.1.2.2.2.2.2
      (⟨j, hfin⟩ : Fin (topMobileWidth n)) hjpos
  exact (hpub _).2.2.1.trans htarget

/-- A selected OLD QO offer with a beta-marked target responder
can meet the designated target window only at offset zero.  This is
the necessary beta guard of QO port acceptance, not an assertion
that the private E/OFF acceptance guards hold. -/
theorem topMobileFixedPortGuardOnlyAtBorder {n : Nat}
    (ring : DirectedRing n)
    (C D : HeadlineConfiguration n) (s : Fin n) (r j : Nat)
    (e : Fin n)
    (hfixed : TopMobileFixedPair C D s r)
    (hj : j < r)
    (he : ring.rightNeighbor e = topMobileSite s r j)
    (hguard :
      (D e).qOut.isD && (D (ring.rightNeighbor e)).beta = true) :
    j = 0 := by
  have hbeta : (D (ring.rightNeighbor e)).beta = true := by
    simp only [Bool.and_eq_true] at hguard
    exact of_decide_eq_true hguard.2
  have hsite : (D (topMobileSite s r j)).beta = true := by
    rw [← he]
    exact hbeta
  by_cases hz : j = 0
  · exact hz
  · have hjpos : 0 < j := by omega
    have hnobeta :=
      topMobileFixedTargetInteriorBeta C D s r j
        hfixed hjpos hj
    rw [hsite] at hnobeta
    cases hnobeta

/-- In this concrete DirectedRing, the service responder of the
source at target offset j is precisely target offset j+1. -/
theorem topMobileSiteRightNeighbor {n : Nat}
    (ring : DirectedRing n) (s : Fin n) (r j : Nat) :
    ring.rightNeighbor (topMobileSite s r j) =
      topMobileSite s r (j + 1) := by
  change certSite (certSite (certSite s r) j) 1 =
    certSite (certSite s r) (j + 1)
  rw [certSite_add]

/-- One genuine rootless QI pendingMoves service shifts its P by
exactly one offset, clearing its OLD source; the public beta/leader
guards are obtained from TopMobileFixedPair rather than postulated.
No assumption on the simultaneous QO tag is made. -/
theorem topMobileFixedPendingMoveRight {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (C D : HeadlineConfiguration n) (s : Fin n)
    (r j : Nat) (e : Fin n)
    (v : Fin (compileAdvice (ceilLogTwo n)).topA)
    (tail : Bool)
    (hfixed : TopMobileFixedPair C D s r)
    (hj : j + 1 < r) (he : e = topMobileSite s r j)
    (hxc : (D e).qCarry = .OFF)
    (hyc : (D (ring.rightNeighbor e)).qCarry = .OFF)
    (hxi : (D e).qIn = .P v tail)
    (hyi : (D (ring.rightNeighbor e)).qIn = .E) :
    topMobilePending (topFixedPublicNext ring C D e) s r j =
      false ∧
    topMobilePending (topFixedPublicNext ring C D e) s r
      (j + 1) = true := by
  have hneighbor :
      ring.rightNeighbor e = topMobileSite s r (j + 1) := by
    rw [he]
    exact topMobileSiteRightNeighbor ring s r j
  have hxl : (D e).l = false := by
    rw [he]
    exact topMobileFixedTargetFollower C D s r j
      hfixed (by omega)
  have hyl : (D (ring.rightNeighbor e)).l = false := by
    rw [hneighbor]
    exact topMobileFixedTargetFollower C D s r (j + 1)
      hfixed hj
  have hyb : (D (ring.rightNeighbor e)).beta = false := by
    rw [hneighbor]
    exact topMobileFixedTargetInteriorBeta C D s r (j + 1)
      hfixed (by omega) hj
  have hrow := topMobilePhysicalQIPendingMove
    ring hn C D e v tail hxl hyl hxc hyc hxi hyi hyb
  constructor
  · change topMobileIsPending
      ((topFixedPublicNext ring C D e)
        (topMobileSite s r j)).qIn = false
    rw [← he, hrow.1]
    rfl
  · change topMobileIsPending
      ((topFixedPublicNext ring C D e)
        (topMobileSite s r (j + 1))).qIn = true
    rw [← hneighbor, hrow.2]
    rfl

/-- The three possible old blocking predicates, as a single
proposition usable in the two-endpoint proof. -/
def TopMobileBarrierObstacle {n : Nat}
    (D : HeadlineConfiguration n) (s : Fin n)
    (r j : Nat) : Prop :=
  topMobileSettled D s r j = true ∨
  topMobileFront D s r j = true ∨
  topMobileLiveCarry D s r j = true

/-- Exact combined-row obligations sufficient for the barrier.

New P: an OLD P stays, an offer enters at zero, or an OLD P moves
to its next OLD-empty, carry-free slot.

New S/X/L blocker: the position was already an OLD blocker, or an
OLD pending at that position settled against the OLD S to its right,
or settled at the terminal target position.

Finally a newly pending slot cannot also be a new blocker.  This
last clause includes the simultaneous QI/QC carry exclusion and must
not be assumed from one-hot QI tags alone.

These are obligations for the real selected-edge PRODUCT, not
separate transitions or automatic consequences of fixed geometry. -/
def TopMobilePendingStepOrigins {n : Nat}
    (D E : HeadlineConfiguration n) (s : Fin n)
    (r : Nat) : Prop :=
  (∀ i : Nat, i < r →
    topMobilePending E s r i = true →
    topMobilePending D s r i = true ∨
    (i = 0 ∧ topMobileInput D s r 0 = .E ∧
      topMobileCarry D s r 0 = .OFF) ∨
    (∃ k : Nat, i = k + 1 ∧
      topMobilePending D s r k = true ∧
      topMobileInput D s r i = .E ∧
      topMobileCarry D s r i = .OFF)) ∧
  (∀ j : Nat, j < r →
    TopMobileBarrierObstacle E s r j →
    TopMobileBarrierObstacle D s r j ∨
    (topMobilePending D s r j = true ∧
      (j = r - 1 ∨
        (j + 1 < r ∧
          topMobileSettled D s r (j + 1) = true)))) ∧
  (∀ i : Nat, i < r →
    topMobilePending E s r i = true →
    ¬ TopMobileBarrierObstacle E s r i)

/-- Pure arithmetic/order proof: the exact origin certificate
makes the OLD pending-left-of-blockers barrier inductive.
The difficult physical product-row origin certificate is
explicitly an additional premise, not a fabricated theorem. -/
theorem topMobilePendingBarrierOfOrigins {n : Nat}
    (D E : HeadlineConfiguration n) (s : Fin n) (r : Nat)
    (hbarrier : TopMobilePendingBarrier D s r)
    (horigins : TopMobilePendingStepOrigins D E s r) :
    TopMobilePendingBarrier E s r := by
  intro i j hi hj hip hblock
  have hne : i ≠ j := by
    intro heq
    apply horigins.2.2 i hi hip
    rw [heq]
    exact hblock
  have hblockOldOrNew := horigins.2.1 j hj hblock
  rcases horigins.1 i hi hip with hstay | hport | hmove
  · rcases hblockOldOrNew with hblockOld | hnew
    · exact hbarrier i j hi hj hstay hblockOld
    · rcases hnew with ⟨_, hterminal | hnext⟩
      · omega
      · have hbefore :
            i < j + 1 :=
          hbarrier i (j + 1) hi hnext.1 hstay
            (Or.inl hnext.2)
        omega
  · have hz : i = 0 := hport.1
    omega
  · obtain ⟨k, hik, hkp, hEmpty, _⟩ := hmove
    have hk : k < r := by omega
    rcases hblockOldOrNew with hblockOld | hnew
    · have hbefore : k < j :=
        hbarrier k j hk hj hkp hblockOld
      omega
    · rcases hnew with ⟨_, hterminal | hnext⟩
      · omega
      · have hbefore : k < j + 1 :=
          hbarrier k (j + 1) hk hnext.1 hkp
            (Or.inl hnext.2)
        have hneqNext : i ≠ j + 1 := by
          intro heq
          have hsettled :
              topMobileSettled D s r i = true := by
            rw [heq]
            exact hnext.2
          have hnotSettled :
              topMobileSettled D s r i = false := by
            simp [topMobileSettled, topMobileIsSettled, hEmpty]
          rw [hnotSettled] at hsettled
          cases hsettled
        omega

/-!
REMAINING OBLIGATION -- NOT DECLARED:

For all ring C D s r e with TopMobileFixedPair C D s r, show

  TopMobilePendingStepOrigins D
    (topFixedPublicNext ring C D e) s r.

This requires a complete OLD-first-match source-QI, responder-QI,
QC and QO product analysis and the target-offset endpoint frame,
including the cyclic self-pair.  Only after that obligation is
established may the unconditional topMobilePendingBarrierStep be
obtained from topMobilePendingBarrierOfOrigins.

In particular the fixed-public marker lemmas rule out the earlier
interior-beta counterword, but do not themselves establish the
unconditional physical row-origin premise.
-/

end L3
/-!
Further OLD-owner row analysis, target offset geometry,
and an attempt at the unconditional fixed-public
pending-barrier step.  None of this changes the physical protocol.

The input/carry origin analysis is performed at the exact
liveTopPair product, not by assuming QI, QC, and QO exclusive.
-/

namespace L3

set_option autoImplicit false
set_option Elab.async false

private theorem topMobileShortSiteInjective {n : Nat}
    (s : Fin n) (i j : Nat) (hi : i < n) (hj : j < n)
    (he : certSite s i = certSite s j) : i = j := by
  have hv := congrArg Fin.val he
  change (s.val + i) % n = (s.val + j) % n at hv
  by_cases hleft : s.val + i < n
  · rw [Nat.mod_eq_of_lt hleft] at hv
    by_cases hright : s.val + j < n
    · rw [Nat.mod_eq_of_lt hright] at hv
      omega
    · have hge : n ≤ s.val + j := by omega
      have hrem : s.val + j - n < n := by
        have hs := s.isLt
        omega
      rw [Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt hrem] at hv
      omega
  · have hge : n ≤ s.val + i := by omega
    have hrem : s.val + i - n < n := by
      have hs := s.isLt
      omega
    rw [Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt hrem] at hv
    by_cases hright : s.val + j < n
    · rw [Nat.mod_eq_of_lt hright] at hv
      omega
    · have hge' : n ≤ s.val + j := by omega
      have hrem' : s.val + j - n < n := by
        have hs := s.isLt
        omega
      rw [Nat.mod_eq_sub_mod hge',
        Nat.mod_eq_of_lt hrem'] at hv
      omega

theorem topMobileFixedTargetSiteInjective {n : Nat}
    (C D : HeadlineConfiguration n) (s : Fin n) (r i j : Nat)
    (hfixed : TopMobileFixedPair C D s r)
    (hi : i < r) (hj : j < r)
    (he : topMobileSite s r i = topMobileSite s r j) :
    i = j := by
  have hr := topMobileFixedWidthLeRing C D s r hfixed
  exact topMobileShortSiteInjective
    (certSite s r) i j (by omega) (by omega) he

private theorem topMobileRightNeighborInjective {n : Nat}
    (ring : DirectedRing n) (e f : Fin n)
    (h : ring.rightNeighbor e = ring.rightNeighbor f) :
    e = f := by
  apply Fin.ext
  have hv := congrArg Fin.val h
  change (e.val + 1) % n = (f.val + 1) % n at hv
  by_cases he : e.val + 1 < n
  · rw [Nat.mod_eq_of_lt he] at hv
    by_cases hf : f.val + 1 < n
    · rw [Nat.mod_eq_of_lt hf] at hv
      omega
    · have hfn : f.val + 1 = n := by
        have hfLt := f.isLt
        omega
      rw [hfn, Nat.mod_self] at hv
      omega
  · have hen : e.val + 1 = n := by
      have heLt := e.isLt
      omega
    rw [hen, Nat.mod_self] at hv
    by_cases hf : f.val + 1 < n
    · rw [Nat.mod_eq_of_lt hf] at hv
      omega
    · have hfn : f.val + 1 = n := by
        have hfLt := f.isLt
        omega
      omega

/-- An interior responder has its physical source at the immediately
preceding target offset, including the cyclic target r=n. -/
theorem topMobileFixedInteriorPredecessor {n : Nat}
    (ring : DirectedRing n)
    (C D : HeadlineConfiguration n) (s : Fin n)
    (r i : Nat) (e : Fin n)
    (hfixed : TopMobileFixedPair C D s r)
    (hi : i < r) (hpositive : 0 < i)
    (hresponder : ring.rightNeighbor e = topMobileSite s r i) :
    e = topMobileSite s r (i - 1) := by
  have hprev :
      ring.rightNeighbor (topMobileSite s r (i - 1)) =
        topMobileSite s r i := by
    rw [topMobileSiteRightNeighbor]
    have heq : i - 1 + 1 = i := by omega
    rw [heq]
  exact topMobileRightNeighborInjective ring e
    (topMobileSite s r (i - 1)) (hresponder.trans hprev.symm)

/-- A target source with an old terminal responder must be the last
target offset; all nonterminal successor offsets are root-free and
non-markers on the fixed public mask. -/
theorem topMobileFixedTerminalSourceLast {n : Nat}
    (ring : DirectedRing n)
    (C D : HeadlineConfiguration n) (s : Fin n)
    (r j : Nat) (e : Fin n)
    (hfixed : TopMobileFixedPair C D s r)
    (hj : j < r) (he : e = topMobileSite s r j)
    (hterminal :
      topTerminal (D e) (D (ring.rightNeighbor e)) = true) :
    j = r - 1 := by
  by_cases hnext : j + 1 < r
  · have hyl : (D (ring.rightNeighbor e)).l = false := by
      rw [he, topMobileSiteRightNeighbor]
      exact topMobileFixedTargetFollower C D s r (j + 1)
        hfixed hnext
    have hyb : (D (ring.rightNeighbor e)).beta = false := by
      rw [he, topMobileSiteRightNeighbor]
      exact topMobileFixedTargetInteriorBeta C D s r (j + 1)
        hfixed (by omega) hnext
    have hnot :
        topTerminal (D e) (D (ring.rightNeighbor e)) = false := by
      simp [topTerminal, hyl, hyb]
    rw [hnot] at hterminal
    cases hterminal
  · omega

/-- One OLD-QI/QC product result, packaged without collapsing
simultaneous QO actions.  Obstacle means S, X, or live carry. -/
def topMobileAgentObstacle {c : Compiled} (a : Agent c) : Prop :=
  topMobileIsSettled a.qIn = true ∨
  topMobileIsFront a.qIn = true ∨
  topMobileIsLiveCarry a.qCarry = true

def topMobileFieldsObstacle {c : Compiled} (a : TopFields c) : Prop :=
  topMobileIsSettled a.qIn = true ∨
  topMobileIsFront a.qIn = true ∨
  topMobileIsLiveCarry a.qCarry = true

/-- A tail-triggered conversion of an OLD settled source S can
produce S or X, but never a fresh pending P. -/
private theorem topMobileSettledTailChoiceNotPending {a : Nat}
    (v : Fin a) (tail : Bool) :
    (match (if tail = true then (InTok.X : InTok a)
      else .S v tail) with
      | .P _ _ => true
      | _ => false) = false := by
  cases tail <;> rfl

/-- QI source never mints pending: P on the source is an old P. -/
private theorem topMobileOwnerSourcePendingOrigin
    (c : Compiled) (x y : Agent c) (bx byy : Bool)
    (hnew :
      topMobileIsPending (liveTopPair c x y bx byy).x.qIn = true) :
    topMobileIsPending x.qIn = true := by
  try simp only [liveTopPair_x_wIn, liveTopPair_y_wIn, liveTopPair_x_wCarry, liveTopPair_y_wCarry,
    liveTopPair_x_wOut, liveTopPair_y_wOut, liveTopPair_x_qIn, liveTopPair_y_qIn,
    liveTopPair_x_qCarry, liveTopPair_y_qCarry, liveTopPair_x_qOut, liveTopPair_y_qOut] at *
  cases hxl : x.l <;> cases hyl : y.l <;>
    cases hxc : x.qCarry <;> cases hyc : y.qCarry <;>
    cases hxi : x.qIn <;>
    simp [apply_ite InSt.iX, apply_ite InSt.iY, apply_ite InSt.fx, apply_ite InSt.fy, ite_self,
        liveTopPair, liveTopWC, liveTopWI, liveTopWO, liveTopQC,
      liveTopQI, liveTopQO, topMobileIsPending, hxl, hyl, hxc, hyc, hxi,
      topBorder, topTerminal, topInternal,
      QCarry.isOff, QCarry.isL, InTok.isP,
      InTok.isS, InTok.isX, InTok.isE, inT] at hnew ⊢
  all_goals
    cases hyi : y.qIn <;> cases hyb : y.beta <;> cases hxb : x.beta <;>
    simp [hyb, hxb, apply_ite InSt.iX, apply_ite InSt.iY, apply_ite InSt.fx, apply_ite InSt.fy,
        ite_self, liveTopPair, liveTopWC, liveTopWI, liveTopWO, liveTopQC,
      liveTopQI, liveTopQO, topMobileIsPending, hxl, hyl, hxc,
      hyc, hxi, hyi, topBorder, topTerminal, topInternal,
      QCarry.isOff, QCarry.isL, InTok.isP,
      InTok.isS, InTok.isX, InTok.isE, inT] at hnew ⊢
  all_goals
    simp [topMobileSettledTailChoiceNotPending] at hnew

/-- QI responder has only three ways to retain/create a P:
old P, clockwise transport from source into old E, or a QO
port acceptance whose OLD responder beta is true. -/
private theorem topMobileOwnerResponderPendingOrigin
    (c : Compiled) (x y : Agent c) (bx byy : Bool)
    (hnew :
      topMobileIsPending (liveTopPair c x y bx byy).y.qIn = true) :
    topMobileIsPending y.qIn = true ∨
    (topMobileIsPending x.qIn = true ∧ y.qIn = .E) ∨
    y.beta = true := by
  try simp only [liveTopPair_x_wIn, liveTopPair_y_wIn, liveTopPair_x_wCarry, liveTopPair_y_wCarry,
    liveTopPair_x_wOut, liveTopPair_y_wOut, liveTopPair_x_qIn, liveTopPair_y_qIn,
    liveTopPair_x_qCarry, liveTopPair_y_qCarry, liveTopPair_x_qOut, liveTopPair_y_qOut] at *
  cases hxl : x.l <;> cases hyl : y.l <;>
    cases hyb : y.beta <;>
    cases hxc : x.qCarry <;> cases hyc : y.qCarry <;>
    cases hxi : x.qIn <;> cases hyi : y.qIn <;>
    simp [apply_ite InSt.iX, apply_ite InSt.iY, apply_ite InSt.fx, apply_ite InSt.fy, ite_self,
        liveTopPair, liveTopWC, liveTopWI, liveTopWO, liveTopQC,
      liveTopQI, liveTopQO, topMobileIsPending, hxl, hyl,
      hyb, hxc, hyc, hxi, hyi, topBorder, topTerminal, topInternal,
      QCarry.isOff, QCarry.isL, InTok.isP,
      InTok.isS, InTok.isX, InTok.isE, inT,
      OutTok.isD, outT, outV] at hnew ⊢
  all_goals
    cases hqo : x.qOut.isD <;>
    simp [apply_ite InSt.iX, apply_ite InSt.iY, apply_ite InSt.fx, apply_ite InSt.fy, ite_self,
        liveTopPair, liveTopWC, liveTopWI, liveTopWO, liveTopQC,
      liveTopQI, liveTopQO, topMobileIsPending, hxl, hyl,
      hyb, hxc, hyc, hxi, hyi, hqo,
      topBorder, topTerminal, topInternal,
      QCarry.isOff, QCarry.isL, InTok.isP,
      InTok.isS, InTok.isX, InTok.isE, inT,
      OutTok.isD, outT, outV] at hnew ⊢

/-- A newly obstructing source is an old S/X/L, or an old
P converted to S at a terminal or before an old S. -/
private theorem topMobileOwnerSourceObstacleOrigin
    (c : Compiled) (x y : Agent c) (bx byy : Bool)
    (hnew : topMobileFieldsObstacle
      (liveTopPair c x y bx byy).x) :
    topMobileAgentObstacle x ∨
    (topMobileIsPending x.qIn = true ∧
      (topTerminal x y = true ∨ y.qIn.isS = true)) := by
  try simp only [topMobileFieldsObstacle, liveTopPair_x_wIn, liveTopPair_y_wIn,
      liveTopPair_x_wCarry,
      liveTopPair_y_wCarry,
    liveTopPair_x_wOut, liveTopPair_y_wOut, liveTopPair_x_qIn, liveTopPair_y_qIn,
    liveTopPair_x_qCarry, liveTopPair_y_qCarry, liveTopPair_x_qOut, liveTopPair_y_qOut] at *
  cases hxi : x.qIn with
  | S v tail =>
      exact Or.inl (Or.inl (by rw [hxi]; rfl))
  | X =>
      exact Or.inl (Or.inr (Or.inl (by rw [hxi]; rfl)))
  | E =>
      cases hxc : x.qCarry with
      | L carry error =>
          exact Or.inl (Or.inr (Or.inr (by rw [hxc]; rfl)))
      | OFF =>
          cases hxl : x.l <;> cases hyl : y.l <;>
            cases hyc : y.qCarry <;> cases hyi : y.qIn <;>
            cases hyb : y.beta <;> cases hxb : x.beta <;>
            simp [hyb, hxb, apply_ite InSt.iX, apply_ite InSt.iY, apply_ite InSt.fx,
                apply_ite InSt.fy, ite_self, topMobileFieldsObstacle, liveTopPair, liveTopWC,
                liveTopWI, liveTopWO, liveTopQC,
      liveTopQI, liveTopQO,
              topMobileAgentObstacle, topMobileIsSettled,
              topMobileIsFront, topMobileIsLiveCarry,
              hxi, hxc, hyc, hyi, hxl, hyl,
              QCarry.isOff, QCarry.isL, InTok.isP,
              InTok.isS, InTok.isX, InTok.isE, inT,
              topTerminal, topInternal, topBorder] at hnew ⊢
  | P v tail =>
      cases hxc : x.qCarry with
      | L carry error =>
          exact Or.inl (Or.inr (Or.inr (by rw [hxc]; rfl)))
      | OFF =>
          cases ht : topTerminal x y with
          | true =>
              exact Or.inr ⟨rfl, Or.inl rfl⟩
          | false =>
              cases hs : y.qIn.isS with
              | true =>
                  exact Or.inr ⟨rfl, Or.inr rfl⟩
              | false =>
                  cases hxl : x.l <;> cases hyl : y.l <;>
                    cases hyc : y.qCarry <;> cases hyi : y.qIn <;>
                    cases hyb : y.beta <;> cases hxb : x.beta <;>
                    simp [hyb, hxb, apply_ite InSt.iX, apply_ite InSt.iY, apply_ite InSt.fx,
                        apply_ite InSt.fy, ite_self, topMobileFieldsObstacle, liveTopPair,
                        liveTopWC, liveTopWI, liveTopWO, liveTopQC,
      liveTopQI, liveTopQO,
                      topMobileAgentObstacle, topMobileIsSettled,
                      topMobileIsFront, topMobileIsLiveCarry,
                      hxi, hxc, hyc, hyi, hxl, hyl,
                      ht, hs, QCarry.isOff, QCarry.isL,
                      InTok.isP, InTok.isS, InTok.isX, InTok.isE,
                      topBorder, topInternal, topTerminal] at hnew ⊢
                  all_goals (try simp [topTerminal, hyl, hyb] at ht)
                  all_goals (try simp [hyi, InTok.isS] at hs)

/-- A newly obstructing responder was already S/X/L in the OLD
record: QC2 and X-advance require OLD responder S. -/
private theorem topMobileOwnerResponderObstacleOrigin
    (c : Compiled) (x y : Agent c) (bx byy : Bool)
    (hnew : topMobileFieldsObstacle
      (liveTopPair c x y bx byy).y) :
    topMobileAgentObstacle y := by
  try simp only [topMobileFieldsObstacle, liveTopPair_x_wIn, liveTopPair_y_wIn,
      liveTopPair_x_wCarry,
      liveTopPair_y_wCarry,
    liveTopPair_x_wOut, liveTopPair_y_wOut, liveTopPair_x_qIn, liveTopPair_y_qIn,
    liveTopPair_x_qCarry, liveTopPair_y_qCarry, liveTopPair_x_qOut, liveTopPair_y_qOut] at *
  cases hyi : y.qIn with
  | S v tail =>
      exact Or.inl (by rw [hyi]; rfl)
  | X =>
      exact Or.inr (Or.inl (by rw [hyi]; rfl))
  | E =>
      cases hyc : y.qCarry with
      | L carry error =>
          exact Or.inr (Or.inr (by rw [hyc]; rfl))
      | OFF =>
          cases hxl : x.l <;> cases hyl : y.l <;>
            cases hxc : x.qCarry <;> cases hxi : x.qIn <;>
            cases hyb : y.beta <;> cases hqo : x.qOut <;>
            simp [apply_ite InSt.iX, apply_ite InSt.iY, apply_ite InSt.fx, apply_ite InSt.fy,
                ite_self, topMobileFieldsObstacle, liveTopPair, liveTopWC, liveTopWI, liveTopWO,
                liveTopQC,
      liveTopQI, liveTopQO,
              topMobileAgentObstacle, topMobileIsSettled,
              topMobileIsFront, topMobileIsLiveCarry,
              hxl, hyl, hxc, hxi, hyi, hyc, hyb, hqo,
              QCarry.isOff, QCarry.isL, InTok.isE,
              InTok.isP, InTok.isS, InTok.isX, OutTok.isD,
              topTerminal, topInternal, topBorder] at hnew ⊢
  | P v tail =>
      cases hyc : y.qCarry with
      | L carry error =>
          exact Or.inr (Or.inr (by rw [hyc]; rfl))
      | OFF =>
          cases hxl : x.l <;> cases hyl : y.l <;>
            cases hxc : x.qCarry <;> cases hxi : x.qIn <;>
            cases hyb : y.beta <;> cases hqo : x.qOut <;>
            simp [apply_ite InSt.iX, apply_ite InSt.iY, apply_ite InSt.fx, apply_ite InSt.fy,
                ite_self, topMobileFieldsObstacle, liveTopPair, liveTopWC, liveTopWI, liveTopWO,
                liveTopQC,
      liveTopQI, liveTopQO,
              topMobileAgentObstacle, topMobileIsSettled,
              topMobileIsFront, topMobileIsLiveCarry,
              hxl, hyl, hxc, hxi, hyi, hyc, hyb, hqo,
              QCarry.isOff, QCarry.isL, InTok.isE,
              InTok.isP, InTok.isS, InTok.isX, OutTok.isD,
              topTerminal, topInternal, topBorder] at hnew ⊢

/-- A newly pending input cannot share its source with a live
QC carry, even when QO acted simultaneously. -/
private theorem topMobileOwnerSourcePendingCarryOff
    (c : Compiled) (x y : Agent c) (bx byy : Bool)
    (hnew :
      topMobileIsPending (liveTopPair c x y bx byy).x.qIn = true) :
    (liveTopPair c x y bx byy).x.qCarry = .OFF := by
  try simp only [liveTopPair_x_wIn, liveTopPair_y_wIn, liveTopPair_x_wCarry, liveTopPair_y_wCarry,
    liveTopPair_x_wOut, liveTopPair_y_wOut, liveTopPair_x_qIn, liveTopPair_y_qIn,
    liveTopPair_x_qCarry, liveTopPair_y_qCarry, liveTopPair_x_qOut, liveTopPair_y_qOut] at *
  have hold := topMobileOwnerSourcePendingOrigin c x y bx byy hnew
  cases hxi : x.qIn with
  | P v tail =>
      cases hxc : x.qCarry with
      | OFF =>
          simp [apply_ite InSt.iX, apply_ite InSt.iY, apply_ite InSt.fx, apply_ite InSt.fy,
              ite_self, liveTopPair, liveTopWC, liveTopWI, liveTopWO, liveTopQC,
      liveTopQI, liveTopQO, hxi, hxc, QCarry.isOff,
            QCarry.isL, InTok.isS, topBorder]
      | L carry error =>
          cases hxl : x.l <;> cases hyl : y.l <;>
            cases hyc : y.qCarry <;> cases hyi : y.qIn <;>
            simp [apply_ite InSt.iX, apply_ite InSt.iY, apply_ite InSt.fx, apply_ite InSt.fy,
                ite_self, liveTopPair, liveTopWC, liveTopWI, liveTopWO, liveTopQC,
      liveTopQI, liveTopQO, topMobileIsPending,
              hxi, hxc, hxl, hyl, hyc, hyi, QCarry.isOff,
              QCarry.isL, InTok.isE, InTok.isS, InTok.isP,
              topTerminal, topInternal, topBorder] at hnew
  | E =>
      simp [topMobileIsPending, hxi] at hold
  | X =>
      simp [topMobileIsPending, hxi] at hold
  | S v tail =>
      simp [topMobileIsPending, hxi] at hold

/-- A newly pending responder is also carry-free: QC2 needs OLD
responder S, whereas both ways to inject a P need OLD responder E. -/
private theorem topMobileOwnerResponderPendingCarryOff
    (c : Compiled) (x y : Agent c) (bx byy : Bool)
    (hnew :
      topMobileIsPending (liveTopPair c x y bx byy).y.qIn = true) :
    (liveTopPair c x y bx byy).y.qCarry = .OFF := by
  try simp only [liveTopPair_x_wIn, liveTopPair_y_wIn, liveTopPair_x_wCarry, liveTopPair_y_wCarry,
    liveTopPair_x_wOut, liveTopPair_y_wOut, liveTopPair_x_qIn, liveTopPair_y_qIn,
    liveTopPair_x_qCarry, liveTopPair_y_qCarry, liveTopPair_x_qOut, liveTopPair_y_qOut] at *
  cases hyc : y.qCarry <;> cases hyi : y.qIn <;>
    cases hxl : x.l <;> cases hyl : y.l <;>
    cases hxc : x.qCarry <;> cases hxi : x.qIn <;>
    simp [apply_ite InSt.iX, apply_ite InSt.iY, apply_ite InSt.fx, apply_ite InSt.fy, ite_self,
        liveTopPair, liveTopWC, liveTopWI, liveTopWO, liveTopQC,
      liveTopQI, liveTopQO, topMobileIsPending,
      hyc, hyi, hxl, hyl, hxc, hxi,
      QCarry.isOff, QCarry.isL, InTok.isE,
      InTok.isS, InTok.isP, InTok.isX,
      topTerminal, topInternal, topBorder] at hnew ⊢
  all_goals
    cases hyb : y.beta <;> cases hqo : x.qOut.isD <;>
    simp [apply_ite InSt.iX, apply_ite InSt.iY, apply_ite InSt.fx, apply_ite InSt.fy, ite_self,
        liveTopPair, liveTopWC, liveTopWI, liveTopWO, liveTopQC,
      liveTopQI, liveTopQO, topMobileIsPending,
      hyc, hyi, hxl, hyl, hxc, hxi, hyb, hqo,
      QCarry.isOff, QCarry.isL, InTok.isE,
      InTok.isS, InTok.isP, InTok.isX, OutTok.isD,
      topTerminal, topInternal, topBorder] at hnew ⊢

/-- All target sites are projections of exactly one OLD owner pair:
source, responder, or unrelated frame.  In particular there is no
poststep public restoration of checker QI or QC. -/
private theorem topMobileSelectedInputProjection {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (C D : HeadlineConfiguration n) (e i : Fin n) :
    (topFixedPublicNext ring C D e i).qIn =
      (if i = e then (topMobileLiteralTopOwner ring D e).x.qIn
      else if i = ring.rightNeighbor e then
        (topMobileLiteralTopOwner ring D e).y.qIn
      else (D i).qIn) := by
  split
  · next he =>
      rw [he]
      exact (topMobileLiteralSourceFields ring C D e).1
  · split
    · next hy =>
        rw [hy]
        exact (topMobileLiteralResponderFields ring hn C D e).1
    · next he hy =>
        exact (topMobileLiteralAwayFields ring C D e i he hy).1

private theorem topMobileSelectedCarryProjection {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (C D : HeadlineConfiguration n) (e i : Fin n) :
    (topFixedPublicNext ring C D e i).qCarry =
      (if i = e then (topMobileLiteralTopOwner ring D e).x.qCarry
      else if i = ring.rightNeighbor e then
        (topMobileLiteralTopOwner ring D e).y.qCarry
      else (D i).qCarry) := by
  split
  · next he =>
      rw [he]
      exact (topMobileLiteralSourceFields ring C D e).2.1
  · split
    · next hy =>
        rw [hy]
        exact (topMobileLiteralResponderFields ring hn C D e).2.1
    · next he hy =>
        exact (topMobileLiteralAwayFields ring C D e i he hy).2.1

/-- Weak, geometrically sufficient origins: target border birth
need not carry a private E/OFF receipt for the order proof. -/
def TopMobilePendingWeakOrigins {n : Nat}
    (D E : HeadlineConfiguration n) (s : Fin n) (r : Nat) : Prop :=
  (∀ i : Nat, i < r →
    topMobilePending E s r i = true →
    i = 0 ∨ topMobilePending D s r i = true ∨
    ∃ k : Nat, i = k + 1 ∧
      topMobilePending D s r k = true ∧
      topMobileInput D s r i = .E) ∧
  (∀ j : Nat, j < r →
    TopMobileBarrierObstacle E s r j →
    TopMobileBarrierObstacle D s r j ∨
    (topMobilePending D s r j = true ∧
      (j = r - 1 ∨
        (j + 1 < r ∧
          topMobileSettled D s r (j + 1) = true)))) ∧
  (∀ i : Nat, i < r →
    topMobilePending E s r i = true →
    ¬ TopMobileBarrierObstacle E s r i)

/-- Reuses the exact P/barrier order argument, but only the birth
index zero is relevant, not the port's private offer receipt. -/
theorem topMobilePendingBarrierOfWeakOrigins {n : Nat}
    (D E : HeadlineConfiguration n) (s : Fin n) (r : Nat)
    (hbarrier : TopMobilePendingBarrier D s r)
    (horigins : TopMobilePendingWeakOrigins D E s r) :
    TopMobilePendingBarrier E s r := by
  intro i j hi hj hip hblock
  have hne : i ≠ j := by
    intro heq
    apply horigins.2.2 i hi hip
    rw [heq]
    exact hblock
  have hblockOldOrNew := horigins.2.1 j hj hblock
  rcases horigins.1 i hi hip with hz | hstay | hmove
  · omega
  · rcases hblockOldOrNew with hblockOld | hnew
    · exact hbarrier i j hi hj hstay hblockOld
    · rcases hnew with ⟨_, hterminal | hnext⟩
      · omega
      · have hbefore : i < j + 1 :=
          hbarrier i (j + 1) hi hnext.1 hstay
            (Or.inl hnext.2)
        omega
  · obtain ⟨k, hik, hkp, hEmpty⟩ := hmove
    have hk : k < r := by omega
    rcases hblockOldOrNew with hblockOld | hnew
    · have hbefore : k < j :=
        hbarrier k j hk hj hkp hblockOld
      omega
    · rcases hnew with ⟨_, hterminal | hnext⟩
      · omega
      · have hbefore : k < j + 1 :=
          hbarrier k (j + 1) hk hnext.1 hkp
            (Or.inl hnext.2)
        have hneqNext : i ≠ j + 1 := by
          intro heq
          have hsettled :
              topMobileSettled D s r i = true := by
            rw [heq]
            exact hnext.2
          have hnotSettled :
              topMobileSettled D s r i = false := by
            simp [topMobileSettled, topMobileIsSettled, hEmpty]
          rw [hnotSettled] at hsettled
          cases hsettled
        omega

/-!
The following final physical lifting is a PROOF OUTLINE, not a
certified row theorem.  Its four semantic ingredients are:
 (a) target-site injectivity and interior-predecessor geometry;
 (b) the six exact liveTopPair owner origin/off lemmas above;
 (c) source/responder/away projection; and
 (d) topMobilePendingBarrierOfWeakOrigins.

The omitted section is the exhaustive connection of (a)--(c)
to TopMobilePendingWeakOrigins for all selected edges.  No
declaration named topMobilePendingBarrierStep is provided here:
that name is reserved for a genuine unconditional proof after
the physical lifting has been checked.  No fixed-pair counterword
has been established either.
-/

end L3


/-!
Fixed-public pending origin lifting, same-clock one-edge and
word-level barrier closure.

The weak-origin third clause requires the OLD pending barrier for
away-site carry exclusion. Merely fixing public markers does not imply
that arbitrary private qIn=P and qCarry=L at an untouched site are
disjoint. No additional unjustified private scratch hypothesis is made.
-/

namespace L3

set_option autoImplicit false
set_option Elab.async false

/-! Selected pair projections with the exact frozen-public successor.
The source and away cases use both selected projection lemmas. The
responder case uses their already-proved endpoint specialization. -/

private theorem topMobileWindowSourceFields {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (C D : HeadlineConfiguration n) (s : Fin n)
    (r j : Nat) (e : Fin n)
    (he : topMobileSite s r j = e) :
    topMobileInput (topFixedPublicNext ring C D e) s r j =
        (topMobileLiteralTopOwner ring D e).x.qIn ∧
      topMobileCarry (topFixedPublicNext ring C D e) s r j =
        (topMobileLiteralTopOwner ring D e).x.qCarry := by
  constructor
  · change ((topFixedPublicNext ring C D e)
      (topMobileSite s r j)).qIn = _
    simpa only [if_pos he] using
      (topMobileSelectedInputProjection ring hn C D e
        (topMobileSite s r j))
  · change ((topFixedPublicNext ring C D e)
      (topMobileSite s r j)).qCarry = _
    simpa only [if_pos he] using
      (topMobileSelectedCarryProjection ring hn C D e
        (topMobileSite s r j))

private theorem topMobileWindowResponderFields {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (C D : HeadlineConfiguration n) (s : Fin n)
    (r j : Nat) (e : Fin n)
    (he : topMobileSite s r j = ring.rightNeighbor e) :
    topMobileInput (topFixedPublicNext ring C D e) s r j =
        (topMobileLiteralTopOwner ring D e).y.qIn ∧
      topMobileCarry (topFixedPublicNext ring C D e) s r j =
        (topMobileLiteralTopOwner ring D e).y.qCarry := by
  constructor
  · change ((topFixedPublicNext ring C D e)
      (topMobileSite s r j)).qIn = _
    rw [he]
    exact (topMobileLiteralResponderFields ring hn C D e).1
  · change ((topFixedPublicNext ring C D e)
      (topMobileSite s r j)).qCarry = _
    rw [he]
    exact (topMobileLiteralResponderFields ring hn C D e).2.1

private theorem topMobileWindowAwayFields {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (C D : HeadlineConfiguration n) (s : Fin n)
    (r j : Nat) (e : Fin n)
    (he : topMobileSite s r j ≠ e)
    (hy : topMobileSite s r j ≠ ring.rightNeighbor e) :
    topMobileInput (topFixedPublicNext ring C D e) s r j =
        topMobileInput D s r j ∧
      topMobileCarry (topFixedPublicNext ring C D e) s r j =
        topMobileCarry D s r j := by
  constructor
  · change ((topFixedPublicNext ring C D e)
      (topMobileSite s r j)).qIn =
        (D (topMobileSite s r j)).qIn
    simpa only [if_neg he, if_neg hy] using
      (topMobileSelectedInputProjection ring hn C D e
        (topMobileSite s r j))
  · change ((topFixedPublicNext ring C D e)
      (topMobileSite s r j)).qCarry =
        (D (topMobileSite s r j)).qCarry
    simpa only [if_neg he, if_neg hy] using
      (topMobileSelectedCarryProjection ring hn C D e
        (topMobileSite s r j))

/-! Unfold the OLD selected owner once, then reuse exactly the six
proved owner-origin and pending/carry-off equations. The actual
SI-resolved beta values remain implicit arguments of liveTopPair. -/

private theorem topMobileLiteralSourcePendingOld {n : Nat}
    (ring : DirectedRing n) (D : HeadlineConfiguration n)
    (e : Fin n)
    (h : topMobileIsPending
      (topMobileLiteralTopOwner ring D e).x.qIn = true) :
    topMobileIsPending (D e).qIn = true := by
  unfold topMobileLiteralTopOwner at h
  exact topMobileOwnerSourcePendingOrigin
    (compileAdvice (ceilLogTwo n))
    (D e) (D (ring.rightNeighbor e)) _ _ h

private theorem topMobileLiteralResponderPendingOld {n : Nat}
    (ring : DirectedRing n) (D : HeadlineConfiguration n)
    (e : Fin n)
    (h : topMobileIsPending
      (topMobileLiteralTopOwner ring D e).y.qIn = true) :
    topMobileIsPending (D (ring.rightNeighbor e)).qIn = true ∨
      (topMobileIsPending (D e).qIn = true ∧
        (D (ring.rightNeighbor e)).qIn = .E) ∨
      (D (ring.rightNeighbor e)).beta = true := by
  unfold topMobileLiteralTopOwner at h
  exact topMobileOwnerResponderPendingOrigin
    (compileAdvice (ceilLogTwo n))
    (D e) (D (ring.rightNeighbor e)) _ _ h

private theorem topMobileLiteralSourceObstacleOld {n : Nat}
    (ring : DirectedRing n) (D : HeadlineConfiguration n)
    (e : Fin n)
    (h : topMobileFieldsObstacle
      (topMobileLiteralTopOwner ring D e).x) :
    topMobileAgentObstacle (D e) ∨
      (topMobileIsPending (D e).qIn = true ∧
        (topTerminal (D e) (D (ring.rightNeighbor e)) = true ∨
          (D (ring.rightNeighbor e)).qIn.isS = true)) := by
  unfold topMobileLiteralTopOwner at h
  exact topMobileOwnerSourceObstacleOrigin
    (compileAdvice (ceilLogTwo n))
    (D e) (D (ring.rightNeighbor e)) _ _ h

private theorem topMobileLiteralResponderObstacleOld {n : Nat}
    (ring : DirectedRing n) (D : HeadlineConfiguration n)
    (e : Fin n)
    (h : topMobileFieldsObstacle
      (topMobileLiteralTopOwner ring D e).y) :
    topMobileAgentObstacle (D (ring.rightNeighbor e)) := by
  unfold topMobileLiteralTopOwner at h
  exact topMobileOwnerResponderObstacleOrigin
    (compileAdvice (ceilLogTwo n))
    (D e) (D (ring.rightNeighbor e)) _ _ h

private theorem topMobileLiteralSourcePendingCarryOff {n : Nat}
    (ring : DirectedRing n) (D : HeadlineConfiguration n)
    (e : Fin n)
    (h : topMobileIsPending
      (topMobileLiteralTopOwner ring D e).x.qIn = true) :
    (topMobileLiteralTopOwner ring D e).x.qCarry = .OFF := by
  unfold topMobileLiteralTopOwner at h ⊢
  exact topMobileOwnerSourcePendingCarryOff
    (compileAdvice (ceilLogTwo n))
    (D e) (D (ring.rightNeighbor e)) _ _ h

private theorem topMobileLiteralResponderPendingCarryOff {n : Nat}
    (ring : DirectedRing n) (D : HeadlineConfiguration n)
    (e : Fin n)
    (h : topMobileIsPending
      (topMobileLiteralTopOwner ring D e).y.qIn = true) :
    (topMobileLiteralTopOwner ring D e).y.qCarry = .OFF := by
  unfold topMobileLiteralTopOwner at h ⊢
  exact topMobileOwnerResponderPendingCarryOff
    (compileAdvice (ceilLogTwo n))
    (D e) (D (ring.rightNeighbor e)) _ _ h

/-! Pure local conversions between the three checker slots and
the window predicates. No equality of full physical configurations
is used. -/

private theorem topMobileObstacleFromFields {n : Nat}
    (E : HeadlineConfiguration n) (s : Fin n) (r j : Nat)
    (input : InTok (compileAdvice (ceilLogTwo n)).topA)
    (carry : QCarry)
    (hinput : topMobileInput E s r j = input)
    (hcarry : topMobileCarry E s r j = carry)
    (h : TopMobileBarrierObstacle E s r j) :
    topMobileIsSettled input = true ∨
      topMobileIsFront input = true ∨
      topMobileIsLiveCarry carry = true := by
  change topMobileIsSettled (topMobileInput E s r j) = true ∨
    topMobileIsFront (topMobileInput E s r j) = true ∨
    topMobileIsLiveCarry (topMobileCarry E s r j) = true at h
  rw [hinput, hcarry] at h
  exact h

private theorem topMobilePendingCarryOffNoObstacle {a : Nat}
    (input : InTok a) (carry : QCarry)
    (hp : topMobileIsPending input = true)
    (hc : carry = .OFF) :
    ¬ (topMobileIsSettled input = true ∨
       topMobileIsFront input = true ∨
       topMobileIsLiveCarry carry = true) := by
  cases input <;>
    simp [topMobileIsPending, topMobileIsSettled,
      topMobileIsFront, topMobileIsLiveCarry, hc] at hp ⊢

private theorem topMobilePendingNoObstacleOfOff {n : Nat}
    (E : HeadlineConfiguration n) (s : Fin n) (r i : Nat)
    (hp : topMobilePending E s r i = true)
    (hc : topMobileCarry E s r i = .OFF) :
    ¬ TopMobileBarrierObstacle E s r i := by
  change topMobileIsPending (topMobileInput E s r i) = true at hp
  change ¬ (topMobileIsSettled (topMobileInput E s r i) = true ∨
    topMobileIsFront (topMobileInput E s r i) = true ∨
    topMobileIsLiveCarry (topMobileCarry E s r i) = true)
  exact topMobilePendingCarryOffNoObstacle
    (topMobileInput E s r i) (topMobileCarry E s r i) hp hc

private theorem topMobileOldPendingCarryOff {n : Nat}
    (D : HeadlineConfiguration n) (s : Fin n) (r i : Nat)
    (hbar : TopMobilePendingBarrier D s r)
    (hi : i < r)
    (hp : topMobilePending D s r i = true) :
    topMobileCarry D s r i = .OFF := by
  cases hc : topMobileCarry D s r i with
  | OFF => rfl
  | L carry error =>
      have hob : TopMobileBarrierObstacle D s r i :=
        Or.inr (Or.inr (by
          change topMobileIsLiveCarry (topMobileCarry D s r i) = true
          rw [hc]
          rfl))
      have hbad := hbar i i hi hi hp hob
      omega

/-! FIRST WEAK ORIGIN: new pending is an old resident, a
one-offset move, or a port admission at the unique marker zero. -/

private theorem topMobilePendingOriginAtWindow {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (C D : HeadlineConfiguration n) (s : Fin n)
    (r : Nat) (e : Fin n)
    (hfixed : TopMobileFixedPair C D s r) :
    ∀ i : Nat, i < r →
      topMobilePending (topFixedPublicNext ring C D e) s r i = true →
      i = 0 ∨ topMobilePending D s r i = true ∨
        ∃ k : Nat, i = k + 1 ∧
          topMobilePending D s r k = true ∧
          topMobileInput D s r i = .E := by
  intro i hi hp
  by_cases he : topMobileSite s r i = e
  · have hfield := topMobileWindowSourceFields
      ring hn C D s r i e he
    have hnew : topMobileIsPending
        (topMobileLiteralTopOwner ring D e).x.qIn = true := by
      change topMobileIsPending
        (topMobileInput (topFixedPublicNext ring C D e) s r i) =
          true at hp
      rw [hfield.1] at hp
      exact hp
    have hold := topMobileLiteralSourcePendingOld ring D e hnew
    right
    left
    change topMobileIsPending (D (topMobileSite s r i)).qIn = true
    rw [he]
    exact hold
  · by_cases hy :
        topMobileSite s r i = ring.rightNeighbor e
    · by_cases hz : i = 0
      · exact Or.inl hz
      · have hpos : 0 < i := by omega
        have hfield := topMobileWindowResponderFields
          ring hn C D s r i e hy
        have hnew : topMobileIsPending
            (topMobileLiteralTopOwner ring D e).y.qIn = true := by
          change topMobileIsPending
            (topMobileInput (topFixedPublicNext ring C D e) s r i) =
              true at hp
          rw [hfield.1] at hp
          exact hp
        rcases topMobileLiteralResponderPendingOld ring D e hnew with
          hstay | hmove | hbeta
        · right
          left
          change topMobileIsPending
            (D (topMobileSite s r i)).qIn = true
          rw [hy]
          exact hstay
        · obtain ⟨hsource, hEmpty⟩ := hmove
          have hprev := topMobileFixedInteriorPredecessor
            ring C D s r i e hfixed hi hpos hy.symm
          have hsourceAt :
              topMobilePending D s r (i - 1) = true := by
            change topMobileIsPending
              (D (topMobileSite s r (i - 1))).qIn = true
            rw [← hprev]
            exact hsource
          have hEmptyAt : topMobileInput D s r i = .E := by
            change (D (topMobileSite s r i)).qIn = .E
            rw [hy]
            exact hEmpty
          exact Or.inr (Or.inr
            ⟨i - 1, by omega, hsourceAt, hEmptyAt⟩)
        · have hnot := topMobileFixedTargetInteriorBeta
            C D s r i hfixed hpos hi
          rw [hy] at hnot
          rw [hnot] at hbeta
          cases hbeta
    · have hfield := topMobileWindowAwayFields
        ring hn C D s r i e he hy
      right
      left
      change topMobileIsPending
        (topMobileInput D s r i) = true
      change topMobileIsPending
        (topMobileInput (topFixedPublicNext ring C D e) s r i) =
          true at hp
      rw [hfield.1] at hp
      exact hp

/-! SECOND WEAK ORIGIN: newly blocking source comes only from
an OLD blocker or the OLD pending that settled at terminal/before
the OLD settled successor. A responder blocker must be old. -/

private theorem topMobileObstacleOriginAtWindow {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (C D : HeadlineConfiguration n) (s : Fin n)
    (r : Nat) (e : Fin n)
    (hfixed : TopMobileFixedPair C D s r) :
    ∀ j : Nat, j < r →
      TopMobileBarrierObstacle
        (topFixedPublicNext ring C D e) s r j →
      TopMobileBarrierObstacle D s r j ∨
      (topMobilePending D s r j = true ∧
        (j = r - 1 ∨
          (j + 1 < r ∧
            topMobileSettled D s r (j + 1) = true))) := by
  intro j hj hblock
  by_cases he : topMobileSite s r j = e
  · have hfield := topMobileWindowSourceFields
      ring hn C D s r j e he
    have hlocal : topMobileFieldsObstacle
        (topMobileLiteralTopOwner ring D e).x :=
      topMobileObstacleFromFields
        (topFixedPublicNext ring C D e) s r j
        (topMobileLiteralTopOwner ring D e).x.qIn
        (topMobileLiteralTopOwner ring D e).x.qCarry
        hfield.1 hfield.2 hblock
    rcases topMobileLiteralSourceObstacleOld ring D e hlocal with
      hold | hnew
    · left
      change topMobileAgentObstacle (D (topMobileSite s r j))
      rw [he]
      exact hold
    · right
      obtain ⟨hp, hreason⟩ := hnew
      have hpAt : topMobilePending D s r j = true := by
        change topMobileIsPending
          (D (topMobileSite s r j)).qIn = true
        rw [he]
        exact hp
      refine ⟨hpAt, ?_⟩
      rcases hreason with hterminal | hsettled
      · exact Or.inl (topMobileFixedTerminalSourceLast
          ring C D s r j e hfixed hj he.symm hterminal)
      · by_cases hnext : j + 1 < r
        · right
          refine ⟨hnext, ?_⟩
          change topMobileIsSettled
            (D (topMobileSite s r (j + 1))).qIn = true
          rw [← topMobileSiteRightNeighbor ring s r j, he]
          cases hq : (D (ring.rightNeighbor e)).qIn <;>
            simp [InTok.isS, topMobileIsSettled, hq] at hsettled ⊢
        · left
          omega
  · by_cases hy :
        topMobileSite s r j = ring.rightNeighbor e
    · have hfield := topMobileWindowResponderFields
        ring hn C D s r j e hy
      have hlocal : topMobileFieldsObstacle
          (topMobileLiteralTopOwner ring D e).y :=
        topMobileObstacleFromFields
          (topFixedPublicNext ring C D e) s r j
          (topMobileLiteralTopOwner ring D e).y.qIn
          (topMobileLiteralTopOwner ring D e).y.qCarry
          hfield.1 hfield.2 hblock
      have hold :=
        topMobileLiteralResponderObstacleOld ring D e hlocal
      left
      change topMobileAgentObstacle (D (topMobileSite s r j))
      rw [hy]
      exact hold
    · have hfield := topMobileWindowAwayFields
        ring hn C D s r j e he hy
      have hold : TopMobileBarrierObstacle D s r j :=
        topMobileObstacleFromFields
          (topFixedPublicNext ring C D e) s r j
          (topMobileInput D s r j) (topMobileCarry D s r j)
          hfield.1 hfield.2 hblock
      exact Or.inl hold

/-! THIRD WEAK ORIGIN: the selected owner makes new P carry-free;
at an away site the OLD barrier supplies the missing P/L exclusion. -/

private theorem topMobilePendingNoObstacleAtWindow {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (C D : HeadlineConfiguration n) (s : Fin n)
    (r : Nat) (e : Fin n)
    (hbarrier : TopMobilePendingBarrier D s r) :
    ∀ i : Nat, i < r →
      topMobilePending (topFixedPublicNext ring C D e) s r i =
        true →
      ¬ TopMobileBarrierObstacle
        (topFixedPublicNext ring C D e) s r i := by
  intro i hi hp
  by_cases he : topMobileSite s r i = e
  · have hfield := topMobileWindowSourceFields
      ring hn C D s r i e he
    have hnew : topMobileIsPending
        (topMobileLiteralTopOwner ring D e).x.qIn = true := by
      change topMobileIsPending
        (topMobileInput (topFixedPublicNext ring C D e) s r i) =
          true at hp
      rw [hfield.1] at hp
      exact hp
    have hc :
        topMobileCarry (topFixedPublicNext ring C D e) s r i =
          .OFF :=
      hfield.2.trans
        (topMobileLiteralSourcePendingCarryOff ring D e hnew)
    exact topMobilePendingNoObstacleOfOff
      (topFixedPublicNext ring C D e) s r i hp hc
  · by_cases hy :
        topMobileSite s r i = ring.rightNeighbor e
    · have hfield := topMobileWindowResponderFields
        ring hn C D s r i e hy
      have hnew : topMobileIsPending
          (topMobileLiteralTopOwner ring D e).y.qIn = true := by
        change topMobileIsPending
          (topMobileInput (topFixedPublicNext ring C D e) s r i) =
            true at hp
        rw [hfield.1] at hp
        exact hp
      have hc :
          topMobileCarry (topFixedPublicNext ring C D e) s r i =
            .OFF :=
        hfield.2.trans
          (topMobileLiteralResponderPendingCarryOff ring D e hnew)
      exact topMobilePendingNoObstacleOfOff
        (topFixedPublicNext ring C D e) s r i hp hc
    · have hfield := topMobileWindowAwayFields
        ring hn C D s r i e he hy
      have hpOld : topMobilePending D s r i = true := by
        change topMobileIsPending (topMobileInput D s r i) =
          true
        change topMobileIsPending
          (topMobileInput (topFixedPublicNext ring C D e) s r i) =
            true at hp
        rw [hfield.1] at hp
        exact hp
      have hcOld : topMobileCarry D s r i = .OFF :=
        topMobileOldPendingCarryOff D s r i hbarrier hi hpOld
      have hc :
          topMobileCarry (topFixedPublicNext ring C D e) s r i =
            .OFF := hfield.2.trans hcOld
      exact topMobilePendingNoObstacleOfOff
        (topFixedPublicNext ring C D e) s r i hp hc

/-- The actual OLD-first-match selected checker owner satisfies the
three weak-origin clauses on every fixed-public edge, PROVIDED the
old barrier excludes arbitrary untouched P/L coincidences.
No additional row/ghost premise is used. -/
theorem topMobilePendingWeakOriginsFixed {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (C D : HeadlineConfiguration n) (s : Fin n)
    (r : Nat) (e : Fin n)
    (hfixed : TopMobileFixedPair C D s r)
    (hbarrier : TopMobilePendingBarrier D s r) :
    TopMobilePendingWeakOrigins D
      (topFixedPublicNext ring C D e) s r := by
  exact ⟨topMobilePendingOriginAtWindow ring hn C D s r e hfixed,
    topMobileObstacleOriginAtWindow ring hn C D s r e hfixed,
    topMobilePendingNoObstacleAtWindow
      ring hn C D s r e hbarrier⟩

/-- Fixed-public, one selected scheduler service. In particular the
unconditional claim is relative to the SAME fixed-pair entrance and
old barrier; no false assertion for arbitrary Cartesian scratch. -/
theorem topMobilePendingBarrierStep {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (C D : HeadlineConfiguration n) (s : Fin n)
    (r : Nat) (e : Fin n)
    (hfixed : TopMobileFixedPair C D s r)
    (hbarrier : TopMobilePendingBarrier D s r) :
    TopMobilePendingBarrier
      (topFixedPublicNext ring C D e) s r := by
  exact topMobilePendingBarrierOfWeakOrigins
    D (topFixedPublicNext ring C D e) s r
    hbarrier
    (topMobilePendingWeakOriginsFixed ring hn C D s r e
      hfixed hbarrier)

/-- The frozen-public mask is restored on every selected edge,
including at cyclic target offsets. -/
theorem topMobileFixedPairStep {n : Nat}
    (ring : DirectedRing n)
    (C D : HeadlineConfiguration n) (s : Fin n)
    (r : Nat) (e : Fin n)
    (hfixed : TopMobileFixedPair C D s r) :
    TopMobileFixedPair C (topFixedPublicNext ring C D e) s r := by
  refine ⟨hfixed.1, hfixed.2.1, ?_⟩
  intro i
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- Finite selected-edge iteration of the original fixed-trace
physical transition, without changing the public mask. -/
def topMobileFixedWordRun {n : Nat}
    (ring : DirectedRing n) (C D : HeadlineConfiguration n)
    (word : List (Fin n)) : HeadlineConfiguration n :=
  word.foldl (topFixedPublicNext ring C) D

/-- Same-scheduler word closure of the pending-left-of-obstacles
barrier, using the fixed-pair step and no new private scratch axiom. -/
theorem topMobilePendingBarrierWord {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (C : HeadlineConfiguration n) (s : Fin n) (r : Nat)
    (word : List (Fin n)) :
    ∀ D : HeadlineConfiguration n,
      TopMobileFixedPair C D s r →
      TopMobilePendingBarrier D s r →
      TopMobilePendingBarrier
        (topMobileFixedWordRun ring C D word) s r := by
  induction word with
  | nil =>
      intro D _ hbar
      exact hbar
  | cons e rest ih =>
      intro D hfixed hbar
      change TopMobilePendingBarrier
        (topMobileFixedWordRun ring C
          (topFixedPublicNext ring C D e) rest) s r
      exact ih (topFixedPublicNext ring C D e)
        (topMobileFixedPairStep ring C D s r e hfixed)
        (topMobilePendingBarrierStep ring hn C D s r e hfixed hbar)

end L3
