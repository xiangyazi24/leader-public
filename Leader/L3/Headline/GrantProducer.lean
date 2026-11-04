import Leader.L3.Headline.Grant
import Leader.L3.Bank.CounterCold

/-!
Literal physical first-grant rows and integer spatial radius.
BANK and SMALL have distinct OLD success selectors. No substitute
transition or observer is used.
-/

namespace L3

set_option autoImplicit false
set_option Elab.async false

def grantClockSelectedSuccess (c : Compiled)
    (x y : Agent c) : Bool :=
  if c.useSmall then (smallPair x y c.K).2.2
  else bankSuccess
    (bankCell x x.pack.val) (bankCell y y.pack.val)
    (packNext x.pack.val y.pack.val c.b) c.b

def grantClockLiteralTokenPair (c : Compiled)
    (x y : Agent c) : TokPair × TokPair × TokMeta :=
  tokenStep x y
    (if fireAtSite
      (fireSelect x y
        (certLiteralEPair x.certNative y.certNative).1
        (certLiteralEPair x.certNative y.certNative).2)
        .siteX then firedNative
     else (certLiteralEPair x.certNative y.certNative).1)
    (if fireAtSite
      (fireSelect x y
        (certLiteralEPair x.certNative y.certNative).1
        (certLiteralEPair x.certNative y.certNative).2)
        .siteY then firedNative
     else (certLiteralEPair x.certNative y.certNative).2)
    (fireSelect x y
      (certLiteralEPair x.certNative y.certNative).1
      (certLiteralEPair x.certNative y.certNative).2)
    (dccStep x y (certificateStep c x y).2.2).request
    (grantClockSelectedSuccess c x y)

/-- The true full transition retains the base token output,
not an abstract success latch. -/
theorem grantClockTransitionTokenFrame (c : Compiled)
    (x y : Agent c) :
    (transition c x y).1.grant =
        (grantClockLiteralTokenPair c x y).1.grant ∧
    (transition c x y).2.grant =
        (grantClockLiteralTokenPair c x y).2.1.grant := by
  have hx :
      (transition c x y).1.grant =
        (baseStep c (certificateStep c x y).2.2 x y).1.grant := rfl
  have hy :
      (transition c x y).2.grant =
        (baseStep c (certificateStep c x y).2.2 x y).2.grant := rfl
  constructor
  · rw [hx]
    unfold grantClockLiteralTokenPair grantClockSelectedSuccess baseStep
    cases c.useSmall <;> rfl
  · rw [hy]
    unfold grantClockLiteralTokenPair grantClockSelectedSuccess baseStep
    cases c.useSmall <;> rfl

private theorem grantClockOldFireNone {c : Compiled}
    (x y : Agent c)
    (hx : x.grant = false) (hy : y.grant = false) :
    fireSelect x y
      (certLiteralEPair x.certNative y.certNative).1
      (certLiteralEPair x.certNative y.certNative).2 = none := by
  simp [fireSelect, hx, hy]

/-- The actual T0/T1/T2/HOLD/REQ/GRANT row from zero OLD
grants and a false selected producer bit. -/
theorem grantClockTokenNoProducer {c : Compiled}
    (x y : Agent c) (fx fy : CertNative) (req : Bool)
    (hx : x.grant = false) (hy : y.grant = false) :
    (tokenStep x y fx fy none req false).1.grant = false ∧
      (tokenStep x y fx fy none req false).2.1.grant = false := by
  cases hrx : x.req <;>
    cases hry : y.req <;>
    cases hlx : fx.l <;>
    cases hly : fy.l <;>
    cases hd : req <;>
    simp [tokenStep, hx, hy, hrx, hry, hlx, hly, hd,
      fireAtSite]

/-- A true OLD selected success mints a grant at X; there is
no OLD FIRE or sink of X because all OLD grants are zero and
the final source is a native follower. -/
theorem grantClockTokenSuccessMintsSource {c : Compiled}
    (x y : Agent c) (fx fy : CertNative) (req : Bool)
    (hx : x.grant = false) (hy : y.grant = false)
    (hfx : fx.l = false) :
    (tokenStep x y fx fy none req true).1.grant = true := by
  cases hrx : x.req <;>
    cases hry : y.req <;>
    cases hly : fy.l <;>
    cases hd : req <;>
    simp [tokenStep, hx, hy, hfx, hly, hrx, hry, hd,
      fireAtSite]

theorem grantClockTransitionWithoutSuccess
    (c : Compiled) (x y : Agent c)
    (hx : x.grant = false) (hy : y.grant = false)
    (hselected : grantClockSelectedSuccess c x y = false) :
    (transition c x y).1.grant = false ∧
      (transition c x y).2.grant = false := by
  have hfire := grantClockOldFireNone x y hx hy
  have hrow := grantClockTokenNoProducer x y
    (certLiteralEPair x.certNative y.certNative).1
    (certLiteralEPair x.certNative y.certNative).2
    (dccStep x y (certificateStep c x y).2.2).request hx hy
  have hp :
      grantClockLiteralTokenPair c x y =
      tokenStep x y
        (certLiteralEPair x.certNative y.certNative).1
        (certLiteralEPair x.certNative y.certNative).2
        none
        (dccStep x y (certificateStep c x y).2.2).request
        false := by
    simp [grantClockLiteralTokenPair, hfire, hselected,
      fireAtSite]
  rw [← hp] at hrow
  have hf := grantClockTransitionTokenFrame c x y
  exact ⟨hf.1.trans hrow.1, hf.2.trans hrow.2⟩

theorem grantClockTransitionSuccessMintsSource
    (c : Compiled) (x y : Agent c)
    (hx : x.grant = false) (hy : y.grant = false)
    (hfx : (certLiteralEPair x.certNative y.certNative).1.l = false)
    (hselected : grantClockSelectedSuccess c x y = true) :
    (transition c x y).1.grant = true := by
  have hfire := grantClockOldFireNone x y hx hy
  have hrow := grantClockTokenSuccessMintsSource x y
    (certLiteralEPair x.certNative y.certNative).1
    (certLiteralEPair x.certNative y.certNative).2
    (dccStep x y (certificateStep c x y).2.2).request
    hx hy hfx
  have hp :
      grantClockLiteralTokenPair c x y =
      tokenStep x y
        (certLiteralEPair x.certNative y.certNative).1
        (certLiteralEPair x.certNative y.certNative).2
        none
        (dccStep x y (certificateStep c x y).2.2).request
        true := by
    simp [grantClockLiteralTokenPair, hfire, hselected,
      fireAtSite]
  rw [← hp] at hrow
  exact (grantClockTransitionTokenFrame c x y).1.trans hrow

/-- Two-level if evaluation on a plain type (rewriting the if in a
HeadlineConfiguration term fails with "function expected"). -/
private theorem grantIteTwoNeg {α : Type} (P Q : Prop) [Decidable P]
    [Decidable Q] (a b c : α) (hp : ¬ P) (hq : ¬ Q) :
    (if P then a else if Q then b else c) = c := by
  rw [if_neg hp, if_neg hq]

private theorem grantIteTwoSecond {α : Type} (P Q : Prop) [Decidable P]
    [Decidable Q] (a b c : α) (hp : ¬ P) (hq : Q) :
    (if P then a else if Q then b else c) = b := by
  rw [if_neg hp, if_pos hq]

/-- Evaluate the literal protocol step at the source without
identifying HeadlineConfiguration with an arbitrary function. -/
private theorem grantClockStepSource {n : Nat}
    (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (e : Fin n) :
    headlinePhysicalNext ring C e e =
      (transition (compileAdvice (ceilLogTwo n))
        (C e) (C (ring.rightNeighbor e))).1 := by
  change
    (if e = e then
       (transition (compileAdvice (ceilLogTwo n))
         (C e) (C (ring.rightNeighbor e))).1
     else if e = ring.rightNeighbor e then
       (transition (compileAdvice (ceilLogTwo n))
         (C e) (C (ring.rightNeighbor e))).2
     else C e) =
       (transition (compileAdvice (ceilLogTwo n))
         (C e) (C (ring.rightNeighbor e))).1
  split
  · rfl
  · rename_i h
    exact False.elim (h rfl)

private theorem grantClockStepResponder {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (C : HeadlineConfiguration n) (e : Fin n) :
    headlinePhysicalNext ring C e (ring.rightNeighbor e) =
      (transition (compileAdvice (ceilLogTwo n))
        (C e) (C (ring.rightNeighbor e))).2 := by
  have hne : ring.rightNeighbor e ≠ e :=
    EWord.rightNeighborDifferent ring hn e
  change
    (if ring.rightNeighbor e = e then
       (transition (compileAdvice (ceilLogTwo n))
         (C e) (C (ring.rightNeighbor e))).1
     else if ring.rightNeighbor e = ring.rightNeighbor e then
       (transition (compileAdvice (ceilLogTwo n))
         (C e) (C (ring.rightNeighbor e))).2
     else C (ring.rightNeighbor e)) =
       (transition (compileAdvice (ceilLogTwo n))
         (C e) (C (ring.rightNeighbor e))).2
  exact grantIteTwoSecond _ _ _ _ _ hne rfl

private theorem grantClockStepAway {n : Nat}
    (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (e i : Fin n) (he : i ≠ e)
    (hj : i ≠ ring.rightNeighbor e) :
    headlinePhysicalNext ring C e i = C i := by
  change
    (if i = e then
       (transition (compileAdvice (ceilLogTwo n))
         (C e) (C (ring.rightNeighbor e))).1
     else if i = ring.rightNeighbor e then
       (transition (compileAdvice (ceilLogTwo n))
         (C e) (C (ring.rightNeighbor e))).2
     else C i) = C i
  exact grantIteTwoNeg _ _ _ _ _ he hj

/-- Branch-independent physical zero-grant lemma for the exact
success bit consumed by baseStep, with no rootless hypothesis. -/
theorem grantClockNoGrantWithoutSelectedSuccess {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (C : HeadlineConfiguration n) (e : Fin n)
    (hzero : ∀ i : Fin n, (C i).grant = false)
    (hselected : grantClockSelectedSuccess
      (compileAdvice (ceilLogTwo n))
      (C e) (C (ring.rightNeighbor e)) = false) :
    ∀ i : Fin n, (headlinePhysicalNext ring C e i).grant = false := by
  have hp := grantClockTransitionWithoutSuccess
    (compileAdvice (ceilLogTwo n))
    (C e) (C (ring.rightNeighbor e))
    (hzero e) (hzero (ring.rightNeighbor e)) hselected
  intro i
  by_cases he : i = e
  · subst i
    have hs := congrArg Agent.grant
      (grantClockStepSource ring C e)
    exact hs.trans hp.1
  · by_cases hj : i = ring.rightNeighbor e
    · subst i
      have hs := congrArg Agent.grant
        (grantClockStepResponder ring hn C e)
      exact hs.trans hp.2
    · have hs := congrArg Agent.grant
        (grantClockStepAway ring C e i he hj)
      exact hs.trans (hzero i)

/-- BANK mode requires useSmall=false: in SMALL mode the BANK
guard can fail while a true SMALL success mints a grant. -/
theorem grantClockNoGrantWithoutBankSuccess {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (C : HeadlineConfiguration n) (e : Fin n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hzero : ∀ i : Fin n, (C i).grant = false)
    (hno : ¬ Counter.resetColdPrivateSuccessAt ring e C e) :
    ∀ i : Fin n, (headlinePhysicalNext ring C e i).grant = false := by
  have hsuccess :
      bankSuccess
        (bankCell (C e) (C e).pack.val)
        (bankCell (C (ring.rightNeighbor e))
          (C (ring.rightNeighbor e)).pack.val)
        (packNext (C e).pack.val
          (C (ring.rightNeighbor e)).pack.val
          (compileAdvice (ceilLogTwo n)).b)
        (compileAdvice (ceilLogTwo n)).b = false := by
    cases hb : bankSuccess
        (bankCell (C e) (C e).pack.val)
        (bankCell (C (ring.rightNeighbor e))
          (C (ring.rightNeighbor e)).pack.val)
        (packNext (C e).pack.val
          (C (ring.rightNeighbor e)).pack.val
          (compileAdvice (ceilLogTwo n)).b)
        (compileAdvice (ceilLogTwo n)).b with
    | false => rfl
    | true =>
        exact False.elim (hno ⟨rfl, hb⟩)
  have hsel :
      grantClockSelectedSuccess
        (compileAdvice (ceilLogTwo n))
        (C e) (C (ring.rightNeighbor e)) = false := by
    simp [grantClockSelectedSuccess, hbank, hsuccess]
  exact grantClockNoGrantWithoutSelectedSuccess
    ring hn C e hzero hsel

/-- BANK success is an OLD private CWAIT/CL1 comparison.
On a rootless, grant-free edge it mints a physical grant at e. -/
theorem grantClockPrivateBankSuccessMintsPhysicalGrant {n : Nat}
    (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (e : Fin n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hrootless : ∀ i : Fin n, (C i).l = false)
    (hzero : ∀ i : Fin n, (C i).grant = false)
    (hsuccess : Counter.resetColdPrivateSuccessAt ring e C e) :
    (headlinePhysicalNext ring C e e).grant = true := by
  have hpost := headlineRendezvousLeaderlessPostE
    (C e).certNative (C (ring.rightNeighbor e)).certNative
    (by simpa only [Agent.certNative] using hrootless e)
    (by simpa only [Agent.certNative] using
      hrootless (ring.rightNeighbor e))
  have hselected :
      grantClockSelectedSuccess
        (compileAdvice (ceilLogTwo n))
        (C e) (C (ring.rightNeighbor e)) = true := by
    simp [grantClockSelectedSuccess, hbank, hsuccess.2]
  have hlocal := grantClockTransitionSuccessMintsSource
    (compileAdvice (ceilLogTwo n))
    (C e) (C (ring.rightNeighbor e))
    (hzero e) (hzero (ring.rightNeighbor e))
    hpost.1 hselected
  have hs := congrArg Agent.grant
    (grantClockStepSource ring C e)
  exact hs.trans hlocal

theorem grantClockNoGrantWithoutSmallSuccess {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (C : HeadlineConfiguration n) (e : Fin n)
    (hsmall : (compileAdvice (ceilLogTwo n)).useSmall = true)
    (hzero : ∀ i : Fin n, (C i).grant = false)
    (hno : (smallPair (C e) (C (ring.rightNeighbor e))
        (compileAdvice (ceilLogTwo n)).K).2.2 = false) :
    ∀ i : Fin n, (headlinePhysicalNext ring C e i).grant = false := by
  have hselected :
      grantClockSelectedSuccess
        (compileAdvice (ceilLogTwo n))
        (C e) (C (ring.rightNeighbor e)) = false := by
    simp [grantClockSelectedSuccess, hsmall, hno]
  exact grantClockNoGrantWithoutSelectedSuccess
    ring hn C e hzero hselected

theorem grantClockSmallSuccessMintsPhysicalGrant {n : Nat}
    (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (e : Fin n)
    (hsmall : (compileAdvice (ceilLogTwo n)).useSmall = true)
    (hrootless : ∀ i : Fin n, (C i).l = false)
    (hzero : ∀ i : Fin n, (C i).grant = false)
    (hsuccess : (smallPair (C e) (C (ring.rightNeighbor e))
        (compileAdvice (ceilLogTwo n)).K).2.2 = true) :
    (headlinePhysicalNext ring C e e).grant = true := by
  have hpost := headlineRendezvousLeaderlessPostE
    (C e).certNative (C (ring.rightNeighbor e)).certNative
    (by simpa only [Agent.certNative] using hrootless e)
    (by simpa only [Agent.certNative] using
      hrootless (ring.rightNeighbor e))
  have hselected :
      grantClockSelectedSuccess
        (compileAdvice (ceilLogTwo n))
        (C e) (C (ring.rightNeighbor e)) = true := by
    simp [grantClockSelectedSuccess, hsmall, hsuccess]
  have hlocal := grantClockTransitionSuccessMintsSource
    (compileAdvice (ceilLogTwo n))
    (C e) (C (ring.rightNeighbor e))
    (hzero e) (hzero (ring.rightNeighbor e))
    hpost.1 hselected
  have hs := congrArg Agent.grant
    (grantClockStepSource ring C e)
  exact hs.trans hlocal

private theorem grantClockRadiusSquareStrict (R : Nat) :
    (256 * (R + 1)) ^ 2 < (256 * (R + 2)) ^ 2 := by
  have ha : 0 < 256 * (R + 1) := by omega
  have hab : 256 * (R + 1) < 256 * (R + 2) := by omega
  have hm := Nat.mul_lt_mul_of_pos_right hab ha
  have hle := Nat.mul_le_mul_left (256 * (R + 2))
    (Nat.le_of_lt hab)
  have hsq :
      (256 * (R + 1)) * (256 * (R + 1)) <
        (256 * (R + 2)) * (256 * (R + 2)) :=
    Nat.lt_of_lt_of_le hm hle
  simpa only [Nat.pow_two] using hsq

/-- Integer radius floor(sqrt(n)/256) by induction on n;
the proof uses only exact Nat inequalities. -/
theorem grantClockIntegerRadius (n : Nat) :
    ∃ R : Nat,
      (256 * R) ^ 2 ≤ n ∧ n < (256 * (R + 1)) ^ 2 := by
  induction n with
  | zero =>
      exact ⟨0, by decide, by decide⟩
  | succ n ih =>
      obtain ⟨R, hlow, hhigh⟩ := ih
      by_cases hsame : n + 1 < (256 * (R + 1)) ^ 2
      · exact ⟨R, Nat.le_trans hlow (Nat.le_succ n), hsame⟩
      · have heq : n + 1 = (256 * (R + 1)) ^ 2 := by omega
        refine ⟨R + 1, ?_, ?_⟩
        · omega
        · rw [heq]
          simpa only [show R + 1 + 1 = R + 2 by omega] using
            grantClockRadiusSquareStrict R

/-- The already Counter cutoff is the exact
q>=80 lower population threshold, not an approximation. -/
theorem grantClockSpatialPopulationLower (n : Nat)
    (hn : 5 ≤ n)
    (hsp : (compileAdvice (ceilLogTwo n)).useSmall = false) :
    2 ^ 79 + 1 ≤ n := by
  have h := Counter.resetColdPrivateHeadlineSpatialLower n hn hsp
  omega

/-- A square-population bound forces any integer radius
enclosing n to exceed the specified target radius. -/
theorem grantClockRadiusAtLeastOfSquareLower
    (n R target : Nat)
    (hradius :
      (256 * R) ^ 2 ≤ n ∧ n < (256 * (R + 1)) ^ 2)
    (hlower : (256 * target) ^ 2 ≤ n) :
    target ≤ R := by
  by_cases hle : target ≤ R
  · exact hle
  · have hnext : R + 1 ≤ target := by omega
    have hmul : 256 * (R + 1) ≤ 256 * target :=
      Nat.mul_le_mul_left 256 hnext
    have hsquare :
        (256 * (R + 1)) ^ 2 ≤ (256 * target) ^ 2 :=
      Nat.pow_le_pow_left hmul 2
    have hbad := Nat.le_trans hsquare hlower
    exact False.elim (by omega : False)

/-- C.12 exact arithmetic consumer, conditional on the
compiled square-population lower estimate. -/
theorem grantClockRadiusPaperCutoffOfSquareLower
    (n R c0 alphaTransit K : Nat)
    (hradius :
      (256 * R) ^ 2 ≤ n ∧ n < (256 * (R + 1)) ^ 2)
    (hcompiledSquare :
      (256 * (1024 * (c0 + alphaTransit * (K + 2)))) ^ 2 ≤ n) :
    1024 * (c0 + alphaTransit * (K + 2)) ≤ R := by
  exact grantClockRadiusAtLeastOfSquareLower n R
    (1024 * (c0 + alphaTransit * (K + 2)))
    hradius hcompiledSquare

end L3

/-!
Integer-only spatial cutoffs from the production compiler.
Paper C.12--C.18; all inequalities are Nat-valued.
-/

namespace L3

set_option autoImplicit false
set_option Elab.async false

/-- A spatial compiled advice is at least the first BANK advice 80. -/
theorem grantClockSpatialAdviceEighty (q : Nat)
    (hsp : (compileAdvice q).useSmall = false) : 80 ≤ q := by
  by_cases hq : q ≤ 79
  · have ht : (compileAdvice q).useSmall = true := by
      simp [Compiled.useSmall, compileAdvice, qStar, hq]
    rw [ht] at hsp
    cases hsp
  · omega

/-- The padded width is at least seven at the first spatial advice;
the coarse upper width bound suffices for the numeric cutoff. -/
theorem grantClockSpatialWidthBounds (q : Nat)
    (hq : 80 ≤ q) :
    7 ≤ (compileAdvice q).s ∧
      (compileAdvice q).s ≤ q ∧
      (compileAdvice q).b ≤ q + 11 := by
  have hs := ceilLogTwo_spec q (by omega)
  have hseven : 7 ≤ ceilLogTwo q := by
    by_cases hh : 7 ≤ ceilLogTwo q
    · exact hh
    · have hp : 2 ^ ceilLogTwo q ≤ 2 ^ 6 :=
        Nat.pow_le_pow_right (by omega) (by omega)
      have h64 : (2 : Nat) ^ 6 = 64 := by decide
      omega
  have hself := ceilLogTwo_le_self q
  have hmax : max 2 (ceilLogTwo q) = ceilLogTwo q := by omega
  have hwidth : (compileAdvice q).s = ceilLogTwo q := by
    rw [compileAdvice_s, hmax]
  have hb : (compileAdvice q).b =
      (compileAdvice q).s + 11 := rfl
  omega

/-- Exponential growth beats the crude linear ceiling for kappa.
This uses no real logarithm or library asymptotics. -/
private theorem grantClockPowerBeatsLinear (q : Nat)
    (hq : 80 ≤ q) : 557 * q + 119982 ≤ 2 ^ q := by
  obtain ⟨k, rfl⟩ : ∃ k, q = k + 80 := ⟨q - 80, by omega⟩
  clear hq
  induction k with
  | zero => exact Nat.le_of_ble_eq_true rfl
  | succ k ih =>
      rw [show k + 1 + 80 = (k + 80) + 1 by omega, Nat.pow_succ,
        Nat.mul_succ]
      generalize 2 ^ (k + 80) = P at ih ⊢
      generalize 557 * (k + 80) = X at ih ⊢
      omega

/-- Elementary reverse bound for ceilLogTwo: m <= 2^q implies
ceilLogTwo m <= q, provided m >= 2. -/
private theorem grantClockCeilLogLeOfPow
    (m q : Nat) (hm : 2 ≤ m)
    (hp : m ≤ 2 ^ q) : ceilLogTwo m ≤ q := by
  by_cases hh : ceilLogTwo m ≤ q
  · exact hh
  · have he : q ≤ ceilLogTwo m - 1 := by omega
    have hpow := Nat.pow_le_pow_right (by omega : 0 < 2) he
    have hs := (ceilLogTwo_spec m hm).1
    omega

/-- The actual compiled threshold is <= its advice q on the
spatial band; this is sufficient for K <= 3q. -/
theorem grantClockSpatialKappaLeAdvice (q : Nat)
    (hq : 80 ≤ q) :
    (compileAdvice q).kappa ≤ q := by
  have hs := grantClockSpatialWidthBounds q hq
  have hq32 : ¬ q ≤ 32 := by omega
  have hnotTwo : (compileAdvice q).s ≠ 2 := by omega
  have hnotThree : (compileAdvice q).s ≠ 3 := by omega
  have hnotFour : (compileAdvice q).s ≠ 4 := by omega
  have hnotFive : (compileAdvice q).s ≠ 5 := by omega
  have hnotSix : (compileAdvice q).s ≠ 6 := by omega
  have hnotSmall : ¬ (compileAdvice q).s ≤ 5 := by omega
  have hlarge :
      (compileAdvice q).kappa =
        kappaDot (compileAdvice q).s := by
    change productionKappa q = kappaDot (paddedS (sourceTOfQ q))
    unfold productionKappa
    rw [if_neg hq32]
  have hdot :
      kappaDot (compileAdvice q).s =
        ceilLogTwo (557 * (compileAdvice q).s + 119982) := by
    simp only [kappaDot, if_neg hnotTwo,
      if_neg hnotThree, if_neg hnotFour,
      if_neg hnotFive, if_neg hnotSmall, if_neg hnotSix,
      Nat.add_assoc, Nat.reduceAdd]
  rw [hlarge, hdot]
  have hm : 557 * (compileAdvice q).s + 119982 ≤
      557 * q + 119982 := by omega
  have hp := Nat.le_trans hm (grantClockPowerBeatsLinear q hq)
  exact grantClockCeilLogLeOfPow
    (557 * (compileAdvice q).s + 119982) q
    (by omega) hp

/-- Production K=2q+kappa is <=3q on the spatial band. -/
theorem grantClockSpatialKLeTriple (q : Nat) (hq : 80 ≤ q) :
    (compileAdvice q).K ≤ 3 * q := by
  have hk := grantClockSpatialKappaLeAdvice q hq
  change 2 * q + (compileAdvice q).kappa ≤ 3 * q
  omega

/-- Fourth powers grow by less than a factor of two after x>=8.
The rational-looking 8/9 comparison is purely integer arithmetic. -/
private theorem grantClockFourthPowerGrowth (x : Nat)
    (hx : 8 ≤ x) : (x + 1) ^ 4 ≤ 2 * x ^ 4 := by
  have hratio : 8 * (x + 1) ≤ 9 * x := by omega
  have hp := Nat.pow_le_pow_left hratio 4
  rw [Nat.mul_pow, Nat.mul_pow] at hp
  have h8 : (8 : Nat) ^ 4 = 4096 := by decide
  have h9 : (9 : Nat) ^ 4 = 6561 := by decide
  rw [h8, h9] at hp
  omega

/-- Exact power-four reserve for all q>=80.
The q=80 base is a closed integer comparison. -/
private theorem grantClockPowerBeatsFourth (q : Nat)
    (hq : 80 ≤ q) :
    2 ^ 50 * (q + 1) ^ 4 ≤ 2 ^ (q - 1) := by
  have haux :
      ∀ k : Nat, 2 ^ 50 * (k + 81) ^ 4 ≤ 2 ^ (k + 79) := by
    intro k
    induction k with
    | zero => decide
    | succ k ih =>
        have hg := grantClockFourthPowerGrowth (k + 81) (by omega)
        have hm := Nat.mul_le_mul_left (2 ^ 50) hg
        have hi := Nat.mul_le_mul_left 2 ih
        have hpower : 2 ^ (k + 1 + 79) =
            2 * 2 ^ (k + 79) := by
          have he : k + 1 + 79 = (k + 79) + 1 := by omega
          rw [he, Nat.pow_succ]
          omega
        have hshift : k + 1 + 81 = (k + 81) + 1 := by omega
        rw [hshift]
        calc
          2 ^ 50 * ((k + 81) + 1) ^ 4 ≤
              2 ^ 50 * (2 * (k + 81) ^ 4) := hm
          _ = 2 * (2 ^ 50 * (k + 81) ^ 4) := by ac_rfl
          _ ≤ 2 * 2 ^ (k + 79) := hi
          _ = 2 ^ (k + 1 + 79) := hpower.symm
  have hh := haux (q - 80)
  have hleft : q - 80 + 81 = q + 1 := by omega
  have hright : q - 80 + 79 = q - 1 := by omega
  rw [hleft, hright] at hh
  exact hh

/-- Exact algebraic identity for the square radius upper envelope.
The coefficient 2^50 is (256*1024*128)^2. -/
private theorem grantClockQuadraticSquareIdentity (q : Nat) :
    (256 * (1024 * (128 * (q + 1) ^ 2))) ^ 2 =
      2 ^ 50 * (q + 1) ^ 4 := by
  have hc : 256 * 1024 * 128 = 2 ^ 25 := by decide
  have hpow : ((q + 1) ^ 2) ^ 2 = (q + 1) ^ 4 := by
    rw [← Nat.pow_mul]
  have htwo : (2 ^ 25) ^ 2 = 2 ^ 50 := by
    rw [← Nat.pow_mul]
  calc
    (256 * (1024 * (128 * (q + 1) ^ 2))) ^ 2 =
        (256 * 1024 * 128) ^ 2 * ((q + 1) ^ 2) ^ 2 := by
          simp only [Nat.mul_pow]
          ac_rfl
    _ = 2 ^ 50 * (q + 1) ^ 4 := by rw [hc, hpow, htwo]

/-- The stronger paper alpha_0+alpha_tr(K+2) is below the
quadratic 128(q+1)^2 envelope. In particular it also bounds
the requested c_0+alpha_tr(K+2). -/
theorem grantClockSpatialPaperBudgetQuadratic (q : Nat)
    (hq : 80 ≤ q) :
    224 * ((compileAdvice q).b + 2) +
        32 * ((compileAdvice q).b + 1) *
          ((compileAdvice q).K + 2) ≤
      128 * (q + 1) ^ 2 := by
  have hwidth := (grantClockSpatialWidthBounds q hq).2.2
  have hK := grantClockSpatialKLeTriple q hq
  have hratio :
      5 * ((compileAdvice q).b + 1) ≤ 6 * q := by omega
  have hkratio :
      10 * ((compileAdvice q).K + 2) ≤ 31 * q := by omega
  have hboth :
      50 * (((compileAdvice q).b + 1) *
          ((compileAdvice q).K + 2)) ≤ 186 * (q * q) := by
    calc
      50 * (((compileAdvice q).b + 1) *
          ((compileAdvice q).K + 2)) =
        (5 * ((compileAdvice q).b + 1)) *
          (10 * ((compileAdvice q).K + 2)) := by
            change (5 * 10) *
              (((compileAdvice q).b + 1) *
                ((compileAdvice q).K + 2)) =
              (5 * ((compileAdvice q).b + 1)) *
                (10 * ((compileAdvice q).K + 2))
            ac_rfl
      _ ≤ (6 * q) * (31 * q) :=
        Nat.mul_le_mul hratio hkratio
      _ = 186 * (q * q) := by
        change (6 * q) * (31 * q) = (6 * 31) * (q * q)
        ac_rfl
  have hscale : 1600 * (((compileAdvice q).b + 1) *
          ((compileAdvice q).K + 2)) ≤
      5952 * (q * q) := by
    have hm := Nat.mul_le_mul_left 32 hboth
    have hcLeft : (32 : Nat) * 50 = 1600 := by decide
    have hcRight : (32 : Nat) * 186 = 5952 := by decide
    calc
      1600 * (((compileAdvice q).b + 1) *
          ((compileAdvice q).K + 2)) =
          (32 * 50) * (((compileAdvice q).b + 1) *
            ((compileAdvice q).K + 2)) := by rw [hcLeft]
      _ = 32 * (50 * (((compileAdvice q).b + 1) *
            ((compileAdvice q).K + 2))) := by ac_rfl
      _ ≤ 32 * (186 * (q * q)) := hm
      _ = (32 * 186) * (q * q) := by ac_rfl
      _ = 5952 * (q * q) := by rw [hcRight]
  have hterm :
      32 * (((compileAdvice q).b + 1) *
          ((compileAdvice q).K + 2)) ≤
      120 * (q * q) := by omega
  have hq2 : 80 * q ≤ q * q :=
    Nat.mul_le_mul_right q hq
  have hAlpha :
      224 * ((compileAdvice q).b + 2) ≤
        8 * (q * q) := by omega
  have hbound :
      224 * ((compileAdvice q).b + 2) +
        32 * ((compileAdvice q).b + 1) *
          ((compileAdvice q).K + 2) ≤
      128 * (q * q) := by
    calc
      _ = 224 * ((compileAdvice q).b + 2) +
          32 * (((compileAdvice q).b + 1) *
            ((compileAdvice q).K + 2)) := by ac_rfl
      _ ≤ 8 * (q * q) + 120 * (q * q) :=
        Nat.add_le_add hAlpha hterm
      _ = 128 * (q * q) := by omega
  have hp : q * q ≤ (q + 1) ^ 2 := by
    simpa only [Nat.pow_two] using
      (Nat.pow_le_pow_left (by omega : q ≤ q + 1) 2)
  exact Nat.le_trans hbound (Nat.mul_le_mul_left 128 hp)

/-- C.12: the square lower bound for the stronger alpha_0 budget. -/
theorem grantClockSpatialPaperBudgetSquareLower (n : Nat)
    (hn : 5 ≤ n)
    (hsp : (compileAdvice (ceilLogTwo n)).useSmall = false) :
    (256 * (1024 *
      (224 * ((compileAdvice (ceilLogTwo n)).b + 2) +
        32 * ((compileAdvice (ceilLogTwo n)).b + 1) *
          ((compileAdvice (ceilLogTwo n)).K + 2)))) ^ 2 ≤ n := by
  have hq := grantClockSpatialAdviceEighty (ceilLogTwo n) hsp
  have hbound := grantClockSpatialPaperBudgetQuadratic
    (ceilLogTwo n) hq
  have hm := Nat.mul_le_mul_left (256 * 1024) hbound
  have hscale :
      256 * (1024 *
        (224 * ((compileAdvice (ceilLogTwo n)).b + 2) +
          32 * ((compileAdvice (ceilLogTwo n)).b + 1) *
            ((compileAdvice (ceilLogTwo n)).K + 2))) ≤
      256 * (1024 * (128 * (ceilLogTwo n + 1) ^ 2)) := by
    simpa only [Nat.mul_assoc] using hm
  have hsquare := Nat.pow_le_pow_left hscale 2
  have hpower := grantClockPowerBeatsFourth (ceilLogTwo n) hq
  have hspec := (ceilLogTwo_spec n (by omega)).1
  calc
    _ ≤ (256 * (1024 *
          (128 * (ceilLogTwo n + 1) ^ 2))) ^ 2 := hsquare
    _ = 2 ^ 50 * (ceilLogTwo n + 1) ^ 4 :=
      grantClockQuadraticSquareIdentity (ceilLogTwo n)
    _ ≤ 2 ^ (ceilLogTwo n - 1) := hpower
    _ ≤ n := Nat.le_of_lt hspec

/-- The paper's c_0=2 Lambda+5b+13 is dominated by alpha_0.
This establishes the exact premise consumed by the existing
grantClockRadiusPaperCutoffOfSquareLower. -/
theorem grantClockSpatialCompiledSquareLower (n : Nat)
    (hn : 5 ≤ n)
    (hsp : (compileAdvice (ceilLogTwo n)).useSmall = false) :
    (256 * (1024 *
      ((2 * (compileAdvice (ceilLogTwo n)).bankLeaseCap +
          5 * (compileAdvice (ceilLogTwo n)).b + 13) +
        32 * ((compileAdvice (ceilLogTwo n)).b + 1) *
          ((compileAdvice (ceilLogTwo n)).K + 2)))) ^ 2 ≤ n := by
  have hcb :
      2 * (compileAdvice (ceilLogTwo n)).bankLeaseCap +
          5 * (compileAdvice (ceilLogTwo n)).b + 13 ≤
        224 * ((compileAdvice (ceilLogTwo n)).b + 2) := by
    change 2 * (13 * ((compileAdvice (ceilLogTwo n)).b + 2)) +
        5 * (compileAdvice (ceilLogTwo n)).b + 13 ≤
        224 * ((compileAdvice (ceilLogTwo n)).b + 2)
    omega
  have hsum := Nat.add_le_add_right hcb
    (32 * ((compileAdvice (ceilLogTwo n)).b + 1) *
      ((compileAdvice (ceilLogTwo n)).K + 2))
  have hscale := Nat.mul_le_mul_left (256 * 1024) hsum
  have hscaled :
      256 * (1024 *
      ((2 * (compileAdvice (ceilLogTwo n)).bankLeaseCap +
          5 * (compileAdvice (ceilLogTwo n)).b + 13) +
        32 * ((compileAdvice (ceilLogTwo n)).b + 1) *
          ((compileAdvice (ceilLogTwo n)).K + 2))) ≤
      256 * (1024 *
      (224 * ((compileAdvice (ceilLogTwo n)).b + 2) +
        32 * ((compileAdvice (ceilLogTwo n)).b + 1) *
          ((compileAdvice (ceilLogTwo n)).K + 2))) := by
    simpa only [Nat.mul_assoc] using hscale
  have hp := Nat.pow_le_pow_left hscaled 2
  exact Nat.le_trans hp (grantClockSpatialPaperBudgetSquareLower n hn hsp)

/-- Unconditional C.12 cutoff on the exact integer radius enclosure. -/
theorem grantClockSpatialRadiusCutoff (n R : Nat)
    (hn : 5 ≤ n)
    (hsp : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hradius : (256 * R) ^ 2 ≤ n ∧
      n < (256 * (R + 1)) ^ 2) :
    1024 *
      ((2 * (compileAdvice (ceilLogTwo n)).bankLeaseCap +
          5 * (compileAdvice (ceilLogTwo n)).b + 13) +
        32 * ((compileAdvice (ceilLogTwo n)).b + 1) *
          ((compileAdvice (ceilLogTwo n)).K + 2)) ≤ R := by
  exact grantClockRadiusPaperCutoffOfSquareLower
    n R
    (2 * (compileAdvice (ceilLogTwo n)).bankLeaseCap +
      5 * (compileAdvice (ceilLogTwo n)).b + 13)
    (32 * ((compileAdvice (ceilLogTwo n)).b + 1))
    (compileAdvice (ceilLogTwo n)).K
    hradius (grantClockSpatialCompiledSquareLower n hn hsp)

/-- Stronger paper alpha_0 version of C.12. -/
theorem grantClockSpatialPaperRadiusCutoff (n R : Nat)
    (hn : 5 ≤ n)
    (hsp : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hradius : (256 * R) ^ 2 ≤ n ∧
      n < (256 * (R + 1)) ^ 2) :
    1024 *
      (224 * ((compileAdvice (ceilLogTwo n)).b + 2) +
        32 * ((compileAdvice (ceilLogTwo n)).b + 1) *
          ((compileAdvice (ceilLogTwo n)).K + 2)) ≤ R := by
  exact grantClockRadiusAtLeastOfSquareLower n R
    (1024 *
      (224 * ((compileAdvice (ceilLogTwo n)).b + 2) +
        32 * ((compileAdvice (ceilLogTwo n)).b + 1) *
          ((compileAdvice (ceilLogTwo n)).K + 2)))
    hradius (grantClockSpatialPaperBudgetSquareLower n hn hsp)


/-- The spatial compiler has kappa >=17, hence K>=177.
At q=80 these bounds are equalities. -/
theorem grantClockSpatialKappaLower (q : Nat)
    (hq : 80 ≤ q) :
    17 ≤ (compileAdvice q).kappa ∧
      177 ≤ (compileAdvice q).K := by
  have hs := grantClockSpatialWidthBounds q hq
  have hq32 : ¬ q ≤ 32 := by omega
  have hnotTwo : (compileAdvice q).s ≠ 2 := by omega
  have hnotThree : (compileAdvice q).s ≠ 3 := by omega
  have hnotFour : (compileAdvice q).s ≠ 4 := by omega
  have hnotFive : (compileAdvice q).s ≠ 5 := by omega
  have hnotSix : (compileAdvice q).s ≠ 6 := by omega
  have hnotSmall : ¬ (compileAdvice q).s ≤ 5 := by omega
  have hlarge :
      (compileAdvice q).kappa =
        kappaDot (compileAdvice q).s := by
    change productionKappa q = kappaDot (paddedS (sourceTOfQ q))
    unfold productionKappa
    rw [if_neg hq32]
  have hdot :
      kappaDot (compileAdvice q).s =
        ceilLogTwo (557 * (compileAdvice q).s + 119982) := by
    simp only [kappaDot, if_neg hnotTwo,
      if_neg hnotThree, if_neg hnotFour,
      if_neg hnotFive, if_neg hnotSmall, if_neg hnotSix,
      Nat.add_assoc, Nat.reduceAdd]
  have hm :
      2 ^ 16 < 557 * (compileAdvice q).s + 119982 := by
    have h16 : (2 : Nat) ^ 16 = 65536 := by decide
    omega
  have hspec := (ceilLogTwo_spec
    (557 * (compileAdvice q).s + 119982) (by omega)).2
  have hk :
      17 ≤ ceilLogTwo (557 * (compileAdvice q).s + 119982) := by
    by_cases hh :
        17 ≤ ceilLogTwo (557 * (compileAdvice q).s + 119982)
    · exact hh
    · have hp : 2 ^
          ceilLogTwo (557 * (compileAdvice q).s + 119982) ≤
          2 ^ 16 := Nat.pow_le_pow_right (by omega) (by omega)
      omega
  have hkappa : 17 ≤ (compileAdvice q).kappa := by
    rw [hlarge, hdot]
    exact hk
  have hK : (compileAdvice q).K =
      2 * q + (compileAdvice q).kappa := rfl
  constructor
  · exact hkappa
  · omega

/-- C.13's first cutoff is C.12 written as
alpha_tr(K+2)=alpha_tr(K+1)+alpha_tr. -/
theorem grantClockSpatialCThirteenRadius (n R : Nat)
    (hn : 5 ≤ n)
    (hsp : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hradius : (256 * R) ^ 2 ≤ n ∧
      n < (256 * (R + 1)) ^ 2) :
    1024 *
      ((2 * (compileAdvice (ceilLogTwo n)).bankLeaseCap +
          5 * (compileAdvice (ceilLogTwo n)).b + 13) +
        32 * ((compileAdvice (ceilLogTwo n)).b + 1) *
          ((compileAdvice (ceilLogTwo n)).K + 1) +
        32 * ((compileAdvice (ceilLogTwo n)).b + 1)) ≤ R := by
  have hh := grantClockSpatialRadiusCutoff n R hn hsp hradius
  have he :
      32 * ((compileAdvice (ceilLogTwo n)).b + 1) *
        ((compileAdvice (ceilLogTwo n)).K + 2) =
      32 * ((compileAdvice (ceilLogTwo n)).b + 1) *
        ((compileAdvice (ceilLogTwo n)).K + 1) +
      32 * ((compileAdvice (ceilLogTwo n)).b + 1) := by
    have hk : (compileAdvice (ceilLogTwo n)).K + 2 =
        ((compileAdvice (ceilLogTwo n)).K + 1) + 1 := by omega
    rw [hk, Nat.mul_add, Nat.mul_one]
  rw [he] at hh
  simpa only [Nat.add_assoc] using hh

/-- C.13's elementary floor reserve: Rn >=2048. -/
theorem grantClockSpatialRadiusPopulationProduct
    (n R : Nat) (hn : 5 ≤ n)
    (hsp : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hradius : (256 * R) ^ 2 ≤ n ∧
      n < (256 * (R + 1)) ^ 2) :
    2048 ≤ R * n := by
  have hp := grantClockSpatialPaperRadiusCutoff n R hn hsp hradius
  have hR : 2048 ≤ R := by omega
  have hmul := Nat.mul_le_mul_left R (by omega : 1 ≤ n)
  omega

/-- The exact paper C.14 coefficient f is no larger than
the comparator trial-transit coefficient alpha_tr, for b>=18. -/
theorem grantClockSpatialTransitDominatesFailure
    (b : Nat) (hb : 18 ≤ b) :
    8 * b + 13 ≤ 32 * (b + 1) := by omega

/-- The paper C.18 ratio f/alpha_tr <=157/608
is exact at the first spatial digit width b=18. -/
theorem grantClockSpatialTransitRatio
    (b : Nat) (hb : 18 ≤ b) :
    608 * (8 * b + 13) ≤ 157 * (32 * (b + 1)) := by omega

/-- C.14's purely integer failure-conditional coefficient:
(8b+12)/(1-2^-K) < (8b+13), cross multiplied.
No probabilistic independence is asserted here. -/
theorem grantClockSpatialC14Coefficient
    (q : Nat) (hq : 80 ≤ q) :
    (8 * (compileAdvice q).b + 12) * 2 ^ (compileAdvice q).K <
      (8 * (compileAdvice q).b + 13) *
        (2 ^ (compileAdvice q).K - 1) := by
  have hb := (grantClockSpatialWidthBounds q hq).2.2
  have hK : q ≤ (compileAdvice q).K := by
    change q ≤ 2 * q + (compileAdvice q).kappa
    omega
  have hpow := Nat.pow_le_pow_right (by omega : 0 < 2) hK
  have hlin := grantClockPowerBeatsLinear q hq
  have hbig : 8 * (compileAdvice q).b + 13 <
      2 ^ (compileAdvice q).K := by omega
  have hs : (2 ^ (compileAdvice q).K - 1) + 1 =
      2 ^ (compileAdvice q).K := by omega
  have hdecomp :
      (8 * (compileAdvice q).b + 13) *
        (2 ^ (compileAdvice q).K - 1) +
        (8 * (compileAdvice q).b + 13) =
      (8 * (compileAdvice q).b + 13) *
        2 ^ (compileAdvice q).K := by
    calc
      _ = (8 * (compileAdvice q).b + 13) *
          ((2 ^ (compileAdvice q).K - 1) + 1) := by
            simp only [Nat.mul_add, Nat.mul_one]
      _ = (8 * (compileAdvice q).b + 13) *
          2 ^ (compileAdvice q).K := by rw [hs]
  have hstep :
      (8 * (compileAdvice q).b + 13) *
        2 ^ (compileAdvice q).K =
      (8 * (compileAdvice q).b + 12) *
        2 ^ (compileAdvice q).K +
        2 ^ (compileAdvice q).K := by
    have hf : 8 * (compileAdvice q).b + 13 =
        (8 * (compileAdvice q).b + 12) + 1 := by omega
    rw [hf, Nat.add_mul, Nat.one_mul]
  omega

/-- The compiled spatial budget yields C0 <=R/1024 and
R >=1024*f*(K+1). Here c0=2 Lambda+5b+13,
g=(8b+12)(K+1), C0=c0+g and f=8b+13. -/
theorem grantClockSpatialColdAndTrialBudget
    (b K R : Nat)
    (hR : 1024 *
      ((2 * (13 * (b + 2)) + 5 * b + 13) +
        32 * (b + 1) * (K + 2)) ≤ R) :
    1024 *
      ((2 * (13 * (b + 2)) + 5 * b + 13) +
        (8 * b + 12) * (K + 1)) ≤ R ∧
    1024 * ((8 * b + 13) * (K + 1)) ≤ R := by
  have hle : 8 * b + 13 ≤ 32 * (b + 1) := by omega
  have hless : 8 * b + 12 ≤ 32 * (b + 1) := by omega
  have hK : K + 1 ≤ K + 2 := by omega
  have hleft := Nat.mul_le_mul_right (K + 1) hless
  have hright := Nat.mul_le_mul_right (K + 1) hle
  have hnext := Nat.mul_le_mul_left (32 * (b + 1)) hK
  have hg := Nat.le_trans hleft hnext
  have hf := Nat.le_trans hright hnext
  constructor
  · have hsum := Nat.add_le_add_left hg
      (2 * (13 * (b + 2)) + 5 * b + 13)
    have hh := Nat.mul_le_mul_left 1024 hsum
    exact Nat.le_trans hh hR
  · have hsum : (8 * b + 13) * (K + 1) ≤
        (2 * (13 * (b + 2)) + 5 * b + 13) +
          32 * (b + 1) * (K + 2) := by omega
    exact Nat.le_trans (Nat.mul_le_mul_left 1024 hsum) hR

/-- Floor(Rn/8) is at least 255Rn/2048 once Rn>=2048.
No approximation of a real-valued time window is used. -/
theorem grantClockSpatialFloorWindow
    (n R W : Nat) (hW : W = R * n / 8)
    (hlarge : 2048 ≤ R * n) :
    255 * (R * n) ≤ 2048 * W := by
  have hmod := Nat.mod_lt (R * n) (by decide : 0 < 8)
  have hsplit := Nat.mod_add_div (R * n) 8
  rw [hW]
  omega

/-- From C0<=R/1024 and W>=255Rn/2048,
the normalized cold overhead obeys C0/t <= 2/255,
where t=W/n. This is its exact cross-multiplied version. -/
theorem grantClockSpatialColdWindowRatio
    (n R W C0 : Nat)
    (hC0 : 1024 * C0 ≤ R)
    (hW : 255 * (R * n) ≤ 2048 * W) :
    255 * (C0 * n) ≤ 2 * W := by
  have hmul := Nat.mul_le_mul_right n hC0
  rw [Nat.mul_assoc] at hmul
  omega

/-- C.16's 22517 threshold in the exact integer form
W >= n(C0 + 22517 f), with t=W/n and f=8b+13.
There is no rounding error from floor(Rn/8). -/
theorem grantClockSpatialLStarQuota
    (n R W b K : Nat)
    (hK : 177 ≤ K)
    (hR : 1024 *
      ((2 * (13 * (b + 2)) + 5 * b + 13) +
        32 * (b + 1) * (K + 2)) ≤ R)
    (hW : W = R * n / 8)
    (hprod : 2048 ≤ R * n) :
    n * ((2 * (13 * (b + 2)) + 5 * b + 13) +
      (8 * b + 12) * (K + 1) + 22517 * (8 * b + 13)) ≤ W := by
  have hbudget := grantClockSpatialColdAndTrialBudget b K R hR
  have hwindow := grantClockSpatialFloorWindow n R W hW hprod
  have hKplus : 178 ≤ K + 1 := by omega
  have hRlower : 182272 * (8 * b + 13) ≤ R := by
    calc
      182272 * (8 * b + 13) =
          (1024 * (8 * b + 13)) * 178 := by
            change (1024 * 178) * (8 * b + 13) = _
            ac_rfl
      _ ≤ (1024 * (8 * b + 13)) * (K + 1) :=
        Nat.mul_le_mul_left _ hKplus
      _ = 1024 * ((8 * b + 13) * (K + 1)) := by ac_rfl
      _ ≤ R := hbudget.2
  have hRn : 182272 * ((8 * b + 13) * n) ≤ R * n := by
    have hh := Nat.mul_le_mul_right n hRlower
    simpa only [Nat.mul_assoc] using hh
  have hC0 :
      2048 * (((2 * (13 * (b + 2)) + 5 * b + 13) +
        (8 * b + 12) * (K + 1)) * n) ≤
      2 * (R * n) := by
    have hh := Nat.mul_le_mul_right (2 * n) hbudget.1
    have hc : (1024 : Nat) * 2 = 2048 := by decide
    calc
      2048 * (((2 * (13 * (b + 2)) + 5 * b + 13) +
        (8 * b + 12) * (K + 1)) * n) =
        (1024 * ((2 * (13 * (b + 2)) + 5 * b + 13) +
          (8 * b + 12) * (K + 1))) * (2 * n) := by
            rw [← hc]
            ac_rfl
      _ ≤ R * (2 * n) := hh
      _ = 2 * (R * n) := by ac_rfl
  have hL :
      2048 * (22517 * ((8 * b + 13) * n)) ≤
        253 * (R * n) := by
    have hh := Nat.mul_le_mul_left 253 hRn
    have hc : 2048 * 22517 = 253 * 182272 := by decide
    calc
      2048 * (22517 * ((8 * b + 13) * n)) =
          (2048 * 22517) * ((8 * b + 13) * n) := by ac_rfl
      _ = (253 * 182272) * ((8 * b + 13) * n) := by rw [hc]
      _ = 253 * (182272 * ((8 * b + 13) * n)) := by ac_rfl
      _ ≤ 253 * (R * n) := hh
  have hsum :
      ((2 * (13 * (b + 2)) + 5 * b + 13) +
        (8 * b + 12) * (K + 1)) * n +
        22517 * ((8 * b + 13) * n) ≤ W := by omega
  have he :
      n * ((2 * (13 * (b + 2)) + 5 * b + 13) +
        (8 * b + 12) * (K + 1) +
        22517 * (8 * b + 13)) =
      ((2 * (13 * (b + 2)) + 5 * b + 13) +
        (8 * b + 12) * (K + 1)) * n +
        22517 * ((8 * b + 13) * n) := by
    rw [Nat.mul_add]
    ac_rfl
  rw [he]
  exact hsum

/-- C.16 final strict integer certificate,
100*253^2*22516 - 98*255^2*22517 = 634207750. -/
theorem grantClockSpatialC16Coefficient :
    98 * 255 ^ 2 * 22517 + 634207750 =
      100 * 253 ^ 2 * 22516 := by decide

/-- C.18 exact integer certificate for eta/epsilon_F <1/1024.
This is the positive difference in the paper, not a real inequality. -/
theorem grantClockSpatialC18Coefficient :
    157 * 100 * 1000 * 8192 * 1024 ^ 4 +
      4028965858833024396820480 =
    608 * 2 ^ 20 * 1023 ^ 3 * 49 * 489 * 255 := by decide

/-- The final C.18 strict coefficient comparison, in the form
needed after cross multiplication by positive denominators. -/
theorem grantClockSpatialC18Strict :
    157 * 100 * 1000 * 8192 * 1024 ^ 4 <
      608 * 2 ^ 20 * 1023 ^ 3 * 49 * 489 * 255 := by
  have hh := grantClockSpatialC18Coefficient
  omega

/-- Unconditional compiled W and C.16 threshold from the
actual integer radius, spatial branch and compiled parameters. -/
theorem grantClockSpatialCompiledWindowQuotas
    (n R W : Nat)
    (hn : 5 ≤ n)
    (hsp : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hradius : (256 * R) ^ 2 ≤ n ∧
      n < (256 * (R + 1)) ^ 2)
    (hW : W = R * n / 8) :
    255 * (R * n) ≤ 2048 * W ∧
    n * ((2 * (compileAdvice (ceilLogTwo n)).bankLeaseCap +
        5 * (compileAdvice (ceilLogTwo n)).b + 13) +
      (8 * (compileAdvice (ceilLogTwo n)).b + 12) *
        ((compileAdvice (ceilLogTwo n)).K + 1) +
      22517 * (8 * (compileAdvice (ceilLogTwo n)).b + 13)) ≤ W := by
  have hproduct := grantClockSpatialRadiusPopulationProduct
    n R hn hsp hradius
  have hfloor := grantClockSpatialFloorWindow n R W hW hproduct
  have hq := grantClockSpatialAdviceEighty (ceilLogTwo n) hsp
  have hK := (grantClockSpatialKappaLower (ceilLogTwo n) hq).2
  have hR := grantClockSpatialRadiusCutoff n R hn hsp hradius
  have hquota := grantClockSpatialLStarQuota n R W
    (compileAdvice (ceilLogTwo n)).b
    (compileAdvice (ceilLogTwo n)).K hK
    (by simpa only [Compiled.bankLeaseCap] using hR)
    hW hproduct
  exact ⟨hfloor, hquota⟩

end L3
