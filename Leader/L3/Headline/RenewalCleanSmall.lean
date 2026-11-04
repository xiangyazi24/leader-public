import Lean
import Leader.L3.Headline.RenewalCleanBank
import Leader.L3.Small.FinishCleanDrain
import Leader.L3.Small.ReaderClean
import Leader.L3.Width.WordCleanClock

/-!
R14 on the clean target, SMALL branch, and the two-branch assembly.

Part A.  The SMALL clean finish from the reader fold and the digit half
only: the W clock (`smallWordCleanWordClockOfSmall`) and the E.G19
retirement clock (`smallCleanResidentRetirementClockProved`) are now
proved, and the debt / request halves are `SmallFinishCleanDrain`.

Part B.  The SMALL reference of `smallRootedReferenceData` with the same
physical next, masked coupling, seen memory, spawn and win, and
`referenceStop := smallCleanStop` (= Gclean of the configuration).  The
renewal shell is the `At` layer of `HeadlineRenewalCleanBank` at
G := `headlineCleanTarget`.  Domination, origin charge and retry coverage
are re-proved on it by the installed arguments of `HeadlineRenewal.lean`
(lines 795-945) and `SmallRenewal.lean` (lines 536-955, 1972-1999); the
source witness `smallRunSourceWitness` never reads its open-prefix
hypothesis, so its body is reused verbatim.  Rarity never reads the stop.
The clock is `smallReferenceClockOfStageData` with the installed
sigma_seen / sigma_G / sigma_1 / candidate-preparation stages and the
clean finish of Part A.  The margins are
`smallReferenceNumericalCertificate`, which does not mention the stop.

Old SMALL R14 premises beyond the finish: none.  The old SMALL clock
(`smallReferenceClockOfCandidateFinish`) has the finish as its only
premise; coverage (`smallReferenceRetryCoverage`), charge, domination,
rarity and margins are unconditional.

Part C.  The combined clean R14 by cases on `useSmall`.

Two private declarations of `SmallRenewal.lean` (the reference iterate
`smallRefAfter`, which the public `SmallSeenRunTrace` is stated with, and
`smallPairSuccessShape`) are reached through their mangled names, the
technique of `PPL/Lemma4Generic/PrimeBridge.lean`.
-/

namespace L3.HeadlineRenewalCleanSmall

open L3
open L3.HeadlineRenewal
open L3.HeadlineRenewalCleanBank
open L3.RenewalReferenceClock
open L3.GrantDrainEntrance
open L3.SmallRenewal
open L3.SmallCandidatePreparation
open L3.SmallFinishClean
open Classical
open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree
open PPL.Convergence.LDLocal (AttemptNode RetryKernel retryCount)

set_option autoImplicit false
set_option Elab.async false

/-! ## Part A: the SMALL clean finish from the fold and the digit half -/

/-- The SMALL clean generated finish from the prepared cut, with the W
clock and the retirement clock discharged.  Open premises: the reader
fold soundness and the digit half-stage.
Consumer: `smallCleanReferenceClock`. -/
theorem smallCleanFinishReferenceOfFoldDigit {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hsmall : (compileAdvice (ceilLogTwo n)).useSmall = true)
    (hfold : SmallCleanReaderFoldSound ring)
    (hdigit : SmallCleanDigitHalf ring) :
    StageReferenceGeneratedFinish
      (renewalSmallNext ring)
      (SmallPreparedAtSomeRoot ring)
      (smallCleanStop ring)
      (headlineReferenceFinishRate (ceilLogTwo n)) := by
  have hword : SmallCleanWordClock ring :=
    L3.RenewalReferenceClock.smallWordCleanWordClockOfSmall ring hn hsmall
  exact L3.SmallFinishCleanDrain.smallCleanFinishReferenceOfReader
    ring hn hsmall hword
    (L3.SmallReaderClean.smallCleanResidentRetirementClockProved ring hn hsmall)
    hfold hdigit

/-! ## Part B: the SMALL reference stopped at Gclean -/

open Lean Elab Term Meta in
/-- `smallren% "name"` elaborates to the private declaration `name` of
`SmallRenewal.lean` (namespace `L3.SmallRenewal`). -/
elab "smallren% " s:str : term => do
  let nm : Name :=
    ((((`_private.Leader.L3.Small.Renewal).num 0).str "L3").str
      "SmallRenewal").str s.getString
  mkConstWithFreshMVarLevels nm

/-- The installed reference iterate of `SmallRenewal.lean`.
Consumer: `SmallRunSourceWitnessClean` and the clean coverage. -/
def smallReferenceAfter {n : Nat} (ring : DirectedRing n) :
    RenewalSmallReference n → List (Fin n) → RenewalSmallReference n :=
  (smallren% "smallRefAfter") ring

theorem smallReferenceAfterNil {n : Nat} (ring : DirectedRing n)
    (r : RenewalSmallReference n) :
    smallReferenceAfter ring r [] = r := rfl

theorem smallReferenceAfterCons {n : Nat} (ring : DirectedRing n)
    (r : RenewalSmallReference n) (e : Fin n) (w : List (Fin n)) :
    smallReferenceAfter ring r (e :: w) =
      smallReferenceAfter ring (renewalSmallNext ring r e) w := rfl

/-- The valid SMALL reference of `smallRootedReferenceData` with its
stop replaced by `Gclean`.  Consumer: `smallCleanRealization`. -/
def smallCleanRootedReferenceData {n : Nat}
    (ring : DirectedRing n)
    (hsmall : (compileAdvice (ceilLogTwo n)).useSmall = true) :
    RootedReferenceData ring :=
  { smallRootedReferenceData ring hsmall with
    referenceStop := smallCleanStop ring }

private theorem renewalWordCostConsSmall {S : Type} {n : Nat}
    (next : S → Fin n → S) (P : S → Prop) (x : S)
    (e : Fin n) (word : List (Fin n)) (hx : ¬ P x) :
    costWord next P x (e :: word) =
      1 + costWord next P (next x e) word := by
  classical
  simp only [costWord, K2FiniteSafeEliminationExpected.rawCost, if_neg hx]

/-- F.1's pathwise charging statement for the SMALL observer stopped at
Gclean.  Consumer: `smallReferenceOriginChargeClean`. -/
theorem renewalSmallOriginsBudgetClean {n : Nat} (ring : DirectedRing n) :
    ∀ (word : List (Fin n)) (r : RenewalSmallReference n),
      Prob.originsWord (renewalSmallNext ring) (smallCleanStop ring)
        (renewalSmallSpawn ring) r word ≤
      costWord (renewalSmallNext ring) (smallCleanStop ring) r word +
        renewalSmallRemaining r.2 := by
  classical
  intro word
  induction word with
  | nil =>
      intro r
      change 0 ≤ 0 + renewalSmallRemaining r.2
      omega
  | cons e word ih =>
      intro r
      by_cases hs : smallCleanStop ring r
      · rw [Prob.originsWord, if_pos hs]
        exact Nat.zero_le _
      · have ht := ih (renewalSmallNext ring r e)
        have hp := renewalSmallRemainingStep ring r.1 r.2 e
        have hp' :
            renewalSmallRemaining (renewalSmallNext ring r e).2 +
              Prob.indicator (renewalSmallExtra r.1 r.2 e) ≤
            renewalSmallRemaining r.2 := hp
        rw [Prob.originsWord, if_neg hs, renewalSmallSpawnLength,
          renewalWordCostConsSmall (renewalSmallNext ring)
            (smallCleanStop ring) r e word hs]
        omega

/-- The clean SMALL origin charge.  Consumer: `smallCleanRealization`. -/
theorem smallReferenceOriginChargeClean {n : Nat} (ring : DirectedRing n)
    (hsmall : (compileAdvice (ceilLogTwo n)).useSmall = true) :
    ReferenceOriginChargeAt ring (headlineCleanTarget ring)
      (smallCleanRootedReferenceData ring hsmall) := by
  intro seed _ word
  have h := renewalSmallOriginsBudgetClean ring word
    (renewalSmallStart ring seed)
  have hz : renewalSmallRemaining (renewalSmallStart ring seed).2 = n :=
    renewalSmallRemainingInitial n
  rw [hz] at h
  exact h

/-- The SMALL attempt is dominated wordwise by the reference stopped at
Gclean.  Consumer: `smallReferenceAttemptDominationClean`. -/
theorem renewalSmallAttemptWordClean {n : Nat} (ring : DirectedRing n)
    (hn : 5 ≤ n) :
    ∀ (word : List (Fin n))
      (a : RootedSeed ring × RenewalSmallMemory n),
      ¬ headlineCleanTarget ring a.1.val →
      costWord
        (Prob.attemptStepper (rootedTrialKernelAt ring
          (headlineCleanTarget ring) hn
          (renewalSmallInitialMemory ring) (renewalSmallTrialAdvance ring)
          (renewalSmallTrialCut ring)))
        (fun z => Prob.attemptGood z ∨ Prob.attemptFail z)
        (.active a) word ≤
      costWord (renewalSmallNext ring) (smallCleanStop ring)
        (a.1.val, a.2) word := by
  classical
  intro word
  induction word with
  | nil =>
      intro a _
      exact Nat.le_refl 0
  | cons e word ih =>
      intro a hnot
      have hactive : ¬
          (Prob.attemptGood (.active a :
            AttemptNode (RootedSeed ring × RenewalSmallMemory n)
              (RootedSeed ring)) ∨
           Prob.attemptFail (.active a :
            AttemptNode (RootedSeed ring × RenewalSmallMemory n)
              (RootedSeed ring))) := by
        intro h
        rcases h with h | h
        · exact h
        · exact h
      have hrefnot : ¬ smallCleanStop ring (a.1.val, a.2) := hnot
      rw [renewalWordCostConsSmall _ _
          (AttemptNode.active a :
            AttemptNode (RootedSeed ring × RenewalSmallMemory n)
              (RootedSeed ring)) e word hactive,
        renewalWordCostConsSmall _ _ (a.1.val, a.2) e word hrefnot]
      change 1 + costWord _ _
          ((rootedTrialKernelAt ring (headlineCleanTarget ring) hn
            (renewalSmallInitialMemory ring)
            (renewalSmallTrialAdvance ring)
            (renewalSmallTrialCut ring)).step a e) word ≤
        1 + costWord (renewalSmallNext ring) (smallCleanStop ring)
          (renewalSmallNext ring (a.1.val, a.2) e) word
      cases hs : (rootedTrialKernelAt ring (headlineCleanTarget ring) hn
          (renewalSmallInitialMemory ring) (renewalSmallTrialAdvance ring)
          (renewalSmallTrialCut ring)).step a e with
      | success =>
          rw [costWord_terminal _ _
            (AttemptNode.success :
              AttemptNode (RootedSeed ring × RenewalSmallMemory n)
                (RootedSeed ring))
            (by exact Or.inl True.intro) word]
          exact Nat.add_le_add_left (Nat.zero_le _) 1
      | retry seed =>
          rw [costWord_terminal _ _
            (AttemptNode.retry seed :
              AttemptNode (RootedSeed ring × RenewalSmallMemory n)
                (RootedSeed ring))
            (by exact Or.inr True.intro) word]
          exact Nat.add_le_add_left (Nat.zero_le _) 1
      | active b =>
          have hs' : rootedTrialStepAt ring (headlineCleanTarget ring) hn
              (renewalSmallTrialAdvance ring) (renewalSmallTrialCut ring)
              a e = .active b := hs
          unfold rootedTrialStepAt at hs'
          split at hs'
          · cases hs'
          · rename_i hnext
            split at hs'
            · cases hs'
            · rename_i hnocut
              cases hs'
              have hcut : renewalSmallTrialCut ring a e = false := by
                cases hc : renewalSmallTrialCut ring a e with
                | false => rfl
                | true => exact False.elim (hnocut hc)
              have href : renewalSmallNext ring (a.1.val, a.2) e =
                  ((rootedSuccessor ring hn a.1 e).val,
                    renewalSmallTrialAdvance ring a e) := by
                apply Prod.ext
                · exact renewalSmallPhysicalBeforeCut ring
                    (a.1.val, a.2) e hcut
                · rfl
              have ht := ih
                (rootedSuccessor ring hn a.1 e,
                  renewalSmallTrialAdvance ring a e) hnext
              rw [← href] at ht
              exact Nat.add_le_add_left ht 1

/-- The clean SMALL attempt domination.
Consumer: `smallCleanRealization`. -/
theorem smallReferenceAttemptDominationClean {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hsmall : (compileAdvice (ceilLogTwo n)).useSmall = true) :
    ReferenceAttemptDominationAt ring (headlineCleanTarget ring) hn
      (smallCleanRootedReferenceData ring hsmall) := by
  intro seed hnot word
  exact renewalSmallAttemptWordClean ring hn word
    (seed, renewalSmallInitialMemory ring seed) hnot

/-- The clean SMALL origin rarity (the stop is only a guard of the
quantifier; the suffix bound does not read it).
Consumer: `smallCleanRealization`. -/
theorem smallReferenceOriginRarityClean {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hsmall : (compileAdvice (ceilLogTwo n)).useSmall = true) :
    ReferenceOriginRarity ring
      (smallCleanRootedReferenceData ring hsmall)
      (compileAdvice (ceilLogTwo n)).kappa := by
  intro r _ e root _ T
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

/-! ### Retry coverage on the clean reference -/

/-- Gclean was not visited at any cut through the prefix, including the
cut at its end.  Consumer: `SmallRunSourceWitnessClean`. -/
def smallRefOpenClean {n : Nat} (ring : DirectedRing n) :
    RenewalSmallReference n → List (Fin n) → Prop
  | r, [] => ¬ smallCleanStop ring r
  | r, e :: w =>
      ¬ smallCleanStop ring r ∧
        smallRefOpenClean ring (renewalSmallNext ring r e) w

private theorem smallRefOpenPrefixClean {n : Nat}
    (ring : DirectedRing n) :
    ∀ (u v : List (Fin n)) (r : RenewalSmallReference n),
      smallRefOpenClean ring r (u ++ v) →
        smallRefOpenClean ring r u := by
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

/-- The installed SMALL source-history statement with the open prefix
taken against Gclean.  Consumer: `smallReferenceRetryCoverageClean`. -/
def SmallRunSourceWitnessClean {n : Nat} (ring : DirectedRing n) : Prop :=
  ∀ (seed : RootedSeed ring) (u : List (Fin n)) (e : Fin n),
    smallRefOpenClean ring (renewalSmallStart ring seed) u →
    (smallReferenceAfter ring (renewalSmallStart ring seed) u).2 e = true →
    (smallPair
      ((smallReferenceAfter ring (renewalSmallStart ring seed) u).1 e)
      ((smallReferenceAfter ring (renewalSmallStart ring seed) u).1
        (ring.rightNeighbor e))
      (compileAdvice (ceilLogTwo n)).K).2.2 = true →
    ∃ (p : List (Fin n)) (f : Fin n) (tail : List (Fin n)),
      u = p ++ f :: tail ∧
      (e = ring.rightNeighbor f ∨
        (e = f ∧
          renewalSmallExtra
            (smallReferenceAfter ring (renewalSmallStart ring seed) p).1
            (smallReferenceAfter ring (renewalSmallStart ring seed) p).2
            f = true)) ∧
      renewalSmallWin ring e
        (compileAdvice (ceilLogTwo n)).K
        (tail ++ [e]) = true

/-- The source witness on the clean reference: the body of
`smallRunSourceWitness`, which does not read the open prefix.
Consumer: `smallReferenceRetryCoverageClean`. -/
theorem smallRunSourceWitnessClean {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hsmall : (compileAdvice (ceilLogTwo n)).useSmall = true) :
    SmallRunSourceWitnessClean ring := by
  intro seed u e _ hseen hsuccess
  obtain ⟨j, hrun, hthreshold⟩ := (smallren% "smallPairSuccessShape")
    (compileAdvice (ceilLogTwo n))
    ((smallReferenceAfter ring (renewalSmallStart ring seed) u).1 e)
    ((smallReferenceAfter ring (renewalSmallStart ring seed) u).1
      (ring.rightNeighbor e)) hsuccess
  obtain ⟨p, f, tail, hword, hbirth, hno, hcount⟩ :=
    (smallSeenRunTraceAll ring hn hsmall seed u)
      e j hseen hrun
  refine ⟨p, f, tail, hword, hbirth, ?_⟩
  exact smallTraceWinOnSuccessEdge ring e tail j
    (compileAdvice (ceilLogTwo n)).K hno hcount hthreshold

private theorem smallWinAppendTrueClean {n : Nat}
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

private theorem smallOriginListPositiveClean {A : Type}
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

private theorem smallSuccessfulOriginClean {n : Nat}
    (ring : DirectedRing n) (root : Fin n) :
    ∀ (u : List (Fin n)) (r : RenewalSmallReference n)
      (e : Fin n) (v : List (Fin n)),
      smallRefOpenClean ring r u →
      root ∈ renewalSmallSpawn ring (smallReferenceAfter ring r u) e →
      renewalSmallWin ring root
        (compileAdvice (ceilLogTwo n)).K v = true →
      0 < Prob.successfulOriginsWord
        (renewalSmallNext ring) (smallCleanStop ring)
        (renewalSmallSpawn ring)
        (fun o w => renewalSmallWin ring o
          (compileAdvice (ceilLogTwo n)).K w)
        r (u ++ e :: v) := by
  intro u
  induction u with
  | nil =>
      intro r e v hopen hmem hwin
      have hh := smallOriginListPositiveClean
        (renewalSmallSpawn ring r e)
        (fun o => renewalSmallWin ring o
          (compileAdvice (ceilLogTwo n)).K v)
        root hmem hwin
      change 0 < (if smallCleanStop ring r then 0
        else ((renewalSmallSpawn ring r e).map
          (fun o => Prob.indicator (renewalSmallWin ring o
            (compileAdvice (ceilLogTwo n)).K v))).sum +
          Prob.successfulOriginsWord
            (renewalSmallNext ring) (smallCleanStop ring)
            (renewalSmallSpawn ring)
            (fun o w => renewalSmallWin ring o
              (compileAdvice (ceilLogTwo n)).K w)
            (renewalSmallNext ring r e) v)
      rw [if_neg hopen]
      omega
  | cons f fs ih =>
      intro r e v hopen hmem hwin
      have hstop : ¬ smallCleanStop ring r := hopen.1
      have htail :
          smallRefOpenClean ring (renewalSmallNext ring r f) fs :=
        hopen.2
      have hh := ih (renewalSmallNext ring r f) e v
        htail hmem hwin
      change 0 < (if smallCleanStop ring r then 0
        else ((renewalSmallSpawn ring r f).map
          (fun o => Prob.indicator (renewalSmallWin ring o
            (compileAdvice (ceilLogTwo n)).K (fs ++ e :: v)))).sum +
          Prob.successfulOriginsWord
            (renewalSmallNext ring) (smallCleanStop ring)
            (renewalSmallSpawn ring)
            (fun o w => renewalSmallWin ring o
              (compileAdvice (ceilLogTwo n)).K w)
            (renewalSmallNext ring r f) (fs ++ e :: v))
      rw [if_neg hstop]
      omega

/-- The clean SMALL retry kernel.
Consumer: `smallReferenceRetryCoverageClean`. -/
noncomputable def smallRetryKernelClean {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hsmall : (compileAdvice (ceilLogTwo n)).useSmall = true) :
    RetryKernel (RootedSeed ring × RenewalSmallMemory n)
      (RootedSeed ring) n :=
  referenceKernelAt ring (headlineCleanTarget ring) hn
    (smallCleanRootedReferenceData ring hsmall)

private theorem smallRetryFirstLeOneClean {A Seed : Type} {n : Nat}
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

private theorem smallRetryFirstHasCutClean {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hsmall : (compileAdvice (ceilLogTwo n)).useSmall = true) :
    ∀ (word : List (Fin n))
      (a : RootedSeed ring × RenewalSmallMemory n)
      (r : RenewalSmallReference n),
      r = (a.1.val, a.2) →
      ¬ smallCleanStop ring r →
      Prob.retryFirstWord (smallRetryKernelClean ring hn hsmall)
        (.active a) word = 1 →
      ∃ (u : List (Fin n)) (e : Fin n) (v : List (Fin n)),
        word = u ++ e :: v ∧
        smallRefOpenClean ring r u ∧
        renewalSmallCut ring (smallReferenceAfter ring r u).1
          (smallReferenceAfter ring r u).2 e = true := by
  intro word
  induction word with
  | nil =>
      intro a r hre hnot hretry
      change (0 : Nat) = 1 at hretry
      cases hretry
  | cons e es ih =>
      intro a r hre hnot hretry
      change Prob.retryFirstWord
        (smallRetryKernelClean ring hn hsmall)
        ((smallRetryKernelClean ring hn hsmall).step a e) es = 1 at hretry
      cases hs : (smallRetryKernelClean ring hn hsmall).step a e with
      | success =>
          rw [hs] at hretry
          simp [Prob.retryFirstWord] at hretry
      | retry seed =>
          have hs' : rootedTrialStepAt ring (headlineCleanTarget ring) hn
              (renewalSmallTrialAdvance ring)
              (renewalSmallTrialCut ring) a e = .retry seed := hs
          unfold rootedTrialStepAt at hs'
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
          have hs' : rootedTrialStepAt ring (headlineCleanTarget ring) hn
              (renewalSmallTrialAdvance ring)
              (renewalSmallTrialCut ring) a e = .active b := hs
          unfold rootedTrialStepAt at hs'
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
                  ¬ smallCleanStop ring
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

/-- Clean SMALL retry-first wordwise origin coverage, from the source
witness.  Consumer: `smallReferenceRetryCoverageClean`. -/
theorem smallReferenceRetryCoverageOfSourceWitnessClean {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hsmall : (compileAdvice (ceilLogTwo n)).useSmall = true)
    (hsource : SmallRunSourceWitnessClean ring) :
    ReferenceRetryCoverageAt ring (headlineCleanTarget ring) hn
      (smallCleanRootedReferenceData ring hsmall) := by
  intro seed hnot word
  change Prob.retryFirstWord (smallRetryKernelClean ring hn hsmall)
      (.active (seed, renewalSmallInitialMemory ring seed)) word ≤
    Prob.originEventWord (renewalSmallNext ring) (smallCleanStop ring)
      (renewalSmallSpawn ring)
      (fun o w => renewalSmallWin ring o
        (compileAdvice (ceilLogTwo n)).K w)
      (renewalSmallStart ring seed) word
  by_cases hz :
      Prob.retryFirstWord (smallRetryKernelClean ring hn hsmall)
        (.active (seed, renewalSmallInitialMemory ring seed)) word = 0
  · rw [hz]
    exact Nat.zero_le _
  · have hle :
        Prob.retryFirstWord (smallRetryKernelClean ring hn hsmall)
          (.active (seed, renewalSmallInitialMemory ring seed)) word ≤ 1 :=
      smallRetryFirstLeOneClean (smallRetryKernelClean ring hn hsmall)
        word _
    have hretry :
        Prob.retryFirstWord (smallRetryKernelClean ring hn hsmall)
          (.active (seed, renewalSmallInitialMemory ring seed)) word = 1 := by
      omega
    have hstart :
        ¬ smallCleanStop ring (renewalSmallStart ring seed) := hnot
    obtain ⟨u, e, v, hword, hopen, hcut⟩ :=
      smallRetryFirstHasCutClean ring hn hsmall word
        (seed, renewalSmallInitialMemory ring seed)
        (renewalSmallStart ring seed) rfl hstart hretry
    have hdet := smallOldCutDetector ring
      (smallReferenceAfter ring (renewalSmallStart ring seed) u) e hcut
    obtain ⟨p, f, tail, hp, hbirth, hwin⟩ :=
      hsource seed u e hopen hdet.1 hdet.2
    have hpopen :
        smallRefOpenClean ring (renewalSmallStart ring seed) p := by
      have hfull :
          smallRefOpenClean ring (renewalSmallStart ring seed)
            (p ++ f :: tail) := by
        rw [← hp]
        exact hopen
      exact smallRefOpenPrefixClean ring p (f :: tail)
        (renewalSmallStart ring seed) hfull
    have hmem :
        e ∈ renewalSmallSpawn ring
          (smallReferenceAfter ring (renewalSmallStart ring seed) p) f := by
      rcases hbirth with hres | hsrc
      · rw [hres]
        exact smallResponderOriginMem ring
          (smallReferenceAfter ring (renewalSmallStart ring seed) p) f
      · obtain ⟨he, hextra⟩ := hsrc
        rw [he]
        exact smallExtraOriginMem ring
          (smallReferenceAfter ring (renewalSmallStart ring seed) p)
          f hextra
    have hwinLong :
        renewalSmallWin ring e (compileAdvice (ceilLogTwo n)).K
          (tail ++ e :: v) = true := by
      have hh := smallWinAppendTrueClean ring e
        (tail ++ [e]) v (compileAdvice (ceilLogTwo n)).K hwin
      simpa only [List.append_assoc, List.singleton_append] using hh
    have hpos := smallSuccessfulOriginClean ring e p
      (renewalSmallStart ring seed) f (tail ++ e :: v)
      hpopen hmem hwinLong
    have hlist :
        u ++ e :: v = p ++ f :: (tail ++ e :: v) := by
      rw [hp]
      simp only [List.append_assoc, List.cons_append]
    have hpositive :
        0 < Prob.successfulOriginsWord
          (renewalSmallNext ring) (smallCleanStop ring)
          (renewalSmallSpawn ring)
          (fun o w => renewalSmallWin ring o
            (compileAdvice (ceilLogTwo n)).K w)
          (renewalSmallStart ring seed) word := by
      rw [hword, hlist]
      exact hpos
    have hevent :
        Prob.originEventWord (renewalSmallNext ring)
          (smallCleanStop ring) (renewalSmallSpawn ring)
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

/-- Unconditional clean SMALL retry coverage.
Consumer: `smallCleanRealization`. -/
theorem smallReferenceRetryCoverageClean {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hsmall : (compileAdvice (ceilLogTwo n)).useSmall = true) :
    ReferenceRetryCoverageAt ring (headlineCleanTarget ring) hn
      (smallCleanRootedReferenceData ring hsmall) :=
  smallReferenceRetryCoverageOfSourceWitnessClean ring hn hsmall
    (smallRunSourceWitnessClean ring hn hsmall)

/-! ### The clean SMALL clock -/

private theorem smallInvariantConjunctionCostClean
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

/-- The clean SMALL reference clock at the selected rate: the installed
seen clock, grant drain, singleton and candidate preparation stages, and
the clean finish.  Open premises: fold soundness and the digit half.
Consumer: `smallCleanStageRootedRenewalCost`. -/
theorem smallCleanReferenceClock {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hsmall : (compileAdvice (ceilLogTwo n)).useSmall = true)
    (hfold : SmallCleanReaderFoldSound ring)
    (hdigit : SmallCleanDigitHalf ring) :
    ReferenceClockAt ring (headlineCleanTarget ring)
      (smallCleanRootedReferenceData ring hsmall)
      (headlineReferenceRate (ceilLogTwo n)) := by
  have hrootclosed := smallReferenceRootedClosed ring hn
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
    have heq := smallInvariantConjunctionCostClean
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
    (smallReferenceGrantFreeRootedSeen ring)
    (smallReferenceNativeRooted ring)
    (SmallPreparedAtSomeRoot ring) (smallCleanStop ring)
    (ceilLogTwo n) hthree (by omega : 0 < n)
    hOld (smallReferenceGrantDrainStage ring hn hsmall)
    (smallReferenceSingletonStageRooted ring hn hsmall)
    (smallPreparedAtSomeRootStage ring hn hsmall)
    (smallCleanFinishReferenceOfFoldDigit ring hn hsmall hfold hdigit)
  intro seed _ T
  change costNumerator (renewalSmallNext ring) (smallCleanStop ring)
      (renewalSmallStart ring seed) T ≤
    n ^ T * (headlineReferenceRate (ceilLogTwo n) * n ^ 2)
  exact (UniformFirstHit.expectedHittingTimeAtMost_iff_cost
    (renewalSmallNext ring) (smallCleanStop ring)
    (by omega : 0 < n) (renewalSmallStart ring seed)
    (headlineReferenceRate (ceilLogTwo n) * n ^ 2)).1
    (hstages (renewalSmallStart ring seed) seed.property) T

/-! ### Realization and the SMALL clean R14 -/

/-- The clean SMALL realization: every field proved here except the
two finish premises of the clock.  Consumer:
`smallCleanStageRootedRenewalCost`. -/
theorem smallCleanRealization {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hsmall : (compileAdvice (ceilLogTwo n)).useSmall = true)
    (hfold : SmallCleanReaderFoldSound ring)
    (hdigit : SmallCleanDigitHalf ring) :
    RootedReferenceRealizationAt ring (headlineCleanTarget ring) hn := by
  have hmargins := smallReferenceNumericalCertificate n hn hsmall
  refine ⟨smallCleanRootedReferenceData ring hsmall,
    headlineReferenceRate (ceilLogTwo n), ?_, hmargins.1, hmargins.2⟩
  exact {
    domination := smallReferenceAttemptDominationClean ring hn hsmall
    coverage := smallReferenceRetryCoverageClean ring hn hsmall
    charge := smallReferenceOriginChargeClean ring hsmall
    rarity := smallReferenceOriginRarityClean ring hn hsmall
    clock := smallCleanReferenceClock ring hn hsmall hfold hdigit }

/-- The SMALL case of the clean R14.  Open premises: the reader fold
soundness and the SMALL digit half-stage; nothing else.
Consumer: `stageCleanRootedRenewalCostOfBranches` and the clean headline
(`HeadlineClean`, SMALL branch). -/
theorem smallCleanStageRootedRenewalCost {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hsmall : (compileAdvice (ceilLogTwo n)).useSmall = true)
    (hfold : SmallCleanReaderFoldSound ring)
    (hdigit : SmallCleanDigitHalf ring) :
    StageCleanRootedRenewalCost ring := by
  obtain ⟨D, A, hcertificate, hmargin, hreserve⟩ :=
    smallCleanRealization ring hn hsmall hfold hdigit
  intro C hC T
  exact rootedCostFromReferenceAt ring (headlineCleanTarget ring) hn D A
    (compileAdvice (ceilLogTwo n)).kappa (headlineRenewalRate n)
    hcertificate hmargin hreserve C hC T

/-! ## Part C: both branches -/

/-- The clean R14 on every ring with 5 ≤ n, by cases on the
compiled branch.  BANK premises (as functions of the branch proof): the
digit half on the drain (R10c), the K-head threshold of the old R11, and
R7 (a rooted class containing every non-Gclean start, with sigma_B).
SMALL premises: the reader fold soundness and the SMALL digit half.
Consumer: the clean headline assembly (`HeadlineClean`). -/
theorem stageCleanRootedRenewalCostOfBranches {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbankDigit : ∀ hbank : (compileAdvice (ceilLogTwo n)).useSmall = false,
      BankCleanDigitHalfOnDrain ring hbank)
    (hbankThreshold :
      ∀ hbank : (compileAdvice (ceilLogTwo n)).useSmall = false,
        L3.BankRetryCoverage.BankCutGenuineHeadThreshold ring hbank)
    (hbankOld : ∀ hbank : (compileAdvice (ceilLogTwo n)).useSmall = false,
      ∃ rooted : (bankCleanRootedReferenceData ring hbank).Reference → Prop,
        (∀ seed : RootedSeed ring,
          ¬ headlineCleanTarget ring seed.val →
            rooted ((bankCleanRootedReferenceData ring hbank).referenceStart
              seed)) ∧
        StageInheritedAuthorityExtinction
          (bankCleanRootedReferenceData ring hbank).referenceNext
          rooted
          (fun z => headlineRooted ring z.val.1 ∧
            InheritedAuthorityExtinct ring hbank z)
          (ceilLogTwo n))
    (hsmallFold : (compileAdvice (ceilLogTwo n)).useSmall = true →
      SmallCleanReaderFoldSound ring)
    (hsmallDigit : (compileAdvice (ceilLogTwo n)).useSmall = true →
      SmallCleanDigitHalf ring) :
    StageCleanRootedRenewalCost ring := by
  cases hb : (compileAdvice (ceilLogTwo n)).useSmall with
  | true =>
      exact smallCleanStageRootedRenewalCost ring hn hb
        (hsmallFold hb) (hsmallDigit hb)
  | false =>
      obtain ⟨rooted, hstart, hOld⟩ := hbankOld hb
      exact bankCleanStageRootedRenewalCost ring hn hb
        (hbankDigit hb) (hbankThreshold hb) rooted hstart hOld

end L3.HeadlineRenewalCleanSmall

#print axioms L3.HeadlineRenewalCleanSmall.smallCleanFinishReferenceOfFoldDigit
#print axioms L3.HeadlineRenewalCleanSmall.smallReferenceAfterNil
#print axioms L3.HeadlineRenewalCleanSmall.smallReferenceAfterCons
#print axioms L3.HeadlineRenewalCleanSmall.renewalSmallOriginsBudgetClean
#print axioms L3.HeadlineRenewalCleanSmall.smallReferenceOriginChargeClean
#print axioms L3.HeadlineRenewalCleanSmall.renewalSmallAttemptWordClean
#print axioms L3.HeadlineRenewalCleanSmall.smallReferenceAttemptDominationClean
#print axioms L3.HeadlineRenewalCleanSmall.smallReferenceOriginRarityClean
#print axioms L3.HeadlineRenewalCleanSmall.smallRunSourceWitnessClean
#print axioms L3.HeadlineRenewalCleanSmall.smallReferenceRetryCoverageOfSourceWitnessClean
#print axioms L3.HeadlineRenewalCleanSmall.smallReferenceRetryCoverageClean
#print axioms L3.HeadlineRenewalCleanSmall.smallCleanReferenceClock
#print axioms L3.HeadlineRenewalCleanSmall.smallCleanRealization
#print axioms L3.HeadlineRenewalCleanSmall.smallCleanStageRootedRenewalCost
#print axioms L3.HeadlineRenewalCleanSmall.stageCleanRootedRenewalCostOfBranches
