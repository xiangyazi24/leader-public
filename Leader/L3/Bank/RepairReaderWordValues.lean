import Leader.L3.Bank.WordPassMonitor
import Leader.L3.Bank.RepairReaderCloseUse

/-!
R10b: supplying the clean-worker word values to the R stage.

Route (b).  `AcceptedWord` is a monitored W history from
`initializesWord`, which fixes only the root and leaves the physical
serializer/SI fields arbitrary; deriving `CleanWorkerWordValues` from it
would need clean-worker preservation along every monitored W run (an
open statement), so route (a) is not taken.  Instead the W
stage's target is strengthened to `BankWordProjectedTarget ∧
CleanWorkerWordValues` at the native leader.  At every reachable
completion of the causal W epoch the new conjunct is
`bankWordEpochCompletedClean` (all widths); the AcceptedWord
conjunct stays the explicit completion premise.  The strengthened W
stage hands the R stage a start in which the word values hold, so the
R stage needs no further input, and the six-stage finish composes.
-/

namespace L3.RenewalReferenceClock

open L3.HeadlineRenewal
open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree

set_option autoImplicit false
set_option Elab.async false

/-! ## The strengthened W target and clock -/

/-- W acceptance together with the static clean-worker word values at
the native leader.  Consumer: `BankWordCleanClock`,
`BankRepairWordClean`. -/
def BankWordCleanTarget {n : Nat}
    (ring : DirectedRing n)
    (p : Fin n → ProjW (compileAdvice (ceilLogTwo n))) : Prop :=
  BankWordProjectedTarget ring p ∧
    ∃ root : Fin n, (p root).native.l = true ∧
      AcceptedReceipts.WordEntrance.CleanWorker.CleanWorkerWordValues
        ring root p

/-- `BankWordProjectedClock` with the strengthened target.
Consumer: `bankRepairWordCleanHalfStageOfClock`. -/
def BankWordCleanClock {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) : Prop :=
  ∀ z : BankReferenceState ring hbank,
    BankPreparedAtSomeRoot ring hbank z →
    ∀ T : Nat,
      costNumerator (phiW ring)
        (BankWordCleanTarget ring) (piW z.val.1) T ≤
      n ^ T *
        ((440 * ceilLogTwo (ceilLogTwo n) + 275) * n ^ 2)

/-- The strengthened W clock from the argument of
`bankWordProjectedClockOfCompletionBridge`.  The only premise is the
AcceptedWord conjunct at every reachable causal completion; the
word-values conjunct is `bankWordEpochCompletedClean` and the native
leader is the epoch's fixed root.
Consumer: `bankFinishReferenceFinishOfCleanCompletion`. -/
theorem bankWordCleanClockOfCompletion {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hcompletion : ∀ root : Fin n,
      ∀ s : Fin n → ProjW (compileAdvice (ceilLogTwo n)),
        BankWordSerializerRootClass ring hbank root s →
        ∀ z : BankWordEpochState n,
          BankWordEpochReachable ring root s z →
          BankWordRenewalCompleted z →
          BankWordProjectedTarget ring z.2.1) :
    BankWordCleanClock ring hbank := by
  intro z hz T
  obtain ⟨root, hs, _⟩ :=
    bankWordPreparedProjectedSerializerRoot ring hbank z hz
  have hcompletionCost := bankWordEpochCompletionFiveCostHolds
    ring hn hbank root (piW z.val.1) hs T
  have hmono := costNumerator_target_mono_on
    (bankWordEpochNext ring root)
    (BankWordEpochReachable ring root (piW z.val.1))
    BankWordRenewalCompleted
    (fun q : BankWordEpochState n =>
      BankWordCleanTarget ring q.2.1)
    (fun q hq e =>
      bankWordEpochReachableNext
        ring root (piW z.val.1) q hq e)
    (fun q hq hcomplete =>
      ⟨hcompletion root (piW z.val.1) hs q hq hcomplete,
        root,
        (bankWordEpochFixedRoot ring hn hbank root (piW z.val.1) hs q hq).1,
        (bankWordEpochCompletedClean ring hn hbank root (piW z.val.1)
          hs q hq hcomplete).1⟩)
    T (bankWordEpochStart (piW z.val.1)) ⟨[], rfl⟩
  have hmap := costNumerator_map_eq
    (bankWordEpochNext ring root)
    (phiW ring)
    (fun q : BankWordEpochState n => q.2.1)
    (by intro q e; exact bankWordEpochPhysicalNext ring root q e)
    (BankWordCleanTarget ring)
    T (bankWordEpochStart (piW z.val.1))
  rw [hmap] at hmono
  exact Nat.le_trans hmono hcompletionCost

/-! ## The strengthened W stage on the masked BANK reference -/

/-- The W stage target on the reference: accepted W with the word
values at the native leader.  Consumer: `bankRepairWordCleanHalfStageOfClock`,
`bankFinishMaskedRepairBoundOfCleanWord`. -/
def BankRepairWordClean {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank) : Prop :=
  BankWordCleanTarget ring (piW z.val.1)

/-- Generic form of `bankWordReferenceCostProjection`: on the drain,
every first-hit numerator of a W-projected target is the phiW one.
Consumer: `bankRepairWordCleanHalfStageOfClock`. -/
theorem bankRepairCloseWCostProjection {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (Q : (Fin n → ProjW (compileAdvice (ceilLogTwo n))) → Prop) :
    ∀ T : Nat, ∀ z : BankReferenceState ring hbank,
      BankPostInheritedGrantDrain ring hbank z →
      costNumerator (bankRepairNext ring hbank)
        (fun y => Q (piW y.val.1)) z T =
      costNumerator (phiW ring) Q (piW z.val.1) T := by
  classical
  intro T
  induction T with
  | zero =>
      intro z _
      simp only [costNumerator_zero]
  | succ T ih =>
      intro z hz
      by_cases hw : Q (piW z.val.1)
      · rw [costNumerator_terminal
          (bankRepairNext ring hbank)
          (fun y => Q (piW y.val.1)) z hw (T + 1),
          costNumerator_terminal
            (phiW ring) Q (piW z.val.1) hw (T + 1)]
      · rw [costNumerator_succ
          (bankRepairNext ring hbank)
          (fun y => Q (piW y.val.1)) z hw T,
          costNumerator_succ
            (phiW ring) Q (piW z.val.1) hw T]
        congr 1
        exact ofFn_sum_eq _ _ (fun e => by
          have hh := ih (bankRepairNext ring hbank z e)
            (bankWordPostInheritedDomainStep ring hn hbank z hz e)
          rw [bankWordReferenceProjectedStep ring
            (by omega : 2 ≤ n) hbank z hz.1.2 e] at hh
          exact hh)

/-- The strengthened W half-stage from the strengthened clock (same
budget as `BankRepairWordStage`).
Consumer: `bankFinishMaskedRepairBoundOfCleanWord`. -/
theorem bankRepairWordCleanHalfStageOfClock {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hclock : BankWordCleanClock ring hbank) :
    BankRepairHalfStage
      (bankRepairNext ring hbank)
      (BankPreparedAtSomeRoot ring hbank)
      (BankRepairWordClean ring hbank)
      (2 * (440 * ceilLogTwo (ceilLogTwo n) + 275)) := by
  intro z hz T
  have hprojection := bankRepairCloseWCostProjection
    ring hn hbank (BankWordCleanTarget ring) T z
    (bankWordPreparedPostInherited ring hbank z hz)
  have hcost := hclock z hz T
  rw [← hprojection] at hcost
  have hscaled := Nat.mul_le_mul_left 2 hcost
  have hfactor :
      2 * (n ^ T *
        ((440 * ceilLogTwo (ceilLogTwo n) + 275) * n ^ 2)) =
      n ^ T *
        ((2 * (440 * ceilLogTwo (ceilLogTwo n) + 275)) *
          n ^ 2) := by
    ac_rfl
  rw [hfactor] at hscaled
  exact hscaled

/-! ## The R stage on the strengthened start -/

/-- R-stage start: grant-free, W-accepted, with the word values at
the native leader.  Consumer: `bankRepairReaderStageClean`. -/
def BankRepairWAcceptedClean {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank) : Prop :=
  BankRepairWAcceptedOnDrain ring hbank z ∧
    BankRepairCloseWordValuesAt ring hbank z

/-- The R half-stage with no open input: the proved retirement clock
and the window-geometry fold soundness at the start's own word values.
Consumer: `bankFinishMaskedRepairBoundOfCleanWord`. -/
theorem bankRepairReaderStageClean {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) :
    BankRepairHalfStage
      (bankRepairNext ring hbank)
      (BankRepairWAcceptedClean ring hbank)
      (BankRepairReader ring hbank)
      (2 * ceilLogTwo (ceilLogTwo n)) := by
  intro start hS T
  obtain ⟨root, hroot, hvals⟩ := hS.2
  have hrows := bankRepairCloseRowsAtOfValues ring hn hbank start root
    (bankRepairCloseFixedRootOfAccepted ring hbank start hS.1.2 root hroot)
    hvals
  have hmono :
      costNumerator (bankRepairNext ring hbank)
          (BankRepairReader ring hbank) start T ≤
        costNumerator (bankRepairNext ring hbank)
          (BankRepairReaderRetiredFrom ring hbank start)
          start T :=
    Prob.costNumerator_target_mono
      (bankRepairNext ring hbank)
      (BankRepairReaderRetiredFrom ring hbank start)
      (BankRepairReader ring hbank)
      (fun finish hret => by
        rcases hret with
          ⟨word, initial, control, _hactual, hinit,
            hrun, hdone, hnames⟩
        have hacc := bankRepairCloseFoldAt ring hbank start finish hrows
          word initial control hinit hrun hdone hnames
        change AcceptedReceipts.AcceptedReader ring
          (AcceptedReceipts.AcceptedWord ring
            (BlockA.wordT ring) (BlockA.wordValidated ring))
          (Closure.readerFoldValid (ceilLogTwo n) n)
          (piR finish.val.1)
        exact ⟨piR start.val.1, initial, word,
          .live (piR finish.val.1) control,
          hinit, hrun, hacc⟩) start T
  exact Nat.le_trans (Nat.mul_le_mul_left 2 hmono)
    (bankRepairResidentRetirementClockOnDrain ring hn hbank
      start hS.1.1 hS.1.2 T)

/-! ## The six-stage finish with the strengthened W target -/

/-- Replaces `bankFinishMaskedRepairBoundOfStagesOnDrain`: W stage on
the strengthened target, R stage `bankRepairReaderStageClean` (no
premise); digit, debt, request and stop stages and the receipt
preservation as installed.
Consumer: `bankFinishReferenceFinishOfCleanCompletion`. -/
theorem bankFinishMaskedRepairBoundOfCleanWord {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hpres : BankRepairReceiptPreservation ring hbank)
    (hword : BankRepairHalfStage
      (bankRepairNext ring hbank)
      (BankPreparedAtSomeRoot ring hbank)
      (BankRepairWordClean ring hbank)
      (2 * (440 * ceilLogTwo (ceilLogTwo n) + 275)))
    (hdigit : BankRepairDigitStage ring hbank)
    (hdebt : BankRepairDebtStage ring hbank)
    (hrequest : BankRepairRequestStage ring hbank)
    (hstop : BankRepairStopStage ring hbank) :
    BankFinishMaskedRepairBound ring hbank := by
  rcases hpres with
    ⟨hCoreClosed, hWordClosed, hReaderClosed,
      hDigitClosed, hDebtClosed⟩
  have hDrainClosed := bankPostInheritedGrantDrainClosed ring hn hbank
  have hW0 : BankRepairHalfStage
      (bankRepairNext ring hbank)
      (BankPreparedAtSomeRoot ring hbank)
      (fun z => (BankPostInheritedGrantDrain ring hbank z ∧
          BankRepairCore ring hbank z) ∧ BankRepairWordClean ring hbank z)
      (2 * (440 * ceilLogTwo (ceilLogTwo n) + 275)) :=
    bankRepairCloseHalfStrengthen (bankRepairNext ring hbank)
      (BankPreparedAtSomeRoot ring hbank)
      (fun z => BankPostInheritedGrantDrain ring hbank z ∧
        BankRepairCore ring hbank z)
      (BankRepairWordClean ring hbank)
      (2 * (440 * ceilLogTwo (ceilLogTwo n) + 275))
      (fun z hz => ⟨bankWordPreparedPostInherited ring hbank z hz,
        bankRepairPreparedCore ring hn hbank z hz⟩)
      (fun z hz e => ⟨hDrainClosed z hz.1 e, hCoreClosed z hz.2 e⟩)
      hword
  have hW : BankRepairHalfStage
      (bankRepairNext ring hbank)
      (BankPreparedAtSomeRoot ring hbank)
      (BankRepairWAcceptedClean ring hbank)
      (2 * (440 * ceilLogTwo (ceilLogTwo n) + 275)) :=
    bankRepairCloseHalfWeaken (bankRepairNext ring hbank) _ _ _ _
      (fun z hz => ⟨⟨hz.1.1, hz.1.2, hz.2.1⟩, hz.2.2⟩) hW0
  have hR0 : BankRepairHalfStage
      (bankRepairNext ring hbank)
      (BankRepairWAcceptedClean ring hbank)
      (fun z => BankRepairWAcceptedOnDrain ring hbank z ∧
        BankRepairReader ring hbank z)
      (2 * ceilLogTwo (ceilLogTwo n)) :=
    bankRepairCloseHalfStrengthen (bankRepairNext ring hbank)
      (BankRepairWAcceptedClean ring hbank)
      (BankRepairWAcceptedOnDrain ring hbank)
      (BankRepairReader ring hbank) (2 * ceilLogTwo (ceilLogTwo n))
      (fun z hz => hz.1)
      (fun z hz e => ⟨hDrainClosed z hz.1 e, hWordClosed z hz.2 e⟩)
      (bankRepairReaderStageClean ring hn hbank)
  have hR : BankRepairHalfStage
      (bankRepairNext ring hbank)
      (BankRepairWAcceptedClean ring hbank)
      (BankRepairRFoldEstablished ring hbank)
      (2 * ceilLogTwo (ceilLogTwo n)) :=
    bankRepairCloseHalfWeaken (bankRepairNext ring hbank) _ _ _ _
      (fun z hz => ⟨hz.1.2, hz.2⟩) hR0
  have hD : BankRepairHalfStage
      (bankRepairNext ring hbank)
      (BankRepairRFoldEstablished ring hbank)
      (BankRepairDBarred ring hbank) 203 :=
    bankRepairCloseHalfStrengthen (bankRepairNext ring hbank)
      (BankRepairRFoldEstablished ring hbank)
      (BankRepairRFoldEstablished ring hbank)
      (BankRepairDigit ring hbank) 203
      (fun z hz => hz) hReaderClosed hdigit.2
  have hDebt : BankRepairHalfStage
      (bankRepairNext ring hbank)
      (BankRepairDBarred ring hbank)
      (BankRepairDebtCleared ring hbank) 1 :=
    bankRepairCloseHalfStrengthen (bankRepairNext ring hbank)
      (BankRepairDBarred ring hbank)
      (BankRepairDBarred ring hbank)
      (BankRepairDebtZero ring hbank) 1
      (fun z hz => hz) hDigitClosed hdebt.2
  have hRequest : BankRepairHalfStage
      (bankRepairNext ring hbank)
      (BankRepairDebtCleared ring hbank)
      (BankRepairRequestsQuiet ring hbank) 2 :=
    bankRepairCloseHalfStrengthen (bankRepairNext ring hbank)
      (BankRepairDebtCleared ring hbank)
      (BankRepairDebtCleared ring hbank)
      (BankRepairRequestZero ring hbank) 2
      (fun z hz => hz) hDebtClosed hrequest.2
  have hFromDebt := bankRepairCloseHalfCompose (bankRepairNext ring hbank)
    (BankRepairDebtCleared ring hbank)
    (BankRepairRequestsQuiet ring hbank)
    (bankRepairStop ring hbank) 2 0 hRequest hstop.2
  have hFromDigit := bankRepairCloseHalfCompose (bankRepairNext ring hbank)
    (BankRepairDBarred ring hbank)
    (BankRepairDebtCleared ring hbank)
    (bankRepairStop ring hbank) 1 (2 + 0) hDebt hFromDebt
  have hFromReader := bankRepairCloseHalfCompose (bankRepairNext ring hbank)
    (BankRepairRFoldEstablished ring hbank)
    (BankRepairDBarred ring hbank)
    (bankRepairStop ring hbank) 203 (1 + (2 + 0)) hD hFromDigit
  have hFromWord := bankRepairCloseHalfCompose (bankRepairNext ring hbank)
    (BankRepairWAcceptedClean ring hbank)
    (BankRepairRFoldEstablished ring hbank)
    (bankRepairStop ring hbank)
    (2 * ceilLogTwo (ceilLogTwo n)) (203 + (1 + (2 + 0))) hR hFromReader
  have hFromPrepared := bankRepairCloseHalfCompose (bankRepairNext ring hbank)
    (BankPreparedAtSomeRoot ring hbank)
    (BankRepairWAcceptedClean ring hbank)
    (bankRepairStop ring hbank)
    (2 * (440 * ceilLogTwo (ceilLogTwo n) + 275))
    (2 * ceilLogTwo (ceilLogTwo n) + (203 + (1 + (2 + 0)))) hW hFromWord
  intro z hz T
  change costNumerator (bankRepairNext ring hbank)
    (bankRepairStop ring hbank) z T ≤
      n ^ T * ((441 * ceilLogTwo (ceilLogTwo n) + 378) * n ^ 2)
  have hcost := hFromPrepared z hz T
  have hcoefficient :
      2 * (440 * ceilLogTwo (ceilLogTwo n) + 275) +
        (2 * ceilLogTwo (ceilLogTwo n) + (203 + (1 + (2 + 0)))) =
        2 * (441 * ceilLogTwo (ceilLogTwo n) + 378) := by
    omega
  rw [hcoefficient] at hcost
  have hscale :
      n ^ T * (2 * (441 * ceilLogTwo (ceilLogTwo n) + 378) * n ^ 2) =
        2 * (n ^ T * ((441 * ceilLogTwo (ceilLogTwo n) + 378) * n ^ 2)) := by
    ac_rfl
  rw [hscale] at hcost
  omega

/-- The installed reference finish allowance from: the AcceptedWord
conjunct at every reachable causal W completion (explicit premise),
all widths, receipt preservation, and the digit, debt, request and
stop stages.  The W word values and the whole R stage are discharged.
Consumer: the BANK reference finish (`BankReferenceClock` finish field). -/
theorem bankFinishReferenceFinishOfCleanCompletion {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hcompletion : ∀ root : Fin n,
      ∀ s : Fin n → ProjW (compileAdvice (ceilLogTwo n)),
        BankWordSerializerRootClass ring hbank root s →
        ∀ z : BankWordEpochState n,
          BankWordEpochReachable ring root s z →
          BankWordRenewalCompleted z →
          BankWordProjectedTarget ring z.2.1)
    (hpres : BankRepairReceiptPreservation ring hbank)
    (hdigit : BankRepairDigitStage ring hbank)
    (hdebt : BankRepairDebtStage ring hbank)
    (hrequest : BankRepairRequestStage ring hbank)
    (hstop : BankRepairStopStage ring hbank) :
    StageReferenceGeneratedFinish
      (bankRepairNext ring hbank)
      (BankPreparedAtSomeRoot ring hbank)
      (bankRepairStop ring hbank)
      (headlineReferenceFinishRate (ceilLogTwo n)) :=
  bankFinishRepairBoundToReferenceFinish ring hn hbank
    (bankFinishMaskedRepairBoundOfCleanWord ring hn hbank hpres
      (bankRepairWordCleanHalfStageOfClock ring hn hbank
        (bankWordCleanClockOfCompletion ring hn hbank hcompletion))
      hdigit hdebt hrequest hstop)

end L3.RenewalReferenceClock

#print axioms L3.RenewalReferenceClock.bankWordCleanClockOfCompletion
#print axioms L3.RenewalReferenceClock.bankRepairWordCleanHalfStageOfClock
#print axioms L3.RenewalReferenceClock.bankRepairReaderStageClean
#print axioms L3.RenewalReferenceClock.bankFinishMaskedRepairBoundOfCleanWord
#print axioms L3.RenewalReferenceClock.bankFinishReferenceFinishOfCleanCompletion
