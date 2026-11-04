import Leader.L3.Bank.FinishCleanWord
import Leader.L3.Small.RepairStages
import Leader.L3.Small.ReferenceFinish
import Leader.L3.CleanTargetClosure

/-!
SMALL clean-reference finish: closed transport and conditional stage assembly.

This module deliberately does not assert the requested premise-only
smallCleanFinishReference.  The first absent producer is the genuine SMALL
resident-retirement trace/clock, not the static clean reader initializer.
All statements below use the actual renewalSmallNext and Gclean.
-/

namespace L3.SmallFinishClean

open L3
open L3.HeadlineRenewal
open L3.SmallRenewal
open L3.SmallFinishRepair
open L3.SmallRepairStages
open L3.SmallCandidatePreparation
open L3.RenewalReferenceClock
open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree
open Classical

set_option autoImplicit false
set_option Elab.async false

/-! Clean SMALL factors, on the actual physical projection. -/

/-- Consumer: the SMALL clean W entrance and clean reader initializer. -/
def SmallCleanWord {n : Nat}
    (ring : DirectedRing n) (r : RenewalSmallReference n) : Prop :=
  CleanWord ring (piW r.1)

/-- Consumer: the clean R stage and the six-stage composition. -/
def SmallCleanReader {n : Nat}
    (ring : DirectedRing n) (r : RenewalSmallReference n) : Prop :=
  AcceptedReceipts.AcceptedReader ring (CleanWord ring)
    (Closure.readerFoldValid (ceilLogTwo n) n) (piR r.1)

/-- Consumer: the clean digit stage and physical debt event. -/
def SmallCleanDigit {n : Nat}
    (ring : DirectedRing n) (r : RenewalSmallReference n) : Prop :=
  AcceptedReceipts.BarredDigitClass ring
    (CleanWordAtRoot ring) (piD r.1)

/-- Consumer: clean W to R stage. -/
def SmallCleanWAccepted {n : Nat}
    (ring : DirectedRing n) (r : RenewalSmallReference n) : Prop :=
  SmallRepairCore ring r ∧ SmallCleanWord ring r

/-- Consumer: clean R to D stage. -/
def SmallCleanRFold {n : Nat}
    (ring : DirectedRing n) (r : RenewalSmallReference n) : Prop :=
  SmallCleanWAccepted ring r ∧ SmallCleanReader ring r

/-- Consumer: clean D to debt stage. -/
def SmallCleanDBarred {n : Nat}
    (ring : DirectedRing n) (r : RenewalSmallReference n) : Prop :=
  SmallCleanRFold ring r ∧ SmallCleanDigit ring r

/-- Consumer: clean debt to request stage. -/
def SmallCleanDebtCleared {n : Nat}
    (ring : DirectedRing n) (r : RenewalSmallReference n) : Prop :=
  SmallCleanDBarred ring r ∧ RepairDebtZero smallRepairView r

/-- Consumer: the clean STOP line. -/
def SmallCleanRequestsQuiet {n : Nat}
    (ring : DirectedRing n) (r : RenewalSmallReference n) : Prop :=
  SmallCleanDebtCleared ring r ∧ RepairRequestZero smallRepairView r

/-- The exact clean target, not the OLD generated monitor. -/
def smallCleanStop {n : Nat}
    (ring : DirectedRing n) (r : RenewalSmallReference n) : Prop :=
  Gclean ring r.1

/-- Consumer: the clean reader stage on the no-new-FIRE suffix. -/
def SmallCleanWAcceptedOnGuard {n : Nat}
    (ring : DirectedRing n) (r : RenewalSmallReference n) : Prop :=
  SmallRepairGuard ring r ∧ SmallCleanWAccepted ring r

/-- Consumer: the clean digit half-stage. -/
def SmallCleanRFoldOnGuard {n : Nat}
    (ring : DirectedRing n) (r : RenewalSmallReference n) : Prop :=
  SmallRepairGuard ring r ∧ SmallCleanRFold ring r

/-- Consumer: the clean debt half-stage. -/
def SmallCleanDBarredOnGuard {n : Nat}
    (ring : DirectedRing n) (r : RenewalSmallReference n) : Prop :=
  SmallRepairGuard ring r ∧ SmallCleanDBarred ring r

/-- Consumer: the clean request half-stage. -/
def SmallCleanDebtClearedOnGuard {n : Nat}
    (ring : DirectedRing n) (r : RenewalSmallReference n) : Prop :=
  SmallRepairGuard ring r ∧ SmallCleanDebtCleared ring r

/-! The five genuine guard-relative receipt closures. -/

/-- Clean W is stable under the masked SMALL step on its proven guard.
Consumer: smallCleanReceiptPreservationOnGuard. -/
theorem smallCleanWordStepOnGuard {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (r : RenewalSmallReference n)
    (hg : SmallRepairGuard ring r)
    (hw : SmallCleanWord ring r) (e : Fin n) :
    SmallCleanWord ring (renewalSmallNext ring r e) := by
  change CleanWord ring (piW (renewalSmallNext ring r e).1)
  rw [smallRepairWordPhiStep ring (by omega : 2 ≤ n) r hg e]
  exact cleanWordPhiStep (by omega : 3 ≤ n) ring (piW r.1) e hw

/-- E.G22/E.G23 with the CleanWord origin on the actual SMALL mask.
Consumer: smallCleanReceiptPreservationOnGuard. -/
theorem smallCleanReaderStepOnGuard {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (r : RenewalSmallReference n)
    (hg : SmallRepairGuard ring r)
    (hr : SmallCleanReader ring r) (e : Fin n) :
    SmallCleanReader ring (renewalSmallNext ring r e) := by
  change AcceptedReceipts.AcceptedReader ring (CleanWord ring)
    (Closure.readerFoldValid (ceilLogTwo n) n)
    (piR (renewalSmallNext ring r e).1)
  rw [smallRepairReaderPhiStep ring (by omega : 2 ≤ n) r hg e]
  exact cleanReaderGeneratedPhiStep (by omega : 2 ≤ n)
    ring (piR r.1) e hr

/-- E.G35/E.G36 with the clean fixed-root origin.
Consumer: smallCleanReceiptPreservationOnGuard. -/
theorem smallCleanDigitStepOnGuard {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (r : RenewalSmallReference n)
    (hg : SmallRepairGuard ring r)
    (hd : SmallCleanDigit ring r) (e : Fin n) :
    SmallCleanDigit ring (renewalSmallNext ring r e) := by
  change AcceptedReceipts.BarredDigitClass ring (CleanWordAtRoot ring)
    (piD (renewalSmallNext ring r e).1)
  rw [smallRepairDigitPhiStep ring (by omega : 2 ≤ n) r hg e]
  exact cleanDigitGeneratedPhiStep hn ring (piD r.1) e hd

/-- The physical DCC debt row only requires QReader and QDigit;
their clean-origin witnesses imply exactly those two facts.
Consumer: the fifth clean receipt closure and the debt half-stage. -/
theorem smallCleanDebtZeroStep {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (r : RenewalSmallReference n)
    (hreader : SmallCleanReader ring r)
    (hdigit : SmallCleanDigit ring r)
    (hdebt : RepairDebtZero smallRepairView r)
    (e : Fin n) :
    RepairDebtZero smallRepairView (renewalSmallNext ring r e) := by
  have hQReader : AcceptedReceipts.QReader ring (piR r.1) :=
    AcceptedReceipts.accepted_reader_qreader ring
      (CleanWord ring)
      (Closure.readerFoldValid (ceilLogTwo n) n)
      (piR r.1) hreader
  have hQDigit : AcceptedReceipts.QDigit ring (piD r.1) :=
    AcceptedReceipts.barred_digit_qdigit ring
      (CleanWordAtRoot ring) (piD r.1) hdigit
  have hev := Closure.certificateEventQuietFromSafe
    (by omega : 2 ≤ n) ring r.1 e hQReader hQDigit
  have hdcc := Closure.dccQuietRow
    (r.1 e) (r.1 (ring.rightNeighbor e))
    (certificateStep (compileAdvice (ceilLogTwo n))
      (r.1 e) (r.1 (ring.rightNeighbor e))).2.2
    (hdebt e).1 (hdebt e).2
    (hdebt (ring.rightNeighbor e)).1
    (hdebt (ring.rightNeighbor e)).2 hev
  have hx := Closure.transitionDebtSourceFormula
    (compileAdvice (ceilLogTwo n))
    (r.1 e) (r.1 (ring.rightNeighbor e))
  have hy := Closure.transitionDebtDestinationFormula
    (compileAdvice (ceilLogTwo n))
    (r.1 e) (r.1 (ring.rightNeighbor e))
  rw [hdcc] at hx hy
  have hmaskX :
      (renewalMaskedPair (compileAdvice (ceilLogTwo n))
        (renewalSmallCut ring r.1 r.2 e)
        (r.1 e) (r.1 (ring.rightNeighbor e))).1.EU = false ∧
      (renewalMaskedPair (compileAdvice (ceilLogTwo n))
        (renewalSmallCut ring r.1 r.2 e)
        (r.1 e) (r.1 (ring.rightNeighbor e))).1.ED = false := by
    cases hm : renewalSmallCut ring r.1 r.2 e with
    | false => simpa [renewalMaskedPair, hm] using hx
    | true => simpa [renewalMaskedPair, hm] using hx
  have hmaskY :
      (renewalMaskedPair (compileAdvice (ceilLogTwo n))
        (renewalSmallCut ring r.1 r.2 e)
        (r.1 e) (r.1 (ring.rightNeighbor e))).2.EU = false ∧
      (renewalMaskedPair (compileAdvice (ceilLogTwo n))
        (renewalSmallCut ring r.1 r.2 e)
        (r.1 e) (r.1 (ring.rightNeighbor e))).2.ED = false := by
    cases hm : renewalSmallCut ring r.1 r.2 e with
    | false => simpa [renewalMaskedPair, hm] using hy
    | true => simpa [renewalMaskedPair, hm] using hy
  intro i
  change
    (if i = e then
      (renewalMaskedPair (compileAdvice (ceilLogTwo n))
        (renewalSmallCut ring r.1 r.2 e)
        (r.1 e) (r.1 (ring.rightNeighbor e))).1
     else if i = ring.rightNeighbor e then
      (renewalMaskedPair (compileAdvice (ceilLogTwo n))
        (renewalSmallCut ring r.1 r.2 e)
        (r.1 e) (r.1 (ring.rightNeighbor e))).2
     else r.1 i).EU = false ∧
    (if i = e then
      (renewalMaskedPair (compileAdvice (ceilLogTwo n))
        (renewalSmallCut ring r.1 r.2 e)
        (r.1 e) (r.1 (ring.rightNeighbor e))).1
     else if i = ring.rightNeighbor e then
      (renewalMaskedPair (compileAdvice (ceilLogTwo n))
        (renewalSmallCut ring r.1 r.2 e)
        (r.1 e) (r.1 (ring.rightNeighbor e))).2
     else r.1 i).ED = false
  by_cases hi : i = e
  · simpa only [if_pos hi] using hmaskX
  · by_cases hj : i = ring.rightNeighbor e
    · subst hj
      simpa [hi] using hmaskY
    · simpa [hi, hj, smallRepairView] using hdebt i

/-- Consumer: six-stage SMALL clean reference composition.
The guard is essential; this is not an unguarded closure theorem. -/
def SmallCleanReceiptPreservationOnGuard {n : Nat}
    (ring : DirectedRing n) : Prop :=
  (∀ r, SmallRepairGuard ring r → SmallRepairCore ring r →
    ∀ e, SmallRepairCore ring (renewalSmallNext ring r e)) ∧
  (∀ r, SmallRepairGuard ring r → SmallCleanWAccepted ring r →
    ∀ e, SmallCleanWAccepted ring (renewalSmallNext ring r e)) ∧
  (∀ r, SmallRepairGuard ring r → SmallCleanRFold ring r →
    ∀ e, SmallCleanRFold ring (renewalSmallNext ring r e)) ∧
  (∀ r, SmallRepairGuard ring r → SmallCleanDBarred ring r →
    ∀ e, SmallCleanDBarred ring (renewalSmallNext ring r e)) ∧
  (∀ r, SmallRepairGuard ring r → SmallCleanDebtCleared ring r →
    ∀ e, SmallCleanDebtCleared ring (renewalSmallNext ring r e))

/-- Five masked SMALL clean closures without extra clock premises.
Consumer: smallCleanFinishReferenceOfStages. -/
theorem smallCleanReceiptPreservationOnGuard {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n) :
    SmallCleanReceiptPreservationOnGuard ring := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro r hg hc e
    exact smallRepairCoreStepOnGuard ring hn r hg hc e
  · intro r hg hw e
    exact ⟨smallRepairCoreStepOnGuard ring hn r hg hw.1 e,
      smallCleanWordStepOnGuard ring hn r hg hw.2 e⟩
  · intro r hg hr e
    exact ⟨⟨smallRepairCoreStepOnGuard ring hn r hg hr.1.1 e,
      smallCleanWordStepOnGuard ring hn r hg hr.1.2 e⟩,
      smallCleanReaderStepOnGuard ring hn r hg hr.2 e⟩
  · intro r hg hd e
    exact ⟨⟨⟨smallRepairCoreStepOnGuard ring hn r hg hd.1.1.1 e,
      smallCleanWordStepOnGuard ring hn r hg hd.1.1.2 e⟩,
      smallCleanReaderStepOnGuard ring hn r hg hd.1.2 e⟩,
      smallCleanDigitStepOnGuard ring hn r hg hd.2 e⟩
  · intro r hg hb e
    exact ⟨⟨⟨⟨smallRepairCoreStepOnGuard ring hn r hg
      hb.1.1.1.1 e,
      smallCleanWordStepOnGuard ring hn r hg hb.1.1.1.2 e⟩,
      smallCleanReaderStepOnGuard ring hn r hg hb.1.1.2 e⟩,
      smallCleanDigitStepOnGuard ring hn r hg hb.1.2 e⟩,
      smallCleanDebtZeroStep ring hn r hb.1.1.2 hb.1.2 hb.2 e⟩

/-- Concrete clean STOP: no debt or request, not OLD monitor acceptance.
Consumer: smallCleanStopStage. -/
theorem smallCleanRequestsQuietStop {n : Nat}
    (ring : DirectedRing n) (r : RenewalSmallReference n)
    (hr : SmallCleanRequestsQuiet ring r) :
    smallCleanStop ring r := by
  rcases hr with
    ⟨⟨⟨⟨⟨hcore, hword⟩, hreader⟩, hdigit⟩, hdebt⟩, hrequest⟩
  rcases hcore with ⟨hnative, hcand⟩
  exact ⟨hnative, hcand, hword, hreader, hdigit,
    fun i => ⟨(hdebt i).1, (hdebt i).2, hrequest i⟩⟩

/-- The zero-unit stage on the *actual* clean target.
Consumer: smallCleanFinishReferenceOfStages. -/
theorem smallCleanStopStage {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n) :
    StageReferenceGeneratedFinish
      (renewalSmallNext ring)
      (SmallCleanRequestsQuiet ring) (smallCleanStop ring) 0 ∧
    BankRepairHalfStage
      (renewalSmallNext ring)
      (SmallCleanRequestsQuiet ring) (smallCleanStop ring) 0 := by
  constructor
  · intro r hr
    apply (UniformFirstHit.expectedHittingTimeAtMost_iff_cost
      (renewalSmallNext ring) (smallCleanStop ring)
      (by omega : 0 < n) r (0 * n ^ 2)).2
    intro T
    rw [costNumerator_terminal (renewalSmallNext ring)
      (smallCleanStop ring) r
      (smallCleanRequestsQuietStop ring r hr) T]
    exact Nat.zero_le _
  · intro r hr T
    rw [costNumerator_terminal (renewalSmallNext ring)
      (smallCleanStop ring) r
      (smallCleanRequestsQuietStop ring r hr) T]
    exact Nat.zero_le _

/-! Clean W projected clock and its real-mask transport. -/

/-- Open W producer, with BankWordCleanWordTarget as requested.
Consumer: smallCleanWordHalfStage; not an assertion of this clock. -/
def SmallCleanWordClock {n : Nat}
    (ring : DirectedRing n) : Prop :=
  ∀ r : RenewalSmallReference n,
    SmallPreparedAtSomeRoot ring r →
    ∀ T : Nat,
      costNumerator (phiW ring)
        (BankWordCleanWordTarget ring) (piW r.1) T ≤
      n ^ T * ((440 * smallRepairWidth n + 275) * n ^ 2)

/-- Exact cost projection on the proven grant-free SMALL guard.
Consumer: smallCleanWordHalfStage. -/
theorem smallCleanWordCostProjection {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hsmall : (compileAdvice (ceilLogTwo n)).useSmall = true) :
    ∀ (T : Nat) (r : RenewalSmallReference n),
      SmallRepairGuard ring r →
      costNumerator (renewalSmallNext ring)
        (fun z => BankWordCleanWordTarget ring (piW z.1)) r T =
      costNumerator (phiW ring)
        (BankWordCleanWordTarget ring) (piW r.1) T := by
  intro T
  induction T with
  | zero =>
      intro r _
      simp only [costNumerator_zero]
  | succ T ih =>
      intro r hg
      by_cases ht : BankWordCleanWordTarget ring (piW r.1)
      · rw [costNumerator_terminal (renewalSmallNext ring)
          (fun z => BankWordCleanWordTarget ring (piW z.1))
          r ht (T + 1),
          costNumerator_terminal (phiW ring)
            (BankWordCleanWordTarget ring) (piW r.1) ht (T + 1)]
      · rw [costNumerator_succ (renewalSmallNext ring)
          (fun z => BankWordCleanWordTarget ring (piW z.1))
          r ht T,
          costNumerator_succ (phiW ring)
            (BankWordCleanWordTarget ring) (piW r.1) ht T]
        congr 1
        exact ofFn_sum_eq _ _ (fun e => by
          have hh := ih (renewalSmallNext ring r e)
            (smallRepairGuardStep ring hn hsmall r hg e)
          rw [smallRepairWordPhiStep ring (by omega : 2 ≤ n)
            r hg e] at hh
          exact hh)

/-- The SMALL clean W half-stage, with no old AcceptedWord hypothesis.
Consumer: smallCleanWAcceptedOnGuardHalfStage. -/
theorem smallCleanWordHalfStage {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hsmall : (compileAdvice (ceilLogTwo n)).useSmall = true)
    (hword : SmallCleanWordClock ring) :
    BankRepairHalfStage (renewalSmallNext ring)
      (SmallPreparedAtSomeRoot ring)
      (fun r => BankWordCleanWordTarget ring (piW r.1))
      (2 * (440 * smallRepairWidth n + 275)) := by
  intro r hr T
  have hprojection := smallCleanWordCostProjection
    ring hn hsmall T r (smallRepairGuardFromPrepared ring r hr)
  have hcost := hword r hr T
  rw [← hprojection] at hcost
  have hdouble := Nat.mul_le_mul_left 2 hcost
  have hfactor :
      2 * (n ^ T * ((440 * smallRepairWidth n + 275) * n ^ 2)) =
      n ^ T * ((2 * (440 * smallRepairWidth n + 275)) *
        n ^ 2) := by
    simp only [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
  rw [hfactor] at hdouble
  exact hdouble

/-- A reached clean W entrance retains the core and the SMALL guard
at the same actual reference cut. Consumer: the R stage. -/
theorem smallCleanWAcceptedOnGuardHalfStage {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hsmall : (compileAdvice (ceilLogTwo n)).useSmall = true)
    (hword : SmallCleanWordClock ring) :
    BankRepairHalfStage (renewalSmallNext ring)
      (SmallPreparedAtSomeRoot ring)
      (SmallCleanWAcceptedOnGuard ring)
      (2 * (440 * smallRepairWidth n + 275)) := by
  have hstrength : BankRepairHalfStage (renewalSmallNext ring)
      (SmallPreparedAtSomeRoot ring)
      (fun r => (SmallRepairGuard ring r ∧ SmallRepairCore ring r) ∧
        BankWordCleanWordTarget ring (piW r.1))
      (2 * (440 * smallRepairWidth n + 275)) :=
    bankRepairCloseHalfStrengthen (renewalSmallNext ring)
      (SmallPreparedAtSomeRoot ring)
      (fun r => SmallRepairGuard ring r ∧ SmallRepairCore ring r)
      (fun r => BankWordCleanWordTarget ring (piW r.1))
      (2 * (440 * smallRepairWidth n + 275))
      (fun r hr => ⟨smallRepairGuardFromPrepared ring r hr,
        smallRepairPreparedCore ring hn r hr⟩)
      (fun r hz e => ⟨smallRepairGuardStep ring hn hsmall r hz.1 e,
        smallRepairCoreStepOnGuard ring hn r hz.1 hz.2 e⟩)
      (smallCleanWordHalfStage ring hn hsmall hword)
  exact bankRepairCloseHalfWeaken (renewalSmallNext ring)
    (SmallPreparedAtSomeRoot ring)
    (fun r => (SmallRepairGuard ring r ∧ SmallRepairCore ring r) ∧
      BankWordCleanWordTarget ring (piW r.1))
    (SmallCleanWAcceptedOnGuard ring)
    (2 * (440 * smallRepairWidth n + 275))
    (fun r hz => by
      obtain ⟨root, hroot, _⟩ := hz.2
      exact ⟨hz.1.1, hz.1.2, root, hroot⟩)
    hstrength

/-! The actual SMALL reader is initialized at the CLEAN W cut.
The source-independent BANK clean visible-read lemmas can be reused;
the BANK reference-state retirement trace cannot. -/

/-- The literal J_R initializer at the current physical W endpoint.
Consumer: the SMALL clean retired-from observer. -/
theorem smallCleanReaderInitializesAtWord {n : Nat}
    (ring : DirectedRing n)
    (r : RenewalSmallReference n)
    (hw : SmallCleanWAccepted ring r) :
    BlockA.initializesReader (CleanWord ring)
      (piR r.1)
      (.live (piR r.1)
        (smallRepairReaderInitialControl ring r)) := by
  constructor
  · change SmallCleanWord ring r
    exact hw.2
  · refine ⟨smallRepairReaderInitialControl ring r, rfl, rfl, ?_⟩
    intro i
    by_cases hi : (piR r.1 i).rawTok.isSome = true
    · simp [smallRepairReaderInitialControl, hi]
    · simp [smallRepairReaderInitialControl, hi]

/-- E.G22: fixed visible old bits and markers on every admitted CLEAN
reader run.  This statement is independent of a BANK hbank witness.
Consumer: a future SMALL clean reader fold proof. -/
theorem smallCleanReaderVisibleRun {n : Nat}
    (ring : DirectedRing n)
    (start : RenewalSmallReference n)
    (initial : BlockA.Decoration
      (Fin n → ProjR (compileAdvice (ceilLogTwo n)))
      (BlockA.ReaderControl n (compileAdvice (ceilLogTwo n))))
    (hinit : BlockA.initializesReader (CleanWord ring)
      (piR start.1) initial) :
    ∀ (word : List (Fin n))
      (p : Fin n → ProjR (compileAdvice (ceilLogTwo n)))
      (gamma : BlockA.Decoration
        (Fin n → ProjR (compileAdvice (ceilLogTwo n)))
        (BlockA.ReaderControl n (compileAdvice (ceilLogTwo n)))),
      BlockA.Run ring (phiR ring) (BlockA.readerControlNext ring)
        (piR start.1) initial word p gamma →
      AcceptedReceipts.QWord ring
        (AcceptedReceipts.wordProjectionR p) ∧
      ∀ i : Fin n,
        AcceptedReceipts.wordVisible
          (AcceptedReceipts.wordProjectionR p) i =
        AcceptedReceipts.wordVisible
          (AcceptedReceipts.wordProjectionR (piR start.1)) i := by
  exact bankCleanRepairReaderE22AdmittedVisibleFixed
    ring (piR start.1) initial hinit

/-- E.G22: R1c/R0b selected reads at a real clean-origin phiR Run.
Consumer: the missing SMALL terminal fold/window proof. -/
theorem smallCleanReaderSelectedReadFixed {n : Nat}
    (ring : DirectedRing n)
    (start : RenewalSmallReference n)
    (initial : BlockA.Decoration
      (Fin n → ProjR (compileAdvice (ceilLogTwo n)))
      (BlockA.ReaderControl n (compileAdvice (ceilLogTwo n))))
    (hinit : BlockA.initializesReader (CleanWord ring)
      (piR start.1) initial)
    (word : List (Fin n))
    (p : Fin n → ProjR (compileAdvice (ceilLogTwo n)))
    (control : BlockA.ReaderControl n (compileAdvice (ceilLogTwo n)))
    (hrun : BlockA.Run ring (phiR ring) (BlockA.readerControlNext ring)
      (piR start.1) initial word p (.live p control))
    (e : Fin n) :
    (BlockA.readerSelectedSample (ring.rightNeighbor e)
      (p e) (p (ring.rightNeighbor e))).oldBit =
        (piR start.1 (ring.rightNeighbor e)).word.u ∧
    (BlockA.readerSelectedSample (ring.rightNeighbor e)
      (p e) (p (ring.rightNeighbor e))).oldMarker =
        (piR start.1 (ring.rightNeighbor e)).word.beta := by
  exact bankCleanRepairReaderE22SelectedReadFixedOnRun
    ring (piR start.1) initial hinit word p control hrun e

/-- The same physical SMALL suffix and a genuinely coupled CleanWord
reader Run, not an arbitrary decorated successful endpoint.
Consumer: smallCleanReaderOfRetiredFrom. -/
def SmallCleanReaderRetiredFrom {n : Nat}
    (ring : DirectedRing n)
    (start finish : RenewalSmallReference n) : Prop :=
  ∃ (word : List (Fin n))
    (initial : BlockA.Decoration
      (Fin n → ProjR (compileAdvice (ceilLogTwo n)))
      (BlockA.ReaderControl n (compileAdvice (ceilLogTwo n))))
    (control : BlockA.ReaderControl n (compileAdvice (ceilLogTwo n))),
    finish = word.foldl (renewalSmallNext ring) start ∧
    BlockA.initializesReader (CleanWord ring)
      (piR start.1) initial ∧
    BlockA.Run ring (phiR ring) (BlockA.readerControlNext ring)
      (piR start.1) initial word
      (piR finish.1) (.live (piR finish.1) control) ∧
    control.phase = .done ∧
    (∀ name : Fin n, control.inheritedNames name = false)

/-- E.G19: still OPEN on the SMALL masked scheduler.  Its first missing
producer is a SMALL resident trace-snoc/run coupling under SmallRepairGuard.
Consumer: smallCleanReaderHalfStageOfRetirementAndFold. -/
def SmallCleanResidentRetirementClock {n : Nat}
    (ring : DirectedRing n) : Prop :=
  ∀ start : RenewalSmallReference n,
    SmallCleanWAcceptedOnGuard ring start →
    ∀ T : Nat,
      2 * costNumerator (renewalSmallNext ring)
        (SmallCleanReaderRetiredFrom ring start) start T ≤
      n ^ T * ((2 * smallRepairWidth n) * n ^ 2)

/-- E.G22 terminal comparison: still OPEN for the SMALL advice width.
The clean visible/sample facts above are necessary, not sufficient.
Consumer: smallCleanReaderOfRetiredFrom. -/
def SmallCleanReaderFoldSound {n : Nat}
    (ring : DirectedRing n) : Prop :=
  ∀ (start finish : RenewalSmallReference n)
    (word : List (Fin n))
    (initial : BlockA.Decoration
      (Fin n → ProjR (compileAdvice (ceilLogTwo n)))
      (BlockA.ReaderControl n (compileAdvice (ceilLogTwo n))))
    (control : BlockA.ReaderControl n (compileAdvice (ceilLogTwo n))),
    SmallCleanWAcceptedOnGuard ring start →
    finish = word.foldl (renewalSmallNext ring) start →
    BlockA.initializesReader (CleanWord ring)
      (piR start.1) initial →
    BlockA.Run ring (phiR ring) (BlockA.readerControlNext ring)
      (piR start.1) initial word
      (piR finish.1) (.live (piR finish.1) control) →
    control.phase = .done →
    (∀ name : Fin n, control.inheritedNames name = false) →
    BlockA.acceptsReader
      (Closure.readerFoldValid (ceilLogTwo n) n)
      (AcceptedReceipts.QReader ring)
      (piR finish.1) (.live (piR finish.1) control)

/-- A coupled retired endpoint gives the *clean-origin* generated reader.
Consumer: the R half-stage. -/
theorem smallCleanReaderOfRetiredFrom {n : Nat}
    (ring : DirectedRing n)
    (hfold : SmallCleanReaderFoldSound ring)
    (start finish : RenewalSmallReference n)
    (hw : SmallCleanWAcceptedOnGuard ring start)
    (hret : SmallCleanReaderRetiredFrom ring start finish) :
    SmallCleanReader ring finish := by
  rcases hret with
    ⟨word, initial, control, hactual, hinit, hrun,
      hdone, hnames⟩
  have hacc := hfold start finish word initial control
    hw hactual hinit hrun hdone hnames
  exact ⟨piR start.1, initial, word,
    .live (piR finish.1) control,
    hinit, hrun, hacc⟩

/-- Cost monotonicity transports genuine retirement to clean R.
The OPEN clock and fold soundness are shown explicitly, not smuggled
into smallCleanFinishReference. -/
theorem smallCleanReaderHalfStageOfRetirementAndFold {n : Nat}
    (ring : DirectedRing n)
    (hclock : SmallCleanResidentRetirementClock ring)
    (hfold : SmallCleanReaderFoldSound ring) :
    BankRepairHalfStage (renewalSmallNext ring)
      (SmallCleanWAcceptedOnGuard ring)
      (SmallCleanReader ring)
      (2 * smallRepairWidth n) := by
  intro start hw T
  have hmono :
      costNumerator (renewalSmallNext ring)
          (SmallCleanReader ring) start T ≤
      costNumerator (renewalSmallNext ring)
          (SmallCleanReaderRetiredFrom ring start) start T :=
    Prob.costNumerator_target_mono
      (renewalSmallNext ring)
      (SmallCleanReaderRetiredFrom ring start)
      (SmallCleanReader ring)
      (fun finish hret =>
        smallCleanReaderOfRetiredFrom ring hfold start finish hw hret)
      start T
  exact Nat.le_trans (Nat.mul_le_mul_left 2 hmono)
    (hclock start hw T)

/-! The two SMALL-specific tail clocks are named separately.
They are not consequences of an unproved old-target SMALL stage. -/

/-- The open clean D half-stage, mirroring BankCleanDigitHalfOnDrain.
Consumer: smallCleanFinishReferenceOfStages. -/
def SmallCleanDigitHalf {n : Nat}
    (ring : DirectedRing n) : Prop :=
  BankRepairHalfStage (renewalSmallNext ring)
    (SmallCleanRFoldOnGuard ring)
    (SmallCleanDigit ring) (smallRepairDigitHalf n)

/-- Open DCC debt hitting clock, *after* the proved clean debt closure.
Consumer: smallCleanFinishReferenceOfStages. -/
def SmallCleanDebtHalf {n : Nat}
    (ring : DirectedRing n) : Prop :=
  BankRepairHalfStage (renewalSmallNext ring)
    (SmallCleanDBarredOnGuard ring)
    (RepairDebtZero smallRepairView) 1

/-- Open SMALL request hitting clock, with the clean lower factors.
Consumer: smallCleanFinishReferenceOfStages. -/
def SmallCleanRequestHalf {n : Nat}
    (ring : DirectedRing n) : Prop :=
  BankRepairHalfStage (renewalSmallNext ring)
    (SmallCleanDebtClearedOnGuard ring)
    (RepairRequestZero smallRepairView) 2

/-! A conditional, genuinely quantitative same-scheduler assembly.
This is NOT the requested two-premise theorem: its missing clock
parameters are exposed until the SMALL R/debt/request producers land. -/

/-- Six-stage clean masked ledger at the exact published SMALL rate.
Consumer: smallCleanFinishReference once R/debt/request are proved.
This proves more than an endpoint restatement: guarded suffix
strengthening, half-cost composition and the 441t+277 rate ledger. -/
theorem smallCleanFinishReferenceOfStages {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hsmall : (compileAdvice (ceilLogTwo n)).useSmall = true)
    (hword : SmallCleanWordClock ring)
    (hretirement : SmallCleanResidentRetirementClock ring)
    (hfold : SmallCleanReaderFoldSound ring)
    (hdigit : SmallCleanDigitHalf ring)
    (hdebt : SmallCleanDebtHalf ring)
    (hrequest : SmallCleanRequestHalf ring) :
    StageReferenceGeneratedFinish
      (renewalSmallNext ring)
      (SmallPreparedAtSomeRoot ring)
      (smallCleanStop ring)
      (headlineReferenceFinishRate (ceilLogTwo n)) := by
  have hp := smallCleanReceiptPreservationOnGuard ring hn
  have hW := smallCleanWAcceptedOnGuardHalfStage ring hn hsmall hword
  have hRinitial := smallCleanReaderHalfStageOfRetirementAndFold
    ring hretirement hfold
  have hRzero : BankRepairHalfStage (renewalSmallNext ring)
      (SmallCleanWAcceptedOnGuard ring)
      (fun r => SmallCleanWAcceptedOnGuard ring r ∧ SmallCleanReader ring r)
      (2 * smallRepairWidth n) :=
    bankRepairCloseHalfStrengthen (renewalSmallNext ring)
      (SmallCleanWAcceptedOnGuard ring)
      (SmallCleanWAcceptedOnGuard ring)
      (SmallCleanReader ring) (2 * smallRepairWidth n)
      (fun r hr => hr)
      (fun r hr e => ⟨smallRepairGuardStep ring hn hsmall r hr.1 e,
        hp.2.1 r hr.1 hr.2 e⟩)
      hRinitial
  have hR : BankRepairHalfStage (renewalSmallNext ring)
      (SmallCleanWAcceptedOnGuard ring)
      (SmallCleanRFoldOnGuard ring)
      (2 * smallRepairWidth n) :=
    bankRepairCloseHalfWeaken (renewalSmallNext ring)
      (SmallCleanWAcceptedOnGuard ring)
      (fun r => SmallCleanWAcceptedOnGuard ring r ∧ SmallCleanReader ring r)
      (SmallCleanRFoldOnGuard ring) (2 * smallRepairWidth n)
      (fun r hr => ⟨hr.1.1, hr.1.2, hr.2⟩) hRzero
  have hDzero : BankRepairHalfStage (renewalSmallNext ring)
      (SmallCleanRFoldOnGuard ring)
      (fun r => SmallCleanRFoldOnGuard ring r ∧ SmallCleanDigit ring r)
      (smallRepairDigitHalf n) :=
    bankRepairCloseHalfStrengthen (renewalSmallNext ring)
      (SmallCleanRFoldOnGuard ring)
      (SmallCleanRFoldOnGuard ring)
      (SmallCleanDigit ring) (smallRepairDigitHalf n)
      (fun r hr => hr)
      (fun r hr e => ⟨smallRepairGuardStep ring hn hsmall r hr.1 e,
        hp.2.2.1 r hr.1 hr.2 e⟩)
      hdigit
  have hD : BankRepairHalfStage (renewalSmallNext ring)
      (SmallCleanRFoldOnGuard ring)
      (SmallCleanDBarredOnGuard ring)
      (smallRepairDigitHalf n) :=
    bankRepairCloseHalfWeaken (renewalSmallNext ring)
      (SmallCleanRFoldOnGuard ring)
      (fun r => SmallCleanRFoldOnGuard ring r ∧ SmallCleanDigit ring r)
      (SmallCleanDBarredOnGuard ring) (smallRepairDigitHalf n)
      (fun r hr => ⟨hr.1.1, hr.1.2, hr.2⟩) hDzero
  have hDebtZero : BankRepairHalfStage (renewalSmallNext ring)
      (SmallCleanDBarredOnGuard ring)
      (fun r => SmallCleanDBarredOnGuard ring r ∧
        RepairDebtZero smallRepairView r) 1 :=
    bankRepairCloseHalfStrengthen (renewalSmallNext ring)
      (SmallCleanDBarredOnGuard ring)
      (SmallCleanDBarredOnGuard ring)
      (RepairDebtZero smallRepairView) 1
      (fun r hr => hr)
      (fun r hr e => ⟨smallRepairGuardStep ring hn hsmall r hr.1 e,
        hp.2.2.2.1 r hr.1 hr.2 e⟩)
      hdebt
  have hDebt : BankRepairHalfStage (renewalSmallNext ring)
      (SmallCleanDBarredOnGuard ring)
      (SmallCleanDebtClearedOnGuard ring) 1 :=
    bankRepairCloseHalfWeaken (renewalSmallNext ring)
      (SmallCleanDBarredOnGuard ring)
      (fun r => SmallCleanDBarredOnGuard ring r ∧
        RepairDebtZero smallRepairView r)
      (SmallCleanDebtClearedOnGuard ring) 1
      (fun r hr => ⟨hr.1.1, hr.1.2, hr.2⟩) hDebtZero
  have hRequestZero : BankRepairHalfStage (renewalSmallNext ring)
      (SmallCleanDebtClearedOnGuard ring)
      (fun r => SmallCleanDebtClearedOnGuard ring r ∧
        RepairRequestZero smallRepairView r) 2 :=
    bankRepairCloseHalfStrengthen (renewalSmallNext ring)
      (SmallCleanDebtClearedOnGuard ring)
      (SmallCleanDebtClearedOnGuard ring)
      (RepairRequestZero smallRepairView) 2
      (fun r hr => hr)
      (fun r hr e => ⟨smallRepairGuardStep ring hn hsmall r hr.1 e,
        hp.2.2.2.2 r hr.1 hr.2 e⟩)
      hrequest
  have hRequest : BankRepairHalfStage (renewalSmallNext ring)
      (SmallCleanDebtClearedOnGuard ring)
      (SmallCleanRequestsQuiet ring) 2 :=
    bankRepairCloseHalfWeaken (renewalSmallNext ring)
      (SmallCleanDebtClearedOnGuard ring)
      (fun r => SmallCleanDebtClearedOnGuard ring r ∧
        RepairRequestZero smallRepairView r)
      (SmallCleanRequestsQuiet ring) 2
      (fun r hr => ⟨hr.1.2, hr.2⟩) hRequestZero
  have hAfterRequest := bankRepairCloseHalfCompose
    (renewalSmallNext ring) (SmallCleanDebtClearedOnGuard ring)
    (SmallCleanRequestsQuiet ring) (smallCleanStop ring)
    2 0 hRequest (smallCleanStopStage ring hn).2
  have hAfterDebt := bankRepairCloseHalfCompose
    (renewalSmallNext ring) (SmallCleanDBarredOnGuard ring)
    (SmallCleanDebtClearedOnGuard ring) (smallCleanStop ring)
    1 (2 + 0) hDebt hAfterRequest
  have hAfterDigit := bankRepairCloseHalfCompose
    (renewalSmallNext ring) (SmallCleanRFoldOnGuard ring)
    (SmallCleanDBarredOnGuard ring) (smallCleanStop ring)
    (smallRepairDigitHalf n) (1 + (2 + 0)) hD hAfterDebt
  have hAfterReader := bankRepairCloseHalfCompose
    (renewalSmallNext ring) (SmallCleanWAcceptedOnGuard ring)
    (SmallCleanRFoldOnGuard ring) (smallCleanStop ring)
    (2 * smallRepairWidth n)
    (smallRepairDigitHalf n + (1 + (2 + 0)))
    hR hAfterDigit
  have hAll := bankRepairCloseHalfCompose
    (renewalSmallNext ring) (SmallPreparedAtSomeRoot ring)
    (SmallCleanWAcceptedOnGuard ring) (smallCleanStop ring)
    (2 * (440 * smallRepairWidth n + 275))
    (2 * smallRepairWidth n +
      (smallRepairDigitHalf n + (1 + (2 + 0))))
    hW hAfterReader
  intro r hr
  apply (UniformFirstHit.expectedHittingTimeAtMost_iff_cost
    (renewalSmallNext ring) (smallCleanStop ring)
    (by omega : 0 < n) r
    (headlineReferenceFinishRate (ceilLogTwo n) * n ^ 2)).2
  intro T
  have hcost := hAll r hr T
  rw [smallRepairHalfRate hn hsmall] at hcost
  have hscale :
      n ^ T *
        (2 * headlineReferenceFinishRate (ceilLogTwo n) * n ^ 2) =
      2 * (n ^ T *
        (headlineReferenceFinishRate (ceilLogTwo n) * n ^ 2)) := by
    simp only [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
  rw [hscale] at hcost
  omega

end L3.SmallFinishClean

#print axioms L3.SmallFinishClean.smallCleanWordStepOnGuard
#print axioms L3.SmallFinishClean.smallCleanReaderStepOnGuard
#print axioms L3.SmallFinishClean.smallCleanDigitStepOnGuard
#print axioms L3.SmallFinishClean.smallCleanDebtZeroStep
#print axioms L3.SmallFinishClean.smallCleanReceiptPreservationOnGuard
#print axioms L3.SmallFinishClean.smallCleanRequestsQuietStop
#print axioms L3.SmallFinishClean.smallCleanStopStage
#print axioms L3.SmallFinishClean.smallCleanWordCostProjection
#print axioms L3.SmallFinishClean.smallCleanWordHalfStage
#print axioms L3.SmallFinishClean.smallCleanWAcceptedOnGuardHalfStage
#print axioms L3.SmallFinishClean.smallCleanReaderInitializesAtWord
#print axioms L3.SmallFinishClean.smallCleanReaderVisibleRun
#print axioms L3.SmallFinishClean.smallCleanReaderSelectedReadFixed
#print axioms L3.SmallFinishClean.smallCleanReaderOfRetiredFrom
#print axioms L3.SmallFinishClean.smallCleanReaderHalfStageOfRetirementAndFold
#print axioms L3.SmallFinishClean.smallCleanFinishReferenceOfStages
