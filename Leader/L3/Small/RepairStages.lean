import Leader.L3.Small.FinishRepair
import Leader.L3.ClosureFull

/-!
SMALL repair stages on the ORIGINAL masked renewalSmallNext.

The five preservation statements proved below are restricted to the
grant-free, seen-complete, rooted suffix. In particular they
do NOT inhabit SmallRepairReceiptPreservation, which quantifies over
all reference states, including states with unrestrained old grants.

The W/R producers have exactly two remaining families of obligations:
the projected hard-word first-hit estimate (repair.tex, generated
recurrence pass, lines 906--1097), and the physical resident-reader
retirement plus five-fold terminal correctness (lines 1098--1118).
No BANK-band width identity or BANK-specific memory is assumed.
-/

namespace L3.SmallRepairStages

open L3
open L3.HeadlineRenewal
open L3.SmallRenewal
open L3.SmallCandidatePreparation
open L3.SmallFinishRepair
open L3.RenewalReferenceClock
open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree
open Classical

set_option autoImplicit false
set_option Elab.async false

/-! The guard is an already proved physical invariant, not a
new persistent counter or an unmasked substitute successor. -/

abbrev SmallRepairGuard {n : Nat}
    (ring : DirectedRing n) : RenewalSmallReference n → Prop :=
  smallReferenceGrantFreeRootedSeen ring

theorem smallRepairGuardFromPrepared {n : Nat}
    (ring : DirectedRing n) (r : RenewalSmallReference n)
    (hr : SmallPreparedAtSomeRoot ring r) :
    SmallRepairGuard ring r := by
  obtain ⟨root, hfixed, _⟩ := hr
  exact hfixed.1

theorem smallRepairGuardStep {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hsmall : (compileAdvice (ceilLogTwo n)).useSmall = true)
    (r : RenewalSmallReference n)
    (hr : SmallRepairGuard ring r) (e : Fin n) :
    SmallRepairGuard ring (renewalSmallNext ring r e) := by
  exact smallReferenceGrantFreeClosed ring hn hsmall r hr e

theorem smallRepairOldNoFire {n : Nat}
    (ring : DirectedRing n) (r : RenewalSmallReference n)
    (hr : SmallRepairGuard ring r) (e : Fin n) :
    oldFire (r.1 e) (r.1 (ring.rightNeighbor e)) = none := by
  have hf := native_lift_no_fire_of_pair_grant_free
    ring r.1 e (hr.2.2 e) (hr.2.2 (ring.rightNeighbor e))
  change oldFire (r.1 e) (r.1 (ring.rightNeighbor e)) = none at hf
  exact hf

/-! This projection-frame proof is the generic part of
bankRepairMaskedReaderProjection / bankWordMaskedFrame.
No BANK selector, BANK time stamp or compiler-band premise occurs. -/

private theorem smallRepairMaskedProjection {n : Nat} {A : Type}
    (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (e : Fin n) (suppress : Bool)
    (project : Agent (compileAdvice (ceilLogTwo n)) → A)
    (hpair : ∀ (x y : Agent (compileAdvice (ceilLogTwo n)))
      (b : Bool),
      project (renewalMaskedPair
        (compileAdvice (ceilLogTwo n)) b x y).1 =
          project (transition (compileAdvice (ceilLogTwo n)) x y).1 ∧
      project (renewalMaskedPair
        (compileAdvice (ceilLogTwo n)) b x y).2 =
          project (transition (compileAdvice (ceilLogTwo n)) x y).2) :
    (fun i => project (renewalMaskedStep ring C e suppress i)) =
      (fun i => project (headlinePhysicalNext ring C e i)) := by
  have hrow :
      (fun i => project (renewalMaskedStep ring C e suppress i)) =
        (fun i => project (renewalMaskedStep ring C e false i)) := by
    funext i
    change project
      (if i = e then
        (renewalMaskedPair (compileAdvice (ceilLogTwo n))
          suppress (C e) (C (ring.rightNeighbor e))).1
      else if i = ring.rightNeighbor e then
        (renewalMaskedPair (compileAdvice (ceilLogTwo n))
          suppress (C e) (C (ring.rightNeighbor e))).2
      else C i) =
      project
      (if i = e then
        (renewalMaskedPair (compileAdvice (ceilLogTwo n))
          false (C e) (C (ring.rightNeighbor e))).1
      else if i = ring.rightNeighbor e then
        (renewalMaskedPair (compileAdvice (ceilLogTwo n))
          false (C e) (C (ring.rightNeighbor e))).2
      else C i)
    by_cases hi : i = e
    · simp only [if_pos hi]
      exact (hpair (C e) (C (ring.rightNeighbor e)) suppress).1.trans
        (hpair (C e) (C (ring.rightNeighbor e)) false).1.symm
    · simp only [if_neg hi]
      by_cases hj : i = ring.rightNeighbor e
      · subst hj
        simp only [ite_true]
        exact (hpair (C e) (C (ring.rightNeighbor e)) suppress).2.trans
          (hpair (C e) (C (ring.rightNeighbor e)) false).2.symm
      · simp [hj]
  exact hrow.trans (congrArg
    (fun X : HeadlineConfiguration n => fun i => project (X i))
    (renewalMaskedStepOff ring C e))

theorem smallRepairWordMaskedStep {n : Nat}
    (ring : DirectedRing n) (r : RenewalSmallReference n)
    (e : Fin n) :
    piW (renewalSmallNext ring r e).1 =
      piW (headlinePhysicalNext ring r.1 e) := by
  change (fun i => ProjW.ofAgent
    (renewalMaskedStep ring r.1 e
      (renewalSmallCut ring r.1 r.2 e) i)) =
    (fun i => ProjW.ofAgent (headlinePhysicalNext ring r.1 e i))
  exact smallRepairMaskedProjection ring r.1 e
    (renewalSmallCut ring r.1 r.2 e) ProjW.ofAgent
    (by intro x y b; cases b <;> exact ⟨rfl, rfl⟩)

theorem smallRepairReaderMaskedStep {n : Nat}
    (ring : DirectedRing n) (r : RenewalSmallReference n)
    (e : Fin n) :
    piR (renewalSmallNext ring r e).1 =
      piR (headlinePhysicalNext ring r.1 e) := by
  change (fun i => ProjR.ofAgent
    (renewalMaskedStep ring r.1 e
      (renewalSmallCut ring r.1 r.2 e) i)) =
    (fun i => ProjR.ofAgent (headlinePhysicalNext ring r.1 e i))
  exact smallRepairMaskedProjection ring r.1 e
    (renewalSmallCut ring r.1 r.2 e) ProjR.ofAgent
    (by intro x y b; cases b <;> exact ⟨rfl, rfl⟩)

theorem smallRepairDigitMaskedStep {n : Nat}
    (ring : DirectedRing n) (r : RenewalSmallReference n)
    (e : Fin n) :
    piD (renewalSmallNext ring r e).1 =
      piD (headlinePhysicalNext ring r.1 e) := by
  change (fun i => ProjD.ofAgent
    (renewalMaskedStep ring r.1 e
      (renewalSmallCut ring r.1 r.2 e) i)) =
    (fun i => ProjD.ofAgent (headlinePhysicalNext ring r.1 e i))
  exact smallRepairMaskedProjection ring r.1 e
    (renewalSmallCut ring r.1 r.2 e) ProjD.ofAgent
    (by intro x y b; cases b <;> exact ⟨rfl, rfl⟩)

theorem smallRepairWordPhiStep {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (r : RenewalSmallReference n)
    (hr : SmallRepairGuard ring r) (e : Fin n) :
    piW (renewalSmallNext ring r e).1 =
      phiW ring (piW r.1) e := by
  have hphysical := stepW_noFire (q := ceilLogTwo n)
    hn ring r.1 e (smallRepairOldNoFire ring r hr e)
  change piW (headlinePhysicalNext ring r.1 e) =
    phiW ring (piW r.1) e at hphysical
  exact (smallRepairWordMaskedStep ring r e).trans hphysical

theorem smallRepairReaderPhiStep {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (r : RenewalSmallReference n)
    (hr : SmallRepairGuard ring r) (e : Fin n) :
    piR (renewalSmallNext ring r e).1 =
      phiR ring (piR r.1) e := by
  have hphysical := stepR_noFire (q := ceilLogTwo n)
    hn ring r.1 e (smallRepairOldNoFire ring r hr e)
  change piR (headlinePhysicalNext ring r.1 e) =
    phiR ring (piR r.1) e at hphysical
  exact (smallRepairReaderMaskedStep ring r e).trans hphysical

theorem smallRepairDigitPhiStep {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (r : RenewalSmallReference n)
    (hr : SmallRepairGuard ring r) (e : Fin n) :
    piD (renewalSmallNext ring r e).1 =
      phiD ring (piD r.1) e := by
  have hphysical := stepD_noFire (q := ceilLogTwo n)
    hn ring r.1 e (smallRepairOldNoFire ring r hr e)
  change piD (headlinePhysicalNext ring r.1 e) =
    phiD ring (piD r.1) e at hphysical
  exact (smallRepairDigitMaskedStep ring r e).trans hphysical

/-! Five factor-by-factor SMALL suffix closures. The core
uses the native E-sector and birth-free candidate history.
W/R/D reuse exactly the existing projected acceptance-step lemmas. -/

theorem smallRepairCoreStepOnGuard {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (r : RenewalSmallReference n)
    (hr : SmallRepairGuard ring r)
    (hc : SmallRepairCore ring r) (e : Fin n) :
    SmallRepairCore ring (renewalSmallNext ring r e) := by
  have hnative := smallReferenceGrantFreeNativeStep
    ring (by omega : 3 ≤ n) r hr e
  change nativeProjection (renewalSmallNext ring r e).1 =
    nativeE ring (nativeProjection r.1) e at hnative
  have hsector := nativeE_preserves_singleton_C_native
    hn ring (nativeProjection r.1) e ⟨hc.1.1, hc.1.2.2⟩
  constructor
  · change OneNativeLeader (nativeProjection
        (renewalSmallNext ring r e).1) ∧
      Protected ring (nativeProjection
        (renewalSmallNext ring r e).1) ∧
      C_native ring (nativeProjection
        (renewalSmallNext ring r e).1)
    rw [hnative]
    exact ⟨hsector.1, hsector.2.1.1, hsector.2⟩
  · change H_cand ring
      (smallCandidateView (renewalSmallNext ring r e))
    rw [smallCandidateStep ring hn r hr e]
    exact H_cand_birthFree_step ring (smallCandidateView r) e hc.2

theorem smallRepairWordStepOnGuard {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (r : RenewalSmallReference n)
    (hr : SmallRepairGuard ring r)
    (hw : SmallRepairWord ring r) (e : Fin n) :
    SmallRepairWord ring (renewalSmallNext ring r e) := by
  change AcceptedReceipts.AcceptedWord ring
    (BlockA.wordT ring) (BlockA.wordValidated ring)
    (piW r.1) at hw
  change AcceptedReceipts.AcceptedWord ring
    (BlockA.wordT ring) (BlockA.wordValidated ring)
    (piW (renewalSmallNext ring r e).1)
  rw [smallRepairWordPhiStep ring hn r hr e]
  exact AcceptedReceipts.accepted_word_phi_step
    ring (piW r.1) e hw

theorem smallRepairReaderStepOnGuard {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (r : RenewalSmallReference n)
    (hr : SmallRepairGuard ring r)
    (hreader : SmallRepairReader ring r) (e : Fin n) :
    SmallRepairReader ring (renewalSmallNext ring r e) := by
  change AcceptedReceipts.AcceptedReader ring
    (AcceptedReceipts.AcceptedWord ring
      (BlockA.wordT ring) (BlockA.wordValidated ring))
    (Closure.readerFoldValid (ceilLogTwo n) n)
    (piR r.1) at hreader
  change AcceptedReceipts.AcceptedReader ring
    (AcceptedReceipts.AcceptedWord ring
      (BlockA.wordT ring) (BlockA.wordValidated ring))
    (Closure.readerFoldValid (ceilLogTwo n) n)
    (piR (renewalSmallNext ring r e).1)
  rw [smallRepairReaderPhiStep ring hn r hr e]
  exact Closure.readerGeneratedPhiStep hn
    (ClosureFull.adviceWidthPositive (ceilLogTwo n))
    ring
    (AcceptedReceipts.AcceptedWord ring
      (BlockA.wordT ring) (BlockA.wordValidated ring))
    (piR r.1) e hreader

theorem smallRepairDigitStepOnGuard {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (r : RenewalSmallReference n)
    (hr : SmallRepairGuard ring r)
    (hdigit : SmallRepairDigit ring r) (e : Fin n) :
    SmallRepairDigit ring (renewalSmallNext ring r e) := by
  change AcceptedReceipts.BarredDigitClass ring
    (AcceptedReceipts.AcceptedWordAtRoot ring
      (BlockA.wordT ring) (BlockA.wordValidated ring))
    (piD r.1) at hdigit
  change AcceptedReceipts.BarredDigitClass ring
    (AcceptedReceipts.AcceptedWordAtRoot ring
      (BlockA.wordT ring) (BlockA.wordValidated ring))
    (piD (renewalSmallNext ring r e).1)
  rw [smallRepairDigitPhiStep ring hn r hr e]
  exact Closure.digitGeneratedPhiStep hn ring
    (piD r.1) e hdigit

/-! The DCC debt-only row needs the genuine QReader and QDigit
consequences; it does NOT need an OLD request-zero premise.
The pair mask changes req/grant but neither EU nor ED. -/

theorem smallRepairDebtZeroStep {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (r : RenewalSmallReference n)
    (hreader : SmallRepairReader ring r)
    (hdigit : SmallRepairDigit ring r)
    (hdebt : RepairDebtZero smallRepairView r)
    (e : Fin n) :
    RepairDebtZero smallRepairView (renewalSmallNext ring r e) := by
  have hQReader : AcceptedReceipts.QReader ring (piR r.1) :=
    AcceptedReceipts.accepted_reader_qreader ring
      (AcceptedReceipts.AcceptedWord ring
        (BlockA.wordT ring) (BlockA.wordValidated ring))
      (Closure.readerFoldValid (ceilLogTwo n) n)
      (piR r.1) hreader
  have hQDigit : AcceptedReceipts.QDigit ring (piD r.1) :=
    AcceptedReceipts.barred_digit_qdigit ring
      (AcceptedReceipts.AcceptedWordAtRoot ring
        (BlockA.wordT ring) (BlockA.wordValidated ring))
      (piD r.1) hdigit
  have hev := Closure.certificateEventQuietFromSafe
    hn ring r.1 e hQReader hQDigit
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

/-! The exact five SMALL clauses requested by the repair ledger,
but correctly guarded by a reachable suffix invariant. -/

def SmallRepairReceiptPreservationOnGuard {n : Nat}
    (ring : DirectedRing n) : Prop :=
  (∀ r, SmallRepairGuard ring r → SmallRepairCore ring r →
    ∀ e, SmallRepairCore ring (renewalSmallNext ring r e)) ∧
  (∀ r, SmallRepairGuard ring r → SmallRepairWAccepted ring r →
    ∀ e, SmallRepairWAccepted ring (renewalSmallNext ring r e)) ∧
  (∀ r, SmallRepairGuard ring r → SmallRepairRFoldEstablished ring r →
    ∀ e, SmallRepairRFoldEstablished ring
      (renewalSmallNext ring r e)) ∧
  (∀ r, SmallRepairGuard ring r → SmallRepairDBarred ring r →
    ∀ e, SmallRepairDBarred ring (renewalSmallNext ring r e)) ∧
  (∀ r, SmallRepairGuard ring r → SmallRepairDebtCleared ring r →
    ∀ e, SmallRepairDebtCleared ring (renewalSmallNext ring r e))

theorem smallRepairReceiptPreservationOnGuardProved {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n) :
    SmallRepairReceiptPreservationOnGuard ring := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro r hg hc e
    exact smallRepairCoreStepOnGuard ring hn r hg hc e
  · intro r hg hW e
    exact ⟨smallRepairCoreStepOnGuard ring hn r hg hW.1 e,
      smallRepairWordStepOnGuard ring (by omega : 2 ≤ n)
        r hg hW.2 e⟩
  · intro r hg hR e
    exact ⟨⟨smallRepairCoreStepOnGuard ring hn r hg hR.1.1 e,
      smallRepairWordStepOnGuard ring (by omega : 2 ≤ n)
        r hg hR.1.2 e⟩,
      smallRepairReaderStepOnGuard ring (by omega : 2 ≤ n)
        r hg hR.2 e⟩
  · intro r hg hD e
    exact ⟨⟨⟨smallRepairCoreStepOnGuard ring hn r hg
      hD.1.1.1 e,
      smallRepairWordStepOnGuard ring (by omega : 2 ≤ n)
        r hg hD.1.1.2 e⟩,
      smallRepairReaderStepOnGuard ring (by omega : 2 ≤ n)
        r hg hD.1.2 e⟩,
      smallRepairDigitStepOnGuard ring (by omega : 2 ≤ n)
        r hg hD.2 e⟩
  · intro r hg hDebt e
    exact ⟨⟨⟨⟨smallRepairCoreStepOnGuard ring hn r hg
      hDebt.1.1.1.1 e,
      smallRepairWordStepOnGuard ring (by omega : 2 ≤ n)
        r hg hDebt.1.1.1.2 e⟩,
      smallRepairReaderStepOnGuard ring (by omega : 2 ≤ n)
        r hg hDebt.1.1.2 e⟩,
      smallRepairDigitStepOnGuard ring (by omega : 2 ≤ n)
        r hg hDebt.1.2 e⟩,
      smallRepairDebtZeroStep ring (by omega : 2 ≤ n)
        r hDebt.1.1.2 hDebt.1.2 hDebt.2 e⟩

private theorem smallRepairRunOnGuard {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hsmall : (compileAdvice (ceilLogTwo n)).useSmall = true)
    (P : RenewalSmallReference n → Prop)
    (hstep : ∀ r, SmallRepairGuard ring r → P r →
      ∀ e, P (renewalSmallNext ring r e)) :
    ∀ (word : List (Fin n)) (r : RenewalSmallReference n),
      SmallRepairGuard ring r → P r →
        P (word.foldl (renewalSmallNext ring) r) := by
  intro word
  induction word with
  | nil =>
      intro r _ hp
      exact hp
  | cons e tail ih =>
      intro r hg hp
      change P (tail.foldl (renewalSmallNext ring)
        (renewalSmallNext ring r e))
      exact ih (renewalSmallNext ring r e)
        (smallRepairGuardStep ring hn hsmall r hg e)
        (hstep r hg hp e)

theorem smallRepairReceiptSuffixFromGuard {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hsmall : (compileAdvice (ceilLogTwo n)).useSmall = true)
    (r : RenewalSmallReference n)
    (hg : SmallRepairGuard ring r)
    (word : List (Fin n)) :
    (SmallRepairCore ring r →
      SmallRepairCore ring (word.foldl (renewalSmallNext ring) r)) ∧
    (SmallRepairWAccepted ring r →
      SmallRepairWAccepted ring
        (word.foldl (renewalSmallNext ring) r)) ∧
    (SmallRepairRFoldEstablished ring r →
      SmallRepairRFoldEstablished ring
        (word.foldl (renewalSmallNext ring) r)) ∧
    (SmallRepairDBarred ring r →
      SmallRepairDBarred ring
        (word.foldl (renewalSmallNext ring) r)) ∧
    (SmallRepairDebtCleared ring r →
      SmallRepairDebtCleared ring
        (word.foldl (renewalSmallNext ring) r)) := by
  have hp := smallRepairReceiptPreservationOnGuardProved ring hn
  exact ⟨
    (fun hc => smallRepairRunOnGuard ring hn hsmall
      (SmallRepairCore ring) hp.1 word r hg hc),
    (fun hw => smallRepairRunOnGuard ring hn hsmall
      (SmallRepairWAccepted ring) hp.2.1 word r hg hw),
    (fun hr => smallRepairRunOnGuard ring hn hsmall
      (SmallRepairRFoldEstablished ring) hp.2.2.1 word r hg hr),
    (fun hd => smallRepairRunOnGuard ring hn hsmall
      (SmallRepairDBarred ring) hp.2.2.2.1 word r hg hd),
    (fun hb => smallRepairRunOnGuard ring hn hsmall
      (SmallRepairDebtCleared ring) hp.2.2.2.2 word r hg hb)⟩

theorem smallRepairReceiptSuffixFromPrepared {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hsmall : (compileAdvice (ceilLogTwo n)).useSmall = true)
    (r : RenewalSmallReference n)
    (hr : SmallPreparedAtSomeRoot ring r)
    (word : List (Fin n)) :
    (SmallRepairCore ring r →
      SmallRepairCore ring (word.foldl (renewalSmallNext ring) r)) ∧
    (SmallRepairWAccepted ring r →
      SmallRepairWAccepted ring
        (word.foldl (renewalSmallNext ring) r)) ∧
    (SmallRepairRFoldEstablished ring r →
      SmallRepairRFoldEstablished ring
        (word.foldl (renewalSmallNext ring) r)) ∧
    (SmallRepairDBarred ring r →
      SmallRepairDBarred ring
        (word.foldl (renewalSmallNext ring) r)) ∧
    (SmallRepairDebtCleared ring r →
      SmallRepairDebtCleared ring
        (word.foldl (renewalSmallNext ring) r)) := by
  exact smallRepairReceiptSuffixFromGuard ring hn hsmall r
    (smallRepairGuardFromPrepared ring r hr) word

/-! W: the only missing producer is the actual projected
hard-accepted first-hit clock. This is precisely the BANK
BankWordProjectedClock interface with the SMALL width and start.
The accepted projected target and all abstract W rows are shared. -/

def SmallWordProjectedTarget {n : Nat}
    (ring : DirectedRing n)
    (p : Fin n → ProjW (compileAdvice (ceilLogTwo n))) : Prop :=
  AcceptedReceipts.AcceptedWord ring
    (BlockA.wordT ring) (BlockA.wordValidated ring) p

def SmallWordProjectedClock {n : Nat}
    (ring : DirectedRing n) : Prop :=
  ∀ r : RenewalSmallReference n,
    SmallPreparedAtSomeRoot ring r →
    ∀ T : Nat,
      costNumerator (phiW ring)
        (SmallWordProjectedTarget ring) (piW r.1) T ≤
      n ^ T * ((440 * smallRepairWidth n + 275) * n ^ 2)

private theorem smallRepairCostProjection
    {n : Nat} {S P : Type}
    (next : S → Fin n → S) (phi : P → Fin n → P)
    (view : S → P) (guard : S → Prop) (target : P → Prop)
    (hstep : ∀ z, guard z → ∀ e,
      view (next z e) = phi (view z) e)
    (hclosed : ∀ z, guard z → ∀ e, guard (next z e)) :
    ∀ T z, guard z →
      costNumerator next (fun y => target (view y)) z T =
        costNumerator phi target (view z) T := by
  intro T
  induction T with
  | zero =>
      intro z _
      simp only [costNumerator_zero]
  | succ T ih =>
      intro z hz
      by_cases ht : target (view z)
      · rw [costNumerator_terminal next
          (fun y => target (view y)) z ht (T + 1),
          costNumerator_terminal phi target (view z) ht (T + 1)]
      · rw [costNumerator_succ next
          (fun y => target (view y)) z ht T,
          costNumerator_succ phi target (view z) ht T]
        congr 1
        exact ofFn_sum_eq _ _ (fun e => by
          have hh := ih (next z e) (hclosed z hz e)
          rw [hstep z hz e] at hh
          exact hh)

theorem smallRepairWordReferenceCostProjection {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hsmall : (compileAdvice (ceilLogTwo n)).useSmall = true)
    (T : Nat) (r : RenewalSmallReference n)
    (hr : SmallRepairGuard ring r) :
    costNumerator (renewalSmallNext ring)
      (SmallRepairWord ring) r T =
    costNumerator (phiW ring)
      (SmallWordProjectedTarget ring) (piW r.1) T := by
  exact smallRepairCostProjection
    (renewalSmallNext ring) (phiW ring)
    (fun z : RenewalSmallReference n => piW z.1)
    (SmallRepairGuard ring) (SmallWordProjectedTarget ring)
    (fun z hz e => smallRepairWordPhiStep ring
      (by omega : 2 ≤ n) z hz e)
    (smallRepairGuardStep ring hn hsmall)
    T r hr

theorem smallRepairWordStageOfProjectedClock {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hsmall : (compileAdvice (ceilLogTwo n)).useSmall = true)
    (hclock : SmallWordProjectedClock ring) :
    SmallRepairWordStage ring := by
  constructor
  · intro r hr
    apply (UniformFirstHit.expectedHittingTimeAtMost_iff_cost
      (renewalSmallNext ring) (SmallRepairWord ring)
      (by omega : 0 < n) r
      ((440 * smallRepairWidth n + 275) * n ^ 2)).2
    intro T
    rw [smallRepairWordReferenceCostProjection ring hn hsmall
      T r (smallRepairGuardFromPrepared ring r hr)]
    exact hclock r hr T
  · intro r hr T
    have hprojection := smallRepairWordReferenceCostProjection
      ring hn hsmall T r (smallRepairGuardFromPrepared ring r hr)
    have hcost := hclock r hr T
    rw [← hprojection] at hcost
    have hdouble := Nat.mul_le_mul_left 2 hcost
    have hfactor :
        2 * (n ^ T * ((440 * smallRepairWidth n + 275) * n ^ 2)) =
        n ^ T * ((2 * (440 * smallRepairWidth n + 275)) *
          n ^ 2) := by
      simp only [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
    rw [hfactor] at hdouble
    exact hdouble

/-! R: one actual W-endpoint observer, not a reset raw-token
process. The retired-from endpoint carries a genuine SAME-word
phiR trace. E.G19 and E.G22 below remain separate missing Props,
just as BankRepairResidentRetirementClock and
BankRepairReaderFoldSound do on BANK. -/

def smallRepairReaderInitialControl {n : Nat}
    (ring : DirectedRing n)
    (r : RenewalSmallReference n) :
    BlockA.ReaderControl n (compileAdvice (ceilLogTwo n)) :=
  { phase := .retire
    tags := fun i =>
      if (piR r.1 i).rawTok.isSome = true
        then .inherited i else .empty
    inheritedNames := fun i => (piR r.1 i).rawTok.isSome }

theorem smallRepairReaderInitializesAtW {n : Nat}
    (ring : DirectedRing n) (r : RenewalSmallReference n)
    (hW : SmallRepairWAccepted ring r) :
    BlockA.initializesReader
      (AcceptedReceipts.AcceptedWord ring
        (BlockA.wordT ring) (BlockA.wordValidated ring))
      (piR r.1)
      (.live (piR r.1)
        (smallRepairReaderInitialControl ring r)) := by
  constructor
  · change SmallRepairWord ring r
    exact hW.2
  · refine ⟨smallRepairReaderInitialControl ring r,
        rfl, rfl, ?_⟩
    intro i
    by_cases hi : (piR r.1 i).rawTok.isSome = true
    · simp [smallRepairReaderInitialControl, hi]
    · simp [smallRepairReaderInitialControl, hi]

def SmallReaderRetiredFrom {n : Nat}
    (ring : DirectedRing n)
    (start finish : RenewalSmallReference n) : Prop :=
  ∃ (word : List (Fin n))
    (initial : BlockA.Decoration
      (Fin n → ProjR (compileAdvice (ceilLogTwo n)))
      (BlockA.ReaderControl n (compileAdvice (ceilLogTwo n))))
    (control : BlockA.ReaderControl n
      (compileAdvice (ceilLogTwo n))),
    finish = word.foldl (renewalSmallNext ring) start ∧
    BlockA.initializesReader
      (AcceptedReceipts.AcceptedWord ring
        (BlockA.wordT ring) (BlockA.wordValidated ring))
      (piR start.1) initial ∧
    BlockA.Run ring (phiR ring)
      (BlockA.readerControlNext ring)
      (piR start.1) initial word
      (piR finish.1)
      (.live (piR finish.1) control) ∧
    control.phase = .done ∧
    (∀ name : Fin n, control.inheritedNames name = false)

/-- Open E.G19, repair.tex lines 1098--1109; owner must
retire every resident raw token, even the one born on the
entering W edge. This half-unit clock is on the original
renewalSmallNext, not a fresh phiR chain. -/
def SmallResidentRetirementClock {n : Nat}
    (ring : DirectedRing n) : Prop :=
  ∀ start : RenewalSmallReference n,
    SmallRepairWAccepted ring start →
    ∀ T : Nat,
      2 * costNumerator (renewalSmallNext ring)
        (SmallReaderRetiredFrom ring start) start T ≤
      n ^ T * ((2 * smallRepairWidth n) * n ^ 2)

/-- Open E.G22, repair.tex lines 1109--1118: the five
sampled accumulators, root-touch exemption, silent terminal
comparison and identity provenance at the SAME done cut. -/
def SmallReaderFoldSound {n : Nat}
    (ring : DirectedRing n) : Prop :=
  ∀ (start finish : RenewalSmallReference n)
    (word : List (Fin n))
    (initial : BlockA.Decoration
      (Fin n → ProjR (compileAdvice (ceilLogTwo n)))
      (BlockA.ReaderControl n (compileAdvice (ceilLogTwo n))))
    (control : BlockA.ReaderControl n
      (compileAdvice (ceilLogTwo n))),
    SmallRepairWAccepted ring start →
    finish = word.foldl (renewalSmallNext ring) start →
    BlockA.initializesReader
      (AcceptedReceipts.AcceptedWord ring
        (BlockA.wordT ring) (BlockA.wordValidated ring))
      (piR start.1) initial →
    BlockA.Run ring (phiR ring)
      (BlockA.readerControlNext ring)
      (piR start.1) initial word
      (piR finish.1)
      (.live (piR finish.1) control) →
    control.phase = .done →
    (∀ name : Fin n, control.inheritedNames name = false) →
    BlockA.acceptsReader
      (Closure.readerFoldValid (ceilLogTwo n) n)
      (AcceptedReceipts.QReader ring)
      (piR finish.1)
      (.live (piR finish.1) control)

theorem smallRepairReaderOfRetiredFrom {n : Nat}
    (ring : DirectedRing n)
    (hfold : SmallReaderFoldSound ring)
    (start finish : RenewalSmallReference n)
    (hW : SmallRepairWAccepted ring start)
    (hret : SmallReaderRetiredFrom ring start finish) :
    SmallRepairReader ring finish := by
  rcases hret with
    ⟨word, initial, control, hactual, hinit, hrun,
      hdone, hnames⟩
  have hacc := hfold start finish word initial control
    hW hactual hinit hrun hdone hnames
  change AcceptedReceipts.AcceptedReader ring
    (AcceptedReceipts.AcceptedWord ring
      (BlockA.wordT ring) (BlockA.wordValidated ring))
    (Closure.readerFoldValid (ceilLogTwo n) n)
    (piR finish.1)
  exact ⟨piR start.1, initial, word,
    .live (piR finish.1) control,
    hinit, hrun, hacc⟩

theorem smallRepairReaderStageOfRetirementAndFold {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hclock : SmallResidentRetirementClock ring)
    (hfold : SmallReaderFoldSound ring) :
    SmallRepairReaderStage ring := by
  have hhalf : BankRepairHalfStage
      (renewalSmallNext ring)
      (SmallRepairWAccepted ring)
      (SmallRepairReader ring)
      (2 * smallRepairWidth n) := by
    intro start hW T
    have hmono :
        costNumerator (renewalSmallNext ring)
            (SmallRepairReader ring) start T ≤
          costNumerator (renewalSmallNext ring)
            (SmallReaderRetiredFrom ring start) start T :=
      Prob.costNumerator_target_mono
        (renewalSmallNext ring)
        (SmallReaderRetiredFrom ring start)
        (SmallRepairReader ring)
        (fun finish hret =>
          smallRepairReaderOfRetiredFrom ring hfold
            start finish hW hret) start T
    calc
      2 * costNumerator (renewalSmallNext ring)
          (SmallRepairReader ring) start T ≤
        2 * costNumerator (renewalSmallNext ring)
          (SmallReaderRetiredFrom ring start) start T :=
            Nat.mul_le_mul_left 2 hmono
      _ ≤ n ^ T * ((2 * smallRepairWidth n) * n ^ 2) :=
            hclock start hW T
  constructor
  · intro start hW
    apply (UniformFirstHit.expectedHittingTimeAtMost_iff_cost
      (renewalSmallNext ring)
      (SmallRepairReader ring)
      (by omega : 0 < n) start
      (smallRepairWidth n * n ^ 2)).2
    intro T
    have hcost := hhalf start hW T
    have hscale :
        n ^ T * ((2 * smallRepairWidth n) * n ^ 2) =
          2 * (n ^ T * (smallRepairWidth n * n ^ 2)) := by
      simp only [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
    rw [hscale] at hcost
    omega
  · exact hhalf

end L3.SmallRepairStages
#print axioms L3.SmallRepairStages.smallRepairGuardFromPrepared
#print axioms L3.SmallRepairStages.smallRepairGuardStep
#print axioms L3.SmallRepairStages.smallRepairOldNoFire
#print axioms L3.SmallRepairStages.smallRepairWordMaskedStep
#print axioms L3.SmallRepairStages.smallRepairReaderMaskedStep
#print axioms L3.SmallRepairStages.smallRepairDigitMaskedStep
#print axioms L3.SmallRepairStages.smallRepairWordPhiStep
#print axioms L3.SmallRepairStages.smallRepairReaderPhiStep
#print axioms L3.SmallRepairStages.smallRepairDigitPhiStep
#print axioms L3.SmallRepairStages.smallRepairCoreStepOnGuard
#print axioms L3.SmallRepairStages.smallRepairWordStepOnGuard
#print axioms L3.SmallRepairStages.smallRepairReaderStepOnGuard
#print axioms L3.SmallRepairStages.smallRepairDigitStepOnGuard
#print axioms L3.SmallRepairStages.smallRepairDebtZeroStep
#print axioms L3.SmallRepairStages.smallRepairReceiptPreservationOnGuardProved
#print axioms L3.SmallRepairStages.smallRepairReceiptSuffixFromGuard
#print axioms L3.SmallRepairStages.smallRepairReceiptSuffixFromPrepared
#print axioms L3.SmallRepairStages.smallRepairWordReferenceCostProjection
#print axioms L3.SmallRepairStages.smallRepairWordStageOfProjectedClock
#print axioms L3.SmallRepairStages.smallRepairReaderInitializesAtW
#print axioms L3.SmallRepairStages.smallRepairReaderOfRetiredFrom
#print axioms L3.SmallRepairStages.smallRepairReaderStageOfRetirementAndFold
