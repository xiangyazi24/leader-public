import Leader.L3.Bank.FinishRepair

/-!
BANK R-reader handoff after the actual accepted W cut.

This file does not replace the masked BANK
reference by an unmasked physical chain and does not claim a reader
retirement clock without its two named producer obligations.

The existing half-unit convention charges a rate of 2*s for the
ordinary s*n^2 bound, where s = ceilLogTwo (ceilLogTwo n).
-/

namespace L3.RenewalReferenceClock

open L3.HeadlineRenewal
open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree

set_option autoImplicit false
set_option Elab.async false

/-! ## The BANK reader width and physical masked projection -/

/-- On the BANK band q >= 80 the production reader sample count
is exactly s = ceilLogTwo q, rather than an arbitrary width. -/
theorem bankRepairReaderCompiledWidth {n : Nat}
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) :
    (compileAdvice (ceilLogTwo n)).t =
      ceilLogTwo (ceilLogTwo n) := by
  have hq := bankRepairBankBand hbank
  have hspec :
      ceilLogTwo n ≤ 2 ^ ceilLogTwo (ceilLogTwo n) :=
    (ceilLogTwo_spec (ceilLogTwo n) (by omega : 2 ≤ ceilLogTwo n)).2
  have hone : ceilLogTwo (ceilLogTwo n) ≠ 1 := by
    intro he
    rw [he] at hspec
    change ceilLogTwo n ≤ 2 at hspec
    omega
  have hlarge : ¬ ceilLogTwo n ≤ 32 := by omega
  change (if ceilLogTwo (ceilLogTwo n) = 1 then 2
    else if ceilLogTwo n ≤ 32 then finiteCertWidth (ceilLogTwo n)
    else ceilLogTwo (ceilLogTwo n)) = ceilLogTwo (ceilLogTwo n)
  simp only [if_neg hone, if_neg hlarge]

theorem bankRepairReaderCompiledWidthPos {n : Nat}
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) :
    0 < (compileAdvice (ceilLogTwo n)).t := by
  rw [bankRepairReaderCompiledWidth hbank]
  have hq := bankRepairBankBand hbank
  have hspec :
      ceilLogTwo n ≤ 2 ^ ceilLogTwo (ceilLogTwo n) :=
    (ceilLogTwo_spec (ceilLogTwo n) (by omega : 2 ≤ ceilLogTwo n)).2
  by_cases hz : ceilLogTwo (ceilLogTwo n) = 0
  · rw [hz] at hspec
    change ceilLogTwo n ≤ 1 at hspec
    omega
  · omega

/-- Suppressing fresh BANK request/grant output is invisible to
the actual projected R0/R1 reader fields, including old raw tokens. -/
private theorem bankRepairMaskedReaderPair
    (c : Compiled) (x y : Agent c) (suppress : Bool) :
    ProjR.ofAgent (renewalMaskedPair c suppress x y).1 =
      ProjR.ofAgent (transition c x y).1 ∧
    ProjR.ofAgent (renewalMaskedPair c suppress x y).2 =
      ProjR.ofAgent (transition c x y).2 := by
  cases suppress <;> exact ⟨rfl, rfl⟩

private theorem bankRepairMaskedWordPair
    (c : Compiled) (x y : Agent c) (suppress : Bool) :
    ProjW.ofAgent (renewalMaskedPair c suppress x y).1 =
      ProjW.ofAgent (transition c x y).1 ∧
    ProjW.ofAgent (renewalMaskedPair c suppress x y).2 =
      ProjW.ofAgent (transition c x y).2 := by
  cases suppress <;> exact ⟨rfl, rfl⟩

/-- Projection equality holds for either value of the mask,
without assuming an OLD no-FIRE edge. -/
private theorem bankRepairMaskedReaderProjection {n : Nat}
    (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (e : Fin n) (suppress : Bool) :
    piR (renewalMaskedStep ring C e suppress) =
      piR (headlinePhysicalNext ring C e) := by
  have hsame :
      piR (renewalMaskedStep ring C e suppress) =
        piR (renewalMaskedStep ring C e false) := by
    funext i
    change ProjR.ofAgent
      (if i = e then
        (renewalMaskedPair (compileAdvice (ceilLogTwo n))
          suppress (C e) (C (ring.rightNeighbor e))).1
      else if i = ring.rightNeighbor e then
        (renewalMaskedPair (compileAdvice (ceilLogTwo n))
          suppress (C e) (C (ring.rightNeighbor e))).2
      else C i) =
      ProjR.ofAgent
      (if i = e then
        (renewalMaskedPair (compileAdvice (ceilLogTwo n))
          false (C e) (C (ring.rightNeighbor e))).1
      else if i = ring.rightNeighbor e then
        (renewalMaskedPair (compileAdvice (ceilLogTwo n))
          false (C e) (C (ring.rightNeighbor e))).2
      else C i)
    by_cases he : i = e
    · simp only [if_pos he]
      exact (bankRepairMaskedReaderPair
        (compileAdvice (ceilLogTwo n))
        (C e) (C (ring.rightNeighbor e)) suppress).1
    · by_cases hj : i = ring.rightNeighbor e
      · exact (congrArg ProjR.ofAgent ((if_neg he).trans (if_pos hj))).trans
          ((bankRepairMaskedReaderPair
            (compileAdvice (ceilLogTwo n))
            (C e) (C (ring.rightNeighbor e)) suppress).2.trans
            (congrArg ProjR.ofAgent ((if_neg he).trans (if_pos hj))).symm)
      · exact congrArg ProjR.ofAgent
          (((if_neg he).trans (if_neg hj)).trans
            ((if_neg he).trans (if_neg hj)).symm)
  rw [renewalMaskedStepOff] at hsame
  exact hsame

private theorem bankRepairMaskedWordProjection {n : Nat}
    (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (e : Fin n) (suppress : Bool) :
    piW (renewalMaskedStep ring C e suppress) =
      piW (headlinePhysicalNext ring C e) := by
  have hsame :
      piW (renewalMaskedStep ring C e suppress) =
        piW (renewalMaskedStep ring C e false) := by
    funext i
    change ProjW.ofAgent
      (if i = e then
        (renewalMaskedPair (compileAdvice (ceilLogTwo n))
          suppress (C e) (C (ring.rightNeighbor e))).1
      else if i = ring.rightNeighbor e then
        (renewalMaskedPair (compileAdvice (ceilLogTwo n))
          suppress (C e) (C (ring.rightNeighbor e))).2
      else C i) =
      ProjW.ofAgent
      (if i = e then
        (renewalMaskedPair (compileAdvice (ceilLogTwo n))
          false (C e) (C (ring.rightNeighbor e))).1
      else if i = ring.rightNeighbor e then
        (renewalMaskedPair (compileAdvice (ceilLogTwo n))
          false (C e) (C (ring.rightNeighbor e))).2
      else C i)
    by_cases he : i = e
    · simp only [if_pos he]
      exact (bankRepairMaskedWordPair
        (compileAdvice (ceilLogTwo n))
        (C e) (C (ring.rightNeighbor e)) suppress).1
    · by_cases hj : i = ring.rightNeighbor e
      · exact (congrArg ProjW.ofAgent ((if_neg he).trans (if_pos hj))).trans
          ((bankRepairMaskedWordPair
            (compileAdvice (ceilLogTwo n))
            (C e) (C (ring.rightNeighbor e)) suppress).2.trans
            (congrArg ProjW.ofAgent ((if_neg he).trans (if_pos hj))).symm)
      · exact congrArg ProjW.ofAgent
          (((if_neg he).trans (if_neg hj)).trans
            ((if_neg he).trans (if_neg hj)).symm)
  rw [renewalMaskedStepOff] at hsame
  exact hsame

/-- Bridge the exact valid masked BANK referenceNext to its R
projection. The reference history and bank memory remain intact. -/
theorem bankRepairReaderMaskedStep {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank) (e : Fin n) :
    piR ((bankRepairNext ring hbank z e).val.1) =
      piR (headlinePhysicalNext ring z.val.1 e) := by
  have hrow :
      ((bankRepairNext ring hbank z e).val.1) =
        renewalMaskedStep ring z.val.1 e
          (renewalBankCut ring z.val.1 z.val.2 e) := by
    rfl
  rw [hrow]
  exact bankRepairMaskedReaderProjection ring z.val.1 e
    (renewalBankCut ring z.val.1 z.val.2 e)

theorem bankRepairWordMaskedStep {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank) (e : Fin n) :
    piW ((bankRepairNext ring hbank z e).val.1) =
      piW (headlinePhysicalNext ring z.val.1 e) := by
  have hrow :
      ((bankRepairNext ring hbank z e).val.1) =
        renewalMaskedStep ring z.val.1 e
          (renewalBankCut ring z.val.1 z.val.2 e) := by
    rfl
  rw [hrow]
  exact bankRepairMaskedWordProjection ring z.val.1 e
    (renewalBankCut ring z.val.1 z.val.2 e)

/-! ## The OLD no-FIRE requirement and genuine projected rows -/

/-- The accepted W class alone is not yet proved to imply this
OLD-physical no-FIRE premise on every masked reference cut.
The post-preparation grant-free invariant must supply it. -/
def BankRepairNoFireFromW {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) : Prop :=
  ∀ z : BankReferenceState ring hbank,
    BankRepairWAccepted ring hbank z →
      ∀ e : Fin n,
        oldFire (z.val.1 e) (z.val.1 (ring.rightNeighbor e)) = none

/-- The masked raw projection is the genuine R owner phiR
whenever the OLD physical pair is birth-free. -/
theorem bankRepairReaderPhiStepOfNoFire {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank) (e : Fin n)
    (hfire :
      oldFire (z.val.1 e)
        (z.val.1 (ring.rightNeighbor e)) = none) :
    piR ((bankRepairNext ring hbank z e).val.1) =
      phiR ring (piR z.val.1) e := by
  have hreal := stepR_noFire (q := ceilLogTwo n)
    hn ring z.val.1 e hfire
  change piR (headlinePhysicalNext ring z.val.1 e) =
    phiR ring (piR z.val.1) e at hreal
  exact (bankRepairReaderMaskedStep ring hbank z e).trans hreal

theorem bankRepairWordPhiStepOfNoFire {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank) (e : Fin n)
    (hfire :
      oldFire (z.val.1 e)
        (z.val.1 (ring.rightNeighbor e)) = none) :
    piW ((bankRepairNext ring hbank z e).val.1) =
      phiW ring (piW z.val.1) e := by
  have hreal := stepW_noFire (q := ceilLogTwo n)
    hn ring z.val.1 e hfire
  change piW (headlinePhysicalNext ring z.val.1 e) =
    phiW ring (piW z.val.1) e at hreal
  exact (bankRepairWordMaskedStep ring hbank z e).trans hreal

/-- This is the exact E.G18 WordFactor transport along the
masked successor, once OLD FIRE absence is established. -/
theorem bankRepairWordStepOfNoFire {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank) (e : Fin n)
    (hfire :
      oldFire (z.val.1 e)
        (z.val.1 (ring.rightNeighbor e)) = none)
    (hword : BankRepairWord ring hbank z) :
    BankRepairWord ring hbank
      (bankRepairNext ring hbank z e) := by
  change AcceptedReceipts.AcceptedWord ring
    (BlockA.wordT ring) (BlockA.wordValidated ring)
    (piW z.val.1) at hword
  change AcceptedReceipts.AcceptedWord ring
    (BlockA.wordT ring) (BlockA.wordValidated ring)
    (piW ((bankRepairNext ring hbank z e).val.1))
  rw [bankRepairWordPhiStepOfNoFire ring hn hbank z e hfire]
  exact AcceptedReceipts.accepted_word_phi_step
    ring (piW z.val.1) e hword

/-- The reachable E.G23 reader theorem, not the stronger
unrestricted accepted_reader_step, transports the genuine
five-fold receipt on a birth-free masked BANK edge. -/
theorem bankRepairReaderStepOfNoFire {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank) (e : Fin n)
    (hfire :
      oldFire (z.val.1 e)
        (z.val.1 (ring.rightNeighbor e)) = none)
    (hreader : BankRepairReader ring hbank z) :
    BankRepairReader ring hbank
      (bankRepairNext ring hbank z e) := by
  change AcceptedReceipts.AcceptedReader ring
    (AcceptedReceipts.AcceptedWord ring
      (BlockA.wordT ring) (BlockA.wordValidated ring))
    (Closure.readerFoldValid (ceilLogTwo n) n)
    (piR z.val.1) at hreader
  change AcceptedReceipts.AcceptedReader ring
    (AcceptedReceipts.AcceptedWord ring
      (BlockA.wordT ring) (BlockA.wordValidated ring))
    (Closure.readerFoldValid (ceilLogTwo n) n)
    (piR ((bankRepairNext ring hbank z e).val.1))
  rw [bankRepairReaderPhiStepOfNoFire ring hn hbank z e hfire]
  exact Closure.readerGeneratedPhiStep hn
    (bankRepairReaderCompiledWidthPos hbank) ring
    (AcceptedReceipts.AcceptedWord ring
      (BlockA.wordT ring) (BlockA.wordValidated ring))
    (piR z.val.1) e hreader

/-- The E.G19/E.G20 ghost invariant applies on the
same masked physical state, under the same OLD no-FIRE guard. -/
theorem bankRepairReaderGhostStepOfNoFire {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank) (e : Fin n)
    (control : BlockA.ReaderControl n
      (compileAdvice (ceilLogTwo n)))
    (hfire :
      oldFire (z.val.1 e)
        (z.val.1 (ring.rightNeighbor e)) = none)
    (hwf : Closure.ReaderGhostWellFormed
      (piR z.val.1) control) :
    Closure.ReaderGhostWellFormed
      (piR ((bankRepairNext ring hbank z e).val.1))
      (BlockA.readerControlNext ring control
        (piR z.val.1) e
        (piR ((bankRepairNext ring hbank z e).val.1))) := by
  rw [bankRepairReaderPhiStepOfNoFire ring hn hbank z e hfire]
  exact Closure.readerGhostWellFormedStep hn
    (bankRepairReaderCompiledWidthPos hbank) ring
    (piR z.val.1) control e hwf

/-! ## E.G5/E.G37 closure remains explicitly scoped -/

def BankRepairCoreClosedFromW {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) : Prop :=
  ∀ z : BankReferenceState ring hbank,
    BankRepairWAccepted ring hbank z →
      ∀ e : Fin n,
        BankRepairCore ring hbank
          (bankRepairNext ring hbank z e)

def BankRepairWAcceptedClosed {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) : Prop :=
  ∀ z : BankReferenceState ring hbank,
    BankRepairWAccepted ring hbank z →
      ∀ e : Fin n,
        BankRepairWAccepted ring hbank
          (bankRepairNext ring hbank z e)

/-- WordFactor preservation plus the separately earned core
closure yields the full W-accepted closure in the real reference. -/
theorem bankRepairWAcceptedClosedOfInputs {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hcore : BankRepairCoreClosedFromW ring hbank)
    (hnofire : BankRepairNoFireFromW ring hbank) :
    BankRepairWAcceptedClosed ring hbank := by
  intro z hz e
  exact ⟨hcore z hz e,
    bankRepairWordStepOfNoFire ring hn hbank z e
      (hnofire z hz e) hz.2⟩

/-- The second conjunct of the existing E.G5/E.G37 five-factor
preservation interface is exactly this closure contract. -/
theorem bankRepairWAcceptedClosedOfReceipts {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hpres : BankRepairReceiptPreservation ring hbank) :
    BankRepairWAcceptedClosed ring hbank :=
  hpres.2.1

/-- Finite actual masked-reference edge words preserve WAccepted
without reinitializing the word/worker history at an R cut. -/
theorem bankRepairWAcceptedRun {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hclosed : BankRepairWAcceptedClosed ring hbank)
    (z : BankReferenceState ring hbank)
    (hz : BankRepairWAccepted ring hbank z)
    (word : List (Fin n)) :
    BankRepairWAccepted ring hbank
      (word.foldl (bankRepairNext ring hbank) z) := by
  induction word generalizing z with
  | nil =>
      simpa only [List.foldl_nil] using hz
  | cons e rest ih =>
      simpa only [List.foldl_cons] using
        (ih (bankRepairNext ring hbank z e) (hclosed z hz e))

/-! ## Initialize the R monitor at the ACTUAL accepted W endpoint -/

/-- Every occupied raw slot at the W cut receives its own
inherited name, including any raw token minted on the entering
physical service. No physical raw fields are cleared or reset. -/
def bankRepairReaderInitialControl {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank) :
    BlockA.ReaderControl n (compileAdvice (ceilLogTwo n)) :=
  { phase := .retire
    tags := fun i =>
      if (piR z.val.1 i).rawTok.isSome = true
        then .inherited i else .empty
    inheritedNames := fun i => (piR z.val.1 i).rawTok.isSome }

/-- This is the concrete J_R initializer at the present W state,
not an imaginary token-free snapshot after the entering edge. -/
theorem bankRepairReaderInitializesAtW {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank)
    (hz : BankRepairWAccepted ring hbank z) :
    BlockA.initializesReader
      (AcceptedReceipts.AcceptedWord ring
        (BlockA.wordT ring) (BlockA.wordValidated ring))
      (piR z.val.1)
      (.live (piR z.val.1)
        (bankRepairReaderInitialControl ring hbank z)) := by
  constructor
  · change BankRepairWord ring hbank z
    exact hz.2
  · refine ⟨bankRepairReaderInitialControl ring hbank z,
        rfl, rfl, ?_⟩
    intro i
    by_cases hi : (piR z.val.1 i).rawTok.isSome = true
    · simp [bankRepairReaderInitialControl, hi]
    · simp [bankRepairReaderInitialControl, hi]

/-- The initial monitor is structurally well formed by the
readerGhostWellFormedOrigin theorem. -/
theorem bankRepairReaderOriginWellFormed {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank)
    (hz : BankRepairWAccepted ring hbank z) :
    ∃ control : BlockA.ReaderControl n
          (compileAdvice (ceilLogTwo n)),
      (.live (piR z.val.1) control :
        BlockA.Decoration
          (Fin n → ProjR (compileAdvice (ceilLogTwo n)))
          (BlockA.ReaderControl n (compileAdvice (ceilLogTwo n)))) =
        .live (piR z.val.1)
          (bankRepairReaderInitialControl ring hbank z) ∧
      Closure.ReaderGhostWellFormed (piR z.val.1) control := by
  have hinit := bankRepairReaderInitializesAtW ring hbank z hz
  obtain ⟨control, heq, hgood⟩ :=
    Closure.readerGhostWellFormedOrigin
      (AcceptedReceipts.AcceptedWord ring
        (BlockA.wordT ring) (BlockA.wordValidated ring))
      (piR z.val.1)
      (.live (piR z.val.1)
        (bankRepairReaderInitialControl ring hbank z)) hinit
  exact ⟨control, heq.symm, hgood⟩

/-! ## Exact missing physical retirement and five-fold validation -/

/-- A retirement certificate is tied to the same concrete
reference suffix from its actual W endpoint; it retains the
whole projected R0/R1 run and finishes with no inherited names.
It does NOT yet assert numerical E.G22 acceptance. -/
def BankRepairReaderRetiredFrom {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (start finish : BankReferenceState ring hbank) : Prop :=
  ∃ (word : List (Fin n))
    (initial : BlockA.Decoration
      (Fin n → ProjR (compileAdvice (ceilLogTwo n)))
      (BlockA.ReaderControl n (compileAdvice (ceilLogTwo n))))
    (control : BlockA.ReaderControl n
      (compileAdvice (ceilLogTwo n))),
    finish = word.foldl (bankRepairNext ring hbank) start ∧
    BlockA.initializesReader
      (AcceptedReceipts.AcceptedWord ring
        (BlockA.wordT ring) (BlockA.wordValidated ring))
      (piR start.val.1) initial ∧
    BlockA.Run ring (phiR ring)
      (BlockA.readerControlNext ring)
      (piR start.val.1) initial word
      (piR finish.val.1)
      (.live (piR finish.val.1) control) ∧
    control.phase = .done ∧
    (∀ name : Fin n, control.inheritedNames name = false)

/-- Missing paper E.G19 retirement clock, with precisely its
s*n^2 budget on the actual masked next, not on phiR alone.
The doubled numerator is the half-unit form 2*s. -/
def BankRepairResidentRetirementClock {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) : Prop :=
  ∀ start : BankReferenceState ring hbank,
    BankRepairWAccepted ring hbank start →
      ∀ T : Nat,
        2 * costNumerator
          (bankRepairNext ring hbank)
          (BankRepairReaderRetiredFrom ring hbank start)
          start T ≤
        n ^ T * ((2 * ceilLogTwo (ceilLogTwo n)) * n ^ 2)

/-- Missing E.G22 five-fold induction from the SAME W-endpoint
and reader observer. This asks for R0b/R1c sample-fold validity,
R0c safety and surviving-token correctness at a done cut;
it does not posit an independent invented reader witness. -/
def BankRepairReaderFoldSound {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) : Prop :=
  ∀ (start finish : BankReferenceState ring hbank)
    (word : List (Fin n))
    (initial : BlockA.Decoration
      (Fin n → ProjR (compileAdvice (ceilLogTwo n)))
      (BlockA.ReaderControl n (compileAdvice (ceilLogTwo n))))
    (control : BlockA.ReaderControl n
      (compileAdvice (ceilLogTwo n))),
    BankRepairWAccepted ring hbank start →
    finish = word.foldl (bankRepairNext ring hbank) start →
    BlockA.initializesReader
      (AcceptedReceipts.AcceptedWord ring
        (BlockA.wordT ring) (BlockA.wordValidated ring))
      (piR start.val.1) initial →
    BlockA.Run ring (phiR ring)
      (BlockA.readerControlNext ring)
      (piR start.val.1) initial word
      (piR finish.val.1)
      (.live (piR finish.val.1) control) →
    control.phase = .done →
    (∀ name : Fin n, control.inheritedNames name = false) →
    BlockA.acceptsReader
      (Closure.readerFoldValid (ceilLogTwo n) n)
      (AcceptedReceipts.QReader ring)
      (piR finish.val.1)
      (.live (piR finish.val.1) control)

/-- From true reader retirement plus E.G22 soundness, the R
factor is an actual generated witness in the full BANK state. -/
theorem bankRepairReaderOfRetiredFrom {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hfold : BankRepairReaderFoldSound ring hbank)
    (start finish : BankReferenceState ring hbank)
    (hW : BankRepairWAccepted ring hbank start)
    (hret : BankRepairReaderRetiredFrom ring hbank start finish) :
    BankRepairReader ring hbank finish := by
  rcases hret with
    ⟨word, initial, control, hactual, hinit,
      hrun, hdone, hnames⟩
  have hacc := hfold start finish word initial control
    hW hactual hinit hrun hdone hnames
  change AcceptedReceipts.AcceptedReader ring
    (AcceptedReceipts.AcceptedWord ring
      (BlockA.wordT ring) (BlockA.wordValidated ring))
    (Closure.readerFoldValid (ceilLogTwo n) n)
    (piR finish.val.1)
  exact ⟨piR start.val.1, initial, word,
    .live (piR finish.val.1) control,
    hinit, hrun, hacc⟩

/-- Any reader certificate obtained at a post-W cut retains the
W factor if E.G5/E.G37 W closure is separately established. -/
theorem bankRepairRFoldOfRetiredFrom {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hclosed : BankRepairWAcceptedClosed ring hbank)
    (hfold : BankRepairReaderFoldSound ring hbank)
    (start finish : BankReferenceState ring hbank)
    (hW : BankRepairWAccepted ring hbank start)
    (hret : BankRepairReaderRetiredFrom ring hbank start finish) :
    BankRepairRFoldEstablished ring hbank finish := by
  rcases hret with
    ⟨word, initial, control, hactual, hinit,
      hrun, hdone, hnames⟩
  have hWfinal : BankRepairWAccepted ring hbank finish := by
    rw [hactual]
    exact bankRepairWAcceptedRun ring hbank hclosed start hW word
  have hret' : BankRepairReaderRetiredFrom ring hbank
      start finish :=
    ⟨word, initial, control, hactual, hinit,
      hrun, hdone, hnames⟩
  exact ⟨hWfinal,
    bankRepairReaderOfRetiredFrom ring hbank hfold
      start finish hW hret'⟩

/-- Conditional completion of the R producer. The sole
quantitative premise is the resident-retirement clock, and the
other missing premise is the five-field acceptance at that cut.
Both use the SAME bankRepairNext and W-endpoint physical records. -/
theorem bankRepairReaderStageOfRetirementAndFold {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hclock : BankRepairResidentRetirementClock ring hbank)
    (hfold : BankRepairReaderFoldSound ring hbank) :
    BankRepairReaderStage ring hbank := by
  have hhalf : BankRepairHalfStage
      (bankRepairNext ring hbank)
      (BankRepairWAccepted ring hbank)
      (BankRepairReader ring hbank)
      (2 * ceilLogTwo (ceilLogTwo n)) := by
    intro start hW T
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
        (fun finish hret =>
          bankRepairReaderOfRetiredFrom ring hbank hfold
            start finish hW hret) start T
    calc
      2 * costNumerator (bankRepairNext ring hbank)
          (BankRepairReader ring hbank) start T ≤
        2 * costNumerator (bankRepairNext ring hbank)
          (BankRepairReaderRetiredFrom ring hbank start)
          start T := Nat.mul_le_mul_left 2 hmono
      _ ≤ n ^ T *
          ((2 * ceilLogTwo (ceilLogTwo n)) * n ^ 2) :=
            hclock start hW T
  constructor
  · intro start hW
    apply (UniformFirstHit.expectedHittingTimeAtMost_iff_cost
      (bankRepairNext ring hbank)
      (BankRepairReader ring hbank)
      (by omega : 0 < n) start
      (ceilLogTwo (ceilLogTwo n) * n ^ 2)).2
    intro T
    have hcost := hhalf start hW T
    have hscale :
        n ^ T * ((2 * ceilLogTwo (ceilLogTwo n)) * n ^ 2) =
          2 * (n ^ T * (ceilLogTwo (ceilLogTwo n) * n ^ 2)) := by
      ac_rfl
    rw [hscale] at hcost
    omega
  · exact hhalf

end L3.RenewalReferenceClock

/-!
Reachable E.G22 induction reduction.

This block deliberately does not declare BankRepairReaderFoldSound
as a theorem. The single named missing row certificate below is a
reachable-prefix statement: it cannot be applied to arbitrary ghost
tags. The existing R0b/R1c five-field lemmas in Closure.lean and the
existing ReaderGhostWellFormed transport are reused conceptually.

R0c is the only rejecting raw owner row. The terminal condition must
be proved from actual sampled W provenance, rather than assumed from
the five numerical accumulators or from a nonexistent QReader at the
W cut. No physical chain, masked step, or W observer is reset here.
-/

namespace L3.RenewalReferenceClock

/-- R0c can report a pre-existing marker error. This is an
explicit row-level obstruction to deducing QReader from a
structurally well-formed done ghost alone. -/
theorem bankRepairReaderTerminalMarkerReject {c : Compiled}
    (x y : ProjR c) (old : RawTok c.t)
    (hx : x.rawTok = some old)
    (hy : y.rawTok = none)
    (hterminal : ¬ old.j < c.t)
    (hmarker : old.m = true) :
    (rawR x y).reject = true := by
  simp [rawR, rawD1Step, ProjR.lift,
    hx, hy, hterminal, hmarker]

/-- At any reachable done control, the structural invariant rules
out both empty tags at occupied sites and surviving inherited tags.
It does not yet certify the five numerical ledger equations. -/
theorem bankRepairReaderDoneTagFresh {n : Nat} {c : Compiled}
    (p : Fin n → ProjR c)
    (h : BlockA.ReaderControl n c)
    (hwf : Closure.ReaderGhostWellFormed p h)
    (hdone : h.phase = .done)
    (i : Fin n)
    (htok : (p i).rawTok.isSome = true) :
    ∃ (name : Fin n) (index : Fin (c.t + 1))
      (samples : BlockA.FiniteLedger
        (BlockA.ReaderSample n) c.t),
      h.tags i = .fresh name index samples := by
  cases htag : h.tags i with
  | empty =>
      have hs := hwf.support i
      rw [htag] at hs
      have hzero : (p i).rawTok.isSome = false := by
        simpa [BlockA.RawTag.identity?] using hs.symm
      rw [htok] at hzero
      cases hzero
  | inherited name =>
      have hbit : h.inheritedNames name = true := by
        rw [hwf.inherited name]
        exact (Closure.readerInheritedSetIff h.tags name).2
          ⟨i, htag⟩
      have hz := hwf.done hdone name
      rw [hz] at hbit
      cases hbit
  | fresh name index samples =>
      exact ⟨name, index, samples, rfl⟩

/-- Numerical part of the one E.G22 prefix invariant. The first
conjunct says every fresh tag has the actual complete five-fold
ledger. The second is precisely the source-scope R0c guard:
a fresh terminal cannot report a raw rejection. Inherited tags
are deliberately not required to be fold-valid. -/
def BankRepairReaderE22Evidence {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (p : Fin n → ProjR (compileAdvice (ceilLogTwo n)))
    (h : BlockA.ReaderControl n
      (compileAdvice (ceilLogTwo n))) : Prop :=
  (∀ (i name : Fin n)
      (index : Fin ((compileAdvice (ceilLogTwo n)).t + 1))
      (samples : BlockA.FiniteLedger (BlockA.ReaderSample n)
        (compileAdvice (ceilLogTwo n)).t),
      h.tags i = .fresh name index samples →
        samples.count = index ∧
        Closure.readerFoldValid (ceilLogTwo n) n
          i (p i).rawTok index samples) ∧
  (∀ (e : Fin n)
      (old : RawTok (compileAdvice (ceilLogTwo n)).t)
      (name : Fin n)
      (index : Fin ((compileAdvice (ceilLogTwo n)).t + 1))
      (samples : BlockA.FiniteLedger (BlockA.ReaderSample n)
        (compileAdvice (ceilLogTwo n)).t),
      (p e).rawTok = some old →
      (p (ring.rightNeighbor e)).rawTok = none →
      ¬ old.j < (compileAdvice (ceilLogTwo n)).t →
      h.tags e = .fresh name index samples →
      (rawR (p e) (p (ring.rightNeighbor e))).reject = false)

/-- The invariant is carried on the actual projected W-accepted
reader run, never on a free-standing arbitrary decoration. -/
def BankRepairReaderE22Invariant {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (p : Fin n → ProjR (compileAdvice (ceilLogTwo n)))
    (h : BlockA.ReaderControl n
      (compileAdvice (ceilLogTwo n))) : Prop :=
  AcceptedReceipts.AcceptedWord ring
      (BlockA.wordT ring) (BlockA.wordValidated ring)
      (fun i => (p i).word) ∧
    Closure.ReaderGhostWellFormed p h ∧
    BankRepairReaderE22Evidence ring hbank p h

/-- The sole unproved producer: a reachable W-origin E.G22 prefix
invariant is preserved on the selected genuine phiR row. R0b and
R1c use the already present numerical lemmas; the new substantive
safety obligation is R0c under stamped W provenance. The Run
premise is essential: arbitrary well-formed but fabricated fresh
sample ledgers need not be safe. -/
def BankRepairReaderE22RowPreservation {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) :
    Prop :=
  ∀ (start : BankReferenceState ring hbank)
    (initial : BlockA.Decoration
      (Fin n → ProjR (compileAdvice (ceilLogTwo n)))
      (BlockA.ReaderControl n
        (compileAdvice (ceilLogTwo n))))
    (word : List (Fin n))
    (p : Fin n → ProjR (compileAdvice (ceilLogTwo n)))
    (h : BlockA.ReaderControl n
      (compileAdvice (ceilLogTwo n)))
    (e : Fin n),
    BankRepairWAccepted ring hbank start →
    BlockA.initializesReader
      (AcceptedReceipts.AcceptedWord ring
        (BlockA.wordT ring) (BlockA.wordValidated ring))
      (piR start.val.1) initial →
    BlockA.Run ring (phiR ring)
      (BlockA.readerControlNext ring)
      (piR start.val.1) initial word p (.live p h) →
    BankRepairReaderE22Invariant ring hbank p h →
    BankRepairReaderE22Invariant ring hbank
      (phiR ring p e)
      (BlockA.readerControlNext ring h p e (phiR ring p e))

/-- At J_R every raw site is inherited or empty, hence there
are no fresh ledgers for which an E.G22 equation could fail. -/
theorem bankRepairReaderE22InitialNoFresh {n : Nat}
    (p : Fin n → ProjR (compileAdvice (ceilLogTwo n)))
    (h : BlockA.ReaderControl n
      (compileAdvice (ceilLogTwo n)))
    (hslots : ∀ i : Fin n,
      if (p i).rawTok.isSome = true then
        h.tags i = .inherited i ∧ h.inheritedNames i = true
      else h.tags i = .empty ∧ h.inheritedNames i = false) :
    ∀ (i name : Fin n)
      (index : Fin ((compileAdvice (ceilLogTwo n)).t + 1))
      (samples : BlockA.FiniteLedger (BlockA.ReaderSample n)
        (compileAdvice (ceilLogTwo n)).t),
      h.tags i ≠ .fresh name index samples := by
  intro i name index samples htag
  cases hb : (p i).rawTok.isSome with
  | false =>
      have hs := hslots i
      simp [hb] at hs
      rw [hs.1] at htag
      cases htag
  | true =>
      have hs := hslots i
      simp [hb] at hs
      rw [hs.1] at htag
      cases htag

theorem bankRepairReaderE22EvidenceOrigin {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (p : Fin n → ProjR (compileAdvice (ceilLogTwo n)))
    (h : BlockA.ReaderControl n
      (compileAdvice (ceilLogTwo n)))
    (hslots : ∀ i : Fin n,
      if (p i).rawTok.isSome = true then
        h.tags i = .inherited i ∧ h.inheritedNames i = true
      else h.tags i = .empty ∧ h.inheritedNames i = false) :
    BankRepairReaderE22Evidence ring hbank p h := by
  have hno := bankRepairReaderE22InitialNoFresh p h hslots
  constructor
  · intro i name index samples ht
    exact False.elim (hno i name index samples ht)
  · intro e old name index samples _ _ _ ht
    exact False.elim (hno e name index samples ht)

/-- The exact W-origin constructor supplies all three fields of
the proposed invariant. This uses the existing E.G20 lemma. -/
theorem bankRepairReaderE22InvariantOrigin {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (p : Fin n → ProjR (compileAdvice (ceilLogTwo n)))
    (initial : BlockA.Decoration
      (Fin n → ProjR (compileAdvice (ceilLogTwo n)))
      (BlockA.ReaderControl n
        (compileAdvice (ceilLogTwo n))))
    (hinit : BlockA.initializesReader
      (AcceptedReceipts.AcceptedWord ring
        (BlockA.wordT ring) (BlockA.wordValidated ring))
      p initial) :
    ∃ control : BlockA.ReaderControl n
        (compileAdvice (ceilLogTwo n)),
      initial = .live p control ∧
      BankRepairReaderE22Invariant ring hbank p control := by
  obtain ⟨hword, control, heq, hphase, hslots⟩ := hinit
  refine ⟨control, heq, ?_⟩
  exact ⟨hword,
    Closure.readerGhostWellFormedStart p control hphase hslots,
    bankRepairReaderE22EvidenceOrigin ring hbank p control hslots⟩

/-- All finite prefixes from J_R preserve the proposed invariant
IF and only if its missing reachable per-row producer is supplied.
The induction follows precisely the same E.G9 Run, with no extra
fictional source or reinitialization. -/
theorem bankRepairReaderE22RunInvariant {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hrows : BankRepairReaderE22RowPreservation ring hbank)
    (start : BankReferenceState ring hbank)
    (hW : BankRepairWAccepted ring hbank start)
    (initial : BlockA.Decoration
      (Fin n → ProjR (compileAdvice (ceilLogTwo n)))
      (BlockA.ReaderControl n
        (compileAdvice (ceilLogTwo n))))
    (hinit : BlockA.initializesReader
      (AcceptedReceipts.AcceptedWord ring
        (BlockA.wordT ring) (BlockA.wordValidated ring))
      (piR start.val.1) initial)
    (word : List (Fin n))
    (p : Fin n → ProjR (compileAdvice (ceilLogTwo n)))
    (γ : BlockA.Decoration
      (Fin n → ProjR (compileAdvice (ceilLogTwo n)))
      (BlockA.ReaderControl n
        (compileAdvice (ceilLogTwo n))))
    (hrun : BlockA.Run ring (phiR ring)
      (BlockA.readerControlNext ring)
      (piR start.val.1) initial word p γ) :
    ∃ control : BlockA.ReaderControl n
        (compileAdvice (ceilLogTwo n)),
      γ = .live p control ∧
      BankRepairReaderE22Invariant ring hbank p control := by
  induction hrun with
  | empty =>
      exact bankRepairReaderE22InvariantOrigin ring hbank
        (piR start.val.1) initial hinit
  | @next w q γ' h e ih =>
      obtain ⟨control, hγ, hI⟩ := ih
      have hprefix : BlockA.Run ring (phiR ring)
          (BlockA.readerControlNext ring)
          (piR start.val.1) initial w q (.live q control) := by
        simpa [hγ] using h
      have hstep := hrows start initial w q control e
        hW hinit hprefix hI
      refine ⟨_, ?_, hstep⟩
      rw [hγ]
      classical
      simp [BlockA.update]

/-- At a done control no inherited token can mask an unsafe R0c
row. Every other R0/R1 row has reject=false definitionally. -/
theorem bankRepairReaderE22NoRejectAtDone {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (p : Fin n → ProjR (compileAdvice (ceilLogTwo n)))
    (h : BlockA.ReaderControl n
      (compileAdvice (ceilLogTwo n)))
    (hI : BankRepairReaderE22Invariant ring hbank p h)
    (hdone : h.phase = .done)
    (e : Fin n) :
    ¬ AcceptedReceipts.badReader ring p e := by
  change (rawR (p e) (p (ring.rightNeighbor e))).reject ≠ true
  cases hx : (p e).rawTok with
  | none =>
      cases hy : (p (ring.rightNeighbor e)).rawTok with
      | none =>
          cases hk : (p (ring.rightNeighbor e)).rawKick <;>
            simp [rawR, rawD1Step, ProjR.lift, hx, hy, hk]
      | some resident =>
          simp [rawR, rawD1Step, ProjR.lift, hx, hy]
  | some old =>
      cases hy : (p (ring.rightNeighbor e)).rawTok with
      | some resident =>
          simp [rawR, rawD1Step, ProjR.lift, hx, hy]
      | none =>
          by_cases hmore : old.j <
              (compileAdvice (ceilLogTwo n)).t
          · simp [rawR, rawD1Step, ProjR.lift,
              hx, hy, hmore]
          · have htok : (p e).rawTok.isSome = true := by
              rw [hx]
              rfl
            obtain ⟨name, index, samples, htag⟩ :=
              bankRepairReaderDoneTagFresh p h
                hI.2.1 hdone e htok
            have hno := hI.2.2.2 e old name index samples
              hx hy hmore htag
            intro hbad
            rw [hno] at hbad
            cases hbad

/-- For the coinductive SafeAll argument the witness remembers
the SAME J_R and its actual projected Run prefix, together with
the one invariant and a sticky done bit. -/
def BankRepairReaderE22PostDoneWitness {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (start : BankReferenceState ring hbank)
    (initial : BlockA.Decoration
      (Fin n → ProjR (compileAdvice (ceilLogTwo n)))
      (BlockA.ReaderControl n
        (compileAdvice (ceilLogTwo n))))
    (cursor : List (Fin n) ×
      BlockA.ReaderControl n (compileAdvice (ceilLogTwo n)))
    (p : Fin n → ProjR (compileAdvice (ceilLogTwo n))) : Prop :=
  BlockA.Run ring (phiR ring) (BlockA.readerControlNext ring)
      (piR start.val.1) initial cursor.1 p (.live p cursor.2) ∧
    BankRepairReaderE22Invariant ring hbank p cursor.2 ∧
    cursor.2.phase = .done

/-- Conditional QReader proof: no safety is postulated at the W
cut. At the done cut the reachable invariant excludes every R0c
reject and is maintained along every future projected edge. -/
theorem bankRepairReaderE22SafeFromRows {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hrows : BankRepairReaderE22RowPreservation ring hbank)
    (start : BankReferenceState ring hbank)
    (initial : BlockA.Decoration
      (Fin n → ProjR (compileAdvice (ceilLogTwo n)))
      (BlockA.ReaderControl n
        (compileAdvice (ceilLogTwo n))))
    (hW : BankRepairWAccepted ring hbank start)
    (hinit : BlockA.initializesReader
      (AcceptedReceipts.AcceptedWord ring
        (BlockA.wordT ring) (BlockA.wordValidated ring))
      (piR start.val.1) initial)
    (word : List (Fin n))
    (p : Fin n → ProjR (compileAdvice (ceilLogTwo n)))
    (control : BlockA.ReaderControl n
      (compileAdvice (ceilLogTwo n)))
    (hrun : BlockA.Run ring (phiR ring)
      (BlockA.readerControlNext ring)
      (piR start.val.1) initial word p (.live p control))
    (hI : BankRepairReaderE22Invariant ring hbank p control)
    (hdone : control.phase = .done) :
    AcceptedReceipts.QReader ring p := by
  apply AcceptedReceipts.safe_inclusion_image
    (phiR ring) (AcceptedReceipts.badReader ring)
    (BankRepairReaderE22PostDoneWitness ring hbank start initial)
  · intro cursor state hc e
    rcases cursor with ⟨pfx, h⟩
    obtain ⟨hprefix, hInv, hphase⟩ := hc
    have hno := bankRepairReaderE22NoRejectAtDone
      ring hbank state h hInv hphase e
    have hstep := hrows start initial pfx state h e
      hW hinit hprefix hInv
    have hdoneNext :=
      Closure.readerDoneSticky ring h state e hphase
    have hrunNext : BlockA.Run ring (phiR ring)
        (BlockA.readerControlNext ring)
        (piR start.val.1) initial (pfx ++ [e])
        (phiR ring state e)
        (.live (phiR ring state e)
          (BlockA.readerControlNext ring h state e
            (phiR ring state e))) := by
      have hs := BlockA.Run.next hprefix e
      simpa [BlockA.update] using hs
    exact ⟨hno, ⟨(pfx ++ [e],
      BlockA.readerControlNext ring h state e
        (phiR ring state e)), hrunNext, hstep, hdoneNext⟩⟩
  · exact ⟨(word, control), hrun, hI, hdone⟩

/-- Conditional assembly of the exact advertised E.G22 Prop.
One reachable row certificate remains open; it is not assumed as
an axiom, nor is the main soundness claim asserted unconditionally. -/
theorem bankRepairReaderFoldSoundOfE22Rows {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hrows : BankRepairReaderE22RowPreservation ring hbank) :
    BankRepairReaderFoldSound ring hbank := by
  intro start finish word initial control hW _hactual
    hinit hrun hdone hnames
  obtain ⟨observed, hEq, hInv⟩ :=
    bankRepairReaderE22RunInvariant ring hbank hrows
      start hW initial hinit word (piR finish.val.1)
      (.live (piR finish.val.1) control) hrun
  have hControl : control = observed := by
    cases hEq
    rfl
  subst observed
  have hsafe : AcceptedReceipts.QReader ring
      (piR finish.val.1) :=
    bankRepairReaderE22SafeFromRows ring hbank hrows
      start initial hW hinit word (piR finish.val.1)
      control hrun hInv hdone
  change BlockA.acceptsReader
    (Closure.readerFoldValid (ceilLogTwo n) n)
    (AcceptedReceipts.QReader ring)
    (piR finish.val.1)
    (.live (piR finish.val.1) control)
  dsimp [BlockA.acceptsReader]
  refine ⟨rfl, hdone, hnames, ?_, hsafe⟩
  intro i htok
  obtain ⟨name, index, samples, htag⟩ :=
    bankRepairReaderDoneTagFresh (piR finish.val.1)
      control hInv.2.1 hdone i htok
  have hn := hInv.2.2.1 i name index samples htag
  exact ⟨name, index, samples, htag, hn.1, hn.2⟩

end L3.RenewalReferenceClock


/-!
Source-level E.G19 retirement accounting.

All definitions here use the actual
bankRepairNext chain. The proof-only reader control is initialized
at the SAME accepted W cut, and follows the selected OLD reader
pair on that chain.

Paper repair.tex, Generated window readers (E.G19), lines
1096--1121: at most n old identities, each needing at most t
outgoing services. The weight of an inherited token at raw
index j (1 <= j <= t) is t+1-j, i.e. t-jm1. R0a and R0c erase
the weight; R0b moves it with j increased by one; R1a/R1b/R1c
do not create inherited weight.

There is an important zero-resident corner: the initial control
is .retire even if all raw tokens are empty. The naive total
inherited weight is then zero but completion still needs one
physical edge to set phase .done. The corrected potential
charges one final ticket in the empty-but-not-done case.

The one OPEN source obligation below is the complete real
owner-row certificate. In particular it does not assume a
different independent reader clock or a forged terminal control.
-/

namespace L3.RenewalReferenceClock

open L3.HeadlineRenewal
open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree

set_option autoImplicit false
set_option Elab.async false

/-- E.G19's remaining number of outgoing services for a
physically present inherited raw token. A fresh tag never
inherits any part of this potential. -/
def bankRepairReaderResidentSiteDebt {n t : Nat}
    (tag : BlockA.RawTag n t)
    (tok : Option (RawTok t)) : Nat :=
  match tag, tok with
  | .inherited _, some raw => t - raw.jm1.val
  | _, _ => 0

theorem bankRepairReaderResidentSiteDebtCap {n t : Nat}
    (tag : BlockA.RawTag n t)
    (tok : Option (RawTok t)) :
    bankRepairReaderResidentSiteDebt tag tok ≤ t := by
  cases tag with
  | empty =>
      cases tok <;> simp [bankRepairReaderResidentSiteDebt]
  | inherited name =>
      cases tok with
      | none => simp [bankRepairReaderResidentSiteDebt]
      | some raw =>
          change t - raw.jm1.val ≤ t
          exact Nat.sub_le _ _
  | fresh name index samples =>
      cases tok <;> simp [bankRepairReaderResidentSiteDebt]

/-- The last R0c outgoing hit of an inherited token has one
unpaid ticket; no legal raw token has zero residual weight. -/
theorem bankRepairReaderResidentDebtPositive {t : Nat}
    (raw : RawTok t) :
    1 ≤ t - raw.jm1.val := by
  have hi := raw.jm1.isLt
  omega

/-- On R0b, the NEW jm1 is the OLD numerical j. This is
exactly a decrease of one in the per-inherited-reader rank. -/
theorem bankRepairReaderResidentDebtMove {t : Nat}
    (raw : RawTok t) (hmove : raw.j < t) :
    t - (raw.jm1.val + 1) + 1 = t - raw.jm1.val := by
  change raw.jm1.val + 1 < t at hmove
  omega

/-- Aggregate all inherited outstanding hits on the actual raw
projection. The original physical sites, not a separate reader
scheduler, are the indexed summands. -/
def bankRepairReaderResidentTotal {n : Nat} {c : Compiled}
    (p : Fin n → ProjR c) (h : BlockA.ReaderControl n c) :
    Nat :=
  (List.ofFn (fun i : Fin n =>
    bankRepairReaderResidentSiteDebt
      (h.tags i) (p i).rawTok)).sum

theorem bankRepairReaderResidentTotalCap {n : Nat} {c : Compiled}
    (p : Fin n → ProjR c) (h : BlockA.ReaderControl n c) :
    bankRepairReaderResidentTotal p h ≤ n * c.t := by
  unfold bankRepairReaderResidentTotal
  calc
    (List.ofFn (fun i : Fin n =>
      bankRepairReaderResidentSiteDebt
        (h.tags i) (p i).rawTok)).sum ≤
      (List.ofFn (fun _ : Fin n => c.t)).sum :=
        ofFn_sum_le _ _ (fun i =>
          bankRepairReaderResidentSiteDebtCap
            (h.tags i) (p i).rawTok)
    _ = n * c.t := by rw [ofFn_sum_const]

/-- One final ticket when H is empty but the initial reader
phase has not yet observed a physical edge and become done. -/
def bankRepairReaderResidentPotential {n : Nat} {c : Compiled}
    (p : Fin n → ProjR c) (h : BlockA.ReaderControl n c) :
    Nat :=
  if h.phase = .done then 0
  else if Closure.readerHasInherited h then
    bankRepairReaderResidentTotal p h
  else 1

theorem bankRepairReaderResidentPotentialCap {n : Nat}
    {c : Compiled} (p : Fin n → ProjR c)
    (h : BlockA.ReaderControl n c)
    (hn : 0 < n) (ht : 0 < c.t) :
    bankRepairReaderResidentPotential p h ≤ n * c.t := by
  have htotal := bankRepairReaderResidentTotalCap p h
  have hpositive : 0 < n * c.t := Nat.mul_pos hn ht
  unfold bankRepairReaderResidentPotential
  split
  · exact Nat.zero_le _
  · split
    · exact htotal
    · omega

theorem bankRepairReaderResidentEmptyTicket {n : Nat}
    {c : Compiled} (p : Fin n → ProjR c)
    (h : BlockA.ReaderControl n c)
    (hr : h.phase = .retire)
    (he : Closure.readerHasInherited h = false) :
    bankRepairReaderResidentPotential p h = 1 := by
  simp [bankRepairReaderResidentPotential, hr, he]

/-- Diagnostic: the UNCORRECTED all-empty weight has no possible
positive Bellman drift even for five physical scheduler edges. -/
theorem bankRepairReaderNaiveEmptyDriftFails :
    ¬ (1 + (5 * 0 : Nat) ≤ 5 * 0) := by
  omega

/-- Original physical state plus the one canonical causal
reader-control record; no independent or resampled edge. -/
abbrev BankRepairReaderResidentCoupledState {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) :=
  BankReferenceState ring hbank ×
    BlockA.ReaderControl n (compileAdvice (ceilLogTwo n))

/-- The projected OLD reader pair is read from the actual
bankRepairNext source and successor, even if its phiR
identification is still an unproved source-side obligation. -/
noncomputable def bankRepairReaderResidentCoupledNext {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankRepairReaderResidentCoupledState ring hbank)
    (e : Fin n) :
    BankRepairReaderResidentCoupledState ring hbank :=
  (bankRepairNext ring hbank z.1 e,
   BlockA.readerControlNext ring z.2 (piR z.1.val.1) e
     (piR ((bankRepairNext ring hbank z.1 e).val.1)))

/-- The initial ghost is EXACTLY the installed initializer
at the W endpoint. The word is the original Fin n tape. -/
noncomputable def bankRepairReaderResidentTrace {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (start : BankReferenceState ring hbank)
    (word : List (Fin n)) :
    BankRepairReaderResidentCoupledState ring hbank :=
  word.foldl (bankRepairReaderResidentCoupledNext ring hbank)
    (start, bankRepairReaderInitialControl ring hbank start)

theorem bankRepairReaderResidentTraceSnoc {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (start : BankReferenceState ring hbank)
    (word : List (Fin n)) (e : Fin n) :
    bankRepairReaderResidentTrace ring hbank start (word ++ [e]) =
      bankRepairReaderResidentCoupledNext ring hbank
        (bankRepairReaderResidentTrace ring hbank start word) e := by
  unfold bankRepairReaderResidentTrace
  rw [List.foldl_append]
  rfl

private theorem bankRepairReaderResidentCoupledFoldPhysical {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankRepairReaderResidentCoupledState ring hbank)
    (word : List (Fin n)) :
    (word.foldl
      (bankRepairReaderResidentCoupledNext ring hbank) z).1 =
      word.foldl (bankRepairNext ring hbank) z.1 := by
  induction word generalizing z with
  | nil => rfl
  | cons e rest ih =>
      change
        (rest.foldl (bankRepairReaderResidentCoupledNext ring hbank)
          (bankRepairReaderResidentCoupledNext ring hbank z e)).1 =
        rest.foldl (bankRepairNext ring hbank)
          (bankRepairNext ring hbank z.1 e)
      exact ih _

/-- The physical component is precisely the original masked
reference foldl, not a second simulated physical chain. -/
theorem bankRepairReaderResidentTracePhysical {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (start : BankReferenceState ring hbank)
    (word : List (Fin n)) :
    (bankRepairReaderResidentTrace ring hbank start word).1 =
      word.foldl (bankRepairNext ring hbank) start := by
  unfold bankRepairReaderResidentTrace
  exact bankRepairReaderResidentCoupledFoldPhysical ring hbank
    (start, bankRepairReaderInitialControl ring hbank start) word

/-- A terminal bit on the actual causal reader trace. -/
noncomputable def bankRepairReaderResidentWordDone {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (start : BankReferenceState ring hbank)
    (word : List (Fin n)) : Prop :=
  (bankRepairReaderResidentTrace ring hbank start word).2.phase =
    .done

/-- The numerical debt on the actual causal reader trace. -/
noncomputable def bankRepairReaderResidentWordDebt {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (start : BankReferenceState ring hbank)
    (word : List (Fin n)) : Nat :=
  bankRepairReaderResidentPotential
    (piR (bankRepairReaderResidentTrace
      ring hbank start word).1.val.1)
    (bankRepairReaderResidentTrace ring hbank start word).2

/-- ONE OPEN physical R0/R1 row obligation for E.G19.

(1) The initialized ghost follows the literal BlockA.Run on the
same bankRepairNext word, not an arbitrary decoration.
(2) Done on that run means every inherited name has disappeared.
(3) The corrected per-name rank has a one-unit nominated-edge
Bellman drift under all six physical R0/R1 owner rows.

The first zero-rank failure of the naive formula is local R1b:
n=5, t=2, all five physical rawTok fields absent, responder
rawKick=false, initial control.phase=retire and all H bits false.
R1b leaves raw tokens empty and marks the control done. Naive
rank 0 would require 1+0 <= 5*0. The final ticket fixes that
local case. This diagnostic is not claimed BANK-reachable at n=5.

The unresolved physical issue is proving this full six-row
contract along ALL W-accepted masked reference words; in
particular bankRepairReaderPhiStepOfNoFire still needs the
separately unproved OLD no-FIRE transport premise. -/
def BankRepairResidentRetirementOwnerRows {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) : Prop :=
  ∀ start : BankReferenceState ring hbank,
    BankRepairWAccepted ring hbank start →
    (∀ word : List (Fin n),
      BlockA.Run ring (phiR ring)
        (BlockA.readerControlNext ring)
        (piR start.val.1)
        (.live (piR start.val.1)
          (bankRepairReaderInitialControl ring hbank start))
        word
        (piR (bankRepairReaderResidentTrace
          ring hbank start word).1.val.1)
        (.live (piR (bankRepairReaderResidentTrace
          ring hbank start word).1.val.1)
          (bankRepairReaderResidentTrace
            ring hbank start word).2)) ∧
    (∀ word : List (Fin n),
      bankRepairReaderResidentWordDone ring hbank start word →
      ∀ name : Fin n,
        (bankRepairReaderResidentTrace
          ring hbank start word).2.inheritedNames name = false) ∧
    (∀ word : List (Fin n),
      ¬ bankRepairReaderResidentWordDone ring hbank start word →
      1 + (List.ofFn (fun e : Fin n =>
        bankRepairReaderResidentWordDebt ring hbank start
          (word ++ [e]))).sum ≤
        n * bankRepairReaderResidentWordDebt
          ring hbank start word)

/-- The actual BlockA.Run and zero-H certificate are sufficient
to produce the previously defined physical retirement target.
The initializer is the exact installed bankRepairReaderInitialControl. -/
theorem bankRepairReaderResidentDoneCertifies {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hrows : BankRepairResidentRetirementOwnerRows ring hbank)
    (start : BankReferenceState ring hbank)
    (hW : BankRepairWAccepted ring hbank start)
    (word : List (Fin n))
    (hdone : bankRepairReaderResidentWordDone ring hbank start word) :
    BankRepairReaderRetiredFrom ring hbank start
      (word.foldl (bankRepairNext ring hbank) start) := by
  obtain ⟨hrun, hnames, _⟩ := hrows start hW
  have hphysical := bankRepairReaderResidentTracePhysical
    ring hbank start word
  have hactualRun := hrun word
  rw [hphysical] at hactualRun
  have hd :
      (bankRepairReaderResidentTrace
        ring hbank start word).2.phase = .done := hdone
  exact ⟨word,
    .live (piR start.val.1)
      (bankRepairReaderInitialControl ring hbank start),
    (bankRepairReaderResidentTrace ring hbank start word).2,
    rfl,
    bankRepairReaderInitializesAtW ring hbank start hW,
    hactualRun, hd, hnames word hdone⟩

/-- General word-carrier comparison: if the proof-only word
target certifies the ORIGINAL physical target, its first-hit
charge can only exceed that of the physical target. All
successor edges are still the same Fin n letters. -/
private theorem bankRepairReaderResidentPhysicalWordCostLe {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (start : BankReferenceState ring hbank)
    (Q : List (Fin n) → Prop)
    (hQP : ∀ word : List (Fin n), Q word →
      BankRepairReaderRetiredFrom ring hbank start
        (word.foldl (bankRepairNext ring hbank) start))
    (word : List (Fin n)) (T : Nat) :
    costNumerator (bankRepairNext ring hbank)
      (BankRepairReaderRetiredFrom ring hbank start)
      (word.foldl (bankRepairNext ring hbank) start) T ≤
    costNumerator
      (fun (w : List (Fin n)) (e : Fin n) => w ++ [e])
      Q word T := by
  classical
  induction T generalizing word with
  | zero =>
      simp only [costNumerator_zero]
      exact Nat.le_refl 0
  | succ T ih =>
      by_cases hp : BankRepairReaderRetiredFrom
          ring hbank start
          (word.foldl (bankRepairNext ring hbank) start)
      · rw [costNumerator_terminal
          (bankRepairNext ring hbank)
          (BankRepairReaderRetiredFrom ring hbank start)
          (word.foldl (bankRepairNext ring hbank) start)
          hp (T + 1)]
        exact Nat.zero_le _
      · have hq : ¬ Q word := by
          intro h
          exact hp (hQP word h)
        rw [costNumerator_succ
          (bankRepairNext ring hbank)
          (BankRepairReaderRetiredFrom ring hbank start)
          (word.foldl (bankRepairNext ring hbank) start)
          hp T]
        rw [costNumerator_succ
          (fun (w : List (Fin n)) (e : Fin n) => w ++ [e])
          Q word hq T]
        have hsum := ofFn_sum_le
          (fun e : Fin n =>
            costNumerator (bankRepairNext ring hbank)
              (BankRepairReaderRetiredFrom ring hbank start)
              (bankRepairNext ring hbank
                (word.foldl (bankRepairNext ring hbank) start) e) T)
          (fun e : Fin n =>
            costNumerator
              (fun (w : List (Fin n)) (f : Fin n) => w ++ [f])
              Q (word ++ [e]) T)
          (fun e => by
            have h := ih (word ++ [e])
            simpa only [List.foldl_append, List.foldl_cons,
              List.foldl_nil] using h)
        exact Nat.add_le_add_left hsum (n ^ (T + 1))

/-- Source-level reduction of the exact ORIGINAL target.
The only added input is the single named physical owner-row
obligation above. No unconstrained terminal witness is used. -/
theorem bankRepairResidentRetirementClockOfOwnerRows {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hrows : BankRepairResidentRetirementOwnerRows ring hbank) :
    BankRepairResidentRetirementClock ring hbank := by
  intro start hW T
  obtain ⟨_, _, hdrift⟩ := hrows start hW
  have hscaled :
      ∀ word : List (Fin n),
        ¬ bankRepairReaderResidentWordDone
          ring hbank start word →
        n + (List.ofFn (fun e : Fin n =>
          n * bankRepairReaderResidentWordDebt
            ring hbank start (word ++ [e]))).sum ≤
        n * (n * bankRepairReaderResidentWordDebt
          ring hbank start word) := by
    intro word hnot
    have hbase := hdrift word hnot
    have hm := Nat.mul_le_mul_left n hbase
    calc
      n + (List.ofFn (fun e : Fin n =>
          n * bankRepairReaderResidentWordDebt
            ring hbank start (word ++ [e]))).sum =
        n * (1 + (List.ofFn (fun e : Fin n =>
          bankRepairReaderResidentWordDebt
            ring hbank start (word ++ [e]))).sum) := by
          simp only [ofFn_sum_mul_left, Nat.mul_add, Nat.mul_one]
      _ ≤ n * (n * bankRepairReaderResidentWordDebt
          ring hbank start word) := hm
  have hword := Prob.costNumerator_le_of_potential
    (fun (word : List (Fin n)) (e : Fin n) => word ++ [e])
    (bankRepairReaderResidentWordDone ring hbank start)
    (fun word => n * bankRepairReaderResidentWordDebt
      ring hbank start word) hscaled
  have hcap :
      bankRepairReaderResidentWordDebt
          ring hbank start [] ≤
        n * ceilLogTwo (ceilLogTwo n) := by
    have hc := bankRepairReaderResidentPotentialCap
      (piR start.val.1)
      (bankRepairReaderInitialControl ring hbank start)
      ring.hn (bankRepairReaderCompiledWidthPos hbank)
    change
      bankRepairReaderResidentWordDebt
          ring hbank start [] ≤
        n * (compileAdvice (ceilLogTwo n)).t at hc
    rw [bankRepairReaderCompiledWidth hbank] at hc
    exact hc
  have hbound :
      n * bankRepairReaderResidentWordDebt
          ring hbank start [] ≤
        ceilLogTwo (ceilLogTwo n) * n ^ 2 := by
    calc
      n * bankRepairReaderResidentWordDebt
          ring hbank start [] ≤
        n * (n * ceilLogTwo (ceilLogTwo n)) :=
          Nat.mul_le_mul_left n hcap
      _ = ceilLogTwo (ceilLogTwo n) * n ^ 2 := by
        rw [Nat.pow_two]
        ac_rfl
  have hphysical := bankRepairReaderResidentPhysicalWordCostLe
    ring hbank start
    (bankRepairReaderResidentWordDone ring hbank start)
    (fun word hdone =>
      bankRepairReaderResidentDoneCertifies
        ring hbank hrows start hW word hdone) [] T
  have hcost :
      costNumerator (bankRepairNext ring hbank)
        (BankRepairReaderRetiredFrom ring hbank start)
        start T ≤
      n ^ T * (ceilLogTwo (ceilLogTwo n) * n ^ 2) := by
    calc
      costNumerator (bankRepairNext ring hbank)
          (BankRepairReaderRetiredFrom ring hbank start)
          start T ≤
        costNumerator
          (fun (w : List (Fin n)) (e : Fin n) => w ++ [e])
          (bankRepairReaderResidentWordDone ring hbank start)
          [] T := hphysical
      _ ≤ n ^ T * (n * bankRepairReaderResidentWordDebt
          ring hbank start []) := hword [] T
      _ ≤ n ^ T * (ceilLogTwo (ceilLogTwo n) * n ^ 2) :=
          Nat.mul_le_mul_left (n ^ T) hbound
  have hdouble := Nat.mul_le_mul_left 2 hcost
  calc
    2 * costNumerator (bankRepairNext ring hbank)
        (BankRepairReaderRetiredFrom ring hbank start)
        start T ≤
      2 * (n ^ T * (ceilLogTwo (ceilLogTwo n) * n ^ 2)) :=
        hdouble
    _ = n ^ T *
        ((2 * ceilLogTwo (ceilLogTwo n)) * n ^ 2) := by
      ac_rfl

end L3.RenewalReferenceClock

/-!
Reachable E.G22 six-row audit.

All local proofs below concern
the genuine phiR/BlockA.readerControlNext selected edge.
The six numeric row cases are independent of the E.G22
terminal safety question. One named open Prop isolates the
remaining reachable terminal-marker/recurrence obligation.

Closure.readerMoveFoldValid and readerKickLaunchFoldValid
already implement the five-fold append and singleton arithmetic.
The proofs here permit inherited tokens to remain inherited,
instead of assuming every occupied OLD slot already has a
fresh tag (which is false before E.G19 retirement).
-/

namespace L3.RenewalReferenceClock

open L3.HeadlineRenewal
open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree

set_option autoImplicit false
set_option Elab.async false

/-- BANK implies the ring has at least two physical edges.
This fact is needed for the distinct source/responder R0/R1 patch. -/
theorem bankRepairReaderE22BankSize {n : Nat}
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) :
    2 ≤ n := by
  have hband := bankRepairBankBand hbank
  by_cases hn : n ≤ 1
  · have hz : ceilLogTwo n = 0 := by
      simp [ceilLogTwo, hn]
    omega
  · omega

/-- A site-specific version of the exact first E22Evidence field. -/
def BankRepairReaderE22FreshSite {n : Nat}
    (p : Fin n → ProjR (compileAdvice (ceilLogTwo n)))
    (h : BlockA.ReaderControl n
      (compileAdvice (ceilLogTwo n)))
    (i : Fin n) : Prop :=
  ∀ (name : Fin n)
    (index : Fin ((compileAdvice (ceilLogTwo n)).t + 1))
    (samples : BlockA.FiniteLedger (BlockA.ReaderSample n)
      (compileAdvice (ceilLogTwo n)).t),
    h.tags i = .fresh name index samples →
    samples.count = index ∧
      Closure.readerFoldValid (ceilLogTwo n) n
        i (p i).rawTok index samples

/-- A framed, numerically unchanged OLD fresh tag remains exact. -/
theorem bankRepairReaderE22RetainedFresh {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (p : Fin n → ProjR (compileAdvice (ceilLogTwo n)))
    (h : BlockA.ReaderControl n
      (compileAdvice (ceilLogTwo n)))
    (e i : Fin n)
    (hev : BankRepairReaderE22Evidence ring hbank p h)
    (hraw : ((phiR ring p e) i).rawTok = (p i).rawTok)
    (htag :
      (BlockA.readerControlNext ring h p e (phiR ring p e)).tags i =
        h.tags i) :
    BankRepairReaderE22FreshSite
      (phiR ring p e)
      (BlockA.readerControlNext ring h p e (phiR ring p e)) i := by
  intro name index samples hnew
  rw [htag] at hnew
  have hold := hev.1 i name index samples hnew
  constructor
  · exact hold.1
  · rw [hraw]
    exact hold.2

/-- An erased tag cannot witness a fresh E.G22 ledger. -/
theorem bankRepairReaderE22EmptyFresh {n : Nat}
    (p : Fin n → ProjR (compileAdvice (ceilLogTwo n)))
    (h : BlockA.ReaderControl n
      (compileAdvice (ceilLogTwo n)))
    (i : Fin n)
    (hempty : h.tags i = .empty) :
    BankRepairReaderE22FreshSite p h i := by
  intro name index samples hfresh
  rw [hempty] at hfresh
  cases hfresh

/-- R0a: collision deletes the source and retains the OLD
responder's physical token and numerical ledger unchanged. -/
theorem bankRepairReaderE22CollisionFresh {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (p : Fin n → ProjR (compileAdvice (ceilLogTwo n)))
    (h : BlockA.ReaderControl n
      (compileAdvice (ceilLogTwo n)))
    (e : Fin n)
    (old resident : RawTok (compileAdvice (ceilLogTwo n)).t)
    (hx : (p e).rawTok = some old)
    (hy : (p (ring.rightNeighbor e)).rawTok = some resident)
    (hev : BankRepairReaderE22Evidence ring hbank p h) :
    BankRepairReaderE22FreshSite
      (phiR ring p e)
      (BlockA.readerControlNext ring h p e (phiR ring p e))
      (ring.rightNeighbor e) := by
  have hne := EWord.rightNeighborDifferent ring
    (bankRepairReaderE22BankSize hbank) e
  have hrow := Closure.readerCollisionRow
    (p e) (p (ring.rightNeighbor e)) old resident hx hy
  have hraw :
      ((phiR ring p e) (ring.rightNeighbor e)).rawTok =
        (p (ring.rightNeighbor e)).rawTok := by
    rw [Closure.readerProjectedDestinationRaw ring p e hne,
      hrow.2.1, hy]
  have htag := Closure.readerDestinationRetained ring p h e
    hne (Or.inl hrow.2.2)
  exact bankRepairReaderE22RetainedFresh
    ring hbank p h e (ring.rightNeighbor e) hev hraw htag

/-- R0b: an inherited OLD tag remains inherited, while an OLD
fresh tag extends its ledger by precisely the selected OLD sample. -/
theorem bankRepairReaderE22MoveFresh {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (p : Fin n → ProjR (compileAdvice (ceilLogTwo n)))
    (h : BlockA.ReaderControl n
      (compileAdvice (ceilLogTwo n)))
    (e : Fin n)
    (old : RawTok (compileAdvice (ceilLogTwo n)).t)
    (hx : (p e).rawTok = some old)
    (hy : (p (ring.rightNeighbor e)).rawTok = none)
    (hmore : old.j < (compileAdvice (ceilLogTwo n)).t)
    (hwf : Closure.ReaderGhostWellFormed p h)
    (hev : BankRepairReaderE22Evidence ring hbank p h) :
    BankRepairReaderE22FreshSite
      (phiR ring p e)
      (BlockA.readerControlNext ring h p e (phiR ring p e))
      (ring.rightNeighbor e) := by
  have hne := EWord.rightNeighborDifferent ring
    (bankRepairReaderE22BankSize hbank) e
  have hrow := Closure.readerMoveRow
    (p e) (p (ring.rightNeighbor e)) old hx hy hmore
  have hdst := Closure.readerDestinationMoved ring p h e
    hne hrow.2.2
  cases hsource : h.tags e with
  | empty =>
      have hbad : (p e).rawTok = none :=
        (Closure.readerGhostTagSupport p h hwf e).1 hsource
      rw [hx] at hbad
      cases hbad
  | inherited oldName =>
      intro name index samples hnew
      rw [hdst, hsource] at hnew
      change BlockA.RawTag.inherited oldName =
        .fresh name index samples at hnew
      cases hnew
  | fresh oldName oldIndex oldSamples =>
      have hvalid := (hev.1 e oldName oldIndex oldSamples hsource).2
      rw [hx] at hvalid
      have hcursor := Closure.readerFoldCursor
        (q := ceilLogTwo n) e old oldIndex oldSamples hvalid
      have hindex :
          oldIndex.val < (compileAdvice (ceilLogTwo n)).t := by
        omega
      obtain ⟨nextIndex, hnext, hvalidNew⟩ :=
        Closure.readerMoveFoldValid (q := ceilLogTwo n)
          e (ring.rightNeighbor e) (p e)
          (p (ring.rightNeighbor e)) old oldIndex oldSamples
          hx hy hmore hvalid
      have hindexEq :
          (⟨oldIndex.val + 1, by omega⟩ :
            Fin ((compileAdvice (ceilLogTwo n)).t + 1)) =
              nextIndex := by
        apply Fin.ext
        exact hnext.symm
      have htagNext :
          (BlockA.readerControlNext ring h p e
            (phiR ring p e)).tags (ring.rightNeighbor e) =
          .fresh oldName nextIndex
            (oldSamples.push
              (BlockA.readerSelectedSample
                (ring.rightNeighbor e) (p e)
                (p (ring.rightNeighbor e)))) := by
        rw [hdst, hsource]
        change BlockA.readerTransfer
          (.fresh oldName oldIndex oldSamples)
          (BlockA.readerSelectedSample
            (ring.rightNeighbor e) (p e)
            (p (ring.rightNeighbor e))) = _
        simp [BlockA.readerTransfer, hindex, hindexEq]
      have hcountNew :
          (oldSamples.push
            (BlockA.readerSelectedSample
              (ring.rightNeighbor e) (p e)
              (p (ring.rightNeighbor e)))).count =
              nextIndex :=
        Closure.readerFoldCount (q := ceilLogTwo n)
          (ring.rightNeighbor e)
          (pairR (p e) (p (ring.rightNeighbor e))).2.rawTok
          nextIndex
          (oldSamples.push
            (BlockA.readerSelectedSample
              (ring.rightNeighbor e) (p e)
              (p (ring.rightNeighbor e)))) hvalidNew
      intro name index samples hnew
      rw [htagNext] at hnew
      cases hnew
      constructor
      · exact hcountNew
      · rw [Closure.readerProjectedDestinationRaw ring p e hne]
        exact hvalidNew

/-- R0c: terminal erases both physical token slots and the
selected destination tag. No terminal tag survives this edge. -/
theorem bankRepairReaderE22TerminalFresh {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (p : Fin n → ProjR (compileAdvice (ceilLogTwo n)))
    (h : BlockA.ReaderControl n
      (compileAdvice (ceilLogTwo n)))
    (e : Fin n)
    (old : RawTok (compileAdvice (ceilLogTwo n)).t)
    (hx : (p e).rawTok = some old)
    (hy : (p (ring.rightNeighbor e)).rawTok = none)
    (hterminal : ¬ old.j < (compileAdvice (ceilLogTwo n)).t) :
    BankRepairReaderE22FreshSite
      (phiR ring p e)
      (BlockA.readerControlNext ring h p e (phiR ring p e))
      (ring.rightNeighbor e) := by
  have hne := EWord.rightNeighborDifferent ring
    (bankRepairReaderE22BankSize hbank) e
  have hrow := Closure.readerTerminalRow
    (p e) (p (ring.rightNeighbor e)) old hx hy hterminal
  exact bankRepairReaderE22EmptyFresh _ _ _
    (Closure.readerDestinationTerminal ring p h e hne hrow.2.2)

/-- R1a: no OLD source token; the resident responder and its
complete fresh evidence (if fresh) remain unchanged. -/
theorem bankRepairReaderE22ResidentFresh {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (p : Fin n → ProjR (compileAdvice (ceilLogTwo n)))
    (h : BlockA.ReaderControl n
      (compileAdvice (ceilLogTwo n)))
    (e : Fin n)
    (resident : RawTok (compileAdvice (ceilLogTwo n)).t)
    (hx : (p e).rawTok = none)
    (hy : (p (ring.rightNeighbor e)).rawTok = some resident)
    (hev : BankRepairReaderE22Evidence ring hbank p h) :
    BankRepairReaderE22FreshSite
      (phiR ring p e)
      (BlockA.readerControlNext ring h p e (phiR ring p e))
      (ring.rightNeighbor e) := by
  have hne := EWord.rightNeighborDifferent ring
    (bankRepairReaderE22BankSize hbank) e
  have hrow := Closure.readerResidentRow
    (p e) (p (ring.rightNeighbor e)) resident hx hy
  have hraw :
      ((phiR ring p e) (ring.rightNeighbor e)).rawTok =
        (p (ring.rightNeighbor e)).rawTok := by
    rw [Closure.readerProjectedDestinationRaw ring p e hne,
      hrow.2.1, hy]
  have htag := Closure.readerDestinationRetained ring p h e
    hne (Or.inr (Or.inl hrow.2.2))
  exact bankRepairReaderE22RetainedFresh
    ring hbank p h e (ring.rightNeighbor e) hev hraw htag

/-- R1b: a kick-arm service cannot create a fresh tag. -/
theorem bankRepairReaderE22KickArmFresh {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (p : Fin n → ProjR (compileAdvice (ceilLogTwo n)))
    (h : BlockA.ReaderControl n
      (compileAdvice (ceilLogTwo n)))
    (e : Fin n)
    (hx : (p e).rawTok = none)
    (hy : (p (ring.rightNeighbor e)).rawTok = none)
    (hk : (p (ring.rightNeighbor e)).rawKick = false)
    (hwf : Closure.ReaderGhostWellFormed p h) :
    BankRepairReaderE22FreshSite
      (phiR ring p e)
      (BlockA.readerControlNext ring h p e (phiR ring p e))
      (ring.rightNeighbor e) := by
  have hne := EWord.rightNeighborDifferent ring
    (bankRepairReaderE22BankSize hbank) e
  have hrow := Closure.readerKickArmRow
    (p e) (p (ring.rightNeighbor e)) hx hy hk
  have hzero : h.tags (ring.rightNeighbor e) = .empty :=
    (Closure.readerGhostTagSupport p h hwf
      (ring.rightNeighbor e)).2 hy
  have htag :
      (BlockA.readerControlNext ring h p e
        (phiR ring p e)).tags (ring.rightNeighbor e) = .empty := by
    rw [Closure.readerDestinationRetained ring p h e
      hne (Or.inr (Or.inr hrow.2.2))]
    exact hzero
  exact bankRepairReaderE22EmptyFresh _ _ _ htag

/-- R1c: launch takes exactly the selected OLD responder sample,
allocates a genuinely unused name, and satisfies all five folds. -/
theorem bankRepairReaderE22KickLaunchFresh {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (p : Fin n → ProjR (compileAdvice (ceilLogTwo n)))
    (h : BlockA.ReaderControl n
      (compileAdvice (ceilLogTwo n)))
    (e : Fin n)
    (hx : (p e).rawTok = none)
    (hy : (p (ring.rightNeighbor e)).rawTok = none)
    (hk : (p (ring.rightNeighbor e)).rawKick = true)
    (hwf : Closure.ReaderGhostWellFormed p h) :
    BankRepairReaderE22FreshSite
      (phiR ring p e)
      (BlockA.readerControlNext ring h p e (phiR ring p e))
      (ring.rightNeighbor e) := by
  have hne := EWord.rightNeighborDifferent ring
    (bankRepairReaderE22BankSize hbank) e
  have ht := bankRepairReaderCompiledWidthPos hbank
  have hrow := Closure.readerKickLaunchRow
    (p e) (p (ring.rightNeighbor e)) hx hy hk ht
  obtain ⟨chosen, hchoose⟩ :=
    Closure.readerKickLaunchNameAvailable ring p h e
      hwf hx hy hk ht
  have htag := Closure.readerDestinationFresh ring p h
    e chosen hne hrow.2.2 hchoose ht
  have hvalid := Closure.readerKickLaunchFoldValid
    (q := ceilLogTwo n) (ring.rightNeighbor e)
    (p e) (p (ring.rightNeighbor e)) hx hy hk ht
  have hcount :
      (({ count := ⟨0, by omega⟩, entries := fun _ => none } :
        BlockA.FiniteLedger (BlockA.ReaderSample n)
          (compileAdvice (ceilLogTwo n)).t).push
        (BlockA.readerSelectedSample
          (ring.rightNeighbor e) (p e)
          (p (ring.rightNeighbor e)))).count =
          (⟨1, by omega⟩ :
            Fin ((compileAdvice (ceilLogTwo n)).t + 1)) := by
    simp [BlockA.FiniteLedger.push, ht]
  intro name index samples hfresh
  rw [htag] at hfresh
  cases hfresh
  constructor
  · exact hcount
  · rw [Closure.readerProjectedDestinationRaw ring p e hne]
    exact hvalid

/-- The six source/destination owner rows and the remote frame
preserve the numerical first E22Evidence conjunct. This does
not silently assume that inherited tokens are fresh. -/
theorem bankRepairReaderE22FreshStep {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (p : Fin n → ProjR (compileAdvice (ceilLogTwo n)))
    (h : BlockA.ReaderControl n
      (compileAdvice (ceilLogTwo n)))
    (e : Fin n)
    (hwf : Closure.ReaderGhostWellFormed p h)
    (hev : BankRepairReaderE22Evidence ring hbank p h) :
    ∀ i : Fin n,
      BankRepairReaderE22FreshSite
        (phiR ring p e)
        (BlockA.readerControlNext ring h p e (phiR ring p e))
        i := by
  intro i
  by_cases hi : i = e
  · subst i
    exact bankRepairReaderE22EmptyFresh _ _ _
      (Closure.readerSourceTagCleared ring h p e hwf)
  · by_cases hj : i = ring.rightNeighbor e
    · subst i
      cases hx : (p e).rawTok with
      | some old =>
          cases hy : (p (ring.rightNeighbor e)).rawTok with
          | some resident =>
              exact bankRepairReaderE22CollisionFresh
                ring hbank p h e old resident hx hy hev
          | none =>
              by_cases hmore :
                  old.j < (compileAdvice (ceilLogTwo n)).t
              · exact bankRepairReaderE22MoveFresh
                  ring hbank p h e old hx hy hmore hwf hev
              · exact bankRepairReaderE22TerminalFresh
                  ring hbank p h e old hx hy hmore
      | none =>
          cases hy : (p (ring.rightNeighbor e)).rawTok with
          | some resident =>
              exact bankRepairReaderE22ResidentFresh
                ring hbank p h e resident hx hy hev
          | none =>
              cases hk : (p (ring.rightNeighbor e)).rawKick with
              | false =>
                  exact bankRepairReaderE22KickArmFresh
                    ring hbank p h e hx hy hk hwf
              | true =>
                  exact bankRepairReaderE22KickLaunchFresh
                    ring hbank p h e hx hy hk hwf
    · exact bankRepairReaderE22RetainedFresh
        ring hbank p h e i hev
        (Closure.readerProjectedRemoteFrame ring p e i hi hj)
        (Closure.readerTagRemoteFrame ring p h e i hi hj)

/-- THE ONE OPEN REACHABILITY FACT.

On an ACTUAL reader Run beginning at a W-accepted endpoint,
each fresh FULL terminal seen after an R0/R1 step must have
both marker error and terminal lower-test error absent. The
Boolean equality is exactly the R0c rawReject guard. It
requires W-origin information about sampled marker/beta and
the adjacent recurrence word, not merely the numerical fold
equalities. It is stronger than old.m=false alone because
lowerBad is another independent R0c rejection reason.

Local obstruction (not claimed reachable, and n=5 lies
outside the BANK band): n=5, root=0, edge 0->1, reader width
t=2, OLD source token jm1=1 (j=2), m=true, destination
rawTok=none. The row is terminal R0c, and its OR guard
rejects regardless of z/p/a/h or destination word bits.
The installed bankRepairReaderTerminalMarkerReject theorem
certifies this local raw owner computation. -/
def BankRepairReaderE22TerminalMarkerReachability {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) :
    Prop :=
  ∀ (start : BankReferenceState ring hbank)
    (initial : BlockA.Decoration
      (Fin n → ProjR (compileAdvice (ceilLogTwo n)))
      (BlockA.ReaderControl n
        (compileAdvice (ceilLogTwo n))))
    (word : List (Fin n))
    (p : Fin n → ProjR (compileAdvice (ceilLogTwo n)))
    (h : BlockA.ReaderControl n
      (compileAdvice (ceilLogTwo n)))
    (e : Fin n),
    BankRepairWAccepted ring hbank start →
    BlockA.initializesReader
      (AcceptedReceipts.AcceptedWord ring
        (BlockA.wordT ring) (BlockA.wordValidated ring))
      (piR start.val.1) initial →
    BlockA.Run ring (phiR ring)
      (BlockA.readerControlNext ring)
      (piR start.val.1) initial word p (.live p h) →
    BankRepairReaderE22Invariant ring hbank p h →
    ∀ (site : Fin n)
      (old : RawTok (compileAdvice (ceilLogTwo n)).t)
      (name : Fin n)
      (index : Fin ((compileAdvice (ceilLogTwo n)).t + 1))
      (samples : BlockA.FiniteLedger (BlockA.ReaderSample n)
        (compileAdvice (ceilLogTwo n)).t),
      ((phiR ring p e) site).rawTok = some old →
      ((phiR ring p e) (ring.rightNeighbor site)).rawTok = none →
      ¬ old.j < (compileAdvice (ceilLogTwo n)).t →
      (BlockA.readerControlNext ring h p e
        (phiR ring p e)).tags site =
        .fresh name index samples →
      (old.m ||
        (!(old.h ||
          (postW ((phiR ring p e) site).word
            ((phiR ring p e) (ring.rightNeighbor site)).word).eY.l) &&
          (!old.z ||
            (((phiR ring p e) (ring.rightNeighbor site)).word.u !=
              old.p)))) = false

/-- Explicit small token realizing the OLD terminal-marker error.
No W-accepted global execution is asserted from this token. -/
def bankRepairReaderE22BadTerminalSmall : RawTok 2 :=
  { jm1 := ⟨1, by omega⟩
    z := false
    p := false
    a := false
    h := false
    m := true }

/-- At width two the old index is terminal and the marker is true. -/
theorem bankRepairReaderE22BadTerminalSmallFacts :
    bankRepairReaderE22BadTerminalSmall.j = 2 ∧
      bankRepairReaderE22BadTerminalSmall.m = true := by
  constructor <;> rfl

/-- The literal n=5 port pair for the local diagnostic. -/
theorem bankRepairReaderE22BadTerminalSmallEdge :
    (DirectedRing.rightNeighbor
      (⟨by omega⟩ : DirectedRing 5)
      (⟨0, by omega⟩ : Fin 5)) =
        (⟨1, by omega⟩ : Fin 5) := by
  rfl

/-- The old marker alone forces failure of the exact R0c
guard independently of other sampled fields. -/
theorem bankRepairReaderE22BadMarkerBoolean
    (z p a h u g : Bool) :
    ¬ ((true ||
        (!(h || g) && (!z || (u != p)))) = false) := by
  cases z <;> cases p <;> cases a <;> cases h <;>
    cases u <;> cases g <;> decide

/-- Conditional assembly of the original exact E22 row statement.
No numerical evidence is postulated beyond the six proved
local row cases; the remaining premise is ONLY terminal-marker
reachability from the W-origin Run. -/
theorem bankRepairReaderE22RowPreservationOfMarkerReachability
    {n : Nat} (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hmarker :
      BankRepairReaderE22TerminalMarkerReachability ring hbank) :
    BankRepairReaderE22RowPreservation ring hbank := by
  intro start initial word p h e hW hinit hrun hI
  have hword :
      AcceptedReceipts.AcceptedWord ring
        (BlockA.wordT ring) (BlockA.wordValidated ring)
        (fun i => ((phiR ring p e) i).word) := by
    change AcceptedReceipts.AcceptedWord ring
      (BlockA.wordT ring) (BlockA.wordValidated ring)
      (AcceptedReceipts.wordProjectionR (phiR ring p e))
    rw [AcceptedReceipts.wordProjectionR_phiR]
    exact AcceptedReceipts.accepted_word_phi_step
      ring (AcceptedReceipts.wordProjectionR p) e hI.1
  have hghost := Closure.readerGhostWellFormedStep
    (bankRepairReaderE22BankSize hbank)
    (bankRepairReaderCompiledWidthPos hbank)
    ring p h e hI.2.1
  have hnumeric := bankRepairReaderE22FreshStep
    ring hbank p h e hI.2.1 hI.2.2
  refine ⟨hword, hghost, ⟨?_, ?_⟩⟩
  · intro i name index samples htag
    exact hnumeric i name index samples htag
  · intro site old name index samples hx hy hterminal htag
    have hguard := hmarker start initial word p h e
      hW hinit hrun hI site old name index samples
      hx hy hterminal htag
    simpa [rawR, rawD1Step, ProjR.lift, ProjW.lift,
      hx, hy, hterminal] using hguard

/-- Consequently the already FoldSound reduction applies
whenever the single terminal-marker reachability fact is provided. -/
theorem bankRepairReaderFoldSoundOfMarkerReachability
    {n : Nat} (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hmarker :
      BankRepairReaderE22TerminalMarkerReachability ring hbank) :
    BankRepairReaderFoldSound ring hbank := by
  exact bankRepairReaderFoldSoundOfE22Rows ring hbank
    (bankRepairReaderE22RowPreservationOfMarkerReachability
      ring hbank hmarker)

end L3.RenewalReferenceClock



/-!
R0c terminal marker: completed root-touch branch and
exact no-root sampled-word residual.

The selected R1c/R0b five-fold receipts already prove that every
reachable fresh token has the actual physical raw fields equal to
the numerical sampled folds (bankRepairReaderE22FreshStep).
The fifth fold forces m=false whenever the recorded samples
have touched a root (h=true). Then BOTH disjuncts of the
literal R0c rejection guard are false, without any extra
history or data assumptions. This closes an entire branch
of the proposed new-row proof.

The remaining branch is h=false. It needs a causal, stable
word-window invariant tying the sampled OLD u/beta ledger
to the current AcceptedWord. The exact two obligations are:
  marker: old.m=false at completion;
  recurrence: when the next POST-E responder is not a leader,
      old.z=true and the next OLD u equals old.p.
These are not consequences of readerFoldValid alone: that
predicate checks five accumulator equations and the last
sample's site, but not every earlier sample's cyclic position
or its equality with the immutable accepted W word. Arbitrary
fabricated fresh sample arrays would be unsound witnesses.

The state predicate below expresses the outstanding h=false
window relation. It holds vacuously at the genuine W-cut
initializer (all tokens are inherited or empty). A named
reachable-next producer is left open; its proof must use the
actual old-sample movement/launch rows, cyclic position,
accepted W publication and QWord visibility stability.
The conditional handoff into the existing E22 and FoldSound
targets is proved, without asserting the missing producer.
-/

namespace L3.RenewalReferenceClock

open L3.HeadlineRenewal
open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree

set_option autoImplicit false
set_option Elab.async false

/-- The fifth receipt fold cannot report a marker mismatch
after any sampled root touch. This holds for all widths and
all finite sample arrays, without a sampled-word assumption. -/
private theorem bankRepairReaderMarkerErrorRootTouch
    {n : Nat} (c : Compiled)
    (reads : List (BlockA.ReaderSample n))
    (htouch : Closure.readerSampleRootTouch reads = true) :
    Closure.readerSampleMarkerError c reads = false := by
  unfold Closure.readerSampleMarkerError
  split
  · cases hr : reads.reverse with
    | nil =>
        rfl
    | cons last rest =>
        simp [htouch]
  · rfl

/-- Even without a root touch, the marker error vanishes if
the actual last recorded OLD beta equals the full sampled AND.
The missing semantic step is to derive this equality from the
causal W-origin word, not to assume it of arbitrary samples. -/
private theorem bankRepairReaderMarkerErrorOfLastMatch
    {n : Nat} (c : Compiled)
    (reads : List (BlockA.ReaderSample n))
    (hmatch : ∀ last : BlockA.ReaderSample n,
      reads.reverse.head? = some last →
      last.oldMarker = Closure.readerSampleAnd reads) :
    Closure.readerSampleMarkerError c reads = false := by
  unfold Closure.readerSampleMarkerError
  split
  · cases hr : reads.reverse with
    | nil =>
        rfl
    | cons last rest =>
        have heq : last.oldMarker =
            Closure.readerSampleAnd reads :=
          hmatch last (by simp [hr])
        simp [heq]
  · rfl

/-- The existing five-fold readerFoldValid at a fresh
physical token forces m=false whenever its physical h=true.
The proof uses the genuine fifth (sample-marker) fold, not
a manufactured QReader assumption. -/
theorem bankRepairReaderFreshRootTouchNoMarker
    {q n : Nat}
    (site : Fin n)
    (old : RawTok (compileAdvice q).t)
    (index : Fin ((compileAdvice q).t + 1))
    (samples : BlockA.FiniteLedger (BlockA.ReaderSample n)
      (compileAdvice q).t)
    (hvalid : Closure.readerFoldValid q n
      site (some old) index samples)
    (htouch : old.h = true) :
    old.m = false := by
  dsimp [Closure.readerFoldValid] at hvalid
  obtain ⟨_hcount, _hindex, reads, _hreads, _hlength,
    _hlast, _hz, _hp, _ha, hh, hm⟩ := hvalid
  have hfold : Closure.readerSampleRootTouch reads = true :=
    hh.symm.trans htouch
  rw [hm]
  exact bankRepairReaderMarkerErrorRootTouch
    (compileAdvice q) reads hfold

/-- The full R0c Boolean is false when a valid terminal token
has touched a root: the root-touch flag suppresses lowerBad,
and the sample fold suppresses m. The neighbor's current
word may otherwise be arbitrary. -/
theorem bankRepairReaderRootTouchTerminalGuard
    {n : Nat} {c : Compiled}
    (p : Fin n → ProjR c) (site : Fin n)
    (old : RawTok c.t)
    (htouch : old.h = true)
    (hmarker : old.m = false) :
    (old.m ||
      (!(old.h ||
        (postW (p site).word (p site).word).eY.l) &&
        (!old.z || ((p site).word.u != old.p)))) = false := by
  simp [htouch, hmarker]

/-- Root touch closes the requested terminal test at the
ACTUAL successor of any E22Invariant state. The genuine
readerControlNext produces a new fresh token only through
the six already proved R0/R1 cases; we use their local
numerical preservation, not a free-standing fake ledger. -/
theorem bankRepairReaderE22NextFreshRootTouchSafe
    {n : Nat} (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (p : Fin n → ProjR (compileAdvice (ceilLogTwo n)))
    (h : BlockA.ReaderControl n
      (compileAdvice (ceilLogTwo n)))
    (e site : Fin n)
    (old : RawTok (compileAdvice (ceilLogTwo n)).t)
    (name : Fin n)
    (index : Fin ((compileAdvice (ceilLogTwo n)).t + 1))
    (samples : BlockA.FiniteLedger (BlockA.ReaderSample n)
      (compileAdvice (ceilLogTwo n)).t)
    (hI : BankRepairReaderE22Invariant ring hbank p h)
    (hraw : ((phiR ring p e) site).rawTok = some old)
    (htag :
      (BlockA.readerControlNext ring h p e (phiR ring p e)).tags site =
        .fresh name index samples)
    (htouch : old.h = true) :
    (old.m ||
      (!(old.h ||
        (postW ((phiR ring p e) site).word
          ((phiR ring p e) (ring.rightNeighbor site)).word).eY.l) &&
        (!old.z ||
          (((phiR ring p e) (ring.rightNeighbor site)).word.u !=
            old.p)))) = false := by
  have hfresh := (bankRepairReaderE22FreshStep
    ring hbank p h e hI.2.1 hI.2.2 site)
      name index samples htag
  have hvalid : Closure.readerFoldValid (ceilLogTwo n) n
      site (some old) index samples := by
    have hh := hfresh.2
    rw [hraw] at hh
    exact hh
  have hm := bankRepairReaderFreshRootTouchNoMarker
    site old index samples hvalid htouch
  simp [htouch, hm]

/-- The one remaining no-root terminal source class, phrased
on the actual physical reader configuration and E.G20 control.
A fresh terminal with h=false needs an authentic immutable
accepted-word marker and, when the next responder is not a
leader, the recurrence parity of the first t old reads.
The five-fold equality alone does NOT prove this. -/
def BankRepairReaderE22NoRootWindow {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (p : Fin n → ProjR (compileAdvice (ceilLogTwo n)))
    (h : BlockA.ReaderControl n
      (compileAdvice (ceilLogTwo n))) : Prop :=
  ∀ (site : Fin n)
    (old : RawTok (compileAdvice (ceilLogTwo n)).t)
    (name : Fin n)
    (index : Fin ((compileAdvice (ceilLogTwo n)).t + 1))
    (samples : BlockA.FiniteLedger (BlockA.ReaderSample n)
      (compileAdvice (ceilLogTwo n)).t),
    (p site).rawTok = some old →
    (p (ring.rightNeighbor site)).rawTok = none →
    ¬ old.j < (compileAdvice (ceilLogTwo n)).t →
    h.tags site = .fresh name index samples →
    old.h = false →
    old.m = false ∧
      ((postW (p site).word
        (p (ring.rightNeighbor site)).word).eY.l = false →
        old.z = true ∧
          (p (ring.rightNeighbor site)).word.u = old.p)

/-- At the actual W-accepted reader initialization, no fresh
sample ledger exists. Thus the no-root word obligation is
true before any R1c launch, regardless of inherited OLD
tokens and arbitrary inherited marker bits. -/
theorem bankRepairReaderE22NoRootWindowInitial
    {n : Nat} (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (p : Fin n → ProjR (compileAdvice (ceilLogTwo n)))
    (h : BlockA.ReaderControl n
      (compileAdvice (ceilLogTwo n)))
    (hslots : ∀ i : Fin n,
      if (p i).rawTok.isSome = true then
        h.tags i = .inherited i ∧ h.inheritedNames i = true
      else h.tags i = .empty ∧ h.inheritedNames i = false) :
    BankRepairReaderE22NoRootWindow ring hbank p h := by
  intro site old name index samples _ _ _ htag _
  exact False.elim
    ((bankRepairReaderE22InitialNoFresh p h hslots)
      site name index samples htag)

/-- SOURCE GAP: a reachable OLD R0/R1 service must preserve
the no-root sampled-word relation, not merely the numerical
five-fold receipt. In the R0b case it requires chronological
sample-site adjacency, immutable W visible u/beta from QWord,
and the accepted prefix/recurrence publication equations.
R1c has only one read; framed and collision rows must
preserve the relevant source-to-current W correspondence.

The accepted W origin and actual BlockA.Run are retained as
premises; synthetic fresh ledgers are not admitted. This
single explicitly unproved Prop isolates the remaining
substantive per-row/history bridge. -/
def BankRepairReaderE22NoRootWindowReachability {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) : Prop :=
  ∀ (start : BankReferenceState ring hbank)
    (initial : BlockA.Decoration
      (Fin n → ProjR (compileAdvice (ceilLogTwo n)))
      (BlockA.ReaderControl n
        (compileAdvice (ceilLogTwo n))))
    (word : List (Fin n))
    (p : Fin n → ProjR (compileAdvice (ceilLogTwo n)))
    (h : BlockA.ReaderControl n
      (compileAdvice (ceilLogTwo n)))
    (e : Fin n),
    BankRepairWAccepted ring hbank start →
    BlockA.initializesReader
      (AcceptedReceipts.AcceptedWord ring
        (BlockA.wordT ring) (BlockA.wordValidated ring))
      (piR start.val.1) initial →
    BlockA.Run ring (phiR ring)
      (BlockA.readerControlNext ring)
      (piR start.val.1) initial word p (.live p h) →
    BankRepairReaderE22Invariant ring hbank p h →
    BankRepairReaderE22NoRootWindow ring hbank
      (phiR ring p e)
      (BlockA.readerControlNext ring h p e (phiR ring p e))

/-- All of the terminal marker statement now follows from the
single no-root W-origin sample-window producer. The root-touch
case was proved above without this producer. This is a
conditional reduction, NOT an unconditional E22 theorem. -/
theorem bankRepairReaderE22TerminalMarkerReachabilityOfNoRootWindow
    {n : Nat} (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hwindow :
      BankRepairReaderE22NoRootWindowReachability ring hbank) :
    BankRepairReaderE22TerminalMarkerReachability ring hbank := by
  intro start initial word p h e hW hinit hrun hI
    site old name index samples hraw hempty hterminal htag
  by_cases htouch : old.h = true
  · exact bankRepairReaderE22NextFreshRootTouchSafe
      ring hbank p h e site old name index samples
      hI hraw htag htouch
  · have hfalse : old.h = false := by
      cases hh : old.h with
      | false =>
          rfl
      | true =>
          exact False.elim (htouch hh)
    have hstate := hwindow start initial word p h e
      hW hinit hrun hI
    obtain ⟨hm, hrec⟩ :=
      hstate site old name index samples
        hraw hempty hterminal htag hfalse
    cases hg : (postW ((phiR ring p e) site).word
        ((phiR ring p e) (ring.rightNeighbor site)).word).eY.l with
    | true =>
        simp [hfalse, hm, hg]
    | false =>
        obtain ⟨hz, hp⟩ := hrec hg
        simp [hfalse, hm, hg, hz, hp]

/-- The original E.G22 full row and E.G23 FoldSound
interfaces follow from the same precise no-root producer.
This does not change the accepted source file or assert the
producer without a causal word proof. -/
theorem bankRepairReaderFoldSoundOfNoRootWindow
    {n : Nat} (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hwindow :
      BankRepairReaderE22NoRootWindowReachability ring hbank) :
    BankRepairReaderFoldSound ring hbank := by
  exact bankRepairReaderFoldSoundOfMarkerReachability ring hbank
    (bankRepairReaderE22TerminalMarkerReachabilityOfNoRootWindow
      ring hbank hwindow)

/-!
STATUS — MAIN TARGET NOT YET CLOSED.

Closed at source level:
* valid numerical fresh ledger + old.h=true -> old.m=false;
* therefore full R0c guard=false for every successor fresh
  terminal with root touch, independent of endpoint u/beta;
* initial no-root sampled-word invariant (no fresh tags);
* exact conditional handoff to E22TerminalMarkerReachability
  and BankRepairReaderFoldSound.

FIRST REMAINING ROW: a generated fresh full-width R0b token
with h=false (no sampled root), entering an OLD-empty responder
site. Its last genuine OLD beta sample must equal the AND fold;
if its next responder is a follower, the accepted-W
recurrence gives z=true and next OLD u=parity p. Both require
the chronological sampled-site window, not just a finite
numeric readerFoldValid certificate.

This is precisely BankRepairReaderE22NoRootWindowReachability.
The existing width-two OLD terminal m=true example is a valid
local R0c rejection diagnostic, NOT a word proved reachable
from any W-accepted start. No explicit W-accepted counter-word
has been found or asserted. The complete q=ceilLogTwo n
BANK-band target remains open until the causal sampled-word
row-preservation lemma is supplied.
-/

end L3.RenewalReferenceClock

/-!
Accepted-W visible-word transport and an exact audit of the
remaining generated R0b no-root window obligation.

The admission test already supplies AcceptedWord at the original
reader cut. Its QWord factor freezes all visible u/beta coordinates
along the genuine projected reader Run. In particular, OLD samples
taken by R1c/R0b cannot become stale because of later W services.

The remaining missing step is not visible-word transport: it is the
source geometry and the accepted-word recurrence/marker equations for
the full generated no-root sampling interval. No theorem below
pretends that the five accumulator folds imply those equations.
-/

namespace L3.RenewalReferenceClock

open L3.HeadlineRenewal
open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree

set_option autoImplicit false
set_option Elab.async false

/-- Every genuine projected R Run admitted at an accepted W cut
has the accepted W factor at every prefix. Moreover all visible
u/beta coordinates equal their original accepted values, including
on failed reader decorations. This is an induction on the ACTUAL
BlockA.Run, not a fabricated independent W chain. -/
theorem bankRepairReaderE22AdmittedVisibleFixed {n : Nat}
    (ring : DirectedRing n)
    (origin : Fin n → ProjR (compileAdvice (ceilLogTwo n)))
    (initial : BlockA.Decoration
      (Fin n → ProjR (compileAdvice (ceilLogTwo n)))
      (BlockA.ReaderControl n
        (compileAdvice (ceilLogTwo n))))
    (hinit : BlockA.initializesReader
      (AcceptedReceipts.AcceptedWord ring
        (BlockA.wordT ring) (BlockA.wordValidated ring))
      origin initial) :
    ∀ (word : List (Fin n))
      (p : Fin n → ProjR (compileAdvice (ceilLogTwo n)))
      (gamma : BlockA.Decoration
        (Fin n → ProjR (compileAdvice (ceilLogTwo n)))
        (BlockA.ReaderControl n
          (compileAdvice (ceilLogTwo n)))),
      BlockA.Run ring (phiR ring)
        (BlockA.readerControlNext ring)
        origin initial word p gamma →
      AcceptedReceipts.AcceptedWord ring
        (BlockA.wordT ring) (BlockA.wordValidated ring)
        (AcceptedReceipts.wordProjectionR p) ∧
      ∀ i : Fin n,
        AcceptedReceipts.wordVisible
          (AcceptedReceipts.wordProjectionR p) i =
        AcceptedReceipts.wordVisible
          (AcceptedReceipts.wordProjectionR origin) i := by
  intro word p gamma hrun
  induction hrun with
  | empty =>
      constructor
      · exact hinit.1
      · intro i
        rfl
  | @next w q gamma h e ih =>
      have hqword : AcceptedReceipts.QWord ring
          (AcceptedReceipts.wordProjectionR q) :=
        AcceptedReceipts.accepted_word_qword_concrete
          ring (AcceptedReceipts.wordProjectionR q) ih.1
      have hvisible (i : Fin n) :
          AcceptedReceipts.wordVisible
            (phiW ring (AcceptedReceipts.wordProjectionR q) e) i =
          AcceptedReceipts.wordVisible
            (AcceptedReceipts.wordProjectionR q) i :=
        AcceptedReceipts.qword_visible_fixed
          ring (AcceptedReceipts.wordProjectionR q) hqword e i
      constructor
      · rw [AcceptedReceipts.wordProjectionR_phiR]
        exact AcceptedReceipts.accepted_word_phi_step
          ring (AcceptedReceipts.wordProjectionR q) e ih.1
      · intro i
        calc
          AcceptedReceipts.wordVisible
              (AcceptedReceipts.wordProjectionR (phiR ring q e)) i =
            AcceptedReceipts.wordVisible
              (phiW ring (AcceptedReceipts.wordProjectionR q) e) i := by
                rw [AcceptedReceipts.wordProjectionR_phiR]
          _ = AcceptedReceipts.wordVisible
                (AcceptedReceipts.wordProjectionR q) i := hvisible i
          _ = AcceptedReceipts.wordVisible
                (AcceptedReceipts.wordProjectionR origin) i := ih.2 i

/-- The exact J_R admission predicate supplies the existing
no-fresh-tag initialization lemma, without imposing zero
inherited-token count or choosing a different physical start. -/
theorem bankRepairReaderE22AdmittedNoRootStart {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (p : Fin n → ProjR (compileAdvice (ceilLogTwo n)))
    (initial : BlockA.Decoration
      (Fin n → ProjR (compileAdvice (ceilLogTwo n)))
      (BlockA.ReaderControl n
        (compileAdvice (ceilLogTwo n))))
    (hinit : BlockA.initializesReader
      (AcceptedReceipts.AcceptedWord ring
        (BlockA.wordT ring) (BlockA.wordValidated ring))
      p initial) :
    ∃ h : BlockA.ReaderControl n
        (compileAdvice (ceilLogTwo n)),
      initial = .live p h ∧
      BankRepairReaderE22NoRootWindow ring hbank p h := by
  obtain ⟨_hword, h, heq, _hphase, hslots⟩ := hinit
  exact ⟨h, heq,
    bankRepairReaderE22NoRootWindowInitial
      ring hbank p h hslots⟩

/-- Pure Boolean extraction from the literal R0c reject guard.
No assumption on the numerical provenance is used here. -/
private theorem bankRepairReaderE22NoRootGuardExtract
    (m h z parity visible postLeader : Bool)
    (hno : h = false)
    (hguard :
      (m || (!(h || postLeader) &&
        (!z || (visible != parity)))) = false) :
    m = false ∧
      (postLeader = false →
        z = true ∧ visible = parity) := by
  cases m <;> cases h <;> cases z <;>
    cases parity <;> cases visible <;>
      cases postLeader <;>
        simp at hno hguard ⊢

/-- The no-root-window predicate is already entailed at the
CURRENT state by E22Invariant's second numerical evidence clause:
R0c reject=false entails marker=false and the lower recurrence
test whenever the old token is root-free. This does NOT transport
the invariant through the next reader owner row. -/
theorem bankRepairReaderE22NoRootWindowOfInvariant {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (p : Fin n → ProjR (compileAdvice (ceilLogTwo n)))
    (h : BlockA.ReaderControl n
      (compileAdvice (ceilLogTwo n)))
    (hI : BankRepairReaderE22Invariant ring hbank p h) :
    BankRepairReaderE22NoRootWindow ring hbank p h := by
  intro site old name index samples
    hraw hempty hterminal htag hno
  have howner :
      (rawR (p site) (p (ring.rightNeighbor site))).reject =
        false :=
    hI.2.2.2 site old name index samples
      hraw hempty hterminal htag
  have hguard :
      (old.m ||
        (!(old.h ||
          (postW (p site).word
            (p (ring.rightNeighbor site)).word).eY.l) &&
          (!old.z ||
            ((p (ring.rightNeighbor site)).word.u != old.p)))) =
        false := by
    simpa [rawR, rawD1Step, ProjR.lift, ProjW.lift,
      hraw, hempty, hterminal] using howner
  exact bankRepairReaderE22NoRootGuardExtract
    old.m old.h old.z old.p
    (p (ring.rightNeighbor site)).word.u
    (postW (p site).word
      (p (ring.rightNeighbor site)).word).eY.l
    hno hguard

/-- The apparently new no-root reachability premise is, with its
CURRENT E22Invariant hypothesis, logically equivalent to the
original missing E22RowPreservation premise. The forward
implication uses the already installed root-touch and numerical
six-row lemmas; the reverse is the R0c Boolean extraction above.

Thus replacing E22RowPreservation by NoRootWindowReachability
does not by itself establish an independent inductive invariant. -/
theorem bankRepairReaderE22NoRootReachabilityIffRows {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) :
    BankRepairReaderE22NoRootWindowReachability ring hbank ↔
      BankRepairReaderE22RowPreservation ring hbank := by
  constructor
  · intro hwindow
    exact bankRepairReaderE22RowPreservationOfMarkerReachability
      ring hbank
      (bankRepairReaderE22TerminalMarkerReachabilityOfNoRootWindow
        ring hbank hwindow)
  · intro hrows
    intro start initial word p h e hW hinit hrun hI
    exact bankRepairReaderE22NoRootWindowOfInvariant
      ring hbank
      (phiR ring p e)
      (BlockA.readerControlNext ring h p e (phiR ring p e))
      (hrows start initial word p h e hW hinit hrun hI)

end L3.RenewalReferenceClock

/-!
R10 resident-debt row audit.

The six equations below concern the literal OLD raw-reader pair.
They do not substitute phiR for the masked physical successor.
The additional physical-transport proposition below is deliberately
not asserted without its OLD no-FIRE premise.
-/

namespace L3.RenewalReferenceClock

open L3.HeadlineRenewal
open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree

set_option autoImplicit false
set_option Elab.async false

/-- Debt on just the two selected sites before or after an OLD
R0/R1 service. This is a local arithmetic device, not a new
global potential or a new scheduler. -/
def bankRepairReaderResidentPairDebt {n : Nat} {c : Compiled}
    (x y : ProjR c)
    (tagX tagY : BlockA.RawTag n c.t) : Nat :=
  bankRepairReaderResidentSiteDebt tagX x.rawTok +
    bankRepairReaderResidentSiteDebt tagY y.rawTok

/-- A fresh or empty tag has no prepaid inherited debt;
an inherited tag contributes the one service paid by its
next outgoing edge. -/
def bankRepairReaderResidentMoveCharge {n t : Nat}
    (tag : BlockA.RawTag n t) : Nat :=
  match tag with
  | .inherited _ => 1
  | _ => 0

/-- An occupied inherited slot always carries at least one
remaining service, including its terminal R0c service. -/
theorem bankRepairReaderResidentInheritedPositive
    {n t : Nat} (name : Fin n) (raw : RawTok t) :
    1 ≤ bankRepairReaderResidentSiteDebt
      (.inherited name) (some raw) := by
  change 1 ≤ t - raw.jm1.val
  exact bankRepairReaderResidentDebtPositive raw

/-- R0a: OLD source and OLD target both occupied. The source
is erased; the target token and target tag are retained.
The pair loses exactly the OLD source's inherited debt. -/
theorem bankRepairReaderResidentCollisionPair
    {n : Nat} {c : Compiled}
    (x y : ProjR c)
    (sourceTag targetTag : BlockA.RawTag n c.t)
    (source resident : RawTok c.t)
    (hx : x.rawTok = some source)
    (hy : y.rawTok = some resident) :
    bankRepairReaderResidentPairDebt
        (pairR x y).1 (pairR x y).2
        .empty targetTag +
      bankRepairReaderResidentSiteDebt sourceTag x.rawTok =
    bankRepairReaderResidentPairDebt x y sourceTag targetTag := by
  have hrow := Closure.readerCollisionRow
    x y source resident hx hy
  simp [bankRepairReaderResidentPairDebt,
    bankRepairReaderResidentSiteDebt,
    hrow.1, hrow.2.1, hx, hy]
  omega

/-- R0b: the OLD inherited token moves one site right, with
jm1 increasing by one; a fresh tag stays fresh and carries
zero inherited debt. This is the exact one-ticket identity. -/
theorem bankRepairReaderResidentMovePair
    {n : Nat} {c : Compiled}
    (x y : ProjR c)
    (sourceTag targetTag : BlockA.RawTag n c.t)
    (source : RawTok c.t) (site : Fin n)
    (hx : x.rawTok = some source)
    (hy : y.rawTok = none)
    (hmove : source.j < c.t) :
    bankRepairReaderResidentPairDebt
        (pairR x y).1 (pairR x y).2
        .empty
        (BlockA.readerTransfer sourceTag
          (BlockA.readerSelectedSample
            site
            x y)) +
      bankRepairReaderResidentMoveCharge sourceTag =
    bankRepairReaderResidentPairDebt
      x y sourceTag targetTag := by
  have hrow := Closure.readerMoveRow
    x y source hx hy hmove
  cases sourceTag with
  | empty =>
      simp [bankRepairReaderResidentPairDebt,
        bankRepairReaderResidentSiteDebt,
        bankRepairReaderResidentMoveCharge,
        BlockA.readerTransfer, hrow.1, hx, hy]
  | fresh name index samples =>
      simp [bankRepairReaderResidentPairDebt,
        bankRepairReaderResidentSiteDebt,
        bankRepairReaderResidentMoveCharge,
        BlockA.readerTransfer, hrow.1, hx, hy]
  | inherited name =>
      have hcursor :
          ((pairR x y).2.rawTok.map
            (fun raw => raw.jm1.val)) = some source.j := by
        simp [pairR, rawR, rawD1Step,
          ProjR.lift, hx, hy, hmove]
      cases hnext : (pairR x y).2.rawTok with
      | none =>
          rw [hnext] at hcursor
          cases hcursor
      | some next =>
          have hindex : next.jm1.val = source.j := by
            rw [hnext] at hcursor
            exact Option.some.inj hcursor
          have hrank := bankRepairReaderResidentDebtMove
            source hmove
          have heq : c.t - next.jm1.val + 1 =
              c.t - source.jm1.val := by
            rw [hindex]
            exact hrank
          change
            bankRepairReaderResidentSiteDebt
                (.empty : BlockA.RawTag n c.t) (pairR x y).1.rawTok +
              bankRepairReaderResidentSiteDebt
                (.inherited name)
                (pairR x y).2.rawTok +
              bankRepairReaderResidentMoveCharge
                (.inherited name) =
              bankRepairReaderResidentSiteDebt
                (.inherited name) x.rawTok +
              bankRepairReaderResidentSiteDebt
                targetTag y.rawTok
          rw [hrow.1, hnext, hx, hy]
          simpa [bankRepairReaderResidentSiteDebt,
            bankRepairReaderResidentMoveCharge] using heq

/-- R0c: the terminal token and both selected tags are erased.
The OLD responder was token-free; all its site debt was zero. -/
theorem bankRepairReaderResidentTerminalPair
    {n : Nat} {c : Compiled}
    (x y : ProjR c)
    (sourceTag targetTag : BlockA.RawTag n c.t)
    (source : RawTok c.t)
    (hx : x.rawTok = some source)
    (hy : y.rawTok = none)
    (hterminal : ¬ source.j < c.t) :
    bankRepairReaderResidentPairDebt
        (pairR x y).1 (pairR x y).2
        (.empty : BlockA.RawTag n c.t) (.empty : BlockA.RawTag n c.t) +
      bankRepairReaderResidentSiteDebt sourceTag x.rawTok =
    bankRepairReaderResidentPairDebt x y sourceTag targetTag := by
  have hrow := Closure.readerTerminalRow
    x y source hx hy hterminal
  simp [bankRepairReaderResidentPairDebt,
    bankRepairReaderResidentSiteDebt,
    hrow.1, hrow.2.1, hx, hy]

/-- R1a: the initiator was empty and the responder token
is kept; neither selected site changes inherited debt. -/
theorem bankRepairReaderResidentResidentPair
    {n : Nat} {c : Compiled}
    (x y : ProjR c)
    (sourceTag targetTag : BlockA.RawTag n c.t)
    (resident : RawTok c.t)
    (hx : x.rawTok = none)
    (hy : y.rawTok = some resident) :
    bankRepairReaderResidentPairDebt
        (pairR x y).1 (pairR x y).2
        .empty targetTag =
    bankRepairReaderResidentPairDebt x y sourceTag targetTag := by
  have hrow := Closure.readerResidentRow
    x y resident hx hy
  simp [bankRepairReaderResidentPairDebt,
    bankRepairReaderResidentSiteDebt,
    hrow.1, hrow.2.1, hx, hy]

/-- R1b: no token at either OLD site; kick-arming creates
no inherited token, and the pair's inherited debt remains zero. -/
theorem bankRepairReaderResidentKickArmPair
    {n : Nat} {c : Compiled}
    (x y : ProjR c)
    (sourceTag targetTag : BlockA.RawTag n c.t)
    (hx : x.rawTok = none)
    (hy : y.rawTok = none)
    (hk : y.rawKick = false) :
    bankRepairReaderResidentPairDebt
        (pairR x y).1 (pairR x y).2
        .empty targetTag =
    bankRepairReaderResidentPairDebt x y sourceTag targetTag := by
  have hrow := Closure.readerKickArmRow
    x y hx hy hk
  simp [bankRepairReaderResidentPairDebt,
    bankRepairReaderResidentSiteDebt,
    hrow.1, hrow.2.1, hx, hy]

/-- R1c: a new physical raw token receives a fresh name,
not an inherited name. No inherited debt is minted. The
equation is independent of which unused name was chosen. -/
theorem bankRepairReaderResidentKickLaunchPair
    {n : Nat} {c : Compiled}
    (x y : ProjR c)
    (sourceTag targetTag : BlockA.RawTag n c.t)
    (name : Fin n)
    (index : Fin (c.t + 1))
    (samples : BlockA.FiniteLedger
      (BlockA.ReaderSample n) c.t)
    (hx : x.rawTok = none)
    (hy : y.rawTok = none)
    (hk : y.rawKick = true)
    (ht : 0 < c.t) :
    bankRepairReaderResidentPairDebt
        (pairR x y).1 (pairR x y).2
        .empty (.fresh name index samples) =
    bankRepairReaderResidentPairDebt x y sourceTag targetTag := by
  have hrow := Closure.readerKickLaunchRow
    x y hx hy hk ht
  simp [bankRepairReaderResidentPairDebt,
    bankRepairReaderResidentSiteDebt,
    hrow.1, hx, hy]

/-- A terminal source with inherited provenance loses at least
one ticket, independently of the OLD beta/u/leader values. -/
theorem bankRepairReaderResidentTerminalInheritedDrop
    {n : Nat} {c : Compiled}
    (x y : ProjR c)
    (name : Fin n) (targetTag : BlockA.RawTag n c.t)
    (source : RawTok c.t)
    (hx : x.rawTok = some source)
    (hy : y.rawTok = none)
    (hterminal : ¬ source.j < c.t) :
    1 + bankRepairReaderResidentPairDebt
        (pairR x y).1 (pairR x y).2
        (.empty : BlockA.RawTag n c.t) (.empty : BlockA.RawTag n c.t) ≤
      bankRepairReaderResidentPairDebt
        x y (.inherited name) targetTag := by
  have hbalance := bankRepairReaderResidentTerminalPair
    x y (.inherited name) targetTag source
    hx hy hterminal
  have hpositive := bankRepairReaderResidentInheritedPositive
    name source
  rw [hx] at hbalance
  omega

/-- An inherited collision source is likewise retired in one
selected outgoing service; an OLD resident at the target remains. -/
theorem bankRepairReaderResidentCollisionInheritedDrop
    {n : Nat} {c : Compiled}
    (x y : ProjR c)
    (name : Fin n) (targetTag : BlockA.RawTag n c.t)
    (source resident : RawTok c.t)
    (hx : x.rawTok = some source)
    (hy : y.rawTok = some resident) :
    1 + bankRepairReaderResidentPairDebt
        (pairR x y).1 (pairR x y).2
        .empty targetTag ≤
      bankRepairReaderResidentPairDebt
        x y (.inherited name) targetTag := by
  have hbalance := bankRepairReaderResidentCollisionPair
    x y (.inherited name) targetTag source resident
    hx hy
  have hpositive := bankRepairReaderResidentInheritedPositive
    name source
  rw [hx] at hbalance
  omega

/-- Exact unresolved physical bridge: the old projected R
successor must equal the actual masked-reference R projection
on every word generated from a W-accepted start. Raw row
arithmetic alone cannot give native/serializer/worker equality
if the selected full base owner fires a new leader. -/
def BankRepairReaderResidentPhysicalTransport {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) :
    Prop :=
  ∀ (start : BankReferenceState ring hbank),
    BankRepairWAccepted ring hbank start →
    ∀ (word : List (Fin n)) (e : Fin n),
      piR ((bankRepairNext ring hbank
        (bankRepairReaderResidentTrace ring hbank start word).1 e).val.1) =
      phiR ring
        (piR (bankRepairReaderResidentTrace
          ring hbank start word).1.val.1) e

/-- This physical bridge follows from the two ALREADY NAMED
sources: W-accepted closure and no OLD FIRE on W-accepted states.
Neither is provided by the six local raw-reader row equations. -/
theorem bankRepairReaderResidentPhysicalTransportOfNoFire
    {n : Nat} (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hclosed : BankRepairWAcceptedClosed ring hbank)
    (hnofire : BankRepairNoFireFromW ring hbank) :
    BankRepairReaderResidentPhysicalTransport ring hbank := by
  intro start hW word e
  have hphysical := bankRepairReaderResidentTracePhysical
    ring hbank start word
  have haccepted := bankRepairWAcceptedRun
    ring hbank hclosed start hW word
  rw [← hphysical] at haccepted
  have hfire := hnofire
    (bankRepairReaderResidentTrace ring hbank start word).1
    haccepted e
  exact bankRepairReaderPhiStepOfNoFire ring
    (bankRepairReaderE22BankSize hbank) hbank
    (bankRepairReaderResidentTrace ring hbank start word).1
    e hfire

/-!
REMAINING ASSEMBLY, NOT ASSERTED AS A THEOREM.

* The six selected-pair debt identities above still need a
  two-site sum-replacement calculation for
  bankRepairReaderResidentTotal, with
  Closure.readerProjectedRemoteFrame and
  Closure.readerTagRemoteFrame.
* The chosen outgoing edge for an inherited tag must be
  obtained from Closure.ReaderGhostWellFormed and
  Closure.readerInheritedSetIff. The R0b/R0a/R0c strict
  local reductions then pay one unit; the other five edges
  must only be shown weakly nonincreasing.
* Once no inherited name remains, the E.G20 phase update
  makes the new control done, and
  bankRepairReaderResidentEmptyTicket pays the final step.
* Physical transport is a separate issue: the existing
  bankRepairReaderPhiStepOfNoFire requires OLD no-FIRE.
  BankRepairWAcceptedClosed and BankRepairNoFireFromW
  are not unconditional theorems at this source cut.
* Hence BankRepairResidentRetirementOwnerRows, and therefore
  BankRepairResidentRetirementClock, are NOT claimed.
  The already installed
  bankRepairResidentRetirementClockOfOwnerRows is the
  correct final conditional handoff once all three
  OwnerRows conjuncts are proved.

No concrete W-accepted reachable counterexample to the
original OwnerRows Prop is claimed. The n=5 zero-ticket
diagnostic above is only a local test,
and does not refute the corrected potential.
-/

end L3.RenewalReferenceClock

/-!
E.G22 numerical/visible-word audit.

The numerical five folds and visible-bit transport are proved along
the genuine decorated Run. The W recurrence/marker equations are
NOT fields of AcceptedWord and are not manufactured here.
-/

namespace L3.RenewalReferenceClock

open L3.HeadlineRenewal
open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree

set_option autoImplicit false
set_option Elab.async false

/-- Actual numerical folds and structural ghost support,
without the missing R0c no-rejection conclusion. -/
def BankRepairReaderE22NumericalOnly {n : Nat}
    (p : Fin n → ProjR (compileAdvice (ceilLogTwo n)))
    (h : BlockA.ReaderControl n
      (compileAdvice (ceilLogTwo n))) : Prop :=
  Closure.ReaderGhostWellFormed p h ∧
    ∀ i : Fin n, BankRepairReaderE22FreshSite p h i

/-- Unchanged tags and tokens preserve their exact genuine fold.
This is a numerical-only version of the existing retention lemma. -/
private theorem bankRepairReaderE22NumericalRetained
    {n : Nat} (ring : DirectedRing n)
    (p : Fin n → ProjR (compileAdvice (ceilLogTwo n)))
    (h : BlockA.ReaderControl n
      (compileAdvice (ceilLogTwo n)))
    (e site : Fin n)
    (hnumeric : ∀ i : Fin n,
      BankRepairReaderE22FreshSite p h i)
    (hraw : ((phiR ring p e) site).rawTok = (p site).rawTok)
    (htag :
      (BlockA.readerControlNext ring h p e
        (phiR ring p e)).tags site = h.tags site) :
    BankRepairReaderE22FreshSite (phiR ring p e)
      (BlockA.readerControlNext ring h p e
        (phiR ring p e)) site := by
  intro name index samples hnew
  rw [htag] at hnew
  have hold := hnumeric site name index samples hnew
  constructor
  · exact hold.1
  · rw [hraw]
    exact hold.2

/-- R0b extends a genuinely fresh finite ledger by exactly
the selected OLD responder sample, never by a guessed value. -/
private theorem bankRepairReaderE22NumericalMove
    {n : Nat} (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (p : Fin n → ProjR (compileAdvice (ceilLogTwo n)))
    (h : BlockA.ReaderControl n
      (compileAdvice (ceilLogTwo n)))
    (e : Fin n)
    (old : RawTok (compileAdvice (ceilLogTwo n)).t)
    (hx : (p e).rawTok = some old)
    (hy : (p (ring.rightNeighbor e)).rawTok = none)
    (hmore : old.j < (compileAdvice (ceilLogTwo n)).t)
    (hwf : Closure.ReaderGhostWellFormed p h)
    (hnumeric : ∀ i : Fin n,
      BankRepairReaderE22FreshSite p h i) :
    BankRepairReaderE22FreshSite (phiR ring p e)
      (BlockA.readerControlNext ring h p e
        (phiR ring p e)) (ring.rightNeighbor e) := by
  have hne := EWord.rightNeighborDifferent ring
    (bankRepairReaderE22BankSize hbank) e
  have hrow := Closure.readerMoveRow
    (p e) (p (ring.rightNeighbor e)) old hx hy hmore
  have hdst := Closure.readerDestinationMoved ring p h e
    hne hrow.2.2
  cases hsource : h.tags e with
  | empty =>
      have hbad : (p e).rawTok = none :=
        (Closure.readerGhostTagSupport p h hwf e).1 hsource
      rw [hx] at hbad
      cases hbad
  | inherited oldName =>
      intro name index samples hnew
      rw [hdst, hsource] at hnew
      change BlockA.RawTag.inherited oldName =
        .fresh name index samples at hnew
      cases hnew
  | fresh oldName oldIndex oldSamples =>
      have hvalid :=
        (hnumeric e oldName oldIndex oldSamples hsource).2
      rw [hx] at hvalid
      have hcursor := Closure.readerFoldCursor
        (q := ceilLogTwo n) e old oldIndex oldSamples hvalid
      have hindex :
          oldIndex.val < (compileAdvice (ceilLogTwo n)).t := by
        omega
      obtain ⟨nextIndex, hnext, hvalidNew⟩ :=
        Closure.readerMoveFoldValid (q := ceilLogTwo n)
          e (ring.rightNeighbor e) (p e)
          (p (ring.rightNeighbor e)) old oldIndex oldSamples
          hx hy hmore hvalid
      have hindexEq :
          (⟨oldIndex.val + 1, by omega⟩ :
            Fin ((compileAdvice (ceilLogTwo n)).t + 1)) =
              nextIndex := by
        apply Fin.ext
        exact hnext.symm
      have htagNext :
          (BlockA.readerControlNext ring h p e
            (phiR ring p e)).tags (ring.rightNeighbor e) =
          .fresh oldName nextIndex
            (oldSamples.push
              (BlockA.readerSelectedSample
                (ring.rightNeighbor e) (p e)
                (p (ring.rightNeighbor e)))) := by
        rw [hdst, hsource]
        change BlockA.readerTransfer
          (.fresh oldName oldIndex oldSamples)
          (BlockA.readerSelectedSample
            (ring.rightNeighbor e) (p e)
            (p (ring.rightNeighbor e))) = _
        simp [BlockA.readerTransfer, hindex, hindexEq]
      have hcountNew :
          (oldSamples.push
            (BlockA.readerSelectedSample
              (ring.rightNeighbor e) (p e)
              (p (ring.rightNeighbor e)))).count =
              nextIndex :=
        Closure.readerFoldCount (q := ceilLogTwo n)
          (ring.rightNeighbor e)
          (pairR (p e) (p (ring.rightNeighbor e))).2.rawTok
          nextIndex
          (oldSamples.push
            (BlockA.readerSelectedSample
              (ring.rightNeighbor e) (p e)
              (p (ring.rightNeighbor e)))) hvalidNew
      intro name index samples hnew
      rw [htagNext] at hnew
      cases hnew
      constructor
      · exact hcountNew
      · rw [Closure.readerProjectedDestinationRaw ring p e hne]
        exact hvalidNew

/-- All six R0a/R0b/R0c/R1a/R1b/R1c physical reader rows
preserve numerical evidence without assuming terminal safety. -/
theorem bankRepairReaderE22NumericalOwnerStep
    {n : Nat} (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (p : Fin n → ProjR (compileAdvice (ceilLogTwo n)))
    (h : BlockA.ReaderControl n
      (compileAdvice (ceilLogTwo n)))
    (e : Fin n)
    (hnumeric : BankRepairReaderE22NumericalOnly p h) :
    BankRepairReaderE22NumericalOnly
      (phiR ring p e)
      (BlockA.readerControlNext ring h p e
        (phiR ring p e)) := by
  have hne := EWord.rightNeighborDifferent ring
    (bankRepairReaderE22BankSize hbank) e
  refine ⟨Closure.readerGhostWellFormedStep
    (bankRepairReaderE22BankSize hbank)
    (bankRepairReaderCompiledWidthPos hbank)
    ring p h e hnumeric.1, ?_⟩
  intro i
  by_cases his : i = e
  · subst i
    exact bankRepairReaderE22EmptyFresh _ _ _
      (Closure.readerSourceTagCleared ring h p e hnumeric.1)
  · by_cases hid : i = ring.rightNeighbor e
    · subst i
      cases hx : (p e).rawTok with
      | some old =>
          cases hy : (p (ring.rightNeighbor e)).rawTok with
          | some resident =>
              have hrow := Closure.readerCollisionRow
                (p e) (p (ring.rightNeighbor e)) old resident hx hy
              have htag := Closure.readerDestinationRetained
                ring p h e hne (Or.inl hrow.2.2)
              have hraw :
                  ((phiR ring p e) (ring.rightNeighbor e)).rawTok =
                    (p (ring.rightNeighbor e)).rawTok := by
                rw [Closure.readerProjectedDestinationRaw
                  ring p e hne, hrow.2.1, hy]
              exact bankRepairReaderE22NumericalRetained
                ring p h e (ring.rightNeighbor e)
                hnumeric.2 hraw htag
          | none =>
              by_cases hmore :
                  old.j < (compileAdvice (ceilLogTwo n)).t
              · exact bankRepairReaderE22NumericalMove
                  ring hbank p h e old hx hy hmore
                  hnumeric.1 hnumeric.2
              · exact bankRepairReaderE22TerminalFresh
                  ring hbank p h e old hx hy hmore
      | none =>
          cases hy : (p (ring.rightNeighbor e)).rawTok with
          | some resident =>
              have hrow := Closure.readerResidentRow
                (p e) (p (ring.rightNeighbor e)) resident hx hy
              have htag := Closure.readerDestinationRetained
                ring p h e hne (Or.inr (Or.inl hrow.2.2))
              have hraw :
                  ((phiR ring p e) (ring.rightNeighbor e)).rawTok =
                    (p (ring.rightNeighbor e)).rawTok := by
                rw [Closure.readerProjectedDestinationRaw
                  ring p e hne, hrow.2.1, hy]
              exact bankRepairReaderE22NumericalRetained
                ring p h e (ring.rightNeighbor e)
                hnumeric.2 hraw htag
          | none =>
              cases hk : (p (ring.rightNeighbor e)).rawKick with
              | false =>
                  exact bankRepairReaderE22KickArmFresh
                    ring hbank p h e hx hy hk hnumeric.1
              | true =>
                  exact bankRepairReaderE22KickLaunchFresh
                    ring hbank p h e hx hy hk hnumeric.1
    · exact bankRepairReaderE22NumericalRetained
        ring p h e i hnumeric.2
        (Closure.readerProjectedRemoteFrame ring p e i his hid)
        (Closure.readerTagRemoteFrame ring p h e i his hid)

/-- The actual admitted decorated Run, including inherited
tokens, carries the numerical five-fold invariant on every prefix.
The stronger R0c guard is not used. -/
theorem bankRepairReaderE22NumericalRun
    {n : Nat} (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (origin : Fin n → ProjR (compileAdvice (ceilLogTwo n)))
    (initial : BlockA.Decoration
      (Fin n → ProjR (compileAdvice (ceilLogTwo n)))
      (BlockA.ReaderControl n
        (compileAdvice (ceilLogTwo n))))
    (hinit : BlockA.initializesReader
      (AcceptedReceipts.AcceptedWord ring
        (BlockA.wordT ring) (BlockA.wordValidated ring))
      origin initial)
    (word : List (Fin n))
    (p : Fin n → ProjR (compileAdvice (ceilLogTwo n)))
    (gamma : BlockA.Decoration
      (Fin n → ProjR (compileAdvice (ceilLogTwo n)))
      (BlockA.ReaderControl n
        (compileAdvice (ceilLogTwo n))))
    (hrun : BlockA.Run ring (phiR ring)
      (BlockA.readerControlNext ring)
      origin initial word p gamma) :
    ∃ h : BlockA.ReaderControl n
        (compileAdvice (ceilLogTwo n)),
      gamma = .live p h ∧
      BankRepairReaderE22NumericalOnly p h := by
  induction hrun with
  | empty =>
      obtain ⟨_hword, h, heq, hphase, hslots⟩ := hinit
      refine ⟨h, heq, ?_⟩
      constructor
      · exact Closure.readerGhostWellFormedStart
          origin h hphase hslots
      · intro site name index samples htag
        exact False.elim
          ((bankRepairReaderE22InitialNoFresh origin h hslots)
            site name index samples htag)
  | @next w q gamma' hrunPrefix e ih =>
      obtain ⟨h, hgamma, hnumeric⟩ := ih
      refine ⟨BlockA.readerControlNext ring h q e
        (phiR ring q e), ?_, ?_⟩
      · rw [hgamma]
        classical
        simp [BlockA.update]
      · exact bankRepairReaderE22NumericalOwnerStep
          ring hbank q h e hnumeric

/-- Extract the actual numerical invariant at a live Run endpoint. -/
theorem bankRepairReaderE22NumericalRunLive
    {n : Nat} (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (origin : Fin n → ProjR (compileAdvice (ceilLogTwo n)))
    (initial : BlockA.Decoration
      (Fin n → ProjR (compileAdvice (ceilLogTwo n)))
      (BlockA.ReaderControl n
        (compileAdvice (ceilLogTwo n))))
    (hinit : BlockA.initializesReader
      (AcceptedReceipts.AcceptedWord ring
        (BlockA.wordT ring) (BlockA.wordValidated ring))
      origin initial)
    (word : List (Fin n))
    (p : Fin n → ProjR (compileAdvice (ceilLogTwo n)))
    (h : BlockA.ReaderControl n
      (compileAdvice (ceilLogTwo n)))
    (hrun : BlockA.Run ring (phiR ring)
      (BlockA.readerControlNext ring)
      origin initial word p (.live p h)) :
    BankRepairReaderE22NumericalOnly p h := by
  obtain ⟨control, heq, hnumeric⟩ :=
    bankRepairReaderE22NumericalRun
      ring hbank origin initial hinit word p (.live p h) hrun
  have hc : h = control := by
    cases heq
    rfl
  subst control
  exact hnumeric

/-- R1c and R0b sample exactly the OLD receiver's actual bit
and marker; AcceptedWord keeps both equal to the original
admitted W word at that physical site. -/
theorem bankRepairReaderE22SelectedReadFixedOnRun
    {n : Nat} (ring : DirectedRing n)
    (origin : Fin n → ProjR (compileAdvice (ceilLogTwo n)))
    (initial : BlockA.Decoration
      (Fin n → ProjR (compileAdvice (ceilLogTwo n)))
      (BlockA.ReaderControl n
        (compileAdvice (ceilLogTwo n))))
    (hinit : BlockA.initializesReader
      (AcceptedReceipts.AcceptedWord ring
        (BlockA.wordT ring) (BlockA.wordValidated ring))
      origin initial)
    (word : List (Fin n))
    (p : Fin n → ProjR (compileAdvice (ceilLogTwo n)))
    (h : BlockA.ReaderControl n
      (compileAdvice (ceilLogTwo n)))
    (hrun : BlockA.Run ring (phiR ring)
      (BlockA.readerControlNext ring)
      origin initial word p (.live p h))
    (e : Fin n) :
    (BlockA.readerSelectedSample (ring.rightNeighbor e)
        (p e) (p (ring.rightNeighbor e))).oldBit =
        (origin (ring.rightNeighbor e)).word.u ∧
    (BlockA.readerSelectedSample (ring.rightNeighbor e)
        (p e) (p (ring.rightNeighbor e))).oldMarker =
        (origin (ring.rightNeighbor e)).word.beta := by
  have hv :=
    (bankRepairReaderE22AdmittedVisibleFixed
      ring origin initial hinit
      word p (.live p h) hrun).2 (ring.rightNeighbor e)
  constructor
  · simpa [BlockA.readerSelectedSample,
      AcceptedReceipts.wordProjectionR,
      AcceptedReceipts.wordVisible] using congrArg Prod.fst hv
  · simpa [BlockA.readerSelectedSample,
      AcceptedReceipts.wordProjectionR,
      AcceptedReceipts.wordVisible] using congrArg Prod.snd hv

/-- The next genuine reader owner preserves both completed
numerical E.G22 folds and W acceptance/visible immutability. -/
theorem bankRepairReaderE22AdmittedNextFoldAndVisible
    {n : Nat} (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (origin : Fin n → ProjR (compileAdvice (ceilLogTwo n)))
    (initial : BlockA.Decoration
      (Fin n → ProjR (compileAdvice (ceilLogTwo n)))
      (BlockA.ReaderControl n
        (compileAdvice (ceilLogTwo n))))
    (hinit : BlockA.initializesReader
      (AcceptedReceipts.AcceptedWord ring
        (BlockA.wordT ring) (BlockA.wordValidated ring))
      origin initial)
    (word : List (Fin n))
    (p : Fin n → ProjR (compileAdvice (ceilLogTwo n)))
    (h : BlockA.ReaderControl n
      (compileAdvice (ceilLogTwo n)))
    (hrun : BlockA.Run ring (phiR ring)
      (BlockA.readerControlNext ring)
      origin initial word p (.live p h))
    (e : Fin n) :
    (∀ site : Fin n,
      BankRepairReaderE22FreshSite
        (phiR ring p e)
        (BlockA.readerControlNext ring h p e
          (phiR ring p e)) site) ∧
    AcceptedReceipts.AcceptedWord ring
      (BlockA.wordT ring) (BlockA.wordValidated ring)
      (AcceptedReceipts.wordProjectionR (phiR ring p e)) ∧
    (∀ site : Fin n,
      AcceptedReceipts.wordVisible
        (AcceptedReceipts.wordProjectionR (phiR ring p e)) site =
      AcceptedReceipts.wordVisible
        (AcceptedReceipts.wordProjectionR origin) site) := by
  have hnumeric := bankRepairReaderE22NumericalRunLive
    ring hbank origin initial hinit word p h hrun
  have hold := bankRepairReaderE22AdmittedVisibleFixed
    ring origin initial hinit word p (.live p h) hrun
  have hqword : AcceptedReceipts.QWord ring
      (AcceptedReceipts.wordProjectionR p) :=
    AcceptedReceipts.accepted_word_qword_concrete
      ring (AcceptedReceipts.wordProjectionR p) hold.1
  refine ⟨(bankRepairReaderE22NumericalOwnerStep
    ring hbank p h e hnumeric).2, ?_, ?_⟩
  · rw [AcceptedReceipts.wordProjectionR_phiR]
    exact AcceptedReceipts.accepted_word_phi_step
      ring (AcceptedReceipts.wordProjectionR p) e hold.1
  · intro site
    calc
      AcceptedReceipts.wordVisible
          (AcceptedReceipts.wordProjectionR (phiR ring p e)) site =
        AcceptedReceipts.wordVisible
          (phiW ring (AcceptedReceipts.wordProjectionR p) e) site := by
            rw [AcceptedReceipts.wordProjectionR_phiR]
      _ = AcceptedReceipts.wordVisible
            (AcceptedReceipts.wordProjectionR p) site :=
          AcceptedReceipts.qword_visible_fixed
            ring (AcceptedReceipts.wordProjectionR p)
            hqword e site
      _ = AcceptedReceipts.wordVisible
            (AcceptedReceipts.wordProjectionR origin) site :=
          hold.2 site

/-- Existing CleanWorkerWordValues equations transfer along the
actual Run whenever they were established at its W origin.
This does not assert their derivation from AcceptedWord. -/
theorem bankRepairReaderE22AdmittedStaticWordValuesNext
    {n : Nat} (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (root : Fin n)
    (origin : Fin n → ProjR (compileAdvice (ceilLogTwo n)))
    (initial : BlockA.Decoration
      (Fin n → ProjR (compileAdvice (ceilLogTwo n)))
      (BlockA.ReaderControl n
        (compileAdvice (ceilLogTwo n))))
    (hinit : BlockA.initializesReader
      (AcceptedReceipts.AcceptedWord ring
        (BlockA.wordT ring) (BlockA.wordValidated ring))
      origin initial)
    (hvalues :
      AcceptedReceipts.WordEntrance.CleanWorker.CleanWorkerWordValues
        ring root (AcceptedReceipts.wordProjectionR origin))
    (word : List (Fin n))
    (p : Fin n → ProjR (compileAdvice (ceilLogTwo n)))
    (h : BlockA.ReaderControl n
      (compileAdvice (ceilLogTwo n)))
    (hrun : BlockA.Run ring (phiR ring)
      (BlockA.readerControlNext ring)
      origin initial word p (.live p h))
    (e : Fin n) :
    AcceptedReceipts.WordEntrance.CleanWorker.CleanWorkerWordValues
      ring root
      (AcceptedReceipts.wordProjectionR (phiR ring p e)) := by
  have hfixed :=
    (bankRepairReaderE22AdmittedNextFoldAndVisible
      ring hbank origin initial hinit
      word p h hrun e).2.2
  exact AcceptedReceipts.WordEntrance.CleanWorker.cleanWorkerWordValues_congr
    ring root
    (AcceptedReceipts.wordProjectionR (phiR ring p e))
    (AcceptedReceipts.wordProjectionR origin)
    hfixed hvalues

/-- The last OLD marker in a complete ledger has no mismatch
whenever beta(last) equals the AND of all t actual samples.
This is a W word equation, not a numerical fold consequence. -/
theorem bankRepairReaderE22MarkerOfPublishedSamples
    {q n : Nat}
    (site : Fin n)
    (old : RawTok (compileAdvice q).t)
    (index : Fin ((compileAdvice q).t + 1))
    (samples : BlockA.FiniteLedger
      (BlockA.ReaderSample n) (compileAdvice q).t)
    (hvalid : Closure.readerFoldValid q n
      site (some old) index samples)
    (hmarker : ∀ reads : List (BlockA.ReaderSample n),
      Closure.readerSampleList (compileAdvice q) samples index =
        some reads →
      ∀ last : BlockA.ReaderSample n,
        reads.reverse.head? = some last →
          last.oldMarker = Closure.readerSampleAnd reads) :
    old.m = false := by
  dsimp [Closure.readerFoldValid] at hvalid
  obtain ⟨_hcount, _hindex, reads, hreads, _hlength,
    _hlast, _hz, _hp, _ha, _hh, hm⟩ := hvalid
  rw [hm]
  unfold Closure.readerSampleMarkerError
  split
  · cases hr : reads.reverse with
    | nil => rfl
    | cons last rest =>
        have hmatch : last.oldMarker =
            Closure.readerSampleAnd reads :=
          hmarker reads hreads last (by simp [hr])
        simp [hmatch]
  · rfl

/-- Literal R0c reject=false from the three published equations
on a correctly positioned full root-free sample window:
last marker = AND, nonzero OR, next bit = tap parity.
The link to AcceptedWord remains the missing W/geometry step. -/
theorem bankRepairReaderE22GuardOfPublishedSamples
    {q n : Nat}
    (ring : DirectedRing n)
    (p : Fin n → ProjR (compileAdvice q))
    (site : Fin n)
    (old : RawTok (compileAdvice q).t)
    (index : Fin ((compileAdvice q).t + 1))
    (samples : BlockA.FiniteLedger
      (BlockA.ReaderSample n) (compileAdvice q).t)
    (hvalid : Closure.readerFoldValid q n
      site (some old) index samples)
    (hmarker : ∀ reads : List (BlockA.ReaderSample n),
      Closure.readerSampleList (compileAdvice q) samples index =
        some reads →
      ∀ last : BlockA.ReaderSample n,
        reads.reverse.head? = some last →
          last.oldMarker = Closure.readerSampleAnd reads)
    (hnonzero : ∀ reads : List (BlockA.ReaderSample n),
      Closure.readerSampleList (compileAdvice q) samples index =
        some reads →
        Closure.readerSampleOr reads = true)
    (hrecurrence : ∀ reads : List (BlockA.ReaderSample n),
      Closure.readerSampleList (compileAdvice q) samples index =
        some reads →
      (p (ring.rightNeighbor site)).word.u =
        Closure.readerSampleParity (compileAdvice q) reads) :
    (old.m ||
      (!(old.h ||
        (postW (p site).word
          (p (ring.rightNeighbor site)).word).eY.l) &&
        (!old.z ||
          ((p (ring.rightNeighbor site)).word.u != old.p)))) =
      false := by
  have hm := bankRepairReaderE22MarkerOfPublishedSamples
    site old index samples hvalid hmarker
  have hvalidCopy := hvalid
  dsimp [Closure.readerFoldValid] at hvalidCopy
  obtain ⟨_hcount, _hindex, reads, hreads, _hlength,
    _hlast, hz, hp, _ha, _hh, _hm⟩ := hvalidCopy
  have hnonzeroActual : old.z = true := by
    rw [hz]
    exact hnonzero reads hreads
  have hparityActual :
      (p (ring.rightNeighbor site)).word.u = old.p := by
    rw [hp]
    exact hrecurrence reads hreads
  simp [hm, hnonzeroActual, hparityActual]

/-!
OPEN SOURCE GAP — NOT ASSERTED HERE.

AcceptedReceipts.AcceptedWordAtRoot (Target.lean near line 3947)
is a genuine BlockA.Generated W history. Its terminal
BlockA.acceptsWord (near 2970) asks for phase done, the
publication-kind census, wordValidated receipt flags, QWord.
It does NOT have as a field the existing
AcceptedReceipts.WordEntrance.CleanWorker.CleanWorkerWordValues
structure (Target.lean near line 5530).

That existing structure states precisely:
 prefixZeros: beta_k=0 for 0<k<t;
 firstNonzero: OR(u_1,...,u_t)=true;
 laterNonzero: OR(u_(k-t),...,u_(k-1))=true for t<k<n;
 recurrence: u_k = XOR_j(taps_j AND u_(k-t+j)) for t<k<n;
 markers: beta_k = AND(u_(k-t+1),...,u_k) for t<=k<n.
The first window is initialized with a nonzero kick.
The paper's lemma e-word, clean-worker induction and future
idempotence (repair.tex lines roughly 967–1024) establish
these from causal publications, but the Lean source lacks
the accepted-W-to-static-word-values extraction theorem.

The numerical Run invariant above proves all five folds.
The existing admitted visible fixed lemma supplies sampled
u/beta immutability (and the selected read lemma exposes it).
A further historical site-geometry induction must identify
the entire ledger with consecutive clockwise root-free sites:
readerFoldValid alone records its last site but no pairwise
consecutive-source equation. Only then can the published W
marker/OR/recurrence equations be instantiated to the
three parameters of GuardOfPublishedSamples.

Therefore BankRepairReaderE22NoRootWindowReachability and the
equivalent BankRepairReaderE22RowPreservation remain OPEN.
No theorem above asserts either target, nor assumes a new
premise in place of the numerical or visible-word steps.
-/

end L3.RenewalReferenceClock

/-!
W-acceptance / clean-worker-value interface audit.

The literal W acceptance monitor records publication kinds and
Boolean receipts, but it has no field carrying the five physical
CleanWorkerWordValues equations. This block extracts everything
available at an accepted cut, proves the existing DONE-phase
certificate is sufficient, and transports such a certificate along
the accepted W and R projected runs. No fabricated phase certificate
or extra physical step is inserted.
-/

namespace L3.RenewalReferenceClock

open L3.HeadlineRenewal
open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree

set_option autoImplicit false
set_option Elab.async false

/-- The actual E.G17 acceptance fields: DONE, the finite
validated receipt flags, QWord, and the specified monitor root. -/
theorem bankRepairWAcceptCutFields {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (p : Fin n → ProjW c)
    (h : BlockA.WordControl n c)
    (hacc : AcceptedReceipts.WordAcceptAtRoot
      ring root (BlockA.wordValidated ring)
      p (.live p h)) :
    h.phase = .done ∧
      BlockA.wordValidated ring h ∧
      AcceptedReceipts.QWord ring p ∧
      h.root = root := by
  exact ⟨hacc.1.2.1, hacc.1.2.2.1,
    hacc.1.2.2.2.2, hacc.2⟩

/-- The accepted W cut certifies the prefix-zero PUBLICATION
flag and both finite receipts. This statement intentionally
does not replace the flag by the physical word beta bit. -/
theorem bankRepairWAcceptPrefixReceipt {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (p : Fin n → ProjW c)
    (h : BlockA.WordControl n c)
    (hacc : AcceptedReceipts.WordAcceptAtRoot
      ring root (BlockA.wordValidated ring)
      p (.live p h))
    (k : Fin n) (hk : 0 < k.val) (hsmall : k.val < c.t) :
    h.publications (PPL.shiftRight ring root k.val) =
        .prefixZero ∧
      h.prefixMarkers (PPL.shiftRight ring root k.val) =
        true ∧
      h.visibleReceipts (PPL.shiftRight ring root k.val) =
        true := by
  have hpub := hacc.1.2.2.2.1 k hk
  simpa [hsmall, hacc.2] using hpub

/-- Beyond the initial t-site prefix the accepted W monitor
records the recurrence publication kind, but this is not
yet an equation between u and the taps. -/
theorem bankRepairWAcceptRecurrenceReceipt {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (p : Fin n → ProjW c)
    (h : BlockA.WordControl n c)
    (hacc : AcceptedReceipts.WordAcceptAtRoot
      ring root (BlockA.wordValidated ring)
      p (.live p h))
    (k : Fin n) (hk : 0 < k.val) (hlater : c.t < k.val) :
    h.publications (PPL.shiftRight ring root k.val) =
        .recurrence ∧
      h.visibleReceipts (PPL.shiftRight ring root k.val) =
        true := by
  have hnot : ¬ k.val < c.t := by omega
  have hneq : k.val ≠ c.t := by omega
  have hpub := hacc.1.2.2.2.1 k hk
  simpa [hnot, hneq, hacc.2] using hpub

/-- The existing phase-local clean-worker invariant is the
precise missing W-stage producer. Its DONE case contains
the five static word equations. The accepted monitor gives
DONE and the root identification, but not this invariant. -/
theorem bankRepairWAcceptStaticOfPhaseCertificate
    {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (p : Fin n → ProjW c)
    (h : BlockA.WordControl n c)
    (hacc : AcceptedReceipts.WordAcceptAtRoot
      ring root (BlockA.wordValidated ring)
      p (.live p h))
    (hphase :
      AcceptedReceipts.WordEntrance.CleanWorker.CleanWorkerPhaseInv
        ring h p) :
    AcceptedReceipts.WordEntrance.CleanWorker.CleanWorkerWordValues
      ring root p := by
  have hdone : h.phase = .done :=
    (bankRepairWAcceptCutFields ring root p h hacc).1
  have hstatic :
      AcceptedReceipts.WordEntrance.CleanWorker.CleanWorkerWordValues
        ring h.root p :=
    (AcceptedReceipts.WordEntrance.CleanWorker.cwPhaseDoneValues
      ring h p hdone hphase).1
  simpa only [hacc.2] using hstatic

/-- Static recurrence/marker equations persist along any one
accepted projected W edge, using its already-proved QWord
visible fixity rather than a putative worker-control closure. -/
theorem bankRepairWAcceptStaticAfterEdgeOfPhase
    {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (p : Fin n → ProjW c)
    (h : BlockA.WordControl n c)
    (hacc : AcceptedReceipts.WordAcceptAtRoot
      ring root (BlockA.wordValidated ring)
      p (.live p h))
    (hphase :
      AcceptedReceipts.WordEntrance.CleanWorker.CleanWorkerPhaseInv
        ring h p)
    (e : Fin n) :
    AcceptedReceipts.WordEntrance.CleanWorker.CleanWorkerWordValues
      ring root (phiW ring p e) := by
  have hq : AcceptedReceipts.QWord ring p :=
    (bankRepairWAcceptCutFields ring root p h hacc).2.2.1
  have hv : ∀ i : Fin n,
      AcceptedReceipts.wordVisible (phiW ring p e) i =
        AcceptedReceipts.wordVisible p i := by
    intro i
    exact AcceptedReceipts.qword_visible_fixed
      ring p hq e i
  exact
    AcceptedReceipts.WordEntrance.CleanWorker.cleanWorkerWordValues_congr
      ring root (phiW ring p e) p hv
      (bankRepairWAcceptStaticOfPhaseCertificate
        ring root p h hacc hphase)

/-- The exact missing W acceptance producer is a terminal
CleanWorkerPhaseInv witness for a real accepted decoration.
This theorem discharges the Generated existential once that
producer has been established. No such producer is assumed
as an unconditional declaration. -/
theorem bankRepairWAtRootStaticOfPhaseProducer
    {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (p : Fin n → ProjW c)
    (haccepted : AcceptedReceipts.AcceptedWordAtRoot
      ring (BlockA.wordT ring) (BlockA.wordValidated ring)
      root p)
    (hproducer :
      ∀ gamma : BlockA.Decoration
        (Fin n → ProjW c) (BlockA.WordControl n c),
        AcceptedReceipts.WordAcceptAtRoot ring root
          (BlockA.wordValidated ring) p gamma →
        ∃ h : BlockA.WordControl n c,
          gamma = .live p h ∧
          AcceptedReceipts.WordEntrance.CleanWorker.CleanWorkerPhaseInv
            ring h p) :
    AcceptedReceipts.WordEntrance.CleanWorker.CleanWorkerWordValues
      ring root p := by
  obtain ⟨origin, initial, word, gamma,
    _hinit, _hrun, hacc⟩ := haccepted
  obtain ⟨control, hgamma, hphase⟩ := hproducer gamma hacc
  rw [hgamma] at hacc
  exact bankRepairWAcceptStaticOfPhaseCertificate
    ring root p control hacc hphase

/-- The existential-root AcceptedWord interface yields a
static equation certificate at its own accepted W root once
the same missing terminal phase producer is proved. No
identification with an independently named BANK root is inferred. -/
theorem bankRepairWStaticExistsOfPhaseProducer
    {n : Nat} {c : Compiled}
    (ring : DirectedRing n)
    (p : Fin n → ProjW c)
    (haccepted : AcceptedReceipts.AcceptedWord ring
      (BlockA.wordT ring) (BlockA.wordValidated ring) p)
    (hproducer :
      ∀ root : Fin n,
        ∀ gamma : BlockA.Decoration
          (Fin n → ProjW c) (BlockA.WordControl n c),
          AcceptedReceipts.WordAcceptAtRoot ring root
            (BlockA.wordValidated ring) p gamma →
          ∃ h : BlockA.WordControl n c,
            gamma = .live p h ∧
            AcceptedReceipts.WordEntrance.CleanWorker.CleanWorkerPhaseInv
              ring h p) :
    ∃ root : Fin n,
      AcceptedReceipts.WordEntrance.CleanWorker.CleanWorkerWordValues
        ring root p := by
  obtain ⟨root, hroot⟩ := haccepted
  exact ⟨root, bankRepairWAtRootStaticOfPhaseProducer
    ring root p hroot (hproducer root)⟩

/-- Once the static equations are certified at an admitted W
origin, the genuine reader Run carries them at EVERY prefix.
This reuses the visible-fixed theorem; no reader phase,
R0c guard, or synthetic window is assumed. -/
theorem bankRepairReaderStaticWordValuesAlongRun
    {n : Nat}
    (ring : DirectedRing n)
    (origin : Fin n → ProjR (compileAdvice (ceilLogTwo n)))
    (initial : BlockA.Decoration
      (Fin n → ProjR (compileAdvice (ceilLogTwo n)))
      (BlockA.ReaderControl n
        (compileAdvice (ceilLogTwo n))))
    (hinit : BlockA.initializesReader
      (AcceptedReceipts.AcceptedWord ring
        (BlockA.wordT ring) (BlockA.wordValidated ring))
      origin initial)
    (root : Fin n)
    (hstatic :
      AcceptedReceipts.WordEntrance.CleanWorker.CleanWorkerWordValues
        ring root (AcceptedReceipts.wordProjectionR origin))
    (word : List (Fin n))
    (p : Fin n → ProjR (compileAdvice (ceilLogTwo n)))
    (gamma : BlockA.Decoration
      (Fin n → ProjR (compileAdvice (ceilLogTwo n)))
      (BlockA.ReaderControl n
        (compileAdvice (ceilLogTwo n))))
    (hrun : BlockA.Run ring (phiR ring)
      (BlockA.readerControlNext ring)
      origin initial word p gamma) :
    AcceptedReceipts.WordEntrance.CleanWorker.CleanWorkerWordValues
      ring root (AcceptedReceipts.wordProjectionR p) := by
  have hv :=
    (bankRepairReaderE22AdmittedVisibleFixed ring origin initial
      hinit word p gamma hrun).2
  exact
    AcceptedReceipts.WordEntrance.CleanWorker.cleanWorkerWordValues_congr
      ring root
      (AcceptedReceipts.wordProjectionR p)
      (AcceptedReceipts.wordProjectionR origin)
      hv hstatic

/-!
SOURCE-SCOPE STATUS. Not a theorem.

WordAcceptAtRoot = acceptsWord AND matching monitor root.
BlockA.acceptsWord has precisely:
  shadow agreement, phase.done, validated,
  publication-kind/follower receipt census, QWord.

BlockA.wordValidated has only these two kinds of implication:
  publication prefixZero -> prefixMarkers=true and visibleReceipts=true;
  publication prefixEnd/recurrence -> visibleReceipts=true.
It does not mention u, beta, taps or the projected word p.
A prefixMarkers Boolean receipt is NOT a beta=0 equation.
A recurrence publication flag is NOT a tap-parity equation.

The five fields missing from these acceptance records are
CleanWorkerWordValues.prefixZeros, firstNonzero, laterNonzero,
recurrence, and markers (Target.lean near 5530).
CleanWorkerInv.wordValues already supplies all five.
CleanWorkerPhaseInv.done stores CleanWorkerInv; the proved
cwPhaseDoneValues extracts wordValues at a DONE control.

The W-stage missing producer is the actual-run proof that
a genuine BlockA.Generated wordT accepted witness has a
CleanWorkerPhaseInv at its DONE endpoint. A genuine I0
establishment theorem cwPhaseIZeroEstablishment exists
(Target.lean), but the complete all-row phase-local
history induction has not been proved.
WordCertificate.lean: doneWorkerRows_ofPhaseCertificate is
conditional on CleanWorkerPhaseInv; doneWorkerRows_staticStep
only gives static values for one quiet edge.
futureWorkerCertificate_ofRowTransport and
qword_ofRowTransport are conditional on an all-row
CleanWorkerInv transport premise. The toy
rogueUniversalRowTransportFalse refutes that
unqualified universal transport premise, not a
strengthened canonical-history invariant.
The frontier certificates also have documented
closed counterexamples to naive local closure.

BankRepairWord.lean proves bankRepairWordStageOfProjectedClock
only under BankWordProjectedClock, a hitting-time obligation;
it does not furnish CleanWorkerPhaseInv at W acceptance.
The paper proof producer is research/paper/l3/appendices/
repair.tex, lem:e-word: clean-worker induction and subsequent
future-idempotence paragraphs (roughly lines 967--1024).

The witness root in AcceptedWord is existential. A distinct
BANK-root identification, if required, must also be justified
from the W history/native singleton; it is not a field of
wordValidated.

The consecutive clockwise reader sample-site geometry is a
separate uncompleted induction on R1c launch / R0b move.
This block does not claim that CleanWorkerWordValues
follows unconditionally from AcceptedWord, nor that
BankRepairReaderE22NoRootWindowReachability is closed.
-/

end L3.RenewalReferenceClock
