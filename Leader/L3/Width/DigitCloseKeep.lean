import Leader.L3.Width.DigitBoundary

/-!
# The boundary leader receipt along the width cuts

DESIGN-MOTIVATIONS 2026-11-02 08:45: every width cut from the boundary-retired cut on carries
`WidthDigitLeaderReceipt` (the boundary receipt at the W fixed leader).  This module supplies the
persistence and the stage lifting, for any `WidthBoundaryReference`:

* `boundaryWord`: the boundary receipt persists along every word on the layout-fixed class
  (`bankRepairDigitReceiptStep` lifted by `widthBoundaryDigitBankStepOf`; the generic form of
  BANK's `bankCleanDigitBoundaryReceiptOnWord`);
* `leaderWord`: on every continuation of a clean start, the leader receipt persists;
* `reachedOfFold`, `reachedOfZeroRun`, `reachedOfFirstZero`, `reachedOfStructural`,
  `reachedOfEntry`: the width cuts are continuations of a clean start;
* `leaderKeep`: a charged stage from continuations of a clean start lifts to the same stage with
  the leader receipt on both ends, at the same charge;
* `leaderBoundaryAt`: the leader receipt is the boundary receipt at the W fixed root.
-/

namespace L3.CloseKeep

set_option autoImplicit false

open L3
open L3.RenewalReferenceClock
open K2ArbitraryElimination.FiniteAccounting
open L3.WidthDigit
open L3.DigitStructuralClean

variable {n : Nat} {ring : DirectedRing n}

/-- **The boundary receipt persists along every word on the layout-fixed class** (any boundary
reference).  Consumer: `leaderWord`, `L3.CloseBoundary.readyAtClock`. -/
theorem boundaryWord (ref : WidthBoundaryReference ring) (hn : 5 ≤ n) (root : Fin n) :
    ∀ (w : List (Fin n)) (y : ref.State),
      WidthDigitLayoutFixed ref.toWidthDigitReference root y →
      DigitBoundaryReceipt ring root (piD (ref.phys y)) →
      DigitBoundaryReceipt ring root (piD (ref.phys (w.foldl ref.next y))) := by
  intro w
  induction w with
  | nil => intro y _ h; exact h
  | cons e rest ih =>
    intro y hy h
    exact ih _ (widthBoundaryDigitLayoutFixedStep ref root y hy e)
      (widthBoundaryDigitBankStepOf ref hn root (DigitBoundaryReceipt ring root)
        (fun S e hroot hbX hbY h => bankRepairDigitReceiptStep ring (by omega) root S e
          (bankRepairDigitLaneRowFactsHold _) hroot hbX hbY h) y hy e h)

/-- **The leader receipt persists on every continuation of a clean start.**  Consumer:
`leaderKeep`, `L3.ClosePersist.comparisonCutOfReady`. -/
theorem leaderWord (ref : WidthBoundaryReference ring) (hn : 5 ≤ n) (start : ref.State)
    (hst : ref.start start) (word : List (Fin n))
    (hL : WidthDigitLeaderReceipt ref.toWidthDigitReference (word.foldl ref.next start))
    (w : List (Fin n)) :
    WidthDigitLeaderReceipt ref.toWidthDigitReference (w.foldl ref.next (word.foldl ref.next start)) := by
  obtain ⟨r, hW, hB⟩ := hL
  obtain ⟨root0, hs, hLV⟩ := widthCleanBoundaryRoot ref start hst
  have hr : r = root0 :=
    (widthBoundaryDigitBoundaryWFixedRootOfSingleton ref root0 start hs word).2.1 r hW.1
  rw [hr] at hB
  refine ⟨root0, ?_, boundaryWord ref hn root0 w _
    (widthBoundaryDigitLayoutValuesWord ref root0 word start hLV).1 hB⟩
  rw [← List.foldl_append]
  exact widthBoundaryDigitBoundaryWFixedRootOfSingleton ref root0 start hs (word ++ w)

/-- The leader receipt is the boundary receipt at the W fixed root.  Consumer:
`L3.CloseBoundary.readyAtClock`. -/
theorem leaderBoundaryAt (ref : WidthDigitReference ring) (root : Fin n) (z : ref.State)
    (hW : WFixedRoot ring root (piW (ref.phys z))) (hL : WidthDigitLeaderReceipt ref z) :
    DigitBoundaryReceipt ring root (piD (ref.phys z)) := by
  obtain ⟨r, hW', hB⟩ := hL
  have hr : r = root := hW.2.1 r hW'.1
  rw [hr] at hB
  exact hB

/-- The state of a coupled run from a clean start is the reference run.  Consumer: the
`reachedOf…` lemmas. -/
theorem reachedOfFold (ref : WidthBoundaryReference ring) (start : ref.State)
    (word : List (Fin n)) (z : ref.State) (audit : DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (h : word.foldl (widthDigitAuditNext ref.toWidthDigitReference)
      (start, digitAuditInitial (piD (ref.phys start))) = (z, audit)) :
    z = word.foldl ref.next start := by
  have := widthBoundaryDigitBoundaryAuditFirst ref start
    (digitAuditInitial (piD (ref.phys start))) word
  rw [h] at this
  exact this

/-- A first-zero continuation is a continuation of a clean start.  Consumer: `reachedOfEntry`,
`L3.WriterStage.widthWaveClockOfWriter`. -/
theorem reachedOfZeroRun (ref : WidthBoundaryReference ring) (root : Fin n) (z : ref.State)
    (audit : DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (h : WidthZeroRun ref.toWidthDigitReference root (z, audit)) :
    ∃ (start : ref.State) (word : List (Fin n)), ref.start start ∧
      z = word.foldl ref.next start := by
  obtain ⟨start, word0, word, y, _, hst, hy, -, -, -, -, hx⟩ := h
  refine ⟨start, word0 ++ word, hst, reachedOfFold ref start (word0 ++ word) z audit ?_⟩
  rw [List.foldl_append, hy, hx]

/-- Consumer: `L3.WriterCore.bankWriterValueWaveOfMoments`, `L3.WriterStage.widthWaveClockOfWriter`. -/
theorem reachedOfFirstZero (ref : WidthBoundaryReference ring) (z : ref.State)
    (h : WidthDigitFirstZeroCut ref.toWidthDigitReference z) :
    ∃ (start : ref.State) (word : List (Fin n)), ref.start start ∧
      z = word.foldl ref.next start := by
  obtain ⟨start, word, _, audit, _, hst, hfold, -⟩ := h
  exact ⟨start, word, hst, reachedOfFold ref start word z audit hfold⟩

/-- Consumer: `L3.WriterCore.bankWriterValueWaveOfMoments`. -/
theorem reachedOfStructural (ref : WidthBoundaryReference ring) (z : ref.State)
    (h : WidthDigitStructuralCut ref.toWidthDigitReference z) :
    ∃ (start : ref.State) (word : List (Fin n)), ref.start start ∧
      z = word.foldl ref.next start := by
  obtain ⟨start, word, _, audit, _, _, _, hst, hfold, -⟩ := h
  exact ⟨start, word, hst, reachedOfFold ref start word z audit hfold⟩

/-- Consumer: `L3.WriterCore.bankWriterValueWaveOfMoments`, `L3.WriterStage.widthWaveClockOfWriter`. -/
theorem reachedOfEntry (ref : WidthBoundaryReference ring) (j : Nat) (z : ref.State)
    (h : WidthEntryCut ref.toWidthDigitReference j z) :
    ∃ (start : ref.State) (word : List (Fin n)), ref.start start ∧
      z = word.foldl ref.next start := by
  obtain ⟨root, audit, hrun, -⟩ := h
  exact reachedOfZeroRun ref root z audit hrun

/-- The first-zero cut carries the leader receipt.  Consumer: `L3.WriterCore.bankWriterValueWaveOfMoments`,
`L3.WriterStage.widthWaveClockOfWriter`. -/
theorem firstZeroLeader (ref : WidthDigitReference ring) (z : ref.State)
    (h : WidthDigitFirstZeroCut ref z) : WidthDigitLeaderReceipt ref z := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hL⟩ := h
  exact hL

/-- **A charged stage from continuations of a clean start keeps the leader receipt**, at the same
charge.  Consumer: `leaderWave`. -/
theorem leaderKeep (ref : WidthBoundaryReference ring) (hn : 5 ≤ n) (P Q : ref.State → Prop)
    (c : Nat)
    (hP : ∀ z, P z → ∃ (start : ref.State) (word : List (Fin n)), ref.start start ∧
      z = word.foldl ref.next start)
    (h : BankRepairDigitChargedStage ref.next P Q c) :
    BankRepairDigitChargedStage ref.next
      (fun z => P z ∧ WidthDigitLeaderReceipt ref.toWidthDigitReference z)
      (fun z => Q z ∧ WidthDigitLeaderReceipt ref.toWidthDigitReference z) c := by
  rintro z ⟨hz, hL⟩ T
  obtain ⟨start, word, hst, rfl⟩ := hP z hz
  exact Nat.le_trans (Nat.mul_le_mul_left 2 (bankRepairDigitCostTransfer ref.next ref.next
    (fun y => Q y ∧ WidthDigitLeaderReceipt ref.toWidthDigitReference y) Q T _ _
    (fun w hw => ⟨hw, leaderWord ref hn start hst word hL w⟩))) (h _ hz T)

/-- **Three composed stages keep the leader receipt**: stages `A → B → C → D` from continuations
of a clean start compose, with the leader receipt carried from `A`, into the stage from `A` with
the receipt to any `D'` that `D` and the receipt give.  Consumer:
`L3.WriterCore.bankWriterValueWaveOfMoments`, `L3.WriterStage.widthWaveClockOfWriter`. -/
theorem leaderWave (ref : WidthBoundaryReference ring) (hn : 5 ≤ n)
    (A B C D D' : ref.State → Prop) (a b c : Nat)
    (hA : ∀ z, A z → ∃ (start : ref.State) (word : List (Fin n)), ref.start start ∧
      z = word.foldl ref.next start)
    (hB : ∀ z, B z → ∃ (start : ref.State) (word : List (Fin n)), ref.start start ∧
      z = word.foldl ref.next start)
    (hC : ∀ z, C z → ∃ (start : ref.State) (word : List (Fin n)), ref.start start ∧
      z = word.foldl ref.next start)
    (h1 : BankRepairDigitChargedStage ref.next A B a)
    (h2 : BankRepairDigitChargedStage ref.next B C b)
    (h3 : BankRepairDigitChargedStage ref.next C D c)
    (hD : ∀ z, D z → WidthDigitLeaderReceipt ref.toWidthDigitReference z → D' z) :
    BankRepairDigitChargedStage ref.next
      (fun z => A z ∧ WidthDigitLeaderReceipt ref.toWidthDigitReference z) D' (a + b + c) :=
  bankRepairDigitChargedWeaken ref.next _ _ _ _ _ (fun _ h => h) (fun z h => hD z h.1 h.2)
    (bankRepairDigitZeroCompose ref.next _ _ _ _ _
      (bankRepairDigitZeroCompose ref.next _ _ _ _ _
        (leaderKeep ref hn A B a hA h1) (leaderKeep ref hn B C b hB h2))
      (leaderKeep ref hn C D c hC h3))

end L3.CloseKeep

#print axioms L3.CloseKeep.boundaryWord
#print axioms L3.CloseKeep.leaderWord
#print axioms L3.CloseKeep.leaderKeep
#print axioms L3.CloseKeep.leaderWave
