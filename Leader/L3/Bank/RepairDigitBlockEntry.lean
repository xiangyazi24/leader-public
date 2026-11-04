import Leader.L3.Bank.RepairDigitValueWaveClose
import Leader.L3.Bank.RepairDigitPairBlock

/-!
# T35: the block entry of the value wave

**Step 1 (`BlockEntryLift`).** `completionClockLower`: a `DigitCompletion` at cut `cut` has its
terminal at time `≥ 2 r + 2 + cut` (`r` = `digitSpan`: `r` samples after the cut, `r` exports
in reverse order after them, `r` uses in forward order after the first export, and the terminal
after the last use, all at distinct audit times), and at most the clock. Hence
`anchorClockLower` (an anchor needs `2R + 2 ≤ clock`) and `liftNeedsClock`: `BlockEntryLift`
forces every first-zero continuation with an interior first block to have audit clock
`≥ 2R + 2`, i.e. a whole cohort of the first pair completed and recorded **before** the value
wave starts. Nothing in the first-zero cut (base covers only) gives it; see the T35 notes.

**The anchor is not needed** (`L3.PairBlock`): the chain uses of the anchor only the complete
pair on the audit start, which is static. `structuralAnchor`: at a structural cut the anchors
exist (for the report: the anchor is the `DigitStructuralAt` receipt).

**Step 2 (the strengthened cuts).**
* `PairPin root src x`: the pair `(src, src + R)` is complete on the audit start, and some cycle
  ghost of its writer lane carries `WinInvD … (InheritedOk writer)` and `UseReach` on `x`.
* `PairsFrom j root x`: `PairPin` for every interior block `i ≥ j` of the first delimiter.
  Carried by every coupled letter (`pairsFromStep`: `winInvDStep`, `useReachStep`, and the
  ghost advanced by `windowGhost`).
* `EntryCut j z` (the `P' j`): `ValueBlockCut j` (first-zero continuation and the receipts of
  blocks `< j`) and `PairsFrom j`.
* `entryBlockStage`: `EntryCut j → EntryCut (j + 1)` at `200 n R`, with no hypothesis: block `j`
  starts at the block cut itself (`PairBlock.runPairBlock`, `after` = the clock, counter reset),
  and the pins of the later blocks are carried through it.

**Step 3 (the clocks).**
* `waveAfterEntry`: from `ReceiptsClose` alone, the charged stage
  `EntryCut 0 → ValuesStableCut` at `200 n^2`.
* `bankRepairDigitValueWaveClockOfPairs`: `BankRepairDigitValueWaveClock` from `ReceiptsClose`
  and `FirstZeroPairs` (the pins of all interior pairs at the first-zero cut: Lemma e-max's
  post-strict class in the cycle form, not formalized).
-/

namespace L3.BlockEntry

set_option autoImplicit false

open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree
open L3.RenewalReferenceClock
open L3.CohortStages
open L3.CohortTransfer
open L3.CohortLedger
open L3.FiveTransfer
open L3.Projection
open L3.CohortDomination
open L3.CohortTail
open L3.CohortSites
open L3.CohortEntry
open L3.PacketClass
open L3.Rearm
open L3.Recording
open L3.GhostBridge
open L3.Correspondence
open L3.CohortIdentity
open L3.CohortWindow
open L3.CohortClose
open L3.CohortOrder
open L3.BlockStart
open L3.FiveClose
open L3.HClose
open L3.CloseReceipt
open L3.FiveReach
open L3.ValueCorr
open L3.ValueLedger
open L3.SitePin
open L3.UseRows
open L3.UseCells
open L3.UseTrack
open L3.BlockCuts
open L3.ValueWaveClose
open L3.PairBlock

/-! ### Step 1: an anchor needs a long recorded past -/

/-- **A completion needs `2 r + 2` audit steps after its cut**: its terminal is at time
`≥ 2 r + 2 + cut` and `≤ clock`. Consumer: `anchorClockLower`. -/
theorem completionClockLower {c : Compiled} {n : Nat} (ring : DirectedRing n)
    (A : DigitAudit c n) (root : Fin n) (source target : Nat) (lane : DigitLane) (cut : Nat)
    (t : DigitTerminal c n) (h : DigitCompletion ring A root source target lane cut t) :
    2 * digitSpan c + 2 + cut ≤ t.time ∧ t.time ≤ A.clock := by
  obtain ⟨-, -, -, -, -, hclk, hpos, ledger, samples, exports, uses, -, -, -, hj, hord, -⟩ := h
  have hx : ∀ k m (hm : m < digitSpan c), m + k = digitSpan c - 1 →
      k + 2 + cut ≤ (exports ⟨m, hm⟩).time := by
    intro k
    induction k with
    | zero =>
        intro m hm _
        obtain ⟨-, -, -, h4, -, -, -, -, -, -, -, -, -, -, -, -, -, t1, -, -⟩ := hj ⟨m, hm⟩
        omega
    | succ k ih =>
        intro m hm hmk
        have h1 := ih (m + 1) (by omega) (by omega)
        have h2 := (hord ⟨m, hm⟩ ⟨m + 1, by omega⟩ (by show m < m + 1; omega)).1
        omega
  have hu : ∀ k (hk : k < digitSpan c), digitSpan c + 2 + cut + k ≤ (uses ⟨k, hk⟩).time := by
    intro k
    induction k with
    | zero =>
        intro hk
        have h1 := hx (digitSpan c - 1) 0 hk (by omega)
        obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, t2, -⟩ := hj ⟨0, hk⟩
        omega
    | succ k ih =>
        intro hk
        have h1 := ih (by omega)
        have h2 := (hord ⟨k, by omega⟩ ⟨k + 1, hk⟩ (by show k < k + 1; omega)).2
        omega
  have h1 := hu (digitSpan c - 1) (by omega)
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, t3⟩ :=
    hj ⟨digitSpan c - 1, by omega⟩
  have hp : 0 < digitSpan c := hpos
  exact ⟨by omega, hclk⟩

/-- **An anchor needs `2 R + 2` audit steps**: if `AnchorIn after A` then `2 r + 2 ≤ A.clock`.
Consumer: `liftNeedsClock` and the T35 report (step 1). -/
theorem anchorClockLower {n : Nat} (ring : DirectedRing n) (root : Fin n) (lane : DigitLane)
    (src R after : Nat) (A : DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (h : AnchorIn ring root lane src R after A) :
    2 * digitSpan (compileAdvice (ceilLogTwo n)) + 2 ≤ A.clock := by
  obtain ⟨t, ht, -⟩ := h
  have := completionClockLower ring A root src (src + R) lane 0 t ht
  omega

/-- **The anchor is the structural receipt**: at a structural cut `cut` every complete pair has
its anchor at `cut`. Consumer: the T35 report (where the anchor's cost goes). -/
theorem structuralAnchor {n : Nat} (ring : DirectedRing n) (root : Fin n) (lane : DigitLane)
    (src R cut : Nat) (A : DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (hp : PairIn ring root src R A) (hs : DigitStructuralAt ring root A cut) :
    AnchorIn ring root lane src R cut A := by
  obtain ⟨t, hfirst, ht⟩ := hs.2 src (src + R) lane hp
  exact ⟨t, hfirst.1, ht⟩

section Cuts

variable {n : Nat} (ring : DirectedRing n)
  (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)

/-- **`BlockEntryLift` forces a long past at the first-zero cut**: at every first-zero
continuation whose first block is interior, `BlockEntryLift` gives an anchor of the first pair,
hence an audit clock `≥ 2R + 2`. Consumer: the T35 report (step 1). -/
theorem liftNeedsClock (hlift : BlockEntryLift ring hbank) (root : Fin n) (first : Nat)
    (z : BankReferenceState ring hbank) (audit : DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (hrun : ZeroRun ring hbank root (z, audit))
    (hf : DigitFirstDelimiter ring root audit.start first) (h1 : 2 ≤ first)
    (h2 : first + 2 * valueSpan n < n) :
    2 * valueSpan n + 2 ≤ audit.clock := by
  obtain ⟨g, after, -, -, -, hanc⟩ := hlift 0 root first z audit hrun hf
    (fun i hi => absurd hi (Nat.not_lt_zero i)) (by rw [Nat.zero_mul, Nat.add_zero]; exact h1)
    (by rw [Nat.zero_mul, Nat.add_zero]; exact h2)
  exact anchorClockLower ring root DigitLane.writer _ _ after audit hanc

/-! ### Step 2: the strengthened cuts -/

/-- The lift data of one pair `(src, src + R)`: complete on the audit start, and a cycle ghost of
its writer lane with the strengthened window invariant and `UseReach`. -/
def PairPin (root : Fin n) (src : Nat)
    (x : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n) : Prop :=
  PairIn ring root src (valueSpan n) x.2 ∧
  ∃ g : (Nat → Nat) × Nat,
    WinInvD ring hbank root DigitLane.writer src (valueSpan n) (InheritedOk DigitLane.writer) x g ∧
    UseReach ring hbank root DigitLane.writer src (valueSpan n) (x, g)

/-- The lift data of every interior block `i ≥ j` (from the first delimiter of the audit
start). -/
def PairsFrom (j : Nat) (root : Fin n)
    (x : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n) : Prop :=
  ∀ first : Nat, DigitFirstDelimiter ring root x.2.start first → ∀ i, j ≤ i →
    2 ≤ first + i * valueSpan n → first + i * valueSpan n + 2 * valueSpan n < n →
    PairPin ring hbank root (first + i * valueSpan n) x

/-- **The strengthened block cut `P' j`**: `ValueBlockCut j` with the lift data of the interior
blocks `≥ j`. Consumer: `entryBlockStage`, `waveAfterEntry`. -/
def EntryCut (j : Nat) (z : BankReferenceState ring hbank) : Prop :=
  ∃ (root : Fin n) (audit : DigitAudit (compileAdvice (ceilLogTwo n)) n),
    ZeroRun ring hbank root (z, audit) ∧ (∀ i, i < j → BlockReceipt ring root audit i) ∧
    PairsFrom ring hbank j root (z, audit)

/-- The lift data of one interior pair is carried by every coupled letter (the ghost advances by
`windowGhost`). Consumer: `pairsFromStep`. -/
theorem pairPinStep (hn : 5 ≤ n) (root : Fin n) (src : Nat) (hsrc : 2 ≤ src)
    (hend : src + 2 * valueSpan n < n)
    (x : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (e : Fin n) (h : PairPin ring hbank root src x) :
    PairPin ring hbank root src (bankRepairDigitBoundaryAuditNext ring hbank x e) := by
  have hR := valueSpanTwo hn
  obtain ⟨hp, g, hw, hu⟩ := h
  exact ⟨hp, windowGhost ring hbank root DigitLane.writer src (valueSpan n) x g e,
    (winInvDStep ring hn hbank root DigitLane.writer src (valueSpan n) hR hsrc hend
      (InheritedOk DigitLane.writer) x g hw e).1,
    useReachStep ring hn hbank root DigitLane.writer src (valueSpan n) hR hsrc hend
      (InheritedOk DigitLane.writer) (x, g) e hw hu⟩

/-- `PairsFrom` is carried by every coupled letter (the audit start does not move). Consumer:
`entryBlockStage` (the pins of the later blocks ride along the run of block `j`). -/
theorem pairsFromStep (hn : 5 ≤ n) (j : Nat) (root : Fin n)
    (x : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (e : Fin n) (h : PairsFrom ring hbank j root x) :
    PairsFrom ring hbank j root (bankRepairDigitBoundaryAuditNext ring hbank x e) := by
  intro first hf i hi h1 h2
  exact pairPinStep ring hbank hn root _ h1 h2 x e (h first hf i hi h1 h2)

/-- Dropping block `j`. Consumer: `entryBlockStage`. -/
theorem pairsFromSucc (j : Nat) (root : Fin n)
    (x : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (h : PairsFrom ring hbank j root x) : PairsFrom ring hbank (j + 1) root x :=
  fun first hf i hi h1 h2 => h first hf i (by omega) h1 h2

/-- The pieces of an entry cut: by leader, and by the first delimiter (or its absence). -/
def EntryPiece (j : Nat) (root : Fin n) : Option Nat → BankReferenceState ring hbank → Prop
  | none, z => ∃ audit : DigitAudit (compileAdvice (ceilLogTwo n)) n,
      ZeroRun ring hbank root (z, audit) ∧
      (∀ first, ¬ DigitFirstDelimiter ring root audit.start first) ∧
      (∀ i, i < j → BlockReceipt ring root audit i) ∧ PairsFrom ring hbank j root (z, audit)
  | some first, z => ∃ audit : DigitAudit (compileAdvice (ceilLogTwo n)) n,
      ZeroRun ring hbank root (z, audit) ∧ DigitFirstDelimiter ring root audit.start first ∧
      (∀ i, i < j → BlockReceipt ring root audit i) ∧ PairsFrom ring hbank j root (z, audit)

/-- **The block stage `P' j → P' (j + 1)` at `200 n R`, with no hypothesis.** Empty blocks are
inclusions; an interior block `j` is `PairBlock.runPairBlock` on the window chain of its pair,
started at the block cut itself (the pinned ghost, counter reset to `0`, `after` = the clock),
split by leader, first delimiter and start clock; its finish records the receipt of block `j`,
and the pins of the blocks `> j` are carried through the run. Consumer: `waveAfterEntry`,
`bankRepairDigitValueWaveClockOfPairs`. -/
theorem entryBlockStage (hn : 5 ≤ n) (j : Nat) :
    CoupledBlock ring hbank (EntryCut ring hbank j) (EntryCut ring hbank (j + 1))
      (200 * n * valueSpan n) := by
  have hR := valueSpanTwo hn
  refine coupledBlockSigma ring hbank _ _ _
    (fun p : Fin n × Option Nat => EntryPiece ring hbank j p.1 p.2) ?_ ?_
  · rintro z ⟨root, audit, hrun, hrec, hpf⟩
    rcases Classical.em (∃ first, DigitFirstDelimiter ring root audit.start first) with
      ⟨first, hf⟩ | hno
    · exact ⟨(root, some first), audit, hrun, hf, hrec, hpf⟩
    · exact ⟨(root, none), audit, hrun, fun f hf => hno ⟨f, hf⟩, hrec, hpf⟩
  rintro ⟨root, o⟩
  cases o with
  | none =>
      refine coupledBlockOfImp ring hbank _ _ _ ?_
      rintro z ⟨audit, hrun, hno, -, hpf⟩
      exact ⟨root, audit, hrun, fun i _ first hf => absurd hf (hno first),
        pairsFromSucc ring hbank j root _ hpf⟩
  | some first =>
      rcases Classical.em (2 ≤ first + j * valueSpan n ∧
          first + j * valueSpan n + 2 * valueSpan n < n) with ⟨hsrc, hend⟩ | hg
      · refine coupledBlockSigma ring hbank _ _ _
          (fun after z => ∃ audit : DigitAudit (compileAdvice (ceilLogTwo n)) n,
            ZeroRun ring hbank root (z, audit) ∧ DigitFirstDelimiter ring root audit.start first ∧
            (∀ i, i < j → BlockReceipt ring root audit i) ∧
            PairsFrom ring hbank j root (z, audit) ∧ audit.clock = after) ?_ ?_
        · rintro z ⟨audit, hrun, hf, hrec, hpf⟩
          exact ⟨audit.clock, audit, hrun, hf, hrec, hpf, rfl⟩
        intro after
        refine runPairBlock ring hn hbank root DigitLane.writer (first + j * valueSpan n)
          (valueSpan n) hR hsrc (by omega) (InheritedOk DigitLane.writer) after _ _
          (fun w => ZeroRun ring hbank root w.1 ∧ DigitFirstDelimiter ring root w.1.2.start first ∧
            (∀ i, i < j → BlockReceipt ring root w.1.2 i) ∧
            PairsFrom ring hbank (j + 1) root w.1) ?_ ?_ ?_
        · intro w e _ hc
          exact ⟨zeroRunStep ring hbank root w.1 hc.1 e, hc.2.1,
            fun i hi => receiptStep ring root _ w.1.2 e i (hc.2.2.1 i hi),
            pairsFromStep ring hbank hn (j + 1) root w.1 e hc.2.2.2⟩
        · rintro z ⟨audit, hrun, hf, hrec, hpf, haft⟩
          obtain ⟨hp, g, hw, hu⟩ := hpf first hf j (Nat.le_refl j) hsrc hend
          exact ⟨((z, audit), (g.1, 0)), rfl,
            winInvDReset ring hbank root DigitLane.writer _ _ _ (z, audit) g hw 0,
            useReachReset ring hbank root DigitLane.writer _ _ (z, audit) g hu, rfl,
            by show after ≤ audit.clock; omega, hp, hrun, hf, hrec,
            pairsFromSucc ring hbank j root _ hpf⟩
        · intro w hfw hc
          refine ⟨root, w.1.2, hc.1, fun i hi => ?_, hc.2.2.2⟩
          rcases Nat.lt_or_ge i j with hij | hij
          · exact hc.2.2.1 i hij
          · have hie : i = j := by omega
            subst hie
            intro first' hf' _ _
            have he := firstDelimUnique ring root _ hc.2.1 hf'
            subst he
            exact ⟨after, hfw⟩
      · refine coupledBlockOfImp ring hbank _ _ _ ?_
        rintro z ⟨audit, hrun, hf, hrec, hpf⟩
        refine ⟨root, audit, hrun, fun i hi => ?_, pairsFromSucc ring hbank j root _ hpf⟩
        rcases Nat.lt_or_ge i j with hij | hij
        · exact hrec i hij
        · have hie : i = j := by omega
          subst hie
          intro first' hf' h1 h2
          have he := firstDelimUnique ring root _ hf hf'
          subst he
          exact absurd ⟨h1, h2⟩ hg

/-! ### Step 3: the clocks -/

/-- **The value wave after the entry cut, from `ReceiptsClose` alone**: `K = n / R` block stages
`entryBlockStage` of `200 n R` from `EntryCut 0` to `EntryCut K ⊆ ValuesStableCut`, within
`200 n^2`. Consumer: the T35 report (the clock in the interface where the entry is charged to
the structural phase) and `bankRepairDigitValueWaveClockOfPairs`. -/
theorem waveAfterEntry (hn : 5 ≤ n) (hclose : ReceiptsClose ring hbank) :
    BankRepairDigitChargedStage (bankRepairNext ring hbank) (EntryCut ring hbank 0)
      (BankRepairDigitValuesStableCut ring hbank) (bankRepairDigitValueWaveMicroCharge n) :=
  bankRepairDigitChargedMono _ _ _ (blockFit (valueBlocksFit n))
    (bankRepairDigitChargedWeaken _ (EntryCut ring hbank 0) (EntryCut ring hbank 0)
      (EntryCut ring hbank (valueBlocks n)) _ _ (fun _ h => h)
      (fun z ⟨root, audit, hrun, hrec, _⟩ => hclose root z audit hrun hrec)
      (bankRepairDigitChargedChain _ (EntryCut ring hbank) _
        (fun j => chargedOfCoupledBlock ring hbank _ _ _ (entryBlockStage ring hbank hn j))
        (valueBlocks n)))

/-- **The missing fact, as a structured hypothesis about the run**: at every first-zero cut
(all fields of `BankRepairDigitFirstZeroCut`), every interior block of the first delimiter of the
audit start is a complete pair on the audit start and carries a writer-lane cycle ghost with
`WinInvD … (InheritedOk writer)` and `UseReach` (Lemma e-max's post-strict class in the
settled cycle form of `winInvDEntry`, with the identity state). -/
def FirstZeroPairs : Prop :=
  ∀ (start : BankReferenceState ring hbank) (word : List (Fin n)) (root : Fin n)
    (z : BankReferenceState ring hbank) (audit : DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (retired : Nat),
    BankRepairRFoldEstablished ring hbank start →
    word.foldl (bankRepairDigitBoundaryAuditNext ring hbank)
      (start, digitAuditInitial (piD start.val.1)) = (z, audit) →
    WFixedRoot ring root (piW z.val.1) →
    DigitAt ring audit audit.clock (piD z.val.1) audit.current →
    DigitTwoBaseCovers ring root audit 0 retired audit.clock →
    PairsFrom ring hbank 0 root (z, audit)

/-- **`h0` for the strengthened cuts** from `FirstZeroPairs`. Consumer:
`bankRepairDigitValueWaveClockOfPairs`. -/
theorem entryOfFirstZero (hpairs : FirstZeroPairs ring hbank) (z : BankReferenceState ring hbank)
    (h : BankRepairDigitFirstZeroCut ring hbank z) : EntryCut ring hbank 0 z := by
  obtain ⟨start, word, root, audit, retired, hR, hfold, hW, hD, hC⟩ := h
  exact ⟨root, audit, ⟨start, word, [], (z, audit), retired, hR, hfold, hW, hD, hC, rfl⟩,
    fun i hi => absurd hi (Nat.not_lt_zero i), hpairs start word root z audit retired hR hfold hW
      hD hC⟩

/-- **The value-wave clock from `ReceiptsClose` and `FirstZeroPairs`**, with no other premise
beyond the BANK band and `5 ≤ n` (no `BlockEntryLift`, no anchor). Consumer: the third conjunct
of `BankRepairDigitFourMicroClocks` (`BankRepairDigitValueWaveClock`). -/
theorem bankRepairDigitValueWaveClockOfPairs (hn : 5 ≤ n) (hpairs : FirstZeroPairs ring hbank)
    (hclose : ReceiptsClose ring hbank) : BankRepairDigitValueWaveClock ring hbank :=
  valueWaveOfCoupledBlocks ring hbank (EntryCut ring hbank) (valueBlocks n) (valueSpan n)
    (entryOfFirstZero ring hbank hpairs) (entryBlockStage ring hbank hn)
    (fun z ⟨root, audit, hrun, hrec, _⟩ => hclose root z audit hrun hrec) (valueBlocksFit n)

end Cuts

end L3.BlockEntry

#print axioms L3.BlockEntry.completionClockLower
#print axioms L3.BlockEntry.anchorClockLower
#print axioms L3.BlockEntry.structuralAnchor
#print axioms L3.BlockEntry.liftNeedsClock
#print axioms L3.BlockEntry.pairPinStep
#print axioms L3.BlockEntry.pairsFromStep
#print axioms L3.BlockEntry.entryBlockStage
#print axioms L3.BlockEntry.waveAfterEntry
#print axioms L3.BlockEntry.entryOfFirstZero
#print axioms L3.BlockEntry.bankRepairDigitValueWaveClockOfPairs
