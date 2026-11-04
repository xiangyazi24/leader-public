import Leader.L3.Width.DigitQuietEntryPairCheck
import Leader.L3.Width.DigitQuietEntryBase
import Leader.L3.Width.DigitComparisonCertificateWord

/-!
# The quiet class at a writer comparison cut: the certificate

* `valuesOfCut`: `DigitValuesCorrect` at the cut, from `firstBlockZeroOfCovers` and `chainFacts`;
* `pairWriterOfCut`, `pairComparisonOfCut`: `PairQuiet` of both lanes;
* `quietOfCut`: `WidthWriterQuietAtCut` on a boundary reference, assembled with `quietPartsOfCut`;
* `widthWriterCertificateOfBand`: the headline premise `hcert` of `l3HeadlineOfCleanBranches`.

Paper: research/lean-l3/ledgers/R10c-qdigit-notes.md section 9.
-/

namespace L3.QuietEntryValues

open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree
open L3
open L3.AcceptedReceipts
open L3.DigitQuiet
open L3.QuietEntryPair
open L3.RenewalReferenceClock
open L3.WidthDigit
open L3.WidthWave
open L3.WidthPacketMoment
open L3.WidthPacketMomentCutEntry
open L3.WidthPacketMomentCompare
open L3.WidthPacketMomentGroupCompletion
open L3.CohortDomination
open L3.CohortTail
open L3.CohortSites
open L3.CohortEntry
open L3.PacketClass
open L3.CohortStages
open L3.Rearm
open L3.Recording
open L3.GhostBridge
open L3.Correspondence
open L3.CohortIdentity
open L3.CohortWindow
open L3.CohortClose
open L3.ValueCorr
open L3.ValueLedger
open L3.UseRows
open L3.UseCells
open L3.UseTrack
open L3.SitePin
open L3.DigitEntryPhase
open L3.ValueWaveClose
open L3.StageMEntry
open L3.StageMEntryPin
open L3.StageMEntryRun
open L3.StageMEntryCarryRows
open L3.StageMEntryPack
open L3.StageMEntryCyc
open L3.ClosePersist
open L3.CloseBoundary
open L3.PairBlock
open L3.FiveTransfer
open L3.TailChain
open L3.TailAhead
open L3.TermEntry
open L3.CurrentWin
open L3.CloseCurrent
open L3.CloseEntry
open L3.CloseRank
open L3.CloseOrder
open L3.WriterOrder
open L3.CohortOrder
open L3.WriterCurrent
open L3.WriterAged
open L3.WriterValueCuts
open L3.WriterCertificate
open L3.DigitPairsClean

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-- A block of zeros has value zero.  Consumer: `valuesOfCut`. -/
theorem blockZero {c : Compiled} {n : Nat} (ring : DirectedRing n) (root : Fin n)
    (v : Fin n → Bool × Fin c.topA) (start : Nat)
    (h : ∀ m, m < digitSpan c → (v (digitSite ring root (start + m))).2 = c.zeroDigit) :
    valueBlockID ring root v start = 0 := by
  have key : ∀ m, m ≤ digitSpan c →
      (List.range m).foldl (fun acc h =>
        acc + c.topA ^ h * (v (digitSite ring root (start + h))).2.val) 0 = 0 := by
    intro m
    induction m with
    | zero => intro _; rfl
    | succ m ih =>
      intro hm
      rw [List.range_succ, List.foldl_append, ih (by omega)]
      simp [h m (by omega), Compiled.zeroDigit]
  exact key _ (Nat.le_refl _)

/-- The next delimiter depends only on the delimiters.  Consumer: `valuesOfCut`. -/
theorem nextCongr {c : Compiled} {n : Nat} {ring : DirectedRing n} {S T : Fin n → ProjD c}
    (root : Fin n) (hb : ∀ i, (S i).word.beta = (T i).word.beta) {a b : Nat}
    (h : DigitNextDelimiterOrRoot ring root S a b) : DigitNextDelimiterOrRoot ring root T a b := by
  obtain ⟨⟨h4, h5, h6⟩, h7, h8, h9, h10⟩ := h
  exact ⟨⟨h4, h5, by rw [← hb]; exact h6⟩, h7, h8, fun x => by rw [← hb]; exact h9 x,
    fun k x y => by rw [← hb]; exact h10 k x y⟩

variable {n : Nat} {ring : DirectedRing n} (ref : WidthBoundaryReference ring) (hn : 5 ≤ n)

include hn in
/-- The delimiters along the run.  Consumer: `quietOfCut`. -/
theorem betaAt (start : ref.State) (w : List (Fin n)) (root : Fin n)
    (h0 : WidthDigitLayoutFixed ref.toWidthDigitReference root start) (m : Nat) (hm : m ≤ w.length)
    (i : Fin n) :
    (piD (ref.phys (stateAt ref.toWidthDigitReference start w m).1) i).word.beta =
      (piD (ref.phys start) i).word.beta := by
  induction m with
  | zero => rfl
  | succ m ih =>
    obtain ⟨e, he⟩ := stateStep ref.toWidthDigitReference start w m (by omega)
    rw [he]
    exact (betaLetter ref hn root _ (layoutAt ref start w root h0 m (by omega)) e i).trans
      (ih (by omega))

/-- The state at the end of the word.  Consumer: `quietOfCut`. -/
theorem stateEnd (start : ref.State) (w : List (Fin n)) :
    stateAt ref.toWidthDigitReference start w w.length =
      w.foldl (widthDigitAuditNext ref.toWidthDigitReference)
        (start, digitAuditInitial (piD (ref.phys start))) := by
  unfold stateAt
  rw [List.take_length]

include hn in
/-- **`DigitValuesCorrect` at the end of a run with the chain.**  Consumer: `quietOfCut`. -/
theorem valuesOfCut (start : ref.State) (hst : ref.start start) (w : List (Fin n)) (root : Fin n)
    (hs : ref.singleton root start) (first stop baseCut restart : Nat) (cuts : List (Nat × Nat))
    (hf2 : 2 ≤ first) (hlay : ∀ k, 0 < k → k < n → ((piD (ref.phys start) (digitSite ring root k)).word.beta = true ↔
      first ≤ k ∧ (k - first) % digitSpan (compileAdvice (ceilLogTwo n)) = 0))
    (hseg : DigitFirstSegment ring root (piD (ref.phys start)) first stop)
    (hstopR : first + digitSpan (compileAdvice (ceilLogTwo n)) < n →
      first + digitSpan (compileAdvice (ceilLogTwo n)) ≤ stop)
    (hFZ : FirstBlockZero ref start w root first stop baseCut)
    (hbeta : ∀ i, (piD (ref.phys (stateAt ref.toWidthDigitReference start w w.length).1) i).word.beta =
      (piD (ref.phys start) i).word.beta)
    (hall : ∀ target st, (target, st) ∈ cuts →
      CutFacts ref start w root first baseCut restart target st)
    (hcover : ∀ block, DigitCompleteBlock ring root (piD (ref.phys start)) block →
      ∃ stable, (block, stable) ∈ cuts)
    (hclk : baseCut ≤ w.length) :
    DigitValuesCorrect ring root (digitValueView (piD (ref.phys
      (w.foldl (widthDigitAuditNext ref.toWidthDigitReference)
        (start, digitAuditInitial (piD (ref.phys start)))).1))) := by
  have hR : 2 ≤ digitSpan (compileAdvice (ceilLogTwo n)) := valueSpanTwo hn
  have hE := stateEnd ref start w
  have hbz : ∀ i, (piD (ref.phys (w.foldl (widthDigitAuditNext ref.toWidthDigitReference)
      (start, digitAuditInitial (piD (ref.phys start)))).1) i).word.beta =
      (piD (ref.phys start) i).word.beta := by
    rw [← hE]
    exact hbeta
  have hzero : ∀ k, first ≤ k → k < stop → k + 1 < n →
      (piD (ref.phys (w.foldl (widthDigitAuditNext ref.toWidthDigitReference)
        (start, digitAuditInitial (piD (ref.phys start)))).1) (digitSite ring root k)).top.d =
        (compileAdvice (ceilLogTwo n)).zeroDigit := by
    intro k h1 h2 h3
    have := hFZ k h1 h2 h3 w.length hclk (Nat.le_refl _)
    unfold digitAt at this
    rw [hE] at this
    exact this
  have hfirst : ∀ f, firstValueDelimiter ring root (digitValueView (piD (ref.phys
      (w.foldl (widthDigitAuditNext ref.toWidthDigitReference)
        (start, digitAuditInitial (piD (ref.phys start)))).1))) f → f = first := by
    rintro f ⟨⟨h0, h1, h2⟩, h3⟩
    have hd : DigitFirstDelimiter ring root (piD (ref.phys start)) f :=
      ⟨⟨h0, h1, by rw [← hbz]; exact h2⟩, fun k a b => by rw [← hbz]; exact h3 k a b⟩
    exact L3.ValueWaveClose.firstDelimUnique ring root _ hd hseg.1
  refine ⟨?_, ?_, ?_⟩
  · rintro i ⟨f', s', k, hf', hs', hk1, hk2, hk3, rfl⟩
    have hff := hfirst f' hf'
    subst hff
    have hsegS : DigitFirstSegment ring root (piD (ref.phys start)) f' s' := by
      refine ⟨hseg.1, ?_⟩
      exact nextCongr root hbz hs'
    have hss := stopUnique root hsegS hseg
    subst hss
    exact hzero k hk1 hk2 hk3
  · intro f' hf' hblock
    have hff := hfirst f' hf'
    subst hff
    refine blockZero ring root _ f' fun m hm => ?_
    have hstop := hstopR hblock.2
    exact hzero (f' + m) (by omega) (by omega) (by have := hblock.2; omega)
  · intro source target hsb htg htb
    subst htg
    have hT : DigitCompleteBlock ring root (piD (ref.phys start))
        (source + digitSpan (compileAdvice (ceilLogTwo n))) := ⟨nextCongr root hbz htb.1, htb.2⟩
    obtain ⟨st, hm⟩ := hcover _ hT
    have hsrc := ((hlay source hsb.1.1.1 hsb.1.1.2.1).1 (by rw [← hbz]; exact hsb.1.1.2.2)).1
    rcases (hall _ st hm).link with h | ⟨src, he, hv, -⟩
    · omega
    · have : src = source := by omega
      subst this
      exact hv

include hn in
/-- **`PairQuiet` of the writer lane at the end of a run with the chain.**  Consumer: `quietOfCut`. -/
theorem pairWriterOfCut (start : ref.State) (hst : ref.start start) (w : List (Fin n)) (root : Fin n)
    (src : Nat) (after born : Nat) (g : (Nat → Nat) × Nat)
    (hbun : PairBundle ref.toWidthDigitReference root DigitLane.writer src
      (digitSpan (compileAdvice (ceilLogTwo n))) after born
      (stateAt ref.toWidthDigitReference start w w.length, g))
    (hsam : SamplesCurrent ring root DigitLane.writer src (digitSpan (compileAdvice (ceilLogTwo n)))
      after (stateAt ref.toWidthDigitReference start w w.length).2
      (piD (ref.phys (stateAt ref.toWidthDigitReference start w w.length).1))) :
    PairQuiet ring root (piD (ref.phys (stateAt ref.toWidthDigitReference start w w.length).1))
      DigitLane.writer src (src + digitSpan (compileAdvice (ceilLogTwo n))) := by
  have hd : ref.toWidthDigitReference.drained start := ref.startDrained start hst
  have hall : L3.CarryAll (piD (ref.phys (stateAt ref.toWidthDigitReference start w w.length).1))
      (stateAt ref.toWidthDigitReference start w w.length).2.current :=
    (auditCarryInv_fold ref.toWidthDigitReference (w.take w.length)
      (start, digitAuditInitial (piD (ref.phys start))) hd (auditCarryInv_initial ring _)).2.1
  exact pairQuietOfBundle ref.toWidthDigitReference root DigitLane.writer src _ after born rfl _ hbun
    hsam (carryBitsWriter ref.toWidthDigitReference root src _ after born _ hbun hsam hall)

include hn in
/-- **`PairQuiet` of the comparison lane at the end of a run**: the pin bundle from the first strict
comparison completion after the restart, the source and target digits quiet from the restart.
Consumer: `quietOfCut`. -/
theorem pairComparisonOfCut (start : ref.State) (hst : ref.start start) (w : List (Fin n)) (root : Fin n)
    (hs : ref.singleton root start) (src restart : Nat) (U : DigitTerminal (compileAdvice (ceilLogTwo n)) n)
    (hsp : DigitCompletePair ring root (piD (ref.phys start)) src
      (src + digitSpan (compileAdvice (ceilLogTwo n))))
    (hU : DigitCompletion ring (w.foldl (widthDigitAuditNext ref.toWidthDigitReference)
      (start, digitAuditInitial (piD (ref.phys start)))).2 root src
      (src + digitSpan (compileAdvice (ceilLogTwo n))) DigitLane.comparison restart U)
    (hsrc : ∀ j, j < digitSpan (compileAdvice (ceilLogTwo n)) → ∀ t, restart ≤ t → t < w.length →
      digitAt ref.toWidthDigitReference start w (t + 1) (digitSite ring root (src + j)) =
        digitAt ref.toWidthDigitReference start w t (digitSite ring root (src + j)))
    (htgt : ∀ j, j < digitSpan (compileAdvice (ceilLogTwo n)) → ∀ t, restart ≤ t → t < w.length →
      digitAt ref.toWidthDigitReference start w (t + 1)
          (digitSite ring root (src + digitSpan (compileAdvice (ceilLogTwo n)) + j)) =
        digitAt ref.toWidthDigitReference start w t
          (digitSite ring root (src + digitSpan (compileAdvice (ceilLogTwo n)) + j)))
    (hE : ∀ k, k < digitSpan (compileAdvice (ceilLogTwo n)) →
      digitAt ref.toWidthDigitReference start w w.length
          (digitSite ring root (src + digitSpan (compileAdvice (ceilLogTwo n)) + k)) =
        (compileAdvice (ceilLogTwo n)).digitMod
          ((digitAt ref.toWidthDigitReference start w w.length (digitSite ring root (src + k))).val +
            (if carryInto (fun m => digitAt ref.toWidthDigitReference start w w.length
              (digitSite ring root (src + m))) k then 1 else 0))) :
    PairQuiet ring root (piD (ref.phys (stateAt ref.toWidthDigitReference start w w.length).1))
      DigitLane.comparison src (src + digitSpan (compileAdvice (ceilLogTwo n))) := by
  have hd : ref.toWidthDigitReference.drained start := ref.startDrained start hst
  have hn2 : 2 ≤ n := by omega
  obtain ⟨root0, hs0, hL⟩ := widthCleanBoundaryRoot ref start hst
  have hr : root = root0 :=
    (ref.singletonFixed root0 start hs0).2.1 root (ref.singletonFixed root start hs).1
  subst hr
  obtain ⟨hsrc2, hend, -⟩ := pairLayoutStart ref hn root start hL src hsp
  have hR : 2 ≤ digitSpan (compileAdvice (ceilLogTwo n)) := valueSpanTwo hn
  obtain ⟨s, -, si, sl, -, hcs, L, v, hLU, hv, -, hhead⟩ :=
    completionTail ring _ root src _ DigitLane.comparison restart U hU
  have hv0 : L.uses[0]? = some v := by
    have e : L.uses.head? = L.uses[0]? := by cases L.uses <;> rfl
    exact e.symm.trans hv
  obtain ⟨hsu, huT⟩ := useLate _ root src _ DigitLane.comparison restart U hU s.id hhead L hLU 0 v hv0
  have hUle : U.time ≤ w.length := by
    have := completionTimeLe ring _ hU
    have hc := clockAt ref start w w.length (Nat.le_refl _)
    rw [stateEnd] at hc
    omega
  have hc4 := clockAt ref start w U.time hUle
  have hback : DigitCompletion ring (stateAt ref.toWidthDigitReference start w U.time).2 root src
      (src + digitSpan (compileAdvice (ceilLogTwo n))) DigitLane.comparison restart U := by
    refine completionFoldBack ref root src _ DigitLane.comparison restart U (w.drop U.time) _ ?_
      (Nat.le_of_eq hc4.symm)
    have hsplit := wRunAtSplit ref.toWidthDigitReference w
      (start, digitAuditInitial (piD (ref.phys start))) U.time
    have hst' : stateAt ref.toWidthDigitReference start w U.time =
        wRunAt ref.toWidthDigitReference (start, digitAuditInitial (piD (ref.phys start))) w
          U.time := rfl
    rw [hst', hsplit]
    exact hU
  have hb0 := bundleAtTerminal ref hn start hst (w.take U.time) root hs DigitLane.comparison src hsp
    restart restart U hback hc4.symm s.id si sl hhead (by omega) (by omega)
  have hb1 := bundleLater ref hn start w root DigitLane.comparison src _ hR hsrc2 hend restart U.time
    U.time hb0 (w.length - U.time) (by omega)
  rw [show U.time + (w.length - U.time) = w.length by omega] at hb1
  obtain ⟨g, hbun⟩ := hb1
  have hsam := samplesCurrentAt ref.toWidthDigitReference start w hd root DigitLane.comparison src
    (digitSpan (compileAdvice (ceilLogTwo n))) restart w.length (Nat.le_refl _) hsrc
  refine pairQuietOfBundle ref.toWidthDigitReference root DigitLane.comparison src _ restart U.time rfl _
    hbun hsam ?_
  refine carryBitsComparison ref.toWidthDigitReference root src _ hn2 start hd w restart U.time g
    (by omega) hbun hsam (fun k hk t h1 h2 => ?_) hE
  exact (digitAtConst ref.toWidthDigitReference start w _ t w.length (by omega)
    (fun t' h3 h4 => htgt k hk t' (by omega) h4)).symm

include hn in
/-- **The quiet class at a writer comparison cut.**  Consumer: `widthWriterCertificateOfBand`. -/
theorem quietOfCut : WidthWriterQuietAtCut ref.toWidthDigitReference := by
  intro z _ hcut root hfixed
  obtain ⟨first, hroot, ⟨hf2, hfn, hlayZ⟩, hbase, hleading, hsegZ, hseg8, hfrag⟩ :=
    quietPartsOfCut ref hn z hcut root hfixed
  refine ⟨first, ?_⟩
  obtain ⟨start, word, root', audit, retired, restart, cmp, hst, hrun, hfixed', hat, hrec, hready, -⟩ :=
    hcut
  have hrr : root' = root := hfixed.2.1 root' hfixed'.1
  subst hrr
  have hzf : (word.foldl (widthDigitAuditNext ref.toWidthDigitReference)
      (start, digitAuditInitial (piD (ref.phys start)))).1 = z := congrArg Prod.fst hrun
  have haf : (word.foldl (widthDigitAuditNext ref.toWidthDigitReference)
      (start, digitAuditInitial (piD (ref.phys start)))).2 = audit := congrArg Prod.snd hrun
  subst hzf
  subst haf
  have hE := stateEnd ref start word
  have hd : ref.toWidthDigitReference.drained start := ref.startDrained start hst
  obtain ⟨root0, hs0, hV⟩ := widthCleanBoundaryRoot ref start hst
  have hfix0 := widthBoundaryDigitBoundaryWFixedRootOfSingleton ref root0 start hs0 word
  have hzn : (word.foldl (widthDigitAuditNext ref.toWidthDigitReference)
      (start, digitAuditInitial (piD (ref.phys start)))).1 = word.foldl ref.next start :=
    widthBoundaryDigitBoundaryAuditFirst ref start _ word
  rw [← hzn] at hfix0
  have hrr0 : root' = root0 := hfix0.2.1 root' hfixed.1
  subst hrr0
  have hs := hs0
  have hbetaS := betaAt ref hn start word root' hV.1 word.length (Nat.le_refl _)
  have hbetaZ : ∀ i, (piD (ref.phys (word.foldl (widthDigitAuditNext ref.toWidthDigitReference)
      (start, digitAuditInitial (piD (ref.phys start)))).1) i).word.beta =
      (piD (ref.phys start) i).word.beta := by
    rw [← hE]
    exact hbetaS
  have hlay : ∀ k, 0 < k → k < n → ((piD (ref.phys start) (digitSite ring root' k)).word.beta = true ↔
      first ≤ k ∧ (k - first) % digitSpan (compileAdvice (ceilLogTwo n)) = 0) := by
    intro k h0 hk
    rw [← hbetaZ]
    exact hlayZ k h0 hk
  obtain ⟨firstA, stopA, baseCut, structural, last, cuts, hseg, hbaseCut, hbd, -, hchain, hcover⟩ := hrec
  have hstartA : (word.foldl (widthDigitAuditNext ref.toWidthDigitReference)
      (start, digitAuditInitial (piD (ref.phys start)))).2.start = piD (ref.phys start) :=
    L3.WriterReceipts.widthAuditStartFold ref.toWidthDigitReference word _
  rw [hstartA] at hseg hcover
  have hfA : firstA = first := firstDelimEq ring root' _ first hlay (by omega) hfn firstA hseg.1
  subst hfA
  have hR : 2 ≤ digitSpan (compileAdvice (ceilLogTwo n)) := valueSpanTwo hn
  have hcov := hbaseCut.1
  have hFZ := firstBlockZeroOfCovers ref hn start hst word root' hs firstA stopA retired baseCut hseg
    hbd hcov
  have hstopR : firstA + digitSpan (compileAdvice (ceilLogTwo n)) < n →
      firstA + digitSpan (compileAdvice (ceilLogTwo n)) ≤ stopA := fun h =>
    stopOfSegment hseg hlay (by omega) (by omega)
  obtain ⟨htip, hall⟩ := chainFacts ref hn start hst word root' hs firstA stopA baseCut retired
    structural hseg.1 hstopR hcov.1 hcov.2.1 hFZ hchain
  have hbase2 : baseCut ≤ word.length := by
    have h1 := hcov.2.2.1
    have hc := clockAt ref start word word.length (Nat.le_refl _)
    rw [hE] at hc
    omega
  have hvalues := valuesOfCut ref hn start hst word root' hs firstA stopA baseCut restart cuts hf2 hlay
    hseg hstopR hFZ hbetaS hall hcover hbase2
  refine { rootFixed := hroot, layout := ⟨hf2, hfn, hlayZ⟩, values := hvalues, base := hbase,
           leading := hleading, firstSegment := hsegZ, pairs := ?_, fragment := hfrag }
  intro lane j hj
  have hRpos : 0 < digitSpan (compileAdvice (ceilLogTwo n)) := by omega
  have hE1 : firstA + (j + 1) * digitSpan (compileAdvice (ceilLogTwo n)) =
      firstA + j * digitSpan (compileAdvice (ceilLogTwo n)) +
        digitSpan (compileAdvice (ceilLogTwo n)) := by
    rw [Nat.succ_mul, Nat.add_assoc]
  have hE2 : firstA + (j + 2) * digitSpan (compileAdvice (ceilLogTwo n)) =
      firstA + j * digitSpan (compileAdvice (ceilLogTwo n)) +
        digitSpan (compileAdvice (ceilLogTwo n)) + digitSpan (compileAdvice (ceilLogTwo n)) := by
    rw [show j + 2 = j + 1 + 1 by omega, Nat.succ_mul, Nat.succ_mul]
    omega
  rw [hE1]
  rw [hE2] at hj
  generalize hsrcD : firstA + j * digitSpan (compileAdvice (ceilLogTwo n)) = src at hj ⊢
  have hm0 : ∀ m, (m * digitSpan (compileAdvice (ceilLogTwo n))) %
      digitSpan (compileAdvice (ceilLogTwo n)) = 0 := fun m => Nat.mul_mod_left _ _
  have hS : DigitCompleteBlock ring root' (piD (ref.phys start)) src := by
    rw [← hsrcD]
    exact completeBlockOfDelims ring root' _ firstA hlay _ (hm0 j) (by omega) (by omega) (by omega)
  have hT : DigitCompleteBlock ring root' (piD (ref.phys start))
      (src + digitSpan (compileAdvice (ceilLogTwo n))) := by
    rw [← hsrcD, ← hE1]
    exact completeBlockOfDelims ring root' _ firstA hlay _ (hm0 (j + 1)) (by omega)
      (by rw [hE1]; omega) (by omega)
  have hsp : DigitCompletePair ring root' (piD (ref.phys start)) src
      (src + digitSpan (compileAdvice (ceilLogTwo n))) := ⟨hS, rfl, hT⟩
  obtain ⟨st, hmT⟩ := hcover _ hT
  obtain ⟨sts, hmS⟩ := hcover _ hS
  have cfT := hall _ st hmT
  have cfS := hall _ sts hmS
  have hsrcPos : firstA ≤ src := by omega
  rcases cfT.link with h0 | ⟨src', he, -, hdig, after, born, g, hbun, hsam⟩
  · omega
  have hss : src' = src := by omega
  subst hss
  cases lane with
  | writer =>
    have := pairWriterOfCut ref hn start hst word root' src' after born g hbun hsam
    rw [hE] at this
    exact this
  | comparison =>
    obtain ⟨-, -, hex, -⟩ := hready.1
    rw [hstartA] at hex
    obtain ⟨U, -, -, hstrict, -⟩ := hex src' _ hsp
    have := pairComparisonOfCut ref hn start hst word root' hs src' restart U hsp hstrict.1
      (fun j hj t h1 h2 => cfS.quiet hS.2 j hj t (by have := cfS.late; omega) h2)
      (fun j hj t h1 h2 => cfT.quiet hT.2 j hj t (by have := cfT.late; omega) h2)
      hdig
    rw [hE] at this
    exact this

end L3.QuietEntryValues

namespace L3.WriterCertificate

open L3.WidthDigit

/-- **The headline premise `hcert`**: `WidthWriterComparisonCertificate` at the band reference (SMALL
and BANK through their boundary references, `L3.QuietEntryValues.quietOfCut`).  Consumer: `hcert` of
`l3HeadlineOfCleanBranches` (Leader/L3/Headline/CleanAssembly.lean). -/
theorem widthWriterCertificateOfBand {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    :
    L3.WriterValueCuts.WidthWriterComparisonCertificate (bandWidthDigitReference ring hn) := by
  by_cases hs : (compileAdvice (ceilLogTwo n)).useSmall = true
  · rw [bandWidthDigitReferenceSmall ring hn hs]
    exact writerCertificateOfQuiet (smallWidthBoundaryReference ring hn hs) hn
      (L3.QuietEntryValues.quietOfCut (smallWidthBoundaryReference ring hn hs) hn)
  · have hb : (compileAdvice (ceilLogTwo n)).useSmall = false := by
      cases hh : (compileAdvice (ceilLogTwo n)).useSmall
      · rfl
      · exact absurd hh hs
    rw [bandWidthDigitReferenceBank ring hn hb]
    exact writerCertificateOfQuiet (bankWidthBoundaryReference ring hn hb) hn
      (L3.QuietEntryValues.quietOfCut (bankWidthBoundaryReference ring hn hb) hn)

end L3.WriterCertificate

#print axioms L3.QuietEntryValues.valuesOfCut
#print axioms L3.QuietEntryValues.pairWriterOfCut
#print axioms L3.QuietEntryValues.pairComparisonOfCut
#print axioms L3.QuietEntryValues.quietOfCut
#print axioms L3.WriterCertificate.widthWriterCertificateOfBand
