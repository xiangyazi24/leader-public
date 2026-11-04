import Leader.L3.Width.DigitQuietEntryValuesStep
import Leader.L3.Width.DigitQuietEntryBase

/-!
# `DigitValuesCorrect` at a chain end

Induction over the value chain with `L3.QuietEntryValues.writerPairStep`: from the base value cut on
no target cell holds the label `ZERO` (`noZeroBeyondFirst`, from the extinction of the old base
labels and the first-zero invariant) and each target block is quiet from the fifth terminal of its
pair on, given `FirstBlockZero` (the first segment holds zero from the base value cut on, proved in
WidthDigitQuietEntryValuesFirst), `chainFacts`.

Consumer: `L3.QuietEntryValues.valuesOfCut`, `quietOfCut` (WidthDigitQuietEntryValuesFinal).

Paper: research/lean-l3/ledgers/R10c-qdigit-notes.md section 9.
-/

namespace L3.QuietEntryValues

open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree
open L3
open L3.AcceptedReceipts
open L3.DigitQuiet
open L3.RenewalReferenceClock
open L3.WidthDigit
open L3.WidthWave
open L3.WidthPacketMoment
open L3.WidthPacketMomentCutEntry
open L3.WidthPacketMomentCompare
open L3.ClosePersist
open L3.WriterCurrent
open L3.WriterValueCuts
open L3.WriterCertificate
open L3.QuietEntryPair

set_option autoImplicit false
set_option linter.unusedSectionVars false

variable {n : Nat} {ring : DirectedRing n} (ref : WidthBoundaryReference ring) (hn : 5 ≤ n)

/-- The extinction of the base labels, at an earlier state.  Consumer: `noZeroAt`. -/
theorem extinctFoldBack (root : Fin n) (boundary retired : Nat) :
    ∀ (word : List (Fin n))
      (y : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n),
      DigitBaseExtinct ring root (word.foldl (widthDigitAuditNext ref.toWidthDigitReference) y).2
        boundary retired →
      retired ≤ y.2.clock → DigitBaseExtinct ring root y.2 boundary retired := by
  intro word
  induction word with
  | nil => intro y h _; exact h
  | cons e rest ih =>
    intro y h ht
    have h1 := ih (widthDigitAuditNext ref.toWidthDigitReference y e) h
      (by show retired ≤ y.2.clock + 1; omega)
    exact L3.ClosePersist.extinctBack ring _ _ e root boundary retired h1 ht

include hn in
/-- **No label `ZERO` beyond the first segment** once the old base labels are extinct.  Consumer:
`noZeroAt`. -/
theorem noZeroBeyondFirst (start : ref.State) (hst : ref.start start) (word : List (Fin n))
    (root : Fin n) (hs : ref.singleton root start) (first : Nat)
    (hf : DigitFirstDelimiter ring root (piD (ref.phys start)) first) (retired : Nat)
    (hext : DigitBaseExtinct ring root (word.foldl (widthDigitAuditNext ref.toWidthDigitReference)
      (start, digitAuditInitial (piD (ref.phys start)))).2 0 retired)
    (hret : retired ≤ (word.foldl (widthDigitAuditNext ref.toWidthDigitReference)
      (start, digitAuditInitial (piD (ref.phys start)))).2.clock)
    (k : Nat) (hk : k < n) (hk2 : first + digitSpan (compileAdvice (ceilLogTwo n)) ≤ k) :
    (piD (ref.phys (word.foldl (widthDigitAuditNext ref.toWidthDigitReference)
      (start, digitAuditInitial (piD (ref.phys start)))).1)
      (digitSite ring root k)).top.wBase ≠ .ZERO := by
  obtain ⟨root', hs', hV⟩ := widthCleanBoundaryRoot ref start hst
  have hr : root = root' :=
    (ref.singletonFixed root' start hs').2.1 root (ref.singletonFixed root start hs).1
  subst hr
  obtain ⟨f₀, ht, hft, hb₀⟩ := widthCleanBoundaryDelimiters ref hn root start hV
  have ht2 := compileAdvice_t_ge_two (ceilLogTwo n) (ringQ_facts n hn).1
  have hlead := L3.WriterOrderedClose.leadWidthBand (n := n) hn
  have hd : WidthBoundaryDigitLeadData ref root f₀ start := ⟨hV.1, by omega, by omega, hb₀⟩
  have hinv := widthFirstZeroInvWord ref hn root f₀ (by omega) _ word _
    (widthFirstZeroInvInitial ref root f₀ start hd)
  have hgone := goneOfExtinct ref hn root start 0 retired word hext hret
  generalize word.foldl (widthDigitAuditNext ref.toWidthDigitReference)
    (start, digitAuditInitial (piD (ref.phys start))) = y at hinv hgone ⊢
  obtain ⟨⟨-, -, hsound⟩, ⟨-, -, -, hbz⟩, hL, -⟩ := hinv
  have htoks := bankRepairDigitZeroToksOf ring root f₀ _ (piD (ref.phys y.1)) y.2.current hsound
    (fun i s h => hgone ⟨s, i, h⟩) hL
  have hff : first = f₀ := by
    have h1 := ((hb₀ first hf.1.1 hf.1.2.1).1 hf.1.2.2).1
    rcases Nat.lt_or_ge f₀ first with h | h
    · have h2 := hf.2 f₀ (by omega) h
      have h3 := (hb₀ f₀ (by omega) (by omega)).2 ⟨Nat.le_refl _, by simp⟩
      rw [h2] at h3
      cases h3
    · omega
  subst hff
  have hstop : widthFirstZeroStop n first ≤ first + digitSpan (compileAdvice (ceilLogTwo n)) :=
    Nat.min_le_left _ _
  intro hw
  have hne : (piD (ref.phys y.1) (digitSite ring root k)).top.wBase ≠ .NONE := by
    rw [hw]
    exact fun h => WBase.noConfusion h
  obtain ⟨-, hks, -, -⟩ := htoks.place k hk hne
  omega

/-- **The first segment holds zero from the base value cut on**: the base case of the chain.
Consumer: `chainFacts`, `valuesOfCut`; producer: `firstBlockZeroOfCovers`. -/
def FirstBlockZero (start : ref.State) (w : List (Fin n)) (root : Fin n)
    (first stop baseCut : Nat) : Prop :=
  ∀ k, first ≤ k → k < stop → k + 1 < n → ∀ t, baseCut ≤ t → t ≤ w.length →
    digitAt ref.toWidthDigitReference start w t (digitSite ring root k) =
      (compileAdvice (ceilLogTwo n)).zeroDigit

section Layout

variable {c : Compiled}

/-- A first segment is a whole block when the layout has period `digitSpan` and the next delimiter
is not past the root.  Consumer: `quietOfCut`. -/
theorem stopOfSegment {S : Fin n → ProjD c} {first stop : Nat} {root : Fin n}
    (hseg : DigitFirstSegment ring root S first stop)
    (hl : ∀ k, 0 < k → k < n → ((S (digitSite ring root k)).word.beta = true ↔
      first ≤ k ∧ (k - first) % digitSpan c = 0)) (hR : 0 < digitSpan c)
    (hfr : first + digitSpan c ≤ n) :
    first + digitSpan c ≤ stop := by
  obtain ⟨⟨h0, -, -⟩, hlt, hle, hstop, -⟩ := hseg.2
  refine Nat.le_of_not_gt fun hc => ?_
  have hbs := hstop (by omega)
  obtain ⟨-, hmod⟩ := (hl stop (by omega) (by omega)).1 hbs
  rw [Nat.mod_eq_of_lt (by omega)] at hmod
  omega

end Layout

/-- What the chain knows of one of its cuts at the end of the run.  Consumer: `chainFacts`,
`valuesOfCut`, `quietOfCut`. -/
structure CutFacts (start : ref.State) (w : List (Fin n)) (root : Fin n) (first baseCut previous : Nat)
    (target st : Nat) : Prop where
  base : baseCut ≤ st
  late : st ≤ previous
  low : first ≤ target
  quiet : target + digitSpan (compileAdvice (ceilLogTwo n)) < n →
    ∀ j, j < digitSpan (compileAdvice (ceilLogTwo n)) → ∀ t, st ≤ t → t < w.length →
      digitAt ref.toWidthDigitReference start w (t + 1) (digitSite ring root (target + j)) =
        digitAt ref.toWidthDigitReference start w t (digitSite ring root (target + j))
  link : target = first ∨ ∃ src, target = src + digitSpan (compileAdvice (ceilLogTwo n)) ∧
    valueBlockID ring root
        (digitValueView (piD (ref.phys (w.foldl (widthDigitAuditNext ref.toWidthDigitReference)
          (start, digitAuditInitial (piD (ref.phys start)))).1))) target =
      (valueBlockID ring root
        (digitValueView (piD (ref.phys (w.foldl (widthDigitAuditNext ref.toWidthDigitReference)
          (start, digitAuditInitial (piD (ref.phys start)))).1))) src + 1) %
        (compileAdvice (ceilLogTwo n)).topA ^ digitSpan (compileAdvice (ceilLogTwo n)) ∧
    (∀ j, j < digitSpan (compileAdvice (ceilLogTwo n)) →
      digitAt ref.toWidthDigitReference start w w.length (digitSite ring root (target + j)) =
        (compileAdvice (ceilLogTwo n)).digitMod
          ((digitAt ref.toWidthDigitReference start w w.length (digitSite ring root (src + j))).val +
            (if carryInto (fun k => digitAt ref.toWidthDigitReference start w w.length
              (digitSite ring root (src + k))) j then 1 else 0))) ∧
    ∃ (after born : Nat) (g : (Nat → Nat) × Nat),
      PairBundle ref.toWidthDigitReference root DigitLane.writer src
        (digitSpan (compileAdvice (ceilLogTwo n))) after born
        (stateAt ref.toWidthDigitReference start w w.length, g) ∧
      SamplesCurrent ring root DigitLane.writer src (digitSpan (compileAdvice (ceilLogTwo n))) after
        (stateAt ref.toWidthDigitReference start w w.length).2
        (piD (ref.phys (stateAt ref.toWidthDigitReference start w w.length).1))

include hn in
/-- **The facts along the chain**: each block of the chain is quiet from its cut on, and each target
block is the successor of its source block at the end of the run, with the pin bundle of its pair
there.  Consumer: `quietOfCut`. -/
theorem chainFacts (start : ref.State) (hst : ref.start start) (w : List (Fin n)) (root : Fin n)
    (hs : ref.singleton root start) (first stop baseCut retired structural : Nat)
    (hf : DigitFirstDelimiter ring root (piD (ref.phys start)) first)
    (hstopR : first + digitSpan (compileAdvice (ceilLogTwo n)) < n →
      first + digitSpan (compileAdvice (ceilLogTwo n)) ≤ stop)
    (hext : DigitBaseExtinct ring root (w.foldl (widthDigitAuditNext ref.toWidthDigitReference)
      (start, digitAuditInitial (piD (ref.phys start)))).2 0 retired)
    (hrb : retired ≤ baseCut)
    (hF : FirstBlockZero ref start w root first stop baseCut)
    {source previous : Nat} {cuts : List (Nat × Nat)}
    (hchain : DigitValueChain ring root (w.foldl (widthDigitAuditNext ref.toWidthDigitReference)
      (start, digitAuditInitial (piD (ref.phys start)))).2 structural first baseCut source previous
      cuts) :
    (source, previous) ∈ cuts ∧ ∀ target st, (target, st) ∈ cuts →
      CutFacts ref start w root first baseCut previous target st := by
  have hstart : (w.foldl (widthDigitAuditNext ref.toWidthDigitReference)
      (start, digitAuditInitial (piD (ref.phys start)))).2.start = piD (ref.phys start) := by
    have := L3.WriterReceipts.widthAuditStartFold ref.toWidthDigitReference w
      (start, digitAuditInitial (piD (ref.phys start)))
    exact this
  induction hchain with
  | start =>
    refine ⟨List.mem_singleton.mpr rfl, fun target st hm => ?_⟩
    simp only [List.mem_singleton, Prod.mk.injEq] at hm
    obtain ⟨rfl, rfl⟩ := hm
    refine ⟨Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, fun hfr j hj t h1 h2 => ?_, Or.inl rfl⟩
    have hk := hstopR hfr
    rw [hF (target + j) (by omega) (by omega) (by omega) t h1 (by omega),
      hF (target + j) (by omega) (by omega) (by omega) (t + 1) (by omega) (by omega)]
  | @next source' previous' cuts' h target terminal hp hc ih =>
    obtain ⟨htip, hall⟩ := ih
    have htipF := hall source' previous' htip
    obtain ⟨t1, t2, t3, t4, -, -, -, h1, h2, h3, h4, h5, -⟩ := hc
    have htg : target = source' + digitSpan (compileAdvice (ceilLogTwo n)) := hp.2.1
    subst htg
    have hsp : DigitCompletePair ring root (piD (ref.phys start)) source'
        (source' + digitSpan (compileAdvice (ceilLogTwo n))) := by
      rw [← hstart]
      exact hp
    have hendT := hsp.2.2.2
    have hTle := completionTimeLe ring _ h5.1
    have a1 := h1.2.1
    have a2 := h2.2.1
    have a3 := h3.2.1
    have a4 := h4.2.1
    have a5 := h5.2.1
    have hfs := htipF.low
    have hbp := htipF.base
    have hbl := htipF.late
    obtain ⟨hstepQ, hstepV, hstepD, ⟨born, g, hbun⟩, hsam⟩ := writerPairStep ref hn start hst w root
      hs source' hsp (max structural previous') terminal ⟨t1, t2, t3, t4, h1, h2, h3, h4, h5⟩
      (fun j hj t h3t h4t => htipF.quiet hsp.1.2 j hj t (by omega) h4t)
      (fun j hj t h3t h4t => by
        have hle : retired ≤ t := by omega
        have hk : source' + digitSpan (compileAdvice (ceilLogTwo n)) + j < n := by omega
        have hsplit : (w.drop t).foldl (widthDigitAuditNext ref.toWidthDigitReference)
            (stateAt ref.toWidthDigitReference start w t) = _ :=
          L3.StageMEntryRun.wRunAtSplit ref.toWidthDigitReference w
            (start, digitAuditInitial (piD (ref.phys start))) t
        have hcl := clockAt ref start w t h4t
        have hext' : DigitBaseExtinct ring root (stateAt ref.toWidthDigitReference start w t).2 0
            retired := by
          refine extinctFoldBack ref root 0 retired (w.drop t) _ ?_ (by omega)
          rw [hsplit]
          exact hext
        exact noZeroBeyondFirst ref hn start hst (w.take t) root hs first hf retired hext'
          (by rw [← hcl] at hle; exact hle) _ hk (by omega))
    have hTlate : previous' < terminal.time := by omega
    refine ⟨List.mem_cons_self .., fun tg st hm => ?_⟩
    rcases List.mem_cons.mp hm with he | hold
    · simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      refine ⟨by omega, Nat.le_refl _, by omega, fun _ j hj t h3t h4t => hstepQ j hj t h3t h4t, ?_⟩
      exact Or.inr ⟨source', rfl, hstepV, hstepD, _, born, g, hbun, hsam⟩
    · have hF0 := hall tg st hold
      exact ⟨hF0.base, by have := hF0.late; omega, hF0.low, hF0.quiet, hF0.link⟩

end L3.QuietEntryValues

#print axioms L3.QuietEntryValues.noZeroBeyondFirst
#print axioms L3.QuietEntryValues.chainFacts
