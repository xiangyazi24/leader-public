import Leader.L3.Width.DigitWriterCycle
import Leader.L3.Width.DigitWriterOrdered
import Leader.L3.Width.DigitWriterReceipts
import Leader.L3.Width.DigitBand

/-!
# The headline premise `hord`: ordered receipts give the writer values-stable cut

`L3.WriterOrdered.WidthWriterOrderedReceiptsClose` on every boundary reference and at the band:

* `tailRankUnique`: a border tail has one rank from the anchor tail;
* `anchorMemberBorder`: the only anchor member at the source delimiter is the anchor tail;
* `completionRankPos`: a completion whose tail is later than the anchor tail is ranked `p + 1` by
  `L3.TailAhead.groupCause`, with the same rank on its tail sample and a ranked cause tail;
* `nextCompletionLe`, `fiveCohortOfWindow`: five completions in a window `(a, b]` with `after ≤ a`
  give `DigitFiveCohortCompletions` after `after` with last terminal by `b`; the next completion
  has the next rank (`L3.WriterCycle.tailCauseOfNext`, `tailRankUnique`);
* `lastIndex`, `blockIndex`, `firstSegmentOfDelims`, `valueChainOf`, `leadWidthBand`: the layout
  and the chain along the blocks;
* `writerOrderedCloseOf`: the assembly (first segment, base value cut, first writer structural
  cut, value chain, coverage);
* `bandWriterOrderedClose`: the premise at the band reference.
-/

namespace L3.WriterOrderedClose

set_option autoImplicit false
set_option linter.unusedSectionVars false

open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree
open L3
open L3.HeadlineRenewal
open L3.RenewalReferenceClock
open L3.WidthDigit
open L3.WidthPacketMoment
open L3.WidthPacketMomentCutEntry
open L3.WidthPacketMomentGroupCompletion
open L3.GhostBridge
open L3.Correspondence
open L3.CohortIdentity
open L3.CohortDomination
open L3.ValueWaveClose
open L3.DigitCohortScratch
open L3.DigitPairsClean
open L3.StageMEntryRun
open L3.StageMEntryCyc
open L3.FiveTransfer
open L3.TailChain
open L3.TailAhead
open L3.CloseEntry
open L3.CloseRank
open L3.CloseOrder
open L3.WriterOrder
open L3.WriterCycle
open L3.WriterValueCuts
open L3.WriterOrdered

section Rank

variable {c : Compiled} {n : Nat}

/-- **A border tail has one rank from the anchor tail** (recorded samples are unique, and the
chain of causes is strictly older).  Consumer: `fiveCohortOfWindow`. -/
theorem tailRankUnique {A : DigitAudit c n} {lane : DigitLane} {src0 : Fin n}
    {sigma0 : DigitStamp n} (hfo : AuditFrameOrder A) {t : DigitStamp n} {k : Nat}
    (h : DigitTailRank A lane src0 sigma0 t k) :
    ∀ {t' : DigitStamp n} {k' : Nat}, DigitTailRank A lane src0 sigma0 t' k' → t = t' → k = k' := by
  induction h with
  | anchor =>
    intro t' k' h' he
    cases h' with
    | anchor => rfl
    | successor hprev sample rearm recorded sampleLane sampleSource sampleTail cause rearmLane
        rearmSource previousBefore rearmBefore =>
      exfalso
      have := tailRankTimeGe hprev
      rw [← he] at rearmBefore
      omega
  | successor hprev sample rearm recorded sampleLane sampleSource sampleTail cause rearmLane
      rearmSource previousBefore rearmBefore ih =>
    intro t' k' h' he
    cases h' with
    | anchor =>
      exfalso
      have := tailRankTimeGe hprev
      rw [he] at rearmBefore
      omega
    | successor hprev' sample' rearm' recorded' sampleLane' sampleSource' sampleTail' cause'
        rearmLane' rearmSource' previousBefore' rearmBefore' =>
      have hss : sample = sample' := recordedSampleUnique hfo recorded recorded' he
      subst hss
      rw [cause] at cause'
      simp only [Option.some.injEq, DigitUnread.afterTail.injEq, DigitAtom.sampled.injEq] at cause'
      obtain ⟨-, hprevEq⟩ := cause'
      rw [ih hprev' hprevEq]

/-- **The only anchor member at the source delimiter is the anchor tail.**  Consumer:
`completionRankPos`. -/
theorem anchorMemberBorder (ring : DirectedRing n) (A : DigitAudit c n) (root : Fin n) (src : Nat)
    (lane : DigitLane) (hend : src + 2 * digitSpan c < n) (anchor : DigitTerminal c n)
    (anchorTail id : DigitStamp n)
    (hanc : DigitCompletion ring A root src (src + digitSpan c) lane 0 anchor)
    (hhead : ∀ (L : DigitCarryGhost c n) (u : DigitUse c n), anchor.ledger = some L →
      L.uses.head? = some u → u.operand = some (.sampled anchorTail))
    (hm : DigitAnchorMember anchor id) (hsite : id.site = digitSite ring root src) :
    id = anchorTail := by
  obtain ⟨-, -, -, -, -, -, pos, L, sm, _ex, us, hL, -, hlen, hall, -, -⟩ := hanc
  obtain ⟨L', use, hL', huse, hop⟩ := hm
  have hLL : L' = L := Option.some.inj (hL'.symm.trans hL)
  subst hLL
  obtain ⟨i, hi, hget⟩ := List.mem_iff_getElem.mp huse
  have hj : i < digitSpan c := by rw [← hlen]; exact hi
  obtain ⟨-, -, si, -, -, -, -, -, -, -, -, -, ui, -, uo, -⟩ := hall ⟨i, hj⟩
  have h' : L'.uses[i]? = some use := by rw [List.getElem?_eq_getElem hi, hget]
  have hu' : us ⟨i, hj⟩ = use := Option.some.inj (ui.symm.trans h')
  have e : (sm ⟨i, hj⟩).id = id := by
    rw [hu'] at uo
    have e0 := uo.symm.trans hop
    simp only [Option.some.injEq, DigitAtom.sampled.injEq] at e0
    exact e0
  rw [e, hsite] at si
  have hi0 := bankRepairDigitSiteInj ring root (by omega) (by simp only at hj ⊢; omega) si
  have hi00 : i = 0 := by simp only at hi0; omega
  subst hi00
  have hhd : L'.uses.head? = some use := by
    have e1 : L'.uses.head? = L'.uses[0]? := by cases L'.uses <;> rfl
    exact e1.trans h'
  have e2 := (hhead L' use hL' hhd).symm.trans hop
  simp only [Option.some.injEq, DigitAtom.sampled.injEq] at e2
  exact e2.symm

/-- **The rank of a completion after the anchor tail**: on the run invariants, a completion whose
tail sample `σ` is later than the anchor tail is `DigitTerminalRank` `p + 1`, the tail itself is
ranked `p + 1`, and its cause names a tail ranked `p`.  Consumer: `fiveCohortOfWindow`. -/
theorem completionRankPos (ring : DirectedRing n) (root : Fin n) (lane : DigitLane) (src : Nat)
    (hend : src + 2 * digitSpan c < n) (Base : Bool → DigitAtom n → Prop)
    (S : Fin n → ProjD c) (A : DigitAudit c n) (hfo : AuditFrameOrder A)
    (hgd : GhostCorrDistinct ring root lane src (digitSpan c) Base S A)
    (htail : ∀ sigma0, TailInv ring root lane src (digitSpan c) sigma0 S A)
    (hah : AheadRun ring root lane src (digitSpan c) S A)
    (anchor N : DigitTerminal c n) (anchorTail : DigitStamp n) (hanchorRec : ∃ s0 : DigitSample c n,
      DigitRecordedSample A s0 ∧ s0.id = anchorTail)
    (hasite : anchorTail.site = digitSite ring root src) (halane : anchorTail.lane = lane)
    (hanc : DigitCompletion ring A root src (src + digitSpan c) lane 0 anchor)
    (hahead : ∀ (L : DigitCarryGhost c n) (u : DigitUse c n), anchor.ledger = some L →
      L.uses.head? = some u → u.operand = some (.sampled anchorTail))
    (hN : DigitCompletion ring A root src (src + digitSpan c) lane 0 N)
    (σ : DigitSample c n) (hσ : DigitRecordedSample A σ)
    (hσs : σ.id.site = digitSite ring root src) (hσl : σ.id.lane = lane) (hσt : σ.tail = true)
    (hσh : ∀ (L : DigitCarryGhost c n) (u : DigitUse c n), N.ledger = some L →
      L.uses.head? = some u → u.operand = some (.sampled σ.id))
    (hlate : anchorTail.time < σ.id.time) :
    ∃ (p : Nat) (prev rearm : DigitStamp n),
      DigitTailRank A lane (digitSite ring root src) anchorTail prev p ∧
      σ.cause = some (.afterTail rearm (some (.sampled prev))) ∧
      DigitTailRank A lane (digitSite ring root src) anchorTail σ.id (p + 1) ∧
      DigitTerminalRank A lane (digitSite ring root src) anchor anchorTail N (p + 1) := by
  obtain ⟨L, r, hL, hi, hne, hall⟩ := groupCause ring root lane src hend Base S A hfo hgd htail hah 0
    N hN anchorTail hanchorRec hasite halane (fun L u id hL hu hop => by
      have e := (hσh L u hL hu).symm.trans hop
      simp only [Option.some.injEq, DigitAtom.sampled.injEq] at e
      rw [← e]
      exact hlate) anchor
  -- the first use
  obtain ⟨u0, hu0⟩ : ∃ u0, L.uses.head? = some u0 := by
    cases hc : L.uses with
    | nil => exact absurd hc hne
    | cons a rest => exact ⟨a, rfl⟩
  have hmem : u0 ∈ L.uses := by
    cases hc : L.uses with
    | nil => exact absurd hc hne
    | cons a rest =>
      rw [hc] at hu0
      have : a = u0 := Option.some.inj hu0
      rw [this]
      exact List.mem_cons_self
  obtain ⟨smp, hop, hrec, hlane, hor⟩ := hall u0 hmem
  have hsm : smp = σ := by
    have e := hop.symm.trans (hσh L u0 hL hu0)
    simp only [Option.some.injEq, DigitAtom.sampled.injEq] at e
    exact recordedSampleUnique hfo hrec hσ e
  subst hsm
  rcases hor with ⟨-, hmemb⟩ | ⟨prev, p, rearm, hr, hprev, hc, hrl, hrs, h1, h2⟩
  · exfalso
    have := anchorMemberBorder ring A root src lane hend anchor anchorTail smp.id hanc hahead hmemb
      hσs
    rw [this] at hlate
    exact Nat.lt_irrefl _ hlate
  · subst hr
    refine ⟨p, prev, rearm, hprev, hc,
      DigitTailRank.successor hprev smp rearm hrec hlane hσs hσt hc hrl (hrs.trans hσs) h1 h2,
      hN.2.2.1, L, hL, hi, hne, hall⟩

end Rank

section Coupled

variable {n : Nat} {ring : DirectedRing n}

/-- **A next completion exists, by any completion after the time.**  Consumer:
`fiveCohortOfWindow`. -/
theorem nextCompletionLe {c : Compiled} (A : DigitAudit c n) (root : Fin n)
    (source target : Nat) (lane : DigitLane) (after : Nat) (t : DigitTerminal c n)
    (ht : DigitCompletion ring A root source target lane 0 t) (hlt : after < t.time) :
    ∃ N : DigitTerminal c n, DigitNextCompletion ring A root source target lane after N ∧
      N.time ≤ t.time := by
  obtain ⟨N, ⟨h1, h2⟩, hmin⟩ := minTerminal
    (fun o => DigitCompletion ring A root source target lane 0 o ∧ after < o.time) t.time t
    (Nat.le_refl _) ⟨ht, hlt⟩
  exact ⟨N, ⟨h1, h2, fun o ho hl => hmin o ⟨ho, hl⟩⟩, hmin t ⟨ht, hlt⟩⟩

variable (ref : WidthBoundaryReference ring) (hn : 5 ≤ n) (root : Fin n) (src : Nat)
  (hR : 2 ≤ digitSpan (compileAdvice (ceilLogTwo n))) (hsrc : 2 ≤ src)
  (hend : src + 2 * digitSpan (compileAdvice (ceilLogTwo n)) < n)
  (q0 : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n)
  (hq0 : L3.WidthPacketMomentCutEntry.WidthRunInv ring ref root DigitLane.writer src
    (digitSpan (compileAdvice (ceilLogTwo n))) q0)
  (hi0 : q0.2 = digitAuditInitial (piD (ref.phys q0.1))) (hc0 : q0.2.clock = 0)
  (W : List (Fin n))

include hn hR hsrc hend hq0 hi0 hc0 in
/-- **Five completions in a window give the five cohort completions**: on the run from a start
with the run invariant, with the anchor no later than `after ≤ a`, five completions in `(a, b]`
give the five next completions after `after`, the last by `b`, with consecutive ranks from a
positive rank: the first by `completionRankPos` (strict tail order against the anchor), the others
by `tailCauseOfNext` and `tailRankUnique`.  Consumer: `writerOrderedCloseOf`. -/
theorem fiveCohortOfWindow (after a b : Nat) (hle : after ≤ a)
    (anchor : DigitTerminal (compileAdvice (ceilLogTwo n)) n)
    (hanc : DigitFirstStrictCompletion ring (wRunAt ref.toWidthDigitReference q0 W W.length).2 root
      src (src + digitSpan (compileAdvice (ceilLogTwo n))) DigitLane.writer 0 anchor)
    (hat : anchor.time ≤ after)
    (hc : FwdChainBy ring (wRunAt ref.toWidthDigitReference q0 W W.length).2 root src
      (src + digitSpan (compileAdvice (ceilLogTwo n))) DigitLane.writer 5 a b) :
    ∃ last : DigitTerminal (compileAdvice (ceilLogTwo n)) n,
      DigitFiveCohortCompletions ring (wRunAt ref.toWidthDigitReference q0 W W.length).2 root src
        (src + digitSpan (compileAdvice (ceilLogTwo n))) DigitLane.writer after last ∧
      last.time ≤ b := by
  have hEnd := laneRunFold ref hn root DigitLane.writer src _ hR hsrc hend W q0 hq0
    (by rw [hi0]; exact laneRunInitial ref root DigitLane.writer src _ hR q0.1)
  rw [← wRunAtLen ref.toWidthDigitReference W q0 W.length (Nat.le_refl _)] at hEnd
  obtain ⟨⟨⟨-, hfo, -, -, hgd⟩, -⟩, htail, hah, -, ⟨-, hI2⟩, -, hD2⟩ := hEnd
  generalize hAe : (wRunAt ref.toWidthDigitReference q0 W W.length).2 = A at *
  -- the five completions of the window and the five next completions
  rw [fwdChainBySucc] at hc
  obtain ⟨t1, ht1, h1a, -, hc⟩ := hc
  rw [fwdChainBySucc] at hc
  obtain ⟨t2, ht2, h2a, -, hc⟩ := hc
  rw [fwdChainBySucc] at hc
  obtain ⟨t3, ht3, h3a, -, hc⟩ := hc
  rw [fwdChainBySucc] at hc
  obtain ⟨t4, ht4, h4a, -, hc⟩ := hc
  rw [fwdChainBySucc] at hc
  obtain ⟨t5, ht5, h5a, h5b, -⟩ := hc
  obtain ⟨N1, hN1, hN1t⟩ := nextCompletionLe A root src _ DigitLane.writer after t1 ht1 (by omega)
  obtain ⟨N2, hN2, hN2t⟩ := nextCompletionLe A root src _ DigitLane.writer N1.time t2 ht2 (by omega)
  obtain ⟨N3, hN3, hN3t⟩ := nextCompletionLe A root src _ DigitLane.writer N2.time t3 ht3 (by omega)
  obtain ⟨N4, hN4, hN4t⟩ := nextCompletionLe A root src _ DigitLane.writer N3.time t4 ht4 (by omega)
  obtain ⟨N5, hN5, hN5t⟩ := nextCompletionLe A root src _ DigitLane.writer N4.time t5 ht5 (by omega)
  -- the anchor tail and the tails
  obtain ⟨sa, hdanc, hsar, hsas, hsal, hahead⟩ := anchorOfFirst ring A root src _ DigitLane.writer
    anchor hanc
  have tailOf : ∀ N : DigitTerminal (compileAdvice (ceilLogTwo n)) n,
      DigitCompletion ring A root src (src + digitSpan (compileAdvice (ceilLogTwo n)))
        DigitLane.writer 0 N →
      ∃ s : DigitSample (compileAdvice (ceilLogTwo n)) n, DigitRecordedSample A s ∧
        s.id.site = digitSite ring root src ∧ s.id.lane = DigitLane.writer ∧ s.tail = true ∧
        ∀ (L : DigitCarryGhost (compileAdvice (ceilLogTwo n)) n)
          (u : DigitUse (compileAdvice (ceilLogTwo n)) n), N.ledger = some L →
          L.uses.head? = some u → u.operand = some (.sampled s.id) := by
    intro N hN
    obtain ⟨s, h1, h2, h3, h4, -, L, u, hL, hu, hop, hall⟩ :=
      completionTail ring A root src _ DigitLane.writer 0 N hN
    refine ⟨s, h1, h2, h3, h4, fun L' u' hL' hu' => ?_⟩
    have hLL : L' = L := Option.some.inj (hL'.symm.trans hL)
    subst hLL
    have huu : u' = u := Option.some.inj (hu'.symm.trans hu)
    subst huu
    exact hop
  have strict : ∀ (T0 T : DigitTerminal (compileAdvice (ceilLogTwo n)) n)
      (s0 s : DigitSample (compileAdvice (ceilLogTwo n)) n),
      DigitCompletion ring A root src (src + digitSpan (compileAdvice (ceilLogTwo n)))
        DigitLane.writer 0 T0 →
      DigitCompletion ring A root src (src + digitSpan (compileAdvice (ceilLogTwo n)))
        DigitLane.writer 0 T → T0.time < T.time →
      (∀ (L : DigitCarryGhost (compileAdvice (ceilLogTwo n)) n)
        (u : DigitUse (compileAdvice (ceilLogTwo n)) n), T0.ledger = some L →
        L.uses.head? = some u → u.operand = some (.sampled s0.id)) →
      (∀ (L : DigitCarryGhost (compileAdvice (ceilLogTwo n)) n)
        (u : DigitUse (compileAdvice (ceilLogTwo n)) n), T.ledger = some L →
        L.uses.head? = some u → u.operand = some (.sampled s.id)) →
      s0.id.time < s.id.time := by
    intro T0 T s0 s hT0 hT hlt h0 h1
    have hh0 := termHeadOfCompletion ring A root src DigitLane.writer 0 T0 s0.id hT0 h0
    have hh1 := termHeadOfCompletion ring A root src DigitLane.writer 0 T s.id hT h1
    rcases Nat.lt_or_ge s0.id.time s.id.time with hl | hge
    · exact hl
    · exfalso
      have hle2 := hI2 T0 s0.id T s.id hh0 hh1 hlt
      have he : s0.id = s.id := stampEq (by omega) (by rw [hh0.2.2.2.1, hh1.2.2.2.1])
        (by rw [hh0.2.2.2.2.1, hh1.2.2.2.2.1])
      rw [← he] at hh1
      exact hD2 T0 T s0.id hh0 hh1 hlt
  obtain ⟨σ1, r1, si1, l1, ta1, hd1⟩ := tailOf N1 hN1.1
  obtain ⟨σ2, r2, si2, l2, ta2, hd2⟩ := tailOf N2 hN2.1
  obtain ⟨σ3, r3, si3, l3, ta3, hd3⟩ := tailOf N3 hN3.1
  obtain ⟨σ4, r4, si4, l4, ta4, hd4⟩ := tailOf N4 hN4.1
  obtain ⟨σ5, r5, si5, l5, ta5, hd5⟩ := tailOf N5 hN5.1
  have hlt1 := strict anchor N1 sa σ1 hanc.1 hN1.1 (by have := hN1.2.1; omega) hahead hd1
  have hlt2 := strict N1 N2 σ1 σ2 hN1.1 hN2.1 hN2.2.1 hd1 hd2
  have hlt3 := strict N2 N3 σ2 σ3 hN2.1 hN3.1 hN3.2.1 hd2 hd3
  have hlt4 := strict N3 N4 σ3 σ4 hN3.1 hN4.1 hN4.2.1 hd3 hd4
  have hlt5 := strict N4 N5 σ4 σ5 hN4.1 hN5.1 hN5.2.1 hd4 hd5
  have rankOf : ∀ (N : DigitTerminal (compileAdvice (ceilLogTwo n)) n)
      (σ : DigitSample (compileAdvice (ceilLogTwo n)) n),
      DigitCompletion ring A root src (src + digitSpan (compileAdvice (ceilLogTwo n)))
        DigitLane.writer 0 N → DigitRecordedSample A σ →
      σ.id.site = digitSite ring root src → σ.id.lane = DigitLane.writer → σ.tail = true →
      (∀ (L : DigitCarryGhost (compileAdvice (ceilLogTwo n)) n)
        (u : DigitUse (compileAdvice (ceilLogTwo n)) n), N.ledger = some L →
        L.uses.head? = some u → u.operand = some (.sampled σ.id)) →
      sa.id.time < σ.id.time → _ :=
    fun N σ hN hr hs hl ht hd hlate => completionRankPos ring root DigitLane.writer src hend
      (InheritedOk DigitLane.writer) _ A hfo hgd htail hah anchor N sa.id ⟨sa, hsar, rfl⟩ hsas hsal
      hanc.1 hahead hN σ hr hs hl ht hd hlate
  have step : ∀ (T N : DigitTerminal (compileAdvice (ceilLogTwo n)) n)
      (σT σN : DigitSample (compileAdvice (ceilLogTwo n)) n) (r : Nat),
      DigitNextCompletion ring A root src (src + digitSpan (compileAdvice (ceilLogTwo n)))
        DigitLane.writer T.time N →
      DigitCompletion ring A root src (src + digitSpan (compileAdvice (ceilLogTwo n)))
        DigitLane.writer 0 T →
      DigitRecordedSample A σT → σT.id.site = digitSite ring root src →
      σT.id.lane = DigitLane.writer →
      (∀ (L : DigitCarryGhost (compileAdvice (ceilLogTwo n)) n)
        (u : DigitUse (compileAdvice (ceilLogTwo n)) n), T.ledger = some L →
        L.uses.head? = some u → u.operand = some (.sampled σT.id)) →
      DigitRecordedSample A σN → σN.id.site = digitSite ring root src →
      σN.id.lane = DigitLane.writer → σN.tail = true →
      (∀ (L : DigitCarryGhost (compileAdvice (ceilLogTwo n)) n)
        (u : DigitUse (compileAdvice (ceilLogTwo n)) n), N.ledger = some L →
        L.uses.head? = some u → u.operand = some (.sampled σN.id)) →
      σT.id.time < σN.id.time →
      DigitTailRank A DigitLane.writer (digitSite ring root src) sa.id σT.id r →
      DigitTailRank A DigitLane.writer (digitSite ring root src) sa.id σN.id (r + 1) ∧
        DigitTerminalRank A DigitLane.writer (digitSite ring root src) anchor sa.id N (r + 1) := by
    intro T N σT σN r hN hT hTr hTs hTl hTd hNr hNs hNl hNt hNd hlt hrank
    have hge := tailRankTimeGe hrank
    obtain ⟨p, prev, rearm, hprev, hc, hr1, hr2⟩ := rankOf N σN hN.1 hNr hNs hNl hNt hNd (by omega)
    have hAe' : (wRunAt ref.toWidthDigitReference q0 W W.length).2 = A := hAe
    have hprevEq : prev = σT.id := by
      subst hAe
      exact tailCauseOfNext ref hn root DigitLane.writer src _ hR hsrc hend q0 hq0 hi0 hc0 W rfl T N
        σT.id σN.id hT hN.1 hN.2.2 hTd hNd hlt σT hTr rfl hTs hTl σN hNr rfl hNs hNl rearm prev hc
    subst hprevEq
    have hpr : r = p := tailRankUnique hfo hrank hprev rfl
    subst hpr
    exact ⟨hr1, hr2⟩
  obtain ⟨p1, prev1, rearm1, hprev1, hc1, hr1T, hr1R⟩ := rankOf N1 σ1 hN1.1 r1 si1 l1 ta1 hd1 hlt1
  obtain ⟨hr2T, hr2R⟩ := step N1 N2 σ1 σ2 _ hN2 hN1.1 r1 si1 l1 hd1 r2 si2 l2 ta2 hd2 hlt2 hr1T
  obtain ⟨hr3T, hr3R⟩ := step N2 N3 σ2 σ3 _ hN3 hN2.1 r2 si2 l2 hd2 r3 si3 l3 ta3 hd3 hlt3 hr2T
  obtain ⟨hr4T, hr4R⟩ := step N3 N4 σ3 σ4 _ hN4 hN3.1 r3 si3 l3 hd3 r4 si4 l4 ta4 hd4 hlt4 hr3T
  obtain ⟨hr5T, hr5R⟩ := step N4 N5 σ4 σ5 _ hN5 hN4.1 r4 si4 l4 hd4 r5 si5 l5 ta5 hd5 hlt5 hr4T
  refine ⟨N5, ⟨N1, N2, N3, N4, anchor, sa.id, p1 + 1, hN1, hN2, hN3, hN4, hN5, hdanc, hat, by omega,
    ?_⟩, by omega⟩
  exact DigitSerialTerminalRanks.next _ N1 _ hr1R (DigitSerialTerminalRanks.next _ N2 _ hr2R
    (DigitSerialTerminalRanks.next _ N3 _ hr3R (DigitSerialTerminalRanks.next _ N4 _ hr4R
      (DigitSerialTerminalRanks.next _ N5 _ hr5R (DigitSerialTerminalRanks.empty _)))))

end Coupled

section Top

variable {n : Nat} {ring : DirectedRing n}

/-- A last index: below `B`, either `0` or a satisfying index above every satisfying index.
Consumer: `writerOrderedCloseOf`. -/
theorem lastIndex (P : Nat → Prop) (B : Nat) :
    ∃ m, m ≤ B ∧ (m = 0 ∨ P m) ∧ ∀ j, j ≤ B → P j → j ≤ m := by
  induction B with
  | zero => exact ⟨0, Nat.le_refl _, Or.inl rfl, fun _ hj _ => hj⟩
  | succ B ih =>
    obtain ⟨m, hm, h0, hmax⟩ := ih
    by_cases hp : P (B + 1)
    · exact ⟨B + 1, Nat.le_refl _, Or.inr hp, fun _ hj _ => hj⟩
    · refine ⟨m, by omega, h0, fun j hj hpj => ?_⟩
      rcases Nat.lt_or_ge j (B + 1) with h | h
      · exact hmax j (by omega) hpj
      · have e : j = B + 1 := by omega
        subst e
        exact absurd hpj hp

/-- A complete block of the periodic delimiter layout is at a multiple of the span from the first
delimiter.  Consumer: `writerOrderedCloseOf`. -/
theorem blockIndex {c : Compiled} (root : Fin n) (S : Fin n → ProjD c) (first : Nat)
    (hb : ∀ k, 0 < k → k < n →
      ((S (digitSite ring root k)).word.beta = true ↔ first ≤ k ∧ (k - first) % digitSpan c = 0))
    (block : Nat) (hblock : DigitCompleteBlock ring root S block) :
    ∃ j, block = first + j * digitSpan c ∧ first + j * digitSpan c + digitSpan c < n := by
  obtain ⟨⟨⟨hs0, hsn, hsb⟩, -, -, -, -⟩, hlt⟩ := hblock
  obtain ⟨hfs, hmod⟩ := (hb block hs0 hsn).1 hsb
  have hsrc : block = first + (block - first) / digitSpan c * digitSpan c := by
    have := Nat.div_add_mod (block - first) (digitSpan c)
    rw [hmod, Nat.add_zero, Nat.mul_comm] at this
    omega
  generalize (block - first) / digitSpan c = j at hsrc
  subst hsrc
  exact ⟨j, rfl, hlt⟩

/-- The first segment of the periodic delimiter layout: the next delimiter one span on, or the
root.  Consumer: `writerOrderedCloseOf`. -/
theorem firstSegmentOfDelims {c : Compiled} (root : Fin n) (S : Fin n → ProjD c) (first : Nat)
    (hb : ∀ k, 0 < k → k < n →
      ((S (digitSite ring root k)).word.beta = true ↔ first ≤ k ∧ (k - first) % digitSpan c = 0))
    (h0 : 0 < first) (hfn : first < n) (hR : 1 ≤ digitSpan c) :
    ∃ stop, DigitFirstSegment ring root S first stop := by
  have hfd := firstDelimOf ring root S first hb h0 hfn
  by_cases h : first + digitSpan c < n
  · exact ⟨first + digitSpan c, hfd,
      (completeBlockOfDelims ring root S first hb 0 (Nat.zero_mod _) h0 h hR).1⟩
  · refine ⟨n, hfd, hfd.1, hfn, Nat.le_refl _, fun hlt => absurd hlt (Nat.lt_irrefl _),
      fun k hk1 hk2 => ?_⟩
    cases hbeta : (S (digitSite ring root k)).word.beta with
    | false => rfl
    | true =>
      exfalso
      have hm := ((hb k (by omega) hk2).1 hbeta).2
      rw [Nat.mod_eq_of_lt (by omega)] at hm
      omega

/-- **The value chain along the blocks**: from one ordered step per block, the chain reaches every
block `i` (`0` or complete) with its stable cut no later than `aft i` and every earlier block
listed.  Consumer: `writerOrderedCloseOf`. -/
theorem valueChainOf {c : Compiled} (root : Fin n) (A : DigitAudit c n)
    (structural first baseCut R : Nat) (aft : Nat → Nat) (hbase : baseCut ≤ aft 0)
    (hstep : ∀ i prev, first + i * R + 2 * R < n → prev ≤ aft i →
      ∃ terminal : DigitTerminal c n,
        DigitCompletePair ring root A.start (first + i * R) (first + i * R + R) ∧
        DigitFiveCohortCompletions ring A root (first + i * R) (first + i * R + R)
          DigitLane.writer (max structural prev) terminal ∧
        terminal.time ≤ aft (i + 1)) :
    ∀ i, (i = 0 ∨ first + i * R + R < n) →
      ∃ (prev : Nat) (cuts : List (Nat × Nat)),
        DigitValueChain ring root A structural first baseCut (first + i * R) prev cuts ∧
        prev ≤ aft i ∧ ∀ j, j ≤ i → ∃ stable, (first + j * R, stable) ∈ cuts := by
  intro i
  induction i with
  | zero =>
    intro _
    refine ⟨baseCut, [(first, baseCut)], ?_, hbase, fun j hj => ?_⟩
    · rw [Nat.zero_mul, Nat.add_zero]
      exact DigitValueChain.start
    · have e : j = 0 := by omega
      subst e
      rw [Nat.zero_mul, Nat.add_zero]
      exact ⟨baseCut, List.mem_singleton.mpr rfl⟩
  | succ i ih =>
    intro hi
    have e : first + (i + 1) * R = first + i * R + R := by
      rw [Nat.add_mul, Nat.one_mul, Nat.add_assoc]
    have hend : first + i * R + 2 * R < n := by
      rcases hi with h | h
      · omega
      · rw [e] at h
        omega
    obtain ⟨prev, cuts, hch, hprev, hcov⟩ := ih (Or.inr (by omega))
    obtain ⟨terminal, hp, hc, hle⟩ := hstep i prev hend hprev
    refine ⟨terminal.time, (first + i * R + R, terminal.time) :: cuts, ?_, hle, fun j hj => ?_⟩
    · rw [e]
      exact DigitValueChain.next hch _ terminal hp hc
    · rcases Nat.lt_or_ge j (i + 1) with h | h
      · obtain ⟨stable, hs⟩ := hcov j (by omega)
        exact ⟨stable, List.mem_cons_of_mem _ hs⟩
      · have ej : j = i + 1 := by omega
        subst ej
        rw [e]
        exact ⟨terminal.time, List.mem_cons_self⟩

/-- The leading width fits the ring on both bands.  Consumer: `writerOrderedCloseOf`. -/
theorem leadWidthBand (hn : 5 ≤ n) :
    (compileAdvice (ceilLogTwo n)).t + digitSpan (compileAdvice (ceilLogTwo n)) ≤ n := by
  cases hh : (compileAdvice (ceilLogTwo n)).useSmall with
  | true => exact (widthBoundaryWidthSmall hn hh).1
  | false => exact bankRepairDigitLeadWidth hn hh

/-- **`hord` on every boundary reference**: a first-zero continuation of a clean start
whose audit carries the ordered receipt data of all blocks is in the writer values-stable cut.
Every interior block's five window completions are five consecutive next completions with
consecutive ranks by `fiveCohortOfWindow`.  Consumer: `bandWriterOrderedClose`. -/
theorem writerOrderedCloseOf (ref : WidthBoundaryReference ring) (hn : 5 ≤ n)
    :
    WidthWriterOrderedReceiptsClose ref.toWidthDigitReference := by
  intro root z audit aft hrun hord hlead
  obtain ⟨start, word0, word, y, retired0, hst, hfold0, hW, -, -, -, hfold⟩ := hrun
  obtain ⟨root0, hs, hL⟩ := widthCleanBoundaryRoot ref start hst
  obtain ⟨first, ht, hfl, hb⟩ := widthCleanBoundaryDelimiters ref hn root0 start hL
  have hy1 : y.1 = word0.foldl ref.next start := by
    have := widthBoundaryDigitBoundaryAuditFirst ref start
      (digitAuditInitial (piD (ref.phys start))) word0
    rw [hfold0] at this
    exact this
  have hW0 : WFixedRoot ring root0 (piW (ref.phys y.1)) := by
    rw [hy1]
    exact widthBoundaryDigitBoundaryWFixedRootOfSingleton ref root0 start hs word0
  have hr0 : root = root0 := hW0.2.1 root hW.1
  subst hr0
  have hstart : audit.start = piD (ref.phys start) := by
    have h1 := L3.WriterReceipts.widthAuditStartFold ref.toWidthDigitReference word y
    have h0 := L3.WriterReceipts.widthAuditStartFold ref.toWidthDigitReference word0
      (start, digitAuditInitial (piD (ref.phys start)))
    rw [hfold] at h1
    rw [hfold0] at h0
    rw [h1, h0]
    rfl
  have hU : (word0 ++ word).foldl (widthDigitAuditNext ref.toWidthDigitReference)
      (start, digitAuditInitial (piD (ref.phys start))) = (z, audit) := by
    rw [List.foldl_append, hfold0, hfold]
  have hz : z = (word0 ++ word).foldl ref.next start := by
    have := widthBoundaryDigitBoundaryAuditFirst ref start
      (digitAuditInitial (piD (ref.phys start))) (word0 ++ word)
    rw [hU] at this
    exact this
  have hWz : WFixedRoot ring root (piW (ref.phys z)) := by
    rw [hz]
    exact widthBoundaryDigitBoundaryWFixedRootOfSingleton ref root start hs _
  have hDig : DigitAt ring audit audit.clock (piD (ref.phys z)) audit.current := by
    have hinv := widthBoundaryDigitBoundaryAuditInvariantRun ref hn root start hs (word0 ++ word)
    rw [hU] at hinv
    exact hinv.2.1
  have hA : (wRunAt ref.toWidthDigitReference
      (start, digitAuditInitial (piD (ref.phys start))) (word0 ++ word)
      (word0 ++ word).length).2 = audit := by
    rw [wRunAtLen ref.toWidthDigitReference _ _ _ (Nat.le_refl _), hU]
  obtain ⟨hstrict, ⟨retired, hcov, hBdy⟩, hstage, hj⟩ := hord
  have hR : 2 ≤ digitSpan (compileAdvice (ceilLogTwo n)) := valueSpanTwo hn
  have ht2 : 2 ≤ (compileAdvice (ceilLogTwo n)).t :=
    compileAdvice_t_ge_two (ceilLogTwo n) (ringQ_facts n hn).1
  have hw := leadWidthBand (n := n) hn
  have hfn : first < n := by omega
  have hbA : ∀ k, 0 < k → k < n →
      ((audit.start (digitSite ring root k)).word.beta = true ↔
        first ≤ k ∧ (k - first) % digitSpan (compileAdvice (ceilLogTwo n)) = 0) := by
    rw [hstart]
    exact hb
  have hfd : DigitFirstDelimiter ring root audit.start first :=
    firstDelimOf ring root audit.start first hbA (by omega) hfn
  obtain ⟨stop, hseg⟩ := firstSegmentOfDelims root audit.start first hbA (by omega) hfn (by omega)
  -- the base value cut
  obtain ⟨baseCut, hbc, hbmin⟩ := existsFirst
    (fun k => DigitTwoBaseCovers ring root audit 0 retired k) ⟨aft 0, hcov⟩
  have hbaseLe : baseCut ≤ aft 0 := by
    rcases Nat.lt_or_ge (aft 0) baseCut with h | h
    · exact absurd hcov (hbmin _ h)
    · exact h
  -- the times increase
  have hmono : ∀ i, i ≤ valueBlocks n → aft 0 ≤ aft i := by
    intro i
    induction i with
    | zero => intro _; exact Nat.le_refl _
    | succ i ih =>
      intro hi
      have := ih (by omega)
      have := (hstage i (by omega)).1
      omega
  have hclock : aft 0 ≤ audit.clock := by
    have := hmono _ (Nat.le_refl _)
    omega
  -- the writer structural cut
  have hSA : DigitWriterStructuralAt ring root audit (aft 0) := by
    refine ⟨hclock, fun source target hpair => ?_⟩
    obtain ⟨i, hsrc, -⟩ := blockIndex root audit.start first hbA source hpair.1
    have htg := hpair.2.1
    have hend2 := hpair.2.2.2
    subst hsrc
    subst htg
    have hle : (i + 1) * digitSpan (compileAdvice (ceilLogTwo n)) ≤ n := by
      rw [Nat.add_mul]
      omega
    have hi : i < valueBlocks n := by
      show i < n / digitSpan (compileAdvice (ceilLogTwo n))
      exact Nat.lt_of_succ_le ((Nat.le_div_iff_mul_le (by omega)).2 hle)
    obtain ⟨tm, htm, hle2⟩ := hstrict i hi first hfd (by omega) (by
      show first + i * digitSpan (compileAdvice (ceilLogTwo n)) +
        2 * digitSpan (compileAdvice (ceilLogTwo n)) < n
      omega)
    obtain ⟨t1, ht1⟩ := firstStrictOfCompletion ring audit root _ _ DigitLane.writer 0 ⟨tm, htm⟩
    exact ⟨t1, ht1, Nat.le_trans (ht1.2 tm htm) hle2⟩
  obtain ⟨structural, hstr, hsmin⟩ := existsFirst (DigitWriterStructuralAt ring root audit)
    ⟨_, hSA⟩
  have hstrLe : structural ≤ aft 0 := by
    rcases Nat.lt_or_ge (aft 0) structural with h | h
    · exact absurd hSA (hsmin _ h)
    · exact h
  -- one ordered step per block
  have hstep : ∀ i prev,
      first + i * digitSpan (compileAdvice (ceilLogTwo n)) +
        2 * digitSpan (compileAdvice (ceilLogTwo n)) < n → prev ≤ aft i →
      ∃ terminal : DigitTerminal (compileAdvice (ceilLogTwo n)) n,
        DigitCompletePair ring root audit.start
          (first + i * digitSpan (compileAdvice (ceilLogTwo n)))
          (first + i * digitSpan (compileAdvice (ceilLogTwo n)) +
            digitSpan (compileAdvice (ceilLogTwo n))) ∧
        DigitFiveCohortCompletions ring audit root
          (first + i * digitSpan (compileAdvice (ceilLogTwo n)))
          (first + i * digitSpan (compileAdvice (ceilLogTwo n)) +
            digitSpan (compileAdvice (ceilLogTwo n)))
          DigitLane.writer (max structural prev) terminal ∧
        terminal.time ≤ aft (i + 1) := by
    intro i prev hend hprev
    have hle : (i + 1) * digitSpan (compileAdvice (ceilLogTwo n)) ≤ n := by
      rw [Nat.add_mul]
      omega
    have hi : i < valueBlocks n := by
      show i < n / digitSpan (compileAdvice (ceilLogTwo n))
      exact Nat.lt_of_succ_le ((Nat.le_div_iff_mul_le (by omega)).2 hle)
    have hpairA : DigitCompletePair ring root audit.start
        (first + i * digitSpan (compileAdvice (ceilLogTwo n)))
        (first + i * digitSpan (compileAdvice (ceilLogTwo n)) +
          digitSpan (compileAdvice (ceilLogTwo n))) :=
      pairInOfDelims ring root audit.start first hbA _ (Nat.mul_mod_left i _) (by omega) hend
        (by omega)
    have hpairS : DigitCompletePair ring root (piD (ref.phys start))
        (first + i * digitSpan (compileAdvice (ceilLogTwo n)))
        (first + i * digitSpan (compileAdvice (ceilLogTwo n)) +
          digitSpan (compileAdvice (ceilLogTwo n))) := by
      rw [← hstart]
      exact hpairA
    obtain ⟨hs2, hend2, hlay⟩ := pairLayoutStart ref hn root start hL _ hpairS
    obtain ⟨anchor, hanc, hat⟩ := hstr.2 _ _ hpairA
    have hwin : FwdChainBy ring audit root
        (first + i * digitSpan (compileAdvice (ceilLogTwo n)))
        (first + i * digitSpan (compileAdvice (ceilLogTwo n)) +
          digitSpan (compileAdvice (ceilLogTwo n)))
        DigitLane.writer 5 (aft i) (aft (i + 1)) :=
      (hstage i hi).2 first hfd hs2 hend
    have hafter : max structural prev ≤ aft i := by
      have := hmono i (by omega)
      exact Nat.max_le.2 ⟨by omega, hprev⟩
    have hq0 : WidthRunInv ring ref root DigitLane.writer
        (first + i * digitSpan (compileAdvice (ceilLogTwo n)))
        (digitSpan (compileAdvice (ceilLogTwo n)))
        (start, digitAuditInitial (piD (ref.phys start))) :=
      ⟨widthPairInvInitial ring ref hn root DigitLane.writer _ _ start hlay, hpairS⟩
    rw [← hA] at hanc hwin
    obtain ⟨last, hfive, hlast⟩ := fiveCohortOfWindow ref hn root _ hR hs2 hend2 _ hq0 rfl rfl
      (word0 ++ word) _ _ _ hafter anchor hanc (Nat.le_trans hat (Nat.le_max_left _ _)) hwin
    rw [hA] at hfive
    exact ⟨last, hpairA, hfive, hlast⟩
  -- the last block
  obtain ⟨m, -, hm0, hmax⟩ := lastIndex
    (fun j => first + j * digitSpan (compileAdvice (ceilLogTwo n)) +
      digitSpan (compileAdvice (ceilLogTwo n)) < n) n
  obtain ⟨restart, cuts, hchain, -, hcover⟩ := valueChainOf root audit structural first baseCut
    (digitSpan (compileAdvice (ceilLogTwo n))) aft hbaseLe hstep m hm0
  refine ⟨start, word0 ++ word, root, audit, retired, restart, hst, hU, hWz, hDig,
    ⟨first, stop, baseCut, structural, _, cuts, hseg, ⟨hbc, hbmin⟩, hBdy, ⟨hstr, hsmin⟩, hchain,
      fun block hblock => ?_⟩, hlead⟩
  obtain ⟨j, hbj, hjn⟩ := blockIndex root audit.start first hbA block hblock
  have hjle : j ≤ j * digitSpan (compileAdvice (ceilLogTwo n)) :=
    Nat.le_mul_of_pos_right j (by omega)
  subst hbj
  exact hcover j (hmax j (by omega) hjn)

/-- **The headline premise `hord`**: `WidthWriterOrderedReceiptsClose` at the band reference
(SMALL and BANK through their boundary references, `writerOrderedCloseOf`).  Consumer: `hord` of
`l3HeadlineOfCleanBranches` (Leader/L3/Headline/CleanAssembly.lean). -/
theorem bandWriterOrderedClose (ring : DirectedRing n) (hn : 5 ≤ n)
    :
    WidthWriterOrderedReceiptsClose (bandWidthDigitReference ring hn) := by
  by_cases hs : (compileAdvice (ceilLogTwo n)).useSmall = true
  · rw [bandWidthDigitReferenceSmall ring hn hs]
    exact writerOrderedCloseOf (smallWidthBoundaryReference ring hn hs) hn
  · have hb : (compileAdvice (ceilLogTwo n)).useSmall = false := by
      cases hh : (compileAdvice (ceilLogTwo n)).useSmall
      · rfl
      · exact absurd hh hs
    rw [bandWidthDigitReferenceBank ring hn hb]
    exact writerOrderedCloseOf (bankWidthBoundaryReference ring hn hb) hn

end Top

end L3.WriterOrderedClose

#print axioms L3.WriterOrderedClose.tailRankUnique
#print axioms L3.WriterOrderedClose.anchorMemberBorder
#print axioms L3.WriterOrderedClose.completionRankPos
#print axioms L3.WriterOrderedClose.nextCompletionLe
#print axioms L3.WriterOrderedClose.fiveCohortOfWindow
#print axioms L3.WriterOrderedClose.lastIndex
#print axioms L3.WriterOrderedClose.blockIndex
#print axioms L3.WriterOrderedClose.firstSegmentOfDelims
#print axioms L3.WriterOrderedClose.valueChainOf
#print axioms L3.WriterOrderedClose.leadWidthBand
#print axioms L3.WriterOrderedClose.writerOrderedCloseOf
#print axioms L3.WriterOrderedClose.bandWriterOrderedClose
