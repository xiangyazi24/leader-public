import Leader.L3.Width.DigitCompareRestart
import Leader.L3.Width.DigitWriterReceipts

/-!
# Clause (P) of the comparison close: the cut facts persist under audit extension

`L3.CompareStage.WidthComparisonClose` asks for `WidthWriterComparisonCut` at a continuation
`y = w.foldl next x` of a values-stable state `x`.  Besides the comparison-ready cut itself, that
cut repeats the facts of `x`: the run from a clean start, the W fixed root, the audit at the
current state and the writer value receipts `WidthWriterValueReceipts … retired restart`.

This module proves that these facts survive every audit letter (any compiled `c` for the audit
facts; the receipts at the band compile), and that the comparison-ready predicate survives too:

* `completionBack`: a completion of the stepped audit whose terminal is no later than the old
  clock is a completion of the old audit (the new frame is stamped `clock + 1`);
* forward and backward transport of first strict completions, next completions, anchors, tail
  ranks, cohort ranks, base lineages, base covers and the writer structural cut;
* `receiptsStep`, `receiptsFold`: `WidthWriterValueReceipts` persists;
* `readyStep`, `readyFold`: `DigitComparisonReady … restart cut` persists;
* `comparisonCutOfReady` (any `WidthBoundaryReference`): on a continuation of a values-stable
  state, a comparison-ready cut of the continuation's audit gives `WidthWriterComparisonCut` at the
  continuation (first such cut by `existsFirst`; the boundary leader receipt by
  `L3.CloseKeep.leaderWord`).

So `WidthComparisonClose` reduces to producing one `DigitComparisonReady` cut on the continuation.
-/

namespace L3.ClosePersist

set_option autoImplicit false

open L3
open L3.WidthDigit
open L3.WriterValueCuts
open L3.CompareStage
open L3.DigitCohortScratch

section Audit

variable {c : Compiled} {n : Nat} (ring : DirectedRing n) (S : Fin n → ProjD c)
  (A : DigitAudit c n) (e : Fin n)

/-- Old frames survive one letter.  Consumer: the forward transports below. -/
theorem frameFwd (f : DigitFrame c n) (hf : f ∈ A.frames) :
    f ∈ (digitAuditStep ring S A e).frames :=
  List.mem_cons.mpr (Or.inr hf)

/-- A frame of the stepped audit stamped no later than the old clock is old.  Consumer: the
backward transports below. -/
theorem frameBack (f : DigitFrame c n) (hf : f ∈ (digitAuditStep ring S A e).frames)
    (ht : f.time ≤ A.clock) : f ∈ A.frames := by
  rcases List.mem_cons.mp hf with h | h
  · subst h
    exact absurd ht (Nat.not_succ_le_self A.clock)
  · exact h

/-- Consumer: `completionBack`, `anchorStep`, `tailRankStep`, `currentPacketStep`. -/
theorem sampleFwd (s : DigitSample c n) (h : DigitRecordedSample A s) :
    DigitRecordedSample (digitAuditStep ring S A e) s := by
  obtain ⟨f, hf, h1, h2, h3, h4⟩ := h
  exact ⟨f, frameFwd ring S A e f hf, h1, h2, h3, h4⟩

/-- Consumer: `completionBack`. -/
theorem sampleBack (s : DigitSample c n) (h : DigitRecordedSample (digitAuditStep ring S A e) s)
    (ht : s.id.time ≤ A.clock) : DigitRecordedSample A s := by
  obtain ⟨f, hf, h1, h2, h3, h4⟩ := h
  exact ⟨f, frameBack ring S A e f hf (by rw [h1]; exact ht), h1, h2, h3, h4⟩

/-- Consumer: `completionBack`. -/
theorem exportFwd (x : DigitExport c n) (h : DigitRecordedExport A x) :
    DigitRecordedExport (digitAuditStep ring S A e) x := by
  obtain ⟨f, hf, h1, h2, h3⟩ := h
  exact ⟨f, frameFwd ring S A e f hf, h1, h2, h3⟩

/-- Consumer: `completionBack`. -/
theorem exportBack (x : DigitExport c n) (h : DigitRecordedExport (digitAuditStep ring S A e) x)
    (ht : x.time ≤ A.clock) : DigitRecordedExport A x := by
  obtain ⟨f, hf, h1, h2, h3⟩ := h
  exact ⟨f, frameBack ring S A e f hf (by rw [h1]; exact ht), h1, h2, h3⟩

/-- Consumer: `completionBack`. -/
theorem terminalBack (t : DigitTerminal c n)
    (h : DigitRecordedTerminal (digitAuditStep ring S A e) t) (ht : t.time ≤ A.clock) :
    DigitRecordedTerminal A t := by
  obtain ⟨f, hf, h1, h2, h3⟩ := h
  exact ⟨f, frameBack ring S A e f hf (by rw [h1]; exact ht), h1, h2, h3⟩

/-- The terminal of a completion is no later than the clock.  Consumer: `firstStrictStep`,
`nextCompletionStep`. -/
theorem completionTimeLe {root : Fin n} {source target : Nat} {lane : DigitLane} {cut : Nat}
    {t : DigitTerminal c n} (h : DigitCompletion ring A root source target lane cut t) :
    t.time ≤ A.clock :=
  h.2.2.2.2.2.1

/-- **A completion of the stepped audit with terminal no later than the old clock is a
completion of the old audit.**  Consumer: `firstStrictStep`, `firstStrictBack`,
`nextCompletionStep`. -/
theorem completionBack (root : Fin n) (source target : Nat) (lane : DigitLane) (cut : Nat)
    (terminal : DigitTerminal c n)
    (h : DigitCompletion ring (digitAuditStep ring S A e) root source target lane cut terminal)
    (ht : terminal.time ≤ A.clock) :
    DigitCompletion ring A root source target lane cut terminal := by
  obtain ⟨hp, htm, hl, hs, hd, -, pos, ledger, samples, exports, uses, h1, h2, h3, hj, hij,
    hother⟩ := h
  refine ⟨hp, terminalBack ring S A e terminal htm ht, hl, hs, hd, ht, pos, ledger, samples,
    exports, uses, h1, h2, h3, ?_, hij, ?_⟩
  · intro j
    obtain ⟨s1, s2, s3, s4, s5, x1, x2, x3, x4, x5, x6, x7, u1, u2, u3, u4, u5, t1, t2, t3⟩ :=
      hj j
    exact ⟨sampleBack ring S A e _ s1 (by omega), s2, s3, s4, s5,
      exportBack ring S A e _ x1 (by omega), x2, x3, x4, x5, x6, x7, u1, u2, u3, u4, u5, t1, t2,
      t3⟩
  · intro other ho o1 o2 o3 o4 o5
    exact hother other (exportFwd ring S A e other ho) o1 o2 o3 o4 o5

/-- Consumer: `anchorStep`, `readyStep`. -/
theorem firstStrictStep (root : Fin n) (source target : Nat) (lane : DigitLane) (cut : Nat)
    (tm : DigitTerminal c n)
    (h : DigitFirstStrictCompletion ring A root source target lane cut tm) :
    DigitFirstStrictCompletion ring (digitAuditStep ring S A e) root source target lane cut tm := by
  refine ⟨L3.FiveTransfer.completionStep ring S A e root source target lane cut tm h.1,
    fun other ho => ?_⟩
  have htm := completionTimeLe ring A h.1
  rcases Nat.lt_or_ge A.clock other.time with hlt | hge
  · omega
  · exact h.2 other (completionBack ring S A e root source target lane cut other ho hge)

/-- Consumer: `writerStructuralBack`. -/
theorem firstStrictBack (root : Fin n) (source target : Nat) (lane : DigitLane) (cut : Nat)
    (tm : DigitTerminal c n)
    (h : DigitFirstStrictCompletion ring (digitAuditStep ring S A e) root source target lane cut
      tm)
    (ht : tm.time ≤ A.clock) :
    DigitFirstStrictCompletion ring A root source target lane cut tm :=
  ⟨completionBack ring S A e root source target lane cut tm h.1 ht, fun other ho =>
    h.2 other (L3.FiveTransfer.completionStep ring S A e root source target lane cut other ho)⟩

/-- Consumer: `fiveCohortStep`. -/
theorem nextCompletionStep (root : Fin n) (source target : Nat) (lane : DigitLane) (after : Nat)
    (tm : DigitTerminal c n)
    (h : DigitNextCompletion ring A root source target lane after tm) :
    DigitNextCompletion ring (digitAuditStep ring S A e) root source target lane after tm := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨L3.FiveTransfer.completionStep ring S A e root source target lane 0 tm h1, h2,
    fun other ho hlt => ?_⟩
  have htm := completionTimeLe ring A h1
  rcases Nat.lt_or_ge A.clock other.time with hlt' | hge
  · omega
  · exact h3 other (completionBack ring S A e root source target lane 0 other ho hge) hlt

/-- Consumer: `sampleCohortStep`, `unreadCohortStep`. -/
theorem tailRankStep {lane : DigitLane} {source : Fin n} {anchorTail id : DigitStamp n}
    {rank : Nat} (h : DigitTailRank A lane source anchorTail id rank) :
    DigitTailRank (digitAuditStep ring S A e) lane source anchorTail id rank := by
  induction h with
  | anchor => exact DigitTailRank.anchor
  | successor _ sample rearm recorded sampleLane sampleSource sampleTail cause rearmLane
      rearmSource previousBefore rearmBefore ih =>
    exact DigitTailRank.successor ih sample rearm (sampleFwd ring S A e sample recorded)
      sampleLane sampleSource sampleTail cause rearmLane rearmSource previousBefore rearmBefore

/-- Consumer: `fiveCohortStep`, `readyStep`. -/
theorem anchorStep (root : Fin n) (source target : Nat) (lane : DigitLane)
    (anchor : DigitTerminal c n) (anchorTail : DigitStamp n)
    (h : DigitAnchor ring A root source target lane anchor anchorTail) :
    DigitAnchor ring (digitAuditStep ring S A e) root source target lane anchor anchorTail := by
  obtain ⟨h1, ledger, firstUse, sample, a1, a2, a3, a4, a5, a6, a7, a8⟩ := h
  exact ⟨firstStrictStep ring S A e root source target lane 0 anchor h1, ledger, firstUse,
    sample, a1, a2, a3, sampleFwd ring S A e sample a4, a5, a6, a7, a8⟩

/-- Consumer: `atomCohortStep`. -/
theorem sampleCohortStep {lane : DigitLane} {source : Fin n} {anchor : DigitTerminal c n}
    {anchorTail : DigitStamp n} {sample : DigitSample c n} {rank : Nat}
    (h : DigitSampleCohort A lane source anchor anchorTail sample rank) :
    DigitSampleCohort (digitAuditStep ring S A e) lane source anchor anchorTail sample rank := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨sampleFwd ring S A e sample h1, h2, ?_⟩
  rcases h3 with h | ⟨previous, previousRank, rearm, r1, r2, r3, r4, r5, r6, r7⟩
  · exact Or.inl h
  · exact Or.inr ⟨previous, previousRank, rearm, r1, tailRankStep ring S A e r2, r3, r4, r5, r6,
      r7⟩

/-- Consumer: `terminalRankStep`, `terminalRankedStep`. -/
theorem atomCohortStep {lane : DigitLane} {source : Fin n} {anchor : DigitTerminal c n}
    {anchorTail : DigitStamp n} {origin : Option (DigitAtom n)} {rank : Nat}
    (h : DigitAtomCohort A lane source anchor anchorTail origin rank) :
    DigitAtomCohort (digitAuditStep ring S A e) lane source anchor anchorTail origin rank := by
  obtain ⟨sample, h1, h2⟩ := h
  exact ⟨sample, h1, sampleCohortStep ring S A e h2⟩

/-- Consumer: `serialRanksStep`. -/
theorem terminalRankStep {lane : DigitLane} {source : Fin n} {anchor : DigitTerminal c n}
    {anchorTail : DigitStamp n} {terminal : DigitTerminal c n} {rank : Nat}
    (h : DigitTerminalRank A lane source anchor anchorTail terminal rank) :
    DigitTerminalRank (digitAuditStep ring S A e) lane source anchor anchorTail terminal rank := by
  obtain ⟨h1, ledger, h2, h3, h4, h5⟩ := h
  exact ⟨h1, ledger, h2, h3, h4, fun use hu => atomCohortStep ring S A e (h5 use hu)⟩

/-- Consumer: `readyStep`. -/
theorem terminalRankedStep {lane : DigitLane} {source : Fin n} {anchor : DigitTerminal c n}
    {anchorTail : DigitStamp n} {terminal : DigitTerminal c n}
    (h : DigitTerminalRanked A lane source anchor anchorTail terminal) :
    DigitTerminalRanked (digitAuditStep ring S A e) lane source anchor anchorTail terminal := by
  obtain ⟨ledger, rank, h1, h2, h3, h4⟩ := h
  exact ⟨ledger, rank, h1, h2, h3, fun use hu => atomCohortStep ring S A e (h4 use hu)⟩

/-- Consumer: `fiveCohortStep`. -/
theorem serialRanksStep {lane : DigitLane} {source : Fin n} {anchor : DigitTerminal c n}
    {anchorTail : DigitStamp n} {rank : Nat} {ts : List (DigitTerminal c n)}
    (h : DigitSerialTerminalRanks A lane source anchor anchorTail rank ts) :
    DigitSerialTerminalRanks (digitAuditStep ring S A e) lane source anchor anchorTail rank ts := by
  induction h with
  | empty rank => exact DigitSerialTerminalRanks.empty rank
  | next rank terminal rest head _ ih =>
    exact DigitSerialTerminalRanks.next rank terminal rest (terminalRankStep ring S A e head) ih

/-- Consumer: `valueChainStep`. -/
theorem fiveCohortStep (root : Fin n) (source target : Nat) (lane : DigitLane) (after : Nat)
    (last : DigitTerminal c n)
    (h : DigitFiveCohortCompletions ring A root source target lane after last) :
    DigitFiveCohortCompletions ring (digitAuditStep ring S A e) root source target lane after
      last := by
  obtain ⟨t1, t2, t3, t4, anchor, anchorTail, firstRank, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  exact ⟨t1, t2, t3, t4, anchor, anchorTail, firstRank,
    nextCompletionStep ring S A e root source target lane _ _ h1,
    nextCompletionStep ring S A e root source target lane _ _ h2,
    nextCompletionStep ring S A e root source target lane _ _ h3,
    nextCompletionStep ring S A e root source target lane _ _ h4,
    nextCompletionStep ring S A e root source target lane _ _ h5,
    anchorStep ring S A e root source target lane anchor anchorTail h6, h7, h8,
    serialRanksStep ring S A e h9⟩

/-- Consumer: `receiptsStep`. -/
theorem valueChainStep (root : Fin n) (structural first baseCut : Nat) {source restart : Nat}
    {cuts : List (Nat × Nat)}
    (h : DigitValueChain ring root A structural first baseCut source restart cuts) :
    DigitValueChain ring root (digitAuditStep ring S A e) structural first baseCut source restart
      cuts := by
  induction h with
  | start => exact DigitValueChain.start
  | next _ target terminal hp hc ih =>
    exact DigitValueChain.next ih target terminal hp
      (fiveCohortStep ring S A e root _ target .writer _ terminal hc)

/-! ### Base covers -/

/-- Consumer: `digitAtStep`-based transports, `extinctStep`, `readyStep`. -/
theorem digitAtStep {cut : Nat} {T : Fin n → ProjD c} {G : Fin n → DigitGhost c n}
    (h : DigitAt ring A cut T G) : DigitAt ring (digitAuditStep ring S A e) cut T G := by
  rcases h with h | ⟨f, hf, h1, h2, h3⟩
  · exact Or.inl h
  · exact Or.inr ⟨f, frameFwd ring S A e f hf, h1, h2, h3⟩

/-- Consumer: `extinctBack`. -/
theorem digitAtBack {cut : Nat} {T : Fin n → ProjD c} {G : Fin n → DigitGhost c n}
    (h : DigitAt ring (digitAuditStep ring S A e) cut T G) (ht : cut ≤ A.clock) :
    DigitAt ring A cut T G := by
  rcases h with h | ⟨f, hf, h1, h2, h3⟩
  · exact Or.inl h
  · exact Or.inr ⟨f, frameBack ring S A e f hf (by rw [h1]; exact ht), h1, h2, h3⟩

/-- The boundary receipt at a past time persists.  Consumer: `receiptsStep`,
`L3.WriterOrdered.ordDataStep`. -/
theorem boundaryAtStep (root : Fin n) (cut : Nat) (h : DigitBoundaryAt ring root A cut) :
    DigitBoundaryAt ring root (digitAuditStep ring S A e) cut := by
  obtain ⟨T, G, h2, h3⟩ := h
  exact ⟨T, G, digitAtStep ring S A e h2, h3⟩

/-- Consumer: `coversStep`. -/
theorem extinctStep (root : Fin n) (boundary retired : Nat)
    (h : DigitBaseExtinct ring root A boundary retired) :
    DigitBaseExtinct ring root (digitAuditStep ring S A e) boundary retired := by
  obtain ⟨h1, T, G, h2, h3⟩ := h
  exact ⟨h1, T, G, digitAtStep ring S A e h2, h3⟩

/-- Consumer: `coversBack`. -/
theorem extinctBack (root : Fin n) (boundary retired : Nat)
    (h : DigitBaseExtinct ring root (digitAuditStep ring S A e) boundary retired)
    (ht : retired ≤ A.clock) :
    DigitBaseExtinct ring root A boundary retired := by
  obtain ⟨h1, T, G, h2, h3⟩ := h
  exact ⟨h1, T, G, digitAtBack ring S A e h2 ht, h3⟩

/-- Consumer: `lineageStep`. -/
theorem launchStep (root : Fin n) (time : Nat) (h : DigitActualBaseLaunch ring root A time) :
    DigitActualBaseLaunch ring root (digitAuditStep ring S A e) time := by
  obtain ⟨f, hf, h1, h2, h3⟩ := h
  exact ⟨f, frameFwd ring S A e f hf, h1, h2, h3⟩

/-- Consumer: `lineageBack`. -/
theorem launchBack (root : Fin n) (time : Nat)
    (h : DigitActualBaseLaunch ring root (digitAuditStep ring S A e) time)
    (ht : time ≤ A.clock) : DigitActualBaseLaunch ring root A time := by
  obtain ⟨f, hf, h1, h2, h3⟩ := h
  exact ⟨f, frameBack ring S A e f hf (by rw [h1]; exact ht), h1, h2, h3⟩

/-- Consumer: `coversStep`. -/
theorem lineageStep (root : Fin n) {birth last : Nat} {chain : List (DigitBaseOrigin n)}
    (h : DigitBaseLineage ring root A birth chain last) :
    DigitBaseLineage ring root (digitAuditStep ring S A e) birth chain last := by
  induction h with
  | launch hl => exact DigitBaseLineage.launch _ (launchStep ring S A e root _ hl)
  | transfer _ f merge survivor hf hm hlt hclock hin hout ih =>
    exact DigitBaseLineage.transfer ih f merge survivor (frameFwd ring S A e f hf) hm hlt hclock
      hin hout

/-- Consumer: `coversBack`. -/
theorem lineageBack (root : Fin n) {birth last : Nat} {chain : List (DigitBaseOrigin n)}
    (h : DigitBaseLineage ring root (digitAuditStep ring S A e) birth chain last) :
    last ≤ A.clock → DigitBaseLineage ring root A birth chain last := by
  induction h with
  | launch hl =>
    intro ht
    exact DigitBaseLineage.launch _ (launchBack ring S A e root _ hl ht)
  | transfer _ f merge survivor hf hm hlt hclock hin hout ih =>
    intro ht
    exact DigitBaseLineage.transfer (ih (by omega)) f merge survivor
      (frameBack ring S A e f hf ht) hm hlt hclock hin hout

/-- Consumer: `coversStep`. -/
theorem coverStep (root : Fin n) (boundary retired cut : Nat) (chain : List (DigitBaseOrigin n))
    (site : Fin n) (proposal : DigitZeroProposal n)
    (h : DigitCoverProposal ring root A boundary retired cut chain site proposal) :
    DigitCoverProposal ring root (digitAuditStep ring S A e) boundary retired cut chain site
      proposal := by
  obtain ⟨⟨f, hf, a1, a2, a3⟩, h1, h2, h3, h4⟩ := h
  exact ⟨⟨f, frameFwd ring S A e f hf, a1, a2, a3⟩, h1, h2, h3, h4⟩

/-- Consumer: `coversBack`. -/
theorem coverBack (root : Fin n) (boundary retired cut : Nat) (chain : List (DigitBaseOrigin n))
    (site : Fin n) (proposal : DigitZeroProposal n)
    (h : DigitCoverProposal ring root (digitAuditStep ring S A e) boundary retired cut chain site
      proposal)
    (ht : cut ≤ A.clock) :
    DigitCoverProposal ring root A boundary retired cut chain site proposal := by
  obtain ⟨⟨f, hf, a1, a2, a3⟩, h1, h2, h3, h4⟩ := h
  exact ⟨⟨f, frameBack ring S A e f hf (by rw [← a2]; omega), a1, a2, a3⟩, h1, h2, h3, h4⟩

/-- Consumer: `baseValueCutStep`. -/
theorem coversStep (root : Fin n) (boundary retired cut : Nat)
    (h : DigitTwoBaseCovers ring root A boundary retired cut) :
    DigitTwoBaseCovers ring root (digitAuditStep ring S A e) boundary retired cut := by
  obtain ⟨hx, hrc, hcc, hcov⟩ := h
  refine ⟨extinctStep ring S A e root boundary retired hx, hrc,
    by show cut ≤ A.clock + 1; omega, ?_⟩
  rcases hcov with hno | ⟨fb, sb, fl, sl, fc, sc, h1, h2, h3, h4, h5, h6, h7⟩
  · exact Or.inl hno
  · refine Or.inr ⟨fb, sb, fl, sl, fc, sc, h1, h2, lineageStep ring S A e root h3,
      lineageStep ring S A e root h4, h5, h6, fun i hi => ?_⟩
    obtain ⟨p, q, hp, hq, hpq⟩ := h7 i hi
    exact ⟨p, q, coverStep ring S A e root _ _ _ _ _ _ hp, coverStep ring S A e root _ _ _ _ _ _ hq,
      hpq⟩

/-- Consumer: `baseValueCutStep`. -/
theorem coversBack (root : Fin n) (boundary retired cut : Nat)
    (h : DigitTwoBaseCovers ring root (digitAuditStep ring S A e) boundary retired cut)
    (ht : cut ≤ A.clock) :
    DigitTwoBaseCovers ring root A boundary retired cut := by
  obtain ⟨hx, hrc, -, hcov⟩ := h
  refine ⟨extinctBack ring S A e root boundary retired hx (by omega), hrc, ht, ?_⟩
  rcases hcov with hno | ⟨fb, sb, fl, sl, fc, sc, h1, h2, h3, h4, h5, h6, h7⟩
  · exact Or.inl hno
  · refine Or.inr ⟨fb, sb, fl, sl, fc, sc, h1, h2, lineageBack ring S A e root h3 (by omega),
      lineageBack ring S A e root h4 (by omega), h5, h6, fun i hi => ?_⟩
    obtain ⟨p, q, hp, hq, hpq⟩ := h7 i hi
    exact ⟨p, q, coverBack ring S A e root _ _ _ _ _ _ hp ht,
      coverBack ring S A e root _ _ _ _ _ _ hq ht, hpq⟩

/-- **The base value cut persists.**  Consumer: `receiptsStep`. -/
theorem baseValueCutStep (root : Fin n) (boundary retired baseCut : Nat)
    (h : DigitBaseValueCut ring root A boundary retired baseCut) :
    DigitBaseValueCut ring root (digitAuditStep ring S A e) boundary retired baseCut := by
  obtain ⟨h1, h2⟩ := h
  have hle : baseCut ≤ A.clock := h1.2.2.1
  exact ⟨coversStep ring S A e root boundary retired baseCut h1, fun k hk hc =>
    h2 k hk (coversBack ring S A e root boundary retired k hc (by omega))⟩

/-! ### The writer structural cut -/

/-- Consumer: `structuralCutStep`. -/
theorem writerStructuralStep (root : Fin n) (cut : Nat)
    (h : L3.WriterValueCuts.DigitWriterStructuralAt ring root A cut) :
    L3.WriterValueCuts.DigitWriterStructuralAt ring root (digitAuditStep ring S A e) cut := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨by show cut ≤ A.clock + 1; omega, fun source target hp => ?_⟩
  obtain ⟨t, ht, hle⟩ := h2 source target hp
  exact ⟨t, firstStrictStep ring S A e root source target .writer 0 t ht, hle⟩

/-- Consumer: `structuralCutStep`. -/
theorem writerStructuralBack (root : Fin n) (cut : Nat)
    (h : L3.WriterValueCuts.DigitWriterStructuralAt ring root (digitAuditStep ring S A e) cut)
    (hc : cut ≤ A.clock) :
    L3.WriterValueCuts.DigitWriterStructuralAt ring root A cut := by
  obtain ⟨-, h2⟩ := h
  refine ⟨hc, fun source target hp => ?_⟩
  obtain ⟨t, ht, hle⟩ := h2 source target hp
  exact ⟨t, firstStrictBack ring S A e root source target .writer 0 t ht (by omega), hle⟩

/-- **The first writer structural cut persists.**  Consumer: `receiptsStep`. -/
theorem structuralCutStep (root : Fin n) (structural : Nat)
    (h : DigitFirstCut (L3.WriterValueCuts.DigitWriterStructuralAt ring root A) structural) :
    DigitFirstCut
      (L3.WriterValueCuts.DigitWriterStructuralAt ring root (digitAuditStep ring S A e))
      structural := by
  obtain ⟨h1, h2⟩ := h
  have hle : structural ≤ A.clock := h1.1
  exact ⟨writerStructuralStep ring S A e root structural h1, fun k hk hs =>
    h2 k hk (writerStructuralBack ring S A e root k hs (by omega))⟩

/-! ### Currentness -/

/-- Consumer: `currentOutputStep`, `currentInputStep`, `currentUseStep`. -/
theorem currentPacketStep (root : Fin n) (lane : DigitLane) (source cut now : Nat)
    (origin : Option (DigitAtom n)) (value : Fin c.topA) (tail : Bool)
    (h : DigitCurrentPacket ring root A lane source cut now origin value tail) :
    DigitCurrentPacket ring root (digitAuditStep ring S A e) lane source cut now origin value
      tail := by
  obtain ⟨id, sample, offset, h1, h2, h3, rest⟩ := h
  exact ⟨id, sample, offset, h1, h2, sampleFwd ring S A e sample h3, rest⟩

/-- Consumer: `pairCurrentStep`. -/
theorem currentOutputStep (root : Fin n) (lane : DigitLane) (source cut now : Nat)
    (v : DigitLaneView c) (g : DigitLaneGhost c n)
    (h : DigitCurrentOutput ring root A lane source cut now v g) :
    DigitCurrentOutput ring root (digitAuditStep ring S A e) lane source cut now v g := by
  unfold DigitCurrentOutput at h ⊢
  cases hv : v.out with
  | E => trivial
  | U => rw [hv] at h; exact h
  | D value tail =>
    rw [hv] at h
    exact currentPacketStep ring S A e root lane source cut now _ value tail h

/-- Consumer: `pairCurrentStep`. -/
theorem currentInputStep (root : Fin n) (lane : DigitLane) (source cut now : Nat)
    (v : DigitLaneView c) (g : DigitLaneGhost c n)
    (h : DigitCurrentInput ring root A lane source cut now v g) :
    DigitCurrentInput ring root (digitAuditStep ring S A e) lane source cut now v g := by
  unfold DigitCurrentInput at h ⊢
  cases hv : v.input with
  | E => trivial
  | X => rw [hv] at h; exact h
  | P value tail =>
    rw [hv] at h
    exact currentPacketStep ring S A e root lane source cut now _ value tail h
  | S value tail =>
    rw [hv] at h
    exact currentPacketStep ring S A e root lane source cut now _ value tail h

/-- Consumer: `pairCurrentStep`. -/
theorem currentCarryStep (root : Fin n) (lane : DigitLane) (source cut now : Nat)
    (carry : Option (DigitCarryGhost c n))
    (h : DigitCurrentCarry ring root A lane source cut now carry) :
    DigitCurrentCarry ring root (digitAuditStep ring S A e) lane source cut now carry := by
  obtain ⟨ledger, h1, h2, h3, h4⟩ := h
  refine ⟨ledger, h1, h2, h3, fun use hu => ?_⟩
  obtain ⟨u1, u2, u3⟩ := h4 use hu
  exact ⟨u1, currentPacketStep ring S A e root lane source cut now _ _ _ u2, u3⟩

/-- Consumer: `readyStep`. -/
theorem pairCurrentStep (root : Fin n) (T : Fin n → ProjD c) (G : Fin n → DigitGhost c n)
    (lane : DigitLane) (source target cut now : Nat)
    (h : DigitPairCurrent ring root A T G lane source target cut now) :
    DigitPairCurrent ring root (digitAuditStep ring S A e) T G lane source target cut now := by
  intro offset ho
  obtain ⟨h1, h2, h3⟩ := h offset ho
  exact ⟨currentOutputStep ring S A e root lane source cut now _ _ h1,
    currentInputStep ring S A e root lane source cut now _ _ h2,
    fun hl => currentCarryStep ring S A e root lane source cut now _ (h3 hl)⟩

/-- **A comparison-ready cut persists.**  Consumer: `readyFold`. -/
theorem readyStep (root : Fin n) (restart cut : Nat)
    (h : DigitComparisonReady ring root A restart cut) :
    DigitComparisonReady ring root (digitAuditStep ring S A e) restart cut := by
  obtain ⟨h1, h2, h3, T, G, h4, h5, h6⟩ := h
  refine ⟨h1, by show cut ≤ A.clock + 1; omega, fun source target hp => ?_, T, G,
    digitAtStep ring S A e h4, h5, fun source target hp =>
      pairCurrentStep ring S A e root T G .comparison source target restart cut
        (h6 source target hp)⟩
  obtain ⟨terminal, anchor, anchorTail, a1, a2, a3, a4, a5⟩ := h3 source target hp
  exact ⟨terminal, anchor, anchorTail,
    firstStrictStep ring S A e root source target .comparison restart terminal a1, a2,
    anchorStep ring S A e root source target .comparison anchor anchorTail a3, a4,
    terminalRankedStep ring S A e a5⟩

end Audit

/-! ### The receipts at the band compile -/

/-- **The writer value receipts persist under one audit letter.**  Consumer: `receiptsFold`. -/
theorem receiptsStep {n : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : Fin n → ProjD (compileAdvice (ceilLogTwo n)))
    (A : DigitAudit (compileAdvice (ceilLogTwo n)) n) (e : Fin n) (retired restart : Nat)
    (h : WidthWriterValueReceipts ring root A retired restart) :
    WidthWriterValueReceipts ring root (digitAuditStep ring S A e) retired restart := by
  obtain ⟨first, stop, baseCut, structural, last, cuts, h1, h2, hB, h3, h4, h5⟩ := h
  exact ⟨first, stop, baseCut, structural, last, cuts, h1,
    baseValueCutStep ring S A e root 0 retired baseCut h2,
    boundaryAtStep ring S A e root retired hB,
    structuralCutStep ring S A e root structural h3,
    valueChainStep ring S A e root structural first baseCut h4, h5⟩

section Fold

variable {n : Nat} {ring : DirectedRing n} (ref : WidthDigitReference ring)

/-- **The writer value receipts persist along every continuation** (clause (P) of the comparison
close).  Consumer: `comparisonCutOfReady`. -/
theorem receiptsFold (root : Fin n) (retired restart : Nat) :
    ∀ (w : List (Fin n)) (q : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n),
      WidthWriterValueReceipts ring root q.2 retired restart →
      WidthWriterValueReceipts ring root (w.foldl (widthDigitAuditNext ref) q).2 retired
        restart := by
  intro w
  induction w with
  | nil => intro q h; exact h
  | cons e rest ih =>
    intro q h
    exact ih _ (receiptsStep ring root (piD (ref.phys q.1)) q.2 e retired restart h)

/-- **A comparison-ready cut persists along every continuation.**  Consumer: the assembly of
`WidthComparisonClose` from a ready cut reached before the last pair completes. -/
theorem readyFold (root : Fin n) (restart cut : Nat) :
    ∀ (w : List (Fin n)) (q : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n),
      DigitComparisonReady ring root q.2 restart cut →
      DigitComparisonReady ring root (w.foldl (widthDigitAuditNext ref) q).2 restart cut := by
  intro w
  induction w with
  | nil => intro q h; exact h
  | cons e rest ih =>
    intro q h
    exact ih _ (readyStep ring (piD (ref.phys q.1)) q.2 e root restart cut h)

end Fold

/-! ### The comparison cut from a ready cut -/

/-- **The comparison cut from one ready cut** (any boundary reference): on a continuation `y` of a
values-stable state, a `DigitComparisonReady … restart` cut of the audit of `y` gives
`WidthWriterComparisonCut` at `y` (same clean start and receipts, the W fixed root and the audit
at `y` from the clean run, the first ready cut by `existsFirst`).  Consumer:
`WidthComparisonClose` for both bands (BANK: last premise of
`L3.PacketMomentCompareBank.hcompareBankOfStage`; SMALL: `hcmpCloseSmall` of
`l3HeadlineOfCleanBranches`). -/
theorem comparisonCutOfReady {n : Nat} {ring : DirectedRing n} (ref : WidthBoundaryReference ring)
    (hn : 5 ≤ n) (root : Fin n) (restart : Nat)
    (x : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n) (w : List (Fin n))
    (hx : WidthStableRun ref.toWidthDigitReference root restart x)
    (hready : ∃ cut, DigitComparisonReady ring root
      (w.foldl (widthDigitAuditNext ref.toWidthDigitReference) x).2 restart cut) :
    WidthWriterComparisonCut ref.toWidthDigitReference
      (w.foldl (widthDigitAuditNext ref.toWidthDigitReference) x).1 := by
  obtain ⟨start, word, retired, hst, hfold, hW, -, hrec, hL⟩ := hx
  obtain ⟨root0, hs, -⟩ := widthCleanBoundaryRoot ref start hst
  have hx1 : x.1 = word.foldl ref.next start := by
    have := widthBoundaryDigitBoundaryAuditFirst ref start
      (digitAuditInitial (piD (ref.phys start))) word
    rw [hfold] at this
    exact this
  rw [hx1] at hW hL
  have hr : root = root0 :=
    (widthBoundaryDigitBoundaryWFixedRootOfSingleton ref root0 start hs word).2.1 root hW.1
  subst hr
  have hy : (word ++ w).foldl (widthDigitAuditNext ref.toWidthDigitReference)
      (start, digitAuditInitial (piD (ref.phys start))) =
      w.foldl (widthDigitAuditNext ref.toWidthDigitReference) x := by
    rw [List.foldl_append, hfold]
  have hy1 : (w.foldl (widthDigitAuditNext ref.toWidthDigitReference) x).1 =
      (word ++ w).foldl ref.next start := by
    have := widthBoundaryDigitBoundaryAuditFirst ref start
      (digitAuditInitial (piD (ref.phys start))) (word ++ w)
    rw [hy] at this
    exact this
  have hinv := widthBoundaryDigitBoundaryAuditInvariantRun ref hn root start hs (word ++ w)
  rw [hy] at hinv
  have hLy : WidthDigitLeaderReceipt ref.toWidthDigitReference
      (w.foldl (widthDigitAuditNext ref.toWidthDigitReference) x).1 := by
    rw [hy1, List.foldl_append]
    exact L3.CloseKeep.leaderWord ref hn start hst word hL w
  obtain ⟨cut, hcut⟩ := existsFirst _ hready
  refine ⟨start, word ++ w, root, (w.foldl (widthDigitAuditNext ref.toWidthDigitReference) x).2,
    retired, restart, cut, hst, by rw [hy], ?_, hinv.2.1,
    receiptsFold ref.toWidthDigitReference root retired restart w x hrec, hcut, hLy⟩
  rw [hy1]
  exact widthBoundaryDigitBoundaryWFixedRootOfSingleton ref root start hs (word ++ w)

end L3.ClosePersist

#print axioms L3.ClosePersist.completionBack
#print axioms L3.ClosePersist.receiptsStep
#print axioms L3.ClosePersist.receiptsFold
#print axioms L3.ClosePersist.readyStep
#print axioms L3.ClosePersist.readyFold
#print axioms L3.ClosePersist.comparisonCutOfReady
