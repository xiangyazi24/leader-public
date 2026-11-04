import Leader.L3.Top.FreshTailBarrierRun

/-!
Q7c P.3 J5, post-anchor wave: independently reusable one-edge
bridges from the actual OLD physical/audit trace.

The complete TopFreshTailPostAnchorWave successor is NOT claimed:
a producer for the coupled true-tail interior rearm and global
W.currentOrder/W.rootAndNext/W.sourceCoverage update is still
needed. The same coupled closure is needed after terminal
true-tail acceptance. These are not consequences of the
audit append facts alone.
-/

namespace L3

set_option autoImplicit false
set_option Elab.async false

/-- Each recorded stationary home in the first-root staircase
is an active current-wave home at precisely its own source slot.
Consumer: the W base after topFreshTailFirstRootStaircaseExit. -/
theorem topFreshTailPostAnchorStaircaseActiveHome
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (Z : TopFixedTraceState n)
    (root : TopFreshTailCarrier (topClockSpan n))
    (j : Fin (topClockSpan n))
    (hhome : TopFreshTailFirstBorderHomeSlot ring C s Z root j) :
    ∃ carrier : TopFreshTailCarrier (topClockSpan n),
      TopFreshTailPostAnchorActiveHome
        ring C s Z j j carrier := by
  unfold TopFreshTailFirstBorderHomeSlot at hhome
  obtain ⟨carrier, hslot, hfresh, _, hkind⟩ := hhome
  refine ⟨carrier, Nat.le_refl _, hslot, hfresh, ?_⟩
  rcases hkind with hunread |
      ⟨localSample, hdata, hrecord, hlane,
        hsite, hvalue, htail, hatom⟩
  · exact Or.inl ⟨rfl, hunread⟩
  · exact Or.inr
      ⟨localSample, hdata, hrecord, hlane,
        hsite, hvalue, htail, hatom⟩

/-- On every actual scheduler edge the reached audit and
the pinned anchor persist; the chronological post-anchor
comparison-export list is unchanged or appends one actual
frame's qualified port export. This is the audit half of
W.oneEdge, not the physical packet-order half.
Consumer: topFreshTailPostAnchorWaveOneEdge. -/
theorem topFreshTailPostAnchorWaveEdgeAuditEnvelope
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hn : 5 ≤ n)
    (hbad : HeadlineDigit.BadCompletePair C s)
    (Z : TopFixedTraceState n)
    (anchor : DigitExport
      (compileAdvice (ceilLogTwo n)) n)
    (hwave : TopFreshTailPostAnchorWave
      ring C s hn Z anchor)
    (e : Fin n) :
    topClockReached ring C (topFixedTraceNext ring C Z e) ∧
    topClockConcreteTailAnchor s
      (topFixedTraceNext ring C Z e) anchor ∧
    TopFreshTailCausalQueue ring C s
      (topFixedTraceNext ring C Z e) ∧
    TopFreshTailAuditSourceDataProvenance ring C s
      (topFixedTraceNext ring C Z e) ∧
    (topClockConcreteExportsAfter s
        (topFixedTraceNext ring C Z e) anchor.time =
       topClockConcreteExportsAfter s Z anchor.time ∨
      ∃ exported : DigitExport
          (compileAdvice (ceilLogTwo n)) n,
        topClockConcreteExportsAfter s
          (topFixedTraceNext ring C Z e) anchor.time =
          topClockConcreteExportsAfter s Z anchor.time ++
            [exported] ∧
        anchor.time < exported.time ∧
        exported.source =
          certSite s (topClockSpan n - 1) ∧
        exported.destination =
          certSite s (topClockSpan n)) := by
  have hqueueNext :=
    topFreshTailCausalQueueStep
      ring C s hn hbad Z e hwave.queue
  have hanchorNext :=
    topClockTailAnchorNext
      ring C s Z e anchor hwave.anchorRecorded
  have hprovNext :=
    topFreshTailAuditSourceDataReached
      ring C s hn hbad
      (topFixedTraceNext ring C Z e)
      hqueueNext.trace.1
  refine ⟨hqueueNext.trace.1, hanchorNext,
    hqueueNext, hprovNext, ?_⟩
  rcases topFreshTailPostAnchorNewEntriesShape
      ring s Z anchor.time e with hsilent |
      ⟨exported, hsingleton, htime, hsource, hdestination⟩
  · left
    rw [topFreshTailPostAnchorExportsAfterStep, hsilent]
    simp only [List.append_nil]
  · right
    refine ⟨exported, ?_, htime, hsource, hdestination⟩
    rw [topFreshTailPostAnchorExportsAfterStep, hsingleton]

/-- An actually selected current-wave D with an empty
nonmarker successor transports the same fresh carrier and
its original home-site sampled comparison atom to the right.
The OLD source emits U for the home-zero true tail and E for
any false tail, irrespective of source input and carry.
This supplies the local transport component but not the
global W.next or W.sourceCoverage partition reindexing.
Consumer: topFreshTailPostAnchorWaveOneEdge. -/
theorem topFreshTailPostAnchorActiveHomeInteriorMove
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hn : 5 ≤ n)
    (hbad : HeadlineDigit.BadCompletePair C s)
    (Z : TopFixedTraceState n)
    (hqueue : TopFreshTailCausalQueue ring C s Z)
    (h x : Fin (topClockSpan n))
    (carrier : TopFreshTailCarrier (topClockSpan n))
    (hactive :
      TopFreshTailPostAnchorActiveHome
        ring C s Z h x carrier)
    (e : Fin n) (hsite : e = certSite s x.val)
    (hnext : x.val + 1 < topClockSpan n)
    (hdata :
      (Z.1.1 e).qOut =
        .D (C (certSite s h.val)).d
          (if h.val = 0 then true else false))
    (hempty :
      (Z.1.1 (ring.rightNeighbor e)).qOut = .E) :
    TopFreshTailPostAnchorActiveHome
      ring C s (topFixedTraceNext ring C Z e)
      h
      (⟨x.val + 1, hnext⟩ : Fin (topClockSpan n))
      carrier ∧
    ((topFixedTraceNext ring C Z e).1.1 e).qOut =
      (if h.val = 0 then .U else .E) := by
  obtain ⟨hhomeLe, hslot, hfresh, hkind⟩ := hactive
  rcases hkind with ⟨_, hunread⟩ |
      ⟨localSample, _, hrecord, hlane,
        hsampleSite, hsampleValue, hsampleTail, hatom⟩
  · rw [hsite] at hdata
    rw [hunread] at hdata
    cases hdata
  · have hgeometry :=
      topFreshTailCausalSourcePublicGeometry
        ring C s hn hbad Z hqueue.trace.1 x
    have hxl : (Z.1.1 e).l = false := by
      rw [hsite]
      exact hgeometry.1
    have hyl :
        (Z.1.1 (ring.rightNeighbor e)).l = false := by
      rw [hsite]
      exact hgeometry.2.1
    have hyb :
        (Z.1.1 (ring.rightNeighbor e)).beta = false := by
      have hmarker := hgeometry.2.2.2
      rw [if_neg (show x.val + 1 ≠ topClockSpan n by omega)] at hmarker
      rw [hsite]
      exact hmarker
    have hneighbor :
        ring.rightNeighbor e = certSite s (x.val + 1) := by
      rw [hsite]
      exact topFreshTailFirstBorderNeighborSite ring s x.val
    have htrace := hqueue.trace.2
    have hmoveCarrier :=
      topFreshTailCausalDataMoveTarget
        ring (by omega : 2 ≤ n)
        C s (topFreshTailGenealogy ring C s Z)
        e x (C (certSite s h.val)).d
        (if h.val = 0 then true else false)
        carrier hnext hsite
        (by rw [htrace]; exact hdata)
        (by rw [htrace]; exact hempty)
        (by rw [htrace]; exact hxl)
        (by rw [htrace]; exact hyl)
        (by rw [htrace]; exact hyb)
        hslot
    have hslotNext :
        (topFreshTailGenealogy ring C s
          (topFixedTraceNext ring C Z e)).slots
          (⟨x.val + 1, hnext⟩ : Fin (topClockSpan n)) =
          some carrier := by
      rw [topFreshTailCausalReplayNext]
      exact hmoveCarrier
    have hphysical :=
      topFreshTailFifoDataMove
        ring (by omega : 2 ≤ n) C Z e
        (C (certSite s h.val)).d
        (if h.val = 0 then true else false)
        hxl hyl hdata hempty hyb
    have hnewData :
        ((topFixedTraceNext ring C Z e).1.1
          (certSite s (x.val + 1))).qOut =
          .D (C (certSite s h.val)).d
            (if h.val = 0 then true else false) := by
      rw [← hneighbor]
      exact hphysical.2
    have hatomTransport :=
      topFreshTailAuditPhysicalMoveAtom
        ring (by omega : 2 ≤ n) C Z e
        (C (certSite s h.val)).d
        (if h.val = 0 then true else false)
        hxl hyl hdata hyb hempty
    have hatomNext :
        ((topFixedTraceNext ring C Z e).1.2.current
          (certSite s (x.val + 1))).comparison.out.atom =
          some (.sampled localSample.id) := by
      rw [← hneighbor, hatomTransport, hsite]
      exact hatom
    constructor
    · refine ⟨(show h.val ≤ x.val + 1 by omega), hslotNext, hfresh, Or.inr ?_⟩
      exact ⟨localSample, hnewData,
        digitRecordedSampleStep
          ring (piD Z.1.1) Z.1.2 e
          localSample hrecord,
        hlane, hsampleSite, hsampleValue,
        hsampleTail, hatomNext⟩
    · rw [hphysical.1]
      by_cases hh : h.val = 0 <;> simp [hh]

end L3

namespace L3

set_option autoImplicit false
set_option Elab.async false

/-- A real service away from the source comparison terminal
cannot add a qualified post-anchor comparison-port export.
The new OLD audit frame has source e, whereas every filtered
port export has source certSite s (topClockSpan n - 1).
Consumer: W.export on the nonterminal OLD row groups. -/
theorem topFreshTailPostAnchorNonterminalSilent
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (Z : TopFixedTraceState n) (anchorTime : Nat)
    (e : Fin n)
    (hnotport : e ≠ certSite s (topClockSpan n - 1)) :
    topClockConcreteExportsAfter s
      (topFixedTraceNext ring C Z e) anchorTime =
      topClockConcreteExportsAfter s Z anchorTime := by
  cases hlocal :
      (digitReceiptLane .comparison
        (topFreshTailPostAnchorCurrentFrame
          ring Z e).receipt).exported with
  | none =>
      have hsilent :
          topFreshTailPostAnchorNewEntries
            ring s Z anchorTime e = [] := by
        simp [topFreshTailPostAnchorNewEntries, hlocal]
      rw [topFreshTailPostAnchorExportsAfterStep, hsilent]
      simp only [List.append_nil]
  | some exported =>
      have hservice :
          (digitLaneReplay .comparison
            (Z.1.2.clock + 1) e (ring.rightNeighbor e)
            (digitLaneView .comparison
              (piD Z.1.1 e) (piD Z.1.1 e).word.beta)
            (digitLaneView .comparison
              (piD Z.1.1 (ring.rightNeighbor e))
              (piD Z.1.1 (ring.rightNeighbor e)).word.beta)
            (Z.1.2.current e).comparison
            (Z.1.2.current
              (ring.rightNeighbor e)).comparison).exported =
            some exported := by
        change
          (digitLaneReplay .comparison
            (Z.1.2.clock + 1) e (ring.rightNeighbor e)
            (digitLaneView .comparison
              (piD Z.1.1 e) (piD Z.1.1 e).word.beta)
            (digitLaneView .comparison
              (piD Z.1.1 (ring.rightNeighbor e))
              (piD Z.1.1 (ring.rightNeighbor e)).word.beta)
            (Z.1.2.current e).comparison
            (Z.1.2.current
              (ring.rightNeighbor e)).comparison).exported =
            some exported at hlocal
        exact hlocal
      obtain ⟨_, _, hsource, _, _⟩ :=
        topFreshTailAuditLaneExportFields
          .comparison (Z.1.2.clock + 1)
          e (ring.rightNeighbor e)
          (digitLaneView .comparison
            (piD Z.1.1 e) (piD Z.1.1 e).word.beta)
          (digitLaneView .comparison
            (piD Z.1.1 (ring.rightNeighbor e))
            (piD Z.1.1 (ring.rightNeighbor e)).word.beta)
          (Z.1.2.current e).comparison
          (Z.1.2.current
            (ring.rightNeighbor e)).comparison
          exported hservice
      have hqual :
          ¬ (anchorTime < exported.time ∧
            exported.source =
              certSite s (topClockSpan n - 1) ∧
            exported.destination =
              certSite s (topClockSpan n)) := by
        intro h
        exact hnotport (hsource.symm.trans h.2.1)
      have hsilent :
          topFreshTailPostAnchorNewEntries
            ring s Z anchorTime e = [] := by
        simp [topFreshTailPostAnchorNewEntries,
          hlocal, hqual]
      rw [topFreshTailPostAnchorExportsAfterStep, hsilent]
      simp only [List.append_nil]

/-- Actual enabled source-zero-family D(true) interior service.
The tracked current root advances with its original sampled
home-zero atom, its OLD departure mints a fresh stationary U
which ALSO satisfies ActiveHome with home equal to k, and
every previous root-home staircase site still frames. The
concrete post-anchor export count is unchanged.

This is the genuine coupled local root/child row. It does
not assert the universal currentOrder field: that field
misclassifies this new next-wave U as a current-wave home k
whenever k is within the current export-indexed home range.
Consumer: corrected W.next and W.sourceCoverage induction. -/
theorem topFreshTailPostAnchorTrueHopRootAndChild
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hn : 5 ≤ n)
    (hbad : HeadlineDigit.BadCompletePair C s)
    (Z : TopFixedTraceState n)
    (anchor : DigitExport
      (compileAdvice (ceilLogTwo n)) n)
    (hwave : TopFreshTailPostAnchorWave
      ring C s hn Z anchor)
    (root : TopFreshTailCarrier (topClockSpan n))
    (k : Fin (topClockSpan n))
    (hroot :
      TopFreshTailPostAnchorActiveHome ring C s Z
        (⟨0, show 0 < topClockSpan n by
          have hr := cert_rho_ge_three n hn
          change 3 ≤ topClockSpan n at hr
          omega⟩ : Fin (topClockSpan n)) k root)
    (sample : DigitSample
      (compileAdvice (ceilLogTwo n)) n)
    (hrecord : DigitRecordedSample Z.1.2 sample)
    (hatom :
      (Z.1.2.current
        (certSite s k.val)).comparison.out.atom =
        some (.sampled sample.id))
    (hrootData :
      (Z.1.1 (certSite s k.val)).qOut =
        .D (C (certSite s 0)).d true)
    (hhomes :
      ∀ j : Fin (topClockSpan n), j.val < k.val →
        TopFreshTailFirstBorderHomeSlot ring C s Z root j)
    (e : Fin n)
    (hsite : e = certSite s k.val)
    (hnext : k.val + 1 < topClockSpan n)
    (hempty :
      (Z.1.1 (ring.rightNeighbor e)).qOut = .E) :
    TopFreshTailPostAnchorActiveHome
      ring C s (topFixedTraceNext ring C Z e)
      (⟨0, show 0 < topClockSpan n by
        have hr := cert_rho_ge_three n hn
        change 3 ≤ topClockSpan n at hr
        omega⟩ : Fin (topClockSpan n))
      (⟨k.val + 1, hnext⟩ : Fin (topClockSpan n))
      root ∧
    TopFreshTailPostAnchorActiveHome
      ring C s (topFixedTraceNext ring C Z e) k k
      (topFreshTailGenealogyRearm k
        (Z.1.2.clock + 1) root) ∧
    (∀ j : Fin (topClockSpan n),
      j.val < k.val + 1 →
      TopFreshTailFirstBorderHomeSlot ring C s
        (topFixedTraceNext ring C Z e) root j) ∧
    topClockConcreteExportsAfter s
      (topFixedTraceNext ring C Z e) anchor.time =
      topClockConcreteExportsAfter s Z anchor.time := by
  have hr := cert_rho_ge_three n hn
  change 3 ≤ topClockSpan n at hr
  have hsource :
      (Z.1.1 e).qOut =
        .D (C (certSite s 0)).d true := by
    rw [hsite]
    exact hrootData
  have hrootNext :=
    topFreshTailPostAnchorActiveHomeInteriorMove
      ring C s hn hbad Z hwave.queue
      (⟨0, show 0 < topClockSpan n by omega⟩ :
        Fin (topClockSpan n))
      k root hroot e hsite hnext
      (by simpa only [Fin.val_mk, if_true] using hsource)
      hempty
  obtain ⟨_, hrootSlot, hrootFresh, _⟩ := hroot
  have hgeometry :=
    topFreshTailCausalSourcePublicGeometry
      ring C s hn hbad Z hwave.reached k
  have hxl : (Z.1.1 e).l = false := by
    rw [hsite]
    exact hgeometry.1
  have hyl :
      (Z.1.1 (ring.rightNeighbor e)).l = false := by
    rw [hsite]
    exact hgeometry.2.1
  have hyb :
      (Z.1.1 (ring.rightNeighbor e)).beta = false := by
    have hmarker := hgeometry.2.2.2
    rw [if_neg (show k.val + 1 ≠ topClockSpan n by omega)] at hmarker
    rw [hsite]
    exact hmarker
  have hatomSource :
      (Z.1.2.current e).comparison.out.atom =
        some (.sampled sample.id) := by
    rw [hsite]
    exact hatom
  obtain ⟨hchildSlot, _, hsourceU, _, _, _,
      hchildFresh, _⟩ :=
    topFreshTailFirstBorderStaircaseStep
      ring C s hn hbad Z e k hnext hsite
      root hrootSlot hrootFresh sample hrecord
      hatomSource (C (certSite s 0)).d hsource
      hempty hxl hyl hyb hwave.queue
  have hchildU :
      ((topFixedTraceNext ring C Z e).1.1
        (certSite s k.val)).qOut = .U := by
    rw [← hsite]
    exact hsourceU
  have hchildActive :
      TopFreshTailPostAnchorActiveHome
        ring C s (topFixedTraceNext ring C Z e) k k
        (topFreshTailGenealogyRearm k
          (Z.1.2.clock + 1) root) := by
    exact ⟨Nat.le_refl _, hchildSlot, hchildFresh,
      Or.inl ⟨rfl, hchildU⟩⟩
  have hchildHome :
      TopFreshTailFirstBorderHomeSlot
        ring C s (topFixedTraceNext ring C Z e)
        root k := by
    unfold TopFreshTailFirstBorderHomeSlot
    refine ⟨topFreshTailGenealogyRearm k
      (Z.1.2.clock + 1) root,
      hchildSlot, hchildFresh, ?_, Or.inl hchildU⟩
    intro _
    exact ⟨Z.1.2.clock + 1, rfl⟩
  have hstair :
      ∀ j : Fin (topClockSpan n),
        j.val < k.val + 1 →
        TopFreshTailFirstBorderHomeSlot
          ring C s (topFixedTraceNext ring C Z e)
          root j := by
    intro j hj
    by_cases hearlier : j.val < k.val
    · obtain ⟨hawaySource, hawayTarget⟩ :=
        topFreshTailFirstBorderEarlierSiteOffSelectedPair
          ring s hn j k hearlier e hsite
      exact topFreshTailFirstBorderHomeSlotAway
        ring C s Z root j e hwave.queue
        (hhomes j hearlier) hawaySource hawayTarget
    · have heq : j = k := Fin.ext (by omega)
      rw [heq]
      exact hchildHome
  have hnotport :
      e ≠ certSite s (topClockSpan n - 1) := by
    intro heq
    have hsameSite :
        certSite s k.val =
          certSite s (topClockSpan n - 1) :=
      hsite.symm.trans heq
    have hsameIndex :=
      topFreshTailCausalSourceSiteInjective s hn k
        (⟨topClockSpan n - 1,
          show topClockSpan n - 1 < topClockSpan n by omega⟩ :
            Fin (topClockSpan n))
        hsameSite
    have hvalues := congrArg Fin.val hsameIndex
    change k.val = topClockSpan n - 1 at hvalues
    omega
  exact ⟨hrootNext.1, hchildActive, hstair,
    topFreshTailPostAnchorNonterminalSilent
      ring C s Z anchor.time e hnotport⟩

end L3

#print axioms L3.topFreshTailPostAnchorStaircaseActiveHome
#print axioms L3.topFreshTailPostAnchorWaveEdgeAuditEnvelope
#print axioms L3.topFreshTailPostAnchorActiveHomeInteriorMove
#print axioms L3.topFreshTailPostAnchorNonterminalSilent
#print axioms L3.topFreshTailPostAnchorTrueHopRootAndChild
