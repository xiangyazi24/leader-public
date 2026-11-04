import Leader.L3.Top.FreshTailTicketPrepaid

/-!
Q7c P.3 J5 (groups 2 and 3; paper source
sections 1-2):

* group 2, topFreshTailRootRearmAndOldFrontRows: the tracked fresh root's
  enabled true-tail interior move carries the strengthened home barrier
  from k to k+1 (the departed slot becomes the root's stationary rearm
  U), and an OLD true-tail interior move ahead of the root mints its
  oldVisit child at the OLD departure site while the home barrier and
  the old front are framed;
* group 3, topFreshTailHistoricalOldExitRows: an OLD carrier identity
  (origin, born) seen at any prefix is either live at the end of the
  word, or was the OLD head of a chronological selected terminal
  comparison-port acceptance whose receipt and consumed origin persist.

Group 3 needs one auxiliary reached invariant: an OLD-origin carrier at
source offset zero is a D, never a waiting U (a U at offset zero is
always fresh). Without it, the offset-zero U-to-D rekey would delete an
OLD identity without a receipt. Global leaderlessness is used only to
frame offset zero against an incoming edge.
-/

namespace L3

open Classical

set_option autoImplicit false
set_option Elab.async false

/-- Genealogy-level form of the offset-zero invariant: every OLD-origin
carrier at source offset zero sits on a physical D. -/
def TopFreshTailOldBorderData
    {n : Nat} (s : Fin n) (G : TopFreshTailGenealogyState n) : Prop :=
  ∀ (j : Fin (topClockSpan n)) (a : TopFreshTailCarrier (topClockSpan n)),
    j.val = 0 → G.slots j = some a →
    ((∃ i : Fin (topClockSpan n), a.origin = .inherited i) ∨
      (∃ i t : Fin (topClockSpan n), a.origin = .oldVisit i t)) →
    ∃ (v : Fin (compileAdvice (ceilLogTwo n)).topA) (t : Bool),
      (G.trace.1.1 (certSite s j.val)).qOut = .D v t

/-- The initial labels satisfy the offset-zero invariant: an initial
U at offset zero is the fresh waiting precursor.
Consumer: topFreshTailOldBorderDataReached. -/
theorem topFreshTailOldBorderDataInitial
    {n : Nat} (C : HeadlineConfiguration n) (s : Fin n) :
    TopFreshTailOldBorderData s (topFreshTailGenealogyInitial C s) := by
  intro j a hj hslot hold
  change topFreshTailGenealogyInitialSlot C s j = some a at hslot
  change ∃ (v : Fin (compileAdvice (ceilLogTwo n)).topA) (t : Bool),
    (C (certSite s j.val)).qOut = .D v t
  unfold topFreshTailGenealogyInitialSlot at hslot
  cases h : (C (certSite s j.val)).qOut with
  | E =>
      rw [h] at hslot
      cases hslot
  | U =>
      rw [h] at hslot
      simp only [if_pos hj] at hslot
      cases hslot
      rcases hold with ⟨i, hi⟩ | ⟨i, t, ht⟩
      · cases hi
      · cases ht
  | D v t => exact ⟨v, t, rfl⟩

/-- One genealogy step preserves the offset-zero invariant: a NEW U at
offset zero is a border bootstrap, a border rearm (both fresh), or the
same OLD carrier on an OLD U (excluded by the invariant itself).
Consumer: topFreshTailOldBorderDataReached. -/
theorem topFreshTailOldBorderDataStep
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (G : TopFreshTailGenealogyState n) (e : Fin n)
    (hG : TopFreshTailOldBorderData s G) :
    TopFreshTailOldBorderData s (topFreshTailGenealogyStep ring C s G e) := by
  intro j a hj hslot hold
  change topFreshTailGenealogyNextSlot ring C s G e j = some a at hslot
  unfold topFreshTailGenealogyNextSlot at hslot
  cases hpost : ((topFixedTraceNext ring C G.trace e).1.1
      (certSite s j.val)).qOut with
  | E =>
      simp [hpost] at hslot
  | U =>
      simp only [hpost] at hslot
      cases hprior : (G.trace.1.1 (certSite s j.val)).qOut with
      | E =>
          simp only [hprior, if_pos hj] at hslot
          cases hslot
          rcases hold with ⟨i, hi⟩ | ⟨i, t, ht⟩
          · cases hi
          · cases ht
      | U =>
          have hkeep : G.slots j = some a := by
            simpa only [hprior] using hslot
          obtain ⟨v, t, hD⟩ := hG j a hj hkeep hold
          rw [hprior] at hD
          cases hD
      | D v t =>
          cases t with
          | false =>
              simp [hprior] at hslot
          | true =>
              cases hs : G.slots j with
              | none =>
                  simp [hprior, hs] at hslot
              | some p =>
                  have hchild : topFreshTailGenealogyRearm j
                      (G.trace.1.2.clock + 1) p = a := by
                    simpa [hprior, hs] using hslot
                  rw [← hchild] at hold
                  rcases hold with ⟨i, hi⟩ | ⟨i, k, hk⟩
                  · simp [topFreshTailGenealogyRearm, hj] at hi
                  · simp [topFreshTailGenealogyRearm, hj] at hk
  | D v t => exact ⟨v, t, hpost⟩

/-- On every reached cut an OLD-origin carrier at source offset zero
sits on a physical D. Consumer: topFreshTailOldExitStep. -/
theorem topFreshTailOldBorderDataReached
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (Z : TopFixedTraceState n)
    (hreach : topClockReached ring C Z) :
    ∀ (j : Fin (topClockSpan n)) (a : TopFreshTailCarrier (topClockSpan n)),
      j.val = 0 → (topFreshTailGenealogy ring C s Z).slots j = some a →
      ((∃ i : Fin (topClockSpan n), a.origin = .inherited i) ∨
        (∃ i t : Fin (topClockSpan n), a.origin = .oldVisit i t)) →
      ∃ (v : Fin (compileAdvice (ceilLogTwo n)).topA) (t : Bool),
        (Z.1.1 (certSite s j.val)).qOut = .D v t := by
  have hfold : ∀ (w : List (Fin n)) (G : TopFreshTailGenealogyState n),
      TopFreshTailOldBorderData s G →
      TopFreshTailOldBorderData s (w.foldl (topFreshTailGenealogyStep ring C s) G) := by
    intro w
    induction w with
    | nil => intro G h; exact h
    | cons e rest ih =>
        intro G h
        exact ih _ (topFreshTailOldBorderDataStep ring C s G e h)
  have hG : TopFreshTailOldBorderData s (topFreshTailGenealogy ring C s Z) :=
    hfold Z.2 _ (topFreshTailOldBorderDataInitial C s)
  have htrace := topFreshTailGenealogyTraceReached ring C s Z hreach
  intro j a hj hslot hold
  have h := hG j a hj hslot hold
  rw [htrace] at h
  exact h

/-- Group 3, one-edge row. On a reached cut of a leaderless bad
complete pair, an OLD carrier identity (origin, born) live at source
slot j is, after any actual edge, either live at some source slot, or
was the OLD terminal head of an accepted comparison-port service on
this very edge, whose OLD origin is appended to the consumed list.
Rows: unchanged token (all frames), interior U sample (identity kept),
D hop (identity moves to j+1), accepted terminal D (consumed); an
incoming edge cannot change an occupied slot (offset zero needs the
global leaderless frame); an OLD U at offset zero does not occur.
Consumer: topFreshTailHistoricalOldExitRows (H_old). -/
theorem topFreshTailOldExitStep
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hn : 5 ≤ n)
    (hbad : HeadlineDigit.BadCompletePair C s)
    (hl : ∀ i : Fin n, (C i).l = false)
    (Z : TopFixedTraceState n)
    (hreach : topClockReached ring C Z)
    (e : Fin n) (j : Fin (topClockSpan n))
    (a : TopFreshTailCarrier (topClockSpan n))
    (hslot : (topFreshTailGenealogy ring C s Z).slots j = some a)
    (hold : (∃ i : Fin (topClockSpan n), a.origin = .inherited i) ∨
      (∃ i t : Fin (topClockSpan n), a.origin = .oldVisit i t)) :
    (∃ j' : Fin (topClockSpan n),
      (topFreshTailGenealogy ring C s (topFixedTraceNext ring C Z e)).slots j' =
        some a) ∨
    (j.val + 1 = topClockSpan n ∧ e = certSite s (topClockSpan n - 1) ∧
      ∃ x : DigitExport (compileAdvice (ceilLogTwo n)) n,
        topFreshTailGenealogyPortExport ring C s Z e = some x ∧
        (topFreshTailGenealogy ring C s (topFixedTraceNext ring C Z e)).consumed =
          (topFreshTailGenealogy ring C s Z).consumed ++
            [(Z.1.2.clock + 1, some a.origin)]) := by
  have hr := cert_rho_ge_three n hn
  change 3 ≤ topClockSpan n at hr
  have hqueue := topFreshTailCloseReachedQueue ring C s hn hbad Z hreach
  have htrace := topFreshTailGenealogyTraceReached ring C s Z hreach
  have hne : (Z.1.1 (certSite s j.val)).qOut ≠ .E := by
    intro h
    have := (hqueue.slot j).1 h
    rw [hslot] at this
    cases this
  by_cases hsame : ((topFixedTraceNext ring C Z e).1.1 (certSite s j.val)).qOut =
      (Z.1.1 (certSite s j.val)).qOut
  · left
    refine ⟨j, ?_⟩
    rw [topFreshTailPrepaidSlotFrame ring C s hn hbad Z hreach e j hsame]
    exact hslot
  · by_cases hsrc : e = certSite s j.val
    · have hgeo := topFreshTailCausalSourcePublicGeometry ring C s hn hbad Z hreach j
      have hxl : (Z.1.1 e).l = false := by rw [hsrc]; exact hgeo.1
      have hyl : (Z.1.1 (ring.rightNeighbor e)).l = false := by
        rw [hsrc]; exact hgeo.2.1
      cases hq : (Z.1.1 (certSite s j.val)).qOut with
      | E => exact absurd hq hne
      | U =>
          by_cases hj0 : j.val = 0
          · exfalso
            obtain ⟨v, t, hD⟩ :=
              topFreshTailOldBorderDataReached ring C s Z hreach j a hj0 hslot hold
            rw [hq] at hD
            cases hD
          · left
            refine ⟨j, ?_⟩
            have hnewQ : ((topFixedTraceNext ring C Z e).1.1
                (certSite s j.val)).qOut = .D (Z.1.1 e).d (Z.1.1 e).beta := by
              rw [← hsrc]
              exact topFreshTailFifoUnreadSamples ring C Z e hxl hyl
                (by rw [hsrc]; exact hq)
            rw [topFreshTailCausalReplayNext]
            change topFreshTailGenealogyNextSlot ring C s
              (topFreshTailGenealogy ring C s Z) e j = some a
            unfold topFreshTailGenealogyNextSlot
            rw [htrace, hnewQ, hq]
            simp only [if_neg hj0]
            exact hslot
      | D v t =>
          rcases topFreshTailCausalDSourceOutcomes ring C Z e v t hxl hyl
              (by rw [hsrc]; exact hq) with hstay | hgo
          · exfalso
            apply hsame
            rw [← hsrc, hstay, hsrc, hq]
          · rcases topFreshTailTicketDeparture ring C s hn hbad Z hreach e j hsrc v t hq
                (by rw [← hsrc]; exact hgo) with
              ⟨hnext, _, _, hmove⟩ | ⟨hlast, ⟨x, hx⟩, _⟩
            · left
              exact ⟨⟨j.val + 1, hnext⟩, by rw [hmove]; exact hslot⟩
            · right
              refine ⟨hlast, ?_, x, hx, ?_⟩
              · rw [hsrc]
                congr 1
                omega
              · rw [topFreshTailTicketConsumedStep ring C s hn Z hreach e, hx]
                have hj : j = ⟨topClockSpan n - 1, by omega⟩ := Fin.ext (by
                  show j.val = topClockSpan n - 1
                  omega)
                have hterm : (topFreshTailGenealogy ring C s Z).slots
                    ⟨topClockSpan n - 1, by omega⟩ = some a := by
                  rw [← hj]
                  exact hslot
                rw [hterm]
                rfl
    · exfalso
      by_cases hresp : ring.rightNeighbor e = certSite s j.val
      · by_cases hj0 : j.val = 0
        · have hzero : certSite s j.val = certSite s 0 := by rw [hj0]
          have hframe := topFreshTailPrepaidResponderZeroFrame ring C s hn hbad hl Z
            hreach e (by rw [hresp, hzero])
          rw [hzero] at hsame
          exact hsame hframe
        · rcases topFreshTailTicketSlotPhysical ring C s hn hbad Z hreach e j with
            h1 | h2 | h3 | h4 | h5 | h6
          · exact hsame h1
          · exact hsrc h2.1
          · exact hsrc h3.1
          · exact hsrc h4.1
          · exact hne h5.2.2.1
          · exact hj0 h6.1
      · exact hsame (topPortLiteralAwayFields ring C Z.1.1 e (certSite s j.val)
          (fun h => hsrc h.symm) (fun h => hresp h.symm)).2.2

/-- The consumed list of the actual genealogy only grows along a word.
Consumer: topFreshTailHistoricalOldExitRows. -/
theorem topFreshTailOldExitConsumedGrow
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n) :
    ∀ (v u : List (Fin n))
      (entry : Nat × Option (TopFreshTailOrigin (topClockSpan n))),
      entry ∈ (topFreshTailGenealogy ring C s (topFixedTraceRun ring C u)).consumed →
      entry ∈ (topFreshTailGenealogy ring C s
        (topFixedTraceRun ring C (u ++ v))).consumed := by
  intro v
  induction v with
  | nil =>
      intro u entry h
      rw [List.append_nil]
      exact h
  | cons e rest ih =>
      intro u entry h
      have h1 : entry ∈ (topFreshTailGenealogy ring C s
          (topFixedTraceRun ring C (u ++ [e]))).consumed := by
        rw [topFreshTailFifoRunSnoc, topFreshTailCausalReplayNext]
        simp only [topFreshTailGenealogyStep]
        exact List.mem_append_left _ h
      have h2 := ih (u ++ [e]) entry h1
      have hw : u ++ [e] ++ rest = u ++ e :: rest := by simp
      rw [hw] at h2
      exact h2

/-- Group 3 (H_old). Along any actual scheduler
word u ++ v of a leaderless bad complete pair, an OLD carrier identity
(origin, born) seen at the prefix u is, at the end, either live at some
source slot, or was the OLD head at the terminal slot of a selected
source-terminal service pre ++ [certSite s (r-1)] (pre at least as long
as u) whose comparison-port export is recorded in the final audit, is
stamped pre.length + 1, has exactly one historical scheduler position,
and whose (stamp, OLD origin) is in the final consumed list.
Consumer: H_old in the J5 barrier and first-root family exhaustion. -/
theorem topFreshTailHistoricalOldExitRows
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hn : 5 ≤ n)
    (hbad : HeadlineDigit.BadCompletePair C s)
    (hl : ∀ i : Fin n, (C i).l = false) :
    ∀ (v u : List (Fin n)) (j : Fin (topClockSpan n))
      (a : TopFreshTailCarrier (topClockSpan n)),
      (topFreshTailGenealogy ring C s (topFixedTraceRun ring C u)).slots j = some a →
      ((∃ i : Fin (topClockSpan n), a.origin = .inherited i) ∨
        (∃ i t : Fin (topClockSpan n), a.origin = .oldVisit i t)) →
      (∃ j' : Fin (topClockSpan n),
        (topFreshTailGenealogy ring C s
          (topFixedTraceRun ring C (u ++ v))).slots j' = some a) ∨
      (∃ (pre suffix : List (Fin n))
        (x : DigitExport (compileAdvice (ceilLogTwo n)) n),
        u ++ v = pre ++ [certSite s (topClockSpan n - 1)] ++ suffix ∧
        u.length ≤ pre.length ∧
        (topFreshTailGenealogy ring C s (topFixedTraceRun ring C pre)).slots
          (⟨topClockSpan n - 1, by
            have hr := cert_rho_ge_three n hn
            change 3 ≤ topClockSpan n at hr
            omega⟩ : Fin (topClockSpan n)) = some a ∧
        topFreshTailGenealogyPortExport ring C s (topFixedTraceRun ring C pre)
          (certSite s (topClockSpan n - 1)) = some x ∧
        DigitRecordedExport (topFixedTraceRun ring C (u ++ v)).1.2 x ∧
        x.time = pre.length + 1 ∧
        TopFreshTailAuditHistoricalPortAt ring C s (u ++ v) pre.length x ∧
        (∀ other : Nat,
          TopFreshTailAuditHistoricalPortAt ring C s (u ++ v) other x →
            other = pre.length) ∧
        (x.time, some a.origin) ∈
          (topFreshTailGenealogy ring C s
            (topFixedTraceRun ring C (u ++ v))).consumed) := by
  have hr := cert_rho_ge_three n hn
  change 3 ≤ topClockSpan n at hr
  intro v
  induction v with
  | nil =>
      intro u j a h _
      left
      refine ⟨j, ?_⟩
      rw [List.append_nil]
      exact h
  | cons e rest ih =>
      intro u j a h hold
      have hw : u ++ e :: rest = u ++ [e] ++ rest := by simp
      rw [hw]
      rcases topFreshTailOldExitStep ring C s hn hbad hl (topFixedTraceRun ring C u)
          (topFreshTailAuditRunReached ring C u) e j a h hold with
        ⟨j', hj'⟩ | ⟨hlast, hsite, x, hx, hcons⟩
      · have h' : (topFreshTailGenealogy ring C s
            (topFixedTraceRun ring C (u ++ [e]))).slots j' = some a := by
          rw [topFreshTailFifoRunSnoc]
          exact hj'
        rcases ih (u ++ [e]) j' a h' hold with hlive |
            ⟨pre, suffix, y, hword, hlen, hrest⟩
        · exact Or.inl hlive
        · refine Or.inr ⟨pre, suffix, y, hword, ?_, hrest⟩
          simp only [List.length_append, List.length_singleton] at hlen
          omega
      · right
        have hxe : topFreshTailGenealogyPortExport ring C s (topFixedTraceRun ring C u)
            (certSite s (topClockSpan n - 1)) = some x := by
          rw [← hsite]
          exact hx
        have hrec := topFreshTailAuditHistoricalPortExportRecorded ring C s u rest e x hx
        have hstamp := topFreshTailAuditHistoricalPortStamp ring C s u e x hx
        have hframe := topFreshTailAuditSelectedPortFrame ring C s
          (topFixedTraceRun ring C u) e x hx
        have hpos : TopFreshTailAuditHistoricalPortAt ring C s (u ++ [e] ++ rest)
            u.length x := ⟨u, rest, e, rfl, rfl, hx⟩
        obtain ⟨index, _, huniq⟩ :=
          (topFreshTailAuditHistoricalPortReceiptBijection ring C s (u ++ [e] ++ rest) x
            hframe.2.2.2.2.1
            (hframe.2.2.2.2.2.1.trans hframe.1)
            (hframe.2.2.2.2.2.2.1.trans hframe.2.1)).mp hrec.1
        have hindex : u.length = index := huniq u.length hpos
        have hterm : (topFreshTailGenealogy ring C s (topFixedTraceRun ring C u)).slots
            (⟨topClockSpan n - 1, by omega⟩ : Fin (topClockSpan n)) = some a := by
          have hj : j = ⟨topClockSpan n - 1, by omega⟩ := Fin.ext (by
            show j.val = topClockSpan n - 1
            omega)
          rw [← hj]
          exact h
        have hmem : (x.time, some a.origin) ∈ (topFreshTailGenealogy ring C s
            (topFixedTraceRun ring C (u ++ [e]))).consumed := by
          rw [topFreshTailFifoRunSnoc, hcons, topFreshTailAuditRunClock ring C u,
            hstamp]
          exact List.mem_append_right _ (List.mem_singleton.mpr rfl)
        refine ⟨u, rest, x, by rw [hsite], Nat.le_refl _, hterm, hxe, hrec.1, hstamp,
          hpos, ?_, topFreshTailOldExitConsumedGrow ring C s rest (u ++ [e]) _ hmem⟩
        intro other hother
        exact (huniq other hother).trans hindex.symm

/-- Group 2, tracked-root row ("Tracked root
D(true) into OLD empty nonmarker"). The enabled true-tail interior move
of the tracked fresh root at k carries the strengthened home barrier to
k+1: the root and its sampled atom move right with the OLD front, every
earlier stationary home is off the selected pair and frames, and the
OLD departure slot k becomes the root's own rearm child, a fresh
waiting U. Consumer: B+ root and stationary-home induction (J5). -/
theorem topFreshTailRootRearmAndOldFrontRows
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hn : 5 ≤ n)
    (hbad : HeadlineDigit.BadCompletePair C s)
    (Z : TopFixedTraceState n)
    (root : TopFreshTailCarrier (topClockSpan n))
    (k : Fin (topClockSpan n))
    (sample : DigitSample (compileAdvice (ceilLogTwo n)) n)
    (hbarrier : TopFreshTailFirstBorderHomeBarrier ring C s Z root k sample)
    (hnext : k.val + 1 < topClockSpan n)
    (e : Fin n) (hsite : e = certSite s k.val)
    (hempty : (Z.1.1 (certSite s (k.val + 1))).qOut = .E) :
    TopFreshTailFirstBorderHomeBarrier ring C s (topFixedTraceNext ring C Z e) root
      (⟨k.val + 1, hnext⟩ : Fin (topClockSpan n)) sample ∧
    (topFreshTailGenealogy ring C s (topFixedTraceNext ring C Z e)).slots k =
      some (topFreshTailGenealogyRearm k (Z.1.2.clock + 1) root) ∧
    ((topFixedTraceNext ring C Z e).1.1 (certSite s k.val)).qOut = .U ∧
    ((topFixedTraceNext ring C Z e).1.1 (certSite s (k.val + 1))).qOut =
      .D sample.value true ∧
    ((topFixedTraceNext ring C Z e).1.2.current
      (certSite s (k.val + 1))).comparison.out.atom = some (.sampled sample.id) := by
  have hsp := hbarrier.spatial
  have hq := hsp.queue
  have hreach := hq.trace.1
  have hgeo := topFreshTailCausalSourcePublicGeometry ring C s hn hbad Z hreach k
  have hnb : ring.rightNeighbor e = certSite s (k.val + 1) := by
    rw [hsite, topFreshTailTicketNeighborSite]
  have hemptyR : (Z.1.1 (ring.rightNeighbor e)).qOut = .E := by
    rw [hnb]; exact hempty
  have hspN := topFreshTailFirstBorderSpatialBarrierRootHop ring C s hn hbad Z root k
    sample hsp e hsite hnext hemptyR
  have hxl : (Z.1.1 e).l = false := by rw [hsite]; exact hgeo.1
  have hyl : (Z.1.1 (ring.rightNeighbor e)).l = false := by rw [hsite]; exact hgeo.2.1
  have hyb : (Z.1.1 (ring.rightNeighbor e)).beta = false := by
    have hg := hgeo.2.2.2
    rw [if_neg (show k.val + 1 ≠ topClockSpan n by omega)] at hg
    rw [hsite]
    exact hg
  have hstair := topFreshTailFirstBorderStaircaseStep ring C s hn hbad Z e k hnext hsite
    root hsp.rootSlot hsp.rootFresh sample hsp.sampleRecorded
    (by rw [hsite]; exact hsp.rootAtom) sample.value
    (by rw [hsite]; exact hsp.rootData) hemptyR hxl hyl hyb hq
  refine ⟨{ spatial := hspN, home := ?_ }, hstair.1, ?_, ?_, ?_⟩
  · intro j hj
    change j.val < k.val + 1 at hj
    by_cases hjk : j.val < k.val
    · obtain ⟨h1, h2⟩ :=
        topFreshTailFirstBorderEarlierSiteOffSelectedPair ring s hn j k hjk e hsite
      exact topFreshTailFirstBorderHomeSlotAway ring C s Z root j e hq
        (hbarrier.home j hjk) h1 h2
    · have hjeq : j = k := Fin.ext (by omega)
      rw [hjeq]
      unfold TopFreshTailFirstBorderHomeSlot
      refine ⟨topFreshTailGenealogyRearm k (Z.1.2.clock + 1) root, hstair.1,
        hstair.2.2.2.2.2.2.1, fun _ => ⟨_, rfl⟩, Or.inl ?_⟩
      rw [← hsite]
      exact hstair.2.2.1
  · rw [← hsite]
    exact hstair.2.2.1
  · rw [← hnb]
    exact hstair.2.2.2.1
  · rw [← hnb]
    exact hstair.2.2.2.2.1

/-- Group 2, old-front row ("D(true) of an old
family into OLD empty nonmarker"). An OLD carrier's enabled true-tail
interior move ahead of the tracked root moves the parent to j+1 and
mints its rearm child at the OLD departure slot j (oldVisit i j for an
inherited i parent, oldVisit i t for an oldVisit i t parent), both
strictly ahead of the root; the strengthened home barrier (root, homes
and old front) frames. Consumer: B+ old-front and B.birth induction (J5). -/
theorem topFreshTailOldVisitBirthAheadRow
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hn : 5 ≤ n)
    (hbad : HeadlineDigit.BadCompletePair C s)
    (Z : TopFixedTraceState n)
    (root : TopFreshTailCarrier (topClockSpan n))
    (k : Fin (topClockSpan n))
    (sample : DigitSample (compileAdvice (ceilLogTwo n)) n)
    (hbarrier : TopFreshTailFirstBorderHomeBarrier ring C s Z root k sample)
    (j : Fin (topClockSpan n)) (hahead : k.val < j.val)
    (hnext : j.val + 1 < topClockSpan n)
    (e : Fin n) (hsite : e = certSite s j.val)
    (a : TopFreshTailCarrier (topClockSpan n))
    (hslot : (topFreshTailGenealogy ring C s Z).slots j = some a)
    (v : Fin (compileAdvice (ceilLogTwo n)).topA)
    (hD : (Z.1.1 (certSite s j.val)).qOut = .D v true)
    (hempty : (Z.1.1 (certSite s (j.val + 1))).qOut = .E) :
    TopFreshTailFirstBorderHomeBarrier ring C s (topFixedTraceNext ring C Z e)
      root k sample ∧
    (topFreshTailGenealogy ring C s (topFixedTraceNext ring C Z e)).slots j =
      some (topFreshTailGenealogyRearm j (Z.1.2.clock + 1) a) ∧
    (topFreshTailGenealogy ring C s (topFixedTraceNext ring C Z e)).slots
      (⟨j.val + 1, hnext⟩ : Fin (topClockSpan n)) = some a ∧
    (∀ i : Fin (topClockSpan n), a.origin = .inherited i →
      (topFreshTailGenealogyRearm j (Z.1.2.clock + 1) a).origin = .oldVisit i j) ∧
    (∀ i t : Fin (topClockSpan n), a.origin = .oldVisit i t →
      (topFreshTailGenealogyRearm j (Z.1.2.clock + 1) a).origin = .oldVisit i t) ∧
    ((topFixedTraceNext ring C Z e).1.1 (certSite s j.val)).qOut = .U ∧
    ((topFixedTraceNext ring C Z e).1.1 (certSite s (j.val + 1))).qOut = .D v true := by
  have hq := hbarrier.spatial.queue
  have hreach := hq.trace.1
  have htrace := hq.trace.2
  have hgeo := topFreshTailCausalSourcePublicGeometry ring C s hn hbad Z hreach j
  have hnb : ring.rightNeighbor e = certSite s (j.val + 1) := by
    rw [hsite, topFreshTailTicketNeighborSite]
  have hxo : (Z.1.1 e).qOut = .D v true := by rw [hsite]; exact hD
  have hyo : (Z.1.1 (ring.rightNeighbor e)).qOut = .E := by rw [hnb]; exact hempty
  have hxl : (Z.1.1 e).l = false := by rw [hsite]; exact hgeo.1
  have hyl : (Z.1.1 (ring.rightNeighbor e)).l = false := by rw [hsite]; exact hgeo.2.1
  have hyb : (Z.1.1 (ring.rightNeighbor e)).beta = false := by
    have hg := hgeo.2.2.2
    rw [if_neg (show j.val + 1 ≠ topClockSpan n by omega)] at hg
    rw [hsite]
    exact hg
  have hmoveCarrier := topFreshTailCausalRearmBehindMovedParent ring (by omega : 2 ≤ n)
    C s (topFreshTailGenealogy ring C s Z) e j v a hnext hsite
    (by rw [htrace]; exact hxo) (by rw [htrace]; exact hyo)
    (by rw [htrace]; exact hxl) (by rw [htrace]; exact hyl)
    (by rw [htrace]; exact hyb) hslot
  rw [htrace] at hmoveCarrier
  have hmove := topFreshTailFifoDataMove ring (by omega : 2 ≤ n) C Z e v true
    hxl hyl hxo hyo hyb
  have hj0 : j.val ≠ 0 := by omega
  refine ⟨topFreshTailFirstBorderHomeBarrierAheadStep ring C s hn hbad Z root k sample
      hbarrier j hahead e hsite, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [topFreshTailCausalReplayNext]
    exact hmoveCarrier.1
  · rw [topFreshTailCausalReplayNext]
    exact hmoveCarrier.2
  · intro i hi
    simp [topFreshTailGenealogyRearm, hj0, hi]
  · intro i t ht
    simp [topFreshTailGenealogyRearm, hj0, ht]
  · rw [← hsite]
    simpa only [ite_true] using hmove.1
  · rw [← hnb]
    exact hmove.2

end L3

#print axioms L3.topFreshTailOldBorderDataInitial
#print axioms L3.topFreshTailOldBorderDataStep
#print axioms L3.topFreshTailOldBorderDataReached
#print axioms L3.topFreshTailOldExitStep
#print axioms L3.topFreshTailOldExitConsumedGrow
#print axioms L3.topFreshTailHistoricalOldExitRows
#print axioms L3.topFreshTailRootRearmAndOldFrontRows
#print axioms L3.topFreshTailOldVisitBirthAheadRow
