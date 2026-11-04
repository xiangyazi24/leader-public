import Leader.L3.Top.PinnedPrepareLinks

/-!
# Q7 (preparation, lemma 1, bridge): the pending-or-settled audit window follows the physical window

For a fixed-trace state `Y` and a time `τ`, every edge acts on the labelled window
`(cellOf, paFlagSettled, paLabSettled, paQ)` as one step of the abstract pending-or-settled
labelled window (`PuStep`): a window edge moves a flagged pending input with its label or settles
it in place, the terminal edge settles or deletes the flagged source, the port edge cleans or
accepts, and the accepted packet is appended to the queue of exports after `τ`.

Consumer: `Leader/L3/Top/PinnedPrepareSettled.lean`.
-/

namespace L3
namespace MarkedCells

open Classical

set_option autoImplicit false
set_option linter.unusedSimpArgs false

/-- The pending-or-settled labelled window of `Z` is the abstract data `(c', o', ℓ', Q')` on the
target registers.

Consumer: `bridge_step_settled`. -/
def PuAgree {n : Nat} (s : Fin n) (Z : TopFixedTraceState n) (τ : Nat)
    (c' : Nat → Cell) (o' : Nat → Bool) (ℓ' : Nat → PaLabel n) (Q' : List (PaLabel n)) : Prop :=
  (∀ j, j < topClockSpan n → cellOf s Z j = c' j) ∧
  (∀ j, j < topClockSpan n → paFlagSettled s Z τ j = o' j) ∧
  (∀ j, j < topClockSpan n → o' j = true → paLabSettled s Z j = ℓ' j) ∧
  paQ s Z τ = Q'

/-- **A window edge is an abstract labelled edge.**

Consumer: `bridge_step_settled`. -/
theorem window_bridge_settled {n : Nat} (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (s : Fin n) (hg : WinGeo ring C s) (τ : Nat) (Y : TopFixedTraceState n)
    (hreach : topClockReached ring C Y) (p : Nat) (hp1 : p + 1 < topClockSpan n) :
    ∃ c' o' ℓ' Q', PuStep (topClockSpan n) (cellOf s Y) (paFlagSettled s Y τ) (paLabSettled s Y) (paQ s Y τ)
        c' o' ℓ' Q' ∧
      PuAgree s (topFixedTraceNext ring C Y (winSite s p)) τ c' o' ℓ' Q' := by
  have hp : p < topClockSpan n := by omega
  refine ⟨_, _, _, _, PuStep.edge p hp1, ?_⟩
  have hn2 : 2 ≤ n := by have := hg.hn; omega
  have hr3 := span_ge_three hg.hn
  have hxl : (Y.1.1 (winSite s p)).l = false := agent_l ring C s hg Y hreach _
  have hyl : (Y.1.1 (ring.rightNeighbor (winSite s p))).l = false :=
    agent_l ring C s hg Y hreach _
  have hag := link_window ring C s Y hg hreach p hp
  have hb : winSite s p ≠ certSite s (topClockSpan n - 1) := win_ne_port hg.hn s p hp
  have hpost0 := post_step_away ring C s Y (winSite s p) τ hb
  have hpost : PostIn ring C s Y (winSite s p) τ := fun v => hpost0 _
  have hrn : ring.rightNeighbor (winSite s p) = winSite s (p + 1) := winSite_next ring s p
  have hyb : (Y.1.1 (ring.rightNeighbor (winSite s p))).beta = false := by
    rw [hrn, agent_beta ring C Y hreach, winSite_beta ring C s hg.hbad (p + 1) hp1]
    simp
  have hcp : cellOf s (topFixedTraceNext ring C Y (winSite s p)) p =
      (pair (decide (p = 0)) false (cellOf s Y p) (cellOf s Y (p + 1))).1 := by
    rw [hag p hp]; simp [edgeStep, hp1, setTwo]
  have hcq : cellOf s (topFixedTraceNext ring C Y (winSite s p)) (p + 1) =
      (pair (decide (p = 0)) false (cellOf s Y p) (cellOf s Y (p + 1))).2 := by
    rw [hag (p + 1) hp1]; simp [edgeStep, hp1, setTwo]
  have hdisj : ∀ j, j < topClockSpan n → j ≠ p → j ≠ p + 1 →
      winSite s j ≠ winSite s p ∧ winSite s j ≠ ring.rightNeighbor (winSite s p) := by
    intro j hj hjp hjq
    refine ⟨fun h => hjp (winSite_inj hg.hn s j p (by omega) (by omega) h), ?_⟩
    rw [hrn]
    intro h
    exact hjq (winSite_inj hg.hn s j (p + 1) (by omega) (by omega) h)
  have hflags : ∀ j, j < topClockSpan n →
      paFlagSettled s (topFixedTraceNext ring C Y (winSite s p)) τ j =
        puFlagsEdge (cellOf s Y) (paFlagSettled s Y τ) p j := by
    intro j hj
    apply Bool.eq_iff_iff.2
    unfold puFlagsEdge
    by_cases hjp : j = p
    · subst hjp
      simp only [if_true, Bool.and_eq_true, paFlag_settled_site]
      rw [← hcp, cell_nonE_iff]
      constructor
      · rintro ⟨hj', hF⟩
        obtain ⟨hF1, hF2⟩ := (src_flag_settled ring C s Y _ τ hxl hyl hpost).1 hF
        exact ⟨⟨hj', hF1⟩, hF2⟩
      · rintro ⟨⟨hj', hF1⟩, hF2⟩
        exact ⟨hj', (src_flag_settled ring C s Y _ τ hxl hyl hpost).2 ⟨hF1, hF2⟩⟩
    · simp only [if_neg hjp]
      by_cases hjq : j = p + 1
      · subst hjq
        simp only [if_true, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true',
          paFlag_settled_site]
        rw [← hcq]
        simp only [cell_nonE_iff]
        rw [← hrn]
        have hrf := resp_flag_settled ring hn2 C s Y (winSite s p) τ hxl hyl hyb hpost
        rw [hrf]
        constructor
        · rintro ⟨hj', hF | hF⟩
          · exact Or.inl ⟨⟨hj', hF.1⟩, hF.2⟩
          · exact Or.inr ⟨⟨⟨hp, hF.1⟩, hF.2.1⟩, hF.2.2⟩
        · rintro (⟨⟨hj', hF⟩, hP'⟩ | ⟨⟨⟨_, hF⟩, hn⟩, hP'⟩)
          · exact ⟨hj', Or.inl ⟨hF, hP'⟩⟩
          · exact ⟨hj, Or.inr ⟨hF, hn, hP'⟩⟩
      · simp only [if_neg hjq, paFlag_settled_site]
        obtain ⟨hd1, hd2⟩ := hdisj j hj hjp hjq
        rw [(away_flag_settled ring C s Y _ _ τ hd1 hd2 hpost).1]
  refine ⟨?_, hflags, ?_, ?_⟩
  · intro j hj
    rw [hag j hj]
    unfold edgeStep
    rw [if_pos hp1]
  · intro j hj hoj
    have hF : paFlagSettled s (topFixedTraceNext ring C Y (winSite s p)) τ j = true := by
      rw [hflags j hj]; exact hoj
    by_cases hjp : j = p
    · have hF' := (paFlag_settled_site s τ _ j).1 hF
      rw [hjp] at hF'
      obtain ⟨_, hF2⟩ := hF'
      obtain ⟨_, j2, j3⟩ := src_link_settled ring C Y (winSite s p) hxl hyl hF2.1
      have hnq : ¬ j = p + 1 := by omega
      unfold puLabEdge
      rw [if_neg hnq]
      rw [hjp, paLab_settled_site, paLab_settled_site]
      unfold SiteLabSettled
      rw [j2, j3]
    · by_cases hjq : j = p + 1
      · have hF' := (paFlag_settled_site s τ _ j).1 hF
        obtain ⟨_, hF2⟩ := hF'
        rw [hjq, ← hrn] at hF2
        have hPn := hF2.1
        unfold puLabEdge
        rw [if_pos hjq]
        rw [hjq, paLab_settled_site, ← hrn]
        rcases resp_link_settled ring hn2 C Y (winSite s p) hxl hyl hPn with
          ⟨d1, d2, d3⟩ | ⟨_, d2, d3, d4, d5⟩ | ⟨d1, _⟩
        · have hnon : puNonE (cellOf s Y (p + 1)).i = true := by
            rw [cell_nonE_iff, ← hrn]; exact d1
          rw [if_pos hnon, paLab_settled_site, ← hrn]
          unfold SiteLabSettled
          rw [d2, d3]
        · have hnon : puNonE (cellOf s Y (p + 1)).i = false := by
            rw [cell_nonE_iff, ← hrn, d2]; rfl
          have hn' : ¬ (puNonE (cellOf s Y (p + 1)).i = true) := by rw [hnon]; decide
          rw [if_neg hn', paLab_settled_site]
          unfold SiteLabSettled
          rw [d5, d4]
        · rw [hyb] at d1; exact absurd d1 (by decide)
      · unfold puLabEdge
        rw [if_neg hjq]
        obtain ⟨hd1, hd2⟩ := hdisj j hj hjp hjq
        rw [paLab_settled_site, paLab_settled_site]
        exact (away_flag_settled ring C s Y _ _ τ hd1 hd2 hpost).2
  · unfold paQ
    rw [exportsAfter_step_away ring C s Y _ τ hb]


/-- **The terminal edge is an abstract labelled edge.**

Consumer: `bridge_step_settled`. -/
theorem term_bridge_settled {n : Nat} (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (s : Fin n) (hg : WinGeo ring C s) (τ : Nat) (Y : TopFixedTraceState n)
    (hreach : topClockReached ring C Y) :
    ∃ c' o' ℓ' Q', PuStep (topClockSpan n) (cellOf s Y) (paFlagSettled s Y τ) (paLabSettled s Y) (paQ s Y τ)
        c' o' ℓ' Q' ∧
      PuAgree s (topFixedTraceNext ring C Y (winSite s (topClockSpan n - 1))) τ c' o' ℓ' Q' := by
  have hr3 := span_ge_three hg.hn
  have hp : topClockSpan n - 1 < topClockSpan n := by omega
  have hnl : ¬ (topClockSpan n - 1 + 1 < topClockSpan n) := by omega
  refine ⟨_, _, _, _, PuStep.term, ?_⟩
  have hxl : (Y.1.1 (winSite s (topClockSpan n - 1))).l = false :=
    agent_l ring C s hg Y hreach _
  have hyl : (Y.1.1 (ring.rightNeighbor (winSite s (topClockSpan n - 1)))).l = false :=
    agent_l ring C s hg Y hreach _
  have hag := link_window ring C s Y hg hreach (topClockSpan n - 1) hp
  have hb : winSite s (topClockSpan n - 1) ≠ certSite s (topClockSpan n - 1) :=
    win_ne_port hg.hn s (topClockSpan n - 1) hp
  have hpost0 := post_step_away ring C s Y (winSite s (topClockSpan n - 1)) τ hb
  have hpost : PostIn ring C s Y (winSite s (topClockSpan n - 1)) τ := fun v => hpost0 _
  have hrn : ring.rightNeighbor (winSite s (topClockSpan n - 1)) = winSite s (topClockSpan n) := by
    rw [winSite_next]
    have : topClockSpan n - 1 + 1 = topClockSpan n := by omega
    rw [this]
  have hcp : cellOf s (topFixedTraceNext ring C Y (winSite s (topClockSpan n - 1)))
      (topClockSpan n - 1) =
      (pair false true (cellOf s Y (topClockSpan n - 1)) { i := .e, c := .off }).1 := by
    rw [hag _ hp]
    unfold edgeStep
    rw [if_neg hnl]
    simp [setOne]
  have hdisj : ∀ j, j < topClockSpan n → j ≠ topClockSpan n - 1 →
      winSite s j ≠ winSite s (topClockSpan n - 1) ∧
        winSite s j ≠ ring.rightNeighbor (winSite s (topClockSpan n - 1)) := by
    intro j hj hjp
    refine ⟨fun h => hjp (winSite_inj hg.hn s j _ (by omega) (by omega) h), ?_⟩
    rw [hrn]
    intro h
    have := winSite_inj hg.hn s j (topClockSpan n) (by omega) (by omega) h
    omega
  have hflags : ∀ j, j < topClockSpan n →
      paFlagSettled s (topFixedTraceNext ring C Y (winSite s (topClockSpan n - 1))) τ j =
        puFlagsTerm (topClockSpan n) (cellOf s Y) (paFlagSettled s Y τ) j := by
    intro j hj
    apply Bool.eq_iff_iff.2
    unfold puFlagsTerm
    by_cases hjp : j = topClockSpan n - 1
    · subst hjp
      simp only [if_true, Bool.and_eq_true, paFlag_settled_site]
      rw [← hcp, cell_nonE_iff]
      constructor
      · rintro ⟨hj', hF⟩
        obtain ⟨hF1, hF2⟩ := (src_flag_settled ring C s Y _ τ hxl hyl hpost).1 hF
        exact ⟨⟨hj', hF1⟩, hF2⟩
      · rintro ⟨⟨hj', hF1⟩, hF2⟩
        exact ⟨hj', (src_flag_settled ring C s Y _ τ hxl hyl hpost).2 ⟨hF1, hF2⟩⟩
    · simp only [if_neg hjp, paFlag_settled_site]
      obtain ⟨hd1, hd2⟩ := hdisj j hj hjp
      rw [(away_flag_settled ring C s Y _ _ τ hd1 hd2 hpost).1]
  refine ⟨?_, hflags, ?_, ?_⟩
  · intro j hj
    rw [hag j hj]
    unfold edgeStep
    rw [if_neg hnl]
  · intro j hj hoj
    have hF : paFlagSettled s (topFixedTraceNext ring C Y (winSite s (topClockSpan n - 1))) τ j = true := by
      rw [hflags j hj]; exact hoj
    by_cases hjp : j = topClockSpan n - 1
    · have hF' := (paFlag_settled_site s τ _ j).1 hF
      rw [hjp] at hF'
      obtain ⟨_, hF2⟩ := hF'
      obtain ⟨_, j2, j3⟩ := src_link_settled ring C Y _ hxl hyl hF2.1
      rw [hjp, paLab_settled_site, paLab_settled_site]
      unfold SiteLabSettled
      rw [j2, j3]
    · obtain ⟨hd1, hd2⟩ := hdisj j hj hjp
      rw [paLab_settled_site, paLab_settled_site]
      exact (away_flag_settled ring C s Y _ _ τ hd1 hd2 hpost).2
  · unfold paQ
    rw [exportsAfter_step_away ring C s Y _ τ hb]

/-- **An edge off the window and off the port is the identity on the labelled window.**

Consumer: `bridge_step_settled`. -/
theorem frame_bridge_settled {n : Nat} (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (s : Fin n) (hg : WinGeo ring C s) (τ : Nat) (Y : TopFixedTraceState n) (e : Fin n)
    (hnw : ¬ ∃ p, p < topClockSpan n ∧ e = winSite s p)
    (hb : e ≠ certSite s (topClockSpan n - 1)) :
    ∃ c' o' ℓ' Q', PuStep (topClockSpan n) (cellOf s Y) (paFlagSettled s Y τ) (paLabSettled s Y) (paQ s Y τ)
        c' o' ℓ' Q' ∧
      PuAgree s (topFixedTraceNext ring C Y e) τ c' o' ℓ' Q' := by
  refine ⟨_, _, _, _, PuStep.frame, ?_⟩
  have hag := frame_cells ring C s hg Y e hnw hb
  have hpost0 := post_step_away ring C s Y e τ hb
  have hpost : PostIn ring C s Y e τ := fun v => hpost0 _
  refine ⟨hag, ?_, ?_, ?_⟩
  · intro j hj
    apply Bool.eq_iff_iff.2
    rw [paFlag_settled_site, paFlag_settled_site]
    obtain ⟨h1, h2⟩ := frame_sites ring hg.hn s e hnw hb j hj
    rw [(away_flag_settled ring C s Y e _ τ h1 h2 hpost).1]
  · intro j hj _
    obtain ⟨h1, h2⟩ := frame_sites ring hg.hn s e hnw hb j hj
    rw [paLab_settled_site, paLab_settled_site]
    exact (away_flag_settled ring C s Y e _ τ h1 h2 hpost).2
  · unfold paQ
    rw [exportsAfter_step_away ring C s Y e τ hb]

/-- **The port edge cleans or accepts the labelled packet.**  The accepted packet is the export
recorded in the same service: its operand is the label, and no other register changes its
post-anchor status, because the exported operand is the source output atom, which no input atom
equals (`Lin`).

Consumer: `bridge_step_settled`. -/
theorem port_bridge_settled {n : Nat} (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (s : Fin n) (hg : WinGeo ring C s) (τ : Nat) (Y : TopFixedTraceState n)
    (hreach : topClockReached ring C Y) (hτ : τ ≤ Y.1.2.clock) (hlin : Lin Y.1.2)
    (e : Fin n) (hb : e = certSite s (topClockSpan n - 1))
    (hnone : ∀ ex ∈ topClockConcreteExportsAfter s (topFixedTraceNext ring C Y e) τ,
      ex.operand ≠ none) :
    ∃ c' o' ℓ' Q', PuStep (topClockSpan n) (cellOf s Y) (paFlagSettled s Y τ) (paLabSettled s Y) (paQ s Y τ)
        c' o' ℓ' Q' ∧
      PuAgree s (topFixedTraceNext ring C Y e) τ c' o' ℓ' Q' := by
  have hn2 : 2 ≤ n := by have := hg.hn; omega
  have hr3 := span_ge_three hg.hn
  have hrn := span_lt_n hg.hn
  have hy : ring.rightNeighbor e = winSite s 0 := by
    rw [hb, rn_certSite]
    unfold winSite
    congr 1
    omega
  have hdst : ring.rightNeighbor e = certSite s (topClockSpan n) := by
    rw [hy]; rfl
  have hxl : (Y.1.1 e).l = false := agent_l ring C s hg Y hreach _
  have hyl : (Y.1.1 (ring.rightNeighbor e)).l = false := agent_l ring C s hg Y hreach _
  have hyb : (Y.1.1 (ring.rightNeighbor e)).beta = true := by
    rw [hy, agent_beta ring C Y hreach, winSite_beta ring C s hg.hbad 0 (by omega)]
    simp
  have hresp := siteCell_responder_terminal ring hn2 C Y e hxl hyl hyb
  rw [hy] at hresp
  have hresp' : cellOf s (topFixedTraceNext ring C Y e) 0 = portClean (cellOf s Y 0) ∨
      ∃ t, cellOf s (topFixedTraceNext ring C Y e) 0 = portAccept t (cellOf s Y 0) := hresp
  have hdisj0 : ∀ j, 0 < j → j < topClockSpan n →
      winSite s j ≠ e ∧ winSite s j ≠ ring.rightNeighbor e := by
    intro j h0 hj
    refine ⟨?_, ?_⟩
    · intro h
      rw [hb] at h
      unfold winSite at h
      have := certSite_inj_close s (topClockSpan n - 1) (topClockSpan n + j) (by omega)
        (by omega) h.symm
      omega
    · rw [hy]
      intro h
      have := winSite_inj hg.hn s j 0 (by omega) (by omega) h
      omega
  have haway : ∀ j, 0 < j → j < topClockSpan n →
      cellOf s (topFixedTraceNext ring C Y e) j = cellOf s Y j := by
    intro j h0 hj
    unfold cellOf
    exact siteCell_away ring C Y e _ (hdisj0 j h0 hj).1 (hdisj0 j h0 hj).2
  have hq := owner_qIn ring Y.1.1 e hxl hyl
  have hresp0 := topPortLiteralResponderFields ring hn2 C Y.1.1 e
  have hphys : (topFixedTraceNext ring C Y e).1.1 (ring.rightNeighbor e) =
      topFixedPublicNext ring C Y.1.1 e (ring.rightNeighbor e) := rfl
  have hq2 : ((topFixedTraceNext ring C Y e).1.1 (ring.rightNeighbor e)).qIn =
      (qiPhys (compileAdvice (ceilLogTwo n)) (Y.1.1 e) (Y.1.1 (ring.rightNeighbor e))).1.iY := by
    rw [hphys, hresp0.1, hq.2]
  rcases hR : (traceReplay ring Y e).exported with _ | ex
  · -- no packet is accepted
    have hpostAll := post_step_noexp ring C s Y e τ hR
    have hpost : PostIn ring C s Y e τ := fun v => hpostAll _
    have hkeep : tokNonE ((topFixedTraceNext ring C Y e).1.1 (ring.rightNeighbor e)).qIn = true →
        tokNonE (Y.1.1 (ring.rightNeighbor e)).qIn = true ∧
        puTok ((topFixedTraceNext ring C Y e).1.1 (ring.rightNeighbor e)).qIn =
          puTok (Y.1.1 (ring.rightNeighbor e)).qIn ∧
        ((topFixedTraceNext ring C Y e).1.2.current (ring.rightNeighbor e)).comparison.input =
          (Y.1.2.current (ring.rightNeighbor e)).comparison.input := by
      intro hP
      rcases resp_link_settled ring hn2 C Y e hxl hyl hP with ⟨d1, d2, d3⟩ | ⟨d1, _⟩ |
        ⟨d1, _, _, ex, hex, _⟩
      · exact ⟨d1, d2, d3⟩
      · rw [hyb] at d1; exact absurd d1 (by decide)
      · rw [hR] at hex; exact absurd hex (by simp)
    have hF0 : paFlagSettled s (topFixedTraceNext ring C Y e) τ 0 = true ↔
        (paFlagSettled s Y τ 0 = true ∧ puNonE (cellOf s (topFixedTraceNext ring C Y e) 0).i = true) := by
      rw [paFlag_settled_site, paFlag_settled_site, cell_nonE_iff]
      unfold FlagAtSettled
      rw [← hy]
      constructor
      · rintro ⟨h0, hP, hp⟩
        obtain ⟨d1, d2, d3⟩ := hkeep hP
        rw [d3] at hp
        exact ⟨⟨h0, d1, (hpost _).1 hp⟩, hP⟩
      · rintro ⟨⟨h0, d1', hp⟩, hP⟩
        obtain ⟨d1, d2, d3⟩ := hkeep hP
        rw [d3]
        exact ⟨h0, hP, (hpost _).2 hp⟩
    have hL0 : paFlagSettled s (topFixedTraceNext ring C Y e) τ 0 = true →
        paLabSettled s (topFixedTraceNext ring C Y e) 0 = paLabSettled s Y 0 := by
      intro hF
      have hF' := ((paFlag_settled_site s τ _ 0).1 hF).2
      unfold FlagAtSettled at hF'
      rw [← hy] at hF'
      obtain ⟨d1, d2, d3⟩ := hkeep hF'.1
      rw [paLab_settled_site, paLab_settled_site, ← hy]
      unfold SiteLabSettled
      rw [d2, d3]
    have hFj : ∀ j, 0 < j → j < topClockSpan n →
        paFlagSettled s (topFixedTraceNext ring C Y e) τ j = paFlagSettled s Y τ j := by
      intro j h0 hj
      apply Bool.eq_iff_iff.2
      rw [paFlag_settled_site, paFlag_settled_site]
      obtain ⟨hd1, hd2⟩ := hdisj0 j h0 hj
      rw [(away_flag_settled ring C s Y e _ τ hd1 hd2 hpost).1]
    have hLj : ∀ j, 0 < j → j < topClockSpan n →
        paLabSettled s (topFixedTraceNext ring C Y e) j = paLabSettled s Y j := by
      intro j h0 hj
      obtain ⟨hd1, hd2⟩ := hdisj0 j h0 hj
      rw [paLab_settled_site, paLab_settled_site]
      exact (away_flag_settled ring C s Y e _ τ hd1 hd2 hpost).2
    have hQ : paQ s (topFixedTraceNext ring C Y e) τ = paQ s Y τ := by
      unfold paQ
      rw [exportsAfter_step, hR]
      simp
    rcases hresp' with hc | ⟨t, hc⟩
    · refine ⟨_, _, _, _, PuStep.clean, ?_⟩
      have hflg : ∀ j, j < topClockSpan n →
          paFlagSettled s (topFixedTraceNext ring C Y e) τ j =
            (if j = 0 then paFlagSettled s Y τ 0 && puNonE (portClean (cellOf s Y 0)).i
              else paFlagSettled s Y τ j) := by
        intro j hj
        by_cases hj0 : j = 0
        · subst hj0
          simp only [if_true]
          apply Bool.eq_iff_iff.2
          rw [hF0, Bool.and_eq_true, ← hc]
        · simp only [if_neg hj0]
          exact hFj j (by omega) hj
      refine ⟨?_, hflg, ?_, hQ⟩
      · intro j hj
        by_cases hj0 : j = 0
        · subst hj0
          simp only [setOne, if_true]
          exact hc
        · simp only [setOne, if_neg hj0]
          exact haway j (by omega) hj
      · intro j hj hoj
        have hF : paFlagSettled s (topFixedTraceNext ring C Y e) τ j = true := by
          rw [hflg j hj]; exact hoj
        by_cases hj0 : j = 0
        · subst hj0
          exact hL0 hF
        · exact hLj j (by omega) hj
    · by_cases hemp : cellOf s Y 0 = { i := .e, c := .off }
      · exfalso
        have hnewP : puNonE (cellOf s (topFixedTraceNext ring C Y e) 0).i = true := by
          rw [hc]
          cases t <;> simp [portAccept, hemp, puNonE, Inp.isP, Inp.isS]
        rw [cell_nonE_iff, ← hy] at hnewP
        obtain ⟨d1, _, _⟩ := hkeep hnewP
        have : puNonE (cellOf s Y 0).i = true := by
          rw [cell_nonE_iff, ← hy]; exact d1
        rw [hemp] at this
        exact absurd this (by simp [puNonE, Inp.isP, Inp.isS])
      · have hca : cellOf s (topFixedTraceNext ring C Y e) 0 = cellOf s Y 0 := by
          rw [hc]
          unfold portAccept
          rw [if_neg hemp]
        refine ⟨_, _, _, _, PuStep.frame, ?_⟩
        have hflg : ∀ j, j < topClockSpan n →
            paFlagSettled s (topFixedTraceNext ring C Y e) τ j = paFlagSettled s Y τ j := by
          intro j hj
          by_cases hj0 : j = 0
          · subst hj0
            apply Bool.eq_iff_iff.2
            rw [hF0]
            constructor
            · rintro ⟨h, _⟩; exact h
            · intro h
              refine ⟨h, ?_⟩
              have hF' := ((paFlag_settled_site s τ _ 0).1 h).2
              unfold FlagAtSettled at hF'
              rw [hca, cell_nonE_iff]
              exact hF'.1
          · exact hFj j (by omega) hj
        refine ⟨?_, hflg, ?_, hQ⟩
        · intro j hj
          by_cases hj0 : j = 0
          · subst hj0; exact hca
          · exact haway j (by omega) hj
        · intro j hj hoj
          have hF : paFlagSettled s (topFixedTraceNext ring C Y e) τ j = true := by
            rw [hflg j hj]; exact hoj
          by_cases hj0 : j = 0
          · subst hj0
            exact hL0 hF
          · exact hLj j (by omega) hj
  · -- a packet is accepted
    have hnex : (traceReplay ring Y e).exported ≠ none := by rw [hR]; simp
    have hjoint := qi_joint (c := compileAdvice (ceilLogTwo n)) (Y.1.2.clock + 1) e
      (ring.rightNeighbor e) (Y.1.1 e) (Y.1.1 (ring.rightNeighbor e)) hxl hyl
      (Y.1.2.current e).comparison (Y.1.2.current (ring.rightNeighbor e)).comparison
    have hacc : (qiPhys (compileAdvice (ceilLogTwo n)) (Y.1.1 e)
        (Y.1.1 (ring.rightNeighbor e))).2 = true := hjoint.2.2.1 hnex
    obtain ⟨_, hyE, hyOFF, hiY⟩ := qi_acc _ _ hxl hyl hacc
    have hnewP : tokNonE ((topFixedTraceNext ring C Y e).1.1 (ring.rightNeighbor e)).qIn = true := by
      simp [hq2, hiY, tokNonE, InTok.isP]
    rcases resp_link_settled ring hn2 C Y e hxl hyl hnewP with ⟨d1, _⟩ | ⟨d1, _⟩ |
      ⟨_, _, _, ex', hex', hqIn, hinp, htime, hsrc, hdst'⟩
    · rw [hyE] at d1; simp [tokNonE, InTok.isP, InTok.isS] at d1
    · rw [hyb] at d1; exact absurd d1 (by decide)
    · have hee : ex = ex' := by
        rw [hR] at hex'
        exact Option.some.inj hex'
      rw [← hee] at hqIn hinp htime hsrc hdst'
      have hemp : cellOf s Y 0 = { i := .e, c := .off } := by
        have := siteCell_empty Y (ring.rightNeighbor e) hyE hyOFF
        rw [hy] at this
        exact this
      have hcond : τ < ex.time ∧ ex.source = certSite s (topClockSpan n - 1) ∧
          ex.destination = certSite s (topClockSpan n) :=
        ⟨by omega, by rw [hsrc, hb], by rw [hdst', hdst]⟩
      have hQex : topClockConcreteExportsAfter s (topFixedTraceNext ring C Y e) τ =
          topClockConcreteExportsAfter s Y τ ++ [ex] := by
        rw [exportsAfter_step, hR]
        simp [hcond]
      have hmem : ex ∈ topClockConcreteExportsAfter s (topFixedTraceNext ring C Y e) τ := by
        rw [hQex]; simp
      have hopne : ex.operand ≠ none := hnone ex hmem
      have hpost : PostIn ring C s Y e τ := post_step_in_acc ring C s Y e τ hlin ex hR hopne
      have hpacc : topClockPostAnchor s (topFixedTraceNext ring C Y e) τ ex.operand :=
        post_accept ring C s Y e τ hτ hb hdst ex hR htime hsrc hdst'
      have hcellP : puNonE (cellOf s (topFixedTraceNext ring C Y e) 0).i = true := by
        rw [cell_nonE_iff, ← hy]; exact hnewP
      have hFlag0 : paFlagSettled s (topFixedTraceNext ring C Y e) τ 0 = true := by
        rw [paFlag_settled_site]
        refine ⟨by omega, ?_⟩
        unfold FlagAtSettled
        rw [← hy]
        refine ⟨hnewP, ?_⟩
        rw [hinp]
        exact hpacc
      have hFj : ∀ j, 0 < j → j < topClockSpan n →
          paFlagSettled s (topFixedTraceNext ring C Y e) τ j = paFlagSettled s Y τ j := by
        intro j h0 hj
        apply Bool.eq_iff_iff.2
        rw [paFlag_settled_site, paFlag_settled_site]
        obtain ⟨hd1, hd2⟩ := hdisj0 j h0 hj
        rw [(away_flag_settled ring C s Y e _ τ hd1 hd2 hpost).1]
      have hLj : ∀ j, 0 < j → j < topClockSpan n →
          paLabSettled s (topFixedTraceNext ring C Y e) j = paLabSettled s Y j := by
        intro j h0 hj
        obtain ⟨hd1, hd2⟩ := hdisj0 j h0 hj
        rw [paLab_settled_site, paLab_settled_site]
        exact (away_flag_settled ring C s Y e _ τ hd1 hd2 hpost).2
      rcases hresp' with hc | ⟨t, hc⟩
      · exfalso
        rw [hc, hemp] at hcellP
        simp [portClean, puNonE, Inp.isP, Inp.isS] at hcellP
      · refine ⟨_, _, _, _, PuStep.accept t (ex.operand, InTok.P ex.value ex.tail) hemp, ?_⟩
        refine ⟨?_, ?_, ?_, ?_⟩
        · intro j hj
          by_cases hj0 : j = 0
          · subst hj0
            simp only [setOne, if_true]
            exact hc
          · simp only [setOne, if_neg hj0]
            exact haway j (by omega) hj
        · intro j hj
          by_cases hj0 : j = 0
          · subst hj0
            simp only [if_true]
            exact hFlag0
          · simp only [if_neg hj0]
            exact hFj j (by omega) hj
        · intro j hj hoj
          by_cases hj0 : j = 0
          · subst hj0
            show paLabSettled s (topFixedTraceNext ring C Y e) 0 = (ex.operand, InTok.P ex.value ex.tail)
            rw [paLab_settled_site, ← hy]
            unfold SiteLabSettled
            rw [hinp, hqIn]
            rfl
          · simp only [if_neg hj0]
            exact hLj j (by omega) hj
        · unfold paQ
          rw [hQex]
          simp

/-- **Every edge is an abstract labelled edge.**

Consumer: `linv_step`. -/
theorem bridge_step_settled {n : Nat} (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (s : Fin n) (hg : WinGeo ring C s) (τ : Nat) (Y : TopFixedTraceState n)
    (hreach : topClockReached ring C Y) (hτ : τ ≤ Y.1.2.clock) (e : Fin n)
    (hnone : ∀ ex ∈ topClockConcreteExportsAfter s (topFixedTraceNext ring C Y e) τ,
      ex.operand ≠ none) :
    ∃ c' o' ℓ' Q', PuStep (topClockSpan n) (cellOf s Y) (paFlagSettled s Y τ) (paLabSettled s Y) (paQ s Y τ)
        c' o' ℓ' Q' ∧
      PuAgree s (topFixedTraceNext ring C Y e) τ c' o' ℓ' Q' := by
  have hn2 : 2 ≤ n := by have := hg.hn; omega
  have hr3 := span_ge_three hg.hn
  by_cases ha : ∃ p, p < topClockSpan n ∧ e = winSite s p
  · obtain ⟨p, hp, rfl⟩ := ha
    by_cases hp1 : p + 1 < topClockSpan n
    · exact window_bridge_settled ring C s hg τ Y hreach p hp1
    · have hpe : p = topClockSpan n - 1 := by omega
      subst hpe
      exact term_bridge_settled ring C s hg τ Y hreach
  · by_cases hb : e = certSite s (topClockSpan n - 1)
    · exact port_bridge_settled ring C s hg τ Y hreach hτ (lin_reached ring C hn2 Y hreach) e hb hnone
    · exact frame_bridge_settled ring C s hg τ Y e ha hb


end MarkedCells
end L3

#print axioms L3.MarkedCells.window_bridge_settled
#print axioms L3.MarkedCells.term_bridge_settled
#print axioms L3.MarkedCells.port_bridge_settled
#print axioms L3.MarkedCells.frame_bridge_settled
#print axioms L3.MarkedCells.bridge_step_settled
