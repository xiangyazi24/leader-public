import Leader.L3.Top.PinnedPhaseFillReal

/-!
# Q7 (P.12 preparation, lemma 3, concrete layer): the port letter

The port edge records an export exactly when a sampled token stands at the source terminal and the
border register of the window is empty and carry-free.  In that case the border register receives
the packet and the source terminal is re-armed; otherwise the window and the accepted queue are
unchanged.

Consumer: `Leader/L3/Top/PinnedPhaseFillCost.lean`.
-/

namespace L3
namespace MarkedCells

open Classical
set_option autoImplicit false
set_option linter.unusedSimpArgs false

/-- The token of an output has the sampled-token test of the output.

Consumer: `port_acc_iff`. -/
theorem absOut_isD {a : Nat} (o : OutTok a) : (absOut o).isD = o.isD := by
  cases o with
  | E => rfl
  | U => rfl
  | D v t => cases t <;> rfl

/-- The right neighbour of the port site is the border register.

Consumer: `port_acc_iff`, `real_port_clean`, `real_port_accept`. -/
theorem port_next_site {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n) (s : Fin n) :
    ring.rightNeighbor (certSite s (topClockSpan n - 1)) = winSite s 0 := by
  have hr3 := span_ge_three hn
  rw [rn_certSite]
  unfold winSite
  congr 1
  omega

/-- **The port edge records an export exactly when a sampled token stands at the terminal and the
border register accepts.**

Consumer: `real_port_clean`, `real_port_accept`. -/
theorem port_acc_iff {n : Nat} (ring : DirectedRing n) (C : HeadlineConfiguration n) (s : Fin n)
    (hg : WinGeo ring C s) (Y : TopFixedTraceState n) (hreach : topClockReached ring C Y) :
    (traceReplay ring Y (certSite s (topClockSpan n - 1))).exported ≠ none ↔
      ((srcOf s Y (topClockSpan n - 1)).isD = true ∧ accOf s Y = true) := by
  have hr3 := span_ge_three hg.hn
  obtain ⟨e, he⟩ : ∃ e, e = certSite s (topClockSpan n - 1) := ⟨_, rfl⟩
  rw [← he]
  have hy : ring.rightNeighbor e = winSite s 0 := by rw [he]; exact port_next_site ring hg.hn s
  have hxl : (Y.1.1 e).l = false := agent_l ring C s hg Y hreach _
  have hyl : (Y.1.1 (ring.rightNeighbor e)).l = false := agent_l ring C s hg Y hreach _
  have hyb : (Y.1.1 (ring.rightNeighbor e)).beta = true := by
    rw [hy, agent_beta ring C Y hreach, winSite_beta ring C s hg.hbad 0 (by omega)]
    simp
  have hjoint := qi_joint (c := compileAdvice (ceilLogTwo n)) (Y.1.2.clock + 1) e
    (ring.rightNeighbor e) (Y.1.1 e) (Y.1.1 (ring.rightNeighbor e)) hxl hyl
    (Y.1.2.current e).comparison (Y.1.2.current (ring.rightNeighbor e)).comparison
  have h2 := qi_acc_marker (compileAdvice (ceilLogTwo n)) (Y.1.1 e) (Y.1.1 (ring.rightNeighbor e))
    hxl hyl hyb
  have hsrc : (srcOf s Y (topClockSpan n - 1)).isD = (Y.1.1 e).qOut.isD := by
    unfold srcOf
    rw [← he]
    exact absOut_isD _
  have hacc : accOf s Y = ((Y.1.1 (ring.rightNeighbor e)).qIn.isE &&
      (Y.1.1 (ring.rightNeighbor e)).qCarry.isOff) := by
    unfold accOf
    rw [hy]
  rw [hsrc, hacc]
  constructor
  · intro hex
    have := hjoint.2.2.1 hex
    rw [h2] at this
    simpa [Bool.and_assoc] using this
  · intro h
    apply hjoint.2.2.2
    rw [h2]
    simpa [Bool.and_assoc] using h

/-- **The port letter that does not accept.**

Consumer: `fill_concrete_step`. -/
theorem real_port_clean {n : Nat} (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (s : Fin n) (hg : WinGeo ring C s) (Z : TopFixedTraceState n)
    (hreach : topClockReached ring C Z) (τ : Nat)
    (hs : FillShape (topClockSpan n) (cellOf s Z))
    (hnot : ¬ ((srcOf s Z (topClockSpan n - 1)).isD = true ∧ accOf s Z = true)) :
    Realized ring C s τ Z (certSite s (topClockSpan n - 1))
      (setOne (cellOf s Z) 0 (portClean (cellOf s Z 0)))
      (srcStepAt (topClockSpan n) (accOf s Z) (srcOf s Z) (topClockSpan n - 1))
      (aOf s Z τ) := by
  have hn2 : 2 ≤ n := by have := hg.hn; omega
  have hr3 := span_ge_three hg.hn
  obtain ⟨e, he⟩ : ∃ e, e = certSite s (topClockSpan n - 1) := ⟨_, rfl⟩
  have hy : ring.rightNeighbor e = winSite s 0 := by rw [he]; exact port_next_site ring hg.hn s
  have hxl : (Z.1.1 e).l = false := agent_l ring C s hg Z hreach _
  have hyl : (Z.1.1 (ring.rightNeighbor e)).l = false := agent_l ring C s hg Z hreach _
  have hyb : (Z.1.1 (ring.rightNeighbor e)).beta = true := by
    rw [hy, agent_beta ring C Z hreach, winSite_beta ring C s hg.hbad 0 (by omega)]
    simp
  have hR : (traceReplay ring Z e).exported = none := by
    apply Classical.byContradiction
    intro hh
    apply hnot
    have := (port_acc_iff ring C s hg Z hreach).1 (by rw [← he]; exact hh)
    exact this
  have hk0 := fill_kind hs 0 (by omega)
  have hresp := siteCell_responder_terminal ring hn2 C Z e hxl hyl hyb
  rw [hy] at hresp
  have hresp' : cellOf s (topFixedTraceNext ring C Z e) 0 = portClean (cellOf s Z 0) ∨
      ∃ t, cellOf s (topFixedTraceNext ring C Z e) 0 = portAccept t (cellOf s Z 0) := hresp
  have hc0 : cellOf s (topFixedTraceNext ring C Z e) 0 = cellOf s Z 0 := by
    rcases hresp' with hc | ⟨t, hc⟩
    · rw [hc]; exact pu_port_clean _ hk0.1
    · by_cases hemp : cellOf s Z 0 = { i := .e, c := .off }
      · exfalso
        have hnewP : (cellOf s (topFixedTraceNext ring C Z e) 0).i.isP = true := by
          rw [hc, hemp]; cases t <;> simp [portAccept, Inp.isP]
        rw [cell_isP_iff, ← hy] at hnewP
        have hq := owner_qIn ring Z.1.1 e hxl hyl
        have hresp0 := topPortLiteralResponderFields ring hn2 C Z.1.1 e
        have hphys : (topFixedTraceNext ring C Z e).1.1 (ring.rightNeighbor e) =
            topFixedPublicNext ring C Z.1.1 e (ring.rightNeighbor e) := rfl
        have hq2 : ((topFixedTraceNext ring C Z e).1.1 (ring.rightNeighbor e)).qIn =
            (qiPhys (compileAdvice (ceilLogTwo n)) (Z.1.1 e)
              (Z.1.1 (ring.rightNeighbor e))).1.iY := by
          rw [hphys, hresp0.1, hq.2]
        have hjoint := qi_joint (c := compileAdvice (ceilLogTwo n)) (Z.1.2.clock + 1) e
          (ring.rightNeighbor e) (Z.1.1 e) (Z.1.1 (ring.rightNeighbor e)) hxl hyl
          (Z.1.2.current e).comparison (Z.1.2.current (ring.rightNeighbor e)).comparison
        have hiYP : (qiPhys (compileAdvice (ceilLogTwo n)) (Z.1.1 e)
            (Z.1.1 (ring.rightNeighbor e))).1.iY.isP = true := by
          rw [← hq2]; exact hnewP
        rcases hjoint.2.1 hiYP with ⟨hyP, _⟩ | ⟨hb0, _⟩ | ⟨_, _, _, hacc2, _⟩
        · have : (cellOf s Z 0).i.isP = true := by rw [cell_isP_iff, ← hy]; exact hyP
          rw [hemp] at this
          simp [Inp.isP] at this
        · rw [hyb] at hb0; exact absurd hb0 (by decide)
        · have hex : (traceReplay ring Z e).exported ≠ none := hjoint.2.2.2 hacc2
          rw [hR] at hex
          exact hex rfl
      · rw [hc]; unfold portAccept; rw [if_neg hemp]
  have hdisj : ∀ j, 0 < j → j < topClockSpan n →
      winSite s j ≠ e ∧ winSite s j ≠ ring.rightNeighbor e := by
    intro j h0 hj
    refine ⟨?_, ?_⟩
    · intro h
      rw [he] at h
      exact win_ne_port hg.hn s j hj h
    · rw [hy]
      intro h
      have := winSite_inj hg.hn s j 0 (by omega) (by omega) h
      omega
  have haway : ∀ j, 0 < j → j < topClockSpan n →
      cellOf s (topFixedTraceNext ring C Z e) j = cellOf s Z j := by
    intro j h0 hj
    unfold cellOf
    exact siteCell_away ring C Z e _ (hdisj j h0 hj).1 (hdisj j h0 hj).2
  have hcells : ∀ j, j < topClockSpan n →
      cellOf s (topFixedTraceNext ring C Z e) j =
        setOne (cellOf s Z) 0 (portClean (cellOf s Z 0)) j := by
    intro j hj
    by_cases hj0 : j = 0
    · subst hj0
      simp only [setOne, if_true]
      rw [hc0, pu_port_clean _ hk0.1]
    · simp only [setOne, if_neg hj0]
      exact haway j (by omega) hj
  have hcells' : ∀ j, j < topClockSpan n →
      cellOf s (topFixedTraceNext ring C Z e) j = cellOf s Z j := by
    intro j hj
    by_cases hj0 : j = 0
    · subst hj0; exact hc0
    · exact haway j (by omega) hj
  rw [he] at hcells hcells' hR
  refine ⟨hcells, src_link_edge ring C s Z hg hreach (topClockSpan n - 1) (by omega), ?_⟩
  unfold aOf
  have hQ : paQ s (topFixedTraceNext ring C Z (certSite s (topClockSpan n - 1))) τ = paQ s Z τ := by
    unfold paQ
    rw [exportsAfter_step, hR]
    simp
  rw [hQ, fcnt_congr _ _ _ hcells']

/-- **The port letter that accepts a packet.**

Consumer: `fill_concrete_step`. -/
theorem real_port_accept {n : Nat} (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (s : Fin n) (hg : WinGeo ring C s) (Z : TopFixedTraceState n)
    (hreach : topClockReached ring C Z) (τ : Nat) (hτ : τ ≤ Z.1.2.clock)
    (anchor : DigitExport (compileAdvice (ceilLogTwo n)) n) (hanch : anchor.time = τ)
    (hpureN : topClockConcretePureStream s
      (topFixedTraceNext ring C Z (certSite s (topClockSpan n - 1))) anchor)
    (hle : fcnt (topClockSpan n) (cellOf s Z) ≤ (paQ s Z τ).length)
    (hD : (srcOf s Z (topClockSpan n - 1)).isD = true) (hacc : accOf s Z = true) :
    cellOf s Z 0 = { i := .e, c := .off } ∧
    ∃ t : Bool,
      t = decide ((aOf s Z τ + fcnt (topClockSpan n) (cellOf s Z)) % topClockSpan n =
        topClockSpan n - 1) ∧
      Realized ring C s τ Z (certSite s (topClockSpan n - 1))
        (setOne (cellOf s Z) 0 (portAccept t (cellOf s Z 0)))
        (srcStepAt (topClockSpan n) true (srcOf s Z) (topClockSpan n - 1)) (aOf s Z τ) := by
  have hn2 : 2 ≤ n := by have := hg.hn; omega
  have hr3 := span_ge_three hg.hn
  obtain ⟨e, he⟩ : ∃ e, e = certSite s (topClockSpan n - 1) := ⟨_, rfl⟩
  have hy : ring.rightNeighbor e = winSite s 0 := by rw [he]; exact port_next_site ring hg.hn s
  have hdst : ring.rightNeighbor e = certSite s (topClockSpan n) := by rw [hy]; rfl
  have hxl : (Z.1.1 e).l = false := agent_l ring C s hg Z hreach _
  have hyl : (Z.1.1 (ring.rightNeighbor e)).l = false := agent_l ring C s hg Z hreach _
  have hyb : (Z.1.1 (ring.rightNeighbor e)).beta = true := by
    rw [hy, agent_beta ring C Z hreach, winSite_beta ring C s hg.hbad 0 (by omega)]
    simp
  -- the token at the terminal
  obtain ⟨v, t, hDq⟩ : ∃ v t, (Z.1.1 (certSite s (topClockSpan n - 1))).qOut = .D v t := by
    unfold srcOf at hD
    rcases hq : (Z.1.1 (certSite s (topClockSpan n - 1))).qOut with _ | _ | ⟨v, t⟩
    · rw [hq] at hD; simp [absOut, Tok.isD] at hD
    · rw [hq] at hD; simp [absOut, Tok.isD] at hD
    · exact ⟨v, t, rfl⟩
  have hexp : (traceReplay ring Z e).exported ≠ none := by
    rw [he]; exact (port_acc_iff ring C s hg Z hreach).2 ⟨hD, hacc⟩
  obtain ⟨ex, hR⟩ : ∃ ex, (traceReplay ring Z e).exported = some ex := by
    rcases hh : (traceReplay ring Z e).exported with _ | ex
    · rw [hh] at hexp; exact absurd rfl hexp
    · exact ⟨ex, rfl⟩
  have hjoint := qi_joint (c := compileAdvice (ceilLogTwo n)) (Z.1.2.clock + 1) e
    (ring.rightNeighbor e) (Z.1.1 e) (Z.1.1 (ring.rightNeighbor e)) hxl hyl
    (Z.1.2.current e).comparison (Z.1.2.current (ring.rightNeighbor e)).comparison
  have hacc2 := hjoint.2.2.1 hexp
  obtain ⟨_, hyE, hyOFF, _⟩ := qi_acc _ _ hxl hyl hacc2
  have hemp : cellOf s Z 0 = { i := .e, c := .off } := by
    have := siteCell_empty Z (ring.rightNeighbor e) hyE hyOFF
    rw [hy] at this
    exact this
  have hlink := port_accept_link ring C s Z hg hreach v t hDq hacc
  have hdisj : ∀ j, 0 < j → j < topClockSpan n →
      winSite s j ≠ e ∧ winSite s j ≠ ring.rightNeighbor e := by
    intro j h0 hj
    refine ⟨?_, ?_⟩
    · intro h
      rw [he] at h
      exact win_ne_port hg.hn s j hj h
    · rw [hy]
      intro h
      have := winSite_inj hg.hn s j 0 (by omega) (by omega) h
      omega
  have haway : ∀ j, 0 < j → j < topClockSpan n →
      cellOf s (topFixedTraceNext ring C Z e) j = cellOf s Z j := by
    intro j h0 hj
    unfold cellOf
    exact siteCell_away ring C Z e _ (hdisj j h0 hj).1 (hdisj j h0 hj).2
  have hpa : portAccept t (cellOf s Z 0) = { i := (if t then Inp.pt else Inp.pn), c := Car.off } := by
    unfold portAccept; rw [if_pos hemp]
  have hcells : ∀ j, j < topClockSpan n →
      cellOf s (topFixedTraceNext ring C Z e) j =
        setOne (cellOf s Z) 0 (portAccept t (cellOf s Z 0)) j := by
    intro j hj
    by_cases hj0 : j = 0
    · subst hj0
      simp only [setOne, if_true]
      rw [hpa, ← he] at *
      exact hlink
    · simp only [setOne, if_neg hj0]
      exact haway j (by omega) hj
  -- the accepted queue
  obtain ⟨hf1, hf2, hf3, hf4, hf5, hf6, hf7⟩ :=
    replay_exported_fields (c := compileAdvice (ceilLogTwo n)) .comparison (Z.1.2.clock + 1) e
      (ring.rightNeighbor e)
      (digitLaneView .comparison (ProjD.ofAgent (Z.1.1 e)) (Z.1.1 e).beta)
      (digitLaneView .comparison (ProjD.ofAgent (Z.1.1 (ring.rightNeighbor e)))
        (Z.1.1 (ring.rightNeighbor e)).beta)
      (Z.1.2.current e).comparison (Z.1.2.current (ring.rightNeighbor e)).comparison ex hR
  have hcond : τ < ex.time ∧ ex.source = certSite s (topClockSpan n - 1) ∧
      ex.destination = certSite s (topClockSpan n) :=
    ⟨by omega, by rw [hf1, he], by rw [hf2, hdst]⟩
  have hQex : topClockConcreteExportsAfter s (topFixedTraceNext ring C Z e) τ =
      topClockConcreteExportsAfter s Z τ ++ [ex] := by
    rw [exportsAfter_step, hR]
    simp [hcond]
  have hQ : paQ s (topFixedTraceNext ring C Z e) τ =
      paQ s Z τ ++ [(ex.operand, InTok.P ex.value ex.tail)] := by
    unfold paQ
    rw [hQex]
    simp
  -- the tail bit
  have hexl : (topClockConcreteExportsAfter s Z τ).length = (paQ s Z τ).length := by
    unfold paQ; simp
  rw [← he] at hpureN
  have hlenN : (topClockConcreteExportsAfter s (topFixedTraceNext ring C Z e) anchor.time).length =
      (paQ s Z τ).length + 1 := by
    rw [hanch, hQex]; simp [hexl]
  have hidx : (paQ s Z τ).length <
      (topClockConcreteExportsAfter s (topFixedTraceNext ring C Z e) anchor.time).length := by
    rw [hlenN]; omega
  obtain ⟨sample, _, _, _, htail, _, _, htl⟩ := hpureN ⟨(paQ s Z τ).length, hidx⟩
  have hexget : topClockConcreteExportAt s (topFixedTraceNext ring C Z e) anchor.time
      ⟨(paQ s Z τ).length, hidx⟩ = ex := by
    show (topClockConcreteExportsAfter s (topFixedTraceNext ring C Z e) anchor.time)[(paQ s Z τ).length]'hidx = ex
    have h1 : (topClockConcreteExportsAfter s (topFixedTraceNext ring C Z e) anchor.time) =
        topClockConcreteExportsAfter s Z τ ++ [ex] := by rw [hanch]; exact hQex
    simp only [h1]
    rw [List.getElem_append_right (by omega)]
    simp [hexl]
  rw [hexget] at htl
  have hDe : (Z.1.1 e).qOut = .D v t := by rw [he]; exact hDq
  have htE : ex.tail = t := by
    rw [hf6]
    simp [digitLaneView, ProjD.ofAgent, hDe, outT]
  have htfin : t = decide ((aOf s Z τ + fcnt (topClockSpan n) (cellOf s Z)) % topClockSpan n =
      topClockSpan n - 1) := by
    have h1 : (aOf s Z τ + fcnt (topClockSpan n) (cellOf s Z)) % topClockSpan n =
        (paQ s Z τ).length % topClockSpan n := by
      unfold aOf
      rw [Nat.mod_add_mod]
      congr 1
      omega
    rw [h1, ← htE, htl, htail]
    by_cases hh : (paQ s Z τ).length % topClockSpan n = topClockSpan n - 1 <;> simp [hh]
  rw [← he]
  refine ⟨hemp, t, htfin, hcells, ?_, ?_⟩
  · have := src_link_edge ring C s Z hg hreach (topClockSpan n - 1) (by omega)
    rw [hacc, ← he] at this
    intro i hi
    exact this i hi
  · have hfc : fcnt (topClockSpan n) (cellOf s (topFixedTraceNext ring C Z e)) =
        fcnt (topClockSpan n) (cellOf s Z) + 1 := by
      rw [fcnt_congr _ _ _ hcells]
      have := (accept_counts (topClockSpan n) (by omega) (cellOf s Z) t hemp).1
      rw [hpa] at *
      exact this
    unfold aOf
    rw [hQ, hfc]
    simp only [List.length_append, List.length_singleton]
    have : (paQ s Z τ).length + 1 - (fcnt (topClockSpan n) (cellOf s Z) + 1) =
        (paQ s Z τ).length - fcnt (topClockSpan n) (cellOf s Z) := by omega
    rw [this]

end MarkedCells
end L3

#print axioms L3.MarkedCells.port_acc_iff
#print axioms L3.MarkedCells.real_port_clean
#print axioms L3.MarkedCells.real_port_accept
