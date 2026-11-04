import Leader.L3.Top.SettledWorkSourceRows

/-!
# Q7 (P.8): the source block on the fixed trace, and the delivery of the next operand

The source block of a bad complete pair is the sites `certSite s j`, `j < r`.  On a reached
fixed trace state every edge acts on their output tokens as one step of the abstract source
block (`SrcStep`): an internal edge, the port edge (acceptance read from the border register
of the target window), or nothing.  Hence:

* `src_link_step`: every edge is a `SrcStep` of the abstract tokens;
* `topSettledSourceDeliver`: the source distance `dist` is at most `r + 1`, no edge raises it
  while it is positive, the edge of the last busy site lowers it by one, and when it is zero
  and the border register of the target window is empty and carry-free the port edge
  consumes the sampled token and creates the pending border input of the same tail flag.
  So a packet is accepted after at most `r + 1` source services and one port service, the
  paper's `r + 2`.

Consumer: the P.8--P.10 assembly `Leader/L3/TopSettledWorkPhase.lean` (not yet written): the
supply of the next pending operand when the target window holds none.
-/

namespace L3
namespace MarkedCells

set_option autoImplicit false

/-- The abstract output tokens of the source block.

Consumer: `src_link_step`. -/
def srcOf {n : Nat} (s : Fin n) (Z : TopFixedTraceState n) (j : Nat) : Tok :=
  absOut (Z.1.1 (certSite s j)).qOut

/-- The border register of the target window is empty and carry-free: the port accepts.

Consumer: `src_link_step`. -/
def accOf {n : Nat} (s : Fin n) (Z : TopFixedTraceState n) : Bool :=
  (Z.1.1 (winSite s 0)).qIn.isE && (Z.1.1 (winSite s 0)).qCarry.isOff

/-- Only the first source site is a marker.

Consumer: `src_link_step`. -/
theorem src_beta {n : Nat} (C : HeadlineConfiguration n) (s : Fin n)
    (hbad : HeadlineDigit.BadCompletePair C s) (j : Nat) (hj : j < topClockSpan n) :
    (C (certSite s j)).beta = decide (j = 0) := by
  by_cases h0 : j = 0
  · subst h0
    rw [certSite_zero]
    exact hbad.1.1
  · have hd : decide (j = 0) = false := by simp [h0]
    rw [hd]
    exact hbad.1.2.2.2.2.1 ⟨j, hj⟩ (by show 0 < j; omega)

/-- Source sites are distinct, and distinct from the border register of the target window.

Consumer: `src_link_step`. -/
theorem src_inj {n : Nat} (hn : 5 ≤ n) (s : Fin n) (a b : Nat)
    (ha : a ≤ topClockSpan n) (hb : b ≤ topClockSpan n)
    (h : certSite s a = certSite s b) : a = b := by
  have hr := span_lt_n hn
  rcases Nat.le_total a b with hab | hab
  · exact certSite_inj_close s a b hab (by omega) h
  · exact (certSite_inj_close s b a hab (by omega) h.symm).symm

/-- The output of the edge source, in the abstract tokens.

Consumer: `src_link_edge`. -/
theorem owner_source_out {n : Nat} (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (Z : TopFixedTraceState n) (e : Fin n)
    (hxl : (Z.1.1 e).l = false) (hyl : (Z.1.1 (ring.rightNeighbor e)).l = false) :
    ((topFixedTraceNext ring C Z e).1.1 e).qOut =
      (qoPhys (compileAdvice (ceilLogTwo n)) (Z.1.1 e) (Z.1.1 (ring.rightNeighbor e))).1 := by
  have h := (topPortLiteralSourceFields ring C Z.1.1 e).2.2
  change (topFixedPublicNext ring C Z.1.1 e e).qOut = _
  rw [h]
  unfold topPortLiteralTopOwner
  exact (liveTopPair_qOut _ _ _ _ _ hxl hyl).1

/-- The output of the edge responder, in the abstract tokens.

Consumer: `src_link_edge`, `src_link_away`. -/
theorem owner_resp_out {n : Nat} (ring : DirectedRing n) (hn : 2 ≤ n)
    (C : HeadlineConfiguration n) (Z : TopFixedTraceState n) (e : Fin n)
    (hxl : (Z.1.1 e).l = false) (hyl : (Z.1.1 (ring.rightNeighbor e)).l = false) :
    ((topFixedTraceNext ring C Z e).1.1 (ring.rightNeighbor e)).qOut =
      (qoPhys (compileAdvice (ceilLogTwo n)) (Z.1.1 e) (Z.1.1 (ring.rightNeighbor e))).2 := by
  have h := (topPortLiteralResponderFields ring hn C Z.1.1 e).2.2
  change (topFixedPublicNext ring C Z.1.1 e (ring.rightNeighbor e)).qOut = _
  rw [h]
  unfold topPortLiteralTopOwner
  exact (liveTopPair_qOut _ _ _ _ _ hxl hyl).2

/-- **The edge of source site `j` acts on the abstract tokens as `srcStepAt`.**

Consumer: `src_link_step`. -/
theorem src_link_edge {n : Nat} (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (s : Fin n) (Z : TopFixedTraceState n) (hg : WinGeo ring C s)
    (hreach : topClockReached ring C Z) (j : Nat) (hj : j < topClockSpan n) :
    ∀ i, i < topClockSpan n →
      srcOf s (topFixedTraceNext ring C Z (certSite s j)) i =
        srcStepAt (topClockSpan n) (accOf s Z) (srcOf s Z) j i := by
  intro i hi
  have hfrz := publicFrozen_reached ring C Z hreach
  have hn2 : 2 ≤ n := by have := hg.hn; omega
  have hr3 := span_ge_three hg.hn
  have hrn := span_lt_n hg.hn
  have hxl : (Z.1.1 (certSite s j)).l = false := by rw [(hfrz _).1]; exact hg.hl _
  have hyl : (Z.1.1 (ring.rightNeighbor (certSite s j))).l = false := by
    rw [(hfrz _).1]; exact hg.hl _
  have hbx : (Z.1.1 (certSite s j)).beta = decide (j = 0) := by
    rw [(hfrz _).2]; exact src_beta C s hg.hbad j hj
  have hrn_eq : ring.rightNeighbor (certSite s j) = certSite s (j + 1) := rn_certSite ring s j
  have hsrc := owner_source_out ring C Z (certSite s j) hxl hyl
  have hresp := owner_resp_out ring hn2 C Z (certSite s j) hxl hyl
  unfold srcOf
  by_cases hint : j + 1 < topClockSpan n
  · have hyb : (Z.1.1 (ring.rightNeighbor (certSite s j))).beta = false := by
      rw [hrn_eq, (hfrz _).2, src_beta C s hg.hbad (j + 1) hint]
      simp
    have hq := qo_link_internal (compileAdvice (ceilLogTwo n)) (Z.1.1 (certSite s j))
      (Z.1.1 (ring.rightNeighbor (certSite s j))) hyb
    rw [hbx] at hq
    rw [hrn_eq] at hq hresp hsrc
    by_cases hij : i = j
    · subst hij
      rw [srcStepAt_src _ _ _ _ hint, hsrc, hq.1]
    · by_cases hij1 : i = j + 1
      · subst hij1
        rw [srcStepAt_resp _ _ _ _ hint, hresp, hq.2]
      · rw [srcStepAt_far _ _ _ _ hint _ hij hij1]
        have h1 : certSite s i ≠ certSite s j := fun h =>
          hij (src_inj hg.hn s i j (by omega) (by omega) h)
        have h2 : certSite s i ≠ certSite s (j + 1) := fun h =>
          hij1 (src_inj hg.hn s i (j + 1) (by omega) (by omega) h)
        have haway := topPortLiteralAwayFields ring C Z.1.1 (certSite s j) (certSite s i) h1
          (by rw [hrn_eq]; exact h2)
        change absOut (topFixedPublicNext ring C Z.1.1 (certSite s j) (certSite s i)).qOut = _
        rw [haway.2.2]
  · have hjr : j + 1 = topClockSpan n := by omega
    have hy : ring.rightNeighbor (certSite s j) = winSite s 0 := by
      rw [hrn_eq]
      unfold winSite
      congr 1
    have hyb : (Z.1.1 (ring.rightNeighbor (certSite s j))).beta = true := by
      rw [hy, (hfrz _).2, winSite_beta ring C s hg.hbad 0 (by omega)]
      simp
    have hq := qo_link_marker (compileAdvice (ceilLogTwo n)) (Z.1.1 (certSite s j))
      (Z.1.1 (ring.rightNeighbor (certSite s j))) hxl hyl hyb
    have hj0 : decide (j = 0) = false := by
      have : j ≠ 0 := by omega
      simp [this]
    rw [hbx, hj0] at hq
    by_cases hij : i = j
    · subst hij
      rw [srcStepAt_portSrc _ _ _ _ hint, hsrc, hq.1, srcPair_marker_indep _ _ _ _ Tok.e]
      unfold accOf
      rw [hy]
    · rw [srcStepAt_portFar _ _ _ _ hint _ hij]
      have h1 : certSite s i ≠ certSite s j := fun h =>
        hij (src_inj hg.hn s i j (by omega) (by omega) h)
      have h2 : certSite s i ≠ ring.rightNeighbor (certSite s j) := by
        rw [hrn_eq]
        intro h
        have := src_inj hg.hn s i (j + 1) (by omega) (by omega) h
        omega
      have haway := topPortLiteralAwayFields ring C Z.1.1 (certSite s j) (certSite s i) h1 h2
      change absOut (topFixedPublicNext ring C Z.1.1 (certSite s j) (certSite s i)).qOut = _
      rw [haway.2.2]

/-- **An edge outside the source block, that is not its port, leaves its tokens alone.**

Consumer: `src_link_step`. -/
theorem src_link_away {n : Nat} (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (s : Fin n) (Z : TopFixedTraceState n) (hg : WinGeo ring C s)
    (hreach : topClockReached ring C Z) (e : Fin n)
    (he : ∀ j, j < topClockSpan n → e ≠ certSite s j) :
    ∀ i, i < topClockSpan n →
      srcOf s (topFixedTraceNext ring C Z e) i = srcOf s Z i := by
  intro i hi
  have hfrz := publicFrozen_reached ring C Z hreach
  have hn2 : 2 ≤ n := by have := hg.hn; omega
  have hr3 := span_ge_three hg.hn
  have hxl : (Z.1.1 e).l = false := by rw [(hfrz _).1]; exact hg.hl _
  have hyl : (Z.1.1 (ring.rightNeighbor e)).l = false := by
    rw [(hfrz _).1]; exact hg.hl _
  unfold srcOf
  have h1 : certSite s i ≠ e := fun h => he i hi h.symm
  by_cases h2 : certSite s i = ring.rightNeighbor e
  · -- the responder of the edge is the marker of the block
    have hi0 : i = 0 := by
      refine Classical.byContradiction fun hne => ?_
      apply he (i - 1) (by omega)
      apply certSite_pred ring s e (i - 1)
      have : i - 1 + 1 = i := by omega
      rw [this]
      exact h2.symm
    subst hi0
    have hyb : (Z.1.1 (ring.rightNeighbor e)).beta = true := by
      rw [← h2, (hfrz _).2, src_beta C s hg.hbad 0 hi]
      simp
    have hq := qo_link_marker (compileAdvice (ceilLogTwo n)) (Z.1.1 e)
      (Z.1.1 (ring.rightNeighbor e)) hxl hyl hyb
    have hresp := owner_resp_out ring hn2 C Z e hxl hyl
    rw [h2, hresp, hq.2]
  · have haway := topPortLiteralAwayFields ring C Z.1.1 e (certSite s i) h1 h2
    change absOut (topFixedPublicNext ring C Z.1.1 e (certSite s i)).qOut = _
    rw [haway.2.2]

/-- **Every edge acts on the source tokens as a step of the abstract source block.**

Consumer: `topSettledSourceDeliver`. -/
theorem src_link_step {n : Nat} (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (s : Fin n) (Z : TopFixedTraceState n) (hg : WinGeo ring C s)
    (hreach : topClockReached ring C Z) (e : Fin n) :
    ∃ src', SrcStep (topClockSpan n) (srcOf s Z) src' ∧
      ∀ i, i < topClockSpan n → srcOf s (topFixedTraceNext ring C Z e) i = src' i := by
  by_cases ha : ∃ j, j < topClockSpan n ∧ e = certSite s j
  · obtain ⟨j, hj, rfl⟩ := ha
    exact ⟨_, SrcStep.edge j hj (accOf s Z), src_link_edge ring C s Z hg hreach j hj⟩
  · refine ⟨srcOf s Z, SrcStep.frame, ?_⟩
    apply src_link_away ring C s Z hg hreach e
    intro j hj h
    exact ha ⟨j, hj, h⟩

/-- The border register of the target window after the port edge accepted a sampled token: the
pending input of the token's tail flag, with no carry.

Consumer: `topSettledSourceDeliver`. -/
theorem port_accept_link {n : Nat} (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (s : Fin n) (Z : TopFixedTraceState n) (hg : WinGeo ring C s)
    (hreach : topClockReached ring C Z)
    (v : Fin (compileAdvice (ceilLogTwo n)).topA) (t : Bool)
    (hD : (Z.1.1 (certSite s (topClockSpan n - 1))).qOut = .D v t) (hacc : accOf s Z = true) :
    cellOf s (topFixedTraceNext ring C Z (certSite s (topClockSpan n - 1))) 0 =
      { i := (if t then Inp.pt else Inp.pn), c := Car.off } := by
  have hfrz := publicFrozen_reached ring C Z hreach
  have hn2 : 2 ≤ n := by have := hg.hn; omega
  have hr3 := span_ge_three hg.hn
  obtain ⟨e, he⟩ : ∃ e, e = certSite s (topClockSpan n - 1) := ⟨_, rfl⟩
  rw [← he] at hD ⊢
  have hrn_eq : ring.rightNeighbor e = winSite s 0 := by
    rw [he, rn_certSite]
    unfold winSite
    congr 1
    omega
  have hxl : (Z.1.1 e).l = false := by rw [(hfrz _).1]; exact hg.hl _
  have hyl : (Z.1.1 (ring.rightNeighbor e)).l = false := by
    rw [(hfrz _).1]; exact hg.hl _
  have hyb : (Z.1.1 (ring.rightNeighbor e)).beta = true := by
    rw [hrn_eq, (hfrz _).2, winSite_beta ring C s hg.hbad 0 (by omega)]
    simp
  have haccy : (Z.1.1 (ring.rightNeighbor e)).qIn.isE = true ∧
      (Z.1.1 (ring.rightNeighbor e)).qCarry.isOff = true := by
    unfold accOf at hacc
    rw [← hrn_eq] at hacc
    simpa using hacc
  have hq := owner_qIn ring Z.1.1 e hxl hyl
  have hiY := qi_marker_accept (compileAdvice (ceilLogTwo n)) (Z.1.1 e)
    (Z.1.1 (ring.rightNeighbor e)) v t hxl hyl hyb hD haccy.1 haccy.2
  have hresp := topPortLiteralResponderFields ring hn2 C Z.1.1 e
  have hin : ((topFixedTraceNext ring C Z e).1.1 (ring.rightNeighbor e)).qIn = .P v t := by
    change (topFixedPublicNext ring C Z.1.1 e (ring.rightNeighbor e)).qIn = _
    rw [hresp.1, hq.2, hiY]
  have hoff : (siteCell Z (winSite s 0)).c = .off := by
    have := siteCell_offMatch Z (winSite s 0)
    unfold OffMatch at this
    apply this.2
    have h := haccy.2
    rw [hrn_eq] at h
    cases hk : (Z.1.1 (winSite s 0)).qCarry <;> simp [hk, QCarry.isOff] at h ⊢
  have hdis := siteCell_responder_terminal ring hn2 C Z e hxl hyl hyb
  rw [hrn_eq] at hdis hin
  have hc' : (siteCell (topFixedTraceNext ring C Z e) (winSite s 0)).c = .off := by
    rcases hdis with hc | ⟨t', hc⟩
    · rw [hc, portClean_c, hoff]
    · rw [hc, portAccept_c, hoff]
  have hi' : (siteCell (topFixedTraceNext ring C Z e) (winSite s 0)).i =
      (if t then Inp.pt else Inp.pn) := by
    show absIn ((topFixedTraceNext ring C Z e).1.1 (winSite s 0)).qIn = _
    rw [hin]
    cases t <;> simp [absIn]
  unfold cellOf
  cases hcell : siteCell (topFixedTraceNext ring C Z e) (winSite s 0) with
  | mk a b =>
    rw [hcell] at hc' hi'
    simp only at hc' hi'
    rw [hc', hi']

/-- The source terminal after the accepted offer: re-armed after a tail, empty after a non-tail.

Consumer: `topSettledSourceDeliver`. -/
theorem port_accept_source {n : Nat} (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (s : Fin n) (Z : TopFixedTraceState n) (hg : WinGeo ring C s)
    (hreach : topClockReached ring C Z)
    (v : Fin (compileAdvice (ceilLogTwo n)).topA) (t : Bool)
    (hD : (Z.1.1 (certSite s (topClockSpan n - 1))).qOut = .D v t) (hacc : accOf s Z = true) :
    srcOf s (topFixedTraceNext ring C Z (certSite s (topClockSpan n - 1)))
        (topClockSpan n - 1) = (if t then Tok.u else Tok.e) := by
  have hr3 := span_ge_three hg.hn
  have hl := src_link_edge ring C s Z hg hreach (topClockSpan n - 1) (by omega)
    (topClockSpan n - 1) (by omega)
  rw [hl, srcStepAt_portSrc _ _ _ _ (by omega), hacc]
  have hx : srcOf s Z (topClockSpan n - 1) = (if t then Tok.dt else Tok.dn) := by
    unfold srcOf; rw [hD]; cases t <;> simp [absOut]
  rw [hx]
  cases t <;> simp [srcPair, Tok.isD]

/-- **P.8: delivery of the next source operand.**  Let `d` be the source distance of a reached
state.  Then `d ≤ r + 1`; `d = 0` exactly when a sampled token stands at the source terminal; no
edge raises `d` while it is positive; the edge of the last busy site (the marker when the block is
empty) lowers it by one; and when `d = 0` and the border register of the target window is empty
and carry-free, the port edge consumes the token and leaves the pending border input of the
token's tail flag.  So a packet is accepted after at most `r + 1` source services and one port
service.

Consumer: `Leader/L3/TopSettledWorkPhase.lean` (not yet written): the source side of the
fill/consume accounting of P.8--P.10. -/
theorem topSettledSourceDeliver {n : Nat} (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (s : Fin n) (hg : WinGeo ring C s) :
    (∀ Z, topClockReached ring C Z → dist (topClockSpan n) (srcOf s Z) ≤ topClockSpan n + 1) ∧
    (∀ Z, topClockReached ring C Z →
      (dist (topClockSpan n) (srcOf s Z) = 0 ↔
        absOut (Z.1.1 (certSite s (topClockSpan n - 1))).qOut = .dn ∨
        absOut (Z.1.1 (certSite s (topClockSpan n - 1))).qOut = .dt)) ∧
    (∀ Z, topClockReached ring C Z → dist (topClockSpan n) (srcOf s Z) ≠ 0 → ∀ e,
      dist (topClockSpan n) (srcOf s (topFixedTraceNext ring C Z e)) ≤
        dist (topClockSpan n) (srcOf s Z)) ∧
    (∀ Z, topClockReached ring C Z → dist (topClockSpan n) (srcOf s Z) ≠ 0 →
      srcIdx (topClockSpan n) (srcOf s Z) < topClockSpan n ∧
      dist (topClockSpan n)
          (srcOf s (topFixedTraceNext ring C Z (certSite s (srcIdx (topClockSpan n) (srcOf s Z))))) + 1 ≤
        dist (topClockSpan n) (srcOf s Z)) ∧
    (∀ Z, topClockReached ring C Z → ∀ (v : Fin (compileAdvice (ceilLogTwo n)).topA) (t : Bool),
      (Z.1.1 (certSite s (topClockSpan n - 1))).qOut = .D v t → accOf s Z = true →
      cellOf s (topFixedTraceNext ring C Z (certSite s (topClockSpan n - 1))) 0 =
        { i := (if t then Inp.pt else Inp.pn), c := Car.off } ∧
      srcOf s (topFixedTraceNext ring C Z (certSite s (topClockSpan n - 1)))
        (topClockSpan n - 1) = (if t then Tok.u else Tok.e)) := by
  have hr3 := span_ge_three hg.hn
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro Z _
    exact dist_le _ _
  · intro Z _
    rw [dist_zero_iff _ (by omega)]
    unfold srcOf
    cases ho : (Z.1.1 (certSite s (topClockSpan n - 1))).qOut with
    | E => simp [absOut, Tok.isD]
    | U => simp [absOut, Tok.isD]
    | D v t => cases t <;> simp [absOut, Tok.isD]
  · intro Z hreach hd e
    obtain ⟨src', hstep, hag⟩ := src_link_step ring C s Z hg hreach e
    have hle := dist_step_le _ hr3 _ _ hstep hd
    have heq : dist (topClockSpan n) (srcOf s (topFixedTraceNext ring C Z e)) =
        dist (topClockSpan n) src' := dist_congr _ _ _ hag
    rw [heq]; exact hle
  · intro Z hreach hd
    obtain ⟨hidx, hdrop⟩ := dist_step_drop (topClockSpan n) hr3 (srcOf s Z) (accOf s Z) hd
    refine ⟨hidx, ?_⟩
    have heq := dist_congr (topClockSpan n)
      (srcOf s (topFixedTraceNext ring C Z (certSite s (srcIdx (topClockSpan n) (srcOf s Z)))))
      (srcStepAt (topClockSpan n) (accOf s Z) (srcOf s Z) (srcIdx (topClockSpan n) (srcOf s Z)))
      (src_link_edge ring C s Z hg hreach _ hidx)
    rw [heq]; exact hdrop
  · intro Z hreach v t hD hacc
    exact ⟨port_accept_link ring C s Z hg hreach v t hD hacc,
      port_accept_source ring C s Z hg hreach v t hD hacc⟩

end MarkedCells
end L3

#print axioms L3.MarkedCells.src_link_step
#print axioms L3.MarkedCells.port_accept_link
#print axioms L3.MarkedCells.port_accept_source
#print axioms L3.MarkedCells.topSettledSourceDeliver
