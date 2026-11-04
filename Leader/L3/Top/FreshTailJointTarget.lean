import Leader.L3.Top.FreshTailTicketRows

/-!
Q7c P.3 J4 target half:
the raw P.2 target potential W = topPortPotential on EVERY actual
fixed-public edge of the reached trace, not only at a port-ready cut.

* a selected edge that is not the free-border offer row never raises W
  (untouched, target-internal, target-terminal and blocked-border rows);
* the free-border offer row with an OLD source E or U frames W and
  records no comparison export (the previously unhandled row);
* the free-border offer row with an OLD source D raises W by exactly
  r+2 and the physical port receipt count by exactly one;
* when the target border is blocked, the P.2 frontier edge lowers W.

The P.2 touched-row bounds in TopPortPhase.lean are stated without the
ready-port premise but are private there; `jointport%` names them
(the accessor pattern of HeadlineRenewalCleanSmall.lean), so they are
reused, not re-proved.
-/

namespace L3

open Classical

set_option autoImplicit false
set_option Elab.async false

open Lean Elab Term Meta in
/-- `jointport% "name"` elaborates to the private declaration `L3.name`
of `TopPortPhase.lean`. Consumer: the J4 target rows of this file
(topFreshTailJointTargetUntouchedAndInternalBound and
topFreshTailJointBlockedPortFrontierDrop). -/
elab "jointport% " s:str : term => do
  let nm : Name :=
    (((`_private.Leader.L3.Top.PortPhase).num 0).str "L3").str s.getString
  mkConstWithFreshMVarLevels nm

/-- Section 6 item 1. On a reached cut, every actual edge other
than the OLD free-border offer row leaves the raw target potential
nonincreasing: untouched edges frame it, target-internal and
last-site-to-outside rows and the blocked border row obey the P.2
first-match pair bounds. No port-ready packet is assumed.
Consumer: topFreshTailJointHistoryReserveStep (I.target, J4 all-edge
drift). -/
theorem topFreshTailJointTargetUntouchedAndInternalBound
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hbad : HeadlineDigit.BadCompletePair C s)
    (Z : TopFixedTraceState n)
    (hreach : topClockReached ring C Z)
    (e : Fin n)
    (hnotoffer : ¬ topPortReadyOfferFirstMatch ring s Z e) :
    topPortPotential s (topFixedTraceNext ring C Z e) ≤
      topPortPotential s Z := by
  have hspan : 3 ≤ topClockSpan n := (jointport% "topPortSpanThreeAll") n
  have hle := topPortSpanLeOfBad C s hbad
  have hn2 : 2 ≤ n := by omega
  have hlocal : (jointport% "topPortPairLocalBound") ring s Z e := by
    by_cases htouched : ∃ j : Fin (topClockSpan n),
        certSite s (topClockSpan n + j.val) = e ∨
        certSite s (topClockSpan n + j.val) = ring.rightNeighbor e
    · rcases (jointport% "topPortTouchedShape") ring s e htouched with
        ⟨j, hnext, hsource, htarget⟩ | hlast | hborder
      · exact (jointport% "topPortInternalTouchedBound") ring C s hbad Z
          hreach e j hnext hsource htarget
      · by_cases hb : ring.rightNeighbor e = certSite s (topClockSpan n)
        · exact (jointport% "topPortBorderTouchedBound") ring C s hbad Z
            hreach e hnotoffer hb
        · exact (jointport% "topPortLastSourceOutsideBound") ring C s hbad Z
            hreach e hlast hb
      · exact (jointport% "topPortBorderTouchedBound") ring C s hbad Z
          hreach e hnotoffer hborder
    · exact topPortUntouchedPairBound ring s Z e
        (fun j hj => htouched ⟨j, Or.inl hj⟩)
        (fun j hj => htouched ⟨j, Or.inr hj⟩)
  have heq := (jointport% "topPortOldPairAfterWeight_eq") ring hn2 C s Z e
  have hcover := topPortSelectedEdgeCover ring C s hbad e
  have hframe : ∀ j : Fin (topClockSpan n),
      j ≠ (jointport% "topPortIndexAtSite") s e →
      j ≠ (jointport% "topPortIndexAtSite") s (ring.rightNeighbor e) →
      topPortWeightAt s (topFixedTraceNext ring C Z e) j =
        topPortWeightAt s Z j := by
    intro j hji hjk
    apply topPortWeightAtAway
    · intro he
      rcases hcover j (Or.inl he) with h | h
      · exact hji h
      · exact hjk h
    · intro he
      rcases hcover j (Or.inr he) with h | h
      · exact hji h
      · exact hjk h
  have hl : (if (jointport% "topPortIndexAtSite") s e =
        (jointport% "topPortIndexAtSite") s (ring.rightNeighbor e) then
      (jointport% "topPortOldPairAfterWeight") ring s Z e
          ((jointport% "topPortIndexAtSite") s e) ≤
        topPortWeightAt s Z ((jointport% "topPortIndexAtSite") s e)
    else
      (jointport% "topPortOldPairAfterWeight") ring s Z e
          ((jointport% "topPortIndexAtSite") s e) +
        (jointport% "topPortOldPairAfterWeight") ring s Z e
          ((jointport% "topPortIndexAtSite") s (ring.rightNeighbor e)) ≤
        topPortWeightAt s Z ((jointport% "topPortIndexAtSite") s e) +
        topPortWeightAt s Z
          ((jointport% "topPortIndexAtSite") s (ring.rightNeighbor e))) := hlocal
  rw [topPortPotentialAsSum, topPortPotentialAsSum]
  apply topPortSumTwoLe _ _ _ _ hframe
  rw [heq, heq]
  by_cases hik : (jointport% "topPortIndexAtSite") s e =
      (jointport% "topPortIndexAtSite") s (ring.rightNeighbor e)
  · rw [if_pos hik] at hl
    rw [if_pos hik, if_pos hik]
    exact hl
  · rw [if_neg hik] at hl
    rw [if_neg hik, if_neg hik]
    exact hl

/-- Section 6 item 5. If the OLD target border is not E/OFF, the
P.2 frontier edge topPortFrontierEdge strictly lowers the raw target
potential; this needs no port-ready source packet.
Consumer: topFreshTailJointNominatedDrop (blocked-terminal row, J4). -/
theorem topFreshTailJointBlockedPortFrontierDrop
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hbad : HeadlineDigit.BadCompletePair C s)
    (Z : TopFixedTraceState n)
    (hreach : topClockReached ring C Z)
    (hblocked : ¬ ((Z.1.1 (certSite s (topClockSpan n))).qIn = .E ∧
      (Z.1.1 (certSite s (topClockSpan n))).qCarry = .OFF)) :
    topPortPotential s
        (topFixedTraceNext ring C Z (topPortFrontierEdge s Z)) + 1 ≤
      topPortPotential s Z := by
  have hr : 3 ≤ topClockSpan n := (jointport% "topPortSpanThreeAll") n
  simp only [topPortFrontierEdge, if_neg hblocked]
  have hj : (jointport% "topPortRightmost") s Z (topClockSpan n) <
      topClockSpan n :=
    (jointport% "topPortRightmostLt") s Z (topClockSpan n) (by omega)
  have hactive : 0 < (jointport% "topPortRightmost") s Z (topClockSpan n) →
      (jointport% "topPortMobileAt") s Z
        ((jointport% "topPortRightmost") s Z (topClockSpan n)) = true := by
    intro hpos
    rcases (jointport% "topPortRightmostActiveOrZero") s Z (topClockSpan n)
      with hz | hm
    · omega
    · exact hm
  by_cases hnext :
      (jointport% "topPortRightmost") s Z (topClockSpan n) + 1 <
        topClockSpan n
  · have hpassive := (jointport% "topPortRightmostNextPassive") s Z
      (topClockSpan n) hnext
    apply (jointport% "topPortInternalFrontierDrop") ring C s hbad Z hreach
      (certSite s (topClockSpan n +
        (jointport% "topPortRightmost") s Z (topClockSpan n)))
      (⟨(jointport% "topPortRightmost") s Z (topClockSpan n), hj⟩ :
        Fin (topClockSpan n))
      hnext rfl
    · rw [topFreshTailTicketNeighborSite]
      congr 1 <;> omega
    · exact hblocked
    · intro hpositive
      exact hactive hpositive
    · exact hpassive
  · have hlast : (jointport% "topPortRightmost") s Z (topClockSpan n) =
        topClockSpan n - 1 := by omega
    apply (jointport% "topPortTerminalFrontierDrop") ring C s hbad Z hreach
      (certSite s (topClockSpan n +
        (jointport% "topPortRightmost") s Z (topClockSpan n)))
    · rw [hlast]
    · exact hblocked
    · rw [← hlast]
      exact hactive (by omega)

/-- LIVE-TOP owner at a beta-marked responder with OLD input E and
carry OFF: the responder carry stays OFF whatever the initiator holds
(qTerminal blocks every QC hand-off into the border).
Consumer: topFreshTailJointBorderAfter. -/
theorem topFreshTailJointOwnerBorderCarry
    (c : Compiled) (x y : Agent c) (rx ry : Bool)
    (hxl : x.l = false) (hyl : y.l = false) (hyb : y.beta = true)
    (hyi : y.qIn = .E) (hyc : y.qCarry = .OFF) :
    (liveTopPair c x y rx ry).y.qCarry = .OFF := by
  cases hxo : x.qOut <;> cases hxi : x.qIn <;> cases hxc : x.qCarry <;>
    simp [liveTopPair, hxl, hyl, hyb, hxo, hyi, hyc, hxi, hxc,
      QCarry.isOff, QCarry.isL, InTok.isS, InTok.isE,
      InTok.isX, InTok.isP, OutTok.isD, OutTok.isE, OutTok.isU,
      outT, outV, topTerminal, topInternal, topBorder] <;>
    (try split) <;> (try split) <;> (try split) <;> simp_all

/-- LIVE-TOP owner at a beta-marked responder with OLD input E and
carry OFF: if the initiator output is not D, the responder input stays
E (the QI P-move cannot enter a terminal, and acceptQO reads the OLD
output). Consumer: topFreshTailJointBorderAfter (free/nonready row). -/
theorem topFreshTailJointOwnerBorderUnread
    (c : Compiled) (x y : Agent c) (rx ry : Bool)
    (hxl : x.l = false) (hyl : y.l = false) (hyb : y.beta = true)
    (hxd : x.qOut.isD = false)
    (hyi : y.qIn = .E) (hyc : y.qCarry = .OFF) :
    (liveTopPair c x y rx ry).y.qIn = .E := by
  cases hxo : x.qOut <;> rw [hxo] at hxd <;> simp [OutTok.isD] at hxd <;>
    cases hxi : x.qIn <;> cases hxc : x.qCarry <;>
    simp [liveTopPair, hxl, hyl, hyb, hxo, hyi, hyc, hxi, hxc,
      QCarry.isOff, QCarry.isL, InTok.isS, InTok.isE,
      InTok.isX, InTok.isP, OutTok.isD, OutTok.isE, OutTok.isU,
      outT, outV, topTerminal, topInternal, topBorder] <;>
    (try split) <;> (try split) <;> (try split) <;> simp_all

/-- The source-terminal-to-border edge at an OLD border E/OFF: the NEW
border carry is OFF, and the NEW border input is still E unless the
OLD source output is D.
Consumer: topFreshTailJointFreePortUnreadFrame and
topFreshTailJointPortAcceptedTargetBirth. -/
theorem topFreshTailJointBorderAfter
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hn : 5 ≤ n)
    (hbad : HeadlineDigit.BadCompletePair C s)
    (Z : TopFixedTraceState n)
    (hreach : topClockReached ring C Z)
    (e : Fin n)
    (hsite : e = certSite s (topClockSpan n - 1))
    (hyi : (Z.1.1 (certSite s (topClockSpan n))).qIn = .E)
    (hyc : (Z.1.1 (certSite s (topClockSpan n))).qCarry = .OFF) :
    ((topFixedTraceNext ring C Z e).1.1
        (certSite s (topClockSpan n))).qCarry = .OFF ∧
    ((Z.1.1 (certSite s (topClockSpan n - 1))).qOut.isD = false →
      ((topFixedTraceNext ring C Z e).1.1
        (certSite s (topClockSpan n))).qIn = .E) := by
  have hr := cert_rho_ge_three n hn
  change 3 ≤ topClockSpan n at hr
  have hgeo := topFreshTailCausalSourcePublicGeometry
    ring C s hn hbad Z hreach ⟨topClockSpan n - 1, by omega⟩
  have hnb : ring.rightNeighbor e = certSite s (topClockSpan n) := by
    rw [hsite, topFreshTailTicketNeighborSite]
    congr 1
    omega
  have hxl : (Z.1.1 e).l = false := by rw [hsite]; exact hgeo.1
  have hyl : (Z.1.1 (ring.rightNeighbor e)).l = false := by
    rw [hsite]; exact hgeo.2.1
  have hyb : (Z.1.1 (ring.rightNeighbor e)).beta = true := by
    rw [hsite]
    have h := hgeo.2.2.2
    have hsucc : topClockSpan n - 1 + 1 = topClockSpan n := by omega
    simp only [hsucc, if_true] at h
    exact h
  have hresp := topPortLiteralResponderFields ring (by omega) C Z.1.1 e
  rw [← hnb] at hyi hyc ⊢
  refine ⟨?_, ?_⟩
  · change (topFixedPublicNext ring C Z.1.1 e
      (ring.rightNeighbor e)).qCarry = .OFF
    rw [hresp.2.1]
    unfold topPortLiteralTopOwner
    exact topFreshTailJointOwnerBorderCarry _ _ _ _ _ hxl hyl hyb hyi hyc
  · intro hd
    rw [← hsite] at hd
    change (topFixedPublicNext ring C Z.1.1 e
      (ring.rightNeighbor e)).qIn = .E
    rw [hresp.1]
    unfold topPortLiteralTopOwner
    exact topFreshTailJointOwnerBorderUnread _ _ _ _ _ hxl hyl hyb hd hyi hyc

/-- On the source-terminal edge every target offset other than the
border keeps its weight (the source terminal is never a target site
because r < n). Consumer: topFreshTailJointPortWeightBalance. -/
theorem topFreshTailJointPortOthersFrame
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hn : 5 ≤ n)
    (Z : TopFixedTraceState n) (e : Fin n)
    (hsite : e = certSite s (topClockSpan n - 1))
    (j : Fin (topClockSpan n)) (hj : j.val ≠ 0) :
    topPortWeightAt s (topFixedTraceNext ring C Z e) j =
      topPortWeightAt s Z j := by
  have hr := cert_rho_ge_three n hn
  change 3 ≤ topClockSpan n at hr
  have hlt := MarkedCells.span_lt_n hn
  have hjl := j.isLt
  apply topPortWeightAtAway
  · intro h
    rw [hsite] at h
    have := MarkedCells.certSite_inj_close s (topClockSpan n - 1)
      (topClockSpan n + j.val) (by omega) (by omega) h.symm
    omega
  · intro h
    rw [hsite, topFreshTailTicketNeighborSite] at h
    have h' : certSite s (topClockSpan n - 1 + 1) =
        certSite s (topClockSpan n) := by
      congr 1
      omega
    rw [h'] at h
    have := MarkedCells.certSite_inj_close s (topClockSpan n)
      (topClockSpan n + j.val) (by omega) (by omega) h.symm
    omega

/-- On the source-terminal edge the raw target potential changes only
through the border weight. Consumer: topFreshTailJointFreePortUnreadFrame
and topFreshTailJointPortAcceptedTargetBirth. -/
theorem topFreshTailJointPortWeightBalance
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hn : 5 ≤ n)
    (Z : TopFixedTraceState n) (e : Fin n)
    (hsite : e = certSite s (topClockSpan n - 1)) :
    topPortPotential s (topFixedTraceNext ring C Z e) +
        topPortSiteWeight (topClockSpan n) 0
          (Z.1.1 (certSite s (topClockSpan n))).qIn
          (Z.1.1 (certSite s (topClockSpan n))).qCarry =
      topPortPotential s Z +
        topPortSiteWeight (topClockSpan n) 0
          ((topFixedTraceNext ring C Z e).1.1 (certSite s (topClockSpan n))).qIn
          ((topFixedTraceNext ring C Z e).1.1
            (certSite s (topClockSpan n))).qCarry := by
  have hr := cert_rho_ge_three n hn
  change 3 ≤ topClockSpan n at hr
  let zero : Fin (topClockSpan n) := ⟨0, by omega⟩
  have hframe : ∀ j : Fin (topClockSpan n), j ≠ zero → j ≠ zero →
      topPortWeightAt s (topFixedTraceNext ring C Z e) j =
        topPortWeightAt s Z j := by
    intro j hj _
    apply topFreshTailJointPortOthersFrame ring C s hn Z e hsite j
    intro h0
    apply hj
    exact Fin.ext h0
  have hswap := topPortSumTwoSwap (topPortWeightAt s Z)
    (topPortWeightAt s (topFixedTraceNext ring C Z e)) zero zero hframe
  simp only [if_true] at hswap
  rw [topPortPotentialAsSum, topPortPotentialAsSum]
  have h0 : ∀ Y : TopFixedTraceState n, topPortWeightAt s Y zero =
      topPortSiteWeight (topClockSpan n) 0
        (Y.1.1 (certSite s (topClockSpan n))).qIn
        (Y.1.1 (certSite s (topClockSpan n))).qCarry := by
    intro Y
    unfold topPortWeightAt
    rfl
  rw [← h0 Z, ← h0 (topFixedTraceNext ring C Z e)]
  exact hswap

/-- A genealogy port event happens only on the source-terminal edge,
from an OLD D, into an OLD free border.
Consumer: topFreshTailJointHistoryReserveStep and
topFreshTailJointNominatedDrop. -/
theorem topFreshTailJointExportFree
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hn : 5 ≤ n)
    (hbad : HeadlineDigit.BadCompletePair C s)
    (Z : TopFixedTraceState n)
    (hreach : topClockReached ring C Z)
    (e : Fin n)
    (x : DigitExport (compileAdvice (ceilLogTwo n)) n)
    (hevent : topFreshTailGenealogyPortExport ring C s Z e = some x) :
    e = certSite s (topClockSpan n - 1) ∧
    (∃ (v : Fin (compileAdvice (ceilLogTwo n)).topA) (t : Bool),
      (Z.1.1 (certSite s (topClockSpan n - 1))).qOut = .D v t) ∧
    (Z.1.1 (certSite s (topClockSpan n))).qIn = .E ∧
    (Z.1.1 (certSite s (topClockSpan n))).qCarry = .OFF := by
  obtain ⟨hsite, v, t, hD⟩ :=
    topFreshTailTicketPortExportSource ring C s Z e x hevent
  have hxo : (Z.1.1 e).qOut = .D v t := by rw [hsite]; exact hD
  have hport := topFreshTailTicketPortRow ring C s hn hbad Z hreach e
    hsite v t hxo
  have hguard := hport.2.2.1.1 ⟨x, hevent⟩
  rw [hport.1] at hguard
  exact ⟨hsite, ⟨v, t, hD⟩, hguard.1, hguard.2⟩

/-- Section 6 item 2 (the formerly missing free/nonready row).
At the source-terminal edge with OLD border E/OFF and OLD source E or
U, the NEW border stays E/OFF, no comparison port export is recorded,
the receipt count and the raw target potential are unchanged, and an
OLD terminal U samples into D without same-edge acceptance.
Consumer: topFreshTailJointHistoryReserveStep (I.target/J2). -/
theorem topFreshTailJointFreePortUnreadFrame
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hn : 5 ≤ n)
    (hbad : HeadlineDigit.BadCompletePair C s)
    (Z : TopFixedTraceState n)
    (hreach : topClockReached ring C Z)
    (e : Fin n)
    (hsite : e = certSite s (topClockSpan n - 1))
    (hyi : (Z.1.1 (certSite s (topClockSpan n))).qIn = .E)
    (hyc : (Z.1.1 (certSite s (topClockSpan n))).qCarry = .OFF)
    (hxd : (Z.1.1 (certSite s (topClockSpan n - 1))).qOut.isD = false) :
    ((topFixedTraceNext ring C Z e).1.1 (certSite s (topClockSpan n))).qIn = .E ∧
    ((topFixedTraceNext ring C Z e).1.1
      (certSite s (topClockSpan n))).qCarry = .OFF ∧
    topFreshTailGenealogyPortExport ring C s Z e = none ∧
    topFreshTailPortReceiptCount s (topFixedTraceNext ring C Z e) =
      topFreshTailPortReceiptCount s Z ∧
    topPortPotential s (topFixedTraceNext ring C Z e) = topPortPotential s Z ∧
    ((Z.1.1 (certSite s (topClockSpan n - 1))).qOut = .U →
      ∃ (v : Fin (compileAdvice (ceilLogTwo n)).topA) (t : Bool),
        ((topFixedTraceNext ring C Z e).1.1
          (certSite s (topClockSpan n - 1))).qOut = .D v t) := by
  have hr := cert_rho_ge_three n hn
  change 3 ≤ topClockSpan n at hr
  have hafter := topFreshTailJointBorderAfter ring C s hn hbad Z hreach e hsite hyi hyc
  have hqin := hafter.2 hxd
  have hnone : topFreshTailGenealogyPortExport ring C s Z e = none := by
    cases hx : topFreshTailGenealogyPortExport ring C s Z e with
    | none => rfl
    | some x =>
        obtain ⟨_, ⟨v, t, hD⟩, _, _⟩ :=
          topFreshTailJointExportFree ring C s hn hbad Z hreach e x hx
        rw [hD] at hxd
        cases hxd
  have hcount := topFreshTailTicketReceiptCountStep ring C s Z e
  rw [hnone] at hcount
  have hbal := topFreshTailJointPortWeightBalance ring C s hn Z e hsite
  rw [hyi, hyc, hqin, hafter.1] at hbal
  refine ⟨hqin, hafter.1, hnone, ?_, ?_, ?_⟩
  · rw [hcount]
    rfl
  · omega
  · intro hU
    have hgeo := topFreshTailCausalSourcePublicGeometry
      ring C s hn hbad Z hreach ⟨topClockSpan n - 1, by omega⟩
    have hxl : (Z.1.1 e).l = false := by rw [hsite]; exact hgeo.1
    have hyl : (Z.1.1 (ring.rightNeighbor e)).l = false := by
      rw [hsite]; exact hgeo.2.1
    have hu := topFreshTailFifoUnreadSamples ring C Z e hxl hyl
      (by rw [hsite]; exact hU)
    rw [← hsite]
    exact ⟨_, _, hu⟩

/-- Section 6 item 3 (voucher release). At the source-terminal
edge with OLD border E/OFF and OLD source D v t, the source departs,
the border receives P v t with carry OFF, exactly one comparison port
export (operand: the OLD source comparison atom) is recorded, the
receipt count grows by one, and the raw target potential grows by
exactly r+2 (topPortWeightAcceptedBirth).
Consumer: topFreshTailJointHistoryReserveStep (I.receipt/I.target). -/
theorem topFreshTailJointPortAcceptedTargetBirth
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hn : 5 ≤ n)
    (hbad : HeadlineDigit.BadCompletePair C s)
    (Z : TopFixedTraceState n)
    (hreach : topClockReached ring C Z)
    (e : Fin n)
    (hsite : e = certSite s (topClockSpan n - 1))
    (hyi : (Z.1.1 (certSite s (topClockSpan n))).qIn = .E)
    (hyc : (Z.1.1 (certSite s (topClockSpan n))).qCarry = .OFF)
    (v : Fin (compileAdvice (ceilLogTwo n)).topA) (t : Bool)
    (hxo : (Z.1.1 (certSite s (topClockSpan n - 1))).qOut = .D v t) :
    ((topFixedTraceNext ring C Z e).1.1
      (certSite s (topClockSpan n - 1))).qOut = (if t then .U else .E) ∧
    ((topFixedTraceNext ring C Z e).1.1 (certSite s (topClockSpan n))).qIn =
      .P v t ∧
    ((topFixedTraceNext ring C Z e).1.1
      (certSite s (topClockSpan n))).qCarry = .OFF ∧
    (∃ x : DigitExport (compileAdvice (ceilLogTwo n)) n,
      topFreshTailGenealogyPortExport ring C s Z e = some x ∧
      x.operand = (Z.1.2.current
        (certSite s (topClockSpan n - 1))).comparison.out.atom) ∧
    topFreshTailPortReceiptCount s (topFixedTraceNext ring C Z e) =
      topFreshTailPortReceiptCount s Z + 1 ∧
    topPortPotential s (topFixedTraceNext ring C Z e) =
      topPortPotential s Z + (topClockSpan n + 2) := by
  have hr := cert_rho_ge_three n hn
  change 3 ≤ topClockSpan n at hr
  have hxo' : (Z.1.1 e).qOut = .D v t := by rw [hsite]; exact hxo
  have hport := topFreshTailTicketPortRow ring C s hn hbad Z hreach e hsite v t hxo'
  have hnb := hport.1
  have hafter := topFreshTailJointBorderAfter ring C s hn hbad Z hreach e hsite hyi hyc
  have hyi' : (Z.1.1 (ring.rightNeighbor e)).qIn = .E := by rw [hnb]; exact hyi
  have hyc' : (Z.1.1 (ring.rightNeighbor e)).qCarry = .OFF := by rw [hnb]; exact hyc
  have hqin := hport.2.2.2 hyi' hyc'
  rw [hnb] at hqin
  have hout := hport.2.1
  rw [hyi', hyc'] at hout
  simp only [InTok.isE, QCarry.isOff, Bool.and_self, if_true] at hout
  obtain ⟨x, hx⟩ := hport.2.2.1.2 ⟨hyi', hyc'⟩
  have hframe := topFreshTailAuditSelectedPortFrame ring C s Z e x hx
  have hcount := topFreshTailTicketReceiptCountStep ring C s Z e
  rw [hx] at hcount
  have hbal := topFreshTailJointPortWeightBalance ring C s hn Z e hsite
  rw [hyi, hyc, hqin, hafter.1, topPortWeightAcceptedBirth] at hbal
  have hzero : topPortSiteWeight (topClockSpan n) 0
      (InTok.E : InTok (compileAdvice (ceilLogTwo n)).topA) QCarry.OFF = 0 := by
    simp [topPortSiteWeight, topPortInputWeight, topPortCarryWeight]
  rw [hzero] at hbal
  refine ⟨?_, hqin, hafter.1, ⟨x, hx, ?_⟩, ?_, ?_⟩
  · rw [← hsite]; exact hout
  · rw [hframe.2.2.2.2.2.2.2.1, hsite]
  · rw [hcount]
    rfl
  · omega

end L3

#print axioms L3.topFreshTailJointTargetUntouchedAndInternalBound
#print axioms L3.topFreshTailJointBlockedPortFrontierDrop
#print axioms L3.topFreshTailJointOwnerBorderCarry
#print axioms L3.topFreshTailJointOwnerBorderUnread
#print axioms L3.topFreshTailJointBorderAfter
#print axioms L3.topFreshTailJointPortOthersFrame
#print axioms L3.topFreshTailJointPortWeightBalance
#print axioms L3.topFreshTailJointExportFree
#print axioms L3.topFreshTailJointFreePortUnreadFrame
#print axioms L3.topFreshTailJointPortAcceptedTargetBirth
