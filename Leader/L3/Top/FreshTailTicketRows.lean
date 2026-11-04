import Leader.L3.Top.FreshTailFrameOrder

/-!
Q7c P.3 J3: literal port rows used by the visit-ticket
injection. Every statement is about the actual liveTopPair owner,
the actual digitLaneReplay comparison lane, or the actual
fixed-public trace; nothing here is a ghost assumption.
-/

namespace L3

open Classical

set_option autoImplicit false
set_option Elab.async false

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 12000 in
/-- Owner row of a beta-marked port with an OLD source D: the source
departs exactly when the responder input is E and its carry is OFF;
the source's own input and carry lanes are irrelevant.
Consumer: topFreshTailTicketPortDeparture (J3 port row). -/
theorem topFreshTailTicketOwnerPortOut
    (c : Compiled) (x y : Agent c)
    (resolvedX resolvedY : Bool)
    (v : Fin c.topA) (tail : Bool)
    (hxl : x.l = false) (hyl : y.l = false)
    (hyb : y.beta = true)
    (hxo : x.qOut = .D v tail) :
    (liveTopPair c x y resolvedX resolvedY).x.qOut =
      (if y.qIn.isE && y.qCarry.isOff then
        (if tail then .U else .E) else .D v tail) := by
  cases hyi : y.qIn <;> cases hyc : y.qCarry <;>
    cases hxi : x.qIn <;> cases hxc : x.qCarry <;>
    simp [liveTopPair, hxl, hyl, hyb, hxo, hyi, hyc, hxi, hxc,
      QCarry.isOff, QCarry.isL, InTok.isS, InTok.isE,
      InTok.isX, InTok.isP, OutTok.isD, OutTok.isE, OutTok.isU,
      outT, outV, topTerminal, topInternal, topBorder] <;>
    (try split) <;> (try split) <;> (try split) <;> simp_all

/-- The same owner row delivers the OLD source D payload to the
responder input on acceptance. Consumer: the genuine-tail
identification in topFreshTailTicketFreshExportGenuine (J3). -/
theorem topFreshTailTicketOwnerPortInput
    (c : Compiled) (x y : Agent c)
    (resolvedX resolvedY : Bool)
    (v : Fin c.topA) (tail : Bool)
    (hxl : x.l = false) (hyl : y.l = false)
    (hyb : y.beta = true)
    (hxo : x.qOut = .D v tail)
    (hyi : y.qIn = .E) (hyc : y.qCarry = .OFF) :
    (liveTopPair c x y resolvedX resolvedY).y.qIn = .P v tail := by
  cases hxi : x.qIn <;> cases hxc : x.qCarry <;>
    simp [liveTopPair, hxl, hyl, hyb, hxo, hyi, hyc, hxi, hxc,
      QCarry.isOff, QCarry.isL, InTok.isS, InTok.isE,
      InTok.isX, InTok.isP, OutTok.isD, OutTok.isE, OutTok.isU,
      outT, outV, topTerminal, topInternal, topBorder] <;>
    (try split) <;> (try split) <;> (try split) <;> simp_all

/-- The comparison lane records an export on a marked port with an
OLD D exactly under the same responder guards.
Consumer: topFreshTailTicketPortExportIff (J2/J3 bridge). -/
theorem topFreshTailTicketLaneExportIff
    {c : Compiled} {n : Nat}
    (stamp : Nat) (source destination : Fin n)
    (x y : DigitLaneView c)
    (gx gy : DigitLaneGhost c n)
    (v : Fin c.topA) (tail : Bool)
    (hxl : x.leader = false) (hyl : y.leader = false)
    (hym : y.marker = true)
    (hxo : x.out = .D v tail) :
    (digitLaneReplay .comparison stamp source destination
      x y gx gy).exported ≠ none ↔
      (y.input.isE = true ∧ y.carryLive = false) := by
  cases hyi : y.input <;> cases hyc : y.carryLive <;>
    cases hxi : x.input <;> cases hxc : x.carryLive <;>
    cases hxm : x.marker <;>
    simp [digitLaneReplay, hxl, hyl, hym, hxo, hyi, hyc, hxi, hxc, hxm,
      InTok.isS, InTok.isE, InTok.isX, InTok.isP, OutTok.isD,
      OutTok.isE, OutTok.isU, inT] <;>
    (try split) <;> (try split) <;> (try split) <;> simp_all

/-- Successor arithmetic of the nominated certificate block.
Consumer: every J3 move row (the Genealogy copy is private). -/
theorem topFreshTailTicketNeighborSite
    {n : Nat} (ring : DirectedRing n) (s : Fin n) (k : Nat) :
    ring.rightNeighbor (certSite s k) = certSite s (k + 1) := by
  apply Fin.ext
  change ((s.val + k) % n + 1) % n = (s.val + (k + 1)) % n
  calc
    ((s.val + k) % n + 1) % n = (s.val + k + 1) % n :=
      Nat.mod_add_mod (s.val + k) n 1
    _ = (s.val + (k + 1)) % n := by congr 1

/-- Physical row census of one source output slot on one actual
fixed-public edge: the slot is unchanged, bootstraps at the border,
samples, departs, receives a moved D from its predecessor, or (only
at offset zero, from a leader predecessor) is cleared.
Consumer: topFreshTailTicketSlotCases (J3 all-row induction). -/
theorem topFreshTailTicketSlotPhysical
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hn : 5 ≤ n)
    (hbad : HeadlineDigit.BadCompletePair C s)
    (Z : TopFixedTraceState n)
    (hreach : topClockReached ring C Z)
    (e : Fin n) (j : Fin (topClockSpan n)) :
    ((topFixedTraceNext ring C Z e).1.1 (certSite s j.val)).qOut =
        (Z.1.1 (certSite s j.val)).qOut ∨
    (e = certSite s j.val ∧ (Z.1.1 (certSite s j.val)).qOut = .E ∧
      j.val = 0 ∧
      ((topFixedTraceNext ring C Z e).1.1 (certSite s j.val)).qOut = .U) ∨
    (e = certSite s j.val ∧ (Z.1.1 (certSite s j.val)).qOut = .U ∧
      ((topFixedTraceNext ring C Z e).1.1 (certSite s j.val)).qOut =
        .D (Z.1.1 e).d (if j.val = 0 then true else false)) ∨
    (e = certSite s j.val ∧
      ∃ (v : Fin (compileAdvice (ceilLogTwo n)).topA) (t : Bool),
        (Z.1.1 (certSite s j.val)).qOut = .D v t ∧
        ((topFixedTraceNext ring C Z e).1.1 (certSite s j.val)).qOut =
          (if t then .U else .E)) ∨
    (0 < j.val ∧ e = certSite s (j.val - 1) ∧
      (Z.1.1 (certSite s j.val)).qOut = .E ∧
      ∃ (v : Fin (compileAdvice (ceilLogTwo n)).topA) (t : Bool),
        (Z.1.1 (certSite s (j.val - 1))).qOut = .D v t ∧
        ((topFixedTraceNext ring C Z e).1.1 (certSite s j.val)).qOut =
          .D v t) ∨
    (j.val = 0 ∧
      ((topFixedTraceNext ring C Z e).1.1 (certSite s j.val)).qOut = .E) := by
  have hqueue := topFreshTailCloseReachedQueue ring C s hn hbad Z hreach
  have hgeo := topFreshTailCausalSourcePublicGeometry
    ring C s hn hbad Z hreach j
  by_cases hsrc : e = certSite s j.val
  · have hxl : (Z.1.1 e).l = false := by rw [hsrc]; exact hgeo.1
    have hyl : (Z.1.1 (ring.rightNeighbor e)).l = false := by
      rw [hsrc]; exact hgeo.2.1
    cases ho : (Z.1.1 (certSite s j.val)).qOut with
    | E =>
        by_cases hj : j.val = 0
        · have hb := topFreshTailCausalBadBorderBirthStep
            ring C s hn hbad Z e hqueue j hj hsrc
            (by rw [hsrc]; exact ho)
          refine Or.inr (Or.inl ⟨hsrc, rfl, hj, ?_⟩)
          rw [← hsrc]; exact hb.1
        · have hb := topFreshTailCausalBadInteriorEmptyStep
            ring C s hn hbad Z e hqueue j (by omega) hsrc
            (by rw [hsrc]; exact ho)
          refine Or.inl ?_
          rw [← hsrc]; exact hb.1
    | U =>
        have hu := topFreshTailFifoUnreadSamples ring C Z e hxl hyl
          (by rw [hsrc]; exact ho)
        have hbeta : (Z.1.1 e).beta =
            (if j.val = 0 then true else false) := by
          rw [hsrc]; exact hgeo.2.2.1
        refine Or.inr (Or.inr (Or.inl ⟨hsrc, rfl, ?_⟩))
        rw [← hsrc, hu, hbeta]
    | D v t =>
        rcases topFreshTailCausalDSourceOutcomes ring C Z e v t hxl hyl
            (by rw [hsrc]; exact ho) with hstay | hgo
        · refine Or.inl ?_
          rw [← hsrc]; exact hstay
        · refine Or.inr (Or.inr (Or.inr (Or.inl ⟨hsrc, v, t, rfl, ?_⟩)))
          rw [← hsrc]; exact hgo
  · by_cases hresp : ring.rightNeighbor e = certSite s j.val
    · have hformula := topFreshTailCausalResponderPhysicalOutput
        ring (by omega) C Z e
      rw [hresp] at hformula
      have hjl : (Z.1.1 (certSite s j.val)).l = false := hgeo.1
      by_cases hzero : j.val = 0
      · -- offset zero: beta is true, so no D can enter
        have hbeta : (Z.1.1 (certSite s j.val)).beta = true := by
          rw [hgeo.2.2.1, if_pos hzero]
        rw [hjl, hbeta] at hformula
        cases hle : (Z.1.1 e).l
        · rw [hle] at hformula
          simp only [Bool.false_or, Bool.not_true, Bool.and_false,
            Bool.false_and] at hformula
          refine Or.inl ?_
          simpa using hformula
        · rw [hle] at hformula
          refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨hzero, ?_⟩))))
          simpa using hformula
      · have hpos : 0 < j.val := by omega
        have hpred := topFreshTailCausalIncomingPredecessor
          ring hn s j hpos e hresp
        have hprevFin : j.val - 1 < topClockSpan n := by omega
        have hgeoPrev := topFreshTailCausalSourcePublicGeometry
          ring C s hn hbad Z hreach ⟨j.val - 1, hprevFin⟩
        have hel : (Z.1.1 e).l = false := by
          rw [hpred]; exact hgeoPrev.1
        have hbeta : (Z.1.1 (certSite s j.val)).beta = false := by
          rw [hgeo.2.2.1, if_neg hzero]
        rw [hjl, hbeta, hel] at hformula
        simp only [Bool.false_or, Bool.not_false, Bool.and_true,
          Bool.false_eq_true, if_false] at hformula
        by_cases hmove :
            ((Z.1.1 e).qOut.isD &&
              (Z.1.1 (certSite s j.val)).qOut.isE) = true
        · rw [if_pos hmove] at hformula
          simp only [Bool.and_eq_true] at hmove
          obtain ⟨hxD, hyE⟩ := hmove
          cases hxo : (Z.1.1 e).qOut with
          | E => rw [hxo] at hxD; cases hxD
          | U => rw [hxo] at hxD; cases hxD
          | D v t =>
              have hyo : (Z.1.1 (certSite s j.val)).qOut = .E := by
                cases hy : (Z.1.1 (certSite s j.val)).qOut with
                | E => rfl
                | U => rw [hy] at hyE; cases hyE
                | D w u => rw [hy] at hyE; cases hyE
              refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
                ⟨hpos, hpred, hyo, v, t, ?_, ?_⟩))))
              · rw [← hpred]; exact hxo
              · rw [hformula, hxo]; rfl
        · rw [if_neg hmove] at hformula
          exact Or.inl hformula
    · have haway := (topPortLiteralAwayFields ring C Z.1.1 e
        (certSite s j.val) (fun h => hsrc h.symm)
        (fun h => hresp h.symm)).2.2
      exact Or.inl haway

/-- The literal source-terminal port row on the reached trace: the
OLD source D departs iff the border responder input is E and its
carry OFF; that is also exactly when the comparison audit records the
port export, and the responder then holds the pending payload.
Consumer: topFreshTailTicketDeparture and the genuine-anchor
identification of topFreshTailPreTailVisitCharge (J3). -/
theorem topFreshTailTicketPortRow
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hn : 5 ≤ n)
    (hbad : HeadlineDigit.BadCompletePair C s)
    (Z : TopFixedTraceState n)
    (hreach : topClockReached ring C Z)
    (e : Fin n)
    (hsite : e = certSite s (topClockSpan n - 1))
    (v : Fin (compileAdvice (ceilLogTwo n)).topA) (t : Bool)
    (hold : (Z.1.1 e).qOut = .D v t) :
    ring.rightNeighbor e = certSite s (topClockSpan n) ∧
    ((topFixedTraceNext ring C Z e).1.1 e).qOut =
      (if (Z.1.1 (ring.rightNeighbor e)).qIn.isE &&
          (Z.1.1 (ring.rightNeighbor e)).qCarry.isOff then
        (if t then .U else .E) else .D v t) ∧
    ((∃ x, topFreshTailGenealogyPortExport ring C s Z e = some x) ↔
      ((Z.1.1 (ring.rightNeighbor e)).qIn = .E ∧
       (Z.1.1 (ring.rightNeighbor e)).qCarry = .OFF)) ∧
    ((Z.1.1 (ring.rightNeighbor e)).qIn = .E →
     (Z.1.1 (ring.rightNeighbor e)).qCarry = .OFF →
     ((topFixedTraceNext ring C Z e).1.1
        (ring.rightNeighbor e)).qIn = .P v t) := by
  have hr := cert_rho_ge_three n hn
  change 3 ≤ topClockSpan n at hr
  have hlast : topClockSpan n - 1 < topClockSpan n := by omega
  have hgeo := topFreshTailCausalSourcePublicGeometry
    ring C s hn hbad Z hreach ⟨topClockSpan n - 1, hlast⟩
  have hxl : (Z.1.1 e).l = false := by rw [hsite]; exact hgeo.1
  have hyl : (Z.1.1 (ring.rightNeighbor e)).l = false := by
    rw [hsite]; exact hgeo.2.1
  have hyb : (Z.1.1 (ring.rightNeighbor e)).beta = true := by
    rw [hsite]
    have h := hgeo.2.2.2
    have hsucc : topClockSpan n - 1 + 1 = topClockSpan n := by omega
    simp only [hsucc, if_true] at h
    exact h
  have hnb : ring.rightNeighbor e = certSite s (topClockSpan n) := by
    rw [hsite, topFreshTailTicketNeighborSite]
    congr 1
    omega
  refine ⟨hnb, ?_, ?_, ?_⟩
  · have hx := (topPortLiteralSourceFields ring C Z.1.1 e).2.2
    change (topFixedPublicNext ring C Z.1.1 e e).qOut = _
    rw [hx]
    unfold topPortLiteralTopOwner
    exact topFreshTailTicketOwnerPortOut _ _ _ _ _ v t hxl hyl hyb hold
  · have hp : e = certSite s (topClockSpan n - 1) ∧
        ring.rightNeighbor e = certSite s (topClockSpan n) := ⟨hsite, hnb⟩
    have hlane := topFreshTailTicketLaneExportIff
      (Z.1.2.clock + 1) e (ring.rightNeighbor e)
      (digitLaneView .comparison (piD Z.1.1 e)
        (piD Z.1.1 e).word.beta)
      (digitLaneView .comparison
        (piD Z.1.1 (ring.rightNeighbor e))
        (piD Z.1.1 (ring.rightNeighbor e)).word.beta)
      (Z.1.2.current e).comparison
      (Z.1.2.current (ring.rightNeighbor e)).comparison
      v t
      (by change (Z.1.1 e).l = false; exact hxl)
      (by change (Z.1.1 (ring.rightNeighbor e)).l = false; exact hyl)
      (by change (Z.1.1 (ring.rightNeighbor e)).beta = true; exact hyb)
      (by change (Z.1.1 e).qOut = .D v t; exact hold)
    have hexp :
        topFreshTailGenealogyPortExport ring C s Z e =
          (digitLaneReplay .comparison (Z.1.2.clock + 1) e
            (ring.rightNeighbor e)
            (digitLaneView .comparison (piD Z.1.1 e)
              (piD Z.1.1 e).word.beta)
            (digitLaneView .comparison
              (piD Z.1.1 (ring.rightNeighbor e))
              (piD Z.1.1 (ring.rightNeighbor e)).word.beta)
            (Z.1.2.current e).comparison
            (Z.1.2.current (ring.rightNeighbor e)).comparison).exported := by
      simp only [topFreshTailGenealogyPortExport, if_pos hp]
      rfl
    rw [hexp]
    change _ ↔ _ at hlane
    have hin :
        ((Z.1.1 (ring.rightNeighbor e)).qIn.isE = true ↔
          (Z.1.1 (ring.rightNeighbor e)).qIn = .E) := by
      cases (Z.1.1 (ring.rightNeighbor e)).qIn <;> simp [InTok.isE]
    have hcar :
        ((Z.1.1 (ring.rightNeighbor e)).qCarry.isL = false ↔
          (Z.1.1 (ring.rightNeighbor e)).qCarry = .OFF) := by
      cases (Z.1.1 (ring.rightNeighbor e)).qCarry <;> simp [QCarry.isL]
    constructor
    · rintro ⟨x, hx⟩
      have h := hlane.1 (by rw [hx]; exact Option.some_ne_none x)
      exact ⟨hin.1 h.1, hcar.1 h.2⟩
    · rintro ⟨hi, hc⟩
      have h := hlane.2 ⟨hin.2 hi, hcar.2 hc⟩
      cases hq : (digitLaneReplay .comparison (Z.1.2.clock + 1) e
            (ring.rightNeighbor e)
            (digitLaneView .comparison (piD Z.1.1 e)
              (piD Z.1.1 e).word.beta)
            (digitLaneView .comparison
              (piD Z.1.1 (ring.rightNeighbor e))
              (piD Z.1.1 (ring.rightNeighbor e)).word.beta)
            (Z.1.2.current e).comparison
            (Z.1.2.current (ring.rightNeighbor e)).comparison).exported with
      | none => exact absurd hq h
      | some x => exact ⟨x, rfl⟩
  · intro hi hc
    have hy := (topPortLiteralResponderFields ring (by omega) C Z.1.1 e).1
    change (topFixedPublicNext ring C Z.1.1 e (ring.rightNeighbor e)).qIn = _
    rw [hy]
    unfold topPortLiteralTopOwner
    exact topFreshTailTicketOwnerPortInput _ _ _ _ _ v t hxl hyl hyb hold hi hc

/-- A source D at offset k that actually left its slot on this edge
either moved into the OLD empty successor slot together with its
genealogical carrier, or (at the terminal offset) was accepted by
the port with a recorded comparison export and pending payload.
Consumer: topFreshTailTicketDataTrack and the rearm case of
topFreshTailTicketSlotCases (J3). -/
theorem topFreshTailTicketDeparture
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hn : 5 ≤ n)
    (hbad : HeadlineDigit.BadCompletePair C s)
    (Z : TopFixedTraceState n)
    (hreach : topClockReached ring C Z)
    (e : Fin n) (k : Fin (topClockSpan n))
    (hsite : e = certSite s k.val)
    (v : Fin (compileAdvice (ceilLogTwo n)).topA) (t : Bool)
    (hold : (Z.1.1 (certSite s k.val)).qOut = .D v t)
    (hgo : ((topFixedTraceNext ring C Z e).1.1 (certSite s k.val)).qOut =
      (if t then .U else .E)) :
    (∃ hnext : k.val + 1 < topClockSpan n,
      (Z.1.1 (certSite s (k.val + 1))).qOut = .E ∧
      ((topFixedTraceNext ring C Z e).1.1
        (certSite s (k.val + 1))).qOut = .D v t ∧
      (topFreshTailGenealogy ring C s (topFixedTraceNext ring C Z e)).slots
          ⟨k.val + 1, hnext⟩ =
        (topFreshTailGenealogy ring C s Z).slots k) ∨
    (k.val + 1 = topClockSpan n ∧
      (∃ x, topFreshTailGenealogyPortExport ring C s Z e = some x) ∧
      ((topFixedTraceNext ring C Z e).1.1
        (certSite s (topClockSpan n))).qIn = .P v t) := by
  have hqueue := topFreshTailCloseReachedQueue ring C s hn hbad Z hreach
  have htrace := topFreshTailGenealogyTraceReached ring C s Z hreach
  have hgeo := topFreshTailCausalSourcePublicGeometry
    ring C s hn hbad Z hreach k
  have hxl : (Z.1.1 e).l = false := by rw [hsite]; exact hgeo.1
  have hyl : (Z.1.1 (ring.rightNeighbor e)).l = false := by
    rw [hsite]; exact hgeo.2.1
  have hxo : (Z.1.1 e).qOut = .D v t := by rw [hsite]; exact hold
  have hne : (if t then (OutTok.U : OutTok (compileAdvice (ceilLogTwo n)).topA)
      else .E) ≠ .D v t := by
    cases t <;> simp
  by_cases hnext : k.val + 1 < topClockSpan n
  · left
    refine ⟨hnext, ?_⟩
    have hnb : ring.rightNeighbor e = certSite s (k.val + 1) := by
      rw [hsite, topFreshTailTicketNeighborSite]
    have hyb : (Z.1.1 (ring.rightNeighbor e)).beta = false := by
      rw [hsite]
      have h := hgeo.2.2.2
      have hneq : ¬ (k.val + 1 = topClockSpan n) := by omega
      simp only [hneq, if_false] at h
      exact h
    by_cases hyo : (Z.1.1 (ring.rightNeighbor e)).qOut = .E
    · have hmove := topFreshTailFifoDataMove ring (by omega) C Z e v t
        hxl hyl hxo hyo hyb
      have hnotE : (Z.1.1 (certSite s k.val)).qOut ≠ .E := by
        rw [hold]; intro h; cases h
      cases hslot : (topFreshTailGenealogy ring C s Z).slots k with
      | none =>
          exact absurd ((hqueue.slot k).2 hslot) hnotE
      | some parent =>
          have htarget := topFreshTailCausalDataMoveTarget ring (by omega)
            C s (topFreshTailGenealogy ring C s Z) e k v t parent hnext hsite
            (by rw [htrace]; exact hxo)
            (by rw [htrace]; exact hyo)
            (by rw [htrace]; exact hxl)
            (by rw [htrace]; exact hyl)
            (by rw [htrace]; exact hyb)
            hslot
          refine ⟨?_, ?_, ?_⟩
          · rw [← hnb]; exact hyo
          · rw [← hnb]; exact hmove.2
          · rw [topFreshTailCausalReplayNext]
            exact htarget
    · have hstay := topFreshTailFifoOccupiedFrame ring C Z e v t
        hxl hyl hxo hyb hyo
      rw [← hsite, hstay] at hgo
      exact absurd hgo.symm hne
  · right
    have hk : k.val = topClockSpan n - 1 := by omega
    have hsite' : e = certSite s (topClockSpan n - 1) := by
      rw [hsite, hk]
    have hport := topFreshTailTicketPortRow ring C s hn hbad Z hreach e
      hsite' v t hxo
    have hguard :
        (Z.1.1 (ring.rightNeighbor e)).qIn = .E ∧
        (Z.1.1 (ring.rightNeighbor e)).qCarry = .OFF := by
      have hrow := hport.2.1
      rw [← hsite] at hgo
      rw [hgo] at hrow
      cases hi : (Z.1.1 (ring.rightNeighbor e)).qIn <;>
        cases hc : (Z.1.1 (ring.rightNeighbor e)).qCarry <;>
        simp [hi, hc, InTok.isE, QCarry.isOff] at hrow <;>
        first
          | exact ⟨rfl, rfl⟩
          | exact absurd hrow.symm hne
          | (cases t <;> simp at hrow)
    refine ⟨by omega, hport.2.2.1.2 hguard, ?_⟩
    rw [← hport.1]
    exact hport.2.2.2 hguard.1 hguard.2

/-- Every carrier of the NEW genealogy at source slot j is one of:
the same OLD carrier kept in place (unchanged byte, or an interior
U sampled to D(false)); the OLD predecessor carrier moved into an
OLD empty slot with its exact D byte; the rearm child of an OLD
D(true) that left U; or a fresh border carrier born at offset zero
as U or D(true). Consumer: every clause of the J3 ticket history
and barrier steps (topFreshTailTicketHistoryStep,
topFreshTailFirstBorderBarrierStep). -/
theorem topFreshTailTicketSlotCases
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hn : 5 ≤ n)
    (hbad : HeadlineDigit.BadCompletePair C s)
    (Z : TopFixedTraceState n)
    (hreach : topClockReached ring C Z)
    (e : Fin n) (j : Fin (topClockSpan n))
    (a : TopFreshTailCarrier (topClockSpan n))
    (hnew : (topFreshTailGenealogy ring C s
      (topFixedTraceNext ring C Z e)).slots j = some a) :
    ((topFreshTailGenealogy ring C s Z).slots j = some a ∧
      (Z.1.1 (certSite s j.val)).qOut ≠ .E ∧
      (((topFixedTraceNext ring C Z e).1.1 (certSite s j.val)).qOut =
          (Z.1.1 (certSite s j.val)).qOut ∨
        (0 < j.val ∧ e = certSite s j.val ∧
          (Z.1.1 (certSite s j.val)).qOut = .U ∧
          ((topFixedTraceNext ring C Z e).1.1 (certSite s j.val)).qOut =
            .D (Z.1.1 e).d false))) ∨
    (∃ hpos : 0 < j.val,
      e = certSite s (j.val - 1) ∧
      (Z.1.1 (certSite s j.val)).qOut = .E ∧
      (topFreshTailGenealogy ring C s Z).slots
          ⟨j.val - 1, Nat.lt_of_le_of_lt (Nat.sub_le _ _) j.isLt⟩ = some a ∧
      ∃ (v : Fin (compileAdvice (ceilLogTwo n)).topA) (t : Bool),
        (Z.1.1 (certSite s (j.val - 1))).qOut = .D v t ∧
        ((topFixedTraceNext ring C Z e).1.1 (certSite s j.val)).qOut =
          .D v t) ∨
    (e = certSite s j.val ∧
      ∃ (p : TopFreshTailCarrier (topClockSpan n))
        (v : Fin (compileAdvice (ceilLogTwo n)).topA),
        (topFreshTailGenealogy ring C s Z).slots j = some p ∧
        a = topFreshTailGenealogyRearm j (Z.1.2.clock + 1) p ∧
        (Z.1.1 (certSite s j.val)).qOut = .D v true ∧
        ((topFixedTraceNext ring C Z e).1.1 (certSite s j.val)).qOut =
          .U) ∨
    (j.val = 0 ∧ e = certSite s j.val ∧
      a = { origin := .freshBorder (Z.1.2.clock + 1),
            born := Z.1.2.clock + 1 } ∧
      (((topFixedTraceNext ring C Z e).1.1 (certSite s j.val)).qOut = .U ∨
       ∃ d : Fin (compileAdvice (ceilLogTwo n)).topA,
        ((topFixedTraceNext ring C Z e).1.1 (certSite s j.val)).qOut =
          .D d true)) := by
  have htrace := topFreshTailGenealogyTraceReached ring C s Z hreach
  have hslotEq :
      (topFreshTailGenealogy ring C s
        (topFixedTraceNext ring C Z e)).slots j =
      topFreshTailGenealogyNextSlot ring C s
        (topFreshTailGenealogy ring C s Z) e j := by
    rw [topFreshTailCausalReplayNext]
    rfl
  rw [hslotEq] at hnew
  unfold topFreshTailGenealogyNextSlot at hnew
  rw [htrace] at hnew
  rcases topFreshTailTicketSlotPhysical ring C s hn hbad Z hreach e j with
    hsame | ⟨hsrc, hoE, hj0, hnU⟩ | ⟨hsrc, hoU, hnD⟩ |
    ⟨hsrc, v, t, hoD, hnX⟩ | ⟨hpos, hpred, hoE, v, t, hpD, hnD⟩ |
    ⟨hj0, hnE⟩
  · cases ho : (Z.1.1 (certSite s j.val)).qOut with
    | E =>
        rw [hsame, ho] at hnew
        simp at hnew
    | U =>
        rw [hsame, ho] at hnew
        simp only at hnew
        exact Or.inl ⟨hnew, by simp, Or.inl (hsame.trans ho)⟩
    | D w u =>
        rw [hsame, ho] at hnew
        simp only at hnew
        exact Or.inl ⟨hnew, by simp, Or.inl (hsame.trans ho)⟩
  · rw [hnU, hoE] at hnew
    simp only [hj0, if_true] at hnew
    refine Or.inr (Or.inr (Or.inr ⟨hj0, hsrc, ?_, Or.inl hnU⟩))
    exact (Option.some.inj hnew).symm
  · rw [hnD, hoU] at hnew
    by_cases hj0 : j.val = 0
    · simp only [hj0, if_true] at hnew
      refine Or.inr (Or.inr (Or.inr ⟨hj0, hsrc, ?_, ?_⟩))
      · exact (Option.some.inj hnew).symm
      · right
        refine ⟨(Z.1.1 e).d, ?_⟩
        rw [hnD, if_pos hj0]
    · simp only [hj0, if_false] at hnew
      refine Or.inl ⟨hnew, by rw [hoU]; simp, Or.inr
        ⟨by omega, hsrc, hoU, ?_⟩⟩
      rw [hnD, if_neg hj0]
  · cases t with
    | false =>
        simp only [Bool.false_eq_true, if_false] at hnX
        rw [hnX] at hnew
        simp at hnew
    | true =>
        simp only [if_true] at hnX
        rw [hnX, hoD] at hnew
        simp only at hnew
        cases hp : (topFreshTailGenealogy ring C s Z).slots j with
        | none =>
            rw [hp] at hnew
            simp at hnew
        | some p =>
            rw [hp] at hnew
            simp only [Option.map_some] at hnew
            refine Or.inr (Or.inr (Or.inl ⟨hsrc, p, v, rfl, ?_, hoD, hnX⟩))
            exact (Option.some.inj hnew).symm
  · rw [hnD, hoE] at hnew
    simp only [hpos, dif_pos, hpred, if_true] at hnew
    exact Or.inr (Or.inl ⟨hpos, hpred, hoE, hnew, v, t, hpD, hnD⟩)
  · rw [hnE] at hnew
    simp at hnew

/-- A digit lane records a sample only from its OLD U source, with
the source's own marker as tail and the service stamp and site.
Consumer: topFreshTailTicketRecordedSampleMarker (J3 anchor). -/
theorem topFreshTailTicketLaneSampleMarker
    {c : Compiled} {n : Nat}
    (lane : DigitLane) (stamp : Nat) (source destination : Fin n)
    (x y : DigitLaneView c) (gx gy : DigitLaneGhost c n)
    (smp : DigitSample c n)
    (h : (digitLaneReplay lane stamp source destination
      x y gx gy).sample = some smp) :
    smp.tail = x.marker ∧ smp.id.time = stamp ∧ smp.id.site = source := by
  cases hxo : x.out <;> cases hxl : x.leader <;> cases hyl : y.leader <;>
    simp [digitLaneReplay, hxo, hxl, hyl, OutTok.isD, OutTok.isU,
      OutTok.isE] at h <;>
    (try split at h) <;> (try split at h) <;> (try split at h) <;>
    (try simp_all) <;> (try (subst h; exact ⟨rfl, rfl, rfl⟩))

/-- A digit lane exports only from an OLD D source.
Consumer: topFreshTailTicketPortExportSource (J3 receipts). -/
theorem topFreshTailTicketLaneExportSourceD
    {c : Compiled} {n : Nat}
    (lane : DigitLane) (stamp : Nat) (source destination : Fin n)
    (x y : DigitLaneView c) (gx gy : DigitLaneGhost c n)
    (h : (digitLaneReplay lane stamp source destination
      x y gx gy).exported ≠ none) :
    x.out.isD = true := by
  cases hxo : x.out <;> cases hxl : x.leader <;> cases hyl : y.leader <;>
    simp [digitLaneReplay, hxo, hxl, hyl, OutTok.isD, OutTok.isU,
      OutTok.isE] at h ⊢ <;>
    (try split at h) <;> (try split at h) <;> (try split at h) <;>
    simp_all

/-- A genealogy port event is served by an OLD D at the source
terminal slot. Consumer: the receipt clauses of the J3 history. -/
theorem topFreshTailTicketPortExportSource
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (Z : TopFixedTraceState n) (e : Fin n)
    (x : DigitExport (compileAdvice (ceilLogTwo n)) n)
    (hevent : topFreshTailGenealogyPortExport ring C s Z e = some x) :
    e = certSite s (topClockSpan n - 1) ∧
    ∃ (v : Fin (compileAdvice (ceilLogTwo n)).topA) (t : Bool),
      (Z.1.1 (certSite s (topClockSpan n - 1))).qOut = .D v t := by
  have hframe := topFreshTailAuditSelectedPortFrame ring C s Z e x hevent
  have hsite := hframe.1
  have hp : e = certSite s (topClockSpan n - 1) ∧
      ring.rightNeighbor e = certSite s (topClockSpan n) :=
    ⟨hframe.1, hframe.2.1⟩
  have hlane :
      (digitLaneReplay .comparison (Z.1.2.clock + 1) e
        (ring.rightNeighbor e)
        (digitLaneView .comparison (piD Z.1.1 e)
          (piD Z.1.1 e).word.beta)
        (digitLaneView .comparison
          (piD Z.1.1 (ring.rightNeighbor e))
          (piD Z.1.1 (ring.rightNeighbor e)).word.beta)
        (Z.1.2.current e).comparison
        (Z.1.2.current (ring.rightNeighbor e)).comparison).exported ≠ none := by
    have h : topFreshTailGenealogyPortExport ring C s Z e =
        (digitLaneReplay .comparison (Z.1.2.clock + 1) e
          (ring.rightNeighbor e)
          (digitLaneView .comparison (piD Z.1.1 e)
            (piD Z.1.1 e).word.beta)
          (digitLaneView .comparison
            (piD Z.1.1 (ring.rightNeighbor e))
            (piD Z.1.1 (ring.rightNeighbor e)).word.beta)
          (Z.1.2.current e).comparison
          (Z.1.2.current (ring.rightNeighbor e)).comparison).exported := by
      simp only [topFreshTailGenealogyPortExport, if_pos hp]
      rfl
    rw [← h, hevent]
    exact Option.some_ne_none x
  have hD := topFreshTailTicketLaneExportSourceD .comparison
    (Z.1.2.clock + 1) e (ring.rightNeighbor e) _ _ _ _ hlane
  change (Z.1.1 e).qOut.isD = true at hD
  refine ⟨hsite, ?_⟩
  rw [← hsite]
  cases hxo : (Z.1.1 e).qOut with
  | E => rw [hxo] at hD; cases hD
  | U => rw [hxo] at hD; cases hD
  | D v t => exact ⟨v, t, rfl⟩

/-- Every frame of a reached audit has positive time and each of its
comparison samples carries the public marker of its service site.
Consumer: topFreshTailTicketRecordedSampleMarker. -/
theorem topFreshTailTicketFrameMarker
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (word : List (Fin n)) :
    ∀ f ∈ (topFixedTraceRun ring C word).1.2.frames,
      0 < f.time ∧
      ∀ smp : DigitSample (compileAdvice (ceilLogTwo n)) n,
        (digitReceiptLane .comparison f.receipt).sample = some smp →
        smp.tail = (C f.edge).beta := by
  have hfold : ∀ (w : List (Fin n)) (Z : TopFixedTraceState n),
      topClockReached ring C Z →
      (∀ f ∈ Z.1.2.frames, 0 < f.time ∧
        ∀ smp : DigitSample (compileAdvice (ceilLogTwo n)) n,
          (digitReceiptLane .comparison f.receipt).sample = some smp →
          smp.tail = (C f.edge).beta) →
      ∀ f ∈ (w.foldl (topFixedTraceNext ring C) Z).1.2.frames,
        0 < f.time ∧
        ∀ smp : DigitSample (compileAdvice (ceilLogTwo n)) n,
          (digitReceiptLane .comparison f.receipt).sample = some smp →
          smp.tail = (C f.edge).beta := by
    intro w
    induction w with
    | nil => intro Z _ hZ; exact hZ
    | cons e rest ih =>
        intro Z hreach hZ
        apply ih (topFixedTraceNext ring C Z e)
          (topClockReachedNext ring C Z e hreach)
        intro f hf
        change f ∈ _ :: _ at hf
        rcases List.mem_cons.1 hf with hnew | hold
        · subst hnew
          refine ⟨Nat.succ_pos _, ?_⟩
          intro smp hsmp
          have hm := (topFreshTailTicketLaneSampleMarker .comparison _ _ _ _ _
            _ _ smp hsmp).1
          rw [hm]
          exact (topFreshTailCausalReachedPublicMask ring C Z hreach e).2
        · exact hZ f hold
  exact hfold word ((C, digitAuditInitial (piD C)), [])
    (by unfold topClockReached; rfl)
    (by intro f hf; change f ∈ ([] : List _) at hf; cases hf)

/-- A recorded comparison sample of a reached trace has positive
time and its tail is the public marker of its sampling site.
Consumer: the genuine-anchor identification in
topFreshTailTicketFreshExportGenuine (J3). -/
theorem topFreshTailTicketRecordedSampleMarker
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n)
    (Z : TopFixedTraceState n)
    (hreach : topClockReached ring C Z)
    (smp : DigitSample (compileAdvice (ceilLogTwo n)) n)
    (hrec : DigitRecordedSample Z.1.2 smp)
    (hlane : smp.id.lane = .comparison) :
    0 < smp.id.time ∧ smp.tail = (C smp.id.site).beta := by
  obtain ⟨f, hf, htime, hedge, hsample, _⟩ := hrec
  rw [hlane] at hsample
  rw [hreach] at hf
  have h := topFreshTailTicketFrameMarker ring C Z.2 f hf
  refine ⟨htime ▸ h.1, ?_⟩
  rw [← hedge]
  exact h.2 smp hsample

/-- A tail-true recorded comparison sample taken at a source offset
was taken at offset zero, the only marked source site.
Consumer: topFreshTailTicketFreshExportGenuine (J3 anchor). -/
theorem topFreshTailTicketTailSampleAtBorder
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hn : 5 ≤ n)
    (hbad : HeadlineDigit.BadCompletePair C s)
    (Z : TopFixedTraceState n)
    (hreach : topClockReached ring C Z)
    (smp : DigitSample (compileAdvice (ceilLogTwo n)) n)
    (hrec : DigitRecordedSample Z.1.2 smp)
    (hlane : smp.id.lane = .comparison)
    (k : Fin (topClockSpan n))
    (hsite : smp.id.site = certSite s k.val)
    (htail : smp.tail = true) :
    k.val = 0 ∧ 0 < smp.id.time := by
  have hm := topFreshTailTicketRecordedSampleMarker ring C Z hreach smp hrec hlane
  have hgeo := (topFreshTailCausalSourcePublicGeometry
    ring C s hn hbad Z hreach k).2.2.1
  have hmask := (topFreshTailCausalReachedPublicMask ring C Z hreach
    (certSite s k.val)).2
  refine ⟨?_, hm.1⟩
  have hb : (C (certSite s k.val)).beta = true := by
    rw [← hsite, ← hm.2]; exact htail
  rw [← hmask, hgeo] at hb
  by_cases hk : k.val = 0
  · exact hk
  · rw [if_neg hk] at hb; cases hb

/-- An OLD source D at slot k with carrier b either keeps both on this
edge, or leaves its slot (moving with its carrier, or accepted by the
port with a recorded export), or is cleared at offset zero by a leader
predecessor. Consumer: barrier witness tracking in
topFreshTailFirstBorderBarrierStep (J3). -/
theorem topFreshTailTicketDataTrack
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hn : 5 ≤ n)
    (hbad : HeadlineDigit.BadCompletePair C s)
    (Z : TopFixedTraceState n)
    (hreach : topClockReached ring C Z)
    (e : Fin n) (k : Fin (topClockSpan n))
    (v : Fin (compileAdvice (ceilLogTwo n)).topA) (t : Bool)
    (hold : (Z.1.1 (certSite s k.val)).qOut = .D v t)
    (b : TopFreshTailCarrier (topClockSpan n))
    (hb : (topFreshTailGenealogy ring C s Z).slots k = some b) :
    ((topFreshTailGenealogy ring C s (topFixedTraceNext ring C Z e)).slots k =
        some b ∧
      ((topFixedTraceNext ring C Z e).1.1 (certSite s k.val)).qOut = .D v t) ∨
    (e = certSite s k.val ∧
      ((topFixedTraceNext ring C Z e).1.1 (certSite s k.val)).qOut =
        (if t then .U else .E) ∧
      ((∃ hnext : k.val + 1 < topClockSpan n,
        ((topFixedTraceNext ring C Z e).1.1
          (certSite s (k.val + 1))).qOut = .D v t ∧
        (topFreshTailGenealogy ring C s (topFixedTraceNext ring C Z e)).slots
          ⟨k.val + 1, hnext⟩ = some b) ∨
      (k.val + 1 = topClockSpan n ∧
        (∃ x, topFreshTailGenealogyPortExport ring C s Z e = some x) ∧
        ((topFixedTraceNext ring C Z e).1.1
          (certSite s (topClockSpan n))).qIn = .P v t))) ∨
    (k.val = 0 ∧
      ((topFixedTraceNext ring C Z e).1.1 (certSite s k.val)).qOut = .E) := by
  have htrace := topFreshTailGenealogyTraceReached ring C s Z hreach
  rcases topFreshTailTicketSlotPhysical ring C s hn hbad Z hreach e k with
    hsame | ⟨_, hoE, _, _⟩ | ⟨_, hoU, _⟩ |
    ⟨hsrc, w, u, hoD, hnX⟩ | ⟨_, _, hoE, _⟩ | ⟨hk0, hnE⟩
  · left
    refine ⟨?_, hsame.trans hold⟩
    have hslotEq :
        (topFreshTailGenealogy ring C s
          (topFixedTraceNext ring C Z e)).slots k =
        topFreshTailGenealogyNextSlot ring C s
          (topFreshTailGenealogy ring C s Z) e k := by
      rw [topFreshTailCausalReplayNext]
      rfl
    rw [hslotEq]
    unfold topFreshTailGenealogyNextSlot
    rw [htrace, hsame, hold]
    exact hb
  · rw [hold] at hoE; cases hoE
  · rw [hold] at hoU; cases hoU
  · rw [hold] at hoD
    cases hoD
    right; left
    refine ⟨hsrc, hnX, ?_⟩
    rcases topFreshTailTicketDeparture ring C s hn hbad Z hreach e k hsrc
        v t hold hnX with ⟨hnext, _, hnD, hslot⟩ | hport
    · exact Or.inl ⟨hnext, hnD, hslot.trans hb⟩
    · exact Or.inr hport
  · rw [hold] at hoE; cases hoE
  · exact Or.inr (Or.inr ⟨hk0, hnE⟩)

/-- The consumed receipt list grows on one edge by exactly the OLD
terminal carrier's origin when the genealogy port event occurs, and
not at all otherwise. Consumer: J3 receipt clauses and the count
bridge topFreshTailTicketReceiptCountEq. -/
theorem topFreshTailTicketConsumedStep
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hn : 5 ≤ n)
    (Z : TopFixedTraceState n)
    (hreach : topClockReached ring C Z)
    (e : Fin n) :
    (topFreshTailGenealogy ring C s (topFixedTraceNext ring C Z e)).consumed =
      (topFreshTailGenealogy ring C s Z).consumed ++
        ((topFreshTailGenealogyPortExport ring C s Z e).toList.map
          (fun _ => (Z.1.2.clock + 1,
            ((topFreshTailGenealogy ring C s Z).slots
              ⟨topClockSpan n - 1, by
                have hr := cert_rho_ge_three n hn
                change 3 ≤ topClockSpan n at hr
                omega⟩).map (fun carrier => carrier.origin)))) := by
  have hr := cert_rho_ge_three n hn
  change 3 ≤ topClockSpan n at hr
  have hpos : 0 < topClockSpan n := by omega
  have htrace := topFreshTailGenealogyTraceReached ring C s Z hreach
  rw [topFreshTailCausalReplayNext]
  simp only [topFreshTailGenealogyStep, dif_pos hpos, htrace]

/-- A fresh-border carrier accepted from the source terminal with a
true tail is the first genuine border tail: its operand is a recorded
offset-zero comparison sample and the border holds the pending tail.
Consumer: the receipt clause of topFreshTailFirstBorderBarrierStep
and hence topFreshTailPreTailVisitCharge (J3 stopping rule). -/
theorem topFreshTailTicketFreshExportGenuine
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hn : 5 ≤ n)
    (hbad : HeadlineDigit.BadCompletePair C s)
    (Z : TopFixedTraceState n)
    (hreach : topClockReached ring C Z)
    (e : Fin n)
    (x : DigitExport (compileAdvice (ceilLogTwo n)) n)
    (hevent : topFreshTailGenealogyPortExport ring C s Z e = some x)
    (c : TopFreshTailCarrier (topClockSpan n))
    (hc : (topFreshTailGenealogy ring C s Z).slots
      ⟨topClockSpan n - 1, by
        have hr := cert_rho_ge_three n hn
        change 3 ≤ topClockSpan n at hr
        omega⟩ = some c)
    (hfresh : ∃ b : Nat, c.origin = .freshBorder b)
    (v : Fin (compileAdvice (ceilLogTwo n)).topA)
    (hold : (Z.1.1 (certSite s (topClockSpan n - 1))).qOut = .D v true) :
    topClockGenuineTailAccepted C s (topFixedTraceNext ring C Z e) := by
  obtain ⟨hsite, hnb, hrecX, htime, hlaneX, hsrcX, hdstX, hopX, _⟩ :=
    topFreshTailAuditSelectedPortFrame ring C s Z e x hevent
  obtain ⟨value, tail, hD, hval, htl⟩ :=
    topFreshTailAuditPortOldPayload ring C s Z e
      ((Z.1.2.current (certSite s (topClockSpan n - 1))).comparison.out.atom)
      ⟨v, true, hold, rfl⟩ x hevent
  rw [hold] at hD
  cases hD
  have hr := cert_rho_ge_three n hn
  change 3 ≤ topClockSpan n at hr
  obtain ⟨carrier, hslot, hkind⟩ :=
    topFreshTailAuditSourceDataReached ring C s hn hbad Z hreach
      ⟨topClockSpan n - 1, by omega⟩ v true hold
  rw [hc] at hslot
  cases hslot
  rcases hkind with ⟨i, horigin, _⟩ | ⟨k, smp, hrec, hlane, hsiteS, hatom, hsv, hst⟩
  · obtain ⟨b, hb⟩ := hfresh
    rw [hb] at horigin
    cases horigin
  · obtain ⟨hk0, htpos⟩ := topFreshTailTicketTailSampleAtBorder ring C s hn
      hbad Z hreach smp hrec hlane k hsiteS hst
    have hxo : (Z.1.1 e).qOut = .D v true := by rw [hsite]; exact hold
    have hport := topFreshTailTicketPortRow ring C s hn hbad Z hreach e
      hsite v true hxo
    have hguard := hport.2.2.1.1 ⟨x, hevent⟩
    have hqin := hport.2.2.2 hguard.1 hguard.2
    rw [hport.1] at hqin
    refine ⟨smp, x,
      digitRecordedSampleStep ring (piD Z.1.1) Z.1.2 e smp hrec,
      hrecX, hlane, ?_, htpos, hst, ?_, hlaneX, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hsiteS, hk0]
    · rw [htime]; rfl
    · rw [hsrcX, hsite]
    · rw [hdstX, hnb]
    · rw [hopX, hsite, hatom]
    · rw [hval, hsv]
    · exact htl
    · rw [hsv]; exact hqin

/-- The physical comparison source-port receipt count grows on one
edge by exactly the number of genealogy port events of that edge.
Consumer: topFreshTailTicketReceiptCountEq. -/
theorem topFreshTailTicketReceiptCountStep
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (Z : TopFixedTraceState n) (e : Fin n) :
    topFreshTailPortReceiptCount s (topFixedTraceNext ring C Z e) =
      topFreshTailPortReceiptCount s Z +
        (topFreshTailGenealogyPortExport ring C s Z e).toList.length := by
  unfold topFreshTailPortReceiptCount topClockConcreteExportsAfter
  simp only [topFixedTraceNext, digitAuditStep, List.reverse_cons,
    List.filterMap_append, List.filter_append, List.length_append,
    List.filterMap_cons, List.filterMap_nil]
  congr 1
  unfold topFreshTailGenealogyPortExport
  cases hX : (digitService (Z.1.2.clock + 1) e (ring.rightNeighbor e)
      (piD Z.1.1 e) (piD Z.1.1 (ring.rightNeighbor e))
      (Z.1.2.current e) (Z.1.2.current (ring.rightNeighbor e))).comparison.exported with
  | none =>
      simp [digitReceiptLane, hX]
  | some x =>
      have hfields := topFreshTailAuditLaneExportFields .comparison
        (Z.1.2.clock + 1) e (ring.rightNeighbor e) _ _ _ _ x hX
      obtain ⟨ht, _, hsx, hdx, _⟩ := hfields
      by_cases hp : e = certSite s (topClockSpan n - 1) ∧
          ring.rightNeighbor e = certSite s (topClockSpan n)
      · have h1 : 0 < x.time := by omega
        have h2 : x.source = certSite s (topClockSpan n - 1) := hsx.trans hp.1
        have h3 : x.destination = certSite s (topClockSpan n) := hdx.trans hp.2
        simp only [digitReceiptLane]
        rw [hX, if_pos hp]
        simp [h1, h2, h3]
      · have hq : ¬ (0 < x.time ∧ x.source = certSite s (topClockSpan n - 1) ∧
            x.destination = certSite s (topClockSpan n)) := by
          rintro ⟨_, h1, h2⟩
          exact hp ⟨hsx ▸ h1, hdx ▸ h2⟩
        simp [digitReceiptLane, hX, hp, hq]

/-- On every actual scheduler word the physical comparison
source-port receipt count equals the length of the genealogy's
consumed list. Consumer: topFreshTailPreTailVisitCharge (J2/J3). -/
theorem topFreshTailTicketReceiptCountEq
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hn : 5 ≤ n)
    (word : List (Fin n)) :
    topFreshTailPortReceiptCount s (topFixedTraceRun ring C word) =
      (topFreshTailGenealogy ring C s
        (topFixedTraceRun ring C word)).consumed.length := by
  have hfold : ∀ (w : List (Fin n)) (Z : TopFixedTraceState n),
      topClockReached ring C Z →
      topFreshTailPortReceiptCount s Z =
        (topFreshTailGenealogy ring C s Z).consumed.length →
      topFreshTailPortReceiptCount s (w.foldl (topFixedTraceNext ring C) Z) =
        (topFreshTailGenealogy ring C s
          (w.foldl (topFixedTraceNext ring C) Z)).consumed.length := by
    intro w
    induction w with
    | nil => intro Z _ h; exact h
    | cons e rest ih =>
        intro Z hreach h
        apply ih (topFixedTraceNext ring C Z e)
          (topClockReachedNext ring C Z e hreach)
        rw [topFreshTailTicketReceiptCountStep,
          topFreshTailTicketConsumedStep ring C s hn Z hreach e,
          List.length_append, List.length_map, h]
  exact hfold word ((C, digitAuditInitial (piD C)), [])
    (by unfold topClockReached; rfl) rfl

end L3

#print axioms L3.topFreshTailTicketOwnerPortOut
#print axioms L3.topFreshTailTicketOwnerPortInput
#print axioms L3.topFreshTailTicketLaneExportIff
#print axioms L3.topFreshTailTicketSlotPhysical
#print axioms L3.topFreshTailTicketPortRow
#print axioms L3.topFreshTailTicketDeparture
#print axioms L3.topFreshTailTicketSlotCases
#print axioms L3.topFreshTailTicketLaneSampleMarker
#print axioms L3.topFreshTailTicketLaneExportSourceD
#print axioms L3.topFreshTailTicketPortExportSource
#print axioms L3.topFreshTailTicketFrameMarker
#print axioms L3.topFreshTailTicketRecordedSampleMarker
#print axioms L3.topFreshTailTicketTailSampleAtBorder
#print axioms L3.topFreshTailTicketDataTrack
#print axioms L3.topFreshTailTicketConsumedStep
#print axioms L3.topFreshTailTicketFreshExportGenuine
#print axioms L3.topFreshTailTicketReceiptCountStep
#print axioms L3.topFreshTailTicketReceiptCountEq
