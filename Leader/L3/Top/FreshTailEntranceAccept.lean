import Leader.L3.Top.FreshTailEntrance
import Leader.L3.Top.GhostInput

/-!
Q7c P.3 J5, lemma S (accept-predecessor half).

The first genuinely accepted comparison receipt is a last-frame
OLD terminal event. Its recorded sampled operand identifies the
pre-service D; the OLD target input and carry satisfy the literal
acceptance guards. Source-side QI/QC scratch is unrestricted.

Consumer: the entrance in TopClockBundle.
-/

namespace L3

open Classical
open MarkedCells

set_option autoImplicit false
set_option Elab.async false

/-- A selected comparison export requires an OLD D source, an
OLD empty target input, and an OLD inactive target carry.
This is a direct consequence of the replay's accepted bit,
rather than any post-service target register.
Consumer: topFreshTailEntranceAcceptPredecessor. -/
theorem topFreshTailEntranceExportReplayGuards
    {c : Compiled} {n : Nat}
    (lane : DigitLane) (stamp : Nat)
    (source destination : Fin n)
    (x y : DigitLaneView c)
    (gx gy : DigitLaneGhost c n)
    (exported : DigitExport c n)
    (hevent :
      (digitLaneReplay lane stamp source destination
        x y gx gy).exported = some exported) :
    x.out.isD = true ∧
    y.input.isE = true ∧
    y.carryLive = false := by
  have hselected :
      (replayChain x y gx gy).2 = true := by
    rw [replay_exported_eq] at hevent
    cases hflag : (replayChain x y gx gy).2 with
    | false =>
        simp only [hflag, ↓reduceIte] at hevent <;>
          cases hevent
    | true =>
        rfl
  have hout : x.out.isD = true := by
    cases hd : x.out.isD with
    | false =>
        simp [replayChain, hd] at hselected
    | true =>
        rfl
  have hinput : y.input.isE = true := by
    cases hi : y.input.isE with
    | false =>
        simp [replayChain, hi] at hselected
    | true =>
        rfl
  have hcarry : y.carryLive = false := by
    cases hc : y.carryLive with
    | false =>
        rfl
    | true =>
        simp [replayChain, hc] at hselected
  exact ⟨hout, hinput, hcarry⟩

/-- A current-clock port-authenticated comparison receipt must
come from the last physical scheduler service of a reached word.
Its OLD-prefix service is the actual genealogy port export.
Consumer: topFreshTailEntranceAcceptPredecessor. -/
theorem topFreshTailEntranceFinalPortWord
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (Z : TopFixedTraceState n)
    (hreach : topClockReached ring C Z)
    (exported : DigitExport (compileAdvice (ceilLogTwo n)) n)
    (hrecord : DigitRecordedExport Z.1.2 exported)
    (htime : exported.time = Z.1.2.clock)
    (hlane : exported.lane = .comparison)
    (hsource :
      exported.source = certSite s (topClockSpan n - 1))
    (hdestination :
      exported.destination = certSite s (topClockSpan n)) :
    ∃ (word : List (Fin n)) (e : Fin n),
      Z.2 = word ++ [e] ∧
      e = certSite s (topClockSpan n - 1) ∧
      topFreshTailGenealogyPortExport ring C s
        (topFixedTraceRun ring C word) e = some exported := by
  have hrecordRun :
      DigitRecordedExport
        (topFixedTraceRun ring C Z.2).1.2 exported := by
    have h := hrecord
    rw [hreach] at h
    exact h
  obtain ⟨before, after, e, hword, hevent⟩ :=
    topFreshTailAuditHistoricalPortReceiptConverse
      ring C s Z.2 exported hrecordRun
      hlane hsource hdestination
  have hserviceTime :=
    topFreshTailAuditHistoricalPortStamp
      ring C s before e exported hevent
  have hclock : Z.1.2.clock = Z.2.length := by
    have hrunClock := topFreshTailAuditRunClock ring C Z.2
    rw [← hreach] at hrunClock
    exact hrunClock
  have hafterNil : after = [] := by
    cases after with
    | nil =>
        rfl
    | cons later remaining =>
        have hlength := congrArg List.length hword
        simp only [List.length_append, List.length_cons,
          List.length_nil] at hlength
        omega
  have hlastWord : Z.2 = before ++ [e] := by
    rw [hafterNil] at hword
    simpa only [List.append_nil] using hword
  obtain ⟨hport, _, _, _, _, _, _, _, _⟩ :=
    topFreshTailAuditSelectedPortFrame
      ring C s (topFixedTraceRun ring C before)
      e exported hevent
  exact ⟨before, e, hlastWord, hport, hevent⟩

/-- The predecessor of a first genuine comparison-tail receipt
is exactly one OLD selected terminal port service away. The
actual recorded source-zero sample supplies the old D value
and true tail, and the actual OLD target guards are E and OFF.
No source-side input or carry restriction is introduced.
Consumer: the hword/hterminalData/hterminalAtom/hyi/hyc
premises of topFreshTailEntranceOfFactorization,
and the entrance in TopClockBundle. -/
theorem topFreshTailEntranceAcceptPredecessor
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (Z : TopFixedTraceState n)
    (hpre : TopFreshTailJointPreAnchor ring C s Z)
    (haccepted : topClockGenuineTailAccepted C s Z) :
    ∃ (word : List (Fin n)) (e : Fin n)
      (P : TopFixedTraceState n)
      (sigma : DigitSample (compileAdvice (ceilLogTwo n)) n)
      (exported : DigitExport (compileAdvice (ceilLogTwo n)) n),
      Z.2 = word ++ [e] ∧
      e = certSite s (topClockSpan n - 1) ∧
      P = topFixedTraceRun ring C word ∧
      Z = topFixedTraceNext ring C P e ∧
      DigitRecordedSample Z.1.2 sigma ∧
      DigitRecordedExport Z.1.2 exported ∧
      sigma.id.lane = .comparison ∧
      sigma.id.site = certSite s 0 ∧
      0 < sigma.id.time ∧
      sigma.tail = true ∧
      exported.time = Z.1.2.clock ∧
      exported.lane = .comparison ∧
      exported.source = certSite s (topClockSpan n - 1) ∧
      exported.destination = certSite s (topClockSpan n) ∧
      exported.operand = some (.sampled sigma.id) ∧
      exported.value = sigma.value ∧
      exported.tail = true ∧
      (P.1.1 e).qOut = .D sigma.value true ∧
      (P.1.2.current e).comparison.out.atom =
        some (.sampled sigma.id) ∧
      (P.1.1 (ring.rightNeighbor e)).qIn = .E ∧
      (P.1.1 (ring.rightNeighbor e)).qCarry = .OFF := by
  obtain ⟨sigma, exported, hrecordSample, hrecordExport,
    hlaneSample, hsiteSample, hpositiveSample, htailSample,
    htimeExport, hlaneExport, hsourceExport,
    hdestinationExport, hoperandExport, hvalueExport,
    htailExport, _⟩ := haccepted
  obtain ⟨word, e, hword, hport, hevent⟩ :=
    topFreshTailEntranceFinalPortWord
      ring C s Z hpre.1 exported hrecordExport
      htimeExport hlaneExport hsourceExport hdestinationExport
  have hpreReached :
      topClockReached ring C (topFixedTraceRun ring C word) :=
    topFreshTailAuditRunReached ring C word
  have hstate :
      Z =
        topFixedTraceNext ring C
          (topFixedTraceRun ring C word) e := by
    have hr : Z = topFixedTraceRun ring C Z.2 := hpre.1
    rw [hword] at hr
    rw [topFreshTailFifoRunSnoc] at hr
    exact hr
  obtain ⟨_, _, hrecordNew, htimeNew, _, _, _, _, _⟩ :=
    topFreshTailAuditSelectedPortFrame
      ring C s (topFixedTraceRun ring C word)
      e exported hevent
  have hservice :=
    topFreshTailAuditFreshComparisonIsSelected
      ring C (topFixedTraceRun ring C word) e
      hpreReached exported hrecordNew htimeNew hlaneExport
  have hportConverse :=
    topFreshTailAuditFreshPortConverse
      ring C s (topFixedTraceRun ring C word) e
      hpreReached exported hrecordNew htimeNew
      hlaneExport hsourceExport hdestinationExport
  have hportConfirmed :=
    (topFreshTailAuditSelectedPortFrame
      ring C s (topFixedTraceRun ring C word)
      e exported hportConverse).1
  have hlocal :
      (digitLaneReplay .comparison
        ((topFixedTraceRun ring C word).1.2.clock + 1)
        e (ring.rightNeighbor e)
        (digitLaneView .comparison
          (piD (topFixedTraceRun ring C word).1.1 e)
          (piD (topFixedTraceRun ring C word).1.1 e).word.beta)
        (digitLaneView .comparison
          (piD (topFixedTraceRun ring C word).1.1
            (ring.rightNeighbor e))
          (piD (topFixedTraceRun ring C word).1.1
            (ring.rightNeighbor e)).word.beta)
        ((topFixedTraceRun ring C word).1.2.current e).comparison
        ((topFixedTraceRun ring C word).1.2.current
          (ring.rightNeighbor e)).comparison).exported =
          some exported := by
    exact hservice
  obtain ⟨_, _, _, _, hoperandOld⟩ :=
    topFreshTailAuditLaneExportFields
      .comparison
      ((topFixedTraceRun ring C word).1.2.clock + 1)
      e (ring.rightNeighbor e)
      (digitLaneView .comparison
        (piD (topFixedTraceRun ring C word).1.1 e)
        (piD (topFixedTraceRun ring C word).1.1 e).word.beta)
      (digitLaneView .comparison
        (piD (topFixedTraceRun ring C word).1.1
          (ring.rightNeighbor e))
        (piD (topFixedTraceRun ring C word).1.1
          (ring.rightNeighbor e)).word.beta)
      ((topFixedTraceRun ring C word).1.2.current e).comparison
      ((topFixedTraceRun ring C word).1.2.current
        (ring.rightNeighbor e)).comparison
      exported hlocal
  obtain ⟨hvalueOld, htailOld⟩ :=
    topFreshTailAuditLaneExportPayload
      .comparison
      ((topFixedTraceRun ring C word).1.2.clock + 1)
      e (ring.rightNeighbor e)
      (digitLaneView .comparison
        (piD (topFixedTraceRun ring C word).1.1 e)
        (piD (topFixedTraceRun ring C word).1.1 e).word.beta)
      (digitLaneView .comparison
        (piD (topFixedTraceRun ring C word).1.1
          (ring.rightNeighbor e))
        (piD (topFixedTraceRun ring C word).1.1
          (ring.rightNeighbor e)).word.beta)
      ((topFixedTraceRun ring C word).1.2.current e).comparison
      ((topFixedTraceRun ring C word).1.2.current
        (ring.rightNeighbor e)).comparison
      exported hlocal
  obtain ⟨hsourceD, htargetE, htargetOff⟩ :=
    topFreshTailEntranceExportReplayGuards
      .comparison
      ((topFixedTraceRun ring C word).1.2.clock + 1)
      e (ring.rightNeighbor e)
      (digitLaneView .comparison
        (piD (topFixedTraceRun ring C word).1.1 e)
        (piD (topFixedTraceRun ring C word).1.1 e).word.beta)
      (digitLaneView .comparison
        (piD (topFixedTraceRun ring C word).1.1
          (ring.rightNeighbor e))
        (piD (topFixedTraceRun ring C word).1.1
          (ring.rightNeighbor e)).word.beta)
      ((topFixedTraceRun ring C word).1.2.current e).comparison
      ((topFixedTraceRun ring C word).1.2.current
        (ring.rightNeighbor e)).comparison
      exported hlocal
  have hatom :
      ((topFixedTraceRun ring C word).1.2.current
        e).comparison.out.atom =
          some (.sampled sigma.id) :=
    hoperandOld.symm.trans hoperandExport
  have hdata :
      ((topFixedTraceRun ring C word).1.1 e).qOut =
        .D sigma.value true := by
    have hd :
        ((topFixedTraceRun ring C word).1.1 e).qOut.isD =
          true := hsourceD
    cases hq : ((topFixedTraceRun ring C word).1.1 e).qOut with
    | E =>
        have hfalse : False := by
          simpa [hq, OutTok.isD] using hd
        exact False.elim hfalse
    | U =>
        have hfalse : False := by
          simpa [hq, OutTok.isD] using hd
        exact False.elim hfalse
    | D value tail =>
        have hvOld : exported.value = value := by
          change exported.value =
            outV (compileAdvice (ceilLogTwo n))
              ((topFixedTraceRun ring C word).1.1 e).qOut
            at hvalueOld
          rw [hq] at hvalueOld
          exact hvalueOld
        have htOld : exported.tail = tail := by
          change exported.tail =
            outT ((topFixedTraceRun ring C word).1.1 e).qOut
            at htailOld
          rw [hq] at htailOld
          exact htailOld
        have hv : value = sigma.value :=
          hvOld.symm.trans hvalueExport
        have ht : tail = true :=
          htOld.symm.trans htailExport
        rw [hv, ht]
  have hyi :
      ((topFixedTraceRun ring C word).1.1
        (ring.rightNeighbor e)).qIn = .E := by
    have hinput :
        ((topFixedTraceRun ring C word).1.1
          (ring.rightNeighbor e)).qIn.isE = true := htargetE
    cases hi : ((topFixedTraceRun ring C word).1.1
      (ring.rightNeighbor e)).qIn with
    | E =>
        rfl
    | P value bit =>
        have hfalse : False := by
          simpa [hi, InTok.isE] using hinput
        exact False.elim hfalse
    | S value bit =>
        have hfalse : False := by
          simpa [hi, InTok.isE] using hinput
        exact False.elim hfalse
    | X =>
        have hfalse : False := by
          simpa [hi, InTok.isE] using hinput
        exact False.elim hfalse
  have hyc :
      ((topFixedTraceRun ring C word).1.1
        (ring.rightNeighbor e)).qCarry = .OFF := by
    have hoff :
        ((topFixedTraceRun ring C word).1.1
          (ring.rightNeighbor e)).qCarry.isL = false := htargetOff
    cases hc : ((topFixedTraceRun ring C word).1.1
      (ring.rightNeighbor e)).qCarry with
    | OFF =>
        rfl
    | L bit err =>
        have hfalse : False := by
          simpa [hc, QCarry.isL] using hoff
        exact False.elim hfalse
  refine ⟨word, e, topFixedTraceRun ring C word,
    sigma, exported, hword, hportConfirmed, rfl, hstate,
    hrecordSample, hrecordExport, hlaneSample, hsiteSample,
    hpositiveSample, htailSample, htimeExport, hlaneExport,
    hsourceExport, hdestinationExport, hoperandExport,
    hvalueExport, htailExport, hdata, hatom, hyi, hyc⟩

end L3

#print axioms L3.topFreshTailEntranceExportReplayGuards
#print axioms L3.topFreshTailEntranceFinalPortWord
#print axioms L3.topFreshTailEntranceAcceptPredecessor
