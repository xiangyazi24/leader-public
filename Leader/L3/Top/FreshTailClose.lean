import Leader.L3.Top.FreshTailGenealogy
import Leader.L3.Top.FreshTailFifo
import Leader.L3.Top.RepairedClasses

/-!
Q7c P.3 partial physical-to-genealogy bridge.

The merged causal FIFO records occupied source slots, carrier
identity and causal nonpassing, but does not identify the
DigitSample.id in every later DigitRecordedExport. Accordingly
this module does not assert TopFreshTailBackwardsPurity or
construct a TopFreshTailAdaptedLedger without its physical
receipt/source-history and ranked-contact obligations.

Consumer: P.3 port-export charge and repaired phase bundle.
-/

namespace L3

open Classical

set_option autoImplicit false
set_option Elab.async false

/-- A reached P.3 fixed-public trace carries the genuine,
historically reconstructed causal source queue. Consumer:
port-ready carrier identification for P.3 FIFO charging. -/
theorem topFreshTailCloseReachedQueue
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hn : 5 ≤ n)
    (hbad : HeadlineDigit.BadCompletePair C s)
    (Z : TopFixedTraceState n)
    (hreach : topClockReached ring C Z) :
    TopFreshTailCausalQueue ring C s Z := by
  have hrun :=
    topFreshTailCausalQueueRun ring C s hn hbad Z.2
  rw [← hreach] at hrun
  exact hrun

/-- The physical source-terminal port-ready D always has a
nonempty genealogy carrier at its precise last source slot;
that carrier was born by the old audit clock. This is the
nonempty-carrier half of the historical receipt bridge.
Consumer: P.3 accepted-source receipt authentication. -/
theorem topFreshTailCloseReadyCarrier
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hn : 5 ≤ n)
    (hbad : HeadlineDigit.BadCompletePair C s)
    (Z : TopFixedTraceState n)
    (hreach : topClockReached ring C Z)
    (atom : Option (DigitAtom n))
    (hready : topClockPortReady s atom Z) :
    ∃ carrier : TopFreshTailCarrier (topClockSpan n),
      (topFreshTailGenealogy ring C s Z).slots
        (⟨topClockSpan n - 1,
          show topClockSpan n - 1 < topClockSpan n by
            have h := cert_rho_ge_three n hn
            change 3 ≤ topClockSpan n at h
            omega⟩ : Fin (topClockSpan n)) = some carrier ∧
      carrier.born ≤ Z.1.2.clock := by
  have hwidth : 0 < topClockSpan n := by
    have h := cert_rho_ge_three n hn
    change 3 ≤ topClockSpan n at h
    omega
  have hqueue :=
    topFreshTailCloseReachedQueue ring C s hn hbad Z hreach
  obtain ⟨value, tail, hsource, _⟩ := hready
  cases hslot :
      (topFreshTailGenealogy ring C s Z).slots
        (⟨topClockSpan n - 1,
          show topClockSpan n - 1 < topClockSpan n by omega⟩ :
          Fin (topClockSpan n)) with
  | none =>
      have hE :=
        (hqueue.slot
          (⟨topClockSpan n - 1,
            show topClockSpan n - 1 < topClockSpan n by omega⟩ :
            Fin (topClockSpan n))).2 hslot
      rw [hsource] at hE
      cases hE
  | some carrier =>
      exact ⟨carrier, rfl, hqueue.age _ carrier hslot⟩

/-- When the genuine genealogy port event is present, the
one-step consumed list gains the old source-carrier's
nonempty origin, stamped with the selected service time.
Consumer: the receipt-to-ancestry map before first-tail charge. -/
theorem topFreshTailClosePortEventOrigin
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (G : TopFreshTailGenealogyState n)
    (e : Fin n)
    (hspan : 0 < topClockSpan n)
    (exported : DigitExport (compileAdvice (ceilLogTwo n)) n)
    (hevent :
      topFreshTailGenealogyPortExport
        ring C s G.trace e = some exported)
    (carrier : TopFreshTailCarrier (topClockSpan n))
    (hslot :
      G.slots
        (⟨topClockSpan n - 1,
          show topClockSpan n - 1 < topClockSpan n by omega⟩ :
          Fin (topClockSpan n)) = some carrier) :
    (topFreshTailGenealogyStep ring C s G e).consumed =
      G.consumed ++
        [(G.trace.1.2.clock + 1, some carrier.origin)] := by
  unfold topFreshTailGenealogyStep
  simp [hspan, hevent, hslot]

/-- An actually ready port paired with the literal genealogy
export event has a chronological nonmissing-origin entry.
This does not yet prove equality of that origin with the
recorded DigitSample.id or injectivity of its eventual charge.
Consumer: the physical/audit source-event bridge in P.3. -/
theorem topFreshTailCloseReadyPortEventOrigin
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (hn : 5 ≤ n)
    (hbad : HeadlineDigit.BadCompletePair C s)
    (Z : TopFixedTraceState n)
    (hreach : topClockReached ring C Z)
    (atom : Option (DigitAtom n))
    (hready : topClockPortReady s atom Z)
    (e : Fin n)
    (exported : DigitExport (compileAdvice (ceilLogTwo n)) n)
    (hevent :
      topFreshTailGenealogyPortExport
        ring C s Z e = some exported) :
    ∃ carrier : TopFreshTailCarrier (topClockSpan n),
      (topFreshTailGenealogy ring C s Z).slots
        (⟨topClockSpan n - 1,
          show topClockSpan n - 1 < topClockSpan n by
            have h := cert_rho_ge_three n hn
            change 3 ≤ topClockSpan n at h
            omega⟩ : Fin (topClockSpan n)) = some carrier ∧
      carrier.born ≤ Z.1.2.clock ∧
      (topFreshTailGenealogyStep
        ring C s (topFreshTailGenealogy ring C s Z) e).consumed =
        (topFreshTailGenealogy ring C s Z).consumed ++
          [(Z.1.2.clock + 1, some carrier.origin)] := by
  have hspan : 0 < topClockSpan n := by
    have h := cert_rho_ge_three n hn
    change 3 ≤ topClockSpan n at h
    omega
  obtain ⟨carrier, hslot, hage⟩ :=
    topFreshTailCloseReadyCarrier
      ring C s hn hbad Z hreach atom hready
  have htrace :=
    topFreshTailGenealogyTraceReached ring C s Z hreach
  have hghostEvent :
      topFreshTailGenealogyPortExport ring C s
        (topFreshTailGenealogy ring C s Z).trace e =
          some exported := by
    rw [htrace]
    exact hevent
  have hconsumed :=
    topFreshTailClosePortEventOrigin
      ring C s (topFreshTailGenealogy ring C s Z) e
      hspan exported hghostEvent carrier hslot
  refine ⟨carrier, hslot, hage, ?_⟩
  rw [htrace] at hconsumed
  exact hconsumed

/-- The repaired cut package keeps the first genuine,
permanently pure source-tail class unchanged; only later
coloured/settled/unfavourable cuts are strengthened.
Consumer: the first-tail clause of TopClockPhaseBundle. -/
theorem topFreshTailCloseRepairedFirstTail
    {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n)
    (Z : TopFixedTraceState n) :
    (MarkedCells.topClockRepairedClasses ring C s).firstTail Z ↔
      topFreshTailPermanentCut ring C s Z := by
  rfl

end L3
#print axioms L3.topFreshTailCloseReachedQueue
#print axioms L3.topFreshTailCloseReadyCarrier
#print axioms L3.topFreshTailClosePortEventOrigin
#print axioms L3.topFreshTailCloseReadyPortEventOrigin
#print axioms L3.topFreshTailCloseRepairedFirstTail
