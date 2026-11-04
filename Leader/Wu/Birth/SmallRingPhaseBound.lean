import Leader.Wu.Birth.ShortDoneTerminalNoHitCount


set_option autoImplicit false


namespace BirthSmallRingWrapper


open PPLL PPLLResearchFormulation PPLLExpiringComparisonRepair


variable {n ψ width κ τ : Nat}


/-- The exact small-ring interface needed by the global birth composition.
`postMass` is a numerator lower bound over the original uniform scheduler
words of length `postHorizon`. -/
def SmallRingBirthPhaseBound
    (hψ : 0 < ψ) (hwidth : 0 < width) (hle : width ≤ ψ)
    (ring : DirectedRing n)
    (C : Fin n → ExpiringAgentState ψ κ τ)
    (firstHorizon postHorizon postMass : Nat) : Prop :=
  2 ≤ n ∧ n ≤ 3 ∧
  BirthShortDoneTerminalFirstHit.Leaderless C ∧
  n * FixedSpanRenewalPayload.wordSum n firstHorizon
      (BirthShortDoneTerminalNoHitCount.physicalNoHitBit
        hψ hwidth hle ring C) ≤
    n ^ firstHorizon ∧
  ∀ (pre : List (Fin n)) (e : Fin n),
    pre.length < firstHorizon →
    BirthShortDoneTerminalObserver.NoBirthAlong
      hψ hwidth hle ring C pre →
    let D := pre.foldl
      (BirthShortDoneTerminalConsumer.step hψ hwidth hle ring) C
    BirthShortDoneTerminalObserver.birthEvent
      hψ hwidth hle (D e) (D (ring.rightNeighbor e)) = true →
    let E := BirthShortDoneTerminalConsumer.step
      hψ hwidth hle ring D e
    postMass ≤
      FixedSpanRenewalPayload.wordSum n postHorizon
        (BirthShortDoneTerminalNoHitCount.noBirthBit
          hψ hwidth hle ring E)


end BirthSmallRingWrapper
