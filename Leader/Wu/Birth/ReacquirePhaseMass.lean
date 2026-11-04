import Leader.Wu.Birth.ReacquireReentryMass

set_option autoImplicit false
set_option Elab.async false
set_option pp.structureInstances false

namespace BirthB1ReacquirePhaseMass

open PPLL PPLLRepair PPLLResearchFormulation
  PPLLExpiringComparisonRepair
open BirthB1ReacquireReentryMass

variable {n psi kappa tau : Nat}

abbrev FC (n psi kappa tau : Nat) :=
  BirthPhaseWait2BlockProgress.FC n psi kappa tau

/-- The adopted two-phase B4 Reacquire quantitative leaf. -/
abbrev ReacquirePhaseMass
    (hpsi : 0 < psi) (h2 : 2 <= psi) (hn : 4 <= n)
    (kappa tau : Nat) (ring : DirectedRing n) (anchor : Fin n) : Prop :=
  FallbackReacquireMass
    hpsi h2 hn kappa tau ring anchor

/-- Scheduler-stable progress package needed before doing any probability.
`front` is proof-side only; it adds no protocol state. -/
def ReacquireFrontDrift
    (hpsi : 0 < psi) (h2 : 2 <= psi) (hn : 4 <= n)
    (kappa tau : Nat) (ring : DirectedRing n) (anchor : Fin n)
    (front : FC n psi kappa tau -> Nat) : Prop :=
  (forall C : FC n psi kappa tau,
    BirthPhaseWait2BlockProgress.Reacquire
        hpsi h2 hn kappa tau ring anchor C ->
      front C < n) /\
  (forall C : FC n psi kappa tau,
    BirthPhaseWait2BlockProgress.Reacquire
        hpsi h2 hn kappa tau ring anchor C ->
    forall e : Fin n,
      let D := BirthPhaseWait2BlockProgress.currentStep2 hpsi h2 ring C e
      BirthPhaseWait2BlockProgress.target
          hpsi h2 kappa ring C [e] = true \/
        BirthPhaseWait2BlockProgress.Carrier
          hpsi h2 hn ring anchor D \/
        (BirthPhaseWait2BlockProgress.Reacquire
            hpsi h2 hn kappa tau ring anchor D /\
          front C <= front D)) /\
  (forall C : FC n psi kappa tau,
    BirthPhaseWait2BlockProgress.Reacquire
        hpsi h2 hn kappa tau ring anchor C ->
    exists e : Fin n,
      let D := BirthPhaseWait2BlockProgress.currentStep2 hpsi h2 ring C e
      BirthPhaseWait2BlockProgress.target
          hpsi h2 kappa ring C [e] = true \/
        BirthPhaseWait2BlockProgress.Carrier
          hpsi h2 hn ring anchor D \/
        (BirthPhaseWait2BlockProgress.Reacquire
            hpsi h2 hn kappa tau ring anchor D /\
          front C < front D))

/-- Exact protocol leaf to feed to the later finite-word lower-tail argument. -/
def ReacquireFrontDriftLeaf
    (hpsi : 0 < psi) (h2 : 2 <= psi) (hn : 4 <= n)
    (kappa tau : Nat) (ring : DirectedRing n) (anchor : Fin n) : Prop :=
  exists front : FC n psi kappa tau -> Nat,
    ReacquireFrontDrift
      hpsi h2 hn kappa tau ring anchor front

/-- The old B4 rank clause is literally tracked-count nondecrease.  This is
why width-two `shortCountReset` has to be excluded by the Reacquire invariant. -/
theorem fallbackReacquireMono_iff_shortCountMonotone
    (hpsi : 0 < psi) (h2 : 2 <= psi) (hn : 4 <= n)
    (kappa tau : Nat) (ring : DirectedRing n) (anchor : Fin n) :
    FallbackReacquireMono
        hpsi h2 hn kappa tau ring anchor <->
      forall C : FC n psi kappa tau,
        BirthPhaseWait2BlockProgress.Reacquire
            hpsi h2 hn kappa tau ring anchor C ->
        forall u : List (Fin n),
          u.length = fallbackReacquireL n ->
          BirthPhaseWait2BlockProgress.target
              hpsi h2 kappa ring C u = false ->
            BirthPhaseWait2BlockProgress.shortCountAt ring anchor C <=
              BirthPhaseWait2BlockProgress.shortCountAt ring anchor
                (prefixEndpoint hpsi h2 ring C u) := by
  constructor
  · intro h C hR u hlen ht
    unfold FallbackReacquireMono at h
    exact
      (BirthPhaseWait2BlockProgress.rank_le_iff_shortCount_le
        kappa ring anchor C
          (prefixEndpoint hpsi h2 ring C u)).1
        (h C hR u hlen ht)
  · intro h
    unfold FallbackReacquireMono
    intro C hR u hlen ht
    exact
      (BirthPhaseWait2BlockProgress.rank_le_iff_shortCount_le
        kappa ring anchor C
          (prefixEndpoint hpsi h2 ring C u)).2
        (h C hR u hlen ht)

/-! Smallest-ring literal checks. -/

private theorem hpsi2 : 0 < 2 := by decide
private theorem h2 : 2 <= 2 := by decide
private theorem hn4 : 4 <= 4 := by decide

/-- The public boundary successor, reused as a real Reacquire start. -/
def ringFourReacquire : FC 4 2 2 3 :=
  BirthPhaseWait2BlockProgress.currentStep2
    hpsi2 h2
    BirthPhaseWait2Transfer.boundaryRing4
    BirthPhaseWait2Transfer.boundaryConfig4
    BirthPhaseWait2Transfer.boundaryEdge4

theorem ringFourReacquire_is_reacquire :
    BirthPhaseWait2BlockProgress.Reacquire
      hpsi2 h2 hn4 2 3
      BirthPhaseWait2Transfer.boundaryRing4
      BirthPhaseWait2Transfer.boundaryAnchor4
      ringFourReacquire := by
  simpa [ringFourReacquire] using
    BirthPhaseB3BridgeStageA.boundary_fixture_successor_is_reacquire

/-- One literal opposite-edge row from the Reacquire fixture. -/
def ringFourPad : FC 4 2 2 3 :=
  BirthPhaseWait2BlockProgress.currentStep2
    hpsi2 h2
    BirthPhaseWait2Transfer.boundaryRing4
    ringFourReacquire (3 : Fin 4)

theorem ringFour_pad_preCap :
    BirthShortDoneTerminalPassiveR4.RowPreCap2
      hpsi2 h2 2 BirthPhaseWait2Transfer.boundaryRing4
      ringFourReacquire (3 : Fin 4) := by
  unfold BirthShortDoneTerminalPassiveR4.RowPreCap2
    BirthShortDoneTerminalPassiveR4.RowCap2
  decide

set_option maxHeartbeats 200000000 in
set_option maxRecDepth 131072 in
theorem ringFour_pad_count_stutters :
    BirthPhaseWait2BlockProgress.shortCountAt
        BirthPhaseWait2Transfer.boundaryRing4
        BirthPhaseWait2Transfer.boundaryAnchor4 ringFourReacquire =
      BirthPhaseWait2BlockProgress.shortCountAt
        BirthPhaseWait2Transfer.boundaryRing4
        BirthPhaseWait2Transfer.boundaryAnchor4 ringFourPad := by
  decide

set_option maxHeartbeats 200000000 in
set_option maxRecDepth 131072 in
theorem ringFour_pad_rank_stutters :
    BirthPhaseWait2BlockProgress.rank 2
        BirthPhaseWait2Transfer.boundaryRing4
        BirthPhaseWait2Transfer.boundaryAnchor4 ringFourReacquire =
      BirthPhaseWait2BlockProgress.rank 2
        BirthPhaseWait2Transfer.boundaryRing4
        BirthPhaseWait2Transfer.boundaryAnchor4 ringFourPad := by
  decide

theorem fallbackReacquireL_four :
    fallbackReacquireL 4 = 256 := by
  decide

end BirthB1ReacquirePhaseMass

#print axioms BirthB1ReacquirePhaseMass.fallbackReacquireMono_iff_shortCountMonotone
#print axioms BirthB1ReacquirePhaseMass.ringFourReacquire_is_reacquire
#print axioms BirthB1ReacquirePhaseMass.ringFour_pad_preCap
#print axioms BirthB1ReacquirePhaseMass.ringFour_pad_count_stutters
#print axioms BirthB1ReacquirePhaseMass.ringFour_pad_rank_stutters
#print axioms BirthB1ReacquirePhaseMass.fallbackReacquireL_four
