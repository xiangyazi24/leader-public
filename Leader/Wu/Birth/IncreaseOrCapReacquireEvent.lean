import Leader.Wu.Birth.IncreaseOrCapCarrierBridge

set_option autoImplicit false
set_option Elab.async false
set_option pp.structureInstances false

namespace BirthPhaseB3ReacquireEvent

open PPLL PPLLRepair PPLLResearchFormulation
  PPLLExpiringComparisonRepair

variable {n psi kappa tau : Nat}

abbrev FC (n psi kappa tau : Nat) :=
  BirthPhaseWait2BlockProgress.FC n psi kappa tau

/-! ## The Reacquire event and the phase-dependent union -/

/-- Exact B3 terminal outcome required from a successful Reacquire word. -/
def Resolves
    (hpsi : 0 < psi) (h2 : 2 <= psi)
    (kappa : Nat) (ring : DirectedRing n) (anchor : Fin n)
    (C : FC n psi kappa tau) (u : List (Fin n)) : Prop :=
  BirthPhaseWait2BlockProgress.target
      hpsi h2 kappa ring C u = true \/
    BirthPhaseWait2BlockProgress.shortCountAt ring anchor C <
      BirthPhaseWait2BlockProgress.shortCountAt ring anchor
        (BirthPhaseGenericRenewal.rawEndpoint
          (BirthPhaseWait2BlockProgress.currentStep2 hpsi h2 ring)
          C u)

/-- B1-side success event on the original scheduler alphabet.  The length
condition is part of the event, so this is literally an `L n`-word event. -/
def ReacquireSuccess
    (hpsi : 0 < psi) (h2 : 2 <= psi)
    (kappa : Nat) (ring : DirectedRing n) (anchor : Fin n)
    (C : FC n psi kappa tau) (u : List (Fin n)) : Prop :=
  u.length = BirthPhaseWait2BlockProgress.L n /\
    Resolves hpsi h2 kappa ring anchor C u

/-- The existing raw B3 event, exposed as a relation on the full current
configuration by carrying the proof that the start is a genuine Carrier. -/
def CarrierRawSuccess
    (hpsi : 0 < psi) (h2 : 2 <= psi) (hn : 4 <= n)
    (kappa tau : Nat) (ring : DirectedRing n) (anchor : Fin n)
    (C : FC n psi kappa tau) (u : List (Fin n)) : Prop :=
  exists hC : BirthPhaseWait2BlockProgress.Carrier
      hpsi h2 hn ring anchor C,
    BirthPhaseB3DirtySuccess.DirtySuccess
      hpsi h2 hn ring anchor
      (⟨C, hC⟩ : BirthPhaseB3DirtySuccess.CarrierState
        (kappa := kappa) (tau := tau)
        hpsi h2 hn ring anchor) u

/-- Reacquire branch of the disjoint union. -/
def TaggedReacquireSuccess
    (hpsi : 0 < psi) (h2 : 2 <= psi) (hn : 4 <= n)
    (kappa tau : Nat) (ring : DirectedRing n) (anchor : Fin n)
    (C : FC n psi kappa tau) (u : List (Fin n)) : Prop :=
  BirthPhaseWait2BlockProgress.Reacquire
      hpsi h2 hn kappa tau ring anchor C /\
    ReacquireSuccess hpsi h2 kappa ring anchor C u

/-- One B4 relation, phase-dependent only through the starting state:
Carrier uses the certified raw B3 dirty event; Reacquire uses the B1 event. -/
def PhaseDirtySuccess
    (hpsi : 0 < psi) (h2 : 2 <= psi) (hn : 4 <= n)
    (kappa tau : Nat) (ring : DirectedRing n) (anchor : Fin n) :
    BirthPhaseWait2BlockProgress.DirtySuccessRel n psi kappa tau :=
  fun C u =>
    CarrierRawSuccess hpsi h2 hn kappa tau ring anchor C u \/
      TaggedReacquireSuccess
        hpsi h2 hn kappa tau ring anchor C u

/-- The two summands cannot both occur. -/
theorem carrierRawSuccess_taggedReacquireSuccess_disjoint
    (hpsi : 0 < psi) (h2 : 2 <= psi) (hn : 4 <= n)
    (kappa tau : Nat) (ring : DirectedRing n) (anchor : Fin n)
    (C : FC n psi kappa tau) (u : List (Fin n)) :
    Not
      (CarrierRawSuccess hpsi h2 hn kappa tau ring anchor C u /\
        TaggedReacquireSuccess
          hpsi h2 hn kappa tau ring anchor C u) := by
  rintro ⟨hraw, htag⟩
  rcases hraw with ⟨hC, _⟩
  rcases htag with ⟨hR, _⟩
  exact
    (BirthPhaseB3BridgeStageA.reacquire_not_carrier
      hpsi h2 hn kappa tau ring anchor C hR) hC

/-- On a Carrier start the union is exactly the previously certified raw event. -/
theorem phaseDirty_carrierAgreement
    (hpsi : 0 < psi) (h2 : 2 <= psi) (hn : 4 <= n)
    (kappa tau : Nat) (ring : DirectedRing n) (anchor : Fin n) :
    BirthPhaseB3BridgeStageA.CarrierDirtyAgreement
      hpsi h2 hn kappa tau ring anchor
      (PhaseDirtySuccess hpsi h2 hn kappa tau ring anchor) := by
  intro C hC u
  constructor
  · intro hs
    change
      CarrierRawSuccess hpsi h2 hn kappa tau ring anchor C u \/
        TaggedReacquireSuccess
          hpsi h2 hn kappa tau ring anchor C u at hs
    rcases hs with hraw | htag
    · rcases hraw with ⟨hC', hdirty⟩
      have hx :
          (⟨C, hC'⟩ : BirthPhaseB3DirtySuccess.CarrierState
            (kappa := kappa) (tau := tau)
            hpsi h2 hn ring anchor) =
          (⟨C, hC⟩ : BirthPhaseB3DirtySuccess.CarrierState
            (kappa := kappa) (tau := tau)
            hpsi h2 hn ring anchor) := by
        apply Subtype.ext
        rfl
      rw [hx] at hdirty
      exact hdirty
    · rcases htag with ⟨hR, _⟩
      exact False.elim
        ((BirthPhaseB3BridgeStageA.reacquire_not_carrier
          hpsi h2 hn kappa tau ring anchor C hR) hC)
  · intro hdirty
    change
      CarrierRawSuccess hpsi h2 hn kappa tau ring anchor C u \/
        TaggedReacquireSuccess
          hpsi h2 hn kappa tau ring anchor C u
    exact Or.inl ⟨hC, hdirty⟩

/-- On a Reacquire start the Carrier summand disappears, so the full relation
is exactly the B1 Reacquire word event. -/
theorem phaseDirty_reacquire_iff
    (hpsi : 0 < psi) (h2 : 2 <= psi) (hn : 4 <= n)
    (kappa tau : Nat) (ring : DirectedRing n) (anchor : Fin n)
    (C : FC n psi kappa tau)
    (hR : BirthPhaseWait2BlockProgress.Reacquire
      hpsi h2 hn kappa tau ring anchor C)
    (u : List (Fin n)) :
    PhaseDirtySuccess hpsi h2 hn kappa tau ring anchor C u <->
      ReacquireSuccess hpsi h2 kappa ring anchor C u := by
  constructor
  · intro hs
    change
      CarrierRawSuccess hpsi h2 hn kappa tau ring anchor C u \/
        TaggedReacquireSuccess
          hpsi h2 hn kappa tau ring anchor C u at hs
    rcases hs with hraw | htag
    · rcases hraw with ⟨hC, _⟩
      exact False.elim
        ((BirthPhaseB3BridgeStageA.reacquire_not_carrier
          hpsi h2 hn kappa tau ring anchor C hR) hC)
    · exact htag.2
  · intro hs
    change
      CarrierRawSuccess hpsi h2 hn kappa tau ring anchor C u \/
        TaggedReacquireSuccess
          hpsi h2 hn kappa tau ring anchor C u
    exact Or.inr ⟨hR, hs⟩

/-! ## Exact Stage-A pointwise statements -/

/-- The dirty-qualified replacement for the false unconditional
`BoundaryCaseResolvesBridge` from Stage A. -/
def BoundaryDirtyCaseResolvesBridge
    (hpsi : 0 < psi) (h2 : 2 <= psi) (hn : 4 <= n)
    (kappa tau : Nat) (ring : DirectedRing n) (anchor : Fin n)
    (DirtySuccess :
      BirthPhaseWait2BlockProgress.DirtySuccessRel n psi kappa tau) : Prop :=
  forall C : FC n psi kappa tau,
    BirthPhaseWait2BlockProgress.Carrier
        hpsi h2 hn ring anchor C ->
    forall u : List (Fin n),
      u.length = BirthPhaseWait2BlockProgress.L n ->
      DirtySuccess C u ->
      BirthPhaseB3BridgeStageA.BoundaryCaseWithin
          hpsi h2 hn kappa tau ring anchor C u ->
        BirthPhaseWait2BlockProgress.target
            hpsi h2 kappa ring C u = true \/
          BirthPhaseWait2BlockProgress.shortCountAt ring anchor C <
            BirthPhaseWait2BlockProgress.shortCountAt ring anchor
              (BirthPhaseGenericRenewal.rawEndpoint
                (BirthPhaseWait2BlockProgress.currentStep2 hpsi h2 ring)
                C u)

/-- Specialized dirty-qualified Carrier boundary obligation for the new union. -/
abbrev PhaseBoundaryDirtyCaseResolvesBridge
    (hpsi : 0 < psi) (h2 : 2 <= psi) (hn : 4 <= n)
    (kappa tau : Nat) (ring : DirectedRing n) (anchor : Fin n) : Prop :=
  BoundaryDirtyCaseResolvesBridge
    hpsi h2 hn kappa tau ring anchor
    (PhaseDirtySuccess hpsi h2 hn kappa tau ring anchor)

/-- The Reacquire pointwise Stage-A obligation closes immediately for the
semantic B1 event: success was defined to be exactly the required outcome. -/
theorem phaseDirty_reacquireStartBridge
    (hpsi : 0 < psi) (h2 : 2 <= psi) (hn : 4 <= n)
    (kappa tau : Nat) (ring : DirectedRing n) (anchor : Fin n) :
    BirthPhaseB3BridgeStageA.ReacquireStartBridge
      hpsi h2 hn kappa tau ring anchor
      (PhaseDirtySuccess hpsi h2 hn kappa tau ring anchor) := by
  intro C hR u _hlen hs
  have hrs :=
    (phaseDirty_reacquire_iff
      hpsi h2 hn kappa tau ring anchor C hR u).mp hs
  exact hrs.2

/-! ## Exact Reacquire mass leaf -/

/-- Classical indicator only for finite word counting; the protocol/event
itself remains the proposition `ReacquireSuccess`. -/
noncomputable def ReacquireSuccessBit
    (hpsi : 0 < psi) (h2 : 2 <= psi)
    (kappa : Nat) (ring : DirectedRing n) (anchor : Fin n)
    (C : FC n psi kappa tau) (u : List (Fin n)) : Nat :=
  @ite Nat (ReacquireSuccess hpsi h2 kappa ring anchor C u)
    (Classical.propDecidable _) 1 0

/-- This is the one genuinely missing quantitative B1 statement. -/
def ReacquireSuccessMass
    (hpsi : 0 < psi) (h2 : 2 <= psi) (hn : 4 <= n)
    (kappa tau : Nat) (ring : DirectedRing n) (anchor : Fin n) : Prop :=
  forall C : FC n psi kappa tau,
    BirthPhaseWait2BlockProgress.Reacquire
        hpsi h2 hn kappa tau ring anchor C ->
      n ^ BirthPhaseWait2BlockProgress.L n <=
        BirthPhaseWait2BlockProgress.Q *
          FixedSpanRenewalPayload.wordSum n
            (BirthPhaseWait2BlockProgress.L n)
            (fun u =>
              ReacquireSuccessBit
                hpsi h2 kappa ring anchor C u)

/-- The phase relation is classically decidable for the finite word sum used by
Stage A.  No new axiom is introduced; this is Lean's standard classical
propositional decidability. -/
noncomputable instance phaseDirtySuccess_decidable
    (hpsi : 0 < psi) (h2 : 2 <= psi) (hn : 4 <= n)
    (kappa tau : Nat) (ring : DirectedRing n) (anchor : Fin n)
    (C : FC n psi kappa tau) (u : List (Fin n)) :
    Decidable
      (PhaseDirtySuccess
        hpsi h2 hn kappa tau ring anchor C u) :=
  Classical.propDecidable _

/-- On a Reacquire start, the Stage-A indicator for the combined event is
pointwise the indicator of `ReacquireSuccess`. -/
theorem phaseDirty_reacquire_weight_eq
    (hpsi : 0 < psi) (h2 : 2 <= psi) (hn : 4 <= n)
    (kappa tau : Nat) (ring : DirectedRing n) (anchor : Fin n)
    (C : FC n psi kappa tau)
    (hR : BirthPhaseWait2BlockProgress.Reacquire
      hpsi h2 hn kappa tau ring anchor C) :
    (fun u : List (Fin n) =>
      if PhaseDirtySuccess
          hpsi h2 hn kappa tau ring anchor C u
      then 1 else 0) =
      (fun u => ReacquireSuccessBit
        hpsi h2 kappa ring anchor C u) := by
  funext u
  have hiff :=
    phaseDirty_reacquire_iff
      hpsi h2 hn kappa tau ring anchor C hR u
  unfold ReacquireSuccessBit
  by_cases hs : ReacquireSuccess hpsi h2 kappa ring anchor C u
  · have hp :
        PhaseDirtySuccess
          hpsi h2 hn kappa tau ring anchor C u :=
      hiff.mpr hs
    simp [hs, hp]
  · have hp :
        Not (PhaseDirtySuccess
          hpsi h2 hn kappa tau ring anchor C u) := by
      intro hphase
      exact hs (hiff.mp hphase)
    simp [hs, hp]

/-- Exact specialization of Stage A's `ReacquireSourceMass`: there is no
further adapter theorem to prove.  The Stage-A source is equivalent to the one
new B1 original-word mass statement above. -/
theorem phaseDirty_reacquireSourceMass_iff
    (hpsi : 0 < psi) (h2 : 2 <= psi) (hn : 4 <= n)
    (kappa tau : Nat) (ring : DirectedRing n) (anchor : Fin n) :
    BirthPhaseB3BridgeStageA.ReacquireSourceMass
        hpsi h2 hn kappa tau ring anchor
        (PhaseDirtySuccess hpsi h2 hn kappa tau ring anchor) <->
      ReacquireSuccessMass
        hpsi h2 hn kappa tau ring anchor := by
  constructor
  · intro hmass C hR
    have hm := hmass C hR
    rw [phaseDirty_reacquire_weight_eq
      hpsi h2 hn kappa tau ring anchor C hR] at hm
    exact hm
  · intro hmass C hR
    have hm := hmass C hR
    rw [phaseDirty_reacquire_weight_eq
      hpsi h2 hn kappa tau ring anchor C hR]
    exact hm

/-- Convenient forward adapter: once the missing B1 mass theorem is supplied,
Stage A receives exactly its existing `ReacquireSourceMass`. -/
theorem phaseDirty_reacquireSourceMass
    (hpsi : 0 < psi) (h2 : 2 <= psi) (hn : 4 <= n)
    (kappa tau : Nat) (ring : DirectedRing n) (anchor : Fin n)
    (hmass : ReacquireSuccessMass
      hpsi h2 hn kappa tau ring anchor) :
    BirthPhaseB3BridgeStageA.ReacquireSourceMass
      hpsi h2 hn kappa tau ring anchor
      (PhaseDirtySuccess hpsi h2 hn kappa tau ring anchor) :=
  (phaseDirty_reacquireSourceMass_iff
    hpsi h2 hn kappa tau ring anchor).2 hmass

#print axioms BirthPhaseB3ReacquireEvent.carrierRawSuccess_taggedReacquireSuccess_disjoint
#print axioms BirthPhaseB3ReacquireEvent.phaseDirty_carrierAgreement
#print axioms BirthPhaseB3ReacquireEvent.phaseDirty_reacquire_iff
#print axioms BirthPhaseB3ReacquireEvent.phaseDirty_reacquireStartBridge
#print axioms BirthPhaseB3ReacquireEvent.phaseDirty_reacquire_weight_eq
#print axioms BirthPhaseB3ReacquireEvent.phaseDirty_reacquireSourceMass_iff
#print axioms BirthPhaseB3ReacquireEvent.phaseDirty_reacquireSourceMass

end BirthPhaseB3ReacquireEvent
