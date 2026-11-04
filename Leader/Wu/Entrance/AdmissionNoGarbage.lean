import Leader.Wu.Entrance.AdmissionLanding
import Leader.Wu.Entrance.PassivePost
import Leader.Wu.Entrance.PassiveWriterPost
import Leader.Wu.Entrance.PassiveOuterNeutralFrame
import Leader.Wu.Entrance.PassiveInputNeutralProjection
import Leader.Wu.Entrance.PassiveResetEcho

set_option autoImplicit false
set_option Elab.async false

namespace CFinalJ2Edge

open CFinalJ2Landing
open FinalCandidateR2C
open FinalCandidateR2C.FinalCandidateR2C
open FinalCandidateR2C.FinalCandidateR2C.FinalCandidateR2C
open FinalCandidateR2C.FinalCandidateR2C.FinalCandidateR2C.FinalCandidateR2C
open FinalCandidateR2C.FinalCandidateR2C.FinalCandidateR2C.FinalCandidateR2C.FinalCandidateR2C

variable {n psi : Nat}

/-- Neutral outer controllers rule out the ticket/backing part of recovery
    garbage.  The geometric `Hole` part is deliberately not claimed here. -/
theorem no_finalScrubGarbage_of_neutral
    (l r : Cell psi psi (16 * psi))
    (hl : NeutralController l) (hr : NeutralController r) :
    ¬ B9ControllerRecovery.ScrubGarbage (oldCell l) (oldCell r) := by
  intro h
  rcases h with hL | hR | hB
  · have ht : l.acquireTicket = true := hL.1
    rw [hl.2.2] at ht
    cases ht
  · have ht : r.acquireTicket = true := hR.1
    rw [hr.2.2] at ht
    cases ht
  · have hp : l.spliceRole = .predecessorArmed := hB.1.1
    rw [hl.1] at hp
    cases hp

/-- Hence, on a neutral pair, excluding the sole remaining `FinalHole`
    excludes all `FinalGarbage`. -/
theorem no_finalGarbage_of_neutral_noHole
    (hpsi : 0 < psi) {l r : Cell psi psi (16 * psi)}
    (hl : NeutralController l) (hr : NeutralController r)
    (hHole : ¬ FinalHole hpsi l r) :
    ¬ FinalGarbage hpsi l r := by
  intro hG
  change B9ControllerRecovery.Garbage hpsi (oldCell l) (oldCell r) at hG
  rcases hG with hScrub | hH
  · exact no_finalScrubGarbage_of_neutral l r hl hr hScrub
  · exact hHole hH

/-- Exact remaining geometric part of J2's no-garbage conjunct. -/
def J2C1AdmissionHoleResidual
    (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (ring : DirectedRing n) : Prop :=
  ∀ (C : Config n psi psi (16 * psi)) (e : Fin n),
    ConcreteB7AdmittedPassive hpsi h2 ring C →
    FinalLeaderless C →
    let D := stepConcrete (κ := psi) (τ := 16 * psi) hpsi h2 ring C e
    FinalLeaderless D →
    R2CoherenceV31Closure.ElectionGeometryV31 ring
      (R2CoherenceV31MissionGate.finalV31View D) →
    R2CoherenceV31.CoherentPrefixesV3 ring
      (R2CoherenceV31MissionGate.finalV31View D) →
    (∀ i : Fin n, NeutralController (D i)) →
    ∀ a : Fin n,
      ¬ FinalHole hpsi (D a) (D (ring.rightNeighbor a))

/-- Exact remaining selector direction: current source has HOST -> neutral
    facts, not neutral -> HOST. -/
def J2C1AdmissionHostActionResidual
    (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (ring : DirectedRing n) : Prop :=
  ∀ (C : Config n psi psi (16 * psi)) (e : Fin n),
    ConcreteB7AdmittedPassive hpsi h2 ring C →
    FinalLeaderless C →
    let D := stepConcrete (κ := psi) (τ := 16 * psi) hpsi h2 ring C e
    FinalLeaderless D →
    R2CoherenceV31Closure.ElectionGeometryV31 ring
      (R2CoherenceV31MissionGate.finalV31View D) →
    R2CoherenceV31.CoherentPrefixesV3 ring
      (R2CoherenceV31MissionGate.finalV31View D) →
    (∀ i : Fin n, NeutralController (D i)) →
    ∀ a : Fin n,
      (concretePortLocal (κ := psi) (τ := 16 * psi) hpsi h2).action
        (D a) (D (ring.rightNeighbor a)) = .host

/-- Once the geometric-hole leaf, the converse HOST selector leaf, and the
    already-named second-step ProposalNoWrite leaf are available, J2's edge
    residual is only conjunction wiring. -/
theorem j2C1AdmissionEdgeResidual_of_residuals
    (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (ring : DirectedRing n)
    (hHole : J2C1AdmissionHoleResidual hpsi h2 ring)
    (hHost : J2C1AdmissionHostActionResidual hpsi h2 ring)
    (hNoWrite : ConcreteB7PassiveProposalNoWritePostObligation
      (κ := psi) (τ := 16 * psi) hpsi h2 ring) :
    J2C1AdmissionEdgeResidual hpsi h2 ring := by
  intro C e hA hL
  dsimp only
  intro hDL hGeom hPrefix hNeutral a
  have hh := hHole C e hA hL hDL hGeom hPrefix hNeutral a
  have ha := hHost C e hA hL hDL hGeom hPrefix hNeutral a
  have hn := hNoWrite C e hA hL hDL a
  refine ⟨?_, ha, hn⟩
  exact no_finalGarbage_of_neutral_noHole hpsi
    (hNeutral a) (hNeutral (ring.rightNeighbor a)) hh

end CFinalJ2Edge
