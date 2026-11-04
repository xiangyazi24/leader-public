import Leader.Wu.Entrance.ComposedRow
import Leader.Wu.Splice.FullCarrierRows


set_option autoImplicit false
set_option Elab.async false


namespace FinalCandidateR2C
namespace FinalCandidateR2C
namespace FinalCandidateR2C
namespace FinalCandidateR2C
namespace FinalCandidateR2C


open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
  PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
  PPLLLeaderCreationCleanupRepair
open B9Host B9FullCarrierHost
open WriterProducerRepair
open BirthLeaderlessBirthMassRenewal BirthTwoStageEscape


variable {n ψ κ τ : Nat}


/-- The route-frozen complete B9 port over the R2C physical host. -/
noncomputable def concretePort
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) :
    Port (κ := κ) (τ := τ) hψ h2 :=
  B9FullCarrierRows.fullRowPort
    (carrierLaws (ψ := ψ) (κ := κ) (τ := τ))
    (hostR2C (κ := κ) (τ := τ) hψ h2) hψ


/-- Exact final scheduler step after freezing the port. -/
noncomputable def stepConcrete
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) :
    Config n ψ κ τ → Fin n → Config n ψ κ τ :=
  stepFinal hψ h2
    (concretePort (κ := κ) (τ := τ) hψ h2) ring


/-- Local restatement of the writer-clear clause from the B7 admission class.
Kept here so this file needs only the two requested imports. -/
def ConcreteWriterClear (C : Config n ψ κ τ) : Prop :=
  ∀ i : Fin n,
    let u := R2Coherence.raw (C i).phys
    u.path3 = none ∧ u.write_state = .none ∧ u.write = .none


/-- The B7 admission class specialized to the route-frozen port. -/
def ConcreteB7Admitted
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ)
    (ring : DirectedRing n) (C : Config n ψ κ τ) : Prop :=
  FinalNoProducer C ∧ ConcreteWriterClear C ∧ FinalAllOpen C ∧
  (∀ e : Fin n,
    ¬ FinalGarbage hψ (C e) (C (ring.rightNeighbor e)) ∧
    (concretePort (κ := κ) (τ := τ) hψ h2).action
        (C e) (C (ring.rightNeighbor e)) = .host ∧
    R2Coherence.ProposalNoWrite hψ (by decide : 0 < 2) h2
      (C e).phys (C (ring.rightNeighbor e)).phys)


/-- Leaderless one-letter closure of the concrete B7 admission class. -/
def ConcreteB7AdmissionClosedObligation
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ)
    (ring : DirectedRing n) : Prop :=
  ∀ (C : Config n ψ κ τ) (e : Fin n),
    ConcreteB7Admitted hψ h2 ring C →
    FinalLeaderless C →
    HasLeader (stepConcrete (κ := κ) (τ := τ) hψ h2 ring C e) ∨
      ConcreteB7Admitted hψ h2 ring
        (stepConcrete (κ := κ) (τ := τ) hψ h2 ring C e)


/-- Freeze checklist for the concrete full-row port.


The six old gates are preserved verbatim except that controller recovery is
parameterized by the explicit first-hit horizon/denominator pair `H,Q`.
`b7Closure` is the additional admitted-class closure gate required by the
same-word B7 transfer. -/
structure FreezeGatesConcrete
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (Source Entry Ready : Config n ψ κ τ → Prop)
    (H Q entryH entryQ b7H b7Q oldPhysicalCard finalCard : Nat) : Prop where
  coherenceBranches :
    CoherenceBranchObligations hψ h2
      (concretePort (κ := κ) (τ := τ) hψ h2) ring
  controllerRecoveryMass :
    ∀ C : Config n ψ κ τ,
      Q * avoidCount
          (stepConcrete (κ := κ) (τ := τ) hψ h2 ring)
          (fun _ : Config n ψ κ τ => True)
          (FinalRecoveryTarget hψ ring) C H ≤
        (Q - 1) * n ^ H
  writerLease :
    WriterLeaseMassObligation hψ h2
      (concretePort (κ := κ) (τ := τ) hψ h2) ring
  entranceLaws :
    EntranceLawsObligation hψ h2
      (concretePort (κ := κ) (τ := τ) hψ h2) ring
      Source Entry entryH entryQ
  b7ComposedMass :
    B7ComposedMassObligation hψ h2
      (concretePort (κ := κ) (τ := τ) hψ h2) ring
      Ready b7H b7Q
  stateCount :
    StateCountObligation (ψ := ψ) oldPhysicalCard finalCard
  b7Closure :
    ConcreteB7AdmissionClosedObligation
      (κ := κ) (τ := τ) hψ h2 ring


/-- The concrete freeze strictly refines the old generic checklist at its
historical controller constants `H = 6*n`, `Q = n^(6*n)`. -/
theorem freezeGatesConcrete_to_generic
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (Source Entry Ready : Config n ψ κ τ → Prop)
    (entryH entryQ b7H b7Q oldPhysicalCard finalCard : Nat)
    (h : FreezeGatesConcrete hψ h2 ring Source Entry Ready
      (6 * n) (n ^ (6 * n))
      entryH entryQ b7H b7Q oldPhysicalCard finalCard) :
    FreezeGates hψ h2
      (concretePort (κ := κ) (τ := τ) hψ h2) ring
      Source Entry Ready
      entryH entryQ b7H b7Q oldPhysicalCard finalCard := by
  refine
    { coherenceBranches := h.coherenceBranches
      controllerRecoveryMass := ?_
      writerLease := h.writerLease
      entranceLaws := h.entranceLaws
      b7ComposedMass := h.b7ComposedMass
      stateCount := h.stateCount }
  simpa only [ControllerRecoveryMassObligation, stepConcrete] using
    h.controllerRecoveryMass


end FinalCandidateR2C
end FinalCandidateR2C
end FinalCandidateR2C
end FinalCandidateR2C
end FinalCandidateR2C
