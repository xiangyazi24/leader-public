import Std
import Leader.Wu.Entrance.PassiveClosure
import Leader.Wu.Entrance.PassiveProjection
import Leader.Wu.Entrance.AdmissionCyclicRuler

set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096

namespace FinalCandidateR2C
namespace FinalCandidateR2C
namespace FinalCandidateR2C
namespace FinalCandidateR2C
namespace FinalCandidateR2C
namespace B4PassiveClosureRefutation

open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
  PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
  PPLLLeaderCreationCleanupRepair
open WriterProducerRepair
open Q11593SpliceControllerDesign
open B9Host B9FullCarrierHost B9FullCarrierRows
open B9SpliceControllerR1Table B9SpliceControllerR1TableV2
  B9SpliceControllerR1TableV3 B9SpliceControllerR1TableV4
  B9SpliceControllerR1TableV6 B9SpliceControllerR1TableV7
  B9SpliceControllerR1TableV8 B9SpliceControllerR1TableV9
  B9SpliceControllerR1TableV10b
open B9OrphanToFence B9SpliceTableV10e B9SpliceTableV10g
  B9SpliceTableV10j B9SpliceTableHost

theorem h3 : 0 < 3 := by omega
theorem h23 : 2 ≤ 3 := by omega
private theorem h02 : 0 < 2 := by omega
def ring6 : DirectedRing 6 := ⟨by omega⟩

private abbrev FCell := Cell 3 3 48
private abbrev FCfg := Config 6 3 3 48

private def fin3 (x : Nat) : Fin 3 := ⟨x % 3, Nat.mod_lt _ h3⟩

private def literal (lab : Fin 3) : R2.Cell 3 3 48 :=
  let seed := WriterProducerRegression.clean h3 (fun _ => false) lab
  let b := seed.base.core.core
  let b' : BoundedAgentState 3 3 := {
    b with
    leader := false
    shield := false
    gen_ws := false
    wait := false
    label := lab
    bit := false
    state := .none
    path := .some lab 0
    path2 := none
    path3 := none
    path4 := none
    path5 := none
    p := false
    p_carry := false
    reset_cmd := false
    echo := false
    write_state := .none
    write := .none
    b_carry := false }
  ⟨⟨⟨b', false⟩, Fin.last 48⟩, 0⟩

private def inner (lab : Fin 3) : R2Coherence.Cell 3 3 48 :=
  ⟨literal lab, ⟨.open, .none⟩⟩

private def outer (lab : Fin 3) : FCell :=
  ⟨inner lab, .none, false, false⟩

private def C0 : FCfg := fun i => outer (fin3 i.val)

private theorem neutralAt (i : Fin 6) : NeutralController (C0 i) := by
  exact ⟨rfl, rfl, rfl⟩

private theorem preLeaderless : FinalLeaderless C0 := by
  intro i
  rfl

private theorem cyclicRuler :
    CFinalJ2Edge2.FinalCyclicRuler h3 ring6 C0 := by
  intro a
  apply Fin.ext
  change ((a.val + 1) % 6) % 3 = (a.val % 3 + 1) % 3
  omega

private theorem noGarbage (e : Fin 6) :
    ¬ FinalGarbage h3 (C0 e) (C0 (ring6.rightNeighbor e)) := by
  exact CFinalJ2Edge.no_finalGarbage_of_neutral_noHole h3
    (neutralAt e) (neutralAt (ring6.rightNeighbor e))
    (CFinalJ2Edge2.no_finalHole_of_cyclicRuler
      h3 ring6 C0 cyclicRuler e)

private theorem noLdc (l r : FCell) (hL : outputFinal l = false) :
    ¬ B9SpliceTableHost.ldc
      (shadowHostAt
        (carrierLaws (ψ := 3) (κ := 3) (τ := 48))
        (hostR2C (κ := 3) (τ := 48) h3 h23) l.phys r.phys)
      (toOld (carrierLaws (ψ := 3) (κ := 3) (τ := 48)) l).carrier
      (toOld (carrierLaws (ψ := 3) (κ := 3) (τ := 48)) r).carrier := by
  intro h
  have hl := h.1
  change outputFinal l = true at hl
  rw [hL] at hl
  cases hl

private theorem hostOfNeutral (l r : FCell)
    (hL : outputFinal l = false)
    (hNL : NeutralController l) (hNR : NeutralController r) :
    (concretePortLocal (κ := 3) (τ := 48) h3 h23).action l r = .host := by
  exact CFinalJ2Edge2.concretePort_action_host_of_neutral_leaderless
    (psi := 3) h3 h23 l r hL hNL hNR

private theorem hostAt (e : Fin 6) :
    (concretePortLocal (κ := 3) (τ := 48) h3 h23).action
      (C0 e) (C0 (ring6.rightNeighbor e)) = .host := by
  exact hostOfNeutral _ _ (preLeaderless e)
    (neutralAt e) (neutralAt (ring6.rightNeighbor e))

private theorem fin6_cases (i : Fin 6) :
    i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 := by
  omega

private def all6 (p : Fin 6 → Bool) : Bool :=
  p 0 && p 1 && p 2 && p 3 && p 4 && p 5

private theorem all6_spec (p : Fin 6 → Bool) :
    all6 p = true ↔ ∀ i, p i = true := by
  constructor
  · intro h i
    have hs :
        ((((p 0 = true ∧ p 1 = true) ∧ p 2 = true) ∧ p 3 = true) ∧
          p 4 = true) ∧ p 5 = true := by
      simpa [all6] using h
    rcases hs with ⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3'⟩, h4⟩, h5⟩
    rcases fin6_cases i with h | h | h | h | h | h <;>
      subst i <;> assumption
  · intro h
    have h0 := h (0 : Fin 6)
    have h1 := h (1 : Fin 6)
    have h2 := h (2 : Fin 6)
    have h3' := h (3 : Fin 6)
    have h4 := h (4 : Fin 6)
    have h5 := h (5 : Fin 6)
    simp [all6, h0, h1, h2, h3', h4, h5]

private def proposalAt (X : FCfg) (a : Fin 6) :
    R2.Cell 3 3 48 × R2.Cell 3 3 48 :=
  R2Coherence.proposal h3 h02 h23
    (X a).phys (X (ring6.rightNeighbor a)).phys

private def noWriteB (X : FCfg) (a : Fin 6) : Bool :=
  let j := ring6.rightNeighbor a
  let q := proposalAt X a
  !(R2Coherence.pairWrites (X a).phys.phys (X j).phys.phys q.1 q.2) &&
  !(R2Coherence.pairRelabels (X a).phys.phys (X j).phys.phys q.1 q.2)

private theorem noWriteB_spec (X : FCfg) (a : Fin 6) :
    noWriteB X a = true ↔
      R2Coherence.ProposalNoWrite h3 h02 h23
        (X a).phys (X (ring6.rightNeighbor a)).phys := by
  simp [noWriteB, proposalAt, R2Coherence.ProposalNoWrite]

private def noWriteAllB (X : FCfg) : Bool := all6 (noWriteB X)

private theorem noWriteAllB_spec (X : FCfg) :
    noWriteAllB X = true ↔
      ∀ a : Fin 6, R2Coherence.ProposalNoWrite h3 h02 h23
        (X a).phys (X (ring6.rightNeighbor a)).phys := by
  constructor
  · intro h a
    exact (noWriteB_spec X a).1 ((all6_spec (noWriteB X)).1 h a)
  · intro h
    apply (all6_spec (noWriteB X)).2
    intro a
    exact (noWriteB_spec X a).2 (h a)

#synth Decidable (noWriteAllB C0 = true)
private theorem preNoWriteAllB : noWriteAllB C0 = true := by
  decide +kernel

private theorem preNoWrite (a : Fin 6) :
    R2Coherence.ProposalNoWrite h3 h02 h23
      (C0 a).phys (C0 (ring6.rightNeighbor a)).phys :=
  (noWriteAllB_spec C0).1 preNoWriteAllB a

private theorem admittedC0 : ConcreteB7AdmittedPassive h3 h23 ring6 C0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i
    change WriterProducerRepair.producerActive
      (R2Coherence.raw (C0 i).phys) = false
    change (decide (WriteState.none = WriteState.produce ∨
      WriteState.none = WriteState.done) : Bool) = false
    rfl
  · intro i
    change
      (R2Coherence.raw (C0 i).phys).path3 = none ∧
      (R2Coherence.raw (C0 i).phys).write = .none ∧
      ((R2Coherence.raw (C0 i).phys).write_state = .none ∨
        (R2Coherence.raw (C0 i).phys).write_state = .depart)
    exact ⟨rfl, rfl, Or.inl rfl⟩
  · intro i
    simp [FinalAllOpen, R2Coherence.OpenControl, C0, outer, inner]
  · intro e
    exact ⟨noGarbage e, hostAt e, preNoWrite e⟩

private def physC0 : R2Coherence.FC 6 3 3 48 := physicalConfig C0
private def physD : R2Coherence.FC 6 3 3 48 :=
  R2Coherence.step h3 h23 ring6 physC0 0
private noncomputable def D0 : FCfg :=
  stepConcrete (κ := 3) (τ := 48) h3 h23 ring6 C0 0

private theorem rightNe0 : ring6.rightNeighbor (0 : Fin 6) ≠ 0 := by
  intro h
  have hv := congrArg Fin.val h
  change (0 + 1) % 6 = 0 at hv
  omega

private theorem D0_phys : physicalConfig D0 = physD := by
  classical
  have hedge := admittedC0.2.2.2 (0 : Fin 6)
  have hg := hedge.1
  have ha :
      (concretePort (κ := 3) (τ := 48) h3 h23).action
        (C0 0) (C0 (ring6.rightNeighbor 0)) = .host := by
    simpa only [concretePort, concretePortLocal] using hedge.2.1
  have hf : finalAction h3 h23
      (concretePort (κ := 3) (τ := 48) h3 h23)
      (C0 0) (C0 (ring6.rightNeighbor 0)) = .host := by
    unfold finalAction
    rw [if_neg hg, ha]
  have hrow : rowFinal h3 h23
      (concretePort (κ := 3) (τ := 48) h3 h23)
      (C0 0) (C0 (ring6.rightNeighbor 0)) =
      (concretePort (κ := 3) (τ := 48) h3 h23).row
        (C0 0) (C0 (ring6.rightNeighbor 0)) := by
    unfold rowFinal
    rw [hf]
  have hstep : D0 =
      B9FullCarrierHost.writeAtP ring6 C0 0
        ((concretePort (κ := 3) (τ := 48) h3 h23).row
          (C0 0) (C0 (ring6.rightNeighbor 0))) := by
    unfold D0 stepConcrete stepFinal
    rw [if_neg rightNe0, hrow]
  have hp :=
    (concretePort (κ := 3) (τ := 48) h3 h23).physical_spec
      (C0 0) (C0 (ring6.rightNeighbor 0))
  simp only [ha] at hp
  calc
    physicalConfig D0 =
      physicalConfig
        (B9FullCarrierHost.writeAtP ring6 C0 0
          ((concretePort (κ := 3) (τ := 48) h3 h23).row
            (C0 0) (C0 (ring6.rightNeighbor 0)))) :=
      congrArg (fun D : FCfg => physicalConfig D) hstep
    _ = B9Host.hostStep
        (hostR2C (κ := 3) (τ := 48) h3 h23) ring6 physC0 0 := by
      funext i
      change
        (B9FullCarrierHost.writeAtP ring6 C0 0
          ((concretePort (κ := 3) (τ := 48) h3 h23).row
            (C0 0) (C0 (ring6.rightNeighbor 0))) i).phys =
        B9Host.hostStep
          (hostR2C (κ := 3) (τ := 48) h3 h23) ring6 physC0 0 i
      by_cases hi : i = (0 : Fin 6)
      · subst i
        rw [B9Host.hostStep_left]
        simp only [B9FullCarrierHost.writeAtP, if_pos rfl]
        exact hp.1
      · by_cases hj : i = ring6.rightNeighbor (0 : Fin 6)
        · subst i
          rw [B9Host.hostStep_right
            (hostR2C (κ := 3) (τ := 48) h3 h23)
            ring6 physC0 0 rightNe0]
          simp only [B9FullCarrierHost.writeAtP,
            if_neg rightNe0, if_pos rfl]
          exact hp.2
        · rw [B9Host.hostStep_other
            (hostR2C (κ := 3) (τ := 48) h3 h23)
            ring6 physC0 0 i hi hj]
          simp only [B9FullCarrierHost.writeAtP, if_neg hi, if_neg hj]
          rfl
    _ = physD := by rfl

private def leaderlessPhysB (X : R2Coherence.FC 6 3 3 48) : Bool :=
  all6 (fun i => !(R2Coherence.raw (X i)).leader)

private theorem leaderlessPhysB_spec (X : R2Coherence.FC 6 3 3 48) :
    leaderlessPhysB X = true ↔
      ∀ i, (R2Coherence.raw (X i)).leader = false := by
  constructor
  · intro h i
    have hb := (all6_spec (fun j => !(R2Coherence.raw (X j)).leader)).1 h i
    simpa using hb
  · intro h
    apply (all6_spec (fun j => !(R2Coherence.raw (X j)).leader)).2
    intro i
    simp [h i]

#synth Decidable (leaderlessPhysB physD = true)
private theorem postLeaderlessB : leaderlessPhysB physD = true := by
  decide +kernel

private theorem physDLeaderless (i : Fin 6) :
    (R2Coherence.raw (physD i)).leader = false :=
  (leaderlessPhysB_spec physD).1 postLeaderlessB i

private theorem D0Leaderless : FinalLeaderless D0 := by
  intro i
  change (R2Coherence.raw ((physicalConfig D0) i)).leader = false
  rw [D0_phys]
  exact physDLeaderless i

private theorem D0NoLeader : ¬ HasLeader D0 := by
  rintro ⟨i, hi⟩
  rw [D0Leaderless i] at hi
  cases hi

private def physProposalAt (X : R2Coherence.FC 6 3 3 48) (a : Fin 6) :
    R2.Cell 3 3 48 × R2.Cell 3 3 48 :=
  R2Coherence.proposal h3 h02 h23 (X a) (X (ring6.rightNeighbor a))

private def relabelPhysB
    (X : R2Coherence.FC 6 3 3 48) (a : Fin 6) : Bool :=
  let j := ring6.rightNeighbor a
  let q := physProposalAt X a
  R2Coherence.pairRelabels (X a).phys (X j).phys q.1 q.2

private theorem relabelPhysB_spec
    (X : R2Coherence.FC 6 3 3 48) (a : Fin 6) :
    relabelPhysB X a = true ↔
      (let j := ring6.rightNeighbor a
       let q := R2Coherence.proposal h3 h02 h23 (X a) (X j)
       R2Coherence.pairRelabels (X a).phys (X j).phys q.1 q.2 = true) := by
  rfl

set_option maxHeartbeats 800000000 in
set_option maxRecDepth 100000 in
private theorem postRelabel1B : relabelPhysB physD (1 : Fin 6) = true := by
  rfl

private theorem D0NotAdmitted :
    ¬ ConcreteB7AdmittedPassive h3 h23 ring6 D0 := by
  intro hA
  have hNW := (hA.2.2.2 (1 : Fin 6)).2.2
  unfold R2Coherence.ProposalNoWrite at hNW
  dsimp only at hNW
  have hRel : relabelPhysB (physicalConfig D0) (1 : Fin 6) = true := by
    rw [D0_phys]
    exact postRelabel1B
  have hTrue :=
    (relabelPhysB_spec (physicalConfig D0) (1 : Fin 6)).1 hRel
  dsimp only at hTrue
  change
    R2Coherence.pairRelabels
      (D0 (1 : Fin 6)).phys.phys
      (D0 (ring6.rightNeighbor (1 : Fin 6))).phys.phys
      (R2Coherence.proposal h3 h02 h23
        (D0 (1 : Fin 6)).phys
        (D0 (ring6.rightNeighbor (1 : Fin 6))).phys).1
      (R2Coherence.proposal h3 h02 h23
        (D0 (1 : Fin 6)).phys
        (D0 (ring6.rightNeighbor (1 : Fin 6))).phys).2 = true at hTrue
  have hFalse := hNW.2
  rw [hTrue] at hFalse
  cases hFalse

/-- PARAMETER-SCOPED refutation only:
    ψ=3, κ=3, τ=48, n=6, and the canonical `ring6`. -/
theorem not_concreteB7AdmittedPassiveClosedObligation_psi3_n6_ring6 :
    ¬ ConcreteB7AdmittedPassiveClosedObligation
      (κ := 3) (τ := 48) h3 h23 ring6 := by
  intro hClosed
  have h := hClosed C0 (0 : Fin 6) admittedC0 preLeaderless
  change HasLeader D0 ∨ ConcreteB7AdmittedPassive h3 h23 ring6 D0 at h
  exact h.elim D0NoLeader D0NotAdmitted

#print axioms not_concreteB7AdmittedPassiveClosedObligation_psi3_n6_ring6

end B4PassiveClosureRefutation
end FinalCandidateR2C
end FinalCandidateR2C
end FinalCandidateR2C
end FinalCandidateR2C
end FinalCandidateR2C
