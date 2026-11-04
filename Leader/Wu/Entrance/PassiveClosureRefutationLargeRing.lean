import Std
import Leader.Wu.Entrance.PassiveClosureRefutationRingSix
import Leader.Wu.Entrance.LargeRingLaws


set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096


namespace FinalCandidateR2C
namespace FinalCandidateR2C
namespace FinalCandidateR2C
namespace FinalCandidateR2C
namespace FinalCandidateR2C
namespace B4PassiveClosureRefutationLargeRing


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


/-- Same parameters as the n=6 refutation. -/
theorem h3 : 0 < 3 := by omega
theorem h23 : 2 ≤ 3 := by omega
private theorem h02 : 0 < 2 := by omega


def ring45 : DirectedRing 45 := ⟨by omega⟩


private abbrev FCell := Cell 3 3 48
private abbrev FCfg := Config 45 3 3 48


private def fin3 (x : Nat) : Fin 3 :=
  ⟨x % 3, Nat.mod_lt _ h3⟩


/-- Exact local physical state used by the n=6 witness. -/
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


/--
The large-ring witness is the literal 0,1,2 pattern repeated around all 45
sites:


* 0,3,6,...,42  carry `outer 0`;
* 1,4,7,...,43  carry `outer 1`;
* 2,5,8,...,44  carry `outer 2`.


In particular cells 0,1,2 are exactly the destructive local triple from the
n=6 witness.  Since 45 is divisible by 3, the wrap edge 44 -> 0 is also the
same 2 -> 0 local pair.
-/
def C45 : FCfg := fun i => outer (fin3 i.val)


private theorem neutralAt (i : Fin 45) : NeutralController (C45 i) := by
  exact ⟨rfl, rfl, rfl⟩


private theorem preLeaderless : FinalLeaderless C45 := by
  intro i
  rfl


private theorem cyclicRuler :
    CFinalJ2Edge2.FinalCyclicRuler h3 ring45 C45 := by
  intro a
  apply Fin.ext
  change ((a.val + 1) % 45) % 3 = (a.val % 3 + 1) % 3
  omega


private theorem noGarbage (e : Fin 45) :
    ¬ FinalGarbage h3 (C45 e) (C45 (ring45.rightNeighbor e)) := by
  exact CFinalJ2Edge.no_finalGarbage_of_neutral_noHole h3
    (neutralAt e) (neutralAt (ring45.rightNeighbor e))
    (CFinalJ2Edge2.no_finalHole_of_cyclicRuler
      h3 ring45 C45 cyclicRuler e)


/-!
The imported n=6 module proves its HOST-selector helper privately, so it cannot
be referenced by name here.  The following is the same source-local classifier
argument, kept generic in the pair and therefore independent of ring size.
-/
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


private theorem hostAt (e : Fin 45) :
    (concretePortLocal (κ := 3) (τ := 48) h3 h23).action
      (C45 e) (C45 (ring45.rightNeighbor e)) = .host := by
  exact hostOfNeutral _ _ (preLeaderless e)
    (neutralAt e) (neutralAt (ring45.rightNeighbor e))


/-!
`ProposalNoWrite` is pair-local and has no ring argument.  We kernel-check only
the three ordered local pair types occurring in C45.  Every `decide +kernel`
below is preceded by an exact `#synth Decidable (...)` for the proposition fed
to `decide`.
-/
private def noWritePairB (a b : Fin 3) : Bool :=
  let l := inner a
  let r := inner b
  let q := R2Coherence.proposal h3 h02 h23 l r
  !(R2Coherence.pairWrites l.phys r.phys q.1 q.2) &&
    !(R2Coherence.pairRelabels l.phys r.phys q.1 q.2)


private theorem noWritePairB_spec (a b : Fin 3) :
    noWritePairB a b = true ↔
      R2Coherence.ProposalNoWrite h3 h02 h23 (inner a) (inner b) := by
  simp [noWritePairB, R2Coherence.ProposalNoWrite]


#synth Decidable (noWritePairB (0 : Fin 3) (1 : Fin 3) = true)
private theorem noWrite01B :
    noWritePairB (0 : Fin 3) (1 : Fin 3) = true := by
  decide +kernel


#synth Decidable (noWritePairB (1 : Fin 3) (2 : Fin 3) = true)
private theorem noWrite12B :
    noWritePairB (1 : Fin 3) (2 : Fin 3) = true := by
  decide +kernel


#synth Decidable (noWritePairB (2 : Fin 3) (0 : Fin 3) = true)
private theorem noWrite20B :
    noWritePairB (2 : Fin 3) (0 : Fin 3) = true := by
  decide +kernel


private theorem noWrite01 :
    R2Coherence.ProposalNoWrite h3 h02 h23
      (inner (0 : Fin 3)) (inner (1 : Fin 3)) :=
  (noWritePairB_spec 0 1).1 noWrite01B


private theorem noWrite12 :
    R2Coherence.ProposalNoWrite h3 h02 h23
      (inner (1 : Fin 3)) (inner (2 : Fin 3)) :=
  (noWritePairB_spec 1 2).1 noWrite12B


private theorem noWrite20 :
    R2Coherence.ProposalNoWrite h3 h02 h23
      (inner (2 : Fin 3)) (inner (0 : Fin 3)) :=
  (noWritePairB_spec 2 0).1 noWrite20B


private theorem fin3_cases (x : Fin 3) :
    x = 0 ∨ x = 1 ∨ x = 2 := by
  omega


private theorem fin3_rightNeighbor (a : Fin 45) :
    fin3 ((ring45.rightNeighbor a).val) =
      ⟨((fin3 a.val).val + 1) % 3, Nat.mod_lt _ h3⟩ := by
  apply Fin.ext
  change (((a.val + 1) % 45) % 3) = ((a.val % 3 + 1) % 3)
  omega


private theorem preNoWrite (a : Fin 45) :
    R2Coherence.ProposalNoWrite h3 h02 h23
      (C45 a).phys (C45 (ring45.rightNeighbor a)).phys := by
  change R2Coherence.ProposalNoWrite h3 h02 h23
    (inner (fin3 a.val))
    (inner (fin3 ((ring45.rightNeighbor a).val)))
  have hn := fin3_rightNeighbor a
  rcases fin3_cases (fin3 a.val) with h0 | h1 | h2
  · have hr : fin3 ((ring45.rightNeighbor a).val) = (1 : Fin 3) := by
      simpa [h0] using hn
    rw [h0, hr]
    exact noWrite01
  · have hr : fin3 ((ring45.rightNeighbor a).val) = (2 : Fin 3) := by
      simpa [h1] using hn
    rw [h1, hr]
    exact noWrite12
  · have hr : fin3 ((ring45.rightNeighbor a).val) = (0 : Fin 3) := by
      simpa [h2] using hn
    rw [h2, hr]
    exact noWrite20


private theorem admittedC45 :
    ConcreteB7AdmittedPassive h3 h23 ring45 C45 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i
    change WriterProducerRepair.producerActive
      (R2Coherence.raw (C45 i).phys) = false
    change (decide (WriteState.none = WriteState.produce ∨
      WriteState.none = WriteState.done) : Bool) = false
    rfl
  · intro i
    change
      (R2Coherence.raw (C45 i).phys).path3 = none ∧
      (R2Coherence.raw (C45 i).phys).write = .none ∧
      ((R2Coherence.raw (C45 i).phys).write_state = .none ∨
        (R2Coherence.raw (C45 i).phys).write_state = .depart)
    exact ⟨rfl, rfl, Or.inl rfl⟩
  · intro i
    simp [FinalAllOpen, R2Coherence.OpenControl, C45, outer, inner]
  · intro e
    exact ⟨noGarbage e, hostAt e, preNoWrite e⟩


private def physC45 : R2Coherence.FC 45 3 3 48 := physicalConfig C45
private def physD45 : R2Coherence.FC 45 3 3 48 :=
  R2Coherence.step h3 h23 ring45 physC45 0
private noncomputable def D45 : FCfg :=
  stepConcrete (κ := 3) (τ := 48) h3 h23 ring45 C45 0


private theorem rightNe0 : ring45.rightNeighbor (0 : Fin 45) ≠ 0 := by
  intro h
  have hv := congrArg Fin.val h
  change (0 + 1) % 45 = 0 at hv
  omega


private theorem rightNe0_eq_one :
    ring45.rightNeighbor (0 : Fin 45) = (1 : Fin 45) := by
  apply Fin.ext
  change (0 + 1) % 45 = 1
  omega


/--
`B9Host.hostStep_pairLocal` is the installed physical pair-locality theorem.
It does not have the type of a `stepConcrete` locality theorem.  For the full
final carrier, the exact fact needed here follows directly from
`stepConcrete = stepFinal ...` and `B9FullCarrierHost.writeAtP`: every site
other than the served pair is copied literally.
-/
private theorem D45_other
    (i : Fin 45)
    (hi : i ≠ (0 : Fin 45))
    (hj : i ≠ ring45.rightNeighbor (0 : Fin 45)) :
    D45 i = C45 i := by
  unfold D45 stepConcrete stepFinal
  rw [if_neg rightNe0]
  simp only [B9FullCarrierHost.writeAtP, if_neg hi, if_neg hj]


private theorem D45_phys : physicalConfig D45 = physD45 := by
  classical
  have hedge := admittedC45.2.2.2 (0 : Fin 45)
  have hg := hedge.1
  have ha :
      (concretePort (κ := 3) (τ := 48) h3 h23).action
        (C45 0) (C45 (ring45.rightNeighbor 0)) = .host := by
    simpa only [concretePort, concretePortLocal] using hedge.2.1
  have hf : finalAction h3 h23
      (concretePort (κ := 3) (τ := 48) h3 h23)
      (C45 0) (C45 (ring45.rightNeighbor 0)) = .host := by
    unfold finalAction
    rw [if_neg hg, ha]
  have hrow : rowFinal h3 h23
      (concretePort (κ := 3) (τ := 48) h3 h23)
      (C45 0) (C45 (ring45.rightNeighbor 0)) =
      (concretePort (κ := 3) (τ := 48) h3 h23).row
        (C45 0) (C45 (ring45.rightNeighbor 0)) := by
    unfold rowFinal
    rw [hf]
  have hstep : D45 =
      B9FullCarrierHost.writeAtP ring45 C45 0
        ((concretePort (κ := 3) (τ := 48) h3 h23).row
          (C45 0) (C45 (ring45.rightNeighbor 0))) := by
    unfold D45 stepConcrete stepFinal
    rw [if_neg rightNe0, hrow]
  have hp :=
    (concretePort (κ := 3) (τ := 48) h3 h23).physical_spec
      (C45 0) (C45 (ring45.rightNeighbor 0))
  simp only [ha] at hp
  calc
    physicalConfig D45 =
      physicalConfig
        (B9FullCarrierHost.writeAtP ring45 C45 0
          ((concretePort (κ := 3) (τ := 48) h3 h23).row
            (C45 0) (C45 (ring45.rightNeighbor 0)))) :=
      congrArg (fun D : FCfg => physicalConfig D) hstep
    _ = B9Host.hostStep
        (hostR2C (κ := 3) (τ := 48) h3 h23) ring45 physC45 0 := by
      funext i
      change
        (B9FullCarrierHost.writeAtP ring45 C45 0
          ((concretePort (κ := 3) (τ := 48) h3 h23).row
            (C45 0) (C45 (ring45.rightNeighbor 0))) i).phys =
        B9Host.hostStep
          (hostR2C (κ := 3) (τ := 48) h3 h23) ring45 physC45 0 i
      by_cases hi : i = (0 : Fin 45)
      · subst i
        rw [B9Host.hostStep_left]
        simp only [B9FullCarrierHost.writeAtP, if_pos rfl]
        exact hp.1
      · by_cases hj : i = ring45.rightNeighbor (0 : Fin 45)
        · subst i
          rw [B9Host.hostStep_right
            (hostR2C (κ := 3) (τ := 48) h3 h23)
            ring45 physC45 0 rightNe0]
          simp only [B9FullCarrierHost.writeAtP,
            if_neg rightNe0, if_pos rfl]
          exact hp.2
        · rw [B9Host.hostStep_other
            (hostR2C (κ := 3) (τ := 48) h3 h23)
            ring45 physC45 0 i hi hj]
          simp only [B9FullCarrierHost.writeAtP, if_neg hi, if_neg hj]
          rfl
    _ = physD45 := by rfl


private def leaderFalseB
    (X : R2Coherence.FC 45 3 3 48) (i : Fin 45) : Bool :=
  !(R2Coherence.raw (X i)).leader


private theorem leaderFalseB_spec
    (X : R2Coherence.FC 45 3 3 48) (i : Fin 45) :
    leaderFalseB X i = true ↔
      (R2Coherence.raw (X i)).leader = false := by
  simp [leaderFalseB]


#synth Decidable (leaderFalseB physD45 (0 : Fin 45) = true)
private theorem postLeader0B :
    leaderFalseB physD45 (0 : Fin 45) = true := by
  decide +kernel


#synth Decidable (leaderFalseB physD45 (1 : Fin 45) = true)
private theorem postLeader1B :
    leaderFalseB physD45 (1 : Fin 45) = true := by
  decide +kernel


private theorem physD45Leader0 :
    (R2Coherence.raw (physD45 (0 : Fin 45))).leader = false :=
  (leaderFalseB_spec physD45 0).1 postLeader0B


private theorem physD45Leader1 :
    (R2Coherence.raw (physD45 (1 : Fin 45))).leader = false :=
  (leaderFalseB_spec physD45 1).1 postLeader1B


private theorem D45Leaderless : FinalLeaderless D45 := by
  intro i
  by_cases hi : i = (0 : Fin 45)
  · subst i
    change (R2Coherence.raw ((physicalConfig D45) 0)).leader = false
    rw [D45_phys]
    exact physD45Leader0
  · by_cases hj : i = ring45.rightNeighbor (0 : Fin 45)
    · rw [hj, rightNe0_eq_one]
      change (R2Coherence.raw ((physicalConfig D45) 1)).leader = false
      rw [D45_phys]
      exact physD45Leader1
    · rw [D45_other i hi hj]
      exact preLeaderless i


private theorem D45NoLeader : ¬ HasLeader D45 := by
  rintro ⟨i, hi⟩
  rw [D45Leaderless i] at hi
  cases hi


private def physProposalAt
    (X : R2Coherence.FC 45 3 3 48) (a : Fin 45) :
    R2.Cell 3 3 48 × R2.Cell 3 3 48 :=
  R2Coherence.proposal h3 h02 h23
    (X a) (X (ring45.rightNeighbor a))


private def relabelPhysB
    (X : R2Coherence.FC 45 3 3 48) (a : Fin 45) : Bool :=
  let j := ring45.rightNeighbor a
  let q := physProposalAt X a
  R2Coherence.pairRelabels (X a).phys (X j).phys q.1 q.2


private theorem relabelPhysB_spec
    (X : R2Coherence.FC 45 3 3 48) (a : Fin 45) :
    relabelPhysB X a = true ↔
      (let j := ring45.rightNeighbor a
       let q := R2Coherence.proposal h3 h02 h23 (X a) (X j)
       R2Coherence.pairRelabels
         (X a).phys (X j).phys q.1 q.2 = true) := by
  rfl


#synth Decidable (relabelPhysB physD45 (1 : Fin 45) = true)
private theorem postRelabel1B :
    relabelPhysB physD45 (1 : Fin 45) = true := by
  decide +kernel


private theorem D45NotAdmitted :
    ¬ ConcreteB7AdmittedPassive h3 h23 ring45 D45 := by
  intro hA
  have hNW := (hA.2.2.2 (1 : Fin 45)).2.2
  unfold R2Coherence.ProposalNoWrite at hNW
  dsimp only at hNW
  have hRel : relabelPhysB (physicalConfig D45) (1 : Fin 45) = true := by
    rw [D45_phys]
    exact postRelabel1B
  have hTrue :=
    (relabelPhysB_spec (physicalConfig D45) (1 : Fin 45)).1 hRel
  dsimp only at hTrue
  change
    R2Coherence.pairRelabels
      (D45 (1 : Fin 45)).phys.phys
      (D45 (ring45.rightNeighbor (1 : Fin 45))).phys.phys
      (R2Coherence.proposal h3 h02 h23
        (D45 (1 : Fin 45)).phys
        (D45 (ring45.rightNeighbor (1 : Fin 45))).phys).1
      (R2Coherence.proposal h3 h02 h23
        (D45 (1 : Fin 45)).phys
        (D45 (ring45.rightNeighbor (1 : Fin 45))).phys).2 = true at hTrue
  have hFalse := hNW.2
  rw [hTrue] at hFalse
  cases hFalse


theorem not_concreteB7AdmittedPassiveClosedObligation_psi3_n45 :
    ¬ ConcreteB7AdmittedPassiveClosedObligation
      (κ := 3) (τ := 48) h3 h23 ring45 := by
  intro hClosed
  have h := hClosed C45 (0 : Fin 45) admittedC45 preLeaderless
  change HasLeader D45 ∨ ConcreteB7AdmittedPassive h3 h23 ring45 D45 at h
  exact h.elim D45NoLeader D45NotAdmitted


theorem largeRingDomain_does_not_rescue :
    B6EntranceLargeRingPackage.LargeRingDomain 3 45 ∧
      ¬ ConcreteB7AdmittedPassiveClosedObligation
        (κ := 3) (τ := 48) h3 h23 ring45 := by
  constructor
  · unfold B6EntranceLargeRingPackage.LargeRingDomain
      B6EntranceV2.envelopeWidth B6EntranceV2.coreWidth
      B6EntranceV2.collarWidth
    omega
  · exact not_concreteB7AdmittedPassiveClosedObligation_psi3_n45


#print axioms not_concreteB7AdmittedPassiveClosedObligation_psi3_n45
#print axioms largeRingDomain_does_not_rescue


end B4PassiveClosureRefutationLargeRing
end FinalCandidateR2C
end FinalCandidateR2C
end FinalCandidateR2C
end FinalCandidateR2C
end FinalCandidateR2C
