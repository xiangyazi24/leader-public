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
namespace B4PassiveClosureRefutationPsi4


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


theorem h4 : 0 < 4 := by omega
theorem h24 : 2 ≤ 4 := by omega
private theorem h02 : 0 < 2 := by omega


def ring8 : DirectedRing 8 := ⟨by omega⟩


private abbrev FCell := Cell 4 4 64
private abbrev FCfg := Config 8 4 4 64


private def fin4 (x : Nat) : Fin 4 :=
  ⟨x % 4, Nat.mod_lt _ h4⟩


/-- Exactly the seed: site 1 is `.equal`; every other site is `.none`. -/
private def seededState (i : Fin 8) : MainState :=
  if i = (1 : Fin 8) then .equal else .none


/-- Same physical literal as the certified psi=3 witness, with only MainState
    exposed as a parameter so site 1 can carry the seeded equality. -/
private def literal (lab : Fin 4) (st : MainState) : R2.Cell 4 4 64 :=
  let seed := WriterProducerRegression.clean h4 (fun _ => false) lab
  let b := seed.base.core.core
  let b' : BoundedAgentState 4 4 := {
    b with
    leader := false
    shield := false
    gen_ws := false
    wait := false
    label := lab
    bit := false
    state := st
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
  ⟨⟨⟨b', false⟩, Fin.last 64⟩, 0⟩


private def inner (lab : Fin 4) (st : MainState) :
    R2Coherence.Cell 4 4 64 :=
  ⟨literal lab st, ⟨.open, .none⟩⟩


private def outer (lab : Fin 4) (st : MainState) : FCell :=
  ⟨inner lab st, .none, false, false⟩


/-- Labels are 0,1,2,3,0,1,2,3.  Only site 1's MainState is seeded. -/
private def C4 : FCfg := fun i =>
  outer (fin4 i.val) (seededState i)


private theorem neutralAt (i : Fin 8) : NeutralController (C4 i) := by
  exact ⟨rfl, rfl, rfl⟩


private theorem preLeaderless : FinalLeaderless C4 := by
  intro i
  rfl


private theorem cyclicRuler :
    CFinalJ2Edge2.FinalCyclicRuler h4 ring8 C4 := by
  intro a
  apply Fin.ext
  change ((a.val + 1) % 8) % 4 = (a.val % 4 + 1) % 4
  omega


/-- The `.equal` seed is irrelevant here: the first lemma reads labels only,
    and the second reads only outer-neutral controller fields plus no-hole. -/
private theorem noGarbage (e : Fin 8) :
    ¬ FinalGarbage h4 (C4 e) (C4 (ring8.rightNeighbor e)) := by
  exact CFinalJ2Edge.no_finalGarbage_of_neutral_noHole h4
    (neutralAt e) (neutralAt (ring8.rightNeighbor e))
    (CFinalJ2Edge2.no_finalHole_of_cyclicRuler
      h4 ring8 C4 cyclicRuler e)


private theorem hostOfNeutral (l r : FCell)
    (hL : outputFinal l = false)
    (hNL : NeutralController l) (hNR : NeutralController r) :
    (concretePortLocal (κ := 4) (τ := 64) h4 h24).action l r = .host := by
  exact CFinalJ2Edge2.concretePort_action_host_of_neutral_leaderless
    (psi := 4) h4 h24 l r hL hNL hNR


private theorem hostAt (e : Fin 8) :
    (concretePortLocal (κ := 4) (τ := 64) h4 h24).action
      (C4 e) (C4 (ring8.rightNeighbor e)) = .host := by
  exact hostOfNeutral _ _ (preLeaderless e)
    (neutralAt e) (neutralAt (ring8.rightNeighbor e))


private theorem fin8_cases (i : Fin 8) :
    i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨
    i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by
  omega


private def all8 (p : Fin 8 → Bool) : Bool :=
  p 0 && p 1 && p 2 && p 3 && p 4 && p 5 && p 6 && p 7


private theorem all8_spec (p : Fin 8 → Bool) :
    all8 p = true ↔ ∀ i, p i = true := by
  constructor
  · intro h i
    have hs :
        ((((((p 0 = true ∧ p 1 = true) ∧ p 2 = true) ∧ p 3 = true) ∧
          p 4 = true) ∧ p 5 = true) ∧ p 6 = true) ∧ p 7 = true := by
      simpa [all8] using h
    rcases hs with
      ⟨⟨⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3'⟩, h4'⟩, h5⟩, h6⟩, h7⟩
    rcases fin8_cases i with h | h | h | h | h | h | h | h <;>
      subst i <;> assumption
  · intro h
    have h0 := h (0 : Fin 8)
    have h1 := h (1 : Fin 8)
    have h2 := h (2 : Fin 8)
    have h3' := h (3 : Fin 8)
    have h4' := h (4 : Fin 8)
    have h5 := h (5 : Fin 8)
    have h6 := h (6 : Fin 8)
    have h7 := h (7 : Fin 8)
    simp [all8, h0, h1, h2, h3', h4', h5, h6, h7]


private def proposalAt (X : FCfg) (a : Fin 8) :
    R2.Cell 4 4 64 × R2.Cell 4 4 64 :=
  R2Coherence.proposal h4 h02 h24
    (X a).phys (X (ring8.rightNeighbor a)).phys


private def noWriteB (X : FCfg) (a : Fin 8) : Bool :=
  let j := ring8.rightNeighbor a
  let q := proposalAt X a
  !(R2Coherence.pairWrites (X a).phys.phys (X j).phys.phys q.1 q.2) &&
  !(R2Coherence.pairRelabels (X a).phys.phys (X j).phys.phys q.1 q.2)


private theorem noWriteB_spec (X : FCfg) (a : Fin 8) :
    noWriteB X a = true ↔
      R2Coherence.ProposalNoWrite h4 h02 h24
        (X a).phys (X (ring8.rightNeighbor a)).phys := by
  simp [noWriteB, proposalAt, R2Coherence.ProposalNoWrite]


private def noWriteAllB (X : FCfg) : Bool := all8 (noWriteB X)


private theorem noWriteAllB_spec (X : FCfg) :
    noWriteAllB X = true ↔
      ∀ a : Fin 8, R2Coherence.ProposalNoWrite h4 h02 h24
        (X a).phys (X (ring8.rightNeighbor a)).phys := by
  constructor
  · intro h a
    exact (noWriteB_spec X a).1 ((all8_spec (noWriteB X)).1 h a)
  · intro h
    apply (all8_spec (noWriteB X)).2
    intro a
    exact (noWriteB_spec X a).2 (h a)


#synth Decidable (noWriteAllB C4 = true)
private theorem preNoWriteAllB : noWriteAllB C4 = true := by
  decide +kernel


private theorem preNoWrite (a : Fin 8) :
    R2Coherence.ProposalNoWrite h4 h02 h24
      (C4 a).phys (C4 (ring8.rightNeighbor a)).phys :=
  (noWriteAllB_spec C4).1 preNoWriteAllB a


/-- Real admission, not the sufficient proxy. -/
private theorem admittedC4 : ConcreteB7AdmittedPassive h4 h24 ring8 C4 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i
    change WriterProducerRepair.producerActive
      (R2Coherence.raw (C4 i).phys) = false
    change (decide (WriteState.none = WriteState.produce ∨
      WriteState.none = WriteState.done) : Bool) = false
    rfl
  · intro i
    change
      (R2Coherence.raw (C4 i).phys).path3 = none ∧
      (R2Coherence.raw (C4 i).phys).write = .none ∧
      ((R2Coherence.raw (C4 i).phys).write_state = .none ∨
        (R2Coherence.raw (C4 i).phys).write_state = .depart)
    exact ⟨rfl, rfl, Or.inl rfl⟩
  · intro i
    change
      (C4 i).phys.ctl.mark = .open ∧
      (C4 i).phys.ctl.tok = .none
    exact ⟨rfl, rfl⟩
  · intro e
    exact ⟨noGarbage e, hostAt e, preNoWrite e⟩


private def physC4 : R2Coherence.FC 8 4 4 64 := physicalConfig C4
private def physD : R2Coherence.FC 8 4 4 64 :=
  R2Coherence.step h4 h24 ring8 physC4 1


private noncomputable def D4 : FCfg :=
  stepConcrete (κ := 4) (τ := 64) h4 h24 ring8 C4 1


private theorem rightNe1 : ring8.rightNeighbor (1 : Fin 8) ≠ 1 := by
  intro h
  have hv := congrArg Fin.val h
  change (1 + 1) % 8 = 1 at hv
  omega


/-- Transfer the computable physical R2 successor to the real noncomputable
    `stepConcrete` successor, exactly as in the psi=3 refutation. -/
private theorem D4_phys : physicalConfig D4 = physD := by
  classical
  have hedge := admittedC4.2.2.2 (1 : Fin 8)
  have hg := hedge.1
  have ha :
      (concretePort (κ := 4) (τ := 64) h4 h24).action
        (C4 1) (C4 (ring8.rightNeighbor 1)) = .host := by
    simpa only [concretePort, concretePortLocal] using hedge.2.1
  have hf : finalAction h4 h24
      (concretePort (κ := 4) (τ := 64) h4 h24)
      (C4 1) (C4 (ring8.rightNeighbor 1)) = .host := by
    unfold finalAction
    rw [if_neg hg, ha]
  have hrow : rowFinal h4 h24
      (concretePort (κ := 4) (τ := 64) h4 h24)
      (C4 1) (C4 (ring8.rightNeighbor 1)) =
      (concretePort (κ := 4) (τ := 64) h4 h24).row
        (C4 1) (C4 (ring8.rightNeighbor 1)) := by
    unfold rowFinal
    rw [hf]
  have hstep : D4 =
      B9FullCarrierHost.writeAtP ring8 C4 1
        ((concretePort (κ := 4) (τ := 64) h4 h24).row
          (C4 1) (C4 (ring8.rightNeighbor 1))) := by
    unfold D4 stepConcrete stepFinal
    rw [if_neg rightNe1, hrow]
  have hp :=
    (concretePort (κ := 4) (τ := 64) h4 h24).physical_spec
      (C4 1) (C4 (ring8.rightNeighbor 1))
  simp only [ha] at hp
  calc
    physicalConfig D4 =
      physicalConfig
        (B9FullCarrierHost.writeAtP ring8 C4 1
          ((concretePort (κ := 4) (τ := 64) h4 h24).row
            (C4 1) (C4 (ring8.rightNeighbor 1)))) :=
      congrArg (fun D : FCfg => physicalConfig D) hstep
    _ = B9Host.hostStep
        (hostR2C (κ := 4) (τ := 64) h4 h24) ring8 physC4 1 := by
      funext i
      change
        (B9FullCarrierHost.writeAtP ring8 C4 1
          ((concretePort (κ := 4) (τ := 64) h4 h24).row
            (C4 1) (C4 (ring8.rightNeighbor 1))) i).phys =
        B9Host.hostStep
          (hostR2C (κ := 4) (τ := 64) h4 h24) ring8 physC4 1 i
      by_cases hi : i = (1 : Fin 8)
      · subst i
        rw [B9Host.hostStep_left]
        simp only [B9FullCarrierHost.writeAtP, if_pos rfl]
        exact hp.1
      · by_cases hj : i = ring8.rightNeighbor (1 : Fin 8)
        · subst i
          rw [B9Host.hostStep_right
            (hostR2C (κ := 4) (τ := 64) h4 h24)
            ring8 physC4 1 rightNe1]
          simp only [B9FullCarrierHost.writeAtP,
            if_neg rightNe1, if_pos rfl]
          exact hp.2
        · rw [B9Host.hostStep_other
            (hostR2C (κ := 4) (τ := 64) h4 h24)
            ring8 physC4 1 i hi hj]
          simp only [B9FullCarrierHost.writeAtP, if_neg hi, if_neg hj]
          rfl
    _ = physD := by rfl


private def leaderlessPhysB (X : R2Coherence.FC 8 4 4 64) : Bool :=
  all8 (fun i => !(R2Coherence.raw (X i)).leader)


private theorem leaderlessPhysB_spec (X : R2Coherence.FC 8 4 4 64) :
    leaderlessPhysB X = true ↔
      ∀ i, (R2Coherence.raw (X i)).leader = false := by
  constructor
  · intro h i
    have hb := (all8_spec (fun j => !(R2Coherence.raw (X j)).leader)).1 h i
    simpa using hb
  · intro h
    apply (all8_spec (fun j => !(R2Coherence.raw (X j)).leader)).2
    intro i
    simp [h i]


#synth Decidable (leaderlessPhysB physD = true)
private theorem postLeaderlessB : leaderlessPhysB physD = true := by
  decide +kernel


private theorem physDLeaderless (i : Fin 8) :
    (R2Coherence.raw (physD i)).leader = false :=
  (leaderlessPhysB_spec physD).1 postLeaderlessB i


private theorem D4Leaderless : FinalLeaderless D4 := by
  intro i
  change (R2Coherence.raw ((physicalConfig D4) i)).leader = false
  rw [D4_phys]
  exact physDLeaderless i


private theorem D4NoLeader : ¬ HasLeader D4 := by
  rintro ⟨i, hi⟩
  rw [D4Leaderless i] at hi
  cases hi


private def physProposalAt (X : R2Coherence.FC 8 4 4 64) (a : Fin 8) :
    R2.Cell 4 4 64 × R2.Cell 4 4 64 :=
  R2Coherence.proposal h4 h02 h24 (X a) (X (ring8.rightNeighbor a))


private def relabelPhysB
    (X : R2Coherence.FC 8 4 4 64) (a : Fin 8) : Bool :=
  let j := ring8.rightNeighbor a
  let q := physProposalAt X a
  R2Coherence.pairRelabels (X a).phys (X j).phys q.1 q.2


private theorem relabelPhysB_spec
    (X : R2Coherence.FC 8 4 4 64) (a : Fin 8) :
    relabelPhysB X a = true ↔
      (let j := ring8.rightNeighbor a
       let q := R2Coherence.proposal h4 h02 h24 (X a) (X j)
       R2Coherence.pairRelabels (X a).phys (X j).phys q.1 q.2 = true) := by
  rfl


set_option maxHeartbeats 800000000 in
set_option maxRecDepth 100000 in
/-- The decisive finite physical fact, now consumed by the Prop proof. -/
private theorem postRelabel2B : relabelPhysB physD (2 : Fin 8) = true := by
  rfl


private theorem D4NotAdmitted :
    ¬ ConcreteB7AdmittedPassive h4 h24 ring8 D4 := by
  intro hA
  have hNW := (hA.2.2.2 (2 : Fin 8)).2.2
  unfold R2Coherence.ProposalNoWrite at hNW
  dsimp only at hNW
  have hRel : relabelPhysB (physicalConfig D4) (2 : Fin 8) = true := by
    rw [D4_phys]
    exact postRelabel2B
  have hTrue :=
    (relabelPhysB_spec (physicalConfig D4) (2 : Fin 8)).1 hRel
  dsimp only at hTrue
  change
    R2Coherence.pairRelabels
      (D4 (2 : Fin 8)).phys.phys
      (D4 (ring8.rightNeighbor (2 : Fin 8))).phys.phys
      (R2Coherence.proposal h4 h02 h24
        (D4 (2 : Fin 8)).phys
        (D4 (ring8.rightNeighbor (2 : Fin 8))).phys).1
      (R2Coherence.proposal h4 h02 h24
        (D4 (2 : Fin 8)).phys
        (D4 (ring8.rightNeighbor (2 : Fin 8))).phys).2 = true at hTrue
  have hFalse := hNW.2
  rw [hTrue] at hFalse
  cases hFalse


/-- Parameter-scoped real refutation at psi=4, kappa=4, tau=64, n=8. -/
theorem not_concreteB7AdmittedPassiveClosedObligation_psi4_n8 :
    ¬ ConcreteB7AdmittedPassiveClosedObligation
      (κ := 4) (τ := 64) h4 h24 ring8 := by
  intro hClosed
  have h := hClosed C4 (1 : Fin 8) admittedC4 preLeaderless
  change HasLeader D4 ∨ ConcreteB7AdmittedPassive h4 h24 ring8 D4 at h
  exact h.elim D4NoLeader D4NotAdmitted


#print axioms not_concreteB7AdmittedPassiveClosedObligation_psi4_n8


end B4PassiveClosureRefutationPsi4
end FinalCandidateR2C
end FinalCandidateR2C
end FinalCandidateR2C
end FinalCandidateR2C
end FinalCandidateR2C
