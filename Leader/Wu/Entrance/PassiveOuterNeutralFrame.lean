import Leader.Wu.Entrance.PassiveRelabelExit
import Leader.Wu.Entrance.ConcretePort
import Leader.Wu.Splice.FullCarrierRows
import Leader.Wu.Splice.HostQuiescence

set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096

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
open BirthLeaderlessBirthMassRenewal
open B9SpliceControllerR1Table B9SpliceControllerR1TableV7
open B9SpliceTableHost

variable {n ψ κ τ : Nat}

/-- Accepted-side restatement of
`FullRowPortFaithful.concretePort_controller_faithful`.
Source equality: Leader/FullRowPortFaithful.lean:145-151. -/
def ConcretePortControllerFaithfulObligation
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) : Prop :=
  ∀ l r : Cell ψ κ τ,
    (oldCell
        ((concretePort (κ := κ) (τ := τ) hψ h2).row l r).1,
      oldCell
        ((concretePort (κ := κ) (τ := τ) hψ h2).row l r).2) =
      B9SpliceTableHost.rowB9
        (B9FullCarrierHost.shadowHostAt
          (carrierLaws (ψ := ψ) (κ := κ) (τ := τ))
          (hostR2C (κ := κ) (τ := τ) hψ h2)
          l.phys r.phys)
        hψ (oldCell l) (oldCell r)

private theorem q13665_proposalNoWrite_right_label
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ)
    (l r : R2Coherence.Cell ψ κ τ)
    (hNo : R2Coherence.ProposalNoWrite
      hψ (by decide : 0 < 2) h2 l r) :
    ((R2Coherence.proposal hψ (by decide : 0 < 2) h2 l r).2).base.core.core.label =
      r.phys.base.core.core.label := by
  change
    R2Coherence.pairWrites l.phys r.phys
        (R2Coherence.proposal hψ (by decide : 0 < 2) h2 l r).1
        (R2Coherence.proposal hψ (by decide : 0 < 2) h2 l r).2 = false ∧
      R2Coherence.pairRelabels l.phys r.phys
        (R2Coherence.proposal hψ (by decide : 0 < 2) h2 l r).1
        (R2Coherence.proposal hψ (by decide : 0 < 2) h2 l r).2 = false at hNo
  by_cases hEq :
      ((R2Coherence.proposal hψ (by decide : 0 < 2) h2 l r).2).base.core.core.label =
        r.phys.base.core.core.label
  · exact hEq
  · have hNe :
        r.phys.base.core.core.label ≠
          ((R2Coherence.proposal hψ (by decide : 0 < 2) h2 l r).2).base.core.core.label := by
      intro h
      exact hEq h.symm
    have hchg :
        R2Coherence.labelChanged r.phys
          (R2Coherence.proposal hψ (by decide : 0 < 2) h2 l r).2 = true := by
      unfold R2Coherence.labelChanged
      simp [hNe]
    have hrel := hNo.2
    unfold R2Coherence.pairRelabels at hrel
    rw [hchg] at hrel
    simp at hrel

private theorem q13665_hostR2C_right_label
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ)
    (l r : R2Coherence.Cell ψ κ τ)
    (hOpenL : R2Coherence.OpenControl l)
    (hOpenR : R2Coherence.OpenControl r)
    (hNo : R2Coherence.ProposalNoWrite
      hψ (by decide : 0 < 2) h2 l r) :
    (((hostR2C (κ := κ) (τ := τ) hψ h2).row l r).2).phys.base.core.core.label =
      r.phys.base.core.core.label := by
  rcases hOpenL with ⟨hlm, hlt⟩
  rcases hOpenR with ⟨hrm, hrt⟩
  have hrow := R2Coherence.row_eq_r2_of_open_no_write
    hψ (by decide : 0 < 2) h2 l r hlm hrm hlt hrt hNo
  have hlabel := q13665_proposalNoWrite_right_label hψ h2 l r hNo
  change
    ((R2Coherence.row hψ (by decide : 0 < 2) h2 l r).2).phys.base.core.core.label =
      r.phys.base.core.core.label
  rw [hrow]
  simpa [R2Coherence.install] using hlabel

private theorem q13665_oldCell_neutral_iff
    (u : Cell ψ κ τ) :
    B9SpliceHostQuiescence.Neutral (oldCell u) ↔
      NeutralController u := by
  change
    (u.spliceRole = .none ∧
      u.repairPending = false ∧ u.acquireTicket = false) ↔
    (u.spliceRole = .none ∧
      u.repairPending = false ∧ u.acquireTicket = false)
  exact Iff.rfl

private theorem q13665_shadow_no_right_relabel
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ)
    (l r : Cell ψ κ τ)
    (hOpenL : R2Coherence.OpenControl l.phys)
    (hOpenR : R2Coherence.OpenControl r.phys)
    (hNo : R2Coherence.ProposalNoWrite
      hψ (by decide : 0 < 2) h2 l.phys r.phys) :
    rightFollowerRelabelledV7 (oldCell r).carrier
      (ordinaryRowH
        (B9FullCarrierHost.shadowHostAt
          (carrierLaws (ψ := ψ) (κ := κ) (τ := τ))
          (hostR2C (κ := κ) (τ := τ) hψ h2)
          l.phys r.phys)
        (oldCell l).carrier (oldCell r).carrier).2 = false := by
  have hlabel :
      (ordinaryRowH
        (B9FullCarrierHost.shadowHostAt
          (carrierLaws (ψ := ψ) (κ := κ) (τ := τ))
          (hostR2C (κ := κ) (τ := τ) hψ h2)
          l.phys r.phys)
        (oldCell l).carrier (oldCell r).carrier).2.splice.base.core.core.label =
      (oldCell r).carrier.splice.base.core.core.label := by
    change
      (((hostR2C (κ := κ) (τ := τ) hψ h2).row l.phys r.phys).2).phys.base.core.core.label =
        r.phys.phys.base.core.core.label
    exact q13665_hostR2C_right_label
      hψ h2 l.phys r.phys hOpenL hOpenR hNo
  unfold rightFollowerRelabelledV7
  simp [hlabel]


/-- The local fact: after the relabel arm is excluded,
there is no HOST-tagged neutral-input leak in the concrete full port. -/
theorem q13665_concretePort_neutral_pair_frame
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ)
    (l r : Cell ψ κ τ)
    (hNL : NeutralController l)
    (hNR : NeutralController r)
    (hLeadL : outputFinal l = false)
    (hOpenL : R2Coherence.OpenControl l.phys)
    (hOpenR : R2Coherence.OpenControl r.phys)
    (hNo : R2Coherence.ProposalNoWrite
      hψ (by decide : 0 < 2) h2 l.phys r.phys)
    (hFaith : ConcretePortControllerFaithfulObligation
      (κ := κ) (τ := τ) hψ h2) :
    let q := (concretePort (κ := κ) (τ := τ) hψ h2).row l r
    NeutralController q.1 ∧ NeutralController q.2 := by
  have hlOld : B9SpliceHostQuiescence.Neutral (oldCell l) :=
    (q13665_oldCell_neutral_iff l).2 hNL
  have hrOld : B9SpliceHostQuiescence.Neutral (oldCell r) :=
    (q13665_oldCell_neutral_iff r).2 hNR
  have hleadOld :
      (oldCell l).carrier.splice.base.core.core.leader = false := by
    change outputFinal l = false
    exact hLeadL
  have hrel := q13665_shadow_no_right_relabel
    hψ h2 l r hOpenL hOpenR hNo
  have hrow := B9SpliceHostQuiescence.neutral_row
    (B9FullCarrierHost.shadowHostAt
      (carrierLaws (ψ := ψ) (κ := κ) (τ := τ))
      (hostR2C (κ := κ) (τ := τ) hψ h2)
      l.phys r.phys)
    hψ (oldCell l) (oldCell r) hlOld hrOld hleadOld hrel
  have hfaith := hFaith l r
  change
    (oldCell ((concretePort (κ := κ) (τ := τ) hψ h2).row l r).1,
      oldCell ((concretePort (κ := κ) (τ := τ) hψ h2).row l r).2) =
      rowB9
        (B9FullCarrierHost.shadowHostAt
          (carrierLaws (ψ := ψ) (κ := κ) (τ := τ))
          (hostR2C (κ := κ) (τ := τ) hψ h2)
          l.phys r.phys)
        hψ (oldCell l) (oldCell r) at hfaith
  have hpair := hfaith.trans hrow
  have hquietL :
      B9SpliceHostQuiescence.Neutral
        (B9SpliceHostQuiescence.quietWrite
          (B9FullCarrierHost.shadowHostAt
            (carrierLaws (ψ := ψ) (κ := κ) (τ := τ))
            (hostR2C (κ := κ) (τ := τ) hψ h2)
            l.phys r.phys)
          (oldCell l) (oldCell r)).1 := by
    unfold B9SpliceHostQuiescence.Neutral
    constructor
    · change role (oldCell l).carrier = .none
      exact hlOld.1
    · constructor
      · change (oldCell l).carrier.repairPending = false
        exact hlOld.2.1
      · rfl
  have hquietR :
      B9SpliceHostQuiescence.Neutral
        (B9SpliceHostQuiescence.quietWrite
          (B9FullCarrierHost.shadowHostAt
            (carrierLaws (ψ := ψ) (κ := κ) (τ := τ))
            (hostR2C (κ := κ) (τ := τ) hψ h2)
            l.phys r.phys)
          (oldCell l) (oldCell r)).2 := by
    unfold B9SpliceHostQuiescence.Neutral
    constructor
    · change role (oldCell r).carrier = .none
      exact hrOld.1
    · constructor
      · change (oldCell r).carrier.repairPending = false
        exact hrOld.2.1
      · rfl
  have hOldL :
      B9SpliceHostQuiescence.Neutral
        (oldCell ((concretePort (κ := κ) (τ := τ) hψ h2).row l r).1) := by
    have heq :
        oldCell (((concretePort (κ := κ) (τ := τ) hψ h2).row l r).1) =
          (B9SpliceHostQuiescence.quietWrite
            (B9FullCarrierHost.shadowHostAt
              (carrierLaws (ψ := ψ) (κ := κ) (τ := τ))
              (hostR2C (κ := κ) (τ := τ) hψ h2)
              l.phys r.phys)
            (oldCell l) (oldCell r)).1 := by
      simpa only using congrArg Prod.fst hpair
    rw [heq]
    exact hquietL
  have hOldR :
      B9SpliceHostQuiescence.Neutral
        (oldCell ((concretePort (κ := κ) (τ := τ) hψ h2).row l r).2) := by
    have heq :
        oldCell (((concretePort (κ := κ) (τ := τ) hψ h2).row l r).2) =
          (B9SpliceHostQuiescence.quietWrite
            (B9FullCarrierHost.shadowHostAt
              (carrierLaws (ψ := ψ) (κ := κ) (τ := τ))
              (hostR2C (κ := κ) (τ := τ) hψ h2)
              l.phys r.phys)
            (oldCell l) (oldCell r)).2 := by
      simpa only using congrArg Prod.snd hpair
    rw [heq]
    exact hquietR
  exact ⟨
    (q13665_oldCell_neutral_iff _).1 hOldL,
    (q13665_oldCell_neutral_iff _).1 hOldR⟩


/-- Exact missing global premise.  It is not a field of
`ConcreteB7AdmittedPassive` on current main. -/
def ConcreteB7PassiveInputOuterNeutralObligation
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ)
    (ring : DirectedRing n) : Prop :=
  ∀ C : Config n ψ κ τ,
    ConcreteB7AdmittedPassive hψ h2 ring C →
    FinalLeaderless C →
    ∀ i : Fin n, NeutralController (C i)

/-- Once the genuinely missing input-neutrality fact and the explicit
controller-faithfulness fact are supplied, the requested post theorem is
immediate from the concrete-port pair frame plus `writeAtP` locality. -/
theorem concreteB7PassiveOuterNeutralPost_of_input_outer_neutral
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ)
    (ring : DirectedRing n)
    (hInput : ConcreteB7PassiveInputOuterNeutralObligation
      (κ := κ) (τ := τ) hψ h2 ring)
    (hFaith : ConcretePortControllerFaithfulObligation
      (κ := κ) (τ := τ) hψ h2) :
    ConcreteB7PassiveOuterNeutralPostObligation
      (κ := κ) (τ := τ) hψ h2 ring := by
  intro C e hA hL
  dsimp only
  intro _hD i
  have hN : ∀ a : Fin n, NeutralController (C a) :=
    hInput C hA hL
  by_cases hs : ring.rightNeighbor e = e
  · have hg := (hA.2.2.2 e).1
    have hgs : ¬ FinalGarbage hψ (C e) (C e) := by
      simpa only [hs] using hg
    have hstep :
        stepConcrete (κ := κ) (τ := τ) hψ h2 ring C e = C := by
      unfold stepConcrete stepFinal
      rw [if_pos hs, if_neg hgs]
    rw [hstep]
    exact hN i
  · have hedge := hA.2.2.2 e
    have hg := hedge.1
    have ha :
        (concretePort (κ := κ) (τ := τ) hψ h2).action
          (C e) (C (ring.rightNeighbor e)) = .host := by
      simpa only [concretePort, concretePortLocal] using hedge.2.1
    have hfa :
        finalAction hψ h2
          (concretePort (κ := κ) (τ := τ) hψ h2)
          (C e) (C (ring.rightNeighbor e)) = .host := by
      unfold finalAction
      rw [if_neg hg, ha]
    have hrow :
        rowFinal hψ h2
          (concretePort (κ := κ) (τ := τ) hψ h2)
          (C e) (C (ring.rightNeighbor e)) =
        (concretePort (κ := κ) (τ := τ) hψ h2).row
          (C e) (C (ring.rightNeighbor e)) := by
      unfold rowFinal
      rw [hfa]
    have hstep :
        stepConcrete (κ := κ) (τ := τ) hψ h2 ring C e =
          B9FullCarrierHost.writeAtP ring C e
            ((concretePort (κ := κ) (τ := τ) hψ h2).row
              (C e) (C (ring.rightNeighbor e))) := by
      unfold stepConcrete stepFinal
      rw [if_neg hs, hrow]
    have hpair := q13665_concretePort_neutral_pair_frame
      hψ h2 (C e) (C (ring.rightNeighbor e))
      (hN e) (hN (ring.rightNeighbor e)) (hL e)
      (hA.2.2.1 e) (hA.2.2.1 (ring.rightNeighbor e)) hedge.2.2 hFaith
    by_cases hi : i = e
    · subst i
      rw [hstep]
      simp only [B9FullCarrierHost.writeAtP, if_pos rfl]
      exact hpair.1
    · by_cases hj : i = ring.rightNeighbor e
      · subst i
        rw [hstep]
        simp only [B9FullCarrierHost.writeAtP, if_neg hs, if_pos rfl]
        exact hpair.2
      · rw [hstep]
        simp only [B9FullCarrierHost.writeAtP, if_neg hi, if_neg hj]
        exact hN i

end FinalCandidateR2C
end FinalCandidateR2C
end FinalCandidateR2C
end FinalCandidateR2C
end FinalCandidateR2C
