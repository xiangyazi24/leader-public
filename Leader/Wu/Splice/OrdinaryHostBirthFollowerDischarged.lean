import Leader.Wu.Splice.OrdinaryHostBirthAdapter

set_option autoImplicit false
set_option Elab.async false
set_option pp.structureInstances false

namespace B9SpliceV8BirthCaseUnconditional

open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
  PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
open PPLLLeaderCreationCleanupRepair BirthSigMoveDisposalRepair
open BirthShortDoneTerminalHost K2BirthLeaderNormalize
open Q11593SpliceControllerDesign
open B9SpliceControllerR1Table B9SpliceControllerR1TableV2
  B9SpliceControllerR1TableV3 B9SpliceControllerR1TableV4
  B9SpliceControllerR1TableV6 B9SpliceControllerR1TableV7
  B9SpliceControllerR1TableV8 B9SpliceV8LabelFrame
open B9SpliceV8OrdinaryHost B9SpliceV8BirthCaseAdapter

variable {n psi width kappa tau : Nat}

private theorem ordinary_left_role
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (l r : R1AgentStateV6 psi kappa tau) :
    role (ordinaryHostWriteV7 hpsi hwidth hle l r).1.carrier = role l.carrier := by
  unfold ordinaryHostWriteV7
  simp only []
  split
  · change role (ordinaryRow hpsi hwidth hle l.carrier r.carrier).1 = role l.carrier
    unfold ordinaryRow
    rfl
  · change role (ordinaryRow hpsi hwidth hle l.carrier r.carrier).1 = role l.carrier
    unfold ordinaryRow
    rfl

private theorem ordinary_no_left_deletion
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (l r : R1AgentStateV6 psi kappa tau)
    (hneutral : OrdinaryNeutralPairV8 l r)
    (hrow : rowV8 hpsi hwidth hle l r =
      ordinaryHostWriteV7 hpsi hwidth hle l r) :
    ¬ LeftDeletionCandidate hpsi hwidth hle l.carrier.splice r.carrier.splice := by
  rcases hneutral with
    ⟨hlRole, hlPend, hlTicket, hrRole, hrPend, hrTicket⟩
  intro hd
  have hstale : ¬ RightStalePredecessorHoldGuardV8 l r := by
    intro hs
    have hbad : (SpliceRole.none : SpliceRole) = .predecessorArmed :=
      hrRole.symm.trans hs.2.2.2.1
    cases hbad
  have hfL : ¬ HostFenceShapeV7 l := by
    intro hf
    have hbad : (false : Bool) = true := hlTicket.symm.trans hf.2.2
    cases hbad
  have hfR : ¬ HostFenceShapeV7 r := by
    intro hf
    have hbad : (false : Bool) = true := hrTicket.symm.trans hf.2.2
    cases hbad
  have hacq : ¬ MoveAcquireFrontGuardV6 hpsi l r := by
    intro ha
    have hbad : (SpliceRole.none : SpliceRole) = .front :=
      hlRole.symm.trans ha.1.1
    cases hbad
  have harm : ArmAGuard hpsi hwidth hle l.carrier r.carrier :=
    ⟨hlRole, hrRole, hlPend, hrPend, hd⟩
  have hv : role (rowV8 hpsi hwidth hle l r).1.carrier = .victimArmed := by
    unfold rowV8
    rw [if_neg hstale]
    unfold rowV7
    rw [if_neg hfL, if_neg hfR, if_neg hacq, if_pos harm]
    rfl
  have heq := congrArg
    (fun z : R1AgentStateV6 psi kappa tau × R1AgentStateV6 psi kappa tau =>
      role z.1.carrier) hrow
  have hn : role (ordinaryHostWriteV7 hpsi hwidth hle l r).1.carrier = .none :=
    (ordinary_left_role hpsi hwidth hle l r).trans hlRole
  have hbad : (SpliceRole.victimArmed : SpliceRole) = .none :=
    hv.symm.trans (heq.trans hn)
  cases hbad

/-- Exact physical adapter in the shape consumed by the conditional birth proof. -/
theorem left_follower_label_frame_for_birth
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (l r : R1AgentStateV6 psi kappa tau)
    (hneutral : OrdinaryNeutralPairV8 l r)
    (hrow : rowV8 hpsi hwidth hle l r =
      ordinaryHostWriteV7 hpsi hwidth hle l r)
    (hout : (BirthShortDoneTerminalHost.row hpsi hwidth hle
      l.carrier.splice.base r.carrier.splice.base).1.core.core.leader = false) :
    (BirthShortDoneTerminalHost.row hpsi hwidth hle
      l.carrier.splice.base r.carrier.splice.base).1.core.core.label =
      l.carrier.splice.base.core.core.label := by
  let L := l.carrier.splice.base
  let R := r.carrier.splice.base
  let d := doneMetadataEntryWidth hpsi hwidth hle L R
  have hnoDel := ordinary_no_left_deletion
    (kappa := kappa) (tau := tau) hpsi hwidth hle l r hneutral hrow
  have hLfalse : L.core.core.leader = false := by
    change l.carrier.splice.base.core.core.leader = false
    cases hl : l.carrier.splice.base.core.core.leader with
    | false => rfl
    | true => exact (hnoDel ⟨hl, hout⟩).elim
  have hdfalse : d.1.core.core.leader = false :=
    (metadataEntry_left_leader (kappa := kappa) (tau := tau)
      hpsi hwidth hle L R).trans hLfalse
  let m := BirthShortDoneTerminalHost.metadata hpsi hwidth hle L R
  have hnlabel : m.1.core.core.label = d.1.core.core.label := by
    change (normalizeLeader hpsi d.1).core.core.label = d.1.core.core.label
    unfold normalizeLeader
    rw [hdfalse]
    rfl
  have hrowlabel := hostRow_labels_metadata
    (kappa := kappa) (tau := tau) hpsi hwidth hle L R
  have hdlabel := metadataEntry_left_label
    (kappa := kappa) (tau := tau) hpsi hwidth hle L R
  change (BirthShortDoneTerminalHost.row hpsi hwidth hle L R).1.core.core.label =
    L.core.core.label
  exact hrowlabel.1.trans (hnlabel.trans hdlabel)

/-- V8 ordinary physical-birth safety with the left-follower premise discharged. -/
theorem ordinary_birth_preserves_spliceSafeV7_unconditional
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (ring : DirectedRing n) :
    OrdinaryBirthBranchStatement (kappa := kappa) (tau := tau)
      hpsi hwidth hle ring := by
  exact B9SpliceV8BirthCase.ordinary_birth_preserves_spliceSafeV7
    (kappa := kappa) (tau := tau) hpsi hwidth hle ring
    (fun l r hn hr ho =>
      left_follower_label_frame_for_birth
        (kappa := kappa) (tau := tau) hpsi hwidth hle l r hn hr ho)

#print axioms B9SpliceV8BirthCaseUnconditional.left_follower_label_frame_for_birth
#print axioms B9SpliceV8BirthCaseUnconditional.ordinary_birth_preserves_spliceSafeV7_unconditional

end B9SpliceV8BirthCaseUnconditional
