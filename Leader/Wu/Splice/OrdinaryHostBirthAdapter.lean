import Leader.Wu.Splice.OrdinaryBirthLabelPriority
import Leader.Wu.Splice.OrdinaryLeftLeaderFrame

set_option autoImplicit false
set_option Elab.async false
set_option pp.structureInstances false

namespace B9SpliceV8BirthCaseAdapter

open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
  PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
  PPLLLeaderCreationCleanupRepair
open BirthShortDoneTerminalHost BirthSigMoveDisposalRepair
  K2BirthDispatcher ExpiringK2Projection
open B9SpliceV8LabelFrame B9SpliceV8BirthCaseAdapterLabelProjection

variable {psi width kappa tau : Nat}

private theorem authSignal_left_leader
    {q p : AuthorizedAgentState psi × AuthorizedAgentState psi}
    (h : authSignalPair q = authSignalPair p) :
    q.1.core.leader = p.1.core.leader := by
  have hl := congrArg (fun z : AgentState 1 × AgentState 1 => z.1.leader) h
  change q.1.core.leader = p.1.core.leader at hl
  exact hl

private theorem normalizeDeletion_leader_local (u : AuthorizedAgentState psi) :
    (normalizeDeletion u).core.leader = u.core.leader := by
  unfold normalizeDeletion
  split <;> rfl

private theorem authorizedEntry_left_leader
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (l r : AuthorizedAgentState psi) :
    (doneMetadataAuthorizedEntryWidth hpsi hwidth hle kappa l r).1.core.leader =
      l.core.leader := by
  let l0 := normalizeDeletion l
  let r0 := normalizeDeletion r
  have hl0 : l0.core.leader = l.core.leader := normalizeDeletion_leader_local l
  unfold doneMetadataAuthorizedEntryWidth
  dsimp only
  split
  · exact (authSignal_left_leader (eliminate_signal hpsi l0 r0)).trans hl0
  · split
    · exact hl0
    · exact B9SpliceV8LeftLeaderFrame.ordinary_normalized_left_leader
        (kappa := kappa) hpsi hwidth hle l r

theorem metadataEntry_left_leader
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (l r : ExpiringAgentState psi kappa tau) :
    (doneMetadataEntryWidth hpsi hwidth hle l r).1.core.core.leader =
      l.core.core.leader := by
  let pl := prepareExpiringDisposal hpsi l
  let pr := prepareExpiringDisposal hpsi r
  let a := doneMetadataAuthorizedEntryWidth hpsi hwidth hle kappa
    pl.core.erase pr.core.erase
  let d := doneMetadataEntryWidth hpsi hwidth hle l r
  have ha := authorizedEntry_left_leader (kappa := kappa)
    hpsi hwidth hle pl.core.erase pr.core.erase
  change a.1.core.leader = pl.core.erase.core.leader at ha
  have hp := congrArg AgentState.leader (prepareExpiring_signal hpsi l)
  change pl.core.erase.core.leader = l.core.core.leader at hp
  have ho := BirthShortDoneTerminalConsumer.doneMetadataEntryWidth_observation
    hpsi hwidth hle l r
  have hd := congrArg (fun z : AgentState 1 × AgentState 1 => z.1.leader) ho
  change d.1.core.core.leader = a.1.core.leader at hd
  exact hd.trans (ha.trans hp)

theorem ordinary_left_label
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (l r : AuthorizedAgentState psi) :
    (doneOrdinaryMetadataEntryWidth hpsi hwidth hle kappa l r).1.core.label =
      l.core.label :=
  B9SpliceV8BirthCaseAdapterLabelProjection.ordinary_left_label
    (kappa := kappa) hpsi hwidth hle l r

private theorem authorizedEntry_eq_ordinary_false_false
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (l r : AuthorizedAgentState psi) :
    (if false = true then
        authorizedEliminateSig hpsi (normalizeDeletion l) (normalizeDeletion r)
      else if false = true then
        (normalizeDeletion l, normalizeDeletion r)
      else doneOrdinaryMetadataEntryWidth hpsi hwidth hle kappa
        (normalizeDeletion l) (normalizeDeletion r)) =
      doneOrdinaryMetadataEntryWidth hpsi hwidth hle kappa
        (normalizeDeletion l) (normalizeDeletion r) := by
  calc
    (if false = true then
        authorizedEliminateSig hpsi (normalizeDeletion l) (normalizeDeletion r)
      else if false = true then
        (normalizeDeletion l, normalizeDeletion r)
      else doneOrdinaryMetadataEntryWidth hpsi hwidth hle kappa
        (normalizeDeletion l) (normalizeDeletion r)) =
        (if false = true then
          (normalizeDeletion l, normalizeDeletion r)
        else doneOrdinaryMetadataEntryWidth hpsi hwidth hle kappa
          (normalizeDeletion l) (normalizeDeletion r)) := if_neg Bool.false_ne_true
    _ = doneOrdinaryMetadataEntryWidth hpsi hwidth hle kappa
        (normalizeDeletion l) (normalizeDeletion r) := if_neg Bool.false_ne_true

private theorem authorizedEntry_eq_ordinary
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (l r : AuthorizedAgentState psi)
    (hr : deletionActive (normalizeDeletion r) = false)
    (hl : deletionActive (normalizeDeletion l) = false) :
    doneMetadataAuthorizedEntryWidth hpsi hwidth hle kappa l r =
      doneOrdinaryMetadataEntryWidth hpsi hwidth hle kappa
        (normalizeDeletion l) (normalizeDeletion r) := by
  unfold doneMetadataAuthorizedEntryWidth
  dsimp only
  rw [hr, hl]
  have hordinary :
      (if false = true then
          authorizedEliminateSig hpsi (normalizeDeletion l) (normalizeDeletion r)
        else if false = true then
          (normalizeDeletion l, normalizeDeletion r)
        else doneOrdinaryMetadataEntryWidth hpsi hwidth hle kappa
          (normalizeDeletion l) (normalizeDeletion r)) =
        doneOrdinaryMetadataEntryWidth hpsi hwidth hle kappa
          (normalizeDeletion l) (normalizeDeletion r) := by
    exact authorizedEntry_eq_ordinary_false_false
      (kappa := kappa) hpsi hwidth hle l r
  exact hordinary

theorem metadataEntry_left_label
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (L R : ExpiringAgentState psi kappa tau) :
    (doneMetadataEntryWidth hpsi hwidth hle L R).1.core.core.label =
      L.core.core.label := by
  by_cases hr : deletionActive
      (normalizeDeletion (prepareExpiringDisposal hpsi R).core.erase) = true
  · exact (host_responder_deletion_label_frame (kappa := kappa) (tau := tau)
      hpsi hwidth hle L R hr).1
  · have hrf : deletionActive
        (normalizeDeletion (prepareExpiringDisposal hpsi R).core.erase) = false := by
      cases h : deletionActive
          (normalizeDeletion (prepareExpiringDisposal hpsi R).core.erase) with
      | false => rfl
      | true => exact (hr h).elim
    by_cases hl : deletionActive
        (normalizeDeletion (prepareExpiringDisposal hpsi L).core.erase) = true
    · exact (host_initiator_deletion_label_frame (kappa := kappa) (tau := tau)
        hpsi hwidth hle L R hrf hl).1
    · have hlf : deletionActive
          (normalizeDeletion (prepareExpiringDisposal hpsi L).core.erase) = false := by
        cases h : deletionActive
            (normalizeDeletion (prepareExpiringDisposal hpsi L).core.erase) with
        | false => rfl
        | true => exact (hl h).elim
      let pl := prepareExpiringDisposal hpsi L
      let pr := prepareExpiringDisposal hpsi R
      let b := doneMetadataBoundedEntryWidth hpsi hwidth hle pl.core pr.core
      let xL : ExpiringAgentState psi kappa tau := ⟨b.1, pl.stall⟩
      let a := doneMetadataAuthorizedEntryWidth hpsi hwidth hle kappa
        pl.core.erase pr.core.erase
      have he := doneMetadataBoundedEntryWidth_erase hpsi hwidth hle pl.core pr.core
      have hel := congrArg (fun z : AuthorizedAgentState psi => z.core.label)
        (congrArg Prod.fst he)
      change xL.core.core.label = a.1.core.label at hel
      have hauth :
          doneMetadataAuthorizedEntryWidth hpsi hwidth hle kappa
              pl.core.erase pr.core.erase =
            doneOrdinaryMetadataEntryWidth hpsi hwidth hle kappa
              (normalizeDeletion pl.core.erase) (normalizeDeletion pr.core.erase) := by
        exact authorizedEntry_eq_ordinary (kappa := kappa)
          hpsi hwidth hle pl.core.erase pr.core.erase hrf hlf
      have hauthL := congrArg
        (fun z : AuthorizedAgentState psi × AuthorizedAgentState psi => z.1.core.label)
        hauth
      have ha : a.1.core.label = L.core.core.label := by
        change (doneMetadataAuthorizedEntryWidth hpsi hwidth hle kappa
          pl.core.erase pr.core.erase).1.core.label = L.core.core.label
        exact hauthL.trans
          ((ordinary_left_label (kappa := kappa) hpsi hwidth hle
              (normalizeDeletion pl.core.erase) (normalizeDeletion pr.core.erase)).trans
            ((normalizeDeletion_label_local pl.core.erase).trans
              (prepared_label_local hpsi L)))
      have hx := deletionPriorityExpireOne_label_frame (kappa := kappa) (tau := tau)
        pl xL
      change (deletionPriorityExpireOne tau pl xL).core.core.label =
        xL.core.core.label at hx
      change (deletionPriorityExpireOne tau pl xL).core.core.label = L.core.core.label
      exact hx.trans (hel.trans ha)

end B9SpliceV8BirthCaseAdapter

#print axioms B9SpliceV8BirthCaseAdapter.ordinary_left_label
#print axioms B9SpliceV8BirthCaseAdapter.metadataEntry_left_leader
#print axioms B9SpliceV8BirthCaseAdapter.metadataEntry_left_label
