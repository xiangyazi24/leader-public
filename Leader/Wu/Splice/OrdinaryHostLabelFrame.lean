import Leader.Wu.Splice.StaleHoldTable
import Leader.Wu.Birth.ShortDoneTerminalOrdinaryLabel

set_option autoImplicit false
set_option Elab.async false
set_option pp.structureInstances false

namespace B9SpliceV8LabelFrame

open PPLL PPLLRepair PPLLResearchFormulation
  PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
  PPLLLeaderCreationCleanupRepair
open PPLLWallSweepNormalResetContract
open BirthSigMoveDisposalRepair
open BirthShortDoneTerminalHost
open BirthShortDoneTerminalOrdinaryLabelR1
open K2BirthLeaderNormalize
open B9SpliceControllerR1Table
open B9SpliceControllerR1TableV3
open B9SpliceControllerR1TableV6
open B9SpliceControllerR1TableV7
open B9SpliceControllerR1TableV8

variable {n psi width kappa tau : Nat}

private theorem normalizeDeletion_label_local
    (u : AuthorizedAgentState psi) :
    (normalizeDeletion u).core.label = u.core.label := by
  unfold normalizeDeletion
  split <;> rfl

private theorem prepared_label_local
    (hpsi : 0 < psi) (u : ExpiringAgentState psi kappa tau) :
    (prepareExpiringDisposal hpsi u).core.erase.core.label =
      u.core.core.label := by
  change (prepareBoundedDisposal hpsi u.core).erase.core.label =
    u.core.core.label
  rw [erase_prepareBoundedDisposal]
  unfold prepareDisposal
  split
  · unfold markComparisonForDeletion
    split <;> rfl
  · rfl

/-- Outer deletion-priority refresh / path expiry never writes a label. -/
theorem deletionPriorityExpireOne_label_frame
    (old out : ExpiringAgentState psi kappa tau) :
    (deletionPriorityExpireOne tau old out).core.core.label =
      out.core.core.label := by
  have h := congrArg (fun z => z.label)
    (deletionPriorityExpireOne_peaceView_frame old out)
  change (deletionPriorityExpireOne tau old out).core.core.label =
    out.core.core.label at h
  exact h

private theorem metadataEntry_authorized_label_frame
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (l r : ExpiringAgentState psi kappa tau) :
    let pl := prepareExpiringDisposal hpsi l
    let pr := prepareExpiringDisposal hpsi r
    let a := doneMetadataAuthorizedEntryWidth
      hpsi hwidth hle kappa pl.core.erase pr.core.erase
    let d := doneMetadataEntryWidth hpsi hwidth hle l r
    d.1.core.core.label = a.1.core.label ∧
      d.2.core.core.label = a.2.core.label := by
  let pl := prepareExpiringDisposal hpsi l
  let pr := prepareExpiringDisposal hpsi r
  let b := doneMetadataBoundedEntryWidth hpsi hwidth hle pl.core pr.core
  let xL : ExpiringAgentState psi kappa tau := ⟨b.1, pl.stall⟩
  let xR : ExpiringAgentState psi kappa tau := ⟨b.2, pr.stall⟩
  let a := doneMetadataAuthorizedEntryWidth
    hpsi hwidth hle kappa pl.core.erase pr.core.erase
  have he := doneMetadataBoundedEntryWidth_erase
    hpsi hwidth hle pl.core pr.core
  have hel := congrArg (fun z : AuthorizedAgentState psi => z.core.label)
    (congrArg Prod.fst he)
  have her := congrArg (fun z : AuthorizedAgentState psi => z.core.label)
    (congrArg Prod.snd he)
  change xL.core.core.label = a.1.core.label at hel
  change xR.core.core.label = a.2.core.label at her
  have hl := deletionPriorityExpireOne_label_frame pl xL
  have hr := deletionPriorityExpireOne_label_frame pr xR
  unfold doneMetadataEntryWidth
  exact ⟨hl.trans hel, hr.trans her⟩

private theorem responderDelete_authorized_labels
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (l r : AuthorizedAgentState psi)
    (hr : deletionActive (normalizeDeletion r) = true) :
    let q := doneMetadataAuthorizedEntryWidth hpsi hwidth hle kappa l r
    q.1.core.label = l.core.label ∧ q.2.core.label = r.core.label := by
  have he := PPLLVerify.eliminateSig_labels_eq hpsi
    (normalizeDeletion l).core (normalizeDeletion r).core
  unfold doneMetadataAuthorizedEntryWidth
  dsimp only
  rw [hr]
  change
    (eliminateSig hpsi (normalizeDeletion l).core
      (normalizeDeletion r).core).1.label = l.core.label ∧
    (eliminateSig hpsi (normalizeDeletion l).core
      (normalizeDeletion r).core).2.label = r.core.label
  exact ⟨he.1.trans (normalizeDeletion_label_local l),
    he.2.trans (normalizeDeletion_label_local r)⟩

private theorem initiatorWait_authorized_labels
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (l r : AuthorizedAgentState psi)
    (hr : deletionActive (normalizeDeletion r) = false)
    (hl : deletionActive (normalizeDeletion l) = true) :
    let q := doneMetadataAuthorizedEntryWidth hpsi hwidth hle kappa l r
    q.1.core.label = l.core.label ∧ q.2.core.label = r.core.label := by
  unfold doneMetadataAuthorizedEntryWidth
  dsimp only
  rw [hr, hl]
  exact ⟨normalizeDeletion_label_local l,
    normalizeDeletion_label_local r⟩

/-- Literal responder-deletion branch of the finite host writes no label. -/
theorem host_responder_deletion_label_frame
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (l r : ExpiringAgentState psi kappa tau)
    (hdel : deletionActive
      (normalizeDeletion (prepareExpiringDisposal hpsi r).core.erase) = true) :
    let d := doneMetadataEntryWidth hpsi hwidth hle l r
    d.1.core.core.label = l.core.core.label ∧
      d.2.core.core.label = r.core.core.label := by
  let pl := prepareExpiringDisposal hpsi l
  let pr := prepareExpiringDisposal hpsi r
  let a := doneMetadataAuthorizedEntryWidth
    hpsi hwidth hle kappa pl.core.erase pr.core.erase
  let d := doneMetadataEntryWidth hpsi hwidth hle l r
  have hd := metadataEntry_authorized_label_frame hpsi hwidth hle l r
  change d.1.core.core.label = a.1.core.label ∧
    d.2.core.core.label = a.2.core.label at hd
  have ha := responderDelete_authorized_labels (kappa := kappa)
    hpsi hwidth hle pl.core.erase pr.core.erase hdel
  change a.1.core.label = pl.core.erase.core.label ∧
    a.2.core.label = pr.core.erase.core.label at ha
  exact ⟨hd.1.trans (ha.1.trans (prepared_label_local hpsi l)),
    hd.2.trans (ha.2.trans (prepared_label_local hpsi r))⟩

/-- Literal initiator-wait deletion-priority branch also writes no label. -/
theorem host_initiator_deletion_label_frame
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (l r : ExpiringAgentState psi kappa tau)
    (hr : deletionActive
      (normalizeDeletion (prepareExpiringDisposal hpsi r).core.erase) = false)
    (hl : deletionActive
      (normalizeDeletion (prepareExpiringDisposal hpsi l).core.erase) = true) :
    let d := doneMetadataEntryWidth hpsi hwidth hle l r
    d.1.core.core.label = l.core.core.label ∧
      d.2.core.core.label = r.core.core.label := by
  let pl := prepareExpiringDisposal hpsi l
  let pr := prepareExpiringDisposal hpsi r
  let a := doneMetadataAuthorizedEntryWidth
    hpsi hwidth hle kappa pl.core.erase pr.core.erase
  let d := doneMetadataEntryWidth hpsi hwidth hle l r
  have hd := metadataEntry_authorized_label_frame hpsi hwidth hle l r
  change d.1.core.core.label = a.1.core.label ∧
    d.2.core.core.label = a.2.core.label at hd
  have ha := initiatorWait_authorized_labels (kappa := kappa)
    hpsi hwidth hle pl.core.erase pr.core.erase hr hl
  change a.1.core.label = pl.core.erase.core.label ∧
    a.2.core.label = pr.core.erase.core.label at ha
  exact ⟨hd.1.trans (ha.1.trans (prepared_label_local hpsi l)),
    hd.2.trans (ha.2.trans (prepared_label_local hpsi r))⟩

/-- `normalizeLeader` can change the label only when its input is a leader. -/
theorem normalizeLeader_label_change_only_on_leader
    (hpsi : 0 < psi) (q : ExpiringAgentState psi kappa tau)
    (hne : (normalizeLeader hpsi q).core.core.label ≠ q.core.core.label) :
    q.core.core.leader = true := by
  cases h : q.core.core.leader with
  | true => rfl
  | false =>
      have heq : (normalizeLeader hpsi q).core.core.label =
          q.core.core.label := by
        simp [normalizeLeader, h]
      exact (hne heq).elim

/-- The physical tail after normalization keeps both normalized labels. -/
theorem hostRow_labels_metadata
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (l r : ExpiringAgentState psi kappa tau) :
    let m := BirthShortDoneTerminalHost.metadata hpsi hwidth hle l r
    let q := BirthShortDoneTerminalHost.row hpsi hwidth hle l r
    q.1.core.core.label = m.1.core.core.label ∧
      q.2.core.core.label = m.2.core.core.label := by
  have h := BirthShortDoneTerminalHost.row_metadata_frame
    hpsi hwidth hle l r
  have hl := congrArg
    (fun z : ExpiringAgentState psi kappa tau => z.core.core.label) h.1
  have hr := congrArg
    (fun z : ExpiringAgentState psi kappa tau => z.core.core.label) h.2
  exact ⟨hl, hr⟩

/-- V8 updates no site other than the scheduled pair. -/
theorem stepV8_other
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau)
    (e i : Fin n) (hi : i ≠ e) (hj : i ≠ ring.rightNeighbor e) :
    stepV8 hpsi hwidth hle ring C e i = C i := by
  by_cases hself : ring.rightNeighbor e = e
  · simp [stepV8, hself]
  · simp [stepV8, hself, hi, hj]

/-- A fully disjoint edge keeps exactly the same V7 protection status. -/
theorem stepV8_disjoint_protection_iff
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau)
    (e x : Fin n)
    (hx0 : x ≠ e) (hx1 : x ≠ ring.rightNeighbor e)
    (hr0 : ring.rightNeighbor x ≠ e)
    (hr1 : ring.rightNeighbor x ≠ ring.rightNeighbor e) :
    ProtectedSpliceEdgeV7 ring (stepV8 hpsi hwidth hle ring C e) x ↔
      ProtectedSpliceEdgeV7 ring C x := by
  have hL := stepV8_other hpsi hwidth hle ring C e x hx0 hx1
  have hR := stepV8_other hpsi hwidth hle ring C e
    (ring.rightNeighbor x) hr0 hr1
  unfold ProtectedSpliceEdgeV7 R1ProtectedSpliceEdgeV3 projectV6
  dsimp only
  rw [hL, hR]

private def physicalV8
    (u : R1AgentStateV6 psi kappa tau) : ExpiringAgentState psi kappa tau :=
  u.carrier.splice.base

private def physicalLabelV8
    (u : R1AgentStateV6 psi kappa tau) : Fin psi :=
  (physicalV8 u).core.core.label

/-- Lift the compiled ordinary-host label theorem through the V7 ticket wrapper. -/
theorem ordinaryHostWriteV7_labels_of_no_birth
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (l r : R1AgentStateV6 psi kappa tau)
    (hl : (physicalV8 l).core.core.leader = false)
    (hr : (physicalV8 r).core.core.leader = false)
    (hopen : PreparedOrdinaryOpen hpsi (physicalV8 l) (physicalV8 r))
    (hb : BirthShortDoneTerminalObserver.birthEvent
      hpsi hwidth hle (physicalV8 l) (physicalV8 r) = false) :
    let q := ordinaryHostWriteV7 hpsi hwidth hle l r
    physicalLabelV8 q.1 = physicalLabelV8 l ∧
      physicalLabelV8 q.2 =
        ⟨((physicalLabelV8 l).val + 1) % psi, Nat.mod_lt _ hpsi⟩ := by
  have h := ordinary_row_labels_of_no_birth
    hpsi hwidth hle (physicalV8 l) (physicalV8 r) hl hr hopen hb
  unfold ordinaryHostWriteV7
  dsimp only
  split <;>
    simpa [ordinaryRow, setPhysical, withCarrierClearTicketV6,
      setTicketV6, physicalV8, physicalLabelV8] using h

/-- Incoming-edge frame: its other endpoint is untouched; only `e` sees the
scheduled row's left output. -/
theorem stepV8_incoming_edge_frame
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau)
    (e p : Fin n) (hne : ring.rightNeighbor e ≠ e)
    (_hin : ring.rightNeighbor p = e)
    (hp0 : p ≠ e) (hp1 : p ≠ ring.rightNeighbor e) :
    let D := stepV8 hpsi hwidth hle ring C e
    D p = C p ∧
      D e = (rowV8 hpsi hwidth hle
        (C e) (C (ring.rightNeighbor e))).1 := by
  let D := stepV8 hpsi hwidth hle ring C e
  have hp := stepV8_other hpsi hwidth hle ring C e p hp0 hp1
  change D p = C p at hp
  have he : D e = (rowV8 hpsi hwidth hle
      (C e) (C (ring.rightNeighbor e))).1 := by
    simp [D, stepV8, hne]
  exact ⟨hp, he⟩

/-- On the non-guard ordinary fallback with no birth, even the serviced left
label is unchanged. Thus the incoming edge's two physical labels are framed. -/
theorem stepV8_incoming_edge_no_birth_label_frame
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau)
    (e p : Fin n) (hne : ring.rightNeighbor e ≠ e)
    (hin : ring.rightNeighbor p = e)
    (hp0 : p ≠ e) (hp1 : p ≠ ring.rightNeighbor e)
    (hordinary : rowV8 hpsi hwidth hle
      (C e) (C (ring.rightNeighbor e)) =
        ordinaryHostWriteV7 hpsi hwidth hle
          (C e) (C (ring.rightNeighbor e)))
    (hl : (physicalV8 (C e)).core.core.leader = false)
    (hr : (physicalV8 (C (ring.rightNeighbor e))).core.core.leader = false)
    (hopen : PreparedOrdinaryOpen hpsi
      (physicalV8 (C e)) (physicalV8 (C (ring.rightNeighbor e))))
    (hb : BirthShortDoneTerminalObserver.birthEvent hpsi hwidth hle
      (physicalV8 (C e)) (physicalV8 (C (ring.rightNeighbor e))) = false) :
    let D := stepV8 hpsi hwidth hle ring C e
    physicalLabelV8 (D p) = physicalLabelV8 (C p) ∧
      physicalLabelV8 (D e) = physicalLabelV8 (C e) := by
  let D := stepV8 hpsi hwidth hle ring C e
  have hf := stepV8_incoming_edge_frame
    hpsi hwidth hle ring C e p hne hin hp0 hp1
  change D p = C p ∧ D e =
    (rowV8 hpsi hwidth hle (C e) (C (ring.rightNeighbor e))).1 at hf
  have ho := ordinaryHostWriteV7_labels_of_no_birth
    hpsi hwidth hle (C e) (C (ring.rightNeighbor e)) hl hr hopen hb
  constructor
  · exact congrArg physicalLabelV8 hf.1
  · have he := congrArg physicalLabelV8 hf.2
    rw [hordinary] at he
    exact he.trans ho.1

end B9SpliceV8LabelFrame

#print axioms B9SpliceV8LabelFrame.deletionPriorityExpireOne_label_frame
#print axioms B9SpliceV8LabelFrame.host_responder_deletion_label_frame
#print axioms B9SpliceV8LabelFrame.host_initiator_deletion_label_frame
#print axioms B9SpliceV8LabelFrame.normalizeLeader_label_change_only_on_leader
#print axioms B9SpliceV8LabelFrame.hostRow_labels_metadata
#print axioms B9SpliceV8LabelFrame.stepV8_disjoint_protection_iff
#print axioms B9SpliceV8LabelFrame.ordinaryHostWriteV7_labels_of_no_birth
#print axioms B9SpliceV8LabelFrame.stepV8_incoming_edge_no_birth_label_frame
