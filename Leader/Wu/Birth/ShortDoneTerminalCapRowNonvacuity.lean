import Leader.Wu.Birth.ShortDoneTerminalCapRow
import Leader.Wu.Birth.ShortDoneTerminalPassiveLocalTripleRotationWitness


namespace BirthShortDoneTerminalCapGeneralR5Nonvacuity


open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
  PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
  PPLLLeaderCreationCleanupRepair
open BirthWaitPassive BirthShortWait BirthShortWaitTerminalEntryRepair
  BirthShortDoneTerminalPassiveR1
open BirthSigMoveDisposalRepair
open K2BirthDispatcher ExpiringK2Projection K2BirthLeaderNormalize


set_option autoImplicit false
set_option Elab.async false
set_option pp.structureInstances false


private theorem h2 : 0 < 2 := by decide
private theorem hle2 : 2 <= 2 := by decide


/-- Finite nonvacuity of the candidate R5 endpoint on the accepted rotated
    n=5, psi=2, kappa=1, tau=0 fixture.  The physical edge is the exported
    wrap edge 4 -> 0.  The responder starts at count zero; the accepted cap
    computation raises the pre-Finish count to one; then R5 is consumed on
    those exact cell-shaped endpoints.


    The last disjunction is intentionally a newborn-metadata statement, not a
    physical-leader statement. -/
theorem n5_psi2_kappa1_tau0_rotation_cap_r5_nonvacuous :
    let l : ExpiringAgentState 2 1 0 :=
      BirthShortDoneTerminalPassiveLocal3RotationAudit.auditSource
        BirthShortDoneTerminalPassiveLocal3RotationAudit.auditAnchor4
    let r : ExpiringAgentState 2 1 0 :=
      BirthShortDoneTerminalPassiveLocal3RotationAudit.auditSource
        (BirthShortDoneTerminalPassiveLocal3RotationAudit.auditRing5.rightNeighbor
          BirthShortDoneTerminalPassiveLocal3RotationAudit.auditAnchor4)
    let a : Registers 2 := registers (raw l)
    let b : Registers 2 := registers (raw r)
    let l0 := prepareExpiringDisposal h2 l
    let r0 := prepareExpiringDisposal h2 r
    let q0 := BirthShortDoneTerminalHost.doneMetadataBoundedEntryWidth
      h2 h2 hle2 l0.core r0.core
    let eL := deletionPriorityExpireOne 0 l0 ⟨q0.1, l0.stall⟩
    let eR := deletionPriorityExpireOne 0 r0 ⟨q0.2, r0.stall⟩
    let mL := normalizeLeader h2 eL
    let mR := normalizeLeader h2 eR
    let out := BirthShortDoneTerminalHost.row h2 h2 hle2 l r
    raw l = cell a /\
      raw r = cell b /\
      a.label = 0 /\
      b.label = 1 /\
      b.label = ⟨(a.label.val + 1) % 2, Nat.mod_lt _ h2⟩ /\
      BirthShortDoneTerminalCapGeneralR2.AtCapEntry2 1 (cell a) (cell b) /\
      (raw r).count = 0 /\
      out = finalPhysical h2 l r mL mR /\
      (raw out.2).count = 1 /\
      (raw out.1).wait = true /\
      (raw out.2).wait = true /\
      (raw out.1).label = 0 /\
      ((newborn r mR = true /\ (raw out.2).label = 0) \/
        (newborn r mR = false /\ (raw out.2).label = 1)) := by
  let l : ExpiringAgentState 2 1 0 :=
    BirthShortDoneTerminalPassiveLocal3RotationAudit.auditSource
      BirthShortDoneTerminalPassiveLocal3RotationAudit.auditAnchor4
  let r : ExpiringAgentState 2 1 0 :=
    BirthShortDoneTerminalPassiveLocal3RotationAudit.auditSource
      (BirthShortDoneTerminalPassiveLocal3RotationAudit.auditRing5.rightNeighbor
        BirthShortDoneTerminalPassiveLocal3RotationAudit.auditAnchor4)
  let a : Registers 2 := registers (raw l)
  let b : Registers 2 := registers (raw r)
  let l0 := prepareExpiringDisposal h2 l
  let r0 := prepareExpiringDisposal h2 r
  let q0 := BirthShortDoneTerminalHost.doneMetadataBoundedEntryWidth
    h2 h2 hle2 l0.core r0.core
  let eL := deletionPriorityExpireOne 0 l0 ⟨q0.1, l0.stall⟩
  let eR := deletionPriorityExpireOne 0 r0 ⟨q0.2, r0.stall⟩
  let mL := normalizeLeader h2 eL
  let mR := normalizeLeader h2 eR
  let out := BirthShortDoneTerminalHost.row h2 h2 hle2 l r


  change
    raw l = cell a /\
      raw r = cell b /\
      a.label = 0 /\
      b.label = 1 /\
      b.label = ⟨(a.label.val + 1) % 2, Nat.mod_lt _ h2⟩ /\
      BirthShortDoneTerminalCapGeneralR2.AtCapEntry2 1 (cell a) (cell b) /\
      (raw r).count = 0 /\
      out = finalPhysical h2 l r mL mR /\
      (raw out.2).count = 1 /\
      (raw out.1).wait = true /\
      (raw out.2).wait = true /\
      (raw out.1).label = 0 /\
      ((newborn r mR = true /\ (raw out.2).label = 0) \/
        (newborn r mR = false /\ (raw out.2).label = 1))


  have hline :=
    BirthShortDoneTerminalPassiveLocal3RotationAudit.source_localLine3At


  have hlMeta : Metadata (raw l) := by
    simpa only [l] using hline.pass0.1
  have hrMeta : Metadata (raw r) := by
    simpa only [r] using hline.pass1.1


  have hl : raw l = cell a := by
    change Metadata (raw l)
    exact hlMeta
  have hr : raw r = cell b := by
    change Metadata (raw r)
    exact hrMeta


  have ha0 : a.label = 0 := by
    apply Fin.ext
    change (raw l).label.val = 0
    simpa only [l] using hline.lab0


  have hb1 : b.label = 1 := by
    apply Fin.ext
    change (raw r).label.val = 1
    simpa only [r] using hline.lab1


  have hab :
      b.label = ⟨(a.label.val + 1) % 2, Nat.mod_lt _ h2⟩ := by
    apply Fin.ext
    simp [ha0, hb1]


  have hrowcap :=
    BirthShortDoneTerminalPassiveLocal3RotationAudit.positive_cap_on_physical_wrap
  have hcap :
      BirthShortDoneTerminalCapGeneralR2.AtCapEntry2
        1 (cell a) (cell b) := by
    unfold BirthShortDoneTerminalCapGeneralR2.AtCapEntry2
    rw [← hl, ← hr]
    unfold BirthShortDoneTerminalPassiveR4.RowCap2 at hrowcap
    simpa only [l, r] using hrowcap


  have hzero : (raw r).count = 0 := by
    simpa only [r] using
      BirthShortDoneTerminalPassiveLocal3RotationAudit.cap_responder_count_zero


  have hfull :=
    BirthShortDoneTerminalCapGeneralR5.full_terminal_row2_cap
      1 0 l r a b hl hr hab hcap
  change
    out = finalPhysical h2 l r mL mR /\
      (raw eL).label = 0 /\
      (raw eR).label = 1 /\
      (raw eR).count = 1 /\
      (raw eL).wait = true /\
      (raw eR).wait = true /\
      (raw out.2).count = 1 /\
      (raw out.1).wait = true /\
      (raw out.2).wait = true /\
      (raw out.1).label = 0 /\
      ((newborn r mR = true /\ (raw out.2).label = 0) \/
        (newborn r mR = false /\ (raw out.2).label = 1)) at hfull


  rcases hfull with
    ⟨hrow, _hELL, _hERL, _hERC, _hELW, _hERW,
      houtRC, houtLW, houtRW, houtLL, hbirth⟩


  exact ⟨hl, hr, ha0, hb1, hab, hcap, hzero,
    hrow, houtRC, houtLW, houtRW, houtLL, hbirth⟩


#print axioms
  BirthShortDoneTerminalCapGeneralR5Nonvacuity.n5_psi2_kappa1_tau0_rotation_cap_r5_nonvacuous


end BirthShortDoneTerminalCapGeneralR5Nonvacuity
