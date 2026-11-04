import Leader.Wu.Birth.ShortDoneTerminalCapClock

namespace BirthShortDoneTerminalCapGeneralR5

open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
  PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
  PPLLLeaderCreationCleanupRepair PPLLWallSweepRepair
  PPLLWallSweepPreCheckResetRepair PPLLTerminalEqualSupportRepair
open BirthGenerationControlRepair BirthGenerationDone
  BirthWaitPassive BirthShortWait BirthShortWaitTerminalEntryRepair
open BirthShortDoneTerminalPassiveR1 BirthShortDoneTerminalEntryCut
  BirthShortDoneCuts BirthSigMoveDisposalRepair
open K2BirthDispatcher ExpiringK2Projection K2BirthLeaderNormalize

set_option autoImplicit false
set_option Elab.async false
set_option pp.structureInstances false

private theorem h2 : 0 < 2 := by decide
private theorem hle2 : 2 <= 2 := by decide

/-! ## The cap row really takes the ordinary metadata branch -/

/-- Once the ruler has reset the authorization bit to false, reconciliation
    stays false even when cap GEN creates a nonempty path. -/
private theorem permit_false (u : AgentState 2) :
    normalizePermit u false = false := by
  cases h : u.path with
  | bot => simp [normalizePermit, h]
  | some j b =>
      cases j <;> simp [normalizePermit, h]

private theorem reconcile_false (old out : AgentState 2) :
    reconcilePermit ⟨old, false⟩ out = false := by
  unfold reconcilePermit
  split
  · exact permit_false out
  · rfl

/-- No pre-cap hypothesis is used here.  `waitWidthEntry2_metadata` says the
    actual repaired WAIT output is still literally the two corresponding
    metadata cells, even on the cap branch.  Thus the remainder of the real
    GEN/CLEAN/ELIMINATE prefix is exactly the R2 post-WAIT prefix. -/
private theorem generation_cap_factor
    (kappa : Nat) (a b : Registers 2) (pa pb : Bool)
    (hab : b.label =
      ⟨(a.label.val + 1) % 2, Nat.mod_lt _ h2⟩) :
    let w := waitWidthEntry h2 h2 hle2 kappa (cell a) (cell b)
    generationBeforeMoveEntryWidth h2 h2 hle2 kappa
      ⟨cell a, pa⟩ ⟨cell b, pb⟩ =
      let g := genCleanAfterWait h2
        (cell (registers w.1)) (cell (registers w.2))
      let q1 := authorizedCleanSig h2 ⟨g.1, false⟩ ⟨g.2, false⟩
      authorizedEliminateSig h2 q1.1 q1.2 := by
  let w := waitWidthEntry h2 h2 hle2 kappa (cell a) (cell b)
  have hm := waitWidthEntry2_metadata h2 hle2 kappa a b
  change w.1 = cell (registers w.1) /\
    w.2 = cell (registers w.2) at hm
  have hg :
      genCleanEntryWidth h2 h2 hle2 kappa (cell a) (cell b) =
        genCleanAfterWait h2
          (cell (registers w.1)) (cell (registers w.2)) := by
    unfold genCleanEntryWidth
    change genCleanAfterWait h2 w.1 w.2 = _
    exact (congrArg (fun x => genCleanAfterWait h2 x w.2) hm.1).trans
      (congrArg (genCleanAfterWait h2 (cell (registers w.1))) hm.2)
  unfold generationBeforeMoveEntryWidth
  rw [wall_cell h2 a b pa pb hab]
  simp only [authorizedGenCleanEntryWidth, authorizedReconcile, hg,
    reconcile_false]
  rfl

/-- Exact ordinary Host factorization through DONE movement, sanitize, CHECK,
    post-CHECK metadata, and the real `authBirth`/`markLeaderBirth`. -/
private theorem ordinary_cap_factor
    (kappa : Nat) (a b : Registers 2) (pa pb : Bool)
    (hab : b.label =
      ⟨(a.label.val + 1) % 2, Nat.mod_lt _ h2⟩) :
    let w := waitWidthEntry h2 h2 hle2 kappa (cell a) (cell b)
    BirthShortDoneTerminalHost.doneOrdinaryMetadataEntryWidth
        h2 h2 hle2 kappa ⟨cell a, pa⟩ ⟨cell b, pb⟩ =
      BirthShortDoneTerminalCapGeneralR2.postWaitDone2
        a b (registers w.1) (registers w.2) pa pb := by
  unfold BirthShortDoneTerminalHost.doneOrdinaryMetadataEntryWidth
    doneThroughCheckEntryWidth doneBeforeCheckEntryWidth
    BirthShortDoneTerminalCapGeneralR2.postWaitDone2
  rw [generation_cap_factor kappa a b pa pb hab]

/-- Cell inputs cannot enter either deletion-priority branch, irrespective of
    their incoming authorization bits. -/
private theorem authorized_cap_factor
    (kappa : Nat) (a b : Registers 2) (pa pb : Bool)
    (hab : b.label =
      ⟨(a.label.val + 1) % 2, Nat.mod_lt _ h2⟩) :
    let w := waitWidthEntry h2 h2 hle2 kappa (cell a) (cell b)
    BirthShortDoneTerminalHost.doneMetadataAuthorizedEntryWidth
        h2 h2 hle2 kappa ⟨cell a, pa⟩ ⟨cell b, pb⟩ =
      BirthShortDoneTerminalCapGeneralR2.postWaitDone2
        a b (registers w.1) (registers w.2) pa pb := by
  unfold BirthShortDoneTerminalHost.doneMetadataAuthorizedEntryWidth
  dsimp only
  simp only [normalize_cell, active_cell, Bool.false_eq_true, if_false]
  exact ordinary_cap_factor kappa a b pa pb hab

/-! ## R4 -> bounded reification -> arbitrary expiry -/

/-- Reify the public R4 result on the exact bounded Host input.  This is still
    before expiry, but no assumption is made on either finite stall timer. -/
private theorem bounded_cap_frame
    (kappa : Nat)
    (l r : AuthorizedBoundedAgentState 2 kappa)
    (a b : Registers 2) (pa pb : Bool)
    (hl : l.erase = ⟨cell a, pa⟩)
    (hr : r.erase = ⟨cell b, pb⟩)
    (hab : b.label =
      ⟨(a.label.val + 1) % 2, Nat.mod_lt _ h2⟩)
    (hcap : BirthShortDoneTerminalCapGeneralR2.AtCapEntry2
      kappa (cell a) (cell b)) :
    let q := BirthShortDoneTerminalHost.doneMetadataBoundedEntryWidth
      h2 h2 hle2 l r
    q.1.core.erase.label = 0 /\
      q.2.core.erase.label = 1 /\
      q.2.core.erase.count = kappa /\
      q.1.core.erase.wait = true /\
      q.2.core.erase.wait = true := by
  let w := waitWidthEntry h2 h2 hle2 kappa (cell a) (cell b)
  let d := registers w.1
  let e := registers w.2

  have hw :=
    BirthShortDoneTerminalCapGeneralR2.waitWidthEntry2_of_atCap
      kappa (cell a) (cell b) (by simpa [cell] using hab) hcap
  change w.1.label = 0 /\ w.2.label = 1 /\
    w.1.wait = false /\ w.2.wait = true /\
    w.2.count = kappa at hw

  have hd : d.label = 0 := by
    change w.1.label = 0
    exact hw.1
  have he : e.label = 1 := by
    change w.2.label = 1
    exact hw.2.1
  have hwd : d.wait = false := by
    change w.1.wait = false
    exact hw.2.2.1
  have hwe : e.wait = true := by
    change w.2.wait = true
    exact hw.2.2.2.1
  have heCount : e.count = kappa := by
    change w.2.count = kappa
    exact hw.2.2.2.2

  have hpost :=
    BirthShortDoneTerminalCapGeneralR4.postWaitDone2_cap_clock_frame
      a b d e pa pb hd he hwd hwe
  change
    (BirthShortDoneTerminalCapGeneralR2.postWaitDone2
      a b d e pa pb).1.core.label = 0 /\
    (BirthShortDoneTerminalCapGeneralR2.postWaitDone2
      a b d e pa pb).2.core.label = 1 /\
    (BirthShortDoneTerminalCapGeneralR2.postWaitDone2
      a b d e pa pb).2.core.count = e.count /\
    (BirthShortDoneTerminalCapGeneralR2.postWaitDone2
      a b d e pa pb).1.core.wait = true /\
    (BirthShortDoneTerminalCapGeneralR2.postWaitDone2
      a b d e pa pb).2.core.wait = true at hpost

  let q := BirthShortDoneTerminalHost.doneMetadataBoundedEntryWidth
    h2 h2 hle2 l r
  have hb := BirthShortDoneTerminalHost.doneMetadataBoundedEntryWidth_erase
    h2 h2 hle2 l r
  change
    (q.1.erase, q.2.erase) =
      BirthShortDoneTerminalHost.doneMetadataAuthorizedEntryWidth
        h2 h2 hle2 kappa l.erase r.erase at hb

  have hfactor := authorized_cap_factor kappa a b pa pb hab
  change
    BirthShortDoneTerminalHost.doneMetadataAuthorizedEntryWidth
        h2 h2 hle2 kappa ⟨cell a, pa⟩ ⟨cell b, pb⟩ =
      BirthShortDoneTerminalCapGeneralR2.postWaitDone2
        a b d e pa pb at hfactor

  have hpair :
      (q.1.erase, q.2.erase) =
        BirthShortDoneTerminalCapGeneralR2.postWaitDone2
          a b d e pa pb := by
    calc
      (q.1.erase, q.2.erase) =
          BirthShortDoneTerminalHost.doneMetadataAuthorizedEntryWidth
            h2 h2 hle2 kappa l.erase r.erase := hb
      _ = BirthShortDoneTerminalHost.doneMetadataAuthorizedEntryWidth
            h2 h2 hle2 kappa ⟨cell a, pa⟩ ⟨cell b, pb⟩ := by
          rw [hl, hr]
      _ = BirthShortDoneTerminalCapGeneralR2.postWaitDone2
            a b d e pa pb := hfactor

  rw [← hpair] at hpost
  change
    q.1.core.erase.label = 0 /\
      q.2.core.erase.label = 1 /\
      q.2.core.erase.count = e.count /\
      q.1.core.erase.wait = true /\
      q.2.core.erase.wait = true at hpost
  exact ⟨hpost.1,
    hpost.2.1,
    hpost.2.2.1.trans heCount,
    hpost.2.2.2.1,
    hpost.2.2.2.2⟩

/-! ## Normalization and the unique final physical tail -/

private theorem normalizeLeader_clock_tail
    {kappa tau : Nat} (u : ExpiringAgentState 2 kappa tau) :
    (raw (normalizeLeader h2 u)).count = (raw u).count /\
      (raw (normalizeLeader h2 u)).wait = (raw u).wait := by
  unfold normalizeLeader
  split <;> exact ⟨rfl, rfl⟩

private theorem normalizeLeader_label_of_zero
    {kappa tau : Nat} (u : ExpiringAgentState 2 kappa tau)
    (hu : (raw u).label = 0) :
    (raw (normalizeLeader h2 u)).label = 0 := by
  unfold normalizeLeader
  split
  · rfl
  · exact hu

/-- For a literal responder cell, computed leadership is exactly the physical
    newborn event used by `finalPhysical`.  The leader branch is normalized to
    label zero; the follower branch retains the R4 label one. -/
private theorem normalizeLeader_right_birth_split
    {kappa tau : Nat}
    (old u : ExpiringAgentState 2 kappa tau)
    (hold : (raw old).leader = false)
    (hu : (raw u).label = 1) :
    let m := normalizeLeader h2 u
    (newborn old m = true /\ (raw m).label = 0) \/
      (newborn old m = false /\ (raw m).label = 1) := by
  let m := normalizeLeader h2 u
  change
    (newborn old m = true /\ (raw m).label = 0) \/
      (newborn old m = false /\ (raw m).label = 1)
  have holdCore : old.core.core.leader = false := by
    change old.core.core.leader = false at hold
    exact hold
  cases hlead : u.core.core.leader with
  | false =>
      have hm : m = u := by
        unfold m normalizeLeader
        simp [hlead]
      apply Or.inr
      constructor
      · rw [hm]
        simp [newborn, holdCore, hlead]
      · rw [hm]
        exact hu
  | true =>
      have hmLead : m.core.core.leader = true := by
        unfold m
        exact (normalizeLeader_leader h2 u).trans hlead
      apply Or.inl
      constructor
      · simp [newborn, holdCore, hmLead]
      · change (raw m).label = 0
        unfold m
        change (normalizeLeader h2 u).core.core.label = 0
        exact normalizeLeader_label_zero h2 u
          ((normalizeLeader_leader h2 u).trans hlead)

/-- `nonK2` changes only the four signal fields, none of which is observed by
    the WAIT clock. -/
private theorem nonK2_clock
    {kappa tau : Nat} (u : ExpiringAgentState 2 kappa tau) :
    clock (raw (nonK2 u)) = clock (raw u) := by
  rfl

/-- The unique final physical stage preserves the complete WAIT clock of the
    normalized metadata, in both collision and ordinary K2 branches and for a
    real newborn initialization. -/
private theorem finalPhysical_clock
    {kappa tau : Nat}
    (oldL oldR metaL metaR : ExpiringAgentState 2 kappa tau) :
    let q := finalPhysical h2 oldL oldR metaL metaR
    clock (raw q.1) = clock (raw metaL) /\
      clock (raw q.2) = clock (raw metaR) := by
  let q := finalPhysical h2 oldL oldR metaL metaR
  have h := finalPhysical_nonK2 h2 oldL oldR metaL metaR
  change nonK2 q.1 = nonK2 metaL /\
    nonK2 q.2 = nonK2 metaR at h
  have hL := congrArg
    (fun u : ExpiringAgentState 2 kappa tau => clock (raw u)) h.1
  have hR := congrArg
    (fun u : ExpiringAgentState 2 kappa tau => clock (raw u)) h.2
  exact ⟨(nonK2_clock q.1).symm.trans
      (hL.trans (nonK2_clock metaL)),
    (nonK2_clock q.2).symm.trans
      (hR.trans (nonK2_clock metaR))⟩

/-- Full actual finite/expiry/normalization/finalPhysical width-two cap
    endpoint.  No timer positivity, no no-expiry condition and no no-birth
    condition are assumed.

    The first conjunct pins the statement to the literal current Host row.
    The next five conjuncts expose the post-expiry cap frame.  Count and WAIT
    then survive normalization and the unique physical tail.  Finally, the
    responder label records the exact newborn split: a real computed birth is
    normalized to zero; otherwise the cap label one is retained. -/
theorem full_terminal_row2_cap
    (kappa tau : Nat)
    (l r : ExpiringAgentState 2 kappa tau)
    (a b : Registers 2)
    (hl : raw l = cell a) (hr : raw r = cell b)
    (hab : b.label =
      ⟨(a.label.val + 1) % 2, Nat.mod_lt _ h2⟩)
    (hcap : BirthShortDoneTerminalCapGeneralR2.AtCapEntry2
      kappa (cell a) (cell b)) :
    let l0 := prepareExpiringDisposal h2 l
    let r0 := prepareExpiringDisposal h2 r
    let q0 := BirthShortDoneTerminalHost.doneMetadataBoundedEntryWidth
      h2 h2 hle2 l0.core r0.core
    let eL := deletionPriorityExpireOne tau l0 ⟨q0.1, l0.stall⟩
    let eR := deletionPriorityExpireOne tau r0 ⟨q0.2, r0.stall⟩
    let mL := normalizeLeader h2 eL
    let mR := normalizeLeader h2 eR
    let out := BirthShortDoneTerminalHost.row h2 h2 hle2 l r
    out = finalPhysical h2 l r mL mR /\
      (raw eL).label = 0 /\
      (raw eR).label = 1 /\
      (raw eR).count = kappa /\
      (raw eL).wait = true /\
      (raw eR).wait = true /\
      (raw out.2).count = kappa /\
      (raw out.1).wait = true /\
      (raw out.2).wait = true /\
      (raw out.1).label = 0 /\
      ((newborn r mR = true /\ (raw out.2).label = 0) \/
        (newborn r mR = false /\ (raw out.2).label = 1)) := by
  let l0 := prepareExpiringDisposal h2 l
  let r0 := prepareExpiringDisposal h2 r
  let q0 := BirthShortDoneTerminalHost.doneMetadataBoundedEntryWidth
    h2 h2 hle2 l0.core r0.core
  let oL : ExpiringAgentState 2 kappa tau := ⟨q0.1, l0.stall⟩
  let oR : ExpiringAgentState 2 kappa tau := ⟨q0.2, r0.stall⟩
  let eL := deletionPriorityExpireOne tau l0 oL
  let eR := deletionPriorityExpireOne tau r0 oR
  let mL := normalizeLeader h2 eL
  let mR := normalizeLeader h2 eR
  let out := BirthShortDoneTerminalHost.row h2 h2 hle2 l r

  change
    out = finalPhysical h2 l r mL mR /\
      (raw eL).label = 0 /\
      (raw eR).label = 1 /\
      (raw eR).count = kappa /\
      (raw eL).wait = true /\
      (raw eR).wait = true /\
      (raw out.2).count = kappa /\
      (raw out.1).wait = true /\
      (raw out.2).wait = true /\
      (raw out.1).label = 0 /\
      ((newborn r mR = true /\ (raw out.2).label = 0) \/
        (newborn r mR = false /\ (raw out.2).label = 1))

  have hl0 := prepared_erasure h2 l a hl
  have hr0 := prepared_erasure h2 r b hr
  change l0.core.erase = ⟨cell a, l.core.path0Crossed⟩ at hl0
  change r0.core.erase = ⟨cell b, r.core.path0Crossed⟩ at hr0

  have hbnd := bounded_cap_frame kappa l0.core r0.core a b
    l.core.path0Crossed r.core.path0Crossed
    hl0 hr0 hab hcap
  change
    q0.1.core.erase.label = 0 /\
      q0.2.core.erase.label = 1 /\
      q0.2.core.erase.count = kappa /\
      q0.1.core.erase.wait = true /\
      q0.2.core.erase.wait = true at hbnd

  have hexL := expiry_clock l0 oL
  have hexR := expiry_clock r0 oR
  change clock (raw eL) = clock (raw oL) at hexL
  change clock (raw eR) = clock (raw oR) at hexR

  have heLL := congrArg (fun c : Clock 2 => c.label) hexL
  have heLW := congrArg (fun c : Clock 2 => c.wait) hexL
  have heRL := congrArg (fun c : Clock 2 => c.label) hexR
  have heRC := congrArg (fun c : Clock 2 => c.count) hexR
  have heRW := congrArg (fun c : Clock 2 => c.wait) hexR
  change (raw eL).label = q0.1.core.erase.label at heLL
  change (raw eL).wait = q0.1.core.erase.wait at heLW
  change (raw eR).label = q0.2.core.erase.label at heRL
  change (raw eR).count = q0.2.core.erase.count at heRC
  change (raw eR).wait = q0.2.core.erase.wait at heRW

  have hELL : (raw eL).label = 0 := heLL.trans hbnd.1
  have hERL : (raw eR).label = 1 := heRL.trans hbnd.2.1
  have hERC : (raw eR).count = kappa := heRC.trans hbnd.2.2.1
  have hELW : (raw eL).wait = true := heLW.trans hbnd.2.2.2.1
  have hERW : (raw eR).wait = true := heRW.trans hbnd.2.2.2.2

  have hnL := normalizeLeader_clock_tail eL
  have hnR := normalizeLeader_clock_tail eR
  change (raw mL).count = (raw eL).count /\
    (raw mL).wait = (raw eL).wait at hnL
  change (raw mR).count = (raw eR).count /\
    (raw mR).wait = (raw eR).wait at hnR

  have hmLL := normalizeLeader_label_of_zero eL hELL
  change (raw mL).label = 0 at hmLL

  have hrFollower : (raw r).leader = false := by
    rw [hr]
    rfl
  have hbirth := normalizeLeader_right_birth_split r eR hrFollower hERL
  change
    (newborn r mR = true /\ (raw mR).label = 0) \/
      (newborn r mR = false /\ (raw mR).label = 1) at hbirth

  have hrow := BirthShortDoneTerminalHost.row_real_host_witness
    h2 h2 hle2 l r
  change out = finalPhysical h2 l r mL mR at hrow

  have hf := finalPhysical_clock l r mL mR
  change
    clock (raw (finalPhysical h2 l r mL mR).1) = clock (raw mL) /\
      clock (raw (finalPhysical h2 l r mL mR).2) = clock (raw mR) at hf
  rw [← hrow] at hf
  change clock (raw out.1) = clock (raw mL) /\
    clock (raw out.2) = clock (raw mR) at hf

  have hfLL := congrArg (fun c : Clock 2 => c.label) hf.1
  have hfLW := congrArg (fun c : Clock 2 => c.wait) hf.1
  have hfRL := congrArg (fun c : Clock 2 => c.label) hf.2
  have hfRC := congrArg (fun c : Clock 2 => c.count) hf.2
  have hfRW := congrArg (fun c : Clock 2 => c.wait) hf.2
  change (raw out.1).label = (raw mL).label at hfLL
  change (raw out.1).wait = (raw mL).wait at hfLW
  change (raw out.2).label = (raw mR).label at hfRL
  change (raw out.2).count = (raw mR).count at hfRC
  change (raw out.2).wait = (raw mR).wait at hfRW

  have houtRC : (raw out.2).count = kappa :=
    hfRC.trans (hnR.1.trans hERC)
  have houtLW : (raw out.1).wait = true :=
    hfLW.trans (hnL.2.trans hELW)
  have houtRW : (raw out.2).wait = true :=
    hfRW.trans (hnR.2.trans hERW)
  have houtLL : (raw out.1).label = 0 :=
    hfLL.trans hmLL

  have hbirthOut :
      (newborn r mR = true /\ (raw out.2).label = 0) \/
        (newborn r mR = false /\ (raw out.2).label = 1) := by
    rcases hbirth with hb | hb
    · exact Or.inl ⟨hb.1, hfRL.trans hb.2⟩
    · exact Or.inr ⟨hb.1, hfRL.trans hb.2⟩

  exact ⟨hrow,
    hELL, hERL, hERC, hELW, hERW,
    houtRC, houtLW, houtRW, houtLL, hbirthOut⟩

#print axioms BirthShortDoneTerminalCapGeneralR5.full_terminal_row2_cap

end BirthShortDoneTerminalCapGeneralR5
