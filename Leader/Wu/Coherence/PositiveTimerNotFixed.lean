import Leader.Wu.Coherence.SixTokenController

set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096

namespace R2CoherenceOpenPositiveTimerNotFixed

open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
open PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
open PPLLPathStallComparisonRepair PPLLLeaderCreationCleanupRepair
open BirthSigMoveDisposalRepair
open K2BirthDispatcher K2BirthLeaderNormalize ExpiringK2Projection
open WriterProducerRepair

variable {n psi kappa tau width : Nat}

private theorem deletionActive_true_fields_local
    (u : AuthorizedAgentState psi)
    (hactive : deletionActive u = true) :
    u.core.state = .eliminate_signal ∧ u.core.path ≠ .bot := by
  cases hpath : u.core.path with
  | bot => simp [deletionActive, pathPresent, hpath] at hactive
  | some label bit =>
      have hstate : u.core.state = .eliminate_signal := by
        simpa [deletionActive, pathPresent, hpath] using hactive
      exact ⟨hstate, by simp⟩

private theorem normalizeDeletion_path_local
    (u : AuthorizedAgentState psi) :
    (normalizeDeletion u).core.path = u.core.path := by
  unfold normalizeDeletion
  split <;> rfl

private theorem prepareExpiringDisposal_path_local
    (hpsi : 0 < psi) (u : ExpiringAgentState psi kappa tau) :
    (prepareExpiringDisposal hpsi u).core.erase.core.path =
      u.core.erase.core.path := by
  change
    (prepareBoundedDisposal hpsi u.core).erase.core.path =
      u.core.erase.core.path
  exact
    (congrArg (fun a : AuthorizedAgentState psi => a.core.path)
      (erase_prepareBoundedDisposal hpsi u.core)).trans
      (prepareDisposal_path hpsi u.core.erase)

private theorem prepareDisposal_eq_of_path_bot_local
    (hpsi : 0 < psi) (u : AuthorizedAgentState psi)
    (hpath : u.core.path = .bot) :
    prepareDisposal hpsi u = u := by
  unfold prepareDisposal
  split
  · simp [markComparisonForDeletion, hpath]
  · rfl

private theorem prepareBoundedDisposal_eq_of_path_bot_local
    (hpsi : 0 < psi) (u : AuthorizedBoundedAgentState psi kappa)
    (hpath : u.erase.core.path = .bot) :
    prepareBoundedDisposal hpsi u = u := by
  unfold prepareBoundedDisposal
  simp only [prepareDisposal_eq_of_path_bot_local hpsi u.erase hpath]
  cases u with
  | mk core permit =>
      simp only [AuthorizedBoundedAgentState.erase]
      rw [BoundedAgentState.ofDomain_erase]

private theorem prepareExpiringDisposal_eq_or_active
    (hpsi : 0 < psi) (u : ExpiringAgentState psi kappa tau) :
    prepareExpiringDisposal hpsi u = u ∨
      deletionActive
        (normalizeDeletion (prepareExpiringDisposal hpsi u).core.erase) = true := by
  cases hp : pendingTerminalDisposal hpsi u.core.erase.core with
  | false =>
      left
      unfold prepareExpiringDisposal
      rw [prepareBoundedDisposal_eq_of_clear hpsi u.core hp]
  | true =>
      cases hpath : u.core.erase.core.path with
      | bot =>
          left
          unfold prepareExpiringDisposal
          rw [prepareBoundedDisposal_eq_of_path_bot_local hpsi u.core hpath]
      | some label bit =>
          right
          have hpresent0 : u.core.erase.core.path ≠ .bot := by
            rw [hpath]
            simp
          have hstate :
              (prepareExpiringDisposal hpsi u).core.erase.core.state =
                .eliminate_signal := by
            change
              (prepareBoundedDisposal hpsi u.core).erase.core.state =
                .eliminate_signal
            rw [erase_prepareBoundedDisposal]
            exact (prepareDisposal_pending hpsi u.core.erase hp hpresent0).1
          have hpresent :
              (prepareExpiringDisposal hpsi u).core.erase.core.path ≠ .bot := by
            rw [prepareExpiringDisposal_path_local hpsi u]
            exact hpresent0
          have hnorm := normalizeDeletion_eq_of_path_present
            (prepareExpiringDisposal hpsi u).core.erase hpresent
          rw [hnorm]
          exact deletionActive_eq_true
            (prepareExpiringDisposal hpsi u).core.erase hstate hpresent

private theorem birthCheckAuthorized_active_responder_path
    (hpsi : 0 < psi) (hw : 0 < width) (hle : width <= psi)
    (kappa : Nat) (l r : AuthorizedAgentState psi)
    (hr : deletionActive (normalizeDeletion r) = true) :
    (BirthCheckPermitRepair.authorized hpsi hw hle kappa l r).2.core.path =
      .bot := by
  let r0 := normalizeDeletion r
  have hrs := deletionActive_true_fields_local r0 hr
  unfold BirthCheckPermitRepair.authorized
  dsimp only
  rw [if_pos hr]
  unfold authorizedEliminateSig authorizedReconcile eliminateSig
  dsimp only
  rw [if_pos hrs.1]

private theorem birthCheckBounded_active_responder_path
    (hpsi : 0 < psi) (hw : 0 < width) (hle : width <= psi)
    (l r : AuthorizedBoundedAgentState psi kappa)
    (hr : deletionActive (normalizeDeletion r.erase) = true) :
    (BirthCheckPermitRepair.bounded hpsi hw hle l r).2.erase.core.path =
      .bot := by
  have ha := birthCheckAuthorized_active_responder_path
    hpsi hw hle kappa l.erase r.erase hr
  unfold BirthCheckPermitRepair.bounded
  dsimp only
  simpa only [AuthorizedBoundedAgentState.erase,
    BoundedAgentState.erase_ofDomain] using ha

private theorem tick_erase_path_local (u : WCell psi kappa) :
    (tick u).agent.erase.core.path = u.agent.erase.core.path := by
  unfold WriterProducerRepair.tick WriterProducerRepair.put
  dsimp only
  repeat (first | rfl | (split <;> try dsimp only))

private theorem r2Bounded_active_responder_path
    (hpsi : 0 < psi) (hw : 0 < width) (hle : width <= psi)
    (l r : WCell psi kappa)
    (hr : deletionActive (normalizeDeletion r.agent.erase) = true) :
    (R2.bounded hpsi hw hle l r).2.agent.erase.core.path = .bot := by
  have hb := birthCheckBounded_active_responder_path
    hpsi hw hle l.agent r.agent hr
  have hdel :
      deletionActive (normalizeDeletion r.agent.erase) ||
        deletionActive (normalizeDeletion l.agent.erase) = true := by
    simp [hr]
  have htick :
      (tick
        (⟨(BirthCheckPermitRepair.bounded hpsi hw hle l.agent r.agent).2,
          r.fuel⟩ : WCell psi kappa)).agent.erase.core.path = .bot :=
    (tick_erase_path_local
      (⟨(BirthCheckPermitRepair.bounded hpsi hw hle l.agent r.agent).2,
        r.fuel⟩ : WCell psi kappa)).trans hb
  simpa [R2.bounded, hr, hdel] using htick

private theorem expiry_preserves_absence_local
    (old out : ExpiringAgentState psi kappa tau)
    (h : out.core.erase.core.path = .bot) :
    (deletionPriorityExpireOne tau old out).core.erase.core.path = .bot := by
  unfold deletionPriorityExpireOne pathExpireOne
  split
  · exact h
  · split
    · exact h
    · split
      · rfl
      · exact h

private theorem nonK2_progress_eq
    {a b : ExpiringAgentState psi kappa tau}
    (h : nonK2 a = nonK2 b) :
    PathProgressView.ofState a.core = PathProgressView.ofState b.core := by
  have hp := congrArg
    (fun u : ExpiringAgentState psi kappa tau =>
      PathProgressView.ofState u.core) h
  change PathProgressView.ofState a.core = PathProgressView.ofState b.core at hp
  exact hp

private theorem nonK2_path_eq
    {a b : ExpiringAgentState psi kappa tau}
    (h : nonK2 a = nonK2 b) :
    a.core.erase.core.path = b.core.erase.core.path := by
  have hp := congrArg
    (fun u : ExpiringAgentState psi kappa tau => u.core.erase.core.path) h
  change a.core.erase.core.path = b.core.erase.core.path at hp
  exact hp

private theorem nonK2_state_eq
    {a b : ExpiringAgentState psi kappa tau}
    (h : nonK2 a = nonK2 b) :
    a.core.erase.core.state = b.core.erase.core.state := by
  have hs := congrArg
    (fun u : ExpiringAgentState psi kappa tau => u.core.erase.core.state) h
  change a.core.erase.core.state = b.core.erase.core.state at hs
  exact hs

private theorem nonK2_stall_eq
    {a b : ExpiringAgentState psi kappa tau}
    (h : nonK2 a = nonK2 b) : a.stall = b.stall := by
  have hs := congrArg ExpiringAgentState.stall h
  change a.stall = b.stall at hs
  exact hs

private theorem normalizeLeader_progress
    (hpsi : 0 < psi) (u : ExpiringAgentState psi kappa tau) :
    PathProgressView.ofState (normalizeLeader hpsi u).core =
      PathProgressView.ofState u.core := by
  unfold normalizeLeader
  split <;> rfl

private theorem normalizeLeader_path
    (hpsi : 0 < psi) (u : ExpiringAgentState psi kappa tau) :
    (normalizeLeader hpsi u).core.erase.core.path =
      u.core.erase.core.path := by
  unfold normalizeLeader
  split <;> rfl

private theorem normalizeLeader_state
    (hpsi : 0 < psi) (u : ExpiringAgentState psi kappa tau) :
    (normalizeLeader hpsi u).core.erase.core.state =
      u.core.erase.core.state := by
  unfold normalizeLeader
  split <;> rfl

private theorem normalizeLeader_stall
    (hpsi : 0 < psi) (u : ExpiringAgentState psi kappa tau) :
    (normalizeLeader hpsi u).stall = u.stall := by
  unfold normalizeLeader
  split <;> rfl

private theorem r2_row_right_expiry_frame
    (hpsi : 0 < psi) (hw : 0 < width) (hle : width <= psi)
    (l r : R2.Cell psi kappa tau) :
    let l0 := prepareExpiringDisposal hpsi l.base
    let r0 := prepareExpiringDisposal hpsi r.base
    let q := R2.bounded hpsi hw hle
      ⟨l0.core, l.fuel⟩ ⟨r0.core, r.fuel⟩
    let eR := deletionPriorityExpireOne tau r0
      ⟨q.2.agent, r0.stall⟩
    PathProgressView.ofState (R2.row hpsi hw hle l r).2.base.core =
        PathProgressView.ofState eR.core ∧
      (R2.row hpsi hw hle l r).2.base.core.erase.core.path =
        eR.core.erase.core.path ∧
      (R2.row hpsi hw hle l r).2.base.core.erase.core.state =
        eR.core.erase.core.state ∧
      (R2.row hpsi hw hle l r).2.base.stall = eR.stall := by
  dsimp only
  unfold R2.row
  dsimp only
  generalize prepareExpiringDisposal hpsi l.base = l0
  generalize prepareExpiringDisposal hpsi r.base = r0
  generalize R2.bounded hpsi hw hle
    ⟨l0.core, l.fuel⟩ ⟨r0.core, r.fuel⟩ = q0
  generalize deletionPriorityExpireOne tau l0
    ⟨q0.1.agent, l0.stall⟩ = eL
  generalize deletionPriorityExpireOne tau r0
    ⟨q0.2.agent, r0.stall⟩ = eR
  have hf := finalPhysical_nonK2 hpsi l.base r.base
    (normalizeLeader hpsi eL) (normalizeLeader hpsi eR)
  exact ⟨
    (nonK2_progress_eq hf.2).trans (normalizeLeader_progress hpsi eR),
    (nonK2_path_eq hf.2).trans (normalizeLeader_path hpsi eR),
    (nonK2_state_eq hf.2).trans (normalizeLeader_state hpsi eR),
    (nonK2_stall_eq hf.2).trans (normalizeLeader_stall hpsi eR)⟩

theorem raw_row_not_fixed_of_positive_timer_any
    (hpsi : 0 < psi) (hw : 0 < width) (hle : width <= psi)
    (htau : 0 < tau) (l r : R2.Cell psi kappa tau) :
    R2.row hpsi hw hle l r ≠ (l, r) := by
  intro hfix
  let l0 := prepareExpiringDisposal hpsi l.base
  let r0 := prepareExpiringDisposal hpsi r.base
  let q := R2.bounded hpsi hw hle
    (⟨l0.core, l.fuel⟩ : WCell psi kappa)
    (⟨r0.core, r.fuel⟩ : WCell psi kappa)
  let baseR : ExpiringAgentState psi kappa tau :=
    ⟨q.2.agent, r0.stall⟩
  let eR := deletionPriorityExpireOne tau r0 baseR
  have hframe := r2_row_right_expiry_frame hpsi hw hle l r
  change
    PathProgressView.ofState (R2.row hpsi hw hle l r).2.base.core =
        PathProgressView.ofState eR.core ∧
      (R2.row hpsi hw hle l r).2.base.core.erase.core.path =
        eR.core.erase.core.path ∧
      (R2.row hpsi hw hle l r).2.base.core.erase.core.state =
        eR.core.erase.core.state ∧
      (R2.row hpsi hw hle l r).2.base.stall = eR.stall at hframe
  have hfixedProgress := congrArg
    (fun p : R2.Cell psi kappa tau × R2.Cell psi kappa tau =>
      PathProgressView.ofState p.2.base.core) hfix
  change
    PathProgressView.ofState (R2.row hpsi hw hle l r).2.base.core =
      PathProgressView.ofState r.base.core at hfixedProgress
  have hfixedPath := congrArg
    (fun p : R2.Cell psi kappa tau × R2.Cell psi kappa tau =>
      p.2.base.core.erase.core.path) hfix
  change
    (R2.row hpsi hw hle l r).2.base.core.erase.core.path =
      r.base.core.erase.core.path at hfixedPath
  have hfixedState := congrArg
    (fun p : R2.Cell psi kappa tau × R2.Cell psi kappa tau =>
      p.2.base.core.erase.core.state) hfix
  change
    (R2.row hpsi hw hle l r).2.base.core.erase.core.state =
      r.base.core.erase.core.state at hfixedState
  have hfixedStall := congrArg
    (fun p : R2.Cell psi kappa tau × R2.Cell psi kappa tau =>
      p.2.base.stall) hfix
  change (R2.row hpsi hw hle l r).2.base.stall = r.base.stall at hfixedStall
  have heRStallInput : eR.stall = r.base.stall :=
    hframe.2.2.2.symm.trans hfixedStall
  rcases prepareExpiringDisposal_eq_or_active hpsi r.base with hprep | hprepActive
  · have hr0eq : r0 = r.base := by
      simpa [r0] using hprep
    have hr0stall : r.base.stall = r0.stall :=
      congrArg ExpiringAgentState.stall hr0eq.symm
    have heRStallOld : eR.stall = r0.stall :=
      heRStallInput.trans hr0stall
    by_cases hact : deletionActive baseR.core.erase = true
    · have heActive : eR = ⟨baseR.core, freshStall tau⟩ := by
        change deletionPriorityExpireOne tau r0 baseR =
          ⟨baseR.core, freshStall tau⟩
        exact deletionPriorityExpireOne_of_active tau r0 baseR hact
      have hbaseFields := deletionActive_true_fields_local baseR.core.erase hact
      have hbasePathEqInput :
          baseR.core.erase.core.path = r.base.core.erase.core.path := by
        calc
          baseR.core.erase.core.path = eR.core.erase.core.path := by rw [heActive]
          _ = (R2.row hpsi hw hle l r).2.base.core.erase.core.path :=
            hframe.2.1.symm
          _ = r.base.core.erase.core.path := hfixedPath
      have hbaseStateEqInput :
          baseR.core.erase.core.state = r.base.core.erase.core.state := by
        calc
          baseR.core.erase.core.state = eR.core.erase.core.state := by rw [heActive]
          _ = (R2.row hpsi hw hle l r).2.base.core.erase.core.state :=
            hframe.2.2.1.symm
          _ = r.base.core.erase.core.state := hfixedState
      have hinputPath : r.base.core.erase.core.path ≠ .bot := by
        intro hb
        apply hbaseFields.2
        exact hbasePathEqInput.trans hb
      have hinputState :
          r.base.core.erase.core.state = .eliminate_signal :=
        hbaseStateEqInput.symm.trans hbaseFields.1
      have hinputActive := deletionActive_eq_true
        r.base.core.erase hinputState hinputPath
      have hnorm := normalizeDeletion_eq_of_path_present
        r.base.core.erase hinputPath
      have hr0active : deletionActive (normalizeDeletion r0.core.erase) = true := by
        rw [hr0eq, hnorm]
        exact hinputActive
      have hqpath : q.2.agent.erase.core.path = .bot := by
        change
          (R2.bounded hpsi hw hle
            (⟨l0.core, l.fuel⟩ : WCell psi kappa)
            (⟨r0.core, r.fuel⟩ : WCell psi kappa)).2.agent.erase.core.path = .bot
        exact r2Bounded_active_responder_path hpsi hw hle
          (⟨l0.core, l.fuel⟩ : WCell psi kappa)
          (⟨r0.core, r.fuel⟩ : WCell psi kappa) hr0active
      have hbaseBot : baseR.core.erase.core.path = .bot := by
        change q.2.agent.erase.core.path = .bot
        exact hqpath
      exact hbaseFields.2 hbaseBot
    · have hePathExpire : eR = pathExpireOne tau r0 baseR := by
        change deletionPriorityExpireOne tau r0 baseR =
          pathExpireOne tau r0 baseR
        simp only [deletionPriorityExpireOne, hact,
          Bool.false_eq_true, if_false]
      by_cases hstatic :
          PathProgressView.ofState baseR.core =
            PathProgressView.ofState r0.core
      · by_cases hz : r0.stall.val = 0
        · have heFresh : eR.stall = freshStall tau := by
            rw [hePathExpire]
            unfold pathExpireOne
            rw [if_neg (not_not_intro hstatic)]
            simp [hz]
          have hfresh : freshStall tau = r0.stall :=
            heFresh.symm.trans heRStallOld
          have hv := congrArg Fin.val hfresh
          simp [freshStall] at hv
          omega
        · have hpos : 0 < r0.stall.val := Nat.pos_of_ne_zero hz
          have hdec := pathExpireOne_decreases_of_static
            tau r0 baseR hstatic hpos
          have hlt : eR.stall.val < r0.stall.val := by
            rw [hePathExpire]
            exact hdec
          have heqVal : eR.stall.val = r0.stall.val :=
            congrArg Fin.val heRStallOld
          omega
      · have heProgress : eR = ⟨baseR.core, freshStall tau⟩ := by
          rw [hePathExpire]
          exact pathExpireOne_of_progress tau r0 baseR hstatic
        have hbad :
            PathProgressView.ofState baseR.core =
              PathProgressView.ofState r0.core := by
          calc
            PathProgressView.ofState baseR.core =
                PathProgressView.ofState eR.core := by rw [heProgress]
            _ = PathProgressView.ofState
                (R2.row hpsi hw hle l r).2.base.core := hframe.1.symm
            _ = PathProgressView.ofState r.base.core := hfixedProgress
            _ = PathProgressView.ofState r0.core := by rw [hr0eq]
        exact hstatic hbad
  · have hr0active :
        deletionActive (normalizeDeletion r0.core.erase) = true := by
      simpa [r0] using hprepActive
    have hfields := deletionActive_true_fields_local
      (normalizeDeletion r0.core.erase) hr0active
    have hr0path : r0.core.erase.core.path ≠ .bot := by
      intro hbot
      apply hfields.2
      exact (normalizeDeletion_path_local r0.core.erase).trans hbot
    have hinputPath : r.base.core.erase.core.path ≠ .bot := by
      intro hbot
      apply hr0path
      have hp : r0.core.erase.core.path = r.base.core.erase.core.path := by
        simpa [r0] using prepareExpiringDisposal_path_local hpsi r.base
      exact hp.trans hbot
    have hqpath : q.2.agent.erase.core.path = .bot := by
      change
        (R2.bounded hpsi hw hle
          (⟨l0.core, l.fuel⟩ : WCell psi kappa)
          (⟨r0.core, r.fuel⟩ : WCell psi kappa)).2.agent.erase.core.path = .bot
      exact r2Bounded_active_responder_path hpsi hw hle
        (⟨l0.core, l.fuel⟩ : WCell psi kappa)
        (⟨r0.core, r.fuel⟩ : WCell psi kappa) hr0active
    have hbasePath : baseR.core.erase.core.path = .bot := by
      change q.2.agent.erase.core.path = .bot
      exact hqpath
    have hePath : eR.core.erase.core.path = .bot := by
      change
        (deletionPriorityExpireOne tau r0 baseR).core.erase.core.path = .bot
      exact expiry_preserves_absence_local r0 baseR hbasePath
    have hout :
        (R2.row hpsi hw hle l r).2.base.core.erase.core.path = .bot :=
      hframe.2.1.trans hePath
    exact hinputPath (hfixedPath.symm.trans hout)

theorem raw_row_not_fixed_of_root_successor_positive_timer
    (hpsi : 0 < psi) (h2 : 2 <= psi) (htau : 0 < tau)
    (l r : R2.Cell psi kappa tau)
    (_hroot : l.base.core.core.label.val = 0)
    (_hsucc : r.base.core.core.label.val = 1) :
    R2.row hpsi (by decide : 0 < 2) h2 l r ≠ (l, r) :=
  raw_row_not_fixed_of_positive_timer_any
    hpsi (by decide : 0 < 2) h2 htau l r

private theorem open_row_not_fixed_of_raw
    (hpsi : 0 < psi) (h2 : 2 <= psi)
    (l r : R2Coherence.Cell psi kappa tau)
    (hl : R2Coherence.OpenControl l)
    (hr : R2Coherence.OpenControl r)
    (hraw :
      R2.row hpsi (by decide : 0 < 2) h2 l.phys r.phys ≠
        (l.phys, r.phys)) :
    R2Coherence.row hpsi (by decide : 0 < 2) h2 l r ≠ (l, r) := by
  rcases hl with ⟨hlm, hlt⟩
  rcases hr with ⟨hrm, hrt⟩
  have hdispatch :
      R2Coherence.row hpsi (by decide : 0 < 2) h2 l r =
        R2Coherence.openStage hpsi (by decide : 0 < 2) h2 l r := by
    simp [R2Coherence.row, R2Coherence.ordinaryStage,
      hlm, hrm, hlt, hrt]
  rw [hdispatch]
  unfold R2Coherence.openStage
  dsimp only
  split
  · split
    · intro heq
      have hc := congrArg
        (fun q : R2Coherence.Cell psi kappa tau ×
            R2Coherence.Cell psi kappa tau => q.2.ctl.mark) heq
      change R2Coherence.Mark.closing = r.ctl.mark at hc
      rw [hrm] at hc
      cases hc
    · intro heq
      have hc := congrArg
        (fun q : R2Coherence.Cell psi kappa tau ×
            R2Coherence.Cell psi kappa tau => q.1.ctl.mark) heq
      change R2Coherence.Mark.closing = l.ctl.mark at hc
      rw [hlm] at hc
      cases hc
  · intro heq
    have hpL := congrArg
      (fun q : R2Coherence.Cell psi kappa tau ×
          R2Coherence.Cell psi kappa tau => q.1.phys) heq
    have hpR := congrArg
      (fun q : R2Coherence.Cell psi kappa tau ×
          R2Coherence.Cell psi kappa tau => q.2.phys) heq
    have hpL' :
        (R2.row hpsi (by decide : 0 < 2) h2 l.phys r.phys).1 =
          l.phys := by
      simpa [R2Coherence.install, R2Coherence.proposal] using hpL
    have hpR' :
        (R2.row hpsi (by decide : 0 < 2) h2 l.phys r.phys).2 =
          r.phys := by
      simpa [R2Coherence.install, R2Coherence.proposal] using hpR
    exact hraw (Prod.ext hpL' hpR')

theorem allOpen_leaderless_not_whole_fixed_of_root_successor_positive_timer
    (hpsi : 0 < psi) (h2 : 2 <= psi) (htau : 0 < tau)
    (ring : DirectedRing n)
    (C : R2Coherence.FC n psi kappa tau)
    (hOpen : R2Coherence.AllOpen C)
    (_hLeaderless :
      ∀ i : Fin n, (C i).phys.base.core.core.leader = false)
    (hRoot :
      ∃ e : Fin n,
        (C e).phys.base.core.core.label.val = 0 ∧
        (C (ring.rightNeighbor e)).phys.base.core.core.label.val = 1) :
    (∀ e : Fin n, R2Coherence.step hpsi h2 ring C e = C) → False := by
  rcases hRoot with ⟨e, hroot, hsucc⟩
  have hraw :
      R2.row hpsi (by decide : 0 < 2) h2
          (C e).phys (C (ring.rightNeighbor e)).phys ≠
        ((C e).phys, (C (ring.rightNeighbor e)).phys) :=
    raw_row_not_fixed_of_root_successor_positive_timer
      hpsi h2 htau (C e).phys (C (ring.rightNeighbor e)).phys
      hroot hsucc
  have hpair :
      R2Coherence.row hpsi (by decide : 0 < 2) h2
          (C e) (C (ring.rightNeighbor e)) ≠
        (C e, C (ring.rightNeighbor e)) :=
    open_row_not_fixed_of_raw hpsi h2
      (C e) (C (ring.rightNeighbor e))
      (hOpen e) (hOpen (ring.rightNeighbor e)) hraw
  have hne : ring.rightNeighbor e ≠ e := by
    intro heq
    have h1 := hsucc
    rw [heq] at h1
    omega
  intro hFixed
  have hcfg := hFixed e
  have hleft :
      (R2Coherence.row hpsi (by decide : 0 < 2) h2
        (C e) (C (ring.rightNeighbor e))).1 = C e := by
    have h := congrFun hcfg e
    simpa only [R2Coherence.step, R2Coherence.protocol,
      PopulationProtocol.step, if_true] using h
  have hright :
      (R2Coherence.row hpsi (by decide : 0 < 2) h2
        (C e) (C (ring.rightNeighbor e))).2 =
          C (ring.rightNeighbor e) := by
    have h := congrFun hcfg (ring.rightNeighbor e)
    simpa only [R2Coherence.step, R2Coherence.protocol,
      PopulationProtocol.step, if_neg hne, if_true] using h
  exact hpair (Prod.ext hleft hright)

end R2CoherenceOpenPositiveTimerNotFixed
