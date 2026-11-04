import Leader.Wu.Birth.CheckChainLessRow
import Leader.Wu.Birth.CheckChainActionSixTransport

set_option autoImplicit false

/-! # Transport of the action-6 signal on the actual R1 row

On an internal edge (label i, label i + 1) with 1 ≤ i and i + 1 < psi - 1, an `equal` follower at label i without
path2 and a `less` follower at label i + 1 holding the action-6 signal: the R1 row moves the signal to the left cell
and CHECK writes a fresh one on the `less` cell (`r1_signal6_row`): both cells end with the signal, states,
paths and labels unchanged, followers.  So a `less` cell emits action-6 signals towards label 0 one cell per
interaction.  Supporting pieces: the DONE move as an equality (`doneCaptureSigMove_signal6_eq`), CHECK on an
(`equal`, `less`) pair (`checkSig_equal_less`), the action-one COMPARE and the after-CHECK stages with signals on
both cells (`compare_keeps_signal6`, `afterCheck_keeps_signal6`), and the expiry and final-tail frames under the
weaker hypothesis that no endpoint has a pending terminal disposal (`row_right_frame_clear`,
`row_left_frame_clear`).
-/

namespace BirthCheckPermitRepairRowLift

open PPLL PPLLResearchFormulation PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
  PPLLLeaderCreationCleanupRepair BirthSigMoveDisposalRepair
open K2BirthDispatcher ExpiringK2Projection LDSinkKernelC K2BirthLeaderNormalize
open BirthCheckPermitRepairBirth

variable {ψ κ τ : Nat}

theorem prepare_identity_clear (hψ : 0 < ψ) (u : ExpiringAgentState ψ κ τ)
    (h : pendingTerminalDisposal hψ u.core.erase.core = false) : prepareExpiringDisposal hψ u = u := by
  unfold prepareExpiringDisposal
  rw [prepareBoundedDisposal_eq_of_clear hψ u.core h]

theorem expiring_right_erase_clear (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (l r : ExpiringAgentState ψ κ τ)
    (hld : BirthSigMoveDisposalRepair.pendingTerminalDisposal hψ l.core.erase.core = false)
    (hrd : BirthSigMoveDisposalRepair.pendingTerminalDisposal hψ r.core.erase.core = false)
    (hlel : l.core.erase.core.state ≠ .eliminate_signal) (hrel : r.core.erase.core.state ≠ .eliminate_signal)
    (hstall : r.stall.val ≠ 0) :
    (BirthCheckPermitRepair.expiring hψ (by decide : 0 < 2) h2 l r).2.core.erase =
      (BirthCheckPermitRepair.ordinary hψ (by decide : 0 < 2) h2 κ l.core.erase r.core.erase).2 := by
  have hb := congrArg Prod.snd (r1_bounded_erase (κ := κ) hψ h2 l.core r.core)
  rw [authorized_eq_ordinary hψ h2 _ _ hlel hrel] at hb
  unfold BirthCheckPermitRepair.expiring
  dsimp only
  rw [prepare_identity_clear hψ l hld, prepare_identity_clear hψ r hrd, expire_core_of_stall r _ hstall]
  exact hb

theorem expiring_left_erase_clear (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (l r : ExpiringAgentState ψ κ τ)
    (hld : BirthSigMoveDisposalRepair.pendingTerminalDisposal hψ l.core.erase.core = false)
    (hrd : BirthSigMoveDisposalRepair.pendingTerminalDisposal hψ r.core.erase.core = false)
    (hlel : l.core.erase.core.state ≠ .eliminate_signal) (hrel : r.core.erase.core.state ≠ .eliminate_signal)
    (hstall : l.stall.val ≠ 0) :
    (BirthCheckPermitRepair.expiring hψ (by decide : 0 < 2) h2 l r).1.core.erase =
      (BirthCheckPermitRepair.ordinary hψ (by decide : 0 < 2) h2 κ l.core.erase r.core.erase).1 := by
  have hb := congrArg Prod.fst (r1_bounded_erase (κ := κ) hψ h2 l.core r.core)
  rw [authorized_eq_ordinary hψ h2 _ _ hlel hrel] at hb
  unfold BirthCheckPermitRepair.expiring
  dsimp only
  rw [prepare_identity_clear hψ l hld, prepare_identity_clear hψ r hrd, expire_core_of_stall l _ hstall]
  exact hb


theorem row_right_frame_clear (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (l r : ExpiringAgentState ψ κ τ)
    (hld : BirthSigMoveDisposalRepair.pendingTerminalDisposal hψ l.core.erase.core = false)
    (hrd : BirthSigMoveDisposalRepair.pendingTerminalDisposal hψ r.core.erase.core = false)
    (hlel : l.core.erase.core.state ≠ .eliminate_signal) (hrel : r.core.erase.core.state ≠ .eliminate_signal)
    (hstall : r.stall.val ≠ 0)
    (hfol : (BirthCheckPermitRepair.ordinary hψ (by decide : 0 < 2) h2 κ l.core.erase r.core.erase).2.core.leader =
      false) :
    let q := BirthCheckPermitRepair.ordinary hψ (by decide : 0 < 2) h2 κ l.core.erase r.core.erase
    let o := (BirthCheckPermitRepair.row hψ (by decide : 0 < 2) h2 l r).2
    o.core.erase.core.state = q.2.core.state ∧ o.core.erase.core.path = q.2.core.path ∧
      o.core.erase.core.path2 = q.2.core.path2 ∧ o.core.erase.core.label = q.2.core.label ∧
      o.core.erase.core.reset_cmd = q.2.core.reset_cmd ∧ o.core.erase.core.leader = false := by
  intro q o
  have he := expiring_right_erase_clear (κ := κ) hψ h2 l r hld hrd hlel hrel hstall
  have hn := (finalPhysical_nonK2 hψ l r
    (normalizeLeader hψ (BirthCheckPermitRepair.expiring hψ (by decide : 0 < 2) h2 l r).1)
    (normalizeLeader hψ (BirthCheckPermitRepair.expiring hψ (by decide : 0 < 2) h2 l r).2)).2
  have hf := finalPhysical_right_follower hψ l r
    (normalizeLeader hψ (BirthCheckPermitRepair.expiring hψ (by decide : 0 < 2) h2 l r).1)
    (normalizeLeader hψ (BirthCheckPermitRepair.expiring hψ (by decide : 0 < 2) h2 l r).2)
  have ho : o = (finalPhysical hψ l r
      (normalizeLeader hψ (BirthCheckPermitRepair.expiring hψ (by decide : 0 < 2) h2 l r).1)
      (normalizeLeader hψ (BirthCheckPermitRepair.expiring hψ (by decide : 0 < 2) h2 l r).2)).2 := rfl
  rw [← ho] at hn hf
  clear_value o
  generalize hE : BirthCheckPermitRepair.expiring hψ (by decide : 0 < 2) h2 l r = E at he hn hf
  have hEl : E.2.core.core.leader = false := (congrArg (fun s : AuthorizedAgentState ψ => s.core.leader) he).trans hfol
  rw [normalizeLeader_of_follower hψ E.2 hEl] at hn hf
  have hx := nonK2_fields o E.2 hn
  refine ⟨?_, ?_, ?_, ?_, ?_, hf hEl⟩
  · exact hx.1.trans (congrArg (fun s : AuthorizedAgentState ψ => s.core.state) he)
  · exact hx.2.1.trans (congrArg (fun s : AuthorizedAgentState ψ => s.core.path) he)
  · exact hx.2.2.1.trans (congrArg (fun s : AuthorizedAgentState ψ => s.core.path2) he)
  · exact hx.2.2.2.1.trans (congrArg (fun s : AuthorizedAgentState ψ => s.core.label) he)
  · exact hx.2.2.2.2.2.1.trans (congrArg (fun s : AuthorizedAgentState ψ => s.core.reset_cmd) he)

/-- The initiator of the actual R1 row output agrees with the ordinary initiator on the chain fields when both
ordinary endpoints are followers and the old initiator stall is positive. -/
theorem row_left_frame_clear (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (l r : ExpiringAgentState ψ κ τ)
    (hld : BirthSigMoveDisposalRepair.pendingTerminalDisposal hψ l.core.erase.core = false)
    (hrd : BirthSigMoveDisposalRepair.pendingTerminalDisposal hψ r.core.erase.core = false)
    (hlel : l.core.erase.core.state ≠ .eliminate_signal) (hrel : r.core.erase.core.state ≠ .eliminate_signal)
    (hlstall : l.stall.val ≠ 0) (hrstall : r.stall.val ≠ 0)
    (hfolL : (BirthCheckPermitRepair.ordinary hψ (by decide : 0 < 2) h2 κ l.core.erase r.core.erase).1.core.leader =
      false)
    (hfolR : (BirthCheckPermitRepair.ordinary hψ (by decide : 0 < 2) h2 κ l.core.erase r.core.erase).2.core.leader =
      false) :
    let q := BirthCheckPermitRepair.ordinary hψ (by decide : 0 < 2) h2 κ l.core.erase r.core.erase
    let o := (BirthCheckPermitRepair.row hψ (by decide : 0 < 2) h2 l r).1
    o.core.erase.core.state = q.1.core.state ∧ o.core.erase.core.path = q.1.core.path ∧
      o.core.erase.core.path2 = q.1.core.path2 ∧ o.core.erase.core.label = q.1.core.label ∧
      o.core.erase.core.leader = false := by
  intro q o
  have heL := expiring_left_erase_clear (κ := κ) hψ h2 l r hld hrd hlel hrel hlstall
  have heR := expiring_right_erase_clear (κ := κ) hψ h2 l r hld hrd hlel hrel hrstall
  have hn := (finalPhysical_nonK2 hψ l r
    (normalizeLeader hψ (BirthCheckPermitRepair.expiring hψ (by decide : 0 < 2) h2 l r).1)
    (normalizeLeader hψ (BirthCheckPermitRepair.expiring hψ (by decide : 0 < 2) h2 l r).2)).1
  have hf := finalPhysical_left_follower hψ l r
    (normalizeLeader hψ (BirthCheckPermitRepair.expiring hψ (by decide : 0 < 2) h2 l r).1)
    (normalizeLeader hψ (BirthCheckPermitRepair.expiring hψ (by decide : 0 < 2) h2 l r).2)
  have ho : o = (finalPhysical hψ l r
      (normalizeLeader hψ (BirthCheckPermitRepair.expiring hψ (by decide : 0 < 2) h2 l r).1)
      (normalizeLeader hψ (BirthCheckPermitRepair.expiring hψ (by decide : 0 < 2) h2 l r).2)).1 := rfl
  rw [← ho] at hn hf
  clear_value o
  generalize hE : BirthCheckPermitRepair.expiring hψ (by decide : 0 < 2) h2 l r = E at heL heR hn hf
  have hEl : E.1.core.core.leader = false :=
    (congrArg (fun s : AuthorizedAgentState ψ => s.core.leader) heL).trans hfolL
  have hEr : E.2.core.core.leader = false :=
    (congrArg (fun s : AuthorizedAgentState ψ => s.core.leader) heR).trans hfolR
  rw [normalizeLeader_of_follower hψ E.1 hEl, normalizeLeader_of_follower hψ E.2 hEr] at hf
  rw [normalizeLeader_of_follower hψ E.1 hEl] at hn
  have hx := nonK2_fields o E.1 hn
  refine ⟨?_, ?_, ?_, ?_, hf hEl hEr⟩
  · exact hx.1.trans (congrArg (fun s : AuthorizedAgentState ψ => s.core.state) heL)
  · exact hx.2.1.trans (congrArg (fun s : AuthorizedAgentState ψ => s.core.path) heL)
  · exact hx.2.2.1.trans (congrArg (fun s : AuthorizedAgentState ψ => s.core.path2) heL)
  · exact hx.2.2.2.1.trans (congrArg (fun s : AuthorizedAgentState ψ => s.core.label) heL)


end BirthCheckPermitRepairRowLift

namespace BirthCheckChainR1

open PPLL PPLLResearchFormulation PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
  PPLLLeaderCreationCleanupRepair BirthGenerationDone BirthShortDoneTerminalEntryCut

variable {ψ : Nat}

theorem checkSig_equal_less (hψ : ψ > 0) (l r : AgentState ψ) (hl : l.state = .equal) (hlab : l.label.val < ψ - 1)
    (hr : r.state = .less) :
    (checkSig hψ l r).1 = l ∧ (checkSig hψ l r).2 = { r with path2 := some ⟨0, 0, 0, 6⟩ } := by
  refine ⟨?_, ?_⟩
  · cases hpath : l.path with
    | bot =>
        simp [checkSig, checkSigSetReady, checkSigCheckL, checkSigSetResult, hpath, hl]
    | some a b =>
        simp [checkSig, checkSigSetReady, checkSigCheckL, checkSigSetResult, hpath, hl]
        split <;> simp_all
  · have hsr : checkSigSetReady r = r := by
      unfold checkSigSetReady; split
      · simp [hr]
      · rfl
    have hsl : (checkSigCheckL hψ (checkSigSetReady l)).state = .equal := by
      cases hpath : l.path with
      | bot => simp [checkSigSetReady, checkSigCheckL, hpath, hl]
      | some a b =>
          simp [checkSigSetReady, checkSigCheckL, hpath, hl]
          split <;> simp_all
    have hcr : checkSigCheckR hψ (checkSigCheckL hψ (checkSigSetReady l)) r = r := by
      unfold checkSigCheckR; split
      · split
        · split
          · rename_i h; rw [hr] at h; cases h
          · rfl
        · rfl
      · rfl
    unfold checkSig
    simp only [hsr, hcr]
    simp [checkSigSetResult, hr]

section Signal6

open PPLLWallSweepRepair PPLLWallSweepPreCheckResetRepair PPLLTerminalEqualSupportRepair BirthSigMoveDisposalRepair
  BirthArrivalCaptureRepair BirthSingleUseReleaseRepair

theorem doneCaptureSigMove_signal6_eq (hψ : 0 < ψ) (l r : AgentState ψ) (a b c d : Nat)
    (hlp : l.path = .some a b) (hrp : r.path = .some c d)
    (hll : l.leader = false) (hrl : r.leader = false)
    (hlp2 : l.path2 = none) (hrp2 : r.path2 = some ⟨0, 0, 0, 6⟩)
    (hldn : l.state ≠ .done) (hrdep : r.state ≠ .depart) (hl0 : l.label ≠ ⟨0, hψ⟩) :
    doneCaptureSigMove hψ l r = ({ l with path2 := some ⟨0, 0, 0, 6⟩ }, { r with path2 := none }) := by
  have hp : sigMoveLeaderPreclear hψ l r = (l, r) := by
    simp [sigMoveLeaderPreclear, incompleteLeftLeaderBoundary, clearIfLeader, hll, hrl]
  have hm : doneTransfers l r = ({ l with path2 := some ⟨0, 0, 0, 6⟩ }, { r with path2 := none }) := by
    simp [doneTransfers, holdDoneStep1, hldn, captureStep1, hlp, hrp, controlTransfers, sigMoveStep2,
      sigMoveStep3, sigMoveStep4, sigMoveStep5, hlp2, hrp2]
  have hw : comparisonLeaderWall { l with path2 := some ⟨0, 0, 0, 6⟩ } { r with path2 := none } =
      ({ l with path2 := some ⟨0, 0, 0, 6⟩ }, { r with path2 := none }) := by
    simp [comparisonLeaderWall, hll, hrl]
  unfold doneCaptureSigMove
  rw [hp]; dsimp only; rw [hm]; dsimp only; rw [hw]
  by_cases hterm : l.label = ⟨ψ - 1, by omega⟩
  · have hne : ψ - 1 ≠ 0 := by
      intro h; apply hl0; rw [hterm]; exact Fin.ext h
    simp [singleUseControlTail, singleUseApplyControl, hl0, hterm, hrdep, hne]
  · simp [singleUseControlTail, singleUseApplyControl, hl0, hterm, hrdep]

/-- The DONE move, reset wall, sanitizer and CHECK cut on an (`equal`, `less` with action 6) generation output. -/
theorem doneThroughCheck_signal6 {width κ : Nat} (hψ : 0 < ψ) (hwidth : 0 < width) (hle : width ≤ ψ)
    (l r : AuthorizedAgentState ψ) (a b c d : Nat)
    (hlp : (generationBeforeMoveEntryWidth hψ hwidth hle κ l r).1.core.path = .some a b)
    (hrp : (generationBeforeMoveEntryWidth hψ hwidth hle κ l r).2.core.path = .some c d)
    (hll : (generationBeforeMoveEntryWidth hψ hwidth hle κ l r).1.core.leader = false)
    (hrl : (generationBeforeMoveEntryWidth hψ hwidth hle κ l r).2.core.leader = false)
    (hlr : (generationBeforeMoveEntryWidth hψ hwidth hle κ l r).1.core.reset_cmd = false)
    (hrr : (generationBeforeMoveEntryWidth hψ hwidth hle κ l r).2.core.reset_cmd = false)
    (hlp2 : (generationBeforeMoveEntryWidth hψ hwidth hle κ l r).1.core.path2 = none)
    (hrp2 : (generationBeforeMoveEntryWidth hψ hwidth hle κ l r).2.core.path2 = some ⟨0, 0, 0, 6⟩)
    (hle' : (generationBeforeMoveEntryWidth hψ hwidth hle κ l r).1.core.state = .equal)
    (hrs : (generationBeforeMoveEntryWidth hψ hwidth hle κ l r).2.core.state = .less)
    (hl0 : (generationBeforeMoveEntryWidth hψ hwidth hle κ l r).1.core.label ≠ ⟨0, hψ⟩)
    (hlab : (generationBeforeMoveEntryWidth hψ hwidth hle κ l r).1.core.label.val < ψ - 1) :
    (doneThroughCheckEntryWidth hψ hwidth hle κ l r).1.core =
        { (generationBeforeMoveEntryWidth hψ hwidth hle κ l r).1.core with path2 := some ⟨0, 0, 0, 6⟩ } ∧
      (doneThroughCheckEntryWidth hψ hwidth hle κ l r).2.core =
        { (generationBeforeMoveEntryWidth hψ hwidth hle κ l r).2.core with path2 := some ⟨0, 0, 0, 6⟩ } := by
  have hc : doneThroughCheckEntryWidth hψ hwidth hle κ l r =
      preserveDoneCheck hψ (doneBeforeCheckEntryWidth hψ hwidth hle κ l r).1
        (doneBeforeCheckEntryWidth hψ hwidth hle κ l r).2 := rfl
  have hd : doneBeforeCheckEntryWidth hψ hwidth hle κ l r =
      sanitizeAuthorizedPair hψ (preCheckResetWall
        (authorizedDoneMove hψ (generationBeforeMoveEntryWidth hψ hwidth hle κ l r).1
          (generationBeforeMoveEntryWidth hψ hwidth hle κ l r).2).1
        (authorizedDoneMove hψ (generationBeforeMoveEntryWidth hψ hwidth hle κ l r).1
          (generationBeforeMoveEntryWidth hψ hwidth hle κ l r).2).2) := rfl
  rw [hc, hd]
  generalize generationBeforeMoveEntryWidth hψ hwidth hle κ l r = B at *
  have hmc := authorizedDoneMove_core hψ B.1 B.2
  have hldn : B.1.core.state ≠ .done := by rw [hle']; decide
  have hrdep : B.2.core.state ≠ .depart := by rw [hrs]; decide
  rw [doneCaptureSigMove_signal6_eq hψ B.1.core B.2.core a b c d hlp hrp hll hrl hlp2 hrp2 hldn hrdep hl0] at hmc
  generalize authorizedDoneMove hψ B.1 B.2 = m at hmc
  have hm1 : m.1.core = { B.1.core with path2 := some ⟨0, 0, 0, 6⟩ } := congrArg Prod.fst hmc
  have hm2 : m.2.core = { B.2.core with path2 := none } := congrArg Prod.snd hmc
  have hw : preCheckResetWall m.1 m.2 = (m.1, m.2) :=
    preCheckResetWall_eq_of_inactive m.1 m.2 (by rw [hm1]; exact hll) (by rw [hm1]; exact hlr)
      (by rw [hm2]; exact hrr)
  have hs1 : sanitizeAuthorizedTerminalEqual hψ m.1 = m.1 := by
    unfold sanitizeAuthorizedTerminalEqual unsupportedTerminalEqual
    have : m.1.core.label ≠ ⟨ψ - 1, by omega⟩ := by
      rw [hm1]; intro h; have := congrArg Fin.val h; simp only at this; omega
    simp [this]
  have hs2 : sanitizeAuthorizedTerminalEqual hψ m.2 = m.2 := by
    unfold sanitizeAuthorizedTerminalEqual unsupportedTerminalEqual
    have : m.2.core.state ≠ .equal := by rw [hm2, hrs]; decide
    simp [this]
  rw [hw]
  simp only [sanitizeAuthorizedPair]
  rw [hs1, hs2]
  rw [preserveDoneCheck_of_no_done hψ m.1 m.2 (by rw [hm1, hle']; decide) (by rw [hm2, hrs]; decide),
    BirthTossCheckPreservationRepair.preserveTossCheck_of_no_toss hψ m.1 m.2 (by rw [hm1, hle']; decide)
      (by rw [hm2, hrs]; decide),
    BirthCheckCongestGuardRepair.congestGuardCheck_of_clear hψ m.1 m.2 (by rw [hm1, hle']; decide)
      (by rw [hm2, hrs]; decide)]
  have e := authorizedCheckSig_cores hψ m.1 m.2
  rw [e.1, e.2, hm1, hm2]
  have hck := checkSig_equal_less hψ { B.1.core with path2 := some ⟨0, 0, 0, 6⟩ } { B.2.core with path2 := none }
    (by simp [hle']) (by simpa using hlab) (by simp [hrs])
  rw [hck.1, hck.2]
  exact ⟨rfl, rfl⟩

end Signal6

theorem compare_keeps_signal6 (hψ : ψ > 0) (l r : AuthorizedAgentState ψ) (a b c d : Nat)
    (hlpath : l.core.path = .some a b) (hrpath : r.core.path = .some c d)
    (hl : l.core.state = .equal) (hr : r.core.state = .less)
    (hlp2 : l.core.path2 = some ⟨0, 0, 0, 6⟩) (hrp2 : r.core.path2 = some ⟨0, 0, 0, 6⟩)
    (hperm : l.core.label ≠ ⟨0, hψ⟩ ∨ l.path0Crossed = false) :
    let q := PPLLCompleteMultiLeaderCleanup.authorizedCompareSigActionOne hψ l r
    q.1.core = l.core ∧ q.2.core = r.core := by
  have hfresh : freshComparisonStart hψ
      (⟨compareSigInit l.core, normalizePermit (compareSigInit l.core) l.path0Crossed⟩ : AuthorizedAgentState ψ)
      = false := by
    unfold freshComparisonStart normalizePermit
    simp only [compareSigInit, hlpath]
    cases a with
    | zero =>
        rcases hperm with h | h
        · simp [h]
        · simp [h]
    | succ a => rfl
  simp only [PPLLCompleteMultiLeaderCleanup.authorizedCompareSigActionOne]
  have hinit : compareSigInit l.core = l.core := by simp [compareSigInit, hlpath]
  simp only [hinit, hlpath, hrpath]
  rw [hinit] at hfresh
  simp only [authorizedCmpUpdate, hfresh, Bool.false_and, if_false, Bool.false_eq_true]
  simp [cmpUpdateReturnPriority, cmpUpdateSetPath2, PPLLCompleteMultiLeaderCleanup.compareSigDispatchActionOne,
    PPLLCompleteMultiLeaderCleanup.compareBitActionOne, PPLLRepair.compareBitUpdateRActionOne, compareBitUpdateL,
    hl, hr, hlp2, hrp2, hlpath]


attribute [local irreducible] BirthStationaryWrite.stationaryPersistentRaw

theorem afterCheck_keeps_signal6 {width : Nat} (hψ : 0 < ψ) (hwidth : 0 < width) (hle : width ≤ ψ)
    (l r : AuthorizedAgentState ψ) (a b c d : Nat)
    (hlpath : l.core.path = .some a b) (hrpath : r.core.path = .some c d)
    (hl : l.core.state = .equal) (hr : r.core.state = .less)
    (hlp2 : l.core.path2 = some ⟨0, 0, 0, 6⟩) (hrp2 : r.core.path2 = some ⟨0, 0, 0, 6⟩)
    (hperm : l.core.label ≠ ⟨0, hψ⟩ ∨ l.path0Crossed = false)
    (hrterm : r.core.label ≠ ⟨ψ - 1, by omega⟩)
    (hll : l.core.leader = false) (hlr : l.core.reset_cmd = false) (hrr : r.core.reset_cmd = false) :
    let q := BirthShortDoneCuts.afterCheckMetadataWidth hψ hwidth hle l r
    postView q.1.core = postView l.core ∧ postView q.2.core = postView r.core := by
  -- DISAPPEAR
  let q0 := authorizedDisappear hψ l r
  have hd := disappear_keeps_view hψ l.core r.core (by rw [hl]; decide) (by rw [hr]; decide) hrterm
  have hdr := disappear_reset_cmd hψ l.core r.core
  have h0c1 : q0.1.core = (disappear hψ l.core r.core).1 := rfl
  have h0c2 : q0.2.core = (disappear hψ l.core r.core).2 := rfl
  have e1 := hd.1; have e2 := hd.2
  unfold chainView at e1 e2
  simp only [Prod.mk.injEq] at e1 e2
  have h0perm : q0.1.core.label ≠ ⟨0, hψ⟩ ∨ q0.1.path0Crossed = false := by
    rcases hperm with h | h
    · left; rw [h0c1, e1.2.2.2.1]; exact h
    · right
      show reconcilePermit l (disappear hψ l.core r.core).1 = false
      unfold reconcilePermit normalizePermit
      split
      · split <;> simp_all
      · rfl
  -- COMPARE
  have hc := compare_keeps_signal6 hψ q0.1 q0.2 a b c d
    (by rw [h0c1, e1.2.1]; exact hlpath) (by rw [h0c2, e2.2.1]; exact hrpath)
    (by rw [h0c1, e1.1]; exact hl) (by rw [h0c2, e2.1]; exact hr)
    (by rw [h0c1, e1.2.2.1]; exact hlp2) (by rw [h0c2, e2.2.2.1]; exact hrp2) h0perm
  -- SUPPRESS
  let q1 := PPLLCompleteMultiLeaderCleanup.authorizedCompareSigActionOne hψ q0.1 q0.2
  have hq1a : q1.1.core = q0.1.core := hc.1
  have hq1b : q1.2.core = q0.2.core := hc.2
  have hs := suppress_keeps_view hψ hwidth hle q1.1.core q1.2.core
    (by rw [hq1a, h0c1, e1.2.2.2.2.2]; exact hll) (by rw [hq1a, h0c1, hdr.1]; exact hlr)
    (by rw [hq1b, h0c2, hdr.2]; exact hrr)
  -- writer
  let q2 := BirthShortDoneCuts.authorizedSuppressWidth hψ hwidth hle q1.1 q1.2
  have hq2a : q2.1.core = (BirthShortWait.suppressSigResetKillWidth hψ hwidth hle q1.1.core q1.2.core).1 := rfl
  have hq2b : q2.2.core = (BirthShortWait.suppressSigResetKillWidth hψ hwidth hle q1.1.core q1.2.core).2 := rfl
  have hw := BirthStationaryWrite.stationaryPersistentRaw_frame hψ q2.1.core q2.2.core
  unfold BirthStationaryWrite.swPair at hw
  obtain ⟨hwa, hwb⟩ := Prod.mk.inj hw
  have hfin : BirthShortDoneCuts.afterCheckMetadataWidth hψ hwidth hle l r =
      BirthStationaryWrite.stationaryPersistentAuthorizedRow hψ q2.1 q2.2 := rfl
  have hc1 : (BirthStationaryWrite.stationaryPersistentAuthorizedRow hψ q2.1 q2.2).1.core =
      (BirthStationaryWrite.stationaryPersistentRaw hψ q2.1.core q2.2.core).1 := rfl
  have hc2 : (BirthStationaryWrite.stationaryPersistentAuthorizedRow hψ q2.1 q2.2).2.core =
      (BirthStationaryWrite.stationaryPersistentRaw hψ q2.1.core q2.2.core).2 := rfl
  have hw1 : postView (BirthStationaryWrite.stationaryPersistentAuthorizedRow hψ q2.1 q2.2).1.core =
      postView q2.1.core := by
    rw [hc1]; exact postView_of_swView hwa
  have hw2 : postView (BirthStationaryWrite.stationaryPersistentAuthorizedRow hψ q2.1 q2.2).2.core =
      postView q2.2.core := by
    rw [hc2]; exact postView_of_swView hwb
  have hs1 : postView q2.1.core = postView q1.1.core := by rw [hq2a]; exact postView_of_chainView hs.1
  have hs2 : postView q2.2.core = postView q1.2.core := by rw [hq2b]; exact postView_of_chainView hs.2
  have hd1 : postView q0.1.core = postView l.core := by rw [h0c1]; exact postView_of_chainView hd.1
  have hd2 : postView q0.2.core = postView r.core := by rw [h0c2]; exact postView_of_chainView hd.2
  rw [hfin]
  exact ⟨hw1.trans (hs1.trans (by rw [hq1a]; exact hd1)), hw2.trans (hs2.trans (by rw [hq1b]; exact hd2))⟩



theorem ordinary_signal6_row (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (κ : Nat) (l r : AuthorizedAgentState ψ) (i bl br : Nat)
    (hcons : r.core.label = ⟨(l.core.label.val + 1) % ψ, Nat.mod_lt _ hψ⟩)
    (hll : l.core.leader = false) (hrl : r.core.leader = false)
    (hlp : l.core.path = .some i bl) (hlab : l.core.label.val = i) (hi0 : 1 ≤ i) (hi : i + 1 < ψ - 1)
    (hrp : r.core.path = .some (i + 1) br) (hrlab : r.core.label.val = i + 1)
    (hleq : l.core.state = .equal) (hlp2 : l.core.path2 = none)
    (hrls : r.core.state = .less) (hrp2 : r.core.path2 = some ⟨0, 0, 0, 6⟩)
    (hlr : l.core.reset_cmd = false) (hrr : r.core.reset_cmd = false)
    (hr5 : ∀ p, r.core.path5 = some p → p.1 ≠ -1) :
    let q := BirthCheckPermitRepair.ordinary hψ (by decide : 0 < 2) h2 κ l r
    (q.1.core.state = .equal ∧ q.1.core.path = l.core.path ∧ q.1.core.path2 = some ⟨0, 0, 0, 6⟩ ∧
        q.1.core.label = l.core.label ∧ q.1.core.leader = false) ∧
      (q.2.core.state = .less ∧ q.2.core.path = r.core.path ∧ q.2.core.path2 = some ⟨0, 0, 0, 6⟩ ∧
        q.2.core.label = r.core.label ∧ q.2.core.leader = false) := by
  intro q
  have hi' : i + 1 < ψ := by omega
  have hg := generation_keeps_chain (κ := κ) hψ (by decide : 0 < 2) h2 l r i bl br hcons hll hrl hlp hrp hi'
    (by rw [hleq]; decide) (by rw [hleq]; decide) (by rw [hrls]; decide) (by rw [hrls]; decide)
    (by rw [hrls]; decide) (fun h => absurd h (by omega)) hr5
  generalize hB : generationBeforeMoveEntryWidth hψ (by decide : 0 < 2) h2 κ l r = B at hg
  have b1 := hg.1; have b2 := hg.2
  unfold genView at b1 b2
  simp only [Prod.mk.injEq] at b1 b2
  obtain ⟨s1, p1, q1, lb1, bt1, ld1, rc1⟩ := b1
  obtain ⟨s2, p2, q2, lb2, bt2, ld2, rc2⟩ := b2
  have hcut := doneThroughCheck_signal6 (κ := κ) hψ (by decide : 0 < 2) h2 l r i bl (i + 1) br
    (by rw [hB, p1]; exact hlp) (by rw [hB, p2]; exact hrp) (by rw [hB, ld1]; exact hll) (by rw [hB, ld2]; exact hrl)
    (by rw [hB, rc1]; exact hlr) (by rw [hB, rc2]; exact hrr) (by rw [hB, q1]; exact hlp2) (by rw [hB, q2]; exact hrp2)
    (by rw [hB, s1]; exact hleq) (by rw [hB, s2]; exact hrls)
    (by rw [hB]; intro h; have := congrArg Fin.val h; rw [lb1, hlab] at this; simp only at this; omega)
    (by rw [hB, lb1, hlab]; omega)
  rw [hB] at hcut
  generalize hC : doneThroughCheckEntryWidth hψ (by decide : 0 < 2) h2 κ l r = C at hcut
  obtain ⟨hc1, hc2⟩ := hcut
  have c1s : C.1.core.state = .equal := by rw [hc1]; exact s1.trans hleq
  have c1p : C.1.core.path = l.core.path := by rw [hc1]; exact p1
  have c1q : C.1.core.path2 = some ⟨0, 0, 0, 6⟩ := by rw [hc1]
  have c1lb : C.1.core.label = l.core.label := by rw [hc1]; exact lb1
  have c1ld : C.1.core.leader = false := by rw [hc1]; exact ld1.trans hll
  have c1rc : C.1.core.reset_cmd = false := by rw [hc1]; exact rc1.trans hlr
  have c2s : C.2.core.state = .less := by rw [hc2]; exact s2.trans hrls
  have c2p : C.2.core.path = r.core.path := by rw [hc2]; exact p2
  have c2q : C.2.core.path2 = some ⟨0, 0, 0, 6⟩ := by rw [hc2]
  have c2lb : C.2.core.label = r.core.label := by rw [hc2]; exact lb2
  have c2ld : C.2.core.leader = false := by rw [hc2]; exact ld2.trans hrl
  have c2rc : C.2.core.reset_cmd = false := by rw [hc2]; exact rc2.trans hrr
  have hfix : BirthCheckPermitRepair.permitFix C.1 = ⟨C.1.core, false⟩ := by
    unfold BirthCheckPermitRepair.permitFix; rw [c1s]; simp
  have hac := afterCheck_keeps_signal6 hψ (by decide : 0 < 2) h2 ⟨C.1.core, false⟩ C.2 i bl (i + 1) br
    (by show C.1.core.path = _; rw [c1p]; exact hlp) (by rw [c2p]; exact hrp)
    (by show C.1.core.state = _; exact c1s) c2s
    (by show C.1.core.path2 = _; exact c1q) c2q
    (Or.inr rfl)
    (by rw [c2lb]; intro h; have := congrArg Fin.val h; rw [hrlab] at this; simp only at this; omega)
    (by show C.1.core.leader = _; exact c1ld) (by show C.1.core.reset_cmd = _; exact c1rc) c2rc
  obtain ⟨pv1, pv2⟩ := hac
  generalize hQ : BirthShortDoneCuts.afterCheckMetadataWidth hψ (by decide : 0 < 2) h2 ⟨C.1.core, false⟩ C.2 = Q
    at pv1 pv2
  unfold postView at pv1 pv2
  simp only [Prod.mk.injEq] at pv1 pv2
  have hq : q = markLeaderBirth (K2BirthDispatcher.authBirth l r Q) Q := by
    show BirthCheckPermitRepair.ordinary hψ (by decide : 0 < 2) h2 κ l r = _
    unfold BirthCheckPermitRepair.ordinary
    dsimp only
    rw [hC, hfix, hQ]
  have hborn : K2BirthDispatcher.authBirth l r Q = false := by
    unfold K2BirthDispatcher.authBirth endpointLeaderBorn
    rw [pv1.2.2.2.2, pv2.2.2.2.2]
    show (!l.core.leader && C.1.core.leader || !r.core.leader && C.2.core.leader) = false
    rw [c1ld, c2ld]
    simp
  rw [hq, hborn]
  simp only [markLeaderBirth, if_false, Bool.false_eq_true]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_⟩⟩
  · rw [pv1.1]; exact c1s
  · rw [pv1.2.1]; exact c1p
  · rw [pv1.2.2.1]; exact c1q
  · rw [pv1.2.2.2.1]; exact c1lb
  · rw [pv1.2.2.2.2]; exact c1ld
  · rw [pv2.1]; exact c2s
  · rw [pv2.2.1]; exact c2p
  · rw [pv2.2.2.1]; exact c2q
  · rw [pv2.2.2.2.1]; exact c2lb
  · rw [pv2.2.2.2.2]; exact c2ld

end BirthCheckChainR1

namespace BirthCheckPermitRepairRowLift

open PPLL PPLLResearchFormulation PPLLExpiringComparisonRepair

variable {ψ κ τ : Nat}

/-- Action-6 transport on the actual R1 row: both cells end with the signal, states, paths and labels unchanged,
followers; the responder also keeps a false reset command. -/
theorem r1_signal6_row (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (l r : ExpiringAgentState ψ κ τ) (i bl br : Nat)
    (hcons : r.core.erase.core.label = ⟨(l.core.erase.core.label.val + 1) % ψ, Nat.mod_lt _ hψ⟩)
    (hll : l.core.erase.core.leader = false) (hrl : r.core.erase.core.leader = false)
    (hlp : l.core.erase.core.path = .some i bl) (hlab : l.core.erase.core.label.val = i) (hi0 : 1 ≤ i)
    (hi : i + 1 < ψ - 1)
    (hrp : r.core.erase.core.path = .some (i + 1) br) (hrlab : r.core.erase.core.label.val = i + 1)
    (hleq : l.core.erase.core.state = .equal) (hlp2 : l.core.erase.core.path2 = none)
    (hrls : r.core.erase.core.state = .less) (hrp2 : r.core.erase.core.path2 = some ⟨0, 0, 0, 6⟩)
    (hlr : l.core.erase.core.reset_cmd = false) (hrr : r.core.erase.core.reset_cmd = false)
    (hr5 : ∀ p, r.core.erase.core.path5 = some p → p.1 ≠ -1)
    (hlstall : l.stall.val ≠ 0) (hrstall : r.stall.val ≠ 0) :
    let o := BirthCheckPermitRepair.row hψ (by decide : 0 < 2) h2 l r
    (o.1.core.erase.core.state = .equal ∧ o.1.core.erase.core.path = l.core.erase.core.path ∧
        o.1.core.erase.core.path2 = some ⟨0, 0, 0, 6⟩ ∧ o.1.core.erase.core.label = l.core.erase.core.label ∧
        o.1.core.erase.core.leader = false) ∧
      (o.2.core.erase.core.state = .less ∧ o.2.core.erase.core.path = r.core.erase.core.path ∧
        o.2.core.erase.core.path2 = some ⟨0, 0, 0, 6⟩ ∧ o.2.core.erase.core.label = r.core.erase.core.label ∧
        o.2.core.erase.core.reset_cmd = false ∧ o.2.core.erase.core.leader = false) := by
  intro o
  have hc := BirthCheckChainR1.ordinary_signal6_row hψ h2 κ l.core.erase r.core.erase i bl br hcons hll hrl hlp hlab
    hi0 hi hrp hrlab hleq hlp2 hrls hrp2 hlr hrr hr5
  have hlel : l.core.erase.core.state ≠ .eliminate_signal := by rw [hleq]; decide
  have hrel : r.core.erase.core.state ≠ .eliminate_signal := by rw [hrls]; decide
  have hld : BirthSigMoveDisposalRepair.pendingTerminalDisposal hψ l.core.erase.core = false := by
    simp [BirthSigMoveDisposalRepair.pendingTerminalDisposal, hlp2]
  have hrd : BirthSigMoveDisposalRepair.pendingTerminalDisposal hψ r.core.erase.core = false := by
    simp [BirthSigMoveDisposalRepair.pendingTerminalDisposal, hrp2]
  have hfR := row_right_frame_clear (κ := κ) hψ h2 l r hld hrd hlel hrel hrstall hc.2.2.2.2.2
  have hfL := row_left_frame_clear (κ := κ) hψ h2 l r hld hrd hlel hrel hlstall hrstall hc.1.2.2.2.2 hc.2.2.2.2.2
  have hres := (ordinary_reset_false hψ h2 κ l.core.erase r.core.erase hlel hrel hll hlr hrr).2
  exact ⟨⟨hfL.1.trans hc.1.1, hfL.2.1.trans hc.1.2.1, hfL.2.2.1.trans hc.1.2.2.1, hfL.2.2.2.1.trans hc.1.2.2.2.1,
      hfL.2.2.2.2⟩,
    ⟨hfR.1.trans hc.2.1, hfR.2.1.trans hc.2.2.1, hfR.2.2.1.trans hc.2.2.2.1, hfR.2.2.2.1.trans hc.2.2.2.2.1,
      hfR.2.2.2.2.1.trans hres, hfR.2.2.2.2.2⟩⟩

end BirthCheckPermitRepairRowLift
