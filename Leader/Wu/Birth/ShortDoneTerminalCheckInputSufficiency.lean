import Leader.Wu.Birth.ShortDoneTerminalCheckInputSources
import Leader.Wu.Birth.ShortDoneTerminalBirthPhysical

namespace BirthShortDoneTerminalCheckInputSufficiency

open PPLL PPLLAuthorizedComparisonRepair
  PPLLExpiringComparisonRepair PPLLLeaderCreationCleanupRepair
  BirthSigMoveDisposalRepair BirthShortDoneTerminalEntryCut
open BirthShortDoneTerminalBirthSources
  BirthShortDoneTerminalCheckInputSources
open BirthGenerationDone BirthTossCheckPreservationRepair
  BirthCheckCongestGuardRepair BirthShortDoneCuts K2BirthDispatcher

set_option autoImplicit false
set_option Elab.async false
set_option pp.structureInstances false

variable {ψ width κ τ : Nat}

/-! ## Raw CHECK sufficiency -/

private theorem checkSigSetReady_path (u : AgentState ψ) :
    (checkSigSetReady u).path = u.path := by
  unfold checkSigSetReady
  cases hp : u.path <;> repeat (first | rfl | exact hp | split)

private theorem checkSigSetReady_label (u : AgentState ψ) :
    (checkSigSetReady u).label = u.label := by
  unfold checkSigSetReady
  cases hp : u.path <;> repeat (first | rfl | split)

private theorem checkSigSetReady_bit (u : AgentState ψ) :
    (checkSigSetReady u).bit = u.bit := by
  unfold checkSigSetReady
  cases hp : u.path <;> repeat (first | rfl | split)

private theorem checkSigSetReady_equal_of_equal
    (u : AgentState ψ) (h : u.state = .equal) :
    (checkSigSetReady u).state = .equal := by
  cases hp : u.path <;> simp [checkSigSetReady, hp, h]

private theorem checkSigSetReady_ready_of_inputAt
    (u : AgentState ψ) {pathLabel pathBit : Nat}
    (hp : u.path = .some pathLabel pathBit)
    (h : ReadyInputAt u pathLabel) :
    (checkSigSetReady u).state = .CHECK_ready := by
  rcases h with hs | hg
  · simp [checkSigSetReady, hp, hs]
  · rcases hg with ⟨hl, hd, he, hg, hs⟩
    simp [checkSigSetReady, hp, hl, hd, he, hg, hs]

private theorem checkSigCheckR_label
    (hψ : 0 < ψ) (l r : AgentState ψ) :
    (checkSigCheckR hψ l r).label = r.label := by
  unfold checkSigCheckR
  cases hp : r.path <;> repeat (first | rfl | split)

private theorem checkSigCheckR_equal_of_equal
    (hψ : 0 < ψ) (l r : AgentState ψ)
    (hr : r.state = .equal) :
    (checkSigCheckR hψ l r).state = .equal := by
  cases hp : r.path <;> simp [checkSigCheckR, hp, hr]

private theorem checkSigSetResult_label (u : AgentState ψ) :
    (checkSigSetResult u).label = u.label := by
  unfold checkSigSetResult
  split <;> dsimp only <;> split <;> rfl

private theorem checkSigSetResult_state (u : AgentState ψ) :
    (checkSigSetResult u).state = u.state := by
  unfold checkSigSetResult
  split <;> dsimp only <;> split <;> rfl

/-- The input-only predicate is not merely necessary: it is
    sufficient for the literal raw Algorithm-11 responder assignment. -/
theorem checkSig_follower_birth_of_input
    (hψ : 0 < ψ) (l r : AgentState ψ)
    (h : CheckFollowerBirthInput hψ l r) :
    (checkSig hψ l r).2.leader = true := by
  rcases h with ⟨_hold, hterminal, hsource⟩

  let l0 := checkSigSetReady l
  let r0 := checkSigSetReady r
  let l1 := checkSigCheckL hψ l0
  let r1 := checkSigCheckR hψ l1 r0
  let r2 := checkSigSetResult r1

  have hr1Equal : r1.state = .equal := by
    rcases hsource with hstale |
      ⟨pathLabel, pathBit, hpath, hready,
        hleftLabel, hleftEqual, hbit⟩
    · have hr0Equal : r0.state = .equal := by
        change (checkSigSetReady r).state = .equal
        exact checkSigSetReady_equal_of_equal r hstale
      change (checkSigCheckR hψ l1 r0).state = .equal
      exact checkSigCheckR_equal_of_equal hψ l1 r0 hr0Equal
    · have hr0Ready : r0.state = .CHECK_ready := by
        change (checkSigSetReady r).state = .CHECK_ready
        exact checkSigSetReady_ready_of_inputAt r hpath hready
      have hr0Path : r0.path = .some pathLabel pathBit := by
        change (checkSigSetReady r).path = .some pathLabel pathBit
        exact (checkSigSetReady_path r).trans hpath
      have hr0Bit : r0.bit = r.bit := by
        change (checkSigSetReady r).bit = r.bit
        exact checkSigSetReady_bit r
      change l1.label.val < ψ - 1 at hleftLabel
      change l1.state = .equal at hleftEqual
      have hleft : l1.label.val < ψ - 1 ∧ l1.state = .equal :=
        ⟨hleftLabel, hleftEqual⟩
      change (checkSigCheckR hψ l1 r0).state = .equal
      unfold checkSigCheckR
      rw [hr0Path]
      dsimp only
      rw [if_pos hleft, if_pos hr0Ready]
      change checkBit r0.bit pathBit = .equal
      rw [hr0Bit]
      exact hbit

  have hr0Label : r0.label = r.label := by
    change (checkSigSetReady r).label = r.label
    exact checkSigSetReady_label r
  have hr1Label : r1.label = r0.label := by
    change (checkSigCheckR hψ l1 r0).label = r0.label
    exact checkSigCheckR_label hψ l1 r0
  have hr2Label : r2.label = r1.label := by
    change (checkSigSetResult r1).label = r1.label
    exact checkSigSetResult_label r1
  have hr2State : r2.state = .equal :=
    (checkSigSetResult_state r1).trans hr1Equal
  have hr2Terminal : r2.label = ⟨ψ - 1, by omega⟩ :=
    hr2Label.trans (hr1Label.trans (hr0Label.trans hterminal))

  rw [checkSig_eq_staged]
  change (checkSigSetLeader hψ r2).leader = true
  simp [checkSigSetLeader, hr2Terminal, hr2State]

/-- Authorization reconciliation leaves the raw CHECK core unchanged, so the
    same positive predicate suffices at the authorized cut. -/
theorem authorizedCheckSig_follower_birth_of_input
    (hψ : 0 < ψ) (l r : AuthorizedAgentState ψ)
    (h : CheckFollowerBirthInput hψ l.core r.core) :
    (authorizedCheckSig hψ l r).2.core.leader = true := by
  change (checkSig hψ l.core r.core).2.leader = true
  exact checkSig_follower_birth_of_input hψ l.core r.core h

/-- Together with the already accepted necessity theorem, the raw responder
    birth condition is exact. -/
theorem checkSig_follower_birth_iff_input
    (hψ : 0 < ψ) (l r : AgentState ψ)
    (hold : r.leader = false) :
    (checkSig hψ l r).2.leader = true ↔
      CheckFollowerBirthInput hψ l r := by
  constructor
  · intro hout
    exact checkSig_follower_birth_input hψ l r hold hout
  · intro hin
    exact checkSig_follower_birth_of_input hψ l r hin

/-! ## Guarded CHECK sufficiency -/

/-- The six existing DONE/TOSS/CONGEST guards plus the input-only raw kernel
    condition suffice for the accepted `ActualCheckBirth` predicate. -/
theorem actualCheckBirth_of_input
    (hψ : 0 < ψ)
    (b : AuthorizedAgentState ψ × AuthorizedAgentState ψ)
    (h : ActualCheckBirthInput hψ b) : ActualCheckBirth hψ b := by
  rcases h with ⟨hdl, hdr, htl, htr, hcl, hcr, hk⟩
  have hout := authorizedCheckSig_follower_birth_of_input
    hψ b.1 b.2 hk
  exact ⟨hdl, hdr, htl, htr, hcl, hcr, hk.1, hout⟩

/-- Necessity plus the positive direction above gives an exact
    characterization of the guarded CHECK birth cut. -/
theorem actualCheckBirth_iff_input
    (hψ : 0 < ψ)
    (b : AuthorizedAgentState ψ × AuthorizedAgentState ψ) :
    ActualCheckBirth hψ b ↔ ActualCheckBirthInput hψ b := by
  constructor
  · exact actualCheckBirth_to_input hψ b
  · exact actualCheckBirth_of_input hψ b

/-- Under `ActualCheckBirthInput`, the actual DONE/TOSS/CONGEST CHECK wrapper
    reduces exactly to `authorizedCheckSig`; no wrapper is silently skipped. -/
private theorem preserveDoneCheck_eq_authorizedCheck_of_input
    (hψ : 0 < ψ)
    (b : AuthorizedAgentState ψ × AuthorizedAgentState ψ)
    (h : ActualCheckBirthInput hψ b) :
    preserveDoneCheck hψ b.1 b.2 = authorizedCheckSig hψ b.1 b.2 := by
  rcases h with ⟨hdl, hdr, htl, htr, hcl, hcr, _hk⟩
  calc
    preserveDoneCheck hψ b.1 b.2 = preserveTossCheck hψ b.1 b.2 :=
      preserveDoneCheck_of_no_done hψ b.1 b.2 hdl hdr
    _ = congestGuardCheck hψ b.1 b.2 :=
      preserveTossCheck_of_no_toss hψ b.1 b.2 htl htr
    _ = authorizedCheckSig hψ b.1 b.2 :=
      congestGuardCheck_of_clear hψ b.1 b.2 hcl hcr

/-- Positive Boolean form at the exact guarded CHECK cut. -/
theorem checkBirth_true_of_input
    (hψ : 0 < ψ)
    (b : AuthorizedAgentState ψ × AuthorizedAgentState ψ)
    (h : ActualCheckBirthInput hψ b) :
    checkBirth hψ b = true := by
  have ha := actualCheckBirth_of_input hψ b h
  rcases ha with ⟨_hdl, _hdr, _htl, _htr, _hcl, _hcr, hf, hout⟩
  have heq := preserveDoneCheck_eq_authorizedCheck_of_input hψ b h
  unfold checkBirth
  dsimp only
  rw [heq]
  unfold authBirth endpointLeaderBorn
  simp [hf, hout]

/-! ## Actual prepared ordinary Host -> birthEvent -/

private theorem right_leader_eq_of_authSignalPair
    {q p : AuthorizedAgentState ψ × AuthorizedAgentState ψ}
    (h : authSignalPair q = authSignalPair p) :
    q.2.core.leader = p.2.core.leader :=
  congrArg (fun z : AgentState 1 × AgentState 1 => z.2.leader) h

private theorem normalizeDeletion_leader_eq_local
    (u : AuthorizedAgentState ψ) :
    (normalizeDeletion u).core.leader = u.core.leader := by
  unfold normalizeDeletion
  split <;> rfl

/-- The exact `doneThroughCheckEntryWidth` output carries the responder birth
    produced by `ActualCheckBirthInput`. -/
private theorem doneThroughCheckEntryWidth_right_leader_of_input
    (hψ : 0 < ψ) (hwidth : 0 < width) (hle : width ≤ ψ)
    (κ : Nat) (l r : AuthorizedAgentState ψ)
    (h : ActualCheckBirthInput hψ
      (doneBeforeCheckEntryWidth hψ hwidth hle κ l r)) :
    (doneThroughCheckEntryWidth hψ hwidth hle κ l r).2.core.leader = true := by
  unfold doneThroughCheckEntryWidth
  generalize doneBeforeCheckEntryWidth hψ hwidth hle κ l r = b at h ⊢
  have ha := actualCheckBirth_of_input hψ b h
  rcases ha with ⟨_hdl, _hdr, _htl, _htr, _hcl, _hcr, _hf, hout⟩
  have heq := preserveDoneCheck_eq_authorizedCheck_of_input hψ b h
  change (preserveDoneCheck hψ b.1 b.2).2.core.leader = true
  rw [heq]
  exact hout

/-- Stationary WRITE and `markLeaderBirth` frame the responder leader produced
    at the actual through-CHECK cut. -/
private theorem doneOrdinaryMetadataEntryWidth_right_leader_of_input
    (hψ : 0 < ψ) (hwidth : 0 < width) (hle : width ≤ ψ)
    (κ : Nat) (l r : AuthorizedAgentState ψ)
    (h : ActualCheckBirthInput hψ
      (doneBeforeCheckEntryWidth hψ hwidth hle κ l r)) :
    (BirthShortDoneTerminalHost.doneOrdinaryMetadataEntryWidth
      hψ hwidth hle κ l r).2.core.leader = true := by
  have hc := doneThroughCheckEntryWidth_right_leader_of_input
    hψ hwidth hle κ l r h
  have hs :
      authSignalPair
          (BirthShortDoneTerminalHost.doneOrdinaryMetadataEntryWidth
            hψ hwidth hle κ l r) =
        authSignalPair
          (doneThroughCheckEntryWidth hψ hwidth hle κ l r) := by
    unfold BirthShortDoneTerminalHost.doneOrdinaryMetadataEntryWidth
    dsimp only
    generalize doneThroughCheckEntryWidth hψ hwidth hle κ l r = c
    have hq := afterCheckMetadataWidth_signal hψ hwidth hle c.1 c.2
    generalize afterCheckMetadataWidth hψ hwidth hle c.1 c.2 = q at hq ⊢
    exact (markBirth_signal (authBirth l r q) q).trans hq
  exact (right_leader_eq_of_authSignalPair hs).trans hc

/-- **Bounded positive Host interface.**

    The two deletion premises are the literal prepared/normalized priority
    guards used by `doneMetadataAuthorizedEntryWidth`.  The CHECK predicate is
    evaluated on the actual sanitized `doneBeforeCheckEntryWidth` cut.  The
    sole old-leader premise is the normalized prepared responder being a
    follower; no final metadata, expiry, normalization, newborn, or physical
    output field is assumed. -/
theorem birthEvent_true_of_prepared_ordinary_check_input
    (hψ : 0 < ψ) (hwidth : 0 < width) (hle : width ≤ ψ)
    (l r : ExpiringAgentState ψ κ τ)
    (hrDeletion :
      deletionActive
        (normalizeDeletion
          (prepareExpiringDisposal hψ r).core.erase) = false)
    (hlDeletion :
      deletionActive
        (normalizeDeletion
          (prepareExpiringDisposal hψ l).core.erase) = false)
    (hrFollower :
      (normalizeDeletion
        (prepareExpiringDisposal hψ r).core.erase).core.leader = false)
    (hcheck :
      ActualCheckBirthInput hψ
        (doneBeforeCheckEntryWidth hψ hwidth hle κ
          (normalizeDeletion
            (prepareExpiringDisposal hψ l).core.erase)
          (normalizeDeletion
            (prepareExpiringDisposal hψ r).core.erase))) :
    BirthShortDoneTerminalObserver.birthEvent
      hψ hwidth hle l r = true := by
  let pl := prepareExpiringDisposal hψ l
  let pr := prepareExpiringDisposal hψ r
  let l0 := normalizeDeletion pl.core.erase
  let r0 := normalizeDeletion pr.core.erase

  change deletionActive r0 = false at hrDeletion
  change deletionActive l0 = false at hlDeletion
  change r0.core.leader = false at hrFollower
  change ActualCheckBirthInput hψ
    (doneBeforeCheckEntryWidth hψ hwidth hle κ l0 r0) at hcheck

  have hordinary :=
    doneOrdinaryMetadataEntryWidth_right_leader_of_input
      hψ hwidth hle κ l0 r0 hcheck

  have hbranch :
      BirthShortDoneTerminalHost.doneMetadataAuthorizedEntryWidth
          hψ hwidth hle κ pl.core.erase pr.core.erase =
        BirthShortDoneTerminalHost.doneOrdinaryMetadataEntryWidth
          hψ hwidth hle κ l0 r0 := by
    unfold BirthShortDoneTerminalHost.doneMetadataAuthorizedEntryWidth
    change
      (if deletionActive r0 then authorizedEliminateSig hψ l0 r0
       else if deletionActive l0 then (l0, r0)
       else BirthShortDoneTerminalHost.doneOrdinaryMetadataEntryWidth
          hψ hwidth hle κ l0 r0) =
        BirthShortDoneTerminalHost.doneOrdinaryMetadataEntryWidth
          hψ hwidth hle κ l0 r0
    simp only [hrDeletion, hlDeletion, Bool.false_eq_true, if_false]

  have hpreparedFollower : pr.core.erase.core.leader = false :=
    (normalizeDeletion_leader_eq_local pr.core.erase).symm.trans hrFollower

  rw [BirthShortDoneTerminalBirthSources.birthEvent_eq_authorized
    hψ hwidth hle l r]
  change authBirth pl.core.erase pr.core.erase
    (BirthShortDoneTerminalHost.doneMetadataAuthorizedEntryWidth
      hψ hwidth hle κ pl.core.erase pr.core.erase) = true
  rw [hbranch]
  unfold authBirth endpointLeaderBorn
  simp [hpreparedFollower, hordinary]

/-- The accepted physical-tail theorem immediately turns the positive Host
    event above into a real surviving physical leader.  No timer condition is
    added. -/
theorem physical_leader_of_prepared_ordinary_check_input
    (hψ : 0 < ψ) (hwidth : 0 < width) (hle : width ≤ ψ)
    (l r : ExpiringAgentState ψ κ τ)
    (hrDeletion :
      deletionActive
        (normalizeDeletion
          (prepareExpiringDisposal hψ r).core.erase) = false)
    (hlDeletion :
      deletionActive
        (normalizeDeletion
          (prepareExpiringDisposal hψ l).core.erase) = false)
    (hrFollower :
      (normalizeDeletion
        (prepareExpiringDisposal hψ r).core.erase).core.leader = false)
    (hcheck :
      ActualCheckBirthInput hψ
        (doneBeforeCheckEntryWidth hψ hwidth hle κ
          (normalizeDeletion
            (prepareExpiringDisposal hψ l).core.erase)
          (normalizeDeletion
            (prepareExpiringDisposal hψ r).core.erase))) :
    (BirthShortDoneTerminalHost.row hψ hwidth hle l r).1.core.core.leader = true ∨
      (BirthShortDoneTerminalHost.row hψ hwidth hle l r).2.core.core.leader = true := by
  exact
    BirthShortDoneTerminalBirthPhysical.birthEvent_true_row_has_physical_leader
      hψ hwidth hle l r
        (birthEvent_true_of_prepared_ordinary_check_input
          hψ hwidth hle l r
          hrDeletion hlDeletion hrFollower hcheck)

#print axioms BirthShortDoneTerminalCheckInputSufficiency.checkSig_follower_birth_of_input
#print axioms BirthShortDoneTerminalCheckInputSufficiency.authorizedCheckSig_follower_birth_of_input
#print axioms BirthShortDoneTerminalCheckInputSufficiency.checkSig_follower_birth_iff_input
#print axioms BirthShortDoneTerminalCheckInputSufficiency.actualCheckBirth_of_input
#print axioms BirthShortDoneTerminalCheckInputSufficiency.actualCheckBirth_iff_input
#print axioms BirthShortDoneTerminalCheckInputSufficiency.checkBirth_true_of_input
#print axioms BirthShortDoneTerminalCheckInputSufficiency.birthEvent_true_of_prepared_ordinary_check_input
#print axioms BirthShortDoneTerminalCheckInputSufficiency.physical_leader_of_prepared_ordinary_check_input

end BirthShortDoneTerminalCheckInputSufficiency
