import Leader.Wu.Birth.CheckChainActionSixRow

set_option autoImplicit false

/-! # The action-6 signal reaches label 0: the toss row on the actual R1 row

On the edge (label 0, label 1) of an aligned train, with an `equal` follower at label 0 (no path2, crossing permit
already consumed) and a follower at label 1 in `equal` or `less` holding the action-6 signal: the R1 row moves the
signal to label 0, which enters `toss` (keeping the signal, ERRATA T29); CHECK is skipped in this row
(`preserveTossCheck`), so the label-1 cell keeps its state without a signal; DISAPPEAR advances the lottery counter
(p bits, not tracked here) without touching the chain fields (`r1_toss_row`).  Supporting facts: a consumed crossing
permit stays consumed through every stage up to CHECK (`doneThroughCheck_left_permit`), the DONE move and CHECK cut
of the pair (`doneCaptureSigMove_toss_eq`, `doneThroughCheck_toss`), DISAPPEAR and COMPARE with a tossing initiator
(`disappear_keeps_view_toss`, `compare_keeps_toss`, `afterCheck_keeps_toss`).
-/

namespace BirthCheckChainR1

open PPLL PPLLResearchFormulation PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
  PPLLLeaderCreationCleanupRepair BirthGenerationDone BirthShortDoneTerminalEntryCut

variable {ψ : Nat}

/-! ## A consumed crossing permit stays consumed up to CHECK -/

theorem reconcilePermit_false (old : AuthorizedAgentState ψ) (out : AgentState ψ) (h : old.path0Crossed = false) :
    reconcilePermit old out = false := by
  unfold reconcilePermit normalizePermit
  rw [h]
  split
  · split <;> rfl
  · rfl

theorem reconcile_left_permit (f : AgentState ψ → AgentState ψ → AgentState ψ × AgentState ψ)
    (l r : AuthorizedAgentState ψ) (h : l.path0Crossed = false) :
    (authorizedReconcile f l r).1.path0Crossed = false :=
  reconcilePermit_false l _ h

theorem pPsiWall_left_permit (hψ : 0 < ψ) (l r : AuthorizedAgentState ψ) (h : l.path0Crossed = false) :
    (PPLLWallSweepFinite.authorizedPPsiLeaderResetProbeWall hψ l r).1.path0Crossed = false := by
  unfold PPLLWallSweepFinite.authorizedPPsiLeaderResetProbeWall
  dsimp only
  split
  · exact reconcilePermit_false l _ h
  · rfl

theorem generation_left_permit {width κ : Nat} (hψ : 0 < ψ) (hwidth : 0 < width) (hle : width ≤ ψ)
    (l r : AuthorizedAgentState ψ) (h : l.path0Crossed = false) :
    (generationBeforeMoveEntryWidth hψ hwidth hle κ l r).1.path0Crossed = false := by
  have h0 := pPsiWall_left_permit hψ l r h
  have h1 := reconcile_left_permit (BirthShortDoneTerminalEntryCut.genCleanEntryWidth hψ hwidth hle κ) _
    (PPLLWallSweepFinite.authorizedPPsiLeaderResetProbeWall hψ l r).2 h0
  have h2 := reconcile_left_permit (cleanSig hψ) _
    (authorizedGenCleanEntryWidth hψ hwidth hle κ (PPLLWallSweepFinite.authorizedPPsiLeaderResetProbeWall hψ l r).1
      (PPLLWallSweepFinite.authorizedPPsiLeaderResetProbeWall hψ l r).2).2 h1
  exact reconcile_left_permit (eliminateSig hψ) _ _ h2

theorem doneMove_left_permit (hψ : 0 < ψ) (l r : AuthorizedAgentState ψ) (h : l.path0Crossed = false) :
    (authorizedDoneMove hψ l r).1.path0Crossed = false := by
  unfold authorizedDoneMove
  dsimp only
  split
  · rfl
  · exact reconcilePermit_false l _ h

theorem doneThroughCheck_left_permit {width κ : Nat} (hψ : 0 < ψ) (hwidth : 0 < width) (hle : width ≤ ψ)
    (l r : AuthorizedAgentState ψ) (h : l.path0Crossed = false) :
    (doneThroughCheckEntryWidth hψ hwidth hle κ l r).1.path0Crossed = false := by
  have hg := generation_left_permit (κ := κ) hψ hwidth hle l r h
  have hm := doneMove_left_permit hψ _ (generationBeforeMoveEntryWidth hψ hwidth hle κ l r).2 hg
  have hc : doneThroughCheckEntryWidth hψ hwidth hle κ l r =
      preserveDoneCheck hψ (doneBeforeCheckEntryWidth hψ hwidth hle κ l r).1
        (doneBeforeCheckEntryWidth hψ hwidth hle κ l r).2 := rfl
  have hd : doneBeforeCheckEntryWidth hψ hwidth hle κ l r =
      PPLLTerminalEqualSupportRepair.sanitizeAuthorizedPair hψ (PPLLWallSweepPreCheckResetRepair.preCheckResetWall
        (authorizedDoneMove hψ (generationBeforeMoveEntryWidth hψ hwidth hle κ l r).1
          (generationBeforeMoveEntryWidth hψ hwidth hle κ l r).2).1
        (authorizedDoneMove hψ (generationBeforeMoveEntryWidth hψ hwidth hle κ l r).1
          (generationBeforeMoveEntryWidth hψ hwidth hle κ l r).2).2) := rfl
  rw [hc, hd]
  generalize authorizedDoneMove hψ (generationBeforeMoveEntryWidth hψ hwidth hle κ l r).1
    (generationBeforeMoveEntryWidth hψ hwidth hle κ l r).2 = m at hm ⊢
  have hw : (PPLLWallSweepPreCheckResetRepair.preCheckResetWall m.1 m.2).1.path0Crossed = false := by
    unfold PPLLWallSweepPreCheckResetRepair.preCheckResetWall
    dsimp only
    split
    · rfl
    · exact hm
  generalize PPLLWallSweepPreCheckResetRepair.preCheckResetWall m.1 m.2 = w at hw ⊢
  have hs : (PPLLTerminalEqualSupportRepair.sanitizeAuthorizedPair hψ w).1.path0Crossed = false := by
    unfold PPLLTerminalEqualSupportRepair.sanitizeAuthorizedPair
      PPLLTerminalEqualSupportRepair.sanitizeAuthorizedTerminalEqual
    dsimp only
    split
    · rfl
    · exact hw
  generalize PPLLTerminalEqualSupportRepair.sanitizeAuthorizedPair hψ w = d at hs ⊢
  unfold preserveDoneCheck BirthTossCheckPreservationRepair.preserveTossCheck
    BirthCheckCongestGuardRepair.congestGuardCheck authorizedCheckSig
  split
  · exact hs
  · split
    · exact hs
    · split
      · exact hs
      · exact reconcilePermit_false d.1 _ hs

/-! ## The toss row -/

section Toss

open PPLLWallSweepRepair PPLLWallSweepPreCheckResetRepair PPLLTerminalEqualSupportRepair BirthSigMoveDisposalRepair
  BirthArrivalCaptureRepair BirthSingleUseReleaseRepair

theorem doneCaptureSigMove_toss_eq (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (l r : AgentState ψ) (a b c d : Nat)
    (hlp : l.path = .some a b) (hrp : r.path = .some c d)
    (hll : l.leader = false) (hrl : r.leader = false)
    (hlp2 : l.path2 = none) (hrp2 : r.path2 = some ⟨0, 0, 0, 6⟩)
    (hldn : l.state ≠ .done) (hrdep : r.state ≠ .depart) (hl0 : l.label = ⟨0, hψ⟩) :
    doneCaptureSigMove hψ l r =
      ({ l with path2 := some ⟨0, 0, 0, 6⟩, state := .toss }, { r with path2 := none }) := by
  have hp : sigMoveLeaderPreclear hψ l r = (l, r) := by
    simp [sigMoveLeaderPreclear, incompleteLeftLeaderBoundary, clearIfLeader, hll, hrl]
  have hm : doneTransfers l r = ({ l with path2 := some ⟨0, 0, 0, 6⟩ }, { r with path2 := none }) := by
    simp [doneTransfers, holdDoneStep1, hldn, captureStep1, hlp, hrp, controlTransfers, sigMoveStep2,
      sigMoveStep3, sigMoveStep4, sigMoveStep5, hlp2, hrp2]
  have hw : comparisonLeaderWall { l with path2 := some ⟨0, 0, 0, 6⟩ } { r with path2 := none } =
      ({ l with path2 := some ⟨0, 0, 0, 6⟩ }, { r with path2 := none }) := by
    simp [comparisonLeaderWall, hll, hrl]
  have hne : ¬ (0 = ψ - 1) := by omega
  unfold doneCaptureSigMove
  rw [hp]; dsimp only; rw [hm]; dsimp only; rw [hw]
  simp [singleUseControlTail, singleUseApplyControl, hl0, hrdep, hne]

theorem doneThroughCheck_toss {width κ : Nat} (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (hwidth : 0 < width) (hle : width ≤ ψ)
    (l r : AuthorizedAgentState ψ) (a b c d : Nat)
    (hlp : (generationBeforeMoveEntryWidth hψ hwidth hle κ l r).1.core.path = .some a b)
    (hrp : (generationBeforeMoveEntryWidth hψ hwidth hle κ l r).2.core.path = .some c d)
    (hll : (generationBeforeMoveEntryWidth hψ hwidth hle κ l r).1.core.leader = false)
    (hrl : (generationBeforeMoveEntryWidth hψ hwidth hle κ l r).2.core.leader = false)
    (hlr : (generationBeforeMoveEntryWidth hψ hwidth hle κ l r).1.core.reset_cmd = false)
    (hrr : (generationBeforeMoveEntryWidth hψ hwidth hle κ l r).2.core.reset_cmd = false)
    (hlp2 : (generationBeforeMoveEntryWidth hψ hwidth hle κ l r).1.core.path2 = none)
    (hrp2 : (generationBeforeMoveEntryWidth hψ hwidth hle κ l r).2.core.path2 = some ⟨0, 0, 0, 6⟩)
    (hldn : (generationBeforeMoveEntryWidth hψ hwidth hle κ l r).1.core.state ≠ .done)
    (hrs : (generationBeforeMoveEntryWidth hψ hwidth hle κ l r).2.core.state = .equal ∨
      (generationBeforeMoveEntryWidth hψ hwidth hle κ l r).2.core.state = .less)
    (hl0 : (generationBeforeMoveEntryWidth hψ hwidth hle κ l r).1.core.label = ⟨0, hψ⟩)
    (hrterm : (generationBeforeMoveEntryWidth hψ hwidth hle κ l r).2.core.label ≠ ⟨ψ - 1, by omega⟩) :
    (doneThroughCheckEntryWidth hψ hwidth hle κ l r).1.core =
        { (generationBeforeMoveEntryWidth hψ hwidth hle κ l r).1.core with
          path2 := some ⟨0, 0, 0, 6⟩, state := .toss } ∧
      (doneThroughCheckEntryWidth hψ hwidth hle κ l r).2.core =
        { (generationBeforeMoveEntryWidth hψ hwidth hle κ l r).2.core with path2 := none } := by
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
  have hrdep : B.2.core.state ≠ .depart := by rcases hrs with h | h <;> rw [h] <;> decide
  rw [doneCaptureSigMove_toss_eq hψ h2 B.1.core B.2.core a b c d hlp hrp hll hrl hlp2 hrp2 hldn hrdep hl0] at hmc
  generalize authorizedDoneMove hψ B.1 B.2 = m at hmc
  have hm1 : m.1.core = { B.1.core with path2 := some ⟨0, 0, 0, 6⟩, state := .toss } := congrArg Prod.fst hmc
  have hm2 : m.2.core = { B.2.core with path2 := none } := congrArg Prod.snd hmc
  have hw : preCheckResetWall m.1 m.2 = (m.1, m.2) :=
    preCheckResetWall_eq_of_inactive m.1 m.2 (by rw [hm1]; exact hll) (by rw [hm1]; exact hlr)
      (by rw [hm2]; exact hrr)
  have hs1 : sanitizeAuthorizedTerminalEqual hψ m.1 = m.1 := by
    unfold sanitizeAuthorizedTerminalEqual unsupportedTerminalEqual
    have : m.1.core.state ≠ .equal := by rw [hm1]; simp
    simp [this]
  have hs2 : sanitizeAuthorizedTerminalEqual hψ m.2 = m.2 := by
    unfold sanitizeAuthorizedTerminalEqual unsupportedTerminalEqual
    have : m.2.core.label ≠ ⟨ψ - 1, by omega⟩ ∨ m.2.core.state ≠ .equal := by
      left
      rw [hm2]
      exact hrterm
    rcases this with h | h <;> simp [h]
  rw [hw]
  simp only [sanitizeAuthorizedPair]
  rw [hs1, hs2]
  rw [preserveDoneCheck_of_no_done hψ m.1 m.2 (by rw [hm1]; simp)
      (by rw [hm2]; rcases hrs with h | h <;> rw [h] <;> decide),
    BirthTossCheckPreservationRepair.preserveTossCheck_of_toss hψ m.1 m.2 (Or.inl (by rw [hm1]))]
  exact ⟨hm1, hm2⟩

theorem disappear_keeps_view_toss (hψ : 0 < ψ) (l r : AgentState ψ) (hlt : l.state = .toss)
    (hl0 : l.label = ⟨0, hψ⟩) (hrt : r.state ≠ .toss) (hrterm : r.label ≠ ⟨ψ - 1, by omega⟩) :
    chainView (disappear hψ l r).1 = chainView l ∧ chainView (disappear hψ l r).2 = chainView r := by
  unfold disappear chainView
  by_cases hp : l.p = true <;> by_cases hc : l.p_carry = true <;> by_cases hq : r.p = true <;>
    simp [hlt, hl0, hrt, hp, hc, hq, hrterm]

theorem compare_keeps_toss (hψ : ψ > 0) (l r : AuthorizedAgentState ψ) (a b c d : Nat)
    (hlpath : l.core.path = .some a b) (hrpath : r.core.path = .some c d)
    (hl : l.core.state = .toss) (hr1 : r.core.state ≠ .compare1) (hr2 : r.core.state ≠ .compare2)
    (hlp2 : l.core.path2 = some ⟨0, 0, 0, 6⟩) (hrp2 : r.core.path2 = none)
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
    hl, hr1, hr2, hlp2, hrp2, hlpath]

end Toss

attribute [local irreducible] BirthStationaryWrite.stationaryPersistentRaw

theorem afterCheck_keeps_toss {width : Nat} (hψ : 0 < ψ) (hwidth : 0 < width) (hle : width ≤ ψ)
    (l r : AuthorizedAgentState ψ) (a b c d : Nat)
    (hlpath : l.core.path = .some a b) (hrpath : r.core.path = .some c d)
    (hl : l.core.state = .toss) (hl0 : l.core.label = ⟨0, hψ⟩) (hrt : r.core.state ≠ .toss)
    (hr1 : r.core.state ≠ .compare1) (hr2 : r.core.state ≠ .compare2)
    (hlp2 : l.core.path2 = some ⟨0, 0, 0, 6⟩) (hrp2 : r.core.path2 = none)
    (hperm : l.core.label ≠ ⟨0, hψ⟩ ∨ l.path0Crossed = false)
    (hrterm : r.core.label ≠ ⟨ψ - 1, by omega⟩)
    (hll : l.core.leader = false) (hlr : l.core.reset_cmd = false) (hrr : r.core.reset_cmd = false) :
    let q := BirthShortDoneCuts.afterCheckMetadataWidth hψ hwidth hle l r
    postView q.1.core = postView l.core ∧ postView q.2.core = postView r.core := by
  -- DISAPPEAR
  let q0 := authorizedDisappear hψ l r
  have hd := disappear_keeps_view_toss hψ l.core r.core hl hl0 hrt hrterm
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
  have hc := compare_keeps_toss hψ q0.1 q0.2 a b c d
    (by rw [h0c1, e1.2.1]; exact hlpath) (by rw [h0c2, e2.2.1]; exact hrpath)
    (by rw [h0c1, e1.1]; exact hl) (by rw [h0c2, e2.1]; exact hr1) (by rw [h0c2, e2.1]; exact hr2)
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




theorem ordinary_toss_row (hψ : 0 < ψ) (h3 : 2 < ψ) (κ : Nat) (l r : AuthorizedAgentState ψ) (bl br : Nat)
    (hcons : r.core.label = ⟨(l.core.label.val + 1) % ψ, Nat.mod_lt _ hψ⟩)
    (hll : l.core.leader = false) (hrl : r.core.leader = false)
    (hlp : l.core.path = .some 0 bl) (hlab : l.core.label = ⟨0, hψ⟩)
    (hrp : r.core.path = .some 1 br) (hrlab : r.core.label.val = 1)
    (hleq : l.core.state = .equal) (hlp2 : l.core.path2 = none) (hperm : l.path0Crossed = false)
    (hrs : r.core.state = .equal ∨ r.core.state = .less) (hrp2 : r.core.path2 = some ⟨0, 0, 0, 6⟩)
    (hlr : l.core.reset_cmd = false) (hrr : r.core.reset_cmd = false)
    (hl4 : ∀ p, l.core.path4 = some p → p.1 ≠ -1) (hr5 : ∀ p, r.core.path5 = some p → p.1 ≠ -1) :
    let q := BirthCheckPermitRepair.ordinary hψ (by decide : 0 < 2) (by omega) κ l r
    (q.1.core.state = .toss ∧ q.1.core.path = l.core.path ∧ q.1.core.path2 = some ⟨0, 0, 0, 6⟩ ∧
        q.1.core.label = l.core.label ∧ q.1.core.leader = false) ∧
      (q.2.core.state = r.core.state ∧ q.2.core.path = r.core.path ∧ q.2.core.path2 = none ∧
        q.2.core.label = r.core.label ∧ q.2.core.leader = false) := by
  intro q
  have h2 : 2 ≤ ψ := by omega
  have hrpr : r.core.state ≠ .produce := by rcases hrs with h | h <;> rw [h] <;> decide
  have hrdn : r.core.state ≠ .done := by rcases hrs with h | h <;> rw [h] <;> decide
  have hrel : r.core.state ≠ .eliminate_signal := by rcases hrs with h | h <;> rw [h] <;> decide
  have hrt : r.core.state ≠ .toss := by rcases hrs with h | h <;> rw [h] <;> decide
  have hr1 : r.core.state ≠ .compare1 := by rcases hrs with h | h <;> rw [h] <;> decide
  have hr2 : r.core.state ≠ .compare2 := by rcases hrs with h | h <;> rw [h] <;> decide
  have hg := generation_keeps_chain (κ := κ) hψ (by decide : 0 < 2) h2 l r 0 bl br hcons hll hrl hlp hrp
    (by omega) (by rw [hleq]; decide) (by rw [hleq]; decide) hrpr hrdn hrel (fun _ => hl4) hr5
  have hP := doneThroughCheck_left_permit (κ := κ) hψ (by decide : 0 < 2) h2 l r hperm
  generalize hB : generationBeforeMoveEntryWidth hψ (by decide : 0 < 2) h2 κ l r = B at hg
  have b1 := hg.1; have b2 := hg.2
  unfold genView at b1 b2
  simp only [Prod.mk.injEq] at b1 b2
  obtain ⟨s1, p1, q1, lb1, bt1, ld1, rc1⟩ := b1
  obtain ⟨s2, p2, q2, lb2, bt2, ld2, rc2⟩ := b2
  have hrterm0 : r.core.label ≠ ⟨ψ - 1, by omega⟩ := by
    intro h; have := congrArg Fin.val h; rw [hrlab] at this; simp only at this; omega
  have hcut := doneThroughCheck_toss (κ := κ) hψ h2 (by decide : 0 < 2) h2 l r 0 bl 1 br
    (by rw [hB, p1]; exact hlp) (by rw [hB, p2]; exact hrp) (by rw [hB, ld1]; exact hll) (by rw [hB, ld2]; exact hrl)
    (by rw [hB, rc1]; exact hlr) (by rw [hB, rc2]; exact hrr) (by rw [hB, q1]; exact hlp2) (by rw [hB, q2]; exact hrp2)
    (by rw [hB, s1, hleq]; decide) (by rw [hB, s2]; exact hrs) (by rw [hB, lb1]; exact hlab)
    (by rw [hB, lb2]; exact hrterm0)
  rw [hB] at hcut
  generalize hC : doneThroughCheckEntryWidth hψ (by decide : 0 < 2) h2 κ l r = C at hcut hP
  obtain ⟨hc1, hc2⟩ := hcut
  have c1s : C.1.core.state = .toss := by rw [hc1]
  have c1p : C.1.core.path = l.core.path := by rw [hc1]; exact p1
  have c1q : C.1.core.path2 = some ⟨0, 0, 0, 6⟩ := by rw [hc1]
  have c1lb : C.1.core.label = l.core.label := by rw [hc1]; exact lb1
  have c1ld : C.1.core.leader = false := by rw [hc1]; exact ld1.trans hll
  have c1rc : C.1.core.reset_cmd = false := by rw [hc1]; exact rc1.trans hlr
  have c2s : C.2.core.state = r.core.state := by rw [hc2]; exact s2
  have c2p : C.2.core.path = r.core.path := by rw [hc2]; exact p2
  have c2q : C.2.core.path2 = none := by rw [hc2]
  have c2lb : C.2.core.label = r.core.label := by rw [hc2]; exact lb2
  have c2ld : C.2.core.leader = false := by rw [hc2]; exact ld2.trans hrl
  have c2rc : C.2.core.reset_cmd = false := by rw [hc2]; exact rc2.trans hrr
  have hfix : BirthCheckPermitRepair.permitFix C.1 = C.1 :=
    BirthCheckPermitRepair.permitFix_of_ne C.1 (by rw [c1s]; decide)
  have hac := afterCheck_keeps_toss hψ (by decide : 0 < 2) h2 C.1 C.2 0 bl 1 br
    (by rw [c1p]; exact hlp) (by rw [c2p]; exact hrp) c1s (by rw [c1lb]; exact hlab)
    (by rw [c2s]; exact hrt) (by rw [c2s]; exact hr1) (by rw [c2s]; exact hr2) c1q c2q (Or.inr hP)
    (by rw [c2lb]; exact hrterm0) c1ld c1rc c2rc
  obtain ⟨pv1, pv2⟩ := hac
  generalize hQ : BirthShortDoneCuts.afterCheckMetadataWidth hψ (by decide : 0 < 2) h2 C.1 C.2 = Q at pv1 pv2
  unfold postView at pv1 pv2
  simp only [Prod.mk.injEq] at pv1 pv2
  have hq : q = markLeaderBirth (K2BirthDispatcher.authBirth l r Q) Q := by
    show BirthCheckPermitRepair.ordinary hψ (by decide : 0 < 2) h2 κ l r = _
    unfold BirthCheckPermitRepair.ordinary
    dsimp only
    rw [hC, hfix, hQ]
  have hborn : K2BirthDispatcher.authBirth l r Q = false := by
    unfold K2BirthDispatcher.authBirth endpointLeaderBorn
    rw [pv1.2.2.2.2, pv2.2.2.2.2, c1ld, c2ld]
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

/-- The toss row on the actual R1 row. -/
theorem r1_toss_row (hψ : 0 < ψ) (h3 : 2 < ψ) (l r : ExpiringAgentState ψ κ τ) (bl br : Nat)
    (hcons : r.core.erase.core.label = ⟨(l.core.erase.core.label.val + 1) % ψ, Nat.mod_lt _ hψ⟩)
    (hll : l.core.erase.core.leader = false) (hrl : r.core.erase.core.leader = false)
    (hlp : l.core.erase.core.path = .some 0 bl) (hlab : l.core.erase.core.label = ⟨0, hψ⟩)
    (hrp : r.core.erase.core.path = .some 1 br) (hrlab : r.core.erase.core.label.val = 1)
    (hleq : l.core.erase.core.state = .equal) (hlp2 : l.core.erase.core.path2 = none)
    (hperm : l.core.erase.path0Crossed = false)
    (hrs : r.core.erase.core.state = .equal ∨ r.core.erase.core.state = .less)
    (hrp2 : r.core.erase.core.path2 = some ⟨0, 0, 0, 6⟩)
    (hlr : l.core.erase.core.reset_cmd = false) (hrr : r.core.erase.core.reset_cmd = false)
    (hl4 : ∀ p, l.core.erase.core.path4 = some p → p.1 ≠ -1)
    (hr5 : ∀ p, r.core.erase.core.path5 = some p → p.1 ≠ -1)
    (hlstall : l.stall.val ≠ 0) (hrstall : r.stall.val ≠ 0) :
    let o := BirthCheckPermitRepair.row hψ (by decide : 0 < 2) (by omega) l r
    (o.1.core.erase.core.state = .toss ∧ o.1.core.erase.core.path = l.core.erase.core.path ∧
        o.1.core.erase.core.path2 = some ⟨0, 0, 0, 6⟩ ∧ o.1.core.erase.core.label = l.core.erase.core.label ∧
        o.1.core.erase.core.leader = false) ∧
      (o.2.core.erase.core.state = r.core.erase.core.state ∧ o.2.core.erase.core.path = r.core.erase.core.path ∧
        o.2.core.erase.core.path2 = none ∧ o.2.core.erase.core.label = r.core.erase.core.label ∧
        o.2.core.erase.core.reset_cmd = false ∧ o.2.core.erase.core.leader = false) := by
  intro o
  have h2 : 2 ≤ ψ := by omega
  have hc := BirthCheckChainR1.ordinary_toss_row hψ h3 κ l.core.erase r.core.erase bl br hcons hll hrl hlp hlab
    hrp hrlab hleq hlp2 hperm hrs hrp2 hlr hrr hl4 hr5
  have hlel : l.core.erase.core.state ≠ .eliminate_signal := by rw [hleq]; decide
  have hrel : r.core.erase.core.state ≠ .eliminate_signal := by rcases hrs with h | h <;> rw [h] <;> decide
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
