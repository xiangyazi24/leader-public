import Leader.Wu.Birth.CheckChainTossRow
import Leader.Wu.Birth.CheckChainBackEdge

set_option autoImplicit false

/-! # The lottery ends: the back-edge row of a tossing label-0 cell

A tossing label-0 cell of an aligned train (holding the action-6 signal, ERRATA T29) meets its back neighbour, the
label psi-1 cell of the previous segment, which is empty and quiet (no path, state `none`, no path2, no clean path5,
follower, no reset command).  On the actual R1 row (`r1_backToss_row`): the DONE move pushes the action-6 signal into
the back neighbour (T29 escape into the previous segment), CHECK is skipped (`preserveTossCheck`), and DISAPPEAR ends
the lottery: the label-0 cell becomes `toss_done` holding the action-5 signal, path and label unchanged; the back
neighbour stays empty and quiet apart from the escaped signal.  Pieces: `cleanSig_back_min`,
`generation_keeps_backToss`, `doneCaptureSigMove_backToss_eq`, `doneThroughCheck_backToss`, `disappear_backToss`,
`afterCheck_backToss`, `ordinary_backToss_row`.
-/

namespace BirthCheckChainR1TossDone

open PPLL PPLLResearchFormulation PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
  PPLLLeaderCreationCleanupRepair BirthGenerationDone BirthShortDoneTerminalEntryCut
open BirthCheckChainR1 BirthCheckChainR1Front BirthCheckChainR1Back
open PPLLWallSweepRepair PPLLWallSweepPreCheckResetRepair PPLLTerminalEqualSupportRepair BirthSigMoveDisposalRepair
  BirthArrivalCaptureRepair BirthSingleUseReleaseRepair

set_option Elab.async false

variable {ψ κ τ : Nat}

/-- An empty quiet back neighbour and a tossing label-0 cell holding the action-6 signal. -/
structure BackTossPair (hψ : 0 < ψ) (l r : AgentState ψ) : Prop where
  lPath : l.path = .bot
  lState : l.state = .none
  lPath2 : l.path2 = none
  lPath5 : ∀ p, l.path5 = some p → p.1 ≠ -1
  lLeader : l.leader = false
  lReset : l.reset_cmd = false
  rToss : r.state = .toss
  rPath2 : r.path2 = some ⟨0, 0, 0, 6⟩
  rPath4 : ∀ p, r.path4 = some p → p.1 ≠ -1
  rLeader : r.leader = false
  rReset : r.reset_cmd = false

/-- The fields of a back toss pair read by the DONE move and the CHECK cut (no markers). -/
structure BackTossCut (hψ : 0 < ψ) (l r : AgentState ψ) : Prop where
  lPath : l.path = .bot
  lState : l.state = .none
  lPath2 : l.path2 = none
  lLeader : l.leader = false
  lReset : l.reset_cmd = false
  rToss : r.state = .toss
  rPath2 : r.path2 = some ⟨0, 0, 0, 6⟩
  rLeader : r.leader = false
  rReset : r.reset_cmd = false

theorem cleanSig_back_min (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (l r : AgentState ψ) (c : Nat)
    (hrp : r.path = .some 0 c) (hlp : l.path = .bot)
    (hl5 : ∀ p, l.path5 = some p → p.1 ≠ -1) :
    genPair (cleanSig hψ l r) = genPair (l, r) := by
  have hψ1 : (0 : Nat) ≠ ψ - 1 := by omega
  have hl1 : cleanSigGenConnect l = l := by simp [cleanSigGenConnect, hlp]
  have hr1p : (cleanSigGenConnect r).path = .some 0 c := by simp [cleanSigGenConnect, hrp]
  have hr14 : (cleanSigGenConnect r).path4 = r.path4 := by simp [cleanSigGenConnect, hrp]
  have hr15 : (cleanSigGenConnect r).path5 = some (Int.ofNat 0, 1) := by simp [cleanSigGenConnect, hrp, hψ1]
  have hrv : genView (cleanSigGenConnect r) = genView r := genConnect_genView r
  generalize hR : cleanSigGenConnect r = R at *
  -- step 3: the initiator has no path
  have hq3 : cleanSigStep3 l R = (l, R) := by unfold cleanSigStep3; cases R.path4 <;> simp [hlp]
  -- step 4: a non-clean initiator path5 is consumed (the initiator may receive a clean path4, harmless on an empty
  -- cell); a clean initiator path5 is excluded
  obtain ⟨L4, hq4, hL4p, hL4v, hL45⟩ : ∃ L4 : AgentState ψ, cleanSigStep4 l R = (L4, R) ∧ L4.path = .bot ∧
      genView L4 = genView l ∧ L4.path5 = none := by
    cases h5 : l.path5 with
    | none =>
        refine ⟨l, ?_, hlp, rfl, h5⟩
        unfold cleanSigStep4; rw [h5]
    | some p =>
        have hp1 := hl5 p h5
        obtain ⟨p1, p2⟩ := p
        refine ⟨if p1 ≠ Int.ofNat 0 - 1 then { { l with path4 := some ((-1 : Int), 1 - p2) } with path5 := none }
          else { l with path5 := none }, ?_, ?_, ?_, ?_⟩
        · unfold cleanSigStep4; rw [h5, hr1p]; simp only [ne_eq, hp1, not_false_eq_true, if_true]
          split <;> rfl
        · split <;> simp [hlp]
        · split <;> rfl
        · split <;> rfl
  -- step 5: the responder path4 (non-clean) moves into the empty initiator
  obtain ⟨L5, R5, hq5, hL5p, hL5v, hL55, hR5v, hR54⟩ : ∃ L5 R5 : AgentState ψ, cleanSigStep5 hψ L4 R = (L5, R5) ∧
      L5.path = .bot ∧ genView L5 = genView L4 ∧ L5.path5 = none ∧ genView R5 = genView R ∧ R5.path4 = none := by
    unfold cleanSigStep5
    split
    · split
      · split
        · exact ⟨_, _, rfl, hL4p, rfl, hL45, rfl, rfl⟩
        · exact ⟨_, _, rfl, hL4p, rfl, hL45, rfl, rfl⟩
      · exact ⟨_, _, rfl, hL4p, rfl, hL45, rfl, rfl⟩
    · rename_i hn
      exact ⟨_, _, rfl, hL4p, rfl, hL45, rfl, hn⟩
  -- step 6: the initiator path5 is empty
  have hq6 : cleanSigStep6 hψ L5 R5 = (L5, R5) := by unfold cleanSigStep6; rw [hL55]
  have hR55 : R5.path5 = some (Int.ofNat 0, 1) := by
    have e := congrArg Prod.snd hq5
    simp only at e
    unfold cleanSigStep5 at e
    revert e
    split
    · split
      · split <;> (intro e; rw [← e]; exact hr15)
      · intro e; rw [← e]; exact hr15
    · intro e; rw [← e]; exact hr15
  have hal : genView (cleanSigCleanApply L5) = genView l := by
    have e : cleanSigCleanApply L5 = L5 := by unfold cleanSigCleanApply; rw [hL5p]
    rw [e]; exact hL5v.trans hL4v
  have har : genView (cleanSigCleanApply R5) = genView r := by
    rw [cleanApply_genView R5 (fun p hp => by rw [hR54] at hp; cases hp)
      (fun p hp => by rw [hR55] at hp; cases hp; exact ofNat_ne_neg_one 0)]
    exact hR5v.trans hrv
  unfold cleanSig genPair
  rw [hl1, hR]
  simp only [hq3, hq4, hq5, hq6]
  exact Prod.ext hal har

theorem generation_keeps_backToss {width κ : Nat} (hψ : 0 < ψ) (hwidth : 0 < width) (hle : width ≤ ψ) (h2 : 2 ≤ ψ)
    (l r : AuthorizedAgentState ψ) (b : Nat)
    (hcons : r.core.label = ⟨(l.core.label.val + 1) % ψ, Nat.mod_lt _ hψ⟩)
    (hlterm : l.core.label = ⟨ψ - 1, by omega⟩) (hr0 : r.core.label = ⟨0, hψ⟩)
    (hrp : r.core.path = .some 0 b) (h : BackTossPair hψ l.core r.core) :
    genView (generationBeforeMoveEntryWidth hψ hwidth hle κ l r).1.core = genView l.core ∧
      genView (generationBeforeMoveEntryWidth hψ hwidth hle κ l r).2.core = genView r.core := by
  have hgen : generationBeforeMoveEntryWidth hψ hwidth hle κ l r =
      authorizedEliminateSig hψ
        (authorizedCleanSig hψ
          (authorizedGenCleanEntryWidth hψ hwidth hle κ (PPLLWallSweepFinite.authorizedPPsiLeaderResetProbeWall hψ l r).1
            (PPLLWallSweepFinite.authorizedPPsiLeaderResetProbeWall hψ l r).2).1
          (authorizedGenCleanEntryWidth hψ hwidth hle κ (PPLLWallSweepFinite.authorizedPPsiLeaderResetProbeWall hψ l r).1
            (PPLLWallSweepFinite.authorizedPPsiLeaderResetProbeWall hψ l r).2).2).1
        (authorizedCleanSig hψ
          (authorizedGenCleanEntryWidth hψ hwidth hle κ (PPLLWallSweepFinite.authorizedPPsiLeaderResetProbeWall hψ l r).1
            (PPLLWallSweepFinite.authorizedPPsiLeaderResetProbeWall hψ l r).2).1
          (authorizedGenCleanEntryWidth hψ hwidth hle κ (PPLLWallSweepFinite.authorizedPPsiLeaderResetProbeWall hψ l r).1
            (PPLLWallSweepFinite.authorizedPPsiLeaderResetProbeWall hψ l r).2).2).2 := rfl
  rw [hgen]
  generalize hA0 : PPLLWallSweepFinite.authorizedPPsiLeaderResetProbeWall hψ l r = A0
  have c0 : (A0.1.core, A0.2.core) = PPLLWallSweepRepair.pPsiLeaderResetProbeWall hψ l.core r.core := by
    rw [← hA0]; rfl
  generalize hA1 : authorizedGenCleanEntryWidth hψ hwidth hle κ A0.1 A0.2 = A1
  have c1 : (A1.1.core, A1.2.core) = BirthGenerationControlRepair.genCleanAfterWait hψ
      (BirthShortWaitTerminalEntryRepair.waitWidthEntry hψ hwidth hle κ A0.1.core A0.2.core).1
      (BirthShortWaitTerminalEntryRepair.waitWidthEntry hψ hwidth hle κ A0.1.core A0.2.core).2 := by
    rw [← hA1]; rfl
  generalize hA2 : authorizedCleanSig hψ A1.1 A1.2 = A2
  have c2 : (A2.1.core, A2.2.core) = cleanSig hψ A1.1.core A1.2.core := by rw [← hA2]; rfl
  have c3 : ((authorizedEliminateSig hψ A2.1 A2.2).1.core, (authorizedEliminateSig hψ A2.1 A2.2).2.core) =
      eliminateSig hψ A2.1.core A2.2.core := rfl
  have hw := pPsiWall_keeps_genView hψ l.core r.core hcons h.lLeader h.rLeader
  have hwm := pPsiWall_keeps_markers hψ l.core r.core
  rw [← c0] at hw hwm
  generalize hW : BirthShortWaitTerminalEntryRepair.waitWidthEntry hψ hwidth hle κ A0.1.core A0.2.core = W at c1
  have hwt := genPair_eq_iff.1 (show genPair W = genPair (A0.1.core, A0.2.core) by
    rw [← hW]; exact waitWidthEntry_keeps_genView hψ hwidth hle _ _)
  have hwtm := markerPair_eq_iff.1 (show markerPair W = markerPair (A0.1.core, A0.2.core) by
    rw [← hW]; exact waitWidthEntry_keeps_markers hψ hwidth hle _ _)
  have v1 : genView W.1 = genView l.core := hwt.1.trans hw.1
  have v2 : genView W.2 = genView r.core := hwt.2.trans hw.2
  have m2 : markers W.2 = markers r.core := hwtm.2.trans hwm.2
  have v1' := v1; have v2' := v2
  unfold genView at v1' v2'; unfold markers at m2
  simp only [Prod.mk.injEq] at v1' v2' m2
  have hgenid := genCleanAfterWait_boundary hψ h2 W.1 W.2 (by rw [v1'.2.2.2.1]; exact hlterm)
    (by rw [v2'.2.2.2.1]; exact hr0)
  rw [hgenid] at c1
  obtain ⟨e1, e2⟩ := Prod.mk.inj c1
  have m1 : markers W.1 = markers l.core := hwtm.1.trans hwm.1
  unfold markers at m1
  simp only [Prod.mk.injEq] at m1
  have hc := genPair_eq_iff.1 (cleanSig_back_min hψ h2 A1.1.core A1.2.core b
    (by rw [e2, v2'.2.1]; exact hrp) (by rw [e1, v1'.2.1]; exact h.lPath) (by rw [e1, m1.2]; exact h.lPath5))
  rw [← c2] at hc
  have k1 : genView A2.1.core = genView l.core := hc.1.trans (by rw [e1]; exact v1)
  have k2 : genView A2.2.core = genView r.core := hc.2.trans (by rw [e2]; exact v2)
  have hrc : A2.2.core.state ≠ .eliminate_signal := by
    have := congrArg (fun v => v.1) k2
    simp only [genView] at this
    rw [this, h.rToss]; decide
  have he : eliminateSig hψ A2.1.core A2.2.core = (A2.1.core, A2.2.core) :=
    eliminateSig_of_not_signal hψ A2.1.core A2.2.core hrc
  rw [he] at c3
  obtain ⟨e3a, e3b⟩ := Prod.mk.inj c3
  rw [e3a, e3b]
  exact ⟨k1, k2⟩



theorem doneCaptureSigMove_backToss_eq (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (l r : AgentState ψ) (c : Nat)
    (hrp : r.path = .some 0 c) (hlterm : l.label = ⟨ψ - 1, by omega⟩) (h : BackTossCut hψ l r) :
    doneCaptureSigMove hψ l r = ({ l with path2 := some ⟨0, 0, 0, 6⟩ }, { r with path2 := none }) := by
  have hp : sigMoveLeaderPreclear hψ l r = (l, r) := by
    simp [sigMoveLeaderPreclear, incompleteLeftLeaderBoundary, clearIfLeader, h.lLeader, h.rLeader]
  have hm : doneTransfers l r = ({ l with path2 := some ⟨0, 0, 0, 6⟩ }, { r with path2 := none }) := by
    simp [doneTransfers, holdDoneStep1, h.lState, captureStep1, h.lPath, controlTransfers, sigMoveStep2,
      sigMoveStep3, sigMoveStep4, sigMoveStep5, h.lPath2, h.rPath2]
  have hw : comparisonLeaderWall { l with path2 := some ⟨0, 0, 0, 6⟩ } { r with path2 := none } =
      ({ l with path2 := some ⟨0, 0, 0, 6⟩ }, { r with path2 := none }) := by
    simp [comparisonLeaderWall, h.lLeader, h.rLeader]
  have hl0 : l.label ≠ ⟨0, hψ⟩ := by
    rw [hlterm]; intro hh; have := congrArg Fin.val hh; simp only at this; omega
  have hne : ψ - 1 ≠ 0 := by omega
  unfold doneCaptureSigMove
  rw [hp]; dsimp only; rw [hm]; dsimp only; rw [hw]
  simp [singleUseControlTail, singleUseApplyControl, h.rToss, hlterm, hne]

theorem doneThroughCheck_backToss {width : Nat} (hψ : 0 < ψ) (hwidth : 0 < width) (hle : width ≤ ψ) (h2 : 2 ≤ ψ)
    (l r : AuthorizedAgentState ψ) (c : Nat)
    (hB : let B := generationBeforeMoveEntryWidth hψ hwidth hle κ l r
      BackTossCut hψ B.1.core B.2.core ∧ B.2.core.path = .some 0 c ∧ B.1.core.label = ⟨ψ - 1, by omega⟩ ∧
        B.2.core.label = ⟨0, hψ⟩) :
    (doneThroughCheckEntryWidth hψ hwidth hle κ l r).1.core =
        { (generationBeforeMoveEntryWidth hψ hwidth hle κ l r).1.core with path2 := some ⟨0, 0, 0, 6⟩ } ∧
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
  generalize generationBeforeMoveEntryWidth hψ hwidth hle κ l r = B at hB ⊢
  obtain ⟨hf, hbq, hbl, hbr⟩ := hB
  have hmc := authorizedDoneMove_core hψ B.1 B.2
  rw [doneCaptureSigMove_backToss_eq hψ h2 B.1.core B.2.core c hbq hbl hf] at hmc
  generalize authorizedDoneMove hψ B.1 B.2 = m at hmc
  have hm1 : m.1.core = { B.1.core with path2 := some ⟨0, 0, 0, 6⟩ } := congrArg Prod.fst hmc
  have hm2 : m.2.core = { B.2.core with path2 := none } := congrArg Prod.snd hmc
  have hw : preCheckResetWall m.1 m.2 = (m.1, m.2) :=
    preCheckResetWall_eq_of_inactive m.1 m.2 (by rw [hm1]; exact hf.lLeader) (by rw [hm1]; exact hf.lReset)
      (by rw [hm2]; exact hf.rReset)
  rw [hw]
  have hs1 : sanitizeAuthorizedTerminalEqual hψ m.1 = m.1 := by
    unfold sanitizeAuthorizedTerminalEqual unsupportedTerminalEqual
    have : m.1.core.state ≠ .equal := by rw [hm1]; show B.1.core.state ≠ _; rw [hf.lState]; decide
    simp [this]
  have hs2 : sanitizeAuthorizedTerminalEqual hψ m.2 = m.2 := by
    unfold sanitizeAuthorizedTerminalEqual unsupportedTerminalEqual
    have : m.2.core.state ≠ .equal := by rw [hm2]; show B.2.core.state ≠ _; rw [hf.rToss]; decide
    simp [this]
  simp only [sanitizeAuthorizedPair, hs1, hs2]
  rw [preserveDoneCheck_of_no_done hψ m.1 m.2 (by rw [hm1]; show B.1.core.state ≠ _; rw [hf.lState]; decide)
      (by rw [hm2]; show B.2.core.state ≠ _; rw [hf.rToss]; decide),
    BirthTossCheckPreservationRepair.preserveTossCheck_of_toss hψ m.1 m.2
      (Or.inr (by rw [hm2]; show B.2.core.state = _; exact hf.rToss))]
  exact ⟨hm1, hm2⟩

theorem disappear_backToss (hψ : 0 < ψ) (l r : AgentState ψ) (hls : l.state ≠ .toss) (hrt : r.state = .toss)
    (hr0 : r.label = ⟨0, hψ⟩) (hrterm : r.label ≠ ⟨ψ - 1, by omega⟩) :
    chainView (disappear hψ l r).1 = chainView l ∧
      chainView (disappear hψ l r).2 = chainView { r with state := .toss_done, path2 := some ⟨0, 0, 0, 5⟩ } := by
  have hrterm' : (⟨0, hψ⟩ : Fin ψ) ≠ ⟨ψ - 1, by omega⟩ := by rw [← hr0]; exact hrterm
  unfold disappear chainView
  by_cases hc : l.p_carry = true <;> simp [hrt, hr0, hls, hc, hrterm']

attribute [local irreducible] BirthStationaryWrite.stationaryPersistentRaw

theorem afterCheck_backToss {width : Nat} (hψ : 0 < ψ) (hwidth : 0 < width) (hle : width ≤ ψ) (h2 : 2 ≤ ψ)
    (l r : AuthorizedAgentState ψ) (hlp : l.core.path = .bot) (hls : l.core.state = .none)
    (hll : l.core.leader = false) (hlr : l.core.reset_cmd = false) (hrr : r.core.reset_cmd = false)
    (hrt : r.core.state = .toss) (hr0 : r.core.label = ⟨0, hψ⟩) :
    let q := BirthShortDoneCuts.afterCheckMetadataWidth hψ hwidth hle l r
    postView q.1.core = postView l.core ∧
      postView q.2.core = postView { r.core with state := .toss_done, path2 := some ⟨0, 0, 0, 5⟩ } := by
  have hrterm : r.core.label ≠ ⟨ψ - 1, by omega⟩ := by
    intro hh; rw [hr0] at hh; have := congrArg Fin.val hh; simp only at this; omega
  let q0 := authorizedDisappear hψ l r
  have hd := disappear_backToss hψ l.core r.core (by rw [hls]; decide) hrt hr0 hrterm
  have hdr := disappear_reset_cmd hψ l.core r.core
  have h0c1 : q0.1.core = (disappear hψ l.core r.core).1 := rfl
  have h0c2 : q0.2.core = (disappear hψ l.core r.core).2 := rfl
  have e1 := hd.1; have e2 := hd.2
  unfold chainView at e1 e2
  simp only [Prod.mk.injEq] at e1 e2
  have hc := compare_back_empty hψ q0.1 q0.2 (by rw [h0c1, e1.2.1]; exact hlp) (by rw [h0c1, e1.1]; exact hls)
  let q1 := PPLLCompleteMultiLeaderCleanup.authorizedCompareSigActionOne hψ q0.1 q0.2
  have hq1a : q1.1.core = q0.1.core := hc.1
  have hq1b : q1.2.core = q0.2.core := hc.2
  have hs := suppress_keeps_view hψ hwidth hle q1.1.core q1.2.core
    (by rw [hq1a, h0c1, e1.2.2.2.2.2]; exact hll) (by rw [hq1a, h0c1, hdr.1]; exact hlr)
    (by rw [hq1b, h0c2, hdr.2]; exact hrr)
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
  have hd2 : postView q0.2.core = postView { r.core with state := .toss_done, path2 := some ⟨0, 0, 0, 5⟩ } := by
    rw [h0c2]; exact postView_of_chainView hd.2
  rw [hfin]
  exact ⟨hw1.trans (hs1.trans (by rw [hq1a]; exact hd1)), hw2.trans (hs2.trans (by rw [hq1b]; exact hd2))⟩


theorem ordinary_backToss_row (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (κ : Nat) (l r : AuthorizedAgentState ψ) (c : Nat)
    (hcons : r.core.label = ⟨(l.core.label.val + 1) % ψ, Nat.mod_lt _ hψ⟩)
    (hlterm : l.core.label = ⟨ψ - 1, by omega⟩) (hr0 : r.core.label = ⟨0, hψ⟩)
    (hrp : r.core.path = .some 0 c) (hf : BackTossPair hψ l.core r.core) :
    let q := BirthCheckPermitRepair.ordinary hψ (by decide : 0 < 2) h2 κ l r
    (q.1.core.state = .none ∧ q.1.core.path = .bot ∧ q.1.core.path2 = some ⟨0, 0, 0, 6⟩ ∧
        q.1.core.label = l.core.label ∧ q.1.core.leader = false) ∧
      (q.2.core.state = .toss_done ∧ q.2.core.path = r.core.path ∧ q.2.core.path2 = some ⟨0, 0, 0, 5⟩ ∧
        q.2.core.label = r.core.label ∧ q.2.core.leader = false) := by
  intro q
  have hg := generation_keeps_backToss (κ := κ) hψ (by decide : 0 < 2) h2 h2 l r c hcons hlterm hr0 hrp hf
  generalize hB : generationBeforeMoveEntryWidth hψ (by decide : 0 < 2) h2 κ l r = B at hg
  have b1 := hg.1; have b2 := hg.2
  unfold genView at b1 b2
  simp only [Prod.mk.injEq] at b1 b2
  obtain ⟨s1, p1, q1, lb1, bt1, ld1, rc1⟩ := b1
  obtain ⟨s2, p2, q2, lb2, bt2, ld2, rc2⟩ := b2
  have hcut := doneThroughCheck_backToss (κ := κ) hψ (by decide : 0 < 2) h2 h2 l r c
    (by
      rw [hB]
      exact ⟨⟨by rw [p1]; exact hf.lPath, by rw [s1]; exact hf.lState, by rw [q1]; exact hf.lPath2,
        by rw [ld1]; exact hf.lLeader, by rw [rc1]; exact hf.lReset, by rw [s2]; exact hf.rToss,
        by rw [q2]; exact hf.rPath2, by rw [ld2]; exact hf.rLeader, by rw [rc2]; exact hf.rReset⟩,
        by rw [p2]; exact hrp, by rw [lb1]; exact hlterm, by rw [lb2]; exact hr0⟩)
  rw [hB] at hcut
  generalize hC : doneThroughCheckEntryWidth hψ (by decide : 0 < 2) h2 κ l r = C at hcut
  obtain ⟨hc1, hc2⟩ := hcut
  have c1s : C.1.core.state = .none := by rw [hc1]; exact s1.trans hf.lState
  have c1p : C.1.core.path = .bot := by rw [hc1]; exact p1.trans hf.lPath
  have c1q : C.1.core.path2 = some ⟨0, 0, 0, 6⟩ := by rw [hc1]
  have c1lb : C.1.core.label = l.core.label := by rw [hc1]; exact lb1
  have c1ld : C.1.core.leader = false := by rw [hc1]; exact ld1.trans hf.lLeader
  have c1rc : C.1.core.reset_cmd = false := by rw [hc1]; exact rc1.trans hf.lReset
  have c2s : C.2.core.state = .toss := by rw [hc2]; exact s2.trans hf.rToss
  have c2p : C.2.core.path = r.core.path := by rw [hc2]; exact p2
  have c2lb : C.2.core.label = r.core.label := by rw [hc2]; exact lb2
  have c2ld : C.2.core.leader = false := by rw [hc2]; exact ld2.trans hf.rLeader
  have c2rc : C.2.core.reset_cmd = false := by rw [hc2]; exact rc2.trans hf.rReset
  have hfix : BirthCheckPermitRepair.permitFix C.1 = C.1 :=
    BirthCheckPermitRepair.permitFix_of_ne C.1 (by rw [c1s]; decide)
  have hac := afterCheck_backToss hψ (by decide : 0 < 2) h2 h2 C.1 C.2 c1p c1s c1ld c1rc c2rc c2s
    (by rw [c2lb]; exact hr0)
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
    rw [pv1.2.2.2.2, pv2.2.2.2.2, c1ld]
    show (!l.core.leader && false || !r.core.leader && C.2.core.leader) = false
    rw [c2ld]
    simp
  rw [hq, hborn]
  simp only [markLeaderBirth, if_false, Bool.false_eq_true]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_⟩⟩
  · rw [pv1.1]; exact c1s
  · rw [pv1.2.1]; exact c1p
  · rw [pv1.2.2.1]; exact c1q
  · rw [pv1.2.2.2.1]; exact c1lb
  · rw [pv1.2.2.2.2]; exact c1ld
  · rw [pv2.1]
  · rw [pv2.2.1]; exact c2p
  · rw [pv2.2.2.1]
  · rw [pv2.2.2.2.1]; exact c2lb
  · rw [pv2.2.2.2.2]; exact c2ld

open BirthCheckPermitRepairRowLift

/-- The lottery-end back-edge row on the actual R1 row. -/
theorem r1_backToss_row (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (l r : ExpiringAgentState ψ κ τ) (c : Nat)
    (hcons : r.core.erase.core.label = ⟨(l.core.erase.core.label.val + 1) % ψ, Nat.mod_lt _ hψ⟩)
    (hlterm : l.core.erase.core.label = ⟨ψ - 1, by omega⟩) (hr0 : r.core.erase.core.label = ⟨0, hψ⟩)
    (hrp : r.core.erase.core.path = .some 0 c) (hf : BackTossPair hψ l.core.erase.core r.core.erase.core)
    (hlstall : l.stall.val ≠ 0) (hrstall : r.stall.val ≠ 0) :
    let o := BirthCheckPermitRepair.row hψ (by decide : 0 < 2) h2 l r
    (o.1.core.erase.core.state = .none ∧ o.1.core.erase.core.path = .bot ∧
        o.1.core.erase.core.path2 = some ⟨0, 0, 0, 6⟩ ∧ o.1.core.erase.core.label = l.core.erase.core.label ∧
        o.1.core.erase.core.leader = false) ∧
      (o.2.core.erase.core.state = .toss_done ∧ o.2.core.erase.core.path = r.core.erase.core.path ∧
        o.2.core.erase.core.path2 = some ⟨0, 0, 0, 5⟩ ∧ o.2.core.erase.core.label = r.core.erase.core.label ∧
        o.2.core.erase.core.reset_cmd = false ∧ o.2.core.erase.core.leader = false) := by
  intro o
  have hc := ordinary_backToss_row hψ h2 κ l.core.erase r.core.erase c hcons hlterm hr0 hrp hf
  have hlel : l.core.erase.core.state ≠ .eliminate_signal := by rw [hf.lState]; decide
  have hrel : r.core.erase.core.state ≠ .eliminate_signal := by rw [hf.rToss]; decide
  have hld : BirthSigMoveDisposalRepair.pendingTerminalDisposal hψ l.core.erase.core = false := by
    simp [BirthSigMoveDisposalRepair.pendingTerminalDisposal, hf.lPath2]
  have hrd : BirthSigMoveDisposalRepair.pendingTerminalDisposal hψ r.core.erase.core = false := by
    simp [BirthSigMoveDisposalRepair.pendingTerminalDisposal, hf.rPath2]
  have hfR := row_right_frame_clear (κ := κ) hψ h2 l r hld hrd hlel hrel hrstall hc.2.2.2.2.2
  have hfL := row_left_frame_clear (κ := κ) hψ h2 l r hld hrd hlel hrel hlstall hrstall hc.1.2.2.2.2 hc.2.2.2.2.2
  have hres := (ordinary_reset_false hψ h2 κ l.core.erase r.core.erase hlel hrel hf.lLeader hf.lReset hf.rReset).2
  exact ⟨⟨hfL.1.trans hc.1.1, hfL.2.1.trans hc.1.2.1, hfL.2.2.1.trans hc.1.2.2.1, hfL.2.2.2.1.trans hc.1.2.2.2.1,
      hfL.2.2.2.2⟩,
    ⟨hfR.1.trans hc.2.1, hfR.2.1.trans hc.2.2.1, hfR.2.2.1.trans hc.2.2.2.1, hfR.2.2.2.1.trans hc.2.2.2.2.1,
      hfR.2.2.2.2.1.trans hres, hfR.2.2.2.2.2⟩⟩

end BirthCheckChainR1TossDone
