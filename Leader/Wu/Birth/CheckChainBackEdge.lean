import Leader.Wu.Birth.CheckChainFrontEdge

set_option autoImplicit false

/-! # The back edge of a CHECK window with a quiet empty back neighbour

The back neighbour (label psi-1 of the previous segment) has no path, state `none`, no path2, no clean path5, is a
follower without reset command; the window's label-0 cell holds its aligned path, no path2, is `CHECK_ready` or
`equal`, a follower without reset command, and has no clean path4.  CLEAN keeps the chain view of both cells
(`cleanSig_back_empty`); the DONE move, CHECK and COMPARE leave both cores alone (`doneCaptureSigMove_back_empty`,
`checkSig_back_empty`, `compare_back_empty`); hence the R1 ordinary branch keeps the label-0 cell's chain view
(`ordinary_back_row`) and so does the actual R1 row (`r1_back_row`, any stall on the back neighbour). -/

namespace BirthCheckChainR1Back

open PPLL PPLLResearchFormulation PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
  PPLLLeaderCreationCleanupRepair BirthGenerationDone BirthShortDoneTerminalEntryCut
open BirthCheckChainR1 BirthCheckChainR1Front
open PPLLWallSweepRepair PPLLWallSweepPreCheckResetRepair PPLLTerminalEqualSupportRepair BirthSigMoveDisposalRepair
  BirthArrivalCaptureRepair BirthSingleUseReleaseRepair

set_option Elab.async false

variable {ψ κ τ : Nat}

structure BackPair (hψ : 0 < ψ) (l r : AgentState ψ) : Prop where
  lPath : l.path = .bot
  lState : l.state = .none
  lPath2 : l.path2 = none
  lPath5 : ∀ p, l.path5 = some p → p.1 ≠ -1
  lLeader : l.leader = false
  lReset : l.reset_cmd = false
  rPath2 : r.path2 = none
  rReadyOrEqual : r.state = .CHECK_ready ∨ r.state = .equal
  rPath4 : ∀ p, r.path4 = some p → p.1 ≠ -1
  rLeader : r.leader = false
  rReset : r.reset_cmd = false

/-- The fields of a back pair read after CLEAN (no markers). -/
structure BackCut (hψ : 0 < ψ) (l r : AgentState ψ) : Prop where
  lPath : l.path = .bot
  lState : l.state = .none
  lPath2 : l.path2 = none
  lLeader : l.leader = false
  lReset : l.reset_cmd = false
  rPath2 : r.path2 = none
  rReadyOrEqual : r.state = .CHECK_ready ∨ r.state = .equal
  rLeader : r.leader = false
  rReset : r.reset_cmd = false

theorem cleanSig_back_empty (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (l r : AgentState ψ) (c : Nat)
    (hrp : r.path = .some 0 c) (h : BackPair hψ l r) :
    genPair (cleanSig hψ l r) = genPair (l, r) := by
  have hψ1 : (0 : Nat) ≠ ψ - 1 := by omega
  have hl1 : cleanSigGenConnect l = l := by simp [cleanSigGenConnect, h.lPath]
  have hr1p : (cleanSigGenConnect r).path = .some 0 c := by simp [cleanSigGenConnect, hrp]
  have hr14 : (cleanSigGenConnect r).path4 = r.path4 := by simp [cleanSigGenConnect, hrp]
  have hr15 : (cleanSigGenConnect r).path5 = some (Int.ofNat 0, 1) := by simp [cleanSigGenConnect, hrp, hψ1]
  have hrv : genView (cleanSigGenConnect r) = genView r := genConnect_genView r
  generalize hR : cleanSigGenConnect r = R at *
  -- step 3: the initiator has no path
  have hq3 : cleanSigStep3 l R = (l, R) := by unfold cleanSigStep3; cases R.path4 <;> simp [h.lPath]
  -- step 4: a non-clean initiator path5 is consumed (the initiator may receive a clean path4, harmless on an empty
  -- cell); a clean initiator path5 is excluded
  obtain ⟨L4, hq4, hL4p, hL4v, hL45⟩ : ∃ L4 : AgentState ψ, cleanSigStep4 l R = (L4, R) ∧ L4.path = .bot ∧
      genView L4 = genView l ∧ L4.path5 = none := by
    cases h5 : l.path5 with
    | none =>
        refine ⟨l, ?_, h.lPath, rfl, h5⟩
        unfold cleanSigStep4; rw [h5]
    | some p =>
        have hp1 := h.lPath5 p h5
        obtain ⟨p1, p2⟩ := p
        refine ⟨if p1 ≠ Int.ofNat 0 - 1 then { { l with path4 := some ((-1 : Int), 1 - p2) } with path5 := none }
          else { l with path5 := none }, ?_, ?_, ?_, ?_⟩
        · unfold cleanSigStep4; rw [h5, hr1p]; simp only [ne_eq, hp1, not_false_eq_true, if_true]
          split <;> rfl
        · split <;> simp [h.lPath]
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

theorem doneCaptureSigMove_back_empty (hψ : 0 < ψ) (l r : AgentState ψ) (c : Nat)
    (hrp : r.path = .some 0 c) (h : BackCut hψ l r) :
    doneCaptureSigMove hψ l r = (l, r) := by
  have hrd : r.state ≠ .depart := by rcases h.rReadyOrEqual with e | e <;> rw [e] <;> decide
  have hp : sigMoveLeaderPreclear hψ l r = (l, r) := by
    simp [sigMoveLeaderPreclear, incompleteLeftLeaderBoundary, clearIfLeader, h.lLeader, h.rLeader]
  have hm : doneTransfers l r = (l, r) := by
    simp [doneTransfers, holdDoneStep1, h.lState, captureStep1, h.lPath, controlTransfers, sigMoveStep2,
      sigMoveStep3, sigMoveStep4, sigMoveStep5, h.lPath2, h.rPath2]
  have hw : comparisonLeaderWall l r = (l, r) := by
    simp [comparisonLeaderWall, h.lLeader, h.rLeader]
  have hc : singleUseControlTail hψ l r = (l, r) := by
    simp [singleUseControlTail, singleUseApplyControl, h.lPath2, h.rPath2, hrd]
  unfold doneCaptureSigMove
  rw [hp]
  dsimp only
  rw [hm]
  dsimp only
  rw [hw]
  exact hc

theorem checkSig_back_empty (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (l r : AgentState ψ) (c : Nat)
    (hrp : r.path = .some 0 c) (hr0 : r.label = ⟨0, hψ⟩) (h : BackCut hψ l r) :
    checkSig hψ l r = (l, r) := by
  have hsl : checkSigSetReady l = l := by unfold checkSigSetReady; rw [h.lPath]
  have hsr : checkSigSetReady r = r := by
    unfold checkSigSetReady
    split
    · split
      · rename_i hh
        rcases h.rReadyOrEqual with e | e
        · show { r with state := MainState.CHECK_ready } = r
          rw [← e]
        · exact absurd e hh.2.2.1
      · rfl
    · rfl
  have hcl : checkSigCheckL hψ l = l := by unfold checkSigCheckL; rw [h.lPath]
  have hcr : checkSigCheckR hψ l r = r := by
    unfold checkSigCheckR; split
    · split
      · rename_i hh; rw [h.lState] at hh; exact absurd hh.2 (by decide)
      · rfl
    · rfl
  have hrl : checkSigSetResult l = l := by simp [checkSigSetResult, h.lState]
  have hrr : checkSigSetResult r = r := by
    rcases h.rReadyOrEqual with e | e <;> simp [checkSigSetResult, e]
  have hrt : r.label ≠ ⟨ψ - 1, by omega⟩ := by
    intro hh; rw [hr0] at hh; have := congrArg Fin.val hh; simp only at this; omega
  unfold checkSig
  simp only [hsl, hsr, hcl, hcr, hrl, hrr]
  rw [if_neg (by intro hh; exact hrt hh.1)]

theorem compare_back_empty (hψ : 0 < ψ) (l r : AuthorizedAgentState ψ) (hlp : l.core.path = .bot) (hls : l.core.state = .none) :
    let q := PPLLCompleteMultiLeaderCleanup.authorizedCompareSigActionOne hψ l r
    q.1.core = l.core ∧ q.2.core = r.core := by
  have hinit : compareSigInit l.core = l.core := by
    unfold compareSigInit
    split
    · show { l.core with state := MainState.none } = l.core
      rw [← hls]
    · rfl
  simp [PPLLCompleteMultiLeaderCleanup.authorizedCompareSigActionOne, hinit, hlp]

theorem generation_keeps_back {width κ : Nat} (hψ : 0 < ψ) (hwidth : 0 < width) (hle : width ≤ ψ) (h2 : 2 ≤ ψ)
    (l r : AuthorizedAgentState ψ) (b : Nat)
    (hcons : r.core.label = ⟨(l.core.label.val + 1) % ψ, Nat.mod_lt _ hψ⟩)
    (hlterm : l.core.label = ⟨ψ - 1, by omega⟩) (hr0 : r.core.label = ⟨0, hψ⟩)
    (hrp : r.core.path = .some 0 b) (h : BackPair hψ l.core r.core) :
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
  have hbW : BackPair hψ A1.1.core A1.2.core := by
    rw [e1, e2]
    exact ⟨by rw [v1'.2.1]; exact h.lPath, by rw [v1'.1]; exact h.lState, by rw [v1'.2.2.1]; exact h.lPath2,
      by rw [m1.2]; exact h.lPath5, by rw [v1'.2.2.2.2.2.1]; exact h.lLeader, by rw [v1'.2.2.2.2.2.2]; exact h.lReset,
      by rw [v2'.2.2.1]; exact h.rPath2, by rw [v2'.1]; exact h.rReadyOrEqual, by rw [m2.1]; exact h.rPath4,
      by rw [v2'.2.2.2.2.2.1]; exact h.rLeader, by rw [v2'.2.2.2.2.2.2]; exact h.rReset⟩
  have hc := genPair_eq_iff.1 (cleanSig_back_empty hψ h2 A1.1.core A1.2.core b
    (by rw [e2, v2'.2.1]; exact hrp) hbW)
  rw [← c2] at hc
  have k1 : genView A2.1.core = genView l.core := hc.1.trans (by rw [e1]; exact v1)
  have k2 : genView A2.2.core = genView r.core := hc.2.trans (by rw [e2]; exact v2)
  have hrc : A2.2.core.state ≠ .eliminate_signal := by
    have := congrArg (fun v => v.1) k2
    simp only [genView] at this
    rw [this]; rcases h.rReadyOrEqual with e | e <;> rw [e] <;> decide
  have he : eliminateSig hψ A2.1.core A2.2.core = (A2.1.core, A2.2.core) :=
    eliminateSig_of_not_signal hψ A2.1.core A2.2.core hrc
  rw [he] at c3
  obtain ⟨e3a, e3b⟩ := Prod.mk.inj c3
  rw [e3a, e3b]
  exact ⟨k1, k2⟩


theorem doneThroughCheck_back {width κ : Nat} (hψ : 0 < ψ) (hwidth : 0 < width) (hle : width ≤ ψ) (h2 : 2 ≤ ψ)
    (l r : AuthorizedAgentState ψ) (c : Nat)
    (hB : let B := generationBeforeMoveEntryWidth hψ hwidth hle κ l r
      BackCut hψ B.1.core B.2.core ∧ B.2.core.path = .some 0 c ∧ B.1.core.label = ⟨ψ - 1, by omega⟩ ∧
        B.2.core.label = ⟨0, hψ⟩) :
    (doneThroughCheckEntryWidth hψ hwidth hle κ l r).1.core = (generationBeforeMoveEntryWidth hψ hwidth hle κ l r).1.core ∧
      (doneThroughCheckEntryWidth hψ hwidth hle κ l r).2.core =
        (generationBeforeMoveEntryWidth hψ hwidth hle κ l r).2.core := by
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
  rw [doneCaptureSigMove_back_empty hψ B.1.core B.2.core c hbq hf] at hmc
  generalize authorizedDoneMove hψ B.1 B.2 = m at hmc
  have hm1 : m.1.core = B.1.core := congrArg Prod.fst hmc
  have hm2 : m.2.core = B.2.core := congrArg Prod.snd hmc
  have hw : preCheckResetWall m.1 m.2 = (m.1, m.2) :=
    preCheckResetWall_eq_of_inactive m.1 m.2 (by rw [hm1]; exact hf.lLeader) (by rw [hm1]; exact hf.lReset)
      (by rw [hm2]; exact hf.rReset)
  rw [hw]
  have hrt : B.2.core.label ≠ ⟨ψ - 1, by omega⟩ := by
    intro hh; rw [hbr] at hh; have := congrArg Fin.val hh; simp only at this; omega
  have hs1 : sanitizeAuthorizedTerminalEqual hψ m.1 = m.1 := by
    unfold sanitizeAuthorizedTerminalEqual unsupportedTerminalEqual
    rw [hm1, hf.lState]; simp
  have hs2 : sanitizeAuthorizedTerminalEqual hψ m.2 = m.2 := by
    unfold sanitizeAuthorizedTerminalEqual unsupportedTerminalEqual
    rw [hm2]; simp [hrt]
  simp only [sanitizeAuthorizedPair, hs1, hs2]
  have hrn : ∀ s : MainState, s = .done ∨ s = .toss ∨ s = .congest → B.2.core.state ≠ s := by
    intro s hs e; rcases hf.rReadyOrEqual with k | k <;> rw [k] at e <;> rcases hs with hs | hs | hs <;> rw [hs] at e <;>
      cases e
  rw [preserveDoneCheck_of_no_done hψ m.1 m.2 (by rw [hm1, hf.lState]; decide) (by rw [hm2]; exact hrn _ (Or.inl rfl)),
    BirthTossCheckPreservationRepair.preserveTossCheck_of_no_toss hψ m.1 m.2 (by rw [hm1, hf.lState]; decide)
      (by rw [hm2]; exact hrn _ (Or.inr (Or.inl rfl))),
    BirthCheckCongestGuardRepair.congestGuardCheck_of_clear hψ m.1 m.2 (by rw [hm1, hf.lState]; decide)
      (by rw [hm2]; exact hrn _ (Or.inr (Or.inr rfl)))]
  have e := authorizedCheckSig_cores hψ m.1 m.2
  have hck := checkSig_back_empty hψ h2 m.1.core m.2.core c (by rw [hm2]; exact hbq) (by rw [hm2]; exact hbr)
    (by rw [hm1, hm2]; exact hf)
  rw [e.1, e.2, hck, hm1, hm2]
  exact ⟨rfl, rfl⟩

attribute [local irreducible] BirthStationaryWrite.stationaryPersistentRaw

theorem afterCheck_back {width : Nat} (hψ : 0 < ψ) (hwidth : 0 < width) (hle : width ≤ ψ) (h2 : 2 ≤ ψ)
    (l r : AuthorizedAgentState ψ) (hf : BackCut hψ l.core r.core) (hr0 : r.core.label = ⟨0, hψ⟩) :
    let q := BirthShortDoneCuts.afterCheckMetadataWidth hψ hwidth hle l r
    postView q.1.core = postView l.core ∧ postView q.2.core = postView r.core := by
  have hrterm : r.core.label ≠ ⟨ψ - 1, by omega⟩ := by
    intro hh; rw [hr0] at hh; have := congrArg Fin.val hh; simp only at this; omega
  let q0 := authorizedDisappear hψ l r
  have hd := disappear_keeps_view hψ l.core r.core (by rw [hf.lState]; decide)
    (by rcases hf.rReadyOrEqual with e | e <;> rw [e] <;> decide) hrterm
  have hdr := disappear_reset_cmd hψ l.core r.core
  have h0c1 : q0.1.core = (disappear hψ l.core r.core).1 := rfl
  have h0c2 : q0.2.core = (disappear hψ l.core r.core).2 := rfl
  have e1 := hd.1; have e2 := hd.2
  unfold chainView at e1 e2
  simp only [Prod.mk.injEq] at e1 e2
  have hc := compare_back_empty hψ q0.1 q0.2 (by rw [h0c1, e1.2.1]; exact hf.lPath) (by rw [h0c1, e1.1]; exact hf.lState)
  let q1 := PPLLCompleteMultiLeaderCleanup.authorizedCompareSigActionOne hψ q0.1 q0.2
  have hq1a : q1.1.core = q0.1.core := hc.1
  have hq1b : q1.2.core = q0.2.core := hc.2
  have hs := suppress_keeps_view hψ hwidth hle q1.1.core q1.2.core
    (by rw [hq1a, h0c1, e1.2.2.2.2.2]; exact hf.lLeader) (by rw [hq1a, h0c1, hdr.1]; exact hf.lReset)
    (by rw [hq1b, h0c2, hdr.2]; exact hf.rReset)
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

/-- The ordinary branch on a quiet empty back neighbour and the window's label-0 cell keeps both chain views. -/
theorem ordinary_back_row (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (κ : Nat) (l r : AuthorizedAgentState ψ) (c : Nat)
    (hcons : r.core.label = ⟨(l.core.label.val + 1) % ψ, Nat.mod_lt _ hψ⟩)
    (hlterm : l.core.label = ⟨ψ - 1, by omega⟩) (hr0 : r.core.label = ⟨0, hψ⟩)
    (hrp : r.core.path = .some 0 c) (hf : BackPair hψ l.core r.core) :
    let q := BirthCheckPermitRepair.ordinary hψ (by decide : 0 < 2) h2 κ l r
    postView q.1.core = postView l.core ∧ postView q.2.core = postView r.core := by
  intro q
  have hg := generation_keeps_back (κ := κ) hψ (by decide : 0 < 2) h2 h2 l r c hcons hlterm hr0 hrp hf
  generalize hB : generationBeforeMoveEntryWidth hψ (by decide : 0 < 2) h2 κ l r = B at hg
  have b1 := hg.1; have b2 := hg.2
  unfold genView at b1 b2
  simp only [Prod.mk.injEq] at b1 b2
  obtain ⟨s1, p1, q1, lb1, bt1, ld1, rc1⟩ := b1
  obtain ⟨s2, p2, q2, lb2, bt2, ld2, rc2⟩ := b2
  have hcB : BackCut hψ B.1.core B.2.core :=
    ⟨by rw [p1]; exact hf.lPath, by rw [s1]; exact hf.lState, by rw [q1]; exact hf.lPath2,
      by rw [ld1]; exact hf.lLeader, by rw [rc1]; exact hf.lReset, by rw [q2]; exact hf.rPath2,
      by rw [s2]; exact hf.rReadyOrEqual, by rw [ld2]; exact hf.rLeader, by rw [rc2]; exact hf.rReset⟩
  have hcut := doneThroughCheck_back (κ := κ) hψ (by decide : 0 < 2) h2 h2 l r c
    (by rw [hB]; exact ⟨hcB, by rw [p2]; exact hrp, by rw [lb1]; exact hlterm, by rw [lb2]; exact hr0⟩)
  rw [hB] at hcut
  generalize hC : doneThroughCheckEntryWidth hψ (by decide : 0 < 2) h2 κ l r = C at hcut
  obtain ⟨hc1, hc2⟩ := hcut
  have hfix : BirthCheckPermitRepair.permitFix C.1 = C.1 := by
    unfold BirthCheckPermitRepair.permitFix; rw [hc1, s1, hf.lState]; simp
  have hcC : BackCut hψ C.1.core C.2.core := by rw [hc1, hc2]; exact hcB
  have hac := afterCheck_back hψ (by decide : 0 < 2) h2 h2 C.1 C.2 hcC (by rw [hc2, lb2]; exact hr0)
  obtain ⟨pv1, pv2⟩ := hac
  generalize hQ : BirthShortDoneCuts.afterCheckMetadataWidth hψ (by decide : 0 < 2) h2 C.1 C.2 = Q at pv1 pv2
  have hq : q = markLeaderBirth (K2BirthDispatcher.authBirth l r Q) Q := by
    show BirthCheckPermitRepair.ordinary hψ (by decide : 0 < 2) h2 κ l r = _
    unfold BirthCheckPermitRepair.ordinary
    dsimp only
    rw [hC, hfix, hQ]
  have pv1' := pv1; have pv2' := pv2
  unfold postView at pv1' pv2'
  simp only [Prod.mk.injEq] at pv1' pv2'
  have hborn : K2BirthDispatcher.authBirth l r Q = false := by
    unfold K2BirthDispatcher.authBirth endpointLeaderBorn
    rw [pv1'.2.2.2.2, pv2'.2.2.2.2, hc1, hc2, ld1, hf.lLeader, ld2, hf.rLeader]
    rfl
  rw [hq, hborn]
  simp only [markLeaderBirth, if_false, Bool.false_eq_true]
  have e1 : postView C.1.core = postView l.core := by
    unfold postView; rw [hc1, s1, p1, q1, lb1, ld1]
  have e2 : postView C.2.core = postView r.core := by
    unfold postView; rw [hc2, s2, p2, q2, lb2, ld2]
  exact ⟨pv1.trans e1, pv2.trans e2⟩

open K2BirthDispatcher ExpiringK2Projection K2BirthLeaderNormalize
open BirthCheckPermitRepairRowLift BirthCheckPermitRepairBirth BirthCheckChainR1Internal

/-- The window's label-0 cell on the actual R1 row with a quiet empty back neighbour keeps state, path, path2, label,
reset-freeness and follower status (any stall on the back neighbour); its stall drops by at most one. -/
theorem r1_back_row (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (l r : ExpiringAgentState ψ κ τ) (c : Nat)
    (hcons : r.core.erase.core.label = ⟨(l.core.erase.core.label.val + 1) % ψ, Nat.mod_lt _ hψ⟩)
    (hlterm : l.core.erase.core.label = ⟨ψ - 1, by omega⟩) (hr0 : r.core.erase.core.label = ⟨0, hψ⟩)
    (hrp : r.core.erase.core.path = .some 0 c) (hf : BackPair hψ l.core.erase.core r.core.erase.core)
    (hrstall : r.stall.val ≠ 0) :
    let o := (BirthCheckPermitRepair.row hψ (by decide : 0 < 2) h2 l r).2
    o.core.erase.core.state = r.core.erase.core.state ∧ o.core.erase.core.path = r.core.erase.core.path ∧
      o.core.erase.core.path2 = none ∧ o.core.erase.core.label = r.core.erase.core.label ∧
      o.core.erase.core.reset_cmd = false ∧ o.core.erase.core.leader = false ∧ r.stall.val ≤ o.stall.val + 1 := by
  intro o
  have hlel : l.core.erase.core.state ≠ .eliminate_signal := by rw [hf.lState]; decide
  have hrel : r.core.erase.core.state ≠ .eliminate_signal := by
    rcases hf.rReadyOrEqual with e | e <;> rw [e] <;> decide
  have hq := ordinary_back_row hψ h2 κ l.core.erase r.core.erase c hcons hlterm hr0 hrp hf
  have q2 := hq.2
  unfold postView at q2
  simp only [Prod.mk.injEq] at q2
  have hres := (ordinary_reset_false hψ h2 κ l.core.erase r.core.erase hlel hrel hf.lLeader hf.lReset hf.rReset).2
  have fR := row_right_frame (κ := κ) hψ h2 l r hf.lPath2 hf.rPath2 hlel hrel hrstall (q2.2.2.2.2.trans hf.rLeader)
  have hs := (row_stall_ge hψ h2 l r).2
  exact ⟨fR.1.trans q2.1, fR.2.1.trans q2.2.1, fR.2.2.1.trans (q2.2.2.1.trans hf.rPath2),
    fR.2.2.2.1.trans q2.2.2.2.1, fR.2.2.2.2.1.trans hres, fR.2.2.2.2.2, hs⟩

end BirthCheckChainR1Back
