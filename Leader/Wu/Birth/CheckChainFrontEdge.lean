import Leader.Wu.Birth.CheckChainInternal
import Leader.Wu.Birth.CountAlongNoBirth

set_option autoImplicit false

/-! # The front edge of a ready CHECK window with a quiet empty neighbour

The terminal cell of a ready window (label psi-1, aligned path, `CHECK_ready`, no path2, follower, no reset command)
and an empty next cell (label 0 of the next segment, no path, state `none`, no path2, no clean path4, follower, no reset
command).  Raw stage lemmas: GEN is inert on a (label psi-1, label 0) pair (`genCleanAfterWait_boundary`); CLEAN keeps
the chain view of both cells (`cleanSig_front_empty`); the DONE move is the identity because `CHECK_ready` blocks the
hop and no control signal is present (`doneCaptureSigMove_front_empty`); raw CHECK is the identity
(`checkSig_front_empty`); COMPARE with a pathless responder keeps both cores (`compare_front_empty`). -/

namespace BirthCheckChainR1Front

open PPLL PPLLResearchFormulation PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
  PPLLLeaderCreationCleanupRepair BirthGenerationDone BirthShortDoneTerminalEntryCut
open BirthCheckChainR1

set_option Elab.async false

variable {ψ κ τ : Nat}

theorem genCleanAfterWait_boundary (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (l r : AgentState ψ)
    (hlterm : l.label = ⟨ψ - 1, by omega⟩) (hr0 : r.label = ⟨0, hψ⟩) :
    BirthGenerationControlRepair.genCleanAfterWait hψ l r = (l, r) := by
  have hl0 : l.label ≠ ⟨0, hψ⟩ := by
    intro h; rw [hlterm] at h; have := congrArg Fin.val h; simp only at this; omega
  have hrt : r.label ≠ ⟨ψ - 1, by omega⟩ := by
    intro h; rw [hr0] at h; have := congrArg Fin.val h; simp only at this; omega
  have hψ1 : ψ - 1 ≠ 0 := by omega
  unfold BirthGenerationControlRepair.genCleanAfterWait PPLLRepair.genSigSaturatedStart
    BirthGenerationControlRepair.genCleanEmit BirthGenerationControlRepair.genCleanPropagate
    PPLLRepair.genSigSaturatedFinish
  simp [hr0, hlterm, hψ1, Ne.symm hψ1]

theorem cleanSig_front_empty (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (l r : AgentState ψ) (b : Nat)
    (hlp : l.path = .some (ψ - 1) b) (hrp : r.path = .bot)
    (hr4 : ∀ p, r.path4 = some p → p.1 ≠ -1) :
    genPair (cleanSig hψ l r) = genPair (l, r) := by
  have hl1p : (cleanSigGenConnect l).path = .some (ψ - 1) b := by simp [cleanSigGenConnect, hlp]
  have hl15 : (cleanSigGenConnect l).path5 = l.path5 := by simp [cleanSigGenConnect, hlp]
  have hr1 : cleanSigGenConnect r = r := by simp [cleanSigGenConnect, hrp]
  have hlv : genView (cleanSigGenConnect l) = genView l := genConnect_genView l
  have hl14 : ∀ p, (cleanSigGenConnect l).path4 = some p → p.1 ≠ -1 := by
    intro p hp
    by_cases h0 : ψ - 1 = 0
    · omega
    · simp [cleanSigGenConnect, hlp, h0] at hp
      subst hp; exact ofNat_ne_neg_one (ψ - 1)
  generalize hL : cleanSigGenConnect l = L at *
  -- step 3: a non-clean path4 on the empty cell is dropped (and may leave a clean path5 on the empty cell)
  obtain ⟨R3, hq3, hR3p, hR3v, hR34⟩ : ∃ R3 : AgentState ψ, cleanSigStep3 L r = (L, R3) ∧ R3.path = .bot ∧
      genView R3 = genView r ∧ R3.path4 = none := by
    cases h4 : r.path4 with
    | none =>
        refine ⟨r, ?_, hrp, rfl, h4⟩
        unfold cleanSigStep3; rw [h4]
    | some p =>
        have hp1 := hr4 p h4
        obtain ⟨p1, p2⟩ := p
        refine ⟨if p1 ≠ Int.ofNat (ψ - 1 + 1) then { { r with path5 := some ((-1 : Int), 1 - p2) } with path4 := none }
          else { r with path4 := none }, ?_, ?_, ?_, ?_⟩
        · unfold cleanSigStep3; rw [h4, hl1p]; simp only [ne_eq, hp1, not_false_eq_true, if_true]
          split <;> rfl
        · split <;> simp [hrp]
        · split <;> rfl
        · split <;> rfl
  -- step 4: no path on the responder, no effect
  have hq4 : cleanSigStep4 L R3 = (L, R3) := by
    unfold cleanSigStep4; cases L.path5 <;> simp [hR3p]
  -- step 5: no path4 on the responder, no effect
  have hq5 : cleanSigStep5 hψ L R3 = (L, R3) := by
    unfold cleanSigStep5; rw [hR34]
  -- step 6: the initiator path5 moves to the empty cell
  obtain ⟨L6, R6, hq6, hL6v, hL64, hL65, hR6v, hR6p⟩ : ∃ L6 R6 : AgentState ψ, cleanSigStep6 hψ L R3 = (L6, R6) ∧
      genView L6 = genView L ∧ L6.path4 = L.path4 ∧ L6.path5 = none ∧ genView R6 = genView R3 ∧ R6.path = .bot := by
    cases h5 : L.path5 with
    | none =>
        refine ⟨L, R3, ?_, rfl, rfl, h5, rfl, hR3p⟩
        unfold cleanSigStep6; rw [h5]
    | some p5 =>
        unfold cleanSigStep6; rw [h5]
        simp only
        split
        · split
          · exact ⟨_, _, rfl, rfl, rfl, rfl, rfl, hR3p⟩
          · exact ⟨_, _, rfl, rfl, rfl, rfl, rfl, hR3p⟩
        · exact ⟨_, _, rfl, rfl, rfl, rfl, rfl, hR3p⟩
  have hal : genView (cleanSigCleanApply L6) = genView l := by
    rw [cleanApply_genView L6 (fun p hp => by rw [hL64] at hp; exact hl14 p hp) (fun p hp => by rw [hL65] at hp; cases hp)]
    exact hL6v.trans hlv
  have har : genView (cleanSigCleanApply R6) = genView r := by
    have e : cleanSigCleanApply R6 = R6 := by unfold cleanSigCleanApply; rw [hR6p]
    rw [e]; exact hR6v.trans hR3v
  unfold cleanSig genPair
  rw [hL, hr1]
  simp only [hq3, hq4, hq5, hq6]
  exact Prod.ext hal har

open PPLLWallSweepRepair PPLLWallSweepPreCheckResetRepair PPLLTerminalEqualSupportRepair BirthSigMoveDisposalRepair
  BirthArrivalCaptureRepair BirthSingleUseReleaseRepair

/-- The ready terminal token and the quiet empty next cell, raw fields. -/
structure FrontPair (hψ : 0 < ψ) (l r : AgentState ψ) : Prop where
  lReady : l.state = .CHECK_ready
  lPath2 : l.path2 = none
  lLeader : l.leader = false
  lReset : l.reset_cmd = false
  rPath : r.path = .bot
  rState : r.state = .none
  rPath2 : r.path2 = none
  rLeader : r.leader = false
  rReset : r.reset_cmd = false

theorem doneCaptureSigMove_front_empty (hψ : 0 < ψ) (l r : AgentState ψ) (a b : Nat)
    (hlp : l.path = .some a b) (h : FrontPair hψ l r) :
    doneCaptureSigMove hψ l r = (l, r) := by
  have hp : sigMoveLeaderPreclear hψ l r = (l, r) := by
    simp [sigMoveLeaderPreclear, incompleteLeftLeaderBoundary, clearIfLeader, h.lLeader, h.rLeader]
  have hm : doneTransfers l r = (l, r) := by
    simp [doneTransfers, holdDoneStep1, h.lReady, captureStep1, hlp, h.rPath, controlTransfers, sigMoveStep2,
      sigMoveStep3, sigMoveStep4, sigMoveStep5, h.lPath2, h.rPath2]
  have hw : comparisonLeaderWall l r = (l, r) := by
    simp [comparisonLeaderWall, h.lLeader, h.rLeader]
  have hc : singleUseControlTail hψ l r = (l, r) := by
    simp [singleUseControlTail, singleUseApplyControl, h.lPath2, h.rPath2, h.rState]
  unfold doneCaptureSigMove
  rw [hp]
  dsimp only
  rw [hm]
  dsimp only
  rw [hw]
  exact hc

theorem checkSig_front_empty (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (l r : AgentState ψ) (b : Nat)
    (hlp : l.path = .some (ψ - 1) b) (hlterm : l.label = ⟨ψ - 1, by omega⟩) (hr0 : r.label = ⟨0, hψ⟩)
    (h : FrontPair hψ l r) :
    checkSig hψ l r = (l, r) := by
  have hψ1 : ψ - 1 ≠ 0 := by omega
  have eL : { l with state := MainState.CHECK_ready } = l := by rw [← h.lReady]
  have hsl : checkSigSetReady l = l := by
    unfold checkSigSetReady
    split
    · split
      · exact eL
      · rfl
    · rfl
  have hsr : checkSigSetReady r = r := by unfold checkSigSetReady; rw [h.rPath]
  have hcl : checkSigCheckL hψ l = l := by
    unfold checkSigCheckL; rw [hlp]
    split
    · rename_i hh; simp only [PathInfo.some.injEq] at hh; omega
    · rfl
  have hcr : checkSigCheckR hψ l r = r := by unfold checkSigCheckR; rw [h.rPath]
  have hrl : checkSigSetResult l = l := by simp [checkSigSetResult, h.lReady]
  have hrr : checkSigSetResult r = r := by simp [checkSigSetResult, h.rState]
  have hrt : r.label ≠ ⟨ψ - 1, by omega⟩ := by
    intro hh; rw [hr0] at hh; have := congrArg Fin.val hh; simp only at this; omega
  unfold checkSig
  simp only [hsl, hsr, hcl, hcr, hrl, hrr]
  rw [if_neg (by intro hh; exact hrt hh.1)]

theorem compare_front_empty (hψ : 0 < ψ) (l r : AuthorizedAgentState ψ) (a b : Nat)
    (hlp : l.core.path = .some a b) (hrp : r.core.path = .bot) :
    let q := PPLLCompleteMultiLeaderCleanup.authorizedCompareSigActionOne hψ l r
    q.1.core = l.core ∧ q.2.core = r.core := by
  have hinit : compareSigInit l.core = l.core := by simp [compareSigInit, hlp]
  simp [PPLLCompleteMultiLeaderCleanup.authorizedCompareSigActionOne, hinit, hlp, hrp]

/-- The whole generation prefix keeps the chain view of the ready terminal token and the quiet empty next cell. -/
theorem generation_keeps_front {width κ : Nat} (hψ : 0 < ψ) (hwidth : 0 < width) (hle : width ≤ ψ) (h2 : 2 ≤ ψ)
    (l r : AuthorizedAgentState ψ) (b : Nat)
    (hcons : r.core.label = ⟨(l.core.label.val + 1) % ψ, Nat.mod_lt _ hψ⟩)
    (hll : l.core.leader = false) (hrl : r.core.leader = false)
    (hlp : l.core.path = .some (ψ - 1) b) (hlterm : l.core.label = ⟨ψ - 1, by omega⟩) (hr0 : r.core.label = ⟨0, hψ⟩)
    (hrp : r.core.path = .bot) (hrs : r.core.state = .none)
    (hr4 : ∀ p, r.core.path4 = some p → p.1 ≠ -1) :
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
  have hw := pPsiWall_keeps_genView hψ l.core r.core hcons hll hrl
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
  have hc := genPair_eq_iff.1 (cleanSig_front_empty hψ h2 A1.1.core A1.2.core b
    (by rw [e1, v1'.2.1]; exact hlp) (by rw [e2, v2'.2.1]; exact hrp) (by rw [e2, m2.1]; exact hr4))
  rw [← c2] at hc
  have k1 : genView A2.1.core = genView l.core := hc.1.trans (by rw [e1]; exact v1)
  have k2 : genView A2.2.core = genView r.core := hc.2.trans (by rw [e2]; exact v2)
  have hrc : A2.2.core.state ≠ .eliminate_signal := by
    have := congrArg (fun v => v.1) k2
    simp only [genView] at this
    rw [this, hrs]; decide
  have he : eliminateSig hψ A2.1.core A2.2.core = (A2.1.core, A2.2.core) :=
    eliminateSig_of_not_signal hψ A2.1.core A2.2.core hrc
  rw [he] at c3
  obtain ⟨e3a, e3b⟩ := Prod.mk.inj c3
  rw [e3a, e3b]
  exact ⟨k1, k2⟩

/-- DONE move, reset wall, sanitizer and CHECK keep both cores of a front pair after generation. -/
theorem doneThroughCheck_front {width κ : Nat} (hψ : 0 < ψ) (hwidth : 0 < width) (hle : width ≤ ψ) (h2 : 2 ≤ ψ)
    (l r : AuthorizedAgentState ψ) (b : Nat)
    (hB : let B := generationBeforeMoveEntryWidth hψ hwidth hle κ l r
      FrontPair hψ B.1.core B.2.core ∧ B.1.core.path = .some (ψ - 1) b ∧ B.1.core.label = ⟨ψ - 1, by omega⟩ ∧
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
  obtain ⟨hf, hbp, hbl, hbr⟩ := hB
  have hmc := authorizedDoneMove_core hψ B.1 B.2
  rw [doneCaptureSigMove_front_empty hψ B.1.core B.2.core (ψ - 1) b hbp hf] at hmc
  generalize authorizedDoneMove hψ B.1 B.2 = m at hmc
  have hm1 : m.1.core = B.1.core := congrArg Prod.fst hmc
  have hm2 : m.2.core = B.2.core := congrArg Prod.snd hmc
  have hw : preCheckResetWall m.1 m.2 = (m.1, m.2) :=
    preCheckResetWall_eq_of_inactive m.1 m.2 (by rw [hm1]; exact hf.lLeader) (by rw [hm1]; exact hf.lReset)
      (by rw [hm2]; exact hf.rReset)
  rw [hw]
  have hs1 : sanitizeAuthorizedTerminalEqual hψ m.1 = m.1 := by
    unfold sanitizeAuthorizedTerminalEqual unsupportedTerminalEqual
    rw [hm1, hf.lReady]; simp
  have hs2 : sanitizeAuthorizedTerminalEqual hψ m.2 = m.2 := by
    unfold sanitizeAuthorizedTerminalEqual unsupportedTerminalEqual
    rw [hm2, hf.rState]; simp
  simp only [sanitizeAuthorizedPair, hs1, hs2]
  rw [preserveDoneCheck_of_no_done hψ m.1 m.2 (by rw [hm1, hf.lReady]; decide) (by rw [hm2, hf.rState]; decide),
    BirthTossCheckPreservationRepair.preserveTossCheck_of_no_toss hψ m.1 m.2 (by rw [hm1, hf.lReady]; decide)
      (by rw [hm2, hf.rState]; decide),
    BirthCheckCongestGuardRepair.congestGuardCheck_of_clear hψ m.1 m.2 (by rw [hm1, hf.lReady]; decide)
      (by rw [hm2, hf.rState]; decide)]
  have e := authorizedCheckSig_cores hψ m.1 m.2
  have hck := checkSig_front_empty hψ h2 m.1.core m.2.core b (by rw [hm1]; exact hbp) (by rw [hm1]; exact hbl)
    (by rw [hm2]; exact hbr) (by rw [hm1, hm2]; exact hf)
  rw [e.1, e.2, hck, hm1, hm2]
  exact ⟨rfl, rfl⟩

attribute [local irreducible] BirthStationaryWrite.stationaryPersistentRaw

/-- Post-CHECK stages keep the chain fields of a front pair. -/
theorem afterCheck_front {width : Nat} (hψ : 0 < ψ) (hwidth : 0 < width) (hle : width ≤ ψ) (h2 : 2 ≤ ψ)
    (l r : AuthorizedAgentState ψ) (a b : Nat)
    (hlpath : l.core.path = .some a b) (hf : FrontPair hψ l.core r.core) (hr0 : r.core.label = ⟨0, hψ⟩) :
    let q := BirthShortDoneCuts.afterCheckMetadataWidth hψ hwidth hle l r
    postView q.1.core = postView l.core ∧ postView q.2.core = postView r.core := by
  have hrterm : r.core.label ≠ ⟨ψ - 1, by omega⟩ := by
    intro hh; rw [hr0] at hh; have := congrArg Fin.val hh; simp only at this; omega
  let q0 := authorizedDisappear hψ l r
  have hd := disappear_keeps_view hψ l.core r.core (by rw [hf.lReady]; decide) (by rw [hf.rState]; decide) hrterm
  have hdr := disappear_reset_cmd hψ l.core r.core
  have h0c1 : q0.1.core = (disappear hψ l.core r.core).1 := rfl
  have h0c2 : q0.2.core = (disappear hψ l.core r.core).2 := rfl
  have e1 := hd.1; have e2 := hd.2
  unfold chainView at e1 e2
  simp only [Prod.mk.injEq] at e1 e2
  have hc := compare_front_empty hψ q0.1 q0.2 a b (by rw [h0c1, e1.2.1]; exact hlpath)
    (by rw [h0c2, e2.2.1]; exact hf.rPath)
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

/-- The ordinary branch on a ready terminal token and a quiet empty next cell keeps the chain view of both. -/
theorem ordinary_front_row (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (κ : Nat) (l r : AuthorizedAgentState ψ) (b : Nat)
    (hcons : r.core.label = ⟨(l.core.label.val + 1) % ψ, Nat.mod_lt _ hψ⟩)
    (hlp : l.core.path = .some (ψ - 1) b) (hlterm : l.core.label = ⟨ψ - 1, by omega⟩) (hr0 : r.core.label = ⟨0, hψ⟩)
    (hf : FrontPair hψ l.core r.core) (hr4 : ∀ p, r.core.path4 = some p → p.1 ≠ -1) :
    let q := BirthCheckPermitRepair.ordinary hψ (by decide : 0 < 2) h2 κ l r
    postView q.1.core = postView l.core ∧ postView q.2.core = postView r.core := by
  intro q
  have hg := generation_keeps_front (κ := κ) hψ (by decide : 0 < 2) h2 h2 l r b hcons hf.lLeader hf.rLeader hlp hlterm hr0
    hf.rPath hf.rState hr4
  generalize hB : generationBeforeMoveEntryWidth hψ (by decide : 0 < 2) h2 κ l r = B at hg
  have b1 := hg.1; have b2 := hg.2
  unfold genView at b1 b2
  simp only [Prod.mk.injEq] at b1 b2
  obtain ⟨s1, p1, q1, lb1, bt1, ld1, rc1⟩ := b1
  obtain ⟨s2, p2, q2, lb2, bt2, ld2, rc2⟩ := b2
  have hfB : FrontPair hψ B.1.core B.2.core :=
    ⟨by rw [s1]; exact hf.lReady, by rw [q1]; exact hf.lPath2, by rw [ld1]; exact hf.lLeader,
      by rw [rc1]; exact hf.lReset, by rw [p2]; exact hf.rPath, by rw [s2]; exact hf.rState,
      by rw [q2]; exact hf.rPath2, by rw [ld2]; exact hf.rLeader, by rw [rc2]; exact hf.rReset⟩
  have hcut := doneThroughCheck_front (κ := κ) hψ (by decide : 0 < 2) h2 h2 l r b
    (by rw [hB]; exact ⟨hfB, by rw [p1]; exact hlp, by rw [lb1]; exact hlterm, by rw [lb2]; exact hr0⟩)
  rw [hB] at hcut
  generalize hC : doneThroughCheckEntryWidth hψ (by decide : 0 < 2) h2 κ l r = C at hcut
  obtain ⟨hc1, hc2⟩ := hcut
  have hfix : BirthCheckPermitRepair.permitFix C.1 = C.1 := by
    unfold BirthCheckPermitRepair.permitFix; rw [hc1, s1, hf.lReady]; simp
  have hfC : FrontPair hψ C.1.core C.2.core := by rw [hc1, hc2]; exact hfB
  have hac := afterCheck_front hψ (by decide : 0 < 2) h2 h2 C.1 C.2 (ψ - 1) b (by rw [hc1, p1]; exact hlp) hfC
    (by rw [hc2, lb2]; exact hr0)
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

/-- The responder leader bit of the R1 expiring layer on clean deletion-free carriers, for any stall. -/
theorem expiring_right_leader (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (l r : ExpiringAgentState ψ κ τ)
    (hlp2 : l.core.erase.core.path2 = none) (hrp2 : r.core.erase.core.path2 = none)
    (hlel : l.core.erase.core.state ≠ .eliminate_signal) (hrel : r.core.erase.core.state ≠ .eliminate_signal) :
    (BirthCheckPermitRepair.expiring hψ (by decide : 0 < 2) h2 l r).2.core.core.leader =
      (BirthCheckPermitRepair.ordinary hψ (by decide : 0 < 2) h2 κ l.core.erase r.core.erase).2.core.leader := by
  have hb := congrArg (fun z : AuthorizedAgentState ψ × AuthorizedAgentState ψ => z.2.core.leader)
    (r1_bounded_erase (κ := κ) hψ h2 l.core r.core)
  rw [authorized_eq_ordinary hψ h2 _ _ hlel hrel] at hb
  unfold BirthCheckPermitRepair.expiring
  dsimp only
  rw [prepare_identity hψ l hlp2, prepare_identity hψ r hrp2, BirthB1CountAlongNoBirth.expireOne_leader]
  exact hb

/-- The ready terminal token on the actual R1 row with a quiet empty next cell keeps state, path, path2, label and
follower status; its stall drops by at most one. -/
theorem r1_front_row (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (l r : ExpiringAgentState ψ κ τ) (b : Nat)
    (hcons : r.core.erase.core.label = ⟨(l.core.erase.core.label.val + 1) % ψ, Nat.mod_lt _ hψ⟩)
    (hlp : l.core.erase.core.path = .some (ψ - 1) b) (hlterm : l.core.erase.core.label = ⟨ψ - 1, by omega⟩)
    (hr0 : r.core.erase.core.label = ⟨0, hψ⟩)
    (hf : FrontPair hψ l.core.erase.core r.core.erase.core)
    (hr4 : ∀ p, r.core.erase.core.path4 = some p → p.1 ≠ -1)
    (hlstall : l.stall.val ≠ 0) :
    let o := (BirthCheckPermitRepair.row hψ (by decide : 0 < 2) h2 l r).1
    o.core.erase.core.state = .CHECK_ready ∧ o.core.erase.core.path = l.core.erase.core.path ∧
      o.core.erase.core.path2 = none ∧ o.core.erase.core.label = l.core.erase.core.label ∧
      o.core.erase.core.leader = false ∧ l.stall.val ≤ o.stall.val + 1 := by
  intro o
  have hlel : l.core.erase.core.state ≠ .eliminate_signal := by rw [hf.lReady]; decide
  have hrel : r.core.erase.core.state ≠ .eliminate_signal := by rw [hf.rState]; decide
  have hq := ordinary_front_row hψ h2 κ l.core.erase r.core.erase b hcons hlp hlterm hr0 hf hr4
  have q1 := hq.1; have q2 := hq.2
  unfold postView at q1 q2
  simp only [Prod.mk.injEq] at q1 q2
  have heL := expiring_left_erase (κ := κ) hψ h2 l r hf.lPath2 hf.rPath2 hlel hrel hlstall
  have hER := expiring_right_leader (κ := κ) hψ h2 l r hf.lPath2 hf.rPath2 hlel hrel
  have hn := (finalPhysical_nonK2 hψ l r
    (normalizeLeader hψ (BirthCheckPermitRepair.expiring hψ (by decide : 0 < 2) h2 l r).1)
    (normalizeLeader hψ (BirthCheckPermitRepair.expiring hψ (by decide : 0 < 2) h2 l r).2)).1
  have hfo := finalPhysical_left_follower hψ l r
    (normalizeLeader hψ (BirthCheckPermitRepair.expiring hψ (by decide : 0 < 2) h2 l r).1)
    (normalizeLeader hψ (BirthCheckPermitRepair.expiring hψ (by decide : 0 < 2) h2 l r).2)
  have hs := (row_stall_ge hψ h2 l r).1
  have ho : o = (finalPhysical hψ l r
      (normalizeLeader hψ (BirthCheckPermitRepair.expiring hψ (by decide : 0 < 2) h2 l r).1)
      (normalizeLeader hψ (BirthCheckPermitRepair.expiring hψ (by decide : 0 < 2) h2 l r).2)).1 := rfl
  rw [← ho] at hn hfo
  have hs' : l.stall.val ≤ o.stall.val + 1 := hs
  clear_value o
  generalize hE : BirthCheckPermitRepair.expiring hψ (by decide : 0 < 2) h2 l r = E at heL hER hn hfo
  have hEl : E.1.core.core.leader = false :=
    (congrArg (fun s : AuthorizedAgentState ψ => s.core.leader) heL).trans (q1.2.2.2.2.trans hf.lLeader)
  have hEr : E.2.core.core.leader = false := hER.trans (q2.2.2.2.2.trans hf.rLeader)
  rw [normalizeLeader_of_follower hψ E.1 hEl, normalizeLeader_of_follower hψ E.2 hEr] at hfo
  rw [normalizeLeader_of_follower hψ E.1 hEl] at hn
  have hx := nonK2_fields o E.1 hn
  refine ⟨?_, ?_, ?_, ?_, hfo hEl hEr, hs'⟩
  · exact hx.1.trans ((congrArg (fun s : AuthorizedAgentState ψ => s.core.state) heL).trans (q1.1.trans hf.lReady))
  · exact hx.2.1.trans ((congrArg (fun s : AuthorizedAgentState ψ => s.core.path) heL).trans q1.2.1)
  · exact hx.2.2.1.trans ((congrArg (fun s : AuthorizedAgentState ψ => s.core.path2) heL).trans
      (q1.2.2.1.trans hf.lPath2))
  · exact hx.2.2.2.1.trans ((congrArg (fun s : AuthorizedAgentState ψ => s.core.label) heL).trans q1.2.2.2.1)

/-! ## A quiet token of the next segment in front -/

structure FrontTokenPair (hψ : 0 < ψ) (l r : AgentState ψ) : Prop where
  lReady : l.state = .CHECK_ready
  lPath2 : l.path2 = none
  lPath5 : l.path5 = none
  lLeader : l.leader = false
  lReset : l.reset_cmd = false
  rPath2 : r.path2 = none
  rPath4 : r.path4 = none
  rNotDone : r.state ≠ .done
  rNotToss : r.state ≠ .toss
  rNotCongest : r.state ≠ .congest
  rNotC1 : r.state ≠ .compare1
  rNotC2 : r.state ≠ .compare2
  rNotElim : r.state ≠ .eliminate_signal
  rNotLarger : r.state ≠ .larger
  rNotLess : r.state ≠ .less
  rLeader : r.leader = false
  rReset : r.reset_cmd = false

/-- The fields of a front-token pair that the DONE move and CHECK read (no markers). -/
structure FrontTokenCut (hψ : 0 < ψ) (l r : AgentState ψ) : Prop where
  lReady : l.state = .CHECK_ready
  lPath2 : l.path2 = none
  lLeader : l.leader = false
  lReset : l.reset_cmd = false
  rPath2 : r.path2 = none
  rNotDone : r.state ≠ .done
  rNotToss : r.state ≠ .toss
  rNotCongest : r.state ≠ .congest
  rNotLarger : r.state ≠ .larger
  rNotLess : r.state ≠ .less
  rLeader : r.leader = false
  rReset : r.reset_cmd = false

theorem cleanSig_front_token (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (l r : AgentState ψ) (b a c : Nat)
    (hlp : l.path = .some (ψ - 1) b) (hrp : r.path = .some a c) (h : FrontTokenPair hψ l r) :
    genView (cleanSig hψ l r).1 = genView l := by
  have hl1p : (cleanSigGenConnect l).path = .some (ψ - 1) b := by simp [cleanSigGenConnect, hlp]
  have hl15 : (cleanSigGenConnect l).path5 = none := by simp [cleanSigGenConnect, hlp, h.lPath5]
  have hr14 : (cleanSigGenConnect r).path4 = none ∨ (cleanSigGenConnect r).path4 = some (Int.ofNat a, 1) := by
    by_cases ha : a = 0
    · left; simp [cleanSigGenConnect, hrp, ha, h.rPath4]
    · right; simp [cleanSigGenConnect, hrp, ha]
  have hr1p : (cleanSigGenConnect r).path = .some a c := by simp [cleanSigGenConnect, hrp]
  have hlv : genView (cleanSigGenConnect l) = genView l := genConnect_genView l
  have hl14 : ∀ p, (cleanSigGenConnect l).path4 = some p → p.1 ≠ -1 := by
    intro p hp
    have h0 : ψ - 1 ≠ 0 := by omega
    simp [cleanSigGenConnect, hlp, h0] at hp
    subst hp; exact ofNat_ne_neg_one (ψ - 1)
  generalize hL : cleanSigGenConnect l = L at *
  generalize hR : cleanSigGenConnect r = R at *
  -- step 3 changes only the responder
  obtain ⟨R3, hq3⟩ : ∃ R3, cleanSigStep3 L R = (L, R3) := by
    unfold cleanSigStep3
    split
    · split
      · exact ⟨_, rfl⟩
      · exact ⟨_, rfl⟩
    · exact ⟨_, rfl⟩
  -- step 4: the initiator path5 is empty
  have hq4 : cleanSigStep4 L R3 = (L, R3) := by unfold cleanSigStep4; rw [hl15]
  -- step 5 may move a non-clean responder path4 (the responder's own GenConnect marker) into the initiator
  obtain ⟨L5, R5, hq5, hL5v, hL54, hL55⟩ : ∃ L5 R5 : AgentState ψ, cleanSigStep5 hψ L R3 = (L5, R5) ∧
      genView L5 = genView L ∧ (∀ p, L5.path4 = some p → p.1 ≠ -1) ∧ L5.path5 = none := by
    have hR34' : R3.path4 = none ∨ R3.path4 = R.path4 := by
      have e := congrArg Prod.snd hq3
      simp only at e
      rw [← e]
      unfold cleanSigStep3
      split
      · split
        · left; split <;> rfl
        · right; rfl
      · right; rfl
    have hR34 : ∀ p, R3.path4 = some p → p.1 ≠ -1 := by
      intro p hp
      rcases hR34' with h0 | h1
      · rw [h0] at hp; cases hp
      · rw [h1] at hp
        rcases hr14 with k0 | k1
        · rw [k0] at hp; cases hp
        · rw [k1] at hp; cases hp; exact ofNat_ne_neg_one a
    unfold cleanSigStep5
    split
    · rename_i p4 hp4
      have hp4c := hR34 p4 hp4
      split
      · split
        · exact ⟨_, _, rfl, rfl, fun q hq => by simp at hq; rw [← hq]; exact hp4c, by simp [hl15]⟩
        · exact ⟨_, _, rfl, rfl, fun q hq => by simp at hq, by simp [hl15]⟩
      · exact ⟨_, _, rfl, rfl, fun q hq => by simp at hq; rw [← hq]; exact hp4c, by simp [hl15]⟩
    · exact ⟨_, _, rfl, rfl, hl14, hl15⟩
  -- step 6: the initiator path5 is empty
  have hq6 : cleanSigStep6 hψ L5 R5 = (L5, R5) := by unfold cleanSigStep6; rw [hL55]
  have hal : genView (cleanSigCleanApply L5) = genView l := by
    rw [cleanApply_genView L5 hL54 (fun p hp => by rw [hL55] at hp; cases hp)]
    exact hL5v.trans hlv
  unfold cleanSig
  rw [hL, hR]
  simp only [hq3, hq4, hq5, hq6]
  exact hal

/-- With an aligned label-0 front token (no path4), CLEAN keeps the chain view of both cells. -/
theorem cleanSig_front_aligned (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (l r : AgentState ψ) (b c : Nat)
    (hlp : l.path = .some (ψ - 1) b) (hrp : r.path = .some 0 c) (h : FrontTokenPair hψ l r) :
    genPair (cleanSig hψ l r) = genPair (l, r) := by
  have hψ1 : (0 : Nat) ≠ ψ - 1 := by omega
  have hl15 : (cleanSigGenConnect l).path5 = none := by simp [cleanSigGenConnect, hlp, h.lPath5]
  have hr14 : (cleanSigGenConnect r).path4 = none := by simp [cleanSigGenConnect, hrp, h.rPath4]
  have hr15 : (cleanSigGenConnect r).path5 = some (Int.ofNat 0, 1) := by simp [cleanSigGenConnect, hrp, hψ1]
  have hl14 : ∀ p, (cleanSigGenConnect l).path4 = some p → p.1 ≠ -1 := by
    intro p hp
    have h0 : ψ - 1 ≠ 0 := by omega
    simp [cleanSigGenConnect, hlp, h0] at hp
    subst hp; exact ofNat_ne_neg_one (ψ - 1)
  have hlv : genView (cleanSigGenConnect l) = genView l := genConnect_genView l
  have hrv : genView (cleanSigGenConnect r) = genView r := genConnect_genView r
  generalize hL : cleanSigGenConnect l = L at *
  generalize hR : cleanSigGenConnect r = R at *
  have hq3 : cleanSigStep3 L R = (L, R) := by unfold cleanSigStep3; rw [hr14]
  have hq4 : cleanSigStep4 L R = (L, R) := by unfold cleanSigStep4; rw [hl15]
  have hq5 : cleanSigStep5 hψ L R = (L, R) := by unfold cleanSigStep5; rw [hr14]
  have hq6 : cleanSigStep6 hψ L R = (L, R) := by unfold cleanSigStep6; rw [hl15]
  have hal : genView (cleanSigCleanApply L) = genView l := by
    rw [cleanApply_genView L hl14 (fun p hp => by rw [hl15] at hp; cases hp)]; exact hlv
  have har : genView (cleanSigCleanApply R) = genView r := by
    rw [cleanApply_genView R (fun p hp => by rw [hr14] at hp; cases hp)
      (fun p hp => by rw [hr15] at hp; cases hp; exact ofNat_ne_neg_one 0)]; exact hrv
  unfold cleanSig genPair
  rw [hL, hR]
  simp only [hq3, hq4, hq5, hq6]
  exact Prod.ext hal har

theorem doneCaptureSigMove_front_token (hψ : 0 < ψ) (l r : AgentState ψ) (a b c d : Nat)
    (hlp : l.path = .some a b) (hrp : r.path = .some c d) (h : FrontTokenCut hψ l r)
    (hlterm : ¬ l.label.val < ψ - 1) :
    doneCaptureSigMove hψ l r = (l, r) := by
  have hp : sigMoveLeaderPreclear hψ l r = (l, r) := by
    simp [sigMoveLeaderPreclear, incompleteLeftLeaderBoundary, clearIfLeader, h.lLeader, h.rLeader]
  have hm : doneTransfers l r = (l, r) := by
    simp [doneTransfers, holdDoneStep1, h.lReady, captureStep1, hlp, hrp, controlTransfers, sigMoveStep2,
      sigMoveStep3, sigMoveStep4, sigMoveStep5, h.lPath2, h.rPath2]
  have hw : comparisonLeaderWall l r = (l, r) := by
    simp [comparisonLeaderWall, h.lLeader, h.rLeader]
  have hc : singleUseControlTail hψ l r = (l, r) := by
    simp [singleUseControlTail, singleUseApplyControl, h.lPath2, h.rPath2, hlterm]
  unfold doneCaptureSigMove
  rw [hp]
  dsimp only
  rw [hm]
  dsimp only
  rw [hw]
  exact hc

theorem checkSig_front_token_left (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (l r : AgentState ψ) (b : Nat)
    (hlp : l.path = .some (ψ - 1) b) (hlterm : l.label = ⟨ψ - 1, by omega⟩) (hr0 : r.label = ⟨0, hψ⟩)
    (hlready : l.state = .CHECK_ready) (hrg : r.state ≠ .larger) (hrs : r.state ≠ .less) :
    (checkSig hψ l r).1 = l ∧ (checkSig hψ l r).2 = checkSigSetReady r := by
  have hψ1 : ψ - 1 ≠ 0 := by omega
  have eL : { l with state := MainState.CHECK_ready } = l := by rw [← hlready]
  have hsl : checkSigSetReady l = l := by
    unfold checkSigSetReady
    split
    · split
      · exact eL
      · rfl
    · rfl
  have hcl : checkSigCheckL hψ l = l := by
    unfold checkSigCheckL; rw [hlp]
    split
    · rename_i hh; simp only [PathInfo.some.injEq] at hh; omega
    · rfl
  have hcr : ∀ u : AgentState ψ, checkSigCheckR hψ l u = u := by
    intro u; unfold checkSigCheckR; split
    · split
      · rename_i hh; rw [hlready] at hh; exact absurd hh.2 (by decide)
      · rfl
    · rfl
  have hrl : checkSigSetResult l = l := by simp [checkSigSetResult, hlready]
  have hrt : r.label ≠ ⟨ψ - 1, by omega⟩ := by
    intro hh; rw [hr0] at hh; have := congrArg Fin.val hh; simp only at this; omega
  have hsr : checkSigSetReady r = r ∨ checkSigSetReady r = { r with state := .CHECK_ready } := by
    unfold checkSigSetReady; split
    · split
      · right; rfl
      · left; rfl
    · left; rfl
  have hres : checkSigSetResult (checkSigSetReady r) = checkSigSetReady r := by
    rcases hsr with e | e <;> rw [e]
    · simp [checkSigSetResult, hrg, hrs]
    · simp [checkSigSetResult]
  have hlab : (checkSigSetReady r).label = r.label := (setReady_fields r).2.2
  unfold checkSig
  simp only [hsl, hcl, hcr, hrl, hres]
  rw [if_neg (by intro hh; rw [hlab] at hh; exact hrt hh.1)]
  exact ⟨trivial, rfl⟩

/-- Generation prefix with an aligned label-0 front token: both chain views are kept. -/
theorem generation_keeps_front_token {width κ : Nat} (hψ : 0 < ψ) (hwidth : 0 < width) (hle : width ≤ ψ)
    (h2 : 2 ≤ ψ) (l r : AuthorizedAgentState ψ) (b c : Nat)
    (hcons : r.core.label = ⟨(l.core.label.val + 1) % ψ, Nat.mod_lt _ hψ⟩)
    (hlp : l.core.path = .some (ψ - 1) b) (hlterm : l.core.label = ⟨ψ - 1, by omega⟩) (hr0 : r.core.label = ⟨0, hψ⟩)
    (hrp : r.core.path = .some 0 c) (h : FrontTokenPair hψ l.core r.core) :
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
  have m1 : markers W.1 = markers l.core := hwtm.1.trans hwm.1
  have m2 : markers W.2 = markers r.core := hwtm.2.trans hwm.2
  have v1' := v1; have v2' := v2
  unfold genView at v1' v2'; unfold markers at m1 m2
  simp only [Prod.mk.injEq] at v1' v2' m1 m2
  have hgenid := genCleanAfterWait_boundary hψ h2 W.1 W.2 (by rw [v1'.2.2.2.1]; exact hlterm)
    (by rw [v2'.2.2.2.1]; exact hr0)
  rw [hgenid] at c1
  obtain ⟨e1, e2⟩ := Prod.mk.inj c1
  have hfW : FrontTokenPair hψ A1.1.core A1.2.core := by
    rw [e1, e2]
    exact ⟨by rw [v1'.1]; exact h.lReady, by rw [v1'.2.2.1]; exact h.lPath2, by rw [m1.2]; exact h.lPath5,
      by rw [v1'.2.2.2.2.2.1]; exact h.lLeader, by rw [v1'.2.2.2.2.2.2]; exact h.lReset,
      by rw [v2'.2.2.1]; exact h.rPath2, by rw [m2.1]; exact h.rPath4,
      by rw [v2'.1]; exact h.rNotDone, by rw [v2'.1]; exact h.rNotToss, by rw [v2'.1]; exact h.rNotCongest,
      by rw [v2'.1]; exact h.rNotC1, by rw [v2'.1]; exact h.rNotC2, by rw [v2'.1]; exact h.rNotElim,
      by rw [v2'.1]; exact h.rNotLarger, by rw [v2'.1]; exact h.rNotLess,
      by rw [v2'.2.2.2.2.2.1]; exact h.rLeader, by rw [v2'.2.2.2.2.2.2]; exact h.rReset⟩
  have hc := genPair_eq_iff.1 (cleanSig_front_aligned hψ h2 A1.1.core A1.2.core b c
    (by rw [e1, v1'.2.1]; exact hlp) (by rw [e2, v2'.2.1]; exact hrp) hfW)
  rw [← c2] at hc
  have k1 : genView A2.1.core = genView l.core := hc.1.trans (by rw [e1]; exact v1)
  have k2 : genView A2.2.core = genView r.core := hc.2.trans (by rw [e2]; exact v2)
  have hrc : A2.2.core.state ≠ .eliminate_signal := by
    have := congrArg (fun v => v.1) k2
    simp only [genView] at this
    rw [this]; exact h.rNotElim
  have he : eliminateSig hψ A2.1.core A2.2.core = (A2.1.core, A2.2.core) :=
    eliminateSig_of_not_signal hψ A2.1.core A2.2.core hrc
  rw [he] at c3
  obtain ⟨e3a, e3b⟩ := Prod.mk.inj c3
  rw [e3a, e3b]
  exact ⟨k1, k2⟩

/-- DONE move, reset wall, sanitizer and CHECK with an aligned front token: the terminal core is kept and the front
core is readied by CHECK line 1-3. -/
theorem doneThroughCheck_front_token {width κ : Nat} (hψ : 0 < ψ) (hwidth : 0 < width) (hle : width ≤ ψ)
    (h2 : 2 ≤ ψ) (l r : AuthorizedAgentState ψ) (b c : Nat)
    (hB : let B := generationBeforeMoveEntryWidth hψ hwidth hle κ l r
      FrontTokenCut hψ B.1.core B.2.core ∧ B.1.core.path = .some (ψ - 1) b ∧ B.2.core.path = .some 0 c ∧
        B.1.core.label = ⟨ψ - 1, by omega⟩ ∧ B.2.core.label = ⟨0, hψ⟩) :
    (doneThroughCheckEntryWidth hψ hwidth hle κ l r).1.core = (generationBeforeMoveEntryWidth hψ hwidth hle κ l r).1.core ∧
      (doneThroughCheckEntryWidth hψ hwidth hle κ l r).2.core =
        checkSigSetReady (generationBeforeMoveEntryWidth hψ hwidth hle κ l r).2.core := by
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
  obtain ⟨hf, hbp, hbq, hbl, hbr⟩ := hB
  have hlt : ¬ B.1.core.label.val < ψ - 1 := by rw [hbl]; simp
  have hmc := authorizedDoneMove_core hψ B.1 B.2
  rw [doneCaptureSigMove_front_token hψ B.1.core B.2.core (ψ - 1) b 0 c hbp hbq hf hlt] at hmc
  generalize authorizedDoneMove hψ B.1 B.2 = m at hmc
  have hm1 : m.1.core = B.1.core := congrArg Prod.fst hmc
  have hm2 : m.2.core = B.2.core := congrArg Prod.snd hmc
  have hw : preCheckResetWall m.1 m.2 = (m.1, m.2) :=
    preCheckResetWall_eq_of_inactive m.1 m.2 (by rw [hm1]; exact hf.lLeader) (by rw [hm1]; exact hf.lReset)
      (by rw [hm2]; exact hf.rReset)
  rw [hw]
  have hs1 : sanitizeAuthorizedTerminalEqual hψ m.1 = m.1 := by
    unfold sanitizeAuthorizedTerminalEqual unsupportedTerminalEqual
    rw [hm1, hf.lReady]; simp
  have hrt : B.2.core.label ≠ ⟨ψ - 1, by omega⟩ := by
    intro hh; rw [hbr] at hh; have := congrArg Fin.val hh; simp only at this; omega
  have hs2 : sanitizeAuthorizedTerminalEqual hψ m.2 = m.2 := by
    unfold sanitizeAuthorizedTerminalEqual unsupportedTerminalEqual
    rw [hm2]; simp [hrt]
  simp only [sanitizeAuthorizedPair, hs1, hs2]
  rw [preserveDoneCheck_of_no_done hψ m.1 m.2 (by rw [hm1, hf.lReady]; decide) (by rw [hm2]; exact hf.rNotDone),
    BirthTossCheckPreservationRepair.preserveTossCheck_of_no_toss hψ m.1 m.2 (by rw [hm1, hf.lReady]; decide)
      (by rw [hm2]; exact hf.rNotToss),
    BirthCheckCongestGuardRepair.congestGuardCheck_of_clear hψ m.1 m.2 (by rw [hm1, hf.lReady]; decide)
      (by rw [hm2]; exact hf.rNotCongest)]
  have e := authorizedCheckSig_cores hψ m.1 m.2
  have hck := checkSig_front_token_left hψ h2 m.1.core m.2.core b (by rw [hm1]; exact hbp) (by rw [hm1]; exact hbl)
    (by rw [hm2]; exact hbr) (by rw [hm1]; exact hf.lReady) (by rw [hm2]; exact hf.rNotLarger)
    (by rw [hm2]; exact hf.rNotLess)
  rw [e.1, e.2, hck.1, hck.2, hm1, hm2]
  exact ⟨rfl, rfl⟩

/-- Post-CHECK stages with a readied aligned front token keep the terminal chain view. -/
theorem afterCheck_front_token {width : Nat} (hψ : 0 < ψ) (hwidth : 0 < width) (hle : width ≤ ψ) (h2 : 2 ≤ ψ)
    (l r : AuthorizedAgentState ψ) (b c : Nat)
    (hlpath : l.core.path = .some (ψ - 1) b) (hrpath : r.core.path = .some 0 c)
    (hlready : l.core.state = .CHECK_ready) (hlp2 : l.core.path2 = none) (hrp2 : r.core.path2 = none)
    (hrt : r.core.state ≠ .toss) (hr1 : r.core.state ≠ .compare1) (hr2 : r.core.state ≠ .compare2)
    (hlterm : l.core.label = ⟨ψ - 1, by omega⟩) (hr0 : r.core.label = ⟨0, hψ⟩)
    (hll : l.core.leader = false) (hlr : l.core.reset_cmd = false) (hrr : r.core.reset_cmd = false) :
    let q := BirthShortDoneCuts.afterCheckMetadataWidth hψ hwidth hle l r
    postView q.1.core = postView l.core := by
  have hl0 : l.core.label ≠ ⟨0, hψ⟩ := by
    intro hh; rw [hlterm] at hh; have := congrArg Fin.val hh; simp only at this; omega
  have hrterm : r.core.label ≠ ⟨ψ - 1, by omega⟩ := by
    intro hh; rw [hr0] at hh; have := congrArg Fin.val hh; simp only at this; omega
  have hq := afterCheck_keeps_quiet hψ hwidth hle l r (ψ - 1) b 0 c hlpath hrpath
    (by rw [hlready]; decide) hrt (by rw [hlready]; decide) (by rw [hlready]; decide) (by rw [hlready]; decide)
    hr1 hr2 hlp2 hrp2 hl0 hrterm hll hlr hrr
  exact hq.1

theorem setReady_frame (u : AgentState ψ) :
    (checkSigSetReady u).path2 = u.path2 ∧ (checkSigSetReady u).path = u.path ∧
      (checkSigSetReady u).reset_cmd = u.reset_cmd ∧ (checkSigSetReady u).leader = u.leader ∧
      (checkSigSetReady u).label = u.label ∧
      ((checkSigSetReady u).state = u.state ∨ (checkSigSetReady u).state = .CHECK_ready) := by
  unfold checkSigSetReady
  split
  · split
    · exact ⟨rfl, rfl, rfl, rfl, rfl, Or.inr rfl⟩
    · exact ⟨rfl, rfl, rfl, rfl, rfl, Or.inl rfl⟩
  · exact ⟨rfl, rfl, rfl, rfl, rfl, Or.inl rfl⟩

/-- The ordinary branch with an aligned quiet front token keeps the terminal chain view. -/
theorem ordinary_front_token_row (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (κ : Nat) (l r : AuthorizedAgentState ψ) (b c : Nat)
    (hcons : r.core.label = ⟨(l.core.label.val + 1) % ψ, Nat.mod_lt _ hψ⟩)
    (hlp : l.core.path = .some (ψ - 1) b) (hlterm : l.core.label = ⟨ψ - 1, by omega⟩) (hr0 : r.core.label = ⟨0, hψ⟩)
    (hrp : r.core.path = .some 0 c) (hf : FrontTokenPair hψ l.core r.core) :
    let q := BirthCheckPermitRepair.ordinary hψ (by decide : 0 < 2) h2 κ l r
    postView q.1.core = postView l.core ∧ q.2.core.leader = false := by
  intro q
  have hg := generation_keeps_front_token (κ := κ) hψ (by decide : 0 < 2) h2 h2 l r b c hcons hlp hlterm hr0 hrp hf
  generalize hB : generationBeforeMoveEntryWidth hψ (by decide : 0 < 2) h2 κ l r = B at hg
  have b1 := hg.1; have b2 := hg.2
  unfold genView at b1 b2
  simp only [Prod.mk.injEq] at b1 b2
  obtain ⟨s1, p1, q1, lb1, bt1, ld1, rc1⟩ := b1
  obtain ⟨s2, p2, q2, lb2, bt2, ld2, rc2⟩ := b2
  have hcB : FrontTokenCut hψ B.1.core B.2.core :=
    ⟨by rw [s1]; exact hf.lReady, by rw [q1]; exact hf.lPath2, by rw [ld1]; exact hf.lLeader,
      by rw [rc1]; exact hf.lReset, by rw [q2]; exact hf.rPath2, by rw [s2]; exact hf.rNotDone,
      by rw [s2]; exact hf.rNotToss, by rw [s2]; exact hf.rNotCongest, by rw [s2]; exact hf.rNotLarger,
      by rw [s2]; exact hf.rNotLess, by rw [ld2]; exact hf.rLeader, by rw [rc2]; exact hf.rReset⟩
  have hcut := doneThroughCheck_front_token (κ := κ) hψ (by decide : 0 < 2) h2 h2 l r b c
    (by rw [hB]; exact ⟨hcB, by rw [p1]; exact hlp, by rw [p2]; exact hrp, by rw [lb1]; exact hlterm,
      by rw [lb2]; exact hr0⟩)
  rw [hB] at hcut
  generalize hC : doneThroughCheckEntryWidth hψ (by decide : 0 < 2) h2 κ l r = C at hcut
  obtain ⟨hc1, hc2⟩ := hcut
  obtain ⟨f2, fp, frc, fld, flb, fst⟩ := setReady_frame B.2.core
  have hfix : BirthCheckPermitRepair.permitFix C.1 = C.1 := by
    unfold BirthCheckPermitRepair.permitFix; rw [hc1, s1, hf.lReady]; simp
  have hac := afterCheck_front_token hψ (by decide : 0 < 2) h2 h2 C.1 C.2 b c
    (by rw [hc1, p1]; exact hlp) (by rw [hc2, fp, p2]; exact hrp)
    (by rw [hc1, s1]; exact hf.lReady) (by rw [hc1, q1]; exact hf.lPath2) (by rw [hc2, f2, q2]; exact hf.rPath2)
    (by rw [hc2]; rcases fst with e | e <;> rw [e]; rw [s2]; exact hf.rNotToss; decide)
    (by rw [hc2]; rcases fst with e | e <;> rw [e]; rw [s2]; exact hf.rNotC1; decide)
    (by rw [hc2]; rcases fst with e | e <;> rw [e]; rw [s2]; exact hf.rNotC2; decide)
    (by rw [hc1, lb1]; exact hlterm) (by rw [hc2, flb, lb2]; exact hr0)
    (by rw [hc1, ld1]; exact hf.lLeader) (by rw [hc1, rc1]; exact hf.lReset) (by rw [hc2, frc, rc2]; exact hf.rReset)
  generalize hQ : BirthShortDoneCuts.afterCheckMetadataWidth hψ (by decide : 0 < 2) h2 C.1 C.2 = Q at hac
  have hsig := BirthShortDoneCuts.afterCheckMetadataWidth_signal hψ (by decide : 0 < 2) h2 C.1 C.2
  rw [hQ] at hsig
  have hq2l : Q.2.core.leader = C.2.core.leader := congrArg (fun z : AgentState 1 × AgentState 1 => z.2.leader) hsig
  have hq : q = markLeaderBirth (K2BirthDispatcher.authBirth l r Q) Q := by
    show BirthCheckPermitRepair.ordinary hψ (by decide : 0 < 2) h2 κ l r = _
    unfold BirthCheckPermitRepair.ordinary
    dsimp only
    rw [hC, hfix, hQ]
  have hac' := hac
  unfold postView at hac'
  simp only [Prod.mk.injEq] at hac'
  have hborn : K2BirthDispatcher.authBirth l r Q = false := by
    unfold K2BirthDispatcher.authBirth endpointLeaderBorn
    rw [hac'.2.2.2.2, hq2l, hc1, hc2, fld, ld1, hf.lLeader, ld2, hf.rLeader]
    rfl
  rw [hq, hborn]
  simp only [markLeaderBirth, if_false, Bool.false_eq_true]
  have e1 : postView C.1.core = postView l.core := by
    unfold postView; rw [hc1, s1, p1, q1, lb1, ld1]
  refine ⟨hac.trans e1, ?_⟩
  show Q.2.core.leader = false
  rw [hq2l, hc2, fld, ld2]; exact hf.rLeader

/-- The ready terminal token on the actual R1 row with an aligned quiet token of the next segment in front keeps
state, path, path2, label and follower status; its stall drops by at most one. -/
theorem r1_front_token_row (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (l r : ExpiringAgentState ψ κ τ) (b c : Nat)
    (hcons : r.core.erase.core.label = ⟨(l.core.erase.core.label.val + 1) % ψ, Nat.mod_lt _ hψ⟩)
    (hlp : l.core.erase.core.path = .some (ψ - 1) b) (hlterm : l.core.erase.core.label = ⟨ψ - 1, by omega⟩)
    (hr0 : r.core.erase.core.label = ⟨0, hψ⟩) (hrp : r.core.erase.core.path = .some 0 c)
    (hf : FrontTokenPair hψ l.core.erase.core r.core.erase.core)
    (hlstall : l.stall.val ≠ 0) :
    let o := (BirthCheckPermitRepair.row hψ (by decide : 0 < 2) h2 l r).1
    o.core.erase.core.state = .CHECK_ready ∧ o.core.erase.core.path = l.core.erase.core.path ∧
      o.core.erase.core.path2 = none ∧ o.core.erase.core.label = l.core.erase.core.label ∧
      o.core.erase.core.leader = false ∧ l.stall.val ≤ o.stall.val + 1 := by
  intro o
  have hlel : l.core.erase.core.state ≠ .eliminate_signal := by rw [hf.lReady]; decide
  have hq := ordinary_front_token_row hψ h2 κ l.core.erase r.core.erase b c hcons hlp hlterm hr0 hrp hf
  have q1 := hq.1
  unfold postView at q1
  simp only [Prod.mk.injEq] at q1
  have heL := expiring_left_erase (κ := κ) hψ h2 l r hf.lPath2 hf.rPath2 hlel hf.rNotElim hlstall
  have hER := expiring_right_leader (κ := κ) hψ h2 l r hf.lPath2 hf.rPath2 hlel hf.rNotElim
  have hn := (finalPhysical_nonK2 hψ l r
    (normalizeLeader hψ (BirthCheckPermitRepair.expiring hψ (by decide : 0 < 2) h2 l r).1)
    (normalizeLeader hψ (BirthCheckPermitRepair.expiring hψ (by decide : 0 < 2) h2 l r).2)).1
  have hfo := finalPhysical_left_follower hψ l r
    (normalizeLeader hψ (BirthCheckPermitRepair.expiring hψ (by decide : 0 < 2) h2 l r).1)
    (normalizeLeader hψ (BirthCheckPermitRepair.expiring hψ (by decide : 0 < 2) h2 l r).2)
  have hs := (row_stall_ge hψ h2 l r).1
  have ho : o = (finalPhysical hψ l r
      (normalizeLeader hψ (BirthCheckPermitRepair.expiring hψ (by decide : 0 < 2) h2 l r).1)
      (normalizeLeader hψ (BirthCheckPermitRepair.expiring hψ (by decide : 0 < 2) h2 l r).2)).1 := rfl
  rw [← ho] at hn hfo
  have hs' : l.stall.val ≤ o.stall.val + 1 := hs
  clear_value o
  generalize hE : BirthCheckPermitRepair.expiring hψ (by decide : 0 < 2) h2 l r = E at heL hER hn hfo
  have hEl : E.1.core.core.leader = false :=
    (congrArg (fun s : AuthorizedAgentState ψ => s.core.leader) heL).trans (q1.2.2.2.2.trans hf.lLeader)
  have hEr : E.2.core.core.leader = false := hER.trans hq.2
  rw [normalizeLeader_of_follower hψ E.1 hEl, normalizeLeader_of_follower hψ E.2 hEr] at hfo
  rw [normalizeLeader_of_follower hψ E.1 hEl] at hn
  have hx := nonK2_fields o E.1 hn
  refine ⟨?_, ?_, ?_, ?_, hfo hEl hEr, hs'⟩
  · exact hx.1.trans ((congrArg (fun s : AuthorizedAgentState ψ => s.core.state) heL).trans (q1.1.trans hf.lReady))
  · exact hx.2.1.trans ((congrArg (fun s : AuthorizedAgentState ψ => s.core.path) heL).trans q1.2.1)
  · exact hx.2.2.1.trans ((congrArg (fun s : AuthorizedAgentState ψ => s.core.path2) heL).trans
      (q1.2.2.1.trans hf.lPath2))
  · exact hx.2.2.2.1.trans ((congrArg (fun s : AuthorizedAgentState ψ => s.core.label) heL).trans q1.2.2.2.1)

end BirthCheckChainR1Front
