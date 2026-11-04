import Leader.Wu.Splice.CheckCleanupReleasedSafe


set_option autoImplicit false
set_option Elab.async false


namespace B9NoRouteStagesB


open PPLL PPLLRepair PPLLResearchFormulation PPLLAuthorizedComparisonRepair
open PPLLWallSweepRepair PPLLWallSweepPreCheckResetRepair PPLLTerminalEqualSupportRepair
open BirthArrivalCaptureRepair BirthSingleUseReleaseRepair BirthGenerationDone
open B9CheckStructuralCensus B9CheckCleanupReleasedSafe B9CheckRouteLifecycle


variable {n psi kappa tau : Nat}


def NoEqualOnPair (l r : AgentState psi) : Prop :=
  l.state ≠ .equal ∧ r.state ≠ .equal


def LeftZeroDepart (u : AgentState psi) : Prop :=
  ∀ b, u.path = .some 0 b → u.state = .depart


theorem eliminate_preserves_noEqual (hpsi : 0 < psi)
    (l r : AuthorizedAgentState psi) (h : NoEqualOnPair l.core r.core) :
    let q := authorizedEliminateSig hpsi l r
    NoEqualOnPair q.1.core q.2.core := by
  change NoEqualOnPair (eliminateSig hpsi l.core r.core).1
    (eliminateSig hpsi l.core r.core).2
  unfold eliminateSig
  dsimp only
  split
  · split
    · exact ⟨(fun he => nomatch he), (fun he => nomatch he)⟩
    · exact ⟨h.1, (fun he => nomatch he)⟩
  · exact h


theorem done_preserves_noEqual (hpsi : 0 < psi)
    (l r : AuthorizedAgentState psi) (h : NoEqualOnPair l.core r.core) :
    let q := authorizedDoneMove hpsi l r
    NoEqualOnPair q.1.core q.2.core := by
  have hraw : let q := doneCaptureSigMove hpsi l.core r.core
      NoEqualOnPair q.1 q.2 := by
    let p := sigMoveLeaderPreclear hpsi l.core r.core
    have hp : NoEqualOnPair p.1 p.2 := by
      unfold p sigMoveLeaderPreclear clearIfLeader clearComparisonSignal
      dsimp only
      split
      · split
        · exact ⟨(fun he => nomatch he), (fun he => nomatch he)⟩
        · exact ⟨(fun he => nomatch he), h.2⟩
      · split
        · exact ⟨h.1, (fun he => nomatch he)⟩
        · exact h
    have hcap (a b : AgentState psi) (hab : NoEqualOnPair a b) :
        let q := captureStep1 a b; NoEqualOnPair q.1 q.2 := by
      cases ha : a.path <;> cases hb : b.path
      all_goals simp only [captureStep1, ha, hb]
      all_goals repeat split
      all_goals simp_all [NoEqualOnPair]
    let first := holdDoneStep1 p.1 p.2
    have hf : NoEqualOnPair first.1 first.2 := by
      unfold first holdDoneStep1
      split
      · exact hp
      · exact hcap p.1 p.2 hp
    let moved := controlTransfers first.1 first.2
    have hm : NoEqualOnPair moved.1 moved.2 := by
      have hs := controlTransfers_phase_path first.1 first.2
      dsimp only at hs
      exact ⟨fun he => hf.1 (hs.1.symm.trans he),
        fun he => hf.2 (hs.2.1.symm.trans he)⟩
    let wall := comparisonLeaderWall moved.1 moved.2
    have hw : NoEqualOnPair wall.1 wall.2 := by
      unfold wall comparisonLeaderWall clearComparisonSignal
      dsimp only
      split
      · split
        · exact ⟨(fun he => nomatch he), (fun he => nomatch he)⟩
        · exact ⟨(fun he => nomatch he), hm.2⟩
      · split
        · exact ⟨hm.1, (fun he => nomatch he)⟩
        · exact hm
    have happly (u : AgentState psi) (hu : u.state ≠ .equal) :
        (singleUseApplyControl hpsi u).state ≠ .equal := by
      rw [singleUseApplyControl_eq_clear, clearTerminalRelease_state]
      unfold sigMoveApplyControl
      split
      · repeat split <;> simp_all
      · exact hu
    have ht : let q := singleUseControlTail hpsi wall.1 wall.2
        NoEqualOnPair q.1 q.2 := by
      have hl := happly wall.1 hw.1
      have hr := happly wall.2 hw.2
      unfold singleUseControlTail
      dsimp only
      split
      · split
        · exact ⟨(fun he => nomatch he), hr⟩
        · exact ⟨hl, hr⟩
      · exact ⟨hl, hr⟩
    change NoEqualOnPair (singleUseControlTail hpsi wall.1 wall.2).1
      (singleUseControlTail hpsi wall.1 wall.2).2
    exact ht
  have hc := authorizedDoneMove_core hpsi l r
  dsimp only at hc
  change NoEqualOnPair (authorizedDoneMove hpsi l r).1.core
    (authorizedDoneMove hpsi l r).2.core
  rw [show (authorizedDoneMove hpsi l r).1.core =
      (doneCaptureSigMove hpsi l.core r.core).1 from congrArg Prod.fst hc,
    show (authorizedDoneMove hpsi l r).2.core =
      (doneCaptureSigMove hpsi l.core r.core).2 from congrArg Prod.snd hc]
  exact hraw


theorem resetSanitize_preserves_noEqual (hpsi : 0 < psi)
    (l r : AuthorizedAgentState psi) (h : NoEqualOnPair l.core r.core) :
    let q := sanitizeAuthorizedPair hpsi (preCheckResetWall l r)
    NoEqualOnPair q.1.core q.2.core := by
  let q := preCheckResetWall l r
  have hq : NoEqualOnPair q.1.core q.2.core := by
    by_cases hs : l.core.leader = true ∨ l.core.reset_cmd = true
    · rw [show q = (clearAuthorizedComparison l, clearAuthorizedComparison r) by
        simp [q, preCheckResetWall, hs]]
      change NoEqualOnPair (clearComparisonSignal l.core) (clearComparisonSignal r.core)
      exact ⟨(fun he => nomatch he), (fun he => nomatch he)⟩
    · by_cases hrst : r.core.reset_cmd = true
      · rw [show q = (l, clearAuthorizedComparison r) by
          simp [q, preCheckResetWall, hs, hrst]]
        change NoEqualOnPair l.core (clearComparisonSignal r.core)
        exact ⟨h.1, (fun he => nomatch he)⟩
      · rw [show q = (l, r) by simp [q, preCheckResetWall, hs, hrst]]
        exact h
  have hl : sanitizeAuthorizedTerminalEqual hpsi q.1 = q.1 := by
    simp [sanitizeAuthorizedTerminalEqual, unsupportedTerminalEqual, hq.1]
  have hr : sanitizeAuthorizedTerminalEqual hpsi q.2 = q.2 := by
    simp [sanitizeAuthorizedTerminalEqual, unsupportedTerminalEqual, hq.2]
  change NoEqualOnPair (sanitizeAuthorizedPair hpsi q).1.core
    (sanitizeAuthorizedPair hpsi q).2.core
  rw [show sanitizeAuthorizedPair hpsi q = q from Prod.ext hl hr]
  exact hq


def CurrentCheckOutputNoEqual (hpsi : 0 < psi) (h2 : 2 <= psi)
    (ring : DirectedRing n) (C : BirthPhaseCohortDesign.FC n psi kappa tau) : Prop :=
  ∀ e i, (currentCheckOutputRawConfig hpsi h2 ring C e i).state ≠ .equal


theorem noCurrentRouteWitnesses_of_output_noEqual (hpsi : 0 < psi) (h2 : 2 <= psi)
    (ring : DirectedRing n) (C : BirthPhaseCohortDesign.FC n psi kappa tau)
    (h : CurrentCheckOutputNoEqual hpsi h2 ring C) :
    NoCurrentRouteWitnesses hpsi h2 ring C := by
  intro e pos referenceC leader sourceSite history carrier
  intro _
  exact h e _ carrier.endpoint_equal


end B9NoRouteStagesB


#print axioms B9NoRouteStagesB.eliminate_preserves_noEqual
#print axioms B9NoRouteStagesB.done_preserves_noEqual
#print axioms B9NoRouteStagesB.resetSanitize_preserves_noEqual
#print axioms B9NoRouteStagesB.noCurrentRouteWitnesses_of_output_noEqual
