import Leader.Wu.Splice.CheckGlobalWitnessCensus


set_option autoImplicit false
set_option Elab.async false
set_option pp.structureInstances false


namespace B9CheckBoundaryClearing


open PPLL PPLLRepair PPLLVerify PPLLResearchFormulation
open PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
open PPLLLeaderCreationCleanupRepair PPLLWallSweepRepair PPLLWallSweepFinite
open PPLLWallSweepNormalResetContract PPLLWallSweepPreCheckResetRepair
open PPLLTerminalEqualSupportRepair
open BirthGenerationDone BirthSingleUseReleaseRepair
open BirthGenerationControlRepair
open BirthShortDoneTerminalEntryCut
open K2BirthDispatcher K2BirthDispatcherDone
open B9CheckStructuralCensus B9CheckGlobalWitnessCensus


variable {n psi kappa tau width : Nat}


private theorem genStart_signal (hpsi : 0 < psi) (l r : AgentState psi) :
    signalPair (genSigSaturatedStart hpsi l r) = signalPair (l, r) := by
  unfold genSigSaturatedStart
  split <;> dsimp only <;> split <;> rfl


private theorem genEmit_signal (hpsi : 0 < psi) (l r : AgentState psi) :
    signalPair (genCleanEmit hpsi l r) = signalPair (l, r) := by
  unfold genCleanEmit
  repeat (first | rfl | split)


private theorem genPropagate_signal (hpsi : 0 < psi) (l r : AgentState psi) :
    signalPair (genCleanPropagate hpsi l r) = signalPair (l, r) := by
  unfold genCleanPropagate
  repeat (first | rfl | split)


private theorem genFinish_signal (hpsi : 0 < psi) (l r : AgentState psi) :
    signalPair (genSigSaturatedFinish hpsi l r) = signalPair (l, r) := by
  unfold genSigSaturatedFinish
  repeat (first | rfl | split)


private theorem genAfter_signal (hpsi : 0 < psi) (l r : AgentState psi) :
    signalPair (genCleanAfterWait hpsi l r) = signalPair (l, r) := by
  unfold genCleanAfterWait
  dsimp only
  rw [genFinish_signal, genPropagate_signal, genEmit_signal, genStart_signal]


private theorem genEntry_signal
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (kappa : Nat) (l r : AgentState psi) :
    signalPair (genCleanEntryWidth hpsi hwidth hle kappa l r) =
      signalPair (l, r) := by
  unfold genCleanEntryWidth
  dsimp only
  rw [genAfter_signal,
    BirthShortDoneTerminalConsumer.waitWidthEntry_signal]


private theorem generation_signal
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (kappa : Nat) (l r : AuthorizedAgentState psi) :
    authSignalPair
        (generationBeforeMoveEntryWidth hpsi hwidth hle kappa l r) =
      authSignalPair (authorizedPPsiLeaderResetProbeWall hpsi l r) := by
  let q0 := authorizedPPsiLeaderResetProbeWall hpsi l r
  let q1 := authorizedGenCleanEntryWidth hpsi hwidth hle kappa q0.1 q0.2
  let q2 := authorizedCleanSig hpsi q1.1 q1.2
  have hg : authSignalPair q1 = authSignalPair q0 := by
    change signalPair
        (genCleanEntryWidth hpsi hwidth hle kappa q0.1.core q0.2.core) =
      signalPair (q0.1.core, q0.2.core)
    exact genEntry_signal hpsi hwidth hle kappa q0.1.core q0.2.core
  unfold generationBeforeMoveEntryWidth
  exact (eliminate_signal hpsi q2.1 q2.2).trans
    ((clean_signal hpsi q1.1 q1.2).trans hg)


private theorem leaders_of_signal
    {q p : AuthorizedAgentState psi × AuthorizedAgentState psi}
    (h : authSignalPair q = authSignalPair p) :
    q.1.core.leader = p.1.core.leader /\
      q.2.core.leader = p.2.core.leader := by
  constructor
  · exact congrArg (fun z : AgentState 1 × AgentState 1 => z.1.leader) h
  · exact congrArg (fun z : AgentState 1 × AgentState 1 => z.2.leader) h


private theorem pprime_keeps_existing_leaders
    (hpsi : 0 < psi) (l r : AuthorizedAgentState psi) :
    (l.core.leader = true ->
      (authorizedPPsiLeaderResetProbeWall hpsi l r).1.core.leader = true) /\
    (r.core.leader = true ->
      (authorizedPPsiLeaderResetProbeWall hpsi l r).2.core.leader = true) := by
  constructor
  · intro hl
    change (pPsiLeaderResetProbeWall hpsi l.core r.core).1.leader = true
    rw [pPsiLeaderResetProbeWall_eq_leaderProbeWall_of_left_leader
      hpsi l.core r.core hl]
    unfold pPsiLeaderProbeWall
    dsimp only
    rw [pPsi_initiator_leader_eq]
    simp [hl]
  · intro hr
    change (pPsiLeaderResetProbeWall hpsi l.core r.core).2.leader = true
    rw [pPsiLeaderResetProbeWall_eq_leaderProbeWall_of_right_leader
      hpsi l.core r.core hr]
    exact (pPsiLeaderProbeWall_responder_frame_of_responder_leader
      hpsi l.core r.core hr).1.trans hr


private theorem doneStep2_signal (l r : AgentState psi) :
    signalPair (sigMoveStep2 l r) = signalPair (l, r) := by
  unfold sigMoveStep2
  repeat (first | rfl | split)
private theorem doneStep3_signal (l r : AgentState psi) :
    signalPair (sigMoveStep3 l r) = signalPair (l, r) := by
  unfold sigMoveStep3
  repeat (first | rfl | split)
private theorem doneStep4_signal (l r : AgentState psi) :
    signalPair (sigMoveStep4 l r) = signalPair (l, r) := by
  unfold sigMoveStep4
  repeat (first | rfl | split)
private theorem doneStep5_signal (l r : AgentState psi) :
    signalPair (sigMoveStep5 l r) = signalPair (l, r) := by
  unfold sigMoveStep5
  repeat (first | rfl | split)


private theorem doneTransfers_signal (l r : AgentState psi) :
    signalPair (doneTransfers l r) = signalPair (l, r) := by
  unfold doneTransfers holdDoneStep1 controlTransfers
  dsimp only
  split
  · rw [doneStep5_signal, doneStep4_signal, doneStep3_signal, doneStep2_signal]
  · rw [doneStep5_signal, doneStep4_signal, doneStep3_signal, doneStep2_signal]
    exact K2BirthDispatcher.captureStep1_signal l r


private theorem singleUseControlTail_eq_of_neutral
    (hpsi : 0 < psi) (l r : AgentState psi)
    (hl : ComparisonNeutral l) (hr : ComparisonNeutral r) :
    singleUseControlTail hpsi l r = (l, r) := by
  rcases hl with ⟨hlState, _, hlPath2, _, _, _, _⟩
  rcases hr with ⟨hrState, _, hrPath2, _, _, _, _⟩
  simp [singleUseControlTail, singleUseApplyControl,
    hlPath2, hrPath2, hrState]


private theorem done_neutral_of_right_leader
    (hpsi : 0 < psi) (l r : AuthorizedAgentState psi)
    (hr : r.core.leader = true) :
    let q := authorizedDoneMove hpsi l r
    ComparisonNeutral q.1.core /\ ComparisonNeutral q.2.core := by
  let p := sigMoveLeaderPreclear hpsi l.core r.core
  let moved := doneTransfers p.1 p.2
  let wall := comparisonLeaderWall moved.1 moved.2
  have hp : p.2.leader = true := by
    simp [p, sigMoveLeaderPreclear, clearIfLeader, hr, clearComparisonSignal]
  have hm := doneTransfers_signal p.1 p.2
  have hmR := congrArg
    (fun z : AgentState 1 × AgentState 1 => z.2.leader) hm
  change moved.2.leader = p.2.leader at hmR
  have hmove : moved.2.leader = true := hmR.trans hp
  have hw : ComparisonNeutral wall.1 /\ ComparisonNeutral wall.2 := by
    simp [wall, comparisonLeaderWall, hmove, clearComparisonSignal_neutral]
  have ht := singleUseControlTail_eq_of_neutral
    hpsi wall.1 wall.2 hw.1 hw.2
  have hraw :
      ComparisonNeutral (doneCaptureSigMove hpsi l.core r.core).1 /\
      ComparisonNeutral (doneCaptureSigMove hpsi l.core r.core).2 := by
    unfold doneCaptureSigMove
    change ComparisonNeutral (singleUseControlTail hpsi wall.1 wall.2).1 /\
      ComparisonNeutral (singleUseControlTail hpsi wall.1 wall.2).2
    rw [ht]
    exact hw
  have hc := authorizedDoneMove_core hpsi l r
  have hcL :
      (authorizedDoneMove hpsi l r).1.core =
        (doneCaptureSigMove hpsi l.core r.core).1 := by
    exact congrArg Prod.fst hc
  have hcR :
      (authorizedDoneMove hpsi l r).2.core =
        (doneCaptureSigMove hpsi l.core r.core).2 := by
    exact congrArg Prod.snd hc
  dsimp only
  rw [hcL, hcR]
  exact hraw


private theorem sanitize_eq_of_neutral
    (hpsi : 0 < psi)
    (q : AuthorizedAgentState psi × AuthorizedAgentState psi)
    (hl : ComparisonNeutral q.1.core) (hr : ComparisonNeutral q.2.core) :
    sanitizeAuthorizedPair hpsi q = q := by
  apply Prod.ext
  · simp [sanitizeAuthorizedPair, sanitizeAuthorizedTerminalEqual,
      unsupportedTerminalEqual, hl.1]
  · simp [sanitizeAuthorizedPair, sanitizeAuthorizedTerminalEqual,
      unsupportedTerminalEqual, hr.1]


private theorem resetWall_core_neutral_of_neutral
    (l r : AuthorizedAgentState psi)
    (hl : ComparisonNeutral l.core) (hr : ComparisonNeutral r.core) :
    let q := preCheckResetWall l r
    ComparisonNeutral q.1.core /\ ComparisonNeutral q.2.core := by
  by_cases hs : l.core.leader = true \/ l.core.reset_cmd = true
  · have hq := preCheckResetWall_both_neutral_of_send l r hs
    exact ⟨hq.1, hq.2.1⟩
  · by_cases hrst : r.core.reset_cmd = true
    · constructor
      · simpa [preCheckResetWall, hs] using hl
      · exact (preCheckResetWall_responder_neutral_of_reset l r hrst).1
    · have hpair :
          ComparisonNeutral l.core /\ ComparisonNeutral r.core :=
        ⟨hl, hr⟩
      simpa [preCheckResetWall, hs, hrst] using hpair


private theorem doneBeforeCheckEntryWidth_stage
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (kappa : Nat) (l r : AuthorizedAgentState psi) :
    let g := generationBeforeMoveEntryWidth hpsi hwidth hle kappa l r
    let m := authorizedDoneMove hpsi g.1 g.2
    doneBeforeCheckEntryWidth hpsi hwidth hle kappa l r =
      sanitizeAuthorizedPair hpsi (preCheckResetWall m.1 m.2) := by
  rfl


private theorem boundary_pair_clears
    (hpsi : 0 < psi) (h2 : 2 <= psi)
    (p : AuthorizedAgentState psi × AuthorizedAgentState psi)
    (hp : p.1.core.leader = true \/ p.2.core.leader = true) :
    let b := doneBeforeCheckEntryWidth
      hpsi (by decide : 0 < 2) h2 kappa p.1 p.2
    ComparisonNeutral b.1.core /\ ComparisonNeutral b.2.core := by
  have hwidth : 0 < 2 := by decide
  rw [doneBeforeCheckEntryWidth_stage
    hpsi hwidth h2 kappa p.1 p.2]
  have hgen :=
    generation_signal hpsi hwidth h2 kappa p.1 p.2
  generalize hg :
      generationBeforeMoveEntryWidth
        hpsi hwidth h2 kappa p.1 p.2 = g
    at hgen ⊢
  have hmSignal := authorizedDoneMove_signal hpsi g.1 g.2
  generalize hm : authorizedDoneMove hpsi g.1 g.2 = m at hmSignal ⊢
  generalize hq : preCheckResetWall m.1 m.2 = q at ⊢
  have hgenLeaders := leaders_of_signal hgen
  have hppsi := pprime_keeps_existing_leaders hpsi p.1 p.2
  rcases hp with hl | hr
  · have hgl : g.1.core.leader = true :=
      hgenLeaders.1.trans (hppsi.1 hl)
    have hmLeaders := leaders_of_signal hmSignal
    have hml : m.1.core.leader = true :=
      hmLeaders.1.trans hgl
    have hq0 := preCheckResetWall_both_neutral_of_send
      m.1 m.2 (Or.inl hml)
    rw [hq] at hq0
    have hn :
        ComparisonNeutral q.1.core /\ ComparisonNeutral q.2.core :=
      ⟨hq0.1, hq0.2.1⟩
    have hs := sanitize_eq_of_neutral hpsi q hn.1 hn.2
    rw [hs]
    exact hn
  · have hgr : g.2.core.leader = true :=
      hgenLeaders.2.trans (hppsi.2 hr)
    have hmNeutral :=
      done_neutral_of_right_leader hpsi g.1 g.2 hgr
    rw [hm] at hmNeutral
    have hqNeutral := resetWall_core_neutral_of_neutral
      m.1 m.2 hmNeutral.1 hmNeutral.2
    rw [hq] at hqNeutral
    have hs := sanitize_eq_of_neutral
      hpsi q hqNeutral.1 hqNeutral.2
    rw [hs]
    exact hqNeutral


theorem leader_boundary_clearing_unconditional
    (hpsi : 0 < psi) (h2 : 2 <= psi) (ring : DirectedRing n)
    (C : BirthPhaseCohortDesign.FC n psi kappa tau) :
    leader_boundary_clearing hpsi h2 ring C := by
  intro e
  let p := preparedPairAt hpsi ring C e
  change (p.1.core.leader = true \/ p.2.core.leader = true) ->
    ComparisonNeutral
        (doneBeforeCheckEntryWidth hpsi (by decide : 0 < 2) h2 kappa
          p.1 p.2).1.core /\
    ComparisonNeutral
        (doneBeforeCheckEntryWidth hpsi (by decide : 0 < 2) h2 kappa
          p.1 p.2).2.core
  exact boundary_pair_clears hpsi h2 p


theorem leaderBoundaryClearingPreservationStatement
    (hpsi : 0 < psi) (h2 : 2 <= psi) (ring : DirectedRing n) :
    LeaderBoundaryClearingPreservationStatement
      (kappa := kappa) (tau := tau) hpsi h2 ring := by
  intro C e _hC
  exact leader_boundary_clearing_unconditional hpsi h2 ring
    (wholePhysicalStep hpsi h2 ring C e)


end B9CheckBoundaryClearing


#print axioms B9CheckBoundaryClearing.leader_boundary_clearing_unconditional
#print axioms B9CheckBoundaryClearing.leaderBoundaryClearingPreservationStatement
