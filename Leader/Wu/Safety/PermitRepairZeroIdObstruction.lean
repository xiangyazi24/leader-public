import Leader.Wu.Entrance.WriterSilence
import Leader.Wu.Safety.PermitRepairZeroIdBirthWord
import Leader.Wu.Splice.HostTable

/-!
# The passive all-zero class cannot enter the stable-ID target

WriterPassive is reproduced locally with the identical body. No dependency
on R1CandidatePrime is introduced. This file adds no runtime state.

PN permits arbitrary main-protocol activity, permits and timers, arbitrary
writer control Booleans, and arbitrarily many leaders. Only the three passive
writer fields and the labels of existing leaders are constrained.

B9 closure exposes its follower-relabel guard as a theorem argument. The bare
R1 closure and the arithmetic obstruction have no such argument. Neither
stable-ID non-entry nor an individual rebirth trace proves nonconvergence.
-/

set_option autoImplicit false
set_option Elab.async false

namespace R1ZeroIdClosedObstruction

open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
  PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
  PPLLPathStallComparisonRepair PPLLLeaderCreationCleanupRepair
  PPLLWriteIncrementGate PPLLWriteSeqPersistenceRepair
  PPLLWallSweepRepair PPLLWallSweepFinite
  PPLLWallSweepPreCheckResetRepair PPLLTerminalEqualSupportRepair
  PPLLCompleteMultiLeaderCleanup PPLLNoCheckBirthConditionTwoPhysical
  BirthGenerationControlRepair BirthGenerationDone
  BirthArrivalCaptureRepair BirthSingleUseReleaseRepair
  BirthTossCheckPreservationRepair BirthCheckCongestGuardRepair
  BirthSigMoveDisposalRepair BirthShortWait
  BirthShortWaitTerminalEntryRepair BirthShortDoneTerminalEntryCut
  BirthShortDoneCuts BirthStationaryWrite K2BirthDispatcher
  K2BirthLeaderNormalize ExpiringK2Projection

variable {n psi kappa tau width : Nat}

abbrev FC (n psi kappa tau : Nat) :=
  Fin n → ExpiringAgentState psi kappa tau

abbrev raw (u : ExpiringAgentState psi kappa tau) : AgentState psi :=
  u.core.erase.core

/-- Identical body to R1CandidatePrime.WriterPassive. -/
def WriterPassive (u : AgentState psi) : Prop :=
  u.path3 = none ∧ u.write = .none ∧
    (u.write_state = .none ∨ u.write_state = .depart)

/-- Val form of leader => label zero; no positivity proof is stored. -/
def Normalized (u : AgentState psi) : Prop :=
  u.leader = true → u.label.val = 0

def PN (C : FC n psi kappa tau) : Prop :=
  ∀ i, WriterPassive (raw (C i)) ∧ Normalized (raw (C i))

def S0 (C : FC n psi kappa tau) : Prop :=
  PN C ∧ ∀ i, (raw (C i)).bit = false

private structure WV where
  bit : Bool
  path3 : Option Path3Info
  write : WriteAction
  state : WriteState

private abbrev MV (psi : Nat) := Fin psi × WV
private abbrev MP (psi : Nat) := MV psi × MV psi

private def wv (u : AgentState psi) : WV :=
  ⟨u.bit, u.path3, u.write, u.write_state⟩
private def mv (u : AgentState psi) : MV psi := (u.label, wv u)
private def mp (q : AgentState psi × AgentState psi) : MP psi :=
  (mv q.1, mv q.2)
private def am (q : AuthorizedAgentState psi × AuthorizedAgentState psi) : MP psi :=
  mp (q.1.core, q.2.core)
private def wp (q : AgentState psi × AgentState psi) : WV × WV :=
  (wv q.1, wv q.2)
private def ew (u : ExpiringAgentState psi kappa tau) : WV := wv (raw u)

private def Good (old out : AgentState psi) : Prop :=
  WriterPassive out ∧ out.bit = old.bit
private def WG (l r : AgentState psi) (q : AgentState psi × AgentState psi) : Prop :=
  Good l q.1 ∧ Good r q.2

private theorem passive_of_wv {u v : AgentState psi}
    (h : wv u = wv v) (hv : WriterPassive v) : WriterPassive u := by
  refine ⟨(congrArg WV.path3 h).trans hv.1,
    (congrArg WV.write h).trans hv.2.1, ?_⟩
  rcases hv.2.2 with hn | hd
  · exact Or.inl ((congrArg WV.state h).trans hn)
  · exact Or.inr ((congrArg WV.state h).trans hd)

private theorem good_of_wv {old u v : AgentState psi}
    (h : wv u = wv v) (hv : Good old v) : Good old u :=
  ⟨passive_of_wv h hv.1, (congrArg WV.bit h).trans hv.2⟩

private theorem good_of_mv {old u v : AgentState psi}
    (h : mv u = mv v) (hv : Good old v) : Good old u :=
  good_of_wv (congrArg Prod.snd h) hv

private theorem normalized_of_mv {u v : AgentState psi}
    (h : mv u = mv v) (hl : u.leader = v.leader)
    (hv : Normalized v) : Normalized u := by
  intro hu
  exact (congrArg (fun z : MV psi => z.1.val) h).trans
    (hv (hl.symm.trans hu))

private theorem wg_of_mp (l r : AgentState psi)
    (q : AgentState psi × AgentState psi) (h : mp q = mp (l, r))
    (hl : WriterPassive l) (hr : WriterPassive r) : WG l r q :=
  ⟨good_of_mv (congrArg Prod.fst h) ⟨hl, rfl⟩,
    good_of_mv (congrArg Prod.snd h) ⟨hr, rfl⟩⟩

private theorem wg_trans (l r : AgentState psi)
    (a b : AgentState psi × AgentState psi)
    (ha : WG l r a) (hb : WG a.1 a.2 b) : WG l r b :=
  ⟨⟨hb.1.1, hb.1.2.trans ha.1.2⟩,
    ⟨hb.2.1, hb.2.2.trans ha.2.2⟩⟩

private theorem lift_frame
    (f : AgentState psi → AgentState psi → AgentState psi × AgentState psi)
    (hf : ∀ l r, mp (f l r) = mp (l, r))
    (l r : AuthorizedAgentState psi) :
    am (authorizedReconcile f l r) = am (l, r) := hf l.core r.core

private theorem wait_prepare_m (h : 0 < psi) (l r : AgentState psi) :
    mp (waitSaturatedPrepare h l r) = mp (l, r) := by
  unfold waitSaturatedPrepare mp mv wv
  try dsimp only
  repeat (first | rfl | split)
private theorem wait_clear_m (hw : 0 < width) (hle : width ≤ psi)
    (l r : AgentState psi) : mp (terminalInactiveClear hw hle l r) = mp (l, r) := by
  unfold terminalInactiveClear mp mv wv
  repeat (first | rfl | split)
private theorem wait_carry_m (hw : 0 < width) (hle : width ≤ psi)
    (cap : Nat) (l r : AgentState psi) :
    mp (waitWidthCarry hw hle cap l r) = mp (l, r) := by
  unfold waitWidthCarry mp mv wv
  repeat (first | rfl | split)
private theorem wait_reset_m (hw : 0 < width) (hle : width ≤ psi)
    (l r : AgentState psi) : mp (waitWidthReset hw hle l r) = mp (l, r) := by
  unfold waitWidthReset mp mv wv
  repeat (first | rfl | split)
private theorem wait_finish_m (h : 0 < psi) (hw : 0 < width)
    (hle : width ≤ psi) (cap : Nat) (l r : AgentState psi) :
    mp (waitWidthFinish h hw hle cap l r) = mp (l, r) := by
  unfold waitWidthFinish mp mv wv
  try dsimp only
  repeat (first | rfl | split)

private theorem wait_entry_m (h : 0 < psi) (hw : 0 < width)
    (hle : width ≤ psi) (cap : Nat) (l r : AgentState psi) :
    mp (waitWidthEntry h hw hle cap l r) = mp (l, r) := by
  unfold waitWidthEntry
  try dsimp only
  rw [wait_finish_m, wait_reset_m, wait_carry_m, wait_clear_m, wait_prepare_m]

private theorem gen_start_m (h : 0 < psi) (l r : AgentState psi) :
    mp (genSigSaturatedStart h l r) = mp (l, r) := by
  unfold genSigSaturatedStart mp mv wv
  try dsimp only
  repeat (first | rfl | split)
private theorem gen_emit_m (h : 0 < psi) (l r : AgentState psi) :
    mp (genCleanEmit h l r) = mp (l, r) := by
  unfold genCleanEmit mp mv wv
  try dsimp only
  repeat (first | rfl | split)
private theorem gen_propagate_m (h : 0 < psi) (l r : AgentState psi) :
    mp (genCleanPropagate h l r) = mp (l, r) := by
  unfold genCleanPropagate mp mv wv
  repeat (first | rfl | split)
private theorem gen_finish_m (h : 0 < psi) (l r : AgentState psi) :
    mp (genSigSaturatedFinish h l r) = mp (l, r) := by
  unfold genSigSaturatedFinish mp mv wv
  try dsimp only
  repeat (first | rfl | split)
private theorem gen_after_m (h : 0 < psi) (l r : AgentState psi) :
    mp (genCleanAfterWait h l r) = mp (l, r) := by
  unfold genCleanAfterWait
  try dsimp only
  rw [gen_finish_m, gen_propagate_m, gen_emit_m, gen_start_m]
private theorem gen_entry_m (h : 0 < psi) (hw : 0 < width)
    (hle : width ≤ psi) (cap : Nat) (l r : AgentState psi) :
    mp (genCleanEntryWidth h hw hle cap l r) = mp (l, r) := by
  unfold genCleanEntryWidth
  try dsimp only
  rw [gen_after_m, wait_entry_m]
private theorem gen_entry_am (h : 0 < psi) (hw : 0 < width)
    (hle : width ≤ psi) (cap : Nat) (l r : AuthorizedAgentState psi) :
    am (authorizedGenCleanEntryWidth h hw hle cap l r) = am (l, r) :=
  lift_frame _ (gen_entry_m h hw hle cap) l r
private theorem clean_connect_m (l r : AgentState psi) :
    mp (cleanSigGenConnect l, cleanSigGenConnect r) = mp (l, r) := by
  unfold cleanSigGenConnect mp mv wv
  try dsimp only
  repeat (first | rfl | split)
private theorem clean3_m (l r : AgentState psi) :
    mp (cleanSigStep3 l r) = mp (l, r) := by
  unfold cleanSigStep3 mp mv wv
  repeat (first | rfl | split)
private theorem clean4_m (l r : AgentState psi) :
    mp (cleanSigStep4 l r) = mp (l, r) := by
  unfold cleanSigStep4 mp mv wv
  repeat (first | rfl | split)
private theorem clean5_m (h : 0 < psi) (l r : AgentState psi) :
    mp (cleanSigStep5 h l r) = mp (l, r) := by
  unfold cleanSigStep5 mp mv wv
  repeat (first | rfl | split)
private theorem clean6_m (h : 0 < psi) (l r : AgentState psi) :
    mp (cleanSigStep6 h l r) = mp (l, r) := by
  unfold cleanSigStep6 mp mv wv
  repeat (first | rfl | split)
private theorem clean_apply_m (u : AgentState psi) :
    mv (cleanSigCleanApply u) = mv u := by
  unfold cleanSigCleanApply mv wv
  try dsimp only
  repeat (first | rfl | split)
private theorem clean_apply_pair_m (l r : AgentState psi) :
    mp (cleanSigCleanApply l, cleanSigCleanApply r) = mp (l, r) :=
  Prod.ext (clean_apply_m l) (clean_apply_m r)
private theorem clean_m (h : 0 < psi) (l r : AgentState psi) :
    mp (cleanSig h l r) = mp (l, r) := by
  unfold cleanSig
  try dsimp only
  rw [clean_apply_pair_m, clean6_m, clean5_m, clean4_m, clean3_m, clean_connect_m]
private theorem clean_am (h : 0 < psi) (l r : AuthorizedAgentState psi) :
    am (authorizedCleanSig h l r) = am (l, r) :=
  lift_frame _ (clean_m h) l r

private theorem eliminate_m (h : 0 < psi) (l r : AgentState psi) :
    mp (eliminateSig h l r) = mp (l, r) := by
  unfold eliminateSig mp mv wv
  try dsimp only
  repeat (first | rfl | split)
private theorem eliminate_am (h : 0 < psi) (l r : AuthorizedAgentState psi) :
    am (authorizedEliminateSig h l r) = am (l, r) :=
  lift_frame _ (eliminate_m h) l r

private theorem preclear_m (h : 0 < psi) (l r : AgentState psi) :
    mp (sigMoveLeaderPreclear h l r) = mp (l, r) := by
  unfold sigMoveLeaderPreclear clearIfLeader clearComparisonSignal mp mv wv
  try dsimp only
  repeat (first | rfl | split)
private theorem capture_m (l r : AgentState psi) :
    mp (captureStep1 l r) = mp (l, r) := by
  unfold captureStep1 mp mv wv
  try dsimp only
  repeat (first | rfl | split)
private theorem hold_done_m (l r : AgentState psi) :
    mp (holdDoneStep1 l r) = mp (l, r) := by
  unfold holdDoneStep1
  split
  · rfl
  · exact capture_m l r
private theorem sig2_m (l r : AgentState psi) : mp (sigMoveStep2 l r) = mp (l, r) := by
  unfold sigMoveStep2 mp mv wv
  repeat (first | rfl | split)
private theorem sig3_m (l r : AgentState psi) : mp (sigMoveStep3 l r) = mp (l, r) := by
  unfold sigMoveStep3 mp mv wv
  repeat (first | rfl | split)
private theorem sig4_m (l r : AgentState psi) : mp (sigMoveStep4 l r) = mp (l, r) := by
  unfold sigMoveStep4 mp mv wv
  repeat (first | rfl | split)
private theorem sig5_m (l r : AgentState psi) : mp (sigMoveStep5 l r) = mp (l, r) := by
  unfold sigMoveStep5 mp mv wv
  repeat (first | rfl | split)
private theorem controls_m (l r : AgentState psi) :
    mp (controlTransfers l r) = mp (l, r) := by
  unfold controlTransfers
  try dsimp only
  rw [sig5_m, sig4_m, sig3_m, sig2_m]
private theorem done_transfers_m (l r : AgentState psi) :
    mp (doneTransfers l r) = mp (l, r) := by
  unfold doneTransfers
  try dsimp only
  rw [controls_m, hold_done_m]
private theorem leader_wall_m (l r : AgentState psi) :
    mp (comparisonLeaderWall l r) = mp (l, r) := by
  unfold comparisonLeaderWall clearComparisonSignal mp mv wv
  try dsimp only
  repeat (first | rfl | split)
private theorem control_apply_m (h : 0 < psi) (l r : AgentState psi) :
    mp (singleUseApplyControl h l, singleUseApplyControl h r) = mp (l, r) := by
  unfold singleUseApplyControl mp mv wv
  try dsimp only
  repeat (first | rfl | split)
private theorem control_tail_m (h : 0 < psi) (l r : AgentState psi) :
    mp (singleUseControlTail h l r) = mp (l, r) := by
  unfold singleUseControlTail
  try dsimp only
  split
  · split
    · simpa only [mp, mv, wv] using control_apply_m h l r
    · exact control_apply_m h l r
  · exact control_apply_m h l r
private theorem done_m (h : 0 < psi) (l r : AgentState psi) :
    mp (doneCaptureSigMove h l r) = mp (l, r) := by
  unfold doneCaptureSigMove
  try dsimp only
  rw [control_tail_m, leader_wall_m, done_transfers_m, preclear_m]
private theorem done_am (h : 0 < psi) (l r : AuthorizedAgentState psi) :
    am (authorizedDoneMove h l r) = am (l, r) :=
  (congrArg mp (authorizedDoneMove_core h l r)).trans (done_m h l.core r.core)

private theorem reset_sanitize_am (h : 0 < psi)
    (q : AuthorizedAgentState psi × AuthorizedAgentState psi) :
    am (sanitizeAuthorizedPair h (preCheckResetWall q.1 q.2)) = am q := by
  unfold sanitizeAuthorizedPair sanitizeAuthorizedTerminalEqual preCheckResetWall
    clearAuthorizedComparison clearComparisonSignal am mp mv wv
  try dsimp only
  repeat (first | rfl | split)

private theorem check_ready_m (l r : AgentState psi) :
    mp (checkSigSetReady l, checkSigSetReady r) = mp (l, r) := by
  unfold checkSigSetReady mp mv wv
  try dsimp only
  repeat (first | rfl | split)
private theorem check_left_m (h : 0 < psi) (l r : AgentState psi) :
    mp (checkSigCheckL h l, r) = mp (l, r) := by
  unfold checkSigCheckL mp mv wv
  try dsimp only
  repeat (first | rfl | split)
private theorem check_right_m (h : 0 < psi) (l r : AgentState psi) :
    mp (l, checkSigCheckR h l r) = mp (l, r) := by
  unfold checkSigCheckR mp mv wv
  try dsimp only
  repeat (first | rfl | split)
private theorem check_result_m (l r : AgentState psi) :
    mp (checkSigSetResult l, checkSigSetResult r) = mp (l, r) := by
  unfold checkSigSetResult mp mv wv
  try dsimp only
  repeat (first | rfl | split)
private theorem check_leader_m (h : 0 < psi) (l r : AgentState psi) :
    mp (l, checkSigSetLeader h r) = mp (l, r) := by
  unfold checkSigSetLeader mp mv wv
  try dsimp only
  repeat (first | rfl | split)
private theorem check_m (h : 0 < psi) (l r : AgentState psi) :
    mp (checkSig h l r) = mp (l, r) := by
  rw [checkSig_eq_staged]
  unfold checkSigStaged
  try dsimp only
  rw [check_leader_m, check_result_m, check_right_m, check_left_m, check_ready_m]
private theorem guarded_check_am (h : 0 < psi) (l r : AuthorizedAgentState psi) :
    am (preserveDoneCheck h l r) = am (l, r) := by
  unfold preserveDoneCheck
  split
  · rfl
  · unfold preserveTossCheck
    split
    · rfl
    · unfold congestGuardCheck
      split
      · rfl
      · exact lift_frame _ (check_m h) l r

private theorem through_check_am (h : 0 < psi) (hw : 0 < width)
    (hle : width ≤ psi) (cap : Nat) (l r : AuthorizedAgentState psi) :
    am (doneThroughCheckEntryWidth h hw hle cap l r) =
      am (authorizedPPsiLeaderResetProbeWall h l r) := by
  let p := authorizedPPsiLeaderResetProbeWall h l r
  let g := authorizedGenCleanEntryWidth h hw hle cap p.1 p.2
  let c := authorizedCleanSig h g.1 g.2
  let e := authorizedEliminateSig h c.1 c.2
  let m := authorizedDoneMove h e.1 e.2
  let s := sanitizeAuthorizedPair h (preCheckResetWall m.1 m.2)
  let z := preserveDoneCheck h s.1 s.2

  have hg : am g = am p :=
    gen_entry_am h hw hle cap p.1 p.2
  have hc : am c = am g := clean_am h g.1 g.2
  have he : am e = am c := eliminate_am h c.1 c.2
  have hm : am m = am e := done_am h e.1 e.2
  have hs : am s = am m := reset_sanitize_am h m
  have hz : am z = am s := guarded_check_am h s.1 s.2

  have hstage : doneThroughCheckEntryWidth h hw hle cap l r = z := by
    rfl
  rw [hstage]
  exact hz.trans (hs.trans (hm.trans (he.trans (hc.trans hg))))

private theorem disappear_m (h : 0 < psi) (l r : AgentState psi) :
    mp (disappear h l r) = mp (l, r) := by
  unfold disappear mp mv wv
  try dsimp only
  repeat (first | rfl | split)
private theorem disappear_am (h : 0 < psi) (l r : AuthorizedAgentState psi) :
    am (authorizedDisappear h l r) = am (l, r) :=
  lift_frame _ (disappear_m h) l r
private theorem compare_init_m (u : AgentState psi) : mv (compareSigInit u) = mv u := by
  unfold compareSigInit mv wv
  repeat (first | rfl | split)
private theorem compare_set_m (h : 0 < psi) (u : AgentState psi) :
    mv (cmpUpdateSetPath2 h u) = mv u := by
  unfold cmpUpdateSetPath2 mv wv
  repeat (first | rfl | split)
private theorem compare_return_m (h : 0 < psi) (l r : AgentState psi) :
    mp (cmpUpdateReturnPriority h l r) = mp (l, r) := by
  unfold cmpUpdateReturnPriority mp mv wv
  try dsimp only
  repeat (first | rfl | split)
private theorem compare_update_am (h : 0 < psi) (l r : AuthorizedAgentState psi) :
    am (authorizedCmpUpdate h l r) = am (l, r) := by
  let lc := if freshComparisonStart h l && !comparisonActive l.core.state then
      { l.core with state := .congest } else l.core
  let q := cmpUpdateReturnPriority h lc r.core
  have hc : mv lc = mv l.core := by unfold lc; split <;> rfl
  have ht : mp (cmpUpdateSetPath2 h q.1, q.2) = mp q :=
    Prod.ext (compare_set_m h q.1) rfl
  change mp (cmpUpdateSetPath2 h q.1, q.2) = mp (l.core, r.core)
  exact ht.trans ((compare_return_m h lc r.core).trans (Prod.ext hc rfl))
private theorem compare_left_m (h : 0 < psi) (u : AgentState psi) :
    mv (compareBitUpdateL h u) = mv u := by
  unfold compareBitUpdateL mv wv
  repeat (first | rfl | split)
private theorem compare_right_m (h : 0 < psi) (u : AgentState psi) :
    mv (compareBitUpdateRActionOne h u) = mv u := by
  simp only [compareBitUpdateRActionOne, compareBitUpdateR, mv, wv]
  repeat (first | rfl | split)
private theorem compare_pair_m (h : 0 < psi) (l r : AgentState psi) :
    mp (compareBitActionOne h l r) = mp (l, r) :=
  Prod.ext (compare_left_m h l) (compare_right_m h r)
private theorem compare_dispatch_m (h : 0 < psi) (l r : AgentState psi) :
    mp (compareSigDispatchActionOne h l r) = mp (l, r) := by
  unfold compareSigDispatchActionOne
  repeat (first | exact compare_pair_m h l r | rfl | split)
private theorem compare_am (h : 0 < psi) (l r : AuthorizedAgentState psi) :
    am (authorizedCompareSigActionOne h l r) = am (l, r) := by
  let l0 : AuthorizedAgentState psi :=
    ⟨compareSigInit l.core, normalizePermit (compareSigInit l.core) l.path0Crossed⟩
  have hi : am (l0, r) = am (l, r) := Prod.ext (compare_init_m l.core) rfl
  unfold authorizedCompareSigActionOne
  try dsimp only
  split
  · exact hi
  · split
    · exact hi
    · let q := authorizedCmpUpdate h l0 r
      change mp (compareSigDispatchActionOne h q.1.core q.2.core) = am (l, r)
      exact (compare_dispatch_m h q.1.core q.2.core).trans
        ((compare_update_am h l0 r).trans hi)

private theorem suppress_start_m (l r : AgentState psi) :
    mp (suppressSigStart l r) = mp (l, r) := by
  unfold suppressSigStart mp mv wv
  try dsimp only
  repeat (first | rfl | split)
private theorem reset_kill_m (l r : AgentState psi) :
    mp (resetKillComparison l, resetKillComparison r) = mp (l, r) := by
  unfold resetKillComparison clearComparisonSignal mp mv wv
  try dsimp only
  repeat (first | rfl | split)
private theorem suppress_move_m (l r : AgentState psi) :
    mp (suppressSigMoveReset l r) = mp (l, r) := by
  unfold suppressSigMoveReset mp mv wv
  try dsimp only
  repeat (first | rfl | split)
private theorem short_count_m (hw : 0 < width) (hle : width ≤ psi)
    (l r : AgentState psi) : mp (shortCountReset hw hle l r) = mp (l, r) := by
  unfold shortCountReset mp mv wv
  try dsimp only
  repeat (first | rfl | split)
private theorem suppress_terminal_m (h : 0 < psi) (l r : AgentState psi) :
    mp (suppressSigTerminal h l r) = mp (l, r) := by
  unfold suppressSigTerminal mp mv wv
  try dsimp only
  repeat (first | rfl | split)
private theorem suppress_echo_m (l r : AgentState psi) :
    mp (suppressSigEcho l r) = mp (l, r) := by
  unfold suppressSigEcho mp mv wv
  try dsimp only
  repeat (first | rfl | split)
private theorem suppress_finish_m (l r : AgentState psi) :
    mp (suppressSigFinish l r) = mp (l, r) := by
  unfold suppressSigFinish mp mv wv
  try dsimp only
  repeat (first | rfl | split)
private theorem suppress_prefix_m (l r : AgentState psi) :
    mp (suppressPrefix l r) = mp (l, r) := by
  unfold suppressPrefix
  try dsimp only
  rw [reset_kill_m, suppress_move_m, reset_kill_m, suppress_start_m]
private theorem suppress_m (h : 0 < psi) (hw : 0 < width)
    (hle : width ≤ psi) (l r : AgentState psi) :
    mp (suppressSigResetKillWidth h hw hle l r) = mp (l, r) := by
  unfold suppressSigResetKillWidth
  try dsimp only
  rw [suppress_finish_m, suppress_echo_m, suppress_terminal_m,
    short_count_m, suppress_prefix_m]
private theorem suppress_am (h : 0 < psi) (hw : 0 < width)
    (hle : width ≤ psi) (l r : AuthorizedAgentState psi) :
    am (authorizedSuppressWidth h hw hle l r) = am (l, r) :=
  lift_frame _ (suppress_m h hw hle) l r
private theorem before_write_stage (h : 0 < psi) (hw : 0 < width)
    (hle : width ≤ psi) (l r : AuthorizedAgentState psi) :
    beforeWriteWidth h hw hle l r =
      let d := authorizedDisappear h l r
      let c := authorizedCompareSigActionOne h d.1 d.2
      authorizedSuppressWidth h hw hle c.1 c.2 := by
  rfl

private theorem before_write_am (h : 0 < psi) (hw : 0 < width)
    (hle : width ≤ psi) (l r : AuthorizedAgentState psi) :
    am (beforeWriteWidth h hw hle l r) = am (l, r) := by
  let d := authorizedDisappear h l r
  let c := authorizedCompareSigActionOne h d.1 d.2
  have hd : am d = am (l, r) := disappear_am h l r
  have hc : am c = am d := compare_am h d.1 d.2
  have hs : am (authorizedSuppressWidth h hw hle c.1 c.2) = am c :=
    suppress_am h hw hle c.1 c.2
  rw [before_write_stage h hw hle l r]
  exact hs.trans (hc.trans hd)


private theorem through_check_preWriter_frame_fast
    (h : 0 < psi) (hw : 0 < width) (hle : width ≤ psi)
    (cap : Nat) (l r : AuthorizedAgentState psi) :
    B6PreWriterFramesA.PreWriterFrame
        (doneThroughCheckEntryWidth h hw hle cap l r) =
      B6PreWriterFramesA.PreWriterFrame
        (authorizedPPsiLeaderResetProbeWall h l r) := by
  let p := authorizedPPsiLeaderResetProbeWall h l r
  let g := authorizedGenCleanEntryWidth h hw hle cap p.1 p.2
  let c := authorizedCleanSig h g.1 g.2
  let e := authorizedEliminateSig h c.1 c.2
  let m := authorizedDoneMove h e.1 e.2
  let s := sanitizeAuthorizedPair h (preCheckResetWall m.1 m.2)
  let z := preserveDoneCheck h s.1 s.2

  have hg :
      B6PreWriterFramesA.PreWriterFrame g =
        B6PreWriterFramesA.PreWriterFrame p :=
    B6PreWriterFramesA.genEntry_frame h hw hle cap p.1 p.2
  have hc :
      B6PreWriterFramesA.PreWriterFrame c =
        B6PreWriterFramesA.PreWriterFrame g :=
    B6PreWriterFramesB.clean_frame h g.1 g.2
  have he :
      B6PreWriterFramesA.PreWriterFrame e =
        B6PreWriterFramesA.PreWriterFrame c :=
    B6PreWriterFramesB.eliminate_frame h c.1 c.2
  have hm :
      B6PreWriterFramesA.PreWriterFrame m =
        B6PreWriterFramesA.PreWriterFrame e :=
    B6PreWriterFramesB.doneMove_frame h e.1 e.2
  have hs :
      B6PreWriterFramesA.PreWriterFrame s =
        B6PreWriterFramesA.PreWriterFrame m :=
    B6PreWriterFramesC.resetSanitize_frame h m
  have hz :
      B6PreWriterFramesA.PreWriterFrame z =
        B6PreWriterFramesA.PreWriterFrame s :=
    B6PreWriterFramesC.preserveDoneCheck_frame h s.1 s.2

  have hstage : doneThroughCheckEntryWidth h hw hle cap l r = z := by
    rfl
  rw [hstage]
  calc
    B6PreWriterFramesA.PreWriterFrame z =
        B6PreWriterFramesA.PreWriterFrame s := hz
    _ = B6PreWriterFramesA.PreWriterFrame m := hs
    _ = B6PreWriterFramesA.PreWriterFrame e := hm
    _ = B6PreWriterFramesA.PreWriterFrame c := he
    _ = B6PreWriterFramesA.PreWriterFrame g := hc
    _ = B6PreWriterFramesA.PreWriterFrame p := hg


private theorem permitFix_preWriter_frame
    (c : AuthorizedAgentState psi × AuthorizedAgentState psi) :
    B6PreWriterFramesA.PreWriterFrame
        (BirthCheckPermitRepair.permitFix c.1, c.2) =
      B6PreWriterFramesA.PreWriterFrame c := by
  unfold B6PreWriterFramesA.PreWriterFrame
  change B6PreWriterFramesA.rawPreWriterFrame
      ((BirthCheckPermitRepair.permitFix c.1).core, c.2.core) =
    B6PreWriterFramesA.rawPreWriterFrame (c.1.core, c.2.core)
  rw [BirthCheckPermitRepair.permitFix_core]

private theorem before_write_preWriter_frame_fast
    (h : 0 < psi) (hw : 0 < width) (hle : width ≤ psi)
    (l r : AuthorizedAgentState psi) :
    B6PreWriterFramesA.PreWriterFrame (beforeWriteWidth h hw hle l r) =
      B6PreWriterFramesA.PreWriterFrame (l, r) := by
  let d := authorizedDisappear h l r
  let c := authorizedCompareSigActionOne h d.1 d.2
  have hd := B6PreWriterFramesC.disappear_frame h l r
  have hc := B6PreWriterFramesC.compare_frame h d.1 d.2
  have hs := B6PreWriterFramesC.suppress_frame h hw hle c.1 c.2
  rw [before_write_stage h hw hle l r]
  exact hs.trans (hc.trans hd)

private theorem input_preWriter_frame_fast
    (h : 0 < psi) (hw : 0 < width) (hle : width ≤ psi)
    (cap : Nat) (l r : AuthorizedAgentState psi) :
    B6PreWriterFramesA.PreWriterFrame
        (B6WriterSilence.r1WriterInput h hw hle cap l r) =
      B6PreWriterFramesA.PreWriterFrame
        (authorizedPPsiLeaderResetProbeWall h l r) := by
  let c := doneThroughCheckEntryWidth h hw hle cap l r
  let f := BirthCheckPermitRepair.permitFix c.1
  let w := beforeWriteWidth h hw hle f c.2
  have hc := through_check_preWriter_frame_fast h hw hle cap l r
  have hf : B6PreWriterFramesA.PreWriterFrame (f, c.2) =
      B6PreWriterFramesA.PreWriterFrame c := by
    exact permitFix_preWriter_frame c
  have hwf := before_write_preWriter_frame_fast h hw hle f c.2
  have hdef : B6WriterSilence.r1WriterInput h hw hle cap l r = w := by
    rfl
  rw [hdef]
  exact hwf.trans (hf.trans hc)

private theorem input_am (h : 0 < psi) (hw : 0 < width)
    (hle : width ≤ psi) (cap : Nat) (l r : AuthorizedAgentState psi) :
    am (B6WriterSilence.r1WriterInput h hw hle cap l r) =
      am (authorizedPPsiLeaderResetProbeWall h l r) := by
  have hc :
      am (doneThroughCheckEntryWidth h hw hle cap l r) =
        am (authorizedPPsiLeaderResetProbeWall h l r) :=
    through_check_am h hw hle cap l r
  simp only [B6WriterSilence.r1WriterInput]
  generalize doneThroughCheckEntryWidth h hw hle cap l r = c at hc ⊢
  have hf :
      am (BirthCheckPermitRepair.permitFix c.1, c.2) = am c := by
    unfold am
    rw [BirthCheckPermitRepair.permitFix_core]
  calc
    am (beforeWriteWidth h hw hle
        (BirthCheckPermitRepair.permitFix c.1) c.2) =
        am (BirthCheckPermitRepair.permitFix c.1, c.2) :=
      before_write_am h hw hle (BirthCheckPermitRepair.permitFix c.1) c.2
    _ = am c := hf
    _ = am (authorizedPPsiLeaderResetProbeWall h l r) := hc



private theorem ordinary_stage_eq (h : 0 < psi) (hw : 0 < width)
    (hle : width ≤ psi) (cap : Nat) (l r : AuthorizedAgentState psi) :
    BirthCheckPermitRepair.ordinary h hw hle cap l r =
      (let p := B6WriterSilence.r1WriterInput h hw hle cap l r
       let w := stationaryPersistentAuthorizedRow h p.1 p.2
       markLeaderBirth (authBirth l r w) w) := by
  rfl

private theorem expiring_stage_eq (h : 0 < psi) (hw : 0 < width)
    (hle : width ≤ psi)
    (l r : ExpiringAgentState psi kappa tau) :
    BirthCheckPermitRepair.expiring h hw hle l r =
      (let l0 := prepareExpiringDisposal h l
       let r0 := prepareExpiringDisposal h r
       let q := BirthCheckPermitRepair.bounded h hw hle l0.core r0.core
       (deletionPriorityExpireOne tau l0 ⟨q.1, l0.stall⟩,
        deletionPriorityExpireOne tau r0 ⟨q.2, r0.stall⟩)) := by
  rfl

private theorem row_stage_eq (h : 0 < psi) (hw : 0 < width)
    (hle : width ≤ psi)
    (l r : ExpiringAgentState psi kappa tau) :
    BirthCheckPermitRepair.row h hw hle l r =
      finalPhysical h l r
        (normalizeLeader h (BirthCheckPermitRepair.expiring h hw hle l r).1)
        (normalizeLeader h (BirthCheckPermitRepair.expiring h hw hle l r).2) := by
  rfl

attribute [local irreducible]
  BirthShortDoneTerminalEntryCut.generationBeforeMoveEntryWidth
  BirthShortDoneTerminalEntryCut.doneBeforeCheckEntryWidth
  BirthShortDoneTerminalEntryCut.doneThroughCheckEntryWidth
  BirthShortDoneCuts.beforeWriteWidth
  BirthShortDoneCuts.afterCheckMetadataWidth
  B6WriterSilence.r1WriterInput
  BirthCheckPermitRepair.permitFix
  BirthCheckPermitRepair.ordinary
  BirthCheckPermitRepair.expiring
  BirthCheckPermitRepair.row

private theorem pprime_w (h : 0 < psi) (l r : AgentState psi) :
    wp (pPsiLeaderResetProbeWall h l r) = wp (l, r) := by
  unfold pPsiLeaderResetProbeWall pPsi wp wv
  try dsimp only
  repeat (first | rfl | split)

private theorem pprime_root_labels_raw (h : 0 < psi) (h3 : 2 < psi)
    (l r : AgentState psi) (hl : l.leader = true)
    (nl : Normalized l) (nr : Normalized r) :
    let q := pPsiLeaderResetProbeWall h l r
    q.1.label.val = 0 ∧ (q.2.label.val = 0 ∨ q.2.label.val = 1) := by
  have hz := nl hl
  have h1 : 1 < psi := by omega
  cases hr : r.leader with
  | false =>
      have hf := pPsiLeaderResetProbeWall_source_follower_normalizes
        h l r (Or.inl hl) hr
      refine ⟨(congrArg Fin.val hf.2.2.1).trans hz, Or.inr ?_⟩
      have he := congrArg Fin.val hf.2.2.2.1
      change (pPsiLeaderResetProbeWall h l r).2.label.val =
        (l.label.val + 1) % psi at he
      simpa only [hz, Nat.zero_add, Nat.mod_eq_of_lt h1] using he
  | true =>
      have hlz : l.label = ⟨0, h⟩ := Fin.ext hz
      have hrz : r.label = ⟨0, h⟩ := Fin.ext (nr hr)
      simp [pPsiLeaderResetProbeWall, pPsi, hl, hr, hlz, hrz,
        Fin.ext_iff, Nat.mod_eq_of_lt h1]

private theorem pprime_root_labels (h : 0 < psi) (h3 : 2 < psi)
    (l r : AuthorizedAgentState psi) (hl : l.core.leader = true)
    (nl : Normalized l.core) (nr : Normalized r.core) :
    let p := authorizedPPsiLeaderResetProbeWall h l r
    p.1.core.label.val = 0 ∧
      (p.2.core.label.val = 0 ∨ p.2.core.label.val = 1) := by
  have hc := authorizedPPsiLeaderResetProbeWall_core h l r
  have hp := pprime_root_labels_raw h h3 l.core r.core hl nl nr
  have hL := congrArg (fun q : AgentState psi × AgentState psi => q.1.label.val) hc
  have hR := congrArg (fun q : AgentState psi × AgentState psi => q.2.label.val) hc
  refine ⟨hL.trans hp.1, ?_⟩
  rcases hp.2 with hz | ho
  · exact Or.inl (hR.trans hz)
  · exact Or.inr (hR.trans ho)
private def EmptyCommand (u : AgentState psi) : Prop :=
  u.path3 = none ∧ u.write = .none
private def Idle (u : AgentState psi) : Prop :=
  u.path3 = none ∧ u.write = .none ∧ u.write_state = .none
private def WriterGeometry (l r : AgentState psi) : Prop :=
  l.leader = true → l.label.val = 0 ∧ (r.label.val = 0 ∨ r.label.val = 1)

private theorem generate_empty (h : 0 < psi) (h3 : 2 < psi)
    (l r : AgentState psi) (hl : WriterPassive l) (hr : WriterPassive r)
    (hg : WriterGeometry l r) :
    let q := writeSeqGenerate h l r
    EmptyCommand q.1 ∧ EmptyCommand q.2 ∧
      q.1.bit = l.bit ∧ q.2.bit = r.bit := by
  by_cases hcall : l.leader = true ∧ l.gen_ws = true
  · obtain ⟨hz, hrlab⟩ := hg hcall.1
    have h0 : (0 : Nat) ≠ psi - 1 := by omega
    have h1 : (1 : Nat) ≠ psi - 1 := by omega
    rcases hrlab with hrz | hrz <;>
      rcases hr.2.2 with hrs | hrs <;>
      simp [writeSeqGenerate, gensigWriteseq, hcall.1, hcall.2,
        Fin.ext_iff, hz, hrz, h0, h1, hl.1, hl.2.1,
        hr.1, hr.2.1, hrs, EmptyCommand]
  · simpa [writeSeqGenerate, hcall] using
      (show EmptyCommand l ∧ EmptyCommand r from
        ⟨⟨hl.1, hl.2.1⟩, ⟨hr.1, hr.2.1⟩⟩)


private theorem prepare_empty (h : 0 < psi) (l r : AgentState psi)
    (hl : EmptyCommand l) (hr : EmptyCommand r) :
    let q := writeSeqPrepareTransport h l r
    Idle q.1 ∧ Idle q.2 ∧ q.1.bit = l.bit ∧ q.2.bit = r.bit := by
  simp [writeSeqPrepareTransport, writeSeqReadyTransport,
    writeSeqSetWriteReadyTransport, writeSeqCompare, writeSeqCommands,
    writeSeqSetWriteAct, Idle, hl.1, hl.2, hr.1, hr.2]


private theorem action_idle (h : 0 < psi) (l r : AgentState psi)
    (hl : Idle l) (hr : Idle r) : WG l r (writeActionPreservingComparison h l r) := by
  have al : writeActionActivateNonempty h l = l := by
    simp [writeActionActivateNonempty, hl.2.1]
  have ar : writeActionActivateNonempty h r = r := by
    simp [writeActionActivateNonempty, hr.2.1]
  rw [writeActionPreservingComparison, al, ar]
  unfold writeActionExecutePreservingComparison
  rw [if_neg (by simp [hr.2.2])]
  unfold writeActionExecutePreservingDepart
  split
  · simp [hr.2.2, WG, Good, WriterPassive, hl.1, hl.2.1, hl.2.2,
      hr.1, hr.2.1]
  · exact ⟨⟨⟨hl.1, hl.2.1, Or.inl hl.2.2⟩, rfl⟩,
      ⟨⟨hr.1, hr.2.1, Or.inl hr.2.2⟩, rfl⟩⟩

private theorem leader_signal_w (l r : AgentState psi) :
    wp (moveWsigLeaderSignal l r) = wp (l, r) := by
  unfold moveWsigLeaderSignal wp wv
  try dsimp only
  repeat (first | rfl | split)
private theorem signal_move_w (l r : AgentState psi) :
    wp (moveWsigSignalMove l r) = wp (l, r) := by
  unfold moveWsigSignalMove wp wv
  try dsimp only
  repeat (first | rfl | split)
private theorem echo_move_w (l r : AgentState psi) :
    wp (moveWsigEchoMove l r) = wp (l, r) := by
  unfold moveWsigEchoMove wp wv
  try dsimp only
  repeat (first | rfl | split)
private theorem finish_w (l r : AgentState psi) (hlw : l.write = .none) :
    wp (moveWsigFinishPreservingCommand l r) = wp (l, r) := by
  unfold moveWsigFinishPreservingCommand
  try dsimp only
  rw [echo_move_w, signal_move_w, leader_signal_w,
    moveWsigMoveWritePreservingNonempty_of_empty l r hlw]

private theorem move_start_good (l r : AgentState psi)
    (hl : WriterPassive l) (hr : WriterPassive r) : WG l r (moveWsigStart l r) := by
  unfold moveWsigStart
  split
  · have he : moveWsigCheckGenWs l r = r := by
      simp [moveWsigCheckGenWs, hl.1]
    simp only [he]
    exact ⟨⟨⟨rfl, rfl, Or.inl rfl⟩, rfl⟩, ⟨hr, rfl⟩⟩
  · exact ⟨⟨hl, rfl⟩, ⟨hr, rfl⟩⟩

private theorem move_good (h : 0 < psi) (l r : AgentState psi)
    (hl : WriterPassive l) (hr : WriterPassive r) : WG l r (moveWsigStopAligned h l r) := by
  let q := moveWsigStart l r
  have hq : WG l r q := move_start_good l r hl hr
  have hc : moveWsigCheckLast q.1 = q.1 := by
    simp [moveWsigCheckLast, hq.1.1.1]
  have ht : moveWsigTransferStopAligned q.1 q.2 = (q.1, q.2) := by
    simp [moveWsigTransferStopAligned, hq.1.1.1]
  change WG l r (moveWsigFinishPreservingCommand
    (moveWsigTransferStopAligned (moveWsigCheckLast q.1) q.2).1
    (moveWsigTransferStopAligned (moveWsigCheckLast q.1) q.2).2)
  rw [hc, ht]
  have hf := finish_w q.1 q.2 hq.1.1.2.1
  exact ⟨good_of_wv (congrArg Prod.fst hf) hq.1,
    good_of_wv (congrArg Prod.snd hf) hq.2⟩

private theorem suffix_idle (h : 0 < psi) (l r : AgentState psi)
    (hl : Idle l) (hr : Idle r) :
    WG l r (writeSeqAfterPrepareComparisonTransport h l r) := by
  let q := writeActionPreservingComparison h l r
  have hq : WG l r q := action_idle h l r hl hr
  exact wg_trans l r q (moveWsigStopAligned h q.1 q.2) hq
    (move_good h q.1 q.2 hq.1.1 hq.2.1)

private theorem group_m (h : 0 < psi) (l r : AgentState psi) :
    mp (groupInfo h l r) = mp (l, r) := by
  unfold groupInfo mp mv wv
  try dsimp only
  repeat (first | rfl | split)
private theorem group_left_leader (h : 0 < psi) (l r : AgentState psi) :
    (groupInfo h l r).1.leader = l.leader := by
  unfold groupInfo
  try dsimp only
  repeat (first | rfl | split)

private theorem stationary_good (h : 0 < psi) (h3 : 2 < psi)
    (l r : AgentState psi) (hl : WriterPassive l) (hr : WriterPassive r)
    (hg : WriterGeometry l r) : WG l r (stationaryPersistentRaw h l r) := by
  have hclear : clearInputIncrementPair l r = (l, r) := by
    simp [clearInputIncrementPair, clearIncrementAction, hl.2.1, hr.2.1]
  let g := groupInfo h l r
  have gm : mp g = mp (l, r) := group_m h l r
  have gl : WriterPassive g.1 := passive_of_wv
    (congrArg (fun z : MP psi => z.1.2) gm) hl
  have gr : WriterPassive g.2 := passive_of_wv
    (congrArg (fun z : MP psi => z.2.2) gm) hr
  have gg : WriterGeometry g.1 g.2 := by
    intro ht
    obtain ⟨hz, hs⟩ := hg ((group_left_leader h l r).symm.trans ht)
    refine ⟨(congrArg (fun z : MP psi => z.1.1.val) gm).trans hz, ?_⟩
    rcases hs with hs | hs
    · exact Or.inl ((congrArg (fun z : MP psi => z.2.1.val) gm).trans hs)
    · exact Or.inr ((congrArg (fun z : MP psi => z.2.1.val) gm).trans hs)
  let a := writeSeqGenerate h g.1 g.2
  have ha := generate_empty h h3 g.1 g.2 gl gr gg
  change EmptyCommand a.1 ∧ EmptyCommand a.2 ∧
    a.1.bit = g.1.bit ∧ a.2.bit = g.2.bit at ha
  let p := writeSeqPrepareTransport h a.1 a.2
  have hp := prepare_empty h a.1 a.2 ha.1 ha.2.1
  change Idle p.1 ∧ Idle p.2 ∧ p.1.bit = a.1.bit ∧ p.2.bit = a.2.bit at hp
  have gpl : gatePreparedIncrement p.1 = p.1 := by
    simp [gatePreparedIncrement, hp.1.2.1]
  have gpr : gatePreparedIncrement p.2 = p.2 := by
    simp [gatePreparedIncrement, hp.2.1.2.1]
  have hs := suffix_idle h p.1 p.2 hp.1 hp.2.1
  have b1 : p.1.bit = l.bit := hp.2.2.1.trans
    (ha.2.2.1.trans (congrArg (fun z : MP psi => z.1.2.bit) gm))
  have b2 : p.2.bit = r.bit := hp.2.2.2.trans
    (ha.2.2.2.trans (congrArg (fun z : MP psi => z.2.2.bit) gm))
  unfold stationaryPersistentRaw swPersistentThroughPrepare
  rw [hclear]
  change WG l r (writeSeqAfterPrepareComparisonTransport h
    (gatePreparedIncrement p.1) (gatePreparedIncrement p.2))
  rw [gpl, gpr]
  exact ⟨⟨hs.1.1, hs.1.2.trans b1⟩, ⟨hs.2.1, hs.2.2.trans b2⟩⟩
private theorem input_good (h : 0 < psi) (h3 : 2 < psi)
    (hw : 0 < width) (hle : width ≤ psi) (cap : Nat)
    (l r : AuthorizedAgentState psi)
    (hl : WriterPassive l.core) (hr : WriterPassive r.core)
    (nl : Normalized l.core) (nr : Normalized r.core) :
    let w := B6WriterSilence.r1WriterInput h hw hle cap l r
    WG l.core r.core (w.1.core, w.2.core) ∧ WriterGeometry w.1.core w.2.core := by
  let p := authorizedPPsiLeaderResetProbeWall h l r
  let w := B6WriterSilence.r1WriterInput h hw hle cap l r
  have hm : am w = am p := input_am h hw hle cap l r
  have pc := authorizedPPsiLeaderResetProbeWall_core h l r
  have pw := pprime_w h l.core r.core
  have pl : wv p.1.core = wv l.core :=
    (congrArg (fun q : AgentState psi × AgentState psi => wv q.1) pc).trans
      (congrArg Prod.fst pw)
  have pr : wv p.2.core = wv r.core :=
    (congrArg (fun q : AgentState psi × AgentState psi => wv q.2) pc).trans
      (congrArg Prod.snd pw)
  have wl : wv w.1.core = wv l.core :=
    (congrArg (fun z : MP psi => z.1.2) hm).trans pl
  have wr : wv w.2.core = wv r.core :=
    (congrArg (fun z : MP psi => z.2.2) hm).trans pr
  -- Reuse the existing exact R1 bit/payload frame, not an old-host cut.
  have hb := B6WriterSilence.r1WriterInput_fields h hw hle cap l r
  refine ⟨⟨⟨passive_of_wv wl hl, hb.1⟩,
    ⟨passive_of_wv wr hr, hb.2.1⟩⟩, ?_⟩
  intro hlead
  have oldlead : l.core.leader = true :=
    (B6WriterSilence.r1WriterInput_left_leader h hw hle cap l r).symm.trans hlead
  have hp := pprime_root_labels h h3 l r oldlead nl nr
  refine ⟨(congrArg (fun z : MP psi => z.1.1.val) hm).trans hp.1, ?_⟩
  rcases hp.2 with hz | ho
  · exact Or.inl ((congrArg (fun z : MP psi => z.2.1.val) hm).trans hz)
  · exact Or.inr ((congrArg (fun z : MP psi => z.2.1.val) hm).trans ho)

private theorem mark_m (born : Bool)
    (q : AuthorizedAgentState psi × AuthorizedAgentState psi) :
    am (markLeaderBirth born q) = am q := by
  unfold markLeaderBirth markComparisonForDeletion am mp mv wv
  try dsimp only
  repeat (first | rfl | split)

private theorem ordinary_stage (h : 0 < psi) (hw : 0 < width)
    (hle : width ≤ psi) (cap : Nat) (l r : AuthorizedAgentState psi) :
    BirthCheckPermitRepair.ordinary h hw hle cap l r =
      (let p := B6WriterSilence.r1WriterInput h hw hle cap l r
       let w := stationaryPersistentAuthorizedRow h p.1 p.2
       markLeaderBirth (authBirth l r w) w) :=
  ordinary_stage_eq h hw hle cap l r


private theorem ordinary_good (h : 0 < psi) (h3 : 2 < psi)
    (hw : 0 < width) (hle : width ≤ psi) (cap : Nat)
    (l r : AuthorizedAgentState psi)
    (hl : WriterPassive l.core) (hr : WriterPassive r.core)
    (nl : Normalized l.core) (nr : Normalized r.core) :
    let q := BirthCheckPermitRepair.ordinary h hw hle cap l r
    WG l.core r.core (q.1.core, q.2.core) := by
  let p := B6WriterSilence.r1WriterInput h hw hle cap l r
  have hp := input_good h h3 hw hle cap l r hl hr nl nr
  change WG l.core r.core (p.1.core, p.2.core) ∧
    WriterGeometry p.1.core p.2.core at hp
  have hwraw :=
    stationary_good h h3 p.1.core p.2.core hp.1.1.1 hp.1.2.1 hp.2
  let w := stationaryPersistentAuthorizedRow h p.1 p.2
  have hwcore :
      (w.1.core, w.2.core) = stationaryPersistentRaw h p.1.core p.2.core :=
    stationaryPersistentAuthorizedRow_core h p.1 p.2
  have hW : WG p.1.core p.2.core (w.1.core, w.2.core) := by
    rw [hwcore]
    exact hwraw
  have hwold := wg_trans l.core r.core (p.1.core, p.2.core)
    (w.1.core, w.2.core) hp.1 hW
  rw [ordinary_stage h hw hle cap l r]
  change WG l.core r.core
    ((markLeaderBirth (authBirth l r w) w).1.core,
     (markLeaderBirth (authBirth l r w) w).2.core)
  have hm := mark_m (authBirth l r w) w
  exact ⟨good_of_mv (congrArg Prod.fst hm) hwold.1,
    good_of_mv (congrArg Prod.snd hm) hwold.2⟩


private theorem normalize_deletion_m (u : AuthorizedAgentState psi) :
    mv (normalizeDeletion u).core = mv u.core ∧
      (normalizeDeletion u).core.leader = u.core.leader := by
  constructor
  · unfold normalizeDeletion
    split
    · unfold mv wv
      rfl
    · rfl
  · unfold normalizeDeletion
    split <;> rfl


private theorem authorized_good (h : 0 < psi) (h3 : 2 < psi)
    (hw : 0 < width) (hle : width ≤ psi) (cap : Nat)
    (l r : AuthorizedAgentState psi)
    (hl : WriterPassive l.core) (hr : WriterPassive r.core)
    (nl : Normalized l.core) (nr : Normalized r.core) :
    let q := BirthCheckPermitRepair.authorized h hw hle cap l r
    WG l.core r.core (q.1.core, q.2.core) := by
  have fl := normalize_deletion_m l
  have fr := normalize_deletion_m r
  simp only [BirthCheckPermitRepair.authorized]
  generalize normalizeDeletion l = l0 at fl ⊢
  generalize normalizeDeletion r = r0 at fr ⊢
  have gl : Good l.core l0.core := good_of_mv fl.1 ⟨hl, rfl⟩
  have gr : Good r.core r0.core := good_of_mv fr.1 ⟨hr, rfl⟩
  have nl0 : Normalized l0.core := normalized_of_mv fl.1 fl.2 nl
  have nr0 : Normalized r0.core := normalized_of_mv fr.1 fr.2 nr
  split
  · have hf := eliminate_am h l0 r0
    exact ⟨good_of_mv (congrArg Prod.fst hf) gl,
      good_of_mv (congrArg Prod.snd hf) gr⟩
  · split
    · exact ⟨gl, gr⟩
    · exact wg_trans l.core r.core (l0.core, r0.core) _ ⟨gl, gr⟩
        (ordinary_good h h3 hw hle cap l0 r0 gl.1 gr.1 nl0 nr0)

private theorem bounded_erase (h : 0 < psi) (hw : 0 < width)
    (hle : width ≤ psi) (l r : AuthorizedBoundedAgentState psi kappa) :
    ((BirthCheckPermitRepair.bounded h hw hle l r).1.erase,
     (BirthCheckPermitRepair.bounded h hw hle l r).2.erase) =
      BirthCheckPermitRepair.authorized h hw hle kappa l.erase r.erase := by
  simp only [BirthCheckPermitRepair.bounded, AuthorizedBoundedAgentState.erase,
    BoundedAgentState.erase_ofDomain] <;> rfl

private theorem disposal_m (h : 0 < psi) (u : AuthorizedAgentState psi) :
    mv (prepareDisposal h u).core = mv u.core ∧
      (prepareDisposal h u).core.leader = u.core.leader := by
  constructor
  · unfold prepareDisposal
    split
    · unfold markComparisonForDeletion
      split
      · rfl
      · unfold mv wv
        rfl
    · rfl
  · unfold prepareDisposal
    split
    · unfold markComparisonForDeletion
      split <;> rfl
    · rfl


private theorem prepared_m (h : 0 < psi) (u : ExpiringAgentState psi kappa tau) :
    mv (raw (prepareExpiringDisposal h u)) = mv (raw u) ∧
      (raw (prepareExpiringDisposal h u)).leader = (raw u).leader := by
  change mv (prepareBoundedDisposal h u.core).erase.core = mv u.core.erase.core ∧
    (prepareBoundedDisposal h u.core).erase.core.leader = u.core.erase.core.leader
  simpa only [erase_prepareBoundedDisposal] using disposal_m h u.core.erase

private theorem expiry_w (old out : ExpiringAgentState psi kappa tau) :
    ew (deletionPriorityExpireOne tau old out) = ew out := by
  unfold deletionPriorityExpireOne pathExpireOne clearComparisonCarrier ew raw wv
  try dsimp only
  repeat (first | rfl | split)

private theorem normalize_w (h : 0 < psi) (u : ExpiringAgentState psi kappa tau) :
    ew (normalizeLeader h u) = ew u := by
  have hf := congrArg (fun z : ExpiringAgentState psi kappa tau => ew z)
    (normalizeLeader_field_frame h u)
  exact hf

private theorem putSignals_ew
    (u : ExpiringAgentState psi kappa tau) (v : AgentState 1) :
    ew (ExpiringK2Projection.putSignals u v) = ew u := by
  rfl

private theorem putSignals_raw_label
    (u : ExpiringAgentState psi kappa tau) (v : AgentState 1) :
    (raw (ExpiringK2Projection.putSignals u v)).label = (raw u).label := by
  rfl

private theorem final_w (h : 0 < psi)
    (oldL oldR metaL metaR : ExpiringAgentState psi kappa tau) :
    let q := finalPhysical h oldL oldR metaL metaR
    ew q.1 = ew metaL ∧ ew q.2 = ew metaR := by
  have hf := finalPhysical_frame h oldL oldR metaL metaR
  have hL := congrArg
    (fun z : ExpiringAgentState psi kappa tau => ew z) hf.1
  have hR := congrArg
    (fun z : ExpiringAgentState psi kappa tau => ew z) hf.2
  constructor
  · simpa only [putSignals_ew] using hL
  · simpa only [putSignals_ew] using hR

private theorem expiring_good (h : 0 < psi) (h3 : 2 < psi)
    (hw : 0 < width) (hle : width ≤ psi)
    (l r : ExpiringAgentState psi kappa tau)
    (hl : WriterPassive (raw l)) (hr : WriterPassive (raw r))
    (nl : Normalized (raw l)) (nr : Normalized (raw r)) :
    let q := BirthCheckPermitRepair.expiring h hw hle l r
    WG (raw l) (raw r) (raw q.1, raw q.2) := by
  let l0 := prepareExpiringDisposal h l
  let r0 := prepareExpiringDisposal h r
  have fl := prepared_m h l
  have fr := prepared_m h r
  have gl : Good (raw l) (raw l0) := good_of_mv fl.1 ⟨hl, rfl⟩
  have gr : Good (raw r) (raw r0) := good_of_mv fr.1 ⟨hr, rfl⟩
  have nl0 : Normalized (raw l0) := normalized_of_mv fl.1 fl.2 nl
  have nr0 : Normalized (raw r0) := normalized_of_mv fr.1 fr.2 nr

  let b := BirthCheckPermitRepair.bounded h hw hle l0.core r0.core
  have hb := bounded_erase h hw hle l0.core r0.core
  have ha := authorized_good h h3 hw hle kappa
    l0.core.erase r0.core.erase gl.1 gr.1 nl0 nr0
  have hbcore : (b.1.erase.core, b.2.erase.core) =
      ((BirthCheckPermitRepair.authorized h hw hle kappa
          l0.core.erase r0.core.erase).1.core,
       (BirthCheckPermitRepair.authorized h hw hle kappa
          l0.core.erase r0.core.erase).2.core) :=
    congrArg (fun z : AuthorizedAgentState psi × AuthorizedAgentState psi =>
      (z.1.core, z.2.core)) hb
  have hg : WG (raw l0) (raw r0) (b.1.erase.core, b.2.erase.core) := by
    rw [hbcore]
    exact ha
  have hg0 := wg_trans (raw l) (raw r) (raw l0, raw r0)
    (b.1.erase.core, b.2.erase.core) ⟨gl, gr⟩ hg

  let bl : ExpiringAgentState psi kappa tau := ⟨b.1, l0.stall⟩
  let br : ExpiringAgentState psi kappa tau := ⟨b.2, r0.stall⟩

  change WG (raw l) (raw r)
    (raw (BirthCheckPermitRepair.expiring h hw hle l r).1,
     raw (BirthCheckPermitRepair.expiring h hw hle l r).2)
  rw [expiring_stage_eq h hw hle l r]
  dsimp only
  exact ⟨good_of_wv (expiry_w l0 bl) hg0.1,
    good_of_wv (expiry_w r0 br) hg0.2⟩


/-- The K2/collision tail cannot create a leader at a follower endpoint. -/
private theorem collision_followers (h : 0 < psi)
    (l r : ExpiringAgentState psi kappa tau) :
    ((raw l).leader = false → (raw (collisionRow h l r).1).leader = false) ∧
    ((raw r).leader = false → (raw (collisionRow h l r).2).leader = false) := by
  by_cases hb : l.core.core.leader = true ∧ r.core.core.leader = true
  · constructor
    · intro hl
      have bad : false = true := hl.symm.trans hb.1
      cases bad
    · intro hr
      have bad : false = true := hr.symm.trans hb.2
      cases bad
  · have he := collisionRow_of_not_both h l r hb
    have hk := LDSinkTwoGapEpochSuccessor.kernelC_no_leader_creation
      (by decide : 0 < 1) (observeCell l) (observeCell r)
    constructor
    · intro hl
      rw [he]
      change (LDSinkKernelC.sinkKernelC (by decide : 0 < 1)
        (observeCell l) (observeCell r)).1.leader = false
      exact hk.1 hl
    · intro hr
      rw [he]
      change (LDSinkKernelC.sinkKernelC (by decide : 0 < 1)
        (observeCell l) (observeCell r)).2.leader = false
      exact hk.2 hr

private theorem bool_back (a b : Bool) (hf : a = false → b = false)
    (hb : b = true) : a = true := by
  cases ha : a with
  | false =>
      have bad : false = true := (hf ha).symm.trans hb
      cases bad
  | true => rfl

private theorem final_normalized (h : 0 < psi)
    (oldL oldR metaL metaR : ExpiringAgentState psi kappa tau)
    (nl : Normalized (raw metaL)) (nr : Normalized (raw metaR)) :
    let q := finalPhysical h oldL oldR metaL metaR
    Normalized (raw q.1) ∧ Normalized (raw q.2) := by
  let il := initializeNewborn oldL metaL
  let ir := initializeNewborn oldR metaR
  let q := finalPhysical h oldL oldR metaL metaR
  have hc := collision_followers h il ir
  have hf := finalPhysical_frame h oldL oldR metaL metaR
  have hLf := congrArg
    (fun z : ExpiringAgentState psi kappa tau => (raw z).label) hf.1
  have hRf := congrArg
    (fun z : ExpiringAgentState psi kappa tau => (raw z).label) hf.2
  have ll : (raw q.1).label = (raw metaL).label := by
    simpa only [q, putSignals_raw_label] using hLf
  have lr : (raw q.2).label = (raw metaR).label := by
    simpa only [q, putSignals_raw_label] using hRf
  constructor
  · intro hq
    have hi : (raw il).leader = true :=
      bool_back (raw il).leader (raw q.1).leader hc.1 hq
    have hm : (raw metaL).leader = true :=
      (initializeNewborn_leader oldL metaL).symm.trans hi
    exact (congrArg Fin.val ll).trans (nl hm)
  · intro hq
    have hi : (raw ir).leader = true :=
      bool_back (raw ir).leader (raw q.2).leader hc.2 hq
    have hm : (raw metaR).leader = true :=
      (initializeNewborn_leader oldR metaR).symm.trans hi
    exact (congrArg Fin.val lr).trans (nr hm)


private theorem row_normalized (h : 0 < psi) (hw : 0 < width)
    (hle : width ≤ psi) (l r : ExpiringAgentState psi kappa tau) :
    let q := BirthCheckPermitRepair.row h hw hle l r
    Normalized (raw q.1) ∧ Normalized (raw q.2) := by
  let e := BirthCheckPermitRepair.expiring h hw hle l r
  have nl : Normalized (raw (normalizeLeader h e.1)) := by
    intro he
    exact congrArg Fin.val (normalizeLeader_label_zero h e.1 he)
  have nr : Normalized (raw (normalizeLeader h e.2)) := by
    intro he
    exact congrArg Fin.val (normalizeLeader_label_zero h e.2 he)

  change
    Normalized (raw (BirthCheckPermitRepair.row h hw hle l r).1) ∧
      Normalized (raw (BirthCheckPermitRepair.row h hw hle l r).2)
  rw [row_stage_eq h hw hle l r]
  simpa only [e] using
    (final_normalized h l r (normalizeLeader h e.1) (normalizeLeader h e.2) nl nr)


theorem row_passive_normalized (h : 0 < psi) (h3 : 2 < psi)
    (hw : 0 < width) (hle : width ≤ psi)
    (l r : ExpiringAgentState psi kappa tau)
    (hl : WriterPassive (raw l)) (hr : WriterPassive (raw r))
    (nl : Normalized (raw l)) (nr : Normalized (raw r)) :
    let q := BirthCheckPermitRepair.row h hw hle l r
    (WriterPassive (raw q.1) ∧ Normalized (raw q.1)) ∧
    (WriterPassive (raw q.2) ∧ Normalized (raw q.2)) ∧
      (raw q.1).bit = (raw l).bit ∧ (raw q.2).bit = (raw r).bit := by
  let e := BirthCheckPermitRepair.expiring h hw hle l r
  have he := expiring_good h h3 hw hle l r hl hr nl nr
  have gl : Good (raw l) (raw (normalizeLeader h e.1)) :=
    good_of_wv (normalize_w h e.1) he.1
  have gr : Good (raw r) (raw (normalizeLeader h e.2)) :=
    good_of_wv (normalize_w h e.2) he.2
  have hf := final_w h l r (normalizeLeader h e.1) (normalizeLeader h e.2)
  have ol := good_of_wv hf.1 gl
  have or := good_of_wv hf.2 gr
  have hn := row_normalized h hw hle l r

  change
    (WriterPassive (raw (BirthCheckPermitRepair.row h hw hle l r).1) ∧
      Normalized (raw (BirthCheckPermitRepair.row h hw hle l r).1)) ∧
    (WriterPassive (raw (BirthCheckPermitRepair.row h hw hle l r).2) ∧
      Normalized (raw (BirthCheckPermitRepair.row h hw hle l r).2)) ∧
    (raw (BirthCheckPermitRepair.row h hw hle l r).1).bit = (raw l).bit ∧
      (raw (BirthCheckPermitRepair.row h hw hle l r).2).bit = (raw r).bit
  rw [row_stage_eq h hw hle l r] at hn ⊢
  simpa only [e] using
    (show
      (WriterPassive (raw (finalPhysical h l r
          (normalizeLeader h e.1) (normalizeLeader h e.2)).1) ∧
        Normalized (raw (finalPhysical h l r
          (normalizeLeader h e.1) (normalizeLeader h e.2)).1)) ∧
      (WriterPassive (raw (finalPhysical h l r
          (normalizeLeader h e.1) (normalizeLeader h e.2)).2) ∧
        Normalized (raw (finalPhysical h l r
          (normalizeLeader h e.1) (normalizeLeader h e.2)).2)) ∧
      (raw (finalPhysical h l r
          (normalizeLeader h e.1) (normalizeLeader h e.2)).1).bit = (raw l).bit ∧
      (raw (finalPhysical h l r
          (normalizeLeader h e.1) (normalizeLeader h e.2)).2).bit = (raw r).bit
      from ⟨⟨ol.1, hn.1⟩, ⟨or.1, hn.2⟩, ol.2, or.2⟩)


-- From this point the actual row is used only through its theorem.

private theorem step1_cell_pn_bits (h : 0 < psi) (h2 : 2 ≤ psi)
    (h3 : 2 < psi) (ring : DirectedRing n) (C : FC n psi kappa tau)
    (hC : PN C) (e i : Fin n) :
    let D := BirthCheckPermitRepairLeaf.step1 h h2 ring C e
    (WriterPassive (raw (D i)) ∧ Normalized (raw (D i))) ∧
      (raw (D i)).bit = (raw (C i)).bit := by
  have hq := row_passive_normalized h h3 (by decide : 0 < 2) h2
    (C e) (C (ring.rightNeighbor e))
    (hC e).1 (hC (ring.rightNeighbor e)).1
    (hC e).2 (hC (ring.rightNeighbor e)).2
  by_cases hi : i = e
  · subst i
    simpa only [BirthCheckPermitRepairLeaf.step1, PopulationProtocol.step,
      BirthCheckPermitRepair.protocol, if_pos rfl] using
      And.intro hq.1 hq.2.2.1
  · by_cases hj : i = ring.rightNeighbor e
    · subst i
      simpa only [BirthCheckPermitRepairLeaf.step1, PopulationProtocol.step,
        BirthCheckPermitRepair.protocol, if_neg hi, if_pos rfl, if_true] using
        And.intro hq.2.1 hq.2.2.2
    · simpa only [BirthCheckPermitRepairLeaf.step1, PopulationProtocol.step,
        BirthCheckPermitRepair.protocol, if_neg hi, if_neg hj] using
        And.intro (hC i) (Eq.refl (raw (C i)).bit)


/-- PN is closed even if the row creates or deletes leaders. -/
theorem pn_closed_step1 (h : 0 < psi) (h2 : 2 ≤ psi) (h3 : 2 < psi)
    (ring : DirectedRing n) (C : FC n psi kappa tau) (hC : PN C) (e : Fin n) :
    PN (BirthCheckPermitRepairLeaf.step1 h h2 ring C e) := by
  intro i
  exact (step1_cell_pn_bits h h2 h3 ring C hC e i).1

theorem s0_closed_step1 (h : 0 < psi) (h2 : 2 ≤ psi) (h3 : 2 < psi)
    (ring : DirectedRing n) (C : FC n psi kappa tau) (hC : S0 C) (e : Fin n) :
    S0 (BirthCheckPermitRepairLeaf.step1 h h2 ring C e) := by
  refine ⟨pn_closed_step1 h h2 h3 ring C hC.1 e, ?_⟩
  intro i
  exact (step1_cell_pn_bits h h2 h3 ring C hC.1 e i).2.trans (hC.2 i)

theorem s0_closed (h : 0 < psi) (h2 : 2 ≤ psi) (h3 : 2 < psi)
    (ring : DirectedRing n) :
    PopulationProtocol.ClosedPred (R1LegitKernel.protocolR1 h h2 kappa tau)
      ring S0 := by
  intro C hC D hD
  obtain ⟨e, rfl⟩ := hD
  exact s0_closed_step1 h h2 h3 ring C hC e

private theorem relabel_pn (h : 0 < psi)
    (l r : ExpiringAgentState psi kappa tau)
    (hp : WriterPassive (raw r) ∧ Normalized (raw r))
    (hr : (raw r).leader = false) :
    WriterPassive (raw (B9SpliceTableHost.relabelCell h l r)) ∧
      Normalized (raw (B9SpliceTableHost.relabelCell h l r)) := by
  refine ⟨hp.1, ?_⟩
  intro hl
  have hz : (raw (B9SpliceTableHost.relabelCell h l r)).leader = false := hr
  have bad : false = true := hz.symm.trans hl
  cases bad

private theorem s0_relabel (h : 0 < psi) (ring : DirectedRing n)
    (C : FC n psi kappa tau) (hC : S0 C) (e : Fin n)
    (hr : (raw (C (ring.rightNeighbor e))).leader = false) :
    S0 (B9SpliceTableHost.relabelStep h ring C e) := by
  have hp := relabel_pn h (C e) (C (ring.rightNeighbor e))
    (hC.1 (ring.rightNeighbor e)) hr
  constructor
  · intro i
    by_cases hi : i = e
    · subst i
      simpa only [B9SpliceTableHost.relabelStep, B9SpliceTableHost.relabelHost,
        B9Host.hostStep, if_pos rfl] using hC.1 e
    · by_cases hj : i = ring.rightNeighbor e
      · subst i
        simpa only [B9SpliceTableHost.relabelStep, B9SpliceTableHost.relabelHost,
          B9Host.hostStep, if_neg hi, if_pos rfl, if_true] using hp
      · simpa only [B9SpliceTableHost.relabelStep, B9SpliceTableHost.relabelHost,
          B9Host.hostStep, if_neg hi, if_neg hj] using hC.1 i
  · intro i
    by_cases hi : i = e
    · subst i
      simpa only [B9SpliceTableHost.relabelStep, B9SpliceTableHost.relabelHost,
        B9Host.hostStep, if_pos rfl] using hC.2 e
    · by_cases hj : i = ring.rightNeighbor e
      · subst i
        simp only [B9SpliceTableHost.relabelStep, B9SpliceTableHost.relabelHost,
          B9Host.hostStep, if_neg hi, if_pos rfl, if_true]
        exact hC.2 (ring.rightNeighbor e)
      · simpa only [B9SpliceTableHost.relabelStep, B9SpliceTableHost.relabelHost,
          B9Host.hostStep, if_neg hi, if_neg hj] using hC.2 i


/-- Residual guard fact for an actual final service. The first two premises
exclude overlapping keep/host alternatives, so a coincidental equality with
relabelStep does not demand that a leader be a follower. -/
def RelabelFollowerAt (h : 0 < psi) (h2 : 2 ≤ psi) (ring : DirectedRing n)
    (C : B9SpliceTableHost.Config n psi kappa tau) (e : Fin n) : Prop :=
  B9SpliceTableHost.erase (B9SpliceTableHost.stepV10kR1 h h2 ring C e) ≠
      B9SpliceTableHost.erase C →
  B9SpliceTableHost.erase (B9SpliceTableHost.stepV10kR1 h h2 ring C e) ≠
      BirthCheckPermitRepairLeaf.step1 h h2 ring (B9SpliceTableHost.erase C) e →
  (raw (B9SpliceTableHost.erase C (ring.rightNeighbor e))).leader = false

/-- The B9 theorem is explicitly conditional on its executed relabel guard.
There is no assumed R1 closure law: that part is s0_closed_step1 above. -/
theorem s0_closed_stepV10kR1 (h : 0 < psi) (h2 : 2 ≤ psi) (h3 : 2 < psi)
    (ring : DirectedRing n) (C : B9SpliceTableHost.Config n psi kappa tau)
    (hC : S0 (B9SpliceTableHost.erase C)) (e : Fin n)
    (hguard : RelabelFollowerAt h h2 ring C e) :
    S0 (B9SpliceTableHost.erase (B9SpliceTableHost.stepV10kR1 h h2 ring C e)) := by
  rcases B9SpliceTableHost.stepV10kR1_project_trichotomy h h2 ring C e with
    hk | hh | hr
  · rw [hk]
    exact hC
  · rw [hh]
    exact s0_closed_step1 h h2 h3 ring _ hC e
  · by_cases hk : B9SpliceTableHost.erase (B9SpliceTableHost.stepV10kR1 h h2 ring C e) =
        B9SpliceTableHost.erase C
    · rw [hk]
      exact hC
    · by_cases hh : B9SpliceTableHost.erase (B9SpliceTableHost.stepV10kR1 h h2 ring C e) =
          BirthCheckPermitRepairLeaf.step1 h h2 ring (B9SpliceTableHost.erase C) e
      · rw [hh]
        exact s0_closed_step1 h h2 h3 ring _ hC e
      · rw [hr]
        exact s0_relabel h ring _ hC e (hguard hk hh)
/-- Fixed-start group IDs depend only on bits, not on current labels. -/
private theorem groupID_zero (ring : DirectedRing n) (C : FC n psi kappa tau)
    (hz : ∀ i, (raw (C i)).bit = false) (s : Fin n) :
    groupID ring.hn (fun i => raw (C i)) s = 0 := by
  have hf : ∀ xs : List Nat, ∀ a : Nat,
      xs.foldl (fun b (_ : Nat) => b) a = a := by
    intro xs
    induction xs with
    | nil => intro a; rfl
    | cons x xs ih => intro a; exact ih a
  unfold groupID
  simp only [hz, Bool.false_eq_true, if_false, Nat.zero_mul, Nat.add_zero]
  exact hf (List.range psi) 0

theorem s0_not_stableID (h : 0 < psi) (ring : DirectedRing n)
    (hn : 3 * psi ≤ n) (C : FC n psi kappa tau) (hC : S0 C) :
    ¬ isStableIDSequence h ring (fun i => raw (C i)) := by
  intro hs
  obtain ⟨root, _, _, _, hg⟩ := hs
  have hq : 3 ≤ n / psi := (Nat.le_div_iff_mul_le h).2 hn
  have he := hg 2 (by decide) (by omega)
  have hz := groupID_zero ring C hC.2
    (⟨(root.val + 2 * psi) % n, Nat.mod_lt _ ring.hn⟩ : Fin n)
  change groupID ring.hn (fun i => raw (C i))
      ⟨(root.val + 2 * psi) % n, Nat.mod_lt _ ring.hn⟩ = trailingZeros 2 at he
  have ht : trailingZeros 2 = 1 := by
    simp [trailingZeros]
  rw [hz, ht] at he
  cases he


theorem s0_not_positivePeak (h : 0 < psi) (ring : DirectedRing n)
    (hn : 3 * psi ≤ n) (C : FC n psi kappa tau) (hC : S0 C) (root : Fin n) :
    ¬ R1CandidateKernel.PositivePeak ring C root := by
  have hn2 : 2 < n := by omega
  let a : Fin n := ⟨1, by omega⟩
  let b : Fin n := ⟨2, hn2⟩
  have hza : R1CandidateKernel.lapID ring C root a.val = 0 :=
    groupID_zero ring C hC.2 _
  have hzb : R1CandidateKernel.lapID ring C root b.val = 0 :=
    groupID_zero ring C hC.2 _
  have ha : 0 < a.val := by
    change 0 < 1
    omega
  have hab : a.val < b.val := by
    change 1 < 2
    omega
  have hb : (b.val + 1) * psi ≤ n := by
    change 3 * psi ≤ n
    exact hn
  intro hp
  obtain ⟨k, hk1, hk2, _⟩ := hp a b ha hab hb (hza.trans hzb.symm)
  change 1 < k.val at hk1
  change k.val < 2 at hk2
  omega


/-- Existing zero-ID seed; no new record or replay is substituted. -/
abbrev c0 : FC 9 3 3 48 := R1ZeroIdBirthWord.w0Seed

theorem c0_mem : S0 c0 := by
  constructor
  · intro i
    constructor
    · exact ⟨rfl, rfl, Or.inl rfl⟩
    · intro hl
      have hi : i.val = 0 := by
        simpa only [c0, R1ZeroIdBirthWord.w0Seed, R1CandidateKernel.witness,
          raw, AuthorizedBoundedAgentState.erase, BoundedAgentState.erase,
          decide_eq_true_eq] using hl
      change i.val % 3 = 0
      simp only [hi, Nat.zero_mod]
  · intro i
    exact R1ZeroIdBirthWord.w0Seed_bits i

/-- Induction on words, using only the one-service theorem. -/
theorem s0_runR1 (h : 0 < psi) (h2 : 2 ≤ psi) (h3 : 2 < psi)
    (ring : DirectedRing n) (C : FC n psi kappa tau) (hC : S0 C)
    (w : List (Fin n)) : S0 (R1LegitKernel.runR1 h h2 ring C w) := by
  induction w generalizing C with
  | nil => exact hC
  | cons e es ih =>
      change S0 (R1LegitKernel.runR1 h h2 ring
        (BirthCheckPermitRepairLeaf.step1 h h2 ring C e) es)
      exact ih _ (s0_closed_step1 h h2 h3 ring C hC e)

/-- Every finite continuation of c0 misses the literal stable-ID target. -/
theorem zero_entrance_stableID (w : List (Fin 9)) :
    ¬ isStableIDSequence (by decide : 0 < 3) R1CandidateKernel.witnessRing
      (fun i => raw (R1LegitKernel.runR1 (by decide : 0 < 3)
        (by decide : 2 ≤ 3) R1CandidateKernel.witnessRing c0 w i)) := by
  apply s0_not_stableID (by decide) R1CandidateKernel.witnessRing (by decide)
  exact s0_runR1 (by decide) (by decide) (by decide)
    R1CandidateKernel.witnessRing c0 c0_mem w

/-- Root selection cannot evade the PositivePeak obstruction either. -/
theorem zero_entrance_positivePeak (w : List (Fin 9)) (root : Fin 9) :
    ¬ R1CandidateKernel.PositivePeak R1CandidateKernel.witnessRing
      (R1LegitKernel.runR1 (by decide : 0 < 3) (by decide : 2 ≤ 3)
        R1CandidateKernel.witnessRing c0 w) root := by
  apply s0_not_positivePeak (by decide) R1CandidateKernel.witnessRing (by decide)
  exact s0_runR1 (by decide) (by decide) (by decide)
    R1CandidateKernel.witnessRing c0 c0_mem w

end R1ZeroIdClosedObstruction
