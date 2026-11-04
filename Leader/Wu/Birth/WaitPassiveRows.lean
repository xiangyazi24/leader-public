import Leader.Wu.Birth.GenerationControlRepair
import Leader.Wu.Birth.WaitClockRows
import Leader.Wu.Birth.WaitClockPotential

/-!
# Passive rows of the complete generation host

The records below observe existing registers. They are never added to the
protocol. Ruler bits, phases, clocks and finite expiry timers are unrestricted.
The passive WRITE departure marker is retained explicitly.
-/

namespace BirthWaitPassive

open PPLL PPLLRepair PPLLResearchFormulation PPLLDomain
  PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
  PPLLPathStallComparisonRepair PPLLLeaderCreationCleanupRepair
  PPLLWallSweepRepair PPLLWallSweepFinite PPLLWallSweepPreCheckResetRepair
  PPLLTerminalEqualSupportRepair PPLLWriteIncrementGate
  PPLLCompleteMultiLeaderCleanup PPLLWallSweepNormalResetContract
  BirthCheckCongestGuardRepair BirthMismatchDisposalProducer
  BirthSigMoveDisposalRepair BirthArrivalCaptureRepair BirthGenerationControlRepair

set_option autoImplicit false
set_option Elab.async false

variable {psi kappa tau : Nat}

/-- Existing clock and ruler registers; no protocol state is added. -/
structure Registers (psi : Nat) where
  label : Fin psi
  h : Bool
  carry : Bool
  reset : Bool
  count : Nat
  wait : Bool
  bit : Bool
  phase : Bool
  writer : WriteState
  deriving DecidableEq, Repr

def registers (u : AgentState psi) : Registers psi :=
  ⟨u.label, u.h_field, u.carry, u.reset, u.count, u.wait,
    u.bit, u.phase, u.write_state⟩

def cell (d : Registers psi) : AgentState psi where
  leader := false
  probe := false
  phase := d.phase
  bit := d.bit
  wait := d.wait
  state := .none
  path := .bot
  reset := d.reset
  carry := d.carry
  count := d.count
  label := d.label
  h_field := d.h
  path2 := none
  path3 := none
  path4 := none
  path5 := none
  p := false
  p_carry := false
  reset_cmd := false
  echo := false
  signal_B := 0
  bullet := 0
  shield := false
  write_state := d.writer
  write := .none
  last := false
  last_set := false
  last_unset := false
  b_carry := false
  gen_ws := false
  ws_echo := false
  signal_ws := false

def Metadata (u : AgentState psi) : Prop := u = cell (registers u)

def InertWriter (u : AgentState psi) : Prop :=
  u.write_state = .none ∨ u.write_state = .depart

def Passive (u : AgentState psi) : Prop :=
  Metadata u ∧ u.wait = true ∧ InertWriter u

@[simp] theorem registers_cell (d : Registers psi) : registers (cell d) = d := by
  cases d
  rfl

@[simp] theorem metadata_cell (d : Registers psi) : Metadata (cell d) := by
  simp [Metadata]

private theorem prepare_metadata (hpsi : 0 < psi) (a b : Registers psi) :
    let q := waitSaturatedPrepare hpsi (cell a) (cell b)
    Metadata q.1 ∧ Metadata q.2 := by
  unfold waitSaturatedPrepare
  split <;> try dsimp only
  all_goals split <;> try dsimp only
  all_goals first | exact ⟨rfl, rfl⟩ | (split <;> exact ⟨rfl, rfl⟩)

private theorem carry_metadata (hpsi : 0 < psi) (kappa : Nat)
    (a b : Registers psi) :
    let q := waitSaturatedCarry hpsi kappa (cell a) (cell b)
    Metadata q.1 ∧ Metadata q.2 := by
  unfold waitSaturatedCarry
  split <;> try dsimp only
  · split <;> try dsimp only
    · split <;> exact ⟨rfl, rfl⟩
    · exact ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩

private theorem reset_metadata (hpsi : 0 < psi) (a b : Registers psi) :
    let q := waitSaturatedReset hpsi (cell a) (cell b)
    Metadata q.1 ∧ Metadata q.2 := by
  unfold waitSaturatedReset
  split <;> try dsimp only
  · split <;> exact ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩

private theorem finish_metadata (hpsi : 0 < psi) (kappa : Nat)
    (a b : Registers psi) :
    let q := waitSaturatedFinish hpsi kappa (cell a) (cell b)
    Metadata q.1 ∧ Metadata q.2 := by
  unfold waitSaturatedFinish
  split <;> try dsimp only
  all_goals split <;> exact ⟨rfl, rfl⟩

/-- WAIT itself changes no neutral metadata or ruler register. -/
theorem wait_metadata (hpsi : 0 < psi) (kappa : Nat)
    (a b : Registers psi) :
    let q := waitSaturated hpsi kappa (cell a) (cell b)
    Metadata q.1 ∧ Metadata q.2 := by
  let p := waitSaturatedPrepare hpsi (cell a) (cell b)
  have hp := prepare_metadata hpsi a b
  change Metadata p.1 ∧ Metadata p.2 at hp
  let c := waitSaturatedCarry hpsi kappa p.1 p.2
  have hc : Metadata c.1 ∧ Metadata c.2 := by
    unfold c
    rw [hp.1, hp.2]
    exact carry_metadata hpsi kappa _ _
  let r := waitSaturatedReset hpsi c.1 c.2
  have hr : Metadata r.1 ∧ Metadata r.2 := by
    unfold r
    rw [hc.1, hc.2]
    exact reset_metadata hpsi _ _
  change let q := waitSaturatedFinish hpsi kappa r.1 r.2
    Metadata q.1 ∧ Metadata q.2
  rw [hr.1, hr.2]
  exact finish_metadata hpsi kappa _ _

@[simp] theorem reconcile_cell (old : AuthorizedAgentState psi) (d : Registers psi) :
    reconcilePermit old (cell d) = false := by
  cases h : old.core.path <;>
    simp [reconcilePermit, normalizePermit, cell, h]

theorem prepared_cell (hpsi : 0 < psi) (d : Registers psi) (permit : Bool) :
    preparedInput hpsi ⟨cell d, permit⟩ = ⟨cell d, permit⟩ := by
  simp [preparedInput, prepareDisposal, pendingTerminalDisposal,
    normalizeDeletion, pathPresent, cell]

theorem wall_cell (hpsi : 0 < psi) (a b : Registers psi)
    (pa pb : Bool)
    (hab : b.label = ⟨(a.label.val + 1) % psi, Nat.mod_lt _ hpsi⟩) :
    authorizedPPsiLeaderResetProbeWall hpsi ⟨cell a, pa⟩ ⟨cell b, pb⟩ =
      (⟨cell a, false⟩, ⟨cell b, false⟩) := by
  simp [authorizedPPsiLeaderResetProbeWall, pPsiLeaderResetProbeWall,
    pPsi, cell, hab, reconcilePermit, normalizePermit]

theorem gen_after_wait_cell (hpsi : 0 < psi) (a b : Registers psi)
    (ha : a.label = ⟨0,hpsi⟩ → a.wait = true) :
    genCleanAfterWait hpsi (cell a) (cell b) = (cell a, cell b) := by
  by_cases h0 : a.label = ⟨0,hpsi⟩
  · have hw := ha h0
    simp [genCleanAfterWait, genSigSaturatedStart, genCleanEmit,
      genCleanPropagate, genSigSaturatedFinish, cell, hw]
  · simp [genCleanAfterWait, genSigSaturatedStart, genCleanEmit,
      genCleanPropagate, genSigSaturatedFinish, cell, h0]

theorem clean_cell (hpsi : 0 < psi) (a b : Registers psi) :
    cleanSig hpsi (cell a) (cell b) = (cell a, cell b) := by
  simp [cleanSig, cleanSigGenConnect, cleanSigStep3, cleanSigStep4,
    cleanSigStep5, cleanSigStep6, cleanSigCleanApply, cell]

theorem capture_cell (hpsi : 0 < psi) (a b : Registers psi) :
    captureSigMoveLeaderWall hpsi (cell a) (cell b) = (cell a, cell b) := by
  simp [captureSigMoveLeaderWall, sigMoveLeaderPreclear,
    incompleteLeftLeaderBoundary, clearIfLeader, captureTransfers,
    captureStep1, sigMoveStep2, sigMoveStep3, sigMoveStep4, sigMoveStep5,
    comparisonLeaderWall, sigMoveControlTail, sigMoveApplyControl, cell]

theorem check_cell (hpsi : 0 < psi) (a b : Registers psi) :
    checkSig hpsi (cell a) (cell b) = (cell a, cell b) := by
  simp [checkSig, checkSigSetReady, checkSigCheckL, checkSigCheckR,
    checkSigSetResult, cell]

theorem suppress_cell (hpsi : 0 < psi) (a b : Registers psi) :
    suppressSigResetKill hpsi (cell a) (cell b) = (cell a, cell b) := by
  simp [suppressSigResetKill, suppressSigStart, resetKillComparison,
    suppressSigMoveReset, suppressSigTerminal, suppressSigEcho,
    suppressSigFinish, cell]

theorem elimination_cell (hpsi : 0 < psi) (a b : Registers psi) :
    eliminateLeadersNoCollisionLeaderSink hpsi (cell a) (cell b) =
      (cell a, cell b) := by
  simp [eliminateLeadersNoCollisionLeaderSink, eliminateLeadersNoCollisionFire,
    eliminateLeadersNoCollisionMove, eliminateLeadersNoCollisionSignalLeaderSink,
    cell]
  intro _
  rfl

theorem write_prepare_cell (hpsi : 0 < psi) (a b : Registers psi) :
    writeSeqThroughPrepare hpsi (cell a) (cell b) =
      (cell {a with writer := .none}, cell {b with writer := .none}) := by
  simp [writeSeqThroughPrepare, writeSeqLeaderMove, groupInfo, writeSeqGenerate,
    writeSeqPrepare, writeSeqReady, writeSeqSetWriteReady, writeSeqCompare,
    writeSeqCommands, writeSeqSetWriteAct, cell]

theorem write_cell (hpsi : 0 < psi) (a b : Registers psi) :
    writeSeqIncrementGate hpsi (cell a) (cell b) =
      (cell {a with writer := .none},
       cell {b with writer := if a.label < b.label ∨ b.label = ⟨0,hpsi⟩
         then .depart else .none}) := by
  unfold writeSeqIncrementGate
  rw [write_prepare_cell]
  by_cases hat : a.label = ⟨psi - 1, by omega⟩ <;>
    by_cases hbt : b.label = ⟨psi - 1, by omega⟩ <;>
    by_cases hab : a.label < b.label <;>
    by_cases hb0 : b.label = ⟨0, hpsi⟩ <;>
    simp [gatePreparedIncrement, writeSeqAfterPrepare, writeAction,
      writeActionToState, moveWsig, moveWsigCheckLast, moveWsigTransfer,
      cell, hat, hbt, hab, hb0]
  all_goals simp_all
  all_goals repeat (first | rfl | intro _ | split)

/-- The complete post-CHECK suffix on a passive pair, including inert WRITE. -/
theorem suffix_cell (hpsi : 0 < psi) (a b : Registers psi) :
    actionOneAfterCheckSuffix hpsi ⟨cell a, false⟩ ⟨cell b, false⟩ =
      (⟨cell {a with writer := .none}, false⟩,
       ⟨cell {b with writer := if a.label < b.label ∨ b.label = ⟨0,hpsi⟩
         then .depart else .none}, false⟩) := by
  have hd : disappear hpsi (cell a) (cell b) = (cell a, cell b) := by
    simp [disappear, cell]
  have he : eliminateLeadersNoCollisionLeaderSink hpsi (cell a) (cell b) =
      (cell a, cell b) := elimination_cell hpsi a b
  simp only [actionOneAfterCheckSuffix, authorizedDisappear, authorizedReconcile,
    hd]
  have hc : authorizedCompareSigActionOne hpsi
      ⟨cell a, reconcilePermit ⟨cell a,false⟩ (cell a)⟩
      ⟨cell b, reconcilePermit ⟨cell b,false⟩ (cell b)⟩ =
        (⟨cell a,false⟩, ⟨cell b,false⟩) := by
    simp [authorizedCompareSigActionOne, compareSigInit,
      reconcilePermit, normalizePermit, cell]
  rw [hc]
  simp only [suppress_cell]
  change authorizedPostSuppressLeaderSink hpsi ⟨cell a,false⟩ ⟨cell b,false⟩ = _
  simp only [authorizedPostSuppressLeaderSink, authorizedReconcile, he,
    write_cell]
  rfl

/-- Every ordinary prefix stage after a still-armed WAIT is physically inert. -/
theorem before_check_cell (hpsi : 0 < psi) (kappa : Nat)
    (a b : Registers psi) (pa pb : Bool)
    (hab : b.label = ⟨(a.label.val + 1) % psi, Nat.mod_lt _ hpsi⟩)
    (hw : let q := waitSaturated hpsi kappa (cell a) (cell b)
      q.1.label = ⟨0,hpsi⟩ → q.1.wait = true) :
    let q := waitSaturated hpsi kappa (cell a) (cell b)
    generationBeforeCheck hpsi kappa ⟨cell a,pa⟩ ⟨cell b,pb⟩ =
      (⟨q.1,false⟩, ⟨q.2,false⟩) := by
  let q := waitSaturated hpsi kappa (cell a) (cell b)
  have hm := wait_metadata hpsi kappa a b
  change Metadata q.1 ∧ Metadata q.2 at hm
  change q.1.label = ⟨0,hpsi⟩ → q.1.wait = true at hw
  have hg : genClean hpsi kappa (cell a) (cell b) = q := by
    change genCleanAfterWait hpsi q.1 q.2 = q
    conv => lhs; rw [hm.1, hm.2]
    rw [gen_after_wait_cell hpsi _ _ hw]
    exact Prod.ext hm.1.symm hm.2.symm
  unfold generationBeforeCheck generationBeforeMove
  rw [wall_cell hpsi a b pa pb hab]
  simp only [authorizedGenClean, authorizedReconcile, hg]
  conv => lhs; rw [hm.1, hm.2]
  simp only [reconcile_cell]
  simp only [authorizedCleanSig, authorizedReconcile]
  rw [clean_cell hpsi (registers q.1) (registers q.2)]
  simp only [authorizedEliminateSig, authorizedReconcile]
  have he : eliminateSig hpsi (cell (registers q.1)) (cell (registers q.2)) =
      (cell (registers q.1), cell (registers q.2)) := by
    simp [eliminateSig, cell]
  rw [he]
  have hcap : authorizedCaptureSigMove hpsi
      ⟨cell (registers q.1),false⟩ ⟨cell (registers q.2),false⟩ =
        (⟨cell (registers q.1),false⟩,⟨cell (registers q.2),false⟩) := by
    unfold authorizedCaptureSigMove
    rw [capture_cell]
    simp [pathMovedRight, reconcilePermit, normalizePermit, cell]
  change sanitizeAuthorizedPair hpsi (preCheckResetWall
    (authorizedCaptureSigMove hpsi ⟨cell (registers q.1),false⟩
      ⟨cell (registers q.2),false⟩).1
    (authorizedCaptureSigMove hpsi ⟨cell (registers q.1),false⟩
      ⟨cell (registers q.2),false⟩).2) = _
  rw [hcap]
  rw [preCheckResetWall_eq_of_inactive _ _ rfl rfl rfl]
  have hs (d : Registers psi) :
      sanitizeAuthorizedTerminalEqual hpsi ⟨cell d,false⟩ = ⟨cell d,false⟩ := by
    simp [sanitizeAuthorizedTerminalEqual, unsupportedTerminalEqual, cell]
  simp only [sanitizeAuthorizedPair, hs]
  rw [← hm.1, ← hm.2]

@[simp] theorem normalize_cell (d : Registers psi) (p : Bool) :
    normalizeDeletion ⟨cell d,p⟩ = ⟨cell d,p⟩ := by
  simp [normalizeDeletion, cell]

@[simp] theorem active_cell (d : Registers psi) (p : Bool) :
    deletionActive ⟨cell d,p⟩ = false := by
  rfl

@[simp] theorem guarded_check_cell (hpsi : 0 < psi) (a b : Registers psi) :
    congestGuardCheck hpsi ⟨cell a,false⟩ ⟨cell b,false⟩ =
      (⟨cell a,false⟩,⟨cell b,false⟩) := by
  have hn : ¬ ((cell a).state = .congest ∨ (cell b).state = .congest) := by
    simp [cell]
  unfold congestGuardCheck
  rw [if_neg hn]
  simp only [authorizedCheckSig, authorizedReconcile, check_cell, reconcile_cell]

/-- Exact authorized row whenever WAIT does not release a label-zero source.
No condition on the responder's WAIT bit is needed at this interface. -/
theorem guarded_cell (hpsi : 0 < psi) (kappa : Nat)
    (a b : Registers psi) (pa pb : Bool)
    (hab : b.label = ⟨(a.label.val+1)%psi,Nat.mod_lt _ hpsi⟩)
    (hw : let q := waitSaturated hpsi kappa (cell a) (cell b)
      q.1.label = ⟨0,hpsi⟩ → q.1.wait = true) :
    let q := waitSaturated hpsi kappa (cell a) (cell b)
    generationGuardedAuthorizedTransition hpsi kappa ⟨cell a,pa⟩ ⟨cell b,pb⟩ =
      (⟨cell {registers q.1 with writer := .none},false⟩,
       ⟨cell {registers q.2 with writer :=
          if q.1.label < q.2.label ∨ q.2.label = ⟨0,hpsi⟩ then .depart else .none},false⟩) := by
  let q := waitSaturated hpsi kappa (cell a) (cell b)
  have hm := wait_metadata hpsi kappa a b
  change Metadata q.1 ∧ Metadata q.2 at hm
  have hb := before_check_cell hpsi kappa a b pa pb hab hw
  change generationBeforeCheck hpsi kappa ⟨cell a,pa⟩ ⟨cell b,pb⟩ =
      (⟨q.1,false⟩,⟨q.2,false⟩) at hb
  have hc : congestGuardCheck hpsi ⟨q.1,false⟩ ⟨q.2,false⟩ =
      (⟨q.1,false⟩,⟨q.2,false⟩) := by
    rw [hm.1,hm.2]
    exact guarded_check_cell hpsi _ _
  have hborn : leaderBirthBeforeOrAtCheck ⟨cell a,pa⟩ ⟨cell b,pb⟩
      (⟨q.1,false⟩,⟨q.2,false⟩) (⟨q.1,false⟩,⟨q.2,false⟩) = false := by
    rw [hm.1,hm.2]
    rfl
  unfold generationGuardedAuthorizedTransition
  simp only [normalize_cell, active_cell, Bool.false_eq_true, ↓reduceIte, hb]
  rw [hc]
  simp only [hborn, markLeaderBirth, Bool.false_eq_true, ↓reduceIte]
  conv => lhs; rw [hm.1,hm.2]
  rw [suffix_cell]
  rfl

end BirthWaitPassive
