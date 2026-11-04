import Leader.Wu.Birth.WaitPassiveHost

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

variable {psi : Nat}

private theorem permit_false (u : AgentState psi) : normalizePermit u false = false := by
  cases h : u.path with
  | bot => simp [normalizePermit, h]
  | some j b =>
      cases j <;> simp [normalizePermit, h]

private theorem reconcile_false (old out : AgentState psi) :
    reconcilePermit ⟨old,false⟩ out = false := by
  unfold reconcilePermit
  split
  · exact permit_false out
  · rfl

/-- A named source cut after WAIT, using the original retained stages. -/
def postWaitPrefix (hpsi : 0 < psi) (l r : AgentState psi) :
    AuthorizedAgentState psi × AuthorizedAgentState psi :=
  let g := genCleanAfterWait hpsi l r
  let c := authorizedCleanSig hpsi ⟨g.1,false⟩ ⟨g.2,false⟩
  let e := authorizedEliminateSig hpsi c.1 c.2
  let m := authorizedCaptureSigMove hpsi e.1 e.2
  sanitizeAuthorizedPair hpsi (preCheckResetWall m.1 m.2)

theorem before_check_factor (hpsi : 0 < psi) (kappa : Nat)
    (a b : Registers psi) (pa pb : Bool)
    (hab : b.label = ⟨(a.label.val+1)%psi,Nat.mod_lt _ hpsi⟩) :
    let w := waitSaturated hpsi kappa (cell a) (cell b)
    generationBeforeCheck hpsi kappa ⟨cell a,pa⟩ ⟨cell b,pb⟩ =
      postWaitPrefix hpsi w.1 w.2 := by
  unfold generationBeforeCheck generationBeforeMove
  rw [wall_cell hpsi a b pa pb hab]
  simp only [authorizedGenClean, authorizedReconcile, genClean, reconcile_false]
  rfl

/-- A source-cut expression, not a second physical transition. -/
def postWaitRow (hpsi : 0 < psi) (a b : Registers psi)
    (pa pb : Bool) (l r : AgentState psi) :
    AuthorizedAgentState psi × AuthorizedAgentState psi :=
  let c := postWaitPrefix hpsi l r
  let d := congestGuardCheck hpsi c.1 c.2
  markLeaderBirth (leaderBirthBeforeOrAtCheck ⟨cell a,pa⟩ ⟨cell b,pb⟩ c d)
    (actionOneAfterCheckSuffix hpsi d.1 d.2)

theorem guarded_factor (hpsi : 0 < psi) (kappa : Nat)
    (a b : Registers psi) (pa pb : Bool)
    (hab : b.label = ⟨(a.label.val+1)%psi,Nat.mod_lt _ hpsi⟩) :
    let w := waitSaturated hpsi kappa (cell a) (cell b)
    generationGuardedAuthorizedTransition hpsi kappa ⟨cell a,pa⟩ ⟨cell b,pb⟩ =
      postWaitRow hpsi a b pa pb w.1 w.2 := by
  unfold generationGuardedAuthorizedTransition
  simp only [normalize_cell, active_cell, Bool.false_eq_true, ↓reduceIte,
    before_check_factor hpsi kappa a b pa pb hab]
  rfl

/-- Numeric WAIT fields omit only WAIT itself: GEN can re-arm it in this row. -/
def Numeric (u : AgentState psi) : Fin psi × Bool × Bool × Bool × Nat :=
  (u.label,u.h_field,u.carry,u.reset,u.count)

/-- The released two-site group produces departing comparison components;
neither endpoint becomes a leader and the terminal count is retained. -/
theorem released_two (a b d e : Registers 2) (pa pb : Bool)
    (hd : d.label = 0) (he : e.label = 1) (hw : d.wait = false) :
    let q := postWaitRow (by decide : 0 < 2) a b pa pb (cell d) (cell e)
    Numeric q.1.core = Numeric (cell d) ∧
    Numeric q.2.core = Numeric (cell e) ∧
    q.1.core.leader = false ∧ q.2.core.leader = false := by
  cases hdBit : d.bit <;> cases heBit : e.bit
  all_goals simp [postWaitRow, postWaitPrefix, genCleanAfterWait,
    genSigSaturatedStart, genCleanEmit, genCleanPropagate, genSigSaturatedFinish,
    authorizedCleanSig, authorizedReconcile, cleanSig, cleanSigGenConnect,
    cleanSigStep3, cleanSigStep4, cleanSigStep5, cleanSigStep6, cleanSigCleanApply,
    authorizedEliminateSig, eliminateSig, authorizedCaptureSigMove,
    captureSigMoveLeaderWall, sigMoveLeaderPreclear, incompleteLeftLeaderBoundary,
    clearIfLeader, captureTransfers, captureStep1, sigMoveStep2, sigMoveStep3,
    sigMoveStep4, sigMoveStep5, comparisonLeaderWall, sigMoveControlTail,
    sigMoveApplyControl, pathMovedRight, preCheckResetWall, sanitizeAuthorizedPair,
    sanitizeAuthorizedTerminalEqual, unsupportedTerminalEqual,
    congestGuardCheck, authorizedCheckSig, checkSig, checkSigSetReady,
    checkSigCheckL, checkSigCheckR, checkSigSetResult,
    leaderBirthBeforeOrAtCheck, endpointLeaderBorn, markLeaderBirth,
    actionOneAfterCheckSuffix, authorizedDisappear, disappear,
    authorizedCompareSigActionOne, compareSigInit, authorizedCmpUpdate,
    freshComparisonStart, comparisonActive, cmpUpdateReturnPriority,
    cmpUpdateSetPath2, compareSigDispatchActionOne,
    suppressSigResetKill, suppressSigStart, suppressSigMoveReset,
    resetKillComparison, suppressSigTerminal, suppressSigEcho, suppressSigFinish,
    authorizedPostSuppressLeaderSink, eliminateLeadersNoCollisionLeaderSink,
    eliminateLeadersNoCollisionFire, eliminateLeadersNoCollisionMove,
    eliminateLeadersNoCollisionSignalLeaderSink,
    writeSeqIncrementGate, writeSeqThroughPrepare, writeSeqLeaderMove, groupInfo,
    writeSeqGenerate, writeSeqPrepare, writeSeqReady, writeSeqSetWriteReady,
    writeSeqCompare, writeSeqCommands, writeSeqSetWriteAct, gatePreparedIncrement,
    writeSeqAfterPrepare, writeAction, writeActionToState, moveWsig,
    moveWsigCheckLast, moveWsigTransfer, reconcilePermit, normalizePermit,
    cell, Numeric, hd, he, hw, hdBit, heBit]

/-- The fields needed to recognize a cap in the pre-finish responder are
unchanged by the actual WAIT finish row. -/
private theorem finish_cap_static (hpsi : 0 < psi) (kappa : Nat)
    (l r : AgentState psi) :
    let q := waitSaturatedFinish hpsi kappa l r
    q.1.label = l.label ∧ q.2.label = r.label ∧ q.2.count = r.count := by
  unfold waitSaturatedFinish
  repeat (first | exact ⟨rfl,rfl,rfl⟩ | split <;> try dsimp only)

/-- If the actual WAIT output has a terminal cap and the initiator is
nonterminal, the real finish row releases that initiator. -/
private theorem wait_cap_releases_left (hpsi : 0 < psi) (kappa : Nat)
    (l r : AgentState psi)
    (hl : (waitSaturated hpsi kappa l r).1.label ≠
      ⟨psi-1,by omega⟩)
    (hc : Cap hpsi kappa (waitSaturated hpsi kappa l r).2) :
    (waitSaturated hpsi kappa l r).1.wait = false := by
  let p := waitSaturatedPrepare hpsi l r
  let c := waitSaturatedCarry hpsi kappa p.1 p.2
  let s := waitSaturatedReset hpsi c.1 c.2
  change (waitSaturatedFinish hpsi kappa s.1 s.2).1.label ≠
    ⟨psi-1,by omega⟩ at hl
  change Cap hpsi kappa (waitSaturatedFinish hpsi kappa s.1 s.2).2 at hc
  change (waitSaturatedFinish hpsi kappa s.1 s.2).1.wait = false
  have hf := finish_cap_static hpsi kappa s.1 s.2
  change
    (waitSaturatedFinish hpsi kappa s.1 s.2).1.label = s.1.label ∧
    (waitSaturatedFinish hpsi kappa s.1 s.2).2.label = s.2.label ∧
    (waitSaturatedFinish hpsi kappa s.1 s.2).2.count = s.2.count at hf
  have hlt : s.1.label ≠ ⟨psi-1,by omega⟩ := by
    intro h
    exact hl (hf.1.trans h)
  have hrt : s.2.label = ⟨psi-1,by omega⟩ :=
    hf.2.1.symm.trans hc.1
  have hrc : s.2.count = kappa := hf.2.2.symm.trans hc.2
  simp [waitSaturatedFinish, hrt, hrc, hlt]

/-- Strictly before cap, a passive cyclic pair is closed by the literal full
host row. Bits, phases, clocks, expiry timers and incoming permit bits remain
arbitrary; WRITE is retained only through its inert none/depart projection. -/
theorem full_passive_below (hpsi : 0 < psi) (kappa tau : Nat)
    (l r : ExpiringAgentState psi kappa tau)
    (hl : Passive (raw l)) (hr : Passive (raw r))
    (hab : (raw r).label =
      ⟨((raw l).label.val+1)%psi,Nat.mod_lt _ hpsi⟩)
    (hbelow : Below hpsi kappa
      (waitSaturated hpsi kappa (raw l) (raw r)).2) :
    let q := generationFullTransition hpsi kappa tau l r
    Passive (raw q.1) ∧ Passive (raw q.2) := by
  let a := registers (raw l)
  let b := registers (raw r)
  let w := waitSaturated hpsi kappa (cell a) (cell b)
  let q := generationFullTransition hpsi kappa tau l r
  change Passive (raw q.1) ∧ Passive (raw q.2)
  have hla : raw l = cell a := by
    change raw l = cell (registers (raw l))
    exact hl.1
  have hrb : raw r = cell b := by
    change raw r = cell (registers (raw r))
    exact hr.1
  have hab' : b.label =
      ⟨(a.label.val+1)%psi,Nat.mod_lt _ hpsi⟩ := by
    simpa [a,b,registers] using hab
  have harm := wait_armed hpsi kappa (raw l) (raw r)
    hl.2.1 hr.2.1 hbelow
  rw [hla,hrb] at harm
  change w.1.wait = true ∧ w.2.wait = true at harm
  have hrow := full_cell_row hpsi kappa tau l r a b hla hrb hab'
    (fun _ => harm.1)
  change
    q.1.core.erase =
      ⟨cell {registers w.1 with writer := .none},false⟩ ∧
    q.2.core.erase =
      ⟨cell {registers w.2 with writer :=
        if w.1.label < w.2.label ∨ w.2.label = ⟨0,hpsi⟩
        then .depart else .none},false⟩ at hrow
  have hq1 : raw q.1 = cell {registers w.1 with writer := .none} := by
    change (q.1.core.erase).core = _
    exact congrArg (fun s : AuthorizedAgentState psi => s.core) hrow.1
  have hq2 : raw q.2 = cell {registers w.2 with writer :=
      if w.1.label < w.2.label ∨ w.2.label = ⟨0,hpsi⟩
      then .depart else .none} := by
    change (q.2.core.erase).core = _
    exact congrArg (fun s : AuthorizedAgentState psi => s.core) hrow.2
  constructor
  · rw [hq1]
    unfold Passive
    refine ⟨metadata_cell _, ?_⟩
    refine ⟨?_, ?_⟩
    · change (registers w.1).wait = true
      simpa only [registers] using harm.1
    · unfold InertWriter
      change WriteState.none = .none ∨ WriteState.none = .depart
      exact Or.inl rfl
  · rw [hq2]
    unfold Passive
    refine ⟨metadata_cell _, ?_⟩
    refine ⟨?_, ?_⟩
    · change (registers w.2).wait = true
      simpa only [registers] using harm.2
    · unfold InertWriter
      by_cases hw : w.1.label < w.2.label ∨ w.2.label = ⟨0,hpsi⟩
      · right
        simpa [cell, hw]
      · left
        simpa [cell, hw]

private theorem fin2_cases (i : Fin 2) : i = 0 ∨ i = 1 := by
  have h : i.val = 0 ∨ i.val = 1 := by omega
  rcases h with h | h
  · exact Or.inl (Fin.ext h)
  · exact Or.inr (Fin.ext h)

/-- At the real ψ=2 cap row, full passive closure is intentionally not claimed:
GEN may start. What survives the complete original host is the actual terminal
count. -/
theorem full_cap_two_terminal_count (kappa tau : Nat)
    (l r : ExpiringAgentState 2 kappa tau) (a b : Registers 2)
    (hl : raw l = cell a) (hr : raw r = cell b)
    (hab : b.label =
      ⟨(a.label.val+1)%2,Nat.mod_lt _ (by decide : 0 < 2)⟩)
    (hcap : Cap (by decide : 0 < 2) kappa
      (waitSaturated (by decide : 0 < 2) kappa (cell a) (cell b)).2) :
    let q := generationFullTransition (by decide : 0 < 2) kappa tau l r
    (raw q.2).count = kappa := by
  let w := waitSaturated (by decide : 0 < 2) kappa (cell a) (cell b)
  change (raw (generationFullTransition (by decide : 0 < 2)
    kappa tau l r).2).count = kappa
  change Cap (by decide : 0 < 2) kappa w.2 at hcap
  have hs := wait_static (by decide : 0 < 2) kappa (cell a) (cell b)
  change w.1.label = a.label ∧ w.2.label = b.label ∧
    w.1.count = a.count at hs
  have hb1 : b.label = 1 := by
    apply Fin.ext
    have hv := congrArg Fin.val (hs.2.1.symm.trans hcap.1)
    simpa using hv
  have ha0 : a.label = 0 := by
    rcases fin2_cases a.label with ha | ha
    · exact ha
    · exfalso
      have hv := congrArg Fin.val hab
      simpa [ha,hb1] using hv
  have hw0 : w.1.label = 0 := hs.1.trans ha0
  have hwne : w.1.label ≠ ⟨2-1,by omega⟩ := by
    intro ht
    have hv := congrArg Fin.val (hw0.symm.trans ht)
    simpa using hv
  have hwfalse := wait_cap_releases_left (by decide : 0 < 2) kappa
    (cell a) (cell b) hwne hcap
  have hm := wait_metadata (by decide : 0 < 2) kappa a b
  change w.1 = cell (registers w.1) ∧
    w.2 = cell (registers w.2) at hm
  have hd : (registers w.1).label = 0 := by
    change w.1.label = 0
    exact hw0
  have he : (registers w.2).label = 1 := by
    change w.2.label = 1
    exact hs.2.1.trans hb1
  have hw : (registers w.1).wait = false := by
    change w.1.wait = false
    exact hwfalse
  have hguard :
      generationGuardedAuthorizedTransition (by decide : 0 < 2) kappa
        (prepareExpiringDisposal (by decide : 0 < 2) l).core.erase
        (prepareExpiringDisposal (by decide : 0 < 2) r).core.erase =
      postWaitRow (by decide : 0 < 2) a b
        l.core.path0Crossed r.core.path0Crossed w.1 w.2 := by
    rw [prepared_erasure (by decide : 0 < 2) l a hl,
      prepared_erasure (by decide : 0 < 2) r b hr]
    exact guarded_factor (by decide : 0 < 2) kappa a b _ _ hab
  have hguardCell :
      generationGuardedAuthorizedTransition (by decide : 0 < 2) kappa
        (prepareExpiringDisposal (by decide : 0 < 2) l).core.erase
        (prepareExpiringDisposal (by decide : 0 < 2) r).core.erase =
      postWaitRow (by decide : 0 < 2) a b
        l.core.path0Crossed r.core.path0Crossed
        (cell (registers w.1)) (cell (registers w.2)) := by
    calc
      _ = postWaitRow (by decide : 0 < 2) a b
          l.core.path0Crossed r.core.path0Crossed w.1 w.2 := hguard
      _ = postWaitRow (by decide : 0 < 2) a b
          l.core.path0Crossed r.core.path0Crossed
          (cell (registers w.1)) w.2 := by
            exact congrArg
              (fun x : AgentState 2 =>
                postWaitRow (by decide : 0 < 2) a b
                  l.core.path0Crossed r.core.path0Crossed x w.2) hm.1
      _ = postWaitRow (by decide : 0 < 2) a b
          l.core.path0Crossed r.core.path0Crossed
          (cell (registers w.1)) (cell (registers w.2)) := by
            exact congrArg
              (fun y : AgentState 2 =>
                postWaitRow (by decide : 0 < 2) a b
                  l.core.path0Crossed r.core.path0Crossed
                  (cell (registers w.1)) y) hm.2
  have hrel := released_two a b (registers w.1) (registers w.2)
    l.core.path0Crossed r.core.path0Crossed hd he hw
  have hnum :
      Numeric
        (generationGuardedAuthorizedTransition (by decide : 0 < 2) kappa
          (prepareExpiringDisposal (by decide : 0 < 2) l).core.erase
          (prepareExpiringDisposal (by decide : 0 < 2) r).core.erase).2.core =
      Numeric (cell (registers w.2)) := by
    rw [hguardCell]
    exact hrel.2.1
  have hfc := full_clock (by decide : 0 < 2) kappa tau l r
  have hfullCount :
      (raw (generationFullTransition (by decide : 0 < 2)
        kappa tau l r).2).count =
      (generationGuardedAuthorizedTransition (by decide : 0 < 2) kappa
        (prepareExpiringDisposal (by decide : 0 < 2) l).core.erase
        (prepareExpiringDisposal (by decide : 0 < 2) r).core.erase).2.core.count := by
    have h := congrArg (fun c : Clock 2 => c.count) hfc.2
    simpa [clock] using h
  have hguardCount :
      (generationGuardedAuthorizedTransition (by decide : 0 < 2) kappa
        (prepareExpiringDisposal (by decide : 0 < 2) l).core.erase
        (prepareExpiringDisposal (by decide : 0 < 2) r).core.erase).2.core.count =
      w.2.count := by
    have h := congrArg
      (fun x : Fin 2 × Bool × Bool × Bool × Nat => x.2.2.2.2) hnum
    simpa [Numeric,registers,cell] using h
  exact hfullCount.trans (hguardCount.trans hcap.2)

/-- Actual ψ=2 endpoint adapter for the bounded full host. Strict pre-cap rows
stay passive; at cap the weaker, true endpoint fact is exact terminal-count
retention. -/
theorem full_two_endpoint_adapter (kappa tau : Nat)
    (l r : ExpiringAgentState 2 kappa tau)
    (hl : Passive (raw l)) (hr : Passive (raw r))
    (hab : (raw r).label =
      ⟨((raw l).label.val+1)%2,Nat.mod_lt _ (by decide : 0 < 2)⟩) :
    let w := waitSaturated (by decide : 0 < 2) kappa (raw l) (raw r)
    let q := generationFullTransition (by decide : 0 < 2) kappa tau l r
    (Below (by decide : 0 < 2) kappa w.2 ∧
      Passive (raw q.1) ∧ Passive (raw q.2)) ∨
    (Cap (by decide : 0 < 2) kappa w.2 ∧
      (raw q.2).count = kappa) := by
  let w := waitSaturated (by decide : 0 < 2) kappa (raw l) (raw r)
  let q := generationFullTransition (by decide : 0 < 2) kappa tau l r
  change
    (Below (by decide : 0 < 2) kappa w.2 ∧
      Passive (raw q.1) ∧ Passive (raw q.2)) ∨
    (Cap (by decide : 0 < 2) kappa w.2 ∧
      (raw q.2).count = kappa)
  have hlc : (raw l).count ≤ kappa := by
    change (l.core.core.erase).count ≤ kappa
    have hdom := BoundedAgentState.erase_inProtocolDomain l.core.core
    unfold AgentState.inProtocolDomain at hdom
    exact hdom.1
  have hrc : (raw r).count ≤ kappa := by
    change (r.core.core.erase).count ≤ kappa
    have hdom := BoundedAgentState.erase_inProtocolDomain r.core.core
    unfold AgentState.inProtocolDomain at hdom
    exact hdom.1
  have hclosed := waitSaturated_count_closed (κ := kappa)
    (by decide : 0 < 2) (raw l) (raw r) hlc hrc
  change w.1.count ≤ kappa ∧ w.2.count ≤ kappa at hclosed
  rcases cap_or_below (by decide : 0 < 2) kappa w.2 hclosed.2 with hcap | hbelow
  · apply Or.inr
    refine ⟨hcap, ?_⟩
    let a := registers (raw l)
    let b := registers (raw r)
    have hla : raw l = cell a := by
      change raw l = cell (registers (raw l))
      exact hl.1
    have hrb : raw r = cell b := by
      change raw r = cell (registers (raw r))
      exact hr.1
    have hab' : b.label =
        ⟨(a.label.val+1)%2,Nat.mod_lt _ (by decide : 0 < 2)⟩ := by
      simpa [a,b,registers] using hab
    have hcap' : Cap (by decide : 0 < 2) kappa
        (waitSaturated (by decide : 0 < 2) kappa (cell a) (cell b)).2 := by
      have hx := hcap
      change Cap (by decide : 0 < 2) kappa
        (waitSaturated (by decide : 0 < 2) kappa (raw l) (raw r)).2 at hx
      rw [hla,hrb] at hx
      exact hx
    change (raw (generationFullTransition (by decide : 0 < 2)
      kappa tau l r).2).count = kappa
    exact full_cap_two_terminal_count kappa tau l r a b
      hla hrb hab' hcap'
  · apply Or.inl
    refine ⟨hbelow, ?_⟩
    have hbelow' := hbelow
    change Below (by decide : 0 < 2) kappa
      (waitSaturated (by decide : 0 < 2) kappa (raw l) (raw r)).2 at hbelow'
    change
      Passive (raw (generationFullTransition (by decide : 0 < 2)
        kappa tau l r).1) ∧
      Passive (raw (generationFullTransition (by decide : 0 < 2)
        kappa tau l r).2)
    exact full_passive_below (by decide : 0 < 2) kappa tau
      l r hl hr hab hbelow'

end BirthWaitPassive
