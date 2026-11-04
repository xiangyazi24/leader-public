import Leader.Wu.Birth.CheckChainActionSixRow
import Leader.Wu.Birth.CheckChainTossDoneRow

set_option autoImplicit false
set_option Elab.async false

/-! # Action-five release blocking on the actual R1 row

Closed certificates use psi = 4, kappa = 2, tau = 3 and WAIT width 2.
They distinguish a resident-six collision from a collision-free arrival at
an internal less cell. Additional label-zero certificates use toss_done
as the initiator state. The expiration certificate includes the actual
pre-expiry path/permit view and an idle DISAPPEAR certificate.

The symbolic theorems concern an internal equal/less pair at labels i and
i + 1, with 1 <= i and i + 1 < psi - 1. Their hypotheses are current input
fields, not hypotheses about the computed CHECK or ordinary output.
They are single-row statements, not reachability statements from back-toss
and not assertions about all continuations of an aligned train.
-/

namespace BirthCheckChainR1ReleaseBlock

open PPLL PPLLRepair PPLLResearchFormulation
  PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
  PPLLPathStallComparisonRepair PPLLLeaderCreationCleanupRepair
  PPLLWallSweepRepair PPLLWallSweepPreCheckResetRepair
  PPLLTerminalEqualSupportRepair
  BirthSigMoveDisposalRepair BirthArrivalCaptureRepair
  BirthSingleUseReleaseRepair BirthGenerationDone
  BirthShortDoneTerminalEntryCut BirthCheckChainR1

variable {ψ κ τ : Nat}

def actionFive : Option Path2Info := some ⟨0, 0, 0, 5⟩
def actionSix : Option Path2Info := some ⟨0, 0, 0, 6⟩

/-- True selects O1; false selects O2. -/
def inputRightControl (collision : Bool) : Option Path2Info :=
  if collision then actionSix else none

def movedRightControl (collision : Bool) : Option Path2Info :=
  if collision then none else actionFive

/-- Excludes every action-five token, not just the canonical all-zero one. -/
abbrev NoFive (p : Option Path2Info) : Prop :=
  p.map Path2Info.action ≠ some 5

/-! ## 1. Closed, finite certificates -/

abbrev Cell4 := ExpiringAgentState 4 2 3

/-- All auxiliary fields are explicit. The signal bit and resident bit may
be different; the main path is aligned with the physical label. -/
def raw4 (lab : Fin 4) (residentBit signalBit : Bool)
    (s : MainState) (control : Option Path2Info) : AgentState 4 where
  leader := false
  probe := false
  phase := false
  bit := residentBit
  wait := true
  state := s
  path := .some lab.val (if signalBit then 1 else 0)
  reset := false
  carry := false
  count := 0
  label := lab
  h_field := false
  path2 := control
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
  write_state := .none
  write := .none
  last := false
  last_set := false
  last_unset := false
  b_carry := false
  gen_ws := false
  ws_echo := false
  signal_ws := false

private def pack4 (u : AgentState 4) (hu : u.inProtocolDomain 2)
    (stall : Fin 4) : Cell4 :=
  ⟨⟨BoundedAgentState.ofDomain u hu, false⟩, stall⟩

def left4 : Cell4 :=
  pack4 (raw4 1 false false .equal actionFive) (by simp [AgentState.inProtocolDomain, raw4, actionFive, actionSix]) 3

def collisionRight4 : Cell4 :=
  pack4 (raw4 2 false true .less actionSix) (by simp [AgentState.inProtocolDomain, raw4, actionFive, actionSix]) 3

def arrivalRight4 : Cell4 :=
  pack4 (raw4 2 false true .less none) (by simp [AgentState.inProtocolDomain, raw4, actionFive, actionSix]) 3

/-- A specialization of the real row, not a replacement transition. -/
def row4 (l r : Cell4) : Cell4 × Cell4 :=
  BirthCheckPermitRepair.row (ψ := 4) (width := 2) (κ := 2) (τ := 3)
    (by decide) (by decide) (by decide) l r

/-- O1: Step4 has already removed five before the CHECK cut. -/
theorem collision4_beforeCheck :
    let q := doneBeforeCheckEntryWidth
      (ψ := 4) (width := 2) (by decide) (by decide) (by decide) 2
      left4.core.erase collisionRight4.core.erase
    q.1.core.path2 = actionSix ∧ q.2.core.path2 = none ∧
      q.1.core.state = .equal ∧ q.2.core.state = .less := by
  decide +kernel

/-- O2: five really reaches the less responder before CHECK. -/
theorem arrival4_beforeCheck :
    let q := doneBeforeCheckEntryWidth
      (ψ := 4) (width := 2) (by decide) (by decide) (by decide) 2
      left4.core.erase arrivalRight4.core.erase
    q.1.core.path2 = none ∧ q.2.core.path2 = actionFive ∧
      q.1.core.state = .equal ∧ q.2.core.state = .less := by
  decide +kernel

/-- O1 after the complete row, including expiry and final physical tail. -/
theorem collision4_exact :
    let q := row4 left4 collisionRight4
    q.1.core.erase.core.path2 = actionSix ∧
      q.2.core.erase.core.path2 = actionSix ∧
      q.1.core.erase.core.state = .equal ∧
      q.2.core.erase.core.state = .less ∧
      q.1.core.erase.core.path = .some 1 0 ∧
      q.2.core.erase.core.path = .some 2 1 ∧
      q.1.stall.val = 2 ∧ q.2.stall.val = 2 := by
  decide +kernel

/-- O2 after the complete row. Neither component is deleted by this row. -/
theorem arrival4_exact :
    let q := row4 left4 arrivalRight4
    q.1.core.erase.core.path2 = none ∧
      q.2.core.erase.core.path2 = actionSix ∧
      q.1.core.erase.core.state = .equal ∧
      q.2.core.erase.core.state = .less ∧
      q.1.core.erase.core.path = .some 1 0 ∧
      q.2.core.erase.core.path = .some 2 1 ∧
      q.1.stall.val = 2 ∧ q.2.stall.val = 2 := by
  decide +kernel

theorem collision4_noFive :
    let q := row4 left4 collisionRight4
    NoFive q.1.core.erase.core.path2 ∧
      NoFive q.2.core.erase.core.path2 ∧
      q.2.core.erase.core.state = .less := by
  have h := collision4_exact
  refine ⟨?_, ?_, h.2.2.2.1⟩
  · rw [h.1]
    decide
  · rw [h.2.1]
    decide

theorem arrival4_noFive :
    let q := row4 left4 arrivalRight4
    NoFive q.1.core.erase.core.path2 ∧
      NoFive q.2.core.erase.core.path2 ∧
      q.2.core.erase.core.state = .less := by
  have h := arrival4_exact
  refine ⟨?_, ?_, h.2.2.2.1⟩
  · rw [h.1]
    decide
  · rw [h.2.1]
    decide

/-- The k = 1 inputs, with a toss_done label-zero initiator. -/
def head4 : Cell4 :=
  pack4 (raw4 0 false false .toss_done actionFive) (by simp [AgentState.inProtocolDomain, raw4, actionFive, actionSix]) 3

def headCollisionRight4 : Cell4 :=
  pack4 (raw4 1 false true .less actionSix) (by simp [AgentState.inProtocolDomain, raw4, actionFive, actionSix]) 3

def headArrivalRight4 : Cell4 :=
  pack4 (raw4 1 false true .less none) (by simp [AgentState.inProtocolDomain, raw4, actionFive, actionSix]) 3

/-- At label zero O1 enters toss and suppresses CHECK: the responder does
not regenerate its six in this interaction. -/
theorem head_collision4_exact :
    let q := row4 head4 headCollisionRight4
    q.1.core.erase.core.path2 = actionSix ∧
      q.2.core.erase.core.path2 = none ∧
      q.1.core.erase.core.state = .toss ∧
      q.2.core.erase.core.state = .less ∧
      q.1.core.erase.core.p = true ∧
      q.1.core.erase.core.p_carry = false ∧
      NoFive q.1.core.erase.core.path2 ∧
      NoFive q.2.core.erase.core.path2 := by
  decide +kernel

/-- The collision-free head row rearms toss_done to equal and overwrites
the newly arrived five on the less responder. -/
theorem head_arrival4_exact :
    let q := row4 head4 headArrivalRight4
    q.1.core.erase.core.path2 = none ∧
      q.2.core.erase.core.path2 = actionSix ∧
      q.1.core.erase.core.state = .equal ∧
      q.2.core.erase.core.state = .less ∧
      NoFive q.1.core.erase.core.path2 ∧
      NoFive q.2.core.erase.core.path2 := by
  decide +kernel

/-! ## 3. Closed zero-stall certificate, independent of the symbolic proofs -/

def zeroRight4 : Cell4 := { arrivalRight4 with stall := 0 }

/-- DISAPPEAR itself is idle in the O3 witness, at its actual source cut. -/
theorem zero4_disappear_idle :
    let l0 := prepareExpiringDisposal (by decide : 0 < 4) left4
    let r0 := prepareExpiringDisposal (by decide : 0 < 4) zeroRight4
    let c := doneThroughCheckEntryWidth
      (ψ := 4) (width := 2) (by decide) (by decide) (by decide) 2
      l0.core.erase r0.core.erase
    let l := BirthCheckPermitRepair.permitFix c.1
    authorizedDisappear (by decide : 0 < 4) l c.2 = (l, c.2) := by
  decide +kernel

/-- The actual bounded metadata retains the responder's path and permit;
it is still less, with no active deletion marker and no pending p-carry. -/
theorem zero4_beforeExpiry :
    let l0 := prepareExpiringDisposal (by decide : 0 < 4) left4
    let r0 := prepareExpiringDisposal (by decide : 0 < 4) zeroRight4
    let q := BirthCheckPermitRepair.bounded
      (ψ := 4) (width := 2) (κ := 2)
      (by decide) (by decide) (by decide) l0.core r0.core
    r0.stall.val = 0 ∧
      PathProgressView.ofState q.2 = PathProgressView.ofState r0.core ∧
      q.2.erase.core.path = .some 2 1 ∧
      q.2.erase.core.state = .less ∧
      deletionActive q.2.erase = false ∧
      q.1.erase.core.p_carry = false ∧
      q.2.erase.core.p_carry = false := by
  decide +kernel

/-- The real R1 row clears the retained responder at zero stall. -/
theorem zero4_expired :
    let q := row4 left4 zeroRight4
    q.2.core.erase.core.path = .bot ∧
      q.2.core.erase.core.path2 = none ∧
      q.2.core.erase.core.state = .none ∧
      q.2.core.path0Crossed = false ∧
      q.2.core.erase.core.p = false ∧
      q.2.core.erase.core.p_carry = false ∧
      q.2.stall.val = 3 := by
  decide +kernel

/-! ## 2. Symbolic internal equal/less rows -/

/-- These are input fields only. The cleanup hypothesis is the same
right-path5 condition used by generation_keeps_chain. At positive i the
left path4 is regenerated by CLEAN, so no left-path4 premise is needed. -/
structure ReleasePair (collision : Bool) (i bl br : Nat)
    (l r : ExpiringAgentState ψ κ τ) : Prop where
  leftLabel : l.core.erase.core.label.val = i
  rightLabel : r.core.erase.core.label.val = i + 1
  positiveIndex : 1 ≤ i
  nonterminal : i + 1 < ψ - 1
  leftPath : l.core.erase.core.path = .some i bl
  rightPath : r.core.erase.core.path = .some (i + 1) br
  leftState : l.core.erase.core.state = .equal
  rightState : r.core.erase.core.state = .less
  leftControl : l.core.erase.core.path2 = actionFive
  rightControl : r.core.erase.core.path2 = inputRightControl collision
  leftFollower : l.core.erase.core.leader = false
  rightFollower : r.core.erase.core.leader = false
  leftReset : l.core.erase.core.reset_cmd = false
  rightReset : r.core.erase.core.reset_cmd = false
  leftCarry : l.core.erase.core.p_carry = false
  rightCarry : r.core.erase.core.p_carry = false
  rightClean : ∀ p, r.core.erase.core.path5 = some p → p.1 ≠ -1
  leftStall : l.stall.val ≠ 0
  rightStall : r.stall.val ≠ 0

structure ReleaseResult (collision : Bool) (l r : AgentState ψ) : Prop where
  leftControl : l.path2 = inputRightControl collision
  rightControl : r.path2 = actionSix
  leftState : l.state = .equal
  rightState : r.state = .less
  leftFollower : l.leader = false
  rightFollower : r.leader = false

theorem result_noFive (collision : Bool) (l r : AgentState ψ)
    (h : ReleaseResult collision l r) :
    NoFive l.path2 ∧ NoFive r.path2 ∧ r.state = .less := by
  refine ⟨?_, ?_, h.rightState⟩
  · rw [h.leftControl]
    cases collision <;> decide
  · rw [h.rightControl]
    decide

/-- Exact occupied-pair transport: O1 overwrites the initiator before
Step5; O2 actually delivers five to the nonterminal responder. -/
theorem doneMove_release (hψ : 0 < ψ) (collision : Bool)
    (l r : AgentState ψ) (a b c d : Nat)
    (hlp : l.path = .some a b) (hrp : r.path = .some c d)
    (hll : l.leader = false) (hrl : r.leader = false)
    (hlp2 : l.path2 = actionFive)
    (hrp2 : r.path2 = inputRightControl collision)
    (hleq : l.state = .equal) (hrls : r.state = .less)
    (hl0 : l.label ≠ ⟨0, hψ⟩)
    (hrterm : r.label ≠ ⟨ψ - 1, by omega⟩) :
    doneCaptureSigMove hψ l r =
      ({ l with path2 := inputRightControl collision },
       { r with path2 := movedRightControl collision }) := by
  have hp : sigMoveLeaderPreclear hψ l r = (l, r) := by
    simp [sigMoveLeaderPreclear, incompleteLeftLeaderBoundary,
      clearIfLeader, hll, hrl]
  have hm : doneTransfers l r =
      ({ l with path2 := inputRightControl collision },
       { r with path2 := movedRightControl collision }) := by
    cases collision <;>
      simp [doneTransfers, holdDoneStep1, hleq, captureStep1, hlp, hrp,
        controlTransfers, sigMoveStep2, sigMoveStep3, sigMoveStep4,
        sigMoveStep5, hlp2, hrp2, inputRightControl, movedRightControl,
        actionFive, actionSix]
  have hw : comparisonLeaderWall
      { l with path2 := inputRightControl collision }
      { r with path2 := movedRightControl collision } =
      ({ l with path2 := inputRightControl collision },
       { r with path2 := movedRightControl collision }) := by
    simp [comparisonLeaderWall, hll, hrl]
  unfold doneCaptureSigMove
  rw [hp]
  dsimp only
  rw [hm]
  dsimp only
  rw [hw]
  cases collision <;>
    simp [singleUseControlTail, singleUseApplyControl,
      inputRightControl, movedRightControl, actionFive, actionSix,
      hl0, hrterm, hleq, hrls]

/-- A definitional factoring of the existing post-generation CHECK cut. -/
private def checkAfterMove (hψ : 0 < ψ)
    (l r : AuthorizedAgentState ψ) :
    AuthorizedAgentState ψ × AuthorizedAgentState ψ :=
  let m := authorizedDoneMove hψ l r
  let s := sanitizeAuthorizedPair hψ (preCheckResetWall m.1 m.2)
  preserveDoneCheck hψ s.1 s.2

private theorem checkAfterMove_release (hψ : 0 < ψ) (collision : Bool)
    (l r : AuthorizedAgentState ψ) (a b c d : Nat)
    (hlp : l.core.path = .some a b) (hrp : r.core.path = .some c d)
    (hll : l.core.leader = false) (hrl : r.core.leader = false)
    (hlr : l.core.reset_cmd = false) (hrr : r.core.reset_cmd = false)
    (hlp2 : l.core.path2 = actionFive)
    (hrp2 : r.core.path2 = inputRightControl collision)
    (hleq : l.core.state = .equal) (hrls : r.core.state = .less)
    (hl0 : l.core.label ≠ ⟨0, hψ⟩)
    (hlab : l.core.label.val < ψ - 1)
    (hrterm : r.core.label ≠ ⟨ψ - 1, by omega⟩) :
    (checkAfterMove hψ l r).1.core =
        { l.core with path2 := inputRightControl collision } ∧
      (checkAfterMove hψ l r).2.core =
        { r.core with path2 := actionSix } := by
  have hmc := authorizedDoneMove_core hψ l r
  rw [doneMove_release hψ collision l.core r.core a b c d
    hlp hrp hll hrl hlp2 hrp2 hleq hrls hl0 hrterm] at hmc
  unfold checkAfterMove
  dsimp only
  generalize authorizedDoneMove hψ l r = m at hmc ⊢
  have hm1 : m.1.core = { l.core with path2 := inputRightControl collision } :=
    congrArg Prod.fst hmc
  have hm2 : m.2.core = { r.core with path2 := movedRightControl collision } :=
    congrArg Prod.snd hmc
  have hw : preCheckResetWall m.1 m.2 = (m.1, m.2) :=
    preCheckResetWall_eq_of_inactive m.1 m.2
      (by rw [hm1]; exact hll)
      (by rw [hm1]; exact hlr)
      (by rw [hm2]; exact hrr)
  have hs1 : sanitizeAuthorizedTerminalEqual hψ m.1 = m.1 := by
    unfold sanitizeAuthorizedTerminalEqual unsupportedTerminalEqual
    have hn : m.1.core.label ≠ ⟨ψ - 1, by omega⟩ := by
      rw [hm1]
      intro h
      have hv := congrArg Fin.val h
      simp only at hv
      omega
    simp [hn]
  have hs2 : sanitizeAuthorizedTerminalEqual hψ m.2 = m.2 := by
    unfold sanitizeAuthorizedTerminalEqual unsupportedTerminalEqual
    have hn : m.2.core.state ≠ .equal := by rw [hm2, hrls]; decide
    simp [hn]
  rw [hw]
  simp only [sanitizeAuthorizedPair]
  rw [hs1, hs2]
  rw [preserveDoneCheck_of_no_done hψ m.1 m.2
      (by rw [hm1, hleq]; decide) (by rw [hm2, hrls]; decide),
    BirthTossCheckPreservationRepair.preserveTossCheck_of_no_toss hψ m.1 m.2
      (by rw [hm1, hleq]; decide) (by rw [hm2, hrls]; decide),
    BirthCheckCongestGuardRepair.congestGuardCheck_of_clear hψ m.1 m.2
      (by rw [hm1, hleq]; decide) (by rw [hm2, hrls]; decide)]
  have e := authorizedCheckSig_cores hψ m.1 m.2
  rw [e.1, e.2, hm1, hm2]
  have hc := checkSig_equal_less hψ
    { l.core with path2 := inputRightControl collision }
    { r.core with path2 := movedRightControl collision }
    (by simpa using hleq) (by simpa using hlab) (by simpa using hrls)
  rw [hc.1, hc.2]
  exact ⟨rfl, rfl⟩

/-- Reuse the two existing suffix frames; no new suffix semantics. -/
private theorem afterCheck_release {width : Nat}
    (hψ : 0 < ψ) (hwidth : 0 < width) (hle : width ≤ ψ)
    (collision : Bool) (l r : AuthorizedAgentState ψ) (a b c d : Nat)
    (hlp : l.core.path = .some a b) (hrp : r.core.path = .some c d)
    (hls : l.core.state = .equal) (hrs : r.core.state = .less)
    (hlq : l.core.path2 = inputRightControl collision)
    (hrq : r.core.path2 = actionSix)
    (hperm : l.core.label ≠ ⟨0, hψ⟩ ∨ l.path0Crossed = false)
    (hrterm : r.core.label ≠ ⟨ψ - 1, by omega⟩)
    (hll : l.core.leader = false)
    (hlr : l.core.reset_cmd = false) (hrr : r.core.reset_cmd = false) :
    let q := BirthShortDoneCuts.afterCheckMetadataWidth hψ hwidth hle l r
    postView q.1.core = postView l.core ∧
      postView q.2.core = postView r.core := by
  cases collision with
  | false =>
      exact afterCheck_keeps_less hψ hwidth hle l r a b c d
        hlp hrp hls hrs hlq hrq hperm hrterm hll hlr hrr
  | true =>
      exact afterCheck_keeps_signal6 hψ hwidth hle l r a b c d
        hlp hrp hls hrs hlq hrq hperm hrterm hll hlr hrr

private theorem ordinary_release_row (hψ : 0 < ψ) (h2 : 2 ≤ ψ)
    (κ : Nat) (collision : Bool) (l r : AuthorizedAgentState ψ)
    (i bl br : Nat)
    (hcons : r.core.label =
      ⟨(l.core.label.val + 1) % ψ, Nat.mod_lt _ hψ⟩)
    (hll : l.core.leader = false) (hrl : r.core.leader = false)
    (hlp : l.core.path = .some i bl) (hlab : l.core.label.val = i)
    (hi0 : 1 ≤ i) (hi : i + 1 < ψ - 1)
    (hrp : r.core.path = .some (i + 1) br)
    (hrlab : r.core.label.val = i + 1)
    (hleq : l.core.state = .equal) (hlp2 : l.core.path2 = actionFive)
    (hrls : r.core.state = .less)
    (hrp2 : r.core.path2 = inputRightControl collision)
    (hlr : l.core.reset_cmd = false) (hrr : r.core.reset_cmd = false)
    (hr5 : ∀ p, r.core.path5 = some p → p.1 ≠ -1) :
    let q := BirthCheckPermitRepair.ordinary
      hψ (by decide : 0 < 2) h2 κ l r
    ReleaseResult collision q.1.core q.2.core := by
  intro q
  have hg := generation_keeps_chain (κ := κ)
    hψ (by decide : 0 < 2) h2 l r i bl br
    hcons hll hrl hlp hrp (by omega)
    (by rw [hleq]; decide) (by rw [hleq]; decide)
    (by rw [hrls]; decide) (by rw [hrls]; decide)
    (by rw [hrls]; decide) (fun h => absurd h (by omega)) hr5
  generalize hB : generationBeforeMoveEntryWidth
    hψ (by decide : 0 < 2) h2 κ l r = B at hg
  have b1 := hg.1
  have b2 := hg.2
  unfold genView at b1 b2
  simp only [Prod.mk.injEq] at b1 b2
  obtain ⟨s1, p1, q1, lb1, bt1, ld1, rc1⟩ := b1
  obtain ⟨s2, p2, q2, lb2, bt2, ld2, rc2⟩ := b2
  have hcut := checkAfterMove_release hψ collision B.1 B.2 i bl (i + 1) br
    (by rw [p1]; exact hlp) (by rw [p2]; exact hrp)
    (ld1.trans hll) (ld2.trans hrl) (rc1.trans hlr) (rc2.trans hrr)
    (q1.trans hlp2) (q2.trans hrp2) (s1.trans hleq) (s2.trans hrls)
    (by
      intro h
      have hv := congrArg Fin.val h
      rw [lb1, hlab] at hv
      simp only at hv
      omega)
    (by rw [lb1, hlab]; omega)
    (by
      intro h
      have hv := congrArg Fin.val h
      rw [lb2, hrlab] at hv
      simp only at hv
      omega)
  have hbridge : doneThroughCheckEntryWidth
      hψ (by decide : 0 < 2) h2 κ l r = checkAfterMove hψ B.1 B.2 := by
    change checkAfterMove hψ
      (generationBeforeMoveEntryWidth hψ (by decide : 0 < 2) h2 κ l r).1
      (generationBeforeMoveEntryWidth hψ (by decide : 0 < 2) h2 κ l r).2 = _
    rw [hB]
  simp only [← hbridge] at hcut
  generalize hC : doneThroughCheckEntryWidth
    hψ (by decide : 0 < 2) h2 κ l r = C at hcut
  obtain ⟨hc1, hc2⟩ := hcut
  have c1s : C.1.core.state = .equal := by rw [hc1]; exact s1.trans hleq
  have c1p : C.1.core.path = l.core.path := by rw [hc1]; exact p1
  have c1q : C.1.core.path2 = inputRightControl collision := by rw [hc1]
  have c1ld : C.1.core.leader = false := by rw [hc1]; exact ld1.trans hll
  have c1rc : C.1.core.reset_cmd = false := by rw [hc1]; exact rc1.trans hlr
  have c2s : C.2.core.state = .less := by rw [hc2]; exact s2.trans hrls
  have c2p : C.2.core.path = r.core.path := by rw [hc2]; exact p2
  have c2q : C.2.core.path2 = actionSix := by rw [hc2]
  have c2lb : C.2.core.label = r.core.label := by rw [hc2]; exact lb2
  have c2ld : C.2.core.leader = false := by rw [hc2]; exact ld2.trans hrl
  have c2rc : C.2.core.reset_cmd = false := by rw [hc2]; exact rc2.trans hrr
  have hfix : BirthCheckPermitRepair.permitFix C.1 = ⟨C.1.core, false⟩ := by
    simp [BirthCheckPermitRepair.permitFix, c1s]
  have hac := afterCheck_release hψ (by decide : 0 < 2) h2 collision
    ⟨C.1.core, false⟩ C.2 i bl (i + 1) br
    (c1p.trans hlp) (c2p.trans hrp) c1s c2s c1q c2q (Or.inr rfl)
    (by
      rw [c2lb]
      intro h
      have hv := congrArg Fin.val h
      rw [hrlab] at hv
      simp only at hv
      omega)
    c1ld c1rc c2rc
  obtain ⟨pv1, pv2⟩ := hac
  generalize hQ : BirthShortDoneCuts.afterCheckMetadataWidth
    hψ (by decide : 0 < 2) h2 ⟨C.1.core, false⟩ C.2 = Q at pv1 pv2
  unfold postView at pv1 pv2
  simp only [Prod.mk.injEq] at pv1 pv2
  have hq : q = markLeaderBirth (K2BirthDispatcher.authBirth l r Q) Q := by
    change BirthCheckPermitRepair.ordinary
      hψ (by decide : 0 < 2) h2 κ l r = _
    unfold BirthCheckPermitRepair.ordinary
    dsimp only
    rw [hC, hfix, hQ]
  have hborn : K2BirthDispatcher.authBirth l r Q = false := by
    simp [K2BirthDispatcher.authBirth, endpointLeaderBorn,
      pv1.2.2.2.2, pv2.2.2.2.2, c1ld, c2ld]
  rw [hq, hborn]
  simp only [markLeaderBirth, Bool.false_eq_true, if_false]
  exact
    { leftControl := pv1.2.2.1.trans c1q
      rightControl := pv2.2.2.1.trans c2q
      leftState := pv1.1.trans c1s
      rightState := pv2.1.trans c2s
      leftFollower := pv1.2.2.2.2.trans c1ld
      rightFollower := pv2.2.2.2.2.trans c2ld }

/-- Lift the computed ordinary result through actual disposal preparation,
expiry, leader normalization and the final physical tail. -/
theorem r1_release_row (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (collision : Bool)
    (l r : ExpiringAgentState ψ κ τ) (i bl br : Nat)
    (h : ReleasePair collision i bl br l r) :
    let q := BirthCheckPermitRepair.row hψ (by decide : 0 < 2) h2 l r
    ReleaseResult collision q.1.core.erase.core q.2.core.erase.core := by
  intro q
  have hi : i + 1 < ψ := by have := h.nonterminal; omega
  have hcons : r.core.erase.core.label =
      ⟨(l.core.erase.core.label.val + 1) % ψ, Nat.mod_lt _ hψ⟩ := by
    apply Fin.ext
    change r.core.erase.core.label.val = (l.core.erase.core.label.val + 1) % ψ
    rw [h.rightLabel, h.leftLabel, Nat.mod_eq_of_lt hi]
  have hc := ordinary_release_row hψ h2 κ collision l.core.erase r.core.erase
    i bl br hcons h.leftFollower h.rightFollower h.leftPath h.leftLabel
    h.positiveIndex h.nonterminal h.rightPath h.rightLabel
    h.leftState h.leftControl h.rightState h.rightControl
    h.leftReset h.rightReset h.rightClean
  have hlel : l.core.erase.core.state ≠ .eliminate_signal := by
    rw [h.leftState]
    decide
  have hrel : r.core.erase.core.state ≠ .eliminate_signal := by
    rw [h.rightState]
    decide
  have hld : pendingTerminalDisposal hψ l.core.erase.core = false := by
    simp [pendingTerminalDisposal, h.leftControl, actionFive]
  have hrd : pendingTerminalDisposal hψ r.core.erase.core = false := by
    cases collision <;>
      simp [pendingTerminalDisposal, h.rightControl, inputRightControl, actionSix]
  have hfR := BirthCheckPermitRepairRowLift.row_right_frame_clear
    hψ h2 l r hld hrd hlel hrel h.rightStall hc.rightFollower
  have hfL := BirthCheckPermitRepairRowLift.row_left_frame_clear
    hψ h2 l r hld hrd hlel hrel h.leftStall h.rightStall
    hc.leftFollower hc.rightFollower
  exact
    { leftControl := hfL.2.2.1.trans hc.leftControl
      rightControl := hfR.2.2.1.trans hc.rightControl
      leftState := hfL.1.trans hc.leftState
      rightState := hfR.1.trans hc.rightState
      leftFollower := hfL.2.2.2.2
      rightFollower := hfR.2.2.2.2.2 }

/-- O1, universally over the stated current-field input class. -/
theorem r1_collision_noFive (hψ : 0 < ψ) (h2 : 2 ≤ ψ)
    (l r : ExpiringAgentState ψ κ τ) (i bl br : Nat)
    (h : ReleasePair true i bl br l r) :
    let q := BirthCheckPermitRepair.row hψ (by decide : 0 < 2) h2 l r
    NoFive q.1.core.erase.core.path2 ∧
      NoFive q.2.core.erase.core.path2 ∧ q.2.core.erase.core.state = .less := by
  exact result_noFive true _ _ (r1_release_row hψ h2 true l r i bl br h)

/-- O2, universally over the stated current-field input class. -/
theorem r1_arrival_noFive (hψ : 0 < ψ) (h2 : 2 ≤ ψ)
    (l r : ExpiringAgentState ψ κ τ) (i bl br : Nat)
    (h : ReleasePair false i bl br l r) :
    let q := BirthCheckPermitRepair.row hψ (by decide : 0 < 2) h2 l r
    NoFive q.1.core.erase.core.path2 ∧
      NoFive q.2.core.erase.core.path2 ∧ q.2.core.erase.core.state = .less := by
  exact result_noFive false _ _ (r1_release_row hψ h2 false l r i bl br h)

end BirthCheckChainR1ReleaseBlock
