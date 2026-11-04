import Leader.Wu.Elimination.CensusVariants

/-!
# Post-election CHECK guards for the closure census (board G6.2, design input)

The G6.2 elimination census (run/verification/g62/elim) found that the base
CHECK rule (Algorithm 11 lines 14-15, thesis p.27; `checkSig`,
Algorithm.lean:277-288) creates leaders after election: it cancels Algorithm-15
kills and blocks the K2 absorption of ERRATA R160.  The M2 census found the
same for every release of the M2 self-lock.  This module restates the M2
pipeline (`PPLLElimVariants.pipelineM2`) with switchable post-election
guards, each tied to a source mechanism:

* `probeWall` — P'_ψ probe wall (thesis p.15 prose: a leader blocks probes);
  restatement of `PPLLWallSweepRepair.pPsiLeaderProbeWall`
  (WallSweepRepair.lean:104-110).
* `leaderWall` — comparison-signal wall at a leader (thesis §3.6, p.31: "we set
  a signal to be eliminated when it encounters the leader or the incomplete
  group on the left of the leader"); restatement of
  `PPLLWallSweepRepair.sigMoveLeaderWall` (WallSweepRepair.lean:456-477) with
  the M2 SIGMOVE step 1 and the consuming control application.
* `resetKill` — reset commands delete the comparison signal they meet (thesis
  §3.4, p.29: "The reset command eliminates all signals it encounters"; absent
  from Algorithm 14); restatement of
  `PPLLWallSweepRepair.suppressSigResetKill` (WallSweepRepair.lean:261-269).
* `resetPre` — the same deletion effect moved before CHECK (ERRATA T24: CHECK
  runs before SUPPRESS_SIG in Algorithm 1); restatement of
  `PPLLWallSweepPreCheckResetRepair.preCheckResetWall` on raw states.
* `check` — a guard on CHECK's leader assignment itself, using fields the
  protocol already carries; a blocked terminal equality deletes the checking
  signal instead of leaving it parked in `equal`.
* `readyNoCongest` — CHECK's ready assignment (Algorithm 11 line 2) does not
  accept `congest`.  ERRATA T9: CMP_UPDATE line 1 re-arms a still
  source-aligned signal from `depart` to `congest` in place, and CHECK accepts
  `congest`, so the signal CHECKs its own source group.  The M1 patch
  (`cmpUpdateLeaderlessRearm`) re-opens that re-arm for every follower group.

Elimination kernels: those of `PPLLElimVariants.Elim`, plus `k3`, which is K2
with the absorption guard widened from a follower responder to any responder
(a live bullet in contact with a shielded leader vanishes; YSM 2020 Algorithm 1
line 14, as cited in ERRATA R160).

With every switch off and `check = .none`, `pipeline` is stage for stage
`PPLLElimVariants.pipelineM2`; the census checks this empirically.  No proof
content; no existing module is edited.
-/

set_option autoImplicit false

namespace PPLLPostElectionGuard

open PPLL PPLLRepair PPLLBirthPatch PPLLBirthPatchM2 PPLLElimVariants

/-- Restatement of `PPLLWallSweepRepair.clearComparisonSignal`
(WallSweepRepair.lean:25-33): delete one comparison carrier and its cleanup
residue, keeping leader, label, barrier, reset, bullet and write fields. -/
def clearCmp {ψ : Nat} (u : AgentState ψ) : AgentState ψ :=
  { u with state := MainState.none, path := PathInfo.bot, path2 := none,
           path4 := none, path5 := none, p := false, p_carry := false }

/-- Restatement of `PPLLWallSweepRepair.pPsiLeaderProbeWall`
(WallSweepRepair.lean:104-110). -/
def pPsiProbeWall {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ) :
    AgentState ψ × AgentState ψ :=
  let l0 := if l.leader = true then { l with probe := false } else l
  let r0 := if r.leader = true ∨ l.leader = true then { r with probe := false } else r
  pPsi hψ l0 r0

/-- Restatement of `PPLLWallSweepRepair.comparisonLeaderWall`
(WallSweepRepair.lean:74-77). -/
def leaderWall {ψ : Nat} (l r : AgentState ψ) : AgentState ψ × AgentState ψ :=
  let l := if l.leader = true ∨ r.leader = true then clearCmp l else l
  let r := if r.leader = true then clearCmp r else r
  (l, r)

/-- SIGMOVE with the p.31 leader wall: restatement of
`PPLLWallSweepRepair.sigMoveLeaderWall` (preclear of leader-resident and
incomplete-left material, the five transfers, the wall, then the control
tail), with step 1 and the control application of `PPLLBirthPatchM2.sigMoveM2`. -/
def sigMoveWalled {ψ : Nat} (hψ : ψ > 0) (m : M2) (l r : AgentState ψ) :
    AgentState ψ × AgentState ψ :=
  let nextLabel : Fin ψ := ⟨(l.label.val + 1) % ψ, Nat.mod_lt _ hψ⟩
  let l := if l.leader = true ∨ (r.leader = true ∧ r.label ≠ nextLabel) then
    clearCmp l else l
  let r := if r.leader = true then clearCmp r else r
  let (l, r) := sigMoveStep1With m l r
  let (l, r) := sigMoveStep2 l r
  let (l, r) := sigMoveStep3 l r
  let (l, r) := sigMoveStep4 l r
  let (l, r) := sigMoveStep5 l r
  let (l, r) := leaderWall l r
  let l := sigMoveApplyControlConsume hψ l
  let r := sigMoveApplyControlConsume hψ r
  let l := if r.state = MainState.depart then
    if l.label.val < ψ - 1 ∧ l.state = MainState.CHECK_ready then
      { l with state := MainState.depart }
    else l
  else l
  (l, r)

/-- Restatement of `PPLLWallSweepPreCheckResetRepair.preCheckResetWall` on raw
states: a leader or a left reset token will send reset right later in this
interaction, so both endpoints lose their comparison material; a reset
already at the responder clears the responder. -/
def preCheckReset {ψ : Nat} (l r : AgentState ψ) : AgentState ψ × AgentState ψ :=
  let send : Bool := l.leader || l.reset_cmd
  let l' := if send then clearCmp l else l
  let r' := if send || r.reset_cmd then clearCmp r else r
  (l', r')

/-- Restatement of `PPLLWallSweepRepair.suppressSigResetKill`
(WallSweepRepair.lean:261-269). -/
def suppressSigResetKill {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ) :
    AgentState ψ × AgentState ψ :=
  let kill (u : AgentState ψ) : AgentState ψ := if u.reset_cmd then clearCmp u else u
  let q0 := suppressSigStart l r
  let q0 := (kill q0.1, kill q0.2)
  let q1 := suppressSigMoveReset q0.1 q0.2
  let q1 := (kill q1.1, kill q1.2)
  let q2 := suppressSigTerminal hψ q1.1 q1.2
  let q3 := suppressSigEcho q2.1 q2.2
  suppressSigFinish q3.1 q3.2

/-- Guards on CHECK's leader assignment (Algorithm 11 lines 14-15).  Each is
evaluated on the pair just before that assignment. -/
inductive CheckGuard where
  | none
  /-- the checked group's first agent is a leader (ψ = 2: the initiator) -/
  | leaderGroup
  /-- no reset command or echo on either endpoint (§3.4 suppression carriers) -/
  | resetEvidence
  /-- the terminal agent's wait counter is saturated (`count = κ`): the group has
  not been reset since its counter last filled (§3.4, Lemma 4.1.8) -/
  | countGate
  /-- the absence signal or a live bullet sits on either endpoint (§3.5 carriers
  that exist only while a leader exists or recently existed) -/
  | elimEvidence
  deriving DecidableEq

def allowBirth {ψ : Nat} (κ : Nat) (g : CheckGuard) (l r : AgentState ψ) : Bool :=
  match g with
  | .none => true
  | .leaderGroup => !l.leader
  | .resetEvidence => !(l.reset_cmd || r.reset_cmd || l.echo || r.echo)
  | .countGate => decide (r.count = κ)
  | .elimEvidence =>
      !(decide (l.signal_B = 1) || decide (r.signal_B = 1) ||
        decide (l.bullet = 2) || decide (r.bullet = 2))

/-- CHECK's ready assignment without `congest` (and without the in-flight
control states, as in `checkSigSetReadyGuarded`). -/
def checkSigSetReadyNoCongest {ψ : Nat} (u : AgentState ψ) : AgentState ψ :=
  if u.state = .congest then u else checkSigSetReadyGuarded u

/-- `PPLLBirthPatch.checkSigWith hψ true` (guarded ready assignment) whose leader
assignment additionally requires `allowBirth`; a blocked terminal equality
deletes the signal on both endpoints (the rest of the signal is removed by
CLEAN_SIG, as for any partial signal). -/
def checkSigGuarded {ψ : Nat} (hψ : ψ > 0) (κ : Nat) (g : CheckGuard)
    (noCongest : Bool) (l r : AgentState ψ) : AgentState ψ × AgentState ψ :=
  let ready := if noCongest then checkSigSetReadyNoCongest else checkSigSetReadyGuarded
  let l := ready l
  let r := ready r
  let l := checkSigCheckL hψ l
  let r := checkSigCheckR hψ l r
  let l := checkSigSetResult l
  let r := checkSigSetResult r
  if r.label = ⟨ψ - 1, by omega⟩ ∧ r.state = .equal then
    if allowBirth κ g l r then (l, { r with leader := true })
    else (clearCmp l, clearCmp r)
  else (l, r)

/-- K2's MOVE with the absorption guard not restricted to a follower responder. -/
def absorbAnyMove {ψ : Nat} (hψ : ψ > 0) (nl : Fin ψ)
    (l r : AgentState ψ) : AgentState ψ × AgentState ψ :=
  if l.leader = true ∧ l.shield = true ∧ r.bullet = (2 : Fin 3) then
    (l, { r with bullet := (0 : Fin 3) })
  else
    eliminateLeadersNoCollisionZeroLeaderEgressMove hψ nl l r

/-- `PPLLElimVariants.k2Kernel` with `absorbAnyMove`. -/
def k3Kernel {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ) :
    AgentState ψ × AgentState ψ :=
  let nl : Fin ψ := ⟨(l.label.val + 1) % ψ, Nat.mod_lt _ hψ⟩
  let q0 := eliminateLeadersNoCollisionFire hψ l r
  let q1 := absorbAnyMove hψ nl q0.1 q0.2
  let q2 := eliminateLeadersNoCollisionSignalLeaderSink nl q1.1 q1.2
  dummyBulletSink q2

/-- K3 with the kill branch of MOVE evaluated before FIRE as well: an
unshielded leader facing a live bullet dies before it can shield itself by
firing.  Targets the all-leader label-`0…0` bottom, where every unshielded
leader already holds the absence signal and re-shields on the kill edge. -/
def k4Kernel {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ) :
    AgentState ψ × AgentState ψ :=
  let (l, r) :=
    if r.bullet = (2 : Fin 3) ∧ l.leader = true ∧ l.shield = false then
      ({ l with leader := false }, { r with bullet := (1 : Fin 3) })
    else (l, r)
  k3Kernel hψ l r

inductive ElimG where
  | base (e : Elim)
  | k3
  | k4

def elimG {ψ : Nat} (hψ : ψ > 0) (e : ElimG) (l r : AgentState ψ) :
    AgentState ψ × AgentState ψ :=
  match e with
  | .base e => elimStage hψ e l r
  | .k3 => k3Kernel hψ l r
  | .k4 => k4Kernel hψ l r

/-- States of an in-flight Algorithm-7 wave (`AuthorizedComparisonRepair.comparisonActive`,
AuthorizedComparisonRepair.lean:135-138). -/
def comparisonActive (st : MainState) : Bool :=
  match st with
  | .congest | .lock | .compare1 | .compare2 => true
  | _ => false

/-- Restatement of `AuthorizedComparisonRepair.cmpUpdateReturnPriority`
(AuthorizedComparisonRepair.lean:151-163), the T18 repair of the Algorithm-7
state wave: the return wave moves left before a forward branch can overwrite it. -/
def cmpUpdateReturnPriority {ψ : Nat} (l r : AgentState ψ) :
    AgentState ψ × AgentState ψ :=
  if l.label.val = ψ - 1 ∧ r.state = .compare1 then
    ({ l with state := .compare2 }, r)
  else if r.state = .compare1 ∨ r.state = .compare2 then
    ({ l with state := r.state }, r)
  else if l.label.val = ψ - 1 ∧ l.state = .congest then
    (l, { r with state := .lock })
  else if r.label.val = ψ - 1 ∧ l.state = .lock then
    (l, { r with state := .compare1 })
  else if l.state = .congest ∨ l.state = .lock then
    (l, { r with state := l.state })
  else (l, r)

/-- CMP_UPDATE with the T18 repair on the raw carrier: the line-1 `congest`
start (with the base's re-arm guard) never overwrites an active wave state, and
propagation is return-priority.  Unlike `authorizedCmpUpdate` there is no
moved-carrier permit (the census carrier has no such field). -/
def cmpUpdateRP {ψ : Nat} (hψ : ψ > 0) (cmp : Cmp) (l r : AgentState ψ) :
    AgentState ψ × AgentState ψ :=
  let base : Bool := match cmp with
    | .original => decide (l.label = ⟨0, hψ⟩)
    | .noSourceRearm => decide (l.label = ⟨0, hψ⟩ ∧ l.state ≠ .depart)
    | .leaderlessRearm => decide (l.label = ⟨0, hψ⟩ ∧ (l.state ≠ .depart ∨ l.leader = false))
  let l := if base && !comparisonActive l.state then { l with state := .congest } else l
  let q := cmpUpdateReturnPriority l r
  (cmpUpdateSetPath2 hψ q.1, q.2)

/-- `PPLLBirthPatchM2.compareSigM2` (non-path-keyed M2) with `cmpUpdateRP`. -/
def compareSigRP {ψ : Nat} (hψ : ψ > 0) (cmp : Cmp) (l r : AgentState ψ) :
    AgentState ψ × AgentState ψ :=
  let l := compareSigInit l
  match l.path with
  | .bot => (l, r)
  | .some _ _ =>
    match r.path with
    | .some _ _ =>
      let q := cmpUpdateRP hψ cmp l r
      let q := (keepElim l q.1, keepElim r q.2)
      compareSigDispatch hψ q.1 q.2
    | .bot => (l, r)

structure Guard where
  cmpRP : Bool := false
  readyNoCongest : Bool := false
  probeWall : Bool := false
  leaderWall : Bool := false
  resetPre : Bool := false
  resetKill : Bool := false
  check : CheckGuard := .none

/-- `PPLLElimVariants.pipelineM2` with the guards of `g`. -/
def pipeline {ψ : Nat} (hψ : ψ > 0) (κ : Nat) (cmp : Cmp) (m : M2) (e : ElimG)
    (g : Guard) (l r : AgentState ψ) : AgentState ψ × AgentState ψ :=
  let q := if g.probeWall then pPsiProbeWall hψ l r else pPsi hψ l r
  let q := genSigSaturated hψ κ q.1 q.2
  let q := cleanSig hψ q.1 q.2
  let q := eliminateSig hψ q.1 q.2
  let q := if g.leaderWall then sigMoveWalled hψ m q.1 q.2 else sigMoveM2 hψ m q.1 q.2
  let q := if m = .dropMisaligned then (dropStale q.1, dropStale q.2) else q
  let q := if g.resetPre then preCheckReset q.1 q.2 else q
  let q := checkSigGuarded hψ κ g.check g.readyNoCongest q.1 q.2
  let q := disappear hψ q.1 q.2
  let q := if g.cmpRP then compareSigRP hψ cmp q.1 q.2 else compareSigM2 hψ cmp m q.1 q.2
  let q := if g.resetKill then suppressSigResetKill hψ q.1 q.2 else suppressSig hψ q.1 q.2
  let q := elimG hψ e q.1 q.2
  writeSeq hψ q.1 q.2

/-- Named guard sets. -/
def guards : List (String × Guard) :=
  let wall : Guard := { probeWall := true, leaderWall := true, resetPre := true, resetKill := true }
  [ ("Ctl", {})
  , ("RK", { resetKill := true })                          -- p.29 prose
  , ("RKP", { resetPre := true, resetKill := true })       -- + T24 order fix
  , ("LW", { leaderWall := true })                         -- p.31 leader wall
  , ("LWRK", { leaderWall := true, resetPre := true, resetKill := true })
  , ("Wall", wall)
  , ("CGL", { check := .leaderGroup })
  , ("CGR", { check := .resetEvidence })
  , ("CGC", { check := .countGate })
  , ("CGE", { check := .elimEvidence })
  , ("WallCGR", { wall with check := .resetEvidence })
  , ("WallCGC", { wall with check := .countGate })
  , ("WallCGE", { wall with check := .elimEvidence })
  , ("NC", { readyNoCongest := true })
  , ("LWNC", { leaderWall := true, readyNoCongest := true })
  , ("WallNC", { wall with readyNoCongest := true })
  , ("RKNC", { resetPre := true, resetKill := true, readyNoCongest := true })
  , ("RKLNC", { resetKill := true, readyNoCongest := true })   -- + NC
  , ("PreNC", { resetPre := true, readyNoCongest := true })
  , ("RP", { cmpRP := true })                              -- T18 repair only
  , ("NCRP", { readyNoCongest := true, cmpRP := true })
  , ("WallRP", { wall with cmpRP := true })
  , ("WallNCRP", { wall with readyNoCongest := true, cmpRP := true }) ]

/-- `I0` is the integrated base without the M1 re-arm (`cmpUpdateNoSourceRearm`,
the T9 repair), used to test whether the M1 leaderless trap returns. -/
def bases : List (String × Cmp) :=
  [("B", .original), ("I", .leaderlessRearm), ("I0", .noSourceRearm)]

def m2s : List (String × M2) :=
  [("M1", .none), ("DropMis", .dropMisaligned), ("StaleBlock", .staleBlock)]

def elims : List (String × ElimG) :=
  [("K2", .base .k2), ("Src", .base .source), ("NoCol", .base .noCollision), ("K3", .k3), ("K4", .k4)]

/-- All named variants `peg<base><m2><guard><elim>`, e.g. `pegIDropMisWallK2`. -/
def variants : List (String × Cmp × M2 × ElimG × Guard) :=
  bases.flatMap fun (bs, cmp) => m2s.flatMap fun (ms, m) =>
    guards.flatMap fun (gs, g) => elims.map fun (es, e) =>
      (s!"peg{bs}{ms}{gs}{es}", cmp, m, e, g)

def run {ψ : Nat} (hψ : ψ > 0) (κ : Nat) (t : Cmp × M2 × ElimG × Guard)
    (l r : AgentState ψ) : AgentState ψ × AgentState ψ :=
  let (cmp, m, e, g) := t
  pipeline hψ κ cmp m e g l r

end PPLLPostElectionGuard
