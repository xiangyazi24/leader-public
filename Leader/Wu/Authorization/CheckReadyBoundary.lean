import Leader.Wu.Authorization.GenerationDrain

/-!
# A local CHECK component boundary in the unchanged AuthF pipeline

The scoped row is a same-lineage, token-free internal link from lineage
`depart` to `CHECK_ready`. Its responder is strictly before the terminal, so
arbitrary lottery carries cannot turn the responder into an elimination signal.
CHECK leaves this boundary unchanged, and repair releases the ready responder.
This is one cell of a component argument, not a whole-component sweep theorem.
-/
namespace PPLLAuthCheckComponent

open PPLL PPLLRepair PPLLBirthPatch PPLLBirthPatchM2 PPLLPostElectionGuard
open PPLLFableDesignR1 PPLLAstraDesign2 PPLLAstraDesign3 PPLLAuthF
open PPLLAuthF.AuthState

set_option autoImplicit false

variable {ψ : Nat}

/-- The unchanged candidate used by the frontier campaign. -/
def cfg : PPLLAuthF.Cfg :=
  { retire := true, markClean := true, claimCheck := true }

/-- Comparison fields relevant to this local boundary; lottery registers,
CLEAN records, WAIT and writer fields remain outside this view. -/
def View (u : AuthState ψ) :=
  (u.core.label, u.core.state, u.core.path, u.core.path2,
    u.core.leader, u.core.reset_cmd, u.path_mark, u.ctrl_mark)

/-- A ready component's left boundary, after CLEAN. The two path colours agree;
the departed initiator is in lineage mode, while the ready cell's control
colour is arbitrary. Neither lottery register is restricted. -/
structure ReadyBoundary (l r : AuthState ψ) (k bl br : Nat) : Prop where
  lk : l.core.label.val = k
  rk : r.core.label.val = k + 1
  interior : k + 1 < ψ - 1
  lp : l.core.path = .some k bl
  rp : r.core.path = .some (k + 1) br
  ls : l.core.state = .depart
  rs : r.core.state = .CHECK_ready
  lt : l.core.path2 = none
  rt : r.core.path2 = none
  ll : l.core.leader = false
  rl : r.core.leader = false
  lr : l.core.reset_cmd = false
  rr : r.core.reset_cmd = false
  pm : r.path_mark = l.path_mark
  cm : l.ctrl_mark = l.path_mark

/-- The core projection used to discard WAIT bookkeeping. -/
private def CoreView (u : AgentState ψ) :=
  (u.label,u.state,u.path,u.path2,u.leader,u.reset_cmd,u.path4,u.path5)

private theorem coreView_ite (p : Prop) [Decidable p] (a b : AgentState ψ) :
    CoreView (if p then a else b) = if p then CoreView a else CoreView b := by
  split <;> rfl

/-- WAIT keeps the comparison and CLEAN inputs used by this row. -/
private theorem wait_coreView (hp : ψ > 0) (κ : Nat) (l r : AgentState ψ) :
    CoreView (waitSaturated hp κ l r).1 = CoreView l ∧
      CoreView (waitSaturated hp κ l r).2 = CoreView r := by
  have prep (a b : AgentState ψ) :
      CoreView (waitSaturatedPrepare hp a b).1 = CoreView a ∧
      CoreView (waitSaturatedPrepare hp a b).2 = CoreView b := by
    unfold waitSaturatedPrepare
    (repeat' (first | (dsimp only) | split)) <;> exact ⟨rfl,rfl⟩
  have carry (a b : AgentState ψ) :
      CoreView (waitSaturatedCarry hp κ a b).1 = CoreView a ∧
      CoreView (waitSaturatedCarry hp κ a b).2 = CoreView b := by
    unfold waitSaturatedCarry
    (repeat' (first | (dsimp only) | split)) <;> exact ⟨rfl,rfl⟩
  have reset (a b : AgentState ψ) :
      CoreView (waitSaturatedReset hp a b).1 = CoreView a ∧
      CoreView (waitSaturatedReset hp a b).2 = CoreView b := by
    unfold waitSaturatedReset
    (repeat' (first | (dsimp only) | split)) <;> exact ⟨rfl,rfl⟩
  have finish (a b : AgentState ψ) :
      CoreView (waitSaturatedFinish hp κ a b).1 = CoreView a ∧
      CoreView (waitSaturatedFinish hp κ a b).2 = CoreView b := by
    unfold waitSaturatedFinish
    (repeat' (first | (dsimp only) | split)) <;> exact ⟨rfl,rfl⟩
  let a := waitSaturatedPrepare hp l r
  let b := waitSaturatedCarry hp κ a.1 a.2
  let c := waitSaturatedReset hp b.1 b.2
  exact ⟨(finish c.1 c.2).1.trans ((reset b.1 b.2).1.trans
      ((carry a.1 a.2).1.trans (prep l r).1)),
    (finish c.1 c.2).2.trans ((reset b.1 b.2).2.trans
      ((carry a.1 a.2).2.trans (prep l r).2))⟩

/-- At a quiescent ready boundary, GENSIG only performs its existing WAIT
bookkeeping: no generation guard can fire on these full, non-generation cells. -/
private theorem gen_ready_boundary (hp : ψ > 0) (κ : Nat) (l r : AuthState ψ)
    (k bl br : Nat) (h : ReadyBoundary l r k bl br) :
    genSigAuth hp κ l r = lift2 (waitSaturated hp κ) l r := by
  have hw := PPLLAuthGenDrain.W_fields hp κ l r
  rcases hw with ⟨a1,a2,a3,a4,a5,a6,a7,b1,b2,b3,b4,b5,b6,b7⟩
  unfold genSigAuth
  generalize lift2 (waitSaturated hp κ) l r = q at a1 a2 a3 a4 a5 a6 a7 b1 b2 b3 b4 b5 b6 b7 ⊢
  rcases q with ⟨a,b⟩
  simp only at a1 a2 a3 a4 a5 a6 a7 b1 b2 b3 b4 b5 b6 b7
  simp [AuthState.st, a1, a2, b1, h.lp, h.ls, h.rs]

/-- CLEAN cannot delete this same-lineage link. Its newly generated records
match the adjacent own paths; old CLEAN slots are empty at the input cut. -/
private theorem clean_ready_view (hp : ψ > 0) (l r : AuthState ψ) (k bl br : Nat)
    (h : ReadyBoundary l r k bl br)
    (hl4 : l.core.path4 = none) (hl5 : l.core.path5 = none)
    (hr4 : r.core.path4 = none) (hr5 : r.core.path5 = none) :
    View (cleanSourceAuth hp cfg l r).1 = View l ∧
      View (cleanSourceAuth hp cfg l r).2 = View r := by
  have hkT : k ≠ ψ - 1 := by have := h.interior; omega
  have hrT : k+1 ≠ ψ - 1 := by have := h.interior; omega
  have hki : (k : Int) ≠ -1 := by omega
  have hri : ((k+1 : Nat) : Int) ≠ -1 := by omega
  have hsub : ((k+1 : Nat) : Int) - 1 = (k : Int) := by omega
  have hri' : (k : Int) + 1 ≠ -1 := by omega
  by_cases hk0 : k = 0
  · subst k
    simp [cleanSourceAuth, cfg, genConnectAuth, cleanSigGenConnect,
      step3Auth, step4Auth, step5Auth, step6Auth, cleanApplyAuth,
      isCmd, View, h.lp, h.rp, h.pm, hl4, hl5, hr4, hr5,
      hkT, hrT, hki, hri, hsub]
  · simp [cleanSourceAuth, cfg, genConnectAuth, cleanSigGenConnect,
      step3Auth, step4Auth, step5Auth, step6Auth, cleanApplyAuth,
      isCmd, View, h.lp, h.rp, h.pm, hl4, hl5, hr4, hr5,
      hk0, hkT, hrT, hki, hri, hri', hsub]

/-- MOVE is the identity at this occupied token-free boundary. -/
private theorem move_ready_boundary (hp : ψ > 0) (l r : AuthState ψ)
    (k bl br : Nat) (h : ReadyBoundary l r k bl br) :
    moveSourceAuth hp cfg l r = (l,r) := by
  simp [moveSourceAuth, validateCheck, headBad, checkState, verdict,
    isHead, aligned, sanitizeP2, p2Valid, step1Auth, moveTokensAuth,
    leaderWallAuth, applyControlAuth, AuthState.st, h.lp, h.rp,
    h.lk, h.rk, h.ls, h.rs, h.lt, h.rt, h.ll, h.rl]

/-- On this boundary neither an independent ready assignment nor CHECK result
propagation changes either endpoint: the departed predecessor is not equal. -/
theorem check_ready_boundary (hp : ψ > 0) (l r : AuthState ψ) (k bl br : Nat)
    (h : ReadyBoundary l r k bl br) : checkSourceAuth hp cfg l r = (l,r) := by
  have hvl : validateCheck l r = (l,r) := by
    simp [validateCheck, headBad, checkState, verdict, isHead, h.rk,
      AuthState.st, h.ls, h.rs]
  have hreadyL : readyAuth l = l := by
    simp [readyAuth, waveState, checkSigSetReadyGuarded, controlPending,
      checkSigSetReady, AuthState.st, h.lp, h.lt, h.ls]
  have hreadyR : readyAuth r = r := by
    have hu : {r.core with state := .CHECK_ready} = r.core := by rw [← h.rs]
    simp [readyAuth, waveState, checkSigSetReadyGuarded, controlPending,
      checkSigSetReady, AuthState.st, h.rp, h.rt, h.rs, h.rk, hu]
    rw [← h.rp, ← h.rt, ← h.rs]
  have hL : checkSigCheckL hp l.core = l.core := by
    cases hk : k <;> simp [checkSigCheckL, h.lp, hk, h.ls]
  have hcert : certPred l r = false := by simp [certPred,h.lp,h.rp,AuthState.st,h.ls]
  have hil : issue l = l := by simp [issue,AuthState.st,h.ls]
  have hir : issue r = r := by simp [issue,AuthState.st,h.rs]
  simp [checkSourceAuth,cfg,hvl,hreadyL,hreadyR,AuthState.st,h.rs,hL,
    AuthState.withCore,hcert,hil,hir]

/-- DISAPPEAR may update arbitrary lottery bits but keeps every comparison
field at an internal nonterminal ready boundary. -/
theorem disappear_ready_view (hp : ψ > 0) (l r : AuthState ψ) (k bl br : Nat)
    (h : ReadyBoundary l r k bl br) :
    View (disappearAuth hp l r).1 = View l ∧
      View (disappearAuth hp l r).2 = View r := by
  have hrt : r.core.label ≠ ⟨ψ - 1, by omega⟩ := by
    intro he
    have hv := congrArg Fin.val he
    simp only at hv
    have := h.interior
    rw [h.rk] at hv
    omega
  cases hc : l.core.p_carry <;> cases hb : r.core.p <;>
    simp [disappearAuth, disappearStartL, disappearCarry, lift2, View,
      AuthState.st, h.ls, h.rs, hc, hb, hrt]

/-- Transfer the boundary through any stage that keeps its comparison view. -/
theorem ReadyBoundary.of_view {l r a b : AuthState ψ} {k bl br : Nat}
    (h : ReadyBoundary l r k bl br) (ha : View a = View l) (hb : View b = View r) :
    ReadyBoundary a b k bl br := by
  simp only [View, Prod.mk.injEq] at ha hb
  rcases ha with ⟨a1,a2,a3,a4,a5,a6,a7,a8⟩
  rcases hb with ⟨b1,b2,b3,b4,b5,b6,b7,b8⟩
  constructor <;> simp_all [h.lk, h.rk, h.interior, h.lp, h.rp, h.ls, h.rs,
    h.lt, h.rt, h.ll, h.rl, h.lr, h.rr, h.pm, h.cm]

/-- Repair releases precisely the ready successor, keeping its payload and
stamping its control colour with its own path lineage. -/
theorem repair_ready_boundary (l r : AuthState ψ) (k bl br : Nat)
    (h : ReadyBoundary l r k bl br) :
    repairAuth l r = (l, r.lineage .depart) := by
  simp [repairAuth, liftLife, normalizeCarrier, normalizeOrphan,
    releaseCongest, lift2Life, releaseReadySuffix, ackTailAuth, lift2,
    ackTail, lockedState, AuthState.lineage, h.lp, h.rp, h.ls, h.rs,
    h.ll, h.rl, h.lt, h.rt]

/-- Adjacent lineage-departed cells on an internal edge cannot start a BEQ
session. This prevents immediate recreation of the erased ready boundary. -/
theorem compare_depart_boundary (κ : Nat) (l r : AuthState ψ) (k bl br : Nat)
    (hlp : l.core.path = .some k bl) (hrp : r.core.path = .some (k+1) br)
    (hkt : k + 1 < ψ - 1) (hls : l.core.state = .depart)
    (hrs : r.core.state = .depart) (hlt : l.core.path2 = none)
    (hrt : r.core.path2 = none) (hlm : l.ctrl_mark = l.path_mark)
    (hrm : r.ctrl_mark = r.path_mark) : compareLifecycleAuth κ l r = (l,r) := by
  have hk : k ≠ ψ - 1 := by omega
  simp [compareLifecycleAuth, maintainAuth, completeWaveAuth, waveAuth,
    lift2, PPLLFableDesignR1.dropStray, landBackwardAuth, landForwardAuth,
    lockedState, waveState, sessionTokenOn, AuthState.st,
    hlp, hrp, hls, hrs, hlt, hrt, hlm, hrm, hk]
  cases l <;> cases r <;> simp_all

/-- Literal suffix from CHECK through COMPARE, as it occurs in the pipeline.
This cut is introduced only for composition with the unchanged prefix. -/
def checkSuffix (hp : ψ > 0) (κ : Nat) (l r : AuthState ψ) :
    AuthState ψ × AuthState ψ :=
  let q := checkSourceAuth hp cfg l r
  let q := disappearAuth hp q.1 q.2
  let q := repairAuth q.1 q.2
  compareLifecycleAuth κ q.1 q.2

/-- One internal ready boundary is erased by the literal CHECK-to-COMPARE
suffix. The output statement includes payload/token preservation and lineage
restamping; it is not a promise about the rest of the component. -/
theorem suffix_ready_boundary (hp : ψ > 0) (κ : Nat) (l r : AuthState ψ)
    (k bl br : Nat) (h : ReadyBoundary l r k bl br) :
    let q := checkSuffix hp κ l r
    q.1.core.state = .depart ∧ q.2.core.state = .depart ∧
    q.1.core.path = l.core.path ∧ q.2.core.path = r.core.path ∧
    q.1.core.path2 = none ∧ q.2.core.path2 = none ∧
    q.1.ctrl_mark = q.1.path_mark ∧ q.2.ctrl_mark = q.2.path_mark := by
  unfold checkSuffix
  rw [check_ready_boundary hp l r k bl br h]
  dsimp only
  let d := disappearAuth hp l r
  have hf := disappear_ready_view hp l r k bl br h
  have hd : ReadyBoundary d.1 d.2 k bl br := h.of_view hf.1 hf.2
  rw [repair_ready_boundary d.1 d.2 k bl br hd]
  rw [compare_depart_boundary κ d.1 (d.2.lineage .depart) k bl br
    hd.lp hd.rp hd.interior hd.ls rfl hd.lt hd.rt hd.cm rfl]
  exact ⟨hd.ls, rfl, hd.lp.trans h.lp.symm, hd.rp.trans h.rp.symm,
    hd.lt, hd.rt, hd.cm, rfl⟩

/-- Release, ELIMINATE, MOVE, stale-carrier cleanup, reset and readiness at
this cut. The complete composition is identical to the accepted prefix. -/
private def afterClean (hp : ψ > 0) (l r : AuthState ψ) :
    AuthState ψ × AuthState ψ :=
  let q := lift2Life (releaseSource hp) l r
  let q := lift2 (eliminateSig hp) q.1 q.2
  let q := moveSourceAuth hp cfg q.1 q.2
  let q := (liftLife dropStale q.1, liftLife dropStale q.2)
  let q := preCheckResetAuth q.1 q.2
  (liftLife normalizeReady q.1, liftLife normalizeReady q.2)

private theorem afterClean_ready (hp : ψ > 0) (l r : AuthState ψ)
    (k bl br : Nat) (h : ReadyBoundary l r k bl br) :
    afterClean hp l r = (l,r) := by
  have hm := move_ready_boundary hp l r k bl br h
  simp only [afterClean, lift2Life, releaseSource, h.rs, h.ls]
  simp [lift2, eliminateSig, h.rs, hm, liftLife, dropStale,
    aligned, preCheckResetAuth, normalizeReady, normalizeOrphan,
    normalizeCarrier, releaseCongest, h.ll, h.rl, h.lr, h.rr,
    h.lp, h.rp, h.lk, h.rk, h.ls, h.rs]

private theorem restPair_eq (hp : ψ > 0) (κ : Nat) (l r : AuthState ψ) :
    PPLLAuthGenDrain.restPair hp κ cfg (l,r) =
      let c := cleanSourceAuth hp cfg l r
      let a := afterClean hp c.1 c.2
      checkSuffix hp κ a.1 a.2 := by rfl

/-- The actual unchanged full-row leaf. A same-lineage ready boundary before
an internal nonterminal responder becomes two lineage departures, retaining
both paths and empty token slots. CLEAN is initially quiescent. All lottery,
writer and echo fields are arbitrary. No whole-component decrease is claimed. -/
theorem pipeline_ready_boundary (hp : ψ > 0) (κ : Nat) (l r : AuthState ψ)
    (k bl br : Nat) (h : ReadyBoundary l r k bl br)
    (hl4 : l.core.path4 = none) (hl5 : l.core.path5 = none)
    (hr4 : r.core.path4 = none) (hr5 : r.core.path5 = none) :
    let q := PPLLAuthF.pipeline hp κ cfg l r
    q.1.core.state = .depart ∧ q.2.core.state = .depart ∧
    q.1.core.path = l.core.path ∧ q.2.core.path = r.core.path ∧
    q.1.core.path2 = none ∧ q.2.core.path2 = none ∧
    q.1.ctrl_mark = q.1.path_mark ∧ q.2.ctrl_mark = q.2.path_mark := by
  have row : PPLLAuthGenDrain.RowH ψ l r k :=
    ⟨h.lk,h.rk,Nat.le_of_lt h.interior,h.ll,h.rl,h.lr,h.rr⟩
  obtain ⟨x,y,hf1,hf2⟩ := PPLLAuthGenDrain.row_open hp κ cfg l r k row
  let a := PPLLAuthGenDrain.withProbe l x
  let b := PPLLAuthGenDrain.withProbe r y
  have hab : ReadyBoundary a b k bl br := by
    constructor <;> simp [a,b,PPLLAuthGenDrain.withProbe,h.lk,h.rk,h.interior,
      h.lp,h.rp,h.ls,h.rs,h.lt,h.rt,h.ll,h.rl,h.lr,h.rr,h.pm,h.cm]
  have hg := gen_ready_boundary hp κ a b k bl br hab
  rw [hg] at hf1 hf2
  let w := lift2 (waitSaturated hp κ) a b
  have hw := wait_coreView hp κ a.core b.core
  simp only [CoreView, Prod.mk.injEq] at hw
  rcases hw with ⟨⟨a1,a2,a3,a4,a5,a6,a7,a8⟩,⟨b1,b2,b3,b4,b5,b6,b7,b8⟩⟩
  have hwv1 : View w.1 = View a := by
    simp only [w,lift2,View,a1,a2,a3,a4,a5,a6]
  have hwv2 : View w.2 = View b := by
    simp only [w,lift2,View,b1,b2,b3,b4,b5,b6]
  have hwready : ReadyBoundary w.1 w.2 k bl br := hab.of_view hwv1 hwv2
  have hw4 : w.1.core.path4 = none := a7.trans hl4
  have hw5 : w.1.core.path5 = none := a8.trans hl5
  have hw4' : w.2.core.path4 = none := b7.trans hr4
  have hw5' : w.2.core.path5 = none := b8.trans hr5
  let c := cleanSourceAuth hp cfg w.1 w.2
  have hc := clean_ready_view hp w.1 w.2 k bl br hwready hw4 hw5 hw4' hw5'
  have hcReady : ReadyBoundary c.1 c.2 k bl br := hwready.of_view hc.1 hc.2
  have ha := afterClean_ready hp c.1 c.2 k bl br hcReady
  have hs := suffix_ready_boundary hp κ c.1 c.2 k bl br hcReady
  have he : PPLLAuthGenDrain.restPair hp κ cfg w = checkSuffix hp κ c.1 c.2 := by
    have he0 := restPair_eq hp κ w.1 w.2
    change PPLLAuthGenDrain.restPair hp κ cfg w = _ at he0
    dsimp only at he0
    rw [ha] at he0
    exact he0
  change PPLLAuthGenDrain.FV (PPLLAuthF.pipeline hp κ cfg l r).1 =
    PPLLAuthGenDrain.FV (PPLLAuthGenDrain.restPair hp κ cfg w).1 at hf1
  change PPLLAuthGenDrain.FV (PPLLAuthF.pipeline hp κ cfg l r).2 =
    PPLLAuthGenDrain.FV (PPLLAuthGenDrain.restPair hp κ cfg w).2 at hf2
  rw [he] at hf1 hf2
  rcases hs with ⟨s1,s2,s3,s4,s5,s6,s7,s8⟩
  refine ⟨(PPLLAuthGenDrain.FV_state hf1).trans s1,
    (PPLLAuthGenDrain.FV_state hf2).trans s2,
    (PPLLAuthGenDrain.FV_path hf1).trans (s3.trans (hcReady.lp.trans h.lp.symm)),
    (PPLLAuthGenDrain.FV_path hf2).trans (s4.trans (hcReady.rp.trans h.rp.symm)),
    (PPLLAuthGenDrain.FV_path2 hf1).trans s5,
    (PPLLAuthGenDrain.FV_path2 hf2).trans s6, ?_, ?_⟩
  · rw [PPLLAuthGenDrain.FV_ctrl hf1, PPLLAuthGenDrain.FV_pm hf1]
    exact s7
  · rw [PPLLAuthGenDrain.FV_ctrl hf2, PPLLAuthGenDrain.FV_pm hf2]
    exact s8

#print axioms check_ready_boundary
#print axioms disappear_ready_view
#print axioms repair_ready_boundary
#print axioms suffix_ready_boundary
#print axioms pipeline_ready_boundary

end PPLLAuthCheckComponent
