import Leader.Wu.Authorization.CheckReadyBoundary

/-!
# A ready-component row with arbitrary CLEAN records

This strengthens the frozen quiescent-CLEAN leaf. A deletion is counted only
at the final original AuthF pipeline endpoint. The continuing branch records
both original path colours, permitting the next component edge to use them.
-/
namespace PPLLAuthCheckComponentFrame

open PPLL PPLLRepair PPLLBirthPatch PPLLBirthPatchM2 PPLLPostElectionGuard
open PPLLFableDesignR1 PPLLAstraDesign2 PPLLAstraDesign3 PPLLAuthF
open PPLLAuthF.AuthState PPLLAuthCheckComponent

set_option autoImplicit false
variable {ψ : Nat}

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

private theorem move_ready_boundary (hp : ψ > 0) (l r : AuthState ψ)
    (k bl br : Nat) (h : ReadyBoundary l r k bl br) :
    moveSourceAuth hp cfg l r = (l,r) := by
  simp [moveSourceAuth, validateCheck, headBad, checkState, verdict,
    isHead, aligned, sanitizeP2, p2Valid, step1Auth, moveTokensAuth,
    leaderWallAuth, applyControlAuth, AuthState.st, h.lp, h.rp,
    h.lk, h.rk, h.ls, h.rs, h.lt, h.rt, h.ll, h.rl]

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

/-- WAIT preserves the ready-boundary predicate, with arbitrary non-comparison fields. -/
private theorem wait_ready (hp : ψ > 0) (κ : Nat) (l r : AuthState ψ)
    (k bl br : Nat) (h : ReadyBoundary l r k bl br) :
    ReadyBoundary (lift2 (waitSaturated hp κ) l r).1
      (lift2 (waitSaturated hp κ) l r).2 k bl br := by
  have hw := PPLLAuthGenDrain.W_fields hp κ l r
  have hd := PPLLAuthResetDrain.wait_dv hp κ l.core r.core
  simp only [PPLLAuthResetDrain.dv,Prod.mk.injEq] at hd
  rcases hw with ⟨a1,a2,a3,a4,a5,a6,a7,b1,b2,b3,b4,b5,b6,b7⟩
  rcases hd with ⟨⟨ar,_,_,_⟩,⟨brs,_,_,_⟩⟩
  constructor <;> simp_all [h.lk,h.rk,h.interior,h.lp,h.rp,h.ls,h.rs,
    h.lt,h.rt,h.ll,h.rl,h.lr,h.rr,h.pm,h.cm,lift2]

/-- At a positive nonterminal responder, CLEAN overwrites both old records
with matching fresh records, so only the initiator can be deleted. -/
private theorem clean_right_path (hp : ψ > 0) (l r : AuthState ψ)
    (k bl br : Nat) (h : ReadyBoundary l r k bl br) :
    (cleanSourceAuth hp cfg l r).2.core.path = r.core.path := by
  have hkT : k ≠ ψ - 1 := by have := h.interior; omega
  have hrT : k+1 ≠ ψ - 1 := by have := h.interior; omega
  have hki : (k : Int) ≠ -1 := by omega
  have hri : (k : Int)+1 ≠ -1 := by omega
  by_cases hk0 : k = 0
  · subst k
    cases ht : l.core.path4 with
    | none =>
        simp [cleanSourceAuth,cfg,genConnectAuth,cleanSigGenConnect,step3Auth,
          step4Auth,step5Auth,step6Auth,cleanApplyAuth,isCmd,h.lp,h.rp,h.pm,ht,hkT,hrT]
    | some t =>
        rcases t with ⟨v,bit⟩
        by_cases hv : v = -1 <;>
          simp [cleanSourceAuth,cfg,genConnectAuth,cleanSigGenConnect,step3Auth,
            step4Auth,step5Auth,step6Auth,cleanApplyAuth,isCmd,h.lp,h.rp,h.pm,ht,hkT,hrT,hv]
  · simp [cleanSourceAuth,cfg,genConnectAuth,cleanSigGenConnect,step3Auth,
      step4Auth,step5Auth,step6Auth,cleanApplyAuth,isCmd,h.lp,h.rp,h.pm,
      hk0,hkT,hrT,hki,hri]

/-- CLEAN's accepted path alternatives and field frames specialize to this
boundary. The surviving case has the same exact ready predicate. -/
private theorem clean_ready_or_left_hole (hp : ψ > 0) (l r : AuthState ψ)
    (k bl br : Nat) (h : ReadyBoundary l r k bl br) :
    let q := cleanSourceAuth hp cfg l r
    q.1.core.path = .bot ∨
      (ReadyBoundary q.1 q.2 k bl br ∧
        q.1.path_mark = l.path_mark ∧ q.2.path_mark = r.path_mark) := by
  have hv := PPLLAuthGenDrain.T1_cv hp cfg (l,r)
  have ha := PPLLAuthGenDrain.T1_pa hp cfg (l,r)
  have hrp := clean_right_path hp l r k bl br h
  simp only [PPLLAuthGenDrain.T1] at hv ha
  rcases hv with ⟨vl,vr,pl,_⟩
  rcases pl with pl | pl
  · right
    simp only [PPLLAuthGenDrain.cv,Prod.mk.injEq] at vl vr
    simp only [PPLLAuthGenDrain.PA,PPLLAuthResetDrain.av,PPLLAuthResetDrain.dv,
      Prod.mk.injEq] at ha
    rcases vl with ⟨a1,a2,a3,a4,a5⟩
    rcases vr with ⟨b1,b2,b3,b4,b5⟩
    rcases ha with ⟨⟨a6,_,a7,a8⟩,⟨b6,_,b7,b8⟩⟩
    refine ⟨?_,a5,b5⟩
    constructor <;> simp_all [h.lk,h.rk,h.interior,h.lp,h.rp,h.ls,h.rs,
      h.lt,h.rt,h.ll,h.rl,h.lr,h.rr,h.pm,h.cm]
  · exact Or.inl pl

/-- The suffix preserves each original path colour as well as the frozen
local release result. -/
theorem suffix_ready_marks (hp : ψ > 0) (κ : Nat) (l r : AuthState ψ)
    (k bl br : Nat) (h : ReadyBoundary l r k bl br) :
    (checkSuffix hp κ l r).1.path_mark = l.path_mark ∧
      (checkSuffix hp κ l r).2.path_mark = r.path_mark := by
  unfold checkSuffix
  rw [check_ready_boundary hp l r k bl br h]
  dsimp only
  let d := disappearAuth hp l r
  have hf := disappear_ready_view hp l r k bl br h
  have hd : ReadyBoundary d.1 d.2 k bl br := h.of_view hf.1 hf.2
  rw [repair_ready_boundary d.1 d.2 k bl br hd]
  rw [compare_depart_boundary κ d.1 (d.2.lineage .depart) k bl br
    hd.lp hd.rp hd.interior hd.ls rfl hd.lt hd.rt hd.cm rfl]
  exact ⟨congrArg (fun z => z.2.2.2.2.2.2.1) hf.1,
    congrArg (fun z => z.2.2.2.2.2.2.1) hf.2⟩

/-- Restore only the left path in a predicate, to describe the metadata
retained when CLEAN has removed that path. This does not change the execution. -/
private def restore (l : AuthState ψ) (k bl : Nat) : AuthState ψ :=
  {l with core := {l.core with path := .some k bl}}

private theorem clean_restore_ready (hp : ψ > 0) (l r : AuthState ψ)
    (k bl br : Nat) (h : ReadyBoundary l r k bl br) :
    let q := cleanSourceAuth hp cfg l r
    ReadyBoundary (restore q.1 k bl) q.2 k bl br := by
  have hv := PPLLAuthGenDrain.T1_cv hp cfg (l,r)
  have ha := PPLLAuthGenDrain.T1_pa hp cfg (l,r)
  have hrp := clean_right_path hp l r k bl br h
  simp only [PPLLAuthGenDrain.T1] at hv ha
  rcases hv with ⟨vl,vr,_,_⟩
  simp only [PPLLAuthGenDrain.cv,Prod.mk.injEq] at vl vr
  simp only [PPLLAuthGenDrain.PA,PPLLAuthResetDrain.av,PPLLAuthResetDrain.dv,
    Prod.mk.injEq] at ha
  rcases vl with ⟨a1,a2,a3,a4,a5⟩
  rcases vr with ⟨b1,b2,b3,b4,b5⟩
  rcases ha with ⟨⟨a6,_,a7,a8⟩,⟨b6,_,b7,b8⟩⟩
  constructor <;> simp_all [restore,h.lk,h.rk,h.interior,h.lp,h.rp,h.ls,h.rs,
    h.lt,h.rt,h.ll,h.rl,h.lr,h.rr,h.pm,h.cm]

private theorem move_hole (hp : ψ > 0) (l r : AuthState ψ) (k bl br : Nat)
    (h : ReadyBoundary (restore l k bl) r k bl br) (hlp : l.core.path = .bot) :
    moveSourceAuth hp cfg l r = (l,r) := by
  have hls : l.core.state = .depart := h.ls
  have hlt : l.core.path2 = none := h.lt
  have hll : l.core.leader = false := h.ll
  have hlr : l.core.reset_cmd = false := h.lr
  have hlk : l.core.label.val = k := h.lk
  have hlm : l.ctrl_mark = l.path_mark := h.cm
  have hpm : r.path_mark = l.path_mark := h.pm
  simp [moveSourceAuth, validateCheck, headBad, checkState, verdict,
    isHead, aligned, sanitizeP2, p2Valid, step1Auth, moveTokensAuth,
    leaderWallAuth, applyControlAuth, AuthState.st, hlp, h.rp,
    hlk, h.rk, hls, h.rs, hlt, h.rt, hll, h.rl]

private theorem afterClean_hole (hp : ψ > 0) (l r : AuthState ψ)
    (k bl br : Nat) (h : ReadyBoundary (restore l k bl) r k bl br)
    (hlp : l.core.path = .bot) : afterClean hp l r = (l,r) := by
  have hls : l.core.state = .depart := h.ls
  have hlt : l.core.path2 = none := h.lt
  have hll : l.core.leader = false := h.ll
  have hlr : l.core.reset_cmd = false := h.lr
  have hlk : l.core.label.val = k := h.lk
  have hlm : l.ctrl_mark = l.path_mark := h.cm
  have hpm : r.path_mark = l.path_mark := h.pm
  have hm := move_hole hp l r k bl br h hlp
  simp only [afterClean, lift2Life, releaseSource, h.rs, hls]
  simp [lift2, eliminateSig, h.rs, hm, liftLife, dropStale,
    aligned, preCheckResetAuth, normalizeReady, normalizeOrphan,
    normalizeCarrier, releaseCongest, hll, h.rl, hlr, h.rr,
    hlp, h.rp, hlk, h.rk, hls, h.rs]

private theorem check_hole (hp : ψ > 0) (l r : AuthState ψ) (k bl br : Nat)
    (h : ReadyBoundary (restore l k bl) r k bl br) (hlp : l.core.path = .bot) :
    checkSourceAuth hp cfg l r = (l,r) := by
  have hls : l.core.state = .depart := h.ls
  have hlt : l.core.path2 = none := h.lt
  have hll : l.core.leader = false := h.ll
  have hlr : l.core.reset_cmd = false := h.lr
  have hlk : l.core.label.val = k := h.lk
  have hlm : l.ctrl_mark = l.path_mark := h.cm
  have hpm : r.path_mark = l.path_mark := h.pm
  have hvl : validateCheck l r = (l,r) := by
    simp [validateCheck,headBad,checkState,verdict,isHead,aligned,hlp,h.rk,
      AuthState.st,hls,h.rs]
  have hreadyL : readyAuth l = l := by
    simp [readyAuth,waveState,checkSigSetReadyGuarded,controlPending,
      checkSigSetReady,AuthState.st,hlp,hlt,hls]
  have hreadyR : readyAuth r = r := by
    simp [readyAuth,waveState,checkSigSetReadyGuarded,controlPending,
      checkSigSetReady,AuthState.st,h.rp,h.rt,h.rs,h.rk]
    rw [← h.rp,← h.rt,← h.rs]
  have hL : checkSigCheckL hp l.core = l.core := by simp [checkSigCheckL,hlp]
  have hcert : certPred l r = false := by simp [certPred,hlp]
  have hil : issue l = l := by simp [issue,AuthState.st,hls]
  have hir : issue r = r := by simp [issue,AuthState.st,h.rs]
  simp [checkSourceAuth,cfg,hvl,hreadyL,hreadyR,AuthState.st,h.rs,hL,
    AuthState.withCore,hcert,hil,hir]

/-- Once CLEAN has deleted this head, the remaining actual suffix cannot fill
it. The token mover has no occupied initiator, and no later stage creates paths. -/
private theorem suffix_left_hole (hp : ψ > 0) (κ : Nat) (l r : AuthState ψ)
    (k bl br : Nat) (h : ReadyBoundary (restore l k bl) r k bl br)
    (hlp : l.core.path = .bot) : (checkSuffix hp κ l r).1.core.path = .bot := by
  have hls : l.core.state = .depart := h.ls
  have hlt : l.core.path2 = none := h.lt
  have hll : l.core.leader = false := h.ll
  have hlr : l.core.reset_cmd = false := h.lr
  have hlk : l.core.label.val = k := h.lk
  have hlm : l.ctrl_mark = l.path_mark := h.cm
  have hpm : r.path_mark = l.path_mark := h.pm
  have hrt : r.core.label ≠ ⟨ψ-1,by omega⟩ := by
    intro he
    have hv := congrArg Fin.val he
    simp only at hv
    have hi := h.interior
    rw [h.rk] at hv
    omega
  unfold checkSuffix
  rw [check_hole hp l r k bl br h hlp]
  dsimp only
  cases hc : l.core.p_carry <;> cases hb : r.core.p <;>
    simp [disappearAuth,disappearStartL,disappearCarry,lift2,
      repairAuth,liftLife,normalizeOrphan,normalizeCarrier,releaseCongest,
      lift2Life,releaseReadySuffix,ackTailAuth,ackTail,lockedState,
      compareLifecycleAuth,maintainAuth,completeWaveAuth,waveAuth,
      PPLLFableDesignR1.dropStray,landBackwardAuth,landForwardAuth,
      AuthState.st,AuthState.setState,AuthState.withCore,AuthState.lineage,
      hlp,h.rp,hls,h.rs,hll,h.rl,hlt,h.rt,hlm,hpm,hc,hb,hrt]

/-- The final local exit is an actual missing main path. -/
def PairHole (q : AuthState ψ × AuthState ψ) : Prop :=
  q.1.core.path = .bot ∨ q.2.core.path = .bot

/-- The continuing row has erased the selected ready cell without changing
its path payload or lineage. This records both endpoint lineage links. -/
def Released (l r : AuthState ψ) (q : AuthState ψ × AuthState ψ) : Prop :=
  q.1.core.state = .depart ∧ q.2.core.state = .depart ∧
  q.1.core.path = l.core.path ∧ q.2.core.path = r.core.path ∧
  q.1.core.path2 = none ∧ q.2.core.path2 = none ∧
  q.1.ctrl_mark = q.1.path_mark ∧ q.2.ctrl_mark = q.2.path_mark ∧
  q.1.path_mark = l.path_mark ∧ q.2.path_mark = r.path_mark

private theorem rest_ready_or_hole (hp : ψ > 0) (κ : Nat) (l r : AuthState ψ)
    (k bl br : Nat) (h : ReadyBoundary l r k bl br) :
    let q := PPLLAuthGenDrain.restPair hp κ cfg (l,r)
    PairHole q ∨ Released l r q := by
  dsimp only [PairHole,Released]
  let c := cleanSourceAuth hp cfg l r
  have he0 := restPair_eq hp κ l r
  dsimp only at he0
  rcases clean_ready_or_left_hole hp l r k bl br h with hh | ⟨hc,m1,m2⟩
  · have hc := clean_restore_ready hp l r k bl br h
    have ha := afterClean_hole hp c.1 c.2 k bl br hc hh
    rw [ha] at he0
    rw [he0]
    have hz := suffix_left_hole hp κ c.1 c.2 k bl br hc hh
    generalize hq : checkSuffix hp κ c.1 c.2 = q at hz ⊢
    exact Or.inl (Or.inl hz)
  · have ha := afterClean_ready hp c.1 c.2 k bl br hc
    rw [ha] at he0
    rw [he0]
    have hs := suffix_ready_boundary hp κ c.1 c.2 k bl br hc
    have hm := suffix_ready_marks hp κ c.1 c.2 k bl br hc
    generalize hq : checkSuffix hp κ c.1 c.2 = q at hs hm ⊢
    rcases hs with ⟨s1,s2,s3,s4,s5,s6,s7,s8⟩
    exact Or.inr ⟨s1,s2,s3.trans (hc.lp.trans h.lp.symm),
      s4.trans (hc.rp.trans h.rp.symm),s5,s6,s7,s8,hm.1.trans m1,hm.2.trans m2⟩

/-- Full unchanged AuthF row, with arbitrary CLEAN records. The outcome is a
hole at the final pipeline endpoint or a released ready cell retaining both
original path colours. All lottery, writer and echo fields remain arbitrary.
This is still one internal nonterminal boundary, not an equal-root or wave
component theorem. -/
theorem pipeline_ready_or_hole (hp : ψ > 0) (κ : Nat) (l r : AuthState ψ)
    (k bl br : Nat) (h : ReadyBoundary l r k bl br) :
    let q := PPLLAuthF.pipeline hp κ cfg l r
    PairHole q ∨ Released l r q := by
  dsimp only [PairHole,Released]
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
  have hw : ReadyBoundary w.1 w.2 k bl br := wait_ready hp κ a b k bl br hab
  have hs := rest_ready_or_hole hp κ w.1 w.2 k bl br hw
  change PPLLAuthGenDrain.FV (PPLLAuthF.pipeline hp κ cfg l r).1 =
    PPLLAuthGenDrain.FV (PPLLAuthGenDrain.restPair hp κ cfg w).1 at hf1
  change PPLLAuthGenDrain.FV (PPLLAuthF.pipeline hp κ cfg l r).2 =
    PPLLAuthGenDrain.FV (PPLLAuthGenDrain.restPair hp κ cfg w).2 at hf2
  change PairHole (PPLLAuthGenDrain.restPair hp κ cfg w) ∨
    Released w.1 w.2 (PPLLAuthGenDrain.restPair hp κ cfg w) at hs
  generalize hout : PPLLAuthF.pipeline hp κ cfg l r = out at hf1 hf2 ⊢
  generalize hrest : PPLLAuthGenDrain.restPair hp κ cfg w = rest at hf1 hf2 hs
  dsimp only [PairHole,Released] at hs
  rcases hs with hh | hs
  · left
    rcases hh with hh | hh
    · exact Or.inl ((PPLLAuthGenDrain.FV_path hf1).trans hh)
    · exact Or.inr ((PPLLAuthGenDrain.FV_path hf2).trans hh)
  · rcases hs with ⟨s1,s2,s3,s4,s5,s6,s7,s8,s9,s10⟩
    right
    refine ⟨(PPLLAuthGenDrain.FV_state hf1).trans s1,
      (PPLLAuthGenDrain.FV_state hf2).trans s2,
      (PPLLAuthGenDrain.FV_path hf1).trans (s3.trans (hw.lp.trans h.lp.symm)),
      (PPLLAuthGenDrain.FV_path hf2).trans (s4.trans (hw.rp.trans h.rp.symm)),
      (PPLLAuthGenDrain.FV_path2 hf1).trans s5,
      (PPLLAuthGenDrain.FV_path2 hf2).trans s6, ?_, ?_,
      (PPLLAuthGenDrain.FV_pm hf1).trans s9,
      (PPLLAuthGenDrain.FV_pm hf2).trans s10⟩
    · rw [PPLLAuthGenDrain.FV_ctrl hf1,PPLLAuthGenDrain.FV_pm hf1]
      exact s7
    · rw [PPLLAuthGenDrain.FV_ctrl hf2,PPLLAuthGenDrain.FV_pm hf2]
      exact s8

#print axioms suffix_ready_marks
#print axioms pipeline_ready_or_hole

end PPLLAuthCheckComponentFrame
