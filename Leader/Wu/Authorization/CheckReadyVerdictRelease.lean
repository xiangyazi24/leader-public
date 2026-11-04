import Leader.Wu.Authorization.CheckReadyEqualErasure
import Leader.Wu.Authorization.PostCleanHole

/-! Original nonterminal departed-anchor / larger-or-less successor release.
Source proposal, pending verification. The equal-state copy occurs only in
an equality of demoted cut records; the original full pipeline receives the
original larger/less input. The ψ3 fixture proves raw satisfiability only. -/

namespace PPLLAuthCheckComponentVerdict

open PPLL PPLLRepair PPLLBirthPatch PPLLBirthPatchM2 PPLLPostElectionGuard
open PPLLFableDesignR1 PPLLAstraDesign2 PPLLAstraDesign3 PPLLAuthF
open PPLLAuthF.AuthState PPLLAuthCheckComponent PPLLAuthCheckComponentFrame
open PPLLAuthCheckComponentStep

set_option autoImplicit false
variable {ψ : Nat}

structure VerdictBoundary (l r : AuthState ψ) (k bl br : Nat) : Prop where
  lk : l.core.label.val = k
  rk : r.core.label.val = k + 1
  interior : k + 2 < ψ
  lp : l.core.path = .some k bl
  rp : r.core.path = .some (k + 1) br
  ls : l.core.state = .depart
  rs : r.core.state = .larger ∨ r.core.state = .less
  lt : l.core.path2 = none
  rt : r.core.path2 = none
  ll : l.core.leader = false
  rl : r.core.leader = false
  lr : l.core.reset_cmd = false
  rr : r.core.reset_cmd = false
  pm : r.path_mark = l.path_mark
  cm : l.ctrl_mark = l.path_mark

private theorem VerdictBoundary.asEqual {l r : AuthState ψ} {k bl br : Nat}
    (h : VerdictBoundary l r k bl br) :
    PPLLAuthCheckComponentEqual.EqualBoundary l (r.setState .equal) k bl br := by
  have hi : k + 1 < ψ - 1 := by have := h.interior; omega
  constructor <;> simp [AuthState.setState, h.lk, h.rk, hi, h.lp, h.rp,
    h.ls, h.lt, h.rt, h.ll, h.rl, h.lr, h.rr, h.pm, h.cm]

-- This is equality AFTER validation, not a replacement of the original input.
private theorem demote_equalized (r : AuthState ψ) (ht : r.core.path2 = none) :
    demote (r.setState .equal) = demote r := by
  simp [demote, AuthState.st, AuthState.setState, ht]

theorem move_verdict (hp : ψ > 0) (l r : AuthState ψ)
    (k bl br : Nat) (h : VerdictBoundary l r k bl br) :
    moveSourceAuth hp cfg l r = (l, demote r) := by
  rcases h.rs with hs | hs <;>
    simp [moveSourceAuth, validateCheck, headBad, checkState, verdict,
      certPred, demote, isHead, aligned, sanitizeP2, p2Valid, step1Auth,
      moveTokensAuth, leaderWallAuth, applyControlAuth, AuthState.st,
      h.lp, h.rp, h.lk, h.rk, h.ls, hs, h.lt, h.rt, h.ll, h.rl]

private def afterClean (hp : ψ > 0) (l r : AuthState ψ) :
    AuthState ψ × AuthState ψ :=
  let q := lift2Life (releaseSource hp) l r
  let q := lift2 (eliminateSig hp) q.1 q.2
  let q := moveSourceAuth hp cfg q.1 q.2
  let q := (liftLife dropStale q.1, liftLife dropStale q.2)
  let q := preCheckResetAuth q.1 q.2
  (liftLife normalizeReady q.1, liftLife normalizeReady q.2)

private theorem afterClean_verdict (hp : ψ > 0) (l r : AuthState ψ)
    (k bl br : Nat) (h : VerdictBoundary l r k bl br) :
    afterClean hp l r = (l, demote r) := by
  have hm := move_verdict hp l r k bl br h
  rcases h.rs with hs | hs
  all_goals
    simp only [afterClean, lift2Life, releaseSource, hs, h.ls]
    simp [lift2, eliminateSig, hs, hm, liftLife, dropStale, aligned,
      preCheckResetAuth, normalizeReady, normalizeOrphan, normalizeCarrier,
      releaseCongest, demote, AuthState.st, h.ll, h.rl, h.lr, h.rr,
      h.lp, h.rp, h.lk, h.rk, h.ls, hs]

theorem check_demoted_verdict (hp : ψ > 0) (l r : AuthState ψ)
    (k bl br : Nat) (h : VerdictBoundary l r k bl br) :
    checkSourceAuth hp cfg l (demote r) = (l, r.lineage .CHECK_ready) := by
  have he := PPLLAuthCheckComponentEqual.check_demoted_equal
    hp l (r.setState .equal) k bl br h.asEqual
  rw [demote_equalized r h.rt] at he
  exact he

private theorem suffix_demoted_released (hp : ψ > 0) (κ : Nat)
    (l r : AuthState ψ) (k bl br : Nat) (h : VerdictBoundary l r k bl br) :
    Released l r (checkSuffix hp κ l (demote r)) := by
  have he := PPLLAuthCheckComponentEqual.suffix_demoted_released
    hp κ l (r.setState .equal) k bl br h.asEqual
  rw [demote_equalized r h.rt] at he
  exact he

private theorem gen_verdict (hp : ψ > 0) (κ : Nat) (l r : AuthState ψ)
    (k bl br : Nat) (h : VerdictBoundary l r k bl br) :
    genSigAuth hp κ l r = lift2 (waitSaturated hp κ) l r := by
  have hw := PPLLAuthGenDrain.W_fields hp κ l r
  rcases hw with ⟨a1,a2,a3,a4,a5,a6,a7,b1,b2,b3,b4,b5,b6,b7⟩
  unfold genSigAuth
  generalize lift2 (waitSaturated hp κ) l r = q at a1 a2 a3 a4 a5 a6 a7 b1 b2 b3 b4 b5 b6 b7 ⊢
  rcases q with ⟨a,b⟩
  simp only at a1 a2 a3 a4 a5 a6 a7 b1 b2 b3 b4 b5 b6 b7
  rcases h.rs with hs | hs <;>
    simp [AuthState.st, a1, a2, b1, h.lp, h.ls, hs]

private theorem wait_verdict (hp : ψ > 0) (κ : Nat) (l r : AuthState ψ)
    (k bl br : Nat) (h : VerdictBoundary l r k bl br) :
    VerdictBoundary (lift2 (waitSaturated hp κ) l r).1
      (lift2 (waitSaturated hp κ) l r).2 k bl br := by
  have hw := PPLLAuthGenDrain.W_fields hp κ l r
  have hd := PPLLAuthResetDrain.wait_dv hp κ l.core r.core
  simp only [PPLLAuthResetDrain.dv, Prod.mk.injEq] at hd
  rcases hw with ⟨a1,a2,a3,a4,a5,a6,a7,b1,b2,b3,b4,b5,b6,b7⟩
  rcases hd with ⟨⟨ar,_,_,_⟩,⟨brs,_,_,_⟩⟩
  constructor <;> simp_all [h.lk,h.rk,h.interior,h.lp,h.rp,h.ls,h.rs,
    h.lt,h.rt,h.ll,h.rl,h.lr,h.rr,h.pm,h.cm,lift2]

-- Exact ORIGINAL P′/GENSIG prefix; the intermediate cells are produced here.
theorem prefix_verdict (hp : ψ > 0) (κ : Nat) (l r : AuthState ψ)
    (k bl br : Nat) (h : VerdictBoundary l r k bl br) :
    ∃ a b : AuthState ψ,
      PPLLAuthCheckPostCleanHole.postCleanCut hp κ cfg l r =
        cleanSourceAuth hp cfg a b ∧
      VerdictBoundary a b k bl br ∧
      a.path_mark = l.path_mark ∧ b.path_mark = r.path_mark := by
  have hn : r.core.label.val = (l.core.label.val + 1) % ψ := by
    rw [h.rk, h.lk, Nat.mod_eq_of_lt]
    have := h.interior
    omega
  obtain ⟨x,y,he⟩ := PPLLAuthGenDrain.P0_frame hp l r h.ll h.rl hn
  let a := PPLLAuthGenDrain.withProbe l x
  let b := PPLLAuthGenDrain.withProbe r y
  have hab : VerdictBoundary a b k bl br := by
    constructor <;> simp [a,b,PPLLAuthGenDrain.withProbe,h.lk,h.rk,
      h.interior,h.lp,h.rp,h.ls,h.rs,h.lt,h.rt,h.ll,h.rl,h.lr,h.rr,h.pm,h.cm]
  let w := lift2 (waitSaturated hp κ) a b
  have hw : VerdictBoundary w.1 w.2 k bl br := wait_verdict hp κ a b k bl br hab
  have hg := gen_verdict hp κ a b k bl br hab
  refine ⟨w.1,w.2,?_,hw,rfl,rfl⟩
  change cleanSourceAuth hp cfg
    (genSigAuth hp κ (PPLLAuthGenDrain.P0 hp l r).1
      (PPLLAuthGenDrain.P0 hp l r).2).1
    (genSigAuth hp κ (PPLLAuthGenDrain.P0 hp l r).1
      (PPLLAuthGenDrain.P0 hp l r).2).2 = cleanSourceAuth hp cfg w.1 w.2
  rw [he]
  change cleanSourceAuth hp cfg (genSigAuth hp κ a b).1
    (genSigAuth hp κ a b).2 = cleanSourceAuth hp cfg w.1 w.2
  rw [hg]

private theorem clean_right_path (hp : ψ > 0) (l r : AuthState ψ)
    (k bl br : Nat) (h : VerdictBoundary l r k bl br) :
    (cleanSourceAuth hp cfg l r).2.core.path = r.core.path := by
  have hkT : k ≠ ψ - 1 := by have := h.interior; omega
  have hrT : k + 1 ≠ ψ - 1 := by have := h.interior; omega
  have hki : (k : Int) ≠ -1 := by omega
  have hri : (k : Int) + 1 ≠ -1 := by omega
  by_cases hk0 : k = 0
  · subst k
    cases ht : l.core.path4 with
    | none =>
        simp [cleanSourceAuth,cfg,genConnectAuth,cleanSigGenConnect,step3Auth,
          step4Auth,step5Auth,step6Auth,cleanApplyAuth,isCmd,
          h.lp,h.rp,h.pm,ht,hkT,hrT]
    | some t =>
        rcases t with ⟨v,bit⟩
        by_cases hv : v = -1 <;>
          simp [cleanSourceAuth,cfg,genConnectAuth,cleanSigGenConnect,step3Auth,
            step4Auth,step5Auth,step6Auth,cleanApplyAuth,isCmd,
            h.lp,h.rp,h.pm,ht,hkT,hrT,hv]
  · simp [cleanSourceAuth,cfg,genConnectAuth,cleanSigGenConnect,step3Auth,
      step4Auth,step5Auth,step6Auth,cleanApplyAuth,isCmd,
      h.lp,h.rp,h.pm,hk0,hkT,hrT,hki,hri]

theorem clean_verdict_or_left_hole (hp : ψ > 0) (l r : AuthState ψ)
    (k bl br : Nat) (h : VerdictBoundary l r k bl br) :
    let q := cleanSourceAuth hp cfg l r
    q.1.core.path = .bot ∨
      (VerdictBoundary q.1 q.2 k bl br ∧
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

private theorem beforeSuppress_cut (hp : ψ > 0) (κ : Nat) (l r : AuthState ψ) :
    PPLLAuthResetDrain.beforeSuppressAuth hp κ cfg l r =
      let q := PPLLAuthCheckPostCleanHole.postCleanCut hp κ cfg l r
      let a := afterClean hp q.1 q.2
      checkSuffix hp κ a.1 a.2 := by
  rfl

theorem pipeline_verdict_or_hole (hp : ψ > 0) (κ : Nat) (l r : AuthState ψ)
    (k bl br : Nat) (h : VerdictBoundary l r k bl br) :
    let q := PPLLAuthF.pipeline hp κ cfg l r
    PairHole q ∨ Released l r q := by
  dsimp only
  obtain ⟨a,b,hcut,hab,ma,mb⟩ := prefix_verdict hp κ l r k bl br h
  let d := cleanSourceAuth hp cfg a b
  rcases clean_verdict_or_left_hole hp a b k bl br hab with hh | ⟨hc,m1,m2⟩
  · left
    change PPLLAuthFPairHole.PairHole (PPLLAuthF.pipeline hp κ cfg l r)
    rw [PPLLAuthCheckPostCleanHole.pipeline_factor_postClean, hcut]
    exact PPLLAuthCheckPostCleanHole.afterCleanToFinal_pairHole
      hp κ cfg l r d.1 d.2 (Or.inl hh)
  · right
    have ha := afterClean_verdict hp d.1 d.2 k bl br hc
    have hbs : PPLLAuthResetDrain.beforeSuppressAuth hp κ cfg l r =
        checkSuffix hp κ d.1 (demote d.2) := by
      rw [beforeSuppress_cut, hcut]
      change (let z := afterClean hp d.1 d.2; checkSuffix hp κ z.1 z.2) =
        checkSuffix hp κ d.1 (demote d.2)
      rw [ha]
    have hs := suffix_demoted_released hp κ d.1 d.2 k bl br hc
    obtain ⟨hf1,hf2⟩ := PPLLAuthGenDrain.pipeline_FV hp κ cfg l r
      h.ll h.rl h.lr h.rr
    rw [hbs] at hf1 hf2
    generalize ho : PPLLAuthF.pipeline hp κ cfg l r = out at hf1 hf2 ⊢
    generalize hz : checkSuffix hp κ d.1 (demote d.2) = rest at hf1 hf2 hs
    rcases hs with ⟨s1,s2,s3,s4,s5,s6,s7,s8,s9,s10⟩
    refine ⟨(PPLLAuthGenDrain.FV_state hf1).trans s1,
      (PPLLAuthGenDrain.FV_state hf2).trans s2,
      (PPLLAuthGenDrain.FV_path hf1).trans (s3.trans (hc.lp.trans h.lp.symm)),
      (PPLLAuthGenDrain.FV_path hf2).trans (s4.trans (hc.rp.trans h.rp.symm)),
      (PPLLAuthGenDrain.FV_path2 hf1).trans s5,
      (PPLLAuthGenDrain.FV_path2 hf2).trans s6, ?_, ?_,
      (PPLLAuthGenDrain.FV_pm hf1).trans (s9.trans (m1.trans ma)),
      (PPLLAuthGenDrain.FV_pm hf2).trans (s10.trans (m2.trans mb))⟩
    · rw [PPLLAuthGenDrain.FV_ctrl hf1,PPLLAuthGenDrain.FV_pm hf1]
      exact s7
    · rw [PPLLAuthGenDrain.FV_ctrl hf2,PPLLAuthGenDrain.FV_pm hf2]
      exact s8

theorem verdict_step (hp : ψ > 0) (κ : Nat) (l r : AuthState ψ)
    (k bl br : Nat) (h : VerdictBoundary l r k bl br) :
    let q := PPLLAuthF.pipeline hp κ PPLLAuthCheckComponent.cfg l r
    PPLLAuthCheckComponentStep.Target q ∨
      PPLLAuthCheckComponentStep.Continuing l r q := by
  let q := PPLLAuthF.pipeline hp κ cfg l r
  by_cases hl : q.1.core.leader = true
  · exact Or.inl (Or.inl hl)
  by_cases hr : q.2.core.leader = true
  · exact Or.inl (Or.inr (Or.inl hr))
  have hlf : q.1.core.leader = false := by cases he : q.1.core.leader <;> simp_all
  have hrf : q.2.core.leader = false := by cases he : q.2.core.leader <;> simp_all
  rcases pipeline_verdict_or_hole hp κ l r k bl br h with hh | hc
  · exact Or.inl (Or.inr (Or.inr hh))
  · have hn : r.core.label = ⟨(l.core.label.val + 1) % ψ,Nat.mod_lt _ hp⟩ := by
      apply Fin.ext
      change r.core.label.val = (l.core.label.val + 1) % ψ
      rw [h.rk,h.lk,Nat.mod_eq_of_lt]
      have := h.interior
      omega
    have hs := PPLLAuthGenDrain.row_std hp κ cfg l r h.ll h.rl h.lr h.rr hn hrf
    exact Or.inr ⟨hc,hs.1,hs.2.1,hs.2.2.1,hs.2.2.2,hlf,hrf⟩

private def witnessCell (i : Fin 3) (s : MainState) (cm : ProvColor) : AuthState 3 :=
  { core :=
      { leader := false, probe := false, phase := false, bit := false,
        wait := true, state := s, path := .some i.val 0,
        reset := false, carry := false, count := 0, label := i,
        h_field := false, path2 := none, path3 := none, path4 := none,
        path5 := none, p := false, p_carry := false, reset_cmd := false,
        echo := false, signal_B := 0, bullet := 0, shield := false,
        write_state := .none, write := .none, last := false,
        last_set := false, last_unset := false, b_carry := false,
        gen_ws := false, ws_echo := false, signal_ws := false },
    path_mark := 0, ctrl_mark := cm, path2_scope := .session, path2_mark := 2,
    path4_mark := 0, path5_mark := 0 }

-- Instantiates either verdict at width three, with right control 1 and path mark 0.
theorem entrance_psi3 (s : MainState) (hs : s = .larger ∨ s = .less) :
    ∃ l r : AuthState 3, VerdictBoundary l r 0 0 0 ∧
      r.core.state = s ∧ r.ctrl_mark = 1 ∧ r.path_mark = 0 := by
  refine ⟨witnessCell 0 .depart 0,witnessCell 1 s 1,?_,rfl,rfl,rfl⟩
  exact ⟨rfl,rfl,by omega,rfl,rfl,rfl,hs,
    rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

#print axioms verdict_step
#print axioms entrance_psi3
end PPLLAuthCheckComponentVerdict
