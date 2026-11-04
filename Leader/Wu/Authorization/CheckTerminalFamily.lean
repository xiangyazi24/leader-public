import Leader.Wu.Authorization.CheckTerminalReady
import Leader.Wu.Authorization.PostCleanHole

namespace PPLLAuthCheckTerminalFamily

open PPLL PPLLRepair PPLLBirthPatch PPLLBirthPatchM2 PPLLPostElectionGuard
open PPLLFableDesignR1 PPLLAstraDesign2 PPLLAstraDesign3 PPLLAuthF
open PPLLAuthF.AuthState PPLLAuthCheckComponent PPLLAuthCheckComponentFrame
open PPLLAuthGenDrain PPLLAuthResetDrain PPLLAuthCheckComponentStep
open PPLLAuthCheckTerminalConsume

/-! Initial verification budget matches the accepted TerminalReady and
TerminalGoodEq family: 800000 heartbeats / recursion depth 4096.
This is a new unverified module; these are its initial limits, not a retry
increase. The original entrance and trichotomy remain unchanged. -/

set_option autoImplicit false
variable {ψ : Nat}

def FamilyState (s : MainState) : Prop :=
  s = .equal ∨ s = .larger ∨ s = .less ∨ s = .lock ∨ s = .compare1

structure Boundary (l r : AuthState ψ) (bl br : Nat) : Prop where
  width : 2 ≤ ψ
  lk : l.core.label.val = ψ - 2
  rk : r.core.label.val = ψ - 1
  lp : l.core.path = .some (ψ - 2) bl
  rp : r.core.path = .some (ψ - 1) br
  ls : l.core.state = .depart
  rs : FamilyState r.core.state
  lt : l.core.path2 = none
  rt : r.core.path2 = none
  ll : l.core.leader = false
  rl : r.core.leader = false
  lr : l.core.reset_cmd = false
  rr : r.core.reset_cmd = false
  pm : r.path_mark = l.path_mark
  cm : l.ctrl_mark = l.path_mark

/- Raw fixture: ψ=2, labels/paths 0/1 with payloads 0, depart/lock,
empty tokens, followers/reset-free, common mark and left control 0.
Right control is arbitrary. Other fields may be false/zero/absent;
left p_carry=right p=true instead exercises E. No reachability claim. -/

private theorem wait_row (hp : ψ > 0) (κ : Nat) (l r : AuthState ψ)
    (bl br : Nat) (h : Boundary l r bl br) :
    Boundary (lift2 (waitSaturated hp κ) l r).1
      (lift2 (waitSaturated hp κ) l r).2 bl br := by
  have hw := W_fields hp κ l r
  have hd : av (lift2 (waitSaturated hp κ) l r).1 = av l ∧
      av (lift2 (waitSaturated hp κ) l r).2 = av r :=
    wait_dv hp κ l.core r.core
  generalize lift2 (waitSaturated hp κ) l r = q at hw hd ⊢
  rcases hw with ⟨sL,pL,tL,kL,fL,cL,mL,sR,pR,tR,kR,fR,cR,mR⟩
  simp only [av,dv,Prod.mk.injEq] at hd
  rcases hd with ⟨⟨rL,_,_,_⟩,⟨rR,_,_,_⟩⟩
  refine ⟨h.width,(congrArg Fin.val kL).trans h.lk,
    (congrArg Fin.val kR).trans h.rk,pL.trans h.lp,pR.trans h.rp,
    sL.trans h.ls,?_,tL.trans h.lt,tR.trans h.rt,
    fL.trans h.ll,fR.trans h.rl,rL.trans h.lr,rR.trans h.rr,
    mR.trans (h.pm.trans mL.symm),cL.trans (h.cm.trans mL.symm)⟩
  rw [sR]
  exact h.rs

set_option maxHeartbeats 800000 in
set_option maxRecDepth 4096 in
private theorem gen_eq_wait (hp : ψ > 0) (κ : Nat) (l r : AuthState ψ)
    (bl br : Nat) (h : Boundary l r bl br) :
    genSigAuth hp κ l r = lift2 (waitSaturated hp κ) l r := by
  have hw := W_fields hp κ l r
  unfold genSigAuth
  generalize lift2 (waitSaturated hp κ) l r = q at hw ⊢
  rcases q with ⟨a,b⟩
  dsimp only at hw ⊢
  rcases hw with ⟨sL,pL,_,_,_,_,_,sR,_,_,_,_,_,_⟩
  rcases h.rs with hs | hs | hs | hs | hs <;>
    simp [AuthState.st,sL,pL,sR,h.lp,h.ls,hs]

private def preClean (hp : ψ > 0) (κ : Nat) (l r : AuthState ψ) :=
  let p := P0 hp l r
  genSigAuth hp κ p.1 p.2

private theorem preClean_row (hp : ψ > 0) (κ : Nat) (l r : AuthState ψ)
    (bl br : Nat) (h : Boundary l r bl br) :
    let q := preClean hp κ l r
    Boundary q.1 q.2 bl br ∧
      q.1.path_mark = l.path_mark ∧ q.2.path_mark = r.path_mark := by
  have hk : ψ - 2 + 1 = ψ - 1 := by have := h.width; omega
  have hn : r.core.label.val = (l.core.label.val + 1) % ψ := by
    rw [h.lk,h.rk,hk,Nat.mod_eq_of_lt (by omega)]
  obtain ⟨x,y,he⟩ := P0_frame hp l r h.ll h.rl hn
  let a : AuthState ψ := {l with core := {l.core with probe := x}}
  let b : AuthState ψ := {r with core := {r.core with probe := y}}
  have hab : Boundary a b bl br :=
    ⟨h.width,h.lk,h.rk,h.lp,h.rp,h.ls,h.rs,h.lt,h.rt,
      h.ll,h.rl,h.lr,h.rr,h.pm,h.cm⟩
  unfold preClean
  rw [he]
  change Boundary (genSigAuth hp κ a b).1 (genSigAuth hp κ a b).2 bl br ∧
    (genSigAuth hp κ a b).1.path_mark = l.path_mark ∧
    (genSigAuth hp κ a b).2.path_mark = r.path_mark
  rw [gen_eq_wait hp κ a b bl br hab]
  exact ⟨wait_row hp κ a b bl br hab,rfl,rfl⟩

private theorem clean_row (hp : ψ > 0) (l r : AuthState ψ)
    (bl br : Nat) (h : Boundary l r bl br) :
    let q := T1 hp cfg (l,r)
    PairHole q ∨ (Boundary q.1 q.2 bl br ∧
      q.1.path_mark = l.path_mark ∧ q.2.path_mark = r.path_mark) := by
  have hv := T1_cv hp cfg (l,r)
  have ha := T1_pa hp cfg (l,r)
  dsimp only
  generalize T1 hp cfg (l,r) = q at hv ha ⊢
  rcases hv with ⟨vL,vR,pL,pR⟩
  rcases pL with pL | pL
  · rcases pR with pR | pR
    · right
      simp only [cv,Prod.mk.injEq] at vL vR
      simp only [PA,av,dv,Prod.mk.injEq] at ha
      rcases vL with ⟨sL,_,cL,tL,mL⟩
      rcases vR with ⟨sR,_,_,tR,mR⟩
      rcases ha with ⟨⟨rL,_,kL,fL⟩,⟨rR,_,kR,fR⟩⟩
      refine ⟨?_,mL,mR⟩
      refine ⟨h.width,(congrArg Fin.val kL).trans h.lk,
        (congrArg Fin.val kR).trans h.rk,pL.trans h.lp,pR.trans h.rp,
        sL.trans h.ls,?_,tL.trans h.lt,tR.trans h.rt,
        fL.trans h.ll,fR.trans h.rl,rL.trans h.lr,rR.trans h.rr,
        mR.trans (h.pm.trans mL.symm),cL.trans (h.cm.trans mL.symm)⟩
      rw [sR]
      exact h.rs
    · exact Or.inl (Or.inr pR)
  · exact Or.inl (Or.inl pL)

/-- Actual P0/GENSIG/CLEAN cut. -/
def cleanCut (hp : ψ > 0) (κ : Nat) (l r : AuthState ψ) :=
  let g := preClean hp κ l r
  T1 hp cfg g

/-- Both deletion alternatives, without CLEAN-slot assumptions. -/
theorem cleanCut_hole_or_boundary (hp : ψ > 0) (κ : Nat)
    (l r : AuthState ψ) (bl br : Nat) (h : Boundary l r bl br) :
    let q := cleanCut hp κ l r
    PairHole q ∨ (Boundary q.1 q.2 bl br ∧
      q.1.path_mark = l.path_mark ∧ q.2.path_mark = r.path_mark) := by
  have hg := preClean_row hp κ l r bl br h
  unfold cleanCut
  generalize preClean hp κ l r = g at hg ⊢
  dsimp only at hg ⊢
  rcases hg with ⟨hg,mL,mR⟩
  rcases clean_row hp g.1 g.2 bl br hg with hh | ⟨hc,cL,cR⟩
  · exact Or.inl hh
  · exact Or.inr ⟨hc,cL.trans mL,cR.trans mR⟩

private def afterClean (hp : ψ > 0) (l r : AuthState ψ) :=
  let q := lift2Life (releaseSource hp) l r
  let q := lift2 (eliminateSig hp) q.1 q.2
  let q := moveSourceAuth hp cfg q.1 q.2
  let q := (liftLife dropStale q.1,liftLife dropStale q.2)
  let q := preCheckResetAuth q.1 q.2
  (liftLife normalizeReady q.1,liftLife normalizeReady q.2)

private def movedRight (r : AuthState ψ) : AuthState ψ :=
  if r.core.state = .equal ∨ r.core.state = .larger ∨ r.core.state = .less
  then demote r else r

private def checkedRight (r : AuthState ψ) : AuthState ψ :=
  if r.core.state = .equal ∨ r.core.state = .larger ∨ r.core.state = .less
  then (demote r).lineage .CHECK_ready else r

private theorem move_row (hp : ψ > 0) (l r : AuthState ψ)
    (bl br : Nat) (h : Boundary l r bl br) :
    moveSourceAuth hp cfg l r = (l,movedRight r) := by
  have hr0 : ψ - 1 ≠ 0 := by have := h.width; omega
  rcases h.rs with hs | hs | hs | hs | hs <;>
    simp [movedRight,moveSourceAuth,validateCheck,headBad,checkState,verdict,
      certPred,demote,isHead,aligned,sanitizeP2,p2Valid,step1Auth,
      moveTokensAuth,leaderWallAuth,applyControlAuth,AuthState.st,
      h.lp,h.rp,h.lk,h.rk,h.ls,hs,h.lt,h.rt,h.ll,h.rl,hr0]

private theorem afterClean_row (hp : ψ > 0) (l r : AuthState ψ)
    (bl br : Nat) (h : Boundary l r bl br) :
    afterClean hp l r = (l,movedRight r) := by
  have hrel : lift2Life (releaseSource hp) l r = (l,r) := by
    rcases h.rs with hs | hs | hs | hs | hs <;>
      simp [lift2Life,releaseSource,hs]
  have hel : lift2 (eliminateSig hp) l r = (l,r) := by
    rcases h.rs with hs | hs | hs | hs | hs <;>
      simp [lift2,eliminateSig,hs]
  unfold afterClean
  rw [hrel]
  dsimp only
  rw [hel]
  dsimp only
  rw [move_row hp l r bl br h]
  dsimp only
  rcases h.rs with hs | hs | hs | hs | hs <;>
    simp [movedRight,demote,liftLife,dropStale,aligned,preCheckResetAuth,
      normalizeReady,normalizeOrphan,normalizeCarrier,releaseCongest,
      h.ll,h.rl,h.lr,h.rr,h.lp,h.rp,h.lk,h.rk,h.ls,hs,h.lt,h.rt]

private theorem check_row (hp : ψ > 0) (l r : AuthState ψ)
    (bl br : Nat) (h : Boundary l r bl br) :
    checkSourceAuth hp cfg l (movedRight r) = (l,checkedRight r) := by
  have hr0 : ψ - 1 ≠ 0 := by have := h.width; omega
  have hL : checkSigCheckL hp l.core = l.core := by
    cases hk : ψ - 2 <;> simp [checkSigCheckL,h.lp,hk,h.ls]
  rcases h.rs with hs | hs | hs | hs | hs <;>
    simp [movedRight,checkedRight,checkSourceAuth,cfg,validateCheck,
      headBad,checkState,verdict,certPred,demote,isHead,aligned,readyAuth,
      waveState,checkSigSetReadyGuarded,controlPending,checkSigSetReady,
      hL,issue,AuthState.st,AuthState.withCore,AuthState.lineage,
      h.lp,h.rp,h.lk,h.rk,h.ls,hs,h.lt,h.rt,h.ll,h.rl,hr0]

private def PendingFields (l r : AuthState ψ) (q : AuthState ψ × AuthState ψ) :=
  q.1.core.state = .depart ∧ q.2.core.state = .eliminate_signal ∧
  q.1.core.path = l.core.path ∧ q.2.core.path = r.core.path ∧
  q.1.core.path2 = none ∧ q.2.core.path2 = none ∧
  q.1.ctrl_mark = q.1.path_mark ∧
  q.1.path_mark = l.path_mark ∧ q.2.path_mark = r.path_mark

private def postClean (hp : ψ > 0) (κ : Nat) (l r : AuthState ψ) :=
  let a := afterClean hp l r
  let q := checkSourceAuth hp cfg a.1 a.2
  let d := disappearAuth hp q.1 q.2
  let z := repairAuth d.1 d.2
  compareLifecycleAuth κ z.1 z.2

/-- All five states and all terminal carry valuations. -/
private theorem postClean_fields (hp : ψ > 0) (κ : Nat) (l r : AuthState ψ)
    (bl br : Nat) (h : Boundary l r bl br) :
    Released l r (postClean hp κ l r) ∨
      PendingFields l r (postClean hp κ l r) := by
  have hk : ψ - 2 + 1 = ψ - 1 := by have := h.width; omega
  have hn : ψ - 2 ≠ ψ - 1 := by have := h.width; omega
  have hr0 : ψ - 1 ≠ 0 := by have := h.width; omega
  have hrt : r.core.label = (⟨ψ - 1,by omega⟩ : Fin ψ) := Fin.ext h.rk
  unfold postClean
  rw [afterClean_row hp l r bl br h]
  dsimp only
  rw [check_row hp l r bl br h]
  dsimp only
  rcases h.rs with hs | hs | hs | hs | hs <;>
    cases hc : l.core.p_carry <;> cases hb : r.core.p <;>
    simp [checkedRight,demote,Released,PendingFields,
      disappearAuth,disappearStartL,disappearCarry,lift2,
      repairAuth,liftLife,normalizeOrphan,normalizeCarrier,releaseCongest,
      lift2Life,releaseReadySuffix,ackTailAuth,ackTail,lockedState,
      compareLifecycleAuth,maintainAuth,completeWaveAuth,waveAuth,
      PPLLFableDesignR1.dropStray,landBackwardAuth,landForwardAuth,
      AuthState.st,AuthState.setState,AuthState.withCore,AuthState.lineage,
      h.lp,h.rp,h.lk,h.rk,h.ls,hs,h.lt,h.rt,h.ll,h.rl,h.cm,h.pm,
      hc,hb,hrt,hk,hn,hr0]

private theorem beforeSuppress_factor (hp : ψ > 0) (κ : Nat)
    (l r : AuthState ψ) :
    beforeSuppressAuth hp κ cfg l r =
      postClean hp κ (cleanCut hp κ l r).1 (cleanCut hp κ l r).2 := rfl

private theorem pipeline_cut (hp : ψ > 0) (κ : Nat) (l r : AuthState ψ) :
    PPLLAuthF.pipeline hp κ cfg l r =
      let c := cleanCut hp κ l r
      PPLLAuthCheckPostCleanHole.afterCleanToFinal hp κ cfg l r c.1 c.2 := rfl

private theorem pipeline_fields (hp : ψ > 0) (κ : Nat)
    (l r : AuthState ψ) (bl br : Nat) (h : Boundary l r bl br) :
    let q := PPLLAuthF.pipeline hp κ cfg l r
    PairHole q ∨ Released l r q ∨ PendingFields l r q := by
  dsimp only
  rcases cleanCut_hole_or_boundary hp κ l r bl br h with hh | ⟨hc,mL,mR⟩
  · left
    rw [pipeline_cut hp κ l r]
    exact PPLLAuthCheckPostCleanHole.afterCleanToFinal_pairHole
      hp κ cfg l r (cleanCut hp κ l r).1 (cleanCut hp κ l r).2 hh
  · have hs := postClean_fields hp κ
      (cleanCut hp κ l r).1 (cleanCut hp κ l r).2 bl br hc
    have hf := pipeline_FV hp κ cfg l r h.ll h.rl h.lr h.rr
    rw [beforeSuppress_factor hp κ l r] at hf
    generalize cleanCut hp κ l r = c at hc mL mR hs hf
    generalize postClean hp κ c.1 c.2 = z at hs hf
    generalize PPLLAuthF.pipeline hp κ cfg l r = out at hf ⊢
    rcases hf with ⟨hL,hR⟩
    have sl := FV_state hL
    have sr := FV_state hR
    have pl := FV_path hL
    have pr := FV_path hR
    have tl := FV_path2 hL
    have tr := FV_path2 hR
    have cl := FV_ctrl hL
    have cr := FV_ctrl hR
    have ml := FV_pm hL
    have mr := FV_pm hR
    have cpL : c.1.core.path = l.core.path := hc.lp.trans h.lp.symm
    have cpR : c.2.core.path = r.core.path := hc.rp.trans h.rp.symm
    right
    simpa only [Released,PendingFields,sl,sr,pl,pr,tl,tr,cl,cr,ml,mr,
      cpL,cpR,mL,mR] using hs

/-- Exact accepted output interfaces for the five new terminal cases. -/
theorem terminal_family_step (hp : ψ > 0) (κ : Nat) (l r : AuthState ψ)
    (bl br : Nat) (h : Boundary l r bl br) :
    let q := PPLLAuthF.pipeline hp κ cfg l r
    Target q ∨ Continuing l r q ∨ TerminalPending q.1 q.2 bl br := by
  let q := PPLLAuthF.pipeline hp κ cfg l r
  by_cases hl : q.1.core.leader = true
  · exact Or.inl (Or.inl hl)
  by_cases hr : q.2.core.leader = true
  · exact Or.inl (Or.inr (Or.inl hr))
  have hlf : q.1.core.leader = false := by
    cases he : q.1.core.leader
    · rfl
    · exact False.elim (hl he)
  have hrf : q.2.core.leader = false := by
    cases he : q.2.core.leader
    · rfl
    · exact False.elim (hr he)
  have hk : ψ - 2 + 1 = ψ - 1 := by have := h.width; omega
  have hn : r.core.label = ⟨(l.core.label.val + 1) % ψ,Nat.mod_lt _ hp⟩ := by
    apply Fin.ext
    change r.core.label.val = (l.core.label.val + 1) % ψ
    rw [h.lk,h.rk,hk,Nat.mod_eq_of_lt (by omega)]
  have hf := row_std hp κ cfg l r h.ll h.rl h.lr h.rr hn hrf
  rcases pipeline_fields hp κ l r bl br h with hh | hd | he
  · exact Or.inl (Or.inr (Or.inr hh))
  · exact Or.inr (Or.inl ⟨hd,hf.1,hf.2.1,hf.2.2.1,hf.2.2.2,hlf,hrf⟩)
  · rcases he with ⟨ls,rs,lp,rp,lt,rt,cm,lm,rm⟩
    right; right
    refine ⟨h.width,?_,?_,lp.trans h.lp,rp.trans h.rp,ls,rs,lt,rt,
      hlf,hrf,hf.2.2.1,hf.2.2.2,?_,cm⟩
    · exact (congrArg Fin.val hf.1).trans h.lk
    · exact (congrArg Fin.val hf.2.1).trans h.rk
    · exact rm.trans (h.pm.trans lm.symm)

/-- Reuse accepted TerminalReady for the sixth state. -/
theorem terminal_step (hp : ψ > 0) (κ : Nat) (l r : AuthState ψ)
    (bl br : Nat)
    (h : PPLLAuthCheckTerminalReady.TerminalReady l r bl br ∨ Boundary l r bl br) :
    let q := PPLLAuthF.pipeline hp κ cfg l r
    Target q ∨ Continuing l r q ∨ TerminalPending q.1 q.2 bl br := by
  rcases h with h | h
  · exact PPLLAuthCheckTerminalReady.terminal_ready_step hp κ l r bl br h
  · exact terminal_family_step hp κ l r bl br h

#print axioms PPLLAuthCheckTerminalFamily.cleanCut_hole_or_boundary
#print axioms PPLLAuthCheckTerminalFamily.terminal_family_step
#print axioms PPLLAuthCheckTerminalFamily.terminal_step

end PPLLAuthCheckTerminalFamily
