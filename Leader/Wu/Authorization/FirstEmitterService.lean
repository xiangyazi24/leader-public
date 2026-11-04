import Leader.Wu.Authorization.A6A5RetainedCut
import Leader.Wu.Authorization.PostCleanHole
import Leader.Wu.Authorization.TokenSidecarFrame


/-! Original A6/Ready first emitter service, with arbitrary CLEAN and carry.
The input pair is the actual X0A6/X1Ready constructor entrance. The retained
branch records left toss and carrier fields; it deliberately leaves right
state and final physical bit/p/p_carry unconstrained. This is only the first
service, not the later seam or a population-word theorem.

The CLEAN-hole branch uses pipeline_pairHole_of_postClean as compiled internal
support. That helper has no separately accepted standalone headline; this
consumer requires its own compiler, headline, and dependency-closure checks. -/

namespace PPLLAuthFirstEmitterService
open PPLL PPLLRepair PPLLBirthPatch PPLLBirthPatchM2 PPLLPostElectionGuard
open PPLLFableDesignR1 PPLLAstraDesign2 PPLLAstraDesign3 PPLLAuthF
open PPLLAuthA6A5RetainedCut
open PPLLAuthGenDrain (P0 P0_frame W_fields T1 T1_cv T1_pa cv PA FV pipeline_FV row_std)
open PPLLAuthResetDrain (av dv wait_dv beforeSuppressAuth fst_ite snd_ite)
open PPLLAuthTokenSidecarFrame (TokenSidecar pipeline_tokenSidecar)
open PPLLAuthFPairHole (PairHole)
set_option autoImplicit false
variable {n : Nat}


private abbrev S (u : AuthState n) : P2Scope × ProvColor := TokenSidecar u
/-- Left emitter state, main path, token and provenance fields. -/
def LV (u : AuthState n) :
    MainState × PathInfo × Option Path2Info × ProvColor × ProvColor × P2Scope × ProvColor :=
  (u.core.state,u.core.path,u.core.path2,u.ctrl_mark,u.path_mark,u.path2_scope,u.path2_mark)
/-- Right carrier path, token payload and lineage mark only. -/
def RV (u : AuthState n) : PathInfo × Option Path2Info × ProvColor :=
  (u.core.path,u.core.path2,u.path_mark)
/-- First-service toss/carrier continuation, without lottery-field frames. -/
def Post (g : ProvColor) (i j : Nat) (q : AuthState n × AuthState n) : Prop :=
  LV q.1 = (.toss,.some 0 i,none,g,g,.line,g) ∧ RV q.2 = (.some 1 j,none,g)
def Target (q : AuthState n × AuthState n) : Prop :=
  q.1.core.leader = true ∨ q.2.core.leader = true ∨ PairHole q


def cut (hp : n > 0) (k : Nat) (a b : AuthState n) : AuthState n × AuthState n :=
  let p := P0 hp a b
  let q := genSigAuth hp k p.1 p.2
  cleanSourceAuth hp cfg q.1 q.2
private def tail (k : Nat) (a b : AuthState n) : AuthState n × AuthState n :=
  let q := repairAuth a b
  compareLifecycleAuth k q.1 q.2
private def B (hp : n > 0) (k : Nat) (a b : AuthState n) : AuthState n × AuthState n :=
  let q := lift2Life (releaseSource hp) a b
  let q := lift2 (eliminateSig hp) q.1 q.2
  let q := preDisappear hp cfg q.1 q.2
  let q := disappearAuth hp q.1 q.2
  tail k q.1 q.2


private theorem s_ite (p : Prop) [Decidable p] (a b : AuthState n) :
    S (if p then a else b) = if p then S a else S b := by split <;> rfl
private theorem s_core (a : AuthState n) (b : AgentState n) :
    S {a with core := b} = S a := rfl
private theorem s_gen (a : AuthState n) : S (genConnectAuth a) = S a := by
  unfold genConnectAuth
  (repeat' (first | rfl | (dsimp only) | split))


private def sidecarApply4 (pl : Nat) (u : AuthState n) : AuthState n :=
  match u.core.path4 with
  | some (lbl,_) =>
    if lbl = (-1 : Int) then
      if u.path4_mark == u.path_mark then
        let c := if pl = 0 then {u.core with path4 := none} else u.core
        {u with core := {c with path := .bot}}
      else {u with core := {u.core with path4 := none}}
    else u
  | none => u
private def sidecarApply5 (pl : Nat) (u : AuthState n) : AuthState n :=
  match u.core.path5 with
  | some (lbl,_) =>
    if lbl = (-1 : Int) then
      if u.path5_mark == u.path_mark then
        let c := if pl = n - 1 then {u.core with path5 := none} else u.core
        {u with core := {c with path := .bot}}
      else {u with core := {u.core with path5 := none}}
    else u
  | none => u
private theorem sidecarApply_eq (u : AuthState n) :
    cleanApplyAuth u =
      match u.core.path with
      | .bot => u
      | .some pl _ => sidecarApply5 pl (sidecarApply4 pl u) := by rfl
private theorem sidecarApply4_keeps (pl : Nat) (u : AuthState n) :
    TokenSidecar (sidecarApply4 pl u) = TokenSidecar u := by
  unfold sidecarApply4
  repeat (first | rfl | split)
private theorem sidecarApply5_keeps (pl : Nat) (u : AuthState n) :
    TokenSidecar (sidecarApply5 pl u) = TokenSidecar u := by
  unfold sidecarApply5
  repeat (first | rfl | split)
private theorem s_apply (u : AuthState n) : S (cleanApplyAuth u) = S u := by
  rw [sidecarApply_eq]
  cases h : u.core.path with
  | bot => rfl
  | some pl bit =>
    exact (sidecarApply5_keeps pl (sidecarApply4 pl u)).trans
      (sidecarApply4_keeps pl u)
private theorem s3 (c : PPLLAuthF.Cfg) (a b : AuthState n) :
    S (step3Auth c.cleanNbr c.markClean a b).1 = S a ∧
    S (step3Auth c.cleanNbr c.markClean a b).2 = S b := by
  unfold step3Auth
  (repeat' (first | exact ⟨rfl,rfl⟩ | (dsimp only) | split))
private theorem s4 (c : PPLLAuthF.Cfg) (a b : AuthState n) :
    S (step4Auth c.cleanNbr c.markClean a b).1 = S a ∧
    S (step4Auth c.cleanNbr c.markClean a b).2 = S b := by
  unfold step4Auth
  (repeat' (first | exact ⟨rfl,rfl⟩ | (dsimp only) | split))
private theorem s5 (hp : n > 0) (a b : AuthState n) :
    S (step5Auth hp a b).1 = S a ∧ S (step5Auth hp a b).2 = S b := by
  unfold step5Auth
  (repeat' (first | exact ⟨rfl,rfl⟩ | (dsimp only) | split))
private theorem s6 (hp : n > 0) (a b : AuthState n) :
    S (step6Auth hp a b).1 = S a ∧ S (step6Auth hp a b).2 = S b := by
  unfold step6Auth
  (repeat' (first | exact ⟨rfl,rfl⟩ | (dsimp only) | split))
private theorem clean_S (hp : n > 0) (c : PPLLAuthF.Cfg) (a b : AuthState n) :
    S (cleanSourceAuth hp c a b).1 = S a ∧ S (cleanSourceAuth hp c a b).2 = S b := by
  simp only [cleanSourceAuth,fst_ite,snd_ite,s_ite,s_core,
    s_apply,s6,s5,s4,s3,s_gen,ite_self,and_self]


private theorem wait_V (hp : n > 0) (k : Nat) (a b : AuthState n) :
    V (lift2 (waitSaturated hp k) a b).1 = V a ∧
    V (lift2 (waitSaturated hp k) a b).2 = V b := by
  obtain ⟨a1,a2,a3,a4,a5,a6,a7,b1,b2,b3,b4,b5,b6,b7⟩ := W_fields hp k a b
  have hd := wait_dv hp k a.core b.core
  simp only [V,Prod.mk.injEq]
  exact ⟨⟨a1,a2,a3,a4,a5,congrArg Prod.fst hd.1,a7,a6,rfl,rfl⟩,
    ⟨b1,b2,b3,b4,b5,congrArg Prod.fst hd.2,b7,b6,rfl,rfl⟩⟩
private theorem gen_V (hp : n > 0) (k : Nat) (a b : AuthState n) (i : Nat)
    (hp0 : a.core.path = .some 0 i) (hs : a.core.state = .less)
    (hr : b.core.state = .CHECK_ready) :
    V (genSigAuth hp k a b).1 = V a ∧ V (genSigAuth hp k a b).2 = V b := by
  have hw := wait_V hp k a b
  unfold genSigAuth
  generalize lift2 (waitSaturated hp k) a b = q at hw ⊢
  rcases q with ⟨u,v⟩
  dsimp only at hw ⊢
  have up : u.core.path = .some 0 i := (congrArg (fun x => x.2.1) hw.1).trans hp0
  have us : u.core.state = .less := (congrArg Prod.fst hw.1).trans hs
  have vs : v.core.state = .CHECK_ready := (congrArg Prod.fst hw.2).trans hr
  simpa [AuthState.st,up,us,vs] using hw
private theorem clean_V (hp : n > 0) (a b : AuthState n) :
    let q := cleanSourceAuth hp cfg a b
    PairHole q ∨ (V q.1 = V a ∧ V q.2 = V b) := by
  have hv := T1_cv hp cfg (a,b)
  have ha := T1_pa hp cfg (a,b)
  have ht := clean_S hp cfg a b
  simp only [T1] at hv ha
  dsimp only
  generalize cleanSourceAuth hp cfg a b = q at hv ha ht ⊢
  rcases hv with ⟨vl,vr,pl,pr⟩
  rcases pl with pl | pl
  · rcases pr with pr | pr
    · right
      simp_all [V,cv,PA,av,dv,S,TokenSidecar,Prod.mk.injEq]
    · exact Or.inl (Or.inr pr)
  · exact Or.inl (Or.inl pl)


theorem first_clean_split (hp : n > 0) (h2 : 2 ≤ n) (k : Nat)
    (g : ProvColor) (i j : Nat) (l r : AuthState n) :
    let a := X0A6 hp g i l
    let b := X1Ready h2 g j r
    let c := cut hp k a b
    PairHole c ∨ (V c.1 = V a ∧ V c.2 = V b) := by
  dsimp only
  let a := X0A6 hp g i l
  let b := X1Ready h2 g j r
  change PairHole (cut hp k a b) ∨
    (V (cut hp k a b).1 = V a ∧ V (cut hp k a b).2 = V b)
  let p := P0 hp a b
  let q := genSigAuth hp k p.1 p.2
  let c := cleanSourceAuth hp cfg q.1 q.2
  have hcut : cut hp k a b = c := rfl
  rw [hcut]
  have hn : b.core.label.val = (a.core.label.val + 1) % n := by
    change 1 = (0 + 1) % n
    exact (Nat.mod_eq_of_lt (show 1 < n by omega)).symm
  obtain ⟨x,y,he⟩ := P0_frame hp a b rfl rfl hn
  have hv : V p.1 = V a ∧ V p.2 = V b := by
    change V (P0 hp a b).1 = V a ∧ V (P0 hp a b).2 = V b
    rw [he]
    exact ⟨rfl,rfl⟩
  have ap : a.core.path = .some 0 i := rfl
  have as : a.core.state = .less := rfl
  have bs : b.core.state = .CHECK_ready := rfl
  have hg : V q.1 = V p.1 ∧ V q.2 = V p.2 := by
    change V (genSigAuth hp k p.1 p.2).1 = V p.1 ∧
      V (genSigAuth hp k p.1 p.2).2 = V p.2
    exact gen_V hp k p.1 p.2 i
      ((congrArg (fun x => x.2.1) hv.1).trans ap)
      ((congrArg Prod.fst hv.1).trans as)
      ((congrArg Prod.fst hv.2).trans bs)
  have hc : PairHole c ∨ (V c.1 = V q.1 ∧ V c.2 = V q.2) := by
    change PairHole (cleanSourceAuth hp cfg q.1 q.2) ∨
      (V (cleanSourceAuth hp cfg q.1 q.2).1 = V q.1 ∧
       V (cleanSourceAuth hp cfg q.1 q.2).2 = V q.2)
    simpa only using (clean_V hp q.1 q.2)
  rcases hc with hh | ⟨h0,h1⟩
  · exact Or.inl hh
  · exact Or.inr ⟨h0.trans (hg.1.trans hv.1),h1.trans (hg.2.trans hv.2)⟩


private theorem rewrap (hp : n > 0) (h2 : 2 ≤ n) (g : ProvColor)
    (i j : Nat) (a b l r : AuthState n)
    (ha : V a = V (X0A6 hp g i l)) (hb : V b = V (X1Ready h2 g j r)) :
    X0A6 hp g i a = a ∧ X1Ready h2 g j b = b := by
  constructor
  · rcases a with ⟨c,pm,cm,sc,tm,m4,m5⟩
    cases c
    simp_all [V,X0A6,Prod.mk.injEq]
  · rcases b with ⟨c,pm,cm,sc,tm,m4,m5⟩
    cases c
    simp_all [V,X1Ready,Prod.mk.injEq]


private theorem orphan_R (u : AgentState n) :
    (normalizeOrphan u).path = u.path ∧ (normalizeOrphan u).path2 = u.path2 := by
  unfold normalizeOrphan
  (repeat' (first | exact ⟨rfl,rfl⟩ | rfl | (dsimp only) | split))
private theorem carrier_R (u : AgentState n) :
    (normalizeCarrier u).path = u.path ∧ (normalizeCarrier u).path2 = u.path2 := by
  unfold normalizeCarrier releaseCongest
  (repeat' (first | exact ⟨rfl,rfl⟩ | rfl | (dsimp only) | split))
private theorem norm_R (u : AuthState n) :
    RV (liftLife (fun x => normalizeCarrier (normalizeOrphan x)) u) = RV u := by
  have ho := orphan_R u.core
  have hc := carrier_R (normalizeOrphan u.core)
  have hp := hc.1.trans ho.1
  have ht := hc.2.trans ho.2
  unfold liftLife
  dsimp only
  split <;> simp only [RV,hp,ht]
private theorem norm_toss (a : AuthState n) (i : Nat)
    (hs : a.core.state = .toss) (hk : a.core.label.val = 0)
    (ha : a.core.path = .some 0 i) :
    liftLife (fun x => normalizeCarrier (normalizeOrphan x)) a = a := by
  have ho : normalizeOrphan a.core = a.core := by
    simp [normalizeOrphan,hs,hk,ha]
  have hc : normalizeCarrier a.core = a.core := by
    simp [normalizeCarrier,hs,ha]
  simp [liftLife,ho,hc]


private theorem repair_frame (a b : AuthState n) (i j : Nat)
    (hs : a.core.state = .toss) (hk : a.core.label.val = 0)
    (ha : a.core.path = .some 0 i) (hb : b.core.path = .some 1 j) :
    (repairAuth a b).1 = a ∧ RV (repairAuth a b).2 = RV b := by
  have hna := norm_toss a i hs hk ha
  have hnb := norm_R b
  unfold repairAuth
  dsimp only
  generalize liftLife (fun x => normalizeCarrier (normalizeOrphan x)) b = nb at hnb ⊢
  rw [hna]
  have nbp : nb.core.path = .some 1 j := (congrArg Prod.fst hnb).trans hb
  have hrel : lift2Life releaseReadySuffix a nb = (a,nb) := by
    simp [lift2Life,releaseReadySuffix,ha,nbp,hs]
  rw [hrel]
  dsimp only
  have hack : ackTailAuth a nb = (a,nb) := by
    simp [ackTailAuth,lift2,ackTail,ha,nbp,hs,lockedState]
  rw [hack]
  exact ⟨rfl,hnb⟩


private theorem compare_frame (k : Nat) (a b : AuthState n) (i j : Nat)
    (hs : a.core.state = .toss) (ha : a.core.path = .some 0 i)
    (hb : b.core.path = .some 1 j)
    (haTok : a.core.path2 = none) (hbTok : b.core.path2 = none) :
    (compareLifecycleAuth k a b).1 = a ∧ RV (compareLifecycleAuth k a b).2 = RV b := by
  let t : AuthState n := if lockedState b.st then b.lineage .depart else b
  have em : maintainAuth a b = (a,t) := by
    simp [t,maintainAuth,ha,hb,hs,AuthState.st,lockedState] <;> rfl
  have ht : RV t = RV b := by
    dsimp only [t]
    split <;> rfl
  have tp : t.core.path = .some 1 j := (congrArg Prod.fst ht).trans hb
  have tt : t.core.path2 = none := (congrArg (fun x => x.2.1) ht).trans hbTok
  have hc : completeWaveAuth a t = (a,t) := by
    simp [completeWaveAuth,ha,tp,hs,AuthState.st,lockedState]
  have hw : waveAuth a t = (a,t) := by
    simp [waveAuth,ha,tp,hs,haTok,tt,AuthState.st,lockedState,lockerState,sessionTokenOn]
  have hd : lift2 PPLLFableDesignR1.dropStray a t = (a,t) := by
    simp [lift2,PPLLFableDesignR1.dropStray,haTok,tt]
  have hla : landBackwardAuth a = a := by simp [landBackwardAuth,haTok]
  have hlb : landForwardAuth k t = t := by simp [landForwardAuth,tt]
  unfold compareLifecycleAuth
  simp only [ha]
  rw [em]
  dsimp only
  rw [hc]
  dsimp only
  rw [hw]
  dsimp only
  rw [hd]
  dsimp only
  rw [hla,hlb]
  exact ⟨rfl,ht⟩


private theorem tail_frame (k : Nat) (a b : AuthState n) (i j : Nat)
    (hs : a.core.state = .toss) (hk : a.core.label.val = 0)
    (ha : a.core.path = .some 0 i) (hb : b.core.path = .some 1 j)
    (haTok : a.core.path2 = none) (hbTok : b.core.path2 = none) :
    LV (tail k a b).1 = LV a ∧ RV (tail k a b).2 = RV b := by
  have h := repair_frame a b i j hs hk ha hb
  unfold tail
  generalize repairAuth a b = q at h ⊢
  dsimp only
  rcases h with ⟨h0,h1⟩
  rw [h0]
  have qp : q.2.core.path = .some 1 j := (congrArg Prod.fst h1).trans hb
  have qt : q.2.core.path2 = none := (congrArg (fun x => x.2.1) h1).trans hbTok
  have hc := compare_frame k a q.2 i j hs ha qp haTok qt
  exact ⟨congrArg LV hc.1,hc.2.trans h1⟩


private theorem retained_post (hp : n > 0) (h2 : 2 ≤ n) (k : Nat)
    (g : ProvColor) (i j : Nat) (l r : AuthState n) :
    Post g i j (B hp k (X0A6 hp g i l) (X1Ready h2 g j r)) := by
  have hrel : lift2Life (releaseSource hp) (X0A6 hp g i l) (X1Ready h2 g j r) =
      (X0A6 hp g i l,X1Ready h2 g j r) := by
    simp [lift2Life,releaseSource,X1Ready]
  have helim : lift2 (eliminateSig hp) (X0A6 hp g i l) (X1Ready h2 g j r) =
      (X0A6 hp g i l,X1Ready h2 g j r) := by
    simp [lift2,eliminateSig,X1Ready]
  have hd := first_retained_handoff hp h2 g i j l r
  simp only [B,hrel,helim]
  dsimp only at hd ⊢
  generalize preDisappear hp cfg (X0A6 hp g i l) (X1Ready h2 g j r) = q at hd ⊢
  generalize disappearAuth hp q.1 q.2 = d at hd ⊢
  simp only [V,CarrierV,X0Toss,X0A6,X1Ready,Prod.mk.injEq] at hd
  rcases hd with ⟨⟨s,p,t,kl,_,_,pm,cm,sc,tm⟩,⟨rp,rt,_,_,_,rm,_,_,_⟩⟩
  have hk : d.1.core.label.val = 0 := congrArg (fun x : Fin n => x.val) kl
  have hf := tail_frame k d.1 d.2 i j s hk p rp t rt
  refine ⟨hf.1.trans ?_,hf.2.trans ?_⟩
  · simp only [LV,Prod.mk.injEq]
    exact ⟨s,p,t,cm,pm,sc,tm⟩
  · simp only [RV,Prod.mk.injEq]
    exact ⟨rp,rt,rm⟩


private theorem LV_frame {a b : AuthState n}
    (hf : FV a = FV b) (hs : S a = S b) : LV a = LV b := by
  simp only [LV,FV,S,TokenSidecar,Prod.mk.injEq] at hf hs ⊢
  rcases hf with ⟨h0,h1,h2,_,h3,h4⟩
  rcases hs with ⟨h5,h6⟩
  exact ⟨h0,h1,h2,h3,h4,h5,h6⟩
private theorem RV_frame {a b : AuthState n} (hf : FV a = FV b) : RV a = RV b := by
  simp only [RV,FV,Prod.mk.injEq] at hf ⊢
  rcases hf with ⟨_,h1,h2,_,_,h3⟩
  exact ⟨h1,h2,h3⟩


private theorem first_emitter_service_pair (hp : n > 0) (h2 : 2 ≤ n) (k : Nat)
    (g : ProvColor) (i j : Nat) (l r a b : AuthState n)
    (ha : a = X0A6 hp g i l) (hb : b = X1Ready h2 g j r) :
    let q := PPLLAuthF.pipeline hp k cfg a b
    Target q ∨ (Post g i j q ∧ q.1.core.label.val = 0 ∧ q.2.core.label.val = 1) := by
  dsimp only
  generalize hout : PPLLAuthF.pipeline hp k cfg a b = out
  have hal : a.core.leader = false := by rw [ha]; rfl
  have hbl : b.core.leader = false := by rw [hb]; rfl
  have har : a.core.reset_cmd = false := by rw [ha]; rfl
  have hbr : b.core.reset_cmd = false := by rw [hb]; rfl
  have hn : b.core.label = ⟨(a.core.label.val + 1) % n,Nat.mod_lt _ hp⟩ := by
    rw [ha,hb]
    apply Fin.ext
    change 1 = (0 + 1) % n
    exact (Nat.mod_eq_of_lt (show 1 < n by omega)).symm
  have hc : PairHole (cut hp k a b) ∨
      (V (cut hp k a b).1 = V a ∧ V (cut hp k a b).2 = V b) := by
    rw [ha,hb]
    simpa only using (first_clean_split hp h2 k g i j l r)
  rcases hc with hh | ⟨h0,h1⟩
  · have hh' : PairHole (PPLLAuthCheckPostCleanHole.postCleanCut hp k cfg a b) := by
      change PairHole (cut hp k a b)
      exact hh
    have hpH :=
      PPLLAuthCheckPostCleanHole.pipeline_pairHole_of_postClean hp k cfg a b hh'
    have hoH : PairHole out := by rw [← hout]; exact hpH
    exact Or.inl (Or.inr (Or.inr hoH))
  · by_cases hr : out.2.core.leader = true
    · exact Or.inl (Or.inr (Or.inl hr))
    · have hr0 : out.2.core.leader = false := by
        cases he : out.2.core.leader
        · rfl
        · exact False.elim (hr he)
      have hrp : (PPLLAuthF.pipeline hp k cfg a b).2.core.leader = false := by
        rw [hout]
        exact hr0
      have hs0 := row_std hp k cfg a b hal hbl har hbr hn hrp
      rw [hout] at hs0
      let c := cut hp k a b
      have hc0 : V c.1 = V a := by
        change V (cut hp k a b).1 = V a
        exact h0
      have hc1 : V c.2 = V b := by
        change V (cut hp k a b).2 = V b
        exact h1
      have he := rewrap hp h2 g i j c.1 c.2 l r
        (hc0.trans (congrArg V ha)) (hc1.trans (congrArg V hb))
      have hz := retained_post hp h2 k g i j c.1 c.2
      have eb : beforeSuppressAuth hp k cfg a b = B hp k c.1 c.2 := by
        change beforeSuppressAuth hp k cfg a b =
          B hp k (cut hp k a b).1 (cut hp k a b).2
        rfl
      rw [he.1,he.2,← eb] at hz
      have hf := pipeline_FV hp k cfg a b hal hbl har hbr
      have ht := pipeline_tokenSidecar hp k cfg a b hal hbl har hbr
      rw [hout] at hf ht
      right
      refine ⟨?_,?_,?_⟩
      · exact ⟨(LV_frame hf.1 ht.1).trans hz.1,(RV_frame hf.2).trans hz.2⟩
      · calc
          out.1.core.label.val = a.core.label.val := congrArg Fin.val hs0.1
          _ = 0 := by rw [ha]; rfl
      · calc
          out.2.core.label.val = b.core.label.val := congrArg Fin.val hs0.2.1
          _ = 1 := by rw [hb]; rfl


theorem first_emitter_service (hp : n > 0) (h2 : 2 ≤ n) (k : Nat)
    (g : ProvColor) (i j : Nat) (l r : AuthState n) :
    let q := PPLLAuthF.pipeline hp k cfg (X0A6 hp g i l) (X1Ready h2 g j r)
    Target q ∨ (Post g i j q ∧ q.1.core.label.val = 0 ∧ q.2.core.label.val = 1) := by
  exact first_emitter_service_pair hp h2 k g i j l r
    (X0A6 hp g i l) (X1Ready h2 g j r) rfl rfl


#print axioms first_clean_split
#print axioms first_emitter_service

end PPLLAuthFirstEmitterService
