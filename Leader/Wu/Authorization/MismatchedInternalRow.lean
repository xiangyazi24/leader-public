import Leader.Wu.Authorization.PostCleanHole
import Leader.Wu.Authorization.TokenSidecarFrame

/-! Original unsupported left lock/compare1 against right compare2.
The retained outcome releases only the LEFT cell to lineage-depart. The right
stays compare2 except for terminal carry producing E; this does not extend a
departed prefix across the right cell. The actual prefix preserves p/p_carry,
so rightE_iff uses their original values. No final lottery-field frame is claimed.
The pipeline hole corollary is compiled internal support, not a separately
accepted headline. This module is an unverified proposal. -/

namespace PPLLAuthMismatchedInternalRow
open PPLL PPLLRepair PPLLBirthPatch PPLLBirthPatchM2 PPLLPostElectionGuard
open PPLLFableDesignR1 PPLLAstraDesign2 PPLLAstraDesign3 PPLLAuthF
open PPLLAuthF.AuthState
open PPLLAuthGenDrain (P0 P0_frame W_fields T1 T1_cv T1_pa cv PA FV pipeline_FV row_std)
open PPLLAuthResetDrain (av dv wait_dv beforeSuppressAuth fst_ite snd_ite)
open PPLLAuthTokenSidecarFrame (TokenSidecar pipeline_tokenSidecar)
open PPLLAuthFPairHole (PairHole)
set_option autoImplicit false
variable {n : Nat}

abbrev cfg : PPLLAuthF.Cfg :=
  { retire := true, markClean := true, claimCheck := true }
abbrev CV := MainState × PathInfo × Option Path2Info × ProvColor × ProvColor
abbrev AV := Bool × Bool × P2Scope × ProvColor

def C (u : AuthState n) : CV :=
  (u.core.state,u.core.path,u.core.path2,u.ctrl_mark,u.path_mark)
def A (u : AuthState n) : AV :=
  (u.core.p,u.core.p_carry,u.path2_scope,u.path2_mark)
def V (u : AuthState n) : CV × (Bool × Bool × Fin n × Bool) × AV :=
  (C u,av u,A u)

structure InRow (l r : AuthState n) (j bl br : Nat) (g : ProvColor) : Prop where
  bound : j+1<n
  lk : l.core.label.val=j
  rk : r.core.label.val=j+1
  lp : l.core.path=.some j bl
  rp : r.core.path=.some (j+1) br
  ls : l.core.state=.lock ∨ l.core.state=.compare1
  rs : r.core.state=.compare2
  lt : l.core.path2=none
  rt : r.core.path2=none
  ll : l.core.leader=false
  rl : r.core.leader=false
  lr : l.core.reset_cmd=false
  rr : r.core.reset_cmd=false
  lm : l.path_mark=g
  rm : r.path_mark=g
  ne : l.ctrl_mark≠r.ctrl_mark

def rightState (j : Nat) (l r : AuthState n) : MainState :=
  if j+1=n-1 ∧ l.core.p_carry=true ∧ r.core.p=true
  then .eliminate_signal else .compare2

def Fields (l r : AuthState n) (j bl br : Nat) (g : ProvColor)
    (q : AuthState n × AuthState n) : Prop :=
  C q.1=(.depart,.some j bl,none,g,g) ∧
  C q.2=(rightState j l r,.some (j+1) br,none,r.ctrl_mark,g) ∧
  TokenSidecar q.1=TokenSidecar l ∧ TokenSidecar q.2=TokenSidecar r

def Std (l r : AuthState n) (q : AuthState n × AuthState n) : Prop :=
  q.1.core.label=l.core.label ∧ q.2.core.label=r.core.label ∧
  q.1.core.reset_cmd=false ∧ q.2.core.reset_cmd=false ∧
  q.1.core.leader=false ∧ q.2.core.leader=false

def Target (q : AuthState n × AuthState n) : Prop :=
  q.1.core.leader=true ∨ q.2.core.leader=true ∨ PairHole q

private theorem A_ite (p : Prop) [Decidable p] (a b : AuthState n) :
    A (if p then a else b)=if p then A a else A b := by split <;> rfl
private theorem p_ite (p : Prop) [Decidable p] (a b : AgentState n) :
    (if p then a else b).p=if p then a.p else b.p := by split <;> rfl
private theorem pc_ite (p : Prop) [Decidable p] (a b : AgentState n) :
    (if p then a else b).p_carry=if p then a.p_carry else b.p_carry := by split <;> rfl
private theorem clear4_A (u : AuthState n) :
    A {u with core:={u.core with path4:=none}}=A u := rfl
private theorem clear5_A (u : AuthState n) :
    A {u with core:={u.core with path5:=none}}=A u := rfl
private theorem gen_A (u : AuthState n) : A (genConnectAuth u)=A u := by
  unfold genConnectAuth cleanSigGenConnect
  (repeat' (first | rfl | (dsimp only) | split))

private def ca4 (p : Nat) (u : AuthState n) : AuthState n :=
  match u.core.path4 with
  | some (v,_) =>
    if v=(-1 : Int) then
      if u.path4_mark==u.path_mark then
        let c := if p=0 then {u.core with path4:=none} else u.core
        {u with core:={c with path:=.bot}}
      else {u with core:={u.core with path4:=none}}
    else u
  | none => u
private def ca5 (p : Nat) (u : AuthState n) : AuthState n :=
  match u.core.path5 with
  | some (v,_) =>
    if v=(-1 : Int) then
      if u.path5_mark==u.path_mark then
        let c := if p=n-1 then {u.core with path5:=none} else u.core
        {u with core:={c with path:=.bot}}
      else {u with core:={u.core with path5:=none}}
    else u
  | none => u
private theorem ca4_A (p : Nat) (u : AuthState n) : A (ca4 p u)=A u := by
  unfold ca4
  repeat (first | rfl | split)
private theorem ca5_A (p : Nat) (u : AuthState n) : A (ca5 p u)=A u := by
  unfold ca5
  repeat (first | rfl | split)
private theorem apply_A (u : AuthState n) : A (cleanApplyAuth u)=A u := by
  have e : cleanApplyAuth u = match u.core.path with
    | .bot => u | .some p _ => ca5 p (ca4 p u) := rfl
  rw [e]
  cases h : u.core.path with
  | bot => rfl
  | some p b => exact (ca5_A p (ca4 p u)).trans (ca4_A p u)

private theorem a3 (c : PPLLAuthF.Cfg) (a b : AuthState n) :
    A (step3Auth c.cleanNbr c.markClean a b).1=A a ∧
    A (step3Auth c.cleanNbr c.markClean a b).2=A b := by
  unfold step3Auth
  (repeat' (first | exact ⟨rfl,rfl⟩ | (dsimp only) | split))
private theorem a4 (c : PPLLAuthF.Cfg) (a b : AuthState n) :
    A (step4Auth c.cleanNbr c.markClean a b).1=A a ∧
    A (step4Auth c.cleanNbr c.markClean a b).2=A b := by
  unfold step4Auth
  (repeat' (first | exact ⟨rfl,rfl⟩ | (dsimp only) | split))
private theorem a5 (hp : n>0) (a b : AuthState n) :
    A (step5Auth hp a b).1=A a ∧ A (step5Auth hp a b).2=A b := by
  unfold step5Auth
  (repeat' (first | exact ⟨rfl,rfl⟩ | (dsimp only) | split))
private theorem a6 (hp : n>0) (a b : AuthState n) :
    A (step6Auth hp a b).1=A a ∧ A (step6Auth hp a b).2=A b := by
  unfold step6Auth
  (repeat' (first | exact ⟨rfl,rfl⟩ | (dsimp only) | split))
private theorem clean_A (hp : n>0) (a b : AuthState n) :
    A (cleanSourceAuth hp cfg a b).1=A a ∧
    A (cleanSourceAuth hp cfg a b).2=A b := by
  -- These are exactly the two guarded stages in cleanSourceAuth.
  let pass5 (u v : AuthState n) : AuthState n × AuthState n :=
    if isCmd u.core.path4 then
      (u, {v with core := {v.core with path4 := none}})
    else step5Auth hp u v
  let pass6 (u v : AuthState n) : AuthState n × AuthState n :=
    if isCmd v.core.path5 then
      ({u with core := {u.core with path5 := none}}, v)
    else step6Auth hp u v

  have hpass5 (u v : AuthState n) :
      A (pass5 u v).1 = A u ∧ A (pass5 u v).2 = A v := by
    by_cases hc : isCmd u.core.path4 = true
    · simpa only [pass5, if_pos hc] using
        (show A u = A u ∧
          A {v with core := {v.core with path4 := none}} = A v from
          ⟨rfl, clear4_A v⟩)
    · simpa only [pass5, if_neg hc] using (a5 hp u v)
  have hpass6 (u v : AuthState n) :
      A (pass6 u v).1 = A u ∧ A (pass6 u v).2 = A v := by
    by_cases hc : isCmd v.core.path5 = true
    · simpa only [pass6, if_pos hc] using
        (show A {u with core := {u.core with path5 := none}} = A u ∧
          A v = A v from ⟨clear5_A u, rfl⟩)
    · simpa only [pass6, if_neg hc] using (a6 hp u v)

  let q3 := step3Auth cfg.cleanNbr cfg.markClean
    (genConnectAuth a) (genConnectAuth b)
  have h3 : A q3.1 = A a ∧ A q3.2 = A b := by
    have hs := a3 cfg (genConnectAuth a) (genConnectAuth b)
    exact ⟨hs.1.trans (gen_A a), hs.2.trans (gen_A b)⟩

  let q4 := step4Auth cfg.cleanNbr cfg.markClean q3.1 q3.2
  have h4 : A q4.1 = A a ∧ A q4.2 = A b := by
    have hs := a4 cfg q3.1 q3.2
    exact ⟨hs.1.trans h3.1, hs.2.trans h3.2⟩

  let q5 := pass5 q4.1 q4.2
  have h5 : A q5.1 = A a ∧ A q5.2 = A b := by
    have hs := hpass5 q4.1 q4.2
    exact ⟨hs.1.trans h4.1, hs.2.trans h4.2⟩

  let q6 := pass6 q5.1 q5.2
  have h6 : A q6.1 = A a ∧ A q6.2 = A b := by
    have hs := hpass6 q5.1 q5.2
    exact ⟨hs.1.trans h5.1, hs.2.trans h5.2⟩

  change A (cleanApplyAuth q6.1) = A a ∧
    A (cleanApplyAuth q6.2) = A b
  exact ⟨(apply_A q6.1).trans h6.1,
    (apply_A q6.2).trans h6.2⟩

private theorem wait_V (hp : n>0) (k : Nat) (a b : AuthState n) :
    V (lift2 (waitSaturated hp k) a b).1=V a ∧
    V (lift2 (waitSaturated hp k) a b).2=V b := by
  have ha : A (lift2 (waitSaturated hp k) a b).1=A a ∧
      A (lift2 (waitSaturated hp k) a b).2=A b := by
    simp only [lift2,A,waitSaturated,waitSaturatedPrepare,waitSaturatedCarry,
      waitSaturatedReset,waitSaturatedFinish]
    simp [fst_ite,snd_ite,p_ite,pc_ite]
  obtain ⟨a1,a2,a3,a4,a5,a6,a7,b1,b2,b3,b4,b5,b6,b7⟩ := W_fields hp k a b
  have hd := wait_dv hp k a.core b.core
  simp only [V,C,Prod.mk.injEq]
  exact ⟨⟨⟨a1,a2,a3,a6,a7⟩,hd.1,ha.1⟩,
    ⟨⟨b1,b2,b3,b6,b7⟩,hd.2,ha.2⟩⟩

private theorem from_V (a b l r : AuthState n) (j bl br : Nat) (g : ProvColor)
    (h : InRow l r j bl br g) (ha : V a=V l) (hb : V b=V r) : InRow a b j bl br g := by
  rcases h with ⟨bd,lk,rk,lp,rp,ls,rs,lt,rt,ll,rl,lr,rr,lm,rm,ne⟩
  constructor <;> simp_all [V,C,A,av,dv,Prod.mk.injEq]

private theorem gen_V (hp : n>0) (k : Nat) (a b : AuthState n) (j bl : Nat)
    (pa : a.core.path=.some j bl)
    (sa : a.core.state=.lock ∨ a.core.state=.compare1) (sb : b.core.state=.compare2) :
    V (genSigAuth hp k a b).1=V a ∧ V (genSigAuth hp k a b).2=V b := by
  have hw := wait_V hp k a b
  have hg : genSigAuth hp k a b =
      lift2 (waitSaturated hp k) a b := by
    unfold genSigAuth
    generalize lift2 (waitSaturated hp k) a b = q at hw ⊢
    rcases q with ⟨u,v⟩
    change V u = V a ∧ V v = V b at hw
    have up : u.core.path = .some j bl :=
      (congrArg (fun x => x.1.2.1) hw.1).trans pa
    have us : u.core.state = a.core.state :=
      congrArg (fun x => x.1.1) hw.1
    have vs : v.core.state = .compare2 :=
      (congrArg (fun x => x.1.1) hw.2).trans sb
    rcases sa with hs | hs <;>
      simp [AuthState.st, up, us, vs, hs]
  simpa only [hg] using hw

private theorem clean_V (hp : n>0) (a b : AuthState n) :
    PairHole (cleanSourceAuth hp cfg a b) ∨
    (V (cleanSourceAuth hp cfg a b).1=V a ∧ V (cleanSourceAuth hp cfg a b).2=V b) := by
  have hv := T1_cv hp cfg (a,b)
  have ha := T1_pa hp cfg (a,b)
  have ht := clean_A hp a b
  simp only [T1] at hv ha
  generalize cleanSourceAuth hp cfg a b=q at hv ha ht ⊢
  rcases hv with ⟨vl,vr,pl,pr⟩
  rcases pl with pl | pl
  · rcases pr with pr | pr
    · right; simp_all [V,C,A,cv,PA,av,dv,Prod.mk.injEq]
    · exact Or.inl (Or.inr pr)
  · exact Or.inl (Or.inl pl)

def cut (hp : n>0) (k : Nat) (l r : AuthState n) : AuthState n × AuthState n :=
  let p := P0 hp l r
  let q := genSigAuth hp k p.1 p.2
  cleanSourceAuth hp cfg q.1 q.2

private theorem prefix_V (hp : n>0) (k : Nat) (l r : AuthState n)
    (j bl br : Nat) (g : ProvColor) (h : InRow l r j bl br g) :
    PairHole (cut hp k l r) ∨ (V (cut hp k l r).1=V l ∧ V (cut hp k l r).2=V r) := by
  let p := P0 hp l r
  let q := genSigAuth hp k p.1 p.2
  let z := cleanSourceAuth hp cfg q.1 q.2
  have hcut : cut hp k l r = z := rfl
  rw [hcut]

  have hn : r.core.label.val = (l.core.label.val + 1) % n := by
    rw [h.lk, h.rk, Nat.mod_eq_of_lt h.bound]
  obtain ⟨x,y,he⟩ := P0_frame hp l r h.ll h.rl hn
  have hv : V p.1 = V l ∧ V p.2 = V r := by
    change V (P0 hp l r).1 = V l ∧ V (P0 hp l r).2 = V r
    rw [he]
    exact ⟨rfl,rfl⟩

  have hi := from_V p.1 p.2 l r j bl br g h hv.1 hv.2
  have hg : V q.1 = V p.1 ∧ V q.2 = V p.2 := by
    change V (genSigAuth hp k p.1 p.2).1 = V p.1 ∧
      V (genSigAuth hp k p.1 p.2).2 = V p.2
    exact gen_V hp k p.1 p.2 j bl hi.lp hi.ls hi.rs
  have hc : PairHole z ∨ (V z.1 = V q.1 ∧ V z.2 = V q.2) := by
    change PairHole (cleanSourceAuth hp cfg q.1 q.2) ∨
      (V (cleanSourceAuth hp cfg q.1 q.2).1 = V q.1 ∧
       V (cleanSourceAuth hp cfg q.1 q.2).2 = V q.2)
    exact clean_V hp q.1 q.2
  rcases hc with hh | ⟨h0,h1⟩
  · exact Or.inl hh
  · exact Or.inr
      ⟨h0.trans (hg.1.trans hv.1), h1.trans (hg.2.trans hv.2)⟩

private def preD (hp : n>0) (l r : AuthState n) : AuthState n × AuthState n :=
  let q := lift2Life (releaseSource hp) l r
  let q := lift2 (eliminateSig hp) q.1 q.2
  let q := moveSourceAuth hp cfg q.1 q.2
  let q := (liftLife dropStale q.1,liftLife dropStale q.2)
  let q := preCheckResetAuth q.1 q.2
  let q := (liftLife normalizeReady q.1,liftLife normalizeReady q.2)
  checkSourceAuth hp cfg q.1 q.2

def preDisappearCut (hp : n>0) (k : Nat) (l r : AuthState n) : AuthState n × AuthState n :=
  let q := cut hp k l r
  preD hp q.1 q.2

private theorem preD_id (hp : n>0) (l r : AuthState n)
    (j bl br : Nat) (g : ProvColor) (h : InRow l r j bl br g) : preD hp l r=(l,r) := by
  have hv : validateCheck l r=(l,r) := by
    rcases h.ls with ls | ls <;>
      simp [validateCheck,headBad,checkState,verdict,AuthState.st,ls,h.rs]
  have hm : moveSourceAuth hp cfg l r=(l,r) := by
    rcases h.ls with ls | ls <;>
      simp [moveSourceAuth,hv,sanitizeP2,p2Valid,step1Auth,moveTokensAuth,
        leaderWallAuth,applyControlAuth,AuthState.st,h.lp,h.rp,ls,h.rs,h.lt,h.rt,h.ll,h.rl]
  have hcL : checkSigCheckL hp l.core=l.core := by
    rcases h.ls with ls | ls <;> cases hj : j <;>
      simp [checkSigCheckL,h.lp,hj,ls]
  have hc : checkSourceAuth hp cfg l r=(l,r) := by
    rcases h.ls with ls | ls <;>
      simp [checkSourceAuth,cfg,hv,readyAuth,waveState,hcL,certPred,issue,
        AuthState.st,AuthState.withCore,h.lp,h.rp,ls,h.rs]
  rcases h.ls with ls | ls <;>
    simp [preD,lift2Life,releaseSource,lift2,eliminateSig,h.rs,hm,hc,liftLife,
      dropStale,aligned,preCheckResetAuth,normalizeReady,normalizeOrphan,
      normalizeCarrier,releaseCongest,h.lp,h.rp,h.lk,h.rk,ls,h.ll,h.rl,h.lr,h.rr]

private def tail (k : Nat) (l r : AuthState n) : AuthState n × AuthState n :=
  let q := repairAuth l r
  compareLifecycleAuth k q.1 q.2
private def B (hp : n>0) (k : Nat) (l r : AuthState n) : AuthState n × AuthState n :=
  let q := preD hp l r
  let q := disappearAuth hp q.1 q.2
  tail k q.1 q.2

private theorem tail_exact (k : Nat) (l r : AuthState n) (j bl br : Nat)
    (bd : j+1<n) (lp : l.core.path=.some j bl) (rp : r.core.path=.some (j+1) br)
    (ls : l.core.state=.lock ∨ l.core.state=.compare1)
    (rs : r.core.state=.compare2 ∨ r.core.state=.eliminate_signal)
    (lt : l.core.path2=none) (rt : r.core.path2=none)
    (ll : l.core.leader=false) (rl : r.core.leader=false) (ne : l.ctrl_mark≠r.ctrl_mark) :
    tail k l r=(l.lineage .depart,r) := by
  have hn : j≠n-1 := by omega
  have nr := Ne.symm ne
  rcases ls with ls | ls <;> rcases rs with rs | rs <;>
    simp [tail,repairAuth,liftLife,normalizeOrphan,normalizeCarrier,releaseCongest,
      lift2Life,releaseReadySuffix,ackTailAuth,compareLifecycleAuth,maintainAuth,
      completeWaveAuth,waveAuth,lift2,PPLLFableDesignR1.dropStray,landBackwardAuth,
      landForwardAuth,lockedState,waveState,AuthState.st,AuthState.setState,
      AuthState.lineage,AuthState.withCore,lp,rp,ls,rs,lt,rt,ll,rl,ne,nr,hn]

private theorem disappear_fields (hp : n>0) (l r : AuthState n)
    (j bl br : Nat) (g : ProvColor) (h : InRow l r j bl br g) :
    let q := disappearAuth hp l r
    C q.1=C l ∧ C q.2=C (r.setState (rightState j l r)) ∧
    TokenSidecar q.1=TokenSidecar l ∧ TokenSidecar q.2=TokenSidecar r ∧
    q.1.core.leader=false ∧ q.2.core.leader=false := by
  have term : (r.core.label=(⟨n-1,by omega⟩ : Fin n)) ↔ j+1=n-1 := by
    constructor
    · intro e; exact h.rk.symm.trans (congrArg Fin.val e)
    · intro e; apply Fin.ext; exact h.rk.trans e
  rcases h.ls with ls | ls <;>
    cases hc : l.core.p_carry <;> cases hb : r.core.p <;>
    by_cases ht : j+1=n-1 <;>
    simp [disappearAuth,disappearStartL,disappearCarry,lift2,C,rightState,
      TokenSidecar,AuthState.st,AuthState.setState,ls,h.rs,h.ll,h.rl,hc,hb,term,ht]

private theorem retained_B (hp : n>0) (k : Nat) (l r : AuthState n)
    (j bl br : Nat) (g : ProvColor) (h : InRow l r j bl br g) :
    Fields l r j bl br g (B hp k l r) := by
  have hd := disappear_fields hp l r j bl br g h
  simp only [B,preD_id hp l r j bl br g h]
  generalize disappearAuth hp l r=d at hd ⊢
  rcases hd with ⟨cl,cr,sl,sr,dl,dr⟩
  simp only [C,AuthState.setState,Prod.mk.injEq] at cl cr
  rcases cl with ⟨ds,dp,dt,dc,dm⟩
  rcases cr with ⟨es,ep,et,ec,em⟩
  have dls : d.1.core.state=.lock ∨ d.1.core.state=.compare1 := by rw [ds]; exact h.ls
  have ers : d.2.core.state=.compare2 ∨ d.2.core.state=.eliminate_signal := by
    rw [es]; unfold rightState; split <;> simp
  have dne : d.1.ctrl_mark≠d.2.ctrl_mark := by rw [dc,ec]; exact h.ne
  rw [tail_exact k d.1 d.2 j bl br h.bound (dp.trans h.lp) (ep.trans h.rp)
    dls ers (dt.trans h.lt) (et.trans h.rt) dl dr dne]
  refine ⟨?_,?_,sl,sr⟩
  · simp [C,AuthState.lineage,dp,dt,dm,h.lp,h.lt,h.lm]
  · simp [C,es,ep,et,ec,em,h.rp,h.rt,h.rm]

private theorem fields_lift (a b l r : AuthState n) (j bl br : Nat) (g : ProvColor)
    (z q : AuthState n × AuthState n) (ha : V a=V l) (hb : V b=V r)
    (hz : Fields a b j bl br g z)
    (hf : FV q.1=FV z.1 ∧ FV q.2=FV z.2)
    (ht : TokenSidecar q.1=TokenSidecar z.1 ∧ TokenSidecar q.2=TokenSidecar z.2) :
    Fields l r j bl br g q := by
  simp_all [Fields,C,V,A,FV,TokenSidecar,rightState,Prod.mk.injEq]

/-- Original entrance only; the produced cut frame is a conclusion. -/
theorem full_row (hp : n>0) (k : Nat) (l r : AuthState n)
    (j bl br : Nat) (g : ProvColor) (h : InRow l r j bl br g) :
    let q := PPLLAuthF.pipeline hp k cfg l r
    Target q ∨ (Fields l r j bl br g q ∧ Std l r q ∧
      V (preDisappearCut hp k l r).1=V l ∧ V (preDisappearCut hp k l r).2=V r) := by
  dsimp only
  by_cases hl : (PPLLAuthF.pipeline hp k cfg l r).1.core.leader=true
  · exact Or.inl (Or.inl hl)
  by_cases hr : (PPLLAuthF.pipeline hp k cfg l r).2.core.leader=true
  · exact Or.inl (Or.inr (Or.inl hr))
  have hl0 : (PPLLAuthF.pipeline hp k cfg l r).1.core.leader=false := by
    cases he : (PPLLAuthF.pipeline hp k cfg l r).1.core.leader <;> simp_all
  have hr0 : (PPLLAuthF.pipeline hp k cfg l r).2.core.leader=false := by
    cases he : (PPLLAuthF.pipeline hp k cfg l r).2.core.leader <;> simp_all
  have hn : r.core.label=⟨(l.core.label.val+1)%n,Nat.mod_lt _ hp⟩ := by
    apply Fin.ext
    change r.core.label.val=(l.core.label.val+1)%n
    rw [h.lk,h.rk,Nat.mod_eq_of_lt h.bound]
  have hs := row_std hp k cfg l r h.ll h.rl h.lr h.rr hn hr0
  have hc := prefix_V hp k l r j bl br g h
  have eb : beforeSuppressAuth hp k cfg l r=B hp k (cut hp k l r).1 (cut hp k l r).2 := rfl
  generalize hcut : cut hp k l r=c at hc eb
  rcases hc with hh | ⟨h0,h1⟩
  · have hd : PairHole (PPLLAuthCheckPostCleanHole.postCleanCut hp k cfg l r) := by
      change PairHole (cut hp k l r)
      rw [hcut]; exact hh
    exact Or.inl (Or.inr (Or.inr
      (PPLLAuthCheckPostCleanHole.pipeline_pairHole_of_postClean hp k cfg l r hd)))
  · have hi := from_V c.1 c.2 l r j bl br g h h0 h1
    have ec : V (preDisappearCut hp k l r).1=V l ∧
        V (preDisappearCut hp k l r).2=V r := by
      unfold preDisappearCut
      rw [hcut]
      dsimp only
      rw [preD_id hp c.1 c.2 j bl br g hi]
      exact ⟨h0,h1⟩
    have hz := retained_B hp k c.1 c.2 j bl br g hi
    have hf := pipeline_FV hp k cfg l r h.ll h.rl h.lr h.rr
    have ht := pipeline_tokenSidecar hp k cfg l r h.ll h.rl h.lr h.rr
    generalize beforeSuppressAuth hp k cfg l r=z at eb hf ht
    rw [← eb] at hz
    generalize PPLLAuthF.pipeline hp k cfg l r=q at hf ht hs hl0 hr0 ⊢
    exact Or.inr ⟨fields_lift c.1 c.2 l r j bl br g z q h0 h1 hz hf ht,
      ⟨hs.1,hs.2.1,hs.2.2.1,hs.2.2.2,hl0,hr0⟩,ec.1,ec.2⟩

theorem rightE_iff (l r : AuthState n) (j bl br : Nat) (g : ProvColor)
    (q : AuthState n × AuthState n) (h : Fields l r j bl br g q) :
    q.2.core.state=.eliminate_signal ↔ j+1=n-1 ∧ l.core.p_carry=true ∧ r.core.p=true := by
  have he := congrArg Prod.fst h.2.1
  change q.2.core.state=rightState j l r at he
  rw [he]
  unfold rightState
  split <;> simp_all

-- The n=2, j=0 case has no additional entrance guard.
theorem psi2 (k : Nat) (l r : AuthState 2) (bl br : Nat) (g : ProvColor)
    (h : InRow l r 0 bl br g) :
    let q := PPLLAuthF.pipeline (by omega : 2>0) k cfg l r
    Target q ∨ (Fields l r 0 bl br g q ∧ Std l r q ∧
      V (preDisappearCut (by omega) k l r).1=V l ∧
      V (preDisappearCut (by omega) k l r).2=V r) :=
  full_row (by omega) k l r 0 bl br g h

#print axioms full_row
#print axioms rightE_iff
#print axioms psi2
end PPLLAuthMismatchedInternalRow
