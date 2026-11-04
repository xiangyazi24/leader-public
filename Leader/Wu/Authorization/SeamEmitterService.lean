import Leader.Wu.Authorization.A6A5RetainedCut
import Leader.Wu.Authorization.PostCleanHole
import Leader.Wu.Authorization.TokenSidecarFrame

/-! Original B-tail / X-head toss seam service, with independent B/X marks.
Post records the canonical A5 view, not whole-record equality to X0A5 and not
final p/p_carry/bit values. This is one original full row; population-word
composition is separate. Uses the accepted raw post-CLEAN hole theorem. -/

namespace PPLLAuthSeamEmitterService

open PPLL PPLLRepair PPLLBirthPatch PPLLBirthPatchM2 PPLLPostElectionGuard
open PPLLFableDesignR1 PPLLAstraDesign2 PPLLAstraDesign3 PPLLAuthF
open PPLLAuthA6A5RetainedCut
open PPLLAuthGenDrain (P0 P0_frame W_fields T1 T1_cv T1_pa cv PA FV pipeline_FV row_std)
open PPLLAuthResetDrain (av dv wait_dv beforeSuppressAuth fst_ite snd_ite)
open PPLLAuthTokenSidecarFrame (TokenSidecar pipeline_tokenSidecar)
open PPLLAuthCheckPostCleanHole (afterCleanToFinal afterCleanToFinal_pairHole)
open PPLLAuthFPairHole (PairHole)

set_option autoImplicit false
variable {n : Nat}

private abbrev S (u : AuthState n) : P2Scope × ProvColor := TokenSidecar u

def LV (u : AuthState n) :
    MainState × PathInfo × Option Path2Info × ProvColor × ProvColor :=
  (u.core.state, u.core.path, u.core.path2, u.path_mark, u.ctrl_mark)

def Post (gB gX : ProvColor) (i j : Nat) (q : AuthState n × AuthState n) : Prop :=
  LV q.1 = (.depart, .some (n - 1) i, none, gB, gB) ∧
  LV q.2 = (.toss_done, .some 0 j, some A5, gX, gX) ∧
  TokenSidecar q.2 = (.line, gX)

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
  (repeat' (first | exact ⟨rfl, rfl⟩ | (dsimp only) | split))

private theorem s4 (c : PPLLAuthF.Cfg) (a b : AuthState n) :
    S (step4Auth c.cleanNbr c.markClean a b).1 = S a ∧
    S (step4Auth c.cleanNbr c.markClean a b).2 = S b := by
  unfold step4Auth
  (repeat' (first | exact ⟨rfl, rfl⟩ | (dsimp only) | split))

private theorem s5 (hp : n > 0) (a b : AuthState n) :
    S (step5Auth hp a b).1 = S a ∧ S (step5Auth hp a b).2 = S b := by
  unfold step5Auth
  (repeat' (first | exact ⟨rfl, rfl⟩ | (dsimp only) | split))

private theorem s6 (hp : n > 0) (a b : AuthState n) :
    S (step6Auth hp a b).1 = S a ∧ S (step6Auth hp a b).2 = S b := by
  unfold step6Auth
  (repeat' (first | exact ⟨rfl, rfl⟩ | (dsimp only) | split))

private theorem clean_S (hp : n > 0) (c : PPLLAuthF.Cfg) (a b : AuthState n) :
    S (cleanSourceAuth hp c a b).1 = S a ∧
    S (cleanSourceAuth hp c a b).2 = S b := by
  simp only [cleanSourceAuth, fst_ite, snd_ite, s_ite, s_core,
    s_apply, s6, s5, s4, s3, s_gen, ite_self, and_self]

private theorem wait_V (hp : n > 0) (k : Nat) (a b : AuthState n) :
    V (lift2 (waitSaturated hp k) a b).1 = V a ∧
    V (lift2 (waitSaturated hp k) a b).2 = V b := by
  obtain ⟨a1,a2,a3,a4,a5,a6,a7,b1,b2,b3,b4,b5,b6,b7⟩ := W_fields hp k a b
  have hd := wait_dv hp k a.core b.core
  simp only [V, Prod.mk.injEq]
  exact ⟨⟨a1,a2,a3,a4,a5,congrArg Prod.fst hd.1,a7,a6,rfl,rfl⟩,
    ⟨b1,b2,b3,b4,b5,congrArg Prod.fst hd.2,b7,b6,rfl,rfl⟩⟩

private theorem gen_V (hp : n > 0) (k : Nat) (a b : AuthState n) (p i : Nat)
    (ha : a.core.path = .some p i) (hs : a.core.state = .depart)
    (hr : b.core.state = .toss) :
    V (genSigAuth hp k a b).1 = V a ∧ V (genSigAuth hp k a b).2 = V b := by
  have hw := wait_V hp k a b
  unfold genSigAuth
  generalize lift2 (waitSaturated hp k) a b = q at hw ⊢
  rcases q with ⟨u,v⟩
  dsimp only at hw ⊢
  have up : u.core.path = .some p i := (congrArg (fun x => x.2.1) hw.1).trans ha
  have us : u.core.state = .depart := (congrArg Prod.fst hw.1).trans hs
  have vs : v.core.state = .toss := (congrArg Prod.fst hw.2).trans hr
  simpa [AuthState.st, up, us, vs] using hw

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
      simp_all [V, cv, PA, av, dv, S, TokenSidecar, Prod.mk.injEq]
    · exact Or.inl (Or.inr pr)
  · exact Or.inl (Or.inl pl)

private theorem seam_next (hp : n > 0) (gB gX : ProvColor) (i j : Nat)
    (l r : AuthState n) :
    (X0Toss hp gX j r).core.label.val =
      ((BTail hp gB i l).core.label.val + 1) % n := by
  change 0 = (n - 1 + 1) % n
  have e : n - 1 + 1 = n := by omega
  rw [e, Nat.mod_self]

theorem seam_clean_split (hp : n > 0) (h2 : 2 ≤ n) (k : Nat)
    (gB gX : ProvColor) (i j : Nat) (l r : AuthState n) :
    let a := BTail hp gB i l
    let b := X0Toss hp gX j r
    let c := cut hp k a b
    PairHole c ∨ (V c.1 = V a ∧ V c.2 = V b) := by
  let a := BTail hp gB i l
  let b := X0Toss hp gX j r
  change PairHole (cut hp k a b) ∨
    (V (cut hp k a b).1 = V a ∧ V (cut hp k a b).2 = V b)
  obtain ⟨x,y,he⟩ := P0_frame hp a b rfl rfl (seam_next hp gB gX i j l r)
  have hv : V (P0 hp a b).1 = V a ∧ V (P0 hp a b).2 = V b := by
    rw [he]
    exact ⟨rfl,rfl⟩
  unfold cut
  generalize P0 hp a b = p at hv ⊢
  dsimp only
  have hg := gen_V hp k p.1 p.2 (n - 1) i
    (congrArg (fun x => x.2.1) hv.1)
    (congrArg Prod.fst hv.1) (congrArg Prod.fst hv.2)
  generalize genSigAuth hp k p.1 p.2 = q at hg ⊢
  rcases clean_V hp q.1 q.2 with hh | ⟨h0,h1⟩
  · exact Or.inl hh
  · exact Or.inr ⟨h0.trans (hg.1.trans hv.1), h1.trans (hg.2.trans hv.2)⟩

private theorem rewrap (hp : n > 0) (gB gX : ProvColor) (i j : Nat)
    (a b l r : AuthState n)
    (ha : V a = V (BTail hp gB i l)) (hb : V b = V (X0Toss hp gX j r)) :
    BTail hp gB i a = a ∧ X0Toss hp gX j b = b := by
  constructor
  · rcases a with ⟨c,pm,cm,sc,tm,m4,m5⟩
    cases c
    simp_all [V, BTail, Prod.mk.injEq]
  · rcases b with ⟨c,pm,cm,sc,tm,m4,m5⟩
    cases c
    simp_all [V, X0Toss, X0A6, Prod.mk.injEq]

-- This identity concerns the actual post-DISAPPEAR records, not X0A5's p field.
private theorem tail_exact (k : Nat) (a b : AuthState n) (i j : Nat)
    (sa : a.core.state = .depart) (sb : b.core.state = .toss_done)
    (pa : a.core.path = .some (n - 1) i) (pb : b.core.path = .some 0 j)
    (kb : b.core.label.val = 0)
    (ta : a.core.path2 = none) (tb : b.core.path2 = some A5)
    (cm : a.ctrl_mark = a.path_mark) :
    tail k a b = (a,b) := by
  have nl : liftLife (fun x => normalizeCarrier (normalizeOrphan x)) a = a := by
    cases h : a.core.leader <;>
      simp [liftLife, normalizeCarrier, normalizeOrphan, releaseCongest, h, sa, pa]
  have nr : liftLife (fun x => normalizeCarrier (normalizeOrphan x)) b = b := by
    cases h : b.core.leader <;>
      simp [liftLife, normalizeCarrier, normalizeOrphan, releaseCongest, h, sb, pb, kb]
  have er : repairAuth a b = (a,b) := by
    simp [repairAuth, nl, nr, lift2Life, releaseReadySuffix, ackTailAuth,
      lift2, ackTail, sa, sb, pa, pb, ta, tb, A5, lockedState]
  unfold tail
  rw [er]
  simp [compareLifecycleAuth, maintainAuth, completeWaveAuth, waveAuth,
    lift2, PPLLFableDesignR1.dropStray, landBackwardAuth, landForwardAuth,
    sa, sb, pa, pb, ta, tb, A5, AuthState.st, lockedState, cm]
  exact congrArg (fun m => { a with ctrl_mark := m }) cm.symm

private theorem retained_post (hp : n > 0) (h2 : 2 ≤ n) (k : Nat)
    (gB gX : ProvColor) (i j : Nat) (l r : AuthState n) :
    Post gB gX i j (B hp k (BTail hp gB i l) (X0Toss hp gX j r)) := by
  have hrel : lift2Life (releaseSource hp) (BTail hp gB i l) (X0Toss hp gX j r) =
      (BTail hp gB i l, X0Toss hp gX j r) := by
    simp [lift2Life, releaseSource, X0Toss, X0A6]
  have helim : lift2 (eliminateSig hp) (BTail hp gB i l) (X0Toss hp gX j r) =
      (BTail hp gB i l, X0Toss hp gX j r) := by
    simp [lift2, eliminateSig, X0Toss, X0A6]
  have hd := seam_retained_handoff hp h2 gB gX i j l r
  simp only [B, hrel, helim]
  dsimp only at hd ⊢
  generalize preDisappear hp cfg (BTail hp gB i l) (X0Toss hp gX j r) = q at hd ⊢
  generalize disappearAuth hp q.1 q.2 = d at hd ⊢
  simp only [V, BTail, X0A5, X0Toss, X0A6, Prod.mk.injEq] at hd
  rcases hd with ⟨⟨sa,pa,ta,_,_,_,ma,ca,_,_⟩,
    ⟨sb,pb,tb,kb,_,_,mb,cb,sc,tm⟩⟩
  have hk : d.2.core.label.val = 0 := congrArg (fun x : Fin n => x.val) kb
  rw [tail_exact k d.1 d.2 i j sa sb pa pb hk ta tb (ca.trans ma.symm)]
  simp only [Post, LV, TokenSidecar, Prod.mk.injEq]
  exact ⟨⟨sa,pa,ta,ma,ca⟩,⟨sb,pb,tb,mb,cb⟩,sc,tm⟩

private theorem seam_emitter_service_pair (hp : n > 0) (h2 : 2 ≤ n) (k : Nat)
    (gB gX : ProvColor) (i j : Nat) (l r a b : AuthState n)
    (ha : a = BTail hp gB i l) (hb : b = X0Toss hp gX j r) :
    let q := PPLLAuthF.pipeline hp k cfg a b
    Target q ∨ (Post gB gX i j q ∧
      q.1.core.label.val = n - 1 ∧ q.2.core.label.val = 0) := by
  dsimp only
  generalize hout : PPLLAuthF.pipeline hp k cfg a b = out
  have hal : a.core.leader = false := by rw [ha]; rfl
  have hbl : b.core.leader = false := by rw [hb]; rfl
  have har : a.core.reset_cmd = false := by rw [ha]; rfl
  have hbr : b.core.reset_cmd = false := by rw [hb]; rfl
  have hc : PairHole (cut hp k a b) ∨
      (V (cut hp k a b).1 = V a ∧ V (cut hp k a b).2 = V b) := by
    rw [ha,hb]
    exact seam_clean_split hp h2 k gB gX i j l r
  have ef : PPLLAuthF.pipeline hp k cfg a b =
      afterCleanToFinal hp k cfg a b (cut hp k a b).1 (cut hp k a b).2 := rfl
  have eb : beforeSuppressAuth hp k cfg a b =
      B hp k (cut hp k a b).1 (cut hp k a b).2 := rfl
  generalize cut hp k a b = c at hc ef eb
  rcases hc with hh | ⟨h0,h1⟩
  · left
    have hoH : PairHole out := by
      rw [← hout, ef]
      exact afterCleanToFinal_pairHole hp k cfg a b c.1 c.2 hh
    exact Or.inr (Or.inr hoH)
  · by_cases hr : out.2.core.leader = true
    · exact Or.inl (Or.inr (Or.inl hr))
    have hr0 : out.2.core.leader = false := by
      cases he : out.2.core.leader
      · rfl
      · exact False.elim (hr he)
    have hrp : (PPLLAuthF.pipeline hp k cfg a b).2.core.leader = false := by
      rw [hout]
      exact hr0
    have hn : b.core.label = ⟨(a.core.label.val + 1) % n, Nat.mod_lt _ hp⟩ := by
      rw [ha,hb]
      apply Fin.ext
      exact seam_next hp gB gX i j l r
    have hs := row_std hp k cfg a b hal hbl har hbr hn hrp
    rw [hout] at hs
    have he := rewrap hp gB gX i j c.1 c.2 l r
      (h0.trans (congrArg V ha)) (h1.trans (congrArg V hb))
    have hz := retained_post hp h2 k gB gX i j c.1 c.2
    rw [he.1, he.2, ← eb] at hz
    have hf := pipeline_FV hp k cfg a b hal hbl har hbr
    have ht := pipeline_tokenSidecar hp k cfg a b hal hbl har hbr
    rw [hout] at hf ht
    right
    generalize beforeSuppressAuth hp k cfg a b = z at hz hf ht
    refine ⟨?_, ?_, ?_⟩
    · simp only [Post, LV, FV, TokenSidecar, Prod.mk.injEq] at hz hf ht ⊢
      rcases hf with ⟨⟨s,p,t,_,cm,pm⟩,⟨rs,rp,rt,_,rc,rm⟩⟩
      rcases ht with ⟨_,sc,tm⟩
      rcases hz with ⟨⟨s0,p0,t0,m0,c0⟩,⟨s1,p1,t1,m1,c1⟩,sc1,tm1⟩
      exact ⟨⟨s.trans s0,p.trans p0,t.trans t0,pm.trans m0,cm.trans c0⟩,
        ⟨rs.trans s1,rp.trans p1,rt.trans t1,rm.trans m1,rc.trans c1⟩,
        sc.trans sc1,tm.trans tm1⟩
    · calc
        out.1.core.label.val = a.core.label.val := congrArg Fin.val hs.1
        _ = n - 1 := by rw [ha]; rfl
    · calc
        out.2.core.label.val = b.core.label.val := congrArg Fin.val hs.2.1
        _ = 0 := by rw [hb]; rfl

/-- One original seam service; final lottery fields remain unconstrained. -/
theorem seam_emitter_service (hp : n > 0) (h2 : 2 ≤ n) (k : Nat)
    (gB gX : ProvColor) (i j : Nat) (l r : AuthState n) :
    let q := PPLLAuthF.pipeline hp k cfg (BTail hp gB i l) (X0Toss hp gX j r)
    Target q ∨ (Post gB gX i j q ∧
      q.1.core.label.val = n - 1 ∧ q.2.core.label.val = 0) := by
  exact seam_emitter_service_pair hp h2 k gB gX i j l r
    (BTail hp gB i l) (X0Toss hp gX j r) rfl rfl

#print axioms PPLLAuthSeamEmitterService.seam_clean_split
#print axioms PPLLAuthSeamEmitterService.seam_emitter_service
end PPLLAuthSeamEmitterService
