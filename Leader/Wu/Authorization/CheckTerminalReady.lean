import Leader.Wu.Authorization.CheckTerminalConsume
import Leader.Wu.Authorization.CheckReadyStep
import Leader.Wu.Authorization.MoveHole
import Leader.Wu.Authorization.CheckSuffixPathFrame

/-!
# The first service of a terminal CHECK-ready boundary

A CLEAN deletion is retained as a final pair hole. MOVE may transfer the left
path into a right vacancy, leaving the hole at the initiator instead.
With both paths retained, carry either permits the ordinary release or leaves
the exact pending elimination consumed by the accepted next-service theorem.
This is a local original-pipeline statement, not a reachability assertion.
-/
namespace PPLLAuthCheckTerminalReady

open PPLL PPLLRepair PPLLBirthPatch PPLLBirthPatchM2 PPLLPostElectionGuard
open PPLLFableDesignR1 PPLLAstraDesign2 PPLLAstraDesign3 PPLLAuthF
open PPLLAuthF.AuthState PPLLAuthCheckComponent PPLLAuthCheckComponentFrame
open PPLLAuthCheckComponentStep PPLLAuthCheckTerminalConsume

set_option autoImplicit false
variable {ψ : Nat}

/-- Token-free own-path terminal row; right control and CLEAN/carry are free. -/
structure TerminalReady (l r : AuthState ψ) (bl br : Nat) : Prop where
  width : 2 ≤ ψ
  lk : l.core.label.val = ψ - 2
  rk : r.core.label.val = ψ - 1
  lp : l.core.path = .some (ψ - 2) bl
  rp : r.core.path = .some (ψ - 1) br
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

/- A source-level nonempty entrance: psi=2, labels 0/1, paths some 0 0 /
some 1 0, states depart/CHECK_ready, marks and control 0, both followers and
reset-free, path2/3/4/5 none, other Boolean/numeric fields false/zero. This
satisfies the local entrance; no generator reachability is asserted. -/

private def afterClean (hp : ψ > 0) (l r : AuthState ψ) : AuthState ψ × AuthState ψ :=
  let q := lift2Life (releaseSource hp) l r
  let q := lift2 (eliminateSig hp) q.1 q.2
  let q := moveSourceAuth hp cfg q.1 q.2
  let q := (liftLife dropStale q.1, liftLife dropStale q.2)
  let q := preCheckResetAuth q.1 q.2
  (liftLife normalizeReady q.1, liftLife normalizeReady q.2)

private theorem restPair_eq (hp : ψ > 0) (κ : Nat) (l r : AuthState ψ) :
    PPLLAuthGenDrain.restPair hp κ cfg (l,r) =
      let c := cleanSourceAuth hp cfg l r
      let a := afterClean hp c.1 c.2
      checkSuffix hp κ a.1 a.2 := rfl

private theorem gen_ready (hp : ψ > 0) (κ : Nat) (l r : AuthState ψ)
    (bl br : Nat) (h : TerminalReady l r bl br) :
    genSigAuth hp κ l r = lift2 (waitSaturated hp κ) l r := by
  have hw := PPLLAuthGenDrain.W_fields hp κ l r
  rcases hw with ⟨a1,a2,a3,a4,a5,a6,a7,b1,b2,b3,b4,b5,b6,b7⟩
  unfold genSigAuth
  generalize lift2 (waitSaturated hp κ) l r = q at a1 a2 a3 a4 a5 a6 a7 b1 b2 b3 b4 b5 b6 b7 ⊢
  rcases q with ⟨a,b⟩
  simp only at a1 a2 a3 a4 a5 a6 a7 b1 b2 b3 b4 b5 b6 b7
  simp [AuthState.st, a1, a2, b1, h.lp, h.ls, h.rs]

/-- WAIT preserves the entrance, including reset-free inputs, even though
its own counters and carry fields are unrestricted. -/
private theorem wait_ready (hp : ψ > 0) (κ : Nat) (l r : AuthState ψ)
    (bl br : Nat) (h : TerminalReady l r bl br) :
    TerminalReady (lift2 (waitSaturated hp κ) l r).1
      (lift2 (waitSaturated hp κ) l r).2 bl br := by
  have hw := PPLLAuthGenDrain.W_fields hp κ l r
  have hd := PPLLAuthResetDrain.wait_dv hp κ l.core r.core
  simp only [PPLLAuthResetDrain.dv, Prod.mk.injEq] at hd
  rcases hw with ⟨a1,a2,a3,a4,a5,a6,a7,b1,b2,b3,b4,b5,b6,b7⟩
  rcases hd with ⟨⟨ar,_,_,_⟩,⟨brs,_,_,_⟩⟩
  constructor <;> simp_all [h.width,h.lk,h.rk,h.lp,h.rp,h.ls,h.rs,
    h.lt,h.rt,h.ll,h.rl,h.lr,h.rr,h.pm,h.cm,lift2]

/-- Restoring paths is used only to state CLEAN's preserved non-path frame. -/
private def restore (u : AuthState ψ) (k bit : Nat) : AuthState ψ :=
  {u with core := {u.core with path := .some k bit}}

private theorem clean_cut (hp : ψ > 0) (l r : AuthState ψ)
    (bl br : Nat) (h : TerminalReady l r bl br) :
    let q := cleanSourceAuth hp cfg l r
    TerminalReady (restore q.1 (ψ-2) bl) (restore q.2 (ψ-1) br) bl br ∧
      (q.1.core.path = l.core.path ∨ q.1.core.path = .bot) ∧
      (q.2.core.path = r.core.path ∨ q.2.core.path = .bot) := by
  have hv := PPLLAuthGenDrain.T1_cv hp cfg (l,r)
  have ha := PPLLAuthGenDrain.T1_pa hp cfg (l,r)
  simp only [PPLLAuthGenDrain.T1] at hv ha
  rcases hv with ⟨vl,vr,pl,pr⟩
  simp only [PPLLAuthGenDrain.cv,Prod.mk.injEq] at vl vr
  simp only [PPLLAuthGenDrain.PA,PPLLAuthResetDrain.av,PPLLAuthResetDrain.dv,
    Prod.mk.injEq] at ha
  rcases vl with ⟨a1,a2,a3,a4,a5⟩
  rcases vr with ⟨b1,b2,b3,b4,b5⟩
  rcases ha with ⟨⟨a6,_,a7,a8⟩,⟨b6,_,b7,b8⟩⟩
  refine ⟨?_,pl,pr⟩
  constructor <;> simp_all [restore,h.width,h.lk,h.rk,h.ls,h.rs,h.lt,h.rt,
    h.ll,h.rl,h.lr,h.rr,h.pm,h.cm]

private theorem afterClean_ready (hp : ψ > 0) (l r : AuthState ψ)
    (bl br : Nat) (h : TerminalReady l r bl br) : afterClean hp l r = (l,r) := by
  have hr0 : ψ - 1 ≠ 0 := by have := h.width; omega
  have hm : moveSourceAuth hp cfg l r = (l,r) := by
    simp [moveSourceAuth,validateCheck,headBad,checkState,verdict,isHead,aligned,
      sanitizeP2,p2Valid,step1Auth,moveTokensAuth,leaderWallAuth,applyControlAuth,
      AuthState.st,h.lp,h.rp,h.lk,h.rk,h.ls,h.rs,h.lt,h.rt,h.ll,h.rl,hr0]
  simp only [afterClean,lift2Life,releaseSource,h.rs,h.ls]
  simp [lift2,eliminateSig,h.rs,hm,liftLife,dropStale,aligned,
    preCheckResetAuth,normalizeReady,normalizeOrphan,normalizeCarrier,releaseCongest,
    h.ll,h.rl,h.lr,h.rr,h.lp,h.rp,h.lk,h.rk,h.ls,h.rs]

private theorem check_ready (hp : ψ > 0) (l r : AuthState ψ)
    (bl br : Nat) (h : TerminalReady l r bl br) : checkSourceAuth hp cfg l r = (l,r) := by
  have hr0 : ψ - 1 ≠ 0 := by have := h.width; omega
  have hvl : validateCheck l r = (l,r) := by
    simp [validateCheck,headBad,checkState,verdict,isHead,h.rk,hr0,AuthState.st,h.ls,h.rs]
  have hreadyL : readyAuth l = l := by
    simp [readyAuth,waveState,checkSigSetReadyGuarded,controlPending,
      checkSigSetReady,AuthState.st,h.lp,h.lt,h.ls]
  have hreadyR : readyAuth r = r := by
    have hu : {r.core with state := .CHECK_ready} = r.core := by rw [← h.rs]
    simp [readyAuth,waveState,checkSigSetReadyGuarded,controlPending,
      checkSigSetReady,AuthState.st,h.rp,h.rt,h.rs,h.rk,hu]
    rw [← h.rp,← h.rt,← h.rs]
  have hL : checkSigCheckL hp l.core = l.core := by
    cases hk : ψ - 2 <;> simp [checkSigCheckL,h.lp,hk,h.ls]
  have hc : certPred l r = false := by simp [certPred,h.lp,h.rp,AuthState.st,h.ls]
  have hiL : issue l = l := by simp [issue,AuthState.st,h.ls]
  have hiR : issue r = r := by simp [issue,AuthState.st,h.rs]
  simp [checkSourceAuth,cfg,hvl,hreadyL,hreadyR,AuthState.st,h.rs,hL,
    AuthState.withCore,hc,hiL,hiR]

/-- Pending comparison fields; labels/reset/followers are added at the final row. -/
private def PendingFields (l r : AuthState ψ) (q : AuthState ψ × AuthState ψ) : Prop :=
  q.1.core.state = .depart ∧ q.2.core.state = .eliminate_signal ∧
  q.1.core.path = l.core.path ∧ q.2.core.path = r.core.path ∧
  q.1.core.path2 = none ∧ q.2.core.path2 = none ∧
  q.1.ctrl_mark = q.1.path_mark ∧
  q.1.path_mark = l.path_mark ∧ q.2.path_mark = r.path_mark

private theorem suffix_ready (hp : ψ > 0) (κ : Nat) (l r : AuthState ψ)
    (bl br : Nat) (h : TerminalReady l r bl br) :
    Released l r (checkSuffix hp κ l r) ∨ PendingFields l r (checkSuffix hp κ l r) := by
  have hk : ψ - 2 + 1 = ψ - 1 := by have := h.width; omega
  have hn : ψ - 2 ≠ ψ - 1 := by have := h.width; omega
  have hr0 : ψ - 1 ≠ 0 := by have := h.width; omega
  have hrt : r.core.label = (⟨ψ-1,by omega⟩ : Fin ψ) := Fin.ext h.rk
  unfold checkSuffix
  rw [check_ready hp l r bl br h]
  cases hc : l.core.p_carry <;> cases hb : r.core.p <;>
    simp [Released,PendingFields,disappearAuth,disappearStartL,disappearCarry,lift2,
      repairAuth,liftLife,normalizeOrphan,normalizeCarrier,releaseCongest,
      lift2Life,releaseReadySuffix,ackTailAuth,ackTail,lockedState,
      compareLifecycleAuth,maintainAuth,completeWaveAuth,waveAuth,
      PPLLFableDesignR1.dropStray,landBackwardAuth,landForwardAuth,
      AuthState.st,AuthState.setState,AuthState.withCore,AuthState.lineage,
      h.lp,h.rp,h.lk,h.rk,h.ls,h.rs,h.lt,h.rt,h.ll,h.rl,h.cm,h.pm,hc,hb,hrt,hk,hn,hr0]

private theorem fst_ite {α β : Type} (p : Prop) [Decidable p] (a b : α × β) :
    (if p then a else b).1 = if p then a.1 else b.1 := by
  split <;> rfl

private theorem snd_ite {α β : Type} (p : Prop) [Decidable p] (a b : α × β) :
    (if p then a else b).2 = if p then a.2 else b.2 := by
  split <;> rfl

private theorem path_ite (p : Prop) [Decidable p] (a b : AgentState ψ) :
    (if p then a else b).path = if p then a.path else b.path := by
  split <;> rfl

private theorem core_ite (p : Prop) [Decidable p] (a b : AuthState ψ) :
    (if p then a else b).core = if p then a.core else b.core := by
  split <;> rfl

private theorem pairHole_of_paths
    (q : AuthState ψ × AuthState ψ) (l r : AuthState ψ)
    (hp : q.1.core.path = l.core.path ∧ q.2.core.path = r.core.path)
    (h : PairHole (l, r)) : PairHole q := by
  unfold PairHole at h ⊢
  rw [hp.1, hp.2]
  exact h

private theorem clearCmpAuth_path' (u : AuthState ψ) :
    (clearCmpAuth u).core.path = .bot := by
  simp [clearCmpAuth, PPLLPostElectionGuard.clearCmp]

private theorem lift2_paths
    (f : AgentState ψ → AgentState ψ → AgentState ψ × AgentState ψ)
    (hf : ∀ a b, (f a b).1.path = a.path ∧ (f a b).2.path = b.path)
    (l r : AuthState ψ) :
    (lift2 f l r).1.core.path = l.core.path ∧
      (lift2 f l r).2.core.path = r.core.path :=
  hf l.core r.core

private theorem lift2Life_paths
    (f : AgentState ψ → AgentState ψ → AgentState ψ × AgentState ψ)
    (hf : ∀ a b, (f a b).1.path = a.path ∧ (f a b).2.path = b.path)
    (l r : AuthState ψ) :
    (lift2Life f l r).1.core.path = l.core.path ∧
      (lift2Life f l r).2.core.path = r.core.path := by
  have h := hf l.core r.core
  unfold lift2Life
  dsimp only
  constructor <;> split <;> simp only [h]

private theorem liftLife_path
    (f : AgentState ψ → AgentState ψ)
    (hf : ∀ a, (f a).path = a.path) (u : AuthState ψ) :
    (liftLife f u).core.path = u.core.path := by
  unfold liftLife
  dsimp only
  split <;> exact hf u.core

private theorem lift2_pairHole_of_paths
    (f : AgentState ψ → AgentState ψ → AgentState ψ × AgentState ψ)
    (hf : ∀ a b, (f a b).1.path = a.path ∧ (f a b).2.path = b.path)
    (l r : AuthState ψ) (h : PairHole (l, r)) :
    PairHole (lift2 f l r) :=
  pairHole_of_paths _ l r (lift2_paths f hf l r) h

private theorem releaseSource_paths (hψ : ψ > 0) (l r : AgentState ψ) :
    (releaseSource hψ l r).1.path = l.path ∧
      (releaseSource hψ l r).2.path = r.path := by
  simp [releaseSource, fst_ite, snd_ite, path_ite]

private theorem release_pairHole (hψ : ψ > 0) (l r : AuthState ψ)
    (h : PairHole (l, r)) :
    PairHole (lift2Life (releaseSource hψ) l r) :=
  pairHole_of_paths _ l r
    (lift2Life_paths (releaseSource hψ) (releaseSource_paths hψ) l r) h

private theorem eliminateSig_left_path (hψ : ψ > 0) (l r : AgentState ψ) :
    (eliminateSig hψ l r).1.path = l.path := by
  simp [eliminateSig, fst_ite, path_ite]

private theorem eliminateSig_right_bot (hψ : ψ > 0) (l r : AgentState ψ)
    (hr : r.path = .bot) :
    (eliminateSig hψ l r).2.path = .bot := by
  simp [eliminateSig, snd_ite, path_ite, hr]

private theorem eliminate_pairHole (hψ : ψ > 0) (l r : AuthState ψ)
    (h : PairHole (l, r)) :
    PairHole (lift2 (eliminateSig hψ) l r) := by
  unfold PairHole at h ⊢
  change l.core.path = .bot ∨ r.core.path = .bot at h
  rcases h with hl | hr
  · left
    change (eliminateSig hψ l.core r.core).1.path = .bot
    exact (eliminateSig_left_path hψ l.core r.core).trans hl
  · right
    change (eliminateSig hψ l.core r.core).2.path = .bot
    exact eliminateSig_right_bot hψ l.core r.core hr

private theorem dropStale_bot (u : AgentState ψ) (h : u.path = .bot) :
    (dropStale u).path = .bot := by
  simp [dropStale, h]

private theorem liftLife_dropStale_bot (u : AuthState ψ)
    (h : u.core.path = .bot) :
    (liftLife dropStale u).core.path = .bot := by
  unfold liftLife
  dsimp only
  split <;> exact dropStale_bot u.core h

private theorem dropStale_pairHole (l r : AuthState ψ)
    (h : PairHole (l, r)) :
    PairHole (liftLife dropStale l, liftLife dropStale r) := by
  unfold PairHole at h ⊢
  change l.core.path = .bot ∨ r.core.path = .bot at h
  rcases h with hl | hr
  · exact Or.inl (liftLife_dropStale_bot l hl)
  · exact Or.inr (liftLife_dropStale_bot r hr)

private theorem preCheckReset_pairHole (l r : AuthState ψ)
    (h : PairHole (l, r)) :
    PairHole (preCheckResetAuth l r) := by
  unfold PairHole at h ⊢
  change l.core.path = .bot ∨ r.core.path = .bot at h
  rcases h with hl | hr
  · left
    simp [preCheckResetAuth, clearCmpAuth_path', core_ite, path_ite, hl]
  · right
    simp [preCheckResetAuth, clearCmpAuth_path', core_ite, path_ite, hr]

private theorem orphan_path_local (u : AgentState ψ) :
    (normalizeOrphan u).path = u.path := by
  cases h : u.path <;> simp [normalizeOrphan, h, path_ite]

private theorem carrier_path_local (u : AgentState ψ) :
    (normalizeCarrier u).path = u.path := by
  cases h : u.path <;>
    simp [normalizeCarrier, releaseCongest, h, path_ite]

private theorem normalizeReady_path_local (u : AgentState ψ) :
    (normalizeReady u).path = u.path := by
  cases h : u.path <;>
    simp [normalizeReady, path_ite, orphan_path_local, carrier_path_local, h]

private theorem normalizeReady_pairHole (l r : AuthState ψ)
    (h : PairHole (l, r)) :
    PairHole (liftLife normalizeReady l, liftLife normalizeReady r) :=
  pairHole_of_paths _ l r
    ⟨liftLife_path normalizeReady normalizeReady_path_local l,
      liftLife_path normalizeReady normalizeReady_path_local r⟩ h

private theorem checkSuffix_eq (hp : ψ > 0) (κ : Nat) (u v : AuthState ψ) :
    checkSuffix hp κ u v =
      PPLLAuthCheckSuffixPathFrame.checkSuffixC hp κ cfg u v := rfl

private theorem checkSuffix_pairHole
    (hp : ψ > 0) (κ : Nat)
    (l r : AuthState ψ) (h : PairHole (l, r)) :
    PairHole (checkSuffix hp κ l r) := by
  rw [checkSuffix_eq]
  exact pairHole_of_paths _ l r
    (PPLLAuthCheckSuffixPathFrame.checkSuffixC_path hp κ cfg l r) h

/-- An arbitrary pair hole survives the literal T2--T7 prefix.
MOVE may move the hole between endpoints; no state/token bundle is needed. -/
private theorem afterClean_pairHole (hp : ψ > 0) (l r : AuthState ψ)
    (h : PairHole (l,r)) : PairHole (afterClean hp l r) := by
  unfold afterClean
  have h2 := release_pairHole hp l r h
  generalize lift2Life (releaseSource hp) l r = q2 at h2 ⊢
  rcases q2 with ⟨l2,r2⟩
  dsimp only at h2 ⊢
  have h3 := eliminate_pairHole hp l2 r2 h2
  generalize lift2 (eliminateSig hp) l2 r2 = q3 at h3 ⊢
  rcases q3 with ⟨l3,r3⟩
  dsimp only at h3 ⊢
  have h4 : PairHole (moveSourceAuth hp cfg l3 r3) :=
    PPLLAuthFPairHole.moveSourceAuth_pairHole hp cfg l3 r3 h3
  generalize moveSourceAuth hp cfg l3 r3 = q4 at h4 ⊢
  rcases q4 with ⟨l4,r4⟩
  dsimp only at h4 ⊢
  have h5 := dropStale_pairHole l4 r4 h4
  have h6 := preCheckReset_pairHole (liftLife dropStale l4) (liftLife dropStale r4) h5
  generalize preCheckResetAuth (liftLife dropStale l4) (liftLife dropStale r4) = q6 at h6 ⊢
  rcases q6 with ⟨l6,r6⟩
  exact normalizeReady_pairHole l6 r6 h6

/-- CLEAN's four path outcomes reduce to generic pair-hole transport or the
retained-path carry split. Old CLEAN records are never enumerated. -/
private theorem rest_ready (hp : ψ > 0) (κ : Nat) (l r : AuthState ψ)
    (bl br : Nat) (h : TerminalReady l r bl br) :
    let q := PPLLAuthGenDrain.restPair hp κ cfg (l,r)
    PairHole q ∨ Released l r q ∨ PendingFields l r q := by
  obtain ⟨hc,hl,hr⟩ := clean_cut hp l r bl br h
  have hv := PPLLAuthGenDrain.T1_cv hp cfg (l,r)
  have hmL : (cleanSourceAuth hp cfg l r).1.path_mark = l.path_mark :=
    congrArg (fun z => z.2.2.2.2) hv.1
  have hmR : (cleanSourceAuth hp cfg l r).2.path_mark = r.path_mark :=
    congrArg (fun z => z.2.2.2.2) hv.2.1
  rw [restPair_eq]
  generalize hclean : cleanSourceAuth hp cfg l r = c at hc hl hr hmL hmR ⊢
  rcases c with ⟨cl,cr⟩
  dsimp only at hc hl hr hmL hmR ⊢
  by_cases hh : cl.core.path = .bot ∨ cr.core.path = .bot
  · have ha := afterClean_pairHole hp cl cr hh
    generalize hafter : afterClean hp cl cr = a at ha ⊢
    rcases a with ⟨al,ar⟩
    exact Or.inl (checkSuffix_pairHole hp κ al ar ha)
  · have hlp : cl.core.path = l.core.path := hl.resolve_right (fun he => hh (Or.inl he))
    have hrp : cr.core.path = r.core.path := hr.resolve_right (fun he => hh (Or.inr he))
    have hlc : restore cl (ψ-2) bl = cl := by
      unfold restore; rw [← h.lp,← hlp]
    have hrc : restore cr (ψ-1) br = cr := by
      unfold restore; rw [← h.rp,← hrp]
    rw [hlc,hrc] at hc
    rw [afterClean_ready hp cl cr bl br hc]
    right
    rcases suffix_ready hp κ cl cr bl br hc with hd | he
    · left; simpa only [Released,hlp,hrp,hmL,hmR] using hd
    · right; simpa only [PendingFields,hlp,hrp,hmL,hmR] using he

/-- The full original row gives a target, exact released endpoints, or the
comparison-field portion of the accepted pending terminal consumer. -/
private theorem pipeline_ready_fields (hp : ψ > 0) (κ : Nat) (l r : AuthState ψ)
    (bl br : Nat) (h : TerminalReady l r bl br) :
    let q := PPLLAuthF.pipeline hp κ cfg l r
    PairHole q ∨ Released l r q ∨ PendingFields l r q := by
  have hk : ψ - 2 + 1 = ψ - 1 := by have := h.width; omega
  have row : PPLLAuthGenDrain.RowH ψ l r (ψ-2) := by
    refine ⟨h.lk,?_,?_,h.ll,h.rl,h.lr,h.rr⟩
    · rw [hk]; exact h.rk
    · omega
  obtain ⟨x,y,hf1,hf2⟩ := PPLLAuthGenDrain.row_open hp κ cfg l r (ψ-2) row
  let a := PPLLAuthGenDrain.withProbe l x
  let b := PPLLAuthGenDrain.withProbe r y
  have hab : TerminalReady a b bl br := by
    constructor <;> simp [a,b,PPLLAuthGenDrain.withProbe,h.width,h.lk,h.rk,
      h.lp,h.rp,h.ls,h.rs,h.lt,h.rt,h.ll,h.rl,h.lr,h.rr,h.pm,h.cm]
  have hg := gen_ready hp κ a b bl br hab
  have hw := wait_ready hp κ a b bl br hab
  have wmL : (lift2 (waitSaturated hp κ) a b).1.path_mark = l.path_mark := by
    simp [a,lift2,PPLLAuthGenDrain.withProbe]
  have wmR : (lift2 (waitSaturated hp κ) a b).2.path_mark = r.path_mark := by
    simp [b,lift2,PPLLAuthGenDrain.withProbe]
  generalize hwdef : lift2 (waitSaturated hp κ) a b = w at hg hw wmL wmR
  rcases w with ⟨wl,wr⟩
  change wl.path_mark = l.path_mark at wmL
  change wr.path_mark = r.path_mark at wmR
  have hs := rest_ready hp κ wl wr bl br hw
  change PPLLAuthGenDrain.FV (PPLLAuthF.pipeline hp κ cfg l r).1 =
    PPLLAuthGenDrain.FV (PPLLAuthGenDrain.restPair hp κ cfg (genSigAuth hp κ a b)).1 at hf1
  change PPLLAuthGenDrain.FV (PPLLAuthF.pipeline hp κ cfg l r).2 =
    PPLLAuthGenDrain.FV (PPLLAuthGenDrain.restPair hp κ cfg (genSigAuth hp κ a b)).2 at hf2
  rw [hg] at hf1 hf2
  have wpL : wl.core.path = l.core.path := hw.lp.trans h.lp.symm
  have wpR : wr.core.path = r.core.path := hw.rp.trans h.rp.symm
  generalize hout : PPLLAuthF.pipeline hp κ cfg l r = out at hf1 hf2 ⊢
  generalize hrest : PPLLAuthGenDrain.restPair hp κ cfg (wl,wr) = rest at hf1 hf2 hs
  have sl := PPLLAuthGenDrain.FV_state hf1
  have sr := PPLLAuthGenDrain.FV_state hf2
  have pl := PPLLAuthGenDrain.FV_path hf1
  have pr := PPLLAuthGenDrain.FV_path hf2
  have tl := PPLLAuthGenDrain.FV_path2 hf1
  have tr := PPLLAuthGenDrain.FV_path2 hf2
  have cl := PPLLAuthGenDrain.FV_ctrl hf1
  have cr := PPLLAuthGenDrain.FV_ctrl hf2
  have ml := PPLLAuthGenDrain.FV_pm hf1
  have mr := PPLLAuthGenDrain.FV_pm hf2
  simpa only [PairHole,Released,PendingFields,sl,sr,pl,pr,tl,tr,cl,cr,ml,mr,
    wpL,wpR,wmL,wmR] using hs

/-- First terminal service: the pending branch includes every final label,
reset and follower fact needed to apply the accepted same-edge consumer. -/
theorem terminal_ready_step (hp : ψ > 0) (κ : Nat) (l r : AuthState ψ)
    (bl br : Nat) (h : TerminalReady l r bl br) :
    let q := PPLLAuthF.pipeline hp κ cfg l r
    Target q ∨ Continuing l r q ∨ TerminalPending q.1 q.2 bl br := by
  let q := PPLLAuthF.pipeline hp κ cfg l r
  by_cases hl : q.1.core.leader = true
  · exact Or.inl (Or.inl hl)
  by_cases hr : q.2.core.leader = true
  · exact Or.inl (Or.inr (Or.inl hr))
  have hlf : q.1.core.leader = false := by cases he : q.1.core.leader <;> simp_all
  have hrf : q.2.core.leader = false := by cases he : q.2.core.leader <;> simp_all
  have hk : ψ - 2 + 1 = ψ - 1 := by have := h.width; omega
  have hn : r.core.label = ⟨(l.core.label.val+1)%ψ,Nat.mod_lt _ hp⟩ := by
    apply Fin.ext
    change r.core.label.val = (l.core.label.val+1)%ψ
    rw [h.lk,h.rk,hk,Nat.mod_eq_of_lt (by have := h.width; omega)]
  have hs := PPLLAuthGenDrain.row_std hp κ cfg l r h.ll h.rl h.lr h.rr hn hrf
  rcases pipeline_ready_fields hp κ l r bl br h with hh | hd | he
  · exact Or.inl (Or.inr (Or.inr hh))
  · exact Or.inr (Or.inl ⟨hd,hs.1,hs.2.1,hs.2.2.1,hs.2.2.2,hlf,hrf⟩)
  · rcases he with ⟨ls,rs,lp,rp,lt,rt,cm,lm,rm⟩
    right; right
    refine ⟨h.width,?_,?_,lp.trans h.lp,rp.trans h.rp,ls,rs,lt,rt,
      hlf,hrf,hs.2.2.1,hs.2.2.2,?_,cm⟩
    · exact (congrArg Fin.val hs.1).trans h.lk
    · exact (congrArg Fin.val hs.2.1).trans h.rk
    · exact rm.trans (h.pm.trans lm.symm)

#print axioms terminal_ready_step
end PPLLAuthCheckTerminalReady
