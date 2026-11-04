import Leader.Wu.Authorization.CheckReadyCleanFrame

/-!
# Consuming a pending terminal elimination on its incoming edge

This file treats only the second service of a terminal incoming edge: the
initiator is `depart` and the responder already holds `eliminate_signal`.
It does not prove the first-service CHECK-ready trichotomy or a component
scheduling theorem. All transitions are the original `authFplusmcc` pipeline.

Algorithm 9 deletes the responder's path and propagates `eliminate_signal`
left. The F1 `outcomePending` guard then prevents SIGMOVE from refilling that
hole in the same interaction. CLEAN may already have deleted either path;
its field frame suffices, without enumerating old CLEAN records. The final
claim uses `row_open`/`pipeline_FV`, including the K4 and WRITE suffix.

The entrance is nonempty at the source level already for psi = 2: take
physical/path labels 0 and 1, path payloads 0, states depart/eliminate_signal,
false leader/reset bits, empty path2/3/4/5, and path/control marks 0. All other
Boolean and numeric registers may be false/zero and writer state/action none.
The theorem leaves CLEAN, lottery, writer, echo and right control arbitrary.
-/

namespace PPLLAuthCheckTerminalConsume

open PPLL PPLLRepair PPLLBirthPatch PPLLBirthPatchM2 PPLLPostElectionGuard
open PPLLFableDesignR1 PPLLAstraDesign2 PPLLAstraDesign3 PPLLAuthF
open PPLLAuthF.AuthState PPLLAuthCheckComponent

set_option autoImplicit false

variable {ψ : Nat}

/-- The pending terminal row delivered by the carry branch, together with
the standing label/reset facts needed to service the same edge again.
No premise is imposed on the old CLEAN records or responder control mark. -/
structure TerminalPending (l r : AuthState ψ) (bl br : Nat) : Prop where
  width : 2 ≤ ψ
  lk : l.core.label.val = ψ - 2
  rk : r.core.label.val = ψ - 1
  lp : l.core.path = .some (ψ - 2) bl
  rp : r.core.path = .some (ψ - 1) br
  ls : l.core.state = .depart
  rs : r.core.state = .eliminate_signal
  lt : l.core.path2 = none
  rt : r.core.path2 = none
  ll : l.core.leader = false
  rl : r.core.leader = false
  lr : l.core.reset_cmd = false
  rr : r.core.reset_cmd = false
  pm : r.path_mark = l.path_mark
  cm : l.ctrl_mark = l.path_mark

/-- The weaker cut after CLEAN: deletion may have removed either path,
but the pending elimination and the fields it needs survive. -/
private structure PendingCut (l r : AuthState ψ) : Prop where
  nonterminal : l.core.label.val ≠ ψ - 1
  terminal : r.core.label.val = ψ - 1
  ls : l.core.state = .depart
  rs : r.core.state = .eliminate_signal
  lt : l.core.path2 = none
  rt : r.core.path2 = none
  ll : l.core.leader = false
  rl : r.core.leader = false
  lr : l.core.reset_cmd = false
  rr : r.core.reset_cmd = false

/-- GENSIG cannot overwrite an occupied departing source or its pending
terminal responder. Its only activity on this row is WAIT bookkeeping. -/
private theorem gen_pending (hp : ψ > 0) (κ : Nat) (l r : AuthState ψ)
    (bl br : Nat) (h : TerminalPending l r bl br) :
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
private theorem wait_pending (hp : ψ > 0) (κ : Nat) (l r : AuthState ψ)
    (bl br : Nat) (h : TerminalPending l r bl br) :
    TerminalPending (lift2 (waitSaturated hp κ) l r).1
      (lift2 (waitSaturated hp κ) l r).2 bl br := by
  have hw := PPLLAuthGenDrain.W_fields hp κ l r
  have hd := PPLLAuthResetDrain.wait_dv hp κ l.core r.core
  simp only [PPLLAuthResetDrain.dv, Prod.mk.injEq] at hd
  rcases hw with ⟨a1,a2,a3,a4,a5,a6,a7,b1,b2,b3,b4,b5,b6,b7⟩
  rcases hd with ⟨⟨ar,_,_,_⟩,⟨brs,_,_,_⟩⟩
  constructor <;> simp_all [h.width,h.lk,h.rk,h.lp,h.rp,h.ls,h.rs,
    h.lt,h.rt,h.ll,h.rl,h.lr,h.rr,h.pm,h.cm,lift2]

/-- CLEAN's existing field frame supplies the pending cut. No preservation
of either path is assumed: the next stage deletes the responder in any case. -/
private theorem clean_pending (hp : ψ > 0) (l r : AuthState ψ)
    (bl br : Nat) (h : TerminalPending l r bl br) :
    PendingCut (cleanSourceAuth hp cfg l r).1 (cleanSourceAuth hp cfg l r).2 := by
  have hv := PPLLAuthGenDrain.T1_cv hp cfg (l,r)
  have ha := PPLLAuthGenDrain.T1_pa hp cfg (l,r)
  simp only [PPLLAuthGenDrain.T1] at hv ha
  rcases hv with ⟨vl,vr,_,_⟩
  simp only [PPLLAuthGenDrain.cv, Prod.mk.injEq] at vl vr
  simp only [PPLLAuthGenDrain.PA,PPLLAuthResetDrain.av,PPLLAuthResetDrain.dv,
    Prod.mk.injEq] at ha
  rcases vl with ⟨a1,a2,a3,a4,a5⟩
  rcases vr with ⟨b1,b2,b3,b4,b5⟩
  rcases ha with ⟨⟨a6,_,a7,a8⟩,⟨b6,_,b7,b8⟩⟩
  have hn : l.core.label.val ≠ ψ - 1 := by rw [h.lk]; have := h.width; omega
  constructor <;> simp_all [h.rk,h.ls,h.rs,h.lt,h.rt,h.ll,h.rl,h.lr,h.rr]

/-- The exact pair immediately after consuming the pending signal. The
initiator retains whichever path survived CLEAN; the responder is empty. -/
private def consumed (l r : AuthState ψ) : AuthState ψ × AuthState ψ :=
  ({l with core := {l.core with state := .eliminate_signal}},
   {r with core := {r.core with path := .bot, state := .none}})

/-- Stages between CLEAN and CHECK, matching the original pipeline order. -/
private def afterClean (hp : ψ > 0) (l r : AuthState ψ) : AuthState ψ × AuthState ψ :=
  let q := lift2Life (releaseSource hp) l r
  let q := lift2 (eliminateSig hp) q.1 q.2
  let q := moveSourceAuth hp cfg q.1 q.2
  let q := (liftLife dropStale q.1, liftLife dropStale q.2)
  let q := preCheckResetAuth q.1 q.2
  (liftLife normalizeReady q.1, liftLife normalizeReady q.2)

/-- The propagated elimination blocks refilling the right hole. This is the
F1 guard `outcomePending`, rather than a general path-count monotonicity claim. -/
private theorem afterClean_consumed (hp : ψ > 0) (l r : AuthState ψ)
    (h : PendingCut l r) : afterClean hp l r = consumed l r := by
  have hn : l.core.label ≠ (⟨ψ - 1, by omega⟩ : Fin ψ) := by
    intro he
    exact h.nonterminal (congrArg Fin.val he)
  cases hlp : l.core.path <;>
    simp [afterClean,consumed,lift2Life,releaseSource,lift2,eliminateSig,
      moveSourceAuth,validateCheck,headBad,checkState,verdict,isHead,
      sanitizeP2,p2Valid,step1Auth,blockingState,PPLLFableZDiv.outcomePending,
      moveTokensAuth,leaderWallAuth,applyControlAuth,liftLife,dropStale,aligned,
      preCheckResetAuth,normalizeReady,normalizeOrphan,normalizeCarrier,releaseCongest,
      AuthState.st,h.ls,h.rs,h.lt,h.rt,h.ll,h.rl,h.lr,h.rr,hn,hlp]

/-- The head-only CHECK matcher leaves a pending elimination untouched,
including when its arbitrary surviving path has label zero. -/
private theorem checkL_eliminate (hp : ψ > 0) (u : AgentState ψ)
    (hs : u.state = .eliminate_signal) : checkSigCheckL hp u = u := by
  cases ht : u.path with
  | bot => simp [checkSigCheckL,ht]
  | some n b => cases n <;> simp [checkSigCheckL,ht,hs]

/-- On the consumed pair CHECK has no path at the responder and cannot
turn the initiator's protected elimination state into a ready head. -/
private theorem check_consumed (hp : ψ > 0) (l r : AuthState ψ)
    (h : PendingCut l r) :
    checkSourceAuth hp cfg (consumed l r).1 (consumed l r).2 = consumed l r := by
  cases hlp : l.core.path <;>
    simp [consumed,checkSourceAuth,cfg,validateCheck,headBad,checkState,verdict,
      isHead,readyAuth,waveState,checkSigSetReadyGuarded,controlPending,
      checkSigSetReady,checkL_eliminate,certPred,issue,aligned,AuthState.st,
      AuthState.withCore,
      h.lt,h.rt,hlp]

/-- The suffix may change control states or lottery bits, but cannot refill
the empty responder. Empty tokens keep both comparison readers inactive. -/
private theorem suffix_consumed_hole (hp : ψ > 0) (κ : Nat) (l r : AuthState ψ)
    (h : PendingCut l r) :
    (checkSuffix hp κ (consumed l r).1 (consumed l r).2).2.core.path = .bot := by
  have hrt : r.core.label = (⟨ψ - 1, by omega⟩ : Fin ψ) := Fin.ext h.terminal
  unfold checkSuffix
  rw [check_consumed hp l r h]
  cases hlp : l.core.path <;>
    cases hc : l.core.p_carry <;> cases hrp : r.core.p <;>
    simp [consumed,disappearAuth,disappearStartL,disappearCarry,lift2,
      repairAuth,liftLife,normalizeOrphan,normalizeCarrier,releaseCongest,
      lift2Life,releaseReadySuffix,ackTailAuth,ackTail,
      compareLifecycleAuth,maintainAuth,completeWaveAuth,waveAuth,
      lockedState,lockerState,waveState,PPLLFableDesignR1.dropStray,
      landBackwardAuth,landForwardAuth,AuthState.st,AuthState.setState,
      AuthState.withCore,AuthState.lineage,h.lt,h.rt,h.ll,h.rl,hlp,hc,hrp,hrt]

/-- Reassociation only: the accepted stage decomposition and the local
after-CLEAN cut denote the same CHECK-to-COMPARE prefix. -/
private theorem restPair_eq (hp : ψ > 0) (κ : Nat) (l r : AuthState ψ) :
    PPLLAuthGenDrain.restPair hp κ cfg (l,r) =
      let c := cleanSourceAuth hp cfg l r
      let a := afterClean hp c.1 c.2
      checkSuffix hp κ a.1 a.2 := by rfl

/-- The original prefix after GENSIG consumes the terminal elimination,
with arbitrary CLEAN records handled through their existing field frame. -/
private theorem rest_pending_hole (hp : ψ > 0) (κ : Nat) (l r : AuthState ψ)
    (bl br : Nat) (h : TerminalPending l r bl br) :
    (PPLLAuthGenDrain.restPair hp κ cfg (l,r)).2.core.path = .bot := by
  rw [restPair_eq]
  dsimp only
  have hc := clean_pending hp l r bl br h
  rw [afterClean_consumed hp _ _ hc]
  exact suffix_consumed_hole hp κ _ _ hc

/-- One further service of the same terminal incoming edge consumes its
pending elimination and leaves an actual right main-path hole in the full
original pipeline output. This theorem has no premise about final leaders,
no CLEAN-slot restrictions, and no carry-bit or responder-control restriction.
It is a local consumer, not the first-service terminal trichotomy. -/
theorem pipeline_terminal_pending_right_hole (hp : ψ > 0) (κ : Nat)
    (l r : AuthState ψ) (bl br : Nat) (h : TerminalPending l r bl br) :
    (PPLLAuthF.pipeline hp κ cfg l r).2.core.path = .bot := by
  have hk : ψ - 2 + 1 = ψ - 1 := by have := h.width; omega
  have row : PPLLAuthGenDrain.RowH ψ l r (ψ - 2) := by
    refine ⟨h.lk,?_,?_,h.ll,h.rl,h.lr,h.rr⟩
    · rw [hk]; exact h.rk
    · omega
  obtain ⟨x,y,_,hf⟩ := PPLLAuthGenDrain.row_open hp κ cfg l r (ψ - 2) row
  let a := PPLLAuthGenDrain.withProbe l x
  let b := PPLLAuthGenDrain.withProbe r y
  have hab : TerminalPending a b bl br := by
    constructor <;> simp [a,b,PPLLAuthGenDrain.withProbe,h.width,h.lk,h.rk,
      h.lp,h.rp,h.ls,h.rs,h.lt,h.rt,h.ll,h.rl,h.lr,h.rr,h.pm,h.cm]
  have hg := gen_pending hp κ a b bl br hab
  have hw := wait_pending hp κ a b bl br hab
  generalize hwdef : lift2 (waitSaturated hp κ) a b = w at hg hw
  rcases w with ⟨wl,wr⟩
  have hz := rest_pending_hole hp κ wl wr bl br hw
  change PPLLAuthGenDrain.FV (PPLLAuthF.pipeline hp κ cfg l r).2 =
    PPLLAuthGenDrain.FV (PPLLAuthGenDrain.restPair hp κ cfg
      (genSigAuth hp κ a b)).2 at hf
  rw [hg] at hf
  generalize hout : PPLLAuthF.pipeline hp κ cfg l r = out at hf ⊢
  generalize hrest : PPLLAuthGenDrain.restPair hp κ cfg (wl,wr) = rest at hf hz
  exact (PPLLAuthGenDrain.FV_path hf).trans hz

#print axioms pipeline_terminal_pending_right_hole

end PPLLAuthCheckTerminalConsume
