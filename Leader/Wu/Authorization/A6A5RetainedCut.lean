import Leader.Wu.Authorization.GenerationDrain
import Leader.Wu.Authorization.ResetDrain

/-!
# AuthF A6 -> toss -> A5 retained-cut handoff

This file starts at the exact input of `moveSourceAuth`, i.e. after
P', GENSIG, CLEAN, releaseSource and eliminateSig.  It proves only the
non-hole retained branch. The complementary CLEAN-hole branch and the
post-DISAPPEAR repair/lifecycle/full-tail assembly are separate obligations;
the accepted TerminalReady module now contains generic cut-level hole helpers.
This file makes no full-row or population-word claim.

The entrances are source-satisfiable at psi=2: choose arbitrary base records
and apply the constructors below. For a later two-block population composition,
n=4 supplies distinct Btail, X0 and X1 sites. No reachability claim is made.
-/

namespace PPLLAuthA6A5RetainedCut

open PPLL PPLLRepair PPLLBirthPatch PPLLBirthPatchM2 PPLLPostElectionGuard
open PPLLFableDesignR1 PPLLAstraDesign2 PPLLAstraDesign3 PPLLAuthF

set_option autoImplicit false

def cfg : PPLLAuthF.Cfg :=
  { retire := true, markClean := true, claimCheck := true }

def A5 : Path2Info := ⟨0, 0, 0, 5⟩
def A6 : Path2Info := ⟨0, 0, 0, 6⟩

private def f0 {ψ : Nat} (hp : ψ > 0) : Fin ψ :=
  ⟨0, hp⟩

private def f1 {ψ : Nat} (h2 : 2 ≤ ψ) : Fin ψ :=
  ⟨1, by omega⟩

private def flast {ψ : Nat} (hp : ψ > 0) : Fin ψ :=
  ⟨ψ - 1, by omega⟩

/-- Retained X-head A6 cut.  Every field not listed in the question is
inherited from `u`. -/
def X0A6 {ψ : Nat} (hp : ψ > 0) (γ : ProvColor) (b : Nat)
    (u : AuthState ψ) : AuthState ψ :=
  { u with
    core := { u.core with
      leader := false, reset_cmd := false, label := f0 hp,
      path := .some 0 b, state := .less, path2 := some A6 },
    path_mark := γ, ctrl_mark := γ,
    path2_scope := .line, path2_mark := γ }

/-- X1 at the retained first-row cut.  Its ctrl_mark is intentionally
left arbitrary. -/
def X1Ready {ψ : Nat} (h2 : 2 ≤ ψ) (γ : ProvColor) (b : Nat)
    (u : AuthState ψ) : AuthState ψ :=
  { u with
    core := { u.core with
      leader := false, reset_cmd := false, label := f1 h2,
      path := .some 1 b, state := .CHECK_ready, path2 := none },
    path_mark := γ }

/-- Btail at the retained seam cut. -/
def BTail {ψ : Nat} (hp : ψ > 0) (γ : ProvColor) (b : Nat)
    (u : AuthState ψ) : AuthState ψ :=
  { u with
    core := { u.core with
      leader := false, reset_cmd := false, label := flast hp,
      path := .some (ψ - 1) b, state := .depart, path2 := none },
    path_mark := γ, ctrl_mark := γ }

/-- Result of consuming the head A6. -/
def X0Toss {ψ : Nat} (hp : ψ > 0) (γ : ProvColor) (b : Nat)
    (u : AuthState ψ) : AuthState ψ :=
  let x := X0A6 hp γ b u
  { x with core := { x.core with state := .toss, path2 := none } }

/-- Source-level shell written by the responder-toss branch of DISAPPEAR.
The later carry is allowed to change p again; all the projections used below
ignore p/p_carry. -/
def X0A5 {ψ : Nat} (hp : ψ > 0) (γ : ProvColor) (b : Nat)
    (u : AuthState ψ) : AuthState ψ :=
  let x := X0Toss hp γ b u
  { x with
    core := { x.core with
      state := .toss_done, path2 := some A5, p := false },
    path2_scope := .line, path2_mark := γ }

/-- Fields needed for the A6/toss/A5 handoff.  Lottery and writer fields,
including p/p_carry and bit, are deliberately absent. -/
def V {ψ : Nat} (u : AuthState ψ) :=
  (u.core.state, u.core.path, u.core.path2, u.core.label,
   u.core.leader, u.core.reset_cmd,
   u.path_mark, u.ctrl_mark, u.path2_scope, u.path2_mark)

/-- First-row responder frame with state intentionally omitted: for ψ=2 an
incoming carry may make X1 eliminate_signal. -/
def CarrierV {ψ : Nat} (u : AuthState ψ) :=
  (u.core.path, u.core.path2, u.core.label,
   u.core.leader, u.core.reset_cmd,
   u.path_mark, u.ctrl_mark, u.path2_scope, u.path2_mark)

/-! ## MOVE and CHECK -/

/-- At physical label 0 the retained canonical A6 cannot move left; the
ownership check succeeds and applyControlAuth consumes it into toss. -/
theorem move_A6_head_exact {ψ : Nat} (hp : ψ > 0) (h2 : 2 ≤ ψ)
    (γ : ProvColor) (b0 b1 : Nat) (l r : AuthState ψ) :
    moveSourceAuth hp cfg (X0A6 hp γ b0 l) (X1Ready h2 γ b1 r) =
      (X0Toss hp γ b0 l, X1Ready h2 γ b1 r) := by
  simp [moveSourceAuth, cfg, X0A6, X0Toss, X1Ready, A6, f0, f1,
    validateCheck, headBad, checkState, verdict, isHead, aligned,
    sanitizeP2, p2Valid, AuthState.hasPath, step1Auth, moveTokensAuth,
    canMoveR, canMoveL, leaderWallAuth, applyControlAuth,
    sigMoveApplyControlConsume, AuthState.st]

/-- Guarded CHECK does not rewrite the retained X0 toss cell and does not
change the X1 CHECK_ready cell. -/
theorem check_toss_ready_exact {ψ : Nat} (hp : ψ > 0) (h2 : 2 ≤ ψ)
    (γ : ProvColor) (b0 b1 : Nat) (l r : AuthState ψ) :
    checkSourceAuth hp cfg (X0Toss hp γ b0 l) (X1Ready h2 γ b1 r) =
      (X0Toss hp γ b0 l, X1Ready h2 γ b1 r) := by
  simp [checkSourceAuth, cfg, X0Toss, X0A6, X1Ready, A6, f0, f1,
    validateCheck, headBad, checkState, verdict, isHead, aligned,
    readyAuth, waveState, checkSigSetReadyGuarded, controlPending,
    checkSigSetReady, checkSigCheckL, certPred, issue, checkSigSetResult,
    AuthState.st, AuthState.withCore, AuthState.lineage]

/-- The seam has no colour-equality premise: a depart Btail and a toss X-head
have no movable token and MOVE is exactly the identity. -/
theorem move_seam_exact {ψ : Nat} (hp : ψ > 0) (h2 : 2 ≤ ψ)
    (γB γX : ProvColor) (bB b0 : Nat) (l r : AuthState ψ) :
    moveSourceAuth hp cfg (BTail hp γB bB l) (X0Toss hp γX b0 r) =
      (BTail hp γB bB l, X0Toss hp γX b0 r) := by
  simp [moveSourceAuth, cfg, BTail, X0Toss, X0A6, A6, f0, flast,
    validateCheck, headBad, checkState, verdict, isHead, aligned,
    sanitizeP2, p2Valid, AuthState.hasPath, step1Auth, moveTokensAuth,
    leaderWallAuth, applyControlAuth, AuthState.st]

/-- On the seam CHECK cannot certify X0 from Btail: Btail is depart, not equal.
The toss responder is also protected by the controlPending guard. -/
theorem check_depart_toss_exact {ψ : Nat} (hp : ψ > 0) (h2 : 2 ≤ ψ)
    (γB γX : ProvColor) (bB b0 : Nat) (l r : AuthState ψ) :
    checkSourceAuth hp cfg (BTail hp γB bB l) (X0Toss hp γX b0 r) =
      (BTail hp γB bB l, X0Toss hp γX b0 r) := by
  have hlast : ψ - 1 = (ψ - 2) + 1 := by omega
  simp [hlast, checkSourceAuth, cfg, BTail, X0Toss, X0A6, A6, f0, flast,
    validateCheck, headBad, checkState, verdict, isHead, aligned,
    readyAuth, waveState, checkSigSetReadyGuarded, controlPending,
    checkSigSetReady, checkSigCheckL, certPred, issue, checkSigSetResult,
    AuthState.st, AuthState.withCore, AuthState.lineage]

/-! ## Quiet stages between MOVE and CHECK -/

private theorem drop_X0Toss {ψ : Nat} (hp : ψ > 0)
    (γ : ProvColor) (b : Nat) (u : AuthState ψ) :
    liftLife dropStale (X0Toss hp γ b u) = X0Toss hp γ b u := by
  simp [liftLife, dropStale, aligned, X0Toss, X0A6, f0]

private theorem drop_X1Ready {ψ : Nat} (h2 : 2 ≤ ψ)
    (γ : ProvColor) (b : Nat) (u : AuthState ψ) :
    liftLife dropStale (X1Ready h2 γ b u) = X1Ready h2 γ b u := by
  simp [liftLife, dropStale, aligned, X1Ready, f1]

private theorem drop_BTail {ψ : Nat} (hp : ψ > 0)
    (γ : ProvColor) (b : Nat) (u : AuthState ψ) :
    liftLife dropStale (BTail hp γ b u) = BTail hp γ b u := by
  simp [liftLife, dropStale, aligned, BTail, flast]

private theorem normalize_X0Toss {ψ : Nat} (hp : ψ > 0)
    (γ : ProvColor) (b : Nat) (u : AuthState ψ) :
    liftLife normalizeReady (X0Toss hp γ b u) = X0Toss hp γ b u := by
  simp [liftLife, normalizeReady, normalizeOrphan, normalizeCarrier,
    releaseCongest, aligned, X0Toss, X0A6, f0]

private theorem normalize_X1Ready {ψ : Nat} (h2 : 2 ≤ ψ)
    (γ : ProvColor) (b : Nat) (u : AuthState ψ) :
    liftLife normalizeReady (X1Ready h2 γ b u) = X1Ready h2 γ b u := by
  simp [liftLife, normalizeReady, normalizeOrphan, normalizeCarrier,
    releaseCongest, aligned, X1Ready, f1]

private theorem normalize_BTail {ψ : Nat} (hp : ψ > 0)
    (γ : ProvColor) (b : Nat) (u : AuthState ψ) :
    liftLife normalizeReady (BTail hp γ b u) = BTail hp γ b u := by
  simp [liftLife, normalizeReady, normalizeOrphan, normalizeCarrier,
    releaseCongest, aligned, BTail, flast]

private theorem preReset_first {ψ : Nat} (hp : ψ > 0) (h2 : 2 ≤ ψ)
    (γ : ProvColor) (b0 b1 : Nat) (l r : AuthState ψ) :
    preCheckResetAuth (X0Toss hp γ b0 l) (X1Ready h2 γ b1 r) =
      (X0Toss hp γ b0 l, X1Ready h2 γ b1 r) := by
  simp [preCheckResetAuth, X0Toss, X0A6, X1Ready]

private theorem preReset_seam {ψ : Nat} (hp : ψ > 0)
    (γB γX : ProvColor) (bB b0 : Nat) (l r : AuthState ψ) :
    preCheckResetAuth (BTail hp γB bB l) (X0Toss hp γX b0 r) =
      (BTail hp γB bB l, X0Toss hp γX b0 r) := by
  simp [preCheckResetAuth, BTail, X0Toss, X0A6]

/-- Literal original sub-suffix from the input of MOVE through CHECK, stopping
immediately before DISAPPEAR. -/
def preDisappear {ψ : Nat} (hp : ψ > 0) (c : PPLLAuthF.Cfg)
    (l r : AuthState ψ) : AuthState ψ × AuthState ψ :=
  let q := moveSourceAuth hp c l r
  let q := (liftLife dropStale q.1, liftLife dropStale q.2)
  let q := preCheckResetAuth q.1 q.2
  let q := (liftLife normalizeReady q.1, liftLife normalizeReady q.2)
  checkSourceAuth hp c q.1 q.2

theorem first_preDisappear_exact {ψ : Nat} (hp : ψ > 0) (h2 : 2 ≤ ψ)
    (γ : ProvColor) (b0 b1 : Nat) (l r : AuthState ψ) :
    preDisappear hp cfg (X0A6 hp γ b0 l) (X1Ready h2 γ b1 r) =
      (X0Toss hp γ b0 l, X1Ready h2 γ b1 r) := by
  simp only [preDisappear, move_A6_head_exact, drop_X0Toss, drop_X1Ready,
    preReset_first, normalize_X0Toss, normalize_X1Ready,
    check_toss_ready_exact]

theorem seam_preDisappear_exact {ψ : Nat} (hp : ψ > 0) (h2 : 2 ≤ ψ)
    (γB γX : ProvColor) (bB b0 : Nat) (l r : AuthState ψ) :
    preDisappear hp cfg (BTail hp γB bB l) (X0Toss hp γX b0 r) =
      (BTail hp γB bB l, X0Toss hp γX b0 r) := by
  simp only [preDisappear, move_seam_exact hp h2, drop_BTail, drop_X0Toss,
    preReset_seam, normalize_BTail, normalize_X0Toss,
    check_depart_toss_exact hp h2]

/-! ## DISAPPEAR -/

/-- DISAPPEAR never changes the handoff view of its initiator.  It may change
only the lottery coordinates p/p_carry there. -/
theorem disappear_left_V {ψ : Nat} (hp : ψ > 0) (l r : AuthState ψ) :
    V (disappearAuth hp l r).1 = V l := by
  unfold V
  unfold disappearAuth
  dsimp only [lift2]
  unfold disappearStartL disappearCarry
  simp only [Prod.mk.injEq]
  (repeat' constructor) <;>
    (repeat' (first | (dsimp only) | split)) <;> rfl

/-- If the responder is not toss, DISAPPEAR keeps its carrier/token/provenance
view.  Its state is omitted because an incoming carry can make a terminal
responder eliminate_signal. -/
theorem disappear_right_not_toss_CarrierV {ψ : Nat} (hp : ψ > 0)
    (l r : AuthState ψ) (hr : r.st ≠ .toss) :
    CarrierV (disappearAuth hp l r).2 = CarrierV r := by
  unfold CarrierV
  unfold disappearAuth
  simp only [hr, false_and, if_false]
  dsimp only [lift2]
  unfold disappearStartL disappearCarry
  simp only [Prod.mk.injEq]
  (repeat' constructor) <;>
    (repeat' (first | (dsimp only) | split)) <;> rfl

/-- The exact marked responder emitter.  No premise on l.p_carry or r.p is
needed: the responder-toss branch first writes p=false, so the following carry
can at most make p=true; it cannot change toss_done/A5 or its provenance. -/
theorem disappear_toss_A5_V {ψ : Nat} (hp : ψ > 0)
    (γ : ProvColor) (b : Nat) (l r : AuthState ψ) :
    V (disappearAuth hp l (X0Toss hp γ b r)).2 =
      V (X0A5 hp γ b r) := by
  simp [disappearAuth, V, X0A5, X0Toss, X0A6, A5, f0,
    lift2, disappearStartL, disappearCarry, AuthState.st]
  repeat' split <;> rfl

/-- First retained row: after the actual MOVE...CHECK...DISAPPEAR stages X0 is
still the toss head with no token.  X1 keeps its main path, empty token slot and
provenance; its state is intentionally not asserted. -/
theorem first_retained_handoff {ψ : Nat} (hp : ψ > 0) (h2 : 2 ≤ ψ)
    (γ : ProvColor) (b0 b1 : Nat) (l r : AuthState ψ) :
    let q := preDisappear hp cfg (X0A6 hp γ b0 l) (X1Ready h2 γ b1 r)
    V (disappearAuth hp q.1 q.2).1 = V (X0Toss hp γ b0 l) ∧
    CarrierV (disappearAuth hp q.1 q.2).2 = CarrierV (X1Ready h2 γ b1 r) := by
  rw [first_preDisappear_exact]
  refine ⟨disappear_left_V hp _ _, ?_⟩
  apply disappear_right_not_toss_CarrierV hp
  simp [X1Ready, AuthState.st]

/-- Seam retained row: Btail keeps depart/path/no-token/provenance in V, while
X0 emits the canonical line A5 with the X colour.  ΓB and ΓX are independent. -/
theorem seam_retained_handoff {ψ : Nat} (hp : ψ > 0) (h2 : 2 ≤ ψ)
    (γB γX : ProvColor) (bB b0 : Nat) (l r : AuthState ψ) :
    let q := preDisappear hp cfg (BTail hp γB bB l) (X0Toss hp γX b0 r)
    V (disappearAuth hp q.1 q.2).1 = V (BTail hp γB bB l) ∧
    V (disappearAuth hp q.1 q.2).2 = V (X0A5 hp γX b0 r) := by
  rw [seam_preDisappear_exact hp h2]
  exact ⟨disappear_left_V hp _ _, disappear_toss_A5_V hp γX b0 _ _⟩

#print axioms PPLLAuthA6A5RetainedCut.first_retained_handoff
#print axioms PPLLAuthA6A5RetainedCut.seam_retained_handoff

end PPLLAuthA6A5RetainedCut
