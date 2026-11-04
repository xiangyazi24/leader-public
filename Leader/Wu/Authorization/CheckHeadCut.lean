import Leader.Wu.Authorization.ProvenanceMarks

/-!
# CHECK-head cut for AuthF

This module isolates only the left CHECK-head behavior of `checkSourceAuth`.
A correctly lineage-stamped, aligned label-0 `CHECK_ready` cell is not
demoted by `headBad`, is checked even when `Cfg.strictReady = true`, and
then either stays `equal` with no token or emits the canonical line-scoped
A4/A6 result token.  The right endpoint is unrestricted.

The comparison uses the INPUT bit `l.core.bit`; no statement is made about
bits after later WRITE stages. This is only the actual CHECK substage.
Earlier MOVE/CLEAN and later lifecycle/full-row transport remain separate.

A source-level entrance is feasible already at psi=1: physical label 0,
path some 0 0, state CHECK_ready, empty path2, and both path/control marks 0.
Choose all other optional registers empty and Boolean/numeric fields false/zero;
the right raw state is arbitrary. This is a local entrance, not a claim of
generator reachability.
-/

namespace PPLLAuthCheckHeadCut

open PPLL PPLLBirthPatch PPLLBirthPatchM2 PPLLFableDesignR1 PPLLAuthF
open PPLLAuthF.AuthState

set_option autoImplicit false

variable {ψ : Nat}

private theorem fst_ite {α β : Type} (p : Prop) [Decidable p]
    (a b : α × β) :
    (if p then a else b).1 = if p then a.1 else b.1 := by
  split <;> rfl

private theorem state_ite (p : Prop) [Decidable p] (a b : AgentState ψ) :
    (if p then a else b).state = if p then a.state else b.state := by
  split <;> rfl

private theorem path_ite (p : Prop) [Decidable p] (a b : AgentState ψ) :
    (if p then a else b).path = if p then a.path else b.path := by
  split <;> rfl

private theorem issue_frame (u : AuthState ψ) :
    (issue u).core.state = u.core.state ∧
    (issue u).core.path = u.core.path ∧
    (issue u).ctrl_mark = u.ctrl_mark ∧
    (issue u).path_mark = u.path_mark := by
  unfold issue
  split <;> simp [checkSigSetResult, state_ite, path_ite]

private theorem left_eq_issue (hp : ψ > 0) (c : PPLLAuthF.Cfg)
    (l r : AuthState ψ) (b : Nat)
    (hl : l.core.label.val = 0)
    (hpath : l.core.path = .some 0 b)
    (hs : l.core.state = .CHECK_ready)
    (h2 : l.core.path2 = none)
    (hm : l.ctrl_mark = l.path_mark) :
    (checkSourceAuth hp c l r).1 =
      issue (l.withCore { l.core with state := checkBit l.core.bit b }) := by
  have hlabel : l.core.label = ⟨0, hp⟩ := by
    apply Fin.ext
    exact hl
  have hal : aligned l.core = true := by
    simp [aligned, hpath, hl]
  have hh : isHead l = true := by
    simp [isHead, hl, hal]
  have hb : headBad l = false := by
    simp [headBad, hh, hm]
  have hrdy : readyAuth l = l := by
    have hready : checkSigSetReadyGuarded l.core = l.core := by
      generalize hcore : l.core = u at hs ⊢
      cases hpu : u.path <;> cases u <;>
        simp_all [checkSigSetReadyGuarded, controlPending, checkSigSetReady]
    simp [readyAuth, waveState, AuthState.st, hs, hready]
  have hcheck : checkSigCheckL hp l.core =
      { l.core with state := checkBit l.core.bit b } := by
    simp [checkSigCheckL, hpath, hlabel, hs]
  have hh' : isHead
      (l.withCore { l.core with state := checkBit l.core.bit b }) = true := by
    simp [isHead, aligned, AuthState.withCore, hpath, hl]
  have hm' :
      (l.withCore { l.core with state := checkBit l.core.bit b }).ctrl_mark =
      (l.withCore { l.core with state := checkBit l.core.bit b }).path_mark := by
    simpa [AuthState.withCore] using hm
  simp [checkSourceAuth, validateCheck, hb, hh, hrdy, hcheck, hh', hm',
    AuthState.st, hs, fst_ite]

/-- Exact CHECK-head cut.  No hypothesis is imposed on the right endpoint or
on `c.strictReady`.  The left physical path and lineage marks are framed,
and the three possible CHECK results have their exact token behavior. -/
theorem check_head_cut (hp : ψ > 0) (c : PPLLAuthF.Cfg)
    (l r : AuthState ψ) (b : Nat)
    (hl : l.core.label.val = 0)
    (hpath : l.core.path = .some 0 b)
    (hs : l.core.state = .CHECK_ready)
    (h2 : l.core.path2 = none)
    (hm : l.ctrl_mark = l.path_mark) :
    let q := checkSourceAuth hp c l r
    q.1.core.state = checkBit l.core.bit b ∧
    q.1.core.path = .some 0 b ∧
    q.1.ctrl_mark = l.path_mark ∧
    q.1.path_mark = l.path_mark ∧
    (checkBit l.core.bit b = .larger →
      q.1.core.path2 = some ⟨0, 0, 0, 4⟩ ∧
      q.1.path2_scope = .line ∧ q.1.path2_mark = l.path_mark) ∧
    (checkBit l.core.bit b = .less →
      q.1.core.path2 = some ⟨0, 0, 0, 6⟩ ∧
      q.1.path2_scope = .line ∧ q.1.path2_mark = l.path_mark) ∧
    (checkBit l.core.bit b = .equal → q.1.core.path2 = none) := by
  dsimp only
  rw [left_eq_issue hp c l r b hl hpath hs h2 hm]
  have hf := issue_frame
    (l.withCore { l.core with state := checkBit l.core.bit b })
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [AuthState.withCore] using hf.1
  · simpa [AuthState.withCore, hpath] using hf.2.1
  · simpa [AuthState.withCore, hm] using hf.2.2.1
  · simpa [AuthState.withCore] using hf.2.2.2
  · intro h
    simp [issue, checkSigSetResult, AuthState.st, AuthState.withCore, h2, h, hm]
  · intro h
    simp [issue, checkSigSetResult, AuthState.st, AuthState.withCore, h2, h, hm]
  · intro h
    simp [issue, checkSigSetResult, AuthState.st, AuthState.withCore, h2, h, hm]

/-- The same cut as an unconditional three-way output classification. -/
theorem check_head_cases (hp : ψ > 0) (c : PPLLAuthF.Cfg)
    (l r : AuthState ψ) (b : Nat)
    (hl : l.core.label.val = 0)
    (hpath : l.core.path = .some 0 b)
    (hs : l.core.state = .CHECK_ready)
    (h2 : l.core.path2 = none)
    (hm : l.ctrl_mark = l.path_mark) :
    let q := checkSourceAuth hp c l r
    (q.1.core.state = .larger ∧
      q.1.core.path2 = some ⟨0, 0, 0, 4⟩ ∧
      q.1.path2_scope = .line ∧ q.1.path2_mark = l.path_mark) ∨
    (q.1.core.state = .less ∧
      q.1.core.path2 = some ⟨0, 0, 0, 6⟩ ∧
      q.1.path2_scope = .line ∧ q.1.path2_mark = l.path_mark) ∨
    (q.1.core.state = .equal ∧ q.1.core.path2 = none) := by
  have h := check_head_cut hp c l r b hl hpath hs h2 hm
  dsimp only at h ⊢
  rcases h with ⟨hst, _, _, _, h4, h6, he⟩
  cases hbit : l.core.bit
  · cases b with
    | zero =>
        right
        right
        exact ⟨by simpa [checkBit, hbit] using hst,
          he (by simp [checkBit, hbit])⟩
    | succ b =>
        right
        left
        exact ⟨by simpa [checkBit, hbit] using hst,
          h6 (by simp [checkBit, hbit])⟩
  · cases b with
    | zero =>
        left
        exact ⟨by simpa [checkBit, hbit] using hst,
          h4 (by simp [checkBit, hbit])⟩
    | succ b =>
        cases b with
        | zero =>
            right
            right
            exact ⟨by simpa [checkBit, hbit] using hst,
              he (by simp [checkBit, hbit])⟩
        | succ b =>
            right
            left
            exact ⟨by simpa [checkBit, hbit] using hst,
              h6 (by simp [checkBit, hbit])⟩

#print axioms check_head_cut
#print axioms check_head_cases

end PPLLAuthCheckHeadCut
