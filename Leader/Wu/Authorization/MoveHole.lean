import Leader.Wu.Authorization.ProvenanceMarks

/-!
A main-path hole survives the original MOVE stage as a hole at one endpoint.
The transfer substage may move the hole from right to left. All other MOVE
substages retain or delete each endpoint path. Inputs are arbitrary raw states;
no token, state, label, leader, reset, mark or lottery premise is required.
-/

set_option autoImplicit false

namespace PPLLAuthFPairHole

open PPLL PPLLBirthPatch PPLLPostElectionGuard
open PPLLAuthF PPLLFableDesignR1
open PPLLAuthF.AuthState

variable {ψ : Nat}

private theorem core_ite (p : Prop) [Decidable p] (a b : AuthState ψ) :
    (if p then a else b).core = if p then a.core else b.core := by split <;> rfl
private theorem path_ite (p : Prop) [Decidable p] (a b : AgentState ψ) :
    (if p then a else b).path = if p then a.path else b.path := by split <;> rfl
private theorem fst_ite {α β : Type} (p : Prop) [Decidable p] (a b : α × β) :
    (if p then a else b).1 = if p then a.1 else b.1 := by split <;> rfl
private theorem snd_ite {α β : Type} (p : Prop) [Decidable p] (a b : α × β) :
    (if p then a else b).2 = if p then a.2 else b.2 := by split <;> rfl
attribute [local simp] core_ite path_ite fst_ite snd_ite

/-- At least one endpoint has no main path. -/
def PairHole (q : AuthState ψ × AuthState ψ) : Prop :=
  q.1.core.path = .bot ∨ q.2.core.path = .bot

@[simp] theorem clearCmpAuth_path (u : AuthState ψ) :
    (clearCmpAuth u).core.path = .bot := by
  simp [clearCmpAuth, PPLLPostElectionGuard.clearCmp]

@[simp] theorem dropP2_path (u : AuthState ψ) :
    (u.dropP2).core.path = u.core.path := by
  rfl

@[simp] theorem lineage_path (u : AuthState ψ) (s : MainState) :
    (u.lineage s).core.path = u.core.path := by
  rfl

@[simp] theorem demote_path (u : AuthState ψ) :
    (demote u).core.path = u.core.path := by
  simp [demote]

@[simp] theorem sanitizeP2_path (u : AuthState ψ) :
    (sanitizeP2 u).core.path = u.core.path := by
  simp [sanitizeP2]

@[simp] theorem claimA2_path (σ : ProvColor) (u : AuthState ψ) :
    (claimA2 σ u).core.path = u.core.path := by
  simp [claimA2]

@[simp] theorem receive_path (e : Entry) (src dst : AuthState ψ) (t : Path2Info) :
    (receive e src dst t).core.path = dst.core.path := by
  simp [receive]

@[simp] theorem sigMoveApplyControlConsume_path
    (hψ : ψ > 0) (u : AgentState ψ) :
    (PPLLBirthPatch.sigMoveApplyControlConsume hψ u).path = u.path := by
  cases h2 : u.path2 <;>
  simp [PPLLBirthPatch.sigMoveApplyControlConsume, h2]

@[simp] theorem applyControlAuth_path (hψ : ψ > 0) (u : AuthState ψ) :
    (applyControlAuth hψ u).core.path = u.core.path := by
  cases h2 : u.core.path2 <;>
  simp [applyControlAuth, h2]

@[simp] theorem validateCheck_left_path (l r : AuthState ψ) :
    (validateCheck l r).1.core.path = l.core.path := by
  simp [validateCheck]

@[simp] theorem validateCheck_right_path (l r : AuthState ψ) :
    (validateCheck l r).2.core.path = r.core.path := by
  simp [validateCheck]

theorem validateCheck_pairHole (l r : AuthState ψ)
    (h : PairHole (l, r)) : PairHole (validateCheck l r) := by
  simpa [PairHole] using h

theorem sanitizeP2_pairHole (l r : AuthState ψ)
    (h : PairHole (l, r)) : PairHole (sanitizeP2 l, sanitizeP2 r) := by
  simpa [PairHole] using h

/-- Transfer may refill the responder only by emptying the initiator. -/
theorem step1Auth_pairHole (l r : AuthState ψ)
    (h : PairHole (l, r)) : PairHole (step1Auth l r) := by
  change l.core.path = .bot ∨ r.core.path = .bot at h
  rcases h with hl | hr
  · simpa [PairHole, step1Auth, hl]
  · cases hlp : l.core.path with
    | bot => simp [PairHole, step1Auth, hlp]
    | some k b =>
      simp only [step1Auth, hlp, hr]
      split
      · split <;> simp [PairHole, hlp, hr]
      · simp [PairHole, hlp, hr]

private def tokenQueue (eL eR : Entry) (l r : AuthState ψ) : AuthState ψ × AuthState ψ :=
  match l.core.path2, r.core.path2 with
  | some tl, some tr =>
    if canMoveR l.core tl ∧ canMoveL r.core tr then
      (receive eL r l (dec tr), receive eR l r (dec tl))
    else if canMoveR l.core tl ∧ rightward tr ∧ canMoveR r.core tr then
      (l.dropP2, r)
    else if canMoveL r.core tr ∧ leftward tl ∧ canMoveL l.core tl then
      (l, r.dropP2)
    else (l, r)
  | some tl, none =>
    if canMoveR l.core tl then (l.dropP2, receive eR l r (dec tl)) else (l, r)
  | none, some tr =>
    if canMoveL r.core tr then (receive eL r l (dec tr), r.dropP2) else (l, r)
  | none, none => (l, r)


/-- The token queue leaves both destination main paths exactly unchanged. -/
private theorem tokenQueue_path (eL eR : Entry) (l r : AuthState ψ) :
    (tokenQueue eL eR l r).1.core.path = l.core.path ∧
      (tokenQueue eL eR l r).2.core.path = r.core.path := by
  cases h1 : l.core.path2 <;> cases h2 : r.core.path2 <;>
    simp only [tokenQueue, h1, h2] <;>
    (repeat' (first | (dsimp only) | split)) <;>
    simp only [receive_path, dropP2_path, and_self]

private theorem tokenQueue_drop_path (eL eR : Entry) (l r : AuthState ψ) :
    (tokenQueue eL eR (if eR = .reject then l.dropP2 else l)
      (if eL = .reject then r.dropP2 else r)).1.core.path = l.core.path ∧
    (tokenQueue eL eR (if eR = .reject then l.dropP2 else l)
      (if eL = .reject then r.dropP2 else r)).2.core.path = r.core.path := by
  have hq := tokenQueue_path eL eR
    (if eR = .reject then l.dropP2 else l)
    (if eL = .reject then r.dropP2 else r)
  simpa only [core_ite, path_ite, dropP2_path, ite_self] using hq

private def retirement4 (c : PPLLAuthF.Cfg) (l r : AuthState ψ) : Bool :=
  match l.core.path2 with
    | some tl => c.retire && tl.action == 4 && l.path2_scope == .line && p2Valid l &&
        canMoveR l.core tl && r.hasPath && l.path2_mark != r.path_mark
    | none => false

private def retirement2 (c : PPLLAuthF.Cfg) (l r : AuthState ψ) : Bool :=
  match r.core.path2 with
    | some tr => c.retire && tr.action == 2 && r.path2_scope == .session && p2Valid r &&
        canMoveL r.core tr && l.hasPath &&
        (waveState l.st || l.st == .CHECK_ready || l.st == .equal || l.st == .larger || l.st == .less) &&
        l.ctrl_mark != r.path2_mark && !claimable c.claimCheck l
    | none => false

private def moveTokensFactored (c : PPLLAuthF.Cfg) (l r : AuthState ψ) : AuthState ψ × AuthState ψ :=
  let cc := c.claimCheck
  let failA4 := retirement4 c l r
  let failA2 := retirement2 c l r
  if failA4 || failA2 then
    ((if failA4 then clearCmpAuth l else l), (if failA2 then clearCmpAuth r else r))
  else
  let eR : Entry := match l.core.path2 with
    | some tl => if canMoveR l.core tl then entry cc l r tl else .ok
    | none => .ok
  let eL : Entry := match r.core.path2 with
    | some tr => if canMoveL r.core tr then entry cc r l tr else .ok
    | none => .ok
  let l := if eR = .reject then l.dropP2 else l
  let r := if eL = .reject then r.dropP2 else r
  tokenQueue eL eR l r

private theorem moveTokens_eq (c : PPLLAuthF.Cfg) (l r : AuthState ψ) :
    moveTokensAuth c l r = moveTokensFactored c l r := rfl

/-- Opaque retirement flags can only delete; the remaining queue frames paths. -/
private theorem moveTokens_path_or_bot (c : PPLLAuthF.Cfg) (l r : AuthState ψ) :
    ((moveTokensAuth c l r).1.core.path = l.core.path ∨
      (moveTokensAuth c l r).1.core.path = .bot) ∧
    ((moveTokensAuth c l r).2.core.path = r.core.path ∨
      (moveTokensAuth c l r).2.core.path = .bot) := by
  rw [moveTokens_eq]
  unfold moveTokensFactored
  dsimp only
  generalize retirement4 c l r = b4
  generalize retirement2 c l r = b2
  by_cases hret : (b4 || b2) = true
  · rw [if_pos hret]
    constructor
    · change (if b4 then clearCmpAuth l else l).core.path = l.core.path ∨
        (if b4 then clearCmpAuth l else l).core.path = .bot
      cases b4 <;> simp [clearCmpAuth_path]
    · change (if b2 then clearCmpAuth r else r).core.path = r.core.path ∨
        (if b2 then clearCmpAuth r else r).core.path = .bot
      cases b2 <;> simp [clearCmpAuth_path]
  · rw [if_neg hret]
    exact ⟨Or.inl (tokenQueue_drop_path _ _ l r).1,
      Or.inl (tokenQueue_drop_path _ _ l r).2⟩

/-- Token retirement and movement preserve an existing initiator hole. -/
theorem moveTokensAuth_left_bot (c : PPLLAuthF.Cfg) (l r : AuthState ψ)
    (h : l.core.path = .bot) :
    (moveTokensAuth c l r).1.core.path = .bot := by
  rcases (moveTokens_path_or_bot c l r).1 with he | he
  · exact he.trans h
  · exact he

/-- Token retirement and movement preserve an existing responder hole. -/
theorem moveTokensAuth_right_bot (c : PPLLAuthF.Cfg) (l r : AuthState ψ)
    (h : r.core.path = .bot) :
    (moveTokensAuth c l r).2.core.path = .bot := by
  rcases (moveTokens_path_or_bot c l r).2 with he | he
  · exact he.trans h
  · exact he

theorem moveTokensAuth_pairHole (c : PPLLAuthF.Cfg) (l r : AuthState ψ)
    (h : PairHole (l, r)) : PairHole (moveTokensAuth c l r) := by
  change l.core.path = .bot ∨ r.core.path = .bot at h
  rcases h with hl | hr
  · exact Or.inl (moveTokensAuth_left_bot c l r hl)
  · exact Or.inr (moveTokensAuth_right_bot c l r hr)

theorem leaderWallAuth_pairHole (l r : AuthState ψ)
    (h : PairHole (l, r)) : PairHole (leaderWallAuth l r) := by
  change l.core.path = .bot ∨ r.core.path = .bot at h
  rcases h with hl | hr
  · simp [PairHole, leaderWallAuth, hl]
  · simp [PairHole, leaderWallAuth, hr]

theorem applyControlAuth_pairHole (hψ : ψ > 0) (l r : AuthState ψ)
    (h : PairHole (l, r)) :
    PairHole (applyControlAuth hψ l, applyControlAuth hψ r) := by
  simpa [PairHole] using h

/-- The complete original MOVE stage preserves pair-hole existence for raw inputs. -/
theorem moveSourceAuth_pairHole (hψ : ψ > 0) (c : PPLLAuthF.Cfg)
    (l r : AuthState ψ) (h : PairHole (l, r)) :
    PairHole (moveSourceAuth hψ c l r) := by
  let nextLabel : Fin ψ := ⟨(l.core.label.val + 1) % ψ, Nat.mod_lt _ hψ⟩
  let l0 : AuthState ψ :=
    if l.core.leader = true ∨ (r.core.leader = true ∧ r.core.label ≠ nextLabel) then
      clearCmpAuth l
    else l
  let r0 : AuthState ψ :=
    if r.core.leader = true then clearCmpAuth r else r
  have h0 : PairHole (l0, r0) := by
    change l.core.path = .bot ∨ r.core.path = .bot at h
    rcases h with hl | hr
    · simp [PairHole, l0, hl]
    · simp [PairHole, r0, hr]

  let q1 := validateCheck l0 r0
  have h1 : PairHole q1 := validateCheck_pairHole l0 r0 h0

  let l1 := sanitizeP2 q1.1
  let r1 := sanitizeP2 q1.2
  have h2 : PairHole (l1, r1) := by
    simpa [l1, r1] using sanitizeP2_pairHole q1.1 q1.2 h1

  let q2 := if l1.st = .done then (l1, r1) else step1Auth l1 r1
  have h3 : PairHole q2 := by
    by_cases hd : l1.st = .done
    · simpa [q2, hd] using h2
    · simpa [q2, hd] using step1Auth_pairHole l1 r1 h2

  let q3 := moveTokensAuth c q2.1 q2.2
  have h4 : PairHole q3 := moveTokensAuth_pairHole c q2.1 q2.2 h3

  let q4 := leaderWallAuth q3.1 q3.2
  have h5 : PairHole q4 := leaderWallAuth_pairHole q3.1 q3.2 h4

  let l4 := applyControlAuth hψ q4.1
  let r4 := applyControlAuth hψ q4.2
  have h6 : PairHole (l4, r4) := by
    simpa [l4, r4] using applyControlAuth_pairHole hψ q4.1 q4.2 h5

  let l5 : AuthState ψ :=
    if r4.st = .depart ∧ l4.core.label.val < ψ - 1 ∧ l4.st = .CHECK_ready then
      l4.lineage .depart
    else l4
  have h7 : PairHole (l5, r4) := by
    simpa [PairHole, l5] using h6

  change PairHole (l5, r4)
  exact h7

#print axioms moveSourceAuth_pairHole
#print axioms step1Auth_pairHole

end PPLLAuthFPairHole
