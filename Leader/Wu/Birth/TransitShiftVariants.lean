import Leader.Wu.Birth.ChannelVariants

/-!
# M2 candidates on top of the best M1 patch (board G6.2 follow-up; design input)

Every M2 family found by the G6.2 census (n = 2, 4, 6) is one signal stopped
in transit, shifted by one cell: sub-signal `s0` (path label 0) sits on a
label-(ψ-1) cell and `s1` (path label ψ-1) on the next, label-0 cell.  The
printed CMP_UPDATE (Algorithm 7, thesis p.23 / PDF p.36; `cmpUpdate`,
Algorithm.lean:394-399, `cmpUpdatePropagate` Algorithm.lean:371-384) keys its
roles on the *cell* label, so the pair (`s0` on a terminal-label cell in
`congest`, `s1` on a label-0 cell) reads as "tail of S, head of S'" and line 4
puts the signal's own head into `lock`.  SIGMOVE line 2 (thesis p.25 / PDF
p.38; `sigMoveStep1`, Algorithm.lean:462-470) then refuses to move a head in
`lock`, `compare1` or `CHECK_ready`, and nothing ever releases it (the cell to
its right is empty, so COMPARE never runs there).

The thesis text describes both mechanisms in terms of sub-signal positions,
not cell labels: COMPARE runs when "two signals are adjacent, and the signal in
front is not moving" (§3.3.3, p.22 / PDF p.35), and CHECK "begins when each
sub-signal is on the corresponding agent (sᵢ is on uᵢ)" (§3.3.4, p.26 /
PDF p.39; Algorithm 11 line 2 tests `u.label = u.path[1]`).  CLEAN_SIG
(Algorithm 5, p.21 / PDF p.34) is the one place where the printed code keys
signal structure on path labels (`r.path4[1] ≠ l.path[1] + 1`).  The source
has no rule for a path whose label disagrees with its holder other than CHECK's
alignment test; it never resets a stale blocking state.

Candidates (each is applied on top of the best M1 patch):

* `staleReady` — SIGMOVE line 2 treats `CHECK_ready` as blocking only on an
  aligned holder (`u.label = u.path[1]`, the CHECK line-2 condition).
* `staleBlock` — all three blocking states block only on an aligned holder.
* `dropMisaligned` — at CHECK time, a misaligned holder in a blocking state
  drops its path (`path := ⊥`, `state := none`); CLEAN_SIG then removes the
  rest of the partial signal.
* `pathKeyed` — source-based: CMP_UPDATE's role tests use the sub-signal index
  `u.path[1]` in place of the cell label `u.label` (identical on aligned
  signals, which is the only case the prose describes).  Rearm guard, line-15
  `path2` start and all later stages are unchanged.
-/

set_option autoImplicit false

namespace PPLLBirthPatchM2

open PPLL PPLLRepair PPLLBirthPatch

inductive M2 where
  | none | staleReady | staleBlock | dropMisaligned | pathKeyed | pathKeyedStaleBlock
  deriving DecidableEq

/-- Holder aligned with its sub-signal (Algorithm 11 line 2 / Algorithm.lean:229). -/
def aligned {ψ : Nat} (u : AgentState ψ) : Bool :=
  match u.path with
  | .some pl _ => decide (u.label.val = pl)
  | .bot => false

def blockingState {ψ : Nat} (u : AgentState ψ) : Bool :=
  decide (u.state = .lock ∨ u.state = .compare1 ∨ u.state = .CHECK_ready)

/-- SIGMOVE line 1-6 (`sigMoveStep1`, Algorithm.lean:462-470) with the
blocking test chosen by the M2 candidate. -/
def sigMoveStep1With {ψ : Nat} (m : M2) (l r : AgentState ψ) :
    AgentState ψ × AgentState ψ :=
  match l.path, r.path with
  | .some pathLabel _, .bot =>
    let blocked : Bool := match m with
      | .staleReady =>
          decide (l.state = .lock ∨ l.state = .compare1) ||
          (decide (l.state = .CHECK_ready) && aligned l)
      | .staleBlock | .pathKeyedStaleBlock => blockingState l && aligned l
      | _ => blockingState l
    if !blocked then
      if r.state ≠ MainState.produce ∨ pathLabel ≠ ψ - 1 then
        ({ l with path := .bot, state := .none }, { r with path := l.path })
      else (l, r)
    else (l, r)
  | _, _ => (l, r)

/-- `PPLLBirthPatch.sigMoveWith` (consume = true) with step 1 replaced. -/
def sigMoveM2 {ψ : Nat} (hψ : ψ > 0) (m : M2) (l r : AgentState ψ) :
    AgentState ψ × AgentState ψ :=
  let (l, r) := sigMoveStep1With m l r
  let (l, r) := sigMoveStep2 l r
  let (l, r) := sigMoveStep3 l r
  let (l, r) := sigMoveStep4 l r
  let (l, r) := sigMoveStep5 l r
  let l := sigMoveApplyControlConsume hψ l
  let r := sigMoveApplyControlConsume hψ r
  let l := if r.state = MainState.depart then
    if l.label.val < ψ - 1 ∧ l.state = MainState.CHECK_ready then
      { l with state := MainState.depart }
    else l
  else l
  (l, r)

/-- `dropMisaligned`: a misaligned holder in a blocking state drops its path. -/
def dropStale {ψ : Nat} (u : AgentState ψ) : AgentState ψ :=
  if u.path ≠ .bot ∧ aligned u = false ∧ blockingState u = true then
    { u with path := .bot, state := .none }
  else u

/-- Sub-signal index used as the CMP_UPDATE role (`u.path[1]`); the cell label
only when there is no path (COMPARE runs only when both endpoints hold one). -/
def role {ψ : Nat} (hψ : ψ > 0) (u : AgentState ψ) : Fin ψ :=
  match u.path with
  | .some pl _ => ⟨pl % ψ, Nat.mod_lt _ hψ⟩
  | .bot => u.label

/-- `cmpUpdatePropagate` (Algorithm.lean:371-384) keyed on `role`. -/
def cmpPropagateByRole {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ) :
    AgentState ψ × AgentState ψ :=
  let last : Fin ψ := ⟨ψ - 1, by omega⟩
  if role hψ l = last ∧ l.state = .congest then
    (l, { r with state := .lock })
  else if role hψ r = last ∧ l.state = .lock then
    (l, { r with state := .compare1 })
  else if role hψ l = last ∧ r.state = .compare1 then
    ({ l with state := .compare2 }, r)
  else
    if l.state = .congest ∨ l.state = .lock then
      (l, { r with state := l.state })
    else if r.state = .compare1 ∨ r.state = .compare2 then
      ({ l with state := r.state }, r)
    else (l, r)

/-- `cmpUpdateSetPath2` (Algorithm.lean:386-392) keyed on `role`. -/
def cmpSetPath2ByRole {ψ : Nat} (hψ : ψ > 0) (l : AgentState ψ) : AgentState ψ :=
  match l.path with
  | .some pathLabel pathBit =>
    if role hψ l = ⟨0, hψ⟩ ∧ l.state = .compare2 then
      { l with path2 := some ⟨pathLabel, pathBit, ψ, 1⟩ }
    else l
  | .bot => l

/-- CMP_UPDATE keyed on `role`, with the rearm guard of the chosen base. -/
def cmpUpdateByRole {ψ : Nat} (hψ : ψ > 0) (cmp : Cmp) (l r : AgentState ψ) :
    AgentState ψ × AgentState ψ :=
  let start : Bool := match cmp with
    | .original => decide (role hψ l = ⟨0, hψ⟩)
    | .noSourceRearm => decide (role hψ l = ⟨0, hψ⟩ ∧ l.state ≠ .depart)
    | .leaderlessRearm =>
        decide (role hψ l = ⟨0, hψ⟩ ∧ (l.state ≠ .depart ∨ l.leader = false))
  let l := if start then { l with state := .congest } else l
  let q := cmpPropagateByRole hψ l r
  (cmpSetPath2ByRole hψ q.1, q.2)

def compareSigM2 {ψ : Nat} (hψ : ψ > 0) (cmp : Cmp) (m : M2)
    (l r : AgentState ψ) : AgentState ψ × AgentState ψ :=
  let l := compareSigInit l
  match l.path with
  | .bot => (l, r)
  | .some _ _ =>
    match r.path with
    | .some _ _ =>
      let q := match m with
        | .pathKeyed | .pathKeyedStaleBlock => cmpUpdateByRole hψ cmp l r
        | _ => match cmp with
          | .original => cmpUpdate hψ l r
          | .noSourceRearm => cmpUpdateNoSourceRearm hψ l r
          | .leaderlessRearm => cmpUpdateLeaderlessRearm hψ l r
      let q := (keepElim l q.1, keepElim r q.2)
      compareSigDispatch hψ q.1 q.2
    | .bot => (l, r)

/-- Best M1 patch (consume, protect, readyGuard; `cmp` = `.original` for the
bounded base, `.leaderlessRearm` for the integrated base) plus one M2 candidate.
With `m = .none` it is `PPLLBirthPatch.pipeline hψ κ true cmp true true`. -/
def pipeline {ψ : Nat} (hψ : ψ > 0) (κ : Nat) (cmp : Cmp) (m : M2)
    (l r : AgentState ψ) : AgentState ψ × AgentState ψ :=
  let q := pPsi hψ l r
  let q := genSigSaturated hψ κ q.1 q.2
  let q := cleanSig hψ q.1 q.2
  let q := eliminateSig hψ q.1 q.2
  let q := sigMoveM2 hψ m q.1 q.2
  let q := if m = .dropMisaligned then (dropStale q.1, dropStale q.2) else q
  let q := checkSigWith hψ true q.1 q.2
  let q := disappear hψ q.1 q.2
  let q := compareSigM2 hψ cmp m q.1 q.2
  let q := suppressSig hψ q.1 q.2
  let q := eliminateLeadersNoCollision hψ q.1 q.2
  writeSeq hψ q.1 q.2

def variants : List (String × Cmp × M2) :=
  [ ("boundedM1", .original, .none)
  , ("integratedM1", .leaderlessRearm, .none) ] ++
  ([("StaleReady", M2.staleReady), ("StaleBlock", .staleBlock),
    ("DropMis", .dropMisaligned), ("PathKeyed", .pathKeyed),
    ("PathKeyedStaleBlock", .pathKeyedStaleBlock)].flatMap fun (s, m) =>
    [("boundedM1" ++ s, Cmp.original, m), ("integratedM1" ++ s, .leaderlessRearm, m)])

end PPLLBirthPatchM2
