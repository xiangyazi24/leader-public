import Leader.Wu.Authorization.ProvenanceMarks

/-!
# authFchamp: the debris-hygiene amendment

Executable transcription of the amendment's code shape. No existing module is edited:
everything here is new, and every stage function reused from `PPLLAuthF` is called
exactly as `PPLLAuthF.pipeline`/`beforeElimination`/`cleanSourceAuth`/`moveSourceAuth`/
`disappearAuth` call it, with the four amendments spliced in at their exact insertion
points.

The four flags (`emptyScrub`, `seamFenceOn`, `lotteryScrub`, `strictScope`) implement
the three required repairs ((a) is `emptyScrub` + the seam fence, (c) is
`lotteryScrub`, (d, required half) is `strictScope`); `authFchamp` sets all four `true`.
The optional `routeA3` is *not* implemented (the max-source proof avoids genuine A3
entirely; `routeA3` would be the next amendment if a symmetric arbitrary-pair prune
theorem becomes necessary — out of scope for this regression pass).

## Design choices

* **Neutral pathless state.** The `emptyScrub` clause resets a pathless
  non-producer's `eliminate_signal` to `state := none` (`if u.state = eliminate_signal:
  set state := none`); no interpretation needed.
* **`seamFenceOn` as its own Cfg field.** The exact code shape gates the seam fence on
  the same `emptyScrub` flag used for (a)'s first half (`if emptyScrub and
  l.label = ψ-1 ...`). This file keeps them as two independently switchable fields
  (`emptyScrub`, `seamFenceOn`) so a regression ablation can attribute a trap to one
  mechanism rather than to both jointly (`run/verification/g62/champ/REGRESSION.md`);
  `authFchamp` sets both `true`, so this is a diagnostic-only deviation with no effect on
  `authFchamp`'s own behaviour or on any theorem checked against it.

## Regression scope

`emptyScrub` is a real departure from Wu's CLEAN semantics: it sacrifices remote CLEAN
back-transport (Algorithm 5) and can let disconnected CLEAN-killable fragments persist;
a regression battery against the old AuthF/AuthF+ trap seeds and small exact closures
is therefore mandatory. `run/verification/
g62/champ/REGRESSION.md` carries that battery for `authFplusmcc` vs `authFchamp`.
-/

set_option autoImplicit false

namespace PPLLAuthChamp

open PPLL PPLLRepair PPLLBirthPatch PPLLBirthPatchM2 PPLLPostElectionGuard
open PPLLFableDesignR1 PPLLAstraDesign2 PPLLAstraDesign3 PPLLAuthF

variable {ψ : Nat}

/-! ## Configuration -/

/-- The three flags wrapping a base `PPLLAuthF.Cfg` (kept as `authFplusmcc` in
`authFchamp`, but left free so the champion amendment can be composed with any base
reading, matching the Cfg-parametric shape of the checked Stage 1/2 theorems). -/
structure ChampCfg where
  base : PPLLAuthF.Cfg := {}
  /-- (a): scrub `-1` CLEAN commands, `path2` tokens, `p`/`p_carry`, and a stray
  `eliminate_signal` on a pathless non-producer cell, immediately after `genSigAuth` and
  before `cleanSourceAuth`. -/
  emptyScrub : Bool := false
  /-- (b): the terminal/head seam fence (`seamFence`), *inside* `cleanSourceAuth`
  after `genConnectAuth` and before `step3Auth`/`step4Auth`. The exact code
  shape gates this on the same `emptyScrub` flag; kept as its own field here so a
  regression ablation can attribute a trap to one mechanism rather than to both jointly
  (`run/verification/g62/champ/REGRESSION.md`); `authFchamp` sets both, so this split
  changes no behaviour. -/
  seamFenceOn : Bool := false
  /-- (c): replace `disappearAuth` (clear `p`/`p_carry` on both served cells, keep
  only the responder-toss completion, drop `disappearStartL`/`disappearCarry`), plus
  clear `p`/`p_carry` on the vacated `step1Auth` sender at its own position inside
  `moveSourceAuth`. -/
  lotteryScrub : Bool := false
  /-- (d, required half only): drop a `path2` token whose `(action, scope)`
  pair genuine token emission never produces (e.g. line-scope A3). -/
  strictScope : Bool := false
  deriving Repr

/-! ## (a) emptyScrub: pathless non-producer hygiene + terminal/head seam fence -/

/-- On a pathless (`path = .bot`), non-`produce` cell: drop a `-1` CLEAN command
(ordinary non-command `path4`/`path5` traffic is left alone, erasing ordinary
non-command `path4`/`path5` traffic there is not required), drop any `path2` token, clear
`p`/`p_carry`, and normalize a stray `eliminate_signal` to `MainState.none` (the exact
code shape: "if u.state = eliminate_signal: set state := none"). Occupied cells and
producers are untouched. -/
def emptyScrubOne (c : ChampCfg) (u : AuthState ψ) : AuthState ψ :=
  match u.core.path with
  | .some _ _ => u
  | .bot =>
    if u.st = .produce then u
    else if !c.emptyScrub then u
    else
      { u with core := { u.core with
          path4 := if isCmd u.core.path4 then none else u.core.path4,
          path5 := if isCmd u.core.path5 then none else u.core.path5,
          path2 := none,
          p := false, p_carry := false,
          state := if u.core.state = .eliminate_signal then .none else u.core.state } }

def emptyScrub (c : ChampCfg) (l r : AuthState ψ) : AuthState ψ × AuthState ψ :=
  (emptyScrubOne c l, emptyScrubOne c r)

/-- The seam fence, exact code shape: on an edge whose initiator `l` is a
physical terminal (`label = ψ - 1`) and whose responder `r` is a physical head
(`label = 0`), clear the initiator's `path5` and the responder's `path4` (and their
marks). Called from `champCleanSourceAuth`, *inside* `cleanSourceAuth`'s own composition,
after `genConnectAuth` and before `step3Auth`/`step4Auth` — not as an external pre-pass
before `cleanSourceAuth` runs at all. -/
def seamFence (c : ChampCfg) (l r : AuthState ψ) : AuthState ψ × AuthState ψ :=
  if !c.seamFenceOn then (l, r)
  else if l.core.label.val = ψ - 1 ∧ r.core.label.val = 0 then
    ({ l with core := { l.core with path5 := none }, path5_mark := 0 },
     { r with core := { r.core with path4 := none }, path4_mark := 0 })
  else (l, r)

/-! ## (d) strictScope: reject action/scope pairs genuine emission never produces -/

/-- Source facts: genuine line traffic is A4/A5/A6; genuine BEQ/session traffic is
A1/A2/A3/A4. -/
def scopeOK (scope : P2Scope) (t : Path2Info) : Bool :=
  match scope with
  | .line => t.action == 4 || t.action == 5 || t.action == 6
  | .session => t.action == 1 || t.action == 2 || t.action == 3 || t.action == 4

def strictScopeOne (c : ChampCfg) (u : AuthState ψ) : AuthState ψ :=
  if !c.strictScope then u
  else
    match u.core.path2 with
    | none => u
    | some t => if scopeOK u.path2_scope t then u else u.dropP2

/-! ## `champCleanSourceAuth`: `PPLLAuthF.cleanSourceAuth` with the seam fence spliced
in at its exact insertion point. -/

/-- `PPLLAuthF.cleanSourceAuth`'s own composition, verbatim, with `seamFence` inserted
after `genConnectAuth` and before `step3Auth`/`step4Auth` (the exact code
shape). -/
def champCleanSourceAuth (hψ : ψ > 0) (c : ChampCfg) (l r : AuthState ψ) :
    AuthState ψ × AuthState ψ :=
  let l := genConnectAuth l
  let r := genConnectAuth r
  let (l, r) := seamFence c l r
  let (l, r) := step3Auth c.base.cleanNbr c.base.markClean l r
  let (l, r) := step4Auth c.base.cleanNbr c.base.markClean l r
  let (l, r) := if isCmd l.core.path4 then (l, { r with core := { r.core with path4 := none } })
    else step5Auth hψ l r
  let (l, r) := if isCmd r.core.path5 then ({ l with core := { l.core with path5 := none } }, r)
    else step6Auth hψ l r
  (cleanApplyAuth l, cleanApplyAuth r)

/-! ## `champMoveSourceAuth`: `PPLLAuthF.moveSourceAuth` with `strictScope`'s
`sanitizeP2` replacement and `lotteryScrub`'s vacated-sender clear spliced in -/

/-- `sanitizeP2` (the mark-based half of holder validation) plus, when `strictScope` is
on, `strictScopeOne`'s action/scope check (when `strictScope` is true, `sanitizeP2`
drops all other combinations). -/
def champSanitizeP2 (c : ChampCfg) (u : AuthState ψ) : AuthState ψ :=
  strictScopeOne c (sanitizeP2 u)

/-- `PPLLAuthF.moveSourceAuth`'s own composition, verbatim, with `sanitizeP2` replaced
by `champSanitizeP2` and one addition: when `lotteryScrub` is on and `step1Auth` just
vacated `l` (`l`'s path went from `.some` to `.bot` on this very call — the only place
`moveSourceAuth` moves a main path), clear `l`'s `p`/`p_carry` right there, so movement
endpoints are canonical immediately rather than only at the later DISAPPEAR cut. The receiver's
`p`/`p_carry` needs no separate clear: `step1Auth` itself already sets them `false` on a
successful arrival. -/
def champMoveSourceAuth (hψ : ψ > 0) (c : ChampCfg) (l r : AuthState ψ) :
    AuthState ψ × AuthState ψ :=
  let nextLabel : Fin ψ := ⟨(l.core.label.val + 1) % ψ, Nat.mod_lt _ hψ⟩
  let l := if l.core.leader = true ∨ (r.core.leader = true ∧ r.core.label ≠ nextLabel) then
    clearCmpAuth l else l
  let r := if r.core.leader = true then clearCmpAuth r else r
  let (l, r) := validateCheck l r
  let l := champSanitizeP2 c l
  let r := champSanitizeP2 c r
  let preL := l
  let preR := r
  let (l, r) := if l.st = .done then (l, r) else step1Auth l r
  let l := if c.lotteryScrub then
      match preL.core.path, preR.core.path, l.core.path with
      | .some _ _, .bot, .bot => { l with core := { l.core with p := false, p_carry := false } }
      | _, _, _ => l
    else l
  let (l, r) := moveTokensAuth c.base l r
  let (l, r) := leaderWallAuth l r
  let l := applyControlAuth hψ l
  let r := applyControlAuth hψ r
  let l := if r.st = .depart ∧ l.core.label.val < ψ - 1 ∧ l.st = .CHECK_ready then
    l.lineage .depart else l
  (l, r)

/-! ## `champDisappearAuth`: `disappearAuth` amended under `lotteryScrub` -/

/-- Exact code shape (c): `disappearAuth` first clears `p` and `p_carry` on both served
cells, then runs only the responder-toss completion; it does not run `disappearStartL`
or `disappearCarry`. The responder-toss branch is copied verbatim
from `PPLLAuthF.disappearAuth`. When `lotteryScrub` is off, defers to `disappearAuth`
unchanged. -/
def champDisappearAuth (hψ : ψ > 0) (c : ChampCfg) (l r : AuthState ψ) :
    AuthState ψ × AuthState ψ :=
  if !c.lotteryScrub then disappearAuth hψ l r
  else
    let l := { l with core := { l.core with p := false, p_carry := false } }
    let r := { r with core := { r.core with p := false, p_carry := false } }
    if r.st = .toss ∧ r.core.label = ⟨0, hψ⟩ then
      let rCore := { r.core with state := MainState.toss_done, path2 := some ⟨0, 0, 0, 5⟩, p := false }
      (l, { r with core := rCore, path2_scope := .line, path2_mark := r.ctrl_mark })
    else (l, r)

/-! ## The champion pipeline -/

/-- `PPLLAuthF.beforeElimination` with the four amendments spliced in at their exact
insertion points. -/
def champBeforeElimination (hψ : ψ > 0) (κ : Nat) (c : ChampCfg) (l r : AuthState ψ) :
    AuthState ψ × AuthState ψ :=
  let q := lift2 (pPsiProbeWall hψ) l r
  let q := genSigAuth hψ κ q.1 q.2
  -- (a) emptyScrub pre-pass, before cleanSourceAuth runs at all.
  let q := emptyScrub c q.1 q.2
  -- (a)+(b) cleanSourceAuth, with the seam fence spliced in after genConnectAuth.
  let q := champCleanSourceAuth hψ c q.1 q.2
  let q := lift2Life (releaseSource hψ) q.1 q.2
  let q := lift2 (eliminateSig hψ) q.1 q.2
  -- (c)+(d) moveSourceAuth, with strictScope's sanitizeP2 replacement and the
  -- lotteryScrub vacated-sender clear spliced in at step1Auth's own position.
  let q := champMoveSourceAuth hψ c q.1 q.2
  let q := (liftLife dropStale q.1, liftLife dropStale q.2)
  let q := preCheckResetAuth q.1 q.2
  let q := (liftLife normalizeReady q.1, liftLife normalizeReady q.2)
  let q := checkSourceAuth hψ c.base q.1 q.2
  -- (c) disappearAuth, replaced under lotteryScrub.
  let q := champDisappearAuth hψ c q.1 q.2
  let q := repairAuth q.1 q.2
  let q := compareLifecycleAuth κ q.1 q.2
  suppressSigResetKillAuth hψ q.1 q.2

/-- `PPLLAuthF.pipeline` with `champBeforeElimination` in place of `beforeElimination`.
The pairwise interaction step of the champion protocol. -/
def champStep (hψ : ψ > 0) (κ : Nat) (c : ChampCfg) (l r : AuthState ψ) :
    AuthState ψ × AuthState ψ :=
  let q := champBeforeElimination hψ κ c l r
  let q := lift2 (k4Kernel hψ) q.1 q.2
  let q := lift2 (writeWithBundle hψ) q.1 q.2
  conserveAuth l r q

/-- `authFplusmcc` with all four flags on. -/
def authFchamp : ChampCfg :=
  { base := { retire := true, markClean := true, claimCheck := true }
    emptyScrub := true, seamFenceOn := true, lotteryScrub := true, strictScope := true }

/-- Coordinator-requested variant (`run/verification/g62/champ/REGRESSION.md`, "authFchampNF
round"): `authFchamp` with the seam fence switched off, `emptyScrub`/`lotteryScrub`/
`strictScope` left on. Isolates how much of the `seamFence`-attributed same-cap regression
signal (every deep-dived regression seed implicated `seamFence`, alone or jointly) is
actually removed by dropping just that one mechanism. -/
def authFchampNF : ChampCfg := { authFchamp with seamFenceOn := false }

/-! ## Physical words (mirrors `PPLLAuthResetDrain.authRun`) -/

/-- The champion protocol with configuration `c`; output is the core leader bit. -/
abbrev champProtocol (hψ : ψ > 0) (κ : Nat) (c : ChampCfg) : PopulationProtocol where
  Q := AuthState ψ
  Y := Bool
  transition := champStep hψ κ c
  output := fun a => a.core.leader

/-- Execute a physical word under the champion protocol. -/
def champRun {n : Nat} (hψ : ψ > 0) (κ : Nat) (c : ChampCfg) (ring : DirectedRing n)
    (C : Fin n → AuthState ψ) : List (Fin n) → (Fin n → AuthState ψ)
  | [] => C
  | e :: es => champRun hψ κ c ring ((champProtocol hψ κ c).step ring C e) es

theorem champRun_reachable {n : Nat} (hψ : ψ > 0) (κ : Nat) (c : ChampCfg)
    (ring : DirectedRing n) (C : Fin n → AuthState ψ) (w : List (Fin n)) :
    (champProtocol hψ κ c).Reachable ring C (champRun hψ κ c ring C w) := by
  induction w generalizing C with
  | nil => exact PopulationProtocol.Reachable.refl (P := champProtocol hψ κ c) C
  | cons e es ih =>
    have h1 : (champProtocol hψ κ c).Reachable ring C ((champProtocol hψ κ c).step ring C e) :=
      PopulationProtocol.OneStep.to_reachable ⟨e, rfl⟩
    exact PopulationProtocol.Reachable.trans h1 (ih _)

end PPLLAuthChamp
