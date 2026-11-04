import Leader.Wu.Protocol.Repairs

/-!
# Birth-channel patch candidates (board G6.2 design input, not a proof)

Local patches of the repaired P_PLL pipelines, for the closure census only.
No existing protocol module is edited; each pipeline below is spelled out
stage by stage from the public stage functions of `Leader/Wu/Protocol/Algorithm.lean` and
`Leader/Wu/Protocol/Repairs.lean`, and `rebuiltBounded` / `rebuiltIntegrated` are meant to
reproduce `ppllSaturatedNoCollision` (Repairs.lean:946) and
`ppllIntegratedRepair` (Repairs.lean:987) without any patch.  The `rfl`
equation times out in `whnf` at the default heartbeat budget, so the census
checks the reconstruction empirically: the rebuilt variants must reproduce the
original closures byte for byte before a patched run is trusted.

Patches:

* **consume** — `sigMoveApplyControlConsume`: the SIGMOVE control application
  (Algorithm.lean:472-480) clears `path2` in the step in which it fires one of
  its three actions.  Same definition as
  `ZZRepairAll10Consume.sigMoveApplyControlConsume` (ERRATA T29 repair),
  restated here because that module's import closure is ~520 modules.
* **rearm** — `cmpUpdateLeaderlessRearm`: the integrated T9 guard
  `l.label = 0 ∧ l.state ≠ .depart` (Repairs.lean:955-959) keeps the `.depart`
  exclusion only for a cell that carries a leader:
  `l.label = 0 ∧ (l.state ≠ .depart ∨ l.leader = false)` (repair 3 of
  `ZZRepairAll`).
* **protect** — `keepElim`: CMP_UPDATE (Algorithm.lean:394-399, including
  `cmpUpdatePropagate` Algorithm.lean:371-384) may not overwrite an in-flight
  control state (`eliminate_signal`, `toss`) written earlier in
  the same interaction.
* **readyGuard** — `checkSigSetReadyGuarded`: CHECK's ready assignment
  (Algorithm.lean:226-233) excludes `depart/equal/larger/less` but not the
  in-flight control states, so a `toss` (or `eliminate_signal`) that SIGMOVE's
  control application (Algorithm.lean:472-480) writes is replaced by
  `CHECK_ready` in the same interaction, before DISAPPEAR's lottery
  (Algorithm.lean:297-330) / ELIMINATE_SIG (Algorithm.lean:201) can act on it.  The guarded version leaves those states alone.

These are raw `AgentState ψ` transitions with no domain-closure theorem; the
census reifies their outputs into `BoundedAgentState` by a checked runtime
conversion and reports any output outside the declared domain.
-/

set_option autoImplicit false

namespace PPLLBirthPatch

open PPLL PPLLRepair

/-- SIGMOVE control application that consumes the `path2` token it acts on. -/
def sigMoveApplyControlConsume {ψ : Nat} (hψ : ψ > 0) (u : AgentState ψ) : AgentState ψ :=
  match u.path2 with
  | some p2 =>
    let hit1 := u.label = (⟨ψ - 1, by omega⟩ : Fin ψ) ∧ (p2.action = 3 ∨ p2.action = 4)
    let hit2 := u.label = (⟨ψ - 1, by omega⟩ : Fin ψ) ∧ p2.action = 5
    let hit3 := u.label = (⟨0, hψ⟩ : Fin ψ) ∧ p2.action = 6
    let u := if hit1 then { u with state := MainState.eliminate_signal } else u
    let u := if hit2 then { u with state := MainState.depart } else u
    let u := if hit3 then { u with state := MainState.toss } else u
    if hit1 ∨ hit2 ∨ hit3 then { u with path2 := none } else u
  | none => u

/-- `sigMove` (Algorithm.lean:516-530) with the control application chosen. -/
def sigMoveWith {ψ : Nat} (hψ : ψ > 0) (consume : Bool) (l r : AgentState ψ) :
    AgentState ψ × AgentState ψ :=
  let (l, r) := sigMoveStep1 l r
  let (l, r) := sigMoveStep2 l r
  let (l, r) := sigMoveStep3 l r
  let (l, r) := sigMoveStep4 l r
  let (l, r) := sigMoveStep5 l r
  let apply := if consume then sigMoveApplyControlConsume hψ else sigMoveApplyControl hψ
  let l := apply l
  let r := apply r
  let l := if r.state = MainState.depart then
    if l.label.val < ψ - 1 ∧ l.state = MainState.CHECK_ready then
      { l with state := MainState.depart }
    else l
  else l
  (l, r)

/-- CMP_UPDATE whose `.depart` exclusion applies only to a leader cell. -/
def cmpUpdateLeaderlessRearm {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ) :
    AgentState ψ × AgentState ψ :=
  let l := if l.label = ⟨0, hψ⟩ ∧ (l.state ≠ .depart ∨ l.leader = false) then
    { l with state := .congest }
  else l
  let q := cmpUpdatePropagate hψ l r
  (cmpUpdateSetPath2 hψ q.1, q.2)

/-- Which CMP_UPDATE the COMPARE stage uses. -/
inductive Cmp where
  | original      -- `cmpUpdate` (Algorithm.lean:394), used by `boundedProtocol`
  | noSourceRearm -- `cmpUpdateNoSourceRearm` (Repairs.lean:955), integrated
  | leaderlessRearm

/-- In-flight SIGMOVE control states written by `sigMoveApplyControl`
(Algorithm.lean:472-480) and consumed by ELIMINATE_SIG (Algorithm.lean:201) /
DISAPPEAR (Algorithm.lean:297-330).  `toss_done` is deliberately not included:
nothing in the transition leaves `toss_done` except these overwrites, and a
first version that protected it froze a new leaderless family at n = 2. -/
def controlPending {ψ : Nat} (u : AgentState ψ) : Prop :=
  u.state = .eliminate_signal ∨ u.state = .toss

instance {ψ : Nat} (u : AgentState ψ) : Decidable (controlPending u) := by
  unfold controlPending; exact inferInstance

/-- Restore an in-flight control state that CMP_UPDATE overwrote. -/
def keepElim {ψ : Nat} (before after : AgentState ψ) : AgentState ψ :=
  if controlPending before then { after with state := before.state } else after

/-- CHECK's ready assignment (Algorithm.lean:226-233) that also leaves an
in-flight control state alone. -/
def checkSigSetReadyGuarded {ψ : Nat} (u : AgentState ψ) : AgentState ψ :=
  if controlPending u then u else checkSigSetReady u

/-- `checkSig` (Algorithm.lean:277-288) with the ready assignment chosen. -/
def checkSigWith {ψ : Nat} (hψ : ψ > 0) (readyGuard : Bool) (l r : AgentState ψ) :
    AgentState ψ × AgentState ψ :=
  let ready := if readyGuard then checkSigSetReadyGuarded else checkSigSetReady
  let l := ready l
  let r := ready r
  let l := checkSigCheckL hψ l
  let r := checkSigCheckR hψ l r
  let l := checkSigSetResult l
  let r := checkSigSetResult r
  let r :=
    if r.label = ⟨ψ - 1, by omega⟩ ∧ r.state = .equal then
      { r with leader := true }
    else r
  (l, r)

def compareSigWith {ψ : Nat} (hψ : ψ > 0) (cmp : Cmp) (protect : Bool)
    (l r : AgentState ψ) : AgentState ψ × AgentState ψ :=
  let l := compareSigInit l
  match l.path with
  | .bot => (l, r)
  | .some _ _ =>
    match r.path with
    | .some _ _ =>
      let q := match cmp with
        | .original => cmpUpdate hψ l r
        | .noSourceRearm => cmpUpdateNoSourceRearm hψ l r
        | .leaderlessRearm => cmpUpdateLeaderlessRearm hψ l r
      let q := if protect then (keepElim l q.1, keepElim r q.2) else q
      compareSigDispatch hψ q.1 q.2
    | .bot => (l, r)

/-- The full repaired pipeline with the two patch switches.  With
`consume = false`, `protect = false` and `cmp = .original` it is `ppllSaturatedNoCollision`;
with `consume = false` and `cmp = .noSourceRearm` it is `ppllIntegratedRepair`. -/
def pipeline {ψ : Nat} (hψ : ψ > 0) (κ : Nat) (consume : Bool) (cmp : Cmp)
    (protect readyGuard : Bool) (l r : AgentState ψ) : AgentState ψ × AgentState ψ :=
  let q := pPsi hψ l r
  let q := genSigSaturated hψ κ q.1 q.2
  let q := cleanSig hψ q.1 q.2
  let q := eliminateSig hψ q.1 q.2
  let q := sigMoveWith hψ consume q.1 q.2
  let q := checkSigWith hψ readyGuard q.1 q.2
  let q := disappear hψ q.1 q.2
  let q := compareSigWith hψ cmp protect q.1 q.2
  let q := suppressSig hψ q.1 q.2
  let q := eliminateLeadersNoCollision hψ q.1 q.2
  writeSeq hψ q.1 q.2

/-- Named patch variants: `(consume, cmp, protect, readyGuard)`. -/
def variants : List (String × Bool × Cmp × Bool × Bool) :=
  [ ("rebuiltBounded", false, .original, false, false)
  , ("rebuiltIntegrated", false, .noSourceRearm, false, false)
  , ("boundedConsume", true, .original, false, false)
  , ("integratedConsume", true, .noSourceRearm, false, false)
  , ("integratedRearm", false, .leaderlessRearm, false, false)
  , ("integratedConsumeRearm", true, .leaderlessRearm, false, false)
  , ("boundedProtect", false, .original, true, false)
  , ("integratedProtect", false, .noSourceRearm, true, false)
  , ("integratedRearmProtect", false, .leaderlessRearm, true, false)
  , ("integratedConsumeRearmProtect", true, .leaderlessRearm, true, false)
  , ("boundedReady", false, .original, false, true)
  , ("integratedReady", false, .noSourceRearm, false, true)
  , ("boundedReadyProtect", false, .original, true, true)
  , ("integratedReadyProtect", false, .noSourceRearm, true, true)
  , ("integratedRearmReadyProtect", false, .leaderlessRearm, true, true)
  , ("boundedConsumeReadyProtect", true, .original, true, true)
  , ("integratedConsumeRearmReadyProtect", true, .leaderlessRearm, true, true) ]

end PPLLBirthPatch
