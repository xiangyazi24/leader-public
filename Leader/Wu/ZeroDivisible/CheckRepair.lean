import Leader.Wu.ZeroDivisible.OverwritingGeneration

/-!
# Round-five CHECK repairs of zdivOWF

Two independent obstructions require two local changes. Preserve controls
already in transit when a stale outcome would reissue its own verdict, and
release an aligned penultimate equality facing a terminal comparison wave.
No fields or payloads are added. All other stages use the original zdivOWF
definitions, including original R1 maintenance and terminal-only F1.
These are experimental candidates, not a global liveness theorem.
-/

namespace PPLLAstraR5Repair

open PPLL PPLLRepair PPLLBirthPatch PPLLBirthPatchM2 PPLLPostElectionGuard
open PPLLFableDesignR1 PPLLAstraDesign2 PPLLAstraDesign3

/-- Selective preservation keeps A3--A6; the comparator keeps every token. -/
structure Cfg where
  selective : Bool := true
  deriving Repr

/-- Fixed original zdivOWF switches: no additional head overwrite. -/
def sourceCfg : PPLLFableZDiv.Cfg :=
  { wave := true, outcome := true, arrive := true }

/-- Whether an existing token must survive this CHECK result write. -/
def preserveToken {ψ : Nat} (c : Cfg) (u : AgentState ψ) : Bool :=
  match u.path2 with
  | none => false
  | some p => !c.selective || (3 ≤ p.action && p.action ≤ 6)

/-- Preserve an in-flight control; otherwise keep the original result writer. -/
def setResult {ψ : Nat} (c : Cfg) (u : AgentState ψ) : AgentState ψ :=
  if preserveToken c u then u else checkSigSetResult u

/-- Existing equality release plus Candidate E's terminal-C2 release.
The second branch requires consecutive, aligned occupied main paths. -/
def releaseEqual {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ) : AgentState ψ :=
  if r.state = .depart ∧ aligned r ∧ l.state = .equal ∧ aligned l ∧
      l.label.val < ψ - 1 then
    { l with state := .depart }
  else
    match l.path, r.path with
    | .some ll _, .some rl _ =>
      if r.state = .compare2 ∧ r.label = ⟨ψ - 1, by omega⟩ ∧
          aligned r ∧ l.state = .equal ∧ aligned l ∧ ll + 1 = rl then
        { l with state := .depart }
      else l
    | _, _ => l

/-- Original CHECK ordering with exactly the two experimental changes. -/
def checkSource {ψ : Nat} (hψ : ψ > 0) (c : Cfg)
    (l r : AgentState ψ) : AgentState ψ × AgentState ψ :=
  let ready (u : AgentState ψ) :=
    if waveState u.state ∨ u.state = .congest ∨ u.state = .done then u
    else checkSigSetReadyGuarded u
  let l := ready l
  let r := ready r
  let l := releaseEqual hψ l r
  let l := checkSigCheckL hψ l
  let r := checkSigCheckR hψ l r
  let l := setResult c l
  let r := setResult c r
  if r.label = ⟨ψ - 1, by omega⟩ ∧ r.state = .equal then
    (l, { r with leader := true }) else (l, r)

/-- Literal original prefix and suffix around the modified CHECK stage. -/
def beforeElimination {ψ : Nat} (hψ : ψ > 0) (κ : Nat) (c : Cfg)
    (l r : AgentState ψ) : AgentState ψ × AgentState ψ :=
  let q := pPsiProbeWall hψ l r
  let q := PPLLFableZDiv.genSigOverwrite hψ κ true 0 q.1 q.2
  let q := cleanSource hψ q.1 q.2
  let q := releaseSource hψ q.1 q.2
  let q := eliminateSig hψ q.1 q.2
  let q := PPLLFableZDiv.moveSourceF hψ sourceCfg q.1 q.2
  let q := (dropStale q.1, dropStale q.2)
  let q := preCheckReset q.1 q.2
  let q := (normalizeReady q.1, normalizeReady q.2)
  let q := checkSource hψ c q.1 q.2
  let q := disappear hψ q.1 q.2
  let q := repair .readyAck q.1 q.2
  let q := compareLifecycle κ q.1 q.2
  suppressSigResetKill hψ q.1 q.2

/-- Full raw transition; bounded simulators reify its actual output. -/
def pipeline {ψ : Nat} (hψ : ψ > 0) (κ : Nat) (c : Cfg)
    (l r : AgentState ψ) : AgentState ψ × AgentState ψ :=
  let q := beforeElimination hψ κ c l r
  let q := k4Kernel hψ q.1 q.2
  let q := writeWithBundle hψ q.1 q.2
  conserve .head l r q

/-- Names shared by the exact census and random-walk dispatchers. -/
def variants : List (String × Cfg) :=
  [("r5ESelective", { selective := true }),
   ("r5EBroad", { selective := false })]

/-- The common conserve guard still prevents removal of the last leader. -/
theorem pipeline_nonempty {ψ : Nat} (hψ : ψ > 0) (κ : Nat) (c : Cfg)
    (l r : AgentState ψ) (h : l.leader = true ∨ r.leader = true) :
    (pipeline hψ κ c l r).1.leader = true ∨
      (pipeline hψ κ c l r).2.leader = true := by
  exact conserve_nonempty .head l r _ h

end PPLLAstraR5Repair
