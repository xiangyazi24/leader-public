import Leader.Wu.ZeroDivisible.LockCycleRepairs

/-!
# Z-div experiments on ReadyAck

Variants of `PPLLAstraDesign3.pipeline .readyAck` for the divisible zero-leader
branch (ψ ∣ n, perfectly labelled, leaderless, arbitrary other fields).  The
only change is GENSIG (Algorithm 4): *overwriting generation* (controller's
proposal).  In ReadyAck the produce wave of a group G stops at any occupied
cell of G (Algorithm 4 line 4 needs `r.path = ⊥`).  Here the wave wipes the reached
cell's comparison fields (`path`, `path2`, `path4`, `path5`, `state`) and
continues; the cell then receives its own sub-signal from the reverse wave
(lines 6–12, unchanged).  In the overwriting variants a cell entering `produce` is wiped even when
its `path` is already `⊥` (its tokens go too).  Nothing else is touched: never `leader`, `shield`,
`bullet`, `signal_B`, `label`, `bit`, `probe`, the writer fields
(`path3`, `write*`, `gen_ws`, `ws_echo`, `signal_ws`), nor WAIT.

Two switches: `wave` (line 4 overwrites: a cell of label ≠ 0 behind a
`produce` cell is wiped unless it is already `produce`/`done`, i.e. already
part of this generation) and `head` (line 2 overwrites: the head starts
producing when `wait = 0` even if it holds a path; level 1 keeps a `depart`
head, level 2 wipes it too).  The `produce`/`done`
exclusion is needed for ψ ≥ 3: without it the edge `(u_i produce, u_{i+1} done)`
would wipe the freshly written own path of `u_{i+1}` again and the wave would
never complete.

## Outcome-first movement and arrival normalisation (2026-09-26, after the ruler census)

`run/verification/g62/ruler-closure/README.md` found that ReadyAck births a second
leader from clean ruler configurations.  Class (c): CHECK marks the terminal cell of a visiting
signal `larger` and issues the action-4 token there, but on the next interaction of the edge
(terminal, next head) SIGMOVE line 1 moves the terminal's sub-signal forward *before* the control
application turns the cell into `eliminate_signal`: `larger` is not in the blocking set
{lock, compare1, CHECK_ready} of `sigMoveStep1` (Algorithm.lean:462-470, thesis Algorithm 10).
The escaped sub-signal becomes `depart`, the train follows, and the signal is CHECKed again at
the next group.  Class (e): a sub-signal moving into a cell that still holds a stale `depart`
inherits that state (line 1 copies only `path`), is therefore never CHECKed
(`checkSigSetReady` excludes `depart`), and takes part in a BEQ instead.

Two switches, both local to SIGMOVE line 1:
* `outcome` (F1): a cell whose comparison outcome is pending does not move its sub-signal:
  `larger`/`less` at the terminal label (all labels with `outcomeAll`), `eliminate_signal`
  anywhere, `toss` at label 0.  The action-4 token issued on a terminal `larger` is then consumed
  on that cell in the same interaction (`sigMoveApplyControlConsume`), and `eliminateSig` clears
  the signal from the terminal backwards.
* `arrive` (F2): the receiving cell of line 1 takes state `none` when its state is a stale
  outcome or lifecycle state (`depart`, `equal`, `larger`, `less`, `toss_done`, `done`), so every
  arrival is CHECKed at its new group before it can be a BEQ partner.
-/

namespace PPLLFableZDiv

open PPLL PPLLRepair PPLLBirthPatch PPLLBirthPatchM2 PPLLPostElectionGuard
open PPLLFableDesignR1 PPLLAstraDesign2 PPLLAstraDesign3

/-- Wipe the comparison fields of a cell and put it into `produce`. -/
def wipeProduce {ψ : Nat} (u : AgentState ψ) : AgentState ψ :=
  { u with path := .bot, path2 := none, path4 := none, path5 := none, state := .produce }

/-- Algorithm 4 with overwriting lines 2 (`head`) and 4 (`wave`); WAIT and
lines 6–15 are `PPLLRepair`'s unchanged stages. -/
def genSigOverwrite {ψ : Nat} (hψ : ψ > 0) (κ : Nat) (wave : Bool) (head : Nat)
    (l r : AgentState ψ) : AgentState ψ × AgentState ψ :=
  let q := waitSaturated hψ κ l r
  let (l, r) := q
  -- line 2 (with `wave = false` and `head = 0` this is exactly `genSigSaturatedStart`)
  let l :=
    if l.leader = false ∧ l.label = ⟨0, hψ⟩ ∧ l.wait = false ∧
        (l.path = .bot ∨ (head ≥ 1 ∧ l.state ≠ .produce ∧ l.state ≠ .done ∧ (head ≥ 2 ∨ l.state ≠ .depart))) then
      (if wave ∨ head ≥ 1 then wipeProduce l else { l with state := .produce })
    else l
  -- line 4
  let r :=
    if r.label ≠ ⟨0, hψ⟩ ∧ l.state = .produce ∧
        (r.path = .bot ∨ (wave ∧ r.state ≠ .produce ∧ r.state ≠ .done)) then
      (if wave then wipeProduce r else { r with state := .produce })
    else r
  let q := genSigSaturatedEmit hψ l r
  let q := genSigSaturatedPropagate hψ q.1 q.2
  genSigSaturatedFinish hψ q.1 q.2

/-- Switches of a Z-div variant (all `false`/`0` = ReadyAck). -/
structure Cfg where
  wave : Bool := false
  head : Nat := 0
  outcome : Bool := false
  outcomeAll : Bool := false
  arrive : Bool := false
  deriving Repr

/-- A comparison outcome that has not yet been applied to the signal (F1). -/
def outcomePending {ψ : Nat} (all : Bool) (u : AgentState ψ) : Bool :=
  ((u.state = .larger ∨ u.state = .less) ∧ (all ∨ u.label.val = ψ - 1)) ∨
    u.state = .eliminate_signal ∨ (u.state = .toss ∧ u.label.val = 0)

/-- Stale receiver states that would exempt an arriving sub-signal from CHECK (F2). -/
def staleReceiver {ψ : Nat} (u : AgentState ψ) : Bool :=
  u.state = .depart ∨ u.state = .equal ∨ u.state = .larger ∨ u.state = .less ∨
    u.state = .toss_done ∨ u.state = .done

/-- SIGMOVE line 1 (`sigMoveStep1With .dropMisaligned`) with the F1/F2 switches. -/
def sigMoveStep1F {ψ : Nat} (c : Cfg) (l r : AgentState ψ) :
    AgentState ψ × AgentState ψ :=
  match l.path, r.path with
  | .some pathLabel _, .bot =>
    let blocked : Bool := blockingState l || (c.outcome && outcomePending c.outcomeAll l)
    if !blocked then
      if r.state ≠ MainState.produce ∨ pathLabel ≠ ψ - 1 then
        ({ l with path := .bot, state := .none },
         { r with path := l.path,
                  state := if c.arrive && staleReceiver r then .none else r.state })
      else (l, r)
    else (l, r)
  | _, _ => (l, r)

/-- `PPLLAstraDesign3.moveSource` with line 1 replaced (identical for the default `Cfg`). -/
def moveSourceF {ψ : Nat} (hψ : ψ > 0) (c : Cfg) (l r : AgentState ψ) :
    AgentState ψ × AgentState ψ :=
  let nextLabel : Fin ψ := ⟨(l.label.val + 1) % ψ, Nat.mod_lt _ hψ⟩
  let l := if l.leader = true ∨ (r.leader = true ∧ r.label ≠ nextLabel) then
    clearCmp l else l
  let r := if r.leader = true then clearCmp r else r
  let (l, r) := if l.state = .done then (l, r)
    else sigMoveStep1F c l r
  let (l, r) := PPLLFableDesignR1.moveTokens l r
  let (l, r) := leaderWall l r
  let l := sigMoveApplyControlConsume hψ l
  let r := sigMoveApplyControlConsume hψ r
  let l := if r.state = .depart ∧ l.label.val < ψ - 1 ∧ l.state = .CHECK_ready then
    { l with state := .depart } else l
  (l, r)

/-- `PPLLAstraDesign3.beforeElimination hψ κ .readyAck` with GENSIG and SIGMOVE replaced. -/
def beforeElimination {ψ : Nat} (hψ : ψ > 0) (κ : Nat) (c : Cfg)
    (l r : AgentState ψ) : AgentState ψ × AgentState ψ :=
  let q := pPsiProbeWall hψ l r
  let q := genSigOverwrite hψ κ c.wave c.head q.1 q.2
  let q := cleanSource hψ q.1 q.2
  let q := releaseSource hψ q.1 q.2
  let q := eliminateSig hψ q.1 q.2
  let q := moveSourceF hψ c q.1 q.2
  let q := (dropStale q.1, dropStale q.2)
  let q := preCheckReset q.1 q.2
  let q := (normalizeReady q.1, normalizeReady q.2)
  let q := checkSource hψ q.1 q.2
  let q := disappear hψ q.1 q.2
  let q := repair .readyAck q.1 q.2
  let q := compareLifecycle κ q.1 q.2
  suppressSigResetKill hψ q.1 q.2

def pipeline {ψ : Nat} (hψ : ψ > 0) (κ : Nat) (c : Cfg)
    (l r : AgentState ψ) : AgentState ψ × AgentState ψ :=
  let q := beforeElimination hψ κ c l r
  let q := k4Kernel hψ q.1 q.2
  let q := writeWithBundle hψ q.1 q.2
  conserve .head l r q

/-- `zdivRA` = ReadyAck rebuilt through this file (control: must equal
`astR3ReadyAckHeadK4`); `zdivOW` = overwriting wave, ReadyAck head (starts only
on `path = ⊥`); `zdivOWH` = wave + head overwriting a head that is not
`produce`/`done`/`depart` (a head whose own signal has not left is kept);
`zdivOWHD` = wave + head overwriting also a `depart` head (the head regenerates
every WAIT cycle, destroying its own in-flight signal cell).
`raF*` are ReadyAck with the SIGMOVE switches only (F1 = `outcome`, F2 = `arrive`,
F1a = `outcomeAll`); `zdivOWF*` combine them with the overwriting wave. -/
def variants : List (String × Cfg) :=
  [ ("zdivRA", {}), ("zdivOW", { wave := true }), ("zdivOWH", { wave := true, head := 1 })
  , ("zdivOWHD", { wave := true, head := 2 })
  , ("raF1", { outcome := true }), ("raF2", { arrive := true })
  , ("raF", { outcome := true, arrive := true })
  , ("raFa", { outcome := true, outcomeAll := true, arrive := true })
  , ("zdivOWF1", { wave := true, outcome := true })
  , ("zdivOWF", { wave := true, outcome := true, arrive := true })
  , ("zdivOWFa", { wave := true, outcome := true, outcomeAll := true, arrive := true }) ]

theorem pipeline_nonempty {ψ : Nat} (hψ : ψ > 0) (κ : Nat) (c : Cfg)
    (l r : AgentState ψ) (h : l.leader = true ∨ r.leader = true) :
    (pipeline hψ κ c l r).1.leader = true ∨ (pipeline hψ κ c l r).2.leader = true := by
  exact conserve_nonempty .head l r _ h

end PPLLFableZDiv
