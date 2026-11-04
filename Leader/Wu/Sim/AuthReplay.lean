import Leader.Wu.Sim.AuthCarrier

/-!
# Replay an edge word under an AuthF variant (design exploration, not a proof)

`ppll-authf-replay VARIANT N PSI KAPPA SEED.json WORD` reads one configuration (a JSON
array of `n` agents in the `PPLLAuthSim` format), fires the physical edges of `WORD`
(comma separated; edge `i` is the interaction `(i, i+1 mod n)` with initiator `i`) and
prints one JSON line per step: the edge, the leader sites, and a compact per-cell summary
`state/path/path2-action/marks`.  The last line holds the final configuration.
-/

set_option autoImplicit false

open Lean

namespace PPLLAuthReplay

open PPLLAuthSim

def mainName (s : MainState) : String :=
  match s with
  | .produce => "produce" | .done => "done" | .depart => "depart" | .none => "none"
  | .congest => "congest" | .lock => "lock" | .compare1 => "compare1"
  | .compare2 => "compare2" | .eliminate_signal => "elim" | .CHECK_ready => "ready"
  | .equal => "equal" | .larger => "larger" | .less => "less" | .toss => "toss"
  | .toss_done => "toss_done"

def cell {ψ κ : Nat} (a : AuthB ψ κ) : String :=
  let s := a.core.erase
  let p := match s.path with | .bot => "_" | .some l b => s!"{l}.{b}"
  let t := match s.path2 with | none => "" | some t => s!" A{t.action}@{t.position}L{t.label}"
  let m := a.m
  let sc := if m.scope = .session then "s" else "l"
  s!"{if s.leader then "L:" else ""}{mainName s.state} {p}{t} [{m.path.val}{m.ctrl.val}{sc}{m.p2.val}{m.p4.val}{m.p5.val}]"

def run (variant : String) (n ψ κ : Nat) (seed : System.FilePath) (word : List Nat) : IO UInt32 := do
  if hψ : ψ > 0 then
    let tr ← IO.ofExcept (PPLLAuthSim.localTransition variant hψ κ)
    let j ← IO.ofExcept (Json.parse (← IO.FS.readFile seed))
    let mut c ← IO.ofExcept (PPLLAuthSim.decodeConfig (ψ := ψ) (κ := κ) n j)
    let summary := fun (c : Array (AuthB ψ κ)) =>
      Json.arr (c.map fun a => toJson (cell a))
    let leaders := fun (c : Array (AuthB ψ κ)) =>
      toJson ((List.range n).filter fun i => match c[i]? with | some a => a.core.leader | none => false)
    IO.println (Json.mkObj [("step", 0), ("leaders", leaders c), ("cells", summary c)]).compress
    let mut k : Nat := 0
    for e in word do
      k := k + 1
      if e ≥ n then throw (IO.userError s!"edge {e} out of range")
      let some a := c[e]? | throw (IO.userError "bad index")
      let some b := c[(e + 1) % n]? | throw (IO.userError "bad index")
      let q ← IO.ofExcept (tr a b)
      c := (c.set! e q.1).set! ((e + 1) % n) q.2
      IO.println (Json.mkObj [("step", toJson k), ("edge", toJson e), ("leaders", leaders c), ("cells", summary c)]).compress
    IO.println (Json.mkObj [("final", Json.arr (c.map PPLLAuthSim.encode))]).compress
    return 0
  else throw (IO.userError "psi must be positive")

end PPLLAuthReplay

def main (args : List String) : IO UInt32 := do
  match args with
  | [variant, n, ψ, κ, seed, word] =>
    match n.toNat?, ψ.toNat?, κ.toNat? with
    | some n, some ψ, some κ =>
      let w := if word.isEmpty then [] else (word.splitOn ",").filterMap String.toNat?
      PPLLAuthReplay.run variant n ψ κ seed w
    | _, _, _ => IO.eprintln "numeric arguments expected"; return 2
  | _ => IO.eprintln "usage: ppll-authf-replay VARIANT N PSI KAPPA SEED.json WORD"; return 2
