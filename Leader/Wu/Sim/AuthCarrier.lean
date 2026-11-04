import Lean.Data.Json
import Leader.Wu.Sim.BoundedCodec
import Leader.Wu.Sim.RawCodec
import Leader.Wu.Authorization.ProvenanceMarks

/-!
# Bounded carrier and JSON codec for the AuthF census tools

Design-exploration support, not a proof certificate.  A census agent is a bounded
`BoundedAgentState ψ κ` core plus the six AuthF sidecars (`Marks`).  The local transition
erases the core, runs `PPLLAuthF.pipeline` (or the `zdivOWFlift` control), and reifies
the output core through the checked bounded decoder, as `PPLLDiskCensus.reify` does.

JSON: an agent is `{"core": <PPLLSimCodec state>, "m": [path, ctrl, p2, p4, p5, scope]}`
with colours in `0..2` and scope `0` = line, `1` = session.  A plain core object (no
`"core"` key) decodes with all marks `0` and scope line.
-/

set_option autoImplicit false

open Lean

namespace PPLLAuthSim
private theorem path_wire {psi kappa : Nat} (b : BoundedAgentState psi kappa) :
    PPLLSimRawCodec.ePath b.erase.path = PPLLSimCodec.ePath b.path := by
  rcases b with
    ⟨leader, probe, phase, bit, wait, state, path, reset, carry,
     count, label, h_field, path2, path3, path4, path5, p, p_carry,
     reset_cmd, echo, signal_B, bullet, shield, write_state, write,
     last, last_set, last_unset, b_carry, gen_ws, ws_echo, signal_ws⟩
  cases path <;> rfl
end PPLLAuthSim

namespace PPLLAuthSim
private theorem path2_wire {psi kappa : Nat} (b : BoundedAgentState psi kappa) :
    PPLLSimRawCodec.eP2 b.erase.path2 = PPLLSimCodec.eP2 b.path2 := by
  rcases b with
    ⟨leader, probe, phase, bit, wait, state, path, reset, carry,
     count, label, h_field, path2, path3, path4, path5, p, p_carry,
     reset_cmd, echo, signal_B, bullet, shield, write_state, write,
     last, last_set, last_unset, b_carry, gen_ws, ws_echo, signal_ws⟩
  cases path2 <;> rfl
end PPLLAuthSim

namespace PPLLAuthSim
private theorem path3_wire {psi kappa : Nat} (b : BoundedAgentState psi kappa) :
    PPLLSimRawCodec.eP3 b.erase.path3 = PPLLSimCodec.eP3 b.path3 := by
  rcases b with
    ⟨leader, probe, phase, bit, wait, state, path, reset, carry,
     count, label, h_field, path2, path3, path4, path5, p, p_carry,
     reset_cmd, echo, signal_B, bullet, shield, write_state, write,
     last, last_set, last_unset, b_carry, gen_ws, ws_echo, signal_ws⟩
  cases path3 <;> rfl
end PPLLAuthSim

namespace PPLLAuthSim
private theorem path4_wire {psi kappa : Nat} (b : BoundedAgentState psi kappa) :
    PPLLSimRawCodec.eClean b.erase.path4 = PPLLSimCodec.eClean b.path4 := by
  rcases b with
    ⟨leader, probe, phase, bit, wait, state, path, reset, carry,
     count, label, h_field, path2, path3, path4, path5, p, p_carry,
     reset_cmd, echo, signal_B, bullet, shield, write_state, write,
     last, last_set, last_unset, b_carry, gen_ws, ws_echo, signal_ws⟩
  cases path4 with
  | none => rfl
  | some q => cases q with
    | mk l b => cases l <;> rfl
end PPLLAuthSim

namespace PPLLAuthSim
private theorem path5_wire {psi kappa : Nat} (b : BoundedAgentState psi kappa) :
    PPLLSimRawCodec.eClean b.erase.path5 = PPLLSimCodec.eClean b.path5 := by
  rcases b with
    ⟨leader, probe, phase, bit, wait, state, path, reset, carry,
     count, label, h_field, path2, path3, path4, path5, p, p_carry,
     reset_cmd, echo, signal_B, bullet, shield, write_state, write,
     last, last_set, last_unset, b_carry, gen_ws, ws_echo, signal_ws⟩
  cases path5 with
  | none => rfl
  | some q => cases q with
    | mk l b => cases l <;> rfl
end PPLLAuthSim
namespace PPLLAuthSim
/-- Erasure preserves the bounded codec's exact wire object. -/
theorem encodeState_erase {psi kappa : Nat}
    (b : BoundedAgentState psi kappa) :
    PPLLSimRawCodec.encodeState b.erase = PPLLSimCodec.encodeState b := by
  unfold PPLLSimRawCodec.encodeState PPLLSimCodec.encodeState
  simp only [path_wire, path2_wire, path3_wire, path4_wire, path5_wire]
  rfl
end PPLLAuthSim


namespace PPLLAuthSim

open PPLLAuthF

structure Marks where
  path : Fin 3 := 0
  ctrl : Fin 3 := 0
  p2 : Fin 3 := 0
  p4 : Fin 3 := 0
  p5 : Fin 3 := 0
  scope : P2Scope := .line
  /-- EpisodeCap counter (`PPLLAuthSeam.seamStepE`): counted session
  openings at this physical head.  Threaded beside `AuthState` by the seam glue, not
  part of `toState`/`marksOf`; always 0 for every variant without `episodeCap`. -/
  episodes : Fin 3 := 0
  /-- EpisodeCap arm latch (`PPLLAuthSeam.seamStepA`, `episodeLatch`): set once the cell has
  carried `reset_cmd` or been a leader (graced variants: a countdown); threaded like `episodes`. -/
  armed : Nat := 0
  deriving DecidableEq, Repr, Inhabited

structure AuthB (ψ κ : Nat) where
  core : BoundedAgentState ψ κ
  m : Marks
  deriving DecidableEq

def AuthB.leader {ψ κ : Nat} (a : AuthB ψ κ) : Bool := a.core.leader
def AuthB.hole {ψ κ : Nat} (a : AuthB ψ κ) : Bool :=
  match a.core.path with | .bot => true | _ => false

def toState {ψ κ : Nat} (a : AuthB ψ κ) : AuthState ψ :=
  { core := a.core.erase, path_mark := a.m.path, ctrl_mark := a.m.ctrl,
    path2_scope := a.m.scope, path2_mark := a.m.p2, path4_mark := a.m.p4, path5_mark := a.m.p5 }

def marksOf {ψ : Nat} (u : AuthState ψ) : Marks :=
  { path := u.path_mark, ctrl := u.ctrl_mark, p2 := u.path2_mark, p4 := u.path4_mark,
    p5 := u.path5_mark, scope := u.path2_scope }

def reifyCore {ψ κ : Nat} (s : AgentState ψ) : Except String (BoundedAgentState ψ κ) :=
  PPLLSimCodec.decodeState (psi := ψ) (kappa := κ) (PPLLSimRawCodec.encodeState s)

def encodeMarks (m : Marks) : Json :=
  Json.arr #[toJson m.path.val, toJson m.ctrl.val, toJson m.p2.val, toJson m.p4.val,
    toJson m.p5.val, toJson (if m.scope = .session then 1 else 0), toJson m.episodes.val,
    toJson m.armed]

def encode {ψ κ : Nat} (a : AuthB ψ κ) : Json :=
  Json.mkObj [("core", PPLLSimCodec.encodeState a.core), ("m", encodeMarks a.m)]

/-- Interning key: compact and injective (core JSON plus eight digits). -/
def key {ψ κ : Nat} (a : AuthB ψ κ) : String :=
  (PPLLSimCodec.encodeState a.core).compress ++ "|" ++
    s!"{a.m.path.val}{a.m.ctrl.val}{a.m.p2.val}{a.m.p4.val}{a.m.p5.val}{if a.m.scope = .session then 1 else 0}{a.m.episodes.val}{a.m.armed}"

def fin3 (j : Json) : Except String (Fin 3) := do
  let v ← j.getNat?
  if h : v < 3 then return ⟨v, h⟩ else throw s!"colour {v} out of range"

def decodeMarks (j : Json) : Except String Marks := do
  let a ← j.getArr?
  if a.size < 6 || a.size > 8 then throw "marks: expected 6 to 8 entries"
  let sc ← a[5]!.getNat?
  let ep ← if h : 6 < a.size then fin3 a[6] else pure 0
  let ar ← if h : 7 < a.size then a[7].getNat? else pure 0
  return { path := ← fin3 a[0]!, ctrl := ← fin3 a[1]!, p2 := ← fin3 a[2]!, p4 := ← fin3 a[3]!,
           p5 := ← fin3 a[4]!, scope := if sc = 1 then .session else .line, episodes := ep,
           armed := ar }

def decode {ψ κ : Nat} (j : Json) : Except String (AuthB ψ κ) := do
  match j.getObjVal? "core" with
  | .ok c =>
    let core ← PPLLSimCodec.decodeState (psi := ψ) (kappa := κ) c
    let m ← match j.getObjVal? "m" with
      | .ok mj => decodeMarks mj
      | .error _ => pure {}
    return ⟨core, m⟩
  | .error _ =>
    let core ← PPLLSimCodec.decodeState (psi := ψ) (kappa := κ) j
    return ⟨core, {}⟩

def decodeConfig {ψ κ : Nat} (n : Nat) (j : Json) : Except String (Array (AuthB ψ κ)) := do
  let a ← j.getArr?
  if a.size != n then throw s!"configuration length {a.size}, expected {n}"
  let mut out := #[]
  for i in [0:n] do
    match decode (ψ := ψ) (κ := κ) a[i]! with
    | .ok s => out := out.push s
    | .error e => throw s!"states[{i}]: {e}"
  return out

/-- The local transition of an AuthF variant on the bounded carrier. -/
def localTransition (variant : String) {ψ : Nat} (hψ : ψ > 0) (κ : Nat) :
    Except String (AuthB ψ κ → AuthB ψ κ → Except String (AuthB ψ κ × AuthB ψ κ)) :=
  match PPLLAuthF.variants.find? (fun t => t.1 == variant) with
  | none => .error s!"unknown variant {variant}"
  | some (_, c) => .ok fun a b => do
      let q := match c with
        | some c => PPLLAuthF.pipeline hψ κ c (toState a) (toState b)
        | none => PPLLAuthF.zdivOWFLift hψ κ (toState a) (toState b)
      let a' ← (reifyCore (κ := κ) q.1.core).mapError fun e => s!"{variant}: left output out of domain ({e})"
      let b' ← (reifyCore (κ := κ) q.2.core).mapError fun e => s!"{variant}: right output out of domain ({e})"
      pure (⟨a', marksOf q.1⟩, ⟨b', marksOf q.2⟩)

end PPLLAuthSim
