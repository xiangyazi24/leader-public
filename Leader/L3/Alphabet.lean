import Leader.L3.Params

/-!
# L3 local state alphabet

One agent's state is the full Cartesian product of the legal field ranges of the production
machine: `randomFullState` (`composed-full.mjs:1018-1043`, which samples every field
independently over its whole range) and the checker `assertAgent` (`composed-full.mjs:986-1013`).
No invariant ties fields together; every value of `Agent c` is a legal initial local state
(`main.tex:268-275`: "every combination of their legal values is admitted").

JS bits (`0/1`) are `Bool`.  Ranges:
* native `l, sh, sg : Bool`, bullet `b ∈ {0,1,2}`;
* `pack ∈ 0..b+1`, BANK `mode`, `bit`, `tok`, `lease ∈ 0..13(b+2)`;
* SMALL `OFF | SPENT | RUN j` with `j < K_* = 199`;
* bits `req grant C alpha m EU ED u beta topDirty rawKick`;
* LIVE-TOP digit `d < topA`;
* serializer record; `siLease ∈ 0..8t+4`; SI record with `j ∈ 0..t` and bits `busy z p a`
  (`randomFullState` samples them as bits; `assertAgent` does not check them);
* raw scanner token `none` or `j ∈ 1..t` with bits `z p a h m` (stored as `jm1 = j - 1 < t`);
* H code `h < 34t + 3` and `kH ∈ 0..t`;
* writer/checker packets: `OUT ∈ {E, U, D(v,T)}`, `IN ∈ {E, X, P(v,T), S(v,T)}` with `v < topA`,
  writer carry `OFF | W c`, checker carry `OFF | L c e`, writer base `NONE | SEEK | ZERO`.
-/

namespace L3

set_option autoImplicit false

/-- BANK modes (`composed-full.mjs:40`). -/
inductive Mode | RESET | RWAIT | ARMED | IWAIT | CSTART | CWAIT
  deriving DecidableEq, Repr

/-- BANK tokens (`composed-full.mjs:41`). -/
inductive BTok | E | RR | RL | IR | AL | CR0 | CR1 | CL0 | CL1
  deriving DecidableEq, Repr

/-- SMALL short-counter field: `'OFF' | 'SPENT' | 'RUN<j>'`, `j < K_*` (`composed-full.mjs:1001-1002`). -/
inductive Small | OFF | SPENT | RUN (j : Fin kStar)
  deriving DecidableEq, Repr

inductive SerPhase | C | B | F
  deriving DecidableEq, Repr
inductive SerOut | NEW | WAIT | DONE
  deriving DecidableEq, Repr
inductive SerProbe | NONE | PENDING | INTERNAL_OK | LEAF_OK
  deriving DecidableEq, Repr
inductive SerCert | IDLE | REQUESTED | RUNNING
  deriving DecidableEq, Repr
inductive SerWPhase | OFF | QUARANTINE | VALIDATING | CURRENT
  deriving DecidableEq, Repr

/-- Serializer record (`composed-full.mjs:204` `ser0`, ranges `1005-1008`). -/
structure Ser where
  phase : SerPhase
  out : SerOut
  probe : SerProbe
  cert : SerCert
  wphase : SerWPhase
  deriving DecidableEq, Repr

inductive SIKind | OFF | PREFIX | ROOT
  deriving DecidableEq, Repr
inductive SICur | NONE | BACK | SUM
  deriving DecidableEq, Repr

/-- SI record (`composed-full.mjs:205` `si0`, ranges `1011-1013`, `1030`). -/
structure SI (t : Nat) where
  kind : SIKind
  busy : Bool
  cur : SICur
  j : Fin (t + 1)
  z : Bool
  p : Bool
  a : Bool
  deriving DecidableEq, Repr

/-- Raw D1 scanner token (`composed-full.mjs:1031`); its index is `jm1 + 1 ∈ 1..t`. -/
structure RawTok (t : Nat) where
  jm1 : Fin t
  z : Bool
  p : Bool
  a : Bool
  h : Bool
  m : Bool
  deriving DecidableEq, Repr

/-- The raw scanner index `j ∈ 1..t`. -/
def RawTok.j {t : Nat} (r : RawTok t) : Nat := r.jm1.val + 1

inductive WBase | NONE | SEEK | ZERO
  deriving DecidableEq, Repr

/-- Outgoing packet `E | U | D(v,T)` (`composed-full.mjs:207-209`, `979-983`). -/
inductive OutTok (A : Nat) | E | U | D (v : Fin A) (T : Bool)
  deriving DecidableEq, Repr

/-- Incoming packet `E | X | P(v,T) | S(v,T)` (`composed-full.mjs:207-212`, `979-983`). -/
inductive InTok (A : Nat) | E | X | P (v : Fin A) (T : Bool) | S (v : Fin A) (T : Bool)
  deriving DecidableEq, Repr

/-- Writer carry `OFF | W c` (`composed-full.mjs:213-214`). -/
inductive WCarry | OFF | W (c : Bool)
  deriving DecidableEq, Repr

/-- Checker carry `OFF | L c e` (`composed-full.mjs:213`, `215`). -/
inductive QCarry | OFF | L (c e : Bool)
  deriving DecidableEq, Repr

/-- One agent's local state for compiled data `c`: the full Cartesian product of the field
ranges listed in the module docstring. -/
structure Agent (c : Compiled) where
  -- native (composed-gpt.mjs:324)
  l : Bool
  b : Fin 3
  sh : Bool
  sg : Bool
  -- PACK, BANK, SMALL (composed-gpt.mjs:325-326; composed-full.mjs:997-1002)
  pack : Fin (c.b + 2)
  mode : Mode
  bit : Bool
  tok : BTok
  lease : Fin (c.bankLeaseCap + 1)
  small : Small
  -- tokens, candidate, debt (composed-gpt.mjs:327-329)
  req : Bool
  grant : Bool
  C : Bool
  alpha : Bool
  m : Bool
  EU : Bool
  ED : Bool
  -- certificate namespaces (composed-full.mjs:217-227)
  u : Bool
  beta : Bool
  d : Fin c.topA
  ser : Ser
  siLease : Fin (c.siLeaseMax + 1)
  si : SI c.t
  rawKick : Bool
  rawTok : Option (RawTok c.t)
  h : Fin (34 * c.t + 3)
  kH : Fin (c.t + 1)
  wBase : WBase
  wOut : OutTok c.topA
  wIn : InTok c.topA
  wCarry : WCarry
  qOut : OutTok c.topA
  qIn : InTok c.topA
  qCarry : QCarry
  topDirty : Bool
  deriving DecidableEq, Repr

/-- `blankAgent` (`composed-gpt.mjs:323-331`) extended by `extendAgent`
(`composed-full.mjs:217-227`). -/
def Agent.blank (c : Compiled) : Agent c where
  l := false
  b := 0
  sh := false
  sg := false
  pack := ⟨0, by omega⟩
  mode := .RESET
  bit := false
  tok := .E
  lease := ⟨0, by omega⟩
  small := .OFF
  req := false
  grant := false
  C := false
  alpha := false
  m := false
  EU := false
  ED := false
  u := false
  beta := false
  d := ⟨0, c.topA_pos⟩
  ser := { phase := .C, out := .NEW, probe := .NONE, cert := .IDLE, wphase := .OFF }
  siLease := ⟨0, by omega⟩
  si := { kind := .OFF, busy := false, cur := .NONE, j := ⟨0, by omega⟩,
          z := false, p := false, a := true }
  rawKick := false
  rawTok := none
  h := ⟨0, by omega⟩
  kH := ⟨0, by omega⟩
  wBase := .NONE
  wOut := .E
  wIn := .E
  wCarry := .OFF
  qOut := .E
  qIn := .E
  qCarry := .OFF
  topDirty := false

end L3
