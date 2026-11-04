import Leader.Core.Basic

/-!
# Agent State for Protocol P_PLL

The complete state of each agent in the P_PLL protocol, following Algorithm 1 (p.14).
Each agent on the directed ring carries ~30 variables. We encode them as a single
structure `AgentState` parameterized by the knowledge parameter ψ.

This file currently uses `Nat`/`Int` for several bounded pseudocode fields, so
it is an infinite over-approximation of the intended finite state space.  See
`PPLLCounterexample.countFamily_injective`.  A space-complexity theorem requires
refactoring those fields to `Fin`-bounded types (or a reachable-value invariant).
-/

/-! ## Enumeration types for protocol states -/

/-- The main state machine variable (Algorithm 1, line 3).
Controls signal generation, comparison, checking, and movement. -/
inductive MainState where
  | produce
  | done
  | depart
  | none
  | congest
  | lock
  | compare1
  | compare2
  | eliminate_signal
  | CHECK_ready
  | equal
  | larger
  | less
  | toss
  | toss_done
  deriving DecidableEq, Repr

/-- The write state for the stabilizing phase's overwriting signals.
Algorithm 1 lists `increment_WS_done` but omits `none`, while Algorithms 16 and
20 assign `none`; the executable model includes the union of the listed and
operationally assigned values. -/
inductive WriteState where
  | depart
  | ready
  | increment_WS
  | increment_WS_done
  | done
  | equal
  | larger
  | less
  | produce
  | overwrite
  | move_flip
  | move
  | increment_group
  | none
  deriving DecidableEq, Repr

/-- The write action type (Algorithm 1). -/
inductive WriteAction where
  | overwrite
  | move_flip
  | move
  | increment_group
  | none
  deriving DecidableEq, Repr

/-- Leader election output: either leader or follower. -/
inductive LeaderOutput where
  | leader
  | follower
  deriving DecidableEq, Repr

/-! ## Path information -/

/-- Sub-signal path information. `bot` means no information;
`some label bit` carries the label index and bit value. -/
inductive PathInfo where
  | bot
  | some (label : Nat) (bit : Nat)
  deriving DecidableEq, Repr

/-- Path2 information for signal comparison.
Carries (label, bit, position, action_code). -/
structure Path2Info where
  label : Nat
  bit : Nat
  position : Nat
  action : Nat
  deriving DecidableEq, Repr

/-- Path3 information for overwriting signals.
Carries (label, bit, write_flag). -/
structure Path3Info where
  label : Nat
  bit : Nat
  flag : Nat
  deriving DecidableEq, Repr

/-! ## The complete agent state -/

/-- Complete state record for the current P_PLL encoding.
Parameterized by ψ (the knowledge parameter, ψ = ⌈log log n⌉ + O(1)). Fields
represented by `Nat`/`Int` intentionally over-approximate the bounded domains
in Algorithm 1 and do not yet certify finite-state complexity. -/
structure AgentState (ψ : Nat) where
  leader : Bool
  probe : Bool
  phase : Bool
  bit : Bool
  wait : Bool
  state : MainState
  path : PathInfo
  reset : Bool
  carry : Bool
  count : Nat
  label : Fin ψ
  h_field : Bool
  path2 : Option Path2Info
  path3 : Option Path3Info
  path4 : Option (Int × Nat)
  path5 : Option (Int × Nat)
  p : Bool
  p_carry : Bool
  reset_cmd : Bool
  echo : Bool
  -- Algorithm 1 declares exactly `{0,1}`.
  signal_B : Fin 2
  bullet : Fin 3
  shield : Bool
  write_state : WriteState
  write : WriteAction
  last : Bool
  last_set : Bool
  last_unset : Bool
  b_carry : Bool
  gen_ws : Bool
  ws_echo : Bool
  signal_ws : Bool
  deriving DecidableEq, Repr

namespace AgentState

/-- Membership in the bounded value domains declared by Algorithm 1.

The record uses `Nat`/`Int` as an implementation convenience; this predicate
recovers the intended ranges. `path4`/`path5` also admit the `-1` cleaning
sentinel used by Algorithm 5 even though Algorithm 1 omits it from the listed
domain. This is only a value-range predicate, not the stronger coherence
invariant relating signals to their source groups. -/
def inProtocolDomain {ψ : Nat} (κ : Nat) (s : AgentState ψ) : Prop :=
  s.count ≤ κ ∧
  (match s.path with
   | .bot => True
   | .some label bit => label < ψ ∧ bit ≤ 1) ∧
  (match s.path2 with
   | none => True
   | some p => p.label < ψ ∧ p.bit ≤ 1 ∧ p.position ≤ ψ ∧
       1 ≤ p.action ∧ p.action ≤ 6) ∧
  (match s.path3 with
   | none => True
   | some p => p.label < ψ ∧ p.bit ≤ 1 ∧ p.flag ≤ 1) ∧
  (match s.path4 with
   | none => True
   | some (label, bit) => (-1 : Int) ≤ label ∧ label < Int.ofNat ψ ∧ bit ≤ 1) ∧
  (match s.path5 with
   | none => True
   | some (label, bit) => (-1 : Int) ≤ label ∧ label < Int.ofNat ψ ∧ bit ≤ 1)

/-- The output function for leader election: an agent outputs `leader` iff
its `leader` field is true. -/
def outputFn {ψ : Nat} (s : AgentState ψ) : LeaderOutput :=
  if s.leader then .leader else .follower

/-- Whether this agent is a leader. -/
def isLeader {ψ : Nat} (s : AgentState ψ) : Bool := s.leader

end AgentState

/-! ## The P_PLL protocol as a PopulationProtocol -/

/-- The output function predicate: is this output a leader? -/
def isLeaderOutput : LeaderOutput → Bool
  | .leader => true
  | .follower => false
