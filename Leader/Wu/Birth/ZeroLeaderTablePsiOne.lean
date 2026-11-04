import Leader.Wu.Protocol.BoundedProtocol

/-!
# Four-state zero-leader local closure at ψ = 1 and κ = 1

This file certifies the finite raw-state computation used by the bounded
zero-leader investigation.  It is deliberately local: no bounded lift,
configuration predicate, schedule theorem, or producer refutation is claimed
here.
-/

namespace ZZZeroLeaderFinite

open PPLL PPLLRepair

set_option autoImplicit false

abbrev hψ : 0 < 1 := by decide

/-- The neutral raw state from which the local closure is generated. -/
def neutral : AgentState 1 where
  leader := false
  probe := false
  phase := false
  bit := false
  wait := false
  state := .none
  path := .bot
  reset := false
  carry := false
  count := 0
  label := 0
  h_field := false
  path2 := none
  path3 := none
  path4 := none
  path5 := none
  p := false
  p_carry := false
  reset_cmd := false
  echo := false
  signal_B := 0
  bullet := 0
  shield := false
  write_state := .none
  write := .none
  last := false
  last_set := false
  last_unset := false
  b_carry := false
  gen_ws := false
  ws_echo := false
  signal_ws := false

/-- Names for the four states in the local closure. -/
inductive Code4 where
  | A | B | C | D
  deriving DecidableEq, Repr

/-- The four states vary only in reset, h_field, and the reset-determined
write state. -/
def cell : Code4 → AgentState 1
  | .A => neutral
  | .B => { neutral with h_field := true }
  | .C => { neutral with reset := true, write_state := .depart }
  | .D => { ({ neutral with reset := true, write_state := .depart }) with
      h_field := true }

/-- The next initiator code depends only on the old initiator code. -/
def leftNext : Code4 → Code4
  | .A => .B
  | .B => .A
  | .C => .B
  | .D => .A

/-- The next responder code also depends only on the old initiator code. -/
def rightNext : Code4 → Code4
  | .A => .C
  | .B => .D
  | .C => .C
  | .D => .C

/-- All sixteen ordered pairs follow the displayed four-row table.  The
responder input is immaterial for this family. -/
theorem pair_transition (l r : Code4) :
    ppllSaturatedNoCollision hψ 1 (cell l) (cell r) =
      (cell (leftNext l), cell (rightNext l)) := by
  cases l <;> cases r <;> decide

theorem transition_AA :
    ppllSaturatedNoCollision hψ 1 (cell .A) (cell .A) =
      (cell .B, cell .C) := pair_transition .A .A
theorem transition_AB :
    ppllSaturatedNoCollision hψ 1 (cell .A) (cell .B) =
      (cell .B, cell .C) := pair_transition .A .B
theorem transition_AC :
    ppllSaturatedNoCollision hψ 1 (cell .A) (cell .C) =
      (cell .B, cell .C) := pair_transition .A .C
theorem transition_AD :
    ppllSaturatedNoCollision hψ 1 (cell .A) (cell .D) =
      (cell .B, cell .C) := pair_transition .A .D

theorem transition_BA :
    ppllSaturatedNoCollision hψ 1 (cell .B) (cell .A) =
      (cell .A, cell .D) := pair_transition .B .A
theorem transition_BB :
    ppllSaturatedNoCollision hψ 1 (cell .B) (cell .B) =
      (cell .A, cell .D) := pair_transition .B .B
theorem transition_BC :
    ppllSaturatedNoCollision hψ 1 (cell .B) (cell .C) =
      (cell .A, cell .D) := pair_transition .B .C
theorem transition_BD :
    ppllSaturatedNoCollision hψ 1 (cell .B) (cell .D) =
      (cell .A, cell .D) := pair_transition .B .D

theorem transition_CA :
    ppllSaturatedNoCollision hψ 1 (cell .C) (cell .A) =
      (cell .B, cell .C) := pair_transition .C .A
theorem transition_CB :
    ppllSaturatedNoCollision hψ 1 (cell .C) (cell .B) =
      (cell .B, cell .C) := pair_transition .C .B
theorem transition_CC :
    ppllSaturatedNoCollision hψ 1 (cell .C) (cell .C) =
      (cell .B, cell .C) := pair_transition .C .C
theorem transition_CD :
    ppllSaturatedNoCollision hψ 1 (cell .C) (cell .D) =
      (cell .B, cell .C) := pair_transition .C .D

theorem transition_DA :
    ppllSaturatedNoCollision hψ 1 (cell .D) (cell .A) =
      (cell .A, cell .C) := pair_transition .D .A
theorem transition_DB :
    ppllSaturatedNoCollision hψ 1 (cell .D) (cell .B) =
      (cell .A, cell .C) := pair_transition .D .B
theorem transition_DC :
    ppllSaturatedNoCollision hψ 1 (cell .D) (cell .C) =
      (cell .A, cell .C) := pair_transition .D .C
theorem transition_DD :
    ppllSaturatedNoCollision hψ 1 (cell .D) (cell .D) =
      (cell .A, cell .C) := pair_transition .D .D

/-- Extensional membership in the four-state local family. -/
def InFamily (s : AgentState 1) : Prop := ∃ c : Code4, s = cell c

/-- Arbitrary ordered interactions of family members remain in the family. -/
theorem pair_closed {l r : AgentState 1}
    (hl : InFamily l) (hr : InFamily r) :
    let q := ppllSaturatedNoCollision hψ 1 l r
    InFamily q.1 ∧ InFamily q.2 := by
  rcases hl with ⟨lc, rfl⟩
  rcases hr with ⟨rc, rfl⟩
  rw [pair_transition]
  exact ⟨⟨leftNext lc, rfl⟩, ⟨rightNext lc, rfl⟩⟩

/-- Every named family member has no leader. -/
theorem cell_zero_leader (c : Code4) : (cell c).leader = false := by
  cases c <;> rfl

/-- Membership in the family forces the leader bit to be false. -/
theorem inFamily_zero_leader {s : AgentState 1} (hs : InFamily s) :
    s.leader = false := by
  rcases hs with ⟨c, rfl⟩
  exact cell_zero_leader c

#print axioms pair_transition
#print axioms transition_AA
#print axioms transition_AB
#print axioms transition_AC
#print axioms transition_AD
#print axioms transition_BA
#print axioms transition_BB
#print axioms transition_BC
#print axioms transition_BD
#print axioms transition_CA
#print axioms transition_CB
#print axioms transition_CC
#print axioms transition_CD
#print axioms transition_DA
#print axioms transition_DB
#print axioms transition_DC
#print axioms transition_DD
#print axioms pair_closed
#print axioms cell_zero_leader
#print axioms inFamily_zero_leader

end ZZZeroLeaderFinite
