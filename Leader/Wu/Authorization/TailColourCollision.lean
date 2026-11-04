import Leader.Wu.Authorization.ResetDrain
import Leader.Wu.Authorization.BitFrozenClosure

/-!
# A colour collision in the proposed CHECK tail cleanup word

For `ψ=4` and two adjacent blocks, the old tail-debt colour `1` can equal
`fresh3 0 0`. The fixed word `[7,6,5,4]` then leaves an old X departure
session-stamped. This refutes that word's claimed `BoundarySessionRoot`
endpoint, not the existence of a different successful word.
-/
namespace PPLLAuthCheckTailCollision

open PPLL PPLLAuthF PPLLAuthResetDrain
set_option autoImplicit false

def base (label : Fin 4) : AgentState 4 :=
  { leader := false, probe := false, phase := false, bit := false,
    wait := false, state := .depart, path := .some label.val 0,
    reset := false, carry := false, count := 0, label := label,
    h_field := false, path2 := none, path3 := none,
    path4 := none, path5 := none, p := false, p_carry := false,
    reset_cmd := false, echo := false, signal_B := 0, bullet := 0,
    shield := false, write_state := .none, write := .none,
    last := false, last_set := false, last_unset := false,
    b_carry := false, gen_ws := false, ws_echo := false,
    signal_ws := false }

def physLabel (i : Fin 8) : Fin 4 :=
  ⟨i.val % 4, Nat.mod_lt _ (by omega)⟩

/-- B has colour 0; X has path colour 0 and only its suffix X₁..X₃
has old control colour 1. The X head is already lineage departed. -/
def seed (i : Fin 8) : AuthState 4 :=
  { core := base (physLabel i), path_mark := 0,
    ctrl_mark := if 4 < i.val then 1 else 0,
    path2_scope := .line, path2_mark := 0,
    path4_mark := 0, path5_mark := 0 }

def ring : DirectedRing 8 := ⟨by omega⟩

def afterWrap : Fin 8 → AuthState 4 :=
  authRun (by omega : 0 < 4) 2 authFplusmcc ring seed [7]

def afterTwoEdges : Fin 8 → AuthState 4 :=
  authRun (by omega : 0 < 4) 2 authFplusmcc ring seed [7, 6]

def afterThreeEdges : Fin 8 → AuthState 4 :=
  authRun (by omega : 0 < 4) 2 authFplusmcc ring seed [7, 6, 5]

def afterTail : Fin 8 → AuthState 4 :=
  authRun (by omega : 0 < 4) 2 authFplusmcc ring seed [7, 6, 5, 4]

theorem fresh_colour_collision : fresh3 0 0 = (1 : ProvColor) := by rfl

set_option maxHeartbeats 6000000 in
set_option maxRecDepth 16384 in
/-- The wrap starts a boundary session using exactly the old debt colour. -/
theorem wrap_head_lock :
    (afterWrap 0).core.state = .lock ∧
      (afterWrap 0).ctrl_mark = 1 ∧
      (afterWrap 7).ctrl_mark = 1 := by
  exact ⟨rfl, rfl, rfl⟩

set_option maxHeartbeats 6000000 in
set_option maxRecDepth 16384 in
/-- The prescribed reverse tail sweep does not clean X₂'s old mark. -/
theorem old_tail_survives :
    (afterTail 6).core.state = .depart ∧
      (afterTail 6).path_mark = 0 ∧
      (afterTail 6).ctrl_mark = 1 := by
  exact ⟨rfl, rfl, rfl⟩

set_option maxHeartbeats 6000000 in
set_option maxRecDepth 16384 in
/-- The endpoint retains the boundary root and terminal session departure,
while X₂ still violates the required lineage colour. -/
theorem prescribed_word_collision :
    (afterTail 0).core.state = .lock ∧
      (afterTail 0).ctrl_mark = 1 ∧
      (afterTail 7).core.state = .depart ∧
      (afterTail 7).path_mark = 0 ∧
      (afterTail 7).ctrl_mark = 1 ∧
      (afterTail 6).path_mark = 0 ∧
      (afterTail 6).ctrl_mark = 1 := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem all_eight (P : Fin 8 → Prop)
    (h0 : P 0) (h1 : P 1) (h2 : P 2) (h3 : P 3)
    (h4 : P 4) (h5 : P 5) (h6 : P 6) (h7 : P 7) : ∀ i, P i := by
  intro i
  have hi := i.isLt
  by_cases e0 : i = 0
  · simpa [e0] using h0
  by_cases e1 : i = 1
  · simpa [e1] using h1
  by_cases e2 : i = 2
  · simpa [e2] using h2
  by_cases e3 : i = 3
  · simpa [e3] using h3
  by_cases e4 : i = 4
  · simpa [e4] using h4
  by_cases e5 : i = 5
  · simpa [e5] using h5
  by_cases e6 : i = 6
  · simpa [e6] using h6
  have e7 : i = 7 := by apply Fin.ext; omega
  simpa [e7] using h7

theorem seed_full : ∀ i : Fin 8, (seed i).core.path ≠ .bot := by
  apply all_eight
  all_goals simp [seed, base, physLabel]

theorem seed_no_leader : ∀ i : Fin 8, (seed i).core.leader = false := by
  apply all_eight
  all_goals rfl

theorem seed_domain : ∀ i : Fin 8, (seed i).core.inProtocolDomain 2 := by
  apply all_eight
  all_goals simp [seed, base, physLabel, AgentState.inProtocolDomain] <;> omega

theorem seed_LBF : PPLLAuthBitFrozen.LBF seed := by
  constructor
  · intro i
    exact ⟨by simp [PPLLAuthBitFrozen.NIc, seed, base],
      by simp [PPLLAuthBitFrozen.NIc, seed, base]⟩
  · intro t ht
    left
    intro p hp
    have : (seed t).core.path3 = none := by simp [seed, base]
    rw [this] at hp
    cases hp

/-- The starting point is the §4 tail-debt entrance: B is entirely clean,
X₀ is already a lineage departure, and only X₁..X₃ retain the old mark. -/
theorem seed_tail_debt_shape :
    (∀ i : Fin 8, (seed i).core.state = .depart ∧
      (seed i).core.path2 = none ∧ (seed i).core.reset_cmd = false ∧
      (seed i).core.write = .none ∧ (seed i).core.write_state = .none) ∧
    (∀ i : Fin 8, (seed i).path_mark = 0) ∧
    (∀ i : Fin 8, i.val < 5 → (seed i).ctrl_mark = 0) ∧
    (∀ i : Fin 8, 5 ≤ i.val → (seed i).ctrl_mark = 1) := by
  constructor
  · apply all_eight
    all_goals exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  constructor
  · intro i
    rfl
  constructor
  · intro i hi
    simp [seed, hi, show ¬ 4 < i.val by omega]
  · intro i hi
    simp [seed, show 4 < i.val by omega]

set_option maxHeartbeats 6000000 in
set_option maxRecDepth 16384 in
private theorem afterWrap_own_paths : ∀ i : Fin 8,
    (afterWrap i).core.path = .some (i.val % 4) 0 := by
  apply all_eight
  all_goals rfl

set_option maxHeartbeats 6000000 in
set_option maxRecDepth 16384 in
private theorem afterTwoEdges_own_paths : ∀ i : Fin 8,
    (afterTwoEdges i).core.path = .some (i.val % 4) 0 := by
  apply all_eight
  all_goals rfl

set_option maxHeartbeats 6000000 in
set_option maxRecDepth 16384 in
private theorem afterThreeEdges_own_paths : ∀ i : Fin 8,
    (afterThreeEdges i).core.path = .some (i.val % 4) 0 := by
  apply all_eight
  all_goals rfl

set_option maxHeartbeats 6000000 in
set_option maxRecDepth 16384 in
private theorem afterWrap_no_leader : ∀ i : Fin 8,
    (afterWrap i).core.leader = false := by
  apply all_eight
  all_goals rfl

set_option maxHeartbeats 6000000 in
set_option maxRecDepth 16384 in
private theorem afterTwoEdges_no_leader : ∀ i : Fin 8,
    (afterTwoEdges i).core.leader = false := by
  apply all_eight
  all_goals rfl

set_option maxHeartbeats 6000000 in
set_option maxRecDepth 16384 in
private theorem afterThreeEdges_no_leader : ∀ i : Fin 8,
    (afterThreeEdges i).core.leader = false := by
  apply all_eight
  all_goals rfl

set_option maxHeartbeats 6000000 in
set_option maxRecDepth 16384 in
theorem final_own_paths : ∀ i : Fin 8,
    (afterTail i).core.path = .some (i.val % 4) 0 := by
  apply all_eight
  all_goals rfl

theorem final_full : ∀ i : Fin 8, (afterTail i).core.path ≠ .bot := by
  intro i
  rw [final_own_paths i]
  simp

set_option maxHeartbeats 6000000 in
set_option maxRecDepth 16384 in
theorem final_no_leader : ∀ i : Fin 8, (afterTail i).core.leader = false := by
  apply all_eight
  all_goals rfl

/-- No prefix of this prescribed four-edge word reaches the leader-or-
main-path-hole target. The terminal comparison interface is therefore the
relevant branch of the fixed-word lemma. -/
theorem every_prefix_target_free :
    ∀ i : Fin 8,
      (seed i).core.leader = false ∧ (seed i).core.path ≠ .bot ∧
      (afterWrap i).core.leader = false ∧ (afterWrap i).core.path ≠ .bot ∧
      (afterTwoEdges i).core.leader = false ∧ (afterTwoEdges i).core.path ≠ .bot ∧
      (afterThreeEdges i).core.leader = false ∧ (afterThreeEdges i).core.path ≠ .bot ∧
      (afterTail i).core.leader = false ∧ (afterTail i).core.path ≠ .bot := by
  intro i
  have p0 := seed_full i
  have p1 := afterWrap_own_paths i
  have p2 := afterTwoEdges_own_paths i
  have p3 := afterThreeEdges_own_paths i
  have p4 := final_full i
  rw [p1, p2, p3]
  exact ⟨seed_no_leader i, p0, afterWrap_no_leader i, by simp,
    afterTwoEdges_no_leader i, by simp, afterThreeEdges_no_leader i,
    by simp, final_no_leader i, p4⟩

/-- The actual original AuthF protocol reaches the displayed collision. -/
theorem collision_reachable :
    (authProtocol (by omega : 0 < 4) 2 authFplusmcc).Reachable ring seed afterTail ∧
      (afterTail 6).path_mark = 0 ∧ (afterTail 6).ctrl_mark = 1 := by
  exact ⟨authRun_reachable (by omega : 0 < 4) 2 authFplusmcc ring seed [7,6,5,4],
    old_tail_survives.2⟩

#print axioms fresh_colour_collision
#print axioms wrap_head_lock
#print axioms old_tail_survives
#print axioms prescribed_word_collision
#print axioms seed_full
#print axioms seed_no_leader
#print axioms seed_domain
#print axioms seed_LBF
#print axioms seed_tail_debt_shape
#print axioms final_own_paths
#print axioms final_full
#print axioms final_no_leader
#print axioms every_prefix_target_free
#print axioms collision_reachable
end PPLLAuthCheckTailCollision
