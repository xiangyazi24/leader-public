import Leader.Wu.Authorization.ResetDrain

/-!
# A two-edge exit from the recorded frontier collar state

This transcribes `frontier-seed1997-trap-scc-witness.json` at `ψ=2`, `κ=2`.
The JSON action number is the raw `Path2Info.action`, so cell 4 stores A1
with action `1`. Serving physical edge 4 twice reaches a terminal elimination
state and then deletes cell 5's main path. This is a finite fixture only.
-/
namespace PPLLAuthFrontierCollarWitness

open PPLL PPLLAuthF PPLLAuthResetDrain
set_option autoImplicit false

/-- Shared values in all six raw JSON cores; each cell below sets every
remaining non-shared field and all six provenance sidecars. -/
def base (label : Fin 2) (bit : Bool) : AgentState 2 :=
  { leader := false, probe := false, phase := false, bit := bit,
    wait := false, state := .depart,
    path := .some label.val (if bit then 1 else 0),
    reset := false, carry := false, count := 0, label := label,
    h_field := false, path2 := none, path3 := none,
    path4 := none, path5 := none, p := false, p_carry := false,
    reset_cmd := false, echo := false, signal_B := 0, bullet := 0,
    shield := false, write_state := .none, write := .none,
    last := false, last_set := false, last_unset := false,
    b_carry := false, gen_ws := false, ws_echo := false,
    signal_ws := false }

def cell0 : AuthState 2 :=
  { core := base 0 true, path_mark := 2, ctrl_mark := 2,
    path2_scope := .line, path2_mark := 2, path4_mark := 0, path5_mark := 2 }

def cell1 : AuthState 2 :=
  { core := { (base 1 true) with wait := true, count := 2, h_field := true, p := true, path4 := some (1, 1) },
    path_mark := 2, ctrl_mark := 0, path2_scope := .line,
    path2_mark := 2, path4_mark := 2, path5_mark := 0 }

def cell2 : AuthState 2 :=
  { core := { (base 0 true) with h_field := true, p := true },
    path_mark := 1, ctrl_mark := 1, path2_scope := .line,
    path2_mark := 1, path4_mark := 0, path5_mark := 1 }

def cell3 : AuthState 2 :=
  { core := { (base 1 true) with state := .compare2, wait := true, count := 2, p := true, path4 := some (1, 1) },
    path_mark := 1, ctrl_mark := 1, path2_scope := .session,
    path2_mark := 1, path4_mark := 1, path5_mark := 0 }

def cell4 : AuthState 2 :=
  { core := { (base 0 false) with state := .compare1, reset := true, path2 := some ⟨1, 1, 1, 1⟩, path5 := some (0, 1), p_carry := true, write_state := .depart },
    path_mark := 1, ctrl_mark := 1, path2_scope := .line,
    path2_mark := 1, path4_mark := 0, path5_mark := 1 }

def cell5 : AuthState 2 :=
  { core := { (base 1 false) with state := .compare2, p := true },
    path_mark := 1, ctrl_mark := 1, path2_scope := .line,
    path2_mark := 1, path4_mark := 0, path5_mark := 0 }

def seed : Fin 6 → AuthState 2 := fun i =>
  if i = 0 then cell0 else if i = 1 then cell1 else
  if i = 2 then cell2 else if i = 3 then cell3 else
  if i = 4 then cell4 else cell5

def ring : DirectedRing 6 := ⟨by omega⟩

def afterOne : Fin 6 → AuthState 2 :=
  authRun (by omega : 0 < 2) 2 authFplusmcc ring seed [4]

def afterTwo : Fin 6 → AuthState 2 :=
  authRun (by omega : 0 < 2) 2 authFplusmcc ring seed [4, 4]

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 8192 in
/-- The first service creates terminal elimination at physical cell 5. -/
theorem first_terminal_E : (afterOne 5).core.state = .eliminate_signal := by
  rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 8192 in
/-- The second service deletes that same cell's main path. -/
theorem second_path_hole : (afterTwo 5).core.path = .bot := by
  rfl

/-- This is a genuine finite reachable deletion under the original AuthF
candidate, with no closure or global liveness assertion. -/
theorem reachable_hole :
    (authProtocol (by omega : 0 < 2) 2 authFplusmcc).Reachable ring seed afterTwo ∧
      (afterTwo 5).core.path = .bot := by
  exact ⟨authRun_reachable (by omega : 0 < 2) 2 authFplusmcc ring seed [4, 4],
    second_path_hole⟩

private theorem all_six (P : Fin 6 → Prop)
    (h0 : P 0) (h1 : P 1) (h2 : P 2)
    (h3 : P 3) (h4 : P 4) (h5 : P 5) : ∀ i, P i := by
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
  have e5 : i = 5 := by apply Fin.ext; omega
  simpa [e5] using h5

theorem seed_full : ∀ i : Fin 6, (seed i).core.path ≠ .bot := by
  apply all_six
  all_goals simp [seed, cell0, cell1, cell2, cell3, cell4, cell5, base]

theorem seed_no_leader : ∀ i : Fin 6, (seed i).core.leader = false := by
  apply all_six
  all_goals rfl

theorem seed_domain : ∀ i : Fin 6, (seed i).core.inProtocolDomain 2 := by
  apply all_six
  all_goals simp [seed, cell0, cell1, cell2, cell3, cell4, cell5, base,
    AgentState.inProtocolDomain] <;> omega

#print axioms first_terminal_E
#print axioms second_path_hole
#print axioms reachable_hole
#print axioms seed_full
#print axioms seed_no_leader
#print axioms seed_domain
end PPLLAuthFrontierCollarWitness
