import Leader.Wu.Protocol.Algorithm

/-! Literal Algorithm 1 at psi = 3: the row on the internal edge (label 0, label 1) of an aligned equal signal.
CHECK writes `equal` on both endpoints, then COMPARE (CMP_UPDATE line 1 and its propagation) rewrites both to
`congest`, so label 1 never leaves the row in `equal` and CHECK cannot reach label psi - 1. -/

open PPLL

set_option autoImplicit false

namespace B6CheckClobberLiteral

def cellA (lab : Fin 3) (b : Bool) : AgentState 3 :=
  { leader := false, probe := false, phase := false, bit := b, wait := true, state := .none,
    path := .some lab.val (if b then 1 else 0),
    reset := false, carry := false, count := 0, label := lab, h_field := false,
    path2 := none, path3 := none, path4 := none, path5 := none, p := false, p_carry := false,
    reset_cmd := false, echo := false, signal_B := 0, bullet := 0, shield := false,
    write_state := .none, write := .none, last := false, last_set := false, last_unset := false,
    b_carry := false, gen_ws := false, ws_echo := false, signal_ws := false }

/-- CHECK alone accepts the aligned pair: both endpoints become `equal`. -/
theorem check_writes_equal :
    let q := ppllAfterCheck (ψ := 3) (by decide) 1 (cellA 0 true) (cellA 1 false)
    q.1.state = .equal ∧ q.2.state = .equal := by
  decide

/-- The complete literal row leaves both endpoints in `congest`. -/
theorem row_leaves_congest :
    let q := ppll (ψ := 3) (by decide) 1 (cellA 0 true) (cellA 1 false)
    q.1.state = .congest ∧ q.2.state = .congest ∧ q.2.leader = false := by
  decide

end B6CheckClobberLiteral
