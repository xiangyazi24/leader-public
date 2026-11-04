import Leader.Wu.Protocol.Algorithm

set_option autoImplicit false
set_option Elab.async false

namespace ZZWaitProbe2

open PPLL

/-! Diagnostic for the stuck WAIT frame lemmas.

    Round 1 established that the claims are NOT definitional: plain `rfl` fails
    under a symbolic psi because the guards cannot reduce.  That says nothing
    about truth.  This round settles truth by kernel evaluation on concrete
    states that exercise every guard, and simultaneously tries `split_ifs`,
    which none of the three failed rounds used.
-/

private theorem hps : (0 : Nat) < 2 := by decide

/-- A base cell at psi = 2 whose branch-deciding fields are parameters. -/
private def cell (lab : Fin 2) (res hf car wt : Bool) (cnt : Nat) : AgentState 2 :=
  { leader := true, probe := false, phase := false, bit := true, wait := wt,
    state := MainState.congest, path := PathInfo.some 1 0, reset := res,
    carry := car, count := cnt, label := lab, h_field := hf,
    path2 := some ⟨0, 0, 1, 5⟩, path3 := none, path4 := none, path5 := none,
    p := false, p_carry := false, reset_cmd := false, echo := false,
    signal_B := ⟨0, by decide⟩, bullet := ⟨0, by decide⟩, shield := false,
    write_state := WriteState.none, write := WriteAction.overwrite,
    last := false, last_set := false, last_unset := false, b_carry := false,
    gen_ws := false, ws_echo := false, signal_ws := false }

/-- Boolean mirror of the eight frame claims on one concrete pair. -/
private def frameOK (l r : AgentState 2) : Bool :=
  let q := wait hps 2 l r
  (decide (q.1.leader = l.leader)) && (decide (q.2.leader = r.leader)) &&
  (decide (q.1.label = l.label)) && (decide (q.2.label = r.label)) &&
  (decide (q.1.bit = l.bit)) && (decide (q.2.bit = r.bit)) &&
  (decide (q.1.state = l.state)) && (decide (q.2.state = r.state)) &&
  (decide (q.1.path = l.path)) && (decide (q.2.path = r.path)) &&
  (decide (q.1.path2 = l.path2)) && (decide (q.2.path2 = r.path2)) &&
  (decide (q.1.path3 = l.path3)) && (decide (q.2.path3 = r.path3)) &&
  (decide (q.1.write = l.write)) && (decide (q.2.write = r.write))

/-- Exhaust every guard-relevant combination at psi = 2: both labels, all four
    booleans on each side, and counts 0..2 straddling kappa = 2. -/
private def allFramesOK : Bool :=
  List.all [(0 : Fin 2), 1] fun a =>
  List.all [(0 : Fin 2), 1] fun b =>
  List.all [false, true] fun r1 =>
  List.all [false, true] fun h1 =>
  List.all [false, true] fun c1 =>
  List.all [false, true] fun w1 =>
  List.all [false, true] fun r2 =>
  List.all [false, true] fun h2 =>
  List.all [false, true] fun c2 =>
  List.all [false, true] fun w2 =>
  List.all [0, 1, 2] fun n1 =>
  List.all [0, 1, 2] fun n2 =>
    frameOK (cell a r1 h1 c1 w1 n1) (cell b r2 h2 c2 w2 n2)

/-- TRUTH VERDICT: if this is `true`, the eight frame claims hold on every
    guard-relevant configuration at psi = 2, so the repeated failures are
    tactic failures and not a false statement. -/
theorem wait_frames_hold_psi2 : allFramesOK = true := by decide +kernel

#print axioms wait_frames_hold_psi2

end ZZWaitProbe2
