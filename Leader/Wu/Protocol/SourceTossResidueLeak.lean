import Leader.Wu.Protocol.Algorithm

/-! Literal Algorithm 1 at psi = 3: the action-6 residue of a finished toss leaks into the previous segment.

Algorithm 10 (SIGMOVE) lines 26-27 set `toss` at a label-0 cell carrying `path2` action 6 but do not clear `path2`;
Algorithm 11 line 13 created that action-6 signal.  When the tossing label-0 cell `u0` of segment j+1 is the responder
of its left neighbour (the label psi-1 cell of segment j), SIGMOVE lines 15-17 (run before DISAPPEAR in Algorithm 1)
move the action-6 `path2` into that neighbour, and only afterwards DISAPPEAR lines 1-4 turn `u0` into `toss_done`
with action 5.  The leaked action-6 signal then moves left through segment j by lines 15-17 and at segment j's
label-0 cell lines 26-27 set `toss`: a lottery game started in a segment whose comparison never produced `less`.

Cells: `c k b` is a clean passive carrier at label k with path (k, bit b); `u0` is a tossing label-0 carrier with
action-6 `path2`.  `literal_leak_first`: one literal row of Algorithm 1 on the edge (label 2 of segment j, u0) moves the action-6
residue into segment j (in the literal algorithm CHECK lines 1-3 then re-ready u0 itself, because `toss` is not
excluded there; the consumer's toss-preservation repair keeps the toss, see B6TossResidueLeakR1).
-/

open PPLL

set_option autoImplicit false

namespace SourceTossResidueLeak

def c (lab : Fin 3) (b : Bool) : AgentState 3 :=
  { leader := false, probe := false, phase := false, bit := b, wait := true, state := .CHECK_ready,
    path := .some lab.val (if b then 1 else 0),
    reset := false, carry := false, count := 0, label := lab, h_field := false,
    path2 := none, path3 := none, path4 := none, path5 := none, p := false, p_carry := false,
    reset_cmd := false, echo := false, signal_B := 0, bullet := 0, shield := false,
    write_state := .none, write := .none, last := false, last_set := false, last_unset := false,
    b_carry := false, gen_ws := false, ws_echo := false, signal_ws := false }

/-- The tossing label-0 carrier of the next segment, still holding the action-6 signal of its CHECK result. -/
def u0 : AgentState 3 :=
  { c 0 true with state := .toss, path2 := some ⟨0, 0, 0, 6⟩ }


/-- Literal Algorithm 1, edge (label 2 of segment j, u0): SIGMOVE lines 15-17 move the action-6 residue into the
label-2 cell of the previous segment and clear it at u0. -/
theorem literal_leak_first :
    let q := ppll (ψ := 3) (by decide) 3 (c 2 false) u0
    q.1.path2 = some ⟨0, 0, 0, 6⟩ ∧ q.2.path2 = none := by
  decide


/-- A `less` result just written at label 0 (Algorithm 11 line 13). -/
def u0less : AgentState 3 :=
  { c 0 true with state := .less, path2 := some ⟨0, 0, 0, 6⟩ }

/-- Literal Algorithm 1: escape before application.  If the fresh action-6 signal's first interaction has u0 as
responder, Algorithm 10 lines 15-17 move it into the previous segment before lines 26-27 can set `toss` at u0 (u0
stays `less`; its later path2 is rewritten by CHECK and COMPARE_BIT in the same interaction). -/
theorem literal_less_escapes_before_toss :
    let q := ppll (ψ := 3) (by decide) 3 (c 2 false) u0less
    q.1.path2 = some ⟨0, 0, 0, 6⟩ ∧ q.2.state = .less := by
  decide

/-- A pathless label-2 cell left in `eliminate_signal` with its action-4 signal (lines 22-23 do not clear it). -/
def elimResidue : AgentState 3 :=
  { c 2 false with path := .bot, state := .eliminate_signal, path2 := some ⟨0, 0, 0, 4⟩ }

/-- Literal Algorithm 1: as initiator, Algorithm 10 lines 18-20 move the action-4 residue right into the next
segment's label-0 carrier. -/
theorem literal_eliminate_residue_escapes_right :
    let q := ppll (ψ := 3) (by decide) 3 elimResidue (c 0 true)
    q.2.path2 = some ⟨0, 0, 0, 4⟩ := by
  decide

end SourceTossResidueLeak
