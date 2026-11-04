import Leader.Wu.Protocol.Algorithm

/-! Literal Algorithm 13 (DISAPPEAR) at psi = 3: the lottery counter is not reset between lotteries.

The thesis (p.26-27 / PDF p.39-40) describes P(G) = sum p_i 2^i as increased by u0's interactions with its right
neighbour until u0 interacts with its left neighbour, the signal disappearing when the count overflows, and derives a
1/2^(2^psi) disappearance probability from 2^psi consecutive increments.  Algorithm 13 (p.28 / PDF p.41) resets only
`u0.p` when the lottery ends (line 4) and writes `p` nowhere else (lines 7, 10, 13, 19 are the increment and carry);
no other algorithm of Algorithm 1 writes `p`.  So the bits of labels 1..psi-1 left by one lottery start the next one.

`second_lottery_eliminates`: after a finished lottery left `p = 1` on labels 1 and 2 (and `p = 0` on u0), a new lottery
at u0 eliminates the signal after two increments and one carry interaction, instead of 2^3 = 8 increments from zero.
-/

open PPLL

set_option autoImplicit false

namespace SourceDisappearCounterNoReset

def cellP (lab : Fin 3) (st : MainState) (pb : Bool) : AgentState 3 :=
  { leader := false, probe := false, phase := false, bit := false, wait := true, state := st,
    path := .bot, reset := false, carry := false, count := 0, label := lab, h_field := false,
    path2 := none, path3 := none, path4 := none, path5 := none, p := pb, p_carry := false,
    reset_cmd := false, echo := false, signal_B := 0, bullet := 0, shield := false,
    write_state := .none, write := .none, last := false, last_set := false, last_unset := false,
    b_carry := false, gen_ws := false, ws_echo := false, signal_ws := false }

/-- Line 4 resets only the finishing u0: a responder u0 in `toss` becomes `toss_done` with `p = 0`, and the
initiator's `p` (a cell of the previous segment) is untouched. -/
theorem lottery_end_resets_only_u0 :
    let q := disappear (ψ := 3) (by decide) (cellP 2 .none true) (cellP 0 .toss true)
    q.2.state = .toss_done ∧ q.2.p = false ∧ q.1.p = true := by
  decide

/-- Second lottery with labels 1 and 2 still at `p = 1`: two increments at u0 and one carry interaction eliminate the
signal at label 2. -/
theorem second_lottery_eliminates :
    let u1 := cellP 1 .none true
    let u2 := cellP 2 .none true
    -- first increment: u0 p 0 -> 1
    let a := disappear (ψ := 3) (by decide) (cellP 0 .toss false) u1
    -- second increment: u0 p 1 -> 0 with carry, the carry enters label 1 (p 1 -> 0, carry on)
    let b := disappear (ψ := 3) (by decide) a.1 a.2
    -- carry interaction (label 1, label 2): label 2 has p = 1, so it enters eliminate_signal
    let c := disappear (ψ := 3) (by decide) b.2 u2
    a.1.p = true ∧ b.2.p_carry = true ∧ c.2.state = .eliminate_signal := by
  decide

end SourceDisappearCounterNoReset
