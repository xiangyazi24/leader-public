import Leader.Wu.Protocol.Algorithm

set_option autoImplicit false
set_option Elab.async false

namespace ZZStep6

open PPLL

/-- C5 step 6, CheckR route only.  The fields relevant to the CheckR
    two-write route are fixed to the literal psi=2 shape; every other field
    is inherited from the supplied base states. -/
private def checkRLeft (l : AgentState 2) : AgentState 2 :=
  { l with
      label := (0 : Fin 2)
      state := .equal }

private def checkRRight (r : AgentState 2) : AgentState 2 :=
  { r with
      bit := false
      label := (1 : Fin 2)
      state := .congest
      path := .some 1 0 }

/-- C5 step 6, CheckR route (not a universal characterization):
    SetReady performs the first write .congest -> .CHECK_ready, then CheckR
    performs the second write .CHECK_ready -> .equal. -/
theorem checkSigCheckR_congest_to_equal_two_writes
    (h2 : 0 < 2) (l r : AgentState 2) :
    let l0 := checkRLeft l
    let r0 := checkRRight r
    let r1 := checkSigSetReady r0
    let r2 := checkSigCheckR h2 l0 r1
    (r1, r2) =
      ({ r0 with state := .CHECK_ready },
       { r0 with state := .equal }) := by
  unfold checkRLeft checkRRight checkSigSetReady checkSigCheckR checkBit
  rfl

/-- CheckL counterexample to any universal claim that every
    .congest -> .equal CHECK route needs the CheckR left-endpoint hypotheses. -/
private def checkLCounterexampleCell (u : AgentState 2) : AgentState 2 :=
  { u with
      bit := false
      label := (0 : Fin 2)
      state := .congest
      path := .some 0 0 }

theorem checkSigCheckL_congest_to_equal_counterexample
    (h2 : 0 < 2) (u : AgentState 2) :
    let u0 := checkLCounterexampleCell u
    let u1 := checkSigSetReady u0
    let u2 := checkSigCheckL h2 u1
    (u1, u2) =
      ({ u0 with state := .CHECK_ready },
       { u0 with state := .equal }) := by
  unfold checkLCounterexampleCell checkSigSetReady checkSigCheckL checkBit
  rfl

#print axioms ZZStep6.checkSigCheckR_congest_to_equal_two_writes
#print axioms ZZStep6.checkSigCheckL_congest_to_equal_counterexample

end ZZStep6
