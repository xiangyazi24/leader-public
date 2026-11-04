import Leader.Wu.Birth.LeaderlessEscapeConsumeControl

set_option autoImplicit false
set_option Elab.async false

namespace ZZQuiescent

open PPLL

/-!
# Is there a leaderless configuration every edge fixes?

`PPartialFactorSixteenSameEpochResetNoGoSol.lean:116-133` proves, for an
arbitrary population protocol, that a configuration which is leaderless and
fixed by every edge has `stabilizingScheduleCount = 0` at every horizon.  The
deliverable `UniformFiniteHorizonSSLE P ring isLeader t A` asserts
`(allSchedules n t).length ≤ stabilizingScheduleCount ... + A` for *every*
configuration, so one such configuration forces `n ^ t ≤ A` and refutes every
bound below `n ^ t`.

`pPsi` (`Algorithm.lean:29-46`) has an identity branch: when the responder
label already equals `(l.label + 1) % ψ` and the responder carries no probe,
the stage returns `(l, r)` unchanged.  At `ψ = n = 2` with the two labels laid
out as 0 and 1, both edges take that branch.  Whether the whole transition is
then the identity is what this file decides by kernel evaluation.
-/

private theorem hps : (0 : Nat) < 2 := by decide

/-- A cell carrying nothing: no leader, no probe, no token, every flag low.
`phase` is set so that the `pPsi` phase-raising branch has nothing to do. -/
private def quiet (lab : Fin 2) : AgentState 2 :=
  { leader := false, probe := false, phase := true, bit := false, wait := false,
    state := MainState.none, path := PathInfo.bot, reset := false,
    carry := false, count := 0, label := lab, h_field := false,
    path2 := none, path3 := none, path4 := none, path5 := none,
    p := false, p_carry := false, reset_cmd := false, echo := false,
    signal_B := ⟨0, by decide⟩, bullet := ⟨0, by decide⟩, shield := false,
    write_state := WriteState.none, write := WriteAction.overwrite,
    last := false, last_set := false, last_unset := false, b_carry := false,
    gen_ws := false, ws_echo := false, signal_ws := false }

private def u0 : AgentState 2 := quiet ⟨0, by decide⟩
private def u1 : AgentState 2 := quiet ⟨1, by decide⟩

/-- `pPsi` alone on both edges. -/
def pPsiFixed : Bool :=
  decide (pPsi hps u0 u1 = (u0, u1)) && decide (pPsi hps u1 u0 = (u1, u0))

/-- The full repaired transition on both edges of the two-cell ring. -/
def chainFixed : Bool :=
  decide (ZZRepairAll10Consume.ppllIntegratedRepairAll5Consume hps 2 u0 u1 = (u0, u1)) &&
  decide (ZZRepairAll10Consume.ppllIntegratedRepairAll5Consume hps 2 u1 u0 = (u1, u0))

/-- The same question for the unrepaired integrated transition. -/
def chainFixedAll8 : Bool :=
  decide (PPLLRepair.ppllIntegratedRepair hps 2 u0 u1 = (u0, u1)) &&
  decide (PPLLRepair.ppllIntegratedRepair hps 2 u1 u0 = (u1, u0))

/-- The configuration is leaderless, so the follower premise of the execution
lemma is met. -/
theorem quiet_leaderless : (u0.leader = false) ∧ (u1.leader = false) := by
  constructor <;> rfl

theorem pPsi_fixed_kernel : pPsiFixed = true := by decide +kernel

#print axioms pPsi_fixed_kernel
#print axioms quiet_leaderless

/-- VERDICT.  The full repaired transition is NOT the identity on the canonical
quiescent configuration, so this configuration does not refute the deliverable.
`pPsi` is the identity here, hence some later stage moves. -/
theorem chain_not_fixed_kernel : chainFixed = false := by decide +kernel

#print axioms chain_not_fixed_kernel

/-! ## Which stage breaks the fixity -/

def afterPPsi : AgentState 2 × AgentState 2 := pPsi hps u0 u1

def genSigFixed : Bool :=
  decide (genSig hps 2 u0 u1 = (u0, u1))

def cleanSigFixed : Bool :=
  decide (cleanSig hps u0 u1 = (u0, u1))

def eliminateSigFixed : Bool :=
  decide (eliminateSig hps u0 u1 = (u0, u1))

def sigMoveFixed : Bool :=
  decide (sigMove hps u0 u1 = (u0, u1))

def checkSigFixed : Bool :=
  decide (checkSig hps u0 u1 = (u0, u1))

def writeSeqFixed : Bool :=
  decide (writeSeq hps u0 u1 = (u0, u1))

def stageReport : List Bool :=
  [pPsiFixed, genSigFixed, cleanSigFixed, eliminateSigFixed,
   sigMoveFixed, checkSigFixed, writeSeqFixed]

/-- Stage-by-stage verdict.  Only `genSig` and `writeSeq` move; the label
rotation, the cleanup stages, the signal move and CHECK are all inert here.
So the protocol escapes the quiescent self-loop through token creation, not
through label rotation as first guessed. -/
theorem stage_report_kernel :
    stageReport = [true, false, true, true, true, true, false] := by
  decide +kernel

#print axioms stage_report_kernel

/-- The load-bearing half: token creation is what refuses the self-loop. -/
theorem genSig_moves_quiescent : genSigFixed = false := by decide +kernel

#print axioms genSig_moves_quiescent

end ZZQuiescent
