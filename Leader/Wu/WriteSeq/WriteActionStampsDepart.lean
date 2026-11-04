import Leader.Wu.Protocol.Algorithm

set_option autoImplicit false
set_option Elab.async false

namespace ZZWriteActionStamp

open PPLL

/-!
# The write sequence stamps `.depart` out of nothing

`writeAction` (`Algorithm.lean:826-848`) opens a branch on
`l.label < r.label ∨ r.label = 0`, tries three write actions inside it, and
then closes with `(l, { r with write_state := .depart })` at `:847`.  That last
write is unconditional: it fires whether or not any of the three inner guards
matched, so a responder that had nothing to write still leaves the stage
carrying `.depart`.

This is the same shape as the `path2` defect, where a stage acts on a token it
never had.  It is recorded here with a concrete witness rather than argued.

`.depart` is one of the four states `checkSigSetReady` (`:229`) excludes, so
the stamp lands exactly on the field CHECK tests.  Whether that blocks leader
creation is a separate question and is not settled here.
-/

private theorem hps : (0 : Nat) < 2 := by decide

/-- A cell holding nothing at all: no leader, no token, every flag low, and
both write fields at their inert values. -/
private def empty (lab : Fin 2) : AgentState 2 :=
  { leader := false, probe := false, phase := true, bit := false, wait := false,
    state := MainState.none, path := PathInfo.bot, reset := false,
    carry := false, count := 0, label := lab, h_field := false,
    path2 := none, path3 := none, path4 := none, path5 := none,
    p := false, p_carry := false, reset_cmd := false, echo := false,
    signal_B := ⟨0, by decide⟩, bullet := ⟨0, by decide⟩, shield := false,
    write_state := WriteState.none, write := WriteAction.none,
    last := false, last_set := false, last_unset := false, b_carry := false,
    gen_ws := false, ws_echo := false, signal_ws := false }

private def e0 : AgentState 2 := empty ⟨0, by decide⟩
private def e1 : AgentState 2 := empty ⟨1, by decide⟩

/-- Both cells start with no pending write. -/
theorem inputs_are_inert :
    e0.write_state = WriteState.none ∧ e1.write_state = WriteState.none ∧
    e0.write = WriteAction.none ∧ e1.write = WriteAction.none := by
  refine ⟨rfl, rfl, rfl, rfl⟩

/-- Yet the responder leaves `writeAction` stamped `.depart`. -/
theorem writeAction_stamps_depart :
    (writeAction hps e0 e1).2.write_state = WriteState.depart := by
  decide +kernel

/-- The initiator is left alone, so the stamp is one-sided. -/
theorem writeAction_leaves_initiator :
    (writeAction hps e0 e1).1 = e0 := by decide +kernel

/-- Sub-stage census of the write sequence on this input: only `writeAction`
moves, so the stamp above is the whole of the write sequence motion. -/
def writeSubstages : List Bool :=
  [decide (writeSeqLeaderMove hps e0 e1 = (e0, e1)),
   decide (groupInfo hps e0 e1 = (e0, e1)),
   decide (writeSeqGenerate hps e0 e1 = (e0, e1)),
   decide (writeSeqPrepare hps e0 e1 = (e0, e1)),
   decide (writeAction hps e0 e1 = (e0, e1)),
   decide (moveWsig hps e0 e1 = (e0, e1))]

theorem write_substage_census :
    writeSubstages = [true, true, true, true, false, true] := by decide +kernel

#print axioms inputs_are_inert
#print axioms writeAction_stamps_depart
#print axioms writeAction_leaves_initiator
#print axioms write_substage_census

end ZZWriteActionStamp
