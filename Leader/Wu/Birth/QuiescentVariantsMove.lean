import Leader.Wu.Birth.LeaderlessEscapeConsumeControl

set_option autoImplicit false
set_option Elab.async false

namespace ZZQuiescent2

open PPLL

/-!
# Can the adversary silence token creation?

`Leader/Wu/Birth/QuiescentRingMoves.lean` showed the canonical quiescent ring is not edgewise
fixed, because token creation and the write sequence both move.  Two follow-ups
are needed before that counts as a defence.

First, the earlier cell carried `write := .overwrite`, which is an action rather
than the inert value; `WriteAction.none` is the inert one (`State.lean:60-65`).
So the write-sequence motion may be an artefact of the chosen fields.

Second, the token creation guard (`Algorithm.lean:91-95`) is
`l.leader = false ∧ l.label = 0 ∧ l.wait = false ∧ l.path = .bot`.
An adversary holding the ring leaderless cannot touch the first two
conjuncts, but `wait` and `path` are free.  Those are the two knobs, and each
gets its own variant here.
-/

private theorem hps : (0 : Nat) < 2 := by decide

/-- A cell parameterised by the three fields under test. -/
private def cell (lab : Fin 2) (w : Bool) (pa : PathInfo) (wr : WriteAction) :
    AgentState 2 :=
  { leader := false, probe := false, phase := true, bit := false, wait := w,
    state := MainState.none, path := pa, reset := false,
    carry := false, count := 0, label := lab, h_field := false,
    path2 := none, path3 := none, path4 := none, path5 := none,
    p := false, p_carry := false, reset_cmd := false, echo := false,
    signal_B := ⟨0, by decide⟩, bullet := ⟨0, by decide⟩, shield := false,
    write_state := WriteState.none, write := wr,
    last := false, last_set := false, last_unset := false, b_carry := false,
    gen_ws := false, ws_echo := false, signal_ws := false }

private def L0 : Fin 2 := ⟨0, by decide⟩
private def L1 : Fin 2 := ⟨1, by decide⟩

/-- Is the whole repaired transition the identity on both edges? -/
private def chainFixed (a b : AgentState 2) : Bool :=
  decide (ZZRepairAll10Consume.ppllIntegratedRepairAll5Consume hps 2 a b = (a, b)) &&
  decide (ZZRepairAll10Consume.ppllIntegratedRepairAll5Consume hps 2 b a = (b, a))

private def stages (a b : AgentState 2) : List Bool :=
  [decide (pPsi hps a b = (a, b)),
   decide (genSig hps 2 a b = (a, b)),
   decide (cleanSig hps a b = (a, b)),
   decide (eliminateSig hps a b = (a, b)),
   decide (sigMove hps a b = (a, b)),
   decide (checkSig hps a b = (a, b)),
   decide (writeSeq hps a b = (a, b))]

/-! ## Variant A: the inert write action, otherwise as before -/

private def a0 : AgentState 2 := cell L0 false PathInfo.bot WriteAction.none
private def a1 : AgentState 2 := cell L1 false PathInfo.bot WriteAction.none

/-! ## Variant B: the WAIT knob raised -/

private def b0 : AgentState 2 := cell L0 true PathInfo.bot WriteAction.none
private def b1 : AgentState 2 := cell L1 true PathInfo.bot WriteAction.none

/-! ## Variant C: the path knob occupied -/

private def c0 : AgentState 2 := cell L0 false (PathInfo.some 0 0) WriteAction.none
private def c1 : AgentState 2 := cell L1 false (PathInfo.some 0 0) WriteAction.none

/-! ## Variant D: both knobs at once -/

private def d0 : AgentState 2 := cell L0 true (PathInfo.some 0 0) WriteAction.none
private def d1 : AgentState 2 := cell L1 true (PathInfo.some 0 0) WriteAction.none

/-- Neither knob silences token creation, and the inert write action does not
stop the write sequence either.  Raising WAIT changes nothing; occupying the
path makes three further stages move rather than fewer. -/
theorem variant_stages :
    (stages a0 a1 = [true, false, true, true, true, true, false]) ∧
    (stages b0 b1 = [true, false, true, true, true, true, false]) ∧
    (stages c0 c1 = [true, false, false, true, true, false, false]) ∧
    (stages d0 d1 = [true, false, false, true, true, false, false]) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide +kernel

/-- VERDICT.  None of the four leaderless candidates is edgewise fixed, so none
of them refutes the deliverable through the execution lemma. -/
theorem no_variant_is_edgewise_fixed :
    (chainFixed a0 a1 = false) ∧ (chainFixed b0 b1 = false) ∧
    (chainFixed c0 c1 = false) ∧ (chainFixed d0 d1 = false) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide +kernel

/-- Token creation moves in every one of the four, which is the common cause. -/
theorem genSig_moves_in_all_variants :
    (decide (genSig hps 2 a0 a1 = (a0, a1)) = false) ∧
    (decide (genSig hps 2 b0 b1 = (b0, b1)) = false) ∧
    (decide (genSig hps 2 c0 c1 = (c0, c1)) = false) ∧
    (decide (genSig hps 2 d0 d1 = (d0, d1)) = false) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide +kernel

#print axioms variant_stages
#print axioms no_variant_is_edgewise_fixed
#print axioms genSig_moves_in_all_variants

end ZZQuiescent2
