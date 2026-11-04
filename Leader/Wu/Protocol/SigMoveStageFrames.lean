import Leader.Wu.Protocol.Algorithm

set_option autoImplicit false

namespace ZZT0SigMove

open PPLL

def A5 : Path2Info := ⟨0, 0, 1, 5⟩

/-- `sigMoveStep1` either installs the source path at the responder or leaves
    the responder path unchanged. -/
theorem sigMoveStep1_path_shape {ψ : Nat} (l r : AgentState ψ) :
    (sigMoveStep1 l r).2.path = l.path ∨
      (sigMoveStep1 l r).2.path = r.path := by
  simp only [sigMoveStep1]
  repeat (first | exact Or.inl rfl | exact Or.inr rfl | split)

/-- `sigMoveStep1` either clears the initiator state to `none` or preserves it. -/
theorem sigMoveStep1_left_state_shape {ψ : Nat} (l r : AgentState ψ) :
    (sigMoveStep1 l r).1.state = .none ∨
      (sigMoveStep1 l r).1.state = l.state := by
  simp only [sigMoveStep1]
  repeat (first | exact Or.inl rfl | exact Or.inr rfl | split)

/-- `sigMoveStep1` frames both `path2` fields. -/
theorem sigMoveStep1_path2_frame {ψ : Nat} (l r : AgentState ψ) :
    (sigMoveStep1 l r).1.path2 = l.path2 ∧
      (sigMoveStep1 l r).2.path2 = r.path2 := by
  simp only [sigMoveStep1]
  repeat (first | constructor | rfl | split)

/-- `sigMoveStep1` frames both `bit` fields. -/
theorem sigMoveStep1_bit_frame {ψ : Nat} (l r : AgentState ψ) :
    (sigMoveStep1 l r).1.bit = l.bit ∧
      (sigMoveStep1 l r).2.bit = r.bit := by
  simp only [sigMoveStep1]
  repeat (first | constructor | rfl | split)

/-- `sigMoveStep1` frames both `leader` fields. -/
theorem sigMoveStep1_leader_frame {ψ : Nat} (l r : AgentState ψ) :
    (sigMoveStep1 l r).1.leader = l.leader ∧
      (sigMoveStep1 l r).2.leader = r.leader := by
  simp only [sigMoveStep1]
  repeat (first | constructor | rfl | split)

/-- Action five cannot trigger the action-one transfer in `sigMoveStep2`. -/
theorem sigMoveStep2_none_or_A5 {ψ : Nat} (l r : AgentState ψ)
    (h : l.path2 = none ∨ l.path2 = some A5) :
    sigMoveStep2 l r = (l, r) := by
  simp only [sigMoveStep2]
  rcases h with h | h <;> rw [h] <;> rfl

/-- Action five cannot trigger the action-two transfer in `sigMoveStep3`. -/
theorem sigMoveStep3_none_or_A5 {ψ : Nat} (l r : AgentState ψ)
    (h : r.path2 = none ∨ r.path2 = some A5) :
    sigMoveStep3 l r = (l, r) := by
  simp only [sigMoveStep3]
  rcases h with h | h <;> rw [h] <;> rfl

/-- Under the requested two-end membership condition, action five cannot
    trigger the action-three/action-six transfer in `sigMoveStep4`.
    The left conjunct is not inspected by the source definition. -/
theorem sigMoveStep4_none_or_A5 {ψ : Nat} (l r : AgentState ψ)
    (h : (l.path2 = none ∨ l.path2 = some A5) ∧
      (r.path2 = none ∨ r.path2 = some A5)) :
    sigMoveStep4 l r = (l, r) := by
  simp only [sigMoveStep4]
  rcases h with ⟨_, hr⟩
  rcases hr with hr | hr <;> rw [hr] <;> rfl

/-- `sigMoveStep5` moves an action-five token from left to right. -/
theorem sigMoveStep5_A5 {ψ : Nat} (l r : AgentState ψ)
    (h : l.path2 = some A5) :
    (sigMoveStep5 l r).1.path2 = none ∧
      (sigMoveStep5 l r).2.path2 = some A5 := by
  simp only [sigMoveStep5]
  rw [h]
  constructor <;> rfl

/-- With no left token, `sigMoveStep5` is the identity. -/
theorem sigMoveStep5_none {ψ : Nat} (l r : AgentState ψ)
    (h : l.path2 = none) :
    sigMoveStep5 l r = (l, r) := by
  simp only [sigMoveStep5]
  rw [h] <;> rfl

/-- With no control token, `sigMoveApplyControl` is the identity. -/
theorem sigMoveApplyControl_none {ψ : Nat} (hψ : ψ > 0)
    (u : AgentState ψ) (h : u.path2 = none) :
    sigMoveApplyControl hψ u = u := by
  simp only [sigMoveApplyControl]
  rw [h] <;> rfl

/-- An action-five token sets a terminal-label host to `depart`. -/
private theorem A5_action : A5.action = 5 := rfl
private theorem A5_position : A5.position = 1 := rfl
private theorem A5_label : A5.label = 0 := rfl

theorem sigMoveApplyControl_A5_top {ψ : Nat} (hψ : ψ > 0)
    (u : AgentState ψ) (hp : u.path2 = some A5)
    (hl : u.label = (⟨ψ - 1, by omega⟩ : Fin ψ)) :
    (sigMoveApplyControl hψ u).state = .depart := by
  simp only [sigMoveApplyControl, hp]
  have hA5_not_34 : ¬ (A5.action = 3 ∨ A5.action = 4) := by
    rw [A5_action]
    decide
  have hfirst :
      ¬ (u.label = (⟨ψ - 1, by omega⟩ : Fin ψ) ∧
          (A5.action = 3 ∨ A5.action = 4)) := by
    intro h
    exact hA5_not_34 h.2
  rw [if_neg hfirst]
  have hsecond :
      u.label = (⟨ψ - 1, by omega⟩ : Fin ψ) ∧ A5.action = 5 :=
    ⟨hl, A5_action⟩
  rw [if_pos hsecond]
  have hA5_not_6 : A5.action ≠ 6 := by
    rw [A5_action]
    decide
  have hthird :
      ¬ (({ u with state := MainState.depart }).label =
            (⟨0, hψ⟩ : Fin ψ) ∧
          A5.action = 6) := by
    intro h
    exact hA5_not_6 h.2
  rw [if_neg hthird]

theorem sigMoveApplyControl_A5_zero {ψ : Nat} (hψ : ψ > 0)
    (u : AgentState ψ) (hp : u.path2 = some A5)
    (hl : u.label = (⟨0, hψ⟩ : Fin ψ)) (hψ1 : ψ > 1) :
    sigMoveApplyControl hψ u = u := by
  simp only [sigMoveApplyControl, hp]
  have hA5_not_34 : ¬ (A5.action = 3 ∨ A5.action = 4) := by
    rw [A5_action]
    decide
  have hfirst :
      ¬ (u.label = (⟨ψ - 1, by omega⟩ : Fin ψ) ∧
          (A5.action = 3 ∨ A5.action = 4)) := by
    intro h
    exact hA5_not_34 h.2
  rw [if_neg hfirst]
  have hzero_ne_top :
      (⟨0, hψ⟩ : Fin ψ) ≠ (⟨ψ - 1, by omega⟩ : Fin ψ) := by
    intro h
    have hv := Fin.ext_iff.mp h
    change (0 : Nat) = ψ - 1 at hv
    omega
  have hlabel_ne_top :
      u.label ≠ (⟨ψ - 1, by omega⟩ : Fin ψ) := by
    intro h
    rw [hl] at h
    exact hzero_ne_top h
  have hsecond :
      ¬ (u.label = (⟨ψ - 1, by omega⟩ : Fin ψ) ∧
          A5.action = 5) := by
    intro h
    exact hlabel_ne_top h.1
  rw [if_neg hsecond]
  have hA5_not_6 : A5.action ≠ 6 := by
    rw [A5_action]
    decide
  have hthird :
      ¬ (u.label = (⟨0, hψ⟩ : Fin ψ) ∧ A5.action = 6) := by
    intro h
    exact hA5_not_6 h.2
  rw [if_neg hthird]

#print axioms ZZT0SigMove.sigMoveStep1_path_shape
#print axioms ZZT0SigMove.sigMoveStep1_left_state_shape
#print axioms ZZT0SigMove.sigMoveStep1_path2_frame
#print axioms ZZT0SigMove.sigMoveStep1_bit_frame
#print axioms ZZT0SigMove.sigMoveStep1_leader_frame
#print axioms ZZT0SigMove.sigMoveStep2_none_or_A5
#print axioms ZZT0SigMove.sigMoveStep3_none_or_A5
#print axioms ZZT0SigMove.sigMoveStep4_none_or_A5
#print axioms ZZT0SigMove.sigMoveStep5_A5
#print axioms ZZT0SigMove.sigMoveStep5_none
#print axioms ZZT0SigMove.sigMoveApplyControl_none
#print axioms ZZT0SigMove.sigMoveApplyControl_A5_top
#print axioms ZZT0SigMove.sigMoveApplyControl_A5_zero
