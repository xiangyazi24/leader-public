import Leader.Wu.Protocol.Repairs


set_option autoImplicit false
set_option Elab.async false


namespace ZZIntegratedBirthLabel


theorem terminal_right_forces_predecessor
    {ψ : Nat} (h2 : 2 ≤ ψ)
    (l r : Fin ψ)
    (halign : r.val = (l.val + 1) % ψ)
    (hterminal : r.val = ψ - 1) :
    l.val = ψ - 2 ∧ l.val < ψ - 1 := by
  have hl : l.val < ψ := l.isLt
  have hm : (l.val + 1) % ψ = ψ - 1 :=
    halign.symm.trans hterminal
  by_cases hlt : l.val + 1 < ψ
  · rw [Nat.mod_eq_of_lt hlt] at hm
    constructor <;> omega
  · have heq : l.val + 1 = ψ := by
      omega
    rw [heq, Nat.mod_self] at hm
    omega


theorem terminal_label_guard_reachable
    {ψ : Nat} (h2 : 2 ≤ ψ) :
    ∃ l r : Fin ψ,
      r.val = (l.val + 1) % ψ ∧
      r.val = ψ - 1 ∧
      l.val < ψ - 1 := by
  let l : Fin ψ := ⟨ψ - 2, by omega⟩
  let r : Fin ψ := ⟨ψ - 1, by omega⟩
  refine ⟨l, r, ?_, rfl, ?_⟩
  · dsimp [l, r]
    have hlt : ψ - 2 + 1 < ψ := by
      omega
    rw [Nat.mod_eq_of_lt hlt]
    omega
  · dsimp [l]
    omega


theorem checkR_label_side_compatible
    {ψ : Nat} (h2 : 2 ≤ ψ)
    (l r : AgentState ψ)
    (halign :
      r.label.val = (l.label.val + 1) % ψ)
    (hterminal :
      r.label.val = ψ - 1) :
    l.label.val < ψ - 1 := by
  exact
    (terminal_right_forces_predecessor
      h2 l.label r.label halign hterminal).2


#print axioms ZZIntegratedBirthLabel.terminal_right_forces_predecessor
#print axioms ZZIntegratedBirthLabel.terminal_label_guard_reachable
#print axioms ZZIntegratedBirthLabel.checkR_label_side_compatible


end ZZIntegratedBirthLabel
