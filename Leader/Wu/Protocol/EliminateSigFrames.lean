import Leader.Wu.Protocol.Algorithm

set_option autoImplicit false
set_option Elab.async false

namespace ZZT1EliminateSig

open PPLL

/-! ## ELIMINATE_SIG frame projections -/

theorem eliminateSig_leader
    {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ) :
    let q := eliminateSig hψ l r
    q.1.leader = l.leader ∧ q.2.leader = r.leader := by
  simp only [eliminateSig]
  repeat (first | constructor | rfl | split)

theorem eliminateSig_label
    {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ) :
    let q := eliminateSig hψ l r
    q.1.label = l.label ∧ q.2.label = r.label := by
  simp only [eliminateSig]
  repeat (first | constructor | rfl | split)

theorem eliminateSig_bit
    {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ) :
    let q := eliminateSig hψ l r
    q.1.bit = l.bit ∧ q.2.bit = r.bit := by
  simp only [eliminateSig]
  repeat (first | constructor | rfl | split)

theorem eliminateSig_path2
    {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ) :
    let q := eliminateSig hψ l r
    q.1.path2 = l.path2 ∧ q.2.path2 = r.path2 := by
  simp only [eliminateSig]
  repeat (first | constructor | rfl | split)

theorem eliminateSig_path3
    {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ) :
    let q := eliminateSig hψ l r
    q.1.path3 = l.path3 ∧ q.2.path3 = r.path3 := by
  simp only [eliminateSig]
  repeat (first | constructor | rfl | split)

theorem eliminateSig_write
    {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ) :
    let q := eliminateSig hψ l r
    q.1.write = l.write ∧ q.2.write = r.write := by
  simp only [eliminateSig]
  repeat (first | constructor | rfl | split)

/-! ## ELIMINATE_SIG state/path shapes -/

/-- Stronger endpoint-specific form of “state is eliminate_signal/none/original”. -/
theorem eliminateSig_state
    {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ) :
    let q := eliminateSig hψ l r
    (q.1.state = .eliminate_signal ∨ q.1.state = l.state) ∧
      (q.2.state = .none ∨ q.2.state = r.state) := by
  simp only [eliminateSig]
  split
  · split
    · exact ⟨Or.inl rfl, Or.inl rfl⟩
    · exact ⟨Or.inr rfl, Or.inl rfl⟩
  · exact ⟨Or.inr rfl, Or.inr rfl⟩

/-- Stronger endpoint-specific form of “path is bot/original”. -/
theorem eliminateSig_path
    {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ) :
    let q := eliminateSig hψ l r
    q.1.path = l.path ∧
      (q.2.path = .bot ∨ q.2.path = r.path) := by
  simp only [eliminateSig]
  split
  · split
    · exact ⟨rfl, Or.inl rfl⟩
    · exact ⟨rfl, Or.inl rfl⟩
  · exact ⟨rfl, Or.inr rfl⟩

end ZZT1EliminateSig

#print axioms ZZT1EliminateSig.eliminateSig_leader
#print axioms ZZT1EliminateSig.eliminateSig_label
#print axioms ZZT1EliminateSig.eliminateSig_bit
#print axioms ZZT1EliminateSig.eliminateSig_path2
#print axioms ZZT1EliminateSig.eliminateSig_path3
#print axioms ZZT1EliminateSig.eliminateSig_write
#print axioms ZZT1EliminateSig.eliminateSig_state
#print axioms ZZT1EliminateSig.eliminateSig_path
