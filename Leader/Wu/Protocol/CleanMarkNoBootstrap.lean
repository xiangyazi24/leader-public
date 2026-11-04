import Leader.Wu.Protocol.Repairs

set_option autoImplicit false
set_option Elab.async false

namespace ZZCleanBootstrap3

open PPLL PPLLRepair

/-- When the responder's `path4` is absent, CLEAN-STEP-3 falls through to its
default arm and returns the pair unchanged. -/
theorem step3_eq_self {ψ : Nat} (l r : AgentState ψ) (hr4 : r.path4 = none) :
    cleanSigStep3 l r = (l, r) := by
  unfold cleanSigStep3
  rw [hr4]

/-- When the initiator's `path5` is absent, CLEAN-STEP-4 falls through to its
default arm and returns the pair unchanged. -/
theorem step4_eq_self {ψ : Nat} (l r : AgentState ψ) (hl5 : l.path5 = none) :
    cleanSigStep4 l r = (l, r) := by
  unfold cleanSigStep4
  rw [hl5]

/-- Double-`none` closure of the two CLEAN-mark-creating steps: if both
endpoints have `path4` and `path5` absent, then after `cleanSigStep3` followed by
`cleanSigStep4` all four fields are still absent. -/
theorem no_mark_from_double_none {ψ : Nat} (l r : AgentState ψ)
    (hl4 : l.path4 = none) (hl5 : l.path5 = none)
    (hr4 : r.path4 = none) (hr5 : r.path5 = none) :
    let q := cleanSigStep4 (cleanSigStep3 l r).1 (cleanSigStep3 l r).2
    q.1.path4 = none ∧ q.1.path5 = none ∧ q.2.path4 = none ∧ q.2.path5 = none := by
  rw [step3_eq_self l r hr4, step4_eq_self l r hl5]
  exact ⟨hl4, hl5, hr4, hr5⟩

#print axioms ZZCleanBootstrap3.step3_eq_self
#print axioms ZZCleanBootstrap3.step4_eq_self
#print axioms ZZCleanBootstrap3.no_mark_from_double_none

end ZZCleanBootstrap3
