import Leader.Wu.Protocol.Algorithm

set_option autoImplicit false
set_option Elab.async false

namespace ZZStep4

open PPLL

/-- C5 step 4: when the CHECK-ready guard holds and the input is not already
`.CHECK_ready`, `checkSigSetReady` really changes the state field to
`.CHECK_ready` and is therefore non-identity. -/
theorem checkSigSetReady_changes_state
    {ψ : Nat} (u : AgentState ψ) (pathLabel pathBit : Nat)
    (hpath : u.path = .some pathLabel pathBit)
    (hlabel : u.label.val = pathLabel)
    (hdepart : u.state ≠ .depart)
    (hequal : u.state ≠ .equal)
    (hlarger : u.state ≠ .larger)
    (hless : u.state ≠ .less)
    (hready : u.state ≠ .CHECK_ready) :
    checkSigSetReady u = { u with state := .CHECK_ready } ∧
    checkSigSetReady u ≠ u := by
  have hguard :
      u.label.val = pathLabel ∧
      u.state ≠ .depart ∧
      u.state ≠ .equal ∧
      u.state ≠ .larger ∧
      u.state ≠ .less := by
    exact
      ⟨hlabel,
        ⟨hdepart,
          ⟨hequal,
            ⟨hlarger, hless⟩⟩⟩⟩

  have hset :
      checkSigSetReady u = { u with state := .CHECK_ready } := by
    unfold checkSigSetReady
    rw [hpath]
    dsimp only
    split
    · rfl
    · next h =>
      exact (h hguard).elim

  refine ⟨hset, ?_⟩
  intro hsame
  have hrecord :
      ({ u with state := MainState.CHECK_ready } : AgentState ψ) = u :=
    hset.symm.trans hsame
  have hstate : MainState.CHECK_ready = u.state :=
    congrArg (fun v : AgentState ψ => v.state) hrecord
  exact hready hstate.symm

#print axioms ZZStep4.checkSigSetReady_changes_state

end ZZStep4
