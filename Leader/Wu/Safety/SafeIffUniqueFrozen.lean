import Leader.Wu.Protocol.Algorithm

set_option autoImplicit false
set_option Elab.async false

namespace ZZProtocolProjections

open PopulationProtocol

@[simp] theorem protocol_Q {ψ : Nat} (hψ : 0 < ψ) (κ : Nat) :
    (PPLL.protocol hψ κ).Q = AgentState ψ := rfl

@[simp] theorem protocol_Y {ψ : Nat} (hψ : 0 < ψ) (κ : Nat) :
    (PPLL.protocol hψ κ).Y = LeaderOutput := rfl

@[simp] theorem protocol_transition {ψ : Nat} (hψ : 0 < ψ) (κ : Nat) :
    (PPLL.protocol hψ κ).transition = PPLL.ppll hψ κ := rfl

@[simp] theorem protocol_output {ψ : Nat} (hψ : 0 < ψ) (κ : Nat) :
    (PPLL.protocol hψ κ).output = @AgentState.outputFn ψ := rfl

/-- Pointwise conversion of the public leader-output test. -/
theorem isLeader_output {ψ : Nat} (a : AgentState ψ) :
    isLeaderOutput (AgentState.outputFn a) = a.leader := by
  cases h : a.leader <;>
    simp [AgentState.outputFn, isLeaderOutput, h]

/-- Pointwise conversion of complete output equality. -/
theorem output_eq_iff_leader_eq {ψ : Nat} (a b : AgentState ψ) :
    AgentState.outputFn a = AgentState.outputFn b ↔
      a.leader = b.leader := by
  cases ha : a.leader <;> cases hb : b.leader <;>
    simp [AgentState.outputFn, ha, hb]

/-- Exact safety: unique leader and pointwise freezing on the full
forward closure of the real protocol. -/
theorem isSafe_iff_unique_frozen {ψ n : Nat} (hψ : 0 < ψ) (κ : Nat)
    (ring : DirectedRing n) (C : Fin n → AgentState ψ) :
    (PPLL.protocol hψ κ).IsSafe ring C isLeaderOutput ↔
      (∃ i : Fin n, (C i).leader = true ∧
        ∀ j : Fin n, (C j).leader = true → j = i) ∧
      (∀ D : Fin n → AgentState ψ,
        Reachable (PPLL.protocol hψ κ) ring C D →
        ∀ i : Fin n, (D i).leader = (C i).leader) := by
  constructor
  · intro hs
    obtain ⟨hunique, hstable⟩ := hs
    refine And.intro ?_ ?_
    · obtain ⟨root, hroot, honly⟩ := hunique
      refine ⟨root, ?_, ?_⟩
      · rw [protocol_output hψ κ, isLeader_output (C root)] at hroot
        exact hroot
      · intro j hj
        apply honly j
        rw [protocol_output hψ κ, isLeader_output (C j)]
        exact hj
    · intro D hr i
      have hout :
          (PPLL.protocol hψ κ).output (D i) =
            (PPLL.protocol hψ κ).output (C i) := hstable D hr i
      rw [protocol_output hψ κ] at hout
      exact (output_eq_iff_leader_eq (D i) (C i)).mp hout
  · intro h
    obtain ⟨hunique, hfrozen⟩ := h
    refine And.intro ?_ ?_
    · obtain ⟨root, hroot, honly⟩ := hunique
      refine ⟨root, ?_, ?_⟩
      · rw [protocol_output hψ κ, isLeader_output (C root)]
        exact hroot
      · intro j hj
        apply honly j
        rw [protocol_output hψ κ, isLeader_output (C j)] at hj
        exact hj
    · intro D hr i
      rw [protocol_output hψ κ]
      exact (output_eq_iff_leader_eq (D i) (C i)).mpr (hfrozen D hr i)

end ZZProtocolProjections

#print axioms ZZProtocolProjections.protocol_Q
#print axioms ZZProtocolProjections.protocol_Y
#print axioms ZZProtocolProjections.protocol_transition
#print axioms ZZProtocolProjections.protocol_output
#print axioms ZZProtocolProjections.isLeader_output
#print axioms ZZProtocolProjections.output_eq_iff_leader_eq
#print axioms ZZProtocolProjections.isSafe_iff_unique_frozen
