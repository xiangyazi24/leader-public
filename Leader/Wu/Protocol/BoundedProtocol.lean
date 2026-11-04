import Leader.Wu.Protocol.BoundedState
import Leader.Wu.Protocol.FiniteState
import Leader.Wu.Protocol.DomainClosure

/-!
# Genuinely bounded repaired protocol

The executable transition in this module is a restriction/reification of the
separately named repaired audit transition.  Its exact erasure theorem prevents
the wrapper from becoming a second transcription of Algorithms 1–20.
-/

namespace PPLLRepair

/-- Total local transition on the finite-by-construction carrier. -/
def boundedTransition {ψ : Nat} (hψ : ψ > 0) (κ : Nat)
    (l r : BoundedAgentState ψ κ) :
    BoundedAgentState ψ κ × BoundedAgentState ψ κ :=
  let q := ppllSaturatedNoCollision hψ κ
    (BoundedAgentState.erase l) (BoundedAgentState.erase r)
  have hq := PPLLDomain.ppllSaturatedNoCollision_inProtocolDomain hψ
    (BoundedAgentState.erase l) (BoundedAgentState.erase r)
    (BoundedAgentState.erase_inProtocolDomain l)
    (BoundedAgentState.erase_inProtocolDomain r)
  (BoundedAgentState.ofDomain q.1 hq.1,
    BoundedAgentState.ofDomain q.2 hq.2)

/-- The bounded local transition erases exactly to the repaired audit
transition, with no clamping or semantic approximation. -/
theorem erase_boundedTransition {ψ : Nat} (hψ : ψ > 0) (κ : Nat)
    (l r : BoundedAgentState ψ κ) :
    let q := boundedTransition hψ κ l r
    BoundedAgentState.erase q.1 =
        (ppllSaturatedNoCollision hψ κ
          (BoundedAgentState.erase l) (BoundedAgentState.erase r)).1 ∧
      BoundedAgentState.erase q.2 =
        (ppllSaturatedNoCollision hψ κ
          (BoundedAgentState.erase l) (BoundedAgentState.erase r)).2 := by
  simp [boundedTransition, BoundedAgentState.erase_ofDomain]

/-- Population protocol whose actual local state carrier is bounded. -/
def boundedProtocol {ψ : Nat} (hψ : ψ > 0) (κ : Nat) :
    PopulationProtocol where
  Q := BoundedAgentState ψ κ
  Y := LeaderOutput
  transition := boundedTransition hψ κ
  output := fun s => AgentState.outputFn (BoundedAgentState.erase s)

/-- Explicit exhaustive-list certificate for the bounded protocol's actual
local state type. -/
def boundedProtocolStateCertificate {ψ : Nat} (hψ : ψ > 0) (κ : Nat) :
    ExhaustiveList (boundedProtocol hψ κ).Q :=
  PPLLFinite.boundedAgentState ψ κ

/-- A finite index type surjects onto every local state of the bounded
protocol. -/
theorem boundedProtocol_state_decode_surjective {ψ : Nat}
    (hψ : ψ > 0) (κ : Nat) :
    Function.Surjective (boundedProtocolStateCertificate hψ κ).decode :=
  (boundedProtocolStateCertificate hψ κ).decode_surjective

/-! ## Bounded form of the integrated T9 candidate -/

/-- Total bounded transition for the integrated source-rearm candidate. -/
def integratedBoundedTransition {ψ : Nat} (hψ : ψ > 0) (κ : Nat)
    (l r : BoundedAgentState ψ κ) :
    BoundedAgentState ψ κ × BoundedAgentState ψ κ :=
  let q := ppllIntegratedRepair hψ κ
    (BoundedAgentState.erase l) (BoundedAgentState.erase r)
  have hq := PPLLDomain.ppllIntegratedRepair_inProtocolDomain hψ
    (BoundedAgentState.erase l) (BoundedAgentState.erase r)
    (BoundedAgentState.erase_inProtocolDomain l)
    (BoundedAgentState.erase_inProtocolDomain r)
  (BoundedAgentState.ofDomain q.1 hq.1,
    BoundedAgentState.ofDomain q.2 hq.2)

theorem erase_integratedBoundedTransition {ψ : Nat}
    (hψ : ψ > 0) (κ : Nat) (l r : BoundedAgentState ψ κ) :
    let q := integratedBoundedTransition hψ κ l r
    BoundedAgentState.erase q.1 = (ppllIntegratedRepair hψ κ
        (BoundedAgentState.erase l) (BoundedAgentState.erase r)).1 ∧
      BoundedAgentState.erase q.2 = (ppllIntegratedRepair hψ κ
        (BoundedAgentState.erase l) (BoundedAgentState.erase r)).2 := by
  simp [integratedBoundedTransition, BoundedAgentState.erase_ofDomain]

def integratedBoundedProtocol {ψ : Nat} (hψ : ψ > 0) (κ : Nat) :
    PopulationProtocol where
  Q := BoundedAgentState ψ κ
  Y := LeaderOutput
  transition := integratedBoundedTransition hψ κ
  output := fun s => AgentState.outputFn (BoundedAgentState.erase s)

/-- The integrated candidate retains the same explicit finite carrier
certificate. -/
def integratedBoundedProtocolStateCertificate {ψ : Nat}
    (hψ : ψ > 0) (κ : Nat) :
    ExhaustiveList (integratedBoundedProtocol hψ κ).Q :=
  PPLLFinite.boundedAgentState ψ κ

/-- Pointwise erasure of a bounded configuration. -/
def eraseConfig {ψ κ n : Nat}
    (C : Fin n → BoundedAgentState ψ κ) : Fin n → AgentState ψ :=
  fun i => BoundedAgentState.erase (C i)

/-- Configuration-level erasure for one integrated-candidate step. -/
theorem erase_integrated_step {ψ κ n : Nat} (hψ : ψ > 0)
    (ring : DirectedRing n) (C : Fin n → BoundedAgentState ψ κ)
    (e : Fin n) :
    eraseConfig (PopulationProtocol.step (integratedBoundedProtocol hψ κ)
      ring C e) =
      PopulationProtocol.step (integratedProtocol hψ κ) ring
        (eraseConfig C) e := by
  funext k
  unfold PopulationProtocol.step
  simp only [integratedBoundedProtocol, eraseConfig, integratedProtocol]
  have ht := erase_integratedBoundedTransition hψ κ
    (C e) (C (ring.rightNeighbor e))
  split
  · exact ht.1
  · split
    · exact ht.2
    · rfl

/-- Every finite integrated-candidate execution erases to an execution of its
audit transition. -/
theorem erase_integrated_reachable {ψ κ n : Nat} (hψ : ψ > 0)
    (ring : DirectedRing n)
    {C C' : PopulationProtocol.Configuration
      (integratedBoundedProtocol hψ κ) n}
    (h : PopulationProtocol.Reachable
      (integratedBoundedProtocol hψ κ) ring C C') :
    PopulationProtocol.Reachable (integratedProtocol hψ κ) ring
      (eraseConfig C) (eraseConfig C') := by
  induction h
  · exact .refl _
  · rename_i C₂ C₃ _ hone ih
    apply PopulationProtocol.Reachable.step _ _ _ ih
    obtain ⟨e, rfl⟩ := hone
    exact ⟨e, erase_integrated_step hψ ring C₂ e⟩

/-- Pointwise output is unchanged by erasure. -/
theorem output_erase {ψ : Nat} (hψ : ψ > 0) (κ : Nat)
    (s : BoundedAgentState ψ κ) :
    (boundedProtocol hψ κ).output s =
      (protocol hψ κ).output (BoundedAgentState.erase s) := by
  rfl

/-- Configuration-level one-step erasure commutation. -/
theorem erase_step {ψ κ n : Nat} (hψ : ψ > 0)
    (ring : DirectedRing n) (C : Fin n → BoundedAgentState ψ κ)
    (e : Fin n) :
    eraseConfig (PopulationProtocol.step (boundedProtocol hψ κ) ring C e) =
      PopulationProtocol.step (protocol hψ κ) ring (eraseConfig C) e := by
  funext k
  unfold PopulationProtocol.step
  simp only [boundedProtocol, eraseConfig, protocol]
  have ht := erase_boundedTransition hψ κ (C e) (C (ring.rightNeighbor e))
  split
  · exact ht.1
  · split
    · exact ht.2
    · rfl

/-- Every bounded execution maps to an execution of the repaired audit
protocol. -/
theorem erase_reachable {ψ κ n : Nat} (hψ : ψ > 0)
    (ring : DirectedRing n)
    {C C' : PopulationProtocol.Configuration (boundedProtocol hψ κ) n}
    (h : PopulationProtocol.Reachable (boundedProtocol hψ κ) ring C C') :
    PopulationProtocol.Reachable (protocol hψ κ) ring
      (eraseConfig C) (eraseConfig C') := by
  induction h
  · exact .refl _
  · rename_i C₂ C₃ _ hone ih
    apply PopulationProtocol.Reachable.step _ _ _ ih
    obtain ⟨e, rfl⟩ := hone
    exact ⟨e, erase_step hψ ring C₂ e⟩

end PPLLRepair
