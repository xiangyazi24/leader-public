import Leader.Wu.Comparison.ExpiringK2Projection
import Leader.Wu.Protocol.StateBoundCarrier

/-! Count the actual bounded legacy domain, permit bit and finite stall. -/

namespace ExpiringK2Projection

open PPLLExpiringComparisonRepair PPLLStateBoundCarrier

set_option autoImplicit false

variable {ψ κ τ : Nat}

/-- The existing expiring certificate, which is already duplicate-free. -/
abbrev states (ψ κ τ : Nat) := expiringAgentState ψ κ τ

/-- Each state, including every replacement output, has its original finite
representation. No signal observation state or UNode is added to the carrier. -/
theorem finite_bijection (ψ κ τ : Nat) :
    Function.Injective (states ψ κ τ).decode ∧
      Function.Surjective (states ψ κ τ).decode :=
  expiringAgentState_decode_bijective ψ κ τ

def localBound (ψ κ τ : Nat) : Nat :=
  2 * (6606028800 * (κ + 1) * ψ * (2 * ψ + 1) *
    (12 * ψ * (ψ + 1) + 1) * (4 * ψ + 1) * (2 * ψ + 3) ^ 2) * (τ + 1)

/-- Compare the existing duplicate-free certificate with the independently
counted, complete list of the very same BoundedAgentState, not UCell. -/
theorem legacy_count_bound (ψ κ : Nat) :
    (PPLLFinite.boundedAgentState ψ κ).values.length ≤
      6606028800 * (κ + 1) * ψ * (2 * ψ + 1) *
        (12 * ψ * (ψ + 1) + 1) * (4 * ψ + 1) * (2 * ψ + 3) ^ 2 := by
  rw [← boundedAgentState_length]
  apply (PPLLFinite.boundedAgentState_values_nodup ψ κ).length_le_of_subset
  intro q _
  exact boundedAgentStateList_complete ψ κ q

/-- An unconditional finite local-state bound, with all three actual
parameters retained. The two extra factors are the permit and stall domains. -/
theorem state_bound (ψ κ τ : Nat) :
    (states ψ κ τ).values.length ≤ localBound ψ κ τ := by
  rw [expiringAgentState_values_length]
  exact Nat.mul_le_mul_right (τ + 1)
    (Nat.mul_le_mul_left 2 (legacy_count_bound ψ κ))

/-- Optional polynomial simplification in the usual ψ ≤ κ+1 regime. It
still retains the actual arbitrary τ+1 factor. -/
theorem state_bound_poly (hψ : 0 < ψ) (hκ : ψ ≤ κ + 1) :
    (states ψ κ τ).values.length ≤
      2 * 61931520000000 * (κ + 1) ^ 8 * (τ + 1) := by
  apply Nat.le_trans (state_bound ψ κ τ)
  have h := Nat.mul_le_mul_right (τ + 1)
    (Nat.mul_le_mul_left 2 (carrier_le_poly κ ψ hψ hκ))
  simpa only [localBound, Nat.mul_assoc] using h

theorem row_enumerated (hψ : 0 < ψ) (l r : ExpiringAgentState ψ κ τ) :
    (row hψ l r).1 ∈ (states ψ κ τ).values ∧
      (row hψ l r).2 ∈ (states ψ κ τ).values :=
  ⟨(states ψ κ τ).complete _, (states ψ κ τ).complete _⟩

end ExpiringK2Projection

#print axioms ExpiringK2Projection.finite_bijection
#print axioms ExpiringK2Projection.state_bound
#print axioms ExpiringK2Projection.state_bound_poly
#print axioms ExpiringK2Projection.row_enumerated
