import Leader.Wu.Birth.ShortDoneDispatcher

set_option autoImplicit false
namespace BirthShortDoneDispatcher

def loglogScale (n : Nat) : Nat :=
  Nat.log2 (Nat.log2 n) + 1

/-- Conditional state-count consumer only.  A,B,a,b must be fixed independently
of n in the eventual asymptotic theorem; no parameter producer is claimed here. -/
theorem finite_state_bound_polyloglog
    {ψ width κ τ n : Nat}
    (hψ : 0 < ψ) (hwidth : 0 < width) (hle : width ≤ ψ)
    (hψκ : ψ ≤ κ + 1)
    (A a B b : Nat)
    (hκ : κ + 1 ≤ A * (loglogScale n) ^ a)
    (hτ : τ + 1 ≤ B * (loglogScale n) ^ b) :
    (stateCertificate hψ hwidth hle κ τ).values.length ≤
      2 * 61931520000000 *
        (A * (loglogScale n) ^ a) ^ 8 *
        (B * (loglogScale n) ^ b) := by
  have hc := (finite_state_bound hψ hwidth hle κ τ).2.2
  have hp :
      ExpiringK2Projection.localBound ψ κ τ ≤
        2 * 61931520000000 * (κ + 1) ^ 8 * (τ + 1) := by
    have h := Nat.mul_le_mul_right (τ + 1)
      (Nat.mul_le_mul_left 2
        (PPLLStateBoundCarrier.carrier_le_poly κ ψ hψ hψκ))
    simpa only [ExpiringK2Projection.localBound, Nat.mul_assoc] using h
  have hk8 :
      (κ + 1) ^ 8 ≤ (A * (loglogScale n) ^ a) ^ 8 :=
    Nat.pow_le_pow_left hκ 8
  have hpar :
      2 * 61931520000000 * (κ + 1) ^ 8 * (τ + 1) ≤
        2 * 61931520000000 *
          (A * (loglogScale n) ^ a) ^ 8 *
          (B * (loglogScale n) ^ b) :=
    Nat.mul_le_mul
      (Nat.mul_le_mul_left (2 * 61931520000000) hk8) hτ
  exact Nat.le_trans hc (Nat.le_trans hp hpar)

#print axioms finite_state_bound_polyloglog
end BirthShortDoneDispatcher
