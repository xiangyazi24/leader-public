import Leader.Wu.Comparison.ExpiringRepair
import Leader.Wu.Comparison.MoveFuelRepair

/-!
# Final finite agent carrier

This module combines:

* the finite Algorithm-1 carrier;
* moved-carrier authorization;
* nonrefreshing movement fuel;
* comparison stall expiration;
* writer age expiration;
* the bootstrap compare-and-copy token;
* the writer-reset mode bit.

`MoveFuelBoundedAgentState` is placed inside the stall timer because the
move-fuel transition is the physical comparison transition observed by the
outer no-progress policy.  Writer age and the two mode/capability bits are
independent outer coordinates.
-/

namespace PPLLFinalAgentState

open PPLLAuthorizedComparisonRepair
open PPLLExpiringComparisonRepair
open PPLLMoveFuelComparisonRepair

/-- Complete finite local state for the final repaired protocol.

Nesting:

`BoundedAgentState`
  → `AuthorizedBoundedAgentState`
  → `MoveFuelBoundedAgentState`
  → `FinalAgentState`.

The comparison stall timer is deliberately outside move fuel.  The remaining
coordinates are independent finite writer/bootstrap controls. -/
structure FinalAgentState
    (ψ κ τ μ ω : Nat) where
  core : MoveFuelBoundedAgentState ψ κ μ
  stall : Fin (τ + 1)
  writerAge : Fin (ω + 1)
  bootstrapCopyToken : Bool
  writerResetMode : Bool
  deriving DecidableEq, Repr

namespace FinalAgentState

/-- Projection to the original finite Algorithm-1 carrier. -/
def toBounded
    (s : FinalAgentState ψ κ τ μ ω) : BoundedAgentState ψ κ :=
  s.core.core.core

/-- Projection to the authorized finite carrier. -/
def toAuthorizedBounded
    (s : FinalAgentState ψ κ τ μ ω) :
    AuthorizedBoundedAgentState ψ κ :=
  s.core.core

/-- Projection to the existing move-fuel finite carrier. -/
def toMoveFuelBounded
    (s : FinalAgentState ψ κ τ μ ω) :
    MoveFuelBoundedAgentState ψ κ μ :=
  s.core

/-- Projection to the existing comparison-expiration carrier.

This proves that the final record really merges the old expiration and
move-fuel forks over one shared authorized bounded core. -/
def toExpiring
    (s : FinalAgentState ψ κ τ μ ω) :
    ExpiringAgentState ψ κ τ :=
  ⟨s.core.core, s.stall⟩

end FinalAgentState

/-! ## Constructive finite-state certificate -/

/-- Balanced product used to enumerate the final record without constructing
an additional semantic wrapper for each independent coordinate. -/
private def finalAgentStateSource
    (ψ κ τ μ ω : Nat) :
    ExhaustiveList
      ((MoveFuelBoundedAgentState ψ κ μ × Fin (τ + 1)) ×
        (Fin (ω + 1) × (Bool × Bool))) :=
  ExhaustiveList.prod
    (ExhaustiveList.prod
      (moveFuelBoundedAgentState ψ κ μ)
      (ExhaustiveList.fin (τ + 1)))
    (ExhaustiveList.prod
      (ExhaustiveList.fin (ω + 1))
      (ExhaustiveList.prod ExhaustiveList.bool ExhaustiveList.bool))

/-- Explicit exhaustive list for every final local state. -/
def finalAgentState
    (ψ κ τ μ ω : Nat) :
    ExhaustiveList (FinalAgentState ψ κ τ μ ω) :=
  ExhaustiveList.mapSurjective
    (finalAgentStateSource ψ κ τ μ ω)
    (fun x =>
      { core := x.1.1
        stall := x.1.2
        writerAge := x.2.1
        bootstrapCopyToken := x.2.2.1
        writerResetMode := x.2.2.2 })
    (by
      intro s
      exact ⟨((s.core, s.stall),
        (s.writerAge, (s.bootstrapCopyToken, s.writerResetMode))),
        by cases s; rfl⟩)

/-- The final exhaustive certificate has no duplicate semantic states. -/
theorem finalAgentState_values_nodup
    (ψ κ τ μ ω : Nat) :
    (finalAgentState ψ κ τ μ ω).values.Nodup := by
  unfold finalAgentState
  apply ExhaustiveList.values_nodup_mapSurjective
  · unfold finalAgentStateSource
    apply ExhaustiveList.values_nodup_prod
    · apply ExhaustiveList.values_nodup_prod
      · exact moveFuelBoundedAgentState_values_nodup ψ κ μ
      · exact ExhaustiveList.values_nodup_fin (τ + 1)
    · apply ExhaustiveList.values_nodup_prod
      · exact ExhaustiveList.values_nodup_fin (ω + 1)
      · apply ExhaustiveList.values_nodup_prod
        · exact ExhaustiveList.values_nodup_bool
        · exact ExhaustiveList.values_nodup_bool
  · intro x y h
    rcases x with ⟨⟨xc, xs⟩, ⟨xa, ⟨xt, xr⟩⟩⟩
    rcases y with ⟨⟨yc, ys⟩, ⟨ya, ⟨yt, yr⟩⟩⟩
    cases h
    rfl

/-- Product-form exact list length, before commutative normalization. -/
theorem finalAgentState_values_length
    (ψ κ τ μ ω : Nat) :
    (finalAgentState ψ κ τ μ ω).values.length =
      (((2 * (PPLLFinite.boundedAgentState ψ κ).values.length) *
          (μ + 1)) * (τ + 1)) *
        ((ω + 1) * (2 * 2)) := by
  unfold finalAgentState finalAgentStateSource
    ExhaustiveList.mapSurjective
  rw [List.length_map,
    ExhaustiveList.values_length_prod,
    ExhaustiveList.values_length_prod,
    moveFuelBoundedAgentState_values_length,
    ExhaustiveList.values_length_fin,
    ExhaustiveList.values_length_prod,
    ExhaustiveList.values_length_fin,
    ExhaustiveList.values_length_prod,
    ExhaustiveList.values_length_bool]

/-- The exact cardinality with every independent Boolean displayed. -/
theorem finalAgentState_values_length_expanded
    (ψ κ τ μ ω : Nat) :
    (finalAgentState ψ κ τ μ ω).values.length =
      (PPLLFinite.boundedAgentState ψ κ).values.length * 2 *
        (τ + 1) * (μ + 1) * (ω + 1) * 2 * 2 := by
  rw [finalAgentState_values_length]
  ac_rfl

/-- The exact cardinality relative to the original bounded carrier.
The Boolean factor is eight, not four. -/
theorem finalAgentState_values_length_factorized
    (ψ κ τ μ ω : Nat) :
    (finalAgentState ψ κ τ μ ω).values.length =
      (PPLLFinite.boundedAgentState ψ κ).values.length * 8 *
        (τ + 1) * (μ + 1) * (ω + 1) := by
  rw [finalAgentState_values_length]
  rw [show (8 : Nat) = 2 * (2 * 2) from rfl]; ac_rfl

/-- Every final local state occurs in the explicit finite list. -/
theorem mem_finalAgentState
    (s : FinalAgentState ψ κ τ μ ω) :
    s ∈ (finalAgentState ψ κ τ μ ω).values :=
  (finalAgentState ψ κ τ μ ω).complete s

/-- Every final local state is represented by a finite list index. -/
theorem finalAgentState_decode_surjective
    (ψ κ τ μ ω : Nat) :
    Function.Surjective
      (finalAgentState ψ κ τ μ ω).decode :=
  (finalAgentState ψ κ τ μ ω).decode_surjective

/-- Duplicate-freedom and exhaustiveness give an exact finite-index
representation, hence an exact semantic cardinality certificate. -/
theorem finalAgentState_decode_bijective
    (ψ κ τ μ ω : Nat) :
    Function.Injective (finalAgentState ψ κ τ μ ω).decode ∧
      Function.Surjective (finalAgentState ψ κ τ μ ω).decode :=
  ⟨ExhaustiveList.decode_injective_of_values_nodup _
      (finalAgentState_values_nodup ψ κ τ μ ω),
    finalAgentState_decode_surjective ψ κ τ μ ω⟩

end PPLLFinalAgentState
