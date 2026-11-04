import Leader.Wu.Carrier.PolylogParameters

/-!
# Literal carrier certificate for the paired five-pass overlay

This module gives a conservative state-count certificate for the proposed
paired-defect transaction layer.  It does not claim that the new controls fit
inside unused semantic combinations of the existing rooted carrier.  Instead
it retains the entire `RootedCarrierCode` and takes a literal Cartesian product
with the deliberately loose compiler fields

`Role4 × RootCtl32 × Msg32 × Trail16`.

The fields reserve modes for the two-sided frozen-coin lifecycle, endpoint
locks, wash/cooldown, source/target transaction phases, return messages, and
the five-pass trail.  Their overlay has exactly

`4 * 32 * 32 * 16 = 65536`

states.  If used as a standalone position/compiler carrier, adjoining `Fin h`
gives exactly `65536 * h` states.  When the overlay is adjoined to the existing
rooted carrier, it multiplies the existing exact cubic count by the fixed
constant `65536`, so the literal `O((log log n)^3)` bound is preserved.  This
is not a packing claim: a future theorem may reduce the constant only by giving
an explicit semantics-preserving encode/decode map.
-/

namespace PPLLPairedFivePassCarrier

open PPLLPolylogCarrierParameters

set_option autoImplicit false

/-- Logical root role: neutral, unmatched, selected source, or selected target. -/
abbrev Role4 := Fin 4

/-- Root control modes.  The occupied modes include `Dirty`, wash states,
`Armed`, all eight `Fixed(bit,inDone,outDone)` states, source/target tentative
and locked states, `Blocked`, and cooldown substates. -/
abbrev RootCtl32 := Fin 32

/-- Endpoint phase, return kind, and transaction-finalization tag. -/
abbrev Msg32 := Fin 32

/-- Literal trail alphabet.  Its occupied modes include
`Empty/Clean`, `WHead/WTrail/WAck`, `Q0/Q1`, `P0/P1`, `Pull`,
`LGrant/LReject/LBlock`, `F0/F1`, and `Erase`. -/
abbrev Trail16 := Fin 16

/-- Literal constant compiler overlay, without semantic packing. -/
abbrev FivePassOverlayCode :=
  ((Role4 × RootCtl32) × Msg32) × Trail16

/-- Standalone position/compiler carrier from the physical design. -/
abbrev FivePassPhysicalCode (h : Nat) :=
  Fin h × FivePassOverlayCode

/-- Conservative carrier: keep every old rooted field and add the overlay. -/
abbrev PairedFivePassCarrierCode (h : Nat) :=
  FivePassOverlayCode × RootedCarrierCode h

private def fivePassOverlaySource : ExhaustiveList FivePassOverlayCode :=
  ExhaustiveList.prod
    (ExhaustiveList.prod
      (ExhaustiveList.prod (ExhaustiveList.fin 4)
        (ExhaustiveList.fin 32))
      (ExhaustiveList.fin 32))
    (ExhaustiveList.fin 16)

private def fivePassPhysicalSource (h : Nat) :
    ExhaustiveList (FivePassPhysicalCode h) :=
  ExhaustiveList.prod (ExhaustiveList.fin h) fivePassOverlaySource

/-- Count of the earlier `Fin h × Role4 × Msg8 × Trail3` proposal.
This is a comparison constant only; that old carrier has no frozen-coin/wash
decode for the new compiler. -/
def legacyNinetySixCount (h : Nat) : Nat := 96 * h

/-- Duplicate-free exhaustive enumeration of the conservative product. -/
def pairedFivePassCarrierStates (h : Nat) :
    ExhaustiveList (PairedFivePassCarrierCode h) :=
  ExhaustiveList.prod fivePassOverlaySource (rootedCarrierStates h)

private theorem fivePassOverlaySource_nodup :
    fivePassOverlaySource.values.Nodup := by
  apply ExhaustiveList.values_nodup_prod
  · apply ExhaustiveList.values_nodup_prod
    · exact ExhaustiveList.values_nodup_prod _ _
        (ExhaustiveList.values_nodup_fin 4)
        (ExhaustiveList.values_nodup_fin 32)
    · exact ExhaustiveList.values_nodup_fin 32
  · exact ExhaustiveList.values_nodup_fin 16

private theorem fivePassPhysicalSource_nodup (h : Nat) :
    (fivePassPhysicalSource h).values.Nodup := by
  exact ExhaustiveList.values_nodup_prod _ _
    (ExhaustiveList.values_nodup_fin h) fivePassOverlaySource_nodup

theorem pairedFivePassCarrierStates_nodup (h : Nat) :
    (pairedFivePassCarrierStates h).values.Nodup := by
  exact ExhaustiveList.values_nodup_prod _ _
    fivePassOverlaySource_nodup (rootedCarrierStates_nodup h)

/-- The compiler overlay has exactly `65536` literal modes. -/
theorem fivePassOverlaySource_length :
    fivePassOverlaySource.values.length = 65536 := by
  simp [fivePassOverlaySource, ExhaustiveList.values_length_prod,
    ExhaustiveList.values_length_fin]

/-- The standalone position/compiler carrier has exactly `65536 * h` states. -/
theorem fivePassPhysicalSource_length (h : Nat) :
    (fivePassPhysicalSource h).values.length = 65536 * h := by
  simp [fivePassPhysicalSource, ExhaustiveList.values_length_prod,
    ExhaustiveList.values_length_fin, fivePassOverlaySource_length,
    Nat.mul_comm]

/-- The loose compiler carrier does not fit the old `96h` cardinality when
`h` is positive; it replaces that carrier by a larger constant-factor one. -/
theorem legacyNinetySixCount_lt_fivePassPhysical {h : Nat} (hh : 0 < h) :
    legacyNinetySixCount h < (fivePassPhysicalSource h).values.length := by
  rw [fivePassPhysicalSource_length]
  unfold legacyNinetySixCount
  omega

/-- Exact rational comparison: the new standalone constant is `2048/3`
times the old one. -/
theorem three_mul_fivePassPhysical_length_eq_2048_mul_legacy (h : Nat) :
    3 * (fivePassPhysicalSource h).values.length =
      2048 * legacyNinetySixCount h := by
  rw [fivePassPhysicalSource_length]
  unfold legacyNinetySixCount
  rw [← Nat.mul_assoc, ← Nat.mul_assoc,
    show 3 * 65536 = 196608 by decide]

/-- Closed-form count for the conservative carrier at block height `h`. -/
def pairedFivePassCountAtHeight (h : Nat) : Nat :=
  65536 * rootedCarrierCountAtHeight h

/-- The closed form is exactly the length of the duplicate-free enumeration. -/
theorem pairedFivePassCountAtHeight_eq_states (h : Nat) :
    pairedFivePassCountAtHeight h =
      (pairedFivePassCarrierStates h).values.length := by
  rw [show pairedFivePassCountAtHeight h =
      65536 * rootedCarrierCountAtHeight h by rfl,
    rootedCarrierCountAtHeight_eq_states,
    show (pairedFivePassCarrierStates h).values.length =
      fivePassOverlaySource.values.length *
        (rootedCarrierStates h).values.length by
      simp [pairedFivePassCarrierStates,
        ExhaustiveList.values_length_prod],
    fivePassOverlaySource_length]

/-- Exact expanded literal state polynomial. -/
theorem pairedFivePassCountAtHeight_eq (h : Nat) :
    pairedFivePassCountAtHeight h =
      8796093022208 * h * (h + 1) * (8 * h + 9) := by
  unfold pairedFivePassCountAtHeight rootedCarrierCountAtHeight
  simp only [Nat.mul_assoc]
  rw [← Nat.mul_assoc,
    show 65536 * 134217728 = 8796093022208 by decide]

/-- Multiplying the existing carrier changes only the cubic coefficient. -/
theorem pairedFivePassCountAtHeight_le_cube {h : Nat} (hh : 0 < h) :
    pairedFivePassCountAtHeight h ≤ 299067162755072 * h ^ 3 := by
  calc
    pairedFivePassCountAtHeight h =
        65536 * rootedCarrierCountAtHeight h := rfl
    _ ≤ 65536 * (4563402752 * h ^ 3) :=
      Nat.mul_le_mul_left 65536 (rootedCarrierCountAtHeight_le_cube hh)
    _ = 299067162755072 * h ^ 3 := by
      rw [← Nat.mul_assoc,
        show 65536 * 4563402752 = 299067162755072 by decide]

/-- Exact conservative state count at physical ring size `n`. -/
def pairedFivePassStateCount (n : Nat) : Nat :=
  pairedFivePassCountAtHeight (carrierHeight n)

theorem pairedFivePassStateCount_eq (n : Nat) :
    pairedFivePassStateCount n =
      8796093022208 * carrierHeight n * (carrierHeight n + 1) *
        (8 * carrierHeight n + 9) := by
  exact pairedFivePassCountAtHeight_eq (carrierHeight n)

/-- Literal cubic iterated-logarithm envelope for the conservative overlay. -/
theorem pairedFivePassStateCount_le_explicit_cube {n : Nat} (hn : 0 < n) :
    pairedFivePassStateCount n ≤
      299067162755072 * (explicitHeightBound n) ^ 3 := by
  calc
    pairedFivePassStateCount n ≤
        299067162755072 * (carrierHeight n) ^ 3 :=
      pairedFivePassCountAtHeight_le_cube (carrierHeight_pos n)
    _ ≤ 299067162755072 * (explicitHeightBound n) ^ 3 :=
      Nat.mul_le_mul_left _
        (Nat.pow_le_pow_left (carrierHeight_le_explicitHeightBound hn) 3)

end PPLLPairedFivePassCarrier
