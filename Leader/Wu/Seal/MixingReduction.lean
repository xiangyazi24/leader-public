import Leader.Wu.Seal.ABGate

namespace PPLLCompleteMultiLeaderCleanup
namespace Q11574FixedFrontMassMixing

open PPLL PPLLResearchFormulation
open PPartialSealSweepTasepMixingFirstBrickSol
open PPartialSealSweepTasepRotationBridgeSol
open PPartialSealSweepABGateBreakthroughSol

set_option autoImplicit false

/-!
Seal-mixing decomposition.

The only dynamical assumption below is
`Q11574HalfStationaryMarked11At`.  It is a `Prop`, not an asserted theorem.
Everything else is finite Nat arithmetic over declarations available through
`PPartialSealSweepABGateBreakthroughSol`, so this file does not import the
currently broken `PPartialSealSweepTasepFiniteTimeSol`.
-/

private theorem q11574_frontSliceCard_pos_of_le
    (n k : Nat) (hkn : k <= n) :
    0 < frontSliceCard n k := by
  induction n generalizing k with
  | zero =>
      have hk : k = 0 := by omega
      subst k
      simp
  | succ n ih =>
      cases k with
      | zero => simp
      | succ k =>
          rw [frontSliceCard_succ_succ]
          have hleft : 0 < frontSliceCard n k := ih k (by omega)
          omega

private theorem q11574_markedPairSliceCard_pos
    (n k : Nat) (hk : 2 <= k) (hkn : k < n) :
    0 < markedPairSliceCard n k := by
  unfold markedPairSliceCard
  apply q11574_frontSliceCard_pos_of_le
  omega

/--
Lemma 1 of the decomposition.

The exact incidence identity gives a factor TWO of stationary slack in the
interior slice.  This is the amount needed so that a half-stationary pointwise
mixing estimate still leaves the desired inverse-square endpoint mass.
-/
theorem q11574_two_mul_frontSliceCard_le_square_mul_markedPair
    (n k : Nat) (hn : 3 <= n) (hk : 2 <= k) (hkn : k < n) :
    2 * frontSliceCard n k <=
      n ^ 2 * markedPairSliceCard n k := by
  have hexact :=
    frontSliceCard_markedPair_exact n k hk (by omega)
  have hkminus : 1 <= k - 1 := by omega
  have hkfactor : 2 <= k * (k - 1) := by
    calc
      2 = 2 * 1 := by omega
      _ <= k * (k - 1) := Nat.mul_le_mul hk hkminus
  have hscale :
      2 * frontSliceCard n k <=
        (k * (k - 1)) * frontSliceCard n k := by
    exact Nat.mul_le_mul_right (frontSliceCard n k) hkfactor
  have hcoeff : n * (n - 1) <= n ^ 2 := by
    have hsub : n - 1 <= n := Nat.le_of_lt (by omega)
    rw [Nat.pow_two]
    exact Nat.mul_le_mul_left n hsub
  calc
    2 * frontSliceCard n k <=
        (k * (k - 1)) * frontSliceCard n k := hscale
    _ = n * (n - 1) * markedPairSliceCard n k := hexact.symm
    _ <= n ^ 2 * markedPairSliceCard n k :=
      Nat.mul_le_mul_right _ hcoeff

/--
Lemma 2 contract of the decomposition.

For every selected start on the fixed-mass slice, the marked-11 endpoint row
at time `t` has at least one half of the stationary marked-pair mass.  All
normalizing denominators are cleared:

  M * n^t <= 2 * S * C.

This is deliberately a definition of a proposition, not a theorem.  Proving
it at `t = 16*n^4` is the remaining coupling / Poincare / mixing leaf.
-/
def Q11574HalfStationaryMarked11At
    {n : Nat} (ring : DirectedRing n) (k t : Nat) : Prop :=
  forall (F : Fin n -> Bool) (edge : Fin n),
    frontConfigMass F = k ->
      markedPairSliceCard n k * n ^ t <=
        2 * frontSliceCard n k *
          tasepMarked11EndpointCount ring F edge t

/--
Lemma 3 of the decomposition.

A half-stationary marked-event estimate plus the factor-two stationary slack
implies the exact inverse-square endpoint gate.  The cancellation is by the
strictly positive marked-slice cardinality; no division or probability type
is used.
-/
theorem q11574_halfStationaryMarked11At_to_endpointGate
    {n k : Nat} (ring : DirectedRing n)
    (hn : 3 <= n) (hk : 2 <= k) (hkn : k < n)
    (t : Nat)
    (hmix : Q11574HalfStationaryMarked11At ring k t)
    (F : Fin n -> Bool) (edge : Fin n)
    (hmass : frontConfigMass F = k) :
    TasepMarked11InverseSquareEndpointGate ring F edge t := by
  unfold TasepMarked11InverseSquareEndpointGate
  let C := tasepMarked11EndpointCount ring F edge t
  have hstatic :=
    q11574_two_mul_frontSliceCard_le_square_mul_markedPair
      n k hn hk hkn
  have hmixF :
      markedPairSliceCard n k * n ^ t <=
        2 * frontSliceCard n k * C := by
    simpa [C] using hmix F edge hmass
  have hupper :
      (2 * frontSliceCard n k) * C <=
        (n ^ 2 * markedPairSliceCard n k) * C :=
    Nat.mul_le_mul_right C hstatic
  have hscaled :
      markedPairSliceCard n k * n ^ t <=
        markedPairSliceCard n k * (n ^ 2 * C) := by
    calc
      markedPairSliceCard n k * n ^ t <=
          2 * frontSliceCard n k * C := hmixF
      _ <= (n ^ 2 * markedPairSliceCard n k) * C := hupper
      _ = markedPairSliceCard n k * (n ^ 2 * C) := by ac_rfl
  have hmarked : 0 < markedPairSliceCard n k :=
    q11574_markedPairSliceCard_pos n k hk hkn
  exact Nat.le_of_mul_le_mul_left hscaled hmarked

/--
Pointwise target, conditional only on the single remaining mixing
contract at the requested horizon.
-/
theorem q11574_fixedFrontMassTasepMarked11Endpoint_16n4_of_halfStationary
    {n k : Nat} (ring : DirectedRing n)
    (hn : 3 <= n) (hk : 2 <= k) (hkn : k < n)
    (hmix : Q11574HalfStationaryMarked11At
      ring k (16 * n ^ 4))
    (F : Fin n -> Bool) (edge : Fin n)
    (hmass : frontConfigMass F = k) :
    TasepMarked11InverseSquareEndpointGate
      ring F edge (16 * n ^ 4) := by
  exact q11574_halfStationaryMarked11At_to_endpointGate
    ring hn hk hkn (16 * n ^ 4) hmix F edge hmass

/--
The exact `FixedFrontMassTasepMarked11EndpointBoundAt` package consumed by the
existing AB-gate bridge, again conditional only on the one remaining mixing
contract.
-/
theorem q11574_fixedFrontMassTasepMarked11EndpointBoundAt_16n4_of_halfStationary
    {n k : Nat} (ring : DirectedRing n)
    (hn : 3 <= n) (hk : 2 <= k) (hkn : k < n)
    (hmix : Q11574HalfStationaryMarked11At
      ring k (16 * n ^ 4)) :
    FixedFrontMassTasepMarked11EndpointBoundAt
      ring k (16 * n ^ 4) := by
  refine ⟨hn, hk, hkn, ?_⟩
  intro F edge hmass
  exact q11574_fixedFrontMassTasepMarked11Endpoint_16n4_of_halfStationary
    ring hn hk hkn hmix F edge hmass

#print axioms q11574_two_mul_frontSliceCard_le_square_mul_markedPair
#print axioms q11574_halfStationaryMarked11At_to_endpointGate
#print axioms q11574_fixedFrontMassTasepMarked11Endpoint_16n4_of_halfStationary
#print axioms q11574_fixedFrontMassTasepMarked11EndpointBoundAt_16n4_of_halfStationary

end Q11574FixedFrontMassMixing
end PPLLCompleteMultiLeaderCleanup
