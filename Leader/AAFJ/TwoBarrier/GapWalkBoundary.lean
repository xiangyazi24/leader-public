import Leader.AAFJ.TwoBarrier.ColoredEndpointTerminals
import Leader.Wu.Safety.NoCheckBirthConditionTwoGeometry

/-!
# Exact signed boundary term for the endpoint gap walk

The colored service tree reduces the remaining stochastic question to one
integer term.  Rear advance sends `d` to `d-1`, front advance sends it to
`d+1`, and contact has zero continuation value.  For the gambler's-ruin
potential `d*(n-d)`, the exact boundary correction is the directional mass
imbalance times the centered coordinate, minus one unit for every advance and
minus the full potential for every contact.
-/

set_option autoImplicit false

namespace AAFJPK.TwoEndpointGapBoundary

open BarrierAlgebra
open PPLLNoCheckBirthConditionTwoGeometry
open TwoEndpointServiceClock
open TwoEndpointColoredClock

private theorem cwDist_advance_rear
    {n : Nat} (ring : DirectedRing n) {rear front : Fin n}
    (hgap : 1 < cwDist ring rear front) :
    cwDist ring (ring.rightNeighbor rear) front + 1 =
      cwDist ring rear front := by
  let d := cwDist ring rear front
  have hpos := cwPos_cwDist ring rear front
  have hw : cwPos ring (ring.rightNeighbor rear) (d - 1) = front := by
    rw [cwPos_rightNeighbor]
    simpa [d, show d - 1 + 1 = d by omega] using hpos
  have hc := cwPos_bounded_unique ring (ring.rightNeighbor rear) front
    (d - 1) (by have := cwDist_lt ring rear front; omega) hw
  dsimp [d] at hc ⊢
  omega

private theorem cwDist_advance_front
    {n : Nat} (ring : DirectedRing n) {rear front : Fin n}
    (hne : ring.rightNeighbor front ≠ rear) :
    cwDist ring rear (ring.rightNeighbor front) =
      cwDist ring rear front + 1 := by
  let d := cwDist ring rear front
  have hdlt : d < n := cwDist_lt ring rear front
  have hlt : d + 1 < n := by
    by_cases h : d + 1 < n
    · exact h
    · have heq : d + 1 = n := by omega
      have hp : cwPos ring rear (d + 1) = ring.rightNeighbor front := by
        rw [cwPos_succ]
        simp only [d, cwPos_cwDist]
      rw [heq, cwPos_period] at hp
      exact (hne hp.symm).elim
  have hp : cwPos ring rear (d + 1) = ring.rightNeighbor front := by
    rw [cwPos_succ]
    simp only [d, cwPos_cwDist]
  simpa [d] using (cwPos_bounded_unique ring rear (ring.rightNeighbor front)
    (d + 1) hlt hp).symm

/-- A colored rear-advance terminal has the literal `d ↦ d-1` transported
gap update. -/
theorem rearAdvance_gap
    {n k : Nat} {hk : 0 < k} {ring : DirectedRing n}
    (p : TerminalPayload hk ring) (hkind : p.kind = .rearAdvance) :
    cwDist ring (ring.rightNeighbor p.origin.rear) p.origin.front + 1 =
      cwDist ring p.origin.rear p.origin.front := by
  have hne : ring.rightNeighbor p.origin.rear ≠ p.origin.front := by
    intro h
    apply p.origin.rearPre.2.1
    simpa [h] using p.origin.frontPre.1
  have hpos : 0 < cwDist ring p.origin.rear p.origin.front := by
    apply Nat.pos_of_ne_zero
    intro hz
    have hp := cwPos_cwDist ring p.origin.rear p.origin.front
    rw [hz, cwPos_zero] at hp
    exact p.origin.ne hp
  have hnotOne : cwDist ring p.origin.rear p.origin.front ≠ 1 := by
    intro hd
    apply hne
    have hp := cwPos_cwDist ring p.origin.rear p.origin.front
    rw [hd] at hp
    simpa using hp
  exact cwDist_advance_rear ring (by omega)

/-- A colored front-advance terminal has the literal `d ↦ d+1` transported
gap update. -/
theorem frontAdvance_gap
    {n k : Nat} {hk : 0 < k} {ring : DirectedRing n}
    (p : TerminalPayload hk ring) (hkind : p.kind = .frontAdvance) :
    cwDist ring p.origin.rear (ring.rightNeighbor p.origin.front) =
      cwDist ring p.origin.rear p.origin.front + 1 := by
  have hne : ring.rightNeighbor p.origin.front ≠ p.origin.rear := by
    intro h
    apply p.origin.frontPre.2.1
    simpa [h] using p.origin.rearPre.1
  exact cwDist_advance_front ring hne

/-- Integer form of the usual absorbing-gap potential. -/
def gapPhi (n d : Nat) : Int := (d : Int) * ((n : Int) - (d : Int))

theorem gapPhi_front_diff (n d : Nat) :
    gapPhi n (d + 1) - gapPhi n d =
      (n : Int) - 2 * (d : Int) - 1 := by
  simp only [gapPhi, Int.natCast_add, Int.natCast_one]
  have h : (n : Int) - ((d : Int) + 1) =
      ((n : Int) - (d : Int)) - 1 := by omega
  rw [h, Int.add_mul, Int.mul_sub]
  simp
  omega

theorem gapPhi_rear_diff (n d : Nat) (hd : 0 < d) :
    gapPhi n (d - 1) - gapPhi n d =
      -((n : Int) - 2 * (d : Int)) - 1 := by
  have hcast : ((d - 1 : Nat) : Int) = (d : Int) - 1 := by omega
  simp only [gapPhi, hcast]
  have h : (n : Int) - ((d : Int) - 1) =
      ((n : Int) - (d : Int)) + 1 := by omega
  rw [h, Int.sub_mul, Int.mul_add]
  simp
  omega

/-- Exact first-terminal identity.  `rearMass`, `frontMass`, and
`contactMass` can be instantiated by the three exact colored masses. -/
theorem colored_gap_boundary_identity
    (n d rearMass frontMass contactMass : Nat) (hd : 0 < d) :
    (rearMass : Int) * gapPhi n (d - 1) +
          (frontMass : Int) * gapPhi n (d + 1) -
        ((rearMass + frontMass + contactMass : Nat) : Int) * gapPhi n d =
      ((frontMass : Int) - (rearMass : Int)) *
          ((n : Int) - 2 * (d : Int)) -
        ((rearMass + frontMass : Nat) : Int) -
        (contactMass : Int) * gapPhi n d := by
  have hr := gapPhi_rear_diff n d hd
  have hf := gapPhi_front_diff n d
  have hr' : gapPhi n (d - 1) = gapPhi n d -
      ((n : Int) - 2 * (d : Int)) - 1 := by omega
  have hf' : gapPhi n (d + 1) = gapPhi n d +
      ((n : Int) - 2 * (d : Int)) - 1 := by omega
  rw [hr', hf']
  simp only [Int.natCast_add]
  simp [Int.mul_add, Int.mul_sub, Int.add_mul, Int.sub_mul]
  omega

/-- The precise sufficient signed-balance row for nonpositive gap drift.  The
clock and color partition do not currently prove this premise. -/
theorem colored_gap_nonincrease_of_signed_balance
    (n d rearMass frontMass contactMass : Nat) (hd : 0 < d)
    (hbalance :
      ((frontMass : Int) - (rearMass : Int)) *
          ((n : Int) - 2 * (d : Int)) ≤
        ((rearMass + frontMass : Nat) : Int) +
          (contactMass : Int) * gapPhi n d) :
    (rearMass : Int) * gapPhi n (d - 1) +
        (frontMass : Int) * gapPhi n (d + 1) ≤
      ((rearMass + frontMass + contactMass : Nat) : Int) * gapPhi n d := by
  have hid := colored_gap_boundary_identity
    n d rearMass frontMass contactMass hd
  have hz :
      ((frontMass : Int) - (rearMass : Int)) *
          ((n : Int) - 2 * (d : Int)) -
        ((rearMass + frontMass : Nat) : Int) -
        (contactMass : Int) * gapPhi n d ≤ 0 := by omega
  omega

#print axioms colored_gap_boundary_identity
#print axioms colored_gap_nonincrease_of_signed_balance

end AAFJPK.TwoEndpointGapBoundary
