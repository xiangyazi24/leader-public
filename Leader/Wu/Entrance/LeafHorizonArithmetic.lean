import Leader.Wu.Entrance.ReadyWindowMassSimulation

/-!
# Closure-free producer for leaf 4 of the shared-birth-leaf route

`B6EntranceK2Mass3.C4C5LeafHorizonArithmetic` is pure arithmetic in
`(n, psi, Q₂)`. This module discharges it from an explicit size bound.

It lives downstream rather than inside `B6EntranceK2Mass3` because that module
is an accepted part of the compiled cone and only public names are needed here.

SCOPE LIMIT, deliberately on the record: the discharge is NOT uniform on the
campaign domain. For positive `n` the hypothesis below is not merely sufficient
but exact, obtained by cancelling the common positive factor `256 * n` from the
unfolded leaf. The existing downstream assumptions `2 < psi`, `psi ≤ n` and
`4 ≤ n` do not imply it. At `psi = 3` with the minimal admissible `Q₂ = 29` the
bound is `435 ≤ n`, and every positive `n < 435` genuinely fails the leaf.
-/

namespace C4C5LeafHorizonProducer

open B6EntranceK2Mass3

variable {n psi : Nat}

/-- Pure arithmetic producer for the old `256*n^2` C4/C5 leaf horizon.
On the campaign domain `0 < psi` the premise simplifies to
`3 * Q₂ * (psi + 2) ≤ n`. -/
theorem c4C5LeafHorizonArithmetic_of_bound
    (Q₂ : Nat)
    (hn : 3 * Q₂ * (3 + (psi - 1)) ≤ n) :
    C4C5LeafHorizonArithmetic n psi Q₂ := by
  change
    3 * (128 * Q₂) * (n * 6 + 2 * n * (psi - 1)) ≤
      256 * n ^ 2
  have h6 : n * 6 = (2 * n) * 3 := by
    omega
  have hblock :
      n * 6 + 2 * n * (psi - 1) =
        2 * n * (3 + (psi - 1)) := by
    calc
      n * 6 + 2 * n * (psi - 1)
          = (2 * n) * 3 + (2 * n) * (psi - 1) := by
              rw [h6]
      _ = (2 * n) * (3 + (psi - 1)) := by
            rw [Nat.mul_add]
  rw [hblock]
  have h256 : (256 : Nat) = 128 * 2 := by
    omega
  calc
    3 * (128 * Q₂) * (2 * n * (3 + (psi - 1)))
        = (256 * n) * (3 * Q₂ * (3 + (psi - 1))) := by
            rw [h256]
            ac_rfl
    _ ≤ (256 * n) * n :=
      Nat.mul_le_mul_left (256 * n) hn
    _ = 256 * n ^ 2 := by
      simp only [Nat.pow_succ, Nat.pow_zero, Nat.one_mul, Nat.mul_assoc]

/-- The campaign threshold at `psi = 3` with the minimal admissible `Q₂ = 29`. -/
theorem c4C5LeafHorizonArithmetic_psi3_q29
    (hn : 435 ≤ n) :
    C4C5LeafHorizonArithmetic n 3 29 := by
  apply c4C5LeafHorizonArithmetic_of_bound
    (n := n) (psi := 3) (Q₂ := 29)
  omega

end C4C5LeafHorizonProducer
