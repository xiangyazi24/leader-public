import Leader.Wu.Entrance.CalibratedLeaf

set_option autoImplicit false
set_option Elab.async false

namespace C4C5LeafHorizonV2Producer

open B6EntranceV2 B6EntranceV2K2
open B6EntranceK2Budget
open CFinalAssembly2

/--
The calibrated C4 horizon always contains the exact R1 boosted horizon.
Unlike the old `256 * n^2` target, this requires no lower bound on `n`.
-/
theorem calibratedLeafHorizon
    (n psi : Nat) :
    3 * (entranceQ (c4Budget n psi) * Q2star psi) *
        (entranceB n (c4Budget n psi) + 2 * n * (psi - 1)) <=
      FinalLeafHV2 n psi := by
  change
    B6EntranceK2Mass4.c4BoostedH
        n psi (c4Budget n psi) (Q2star psi) <=
      FinalLeafHV2 n psi
  rw [B6EntranceK2Budget.B6EntranceK2Budget.c4BoostedH_eq_frozenCoeff_mul_n]
  rw [FinalLeafHV2_eq]
  have hnn : n <= n ^ 2 := by
    cases n with
    | zero =>
        exact Nat.le_refl 0
    | succ k =>
        have hk : 1 <= Nat.succ k := by omega
        have h := Nat.le_mul_of_pos_right (Nat.succ k) hk
        simpa only [Nat.pow_succ, Nat.pow_zero, Nat.one_mul] using h
  exact Nat.mul_le_mul_left _ hnn

/-- `psi = 3` specialization used by the current campaign. -/
theorem calibratedLeafHorizon_psi3
    (n : Nat) :
    3 * (entranceQ (c4Budget n 3) * Q2star 3) *
        (entranceB n (c4Budget n 3) + 2 * n * (3 - 1)) <=
      FinalLeafHV2 n 3 := by
  exact calibratedLeafHorizon n 3

end C4C5LeafHorizonV2Producer
