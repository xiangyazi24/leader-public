import Leader.PPL.MainTheorem.SPLClosureCost

/-!
P_PL Theorem 1 cleanup, phase 2: the declarations of this file that served only the old
psi <= log2 n + 1 route to `theorem1Statement_proved` moved to
`Leader/PPL/LogWindow/CostMid.lean`, namespace `PPL.Superseded.LogWindow`: `Theorem1UniformHalfFailureMid`, `theorem1_cost_mid`, `Theorem1TinyNCost`, `theorem1SmallNCost_of_tiny`.
-/

namespace PPL

set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false

open K2ArbitraryElimination.FiniteAccounting
open LeaderCountDyadicTail

/--
A state-uniform block estimate with denominator q and numerator loss a
amplifies multiplicatively on a closed target.

This is the multiplicative analogue of the conditioning step in
K2ArbitraryElimination.FiniteAccounting.compose_miss.
-/
theorem amplify_miss_with_loss
    {S : Type} {n : Nat}
    (next : S → Fin n → S)
    (P : S → Prop)
    (hc : ∀ x e, P x → P (next x e))
    (B q a : Nat)
    (hb :
      ∀ x,
        q * wordSum next (miss P) x B ≤
          a * n ^ B) :
    ∀ k x,
      q ^ k *
          wordSum next (miss P) x (k * B) ≤
        a ^ k * n ^ (k * B) := by
  classical
  intro k
  induction k with
  | zero =>
      intro x
      simpa only
        [Nat.pow_zero, Nat.zero_mul, Nat.one_mul]
        using
          (miss_mass_le next P x 0)
  | succ k ih =>
      intro x

      have hpoint :
          ∀ y,
            q *
                wordSum next (miss P) y B ≤
              (a * n ^ B) * miss P y := by
        intro y
        by_cases hy : P y
        · rw [miss_zero next P hc y hy B]
          simp [miss, hy]
        · simpa [miss, hy] using hb y

      have hsum :=
        wordSum_mono
          next
          (fun y =>
            q * wordSum next (miss P) y B)
          (fun y =>
            (a * n ^ B) * miss P y)
          hpoint
          x
          (k * B)

      have hsum' :
          q *
              wordSum next
                (fun y =>
                  wordSum next (miss P) y B)
                x (k * B) ≤
            (a * n ^ B) *
              wordSum next (miss P) x (k * B) := by
        simpa only [wordSum_mul] using hsum

      have hsplit :
          wordSum next (miss P) x ((k + 1) * B) =
            wordSum next
              (fun y =>
                wordSum next (miss P) y B)
              x (k * B) := by
        calc
          wordSum next (miss P) x ((k + 1) * B) =
              wordSum next (miss P) x (k * B + B) := by
            rw [Nat.add_mul, Nat.one_mul]
          _ =
              wordSum next
                (fun y =>
                  wordSum next (miss P) y B)
                x (k * B) :=
            wordSum_horizon_add
              next (miss P) x (k * B) B

      calc
        q ^ (k + 1) *
              wordSum next (miss P) x ((k + 1) * B) =
            q ^ k *
              (q *
                wordSum next
                  (fun y =>
                    wordSum next (miss P) y B)
                  x (k * B)) := by
          rw [hsplit, Nat.pow_succ]
          ac_rfl
        _ ≤
            q ^ k *
              ((a * n ^ B) *
                wordSum next (miss P) x (k * B)) :=
          Nat.mul_le_mul_left _ hsum'
        _ =
            (a * n ^ B) *
              (q ^ k *
                wordSum next (miss P) x (k * B)) := by
          ac_rfl
        _ ≤
            (a * n ^ B) *
              (a ^ k * n ^ (k * B)) :=
          Nat.mul_le_mul_left _ (ih x)
        _ =
            a ^ (k + 1) *
              n ^ ((k + 1) * B) := by
          rw [Nat.pow_succ, Nat.add_mul, Nat.one_mul, Nat.pow_add]
          ac_rfl

end PPL

#print axioms PPL.amplify_miss_with_loss
