import Leader.AAFJ.TwoBarrier.RingSixMPlusFourConstantMass
import Leader.Wu.Splice.OrderedWindowMatcher

set_option autoImplicit false
set_option Elab.async false

namespace AAFJPK.N6m4Premises

open N6m4ColoredChildTable
open N6m4ConstantMass

/-- On the special family N = 6m+4, a q = 2m+1 Bernoulli block
already gains a factor 4/3. -/
private theorem four_pred_block_le_three (m : Nat) :
    4 * (N m - 1) ^ (2 * m + 1) ≤
      3 * (N m) ^ (2 * m + 1) := by
  let q := 2 * m + 1
  have hq : 0 < q := by
    dsimp [q]
    omega
  have hpred : N m - 1 = 3 * q := by
    dsimp [N, q]
    omega
  have hsucc : N m - 1 + 1 = N m := by
    dsimp [N] <;> omega
  have hqsub : q - 1 + 1 = q := by
    omega
  have hb0 :=
    B9OrderedWindowMatcher.bernoulli (N m - 1) (q - 1)
  have hb :
      (N m - 1) ^ q +
          q * (N m - 1) ^ (q - 1) ≤
        (N m) ^ q := by
    simpa [hqsub, hsucc] using hb0
  have hmul := Nat.mul_le_mul_left 3 hb
  have hpow :
      3 * q * (N m - 1) ^ (q - 1) =
        (N m - 1) ^ q := by
    rw [hpred]
    obtain ⟨k, hk⟩ : ∃ k, q = k + 1 := ⟨q - 1, by omega⟩
    rw [hk, Nat.add_sub_cancel, Nat.pow_succ]
    ac_rfl
  change
    4 * (N m - 1) ^ q ≤
      3 * (N m) ^ q
  calc
    4 * (N m - 1) ^ q =
        3 * (N m - 1) ^ q + (N m - 1) ^ q := by
          omega
    _ =
        3 * (N m - 1) ^ q +
          3 * q * (N m - 1) ^ (q - 1) := by
          rw [hpow]
    _ =
        3 *
          ((N m - 1) ^ q +
            q * (N m - 1) ^ (q - 1)) := by
          rw [Nat.mul_add 3 ((N m - 1) ^ q) (q * (N m - 1) ^ (q - 1)),
            Nat.mul_assoc 3 q]
    _ ≤ 3 * (N m) ^ q := hmul

/-- A uniform one-block ratio for the N=6m+4 family. -/
private theorem sixtyfour_pred_pow_le_twentyseven (m : Nat) :
    64 * (N m - 1) ^ (N m) ≤
      27 * (N m) ^ (N m) := by
  let q := 2 * m + 1
  have hb :
      4 * (N m - 1) ^ q ≤
        3 * (N m) ^ q := by
    simpa [q] using four_pred_block_le_three m
  have hc := Nat.pow_le_pow_left hb 3
  have hc' :
      64 * (N m - 1) ^ (3 * q) ≤
        27 * (N m) ^ (3 * q) := by
    simpa [Nat.mul_pow, ← Nat.pow_mul, Nat.mul_assoc,
      Nat.mul_left_comm, Nat.mul_comm] using hc
  have hbase : N m - 1 ≤ N m := by
    omega
  have hmul := Nat.mul_le_mul hc' hbase
  have hN : N m = 3 * q + 1 := by
    dsimp [N, q]
    omega
  calc
    64 * (N m - 1) ^ (N m) =
        (64 * (N m - 1) ^ (3 * q)) * (N m - 1) := by
          rw [hN, Nat.pow_succ]
          ac_rfl
    _ ≤ (27 * (N m) ^ (3 * q)) * N m := hmul
    _ = 27 * (N m) ^ (N m) := by
          rw [hN, Nat.pow_succ]
          ac_rfl

private theorem thirtytwo_pred_pow_three_le_three (m : Nat) :
    32 * (N m - 1) ^ (3 * N m) ≤
      3 * (N m) ^ (3 * N m) := by
  have h :=
    Nat.pow_le_pow_left
      (sixtyfour_pred_pow_le_twentyseven m) 3
  have hs :
      262144 * (N m - 1) ^ (3 * N m) ≤
        19683 * (N m) ^ (3 * N m) := by
    simpa [Nat.mul_pow, ← Nat.pow_mul, Nat.mul_assoc,
      Nat.mul_left_comm, Nat.mul_comm] using h
  omega

private theorem onefive68_pred_pow_six_le_twelve (m : Nat) :
    1568 * (N m - 1) ^ (6 * N m) ≤
      12 * (N m) ^ (6 * N m) := by
  have h :=
    Nat.pow_le_pow_left
      (sixtyfour_pred_pow_le_twentyseven m) 6
  have hs :
      68719476736 * (N m - 1) ^ (6 * N m) ≤
        387420489 * (N m) ^ (6 * N m) := by
    simpa [Nat.mul_pow, ← Nat.pow_mul, Nat.mul_assoc,
      Nat.mul_left_comm, Nat.mul_comm] using h
  omega

/-- First arithmetic premise of product_bounds_to_1085_Dm, uniformly in m. -/
theorem hA (m : Nat) :
    5 * (N m) ^ (3 * N m) ≤
      64 * A (N m) := by
  have hn : 2 ≤ N m := by
    unfold N
    omega
  have hsum :=
    markedCount_add_lowCount
      (n := N m) (k := 3) (T := 3 * N m) hn
  have hlow0 :=
    lowCount_le_half_weight
      (n := N m) (T := 3 * N m) hn 2
  have hlow :
      8 * lowCount (N m) 3 (3 * N m) ≤
        3 * (N m) ^ (3 * N m) := by
    calc
      8 * lowCount (N m) 3 (3 * N m) ≤
          8 *
            (2 ^ 2 *
              (N m - 1) ^ (3 * N m)) :=
        Nat.mul_le_mul_left 8 hlow0
      _ = 32 * (N m - 1) ^ (3 * N m) := by
        simp [Nat.mul_assoc] <;> omega
      _ ≤ 3 * (N m) ^ (3 * N m) :=
        thirtytwo_pred_pow_three_le_three m
  have hmark :
      5 * (N m) ^ (3 * N m) ≤
        8 * markedCount (N m) 3 (3 * N m) := by
    omega
  have hscale :=
    markedCount_eq_scaled_goodCount
      (n := N m) (k := 3) (T := 3 * N m) hn
  change
    5 * (N m) ^ (3 * N m) ≤
      64 * goodCount (N m) 3 (3 * N m)
  calc
    5 * (N m) ^ (3 * N m) ≤
        8 * markedCount (N m) 3 (3 * N m) := hmark
    _ = 64 * goodCount (N m) 3 (3 * N m) := by
      rw [← hscale]
      simp [Nat.mul_assoc] <;> omega

/-- Second arithmetic premise of product_bounds_to_1085_Dm, uniformly in m. -/
theorem hG (m : Nat) :
    37 * (N m) ^ (6 * N m) ≤
      3136 * G (N m) := by
  have hn : 2 ≤ N m := by
    unfold N
    omega
  have hsum :=
    markedCount_add_lowCount
      (n := N m) (k := 6) (T := 6 * N m) hn
  have hlow0 :=
    lowCount_le_half_weight
      (n := N m) (T := 6 * N m) hn 5
  have hlow :
      49 * lowCount (N m) 6 (6 * N m) ≤
        12 * (N m) ^ (6 * N m) := by
    calc
      49 * lowCount (N m) 6 (6 * N m) ≤
          49 *
            (2 ^ 5 *
              (N m - 1) ^ (6 * N m)) :=
        Nat.mul_le_mul_left 49 hlow0
      _ = 1568 * (N m - 1) ^ (6 * N m) := by
        simp [Nat.mul_assoc] <;> omega
      _ ≤ 12 * (N m) ^ (6 * N m) :=
        onefive68_pred_pow_six_le_twelve m
  have hmark :
      37 * (N m) ^ (6 * N m) ≤
        49 * markedCount (N m) 6 (6 * N m) := by
    omega
  have hscale :=
    markedCount_eq_scaled_goodCount
      (n := N m) (k := 6) (T := 6 * N m) hn
  change
    37 * (N m) ^ (6 * N m) ≤
      3136 * goodCount (N m) 6 (6 * N m)
  calc
    37 * (N m) ^ (6 * N m) ≤
        49 * markedCount (N m) 6 (6 * N m) := hmark
    _ = 3136 * goodCount (N m) 6 (6 * N m) := by
      rw [← hscale]
      simp [Nat.mul_assoc] <;> omega

/-!
## Exact remaining hfamily decomposition

These are statements for the next file/round, not declarations in this
proof-complete arithmetic file.

The physical encoder should have this raw type:

noncomputable def physicalEncodeWord
    (m : Nat)
    (p : List (Fin (N m)) × List (Fin (N m))) :
    List (Fin (N m))

First remove the current positive-m artifact in the family geometry:

theorem S0_support_all {m : Nat} (e : Fin (N m)) :
    BarrierAt (by decide : 0 < 3) (ring m)
        (labelsOf (S0 (m := m))) e ↔
      e = v0 m ∨ e = v2 m

theorem H_support_all {m : Nat} (e : Fin (N m)) :
    BarrierAt (by decide : 0 < 3) (ring m)
        (labelsOf (H (m := m))) e ↔
      e = v1 m ∨ e = v2 m

The encoder obligations are:

theorem physicalEncode_length
    {m : Nat}
    {p : List (Fin (N m)) × List (Fin (N m))}
    (hp : p ∈ ContactAdaptiveDropCodePairs m) :
    (physicalEncodeWord m p).length = 9 * N m

theorem physicalEncode_strict_drop
    {m : Nat}
    {p : List (Fin (N m)) × List (Fin (N m))}
    (hp : p ∈ ContactAdaptiveDropCodePairs m) :
    barrierCount (by decide : 0 < 3) (ring m)
        (labelsOf
          (rawRun (by decide : 0 < 3) (ring m) S0
            (physicalEncodeWord m p))) <
      barrierCount (by decide : 0 < 3) (ring m)
        (labelsOf S0)

theorem physicalEncode_injective_on_codes
    {m : Nat}
    {p q : List (Fin (N m)) × List (Fin (N m))}
    (hp : p ∈ ContactAdaptiveDropCodePairs m)
    (hq : q ∈ ContactAdaptiveDropCodePairs m)
    (heq : physicalEncodeWord m p = physicalEncodeWord m q) :
    p = q

The finite-list counting bridge then needs only duplicate-freedom:

theorem ContactAdaptiveDropCodePairs_nodup (m : Nat) :
    (ContactAdaptiveDropCodePairs m).Nodup

theorem encodedPairs_le_Dm (m : Nat) :
    (ContactAdaptiveDropCodePairs m).length ≤
      Dm m (9 * N m)

and finally:

theorem hfamily (m : Nat) :
    A (N m) * G (N m) ≤ Dm m (9 * N m)

physicalEncode_strict_drop is the hard lemma. Its proof should scan the
reversed contact code until the first three marked zeroes, producing the
literal contact path, then scan the reversed drop code with the state-dependent
alphabet and OriginalRawSixTrace.rawTrace_decompose. The good-code property
rules out a competitor before the required marked zeroes. An early parser
drop is success; a six-hit complete is discharged by
sixCompleteEndpoint_drops; unused code tails are appended after success.
physicalEncode_injective_on_codes then decodes the same scan using the
injectivity of the current free-edge enumeration and fixed residual lengths.
-/

#print axioms hA
#print axioms hG

end AAFJPK.N6m4Premises
