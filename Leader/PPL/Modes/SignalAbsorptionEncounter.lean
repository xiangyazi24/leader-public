import Leader.PPL.Modes.SignalAbsorptionSplit
import Leader.Core.LeaderCountDyadicTail

namespace PPL.Modes.Lemma9

set_option autoImplicit false

open PPL.Probability

/--
Encounter lower tail for paper Lemma 9.

The stopped predictable-host failure numerator is first dominated by the exact
two-edge lower tail.  At T = n*E, the public Bernoulli inequality gives a
half-life every n-1 powers:
  2*(n-1)^(n-1) ≤ n^(n-1).
The first (n-1)*E powers supply E factors of two.  Since
(n-1)*(2*psi) ≤ E at the Lemma-9 scale, the remaining E powers supply another
2*psi factors.  This is enough to absorb n^2 ≤ 2^(2*psi).
-/
theorem lemma9EncounterLowerTail :
    Lemma9EncounterLowerTail := by
  intro n psi c hn3 hpsi hc hnpow ring host stop htails

  have hn2 : 2 ≤ n := by
    omega

  let E : Nat := lemma9E psi c
  let T : Nat := lemma9T n psi c
  let K : Nat := 2 * psi
  let d : Nat := n - 1

  change
    n * n *
        stoppedPredictableHostLowerFailureCount
          ring host stop T E ≤
      3 * n ^ T

  have hhost :=
    htails n T E hn2 ring host
  have hdom :
      stoppedPredictableHostLowerFailureCount
          ring host stop T E ≤
        twoEdgeLowerTailCount n T E :=
    (hhost.2.2 stop).2

  have hdpos : 0 < d := by
    dsimp [d]
    omega

  have hdn : d + 1 = n := by
    dsimp [d]
    omega

  have hber :=
    LeaderCountDyadicTail.bernoulli_scaled d d

  have hscaled :
      d * (2 * d ^ d) ≤
        d * n ^ d := by
    calc
      d * (2 * d ^ d) =
          (d + d) * d ^ d := by
        simp only [Nat.two_mul, Nat.add_mul, Nat.mul_add]
      _ ≤ d * (d + 1) ^ d := hber
      _ = d * n ^ d := by
        rw [hdn]

  have hblock :
      2 * d ^ d ≤ n ^ d :=
    Nat.le_of_mul_le_mul_left hscaled hdpos

  have hfirst :
      2 ^ E * d ^ (d * E) ≤
        n ^ (d * E) := by
    simpa only [Nat.mul_pow, ← Nat.pow_mul] using
      (Nat.pow_le_pow_left hblock E)

  have hdlePow :
      d ≤ 2 ^ psi := by
    dsimp [d]
    omega

  have hcoef : 2 ≤ 64 * c := by
    omega

  have hdk :
      d * K ≤ E := by
    calc
      d * K ≤ (2 ^ psi) * K :=
        Nat.mul_le_mul_right K hdlePow
      _ = 2 * (psi * 2 ^ psi) := by
        dsimp [K]
        ac_rfl
      _ ≤ (64 * c) * (psi * 2 ^ psi) :=
        Nat.mul_le_mul_right (psi * 2 ^ psi) hcoef
      _ = E := by
        dsimp [E, lemma9E, lotteryL8Horizon]
        ac_rfl

  have hkcore :
      2 ^ K * d ^ (d * K) ≤
        n ^ (d * K) := by
    simpa only [Nat.mul_pow, ← Nat.pow_mul] using
      (Nat.pow_le_pow_left hblock K)

  let R : Nat := E - d * K

  have hER :
      E = d * K + R := by
    dsimp [R]
    omega

  have hdleN : d ≤ n := by
    dsimp [d]
    omega

  have hrem :
      d ^ R ≤ n ^ R :=
    Nat.pow_le_pow_left hdleN R

  have hsecond :
      2 ^ K * d ^ E ≤ n ^ E := by
    calc
      2 ^ K * d ^ E =
          (2 ^ K * d ^ (d * K)) * d ^ R := by
        rw [hER, Nat.pow_add]
        ac_rfl
      _ ≤ n ^ (d * K) * n ^ R :=
        Nat.mul_le_mul hkcore hrem
      _ = n ^ E := by
        rw [hER, Nat.pow_add]

  have hboth :=
    Nat.mul_le_mul hfirst hsecond

  have hTdef :
      T = n * E := by
    rfl

  have hTdecomp :
      T = d * E + E := by
    rw [hTdef, ← hdn, Nat.add_mul, Nat.one_mul]

  have hdecay :
      2 ^ (E + K) * d ^ T ≤ n ^ T := by
    calc
      2 ^ (E + K) * d ^ T =
          (2 ^ E * d ^ (d * E)) *
            (2 ^ K * d ^ E) := by
        rw [hTdecomp, Nat.pow_add, Nat.pow_add]
        ac_rfl
      _ ≤ n ^ (d * E) * n ^ E := hboth
      _ = n ^ T := by
        rw [hTdecomp, Nat.pow_add]

  have hET : E ≤ T := by
    rw [hTdef]
    calc
      E = 1 * E := by
        simp
      _ ≤ n * E :=
        Nat.mul_le_mul_right E (by omega)

  have ha : E ≤ T + 1 := by
    omega

  have hscale :
      LowerTailScaleArithmetic n T E K := by
    unfold LowerTailScaleArithmetic
    have hbase :
        2 * n - 2 = 2 * d := by
      dsimp [d]
      omega
    rw [hbase, Nat.mul_pow]

    have hexp :
        T + K ≤ (T + 1 - E) + (E + K) := by
      omega

    have hp :
        2 ^ (T + K) ≤
          2 ^ ((T + 1 - E) + (E + K)) :=
      Nat.pow_le_pow_right (by decide) hexp

    have hleft :
        (2 ^ T * d ^ T) * 2 ^ K ≤
          2 ^ (T + 1 - E) *
            (2 ^ (E + K) * d ^ T) := by
      calc
        (2 ^ T * d ^ T) * 2 ^ K =
            2 ^ (T + K) * d ^ T := by
          rw [Nat.pow_add]
          ac_rfl
        _ ≤
            2 ^ ((T + 1 - E) + (E + K)) *
              d ^ T :=
          Nat.mul_le_mul_right (d ^ T) hp
        _ =
            2 ^ (T + 1 - E) *
              (2 ^ (E + K) * d ^ T) := by
          rw [Nat.pow_add]
          ac_rfl

    have hm :=
      Nat.mul_le_mul_left
        (2 ^ (T + 1 - E)) hdecay

    calc
      (2 ^ T * d ^ T) * 2 ^ K ≤
          2 ^ (T + 1 - E) *
            (2 ^ (E + K) * d ^ T) := hleft
      _ ≤ 2 ^ (T + 1 - E) * n ^ T := hm
      _ = n ^ T * 2 ^ (T + 1 - E) := by
        ac_rfl

  have hraw :
      twoEdgeLowerTailCount n T E * 2 ^ K ≤
        n ^ T :=
    twoEdgeLowerTail_scaled_of_arithmetic
      n T E K hn2 ha hscale

  have hnn :
      n * n ≤ 2 ^ K := by
    have hsq :=
      Nat.mul_le_mul hnpow hnpow
    calc
      n * n ≤ (2 ^ psi) * (2 ^ psi) := hsq
      _ = 2 ^ (psi + psi) := by
        rw [Nat.pow_add]
      _ = 2 ^ K := by
        rw [show psi + psi = K by
          dsimp [K]
          omega]

  calc
    n * n *
        stoppedPredictableHostLowerFailureCount
          ring host stop T E ≤
        n * n * twoEdgeLowerTailCount n T E :=
      Nat.mul_le_mul_left (n * n) hdom
    _ ≤
        2 ^ K * twoEdgeLowerTailCount n T E :=
      Nat.mul_le_mul_right
        (twoEdgeLowerTailCount n T E) hnn
    _ =
        twoEdgeLowerTailCount n T E * 2 ^ K := by
      ac_rfl
    _ ≤ n ^ T := hraw
    _ ≤ 3 * n ^ T := by
      omega

end PPL.Modes.Lemma9

#print axioms PPL.Modes.Lemma9.lemma9EncounterLowerTail
