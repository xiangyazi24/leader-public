import Leader.PPL.MainTheorem.Skeleton
import Init.Data.Nat.Log2
import Init.Omega

/-!
P_PL Theorem 1 cleanup, phase 2: the declarations of this file that served only the old
psi <= log2 n + 1 route to `theorem1Statement_proved` moved to
`Leader/PPL/LogWindow/Kappa.lean`, namespace `PPL.Superseded.LogWindow`: `theorem1_quietWindow_covers_run`.
-/

namespace PPL

set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false

/--
Absolute protocol constant of Theorem 1.

The factor 16 simultaneously preserves the exact parameter forms consumed by
Lemma 16 and Lemma 5(ii).  The inner coefficient is exactly the bound needed
to fit H17 + H18 inside the fixed Lemma-5(ii) quiet window.
-/
def theorem1C1 : Nat :=
  16 * (4 * theorem1C17 + 24)

/-- Clock parameter of Theorem 1. -/
def theorem1Kappa (psi : Nat) : Nat :=
  theorem1C1 * psi

/--
The Lemma-16 mode constant witnessing
  theorem1Kappa = 8 * modeC * psi.
-/
def theorem1ModeC : Nat :=
  2 * (4 * theorem1C17 + 24)

/--
The Lemma-5(ii) constant witnessing
  theorem1Kappa = 16 * c * psi.
-/
def theorem1Lemma5iiC : Nat :=
  4 * theorem1C17 + 24

/--
Top-level horizon: Lemma 17 and Lemma 18 execute inside the fixed
Lemma-5(ii) Construct window rather than after it.
-/
def theorem1Horizon (n psi : Nat) : Nat :=
  PPL.Convergence.ReachCPB.lemma16Horizon
      n psi (theorem1Kappa psi) +
    PPL.Modes.Lemma5.lemma5iHorizon n +
    PPL.Modes.Lemma5.lemma5iiHorizon
      n psi (theorem1Kappa psi)

/-- Exact parameter form required by the committed Lemma-16 theorem. -/
theorem theorem1Kappa_eq_lemma16_form
    (psi : Nat) :
    theorem1Kappa psi =
      8 * theorem1ModeC * psi := by
  unfold theorem1Kappa theorem1C1
    theorem1ModeC theorem1C17
  omega

theorem theorem1ModeC_ge_six :
    6 ≤ theorem1ModeC := by
  unfold theorem1ModeC theorem1C17
  omega

/-- Exact parameter form required by the committed Lemma-5(ii) theorem. -/
theorem theorem1Kappa_eq_lemma5ii_form
    (psi : Nat) :
    theorem1Kappa psi =
      16 * theorem1Lemma5iiC * psi := by
  unfold theorem1Kappa theorem1C1
    theorem1Lemma5iiC theorem1C17
  omega

theorem theorem1Lemma5iiC_ge_three :
    3 ≤ theorem1Lemma5iiC := by
  unfold theorem1Lemma5iiC theorem1C17
  omega

/-- The generic Lemma-5(i) numerical premise is automatic. -/
theorem theorem1Kappa_ge_48_mul
    (psi : Nat) :
    48 * psi ≤ theorem1Kappa psi := by
  unfold theorem1Kappa theorem1C1 theorem1C17
  omega

/--
The lower power-window inequality already implies log2 n <= psi.
-/
theorem theorem1_log2_le_psi
    {n psi : Nat}
    (hn3 : 3 ≤ n)
    (hnpow : n ≤ 2 ^ psi) :
    Nat.log2 n ≤ psi := by
  have hn0 : n ≠ 0 := by
    omega
  by_cases hle : Nat.log2 n ≤ psi
  · exact hle
  · have hs :
        psi + 1 ≤ Nat.log2 n := by
      omega
    have hp :
        2 ^ (psi + 1) ≤ n :=
      (Nat.le_log2 hn0).1 hs
    rw [Nat.pow_succ] at hp
    have hp0 :
        0 < 2 ^ psi :=
      Nat.pow_pos (by decide)
    omega

theorem theorem1K_le_psi_add_one
    {n psi : Nat}
    (hn3 : 3 ≤ n)
    (hnpow : n ≤ 2 ^ psi) :
    theorem1K n ≤ psi + 1 := by
  have hlog :=
    theorem1_log2_le_psi hn3 hnpow
  unfold theorem1K
  omega

/--
For zeta = ceil(n/psi), the number zeta-2 of Lemma-4 build blocks satisfies
  (zeta-2) * psi <= n.
-/
theorem theorem1_l18BlockCount_mul_psi_le
    {n psi : Nat}
    (hpsi : 2 ≤ psi) :
    PPL.Convergence.L18.l18BlockCount n psi * psi ≤ n := by
  unfold PPL.Convergence.L18.l18BlockCount
  let z := PPL.segmentCount n psi
  change (z - 2) * psi ≤ n
  have hmul :
      z * psi ≤ n + psi - 1 := by
    dsimp only [z]
    unfold PPL.segmentCount
    exact
      Nat.div_mul_le_self
        (n + psi - 1) psi
  by_cases hz : 2 ≤ z
  · rw [Nat.sub_mul]
    omega
  · have hz0 : z - 2 = 0 := by
      omega
    rw [hz0, Nat.zero_mul]
    exact Nat.zero_le n

/-- Direct bound from the current l18Length definition. -/
theorem theorem1_l18Length_le
    {n psi : Nat}
    (hpsi : 2 ≤ psi) :
    PPL.Convergence.L18.l18Length n psi ≤
      2 * n + 2 * psi + 8 * n * psi := by
  have hb :=
    theorem1_l18BlockCount_mul_psi_le
      (n := n) hpsi
  have hcoef :
      8 * psi * psi - 4 * psi ≤
        8 * psi * psi :=
    Nat.sub_le _ _
  have hterm :
      PPL.Convergence.L18.l18BlockCount n psi *
          (8 * psi * psi - 4 * psi) ≤
        8 * n * psi := by
    calc
      PPL.Convergence.L18.l18BlockCount n psi *
            (8 * psi * psi - 4 * psi) ≤
          PPL.Convergence.L18.l18BlockCount n psi *
            (8 * psi * psi) :=
        Nat.mul_le_mul_left
          (PPL.Convergence.L18.l18BlockCount n psi)
          hcoef
      _ =
          8 *
            (PPL.Convergence.L18.l18BlockCount n psi * psi) *
            psi := by
        ac_rfl
      _ ≤ 8 * n * psi :=
        Nat.mul_le_mul_right psi
          (Nat.mul_le_mul_left 8 hb)
  unfold PPL.Convergence.L18.l18Length
  exact
    Nat.add_le_add_left hterm
      (2 * n + 2 * psi)

/--
The entire inner Lemma-18 fixed-word horizon is at most 12*n*psi.
-/
theorem theorem1_l18Core_le
    {n psi : Nat}
    (hn3 : 3 ≤ n)
    (hpsi : 2 ≤ psi)
    (hnpow : n ≤ 2 ^ psi) :
    PPL.Convergence.L18.l18Length n psi +
        4 * PPL.Convergence.L18.l18K n ≤
      12 * n * psi := by
  have hlen :=
    theorem1_l18Length_le
      (n := n) hpsi
  have hk0 :=
    theorem1K_le_psi_add_one
      hn3 hnpow
  have hk :
      PPL.Convergence.L18.l18K n ≤
        psi + 1 := by
    simpa
      [PPL.Convergence.L18.l18K,
        theorem1K]
      using hk0

  have h2n :
      2 * n ≤ n * psi := by
    have h :=
      Nat.mul_le_mul_left n hpsi
    simpa [Nat.mul_comm] using h

  have h3psi :
      3 * psi ≤ n * psi :=
    Nat.mul_le_mul_right psi hn3

  have h6psi :
      6 * psi ≤ 2 * (n * psi) := by
    have h :=
      Nat.mul_le_mul_left 2 h3psi
    calc 6 * psi = 2 * (3 * psi) := by omega
      _ ≤ 2 * (n * psi) := h

  have h4 :
      4 ≤ n * psi := by
    have h6 :
        6 ≤ 2 * n := by
      omega
    have h6' :
        6 ≤ n * psi :=
      Nat.le_trans h6 h2n
    omega

  have hbound :
      (2 * n + 2 * psi + 8 * n * psi) +
          4 * (psi + 1) ≤
        12 * n * psi := by
    have h8 :
        8 * n * psi =
          8 * (n * psi) := by
      ac_rfl
    have h12 :
        12 * n * psi =
          12 * (n * psi) := by
      ac_rfl
    rw [h8, h12]
    omega

  calc
    PPL.Convergence.L18.l18Length n psi +
          4 * PPL.Convergence.L18.l18K n ≤
        (2 * n + 2 * psi + 8 * n * psi) +
          4 * (psi + 1) :=
      Nat.add_le_add hlen
        (Nat.mul_le_mul_left 4 hk)
    _ ≤ 12 * n * psi :=
      hbound

/-- Lemma 17 fits in coefficient 4*C17 of n*psi*2^psi. -/
theorem theorem1_H17_le
    {n psi : Nat}
    (hn3 : 3 ≤ n)
    (hpsi : 2 ≤ psi)
    (hnpow : n ≤ 2 ^ psi) :
    PPL.Convergence.L17.H17 theorem1C17 n ≤
      4 * theorem1C17 *
        (n * psi * 2 ^ psi) := by
  have hk0 :=
    theorem1K_le_psi_add_one
      hn3 hnpow
  have hk1 :
      PPL.Convergence.L17.K n ≤
        psi + 1 := by
    simpa
      [PPL.Convergence.L17.K,
        theorem1K]
      using hk0
  have hk :
      PPL.Convergence.L17.K n ≤
        2 * psi := by
    omega
  unfold PPL.Convergence.L17.H17
  calc
    2 * theorem1C17 * n * n *
          PPL.Convergence.L17.K n ≤
        2 * theorem1C17 * n * n *
          (2 * psi) :=
      Nat.mul_le_mul_left
        (2 * theorem1C17 * n * n) hk
    _ = 4 * theorem1C17 * n * n * psi := by
      ac_rfl
    _ ≤
        4 * theorem1C17 * n *
          (2 ^ psi) * psi :=
      Nat.mul_le_mul_right psi
        (Nat.mul_le_mul_left
          (4 * theorem1C17 * n) hnpow)
    _ =
        4 * theorem1C17 *
          (n * psi * 2 ^ psi) := by
      ac_rfl

/-- Lemma 18 fits in coefficient 24 of n*psi*2^psi. -/
theorem theorem1_H18_le
    {n psi : Nat}
    (hn3 : 3 ≤ n)
    (hpsi : 2 ≤ psi)
    (hnpow : n ≤ 2 ^ psi) :
    PPL.Convergence.L18.l18Horizon n psi ≤
      24 * (n * psi * 2 ^ psi) := by
  have hcore :=
    theorem1_l18Core_le
      hn3 hpsi hnpow
  unfold PPL.Convergence.L18.l18Horizon
  calc
    2 * n *
          (PPL.Convergence.L18.l18Length n psi +
            4 * PPL.Convergence.L18.l18K n) ≤
        2 * n * (12 * n * psi) :=
      Nat.mul_le_mul_left
        (2 * n) hcore
    _ = 24 * n * n * psi := by
      ac_rfl
    _ ≤
        24 * n * (2 ^ psi) * psi :=
      Nat.mul_le_mul_right psi
        (Nat.mul_le_mul_left
          (24 * n) hnpow)
    _ = 24 * (n * psi * 2 ^ psi) := by
      ac_rfl

/-- Exact cancellation of the factor 16 in the Lemma-5(ii) horizon. -/
theorem theorem1_lemma5iiHorizon_eq
    (n psi : Nat) :
    PPL.Modes.Lemma5.lemma5iiHorizon
        n psi (theorem1Kappa psi) =
      (4 * theorem1C17 + 24) *
        (n * psi * 2 ^ psi) := by
  unfold PPL.Modes.Lemma5.lemma5iiHorizon
    theorem1Kappa theorem1C1
  have hdiv :
      n * (16 * (4 * theorem1C17 + 24) * psi) / 16 =
        n * (4 * theorem1C17 + 24) * psi := by
    have heq :
        n * (16 * (4 * theorem1C17 + 24) * psi) =
          (n * (4 * theorem1C17 + 24) * psi) * 16 := by
      ac_rfl
    rw [heq]
    exact
      Nat.mul_div_left
        (n * (4 * theorem1C17 + 24) * psi)
        (by decide)
  rw [hdiv]
  ac_rfl

end PPL

#print axioms PPL.theorem1Kappa_eq_lemma16_form
#print axioms PPL.theorem1Kappa_eq_lemma5ii_form
#print axioms PPL.theorem1Kappa_ge_48_mul
#print axioms PPL.theorem1_l18Length_le
#print axioms PPL.theorem1_H17_le
#print axioms PPL.theorem1_H18_le
