import Leader.PPL.MainTheorem.Statement
import Leader.PPL.StateCount
import Init.Omega


namespace PPL


set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false


/-!
# Paper-facing finite-state and horizon bounds for Theorem 1


F.2 gives an explicit degree-six polylogarithmic state-count bound.


F.3 gives an explicit horizon bound
  A * 2^s * n^2 * (log2 n + s + 1)
under the paper window
  n <= 2^psi
  psi <= log2 n + s.


No Mathlib asymptotics are used.
-/


/-- Absolute constant for the paper-facing local-state bound. -/
def theorem1StateD : Nat :=
  1000000000000000000000


/-- Absolute constant for the paper-facing horizon bound. -/
def theorem1HorizonA : Nat :=
  1000000000


/-! ## F.2: exact local carrier and explicit state-count bound -/


/--
The enumeration used for the Theorem-1 local carrier is duplicate-free.
This is the landed exactness lemma, specialized to `theorem1Kappa`.
-/
theorem theorem1_stateEnumeration_nodup
    (psi : Nat) :
    (PPLv2.states psi (theorem1Kappa psi)).values.Nodup := by
  exact
    PPLv2.states_nodup
      psi (theorem1Kappa psi)


/--
The finite index set of size
`(PPLv2.states psi (theorem1Kappa psi)).values.length`
is in bijection with the actual local state type of `PPL.protocol`.


Thus the exhaustive-list length is the exact number of local states, not
merely an upper bound.
-/
theorem theorem1_stateCount_exact
    (psi : Nat) :
    Exists fun decode :
        Fin
            ((PPLv2.states
                psi (theorem1Kappa psi)).values.length) ->
          (protocol psi (theorem1Kappa psi)).Q =>
      And
        (Function.Injective decode)
        (Function.Surjective decode) := by
  refine
    ⟨(PPLv2.states
        psi (theorem1Kappa psi)).decode, ?_⟩
  exact
    PPLv2.states_decode_bijective
      psi (theorem1Kappa psi)


/--
Explicit F.2 bound.


The exact formula has factors of degrees
  1 + 2 + 2 + 1 = 6
in `psi`, after substituting
  kappa = theorem1C1 * psi.
-/
theorem theorem1_stateCount_le
    (s : Nat) :
    forall n psi : Nat,
      3 <= n ->
      2 <= psi ->
      psi <= Nat.log2 n + s ->
      (PPLv2.states
          psi (theorem1Kappa psi)).values.length <=
        theorem1StateD *
          (Nat.log2 n + s + 1) ^ 6 := by
  intro n psi _hn3 hpsi hpsiUpper


  let X := Nat.log2 n + s + 1


  have hpsiPos : 0 < psi := by
    omega


  have hX1 : 1 <= X := by
    dsimp [X]
    omega


  have hpsiX : psi <= X := by
    dsimp [X]
    omega


  have hpsi1X : psi + 1 <= X := by
    dsimp [X]
    omega


  have htoken :
      8 * psi - 3 <= 8 * X := by
    calc
      8 * psi - 3 <= 8 * psi :=
        Nat.sub_le _ _
      _ <= 8 * X :=
        Nat.mul_le_mul_left 8 hpsiX


  have htoken2 :
      (8 * psi - 3) ^ 2 <=
        64 * X ^ 2 := by
    have h :=
      Nat.pow_le_pow_left htoken 2
    simpa only
      [Nat.mul_pow,
        show (8 : Nat) ^ 2 = 64 by decide]
      using h


  have hkappaX :
      theorem1Kappa psi + 1 <=
        (theorem1C1 + 1) * X := by
    unfold theorem1Kappa
    have hmul :
        theorem1C1 * psi <=
          theorem1C1 * X :=
      Nat.mul_le_mul_left theorem1C1 hpsiX
    calc
      theorem1C1 * psi + 1 <=
          theorem1C1 * X + X :=
        Nat.add_le_add hmul hX1
      _ = (theorem1C1 + 1) * X := by
        rw [Nat.add_mul]
        simp


  have hkappa2 :
      (theorem1Kappa psi + 1) ^ 2 <=
        (theorem1C1 + 1) ^ 2 * X ^ 2 := by
    have h :=
      Nat.pow_le_pow_left hkappaX 2
    simpa only [Nat.mul_pow] using h


  have hfirst :
      384 * psi <= 384 * X :=
    Nat.mul_le_mul_left 384 hpsiX


  have hsecond :
      384 * psi * (8 * psi - 3) ^ 2 <=
        384 * X * (64 * X ^ 2) :=
    Nat.mul_le_mul hfirst htoken2


  have hthird :
      384 * psi * (8 * psi - 3) ^ 2 *
          (theorem1Kappa psi + 1) ^ 2 <=
        384 * X * (64 * X ^ 2) *
          ((theorem1C1 + 1) ^ 2 * X ^ 2) :=
    Nat.mul_le_mul hsecond hkappa2


  have hproduct :
      384 * psi * (8 * psi - 3) ^ 2 *
          (theorem1Kappa psi + 1) ^ 2 *
          (psi + 1) <=
        384 * X * (64 * X ^ 2) *
          ((theorem1C1 + 1) ^ 2 * X ^ 2) *
          X :=
    Nat.mul_le_mul hthird hpsi1X


  have hX6 :
      X * X ^ 2 * X ^ 2 * X =
        X ^ 6 := by
    simp only
      [Nat.pow_succ, Nat.pow_zero, Nat.one_mul]
    ac_rfl


  have hfactor :
      384 * X * (64 * X ^ 2) *
          ((theorem1C1 + 1) ^ 2 * X ^ 2) *
          X =
        (384 * 64 * (theorem1C1 + 1) ^ 2) *
          X ^ 6 := by
    calc
      384 * X * (64 * X ^ 2) *
            ((theorem1C1 + 1) ^ 2 * X ^ 2) *
            X =
          (384 * 64 *
              (theorem1C1 + 1) ^ 2) *
            (X * X ^ 2 * X ^ 2 * X) := by
        ac_rfl
      _ =
          (384 * 64 *
              (theorem1C1 + 1) ^ 2) *
            X ^ 6 := by
        rw [hX6]


  have hD :
      384 * 64 * (theorem1C1 + 1) ^ 2 <=
        theorem1StateD := by
    unfold theorem1StateD theorem1C1 theorem1C17
    decide


  rw
    [PPLv2.states_length_eq_paper_formula
      psi (theorem1Kappa psi) hpsiPos]


  calc
    384 * psi * (8 * psi - 3) ^ 2 *
          (theorem1Kappa psi + 1) ^ 2 *
          (psi + 1) <=
        384 * X * (64 * X ^ 2) *
          ((theorem1C1 + 1) ^ 2 * X ^ 2) *
          X :=
      hproduct
    _ =
        (384 * 64 *
            (theorem1C1 + 1) ^ 2) *
          X ^ 6 :=
      hfactor
    _ <= theorem1StateD * X ^ 6 :=
      Nat.mul_le_mul_right (X ^ 6) hD
    _ =
        theorem1StateD *
          (Nat.log2 n + s + 1) ^ 6 := by
      simp [X]


/-! ## F.3: explicit horizon bound -/


/--
The slack window converts the exponential factor in every clock term to
`2^s * n`.
-/
private theorem theorem1_two_pow_psi_le_slack
    {n psi s : Nat}
    (hn3 : 3 <= n)
    (hpsiUpper : psi <= Nat.log2 n + s) :
    2 ^ psi <= 2 ^ s * n := by
  have hn0 : n ≠ 0 := by
    omega


  have hmono :
      2 ^ psi <=
        2 ^ (Nat.log2 n + s) :=
    Nat.pow_le_pow_right
      (by decide : 0 < (2 : Nat))
      hpsiUpper


  have hlog :
      2 ^ Nat.log2 n <= n :=
    (Nat.le_log2 hn0).1
      (Nat.le_refl (Nat.log2 n))


  calc
    2 ^ psi <=
        2 ^ (Nat.log2 n + s) :=
      hmono
    _ =
        2 ^ Nat.log2 n * 2 ^ s := by
      rw [Nat.pow_add]
    _ <= n * 2 ^ s :=
      Nat.mul_le_mul_right (2 ^ s) hlog
    _ = 2 ^ s * n := by
      ac_rfl


/--
Explicit F.3 horizon bound.


The premise `n <= 2^psi` is retained because it is part of the Theorem-1
paper window.  This coarse upper bound itself only needs the upper slack
window and `n >= 3`.
-/
theorem theorem1Horizon_le
    (s : Nat) :
    forall n psi : Nat,
      3 <= n ->
      2 <= psi ->
      n <= 2 ^ psi ->
      psi <= Nat.log2 n + s ->
      theorem1Horizon n psi <=
        theorem1HorizonA *
          2 ^ s * n ^ 2 *
          (Nat.log2 n + s + 1) := by
  intro n psi hn3 _hpsi _hnpow hpsiUpper


  let X := Nat.log2 n + s + 1
  let T := 2 ^ s * n ^ 2 * X


  have hX1 : 1 <= X := by
    dsimp [X]
    omega


  have hpsiX : psi <= X := by
    dsimp [X]
    omega


  have hKX :
      Nat.log2 n + 1 <= X := by
    dsimp [X]
    omega


  have hsPos : 0 < 2 ^ s :=
    Nat.pow_pos (by decide)


  have hs1 : 1 <= 2 ^ s := by
    omega


  have hn1 : 1 <= n := by
    omega


  have hn_n2 :
      n <= n ^ 2 := by
    calc
      n = n * 1 := by
        simp
      _ <= n * n :=
        Nat.mul_le_mul_left n hn1
      _ = n ^ 2 := by
        simp [Nat.pow_two]


  have hn2T :
      n ^ 2 <= T := by
    have hleft :
        1 * n ^ 2 <=
          2 ^ s * n ^ 2 :=
      Nat.mul_le_mul hs1
        (Nat.le_refl (n ^ 2))
    have h :=
      Nat.mul_le_mul hleft hX1
    simpa [T] using h


  have hnT :
      n <= T :=
    Nat.le_trans hn_n2 hn2T


  have hnKT :
      n * (Nat.log2 n + 1) <= T := by
    calc
      n * (Nat.log2 n + 1) <=
          n ^ 2 * X :=
        Nat.mul_le_mul hn_n2 hKX
      _ = 1 * (n ^ 2 * X) := by
        simp
      _ <= 2 ^ s * (n ^ 2 * X) :=
        Nat.mul_le_mul_right
          (n ^ 2 * X) hs1
      _ = T := by
        dsimp [T]
        ac_rfl


  have hpow :
      2 ^ psi <= 2 ^ s * n :=
    theorem1_two_pow_psi_le_slack
      hn3 hpsiUpper


  have hnPsiPowT :
      n * psi * 2 ^ psi <= T := by
    have hleft :
        n * psi <= n * X :=
      Nat.mul_le_mul_left n hpsiX
    have h :=
      Nat.mul_le_mul hleft hpow
    calc
      n * psi * 2 ^ psi <=
          n * X * (2 ^ s * n) :=
        h
      _ = T := by
        dsimp [T]
        simp only [Nat.pow_two]
        ac_rfl


  have hpsiPow :
      psi <= 2 ^ psi := by
    have hlt :
        psi < 2 ^ psi :=
      Nat.lt_two_pow_self
    omega


  have hnPsi2T :
      n * psi ^ 2 <= T := by
    calc
      n * psi ^ 2 =
          (n * psi) * psi := by
        simp only [Nat.pow_two]
        ac_rfl
      _ <= (n * psi) * 2 ^ psi :=
        Nat.mul_le_mul_left
          (n * psi) hpsiPow
      _ = n * psi * 2 ^ psi := by
        rfl
      _ <= T :=
        hnPsiPowT


  have hH15 :
      PPL.Convergence.ReachCPB.lemma16H15 n <=
        12 * T := by
    unfold
      PPL.Convergence.ReachCPB.lemma16H15
      PPL.Convergence.ReachCPB.lemma16K
    calc
      2 * n *
            (2 * n +
              4 * (Nat.log2 n + 1)) =
          4 * n ^ 2 +
            8 * (n * (Nat.log2 n + 1)) := by
        grind
      _ <= 4 * T + 8 * T :=
        Nat.add_le_add
          (Nat.mul_le_mul_left 4 hn2T)
          (Nat.mul_le_mul_left 8 hnKT)
      _ = 12 * T := by
        omega


  have hH6 :
      PPL.Convergence.ReachCPB.lemma16H6
          n psi (theorem1Kappa psi) <=
        16 * theorem1C1 * T := by
    unfold
      PPL.Convergence.ReachCPB.lemma16H6
      theorem1Kappa
    calc
      16 * n * (theorem1C1 * psi) *
            2 ^ psi =
          16 * theorem1C1 *
            (n * psi * 2 ^ psi) := by
        ac_rfl
      _ <= 16 * theorem1C1 * T :=
        Nat.mul_le_mul_left
          (16 * theorem1C1) hnPsiPowT


  have hHDist :
      PPL.Convergence.ReachCPB.lemma16HDist n <=
        10 * T := by
    unfold
      PPL.Convergence.ReachCPB.lemma16HDist
      PPL.Convergence.ReachCPB.lemma16K
    calc
      2 * n *
            (1 + 4 * (Nat.log2 n + 1)) =
          2 * n +
            8 * (n * (Nat.log2 n + 1)) := by
        grind
      _ <= 2 * T + 8 * T :=
        Nat.add_le_add
          (Nat.mul_le_mul_left 2 hnT)
          (Nat.mul_le_mul_left 8 hnKT)
      _ = 10 * T := by
        omega


  have hHLast :
      PPL.Convergence.ReachCPB.lemma16HLast n <=
        10 * T := by
    unfold
      PPL.Convergence.ReachCPB.lemma16HLast
      PPL.Convergence.ReachCPB.lemma16K
    calc
      2 * n *
            (n + 4 * (Nat.log2 n + 1)) =
          2 * n ^ 2 +
            8 * (n * (Nat.log2 n + 1)) := by
        grind
      _ <= 2 * T + 8 * T :=
        Nat.add_le_add
          (Nat.mul_le_mul_left 2 hn2T)
          (Nat.mul_le_mul_left 8 hnKT)
      _ = 10 * T := by
        omega


  have hL4 :
      PPL.Convergence.ReachCPB.lemma16L4 psi <=
        8 * psi ^ 2 := by
    unfold PPL.Convergence.ReachCPB.lemma16L4
    calc
      8 * psi * psi - 4 * psi <=
          8 * psi * psi :=
        Nat.sub_le _ _
      _ = 8 * psi ^ 2 := by
        simp only [Nat.pow_two]
        ac_rfl


  have hnL4 :
      n *
          PPL.Convergence.ReachCPB.lemma16L4 psi <=
        8 * T := by
    calc
      n *
            PPL.Convergence.ReachCPB.lemma16L4 psi <=
          n * (8 * psi ^ 2) :=
        Nat.mul_le_mul_left n hL4
      _ = 8 * (n * psi ^ 2) := by
        ac_rfl
      _ <= 8 * T :=
        Nat.mul_le_mul_left 8 hnPsi2T


  have hHToken :
      PPL.Convergence.ReachCPB.lemma16HToken
          n psi <=
        24 * T := by
    unfold
      PPL.Convergence.ReachCPB.lemma16HToken
      PPL.Convergence.ReachCPB.lemma16K
    calc
      2 * n *
            (PPL.Convergence.ReachCPB.lemma16L4 psi +
              4 * (Nat.log2 n + 1)) =
          2 *
              (n *
                PPL.Convergence.ReachCPB.lemma16L4 psi) +
            8 * (n * (Nat.log2 n + 1)) := by
        grind
      _ <= 2 * (8 * T) + 8 * T :=
        Nat.add_le_add
          (Nat.mul_le_mul_left 2 hnL4)
          (Nat.mul_le_mul_left 8 hnKT)
      _ = 24 * T := by
        omega


  have hH16 :
      theorem1H16 n psi <=
        (16 * theorem1C1 + 56) * T := by
    unfold
      theorem1H16
      PPL.Convergence.ReachCPB.lemma16Horizon
    calc
      PPL.Convergence.ReachCPB.lemma16H15 n +
            PPL.Convergence.ReachCPB.lemma16H6
              n psi (theorem1Kappa psi) +
            PPL.Convergence.ReachCPB.lemma16HDist n +
            PPL.Convergence.ReachCPB.lemma16HLast n +
            PPL.Convergence.ReachCPB.lemma16HToken n psi <=
          12 * T +
            16 * theorem1C1 * T +
            10 * T +
            10 * T +
            24 * T := by
        exact
          Nat.add_le_add
            (Nat.add_le_add
              (Nat.add_le_add
                (Nat.add_le_add hH15 hH6)
                hHDist)
              hHLast)
            hHToken
      _ = (16 * theorem1C1 + 56) * T := by
        unfold theorem1C1 theorem1C17
        omega


  have hH5Arm :
      PPL.Modes.Lemma5.lemma5ArmHorizon n <=
        10 * T := by
    unfold
      PPL.Modes.Lemma5.lemma5ArmHorizon
      PPL.Modes.Lemma5.K
    calc
      2 * n *
            (1 + 4 * (Nat.log2 n + 1)) =
          2 * n +
            8 * (n * (Nat.log2 n + 1)) := by
        grind
      _ <= 2 * T + 8 * T :=
        Nat.add_le_add
          (Nat.mul_le_mul_left 2 hnT)
          (Nat.mul_le_mul_left 8 hnKT)
      _ = 10 * T := by
        omega


  have hH5Sweep :
      PPL.Modes.Lemma5.lemma5SweepHorizon n <=
        8 * T := by
    unfold PPL.Modes.Lemma5.lemma5SweepHorizon
    calc
      8 * n * n =
          8 * n ^ 2 := by
        simp only [Nat.pow_two]
        ac_rfl
      _ <= 8 * T :=
        Nat.mul_le_mul_left 8 hn2T


  have hH5i :
      theorem1H5i n <= 18 * T := by
    unfold
      theorem1H5i
      PPL.Modes.Lemma5.lemma5iHorizon
    calc
      PPL.Modes.Lemma5.lemma5ArmHorizon n +
            PPL.Modes.Lemma5.lemma5SweepHorizon n <=
          10 * T + 8 * T :=
        Nat.add_le_add hH5Arm hH5Sweep
      _ = 18 * T := by
        omega


  have hH5ii :
      theorem1H5ii n psi <=
        (4 * theorem1C17 + 24) * T := by
    unfold theorem1H5ii
    rw [theorem1_lemma5iiHorizon_eq]
    exact
      Nat.mul_le_mul_left
        (4 * theorem1C17 + 24)
        hnPsiPowT


  have hA :
      16 * theorem1C1 +
          (4 * theorem1C17 + 24) + 74 <=
        theorem1HorizonA := by
    unfold
      theorem1HorizonA theorem1C1 theorem1C17
    decide


  rw [theorem1Horizon_eq_phase_sum]


  calc
    theorem1H16 n psi +
          theorem1H5i n +
          theorem1H5ii n psi <=
        (16 * theorem1C1 + 56) * T +
          18 * T +
          (4 * theorem1C17 + 24) * T :=
      Nat.add_le_add
        (Nat.add_le_add hH16 hH5i)
        hH5ii
    _ =
        (16 * theorem1C1 +
            (4 * theorem1C17 + 24) + 74) *
          T := by
      unfold theorem1C1 theorem1C17
      omega
    _ <= theorem1HorizonA * T :=
      Nat.mul_le_mul_right T hA
    _ =
        theorem1HorizonA *
          2 ^ s * n ^ 2 *
          (Nat.log2 n + s + 1) := by
      dsimp [T, X]
      ac_rfl


end PPL


#print axioms PPL.theorem1_stateEnumeration_nodup
#print axioms PPL.theorem1_stateCount_exact
#print axioms PPL.theorem1_stateCount_le
#print axioms PPL.theorem1Horizon_le
