import Leader.PPL.MainTheorem.MissAmplification
import Leader.PPL.MainTheorem.SPLClosureCost
import Leader.PPL.LogWindow.Cost

/-!
# Superseded (log-window route): dead declarations of `Leader/PPL/MainTheorem/MissAmplification.lean`

Moved out of `Leader/PPL/MainTheorem/MissAmplification.lean` by the P_PL Theorem 1 cleanup, phase 2.
These declarations served only the original psi <= log2 n + 1 route to
`PPL.theorem1Statement_proved`, which now goes through
`PPL.theorem1Statement_proved_via_slack` (`Leader/PPL/MainTheorem/PsiWindowSlack.lean`).
Nothing in the live Theorem 1 closure uses them; they are kept, and still build,
as the record of that route.  Every name `PPL.X` became `PPL.Superseded.LogWindow.X`;
see `research-map/RENAME_MAP_PPL.md` (phase 2).
-/

section
set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false
open K2ArbitraryElimination.FiniteAccounting
open LeaderCountDyadicTail
namespace PPL.Superseded.LogWindow

/--
For n >= 65, 65 copies of the uniform 64/n block are a half-failure
block.  The exponent 65 is chosen so the repository's integer_half_life
closes the arithmetic without reducing huge powers.
-/
theorem Theorem1UniformHalfFailureMid
    (hlocal : PPL.Safety.SPL.SPLLocalStepProp)
    (hwhp : Theorem1WhpUniform)
    {n psi : Nat}
    (hn65 : 65 ≤ n)
    (hpsi : 2 ≤ psi)
    (hnpow : n ≤ 2 ^ psi)
    (hpsiK : psi ≤ theorem1K n)
    (ring : DirectedRing n)
    (C : Config n psi (theorem1Kappa psi)) :
    2 *
        wordSum
          (fun D e =>
            PopulationProtocol.step
              (protocol psi (theorem1Kappa psi))
              ring D e)
          (miss (SPL ring))
          C
          (65 * theorem1Horizon n psi) ≤
      n ^ (65 * theorem1Horizon n psi) := by
  have hn3 : 3 ≤ n := by
    omega


  have hclosed :=
    theorem1SPL_closed_of_local
      hlocal hn3 hpsi ring


  have hbase :
      ∀ D : Config n psi (theorem1Kappa psi),
        n *
            wordSum
              (fun E e =>
                PopulationProtocol.step
                  (protocol psi (theorem1Kappa psi))
                  ring E e)
              (miss (SPL ring))
              D
              (theorem1Horizon n psi) ≤
          64 * n ^ theorem1Horizon n psi := by
    intro D
    have h64 :=
      hwhp
        (n := n)
        (psi := psi)
        hn3 hpsi hnpow hpsiK
        ring D
    dsimp only at h64
    rw [
      theorem1FailureNumerator_eq_wordSum_miss
        ring hclosed D
        (theorem1Horizon n psi)
    ] at h64
    exact h64


  have hamp :=
    amplify_miss_with_loss
      (fun D e =>
        PopulationProtocol.step
          (protocol psi (theorem1Kappa psi))
          ring D e)
      (SPL ring)
      hclosed
      (theorem1Horizon n psi)
      n
      64
      hbase
      65
      C


  have h65 :
      2 * 64 ^ 65 ≤ 65 ^ 65 := by
    have h :=
      LeaderCountDyadicTail.integer_half_life
        65 (by omega)
    have hpred : 65 - 1 = 64 := by
      omega
    rw [hpred] at h
    exact h


  have hnPow :
      65 ^ 65 ≤ n ^ 65 :=
    Nat.pow_le_pow_left hn65 65


  have hratio :
      2 * 64 ^ 65 ≤ n ^ 65 :=
    Nat.le_trans h65 hnPow


  have hscaled :
      n ^ 65 *
          (2 *
            wordSum
              (fun D e =>
                PopulationProtocol.step
                  (protocol psi (theorem1Kappa psi))
                  ring D e)
              (miss (SPL ring))
              C
              (65 * theorem1Horizon n psi)) ≤
        n ^ 65 *
          n ^ (65 * theorem1Horizon n psi) := by
    calc
      n ^ 65 *
            (2 *
              wordSum
                (fun D e =>
                  PopulationProtocol.step
                    (protocol psi (theorem1Kappa psi))
                    ring D e)
                (miss (SPL ring))
                C
                (65 * theorem1Horizon n psi)) =
          2 *
            (n ^ 65 *
              wordSum
                (fun D e =>
                  PopulationProtocol.step
                    (protocol psi (theorem1Kappa psi))
                    ring D e)
                (miss (SPL ring))
                C
                (65 * theorem1Horizon n psi)) := by
        ac_rfl
      _ ≤
          2 *
            (64 ^ 65 *
              n ^ (65 * theorem1Horizon n psi)) :=
        Nat.mul_le_mul_left 2 hamp
      _ =
          (2 * 64 ^ 65) *
            n ^ (65 * theorem1Horizon n psi) := by
        ac_rfl
      _ ≤
          n ^ 65 *
            n ^ (65 * theorem1Horizon n psi) :=
        Nat.mul_le_mul_right
          (n ^ (65 * theorem1Horizon n psi))
          hratio


  exact
    Nat.le_of_mul_le_mul_left
      hscaled
      (Nat.pow_pos (by omega))

/--
Mid-range expected-cost consequence.  One amplified block has length
65 * H and half-failure, so cost_le_two_blocks gives coefficient 130.
-/
theorem theorem1_cost_mid
    (hlocal : PPL.Safety.SPL.SPLLocalStepProp)
    (hwhp : Theorem1WhpUniform)
    {n psi : Nat}
    (hn65 : 65 ≤ n)
    (hpsi : 2 ≤ psi)
    (hnpow : n ≤ 2 ^ psi)
    (hpsiK : psi ≤ theorem1K n)
    (ring : DirectedRing n)
    (C0 : Config n psi (theorem1Kappa psi)) :
    ∀ T : Nat,
      theorem1CostNumerator ring C0 T ≤
        n ^ T *
          (130 * theorem1Horizon n psi) := by
  have hn3 : 3 ≤ n := by
    omega


  have hclosed :=
    theorem1SPL_closed_of_local
      hlocal hn3 hpsi ring


  have hnpos : 0 < n := by
    omega


  have h15 :
      0 <
        PPL.Convergence.ReachCPB.lemma16H15 n := by
    unfold PPL.Convergence.ReachCPB.lemma16H15
    exact
      Nat.mul_pos
        (Nat.mul_pos (by omega) hnpos)
        (by omega)


  have h16 :
      0 <
        PPL.Convergence.ReachCPB.lemma16Horizon
          n psi (theorem1Kappa psi) := by
    unfold PPL.Convergence.ReachCPB.lemma16Horizon
    omega


  have hH :
      0 < theorem1Horizon n psi := by
    unfold theorem1Horizon
    omega


  have hB :
      0 <
        65 * theorem1Horizon n psi := by
    exact Nat.mul_pos (by omega) hH


  have hblock :
      ∀ D : Config n psi (theorem1Kappa psi),
        2 *
            wordSum
              (fun E e =>
                PopulationProtocol.step
                  (protocol psi (theorem1Kappa psi))
                  ring E e)
              (miss (SPL ring))
              D
              (65 * theorem1Horizon n psi) ≤
          n ^ (65 * theorem1Horizon n psi) := by
    intro D
    exact
      Theorem1UniformHalfFailureMid
        hlocal hwhp
        hn65 hpsi hnpow hpsiK
        ring D


  have hcost :=
    cost_le_two_blocks
      (fun D e =>
        PopulationProtocol.step
          (protocol psi (theorem1Kappa psi))
          ring D e)
      (SPL ring)
      hclosed
      (65 * theorem1Horizon n psi)
      hB
      hblock


  intro T


  have hraw :
      theorem1CostNumerator ring C0 T ≤
        n ^ T *
          (2 *
            (65 * theorem1Horizon n psi)) := by
    simpa [theorem1CostNumerator]
      using hcost T C0


  have hcoef :
      2 *
          (65 * theorem1Horizon n psi) =
        130 * theorem1Horizon n psi := by
    omega


  rw [hcoef] at hraw
  exact hraw

/--
The only genuinely new finite-size producer left after mid-range
amplification: n <= 64.
-/
def Theorem1TinyNCost : Prop :=
  exists cTiny : Nat,
    2 ≤ cTiny ∧
    forall {n psi : Nat},
      3 ≤ n ->
      n ≤ 64 ->
      2 ≤ psi ->
      n ≤ 2 ^ psi ->
      psi ≤ theorem1K n ->
      forall
        (ring : DirectedRing n)
        (C0 : Config n psi (theorem1Kappa psi))
        (T : Nat),
        theorem1CostNumerator ring C0 T ≤
          n ^ T *
            (cTiny * theorem1Horizon n psi)

/--
The old small-n leaf follows from a tiny-n producer plus the uniform WHP
body.  The absolute constant cTiny + 130 covers both branches.
-/
theorem theorem1SmallNCost_of_tiny
    (hlocal : PPL.Safety.SPL.SPLLocalStepProp)
    (hwhp : Theorem1WhpUniform)
    (htiny : Theorem1TinyNCost) :
    Theorem1SmallNCost := by
  rcases htiny with
    ⟨cTiny, _hcTiny, htinyBound⟩


  refine
    ⟨cTiny + 130, by omega, ?_⟩


  intro n psi
  intro hn3 _hn128 hpsi hnpow hpsiK
  intro ring C0 T


  by_cases hnTiny : n ≤ 64
  · have htinyCost :=
      htinyBound
        (n := n)
        (psi := psi)
        hn3 hnTiny hpsi hnpow hpsiK
        ring C0 T


    have hcoef :
        cTiny * theorem1Horizon n psi ≤
          (cTiny + 130) *
            theorem1Horizon n psi :=
      Nat.mul_le_mul_right
        (theorem1Horizon n psi)
        (by omega)


    exact
      Nat.le_trans
        htinyCost
        (Nat.mul_le_mul_left
          (n ^ T)
          hcoef)


  · have hn65 : 65 ≤ n := by
      omega


    have hmidCost :=
      theorem1_cost_mid
        hlocal hwhp
        hn65 hpsi hnpow hpsiK
        ring C0 T


    have hcoef :
        130 * theorem1Horizon n psi ≤
          (cTiny + 130) *
            theorem1Horizon n psi :=
      Nat.mul_le_mul_right
        (theorem1Horizon n psi)
        (by omega)


    exact
      Nat.le_trans
        hmidCost
        (Nat.mul_le_mul_left
          (n ^ T)
          hcoef)

end PPL.Superseded.LogWindow
end
