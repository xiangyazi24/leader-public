import Leader.PPL.PsiAtLeastN.MainTheorem
import Leader.Wu.Scheduler.UniformFirstHitExpectation

/-!
# P_PL Theorem 1 with the literal expected hitting time

`Theorem1PaperFormSafeTarget s` and `Theorem1PaperForm s` state the
expected-time part of Theorem 1 as the finite-horizon family
`∀ T, costNumerator(T) ≤ n^T · (cExpected · H)`, i.e. `E[min(τ, T)] ≤ B` for
every truncation `T`.  This file restates both theorems with the expectation
itself, `UniformFirstHit.ExpectedHittingTimeAtMost`:

* `P(τ = ∞) = 0` (`AlmostSurelyHits`), and
* `Σ_{k ≤ K} k · P(τ = k) ≤ cExpected · H` for every `K`,

which together say `E[τ] = Σ_k k · P(τ = k) + ∞ · P(τ = ∞) ≤ cExpected · H`
for the first hitting time `τ` of the target under the uniform scheduler
(each step picks one of the `n` ring edges uniformly and independently).

## Why this is the probabilist's `E[τ]`

The scheduler law is the uniform product measure on `(Fin n)^ℕ`.  Every
event used here (`{τ = k}`, `{τ > t}`) depends on finitely many steps, so its
probability is its number of words of that length divided by `n^length`; these
are the counts `firstHitNumerator` and `survivalNumerator` in
`Leader/Wu/Scheduler/UniformFirstHitExpectation.lean`.  For an `ℕ ∪ {∞}`-valued random
variable `E[τ] = Σ_k k P(τ = k) + ∞ · P(τ = ∞)`; a series of nonnegative terms
is at most `B` iff its partial sums are; so the conjunction above is
`E[τ] ≤ B` exactly.  The bridge from the upstream clause is
`UniformFirstHit.expectedHittingTimeAtMost_iff_cost`, proved from word counts:
it contains the tail-sum formula `E[min(τ, T)] = Σ_{t<T} P(τ > t)`,
monotonicity of `E[min(τ, T)]` in `T`, the Abel identity
`E[τ; τ ≤ K] + K · P(τ > K) = E[min(τ, K)]`, and the step from the truncated
bounds to `P(τ = ∞) = 0`; i.e. the monotone-convergence identity
`E[τ] = sup_T E[min(τ, T)]`, stated as an equivalence of the two bounds.

The second new clause is the explicit almost-sure-hitting rate
`T · P(τ > T) ≤ cExpected · H` for every `T`, stated with the repository's
existing failure numerators (`theorem1SafeFailureNumerator`,
`theorem1FailureNumerator`), identified with `survivalNumerator` by
`UniformFirstHit.survivalNumerator_eq_countP`.

All other clauses (target safety, whp bound, state count, horizon bound) are
copied unchanged.
-/

namespace PPL.ExpectedTime

open UniformFirstHit

set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false

/-! ## Failure numerators are survival counts -/

/-- The safe-target failure numerator counts the length-`T` words with
`τ > T`. -/
theorem theorem1SafeFailureNumerator_eq_survival
    {n psi kappa : Nat} (ring : DirectedRing n) (C : Config n psi kappa) (T : Nat) :
    PsiAtLeastN.theorem1SafeFailureNumerator ring C T =
      survivalNumerator
        (fun D e => PopulationProtocol.step (protocol psi kappa) ring D e)
        (PsiAtLeastN.Theorem1SafeTarget ring) C T := by
  unfold PsiAtLeastN.theorem1SafeFailureNumerator
  apply survivalNumerator_eq_countP
  · intro D
    simp [PsiAtLeastN.theorem1ReachesSafeTarget]
  · intro D e es
    simp [PsiAtLeastN.theorem1ReachesSafeTarget]

/-- The `S_PL` failure numerator counts the length-`T` words with `τ > T`. -/
theorem theorem1FailureNumerator_eq_survival
    {n psi kappa : Nat} (ring : DirectedRing n) (C : Config n psi kappa) (T : Nat) :
    theorem1FailureNumerator ring C T =
      survivalNumerator
        (fun D e => PopulationProtocol.step (protocol psi kappa) ring D e)
        (SPL ring) C T := by
  unfold theorem1FailureNumerator
  apply survivalNumerator_eq_countP
  · intro D
    simp [theorem1ReachesSPL]
  · intro D e es
    simp [theorem1ReachesSPL]

/-! ## Whole window, safe target -/

/-- **Paper-form Theorem 1 on the whole window `psi ≤ log2 n + s`, safe
target, literal expected hitting time.**  As `Theorem1PaperFormSafeTarget s`,
with the truncated-cost clause replaced by `E[τ] ≤ cExpected · H`
(`ExpectedHittingTimeAtMost`) and the almost-sure-hitting rate
`T · P(τ > T) ≤ cExpected · H`. -/
def Theorem1PaperFormSafeTargetExpectedTime (s : Nat) : Prop :=
  Exists fun cExpected : Nat =>
    And (0 < cExpected)
      (And (32 * theorem1C17 + 352 <= theorem1C1)
        (And (theorem1C1 % 16 = 0)
          (forall {n psi : Nat},
            3 <= n ->
            2 <= psi ->
            n <= 2 ^ psi ->
            psi <= Nat.log2 n + s ->
            forall
              (ring : DirectedRing n)
              (C0 : Config n psi (theorem1Kappa psi)),
              let H := theorem1Horizon n psi
              And
                (forall C : Config n psi (theorem1Kappa psi),
                  PsiAtLeastN.Theorem1SafeTarget ring C ->
                    PopulationProtocol.IsSafe
                      (protocol psi (theorem1Kappa psi))
                      ring C PPL.Safety.SPL.output)
                (And
                  (n * PsiAtLeastN.theorem1SafeFailureNumerator ring C0 H <=
                    64 * n ^ H)
                  (And
                    (ExpectedHittingTimeAtMost
                      (fun D e =>
                        PopulationProtocol.step
                          (protocol psi (theorem1Kappa psi)) ring D e)
                      (PsiAtLeastN.Theorem1SafeTarget ring) C0
                      ((cExpected * H : Nat) : Rat))
                    (And
                      (forall T : Nat,
                        T * PsiAtLeastN.theorem1SafeFailureNumerator ring C0 T <=
                          n ^ T * (cExpected * H))
                      (And
                        (Exists fun N : Nat =>
                          And
                            (N <= 10 ^ 21 * (Nat.log2 n + s + 1) ^ 6)
                            (Exists fun decode :
                                Fin N -> (protocol psi (theorem1Kappa psi)).Q =>
                              And
                                (Function.Injective decode)
                                (Function.Surjective decode)))
                        (H <= 10 ^ 9 * 2 ^ s * n ^ 2 *
                          (Nat.log2 n + s + 1)))))))))

/-- **Proved for every `s`**, from `theorem1PaperFormSafeTarget_proved` and
`expectedHittingTimeAtMost_iff_cost`. -/
theorem theorem1PaperFormSafeTargetExpectedTime_proved (s : Nat) :
    Theorem1PaperFormSafeTargetExpectedTime s := by
  obtain ⟨c, hc, h1, h2, hbody⟩ := PsiAtLeastN.theorem1PaperFormSafeTarget_proved s
  refine ⟨c, hc, h1, h2, ?_⟩
  intro n psi hn3 hpsi hnpow hwin ring C0
  obtain ⟨hsafe, hwhp, hcost, hcount, hH⟩ := hbody hn3 hpsi hnpow hwin ring C0
  have hn : 0 < n := by omega
  refine ⟨hsafe, hwhp, ?_, ?_, hcount, hH⟩
  · exact (expectedHittingTimeAtMost_iff_cost _ _ hn C0 _).2 hcost
  · intro T
    rw [theorem1SafeFailureNumerator_eq_survival]
    exact Nat.le_trans (survival_mul_le_cost _ _ C0 T) (hcost T)

/-! ## `psi < n`, target `S_PL` -/

/-- **Paper-form Theorem 1 (`psi < n`, target `S_PL`), literal expected
hitting time.**  As `Theorem1PaperForm s`, with the truncated-cost clause
replaced by `E[τ] ≤ cExpected · H` and the almost-sure-hitting rate. -/
def Theorem1PaperFormExpectedTime (s : Nat) : Prop :=
  Exists fun cExpected : Nat =>
    And (0 < cExpected)
      (And (32 * theorem1C17 + 352 <= theorem1C1)
        (And (theorem1C1 % 16 = 0)
          (forall {n psi : Nat},
            3 <= n ->
            2 <= psi ->
            n <= 2 ^ psi ->
            psi <= Nat.log2 n + s ->
            psi < n ->
            forall
              (ring : DirectedRing n)
              (C0 : Config n psi (theorem1Kappa psi)),
              let H := theorem1Horizon n psi
              And
                (forall C : Config n psi (theorem1Kappa psi),
                  SPL ring C ->
                    PopulationProtocol.IsSafe
                      (protocol psi (theorem1Kappa psi))
                      ring C PPL.Safety.SPL.output)
                (And
                  (n * theorem1FailureNumerator ring C0 H <=
                    64 * n ^ H)
                  (And
                    (ExpectedHittingTimeAtMost
                      (fun D e =>
                        PopulationProtocol.step
                          (protocol psi (theorem1Kappa psi)) ring D e)
                      (SPL ring) C0
                      ((cExpected * H : Nat) : Rat))
                    (And
                      (forall T : Nat,
                        T * theorem1FailureNumerator ring C0 T <=
                          n ^ T * (cExpected * H))
                      (And
                        (Exists fun N : Nat =>
                          And
                            (N <= 10 ^ 21 * (Nat.log2 n + s + 1) ^ 6)
                            (Exists fun decode :
                                Fin N -> (protocol psi (theorem1Kappa psi)).Q =>
                              And
                                (Function.Injective decode)
                                (Function.Surjective decode)))
                        (H <= 10 ^ 9 * 2 ^ s * n ^ 2 *
                          (Nat.log2 n + s + 1)))))))))

/-- **Proved for every `s`**, from `theorem1PaperForm_proved`. -/
theorem theorem1PaperFormExpectedTime_proved (s : Nat) :
    Theorem1PaperFormExpectedTime s := by
  obtain ⟨c, hc, h1, h2, hbody⟩ := theorem1PaperForm_proved s
  refine ⟨c, hc, h1, h2, ?_⟩
  intro n psi hn3 hpsi hnpow hwin hlt ring C0
  obtain ⟨hsafe, hwhp, hcost, hcount, hH⟩ := hbody hn3 hpsi hnpow hwin hlt ring C0
  have hn : 0 < n := by omega
  refine ⟨hsafe, hwhp, ?_, ?_, hcount, hH⟩
  · exact (expectedHittingTimeAtMost_iff_cost _ _ hn C0 _).2 hcost
  · intro T
    rw [theorem1FailureNumerator_eq_survival]
    exact Nat.le_trans (survival_mul_le_cost _ _ C0 T) (hcost T)

end PPL.ExpectedTime

#print axioms PPL.ExpectedTime.theorem1SafeFailureNumerator_eq_survival
#print axioms PPL.ExpectedTime.theorem1FailureNumerator_eq_survival
#print axioms PPL.ExpectedTime.theorem1PaperFormSafeTargetExpectedTime_proved
#print axioms PPL.ExpectedTime.theorem1PaperFormExpectedTime_proved
