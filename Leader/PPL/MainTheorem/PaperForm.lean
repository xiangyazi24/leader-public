import Leader.PPL.MainTheorem.PsiWindowSlack
import Leader.PPL.MainTheorem.PaperBounds

/-!
# P_PL Theorem 1 in paper form (F.1a + F.2 + F.3)

Yokota–Sudo–Ooshita–Masuzawa (PODC 2023), Theorem 1: for
`log n ≤ psi ≤ log n + O(1)`, P_PL solves self-stabilizing leader election
on directed rings with (i) expected convergence time `O(n² log n)` and
(ii) `polylog(n)` states per agent.

`Theorem1PaperForm s` is `Theorem1StatementSlack s` (window
`psi ≤ log2 n + s`, plus `psi < n`; see `Theorem1Slack.lean`) with two more
conjuncts in every `(n, psi)` block:

* **state count (F.2)**: the local state type
  `(protocol psi (theorem1Kappa psi)).Q` is in bijection with `Fin N` for some
  `N ≤ 10^21 · (log2 n + s + 1)^6`; so `N` is the exact number of local states
  and it is polylogarithmic in `n` for fixed `s`;
* **horizon (F.3)**: the whp horizon `H = theorem1Horizon n psi` satisfies
  `H ≤ 10^9 · 2^s · n² · (log2 n + s + 1)`, so the whp failure bound and the
  truncated-cost bound `cExpected · H` are `O(n² log n)` for fixed `s`.

The constants `10^21` and `10^9` are the values of `theorem1StateD` and
`theorem1HorizonA` (`Theorem1PaperBounds.lean`).  `cExpected` is the one of
`Theorem1StatementSlack s`, which does not depend on `s`.

The case `psi ≥ n` (single segment) is F.1b; see ERRATA S3.14 and
`Leader/PPL/PsiAtLeastN/`.
-/

namespace PPL

set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false

/-- Paper-form Theorem 1 with additive window slack `s`: the safety, whp and
expected-cost clauses of `Theorem1StatementSlack s`, plus the exact local
state count bounded by `10^21 · (log2 n + s + 1)^6` and the horizon bounded by
`10^9 · 2^s · n² · (log2 n + s + 1)`. -/
def Theorem1PaperForm (s : Nat) : Prop :=
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
                    (forall T : Nat,
                      theorem1CostNumerator ring C0 T <=
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
                        (Nat.log2 n + s + 1))))))))

/-- The state-count constant is `10^21`. -/
theorem theorem1StateD_eq : theorem1StateD = 10 ^ 21 := by
  unfold theorem1StateD
  rfl

/-- The horizon constant is `10^9`. -/
theorem theorem1HorizonA_eq : theorem1HorizonA = 10 ^ 9 := by
  unfold theorem1HorizonA
  rfl

/-- **Paper-form Theorem 1, proved for every slack `s`.**  The first three
clauses come from `theorem1StatementSlack_proved s`; the state count from
`theorem1_stateCount_exact` and `theorem1_stateCount_le`; the horizon from
`theorem1Horizon_le`. -/
theorem theorem1PaperForm_proved (s : Nat) : Theorem1PaperForm s := by
  obtain ⟨c, hc, h1, h2, hbody⟩ := theorem1StatementSlack_proved s
  refine ⟨c, hc, h1, h2, ?_⟩
  intro n psi hn3 hpsi hnpow hwin hlt ring C0
  obtain ⟨hsafe, hwhp, hcost⟩ := hbody hn3 hpsi hnpow hwin hlt ring C0
  refine ⟨hsafe, hwhp, hcost, ?_, ?_⟩
  · refine
      ⟨(PPLv2.states psi (theorem1Kappa psi)).values.length, ?_,
        theorem1_stateCount_exact psi⟩
    have h := theorem1_stateCount_le s n psi hn3 hpsi hwin
    rw [theorem1StateD_eq] at h
    exact h
  · have h := theorem1Horizon_le s n psi hn3 hpsi hnpow hwin
    rw [theorem1HorizonA_eq] at h
    exact h

end PPL

#print axioms PPL.theorem1StateD_eq
#print axioms PPL.theorem1HorizonA_eq
#print axioms PPL.theorem1PaperForm_proved
