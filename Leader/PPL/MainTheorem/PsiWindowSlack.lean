import Leader.PPL.PsiBelowN.UpToTwelve

/-!
# P_PL Theorem 1 with additive slack in the psi window (F.1a)

The paper (Yokota–Sudo–Ooshita–Masuzawa, PODC 2023, Theorem 1) allows
`log n ≤ psi ≤ log n + O(1)`.  The proved headline `Theorem1Statement`
fixes the slack to one: `psi ≤ theorem1K n = log2 n + 1`.

This file proves the statement on the larger domain `psi < n` with no upper
logarithmic window at all (`Theorem1StatementPsiLtN`), and derives from it:

* `Theorem1StatementSlack s`, for every fixed `s`: the headline with
  `psi ≤ Nat.log2 n + s` and the extra hypothesis `psi < n`;
* `Theorem1Statement` itself (the case `s = 1`, where `psi < n` follows from
  `psi ≤ log2 n + 1` and `3 ≤ n`).

The constant `cExpected` does not depend on `s` (nor on `psi`): the cost
proof uses the whp contract for `n ≥ 65` and a finite maximum over the pairs
`3 ≤ n ≤ 64`, `psi < n` below that.  The whp constant stays 64.  The slack
enters only through the horizon `theorem1Horizon n psi`, which grows with
`2 ^ psi ≤ 2 ^ s · n` (F.3, `theorem1Horizon_le`).

Why `psi < n` is needed: for `psi ≥ n` there is a single segment, and a
closed class of non-`S_PL` configurations (CDL plus a valid risky token)
exists; `S_PL` is then not reachable from it (ERRATA S3.14,
`run/verification/ppl-psi-ge-n/`).  For fixed `s` the extra hypothesis
excludes only finitely many `n`.

Proof: `PPL.PsiBelowN.*` (copies of the Theorem-1 chain with the window
replaced by `psi < n`; see `Leader/PPL/PsiBelowN/Rows.lean` for which uses
of the window were real).
-/

namespace PPL

set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false

/-- Theorem 1 on the domain `psi < n`, with no upper logarithmic window:
`Theorem1Statement` with `psi ≤ theorem1K n` replaced by `psi < n`. -/
def Theorem1StatementPsiLtN : Prop :=
  Exists fun cExpected : Nat =>
    And (0 < cExpected)
      (And (32 * theorem1C17 + 352 <= theorem1C1)
        (And (theorem1C1 % 16 = 0)
          (forall {n psi : Nat},
            3 <= n ->
            2 <= psi ->
            n <= 2 ^ psi ->
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
                  (forall T : Nat,
                    theorem1CostNumerator ring C0 T <=
                      n ^ T * (cExpected * H))))))

/-- Theorem 1 with additive slack `s` in the psi window:
`Theorem1Statement` with `psi ≤ theorem1K n` replaced by
`psi ≤ Nat.log2 n + s` and the hypothesis `psi < n` added. -/
def Theorem1StatementSlack (s : Nat) : Prop :=
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
                  (forall T : Nat,
                    theorem1CostNumerator ring C0 T <=
                      n ^ T * (cExpected * H))))))

/-- Theorem 1 on `psi < n`, proved.  Same assembly as
`theorem1Statement_of_inputs`, with every input taken from `PPL.PsiBelowN`. -/
theorem theorem1StatementPsiLtN_proved : Theorem1StatementPsiLtN := by
  have hlocal : PPL.Safety.SPL.SPLLocalStepProp :=
    @PPL.Safety.SPL.splLocalStepProp_proved
  have hwhp : PsiBelowN.Theorem1WhpUniform :=
    PsiBelowN.theorem1WhpUniform_proved
  obtain ⟨c, hc, hcost⟩ :=
    PsiBelowN.theorem1Cost_of_whp_and_smallN hlocal hwhp
      (PsiBelowN.theorem1SmallNCost_of_tiny hlocal hwhp
        (PsiBelowN.theorem1TinyNCost_of_producer hlocal
          PsiBelowN.theorem1TinyProducer_proved))
  refine ⟨c, hc, ?_, ?_, ?_⟩
  · unfold theorem1C1
    omega
  · unfold theorem1C1
    exact Nat.mul_mod_right 16 _
  · intro n psi hn3 hpsi hnpow hlt ring C0
    exact
      ⟨fun C hC => theorem1SPL_isSafe_proved hn3 hpsi ring C hC,
        hwhp hn3 hpsi hnpow hlt ring C0,
        fun T => hcost hn3 hpsi hnpow hlt ring C0 T⟩

/-- The slack-`s` statement follows from the `psi < n` statement (the window
premise is not used). -/
theorem theorem1StatementSlack_of_psiLtN
    (h : Theorem1StatementPsiLtN) (s : Nat) :
    Theorem1StatementSlack s := by
  obtain ⟨c, hc, h1, h2, hbody⟩ := h
  exact ⟨c, hc, h1, h2,
    fun hn3 hpsi hnpow _hwindow hlt ring C0 =>
      hbody hn3 hpsi hnpow hlt ring C0⟩

/-- **Theorem 1 with slack `s`, proved for every `s`.** -/
theorem theorem1StatementSlack_proved (s : Nat) :
    Theorem1StatementSlack s :=
  theorem1StatementSlack_of_psiLtN theorem1StatementPsiLtN_proved s

/-- The case `s = 1` contains the proved headline: on its domain
(`3 ≤ n`, `psi ≤ log2 n + 1`) the extra hypothesis `psi < n` holds
(`theorem1_psi_lt_n`). -/
theorem theorem1Statement_of_slack_one
    (h : Theorem1StatementSlack 1) :
    Theorem1Statement := by
  obtain ⟨c, hc, h1, h2, hbody⟩ := h
  exact ⟨c, hc, h1, h2,
    fun hn3 hpsi hnpow hpsiK ring C0 =>
      hbody hn3 hpsi hnpow hpsiK
        (theorem1_psi_lt_n hn3 hpsiK) ring C0⟩

/-- `Theorem1Statement` re-derived through the slack statement. -/
theorem theorem1Statement_proved_via_slack : Theorem1Statement :=
  theorem1Statement_of_slack_one (theorem1StatementSlack_proved 1)

end PPL

#print axioms PPL.theorem1StatementPsiLtN_proved
#print axioms PPL.theorem1StatementSlack_proved
#print axioms PPL.theorem1Statement_of_slack_one
#print axioms PPL.theorem1Statement_proved_via_slack
