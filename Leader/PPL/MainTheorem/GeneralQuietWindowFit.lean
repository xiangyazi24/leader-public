import Leader.PPL.MainTheorem.Statement

/-!
# P_PL Theorem 1, general step lemmas: the quiet-window fit on every domain

The quiet-window fit `H17 + H18 ≤ H5(ii)` at the clock `theorem1Kappa psi`
needs only `3 ≤ n`, `2 ≤ psi` and `n ≤ 2 ^ psi`.  The `psi < n`
(`PPL.PsiBelowN`) and `n ≤ psi` (`PPL.PsiAtLeastN`) chains each carried a
copy with their domain premise threaded and unused; both copies are now
one-line special cases of the lemmas here.

P_PL Theorem 1 cleanup, phase 2, step 6a.
-/

namespace PPL.Theorem1General

set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false

/-- The quiet-window fit: the L17 and L18 horizons fit inside the Lemma-5(ii)
window at `theorem1Kappa`, for every `n ≥ 3`, `psi ≥ 2` with `n ≤ 2 ^ psi`. -/
theorem theorem1_quietWindow_covers_run
    {n psi : Nat}
    (hn3 : 3 ≤ n)
    (hpsi : 2 ≤ psi)
    (hnpow : n ≤ 2 ^ psi) :
    PPL.Convergence.L17.H17 theorem1C17 n +
        PPL.Convergence.L18.l18Horizon n psi ≤
      PPL.Modes.Lemma5.lemma5iiHorizon
        n psi (theorem1Kappa psi) := by
  have h17 := theorem1_H17_le hn3 hpsi hnpow
  have h18 := theorem1_H18_le hn3 hpsi hnpow
  rw [theorem1_lemma5iiHorizon_eq]
  calc
    PPL.Convergence.L17.H17 theorem1C17 n +
          PPL.Convergence.L18.l18Horizon n psi ≤
        4 * theorem1C17 * (n * psi * 2 ^ psi) +
          24 * (n * psi * 2 ^ psi) :=
      Nat.add_le_add h17 h18
    _ = (4 * theorem1C17 + 24) * (n * psi * 2 ^ psi) := by
      rw [Nat.add_mul]

/-- The quiet-window fit in the named horizons of the Theorem 1 chain. -/
theorem theorem1H17_add_H18_le_H5ii
    {n psi : Nat}
    (hn3 : 3 <= n)
    (hpsi : 2 <= psi)
    (hnpow : n <= 2 ^ psi) :
    theorem1H17 n + theorem1H18 n psi <=
      theorem1H5ii n psi := by
  simpa [theorem1H17, theorem1H18, theorem1H5ii]
    using theorem1_quietWindow_covers_run hn3 hpsi hnpow

end PPL.Theorem1General

#print axioms PPL.Theorem1General.theorem1_quietWindow_covers_run
#print axioms PPL.Theorem1General.theorem1H17_add_H18_le_H5ii
