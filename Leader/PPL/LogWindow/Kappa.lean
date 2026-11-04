import Leader.PPL.MainTheorem.Kappa
import Leader.PPL.MainTheorem.Skeleton
import Init.Data.Nat.Log2
import Init.Omega

/-!
# Superseded (log-window route): dead declarations of `Leader/PPL/MainTheorem/Kappa.lean`

Moved out of `Leader/PPL/MainTheorem/Kappa.lean` by the P_PL Theorem 1 cleanup, phase 2.
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
namespace PPL.Superseded.LogWindow

/--
The fixed Lemma-5(ii) quiet window contains the complete Lemma-17 plus
Lemma-18 run throughout the whole Theorem-1 parameter window.

The upper-window premise is retained in the statement for the exact Theorem-1
interface, although the length domination itself only needs n <= 2^psi.
-/
theorem theorem1_quietWindow_covers_run
    {n psi : Nat}
    (hn3 : 3 ≤ n)
    (hpsi : 2 ≤ psi)
    (hnpow : n ≤ 2 ^ psi)
    (_hpsiK : psi ≤ theorem1K n) :
    PPL.Convergence.L17.H17 theorem1C17 n +
        PPL.Convergence.L18.l18Horizon n psi ≤
      PPL.Modes.Lemma5.lemma5iiHorizon
        n psi (theorem1Kappa psi) := by
  have h17 :=
    theorem1_H17_le
      hn3 hpsi hnpow
  have h18 :=
    theorem1_H18_le
      hn3 hpsi hnpow
  rw [theorem1_lemma5iiHorizon_eq]
  calc
    PPL.Convergence.L17.H17 theorem1C17 n +
          PPL.Convergence.L18.l18Horizon n psi ≤
        4 * theorem1C17 *
            (n * psi * 2 ^ psi) +
          24 * (n * psi * 2 ^ psi) :=
      Nat.add_le_add h17 h18
    _ =
        (4 * theorem1C17 + 24) *
          (n * psi * 2 ^ psi) := by
      rw [Nat.add_mul]

end PPL.Superseded.LogWindow
end
