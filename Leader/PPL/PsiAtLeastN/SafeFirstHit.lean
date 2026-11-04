import Leader.PPL.PsiAtLeastN.SafePaddedRows

/-!
# P_PL Theorem 1 on `n ≤ psi`: the safe L18 first-hit bound

The L18 first-hit bound of `Leader/PPL/PsiBelowN/FirstHit.lean` with the
rooted safe predicate in place of rooted `S_PL`.  The one consumer of
`psi < n` there, the scoped forcing count
`n_mul_l18FailureCount_le_pow_scoped`, is replaced by
`n_mul_l18SafeFailureCount_le_pow` (`L18SafeForcing.lean`), which holds for
every `psi`: the first three Lemma-18 phases already end in rooted `S_PL` or
rooted `C_DL`.

P_PL Theorem 1 cleanup, phase 2, step 6c: the counting argument is
`PPL.Theorem1General.theorem1L18FirstHitPhaseBound_at`; the statements here
are unchanged and the private `q184*` helper copies are gone.
-/

namespace PPL.PsiAtLeastN

set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false

/-- The H5(ii)-window safe L18 first-hit bound on `n ≤ psi`
(`PPL.Theorem1General.theorem1L18FirstHitPhaseBound_at` for `L18SafeAt`,
with the per-root failure count `n_mul_l18SafeFailureCount_le_pow`, which
holds for every `psi`). -/
theorem theorem1L18SafeFirstHitPhaseBound_proved :
    Theorem1L18SafeFirstHitPhaseBound := by
  intro n psi hn3 hpsi hnpow _hge ring C0 p hstop _hroom
  rw [show theorem1L18SafeFirstHitPhaseBad ring C0 p =
      PPL.Theorem1General.theorem1L18FirstHitPhaseBadGen ring
        (fun root C => decide (L18SafeAt ring root C)) C0 p from
    funext (theorem1L18SafeFirstHitPhaseBad_eq ring C0 p)]
  refine
    PPL.Theorem1General.theorem1L18FirstHitPhaseBound_at
      ring _ ?_ hn3 hpsi hnpow C0 p hstop
  intro root C hCPB hUnique
  have hbound :=
    n_mul_l18SafeFailureCount_le_pow hn3 hpsi ring root C hCPB hUnique
  unfold l18SafeFailureCount at hbound
  simp only [l18HitsSafe_eq] at hbound
  exact hbound

/-- The padded safe L18 bound on `n ≤ psi`, unconditionally. -/
theorem theorem1L18SafeDynamicPaddedBound_proved :
    Theorem1L18SafeDynamicPaddedBound :=
  theorem1L18SafeDynamicPaddedBound_of_phaseBound
    theorem1L18SafeFirstHitPhaseBound_proved

end PPL.PsiAtLeastN

#print axioms PPL.PsiAtLeastN.theorem1L18SafeFirstHitPhaseBound_proved
#print axioms PPL.PsiAtLeastN.theorem1L18SafeDynamicPaddedBound_proved
