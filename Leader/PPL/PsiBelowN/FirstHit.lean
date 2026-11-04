import Leader.PPL.PsiBelowN.PaddedRows
import Leader.PPL.SPLEntry.ForcingWordClosed

/-!
# P_PL Theorem 1 on `psi < n`: the L18 first-hit bound

Copy of `Theorem1L18FirstHitFromForcing.lean` on the domain `psi < n`.  The
original derived `psi < n` from the log window through
`theorem1_psi_lt_n`; this is the one place in the Theorem-1 chain where the
window carries content (the scoped Lemma-18 forcing word needs `psi < n`;
for `psi ≥ n` there is a single segment and a valid risky token never moves,
ERRATA S3.14).  Here the hypothesis is `psi < n` itself.

P_PL Theorem 1 cleanup, phase 2, step 6c: the counting argument is
`PPL.Theorem1General.theorem1L18FirstHitPhaseBound_at`
(`Leader/PPL/MainTheorem/GeneralFirstHit.lean`) with the rooted predicate
`S_PL` and the scoped failure count; the statements here are unchanged and
the private `q184*` helper copies are gone.
-/

namespace PPL.PsiBelowN

set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false

/-- Board 18.4.  The H5(ii)-window L18 first-hit bound, conditional only on the
scoped Lemma-18 forcing bridge
(`PPL.Theorem1General.theorem1L18FirstHitPhaseBound_at` for rooted `S_PL`,
with the per-root failure count `n_mul_l18FailureCount_le_pow_scoped`, the
one consumer of `psi < n`). -/
theorem theorem1L18FirstHitPhaseBound_of_forcing
    (hforce :
      PPL.Convergence.L18.L18ForcingWordReachesSPLScoped) :
    Theorem1L18FirstHitPhaseBound := by
  intro n psi hn3 hpsi hnpow hpsiK ring C0 p hstop _hroom
  have hlt : psi < n :=
    theorem1_psi_lt_n hn3 hpsiK
  have hphaseEq :
      theorem1L18FirstHitPhaseBad ring C0 p =
        PPL.Theorem1General.theorem1L18FirstHitPhaseBadGen ring
          (fun root C => decide (SPLAt ring root C)) C0 p :=
    funext (PPL.Theorem1General.theorem1L18FirstHitPhaseBad_eq ring C0 p)
  rw [hphaseEq]
  refine
    PPL.Theorem1General.theorem1L18FirstHitPhaseBound_at
      ring _ ?_ hn3 hpsi hnpow C0 p hstop
  intro root C hCPB hUnique
  have hbound :=
    PPL.Convergence.L18.n_mul_l18FailureCount_le_pow_scoped
      hforce lemma4_deterministic_core_proved
      hn3 hpsi hlt ring root C hCPB hUnique
  unfold PPL.Convergence.L18.l18FailureCount at hbound
  simp only [PPL.Theorem1General.l18HitsSPL_eq] at hbound
  exact hbound

/-- The L18 first-hit bound on `psi < n`, unconditionally. -/
theorem theorem1L18FirstHitPhaseBound_proved :
    Theorem1L18FirstHitPhaseBound :=
  theorem1L18FirstHitPhaseBound_of_forcing
    PPL.l18ForcingWordReachesSPLScoped_proved

/-- The padded L18 bound on `psi < n`, unconditionally. -/
theorem theorem1L18DynamicPaddedBound_proved :
    Theorem1L18DynamicPaddedBound :=
  theorem1L18DynamicPaddedBound_of_l18FirstHitPhaseBound
    theorem1L18FirstHitPhaseBound_proved

end PPL.PsiBelowN

#print axioms PPL.PsiBelowN.theorem1L18FirstHitPhaseBound_proved
#print axioms PPL.PsiBelowN.theorem1L18DynamicPaddedBound_proved
