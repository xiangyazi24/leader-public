import Leader.Wu.Splice.HoldRepairGlobalProgress
import Leader.Wu.Splice.LocalStepMass

set_option autoImplicit false
set_option Elab.async false

/-! # V10j with leaders: 1/64 of the length-6n scheduler words make progress

`progress_massJ`: on every ring with at least three sites and from every `SpliceSafeV7g` configuration, with or
without leaders, there is an edge `e` such that at least `n^(6n) / 64` of the scheduler words of length `6n`
contain a physical V10j service or, at some prefix, lower the controller weight of the pair served by `e`.  This
is the with-leader counterpart of `B9SpliceMatcherMass.progress_mass`, obtained from
`B9SpliceV10jGlobalProgress.globalProgressWithin3J` through the step-generic chain `B9SpliceLocalStepMass`. -/

namespace B9SpliceV10jProgressMass

open Q11593SpliceControllerDesign B9SpliceControllerR1Table B9SpliceControllerR1TableV6
  B9SpliceTableV10g B9SpliceTableV10j B9SpliceV10hControllerRowsSafe B9SpliceV10eTransparency
  B9SpliceV10ePairWeight B9SpliceLocalStepMass B9SpliceV10jGlobalProgress
  FixedSpanRenewalPayload

variable {n psi width kappa tau : Nat}

theorem localStep_V10j (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi) (ring : DirectedRing n) :
    LocalStepG ring (stepV10j (kappa := kappa) (tau := tau) hpsi hwidth hle ring) := by
  classical
  refine ⟨?_, ?_⟩
  · intro C e i hi hj
    unfold stepV10j
    by_cases hself : ring.rightNeighbor e = e
    · rw [if_pos hself]
    · rw [if_neg hself]; exact writeAt_other ring C e _ i hi hj
  · intro C C' e hl hr
    unfold stepV10j
    by_cases hself : ring.rightNeighbor e = e
    · rw [if_pos hself, if_pos hself]; exact ⟨hl, hr⟩
    · rw [if_neg hself, if_neg hself, writeAt_e, writeAt_e, writeAt_j ring C' e _ hself, writeAt_j ring C e _ hself,
        hl, hr]
      exact ⟨rfl, rfl⟩

theorem serveIterG_eq_serveIterJ (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi) (ring : DirectedRing n)
    (e : Fin n) (m : Nat) (C : R1ConfigV6 n psi kappa tau) :
    serveIterG (stepV10j hpsi hwidth hle ring) e m C = serveIterJ hpsi hwidth hle ring e m C := by
  induction m with
  | zero => rfl
  | succ m ih =>
    show stepV10j hpsi hwidth hle ring (serveIterG (stepV10j hpsi hwidth hle ring) e m C) e =
      stepV10j hpsi hwidth hle ring (serveIterJ hpsi hwidth hle ring e m C) e
    rw [ih]

theorem progressWithin3_V10j (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
    (ring : DirectedRing n) (hn : 2 ≤ n) (C : R1ConfigV6 n psi kappa tau) (hS : SpliceSafeV7g hpsi ring C) :
    ProgressWithin3G hpsi hwidth hle ring (stepV10j hpsi hwidth hle ring) C := by
  obtain ⟨e, m, hm, h⟩ := globalProgressWithin3J hpsi hwidth hle ring hn C hS
  refine ⟨e, m, hm, ?_⟩
  rw [serveIterG_eq_serveIterJ, serveIterG_eq_serveIterJ]
  rcases h with hp | hd
  · exact Or.inl hp
  · right
    have hself := rightNeighbor_ne_of_two_le ring hn e
    have hid := potential_pair_identity ring C (serveIterJ hpsi hwidth hle ring e (m + 1) C) e hself
      (fun i hi hj => by
        rw [← serveIterG_eq_serveIterJ]
        exact serveIterG_other (localStep_V10j hpsi hwidth hle ring) e (m + 1) C i hi hj)
    omega

theorem progress_massJ (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi)
    (ring : DirectedRing n) (hn : 3 ≤ n) (C : R1ConfigV6 n psi kappa tau) (hS : SpliceSafeV7g hpsi ring C) :
    ∃ e : Fin n, n ^ (6 * n) ≤
      64 * wordSum n (6 * n) (progressBitG hpsi hwidth hle ring (stepV10j hpsi hwidth hle ring) C e) :=
  progress_massG (localStep_V10j hpsi hwidth hle ring) hn C
    (progressWithin3_V10j hpsi hwidth hle ring (by omega) C hS)

end B9SpliceV10jProgressMass
