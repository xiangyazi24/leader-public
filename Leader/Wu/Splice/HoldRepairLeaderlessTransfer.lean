import Leader.Wu.Splice.HoldRepairTable

set_option autoImplicit false

/-! # V10j is V10e on leaderless ShapeClear configurations

`stepV10j_eq_stepV10e_of_leaderless_shapeClear`: on a configuration without leaders and without pending
predecessors or victims, one V10j service equals one V10e service.  With the V10e invariants proved in
`B9SpliceShapeClear` (ShapeClear is preserved on leaderless safe runs) and `B9SpliceV10eAssembly` (SpliceSafeV7
is preserved), every leaderless composed result stated for `stepV10e` (transparency, global progress, first-leader
tail from composed escape mass) is a statement about V10j runs up to the first leader. -/

namespace B9SpliceV10jLeaderlessTransfer

open Q11593SpliceControllerDesign B9SpliceControllerR1Table B9SpliceControllerR1TableV6
  B9SpliceTableV10e B9SpliceTableV10g B9SpliceTableV10j

variable {n psi width kappa tau : Nat}

theorem stepV10j_eq_stepV10e_of_leaderless_shapeClear (hpsi : 0 < psi) (hwidth : 0 < width)
    (hle : width ≤ psi) (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau)
    (hlead : ∀ i, (C i).carrier.splice.base.core.core.leader = false)
    (hSC : B9SpliceComposedEvents.ShapeClear C) (e : Fin n) :
    stepV10j hpsi hwidth hle ring C e = stepV10e hpsi hwidth hle ring C e := by
  classical
  rw [stepV10j_eq_stepV10g_of_leaderless hpsi hwidth hle ring C hlead e]
  unfold stepV10g stepV10e
  by_cases hself : ring.rightNeighbor e = e
  · simp only [if_pos hself]
  · simp only [if_neg hself]
    rw [rowV10g_eq_rowV10e_of_no_pending_pred hpsi hwidth hle _ _ (hSC.2 e) (hSC.2 _)]

end B9SpliceV10jLeaderlessTransfer
