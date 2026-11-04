import Leader.Wu.Splice.PhysicalHoldFirstService

set_option autoImplicit false

/-! # Ring-global progress within three services, unconditionally, for V10e on leaderless rings

Pick edge 0.  Its first service is physical or drops the potential (done), or is the handoff
(the third same-edge service is physical), or is the (pending victim, pending predecessor) hold
(the service of the edge into the victim drops the potential). -/

namespace B9SpliceV10eGlobalProgressFinal

open Q11593SpliceControllerDesign B9SpliceControllerR1Table B9SpliceControllerR1TableV2
  B9SpliceControllerR1TableV3 B9SpliceControllerR1TableV6 B9SpliceControllerR1TableV7
  B9SpliceV10cLiveness B9OrphanToFence B9SpliceTableV10d B9SpliceTableV10e
  B9SpliceV10eTransparency B9SpliceV10eGlobalProgress B9SpliceV10eHandoffFollowUp
  B9SpliceV10eClassification

variable {n psi width kappa tau : Nat}

theorem serveIter_one (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (ring : DirectedRing n) (e : Fin n) (C : R1ConfigV6 n psi kappa tau) :
    serveIter hpsi hwidth hle ring e 1 C = stepV10e hpsi hwidth hle ring C e := rfl

theorem rightNeighbor_zero_ne (ring : DirectedRing n) (hn : 2 ≤ n) :
    ring.rightNeighbor ⟨0, by omega⟩ ≠ ⟨0, by omega⟩ := by
  intro h
  have hv := congrArg Fin.val h
  simp only [DirectedRing.rightNeighbor] at hv
  rw [Nat.mod_eq_of_lt (by omega : 0 + 1 < n)] at hv
  omega

theorem globalProgressWithin3
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (ring : DirectedRing n) (hn : 2 ≤ n) :
    GlobalProgressWithin (kappa := kappa) (tau := tau) hpsi hwidth hle ring 3 := by
  intro C hlead hS _
  let e : Fin n := ⟨0, by omega⟩
  have hne : ring.rightNeighbor e ≠ e := rightNeighbor_zero_ne ring hn
  rcases first_service_classified hpsi hwidth hle ring C e hne hlead hS with hphys | hdrop | hhand | hvp
  · exact ⟨e, 0, by decide, Or.inl hphys⟩
  · exact ⟨e, 0, by decide, Or.inr hdrop⟩
  · refine ⟨e, 2, by decide, Or.inl ?_⟩
    exact handoff_then_seek_then_physical hpsi hwidth hle ring C e hne (hlead e) (hlead _) hhand
  · -- the edge into the pending victim drops the potential
    let p := ring.leftNeighbor e
    have hp : ring.rightNeighbor p = e := rightNeighbor_leftNeighbor ring e
    have hpne : ring.rightNeighbor p ≠ p := by
      intro h
      apply hne
      rw [hp] at h
      rw [← h] at hp
      exact hp
    refine ⟨p, 0, by decide, Or.inr ?_⟩
    rw [serveIter_one]
    show controllerPotentialV6 (stepV10e hpsi hwidth hle ring C p) < controllerPotentialV6 C
    apply edge_into_pending_victim_drops hpsi hwidth hle ring C p hpne
    · rw [hp]; exact hvp.1
    · rw [hp]; exact hvp.2.1

end B9SpliceV10eGlobalProgressFinal
