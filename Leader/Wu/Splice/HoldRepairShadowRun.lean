import Leader.Wu.Splice.HoldRepairBirthAtHostEvents
import Leader.Wu.Splice.LocalStepMass

set_option autoImplicit false
set_option Elab.async false

/-! # V10j with leaders: the K2 layer sees the shadow run on the physical sub-word

`physWordJ w C` is the sub-word of the services of `w` that are physical along the V10j run from `C`; its length is
`physCountG` (`physWordJ_length`).  Along a composed word in which no physical service has a host birth event
(`B9SpliceV10jBirthOnlyAtHostEvents.NoHostBirthAlongJ`), the K2 observation of the base projection after the word is
the frozen K2 shadow run (`K2BirthDispatcher.shadowStep`) on the physical sub-word (`observe_run_J`).  This is the
composed counterpart of `BirthShortDoneTerminalObserver.observe_run_of_no_birth`, with or without leaders and
without any safety hypothesis: physical services are host steps (`B9SpliceV10jK2Observation.project_physical`), a
host step without a birth event is a shadow step on the observation, and non-physical services, including the
MOVE-COMMIT relabels, leave the observation unchanged (`B9SpliceV10jK2Observation.observe_nonphysical`). -/

namespace B9SpliceV10jShadowRun

open Q11593SpliceControllerDesign B9SpliceControllerR1Table B9SpliceControllerR1TableV6
  B9SpliceTableV10j B9SpliceV10hControllerRowsSafe B9SpliceV10eTransparency B9SpliceV10ePhysicalIsB7Step
  B9SpliceV10jK2Observation B9SpliceV10jBirthOnlyAtHostEvents B9SpliceLocalStepMass

variable {n psi width kappa tau : Nat}

/-- The physical sub-word of a composed V10j word. -/
noncomputable def physWordJ (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi) (ring : DirectedRing n) :
    List (Fin n) → R1ConfigV6 n psi kappa tau → List (Fin n)
  | [], _ => []
  | e :: w, C => by
      classical
      exact (if PhysicalServiceAt hpsi hwidth hle ring C (stepV10j hpsi hwidth hle ring C e) e then [e] else []) ++
        physWordJ hpsi hwidth hle ring w (stepV10j hpsi hwidth hle ring C e)

theorem physWordJ_length (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi) (ring : DirectedRing n) :
    ∀ (w : List (Fin n)) (C : R1ConfigV6 n psi kappa tau),
      (physWordJ hpsi hwidth hle ring w C).length =
        physCountG hpsi hwidth hle ring (stepV10j hpsi hwidth hle ring) w C
  | [], _ => rfl
  | e :: w, C => by
      classical
      have ih := physWordJ_length hpsi hwidth hle ring w (stepV10j hpsi hwidth hle ring C e)
      show ((if PhysicalServiceAt hpsi hwidth hle ring C (stepV10j hpsi hwidth hle ring C e) e then [e] else []) ++
          physWordJ hpsi hwidth hle ring w (stepV10j hpsi hwidth hle ring C e)).length =
        (if PhysicalServiceAt hpsi hwidth hle ring C (stepV10j hpsi hwidth hle ring C e) e then 1 else 0) +
          physCountG hpsi hwidth hle ring (stepV10j hpsi hwidth hle ring) w (stepV10j hpsi hwidth hle ring C e)
      by_cases hp : PhysicalServiceAt hpsi hwidth hle ring C (stepV10j hpsi hwidth hle ring C e) e
      · rw [if_pos hp, if_pos hp, List.length_append, ih]; rfl
      · rw [if_neg hp, if_neg hp, List.length_append, ih]; rfl

/-- One service on the K2 observation. -/
theorem observe_step_J (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi) (ring : DirectedRing n)
    (C : R1ConfigV6 n psi kappa tau) (e : Fin n)
    (hphys : PhysicalServiceAt hpsi hwidth hle ring C (stepV10j hpsi hwidth hle ring C e) e)
    (hnb : BirthShortDoneTerminalObserver.birthEvent hpsi hwidth hle
      (C e).carrier.splice.base (C (ring.rightNeighbor e)).carrier.splice.base = false) :
    ExpiringK2Projection.observe (physicalProj (stepV10j hpsi hwidth hle ring C e)) =
      K2BirthDispatcher.shadowStep ring (ExpiringK2Projection.observe (physicalProj C)) e := by
  rw [project_physical hpsi hwidth hle ring C e hphys]
  exact BirthShortDoneTerminalObserver.observe_step_of_no_birth hpsi hwidth hle ring (physicalProj C) e hnb

/-- Along a composed word without host birth events at physical services, the K2 observation is the shadow run on
the physical sub-word. -/
theorem observe_run_J (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width ≤ psi) (ring : DirectedRing n) :
    ∀ (w : List (Fin n)) (C : R1ConfigV6 n psi kappa tau), NoHostBirthAlongJ hpsi hwidth hle ring C w →
      ExpiringK2Projection.observe (physicalProj (w.foldl (stepV10j hpsi hwidth hle ring) C)) =
        LDSinkBoundedKernel.run (K2BirthDispatcher.shadowStep ring)
          (ExpiringK2Projection.observe (physicalProj C)) (physWordJ hpsi hwidth hle ring w C)
  | [], _, _ => rfl
  | e :: w, C, h => by
      classical
      have ih := observe_run_J hpsi hwidth hle ring w (stepV10j hpsi hwidth hle ring C e) h.2
      show ExpiringK2Projection.observe (physicalProj (w.foldl (stepV10j hpsi hwidth hle ring)
          (stepV10j hpsi hwidth hle ring C e))) =
        LDSinkBoundedKernel.run (K2BirthDispatcher.shadowStep ring) (ExpiringK2Projection.observe (physicalProj C))
          ((if PhysicalServiceAt hpsi hwidth hle ring C (stepV10j hpsi hwidth hle ring C e) e then [e] else []) ++
            physWordJ hpsi hwidth hle ring w (stepV10j hpsi hwidth hle ring C e))
      rw [ih]
      by_cases hp : PhysicalServiceAt hpsi hwidth hle ring C (stepV10j hpsi hwidth hle ring C e) e
      · rw [if_pos hp, observe_step_J hpsi hwidth hle ring C e hp (h.1 hp)]
        rfl
      · rw [if_neg hp, observe_nonphysical hpsi hwidth hle ring C e hp]
        rfl

end B9SpliceV10jShadowRun
