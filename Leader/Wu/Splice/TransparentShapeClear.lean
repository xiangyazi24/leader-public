import Leader.Wu.Splice.ComposedEvents
import Leader.Wu.Splice.PhysicalHoldTransparency
import Leader.Wu.Splice.PhysicalHoldHandoffFollowUp
import Leader.Wu.Splice.PhysicalHoldFirstService
import Leader.Wu.Splice.PhysicalHoldLeaderlessSafe
import Leader.Wu.Splice.TwoDropPhysical
import Leader.Wu.Splice.ShapeClearInvariant

set_option autoImplicit false
set_option Elab.async false

namespace B9SpliceTransparentShapeClear

open PPLL PPLLDomain PPLLResearchFormulation
open Q11593SpliceControllerDesign
open B9SpliceControllerR1Table B9SpliceControllerR1TableV2
  B9SpliceControllerR1TableV3 B9SpliceControllerR1TableV6
  B9SpliceControllerR1TableV7 B9SpliceControllerR1TableV8
  B9SpliceControllerR1TableV9 B9SpliceControllerR1TableV10b
open B9OrphanToFence B9SpliceV10cLiveness
  B9SpliceTableV10d B9SpliceTableV10e
  B9SpliceV10eTransparency B9SpliceV10eHandoffFollowUp
  B9SpliceV10eClassification B9SpliceV10eAssembly
  B9SpliceComposedEvents B9SpliceV10ePhysicalIsB7Step

variable {n psi width kappa tau : Nat}

/-- Equality of the physical projection transports leaderlessness cellwise. -/
theorem leaderless_of_physicalProj_eq
    (C D : R1ConfigV6 n psi kappa tau)
    (hlead : forall i,
      (C i).carrier.splice.base.core.core.leader = false)
    (hproj : physicalProj D = physicalProj C) :
    forall i, (D i).carrier.splice.base.core.core.leader = false := by
  intro i
  have hi := congrFun hproj i
  have hb := congrArg (fun u => u.core.core.leader) hi
  change (D i).carrier.splice.base.core.core.leader =
    (C i).carrier.splice.base.core.core.leader at hb
  exact hb.trans (hlead i)

/-- Four-hit same-edge transparency from `ShapeClear`, relative only to the
separate `ShapeClear` preservation hypothesis requested by the composition
layer. -/
theorem transparentWithin4_shapeClear
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (ring : DirectedRing n)
    (hpres :
      forall (D : R1ConfigV6 n psi kappa tau) (f : Fin n),
        ring.rightNeighbor f ≠ f ->
        (forall i,
          (D i).carrier.splice.base.core.core.leader = false) ->
        SpliceSafeV7 hpsi ring D ->
        ShapeClear D ->
        ShapeClear (stepV10e hpsi hwidth hle ring D f)) :
    forall (C : R1ConfigV6 n psi kappa tau) (e : Fin n),
      (forall i,
        (C i).carrier.splice.base.core.core.leader = false) ->
      SpliceSafeV7 hpsi ring C ->
      ShapeClear C ->
      ring.rightNeighbor e ≠ e ->
      exists m, m < 4 /\
        PhysicalServiceAt hpsi hwidth hle ring
          (serveIter hpsi hwidth hle ring e m C)
          (serveIter hpsi hwidth hle ring e (m + 1) C) e := by
  intro C e hlead0 hS0 hclear0 hne

  let C1 : R1ConfigV6 n psi kappa tau :=
    stepV10e hpsi hwidth hle ring C e
  let C2 : R1ConfigV6 n psi kappa tau :=
    stepV10e hpsi hwidth hle ring C1 e

  by_cases hp0 : PhysicalServiceAt hpsi hwidth hle ring C C1 e
  · refine ⟨0, by decide, ?_⟩
    change PhysicalServiceAt hpsi hwidth hle ring C C1 e
    exact hp0

  have hproj0 : physicalProj C1 = physicalProj C := by
    change physicalProj (stepV10e hpsi hwidth hle ring C e) = physicalProj C
    exact stutter_frame hpsi hwidth hle ring C e hne hlead0 hS0 hp0
      (noCommit_of_shapeClear ring C e hclear0)
  have hlead1 : forall i,
      (C1 i).carrier.splice.base.core.core.leader = false :=
    leaderless_of_physicalProj_eq C C1 hlead0 hproj0
  have hS1 : SpliceSafeV7 hpsi ring C1 := by
    change SpliceSafeV7 hpsi ring (stepV10e hpsi hwidth hle ring C e)
    exact B9SpliceV10eAssembly.stepV10e_preserves_spliceSafeV7_leaderless_final
      hpsi hwidth hle ring C e hlead0 hS0
  have hclear1 : ShapeClear C1 := by
    change ShapeClear (stepV10e hpsi hwidth hle ring C e)
    exact hpres C e hne hlead0 hS0 hclear0

  by_cases hp1 : PhysicalServiceAt hpsi hwidth hle ring C1 C2 e
  · refine ⟨1, by decide, ?_⟩
    change PhysicalServiceAt hpsi hwidth hle ring C1 C2 e
    exact hp1

  have hproj1 : physicalProj C2 = physicalProj C1 := by
    change physicalProj (stepV10e hpsi hwidth hle ring C1 e) = physicalProj C1
    exact stutter_frame hpsi hwidth hle ring C1 e hne hlead1 hS1 hp1
      (noCommit_of_shapeClear ring C1 e hclear1)
  have hlead2 : forall i,
      (C2 i).carrier.splice.base.core.core.leader = false :=
    leaderless_of_physicalProj_eq C1 C2 hlead1 hproj1
  have hS2 : SpliceSafeV7 hpsi ring C2 := by
    change SpliceSafeV7 hpsi ring (stepV10e hpsi hwidth hle ring C1 e)
    exact B9SpliceV10eAssembly.stepV10e_preserves_spliceSafeV7_leaderless_final
      hpsi hwidth hle ring C1 e hlead1 hS1
  have hclear2 : ShapeClear C2 := by
    change ShapeClear (stepV10e hpsi hwidth hle ring C1 e)
    exact hpres C1 e hne hlead1 hS1 hclear1

  by_cases hp2 : PhysicalServiceAt hpsi hwidth hle ring C2
      (stepV10e hpsi hwidth hle ring C2 e) e
  · refine ⟨2, by decide, ?_⟩
    change PhysicalServiceAt hpsi hwidth hle ring C2
      (stepV10e hpsi hwidth hle ring C2 e) e
    exact hp2

  have hc0 :
      PhysicalServiceAt hpsi hwidth hle ring C C1 e \/
      controllerPotentialV6 C1 < controllerPotentialV6 C \/
      HostFenceAdvanceGuardV10b hpsi (C e) (C (ring.rightNeighbor e)) \/
      VictimPredHold (C e) (C (ring.rightNeighbor e)) := by
    simpa only [C1] using
      (B9SpliceV10eClassification.first_service_classified
        hpsi hwidth hle ring C e hne hlead0 hS0)

  rcases hc0 with hphys0 | hdrop0 | hhand0 | hv0
  · exact (hp0 hphys0).elim
  · have hc1 :
        PhysicalServiceAt hpsi hwidth hle ring C1 C2 e \/
        controllerPotentialV6 C2 < controllerPotentialV6 C1 \/
        HostFenceAdvanceGuardV10b hpsi
          (C1 e) (C1 (ring.rightNeighbor e)) \/
        VictimPredHold (C1 e) (C1 (ring.rightNeighbor e)) := by
      simpa only [C2] using
        (B9SpliceV10eClassification.first_service_classified
          hpsi hwidth hle ring C1 e hne hlead1 hS1)
    rcases hc1 with hphys1 | hdrop1 | hhand1 | hv1
    · exact (hp1 hphys1).elim
    · have hnext := B9SpliceTwoDropPhysical.two_consecutive_drop_shapeClear_next_physical
        hpsi hwidth hle ring C C1 C2 e hne rfl rfl
        hlead0 hlead1 hlead2 hS0 hS1 hS2
        hclear0 hclear1 hclear2 hp0 hp1 hdrop0 hdrop1
      exact (hp2 hnext).elim
    · have hh := handoff_then_seek_then_physical
        hpsi hwidth hle ring C1 e hne
        (hlead1 e) (hlead1 (ring.rightNeighbor e)) hhand1
      refine ⟨3, by decide, ?_⟩
      change PhysicalServiceAt hpsi hwidth hle ring
        (serveIter hpsi hwidth hle ring e 2 C1)
        (serveIter hpsi hwidth hle ring e 3 C1) e
      exact hh
    · exact (hclear1.1 e hv1.1).elim
  · have hh := handoff_then_seek_then_physical
      hpsi hwidth hle ring C e hne
      (hlead0 e) (hlead0 (ring.rightNeighbor e)) hhand0
    have hh' : PhysicalServiceAt hpsi hwidth hle ring C2
        (stepV10e hpsi hwidth hle ring C2 e) e := by
      change PhysicalServiceAt hpsi hwidth hle ring
        (serveIter hpsi hwidth hle ring e 2 C)
        (serveIter hpsi hwidth hle ring e 3 C) e
      exact hh
    exact (hp2 hh').elim
  · exact (hclear0.1 e hv0.1).elim

/-- Unconditional four-hit same-edge transparency: from a leaderless `SpliceSafeV7` `ShapeClear`
configuration, among four consecutive services of any non-self edge one is physical. -/
theorem transparentWithin4_shapeClear_final
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau) (e : Fin n)
    (hlead : ∀ i, (C i).carrier.splice.base.core.core.leader = false)
    (hS : SpliceSafeV7 hpsi ring C) (hSC : ShapeClear C)
    (hne : ring.rightNeighbor e ≠ e) :
    ∃ m, m < 4 ∧
      PhysicalServiceAt hpsi hwidth hle ring
        (serveIter hpsi hwidth hle ring e m C)
        (serveIter hpsi hwidth hle ring e (m + 1) C) e :=
  transparentWithin4_shapeClear hpsi hwidth hle ring
    (fun D f _ hl hSD hc =>
      B9SpliceShapeClear.stepV10e_preserves_shapeClear hpsi hwidth hle ring D f hl hSD hc)
    C e hlead hS hSC hne

end B9SpliceTransparentShapeClear
