import Leader.Wu.Splice.GarbageDrainTable
import Leader.Wu.Birth.DrainCoupling

/-! # Block-mass accounting for B9 liveness over the V10d table

Mechanical port of `B9SpliceBlockDrainMass` from `stepV10c` to `stepV10d`. -/



set_option autoImplicit false
set_option Elab.async false
set_option pp.structureInstances false


namespace B9SpliceBlockDrainMassV10d


open FiniteUniformStoppingTree FixedSpanRenewalPayload
open B9SpliceControllerR1TableV6 B9SpliceControllerR1TableV7
open B9SpliceControllerR1TableV10b B9SpliceV10cLiveness
open BirthB1ResetDrainParallel BirthB1DrainCoupling
open B9SpliceBlockDrainMass B9SpliceTableV10d


variable {n psi width kappa tau : Nat}


def runV10d
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau)
    (u : List (Fin n)) : R1ConfigV6 n psi kappa tau :=
  u.foldl (stepV10d hpsi hwidth hle ring) C


def blockNextV10d
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau)
    (i : Fin (n ^ (2 * n))) : R1ConfigV6 n psi kappa tau :=
  runV10d hpsi hwidth hle ring C (rawWord n (2 * n) i)


def BlockProductiveV10d
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau)
    (i : Fin (n ^ (2 * n))) : Prop :=
  controllerPotentialV6 (blockNextV10d hpsi hwidth hle ring C i) <
      controllerPotentialV6 C \/
    RolesClearV7 (blockNextV10d hpsi hwidth hle ring C i)


/-- The one-service bridge restated over the V10d table.  Its second clause is no longer
refuted by `B9SpliceLiveSelector.badC` (see `B9SpliceTableV10d.badC_productive_edge_V10d`);
the general selector over all live non-clear states is the open obligation. -/
def OneServiceBlockBridgeV10d
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (ring : DirectedRing n) : Prop :=
  ∃ A : PortBlockAdapter (R1ConfigV6 n psi kappa tau) n,
    (∀ C i, A.next C i = blockNextV10d hpsi hwidth hle ring C i) /\
    (∀ C, LiveNonClearV10c hpsi ring C ->
      ControllerProductiveServiceV10d hpsi hwidth hle ring C (A.ports C).a) /\
    (∀ C i, LiveNonClearV10c hpsi ring C -> A.hit C i = true ->
      BlockProductiveV10d hpsi hwidth hle ring C i)


noncomputable def bridgeAdapter
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (ring : DirectedRing n)
    (hbridge : OneServiceBlockBridgeV10d
      (kappa := kappa) (tau := tau) hpsi hwidth hle ring) :
    PortBlockAdapter (R1ConfigV6 n psi kappa tau) n :=
  Classical.choose hbridge


private noncomputable def bridge_spec
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (ring : DirectedRing n)
    (hbridge : OneServiceBlockBridgeV10d
      (kappa := kappa) (tau := tau) hpsi hwidth hle ring) :=
  Classical.choose_spec hbridge


theorem distinguished_controller_edge
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (ring : DirectedRing n)
    (hbridge : OneServiceBlockBridgeV10d
      (kappa := kappa) (tau := tau) hpsi hwidth hle ring)
    (C : R1ConfigV6 n psi kappa tau) (hC : LiveNonClearV10c hpsi ring C) :
    ∃ e, ControllerProductiveServiceV10d hpsi hwidth hle ring C e := by
  let A := bridgeAdapter hpsi hwidth hle ring hbridge
  exact ⟨(A.ports C).a, (bridge_spec hpsi hwidth hle ring hbridge).2.1 C hC⟩


theorem one_block_quarter_mass
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (ring : DirectedRing n) (hn : 3 <= n)
    (hbridge : OneServiceBlockBridgeV10d
      (kappa := kappa) (tau := tau) hpsi hwidth hle ring)
    (C : R1ConfigV6 n psi kappa tau) :
    let A := bridgeAdapter hpsi hwidth hle ring hbridge
    n ^ (2 * n) <= 4 * successCount (hitStep A.next A.hit) (.active C) 1 := by
  dsimp only
  exact portBlock_quarter (bridgeAdapter hpsi hwidth hle ring hbridge) hn C


theorem controller_potential_budget (C : R1ConfigV6 n psi kappa tau) :
    controllerPotentialV6 C <= 8 * n :=
  controllerPotentialV6_le_eight_mul C


theorem K_block_geometric
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (ring : DirectedRing n) (hn : 3 <= n)
    (hbridge : OneServiceBlockBridgeV10d
      (kappa := kappa) (tau := tau) hpsi hwidth hle ring)
    (C : R1ConfigV6 n psi kappa tau) (K : Nat) :
    let A := bridgeAdapter hpsi hwidth hle ring hbridge
    4 ^ K * badStageCount (stageWindow A.next A.hit K) C (8 * n) <=
      (8 * n) * 3 ^ K * n ^ ((8 * n) * K * (2 * n)) := by
  dsimp only
  exact adaptive_productive_port_coupling
    (bridgeAdapter hpsi hwidth hle ring hbridge) hn C (8 * n) K


abbrev spliceDrainK (n power : Nat) : Nat := resetDrainBlocks n power
abbrev spliceDrainHighProbL (n power : Nat) : Nat :=
  (8 * n) * spliceDrainK n power * (2 * n)


theorem high_probability_geometric
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (ring : DirectedRing n) (hn : 3 <= n)
    (hbridge : OneServiceBlockBridgeV10d
      (kappa := kappa) (tau := tau) hpsi hwidth hle ring)
    (C : R1ConfigV6 n psi kappa tau) (power : Nat) :
    let A := bridgeAdapter hpsi hwidth hle ring hbridge
    4 ^ spliceDrainK n power *
        badStageCount (stageWindow A.next A.hit (spliceDrainK n power)) C (8 * n) <=
      (8 * n) * 3 ^ spliceDrainK n power * n ^ spliceDrainHighProbL n power := by
  dsimp only
  simpa [spliceDrainHighProbL] using
    K_block_geometric hpsi hwidth hle ring hn hbridge C (spliceDrainK n power)



#print axioms distinguished_controller_edge
#print axioms one_block_quarter_mass
#print axioms controller_potential_budget
#print axioms K_block_geometric
#print axioms high_probability_geometric


end B9SpliceBlockDrainMassV10d
