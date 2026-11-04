import Leader.Wu.RaceEntrance.ControlledBirth
import Leader.Wu.RaceEntrance.ControlledShot

set_option autoImplicit false

open FiniteUniformStoppingTree PPLLRepair
open LDSinkGapCleanup LDTwoGapFrame LDSinkTwoGapNoResetKernel
open LDSinkTwoGapDeletion LDSinkTwoGapDeletionWired LDSinkTwoGapReachInvariant
open LDSinkTwoGapArrivalRaceMass LDSinkTwoGapRaceEntranceFreshService
open LDSinkTwoGapRaceEntranceControlledTail LDSinkTwoGapRaceEntranceControlledBirth
open LDSinkTwoGapRaceEntranceControlledShot

namespace LDSinkTwoGapControlledBirthShotComposition

variable {n psi : Nat}

/-! The first carrier adds only the proved, physically closed false-shield
predicate to the existing birth service. Its stopping event is unchanged.
At a successful birth, the same physical post-configuration enters the shot
service with ghost phase transit. The composition below is related edge by
edge to the original controlled physical process, including terminal outcomes.
No additional probability, drift, or scheduler-event bound is assumed.
-/

/-- A proof refinement of the existing birth carrier, with no new physical field. -/
abbrev UnshieldedBirth (hpsi : psi > 0) (F : TwoGapFrame n) :=
  { z : BirthState hpsi F // (z.val.conf (deletePort F)).shield = false }

/-- An active birth edge is the actual post-state and has not fired its stopping event. -/
theorem birth_active_data (hpsi : psi > 0) (F : TwoGapFrame n)
    (z y : BirthState hpsi F) (e : Fin n)
    (he : controlledBirthStep hpsi F z e = .active y) :
    y.val = postState hpsi F z.val (controlledPort F z.val.conf e) ∧
      ¬ BirthEvent hpsi F z.val (controlledPort F z.val.conf e) := by
  classical
  unfold controlledBirthStep birthStep at he
  split at he
  · cases he
  · rename_i hn
    exact ⟨congrArg Subtype.val (StopNode.active.inj he).symm, hn⟩

/-- Lift the same stopped birth tree by propagating its actual shield invariant. -/
noncomputable def unshieldedBirthStep (hpsi : psi > 0) (F : TwoGapFrame n)
    (z : UnshieldedBirth hpsi F) (e : Fin n) : StopNode (UnshieldedBirth hpsi F) :=
  match he : controlledBirthStep hpsi F z.val e with
  | .success => .success
  | .failure => .failure
  | .active y => .active ⟨y, by
      rw [(birth_active_data hpsi F z.val y e he).1]
      exact controlled_shield_closed hpsi F z.val.val z.property e⟩

/-- Forget only the added shield proof. -/
def eraseUnshielded (hpsi : psi > 0) (F : TwoGapFrame n) :
    StopNode (UnshieldedBirth hpsi F) → StopNode (BirthState hpsi F)
  | .success => .success
  | .failure => .failure
  | .active z => .active z.val

/-- The refined birth carrier executes exactly the original birth edge. -/
theorem unshieldedBirthStep_erases (hpsi : psi > 0) (F : TwoGapFrame n)
    (x : StopNode (UnshieldedBirth hpsi F)) (e : Fin n) :
    eraseUnshielded hpsi F (stepNode (unshieldedBirthStep hpsi F) x e) =
      stepNode (controlledBirthStep hpsi F) (eraseUnshielded hpsi F x) e := by
  cases x with
  | success => rfl
  | failure => rfl
  | active z =>
      change eraseUnshielded hpsi F (unshieldedBirthStep hpsi F z e) = _
      unfold unshieldedBirthStep
      split <;> simp_all only [eraseUnshielded, stepNode]

private theorem birth_tree_erases (hpsi : psi > 0) (F : TwoGapFrame n)
    (w : StopNode (BirthState hpsi F) → Nat)
    (x : StopNode (UnshieldedBirth hpsi F)) (T : Nat) :
    treeWeight (unshieldedBirthStep hpsi F)
        (fun y => w (eraseUnshielded hpsi F y)) x T =
      treeWeight (controlledBirthStep hpsi F) w (eraseUnshielded hpsi F x) T := by
  induction T generalizing x with
  | zero => rfl
  | succ T ih =>
      simp only [treeWeight]
      apply ofFn_sum_eq
      intro e
      rw [ih, unshieldedBirthStep_erases]

/-- The existing birth half-mass bound survives the proof refinement exactly. -/
theorem unshielded_birth_half (hpsi : psi > 0) (F : TwoGapFrame n)
    (z : UnshieldedBirth hpsi F) :
    n ^ (2 * n * (12 * F.attack.d + 5)) ≤
      2 * successCount (unshieldedBirthStep hpsi F) (.active z)
        (2 * n * (12 * F.attack.d + 5)) := by
  have hm := controlled_birth_half hpsi F z.val
  have hw : (fun y => successWeight (eraseUnshielded hpsi F y)) = successWeight := by
    funext y
    cases y <;> rfl
  have he := birth_tree_erases hpsi F successWeight (.active z)
    (2 * n * (12 * F.attack.d + 5))
  rw [hw] at he
  change successCount (unshieldedBirthStep hpsi F) (.active z) _ =
    successCount (controlledBirthStep hpsi F) (.active z.val) _ at he
  rw [he]
  exact hm

/-! ## Physical configuration equality under ghost phase retagging -/

/-- Reclassify the proof phase while retaining every physical register. -/
def retagTransit (b : AState n psi) : AState n psi := ⟨b.conf, .transit⟩

theorem retagTransit_conf (b : AState n psi) : (retagTransit b).conf = b.conf := rfl

/-- Both the effective scheduler edge and K2 update depend only on configuration. -/
theorem controlled_post_conf_eq (hpsi : psi > 0) (F : TwoGapFrame n)
    (x y : AState n psi) (hc : x.conf = y.conf) (e : Fin n) :
    attemptStepConf hpsi F x (controlledPort F x.conf e) =
      attemptStepConf hpsi F y (controlledPort F y.conf e) := by
  simp only [attemptStepConf_eq_sinkStepC, hc]

/-- Equality of physical configurations with exact agreement on stopped outcomes. -/
def PhysicalRel : StopNode (AState n psi) → StopNode (AState n psi) → Prop
  | .active x, .active y => x.conf = y.conf
  | .success, .success => True
  | .failure, .failure => True
  | _, _ => False

private theorem physicalRel_refl (x : StopNode (AState n psi)) : PhysicalRel x x := by
  cases x <;> first | rfl | trivial

private theorem physicalRel_trans {x y z : StopNode (AState n psi)}
    (hxy : PhysicalRel x y) (hyz : PhysicalRel y z) : PhysicalRel x z := by
  cases x <;> cases y <;> cases z <;> simp_all [PhysicalRel]

/-- A ghost phase difference cannot change the next physical state or deletion event. -/
theorem physicalRel_next (hpsi : psi > 0) (F : TwoGapFrame n)
    (x y : StopNode (AState n psi)) (h : PhysicalRel x y) (e : Fin n) :
    PhysicalRel (stepNode (controlledPhysicalStep hpsi F) x e)
      (stepNode (controlledPhysicalStep hpsi F) y e) := by
  classical
  cases x <;> cases y <;> simp_all only [PhysicalRel, stepNode]
  rename_i x y
  have hc := controlled_post_conf_eq hpsi F x y h e
  unfold controlledPhysicalStep
  rw [physicalBlockStep_normal_form, physicalBlockStep_normal_form, hc]
  by_cases hs : NoResetSuccess F (attemptStepConf hpsi F y (controlledPort F y.conf e))
  · simp only [if_pos hs]
  · simp only [if_neg hs]
    exact hc

/-- The real post-edge state is handed off on the birth edge itself. Early
physical deletion stops immediately; otherwise only the ghost phase is retagged. -/
noncomputable def shotHandoff (hpsi : psi > 0) (F : TwoGapFrame n)
    (z : UnshieldedBirth hpsi F) (e : Fin n) : StopNode (AState n psi) := by
  classical
  let f := controlledPort F z.val.val.conf e
  exact if NoResetSuccess F (attemptStepConf hpsi F z.val.val f) then .success
    else .active (retagTransit (postState hpsi F z.val.val f))

/-- The handoff has precisely the next physical configuration and stopped outcome. -/
theorem shotHandoff_physical (hpsi : psi > 0) (F : TwoGapFrame n)
    (z : UnshieldedBirth hpsi F) (e : Fin n) :
    PhysicalRel (shotHandoff hpsi F z e)
      (controlledPhysicalStep hpsi F z.val.val e) := by
  classical
  unfold shotHandoff controlledPhysicalStep
  rw [physicalBlockStep_normal_form]
  dsimp only
  split <;> first | trivial | rfl

/-- Successful birth supplies the proved fresh-shot premise and the physically
propagated shield premise. Deleted handoffs retain their full padded success mass. -/
theorem shotHandoff_half (hpsi : psi > 0) (F : TwoGapFrame n)
    (z : UnshieldedBirth hpsi F) (e : Fin n)
    (he : unshieldedBirthStep hpsi F z e = .success) :
    n ^ (2 * n * (F.attack.d + 2)) ≤
      2 * successCount (controlledPhysicalStep hpsi F) (shotHandoff hpsi F z e)
        (2 * n * (F.attack.d + 2)) := by
  classical
  have hb : controlledBirthStep hpsi F z.val e = .success := by
    have hh := unshieldedBirthStep_erases hpsi F (.active z) e
    change eraseUnshielded hpsi F (unshieldedBirthStep hpsi F z e) = _ at hh
    rw [he] at hh
    exact hh.symm
  have hf := controlledBirth_success_produces_fresh hpsi F z.val e hb
  have hs := controlled_shield_closed hpsi F z.val.val z.property e
  unfold shotHandoff
  dsimp only
  split
  · simp only [successCount, treeWeight_success, successWeight, Nat.mul_one]
    omega
  · rename_i hn
    rcases hf with hf | hd
    · exact fresh_controlled_half hpsi F _ hf hs
    · exact (hn hd).elim

/-! ## Same-edge composition and transfer to the actual physical stopping tree -/

/-- The established two-phase constructor consumes each raw edge exactly once. -/
noncomputable def birthShotStep (hpsi : psi > 0) (F : TwoGapFrame n) :=
  sequentialStep (unshieldedBirthStep hpsi F) (controlledPhysicalStep hpsi F)
    (shotHandoff hpsi F)

/-- Forget the service tag and birth proofs, retaining the actual configuration. -/
def eraseComposition (hpsi : psi > 0) (F : TwoGapFrame n) :
    StopNode (Sum (UnshieldedBirth hpsi F) (AState n psi)) → StopNode (AState n psi)
  | .active (.inl z) => .active z.val.val
  | .active (.inr b) => .active b
  | .success => .success
  | .failure => .failure

private theorem eraseComposition_inRace (hpsi : psi > 0) (F : TwoGapFrame n)
    (x : StopNode (AState n psi)) :
    eraseComposition hpsi F (inRace x) = x := by
  cases x <;> rfl

/-- Exact physical erasure at every raw edge, allowing only a ghost phase difference. -/
theorem birthShotStep_erases (hpsi : psi > 0) (F : TwoGapFrame n)
    (x : StopNode (Sum (UnshieldedBirth hpsi F) (AState n psi))) (e : Fin n) :
    PhysicalRel (eraseComposition hpsi F (stepNode (birthShotStep hpsi F) x e))
      (stepNode (controlledPhysicalStep hpsi F) (eraseComposition hpsi F x) e) := by
  classical
  cases x with
  | success => trivial
  | failure => trivial
  | active x =>
      cases x with
      | inr b =>
          change PhysicalRel (eraseComposition hpsi F (inRace _)) _
          rw [eraseComposition_inRace]
          exact physicalRel_refl _
      | inl z =>
          change PhysicalRel
            (eraseComposition hpsi F
              (sequentialStep (unshieldedBirthStep hpsi F)
                (controlledPhysicalStep hpsi F) (shotHandoff hpsi F) (.inl z) e))
            (controlledPhysicalStep hpsi F z.val.val e)
          cases he : unshieldedBirthStep hpsi F z e with
          | success =>
              simp only [sequentialStep, he, eraseComposition_inRace]
              exact shotHandoff_physical hpsi F z e
          | failure =>
              have hh := unshieldedBirthStep_erases hpsi F (.active z) e
              change eraseUnshielded hpsi F (unshieldedBirthStep hpsi F z e) = _ at hh
              rw [he] at hh
              change .failure = controlledBirthStep hpsi F z.val e at hh
              unfold controlledBirthStep birthStep at hh
              split at hh <;> cases hh
          | active y =>
              have hh := unshieldedBirthStep_erases hpsi F (.active z) e
              change eraseUnshielded hpsi F (unshieldedBirthStep hpsi F z e) = _ at hh
              rw [he] at hh
              have hd := birth_active_data hpsi F z.val y.val e hh.symm
              have hn : ¬ NoResetSuccess F (attemptStepConf hpsi F z.val.val
                  (controlledPort F z.val.val.conf e)) := fun h => hd.2 (.inl h)
              simp only [sequentialStep, he, eraseComposition, controlledPhysicalStep]
              rw [physicalBlockStep_normal_form, if_neg hn]
              exact congrArg AState.conf hd.1

/-- The relation used by the existing success-count simulation theorem. -/
def CompositionRel (hpsi : psi > 0) (F : TwoGapFrame n)
    (x : StopNode (Sum (UnshieldedBirth hpsi F) (AState n psi)))
    (y : StopNode (AState n psi)) : Prop :=
  PhysicalRel (eraseComposition hpsi F x) y

/-- No successful leaf is synthetic; the target executes the identical raw edge. -/
theorem composition_simulation (hpsi : psi > 0) (F : TwoGapFrame n) :
    SuccessSimulation (birthShotStep hpsi F) (controlledPhysicalStep hpsi F)
      (CompositionRel hpsi F) where
  terminal := by
    intro x y h
    cases x with
    | active z => exact Nat.zero_le _
    | failure => exact Nat.zero_le _
    | success => cases y <;> simp_all [CompositionRel, eraseComposition, PhysicalRel,
        successWeight]
  next := by
    intro x y h e
    exact physicalRel_trans (birthShotStep_erases hpsi F x e)
      (physicalRel_next hpsi F (eraseComposition hpsi F x) y h e)

/-- From the given unshielded gap pair, the same controlled K2 path deletes
a real endpoint with at least one quarter of all words at the full sum horizon.
The attack frame is unchanged and the initial shield premise remains explicit. -/
theorem gapPair_unshielded_deletion_quarter (hpsi : psi > 0) (F : TwoGapFrame n)
    (b : AState n psi) (hg : GapPair hpsi F b)
    (hs : (b.conf (deletePort F)).shield = false) :
    n ^ (2 * n * (13 * F.attack.d + 7)) ≤
      4 * successCount (controlledPhysicalStep hpsi F) (.active b)
        (2 * n * (13 * F.attack.d + 7)) := by
  let z : UnshieldedBirth hpsi F := ⟨⟨b, hg⟩, hs⟩
  let H := 2 * n * (12 * F.attack.d + 5)
  let L := 2 * n * (F.attack.d + 2)
  have hseq := sequential_mass (unshieldedBirthStep hpsi F)
    (controlledPhysicalStep hpsi F) (shotHandoff hpsi F) z H L 2 2
    (unshielded_birth_half hpsi F z) (shotHandoff_half hpsi F)
  have hsim := successCount_le_of_simulation (birthShotStep hpsi F)
    (controlledPhysicalStep hpsi F) (CompositionRel hpsi F)
    (composition_simulation hpsi F) (.active (.inl z)) (.active b) rfl (H + L)
  have htime : H + L = 2 * n * (13 * F.attack.d + 7) := by
    dsimp only [H, L]
    rw [← Nat.mul_add]
    congr 1
    omega
  change n ^ (H + L) ≤ 4 * successCount (birthShotStep hpsi F)
    (.active (.inl z)) (H + L) at hseq
  rw [htime] at hseq hsim
  exact Nat.le_trans hseq (Nat.mul_le_mul_left 4 hsim)

/-- The physical tree's success event is deletion of one of the frame's three
actual leaders, evaluated after the same controlled K2 interaction. -/
theorem controlled_success_deletes_endpoint (hpsi : psi > 0) (F : TwoGapFrame n)
    (b : AState n psi) (e : Fin n)
    (he : controlledPhysicalStep hpsi F b e = .success) :
    let C := attemptStepConf hpsi F b (controlledPort F b.conf e)
    (C (F.recovery.pos 0)).leader = false ∨
      (C (F.attack.pos 0)).leader = false ∨
      (C (F.attack.pos F.attack.d)).leader = false := by
  exact physicalBlockStep_deletes_one_of_three hpsi F b (controlledPort F b.conf e) he

end LDSinkTwoGapControlledBirthShotComposition

#print axioms LDSinkTwoGapControlledBirthShotComposition.unshieldedBirthStep_erases
#print axioms LDSinkTwoGapControlledBirthShotComposition.unshielded_birth_half
#print axioms LDSinkTwoGapControlledBirthShotComposition.controlled_post_conf_eq
#print axioms LDSinkTwoGapControlledBirthShotComposition.shotHandoff_half
#print axioms LDSinkTwoGapControlledBirthShotComposition.birthShotStep_erases
#print axioms LDSinkTwoGapControlledBirthShotComposition.composition_simulation
#print axioms LDSinkTwoGapControlledBirthShotComposition.gapPair_unshielded_deletion_quarter
#print axioms LDSinkTwoGapControlledBirthShotComposition.controlled_success_deletes_endpoint
