import Leader.Wu.Elimination.TwoLeaderEntranceBirth
import Leader.Wu.Elimination.TwoLeaderEntranceShot
import Leader.Wu.Elimination.TwoLeaderEntranceUnshield

set_option autoImplicit false

open FiniteUniformStoppingTree PPLLRepair
open LDSinkGapCleanup LDSinkTwoGapDeletion
open K2TwoLeaderGeometry K2TwoLeaderEntranceCore K2TwoLeaderEntranceBirth
open K2TwoLeaderEntranceShot K2TwoLeaderEntranceUnshield

namespace K2TwoLeaderEntranceComposition

variable {n psi : Nat}

/-! The proof carriers below all erase to the identical physical configuration
on the original ring.  The handoff consumes its one real edge exactly once;
early deletion is padded to the full sum of the two service horizons. -/

/-- A proof refinement of the existing birth carrier, with no new physical field. -/
abbrev UnshieldedBirth (hpsi : psi > 0) (F : TwoLeaderFrame n) :=
  { z : BirthState hpsi F // (z.val (deletePort F)).shield = false }

/-- An active birth edge is the actual post-state and has not fired its stopping event. -/
theorem birth_active_data (hpsi : psi > 0) (F : TwoLeaderFrame n)
    (z y : BirthState hpsi F) (e : Fin n)
    (he : controlledBirthStep hpsi F z e = .active y) :
    y.val = rawConf hpsi F z.val (controlledPort F z.val e) ∧
      ¬ BirthEvent hpsi F z.val (controlledPort F z.val e) := by
  classical
  unfold controlledBirthStep birthStep at he
  split at he
  · cases he
  · rename_i hn
    exact ⟨congrArg Subtype.val (StopNode.active.inj he).symm, hn⟩

/-- Lift the same stopped birth tree by propagating its actual shield invariant. -/
noncomputable def unshieldedBirthStep (hpsi : psi > 0) (F : TwoLeaderFrame n)
    (z : UnshieldedBirth hpsi F) (e : Fin n) : StopNode (UnshieldedBirth hpsi F) :=
  match he : controlledBirthStep hpsi F z.val e with
  | .success => .success
  | .failure => .failure
  | .active y => .active ⟨y, by
      rw [(birth_active_data hpsi F z.val y e he).1]
      exact controlled_shield_closed hpsi F z.val.val z.property e⟩

/-- Forget only the added shield proof. -/
def eraseUnshielded (hpsi : psi > 0) (F : TwoLeaderFrame n) :
    StopNode (UnshieldedBirth hpsi F) → StopNode (BirthState hpsi F)
  | .success => .success
  | .failure => .failure
  | .active z => .active z.val

/-- The refined birth carrier executes exactly the original birth edge. -/
theorem unshieldedBirthStep_erases (hpsi : psi > 0) (F : TwoLeaderFrame n)
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

private theorem birth_tree_erases (hpsi : psi > 0) (F : TwoLeaderFrame n)
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
theorem unshielded_birth_half (hpsi : psi > 0) (F : TwoLeaderFrame n)
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

/-- Successful birth hands the very same post-interaction configuration to
physical deletion service.  There is no physical or phase retagging. -/
noncomputable def shotHandoff (hpsi : 0 < psi) (F : TwoLeaderFrame n)
    (z : UnshieldedBirth hpsi F) (e : Fin n) : StopNode (Fin n → AgentState psi) :=
  controlledPhysicalStep hpsi F z.val.val e

theorem shotHandoff_half (hpsi : 0 < psi) (F : TwoLeaderFrame n)
    (z : UnshieldedBirth hpsi F) (e : Fin n)
    (he : unshieldedBirthStep hpsi F z e = .success) :
    n ^ (2 * n * (2 * F.attack.d + 1)) ≤
      2 * successCount (controlledPhysicalStep hpsi F) (shotHandoff hpsi F z e)
        (2 * n * (2 * F.attack.d + 1)) := by
  classical
  have hb : controlledBirthStep hpsi F z.val e = .success := by
    have hh := unshieldedBirthStep_erases hpsi F (.active z) e
    change eraseUnshielded hpsi F (unshieldedBirthStep hpsi F z e) = _ at hh
    rw [he] at hh
    exact hh.symm
  have hf := controlledBirth_success_produces_fresh hpsi F z.val e hb
  have hs := controlled_shield_closed hpsi F z.val.val z.property e
  unfold shotHandoff
  rw [controlledPhysicalStep_normal_form]
  split
  · simp only [successCount, treeWeight_success, successWeight, Nat.mul_one]
    omega
  · rename_i hn
    rcases hf with hf | hd
    · exact fresh_controlled_half hpsi F _ hf hs
    · exact (hn hd).elim

noncomputable def birthShotStep (hpsi : 0 < psi) (F : TwoLeaderFrame n) :=
  sequentialStep (unshieldedBirthStep hpsi F) (controlledPhysicalStep hpsi F)
    (shotHandoff hpsi F)

def eraseComposition (hpsi : 0 < psi) (F : TwoLeaderFrame n) :
    StopNode (Sum (UnshieldedBirth hpsi F) (Fin n → AgentState psi)) →
      StopNode (Fin n → AgentState psi)
  | .active (.inl z) => .active z.val.val
  | .active (.inr C) => .active C
  | .success => .success
  | .failure => .failure

private theorem eraseComposition_inRace (hpsi : 0 < psi) (F : TwoLeaderFrame n)
    (x : StopNode (Fin n → AgentState psi)) : eraseComposition hpsi F (inRace x) = x := by
  cases x <;> rfl

/-- Exact physical erasure for every scheduling port, including endpoint aliases. -/
theorem birthShotStep_erases (hpsi : 0 < psi) (F : TwoLeaderFrame n)
    (x : StopNode (Sum (UnshieldedBirth hpsi F) (Fin n → AgentState psi))) (e : Fin n) :
    eraseComposition hpsi F (stepNode (birthShotStep hpsi F) x e) =
      stepNode (controlledPhysicalStep hpsi F) (eraseComposition hpsi F x) e := by
  classical
  cases x with
  | success => rfl
  | failure => rfl
  | active x =>
      cases x with
      | inr C => exact eraseComposition_inRace hpsi F _
      | inl z =>
          change eraseComposition hpsi F
            (sequentialStep (unshieldedBirthStep hpsi F) (controlledPhysicalStep hpsi F)
              (shotHandoff hpsi F) (.inl z) e) = controlledPhysicalStep hpsi F z.val.val e
          cases he : unshieldedBirthStep hpsi F z e with
          | success => simp only [sequentialStep, he, eraseComposition_inRace, shotHandoff]
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
              have hn : ¬ Deleted F (rawConf hpsi F z.val.val
                  (controlledPort F z.val.val e)) := fun h => hd.2 (.inl h)
              simp only [sequentialStep, he, eraseComposition]
              rw [controlledPhysicalStep_normal_form, if_neg hn, hd.1]

theorem composition_simulation (hpsi : 0 < psi) (F : TwoLeaderFrame n) :
    SuccessSimulation (birthShotStep hpsi F) (controlledPhysicalStep hpsi F)
      (fun x y => eraseComposition hpsi F x = y) where
  terminal := by
    intro x y h
    rw [← h]
    cases x with
    | success => exact Nat.le_refl _
    | failure => exact Nat.le_refl _
    | active x => cases x <;> exact Nat.le_refl _
  next := by
    intro x y h e
    rw [← h]
    exact birthShotStep_erases hpsi F x e

/-- Both halves are on the same real controlled path and retain the actual
false-shield premise from entry through the source FIRE and final hit. -/
theorem unshielded_deletion_quarter (hpsi : 0 < psi) (F : TwoLeaderFrame n)
    (C : Fin n → AgentState psi) (hg : WrapInvariant hpsi F C)
    (hs : (C (deletePort F)).shield = false) :
    n ^ (2 * n * (14 * F.attack.d + 6)) ≤
      4 * successCount (controlledPhysicalStep hpsi F) (.active C)
        (2 * n * (14 * F.attack.d + 6)) := by
  let z : UnshieldedBirth hpsi F := ⟨⟨C, hg⟩, hs⟩
  let H := 2 * n * (12 * F.attack.d + 5)
  let L := 2 * n * (2 * F.attack.d + 1)
  have hseq := sequential_mass (unshieldedBirthStep hpsi F)
    (controlledPhysicalStep hpsi F) (shotHandoff hpsi F) z H L 2 2
    (unshielded_birth_half hpsi F z) (shotHandoff_half hpsi F)
  have hsim := successCount_le_of_simulation (birthShotStep hpsi F)
    (controlledPhysicalStep hpsi F) (fun x y => eraseComposition hpsi F x = y)
    (composition_simulation hpsi F) (.active (.inl z)) (.active C) rfl (H + L)
  have ht : H + L = 2 * n * (14 * F.attack.d + 6) := by
    dsimp only [H, L]
    rw [← Nat.mul_add]
    congr 1
    omega
  change n ^ (H + L) ≤ 4 * successCount (birthShotStep hpsi F)
    (.active (.inl z)) (H + L) at hseq
  rw [ht] at hseq hsim
  exact Nat.le_trans hseq (Nat.mul_le_mul_left 4 hsim)

private theorem unshield_active_data (hpsi : psi > 0) (F : TwoLeaderFrame n)
    (z y : UnshieldState hpsi F) (e : Fin n)
    (he : unshieldStep hpsi F z e = .active y) :
    y.val = rawConf hpsi F z.val (controlledPort F z.val e) ∧
      ¬ UnshieldedOrDeleted F
        (rawConf hpsi F z.val (controlledPort F z.val e)) := by
  classical
  unfold unshieldStep at he
  split at he
  · cases he
  · rename_i hn
    exact ⟨congrArg Subtype.val (StopNode.active.inj he).symm, hn⟩

/-- The handoff is the same physical interaction that ended unshield service. -/
noncomputable def unshieldHandoff (hpsi : psi > 0) (F : TwoLeaderFrame n)
    (z : UnshieldState hpsi F) (e : Fin n) : StopNode ((Fin n → AgentState psi)) :=
  controlledPhysicalStep hpsi F z.val e

theorem unshieldHandoff_quarter (hpsi : psi > 0) (F : TwoLeaderFrame n)
    (z : UnshieldState hpsi F) (e : Fin n)
    (he : unshieldStep hpsi F z e = .success) :
    n ^ (2 * n * (14 * F.attack.d + 6)) ≤
      4 * successCount (controlledPhysicalStep hpsi F) (unshieldHandoff hpsi F z e)
        (2 * n * (14 * F.attack.d + 6)) := by
  classical
  have hu : UnshieldedOrDeleted F
      (rawConf hpsi F z.val (controlledPort F z.val e)) := by
    unfold unshieldStep at he
    split at he
    · assumption
    · cases he
  unfold unshieldHandoff
  rw [controlledPhysicalStep_normal_form]
  by_cases hd : Deleted F
      (rawConf hpsi F z.val (controlledPort F z.val e))
  · rw [if_pos hd]
    simp only [successCount, treeWeight_success, successWeight, Nat.mul_one]
    omega
  · rw [if_neg hd]
    have hs : (rawConf hpsi F z.val (controlledPort F z.val e)
        (deletePort F)).shield = false := hu.resolve_right hd
    have hg := rawConf_invariant hpsi F z.val z.property (controlledPort F z.val e) hd
    exact unshielded_deletion_quarter hpsi F _ hg hs

noncomputable def unshieldDeletionStep (hpsi : psi > 0) (F : TwoLeaderFrame n) :=
  sequentialStep (unshieldStep hpsi F) (controlledPhysicalStep hpsi F) (unshieldHandoff hpsi F)

def eraseService (hpsi : psi > 0) (F : TwoLeaderFrame n) :
    StopNode (Sum (UnshieldState hpsi F) ((Fin n → AgentState psi))) → StopNode ((Fin n → AgentState psi))
  | .active (.inl z) => .active z.val
  | .active (.inr b) => .active b
  | .success => .success
  | .failure => .failure

private theorem eraseService_inRace (hpsi : psi > 0) (F : TwoLeaderFrame n)
    (x : StopNode ((Fin n → AgentState psi))) : eraseService hpsi F (inRace x) = x := by
  cases x <;> rfl

/-- The first-unshield handoff consumes no extra interaction and preserves
the full physical state, including every physical register. -/
theorem unshieldDeletionStep_erases (hpsi : psi > 0) (F : TwoLeaderFrame n)
    (x : StopNode (Sum (UnshieldState hpsi F) ((Fin n → AgentState psi)))) (e : Fin n) :
    eraseService hpsi F (stepNode (unshieldDeletionStep hpsi F) x e) =
      stepNode (controlledPhysicalStep hpsi F) (eraseService hpsi F x) e := by
  classical
  cases x with
  | success => rfl
  | failure => rfl
  | active x =>
      cases x with
      | inr b => exact eraseService_inRace hpsi F _
      | inl z =>
          change eraseService hpsi F
            (sequentialStep (unshieldStep hpsi F) (controlledPhysicalStep hpsi F)
              (unshieldHandoff hpsi F) (.inl z) e) = controlledPhysicalStep hpsi F z.val e
          cases he : unshieldStep hpsi F z e with
          | success =>
              simp only [sequentialStep, he, eraseService_inRace, unshieldHandoff]
          | failure =>
              unfold unshieldStep at he
              split at he <;> cases he
          | active y =>
              have hd := unshield_active_data hpsi F z y e he
              have hn : ¬ Deleted F
                  (rawConf hpsi F z.val (controlledPort F z.val e)) :=
                fun h => hd.2 (.inr h)
              simp only [sequentialStep, he, eraseService]
              rw [controlledPhysicalStep_normal_form, if_neg hn, hd.1]

theorem unshield_deletion_simulation (hpsi : psi > 0) (F : TwoLeaderFrame n) :
    SuccessSimulation (unshieldDeletionStep hpsi F) (controlledPhysicalStep hpsi F)
      (fun x y => eraseService hpsi F x = y) where
  terminal := by
    intro x y h
    rw [← h]
    cases x with
    | success => exact Nat.le_refl _
    | failure => exact Nat.le_refl _
    | active x => cases x <;> exact Nat.le_refl _
  next := by
    intro x y h e
    rw [← h]
    exact unshieldDeletionStep_erases hpsi F x e

/-- Actual controlled deletion mass from every gap pair.  No initial shield,
phase, rank, or entrance-service hypothesis is carried by this theorem. -/
theorem controlled_deletion_eighth (hpsi : psi > 0) (F : TwoLeaderFrame n)
    (b : (Fin n → AgentState psi)) (hg : WrapInvariant hpsi F b) :
    n ^ (2 * n * (2 * F.recovery.d + 14 * F.attack.d + 7)) ≤
      8 * successCount (controlledPhysicalStep hpsi F) (.active b)
        (2 * n * (2 * F.recovery.d + 14 * F.attack.d + 7)) := by
  let z : UnshieldState hpsi F := ⟨b, hg⟩
  let H := 2 * n * (2 * F.recovery.d + 1)
  let L := 2 * n * (14 * F.attack.d + 6)
  have hseq := sequential_mass (unshieldStep hpsi F) (controlledPhysicalStep hpsi F)
    (unshieldHandoff hpsi F) z H L 2 4 (unshield_half hpsi F z)
    (unshieldHandoff_quarter hpsi F)
  have hsim := successCount_le_of_simulation (unshieldDeletionStep hpsi F)
    (controlledPhysicalStep hpsi F) (fun x y => eraseService hpsi F x = y)
    (unshield_deletion_simulation hpsi F) (.active (.inl z)) (.active b) rfl (H + L)
  have htime : H + L = 2 * n * (2 * F.recovery.d + 14 * F.attack.d + 7) := by
    dsimp only [H, L]
    rw [← Nat.mul_add]
    congr 1
    omega
  change n ^ (H + L) ≤ 8 * successCount (unshieldDeletionStep hpsi F)
    (.active (.inl z)) (H + L) at hseq
  rw [htime] at hseq hsim
  exact Nat.le_trans hseq (Nat.mul_le_mul_left 8 hsim)

end K2TwoLeaderEntranceComposition

#print axioms K2TwoLeaderEntranceComposition.unshieldedBirthStep_erases
#print axioms K2TwoLeaderEntranceComposition.shotHandoff_half
#print axioms K2TwoLeaderEntranceComposition.birthShotStep_erases
#print axioms K2TwoLeaderEntranceComposition.unshielded_deletion_quarter
#print axioms K2TwoLeaderEntranceComposition.unshieldDeletionStep_erases
#print axioms K2TwoLeaderEntranceComposition.controlled_deletion_eighth
