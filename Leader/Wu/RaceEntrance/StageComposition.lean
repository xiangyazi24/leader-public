import Leader.Wu.RaceEntrance.ArrivalRaceMass

set_option autoImplicit false

open FiniteUniformStoppingTree PPLLRepair LDTwoGapFrame LDSinkTwoGapNoResetKernel
open LDSinkTwoGapDeletion LDSinkTwoGapDeletionWired

namespace LDSinkTwoGapRaceEntranceStageComposition

variable {n psi : Nat}

/-- Successful service leaves require real physical success.  A failed
service prefix is discarded and can relate to any ongoing physical state.
Active nodes retain exactly the physical configuration; ghost phase may differ. -/
def PhysicalLowerRel : StopNode (AState n psi) → StopNode (AState n psi) → Prop
  | .failure, _ => True
  | .success, .success => True
  | .active x, .active y => x.conf = y.conf
  | _, _ => False

theorem physical_lower_refl (x : StopNode (AState n psi)) : PhysicalLowerRel x x := by
  cases x <;> first | trivial | rfl

theorem physical_lower_trans {x y z : StopNode (AState n psi)}
    (hxy : PhysicalLowerRel x y) (hyz : PhysicalLowerRel y z) : PhysicalLowerRel x z := by
  cases x <;> cases y <;> cases z <;> simp_all [PhysicalLowerRel]

theorem physical_lower_next (hpsi : psi > 0) (F : TwoGapFrame n)
    (x y : StopNode (AState n psi)) (h : PhysicalLowerRel x y) (e : Fin n) :
    PhysicalLowerRel (stepNode (physicalBlockStep hpsi F) x e)
      (stepNode (physicalBlockStep hpsi F) y e) := by
  classical
  cases x <;> cases y <;> simp_all only [PhysicalLowerRel, stepNode]
  rename_i x y
  have hc : attemptStepConf hpsi F x e = attemptStepConf hpsi F y e := by
    simp only [attemptStepConf_eq_sinkStepC, h]
  rw [physicalBlockStep_normal_form, physicalBlockStep_normal_form, hc]
  by_cases hs : NoResetSuccess F (attemptStepConf hpsi F y e)
  · simp only [if_pos hs]
  · simp only [if_neg hs]
    exact hc

def serviceView {E : Type} (view : E → AState n psi)
    (handoff : E → Fin n → StopNode (AState n psi))
    (z : E) (e : Fin n) : StopNode E → StopNode (AState n psi)
  | .active y => .active (view y)
  | .success => handoff z e
  | .failure => .failure

def eraseStage {E : Type} (view : E → AState n psi) :
    StopNode (Sum E (AState n psi)) → StopNode (AState n psi)
  | .active (.inl z) => .active (view z)
  | .active (.inr b) => .active b
  | .success => .success
  | .failure => .failure

private theorem eraseStage_inRace {E : Type} (view : E → AState n psi)
    (x : StopNode (AState n psi)) : eraseStage view (inRace x) = x := by cases x <;> rfl

/-- The premise is only a literal one-edge alignment.  It carries no time,
probability, progress, or successful-leaf inequality. -/
theorem stage_simulation {E : Type} (hpsi : psi > 0) (F : TwoGapFrame n)
    (stage : E → Fin n → StopNode E) (view : E → AState n psi)
    (handoff : E → Fin n → StopNode (AState n psi))
    (halign : ∀ z e, PhysicalLowerRel (serviceView view handoff z e (stage z e))
      (physicalBlockStep hpsi F (view z) e)) :
    SuccessSimulation (sequentialStep stage (physicalBlockStep hpsi F) handoff)
      (physicalBlockStep hpsi F) (fun x y => PhysicalLowerRel (eraseStage view x) y) where
  terminal := by
    intro x y h
    cases x with
    | failure => exact Nat.zero_le _
    | active x => exact Nat.zero_le _
    | success => cases y <;> simp_all [eraseStage, PhysicalLowerRel, successWeight]
  next := by
    intro x y h e
    have hrow : PhysicalLowerRel
        (eraseStage view (stepNode (sequentialStep stage (physicalBlockStep hpsi F) handoff) x e))
        (stepNode (physicalBlockStep hpsi F) (eraseStage view x) e) := by
      cases x with
      | failure => trivial
      | success => trivial
      | active x =>
          cases x with
          | inr b =>
              change PhysicalLowerRel (eraseStage view (inRace _)) _
              rw [eraseStage_inRace]
              exact physical_lower_refl _
          | inl z =>
              have hh := halign z e
              cases he : stage z e with
              | active w =>
                  simpa only [stepNode, sequentialStep, he, serviceView, eraseStage] using hh
              | failure => simp only [stepNode, sequentialStep, he, eraseStage, PhysicalLowerRel]
              | success =>
                  change PhysicalLowerRel
                    (eraseStage view (sequentialStep stage (physicalBlockStep hpsi F) handoff (.inl z) e)) _
                  rw [sequentialStep, he, eraseStage_inRace]
                  simpa only [he, serviceView, stepNode, eraseStage] using hh
    exact physical_lower_trans hrow (physical_lower_next hpsi F (eraseStage view x) y h e)

/-- Compose proved finite service and handoff counts on the same original
physical scheduler tree, with failed service prefixes safely omitted. -/
theorem sequential_physical_mass {E : Type} (hpsi : psi > 0) (F : TwoGapFrame n)
    (stage : E → Fin n → StopNode E) (view : E → AState n psi)
    (handoff : E → Fin n → StopNode (AState n psi))
    (halign : ∀ z e, PhysicalLowerRel (serviceView view handoff z e (stage z e))
      (physicalBlockStep hpsi F (view z) e))
    (x : E) (H L p c : Nat)
    (hstage : n ^ H ≤ p * successCount stage (.active x) H)
    (hhandoff : ∀ z e, stage z e = .success →
      n ^ L ≤ c * successCount (physicalBlockStep hpsi F) (handoff z e) L) :
    n ^ (H + L) ≤ (p * c) * successCount (physicalBlockStep hpsi F) (.active (view x)) (H + L) := by
  have hm := sequential_mass stage (physicalBlockStep hpsi F) handoff x H L p c hstage hhandoff
  have hs := successCount_le_of_simulation (sequentialStep stage (physicalBlockStep hpsi F) handoff)
    (physicalBlockStep hpsi F) (fun x y => PhysicalLowerRel (eraseStage view x) y)
    (stage_simulation hpsi F stage view handoff halign)
    (.active (.inl x)) (.active (view x)) rfl (H + L)
  exact Nat.le_trans hm (Nat.mul_le_mul_left (p * c) hs)

theorem physical_mass_padding (hpsi : psi > 0) (F : TwoGapFrame n)
    (b : AState n psi) (T H K : Nat) (ht : T ≤ H)
    (hm : n ^ T ≤ K * successCount (physicalBlockStep hpsi F) (.active b) T) :
    n ^ H ≤ K * successCount (physicalBlockStep hpsi F) (.active b) H := by
  have hsum : T + (H - T) = H := by omega
  have hp := ThreePortSerialCount.success_padding (physicalBlockStep hpsi F) (.active b) T (H - T)
  rw [hsum] at hp
  calc
    n ^ H = n ^ (H - T) * n ^ T := by rw [← Nat.pow_add]; congr 1; omega
    _ ≤ n ^ (H - T) * (K * successCount (physicalBlockStep hpsi F) (.active b) T) :=
      Nat.mul_le_mul_left _ hm
    _ = K * (n ^ (H - T) * successCount (physicalBlockStep hpsi F) (.active b) T) :=
      Nat.mul_left_comm _ _ _
    _ ≤ K * successCount (physicalBlockStep hpsi F) (.active b) H := Nat.mul_le_mul_left K hp

end LDSinkTwoGapRaceEntranceStageComposition

#print axioms LDSinkTwoGapRaceEntranceStageComposition.stage_simulation
#print axioms LDSinkTwoGapRaceEntranceStageComposition.sequential_physical_mass
#print axioms LDSinkTwoGapRaceEntranceStageComposition.physical_mass_padding
