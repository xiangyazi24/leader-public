import Leader.Wu.RaceEntrance.LocalizedRecovery
import Leader.Wu.RaceEntrance.LocalizedFinish
import Leader.Wu.RaceEntrance.Localization
import Leader.Wu.RaceEntrance.BirthBudget

set_option autoImplicit false

open FiniteUniformStoppingTree PPLLRepair LDSinkGapCleanup LDTwoGapFrame LDSinkTwoGapNoResetKernel
open LDSinkTwoGapDeletionWired LDSinkTwoGapReachInvariant
open LDSinkTwoGapRaceEntranceLocalizedRecovery LDSinkTwoGapRaceEntranceLocalizedFinish
open LDSinkTwoGapRaceEntranceLocalization LDSinkTwoGapRaceEntranceStageComposition
open LDSinkTwoGapRaceEntranceBirthBudget LDSinkTwoGapRaceEntranceFreshService
open LDSinkTwoGapRaceEntranceTransit

namespace LDSinkTwoGapRaceEntranceLongMass

variable {n psi : Nat}

def finishTime (F : TwoGapFrame n) : Nat := 2 * n * (16 * F.recovery.d + 4)
def recoveryTime (F : TwoGapFrame n) : Nat := 8 * n * F.recovery.d
def localizationTime (F : TwoGapFrame n) : Nat := 2 * n * (F.attack.d - (16 * F.recovery.d + 1))
def birthTime (F : TwoGapFrame n) : Nat := 2 * n * (4 * F.attack.d + 1)

def finishDenominator : Nat := 4 * 2 ^ finishCollapseBudget
def recoveryDenominator : Nat := 2 * finishDenominator
def localizationDenominator : Nat := 2 * recoveryDenominator
def longDenominator : Nat := 2 * localizationDenominator

private theorem finish_denominator_pos : 0 < finishDenominator :=
  Nat.mul_pos (by decide) (Nat.pow_pos (by decide))

private theorem recovery_denominator_pos : 0 < recoveryDenominator :=
  Nat.mul_pos (by decide) finish_denominator_pos

private theorem localization_denominator_pos : 0 < localizationDenominator :=
  Nat.mul_pos (by decide) recovery_denominator_pos

private theorem success_node_mass (hpsi : psi > 0) (F : TwoGapFrame n) (T K : Nat) (hK : 0 < K) :
    n ^ T ≤ K * successCount (physicalBlockStep hpsi F) .success T := by
  simp only [successCount, treeWeight_success, successWeight, Nat.mul_one]
  have h := Nat.mul_le_mul_right (n ^ T) (show 1 ≤ K by omega)
  simpa only [Nat.one_mul] using h

private theorem alignment_from_rows {E : Type} (hpsi : psi > 0) (F : TwoGapFrame n)
    (stage : E → Fin n → StopNode E) (view : E → AState n psi)
    (handoff : E → Fin n → StopNode (AState n psi))
    (ha : ∀ z y e, stage z e = .active y →
      view y = postState hpsi F (view z) e ∧ ¬ NoResetSuccess F (attemptStepConf hpsi F (view z) e))
    (hh : ∀ z e, PhysicalLowerRel (handoff z e) (physicalBlockStep hpsi F (view z) e)) :
    ∀ z e, PhysicalLowerRel (serviceView view handoff z e (stage z e))
      (physicalBlockStep hpsi F (view z) e) := by
  intro z e
  cases he : stage z e with
  | success => exact hh z e
  | failure => trivial
  | active y =>
      have hd := ha z y e he
      simp only [serviceView]
      rw [physicalBlockStep_normal_form, if_neg hd.2]
      exact congrArg AState.conf hd.1

private theorem recovery_active_data (hpsi : psi > 0) (F : TwoGapFrame n) (q : Nat)
    (z y : RaceState hpsi F q) (e : Fin n) (he : raceStep hpsi F q z e = .active y) :
    y.raw.val = postState hpsi F z.raw.val e ∧ ¬ NoResetSuccess F (attemptStepConf hpsi F z.raw.val e) := by
  classical
  unfold raceStep at he
  split at he
  · cases he
  · rename_i hn
    split at he
    · cases he
    · exact ⟨congrArg (fun z => z.raw.val) (StopNode.active.inj he).symm, fun h => hn (.inr h)⟩

noncomputable def recoveryHandoff (hpsi : psi > 0) (F : TwoGapFrame n)
    (z : RaceState hpsi F (16 * F.recovery.d)) (e : Fin n) : StopNode (AState n psi) :=
  physicalBlockStep hpsi F z.raw.val e

theorem recovery_handoff_finish (hpsi : psi > 0) (F : TwoGapFrame n)
    (hb : 16 * F.recovery.d + 1 ≤ F.attack.d)
    (z : RaceState hpsi F (16 * F.recovery.d)) (e : Fin n)
    (he : raceStep hpsi F (16 * F.recovery.d) z e = .success) :
    n ^ finishTime F ≤ finishDenominator *
      successCount (physicalBlockStep hpsi F) (recoveryHandoff hpsi F z e) (finishTime F) := by
  classical
  have hp := success_payload hpsi F (16 * F.recovery.d) z e he
  unfold recoveryHandoff
  rw [physicalBlockStep_normal_form]
  by_cases hs : NoResetSuccess F (attemptStepConf hpsi F z.raw.val e)
  · rw [if_pos hs]
    exact success_node_mass hpsi F _ _ finish_denominator_pos
  · rw [if_neg hs]
    have h := hp.resolve_left hs
    exact localized_cleanReady_uniform_mass hpsi F
      ⟨postState hpsi F z.raw.val e, h.1⟩ (nextShotPosition F z.position e)
      (by have ht := h.2.2.1; omega) (Nat.le_trans h.2.2.2.1 hb)
      h.2.2.2.2 h.2.1 h.2.2.2.1

/-- Localization followed by the original-scheduler recovery race and the
proved physical finish.  Initial Ready is handed directly to the finish. -/
theorem localized_deletion_mass (hpsi : psi > 0) (F : TwoGapFrame n)
    (x : AActive hpsi F) (hb : 16 * F.recovery.d + 1 ≤ F.attack.d)
    (hl : (x.val.conf (F.attack.pos (16 * F.recovery.d + 1))).bullet = (2 : Fin 3)) :
    n ^ (recoveryTime F + finishTime F) ≤ recoveryDenominator *
      successCount (physicalBlockStep hpsi F) (.active x.val) (recoveryTime F + finishTime F) := by
  classical
  by_cases hr : CleanReady F.recovery x.val.conf
  · have hm := localized_cleanReady_uniform_mass hpsi F x (16 * F.recovery.d + 1)
      (by omega) hb hl hr (Nat.le_refl _)
    have hpad := physical_mass_padding hpsi F x.val (finishTime F)
      (recoveryTime F + finishTime F) finishDenominator (by omega) hm
    have hk : finishDenominator ≤ recoveryDenominator := by
      change finishDenominator ≤ 2 * finishDenominator
      rw [Nat.two_mul]
      exact Nat.le_add_right _ _
    exact Nat.le_trans hpad (Nat.mul_le_mul_right _ hk)
  · have hq : 0 < 16 * F.recovery.d := by have h := F.recovery.hd; omega
    let z : RaceState hpsi F (16 * F.recovery.d) :=
      ⟨x, 16 * F.recovery.d + 1, by omega, hb, Nat.le_refl _, hl, hr⟩
    have h5 := localized_success_five_eighths hpsi F x hb hl
    rw [initialRace, dif_neg hr] at h5
    have hm : n ^ recoveryTime F ≤
        2 * successCount (raceStep hpsi F (16 * F.recovery.d)) (.active z) (recoveryTime F) := by
      change 5 * n ^ recoveryTime F ≤
        8 * successCount (raceStep hpsi F (16 * F.recovery.d)) (.active z) (recoveryTime F) at h5
      omega
    exact sequential_physical_mass hpsi F (raceStep hpsi F (16 * F.recovery.d))
      (fun z => z.raw.val) (recoveryHandoff hpsi F)
      (alignment_from_rows hpsi F _ _ _ (recovery_active_data hpsi F _)
        (fun _ _ => physical_lower_refl _))
      z (recoveryTime F) (finishTime F) 2 finishDenominator hm (recovery_handoff_finish hpsi F hb)

noncomputable def localizationHandoff (hpsi : psi > 0) (F : TwoGapFrame n)
    (z : LocalState hpsi F (16 * F.recovery.d + 1)) (e : Fin n) : StopNode (AState n psi) :=
  physicalBlockStep hpsi F z.raw.val e

theorem localization_handoff_mass (hpsi : psi > 0) (F : TwoGapFrame n)
    (hb : 16 * F.recovery.d + 1 ≤ F.attack.d)
    (z : LocalState hpsi F (16 * F.recovery.d + 1)) (e : Fin n)
    (he : localStep hpsi F (16 * F.recovery.d + 1) (by have h := F.recovery.hd; omega) z e = .success) :
    n ^ (recoveryTime F + finishTime F) ≤ recoveryDenominator *
      successCount (physicalBlockStep hpsi F) (localizationHandoff hpsi F z e)
        (recoveryTime F + finishTime F) := by
  classical
  have hp := local_success_payload hpsi F (16 * F.recovery.d + 1)
    (by have h := F.recovery.hd; omega) z e he
  unfold localizationHandoff
  rw [physicalBlockStep_normal_form]
  by_cases hs : NoResetSuccess F (attemptStepConf hpsi F z.raw.val e)
  · rw [if_pos hs]
    exact success_node_mass hpsi F _ _ recovery_denominator_pos
  · rw [if_neg hs]
    have h := hp.resolve_left hs
    exact localized_deletion_mass hpsi F ⟨postState hpsi F z.raw.val e, h.1⟩ hb h.2

/-- Fresh birth has its real tagged live bullet at the attack shooter.
This theorem transports that same shot through localization and deletion. -/
theorem fresh_deletion_mass (hpsi : psi > 0) (F : TwoGapFrame n)
    (b : AState n psi) (hf : AttemptEntrance hpsi F b)
    (hlong : 16 * F.recovery.d + 2 ≤ F.attack.d) :
    n ^ (localizationTime F + (recoveryTime F + finishTime F)) ≤ localizationDenominator *
      successCount (physicalBlockStep hpsi F) (.active b)
        (localizationTime F + (recoveryTime F + finishTime F)) := by
  have hL : 2 ≤ 16 * F.recovery.d + 1 := by have h := F.recovery.hd; omega
  let z : LocalState hpsi F (16 * F.recovery.d + 1) :=
    ⟨⟨b, hf.1⟩, F.attack.d, by omega, Nat.le_refl _, hf.2.2⟩
  exact sequential_physical_mass hpsi F (localStep hpsi F (16 * F.recovery.d + 1) hL)
    (fun z => z.raw.val) (localizationHandoff hpsi F)
    (alignment_from_rows hpsi F _ _ _ (local_active_data hpsi F _ hL)
      (fun _ _ => physical_lower_refl _))
    z (localizationTime F) (recoveryTime F + finishTime F) 2 recoveryDenominator
    (localization_half hpsi F _ hL z) (localization_handoff_mass hpsi F (by omega))

def freshTag (b : AState n psi) : AState n psi := ⟨b.conf, .transit⟩

noncomputable def birthHandoff (hpsi : psi > 0) (F : TwoGapFrame n)
    (z : BirthState hpsi F) (e : Fin n) : StopNode (AState n psi) := by
  classical
  exact if NoResetSuccess F (attemptStepConf hpsi F z.val e) then .success
    else .active (freshTag (postState hpsi F z.val e))

private theorem birth_active_data (hpsi : psi > 0) (F : TwoGapFrame n)
    (z y : BirthState hpsi F) (e : Fin n) (he : birthStep hpsi F z e = .active y) :
    y.val = postState hpsi F z.val e ∧ ¬ NoResetSuccess F (attemptStepConf hpsi F z.val e) := by
  classical
  unfold birthStep at he
  split at he
  · cases he
  · rename_i hn
    exact ⟨congrArg Subtype.val (StopNode.active.inj he).symm, fun h => hn (.inr h)⟩

theorem birth_handoff_physical (hpsi : psi > 0) (F : TwoGapFrame n)
    (z : BirthState hpsi F) (e : Fin n) :
    PhysicalLowerRel (birthHandoff hpsi F z e) (physicalBlockStep hpsi F z.val e) := by
  classical
  unfold birthHandoff
  rw [physicalBlockStep_normal_form]
  by_cases hs : NoResetSuccess F (attemptStepConf hpsi F z.val e)
  · simp only [if_pos hs, PhysicalLowerRel]
  · simp only [if_neg hs, PhysicalLowerRel, freshTag]

theorem birth_handoff_mass (hpsi : psi > 0) (F : TwoGapFrame n)
    (hlong : 16 * F.recovery.d + 2 ≤ F.attack.d)
    (z : BirthState hpsi F) (e : Fin n) (he : birthStep hpsi F z e = .success) :
    n ^ (localizationTime F + (recoveryTime F + finishTime F)) ≤ localizationDenominator *
      successCount (physicalBlockStep hpsi F) (birthHandoff hpsi F z e)
        (localizationTime F + (recoveryTime F + finishTime F)) := by
  classical
  have hf : FreshOrDeleted hpsi F (attemptStepConf hpsi F z.val e) := by
    unfold birthStep at he
    split at he
    · assumption
    · cases he
  unfold birthHandoff
  by_cases hs : NoResetSuccess F (attemptStepConf hpsi F z.val e)
  · rw [if_pos hs]
    exact success_node_mass hpsi F _ _ localization_denominator_pos
  · rw [if_neg hs]
    exact fresh_deletion_mass hpsi F (freshTag (postState hpsi F z.val e)) (hf.resolve_right hs) hlong

def totalTime (F : TwoGapFrame n) : Nat :=
  birthTime F + (localizationTime F + (recoveryTime F + finishTime F))

/-- Original uniform physical deletion from an arbitrary long-ratio gap
pair.  Every source stage is independently produced and every handoff keeps
the actual configuration of the just-consumed scheduler interaction. -/
theorem gapPair_long_uniform_deletion_mass (hpsi : psi > 0) (F : TwoGapFrame n)
    (b : AState n psi) (hg : GapPair hpsi F b)
    (hlong : 16 * F.recovery.d + 2 ≤ F.attack.d) :
    n ^ totalTime F ≤ longDenominator * successCount (physicalBlockStep hpsi F) (.active b) (totalTime F) := by
  let z : BirthState hpsi F := ⟨b, hg⟩
  have hb := fresh_birth_half hpsi F b hg
  have he := successCount_erases hpsi F (.active z) (birthTime F)
  change successCount (birthStep hpsi F) (.active z) (birthTime F) =
    successCount (freshStep hpsi F) (.active b) (birthTime F) at he
  have hm : n ^ birthTime F ≤ 2 * successCount (birthStep hpsi F) (.active z) (birthTime F) := by
    rw [he]
    exact hb
  exact sequential_physical_mass hpsi F (birthStep hpsi F) Subtype.val (birthHandoff hpsi F)
    (alignment_from_rows hpsi F _ _ _ (birth_active_data hpsi F) (birth_handoff_physical hpsi F))
    z (birthTime F) (localizationTime F + (recoveryTime F + finishTime F)) 2 localizationDenominator
    hm (birth_handoff_mass hpsi F hlong)

theorem long_horizon_le_span (F : TwoGapFrame n)
    (hlong : 16 * F.recovery.d + 2 ≤ F.attack.d) :
    totalTime F ≤ 30 * n * (F.recovery.d + F.attack.d) := by
  have ha := F.recovery.hd
  have hb := F.attack.hd
  have hcoef : 2 * (4 * F.attack.d + 1) + 2 * (F.attack.d - (16 * F.recovery.d + 1)) +
      8 * F.recovery.d + 2 * (16 * F.recovery.d + 4) ≤ 30 * (F.recovery.d + F.attack.d) := by omega
  calc
    totalTime F = n * (2 * (4 * F.attack.d + 1) + 2 * (F.attack.d - (16 * F.recovery.d + 1)) +
        8 * F.recovery.d + 2 * (16 * F.recovery.d + 4)) := by
      simp only [totalTime, birthTime, localizationTime, recoveryTime, finishTime,
        Nat.mul_add, Nat.mul_assoc]
      ac_rfl
    _ ≤ n * (30 * (F.recovery.d + F.attack.d)) := Nat.mul_le_mul_left n hcoef
    _ = 30 * n * (F.recovery.d + F.attack.d) := by ac_rfl

theorem long_denominator_eq : longDenominator = 32 * 2 ^ finishCollapseBudget := by
  have h (q : Nat) : 2 * (2 * (2 * (4 * q))) = 32 * q := by omega
  exact h (2 ^ finishCollapseBudget)

/-- The long-ratio branch has constant actual deletion mass at the same
linear pair-span horizon used by the moderate-ratio branch. -/
theorem gapPair_long_uniform_at_span (hpsi : psi > 0) (F : TwoGapFrame n)
    (b : AState n psi) (hg : GapPair hpsi F b)
    (hlong : 16 * F.recovery.d + 2 ≤ F.attack.d) :
    n ^ (30 * n * (F.recovery.d + F.attack.d)) ≤ longDenominator *
      successCount (physicalBlockStep hpsi F) (.active b) (30 * n * (F.recovery.d + F.attack.d)) :=
  physical_mass_padding hpsi F b (totalTime F) _ longDenominator (long_horizon_le_span F hlong)
    (gapPair_long_uniform_deletion_mass hpsi F b hg hlong)

end LDSinkTwoGapRaceEntranceLongMass

#print axioms LDSinkTwoGapRaceEntranceLongMass.recovery_handoff_finish
#print axioms LDSinkTwoGapRaceEntranceLongMass.localized_deletion_mass
#print axioms LDSinkTwoGapRaceEntranceLongMass.localization_handoff_mass
#print axioms LDSinkTwoGapRaceEntranceLongMass.fresh_deletion_mass
#print axioms LDSinkTwoGapRaceEntranceLongMass.birth_handoff_physical
#print axioms LDSinkTwoGapRaceEntranceLongMass.gapPair_long_uniform_deletion_mass
#print axioms LDSinkTwoGapRaceEntranceLongMass.gapPair_long_uniform_at_span
