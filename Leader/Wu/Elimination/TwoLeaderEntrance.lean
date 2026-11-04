import Leader.Wu.Elimination.TwoLeaderEntranceMass

/-!
Uniform physical entrance/deletion for the final two separated leaders.
The real canonical two-gap layout is rotated so that its shorter gap is the
attack.  Its gaps sum to n and its two outer endpoints are the same agent.
The theorem below starts from the actual GlobalClass count-two state, with
no initial readiness, unshielding, fresh shot, or event-budget assumption.

The conclusion is a first hit of physical leader count one under the original
uniform K2 scheduler.  It does not assert terminal semantic safety, handle
adjacent leaders, or supply the rest of a protocol stabilization theorem.
-/

set_option autoImplicit false

open FiniteUniformStoppingTree PPLLRepair
open K2OutputSafety K2GlobalGapClosure
open K2TwoLeaderGeometry K2TwoLeaderEntranceCore K2TwoLeaderEntranceMass

namespace K2TwoLeaderEntrance

variable {n ψ : Nat}

/-- Every service uses this identical K2 row on the original n-agent ring.
Choosing or rotating a proof frame cannot change a physical register. -/
theorem original_step_eq_actual (hψ : 0 < ψ) (ring : DirectedRing n)
    (F : TwoLeaderFrame n) :
    originalPhysicalStep hψ F = K2TwoLeaderGeometry.physicalStep hψ ring F := by
  classical
  funext C e
  rw [originalPhysicalStep_normal_form, rawConf_eq_rawStep hψ ring F C e]
  rfl

/-- An observed deletion is a real first reduction from two leaders to one.
The surviving endpoint is the same outer agent on both complementary gaps. -/
theorem endpoint_deletion_is_countOne (hψ : 0 < ψ) (ring : DirectedRing n)
    (F : TwoLeaderFrame n) (C : Fin n → AgentState ψ) (hs : TwoLeaderSupport F C)
    (e : Fin n) (hd : Deleted F (rawStep hψ ring C e)) :
    physicalLeaderCount (rawStep hψ ring C e) = 1 := by
  rcases support_step hψ ring F C hs e with h | h
  · exact h.2
  · exact (h.1 hd).elim

/-- A physical GapPair-like entry on the complementary geometry: all
readiness, shield, and bullet registers may be arbitrary subject to the two
actual gap invariants.  Its fixed horizon is 20*n². -/
theorem wrap_countOne_mass (hψ : 0 < ψ) (ring : DirectedRing n)
    (F : TwoLeaderFrame n) (C : Fin n → AgentState ψ)
    (hg : WrapInvariant hψ F C) (hs : TwoLeaderSupport F C)
    (ho : F.attack.d ≤ F.recovery.d) :
    n ^ (20 * n * n) ≤ (16 * 2 ^ uniformCollapseBudget) *
      successCount (countOneStep hψ ring) (.active C) (20 * n * n) := by
  have hm := uniform_deletion_at_square hψ F C hg ho
  rw [original_step_eq_actual hψ ring F] at hm
  exact Nat.le_trans hm (Nat.mul_le_mul_left _
    (endpoint_count_le_countOne hψ ring F C hs (20 * n * n)))

/-- Constant original-scheduler count-one hitting mass from the actual
separated count-two global class.  The denominator is the absolute constant
16*2^1263; shorter-attack ordering is proved by canonical frame selection. -/
theorem globalClass_countOne_mass (hψ : 0 < ψ) (ring : DirectedRing n)
    (C : Fin n → AgentState ψ) (hC : GlobalClass hψ ring 2 C) :
    n ^ (20 * n * n) ≤ (16 * 2 ^ uniformCollapseBudget) *
      successCount (countOneStep hψ ring) (.active C) (20 * n * n) := by
  let F := orderedCanonical hψ ring C hC
  have hd := orderedCanonical_data hψ ring C hC
  exact wrap_countOne_mass hψ ring F C hd.1 hd.2.1 hd.2.2.1

/-- Nonempty initially shielded, nonready domain on the minimal separated
four-agent ring.  This is only a domain witness; the mass theorem is uniform. -/
def shieldedSeed4 (i : Fin 4) : AgentState 1 :=
  { seed4Start i with shield := true }

theorem shieldedSeed4_class : GlobalClass (by decide) ⟨by decide⟩ 2 shieldedSeed4 := by
  refine ⟨by decide, by decide, ?_⟩
  apply global_of_signals_zero
  · unfold Separated
    decide
  · exact cyclicLabels_one _ _
  · intro i
    rfl

theorem shieldedSeed4_initial_fields :
    (∀ i, (shieldedSeed4 i).shield = true) ∧
    (∀ F : TwoLeaderFrame 4, ¬ RaceReady F shieldedSeed4) := by
  refine ⟨fun _ => rfl, ?_⟩
  intro F h
  have hz : (0 : Fin 2) = 1 := h.2
  cases hz

end K2TwoLeaderEntrance

#print axioms K2TwoLeaderEntranceCore.orderedCanonical_data
#print axioms K2TwoLeaderEntranceCore.prepare_frames_attack
#print axioms K2TwoLeaderEntranceCore.controlled_shield_closed
#print axioms K2TwoLeaderEntranceUnshield.original_unshield_quarter
#print axioms K2TwoLeaderEntranceBirth.birthEvent_produces_fresh
#print axioms K2TwoLeaderEntranceShot.shotStep_erases
#print axioms K2TwoLeaderEntranceComposition.birthShotStep_erases
#print axioms K2TwoLeaderEntranceComposition.unshieldDeletionStep_erases
#print axioms K2TwoLeaderEntranceComposition.controlled_deletion_eighth
#print axioms K2TwoLeaderEntranceBudget.budgetStep_erases
#print axioms K2TwoLeaderEntranceMass.physical_audit_failure_sixteenth
#print axioms K2TwoLeaderEntranceMass.uniform_deletion_at_square
#print axioms K2TwoLeaderEntrance.original_step_eq_actual
#print axioms K2TwoLeaderEntrance.endpoint_deletion_is_countOne
#print axioms K2TwoLeaderEntrance.wrap_countOne_mass
#print axioms K2TwoLeaderEntrance.globalClass_countOne_mass
#print axioms K2TwoLeaderEntrance.shieldedSeed4_class
#print axioms K2TwoLeaderEntrance.shieldedSeed4_initial_fields
#check K2TwoLeaderEntrance.globalClass_countOne_mass
