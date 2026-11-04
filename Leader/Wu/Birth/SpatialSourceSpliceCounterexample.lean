import Leader.Wu.Birth.SpatialSourceSpliceFixture
import Leader.Wu.Birth.SpatialSourceSpliceCertificate

set_option autoImplicit false

namespace BirthSpatialSourceSpliceCounterexample

open PPLL PPLLResearchFormulation PPLLAuthorizedComparisonRepair
  PPLLExpiringComparisonRepair PPLLPpsiLeaderCreationRepair PPLLLeaderCreationCleanupRepair
  PPLLNoCheckBirthOutputLegitimacy PPLLWallSweepFinite
  PPLLWallSweepRepair PPLLWallSweepPreCheckResetRepair
  BirthCheckCongestGuardRepair BirthMismatchDisposalProducer
  BirthGenerationControlRepair BirthTossCheckPreservationRepair
  BirthSingleUseReleaseRepair BirthReleaseTerminalInvariant

/-- Exact connection supplied by the sixty separately checked full-state rows.
This theorem changes no transition, initial configuration, or schedule. -/
private theorem runPrefix_eq_cert (t : Nat) :
    runPrefix t =
      (BirthSpatialSourceSpliceCertificate.certPrefix t).get :=
  (BirthSpatialSourceSpliceCertificate.certPrefix_correct t).symm

/-- Exactly two actual GEN events write the two different source words.
There is no later writer, including same-value overwrite or refill. -/
theorem exactly_two_real_generation_events :
    schedule.length = 60 ∧
      observedWrites 7 10 = (true, true) ∧ observedWrites 15 6 = (true, true) ∧
      (runPrefix 8 10).core.core.path = .some 0 0 ∧
      (runPrefix 8 11).core.core.path = .some 1 1 ∧
      (runPrefix 16 6).core.core.path = .some 0 1 ∧
      (runPrefix 16 7).core.core.path = .some 1 0 ∧
      (∀ k : Fin 60, k.val ≠ 7 → k.val ≠ 15 →
        observedWrites k.val schedule[k.val] = (false, false)) := by
  unfold observedWrites
  simp only [runPrefix_eq_cert]
  decide

/-- The two zero-valued components really expire on edge nine, with the
positive and zero timer cuts displayed. The two one-valued survivors are
untouched by that service interval. -/
theorem actual_expiry_selects_two_different_source_bits :
    (runPrefix 36 9).core.core.path = .some 1 0 ∧ (runPrefix 36 9).stall.val = 1 ∧
      (runPrefix 37 9).core.core.path = .some 1 0 ∧ (runPrefix 37 9).stall.val = 0 ∧
      (runPrefix 38 9).core.core.path = .bot ∧
      (runPrefix 39 10).core.core.path = .some 0 0 ∧ (runPrefix 39 10).stall.val = 1 ∧
      (runPrefix 40 10).core.core.path = .some 0 0 ∧ (runPrefix 40 10).stall.val = 0 ∧
      (runPrefix 41 10).core.core.path = .bot ∧
      (∀ t : Fin 18,
        (runPrefix (24 + t.val) 8).core.core.path = .some 0 1 ∧
          (runPrefix (24 + t.val) 11).core.core.path = .some 1 1) := by
  simp only [runPrefix_eq_cert]
  decide

/-- The source-ten terminal retains its real GEN depart phase when a foreign
zero arrives. Backward departure propagation then demotes the newly ready
zero before CHECK, without any action-five token. -/
theorem distinct_source_components_join_under_departure :
    (runPrefix 43 10).core.core.path = .some 0 1 ∧
      (runPrefix 43 10).core.core.state = .CHECK_ready ∧
      (runPrefix 43 11).core.core.path = .some 1 1 ∧
      (runPrefix 43 11).core.core.state = .depart ∧
      (runPrefix 43 10).core.erase.core.path2 = none ∧
      (runPrefix 43 11).core.erase.core.path2 = none ∧
      (beforeCheck 43 10).1.core.state = .depart ∧
      (afterCheck 43 10).1.core.state = .depart ∧
      (runPrefix 44 10).core.core.state = .congest ∧
      (runPrefix 44 11).core.core.state = .congest := by
  unfold afterCheck beforeCheck
  simp only [runPrefix_eq_cert]
  decide

/-- The mixed word performs a genuine less comparison and obtains a new
release at the next smaller group, then arrives freshly ready at the peak. -/
theorem mixed_word_really_compares_and_releases :
    (runPrefix 51 12).core.core.path = .some 0 1 ∧
      (runPrefix 51 13).core.core.path = .some 1 1 ∧
      (afterCheck 51 12).1.core.state = .less ∧
      (afterCheck 51 12).1.core.path2 = some ⟨0, 0, 0, 6⟩ ∧
      (runPrefix 53 12).core.core.state = .toss ∧
      (runPrefix 54 12).core.core.state = .toss_done ∧
      (runPrefix 54 12).core.erase.core.path2 = some ⟨0, 0, 0, 5⟩ ∧
      (runPrefix 55 13).core.core.state = .depart ∧
      (runPrefix 55 13).core.erase.core.path2 = none ∧
      (runPrefix 59 14).core.core.path = .some 0 1 ∧
      (runPrefix 59 15).core.core.path = .some 1 1 ∧
      (runPrefix 59 14).core.core.state = .CHECK_ready ∧
      (runPrefix 59 15).core.core.state = .CHECK_ready ∧
      (runPrefix 59 14).core.erase.core.path2 = none ∧
      (runPrefix 59 15).core.erase.core.path2 = none := by
  unfold afterCheck beforeCheck
  simp only [runPrefix_eq_cert]
  decide

set_option maxRecDepth 16384 in
set_option maxHeartbeats 24000000 in
/-- The full last transition really creates a second leader from the mixed
word's equal CHECK. WRITE migrates the new responder leader to fourteen. -/
theorem mixed_word_causes_second_leader :
    (afterCheck 59 14).1.core.state = .equal ∧
      (afterCheck 59 14).2.core.state = .equal ∧
      (afterCheck 59 14).2.core.leader = true ∧
      (∀ i : Fin 32, (runPrefix 60 i).core.core.leader = true ↔ i = 14 ∨ i = 30) := by
  unfold afterCheck beforeCheck
  simp only [runPrefix_eq_cert]
  decide

/-- Every preceding state retains exactly the old leader, and all sixty
interactions preserve every resident ruler bit and label. -/
theorem all_prefixes_keep_ruler_bits_labels_and_old_leader :
    (∀ t : Fin 60, ∀ i : Fin 32, (runPrefix t.val i).core.core.leader = true ↔ i = 30) ∧
      (∀ t : Fin 61, ∀ i : Fin 32,
        (runPrefix t.val i).core.core.label = (initial i).core.core.label ∧
          (runPrefix t.val i).core.core.bit = (initial i).core.core.bit) := by
  simp only [runPrefix_eq_cert]
  decide

/-- The whole execution satisfies the general terminal-five invariant.
Its violation of safety is therefore compatible with genuine single-use
control consumption on every interaction. -/
theorem all_prefixes_have_no_terminal_five (t : Nat) :
    ∀ i : Fin 32, NoTerminalFive (runPrefix t i).core.erase.core := by
  apply empty_control_run_no_terminal_five ringThirtyTwo twoPositive (by decide) 2 16 initial
  intro i
  rfl

#print axioms initial_paperSafe
#print axioms initial_empty_with_distinct_source_ids
#print axioms exactly_two_real_generation_events
#print axioms actual_expiry_selects_two_different_source_bits
#print axioms distinct_source_components_join_under_departure
#print axioms mixed_word_really_compares_and_releases
#print axioms mixed_word_causes_second_leader
#print axioms all_prefixes_keep_ruler_bits_labels_and_old_leader
#print axioms all_prefixes_have_no_terminal_five

end BirthSpatialSourceSpliceCounterexample
