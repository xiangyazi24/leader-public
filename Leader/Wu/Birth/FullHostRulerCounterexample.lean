import Leader.Wu.Birth.FullHostCheckEntry
import Init.Data.Vector.OfFn

set_option autoImplicit false

namespace BirthFullHostRulerCounterexample

open PPLL PPLLResearchFormulation PPLLExpiringComparisonRepair
  PPLLNoCheckBirthOutputLegitimacy PPLLWallSweepPreCheckResetRepair
  PPLLPpsiLeaderCreationRepair

/-! The small-parameter birth regressions do not satisfy the state-budget
premise `psi <= kappa + 1`.  This module uses `psi = 2`, `kappa = 2`,
`tau = 16`, and a literal stable ruler on eight sites.  These values satisfy
that premise; no assertion is made about a not-yet-defined final `Param`.
The host here remains the exact named complete wall-sweep transition. -/

theorem ringEight : DirectedRing 8 := ⟨by omega⟩

/-- Relative to the leader at six, positive groups at zero, two, and four
have IDs zero, one, and zero: exactly `trailingZeros 1,2,3`.  Every auxiliary
register is initially neutral, including all comparison and writer paths. -/
def stableCore (i : Fin 8) : AgentState 2 :=
  { trapCore (by omega) i with leader := decide (i = 6), bit := decide (i = 3) }

theorem stableCore_domain (kappa : Nat) (i : Fin 8) :
    (stableCore i).inProtocolDomain kappa := by
  simpa [stableCore, AgentState.inProtocolDomain] using
    (trapCore_domain (κ := kappa) (by omega : 0 < 2) i)

def stableInitial (kappa tau : Nat) (i : Fin 8) :
    ExpiringAgentState 2 kappa tau :=
  ⟨⟨BoundedAgentState.ofDomain (stableCore i) (stableCore_domain kappa i),
    false⟩, ⟨0, Nat.zero_lt_succ tau⟩⟩

theorem erase_stableInitial (kappa tau : Nat) :
    eraseExpiringConfig (stableInitial kappa tau) = stableCore := by
  funext i
  change (BoundedAgentState.ofDomain (stableCore i)
    (stableCore_domain kappa i)).erase = stableCore i
  exact BoundedAgentState.erase_ofDomain _ (stableCore_domain kappa i)

theorem stableCore_unique : hasUniqueLeader 8 stableCore := by
  unfold hasUniqueLeader
  decide

theorem stableCore_ruler : isStableIDSequence (by omega) ringEight stableCore := by
  refine ⟨6, by decide, by decide, ?_, ?_⟩
  · intro k hk
    have hcases : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨
        k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 := by omega
    rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · intro i hi hbound
    have hcases : i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases hcases with rfl | rfl | rfl <;>
      simp [groupID, List.range_succ, stableCore, trailingZeros] <;> decide

private theorem stableCore_no_bad_bullet :
    noNonPeacefulBullet (by omega) ringEight stableCore := by
  have hnone : ∀ i : Fin 8, (stableCore i).bullet ≠ (⟨2, by omega⟩ : Fin 3) := by
    decide
  intro i hi
  exact False.elim (hnone i hi)

private theorem stableCore_no_free_writer :
    noFreeOverwritingSignal (by omega) ringEight stableCore := by
  have hnone : ∀ i : Fin 8, (stableCore i).path3 = none := by decide
  refine ⟨6, by decide, by decide, ?_⟩
  intro i _ _ hfree
  obtain ⟨p, hpath, _⟩ := hfree.1.2 0 (by decide)
  rw [hnone] at hpath
  cases hpath

/-- The input satisfies the actual five-field paper predicate, including the
stable ruler and absence of free overwriting signals. -/
theorem stableCore_paperSafe : PaperSafeConfig (by omega) ringEight stableCore where
  unique_leader := stableCore_unique
  no_nonpeaceful_bullet := stableCore_no_bad_bullet
  no_free_barrier := noFreeBarrier_of_stableID _ _ _ stableCore_ruler
  no_free_overwriting_signal := stableCore_no_free_writer
  stable_id_sequence := stableCore_ruler

theorem stableInitial_paperSafe (kappa tau : Nat) :
    PaperSafeConfig (by omega) ringEight
      (eraseExpiringConfig (stableInitial kappa tau)) := by
  rw [erase_stableInitial]
  exact stableCore_paperSafe

theorem stableInitial_quiescent (kappa tau : Nat) :
    isQuiescent ringEight (eraseExpiringConfig (stableInitial kappa tau)) := by
  rw [erase_stableInitial]
  unfold isQuiescent
  decide

/-- No interaction touches the original leader at six. -/
def rulerBirthSchedule : DetSchedule 8 :=
  [0, 0, 2, 1, 1, 2, 1, 1, 1, 2, 0, 1, 0, 1,
    1, 1, 0, 2, 1, 1, 1, 2, 1, 0, 1, 2, 2]

def stableAfter (kappa tau : Nat) : Fin 8 → ExpiringAgentState 2 kappa tau :=
  runLocalSchedule ringEight
    (wallSweepBirthSignalZeroPathStallTransition (by omega) kappa tau)
    (stableInitial kappa tau) rulerBirthSchedule

private theorem vector_get_ofFn {n : Nat} {Q : Type} (C : Fin n → Q) :
    (Vector.ofFn C).get = C := by
  funext i
  simp [Vector.get]
  apply congrArg C
  apply Fin.ext
  rfl

/-- Tabulation is an evaluation representation, not a protocol change. -/
private def vectorRun {n : Nat} {Q : Type} (ring : DirectedRing n)
    (T : Q → Q → Q × Q) : DetSchedule n → Vector Q n → Vector Q n
  | [], C => C
  | e :: rest, C => vectorRun ring T rest
      (Vector.ofFn (localStep ring T C.get e))

private theorem vectorRun_correct {n : Nat} {Q : Type} (ring : DirectedRing n)
    (T : Q → Q → Q × Q) (C : Fin n → Q) (word : DetSchedule n) :
    (vectorRun ring T word (Vector.ofFn C)).get =
      runLocalSchedule ring T C word := by
  induction word generalizing C with
  | nil => exact vector_get_ofFn C
  | cons e rest ih =>
      simp only [vectorRun, vector_get_ofFn, runLocalSchedule]
      exact ih _

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
/-- The exact host creates a second physical leader from the neutral stable
ruler at a parameter point satisfying `psi <= kappa + 1`. -/
theorem current_host_ruler_birth_kappa_two :
    (stableAfter 2 16 2).core.core.leader = true ∧
      (stableAfter 2 16 6).core.core.leader = true ∧
      (stableAfter 2 16 2).core.core.label = 0 ∧
      (stableAfter 2 16 2).core.core.signal_B = 0 := by
  unfold stableAfter
  rw [← vectorRun_correct]
  decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
theorem current_host_ruler_birth_kappa_three :
    (stableAfter 3 16 2).core.core.leader = true ∧
      (stableAfter 3 16 6).core.core.leader = true := by
  unfold stableAfter
  rw [← vectorRun_correct]
  decide

def stablePrefix (kappa tau : Nat) (t : Fin 28) :
    Fin 8 → ExpiringAgentState 2 kappa tau :=
  runLocalSchedule ringEight
    (wallSweepBirthSignalZeroPathStallTransition (by omega) kappa tau)
    (stableInitial kappa tau) (rulerBirthSchedule.take t.val)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 16000000 in
/-- Every prefix of the actual birth execution keeps all ruler bits and all
labels unchanged.  The counterexample does not rely on a source rewrite. -/
theorem current_host_ruler_prefix_bits_labels :
    ∀ t : Fin 28, ∀ i : Fin 8,
      (stablePrefix 2 16 t i).core.core.bit = (stableInitial 2 16 i).core.core.bit ∧
      (stablePrefix 2 16 t i).core.core.label = (stableInitial 2 16 i).core.core.label := by
  unfold stablePrefix
  simp only [← vectorRun_correct]
  decide

attribute [local irreducible] wallSweepBirthSignalZeroPathStallTransition

theorem stableAfter_not_unique :
    ¬ hasUniqueLeader 8 (eraseExpiringConfig (stableAfter 2 16)) := by
  rintro ⟨leader, _, honly⟩
  have htwo := honly 2 (by
    change (stableAfter 2 16 2).core.core.leader = true
    exact current_host_ruler_birth_kappa_two.1)
  have hsix := honly 6 (by
    change (stableAfter 2 16 6).core.core.leader = true
    exact current_host_ruler_birth_kappa_two.2.1)
  have hbad : (2 : Fin 8) = 6 := htwo.trans hsix.symm
  have hv := congrArg (fun i : Fin 8 => i.val) hbad
  omega

/-- Five-condition input safety fails under the exact complete host at the
explicit nonzero-counter parameter point. -/
theorem current_host_paperSafe_counterexample :
    PaperSafeConfig (by omega) ringEight
        (eraseExpiringConfig (stableInitial 2 16)) ∧
      ¬ PaperSafeConfig (by omega) ringEight
        (eraseExpiringConfig (stableAfter 2 16)) :=
  ⟨stableInitial_paperSafe 2 16,
    fun h => stableAfter_not_unique h.unique_leader⟩

/-- The full host does not preserve the actual paper predicate, even though
the initial comparison and writer registers are neutral and the entire
executed prefix leaves the stable ruler bits unchanged. -/
theorem current_host_not_closes_paperSafe :
    ¬ (∀ C : Fin 8 → ExpiringAgentState 2 2 16,
      PaperSafeConfig (by omega) ringEight (eraseExpiringConfig C) →
      ∀ e, PaperSafeConfig (by omega) ringEight
        (eraseExpiringConfig (localStep ringEight
          (wallSweepBirthSignalZeroPathStallTransition (by omega) 2 16) C e))) := by
  intro hclosed
  have hrun : ∀ word : DetSchedule 8,
      ∀ C : Fin 8 → ExpiringAgentState 2 2 16,
        PaperSafeConfig (by omega) ringEight (eraseExpiringConfig C) →
        PaperSafeConfig (by omega) ringEight
          (eraseExpiringConfig (runLocalSchedule ringEight
            (wallSweepBirthSignalZeroPathStallTransition (by omega) 2 16) C word)) := by
    intro word
    induction word with
    | nil => intros C hC; exact hC
    | cons e rest ih =>
        intro C hC
        exact ih _ (hclosed C hC e)
  exact current_host_paperSafe_counterexample.2
    (hrun rulerBirthSchedule (stableInitial 2 16) (stableInitial_paperSafe 2 16))

end BirthFullHostRulerCounterexample

#print axioms BirthFullHostRulerCounterexample.stableInitial_paperSafe
#print axioms BirthFullHostRulerCounterexample.current_host_ruler_birth_kappa_two
#print axioms BirthFullHostRulerCounterexample.current_host_ruler_birth_kappa_three
#print axioms BirthFullHostRulerCounterexample.current_host_ruler_prefix_bits_labels
#print axioms BirthFullHostRulerCounterexample.current_host_not_closes_paperSafe
