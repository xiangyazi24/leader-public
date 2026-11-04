import Leader.Wu.Safety.PermitRepairQuietLap
import Leader.Wu.Safety.SafeConfig

set_option autoImplicit false
set_option Elab.async false

private theorem h3 : (3 : Nat) > 0 := by
  decide

/-- Exact raw erasure of `R1CandidateKernel.witness`. -/
private def clean9 : Fin 9 → AgentState 3 :=
  fun i => (R1CandidateKernel.witness i).core.core.erase

/- Condition 1: exactly site zero is a leader. -/
private theorem clean9_unique_leader :
    hasUniqueLeader 9 clean9 := by
  unfold hasUniqueLeader
  decide +kernel

/-- The clean witness has no live bullet at any site. -/
private theorem clean9_bullet_zero (i : Fin 9) :
    (clean9 i).bullet.val = 0 := by
  rfl

/-- Condition 2: vacuous because every bullet is zero. -/
private theorem clean9_no_nonpeaceful_bullet :
    noNonPeacefulBullet h3 R1CandidateKernel.witnessRing clean9 := by
  intro i hLive
  have hTwo : (clean9 i).bullet.val = 2 := congrArg Fin.val hLive
  rw [clean9_bullet_zero i] at hTwo
  omega

/- Condition 3 is a closed finite check on the nine directed edges. -/
private theorem clean9_no_free_barrier :
    noFreeBarrier h3 R1CandidateKernel.witnessRing clean9 := by
  unfold noFreeBarrier isBarrier
  decide +kernel

/-- Every path3 carrier is absent in the clean fixture. -/
private theorem clean9_path3_none (i : Fin 9) :
    (clean9 i).path3 = none := by
  rfl

/-- Condition 4: root at zero; a complete aligned overwriting signal is
impossible because even its offset-zero path3 component is absent. -/
private theorem clean9_no_free_overwriting_signal :
    noFreeOverwritingSignal h3 R1CandidateKernel.witnessRing clean9 := by
  refine ⟨0, by decide +kernel, by decide +kernel, ?_⟩
  intro i _hi _hbound hFree
  obtain ⟨_, hAligned⟩ := hFree.1
  obtain ⟨p, hPath, _⟩ := hAligned 0 (by omega)
  rw [clean9_path3_none] at hPath
  contradiction

/- Condition 5: labels are 0,1,2 periodically; the two positive full groups
have IDs 000=0 and 001=1, matching trailingZeros 1 and trailingZeros 2. -/
private theorem clean9_stable_id_sequence :
    isStableIDSequence h3 R1CandidateKernel.witnessRing clean9 := by
  refine ⟨0, by decide +kernel, by decide +kernel, ?_, ?_⟩
  · intro k hk
    have hkCases :
        k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨
        k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 := by
      omega
    rcases hkCases with h | h | h | h | h | h | h | h | h <;>
      subst k <;> decide +kernel
  · intro i hi hbound
    have hi12 : i = 1 ∨ i = 2 := by
      omega
    rcases hi12 with h | h
    · subst i
      decide +kernel
    · subst i
      decide +kernel

/-- The exact n=9 rooted clean start satisfies all five paper fields. -/
theorem clean9_paperSafe :
    PaperSafeConfig (by decide : (3 : Nat) > 0)
      R1CandidateKernel.witnessRing
      (fun i => (R1CandidateKernel.witness i).core.core.erase) := by
  change PaperSafeConfig h3 R1CandidateKernel.witnessRing clean9
  exact
    { unique_leader := clean9_unique_leader
      no_nonpeaceful_bullet := clean9_no_nonpeaceful_bullet
      no_free_barrier := clean9_no_free_barrier
      no_free_overwriting_signal := clean9_no_free_overwriting_signal
      stable_id_sequence := clean9_stable_id_sequence }

/-- The paper-safe certificate immediately yields the output-safety kernel. -/
theorem clean9_outputSafe :
    OutputSafeConfig (by decide : (3 : Nat) > 0)
      R1CandidateKernel.witnessRing
      (fun i => (R1CandidateKernel.witness i).core.core.erase) := by
  exact PaperSafeConfig.toOutputSafe clean9_paperSafe

-- Do not execute the fixture through whnf in any later proof in this file.
attribute [local irreducible] clean9 R1CandidateKernel.witness
