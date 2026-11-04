import Leader.Wu.Safety.NoCheckBirthConditionThreeProtocol

/-!
# Exact condition-4 regression for the no-CHECK-birth repair

Wu's interpreted condition 4 constrains complete aligned overwriting signals,
but does not constrain an almost-complete carrier or a pending non-increment
write command.  On a stable `ψ = 3`, `n = 9` ring, a forged `move_flip` at the
terminal component changes the only zero flag to one.  The resulting complete
flag-one signal has payload zero inside positive group two, whose stable ID is
one, and is therefore free.  This happens in the same exact packaged finite
protocol used by corrected conditions 1--3; the increment-only prepared gate
does not inspect `move_flip`.
-/

namespace PPLLNoCheckBirthConditionFourRegression

open PPLL PPLLRepair PPLLNoCheckBirthRepair
  PPLLExpiringComparisonRepair PPLLAuthorizedComparisonRepair
  PPLLNoCheckBirthPhysicalConditionOne
  PPLLNoCheckBirthConditionTwoPhysical
  PPLLNoCheckBirthConditionTwoProtocol
  PPLLNoCheckBirthConditionThreeProtocol

set_option linter.defProp false

theorem hThree : 3 > 0 := by omega

theorem ringNine : DirectedRing 9 := ⟨by omega⟩

private theorem finNine_cases (i : Fin 9) :
    i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨
      i = 6 ∨ i = 7 ∨ i = 8 := by
  have h : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ i.val = 3 ∨
      i.val = 4 ∨ i.val = 5 ∨ i.val = 6 ∨ i.val = 7 ∨ i.val = 8 := by
    omega
  rcases h with h | h | h | h | h | h | h | h | h
  · exact .inl (Fin.ext h)
  · exact .inr (.inl (Fin.ext h))
  · exact .inr (.inr (.inl (Fin.ext h)))
  · exact .inr (.inr (.inr (.inl (Fin.ext h))))
  · exact .inr (.inr (.inr (.inr (.inl (Fin.ext h)))))
  · exact .inr (.inr (.inr (.inr (.inr (.inl (Fin.ext h))))))
  · exact .inr (.inr (.inr (.inr (.inr (.inr (.inl (Fin.ext h)))))))
  · exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl (Fin.ext h))))))))
  · exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (Fin.ext h))))))))

private def baseView (i : Fin 9) : PeaceView 3 :=
  { leader := decide (i.val = 0)
    label := ⟨i.val % 3, by omega⟩
    shield := false
    bullet := ⟨0, by omega⟩
    signal_B := ⟨0, by omega⟩ }

/-- Stable core configuration with an almost-complete group-two path3 signal.
The terminal component is the only one whose flag is zero, and carries the
forged `move_flip` command. -/
def conditionFourCoreConfig (i : Fin 9) : AgentState 3 :=
  let u := PeaceView.toState (baseView i)
  let u := if i.val = 8 then { u with bit := true } else u
  let u := if i.val = 6 then { u with path3 := some ⟨0, 0, 1⟩ } else u
  let u := if i.val = 7 then { u with path3 := some ⟨1, 0, 1⟩ } else u
  if i.val = 8 then
    { u with path3 := some ⟨2, 0, 0⟩, write := .move_flip }
  else u

/-- Every raw field of the regression lies in the declared finite domain. -/
theorem conditionFourCore_inProtocolDomain (i : Fin 9) :
    (conditionFourCoreConfig i).inProtocolDomain 10 := by
  by_cases h8 : i.val = 8
  · simp [conditionFourCoreConfig, PeaceView.toState, baseView,
      AgentState.inProtocolDomain, h8]
  · by_cases h7 : i.val = 7
    · simp [conditionFourCoreConfig, PeaceView.toState, baseView,
        AgentState.inProtocolDomain, h7]
    · by_cases h6 : i.val = 6
      · simp [conditionFourCoreConfig, PeaceView.toState, baseView,
          AgentState.inProtocolDomain, h6]
      · simp [conditionFourCoreConfig, PeaceView.toState, baseView,
          AgentState.inProtocolDomain, h8, h7, h6]

/-- Exact finite reification, with false authorization and the sole `τ=0`
timer value. -/
def conditionFourFiniteConfig (i : Fin 9) : ExpiringAgentState 3 10 0 :=
  ⟨⟨BoundedAgentState.ofDomain (conditionFourCoreConfig i)
      (conditionFourCore_inProtocolDomain i), false⟩, ⟨0, by omega⟩⟩

/-- The scheduled edge flips the terminal signal flag. -/
def conditionFourEdge : Fin 9 := ⟨7, by omega⟩

/-- Exact successor under the packaged finite no-CHECK-birth protocol. -/
def conditionFourFiniteAfter : Fin 9 → ExpiringAgentState 3 10 0 :=
  (noCheckBirthProtocol hThree 10 0).step
    ringNine conditionFourFiniteConfig conditionFourEdge

/-- Erasing the exact finite input recovers the displayed raw witness. -/
theorem erase_conditionFourFiniteConfig :
    eraseExpiringConfig conditionFourFiniteConfig = conditionFourCoreConfig := by
  funext i
  change BoundedAgentState.erase
    (BoundedAgentState.ofDomain (conditionFourCoreConfig i)
      (conditionFourCore_inProtocolDomain i)) = conditionFourCoreConfig i
  exact BoundedAgentState.erase_ofDomain _ _

private theorem conditionFour_unique :
    hasUniqueLeader 9 conditionFourCoreConfig := by
  refine ⟨0, by decide, ?_⟩
  intro i hi
  rcases finNine_cases i with h | h | h | h | h | h | h | h | h <;>
    subst i <;> simp [conditionFourCoreConfig, PeaceView.toState, baseView,
      AgentState.isLeader] at hi ⊢

private theorem conditionFour_no_bad_bullet :
    noNonPeacefulBullet hThree ringNine conditionFourCoreConfig := by
  intro i hLive
  rcases finNine_cases i with h | h | h | h | h | h | h | h | h <;>
    subst i <;>
    simp [conditionFourCoreConfig, PeaceView.toState, baseView] at hLive

private theorem conditionFourCore_path3_three :
    (conditionFourCoreConfig 3).path3 = none := by
  rfl

private theorem conditionFourCore_path3_eight :
    (conditionFourCoreConfig 8).path3 = some ⟨2, 0, 0⟩ := by
  rfl

private theorem conditionFour_no_free_overwriting :
    noFreeOverwritingSignal hThree ringNine conditionFourCoreConfig := by
  refine ⟨0, by decide, by decide, ?_⟩
  intro i hi hbound hfree
  have hi12 : i = 1 ∨ i = 2 := by omega
  rcases hi12 with hi1 | hi2
  · subst i
    obtain ⟨_, haligned⟩ := hfree.1
    obtain ⟨p, hpath, _⟩ := haligned 0 (by omega)
    change (conditionFourCoreConfig 3).path3 = some p at hpath
    rw [conditionFourCore_path3_three] at hpath
    contradiction
  · subst i
    obtain ⟨_, haligned⟩ := hfree.1
    obtain ⟨p, hpath, _, _, hflag⟩ := haligned 2 (by omega)
    change (conditionFourCoreConfig 8).path3 = some p at hpath
    rw [conditionFourCore_path3_eight] at hpath
    cases hpath
    simp at hflag

private theorem conditionFour_stable_id :
    isStableIDSequence hThree ringNine conditionFourCoreConfig := by
  refine ⟨0, by decide, by decide, ?_, ?_⟩
  · intro k hk
    have hkCases : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨
        k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 := by omega
    rcases hkCases with h | h | h | h | h | h | h | h | h <;>
      subst k <;> decide
  · intro i hi hbound
    have hi12 : i = 1 ∨ i = 2 := by omega
    rcases hi12 with h | h
    · subst i
      dsimp only
      change groupID ringNine.hn conditionFourCoreConfig 3 = trailingZeros 1
      have hval : (3 : Fin 9).val = 3 := rfl
      simp [groupID, List.range_succ, conditionFourCoreConfig,
        PeaceView.toState, baseView, trailingZeros, hval]
    · subst i
      dsimp only
      change groupID ringNine.hn conditionFourCoreConfig 6 = trailingZeros 2
      have hval : (6 : Fin 9).val = 6 := rfl
      simp [groupID, List.range_succ, conditionFourCoreConfig,
        PeaceView.toState, baseView, trailingZeros, hval]

private theorem conditionFour_no_free_barrier :
    noFreeBarrier hThree ringNine conditionFourCoreConfig :=
  noFreeBarrier_of_stableID hThree ringNine conditionFourCoreConfig
    conditionFour_stable_id

/-- The regression input satisfies all five fields of `PaperSafeConfig`. -/
theorem conditionFourCore_paperSafe :
    PaperSafeConfig hThree ringNine conditionFourCoreConfig where
  unique_leader := conditionFour_unique
  no_nonpeaceful_bullet := conditionFour_no_bad_bullet
  no_free_barrier := conditionFour_no_free_barrier
  no_free_overwriting_signal := conditionFour_no_free_overwriting
  stable_id_sequence := conditionFour_stable_id

/-- The exact output retains the complete payload-zero path and flips the sole
terminal flag to one. -/
theorem conditionFourAfter_path_fields :
    let D := eraseExpiringConfig conditionFourFiniteAfter
    (D 6).path3 = some ⟨0, 0, 1⟩ ∧
      (D 7).path3 = some ⟨1, 0, 1⟩ ∧
      (D 8).path3 = some ⟨2, 0, 1⟩ := by
  decide

/-- The newly completed signal is free at positive group two: its ID is zero,
its stable group ID is one, and `trailingZeros 2 = 1`. -/
theorem conditionFourAfter_free_signal :
    isFreeOverwritingSignalAt ringNine
      (eraseExpiringConfig conditionFourFiniteAfter) 0 2 := by
  let D := eraseExpiringConfig conditionFourFiniteAfter
  change isAlignedOverwritingSignalAt ringNine D 6 1 ∧
    overwritingSignalIDAt ringNine D 6 ≠ trailingZeros 2 ∧
    groupID ringNine.hn D 6 > overwritingSignalIDAt ringNine D 6
  have hpaths := conditionFourAfter_path_fields
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨by omega, ?_⟩
    intro k hk
    have hkCases : k = 0 ∨ k = 1 ∨ k = 2 := by omega
    rcases hkCases with h | h | h <;> subst k
    · refine ⟨⟨0, 0, 1⟩, ?_, rfl, by decide, rfl⟩
      have hoff : groupOffset ringNine (6 : Fin 9) 0 = 6 := by rfl
      rw [hoff]
      exact hpaths.1
    · refine ⟨⟨1, 0, 1⟩, ?_, rfl, by decide, rfl⟩
      have hoff : groupOffset ringNine (6 : Fin 9) 1 = 7 := by rfl
      rw [hoff]
      exact hpaths.2.1
    · refine ⟨⟨2, 0, 1⟩, ?_, rfl, by decide, rfl⟩
      have hoff : groupOffset ringNine (6 : Fin 9) 2 = 8 := by rfl
      rw [hoff]
      exact hpaths.2.2
  · have hid : overwritingSignalIDAt ringNine D 6 = 0 := by decide
    have htz1 : trailingZeros 1 = 0 :=
      trailingZeros_of_odd 1 (by omega) (by omega)
    have htz : trailingZeros 2 = 1 := by
      have h := trailingZeros_of_even 2 (by omega) (by omega)
      have hdiv : 2 / 2 = 1 := by decide
      rw [hdiv, htz1] at h
      omega
    rw [hid, htz]
    omega
  · have hgroup : groupID ringNine.hn D 6 = 1 := by decide
    have hid : overwritingSignalIDAt ringNine D 6 = 0 := by decide
    rw [hgroup, hid]
    omega

/-- Corrected condition 4 is not preserved by the current exact finite repair.
The witness is PaperSafe before the step and has a free overwriting signal
after the step. -/
theorem noCheckBirthProtocol_conditionFour_counterexample :
    PaperSafeConfig hThree ringNine
        (eraseExpiringConfig conditionFourFiniteConfig) ∧
      ¬noFreeOverwritingSignal hThree ringNine
        (eraseExpiringConfig conditionFourFiniteAfter) := by
  constructor
  · rw [erase_conditionFourFiniteConfig]
    exact conditionFourCore_paperSafe
  · intro hsafe
    obtain ⟨leaderPos, hleader, _, hnone⟩ := hsafe
    have hleaderInput : (conditionFourCoreConfig leaderPos).isLeader := by
      have heq := noCheckBirthProtocol_step_leader_eq hThree 10 0
        ringNine conditionFourFiniteConfig
        (erase_conditionFourFiniteConfig ▸ conditionFourCore_paperSafe)
        conditionFourEdge leaderPos
      unfold AgentState.isLeader at hleader ⊢
      rw [← erase_conditionFourFiniteConfig]
      rw [← heq]
      exact hleader
    obtain ⟨uniquePos, _, honly⟩ := conditionFour_unique
    have hzero : (conditionFourCoreConfig 0).isLeader := by decide
    have hzeroPos : (0 : Fin 9) = uniquePos := honly 0 hzero
    have hleaderPos : leaderPos = uniquePos := honly leaderPos hleaderInput
    have hleaderZero : leaderPos = 0 := hleaderPos.trans hzeroPos.symm
    rw [hleaderZero] at hnone
    exact hnone 2 (by omega) (by omega) conditionFourAfter_free_signal

end PPLLNoCheckBirthConditionFourRegression
