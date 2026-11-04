import Leader.Wu.Safety.NoCheckBirthConditionFourRegression

/-!
# Exact condition-5 regression for the no-CHECK-birth repair

The increment-only prepared gate rejects an unsupported orphan command, but a
locally supported forged twin is still executable.  On a stable `ψ = 2`,
`n = 4` ring, the terminal follower carries `path3=(1,0,0)` together with
`write=increment_group`.  Condition 4 does not constrain this incomplete,
flag-zero carrier.  One exact packaged step accepts the local support and flips
the follower bit from zero to one, destroying the stable positive-group ID.
-/

namespace PPLLNoCheckBirthConditionFiveRegression

open PPLL PPLLRepair PPLLNoCheckBirthRepair
  PPLLExpiringComparisonRepair PPLLAuthorizedComparisonRepair
  PPLLNoCheckBirthPhysicalConditionOne
  PPLLNoCheckBirthConditionTwoPhysical
  PPLLNoCheckBirthConditionTwoProtocol
  PPLLNoCheckBirthConditionThreeProtocol

set_option linter.defProp false

theorem hTwo : 2 > 0 := by omega

theorem conditionFiveRing : DirectedRing 4 := ⟨by omega⟩

private theorem finFour_cases (i : Fin 4) :
    i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by
  have h : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ i.val = 3 := by omega
  rcases h with h | h | h | h
  · exact .inl (Fin.ext h)
  · exact .inr (.inl (Fin.ext h))
  · exact .inr (.inr (.inl (Fin.ext h)))
  · exact .inr (.inr (.inr (Fin.ext h)))

private def baseView (i : Fin 4) : PeaceView 2 :=
  { leader := decide (i.val = 0)
    label := ⟨i.val % 2, by omega⟩
    shield := false
    bullet := ⟨0, by omega⟩
    signal_B := ⟨0, by omega⟩ }

/-- Stable two-group input with one locally supported forged increment at the
terminal follower. -/
def conditionFiveCoreConfig (i : Fin 4) : AgentState 2 :=
  let u := PeaceView.toState (baseView i)
  if i.val = 3 then
    { u with path3 := some ⟨1, 0, 0⟩, write := .increment_group }
  else u

/-- Every raw field of the regression lies in the declared finite domain. -/
theorem conditionFiveCore_inProtocolDomain (i : Fin 4) :
    (conditionFiveCoreConfig i).inProtocolDomain 10 := by
  by_cases h3 : i.val = 3
  · simp [conditionFiveCoreConfig, PeaceView.toState, baseView,
      AgentState.inProtocolDomain, h3]
  · simp [conditionFiveCoreConfig, PeaceView.toState, baseView,
      AgentState.inProtocolDomain, h3]

/-- Exact finite reification with arbitrary auxiliary fields fixed to false and
the sole `τ=0` timer value. -/
def conditionFiveFiniteConfig (i : Fin 4) : ExpiringAgentState 2 10 0 :=
  ⟨⟨BoundedAgentState.ofDomain (conditionFiveCoreConfig i)
      (conditionFiveCore_inProtocolDomain i), false⟩, ⟨0, by omega⟩⟩

/-- The edge immediately preceding the terminal follower. -/
def conditionFiveEdge : Fin 4 := ⟨2, by omega⟩

/-- Exact successor under the packaged finite no-CHECK-birth protocol. -/
def conditionFiveFiniteAfter : Fin 4 → ExpiringAgentState 2 10 0 :=
  (noCheckBirthProtocol hTwo 10 0).step
    conditionFiveRing conditionFiveFiniteConfig conditionFiveEdge

/-- Erasing the exact finite input recovers the displayed raw witness. -/
theorem erase_conditionFiveFiniteConfig :
    eraseExpiringConfig conditionFiveFiniteConfig = conditionFiveCoreConfig := by
  funext i
  change BoundedAgentState.erase
    (BoundedAgentState.ofDomain (conditionFiveCoreConfig i)
      (conditionFiveCore_inProtocolDomain i)) = conditionFiveCoreConfig i
  exact BoundedAgentState.erase_ofDomain _ _

private theorem conditionFive_unique :
    hasUniqueLeader 4 conditionFiveCoreConfig := by
  refine ⟨0, by decide, ?_⟩
  intro i hi
  rcases finFour_cases i with h | h | h | h <;>
    subst i <;> simp [conditionFiveCoreConfig, PeaceView.toState, baseView,
      AgentState.isLeader] at hi ⊢

private theorem conditionFive_no_bad_bullet :
    noNonPeacefulBullet hTwo conditionFiveRing conditionFiveCoreConfig := by
  intro i hLive
  rcases finFour_cases i with h | h | h | h <;>
    subst i <;>
    simp [conditionFiveCoreConfig, PeaceView.toState, baseView] at hLive

private theorem conditionFiveCore_path3_two :
    (conditionFiveCoreConfig 2).path3 = none := by
  rfl

private theorem conditionFive_no_free_overwriting :
    noFreeOverwritingSignal hTwo conditionFiveRing conditionFiveCoreConfig := by
  refine ⟨0, by decide, by decide, ?_⟩
  intro i hi hbound hfree
  have hi1 : i = 1 := by omega
  subst i
  obtain ⟨_, haligned⟩ := hfree.1
  obtain ⟨p, hpath, _⟩ := haligned 0 (by omega)
  change (conditionFiveCoreConfig 2).path3 = some p at hpath
  rw [conditionFiveCore_path3_two] at hpath
  contradiction

private theorem conditionFive_stable_id :
    isStableIDSequence hTwo conditionFiveRing conditionFiveCoreConfig := by
  refine ⟨0, by decide, by decide, ?_, ?_⟩
  · intro k hk
    have hkCases : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
    rcases hkCases with h | h | h | h <;> subst k <;> decide
  · intro i hi hbound
    have hi1 : i = 1 := by omega
    subst i
    dsimp only
    change groupID conditionFiveRing.hn conditionFiveCoreConfig 2 =
      trailingZeros 1
    simp [groupID, List.range_succ, conditionFiveCoreConfig,
      PeaceView.toState, baseView, trailingZeros]

private theorem conditionFive_no_free_barrier :
    noFreeBarrier hTwo conditionFiveRing conditionFiveCoreConfig :=
  noFreeBarrier_of_stableID hTwo conditionFiveRing conditionFiveCoreConfig
    conditionFive_stable_id

/-- The exact condition-5 regression input satisfies all five paper fields. -/
theorem conditionFiveCore_paperSafe :
    PaperSafeConfig hTwo conditionFiveRing conditionFiveCoreConfig where
  unique_leader := conditionFive_unique
  no_nonpeaceful_bullet := conditionFive_no_bad_bullet
  no_free_barrier := conditionFive_no_free_barrier
  no_free_overwriting_signal := conditionFive_no_free_overwriting
  stable_id_sequence := conditionFive_stable_id

/-- The locally supported forged increment survives the prepared gate and flips
the terminal follower bit from zero to one. -/
theorem conditionFiveAfter_terminal_bit :
    (eraseExpiringConfig conditionFiveFiniteAfter 3).bit = true := by
  decide

/-- The exact output's positive group ID is one instead of the required
`trailingZeros 1 = 0`. -/
theorem conditionFiveAfter_groupID :
    groupID conditionFiveRing.hn
      (eraseExpiringConfig conditionFiveFiniteAfter) 2 = 1 := by
  decide

/-- The exact packaged output does not have a stable ID sequence. -/
theorem conditionFiveAfter_not_stableID :
    ¬isStableIDSequence hTwo conditionFiveRing
      (eraseExpiringConfig conditionFiveFiniteAfter) := by
  intro hstable
  obtain ⟨leaderPos, hleader, _, _, hgroups⟩ := hstable
  have hleaderInput : (conditionFiveCoreConfig leaderPos).isLeader := by
    have heq := noCheckBirthProtocol_step_leader_eq hTwo 10 0
      conditionFiveRing conditionFiveFiniteConfig
      (erase_conditionFiveFiniteConfig ▸ conditionFiveCore_paperSafe)
      conditionFiveEdge leaderPos
    unfold AgentState.isLeader at hleader ⊢
    exact heq.symm.trans hleader
  obtain ⟨uniquePos, _, honly⟩ := conditionFive_unique
  have hzero : (conditionFiveCoreConfig 0).isLeader := by decide
  have hzeroPos : (0 : Fin 4) = uniquePos := honly 0 hzero
  have hleaderPos : leaderPos = uniquePos := honly leaderPos hleaderInput
  have hleaderZero : leaderPos = 0 := hleaderPos.trans hzeroPos.symm
  rw [hleaderZero] at hgroups
  have hgroup := hgroups 1 (by omega) (by omega)
  dsimp only at hgroup
  change groupID conditionFiveRing.hn
    (eraseExpiringConfig conditionFiveFiniteAfter) 2 = trailingZeros 1 at hgroup
  have htz : trailingZeros 1 = 0 :=
    trailingZeros_of_odd 1 (by omega) (by omega)
  rw [conditionFiveAfter_groupID, htz] at hgroup
  omega

/-- Corrected condition 5 is not preserved by the current exact finite repair.
The input is PaperSafe, but one packaged step destroys the stable positive-group
ID sequence. -/
theorem noCheckBirthProtocol_conditionFive_counterexample :
    PaperSafeConfig hTwo conditionFiveRing
        (eraseExpiringConfig conditionFiveFiniteConfig) ∧
      ¬isStableIDSequence hTwo conditionFiveRing
        (eraseExpiringConfig conditionFiveFiniteAfter) := by
  constructor
  · rw [erase_conditionFiveFiniteConfig]
    exact conditionFiveCore_paperSafe
  · exact conditionFiveAfter_not_stableID

end PPLLNoCheckBirthConditionFiveRegression
