import Leader.Wu.Safety.NoCheckBirthOutputLegitimacy
import Leader.Wu.Birth.CheckChainRing


set_option autoImplicit false


/-!
# R1 does not preserve packaged output legitimacy


The analysis isolates a two-interaction obstruction to reusing
`PPLLNoCheckBirthOutputLegitimacy.OutputLegit` as a closed predicate for the
R1 row.  At `n = 9`, `psi = kappa = 3`, `tau = 48`, the starting ring has
clockwise labels `i mod 3`, one leader at cell zero, and no live bullets or
free barriers.  Cells 3, 4, 5 are the checked R1 train witnesses


* `tok 0 true true`,
* `tok 1 false false`,
* `tok 2 true false`.


The scheduler word `[3, 4]` first serves edge `(3,4)` and then edge `(4,5)`.
The existing `crossed_chain_births` certificate makes cell 5 a leader, while
`step1_other` frames the old leader at cell 0.  Hence the old four-field
`OutputLegit` predicate is not closed under R1.
-/


namespace R1OutputLegitNotClosed


open PPLL PPLLResearchFormulation PPLLExpiringComparisonRepair
open PPLLNoCheckBirthPhysicalConditionOne
open PPLLNoCheckBirthConditionTwoPhysical
open BirthCheckPermitRepairLeaf BirthCheckChainR1Ring


private theorem h3 : 0 < 3 := by
  decide


private theorem h23 : 2 ≤ 3 := by
  decide


abbrev Config := BirthCheckPermitRepairLeaf.FC 9 3 3 48


/-- The nine-cell directed ring used by the counterexample. -/
theorem ring9 : DirectedRing 9 := ⟨by decide⟩


/--
Canonical output-safe cells everywhere except the checked R1 train at 3,4,5.
The canonical cell at 0 is the unique leader; every physical label is `i mod 3`.
-/
def initial : Config :=
  fun i =>
    if i = (3 : Fin 9) then
      BirthCheckPermitRepair.tok 0 true true
    else if i = (4 : Fin 9) then
      BirthCheckPermitRepair.tok 1 false false
    else if i = (5 : Fin 9) then
      BirthCheckPermitRepair.tok 2 true false
    else
      PPLLNoCheckBirthOutputLegitimacy.outputFinite
        (n := 9) h3 3 48 i


/-- Raw physical erasure of the R1 starting configuration. -/
def rawInitial : Fin 9 → AgentState 3 :=
  PPLLNoCheckBirthPhysicalConditionOne.eraseExpiringConfig initial


/-- The canonical raw output-safe witness on the same ring. -/
abbrev baseRaw : Fin 9 → AgentState 3 :=
  PPLLNoCheckBirthOutputLegitimacy.outputCore h3


/--
Replacing canonical cells 3,4,5 by the three R1 tokens changes no field read by
`OutputSafeConfig`: leader, label, shield, bullet, or `signal_B`.
-/
private theorem initial_peaceView (i : Fin 9) :
    PeaceView.ofState (rawInitial i) =
      PeaceView.ofState (baseRaw i) := by
  by_cases hi3 : i = (3 : Fin 9)
  · subst i
    decide +kernel
  by_cases hi4 : i = (4 : Fin 9)
  · subst i
    decide +kernel
  by_cases hi5 : i = (5 : Fin 9)
  · subst i
    decide +kernel
  · have hcell :
        initial i =
          PPLLNoCheckBirthOutputLegitimacy.outputFinite
            (n := 9) h3 3 48 i := by
      simp only [initial, if_neg hi3, if_neg hi4, if_neg hi5]
    have hraw :
        rawInitial i =
          PPLLNoCheckBirthPhysicalConditionOne.eraseExpiringConfig
            (PPLLNoCheckBirthOutputLegitimacy.outputFinite
              (n := 9) h3 3 48) i := by
      unfold rawInitial PPLLNoCheckBirthPhysicalConditionOne.eraseExpiringConfig
      rw [hcell]
    have hbase :
        PPLLNoCheckBirthPhysicalConditionOne.eraseExpiringConfig
            (PPLLNoCheckBirthOutputLegitimacy.outputFinite
              (n := 9) h3 3 48) i =
          baseRaw i := by
      simpa only [baseRaw] using
        congrFun
          (PPLLNoCheckBirthOutputLegitimacy.erase_outputFinite
            (n := 9) h3 3 48) i
    exact congrArg PeaceView.ofState (hraw.trans hbase)


private theorem initial_leader_eq (i : Fin 9) :
    (rawInitial i).leader = (baseRaw i).leader := by
  exact congrArg (fun v : PeaceView 3 => v.leader) (initial_peaceView i)


private theorem initial_label_eq (i : Fin 9) :
    (rawInitial i).label = (baseRaw i).label := by
  exact congrArg (fun v : PeaceView 3 => v.label) (initial_peaceView i)


private theorem initial_bullet_eq (i : Fin 9) :
    (rawInitial i).bullet = (baseRaw i).bullet := by
  exact congrArg (fun v : PeaceView 3 => v.bullet) (initial_peaceView i)


private theorem base_bullet_zero (i : Fin 9) :
    (baseRaw i).bullet = (0 : Fin 3) := by
  rfl


private theorem initial_bullet_zero (i : Fin 9) :
    (rawInitial i).bullet = (0 : Fin 3) := by
  exact (initial_bullet_eq i).trans (base_bullet_zero i)


private theorem base_outputSafe :
    OutputSafeConfig h3 ring9 baseRaw :=
  PPLLNoCheckBirthOutputLegitimacy.outputCore_safe h3 ring9


/--
The initial R1 configuration satisfies the exact packaged no-CHECK-birth
`OutputLegit`; no surrogate safety predicate is used.
-/
theorem initial_outputLegit :
    PPLLNoCheckBirthOutputLegitimacy.OutputLegit h3 ring9 initial := by
  unfold PPLLNoCheckBirthOutputLegitimacy.OutputLegit
  change OutputSafeConfig h3 ring9 rawInitial
  refine
    { unique_leader := ?_
      leader_label_zero := ?_
      no_nonpeaceful_bullet := ?_
      no_free_barrier := ?_ }
  · obtain ⟨leaderPos, hleader, honly⟩ := base_outputSafe.unique_leader
    refine ⟨leaderPos, ?_, ?_⟩
    · change (rawInitial leaderPos).leader = true
      change (baseRaw leaderPos).leader = true at hleader
      rw [initial_leader_eq leaderPos]
      exact hleader
    · intro j hj
      apply honly j
      change (baseRaw j).leader = true
      change (rawInitial j).leader = true at hj
      rw [initial_leader_eq j] at hj
      exact hj
  · intro i hi
    have hiBase : (baseRaw i).isLeader := by
      change (baseRaw i).leader = true
      change (rawInitial i).leader = true at hi
      rw [initial_leader_eq i] at hi
      exact hi
    have hz := base_outputSafe.leader_label_zero i hiBase
    exact (initial_label_eq i).trans hz
  · intro i hlive
    exfalso
    exact (by decide : (0 : Fin 3) ≠ 2)
      ((initial_bullet_zero i).symm.trans hlive)
  · intro i
    dsimp only
    intro hbarrier
    have hbarrierBase :
        isBarrier h3 (baseRaw i)
          (baseRaw (ring9.rightNeighbor i)) := by
      unfold isBarrier at hbarrier ⊢
      intro hsucc
      apply hbarrier
      simpa only [initial_label_eq] using hsucc
    have hright :
        (baseRaw (ring9.rightNeighbor i)).isLeader :=
      base_outputSafe.no_free_barrier i hbarrierBase
    change (rawInitial (ring9.rightNeighbor i)).leader = true
    change (baseRaw (ring9.rightNeighbor i)).leader = true at hright
    rw [initial_leader_eq (ring9.rightNeighbor i)]
    exact hright


/-- The raw leader projection of the finite wrapper is definitionally exact. -/
private theorem eraseExpiringConfig_leader
    (C : Config) (i : Fin 9) :
    (PPLLNoCheckBirthPhysicalConditionOne.eraseExpiringConfig C i).leader =
      (C i).core.core.leader := by
  rfl


private theorem right_three :
    ring9.rightNeighbor (3 : Fin 9) = (4 : Fin 9) := by
  apply Fin.ext
  rfl


private theorem right_four :
    ring9.rightNeighbor (4 : Fin 9) = (5 : Fin 9) := by
  apply Fin.ext
  rfl


/-- First requested R1 interaction, edge `(3,4)`. -/
def afterFirst : Config :=
  BirthCheckPermitRepairLeaf.step1 h3 h23 ring9 initial (3 : Fin 9)


/-- Second requested R1 interaction, edge `(4,5)`. -/
def afterSecond : Config :=
  BirthCheckPermitRepairLeaf.step1 h3 h23 ring9 afterFirst (4 : Fin 9)


/-- The exact scheduler word of the two-interaction obstruction. -/
def twoStepWord : List (Fin 9) := [(3 : Fin 9), (4 : Fin 9)]


private theorem fold_twoStepWord :
    twoStepWord.foldl
        (BirthCheckPermitRepairLeaf.step1 h3 h23 ring9) initial =
      afterSecond := by
  rfl


/-- Cell 4 after the first global step is exactly the certified pair responder. -/
private theorem after_first_four :
    afterFirst (4 : Fin 9) =
      (BirthCheckPermitRepair.row
        h3 (by decide : 0 < 2) h23
        (BirthCheckPermitRepair.tok 0 true true)
        (BirthCheckPermitRepair.tok 1 false false)).2 := by
  have h := BirthCheckChainR1Ring.step1_right
    h3 h23 ring9 initial (3 : Fin 9)
    (by rw [right_three]; decide)
  rw [right_three] at h
  simpa [afterFirst, initial] using h


/-- The first global step does not touch cell 5. -/
private theorem after_first_five :
    afterFirst (5 : Fin 9) =
      BirthCheckPermitRepair.tok 2 true false := by
  have h := BirthCheckPermitRepairLeaf.step1_other
    h3 h23 ring9 initial (3 : Fin 9) (5 : Fin 9)
    (by decide) (by rw [right_three]; decide)
  simpa [afterFirst, initial] using h


/-- Cell 5 after the second global step is the responder of the certified chain row. -/
private theorem after_second_five :
    afterSecond (5 : Fin 9) =
      (BirthCheckPermitRepair.row
        h3 (by decide : 0 < 2) h23
        (afterFirst (4 : Fin 9))
        (afterFirst (5 : Fin 9))).2 := by
  have h := BirthCheckChainR1Ring.step1_right
    h3 h23 ring9 afterFirst (4 : Fin 9)
    (by rw [right_four]; decide)
  rw [right_four] at h
  simpa [afterSecond] using h


/-- The existing two-row R1 certificate makes cell 5 a leader. -/
private theorem new_leader_at_five :
    (afterSecond (5 : Fin 9)).core.core.leader = true := by
  rw [after_second_five]
  rw [after_first_four, after_first_five]
  decide +kernel


/-- The first requested edge does not touch the old leader at cell 0. -/
private theorem after_first_zero :
    afterFirst (0 : Fin 9) = initial (0 : Fin 9) := by
  have h := BirthCheckPermitRepairLeaf.step1_other
    h3 h23 ring9 initial (3 : Fin 9) (0 : Fin 9)
    (by decide) (by rw [right_three]; decide)
  simpa [afterFirst] using h


/-- The second requested edge also does not touch cell 0. -/
private theorem after_second_zero :
    afterSecond (0 : Fin 9) = afterFirst (0 : Fin 9) := by
  have h := BirthCheckPermitRepairLeaf.step1_other
    h3 h23 ring9 afterFirst (4 : Fin 9) (0 : Fin 9)
    (by decide) (by rw [right_four]; decide)
  simpa [afterSecond] using h


private theorem initial_zero_leader :
    (initial (0 : Fin 9)).core.core.leader = true := by
  have hraw :
      (PPLLNoCheckBirthPhysicalConditionOne.eraseExpiringConfig initial
        (0 : Fin 9)).leader = true := by
    change (rawInitial (0 : Fin 9)).leader = true
    rw [initial_leader_eq (0 : Fin 9)]
    rfl
  exact
    (eraseExpiringConfig_leader initial (0 : Fin 9)).symm.trans hraw


private theorem old_leader_at_zero :
    (afterSecond (0 : Fin 9)).core.core.leader = true := by
  rw [after_second_zero, after_first_zero]
  exact initial_zero_leader


/-- After the two R1 steps, cells 0 and 5 are simultaneously leaders. -/
theorem two_steps_two_leaders :
    (afterSecond (0 : Fin 9)).core.core.leader = true ∧
      (afterSecond (5 : Fin 9)).core.core.leader = true := by
  exact ⟨old_leader_at_zero, new_leader_at_five⟩


private theorem afterSecond_not_unique :
    ¬ hasUniqueLeader 9
      (PPLLNoCheckBirthPhysicalConditionOne.eraseExpiringConfig afterSecond) := by
  intro hUnique
  obtain ⟨leaderPos, _hleader, honly⟩ := hUnique
  have h0 :
      (PPLLNoCheckBirthPhysicalConditionOne.eraseExpiringConfig afterSecond
        (0 : Fin 9)).isLeader := by
    change
      (PPLLNoCheckBirthPhysicalConditionOne.eraseExpiringConfig afterSecond
        (0 : Fin 9)).leader = true
    exact
      (eraseExpiringConfig_leader afterSecond (0 : Fin 9)).trans
        two_steps_two_leaders.1
  have h5 :
      (PPLLNoCheckBirthPhysicalConditionOne.eraseExpiringConfig afterSecond
        (5 : Fin 9)).isLeader := by
    change
      (PPLLNoCheckBirthPhysicalConditionOne.eraseExpiringConfig afterSecond
        (5 : Fin 9)).leader = true
    exact
      (eraseExpiringConfig_leader afterSecond (5 : Fin 9)).trans
        two_steps_two_leaders.2
  have h0pos : (0 : Fin 9) = leaderPos := honly 0 h0
  have h5pos : (5 : Fin 9) = leaderPos := honly 5 h5
  have h05 : (0 : Fin 9) = (5 : Fin 9) := h0pos.trans h5pos.symm
  exact (by decide : (0 : Fin 9) ≠ (5 : Fin 9)) h05


/-- The exact packaged `OutputLegit` predicate is false after the two R1 rows. -/
theorem afterSecond_not_outputLegit :
    ¬ PPLLNoCheckBirthOutputLegitimacy.OutputLegit
      h3 ring9 afterSecond := by
  intro hSafe
  unfold PPLLNoCheckBirthOutputLegitimacy.OutputLegit at hSafe
  exact afterSecond_not_unique hSafe.unique_leader


/--
The old packaged legitimacy predicate is not closed under R1: one explicit
`OutputLegit` configuration and one two-letter scheduler word leave it.
-/
theorem outputLegit_not_closed_R1 :
    ∃ (C : Config) (w : List (Fin 9)),
      PPLLNoCheckBirthOutputLegitimacy.OutputLegit h3 ring9 C ∧
      ¬ PPLLNoCheckBirthOutputLegitimacy.OutputLegit h3 ring9
        (w.foldl (BirthCheckPermitRepairLeaf.step1 h3 h23 ring9) C) := by
  refine ⟨initial, twoStepWord, initial_outputLegit, ?_⟩
  rw [fold_twoStepWord]
  exact afterSecond_not_outputLegit




end R1OutputLegitNotClosed
