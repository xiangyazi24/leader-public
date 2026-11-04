import Leader.PPL.Elim.AttemptCostModerateCleanReady


namespace PPL.Convergence.LDLocal


set_option autoImplicit false
set_option Elab.async false


open FiniteUniformStoppingTree


/-!
# LD(736): moderate attempt cost with configuration-minimum CR rank


The recorded CR mode in the unchanged kernel is not rank-unique.  This file
therefore measures a CR configuration by the minimum rank of any holding mode.


The strict Bellman edge is the required edge of a minimum-rank holding mode.
It need not be the required edge of the recorded mode: the finite scheduler
sum needs one strict edge, and the physical kernel can be evaluated at that
edge regardless of which holding mode it records.


The only residual left by this file is the already-existing
ModerateSealedControlStageRows family for dummyWait, vulnerable, and recovery.
The new potential agrees with the old potential on those stages, and the old
row family is proved below to imply the corresponding min-potential row family.
-/


/-! ## Finite enumeration of CR modes -/


def crModeCandidates (d : Nat) : List CRMode :=
  (List.range d).map (fun p => CRMode.drain p) ++
    ([CRMode.repair] ++
      ((List.range d).map (fun p => CRMode.sweep p) ++
        (List.range d).map (fun q => CRMode.ret (q + 1))))


theorem crModeCandidates_mem_of_valid
    {n : Nat} {ring : DirectedRing n}
    {C0 : Config n} (A : SectorFrame ring C0)
    (m : CRMode) (hvalid : CRModeValid A m) :
    m ∈ crModeCandidates A.gap := by
  cases m with
  | drain p =>
      have hp : p < A.gap := by
        simpa [CRModeValid] using hvalid
      apply List.mem_append.mpr
      exact
        Or.inl
          (List.mem_map.mpr
            ⟨p, List.mem_range.mpr hp, rfl⟩)
  | repair =>
      apply List.mem_append.mpr
      apply Or.inr
      apply List.mem_append.mpr
      exact Or.inl (by simp)
  | sweep p =>
      have hp : p < A.gap := by
        simpa [CRModeValid] using hvalid
      apply List.mem_append.mpr
      apply Or.inr
      apply List.mem_append.mpr
      apply Or.inr
      apply List.mem_append.mpr
      exact
        Or.inl
          (List.mem_map.mpr
            ⟨p, List.mem_range.mpr hp, rfl⟩)
  | ret q =>
      have hq0 : 0 < q := hvalid.1
      obtain ⟨k, hkq⟩ :=
        Nat.exists_eq_succ_of_ne_zero
          (show q ≠ 0 by omega)
      subst q
      have hk : k < A.gap := by
        have hle := hvalid.2
        omega
      apply List.mem_append.mpr
      apply Or.inr
      apply List.mem_append.mpr
      apply Or.inr
      apply List.mem_append.mpr
      apply Or.inr
      exact
        List.mem_map.mpr
          ⟨k, List.mem_range.mpr hk, by simp⟩


def CRMinRankCandidate
    {n : Nat} {ring : DirectedRing n}
    {C0 : Config n} (A : SectorFrame ring C0)
    (C : Config n) (r : Nat) : Prop :=
  ∃ m,
    And (m ∈ crModeCandidates A.gap)
      (And (CRModeHolds A C m)
        (crRank A m = r))


private theorem crMinRankCandidate_of_holds
    {n : Nat} {ring : DirectedRing n}
    {C0 : Config n} (A : SectorFrame ring C0)
    (C : Config n) (m : CRMode)
    (hmode : CRModeHolds A C m) :
    CRMinRankCandidate A C (crRank A m) := by
  refine
    ⟨m,
      And.intro
        (crModeCandidates_mem_of_valid
          A m (crModeHolds_valid A C m hmode))
        (And.intro hmode rfl)⟩


private theorem crMinRankCandidate_exists
    {n : Nat} {ring : DirectedRing n}
    {C0 : Config n} (A : SectorFrame ring C0)
    (C : Config n) (m : CRMode)
    (hmode : CRModeHolds A C m) :
    ∃ r, CRMinRankCandidate A C r :=
  ⟨crRank A m, crMinRankCandidate_of_holds A C m hmode⟩


noncomputable def firstNatFrom
    (p : Nat → Prop) : Nat → Nat → Nat
  | k, 0 => k
  | k, fuel + 1 =>
      @ite Nat (p k) (Classical.propDecidable (p k))
        k (firstNatFrom p (k + 1) fuel)


theorem firstNatFrom_spec
    (p : Nat → Prop) (k fuel : Nat)
    (hex :
      ∃ j,
        And (k ≤ j)
          (And (j ≤ k + fuel) (p j))) :
    p (firstNatFrom p k fuel) := by
  classical
  induction fuel generalizing k with
  | zero =>
      rcases hex with
        ⟨j, hkj, hjk, hpj⟩
      have hj : j = k := by
        omega
      subst j
      simpa [firstNatFrom] using hpj
  | succ fuel ih =>
      by_cases hk : p k
      · simpa [firstNatFrom, hk]
      · simp only [firstNatFrom, if_neg hk]
        apply ih (k := k + 1)
        rcases hex with
          ⟨j, hkj, hjk, hpj⟩
        have hkj' : k + 1 ≤ j := by
          by_cases hj : j = k
          · subst j
            exact False.elim (hk hpj)
          · omega
        refine ⟨j, hkj', ?_, hpj⟩
        omega


theorem firstNatFrom_minimality
    (p : Nat → Prop) (k fuel : Nat) :
    ∀ j,
      k ≤ j →
      j < firstNatFrom p k fuel →
      ¬ p j := by
  classical
  induction fuel generalizing k with
  | zero =>
      intro j hkj hj _hpj
      simp only [firstNatFrom] at hj
      omega
  | succ fuel ih =>
      intro j hkj hj hpj
      by_cases hk : p k
      · simp only [firstNatFrom, if_pos hk] at hj
        omega
      · simp only [firstNatFrom, if_neg hk] at hj
        by_cases hjk : j = k
        · subst j
          exact hk hpj
        · exact
            (ih (k := k + 1) (j := j)
              (by omega) hj) hpj


theorem firstNatFrom_bound
    (p : Nat → Prop) (k fuel : Nat) :
    firstNatFrom p k fuel ≤ k + fuel := by
  classical
  induction fuel generalizing k with
  | zero =>
      simp only [firstNatFrom, Nat.add_zero]
      exact Nat.le_refl k
  | succ fuel ih =>
      by_cases hk : p k
      · simp only [firstNatFrom, if_pos hk]
        omega
      · simp only [firstNatFrom, if_neg hk]
        have h :=
          ih (k := k + 1)
        omega


noncomputable def crMinRank
    {n : Nat} {ring : DirectedRing n}
    {C0 : Config n} (A : SectorFrame ring C0)
    (C : Config n) : Nat :=
  firstNatFrom
    (fun r =>
      ∃ m,
        And (CRModeHolds A C m)
          (crRank A m = r))
    0 (3 * A.gap + 1)


theorem crMinRank_spec
    {n : Nat} {ring : DirectedRing n}
    {C0 : Config n} (A : SectorFrame ring C0)
    (C : Config n) (m : CRMode)
    (hmode : CRModeHolds A C m) :
    CRMinRankCandidate A C (crMinRank A C) := by
  have hrank :
      crRank A m ≤ 3 * A.gap :=
    crRank_le_three_gap
      A m (crModeHolds_valid A C m hmode)
  have hex :
      ∃ r,
        And (0 ≤ r)
          (And
            (r ≤ 0 + (3 * A.gap + 1))
            (∃ mode,
              And (CRModeHolds A C mode)
                (crRank A mode = r))) := by
    refine
      ⟨crRank A m, Nat.zero_le _, ?_, ?_⟩
    · omega
    · exact
        ⟨m, And.intro hmode rfl⟩
  have hfound :=
    firstNatFrom_spec
      (p := fun r =>
        ∃ mode,
          And (CRModeHolds A C mode)
            (crRank A mode = r))
      0 (3 * A.gap + 1) hex
  rcases hfound with
    ⟨minMode, hminMode, hrankMin⟩
  refine
    ⟨minMode,
      crModeCandidates_mem_of_valid
        A minMode
        (crModeHolds_valid
          A C minMode hminMode),
      hminMode, ?_⟩
  simpa [crMinRank] using hrankMin


theorem crMinRank_le_rank
    {n : Nat} {ring : DirectedRing n}
    {C0 : Config n} (A : SectorFrame ring C0)
    (C : Config n) (m : CRMode)
    (hmode : CRModeHolds A C m) :
    crMinRank A C ≤ crRank A m := by
  unfold crMinRank
  let p : Nat → Prop :=
    fun r =>
      ∃ mode,
        And (CRModeHolds A C mode)
          (crRank A mode = r)
  change
    firstNatFrom p 0 (3 * A.gap + 1) ≤
      crRank A m
  by_cases hle :
      firstNatFrom p 0 (3 * A.gap + 1) ≤
        crRank A m
  · exact hle
  · have hlt :
        crRank A m <
          firstNatFrom p 0 (3 * A.gap + 1) := by
      omega
    have hnot :=
      firstNatFrom_minimality
        p 0 (3 * A.gap + 1)
        (crRank A m)
        (Nat.zero_le _) hlt
    exact
      False.elim
        (hnot
          ⟨m, And.intro hmode rfl⟩)

theorem crMinRank_mode
    {n : Nat} {ring : DirectedRing n}
    {C0 : Config n} (A : SectorFrame ring C0)
    (C : Config n) (m : CRMode)
    (hmode : CRModeHolds A C m) :
    ∃ minMode,
      And (CRModeHolds A C minMode)
        (crRank A minMode = crMinRank A C) := by
  rcases
      crMinRank_spec A C m hmode with
    ⟨minMode, _hmem, hminMode, hrank⟩
  exact
    ⟨minMode, And.intro hminMode hrank⟩


theorem crMinRank_pos
    {n : Nat} {ring : DirectedRing n}
    {C0 : Config n} (A : SectorFrame ring C0)
    (C : Config n) (m : CRMode)
    (hmode : CRModeHolds A C m) :
    0 < crMinRank A C := by
  rcases
      crMinRank_mode A C m hmode with
    ⟨minMode, hminMode, hrank⟩
  have hpos :=
    crRank_pos A minMode
      (crModeHolds_valid A C minMode hminMode)
  rw [hrank] at hpos
  exact hpos


/-! ## Min-rank one-step laws -/


theorem crMinRank_step_le
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (A : SectorFrame ring C0)
    (C : Config n)
    (hPB : PPL.Elim.PB ring C)
    (hInterior : CRInteriorFollowers A C)
    (m : CRMode) (hmode : CRModeHolds A C m)
    (e : Fin n)
    (hnotDone : ¬ CRDone A (stepE ring C e)) :
    crMinRank A (stepE ring C e) ≤
      crMinRank A C := by
  rcases
      crMinRank_mode A C m hmode with
    ⟨minMode, hminMode, hrankMin⟩
  rcases
      (crRankStep_proved
        ring A C minMode hPB hInterior hminMode).1 e with
    hdone | hnext
  · exact False.elim (hnotDone hdone)
  · rcases hnext with
      ⟨nextMode, hnextMode, hrankNext⟩
    have hminNext :=
      crMinRank_le_rank
        A (stepE ring C e) nextMode hnextMode
    rw [hrankMin] at hrankNext
    exact Nat.le_trans hminNext hrankNext


theorem crMinRank_required_lt
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (A : SectorFrame ring C0)
    (C : Config n)
    (hPB : PPL.Elim.PB ring C)
    (hInterior : CRInteriorFollowers A C)
    (minMode : CRMode)
    (hminMode : CRModeHolds A C minMode)
    (hrankMin :
      crRank A minMode = crMinRank A C)
    (hnotDone :
      ¬ CRDone A
        (stepE ring C
          (crRequiredEdge A minMode))) :
    crMinRank A
        (stepE ring C
          (crRequiredEdge A minMode)) <
      crMinRank A C := by
  rcases
      (crRankStep_proved
        ring A C minMode hPB hInterior hminMode).2 with
    hdone | hnext
  · exact False.elim (hnotDone hdone)
  · rcases hnext with
      ⟨nextMode, hnextMode, hrankNext⟩
    have hminNext :=
      crMinRank_le_rank
        A
        (stepE ring C
          (crRequiredEdge A minMode))
        nextMode hnextMode
    rw [hrankMin] at hrankNext
    omega


/-! ## Configuration-sensitive live potential -/


noncomputable def moderateStagePotentialMin
    {n : Nat} {ring : DirectedRing n}
    {C0 : Config n} (F : TripleFrame ring C0)
    (C : Config n) : ModerateStage → Nat
  | .attackCR _ =>
      n * crMinRank F.A C +
        moderateAfterAttackBudget F
  | .targetCR _ _ =>
      n * crMinRank F.B C +
        moderateWaitBudget F
  | .dummyWait _ targetPhase =>
      n * phaseDebt F.b targetPhase +
        moderateWaitBudget F
  | .vulnerable attackPhase _ =>
      n * attackerCoeff F attackPhase +
        moderateRecoveryBudget F
  | .recovery _ targetPhase =>
      n * phaseDebt F.b targetPhase
  | .stuck => 0


noncomputable def moderateLivePotentialMin
    {n : Nat} {ring : DirectedRing n}
    {C0 : Config n} (F : TripleFrame ring C0) :
    ModerateAttemptState ring F → Nat
  | .junk _ => 0
  | .live C _ stage =>
      moderateStagePotentialMin F C stage


theorem moderateLivePotentialMin_le
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0)
    (s : ModerateAttemptState ring F)
    (hreach : ModerateReachableGood ring F s) :
    moderateLivePotentialMin F s ≤
      moderateLivePotential F s := by
  cases s with
  | junk C =>
      exact False.elim hreach
  | live C hgood stage =>
      cases stage with
      | attackCR mode =>
          have hmode :
              CRModeHolds F.A C mode := by
            simpa [ModerateReachableGood] using hreach
          have hmin :=
            crMinRank_le_rank F.A C mode hmode
          simp only
            [moderateLivePotentialMin,
              moderateStagePotentialMin,
              moderateLivePotential,
              moderateStagePotential]
          exact
            Nat.add_le_add_right
              (Nat.mul_le_mul_left n hmin) _
      | targetCR attackPhase mode =>
          have hparts :
              And
                (PhaseHolds F.A C attackPhase)
                (CRModeHolds F.B C mode) := by
            simpa [ModerateReachableGood] using hreach
          have hmin :=
            crMinRank_le_rank F.B C mode hparts.2
          simp only
            [moderateLivePotentialMin,
              moderateStagePotentialMin,
              moderateLivePotential,
              moderateStagePotential]
          exact
            Nat.add_le_add_right
              (Nat.mul_le_mul_left n hmin) _
      | dummyWait attackPhase targetPhase =>
          exact Nat.le_refl _
      | vulnerable attackPhase targetPhase =>
          exact Nat.le_refl _
      | recovery attackPhase targetPhase =>
          exact Nat.le_refl _
      | stuck =>
          have hf : False := by
            simpa [ModerateReachableGood] using hreach
          exact False.elim hf


theorem moderateLivePotentialMin_start_le
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0)
    (D : Config n) (hgood : AttemptGood ring F D) :
    moderateLivePotentialMin F
        ((moderateAttemptKernel ring F).start D) ≤
      moderatePaperAttemptBudget n F.a F.b := by
  have hreach :=
    moderateReachableGood_start ring F D hgood
  have hle :=
    moderateLivePotentialMin_le
      ring F
      ((moderateAttemptKernel ring F).start D)
      hreach
  exact
    Nat.le_trans hle
      (moderateLivePotential_start_le
        ring F D hgood)


/-! ## Mirrors needed for the completed attack-CR child -/


private theorem moderateMin_notEndpointB
    {n : Nat} {ring : DirectedRing n}
    {C0 : Config n} (F : TripleFrame ring C0)
    (D : Config n) (hgood : AttemptGood ring F D) :
    ¬ EndpointDeleted F.B D := by
  intro h
  exact hgood.2.1
    (endpointB_deleted_tagged F D h)


private noncomputable def
    moderateMinAfterAttackStageMirror
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0)
    (D : Config n) (hgood : AttemptGood ring F D) :
    ModerateStage := by
  classical
  if hB : CleanReady F.B D then
    exact .dummyWait .ready .ready
  else
    exact .targetCR .ready
      (moderateCRInitModeMirror
        ring F.B D hgood.1
        (moderateMin_notEndpointB F D hgood) hB)


private theorem moderateMin_phaseReady
    {n : Nat} {ring : DirectedRing n}
    {C0 : Config n} (A : SectorFrame ring C0)
    (C : Config n)
    (hInterior : CRInteriorFollowers A C)
    (hclean : CleanReady A C) :
    PhaseHolds A C .ready := by
  constructor
  · intro q hq0 hq
    exact hInterior q hq0 hq
  · exact hclean


private theorem moderateMin_phaseANext
    (hSealed : SealedStepSpec)
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0)
    (C : Config n) (hgood : AttemptGood ring F C)
    (ph : SectorPhase)
    (hph : PhaseHolds F.A C ph)
    (e : Fin n)
    (hnot :
      ¬ TaggedDeleted F (stepE ring C e)) :
    PhaseHolds F.A (stepE ring C e)
      (nextSectorPhase F.A ph e) := by
  have hcur :
      ¬ EndpointDeleted F.A C := by
    intro hdel
    exact hgood.2.1
      (endpointA_deleted_tagged F C hdel)
  have hnext :
      ¬ EndpointDeleted F.A
        (stepE ring C e) := by
    intro hdel
    exact hnot
      (endpointA_deleted_tagged
        F (stepE ring C e) hdel)
  rcases
      hSealed ring F.A C ph hph hcur e with
    hdel | hsurvive
  · exact False.elim (hnext hdel)
  · rcases hsurvive with
      ⟨ph', hph', htr⟩
    have heq :
        ph' = nextSectorPhase F.A ph e := by
      simpa [PhaseTransition] using htr
    rw [heq] at hph'
    exact hph'


private theorem moderateMin_afterAttack_good
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0)
    (D : Config n) (hgood : AttemptGood ring F D)
    (hAready : PhaseHolds F.A D .ready) :
    ModerateReachableGood ring F
      (.live D hgood
        (moderateMinAfterAttackStageMirror
          ring F D hgood)) := by
  classical
  by_cases hB : CleanReady F.B D
  · have hBready :
        PhaseHolds F.B D .ready :=
      moderateMin_phaseReady
        F.B D hgood.2.2.2 hB
    simpa
      [moderateMinAfterAttackStageMirror, hB,
        ModerateReachableGood]
      using And.intro hAready hBready
  · have hinit :=
      moderateCRInitModeMirror_spec
        ring F.B D hgood.1
        (moderateMin_notEndpointB F D hgood) hB
    simpa
      [moderateMinAfterAttackStageMirror, hB,
        ModerateReachableGood]
      using And.intro hAready hinit.1


private theorem moderateMin_targetPreparation_exact
    (n b : Nat) :
    3 * n * b + n * (2 * b - 1) =
      n * (5 * b - 1) := by
  calc
    3 * n * b + n * (2 * b - 1)
        = n * (3 * b) +
            n * (2 * b - 1) := by
          ac_rfl
    _ = n * (3 * b + (2 * b - 1)) := by
          rw [Nat.mul_add]
    _ = n * (5 * b - 1) := by
          congr 1
          omega


private theorem
    moderateMin_waitBudget_le_afterAttack
    {n : Nat} {ring : DirectedRing n}
    {C0 : Config n}
    (F : TripleFrame ring C0) :
    moderateWaitBudget F ≤
      moderateAfterAttackBudget F := by
  unfold moderateWaitBudget
    moderateAfterAttackBudget
  apply Nat.add_le_add_right
  apply Nat.mul_le_mul_left
  have hb : 0 < F.b := by
    have h := F.B.gap_pos
    simpa [F.B_gap] using h
  omega


private theorem
    moderateMin_targetInit_le_afterAttack
    {n : Nat} {ring : DirectedRing n}
    {C0 : Config n}
    (F : TripleFrame ring C0)
    (D : Config n) (mode : CRMode)
    (hmode : CRModeHolds F.B D mode)
    (hrank : crRank F.B mode ≤ 3 * F.B.gap) :
    n * crMinRank F.B D +
        moderateWaitBudget F ≤
      moderateAfterAttackBudget F := by
  have hmin :=
    crMinRank_le_rank F.B D mode hmode
  have hbound :
      crMinRank F.B D ≤ 3 * F.B.gap :=
    Nat.le_trans hmin hrank
  have hrank' :
      n * crMinRank F.B D ≤
        3 * n * F.b := by
    have h :=
      Nat.mul_le_mul_left n hbound
    simpa
      [F.B_gap, Nat.mul_assoc,
        Nat.mul_comm, Nat.mul_left_comm]
      using h
  unfold moderateWaitBudget
    moderateAfterAttackBudget
  have hex :=
    moderateMin_targetPreparation_exact n F.b
  unfold moderateVulnerableBudget
    moderateRecoveryBudget
  omega


private theorem
    moderateMin_afterAttack_potential_le
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0)
    (D : Config n) (hgood : AttemptGood ring F D) :
    moderateStagePotentialMin F D
        (moderateMinAfterAttackStageMirror
          ring F D hgood) ≤
      moderateAfterAttackBudget F := by
  classical
  by_cases hB : CleanReady F.B D
  · simpa
      [moderateMinAfterAttackStageMirror, hB,
        moderateStagePotentialMin, phaseDebt]
      using
        moderateMin_waitBudget_le_afterAttack F
  · have hinit :=
      moderateCRInitModeMirror_spec
        ring F.B D hgood.1
        (moderateMin_notEndpointB F D hgood) hB
    simpa
      [moderateMinAfterAttackStageMirror, hB,
        moderateStagePotentialMin]
      using
        moderateMin_targetInit_le_afterAttack
          F D
          (moderateCRInitModeMirror
            ring F.B D hgood.1
            (moderateMin_notEndpointB F D hgood) hB)
          hinit.1 hinit.2


theorem moderateMinAttackCR_done_step_mirror
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0)
    (C : Config n) (hgood : AttemptGood ring F C)
    (mode : CRMode) (e : Fin n)
    (htag :
      ¬ TaggedDeleted F (stepE ring C e))
    (hmode : CRModeHolds F.A C mode)
    (hdone : CRDone F.A (stepE ring C e)) :
    (moderateAttemptKernel ring F).step
        (.live C hgood (.attackCR mode)) e =
      .active
        (.live (stepE ring C e)
          (attemptGood_step ring F C e hgood htag)
          (moderateMinAfterAttackStageMirror
            ring F (stepE ring C e)
            (attemptGood_step
              ring F C e hgood htag))) := by
  simp
    [moderateAttemptKernel, moderateStep,
      htag, hmode, hdone,
      moderateMinAfterAttackStageMirror,
      moderateCRInitModeMirror]
  all_goals rfl


private theorem moderateMin_dummyWaitReady_potential
    {n : Nat} {ring : DirectedRing n}
    {C0 : Config n} (F : TripleFrame ring C0)
    (D : Config n) (hgood : AttemptGood ring F D)
    (attackPhase : SectorPhase) :
    moderateLivePotentialMin F
        (.live D hgood
          (.dummyWait attackPhase .ready)) =
      moderateWaitBudget F := by
  simp
    [moderateLivePotentialMin,
      moderateStagePotentialMin, phaseDebt]


/-! ## One-service-edge arithmetic -/


private theorem moderateMin_oneExceptionAffine
    {n r tail : Nat}
    (a : Fin n) (f : Fin n → Nat)
    (hr : 0 < r)
    (ha :
      f a ≤ n * (r - 1) + tail)
    (hother :
      ∀ e, e ≠ a →
        f e ≤ n * r + tail) :
    n + (List.ofFn f).sum ≤
      n * (n * r + tail) := by
  let c := n * r + tail
  let g : Fin n → Nat :=
    fun e => if e = a then f e else c
  have hfg : ∀ e, f e ≤ g e := by
    intro e
    by_cases he : e = a
    · simp [g, he]
    · simpa [g, he] using hother e he
  have hsum0 :
      (List.ofFn f).sum ≤
        (List.ofFn g).sum :=
    ofFn_sum_le f g hfg
  have hsumg :
      (List.ofFn g).sum =
        f a + (n - 1) * c := by
    have h :=
      PredictableTwoTargetFiniteTree.ofFn_sum_one_value_else_const
        a g c (by
          intro e he
          simp [g, he])
    simpa [g] using h
  have hsum :
      (List.ofFn f).sum ≤
        f a + (n - 1) * c := by
    rw [hsumg] at hsum0
    exact hsum0
  have hsum' :
      (List.ofFn f).sum ≤
        (n * (r - 1) + tail) +
          (n - 1) * c :=
    Nat.le_trans hsum
      (Nat.add_le_add_right ha _)
  have hc :
      c = n + (n * (r - 1) + tail) := by
    obtain ⟨q, hq⟩ :=
      Nat.exists_eq_succ_of_ne_zero
        (show r ≠ 0 by omega)
    subst r
    dsimp [c]
    rw [Nat.mul_succ]
    omega
  have hm :
      n * c = c + (n - 1) * c := by
    obtain ⟨q, hq⟩ :=
      Nat.exists_eq_succ_of_ne_zero
        (show n ≠ 0 by
          have haLt := a.isLt
          omega)
    rw [hq]
    simp [Nat.succ_mul, Nat.add_comm]
  calc
    n + (List.ofFn f).sum
        ≤ n +
            ((n * (r - 1) + tail) +
              (n - 1) * c) :=
      Nat.add_le_add_left hsum' n
    _ = (n + (n * (r - 1) + tail)) +
          (n - 1) * c := by
      omega
    _ = c + (n - 1) * c := by
      rw [← hc]
    _ = n * c := hm.symm
    _ = n * (n * r + tail) := by
      rfl


/-! ## CR rows for the min potential -/


noncomputable def ModerateCRStageRowsMin : Prop :=
  ∀ (hSealed : SealedStepSpec),
    ∀ {n : Nat} (ring : DirectedRing n)
      {C0 : Config n} (F : TripleFrame ring C0)
      (hb : 2 ≤ F.b)
      (C : Config n)
      (hgood : AttemptGood ring F C)
      (stage : ModerateStage),
      ModerateCRStage stage →
      ModerateReachableGood ring F
        (.live C hgood stage) →
      And
        (∀ e a',
          (moderateAttemptKernel ring F).step
              (.live C hgood stage) e =
            .active a' →
          ModerateReachableGood ring F a')
        (n +
            (List.ofFn (fun e : Fin n =>
              attemptNodePotential
                (moderateLivePotentialMin F)
                ((moderateAttemptKernel ring F).step
                  (.live C hgood stage) e))).sum ≤
          n * moderateLivePotentialMin F
            (.live C hgood stage))


theorem moderateCRStageRowsMin :
    ModerateCRStageRowsMin := by
  intro hSealed n ring C0 F _hb
    C hgood stage hCR hreach
  cases stage with
  | attackCR mode =>
      have hmode :
          CRModeHolds F.A C mode := by
        simpa [ModerateReachableGood] using hreach
      refine And.intro ?_ ?_
      · intro e a' hstep
        by_cases htag :
            TaggedDeleted F (stepE ring C e)
        · have hs :
              (moderateAttemptKernel ring F).step
                  (.live C hgood (.attackCR mode)) e =
                .success := by
            simp
              [moderateAttemptKernel,
                moderateStep, htag]
          have hbad :
              (AttemptNode.success :
                AttemptNode
                  (ModerateAttemptState ring F)
                  (Config n)) =
                .active a' :=
            hs.symm.trans hstep
          cases hbad
        · have hgoodD :
              AttemptGood ring F
                (stepE ring C e) :=
            attemptGood_step
              ring F C e hgood htag
          by_cases hdone :
              CRDone F.A (stepE ring C e)
          · have hnotA :
                ¬ EndpointDeleted F.A
                  (stepE ring C e) := by
              intro hdel
              exact htag
                (endpointA_deleted_tagged
                  F (stepE ring C e) hdel)
            have hcleanA :
                CleanReady F.A
                  (stepE ring C e) :=
              Or.resolve_left hdone hnotA
            have hAready :
                PhaseHolds F.A
                  (stepE ring C e) .ready :=
              moderateMin_phaseReady
                F.A (stepE ring C e)
                hgoodD.2.2.1 hcleanA
            have hs :=
              moderateMinAttackCR_done_step_mirror
                ring F C hgood mode e
                htag hmode hdone
            let child :
                ModerateAttemptState ring F :=
              .live (stepE ring C e) hgoodD
                (moderateMinAfterAttackStageMirror
                  ring F (stepE ring C e) hgoodD)
            have hs' :
                (moderateAttemptKernel ring F).step
                    (.live C hgood
                      (.attackCR mode)) e =
                  .active child := by
              simpa [child] using hs
            have hnodes :
                (AttemptNode.active child :
                  AttemptNode
                    (ModerateAttemptState ring F)
                    (Config n)) =
                  .active a' :=
              hs'.symm.trans hstep
            have ha : child = a' := by
              injection hnodes
            rw [← ha]
            exact
              moderateMin_afterAttack_good
                ring F (stepE ring C e)
                hgoodD hAready
          · have hs :=
              moderateAttackCR_notDone_step_mirror
                ring F C hgood mode e
                htag hmode hdone
            let child :
                ModerateAttemptState ring F :=
              .live (stepE ring C e) hgoodD
                (.attackCR
                  (moderateCRNextModeMirror
                    ring F.A C mode hgood.1
                    hgood.2.2.1 hmode e hdone))
            have hs' :
                (moderateAttemptKernel ring F).step
                    (.live C hgood
                      (.attackCR mode)) e =
                  .active child := by
              simpa [child] using hs
            have hnodes :
                (AttemptNode.active child :
                  AttemptNode
                    (ModerateAttemptState ring F)
                    (Config n)) =
                  .active a' :=
              hs'.symm.trans hstep
            have ha : child = a' := by
              injection hnodes
            rw [← ha]
            have hn :=
              moderateCRNextModeMirror_spec
                ring F.A C mode hgood.1
                hgood.2.2.1 hmode e hdone
            simpa
              [child, ModerateReachableGood]
              using hn.1
      · simp only
          [moderateLivePotentialMin,
            moderateStagePotentialMin]
        have hrpos :
            0 < crMinRank F.A C :=
          crMinRank_pos F.A C mode hmode
        rcases
            crMinRank_mode F.A C mode hmode with
          ⟨minMode, hminMode, hrankMin⟩
        apply
          moderateMin_oneExceptionAffine
            (a := crRequiredEdge F.A minMode)
            (f := fun e : Fin n =>
              attemptNodePotential
                (moderateLivePotentialMin F)
                ((moderateAttemptKernel ring F).step
                  (.live C hgood
                    (.attackCR mode)) e))
            (r := crMinRank F.A C)
            (tail := moderateAfterAttackBudget F)
            hrpos
        · let e := crRequiredEdge F.A minMode
          by_cases htag :
              TaggedDeleted F (stepE ring C e)
          · have hs :
                (moderateAttemptKernel ring F).step
                    (.live C hgood
                      (.attackCR mode)) e =
                  .success := by
              simp
                [moderateAttemptKernel,
                  moderateStep, htag]
            rw [hs]
            simp [attemptNodePotential]
          · by_cases hdone :
                CRDone F.A (stepE ring C e)
            · have hs :=
                moderateMinAttackCR_done_step_mirror
                  ring F C hgood mode e
                  htag hmode hdone
              rw [hs]
              change
                moderateStagePotentialMin F
                    (stepE ring C e)
                    (moderateMinAfterAttackStageMirror
                      ring F (stepE ring C e)
                      (attemptGood_step
                        ring F C e hgood htag)) ≤
                  n * (crMinRank F.A C - 1) +
                    moderateAfterAttackBudget F
              have hp :=
                moderateMin_afterAttack_potential_le
                  ring F (stepE ring C e)
                  (attemptGood_step
                    ring F C e hgood htag)
              exact
                Nat.le_trans hp
                  (Nat.le_add_left _ _)
            · have hs :=
                moderateAttackCR_notDone_step_mirror
                  ring F C hgood mode e
                  htag hmode hdone
              rw [hs]
              change
                n * crMinRank F.A
                    (stepE ring C e) +
                    moderateAfterAttackBudget F ≤
                  n * (crMinRank F.A C - 1) +
                    moderateAfterAttackBudget F
              have hlt :
                  crMinRank F.A
                      (stepE ring C e) <
                    crMinRank F.A C := by
                simpa [e] using
                  (crMinRank_required_lt
                    ring F.A C hgood.1
                    hgood.2.2.1
                    minMode hminMode hrankMin
                    (by simpa [e] using hdone))
              have hle :
                  crMinRank F.A
                      (stepE ring C e) ≤
                    crMinRank F.A C - 1 := by
                omega
              exact
                Nat.add_le_add_right
                  (Nat.mul_le_mul_left n hle) _
        · intro e _hne
          by_cases htag :
              TaggedDeleted F (stepE ring C e)
          · have hs :
                (moderateAttemptKernel ring F).step
                    (.live C hgood
                      (.attackCR mode)) e =
                  .success := by
              simp
                [moderateAttemptKernel,
                  moderateStep, htag]
            rw [hs]
            simp [attemptNodePotential]
          · by_cases hdone :
                CRDone F.A (stepE ring C e)
            · have hs :=
                moderateMinAttackCR_done_step_mirror
                  ring F C hgood mode e
                  htag hmode hdone
              rw [hs]
              change
                moderateStagePotentialMin F
                    (stepE ring C e)
                    (moderateMinAfterAttackStageMirror
                      ring F (stepE ring C e)
                      (attemptGood_step
                        ring F C e hgood htag)) ≤
                  n * crMinRank F.A C +
                    moderateAfterAttackBudget F
              have hp :=
                moderateMin_afterAttack_potential_le
                  ring F (stepE ring C e)
                  (attemptGood_step
                    ring F C e hgood htag)
              exact
                Nat.le_trans hp
                  (Nat.le_add_left _ _)
            · have hs :=
                moderateAttackCR_notDone_step_mirror
                  ring F C hgood mode e
                  htag hmode hdone
              rw [hs]
              change
                n * crMinRank F.A
                    (stepE ring C e) +
                    moderateAfterAttackBudget F ≤
                  n * crMinRank F.A C +
                    moderateAfterAttackBudget F
              have hn :=
                crMinRank_step_le
                  ring F.A C hgood.1
                  hgood.2.2.1 mode hmode e hdone
              exact
                Nat.add_le_add_right
                  (Nat.mul_le_mul_left n hn) _
  | targetCR attackPhase mode =>
      have hparts :
          And
            (PhaseHolds F.A C attackPhase)
            (CRModeHolds F.B C mode) := by
        simpa [ModerateReachableGood] using hreach
      have hA := hparts.1
      have hmode := hparts.2
      refine And.intro ?_ ?_
      · intro e a' hstep
        by_cases htag :
            TaggedDeleted F (stepE ring C e)
        · have hs :
              (moderateAttemptKernel ring F).step
                  (.live C hgood
                    (.targetCR attackPhase mode)) e =
                .success := by
            simp
              [moderateAttemptKernel,
                moderateStep, htag]
          have hbad :
              (AttemptNode.success :
                AttemptNode
                  (ModerateAttemptState ring F)
                  (Config n)) =
                .active a' :=
            hs.symm.trans hstep
          cases hbad
        · have hgoodD :
              AttemptGood ring F
                (stepE ring C e) :=
            attemptGood_step
              ring F C e hgood htag
          have hA' :
              PhaseHolds F.A
                (stepE ring C e)
                (nextSectorPhase
                  F.A attackPhase e) :=
            moderateMin_phaseANext
              hSealed ring F C hgood
              attackPhase hA e htag
          by_cases hdone :
              CRDone F.B (stepE ring C e)
          · have hnotB :
                ¬ EndpointDeleted F.B
                  (stepE ring C e) := by
              intro hdel
              exact htag
                (endpointB_deleted_tagged
                  F (stepE ring C e) hdel)
            have hcleanB :
                CleanReady F.B
                  (stepE ring C e) :=
              Or.resolve_left hdone hnotB
            have hBready :
                PhaseHolds F.B
                  (stepE ring C e) .ready :=
              moderateMin_phaseReady
                F.B (stepE ring C e)
                hgoodD.2.2.2 hcleanB
            let child :
                ModerateAttemptState ring F :=
              .live (stepE ring C e) hgoodD
                (.dummyWait
                  (nextSectorPhase
                    F.A attackPhase e)
                  .ready)
            have hs :
                (moderateAttemptKernel ring F).step
                    (.live C hgood
                      (.targetCR attackPhase mode)) e =
                  .active child := by
              simp
                [moderateAttemptKernel,
                  moderateStep, htag,
                  hmode, hdone, child]
            have hnodes :
                (AttemptNode.active child :
                  AttemptNode
                    (ModerateAttemptState ring F)
                    (Config n)) =
                  .active a' :=
              hs.symm.trans hstep
            have ha : child = a' := by
              injection hnodes
            rw [← ha]
            simpa
              [child, ModerateReachableGood]
              using And.intro hA' hBready
          · have hs :=
              moderateTargetCR_notDone_step_mirror
                ring F C hgood attackPhase mode
                e htag hmode hdone
            let child :
                ModerateAttemptState ring F :=
              .live (stepE ring C e) hgoodD
                (.targetCR
                  (nextSectorPhase
                    F.A attackPhase e)
                  (moderateCRNextModeMirror
                    ring F.B C mode hgood.1
                    hgood.2.2.2 hmode e hdone))
            have hs' :
                (moderateAttemptKernel ring F).step
                    (.live C hgood
                      (.targetCR attackPhase mode)) e =
                  .active child := by
              simpa [child] using hs
            have hnodes :
                (AttemptNode.active child :
                  AttemptNode
                    (ModerateAttemptState ring F)
                    (Config n)) =
                  .active a' :=
              hs'.symm.trans hstep
            have ha : child = a' := by
              injection hnodes
            rw [← ha]
            have hn :=
              moderateCRNextModeMirror_spec
                ring F.B C mode hgood.1
                hgood.2.2.2 hmode e hdone
            simpa
              [child, ModerateReachableGood]
              using And.intro hA' hn.1
      · simp only
          [moderateLivePotentialMin,
            moderateStagePotentialMin]
        have hrpos :
            0 < crMinRank F.B C :=
          crMinRank_pos F.B C mode hmode
        rcases
            crMinRank_mode F.B C mode hmode with
          ⟨minMode, hminMode, hrankMin⟩
        apply
          moderateMin_oneExceptionAffine
            (a := crRequiredEdge F.B minMode)
            (f := fun e : Fin n =>
              attemptNodePotential
                (moderateLivePotentialMin F)
                ((moderateAttemptKernel ring F).step
                  (.live C hgood
                    (.targetCR attackPhase mode)) e))
            (r := crMinRank F.B C)
            (tail := moderateWaitBudget F)
            hrpos
        · let e := crRequiredEdge F.B minMode
          by_cases htag :
              TaggedDeleted F (stepE ring C e)
          · have hs :
                (moderateAttemptKernel ring F).step
                    (.live C hgood
                      (.targetCR attackPhase mode)) e =
                  .success := by
              simp
                [moderateAttemptKernel,
                  moderateStep, htag]
            rw [hs]
            simp [attemptNodePotential]
          · by_cases hdone :
                CRDone F.B (stepE ring C e)
            · have hs :
                  (moderateAttemptKernel ring F).step
                      (.live C hgood
                        (.targetCR attackPhase mode)) e =
                    .active
                      (.live (stepE ring C e)
                        (attemptGood_step
                          ring F C e hgood htag)
                        (.dummyWait
                          (nextSectorPhase
                            F.A attackPhase e)
                          .ready)) := by
                simp
                  [moderateAttemptKernel,
                    moderateStep, htag,
                    hmode, hdone]
              rw [hs]
              simpa only
                [attemptNodePotential,
                  moderateMin_dummyWaitReady_potential]
                using
                  (Nat.le_add_left
                    (moderateWaitBudget F)
                    (n * (crMinRank F.B C - 1)))
            · have hs :=
                moderateTargetCR_notDone_step_mirror
                  ring F C hgood attackPhase mode
                  e htag hmode hdone
              rw [hs]
              change
                n * crMinRank F.B
                    (stepE ring C e) +
                    moderateWaitBudget F ≤
                  n * (crMinRank F.B C - 1) +
                    moderateWaitBudget F
              have hlt :
                  crMinRank F.B
                      (stepE ring C e) <
                    crMinRank F.B C := by
                simpa [e] using
                  (crMinRank_required_lt
                    ring F.B C hgood.1
                    hgood.2.2.2
                    minMode hminMode hrankMin
                    (by simpa [e] using hdone))
              have hle :
                  crMinRank F.B
                      (stepE ring C e) ≤
                    crMinRank F.B C - 1 := by
                omega
              exact
                Nat.add_le_add_right
                  (Nat.mul_le_mul_left n hle) _
        · intro e _hne
          by_cases htag :
              TaggedDeleted F (stepE ring C e)
          · have hs :
                (moderateAttemptKernel ring F).step
                    (.live C hgood
                      (.targetCR attackPhase mode)) e =
                  .success := by
              simp
                [moderateAttemptKernel,
                  moderateStep, htag]
            rw [hs]
            simp [attemptNodePotential]
          · by_cases hdone :
                CRDone F.B (stepE ring C e)
            · have hs :
                  (moderateAttemptKernel ring F).step
                      (.live C hgood
                        (.targetCR attackPhase mode)) e =
                    .active
                      (.live (stepE ring C e)
                        (attemptGood_step
                          ring F C e hgood htag)
                        (.dummyWait
                          (nextSectorPhase
                            F.A attackPhase e)
                          .ready)) := by
                simp
                  [moderateAttemptKernel,
                    moderateStep, htag,
                    hmode, hdone]
              rw [hs]
              simpa only
                [attemptNodePotential,
                  moderateMin_dummyWaitReady_potential]
                using
                  (Nat.le_add_left
                    (moderateWaitBudget F)
                    (n * crMinRank F.B C))
            · have hs :=
                moderateTargetCR_notDone_step_mirror
                  ring F C hgood attackPhase mode
                  e htag hmode hdone
              rw [hs]
              change
                n * crMinRank F.B
                    (stepE ring C e) +
                    moderateWaitBudget F ≤
                  n * crMinRank F.B C +
                    moderateWaitBudget F
              have hn :=
                crMinRank_step_le
                  ring F.B C hgood.1
                  hgood.2.2.2 mode hmode e hdone
              exact
                Nat.add_le_add_right
                  (Nat.mul_le_mul_left n hn) _
  | dummyWait attackPhase targetPhase =>
      exact False.elim hCR
  | vulnerable attackPhase targetPhase =>
      exact False.elim hCR
  | recovery attackPhase targetPhase =>
      exact False.elim hCR
  | stuck =>
      exact False.elim hCR


/-! ## Sealed-control rows under the min potential -/


noncomputable def ModerateSealedControlStageRowsMin : Prop :=
  ∀ (hSealed : SealedStepSpec),
    ∀ {n : Nat} (ring : DirectedRing n)
      {C0 : Config n} (F : TripleFrame ring C0)
      (hb : 2 ≤ F.b)
      (C : Config n)
      (hgood : AttemptGood ring F C)
      (stage : ModerateStage),
      ModerateSealedControlStage stage →
      ModerateReachableGood ring F
        (.live C hgood stage) →
      And
        (∀ e a',
          (moderateAttemptKernel ring F).step
              (.live C hgood stage) e =
            .active a' →
          ModerateReachableGood ring F a')
        (n +
            (List.ofFn (fun e : Fin n =>
              attemptNodePotential
                (moderateLivePotentialMin F)
                ((moderateAttemptKernel ring F).step
                  (.live C hgood stage) e))).sum ≤
          n * moderateLivePotentialMin F
            (.live C hgood stage))


theorem moderateLivePotentialMin_eq_on_sealed
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (F : TripleFrame ring C0)
    (C : Config n) (hgood : AttemptGood ring F C)
    (stage : ModerateStage)
    (hstage : ModerateSealedControlStage stage) :
    moderateLivePotentialMin F
        (.live C hgood stage) =
      moderateLivePotential F
        (.live C hgood stage) := by
  cases stage with
  | attackCR mode =>
      exact False.elim hstage
  | targetCR attackPhase mode =>
      exact False.elim hstage
  | dummyWait attackPhase targetPhase =>
      rfl
  | vulnerable attackPhase targetPhase =>
      rfl
  | recovery attackPhase targetPhase =>
      rfl
  | stuck =>
      exact False.elim hstage


theorem moderateSealedControlStageRowsMin_of_old
    (hOld : ModerateSealedControlStageRows) :
    ModerateSealedControlStageRowsMin := by
  intro hSealed n ring C0 F hb
    C hgood stage hstage hreach
  have hold :=
    hOld hSealed ring F hb
      C hgood stage hstage hreach
  refine And.intro hold.1 ?_
  have hpoint :
      ∀ e : Fin n,
        attemptNodePotential
            (moderateLivePotentialMin F)
            ((moderateAttemptKernel ring F).step
              (.live C hgood stage) e) ≤
          attemptNodePotential
            (moderateLivePotential F)
            ((moderateAttemptKernel ring F).step
              (.live C hgood stage) e) := by
    intro e
    cases hstep :
        (moderateAttemptKernel ring F).step
          (.live C hgood stage) e with
    | active a' =>
        have ha' :=
          hold.1 e a' hstep
        have hp :=
          moderateLivePotentialMin_le
            ring F a' ha'
        simpa
          [hstep, attemptNodePotential]
          using hp
    | success =>
        simp [hstep, attemptNodePotential]
    | retry s =>
        simp [hstep, attemptNodePotential]
  have hsum :
      (List.ofFn (fun e : Fin n =>
        attemptNodePotential
          (moderateLivePotentialMin F)
          ((moderateAttemptKernel ring F).step
            (.live C hgood stage) e))).sum ≤
        (List.ofFn (fun e : Fin n =>
          attemptNodePotential
            (moderateLivePotential F)
            ((moderateAttemptKernel ring F).step
              (.live C hgood stage) e))).sum :=
    ofFn_sum_le _ _ hpoint
  have hcur :=
    moderateLivePotentialMin_eq_on_sealed
      ring F C hgood stage hstage
  calc
    n +
        (List.ofFn (fun e : Fin n =>
          attemptNodePotential
            (moderateLivePotentialMin F)
            ((moderateAttemptKernel ring F).step
              (.live C hgood stage) e))).sum
        ≤
      n +
        (List.ofFn (fun e : Fin n =>
          attemptNodePotential
            (moderateLivePotential F)
            ((moderateAttemptKernel ring F).step
              (.live C hgood stage) e))).sum :=
      Nat.add_le_add_left hsum n
    _ ≤
      n * moderateLivePotential F
        (.live C hgood stage) :=
      hold.2
    _ =
      n * moderateLivePotentialMin F
        (.live C hgood stage) := by
      rw [← hcur]


/-! ## Assembly -/


noncomputable def ModerateLiveSingleInteractionMinSpec : Prop :=
  ∀ (hSealed : SealedStepSpec),
    ∀ {n : Nat} (ring : DirectedRing n)
      {C0 : Config n} (F : TripleFrame ring C0)
      (hb : 2 ≤ F.b),
      And
        (∀ a e a',
          ModerateReachableGood ring F a →
          (moderateAttemptKernel ring F).step a e =
            .active a' →
          ModerateReachableGood ring F a')
        (AttemptCostSuperSolutionOn
          (moderateAttemptKernel ring F)
          (ModerateReachableGood ring F)
          (moderateLivePotentialMin F))


theorem moderateLiveSingleInteractionMin
    (hRest : ModerateSealedControlStageRows) :
    ModerateLiveSingleInteractionMinSpec := by
  intro hSealed n ring C0 F hb
  have hRestMin :=
    moderateSealedControlStageRowsMin_of_old hRest
  constructor
  · intro a e a' hgood hstep
    cases a with
    | junk C =>
        have hf : False := by
          simpa [ModerateReachableGood] using hgood
        exact False.elim hf
    | live C hstate stage =>
        cases stage with
        | attackCR mode =>
            exact
              (moderateCRStageRowsMin
                hSealed ring F hb C hstate
                (.attackCR mode)
                True.intro hgood).1 e a' hstep
        | targetCR attackPhase mode =>
            exact
              (moderateCRStageRowsMin
                hSealed ring F hb C hstate
                (.targetCR attackPhase mode)
                True.intro hgood).1 e a' hstep
        | dummyWait attackPhase targetPhase =>
            exact
              (hRestMin
                hSealed ring F hb C hstate
                (.dummyWait attackPhase targetPhase)
                True.intro hgood).1 e a' hstep
        | vulnerable attackPhase targetPhase =>
            exact
              (hRestMin
                hSealed ring F hb C hstate
                (.vulnerable attackPhase targetPhase)
                True.intro hgood).1 e a' hstep
        | recovery attackPhase targetPhase =>
            exact
              (hRestMin
                hSealed ring F hb C hstate
                (.recovery attackPhase targetPhase)
                True.intro hgood).1 e a' hstep
        | stuck =>
            have hf : False := by
              simpa [ModerateReachableGood] using hgood
            exact False.elim hf
  · unfold AttemptCostSuperSolutionOn
    intro a hgood
    cases a with
    | junk C =>
        have hf : False := by
          simpa [ModerateReachableGood] using hgood
        exact False.elim hf
    | live C hstate stage =>
        cases stage with
        | attackCR mode =>
            exact
              (moderateCRStageRowsMin
                hSealed ring F hb C hstate
                (.attackCR mode)
                True.intro hgood).2
        | targetCR attackPhase mode =>
            exact
              (moderateCRStageRowsMin
                hSealed ring F hb C hstate
                (.targetCR attackPhase mode)
                True.intro hgood).2
        | dummyWait attackPhase targetPhase =>
            exact
              (hRestMin
                hSealed ring F hb C hstate
                (.dummyWait attackPhase targetPhase)
                True.intro hgood).2
        | vulnerable attackPhase targetPhase =>
            exact
              (hRestMin
                hSealed ring F hb C hstate
                (.vulnerable attackPhase targetPhase)
                True.intro hgood).2
        | recovery attackPhase targetPhase =>
            exact
              (hRestMin
                hSealed ring F hb C hstate
                (.recovery attackPhase targetPhase)
                True.intro hgood).2
        | stuck =>
            have hf : False := by
              simpa [ModerateReachableGood] using hgood
            exact False.elim hf


theorem moderateLiveStageSuperSolutionMin
    (hRest : ModerateSealedControlStageRows) :
    ModerateLiveStageSuperSolutionSpec := by
  intro hSealed n ring C0 F hb
  refine
    ⟨ModerateReachableGood ring F,
      moderateLivePotentialMin F,
      ?_, ?_, ?_, ?_⟩
  · intro s hs
    exact
      moderateReachableGood_start
        ring F s hs
  · exact
      (moderateLiveSingleInteractionMin
        hRest hSealed ring F hb).1
  · exact
      (moderateLiveSingleInteractionMin
        hRest hSealed ring F hb).2
  · intro s hs
    exact
      moderateLivePotentialMin_start_le
        ring F s hs


theorem moderateAttemptCostSpec_min
    (hRest : ModerateSealedControlStageRows) :
    ModerateAttemptCostSpec :=
  moderateAttemptCostSpec_of_live_stage
    (moderateLiveStageSuperSolutionMin hRest)


end PPL.Convergence.LDLocal


#print axioms PPL.Convergence.LDLocal.firstNatFrom_spec
#print axioms PPL.Convergence.LDLocal.firstNatFrom_minimality
#print axioms PPL.Convergence.LDLocal.firstNatFrom_bound
#print axioms PPL.Convergence.LDLocal.crModeCandidates_mem_of_valid
#print axioms PPL.Convergence.LDLocal.crMinRank_spec
#print axioms PPL.Convergence.LDLocal.crMinRank_le_rank
#print axioms PPL.Convergence.LDLocal.crMinRank_pos
#print axioms PPL.Convergence.LDLocal.crMinRank_step_le
#print axioms PPL.Convergence.LDLocal.crMinRank_required_lt
#print axioms PPL.Convergence.LDLocal.moderateLivePotentialMin_le
#print axioms PPL.Convergence.LDLocal.moderateLivePotentialMin_start_le
#print axioms PPL.Convergence.LDLocal.moderateMinAttackCR_done_step_mirror
#print axioms PPL.Convergence.LDLocal.moderateCRStageRowsMin
#print axioms PPL.Convergence.LDLocal.moderateLivePotentialMin_eq_on_sealed
#print axioms PPL.Convergence.LDLocal.moderateSealedControlStageRowsMin_of_old
#print axioms PPL.Convergence.LDLocal.moderateLiveSingleInteractionMin
#print axioms PPL.Convergence.LDLocal.moderateLiveStageSuperSolutionMin
#print axioms PPL.Convergence.LDLocal.moderateAttemptCostSpec_min


#check PPL.Convergence.LDLocal.ModerateSealedControlStageRows
#check PPL.Convergence.LDLocal.ModerateSealedControlStageRowsMin

