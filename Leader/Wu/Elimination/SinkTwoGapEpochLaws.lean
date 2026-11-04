import Leader.Wu.Elimination.SinkTwoGapEpochCost


open LDSinkGapCleanup LDSinkKernelC LDSinkProtectedAbsorption LDSinkGapDoneInvariant
  LDSinkGapBlockedPreStep LDSinkGapCleanupBound LDTwoGapFrame
  LDSinkTwoGapEpochDefs LDSinkTwoGapEpochCost PPLLRepair
  FiniteUniformStoppingTree
open Classical


namespace LDSinkTwoGapEpochLaws


set_option autoImplicit false


variable {n ψ : Nat}


/-- The C5 stopping predicate for the gap whose rank is used by `localRank`.
`favorable` has no active one-gap rank, so it is treated as already done and
therefore routed to the residual ghost-progress law below. -/
def ActiveGapDone (F : TwoGapFrame n) (x : EpochState n ψ F) : Prop :=
  match x.phase with
  | .seekK => GapDoneC F.attack x.conf
  | .transit => GapDoneC F.attack x.conf
  | .parked => GapDoneC F.recovery x.conf
  | .resetK => GapDoneC F.attack x.conf
  | .seekJ => GapDoneC F.recovery x.conf
  | .favorable => True


/-- Strict decrease of the currently selected one-gap C5 rank after the
physical epoch step, before any ghost phase change is charged. -/
def ActiveGapStrict (hψ : ψ > 0) (F : TwoGapFrame n)
    (x : EpochState n ψ F) (e : Fin n) : Prop :=
  match x.phase with
  | .seekK =>
      LDSinkGapServiceRank.gapWC F.attack (epochStepConf hψ F x e) <
        LDSinkGapServiceRank.gapWC F.attack x.conf
  | .transit =>
      LDSinkGapServiceRank.gapWC F.attack (epochStepConf hψ F x e) <
        LDSinkGapServiceRank.gapWC F.attack x.conf
  | .parked =>
      LDSinkGapServiceRank.gapWC F.recovery (epochStepConf hψ F x e) <
        LDSinkGapServiceRank.gapWC F.recovery x.conf
  | .resetK =>
      LDSinkGapServiceRank.gapWC F.attack (epochStepConf hψ F x e) <
        LDSinkGapServiceRank.gapWC F.attack x.conf
  | .seekJ =>
      LDSinkGapServiceRank.gapWC F.recovery (epochStepConf hψ F x e) <
        LDSinkGapServiceRank.gapWC F.recovery x.conf
  | .favorable => False


/-- Kernel-facing residue after all same-phase C5 inequalities and the
`transit -> parked` debt arithmetic have been discharged in this file. -/
structure RoundKernelResidual (hψ : ψ > 0) (F : TwoGapFrame n) : Prop where
  /-- **Active-domain seam.** `RoundActive` stores only positive `roundRank`;
  the one-gap C5 lemmas require the two gap invariants and the absorption
  escrow is stated on `Entrance`. -/
  activeEntrance :
    ∀ x : RoundActive (ψ := ψ) F, Entrance hψ F x.1


  /-- **Nonterminal successor-invariant seam.** A non-success,
  non-absorption raw epoch step preserves both gap invariants.  This is used
  only on the `transit -> parked` branch to bound the successor `localRank`
  by `localRankBound`. -/
  successorInvariants :
    ∀ (x : RoundActive (ψ := ψ) F) (e : Fin n),
      ¬ Success F (epochStepConf hψ F x.1 e) →
      ¬ ParkedAbsorption F x.1 (epochStepConf hψ F x.1 e) →
      GapInvariant hψ F.recovery (epochStepConf hψ F x.1 e) ∧
        GapInvariant hψ F.attack (epochStepConf hψ F x.1 e)


  /-- **K2/two-gap projection seam.** On the gap selected by the current ghost
  phase, `epochStepConf` has the same `gapWC` as the checked one-gap K2 step.
  No kernel unfolding is used in this file. -/
  activeGapProjection :
    ∀ (x : RoundActive (ψ := ψ) F) (e : Fin n),
      match x.1.phase with
      | .seekK =>
          LDSinkGapServiceRank.gapWC F.attack (epochStepConf hψ F x.1 e) =
            LDSinkGapServiceRank.gapWC F.attack
              (sinkStepC hψ F.attack x.1.conf e)
      | .transit =>
          LDSinkGapServiceRank.gapWC F.attack (epochStepConf hψ F x.1 e) =
            LDSinkGapServiceRank.gapWC F.attack
              (sinkStepC hψ F.attack x.1.conf e)
      | .parked =>
          LDSinkGapServiceRank.gapWC F.recovery (epochStepConf hψ F x.1 e) =
            LDSinkGapServiceRank.gapWC F.recovery
              (sinkStepC hψ F.recovery x.1.conf e)
      | .resetK =>
          LDSinkGapServiceRank.gapWC F.attack (epochStepConf hψ F x.1 e) =
            LDSinkGapServiceRank.gapWC F.attack
              (sinkStepC hψ F.attack x.1.conf e)
      | .seekJ =>
          LDSinkGapServiceRank.gapWC F.recovery (epochStepConf hψ F x.1 e) =
            LDSinkGapServiceRank.gapWC F.recovery
              (sinkStepC hψ F.recovery x.1.conf e)
      | .favorable => True


  /-- **Absorption-restart seam.** The only phase change not handled by
  `advancePhase` is parked absorption, which jumps to `resetK`.  Given the
  prepaid scalar credit from `AbsorptionPrepaidAtEntrance`, this field states
  exactly the remaining total-rank comparison. -/
  absorptionStep :
    ∀ (x : RoundActive (ψ := ψ) F) (e : Fin n),
      ¬ ActiveGapDone F x.1 →
      ¬ Success F (epochStepConf hψ F x.1 e) →
      ParkedAbsorption F x.1 (epochStepConf hψ F x.1 e) →
      absorptionRaise F ≤ roundRank F x.1 →
      stoppedRoundRank F (roundStepStopped hψ F x e) ≤ roundRank F x.1 ∧
        (ActiveGapStrict hψ F x.1 e →
          stoppedRoundRank F (roundStepStopped hψ F x e) <
            roundRank F x.1)


  /-- **Absorption escrow seam.** The quantitative entrance credit used by the
  preceding field. -/
  absorptionPrepaid : AbsorptionPrepaidAtEntrance hψ F


  /-- **Done-gap ghost-progress seam.** When the selected C5 gap is already
  `GapDoneC` (or the phase is `favorable`), C5 no longer supplies a strict
  physical edge.  The ghost rule must preserve rank on every raw edge and
  expose one strict rank-retiring edge or success. -/
  doneStep :
    ∀ x : RoundActive (ψ := ψ) F,
      ActiveGapDone F x.1 →
      (∀ e : Fin n,
        stoppedRoundRank F (roundStepStopped hψ F x e) ≤ roundRank F x.1) ∧
      ∃ e : Fin n,
        stoppedRoundRank F (roundStepStopped hψ F x e) < roundRank F x.1


private theorem roundActive_not_success (F : TwoGapFrame n)
    (x : RoundActive (ψ := ψ) F) :
    ¬ Success F x.1.conf := by
  intro hs
  have hz := (roundRank_eq_zero_iff_success F x.1).2 hs
  have hp := x.2
  omega


private theorem stoppedRoundRank_eq_zero_of_success
    (hψ : ψ > 0) (F : TwoGapFrame n)
    (x : RoundActive (ψ := ψ) F) (e : Fin n)
    (hs : Success F (epochStepConf hψ F x.1 e)) :
    stoppedRoundRank F (roundStepStopped hψ F x e) = 0 := by
  unfold roundStepStopped
  dsimp only
  split
  · rfl
  · rename_i hnot
    exact False.elim (hnot hs)


/-- C5 gives a strict physical edge whenever the phase-selected gap is not
`GapDoneC`; `activeGapProjection` transfers that edge to `epochStepConf`. -/
private theorem exists_activeGapStrict
    (hψ : ψ > 0) (F : TwoGapFrame n)
    (hR : RoundKernelResidual hψ F)
    (x : RoundActive (ψ := ψ) F)
    (hnd : ¬ ActiveGapDone F x.1) :
    ∃ e : Fin n, ActiveGapStrict hψ F x.1 e := by
  have hE := hR.activeEntrance x
  cases hphase : x.1.phase with
  | seekK =>
      have hn : ¬ GapDoneC F.attack x.1.conf := by
        intro hd
        apply hnd
        unfold ActiveGapDone
        rw [hphase]
        exact hd
      obtain ⟨e, he⟩ :=
        LDSinkGapCleanupBound.exists_gapWC_step_lt'
          hψ F.attack x.1.conf hE.2.1 hn
      have hp := hR.activeGapProjection x e
      simp only [hphase] at hp
      refine ⟨e, ?_⟩
      unfold ActiveGapStrict
      rw [hphase, hp]
      exact he
  | transit =>
      have hn : ¬ GapDoneC F.attack x.1.conf := by
        intro hd
        apply hnd
        unfold ActiveGapDone
        rw [hphase]
        exact hd
      obtain ⟨e, he⟩ :=
        LDSinkGapCleanupBound.exists_gapWC_step_lt'
          hψ F.attack x.1.conf hE.2.1 hn
      have hp := hR.activeGapProjection x e
      simp only [hphase] at hp
      refine ⟨e, ?_⟩
      unfold ActiveGapStrict
      rw [hphase, hp]
      exact he
  | parked =>
      have hn : ¬ GapDoneC F.recovery x.1.conf := by
        intro hd
        apply hnd
        unfold ActiveGapDone
        rw [hphase]
        exact hd
      obtain ⟨e, he⟩ :=
        LDSinkGapCleanupBound.exists_gapWC_step_lt'
          hψ F.recovery x.1.conf hE.1 hn
      have hp := hR.activeGapProjection x e
      simp only [hphase] at hp
      refine ⟨e, ?_⟩
      unfold ActiveGapStrict
      rw [hphase, hp]
      exact he
  | resetK =>
      have hn : ¬ GapDoneC F.attack x.1.conf := by
        intro hd
        apply hnd
        unfold ActiveGapDone
        rw [hphase]
        exact hd
      obtain ⟨e, he⟩ :=
        LDSinkGapCleanupBound.exists_gapWC_step_lt'
          hψ F.attack x.1.conf hE.2.1 hn
      have hp := hR.activeGapProjection x e
      simp only [hphase] at hp
      refine ⟨e, ?_⟩
      unfold ActiveGapStrict
      rw [hphase, hp]
      exact he
  | seekJ =>
      have hn : ¬ GapDoneC F.recovery x.1.conf := by
        intro hd
        apply hnd
        unfold ActiveGapDone
        rw [hphase]
        exact hd
      obtain ⟨e, he⟩ :=
        LDSinkGapCleanupBound.exists_gapWC_step_lt'
          hψ F.recovery x.1.conf hE.1 hn
      have hp := hR.activeGapProjection x e
      simp only [hphase] at hp
      refine ⟨e, ?_⟩
      unfold ActiveGapStrict
      rw [hphase, hp]
      exact he
  | favorable =>
      have hd : ActiveGapDone F x.1 := by
        unfold ActiveGapDone
        rw [hphase]
        trivial
      exact False.elim (hnd hd)


/-- Every non-success, non-absorption edge from a non-done phase is
nonincreasing.  The only genuine `advancePhase` change is handled directly by
`phaseDebt_advance_dominates_local`. -/
private theorem ordinary_nonincrease
    (hψ : ψ > 0) (F : TwoGapFrame n)
    (hR : RoundKernelResidual hψ F)
    (x : RoundActive (ψ := ψ) F) (e : Fin n)
    (hnd : ¬ ActiveGapDone F x.1)
    (hs : ¬ Success F (epochStepConf hψ F x.1 e))
    (ha : ¬ ParkedAbsorption F x.1 (epochStepConf hψ F x.1 e)) :
    stoppedRoundRank F (roundStepStopped hψ F x e) ≤ roundRank F x.1 := by
  have hE := hR.activeEntrance x
  have hOld := roundActive_not_success F x
  cases hphase : x.1.phase with
  | seekK =>
      have hn : ¬ GapDoneC F.attack x.1.conf := by
        intro hd
        apply hnd
        unfold ActiveGapDone
        rw [hphase]
        exact hd
      have hle0 := LDSinkGapCleanupBound.gapWC_step_le'
        hψ F.attack x.1.conf hE.2.1 hn e
      have hproj := hR.activeGapProjection x e
      simp only [hphase] at hproj
      have hle :
          LDSinkGapServiceRank.gapWC F.attack (epochStepConf hψ F x.1 e) ≤
            LDSinkGapServiceRank.gapWC F.attack x.1.conf := by
        calc
          LDSinkGapServiceRank.gapWC F.attack (epochStepConf hψ F x.1 e) =
              LDSinkGapServiceRank.gapWC F.attack
                (sinkStepC hψ F.attack x.1.conf e) := hproj
          _ ≤ LDSinkGapServiceRank.gapWC F.attack x.1.conf := hle0
      have hstay :
          advancePhase F .seekK (epochStepConf hψ F x.1 e) = .seekK :=
        advancePhase_eq_self_of_ne_transit F .seekK
          (epochStepConf hψ F x.1 e) (by
            intro h
            cases h)
      simp only [roundStepStopped, hs, ha, stoppedRoundRank, roundRank,
        hOld, hstay, localRank, hphase, dif_neg, ite_false, if_false,
        reduceIte, reduceDIte]
      omega
  | transit =>
      have hn : ¬ GapDoneC F.attack x.1.conf := by
        intro hd
        apply hnd
        unfold ActiveGapDone
        rw [hphase]
        exact hd
      have hle0 := LDSinkGapCleanupBound.gapWC_step_le'
        hψ F.attack x.1.conf hE.2.1 hn e
      have hproj := hR.activeGapProjection x e
      simp only [hphase] at hproj
      have hle :
          LDSinkGapServiceRank.gapWC F.attack (epochStepConf hψ F x.1 e) ≤
            LDSinkGapServiceRank.gapWC F.attack x.1.conf := by
        calc
          LDSinkGapServiceRank.gapWC F.attack (epochStepConf hψ F x.1 e) =
              LDSinkGapServiceRank.gapWC F.attack
                (sinkStepC hψ F.attack x.1.conf e) := hproj
          _ ≤ LDSinkGapServiceRank.gapWC F.attack x.1.conf := hle0
      by_cases hb :
          ((epochStepConf hψ F x.1 e) (F.attack.pos 1)).bullet =
            (2 : Fin 3)
      · have hchange :
            advancePhase F .transit (epochStepConf hψ F x.1 e) ≠
              .transit := by
          simp [advancePhase, hb]
        have hdom := phaseDebt_advance_dominates_local F .transit
          (epochStepConf hψ F x.1 e) hchange
        have hInv := hR.successorInvariants x e hs ha
        have hlocal := localRank_le_localRankBound hψ F
          ({ conf := epochStepConf hψ F x.1 e,
             phase := advancePhase F .transit
               (epochStepConf hψ F x.1 e) } : EpochState n ψ F)
          hInv.1 hInv.2
        simp only [localRank, localRankBound] at hlocal
        simp only [localRankBound] at hdom
        simp only [roundStepStopped, hs, ha, stoppedRoundRank, roundRank,
          hOld, hphase, dif_neg, ite_false, if_false, reduceIte, reduceDIte,
          localRank, localRankBound]
        omega
      · have hstay :
            advancePhase F .transit (epochStepConf hψ F x.1 e) =
              .transit := by
          simp [advancePhase, hb]
        simp only [roundStepStopped, hs, ha, stoppedRoundRank, roundRank,
          hOld, hstay, localRank, hphase, dif_neg, ite_false, if_false,
          reduceIte, reduceDIte]
        omega
  | parked =>
      have hn : ¬ GapDoneC F.recovery x.1.conf := by
        intro hd
        apply hnd
        unfold ActiveGapDone
        rw [hphase]
        exact hd
      have hle0 := LDSinkGapCleanupBound.gapWC_step_le'
        hψ F.recovery x.1.conf hE.1 hn e
      have hproj := hR.activeGapProjection x e
      simp only [hphase] at hproj
      have hle :
          LDSinkGapServiceRank.gapWC F.recovery (epochStepConf hψ F x.1 e) ≤
            LDSinkGapServiceRank.gapWC F.recovery x.1.conf := by
        calc
          LDSinkGapServiceRank.gapWC F.recovery (epochStepConf hψ F x.1 e) =
              LDSinkGapServiceRank.gapWC F.recovery
                (sinkStepC hψ F.recovery x.1.conf e) := hproj
          _ ≤ LDSinkGapServiceRank.gapWC F.recovery x.1.conf := hle0
      have hstay :
          advancePhase F .parked (epochStepConf hψ F x.1 e) = .parked :=
        advancePhase_eq_self_of_ne_transit F .parked
          (epochStepConf hψ F x.1 e) (by
            intro h
            cases h)
      simp only [roundStepStopped, hs, ha, stoppedRoundRank, roundRank,
        hOld, hstay, localRank, hphase, dif_neg, ite_false, if_false,
        reduceIte, reduceDIte]
      omega
  | resetK =>
      have hn : ¬ GapDoneC F.attack x.1.conf := by
        intro hd
        apply hnd
        unfold ActiveGapDone
        rw [hphase]
        exact hd
      have hle0 := LDSinkGapCleanupBound.gapWC_step_le'
        hψ F.attack x.1.conf hE.2.1 hn e
      have hproj := hR.activeGapProjection x e
      simp only [hphase] at hproj
      have hle :
          LDSinkGapServiceRank.gapWC F.attack (epochStepConf hψ F x.1 e) ≤
            LDSinkGapServiceRank.gapWC F.attack x.1.conf := by
        calc
          LDSinkGapServiceRank.gapWC F.attack (epochStepConf hψ F x.1 e) =
              LDSinkGapServiceRank.gapWC F.attack
                (sinkStepC hψ F.attack x.1.conf e) := hproj
          _ ≤ LDSinkGapServiceRank.gapWC F.attack x.1.conf := hle0
      have hstay :
          advancePhase F .resetK (epochStepConf hψ F x.1 e) = .resetK :=
        advancePhase_eq_self_of_ne_transit F .resetK
          (epochStepConf hψ F x.1 e) (by
            intro h
            cases h)
      simp only [roundStepStopped, hs, ha, stoppedRoundRank, roundRank,
        hOld, hstay, localRank, hphase, dif_neg, ite_false, if_false,
        reduceIte, reduceDIte]
      omega
  | seekJ =>
      have hn : ¬ GapDoneC F.recovery x.1.conf := by
        intro hd
        apply hnd
        unfold ActiveGapDone
        rw [hphase]
        exact hd
      have hle0 := LDSinkGapCleanupBound.gapWC_step_le'
        hψ F.recovery x.1.conf hE.1 hn e
      have hproj := hR.activeGapProjection x e
      simp only [hphase] at hproj
      have hle :
          LDSinkGapServiceRank.gapWC F.recovery (epochStepConf hψ F x.1 e) ≤
            LDSinkGapServiceRank.gapWC F.recovery x.1.conf := by
        calc
          LDSinkGapServiceRank.gapWC F.recovery (epochStepConf hψ F x.1 e) =
              LDSinkGapServiceRank.gapWC F.recovery
                (sinkStepC hψ F.recovery x.1.conf e) := hproj
          _ ≤ LDSinkGapServiceRank.gapWC F.recovery x.1.conf := hle0
      have hstay :
          advancePhase F .seekJ (epochStepConf hψ F x.1 e) = .seekJ :=
        advancePhase_eq_self_of_ne_transit F .seekJ
          (epochStepConf hψ F x.1 e) (by
            intro h
            cases h)
      simp only [roundStepStopped, hs, ha, stoppedRoundRank, roundRank,
        hOld, hstay, localRank, hphase, dif_neg, ite_false, if_false,
        reduceIte, reduceDIte]
      omega
  | favorable =>
      have hd : ActiveGapDone F x.1 := by
        unfold ActiveGapDone
        rw [hphase]
        trivial
      exact False.elim (hnd hd)


/-- If C5 supplies a strict physical edge and that edge is not an absorption,
the outer round strictly drops.  The `transit -> parked` case is paid by the
corrected lexicographic block and the successor local-rank bound. -/
private theorem ordinary_strict_of_activeGapStrict
    (hψ : ψ > 0) (F : TwoGapFrame n)
    (hR : RoundKernelResidual hψ F)
    (x : RoundActive (ψ := ψ) F) (e : Fin n)
    (hs : ¬ Success F (epochStepConf hψ F x.1 e))
    (ha : ¬ ParkedAbsorption F x.1 (epochStepConf hψ F x.1 e))
    (hlt : ActiveGapStrict hψ F x.1 e) :
    stoppedRoundRank F (roundStepStopped hψ F x e) < roundRank F x.1 := by
  have hOld := roundActive_not_success F x
  cases hphase : x.1.phase with
  | seekK =>
      unfold ActiveGapStrict at hlt
      rw [hphase] at hlt
      have hstay :
          advancePhase F .seekK (epochStepConf hψ F x.1 e) = .seekK :=
        advancePhase_eq_self_of_ne_transit F .seekK
          (epochStepConf hψ F x.1 e) (by
            intro h
            cases h)
      simp only [roundStepStopped, hs, ha, stoppedRoundRank, roundRank,
        hOld, hstay, localRank, hphase, dif_neg, ite_false, if_false,
        reduceIte, reduceDIte]
      omega
  | transit =>
      unfold ActiveGapStrict at hlt
      rw [hphase] at hlt
      by_cases hb :
          ((epochStepConf hψ F x.1 e) (F.attack.pos 1)).bullet =
            (2 : Fin 3)
      · have hchange :
            advancePhase F .transit (epochStepConf hψ F x.1 e) ≠
              .transit := by
          simp [advancePhase, hb]
        have hdom := phaseDebt_advance_dominates_local F .transit
          (epochStepConf hψ F x.1 e) hchange
        have hInv := hR.successorInvariants x e hs ha
        have hlocal := localRank_le_localRankBound hψ F
          ({ conf := epochStepConf hψ F x.1 e,
             phase := advancePhase F .transit
               (epochStepConf hψ F x.1 e) } : EpochState n ψ F)
          hInv.1 hInv.2
        have hOldLocalPos : 0 < localRank F x.1 := by
          have hpos :
              0 < LDSinkGapServiceRank.gapWC F.attack x.1.conf := by
            omega
          simpa [localRank, hphase] using hpos
        simp only [localRank, localRankBound] at hlocal
        simp only [localRankBound] at hdom
        simp only [roundStepStopped, hs, ha, stoppedRoundRank, roundRank,
          hOld, hphase, dif_neg, ite_false, if_false, reduceIte, reduceDIte,
          localRank, localRankBound]
        omega
      · have hstay :
            advancePhase F .transit (epochStepConf hψ F x.1 e) =
              .transit := by
          simp [advancePhase, hb]
        simp only [roundStepStopped, hs, ha, stoppedRoundRank, roundRank,
          hOld, hstay, localRank, hphase, dif_neg, ite_false, if_false,
          reduceIte, reduceDIte]
        omega
  | parked =>
      unfold ActiveGapStrict at hlt
      rw [hphase] at hlt
      have hstay :
          advancePhase F .parked (epochStepConf hψ F x.1 e) = .parked :=
        advancePhase_eq_self_of_ne_transit F .parked
          (epochStepConf hψ F x.1 e) (by
            intro h
            cases h)
      simp only [roundStepStopped, hs, ha, stoppedRoundRank, roundRank,
        hOld, hstay, localRank, hphase, dif_neg, ite_false, if_false,
        reduceIte, reduceDIte]
      omega
  | resetK =>
      unfold ActiveGapStrict at hlt
      rw [hphase] at hlt
      have hstay :
          advancePhase F .resetK (epochStepConf hψ F x.1 e) = .resetK :=
        advancePhase_eq_self_of_ne_transit F .resetK
          (epochStepConf hψ F x.1 e) (by
            intro h
            cases h)
      simp only [roundStepStopped, hs, ha, stoppedRoundRank, roundRank,
        hOld, hstay, localRank, hphase, dif_neg, ite_false, if_false,
        reduceIte, reduceDIte]
      omega
  | seekJ =>
      unfold ActiveGapStrict at hlt
      rw [hphase] at hlt
      have hstay :
          advancePhase F .seekJ (epochStepConf hψ F x.1 e) = .seekJ :=
        advancePhase_eq_self_of_ne_transit F .seekJ
          (epochStepConf hψ F x.1 e) (by
            intro h
            cases h)
      simp only [roundStepStopped, hs, ha, stoppedRoundRank, roundRank,
        hOld, hstay, localRank, hphase, dif_neg, ite_false, if_false,
        reduceIte, reduceDIte]
      omega
  | favorable =>
      unfold ActiveGapStrict at hlt
      rw [hphase] at hlt
      exact False.elim hlt


/-- The third field of `RoundRankLaws` is pure phase arithmetic. -/
theorem phaseAdvanceRetires_cost (F : TwoGapFrame n)
    (p : GhostPhase) (C : Fin n → AgentState ψ) :
    phaseDebt F (advancePhase F p C) ≤ phaseDebt F p :=
  phaseDebt_advancePhase_le F p C


/-- Assemble the full rank contract.  All ordinary non-done/non-absorption
edges, including `transit -> parked`, are proved above.  Only the explicit
kernel residual fields remain assumptions. -/
theorem roundRankLaws_of_residual
    (hψ : ψ > 0) (F : TwoGapFrame n)
    (hR : RoundKernelResidual hψ F) :
    RoundRankLaws hψ F := by
  refine ⟨?_, ?_, ?_⟩
  · intro x e
    by_cases hs : Success F (epochStepConf hψ F x.1 e)
    · have hz := stoppedRoundRank_eq_zero_of_success hψ F x e hs
      rw [hz]
      exact Nat.zero_le _
    · by_cases hdone : ActiveGapDone F x.1
      · exact (hR.doneStep x hdone).1 e
      · by_cases habs : ParkedAbsorption F x.1 (epochStepConf hψ F x.1 e)
        · have hcredit : absorptionRaise F ≤ roundRank F x.1 :=
            hR.absorptionPrepaid x.1 (hR.activeEntrance x)
              (roundActive_not_success F x)
          exact (hR.absorptionStep x e hdone hs habs hcredit).1
        · exact ordinary_nonincrease hψ F hR x e hdone hs habs
  · intro x
    by_cases hdone : ActiveGapDone F x.1
    · exact (hR.doneStep x hdone).2
    · obtain ⟨e, hlt⟩ := exists_activeGapStrict hψ F hR x hdone
      refine ⟨e, ?_⟩
      by_cases hs : Success F (epochStepConf hψ F x.1 e)
      · have hz := stoppedRoundRank_eq_zero_of_success hψ F x e hs
        rw [hz]
        exact x.2
      · by_cases habs : ParkedAbsorption F x.1 (epochStepConf hψ F x.1 e)
        · have hcredit : absorptionRaise F ≤ roundRank F x.1 :=
            hR.absorptionPrepaid x.1 (hR.activeEntrance x)
              (roundActive_not_success F x)
          exact (hR.absorptionStep x e hdone hs habs hcredit).2 hlt
        · exact ordinary_strict_of_activeGapStrict
            hψ F hR x e hs habs hlt
  · intro p C
    exact phaseAdvanceRetires_cost F p C


#print axioms LDSinkTwoGapEpochLaws.phaseAdvanceRetires_cost
#print axioms LDSinkTwoGapEpochLaws.roundRankLaws_of_residual


end LDSinkTwoGapEpochLaws
