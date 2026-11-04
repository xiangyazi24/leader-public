import Leader.PPL.Elim.AttemptRetryLongStages


namespace PPL.Convergence.LDLocal


set_option autoImplicit false
set_option Elab.async false


open FiniteUniformStoppingTree


/-!
Truth audit.


LongAttemptConcreteStageFactorSpec is false as written.  The progress-half
row quantifies over every LongAttemptState satisfying longProgressHandoffCut,
not only over actual progress-race entries.  LongStage stores bare SectorPhase
labels, so an inconsistent synthetic label is legal.


The concrete witness below uses n = 7, a = 5, b = 2, two tagged leaders at
0 and 5, both shielded, and no bullets/signals.  The synthetic progress state
has target phase ret 0 and attacker phase live 4.


The target phase ret 0 is absorbing.  Edge 4 is the unique attacker terminal
edge and enters recovery.  Before the first edge 4 the physical safe invariant
below prevents tagged deletion; on the first edge 4, site 4 is still the zero
follower, so that interaction also cannot delete the responder leader at 5.


Therefore longRaceMassFrom at horizon T is exactly 6^T: precisely the words
avoiding edge 4.  At T = 5 this is 7776, whereas the claimed row requires
7^5 <= 2 * 7776, i.e. 16807 <= 15552.
-/


private abbrev qRing : DirectedRing 7 := ⟨by decide⟩


private abbrev q0 : Fin 7 := ⟨0, by decide⟩
private abbrev q1 : Fin 7 := ⟨1, by decide⟩
private abbrev q2 : Fin 7 := ⟨2, by decide⟩
private abbrev q3 : Fin 7 := ⟨3, by decide⟩
private abbrev q4 : Fin 7 := ⟨4, by decide⟩
private abbrev q5 : Fin 7 := ⟨5, by decide⟩
private abbrev q6 : Fin 7 := ⟨6, by decide⟩


private def qFollowerCell : PPL.Elim.Cell4 where
  leader := false
  bullet := 0
  shield := false
  signalB := false


private def qLeaderCell : PPL.Elim.Cell4 where
  leader := true
  bullet := 0
  shield := true
  signalB := false


private def qConfig : Config 7 :=
  fun x =>
    if x = q0 then qLeaderCell
    else if x = q5 then qLeaderCell
    else qFollowerCell


private def qFrameA : SectorFrame qRing qConfig where
  left := q0
  right := q5
  gap := 5
  gap_pos := by decide
  gap_lt_n := by decide
  left_ne_right := by decide
  right_eq := by rfl
  left_leader := by rfl
  right_leader := by rfl
  interior_follower := by
    intro q hq0 hq5
    have hcases :
        Or (q = 1) (Or (q = 2) (Or (q = 3) (q = 4))) := by
      omega
    rcases hcases with h | h | h | h
    · subst q
      rfl
    · subst q
      rfl
    · subst q
      rfl
    · subst q
      rfl


private def qFrameB : SectorFrame qRing qConfig where
  left := q5
  right := q0
  gap := 2
  gap_pos := by decide
  gap_lt_n := by decide
  left_ne_right := by decide
  right_eq := by rfl
  left_leader := by rfl
  right_leader := by rfl
  interior_follower := by
    intro q hq0 hq2
    have hq : q = 1 := by omega
    subst q
    rfl


private def qFrame : TripleFrame qRing qConfig where
  i := q0
  j := q5
  k := q0
  a := 5
  b := 2
  A := qFrameA
  B := qFrameB
  A_left := rfl
  A_right := rfl
  A_gap := rfl
  B_left := rfl
  B_right := rfl
  B_gap := rfl
  span := Or.inl (And.intro rfl rfl)


/-! The Boolean PB mirror is the finite witness checker. -/


private theorem qConfig_pbB :
    PPL.Elim.pbB qRing qConfig = true := by
  decide


private theorem qConfig_pb : PPL.Elim.PB qRing qConfig :=
  (PPL.Elim.pbB_true_iff qRing qConfig).1 qConfig_pbB


private theorem qConfig_good : AttemptGood qRing qFrame qConfig :=
  attemptGood_initial qRing qConfig qConfig_pb qFrame


/-!
Only the cells needed to rule out a tagged deletion before the first bad
edge are frozen.  Cell 6 and all non-leader fields at cell 5 may evolve.
-/
private def qSafe (C : Config 7) : Prop :=
  And (C q0 = qLeaderCell)
    (And (C q1 = qFollowerCell)
      (And (C q2 = qFollowerCell)
        (And (C q3 = qFollowerCell)
          (And (C q4 = qFollowerCell)
            ((C q5).leader = true)))))


/-- Pure Boolean mirror used for finite witness evaluation. -/
private def qSafeB (C : Config 7) : Bool :=
  decide (C q0 = qLeaderCell) &&
    decide (C q1 = qFollowerCell) &&
    decide (C q2 = qFollowerCell) &&
    decide (C q3 = qFollowerCell) &&
    decide (C q4 = qFollowerCell) &&
    decide ((C q5).leader = true)


private theorem qSafeB_true_iff (C : Config 7) :
    qSafeB C = true ↔ qSafe C := by
  simp only [qSafeB, qSafe, Bool.and_eq_true, decide_eq_true_eq,
    and_assoc]


private theorem qSafe_initial : qSafe qConfig := by
  apply (qSafeB_true_iff qConfig).1
  decide


@[simp] private theorem rowE_right_qLeader
    (l : PPL.Elim.Cell4) :
    (PPL.Elim.rowE l qLeaderCell).2 = qLeaderCell := by
  rcases l with ⟨ll, lb, lsh, lsb⟩
  rcases lb with ⟨v, hv⟩
  rcases v with _ | _ | _ | v
  · cases ll <;> cases lsh <;> cases lsb <;>
      simp [qLeaderCell, PPL.Elim.rowE]
  · cases ll <;> cases lsh <;> cases lsb <;>
      simp [qLeaderCell, PPL.Elim.rowE]
  · cases ll <;> cases lsh <;> cases lsb <;>
      simp [qLeaderCell, PPL.Elim.rowE]
  · omega


private theorem rowE_qFollower_right_leader
    (r : PPL.Elim.Cell4) (hr : r.leader = true) :
    (PPL.Elim.rowE qFollowerCell r).2.leader = true := by
  rcases r with ⟨rl, rb, rsh, rs⟩
  cases rl <;> cases rs <;>
    simp_all [qFollowerCell, PPL.Elim.rowE]


private theorem qStep_other
    (C : Config 7) (e k : Fin 7)
    (hke : k ≠ e)
    (hkr : k ≠ qRing.rightNeighbor e) :
    stepE qRing C e k = C k := by
  simp [stepE, PopulationProtocol.step, hke, hkr]


private theorem qStep5_leader
    (C : Config 7) (h5 : (C q5).leader = true) :
    ((stepE qRing C q5) q5).leader = true := by
  have h :=
    PPL.Elim.rowE_left_leader (C q5) (C q6)
  have hout :
      (PPL.Elim.rowE (C q5) (C q6)).1.leader = true :=
    h.trans h5
  simpa [stepE, PopulationProtocol.step, PPL.Elim.protocolE,
    DirectedRing.rightNeighbor, qRing, q5, q6] using hout


private theorem qStep6_zero
    (C : Config 7) (h0 : C q0 = qLeaderCell) :
    stepE qRing C q6 q0 = qLeaderCell := by
  have h0' : C (0 : Fin 7) = qLeaderCell := by
    exact h0
  simp [stepE, PopulationProtocol.step, PPL.Elim.protocolE,
    DirectedRing.rightNeighbor, qRing, q0, q6, h0',
    rowE_right_qLeader]


private theorem fin7_cases (e : Fin 7) :
    Or (e = q0)
      (Or (e = q1)
        (Or (e = q2)
          (Or (e = q3)
            (Or (e = q4)
              (Or (e = q5) (e = q6)))))) := by
  rcases e with ⟨v, hv⟩
  rcases v with _ | _ | _ | _ | _ | _ | _ | v
  · exact Or.inl (by apply Fin.ext; rfl)
  · exact Or.inr (Or.inl (by apply Fin.ext; rfl))
  · exact Or.inr (Or.inr (Or.inl (by apply Fin.ext; rfl)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl
      (by apply Fin.ext; rfl))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      (by apply Fin.ext; rfl)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      (by apply Fin.ext; rfl))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (by apply Fin.ext; rfl))))))
  · omega


private theorem qStep01
    (C : Config 7)
    (h0 : C q0 = qLeaderCell)
    (h1 : C q1 = qFollowerCell) :
    And (stepE qRing C q0 q0 = qLeaderCell)
      (stepE qRing C q0 q1 = qFollowerCell) := by
  have h0' : C (0 : Fin 7) = qLeaderCell := by
    exact h0
  have h1' : C (1 : Fin 7) = qFollowerCell := by
    exact h1
  simp [stepE, PopulationProtocol.step, PPL.Elim.protocolE,
    DirectedRing.rightNeighbor, qRing, q0, q1, h0', h1',
    qLeaderCell, qFollowerCell, PPL.Elim.rowE]


private theorem qStep12
    (C : Config 7)
    (h1 : C q1 = qFollowerCell)
    (h2 : C q2 = qFollowerCell) :
    And (stepE qRing C q1 q1 = qFollowerCell)
      (stepE qRing C q1 q2 = qFollowerCell) := by
  have h1' : C (1 : Fin 7) = qFollowerCell := by
    exact h1
  have h2' : C (2 : Fin 7) = qFollowerCell := by
    exact h2
  simp [stepE, PopulationProtocol.step, PPL.Elim.protocolE,
    DirectedRing.rightNeighbor, qRing, q1, q2, h1', h2',
    qFollowerCell, PPL.Elim.rowE]


private theorem qStep23
    (C : Config 7)
    (h2 : C q2 = qFollowerCell)
    (h3 : C q3 = qFollowerCell) :
    And (stepE qRing C q2 q2 = qFollowerCell)
      (stepE qRing C q2 q3 = qFollowerCell) := by
  have h2' : C (2 : Fin 7) = qFollowerCell := by
    exact h2
  have h3' : C (3 : Fin 7) = qFollowerCell := by
    exact h3
  simp [stepE, PopulationProtocol.step, PPL.Elim.protocolE,
    DirectedRing.rightNeighbor, qRing, q2, q3, h2', h3',
    qFollowerCell, PPL.Elim.rowE]


private theorem qStep34
    (C : Config 7)
    (h3 : C q3 = qFollowerCell)
    (h4 : C q4 = qFollowerCell) :
    And (stepE qRing C q3 q3 = qFollowerCell)
      (stepE qRing C q3 q4 = qFollowerCell) := by
  have h3' : C (3 : Fin 7) = qFollowerCell := by
    exact h3
  have h4' : C (4 : Fin 7) = qFollowerCell := by
    exact h4
  simp [stepE, PopulationProtocol.step, PPL.Elim.protocolE,
    DirectedRing.rightNeighbor, qRing, q3, q4, h3', h4',
    qFollowerCell, PPL.Elim.rowE]


private theorem qSafe_step_of_ne4
    (C : Config 7) (hSafe : qSafe C)
    (e : Fin 7) (hne : e ≠ q4) :
    qSafe (stepE qRing C e) := by
  rcases hSafe with ⟨h0, h1, h2, h3, h4, h5⟩
  rcases fin7_cases e with he | he | he | he | he | he | he
  · subst e
    have hp := qStep01 C h0 h1
    refine ⟨hp.1, hp.2, ?_, ?_, ?_, ?_⟩
    · exact (qStep_other C q0 q2 (by decide) (by decide)).trans h2
    · exact (qStep_other C q0 q3 (by decide) (by decide)).trans h3
    · exact (qStep_other C q0 q4 (by decide) (by decide)).trans h4
    · have hh := qStep_other C q0 q5 (by decide) (by decide)
      rw [hh]
      exact h5
  · subst e
    have hp := qStep12 C h1 h2
    refine ⟨?_, hp.1, hp.2, ?_, ?_, ?_⟩
    · exact (qStep_other C q1 q0 (by decide) (by decide)).trans h0
    · exact (qStep_other C q1 q3 (by decide) (by decide)).trans h3
    · exact (qStep_other C q1 q4 (by decide) (by decide)).trans h4
    · have hh := qStep_other C q1 q5 (by decide) (by decide)
      rw [hh]
      exact h5
  · subst e
    have hp := qStep23 C h2 h3
    refine ⟨?_, ?_, hp.1, hp.2, ?_, ?_⟩
    · exact (qStep_other C q2 q0 (by decide) (by decide)).trans h0
    · exact (qStep_other C q2 q1 (by decide) (by decide)).trans h1
    · exact (qStep_other C q2 q4 (by decide) (by decide)).trans h4
    · have hh := qStep_other C q2 q5 (by decide) (by decide)
      rw [hh]
      exact h5
  · subst e
    have hp := qStep34 C h3 h4
    refine ⟨?_, ?_, ?_, hp.1, hp.2, ?_⟩
    · exact (qStep_other C q3 q0 (by decide) (by decide)).trans h0
    · exact (qStep_other C q3 q1 (by decide) (by decide)).trans h1
    · exact (qStep_other C q3 q2 (by decide) (by decide)).trans h2
    · have hh := qStep_other C q3 q5 (by decide) (by decide)
      rw [hh]
      exact h5
  · exact (hne he).elim
  · subst e
    refine ⟨?_, ?_, ?_, ?_, ?_, qStep5_leader C h5⟩
    · exact (qStep_other C q5 q0 (by decide) (by decide)).trans h0
    · exact (qStep_other C q5 q1 (by decide) (by decide)).trans h1
    · exact (qStep_other C q5 q2 (by decide) (by decide)).trans h2
    · exact (qStep_other C q5 q3 (by decide) (by decide)).trans h3
    · exact (qStep_other C q5 q4 (by decide) (by decide)).trans h4
  · subst e
    refine ⟨qStep6_zero C h0, ?_, ?_, ?_, ?_, ?_⟩
    · exact (qStep_other C q6 q1 (by decide) (by decide)).trans h1
    · exact (qStep_other C q6 q2 (by decide) (by decide)).trans h2
    · exact (qStep_other C q6 q3 (by decide) (by decide)).trans h3
    · exact (qStep_other C q6 q4 (by decide) (by decide)).trans h4
    · have hh := qStep_other C q6 q5 (by decide) (by decide)
      rw [hh]
      exact h5


private theorem qSafe_notDeleted
    (C : Config 7) (hSafe : qSafe C) :
    ¬ TaggedDeleted qFrame C := by
  rcases hSafe with ⟨h0, h1, h2, h3, h4, h5⟩
  have hi : (C q0).leader = true := by
    rw [h0]
    rfl
  change
    ¬ Or ((C q0).leader = false)
      (Or ((C q5).leader = false) ((C q0).leader = false))
  intro hdel
  rcases hdel with hdel | hdel | hdel
  · rw [hi] at hdel
    cases hdel
  · rw [h5] at hdel
    cases hdel
  · rw [hi] at hdel
    cases hdel


private theorem qBadEdge_notDeleted
    (C : Config 7) (hSafe : qSafe C) :
    ¬ TaggedDeleted qFrame (stepE qRing C q4) := by
  rcases hSafe with ⟨h0, h1, h2, h3, h4, h5⟩
  have hi : ((stepE qRing C q4) q0).leader = true := by
    have hh := qStep_other C q4 q0 (by decide) (by decide)
    rw [hh, h0]
    rfl
  have h4' : C (4 : Fin 7) = qFollowerCell := by
    exact h4
  have h5' : (C (5 : Fin 7)).leader = true := by
    exact h5
  have hj : ((stepE qRing C q4) q5).leader = true := by
    have hrow :=
      rowE_qFollower_right_leader (C (5 : Fin 7)) h5'
    simpa [stepE, PopulationProtocol.step, PPL.Elim.protocolE,
      DirectedRing.rightNeighbor, qRing, q4, q5, h4'] using hrow
  change
    ¬ Or (((stepE qRing C q4) q0).leader = false)
      (Or (((stepE qRing C q4) q5).leader = false)
        (((stepE qRing C q4) q0).leader = false))
  intro hdel
  rcases hdel with hdel | hdel | hdel
  · rw [hi] at hdel
    cases hdel
  · rw [hj] at hdel
    cases hdel
  · rw [hi] at hdel
    cases hdel


@[simp] private theorem nextSectorPhase_ret_zero
    {n : Nat} {ring : DirectedRing n} {C0 : Config n}
    (A : SectorFrame ring C0) (e : Fin n) :
    nextSectorPhase A (.ret 0) e = .ret 0 := by
  simp [nextSectorPhase]


private theorem qAdvanceA4 :
    advance qRing qFrame.A.left 4 = q4 := by
  rfl


private theorem qHit_iff (e : Fin 7) :
    (Exists fun p =>
      And ((.live 4 : SectorPhase) = .live p)
        (And (e = advance qRing qFrame.A.left p)
          (p + 1 = qFrame.a))) ↔
      e = q4 := by
  constructor
  · rintro ⟨p, hp, he, hend⟩
    cases hp
    exact he.trans qAdvanceA4
  · intro he
    subst e
    exact Exists.intro 4
      (And.intro rfl
        (And.intro qAdvanceA4.symm rfl))


private theorem qNextA_live4_of_ne4
    (e : Fin 7) (hne : e ≠ q4) :
    nextSectorPhase qFrame.A (.live 4) e = .live 4 := by
  have hs : e ≠ advance qRing qFrame.A.left 4 := by
    intro h
    exact hne (h.trans qAdvanceA4)
  simp [nextSectorPhase, hs]


private def qRaceState
    (C : Config 7) (hgood : AttemptGood qRing qFrame C) :
    LongAttemptState qRing qFrame :=
  .live C hgood (.race (.ret 0) (.live 4))


@[simp] private theorem qRace_handoff
    (C : Config 7) (hgood : AttemptGood qRing qFrame C) :
    longProgressHandoffCut qRing qFrame (qRaceState C hgood) = true := rfl


@[simp] private theorem qRace_notWon
    (C : Config 7) (hgood : AttemptGood qRing qFrame C) :
    longRaceWonCut qRing qFrame (qRaceState C hgood) = false := rfl


@[simp] private theorem qRace_notRecovery
    (C : Config 7) (hgood : AttemptGood qRing qFrame C) :
    longRecoveryCut qRing qFrame (qRaceState C hgood) = false := rfl


private theorem qRace_step_ne4
    (C : Config 7) (hgood : AttemptGood qRing qFrame C)
    (hSafe : qSafe C) (e : Fin 7) (hne : e ≠ q4) :
    Exists fun hgoodD : AttemptGood qRing qFrame (stepE qRing C e) =>
      (longAttemptKernel qRing qFrame).step (qRaceState C hgood) e =
        .active (qRaceState (stepE qRing C e) hgoodD) := by
  have hSafeD := qSafe_step_of_ne4 C hSafe e hne
  have htag := qSafe_notDeleted (stepE qRing C e) hSafeD
  have hgoodD : AttemptGood qRing qFrame (stepE qRing C e) :=
    attemptGood_step qRing qFrame C e hgood htag
  have hready : (.ret 0 : SectorPhase) ≠ .ready := by
    intro h
    cases h
  have hhit :
      ¬ (Exists fun p =>
        And ((.live 4 : SectorPhase) = .live p)
          (And (e = advance qRing qFrame.A.left p)
            (p + 1 = qFrame.a))) := by
    intro h
    exact hne ((qHit_iff e).1 h)
  have hcond :
      ¬ And (e = advance qRing qFrame.A.left 4)
        (5 = qFrame.a) := by
    intro h
    exact hne (h.1.trans qAdvanceA4)
  have htarget :
      nextSectorPhase qFrame.B (.ret 0) e ≠ .ready := by
    simp
  refine Exists.intro hgoodD ?_
  simp [longAttemptKernel, longStep, qRaceState,
    htag, hready, hhit, hcond, htarget,
    qNextA_live4_of_ne4 e hne]


private theorem qRace_bad_branch_zero
    (C : Config 7) (hgood : AttemptGood qRing qFrame C)
    (hSafe : qSafe C) (T : Nat) :
    longCutCount
        (longAttemptKernel qRing qFrame)
        (longRaceWonCut qRing qFrame)
        (longRecoveryCut qRing qFrame)
        ((longAttemptKernel qRing qFrame).step
          (qRaceState C hgood) q4) T = 0 := by
  have htag := qBadEdge_notDeleted C hSafe
  have hready : (.ret 0 : SectorPhase) ≠ .ready := by
    intro h
    cases h
  have hcond :
      And (q4 = advance qRing qFrame.A.left 4)
        (5 = qFrame.a) :=
    And.intro qAdvanceA4.symm rfl
  have htag' :
      ¬ TaggedDeleted qFrame
        (stepE qRing C (advance qRing qFrame.A.left 4)) := by
    rw [qAdvanceA4]
    exact htag
  cases T with
  | zero =>
      simp [longAttemptKernel, longStep, qRaceState,
        htag, htag', hready, hcond, longCutCount,
        longRaceWonCut, longRecoveryCut,
        Bool.false_eq_true]
  | succ T =>
      simp [longAttemptKernel, longStep, qRaceState,
        htag, htag', hready, hcond, longCutCount,
        longRaceWonCut, longRecoveryCut,
        Bool.false_eq_true]


/-! Recursive List.ofFn finite-sum brick used by the fixed Fin 7 count. -/


private theorem q_ofFn_sum_const (m x : Nat) :
    (List.ofFn (fun _ : Fin m => x)).sum = m * x := by
  induction m with
  | zero =>
      simp
  | succ m ih =>
      rw [List.ofFn_succ, List.sum_cons, ih, Nat.succ_mul]
      exact Nat.add_comm _ _


private theorem q_six_copies (x : Nat) :
    x + (x + (x + (x + (x + x)))) = x * 6 := by
  have h := q_ofFn_sum_const 6 x
  rw [Nat.mul_comm 6 x] at h
  simpa [List.ofFn_succ, List.sum_cons] using h


private theorem fin7_sum_avoid4 (x : Nat) :
    (List.ofFn (fun e : Fin 7 => if e = q4 then 0 else x)).sum =
      x * 6 := by
  simpa [List.ofFn_succ, List.sum_cons, q4] using q_six_copies x


private theorem qRaceMassFrom_eq_six_pow :
    forall T (C : Config 7)
      (hgood : AttemptGood qRing qFrame C),
      qSafe C ->
      longRaceMassFrom qRing qFrame (qRaceState C hgood) T =
        6 ^ T := by
  intro T
  induction T with
  | zero =>
      intro C hgood hSafe
      rfl
  | succ T ih =>
      intro C hgood hSafe
      change
        (List.ofFn (fun e : Fin 7 =>
          longCutCount
            (longAttemptKernel qRing qFrame)
            (longRaceWonCut qRing qFrame)
            (longRecoveryCut qRing qFrame)
            ((longAttemptKernel qRing qFrame).step
              (qRaceState C hgood) e) T)).sum =
          6 ^ (T + 1)
      have hterm :
          forall e : Fin 7,
            longCutCount
                (longAttemptKernel qRing qFrame)
                (longRaceWonCut qRing qFrame)
                (longRecoveryCut qRing qFrame)
                ((longAttemptKernel qRing qFrame).step
                  (qRaceState C hgood) e) T =
              if e = q4 then 0 else 6 ^ T := by
        intro e
        by_cases he : e = q4
        · subst e
          rw [if_pos rfl]
          exact qRace_bad_branch_zero C hgood hSafe T
        · rw [if_neg he]
          obtain ⟨hgoodD, hstep⟩ :=
            qRace_step_ne4 C hgood hSafe e he
          rw [hstep]
          have hSafeD := qSafe_step_of_ne4 C hSafe e he
          have hmass :=
            ih (stepE qRing C e) hgoodD hSafeD
          simpa [longRaceMassFrom] using hmass
      calc
        (List.ofFn (fun e : Fin 7 =>
          longCutCount
            (longAttemptKernel qRing qFrame)
            (longRaceWonCut qRing qFrame)
            (longRecoveryCut qRing qFrame)
            ((longAttemptKernel qRing qFrame).step
              (qRaceState C hgood) e) T)).sum
            =
          (List.ofFn (fun e : Fin 7 =>
            if e = q4 then 0 else 6 ^ T)).sum :=
              ofFn_sum_eq _ _ hterm
        _ = (6 ^ T) * 6 := fin7_sum_avoid4 (6 ^ T)
        _ = 6 ^ (T + 1) := (Nat.pow_succ 6 T).symm


theorem q19593_progress_counterexample_mass :
    longRaceMassFrom qRing qFrame
      (qRaceState qConfig qConfig_good) 5 = 7776 := by
  have h :=
    qRaceMassFrom_eq_six_pow 5 qConfig qConfig_good qSafe_initial
  simpa using h


/-- Machine-checkable refutation of the current residual. -/
theorem longAttemptConcreteStageFactorSpec_false :
    ¬ LongAttemptConcreteStageFactorSpec := by
  intro hstage
  have hb : 2 <= qFrame.b := by
    change 2 <= 2
    decide
  have hab : 2 * qFrame.b + 1 <= qFrame.a := by
    change 5 <= 5
    decide
  have hrows :=
    hstage sealedStepSpec qRing qFrame hb hab
  have hhalf :=
    hrows.2.1
      (qRaceState qConfig qConfig_good)
      (qRace_handoff qConfig qConfig_good)
      5
  rw [q19593_progress_counterexample_mass] at hhalf
  have hnot : ¬ ((7 : Nat) ^ 5 <= 2 * 7776) := by
    decide
  exact hnot hhalf


#print axioms PPL.Convergence.LDLocal.q19593_progress_counterexample_mass
#print axioms PPL.Convergence.LDLocal.longAttemptConcreteStageFactorSpec_false


end PPL.Convergence.LDLocal


