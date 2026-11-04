import Leader.PPL.Elim.AttemptLongTargetCleanReadyDone

namespace PPL.Convergence.LDLocal

set_option autoImplicit false
set_option Elab.async false

open FiniteUniformStoppingTree

/-!
# First-cut first-progress race factor

Truth audit.

The counterexample to the corrected spec is not a first-cut state.  Its bad state
  .race (.live 1) (.live 4)
is reached only after three further race interactions following the literal
first race handoff
  .race (.live 1) (.live 1).
RetryFirstCutReachable excludes exactly those post-cut descendants.

At an actual first race handoff, longStep enters .race only from liveWait or
advance.  The source phase arithmetic is the intended balanced race: the
target needs at most 2*b-1 further services while the attacker has the 2*b
budget.  The repository already proves the finite-tree counting leaf
counterRace_first_or_active_half for an equal-counter predictable two-target
race.

What is not yet exported on main is the refinement from the literal first-cut
longStep state to that abstract counter race.  The single residual below is
only that refinement/dominance statement.  It does not assume the desired
half inequality.
-/

/--
Exact missing refinement at a first .race handoff.

For every literal first-progress race state, produce an equal-counter
PredictableCounterRaceFiniteTree race of width 2*b whose active-or-success
mass is bounded above by the literal longRaceMassFrom.  The intended producer
uses the first-handoff shape of longStep together with SealedStepSpec and
nextSectorPhase.  Once this refinement is supplied,
counterRace_first_or_active_half proves the factor two.
-/
def LongFirstProgressRaceCounterRefinement : Prop :=
  forall (hSealed : SealedStepSpec),
    forall {n : Nat} (ring : DirectedRing n)
      {C0 : Config n} (F : TripleFrame ring C0),
      2 <= F.b ->
      2 * F.b + 1 <= F.a ->
      forall s C (hgood : AttemptGood ring F C)
        (targetPhase attackPhase : SectorPhase),
        LongAttemptFirstProgressGood ring F s
          (.live C hgood (.race targetPhase attackPhase)) ->
        Exists fun st :
            PredictableCounterRaceFiniteTree.ActiveRaceState
              (LongAttemptState ring F) (2 * F.b) =>
          And
            (st.firstHits = st.secondHits)
            (Exists fun first :
                LongAttemptState ring F -> Fin n =>
              Exists fun second :
                  LongAttemptState ring F -> Fin n =>
                Exists fun next :
                    LongAttemptState ring F -> Fin n ->
                      LongAttemptState ring F =>
                  And
                    (forall x, Not (first x = second x))
                    (forall T,
                      activeCount
                          (PredictableCounterRaceFiniteTree.counterRaceStep
                            first second next)
                          (.active st) T +
                        successCount
                          (PredictableCounterRaceFiniteTree.counterRaceStep
                            first second next)
                          (.active st) T <=
                        longRaceMassFrom ring F
                          (.live C hgood
                            (.race targetPhase attackPhase)) T))

/--
Conjunct 2 of LongAttemptFirstCutStageFactorSpec, reduced to the single
first-race refinement above.

incident and retained are already longRaceWonCut states, so longCutCount pads
the whole remaining scheduler suffix and their inequality is immediate.
All other LongStage constructors have longProgressHandoffCut = false.
-/
theorem longRaceFactor_proved
    (hrefine : LongFirstProgressRaceCounterRefinement) :
    forall (hSealed : SealedStepSpec),
      forall {n : Nat} (ring : DirectedRing n)
        {C0 : Config n} (F : TripleFrame ring C0),
        2 <= F.b ->
        2 * F.b + 1 <= F.a ->
        forall s a,
          LongAttemptFirstProgressGood ring F s a ->
          longProgressHandoffCut ring F a = true ->
          forall T,
            n ^ T <= 2 * longRaceMassFrom ring F a T := by
  intro hSealed n ring C0 F hb hab
  intro s a hfirst hcut T
  cases a with
  | junk C =>
      simp [longProgressHandoffCut] at hcut
  | live C hgood stage =>
      cases stage with
      | targetCR mode =>
          simp [longProgressHandoffCut] at hcut
      | attackerCR targetPhase mode =>
          simp [longProgressHandoffCut] at hcut
      | liveWait targetPhase attackPhase =>
          simp [longProgressHandoffCut] at hcut
      | advance targetPhase attackPhase =>
          simp [longProgressHandoffCut] at hcut
      | race targetPhase attackPhase =>
          obtain
              ⟨st, hcounters, first, second, next,
                hdistinct, hdom⟩ :=
            hrefine hSealed ring F hb hab
              s C hgood targetPhase attackPhase hfirst
          have hhalf :=
            counterRace_first_or_active_half
              first second next hdistinct st hcounters T
          have hdom2 :=
            Nat.mul_le_mul_left 2 (hdom T)
          exact Nat.le_trans hhalf hdom2
      | incident attackPhase =>
          have hmass :
              longRaceMassFrom ring F
                  (.live C hgood (.incident attackPhase)) T =
                n ^ T := by
            cases T <;>
              simp [longRaceMassFrom, longCutCount, longRaceWonCut]
          rw [hmass]
          have htwo : 1 <= (2 : Nat) := by omega
          have hm :=
            Nat.mul_le_mul_right (n ^ T) htwo
          simpa using hm
      | retained targetPhase attackPhase =>
          have hmass :
              longRaceMassFrom ring F
                  (.live C hgood
                    (.retained targetPhase attackPhase)) T =
                n ^ T := by
            cases T <;>
              simp [longRaceMassFrom, longCutCount, longRaceWonCut]
          rw [hmass]
          have htwo : 1 <= (2 : Nat) := by omega
          have hm :=
            Nat.mul_le_mul_right (n ^ T) htwo
          simpa using hm
      | recovery targetPhase attackPhase =>
          simp [longProgressHandoffCut] at hcut
      | stuck =>
          simp [longProgressHandoffCut] at hcut

end PPL.Convergence.LDLocal

#print axioms PPL.Convergence.LDLocal.longRaceFactor_proved
