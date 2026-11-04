import Leader.PPL.Modes.MidEntryLeaderWaveRows


namespace PPL.Modes.Lemma5


set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false


open PPL.Probability
open PPL.Modes.SignalLineage
open PPL.Modes.Lemma9


/--
The appended scheduler letter is not the live reset frontier.
The Wave host therefore stays put, the next selected rotated edge is still
missing, and all earlier reset witnesses persist.
-/
def Lemma5iWaveResetFrontierAwayRow : Prop :=
  ∀ {n psi kappa : Nat}
    (hn3 : 3 ≤ n)
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (D : Config n psi kappa)
    (pre : DetSchedule n)
    (e : Fin n),
    Lemma5iLeaderWaveActivePrefix ring D pre →
    Lemma5iLeaderWaveResetFrontierAt ring D pre →
    e ≠ lemma5iLeaderWaveHost ring D pre →
    Lemma5iLeaderWaveResetFrontierAt
      ring D (pre ++ [e])


/--
The appended scheduler letter is exactly the live frontier and there is
another selected rotated edge after it.  This interaction records the q-th
reset witness and advances the frontier by exactly one.
-/
def Lemma5iWaveResetFrontierHitContinueRow : Prop :=
  ∀ {n psi kappa : Nat}
    (hn3 : 3 ≤ n)
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (D : Config n psi kappa)
    (pre : DetSchedule n)
    (e : Fin n)
    (q : Nat),
    Lemma5iLeaderWaveActivePrefix ring D pre →
    q < n →
    lemma5iLeaderWaveHost ring D pre =
      PPL.shiftRight ring
        (lemma5iLeaderWaveStart ring D) q →
    (PPL.seqR ring
        (lemma5iLeaderWaveStart ring D) q).Sublist pre →
    ¬ (PPL.seqR ring
        (lemma5iLeaderWaveStart ring D) (q + 1)).Sublist pre →
    (∀ j : Nat,
      j < q →
        Lemma5iLeaderWaveResetWitness
          ring D
          (lemma5iLeaderWaveStart ring D)
          pre j) →
    e = lemma5iLeaderWaveHost ring D pre →
    q + 1 < n →
    Lemma5iLeaderWaveResetFrontierAt
      ring D (pre ++ [e])


/--
The appended scheduler letter is the last selected rotated edge.
It records the last reset witness, completes the rotated word, and the n
selected reset witnesses imply that every site has seen a clock reset.
-/
def Lemma5iWaveResetFrontierHitFinishRow : Prop :=
  ∀ {n psi kappa : Nat}
    (hn3 : 3 ≤ n)
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (D : Config n psi kappa)
    (pre : DetSchedule n)
    (e : Fin n)
    (q : Nat),
    Lemma5iLeaderWaveActivePrefix ring D pre →
    q < n →
    lemma5iLeaderWaveHost ring D pre =
      PPL.shiftRight ring
        (lemma5iLeaderWaveStart ring D) q →
    (PPL.seqR ring
        (lemma5iLeaderWaveStart ring D) q).Sublist pre →
    ¬ (PPL.seqR ring
        (lemma5iLeaderWaveStart ring D) (q + 1)).Sublist pre →
    (∀ j : Nat,
      j < q →
        Lemma5iLeaderWaveResetWitness
          ring D
          (lemma5iLeaderWaveStart ring D)
          pre j) →
    e = lemma5iLeaderWaveHost ring D pre →
    q + 1 = n →
    (PPL.seqR ring
        (lemma5iLeaderWaveStart ring D) n).Sublist
          (pre ++ [e]) ∧
      allClockResetsSeenB ring D (pre ++ [e]) = true


/--
The requested one-step leaf follows from the three position-of-e rows.
No dead S3.11 residual is consumed here.
-/
theorem lemma5iLeaderWaveResetFrontierOneStep_of_routeRows
    (hAway : Lemma5iWaveResetFrontierAwayRow)
    (hContinue : Lemma5iWaveResetFrontierHitContinueRow)
    (hFinish : Lemma5iWaveResetFrontierHitFinishRow) :
    Lemma5iLeaderWaveResetFrontierOneStep := by
  unfold Lemma5iWaveResetFrontierAwayRow at hAway
  unfold Lemma5iWaveResetFrontierHitContinueRow at hContinue
  unfold Lemma5iWaveResetFrontierHitFinishRow at hFinish
  unfold Lemma5iLeaderWaveResetFrontierOneStep
  intro n psi kappa
  intro hn3 hpsi ring D pre e
  intro hactive hfront
  dsimp only


  by_cases he :
      e = lemma5iLeaderWaveHost ring D pre
  · unfold Lemma5iLeaderWaveResetFrontierAt at hfront
    dsimp only at hfront
    rcases hfront with
      ⟨q, hqn, hhost, hsub, hnext, hwit⟩


    by_cases hcont : q + 1 < n
    · exact
        Or.inr
          (Or.inr
            (hContinue
              hn3 hpsi ring D pre e q
              hactive hqn hhost hsub hnext hwit
              he hcont))
    · have hfinish : q + 1 = n := by
        omega
      exact
        Or.inr
          (Or.inl
            (hFinish
              hn3 hpsi ring D pre e q
              hactive hqn hhost hsub hnext hwit
              he hfinish))
  · exact
      Or.inr
        (Or.inr
          (hAway
            hn3 hpsi ring D pre e
            hactive hfront he))


end PPL.Modes.Lemma5


#print axioms PPL.Modes.Lemma5.lemma5iLeaderWaveResetFrontierOneStep_of_routeRows
