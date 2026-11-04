-- Leader/PPL/Modes/MidEntryResetModeCap.lean
import Leader.PPL.Modes.MidEntryLatestResetProjection
import Leader.PPL.Modes.ClockSuffixBridge
import Leader.PPL.Convergence.QuietWindow


namespace PPL.Modes.Lemma5


set_option autoImplicit false
set_option Elab.async false


open PPL.Probability


/-- Direct finishModes certificate at the DetermineMode boundary. -/
private theorem q19701_determineMode_cap
    {psi kappa : Nat}
    (l r : PPL.State psi kappa) :
    let d := PPL.determineMode l r
    And
      (d.1.mode = true ->
        d.1.clock.val = kappa)
      (d.2.mode = true ->
        d.2.clock.val = kappa) := by
  simp only [PPL.determineMode]
  repeat' (split <;> try dsimp only)
  all_goals
    unfoldFinishModes
    dsimp only
    apply And.intro
    · intro hm
      simpa using hm
    · intro hm
      simpa using hm


/-- Algorithms 2/3/5 preserve the mode/clock certificate written by
DetermineMode. -/
private theorem q19701_ppl_cap
    {psi kappa : Nat}
    (hpsi : 2 <= psi)
    (l r : PPL.State psi kappa) :
    let q := PPL.ppl hpsi l r
    And
      (q.1.mode = true ->
        q.1.clock.val = kappa)
      (q.2.mode = true ->
        q.2.clock.val = kappa) := by
  have hm :=
    PPL.Convergence.ConstructCoupling.postDetermineModeModeStable
      hpsi l r
  have hc :=
    PPL.Probability.clockSuffixPairProjection
      hpsi l r
  have hd :=
    q19701_determineMode_cap l r
  dsimp only at hm hc hd ⊢
  apply And.intro
  · intro hmode
    have hdm :
        (PPL.determineMode l r).1.mode = true :=
      hm.1.symm.trans hmode
    have hdcap :
        (PPL.determineMode l r).1.clock.val = kappa :=
      hd.1 hdm
    exact
      (congrArg Fin.val hc.1).trans hdcap
  · intro hmode
    have hdm :
        (PPL.determineMode l r).2.mode = true :=
      hm.2.symm.trans hmode
    have hdcap :
        (PPL.determineMode l r).2.clock.val = kappa :=
      hd.2 hdm
    exact
      (congrArg Fin.val hc.2.2.1).trans hdcap


theorem lemma5iMidResetModeCapStep_proved :
    Lemma5iMidResetModeCapStep := by
  unfold Lemma5iMidResetModeCapStep
  intro n psi kappa hpsi ring C x e hreset hmode


  have hreset' := hreset
  unfold clockResetAt at hreset'
  dsimp only at hreset'
  have hinc :
      x = e ∨ x = ring.rightNeighbor e :=
    (of_decide_eq_true hreset').1


  by_cases hxe : x = e
  · subst x
    have hcap :=
      q19701_ppl_cap
        hpsi (C e) (C (ring.rightNeighbor e))
    dsimp only at hcap
    have hstep :
        pplStep ring C e e =
          (PPL.ppl hpsi
            (C e) (C (ring.rightNeighbor e))).1 := by
      simp [pplStep, PopulationProtocol.step,
        PPL.protocol, PPL.transition, hpsi]
    rw [hstep] at hmode ⊢
    exact hcap.1 hmode
  · have hxj :
        x = ring.rightNeighbor e := by
      rcases hinc with h | h
      · exact False.elim (hxe h)
      · exact h
    subst x
    have hcap :=
      q19701_ppl_cap
        hpsi (C e) (C (ring.rightNeighbor e))
    dsimp only at hcap
    have hstep :
        pplStep ring C e (ring.rightNeighbor e) =
          (PPL.ppl hpsi
            (C e) (C (ring.rightNeighbor e))).2 := by
      simp [pplStep, PopulationProtocol.step,
        PPL.protocol, PPL.transition, hpsi, hxe]
    rw [hstep] at hmode ⊢
    exact hcap.2 hmode


end PPL.Modes.Lemma5


#print axioms PPL.Modes.Lemma5.lemma5iMidResetModeCapStep_proved
