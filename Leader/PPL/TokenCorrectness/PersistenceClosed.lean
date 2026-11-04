import Leader.PPL.TokenCorrectness.PersistenceStep
import Leader.PPL.TokenCorrectness.PersistenceCarry

/-!
# P_PL Remark 2 one-step: the line-29 microlemma discharged

Remark2NegTurnCarry (TokenCorrectnessRemark2Step) is the line-29 turn fact
proved as remark2_negTurn_preserves_correct (TokenCorrectnessRemark2Carry).
The one-step statement then depends only on Remark2SurvivorFrame.
-/

namespace PPL

set_option autoImplicit false

theorem remark2NegTurnValue_eq_next {psi : Nat} (hpsi : 2 <= psi)
    (b : Bool) (t : TokenData psi) :
    remark2NegTurnValue hpsi b t = remark2NegTurnNext hpsi b t := by
  rfl

theorem remark2NegTurnCarry_proved : Remark2NegTurnCarry := by
  intro n psi kappa hpsi ring root seg C C' e i kind t
    hstep hri htok hcneg hpost hvalid hwork hcorr hC hC' hsrc
  have hn3 : 3 <= n := by
    have hs := seg.isLt
    have h3 : 3 <= segmentCount n psi := by omega
    unfold segmentCount at h3
    cases Nat.lt_or_ge n 3 with
    | inl hn =>
        have hlt : (n + psi - 1) / psi < 2 :=
          (Nat.div_lt_iff_lt_mul (by omega)).2 (by omega)
        omega
    | inr hn => exact hn
  exact
    remark2_negTurn_preserves_correct hpsi hn3 ring root seg C C' e i kind t
      hvalid hwork hcorr hC hC' hsrc
      ⟨hstep, hri.symm, htok, hcneg,
        by rw [hpost, remark2NegTurnValue_eq_next]⟩

/-- Remark 2 one-step, with only the survivor frame left open. -/
theorem remark2_one_step_unique_of_survivorFrame
    (hframe : Remark2SurvivorFrame) :
    remark2_one_step_unique :=
  remark2_one_step_unique_of_negTurn remark2NegTurnCarry_proved hframe

end PPL

#print axioms PPL.remark2NegTurnCarry_proved
#print axioms PPL.remark2_one_step_unique_of_survivorFrame
