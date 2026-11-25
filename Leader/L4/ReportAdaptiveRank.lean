import Leader.L4.ReportAdaptiveProgress

namespace L4.ReportAdaptiveFibre
open Height

variable {X : Type} {n : Nat}

/-- Deterministic rank for a progress clock: every letter is harmless to
the old debt, and some current letter strictly reduces it. -/
structure Nomination (step : X→Fin n→X) (Q hit : X→Prop) (rank : X→Nat) : Prop where
  closed : ∀ x e,Q x→Q (step x e)
  idle : ∀ x e,Q x→¬hit x→rank (step x e)≤rank x
  progress : ∀ x,Q x→¬hit x→∃ e, rank (step x e)<rank x

theorem rank_drift (step : X→Fin n→X) (Q hit : X→Prop) (rank : X→Nat)
    (F : Nomination step Q hit rank) (x : X) (G : Q x) (H : ¬hit x) :
    n+(List.ofFn (fun e=>n*rank (step x e))).sum≤n*(n*rank x) := by
  obtain ⟨a,A⟩ := F.progress x G H
  have T (e : Fin n) : (if a=e then 1 else 0)+rank (step x e)≤rank x := by
    by_cases E : a=e
    · subst e
      simp only [if_true]
      omega
    · simpa only [if_neg E,Nat.zero_add] using F.idle x e G H
  have S := sum_ofFn_le _ _ T
  rw [sum_ofFn_add,sum_delta a (fun _=>1),sum_ofFn_const] at S
  rw [sum_ofFn_mul_left]
  conv => lhs; lhs; rw [←Nat.mul_one n]
  rw [←Nat.mul_add]
  exact Nat.mul_le_mul_left n S

theorem nominated_mean (step : X→Fin n→X) (Q hit : X→Prop) (rank : X→Nat)
    (F : Nomination step Q hit rank) (x : X) (G : Q x) :
    IIDExpectedHittingTimeAtMost step hit x (n*rank x) := by
  let M := closedNext step Q F.closed
  let ht := fun y : {x // Q x}=>hit y.1
  let b := fun y : {x // Q x}=>n*rank y.1
  intro t
  rw [←iidHitCost_closedNext step Q F.closed hit t ⟨x,G⟩]
  exact iidHitCost_le_of_budget M ht b
    (fun y E=>rank_drift step Q hit rank F y.1 y.2 E) t ⟨x,G⟩

/-- Auxiliary labels need not be uniform themselves: a nominated
allowed actual label merely needs one uniform DRIVER preimage. -/
theorem driver_nominated_mean (step : X→Fin n→X) (steer : X→Fin n→Fin n)
    (Q hit : X→Prop) (rank : X→Nat)
    (stay : ∀ x e,Q x→Q (step x e))
    (idle : ∀ x e,Q x→¬hit x→rank (step x (steer x e))≤rank x)
    (progress : ∀ x,Q x→¬hit x→
      ∃ a d, steer x d=a ∧ rank (step x a)<rank x)
    (x : X) (G : Q x) :
    IIDExpectedHittingTimeAtMost (driverStep step steer) hit x (n*rank x) := by
  refine nominated_mean (driverStep step steer) Q hit rank ⟨fun y e=>stay y (steer y e),idle,?_⟩ x G
  intro y Y H
  obtain ⟨a,d,D,A⟩ := progress y Y H
  refine ⟨d,?_⟩
  unfold driverStep
  rw [D]
  exact A

/-- One tracked transport edge costs no more than two waiting stages.
The raw adapter owns the irreversible no-rearm property encoded here
by a nonincreasing rank; it is not inferred from fairness. -/
theorem two_stage_wait (step : X→Fin n→X) (Q hit : X→Prop) (rank : X→Nat)
    (F : Nomination step Q hit rank) (x : X) (G : Q x) (R : rank x≤2) :
    IIDExpectedHittingTimeAtMost step hit x (2*n) := by
  intro t
  have F := nominated_mean step Q hit rank F x G t
  exact Nat.le_trans F (Nat.mul_le_mul_right _ (by rw [Nat.mul_comm 2 n]; exact Nat.mul_le_mul_left n R))

end L4.ReportAdaptiveFibre
