import Leader.L4.ControllerTapeIID

namespace L4.PhysicalRawClockTape

/-- Attach the exact sampled history to a raw-state hit clock. The
current tape must itself have the target endpoint; no old hit is retained. -/
theorem raw_endpoint_expected {X : Type} {n : Nat} (step : X→Fin n→X)
    (x : X) (A : X→Prop) (K : Nat)
    (H : Height.IIDExpectedHittingTimeAtMost step A x K) :
    Height.IIDExpectedHittingTimeAtMost ResetReturnIID.appendTape
      (fun w=>A (BStarResetSchedule.run step x w)) [] K := by
  classical
  let run := BStarResetSchedule.run step x
  let P := fun w=>A (run w)
  have compare (t : Nat) (w : List (Fin n)) :
      Height.iidHitCost ResetReturnIID.appendTape P t w ≤ Height.iidHitCost step A t (run w) := by
    induction t generalizing w with
    | zero => exact Nat.le_refl _
    | succ t ih =>
      by_cases hit : P w
      · rw [Height.iidHitCost_of_target _ _ _ hit]
        exact Nat.zero_le _
      · have noA : ¬A (run w) := hit
        simp only [Height.iidHitCost,if_neg hit,if_neg noA]
        apply Nat.add_le_add_left
        apply ControllerTapeIID.sum_mono
        intro e
        rw [←show run (ResetReturnIID.appendTape w e)=step (run w) e from
          BStarResetSchedule.run_append _ _ _ _]
        exact ih _
  intro t
  exact Nat.le_trans (compare t []) (H t)

end L4.PhysicalRawClockTape
