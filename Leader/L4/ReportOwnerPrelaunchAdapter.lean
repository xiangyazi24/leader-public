import Leader.L4.ReportOwnerReceiptClock
import Leader.L4.ReportPrelaunchClock

namespace L4.ReportOwnerPrelaunchAdapter
open AllSizeProtocol PhysicalCustody ReportResetRawHooks ReportOwnerResetDrain
open ShortResetCycle ShortResetChart ReportOwnerReceiptClock

variable {s n : Nat} {h : Fin n→Bool} {Q : Raw s n→Prop}

private def project (z : {x : Raw s n // Q x} × Bool) : Raw s n × Bool :=
  (z.1.val,z.2)

/-- Definitional only on the raw bytes; compare the two launch decisions
extensionally rather than identifying their Decidable instances. -/
theorem pre_project (d : Sheet) (C : Chart h) (F : Fibre (h:=h) d Q)
    (z : {x : Raw s n // Q x} × Bool) (e : Fin n) :
    project (preNext d C F z e) = ReportPrelaunchClock.preStep d C (project z) e := by
  apply Prod.ext
  · rfl
  · by_cases H : ReportPrelaunchClock.Launch d C z.1.val e <;>
      simp only [ReportPrelaunchClock.Launch] at H <;>
      simp [project,preNext,ReportPrelaunchClock.preStep,ReportPrelaunchClock.Launch,H]

private theorem pre_cost_raw (d : Sheet) (C : Chart h) (F : Fibre (h:=h) d Q)
    (t : Nat) (z : {x : Raw s n // Q x} × Bool) :
    Height.iidHitCost (preNext d C F) (fun y=>y.2=true) t z =
      Height.iidHitCost (ReportPrelaunchClock.preStep d C) (fun y=>y.2=true) t (project z) := by
  induction t generalizing z with
  | zero => rfl
  | succ t ih =>
    have A : ∀ e, Height.iidHitCost (preNext d C F) (fun y=>y.2=true) t (preNext d C F z e) =
        Height.iidHitCost (ReportPrelaunchClock.preStep d C) (fun y=>y.2=true) t
          (ReportPrelaunchClock.preStep d C (project z) e) := by
      intro e
      rw [ih,pre_project]
    cases S : z.2 <;> simp [Height.iidHitCost,project,A,S]

/-- Full literal per-owner clock once the local production
RowCases supplier is instantiated (no Good8 conclusion). -/
theorem owner_receipt_mean_of_row_cases (d : Sheet) (C : Chart h)
    (F : Fibre (h:=h) d Q) (N : 1<n) (x : {x : Raw s n // Q x})
    (B : Nat) (L : C.L≤B) (R : ReportPrelaunchClock.RowCases d C Q) :
    Height.IIDExpectedHittingTimeAtMost (next d C F) done (x,none)
      (n*ReportResetEventClock.resetCoefficient B (params d s).digits) := by
  apply owner_receipt_mean_of_polynomial d C F N x B L
  have W := ReportPrelaunchClock.prelaunch_mean d C Q F R x.val x.property
  intro t
  rw [pre_cost d C F t x,pre_cost_raw]
  have Z : ReportPrelaunchClock.preCap (s:=s) d C≤10*(B+4*(params d s).digits+7)^2 := by
    unfold ReportPrelaunchClock.preCap
    have E : C.L+(4*(params d s).digits+5)+2≤B+4*(params d s).digits+7 := by omega
    simpa only [Nat.pow_two] using Nat.mul_le_mul_left 10 (Nat.mul_le_mul E E)
  exact Nat.le_trans (W t) (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.add_le_add_right Z 1)))

#print axioms owner_receipt_mean_of_row_cases
#print axioms pre_project
end L4.ReportOwnerPrelaunchAdapter
