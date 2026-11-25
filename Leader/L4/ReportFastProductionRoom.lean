import Leader.L4.ReportFastRawEvent
import Leader.L4.AdviceBandRadiusBudget

namespace L4.ReportFastProductionRoom
open AllSizeProtocol ShortResetCycle ReportResetRawHooks
open ReportFastRawEvent

/-- The actual width cap leaves room for all five owner charts in
the production advice band, on both report sheets. -/
theorem production_five_room (d : Sheet) {n s B : Nat}
    (advice : s=ell (ell n)) (S : 6≤s) (Bound : B≤maxWidth d s) :
    4*B<n := by
  have W : maxWidth d s≤AdviceBandRadiusBudget.widthMax s := by
    have H : 1≤2*PhysicalCustody.radiusTwo s+1 := by omega
    have A : 81*(2*s+1)≤AdviceBandRadiusBudget.widthMax s := by
      simpa [AdviceBandRadiusBudget.widthMax] using Nat.mul_le_mul_left (81*(2*s+1)) H
    cases d
    · change 81≤AdviceBandRadiusBudget.widthMax s
      have K : 81≤81*(2*s+1) := by omega
      exact Nat.le_trans K A
    · exact A
  have V := AdviceBandRadiusBudget.width_below_486 S
  have E : s+11≤2^(s-1) := by
    have := AdviceBandRadiusBudget.exp_dominates S
    omega
  have N := ProductionH6Count.advice_lower (by omega) advice
  calc
    4*B ≤ 4*AdviceBandRadiusBudget.widthMax s := Nat.mul_le_mul_left 4 (Nat.le_trans Bound W)
    _ ≤ 2048*2^s := by omega
    _ = 2^(s+11) := by rw [Nat.pow_add,Nat.mul_comm]
    _ ≤ 2^(2^(s-1)) := Nat.pow_le_pow_right (by decide) E
    _ < n := N

end L4.ReportFastProductionRoom
