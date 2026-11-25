import Leader.L4.ReportStageMeans
import Leader.L4.ReportWidthHandoff
import Leader.L4.WidthProductionQuadratic
import Leader.L4.PhysicalOwnerCustody

namespace L4.PhysicalCustodyAssembly
set_option exponentiation.threshold 40575
set_option Elab.async false
noncomputable section
open AllSizeProtocol PhysicalCustody ShortMISLift ShortMISPublicationClosed ShortMIS3Entrance
open ShortH2Final ReportStageMeans ReportStageInputs ReportWidthHandoff
open ReportResetRawHooks ReportServiceMesh ReportRawTrialSticky
open WidthPackedBridge WidthProductionEntrance AdviceBandRadiusBudget PhysicalOwnerCustody

variable {s n : Nat}

noncomputable def K_mis : Nat := (5+2*6^9) + (10^8095+19+2*publicationScale) + (K_H3+K_H4)

noncomputable def K_packed (Kreport : Nat) : Nat := K_mis + (Kreport + 5122)

noncomputable def K_custody (Kreport : Nat) : Nat := K_packed Kreport + 5 + 2*ownerCoefficient

theorem production_sites (S : 6≤s) (advice : s=ell (ell n)) : 189<n := by
  have E := ProductionH6Count.advice_lower (by omega : 0<s) advice
  have A : (32:Nat)≤2^(s-1) :=
    Nat.pow_le_pow_right (by decide : (0:Nat)<2) (by omega : 5≤s-1)
  have B : (4294967296:Nat)≤2^(2^(s-1)) :=
    Nat.pow_le_pow_right (by decide : (0:Nat)<2) A
  omega

theorem packed_from_both_reports (advice : s=ell (ell n)) (S : 6≤s) (N : 189<n)
    (y : Raw s n) (Y : DeployedSecond advice S N y) :
    IIDExpectedHittingTimeAtMost (rawNext s) (fun z=>Nonempty (PackedFiber z)) y (5122*n^2) := by
  obtain ⟨a,A,b,B,E⟩ := Y
  let I := firstInputs advice S N a A
  let J := secondOfFirstCover I advice S b B
  have Room := production_radius_room .second advice S
  let P := widthLower_at_report2_cover J.N (by omega : 0<s) J.hh J.G J.F (actual_width .second S J)
    J.Bounds Room y E
  exact packed_from_certified_h6_quadratic P S advice J.N y ⟨E,rfl⟩

theorem packed_from_raw (advice : s=ell (ell n)) (S : 6≤s) (Kreport : Nat)
    (report : ∀ (N : 189<n) (y : Raw s n), PermanentH4 N y →
      IIDExpectedHittingTimeAtMost (rawNext s) (DeployedSecond advice S N) y (Kreport*n^2))
    (x : Raw s n) :
    IIDExpectedHittingTimeAtMost (rawNext s) (fun z=>Nonempty (PackedFiber z)) x (K_packed Kreport*n^2) := by
  let N : 189<n := production_sites S advice
  have H := permanent_h4_from_raw N x
  have M : IIDExpectedHittingTimeAtMost (rawNext s) (PermanentH4 N) x (K_mis*n^2) := by
    unfold K_mis
    rw [Nat.add_mul,Nat.add_mul]
    exact H
  have R (y : Raw s n) (Y : PermanentH4 N y) :
      IIDExpectedHittingTimeAtMost (rawNext s) (fun z=>Nonempty (PackedFiber z)) y
        ((Kreport+5122)*n^2) := by
    rw [Nat.add_mul]
    exact AllSizeComposition.additive_stage (rawNext s) (DeployedSecond advice S N) _ _ _ y
      (report N y Y)
      (packed_from_both_reports advice S N)
  unfold K_packed
  rw [Nat.add_mul]
  exact AllSizeComposition.additive_stage (rawNext s) (PermanentH4 N) _ _ _ x M R

/-- Full production raw custody, including the closed packing entrance
and the actual same-tape sampled owner recovery. The result is the
existing CustodyWitness, including the base-offset field. -/
theorem custody_reached_of_quadratic_reports (advice : s=ell (ell n)) (S : 6≤s)
    (Kreport : Nat) (report : ∀ (N : 189<n) (y : Raw s n),PermanentH4 N y →
      IIDExpectedHittingTimeAtMost (rawNext s) (DeployedSecond advice S N) y (Kreport*n^2))
    (x : Raw s n) :
    IIDExpectedHittingTimeAtMost (rawNext s) Custody x (K_custody Kreport*n^2) :=
  custody_reached_of_geometry (by omega : 2≤s) (ProductionH6Count.room_of_advice S advice)
    (fun z=>Nonempty (PackedFiber z)) (K_packed Kreport) (packed_from_raw advice S Kreport report) (fun _ H=>H) x

#print axioms K_custody
#print axioms packed_from_both_reports
#print axioms packed_from_raw
#print axioms custody_reached_of_quadratic_reports
end
end L4.PhysicalCustodyAssembly
