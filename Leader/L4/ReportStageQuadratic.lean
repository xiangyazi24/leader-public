import Leader.L4.ReportAbsoluteBudget
import Leader.L4.ReportParallelReset
import Leader.L4.ReportCacheSweep

namespace L4.ReportStageQuadratic
set_option maxRecDepth 256
set_option maxHeartbeats 70000
open AllSizeProtocol PhysicalCustody ShortMIS3Entrance
open ReportStageInputs ReportStageMeans ReportAbsoluteBudget ReportParallelReset
open ReportCacheSweep ReportCacheAllSites ReportCacheWindow
open ReportResetRawHooks ReportOwnerResetDrain ReportGoodEightBank
open ReportServiceMesh AdviceBandRadiusBudget
variable {n s : Nat} {h : Fin n→Bool} {Q : Raw s n→Prop}

theorem cache_quadratic (d : Sheet) (I : Inputs d h Q) (x : Raw s n) (A : Q x) :
    L4.IIDExpectedHittingTimeAtMost (rawNext s) (Cached d I.hh Q) x (2*n^2) := by
  apply (MonitorRawBridge.height_iff_row _ _ _ _).mp
  cases d
  · exact all_expected_quadratic I.hh
      (report1_frame (rows s) h Q (ShortResetCycle.edge_sep I.N) I.F.closed I.F.mask) x A
  · exact all_expected_quadratic I.hh
      (report2_frame (rows s) h Q (ShortResetCycle.edge_sep I.N) I.F.closed I.F.mask) x A

theorem flat_bank_cost (d : Sheet) (I : Inputs d h Q)
    (advice : s=ell (ell n)) (S : 6≤s) :
    2*coverCost d I.G s≤67108864*n^2 := by
  have HI : I.G.B≤ReportFastRawEvent.maxWidth d s := I.Hi
  have K := @local_reset_budget d s S I.G.B HI
  have A := flat_two_report_reset S advice K
  unfold coverCost singleCost
  have E (n k u : Nat) : 2*(2*u*(2*(n*k)))=8*n*k*u := by
    calc
      _ = (2*2*2)*(n*k*u) := by ac_rfl
      _ = _ := by rw [show (2*2*2 : Nat)=8 by decide,←Nat.mul_assoc,←Nat.mul_assoc]
  rw [E]
  exact A

def prepBudget : Nat := 67108866

theorem fibre_to_endpoint_flat (d : Sheet) (I : Inputs d h Q)
    (advice : s=ell (ell n)) (S : 6≤s) (x : Raw s n) (A : Q x) :
    L4.IIDExpectedHittingTimeAtMost (rawNext s) (Endpoint d I) x
      (prepBudget*n^2+serviceCost d s n) := by
  have Pos : 0<s := Nat.lt_of_lt_of_le (by decide : 0<6) S
  let Bank := GoodEightBank d I.hh Q I.G
  have R (y : Raw s n) (Y : Cached d I.hh Q y) :
      L4.IIDExpectedHittingTimeAtMost (rawNext s) Bank y (67108864*n^2) := by
    have M := parallel_bank (s:=s) d I.N Pos I.hh I.G I.F ⟨y,Y⟩
    intro t
    exact Nat.le_trans (M t) (Nat.mul_le_mul_right (n^t) (flat_bank_cost d I advice S))
  have Prep := AllSizeComposition.additive_stage (rawNext s) (Cached d I.hh Q)
    Bank (2*n^2) (67108864*n^2) x (cache_quadratic d I x A) R
  have E : 2*n^2+67108864*n^2=prepBudget*n^2 := by
    have C : 2+67108864=prepBudget := by unfold prepBudget; omega
    exact (Nat.add_mul 2 67108864 (n^2)).symm.trans (congrArg (fun a => a*n^2) C)
  exact AllSizeComposition.additive_stage (rawNext s) Bank (Endpoint d I)
    (prepBudget*n^2) (serviceCost d s n) x (E ▸ Prep)
    (fun y Y=>bank_to_endpoint d I advice S y Y)

private theorem total_budget (K p n a b : Nat) (U : a+b≤K*n^2) :
    (p*n^2+a)+(p*n^2+b)≤(K+(p+p))*n^2 := by
  calc
    _ = (a+b)+(p*n^2+p*n^2) := by ac_rfl
    _ ≤ K*n^2+(p*n^2+p*n^2) := Nat.add_le_add_right U (p*n^2+p*n^2)
    _ = K*n^2+(p+p)*n^2 := congrArg (fun v=>K*n^2+v) (Nat.add_mul p p (n^2)).symm
    _ = _ := (Nat.add_mul K (p+p) (n^2)).symm

abbrev coefficient : Nat := K_rad+(prepBudget+prepBudget)

theorem both_from_h4_given (advice : s=ell (ell n)) (S : 6≤s) (N : 189<n)
    (x : Raw s n) (A : PermanentH4 N x)
    (K : Nat) (budget : serviceCost .first s n+serviceCost .second s n≤K*n^2) :
    L4.IIDExpectedHittingTimeAtMost (rawNext s) (DeployedSecond advice S N) x
      ((K+(prepBudget+prepBudget))*n^2) := by
  let I := firstInputs advice S N x A
  have H := AllSizeComposition.additive_stage (rawNext s) (FirstCover I)
    (DeployedSecond advice S N) (prepBudget*n^2+serviceCost .first s n)
    (prepBudget*n^2+serviceCost .second s n) x
    (fibre_to_endpoint_flat .first I advice S x ⟨A,rfl⟩)
    (by
      intro y Y t
      let J := secondOfFirstCover I advice S y Y
      exact Nat.le_trans (RankRenewal.cost_mono_target (next:=rawNext s)
        (Endpoint .second J) (DeployedSecond advice S N)
        (fun z Z=>⟨x,A,y,Y,Z⟩) t y)
        (fibre_to_endpoint_flat .second J advice S y ⟨Y,rfl⟩ t))
  have B := total_budget K prepBudget n (serviceCost .first s n)
    (serviceCost .second s n) budget
  intro t
  exact Nat.le_trans (H t) (Nat.mul_le_mul_right (n^t) B)

end L4.ReportStageQuadratic
