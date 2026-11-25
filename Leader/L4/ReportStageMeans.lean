import Leader.L4.ReportStageInputs
import Leader.L4.ReportProductionSticky

namespace L4.ReportStageMeans
open AllSizeProtocol PhysicalCustody ReportStageInputs ShortMIS3Entrance
open ReportResetRawHooks ReportOwnerResetDrain ReportPrelaunchK1Geometry ReportLeaseOwner
open ReportFastDispatch ReportFastRawEvent ReportFastSplice ReportGoodEightBank
open ReportWriteRailSupplier ReportRawTrialSticky ReportProductionSticky
open ReportCoverHandoff ReportCurrentCustodyCut ReportServiceMesh AdviceBandRadiusBudget
variable {s n : Nat} {h : Fin n→Bool} {Q : Raw s n→Prop}

def Endpoint (d : Sheet) (I : Inputs d h Q) (x : Raw s n) : Prop :=
  CoverAt d I.Bounds I.hh (CurrentCustodyCut d I.hh Q I.G) x

def bankCost (d : Sheet) (I : Inputs d h Q) : Nat :=
  2*ReportResetEventClock.resetCoefficient (3*I.G.B) (params d s).digits*n^2

def serviceCost (d : Sheet) (s n : Nat) : Nat :=
  2*n*trialU (meshRadius d s)*(ell n+1)

def cacheCost (d : Sheet) (s n : Nat) : Nat :=
  (max 3 (params d s).digits+1)*n^2

theorem minWidth_ge_one (d : Sheet) (s : Nat) : 1≤minWidth d s := by
  cases d <;> simp [minWidth] <;> omega

theorem actual_width (d : Sheet) (S : 6≤s) (I : Inputs d h Q) : WidthOK d I.G s := by
  intro r
  have D : (params d s).digits≤minWidth d s := by
    cases d
    · change 1≤16
      decide
    · have H := AdviceBandRadiusBudget.t2_le S
      change (params .second s).digits≤s+1 at H
      change (params .second s).digits≤16*(s+1)
      omega
  exact (charter_width_rooms I.G r (params d s).digits
    (minWidth d s) (maxWidth d s) I.Lo I.Hi D).2

theorem bank_to_endpoint (d : Sheet) (I : Inputs d h Q)
    (advice : s=ell (ell n)) (S : 6≤s) (x : Raw s n) (A : GoodEightBank d I.hh Q I.G x) :
    L4.IIDExpectedHittingTimeAtMost (rawNext s) (Endpoint d I) x (serviceCost d s n) := by
  have H := sticky_cover_expected d I.N I.hh I.G I.F advice S I.Lo I.Hi
    (actual_width d S I) I.Bounds (minWidth_ge_one d s) (production_radius_room d advice S) x A
  intro t
  apply Nat.le_trans (RankRenewal.cost_mono_target (next:=rawNext s) _ _ ?_ t x) (H t)
  intro y Y
  exact ⟨cut_of_bank d I.N (by omega) I.hh I.G I.F y Y.1,Y.2⟩

theorem cached_to_endpoint (d : Sheet) (I : Inputs d h Q)
    (advice : s=ell (ell n)) (S : 6≤s) (x : Raw s n) (A : Cached d I.hh Q x) :
    L4.IIDExpectedHittingTimeAtMost (rawNext s) (Endpoint d I) x
      (bankCost d I+serviceCost d s n) :=
  AllSizeComposition.additive_stage _ _ _ _ _ x
    (bank_expected_from_cached d I.N (by omega) I.hh I.G I.F ⟨x,A⟩)
    (fun y Y=>bank_to_endpoint d I advice S y Y)

theorem fibre_to_endpoint (d : Sheet) (I : Inputs d h Q)
    (advice : s=ell (ell n)) (S : 6≤s) (x : Raw s n) (A : Q x) :
    L4.IIDExpectedHittingTimeAtMost (rawNext s) (Endpoint d I) x
      (cacheCost d s n+(bankCost d I+serviceCost d s n)) :=
  AllSizeComposition.additive_stage _ _ _ _ _ x (cache_entrance d I x A).2
    (fun y Y=>cached_to_endpoint d I advice S y Y)

theorem first_from_h4 (advice : s=ell (ell n)) (S : 6≤s) (N : 189<n)
    (x : Raw s n) (A : PermanentH4 N x) :
    let I := firstInputs advice S N x A
    L4.IIDExpectedHittingTimeAtMost (rawNext s) (FirstCover I) x
      (cacheCost .first s n+(bankCost .first I+serviceCost .first s n)) :=
  fibre_to_endpoint .first (firstInputs advice S N x A) advice S x ⟨A,rfl⟩

theorem second_from_first_cover (I : Inputs .first h Q)
    (advice : s=ell (ell n)) (S : 6≤s) (x : Raw s n) (A : FirstCover I x) :
    let J := secondOfFirstCover I advice S x A
    L4.IIDExpectedHittingTimeAtMost (rawNext s) (Endpoint .second J) x
      (cacheCost .second s n+(bankCost .second J+serviceCost .second s n)) :=
  fibre_to_endpoint .second (secondOfFirstCover I advice S x A) advice S x ⟨A,rfl⟩


def deployedStageCost (d : Sheet) (s n : Nat) : Nat :=
  cacheCost d s n+
    (2*ReportResetEventClock.resetCoefficient (3*maxWidth d s) (params d s).digits*n^2+
      serviceCost d s n)

def DeployedSecond (advice : s=ell (ell n)) (S : 6≤s) (N : 189<n)
    (y : Raw s n) : Prop :=
  ∃ x : Raw s n, ∃ H : PermanentH4 N x,
    let I := firstInputs advice S N x H
    ∃ v : Raw s n, ∃ V : FirstCover I v,
      Endpoint .second (secondOfFirstCover I advice S v V) y

theorem both_from_h4 (advice : s=ell (ell n)) (S : 6≤s) (N : 189<n)
    (x : Raw s n) (A : PermanentH4 N x) :
    L4.IIDExpectedHittingTimeAtMost (rawNext s) (DeployedSecond advice S N) x
      (deployedStageCost .first s n+deployedStageCost .second s n) := by
  let I := firstInputs advice S N x A
  apply AllSizeComposition.additive_stage _ (FirstCover I) _ _ _ x
    (first_from_h4 advice S N x A)
  intro y Y t
  let J := secondOfFirstCover I advice S y Y
  exact Nat.le_trans (RankRenewal.cost_mono_target (next:=rawNext s)
    (Endpoint .second J) (DeployedSecond advice S N)
    (fun z Z=>⟨x,A,y,Y,Z⟩) t y) (second_from_first_cover I advice S y Y t)

#print axioms both_from_h4
#print axioms actual_width
#print axioms bank_to_endpoint
#print axioms cached_to_endpoint
#print axioms fibre_to_endpoint
#print axioms first_from_h4
#print axioms second_from_first_cover
end L4.ReportStageMeans
