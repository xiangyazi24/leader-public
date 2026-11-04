import Leader.Wu.Entrance.StageLengths
import Leader.Wu.Entrance.WriterProtectionWitness
import Leader.Wu.Entrance.SharedBirthWordMassAdmitted
import Leader.Wu.Entrance.K2DrainHolds


set_option autoImplicit false
set_option Elab.async false


namespace B6EntranceLargeRingPackage



/-- The concrete writer-protection predicate is interval-local on every large-ring workspace. -/
def WriterProtectionLocalOnLargeRing
    {n psi : Nat} (ring : DirectedRing n)
    (_hdom : LargeRingDomain psi n) : Prop :=
  B6EntranceV2.HostWriterProtectedLocal
    (B6EntranceLawsWiring2.WPfinal (psi := psi) ring)


/-- From a leaderless state, the concrete writer is admitted within one full envelope sweep. -/
def WriterAdmissionWithinEnvelopeSweep
    {n psi : Nat} (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (ring : DirectedRing n) (_hdom : LargeRingDomain psi n) : Prop :=
  B6EntranceAdmissionV3.HostWriterAdmissionV3
    (B9Host.r1Host (kappa := psi) (tau := 16 * psi) hpsi h2)
    (fun q : B6EntranceV2.Phys psi psi (16 * psi) => q)
    ring (B6EntranceLawsWiring2.WPfinal (psi := psi) ring)
    (B6EntranceStageLengths.writerTargetL psi)


/-- Directional traffic reaches the whole-envelope reset/echo exit within a forward/reverse sweep. -/
def DirectionalTrafficExitWithinDoubleSweep
    {n psi : Nat} (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (ring : DirectedRing n) (_hdom : LargeRingDomain psi n) : Prop :=
  B6EntranceV3.HostDirectionalTrafficExitEnv
    (B9Host.r1Host (kappa := psi) (tau := 16 * psi) hpsi h2)
    (fun q : B6EntranceV2.Phys psi psi (16 * psi) => q)
    ring (B6EntranceLawsWiring2.WPfinal (psi := psi) ring)
    (B6EntranceStageLengths.trafficTargetL psi)


/-- Comparison expiry and the K2 pre-CHECK stability certificate are reached within the full timeout sweep. -/
def ComparisonExpiryWithinTimeoutSweep
    {n psi : Nat} (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (ring : DirectedRing n) (_hdom : LargeRingDomain psi n) : Prop :=
  B6EntranceV3.HostComparisonExpiryWordEnv
    hpsi h2
    (B9Host.r1Host (kappa := psi) (tau := 16 * psi) hpsi h2)
    (fun q : B6EntranceV2.Phys psi psi (16 * psi) => q)
    ring (B6EntranceLawsWiring2.WPfinal (psi := psi) ring)
    (B6EntranceStageLengths.expiryTargetL psi)



/-- The ruler stage reaches the corrected prepared-core target within the sharp core ruler bound. -/
def RulerPreparationWithinCoreBound
    {n psi : Nat} (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (ring : DirectedRing n) (_hdom : LargeRingDomain psi n) : Prop :=
  B6EntranceV2K2.HostRulerWordV2
    hpsi
    (B9Host.r1Host (kappa := psi) (tau := 16 * psi) hpsi h2)
    (fun q : B6EntranceV2.Phys psi psi (16 * psi) => q)
    ring (B6EntranceLawsWiring2.WPfinal (psi := psi) ring)
    (B6EntranceStageLengths.rulerTargetL psi)


/-- The route stage exits the prepared core within one reverse core sweep. -/
def RouteExitWithinCoreSweep
    {n psi : Nat} (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (ring : DirectedRing n) (_hdom : LargeRingDomain psi n) : Prop :=
  B6EntranceV2K2.HostRouteWordV2
    hpsi
    (B9Host.r1Host (kappa := psi) (tau := 16 * psi) hpsi h2)
    (fun q : B6EntranceV2.Phys psi psi (16 * psi) => q)
    ring (B6EntranceLawsWiring2.WPfinal (psi := psi) ring)
    (B6EntranceStageLengths.routeTargetL psi)


/-- The complete corrected seven-law C4 package on the large-ring domain. -/
def C4LargeRingPackage
    {n psi : Nat} (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (ring : DirectedRing n) (hdom : LargeRingDomain psi n) : Prop :=
  WriterProtectionLocalOnLargeRing ring hdom ∧
  WriterAdmissionWithinEnvelopeSweep hpsi h2 ring hdom ∧
  DirectionalTrafficExitWithinDoubleSweep hpsi h2 ring hdom ∧
  ComparisonExpiryWithinTimeoutSweep hpsi h2 ring hdom ∧
  K2DrainWithinEnvelopeSweep hpsi h2 ring hdom ∧
  RulerPreparationWithinCoreBound hpsi h2 ring hdom ∧
  RouteExitWithinCoreSweep hpsi h2 ring hdom


/-- Intended campaign consumer: the corrected package yields the admitted shared-birth mass leaf at the rebudgeted horizon. -/
def C4LargeRingCampaignConsumer
    {n psi : Nat} (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (ring : DirectedRing n) : Prop :=
  ∀ hdom : LargeRingDomain psi n,
    C4LargeRingPackage hpsi h2 ring hdom →
    B6EntranceK2MassAdmitted.C4C5AdmittedR1MassSimulation hpsi h2 ring →
    B6EntranceK2MassAdmitted.C4C5SharedBirthWordMassAdmittedAt
      hpsi h2 ring
      (B6EntranceStageLengths.stageTargetCoeff
        psi (CFinalAssembly2.Q2star psi) * n ^ 2)


/-- The concrete writer-protection witness is local on the corrected large-ring domain. -/
theorem writerProtectionLocalOnLargeRing_holds
    {n psi : Nat} (ring : DirectedRing n)
    (hdom : LargeRingDomain psi n) :
    WriterProtectionLocalOnLargeRing ring hdom := by
  change B6EntranceV2.HostWriterProtectedLocal
    (B6EntranceLawsWiring2.WPfinal (psi := psi) ring)
  exact B6EntranceLawsWiring2.hostWriterProtectedLocal_WPfinal
    (psi := psi) ring

open BirthLeaderlessBirthMassRenewal
open BirthCheckPermitRepairLeaf BirthCheckChainR1PerBlock
open B6EntranceV2 B6EntranceV2K2 B6EntranceV3 B6EntranceAdmissionV3
open B6EntranceK2MassAdmitted
open BirthTwoStageEscape
open CFinalAssembly2


theorem c4LargeRingCampaignConsumer_holds
    {n psi : Nat} (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (ring : DirectedRing n) :
    C4LargeRingCampaignConsumer hpsi h2 ring := by
  intro hdom hC4 hSim
  have h3 : 2 < psi := hdom.1
  have hfit : envelopeWidth psi < n := hdom.2
  have hpsiEnv : psi < envelopeWidth psi := by
    unfold envelopeWidth coreWidth collarWidth
    omega
  have hpsin : psi ≤ n := by omega
  have hn : 1 ≤ n := by omega
  unfold C4LargeRingPackage at hC4
  rcases hC4 with
    ⟨hLocal, hAdmission3, hTraffic, hExpiry, hK2, hRuler, hRoute⟩
  change HostWriterProtectedLocal
    (B6EntranceLawsWiring2.WPfinal (psi := psi) ring) at hLocal
  change HostWriterAdmissionV3
    (B9Host.r1Host (kappa := psi) (tau := 16 * psi) hpsi h2)
    (fun q : Phys psi psi (16 * psi) => q) ring
    (B6EntranceLawsWiring2.WPfinal (psi := psi) ring)
    (B6EntranceStageLengths.stageTargetBudget n psi).writer.L at hAdmission3
  change HostDirectionalTrafficExitEnv
    (B9Host.r1Host (kappa := psi) (tau := 16 * psi) hpsi h2)
    (fun q : Phys psi psi (16 * psi) => q) ring
    (B6EntranceLawsWiring2.WPfinal (psi := psi) ring)
    (B6EntranceStageLengths.stageTargetBudget n psi).traffic.L at hTraffic
  change HostComparisonExpiryWordEnv hpsi h2
    (B9Host.r1Host (kappa := psi) (tau := 16 * psi) hpsi h2)
    (fun q : Phys psi psi (16 * psi) => q) ring
    (B6EntranceLawsWiring2.WPfinal (psi := psi) ring)
    (B6EntranceStageLengths.stageTargetBudget n psi).expiry.L at hExpiry
  change HostK2ClearableOrLeaderV3 hpsi h2
    (B9Host.r1Host (kappa := psi) (tau := 16 * psi) hpsi h2)
    (fun q : Phys psi psi (16 * psi) => q) ring
    (B6EntranceLawsWiring2.WPfinal (psi := psi) ring)
    (B6EntranceStageLengths.stageTargetBudget n psi).k2.L at hK2
  change HostRulerWordV2 hpsi
    (B9Host.r1Host (kappa := psi) (tau := 16 * psi) hpsi h2)
    (fun q : Phys psi psi (16 * psi) => q) ring
    (B6EntranceLawsWiring2.WPfinal (psi := psi) ring)
    (B6EntranceStageLengths.stageTargetBudget n psi).ruler.L at hRuler
  change HostRouteWordV2 hpsi
    (B9Host.r1Host (kappa := psi) (tau := 16 * psi) hpsi h2)
    (fun q : Phys psi psi (16 * psi) => q) ring
    (B6EntranceLawsWiring2.WPfinal (psi := psi) ring)
    (B6EntranceStageLengths.stageTargetBudget n psi).route.L at hRoute
  have hAdmission : HostWriterAdmission
      (B9Host.r1Host (kappa := psi) (tau := 16 * psi) hpsi h2)
      (fun q : Phys psi psi (16 * psi) => q) ring
      (B6EntranceLawsWiring2.WPfinal (psi := psi) ring)
      (B6EntranceStageLengths.stageTargetBudget n psi).writer.L :=
    writerAdmission_of_writerAdmissionV3 _ _ ring _ _ hAdmission3
  have hReadyHost := B6EntranceV3.readyWindowEscape_of_seven_laws
    hpsi h2
    (B9Host.r1Host (kappa := psi) (tau := 16 * psi) hpsi h2)
    (fun q : Phys psi psi (16 * psi) => q) ring
    (B6EntranceLawsWiring2.WPfinal (psi := psi) ring)
    (B6EntranceStageLengths.stageTargetBudget n psi)
    (B6EntranceStageLengths.stageTargetBudget_valid n psi)
    hLocal hAdmission hTraffic hExpiry hK2 hRuler hRoute
  have hstep : B9Host.hostStep
      (B9Host.r1Host (kappa := psi) (tau := 16 * psi) hpsi h2) ring =
      BirthCheckPermitRepairLeaf.step1 hpsi h2 ring := by
    funext C e
    exact B9Host.hostStep_r1_eq_step1
      (kappa := psi) (tau := 16 * psi) hpsi h2 ring C e
  have hReady : ∀ C : BirthCheckPermitRepairLeaf.FC n psi psi (16 * psi),
      BirthShortDoneTerminalFirstHit.Leaderless C →
      entranceQ (B6EntranceStageLengths.stageTargetBudget n psi) *
        avoidCount (BirthCheckPermitRepairLeaf.step1 hpsi h2 ring)
          BirthShortDoneTerminalFirstHit.Leaderless (ReadyWindow ring) C
          (entranceB n (B6EntranceStageLengths.stageTargetBudget n psi)) ≤
      (entranceQ (B6EntranceStageLengths.stageTargetBudget n psi) - 1) *
        n ^ entranceB n (B6EntranceStageLengths.stageTargetBudget n psi) := by
    intro C hC
    have hm := hReadyHost C hC
    rw [hstep] at hm
    exact hm
  have hQ :
      1 ≤ entranceQ (B6EntranceStageLengths.stageTargetBudget n psi) := by
    unfold B6EntranceStageLengths.stageTargetBudget
    rw [B6EntranceK2BudgetAudit.rebudget_entranceQ]
    exact Nat.one_le_pow _ _ (by
      have ht := B6EntranceK2Budget.one_le_envelopeTouchBound psi
      omega)
  have hH :
      3 * (entranceQ (B6EntranceStageLengths.stageTargetBudget n psi) *
        Q2star psi) *
        (entranceB n (B6EntranceStageLengths.stageTargetBudget n psi) +
          2 * n * (psi - 1)) ≤
      B6EntranceStageLengths.stageTargetCoeff psi (Q2star psi) * n ^ 2 := by
    have hh := B6EntranceK2Mass4.c4BoostedH_le_correctedFinalLeafH
      (n := n) (psi := psi)
      (B6EntranceStageLengths.stageTargetBudget n psi) (Q2star psi)
      (B6EntranceStageLengths.stageTargetBudget_valid n psi) hn
    simpa [B6EntranceK2Mass4.c4BoostedH,
      B6EntranceK2Mass4.C4CorrectedFinalLeafH,
      B6EntranceStageLengths.stageTargetCoeff_eq] using hh
  exact c4C5SharedBirthWordMassAdmittedAt_of_r1ReadyWindowMass
    hpsi h2 h3 hpsin ring
    (entranceB n (B6EntranceStageLengths.stageTargetBudget n psi))
    (entranceQ (B6EntranceStageLengths.stageTargetBudget n psi))
    (Q2star psi)
    (B6EntranceStageLengths.stageTargetCoeff psi (Q2star psi) * n ^ 2)
    hQ (Q2star_spec psi) hReady hSim hH

end B6EntranceLargeRingPackage
