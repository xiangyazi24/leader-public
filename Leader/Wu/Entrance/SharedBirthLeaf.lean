import Leader.Wu.Entrance.ReadyWindowMassSimulation
import Leader.Wu.Entrance.WriterProtectionWitness
import Leader.Wu.Entrance.FinalLeafDomainBound
import Leader.Wu.Entrance.TailComposition

set_option autoImplicit false
set_option Elab.async false

namespace CFinalSharedBirthLeaf

open PPLL PPLLResearchFormulation PPLLExpiringComparisonRepair
open BirthLeaderlessBirthMassRenewal BirthTwoStageEscape
open BirthCheckPermitRepairLeaf BirthCheckChainR1PerBlock
open B6LocalReverseFill
open B6EntranceV2 B6EntranceV2K2 B6EntranceV3 B6EntranceAdmissionV3
open B6EntranceK2Budget B6EntranceK2Mass3
open FinalCandidateR2C
open FinalCandidateR2C.FinalCandidateR2C.FinalCandidateR2C.FinalCandidateR2C.FinalCandidateR2C
open CFinalAssembly2

variable {n psi : Nat}

/-- Exactly the inputs read by the ReadyWindow mass path, specialized to the
landed concrete writer witness and fixed C4 budget.  `bitSilence` and
`staticExpiry` are intentionally absent. -/
structure ReducedC4LeafInputsV31
    (hpsi : 0 < psi) (h2 : 2 <= psi) (ring : DirectedRing n) : Prop where
  budgetValid : (c4Budget n psi).Valid n psi
  writerLocal : HostWriterProtectedLocal
    (B6EntranceLawsWiring2.WPfinal (psi := psi) ring)
  writerAdmission : HostWriterAdmissionV3
    (B9Host.r1Host (kappa := psi) (tau := 16 * psi) hpsi h2)
    (fun q : Phys psi psi (16 * psi) => q) ring
    (B6EntranceLawsWiring2.WPfinal (psi := psi) ring)
    (c4Budget n psi).writer.L
  trafficWord : HostDirectionalTrafficExitEnv
    (B9Host.r1Host (kappa := psi) (tau := 16 * psi) hpsi h2)
    (fun q : Phys psi psi (16 * psi) => q) ring
    (B6EntranceLawsWiring2.WPfinal (psi := psi) ring)
    (c4Budget n psi).traffic.L
  expiryWord : HostComparisonExpiryWordEnv hpsi h2
    (B9Host.r1Host (kappa := psi) (tau := 16 * psi) hpsi h2)
    (fun q : Phys psi psi (16 * psi) => q) ring
    (B6EntranceLawsWiring2.WPfinal (psi := psi) ring)
    (c4Budget n psi).expiry.L
  k2Word : HostK2ClearableOrLeaderV3 hpsi h2
    (B9Host.r1Host (kappa := psi) (tau := 16 * psi) hpsi h2)
    (fun q : Phys psi psi (16 * psi) => q) ring
    (B6EntranceLawsWiring2.WPfinal (psi := psi) ring)
    (c4Budget n psi).k2.L
  rulerWord : HostRulerWordV2 hpsi
    (B9Host.r1Host (kappa := psi) (tau := 16 * psi) hpsi h2)
    (fun q : Phys psi psi (16 * psi) => q) ring
    (B6EntranceLawsWiring2.WPfinal (psi := psi) ring)
    (c4Budget n psi).ruler.L
  routeWord : HostRouteWordV2 hpsi
    (B9Host.r1Host (kappa := psi) (tau := 16 * psi) hpsi h2)
    (fun q : Phys psi psi (16 * psi) => q) ring
    (B6EntranceLawsWiring2.WPfinal (psi := psi) ring)
    (c4Budget n psi).route.L

variable {kappa tau : Nat} {P : Type}
variable {ring : DirectedRing n}

private theorem iwAppend (I : Interval ring) (u v : List (Fin n))
    (hu : InternalWord I u) (hv : InternalWord I v) : InternalWord I (u ++ v) := by
  intro e he
  rcases List.mem_append.mp he with he | he
  · exact hu e he
  · exact hv e he

private theorem runAppend (host : B9Host.HostRow P) (u v : List (Fin n))
    (C : PConfig n P) :
    runHost host ring (u ++ v) C = runHost host ring v (runHost host ring u C) := by
  simp only [runHost, List.foldl_append]

private theorem continueRequest
    (host : B9Host.HostRow P) (view : P -> Phys psi kappa tau)
    (I : Interval ring) (A B : PConfig n P -> Prop) (C : PConfig n P)
    (u : List (Fin n)) (Lu Lv : Nat)
    (huI : InternalWord I u) (huL : u.length <= Lu)
    (huE : HostExit host view ring I A (runHost host ring u C))
    (hnext : forall D, HostLeaderless view D -> A D ->
      exists v, InternalWord I v /\ v.length <= Lv /\
        HostExit host view ring I B (runHost host ring v D)) :
    exists w, InternalWord I w /\ w.length <= Lu + Lv /\
      HostExit host view ring I B (runHost host ring w C) := by
  rcases huE with hA | hHit | hBirth
  · let D := runHost host ring u C
    by_cases hD : HostLeaderless view D
    · obtain ⟨v,hvI,hvL,hvE⟩ := hnext D hD hA
      refine ⟨u ++ v, iwAppend I u v huI hvI, ?_, ?_⟩
      · simp only [List.length_append]; omega
      · rw [runAppend]; exact hvE
    · exact ⟨u,huI,by omega,Or.inr (Or.inr hD)⟩
  · exact ⟨u,huI,by omega,Or.inr (Or.inl hHit)⟩
  · exact ⟨u,huI,by omega,Or.inr (Or.inr hBirth)⟩

private theorem postWriterRequest
    (hpsi : 0 < psi) (h2 : 2 <= psi)
    (host : B9Host.HostRow P) (view : P -> Phys psi kappa tau)
    (WP : WriterProtected ring psi P) (b : EntranceBudgets)
    (hTraffic : HostDirectionalTrafficExitEnv host view ring WP b.traffic.L)
    (hExpiry : HostComparisonExpiryWordEnv hpsi h2 host view ring WP b.expiry.L)
    (hK2 : HostK2ClearableOrLeaderV3 hpsi h2 host view ring WP b.k2.L)
    (hRuler : HostRulerWordV2 hpsi host view ring WP b.ruler.L)
    (hRoute : HostRouteWordV2 hpsi host view ring WP b.route.L)
    (X : Workspace ring psi) (C : PConfig n P)
    (hC : HostLeaderless view C) (hW : WriterAt WP X C) :
    exists w, InternalWord X.env.I w /\ w.length <= postWriterL b /\
      HostExit host view ring X.env.I (fun _ => False) (runHost host ring w C) := by
  obtain ⟨u,huI,huL,huE⟩ := hTraffic X C hC hW
  obtain ⟨u1,hu1I,hu1L,hu1E⟩ := continueRequest host view X.env.I
    (TrafficAtEnv view WP X)
    (fun D => ExpiryAtEnv view WP X D /\ R1DrainStableForK2 hpsi h2 host view ring X D)
    C u b.traffic.L b.expiry.L huI huL huE
    (fun D hD hT => hExpiry X D hD hT)
  obtain ⟨u2,hu2I,hu2L,hu2E⟩ := continueRequest host view X.env.I
    (fun D => ExpiryAtEnv view WP X D /\ R1DrainStableForK2 hpsi h2 host view ring X D)
    (K2DrainedAt view WP X) C u1 (b.traffic.L + b.expiry.L) b.k2.L
    hu1I hu1L hu1E (fun D hD hE => hK2 X D hD hE)
  have hRuler' := B6EntranceV2.coreStageWord_stage host view ring WP
    (K2DrainedAt view WP) (CorePreparedV2 hpsi view WP) b.ruler.L hRuler
  obtain ⟨u3,hu3I,hu3L,hu3E⟩ := continueRequest host view X.env.I
    (K2DrainedAt view WP X) (CorePreparedV2 hpsi view WP X)
    C u2 ((b.traffic.L + b.expiry.L) + b.k2.L) b.ruler.L
    hu2I hu2L hu2E (fun D hD hS => hRuler' X D hD hS)
  have hRoute' := B6EntranceV2.coreStageWord_stage host view ring WP
    (CorePreparedV2 hpsi view WP) (fun _ _ => False) b.route.L hRoute
  obtain ⟨u4,hu4I,hu4L,hu4E⟩ := continueRequest host view X.env.I
    (CorePreparedV2 hpsi view WP X) (fun _ => False)
    C u3 (((b.traffic.L + b.expiry.L) + b.k2.L) + b.ruler.L) b.route.L
    hu3I hu3L hu3E (fun D hD hP => hRoute' X D hD hP)
  exact ⟨u4,hu4I,hu4L,hu4E⟩

private theorem postWriterMass
    (hpsi : 0 < psi) (h2 : 2 <= psi)
    (host : B9Host.HostRow P) (view : P -> Phys psi kappa tau)
    (WP : WriterProtected ring psi P) (b : EntranceBudgets)
    (hpostQ : 1 <= postWriterQ b)
    (hpostMatch : (4 * envelopeTouchBound psi) ^ postWriterL b <= postWriterQ b)
    (hTraffic : HostDirectionalTrafficExitEnv host view ring WP b.traffic.L)
    (hExpiry : HostComparisonExpiryWordEnv hpsi h2 host view ring WP b.expiry.L)
    (hK2 : HostK2ClearableOrLeaderV3 hpsi h2 host view ring WP b.k2.L)
    (hRuler : HostRulerWordV2 hpsi host view ring WP b.ruler.L)
    (hRoute : HostRouteWordV2 hpsi host view ring WP b.route.L) :
    forall (X : Workspace ring psi) (C : PConfig n P),
      HostAlive view ring C -> WriterAt WP X C ->
      postWriterQ b * aliveCount (B9Host.hostStep host ring)
          (HostAlive view ring) C (postWriterB n b) <=
        (postWriterQ b - 1) * n ^ postWriterB n b := by
  intro X C hC hW
  obtain ⟨w,hI,hL,hExit⟩ := postWriterRequest hpsi h2 host view WP b
    hTraffic hExpiry hK2 hRuler hRoute X C hC.1 hW
  have hM : 1 <= envelopeTouchBound psi := by
    unfold envelopeTouchBound envelopeWidth coreWidth collarWidth; omega
  have hbudget : B6EntranceCompose.EscapeBudget n (postWriterL b)
      (envelopeTouchBound psi) (postWriterB n b) (postWriterQ b) :=
    ⟨hM,hpostQ,rfl,hpostMatch⟩
  have hm := B6EntranceV2.hostRequest_mass_of_budget host view ring X.env.I
    (fun _ => False) w C (postWriterL b) (envelopeTouchBound psi)
    (postWriterB n b) (postWriterQ b) hbudget hL
    (B6EntranceV2.envelope_touch_le X) hC.1 (by intro A D _; simp) ⟨hI,hExit⟩
  rw [B6EntranceV2.avoidCount_eq_hostPending host view ring
    (fun _ => False) C (postWriterB n b)] at hm
  have hp : HostPending view ring (fun _ : PConfig n P => False) =
      HostAlive view ring := by
    funext D; simp only [HostPending, not_false_eq_true, and_true]
  rw [hp] at hm
  exact hm

private theorem readyWindow_of_reducedInputs
    (hpsi : 0 < psi) (h2 : 2 <= psi) (ring : DirectedRing n)
    (h : ReducedC4LeafInputsV31 hpsi h2 ring) :
    UniformHostReadyWindowEscape
      (B9Host.r1Host (kappa := psi) (tau := 16 * psi) hpsi h2)
      (fun q : Phys psi psi (16 * psi) => q) ring
      (entranceB n (c4Budget n psi)) (entranceQ (c4Budget n psi)) := by
  rcases h.budgetValid with ⟨hBw,hTouch,_,_,_,_,_,hPostQ,hPostMatch⟩
  have hQw : 1 <= (c4Budget n psi).writer.Q := hBw.2.1
  have hAdmission : HostWriterAdmission
      (B9Host.r1Host (kappa := psi) (tau := 16 * psi) hpsi h2)
      (fun q : Phys psi psi (16 * psi) => q) ring
      (B6EntranceLawsWiring2.WPfinal (psi := psi) ring)
      (c4Budget n psi).writer.L :=
    writerAdmission_of_writerAdmissionV3
      (B9Host.r1Host (kappa := psi) (tau := 16 * psi) hpsi h2)
      (fun q : Phys psi psi (16 * psi) => q) ring
      (B6EntranceLawsWiring2.WPfinal (psi := psi) ring)
      (c4Budget n psi).writer.L h.writerAdmission
  have hWriter := B6EntranceV2.writerAdmission_mass
    (B9Host.r1Host (kappa := psi) (tau := 16 * psi) hpsi h2)
    (fun q : Phys psi psi (16 * psi) => q) ring
    (B6EntranceLawsWiring2.WPfinal (psi := psi) ring)
    (c4Budget n psi) hBw hTouch h.writerLocal hAdmission
  have hTail : forall C : PConfig n (Phys psi psi (16 * psi)),
      HostAlive (fun q : Phys psi psi (16 * psi) => q) ring C ->
      WriterStage (B6EntranceLawsWiring2.WPfinal (psi := psi) ring) C ->
      postWriterQ (c4Budget n psi) *
          aliveCount (B9Host.hostStep
            (B9Host.r1Host (kappa := psi) (tau := 16 * psi) hpsi h2) ring)
            (HostAlive (fun q : Phys psi psi (16 * psi) => q) ring) C
            (postWriterB n (c4Budget n psi)) <=
        (postWriterQ (c4Budget n psi) - 1) * n ^ postWriterB n (c4Budget n psi) := by
    intro C hC hStage
    rcases hStage with ⟨X,hX⟩
    exact postWriterMass hpsi h2
      (B9Host.r1Host (kappa := psi) (tau := 16 * psi) hpsi h2)
      (fun q : Phys psi psi (16 * psi) => q)
      (B6EntranceLawsWiring2.WPfinal (psi := psi) ring) (c4Budget n psi)
      hPostQ hPostMatch h.trafficWord h.expiryWord h.k2Word h.rulerWord h.routeWord
      X C hC hX
  have htwo : UniformEscapeMass
      (B9Host.hostStep (B9Host.r1Host (kappa := psi) (tau := 16 * psi) hpsi h2) ring)
      (HostAlive (fun q : Phys psi psi (16 * psi) => q) ring)
      (entranceB n (c4Budget n psi)) (entranceQ (c4Budget n psi)) := by
    change UniformEscapeMass _ _
      ((c4Budget n psi).writer.B + postWriterB n (c4Budget n psi))
      ((c4Budget n psi).writer.Q * postWriterQ (c4Budget n psi))
    exact BirthTwoStageEscape.two_stage_escape _ _
      (WriterStage (B6EntranceLawsWiring2.WPfinal (psi := psi) ring))
      (c4Budget n psi).writer.B (postWriterB n (c4Budget n psi))
      (c4Budget n psi).writer.Q (postWriterQ (c4Budget n psi))
      hQw hPostQ hWriter hTail
  intro C hC
  rw [B6LocalReverseFill.avoidCount_eq_alive_complement]
  change entranceQ (c4Budget n psi) * aliveCount _
      (HostAlive (fun q : Phys psi psi (16 * psi) => q) ring) C
      (entranceB n (c4Budget n psi)) <= _
  by_cases hReady : HostReadyWindow (fun q : Phys psi psi (16 * psi) => q) ring C
  · have hn : ¬ HostAlive (fun q : Phys psi psi (16 * psi) => q) ring C := fun ha => ha.2 hReady
    rw [BirthTwoStageEscape.aliveCount_not_good _ _ C hn (entranceB n (c4Budget n psi)),
      Nat.mul_zero]
    exact Nat.zero_le _
  · exact htwo C ⟨hC,hReady⟩

/-- Frozen-C4-free shared birth leaf. -/
theorem sharedBirthWordMass_of_reducedInputs
    (hpsi : 0 < psi) (h2 : 2 <= psi) (h3 : 2 < psi)
    (hpsin : psi <= n) (ring : DirectedRing n)
    (h : ReducedC4LeafInputsV31 hpsi h2 ring)
    (hSim : C4C5FinalR1MassSimulation hpsi h2 ring) :
    C4C5SharedBirthWordMassAt hpsi h2 ring (FinalLeafHV2 n psi) := by
  have hReadyHost := readyWindow_of_reducedInputs hpsi h2 ring h
  have hstep : B9Host.hostStep
      (B9Host.r1Host (kappa := psi) (tau := 16 * psi) hpsi h2) ring =
      step1 hpsi h2 ring := by
    funext C e
    exact B9Host.hostStep_r1_eq_step1
      (kappa := psi) (tau := 16 * psi) hpsi h2 ring C e
  have hReady : forall C : BirthCheckPermitRepairLeaf.FC n psi psi (16 * psi),
      BirthShortDoneTerminalFirstHit.Leaderless C ->
      entranceQ (c4Budget n psi) * avoidCount (step1 hpsi h2 ring)
        BirthShortDoneTerminalFirstHit.Leaderless (ReadyWindow ring) C
        (entranceB n (c4Budget n psi)) <=
      (entranceQ (c4Budget n psi) - 1) * n ^ entranceB n (c4Budget n psi) := by
    intro C hC
    have hm := hReadyHost C hC
    rw [hstep] at hm
    exact hm
  have hQ1 : 1 <= entranceQ (c4Budget n psi) := by
    rw [c4Budget_entranceQ]
    exact Nat.one_le_pow _ _ (by have ht := one_le_envelopeTouchBound psi; omega)
  have hn : 1 <= n := by omega
  have hH : 3 * (entranceQ (c4Budget n psi) * Q2star psi) *
      (entranceB n (c4Budget n psi) + 2 * n * (psi - 1)) <= FinalLeafHV2 n psi := by
    simpa [B6EntranceK2Mass4.c4BoostedH, FinalLeafHV2] using
      B6EntranceK2Budget.B6EntranceK2Budget.c4BoostedH_le_correctedFinalLeafH
        n psi (Q2star psi) hn
  exact CFinalAssembly2.sharedBirthWordMassAt_of_r1ReadyWindowMass
    hpsi h2 h3 hpsin ring (entranceB n (c4Budget n psi))
    (entranceQ (c4Budget n psi)) (Q2star psi) (FinalLeafHV2 n psi)
    hQ1 (Q2star_spec psi) hReady hSim hH

/-- Referee form: the final one-over-n tail consumes only the reduced C4 leaf
inputs plus the final-to-R1 mass simulation. -/
theorem b7_bound_of_reducedInputs
    (hpsi : 0 < psi) (h2 : 2 <= psi) (h3 : 2 < psi)
    (hpsin : psi <= n) (ring : DirectedRing n)
    (h : ReducedC4LeafInputsV31 hpsi h2 ring)
    (hSim : C4C5FinalR1MassSimulation hpsi h2 ring) :
    FinalB7OneOverN hpsi h2 ring (FinalLeafHV2 n psi) := by
  have hLeaf := sharedBirthWordMass_of_reducedInputs
    hpsi h2 h3 hpsin ring h hSim
  have hn2 : 2 <= n := by omega
  exact CFinalTailComposition.b7_bound_of_sharedBirthWordMass
    hpsi h2 hn2 ring hLeaf

end CFinalSharedBirthLeaf
