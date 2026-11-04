import Leader.Wu.Entrance.SharedBirthWordMassAdmitted
import Leader.Wu.Entrance.SharedBirthLeaf
import Leader.Wu.Entrance.TailComposition

set_option autoImplicit false
set_option Elab.async false

namespace CFinalAdmittedAssembly

open BirthLeaderlessBirthMassRenewal BirthTwoStageEscape
open BirthCheckPermitRepairLeaf BirthCheckChainR1PerBlock
open B6LocalReverseFill
open B6EntranceV2 B6EntranceV2K2 B6EntranceV3 B6EntranceAdmissionV3
open B6EntranceK2Budget B6EntranceK2MassAdmitted
open FinalCandidateR2C
open FinalCandidateR2C.FinalCandidateR2C.FinalCandidateR2C.FinalCandidateR2C.FinalCandidateR2C
open CFinalAssembly2 CFinalSharedBirthLeaf

variable {n psi kappa tau : Nat} {P : Type}
variable {ring : DirectedRing n}

private theorem iwAppendA (I : Interval ring) (u v : List (Fin n))
    (hu : InternalWord I u) (hv : InternalWord I v) : InternalWord I (u ++ v) := by
  intro e he
  rcases List.mem_append.mp he with he | he
  · exact hu e he
  · exact hv e he

private theorem runAppendA (host : B9Host.HostRow P) (u v : List (Fin n))
    (C : PConfig n P) :
    runHost host ring (u ++ v) C = runHost host ring v (runHost host ring u C) := by
  simp only [runHost, List.foldl_append]

private theorem continueRequestA
    (host : B9Host.HostRow P) (view : P → Phys psi kappa tau)
    (I : Interval ring) (A B : PConfig n P → Prop) (C : PConfig n P)
    (u : List (Fin n)) (Lu Lv : Nat)
    (huI : InternalWord I u) (huL : u.length ≤ Lu)
    (huE : HostExit host view ring I A (runHost host ring u C))
    (hnext : ∀ D, HostLeaderless view D → A D →
      ∃ v, InternalWord I v ∧ v.length ≤ Lv ∧
        HostExit host view ring I B (runHost host ring v D)) :
    ∃ w, InternalWord I w ∧ w.length ≤ Lu + Lv ∧
      HostExit host view ring I B (runHost host ring w C) := by
  rcases huE with hA | hHit | hBirth
  · let D := runHost host ring u C
    by_cases hD : HostLeaderless view D
    · obtain ⟨v,hvI,hvL,hvE⟩ := hnext D hD hA
      refine ⟨u ++ v, iwAppendA I u v huI hvI, ?_, ?_⟩
      · simp only [List.length_append]; omega
      · rw [runAppendA]; exact hvE
    · exact ⟨u,huI,by omega,Or.inr (Or.inr hD)⟩
  · exact ⟨u,huI,by omega,Or.inr (Or.inl hHit)⟩
  · exact ⟨u,huI,by omega,Or.inr (Or.inr hBirth)⟩

private theorem postWriterRequestA
    (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (host : B9Host.HostRow P) (view : P → Phys psi kappa tau)
    (WP : WriterProtected ring psi P) (b : EntranceBudgets)
    (hTraffic : HostDirectionalTrafficExitEnv host view ring WP b.traffic.L)
    (hExpiry : HostComparisonExpiryWordEnv hpsi h2 host view ring WP b.expiry.L)
    (hK2 : HostK2ClearableOrLeaderV3 hpsi h2 host view ring WP b.k2.L)
    (hRuler : HostRulerWordV2 hpsi host view ring WP b.ruler.L)
    (hRoute : HostRouteWordV2 hpsi host view ring WP b.route.L)
    (X : Workspace ring psi) (C : PConfig n P)
    (hC : HostLeaderless view C) (hW : WriterAt WP X C) :
    ∃ w, InternalWord X.env.I w ∧ w.length ≤ postWriterL b ∧
      HostExit host view ring X.env.I (fun _ => False) (runHost host ring w C) := by
  obtain ⟨u,huI,huL,huE⟩ := hTraffic X C hC hW
  obtain ⟨u1,h1I,h1L,h1E⟩ := continueRequestA host view X.env.I
    (TrafficAtEnv view WP X)
    (fun D => ExpiryAtEnv view WP X D ∧ R1DrainStableForK2 hpsi h2 host view ring X D)
    C u b.traffic.L b.expiry.L huI huL huE (fun D hD hT => hExpiry X D hD hT)
  obtain ⟨u2,h2I,h2L,h2E⟩ := continueRequestA host view X.env.I
    (fun D => ExpiryAtEnv view WP X D ∧ R1DrainStableForK2 hpsi h2 host view ring X D)
    (K2DrainedAt view WP X) C u1 (b.traffic.L + b.expiry.L) b.k2.L
    h1I h1L h1E (fun D hD hE => hK2 X D hD hE)
  have hR := B6EntranceV2.coreStageWord_stage host view ring WP
    (K2DrainedAt view WP) (CorePreparedV2 hpsi view WP) b.ruler.L hRuler
  obtain ⟨u3,h3I,h3L,h3E⟩ := continueRequestA host view X.env.I
    (K2DrainedAt view WP X) (CorePreparedV2 hpsi view WP X) C u2
    ((b.traffic.L + b.expiry.L) + b.k2.L) b.ruler.L h2I h2L h2E
    (fun D hD hS => hR X D hD hS)
  have hRoute' := B6EntranceV2.coreStageWord_stage host view ring WP
    (CorePreparedV2 hpsi view WP) (fun _ _ => False) b.route.L hRoute
  exact continueRequestA host view X.env.I (CorePreparedV2 hpsi view WP X)
    (fun _ => False) C u3 (((b.traffic.L + b.expiry.L) + b.k2.L) + b.ruler.L)
    b.route.L h3I h3L h3E (fun D hD hP => hRoute' X D hD hP)

private theorem readyWindowReducedA
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) (ring : DirectedRing n)
    (h : ReducedC4LeafInputsV31 hpsi h2 ring) :
    UniformHostReadyWindowEscape
      (B9Host.r1Host (kappa := psi) (tau := 16 * psi) hpsi h2)
      (fun q : Phys psi psi (16 * psi) => q) ring
      (entranceB n (c4Budget n psi)) (entranceQ (c4Budget n psi)) := by
  rcases h.budgetValid with ⟨hBw,hTouch,_,_,_,_,_,hPostQ,hPostMatch⟩
  have hAdmission : HostWriterAdmission
      (B9Host.r1Host (kappa := psi) (tau := 16 * psi) hpsi h2)
      (fun q : Phys psi psi (16 * psi) => q) ring
      (B6EntranceLawsWiring2.WPfinal (psi := psi) ring) (c4Budget n psi).writer.L :=
    writerAdmission_of_writerAdmissionV3 _ _ ring _ _ h.writerAdmission
  have hWriter := B6EntranceV2.writerAdmission_mass
    (B9Host.r1Host (kappa := psi) (tau := 16 * psi) hpsi h2)
    (fun q : Phys psi psi (16 * psi) => q) ring
    (B6EntranceLawsWiring2.WPfinal (psi := psi) ring) (c4Budget n psi)
    hBw hTouch h.writerLocal hAdmission
  have hTail : ∀ C : PConfig n (Phys psi psi (16 * psi)),
      HostAlive (fun q : Phys psi psi (16 * psi) => q) ring C →
      WriterStage (B6EntranceLawsWiring2.WPfinal (psi := psi) ring) C →
      postWriterQ (c4Budget n psi) * aliveCount
        (B9Host.hostStep (B9Host.r1Host (kappa := psi) (tau := 16 * psi) hpsi h2) ring)
        (HostAlive (fun q : Phys psi psi (16 * psi) => q) ring) C
        (postWriterB n (c4Budget n psi)) ≤
      (postWriterQ (c4Budget n psi) - 1) * n ^ postWriterB n (c4Budget n psi) := by
    intro C hC hStage
    rcases hStage with ⟨X,hX⟩
    obtain ⟨w,hI,hL,hExit⟩ := postWriterRequestA hpsi h2
      (B9Host.r1Host (kappa := psi) (tau := 16 * psi) hpsi h2)
      (fun q : Phys psi psi (16 * psi) => q)
      (B6EntranceLawsWiring2.WPfinal (psi := psi) ring) (c4Budget n psi)
      h.trafficWord h.expiryWord h.k2Word h.rulerWord h.routeWord X C hC.1 hX
    have hM := one_le_envelopeTouchBound psi
    have hb : B6EntranceCompose.EscapeBudget n (postWriterL (c4Budget n psi))
        (envelopeTouchBound psi) (postWriterB n (c4Budget n psi))
        (postWriterQ (c4Budget n psi)) := ⟨hM,hPostQ,rfl,hPostMatch⟩
    have hm := B6EntranceV2.hostRequest_mass_of_budget
      (B9Host.r1Host (kappa := psi) (tau := 16 * psi) hpsi h2)
      (fun q : Phys psi psi (16 * psi) => q) ring X.env.I (fun _ => False) w C
      _ _ _ _ hb hL (B6EntranceV2.envelope_touch_le X) hC.1
      (by intro A D _; simp) ⟨hI,hExit⟩
    rw [B6EntranceV2.avoidCount_eq_hostPending _ _ ring (fun _ => False) C _] at hm
    have hPendingFalse :
        (HostPending (fun q : Phys psi psi (16 * psi) => q) ring
          (fun _ : PConfig n (Phys psi psi (16 * psi)) => False)) =
          HostAlive (fun q : Phys psi psi (16 * psi) => q) ring := by
      funext D
      simp only [HostPending, not_false_eq_true, and_true]
    rw [hPendingFalse] at hm
    exact hm
  have hQw : 1 ≤ (c4Budget n psi).writer.Q := hBw.2.1
  have htwo : UniformEscapeMass
      (B9Host.hostStep (B9Host.r1Host (kappa := psi) (tau := 16 * psi) hpsi h2) ring)
      (HostAlive (fun q : Phys psi psi (16 * psi) => q) ring)
      (entranceB n (c4Budget n psi)) (entranceQ (c4Budget n psi)) := by
    change UniformEscapeMass _ _ ((c4Budget n psi).writer.B + postWriterB n (c4Budget n psi))
      ((c4Budget n psi).writer.Q * postWriterQ (c4Budget n psi))
    exact BirthTwoStageEscape.two_stage_escape _ _
      (WriterStage (B6EntranceLawsWiring2.WPfinal (psi := psi) ring)) _ _ _ _
      hQw hPostQ hWriter hTail
  intro C hC
  rw [B6LocalReverseFill.avoidCount_eq_alive_complement]
  change entranceQ (c4Budget n psi) * aliveCount _
      (HostAlive (fun q : Phys psi psi (16 * psi) => q) ring) C _ ≤ _
  by_cases hReady : HostReadyWindow (fun q : Phys psi psi (16 * psi) => q) ring C
  · rw [BirthTwoStageEscape.aliveCount_not_good _ _ C (fun hA => hA.2 hReady) _, Nat.mul_zero]
    exact Nat.zero_le _
  · exact htwo C ⟨hC,hReady⟩

/-- Reduced C4 inputs + the admitted simulation give the admitted Q=8 leaf. -/
theorem sharedBirthWordMassAdmitted_of_reducedInputs
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) (h3 : 2 < psi) (hpsin : psi ≤ n)
    (ring : DirectedRing n) (hC4 : ReducedC4LeafInputsV31 hpsi h2 ring)
    (hSim : C4C5AdmittedR1MassSimulation hpsi h2 ring) :
    C4C5SharedBirthWordMassAdmittedAt hpsi h2 ring (FinalLeafHV2 n psi) := by
  have hh := readyWindowReducedA hpsi h2 ring hC4
  have hs : B9Host.hostStep
      (B9Host.r1Host (kappa := psi) (tau := 16 * psi) hpsi h2) ring = step1 hpsi h2 ring := by
    funext C e; exact B9Host.hostStep_r1_eq_step1 hpsi h2 ring C e
  have hReady : ∀ C : BirthCheckPermitRepairLeaf.FC n psi psi (16 * psi),
      BirthShortDoneTerminalFirstHit.Leaderless C →
      entranceQ (c4Budget n psi) * avoidCount (step1 hpsi h2 ring)
        BirthShortDoneTerminalFirstHit.Leaderless (ReadyWindow ring) C
        (entranceB n (c4Budget n psi)) ≤
      (entranceQ (c4Budget n psi) - 1) * n ^ entranceB n (c4Budget n psi) := by
    intro C hC; have hm := hh C hC; rw [hs] at hm; exact hm
  have hQ : 1 ≤ entranceQ (c4Budget n psi) := by
    rw [c4Budget_entranceQ]
    exact Nat.one_le_pow _ _ (by have ht := one_le_envelopeTouchBound psi; omega)
  have hn : 1 ≤ n := by omega
  have hH : 3 * (entranceQ (c4Budget n psi) * Q2star psi) *
      (entranceB n (c4Budget n psi) + 2 * n * (psi - 1)) ≤ FinalLeafHV2 n psi := by
    simpa [B6EntranceK2Mass4.c4BoostedH, FinalLeafHV2] using
      B6EntranceK2Budget.B6EntranceK2Budget.c4BoostedH_le_correctedFinalLeafH
        n psi (Q2star psi) hn
  exact B6EntranceK2MassAdmitted.c4C5SharedBirthWordMassAdmittedAt_of_r1ReadyWindowMass
    hpsi h2 h3 hpsin ring _ _ (Q2star psi) (FinalLeafHV2 n psi)
    hQ (Q2star_spec psi) hReady hSim hH

private def AdmittedAlive
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) (ring : DirectedRing n)
    (C : FinalCandidateR2C.Config n psi psi (16 * psi)) : Prop :=
  FinalLeaderless C ∧ ConcreteB7AdmittedPassive hpsi h2 ring C

private theorem aliveAlongAdmitted
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) (ring : DirectedRing n)
    (hClosed : ConcreteB7AdmittedPassiveClosedObligation
      (κ := psi) (τ := 16 * psi) hpsi h2 ring)
    (C : FinalCandidateR2C.Config n psi psi (16 * psi))
    (u : List (Fin n))
    (hA : ConcreteB7AdmittedPassive hpsi h2 ring C)
    (h : AliveAlong (stepConcrete (κ := psi) (τ := 16 * psi) hpsi h2 ring)
      FinalLeaderless C u) :
    AliveAlong (stepConcrete (κ := psi) (τ := 16 * psi) hpsi h2 ring)
      (AdmittedAlive hpsi h2 ring) C u := by
  induction u generalizing C with
  | nil => exact ⟨h,hA⟩
  | cons e u ih =>
      rcases h with ⟨hL,hT⟩
      have hLn := aliveAlong_good hT
      have hN := hClosed C e hA hL
      have hA' : ConcreteB7AdmittedPassive hpsi h2 ring
          (stepConcrete (κ := psi) (τ := 16 * psi) hpsi h2 ring C e) := by
        rcases hN with hLead | hAdm
        · rcases hLead with ⟨i,hi⟩
          have hz := hLn i
          rw [hz] at hi
          cases hi
        · exact hAdm
      exact ⟨⟨hL,hA⟩,
        ih (stepConcrete (κ := psi) (τ := 16 * psi) hpsi h2 ring C e) hA' hT⟩

private theorem aliveAlongFinal
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) (ring : DirectedRing n)
    (C : FinalCandidateR2C.Config n psi psi (16 * psi))
    (u : List (Fin n))
    (h : AliveAlong (stepConcrete (κ := psi) (τ := 16 * psi) hpsi h2 ring)
      (AdmittedAlive hpsi h2 ring) C u) :
    AliveAlong (stepConcrete (κ := psi) (τ := 16 * psi) hpsi h2 ring)
      FinalLeaderless C u := by
  induction u generalizing C with
  | nil => exact h.1
  | cons e u ih =>
      exact ⟨h.1.1,
        ih (stepConcrete (κ := psi) (τ := 16 * psi) hpsi h2 ring C e) h.2⟩

private theorem wordSumCongrA {m T : Nat} (f g : List (Fin m) → Nat)
    (h : ∀ u, u.length = T → f u = g u) :
    FixedSpanRenewalPayload.wordSum m T f = FixedSpanRenewalPayload.wordSum m T g := by
  rw [← FixedSpanRenewalPayload.rawWord_sum m T f,
      ← FixedSpanRenewalPayload.rawWord_sum m T g]
  apply FiniteUniformStoppingTree.ofFn_sum_eq
  intro i; exact h _ (FixedSpanRenewalPayload.rawWord_length m T i)

private theorem aliveCountAdmittedEq
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) (ring : DirectedRing n)
    (hClosed : ConcreteB7AdmittedPassiveClosedObligation
      (κ := psi) (τ := 16 * psi) hpsi h2 ring)
    (C : FinalCandidateR2C.Config n psi psi (16 * psi))
    (hA : ConcreteB7AdmittedPassive hpsi h2 ring C) (T : Nat) :
    aliveCount (stepConcrete (κ := psi) (τ := 16 * psi) hpsi h2 ring)
        FinalLeaderless C T =
      aliveCount (stepConcrete (κ := psi) (τ := 16 * psi) hpsi h2 ring)
        (AdmittedAlive hpsi h2 ring) C T := by
  unfold aliveCount
  apply wordSumCongrA
  intro u _
  classical
  unfold aliveBit
  by_cases hf : AliveAlong (stepConcrete (κ := psi) (τ := 16 * psi) hpsi h2 ring)
      FinalLeaderless C u
  · have ha := aliveAlongAdmitted hpsi h2 ring hClosed C u hA hf
    simp [hf,ha]
  · have ha : ¬ AliveAlong (stepConcrete (κ := psi) (τ := 16 * psi) hpsi h2 ring)
        (AdmittedAlive hpsi h2 ring) C u :=
      fun x => hf (aliveAlongFinal hpsi h2 ring C u x)
    simp [hf,ha]

/-- Admitted analogue of `CFinalTailComposition.b7_bound_of_sharedBirthWordMass`. -/
theorem b7Admitted_of_sharedBirthWordMass
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) (hn2 : 2 ≤ n) (ring : DirectedRing n) (H : Nat)
    (hClosed : ConcreteB7AdmittedPassiveClosedObligation
      (κ := psi) (τ := 16 * psi) hpsi h2 ring)
    (hLeaf : C4C5SharedBirthWordMassAdmittedAt hpsi h2 ring H) :
    FinalB7OneOverNAdmittedAt hpsi h2 ring H := by
  have hMass : UniformEscapeMass
      (stepConcrete (κ := psi) (τ := 16 * psi) hpsi h2 ring)
      (AdmittedAlive hpsi h2 ring) H 8 := by
    intro C hCA
    have hm := hLeaf C hCA.2 hCA.1
    rw [← B9RecoveryGate.stepConcrete_aliveCount_eq_avoidCount_hasLeader
      (kappa := psi) (tau := 16 * psi) hpsi h2 ring C H] at hm
    rw [aliveCountAdmittedEq hpsi h2 ring hClosed C hCA.2 H] at hm
    exact hm
  unfold FinalB7OneOverNAdmittedAt
  intro C hA hL
  have ht := BirthLeaderlessBirthMassRenewal.tail_one_over_n
    (stepConcrete (κ := psi) (τ := 16 * psi) hpsi h2 ring)
    (AdmittedAlive hpsi h2 ring) H hMass hn2 C ⟨hL,hA⟩
  change n * aliveCount
      (stepConcrete (κ := psi) (τ := 16 * psi) hpsi h2 ring)
      FinalLeaderless C (6 * (Nat.log2 n + 1) * H) ≤ _
  rw [aliveCountAdmittedEq hpsi h2 ring hClosed C hA
    (6 * (Nat.log2 n + 1) * H)]
  exact ht

/-!
REFEREE READING.

`b7Admitted_bound_of_reducedInputs` is a theorem about the admitted lane.  Under
`2 < psi`, `psi <= n`, the reduced C4 stage inputs, R2-to-R1 agreement, and the
stopped admission-closure obligation, it gives the exact B7 one-over-n failure
bound with horizon based on `FinalLeafHV2`.

It does NOT say that every legal initial protocol state is admitted.  The
conclusion is `FinalB7OneOverNAdmittedAt`; after unfolding it, the quantified
configuration still carries the premise `ConcreteB7AdmittedPassive ... C`
(and `FinalLeaderless C`).  Thus this closes the birth tail only after entry to
the admitted lane.The single upstream theorem still needed to remove that premise should be named
`CFinalAdmissionEntrance.firstHitToAdmittedPassiveOrLeaderMass` and live in a
new `Leader/Wu/Entrance/FirstHitAdmissionMass.lean`.  It must give, from every legal
initial final-carrier state, a finite-horizon first-hit mass bound for the
literal `stepConcrete` process whose success target is
`HasLeader D ∨ ConcreteB7AdmittedPassive ... D`, with explicit horizon and
mass denominator strong enough to compose with this admitted B7 tail.  Mere
eventual reachability, or the existing admission-closure theorem, is not enough.
-/

theorem b7Admitted_bound_of_reducedInputs
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) (h3 : 2 < psi) (hpsin : psi ≤ n)
    (ring : DirectedRing n)
    (hC4 : ReducedC4LeafInputsV31 hpsi h2 ring)
    (hR2 : R2Coherence.R2R1AgreementObligation
      (κ := psi) (τ := 16 * psi) hpsi h2 ring)
    (hClosed : ConcreteB7AdmittedPassiveClosedObligation
      (κ := psi) (τ := 16 * psi) hpsi h2 ring) :
    FinalB7OneOverNAdmittedAt hpsi h2 ring (FinalLeafHV2 n psi) := by
  have hn2 : 2 ≤ n := by omega
  have hSim := B6EntranceK2MassAdmitted.c4C5AdmittedR1MassSimulation_of_closed
    hpsi h2 ring hn2 hClosed hR2
  have hLeaf := sharedBirthWordMassAdmitted_of_reducedInputs
    hpsi h2 h3 hpsin ring hC4 hSim
  exact b7Admitted_of_sharedBirthWordMass
    hpsi h2 hn2 ring (FinalLeafHV2 n psi) hClosed hLeaf

end CFinalAdmittedAssembly
