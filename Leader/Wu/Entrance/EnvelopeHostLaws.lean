import Leader.Wu.Entrance.CoreHostLaws
import Leader.Wu.Entrance.PermitRowWriterLaw
import Leader.Wu.Safety.PermitRepairQuietLap


set_option autoImplicit false
set_option Elab.async false
set_option pp.structureInstances false


namespace B6EntranceV3


open PPLL PPLLResearchFormulation PPLLExpiringComparisonRepair
open BirthShortDoneTerminalFirstHit BirthCheckChainR1Ring
open BirthLeaderlessBirthMassRenewal BirthTwoStageEscape
open FiniteUniformStoppingTree FixedSpanRenewalPayload
open B6LocalReverseFill
open B6EntranceV2 B6EntranceV2K2


variable {n psi kappa tau : Nat} {P : Type}
variable {ring : DirectedRing n}


/-- Whole-envelope analogue of `CoreAll`. -/
def EnvAll (view : P → Phys psi kappa tau) (X : Workspace ring psi)
    (Pred : Phys psi kappa tau → Prop) (C : PConfig n P) : Prop :=
  ∀ i, support X.env.I i = true → Pred (view (C i))


/-- Traffic exit after the collar reset/echo condition is widened from the
core to the whole envelope. -/
def TrafficAtEnv (view : P → Phys psi kappa tau)
    (WP : WriterProtected ring psi P)
    (X : Workspace ring psi) (C : PConfig n P) : Prop :=
  WriterAt WP X C ∧ EnvAll view X ResetEchoClearCell C


/-- Comparison expiry after both reset/echo and comparison sanitation are
required on the whole envelope. -/
def ExpiryAtEnv (view : P → Phys psi kappa tau)
    (WP : WriterProtected ring psi P)
    (X : Workspace ring psi) (C : PConfig n P) : Prop :=
  TrafficAtEnv view WP X C ∧ EnvAll view X ComparisonCleanCell C


/-- Schedule-specific pre-CHECK certificate for the literal reverse K2 word.
For every prefix that is still leaderless and has a next scheduled edge, both
endpoints are quiet at the actual `checkInput` cut and writer-dormant at the
actual writer-input cut used by `R1CandidateKernel.EdgeSafe`. -/
def R1DrainStableForK2
    (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (host : B9Host.HostRow P) (view : P → Phys psi kappa tau)
    (ring : DirectedRing n) (X : Workspace ring psi)
    (C : PConfig n P) : Prop :=
  ∀ (u v : List (Fin n)) (e : Fin n),
    k2DrainWord ring X = u ++ (e :: v) →
      let D := runHost host ring u C
      HostLeaderless view D →
        let l := view (D e)
        let r := view (D (ring.rightNeighbor e))
        let q := R1CandidateKernel.checkInput hpsi h2 l r
        let w := R1CandidateKernel.writerInput hpsi h2 l r
        R1CandidateKernel.AuthQuiet q.1 ∧
          R1CandidateKernel.AuthQuiet q.2 ∧
          R1CandidateKernel.WriterDormant w.1.core ∧
          R1CandidateKernel.WriterDormant w.2.core


/-- Envelope-strengthened directional-traffic stage. -/
def HostDirectionalTrafficExitEnv
    (host : B9Host.HostRow P) (view : P → Phys psi kappa tau)
    (ring : DirectedRing n) (WP : WriterProtected ring psi P)
    (L : Nat) : Prop :=
  HostStageWord host view ring WP
    (WriterAt WP) (TrafficAtEnv view WP) L


/-- Envelope-strengthened comparison-expiry stage.  Its target also certifies
that the fixed reverse K2 schedule is quiet at every literal pre-CHECK cut. -/
def HostComparisonExpiryWordEnv
    (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (host : B9Host.HostRow P) (view : P → Phys psi kappa tau)
    (ring : DirectedRing n) (WP : WriterProtected ring psi P)
    (L : Nat) : Prop :=
  HostStageWord host view ring WP
    (TrafficAtEnv view WP)
    (fun X C => ExpiryAtEnv view WP X C ∧
      R1DrainStableForK2 hpsi h2 host view ring X C) L


/-- Corrected K2 source: whole-envelope expiry plus the fixed-word operational
cut certificate; the destination remains the compiled V2 K2 endpoint. -/
def HostK2ClearableOrLeaderV3
    (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (host : B9Host.HostRow P) (view : P → Phys psi kappa tau)
    (ring : DirectedRing n) (WP : WriterProtected ring psi P)
    (L : Nat) : Prop :=
  HostStageWord host view ring WP
    (fun X C => ExpiryAtEnv view WP X C ∧
      R1DrainStableForK2 hpsi h2 host view ring X C)
    (K2DrainedAt view WP) L


/-- V3 entrance bundle.  Writer admission/locality, bit silence, static expiry,
ruler and route are unchanged; only traffic, expiry and K2 boundaries change. -/
structure EntranceHostLawsV3
    (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (host : B9Host.HostRow P) (view : P → Phys psi kappa tau)
    (ring : DirectedRing n) (WP : WriterProtected ring psi P)
    (b : EntranceBudgets) : Prop where
  writerLocal : HostWriterProtectedLocal WP
  bitSilence : HostCoreBitSilence host view ring WP
  staticExpiry : HostStaticExpiryTick host view
  writerAdmission : HostWriterAdmission host view ring WP b.writer.L
  trafficWord : HostDirectionalTrafficExitEnv
    host view ring WP b.traffic.L
  expiryWord : HostComparisonExpiryWordEnv
    hpsi h2 host view ring WP b.expiry.L
  k2Word : HostK2ClearableOrLeaderV3
    hpsi h2 host view ring WP b.k2.L
  rulerWord : HostRulerWordV2
    hpsi host view ring WP b.ruler.L
  routeWord : HostRouteWordV2
    hpsi host view ring WP b.route.L


/-- Whole-envelope reset/echo immediately implies the old core reset/echo. -/
theorem trafficAtEnv_to_trafficAt
    (view : P → Phys psi kappa tau)
    (WP : WriterProtected ring psi P)
    (X : Workspace ring psi) (C : PConfig n P)
    (h : TrafficAtEnv view WP X C) : TrafficAt view WP X C := by
  refine ⟨h.1, ?_⟩
  intro i hi
  exact h.2 i (X.core.subset i hi)


/-- Cheap bridge: envelope expiry implies the old core
expiry predicate. -/
theorem expiryAtEnv_to_expiryAt
    (view : P → Phys psi kappa tau)
    (WP : WriterProtected ring psi P)
    (X : Workspace ring psi) (C : PConfig n P)
    (h : ExpiryAtEnv view WP X C) : ExpiryAt view WP X C := by
  refine ⟨trafficAtEnv_to_trafficAt view WP X C h.1, ?_⟩
  intro i hi
  exact h.2 i (X.core.subset i hi)


private theorem internalWord_appendV3 (I : Interval ring)
    (u v : List (Fin n)) (hu : InternalWord I u) (hv : InternalWord I v) :
    InternalWord I (u ++ v) := by
  intro e he
  rcases List.mem_append.mp he with he | he
  · exact hu e he
  · exact hv e he


private theorem runHost_appendV3 (host : B9Host.HostRow P)
    (ring : DirectedRing n) (u v : List (Fin n)) (C : PConfig n P) :
    runHost host ring (u ++ v) C =
      runHost host ring v (runHost host ring u C) := by
  simp only [runHost, List.foldl_append]


private theorem continue_requestV3
    (host : B9Host.HostRow P) (view : P → Phys psi kappa tau)
    (ring : DirectedRing n) (I : Interval ring)
    (A B : PConfig n P → Prop) (C : PConfig n P)
    (u : List (Fin n)) (Lu Lv : Nat)
    (huI : InternalWord I u) (huL : u.length ≤ Lu)
    (huE : HostExit host view ring I A (runHost host ring u C))
    (hnext : ∀ D : PConfig n P, HostLeaderless view D → A D →
      ∃ v : List (Fin n), InternalWord I v ∧ v.length ≤ Lv ∧
        HostExit host view ring I B (runHost host ring v D)) :
    ∃ w : List (Fin n), InternalWord I w ∧ w.length ≤ Lu + Lv ∧
      HostExit host view ring I B (runHost host ring w C) := by
  rcases huE with hA | hHit | hBirth
  · let D := runHost host ring u C
    by_cases hD : HostLeaderless view D
    · obtain ⟨v, hvI, hvL, hvE⟩ := hnext D hD hA
      refine ⟨u ++ v, internalWord_appendV3 I u v huI hvI, ?_, ?_⟩
      · simp only [List.length_append]
        omega
      · rw [runHost_appendV3]
        exact hvE
    · exact ⟨u, huI, by omega, Or.inr (Or.inr hD)⟩
  · exact ⟨u, huI, by omega, Or.inr (Or.inl hHit)⟩
  · exact ⟨u, huI, by omega, Or.inr (Or.inr hBirth)⟩


private theorem postWriterRequestV3
    (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (host : B9Host.HostRow P) (view : P → Phys psi kappa tau)
    (ring : DirectedRing n) (WP : WriterProtected ring psi P)
    (b : EntranceBudgets)
    (hTraffic : HostDirectionalTrafficExitEnv
      host view ring WP b.traffic.L)
    (hExpiry : HostComparisonExpiryWordEnv
      hpsi h2 host view ring WP b.expiry.L)
    (hK2 : HostK2ClearableOrLeaderV3
      hpsi h2 host view ring WP b.k2.L)
    (hRuler : HostRulerWordV2 hpsi host view ring WP b.ruler.L)
    (hRoute : HostRouteWordV2 hpsi host view ring WP b.route.L)
    (X : Workspace ring psi) (C : PConfig n P)
    (hC : HostLeaderless view C) (hW : WriterAt WP X C) :
    ∃ w : List (Fin n), InternalWord X.env.I w ∧
      w.length ≤ postWriterL b ∧
      HostExit host view ring X.env.I (fun _ => False)
        (runHost host ring w C) := by
  obtain ⟨u, huI, huL, huE⟩ := hTraffic X C hC hW
  obtain ⟨u1, hu1I, hu1L, hu1E⟩ :=
    continue_requestV3 host view ring X.env.I
      (TrafficAtEnv view WP X)
      (fun D => ExpiryAtEnv view WP X D ∧
        R1DrainStableForK2 hpsi h2 host view ring X D)
      C u b.traffic.L b.expiry.L huI huL huE
      (fun D hD hT => hExpiry X D hD hT)
  obtain ⟨u2, hu2I, hu2L, hu2E⟩ :=
    continue_requestV3 host view ring X.env.I
      (fun D => ExpiryAtEnv view WP X D ∧
        R1DrainStableForK2 hpsi h2 host view ring X D)
      (K2DrainedAt view WP X)
      C u1 (b.traffic.L + b.expiry.L) b.k2.L
      hu1I hu1L hu1E (fun D hD hE => hK2 X D hD hE)
  have hRuler' := B6EntranceV2.coreStageWord_stage host view ring WP
    (K2DrainedAt view WP) (CorePreparedV2 hpsi view WP)
    b.ruler.L hRuler
  obtain ⟨u3, hu3I, hu3L, hu3E⟩ :=
    continue_requestV3 host view ring X.env.I
      (K2DrainedAt view WP X) (CorePreparedV2 hpsi view WP X)
      C u2 ((b.traffic.L + b.expiry.L) + b.k2.L) b.ruler.L
      hu2I hu2L hu2E (fun D hD hS => hRuler' X D hD hS)
  have hRoute' := B6EntranceV2.coreStageWord_stage host view ring WP
    (CorePreparedV2 hpsi view WP) (fun _ _ => False)
    b.route.L hRoute
  obtain ⟨u4, hu4I, hu4L, hu4E⟩ :=
    continue_requestV3 host view ring X.env.I
      (CorePreparedV2 hpsi view WP X) (fun _ => False)
      C u3 (((b.traffic.L + b.expiry.L) + b.k2.L) + b.ruler.L)
      b.route.L hu3I hu3L hu3E
      (fun D hD hP => hRoute' X D hD hP)
  exact ⟨u4, hu4I, hu4L, hu4E⟩
private theorem postWriter_massV3
    (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (host : B9Host.HostRow P) (view : P → Phys psi kappa tau)
    (ring : DirectedRing n) (WP : WriterProtected ring psi P)
    (b : EntranceBudgets)
    (hpostQ : 1 ≤ postWriterQ b)
    (hpostMatch : (4 * envelopeTouchBound psi) ^ postWriterL b ≤
      postWriterQ b)
    (hTraffic : HostDirectionalTrafficExitEnv
      host view ring WP b.traffic.L)
    (hExpiry : HostComparisonExpiryWordEnv
      hpsi h2 host view ring WP b.expiry.L)
    (hK2 : HostK2ClearableOrLeaderV3
      hpsi h2 host view ring WP b.k2.L)
    (hRuler : HostRulerWordV2 hpsi host view ring WP b.ruler.L)
    (hRoute : HostRouteWordV2 hpsi host view ring WP b.route.L) :
    ∀ (X : Workspace ring psi) (C : PConfig n P),
      HostAlive view ring C → WriterAt WP X C →
      postWriterQ b * aliveCount (B9Host.hostStep host ring)
          (HostAlive view ring) C (postWriterB n b) ≤
        (postWriterQ b - 1) * n ^ (postWriterB n b) := by
  intro X C hC hW
  obtain ⟨w, hI, hL, hExit⟩ := postWriterRequestV3
    hpsi h2 host view ring WP b hTraffic hExpiry hK2 hRuler hRoute
    X C hC.1 hW
  have hM : 1 ≤ envelopeTouchBound psi := by
    unfold envelopeTouchBound envelopeWidth coreWidth collarWidth
    omega
  have hbudget : B6EntranceCompose.EscapeBudget n
      (postWriterL b) (envelopeTouchBound psi)
      (postWriterB n b) (postWriterQ b) :=
    ⟨hM, hpostQ, rfl, hpostMatch⟩
  have hm := B6EntranceV2.hostRequest_mass_of_budget
    host view ring X.env.I (fun _ => False) w C
    (postWriterL b) (envelopeTouchBound psi)
    (postWriterB n b) (postWriterQ b)
    hbudget hL (B6EntranceV2.envelope_touch_le X) hC.1
    (by intro A D _; simp) ⟨hI, hExit⟩
  rw [B6EntranceV2.avoidCount_eq_hostPending host view ring
    (fun _ => False) C (postWriterB n b)] at hm
  have hPendingFalse :
      (HostPending view ring (fun _ : PConfig n P => False)) =
        HostAlive view ring := by
    funext D
    simp only [HostPending, not_false_eq_true, and_true]
  rw [hPendingFalse] at hm
  exact hm


/-- Conclusion-level bridge to the compiled V2 theorem: the stochastic layer,
budgets and denominator are unchanged.  We intentionally do not manufacture an
`EntranceHostLawsV2` value, because its weaker K2 source is exactly what V3
removes. -/
theorem entranceLawsV3_to_V2
    (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (host : B9Host.HostRow P) (view : P → Phys psi kappa tau)
    (ring : DirectedRing n) (WP : WriterProtected ring psi P)
    (b : EntranceBudgets) (hbud : b.Valid n psi)
    (hlaws : EntranceHostLawsV3 hpsi h2 host view ring WP b) :
    UniformHostReadyWindowEscape host view ring
      (entranceB n b) (entranceQ b) := by
  rcases hbud with
    ⟨hBw, hTouch, _, _, _, _, _, hPostQ, hPostMatch⟩
  have hQw : 1 ≤ b.writer.Q := hBw.2.1
  have hWriter := B6EntranceV2.writerAdmission_mass
    host view ring WP b hBw hTouch
    hlaws.writerLocal hlaws.writerAdmission
  have hTail : ∀ C : PConfig n P, HostAlive view ring C → WriterStage WP C →
      postWriterQ b * aliveCount (B9Host.hostStep host ring)
          (HostAlive view ring) C (postWriterB n b) ≤
        (postWriterQ b - 1) * n ^ (postWriterB n b) := by
    intro C hC hStage
    rcases hStage with ⟨X, hX⟩
    exact postWriter_massV3 hpsi h2 host view ring WP b
      hPostQ hPostMatch hlaws.trafficWord hlaws.expiryWord hlaws.k2Word
      hlaws.rulerWord hlaws.routeWord X C hC hX
  have htwo : UniformEscapeMass (B9Host.hostStep host ring)
      (HostAlive view ring) (entranceB n b) (entranceQ b) := by
    change UniformEscapeMass (B9Host.hostStep host ring)
      (HostAlive view ring)
      (b.writer.B + postWriterB n b)
      (b.writer.Q * postWriterQ b)
    exact BirthTwoStageEscape.two_stage_escape
      (B9Host.hostStep host ring) (HostAlive view ring) (WriterStage WP)
      b.writer.B (postWriterB n b) b.writer.Q (postWriterQ b)
      hQw hPostQ hWriter hTail
  intro C hC
  rw [B6LocalReverseFill.avoidCount_eq_alive_complement]
  change entranceQ b * aliveCount (B9Host.hostStep host ring)
      (HostAlive view ring) C (entranceB n b) ≤
    (entranceQ b - 1) * n ^ (entranceB n b)
  by_cases hReady : HostReadyWindow view ring C
  · have hnot : ¬ HostAlive view ring C := fun h => h.2 hReady
    rw [BirthTwoStageEscape.aliveCount_not_good
      (B9Host.hostStep host ring) (HostAlive view ring)
      C hnot (entranceB n b), Nat.mul_zero]
    exact Nat.zero_le _
  · exact htwo C ⟨hC, hReady⟩
/-! ## Reset-ingress source is excluded by the V3 envelope boundary -/


namespace Regression


private theorem h3 : 0 < 3 := by decide
private def ring45 : DirectedRing 45 := ⟨by decide⟩


private def envI : Interval ring45 where
  first := 0
  size := 44
  nonempty := by decide
  fits := by decide


private def env : Envelope ring45 3 where
  I := envI
  size_eq := by decide
  proper := by decide


private def coreI : Interval ring45 where
  first := cell ring45 envI.first 4
  size := 36
  nonempty := by decide
  fits := by decide


/-- Concrete workspace geometry: envelope offsets 0..43 and
core offsets 4..39, so envelope offset 3 is the left collar ingress. -/
private def core : Core ring45 3 env where
  J := coreI
  first_eq := rfl
  size_eq := by decide
  subset := by decide


private def X : Workspace ring45 3 := ⟨env, core⟩


private def ingress : Fin 45 := cell ring45 envI.first 3


private theorem ingress_mem_env : support X.env.I ingress = true := by
  change support envI (cell ring45 envI.first 3) = true
  exact B6LocalReverseFill.support_cell envI (by decide)


private def mkCell (i : Fin 45) (resetCmd : Bool) : Phys 3 3 48 :=
  let b : BoundedAgentState 3 3 := {
    leader := false
    probe := false
    phase := false
    bit := false
    wait := true
    state := .none
    path := .bot
    reset := false
    carry := false
    count := 0
    label := ⟨i.val % 3, Nat.mod_lt _ h3⟩
    h_field := false
    path2 := none
    path3 := none
    path4 := none
    path5 := none
    p := false
    p_carry := false
    reset_cmd := resetCmd
    echo := false
    signal_B := 0
    bullet := 0
    shield := false
    write_state := .none
    write := .none
    last := false
    last_set := false
    last_unset := false
    b_carry := false
    gen_ws := false
    ws_echo := false
    signal_ws := false
  }
  ⟨⟨b, false⟩, 1⟩


/-- Exact reset-ingress shape: the only live reset command is at envelope offset 3,
immediately left of the protected core. -/
private def resetIngressSeed : PConfig 45 (Phys 3 3 48) := fun i =>
  if i = ingress then mkCell i true else mkCell i false


private theorem resetIngressSeed_flag :
    (B6Sanitation.rawCell (resetIngressSeed ingress)).reset_cmd = true := by
  rw [resetIngressSeed, if_pos rfl]
  rfl


/-- The V3 traffic boundary sees the collar reset immediately, independently
of the writer predicate.  Hence the reset-ingress source cannot enter the
corrected traffic/expiry/K2 chain. -/
theorem q13396_resetIngress_not_trafficAtEnv
    (WP : WriterProtected ring45 3 (Phys 3 3 48)) :
    ¬ TrafficAtEnv (fun q : Phys 3 3 48 => q) WP X resetIngressSeed := by
  intro h
  have hc := h.2 ingress ingress_mem_env
  unfold ResetEchoClearCell at hc
  dsimp only at hc
  have hfalse :
      (B6Sanitation.rawCell (resetIngressSeed ingress)).reset_cmd = false :=
    hc.1
  have hbad : (true : Bool) = false :=
    resetIngressSeed_flag.symm.trans hfalse
  exact (by decide : (true : Bool) ≠ false) hbad


end Regression


theorem readyWindowEscape_of_seven_laws
    (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (host : B9Host.HostRow P) (view : P → Phys psi kappa tau)
    (ring : DirectedRing n) (WP : WriterProtected ring psi P)
    (b : EntranceBudgets) (hbud : b.Valid n psi)
    (hLocal : HostWriterProtectedLocal WP)
    (hAdmission : HostWriterAdmission host view ring WP b.writer.L)
    (hTraffic : HostDirectionalTrafficExitEnv
      host view ring WP b.traffic.L)
    (hExpiry : HostComparisonExpiryWordEnv
      hpsi h2 host view ring WP b.expiry.L)
    (hK2 : HostK2ClearableOrLeaderV3
      hpsi h2 host view ring WP b.k2.L)
    (hRuler : HostRulerWordV2 hpsi host view ring WP b.ruler.L)
    (hRoute : HostRouteWordV2 hpsi host view ring WP b.route.L) :
    UniformHostReadyWindowEscape host view ring
      (entranceB n b) (entranceQ b) := by
  rcases hbud with
    ⟨hBw, hTouch, _, _, _, _, _, hPostQ, hPostMatch⟩
  have hQw : 1 ≤ b.writer.Q := hBw.2.1
  have hWriter := B6EntranceV2.writerAdmission_mass
    host view ring WP b hBw hTouch hLocal hAdmission
  have hTail : ∀ C : PConfig n P, HostAlive view ring C → WriterStage WP C →
      postWriterQ b * aliveCount (B9Host.hostStep host ring)
          (HostAlive view ring) C (postWriterB n b) ≤
        (postWriterQ b - 1) * n ^ (postWriterB n b) := by
    intro C hC hStage
    rcases hStage with ⟨X, hX⟩
    exact postWriter_massV3 hpsi h2 host view ring WP b
      hPostQ hPostMatch hTraffic hExpiry hK2 hRuler hRoute X C hC hX
  have htwo : UniformEscapeMass (B9Host.hostStep host ring)
      (HostAlive view ring) (entranceB n b) (entranceQ b) := by
    change UniformEscapeMass (B9Host.hostStep host ring)
      (HostAlive view ring)
      (b.writer.B + postWriterB n b)
      (b.writer.Q * postWriterQ b)
    exact BirthTwoStageEscape.two_stage_escape
      (B9Host.hostStep host ring) (HostAlive view ring) (WriterStage WP)
      b.writer.B (postWriterB n b) b.writer.Q (postWriterQ b)
      hQw hPostQ hWriter hTail
  intro C hC
  rw [B6LocalReverseFill.avoidCount_eq_alive_complement]
  change entranceQ b * aliveCount (B9Host.hostStep host ring)
      (HostAlive view ring) C (entranceB n b) ≤
    (entranceQ b - 1) * n ^ (entranceB n b)
  by_cases hReady : HostReadyWindow view ring C
  · have hnot : ¬ HostAlive view ring C := fun h => h.2 hReady
    rw [BirthTwoStageEscape.aliveCount_not_good
      (B9Host.hostStep host ring) (HostAlive view ring)
      C hnot (entranceB n b), Nat.mul_zero]
    exact Nat.zero_le _
  · exact htwo C ⟨hC, hReady⟩

end B6EntranceV3
