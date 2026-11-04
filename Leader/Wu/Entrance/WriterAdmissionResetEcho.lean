import Leader.Wu.Entrance.EnvelopeResetEchoWord

set_option autoImplicit false
set_option Elab.async false

namespace B6EntranceAdmissionV3

open PPLL PPLLResearchFormulation PPLLExpiringComparisonRepair
open B6LocalReverseFill
open B6EntranceV2 B6EntranceV2K2 B6EntranceV3
open B6EntranceEnvelopeFrame B6EntranceEnvelopeWord

variable {n psi kappa tau : Nat} {P : Type}
variable {ring : DirectedRing n}

/-- V3 writer admission: exactly the old `HostWriterAdmission` shape, but a
successful endpoint carries the missing envelope-boundary reset/echo fact in
addition to `WriterAt`.  It deliberately does not duplicate the core half of
`TrafficAt`; that is still the traffic stage's job. -/
def HostWriterAdmissionV3
    (host : B9Host.HostRow P) (view : P → Phys psi kappa tau)
    (ring : DirectedRing n) (WP : WriterProtected ring psi P)
    (L : Nat) : Prop :=
  ∀ C : PConfig n P, HostLeaderless view C →
    ∃ X : Workspace ring psi, ∃ w : List (Fin n),
      InternalWord X.env.I w ∧ w.length ≤ L ∧
      HostExit host view ring X.env.I
        (fun D =>
          WriterAt WP X D ∧
            EnvelopeBoundaryResetEchoClear view X D)
        (runHost host ring w C)

/-- `EntranceHostLawsV3` with only writer admission strengthened. -/
structure EntranceHostLawsV3b
    (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (host : B9Host.HostRow P) (view : P → Phys psi kappa tau)
    (ring : DirectedRing n) (WP : WriterProtected ring psi P)
    (b : EntranceBudgets) : Prop where
  writerLocal : HostWriterProtectedLocal WP
  bitSilence : HostCoreBitSilence host view ring WP
  staticExpiry : HostStaticExpiryTick host view
  writerAdmission : HostWriterAdmissionV3
    host view ring WP b.writer.L
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

/-- Forgetting the collar conjunct recovers the exact old admission law. -/
theorem writerAdmission_of_writerAdmissionV3
    (host : B9Host.HostRow P) (view : P → Phys psi kappa tau)
    (ring : DirectedRing n) (WP : WriterProtected ring psi P)
    (L : Nat)
    (h : HostWriterAdmissionV3 host view ring WP L) :
    HostWriterAdmission host view ring WP L := by
  intro C hC
  obtain ⟨X, w, hInt, hLen, hExit⟩ := h C hC
  refine ⟨X, w, hInt, hLen, ?_⟩
  rcases hExit with hTarget | hRest
  · exact Or.inl hTarget.1
  · exact Or.inr hRest

/-- Compatibility projection: every V3b law bundle is an old V3 bundle. -/
theorem entranceLawsV3b_to_V3
    (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (host : B9Host.HostRow P) (view : P → Phys psi kappa tau)
    (ring : DirectedRing n) (WP : WriterProtected ring psi P)
    (b : EntranceBudgets)
    (hlaws : EntranceHostLawsV3b hpsi h2 host view ring WP b) :
    EntranceHostLawsV3 hpsi h2 host view ring WP b := by
  exact {
    writerLocal := hlaws.writerLocal
    bitSilence := hlaws.bitSilence
    staticExpiry := hlaws.staticExpiry
    writerAdmission := writerAdmission_of_writerAdmissionV3
      host view ring WP b.writer.L hlaws.writerAdmission
    trafficWord := hlaws.trafficWord
    expiryWord := hlaws.expiryWord
    k2Word := hlaws.k2Word
    rulerWord := hlaws.rulerWord
    routeWord := hlaws.routeWord
  }

/-- Therefore the existing V3 assembly theorem is reused verbatim. -/
theorem entranceLawsV3b_to_V2
    (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (host : B9Host.HostRow P) (view : P → Phys psi kappa tau)
    (ring : DirectedRing n) (WP : WriterProtected ring psi P)
    (b : EntranceBudgets) (hbud : b.Valid n psi)
    (hlaws : EntranceHostLawsV3b hpsi h2 host view ring WP b) :
    UniformHostReadyWindowEscape host view ring
      (entranceB n b) (entranceQ b) :=
  B6EntranceV3.entranceLawsV3_to_V2
    hpsi h2 host view ring WP b hbud
    (entranceLawsV3b_to_V3 hpsi h2 host view ring WP b hlaws)

namespace B6EntranceAdmissionV3

/-- V3b admission -> V3 traffic exit -> preservation through the fixed K2
word.  `hDrainLeaderless` is exactly the prefix-leaderless side condition,
specialized to every successful traffic endpoint. -/
theorem k2_trafficAtEnv_of_lawsV3b
    (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (WP : WriterProtected ring psi (Phys psi kappa tau))
    (b : EntranceBudgets)
    (hlaws :
      EntranceHostLawsV3b hpsi h2
        (B9Host.r1Host (kappa := kappa) (tau := tau) hpsi h2)
        (fun q : Phys psi kappa tau => q) ring WP b)
    (X : Workspace ring psi)
    (C : PConfig n (Phys psi kappa tau))
    (hC : HostLeaderless (fun q : Phys psi kappa tau => q) C)
    (hAdmission :
      WriterAt WP X C ∧
        EnvelopeBoundaryResetEchoClear
          (fun q : Phys psi kappa tau => q) X C)
    (hDrainLeaderless :
      ∀ D : PConfig n (Phys psi kappa tau),
        TrafficAtEnv (fun q : Phys psi kappa tau => q) WP X D →
        B6WriterSilentGuarded.LeaderlessAlong hpsi h2 ring D
          (k2DrainWord ring X)) :
    ∃ u : List (Fin n),
      InternalWord X.env.I u ∧ u.length ≤ b.traffic.L ∧
      HostExit
        (B9Host.r1Host (kappa := kappa) (tau := tau) hpsi h2)
        (fun q : Phys psi kappa tau => q) ring X.env.I
        (fun D =>
          TrafficAtEnv (fun q : Phys psi kappa tau => q) WP X
            (runHost
              (B9Host.r1Host
                (kappa := kappa) (tau := tau) hpsi h2)
              ring (k2DrainWord ring X) D))
        (runHost
          (B9Host.r1Host (kappa := kappa) (tau := tau) hpsi h2)
          ring u C) := by
  have hV3 :
      EntranceHostLawsV3 hpsi h2
        (B9Host.r1Host (kappa := kappa) (tau := tau) hpsi h2)
        (fun q : Phys psi kappa tau => q) ring WP b :=
    entranceLawsV3b_to_V3 hpsi h2
      (B9Host.r1Host (kappa := kappa) (tau := tau) hpsi h2)
      (fun q : Phys psi kappa tau => q) ring WP b hlaws
  obtain ⟨u, huI, huL, hExit⟩ :=
    hlaws.trafficWord X C hC hAdmission.1
  refine ⟨u, huI, huL, ?_⟩
  rcases hExit with hTraffic | hRest
  · exact Or.inl
      (B6EntranceEnvelopeWord.r1_internal_word_trafficAtEnv_of_laws
        (ring := ring) (kappa := kappa) (tau := tau)
        hpsi h2 WP b hV3 X (k2DrainWord ring X)
        (runHost
          (B9Host.r1Host (kappa := kappa) (tau := tau) hpsi h2)
          ring u C)
        (B6EntranceV2K2.k2DrainWord_internal ring X)
        (hDrainLeaderless _ hTraffic) hTraffic)
  · exact Or.inr hRest

end B6EntranceAdmissionV3


