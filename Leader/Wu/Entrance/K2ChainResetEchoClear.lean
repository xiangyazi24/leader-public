import Leader.Wu.Entrance.K2Chain
import Leader.Wu.Entrance.PassiveResetEcho

set_option autoImplicit false
set_option Elab.async false

namespace B6EntranceK2ChainCollar

open PPLL PPLLResearchFormulation PPLLExpiringComparisonRepair
open BirthLeaderlessBirthMassRenewal
open B6LocalReverseFill
open B6EntranceV2 B6EntranceV2K2 B6EntranceV3
open B6EntranceEnvelopeFrame B6EntranceEnvelopeWord
open B6EntranceAdmissionV3 B6EntranceAdmissionR1
open B6EntranceExpiryWord
open B4PassiveResetEcho
open FinalCandidateR2C
open FinalCandidateR2C.FinalCandidateR2C.FinalCandidateR2C.FinalCandidateR2C.FinalCandidateR2C

variable {n psi : Nat}
variable {ring : DirectedRing n}

/-- `B6EntranceK2Chain.k2_chain_of_lawsV3b` with its bare-R1 collar premise
replaced by the stronger B4 whole-ring reset/echo clearance.  The explicit
`hBase` identifies the B6 admission endpoint with the bare-R1 projection of
the B4 final configuration. -/
theorem k2_chain_of_lawsV3b_of_resetEchoClear
    (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (WP : WriterProtected ring psi (Phys psi psi (16 * psi)))
    (b : EntranceBudgets)
    (hlaws :
      EntranceHostLawsV3b hpsi h2
        (B9Host.r1Host
          (kappa := psi) (tau := 16 * psi) hpsi h2)
        (fun q : Phys psi psi (16 * psi) => q) ring WP b)
    (X : Workspace ring psi)
    (C : PConfig n (Phys psi psi (16 * psi)))
    (B4C : FinalCandidateR2C.Config n psi psi (16 * psi))
    (hBase : finalBase B4C = C)
    (hC :
      HostLeaderless (fun q : Phys psi psi (16 * psi) => q) C)
    (hWriter : WriterAt WP X C)
    (hClear : FinalResetEchoClear B4C)
    (hDrainLeaderless :
      ∀ D : PConfig n (Phys psi psi (16 * psi)),
        TrafficAtEnv (fun q : Phys psi psi (16 * psi) => q) WP X D →
        B6WriterSilentGuarded.LeaderlessAlong hpsi h2 ring D
          (k2DrainWord ring X))
    (hExpiryCut :
      ∀ E : PConfig n (Phys psi psi (16 * psi)),
        (ExpiryAtEnv (fun q : Phys psi psi (16 * psi) => q) WP X E ∧
          R1DrainStableForK2 hpsi h2
            (B9Host.r1Host
              (kappa := psi) (tau := 16 * psi) hpsi h2)
            (fun q : Phys psi psi (16 * psi) => q) ring X E) →
        R1ExpiryCutSafeAlong
          (kappa := psi) (tau := 16 * psi)
          hpsi h2 ring E (k2DrainWord ring X)) :
    ∃ u : List (Fin n),
      InternalWord X.env.I u ∧ u.length ≤ b.traffic.L ∧
      ∃ w : List (Fin n),
        InternalWord X.env.I w ∧ w.length ≤ b.expiry.L ∧
        HostExit
          (B9Host.r1Host
            (kappa := psi) (tau := 16 * psi) hpsi h2)
          (fun q : Phys psi psi (16 * psi) => q) ring X.env.I
          (fun E =>
            let K :=
              runHost
                (B9Host.r1Host
                  (kappa := psi) (tau := 16 * psi) hpsi h2)
                ring (k2DrainWord ring X) E
            TrafficAtEnv
                (fun q : Phys psi psi (16 * psi) => q) WP X K ∧
              ExpiryAtEnv
                (fun q : Phys psi psi (16 * psi) => q) WP X K)
          (runHost
            (B9Host.r1Host
              (kappa := psi) (tau := 16 * psi) hpsi h2)
            ring (u ++ w) C) := by
  have hEntry :
      R1CollarClearAtEntry X (finalBase B4C) :=
    B4PassiveResetEcho.r1CollarClearAtEntry_of_finalResetEchoClear
      (ring := ring) X B4C hClear
  rw [hBase] at hEntry
  exact B6EntranceK2Chain.k2_chain_of_lawsV3b
    (ring := ring) hpsi h2 WP b hlaws X C hC hWriter hEntry
      hDrainLeaderless hExpiryCut


/-- Clean-fixture lineage specialization.  `QuietBaseFamily` fixes `psi = 3`,
so the final-carrier expiry parameter is `48 = 16 * 3`.  Clearance is proved
at the quiet fixture, transported along the leaderless passive HOST word, and
then converted to the B6 collar premise only at the resulting admission
endpoint. -/
theorem k2_chain_of_lawsV3b_of_quietBase_passiveWord
    (h3 : 0 < 3) (h23 : 2 ≤ 3) (hn : 2 ≤ n)
    (hClosed : ConcreteB7AdmittedPassiveClosedObligation
      (κ := 3) (τ := 48) h3 h23 ring)
    (hR2 : R2Coherence.R2R1AgreementObligation
      (κ := 3) (τ := 48) h3 h23 ring)
    (B4C : FinalCandidateR2C.Config n 3 3 48)
    (f : Fin n → Fin 3) (word : List (Fin n))
    (hQuiet : finalBase B4C = QuietBaseFamily f)
    (hA : ConcreteB7AdmittedPassive h3 h23 ring B4C)
    (hAlive : AliveAlong
      (stepConcrete (κ := 3) (τ := 48) h3 h23 ring)
      FinalLeaderless B4C word)
    (WP : WriterProtected ring 3 (Phys 3 3 48))
    (b : EntranceBudgets)
    (hlaws :
      EntranceHostLawsV3b h3 h23
        (B9Host.r1Host (kappa := 3) (tau := 48) h3 h23)
        (fun q : Phys 3 3 48 => q) ring WP b)
    (X : Workspace ring 3)
    (C : PConfig n (Phys 3 3 48))
    (hBase :
      finalBase
          (word.foldl
            (stepConcrete (κ := 3) (τ := 48) h3 h23 ring) B4C) =
        C)
    (hC : HostLeaderless (fun q : Phys 3 3 48 => q) C)
    (hWriter : WriterAt WP X C)
    (hDrainLeaderless :
      ∀ D : PConfig n (Phys 3 3 48),
        TrafficAtEnv (fun q : Phys 3 3 48 => q) WP X D →
        B6WriterSilentGuarded.LeaderlessAlong h3 h23 ring D
          (k2DrainWord ring X))
    (hExpiryCut :
      ∀ E : PConfig n (Phys 3 3 48),
        (ExpiryAtEnv (fun q : Phys 3 3 48 => q) WP X E ∧
          R1DrainStableForK2 h3 h23
            (B9Host.r1Host (kappa := 3) (tau := 48) h3 h23)
            (fun q : Phys 3 3 48 => q) ring X E) →
        R1ExpiryCutSafeAlong
          (kappa := 3) (tau := 48)
          h3 h23 ring E (k2DrainWord ring X)) :
    ∃ u : List (Fin n),
      InternalWord X.env.I u ∧ u.length ≤ b.traffic.L ∧
      ∃ w : List (Fin n),
        InternalWord X.env.I w ∧ w.length ≤ b.expiry.L ∧
        HostExit
          (B9Host.r1Host (kappa := 3) (tau := 48) h3 h23)
          (fun q : Phys 3 3 48 => q) ring X.env.I
          (fun E =>
            let K :=
              runHost
                (B9Host.r1Host (kappa := 3) (tau := 48) h3 h23)
                ring (k2DrainWord ring X) E
            TrafficAtEnv (fun q : Phys 3 3 48 => q) WP X K ∧
              ExpiryAtEnv (fun q : Phys 3 3 48 => q) WP X K)
          (runHost
            (B9Host.r1Host (kappa := 3) (tau := 48) h3 h23)
            ring (u ++ w) C) := by
  have hClear0 : FinalResetEchoClear B4C :=
    B4PassiveResetEcho.finalResetEchoClear_of_quietBaseFamily
      B4C f hQuiet
  have hClearWord :
      FinalResetEchoClear
        (word.foldl
          (stepConcrete (κ := 3) (τ := 48) h3 h23 ring) B4C) :=
    B4PassiveResetEcho.finalResetEchoClear_passiveWord
      (ring := ring) h3 h23 hn hClosed hR2 B4C word
        hA hAlive hClear0
  exact k2_chain_of_lawsV3b_of_resetEchoClear
    (ring := ring) h3 h23 WP b hlaws X C
      (word.foldl
        (stepConcrete (κ := 3) (τ := 48) h3 h23 ring) B4C)
      hBase hC hWriter hClearWord hDrainLeaderless hExpiryCut

end B6EntranceK2ChainCollar
