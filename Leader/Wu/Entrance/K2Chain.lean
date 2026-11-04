import Leader.Wu.Entrance.AdmissionCollarClear
import Leader.Wu.Entrance.ExpiryCutWord

set_option autoImplicit false
set_option Elab.async false

namespace B6EntranceK2Chain

open PPLL PPLLResearchFormulation PPLLExpiringComparisonRepair
open B6LocalReverseFill
open B6EntranceV2 B6EntranceV2K2 B6EntranceV3
open B6EntranceEnvelopeFrame B6EntranceEnvelopeWord
open B6EntranceAdmissionV3 B6EntranceAdmissionR1
open B6EntranceExpiryWord

variable {n psi : Nat}
variable {ring : DirectedRing n}

private theorem r1_hostLeaderless_of_leaderlessAlong
    (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (ring : DirectedRing n)
    (C : PConfig n (Phys psi psi (16 * psi)))
    (word : List (Fin n))
    (h : B6WriterSilentGuarded.LeaderlessAlong
      hpsi h2 ring C word) :
    HostLeaderless (fun q : Phys psi psi (16 * psi) => q) C := by
  change BirthShortDoneTerminalFirstHit.Leaderless C
  cases word with
  | nil => exact h
  | cons e rest => exact h.1

private theorem runHost_append
    (host : B9Host.HostRow (Phys psi psi (16 * psi)))
    (ring : DirectedRing n)
    (u w : List (Fin n))
    (C : PConfig n (Phys psi psi (16 * psi))) :
    runHost host ring (u ++ w) C =
      runHost host ring w (runHost host ring u C) := by
  simp only [runHost, List.foldl_append]

/-- Correct C4 staged handoff.

`C` is the fixed admission endpoint.  The traffic law produces `D`; the
expiry law produces the genuine K2 source `E`; only then is the fixed reverse
K2 word run.  Thus no same-state `TrafficAtEnv D -> K2 source D` residual is
needed.

Because `E` is existentially chosen by `hlaws.expiryWord`, the residual
`R1ExpiryCutSafeAlong` premise is continuation-shaped and is asserted exactly
at each successful produced K2 source `E`. -/
theorem k2_chain_of_lawsV3b
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
    (hC :
      HostLeaderless (fun q : Phys psi psi (16 * psi) => q) C)
    (hWriter : WriterAt WP X C)
    (hEntry : R1CollarClearAtEntry X C)
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
  have hNilCore : InternalWord X.core.J ([] : List (Fin n)) := by
    intro e he
    simp at he
  have hWriterNil :
      WriterAt WP X
        (runHost
          (B9Host.r1Host
            (kappa := psi) (tau := 16 * psi) hpsi h2)
          ring ([] : List (Fin n)) C) := by
    simpa [runHost] using hWriter
  have hAdmission0 :=
    B6EntranceAdmissionR1.r1_writerAdmissionV3_target_of_entry
      (ring := ring) hpsi h2 WP X C ([] : List (Fin n))
      hNilCore hEntry hWriterNil
  have hWriterAtC : WriterAt WP X C := by
    simpa [runHost] using hAdmission0.1

  have hV3 :
      EntranceHostLawsV3 hpsi h2
        (B9Host.r1Host
          (kappa := psi) (tau := 16 * psi) hpsi h2)
        (fun q : Phys psi psi (16 * psi) => q) ring WP b :=
    B6EntranceAdmissionV3.entranceLawsV3b_to_V3
      hpsi h2
      (B9Host.r1Host
        (kappa := psi) (tau := 16 * psi) hpsi h2)
      (fun q : Phys psi psi (16 * psi) => q) ring WP b hlaws

  obtain ⟨u, huI, huL, huExit⟩ :=
    hlaws.trafficWord X C hC hWriterAtC
  rcases huExit with hTraffic | hHit | hBirth
  · have hDAlive := hDrainLeaderless _ hTraffic
    have hDLeaderless :=
      r1_hostLeaderless_of_leaderlessAlong
        hpsi h2 ring _ (k2DrainWord ring X) hDAlive
    obtain ⟨w, hwI, hwL, hwExit⟩ :=
      hlaws.expiryWord X
        (runHost
          (B9Host.r1Host
            (kappa := psi) (tau := 16 * psi) hpsi h2)
          ring u C)
        hDLeaderless hTraffic
    refine ⟨u, huI, huL, w, hwI, hwL, ?_⟩
    rw [runHost_append]
    rcases hwExit with hSource | hHit2 | hBirth2
    · have hEAlive := hDrainLeaderless _ hSource.1.1
      have hESafe := hExpiryCut _ hSource
      have hExpiryEnd :=
        B6EntranceExpiryWord.r1_k2DrainWord_expiryAtEnv_of_k2_source
          (ring := ring) (kappa := psi) (tau := 16 * psi)
          hpsi h2 WP b hV3 X _ hEAlive hSource hESafe
      exact Or.inl ⟨hExpiryEnd.1, hExpiryEnd⟩
    · exact Or.inr (Or.inl hHit2)
    · exact Or.inr (Or.inr hBirth2)
  · refine ⟨u, huI, huL, [], ?_, by simp, ?_⟩
    · intro e he
      simp at he
    · simp only [List.append_nil]
      exact Or.inr (Or.inl hHit)
  · refine ⟨u, huI, huL, [], ?_, by simp, ?_⟩
    · intro e he
      simp at he
    · simp only [List.append_nil]
      exact Or.inr (Or.inr hBirth)

end B6EntranceK2Chain
