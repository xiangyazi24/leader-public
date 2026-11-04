import Leader.Wu.Entrance.ExpiryCutQuietWriter
import Leader.Wu.Entrance.ExpiryCutWord
import Leader.Wu.Entrance.EnvelopeHostLaws
import Leader.Wu.Entrance.K2ChainResetEchoClear


set_option autoImplicit false
set_option Elab.async false
set_option pp.structureInstances false


namespace B6EntranceExpiryWord


open PPLL PPLLResearchFormulation PPLLExpiringComparisonRepair
open B6LocalReverseFill
open B6EntranceV2 B6EntranceV2K2 B6EntranceV3
open R1CandidateKernel


variable {n psi kappa tau : Nat}
variable {ring : DirectedRing n}


/- SOURCE — Leader/Wu/Entrance/EnvelopeHostLaws.lean:42-47:
`ExpiryAtEnv view WP X C` is `TrafficAtEnv ... ∧ EnvAll ... ComparisonCleanCell`.


SOURCE — Leader/Wu/Entrance/EnvelopeHostLaws.lean:50-70:
`R1DrainStableForK2` quantifies every decomposition
`k2DrainWord ring X = u ++ (e :: v)` and supplies both `AuthQuiet checkInput`
conjuncts only after a `HostLeaderless` premise for the prefix state.


SOURCE — Leader/Wu/Entrance/ExpiryCutWord.lean:169-180:
`R1ExpiryCutSafeAlong` requires `R1ExpiryCutSafeAt` at the head and recurses
from the actual R1 host successor. -/


/-- First unclosed source obligation.  `ExpiryAtEnv` has no leaderless
conjunct, while `R1DrainStableForK2` is conditional on prefix leaderlessness.
The existing K2 chain already carries exactly this premise separately. -/
def R1ExpiryCutSafeAlongLeaderlessResidual
    (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (ring : DirectedRing n) (X : Workspace ring psi)
    (E : PConfig n (Phys psi kappa tau)) : Prop :=
  B6WriterSilentGuarded.LeaderlessAlong
    hpsi h2 ring E (k2DrainWord ring X)


private def R1PreCheckQuietAlong
    (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (ring : DirectedRing n)
    (C : PConfig n (Phys psi kappa tau))
    (word : List (Fin n)) : Prop :=
  ∀ (u v : List (Fin n)) (e : Fin n),
    word = u ++ (e :: v) →
      let D := runHost
        (B9Host.r1Host (kappa := kappa) (tau := tau) hpsi h2)
        ring u C
      HostLeaderless (fun q : Phys psi kappa tau => q) D →
        let q := checkInput hpsi h2
          (D e) (D (ring.rightNeighbor e))
        AuthQuiet q.1 ∧ AuthQuiet q.2


private theorem r1PreCheckQuietAlong_of_drainStable
    (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (ring : DirectedRing n) (X : Workspace ring psi)
    (E : PConfig n (Phys psi kappa tau))
    (hStable :
      R1DrainStableForK2 hpsi h2
        (B9Host.r1Host (kappa := kappa) (tau := tau) hpsi h2)
        (fun q : Phys psi kappa tau => q) ring X E) :
    R1PreCheckQuietAlong hpsi h2 ring E (k2DrainWord ring X) := by
  intro u v e he
  have hs := hStable u v e he
  dsimp only
  intro hLL
  have hz := hs hLL
  exact ⟨hz.1, hz.2.1⟩


private theorem r1ExpiryCutSafeAlong_of_clean_precheck
    (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (ring : DirectedRing n) (X : Workspace ring psi)
    (word : List (Fin n)) :
    ∀ C : PConfig n (Phys psi kappa tau),
      InternalWord X.env.I word →
      B6WriterSilentGuarded.LeaderlessAlong hpsi h2 ring C word →
      R1PreCheckQuietAlong hpsi h2 ring C word →
      EnvAll (fun q : Phys psi kappa tau => q)
        X ComparisonCleanCell C →
      R1ExpiryCutSafeAlong
        (kappa := kappa) (tau := tau) hpsi h2 ring C word := by
  induction word with
  | nil =>
      intro C _ _ _ _
      trivial
  | cons e word ih =>
      intro C hInt hAlive hPre hClean
      have he : internal X.env.I e := hInt e (by simp)
      have hInside := (B6LocalReverseFill.internal_iff X.env.I e).mp he
      have hL : AuthQuiet (C e).core.erase :=
        (comparisonClean_iff_authQuiet (C e)).1 (hClean e hInside.1)
      have hR : AuthQuiet (C (ring.rightNeighbor e)).core.erase :=
        (comparisonClean_iff_authQuiet (C (ring.rightNeighbor e))).1
          (hClean (ring.rightNeighbor e) hInside.2)
      have hLeaderless :
          HostLeaderless (fun q : Phys psi kappa tau => q) C := by
        change BirthShortDoneTerminalFirstHit.Leaderless C
        exact hAlive.1
      have hq :
          AuthQuiet
              (checkInput hpsi h2 (C e) (C (ring.rightNeighbor e))).1 ∧
            AuthQuiet
              (checkInput hpsi h2 (C e) (C (ring.rightNeighbor e))).2 := by
        have hs := hPre [] word e (by simp)
        simpa [runHost] using hs hLeaderless
      have hCut : R1ExpiryCutSafeAt hpsi h2 ring C e := by
        change R1ExpiryCutQuiet hpsi h2
          (C e) (C (ring.rightNeighbor e))
        exact r1ExpiryCutQuiet_of_quiet_inputs
          hpsi h2 (C e) (C (ring.rightNeighbor e)) hL hR hq
      let D := B9Host.hostStep
        (B9Host.r1Host (kappa := kappa) (tau := tau) hpsi h2)
        ring C e
      have hCleanD :
          EnvAll (fun q : Phys psi kappa tau => q)
            X ComparisonCleanCell D :=
        r1_internal_step_env_comparisonClean_frame
          (ring := ring) (kappa := kappa) (tau := tau)
          hpsi h2 X C e hLeaderless hClean he hCut
      have hIntD : InternalWord X.env.I word := by
        intro f hf
        exact hInt f (List.mem_cons_of_mem e hf)
      have hAliveD :
          B6WriterSilentGuarded.LeaderlessAlong hpsi h2 ring D word := by
        dsimp only [D]
        rw [B9Host.hostStep_r1_eq_step1
          (kappa := kappa) (tau := tau) hpsi h2 ring C e]
        exact hAlive.2
      have hPreD : R1PreCheckQuietAlong hpsi h2 ring D word := by
        intro u v f hdecomp
        have hword : e :: word = (e :: u) ++ (f :: v) := by
          simp [hdecomp]
        have hs := hPre (e :: u) v f hword
        have hRun :
            runHost
                (B9Host.r1Host
                  (kappa := kappa) (tau := tau) hpsi h2)
                ring (e :: u) C =
              runHost
                (B9Host.r1Host
                  (kappa := kappa) (tau := tau) hpsi h2)
                ring u D := by
          simp [runHost, D]
        rw [hRun] at hs
        simpa only using hs
      exact ⟨hCut, ih D hIntD hAliveD hPreD hCleanD⟩


/-- K2 source-to-cut lift.  The extra hypothesis is precisely the first
unclosed obligation above; it is the already-existing drain-leaderless side
condition, not a new state invariant. -/
theorem r1ExpiryCutSafeAlong_of_k2_source
    (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (WP : WriterProtected ring psi (Phys psi kappa tau))
    (X : Workspace ring psi)
    (E : PConfig n (Phys psi kappa tau))
    (hExpiry :
      ExpiryAtEnv (fun q : Phys psi kappa tau => q) WP X E)
    (hStable :
      R1DrainStableForK2 hpsi h2
        (B9Host.r1Host (kappa := kappa) (tau := tau) hpsi h2)
        (fun q : Phys psi kappa tau => q) ring X E)
    (hResidual :
      R1ExpiryCutSafeAlongLeaderlessResidual hpsi h2 ring X E) :
    R1ExpiryCutSafeAlong
      (kappa := kappa) (tau := tau)
      hpsi h2 ring E (k2DrainWord ring X) := by
  have hPre := r1PreCheckQuietAlong_of_drainStable
    (kappa := kappa) (tau := tau) hpsi h2 ring X E hStable
  change B6WriterSilentGuarded.LeaderlessAlong
    hpsi h2 ring E (k2DrainWord ring X) at hResidual
  exact r1ExpiryCutSafeAlong_of_clean_precheck
    (ring := ring) (kappa := kappa) (tau := tau)
    hpsi h2 X (k2DrainWord ring X) E
    (B6EntranceV2K2.k2DrainWord_internal ring X)
    hResidual hPre hExpiry.2


end B6EntranceExpiryWord

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


/-- `R1ExpiryCutSafeAlong` is discharged from the produced K2 source.
`hDrainLeaderless` remains: it is exactly the residual identified in Part 1
and is not a consequence of `ExpiryAtEnv` or `EntranceHostLawsV3b`. -/
theorem k2_chain_of_lawsV3b_of_resetEchoClear_no_expiryCut
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
    (hC : HostLeaderless (fun q : Phys psi psi (16 * psi) => q) C)
    (hWriter : WriterAt WP X C)
    (hClear : FinalResetEchoClear B4C)
    (hDrainLeaderless :
      ∀ D : PConfig n (Phys psi psi (16 * psi)),
        TrafficAtEnv (fun q : Phys psi psi (16 * psi) => q) WP X D →
        B6WriterSilentGuarded.LeaderlessAlong hpsi h2 ring D
          (k2DrainWord ring X)) :
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
  apply B6EntranceK2ChainCollar.k2_chain_of_lawsV3b_of_resetEchoClear
    (ring := ring) hpsi h2 WP b hlaws X C B4C hBase
    hC hWriter hClear hDrainLeaderless
  intro E hSource
  have hResidual :
      B6EntranceExpiryWord.R1ExpiryCutSafeAlongLeaderlessResidual
        hpsi h2 ring X E := by
    simpa [B6EntranceExpiryWord.R1ExpiryCutSafeAlongLeaderlessResidual] using
      (hDrainLeaderless E hSource.1.1)
  exact B6EntranceExpiryWord.r1ExpiryCutSafeAlong_of_k2_source
    (ring := ring) (kappa := psi) (tau := 16 * psi)
    hpsi h2 WP X E hSource.1 hSource.2 hResidual


end B6EntranceK2ChainCollar
