import Leader.Wu.Entrance.EnvelopeResetEchoWord

set_option autoImplicit false
set_option Elab.async false

namespace B6EntranceExpiryWord

open PPLL PPLLResearchFormulation PPLLExpiringComparisonRepair
open B6LocalReverseFill
open B6EntranceV2 B6EntranceV2K2 B6EntranceV3

variable {n psi kappa tau : Nat}
variable {ring : DirectedRing n}

theorem comparisonClean_iff_authQuiet
    (q : Phys psi kappa tau) :
    ComparisonCleanCell q ↔
      R1CandidateKernel.AuthQuiet q.core.erase := by
  unfold ComparisonCleanCell R1CandidateKernel.AuthQuiet
    R1CandidateKernel.RawQuiet B6Sanitation.rawCell
  constructor
  · rintro ⟨hstate, hpath, hpath2, hpath4, hpath5, hp, hpcarry, hpermit⟩
    exact ⟨⟨hstate, hpath, hpath2, hpath4, hpath5, hp, hpcarry⟩, hpermit⟩
  · rintro ⟨⟨hstate, hpath, hpath2, hpath4, hpath5, hp, hpcarry⟩, hpermit⟩
    exact ⟨hstate, hpath, hpath2, hpath4, hpath5, hp, hpcarry, hpermit⟩

/-- Exact missing local currency.  This is the final conjunct of
`R1CandidateKernel.EdgeSafe`, isolated from the unrelated ruler, CHECK-result,
writer-bit, and writer-dormancy clauses. -/
def R1ExpiryCutQuiet
    (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (l r : Phys psi kappa tau) : Prop :=
  let q := BirthCheckPermitRepair.expiring
    hpsi (by decide : 0 < 2) h2 l r
  R1CandidateKernel.AuthQuiet q.1.core.erase ∧
    R1CandidateKernel.AuthQuiet q.2.core.erase

/-- Configuration-level form for one scheduled edge. -/
def R1ExpiryCutSafeAt
    (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (ring : DirectedRing n)
    (C : PConfig n (Phys psi kappa tau)) (e : Fin n) : Prop :=
  R1ExpiryCutQuiet hpsi h2 (C e) (C (ring.rightNeighbor e))

private theorem authQuiet_normalizeLeader
    (hpsi : 0 < psi) (u : Phys psi kappa tau)
    (hu : R1CandidateKernel.AuthQuiet u.core.erase) :
    R1CandidateKernel.AuthQuiet
      (K2BirthLeaderNormalize.normalizeLeader hpsi u).core.erase := by
  unfold K2BirthLeaderNormalize.normalizeLeader
  split <;> exact hu

private theorem authQuiet_of_putSignals_restore
    (u v : Phys psi kappa tau)
    (he : ExpiringK2Projection.putSignals u
      (ExpiringK2Projection.observeCell v) = v)
    (hv : R1CandidateKernel.AuthQuiet v.core.erase) :
    R1CandidateKernel.AuthQuiet u.core.erase := by
  have h := congrArg
    (fun z : Phys psi kappa tau =>
      R1CandidateKernel.AuthQuiet z.core.erase) he
  change R1CandidateKernel.AuthQuiet u.core.erase =
    R1CandidateKernel.AuthQuiet v.core.erase at h
  exact Eq.mpr h hv

/-- The only nontrivial row fact needed below: quiet metadata at the actual
expiry cut survives leader normalization and the final K2/collision tail. -/
private theorem r1_pair_comparisonClean_of_expiryCutQuiet
    (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (l r : Phys psi kappa tau)
    (hCut : R1ExpiryCutQuiet hpsi h2 l r) :
    ComparisonCleanCell
        (BirthCheckPermitRepair.row
          hpsi (by decide : 0 < 2) h2 l r).1 ∧
      ComparisonCleanCell
        (BirthCheckPermitRepair.row
          hpsi (by decide : 0 < 2) h2 l r).2 := by
  change
    R1CandidateKernel.AuthQuiet
        (BirthCheckPermitRepair.expiring
          hpsi (by decide : 0 < 2) h2 l r).1.core.erase ∧
      R1CandidateKernel.AuthQuiet
        (BirthCheckPermitRepair.expiring
          hpsi (by decide : 0 < 2) h2 l r).2.core.erase at hCut
  let q := BirthCheckPermitRepair.expiring
    hpsi (by decide : 0 < 2) h2 l r
  let a := K2BirthLeaderNormalize.normalizeLeader hpsi q.1
  let b := K2BirthLeaderNormalize.normalizeLeader hpsi q.2
  have ha : R1CandidateKernel.AuthQuiet a.core.erase :=
    authQuiet_normalizeLeader hpsi q.1 hCut.1
  have hb : R1CandidateKernel.AuthQuiet b.core.erase :=
    authQuiet_normalizeLeader hpsi q.2 hCut.2
  have hf := K2BirthDispatcher.finalPhysical_frame hpsi l r a b
  have ht :
      R1CandidateKernel.AuthQuiet
          (K2BirthDispatcher.finalPhysical hpsi l r a b).1.core.erase ∧
        R1CandidateKernel.AuthQuiet
          (K2BirthDispatcher.finalPhysical hpsi l r a b).2.core.erase :=
    ⟨authQuiet_of_putSignals_restore _ _ hf.1 ha,
      authQuiet_of_putSignals_restore _ _ hf.2 hb⟩
  have he :
      BirthCheckPermitRepair.row
          hpsi (by decide : 0 < 2) h2 l r =
        K2BirthDispatcher.finalPhysical hpsi l r a b := rfl
  have hout :
      R1CandidateKernel.AuthQuiet
          (BirthCheckPermitRepair.row
            hpsi (by decide : 0 < 2) h2 l r).1.core.erase ∧
        R1CandidateKernel.AuthQuiet
          (BirthCheckPermitRepair.row
            hpsi (by decide : 0 < 2) h2 l r).2.core.erase :=
    Eq.mpr
      (congrArg
        (fun z : Phys psi kappa tau × Phys psi kappa tau =>
          R1CandidateKernel.AuthQuiet z.1.core.erase ∧
            R1CandidateKernel.AuthQuiet z.2.core.erase)
        he) ht
  exact ⟨(comparisonClean_iff_authQuiet _).2 hout.1,
    (comparisonClean_iff_authQuiet _).2 hout.2⟩

/-- Conditional one-letter frame.  The unconditional version is refuted by
`B6K2WaitSeeds.localWaitDormant_not_enough`; `hCut` is the exact missing
post-prefix cut fact rather than a guessed WAIT predicate. -/
theorem r1_internal_step_env_comparisonClean_frame
    (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (X : Workspace ring psi)
    (C : PConfig n (Phys psi kappa tau)) (e : Fin n)
    (_hLeaderless :
      HostLeaderless (fun q : Phys psi kappa tau => q) C)
    (hClean :
      EnvAll (fun q : Phys psi kappa tau => q)
        X ComparisonCleanCell C)
    (he : internal X.env.I e)
    (hCut : R1ExpiryCutSafeAt hpsi h2 ring C e) :
    EnvAll (fun q : Phys psi kappa tau => q)
      X ComparisonCleanCell
      (B9Host.hostStep
        (B9Host.r1Host (kappa := kappa) (tau := tau) hpsi h2)
        ring C e) := by
  unfold EnvAll at hClean ⊢
  have hInside := (B6LocalReverseFill.internal_iff X.env.I e).mp he
  have _hLeftClean : ComparisonCleanCell (C e) :=
    hClean e hInside.1
  have _hRightClean : ComparisonCleanCell (C (ring.rightNeighbor e)) :=
    hClean (ring.rightNeighbor e) hInside.2
  have hPair0 := r1_pair_comparisonClean_of_expiryCutQuiet
    (kappa := kappa) (tau := tau) hpsi h2
    (C e) (C (ring.rightNeighbor e)) hCut
  have hPair :
      ComparisonCleanCell
          ((B9Host.r1Host
            (kappa := kappa) (tau := tau) hpsi h2).row
            (C e) (C (ring.rightNeighbor e))).1 ∧
        ComparisonCleanCell
          ((B9Host.r1Host
            (kappa := kappa) (tau := tau) hpsi h2).row
            (C e) (C (ring.rightNeighbor e))).2 := by
    exact hPair0
  intro i hi
  by_cases hie : i = e
  · subst i
    simpa only [B9Host.hostStep, if_pos] using hPair.1
  · by_cases hir : i = ring.rightNeighbor e
    · subst i
      simpa only [B9Host.hostStep, if_neg hie, if_pos] using hPair.2
    · simpa only [B9Host.hostStep, if_neg hie, if_neg hir] using
        hClean i hi

/-- Prefix-by-prefix version of the exact expiry-cut premise. -/
def R1ExpiryCutSafeAlong
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) (ring : DirectedRing n) :
    PConfig n (Phys psi kappa tau) → List (Fin n) → Prop
  | _, [] => True
  | C, e :: w =>
      R1ExpiryCutSafeAt hpsi h2 ring C e ∧
        R1ExpiryCutSafeAlong hpsi h2 ring
          (B9Host.hostStep
            (B9Host.r1Host
              (kappa := kappa) (tau := tau) hpsi h2)
            ring C e) w

private theorem leaderlessAlong_head
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) (ring : DirectedRing n)
    (C : PConfig n (Phys psi kappa tau)) (w : List (Fin n))
    (h : B6WriterSilentGuarded.LeaderlessAlong hpsi h2 ring C w) :
    HostLeaderless (fun q : Phys psi kappa tau => q) C := by
  change BirthShortDoneTerminalFirstHit.Leaderless C
  cases w with
  | nil => exact h
  | cons e w => exact h.1

private theorem leaderlessAlong_tail
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) (ring : DirectedRing n)
    (C : PConfig n (Phys psi kappa tau))
    (e : Fin n) (w : List (Fin n))
    (h : B6WriterSilentGuarded.LeaderlessAlong
      hpsi h2 ring C (e :: w)) :
    B6WriterSilentGuarded.LeaderlessAlong hpsi h2 ring
      (B9Host.hostStep
        (B9Host.r1Host (kappa := kappa) (tau := tau) hpsi h2)
        ring C e) w := by
  rw [B9Host.hostStep_r1_eq_step1
    (kappa := kappa) (tau := tau) hpsi h2 ring C e]
  exact h.2

/-- Word lift, exactly parallel to
`B6EntranceEnvelopeWord.r1_internal_word_env_resetEcho_frame`, with the one
extra prefix currency made explicit. -/
theorem r1_internal_word_env_comparisonClean_frame
    (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (X : Workspace ring psi) (w : List (Fin n)) :
    ∀ C : PConfig n (Phys psi kappa tau),
      InternalWord X.env.I w →
      B6WriterSilentGuarded.LeaderlessAlong hpsi h2 ring C w →
      R1ExpiryCutSafeAlong
        (kappa := kappa) (tau := tau) hpsi h2 ring C w →
      EnvAll (fun q : Phys psi kappa tau => q)
        X ComparisonCleanCell C →
      EnvAll (fun q : Phys psi kappa tau => q)
        X ComparisonCleanCell
        (runHost
          (B9Host.r1Host (kappa := kappa) (tau := tau) hpsi h2)
          ring w C) := by
  induction w with
  | nil =>
      intro C _ _ _ hClean
      change EnvAll (fun q : Phys psi kappa tau => q)
        X ComparisonCleanCell C
      exact hClean
  | cons e w ih =>
      intro C hInt hAlive hSafe hClean
      have he : internal X.env.I e := hInt e (by simp)
      have hTailInt : InternalWord X.env.I w := by
        intro f hf
        exact hInt f (List.mem_cons_of_mem e hf)
      have hLeaderless :
          HostLeaderless (fun q : Phys psi kappa tau => q) C :=
        leaderlessAlong_head hpsi h2 ring C (e :: w) hAlive
      let D := B9Host.hostStep
        (B9Host.r1Host (kappa := kappa) (tau := tau) hpsi h2)
        ring C e
      have hAliveD :
          B6WriterSilentGuarded.LeaderlessAlong hpsi h2 ring D w :=
        leaderlessAlong_tail hpsi h2 ring C e w hAlive
      have hSafeHead : R1ExpiryCutSafeAt hpsi h2 ring C e :=
        hSafe.1
      have hSafeTail :
          R1ExpiryCutSafeAlong
            (kappa := kappa) (tau := tau) hpsi h2 ring D w :=
        hSafe.2
      have hCleanD :
          EnvAll (fun q : Phys psi kappa tau => q)
            X ComparisonCleanCell D :=
        r1_internal_step_env_comparisonClean_frame
          (ring := ring) (kappa := kappa) (tau := tau)
          hpsi h2 X C e hLeaderless hClean he hSafeHead
      have hTail := ih D hTailInt hAliveD hSafeTail hCleanD
      change EnvAll (fun q : Phys psi kappa tau => q)
        X ComparisonCleanCell
        (runHost
          (B9Host.r1Host (kappa := kappa) (tau := tau) hpsi h2)
          ring w D)
      exact hTail

/-- Combine the already-proved TrafficAtEnv word frame with the conditional
comparison-clean word frame. -/
theorem r1_internal_word_expiryAtEnv_frame
    (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (WP : WriterProtected ring psi (Phys psi kappa tau))
    (hBit :
      HostCoreBitSilence
        (B9Host.r1Host (kappa := kappa) (tau := tau) hpsi h2)
        (fun q : Phys psi kappa tau => q) ring WP)
    (X : Workspace ring psi) (w : List (Fin n)) :
    ∀ C : PConfig n (Phys psi kappa tau),
      InternalWord X.env.I w →
      B6WriterSilentGuarded.LeaderlessAlong hpsi h2 ring C w →
      R1ExpiryCutSafeAlong
        (kappa := kappa) (tau := tau) hpsi h2 ring C w →
      ExpiryAtEnv (fun q : Phys psi kappa tau => q) WP X C →
      ExpiryAtEnv (fun q : Phys psi kappa tau => q) WP X
        (runHost
          (B9Host.r1Host (kappa := kappa) (tau := tau) hpsi h2)
          ring w C) := by
  intro C hInt hAlive hSafe hExpiry
  refine ⟨?_, ?_⟩
  · exact B6EntranceEnvelopeWord.r1_internal_word_trafficAtEnv_frame
      (ring := ring) (kappa := kappa) (tau := tau)
      hpsi h2 WP hBit X w C hInt hAlive hExpiry.1
  · exact r1_internal_word_env_comparisonClean_frame
      (ring := ring) (kappa := kappa) (tau := tau)
      hpsi h2 X w C hInt hAlive hSafe hExpiry.2

/-- Host-law packaging of the preceding theorem. -/
theorem r1_internal_word_expiryAtEnv_of_laws
    (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (WP : WriterProtected ring psi (Phys psi kappa tau))
    (b : EntranceBudgets)
    (hlaws :
      EntranceHostLawsV3 hpsi h2
        (B9Host.r1Host (kappa := kappa) (tau := tau) hpsi h2)
        (fun q : Phys psi kappa tau => q) ring WP b)
    (X : Workspace ring psi) (w : List (Fin n))
    (C : PConfig n (Phys psi kappa tau))
    (hInt : InternalWord X.env.I w)
    (hAlive :
      B6WriterSilentGuarded.LeaderlessAlong hpsi h2 ring C w)
    (hSafe :
      R1ExpiryCutSafeAlong
        (kappa := kappa) (tau := tau) hpsi h2 ring C w)
    (hExpiry :
      ExpiryAtEnv (fun q : Phys psi kappa tau => q) WP X C) :
    ExpiryAtEnv (fun q : Phys psi kappa tau => q) WP X
      (runHost
        (B9Host.r1Host (kappa := kappa) (tau := tau) hpsi h2)
        ring w C) := by
  exact r1_internal_word_expiryAtEnv_frame
    (ring := ring) (kappa := kappa) (tau := tau)
    hpsi h2 WP hlaws.bitSilence X w C hInt hAlive hSafe hExpiry

/-- K2-word specialization.  The existing V3 source still supplies
`R1DrainStableForK2`; the genuinely additional requirement is only
`R1ExpiryCutSafeAlong`, because the former stops at CHECK/writer input. -/
theorem r1_k2DrainWord_expiryAtEnv_of_k2_source
    (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (WP : WriterProtected ring psi (Phys psi kappa tau))
    (b : EntranceBudgets)
    (hlaws :
      EntranceHostLawsV3 hpsi h2
        (B9Host.r1Host (kappa := kappa) (tau := tau) hpsi h2)
        (fun q : Phys psi kappa tau => q) ring WP b)
    (X : Workspace ring psi)
    (C : PConfig n (Phys psi kappa tau))
    (hAlive :
      B6WriterSilentGuarded.LeaderlessAlong hpsi h2 ring C
        (k2DrainWord ring X))
    (hSource :
      ExpiryAtEnv (fun q : Phys psi kappa tau => q) WP X C ∧
        R1DrainStableForK2 hpsi h2
          (B9Host.r1Host (kappa := kappa) (tau := tau) hpsi h2)
          (fun q : Phys psi kappa tau => q) ring X C)
    (hSafe :
      R1ExpiryCutSafeAlong
        (kappa := kappa) (tau := tau) hpsi h2 ring C
        (k2DrainWord ring X)) :
    ExpiryAtEnv (fun q : Phys psi kappa tau => q) WP X
      (runHost
        (B9Host.r1Host (kappa := kappa) (tau := tau) hpsi h2)
        ring (k2DrainWord ring X) C) := by
  exact r1_internal_word_expiryAtEnv_of_laws
    (ring := ring) (kappa := kappa) (tau := tau)
    hpsi h2 WP b hlaws X (k2DrainWord ring X) C
    (B6EntranceV2K2.k2DrainWord_internal ring X)
    hAlive hSafe hSource.1

end B6EntranceExpiryWord
