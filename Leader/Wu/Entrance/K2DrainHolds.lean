import Leader.Wu.Entrance.K2DrainContract
import Leader.Wu.Entrance.K2ReverseWord
import Leader.Wu.Entrance.ExpiryCutSafeAlong

set_option autoImplicit false
set_option Elab.async false

namespace B6EntranceLaw2Leaderless

open B6LocalReverseFill
open B6EntranceV2 B6EntranceV2K2 B6EntranceV3
open B6EntranceLargeRingPackage

variable {n psi : Nat}

private theorem leaderlessAlong_runHost
    (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (ring : DirectedRing n)
    (C : PConfig n (Phys psi psi (16 * psi)))
    (w : List (Fin n))
    (h : B6WriterSilentGuarded.LeaderlessAlong
      hpsi h2 ring C w) :
    HostLeaderless (fun q : Phys psi psi (16 * psi) => q)
      (runHost
        (B9Host.r1Host
          (kappa := psi) (tau := 16 * psi) hpsi h2)
        ring w C) := by
  induction w generalizing C with
  | nil =>
      change BirthShortDoneTerminalFirstHit.Leaderless C
      exact h
  | cons e w ih =>
      have ht := h.2
      rw [← B9Host.hostStep_r1_eq_step1
        (kappa := psi) (tau := 16 * psi)
        hpsi h2 ring C e] at ht
      have hfin := ih
        (B9Host.hostStep
          (B9Host.r1Host
            (kappa := psi) (tau := 16 * psi) hpsi h2)
          ring C e) ht
      simpa [runHost] using hfin

private theorem leaderlessAlong_or_nonleaderless_prefix
    (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (ring : DirectedRing n) (I : Interval ring)
    (w : List (Fin n)) :
    ∀ C : PConfig n (Phys psi psi (16 * psi)),
      InternalWord I w →
      HostLeaderless (fun q : Phys psi psi (16 * psi) => q) C →
      B6WriterSilentGuarded.LeaderlessAlong hpsi h2 ring C w ∨
        ∃ p : List (Fin n),
          InternalWord I p ∧ p.length ≤ w.length ∧
          ¬ HostLeaderless (fun q : Phys psi psi (16 * psi) => q)
            (runHost
              (B9Host.r1Host
                (kappa := psi) (tau := 16 * psi) hpsi h2)
              ring p C) := by
  induction w with
  | nil =>
      intro C _ hC
      left
      change BirthShortDoneTerminalFirstHit.Leaderless C
      exact hC
  | cons e w ih =>
      intro C hInt hC
      have he : internal I e := hInt e (by simp)
      have hTailInt : InternalWord I w := by
        intro f hf
        exact hInt f (List.mem_cons_of_mem e hf)
      let D := B9Host.hostStep
        (B9Host.r1Host
          (kappa := psi) (tau := 16 * psi) hpsi h2)
        ring C e
      by_cases hD :
          HostLeaderless (fun q : Phys psi psi (16 * psi) => q) D
      · rcases ih D hTailInt hD with hTail | ⟨p, hpI, hpL, hpN⟩
        · left
          have hTail' := hTail
          dsimp only [D] at hTail'
          rw [B9Host.hostStep_r1_eq_step1
            (kappa := psi) (tau := 16 * psi)
            hpsi h2 ring C e] at hTail'
          change BirthShortDoneTerminalFirstHit.Leaderless C ∧
            B6WriterSilentGuarded.LeaderlessAlong hpsi h2 ring
              (BirthCheckPermitRepairLeaf.step1 hpsi h2 ring C e) w
          exact ⟨hC, hTail'⟩
        · right
          refine ⟨e :: p, ?_, ?_, ?_⟩
          · intro f hf
            rcases List.mem_cons.mp hf with hfe | hfp
            · subst f
              exact he
            · exact hpI f hfp
          · simp only [List.length_cons]
            omega
          · simpa [runHost, D] using hpN
      · right
        refine ⟨[e], ?_, ?_, ?_⟩
        · intro f hf
          simp only [List.mem_singleton] at hf
          subst f
          exact he
        · simp
        · simpa [runHost, D] using hD

private theorem fixedWordTarget_of_leaderlessAlong
    (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (ring : DirectedRing n)
    (X : Workspace ring psi)
    (C : PConfig n (Phys psi psi (16 * psi)))
    (hSource :
      ExpiryAtEnv (fun q : Phys psi psi (16 * psi) => q)
          (B6EntranceLawsWiring2.WPfinal (psi := psi) ring) X C ∧
        R1DrainStableForK2 hpsi h2
          (B9Host.r1Host
            (kappa := psi) (tau := 16 * psi) hpsi h2)
          (fun q : Phys psi psi (16 * psi) => q) ring X C)
    (hAlive :
      B6WriterSilentGuarded.LeaderlessAlong
        hpsi h2 ring C (k2DrainWord ring X)) :
    K2DrainedAt (fun q : Phys psi psi (16 * psi) => q)
      (B6EntranceLawsWiring2.WPfinal (psi := psi) ring) X
      (runHost
        (B9Host.r1Host
          (kappa := psi) (tau := 16 * psi) hpsi h2)
        ring (k2DrainWord ring X) C) := by
  have hSafe :
      B6EntranceExpiryWord.R1ExpiryCutSafeAlong
        (kappa := psi) (tau := 16 * psi)
        hpsi h2 ring C (k2DrainWord ring X) := by
    exact B6EntranceExpiryWord.r1ExpiryCutSafeAlong_of_k2_source
      (ring := ring) (kappa := psi) (tau := 16 * psi)
      hpsi h2
      (B6EntranceLawsWiring2.WPfinal (psi := psi) ring)
      X C hSource.1 hSource.2
      (by
        change B6WriterSilentGuarded.LeaderlessAlong
          hpsi h2 ring C (k2DrainWord ring X)
        exact hAlive)
  have hBit :
      HostCoreBitSilence
        (B9Host.r1Host
          (kappa := psi) (tau := 16 * psi) hpsi h2)
        (fun q : Phys psi psi (16 * psi) => q) ring
        (B6EntranceLawsWiring2.WPfinal (psi := psi) ring) := by
    simpa [B6EntranceLawsCensus.BitSilenceProducer] using
      (B6EntranceLawsWiring2.bitSilenceProducer_WPfinal
        hpsi h2 ring)
  have hExpiryEnvEnd :
      ExpiryAtEnv (fun q : Phys psi psi (16 * psi) => q)
        (B6EntranceLawsWiring2.WPfinal (psi := psi) ring) X
        (runHost
          (B9Host.r1Host
            (kappa := psi) (tau := 16 * psi) hpsi h2)
          ring (k2DrainWord ring X) C) :=
    B6EntranceExpiryWord.r1_internal_word_expiryAtEnv_frame
      (ring := ring) (kappa := psi) (tau := 16 * psi)
      hpsi h2
      (B6EntranceLawsWiring2.WPfinal (psi := psi) ring)
      hBit X (k2DrainWord ring X) C
      (B6EntranceV2K2.k2DrainWord_internal ring X)
      hAlive hSafe hSource.1
  have hExpiryEnd :
      ExpiryAt (fun q : Phys psi psi (16 * psi) => q)
        (B6EntranceLawsWiring2.WPfinal (psi := psi) ring) X
        (runHost
          (B9Host.r1Host
            (kappa := psi) (tau := 16 * psi) hpsi h2)
          ring (k2DrainWord ring X) C) :=
    B6EntranceV3.expiryAtEnv_to_expiryAt
      (fun q : Phys psi psi (16 * psi) => q)
      (B6EntranceLawsWiring2.WPfinal (psi := psi) ring)
      X _ hExpiryEnvEnd
  have hBullet :=
    B6EntranceK2FixedWord.k2FixedWordLeaderlessSuccessV31_holds
      hpsi h2 ring X C hAlive
  have hFinalLeaderless :=
    leaderlessAlong_runHost hpsi h2 ring C
      (k2DrainWord ring X) hAlive
  refine ⟨hExpiryEnd, ?_⟩
  intro i hi
  unfold B6EntranceV2K2.K2DrainedCell
  exact ⟨hFinalLeaderless i, hBullet i hi⟩

/-- C4 law 2 needs no additional no-birth or leaderless-along residual.
If the fixed drain ceases to be leaderless, the shorter prefix is already a
valid HostExit; otherwise the full reverse word reaches K2DrainedAt. -/
theorem k2DrainWithinEnvelopeSweep_holds
    (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (ring : DirectedRing n)
    (hdom : LargeRingDomain psi n) :
    K2DrainWithinEnvelopeSweep hpsi h2 ring hdom := by
  unfold K2DrainWithinEnvelopeSweep
  unfold B6EntranceV3.HostK2ClearableOrLeaderV3
  unfold B6EntranceV2.HostStageWord
  intro X C hC hSource
  have hInt : InternalWord X.env.I (k2DrainWord ring X) :=
    B6EntranceV2K2.k2DrainWord_internal ring X
  rcases leaderlessAlong_or_nonleaderless_prefix
      hpsi h2 ring X.env.I (k2DrainWord ring X) C hInt hC with
    hAlive | ⟨p, hpI, hpL, hpN⟩
  · refine ⟨k2DrainWord ring X, hInt, ?_, ?_⟩
    · exact Nat.le_of_eq (B6EntranceV2K2.k2DrainWord_length ring X)
    · exact Or.inl
        (fixedWordTarget_of_leaderlessAlong
          hpsi h2 ring X C hSource hAlive)
  · refine ⟨p, hpI, ?_, ?_⟩
    · calc
        p.length ≤ (k2DrainWord ring X).length := hpL
        _ = k2DrainLength psi :=
          B6EntranceV2K2.k2DrainWord_length ring X
    · exact Or.inr (Or.inr hpN)

end B6EntranceLaw2Leaderless
