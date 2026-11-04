import Leader.Wu.Entrance.EnvelopeResetEchoFrame

set_option autoImplicit false
set_option Elab.async false

namespace B6EntranceEnvelopeWord

open PPLL PPLLResearchFormulation PPLLExpiringComparisonRepair
open B6LocalReverseFill
open B6EntranceV2 B6EntranceV2K2 B6EntranceV3
open B6EntranceEnvelopeFrame

variable {n psi kappa tau : Nat}
variable {ring : DirectedRing n}

/-!
The prefix side condition is the existing R1 predicate
`B6WriterSilentGuarded.LeaderlessAlong`
(`Leader/Wu/Entrance/WriterSilentGuarded.lean:684-689`).  It is stated using R1 `step1`;
`B9Host.hostStep_r1_eq_step1` (`Leader/Wu/Splice/HostRow.lean:324-329`) identifies it
with the host fold used below.
-/

private theorem r1_leaderlessAlong_head
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) (ring : DirectedRing n)
    (C : PConfig n (Phys psi kappa tau)) (w : List (Fin n))
    (h : B6WriterSilentGuarded.LeaderlessAlong hpsi h2 ring C w) :
    HostLeaderless (fun q : Phys psi kappa tau => q) C := by
  change BirthShortDoneTerminalFirstHit.Leaderless C
  cases w with
  | nil => exact h
  | cons e w => exact h.1

private theorem r1_leaderlessAlong_tail
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

/-- Whole-envelope reset/echo clearance is invariant under any internal R1
word as long as every prefix remains leaderless. -/
theorem r1_internal_word_env_resetEcho_frame
    (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (X : Workspace ring psi) (w : List (Fin n)) :
    ∀ C : PConfig n (Phys psi kappa tau),
      InternalWord X.env.I w →
      B6WriterSilentGuarded.LeaderlessAlong hpsi h2 ring C w →
      EnvAll (fun q : Phys psi kappa tau => q)
        X ResetEchoClearCell C →
      EnvAll (fun q : Phys psi kappa tau => q)
        X ResetEchoClearCell
        (runHost
          (B9Host.r1Host (kappa := kappa) (tau := tau) hpsi h2)
          ring w C) := by
  induction w with
  | nil =>
      intro C _ _ hClear
      change EnvAll (fun q : Phys psi kappa tau => q)
        X ResetEchoClearCell C
      exact hClear
  | cons e w ih =>
      intro C hInt hAlive hClear
      have he : internal X.env.I e := hInt e (by simp)
      have hTailInt : InternalWord X.env.I w := by
        intro f hf
        exact hInt f (List.mem_cons_of_mem e hf)
      have hLeaderless :
          HostLeaderless (fun q : Phys psi kappa tau => q) C :=
        r1_leaderlessAlong_head hpsi h2 ring C (e :: w) hAlive
      let D := B9Host.hostStep
        (B9Host.r1Host (kappa := kappa) (tau := tau) hpsi h2)
        ring C e
      have hAliveD :
          B6WriterSilentGuarded.LeaderlessAlong hpsi h2 ring D w :=
        r1_leaderlessAlong_tail hpsi h2 ring C e w hAlive
      have hClearD :
          EnvAll (fun q : Phys psi kappa tau => q)
            X ResetEchoClearCell D :=
        B6EntranceEnvelopeFrame.r1_internal_step_env_resetEcho_frame
          (ring := ring) (kappa := kappa) (tau := tau)
          hpsi h2 X C e hLeaderless hClear he
      have hTail := ih D hTailInt hAliveD hClearD
      change EnvAll (fun q : Phys psi kappa tau => q)
        X ResetEchoClearCell
        (runHost
          (B9Host.r1Host (kappa := kappa) (tau := tau) hpsi h2)
          ring w D)
      exact hTail

section Admission

variable {P : Type}

/-!
Admission audit:

* `WriterProtected` is arbitrary (`Leader/Wu/Entrance/EnvelopeInterface.lean:89-90`).
* `HostWriterAdmission` targets only `WriterAt` on its successful branch
  (`Leader/Wu/Entrance/EnvelopeInterface.lean:249-254`).
* `EntranceHostLawsV3.writerAdmission` reuses that law unchanged
  (`Leader/Wu/Entrance/EnvelopeHostLaws.lean:108-128`).

So the current API has no theorem from writer admission to collar reset/echo
clearance.  This is the exact stage-level strengthening needed if admission is
to establish that boundary fact: only the successful target branch is
strengthened; hit/birth exits remain unchanged.
-/
def HostWriterAdmissionBoundaryResetEchoClear
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

/-- The named open admission fact is genuinely a strengthening of the current
writer-admission law, not a replacement with different exit semantics. -/
theorem writerAdmission_of_boundary_admission
    (host : B9Host.HostRow P) (view : P → Phys psi kappa tau)
    (ring : DirectedRing n) (WP : WriterProtected ring psi P)
    (L : Nat)
    (h : HostWriterAdmissionBoundaryResetEchoClear
      host view ring WP L) :
    HostWriterAdmission host view ring WP L := by
  intro C hC
  obtain ⟨X, w, hInt, hLen, hExit⟩ := h C hC
  refine ⟨X, w, hInt, hLen, ?_⟩
  rcases hExit with hTarget | hRest
  · exact Or.inl hTarget.1
  · exact Or.inr hRest

end Admission

/-- `WriterAt` has the same word-level frame once the existing
`HostCoreBitSilence` one-letter law is supplied.  The one-letter law already
returns `WriterAt` on a leaderless internal service
(`Leader/Wu/Entrance/EnvelopeInterface.lean:207-212`). -/
theorem r1_internal_word_writerAt_frame
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
      WriterAt WP X C →
      WriterAt WP X
        (runHost
          (B9Host.r1Host (kappa := kappa) (tau := tau) hpsi h2)
          ring w C) := by
  induction w with
  | nil =>
      intro C _ _ hWriter
      change WriterAt WP X C
      exact hWriter
  | cons e w ih =>
      intro C hInt hAlive hWriter
      have he : internal X.env.I e := hInt e (by simp)
      have hTailInt : InternalWord X.env.I w := by
        intro f hf
        exact hInt f (List.mem_cons_of_mem e hf)
      have hLeaderless :
          HostLeaderless (fun q : Phys psi kappa tau => q) C :=
        r1_leaderlessAlong_head hpsi h2 ring C (e :: w) hAlive
      let D := B9Host.hostStep
        (B9Host.r1Host (kappa := kappa) (tau := tau) hpsi h2)
        ring C e
      have hAliveD :
          B6WriterSilentGuarded.LeaderlessAlong hpsi h2 ring D w :=
        r1_leaderlessAlong_tail hpsi h2 ring C e w hAlive
      have hLeaderlessD :
          HostLeaderless (fun q : Phys psi kappa tau => q) D :=
        r1_leaderlessAlong_head hpsi h2 ring D w hAliveD
      have hStep :=
        hBit X C e hWriter hLeaderless he hLeaderlessD
      have hWriterD : WriterAt WP X D := hStep.1
      have hTail := ih D hTailInt hAliveD hWriterD
      change WriterAt WP X
        (runHost
          (B9Host.r1Host (kappa := kappa) (tau := tau) hpsi h2)
          ring w D)
      exact hTail

/-- Therefore the whole `TrafficAtEnv` predicate is invariant under an
internal leaderless R1 word: reset/echo uses the physical frame, while writer
protection uses the already-existing `HostCoreBitSilence` writer component. -/
theorem r1_internal_word_trafficAtEnv_frame
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
      TrafficAtEnv (fun q : Phys psi kappa tau => q) WP X C →
      TrafficAtEnv (fun q : Phys psi kappa tau => q) WP X
        (runHost
          (B9Host.r1Host (kappa := kappa) (tau := tau) hpsi h2)
          ring w C) := by
  intro C hInt hAlive hTraffic
  refine ⟨?_, ?_⟩
  · exact r1_internal_word_writerAt_frame
      (ring := ring) (kappa := kappa) (tau := tau)
      hpsi h2 WP hBit X w C hInt hAlive hTraffic.1
  · exact r1_internal_word_env_resetEcho_frame
      (ring := ring) (kappa := kappa) (tau := tau)
      hpsi h2 X w C hInt hAlive hTraffic.2

/-- `EntranceHostLawsV3.bitSilence` is already the required writer frame;
`writerLocal` is not used for this preservation theorem. -/
theorem r1_internal_word_trafficAtEnv_of_laws
    (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (WP : WriterProtected ring psi (Phys psi kappa tau))
    (b : EntranceBudgets)
    (hlaws :
      EntranceHostLawsV3 hpsi h2
        (B9Host.r1Host (kappa := kappa) (tau := tau) hpsi h2)
        (fun q : Phys psi kappa tau => q) ring WP b)
    (X : Workspace ring psi) (w : List (Fin n)) :
    ∀ C : PConfig n (Phys psi kappa tau),
      InternalWord X.env.I w →
      B6WriterSilentGuarded.LeaderlessAlong hpsi h2 ring C w →
      TrafficAtEnv (fun q : Phys psi kappa tau => q) WP X C →
      TrafficAtEnv (fun q : Phys psi kappa tau => q) WP X
        (runHost
          (B9Host.r1Host (kappa := kappa) (tau := tau) hpsi h2)
          ring w C) := by
  intro C hInt hAlive hTraffic
  exact r1_internal_word_trafficAtEnv_frame
    (ring := ring) (kappa := kappa) (tau := tau)
    hpsi h2 WP hlaws.bitSilence X w C hInt hAlive hTraffic

/-- K2-stage specialization.  `k2DrainWord_internal` supplies internality.
The V3 K2 source carries `ExpiryAtEnv`, whose first component is the
`TrafficAtEnv` premise used here.  `R1DrainStableForK2` remains available for
the separate CHECK/writer-cut obligations; it is not needed for this
reset/echo preservation projection. -/
theorem r1_k2DrainWord_trafficAtEnv_of_k2_source
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
          (fun q : Phys psi kappa tau => q) ring X C) :
    TrafficAtEnv (fun q : Phys psi kappa tau => q) WP X
      (runHost
        (B9Host.r1Host (kappa := kappa) (tau := tau) hpsi h2)
        ring (k2DrainWord ring X) C) := by
  exact r1_internal_word_trafficAtEnv_of_laws
    (ring := ring) (kappa := kappa) (tau := tau)
    hpsi h2 WP b hlaws X (k2DrainWord ring X) C
    (B6EntranceV2K2.k2DrainWord_internal ring X)
    hAlive hSource.1.1

end B6EntranceEnvelopeWord


