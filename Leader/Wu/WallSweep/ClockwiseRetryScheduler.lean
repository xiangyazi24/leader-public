import Leader.Wu.WallSweep.EchoRank

/-!
# Rank-inductive clockwise retry scheduler

This file separates the finite scheduler argument from the remaining
protocol-field invariant.  An abstract attempt contract supplies either the
exact prefix through the canonical first blocker with strict rank descent, or
the exact full clockwise pass at rank zero.  Strong induction then constructs
a literal schedule with the sharp rank bound.  A second abstraction prepends
one deletion drain whose PeaceView/reset/echo frame reconstructs the retry
boundary without charging path cleanup recursively.
-/

namespace PPLLWallSweepClockwiseScheduler

open PPLL PPLLResearchFormulation PPLLWallSweepSchedule
  PPLLWallSweepEchoDrain PPLLWallSweepFiniteCleanup
  PPLLWallSweepRestartableGeneric PPLLWallSweepEchoRank
  PPLLWallSweepNormalResetContract PPLLExpiringComparisonRepair

variable {n psi kappa tau : Nat}

/-- Configuration abbreviation used by the abstract scheduler contracts. -/
abbrev EConfig (n psi kappa tau : Nat) :=
  Fin n → ExpiringAgentState psi kappa tau

/-- Exact failed attempt through the canonical first blocker. -/
def ClockwiseFailedAttempt
    (T : ExpiringTransition psi kappa tau)
    (ring : DirectedRing n) (leader : Fin n)
    (Ready : EConfig n psi kappa tau → Prop)
    (C : EConfig n psi kappa tau) : Prop :=
  ∃ blocker : Fin (n - 1),
    firstTrue? (clockwiseFollowerEchoBits ring leader C) = some blocker ∧
    Ready (clockwiseAttemptConfig T ring leader C (blocker.val + 1)) ∧
    clockwiseEchoRank ring leader
        (clockwiseAttemptConfig T ring leader C (blocker.val + 1)) <
      clockwiseEchoRank ring leader C

/-- Complete operational seam consumed by the rank scheduler.  Failed rounds
are exact first-blocker prefixes; rank zero is one exact `n`-edge pass. -/
structure ClockwiseAttemptContract
    (T : ExpiringTransition psi kappa tau)
    (ring : DirectedRing n) (_hn : 1 < n)
    (leader : Fin n)
    (Ready Done : EConfig n psi kappa tau → Prop) : Prop where
  failed : ∀ C,
    Ready C → clockwiseEchoRank ring leader C ≠ 0 →
      ClockwiseFailedAttempt T ring leader Ready C
  zero_rank : ∀ C,
    Ready C → clockwiseEchoRank ring leader C = 0 →
      Done (clockwiseAttemptConfig T ring leader C n)

/-- One failed prefix plus a recursively bounded tail fits the original rank
budget.  Multiplication monotonicity is supplied explicitly. -/
private theorem retryBudget_step_le
    (n nextRank rank : Nat) (hRank : nextRank < rank) :
    (n - 1) + (n + (n - 1) * nextRank) ≤
      n + (n - 1) * rank := by
  have hSucc : nextRank + 1 ≤ rank := by omega
  have hMul : (n - 1) * (nextRank + 1) ≤ (n - 1) * rank :=
    Nat.mul_le_mul_left (n - 1) hSucc
  calc
    (n - 1) + (n + (n - 1) * nextRank) =
        n + (n - 1) * (nextRank + 1) := by
      rw [Nat.mul_add, Nat.mul_one]
      ac_rfl
    _ ≤ n + (n - 1) * rank := Nat.add_le_add_left hMul n

/-- Strong-induction scheduler with an explicit rank index. -/
theorem exists_clockwiseRetrySchedule_of_rank
    (T : ExpiringTransition psi kappa tau)
    (ring : DirectedRing n) (hn : 1 < n)
    (leader : Fin n)
    (Ready Done : EConfig n psi kappa tau → Prop)
    (A : ClockwiseAttemptContract T ring hn leader Ready Done)
    (rank : Nat) (C : EConfig n psi kappa tau)
    (hready : Ready C)
    (hrank : clockwiseEchoRank ring leader C = rank) :
    ∃ (word : DetSchedule n) (D : EConfig n psi kappa tau),
      D = runLocalSchedule ring T C word ∧
      word.length ≤ n + (n - 1) * rank ∧ Done D := by
  revert C
  induction rank using Nat.strongRecOn with
  | ind rank ih =>
      intro C hready hrank
      by_cases hz : rank = 0
      · have hzero : clockwiseEchoRank ring leader C = 0 :=
          hrank.trans hz
        let word : DetSchedule n := resetSweepSchedule ring leader n
        let D : EConfig n psi kappa tau :=
          clockwiseAttemptConfig T ring leader C n
        have hdone : Done D := by
          simpa [D] using A.zero_rank C hready hzero
        refine ⟨word, D, ?_, ?_, hdone⟩
        · rfl
        · have hwordLen : word.length = n := by
            simpa [word] using resetSweepSchedule_length ring leader n
          rw [hwordLen, hz]
          simp
      · have hactualNe : clockwiseEchoRank ring leader C ≠ 0 := by
          intro hzero
          apply hz
          exact hrank.symm.trans hzero
        obtain ⟨t, _hcanonical, hready1, hdrop⟩ :=
          A.failed C hready hactualNe
        let pref : DetSchedule n :=
          resetSweepSchedule ring leader (t.val + 1)
        let C1 : EConfig n psi kappa tau :=
          clockwiseAttemptConfig T ring leader C (t.val + 1)
        have hready1' : Ready C1 := by simpa [C1] using hready1
        have hlt : clockwiseEchoRank ring leader C1 < rank := by
          calc
            clockwiseEchoRank ring leader C1 <
                clockwiseEchoRank ring leader C := by simpa [C1] using hdrop
            _ = rank := hrank
        obtain ⟨tail, D, hrunTail, htailLen, hdone⟩ :=
          ih (clockwiseEchoRank ring leader C1) hlt
            C1 hready1' rfl
        have hprefixLenEq : pref.length = t.val + 1 := by
          simpa [pref] using
            resetSweepSchedule_length ring leader (t.val + 1)
        have hprefixLen : pref.length ≤ n - 1 := by
          rw [hprefixLenEq]
          omega
        refine ⟨pref ++ tail, D, ?_, ?_, hdone⟩
        · calc
            D = runLocalSchedule ring T C1 tail := hrunTail
            _ = runLocalSchedule ring T
                (runLocalSchedule ring T C pref) tail := by rfl
            _ = runLocalSchedule ring T C (pref ++ tail) :=
              (runLocalSchedule_append_generic ring T C pref tail).symm
        · simp only [List.length_append]
          calc
            pref.length + tail.length ≤
                (n - 1) +
                  (n + (n - 1) * clockwiseEchoRank ring leader C1) :=
              Nat.add_le_add hprefixLen htailLen
            _ ≤ n + (n - 1) * rank :=
              retryBudget_step_le n
                (clockwiseEchoRank ring leader C1) rank hlt

/-- Public inner scheduler bound at the actual initial rank. -/
theorem exists_clockwiseRetrySchedule
    (T : ExpiringTransition psi kappa tau)
    (ring : DirectedRing n) (hn : 1 < n)
    (leader : Fin n)
    (Ready Done : EConfig n psi kappa tau → Prop)
    (A : ClockwiseAttemptContract T ring hn leader Ready Done)
    (C : EConfig n psi kappa tau) (hready : Ready C) :
    ∃ (word : DetSchedule n) (D : EConfig n psi kappa tau),
      D = runLocalSchedule ring T C word ∧
      word.length ≤ n + (n - 1) * clockwiseEchoRank ring leader C ∧
      Done D := by
  exact exists_clockwiseRetrySchedule_of_rank T ring hn leader Ready Done A
    (clockwiseEchoRank ring leader C) C hready rfl

/-! ## One initial deletion drain -/

/-- Combined field frame returned by the strengthened deletion drain. -/
structure PeaceResetEchoConfigFrame
    (C D : EConfig n psi kappa tau) : Prop where
  peaceView : PeaceViewConfigFrame C D
  resetEcho : ResetEchoConfigFrame C D

/-- Exact one-time drain result used before rank induction. -/
def ClockwiseDrainResult
    (T : ExpiringTransition psi kappa tau)
    (ring : DirectedRing n) (C : EConfig n psi kappa tau) : Prop :=
  ∃ (schedule : DetSchedule n) (out : EConfig n psi kappa tau),
    out = runLocalSchedule ring T C schedule ∧
    schedule.length ≤ comparisonPathCount C ∧
    NoActiveDeletion out ∧ PeaceResetEchoConfigFrame C out

/-- Abstract seam connecting a pre-drain seed predicate to a retry-ready
predicate through the combined field frame. -/
structure ClockwiseOneDrainContract
    (T : ExpiringTransition psi kappa tau)
    (ring : DirectedRing n)
    (Seed Ready : EConfig n psi kappa tau → Prop) : Prop where
  drain : ∀ C, Seed C → ClockwiseDrainResult T ring C
  ready_of_frame : ∀ {C D}, Seed C → NoActiveDeletion D →
    PeaceResetEchoConfigFrame C D → Ready D

/-- One deletion drain followed by the explicit-rank retry scheduler. -/
theorem exists_clockwiseRetrySchedule_after_oneDrain_of_rank
    (T : ExpiringTransition psi kappa tau)
    (ring : DirectedRing n) (hn : 1 < n)
    (leader : Fin n)
    (Seed Ready Done : EConfig n psi kappa tau → Prop)
    (A : ClockwiseAttemptContract T ring hn leader Ready Done)
    (H : ClockwiseOneDrainContract T ring Seed Ready)
    (rank : Nat) (C : EConfig n psi kappa tau)
    (hseed : Seed C)
    (hrank : clockwiseEchoRank ring leader C = rank) :
    ∃ (actual : DetSchedule n) (D : EConfig n psi kappa tau),
      D = runLocalSchedule ring T C actual ∧
      actual.length ≤ comparisonPathCount C + n + (n - 1) * rank ∧
      Done D := by
  rcases H.drain C hseed with
    ⟨drain, C0, hC0, hdrainLen, hnoActive, hframe⟩
  have hready0 : Ready C0 :=
    H.ready_of_frame hseed hnoActive hframe
  have hframeRank : clockwiseEchoRank ring leader C0 =
      clockwiseEchoRank ring leader C :=
    clockwiseEchoRank_eq_of_resetEchoConfigFrame
      ring leader hframe.resetEcho
  have hrank0 : clockwiseEchoRank ring leader C0 = rank :=
    hframeRank.trans hrank
  obtain ⟨tail, D, hrunTail, htailLen, hdone⟩ :=
    exists_clockwiseRetrySchedule_of_rank T ring hn leader Ready Done A
      rank C0 hready0 hrank0
  refine ⟨drain ++ tail, D, ?_, ?_, hdone⟩
  · calc
      D = runLocalSchedule ring T C0 tail := hrunTail
      _ = runLocalSchedule ring T (runLocalSchedule ring T C drain) tail := by
        rw [← hC0]
      _ = runLocalSchedule ring T C (drain ++ tail) :=
        (runLocalSchedule_append_generic ring T C drain tail).symm
  · simp only [List.length_append]
    calc
      drain.length + tail.length ≤
          comparisonPathCount C + (n + (n - 1) * rank) :=
        Nat.add_le_add hdrainLen htailLen
      _ = comparisonPathCount C + n + (n - 1) * rank :=
        (Nat.add_assoc (comparisonPathCount C) n ((n - 1) * rank)).symm

/-- Public one-drain scheduler bound at the actual initial rank. -/
theorem exists_clockwiseRetrySchedule_after_oneDrain
    (T : ExpiringTransition psi kappa tau)
    (ring : DirectedRing n) (hn : 1 < n)
    (leader : Fin n)
    (Seed Ready Done : EConfig n psi kappa tau → Prop)
    (A : ClockwiseAttemptContract T ring hn leader Ready Done)
    (H : ClockwiseOneDrainContract T ring Seed Ready)
    (C : EConfig n psi kappa tau) (hseed : Seed C) :
    ∃ (actual : DetSchedule n) (D : EConfig n psi kappa tau),
      D = runLocalSchedule ring T C actual ∧
      actual.length ≤ comparisonPathCount C + n +
        (n - 1) * clockwiseEchoRank ring leader C ∧
      Done D := by
  exact exists_clockwiseRetrySchedule_after_oneDrain_of_rank
    T ring hn leader Seed Ready Done A H
      (clockwiseEchoRank ring leader C) C hseed rfl

end PPLLWallSweepClockwiseScheduler
