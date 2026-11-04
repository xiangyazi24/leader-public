import Leader.Wu.WallSweep.PreCheckResetContractsExpiringCleanup

/-!
# Pre-CHECK reset contracts: Drain

This module is one dependency-ordered part of the former contract monolith.
-/

namespace PPLLWallSweepPreCheckResetContracts

open PPLL PPLLResearchFormulation PPLLAuthorizedComparisonRepair
  PPLLRepair PPLLWriteIncrementGate
  PPLLExpiringComparisonRepair PPLLPathStallComparisonRepair
  PPLLLeaderCreationCleanupRepair PPLLWallSweepRepair
  PPLLWallSweepFinite PPLLWallSweepFiniteCleanup
  PPLLTerminalEqualSupportRepair
  PPLLWallSweepNormalResetContract PPLLWallSweepEchoDrain
  PPLLWallSweepPreCheckResetRepair
  PPLLNoCheckBirthLeaderFrames
  PPLLNoCheckBirthConditionTwoFrames
  PPLLNoCheckBirthConditionTwoKernel
  PPLLNoCheckBirthConditionTwoPhysical

variable {psi kappa tau : Nat}

/-! ## Canonical deletion drain for the corrected transition -/

/-- A global active-host step is exactly the maintained wall step because the
active responder selects the common T19 priority branch. -/
theorem localStep_preCheckReset_eq_wallSweep_of_active_host
    {n : Nat} (hpsi : psi > 0) (ring : DirectedRing n)
    (C : Fin n → ExpiringAgentState psi kappa tau) (e : Fin n)
    (hactive : deletionActive
      (C (ring.rightNeighbor e)).core.erase = true) :
    localStep ring
      (wallSweepPreCheckResetPathStallTransition hpsi kappa tau) C e =
    localStep ring (wallSweepPathStallTransition hpsi kappa tau) C e := by
  unfold localStep
  dsimp only
  rw [wallSweepPreCheckResetPathStall_eq_wallSweep_of_responder_active
    hpsi kappa tau (C e) (C (ring.rightNeighbor e)) hactive]

/-- Scheduling the predecessor of an active host strictly lowers the global
path count and frames every reset/echo field. -/
theorem wallSweepPreCheckResetPathStall_active_edge_decreases
    {n : Nat} (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (C : Fin n → ExpiringAgentState psi kappa tau) (e : Fin n)
    (hactive : deletionActive
      (C (ring.rightNeighbor e)).core.erase = true) :
    let D := localStep ring
      (wallSweepPreCheckResetPathStallTransition hpsi kappa tau) C e
    comparisonPathCount D < comparisonPathCount C ∧
      ResetEchoConfigFrame C D := by
  rw [localStep_preCheckReset_eq_wallSweep_of_active_host
    hpsi ring C e hactive]
  exact wallSweepPathStall_active_edge_decreases
    hpsi ring hn C e hactive

/-- The same active-host step frames every shield pointwise. -/
theorem wallSweepPreCheckResetPathStall_active_edge_shield_frame
    {n : Nat} (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (C : Fin n → ExpiringAgentState psi kappa tau) (e : Fin n)
    (hactive : deletionActive
      (C (ring.rightNeighbor e)).core.erase = true) :
    let D := localStep ring
      (wallSweepPreCheckResetPathStallTransition hpsi kappa tau) C e
    ShieldConfigFrame C D := by
  rw [localStep_preCheckReset_eq_wallSweep_of_active_host
    hpsi ring C e hactive]
  exact wallSweepPathStall_active_edge_shield_frame
    hpsi ring hn C e hactive

/-- Active T19 deletion frames the complete leader/label/shield/bullet/signal
projection under the corrected transition. -/
theorem wallSweepPreCheckResetPathStall_active_edge_peaceView_frame
    {n : Nat} (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (C : Fin n → ExpiringAgentState psi kappa tau) (e : Fin n)
    (hactive : deletionActive
      (C (ring.rightNeighbor e)).core.erase = true) :
    let D := localStep ring
      (wallSweepPreCheckResetPathStallTransition hpsi kappa tau) C e
    PeaceViewConfigFrame C D := by
  rw [localStep_preCheckReset_eq_wallSweep_of_active_host
    hpsi ring C e hactive]
  exact wallSweepPathStall_active_edge_peaceView_frame
    hpsi ring hn C e hactive

/-- On an active hosted responder, the rooted leader-sink local step is
exactly the established pre-CHECK-reset local step. -/
theorem localStep_leaderSink_eq_preCheckReset_of_active_host
    {n : Nat} (hpsi : psi > 0) (ring : DirectedRing n)
    (C : Fin n → ExpiringAgentState psi kappa tau) (e : Fin n)
    (hactive : deletionActive
      (C (ring.rightNeighbor e)).core.erase = true) :
    localStep ring
      (wallSweepPreCheckResetLeaderSinkPathStallTransition
        hpsi kappa tau) C e =
    localStep ring
      (wallSweepPreCheckResetPathStallTransition hpsi kappa tau) C e := by
  unfold localStep
  dsimp only
  rw [wallSweepPreCheckResetLeaderSinkPathStall_eq_of_responder_active
    hpsi kappa tau (C e) (C (ring.rightNeighbor e)) hactive]

/-- The rooted leader-sink deletion step spends one path and frames
reset/echo exactly as the established repair. -/
theorem wallSweepPreCheckResetLeaderSink_active_edge_decreases
    {n : Nat} (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (C : Fin n → ExpiringAgentState psi kappa tau) (e : Fin n)
    (hactive : deletionActive
      (C (ring.rightNeighbor e)).core.erase = true) :
    let D := localStep ring
      (wallSweepPreCheckResetLeaderSinkPathStallTransition
        hpsi kappa tau) C e
    comparisonPathCount D < comparisonPathCount C ∧
      ResetEchoConfigFrame C D := by
  rw [localStep_leaderSink_eq_preCheckReset_of_active_host
    hpsi ring C e hactive]
  exact wallSweepPreCheckResetPathStall_active_edge_decreases
    hpsi ring hn C e hactive

/-- The same active deletion step frames all shields. -/
theorem wallSweepPreCheckResetLeaderSink_active_edge_shield_frame
    {n : Nat} (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (C : Fin n → ExpiringAgentState psi kappa tau) (e : Fin n)
    (hactive : deletionActive
      (C (ring.rightNeighbor e)).core.erase = true) :
    let D := localStep ring
      (wallSweepPreCheckResetLeaderSinkPathStallTransition
        hpsi kappa tau) C e
    ShieldConfigFrame C D := by
  rw [localStep_leaderSink_eq_preCheckReset_of_active_host
    hpsi ring C e hactive]
  exact wallSweepPreCheckResetPathStall_active_edge_shield_frame
    hpsi ring hn C e hactive

/-- The same active deletion step frames the complete physical PeaceView. -/
theorem wallSweepPreCheckResetLeaderSink_active_edge_peaceView_frame
    {n : Nat} (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (C : Fin n → ExpiringAgentState psi kappa tau) (e : Fin n)
    (hactive : deletionActive
      (C (ring.rightNeighbor e)).core.erase = true) :
    let D := localStep ring
      (wallSweepPreCheckResetLeaderSinkPathStallTransition
        hpsi kappa tau) C e
    PeaceViewConfigFrame C D := by
  rw [localStep_leaderSink_eq_preCheckReset_of_active_host
    hpsi ring C e hactive]
  exact wallSweepPreCheckResetPathStall_active_edge_peaceView_frame
    hpsi ring hn C e hactive

/-- Canonical corrected-transition deletion drain. It strictly spends one
physical path per inserted edge, frames reset/echo and the complete PeaceView,
and chooses the empty schedule on an already drained input. -/
theorem exists_wallSweepPreCheckResetDeletionDrain_peaceFrame
    {n : Nat} (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (C : Fin n → ExpiringAgentState psi kappa tau) :
    ∃ schedule : DetSchedule n,
      schedule.length ≤ comparisonPathCount C ∧
      (NoActiveDeletion C → schedule = []) ∧
      let D := runLocalSchedule ring
        (wallSweepPreCheckResetPathStallTransition hpsi kappa tau) C schedule
      NoActiveDeletion D ∧ ResetEchoConfigFrame C D ∧
        ShieldConfigFrame C D ∧ PeaceViewConfigFrame C D := by
  generalize hk : comparisonPathCount C = k
  induction k using Nat.strongRecOn generalizing C with
  | ind k ih =>
      by_cases hnone : NoActiveDeletion C
      · exact ⟨[], by simp, fun _ => rfl, hnone,
          fun i => ResetEchoFrame.refl (C i), ShieldConfigFrame.refl C,
          PeaceViewConfigFrame.refl C⟩
      · have hexists : ∃ j : Fin n,
            deletionActive (C j).core.erase = true := by
          apply Classical.byContradiction
          intro hnot
          apply hnone
          intro i
          cases hi : deletionActive (C i).core.erase with
          | false => rfl
          | true => exact False.elim (hnot ⟨i, hi⟩)
        obtain ⟨j, hj⟩ := hexists
        let e := ring.leftNeighbor j
        have hneighbor : ring.rightNeighbor e = j :=
          rightNeighbor_leftNeighbor_wall ring j
        let C1 := localStep ring
          (wallSweepPreCheckResetPathStallTransition hpsi kappa tau) C e
        have hstep := wallSweepPreCheckResetPathStall_active_edge_decreases
          hpsi ring hn C e (by simpa [hneighbor] using hj)
        change comparisonPathCount C1 < comparisonPathCount C ∧
          ResetEchoConfigFrame C C1 at hstep
        have hshield :=
          wallSweepPreCheckResetPathStall_active_edge_shield_frame
            hpsi ring hn C e (by simpa [hneighbor] using hj)
        change ShieldConfigFrame C C1 at hshield
        have hpeace :=
          wallSweepPreCheckResetPathStall_active_edge_peaceView_frame
            hpsi ring hn C e (by simpa [hneighbor] using hj)
        change PeaceViewConfigFrame C C1 at hpeace
        have hlt : comparisonPathCount C1 < k := by
          rw [← hk]
          exact hstep.1
        obtain ⟨tail, htailLength, htailEmpty, htailNoActive,
          htailFrame, htailShield, htailPeace⟩ :=
          ih (comparisonPathCount C1) hlt C1 rfl
        refine ⟨e :: tail, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · simp only [List.length_cons]
          omega
        · intro hC
          exact (hnone hC).elim
        · exact htailNoActive
        · exact hstep.2.trans htailFrame
        · exact hshield.trans htailShield
        · exact hpeace.trans htailPeace

/-- Canonical deletion drain for the rooted leader-sink repair.  Its schedule
and bound are unchanged because every scheduled active-host step agrees
exactly with the established repair. -/
theorem exists_wallSweepPreCheckResetLeaderSinkDeletionDrain_peaceFrame
    {n : Nat} (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (C : Fin n → ExpiringAgentState psi kappa tau) :
    ∃ schedule : DetSchedule n,
      schedule.length ≤ comparisonPathCount C ∧
      (NoActiveDeletion C → schedule = []) ∧
      let D := runLocalSchedule ring
        (wallSweepPreCheckResetLeaderSinkPathStallTransition
          hpsi kappa tau) C schedule
      NoActiveDeletion D ∧ ResetEchoConfigFrame C D ∧
        ShieldConfigFrame C D ∧ PeaceViewConfigFrame C D := by
  generalize hk : comparisonPathCount C = k
  induction k using Nat.strongRecOn generalizing C with
  | ind k ih =>
      by_cases hnone : NoActiveDeletion C
      · exact ⟨[], by simp, fun _ => rfl, hnone,
          fun i => ResetEchoFrame.refl (C i), ShieldConfigFrame.refl C,
          PeaceViewConfigFrame.refl C⟩
      · have hexists : ∃ j : Fin n,
            deletionActive (C j).core.erase = true := by
          apply Classical.byContradiction
          intro hnot
          apply hnone
          intro i
          cases hi : deletionActive (C i).core.erase with
          | false => rfl
          | true => exact False.elim (hnot ⟨i, hi⟩)
        obtain ⟨j, hj⟩ := hexists
        let e := ring.leftNeighbor j
        have hneighbor : ring.rightNeighbor e = j :=
          rightNeighbor_leftNeighbor_wall ring j
        let C1 := localStep ring
          (wallSweepPreCheckResetLeaderSinkPathStallTransition
            hpsi kappa tau) C e
        have hstep := wallSweepPreCheckResetLeaderSink_active_edge_decreases
          hpsi ring hn C e (by simpa [hneighbor] using hj)
        change comparisonPathCount C1 < comparisonPathCount C ∧
          ResetEchoConfigFrame C C1 at hstep
        have hshield :=
          wallSweepPreCheckResetLeaderSink_active_edge_shield_frame
            hpsi ring hn C e (by simpa [hneighbor] using hj)
        change ShieldConfigFrame C C1 at hshield
        have hpeace :=
          wallSweepPreCheckResetLeaderSink_active_edge_peaceView_frame
            hpsi ring hn C e (by simpa [hneighbor] using hj)
        change PeaceViewConfigFrame C C1 at hpeace
        have hlt : comparisonPathCount C1 < k := by
          rw [← hk]
          exact hstep.1
        obtain ⟨tail, htailLength, htailEmpty, htailNoActive,
          htailFrame, htailShield, htailPeace⟩ :=
          ih (comparisonPathCount C1) hlt C1 rfl
        refine ⟨e :: tail, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · simp only [List.length_cons]
          omega
        · intro hC
          exact (hnone hC).elim
        · exact htailNoActive
        · exact hstep.2.trans htailFrame
        · exact hshield.trans htailShield
        · exact hpeace.trans htailPeace

/-- Projection of the stronger deletion drain used by the shielded scheduler. -/
theorem exists_wallSweepPreCheckResetDeletionDrain_cleanupFrame
    {n : Nat} (hpsi : psi > 0) (ring : DirectedRing n) (hn : 1 < n)
    (C : Fin n → ExpiringAgentState psi kappa tau) :
    ∃ schedule : DetSchedule n,
      schedule.length ≤ comparisonPathCount C ∧
      (NoActiveDeletion C → schedule = []) ∧
      let D := runLocalSchedule ring
        (wallSweepPreCheckResetPathStallTransition hpsi kappa tau) C schedule
      NoActiveDeletion D ∧ ResetEchoConfigFrame C D ∧
        ShieldConfigFrame C D := by
  obtain ⟨schedule, hlength, hempty, hnoActive, hreset, hshield, _⟩ :=
    exists_wallSweepPreCheckResetDeletionDrain_peaceFrame
      hpsi ring hn C
  exact ⟨schedule, hlength, hempty, hnoActive, hreset, hshield⟩


end PPLLWallSweepPreCheckResetContracts
