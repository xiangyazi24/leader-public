import Leader.Wu.PartialProtocol.MinimalLockRepair

/-!
# Stale-lock obstruction to arbitrary-state self-stabilization

The one-bit lock repair has a closed legitimate set, but the bit is ordinary
arbitrary-initialized protocol state.  If every endpoint starts locked, the
complete local transition is the identity independently of the physical
states.  Hence an all-locked configuration with two leaders is a closed bad
trap.

This file gives a concrete two-agent instance.  Both agents carry the same
finite physical leader state and a true lock.  Every one-step and every
reachable execution is equal to the initial configuration, while both agents
emit the leader output.  In particular, no reachable configuration is safe.
-/

namespace PPLLCompleteMultiLeaderCleanup

open PPLL PPLLResearchFormulation
  PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
open PPartialMinimalLockRepairSol

namespace PPartialMinimalLockStaleCounterexampleSol

variable {n psi kappa tau : Nat}

/-! ## Generic all-locked fixed points -/

/-- Every all-locked configuration is fixed by every packaged interaction. -/
theorem allLocked_step_eq
    (hpsi : psi > 0) (kappa tau : Nat)
    (ring : DirectedRing n)
    (C : MinimalLockConfig n psi kappa tau)
    (hlocked : MinimalLockAllLocked C) (e : Fin n) :
    (P_partialMinimalLockProtocol hpsi kappa tau).step ring C e = C :=
  P_partialMinimalLock_step_eq_of_allLocked
    hpsi kappa tau ring C hlocked e

/-- Reachability from an all-locked configuration is the singleton containing
that configuration. -/
theorem allLocked_reachable_eq
    (hpsi : psi > 0) (kappa tau : Nat)
    (ring : DirectedRing n)
    (C : MinimalLockConfig n psi kappa tau)
    (hlocked : MinimalLockAllLocked C)
    {D : MinimalLockConfig n psi kappa tau}
    (hreach : PopulationProtocol.Reachable
      (P_partialMinimalLockProtocol hpsi kappa tau) ring C D) :
    D = C := by
  have hsingleton :
      PopulationProtocol.ClosedPred
        (P_partialMinimalLockProtocol hpsi kappa tau) ring
        (fun X => X = C) := by
    intro X hX Y hstep
    subst X
    obtain ⟨e, rfl⟩ := hstep
    exact allLocked_step_eq hpsi kappa tau ring C hlocked e
  exact hsingleton.reachable rfl hreach

/-- The whole class of all-locked configurations with non-unique leader
output is a closed bad trap. -/
def StaleLockBad
    (hpsi : psi > 0) (kappa tau : Nat)
    (C : MinimalLockConfig n psi kappa tau) : Prop :=
  MinimalLockAllLocked C ∧
    ¬ UniqueLeaderOutput
      (P_partialMinimalLockProtocol hpsi kappa tau)
      n C isLeaderOutput

theorem staleLockBad_closed
    (hpsi : psi > 0) (kappa tau : Nat)
    (ring : DirectedRing n) :
    PopulationProtocol.ClosedPred
      (P_partialMinimalLockProtocol hpsi kappa tau) ring
      (StaleLockBad hpsi kappa tau) := by
  intro C hC D hstep
  obtain ⟨e, rfl⟩ := hstep
  rw [allLocked_step_eq hpsi kappa tau ring C hC.1 e]
  exact hC

/-! ## A literal two-agent stale-lock trap -/

abbrev StalePsi : Nat := 2

private theorem staleHPsi : StalePsi > 0 := by
  decide

private def staleLeaderRaw : AgentState StalePsi :=
  PPLLCounterexample.state2 0 true

private theorem staleLeaderRaw_domain (kappa : Nat) :
    staleLeaderRaw.inProtocolDomain kappa := by
  simp [staleLeaderRaw, PPLLCounterexample.state2,
    AgentState.inProtocolDomain]

/-- A finite physical state whose leader bit is definitionally true. -/
def staleLeaderPhysical (kappa tau : Nat) :
    ExpiringAgentState StalePsi kappa tau :=
  ⟨⟨BoundedAgentState.ofDomain staleLeaderRaw
      (staleLeaderRaw_domain kappa), false⟩,
    freshStall tau⟩

/-- Both agents have a true physical leader bit and an already-true lock. -/
def staleLockedDoubleLeaderConfig (kappa tau : Nat) :
    MinimalLockConfig 2 StalePsi kappa tau :=
  fun _ => (staleLeaderPhysical kappa tau, true)

theorem staleLockedDoubleLeader_allLocked (kappa tau : Nat) :
    MinimalLockAllLocked
      (staleLockedDoubleLeaderConfig kappa tau) := by
  intro i
  rfl

theorem staleLockedDoubleLeader_leader
    (kappa tau : Nat) (i : Fin 2) :
    minimalLockLeader (staleLockedDoubleLeaderConfig kappa tau i) = true := by
  rfl

theorem staleLockedDoubleLeader_output
    (kappa tau : Nat) (i : Fin 2) :
    (P_partialMinimalLockProtocol staleHPsi kappa tau).output
      (staleLockedDoubleLeaderConfig kappa tau i) = .leader := by
  change
    (if minimalLockLeader (staleLockedDoubleLeaderConfig kappa tau i) then
      LeaderOutput.leader else LeaderOutput.follower) = .leader
  rw [staleLockedDoubleLeader_leader]
  rfl

private theorem finTwo_zero_ne_one : (0 : Fin 2) ≠ (1 : Fin 2) := by
  intro h
  have hv := congrArg Fin.val h
  omega

/-- The concrete trapped configuration has at least two leader outputs, so it
does not have a unique leader output. -/
theorem staleLockedDoubleLeader_not_unique (kappa tau : Nat) :
    ¬ UniqueLeaderOutput
      (P_partialMinimalLockProtocol staleHPsi kappa tau)
      2 (staleLockedDoubleLeaderConfig kappa tau) isLeaderOutput := by
  rintro ⟨leader, _, honly⟩
  have hzero :
      isLeaderOutput
        ((P_partialMinimalLockProtocol staleHPsi kappa tau).output
          (staleLockedDoubleLeaderConfig kappa tau 0)) = true := by
    rw [staleLockedDoubleLeader_output]
    rfl
  have hone :
      isLeaderOutput
        ((P_partialMinimalLockProtocol staleHPsi kappa tau).output
          (staleLockedDoubleLeaderConfig kappa tau 1)) = true := by
    rw [staleLockedDoubleLeader_output]
    rfl
  apply finTwo_zero_ne_one
  exact (honly 0 hzero).trans (honly 1 hone).symm

theorem staleLockedDoubleLeader_mem_bad (kappa tau : Nat) :
    StaleLockBad staleHPsi kappa tau
      (staleLockedDoubleLeaderConfig kappa tau) :=
  ⟨staleLockedDoubleLeader_allLocked kappa tau,
    staleLockedDoubleLeader_not_unique kappa tau⟩

/-- Every exact step from the concrete bad configuration is identity. -/
theorem staleLockedDoubleLeader_step_eq
    (kappa tau : Nat) (ring : DirectedRing 2) (e : Fin 2) :
    (P_partialMinimalLockProtocol staleHPsi kappa tau).step ring
        (staleLockedDoubleLeaderConfig kappa tau) e =
      staleLockedDoubleLeaderConfig kappa tau :=
  allLocked_step_eq staleHPsi kappa tau ring
    (staleLockedDoubleLeaderConfig kappa tau)
    (staleLockedDoubleLeader_allLocked kappa tau) e

/-- Every reachable configuration from the concrete trap is literally the
same bad configuration. -/
theorem staleLockedDoubleLeader_reachable_eq
    (kappa tau : Nat) (ring : DirectedRing 2)
    {D : MinimalLockConfig 2 StalePsi kappa tau}
    (hreach : PopulationProtocol.Reachable
      (P_partialMinimalLockProtocol staleHPsi kappa tau) ring
      (staleLockedDoubleLeaderConfig kappa tau) D) :
    D = staleLockedDoubleLeaderConfig kappa tau :=
  allLocked_reachable_eq staleHPsi kappa tau ring
    (staleLockedDoubleLeaderConfig kappa tau)
    (staleLockedDoubleLeader_allLocked kappa tau) hreach

/-- The trapped configuration itself is not Definition-1 safe. -/
theorem staleLockedDoubleLeader_not_isSafe
    (kappa tau : Nat) (ring : DirectedRing 2) :
    ¬ PopulationProtocol.IsSafe
      (P_partialMinimalLockProtocol staleHPsi kappa tau) ring
      (staleLockedDoubleLeaderConfig kappa tau) isLeaderOutput := by
  intro hsafe
  exact staleLockedDoubleLeader_not_unique kappa tau hsafe.1

/-- Strong terminal obstruction: no execution from the stale-lock trap can
reach any Definition-1 safe configuration. -/
theorem staleLockedDoubleLeader_cannot_reach_isSafe
    (kappa tau : Nat) (ring : DirectedRing 2) :
    ¬ ∃ D : MinimalLockConfig 2 StalePsi kappa tau,
      PopulationProtocol.Reachable
          (P_partialMinimalLockProtocol staleHPsi kappa tau) ring
          (staleLockedDoubleLeaderConfig kappa tau) D ∧
        PopulationProtocol.IsSafe
          (P_partialMinimalLockProtocol staleHPsi kappa tau) ring
          D isLeaderOutput := by
  rintro ⟨D, hreach, hsafe⟩
  have hD := staleLockedDoubleLeader_reachable_eq
    kappa tau ring hreach
  subst D
  exact staleLockedDoubleLeader_not_isSafe kappa tau ring hsafe

end PPartialMinimalLockStaleCounterexampleSol
end PPLLCompleteMultiLeaderCleanup
