import Leader.Wu.Scheduler.RepeatedBlocks
import Leader.Wu.Epoch.FilterSweep

/-!
# Repeated-block amplification for the P_PLL-derived epoch repair

One ordered non-wrap sweep is favorable from every physical state.  Because
uniform scheduler outcomes are an exact finite product, aligned repetitions
multiply the miss budget: after `k` blocks, at most
`(n^(n-1)-1)^k` of the `n^(k(n-1))` schedules avoid the protected set.

This is a genuine geometric amplification theorem and needs no fairness or
probabilistic independence axiom.  Its block success probability is still only
`1/n^(n-1)`, so the resulting horizon is not yet Wu's WHP runtime bound.
-/

namespace PPLLDerivedEpochAmplification

open PPLLResearchFormulation PPLLTraceConvergence PPLLSchedulerBlocks
  PPLLProtectedEpochProtocol PPLLProtectedEpochSweep
  PPLLDerivedEpochRepair PPLLDerivedEpochSweep

/-- Boolean decision procedure for the physical protected-rotation predicate. -/
noncomputable def protectedEpochTest (ring : DirectedRing n)
    (C : Fin n → EpochAgentState n ψ κ) : Bool := by
  classical
  exact decide (ProtectedEpoch ring.hn ring C)

/-- The Boolean protected-epoch test is exact. -/
theorem protectedEpochTest_decides (ring : DirectedRing n)
    (C : Fin n → EpochAgentState n ψ κ) :
    protectedEpochTest ring C = true ↔ ProtectedEpoch ring.hn ring C := by
  classical
  simp [protectedEpochTest]

/-- An endpoint satisfying the Boolean target makes the prefix-hitting test
succeed. -/
theorem hitsWithinLocal_of_post_runLocalSchedule
    {Q : Type} (ring : DirectedRing n) (T : Q → Q → Q × Q)
    (post : (Fin n → Q) → Bool)
    (C : Fin n → Q) (s : DetSchedule n)
    (hpost : post (runLocalSchedule ring T C s) = true) :
    hitsWithinLocal ring T post C s = true := by
  induction s generalizing C with
  | nil => exact hpost
  | cons e rest ih =>
      simp only [runLocalSchedule] at hpost
      simp only [hitsWithinLocal]
      have htail := ih (localStep ring T C e) hpost
      simp [htail]

/-- The named non-wrap sweep hits the protected-set Boolean test from every
arbitrary P_PLL-derived epoch state. -/
theorem ppllEpochFilter_sweep_hits
    (hψ : ψ > 0) (κ : Nat) (hn2 : 1 < n)
    (ring : DirectedRing n)
    (C : Fin n → EpochAgentState n ψ κ) :
    hitsWithinLocal ring (ppllEpochFilterTransition hψ κ ring.hn)
      (protectedEpochTest ring) C (epochPreWrapSweep n hn2) = true := by
  apply hitsWithinLocal_of_post_runLocalSchedule
  exact (protectedEpochTest_decides ring _).2
    (ppllEpochFilter_sweep_enters_protected hψ κ hn2 ring C)

/-- At least one exact length-`n-1` outcome reaches the protected set. -/
theorem ppllEpochFilter_localHitCount_pos
    (hψ : ψ > 0) (κ : Nat) (hn2 : 1 < n)
    (ring : DirectedRing n)
    (C : Fin n → EpochAgentState n ψ κ) :
    0 < localHitCount ring
      (ppllEpochFilterTransition hψ κ ring.hn)
      (protectedEpochTest ring) C (n - 1) := by
  unfold localHitCount
  apply List.countP_pos_iff.mpr
  exact ⟨epochPreWrapSweep n hn2,
    mem_allSchedules_of_length n (n - 1) (epochPreWrapSweep n hn2)
      (epochSweepPrefix_length n (n - 1) (by omega)),
    ppllEpochFilter_sweep_hits hψ κ hn2 ring C⟩

/-- One block has at most `n^(n-1)-1` misses. -/
theorem ppllEpochFilter_oneBlockPhase
    (hψ : ψ > 0) (κ : Nat) (hn2 : 1 < n)
    (ring : DirectedRing n) :
    UniformFinitePhase ring
      (ppllEpochFilterTransition hψ κ ring.hn)
      (fun _ => True) (ProtectedEpoch ring.hn ring)
      (protectedEpochTest ring) (n - 1) (n ^ (n - 1) - 1) := by
  constructor
  · exact protectedEpochTest_decides ring
  · intro C hC
    rw [allSchedules_length]
    have hhit := ppllEpochFilter_localHitCount_pos hψ κ hn2 ring C
    have htotal : 0 < n ^ (n - 1) := Nat.pow_pos ring.hn
    omega

/-- Exact aligned-block amplification.  The result counts all successful
schedules, not only repetitions of the single named sweep. -/
theorem ppllEpochFilter_repeatedBlockPhase
    (hψ : ψ > 0) (κ : Nat) (hn2 : 1 < n)
    (ring : DirectedRing n) (k : Nat) :
    UniformFinitePhase ring
      (ppllEpochFilterTransition hψ κ ring.hn)
      (fun _ => True) (ProtectedEpoch ring.hn ring)
      (protectedEpochTest ring)
      (k * (n - 1)) ((n ^ (n - 1) - 1) ^ k) := by
  exact uniformFinitePhase_repeatedBlock ring
    (ppllEpochFilterTransition hψ κ ring.hn)
    (ProtectedEpoch ring.hn ring) (protectedEpochTest ring)
    (n - 1) (n ^ (n - 1) - 1)
    (ppllEpochFilter_oneBlockPhase hψ κ hn2 ring) k

/-- Repeated-block corrected finite convergence capstone: protected legitimacy
is closed and semantically safe, while every requested block count has its
exact geometric miss budget.  Turning this budget into the thesis's symbolic
WHP runtime remains an arithmetic/dynamics obligation, not a hidden premise. -/
theorem ppllEpochFilter_repeatedBlock_capstone
    (hψ : ψ > 0) (κ : Nat) (hn2 : 1 < n)
    (ring : DirectedRing n) :
    PopulationProtocol.ClosedPred
        (ppllEpochFilterProtocol hψ κ ring.hn) ring
        (ProtectedEpoch ring.hn ring) ∧
      (∀ C : Fin n → EpochAgentState n ψ κ,
        ProtectedEpoch ring.hn ring C →
          PopulationProtocol.IsSafe
            (ppllEpochFilterProtocol hψ κ ring.hn) ring C
            isLeaderOutput) ∧
      ∀ k, UniformFinitePhase ring
        (ppllEpochFilterTransition hψ κ ring.hn)
        (fun _ => True) (ProtectedEpoch ring.hn ring)
        (protectedEpochTest ring)
        (k * (n - 1)) ((n ^ (n - 1) - 1) ^ k) := by
  exact ⟨ppllEpochFilter_closed hψ κ ring,
    fun C hC => ppllEpochFilter_isSafe hψ κ ring hC,
    ppllEpochFilter_repeatedBlockPhase hψ κ hn2 ring⟩

end PPLLDerivedEpochAmplification
