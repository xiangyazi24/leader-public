import Leader.Wu.PartialProtocol.CollisionReset

/-!
# Unbounded separated-leader traps for the collision reset

The factor-four collision reset removes a responder leader only on a selected
leader/leader edge.  This file gives one explicit counterfamily at every size
`n ≥ 4`: an all-sealed alternating leader/follower word, with the last
potential leader suppressed when needed to close an odd cycle.  Positions
zero and two are leaders, no two directed neighbors are leaders, and every
transition is therefore identity.

For even `n` the word is the exact repetition `L F L F ... L F`.  For odd
`n`, the same prefix is used and the final even position is changed to a
follower, yielding `L F L F ... F F`.  Thus odd sizes are covered as well;
the exact all-size boundary proved here is `n ≥ 4`.

This is a counterexample to arbitrary-state stabilization of this concrete
collision-reset candidate.  It does not say that collision resets with more
state, nonlocal information, or a different rule are impossible.
-/

namespace PPLLCompleteMultiLeaderCleanup
namespace PPartialDynamicSweepResetCounterfamilySol

open PPLL PPLLResearchFormulation
open PPLLStaticDoubleCoverNoGo
open PPartialMinimalLockRepairSol
open PPartialMinimalLockStaleCounterexampleSol
open PPartialDynamicSweepLockSol
open PPartialDynamicSweepResetSol

variable {n kappa tau : Nat}

/-! ## The padded alternating word -/

abbrev SeparatedPsi : Nat := 2

private theorem separatedHPsi : SeparatedPsi > 0 := by
  decide

/-- A sealed leader state.  The accepted inner lock is also true, although
the collision-reset obstruction uses only the outer seal and leader bits. -/
def separatedLeaderState (kappa tau : Nat) :
    SweepResetState SeparatedPsi kappa tau :=
  ((staleLeaderPhysical kappa tau, true), true)

/-- The matching sealed follower state, obtained by clearing only the
physical leader bit. -/
def separatedFollowerState (kappa tau : Nat) :
    SweepResetState SeparatedPsi kappa tau :=
  (clearMinimalLockLeader (staleLeaderPhysical kappa tau, true), true)

@[simp] theorem separatedLeaderState_leader (kappa tau : Nat) :
    sweepLockLeader (separatedLeaderState kappa tau) = true := by
  rfl

@[simp] theorem separatedFollowerState_leader (kappa tau : Nat) :
    sweepLockLeader (separatedFollowerState kappa tau) = false := by
  rfl

@[simp] theorem separatedLeaderState_sealed (kappa tau : Nat) :
    (separatedLeaderState kappa tau).2 = true := by
  rfl

@[simp] theorem separatedFollowerState_sealed (kappa tau : Nat) :
    (separatedFollowerState kappa tau).2 = true := by
  rfl

/-- Alternation with an explicit closing guard.  A site is a leader exactly
when its index is even and it has a genuine successor before the wrap edge.
For even sizes this is exact period two.  At an odd size the final even site
is forced to be a follower, preventing a wraparound collision. -/
def paddedAlternatingConfig (n kappa tau : Nat) :
    SweepResetConfig n SeparatedPsi kappa tau :=
  fun i =>
    if i.val % 2 = 0 ∧ i.val + 1 < n then
      separatedLeaderState kappa tau
    else
      separatedFollowerState kappa tau

@[simp] theorem paddedAlternatingConfig_sealed
    (n kappa tau : Nat) (i : Fin n) :
    (paddedAlternatingConfig n kappa tau i).2 = true := by
  simp [paddedAlternatingConfig]

theorem paddedAlternatingConfig_leader_iff
    (n kappa tau : Nat) (i : Fin n) :
    sweepLockLeader (paddedAlternatingConfig n kappa tau i) = true ↔
      i.val % 2 = 0 ∧ i.val + 1 < n := by
  unfold paddedAlternatingConfig
  by_cases h : i.val % 2 = 0 ∧ i.val + 1 < n <;> simp [h]

theorem paddedAlternatingConfig_allSealed
    (n kappa tau : Nat) :
    SweepLockAllSealed (paddedAlternatingConfig n kappa tau) := by
  intro i
  exact paddedAlternatingConfig_sealed n kappa tau i

/-! ## Two separated leaders and no collision edge -/

theorem paddedAlternatingConfig_zero_leader
    (kappa tau : Nat) (hn : 4 ≤ n) :
    sweepLockLeader (paddedAlternatingConfig n kappa tau ⟨0, by omega⟩) =
      true := by
  rw [paddedAlternatingConfig_leader_iff]
  constructor
  · rfl
  · change 0 + 1 < n
    omega

theorem paddedAlternatingConfig_two_leader
    (kappa tau : Nat) (hn : 4 ≤ n) :
    sweepLockLeader (paddedAlternatingConfig n kappa tau ⟨2, by omega⟩) =
      true := by
  rw [paddedAlternatingConfig_leader_iff]
  constructor
  · change 2 % 2 = 0
    decide
  · change 2 + 1 < n
    omega

theorem paddedAlternatingConfig_hasTwoLeaders
    (kappa tau : Nat) (hn : 4 ≤ n) :
    HasTwoLeaderOutputs
      (P_partialSweepResetProtocol separatedHPsi kappa tau)
      isLeaderOutput (paddedAlternatingConfig n kappa tau) := by
  let i : Fin n := ⟨0, by omega⟩
  let j : Fin n := ⟨2, by omega⟩
  refine ⟨i, j, ?_, ?_, ?_⟩
  · intro hij
    have hv := congrArg Fin.val hij
    change 0 = 2 at hv
    omega
  · change isLeaderOutput
      (if sweepLockLeader (paddedAlternatingConfig n kappa tau i)
        then LeaderOutput.leader else LeaderOutput.follower) = true
    rw [paddedAlternatingConfig_zero_leader kappa tau hn]
    rfl
  · change isLeaderOutput
      (if sweepLockLeader (paddedAlternatingConfig n kappa tau j)
        then LeaderOutput.leader else LeaderOutput.follower) = true
    rw [paddedAlternatingConfig_two_leader kappa tau hn]
    rfl

/-- No directed edge of the padded alternating word exposes the collision
pair.  If the initiator is a leader, its closing guard proves that the edge
does not wrap, and consecutive naturals cannot both be even. -/
theorem paddedAlternatingConfig_noAdjacent
    (ring : DirectedRing n) (kappa tau : Nat) :
    SweepResetNoAdjacentLeaders ring
      (paddedAlternatingConfig n kappa tau) := by
  intro e hboth
  have he :=
    (paddedAlternatingConfig_leader_iff n kappa tau e).mp hboth.1
  have hj :=
    (paddedAlternatingConfig_leader_iff n kappa tau
      (ring.rightNeighbor e)).mp hboth.2
  have hjval : (ring.rightNeighbor e).val = e.val + 1 := by
    unfold DirectedRing.rightNeighbor
    simp [Nat.mod_eq_of_lt he.2]
  rw [hjval] at hj
  omega

/-! ## Closed bad trap and singleton reachability -/

/-- The exact residual bad class used by the counterfamily. -/
def SweepResetSeparatedBad
    (ring : DirectedRing n)
    (C : SweepResetConfig n SeparatedPsi kappa tau) : Prop :=
  SweepLockAllSealed C ∧
    SweepResetNoAdjacentLeaders ring C ∧
    HasTwoLeaderOutputs
      (P_partialSweepResetProtocol separatedHPsi kappa tau)
      isLeaderOutput C

theorem sweepResetSeparatedBad_every_step_eq
    (ring : DirectedRing n)
    (C : SweepResetConfig n SeparatedPsi kappa tau)
    (hbad : SweepResetSeparatedBad ring C) :
    ∀ e,
      (P_partialSweepResetProtocol separatedHPsi kappa tau).step ring C e = C :=
  P_partialSweepReset_step_eq_of_allSealed_noAdjacent
    separatedHPsi kappa tau ring C hbad.1 hbad.2.1

theorem sweepResetSeparatedBad_closed
    (ring : DirectedRing n) :
    PopulationProtocol.ClosedPred
      (P_partialSweepResetProtocol separatedHPsi kappa tau) ring
      (SweepResetSeparatedBad ring) := by
  intro C hC D hstep
  obtain ⟨e, rfl⟩ := hstep
  rw [sweepResetSeparatedBad_every_step_eq ring C hC e]
  exact hC

theorem sweepResetSeparatedBad_reachable_eq
    (ring : DirectedRing n)
    (C : SweepResetConfig n SeparatedPsi kappa tau)
    (hbad : SweepResetSeparatedBad ring C)
    {D : SweepResetConfig n SeparatedPsi kappa tau}
    (hreach : PopulationProtocol.Reachable
      (P_partialSweepResetProtocol separatedHPsi kappa tau) ring C D) :
    D = C := by
  have hsingleton :
      PopulationProtocol.ClosedPred
        (P_partialSweepResetProtocol separatedHPsi kappa tau) ring
        (fun X => X = C) := by
    intro X hX Y hstep
    subst X
    obtain ⟨e, rfl⟩ := hstep
    exact sweepResetSeparatedBad_every_step_eq ring C hbad e
  exact hsingleton.reachable rfl hreach

theorem sweepResetSeparatedBad_not_unique
    (ring : DirectedRing n)
    {C : SweepResetConfig n SeparatedPsi kappa tau}
    (hbad : SweepResetSeparatedBad ring C) :
    ¬ UniqueLeaderOutput
      (P_partialSweepResetProtocol separatedHPsi kappa tau)
      n C isLeaderOutput :=
  hasTwoLeaders_not_unique
    (P_partialSweepResetProtocol separatedHPsi kappa tau)
    isLeaderOutput hbad.2.2

theorem sweepResetSeparatedBad_cannot_reach_isSafe
    (ring : DirectedRing n)
    {C : SweepResetConfig n SeparatedPsi kappa tau}
    (hbad : SweepResetSeparatedBad ring C) :
    ¬ ∃ D : SweepResetConfig n SeparatedPsi kappa tau,
      PopulationProtocol.Reachable
          (P_partialSweepResetProtocol separatedHPsi kappa tau) ring C D ∧
        PopulationProtocol.IsSafe
          (P_partialSweepResetProtocol separatedHPsi kappa tau)
          ring D isLeaderOutput := by
  rintro ⟨D, hreach, hsafe⟩
  have hD := sweepResetSeparatedBad_reachable_eq ring C hbad hreach
  subst D
  exact sweepResetSeparatedBad_not_unique ring hbad hsafe.1

/-! ## Unbounded all-size, even-size, and odd-size statements -/

/-- Main counterfamily: every population size at least four has an explicit
all-sealed separated multi-leader configuration with singleton reachability,
and no execution from it reaches Definition-1 safety. -/
theorem sweepReset_paddedAlternating_counterfamily
    (n kappa tau : Nat) (hn : 4 ≤ n) :
    let ring : DirectedRing n := ⟨by omega⟩
    let C := paddedAlternatingConfig n kappa tau
    SweepResetSeparatedBad ring C ∧
      (∀ e : Fin n,
        (P_partialSweepResetProtocol separatedHPsi kappa tau).step ring C e = C) ∧
      (∀ D : SweepResetConfig n SeparatedPsi kappa tau,
        PopulationProtocol.Reachable
          (P_partialSweepResetProtocol separatedHPsi kappa tau) ring C D → D = C) ∧
      ¬ ∃ D : SweepResetConfig n SeparatedPsi kappa tau,
        PopulationProtocol.Reachable
            (P_partialSweepResetProtocol separatedHPsi kappa tau) ring C D ∧
          PopulationProtocol.IsSafe
            (P_partialSweepResetProtocol separatedHPsi kappa tau)
            ring D isLeaderOutput := by
  dsimp only
  let ring : DirectedRing n := ⟨by omega⟩
  let C := paddedAlternatingConfig n kappa tau
  have hbad : SweepResetSeparatedBad ring C :=
    ⟨paddedAlternatingConfig_allSealed n kappa tau,
      paddedAlternatingConfig_noAdjacent ring kappa tau,
      paddedAlternatingConfig_hasTwoLeaders kappa tau hn⟩
  refine ⟨hbad, ?_, ?_, ?_⟩
  · exact sweepResetSeparatedBad_every_step_eq ring C hbad
  · intro D hreach
    exact sweepResetSeparatedBad_reachable_eq ring C hbad hreach
  · exact sweepResetSeparatedBad_cannot_reach_isSafe ring hbad

/-- Exact repeating even subfamily `L F` repeated `m` times. -/
theorem sweepReset_even_repeating_counterfamily
    (m kappa tau : Nat) (hm : 2 ≤ m) :
    let n := 2 * m
    let ring : DirectedRing n := ⟨by omega⟩
    let C := paddedAlternatingConfig n kappa tau
    SweepResetSeparatedBad ring C ∧
      ¬ ∃ D : SweepResetConfig n SeparatedPsi kappa tau,
        PopulationProtocol.Reachable
            (P_partialSweepResetProtocol separatedHPsi kappa tau) ring C D ∧
          PopulationProtocol.IsSafe
            (P_partialSweepResetProtocol separatedHPsi kappa tau)
            ring D isLeaderOutput := by
  dsimp only
  have hmain := sweepReset_paddedAlternating_counterfamily
    (2 * m) kappa tau (by omega)
  exact ⟨hmain.1, hmain.2.2.2⟩

/-- Odd sizes are not excluded: for every `m ≥ 2`, size `2m+1` uses the
same alternating prefix and a final follower to break the wrap collision. -/
theorem sweepReset_odd_padded_counterfamily
    (m kappa tau : Nat) (hm : 2 ≤ m) :
    let n := 2 * m + 1
    let ring : DirectedRing n := ⟨by omega⟩
    let C := paddedAlternatingConfig n kappa tau
    SweepResetSeparatedBad ring C ∧
      ¬ ∃ D : SweepResetConfig n SeparatedPsi kappa tau,
        PopulationProtocol.Reachable
            (P_partialSweepResetProtocol separatedHPsi kappa tau) ring C D ∧
          PopulationProtocol.IsSafe
            (P_partialSweepResetProtocol separatedHPsi kappa tau)
            ring D isLeaderOutput := by
  dsimp only
  have hmain := sweepReset_paddedAlternating_counterfamily
    (2 * m + 1) kappa tau (by omega)
  exact ⟨hmain.1, hmain.2.2.2⟩

end PPartialDynamicSweepResetCounterfamilySol
end PPLLCompleteMultiLeaderCleanup
