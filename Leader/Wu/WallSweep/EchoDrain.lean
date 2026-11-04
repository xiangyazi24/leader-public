import Leader.Wu.WallSweep.ResetSweepSchedule
import Leader.Wu.Safety.NoCheckBirthConditionTwoGeometry

/-!
# Draining arbitrary echoes before the reset sweep

Algorithm 14 moves echoes counterclockwise and consumes every responder echo.
With a persistent leader as the sink, the reverse order of the `n-1` edges
drains arbitrary initial echo/reset bits. One additional leader edge then
recreates an echo-free reset source for the existing clockwise sweep.
-/

namespace PPLLWallSweepEchoDrain

open PPLL PPLLWallSweepRepair PPLLWallSweepSchedule
  PPLLWriteSeqPersistenceRegression PPLLWriteSeqRelocation
  PPLLNoCheckBirthConditionTwoGeometry

/-! ## Local Algorithm-14 facts -/

/-- Every scheduled responder loses its old or newly colliding echo in the
same repaired Algorithm-14 call. -/
theorem suppressSigResetKill_responder_echo_false
    (hψ : ψ > 0) (l r : AgentState ψ) :
    (suppressSigResetKill hψ l r).2.echo = false := by
  simp [suppressSigResetKill, suppressSigStart, suppressSigMoveReset,
    resetKillComparison, clearComparisonSignal, suppressSigTerminal,
    suppressSigEcho, suppressSigFinish]

/-- The leader absorbs any echo generated or moved onto its initiator output. -/
theorem suppressSigResetKill_leader_echo_false
    (hψ : ψ > 0) (l r : AgentState ψ)
    (hl : l.leader = true) :
    (suppressSigResetKill hψ l r).1.echo = false := by
  simp [suppressSigResetKill, suppressSigStart, suppressSigMoveReset,
    resetKillComparison, clearComparisonSignal, suppressSigTerminal,
    suppressSigEcho, suppressSigFinish, hl]

/-- With the responder echo already drained, one leader edge leaves both
echoes false and writes a fresh reset token on the responder. -/
theorem suppressSigResetKill_leader_reseed
    (hψ : ψ > 0) (l r : AgentState ψ)
    (hl : l.leader = true) (hrEcho : r.echo = false) :
    let q := suppressSigResetKill hψ l r
    q.1.echo = false ∧ q.2.echo = false ∧ q.2.reset_cmd = true := by
  simp [suppressSigResetKill, suppressSigStart, suppressSigMoveReset,
    resetKillComparison, clearComparisonSignal, suppressSigTerminal,
    suppressSigEcho, suppressSigFinish, hl, hrEcho]

/-- Reset/echo processing never changes either endpoint's leader bit. -/
theorem suppressSigResetKill_leaders_eq
    (hψ : ψ > 0) (l r : AgentState ψ) :
    (suppressSigResetKill hψ l r).1.leader = l.leader ∧
      (suppressSigResetKill hψ l r).2.leader = r.leader := by
  cases hreset : r.reset_cmd <;>
    simp [suppressSigResetKill, suppressSigStart, suppressSigMoveReset,
      resetKillComparison, clearComparisonSignal, suppressSigTerminal,
      suppressSigEcho, suppressSigFinish, hreset]

/-- One scheduled reset/echo interaction frames every pointwise leader bit. -/
theorem stepConfig_suppressSigResetKill_leader_eq {n ψ : Nat}
    (hψ : ψ > 0) (ring : DirectedRing n)
    (C : Fin n → AgentState ψ) (e k : Fin n) :
    (stepConfig ring (suppressSigResetKill hψ) C e k).leader =
      (C k).leader := by
  let q := suppressSigResetKill hψ (C e) (C (ring.rightNeighbor e))
  have hq := suppressSigResetKill_leaders_eq hψ
    (C e) (C (ring.rightNeighbor e))
  change q.1.leader = (C e).leader ∧
    q.2.leader = (C (ring.rightNeighbor e)).leader at hq
  unfold stepConfig
  dsimp only
  by_cases hke : k = e
  · simp only [hke, if_true]
    change q.1.leader = (C e).leader
    exact hq.1
  · by_cases hkr : k = ring.rightNeighbor e
    · have hneighbor : ring.rightNeighbor e ≠ e := by
        intro hj
        apply hke
        rw [hkr, hj]
      simp only [hkr, hneighbor, if_false, if_true]
      change q.2.leader = (C (ring.rightNeighbor e)).leader
      exact hq.2
    · simp [hke, hkr]

/-! ## Reverse echo drain -/

/-- The first `steps` edges in reverse order, beginning with offset `n-2` and
ending at the leader edge when `steps = n-1`. -/
def echoDrainSchedule {n : Nat} (ring : DirectedRing n)
    (leader : Fin n) : Nat → DetSchedule n
  | 0 => []
  | steps + 1 =>
      echoDrainSchedule ring leader steps ++
        [groupOffset ring leader (n - 2 - steps)]

theorem echoDrainSchedule_length {n : Nat} (ring : DirectedRing n)
    (leader : Fin n) (steps : Nat) :
    (echoDrainSchedule ring leader steps).length = steps := by
  induction steps with
  | zero => rfl
  | succ steps ih =>
      simp [echoDrainSchedule, ih]

theorem resetSweepSchedule_length {n : Nat} (ring : DirectedRing n)
    (start : Fin n) (steps : Nat) :
    (resetSweepSchedule ring start steps).length = steps := by
  induction steps with
  | zero => rfl
  | succ steps ih =>
      simp [resetSweepSchedule, ih]

/-- After `steps` reverse edges, the processed clockwise suffix is echo-free;
the designated leader persists and is echo-free after the final edge. -/
def EchoDrainState {n ψ : Nat} (ring : DirectedRing n)
    (leader : Fin n) (current : Fin n → AgentState ψ)
    (steps : Nat) : Prop :=
  steps ≤ n - 1 ∧
    (current leader).leader = true ∧
    (∀ k, n - 1 - steps < k → k < n →
      (current (groupOffset ring leader k)).echo = false) ∧
    (steps = n - 1 → (current leader).echo = false)

theorem echoDrainState_zero {n ψ : Nat} (ring : DirectedRing n)
    (hn : 1 < n) (leader : Fin n) (C : Fin n → AgentState ψ)
    (hleader : (C leader).leader = true) :
    EchoDrainState ring leader C 0 := by
  refine ⟨by omega, hleader, ?_, ?_⟩
  · intro k hk hkn
    omega
  · intro h
    omega

/-- One additional reverse edge clears the next responder; all later offsets
stay clear, and the final leader edge absorbs the last echo. -/
theorem EchoDrainState.step {n ψ steps : Nat} (hψ : ψ > 0)
    (ring : DirectedRing n) (hn : 1 < n) (leader : Fin n)
    (current : Fin n → AgentState ψ)
    (hstate : EchoDrainState ring leader current steps)
    (hnext : steps + 1 ≤ n - 1) :
    let D := stepConfig ring (suppressSigResetKill hψ) current
      (groupOffset ring leader (n - 2 - steps))
    EchoDrainState ring leader D (steps + 1) := by
  let eOffset := n - 2 - steps
  let jOffset := n - 1 - steps
  have heBound : eOffset < n := by omega
  have hjBound : jOffset < n := by omega
  have hsucc : eOffset + 1 = jOffset := by omega
  let e := groupOffset ring leader eOffset
  let j := groupOffset ring leader jOffset
  have hneighbor : ring.rightNeighbor e = j := by
    rw [show e = groupOffset ring leader eOffset by rfl,
      rightNeighbor_groupOffset, hsucc]
  have hene : e ≠ j := by
    apply groupOffset_ne_of_lt ring leader heBound hjBound
    omega
  let q := suppressSigResetKill hψ (current e) (current j)
  have hrightEcho : q.2.echo = false :=
    suppressSigResetKill_responder_echo_false hψ (current e) (current j)
  let D := stepConfig ring (suppressSigResetKill hψ) current e
  have hje : j ≠ e := Ne.symm hene
  have hleft : D e = q.1 := by
    simp [D, q, stepConfig, hneighbor]
  have hright : D j = q.2 := by
    simp [D, q, stepConfig, hneighbor, hje]
  change EchoDrainState ring leader D (steps + 1)
  refine ⟨hnext, ?_, ?_, ?_⟩
  · rw [stepConfig_suppressSigResetKill_leader_eq]
    exact hstate.2.1
  · intro k hkLower hkBound
    by_cases hkNew : k = jOffset
    · subst k
      rw [hright]
      exact hrightEcho
    · have hkOld : n - 1 - steps < k := by omega
      have hke : groupOffset ring leader k ≠ e := by
        apply groupOffset_ne_of_lt ring leader hkBound heBound
        omega
      have hkj : groupOffset ring leader k ≠ j := by
        apply groupOffset_ne_of_lt ring leader hkBound hjBound hkNew
      have hsame := stepConfig_eq_of_ne ring
        (suppressSigResetKill hψ) current e
        (groupOffset ring leader k) hke
        (by simpa [hneighbor] using hkj)
      change D (groupOffset ring leader k) =
        current (groupOffset ring leader k) at hsame
      rw [hsame]
      exact hstate.2.2.1 k hkOld hkBound
  · intro hdone
    have heZero : eOffset = 0 := by omega
    have heLeader : e = leader := by
      apply Fin.ext
      simp [e, eOffset, heZero, groupOffset,
        Nat.mod_eq_of_lt leader.isLt]
    have hinputLeader : (current e).leader = true := by
      rw [heLeader]
      exact hstate.2.1
    rw [← heLeader, hleft]
    exact suppressSigResetKill_leader_echo_false hψ
      (current e) (current j) hinputLeader

/-- Every prefix of the reverse schedule satisfies the suffix-drain invariant. -/
theorem echoDrainSchedule_reaches {n ψ steps : Nat} (hψ : ψ > 0)
    (ring : DirectedRing n) (hn : 1 < n) (leader : Fin n)
    (C : Fin n → AgentState ψ) (hleader : (C leader).leader = true)
    (hsteps : steps ≤ n - 1) :
    let D := applySchedule ring (suppressSigResetKill hψ) C
      (echoDrainSchedule ring leader steps)
    EchoDrainState ring leader D steps := by
  induction steps with
  | zero => exact echoDrainState_zero ring hn leader C hleader
  | succ steps ih =>
      have hprev : steps ≤ n - 1 := by omega
      have hstate := ih hprev
      let C₁ := applySchedule ring (suppressSigResetKill hψ) C
        (echoDrainSchedule ring leader steps)
      change EchoDrainState ring leader C₁ steps at hstate
      have hnext := EchoDrainState.step hψ ring hn leader C₁ hstate hsteps
      rw [echoDrainSchedule, applySchedule_append]
      simpa [applySchedule, C₁] using hnext

/-- The full reverse schedule clears every echo from arbitrary initial echo
and reset bits while preserving the designated leader. -/
theorem echoDrainSchedule_clears_all {n ψ : Nat} (hψ : ψ > 0)
    (ring : DirectedRing n) (hn : 1 < n) (leader : Fin n)
    (C : Fin n → AgentState ψ) (hleader : (C leader).leader = true) :
    let D := applySchedule ring (suppressSigResetKill hψ) C
      (echoDrainSchedule ring leader (n - 1))
    (∀ i, (D i).echo = false) ∧ (D leader).leader = true := by
  have hstate := echoDrainSchedule_reaches hψ ring hn leader C hleader
    (steps := n - 1) (by omega)
  let D := applySchedule ring (suppressSigResetKill hψ) C
    (echoDrainSchedule ring leader (n - 1))
  change EchoDrainState ring leader D (n - 1) at hstate
  constructor
  · intro i
    let k := cwDist ring leader i
    have hkBound : k < n := cwDist_lt ring leader i
    have hpos : groupOffset ring leader k = i := by
      simpa [groupOffset, cwPos] using cwPos_cwDist ring leader i
    rw [← hpos]
    by_cases hkZero : k = 0
    · rw [hkZero]
      change (D (groupOffset ring leader 0)).echo = false
      rw [show groupOffset ring leader 0 = leader by
        apply Fin.ext
        simp [groupOffset, Nat.mod_eq_of_lt leader.isLt]]
      exact hstate.2.2.2 rfl
    · exact hstate.2.2.1 k (by omega) hkBound
  · exact hstate.2.1

/-! ## Leader reseed -/

def leaderReseedSchedule {n : Nat} (ring : DirectedRing n)
    (leader : Fin n) : DetSchedule n :=
  echoDrainSchedule ring leader (n - 1) ++ [leader]

/-- Reverse drain followed by one leader edge establishes the exact premises
of the clockwise reset sweep from arbitrary initial echo/reset bits. -/
theorem leaderReseedSchedule_echo_free_with_reset {n ψ : Nat}
    (hψ : ψ > 0) (ring : DirectedRing n) (hn : 1 < n)
    (leader : Fin n) (C : Fin n → AgentState ψ)
    (hleader : (C leader).leader = true) :
    let D := applySchedule ring (suppressSigResetKill hψ) C
      (leaderReseedSchedule ring leader)
    (∀ i, (D i).echo = false) ∧
      (D (ring.rightNeighbor leader)).reset_cmd = true ∧
      (D leader).leader = true := by
  let drained := applySchedule ring (suppressSigResetKill hψ) C
    (echoDrainSchedule ring leader (n - 1))
  have hdrain := echoDrainSchedule_clears_all hψ ring hn leader C hleader
  change (∀ i, (drained i).echo = false) ∧
    (drained leader).leader = true at hdrain
  let q := suppressSigResetKill hψ
    (drained leader) (drained (ring.rightNeighbor leader))
  have hlocal := suppressSigResetKill_leader_reseed hψ
    (drained leader) (drained (ring.rightNeighbor leader))
    hdrain.2 (hdrain.1 (ring.rightNeighbor leader))
  let D := stepConfig ring (suppressSigResetKill hψ) drained leader
  have hne := rightNeighbor_ne_self_of_one_lt ring hn leader
  have hleft : D leader = q.1 := by
    simp [D, q, stepConfig]
  have hright : D (ring.rightNeighbor leader) = q.2 := by
    simp [D, q, stepConfig, hne]
  rw [leaderReseedSchedule, applySchedule_append]
  simp only [applySchedule]
  change (∀ i, (D i).echo = false) ∧
    (D (ring.rightNeighbor leader)).reset_cmd = true ∧
      (D leader).leader = true
  refine ⟨?_, ?_, ?_⟩
  · intro i
    by_cases hil : i = leader
    · subst i
      rw [hleft]
      exact hlocal.1
    · by_cases hir : i = ring.rightNeighbor leader
      · subst i
        rw [hright]
        exact hlocal.2.1
      · have hsame := stepConfig_eq_of_ne ring
          (suppressSigResetKill hψ) drained leader i hil hir
        change D i = drained i at hsame
        rw [hsame]
        exact hdrain.1 i
  · rw [hright]
    exact hlocal.2.2
  · rw [stepConfig_suppressSigResetKill_leader_eq]
    exact hdrain.2

/-! ## Complete drain/reseed/cleanup word -/

def leaderDrainReseedResetSweep {n : Nat} (ring : DirectedRing n)
    (leader : Fin n) : DetSchedule n :=
  leaderReseedSchedule ring leader ++
    resetSweepSchedule ring (ring.rightNeighbor leader) (n - 1)

/-- Exact deterministic length of the complete cleanup word. -/
theorem leaderDrainReseedResetSweep_length {n : Nat}
    (ring : DirectedRing n) (leader : Fin n) :
    (leaderDrainReseedResetSweep ring leader).length = 2 * n - 1 := by
  simp [leaderDrainReseedResetSweep, leaderReseedSchedule,
    echoDrainSchedule_length, resetSweepSchedule_length]
  have hn : 0 < n := ring.hn
  omega

/-- From arbitrary initial echo/reset bits, one persistent leader supplies a
`2n-1`-edge word that clears every comparison carrier. -/
theorem leaderDrainReseedResetSweep_clears_all {n ψ : Nat}
    (hψ : ψ > 0) (ring : DirectedRing n) (hn : 1 < n)
    (leader : Fin n) (C : Fin n → AgentState ψ)
    (hleader : (C leader).leader = true) :
    let D := applySchedule ring (suppressSigResetKill hψ) C
      (leaderDrainReseedResetSweep ring leader)
    ∀ k, k < n →
      ComparisonNeutral
        (D (groupOffset ring (ring.rightNeighbor leader) k)) := by
  let seeded := applySchedule ring (suppressSigResetKill hψ) C
    (leaderReseedSchedule ring leader)
  have hseed := leaderReseedSchedule_echo_free_with_reset
    hψ ring hn leader C hleader
  change (∀ i, (seeded i).echo = false) ∧
    (seeded (ring.rightNeighbor leader)).reset_cmd = true ∧
      (seeded leader).leader = true at hseed
  have hclear := resetSweepSchedule_clears_all hψ ring hn
    (ring.rightNeighbor leader) seeded hseed.2.1 hseed.1
  rw [leaderDrainReseedResetSweep, applySchedule_append]
  exact hclear

end PPLLWallSweepEchoDrain
