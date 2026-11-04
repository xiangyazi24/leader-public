import Leader.Wu.WallSweep.History
import Leader.Wu.WallSweep.ResetSweepSchedule
import Leader.Wu.WallSweep.EchoDrain

/-!
# Reset-sweep entry for proof-only comparison history

The physical reset schedule already clears every comparison carrier under its
explicit no-echo premise.  This refinement runs the same edges with the marked
reset stage and proves that arbitrary incoming comparison histories become
`FullLocalHistoryTrusted`.  The marks remain proof-only and erase to the
factor-one physical transition.
-/

namespace PPLLWallSweepHistorySchedule

open PPLL PPLLComparisonHistory PPLLWallSweepRepair
  PPLLWallSweepSchedule PPLLWallSweepHistory
  PPLLWallSweepEchoDrain
  PPLLWriteSeqPersistenceRegression PPLLWriteSeqRelocation

/-- One scheduled interaction on the proof-refined marked carrier. -/
def markedStepConfig {n ψ : Nat} (ring : DirectedRing n)
    (T : MarkedAgentState n ψ → MarkedAgentState n ψ →
      MarkedAgentState n ψ × MarkedAgentState n ψ)
    (C : Fin n → MarkedAgentState n ψ) (e : Fin n) :
    Fin n → MarkedAgentState n ψ :=
  let j := ring.rightNeighbor e
  let q := T (C e) (C j)
  fun k => if k = e then q.1 else if k = j then q.2 else C k

/-- Execute a deterministic schedule on marked states. -/
def markedApplySchedule {n ψ : Nat} (ring : DirectedRing n)
    (T : MarkedAgentState n ψ → MarkedAgentState n ψ →
      MarkedAgentState n ψ × MarkedAgentState n ψ)
    (C : Fin n → MarkedAgentState n ψ) :
    DetSchedule n → Fin n → MarkedAgentState n ψ
  | [] => C
  | e :: rest => markedApplySchedule ring T
      (markedStepConfig ring T C e) rest

/-- Forget proof-only source marks pointwise. -/
def eraseMarkedConfig (C : Fin n → MarkedAgentState n ψ) :
    Fin n → AgentState ψ := fun i => (C i).concrete

/-- One marked reset interaction erases to the repaired physical reset
interaction on the same scheduled edge. -/
theorem erase_markedResetStepConfig {n ψ : Nat} (hψ : ψ > 0)
    (ring : DirectedRing n) (C : Fin n → MarkedAgentState n ψ)
    (e : Fin n) :
    eraseMarkedConfig
        (markedStepConfig ring (markedSuppressSigResetKill hψ) C e) =
      stepConfig ring (suppressSigResetKill hψ) (eraseMarkedConfig C) e := by
  let markedOut := markedSuppressSigResetKill hψ
    (C e) (C (ring.rightNeighbor e))
  let out := suppressSigResetKill hψ
    (C e).concrete (C (ring.rightNeighbor e)).concrete
  have herase := erase_markedSuppressSigResetKill hψ
    (C e) (C (ring.rightNeighbor e))
  change (markedOut.1.concrete, markedOut.2.concrete) = out at herase
  have hleft : markedOut.1.concrete = out.1 := by
    simpa using congrArg Prod.fst herase
  have hright : markedOut.2.concrete = out.2 := by
    simpa using congrArg Prod.snd herase
  funext k
  unfold eraseMarkedConfig markedStepConfig stepConfig
  dsimp only
  by_cases hke : k = e
  · simp only [hke, if_true]
    change markedOut.1.concrete = out.1
    exact hleft
  · by_cases hkr : k = ring.rightNeighbor e
    · have hneighbor : ring.rightNeighbor e ≠ e := by
        intro hj
        apply hke
        rw [hkr, hj]
      simp only [hkr, hneighbor, if_false, if_true]
      change markedOut.2.concrete = out.2
      exact hright
    · simp [hke, hkr]

/-- Exact erasure extends to every finite reset schedule. -/
theorem erase_markedResetApplySchedule {n ψ : Nat} (hψ : ψ > 0)
    (ring : DirectedRing n) (C : Fin n → MarkedAgentState n ψ)
    (schedule : DetSchedule n) :
    eraseMarkedConfig
        (markedApplySchedule ring (markedSuppressSigResetKill hψ) C schedule) =
      applySchedule ring (suppressSigResetKill hψ)
        (eraseMarkedConfig C) schedule := by
  induction schedule generalizing C with
  | nil => rfl
  | cons e rest ih =>
      simp only [markedApplySchedule, applySchedule]
      rw [ih, erase_markedResetStepConfig]

theorem markedStepConfig_eq_of_ne {n ψ : Nat}
    (ring : DirectedRing n)
    (T : MarkedAgentState n ψ → MarkedAgentState n ψ →
      MarkedAgentState n ψ × MarkedAgentState n ψ)
    (C : Fin n → MarkedAgentState n ψ) (e i : Fin n)
    (hleft : i ≠ e) (hright : i ≠ ring.rightNeighbor e) :
    markedStepConfig ring T C e i = C i := by
  simp [markedStepConfig, hleft, hright]

theorem markedApplySchedule_append {n ψ : Nat}
    (ring : DirectedRing n)
    (T : MarkedAgentState n ψ → MarkedAgentState n ψ →
      MarkedAgentState n ψ × MarkedAgentState n ψ)
    (C : Fin n → MarkedAgentState n ψ) (first second : DetSchedule n) :
    markedApplySchedule ring T C (first ++ second) =
      markedApplySchedule ring T (markedApplySchedule ring T C first) second := by
  induction first generalizing C with
  | nil => rfl
  | cons e rest ih =>
      simp only [List.cons_append, markedApplySchedule]
      exact ih (markedStepConfig ring T C e)

/-- After `steps` marked reset handoffs, the token host and every visited
offset have trusted local comparison history; offsets ahead are unchanged. -/
def MarkedResetSweepState {n ψ : Nat} (ring : DirectedRing n)
    (start : Fin n) (initial current : Fin n → MarkedAgentState n ψ)
    (steps : Nat) : Prop :=
  steps < n ∧
    (current (groupOffset ring start steps)).concrete.reset_cmd = true ∧
    FullLocalHistoryTrusted
      (current (groupOffset ring start steps)).concrete
      (current (groupOffset ring start steps)).history ∧
    (∀ k, k < steps →
      FullLocalHistoryTrusted
        (current (groupOffset ring start k)).concrete
        (current (groupOffset ring start k)).history) ∧
    (∀ k, steps < k → k < n →
      current (groupOffset ring start k) =
        initial (groupOffset ring start k))

/-- One more clockwise edge advances the marked reset invariant without any
trust premise on the newly visited endpoint. -/
theorem MarkedResetSweepState.step {n ψ steps : Nat} (hψ : ψ > 0)
    (ring : DirectedRing n) (_hn : 1 < n) (start : Fin n)
    (initial current : Fin n → MarkedAgentState n ψ)
    (hstate : MarkedResetSweepState ring start initial current steps)
    (hnext : steps + 1 < n)
    (hecho : ∀ i, (initial i).concrete.echo = false) :
    let D := markedStepConfig ring (markedSuppressSigResetKill hψ) current
      (groupOffset ring start steps)
    MarkedResetSweepState ring start initial D (steps + 1) := by
  let e := groupOffset ring start steps
  let j := groupOffset ring start (steps + 1)
  have hneighbor : ring.rightNeighbor e = j := by
    exact rightNeighbor_groupOffset ring start steps
  have hene : e ≠ j := by
    apply groupOffset_ne_of_lt ring start
    · exact hstate.1
    · exact hnext
    · omega
  have hjUntouched := hstate.2.2.2.2 (steps + 1) (by omega) hnext
  have hjEcho : (current j).concrete.echo = false := by
    rw [hjUntouched]
    exact hecho j
  have hlocal := markedSuppressSigResetKill_handoff_rehabilitates hψ
    (current e) (current j) hstate.2.1 hjEcho
  let q := markedSuppressSigResetKill hψ (current e) (current j)
  change FullLocalHistoryTrusted q.1.concrete q.1.history ∧
    FullLocalHistoryTrusted q.2.concrete q.2.history ∧
      q.1.concrete.reset_cmd = false ∧
      q.2.concrete.reset_cmd = true at hlocal
  let D := markedStepConfig ring (markedSuppressSigResetKill hψ) current e
  have hje : j ≠ e := Ne.symm hene
  have hleft : D e = q.1 := by
    simp [D, q, markedStepConfig, hneighbor]
  have hright : D j = q.2 := by
    simp [D, q, markedStepConfig, hneighbor, hje]
  change MarkedResetSweepState ring start initial D (steps + 1)
  refine ⟨hnext, ?_, ?_, ?_, ?_⟩
  · rw [hright]
    exact hlocal.2.2.2
  · rw [hright]
    exact hlocal.2.1
  · intro k hk
    by_cases hlast : k = steps
    · subst k
      rw [hleft]
      exact hlocal.1
    · have hkOld : k < steps := by omega
      have hke : groupOffset ring start k ≠ e := by
        apply groupOffset_ne_of_lt ring start
        · omega
        · exact hstate.1
        · omega
      have hkj : groupOffset ring start k ≠ j := by
        apply groupOffset_ne_of_lt ring start
        · omega
        · exact hnext
        · omega
      have hsame := markedStepConfig_eq_of_ne ring
        (markedSuppressSigResetKill hψ) current e
        (groupOffset ring start k) hke
        (by simpa [hneighbor] using hkj)
      change D (groupOffset ring start k) =
        current (groupOffset ring start k) at hsame
      rw [hsame]
      exact hstate.2.2.2.1 k hkOld
  · intro k hkAhead hkRange
    have hke : groupOffset ring start k ≠ e := by
      apply groupOffset_ne_of_lt ring start
      · exact hkRange
      · exact hstate.1
      · omega
    have hkj : groupOffset ring start k ≠ j := by
      apply groupOffset_ne_of_lt ring start
      · exact hkRange
      · exact hnext
      · omega
    have hsame := markedStepConfig_eq_of_ne ring
      (markedSuppressSigResetKill hψ) current e
      (groupOffset ring start k) hke
      (by simpa [hneighbor] using hkj)
    change D (groupOffset ring start k) =
      current (groupOffset ring start k) at hsame
    rw [hsame, hstate.2.2.2.2 k (by omega) hkRange]

/-- The first marked handoff establishes trusted history at offsets zero and
one without any premise on their old source marks. -/
theorem markedResetSweepState_one {n ψ : Nat} (hψ : ψ > 0)
    (ring : DirectedRing n) (hn : 1 < n) (start : Fin n)
    (C : Fin n → MarkedAgentState n ψ)
    (hreset : (C start).concrete.reset_cmd = true)
    (hecho : ∀ i, (C i).concrete.echo = false) :
    let D := markedApplySchedule ring (markedSuppressSigResetKill hψ) C
      (resetSweepSchedule ring start 1)
    MarkedResetSweepState ring start C D 1 := by
  let e := groupOffset ring start 0
  let j := groupOffset ring start 1
  have he : e = start := by
    apply Fin.ext
    simp [e, groupOffset, Nat.mod_eq_of_lt start.isLt]
  have hneighbor : ring.rightNeighbor e = j :=
    rightNeighbor_groupOffset ring start 0
  have hene : e ≠ j := by
    apply groupOffset_ne_of_lt ring start <;> omega
  have hlocal := markedSuppressSigResetKill_handoff_rehabilitates hψ
    (C e) (C j) (by simpa [he] using hreset) (hecho j)
  let q := markedSuppressSigResetKill hψ (C e) (C j)
  change FullLocalHistoryTrusted q.1.concrete q.1.history ∧
    FullLocalHistoryTrusted q.2.concrete q.2.history ∧
      q.1.concrete.reset_cmd = false ∧
      q.2.concrete.reset_cmd = true at hlocal
  let D := markedStepConfig ring (markedSuppressSigResetKill hψ) C e
  have hje : j ≠ e := Ne.symm hene
  have hleft : D e = q.1 := by
    simp [D, q, markedStepConfig, hneighbor]
  have hright : D j = q.2 := by
    simp [D, q, markedStepConfig, hneighbor, hje]
  change MarkedResetSweepState ring start C D 1
  refine ⟨by omega, ?_, ?_, ?_, ?_⟩
  · rw [show groupOffset ring start 1 = j by rfl, hright]
    exact hlocal.2.2.2
  · rw [show groupOffset ring start 1 = j by rfl, hright]
    exact hlocal.2.1
  · intro k hk
    have hk0 : k = 0 := by omega
    subst k
    rw [show groupOffset ring start 0 = e by rfl, hleft]
    exact hlocal.1
  · intro k hk hkn
    have hke : groupOffset ring start k ≠ e := by
      apply groupOffset_ne_of_lt ring start <;> omega
    have hkj : groupOffset ring start k ≠ j := by
      apply groupOffset_ne_of_lt ring start <;> omega
    have hsame := markedStepConfig_eq_of_ne ring
      (markedSuppressSigResetKill hψ) C e
      (groupOffset ring start k) hke
      (by simpa [hneighbor] using hkj)
    change D (groupOffset ring start k) = C (groupOffset ring start k) at hsame
    exact hsame

/-- Every positive prefix of the marked reset schedule satisfies the trusted
history invariant. -/
theorem markedResetSweepSchedule_reaches {n ψ steps : Nat}
    (hψ : ψ > 0) (ring : DirectedRing n) (hn : 1 < n)
    (start : Fin n) (C : Fin n → MarkedAgentState n ψ)
    (hsteps : 0 < steps) (hbound : steps < n)
    (hreset : (C start).concrete.reset_cmd = true)
    (hecho : ∀ i, (C i).concrete.echo = false) :
    let D := markedApplySchedule ring (markedSuppressSigResetKill hψ) C
      (resetSweepSchedule ring start steps)
    MarkedResetSweepState ring start C D steps := by
  induction steps with
  | zero => omega
  | succ steps ih =>
      by_cases hzero : steps = 0
      · subst steps
        exact markedResetSweepState_one hψ ring hn start C hreset hecho
      · have hprevBound : steps < n := by omega
        have hprev := ih (by omega) hprevBound
        let C₁ := markedApplySchedule ring (markedSuppressSigResetKill hψ) C
          (resetSweepSchedule ring start steps)
        change MarkedResetSweepState ring start C C₁ steps at hprev
        have hnext := MarkedResetSweepState.step hψ ring hn start C C₁
          hprev (by omega) hecho
        rw [resetSweepSchedule, markedApplySchedule_append]
        simpa [markedApplySchedule, C₁] using hnext

/-- After `n-1` clockwise handoffs, every offset has trusted local comparison
history, even if every incoming proof mark was arbitrary or tainted. -/
theorem markedResetSweepSchedule_rehabilitates_all {n ψ : Nat}
    (hψ : ψ > 0) (ring : DirectedRing n) (hn : 1 < n)
    (start : Fin n) (C : Fin n → MarkedAgentState n ψ)
    (hreset : (C start).concrete.reset_cmd = true)
    (hecho : ∀ i, (C i).concrete.echo = false) :
    let D := markedApplySchedule ring (markedSuppressSigResetKill hψ) C
      (resetSweepSchedule ring start (n - 1))
    ∀ k, k < n →
      FullLocalHistoryTrusted
        (D (groupOffset ring start k)).concrete
        (D (groupOffset ring start k)).history := by
  have hreach := markedResetSweepSchedule_reaches hψ ring hn start C
    (steps := n - 1) (by omega) (by omega) hreset hecho
  let D := markedApplySchedule ring (markedSuppressSigResetKill hψ) C
    (resetSweepSchedule ring start (n - 1))
  change MarkedResetSweepState ring start C D (n - 1) at hreach
  change ∀ k, k < n →
    FullLocalHistoryTrusted
      (D (groupOffset ring start k)).concrete
      (D (groupOffset ring start k)).history
  intro k hk
  by_cases hlast : k = n - 1
  · subst k
    exact hreach.2.2.1
  · exact hreach.2.2.2.1 k (by omega)

/-- Combined cleanup kernel: the marked schedule erases to the existing raw
schedule, and every ring offset ends physically neutral with trusted absent
comparison history. -/
theorem markedResetSweepSchedule_entry {n ψ : Nat}
    (hψ : ψ > 0) (ring : DirectedRing n) (hn : 1 < n)
    (start : Fin n) (C : Fin n → MarkedAgentState n ψ)
    (hreset : (C start).concrete.reset_cmd = true)
    (hecho : ∀ i, (C i).concrete.echo = false) :
    let markedOut := markedApplySchedule ring
      (markedSuppressSigResetKill hψ) C
      (resetSweepSchedule ring start (n - 1))
    let rawOut := applySchedule ring (suppressSigResetKill hψ)
      (eraseMarkedConfig C) (resetSweepSchedule ring start (n - 1))
    eraseMarkedConfig markedOut = rawOut ∧
      ∀ k, k < n →
        ComparisonNeutral (rawOut (groupOffset ring start k)) ∧
        FullLocalHistoryTrusted
          (markedOut (groupOffset ring start k)).concrete
          (markedOut (groupOffset ring start k)).history := by
  let markedOut := markedApplySchedule ring
    (markedSuppressSigResetKill hψ) C
    (resetSweepSchedule ring start (n - 1))
  let rawOut := applySchedule ring (suppressSigResetKill hψ)
    (eraseMarkedConfig C) (resetSweepSchedule ring start (n - 1))
  have herase := erase_markedResetApplySchedule hψ ring C
    (resetSweepSchedule ring start (n - 1))
  change eraseMarkedConfig markedOut = rawOut at herase
  have hneutral := resetSweepSchedule_clears_all hψ ring hn start
    (eraseMarkedConfig C) hreset hecho
  change ∀ k, k < n →
    ComparisonNeutral (rawOut (groupOffset ring start k)) at hneutral
  have htrusted := markedResetSweepSchedule_rehabilitates_all hψ ring hn
    start C hreset hecho
  change ∀ k, k < n →
    FullLocalHistoryTrusted
      (markedOut (groupOffset ring start k)).concrete
      (markedOut (groupOffset ring start k)).history at htrusted
  refine ⟨herase, ?_⟩
  intro k hk
  exact ⟨hneutral k hk, htrusted k hk⟩

/-! ## Arbitrary-echo entry from a persistent leader -/

/-- The `2n-1` drain/reseed/reset word removes arbitrary initial echo/reset
bits, erases exactly to the raw schedule, and enters trusted idle comparison
history from arbitrary old proof marks. -/
theorem markedLeaderDrainReseedResetSweep_entry {n ψ : Nat}
    (hψ : ψ > 0) (ring : DirectedRing n) (hn : 1 < n)
    (leader : Fin n) (R : Fin n → MarkedAgentState n ψ)
    (hleader : (R leader).concrete.leader = true) :
    let markedOut := markedApplySchedule ring
      (markedSuppressSigResetKill hψ) R
      (leaderDrainReseedResetSweep ring leader)
    let rawOut := applySchedule ring (suppressSigResetKill hψ)
      (eraseMarkedConfig R) (leaderDrainReseedResetSweep ring leader)
    eraseMarkedConfig markedOut = rawOut ∧
      ∀ k, k < n →
        ComparisonNeutral
          (rawOut (groupOffset ring (ring.rightNeighbor leader) k)) ∧
        FullLocalHistoryTrusted
          (markedOut
            (groupOffset ring (ring.rightNeighbor leader) k)).concrete
          (markedOut
            (groupOffset ring (ring.rightNeighbor leader) k)).history := by
  let seedSchedule := leaderReseedSchedule ring leader
  let sweepSchedule := resetSweepSchedule ring (ring.rightNeighbor leader) (n - 1)
  let markedSeed := markedApplySchedule ring
    (markedSuppressSigResetKill hψ) R seedSchedule
  let rawSeed := applySchedule ring (suppressSigResetKill hψ)
    (eraseMarkedConfig R) seedSchedule
  have hseedRaw := leaderReseedSchedule_echo_free_with_reset
    hψ ring hn leader (eraseMarkedConfig R) hleader
  change (∀ i, (rawSeed i).echo = false) ∧
    (rawSeed (ring.rightNeighbor leader)).reset_cmd = true ∧
      (rawSeed leader).leader = true at hseedRaw
  have hseedErase := erase_markedResetApplySchedule hψ ring R seedSchedule
  change eraseMarkedConfig markedSeed = rawSeed at hseedErase
  have hseedEcho : ∀ i, (markedSeed i).concrete.echo = false := by
    intro i
    have hi := congrFun hseedErase i
    change (markedSeed i).concrete = rawSeed i at hi
    rw [hi]
    exact hseedRaw.1 i
  have hseedReset :
      (markedSeed (ring.rightNeighbor leader)).concrete.reset_cmd = true := by
    have hi := congrFun hseedErase (ring.rightNeighbor leader)
    change (markedSeed (ring.rightNeighbor leader)).concrete =
      rawSeed (ring.rightNeighbor leader) at hi
    rw [hi]
    exact hseedRaw.2.1
  let markedFinal := markedApplySchedule ring
    (markedSuppressSigResetKill hψ) markedSeed sweepSchedule
  have htrusted := markedResetSweepSchedule_rehabilitates_all hψ ring hn
    (ring.rightNeighbor leader) markedSeed hseedReset hseedEcho
  change ∀ k, k < n →
    FullLocalHistoryTrusted
      (markedFinal
        (groupOffset ring (ring.rightNeighbor leader) k)).concrete
      (markedFinal
        (groupOffset ring (ring.rightNeighbor leader) k)).history at htrusted
  let markedOut := markedApplySchedule ring
    (markedSuppressSigResetKill hψ) R
    (leaderDrainReseedResetSweep ring leader)
  let rawOut := applySchedule ring (suppressSigResetKill hψ)
    (eraseMarkedConfig R) (leaderDrainReseedResetSweep ring leader)
  have hmarked : markedOut = markedFinal := by
    unfold markedOut markedFinal markedSeed seedSchedule sweepSchedule
    rw [leaderDrainReseedResetSweep, markedApplySchedule_append]
  have herase := erase_markedResetApplySchedule hψ ring R
    (leaderDrainReseedResetSweep ring leader)
  change eraseMarkedConfig markedOut = rawOut at herase
  have hneutral := leaderDrainReseedResetSweep_clears_all
    hψ ring hn leader (eraseMarkedConfig R) hleader
  change ∀ k, k < n → ComparisonNeutral
    (rawOut (groupOffset ring (ring.rightNeighbor leader) k)) at hneutral
  refine ⟨herase, ?_⟩
  intro k hk
  refine ⟨hneutral k hk, ?_⟩
  change FullLocalHistoryTrusted
    (markedOut (groupOffset ring (ring.rightNeighbor leader) k)).concrete
    (markedOut (groupOffset ring (ring.rightNeighbor leader) k)).history
  rw [hmarked]
  exact htrusted k hk

end PPLLWallSweepHistorySchedule
