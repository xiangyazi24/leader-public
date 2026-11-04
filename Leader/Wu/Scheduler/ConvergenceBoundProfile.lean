import Leader.Wu.Safety.ConvergencePhasePredicates
import Leader.Wu.Safety.ConditionalClosedness
import Leader.Wu.Scheduler.CitedBoundProfiles
import Leader.Core.ModArith

/-!
# Proposed Bound Profile for Theorem 4.1.13

This module is **not a proof of probabilistic convergence**. It transcribes the
paper's phase pre/postconditions and claimed bounds into `ReachSpec` metadata,
then proves arithmetic facts about those stored numbers. `ReachSpec` has no
execution or probability semantics, and several raw phase profiles are built
without protocol-dynamics proofs.

The concrete protocol also has no `ProtocolProperties` instance. Accordingly,
none of the profiles below may be cited as a proof that P_PLL converges.

## Proof structure

The convergence chain is NOT a simple sequential composition — it is a DAG:

Phase 1: any → C_clean (4.1.2, O(n²))
Phase 2: → leader exists (4.1.4, O(n² log n))
Phase 3: → no non-peaceful bullet (4.1.5, O(n² log n), uses 4.1.2 + 4.1.4)
Phase 4: → suppressed (4.1.7, O(n²))
Phase 5: → no signal (4.1.8, O(n² log n))
Phase 6: → barriers safe (4.1.9, O(n²))
Phase 7: → unique leader (4.1.10, O(n² log n))
Phase 8: → stable ID (4.1.11, O(n² log n log log n))
Phase 9: → no free OW signal (4.1.12, O(n² log n log log n))
Phase 10: → quiescent (O(n²))

Critical subtlety for any future proof: each phase's postcondition must persist
through subsequent phases. The current abstract preservation theorem concerns
only `QuiescentSafeConfig` under a class that concrete P_PLL does not satisfy.
-/

/-! ## Phase profiles

Each phase is stored as a `ReachSpec`. Some profiles calculate their deterministic
schedule length from a `TraversalMetric`; this still does not supply the missing
random-scheduler lifting. Other profiles below simply transcribe formulas. -/

/-- **Lemma 4.1.2**: From any configuration, all bullets become peaceful
within O(n²) steps w.h.p. Each of ≤ n bullets traverses the ring (length n);
all advance simultaneously in the random scheduler. The O(n²) bound uses
parallel Chernoff: in c·n² steps, each edge fires c·n times, sufficient
for every bullet to complete its traversal. -/
def phase_cleaning
    {ψ n : Nat} (hψ : ψ > 0) (ring : DirectedRing n)
    (T : AgentState ψ → AgentState ψ → AgentState ψ × AgentState ψ)
    [_PP : ProtocolProperties ψ hψ n ring T]
    (c : Nat) (_hc : c ≥ 1) : ReachSpec ring T :=
  { Pre := fun _ => True
    Post := fun C => isClean hψ ring C
    steps := fun n => c * n * (n + log2' n)
    failProb := fun n => (1 : Rat) / (n ^ c : Nat) }

/-- **Lemma 4.1.4**: If no leader exists, one is created within O(n² log n)
steps w.h.p. If a leader already exists, this is trivially satisfied. -/
def phase_leader_creation
    {ψ n : Nat} (hψ : ψ > 0) (ring : DirectedRing n)
    (T : AgentState ψ → AgentState ψ → AgentState ψ × AgentState ψ)
    [_PP : ProtocolProperties ψ hψ n ring T]
    (c : Nat) (_hc : c ≥ 1) : ReachSpec ring T :=
  { Pre := fun _ => True
    Post := fun C => hasLeader n C
    steps := fun n => c * n * n * log2' n
    failProb := fun n => (1 : Rat) / (n ^ c : Nat) }

/-- **Lemma 4.1.5**: From C_clean with a leader, no non-peaceful bullet
after O(n² log n) steps w.h.p. -/
def phase_peaceful_bullets
    {ψ n : Nat} (hψ : ψ > 0) (ring : DirectedRing n)
    (T : AgentState ψ → AgentState ψ → AgentState ψ × AgentState ψ)
    [_PP : ProtocolProperties ψ hψ n ring T]
    (c : Nat) (_hc : c ≥ 1) : ReachSpec ring T :=
  { Pre := fun C => isClean hψ ring C ∧ hasLeader n C
    Post := fun C => noNonPeacefulBullet hψ ring C
    steps := fun n => c * n * n * log2' n
    failProb := fun n => (1 : Rat) / (n ^ c : Nat) }

/-- **Lemma 4.1.7**: Suppressed within O(n²) steps w.h.p. Reset signal
traverses the ring (length n). A single signal traverses, so k = 1.

Structurally: `reach_profile_from_traversal` with k = 1 object. -/
def phase_suppression
    {ψ n : Nat} (hψ : ψ > 0) (ring : DirectedRing n)
    (T : AgentState ψ → AgentState ψ → AgentState ψ × AgentState ψ)
    [_PP : ProtocolProperties ψ hψ n ring T]
    {α : Type}
    (M : TraversalMetric ψ n ring T α)
    (signal : (Fin n → AgentState ψ) → List α)
    (hk : ∀ C, hasLeader n C → (signal C).length ≤ 1)
    (hgoal : ∀ C s, hasLeader n C →
      (∀ obj, obj ∈ signal C → M.goal (applySchedule ring T C s) obj) →
      isSuppressed ring (applySchedule ring T C s))
    (c : Nat) (hc : c ≥ 1) : ReachSpec ring T :=
  reach_profile_from_traversal ring T M (hasLeader n) (isSuppressed ring)
    signal 1 hk (fun C s h g => hgoal C s h g) c hc

/-- **Lemma 4.1.8**: No active signal after O(n² log n) steps from suppression
w.h.p. The lottery game (Lemma 4.1.6) has O(log n) rounds, each requiring
O(n²) random steps for all edges to fire sufficiently. -/
def phase_no_signal
    {ψ n : Nat} (hψ : ψ > 0) (ring : DirectedRing n)
    (T : AgentState ψ → AgentState ψ → AgentState ψ × AgentState ψ)
    [_PP : ProtocolProperties ψ hψ n ring T]
    (c : Nat) (_hc : c ≥ 1) : ReachSpec ring T :=
  { Pre := fun C => isSuppressed ring C
    Post := fun C => noActiveSignal ring C
    steps := fun n => c * n * n * log2' n
    failProb := fun n => (1 : Rat) / (n ^ c : Nat) }

/-- **Lemma 4.1.9**: All free barriers safe within O(n²) steps w.h.p.
Each barrier traverses the ring until meeting a leader/probe.
The O(n²) bound uses parallel Chernoff (all barriers advance simultaneously
in the random scheduler), not sequential Yokota lifting. -/
def phase_barriers_safe
    {ψ n : Nat} (hψ : ψ > 0) (ring : DirectedRing n)
    (T : AgentState ψ → AgentState ψ → AgentState ψ × AgentState ψ)
    [_PP : ProtocolProperties ψ hψ n ring T]
    (c : Nat) (_hc : c ≥ 1) : ReachSpec ring T :=
  { Pre := fun C => hasLeader n C
    Post := fun C => noFreeBarrier hψ ring C
    steps := fun n => c * n * (n + log2' n)
    failProb := fun n => (1 : Rat) / (n ^ c : Nat) }

/-- **Lemma 4.1.10**: Unique leader within O(n² log n) steps w.h.p.
Uses Yokota [31] leader elimination with 4× self-stabilization slowdown.
Structurally derived from `yokota_leader_elimination_profile`. -/
def phase_unique_leader
    {ψ n : Nat} (hψ : ψ > 0) (ring : DirectedRing n)
    (T : AgentState ψ → AgentState ψ → AgentState ψ × AgentState ψ)
    [_PP : ProtocolProperties ψ hψ n ring T]
    (c : Nat) (hc : c ≥ 1) : ReachSpec ring T :=
  yokota_leader_elimination_profile hψ ring T c hc

/-- **Lemma 4.1.11**: Stable ID sequence within O(n² log n log log n)
steps w.h.p. The overwriting signal makes log n rounds, each taking
O(n² · ψ) = O(n² log log n) steps. -/
def phase_stable_id
    {ψ n : Nat} (hψ : ψ > 0) (ring : DirectedRing n)
    (T : AgentState ψ → AgentState ψ → AgentState ψ × AgentState ψ)
    [_PP : ProtocolProperties ψ hψ n ring T]
    (c : Nat) (_hc : c ≥ 1) : ReachSpec ring T :=
  { Pre := fun C => hasUniqueLeader n C
    Post := fun C => isStableIDSequence hψ ring C
    steps := fun n => c * n * n * log2' n * (log2' (log2' n) + 1)
    failProb := fun n => (1 : Rat) / (n ^ c : Nat) }

/-- **Lemma 4.1.12**: No free overwriting signal after O(n² log n log log n)
steps w.h.p. -/
def phase_no_ow_signal
    {ψ n : Nat} (hψ : ψ > 0) (ring : DirectedRing n)
    (T : AgentState ψ → AgentState ψ → AgentState ψ × AgentState ψ)
    [_PP : ProtocolProperties ψ hψ n ring T]
    (c : Nat) (_hc : c ≥ 1) : ReachSpec ring T :=
  { Pre := fun C => isStableIDSequence hψ ring C ∧ hasUniqueLeader n C
    Post := fun C => noFreeOverwritingSignal hψ ring C
    steps := fun n => c * n * n * log2' n * (log2' (log2' n) + 1)
    failProb := fun n => (1 : Rat) / (n ^ c : Nat) }

/-- **Phase 10**: Quiescence within O(n²) steps w.h.p. After the ID
sequence is stable and all overwriting signals are gone, the comparison
protocol settles: all agents reach state=.none and gen_ws=false.
Each agent's state is reset in one ring traversal (O(n) det schedule),
lifted to O(n²) random steps by Yokota's formula. -/
def phase_quiescence
    {ψ n : Nat} (hψ : ψ > 0) (ring : DirectedRing n)
    (T : AgentState ψ → AgentState ψ → AgentState ψ × AgentState ψ)
    [_PP : ProtocolProperties ψ hψ n ring T]
    (c : Nat) (_hc : c ≥ 1) : ReachSpec ring T :=
  { Pre := fun C => isStableIDSequence hψ ring C ∧ noFreeOverwritingSignal hψ ring C
    Post := fun C => isQuiescent ring C
    steps := fun n => c * n * (n + log2' n)
    failProb := fun n => (1 : Rat) / (n ^ c : Nat) }

/-! ## Conditions → historical QuiescentSafeConfig

The old quiescent scaffolding uses the per-agent `noActiveWriteAction`
approximation, not Wu's global free-overwriting-signal predicate. Therefore the
phase-9 paper predicate does not by itself construct this structure. -/

/-- Logical constructor from the six explicitly stated conditions. This is not
a theorem that the ten proposed phase profiles establish them. -/
theorem conditions_imply_quiescent_safe
    {ψ n : Nat} (hψ : ψ > 0) (ring : DirectedRing n)
    (C : Fin n → AgentState ψ)
    (_h3 : noNonPeacefulBullet hψ ring C)
    (_h6 : noFreeBarrier hψ ring C)
    (_h7 : hasUniqueLeader n C)
    (_h8 : isStableIDSequence hψ ring C)
    (_h9 : noActiveWriteAction ring C)
    (_h10 : isQuiescent ring C) :
    QuiescentSafeConfig hψ ring C :=
  quiescentSafe_of_conditions hψ ring C _h7 _h3 _h6 _h9 _h8 _h10

/-! ## Phase composition via ReachSpec.seq

The convergence chain has a DAG structure: each phase's postcondition
depends on prior phases. Full structural composition via `ReachSpec.then`
would require monotonicity proofs (each intermediate predicate is
preserved through subsequent phases). Without monotonicity, `ReachSpec.seq`
gives partial composition — the Post is only the LAST phase's postcondition.

Below are compositional lemmas for the sub-chains where Pre/Post
compatibility is trivially provable. -/

/-- **Monotonicity**: isSuppressed is Preserved under any interaction.
Derived from `reset_cmd_stable`: once all agents have reset_cmd = true,
the flag is permanent — no interaction clears it. -/
theorem suppressed_preserved
    {ψ n : Nat} (hψ : ψ > 0) (ring : DirectedRing n)
    (T : AgentState ψ → AgentState ψ → AgentState ψ × AgentState ψ)
    [PP : ProtocolProperties ψ hψ n ring T] :
    Preserved ring T (isSuppressed ring) := by
  intro C hC e; dsimp only
  have hrc := PP.reset_cmd_stable (C e) (C (ring.rightNeighbor e))
    (hC e) (hC (ring.rightNeighbor e))
  intro k
  by_cases h1 : k = e
  · simp only [if_pos h1]; exact hrc.1
  · by_cases h2 : k = ring.rightNeighbor e
    · simp only [if_neg h1, if_pos h2]; exact hrc.2
    · simp only [if_neg h1, if_neg h2]; exact hC k

/-- **Monotonicity**: noActiveSignal is PreservedUnder isSuppressed.
Once all agents are suppressed, no new signal_B is created. Derived
from `suppressed_no_new_signal`. -/
theorem noActiveSignal_preserved_under_suppressed
    {ψ n : Nat} (hψ : ψ > 0) (ring : DirectedRing n)
    (T : AgentState ψ → AgentState ψ → AgentState ψ × AgentState ψ)
    [PP : ProtocolProperties ψ hψ n ring T] :
    PreservedUnder ring T (isSuppressed ring) (noActiveSignal ring) := by
  intro C hS hN e; dsimp only
  have ⟨h1, h2⟩ := PP.suppressed_no_new_signal (C e) (C (ring.rightNeighbor e))
    (hS e) (hS (ring.rightNeighbor e)) (hN e) (hN (ring.rightNeighbor e))
  intro k
  by_cases hk1 : k = e
  · simp only [if_pos hk1]; exact h1
  · by_cases hk2 : k = ring.rightNeighbor e
    · simp only [if_neg hk1, if_pos hk2]; exact h2
    · simp only [if_neg hk1, if_neg hk2]; exact hN k

/-- **Monotonicity**: the conjunction isSuppressed ∧ noActiveSignal is
unconditionally Preserved. Combines `suppressed_preserved` (isSuppressed
is Preserved) with `noActiveSignal_preserved_under_suppressed` (noActiveSignal
is PreservedUnder isSuppressed). -/
theorem suppressed_and_nosignal_preserved
    {ψ n : Nat} (hψ : ψ > 0) (ring : DirectedRing n)
    (T : AgentState ψ → AgentState ψ → AgentState ψ × AgentState ψ)
    [PP : ProtocolProperties ψ hψ n ring T] :
    Preserved ring T (fun C => isSuppressed ring C ∧ noActiveSignal ring C) := by
  intro C ⟨hS, hN⟩ e
  exact ⟨suppressed_preserved hψ ring T C hS e,
         noActiveSignal_preserved_under_suppressed hψ ring T C hS hN e⟩

/-- **Monotonicity**: hasUniqueLeader is PreservedUnder the conjunction
(isSuppressed ∧ noNonPeacefulBullet ∧ noFreeBarrier). No new leaders are
created because barrier-probe creation is blocked by noFreeBarrier and
comparison creation is blocked by suppressed_blocks_comparison_leader.
The existing leader is protected by the shield argument: any bullet(2)
at a neighbor has a shielded leader ahead (noNonPeacefulBullet), and by
uniqueness that leader is the one being attacked — contradicting the
unshielded hypothesis from leader_initiator_stable. -/
theorem hasUniqueLeader_preserved_under_conditions
    {ψ n : Nat} (hψ : ψ > 0) (ring : DirectedRing n)
    (T : AgentState ψ → AgentState ψ → AgentState ψ × AgentState ψ)
    [PP : ProtocolProperties ψ hψ n ring T] :
    PreservedUnder ring T
      (fun C => isSuppressed ring C ∧ noNonPeacefulBullet hψ ring C ∧ noFreeBarrier hψ ring C ∧
                (∀ k : Fin n, (C k).isLeader → (C k).label = ⟨0, hψ⟩))
      (hasUniqueLeader n) := by
  intro C ⟨hSupp, hNPB, hNFB, hLZ⟩ ⟨lp, hlp_leader, hlp_unique⟩ e
  dsimp only
  refine ⟨lp, ?_, fun k hk => ?_⟩
  · -- Leader at lp survives the interaction at edge e
    by_cases h1 : lp = e
    · simp only [if_pos h1]
      rcases PP.leader_initiator_stable (C e) (C (ring.rightNeighbor e))
        (h1 ▸ hlp_leader) with h | ⟨hbullet, hno_shield⟩
      · exact h
      · exfalso
        obtain ⟨_, _, _, hm_leader, hm_shield, _, _⟩ :=
          hNPB (ring.rightNeighbor e) hbullet
        have hm_eq := hlp_unique _ hm_leader
        rw [h1] at hm_eq
        rw [hm_eq] at hm_shield
        exact hno_shield hm_shield
    · by_cases h2 : lp = ring.rightNeighbor e
      · simp only [if_neg h1, if_pos h2]
        exact PP.leader_responder_stable (C e) (C (ring.rightNeighbor e))
          (h2 ▸ hlp_leader) (h2 ▸ hLZ lp hlp_leader)
      · simp only [if_neg h1, if_neg h2]; exact hlp_leader
  · -- No other agent becomes a leader
    by_cases hk1 : k = e
    · simp only [if_pos hk1] at hk
      have hpre : ¬(C (ring.rightNeighbor e)).isLeader ∨
          (C (ring.rightNeighbor e)).label = ⟨0, hψ⟩ := by
        by_cases hrl : (C (ring.rightNeighbor e)).isLeader
        · exact .inr (hLZ _ hrl)
        · exact .inl hrl
      exact hlp_unique k (hk1 ▸ PP.initiator_no_leader_creation (C e)
        (C (ring.rightNeighbor e)) hpre (hk1 ▸ hk))
    · by_cases hk2 : k = ring.rightNeighbor e
      · simp only [if_neg hk1, if_pos hk2] at hk
        by_cases hj_old : (C (ring.rightNeighbor e)).isLeader
        · exact hlp_unique k (hk2 ▸ hj_old)
        · exact absurd (hNFB e (PP.suppressed_blocks_comparison_leader (C e)
            (C (ring.rightNeighbor e)) (hSupp e) (hSupp (ring.rightNeighbor e))
            (hk2 ▸ hk) hj_old)) hj_old
      · simp only [if_neg hk1, if_neg hk2] at hk; exact hlp_unique k hk

/-- Phases 4→5 compose via ReachSpec.then: suppression persists (via
suppressed_preserved) while no-signal is being established. The
conjunction isSuppressed ∧ noActiveSignal holds after both phases. -/
def convergence_phases_4_5
    {ψ n : Nat} (hψ : ψ > 0) (ring : DirectedRing n)
    (T : AgentState ψ → AgentState ψ → AgentState ψ × AgentState ψ)
    [_PP : ProtocolProperties ψ hψ n ring T]
    {α : Type}
    (M : TraversalMetric ψ n ring T α)
    (signal : (Fin n → AgentState ψ) → List α)
    (hk : ∀ C, hasLeader n C → (signal C).length ≤ 1)
    (hgoal : ∀ C s, hasLeader n C →
      (∀ obj, obj ∈ signal C → M.goal (applySchedule ring T C s) obj) →
      isSuppressed ring (applySchedule ring T C s))
    (c : Nat) (hc : c ≥ 1) : ReachSpec ring T :=
  (phase_suppression hψ ring T M signal hk hgoal c hc).then
    (phase_no_signal hψ ring T c hc)
    (suppressed_preserved hψ ring T)

/-- Phases 7→8 compose via ReachSpec.seq: unique leader elimination feeds
directly into stable ID establishment. Pre = hasLeader ∧ noFreeBarrier,
Post = isStableIDSequence. -/
def convergence_phases_7_8
    {ψ n : Nat} (hψ : ψ > 0) (ring : DirectedRing n)
    (T : AgentState ψ → AgentState ψ → AgentState ψ × AgentState ψ)
    [_PP : ProtocolProperties ψ hψ n ring T]
    (c : Nat) (hc : c ≥ 1) : ReachSpec ring T :=
  (phase_unique_leader hψ ring T c hc).seq
    (phase_stable_id hψ ring T c hc)
    (fun _ h => h)

/-! ## Conditional preservation of quiescent scaffolding -/

/-- Restates `quiescent_safe_is_closed` as `Preserved`. This is conditional on
`ProtocolProperties` and has no concrete P_PLL instance. -/
theorem quiescent_safe_preserved
    {ψ n : Nat} (hψ : ψ > 0) (ring : DirectedRing n)
    (T : AgentState ψ → AgentState ψ → AgentState ψ × AgentState ψ)
    [_PP : ProtocolProperties ψ hψ n ring T] :
    Preserved ring T (QuiescentSafeConfig hψ ring) :=
  quiescent_safe_is_closed hψ ring T

/-! ## Aggregate metadata for Theorem 4.1.13 -/

/-- Aggregate of the ten proposed phase bounds. This is a profile constructor,
not Theorem 4.1.13: no phase-validity or union-bound proof is stored. The tenth
(quiescence) phase belongs only to the stronger historical scaffolding and is
not part of Wu's five-condition definition. -/
def convergence_profile
    {ψ n : Nat} (hψ : ψ > 0) (ring : DirectedRing n)
    (T : AgentState ψ → AgentState ψ → AgentState ψ × AgentState ψ)
    [_PP : ProtocolProperties ψ hψ n ring T]
    (c : Nat) (_hc : c ≥ 1) : ReachSpec ring T :=
  { Pre := fun _ => True
    Post := fun C => QuiescentSafeConfig hψ ring C
    steps := fun n =>
      let phase1 := c * n * (n + log2' n)
      let phase2 := c * n * n * log2' n
      let phase3 := c * n * n * log2' n
      let phase4 := c * n * (n + log2' n)
      let phase5 := c * n * n * log2' n
      let phase6 := c * n * (n + log2' n)
      let phase7 := c * n * n * log2' n
      let phase8 := c * n * n * log2' n * (log2' (log2' n) + 1)
      let phase9 := c * n * n * log2' n * (log2' (log2' n) + 1)
      let phase10 := c * n * (n + log2' n)
      phase1 + phase2 + phase3 + phase4 + phase5 + phase6 + phase7 + phase8 + phase9 + phase10
    failProb := fun n => (10 : Rat) / (n ^ c : Nat) }

/-! ## Delayed profile (not SSLE completeness) -/

/-- Extends the stored step count using conditional abstract closedness. Since
the input is non-semantic metadata, this does not prove convergence or SSLE. -/
def delayed_safe_profile
    {ψ n : Nat} (hψ : ψ > 0) (ring : DirectedRing n)
    (T : AgentState ψ → AgentState ψ → AgentState ψ × AgentState ψ)
    [_PP : ProtocolProperties ψ hψ n ring T]
    (c : Nat) (hc : c ≥ 1) (T' : StepBound) : ReachSpec ring T :=
  (convergence_profile hψ ring T c hc).delay T' (quiescent_safe_preserved hψ ring T)

/-! ## Optimal ψ and step bound analysis

The P_PLL protocol uses ψ = ⌈log₂(⌈log₂(n)⌉)⌉ bits for group IDs.
With this choice, the dominant term in the step bound is phase 8
(stable ID sequence), which takes O(n² · ψ · log n) steps. Since
ψ = Θ(log log n), the total convergence time is O(n² log n log log n). -/

/-- The optimal ψ parameter: ψ = log2'(log2' n) + 1.
The +1 ensures ψ > 0 even for small n, and corresponds to
⌈log₂(⌈log₂(n)⌉)⌉ for n ≥ 4. -/
def optimalPsi (n : Nat) : Nat :=
  log2' (log2' n) + 1

theorem optimalPsi_pos (n : Nat) : optimalPsi n > 0 := by
  unfold optimalPsi; omega

/-- Each phase's step bound, expressed as a multiple of the base unit
c · n². The coefficients show the asymptotic profile:
- Phases 1, 4, 6, 10: O(n²) — coefficient 1 + log₂(n)/n
- Phases 2, 3, 5, 7: O(n² log n) — coefficient log₂(n)
- Phases 8, 9: O(n² log n log log n) — coefficient log₂(n) · ψ -/
def phaseStepProfile (c n : Nat) : List Nat :=
  [ c * n * (n + log2' n)                              -- phase 1
  , c * n * n * log2' n                                 -- phase 2
  , c * n * n * log2' n                                 -- phase 3
  , c * n * (n + log2' n)                              -- phase 4
  , c * n * n * log2' n                                 -- phase 5
  , c * n * (n + log2' n)                              -- phase 6
  , c * n * n * log2' n                                 -- phase 7
  , c * n * n * log2' n * (log2' (log2' n) + 1) -- phase 8
  , c * n * n * log2' n * (log2' (log2' n) + 1) -- phase 9
  , c * n * (n + log2' n)                              -- phase 10
  ]

/-- The step bound in convergence_profile equals the sum of the phase profile. -/
theorem convergence_profile_steps_eq_sum
    {ψ n : Nat} (hψ : ψ > 0) (ring : DirectedRing n)
    (T : AgentState ψ → AgentState ψ → AgentState ψ × AgentState ψ)
    [_PP : ProtocolProperties ψ hψ n ring T]
    (c : Nat) (hc : c ≥ 1) :
    (convergence_profile hψ ring T c hc).steps n =
    (phaseStepProfile c n).foldl (· + ·) 0 := by
  simp only [convergence_profile, phaseStepProfile, List.foldl]
  omega

/-! ## O(n² log n log log n) dominance bound

The phase step profile has three tiers:
- Type A (phases 1,4,6,10): c·n·(n + log₂ n) — quadratic
- Type B (phases 2,3,5,7): c·n²·log₂ n — quasi-quadratic
- Type C (phases 8,9): c·n²·log₂ n·(log₂(log₂ n)+1) — dominant

For n ≥ 2: A ≤ 2B (since log₂ n ≥ 1) and B ≤ C (since log₂(log₂ n)+1 ≥ 1).
The total sum = 4A + 4B + 2C ≤ 4·2C + 4C + 2C = 14C.
This gives an arithmetic bound on the proposed profile with constant K = 14. -/

/-- Explicit arithmetic upper bound for the proposed phase profile. -/
def convergenceBound (c n : Nat) : Nat :=
  14 * c * n * n * log2' n * (log2' (log2' n) + 1)

/-- Type-A phases (quadratic): coefficient n + log₂ n ≤ 2 · (n · log₂ n). -/
private theorem type_a_le_b (n : Nat) (hn : n ≥ 2) :
    n + log2' n ≤ 2 * (n * log2' n) := by
  have h1 := log2'_le_self n
  have h2 := log2'_pos n hn
  have : n ≤ n * log2' n := le_mul_of_ge_one n (log2' n) h2
  have : log2' n ≤ n * log2' n := by
    calc log2' n = 1 * log2' n := (Nat.one_mul _).symm
      _ ≤ n * log2' n := Nat.mul_le_mul_right _ (by omega)
  omega

/-- Type-B phases: coefficient n · log₂ n ≤ n · log₂ n · (log₂(log₂ n) + 1). -/
private theorem type_b_le_c (n : Nat) :
    n * log2' n ≤ n * log2' n * (log2' (log2' n) + 1) :=
  le_mul_of_ge_one _ _ (by omega)

/-- Coefficient dominance: 4A + 4B + 2C ≤ 14C for n ≥ 2. -/
theorem coeff_bound (n : Nat) (hn : n ≥ 2) :
    4 * (n + log2' n) + 4 * (n * log2' n) + 2 * (n * log2' n * (log2' (log2' n) + 1))
    ≤ 14 * (n * log2' n * (log2' (log2' n) + 1)) := by
  have hAC : n + log2' n ≤ 2 * (n * log2' n * (log2' (log2' n) + 1)) :=
    Nat.le_trans (type_a_le_b n hn) (Nat.mul_le_mul_left 2 (type_b_le_c n))
  have hB := type_b_le_c n
  calc 4 * (n + log2' n) + 4 * (n * log2' n) + 2 * (n * log2' n * (log2' (log2' n) + 1))
      ≤ 4 * (2 * (n * log2' n * (log2' (log2' n) + 1))) +
        4 * (n * log2' n * (log2' (log2' n) + 1)) +
        2 * (n * log2' n * (log2' (log2' n) + 1)) :=
          Nat.add_le_add (Nat.add_le_add (Nat.mul_le_mul_left 4 hAC) (Nat.mul_le_mul_left 4 hB)) (Nat.le_refl _)
    _ = 14 * (n * log2' n * (log2' (log2' n) + 1)) := by omega

/-- Each type-A phase ≤ 2 · unit, where unit = c·n²·log₂ n·(log₂(log₂ n)+1). -/
private theorem phase_a_le (c n : Nat) (hn : n ≥ 2) :
    c * n * (n + log2' n) ≤ 2 * (c * n * n * log2' n * (log2' (log2' n) + 1)) := by
  have hAC : n + log2' n ≤ 2 * (n * log2' n * (log2' (log2' n) + 1)) :=
    Nat.le_trans (type_a_le_b n hn) (Nat.mul_le_mul_left 2 (type_b_le_c n))
  calc c * n * (n + log2' n)
      ≤ c * n * (2 * (n * log2' n * (log2' (log2' n) + 1))) :=
        Nat.mul_le_mul_left (c * n) hAC
    _ = 2 * (c * n * n * log2' n * (log2' (log2' n) + 1)) := by
        simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]

/-- Each type-B phase ≤ 1 · unit. -/
private theorem phase_b_le (c n : Nat) :
    c * n * n * log2' n ≤ c * n * n * log2' n * (log2' (log2' n) + 1) :=
  le_mul_of_ge_one _ _ (by omega)

/-- The stored profile's step count is at most
`14 · c · n² · log₂ n · (log₂(log₂ n)+1)` for `n ≥ 2`. This is an
arithmetic theorem about metadata, not a bound on executions of P_PLL. -/
theorem convergence_profile_step_bound
    {ψ n : Nat} (hψ : ψ > 0) (ring : DirectedRing n)
    (T : AgentState ψ → AgentState ψ → AgentState ψ × AgentState ψ)
    [_PP : ProtocolProperties ψ hψ n ring T]
    (c : Nat) (hc : c ≥ 1)
    (hn : n ≥ 2) :
    (convergence_profile hψ ring T c hc).steps n ≤ convergenceBound c n := by
  rw [convergence_profile_steps_eq_sum]
  simp only [phaseStepProfile, convergenceBound, List.foldl]
  have pa := phase_a_le c n hn
  have pb := phase_b_le c n
  have pc : c * n * n * log2' n * (log2' (log2' n) + 1) ≤
            c * n * n * log2' n * (log2' (log2' n) + 1) := Nat.le_refl _
  -- 4 type-A phases + 4 type-B phases + 2 type-C phases
  -- Each type-A ≤ 2 * unit, each type-B ≤ unit, each type-C = unit
  -- Total ≤ 4*2*unit + 4*unit + 2*unit = 14*unit
  have : ∀ x y : Nat, x ≤ y → x + 0 ≤ y := by omega
  -- Build the sum bound from individual phase bounds
  calc 0 + c * n * (n + log2' n) + c * n * n * log2' n +
       c * n * n * log2' n + c * n * (n + log2' n) +
       c * n * n * log2' n + c * n * (n + log2' n) +
       c * n * n * log2' n + c * n * n * log2' n * (log2' (log2' n) + 1) +
       c * n * n * log2' n * (log2' (log2' n) + 1) +
       c * n * (n + log2' n)
      ≤ 0 + 2 * (c * n * n * log2' n * (log2' (log2' n) + 1)) +
            c * n * n * log2' n * (log2' (log2' n) + 1) +
            c * n * n * log2' n * (log2' (log2' n) + 1) +
            2 * (c * n * n * log2' n * (log2' (log2' n) + 1)) +
            c * n * n * log2' n * (log2' (log2' n) + 1) +
            2 * (c * n * n * log2' n * (log2' (log2' n) + 1)) +
            c * n * n * log2' n * (log2' (log2' n) + 1) +
            c * n * n * log2' n * (log2' (log2' n) + 1) +
            c * n * n * log2' n * (log2' (log2' n) + 1) +
            2 * (c * n * n * log2' n * (log2' (log2' n) + 1)) :=
          Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add
          (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add
          (Nat.add_le_add (Nat.add_le_add (Nat.le_refl _) pa) pb) pb) pa) pb) pa) pb) pc) pc) pa
    _ = 14 * (c * n * n * log2' n * (log2' (log2' n) + 1)) := by omega
    _ = 14 * c * n * n * log2' n * (log2' (log2' n) + 1) := by
        simp only [Nat.mul_assoc]
