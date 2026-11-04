import Leader.Wu.Safety.SafeConfig

/-!
# Conditional Closedness for the Quiescent Scaffolding

This module contains a modular abstract implication: a transition satisfying
`ProtocolProperties` preserves `QuiescentSafeConfig`. It is historical proof
scaffolding, not a proof of Wu's Lemma 4.1.1 for concrete P_PLL. Several class
fields are false for P_PLL and quiescence is intentionally broken by `genSig`.

The interface has two layers:

1. **Fine-grained axioms**: low-level properties of individual transition rules
   (leader creation requires a free barrier or imperfect ID, etc.). These serve
   as documentation and can be verified against the concrete transition.

2. **Condition-preservation axioms**: each safe-config condition is preserved
   under any step. These capture the paper's per-condition arguments at a
   granularity where the composition into the full closedness theorem is
   immediate.

## Paper's proof structure (p.42-43)

The paper proves preservation of each condition using the others:
- Cond 2 preserved ← Cond 2 + Cond 1
- Cond 1 preserved ← Cond 3 + Cond 5 + Cond 2
- Cond 3 preserved ← Cond 1
- Cond 4 preserved ← Cond 4 + Cond 1
- Cond 5 preserved ← Cond 1 + Cond 4
-/

/-! ## Protocol structural properties as a typeclass -/

/-- The structural properties of the P_PLL transition function that are
needed for the closedness proof. Any transition function satisfying these
properties yields a closed safe configuration.

The axioms fall into two groups:
- Fine-grained structural axioms (13): properties of individual transition rules
- Condition-preservation axiom (1): condition 2 is preserved
Conditions 1, 3, 5, the historical no-active-write field, and quiescence are
derived from fine-grained axioms. This module does not preserve Wu's corrected
global free-overwriting-signal predicate.
The `reset_cmd_stable`, `suppressed_no_new_signal`, and
`suppressed_blocks_comparison_leader` axioms enable derived monotonicity proofs
in the convergence layer. -/
class ProtocolProperties (ψ : Nat) (hψ : ψ > 0) (n : Nat) (ring : DirectedRing n)
    (T : AgentState ψ → AgentState ψ → AgentState ψ × AgentState ψ) where

  /- ### Fine-grained structural axioms

  All axioms use `.1`/`.2` projections instead of `let` bindings over `T l r`
  to avoid prohibitively expensive definitional unfolding during instance
  elaboration (the ppll composition has 11 nested steps × 31-field structs). -/

  /-- A leader is created at edge (i, i+1) only if there is a free barrier
  or the ID sequence is imperfect at that edge. -/
  leader_creation_requires_free_barrier_or_imperfection :
    ∀ (l r : AgentState ψ),
      (T l r).2.isLeader → ¬r.isLeader →
      (isBarrier hψ l r ∧ ¬r.isLeader) ∨
      (r.state = .equal ∧ r.label = ⟨ψ - 1, by omega⟩)

  /-- A leader is destroyed only by a live bullet (value 2) hitting
  an unshielded leader. -/
  leader_destruction_requires_bullet_no_shield :
    ∀ (l r : AgentState ψ),
      l.isLeader → ¬(T l r).1.isLeader →
      r.bullet = ⟨2, by omega⟩ ∧ ¬l.shield

  /-- The shield of a leader is only removed when it fires a dummy bullet. -/
  shield_removed_only_by_dummy :
    ∀ (l r : AgentState ψ),
      l.isLeader → l.shield → ¬(T l r).1.shield →
      (T l r).1.bullet = ⟨1, by omega⟩

  /-- The transition does not change labels of agents not involved, and only
  changes labels according to the barrier-advance rule (which preserves the
  barrier/non-barrier classification relative to leaders). -/
  label_change_preserves_barrier_at_leaders :
    ∀ (l r : AgentState ψ),
      r.isLeader → (T l r).2.isLeader →
      ∀ (l₀ : AgentState ψ), isBarrier hψ l₀ r → isBarrier hψ l₀ (T l r).2

  /-- The transition preserves leader status of the initiator unless
  destroyed by a bullet. -/
  leader_initiator_stable :
    ∀ (l r : AgentState ψ),
      l.isLeader → (T l r).1.isLeader ∨ (r.bullet = ⟨2, by omega⟩ ∧ ¬l.shield)

  /-- The transition preserves leader status of a responder whose label is 0.
  In P_PLL, writeSeq migrates leaders with non-zero labels, but a leader at
  label 0 (the stable position) is never demoted. -/
  leader_responder_stable :
    ∀ (l r : AgentState ψ),
      r.isLeader → r.label = ⟨0, hψ⟩ → (T l r).2.isLeader

  /-- The transition does not create new barriers: if (l, r) is not a barrier
  before the step, then (l', r') is also not a barrier. -/
  no_new_barrier :
    ∀ (l r : AgentState ψ),
      ¬isBarrier hψ l r → ¬isBarrier hψ (T l r).1 (T l r).2

  /-- Without overwriting signals and without free barriers, labels and bits
  are preserved for both interacting agents. In P_PLL, labels change only
  at free barriers (P'_ψ) and bits change only via overwriting signals
  (WRITE_ACTION). -/
  labels_bits_stable :
    ∀ (l r : AgentState ψ),
      (l.write_state = .none ∨ l.write = .none) →
      (r.write_state = .none ∨ r.write = .none) →
      (¬isBarrier hψ l r ∨ r.isLeader) →
      (T l r).1.label = l.label ∧ (T l r).1.bit = l.bit ∧
      (T l r).2.label = r.label ∧ (T l r).2.bit = r.bit

  /-- The initiator (left agent) cannot gain leader status unless via
  writeSeq migration (responder is leader with non-zero label). When the
  responder is not a leader or has label 0, new leaders are only at the
  responder position. -/
  initiator_no_leader_creation :
    ∀ (l r : AgentState ψ),
      (¬r.isLeader ∨ r.label = ⟨0, hψ⟩) →
      (T l r).1.isLeader → l.isLeader

  /-- In a quiescent state with no overwriting signals, the interaction
  preserves quiescence and the absence of overwriting signals. -/
  quiescent_stable :
    ∀ (l r : AgentState ψ),
      l.state = .none → r.state = .none →
      l.gen_ws = false → r.gen_ws = false →
      (l.write_state = .none ∨ l.write = .none) →
      (r.write_state = .none ∨ r.write = .none) →
      (T l r).1.state = .none ∧ (T l r).2.state = .none ∧
      (T l r).1.gen_ws = false ∧ (T l r).2.gen_ws = false ∧
      ((T l r).1.write_state = .none ∨ (T l r).1.write = .none) ∧
      ((T l r).2.write_state = .none ∨ (T l r).2.write = .none)

  /-- Once reset_cmd is true for both interacting agents, the transition
  preserves it. In P_PLL, reset_cmd is a permanent flag set by the reset
  signal — once set, it is never cleared. -/
  reset_cmd_stable :
    ∀ (l r : AgentState ψ),
      l.reset_cmd = true → r.reset_cmd = true →
      (T l r).1.reset_cmd = true ∧ (T l r).2.reset_cmd = true

  /-- Once all agents are suppressed (reset_cmd = true) and no active
  signal_B exists, the transition preserves signal_B = 0. In P_PLL,
  signal_B is part of the barrier-checking sub-protocol; once suppressed,
  the main state machine prevents new signal_B generation. -/
  suppressed_no_new_signal :
    ∀ (l r : AgentState ψ),
      l.reset_cmd = true → r.reset_cmd = true →
      l.signal_B = ⟨0, by omega⟩ → r.signal_B = ⟨0, by omega⟩ →
      (T l r).1.signal_B = ⟨0, by omega⟩ ∧ (T l r).2.signal_B = ⟨0, by omega⟩

  /-- With reset_cmd set, the only leader creation path is via barrier-probe.
  The comparison-based creation (state=.equal at the responder triggering
  leader promotion) is blocked because the CHECK sub-protocol (Algorithm 11)
  resets state to .none when reset_cmd is true, before processing. -/
  suppressed_blocks_comparison_leader :
    ∀ (l r : AgentState ψ),
      l.reset_cmd = true → r.reset_cmd = true →
      (T l r).2.isLeader → ¬r.isLeader →
      isBarrier hψ l r

  /- ### Condition-preservation axiom

  Condition 2 (no non-peaceful bullet) is preserved by a single interaction
  step, assuming the full safe configuration holds before the step.
  The remaining conditions (1, 3, 4, 5, quiescence) are derived from
  fine-grained axioms. -/

  /-- **Condition 2**: No non-peaceful bullet is preserved.
  Paper's argument: with a unique leader (cond 1) and no existing non-peaceful
  bullet (cond 2), new bullets are fired only by the leader and are
  immediately peaceful (adjacent to the shielded leader). -/
  safe_preserves_no_nonpeaceful_bullet :
    ∀ (C : Fin n → AgentState ψ), QuiescentSafeConfig hψ ring C →
    ∀ (e : Fin n),
      noNonPeacefulBullet hψ ring
        (fun k => if k = e then (T (C e) (C (ring.rightNeighbor e))).1
                  else if k = ring.rightNeighbor e then (T (C e) (C (ring.rightNeighbor e))).2
                  else C k)

/-! ## Derived preservation of conditions 1, 3, 4, 5, and quiescence -/

/-- groupID is preserved when all bits are preserved. -/
private theorem groupID_congr {ψ n : Nat} {hn : n > 0}
    {C C' : Fin n → AgentState ψ} {start : Fin n}
    (h : ∀ pos : Fin n, (C' pos).bit = (C pos).bit) :
    groupID hn C' start = groupID hn C start := by
  simp only [groupID, h]

/-- **Condition 5 preservation**: isStableIDSequence is preserved by any
interaction step in a safe configuration. Proved from `labels_bits_stable`:
in this scaffolding, no free barriers and no active write actions, so all labels
and bits are preserved at every position. -/
private theorem stable_id_preserved {ψ n : Nat} (hψ : ψ > 0)
    (ring : DirectedRing n)
    (T : AgentState ψ → AgentState ψ → AgentState ψ × AgentState ψ)
    [PP : ProtocolProperties ψ hψ n ring T]
    (C : Fin n → AgentState ψ) (hC : QuiescentSafeConfig hψ ring C) (e : Fin n) :
    isStableIDSequence hψ ring (fun k =>
      if k = e then (T (C e) (C (ring.rightNeighbor e))).1
      else if k = ring.rightNeighbor e then (T (C e) (C (ring.rightNeighbor e))).2
      else C k) := by
  obtain ⟨lp, hlp_leader, hlp_label, hlabels, hgroups⟩ := hC.stable_id_sequence
  obtain ⟨lp_u, _, hlp_u_unique⟩ := hC.unique_leader
  have hlp_unique : ∀ j : Fin n, (C j).isLeader → j = lp :=
    fun j hj => (hlp_u_unique j hj).trans (hlp_u_unique lp hlp_leader).symm
  have h_nfb : ¬isBarrier hψ (C e) (C (ring.rightNeighbor e)) ∨
      (C (ring.rightNeighbor e)).isLeader := by
    by_cases hb : isBarrier hψ (C e) (C (ring.rightNeighbor e))
    · exact .inr (hC.no_free_barrier e hb)
    · exact .inl hb
  obtain ⟨hli, hbi, hlj, hbj⟩ :=
    PP.labels_bits_stable (C e) (C (ring.rightNeighbor e))
      (hC.no_active_write_action e) (hC.no_active_write_action (ring.rightNeighbor e))
      h_nfb
  have hpres_bit (pos : Fin n) :
      (if pos = e then (T (C e) (C (ring.rightNeighbor e))).1
       else if pos = ring.rightNeighbor e then (T (C e) (C (ring.rightNeighbor e))).2
       else C pos).bit = (C pos).bit := by
    by_cases h1 : pos = e
    · simp only [if_pos h1]; rw [h1]; exact hbi
    · by_cases h2 : pos = ring.rightNeighbor e
      · simp only [if_neg h1, if_pos h2]; rw [h2]; exact hbj
      · simp only [if_neg h1, if_neg h2]
  refine ⟨lp, ?_, ?_, ?_, ?_⟩
  · -- (C' lp).isLeader: leader position is stable
    by_cases h1 : lp = e
    · rw [h1] at hlp_leader hlp_unique ⊢; simp only [ite_true]
      rcases PP.leader_initiator_stable (C e) (C (ring.rightNeighbor e)) hlp_leader
        with h | ⟨hbullet, hno_shield⟩
      · exact h
      · exfalso
        obtain ⟨_, _, _, hm_leader, hm_shield, _, _⟩ :=
          hC.no_nonpeaceful_bullet (ring.rightNeighbor e) hbullet
        have hm_eq := hlp_unique _ hm_leader
        rw [hm_eq] at hm_shield
        exact hno_shield hm_shield
    · by_cases h2 : lp = ring.rightNeighbor e
      · rw [h2] at hlp_leader hlp_label h1 ⊢; simp only [if_neg h1, ite_true]
        exact PP.leader_responder_stable (C e) (C (ring.rightNeighbor e)) hlp_leader hlp_label
      · simp only [if_neg h1, if_neg h2]; exact hlp_leader
  · -- (C' lp).label = ⟨0, hψ⟩
    by_cases h1 : lp = e
    · rw [h1] at hlp_label; simp only [if_pos h1]; rw [hli]; exact hlp_label
    · by_cases h2 : lp = ring.rightNeighbor e
      · rw [h2] at hlp_label; simp only [if_neg h1, if_pos h2]; rw [hlj]; exact hlp_label
      · simp only [if_neg h1, if_neg h2]; exact hlp_label
  · -- ∀ k < n, label at offset k preserved
    intro k hk
    by_cases h1 : (⟨(lp.val + k) % n, Nat.mod_lt _ ring.hn⟩ : Fin n) = e
    · simp only [if_pos h1]; rw [hli, ← h1]; exact hlabels k hk
    · by_cases h2 : (⟨(lp.val + k) % n, Nat.mod_lt _ ring.hn⟩ : Fin n) = ring.rightNeighbor e
      · simp only [if_neg h1, if_pos h2]; rw [hlj, ← h2]; exact hlabels k hk
      · simp only [if_neg h1, if_neg h2]; exact hlabels k hk
  · -- ∀ i > 0, groupID preserved
    intro i hi hlt
    exact (groupID_congr hpres_bit).trans (hgroups i hi hlt)

/-- **Quiescence preservation**: quiescence and the historical absence of
active write actions are preserved by any interaction step in a safe configuration.
Proved from `quiescent_stable`. -/
private theorem quiescent_preserved {ψ n : Nat} (hψ : ψ > 0)
    (ring : DirectedRing n)
    (T : AgentState ψ → AgentState ψ → AgentState ψ × AgentState ψ)
    [PP : ProtocolProperties ψ hψ n ring T]
    (C : Fin n → AgentState ψ) (hC : QuiescentSafeConfig hψ ring C) (e : Fin n) :
    let C' := fun k =>
      if k = e then (T (C e) (C (ring.rightNeighbor e))).1
      else if k = ring.rightNeighbor e then (T (C e) (C (ring.rightNeighbor e))).2
      else C k
    isQuiescent ring C' ∧ noActiveWriteAction ring C' := by
  obtain ⟨hstates, hgenws⟩ := hC.quiescent
  obtain ⟨hs1, hs2, hg1, hg2, how1, how2⟩ :=
    PP.quiescent_stable (C e) (C (ring.rightNeighbor e))
      (hstates e) (hstates (ring.rightNeighbor e))
      (hgenws e) (hgenws (ring.rightNeighbor e))
      (hC.no_active_write_action e)
      (hC.no_active_write_action (ring.rightNeighbor e))
  refine ⟨⟨fun k => ?_, fun k => ?_⟩, fun k => ?_⟩
  · by_cases h1 : k = e
    · simp only [if_pos h1]; exact hs1
    · by_cases h2 : k = ring.rightNeighbor e
      · simp only [if_neg h1, if_pos h2]; exact hs2
      · simp only [if_neg h1, if_neg h2]; exact hstates k
  · by_cases h1 : k = e
    · simp only [if_pos h1]; exact hg1
    · by_cases h2 : k = ring.rightNeighbor e
      · simp only [if_neg h1, if_pos h2]; exact hg2
      · simp only [if_neg h1, if_neg h2]; exact hgenws k
  · by_cases h1 : k = e
    · simp only [if_pos h1]; exact how1
    · by_cases h2 : k = ring.rightNeighbor e
      · simp only [if_neg h1, if_pos h2]; exact how2
      · simp only [if_neg h1, if_neg h2]; exact hC.no_active_write_action k

/-- **Condition 1 preservation**: hasUniqueLeader is preserved by any
interaction step in a safe configuration. Proved from `initiator_no_leader_creation`,
`leader_creation_requires_free_barrier_or_imperfection`, `leader_initiator_stable`,
`leader_responder_stable`, and the safe-config conditions (no free barrier,
no non-peaceful bullet, quiescence). -/
private theorem unique_leader_preserved {ψ n : Nat} (hψ : ψ > 0)
    (ring : DirectedRing n)
    (T : AgentState ψ → AgentState ψ → AgentState ψ × AgentState ψ)
    [PP : ProtocolProperties ψ hψ n ring T]
    (C : Fin n → AgentState ψ) (hC : QuiescentSafeConfig hψ ring C) (e : Fin n) :
    hasUniqueLeader n (fun k =>
      if k = e then (T (C e) (C (ring.rightNeighbor e))).1
      else if k = ring.rightNeighbor e then (T (C e) (C (ring.rightNeighbor e))).2
      else C k) := by
  obtain ⟨lp, hlp_leader, hlp_unique⟩ := hC.unique_leader
  have hlp_label : (C lp).label = ⟨0, hψ⟩ := by
    obtain ⟨lp_s, hlps_leader, hlps_label, _, _⟩ := hC.stable_id_sequence
    rwa [hlp_unique lp_s hlps_leader] at hlps_label
  refine ⟨lp, ?_, fun k hk => ?_⟩
  · -- The leader at lp survives
    by_cases h1 : lp = e
    · rw [h1] at hlp_leader hlp_unique ⊢; simp only [ite_true]
      rcases PP.leader_initiator_stable (C e) (C (ring.rightNeighbor e)) hlp_leader
        with h | ⟨hbullet, hno_shield⟩
      · exact h
      · exfalso
        obtain ⟨_, _, _, hm_leader, hm_shield, _, _⟩ :=
          hC.no_nonpeaceful_bullet (ring.rightNeighbor e) hbullet
        exact hno_shield (by rwa [hlp_unique _ hm_leader] at hm_shield)
    · by_cases h2 : lp = ring.rightNeighbor e
      · rw [h2] at hlp_leader hlp_label h1 ⊢; simp only [if_neg h1, ite_true]
        exact PP.leader_responder_stable (C e) (C (ring.rightNeighbor e)) hlp_leader hlp_label
      · simp only [if_neg h1, if_neg h2]; exact hlp_leader
  · -- No other agent is a leader: (C' k).isLeader → k = lp
    by_cases hke : k = e
    · rw [hke] at hk ⊢; simp only [ite_true] at hk
      have hpre : ¬(C (ring.rightNeighbor e)).isLeader ∨
          (C (ring.rightNeighbor e)).label = ⟨0, hψ⟩ := by
        by_cases hrl : (C (ring.rightNeighbor e)).isLeader
        · exact .inr (by rw [hlp_unique _ hrl]; exact hlp_label)
        · exact .inl hrl
      exact hlp_unique e (PP.initiator_no_leader_creation (C e) (C (ring.rightNeighbor e)) hpre hk)
    · by_cases hkj : k = ring.rightNeighbor e
      · rw [hkj] at hk ⊢
        have hne : ring.rightNeighbor e ≠ e := fun h => hke (hkj.trans h)
        simp only [if_neg hne, ite_true] at hk
        by_cases hjl : (C (ring.rightNeighbor e)).isLeader
        · exact hlp_unique (ring.rightNeighbor e) hjl
        · exfalso
          rcases PP.leader_creation_requires_free_barrier_or_imperfection
            (C e) (C (ring.rightNeighbor e)) hk hjl with ⟨hbar, _⟩ | ⟨hstate, _⟩
          · exact hjl (hC.no_free_barrier e hbar)
          · rw [hC.quiescent.1 (ring.rightNeighbor e)] at hstate
            exact absurd hstate (by decide)
      · simp only [if_neg hke, if_neg hkj] at hk
        exact hlp_unique k hk

/-! ## Closedness proof -/

/-- Conditional closedness of the six-field quiescent scaffolding.
This theorem must not be identified with concrete Lemma 4.1.1. -/
theorem quiescent_safe_is_closed {ψ n : Nat} (hψ : ψ > 0) (ring : DirectedRing n)
    (T : AgentState ψ → AgentState ψ → AgentState ψ × AgentState ψ)
    [PP : ProtocolProperties ψ hψ n ring T] :
    ∀ (C : Fin n → AgentState ψ), QuiescentSafeConfig hψ ring C →
    ∀ (e : Fin n),
    let i := e
    let j := ring.rightNeighbor i
    let (qi', qj') := T (C i) (C j)
    let C' := fun k => if k = i then qi' else if k = j then qj' else C k
    QuiescentSafeConfig hψ ring C' := by
  intro C hC e
  have hstable' := stable_id_preserved hψ ring T C hC e
  have ⟨hquiet', how'⟩ := quiescent_preserved hψ ring T C hC e
  exact {
    unique_leader := unique_leader_preserved hψ ring T C hC e
    no_nonpeaceful_bullet := PP.safe_preserves_no_nonpeaceful_bullet C hC e
    no_free_barrier := noFreeBarrier_of_stableID hψ ring _ hstable'
    no_active_write_action := how'
    stable_id_sequence := hstable'
    quiescent := hquiet'
  }
