import Leader.Wu.Safety.ConditionalClosedness

/-!
# P_PLL Transition Function Analysis

The full transition function for protocol P_PLL (Algorithm 1, p.14).
It composes 11 sub-algorithms applied in sequence to each interacting pair.

For proving safe-config closedness, we identify which sub-algorithms
can create new leaders or modify the safe-config invariants. Rather than
encoding all 20 algorithms in full detail, we identify the LEADER-CREATING
and LEADER-DESTROYING actions.

## Leader creation points (from the paper)
Leaders are created in exactly three places:
1. P'_ψ (Algorithm 2, line 3): probe hits barrier → r.leader ← 1
2. CHECK (Algorithm 11, line 15): ID(S) = ID(G), signal returns → r.leader ← 1
3. WRITE_SEQ (Algorithm 16, line 1): leader moves to label-0 position (reassignment)

## Leader destruction points
Leaders are destroyed in exactly one place:
1. EliminateLeaders' (Algorithm 15, line 7): live bullet hits unshielded leader
   → l.leader ← 0 (and bullet becomes dummy)
-/

/-! ## Abstract transition properties -/

/-- A transition function preserves a predicate on configurations if applying
any single edge interaction to a configuration satisfying the predicate
produces a configuration that also satisfies it. -/
def PreservesPred {ψ : Nat} (n : Nat) (ring : DirectedRing n)
    (T : AgentState ψ → AgentState ψ → AgentState ψ × AgentState ψ)
    (P : (Fin n → AgentState ψ) → Prop) : Prop :=
  ∀ (C : Fin n → AgentState ψ), P C → ∀ e : Fin n,
    let i := e
    let j := ring.rightNeighbor i
    let (qi', qj') := T (C i) (C j)
    let C' := fun k => if k = i then qi' else if k = j then qj' else C k
    P C'

/-! ## Leader creation analysis -/

/-- The two ways a NEW leader can be created, as a disjunction.
In a safe configuration, neither of these conditions can produce a new
leader at a non-leader position:
1. Barrier-probe meeting: requires a FREE barrier (excluded by condition 3
   + condition 5 → no barriers at non-leader positions)
2. Signal-group ID match: requires an active signal state (excluded
   implicitly by the quiescent state in a safe configuration) -/
inductive LeaderCreationEvent {ψ : Nat} (hψ : ψ > 0) (l r : AgentState ψ) : Prop where
  | barrier_probe : l.probe → r.label ≠ ⟨(l.label.val + 1) % ψ, Nat.mod_lt _ hψ⟩ →
      LeaderCreationEvent hψ l r
  | signal_check : r.state = .equal → r.label = ⟨ψ - 1, by omega⟩ →
      LeaderCreationEvent hψ l r

/-! ## Axiom system consistency: the identity transition model

The identity transition (no state change) trivially satisfies all 13
ProtocolProperties axioms. This exhibits a concrete model, proving the
axiom system is consistent (not self-contradictory). -/

/-- The identity transition: agents do not change state. -/
def identityTransition (ψ : Nat) :
    AgentState ψ → AgentState ψ → AgentState ψ × AgentState ψ :=
  fun l r => (l, r)

/-- The identity transition satisfies all 14 ProtocolProperties axioms.
Every premise involving state change (l'.isLeader ≠ l.isLeader, etc.)
is vacuously false, since l' = l and r' = r. -/
instance identityModel {ψ n : Nat} (hψ : ψ > 0) (ring : DirectedRing n) :
    ProtocolProperties ψ hψ n ring (identityTransition ψ) where
  leader_creation_requires_free_barrier_or_imperfection l r :=
    fun h hn => absurd h hn
  leader_destruction_requires_bullet_no_shield l r :=
    fun h hn => absurd h hn
  shield_removed_only_by_dummy l r :=
    fun _ hs hn => absurd hs hn
  label_change_preserves_barrier_at_leaders l r :=
    fun _ _ _ hb => hb
  leader_initiator_stable l r :=
    fun h => .inl h
  leader_responder_stable l r := by intro h _; exact h
  no_new_barrier l r :=
    fun h => h
  labels_bits_stable l r _ _ _ :=
    ⟨rfl, rfl, rfl, rfl⟩
  initiator_no_leader_creation l r := by intro _ h; exact h
  quiescent_stable l r hs1 hs2 hg1 hg2 how1 how2 :=
    ⟨hs1, hs2, hg1, hg2, how1, how2⟩
  reset_cmd_stable l r h1 h2 :=
    ⟨h1, h2⟩
  suppressed_no_new_signal l r _ _ h1 h2 :=
    ⟨h1, h2⟩
  suppressed_blocks_comparison_leader l r _ _ h hn :=
    absurd h hn
  safe_preserves_no_nonpeaceful_bullet C hC e := by
    dsimp only [identityTransition]
    suffices h : (fun k => if k = e then C e
      else if k = ring.rightNeighbor e then C (ring.rightNeighbor e)
      else C k) = C by
      rw [h]; exact hC.no_nonpeaceful_bullet
    funext k
    split
    · next h => rw [h]
    · split
      · next h => rw [h]
      · rfl
