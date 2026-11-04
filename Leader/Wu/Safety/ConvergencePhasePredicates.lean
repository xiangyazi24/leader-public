import Leader.Wu.Safety.SafeConfig
import Leader.Wu.Scheduler.WhpProfiles

/-!
# Phase Predicates for Convergence Analysis

The convergence proof of Theorem 4.1.13 proceeds through intermediate
configurations. Each phase has a precondition (what holds before) and a
postcondition (what holds after). These predicates bridge the gap between
"any initial configuration" and "safe configuration."

Predicates reused from `Leader.Wu.Safety.SafeConfig`:
- `hasLeader`, `hasUniqueLeader`, `noNonPeacefulBullet`, `noFreeBarrier`,
  `noFreeOverwritingSignal`, `noActiveWriteAction`, `isStableIDSequence`, `isQuiescent`

New predicates defined here:
- `isClean` (all bullets peaceful)
- `isSuppressed` (all agents received reset)
- `noActiveSignal` (no active comparison signal)
-/

/-! ## Clean configuration -/

/-- Phase 1 target: a clean configuration where all live bullets are
peaceful. Formally, C ∈ C_PB (every live bullet is peaceful).
See Definition 1 (p.29) and Lemma 4.1.2 (p.43). -/
def isClean {ψ n : Nat} (hψ : ψ > 0) (ring : DirectedRing n)
    (C : Fin n → AgentState ψ) : Prop :=
  ∀ i : Fin n, (C i).bullet = ⟨2, by omega⟩ →
    isPeacefulBullet hψ ring C i

/-! ## Suppressed configuration -/

/-- Phase 3 target: all agents have received a reset command,
preventing new leader creation. -/
def isSuppressed {ψ n : Nat} (_ring : DirectedRing n)
    (C : Fin n → AgentState ψ) : Prop :=
  ∀ i : Fin n, (C i).reset_cmd = true

/-! ## No active signal -/

/-- Phase 4 target: no agent carries an active comparison signal.
This is separate from the historical `noActiveWriteAction` field:
it includes barrier-absence signals (signal_B). -/
def noActiveSignal {ψ n : Nat} (_ring : DirectedRing n)
    (C : Fin n → AgentState ψ) : Prop :=
  ∀ i : Fin n, (C i).signal_B = ⟨0, by omega⟩

/-! ## Predicate implications -/

/-- isStableIDSequence witnesses a leader at its starting position. -/
theorem stable_id_has_leader
    {ψ n : Nat} (hψ : ψ > 0) (ring : DirectedRing n)
    (C : Fin n → AgentState ψ)
    (h : isStableIDSequence hψ ring C) : hasLeader n C :=
  let ⟨lp, hlp, _⟩ := h; ⟨lp, hlp⟩

/-! ## QuiescentSafeConfig construction from convergence conditions -/

/-- The selected profile postconditions construct the historical six-field
quiescent scaffolding. This is a logical constructor, not a reachability claim. -/
theorem quiescentSafe_of_conditions
    {ψ n : Nat} (hψ : ψ > 0) (ring : DirectedRing n)
    (C : Fin n → AgentState ψ)
    (h1 : hasUniqueLeader n C)
    (h2 : noNonPeacefulBullet hψ ring C)
    (h3 : noFreeBarrier hψ ring C)
    (h4 : noActiveWriteAction ring C)
    (h5 : isStableIDSequence hψ ring C)
    (h6 : isQuiescent ring C) :
    QuiescentSafeConfig hψ ring C where
  unique_leader := h1
  no_nonpeaceful_bullet := h2
  no_free_barrier := h3
  no_active_write_action := h4
  stable_id_sequence := h5
  quiescent := h6
