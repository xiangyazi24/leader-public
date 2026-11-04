import Leader.Wu.Elimination.PeacefulCounterexamples

/-!
# Nearest-leader peacefulness for the actual finite elimination component

The old existential peacefulness predicate may skip a nearer unshielded
leader. Here every live bullet has a zero-signal interval to its first
clockwise leader, and that endpoint is shielded. All conditions concern the
current configuration. No future execution or closure is a structure field.
-/

namespace K2PeacefulGlobal

open PPLL PPLLRepair LDSinkKernelC K2OutputSafety LDSinkBoundedKernel
  StateBoundUnifiedCell PPLLNoCheckBirthConditionTwoGeometry
  PPLLNoCheckBirthConditionTwoPhysical PPLLNoCheckBirthConditionTwoProtocol

set_option autoImplicit false

variable {n ψ κ : Nat}

private def signalCell (leader shield : Bool) (bullet : Fin 3) (signal : Fin 2) :
    AgentState 1 := PeaceView.toState ⟨leader, 0, shield, bullet, signal⟩

/-- A finite certificate of the existing row's fields used by the interval
proof. Its inputs and outputs are the actual kernel; it defines no new row. -/
private def RowFacts (l r : AgentState 1) (q : AgentState 1 × AgentState 1) : Prop :=
  (l.leader = true → l.shield = true → l.signal_B = 0 →
    q.1.leader = true ∧ q.1.shield = true) ∧
  (r.leader = true → r.shield = true → r.signal_B = 0 →
    q.2.leader = true ∧ q.2.shield = true) ∧
  (l.signal_B = 0 → q.1.signal_B = 0) ∧
  (l.leader = false → l.signal_B = 0 → r.signal_B = 0 → q.2.signal_B = 0) ∧
  (q.2.bullet = 2 → q.2.signal_B = 0) ∧
  (l.leader = true → l.signal_B = 1 →
    q.1.leader = true ∧ q.1.shield = true ∧ q.1.signal_B = 0) ∧
  (q.1.bullet = 2 → l.bullet = 2 ∨ (l.leader = true ∧ l.signal_B = 1) ∨
    (r.bullet = 2 ∧ l.leader = false)) ∧
  (q.2.bullet = 2 → r.bullet = 2) ∧
  (l.leader = false → r.bullet = 2 → r.signal_B = 0 →
    q.1.signal_B = 0 ∧ q.2.signal_B = 0) ∧
  (l.leader = true → q.1.leader = false → r.bullet = 2)

set_option synthInstance.maxSize 512 in
private instance rowFactsDecision (l r : AgentState 1) (q : AgentState 1 × AgentState 1) :
    Decidable (RowFacts l r q) := by
  unfold RowFacts
  infer_instance

private theorem finite_row_facts :
    ∀ (ll ls rl rs : Bool) (lb rb : Fin 3) (lz rz : Fin 2),
      RowFacts (signalCell ll ls lb lz) (signalCell rl rs rb rz)
        (sinkKernelC (by decide) (signalCell ll ls lb lz) (signalCell rl rs rb rz)) := by
  intro ll ls rl rs
  cases ll <;> cases ls <;> cases rl <;> cases rs <;> decide

private theorem row_facts (l r : AgentState 1) : RowFacts l r (sinkKernelC (by decide) l r) := by
  have h := finite_row_facts l.leader l.shield r.leader r.shield
    l.bullet r.bullet l.signal_B r.signal_B
  have he := signal_kernel (by decide) l r (Or.inl (Subsingleton.elim _ _))
  change (signalView (sinkKernelC (by decide) l r).1,
    signalView (sinkKernelC (by decide) l r).2) =
      sinkKernelC (by decide) (signalView l) (signalView r) at he
  change RowFacts (signalView l) (signalView r)
    (sinkKernelC (by decide) (signalView l) (signalView r)) at h
  rw [← he] at h
  exact h

/-- The bounded interval ends at a shielded leader; every strictly earlier
site, including the bullet site when the distance is positive, is a follower. -/
structure Support (ring : DirectedRing n) (C : Fin n → AgentState 1)
    (start : Fin n) (d : Nat) : Prop where
  distance_lt : d < n
  target_leader : (C (cwPos ring start d)).leader = true
  target_shield : (C (cwPos ring start d)).shield = true
  signal_zero : ∀ k, k ≤ d → (C (cwPos ring start k)).signal_B = 0
  before_follower : ∀ k, k < d → (C (cwPos ring start k)).leader = false

/-- Every live bullet is supported by its first clockwise leader. -/
def NearestPeaceful (ring : DirectedRing n) (C : Fin n → AgentState 1) : Prop :=
  ∀ start, (C start).bullet = 2 → ∃ d, Support ring C start d

/-- Forgetting the first-leader requirement gives the previously defined
literal peacefulness predicate at the singleton observation modulus. -/
theorem nearest_implies_literal (ring : DirectedRing n) (C : Fin n → AgentState 1)
    (hC : NearestPeaceful ring C) : noNonPeacefulBullet (by decide) ring C := by
  intro i hi
  obtain ⟨d, hs⟩ := hC i hi
  exact ⟨hi, d, hs.distance_lt, hs.target_leader, hs.target_shield, hs.signal_zero,
    fun _ _ => Subsingleton.elim _ _⟩

private theorem raw_target_fields (hn : 1 < n) (ring : DirectedRing n)
    (C : Fin n → AgentState 1) (e target : Fin n)
    (hl : (C target).leader = true) (hsh : (C target).shield = true)
    (hz : (C target).signal_B = 0) :
    (rawStep (by decide) ring C e target).leader = true ∧
      (rawStep (by decide) ring C e target).shield = true := by
  let r := ring.rightNeighbor e
  have hne : r ≠ e := rightNeighbor_ne_self_of_one_lt ring hn e
  change (updatePair C e r (sinkKernelC (by decide) (C e) (C r)) target).leader = true ∧
    (updatePair C e r (sinkKernelC (by decide) (C e) (C r)) target).shield = true
  by_cases he : target = e
  · subst target
    simpa only [updatePair_initiator] using
      (row_facts (C e) (C r)).1 hl hsh hz
  · by_cases hr : target = r
    · subst target
      simpa only [updatePair_responder _ _ _ _ hne] using
        (row_facts (C e) (C r)).2.1 hl hsh hz
    · simpa only [updatePair_other _ _ _ _ _ he hr] using And.intro hl hsh

private theorem support_signals (hn : 1 < n) (ring : DirectedRing n)
    (C : Fin n → AgentState 1) (e start : Fin n) (d : Nat)
    (hs : Support ring C start d)
    (hrstart : start = ring.rightNeighbor e →
      (sinkKernelC (by decide) (C e) (C (ring.rightNeighbor e))).2.signal_B = 0) :
    ∀ k, k ≤ d → (rawStep (by decide) ring C e (cwPos ring start k)).signal_B = 0 := by
  intro k hk
  let r := ring.rightNeighbor e
  let m := cwPos ring start k
  have hne : r ≠ e := rightNeighbor_ne_self_of_one_lt ring hn e
  have hz : (C m).signal_B = 0 := hs.signal_zero k hk
  by_cases he : m = e
  · change (updatePair C e r _ m).signal_B = 0
    rw [he, updatePair_initiator]
    exact (row_facts (C e) (C r)).2.2.1 (he ▸ hz)
  · by_cases hr : m = r
    · change (updatePair C e r _ m).signal_B = 0
      rw [hr, updatePair_responder _ _ _ _ hne]
      by_cases hstart : start = r
      · exact hrstart hstart
      · obtain ⟨k0, hk0, hpos⟩ := interval_predecessor ring start e k hr hstart
        have hleft : (C e).leader = false := by
          rw [← hpos]
          exact hs.before_follower k0 (by omega)
        have hzero : (C e).signal_B = 0 := by
          rw [← hpos]
          exact hs.signal_zero k0 (by omega)
        exact (row_facts (C e) (C r)).2.2.2.1 hleft hzero (hr ▸ hz)
    · change (updatePair C e r _ m).signal_B = 0
      rw [updatePair_other _ _ _ _ _ he hr]
      exact hz

private theorem support_kept (hn : 1 < n) (ring : DirectedRing n)
    (C : Fin n → AgentState 1) (e start : Fin n) (d : Nat)
    (hs : Support ring C start d)
    (hb : (rawStep (by decide) ring C e start).bullet = 2) :
    Support ring (rawStep (by decide) ring C e) start d := by
  have ht := raw_target_fields hn ring C e (cwPos ring start d)
    hs.target_leader hs.target_shield (hs.signal_zero d (Nat.le_refl _))
  refine ⟨hs.distance_lt, ht.1, ht.2, ?_, ?_⟩
  · apply support_signals hn ring C e start d hs
    intro hstart
    have hne := rightNeighbor_ne_self_of_one_lt ring hn e
    have hq : (sinkKernelC (by decide) (C e) (C (ring.rightNeighbor e))).2.bullet = 2 := by
      simpa only [rawStep, hstart, updatePair_responder _ _ _ _ hne] using hb
    exact (row_facts (C e) (C (ring.rightNeighbor e))).2.2.2.2.1 hq
  · intro k hk
    exact K2GlobalGapClosure.rawStep_follower (by decide) ring C e _ (hs.before_follower k hk)

private theorem support_moved (hn : 1 < n) (ring : DirectedRing n)
    (C : Fin n → AgentState 1) (e : Fin n) (d : Nat)
    (hs : Support ring C (ring.rightNeighbor e) d)
    (hl : (C e).leader = false) (hb : (C (ring.rightNeighbor e)).bullet = 2) :
    Support ring (rawStep (by decide) ring C e) e (d + 1) := by
  let r := ring.rightNeighbor e
  have hz : (C r).signal_B = 0 := by simpa using hs.signal_zero 0 (by omega)
  have hmove := (row_facts (C e) (C r)).2.2.2.2.2.2.2.2.1 hl hb hz
  have ht := raw_target_fields hn ring C e (cwPos ring r d)
    hs.target_leader hs.target_shield (hs.signal_zero d (Nat.le_refl _))
  refine ⟨peaceful_move_distance_succ_lt ring C e d hs.distance_lt hs.target_leader hl,
    ?_, ?_, ?_, ?_⟩
  · rw [← cwPos_rightNeighbor]
    exact ht.1
  · rw [← cwPos_rightNeighbor]
    exact ht.2
  · intro k hk
    cases k with
    | zero => simpa only [cwPos_zero, rawStep, updatePair_initiator] using hmove.1
    | succ k =>
      rw [← cwPos_rightNeighbor]
      exact support_signals hn ring C e r d hs (fun _ => hmove.2) k (by omega)
  · intro k hk
    apply K2GlobalGapClosure.rawStep_follower (by decide) ring C e
    cases k with
    | zero => simpa using hl
    | succ k =>
      rw [← cwPos_rightNeighbor]
      exact hs.before_follower k (by omega)

/-- Nearest-leader peacefulness is preserved on multileader configurations
by the actual K2 row. No unique-leader or global-gap premise is used. -/
theorem nearest_rawStep (hn : 1 < n) (ring : DirectedRing n)
    (C : Fin n → AgentState 1) (hC : NearestPeaceful ring C) (e : Fin n) :
    NearestPeaceful ring (rawStep (by decide) ring C e) := by
  intro start hb
  let r := ring.rightNeighbor e
  have hne : r ≠ e := rightNeighbor_ne_self_of_one_lt ring hn e
  change (updatePair C e r (sinkKernelC (by decide) (C e) (C r)) start).bullet = 2 at hb
  by_cases he : start = e
  · subst start
    have hq : (sinkKernelC (by decide) (C e) (C r)).1.bullet = 2 := by
      simpa only [rawStep, updatePair_initiator] using hb
    rcases (row_facts (C e) (C r)).2.2.2.2.2.2.1 hq with hold | hfire | hmove
    · obtain ⟨d, hs⟩ := hC e hold
      exact ⟨d, support_kept hn ring C e e d hs hb⟩
    · have hf := (row_facts (C e) (C r)).2.2.2.2.2.1 hfire.1 hfire.2
      refine ⟨0, ring.hn, ?_, ?_, ?_, ?_⟩
      · simpa only [cwPos_zero, rawStep, updatePair_initiator] using hf.1
      · simpa only [cwPos_zero, rawStep, updatePair_initiator] using hf.2.1
      · intro k hk
        have : k = 0 := by omega
        subst k
        simpa only [cwPos_zero, rawStep, updatePair_initiator] using hf.2.2
      · intro k hk
        omega
    · obtain ⟨d, hs⟩ := hC r hmove.1
      exact ⟨d + 1, support_moved hn ring C e d hs hmove.2 hmove.1⟩
  · have hold : (C start).bullet = 2 := by
      by_cases hr : start = r
      · have hq : (sinkKernelC (by decide) (C e) (C r)).2.bullet = 2 := by
          simpa only [rawStep, hr, updatePair_responder _ _ _ _ hne] using hb
        have hh := (row_facts (C e) (C r)).2.2.2.2.2.2.2.1 hq
        exact hr ▸ hh
      · simpa only [rawStep, updatePair_other _ _ _ _ _ he hr] using hb
    obtain ⟨d, hs⟩ := hC start hold
    exact ⟨d, support_kept hn ring C e start d hs hb⟩

/-- If the selected old leader is deleted, its killing old live bullet has
a shielded supporting leader that survives this very edge. -/
theorem hasLeader_rawStep (hn : 1 < n) (ring : DirectedRing n)
    (C : Fin n → AgentState 1) (hC : NearestPeaceful ring C)
    (hL : hasLeader n C) (e : Fin n) : hasLeader n (rawStep (by decide) ring C e) := by
  obtain ⟨p, hp⟩ := hL
  by_cases hd : (rawStep (by decide) ring C e p).leader = true
  · exact ⟨p, hd⟩
  · have he : p = e := by
      by_cases hh : p = e
      · exact hh
      · exact False.elim (hd
          ((K2GlobalGapClosure.rawStep_leader_away (by decide) ring C e p hh).trans hp))
    subst p
    have hfalse : (rawStep (by decide) ring C e e).leader = false := by
      cases h : (rawStep (by decide) ring C e e).leader <;> simp_all
    have hq : (sinkKernelC (by decide) (C e) (C (ring.rightNeighbor e))).1.leader = false := by
      simpa only [rawStep, updatePair_initiator] using hfalse
    have hb := (row_facts (C e) (C (ring.rightNeighbor e))).2.2.2.2.2.2.2.2.2 hp hq
    obtain ⟨d, hs⟩ := hC (ring.rightNeighbor e) hb
    exact ⟨cwPos ring (ring.rightNeighbor e) d,
      (raw_target_fields hn ring C e _ hs.target_leader hs.target_shield
        (hs.signal_zero d (Nat.le_refl _))).1⟩

/-- Current existence and nearest peacefulness on the exact four-field
observation of the existing finite carrier. -/
def PeacefulGlobal (ring : DirectedRing n) (C : Fin n → UCell ψ κ) : Prop :=
  hasLeader n (LabelFreeElimination.observe C) ∧
    NearestPeaceful ring (LabelFreeElimination.observe C)

/-- One actual finite interaction preserves the class through the exact
same-edge observation theorem; real labels and controller fields are arbitrary. -/
theorem peacefulGlobal_step (hψ : 0 < ψ) (hn : 1 < n) (ring : DirectedRing n)
    (C : Fin n → UCell ψ κ) (hC : PeacefulGlobal ring C) (e : Fin n) :
    PeacefulGlobal ring (LabelFreeElimination.step hψ ring C e) := by
  unfold PeacefulGlobal
  rw [LabelFreeElimination.observe_step]
  exact ⟨hasLeader_rawStep hn ring _ hC.2 hC.1 e, nearest_rawStep hn ring _ hC.2 e⟩

/-- Closure for every literal finite scheduler word, with no erased edges,
restarts, or assumed future physical conditions. -/
theorem peacefulGlobal_run (hψ : 0 < ψ) (hn : 1 < n) (ring : DirectedRing n)
    (C : Fin n → UCell ψ κ) (hC : PeacefulGlobal ring C) (es : List (Fin n)) :
    PeacefulGlobal ring (run (LabelFreeElimination.step hψ ring) C es) := by
  induction es generalizing C with
  | nil => exact hC
  | cons e es ih => exact ih _ (peacefulGlobal_step hψ hn ring C hC e)

/-- The current leader witness gives a strictly positive sum of the actual
finite carrier's leader bits. This lower bound is preserved by every word. -/
theorem peacefulGlobal_count_pos (ring : DirectedRing n) (C : Fin n → UCell ψ κ)
    (hC : PeacefulGlobal ring C) : 0 < K2FiniteProgress.count C := by
  obtain ⟨p, hp⟩ := hC.1
  obtain ⟨k, hk, _⟩ := List.mem_iff_getElem.mp
    ((K2CyclicLayout.mem_leaderSites (LabelFreeElimination.observe C) p).mpr hp)
  have hh : k < K2FiniteProgress.count C := by
    simpa only [K2CyclicLayout.leaderSites_length, ← K2FiniteProgress.count_eq_observe] using hk
  omega

/-- The exact sum of finite leader bits being one identifies a unique
physical leader through the already proved enumeration of leader sites. -/
theorem count_one_unique (C : Fin n → UCell ψ κ) (hc : K2FiniteProgress.count C = 1) :
    hasUniqueLeader n (LabelFreeElimination.observe C) := by
  have hl : (K2CyclicLayout.leaderSites (LabelFreeElimination.observe C)).length = 1 :=
    (K2CyclicLayout.leaderSites_length _).trans hc
  obtain ⟨p, hp⟩ := List.length_eq_one_iff.mp hl
  refine ⟨p, ?_, ?_⟩
  · apply (K2CyclicLayout.mem_leaderSites _ p).mp
    rw [hp]
    simp
  · intro j hj
    have hm := (K2CyclicLayout.mem_leaderSites _ j).mpr hj
    simpa only [hp, List.mem_singleton] using hm

/-- At count one, the proved multileader class supplies every field of the
already accepted output-safety predicate on the same physical observation. -/
theorem count_one_signalSafe (ring : DirectedRing n) (C : Fin n → UCell ψ κ)
    (hC : PeacefulGlobal ring C) (hc : K2FiniteProgress.count C = 1) :
    LabelFreeElimination.SignalSafe ring C := by
  apply rowSafe_of_outputSafe (by decide) ring (LabelFreeElimination.observe C)
  refine ⟨count_one_unique C hc, ?_, nearest_implies_literal ring _ hC.2, ?_⟩
  · intro i _
    exact Subsingleton.elim _ _
  · intro i
    dsimp only
    intro hi
    exact False.elim (hi (Subsingleton.elim _ _))

/-- Count one in the proved closed class enters semantic unique-leader
output safety for the actual finite label-free protocol and all its futures. -/
theorem count_one_isSafe (hψ : 0 < ψ) (hn : 1 < n) (ring : DirectedRing n)
    (C : Fin n → UCell ψ κ) (hC : PeacefulGlobal ring C) (hc : K2FiniteProgress.count C = 1) :
    PopulationProtocol.IsSafe (LabelFreeElimination.protocol hψ κ) ring C id :=
  LabelFreeElimination.isSafe hψ hn ring C (count_one_signalSafe ring C hC hc)

/-- The existing nondivisible two-leader example contains a real live
bullet. Its nearest supporting leader is at clockwise distance one. -/
theorem seed5_peaceful : PeacefulGlobal LabelFreeElimination.NondivisibleExample.ring5
    LabelFreeElimination.NondivisibleExample.seed5 := by
  refine ⟨⟨0, by decide⟩, ?_⟩
  intro i hi
  have hloc : ∀ j : Fin 5,
      (LabelFreeElimination.observe LabelFreeElimination.NondivisibleExample.seed5 j).bullet = 2 → j = 4 := by
    decide
  have hi4 := hloc i hi
  subst i
  refine ⟨1, by decide, by decide, by decide, ?_, ?_⟩
  · intro k _
    rfl
  · intro k hk
    have : k = 0 := by omega
    subst k
    decide

/-- The same two physical edges reduce two leaders to one and enter the
proved semantic safe set through multileader peacefulness closure. -/
theorem seed5_two_edges_safe :
    PopulationProtocol.IsSafe (LabelFreeElimination.protocol (by decide) 1)
      LabelFreeElimination.NondivisibleExample.ring5
      (run (LabelFreeElimination.step (by decide) LabelFreeElimination.NondivisibleExample.ring5)
        LabelFreeElimination.NondivisibleExample.seed5 [3, 2]) id :=
  count_one_isSafe (by decide) (by decide) _ _
    (peacefulGlobal_run (by decide) (by decide) _ _ seed5_peaceful [3, 2])
    K2FiniteProgress.seed5_true_count_deletion.2

end K2PeacefulGlobal

#print axioms K2PeacefulGlobal.nearest_rawStep
#print axioms K2PeacefulGlobal.hasLeader_rawStep
#print axioms K2PeacefulGlobal.peacefulGlobal_step
#print axioms K2PeacefulGlobal.peacefulGlobal_run
#print axioms K2PeacefulGlobal.peacefulGlobal_count_pos
#print axioms K2PeacefulGlobal.count_one_signalSafe
#print axioms K2PeacefulGlobal.count_one_isSafe
#print axioms K2PeacefulGlobal.seed5_peaceful
#print axioms K2PeacefulGlobal.seed5_two_edges_safe
