import Leader.Wu.Elimination.AdjacentLeaderPeaceful

/-!
# Individual nearest support and old live-bullet origins

All rows are the frozen elimination/collision component on the existing UCell.
The observer below this module only reads fields; it supplies no protocol state.
The interval predicate is the existing K2PeacefulGlobal.Support.
-/

namespace K2NearestSupportEntry

open PPLL PPLLRepair LDSinkKernelC K2OutputSafety LDSinkBoundedKernel
  StateBoundUnifiedCell PPLLNoCheckBirthConditionTwoGeometry
  PPLLNoCheckBirthConditionTwoPhysical PPLLNoCheckBirthConditionTwoProtocol
  K2PeacefulGlobal LabelFreeElimination

set_option autoImplicit false
set_option Elab.async false

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
  (l.leader = true → q.1.leader = false → r.bullet = 2) ∧
  (l.leader = false → q.2.bullet ≠ 2) ∧
  (l.leader = true → r.leader = false → q.2.bullet ≠ 2)

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

theorem literal_row_facts (l r : AgentState 1) : RowFacts l r (sinkKernelC (by decide) l r) := by
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

theorem raw_target_fields (hn : 1 < n) (ring : DirectedRing n)
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
      (literal_row_facts (C e) (C r)).1 hl hsh hz
  · by_cases hr : target = r
    · subst target
      simpa only [updatePair_responder _ _ _ _ hne] using
        (literal_row_facts (C e) (C r)).2.1 hl hsh hz
    · simpa only [updatePair_other _ _ _ _ _ he hr] using And.intro hl hsh

theorem support_signals (hn : 1 < n) (ring : DirectedRing n)
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
    exact (literal_row_facts (C e) (C r)).2.2.1 (he ▸ hz)
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
        exact (literal_row_facts (C e) (C r)).2.2.2.1 hleft hzero (hr ▸ hz)
    · change (updatePair C e r _ m).signal_B = 0
      rw [updatePair_other _ _ _ _ _ he hr]
      exact hz

theorem raw_support_kept (hn : 1 < n) (ring : DirectedRing n)
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
    exact (literal_row_facts (C e) (C (ring.rightNeighbor e))).2.2.2.2.1 hq
  · intro k hk
    exact K2GlobalGapClosure.rawStep_follower (by decide) ring C e _ (hs.before_follower k hk)

theorem raw_support_moved (hn : 1 < n) (ring : DirectedRing n)
    (C : Fin n → AgentState 1) (e : Fin n) (d : Nat)
    (hs : Support ring C (ring.rightNeighbor e) d)
    (hl : (C e).leader = false) (hb : (C (ring.rightNeighbor e)).bullet = 2) :
    Support ring (rawStep (by decide) ring C e) e (d + 1) := by
  let r := ring.rightNeighbor e
  have hz : (C r).signal_B = 0 := by simpa using hs.signal_zero 0 (by omega)
  have hmove := (literal_row_facts (C e) (C r)).2.2.2.2.2.2.2.2.1 hl hb hz
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

/-- An actual FIRE produces zero-distance nearest support. -/
theorem raw_fresh_support (ring : DirectedRing n) (C : Fin n → AgentState 1)
    (e : Fin n) (hl : (C e).leader = true) (hz : (C e).signal_B = 1) :
    Support ring (rawStep (by decide) ring C e) e 0 := by
  have hf := (literal_row_facts (C e) (C (ring.rightNeighbor e))).2.2.2.2.2.1 hl hz
  refine ⟨ring.hn, ?_, ?_, ?_, ?_⟩
  · simpa only [cwPos_zero, rawStep, updatePair_initiator] using hf.1
  · simpa only [cwPos_zero, rawStep, updatePair_initiator] using hf.2.1
  · intro k hk
    have : k = 0 := by omega
    subst k
    simpa only [cwPos_zero, rawStep, updatePair_initiator] using hf.2.2
  · intro k hk; omega

/-- Support of one inherited live bullet is preserved even when all other
live bullets are arbitrary. Collision may extend its interval by one edge. -/
theorem support_inherited_same (hψ : 0 < ψ) (hn : 1 < n) (ring : DirectedRing n)
    (C : Fin n → UCell ψ κ) (e p : Fin n) (d : Nat)
    (hs : Support ring (observe C) p d)
    (hb : (observe (AdjacentLeaderElimination.step hψ ring C e) p).bullet = 2) :
    ∃ d', Support ring (observe (AdjacentLeaderElimination.step hψ ring C e)) p d' := by
  by_cases hc : (C e).legacy.leader = true ∧
      (C (ring.rightNeighbor e)).legacy.leader = true
  · by_cases ht : cwPos ring p d = e
    · exact ⟨d + 1, AdjacentLeaderPeaceful.support_extended hψ hn ring C e p d
        hc.1 hc.2 hs ht⟩
    · exact ⟨d, AdjacentLeaderPeaceful.support_kept hψ ring C e p d hc.1 hc.2 hs ht⟩
  · rw [AdjacentLeaderElimination.step_eq_old hψ ring C e hc,
      LabelFreeElimination.observe_step] at hb ⊢
    exact ⟨d, raw_support_kept hn ring (observe C) e p d hs hb⟩

/-- Actual follower transport of an individually supported live bullet. -/
theorem support_inherited_move (hψ : 0 < ψ) (hn : 1 < n) (ring : DirectedRing n)
    (C : Fin n → UCell ψ κ) (e : Fin n) (d : Nat)
    (hs : Support ring (observe C) (ring.rightNeighbor e) d)
    (hl : (C e).legacy.leader = false) (hb : (C (ring.rightNeighbor e)).legacy.bullet = 2) :
    Support ring (observe (AdjacentLeaderElimination.step hψ ring C e)) e (d + 1) := by
  have hc : ¬ ((C e).legacy.leader = true ∧
      (C (ring.rightNeighbor e)).legacy.leader = true) := by simp [hl]
  rw [AdjacentLeaderElimination.step_eq_old hψ ring C e hc,
    LabelFreeElimination.observe_step]
  exact raw_support_moved hn ring (observe C) e d hs hl hb

/-- The adjacent winner supports a live bullet sitting at its own site. -/
theorem collision_right_support (hψ : 0 < ψ) (hn : 1 < n) (ring : DirectedRing n)
    (C : Fin n → UCell ψ κ) (e : Fin n)
    (hl : (C e).legacy.leader = true)
    (hr : (C (ring.rightNeighbor e)).legacy.leader = true) :
    Support ring (observe (AdjacentLeaderElimination.step hψ ring C e))
      (ring.rightNeighbor e) 0 := by
  apply AdjacentLeaderPeaceful.support_zero
  · exact (AdjacentLeaderElimination.step_leader_away hψ ring C e _
      (rightNeighbor_ne_self_of_one_lt ring hn e)).trans hr
  · exact AdjacentLeaderElimination.adjacent_shield hψ hn ring C e hl hr
  · exact AdjacentLeaderElimination.adjacent_signal_zero hψ ring C e _ hl hr
      (Or.inr (Or.inl rfl))

/-- The collision loser is now a follower with nearest support at the winner. -/
theorem collision_left_support (hψ : 0 < ψ) (hn : 1 < n) (ring : DirectedRing n)
    (C : Fin n → UCell ψ κ) (e : Fin n)
    (hl : (C e).legacy.leader = true)
    (hr : (C (ring.rightNeighbor e)).legacy.leader = true) :
    Support ring (observe (AdjacentLeaderElimination.step hψ ring C e)) e 1 := by
  have hs := collision_right_support hψ hn ring C e hl hr
  have hpos : cwPos ring e 1 = ring.rightNeighbor e := by
    simpa using cwPos_succ ring e 0
  refine ⟨hn, ?_, ?_, ?_, ?_⟩
  · rw [hpos]; simpa using hs.target_leader
  · rw [hpos]; simpa using hs.target_shield
  · intro k hk
    have : k = 0 ∨ k = 1 := by omega
    rcases this with rfl | rfl
    · rw [cwPos_zero]
      exact AdjacentLeaderElimination.adjacent_signal_zero hψ ring C e e hl hr (Or.inl rfl)
    · rw [hpos]; simpa using hs.signal_zero 0 (Nat.le_refl _)
  · intro k hk
    have : k = 0 := by omega
    subst k
    rw [cwPos_zero]
    exact AdjacentLeaderElimination.adjacent_deletes_source hψ ring C e hl hr

/-- A current unsupported live bullet; this is a proof observation only. -/
def Bad (ring : DirectedRing n) (C : Fin n → UCell ψ κ) (p : Fin n) : Prop :=
  (C p).legacy.bullet = 2 ∧ ¬ ∃ d, Support ring (observe C) p d

/-- After every actual row, the responder has no unsupported live bullet.
A noncollision row clears/demotes it; a collision shields its leader. -/
theorem responder_not_bad (hψ : 0 < ψ) (hn : 1 < n) (ring : DirectedRing n)
    (C : Fin n → UCell ψ κ) (e : Fin n) :
    ¬ Bad ring (AdjacentLeaderElimination.step hψ ring C e) (ring.rightNeighbor e) := by
  intro hb
  by_cases hc : (C e).legacy.leader = true ∧
      (C (ring.rightNeighbor e)).legacy.leader = true
  · exact hb.2 ⟨0, collision_right_support hψ hn ring C e hc.1 hc.2⟩
  · have hq : (sinkKernelC (by decide) (observe C e)
        (observe C (ring.rightNeighbor e))).2.bullet = 2 := by
      have hh : (observe (AdjacentLeaderElimination.step hψ ring C e)
          (ring.rightNeighbor e)).bullet = 2 := hb.1
      rw [AdjacentLeaderElimination.step_eq_old hψ ring C e hc,
        LabelFreeElimination.observe_step] at hh
      simpa only [rawStep, updatePair_responder _ _ _ _
        (rightNeighbor_ne_self_of_one_lt ring hn e)] using hh
    have hf := literal_row_facts (observe C e) (observe C (ring.rightNeighbor e))
    cases hl : (C e).legacy.leader with
    | false => exact hf.2.2.2.2.2.2.2.2.2.2.1 hl hq
    | true =>
      have hr : (C (ring.rightNeighbor e)).legacy.leader = false := by
        cases h : (C (ring.rightNeighbor e)).legacy.leader <;> simp_all
      exact hf.2.2.2.2.2.2.2.2.2.2.2 hl hr hq

/-- Location update of an old proof mark. Several old marks may share one
physical live bullet after an overwrite. No identity is stored in UCell. -/
def nextPos (ring : DirectedRing n) (C : Fin n → UCell ψ κ) (e p : Fin n) : Fin n :=
  if p = ring.rightNeighbor e ∧ (C e).legacy.leader = false then e else p

/-- Every unsupported output live has an unsupported input live origin.
Fresh FIRE and the two collision endpoints are discharged physically. -/
theorem bad_origin (hψ : 0 < ψ) (hn : 1 < n) (ring : DirectedRing n)
    (C : Fin n → UCell ψ κ) (e p : Fin n)
    (hb : Bad ring (AdjacentLeaderElimination.step hψ ring C e) p) :
    ∃ q, Bad ring C q ∧ nextPos ring C e q = p := by
  have hne := rightNeighbor_ne_self_of_one_lt ring hn e
  have hpr : p ≠ ring.rightNeighbor e := by
    intro he; subst p; exact responder_not_bad hψ hn ring C e hb
  have hold_bad : ∀ q, (C q).legacy.bullet = 2 →
      (observe (AdjacentLeaderElimination.step hψ ring C e) q).bullet = 2 →
      ¬ (∃ d, Support ring (observe (AdjacentLeaderElimination.step hψ ring C e)) q d) →
      Bad ring C q := by
    intro q hq hpost hbad
    refine ⟨hq, ?_⟩
    rintro ⟨d, hs⟩
    exact hbad (support_inherited_same hψ hn ring C e q d hs hpost)
  by_cases hc : (C e).legacy.leader = true ∧
      (C (ring.rightNeighbor e)).legacy.leader = true
  · have hpe : p ≠ e := by
      intro he; subst p; exact hb.2 ⟨1, collision_left_support hψ hn ring C e hc.1 hc.2⟩
    refine ⟨p, hold_bad p ?_ hb.1 hb.2, ?_⟩
    · rw [← AdjacentLeaderElimination.adjacent_bullet hψ ring C e p hc.1 hc.2]
      exact hb.1
    · simp [nextPos, hpr]
  · have hraw : Bad ring (AdjacentLeaderElimination.step hψ ring C e) p := hb
    have hbul : (rawStep (by decide) ring (observe C) e p).bullet = 2 := by
      have hh : (observe (AdjacentLeaderElimination.step hψ ring C e) p).bullet = 2 := hb.1
      rwa [AdjacentLeaderElimination.step_eq_old hψ ring C e hc,
        LabelFreeElimination.observe_step] at hh
    by_cases hpe : p = e
    · subst p
      have hq : (sinkKernelC (by decide) (observe C e)
          (observe C (ring.rightNeighbor e))).1.bullet = 2 := by
        simpa only [rawStep, updatePair_initiator] using hbul
      rcases (literal_row_facts (observe C e) (observe C (ring.rightNeighbor e))).2.2.2.2.2.2.1 hq
        with hold | hfire | hmove
      · refine ⟨e, hold_bad e hold hb.1 hb.2, ?_⟩
        simp [nextPos, Ne.symm hne]
      · apply False.elim
        apply hb.2
        rw [AdjacentLeaderElimination.step_eq_old hψ ring C e hc,
          LabelFreeElimination.observe_step]
        exact ⟨0, raw_fresh_support ring (observe C) e hfire.1 hfire.2⟩
      · refine ⟨ring.rightNeighbor e, ⟨hmove.1, ?_⟩, ?_⟩
        · rintro ⟨d, hs⟩
          exact hb.2 ⟨d + 1, support_inherited_move hψ hn ring C e d hs hmove.2 hmove.1⟩
        · simp [nextPos, show (C e).legacy.leader = false from hmove.2]
    · refine ⟨p, hold_bad p ?_ hb.1 hb.2, ?_⟩
      · change (observe C p).bullet = 2
        simpa only [rawStep, updatePair_other _ _ _ _ _ hpe hpr] using hbul
      · simp [nextPos, hpr]

namespace Example

def ring2 : DirectedRing 2 := ⟨by decide⟩

/-- Both old live bullets are unsupported. Labels/controllers are ordinary
existing cell values; collision changes only the actual four signal fields. -/
def seed (i : Fin 2) : UCell 2 1 :=
  { legacy := { K2OutputSafety.boundedCanonical (by decide) 1 i with
      leader := true, label := 1, shield := false, bullet := 2, signal_B := 1 }
    control := (K2OutputSafety.finiteCut 0).control }

theorem initially_bad (i : Fin 2) : Bad ring2 seed i := by
  refine ⟨rfl, ?_⟩
  rintro ⟨d, hs⟩
  have hz := hs.signal_zero 0 (Nat.zero_le _)
  have hf : (1 : Fin 2) = 0 := hz
  cases hf

theorem collision_enters :
    NearestPeaceful ring2 (observe (AdjacentLeaderElimination.step (by decide) ring2 seed 0)) ∧
    (AdjacentLeaderElimination.step (by decide) ring2 seed 0 1).legacy.leader = true := by
  constructor
  · intro p _
    have hp : p = 0 ∨ p = 1 := by
      have := p.isLt
      by_cases h : p.val = 0
      · exact Or.inl (Fin.ext h)
      · exact Or.inr (Fin.ext (by omega))
    rcases hp with rfl | rfl
    · exact ⟨1, collision_left_support (by decide) (by decide) ring2 seed 0 rfl rfl⟩
    · exact ⟨0, collision_right_support (by decide) (by decide) ring2 seed 0 rfl rfl⟩
  · decide

end Example

end K2NearestSupportEntry

#print axioms K2NearestSupportEntry.literal_row_facts
#print axioms K2NearestSupportEntry.support_inherited_same
#print axioms K2NearestSupportEntry.support_inherited_move
#print axioms K2NearestSupportEntry.responder_not_bad
#print axioms K2NearestSupportEntry.bad_origin
