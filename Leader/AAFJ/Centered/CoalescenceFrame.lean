import Leader.AAFJ.Centered.Protocol

/-!
# Local support frame for centered AAFJ coalescence

This module records the exact charged-support effect of one centered
phase-one advance.  A trial must stop before transporting any lineage tag when
the support count drops; the pointwise facts here are the deterministic layer
needed to detect that event.
-/

namespace AAFJPK
namespace CenteredRenewal
namespace CoalescenceFrame

open BarrierAlgebra

set_option autoImplicit false

/-- The advanced source edge is no longer charged. -/
theorem advance_source_not_barrier {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (hn2 : 1 < n)
    (L : Labels n k) (e : Fin n) :
    ¬ BarrierAt hk ring (advanceLabels hk ring L e) e :=
  advance_repairs_edge hk ring hn2 L e

/-- The successor edge is charged after an advance exactly when the sum of
its old charge and the moving charge is nonzero. -/
theorem advance_successor_barrier_iff {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (hn2 : 1 < n)
    (L : Labels n k) (e : Fin n) :
    BarrierAt hk ring (advanceLabels hk ring L e) (ring.rightNeighbor e) ↔
      defect hk ring L e + defect hk ring L (ring.rightNeighbor e) ≠
        zeroResidue hk := by
  unfold BarrierAt
  rw [defect_advance_edgePlus hk ring hn2 L e]

/-- Every edge outside the source/successor pair keeps exactly the same
charged-support membership. -/
theorem advance_other_barrier_iff {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (L : Labels n k) (e j : Fin n)
    (hje : j ≠ e) (hjr : j ≠ ring.rightNeighbor e) :
    BarrierAt hk ring (advanceLabels hk ring L e) j ↔
      BarrierAt hk ring L j := by
  unfold BarrierAt
  rw [defect_advance_other hk ring L e j hje hjr]

/-- If the successor was uncharged, a genuine moving charge remains nonzero
there.  This is the local no-collision transport fact. -/
theorem advance_successor_barrier_of_source_of_successor_free
    {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (hn2 : 1 < n)
    (L : Labels n k) (e : Fin n)
    (he : BarrierAt hk ring L e)
    (hr : ¬ BarrierAt hk ring L (ring.rightNeighbor e)) :
    BarrierAt hk ring (advanceLabels hk ring L e) (ring.rightNeighbor e) := by
  rw [advance_successor_barrier_iff hk ring hn2 L e]
  unfold BarrierAt at he hr
  have hrzero : defect hk ring L (ring.rightNeighbor e) = zeroResidue hk :=
    Decidable.not_not.mp hr
  rw [hrzero]
  have hadd : defect hk ring L e + zeroResidue hk = defect hk ring L e := by
    apply Fin.ext
    change ((defect hk ring L e).val + 0) % k = (defect hk ring L e).val
    rw [Nat.add_zero, Nat.mod_eq_of_lt (defect hk ring L e).isLt]
  rw [hadd]
  exact he

/-- Advancing a charged edge into an already charged successor strictly drops
the support count.  Cancellation may remove two barriers; this theorem does
not assume which charge survives. -/
theorem barrierCount_advance_lt_of_source_and_successor_barriers
    {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (hn2 : 1 < n)
    (L : Labels n k) (e : Fin n)
    (he : BarrierAt hk ring L e)
    (hr : BarrierAt hk ring L (ring.rightNeighbor e)) :
    barrierCount hk ring (advanceLabels hk ring L e) <
      barrierCount hk ring L := by
  let D := advanceLabels hk ring L e
  let old := barrierSupport hk ring L
  let fresh := barrierSupport hk ring D
  have heMem : e ∈ old := by
    exact (mem_barrierSupport_iff hk ring L e).2 he
  have hsub : fresh ⊆ old.erase e := by
    intro j hj
    have hjbar : BarrierAt hk ring D j :=
      (mem_barrierSupport_iff hk ring D j).1 hj
    have hje : j ≠ e := by
      intro h
      subst j
      exact (advance_source_not_barrier hk ring hn2 L e) hjbar
    apply (List.Nodup.mem_erase_iff (barrierSupport_nodup hk ring L)).2
    refine ⟨hje, ?_⟩
    apply (mem_barrierSupport_iff hk ring L j).2
    by_cases hjr : j = ring.rightNeighbor e
    · simpa [hjr] using hr
    · exact (advance_other_barrier_iff hk ring L e j hje hjr).1 hjbar
  have hlen : fresh.length ≤ (old.erase e).length :=
    (barrierSupport_nodup hk ring D).length_le_of_subset hsub
  have herase : (old.erase e).length = old.length - 1 :=
    List.length_erase_of_mem heMem
  have holdPos : 0 < old.length := List.length_pos_of_mem heMem
  unfold barrierCount
  change fresh.length < old.length
  rw [herase] at hlen
  omega

/-- If the moving barrier enters an uncharged successor, support size is
preserved exactly: the source support element is replaced by its successor. -/
theorem barrierCount_advance_eq_of_source_barrier_successor_free
    {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (hn2 : 1 < n)
    (L : Labels n k) (e : Fin n)
    (he : BarrierAt hk ring L e)
    (hr : ¬ BarrierAt hk ring L (ring.rightNeighbor e)) :
    barrierCount hk ring (advanceLabels hk ring L e) =
      barrierCount hk ring L := by
  classical
  let r := ring.rightNeighbor e
  let D := advanceLabels hk ring L e
  let old := barrierSupport hk ring L
  let fresh := barrierSupport hk ring D
  let candidate := r :: old.erase e
  have heMem : e ∈ old :=
    (mem_barrierSupport_iff hk ring L e).2 he
  have hrNotMem : r ∉ old := by
    intro h
    exact hr ((mem_barrierSupport_iff hk ring L r).1 h)
  have hcandNodup : candidate.Nodup := by
    rw [show candidate = r :: old.erase e by rfl, List.nodup_cons]
    constructor
    · intro h
      exact hrNotMem (List.mem_of_mem_erase h)
    · exact (barrierSupport_nodup hk ring L).erase e
  have hrFresh : r ∈ fresh := by
    apply (mem_barrierSupport_iff hk ring D r).2
    simpa [D, r] using
      (advance_successor_barrier_of_source_of_successor_free hk ring hn2
        L e he hr)
  have hperm : fresh.Perm candidate := by
    apply (List.perm_ext_iff_of_nodup
      (barrierSupport_nodup hk ring D) hcandNodup).2
    intro j
    constructor
    · intro hj
      have hjbar : BarrierAt hk ring D j :=
        (mem_barrierSupport_iff hk ring D j).1 hj
      by_cases hjr : j = r
      · simp [candidate, hjr]
      · have hje : j ≠ e := by
          intro h
          subst j
          exact (advance_source_not_barrier hk ring hn2 L e) hjbar
        have hjold : j ∈ old := by
          apply (mem_barrierSupport_iff hk ring L j).2
          exact (advance_other_barrier_iff hk ring L e j hje
            (by simpa [r] using hjr)).1 hjbar
        have hjerase : j ∈ old.erase e :=
          (List.Nodup.mem_erase_iff (barrierSupport_nodup hk ring L)).2
            ⟨hje, hjold⟩
        simp [candidate, hjerase]
    · intro hj
      have hjcases : j = r ∨ j ∈ old.erase e := by
        simpa [candidate] using hj
      rcases hjcases with hjr | hjerase
      · subst j
        exact hrFresh
      · have hjdata :=
          (List.Nodup.mem_erase_iff (barrierSupport_nodup hk ring L)).1
            hjerase
        have hje : j ≠ e := hjdata.1
        have hjold : BarrierAt hk ring L j :=
          (mem_barrierSupport_iff hk ring L j).1 hjdata.2
        have hjr : j ≠ r := by
          intro h
          subst j
          exact hr hjold
        apply (mem_barrierSupport_iff hk ring D j).2
        exact (advance_other_barrier_iff hk ring L e j hje
          (by simpa [r] using hjr)).2 hjold
  have hlen := hperm.length_eq
  have herase : (old.erase e).length = old.length - 1 :=
    List.length_erase_of_mem heMem
  unfold barrierCount
  change fresh.length = old.length
  rw [hlen]
  change (r :: old.erase e).length = old.length
  simp only [List.length_cons, herase]
  have holdPos : 0 < old.length := List.length_pos_of_mem heMem
  omega

/-- Complete pointwise support description for a ready centered physical
step.  No support-count or ancestry convention is hidden in this theorem. -/
theorem protocol_ready_barrierAt_cases {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (hn2 : 1 < n)
    (C : Fin n → State k) (e : Fin n)
    (hready : AdvanceReady hk ring C e) :
    let D : Fin n → State k := (protocol k hk).step ring C e
    (¬ BarrierAt hk ring (labelsOf D) e) ∧
      (BarrierAt hk ring (labelsOf D) (ring.rightNeighbor e) ↔
        defect hk ring (labelsOf C) e +
            defect hk ring (labelsOf C) (ring.rightNeighbor e) ≠
          zeroResidue hk) ∧
      (∀ j : Fin n, j ≠ e → j ≠ ring.rightNeighbor e →
        (BarrierAt hk ring (labelsOf D) j ↔
          BarrierAt hk ring (labelsOf C) j)) := by
  have hlabels := labelsOf_step_eq_advance_of_ready hk ring hn2 C e hready
  dsimp only
  rw [hlabels]
  exact ⟨advance_source_not_barrier hk ring hn2 (labelsOf C) e,
    advance_successor_barrier_iff hk ring hn2 (labelsOf C) e,
    fun j hje hjr =>
      advance_other_barrier_iff hk ring (labelsOf C) e j hje hjr⟩

/-- On a no-collision ready step, the source support membership is transported
to its successor and every other edge is framed. -/
theorem protocol_ready_transport_into_free_successor {n k : Nat}
    (hk : 0 < k) (ring : DirectedRing n) (hn2 : 1 < n)
    (C : Fin n → State k) (e : Fin n)
    (hready : AdvanceReady hk ring C e)
    (hfree : ¬ BarrierAt hk ring (labelsOf C) (ring.rightNeighbor e)) :
    let D : Fin n → State k := (protocol k hk).step ring C e
    (¬ BarrierAt hk ring (labelsOf D) e) ∧
      BarrierAt hk ring (labelsOf D) (ring.rightNeighbor e) ∧
      (∀ j : Fin n, j ≠ e → j ≠ ring.rightNeighbor e →
        (BarrierAt hk ring (labelsOf D) j ↔
          BarrierAt hk ring (labelsOf C) j)) := by
  have hcases := protocol_ready_barrierAt_cases hk ring hn2 C e hready
  dsimp only at hcases ⊢
  refine ⟨hcases.1, ?_, hcases.2.2⟩
  have he : BarrierAt hk ring (labelsOf C) e :=
    (barrierAt_labelsOf_iff hk ring C e).2 hready.1
  have hlabels := labelsOf_step_eq_advance_of_ready hk ring hn2 C e hready
  rw [hlabels]
  exact advance_successor_barrier_of_source_of_successor_free hk ring hn2
    (labelsOf C) e he hfree

/-- A ready centered advance into an occupied successor is exactly a support
drop event.  The trial layer must stop here before attempting tag transport. -/
theorem protocol_ready_barrierCount_lt_of_successor_barrier
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n) (hn2 : 1 < n)
    (C : Fin n → State k) (e : Fin n)
    (hready : AdvanceReady hk ring C e)
    (hoccupied : BarrierAt hk ring (labelsOf C) (ring.rightNeighbor e)) :
    barrierCount hk ring
        (labelsOf ((protocol k hk).step ring C e)) <
      barrierCount hk ring (labelsOf C) := by
  rw [labelsOf_step_eq_advance_of_ready hk ring hn2 C e hready]
  apply barrierCount_advance_lt_of_source_and_successor_barriers hk ring hn2
    (labelsOf C) e
  · exact (barrierAt_labelsOf_iff hk ring C e).2 hready.1
  · exact hoccupied

/-- Conversely, a ready centered advance into an uncharged successor is a
no-drop step. -/
theorem protocol_ready_barrierCount_eq_of_successor_free
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n) (hn2 : 1 < n)
    (C : Fin n → State k) (e : Fin n)
    (hready : AdvanceReady hk ring C e)
    (hfree : ¬ BarrierAt hk ring (labelsOf C) (ring.rightNeighbor e)) :
    barrierCount hk ring
        (labelsOf ((protocol k hk).step ring C e)) =
      barrierCount hk ring (labelsOf C) := by
  rw [labelsOf_step_eq_advance_of_ready hk ring hn2 C e hready]
  apply barrierCount_advance_eq_of_source_barrier_successor_free hk ring hn2
    (labelsOf C) e
  · exact (barrierAt_labelsOf_iff hk ring C e).2 hready.1
  · exact hfree

/-- For a ready centered advance, support drops exactly when the successor is
already occupied.  This is the stopping test for every tagged coalescence
trial. -/
theorem protocol_ready_barrierCount_lt_iff_successor_barrier
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n) (hn2 : 1 < n)
    (C : Fin n → State k) (e : Fin n)
    (hready : AdvanceReady hk ring C e) :
    barrierCount hk ring
          (labelsOf ((protocol k hk).step ring C e)) <
        barrierCount hk ring (labelsOf C) ↔
      BarrierAt hk ring (labelsOf C) (ring.rightNeighbor e) := by
  constructor
  · intro hdrop
    by_cases hoccupied :
        BarrierAt hk ring (labelsOf C) (ring.rightNeighbor e)
    · exact hoccupied
    · have heq := protocol_ready_barrierCount_eq_of_successor_free hk ring hn2
        C e hready hoccupied
      omega
  · intro hoccupied
    exact protocol_ready_barrierCount_lt_of_successor_barrier hk ring hn2
      C e hready hoccupied

/-- A centered protocol step decreases support exactly when its source is
advance-ready and its successor already carries a barrier. -/
theorem protocol_barrierCount_lt_iff_ready_and_successor_barrier
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n) (hn2 : 1 < n)
    (C : Fin n → State k) (e : Fin n) :
    barrierCount hk ring
          (labelsOf ((protocol k hk).step ring C e)) <
        barrierCount hk ring (labelsOf C) ↔
      AdvanceReady hk ring C e ∧
        BarrierAt hk ring (labelsOf C) (ring.rightNeighbor e) := by
  by_cases hready : AdvanceReady hk ring C e
  · rw [protocol_ready_barrierCount_lt_iff_successor_barrier hk ring hn2
      C e hready]
    simp [hready]
  · have hlabels := labelsOf_step_eq_self_of_not_ready hk ring C e hready
    rw [hlabels]
    simp [hready]

/-- Every centered step which is not a collision preserves support count. -/
theorem protocol_barrierCount_eq_of_no_collision
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n) (hn2 : 1 < n)
    (C : Fin n → State k) (e : Fin n)
    (hnocollision : ¬ (AdvanceReady hk ring C e ∧
      BarrierAt hk ring (labelsOf C) (ring.rightNeighbor e))) :
    barrierCount hk ring
        (labelsOf ((protocol k hk).step ring C e)) =
      barrierCount hk ring (labelsOf C) := by
  by_cases hready : AdvanceReady hk ring C e
  · apply protocol_ready_barrierCount_eq_of_successor_free hk ring hn2
      C e hready
    intro hoccupied
    exact hnocollision ⟨hready, hoccupied⟩
  · rw [labelsOf_step_eq_self_of_not_ready hk ring C e hready]

end CoalescenceFrame
end CenteredRenewal
end AAFJPK
