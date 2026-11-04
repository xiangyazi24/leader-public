import Leader.AAFJ.BarrierAlgebra

/-!
# Exact support transport for a non-colliding AAFJ barrier advance

This is a deterministic bridge for the original AAFJ `P_k` protocol.  The
existing barrier algebra proves only a cardinality upper bound after an
advance.  Here we retain the actual support information under the hypothesis
that the edge immediately after the selected edge is not charged.  This is
the local fact needed before a two-barrier gap argument; no scheduler or
probability claim is made here.
-/

namespace AAFJPK
namespace BarrierAlgebra

/-- The physical edge map induced by a non-colliding advance at `e`. -/
def redirectEdge {n : Nat} (ring : DirectedRing n) (e i : Fin n) : Fin n :=
  if i = e then ring.rightNeighbor e else i

private theorem redirectEdge_eq_self_of_ne {n : Nat}
    (ring : DirectedRing n) (e i : Fin n) (h : i ≠ e) :
    redirectEdge ring e i = i := by
  simp [redirectEdge, h]

private theorem redirectEdge_eq_next {n : Nat}
    (ring : DirectedRing n) (e : Fin n) :
    redirectEdge ring e e = ring.rightNeighbor e := by
  simp [redirectEdge]

/-- Exact membership transport for a label advance whose successor edge was
uncharged before the advance.

The support is represented by the source module's canonical `List`; the
statement deliberately uses membership rather than list equality because a
physical wrap at the end of the ring changes the order of the mapped list.
-/
theorem barrierSupport_mem_iff_of_not_barrier_edgePlus
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n) (hn2 : 1 < n)
    (L : Labels n k) (e : Fin n)
    (hnext : ¬ BarrierAt hk ring L (ring.rightNeighbor e)) (j : Fin n) :
    j ∈ barrierSupport hk ring (advanceLabels hk ring L e) ↔
      ∃ i, i ∈ barrierSupport hk ring L ∧
        redirectEdge ring e i = j := by
  let r : Fin n := ring.rightNeighbor e
  have hre : r ≠ e := rightNeighbor_ne_self ring hn2 e
  have her : e ≠ r := Ne.symm hre
  have hnext_zero : defect hk ring L r = zeroResidue hk := by
    exact Decidable.not_not.mp hnext
  constructor
  · intro hj
    have hjbar : BarrierAt hk ring (advanceLabels hk ring L e) j :=
      (mem_barrierSupport_iff hk ring (advanceLabels hk ring L e) j).mp hj
    by_cases hje : j = e
    · subst j
      have hrepair := defect_advance_edge hk ring hn2 L e
      exact (hjbar hrepair).elim
    · by_cases hjr : j = r
      · subst j
        have hebar : BarrierAt hk ring L e := by
          unfold BarrierAt at hjbar ⊢
          intro hezero
          apply hjbar
          rw [defect_advance_edgePlus hk ring hn2 L e, hezero,
            hnext_zero]
          apply Fin.ext
          change (0 + 0) % k = 0
          exact Nat.zero_mod k
        have hm : e ∈ barrierSupport hk ring L :=
          (mem_barrierSupport_iff hk ring L e).mpr hebar
        exact ⟨e, hm, redirectEdge_eq_next ring e⟩
      · have hsame := defect_advance_other hk ring L e j hje hjr
        have hjpre : BarrierAt hk ring L j := by
          unfold BarrierAt at hjbar ⊢
          intro hjzero
          apply hjbar
          rw [hsame, hjzero]
        have hm : j ∈ barrierSupport hk ring L :=
          (mem_barrierSupport_iff hk ring L j).mpr hjpre
        exact ⟨j, hm, redirectEdge_eq_self_of_ne ring e j hje⟩
  · rintro ⟨i, hi, hijeq⟩
    have hibar : BarrierAt hk ring L i :=
      (mem_barrierSupport_iff hk ring L i).mp hi
    by_cases hie : i = e
    · subst i
      have hjr : j = r := by
        simpa [redirectEdge, r] using hijeq.symm
      rw [hjr]
      have hpost : BarrierAt hk ring (advanceLabels hk ring L e) r := by
        unfold BarrierAt at hibar ⊢
        intro hzero
        apply hibar
        change defect hk ring (advanceLabels hk ring L e)
          (ring.rightNeighbor e) = zeroResidue hk at hzero
        rw [defect_advance_edgePlus hk ring hn2 L e] at hzero
        rw [hnext_zero] at hzero
        have hadd : defect hk ring L e + zeroResidue hk =
            defect hk ring L e := by
          apply Fin.ext
          change ((defect hk ring L e).val + 0) % k =
            (defect hk ring L e).val
          rw [Nat.add_zero, Nat.mod_eq_of_lt (defect hk ring L e).isLt]
        rw [hadd] at hzero
        exact hzero
      exact (mem_barrierSupport_iff hk ring
        (advanceLabels hk ring L e) r).mpr hpost
    · have hije : i ≠ r := by
        intro hir
        apply hnext
        simpa [hir] using hibar
      have hsame := defect_advance_other hk ring L e i hie hije
      have hpost : BarrierAt hk ring (advanceLabels hk ring L e) i := by
        unfold BarrierAt at hibar ⊢
        intro hzero
        apply hibar
        rw [hsame] at hzero
        exact hzero
      have hm := (mem_barrierSupport_iff hk ring
        (advanceLabels hk ring L e) i).mpr hpost
      have hij : i = j := by
        simpa [redirectEdge, hie] using hijeq
      simpa [hij] using hm

/-- The same exact support transport for a genuine packaged Protocol-6
advance.  This is the source-level consumer of the preceding label theorem.
-/
theorem protocol_barrierSupport_mem_iff_of_not_barrier_edgePlus
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n) (hn2 : 1 < n)
    (C : Fin n → State k) (e : Fin n)
    (hready : AdvanceReady hk ring C e)
    (hnext : ¬ BarrierAt hk ring (labelsOf C) (ring.rightNeighbor e))
    (j : Fin n) :
    j ∈ barrierSupport hk ring
        (labelsOf ((protocol k hk).step ring C e)) ↔
      ∃ i, i ∈ barrierSupport hk ring (labelsOf C) ∧
        redirectEdge ring e i = j := by
  rw [labelsOf_step_eq_advance_of_ready hk ring hn2 C e hready]
  exact barrierSupport_mem_iff_of_not_barrier_edgePlus hk ring hn2
    (labelsOf C) e hnext j

#check barrierSupport_mem_iff_of_not_barrier_edgePlus
#check protocol_barrierSupport_mem_iff_of_not_barrier_edgePlus
#print axioms barrierSupport_mem_iff_of_not_barrier_edgePlus
#print axioms protocol_barrierSupport_mem_iff_of_not_barrier_edgePlus

end BarrierAlgebra

/-! ## Exact classifiers for the two mover-balance exceptions -/

/-- A phase-zero barrier arm with a probe-free head leaves that head
probe-free exactly when the head is already a leader.  This is the source
level classifier for the fast-arm exception in the mover-balance ledger. -/
theorem transition_barrier_phase_zero_headProbe_false_iff_leader
    {k : Nat} (hk : 0 < k) (u v : State k)
    (hbar : IsBarrier hk u v)
    (hphase : u.phase = false)
    (hprobe : v.probe = false) :
    (transition hk u v).2.probe = false ↔ v.leader = true := by
  rw [transition_of_barrier hk u v hbar]
  rw [barrierStep_phase_zero hk u v hphase]
  cases hv : v.leader <;> simp [hv, hprobe]

/-- On an ordinary successor edge out of a blocked head, the head probe
survives exactly in the responder-leader-with-bullet branch.  This is the
source level classifier for the stubborn leader exception. -/
theorem transition_nonbarrier_headProbe_survives_iff_leader_bullet
    {k : Nat} (hk : 0 < k) (u v : State k)
    (hbar : ¬ IsBarrier hk u v)
    (hprobe : u.probe = true) :
    (transition hk u v).1.probe = true ↔
      v.leader = true ∧ v.bullet = true := by
  rw [transition_of_nonbarrier hk u v hbar]
  cases hv : v.leader <;>
    cases hb : v.bullet <;>
    simp [nonBarrierStep, hv, hb, hprobe]

#check AAFJPK.transition_barrier_phase_zero_headProbe_false_iff_leader
#check AAFJPK.transition_nonbarrier_headProbe_survives_iff_leader_bullet
#print axioms AAFJPK.transition_barrier_phase_zero_headProbe_false_iff_leader
#print axioms AAFJPK.transition_nonbarrier_headProbe_survives_iff_leader_bullet

end AAFJPK
