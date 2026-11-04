import Leader.AAFJ.MultiBarrier.TwoSuccessorPush

set_option autoImplicit false

namespace AAFJPK.OriginalPushOne

open BarrierAlgebra
open OriginalNonbarrierWord

theorem barrier_hit_source_controls_public
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (C : Fin n → State k) (e : Fin n)
    (hbar : BarrierAt hk ring (labelsOf C) e) :
    ((protocol k hk).step ring C e e).probe = false ∧
      ((protocol k hk).step ring C e e).phase = true := by
  have hjournal :
      IsBarrier hk (C e) (C (ring.rightNeighbor e)) :=
    (barrierAt_labelsOf_iff hk ring C e).1 hbar
  have hlocal :
      (transition hk (C e) (C (ring.rightNeighbor e))).1.probe = false ∧
        (transition hk (C e) (C (ring.rightNeighbor e))).1.phase = true := by
    rw [transition_of_barrier hk _ _ hjournal]
    cases hphase : (C e).phase with
    | false =>
        rw [barrierStep_phase_zero hk _ _ hphase]
        cases hp : (C e).probe <;> simp [probeHitsBarrier, hp]
    | true =>
        cases hp : (C (ring.rightNeighbor e)).probe with
        | false =>
            rw [barrierStep_phase_one_probe_free hk _ _ hphase hp]
            cases hu : (C e).probe <;>
              simp [probeHitsBarrier, hu, hphase]
        | true =>
            rw [barrierStep_phase_one_probe_blocked hk _ _ hphase hp]
            cases hu : (C e).probe <;>
              simp [probeHitsBarrier, hu, hphase]
  simpa [PopulationProtocol.step, protocol] using hlocal

theorem nonready_exactTwo_q_hit
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (C : Fin n → State k) (q r : Fin n)
    (hs : ExactTwoBarrierSupport hk ring C q r)
    (hnot : ¬ AdvanceReady hk ring C q) :
    let D := (protocol k hk).step ring C q
    labelsOf D = labelsOf C ∧
      ExactTwoBarrierSupport hk ring D q r ∧
      (D q).phase = true ∧ (D q).probe = false := by
  let D := (protocol k hk).step ring C q
  change labelsOf D = labelsOf C ∧
    ExactTwoBarrierSupport hk ring D q r ∧
    (D q).phase = true ∧ (D q).probe = false
  have hbar : BarrierAt hk ring (labelsOf C) q :=
    (hs.2 q).2 (Or.inl rfl)
  have hlabels : labelsOf D = labelsOf C := by
    dsimp [D]
    exact labelsOf_step_eq_self_of_not_ready hk ring C q hnot
  have hsD : ExactTwoBarrierSupport hk ring D q r := by
    refine ⟨hs.1, ?_⟩
    intro e
    rw [hlabels]
    exact hs.2 e
  have hctl :
      (D q).probe = false ∧ (D q).phase = true := by
    simpa [D] using
      barrier_hit_source_controls_public hk ring C q hbar
  exact ⟨hlabels, hsD, hctl.2, hctl.1⟩

theorem exactTwo_ready_q_hit
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (hn2 : 1 < n) (C : Fin n → State k) (q r : Fin n)
    (hs : ExactTwoBarrierSupport hk ring C q r)
    (hsep : ring.rightNeighbor q ≠ r)
    (hready : AdvanceReady hk ring C q) :
    ExactTwoBarrierSupport hk ring
      ((protocol k hk).step ring C q) (ring.rightNeighbor q) r := by
  have hfree :
      ¬ BarrierAt hk ring (labelsOf C) (ring.rightNeighbor q) := by
    intro h
    rcases (hs.2 (ring.rightNeighbor q)).1 h with h | h
    · exact (rightNeighbor_ne_self ring hn2 q) h
    · exact hsep h
  have hrq : r ≠ q := Ne.symm hs.1
  refine ⟨hsep, ?_⟩
  intro e
  constructor
  · intro he
    have hm := (mem_barrierSupport_iff hk ring
      (labelsOf ((protocol k hk).step ring C q)) e).2 he
    rcases
        (protocol_barrierSupport_mem_iff_of_not_barrier_edgePlus
          hk ring hn2 C q hready hfree e).1 hm with
      ⟨i, hi, hmap⟩
    have hiBar :=
      (mem_barrierSupport_iff hk ring (labelsOf C) i).1 hi
    rcases (hs.2 i).1 hiBar with hiq | hir
    · subst i
      left
      simpa [redirectEdge] using hmap.symm
    · subst i
      right
      simpa [redirectEdge, hrq] using hmap.symm
  · intro he
    rcases he with he | he
    · subst e
      apply (mem_barrierSupport_iff hk ring
        (labelsOf ((protocol k hk).step ring C q))
        (ring.rightNeighbor q)).1
      apply (protocol_barrierSupport_mem_iff_of_not_barrier_edgePlus
        hk ring hn2 C q hready hfree (ring.rightNeighbor q)).2
      refine ⟨q, ?_, by simp [redirectEdge]⟩
      exact (mem_barrierSupport_iff hk ring (labelsOf C) q).2
        ((hs.2 q).2 (Or.inl rfl))
    · subst e
      apply (mem_barrierSupport_iff hk ring
        (labelsOf ((protocol k hk).step ring C q)) r).1
      apply (protocol_barrierSupport_mem_iff_of_not_barrier_edgePlus
        hk ring hn2 C q hready hfree r).2
      refine ⟨r, ?_, by simp [redirectEdge, hrq]⟩
      exact (mem_barrierSupport_iff hk ring (labelsOf C) r).2
        ((hs.2 r).2 (Or.inr rfl))

noncomputable def pushWord
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (C : Fin n → State k) (q : Fin n) : List (Fin n) := by
  classical
  exact if AdvanceReady hk ring C q then
    [q]
  else
    [q, ring.rightNeighbor q, ring.rightNeighbor q, q]

theorem exactTwo_push_one
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n) (hn3 : 2 < n)
    (C : Fin n → State k) (q r : Fin n)
    (hs : ExactTwoBarrierSupport hk ring C q r)
    (hsep : ring.rightNeighbor q ≠ r) :
    (pushWord hk ring C q).length ≤ 4 ∧
      ExactTwoBarrierSupport hk ring
        (rawRun hk ring C (pushWord hk ring C q))
        (ring.rightNeighbor q) r := by
  classical
  have hn2 : 1 < n := by omega
  by_cases hready : AdvanceReady hk ring C q
  · constructor
    · simp [pushWord, hready]
    · simpa [pushWord, hready, rawRun] using
        exactTwo_ready_q_hit hk ring hn2 C q r hs hsep hready
  · let C1 := (protocol k hk).step ring C q
    have hfirst :
        labelsOf C1 = labelsOf C ∧
          ExactTwoBarrierSupport hk ring C1 q r ∧
          (C1 q).phase = true ∧ (C1 q).probe = false := by
      simpa [C1] using nonready_exactTwo_q_hit hk ring C q r hs hready
    have hmid :=
      AAFJPK.OriginalTwoSuccessorPush.armed_exactTwo_push_by_final_q
        hk ring C1 q r hfirst.2.1 hsep hfirst.2.2.1
    rcases hmid with ⟨_, hpost⟩
    constructor
    · simp [pushWord, hready]
    · simpa [pushWord, hready, rawRun, C1] using hpost

#print axioms barrier_hit_source_controls_public
#print axioms nonready_exactTwo_q_hit
#print axioms exactTwo_ready_q_hit
#print axioms exactTwo_push_one

end AAFJPK.OriginalPushOne
