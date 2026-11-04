import Leader.AAFJ.MultiBarrier.SupportTransport
import Leader.AAFJ.MultiBarrier.NonbarrierInterleaving


set_option autoImplicit false


namespace AAFJPK.OriginalTwoSuccessorPush


open BarrierAlgebra
open OriginalNonbarrierWord
open OriginalNonbarrierFrame


private theorem nonBarrierStep_twice_left_probe_false
    {k : Nat} (u v : State k) :
    let p := nonBarrierStep u v
    (nonBarrierStep p.1 p.2).1.probe = false := by
  cases hl : v.leader <;> cases hb : v.bullet <;>
    cases hp : u.probe <;>
    simp [nonBarrierStep, hl, hb, hp]


private theorem transition_nonbarrier_twice_left_probe_false
    {k : Nat} (hk : 0 < k) (u v : State k)
    (hnon : ¬ IsBarrier hk u v) :
    let p := transition hk u v
    (transition hk p.1 p.2).1.probe = false := by
  let p := transition hk u v
  change (transition hk p.1 p.2).1.probe = false
  have hnot : ¬ PairAdvanceReady hk u v := by
    intro h
    exact hnon h.1
  have hlab :
      p.1.label = u.label ∧ p.2.label = v.label := by
    dsimp [p]
    exact transition_labels_of_not_pairAdvanceReady hk u v hnot
  have hnon2 : ¬ IsBarrier hk p.1 p.2 := by
    intro h
    apply hnon
    unfold IsBarrier at h ⊢
    rw [hlab.1, hlab.2] at h
    exact h
  have hp : p = nonBarrierStep u v := by
    dsimp [p]
    exact transition_of_nonbarrier hk u v hnon
  rw [transition_of_nonbarrier hk p.1 p.2 hnon2, hp]
  simpa using nonBarrierStep_twice_left_probe_false u v


theorem armed_exactTwo_ready_after_two_successor_services
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (C : Fin n → State k) (q r : Fin n)
    (hs : ExactTwoBarrierSupport hk ring C q r)
    (hsep : ring.rightNeighbor q ≠ r)
    (hphase : (C q).phase = true) :
    let b := ring.rightNeighbor q
    let D := rawRun hk ring C [b, b]
    AdvanceReady hk ring D q ∧
      ExactTwoBarrierSupport hk ring D q r := by
  let b := ring.rightNeighbor q
  let C1 := (protocol k hk).step ring C b
  let D := rawRun hk ring C [b, b]
  change AdvanceReady hk ring D q ∧
    ExactTwoBarrierSupport hk ring D q r
  have hn2 : 1 < n := by
    have hval : q.val ≠ r.val := by
      intro h
      exact hs.1 (Fin.ext h)
    have hq := q.isLt
    have hr := r.isLt
    omega
  have hbq : b ≠ q := by
    simpa [b] using rightNeighbor_ne_self ring hn2 q
  have hbr : b ≠ r := by
    simpa [b] using hsep
  have hfree : ¬ BarrierAt hk ring (labelsOf C) b := by
    intro h
    rcases (hs.2 b).1 h with h | h
    · exact hbq h
    · exact hbr h
  have hnb0 : ¬ IsBarrier hk (C b) (C (ring.rightNeighbor b)) := by
    intro h
    exact hfree ((barrierAt_labelsOf_iff hk ring C b).2 h)
  have hlabels1 : labelsOf C1 = labelsOf C := by
    dsimp [C1]
    exact labelsOf_step_eq_self_of_not_ready hk ring C b
      (not_advanceReady_of_nonbarrier hk ring C b hnb0)
  have hfree1 : ¬ BarrierAt hk ring (labelsOf C1) b := by
    rw [hlabels1]
    exact hfree
  have hnb1 :
      ¬ IsBarrier hk (C1 b) (C1 (ring.rightNeighbor b)) := by
    intro h
    exact hfree1 ((barrierAt_labelsOf_iff hk ring C1 b).2 h)
  have hword : CurrentNonbarrierWord hk ring C [b, b] := by
    simp only [CurrentNonbarrierWord]
    refine ⟨hnb0, ?_⟩
    refine ⟨?_, trivial⟩
    simpa [C1] using hnb1
  have hsD : ExactTwoBarrierSupport hk ring D q r := by
    simpa [D] using exactTwoBarrierSupport_rawRun hk ring hword hs
  have hphaseD : (D q).phase = true := by
    have h := rawRun_phases_eq hk ring hword q
    have h' : (D q).phase = (C q).phase := by
      simpa [D] using h
    exact h'.trans hphase
  have hre : ring.rightNeighbor b ≠ b :=
    rightNeighbor_ne_self ring hn2 b
  have her : b ≠ ring.rightNeighbor b := Ne.symm hre
  have hprobeD : (D b).probe = false := by
    have hlocal :=
      transition_nonbarrier_twice_left_probe_false
        hk (C b) (C (ring.rightNeighbor b)) hnb0
    simpa [D, rawRun, PopulationProtocol.step, protocol, hre, her] using hlocal
  have hreadyD : AdvanceReady hk ring D q := by
    refine ⟨(barrierAt_labelsOf_iff hk ring D q).1 ?_, hphaseD, ?_⟩
    · exact (hsD.2 q).2 (Or.inl rfl)
    · simpa [b] using hprobeD
  exact ⟨hreadyD, hsD⟩


private theorem exactTwo_ready_advance_first
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


theorem armed_exactTwo_push_by_final_q
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (C : Fin n → State k) (q r : Fin n)
    (hs : ExactTwoBarrierSupport hk ring C q r)
    (hsep : ring.rightNeighbor q ≠ r)
    (hphase : (C q).phase = true) :
    let b := ring.rightNeighbor q
    let D := rawRun hk ring C [b, b]
    let E := (protocol k hk).step ring D q
    AdvanceReady hk ring D q ∧
      ExactTwoBarrierSupport hk ring E b r := by
  let b := ring.rightNeighbor q
  let D := rawRun hk ring C [b, b]
  let E := (protocol k hk).step ring D q
  change AdvanceReady hk ring D q ∧
    ExactTwoBarrierSupport hk ring E b r
  have h :=
    armed_exactTwo_ready_after_two_successor_services
      hk ring C q r hs hsep hphase
  have hreadyD : AdvanceReady hk ring D q := by
    simpa [D, b] using h.1
  have hsD : ExactTwoBarrierSupport hk ring D q r := by
    simpa [D, b] using h.2
  have hn2 : 1 < n := by
    have hval : q.val ≠ r.val := by
      intro h
      exact hsD.1 (Fin.ext h)
    have hq := q.isLt
    have hr := r.isLt
    omega
  refine ⟨hreadyD, ?_⟩
  simpa [E, b] using
    exactTwo_ready_advance_first
      hk ring hn2 D q r hsD hsep hreadyD


#print axioms armed_exactTwo_ready_after_two_successor_services
#print axioms armed_exactTwo_push_by_final_q


end AAFJPK.OriginalTwoSuccessorPush
