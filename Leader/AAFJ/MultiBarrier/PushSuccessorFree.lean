import Leader.AAFJ.MultiBarrier.PushOne

set_option autoImplicit false

namespace AAFJPK.OriginalPushOne

open BarrierAlgebra
open OriginalNonbarrierWord
open OriginalNonbarrierFrame

/-- The exact local row used in the cold branch.  Two repeated services of a
nonbarrier pair force the initiator probe false, even through the
leader+bullet stubborn responder case. -/
private theorem transition_nonbarrier_twice_left_probe_false_remote
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
  cases hl : v.leader <;> cases hb : v.bullet <;>
    cases hpr : u.probe <;>
    simp [nonBarrierStep, hl, hb, hpr]

/-- A charged edge with free successor can be pushed one physical edge by
the adaptive one/four-letter word.  The conclusion is exact global support
transport; arbitrary remote barriers are fixed by redirectEdge. -/
theorem push_one_of_successor_free
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (hn2 : 1 < n)
    (C : Fin n → State k) (q : Fin n)
    (hq : BarrierAt hk ring (labelsOf C) q)
    (hfree :
      ¬ BarrierAt hk ring (labelsOf C) (ring.rightNeighbor q)) :
    let word := pushWord hk ring C q
    let D := rawRun hk ring C word
    word.length ≤ 4 ∧
      ∀ j,
        j ∈ barrierSupport hk ring (labelsOf D) ↔
          ∃ i,
            i ∈ barrierSupport hk ring (labelsOf C) ∧
              redirectEdge ring q i = j := by
  classical
  dsimp only
  by_cases hready : AdvanceReady hk ring C q
  · constructor
    · simp [pushWord, hready]
    · intro j
      simpa [pushWord, hready, rawRun] using
        (protocol_barrierSupport_mem_iff_of_not_barrier_edgePlus
          hk ring hn2 C q hready hfree j)
  · let b := ring.rightNeighbor q
    let C1 := (protocol k hk).step ring C q
    have hlabels1 : labelsOf C1 = labelsOf C := by
      dsimp [C1]
      exact labelsOf_step_eq_self_of_not_ready hk ring C q hready
    have hphase1 : (C1 q).phase = true := by
      simpa [C1] using
        (barrier_hit_source_controls_public hk ring C q hq).2
    have hfree1 : ¬ BarrierAt hk ring (labelsOf C1) b := by
      rw [hlabels1]
      simpa [b] using hfree
    have hnb0 :
        ¬ IsBarrier hk (C1 b) (C1 (ring.rightNeighbor b)) := by
      intro h
      exact hfree1
        ((barrierAt_labelsOf_iff hk ring C1 b).2 h)

    let C2 := (protocol k hk).step ring C1 b
    have hlabels2 : labelsOf C2 = labelsOf C1 := by
      dsimp [C2]
      exact labelsOf_step_eq_self_of_not_ready hk ring C1 b
        (not_advanceReady_of_nonbarrier hk ring C1 b hnb0)
    have hfree2 : ¬ BarrierAt hk ring (labelsOf C2) b := by
      rw [hlabels2]
      exact hfree1
    have hnb1 :
        ¬ IsBarrier hk (C2 b) (C2 (ring.rightNeighbor b)) := by
      intro h
      exact hfree2
        ((barrierAt_labelsOf_iff hk ring C2 b).2 h)
    have hword : CurrentNonbarrierWord hk ring C1 [b, b] := by
      simp only [CurrentNonbarrierWord]
      refine ⟨hnb0, ?_⟩
      refine ⟨?_, trivial⟩
      simpa [C2] using hnb1

    let D := rawRun hk ring C1 [b, b]
    have hlabelsD1 : labelsOf D = labelsOf C1 := by
      simpa [D] using labelsOf_rawRun_eq hk ring hword
    have hlabelsD : labelsOf D = labelsOf C :=
      hlabelsD1.trans hlabels1
    have hphaseD : (D q).phase = true := by
      have hp := rawRun_phases_eq hk ring hword q
      have hp' : (D q).phase = (C1 q).phase := by
        simpa [D] using hp
      exact hp'.trans hphase1

    have hre : ring.rightNeighbor b ≠ b :=
      rightNeighbor_ne_self ring hn2 b
    have her : b ≠ ring.rightNeighbor b := Ne.symm hre
    have hprobeD : (D b).probe = false := by
      have hlocal :=
        transition_nonbarrier_twice_left_probe_false_remote
          hk (C1 b) (C1 (ring.rightNeighbor b)) hnb0
      simpa [D, rawRun, PopulationProtocol.step, protocol, hre, her]
        using hlocal

    have hqD : BarrierAt hk ring (labelsOf D) q := by
      rw [hlabelsD]
      exact hq
    have hfreeD :
        ¬ BarrierAt hk ring (labelsOf D) (ring.rightNeighbor q) := by
      rw [hlabelsD]
      exact hfree
    have hreadyD : AdvanceReady hk ring D q := by
      refine ⟨
        (barrierAt_labelsOf_iff hk ring D q).1 hqD,
        hphaseD, ?_⟩
      simpa [b] using hprobeD

    have hrun :
        rawRun hk ring C (pushWord hk ring C q) =
          (protocol k hk).step ring D q := by
      simp [pushWord, hready, rawRun, C1, D, b]
      rfl

    constructor
    · simp [pushWord, hready]
    · intro j
      rw [hrun]
      have ht :=
        protocol_barrierSupport_mem_iff_of_not_barrier_edgePlus
          hk ring hn2 D q hreadyD hfreeD j
      rw [hlabelsD] at ht
      exact ht

#print axioms push_one_of_successor_free

end AAFJPK.OriginalPushOne
