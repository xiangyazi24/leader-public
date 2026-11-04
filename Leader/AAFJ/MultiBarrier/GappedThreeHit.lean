import Leader.AAFJ.MultiBarrier.SixHitContactBlock
import Leader.AAFJ.MultiBarrier.NonbarrierInterleaving

set_option autoImplicit false

namespace AAFJPK.OriginalGappedThree

open AAFJPK.BarrierAlgebra
open AAFJPK.OriginalNonbarrierWord

/-- Execute one anchored charged hit after an arbitrary current-nonbarrier
word.  The theorem below supplies the CurrentNonbarrierWord premises. -/
def gapHit {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (C : Fin n → State k) (word : List (Fin n)) (e : Fin n) :
    Fin n → State k :=
  (AAFJPK.protocol k hk).step ring
    (rawRun hk ring C word) e

/-- The gapped anchored three-hit word [a,b,a]. -/
def gappedService3 {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (C : Fin n → State k) (a b : Fin n)
    (w0 w1 w2 : List (Fin n)) : Fin n → State k :=
  let C1 := gapHit hk ring C w0 a
  let C2 := gapHit hk ring C1 w1 b
  gapHit hk ring C2 w2 a

/-- Source controls of a phase-zero charged hit.

This is the private Six-file fact reproved downstream from the frozen original
transition API: the selected source is probe-free and armed afterwards. -/
private theorem phase_zero_source_controls
    {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (hn2 : 1 < n)
    (C : Fin n → State k) (e : Fin n)
    (hbar : BarrierAt hk ring (labelsOf C) e)
    (hphase : (C e).phase = false) :
    ((AAFJPK.protocol k hk).step ring C e e).probe = false ∧
      ((AAFJPK.protocol k hk).step ring C e e).phase = true := by
  have hjournal :
      IsBarrier hk (C e) (C (ring.rightNeighbor e)) :=
    (barrierAt_labelsOf_iff hk ring C e).1 hbar
  have hlocal :
      (transition hk (C e) (C (ring.rightNeighbor e))).1.probe = false ∧
        (transition hk (C e) (C (ring.rightNeighbor e))).1.phase = true := by
    rw [transition_of_barrier hk
      (C e) (C (ring.rightNeighbor e)) hjournal]
    rw [barrierStep_phase_zero hk
      (C e) (C (ring.rightNeighbor e)) hphase]
    cases hp : (C e).probe <;> simp [probeHitsBarrier, hp]
  simpa [PopulationProtocol.step, protocol] using hlocal

/-- A phase-zero charged hit preserves the responder's phase. -/
private theorem phase_zero_responder_preserves
    {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (hn2 : 1 < n)
    (C : Fin n → State k) (e : Fin n)
    (hbar : BarrierAt hk ring (labelsOf C) e)
    (hphase : (C e).phase = false) :
    ((AAFJPK.protocol k hk).step ring C e
      (ring.rightNeighbor e)).phase =
      (C (ring.rightNeighbor e)).phase := by
  have hjournal :
      IsBarrier hk (C e) (C (ring.rightNeighbor e)) :=
    (barrierAt_labelsOf_iff hk ring C e).1 hbar
  have hlocal :
      (transition hk (C e) (C (ring.rightNeighbor e))).2.phase =
        (C (ring.rightNeighbor e)).phase := by
    rw [transition_of_barrier hk
      (C e) (C (ring.rightNeighbor e)) hjournal]
    rw [barrierStep_phase_zero hk
      (C e) (C (ring.rightNeighbor e)) hphase]
    cases hv : (C (ring.rightNeighbor e)).leader <;> simp [hv]
  simpa [PopulationProtocol.step, protocol,
    rightNeighbor_ne_self ring hn2 e] using hlocal

/-- A phase-zero charged hit preserves every other site's phase. -/
private theorem phase_zero_other_preserves
    {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (hn2 : 1 < n)
    (C : Fin n → State k) (e j : Fin n)
    (hbar : BarrierAt hk ring (labelsOf C) e)
    (hphase : (C e).phase = false)
    (hje : j ≠ e) :
    ((AAFJPK.protocol k hk).step ring C e j).phase =
      (C j).phase := by
  by_cases hjr : j = ring.rightNeighbor e
  · subst j
    exact phase_zero_responder_preserves
      hk ring hn2 C e hbar hphase
  · have hjournal :
        IsBarrier hk (C e) (C (ring.rightNeighbor e)) :=
      (barrierAt_labelsOf_iff hk ring C e).1 hbar
    simp [PopulationProtocol.step, protocol,
      transition_of_barrier hk
        (C e) (C (ring.rightNeighbor e)) hjournal,
      barrierStep_phase_zero hk
        (C e) (C (ring.rightNeighbor e)) hphase,
      hje, hjr]

/-- Three anchored hits [a,b,a], with an arbitrary current-nonbarrier word
before each hit, strictly lower the charged-barrier count from a normalized
adjacent restart.

No scheduler/probability hypothesis is present.  Every gap is checked in its
actual current prestates by CurrentNonbarrierWord. -/
theorem normalized_adjacent_gapped_service3_drops
    {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (hn2 : 1 < n)
    (C : Fin n → State k) (a b : Fin n)
    (w0 w1 w2 : List (Fin n))
    (hrestart : NormalizedAdjacentRestart hk ring C a b)
    (hw0 : CurrentNonbarrierWord hk ring C w0)
    (hw1 :
      CurrentNonbarrierWord hk ring
        (gapHit hk ring C w0 a) w1)
    (hw2 :
      CurrentNonbarrierWord hk ring
        (gapHit hk ring (gapHit hk ring C w0 a) w1 b) w2) :
    barrierCount hk ring
        (labelsOf (gappedService3 hk ring C a b w0 w1 w2)) <
      barrierCount hk ring (labelsOf C) := by
  rcases hrestart with
    ⟨⟨hab, hs0⟩, hphaseA0, hphaseB0⟩

  have hneab : a ≠ b := by
    intro h
    exact (rightNeighbor_ne_self ring hn2 a) (hab.trans h.symm)

  have hsC0 :
      ExactTwoBarrierSupport hk ring C a b :=
    ⟨hneab, hs0⟩

  let D0 := rawRun hk ring C w0
  let C1 := gapHit hk ring C w0 a
  let D1 := rawRun hk ring C1 w1
  let C2 := gapHit hk ring C1 w1 b
  let D2 := rawRun hk ring C2 w2

  have hw1' : CurrentNonbarrierWord hk ring C1 w1 := by
    simpa [C1] using hw1

  have hw2' : CurrentNonbarrierWord hk ring C2 w2 := by
    simpa [C2, C1] using hw2

  /- First gap: support and cold phases survive. -/
  have hsD0 : ExactTwoBarrierSupport hk ring D0 a b := by
    simpa [D0] using
      exactTwoBarrierSupport_rawRun hk ring hw0 hsC0

  have hbarA0 : BarrierAt hk ring (labelsOf D0) a :=
    (hsD0.2 a).2 (Or.inl rfl)
  have hbarB0 : BarrierAt hk ring (labelsOf D0) b :=
    (hsD0.2 b).2 (Or.inr rfl)

  have hphaseAD0 : (D0 a).phase = false := by
    dsimp [D0]
    exact (rawRun_phases_eq hk ring hw0 a).trans hphaseA0

  have hphaseBD0 : (D0 b).phase = false := by
    dsimp [D0]
    exact (rawRun_phases_eq hk ring hw0 b).trans hphaseB0

  /- Hit a.  Cold phase makes this nonready, so labels/support do not move;
     the hit arms a and keeps b cold. -/
  have hnotA0 : ¬ AdvanceReady hk ring D0 a := by
    intro h
    exact Bool.noConfusion (hphaseAD0.symm.trans h.2.1)

  have hlabels1 : labelsOf C1 = labelsOf D0 := by
    simpa [C1, gapHit, D0] using
      labelsOf_step_eq_self_of_not_ready hk ring D0 a hnotA0

  have hctlA :=
    phase_zero_source_controls hk ring hn2
      D0 a hbarA0 hphaseAD0

  have hphaseAC1 : (C1 a).phase = true := by
    simpa [C1, gapHit, D0] using hctlA.2

  have hphaseBC1 : (C1 b).phase = false := by
    have hkeep :=
      phase_zero_other_preserves hk ring hn2
        D0 a b hbarA0 hphaseAD0 hneab.symm
    have h :
        (((AAFJPK.protocol k hk).step ring D0 a) b).phase = false :=
      hkeep.trans hphaseBD0
    simpa [C1, gapHit, D0] using h

  have hsC1 : ExactTwoBarrierSupport hk ring C1 a b := by
    refine ⟨hneab, ?_⟩
    intro e
    rw [hlabels1]
    exact hsD0.2 e

  /- Second gap: a stays armed, b stays cold, support stays {a,b}. -/
  have hsD1 : ExactTwoBarrierSupport hk ring D1 a b := by
    simpa [D1] using
      exactTwoBarrierSupport_rawRun hk ring hw1' hsC1

  have hbarB1 : BarrierAt hk ring (labelsOf D1) b :=
    (hsD1.2 b).2 (Or.inr rfl)

  have hphaseAD1 : (D1 a).phase = true := by
    dsimp [D1]
    exact (rawRun_phases_eq hk ring hw1' a).trans hphaseAC1

  have hphaseBD1 : (D1 b).phase = false := by
    dsimp [D1]
    exact (rawRun_phases_eq hk ring hw1' b).trans hphaseBC1

  /- Hit b.  Again the source is phase-zero, so this is nonready:
     labels/support stay put, b becomes armed and probe-free, and a remains
     armed. -/
  have hnotB1 : ¬ AdvanceReady hk ring D1 b := by
    intro h
    exact Bool.noConfusion (hphaseBD1.symm.trans h.2.1)

  have hlabels2 : labelsOf C2 = labelsOf D1 := by
    simpa [C2, gapHit, D1] using
      labelsOf_step_eq_self_of_not_ready hk ring D1 b hnotB1

  have hctlB :=
    phase_zero_source_controls hk ring hn2
      D1 b hbarB1 hphaseBD1

  have hprobeBC2 : (C2 b).probe = false := by
    simpa [C2, gapHit, D1] using hctlB.1

  have hphaseAC2 : (C2 a).phase = true := by
    have hkeep :=
      phase_zero_other_preserves hk ring hn2
        D1 b a hbarB1 hphaseBD1 hneab
    have h :
        (((AAFJPK.protocol k hk).step ring D1 b) a).phase = true :=
      hkeep.trans hphaseAD1
    simpa [C2, gapHit, D1] using h

  have hsC2 : ExactTwoBarrierSupport hk ring C2 a b := by
    refine ⟨hneab, ?_⟩
    intro e
    rw [hlabels2]
    exact hsD1.2 e

  have hbarAC2 : BarrierAt hk ring (labelsOf C2) a :=
    (hsC2.2 a).2 (Or.inl rfl)

  have hreadyAC2 : AdvanceReady hk ring C2 a := by
    refine
      ⟨(barrierAt_labelsOf_iff hk ring C2 a).1 hbarAC2,
        hphaseAC2, ?_⟩
    simpa [hab] using hprobeBC2

  /- Final gap preserves the full AdvanceReady payload of a and exact support. -/
  have hreadyAD2 : AdvanceReady hk ring D2 a := by
    simpa [D2] using
      rawRun_preserves_advanceReady hk ring a hreadyAC2 hw2'

  have hsD2 : ExactTwoBarrierSupport hk ring D2 a b := by
    simpa [D2] using
      exactTwoBarrierSupport_rawRun hk ring hw2' hsC2

  have hbarBD2 : BarrierAt hk ring (labelsOf D2) b :=
    (hsD2.2 b).2 (Or.inr rfl)

  have hnextD2 :
      BarrierAt hk ring
        (labelsOf D2) (ring.rightNeighbor a) := by
    simpa [hab] using hbarBD2

  /- All gaps preserve the count, and the first two hits preserve labels. -/
  have hcountD0 :
      barrierCount hk ring (labelsOf D0) =
        barrierCount hk ring (labelsOf C) := by
    simpa [D0] using barrierCount_rawRun_eq hk ring hw0

  have hcountD1 :
      barrierCount hk ring (labelsOf D1) =
        barrierCount hk ring (labelsOf C1) := by
    simpa [D1] using barrierCount_rawRun_eq hk ring hw1'

  have hcountD2 :
      barrierCount hk ring (labelsOf D2) =
        barrierCount hk ring (labelsOf C2) := by
    simpa [D2] using barrierCount_rawRun_eq hk ring hw2'

  have hcountAll :
      barrierCount hk ring (labelsOf D2) =
        barrierCount hk ring (labelsOf C) := by
    calc
      barrierCount hk ring (labelsOf D2) =
          barrierCount hk ring (labelsOf C2) := hcountD2
      _ = barrierCount hk ring (labelsOf D1) := by rw [hlabels2]
      _ = barrierCount hk ring (labelsOf C1) := hcountD1
      _ = barrierCount hk ring (labelsOf D0) := by rw [hlabels1]
      _ = barrierCount hk ring (labelsOf C) := hcountD0

  /- The final anchored a hit is now ready while its successor b is charged,
     so it is exactly the public collision-drop case. -/
  have hdrop :=
    original_ready_collision_drops
      hk ring hn2 D2 a hreadyAD2 hnextD2

  rw [hcountAll] at hdrop
  simpa [gappedService3, C1, C2, gapHit, D2] using hdrop

#check normalized_adjacent_gapped_service3_drops
#print axioms normalized_adjacent_gapped_service3_drops

end AAFJPK.OriginalGappedThree
