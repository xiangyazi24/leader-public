import Leader.AAFJ.MultiBarrier.PairHitPrefix
import Leader.AAFJ.MultiBarrier.AnchoredSecondHit
import Leader.AAFJ.MultiBarrier.ThirdHitRestartOrDrop
import Leader.AAFJ.MultiBarrier.GappedThreeHit


set_option autoImplicit false


namespace AAFJPK.OriginalGappedSix


open AAFJPK.BarrierAlgebra
open AAFJPK.OriginalNonbarrierWord


/-- Six anchored hits [a,b,a,b,c,b], each preceded by its own
current-prestate nonbarrier word. -/
def gappedService6 {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (C : Fin n → State k) (a b c : Fin n)
    (w0 w1 w2 w3 w4 w5 : List (Fin n)) : Fin n → State k :=
  let C1 := AAFJPK.OriginalGappedThree.gapHit hk ring C w0 a
  let C2 := AAFJPK.OriginalGappedThree.gapHit hk ring C1 w1 b
  let C3 := AAFJPK.OriginalGappedThree.gapHit hk ring C2 w2 a
  let C4 := AAFJPK.OriginalGappedThree.gapHit hk ring C3 w3 b
  let C5 := AAFJPK.OriginalGappedThree.gapHit hk ring C4 w4 c
  AAFJPK.OriginalGappedThree.gapHit hk ring C5 w5 b


private theorem gapHit_barrierCount_le
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n) (hn2 : 1 < n)
    (C : Fin n → State k) (word : List (Fin n)) (e : Fin n)
    (hw : CurrentNonbarrierWord hk ring C word) :
    barrierCount hk ring
        (labelsOf (AAFJPK.OriginalGappedThree.gapHit hk ring C word e)) ≤
      barrierCount hk ring (labelsOf C) := by
  have hstep :=
    protocol_step_barrierCount_le hk ring hn2
      (rawRun hk ring C word) e
  have hgap := barrierCount_rawRun_eq hk ring hw
  rw [hgap] at hstep
  simpa [AAFJPK.OriginalGappedThree.gapHit] using hstep


/-- Exact adjacent two-barrier support plus the literal gapped six-hit word
[a,b,a,b,c,b] forces a strict support drop.


Every wi is checked as a CurrentNonbarrierWord in the actual current prestate
immediately before its corresponding charged hit. -/
theorem gapped_six_hit_drops_of_exact_adjacent
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n) (hn3 : 2 < n)
    (C : Fin n → State k) (a b c : Fin n)
    (w0 w1 w2 w3 w4 w5 : List (Fin n))
    (hab : ring.rightNeighbor a = b)
    (hbc : ring.rightNeighbor b = c)
    (hsupport :
      ∀ e, BarrierAt hk ring (labelsOf C) e ↔ e = a ∨ e = b)
    (hw0 : CurrentNonbarrierWord hk ring C w0)
    (hw1 :
      CurrentNonbarrierWord hk ring
        (AAFJPK.OriginalGappedThree.gapHit hk ring C w0 a) w1)
    (hw2 :
      CurrentNonbarrierWord hk ring
        (AAFJPK.OriginalGappedThree.gapHit hk ring
          (AAFJPK.OriginalGappedThree.gapHit hk ring C w0 a) w1 b) w2)
    (hw3 :
      CurrentNonbarrierWord hk ring
        (AAFJPK.OriginalGappedThree.gapHit hk ring
          (AAFJPK.OriginalGappedThree.gapHit hk ring
            (AAFJPK.OriginalGappedThree.gapHit hk ring C w0 a) w1 b) w2 a) w3)
    (hw4 :
      CurrentNonbarrierWord hk ring
        (AAFJPK.OriginalGappedThree.gapHit hk ring
          (AAFJPK.OriginalGappedThree.gapHit hk ring
            (AAFJPK.OriginalGappedThree.gapHit hk ring
              (AAFJPK.OriginalGappedThree.gapHit hk ring C w0 a) w1 b) w2 a)
            w3 b) w4)
    (hw5 :
      CurrentNonbarrierWord hk ring
        (AAFJPK.OriginalGappedThree.gapHit hk ring
          (AAFJPK.OriginalGappedThree.gapHit hk ring
            (AAFJPK.OriginalGappedThree.gapHit hk ring
              (AAFJPK.OriginalGappedThree.gapHit hk ring
                (AAFJPK.OriginalGappedThree.gapHit hk ring C w0 a) w1 b) w2 a)
              w3 b) w4 c) w5) :
    barrierCount hk ring
        (labelsOf
          (gappedService6 hk ring C a b c w0 w1 w2 w3 w4 w5)) <
      barrierCount hk ring (labelsOf C) := by
  have hn2 : 1 < n := by omega


  have hneab : a ≠ b := by
    intro h
    exact (rightNeighbor_ne_self ring hn2 a) (hab.trans h.symm)


  have hsExact : ExactTwoBarrierSupport hk ring C a b :=
    ⟨hneab, hsupport⟩


  let C1 := AAFJPK.OriginalGappedThree.gapHit hk ring C w0 a
  let C2 := AAFJPK.OriginalGappedThree.gapHit hk ring C1 w1 b
  let C3 := AAFJPK.OriginalGappedThree.gapHit hk ring C2 w2 a
  let C4 := AAFJPK.OriginalGappedThree.gapHit hk ring C3 w3 b
  let C5 := AAFJPK.OriginalGappedThree.gapHit hk ring C4 w4 c
  let C6 := AAFJPK.OriginalGappedThree.gapHit hk ring C5 w5 b


  have hC6 :
      C6 = gappedService6 hk ring C a b c w0 w1 w2 w3 w4 w5 := by
    rfl


  have hw1' : CurrentNonbarrierWord hk ring C1 w1 := by
    simpa [C1] using hw1
  have hw2' : CurrentNonbarrierWord hk ring C2 w2 := by
    simpa [C2, C1] using hw2
  have hw3' : CurrentNonbarrierWord hk ring C3 w3 := by
    simpa [C3, C2, C1] using hw3
  have hw4' : CurrentNonbarrierWord hk ring C4 w4 := by
    simpa [C4, C3, C2, C1] using hw4
  have hw5' : CurrentNonbarrierWord hk ring C5 w5 := by
    simpa [C5, C4, C3, C2, C1] using hw5


  have hle1 :
      barrierCount hk ring (labelsOf C1) ≤
        barrierCount hk ring (labelsOf C) := by
    simpa [C1] using
      gapHit_barrierCount_le hk ring hn2 C w0 a hw0
  have hle2 :
      barrierCount hk ring (labelsOf C2) ≤
        barrierCount hk ring (labelsOf C1) := by
    simpa [C2] using
      gapHit_barrierCount_le hk ring hn2 C1 w1 b hw1'
  have hle3 :
      barrierCount hk ring (labelsOf C3) ≤
        barrierCount hk ring (labelsOf C2) := by
    simpa [C3] using
      gapHit_barrierCount_le hk ring hn2 C2 w2 a hw2'
  have hle4 :
      barrierCount hk ring (labelsOf C4) ≤
        barrierCount hk ring (labelsOf C3) := by
    simpa [C4] using
      gapHit_barrierCount_le hk ring hn2 C3 w3 b hw3'
  have hle5 :
      barrierCount hk ring (labelsOf C5) ≤
        barrierCount hk ring (labelsOf C4) := by
    simpa [C5] using
      gapHit_barrierCount_le hk ring hn2 C4 w4 c hw4'
  have hle6 :
      barrierCount hk ring (labelsOf C6) ≤
        barrierCount hk ring (labelsOf C5) := by
    simpa [C6] using
      gapHit_barrierCount_le hk ring hn2 C5 w5 b hw5'


  have hfirst :=
    AAFJPK.OriginalContactPrefix.first_gapped_a_stage
      hk ring hn2 C a b w0 hab hsExact hw0
  dsimp only at hfirst
  rcases hfirst with ⟨_, _, _, hstage1⟩
  rcases hstage1 with hdrop1raw | hstage1keep


  · have hdrop1 :
        barrierCount hk ring (labelsOf C1) <
          barrierCount hk ring (labelsOf C) := by
      simpa [C1, AAFJPK.OriginalGappedThree.gapHit] using hdrop1raw
    have hfinal :
        barrierCount hk ring (labelsOf C6) <
          barrierCount hk ring (labelsOf C) := by
      omega
    rw [← hC6]
    exact hfinal


  · rcases hstage1keep with
      ⟨hsC1raw, haPhaseC1raw, _haProbeC1raw, _hbPhaseC1raw⟩
    have hsC1 : ExactTwoBarrierSupport hk ring C1 a b := by
      simpa [C1, AAFJPK.OriginalGappedThree.gapHit] using hsC1raw
    have haPhaseC1 : (C1 a).phase = true := by
      simpa [C1, AAFJPK.OriginalGappedThree.gapHit] using haPhaseC1raw


    have hsecond :=
      AAFJPK.OriginalAnchoredSecond.second_hit_stage2
        hk ring hn3 C1 a b w1 hab hsC1 haPhaseC1 hw1'
    dsimp only at hsecond
    rcases hsecond with ⟨hreadyC2raw, hshapeC2raw⟩


    have hreadyC2 : AdvanceReady hk ring C2 a := by
      simpa [C2, AAFJPK.OriginalGappedThree.gapHit] using hreadyC2raw


    have hshapeC2 :
        ExactTwoBarrierSupport hk ring C2 a b ∨
          (ExactTwoBarrierSupport hk ring C2 a c ∧
            (C2 c).phase = false ∧ (C2 c).probe = false) := by
      simpa [C2, AAFJPK.OriginalGappedThree.gapHit, hbc] using hshapeC2raw


    rcases hshapeC2 with hsC2ab | hC2ac


    · have hreadyD2 :
          AdvanceReady hk ring (rawRun hk ring C2 w2) a :=
        AAFJPK.OriginalAnchoredSecond.ready_through_next_nb
          hk ring a hreadyC2 hw2'


      have hsD2 :
          ExactTwoBarrierSupport hk ring
            (rawRun hk ring C2 w2) a b :=
        exactTwoBarrierSupport_rawRun hk ring hw2' hsC2ab


      have hbarBD2 :
          BarrierAt hk ring (labelsOf (rawRun hk ring C2 w2)) b :=
        (hsD2.2 b).2 (Or.inr rfl)


      have hdrop3raw :=
        original_ready_collision_drops hk ring hn2
          (rawRun hk ring C2 w2) a hreadyD2
          (by simpa [hab] using hbarBD2)


      have hcountD2 := barrierCount_rawRun_eq hk ring hw2'
      rw [hcountD2] at hdrop3raw


      have hdrop3 :
          barrierCount hk ring (labelsOf C3) <
            barrierCount hk ring (labelsOf C2) := by
        simpa [C3, AAFJPK.OriginalGappedThree.gapHit] using hdrop3raw


      have hfinal :
          barrierCount hk ring (labelsOf C6) <
            barrierCount hk ring (labelsOf C) := by
        omega
      rw [← hC6]
      exact hfinal


    · rcases hC2ac with ⟨hsC2ac, hcPhaseC2, hcProbeC2⟩


      have haPhaseC2 : (C2 a).phase = true :=
        hreadyC2.2.1


      have hbProbeC2 : (C2 b).probe = false := by
        simpa [hab] using hreadyC2.2.2


      have hthird :=
        AAFJPK.OriginalGappedFirstTriple.third_hit_restart_or_drop
          hk ring hn3 C2 a b c hab hbc hsC2ac.2
          haPhaseC2 hbProbeC2 hcPhaseC2 hcProbeC2 w2 hw2'


      rcases hthird with hdrop3raw | hrestartPayload


      · have hcountD2 := barrierCount_rawRun_eq hk ring hw2'
        rw [hcountD2] at hdrop3raw


        have hdrop3 :
            barrierCount hk ring (labelsOf C3) <
              barrierCount hk ring (labelsOf C2) := by
          simpa [C3, AAFJPK.OriginalGappedThree.gapHit] using hdrop3raw


        have hfinal :
            barrierCount hk ring (labelsOf C6) <
              barrierCount hk ring (labelsOf C) := by
          omega
        rw [← hC6]
        exact hfinal


      · rcases hrestartPayload with
          ⟨hrestartRaw, _hbProbeC3, _hcProbeC3⟩


        have hrestartC3 :
            NormalizedAdjacentRestart hk ring C3 b c := by
          simpa [C3, AAFJPK.OriginalGappedThree.gapHit] using hrestartRaw


        have htail :=
          AAFJPK.OriginalGappedThree.normalized_adjacent_gapped_service3_drops
            hk ring hn2 C3 b c w3 w4 w5
            hrestartC3 hw3' hw4' hw5'


        have hdropTail :
            barrierCount hk ring (labelsOf C6) <
              barrierCount hk ring (labelsOf C3) := by
          simpa [C4, C5, C6,
            AAFJPK.OriginalGappedThree.gappedService3] using htail


        have hfinal :
            barrierCount hk ring (labelsOf C6) <
              barrierCount hk ring (labelsOf C) := by
          omega
        rw [← hC6]
        exact hfinal


#check gapped_six_hit_drops_of_exact_adjacent
#print axioms gapped_six_hit_drops_of_exact_adjacent


end AAFJPK.OriginalGappedSix
