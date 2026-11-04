import Leader.AAFJ.MultiBarrier.PushOne
import Leader.AAFJ.MultiBarrier.AdjacentContact
import Leader.Core.LeaderCountPreservation

set_option autoImplicit false

namespace AAFJPK.OriginalN3CountThree

open AAFJPK
open AAFJPK.BarrierAlgebra
open AAFJPK.OriginalNonbarrierWord

private theorem hk2 : 0 < 2 := by decide
private theorem hn2 : 1 < 3 := by decide

def dropWord : List (Fin 3) := [0, 1, 0]

@[simp] theorem dropWord_length : dropWord.length = 3 := rfl

private theorem all_barrier_of_count_three
    (ring : DirectedRing 3) (C : Fin 3 → State 2)
    (hc : barrierCount hk2 ring (labelsOf C) = 3) :
    ∀ e : Fin 3, BarrierAt hk2 ring (labelsOf C) e := by
  intro e
  by_cases he : BarrierAt hk2 ring (labelsOf C) e
  · exact he
  · let S := barrierSupport hk2 ring (labelsOf C)
    let A := (ExhaustiveList.fin 3).values
    have hSn : S.Nodup := by
      simpa [S] using barrierSupport_nodup hk2 ring (labelsOf C)
    have hAn : A.Nodup := by
      simpa [A] using ExhaustiveList.values_nodup_fin 3
    have hsub : S ⊆ A.erase e := by
      intro x hx
      have hxS : x ∈ barrierSupport hk2 ring (labelsOf C) := by
        simpa [S] using hx
      have hxe : x ≠ e := by
        intro h
        subst x
        exact he ((mem_barrierSupport_iff hk2 ring (labelsOf C) e).1 hxS)
      have hxA : x ∈ A := by
        simpa [A] using (ExhaustiveList.fin 3).complete x
      exact (List.Nodup.mem_erase_iff hAn).2 ⟨hxe, hxA⟩
    have hle : S.length ≤ (A.erase e).length :=
      hSn.length_le_of_subset hsub
    have heA : e ∈ A := by
      simpa [A] using (ExhaustiveList.fin 3).complete e
    have hA : A.length = 3 := by
      simpa [A] using ExhaustiveList.values_length_fin 3
    have hAe : (A.erase e).length = 2 := by
      rw [List.length_erase_of_mem heA, hA]
    have hS : S.length = 3 := by
      simpa [S, barrierCount] using hc
    omega

theorem count_three_dropWord
    (ring : DirectedRing 3) (C : Fin 3 → State 2)
    (hc : barrierCount hk2 ring (labelsOf C) = 3) :
    barrierCount hk2 ring (labelsOf (rawRun hk2 ring C dropWord)) <
      barrierCount hk2 ring (labelsOf C) := by
  let C1 := (AAFJPK.protocol 2 hk2).step ring C (0 : Fin 3)
  let C2 := (AAFJPK.protocol 2 hk2).step ring C1 (1 : Fin 3)
  let C3 := (AAFJPK.protocol 2 hk2).step ring C2 (0 : Fin 3)

  have h01 : ring.rightNeighbor (0 : Fin 3) = (1 : Fin 3) := by
    apply Fin.ext
    simp [DirectedRing.rightNeighbor]
  have h02 : (0 : Fin 3) ≠ ring.rightNeighbor (1 : Fin 3) := by
    intro h
    have hv := congrArg Fin.val h
    simp [DirectedRing.rightNeighbor] at hv

  have hCbar := all_barrier_of_count_three ring C hc
  have hle1 :
      barrierCount hk2 ring (labelsOf C1) ≤
        barrierCount hk2 ring (labelsOf C) := by
    simpa [C1] using
      protocol_step_barrierCount_le hk2 ring hn2 C (0 : Fin 3)

  by_cases hd1 :
      barrierCount hk2 ring (labelsOf C1) <
        barrierCount hk2 ring (labelsOf C)
  · have hle2 :
        barrierCount hk2 ring (labelsOf C2) ≤
          barrierCount hk2 ring (labelsOf C1) := by
      simpa [C2] using
        protocol_step_barrierCount_le hk2 ring hn2 C1 (1 : Fin 3)
    have hle3 :
        barrierCount hk2 ring (labelsOf C3) ≤
          barrierCount hk2 ring (labelsOf C2) := by
      simpa [C3] using
        protocol_step_barrierCount_le hk2 ring hn2 C2 (0 : Fin 3)
    have hf :
        barrierCount hk2 ring (labelsOf C3) <
          barrierCount hk2 ring (labelsOf C) := by omega
    simpa [dropWord, rawRun, C1, C2, C3] using hf

  · have hc1 : barrierCount hk2 ring (labelsOf C1) = 3 := by
      omega
    have h1bar := all_barrier_of_count_three ring C1 hc1
    have hphase1 : (C1 (0 : Fin 3)).phase = true := by
      simpa [C1] using
        (AAFJPK.OriginalPushOne.barrier_hit_source_controls_public
          hk2 ring C (0 : Fin 3) (hCbar 0)).2
    have hle2 :
        barrierCount hk2 ring (labelsOf C2) ≤
          barrierCount hk2 ring (labelsOf C1) := by
      simpa [C2] using
        protocol_step_barrierCount_le hk2 ring hn2 C1 (1 : Fin 3)

    by_cases hd2 :
        barrierCount hk2 ring (labelsOf C2) <
          barrierCount hk2 ring (labelsOf C1)
    · have hle3 :
          barrierCount hk2 ring (labelsOf C3) ≤
            barrierCount hk2 ring (labelsOf C2) := by
        simpa [C3] using
          protocol_step_barrierCount_le hk2 ring hn2 C2 (0 : Fin 3)
      have hf :
          barrierCount hk2 ring (labelsOf C3) <
            barrierCount hk2 ring (labelsOf C) := by omega
      simpa [dropWord, rawRun, C1, C2, C3] using hf

    · have hc2 : barrierCount hk2 ring (labelsOf C2) = 3 := by
        omega
      have h2bar := all_barrier_of_count_three ring C2 hc2
      have hprobe2 : (C2 (1 : Fin 3)).probe = false := by
        simpa [C2] using
          (AAFJPK.OriginalPushOne.barrier_hit_source_controls_public
            hk2 ring C1 (1 : Fin 3) (h1bar 1)).1
      have hsame : C2 (0 : Fin 3) = C1 (0 : Fin 3) := by
        dsimp [C2]
        exact step_preserves_others (AAFJPK.protocol 2 hk2) ring C1
          (1 : Fin 3) (0 : Fin 3) (by decide) h02
      have hphase2 : (C2 (0 : Fin 3)).phase = true := by
        rw [hsame]
        exact hphase1
      have hd3 :=
        adjacent_ready_barrierCount_lt hk2 ring hn2 C2
          (0 : Fin 3) (1 : Fin 3) h01
          (h2bar 0) (h2bar 1) hphase2 hprobe2
      have hf :
          barrierCount hk2 ring (labelsOf C3) <
            barrierCount hk2 ring (labelsOf C) := by
        have hd3' :
            barrierCount hk2 ring (labelsOf C3) <
              barrierCount hk2 ring (labelsOf C2) := by
          simpa [C3] using hd3
        omega
      simpa [dropWord, rawRun, C1, C2, C3] using hf

private def coldCell : State 2 :=
  { bullet := false, leader := false, label := 0,
    probe := false, phase := false }

private def cold : Fin 3 → State 2 := fun _ => coldCell
private def ring3 : DirectedRing 3 := ⟨by decide⟩

theorem cold_no_drop_before_three
    (w : List (Fin 3)) (hw : w.length ≤ 2) :
    barrierCount hk2 ring3 (labelsOf (rawRun hk2 ring3 cold w)) = 3 := by
  cases w with
  | nil => decide
  | cons e es =>
      cases es with
      | nil =>
          revert e
          decide
      | cons f fs =>
          cases fs with
          | nil =>
              revert e f
              decide
          | cons g gs =>
              simp at hw

end AAFJPK.OriginalN3CountThree

#print axioms AAFJPK.OriginalN3CountThree.count_three_dropWord
#print axioms AAFJPK.OriginalN3CountThree.cold_no_drop_before_three
