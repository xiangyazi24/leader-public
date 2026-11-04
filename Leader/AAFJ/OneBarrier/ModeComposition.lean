import Leader.AAFJ.OneBarrier.ZeroLeaderToUnique
import Leader.AAFJ.OneBarrier.UniqueLeaderCleanup
import Leader.AAFJ.OneBarrier.MultipleLeaderProgress
import Leader.AAFJ.OneBarrier.DangerousProbeChase

set_option autoImplicit false
set_option Elab.async false

namespace AAFJPK.OriginalOneBarrierComposition

open BarrierAlgebra
open SingleBarrierSanitation
open OriginalNonbarrierWord
open OriginalUniqueLeaderCleanup

/-!  This file is a composition layer only.  Every branch below calls a
    source-grounded original-protocol macro; no centered transition is
    introduced here. -/

def ZeroLeaders {n k : Nat} (C : Fin n → State k) : Prop :=
  ∀ i, (C i).leader = false

def OneBarrierMode {n k : Nat} (C : Fin n → State k) : Prop :=
  ZeroLeaders C ∨
    (∃ ell, UniqueLeaderAt C ell) ∨
    OriginalMultipleLeaderOneBarrier.MultipleLeaders C

def OneBarrierReduction {n k : Nat}
    (hk : 0 < k) (ring : DirectedRing n)
    (b : Fin n) (C : Fin n → State k)
    (b' : Fin n) (D : Fin n → State k) : Prop :=
  Clean hk ring D ∨
    (∃ ell, UniqueLeaderAt D ell) ∨
    OriginalMultipleLeaderOneBarrier.MultipleLeaders D ∨
    PhiAt ring b' D < PhiAt ring b C ∨
    (∃ ell,
      terminalRank ring b' ell D < terminalRank ring b ell C) ∨
    OriginalMultipleLeaderOneBarrier.StrictLexDrop ring b C b' D

theorem zero_birth_to_unique
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (hn3 : 3 ≤ n) (hndvd : ¬ k ∣ n)
    (C : Fin n → State k) (b : Fin n)
    (hB : OneBarrierAt hk ring C b)
    (hzero : ZeroLeaders C) :
    ∃ w b' ell,
      w.length ≤ n + 2 ∧
      OneBarrierAt hk ring (rawRun hk ring C w) b' ∧
      PhiAt ring b' (rawRun hk ring C w) = 1 ∧
      UniqueLeaderAt (rawRun hk ring C w) ell := by
  exact ZeroLeaderToUnique.zeroLeader_oneBarrierAt_unique_word
    hk ring hn3 hndvd C b hB hzero

theorem one_barrier_mode_classification
    {n k : Nat} (C : Fin n → State k) :
    OneBarrierMode C := by
  classical
  by_cases hz : ZeroLeaders C
  · exact Or.inl hz
  · right
    by_cases hu : ∃ ell, UniqueLeaderAt C ell
    · exact Or.inl hu
    · right
      have hsome : ∃ ell, (C ell).leader = true := by
        by_cases hsome : ∃ ell, (C ell).leader = true
        · exact hsome
        · exfalso
          apply hz
          intro i
          cases hbit : (C i).leader with
          | false => simp [hbit]
          | true => exact False.elim (hsome ⟨i, hbit⟩)
      obtain ⟨ell, hell⟩ := hsome
      have hnotall :
          ¬ ∀ i : Fin n, (C i).leader = true → i = ell := by
        intro hall
        apply hu
        exact ⟨ell, hell, hall⟩
      obtain ⟨i, hi⟩ := Classical.not_forall.mp hnotall
      have hileader : (C i).leader = true := by
        cases hbit : (C i).leader with
        | false =>
            exfalso
            apply hi
            intro htrue
            simp [hbit] at htrue
        | true => simp [hbit]
      have hne : i ≠ ell := by
        intro hEq
        apply hi
        intro _
        exact hEq
      exact ⟨i, ell, hne, hileader, hell⟩

theorem one_barrier_mode_step
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (hn3 : 3 ≤ n) (hndvd : ¬ k ∣ n)
    (C : Fin n → State k) (b : Fin n)
    (hB : OneBarrierAt hk ring C b)
    (hmode : OneBarrierMode C) :
    ∃ w b',
      w.length ≤ 8 * n ∧
      OneBarrierAt hk ring (rawRun hk ring C w) b' ∧
      OneBarrierReduction hk ring b C b' (rawRun hk ring C w) := by
  rcases hmode with hzero | hrest
  · obtain ⟨w, b', ell, hw, hB', hphi', hU'⟩ :=
      zero_birth_to_unique hk ring hn3 hndvd C b hB hzero
    refine ⟨w, b', ?_, hB', ?_⟩
    · omega
    · exact Or.inr (Or.inl ⟨ell, hU'⟩)
  · rcases hrest with hunique | hmulti
    · obtain ⟨ell, hU⟩ := hunique
      by_cases hD : Dangerous (cutView ring b C)
      · obtain ⟨w, hwpos, hw, b', hB', hout⟩ :=
          OriginalDangerousProbeChase.uniqueLeader_dangerous_macro
            hk ring hn3 hndvd C b ell hB hU hD
        refine ⟨w, b', ?_, hB', ?_⟩
        · omega
        · rcases hout with hcleanD | hmultiD | hphi
          · obtain ⟨ellD, hcleanD⟩ := hcleanD
            have hcleanD' : Clean hk ring (rawRun hk ring C w) := by
              exact ⟨ellD, b', hcleanD⟩
            exact Or.inl hcleanD'
          · have hmultiD' :
                OriginalMultipleLeaderOneBarrier.MultipleLeaders
                  (rawRun hk ring C w) := by
              simpa [OriginalDangerousProbeChase.MultipleLeaders,
                OriginalMultipleLeaderOneBarrier.MultipleLeaders] using hmultiD
            exact Or.inr (Or.inr (Or.inl hmultiD'))
          · exact Or.inr (Or.inr (Or.inr (Or.inl hphi)))
      · obtain ⟨w, hw, hprogress⟩ :=
          uniqueLeader_progress hk ring hn3 hndvd C b ell hB hU
        let D := rawRun hk ring C w
        have hB' : OneBarrierAt hk ring D (ring.rightNeighbor b) := by
          simpa [D] using hprogress.1
        refine ⟨w, ring.rightNeighbor b, ?_, hB', ?_⟩
        · omega
        · rcases hprogress.2 with hclean | hrank
          · have hclean' : Clean hk ring D := by
              refine ⟨ell, ring.rightNeighbor b, ?_⟩
              simpa [D] using hclean
            exact Or.inl hclean'
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨ell, by
              simpa [D] using hrank⟩))))
    · obtain ⟨w, b', hw, hB', hout⟩ :=
        OriginalMultipleLeaderOneBarrier.multipleLeader_oneBarrier_progress
          hk ring hn3 C b hndvd hB hmulti
      refine ⟨w, b', ?_, hB', ?_⟩
      · omega
      · rcases hout with hclean | hunique | hlex
        · exact Or.inl hclean
        · obtain ⟨ell, hell, hother⟩ := hunique
          exact Or.inr (Or.inl ⟨ell, hell, hother⟩)
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hlex))))

end AAFJPK.OriginalOneBarrierComposition
