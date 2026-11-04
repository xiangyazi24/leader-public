import Leader.AAFJ.OneBarrier.Sweep
import Leader.AAFJ.OneBarrier.PushLeaders
import Leader.AAFJ.OneBarrier.Leaderless
import Leader.AAFJ.OneBarrier.Reduce

set_option autoImplicit false

namespace AAFJPK.OriginalOneBarrierHeadPair

open BarrierAlgebra
open SingleBarrierSanitation
open OriginalPushOne
open OriginalUniqueLeaderCleanup
open OriginalOneBarrierSweep
open OriginalOneBarrierPushLeaders
open OriginalOneBarrierLeaderless
open OriginalNonbarrierWord
open OriginalOneBarrierReduce

private theorem cutCoord_self_local
    {n : Nat} (ring : DirectedRing n) (b : Fin n) :
    cutCoord ring b b = tailCoord ring := by
  apply cutPos_injective ring b
  rw [cutPos_cutCoord, cutPos_tailCoord]

private theorem cutCoord_interior_local
    {n : Nat} (ring : DirectedRing n) (b i : Fin n)
    (hhead : i ≠ ring.rightNeighbor b) (htail : i ≠ b) :
    1 ≤ (cutCoord ring b i).val ∧
      (cutCoord ring b i).val < (cutCoord ring b b).val := by
  have hzero : (cutCoord ring b i).val ≠ 0 := by
    intro hz
    apply hhead
    have hc :
        cutCoord ring b i = (⟨0, ring.hn⟩ : Fin n) := by
      apply Fin.ext
      simpa using hz
    calc
      i = cutPos ring b (cutCoord ring b i) :=
        (cutPos_cutCoord ring b i).symm
      _ = cutPos ring b (⟨0, ring.hn⟩ : Fin n) := by
        rw [hc]
      _ = ring.rightNeighbor b := by simp
  have hlast : (cutCoord ring b i).val ≠ n - 1 := by
    intro hv
    apply htail
    have hc : cutCoord ring b i = tailCoord ring := by
      apply Fin.ext
      change (cutCoord ring b i).val = n - 1
      exact hv
    calc
      i = cutPos ring b (cutCoord ring b i) :=
        (cutPos_cutCoord ring b i).symm
      _ = cutPos ring b (tailCoord ring) := by rw [hc]
      _ = b := cutPos_tailCoord ring b
  constructor
  · omega
  · rw [cutCoord_self_local]
    change (cutCoord ring b i).val < n - 1
    have hlt := (cutCoord ring b i).isLt
    omega

private theorem rightNeighbor_sq_ne_self_local
    {n : Nat} (ring : DirectedRing n) (hn3 : 3 ≤ n) (i : Fin n) :
    ring.rightNeighbor (ring.rightNeighbor i) ≠ i := by
  have hone : cwPos ring i 1 = ring.rightNeighbor i := by
    simpa using (cwPos_succ ring i 0)
  have htwo :
      cwPos ring i 2 = ring.rightNeighbor (cwPos ring i 1) := by
    simpa using (cwPos_succ ring i 1)
  intro hsq
  have hwalk : cwPos ring i 2 = i := by
    calc
      cwPos ring i 2 =
          ring.rightNeighbor (cwPos ring i 1) := htwo
      _ = ring.rightNeighbor (ring.rightNeighbor i) := by rw [hone]
      _ = i := hsq
  have htwoDist :=
    cwPos_bounded_unique ring i i 2 (by omega) hwalk
  have hzeroDist : cwDist ring i i = 0 := by
    exact
      (cwPos_bounded_unique ring i i 0 ring.hn
        (cwPos_zero ring i)).symm
  rw [hzeroDist] at htwoDist
  omega

private theorem uniqueLeaderAt_of_tail_head_clear
    {n k : Nat} (ring : DirectedRing n)
    (D : Fin n → State k) (b : Fin n)
    (htail : (D b).leader = true)
    (hhead : (D (ring.rightNeighbor b)).leader = false)
    (hclear :
      ∀ i : Fin n,
        1 ≤ (cutCoord ring b i).val →
        (cutCoord ring b i).val < (cutCoord ring b b).val →
        (D i).leader = false) :
    UniqueLeaderAt D b := by
  refine ⟨htail, ?_⟩
  intro i hi
  by_cases hib : i = b
  · exact hib
  by_cases hih : i = ring.rightNeighbor b
  · subst i
    exact False.elim
      (Bool.noConfusion (hhead.symm.trans hi))
  · have hc := cutCoord_interior_local ring b i hih hib
    have hf := hclear i hc.1 hc.2
    exact False.elim
      (Bool.noConfusion (hf.symm.trans hi))

/-- `topShoot` with the argument order used by the cleanup leaves. -/
theorem topShoot_pinned {n k : Nat} (hk : 0 < k) (ring : DirectedRing n) (hn3 : 3 ≤ n)
    (C : Fin n → State k) (b p : Fin n) (hB : OneBarrierAt hk ring C b)
    (hpos : 1 ≤ (cutCoord ring b p).val) (hlead : (C p).leader = true)
    (hbul : (C p).bullet = false) :
    let D := rawRun hk ring C ([ring.leftNeighbor p] ++
      sweepWord ring b ((cutCoord ring b p).val - 1))
    OneBarrierAt hk ring D b ∧ D p = C p ∧
    (∀ i, 1 ≤ (cutCoord ring b i).val →
      (cutCoord ring b i).val < (cutCoord ring b p).val → (D i).leader = false) ∧
    (∀ i, (cutCoord ring b p).val < (cutCoord ring b i).val → D i = C i) ∧
    (D (ring.rightNeighbor b)).leader = (C (ring.rightNeighbor b)).leader ∧
    (∀ i, (D i).leader = true → (C i).leader = true) :=
  OriginalOneBarrierReduce.topShoot hk ring hn3 C b p hB hlead hbul hpos

theorem headPair_reaches_clean {n k : Nat}
    (hk : 0 < k) (ring : DirectedRing n) (hn3 : 3 ≤ n)
    (hnd : ¬ k ∣ n)
    (C : Fin n → State k) (b : Fin n)
    (hB : OneBarrierAt hk ring C b) (p : Fin n)
    (hph : p ≠ ring.rightNeighbor b)
    (hp : (C p).leader = true)
    (hh : (C (ring.rightNeighbor b)).leader = true)
    (honly :
      ∀ i, (C i).leader = true →
        i = p ∨ i = ring.rightNeighbor b) :
    ∃ w : List (Fin n), Clean hk ring (rawRun hk ring C w) := by
  have hn2 : 1 < n := by omega
  let h := ring.rightNeighbor b
  let s := ring.rightNeighbor h

  let w₁ := pushWord hk ring C b
  let C₁ := rawRun hk ring C w₁

  have hfresh₁ :
      w₁.length ≤ 4 ∧
        OneBarrierAt hk ring C₁ h ∧
        (C₁ h).bullet = false ∧
        (C₁ h).probe = false := by
    simpa [h, w₁, C₁] using
      (OriginalUniqueLeaderCleanup.pushWord_oneBarrier_fresh
        hk ring hn3 hnd C b hB)
  rcases hfresh₁ with ⟨_, hB₁, hbul₁, hprobe₁⟩

  have hframe₁ :
      (C₁ h).leader = (C h).leader ∧
        (∀ i : Fin n, (C₁ i).leader = true →
          (C i).leader = true ∨ i = b) ∧
        (∀ i : Fin n,
          i ≠ b → i ≠ h → i ≠ s → C₁ i = C i) := by
    simpa [h, s, w₁, C₁] using
      (OriginalOneBarrierPushLeaders.pushWord_leader_frame
        hk ring hn3 hnd C b hB)
  rcases hframe₁ with ⟨hkeepH₁, _, _⟩

  have hlead₁ : (C₁ h).leader = true := by
    calc
      (C₁ h).leader = (C h).leader := hkeepH₁
      _ = true := by simpa [h] using hh

  have hpos₁ : 1 ≤ (cutCoord ring h h).val := by
    rw [cutCoord_self_local]
    change 1 ≤ n - 1
    omega

  let shoot₁ : List (Fin n) :=
    [ring.leftNeighbor h] ++
      sweepWord ring h ((cutCoord ring h h).val - 1)
  let C₂ := rawRun hk ring C₁ shoot₁

  have htop₁ :
      OneBarrierAt hk ring C₂ h ∧
        C₂ h = C₁ h ∧
        (∀ i : Fin n,
          1 ≤ (cutCoord ring h i).val →
          (cutCoord ring h i).val < (cutCoord ring h h).val →
          (C₂ i).leader = false) ∧
        (∀ i : Fin n,
          (cutCoord ring h h).val < (cutCoord ring h i).val →
          C₂ i = C₁ i) ∧
        (C₂ (ring.rightNeighbor h)).leader =
          (C₁ (ring.rightNeighbor h)).leader ∧
        (∀ i : Fin n,
          (C₂ i).leader = true → (C₁ i).leader = true) := by
    simpa [shoot₁, C₂] using
      (topShoot_pinned
        hk ring hn3 C₁ h h hB₁ hpos₁ hlead₁ hbul₁)
  rcases htop₁ with
    ⟨hB₂, htailEq₁, hclear₁, _, _, _⟩

  have hlead₂ : (C₂ h).leader = true := by
    rw [htailEq₁]
    exact hlead₁
  have hfresh₂ :
      (C₂ h).bullet = false ∧ (C₂ h).probe = false := by
    constructor
    · rw [htailEq₁]
      exact hbul₁
    · rw [htailEq₁]
      exact hprobe₁

  cases hs₂ : (C₂ s).leader with
  | false =>
      have hu₂ : UniqueLeaderAt C₂ h := by
        apply uniqueLeaderAt_of_tail_head_clear ring C₂ h
        · exact hlead₂
        · simpa [s] using hs₂
        · exact hclear₁
      have hcleanAt₂ : CleanAt hk ring C₂ h h :=
        OriginalOneBarrierLeaderless.cleanAt_self_of_unique_fresh
          hk ring C₂ h hB₂ hu₂ hfresh₂
      have hclean₂ : Clean hk ring C₂ := by
        exact ⟨h, h, hcleanAt₂⟩
      refine ⟨w₁ ++ shoot₁, ?_⟩
      rw [OriginalOneBarrierLeaderless.rawRun_append
        hk ring C w₁ shoot₁]
      simpa [C₁, C₂] using hclean₂

  | true =>
      let t := ring.rightNeighbor s

      have hts : t ≠ s := by
        dsimp [t]
        exact rightNeighbor_ne_self ring hn2 s
      have hth : t ≠ h := by
        dsimp [t, s]
        exact rightNeighbor_sq_ne_self_local ring hn3 h
      have htCoord :
          1 ≤ (cutCoord ring h t).val ∧
            (cutCoord ring h t).val <
              (cutCoord ring h h).val := by
        apply cutCoord_interior_local ring h t
        · simpa [s] using hts
        · exact hth
      have ht₂ : (C₂ t).leader = false :=
        hclear₁ t htCoord.1 htCoord.2

      let w₃ := pushWord hk ring C₂ h
      let C₃ := rawRun hk ring C₂ w₃

      have hfresh₃ :
          w₃.length ≤ 4 ∧
            OneBarrierAt hk ring C₃ s ∧
            (C₃ s).bullet = false ∧
            (C₃ s).probe = false := by
        simpa [s, w₃, C₃] using
          (OriginalUniqueLeaderCleanup.pushWord_oneBarrier_fresh
            hk ring hn3 hnd C₂ h hB₂)
      rcases hfresh₃ with ⟨_, hB₃, hbul₃, hprobe₃⟩

      have hframe₃ :
          (C₃ s).leader = (C₂ s).leader ∧
            (∀ i : Fin n, (C₃ i).leader = true →
              (C₂ i).leader = true ∨ i = h) ∧
            (∀ i : Fin n,
              i ≠ h → i ≠ s → i ≠ t → C₃ i = C₂ i) := by
        simpa [s, t, w₃, C₃] using
          (OriginalOneBarrierPushLeaders.pushWord_leader_frame
            hk ring hn3 hnd C₂ h hB₂)
      rcases hframe₃ with ⟨hkeepS₃, hnoBirth₃, _⟩

      have hlead₃ : (C₃ s).leader = true :=
        hkeepS₃.trans hs₂

      have ht₃ : (C₃ t).leader = false := by
        cases ht : (C₃ t).leader with
        | false => rfl
        | true =>
            exfalso
            rcases hnoBirth₃ t ht with hprev | htail
            · exact
                Bool.noConfusion (ht₂.symm.trans hprev)
            · exact hth htail

      have hpos₂ : 1 ≤ (cutCoord ring s s).val := by
        rw [cutCoord_self_local]
        change 1 ≤ n - 1
        omega

      let shoot₂ : List (Fin n) :=
        [ring.leftNeighbor s] ++
          sweepWord ring s ((cutCoord ring s s).val - 1)
      let C₄ := rawRun hk ring C₃ shoot₂

      have htop₂ :
          OneBarrierAt hk ring C₄ s ∧
            C₄ s = C₃ s ∧
            (∀ i : Fin n,
              1 ≤ (cutCoord ring s i).val →
              (cutCoord ring s i).val <
                (cutCoord ring s s).val →
              (C₄ i).leader = false) ∧
            (∀ i : Fin n,
              (cutCoord ring s s).val <
                (cutCoord ring s i).val →
              C₄ i = C₃ i) ∧
            (C₄ (ring.rightNeighbor s)).leader =
              (C₃ (ring.rightNeighbor s)).leader ∧
            (∀ i : Fin n,
              (C₄ i).leader = true → (C₃ i).leader = true) := by
        simpa [shoot₂, C₄] using
          (topShoot_pinned
            hk ring hn3 C₃ s s hB₃ hpos₂ hlead₃ hbul₃)
      rcases htop₂ with
        ⟨hB₄, htailEq₂, hclear₂, _, hheadEq₂, _⟩

      have hlead₄ : (C₄ s).leader = true := by
        rw [htailEq₂]
        exact hlead₃
      have hfresh₄ :
          (C₄ s).bullet = false ∧ (C₄ s).probe = false := by
        constructor
        · rw [htailEq₂]
          exact hbul₃
        · rw [htailEq₂]
          exact hprobe₃
      have hhead₄ : (C₄ t).leader = false := by
        calc
          (C₄ t).leader = (C₃ t).leader := by
            simpa [t] using hheadEq₂
          _ = false := ht₃
      have hu₄ : UniqueLeaderAt C₄ s := by
        apply uniqueLeaderAt_of_tail_head_clear ring C₄ s
        · exact hlead₄
        · simpa [t] using hhead₄
        · exact hclear₂
      have hcleanAt₄ : CleanAt hk ring C₄ s s :=
        OriginalOneBarrierLeaderless.cleanAt_self_of_unique_fresh
          hk ring C₄ s hB₄ hu₄ hfresh₄
      have hclean₄ : Clean hk ring C₄ := by
        exact ⟨s, s, hcleanAt₄⟩

      refine
        ⟨w₁ ++ (shoot₁ ++ (w₃ ++ shoot₂)), ?_⟩
      rw [OriginalOneBarrierLeaderless.rawRun_append
        hk ring C w₁ (shoot₁ ++ (w₃ ++ shoot₂))]
      rw [OriginalOneBarrierLeaderless.rawRun_append
        hk ring (rawRun hk ring C w₁)
        shoot₁ (w₃ ++ shoot₂)]
      rw [OriginalOneBarrierLeaderless.rawRun_append
        hk ring
          (rawRun hk ring
            (rawRun hk ring C w₁) shoot₁)
        w₃ shoot₂]
      simpa [C₁, C₂, C₃, C₄] using hclean₄

end AAFJPK.OriginalOneBarrierHeadPair

#print axioms AAFJPK.OriginalOneBarrierHeadPair.topShoot_pinned
#print axioms AAFJPK.OriginalOneBarrierHeadPair.headPair_reaches_clean
