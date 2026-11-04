import Leader.AAFJ.OneBarrier.ZeroLeaderBirth
import Leader.AAFJ.OneBarrier.MultipleLeaderProgress
import Leader.AAFJ.OneBarrier.UniqueLeaderCleanup

set_option autoImplicit false

namespace AAFJPK.ZeroLeaderToUnique

open BarrierAlgebra
open SingleBarrierSanitation
open ZeroLeaderBirth
open OriginalMultipleLeaderOneBarrier
open OriginalUniqueLeaderCleanup
open OriginalNonbarrierWord

private theorem one_le_bitCount_of_true {n : Nat} (bits : Fin n → Bool)
    (i : Fin n) (hi : bits i = true) : 1 ≤ bitCount bits := by
  let after : Fin n → Bool := fun j => if j = i then false else bits j
  have hdrop := bitCount_single_drop bits after i hi (by simp [after]) (by
    intro j hji
    simp [after, hji])
  omega

private theorem two_le_bitCount_of_two_true {n : Nat}
    (bits : Fin n → Bool) (i j : Fin n) (hi : bits i = true)
    (hj : bits j = true) (hne : j ≠ i) : 2 ≤ bitCount bits := by
  let after : Fin n → Bool := fun x => if x = i then false else bits x
  have hafterJ : after j = true := by simp [after, hne, hj]
  have hone := one_le_bitCount_of_true after j hafterJ
  have hdrop := bitCount_single_drop bits after i hi (by simp [after]) (by
    intro x hxi
    simp [after, hxi])
  omega

private theorem uniqueLeaderAt_of_phiAt_one
    {n k : Nat} (ring : DirectedRing n) (C : Fin n → State k)
    (b ell : Fin n) (hphi : PhiAt ring b C = 1)
    (hell : (C ell).leader = true) : UniqueLeaderAt C ell := by
  refine ⟨hell, ?_⟩
  intro i hi
  by_cases hne : i = ell
  · exact hne
  exfalso
  have hcutEll :
      ((cutView ring b C) (cutCoord ring b ell)).leader = true := by
    simpa [cutView] using hell
  have hcutI :
      ((cutView ring b C) (cutCoord ring b i)).leader = true := by
    simpa [cutView] using hi
  have hcoord : cutCoord ring b i ≠ cutCoord ring b ell := by
    intro h
    apply hne
    simpa using congrArg (cutPos ring b) h
  have htwo : 2 ≤ leaderCount (cutView ring b C) :=
    two_le_bitCount_of_two_true
      (fun q => ((cutView ring b C) q).leader)
      (cutCoord ring b ell) (cutCoord ring b i)
      hcutEll hcutI hcoord
  unfold PhiAt Phi at hphi
  omega

theorem zeroLeader_oneBarrierAt_unique_word
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (hn3 : 3 ≤ n) (hnd : ¬ k ∣ n)
    (C : Fin n → State k) (b : Fin n)
    (hone : OneBarrierAt hk ring C b)
    (hzero : ∀ i, (C i).leader = false) :
    ∃ w b' ell,
      w.length ≤ n + 2 ∧
      OneBarrierAt hk ring (rawRun hk ring C w) b' ∧
      PhiAt ring b' (rawRun hk ring C w) = 1 ∧
      UniqueLeaderAt (rawRun hk ring C w) ell := by
  have hn2 : 1 < n := by omega
  obtain ⟨w, b0, hw, hb0, ell, hell⟩ :=
    zeroLeader_oneBarrierAt_birth_word hk ring hn2 hnd C b hone hzero
  obtain ⟨b1, hb1, hphiLe⟩ :=
    rawRun_oneBarrier_phi_le hk ring hn3 C b hnd hone w
  have hbEq : b1 = b0 := by
    apply (hb0 b1).1
    exact oneBarrierAt_barrier hk ring (rawRun hk ring C w) b1 hb1
  subst b1
  have hphiC : PhiAt ring b C = 1 := by
    unfold PhiAt
    apply phi_eq_one_of_no_leaders
    intro i
    exact hzero (cutPos ring b i)
  have hphi : PhiAt ring b0 (rawRun hk ring C w) = 1 := by
    have honePhi : 1 ≤ PhiAt ring b0 (rawRun hk ring C w) := by
      unfold PhiAt Phi
      exact Nat.le_max_left _ _
    omega
  exact ⟨w, b0, ell, hw, hb0, hphi,
    uniqueLeaderAt_of_phiAt_one ring (rawRun hk ring C w) b0 ell hphi hell⟩

end AAFJPK.ZeroLeaderToUnique

#print axioms AAFJPK.ZeroLeaderToUnique.zeroLeader_oneBarrierAt_unique_word
