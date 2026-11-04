import Leader.AAFJ.OneBarrier.Sanitation
import Leader.AAFJ.NonbarrierWord

namespace AAFJPK
namespace SingleBarrierSanitation

open BarrierAlgebra
open OriginalNonbarrierWord

set_option autoImplicit false

private theorem incoming_ne_tail
    {n : Nat} (ring : DirectedRing n) (hn2 : 1 < n) (b : Fin n) :
    ring.leftNeighbor b ≠ b := by
  intro h
  have hr := rightNeighbor_leftNeighbor_clean ring b
  rw [h] at hr
  exact (BarrierAlgebra.rightNeighbor_ne_self ring hn2 b) hr

private theorem incoming_nonbarrier
    {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (hn2 : 1 < n)
    (C : Fin n → State k) (b : Fin n)
    (hone : OneBarrierAt hk ring C b) :
    ¬ IsBarrier hk
      (C (ring.leftNeighbor b))
      (C (ring.rightNeighbor (ring.leftNeighbor b))) := by
  let p := ring.leftNeighbor b
  have hpne : p ≠ b := by
    simpa [p] using incoming_ne_tail ring hn2 b
  intro hbar
  have hphys :
      BarrierAt hk ring (labelsOf C) p := by
    exact (barrierAt_labelsOf_iff hk ring C p).2 hbar
  exact hpne ((hone p).1 hphys)

/-- Two literal services of the edge entering the unique barrier tail clear
the dirty tail bullet.  No barrier service occurs. -/
theorem dirtyTail_two_incoming_clear
    {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (hn3 : 3 ≤ n)
    (hndvd : ¬ k ∣ n)
    (C : Fin n → State k) (b : Fin n)
    (hone : OneBarrierAt hk ring C b)
    (hphi : PhiAt ring b C = 1)
    (hbullet : (C b).bullet = true) :
    let p := ring.leftNeighbor b
    let C1 := (protocol k hk).step ring C p
    let D := (protocol k hk).step ring C1 p
    CurrentNonbarrierWord hk ring C [p, p] ∧
      OneBarrierAt hk ring D b ∧
      PhiAt ring b D = 1 ∧
      (D b).bullet = false ∧
      (D b).leader = false := by
  have hn2 : 1 < n := by omega
  let p := ring.leftNeighbor b
  let C1 := (protocol k hk).step ring C p
  let D := (protocol k hk).step ring C1 p

  have hr : ring.rightNeighbor p = b := by
    simpa [p] using rightNeighbor_leftNeighbor_clean ring b
  have hpne : p ≠ b := by
    simpa [p] using incoming_ne_tail ring hn2 b
  have hbp : b ≠ p := hpne.symm

  have hnb0 :
      ¬ IsBarrier hk (C p) (C (ring.rightNeighbor p)) := by
    simpa [p] using incoming_nonbarrier hk ring hn2 C b hone
  have hnot0 : ¬ AdvanceReady hk ring C p :=
    not_advanceReady_of_nonbarrier hk ring C p hnb0

  have hlabels1 : labelsOf C1 = labelsOf C := by
    dsimp [C1]
    exact labelsOf_step_eq_self_of_not_ready hk ring C p hnot0

  have hone1 : OneBarrierAt hk ring C1 b := by
    intro e
    unfold BarrierAt
    rw [hlabels1]
    exact hone e

  have hnb1 :
      ¬ IsBarrier hk (C1 p) (C1 (ring.rightNeighbor p)) := by
    simpa [p] using incoming_nonbarrier hk ring hn2 C1 b hone1
  have hnot1 : ¬ AdvanceReady hk ring C1 p :=
    not_advanceReady_of_nonbarrier hk ring C1 p hnb1

  have hlabelsD : labelsOf D = labelsOf C1 := by
    dsimp [D]
    exact labelsOf_step_eq_self_of_not_ready hk ring C1 p hnot1

  have honeD : OneBarrierAt hk ring D b := by
    intro e
    unfold BarrierAt
    rw [hlabelsD, hlabels1]
    exact hone e

  have hpair0 :
      transition hk (C p) (C b) = nonBarrierStep (C p) (C b) := by
    rw [transition_of_nonbarrier]
    simpa [hr] using hnb0

  have hC1Leader : (C1 b).leader = false := by
    cases hl : (C b).leader <;>
      cases hp : (C p).probe <;>
      simp [C1, PopulationProtocol.step, protocol, hr, hbp,
        hpair0, nonBarrierStep, hl, hbullet, hp]

  have hpair1 :
      transition hk (C1 p) (C1 b) = nonBarrierStep (C1 p) (C1 b) := by
    apply transition_of_nonbarrier
    simpa [hr] using hnb1

  have hDfields :
      (D b).bullet = false ∧ (D b).leader = false := by
    cases hb1 : (C1 b).bullet <;>
      cases hp1 : (C1 p).probe <;>
      simp [D, PopulationProtocol.step, protocol, hr, hbp,
        hpair1, nonBarrierStep, hC1Leader, hb1, hp1]

  have hframe0 :
      OneBarrierAt hk ring C1 b ∧
        PhiAt ring b C1 ≤ PhiAt ring b C := by
    simpa [C1, hnot0] using
      (oneBarrier_phi_step_le hk ring hn3 C b p hndvd hone)

  have hphi1 : PhiAt ring b C1 = 1 := by
    apply Nat.le_antisymm
    · simpa [hphi] using hframe0.2
    · unfold PhiAt Phi
      exact Nat.le_max_left _ _

  have hframe1 :
      OneBarrierAt hk ring D b ∧
        PhiAt ring b D ≤ PhiAt ring b C1 := by
    simpa [D, hnot1] using
      (oneBarrier_phi_step_le hk ring hn3 C1 b p hndvd hone1)

  have hphiD : PhiAt ring b D = 1 := by
    apply Nat.le_antisymm
    · simpa [hphi1] using hframe1.2
    · unfold PhiAt Phi
      exact Nat.le_max_left _ _

  have hword : CurrentNonbarrierWord hk ring C [p, p] := by
    simp only [CurrentNonbarrierWord]
    refine ⟨hnb0, ?_⟩
    exact ⟨hnb1, trivial⟩

  change
    CurrentNonbarrierWord hk ring C [p, p] ∧
      OneBarrierAt hk ring D b ∧
      PhiAt ring b D = 1 ∧
      (D b).bullet = false ∧
      (D b).leader = false
  exact ⟨hword, honeD, hphiD, hDfields⟩

#print axioms dirtyTail_two_incoming_clear

end SingleBarrierSanitation
end AAFJPK
