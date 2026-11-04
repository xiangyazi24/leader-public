import Leader.AAFJ.OneBarrier.Sanitation
import Leader.AAFJ.NonbarrierWord

set_option autoImplicit false

namespace AAFJPK.OriginalOuterPhi.Counterexample

open SingleBarrierSanitation

private def hk2 : 0 < 2 := by decide
private def ring3 : DirectedRing 3 := ⟨by decide⟩

private def C0 (i : Fin 3) : State 2 :=
  { bullet := false
    leader := decide (i = (0 : Fin 3))
    label := if i = (1 : Fin 3) then (1 : Fin 2) else (0 : Fin 2)
    probe := decide (i = (1 : Fin 3))
    phase := false }

private def C1 : Fin 3 → State 2 :=
  (protocol 2 hk2).step ring3 C0 (1 : Fin 3)

private def C2 : Fin 3 → State 2 :=
  (protocol 2 hk2).step ring3 C1 (2 : Fin 3)

private theorem fin3_cases (i : Fin 3) :
    i = (0 : Fin 3) ∨ i = (1 : Fin 3) ∨ i = (2 : Fin 3) := by
  by_cases h0 : i.val = 0
  · exact Or.inl (Fin.ext h0)
  · by_cases h1 : i.val = 1
    · exact Or.inr (Or.inl (Fin.ext h1))
    · exact Or.inr (Or.inr (Fin.ext (by omega)))

theorem start_is_true_outer :
    OneBarrierAt hk2 ring3 C0 (2 : Fin 3) ∧
      PhiAt ring3 (2 : Fin 3) C0 = 2 ∧
      leaderCount C0 = 1 := by
  decide +kernel

theorem every_first_edge_is_lex_flat :
    ∀ e : Fin 3,
      let D := (protocol 2 hk2).step ring3 C0 e
      OneBarrierAt hk2 ring3 D (2 : Fin 3) ∧
        PhiAt ring3 (2 : Fin 3) D = 2 ∧
        leaderCount D = 1 := by
  intro e
  rcases fin3_cases e with rfl | rfl | rfl
  · refine ⟨?_, by decide +kernel, by decide +kernel⟩
    intro j
    rcases fin3_cases j with rfl | rfl | rfl <;> decide +kernel
  · refine ⟨?_, by decide +kernel, by decide +kernel⟩
    intro j
    rcases fin3_cases j with rfl | rfl | rfl <;> decide +kernel
  · refine ⟨?_, by decide +kernel, by decide +kernel⟩
    intro j
    rcases fin3_cases j with rfl | rfl | rfl <;> decide +kernel

theorem dangerous_service_flat_then_birth :
    OneBarrierAt hk2 ring3 C1 (2 : Fin 3) ∧
      PhiAt ring3 (2 : Fin 3) C1 = 2 ∧
      leaderCount C1 = 1 ∧
      OneBarrierAt hk2 ring3 C2 (2 : Fin 3) ∧
      PhiAt ring3 (2 : Fin 3) C2 = 2 ∧
      leaderCount C2 = 2 := by
  decide +kernel

end AAFJPK.OriginalOuterPhi.Counterexample


namespace AAFJPK.OriginalOuterPhi

open BarrierAlgebra
open SingleBarrierSanitation
open OriginalNonbarrierWord

/-- Explicit lexicographic decrease on the requested two physical coordinates. -/
def OuterLexDrop {n k : Nat}
    (ring : DirectedRing n) (b : Fin n)
    (before after : Fin n → State k) : Prop :=
  PhiAt ring b after < PhiAt ring b before ∨
    (PhiAt ring b after = PhiAt ring b before ∧
      leaderCount after < leaderCount before)

/-- A kernel-simple Nat ranking that also decreases on the kill row. -/
def outerNatRank {n k : Nat}
    (ring : DirectedRing n) (b : Fin n)
    (C : Fin n → State k) : Nat :=
  PhiAt ring b C + leaderCount C

/-- True outer-layer local deletion.

The extra hphi hypothesis only scopes the lemma to the requested PhiAt>1
layer; the local Protocol-6 deletion row itself is valid more generally. -/
theorem killable_responder_one_letter
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (hn3 : 3 ≤ n) (hndvd : ¬ k ∣ n)
    (C : Fin n → State k) (b e : Fin n)
    (hone : OneBarrierAt hk ring C b)
    (hphi : 1 < PhiAt ring b C)
    (hne : e ≠ b)
    (hleader :
      (C (ring.rightNeighbor e)).leader = true)
    (hbullet :
      (C (ring.rightNeighbor e)).bullet = true) :
    ∃ w : List (Fin n),
      w = [e] ∧
      OneBarrierAt hk ring (rawRun hk ring C w) b ∧
      OuterLexDrop ring b C (rawRun hk ring C w) ∧
      outerNatRank ring b (rawRun hk ring C w) <
        outerNatRank ring b C := by
  have hn2 : 1 < n := by omega

  have hnon :
      ¬ IsBarrier hk (C e) (C (ring.rightNeighbor e)) := by
    intro hbar
    apply hne
    exact (hone e).1
      ((barrierAt_labelsOf_iff hk ring C e).2 hbar)

  have hnot : ¬ AdvanceReady hk ring C e :=
    not_advanceReady_of_nonbarrier hk ring C e hnon

  let D := (protocol k hk).step ring C e

  have hframe :
      OneBarrierAt hk ring D b ∧
        PhiAt ring b D ≤ PhiAt ring b C := by
    simpa [D, hnot] using
      (oneBarrier_phi_step_le
        hk ring hn3 C b e hndvd hone)

  have htr :
      transition hk (C e) (C (ring.rightNeighbor e)) =
        (C e,
          { C (ring.rightNeighbor e) with leader := false }) :=
    transition_nonbarrier_leader_hit
      hk (C e) (C (ring.rightNeighbor e))
        hnon hleader hbullet

  have hleft :
      (transition hk (C e) (C (ring.rightNeighbor e))).1.leader =
        (C e).leader := by
    rw [htr]

  have hright :
      (transition hk (C e) (C (ring.rightNeighbor e))).2.leader =
        false := by
    rw [htr]

  have hcountEq :
      leaderCount D + 1 = leaderCount C := by
    simpa [D] using
      (step_leaderCount_single_drop
        hk ring hn2 C e hleft hleader hright)

  have hcountLt : leaderCount D < leaderCount C := by
    omega

  have hlex : OuterLexDrop ring b C D := by
    unfold OuterLexDrop
    by_cases heq : PhiAt ring b D = PhiAt ring b C
    · exact Or.inr ⟨heq, hcountLt⟩
    · left
      omega

  have hrank :
      outerNatRank ring b D < outerNatRank ring b C := by
    unfold outerNatRank
    omega

  refine ⟨[e], rfl, ?_, ?_, ?_⟩
  · simpa [rawRun, D] using hframe.1
  · simpa [rawRun, D] using hlex
  · simpa [rawRun, D] using hrank

end AAFJPK.OriginalOuterPhi

#print axioms AAFJPK.OriginalOuterPhi.Counterexample.start_is_true_outer
#print axioms AAFJPK.OriginalOuterPhi.Counterexample.every_first_edge_is_lex_flat
#print axioms AAFJPK.OriginalOuterPhi.Counterexample.dangerous_service_flat_then_birth
#print axioms AAFJPK.OriginalOuterPhi.killable_responder_one_letter
