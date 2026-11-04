import Leader.Wu.Birth.LeaderlessFixedSuccessorLabels
import Leader.Wu.Safety.SafeConfig

set_option autoImplicit false
set_option Elab.async false

namespace ZZF3Divides

open PPLL

/-- F3's successor-label equalities force the label modulus to divide
    the ring size.  No separate positivity argument for n is needed. -/
theorem leaderless_edgewiseFixed_forces_dvd
    {n psi : Nat} (hpsi : 0 < psi) (kappa : Nat)
    (ring : DirectedRing n) (C : Fin n → AgentState psi)
    (hfixed : ZZF3Skeleton.EdgewiseFixed ring
      (PPLLRepair.ppllNoBulletSignalCollision hpsi kappa) C)
    (hlead : ∀ i : Fin n, (C i).leader = false) :
    psi ∣ n := by
  apply dvd_of_all_successor_labels hpsi ring C
  intro e
  apply Fin.ext
  exact ZZF3Closed.leaderless_edgewiseFixed_forces_successor_labels
    hpsi kappa ring C hfixed hlead e

#print axioms ZZF3Divides.leaderless_edgewiseFixed_forces_dvd

/-- On a ring whose size is not divisible by the label modulus,
    every edgewise-fixed configuration has a leader. -/
theorem no_leaderless_fixed_of_not_dvd
    {n psi : Nat} (hpsi : 0 < psi) (kappa : Nat) (hn : 0 < n)
    (ring : DirectedRing n) (hnd : ¬ (psi ∣ n))
    (C : Fin n → AgentState psi)
    (hfixed : ZZF3Skeleton.EdgewiseFixed ring
      (PPLLRepair.ppllNoBulletSignalCollision hpsi kappa) C) :
    ∃ i : Fin n, (C i).leader = true := by
  classical
  by_cases hex : ∃ i : Fin n, (C i).leader = true
  · exact hex
  · have hlead : ∀ i : Fin n, (C i).leader = false := by
      intro i
      cases hi : (C i).leader with
      | false => rfl
      | true => exact False.elim (hex ⟨i, hi⟩)
    exact False.elim
      (hnd (leaderless_edgewiseFixed_forces_dvd
        hpsi kappa ring C hfixed hlead))

end ZZF3Divides

#print axioms ZZF3Divides.no_leaderless_fixed_of_not_dvd
