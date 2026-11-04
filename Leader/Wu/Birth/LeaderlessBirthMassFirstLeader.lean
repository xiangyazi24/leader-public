import Leader.Wu.Birth.LeaderlessBirthMassRenewal
import Leader.Wu.Birth.FirstLeaderComposition

set_option autoImplicit false

/-! # The uniform birth-mass route in the exact B7 currency

`BirthPhaseFirstLeaderComposition.firstLeaderFailureNumerator` counts the original scheduler words of a
given length along which every prefix configuration (start and end included) is leaderless under the
literal terminal consumer step.  That is exactly `aliveCount` of
`BirthLeaderlessBirthMassRenewal` for the physical step `currentStep2` and the predicate
`BirthShortDoneTerminalFirstHit.Leaderless` (`aliveCount_eq_firstLeaderFailureNumerator`).

Hence the candidate uniform leaf `UniformFirstHitBirthMass` alone gives the B7 conclusion
`n * firstLeaderFailureNumerator C T <= n ^ T` at the horizon `T = 6 (log2 n + 1) L`
(`firstLeader_failure_le_one_over_n_of_uniformBirthMass`), with none of the twelve premises of
`firstPhysicalLeader_failure_le_one_over_n'` (in particular without the refuted `hmono4`). -/

namespace BirthLeaderlessBirthMassB7

open PPLL PPLLRepair PPLLResearchFormulation PPLLExpiringComparisonRepair
open BirthLeaderlessBirthMassRenewal

variable {n psi kappa tau : Nat}

abbrev FC (n psi kappa tau : Nat) := BirthPhaseWait2BlockProgress.FC n psi kappa tau

theorem aliveAlong_iff_leaderlessAlong (hpsi : 0 < psi) (h2 : 2 ≤ psi) (ring : DirectedRing n) :
    ∀ (C : FC n psi kappa tau) (u : List (Fin n)),
      AliveAlong (BirthPhaseWait2BlockProgress.currentStep2 hpsi h2 ring)
          BirthShortDoneTerminalFirstHit.Leaderless C u ↔
        BirthShortDoneTerminalFirstHit.LeaderlessAlong hpsi (by decide : 0 < 2) h2 ring C u
  | C, [] => Iff.rfl
  | C, e :: u => by
      simp only [AliveAlong, BirthShortDoneTerminalFirstHit.LeaderlessAlong]
      rw [aliveAlong_iff_leaderlessAlong hpsi h2 ring _ u]
      rfl

theorem aliveCount_eq_firstLeaderFailureNumerator (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (ring : DirectedRing n) (C : FC n psi kappa tau) (T : Nat) :
    aliveCount (BirthPhaseWait2BlockProgress.currentStep2 hpsi h2 ring)
        BirthShortDoneTerminalFirstHit.Leaderless C T =
      BirthPhaseFirstLeaderComposition.firstLeaderFailureNumerator hpsi h2 ring C T := by
  classical
  unfold aliveCount BirthPhaseFirstLeaderComposition.firstLeaderFailureNumerator
  congr 1
  funext u
  unfold aliveBit BirthShortDoneTerminalNoHitCount.physicalNoHitBit
  have h := aliveAlong_iff_leaderlessAlong hpsi h2 ring C u
  by_cases hA : BirthShortDoneTerminalFirstHit.LeaderlessAlong hpsi (by decide : 0 < 2) h2 ring C u
  · have hB := h.2 hA
    simp [hA, hB]
  · have hB : ¬ AliveAlong (BirthPhaseWait2BlockProgress.currentStep2 hpsi h2 ring)
        BirthShortDoneTerminalFirstHit.Leaderless C u := fun hB => hA (h.1 hB)
    simp [hA, hB]

/-- Candidate uniform leaf in the B7 currency: from every leaderless configuration at most seven eighths
of the words of length `L` stay leaderless along every prefix. -/
def UniformFirstHitBirthMass (hpsi : 0 < psi) (h2 : 2 ≤ psi) (ring : DirectedRing n) (L : Nat) : Prop :=
  UniformEscapeMass (S := FC n psi kappa tau)
    (BirthPhaseWait2BlockProgress.currentStep2 hpsi h2 ring)
    BirthShortDoneTerminalFirstHit.Leaderless L 8

/-- The B7 conclusion from the single uniform leaf, at horizon `6 (log2 n + 1) L`. -/
theorem firstLeader_failure_le_one_over_n_of_uniformBirthMass
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) (ring : DirectedRing n) (L : Nat)
    (hmass : UniformFirstHitBirthMass (kappa := kappa) (tau := tau) hpsi h2 ring L)
    (hn : 2 ≤ n) (C : FC n psi kappa tau) (h0 : BirthShortDoneTerminalFirstHit.Leaderless C) :
    n * BirthPhaseFirstLeaderComposition.firstLeaderFailureNumerator hpsi h2 ring C
        (6 * (Nat.log2 n + 1) * L) ≤
      n ^ (6 * (Nat.log2 n + 1) * L) := by
  rw [← aliveCount_eq_firstLeaderFailureNumerator]
  exact tail_one_over_n _ _ L hmass hn C h0

/-- Restricted-class leaf: the birth mass is only required on a step-closed class `R`. -/
def UniformFirstHitBirthMassOn (hpsi : 0 < psi) (h2 : 2 ≤ psi) (ring : DirectedRing n)
    (R : FC n psi kappa tau → Prop) (L : Nat) : Prop :=
  UniformEscapeMassOn (BirthPhaseWait2BlockProgress.currentStep2 hpsi h2 ring)
    BirthShortDoneTerminalFirstHit.Leaderless R L 8

/-- The B7 conclusion from the restricted-class leaf, for starts in the class. -/
theorem firstLeader_failure_le_one_over_n_of_uniformBirthMassOn
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) (ring : DirectedRing n)
    (R : FC n psi kappa tau → Prop)
    (hR : ∀ C e, R C → R (BirthPhaseWait2BlockProgress.currentStep2 hpsi h2 ring C e)) (L : Nat)
    (hmass : UniformFirstHitBirthMassOn hpsi h2 ring R L)
    (hn : 2 ≤ n) (C : FC n psi kappa tau) (hCR : R C)
    (h0 : BirthShortDoneTerminalFirstHit.Leaderless C) :
    n * BirthPhaseFirstLeaderComposition.firstLeaderFailureNumerator hpsi h2 ring C
        (6 * (Nat.log2 n + 1) * L) ≤
      n ^ (6 * (Nat.log2 n + 1) * L) := by
  rw [← aliveCount_eq_firstLeaderFailureNumerator]
  exact tail_one_over_n_on _ _ R L hR hmass hn C hCR h0

end BirthLeaderlessBirthMassB7
