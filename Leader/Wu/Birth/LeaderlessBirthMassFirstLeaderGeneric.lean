import Leader.Wu.Birth.LeaderlessBirthMassRenewal
import Leader.Wu.Birth.LeaderlessBirthMassFirstLeader

set_option autoImplicit false

/-!
# Step-indexed B7 first-hit failure bounds

The renewal proof needs an arbitrary `Fin n`-indexed step and a predicate,
not pair locality, a ring, or any particular P_PLL transition. The counted
words satisfy the predicate at every prefix endpoint, including the empty
prefix and the complete word. For leader election, `Good` is leaderlessness.

The generic numerator is exactly the existing `aliveCount`; it introduces
no second scheduler and no new event convention. Both the unrestricted and
step-closed-class versions retain the original B7 hypotheses and horizon.

The compatibility section proves the old consumer statements by applying
the generic theorem and the existing consumer numerator identity. It does
not call either old B7 tail corollary, change their types, or identify R1
with the consumer. The old B7 import is used for these compatibility bridges;
the original file remains unchanged, so this additive module creates no
import cycle and existing consumers continue to use their old declarations.
-/

namespace BirthLeaderlessBirthMassB7Generic

open BirthLeaderlessBirthMassRenewal

section Generic

variable {S : Type} {n : Nat}

/-- Exact original-word failure count: every prefix endpoint stays `Good`.
For arbitrary `Good`, this is failure to hit its complement. -/
noncomputable def firstLeaderFailureNumerator
    (step : S → Fin n → S) (Good : S → Prop)
    (x : S) (T : Nat) : Nat :=
  aliveCount step Good x T

theorem firstLeaderFailureNumerator_eq_aliveCount
    (step : S → Fin n → S) (Good : S → Prop)
    (x : S) (T : Nat) :
    firstLeaderFailureNumerator step Good x T =
      aliveCount step Good x T :=
  rfl

/-- The seven-eighths uniform leaf, with the physical step explicit. -/
def UniformFirstHitBirthMass
    (step : S → Fin n → S) (Good : S → Prop) (L : Nat) : Prop :=
  UniformEscapeMass step Good L 8

/-- The same leaf, required only on a specified class. -/
def UniformFirstHitBirthMassOn
    (step : S → Fin n → S) (Good R : S → Prop) (L : Nat) : Prop :=
  UniformEscapeMassOn step Good R L 8

/-- The full geometric estimate, in the step-indexed B7 currency. -/
theorem failure_le_geometric_of_uniformEscapeMass
    (step : S → Fin n → S) (Good : S → Prop) (L Q : Nat)
    (hmass : UniformEscapeMass step Good L Q)
    (k : Nat) (x : S) (hx : Good x) :
    Q ^ k * firstLeaderFailureNumerator step Good x (k * L) ≤
      (Q - 1) ^ k * n ^ (k * L) :=
  alive_tail step Good L Q hmass k x hx

/-- The B7 `1/n` bound for any step. No locality hypothesis is used. -/
theorem firstLeader_failure_le_one_over_n_of_uniformBirthMass
    (step : S → Fin n → S) (Good : S → Prop) (L : Nat)
    (hmass : UniformFirstHitBirthMass step Good L)
    (hn : 2 ≤ n) (x : S) (hx : Good x) :
    n * firstLeaderFailureNumerator step Good x
        (6 * (Nat.log2 n + 1) * L) ≤
      n ^ (6 * (Nat.log2 n + 1) * L) :=
  tail_one_over_n step Good L hmass hn x hx

/-- Restricted-class B7 bound, with exactly the original closure premise. -/
theorem firstLeader_failure_le_one_over_n_of_uniformBirthMassOn
    (step : S → Fin n → S) (Good R : S → Prop)
    (hR : ∀ x e, R x → R (step x e)) (L : Nat)
    (hmass : UniformFirstHitBirthMassOn step Good R L)
    (hn : 2 ≤ n) (x : S) (hxR : R x) (hx : Good x) :
    n * firstLeaderFailureNumerator step Good x
        (6 * (Nat.log2 n + 1) * L) ≤
      n ^ (6 * (Nat.log2 n + 1) * L) :=
  tail_one_over_n_on step Good R L hR hmass hn x hxR hx

end Generic

section ConsumerCompatibility

-- Open the actual defining namespace of currentStep2.
open BirthPhaseWait2BlockProgress

variable {n psi kappa tau : Nat}

/-- The old consumer leaf is precisely an instance of the generic leaf. -/
theorem uniformFirstHitBirthMass_currentStep2_iff
    (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (ring : DirectedRing n) (L : Nat) :
    UniformFirstHitBirthMass
        (currentStep2 (kappa := kappa) (tau := tau) hpsi h2 ring)
        BirthShortDoneTerminalFirstHit.Leaderless L ↔
      BirthLeaderlessBirthMassB7.UniformFirstHitBirthMass
        (kappa := kappa) (tau := tau) hpsi h2 ring L :=
  Iff.rfl

/-- The restricted old leaf is also definitionally the generic instance. -/
theorem uniformFirstHitBirthMassOn_currentStep2_iff
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) (ring : DirectedRing n)
    (R : BirthPhaseWait2BlockProgress.FC n psi kappa tau → Prop)
    (L : Nat) :
    UniformFirstHitBirthMassOn (currentStep2 hpsi h2 ring)
        BirthShortDoneTerminalFirstHit.Leaderless R L ↔
      BirthLeaderlessBirthMassB7.UniformFirstHitBirthMassOn
        hpsi h2 ring R L :=
  Iff.rfl

/-- The generic numerator at currentStep2 is the existing physical B7
numerator. This is a representation identity for the SAME step. -/
theorem firstLeaderFailureNumerator_currentStep2
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) (ring : DirectedRing n)
    (C : BirthPhaseWait2BlockProgress.FC n psi kappa tau) (T : Nat) :
    firstLeaderFailureNumerator (currentStep2 hpsi h2 ring)
        BirthShortDoneTerminalFirstHit.Leaderless C T =
      BirthPhaseFirstLeaderComposition.firstLeaderFailureNumerator
        hpsi h2 ring C T :=
  BirthLeaderlessBirthMassB7.aliveCount_eq_firstLeaderFailureNumerator
    hpsi h2 ring C T

/-- Re-derive the exact old consumer conclusion from the generic theorem.
The original declaration in BirthLeaderlessBirthMassB7 is left untouched. -/
theorem consumer_firstLeader_failure_le_one_over_n_of_uniformBirthMass
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) (ring : DirectedRing n) (L : Nat)
    (hmass : BirthLeaderlessBirthMassB7.UniformFirstHitBirthMass
      (kappa := kappa) (tau := tau) hpsi h2 ring L)
    (hn : 2 ≤ n) (C : BirthPhaseWait2BlockProgress.FC n psi kappa tau)
    (h0 : BirthShortDoneTerminalFirstHit.Leaderless C) :
    n * BirthPhaseFirstLeaderComposition.firstLeaderFailureNumerator
        hpsi h2 ring C (6 * (Nat.log2 n + 1) * L) ≤
      n ^ (6 * (Nat.log2 n + 1) * L) := by
  rw [← firstLeaderFailureNumerator_currentStep2 hpsi h2 ring C
    (6 * (Nat.log2 n + 1) * L)]
  exact firstLeader_failure_le_one_over_n_of_uniformBirthMass
    (currentStep2 hpsi h2 ring) BirthShortDoneTerminalFirstHit.Leaderless
    L hmass hn C h0

/-- The old restricted-class consumer conclusion is a generic instance too. -/
theorem consumer_firstLeader_failure_le_one_over_n_of_uniformBirthMassOn
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) (ring : DirectedRing n)
    (R : BirthPhaseWait2BlockProgress.FC n psi kappa tau → Prop)
    (hR : ∀ C e, R C → R (currentStep2 hpsi h2 ring C e)) (L : Nat)
    (hmass : BirthLeaderlessBirthMassB7.UniformFirstHitBirthMassOn
      hpsi h2 ring R L)
    (hn : 2 ≤ n) (C : BirthPhaseWait2BlockProgress.FC n psi kappa tau)
    (hCR : R C) (h0 : BirthShortDoneTerminalFirstHit.Leaderless C) :
    n * BirthPhaseFirstLeaderComposition.firstLeaderFailureNumerator
        hpsi h2 ring C (6 * (Nat.log2 n + 1) * L) ≤
      n ^ (6 * (Nat.log2 n + 1) * L) := by
  rw [← firstLeaderFailureNumerator_currentStep2 hpsi h2 ring C
    (6 * (Nat.log2 n + 1) * L)]
  exact firstLeader_failure_le_one_over_n_of_uniformBirthMassOn
    (currentStep2 hpsi h2 ring) BirthShortDoneTerminalFirstHit.Leaderless
    R hR L hmass hn C hCR h0

end ConsumerCompatibility

end BirthLeaderlessBirthMassB7Generic
