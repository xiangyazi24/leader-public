import Leader.Wu.Coherence.PhaseDebt

set_option autoImplicit false

namespace R2CoherenceV31Drift

open R2CoherenceV31 R2CoherenceV31PhaseDebt
open BirthLeaderlessBirthMassRenewal

variable {n ψ κ τ : Nat}

/-- Executable current-state proxy used by the group-aware rank. -/
def RecoveryProxyV3
    (ring : DirectedRing n) (C : R2CoherenceV31.FC n ψ κ τ) : Prop :=
  ControllerShapeV3 ring C ∧ CoherentPrefixesV3 ring C

/-- Candidate constant horizon suggested by a census (ψ = 3). -/
def recoveryUniformH : Nat := 16

/-- Coarse linear coefficient. -/
def recoveryRankCapV32 (ψ : Nat) : Nat :=
  rankStrideV32 ψ * (2 * ψ + 3) + (7 * ψ + 13)

/-- Zero-set law for the actual rank. -/
def RecoveryRankZeroLawV31
    (ring : DirectedRing n) : Prop :=
  ∀ C : R2CoherenceV31.FC n ψ κ τ,
    R ring C = 0 ↔ RecoveryProxyV3 ring C

/-- Linear rank cap. -/
def RecoveryRankBoundV31
    (ring : DirectedRing n) : Prop :=
  ∀ C : R2CoherenceV31.FC n ψ κ τ,
    R ring C ≤ recoveryRankCapV32 ψ * n

/-- Missing bridge needed before replacing `¬RecoveryProxyV3` by
`¬RecoveredV3` in the Bellman law. -/
def RecoveryProxyCompleteV31
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) : Prop :=
  ∀ C : R2CoherenceV31.FC n ψ κ τ,
    AdmittedPostBirthGeometryV3 hψ ring C →
    RecoveryProxyV3 ring C →
    RecoveredV3 hψ h2 ring C

/-- Empirically supported uniform-horizon law: exact row sum with one
unit of total H-word deficit.  Prove this version first. -/
def RecoveryUniformBellmanProxyV31
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) : Prop :=
  ∀ C : R2CoherenceV31.FC n ψ κ τ,
    AdmittedPostBirthGeometryV3 hψ ring C →
    ¬ RecoveryProxyV3 ring C →
    FixedSpanRenewalPayload.wordSum n recoveryUniformH
        (fun w => R ring (w.foldl (stepV3 hψ h2 ring) C)) + 1
      ≤ n ^ recoveryUniformH * R ring C

/-- Promoted form requested in the question.  This is derivable from the
proxy form only after `RecoveryProxyCompleteV31`. -/
def RecoveryUniformBellmanRecoveredV31
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) : Prop :=
  ∀ C : R2CoherenceV31.FC n ψ κ τ,
    AdmittedPostBirthGeometryV3 hψ ring C →
    ¬ RecoveredV3 hψ h2 ring C →
    FixedSpanRenewalPayload.wordSum n recoveryUniformH
        (fun w => R ring (w.foldl (stepV3 hψ h2 ring) C)) + 1
      ≤ n ^ recoveryUniformH * R ring C

/-- Stronger mass law.  Average rank drops by at least 1/n per H-block.
This, not the +1 law, is the law matching a 2*Kψ*n^2*H first-hit block. -/
def RecoveryUniformMassBellmanV31
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) : Prop :=
  ∀ C : R2CoherenceV31.FC n ψ κ τ,
    AdmittedPostBirthGeometryV3 hψ ring C →
    ¬ RecoveredV3 hψ h2 ring C →
    FixedSpanRenewalPayload.wordSum n recoveryUniformH
        (fun w => R ring (w.foldl (stepV3 hψ h2 ring) C)) +
          n ^ (recoveryUniformH - 1)
      ≤ n ^ recoveryUniformH * R ring C

/-- One-step additive raise cap for the rank R. -/
def RecoveryRankRaiseBoundV31
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (c : Nat) : Prop :=
  ∀ (C : R2CoherenceV31.FC n ψ κ τ) (e : Fin n),
    R ring (stepV3 hψ h2 ring C e) ≤ R ring C + c

/-- A canonical repair word reaches a strict rank cash-out within H letters. -/
def RecoveryCanonicalProductiveWordV31
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (H : Nat) : Prop :=
  ∀ C : R2CoherenceV31.FC n ψ κ τ,
    AdmittedPostBirthGeometryV3 hψ ring C →
    ¬ RecoveryProxyV3 ring C →
    ∃ w : List (Fin n),
      1 ≤ w.length ∧ w.length ≤ H ∧
      R ring (w.foldl (stepV3 hψ h2 ring) C) < R ring C

end R2CoherenceV31Drift
