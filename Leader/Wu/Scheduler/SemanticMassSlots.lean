import Leader.Wu.Birth.TwoStageEscape
import Leader.Wu.Safety.CorrectedFormulation

set_option autoImplicit false

namespace IntegratedSemanticMassInventory

open PPLLResearchFormulation
open BirthLeaderlessBirthMassRenewal
open BirthTwoStageEscape

variable {n ψ : Nat}

abbrev SemCfg
    (regime : OperationalRegime n ψ) (κ : Nat) :=
  (physicalProtocol regime κ).Configuration n

/-- Scheduler-visible semantic-family step. -/
def semStep
    (regime : OperationalRegime n ψ) (κ : Nat) :
    SemCfg regime κ → Fin n → SemCfg regime κ :=
  (physicalProtocol regime κ).step regime.ring

/-- Exactly the complement of the family's success target. -/
def SemanticBad
    (regime : OperationalRegime n ψ) (κ : Nat)
    (C : SemCfg regime κ) : Prop :=
  ¬ PopulationProtocol.IsSafe
      (physicalProtocol regime κ) regime.ring C isLeaderOutput

/-- Direct semantic block-escape obligation. -/
def IntegratedSemanticBlockEscape
    (regime : OperationalRegime n ψ) (κ L Q : Nat) : Prop :=
  UniformEscapeMass
    (semStep regime κ)
    (SemanticBad regime κ)
    L Q

/-- The form directly consumable by the existing one-over-n renewal theorem. -/
def IntegratedSemanticBlockEscape8
    (regime : OperationalRegime n ψ) (κ L : Nat) : Prop :=
  IntegratedSemanticBlockEscape regime κ L 8

/-- Stage 1 of a two-stage proof, once a genuine integrated recovery target R
is chosen. -/
def IntegratedRecoveryFirstHitMass
    (regime : OperationalRegime n ψ) (κ : Nat)
    (R : SemCfg regime κ → Prop)
    (B1 Q1 : Nat) : Prop :=
  ∀ C : SemCfg regime κ,
    SemanticBad regime κ C →
    Q1 * avoidCount
        (semStep regime κ)
        (SemanticBad regime κ) R C B1 ≤
      (Q1 - 1) * n ^ B1

/-- Stage 2 must escape semantic unsafety.  Calling this merely "leadership"
would be too weak unless a separate leader-to-IsSafe theorem is supplied. -/
def IntegratedStage2SafetyMass
    (regime : OperationalRegime n ψ) (κ : Nat)
    (R : SemCfg regime κ → Prop)
    (B2 Q2 : Nat) : Prop :=
  ∀ C : SemCfg regime κ,
    SemanticBad regime κ C →
    R C →
    Q2 * aliveCount
        (semStep regime κ)
        (SemanticBad regime κ) C B2 ≤
      (Q2 - 1) * n ^ B2

/-- Pure statement of the two-stage producer slot.  `two_stage_escape` then
returns `IntegratedSemanticBlockEscape` at B1+B2 and Q1*Q2. -/
def IntegratedTwoStageSlots
    (regime : OperationalRegime n ψ) (κ : Nat)
    (R : SemCfg regime κ → Prop)
    (B1 B2 Q1 Q2 : Nat) : Prop :=
  1 ≤ Q1 ∧ 1 ≤ Q2 ∧
  IntegratedRecoveryFirstHitMass regime κ R B1 Q1 ∧
  IntegratedStage2SafetyMass regime κ R B2 Q2

end IntegratedSemanticMassInventory
