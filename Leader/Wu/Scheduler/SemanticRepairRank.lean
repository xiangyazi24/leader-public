import Leader.Wu.Scheduler.SemanticMassSlots
import Leader.Wu.Scheduler.BellmanRankMass
import Leader.Wu.Entrance.LocalReverseFill
import Leader.Wu.Splice.GarbageDrainTable

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace ZZSemanticRecoveryC

open PPLL PPLLRepair PPLLResearchFormulation
open BirthLeaderlessBirthMassRenewal BirthTwoStageEscape
open FiniteUniformStoppingTree

variable {n ψ κ : Nat}

abbrev SemCfg (regime : OperationalRegime n ψ) (κ : Nat) :=
  IntegratedSemanticMassInventory.SemCfg regime κ

/-! ## The only state-local defect among the three integrated repairs -/

/-- The exact repository T7 invariant, read on the bounded physical state. -/
def T7RepairedCell (u : BoundedAgentState ψ κ) : Prop :=
  PPLLRepair.LiveBulletSignalExclusive (BoundedAgentState.erase u)

/-- This exposes that the invariant reads exactly the real bounded fields
`bullet` and `signal_B`; no ghost coordinate is involved. -/
theorem t7RepairedCell_iff_fields (u : BoundedAgentState ψ κ) :
    T7RepairedCell u ↔
      (u.bullet = (2 : Fin 3) → u.signal_B = (0 : Fin 2)) := by
  rfl

/-- WAIT overflow is already impossible in the finite semantic carrier. -/
theorem bounded_count_le_kappa (u : BoundedAgentState ψ κ) :
    u.count.val ≤ κ := by
  have h := u.count.isLt
  omega

/-- Zero for a repaired cell, one for a current T7 violation. -/
noncomputable def t7DefectBit (u : BoundedAgentState ψ κ) : Nat := by
  classical
  exact if T7RepairedCell u then 0 else 1

private theorem t7DefectBit_le_one (u : BoundedAgentState ψ κ) :
    t7DefectBit u ≤ 1 := by
  classical
  unfold t7DefectBit
  by_cases h : T7RepairedCell u <;> simp [h]

theorem t7DefectBit_eq_zero_iff (u : BoundedAgentState ψ κ) :
    t7DefectBit u = 0 ↔ T7RepairedCell u := by
  classical
  unfold t7DefectBit
  by_cases h : T7RepairedCell u <;> simp [h]

/-- First honest semantic-recovery target: every current cell satisfies the
actual no-live-bullet/signal collision repair invariant. -/
def SemanticRepairTarget
    (regime : OperationalRegime n ψ) (κ : Nat)
    (C : SemCfg regime κ) : Prop :=
  ∀ i : Fin n, T7RepairedCell (C i)

/-- Active class for the repair-rank Bellman argument. -/
def SemanticRepairBad
    (regime : OperationalRegime n ψ) (κ : Nat)
    (C : SemCfg regime κ) : Prop :=
  ¬ SemanticRepairTarget regime κ C

/-- Number of currently unrepaired T7 cells. -/
noncomputable def semanticRepairRank
    (regime : OperationalRegime n ψ) (κ : Nat)
    (C : SemCfg regime κ) : Nat :=
  (List.ofFn (fun i : Fin n => t7DefectBit (C i))).sum

private theorem ofFn_sum_eq_zero_iff
    (f : Fin n → Nat) :
    (List.ofFn f).sum = 0 ↔ ∀ i : Fin n, f i = 0 := by
  constructor
  · intro hs i
    have hsplit := B9SpliceTableV10d.ofFn_sum_split
      (fun _ : Fin n => 0) f i (fun _ _ => Nat.zero_le _)
    have hz : (List.ofFn (fun _ : Fin n => 0)).sum = 0 := by
      apply List.sum_eq_zero_iff_forall_eq_nat.mpr
      intro x hx
      rw [List.mem_ofFn] at hx
      obtain ⟨i, rfl⟩ := hx
      rfl
    rw [hz, hs] at hsplit
    omega
  · intro h
    apply List.sum_eq_zero_iff_forall_eq_nat.mpr
    intro x hx
    rw [List.mem_ofFn] at hx
    obtain ⟨i, rfl⟩ := hx
    exact h i

/-- Requested trivial lower bound, stated explicitly. -/
theorem semanticRepairRank_nonneg
    (regime : OperationalRegime n ψ) (κ : Nat)
    (C : SemCfg regime κ) :
    0 ≤ semanticRepairRank regime κ C :=
  Nat.zero_le _

/-- One defect bit per site, hence K=n. -/
theorem semanticRepairRank_le_n
    (regime : OperationalRegime n ψ) (κ : Nat)
    (C : SemCfg regime κ) :
    semanticRepairRank regime κ C ≤ n := by
  unfold semanticRepairRank
  calc
    (List.ofFn (fun i : Fin n => t7DefectBit (C i))).sum
        ≤ (List.ofFn (fun _ : Fin n => 1)).sum :=
      FiniteUniformStoppingTree.ofFn_sum_le _ _
        (fun i => t7DefectBit_le_one (C i))
    _ = n := by
      rw [FiniteUniformStoppingTree.ofFn_sum_const]
      simp

/-- The rank-zero target is exactly the real T7 repair invariant everywhere. -/
theorem semanticRepairRank_eq_zero_iff_target
    (regime : OperationalRegime n ψ) (κ : Nat)
    (C : SemCfg regime κ) :
    semanticRepairRank regime κ C = 0 ↔
      SemanticRepairTarget regime κ C := by
  unfold semanticRepairRank SemanticRepairTarget
  constructor
  · intro h i
    have hi :=
      (ofFn_sum_eq_zero_iff
        (fun j : Fin n => t7DefectBit (C j))).1 h i
    exact (t7DefectBit_eq_zero_iff (C i)).1 hi
  · intro h
    apply (ofFn_sum_eq_zero_iff
      (fun j : Fin n => t7DefectBit (C j))).2
    intro i
    exact (t7DefectBit_eq_zero_iff (C i)).2 (h i)

/-- Equivalently, every active repair state has positive rank. -/
theorem semanticRepairRank_pos_iff_bad
    (regime : OperationalRegime n ψ) (κ : Nat)
    (C : SemCfg regime κ) :
    0 < semanticRepairRank regime κ C ↔
      SemanticRepairBad regime κ C := by
  unfold SemanticRepairBad
  constructor
  · intro hp hT
    have hz :=
      (semanticRepairRank_eq_zero_iff_target regime κ C).2 hT
    omega
  · intro hBad
    have hn : semanticRepairRank regime κ C ≠ 0 := by
      intro hz
      exact hBad
        ((semanticRepairRank_eq_zero_iff_target regime κ C).1 hz)
    omega

/-! ## The three exact Bellman ingredients on the real semantic step -/

/-- Ingredient (a): uniform bound.  This one is proved below with K=n. -/
def SemanticRankBound
    (regime : OperationalRegime n ψ) (κ : Nat) : Prop :=
  ∀ C : SemCfg regime κ,
    semanticRepairRank regime κ C ≤ n

/-- Ingredient (b): every original scheduler letter is non-increasing for the
actual `physicalProtocol = integratedBoundedProtocol` step. -/
def SemanticRankNonincrease
    (regime : OperationalRegime n ψ) (κ : Nat) : Prop :=
  ∀ (C : SemCfg regime κ) (e : Fin n),
    semanticRepairRank regime κ
        (IntegratedSemanticMassInventory.semStep regime κ C e) ≤
      semanticRepairRank regime κ C

/-- Ingredient (c): whenever some T7 violation remains, one scheduler edge
strictly lowers the rank. -/
def SemanticRankDescent
    (regime : OperationalRegime n ψ) (κ : Nat) : Prop :=
  ∀ C : SemCfg regime κ,
    SemanticRepairBad regime κ C →
    ∃ e : Fin n,
      semanticRepairRank regime κ
          (IntegratedSemanticMassInventory.semStep regime κ C e) <
        semanticRepairRank regime κ C

theorem semanticRankBound_proved
    (regime : OperationalRegime n ψ) (κ : Nat) :
    SemanticRankBound regime κ := by
  intro C
  exact semanticRepairRank_le_n regime κ C

/-- Once the two semantic transition obligations are supplied, the generic
Bellman theorem gives a Q=2 block with horizon `rankHalfH n n = 2*n*n`. -/
theorem semanticRepair_half_mass_of_rank
    (regime : OperationalRegime n ψ) (κ : Nat)
    (hMono : SemanticRankNonincrease regime κ)
    (hDesc : SemanticRankDescent regime κ) :
    UniformEscapeMass
      (IntegratedSemanticMassInventory.semStep regime κ)
      (SemanticRepairBad regime κ)
      (ZZBellmanTemplate.rankHalfH n n) 2 := by
  apply ZZBellmanTemplate.rank_half_uniformEscapeMass
    (step := IntegratedSemanticMassInventory.semStep regime κ)
    (Bad := SemanticRepairBad regime κ)
    (rank := semanticRepairRank regime κ)
    (K := n)
  · exact semanticRepairRank_le_n regime κ
  · simpa [SemanticRankNonincrease] using hMono
  · simpa [SemanticRankDescent] using hDesc

/-! ## Exact connection to the Stage-1 slot in ZZSemanticMass -/

/-- Same target, now in the exact `Good := SemanticBad` first-hit currency
requested by `ZZSemanticMass`. -/
theorem integratedRecoveryFirstHitMass_of_rank
    (regime : OperationalRegime n ψ) (κ : Nat)
    (hMono : SemanticRankNonincrease regime κ)
    (hDesc : SemanticRankDescent regime κ) :
    IntegratedSemanticMassInventory.IntegratedRecoveryFirstHitMass
      regime κ (SemanticRepairTarget regime κ)
      (ZZBellmanTemplate.rankHalfH n n) 2 := by
  classical
  unfold IntegratedSemanticMassInventory.IntegratedRecoveryFirstHitMass
  intro C _hSemanticBad
  by_cases hT : SemanticRepairTarget regime κ C
  · have hz := BirthTwoStageEscape.avoidCount_zero_of
      (IntegratedSemanticMassInventory.semStep regime κ)
      (IntegratedSemanticMassInventory.SemanticBad regime κ)
      (SemanticRepairTarget regime κ) C
      (fun h => h.2 hT) (ZZBellmanTemplate.rankHalfH n n)
    rw [hz]
    simp
  · have hBell := ZZBellmanTemplate.rank_half_avoidCount
      (step := IntegratedSemanticMassInventory.semStep regime κ)
      (Bad := SemanticRepairBad regime κ)
      (rank := semanticRepairRank regime κ)
      (K := n)
      (hbound := semanticRepairRank_le_n regime κ)
      (hmono := by simpa [SemanticRankNonincrease] using hMono)
      (hdesc := by simpa [SemanticRankDescent] using hDesc)
    have hBellC := hBell C hT
    have hBell' :
        2 * avoidCount
          (IntegratedSemanticMassInventory.semStep regime κ)
          (fun _ : SemCfg regime κ => True)
          (SemanticRepairTarget regime κ) C
          (ZZBellmanTemplate.rankHalfH n n) ≤
        n ^ ZZBellmanTemplate.rankHalfH n n := by
      simpa [SemanticRepairBad] using hBellC
    have hm := B6LocalReverseFill.avoidCount_mono_good
      (IntegratedSemanticMassInventory.semStep regime κ)
      (IntegratedSemanticMassInventory.SemanticBad regime κ)
      (fun _ : SemCfg regime κ => True)
      (SemanticRepairTarget regime κ)
      (fun _ _ => True.intro) C (ZZBellmanTemplate.rankHalfH n n)
    calc
      2 * avoidCount
          (IntegratedSemanticMassInventory.semStep regime κ)
          (IntegratedSemanticMassInventory.SemanticBad regime κ)
          (SemanticRepairTarget regime κ) C
          (ZZBellmanTemplate.rankHalfH n n)
          ≤ 2 * avoidCount
            (IntegratedSemanticMassInventory.semStep regime κ)
            (fun _ : SemCfg regime κ => True)
            (SemanticRepairTarget regime κ) C
            (ZZBellmanTemplate.rankHalfH n n) :=
              Nat.mul_le_mul_left 2 hm
      _ ≤ n ^ ZZBellmanTemplate.rankHalfH n n := hBell'
      _ = (2 - 1) * n ^ ZZBellmanTemplate.rankHalfH n n := by simp

/-! ## Stage-level obligations remaining after reading the actual source -/

/-- The fields relevant to T7 are framed by a pair of raw states. -/
def T7FieldsFrame
    (l r l' r' : AgentState ψ) : Prop :=
  l'.bullet = l.bullet ∧
  l'.signal_B = l.signal_B ∧
  r'.bullet = r.bullet ∧
  r'.signal_B = r.signal_B

/-- Everything before SUPPRESS_SIG should frame the two T7 fields. -/
def IntegratedBeforeSuppressT7Frame
    (hψ : ψ > 0) (κ : Nat) : Prop :=
  ∀ l r : AgentState ψ,
    let q := ppllIntegratedBeforeSuppress hψ κ l r
    T7FieldsFrame l r q.1 q.2

/-- SUPPRESS_SIG itself writes only reset/echo/count. -/
def SuppressSigT7Frame (hψ : ψ > 0) : Prop :=
  ∀ l r : AgentState ψ,
    let q := suppressSig hψ l r
    T7FieldsFrame l r q.1 q.2

/-- WRITE_SEQ writes no bullet/signal_B fields. -/
def WriteSeqT7Frame (hψ : ψ > 0) : Prop :=
  ∀ l r : AgentState ψ,
    let q := writeSeq hψ l r
    T7FieldsFrame l r q.1 q.2

noncomputable def rawT7DefectBit (u : AgentState ψ) : Nat := by
  classical
  exact if LiveBulletSignalExclusive u then 0 else 1

/-- The only stage allowed to touch T7 fields must not increase their total
local defect count. -/
def NoCollisionT7PairNonincrease (hψ : ψ > 0) : Prop :=
  ∀ l r : AgentState ψ,
    let q := eliminateLeadersNoCollision hψ l r
    rawT7DefectBit q.1 + rawT7DefectBit q.2 ≤
      rawT7DefectBit l + rawT7DefectBit r

/-- Strong local descent fact suggested by the actual Algorithm-15 repair:
a violating responder should be repaired by this service. -/
def NoCollisionT7RepairsResponder (hψ : ψ > 0) : Prop :=
  ∀ l r : AgentState ψ,
    ¬ LiveBulletSignalExclusive r →
    LiveBulletSignalExclusive (eliminateLeadersNoCollision hψ l r).2

/-- Exact bounded local form; `erase_integratedBoundedTransition` is the bridge
from the preceding raw stage obligations to this statement. -/
def IntegratedBoundedPairT7Nonincrease
    (hψ : ψ > 0) (κ : Nat) : Prop :=
  ∀ l r : BoundedAgentState ψ κ,
    let q := integratedBoundedTransition hψ κ l r
    t7DefectBit q.1 + t7DefectBit q.2 ≤
      t7DefectBit l + t7DefectBit r

/-- Bounded responder form needed for the ring descent selector. -/
def IntegratedBoundedT7RepairsResponder
    (hψ : ψ > 0) (κ : Nat) : Prop :=
  ∀ l r : BoundedAgentState ψ κ,
    ¬ T7RepairedCell r →
    T7RepairedCell (integratedBoundedTransition hψ κ l r).2

/-- This is the exact remaining stage-2 semantic obligation if the T7-clean
class is used as the intermediate recovery target. -/
def PostT7SemanticSafetyMass
    (regime : OperationalRegime n ψ) (κ B2 Q2 : Nat) : Prop :=
  IntegratedSemanticMassInventory.IntegratedStage2SafetyMass
    regime κ (SemanticRepairTarget regime κ) B2 Q2

#print axioms ZZSemanticRecoveryC.bounded_count_le_kappa
#print axioms ZZSemanticRecoveryC.semanticRepairRank_nonneg
#print axioms ZZSemanticRecoveryC.semanticRepairRank_le_n
#print axioms ZZSemanticRecoveryC.semanticRepairRank_eq_zero_iff_target
#print axioms ZZSemanticRecoveryC.semanticRankBound_proved
#print axioms ZZSemanticRecoveryC.semanticRepair_half_mass_of_rank
#print axioms ZZSemanticRecoveryC.integratedRecoveryFirstHitMass_of_rank

end ZZSemanticRecoveryC
