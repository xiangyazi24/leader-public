import Leader.Wu.Birth.InstalledBlockEscape
import Leader.Wu.Splice.NeutralOrbitLift
import Leader.Wu.Birth.LeafBoost
import Leader.Wu.Entrance.CalibratedLeaf

set_option autoImplicit false
set_option Elab.async false

namespace ZZStage2Leaf

open BirthLeaderlessBirthMassRenewal BirthTwoStageEscape

variable {n ψ κ τ : Nat}

abbrev ConfigV3 (n ψ κ τ : Nat) :=
  ZZFinalCarrierV3.Config n ψ κ τ

/-- The exact scheduler-visible V3 final step. -/
noncomputable def stepV3
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) :
    ConfigV3 n ψ κ τ → Fin n → ConfigV3 n ψ κ τ :=
  ZZFinalCarrierV3.stepConcreteV3
    (κ := κ) (τ := τ) hψ h2 ring

@[simp] theorem stepV3_eq_exact
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) :
    stepV3 (κ := κ) (τ := τ) hψ h2 ring =
      ZZFinalCarrierV3.stepConcreteV3
        (κ := κ) (τ := τ) hψ h2 ring := by
  rfl

/-!
A local `PopulationProtocol` package for the semantic `IsSafe` vocabulary.
For n=1 its generic `PopulationProtocol.step` is not asserted equal to
`stepConcreteV3`, which has an explicit self-edge branch.  This causes no drift
below: only the *present unique-output* conjunct of `IsSafe` is used to prove
that a leaderless configuration is not safe.  The actual mass process is always
`stepV3 = stepConcreteV3`.
-/
noncomputable def semanticProtocolV3
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) : PopulationProtocol where
  Q := ZZFinalCarrierV3.Cell ψ κ τ
  Y := Bool
  transition :=
    ZZFinalCarrierV3.rowFinalV3
      (κ := κ) (τ := τ) hψ h2
      (ZZFinalCarrierV3.concretePortV3
        (κ := κ) (τ := τ) hψ h2)
  output := ZZBlockEscape.outputFinalV3

/-- Semantic Definition-1 safety for the natural local V3 final protocol. -/
def IsSafeV3
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : ConfigV3 n ψ κ τ) : Prop :=
  PopulationProtocol.IsSafe
    (semanticProtocolV3 (κ := κ) (τ := τ) hψ h2)
    ring C (fun b : Bool => b)

/--
The bad predicate: currently leaderless and not semantically
safe.  `FinalLeaderlessV3` is the exact Good predicate used by `ZZBlockEscape`.
-/
def B
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : ConfigV3 n ψ κ τ) : Prop :=
  ZZBlockEscape.FinalLeaderlessV3 C ∧
    ¬ IsSafeV3 (κ := κ) (τ := τ) hψ h2 ring C

/-- `PopulationProtocol.IsSafe` requires a present unique leader output. -/
theorem finalLeaderless_not_isSafeV3
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : ConfigV3 n ψ κ τ)
    (hL : ZZBlockEscape.FinalLeaderlessV3 C) :
    ¬ IsSafeV3 (κ := κ) (τ := τ) hψ h2 ring C := by
  intro hS
  rcases hS.1 with ⟨i, hi, _⟩
  have hi' : ZZBlockEscape.outputFinalV3 (C i) = true := by
    simpa [semanticProtocolV3] using hi
  have h0 := hL i
  rw [hi'] at h0
  cases h0

/-- Hence the extra `¬ IsSafe` conjunct does not change the G3 Good set. -/
theorem B_iff_finalLeaderlessV3
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : ConfigV3 n ψ κ τ) :
    B (κ := κ) (τ := τ) hψ h2 ring C ↔
      ZZBlockEscape.FinalLeaderlessV3 C := by
  constructor
  · intro h
    exact h.1
  · intro h
    exact ⟨h, finalLeaderless_not_isSafeV3 hψ h2 ring C h⟩

private theorem B_eq_finalLeaderlessV3
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) :
    B (κ := κ) (τ := τ) hψ h2 ring =
      (fun C : ConfigV3 n ψ κ τ =>
        ZZBlockEscape.FinalLeaderlessV3 C) := by
  funext C
  apply propext
  exact B_iff_finalLeaderlessV3 hψ h2 ring C

/--
Exact V3 analogue of `B9ControllerRecovery.RecoveryTarget`:
`SpliceSafeV7g ∨ all-neutral`, evaluated on `oldConfigV3`.
Source: `Leader/Wu/Splice/ControllerRecovery.lean:644-647`.
-/
def RecoveryTargetV3
    (hψ : 0 < ψ) (ring : DirectedRing n)
    (C : ConfigV3 n ψ κ τ) : Prop :=
  B9ControllerRecovery.RecoveryTarget hψ ring
    (ZZFinalCarrierV3.oldConfigV3 C)

/-- The recovery target is genuinely inhabited: the compiled orbit lift is
outer-neutral, so its old projection satisfies the all-neutral disjunct. -/
theorem recoveryTargetV3_nonvacuous :
    ∃ C : ConfigV3 6 3 3 48,
      RecoveryTargetV3 ZZOrbitLiftClean.h3
        ZZOrbitLiftClean.ring6 C := by
  refine ⟨ZZOrbitLiftClean.liftC, ?_⟩
  unfold RecoveryTargetV3 B9ControllerRecovery.RecoveryTarget
  right
  intro i
  exact ⟨rfl, rfl, rfl⟩

/-!
FIRST MISSING V3 DECLARATION.

This is the exact retyping of
`B9RecoveryJ3Direct.stepConcrete_oldConfig_eq_stepRecover_of_finalGarbage`.
`ZZG3PositiveRoute.V3GarbageProjection` records the same statement only as a
`Prop`; no theorem producer was found on current main.
-/
def V3GarbageProjection
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) : Prop :=
  ∀ (oldHost : B9Host.HostRow (B9FullCarrierHost.OldPhys ψ κ τ))
    (C : ConfigV3 n ψ κ τ) (e : Fin n),
    ZZFinalCarrierV3.FinalGarbageV3 hψ
        (C e) (C (ring.rightNeighbor e)) →
    ZZFinalCarrierV3.oldConfigV3
        (stepV3 hψ h2 ring C e) =
      B9ControllerRecovery.stepRecover oldHost hψ ring
        (ZZFinalCarrierV3.oldConfigV3 C) e

/--
The V3 first-hit mass after the missing recovery transport has been supplied.
Stage 1 constants are fixed by the existing stopped-rank theorem:
`B1 = RecoveryB n`, `Q1 = RecoveryQ n`.
-/
def RecoveryFirstHitMassV3
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) : Prop :=
  ∀ C : ConfigV3 n ψ κ τ,
    B9ControllerRecovery.RecoveryQ n *
        avoidCount (stepV3 hψ h2 ring)
          (fun _ : ConfigV3 n ψ κ τ => True)
          (RecoveryTargetV3 hψ ring) C
          (B9ControllerRecovery.RecoveryB n) ≤
      (B9ControllerRecovery.RecoveryQ n - 1) *
        n ^ B9ControllerRecovery.RecoveryB n

/-- Stage 1 in the exact `Good := B` currency required by `two_stage_escape`. -/
def RecoveryFirstHitMassOnB
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) : Prop :=
  ∀ C : ConfigV3 n ψ κ τ,
    B (κ := κ) (τ := τ) hψ h2 ring C →
    B9ControllerRecovery.RecoveryQ n *
        avoidCount (stepV3 hψ h2 ring)
          (B (κ := κ) (τ := τ) hψ h2 ring)
          (RecoveryTargetV3 hψ ring) C
          (B9ControllerRecovery.RecoveryB n) ≤
      (B9ControllerRecovery.RecoveryQ n - 1) *
        n ^ B9ControllerRecovery.RecoveryB n

/-- The `Good=True` recovery first-hit theorem mechanically supplies the
`Good=B` first-stage hypothesis; no closure or PairRiskNoRaise is used. -/
theorem recoveryFirstHitMassOnB_of_true
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (hFirst : RecoveryFirstHitMassV3
      (κ := κ) (τ := τ) hψ h2 ring) :
    RecoveryFirstHitMassOnB (κ := κ) (τ := τ) hψ h2 ring := by
  unfold RecoveryFirstHitMassOnB
  intro C _hB
  have hm := B6LocalReverseFill.avoidCount_mono_good
    (stepV3 (κ := κ) (τ := τ) hψ h2 ring)
    (B (κ := κ) (τ := τ) hψ h2 ring)
    (fun _ : ConfigV3 n ψ κ τ => True)
    (RecoveryTargetV3 hψ ring)
    (fun _ _ => True.intro) C (B9ControllerRecovery.RecoveryB n)
  unfold RecoveryFirstHitMassV3 at hFirst
  exact
    (Nat.mul_le_mul_left (B9ControllerRecovery.RecoveryQ n) hm).trans
      (hFirst C)

/--
THE STAGE-2 LEADERSHIP LEAF.

`RecoveryTargetV3` is a starting hypothesis only.  The `aliveCount` Good
predicate remains `B` throughout the whole stage-2 word.
-/
def Stage2LeadershipMassV3
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (B2 Q2 : Nat) : Prop :=
  ∀ C : ConfigV3 n ψ κ τ,
    B (κ := κ) (τ := τ) hψ h2 ring C →
    RecoveryTargetV3 hψ ring C →
    Q2 * aliveCount
        (stepV3 (κ := κ) (τ := τ) hψ h2 ring)
        (B (κ := κ) (τ := τ) hψ h2 ring) C B2 ≤
      (Q2 - 1) * n ^ B2

/-- Honest current gap: the stack supplies no fixed numerical `B2,Q2` for V3. -/
def Stage2LeadershipExistsV3
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) : Prop :=
  ∃ B2 Q2 : Nat,
    1 ≤ Q2 ∧
      Stage2LeadershipMassV3
        (κ := κ) (τ := τ) hψ h2 ring B2 Q2

/-- Same stage-2 statement written directly in `ZZBlockEscape`'s Good currency. -/
def Stage2LeadershipMassFinalLeaderlessV3
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (B2 Q2 : Nat) : Prop :=
  ∀ C : ConfigV3 n ψ κ τ,
    ZZBlockEscape.FinalLeaderlessV3 C →
    RecoveryTargetV3 hψ ring C →
    Q2 * aliveCount
        (stepV3 (κ := κ) (τ := τ) hψ h2 ring)
        ZZBlockEscape.FinalLeaderlessV3 C B2 ≤
      (Q2 - 1) * n ^ B2

/-- No predicate drift: the semantic bad predicate and the consumer Good
predicate give literally the same stage-2 interface. -/
theorem stage2_B_iff_finalLeaderlessV3
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (B2 Q2 : Nat) :
    Stage2LeadershipMassV3
        (κ := κ) (τ := τ) hψ h2 ring B2 Q2 ↔
      Stage2LeadershipMassFinalLeaderlessV3
        (κ := κ) (τ := τ) hψ h2 ring B2 Q2 := by
  unfold Stage2LeadershipMassV3
    Stage2LeadershipMassFinalLeaderlessV3
  rw [B_eq_finalLeaderlessV3 hψ h2 ring]

/--
Old-carrier-shaped *candidate only*: current `CFinalAssembly3` uses this
`B2,Q2` pair on `FinalCandidateR2C.stepConcrete`.  There is no V3 producer of
this statement merely from that old theorem.
-/
def OldRouteShapedStage2CandidateV3
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) : Prop :=
  Stage2LeadershipMassV3
    (κ := κ) (τ := τ) hψ h2 ring
    (CFinalAssembly2.FinalLeafHV2 n ψ) 8

/--
Exact public `two_stage_escape` call site.

Discharged/listed hypotheses:
* `Q1 = RecoveryQ n >= 1`: from `ring.hn` and `RecoveryQ n = n^RecoveryB n`;
* `Q2 >= 1`: explicit `hQ2`;
* stage 1: `RecoveryFirstHitMassOnB`;
* stage 2: `Stage2LeadershipMassV3`.
-/
theorem two_stage_escape_call
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (B2 Q2 : Nat) (hQ2 : 1 ≤ Q2)
    (hStage1 : RecoveryFirstHitMassOnB
      (κ := κ) (τ := τ) hψ h2 ring)
    (hStage2 : Stage2LeadershipMassV3
      (κ := κ) (τ := τ) hψ h2 ring B2 Q2) :
    UniformEscapeMass
      (stepV3 (κ := κ) (τ := τ) hψ h2 ring)
      (B (κ := κ) (τ := τ) hψ h2 ring)
      (B9ControllerRecovery.RecoveryB n + B2)
      (B9ControllerRecovery.RecoveryQ n * Q2) := by
  unfold RecoveryFirstHitMassOnB at hStage1
  unfold Stage2LeadershipMassV3 at hStage2
  have hQ1 : 1 ≤ B9ControllerRecovery.RecoveryQ n := by
    unfold B9ControllerRecovery.RecoveryQ
    have hp : 0 < n ^ B9ControllerRecovery.RecoveryB n :=
      Nat.pow_pos ring.hn
    omega
  exact BirthTwoStageEscape.two_stage_escape
    (stepV3 (κ := κ) (τ := τ) hψ h2 ring)
    (B (κ := κ) (τ := τ) hψ h2 ring)
    (RecoveryTargetV3 hψ ring)
    (B9ControllerRecovery.RecoveryB n) B2
    (B9ControllerRecovery.RecoveryQ n) Q2
    hQ1 hQ2 hStage1 hStage2

/-- The same call rewritten to the exact Good used by `ZZBlockEscape`. -/
theorem two_stage_escape_call_finalLeaderlessV3
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (B2 Q2 : Nat) (hQ2 : 1 ≤ Q2)
    (hStage1 : RecoveryFirstHitMassOnB
      (κ := κ) (τ := τ) hψ h2 ring)
    (hStage2 : Stage2LeadershipMassV3
      (κ := κ) (τ := τ) hψ h2 ring B2 Q2) :
    UniformEscapeMass
      (stepV3 (κ := κ) (τ := τ) hψ h2 ring)
      ZZBlockEscape.FinalLeaderlessV3
      (B9ControllerRecovery.RecoveryB n + B2)
      (B9ControllerRecovery.RecoveryQ n * Q2) := by
  have h := two_stage_escape_call
    (κ := κ) (τ := τ) hψ h2 ring B2 Q2 hQ2 hStage1 hStage2
  rw [B_eq_finalLeaderlessV3 hψ h2 ring] at h
  exact h

/-- Q=8 normalization horizon after the two-stage product. -/
def BoostedLeafH (n B2 Q2 : Nat) : Nat :=
  3 * (B9ControllerRecovery.RecoveryQ n * Q2) *
    (B9ControllerRecovery.RecoveryB n + B2)

/--
Exact `ZZBlockEscape` leaf type, with no step or Good drift.
The only change is the explicitly displayed boosted horizon.
`hn : 2 ≤ n` is carried because the active G3 leaf excludes the n=1 self-edge
counterexample (ERRATA R247 / campaign board).
-/
theorem two_stage_boosted_ZZBlockEscape_leaf
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (hn : 2 ≤ n)
    (B2 Q2 : Nat) (hQ2 : 1 ≤ Q2)
    (hStage1 : RecoveryFirstHitMassOnB
      (κ := κ) (τ := τ) hψ h2 ring)
    (hStage2 : Stage2LeadershipMassV3
      (κ := κ) (τ := τ) hψ h2 ring B2 Q2) :
    ZZBlockEscape.StateUniformFixedWindowEscapeV3
      n ψ κ τ (BoostedLeafH n B2 Q2) hψ h2 ring
      ZZBlockEscape.FinalLeaderlessV3 := by
  have hm := two_stage_escape_call_finalLeaderlessV3
    (κ := κ) (τ := τ) hψ h2 ring B2 Q2 hQ2 hStage1 hStage2
  have hn0 : 0 < n := by omega
  have hQ1pos : 0 < B9ControllerRecovery.RecoveryQ n := by
    unfold B9ControllerRecovery.RecoveryQ
    exact Nat.pow_pos hn0
  have hQ2pos : 0 < Q2 := by omega
  have hQprod : 1 ≤ B9ControllerRecovery.RecoveryQ n * Q2 := by
    have hp : 0 < B9ControllerRecovery.RecoveryQ n * Q2 :=
      Nat.mul_pos hQ1pos hQ2pos
    omega
  change UniformEscapeMass
    (stepV3 (κ := κ) (τ := τ) hψ h2 ring)
    ZZBlockEscape.FinalLeaderlessV3
    (BoostedLeafH n B2 Q2) 8
  unfold BoostedLeafH
  exact BirthLeafBoost.escape_boost
    (stepV3 (κ := κ) (τ := τ) hψ h2 ring)
    ZZBlockEscape.FinalLeaderlessV3
    (B9ControllerRecovery.RecoveryB n + B2)
    (B9ControllerRecovery.RecoveryQ n * Q2)
    hQprod hm

#print axioms ZZStage2Leaf.finalLeaderless_not_isSafeV3
#print axioms ZZStage2Leaf.recoveryTargetV3_nonvacuous
#print axioms ZZStage2Leaf.recoveryFirstHitMassOnB_of_true
#print axioms ZZStage2Leaf.stage2_B_iff_finalLeaderlessV3
#print axioms ZZStage2Leaf.two_stage_escape_call
#print axioms ZZStage2Leaf.two_stage_boosted_ZZBlockEscape_leaf

end ZZStage2Leaf
