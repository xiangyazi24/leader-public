import Leader.Wu.Splice.InstalledCarrier
import Leader.Wu.Splice.ControllerRecoveryMass
import Leader.Wu.Splice.RecoveryFinalStepMass
import Leader.Wu.Splice.HoldRepairPhysicalRate
import Leader.Wu.Coherence.TokenFreeMixedRowMoves
import Leader.Wu.Splice.KeepConsumesPending
import Leader.Wu.Birth.LeaderlessBirthMassRenewal
import Leader.Wu.Birth.TwoStageEscape
import Leader.Wu.Entrance.LocalReverseFill

set_option autoImplicit false
set_option Elab.async false

namespace ZZG3PositiveRoute

open PPLL
open B9Host B9FullCarrierHost
open B9ControllerRecovery
open BirthLeaderlessBirthMassRenewal BirthTwoStageEscape
open ZZFinalCarrierV3

variable {n ψ κ τ : Nat}

abbrev ConfigV3 (n ψ κ τ : Nat) :=
  ZZFinalCarrierV3.Config n ψ κ τ

noncomputable def stepV3
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) :
    ConfigV3 n ψ κ τ → Fin n → ConfigV3 n ψ κ τ :=
  ZZFinalCarrierV3.stepConcreteV3
    (κ := κ) (τ := τ) hψ h2 ring

def rawLeaderV3 (u : ZZFinalCarrierV3.Cell ψ κ τ) : Bool :=
  (R2CoherenceV31.raw u.phys).leader

def HasLeaderV3 (C : ConfigV3 n ψ κ τ) : Prop :=
  ∃ i : Fin n, rawLeaderV3 (C i) = true

def LeaderlessV3 (C : ConfigV3 n ψ κ τ) : Prop :=
  ∀ i : Fin n, rawLeaderV3 (C i) = false

/-- The actual G3 target: a leader exists. -/
def G3TargetV3 (C : ConfigV3 n ψ κ τ) : Prop :=
  HasLeaderV3 C

/-- Exact bad set for G3: leaderless and outside the actual success target. -/
def B (C : ConfigV3 n ψ κ τ) : Prop :=
  LeaderlessV3 C ∧ ¬ G3TargetV3 C

/-- Intermediate recovery target only.  This is not the G3 target. -/
def RecoveryTargetV3
    (hψ : 0 < ψ) (ring : DirectedRing n)
    (C : ConfigV3 n ψ κ τ) : Prop :=
  B9ControllerRecovery.RecoveryTarget hψ ring
    (ZZFinalCarrierV3.oldConfigV3 C)

noncomputable def recoveryRankV3
    (hψ : 0 < ψ) (ring : DirectedRing n)
    (C : ConfigV3 n ψ κ τ) : Nat :=
  B9ControllerRecovery.recoveryRank hψ ring
    (ZZFinalCarrierV3.oldConfigV3 C)

/--
PRODUCER: `B9ControllerRecovery.recoveryRank_le_six_mul`.
The rank is Nat-valued and bounded by `RecoveryB n = 6*n`.
-/
def RecoveryRankBoundV3
    (hψ : 0 < ψ) (ring : DirectedRing n) : Prop :=
  ∀ C : ConfigV3 n ψ κ τ,
    recoveryRankV3 hψ ring C ≤ B9ControllerRecovery.RecoveryB n

/--
FIRST NO CURRENT PRODUCER at main@4516b7a5.
Expected proof template:
`B9RecoveryJ3Direct.stepConcrete_oldConfig_eq_stepRecover_of_finalGarbage`,
retyped from `recoverPair`/`oldConfig` to `recoverPairV3`/`oldConfigV3`.
The recovery branch is selected before the B9 port row is consulted.
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
EXPECTED PRODUCERS: `V3GarbageProjection`, the existing recovery-rank
strict-drop lemmas, and the exact proof pattern of
`B9RecoveryJ3Direct.finalRecoveryRankJ3_descent`.
No `PairRiskNoRaise` premise is required for this existential descent.
-/
def RecoveryDescentV3
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) : Prop :=
  ∀ C : ConfigV3 n ψ κ τ,
    ¬ RecoveryTargetV3 hψ ring C →
    ∃ e : Fin n,
      recoveryRankV3 hψ ring (stepV3 hψ h2 ring C e) <
        recoveryRankV3 hψ ring C

/--
EXPECTED PRODUCERS: `RecoveryRankBoundV3`, `RecoveryDescentV3`, and
`B9ControllerRecovery.avoidCount_lt_pow_of_rank_descent`.
Exact old-final model:
`B9RecoveryJ3Direct.finalRecovery_first_hit_mass_j3`.
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

/--
EXPECTED PRODUCERS: `RecoveryFirstHitMassV3` plus
`B6LocalReverseFill.avoidCount_mono_good`.
This is the exact stage-one shape needed by `two_stage_escape` with `Good := B`.
-/
def RecoveryFirstHitMassOnB
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) : Prop :=
  ∀ C : ConfigV3 n ψ κ τ,
    B C →
    B9ControllerRecovery.RecoveryQ n *
        avoidCount (stepV3 hψ h2 ring)
          B (RecoveryTargetV3 hψ ring) C
          (B9ControllerRecovery.RecoveryB n) ≤
      (B9ControllerRecovery.RecoveryQ n - 1) *
        n ^ B9ControllerRecovery.RecoveryB n

/--
FIRST SUBSTANTIVE G3 GAP: no current producer at main@4516b7a5.
Needed after the recovery target has been reached.
Partial ingredients only:
* `B9SpliceV10jGlobalProgress.globalProgressWithin3J` gives old-V10j
  physical service OR controller-potential drop from `SpliceSafeV7g`;
* `B9SpliceV10jPhysicalRate.noPhysical_one_over_n` quantifies time to an
  old-V10j physical service, not to a leader under `stepConcreteV3`;
* `ZZV31RowEscapesTokenFreeMixed.stepV3_allEdgesTokenFreeMixed_ne` gives
  nonidentity only on the token-free mixed subfamily;
* `ZZKeepConsumesPending` drains the four dg guards locally, while R243 shows
  pending can be recreated elsewhere.
-/
def PostRecoveryEscapeMassV3
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (L Q : Nat) : Prop :=
  ∀ C : ConfigV3 n ψ κ τ,
    B C →
    RecoveryTargetV3 hψ ring C →
    Q * aliveCount (stepV3 hψ h2 ring) B C L ≤
      (Q - 1) * n ^ L

/--
The requested state-level progress disjunction.
EXPECTED PRODUCERS: `RecoveryDescentV3` outside `RecoveryTargetV3`, and
`PostRecoveryEscapeMassV3` inside it.
-/
def EveryBadStateProgressOrExitV3
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (L Q : Nat) : Prop :=
  ∀ C : ConfigV3 n ψ κ τ,
    B C →
      (∃ e : Fin n,
        recoveryRankV3 hψ ring (stepV3 hψ h2 ring C e) <
          recoveryRankV3 hψ ring C) ∨
      (RecoveryTargetV3 hψ ring C ∧
        Q * aliveCount (stepV3 hψ h2 ring) B C L ≤
          (Q - 1) * n ^ L)

def G3BlockH (n L : Nat) : Nat :=
  B9ControllerRecovery.RecoveryB n + L

def G3BlockQ (n Q : Nat) : Nat :=
  B9ControllerRecovery.RecoveryQ n * Q

/--
Exact one-block currency consumed by `alive_tail`.
EXPECTED PRODUCER: `BirthTwoStageEscape.two_stage_escape`, with stage one
`RecoveryFirstHitMassOnB` and stage two `PostRecoveryEscapeMassV3`.
-/
def G3UniformEscapeMassV3
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (L Q : Nat) : Prop :=
  UniformEscapeMass (stepV3 (κ := κ) (τ := τ) hψ h2 ring)
    (B (n := n) (ψ := ψ) (κ := κ) (τ := τ))
    (G3BlockH n L) (G3BlockQ n Q)

/-- Exact hypotheses for the two-stage bounded-window conclusion. -/
def G3TwoStageRouteV3
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (L Q : Nat) : Prop :=
  1 ≤ Q →
  RecoveryFirstHitMassOnB (κ := κ) (τ := τ) hψ h2 ring →
  PostRecoveryEscapeMassV3 (κ := κ) (τ := τ) hψ h2 ring L Q →
  G3UniformEscapeMassV3 (κ := κ) (τ := τ) hψ h2 ring L Q

/--
Exact geometric-tail conclusion obtained from one uniform block.
EXPECTED PRODUCER: `BirthLeaderlessBirthMassRenewal.alive_tail`.
-/
def G3AliveTailV3
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (L Q : Nat) : Prop :=
  ∀ (k : Nat) (C : ConfigV3 n ψ κ τ),
    B C →
    (G3BlockQ n Q) ^ k *
        aliveCount (stepV3 hψ h2 ring) B C
          (k * G3BlockH n L) ≤
      (G3BlockQ n Q - 1) ^ k *
        n ^ (k * G3BlockH n L)

/-- Exact implication into `alive_tail`; no new stochastic machinery. -/
def G3AliveTailRouteV3
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (L Q : Nat) : Prop :=
  G3UniformEscapeMassV3 (κ := κ) (τ := τ) hψ h2 ring L Q →
  G3AliveTailV3 (κ := κ) (τ := τ) hψ h2 ring L Q

end ZZG3PositiveRoute
