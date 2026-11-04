import Leader.Wu.Scheduler.ClosedDomainAmplification
import Leader.Wu.Seal.PositiveLanding

/-!
# Exact iid-scheduler bounds for positive all-closed seal-sweep starts

The deterministic seal-sweep landing theorem supplies one favorable edge word
of length at most `2 * n - 2` from every all-closed configuration containing a
leader.  The exact finite scheduler therefore gives an unconditional one-block
failure numerator `n^(2*n-2) - 1` on that initial class.

Geometric amplification needs a separate restart fact.  The initial class is
not step-closed: a closed leader followed by a closed follower launches an open
anchor/probe pair.  This file therefore does not silently feed that class to a
closed-domain theorem.  Instead it closes the domain under actual reachability
and names the remaining obligation precisely: every nonsafe reachable
descendant must itself have a bounded favorable word.  Supplying that one
protocol lemma gives the exact `k`-block numerator
`(n^L - 1)^k` among `n^(k*L)` iid uniform edge words.

No infinite probability space or independence postulate is used.  The result is an
exact count over `allSchedules`; the product law is the scheduler-list block
decomposition proved in `SchedulerBlocks` and its closed-domain refinement.
-/

namespace PPLLCompleteMultiLeaderCleanup
namespace PPartialSealSweepUniformSchedulerSol

open PPLL PPLLResearchFormulation PPLLTraceConvergence
open PPLLSchedulerBlocks
open PPLLClosedDomainSchedulerAmplificationSol
open PPartialDynamicSweepLockSol
open PPartialDynamicSweepResetSol
open PPartialSealSweepOverlaySol
open PPartialSealSweepPositiveLandingSol

set_option autoImplicit false

variable {n psi kappa tau : Nat}

/-! ## Initial and reachable domains -/

/-- The exact initial class covered by the deterministic positive landing
theorem: every seal is closed and at least one current leader exists. -/
def SealSweepAllClosedPositive
    (C : SealSweepConfig n psi kappa tau) : Prop :=
  SealSweepAllClosed C ∧ 0 < sealSweepLeaderCount C

/-- Reachability closure of the positive all-closed initial class.  Unlike the
initial class itself, this domain contains the open anchor/probe configurations
created by arbitrary scheduler prefixes. -/
def SealSweepPositiveDescendant
    (ring : DirectedRing n)
    (D : SealSweepConfig n psi kappa tau) : Prop :=
  ∃ C : SealSweepConfig n psi kappa tau,
    SealSweepAllClosedPositive C ∧
      PopulationProtocol.Reachable
        (P_partialSealSweepProtocol psi kappa tau) ring C D

/-- Every authorized initial configuration belongs to its reachability
closure. -/
theorem allClosedPositive_mem_positiveDescendant
    (ring : DirectedRing n)
    (C : SealSweepConfig n psi kappa tau)
    (hC : SealSweepAllClosedPositive C) :
    SealSweepPositiveDescendant ring C := by
  exact ⟨C, hC,
    @PopulationProtocol.Reachable.refl n
      (P_partialSealSweepProtocol psi kappa tau) ring C⟩

/-- The descendant domain is closed under every exact local interaction. -/
theorem positiveDescendant_localStepClosed
    (ring : DirectedRing n) :
    LocalStepClosed ring
      (P_partialSealSweep (psi := psi) (kappa := kappa) (tau := tau))
      (SealSweepPositiveDescendant
        (psi := psi) (kappa := kappa) (tau := tau) ring) := by
  intro D hD e
  obtain ⟨C, hC, hreach⟩ := hD
  refine ⟨C, hC, hreach.trans ?_⟩
  apply PopulationProtocol.OneStep.to_reachable
  refine ⟨e, ?_⟩
  exact localStep_eq_protocol_step
    (P_partialSealSweepProtocol psi kappa tau) ring D e

/-! ## A Boolean view of genuine Definition-1 safety -/

/-- Classical Boolean test for genuine semantic safety.  It is used only to
connect finite Boolean schedule counting to `stabilizingScheduleCount`; no
computation or compiler-trusted decision procedure is involved. -/
noncomputable def sealSweepIsSafeTest
    (ring : DirectedRing n)
    (C : SealSweepConfig n psi kappa tau) : Bool := by
  classical
  exact if PopulationProtocol.IsSafe
      (P_partialSealSweepProtocol psi kappa tau) ring C isLeaderOutput
    then true else false

/-- The classical Boolean test decides exactly Definition-1 safety. -/
theorem sealSweepIsSafeTest_spec
    (ring : DirectedRing n)
    (C : SealSweepConfig n psi kappa tau) :
    sealSweepIsSafeTest ring C = true ↔
      PopulationProtocol.IsSafe
        (P_partialSealSweepProtocol psi kappa tau) ring C
        isLeaderOutput := by
  classical
  simp [sealSweepIsSafeTest]

/-! ## Unconditional one-block iid bound -/

/-- The deterministic positive landing theorem is exactly a bounded safe-word
producer on the initial class. -/
theorem allClosedPositive_boundedSafeProducer
    (ring : DirectedRing n) :
    BoundedSafeScheduleProducer ring P_partialSealSweep
      SealSweepAllClosedPositive
      (fun C => PopulationProtocol.IsSafe
        (P_partialSealSweepProtocol psi kappa tau) ring C
        isLeaderOutput)
      (2 * n - 2) := by
  intro C hC hnotSafe
  obtain ⟨word, hlength, hreach, hsafe⟩ :=
    sealSweep_allClosedPositive_reaches_isSafe_two_mul_sub_two
      ring C hC.1 hC.2
  exact ⟨word, hlength, hsafe⟩

/-- From every positive all-closed start, at most `n^(2*n-2)-1` of the
`n^(2*n-2)` iid uniform edge words miss genuine semantic safety.  This theorem
does not need the initial class to be closed because it uses only one block. -/
theorem allClosedPositive_oneBlockSSLEOn
    (ring : DirectedRing n) :
    UniformFiniteHorizonSSLEOn
      (P_partialSealSweepProtocol psi kappa tau) ring isLeaderOutput
      SealSweepAllClosedPositive
      (2 * n - 2) (n ^ (2 * n - 2) - 1) := by
  apply uniformFinitePhase_isSafe_to_SSLEOn
  exact boundedSafeProducer_oneBlockPhase
    ring P_partialSealSweep
    SealSweepAllClosedPositive
    (fun C => PopulationProtocol.IsSafe
      (P_partialSealSweepProtocol psi kappa tau) ring C
      isLeaderOutput)
    (sealSweepIsSafeTest ring)
    (sealSweepIsSafeTest_spec ring)
    (2 * n - 2)
    (allClosedPositive_boundedSafeProducer ring)

/-- Direct failure-numerator form of the one-block theorem. -/
theorem allClosedPositive_oneBlock_failureCount_le
    (ring : DirectedRing n)
    (C : SealSweepConfig n psi kappa tau)
    (hC : SealSweepAllClosedPositive C) :
    (allSchedules n (2 * n - 2)).length -
        stabilizingScheduleCount
          (P_partialSealSweepProtocol psi kappa tau) ring
          isLeaderOutput C (2 * n - 2) ≤
      n ^ (2 * n - 2) - 1 := by
  have hbound := allClosedPositive_oneBlockSSLEOn ring C hC
  omega

/-! ## Exact restartability gap and geometric amplification -/

/-- The sole protocol-specific liveness obligation still needed for repeated
blocks.  Every nonsafe state reachable from an authorized all-closed start must
have a favorable word of length at most `L`.

The existing deterministic theorem proves this statement only when `D` itself
is all closed.  Random prefixes can create open states, so that theorem alone
does not inhabit this definition. -/
def PositiveDescendantBoundedLanding
    (ring : DirectedRing n) (L : Nat) : Prop :=
  BoundedSafeScheduleProducer ring P_partialSealSweep
    (SealSweepPositiveDescendant ring)
    (fun C => PopulationProtocol.IsSafe
      (P_partialSealSweepProtocol psi kappa tau) ring C
      isLeaderOutput)
    L

/-- Once the descendant bounded-landing obligation is supplied, exact iid
block multiplication gives the geometric integer failure numerator. -/
theorem positiveDescendant_repeatedBlockSSLEOn
    (ring : DirectedRing n) (L : Nat)
    (hrestart : PositiveDescendantBoundedLanding
      (psi := psi) (kappa := kappa) (tau := tau) ring L) :
    ∀ blocks,
      UniformFiniteHorizonSSLEOn
        (P_partialSealSweepProtocol psi kappa tau) ring isLeaderOutput
        (SealSweepPositiveDescendant ring)
        (blocks * L) ((n ^ L - 1) ^ blocks) := by
  exact boundedIsSafeProducer_repeatedBlockSSLEOn
    (P_partialSealSweepProtocol psi kappa tau) ring isLeaderOutput
    (SealSweepPositiveDescendant ring)
    (sealSweepIsSafeTest ring)
    (sealSweepIsSafeTest_spec ring)
    (positiveDescendant_localStepClosed ring)
    L hrestart

/-- Initial-state specialization of the conditional repeated-block theorem,
stated directly as the number of failing iid schedules. -/
theorem allClosedPositive_repeatedBlock_failureCount_le
    (ring : DirectedRing n) (L blocks : Nat)
    (hrestart : PositiveDescendantBoundedLanding
      (psi := psi) (kappa := kappa) (tau := tau) ring L)
    (C : SealSweepConfig n psi kappa tau)
    (hC : SealSweepAllClosedPositive C) :
    (allSchedules n (blocks * L)).length -
        stabilizingScheduleCount
          (P_partialSealSweepProtocol psi kappa tau) ring
          isLeaderOutput C (blocks * L) ≤
      (n ^ L - 1) ^ blocks := by
  have hphase :=
    positiveDescendant_repeatedBlockSSLEOn ring L hrestart blocks
  have hbound := hphase C
    (allClosedPositive_mem_positiveDescendant ring C hC)
  omega

/-- The requested `L = 2*n-2` specialization.  The only extra hypothesis over
the unconditional one-block theorem is bounded landing from open reachable
descendants; it is not hidden as an independence or closure assumption. -/
theorem allClosedPositive_twoN_repeatedBlock_failureCount_le
    (ring : DirectedRing n) (blocks : Nat)
    (hrestart : PositiveDescendantBoundedLanding
      (psi := psi) (kappa := kappa) (tau := tau) ring (2 * n - 2))
    (C : SealSweepConfig n psi kappa tau)
    (hC : SealSweepAllClosedPositive C) :
    (allSchedules n (blocks * (2 * n - 2))).length -
        stabilizingScheduleCount
          (P_partialSealSweepProtocol psi kappa tau) ring
          isLeaderOutput C (blocks * (2 * n - 2)) ≤
      (n ^ (2 * n - 2) - 1) ^ blocks := by
  exact allClosedPositive_repeatedBlock_failureCount_le
    ring (2 * n - 2) blocks hrestart C hC

end PPartialSealSweepUniformSchedulerSol
end PPLLCompleteMultiLeaderCleanup
