import Leader.Wu.Seal.BirthBarrier
import Leader.Wu.Seal.MixedAmplification

/-!
# Short iid blocks for the one-bit birth barrier

R93 shortens the balanced-positive R91 landing word to
`M₀ = floor(n/2) * n + 3n - 3`.  This module composes that bound with the
one-bit initialization barrier.  A positive barrier state needs at most
`n-1` commitment edges before the R91 word; a zero-leader start needs one
additional birth edge.  The resulting common closed-domain block is

`L = floor(n/2) * n + 4n - 3`.

The transition and domain are unchanged.  Only the deterministic producer
and its exact finite-iid consequences are sharpened.
-/

namespace PPLLCompleteMultiLeaderCleanup
namespace PPartialSealSweepIidBirthComplexitySol

open PPLL PPLLResearchFormulation PPLLTraceConvergence
open PPLLSchedulerBlocks PPLLClosedDomainSchedulerAmplificationSol
open PPLLExpiringComparisonRepair
open PPartialDynamicSweepLockSol
open PPartialSealSweepOverlaySol
open PPartialSealSweepMixedNormalizerSol
open PPartialSealSweepIidComplexitySol
open PPartialSealSweepIidBirthRepairSol

set_option autoImplicit false

variable {n psi kappa tau : Nat}

/-! ## Exact shortened deterministic bounds -/

/-- R93's balanced-positive inner landing length. -/
def iidBirthInnerLandingLength (n : Nat) : Nat :=
  (n / 2) * n + 3 * n - 3

/-- Common block length after adding at most one birth edge and `n-1`
commitment edges. -/
def iidBirthShortBlockLength (n : Nat) : Nat :=
  (n / 2) * n + 4 * n - 3

theorem iidBirthShortBlockLength_decomposition
    (ring : DirectedRing n) :
    iidBirthShortBlockLength n =
      1 + (n - 1) + iidBirthInnerLandingLength n := by
  dsimp [iidBirthShortBlockLength, iidBirthInnerLandingLength]
  have hn := ring.hn
  omega

/-- Commit the barrier in `n-1` edges, then use R93's tight inner landing. -/
theorem iidBirthPositive_reaches_isSafe_short
    (ring : DirectedRing n) (hn : 1 < n)
    (C : IidBirthConfig n psi kappa tau)
    (hC : IidBirthPositive C) :
    ∃ word : DetSchedule n,
      word.length ≤ (n - 1) + iidBirthInnerLandingLength n ∧
      PopulationProtocol.IsSafe
        (P_partialSealIidBirthProtocol psi kappa tau) ring
        (runLocalSchedule ring P_partialSealIidBirth C word)
        isLeaderOutput := by
  obtain ⟨pre, hpreLength, hDCommitted, hDPositive⟩ :=
    iidBirthPositive_reaches_allCommitted ring hn C hC
  let D := runLocalSchedule ring P_partialSealIidBirth C pre
  change IidBirthAllCommitted D at hDCommitted
  change IidBirthPositive D at hDPositive
  obtain ⟨tail, htailLength, htailSafe⟩ :=
    sealSweep_balancedPositive_reaches_isSafe_half_tight
      ring (iidBirthErase D) hDPositive.2.1 hDPositive.2.2.1
  let E := runLocalSchedule ring P_partialSealIidBirth D tail
  have hsimulation :=
    iidBirth_committed_run_simulation ring D hDCommitted tail
  change IidBirthAllCommitted E ∧
    iidBirthErase E =
      runLocalSchedule ring P_partialSealSweep (iidBirthErase D) tail
    at hsimulation
  have hEraseSafe : PopulationProtocol.IsSafe
      (P_partialSealSweepProtocol psi kappa tau) ring
      (iidBirthErase E) isLeaderOutput := by
    rw [hsimulation.2]
    exact htailSafe
  have hESafe := iidBirthAllCommitted_lift_isSafe
    ring E hsimulation.1 hEraseSafe
  refine ⟨pre ++ tail, ?_, ?_⟩
  · simp only [List.length_append, iidBirthInnerLandingLength]
    omega
  · have hrun :
        runLocalSchedule ring P_partialSealIidBirth C (pre ++ tail) = E := by
        rw [PPLLSchedulerBlocks.runLocalSchedule_append]
    have hsafeEq := congrArg
      (fun X : IidBirthConfig n psi kappa tau =>
        PopulationProtocol.IsSafe
          (P_partialSealIidBirthProtocol psi kappa tau) ring X
          isLeaderOutput)
      hrun
    exact Eq.mpr hsafeEq hESafe

/-- One birth edge followed by the shortened positive producer reaches safety
within the common block on every nontrivial ring. -/
theorem iidBirthZeroStart_reaches_isSafe_short_nontrivial
    (ring : DirectedRing n) (hn : 1 < n)
    (C : IidBirthConfig n psi kappa tau)
    (hC : IidBirthZeroStart C) :
    ∃ word : DetSchedule n,
      word.length ≤ iidBirthShortBlockLength n ∧
      PopulationProtocol.IsSafe
        (P_partialSealIidBirthProtocol psi kappa tau) ring
        (runLocalSchedule ring P_partialSealIidBirth C word)
        isLeaderOutput := by
  let seed : Fin n := ⟨0, ring.hn⟩
  let D := localStep ring P_partialSealIidBirth C seed
  have hDPositive : IidBirthPositive D :=
    iidBirthZeroStart_localStep_positive ring hn C hC seed
  obtain ⟨tail, htailLength, htailSafe⟩ :=
    iidBirthPositive_reaches_isSafe_short ring hn D hDPositive
  refine ⟨seed :: tail, ?_, ?_⟩
  · simp only [List.length_cons]
    rw [iidBirthShortBlockLength_decomposition ring]
    omega
  · have hrun :
        runLocalSchedule ring P_partialSealIidBirth C (seed :: tail) =
          runLocalSchedule ring P_partialSealIidBirth D tail := by
        rfl
    have hsafeEq := congrArg
      (fun X : IidBirthConfig n psi kappa tau =>
        PopulationProtocol.IsSafe
          (P_partialSealIidBirthProtocol psi kappa tau) ring X
          isLeaderOutput)
      hrun
    exact Eq.mpr hsafeEq htailSafe

/-- On one agent, the single self-edge birth exactly fills the shortened
common block `L(1)=1`. -/
theorem iidBirthZeroStart_reaches_isSafe_short_singleton
    (ring : DirectedRing 1)
    (C : IidBirthConfig 1 psi kappa tau)
    (hC : IidBirthZeroStart C) :
    ∃ word : DetSchedule 1,
      word.length ≤ iidBirthShortBlockLength 1 ∧
      PopulationProtocol.IsSafe
        (P_partialSealIidBirthProtocol psi kappa tau) ring
        (runLocalSchedule ring P_partialSealIidBirth C word)
        isLeaderOutput := by
  let seed : Fin 1 := ⟨0, by omega⟩
  have hkernel := iidBirthZeroStart_localStep_singleton
    ring C hC seed
  refine ⟨[seed], by simp [iidBirthShortBlockLength], ?_⟩
  have hsafe := iidBirthSingletonKernel_isSafe ring
    (localStep ring P_partialSealIidBirth C seed) hkernel
  have hrun :
      runLocalSchedule ring P_partialSealIidBirth C [seed] =
        localStep ring P_partialSealIidBirth C seed := by
    rfl
  have hsafeEq := congrArg
    (fun X : IidBirthConfig 1 psi kappa tau =>
      PopulationProtocol.IsSafe
        (P_partialSealIidBirthProtocol psi kappa tau) ring X
        isLeaderOutput)
    hrun
  exact Eq.mpr hsafeEq hsafe

/-- Uniform shortened landing from every authorized zero-leader start. -/
theorem iidBirthZeroStart_reaches_isSafe_short
    (ring : DirectedRing n)
    (C : IidBirthConfig n psi kappa tau)
    (hC : IidBirthZeroStart C) :
    ∃ word : DetSchedule n,
      word.length ≤ iidBirthShortBlockLength n ∧
      PopulationProtocol.IsSafe
        (P_partialSealIidBirthProtocol psi kappa tau) ring
        (runLocalSchedule ring P_partialSealIidBirth C word)
        isLeaderOutput := by
  by_cases hn : n = 1
  · subst n
    exact iidBirthZeroStart_reaches_isSafe_short_singleton ring C hC
  · have hnTwo : 1 < n := by
      have hnPos := ring.hn
      omega
    exact iidBirthZeroStart_reaches_isSafe_short_nontrivial
      ring hnTwo C hC

/-! ## Closed-domain producer and exact iid consequences -/

/-- R93 tightens the common favorable-word producer from `n²+4n` to
`floor(n/2)*n+4n-3`. -/
theorem iidBirthDomain_boundedSafeProducer_short
    (ring : DirectedRing n) :
    BoundedSafeScheduleProducer ring P_partialSealIidBirth
      (IidBirthDomain (psi := psi) (kappa := kappa) (tau := tau))
      (fun C => PopulationProtocol.IsSafe
        (P_partialSealIidBirthProtocol psi kappa tau) ring C
        isLeaderOutput)
      (iidBirthShortBlockLength n) := by
  intro C hC _
  rcases hC with hzero | hpositive | hsingleton
  · exact iidBirthZeroStart_reaches_isSafe_short ring C hzero
  · by_cases hn : n = 1
    · have hall : IidBirthAllCommitted C := by
        obtain ⟨root, hroot⟩ := hpositive.2.2.2
        intro i
        have hir : i = root := by
          apply Fin.ext
          have hi := i.isLt
          have hr := root.isLt
          omega
        simpa [hir] using hroot
      have hkernel : IidBirthSingletonKernel C :=
        ⟨hn, hall, hpositive.2.2.1⟩
      refine ⟨[], by simp, ?_⟩
      simpa only [runLocalSchedule] using
        (iidBirthSingletonKernel_isSafe ring C hkernel)
    · have hnTwo : 1 < n := by
        have hnPos := ring.hn
        omega
      obtain ⟨word, hlength, hsafe⟩ :=
        iidBirthPositive_reaches_isSafe_short ring hnTwo C hpositive
      refine ⟨word, ?_, hsafe⟩
      rw [iidBirthShortBlockLength_decomposition ring]
      omega
  · refine ⟨[], by simp, ?_⟩
    simpa only [runLocalSchedule] using
      (iidBirthSingletonKernel_isSafe ring C hsingleton)

/-- Exact repeated-block iid count on the same closed repair domain, now at
the shorter common block. -/
theorem iidBirthDomain_repeatedBlockSSLEOn_short
    (ring : DirectedRing n) :
    ∀ blocks,
      UniformFiniteHorizonSSLEOn
        (P_partialSealIidBirthProtocol psi kappa tau) ring
        isLeaderOutput
        (IidBirthDomain (psi := psi) (kappa := kappa) (tau := tau))
        (blocks * iidBirthShortBlockLength n)
        ((n ^ iidBirthShortBlockLength n - 1) ^ blocks) := by
  exact boundedIsSafeProducer_repeatedBlockSSLEOn
    (P_partialSealIidBirthProtocol psi kappa tau) ring
    isLeaderOutput
    (IidBirthDomain (psi := psi) (kappa := kappa) (tau := tau))
    (iidBirthIsSafeTest ring)
    (iidBirthIsSafeTest_spec ring)
    (iidBirthDomain_localStepClosed ring)
    (iidBirthShortBlockLength n)
    (iidBirthDomain_boundedSafeProducer_short ring)

/-- Explicit finite WHP theorem at the shorter block.  With
`blocks=(n-1)(n^L-1)+1`, the exact uniform iid failure fraction is at most
`1/n`. -/
theorem iidBirthDomain_explicitOneOverNSSLEOn_short
    (ring : DirectedRing n) (hn : 1 < n) :
    let L := iidBirthShortBlockLength n
    let blocks := (n - 1) * (n ^ L - 1) + 1
    UniformOneOverNFailureAtHorizonOn
      (P_partialSealIidBirthProtocol psi kappa tau) ring
      isLeaderOutput
      (IidBirthDomain (psi := psi) (kappa := kappa) (tau := tau))
      1 (blocks * L) := by
  dsimp only
  have hL : 0 < iidBirthShortBlockLength n := by
    dsimp [iidBirthShortBlockLength]
    omega
  exact boundedIsSafeProducer_explicitOneOverNSSLEOn
    (P_partialSealIidBirthProtocol psi kappa tau) ring
    isLeaderOutput
    (IidBirthDomain (psi := psi) (kappa := kappa) (tau := tau))
    (iidBirthIsSafeTest ring)
    (iidBirthIsSafeTest_spec ring)
    (iidBirthDomain_localStepClosed ring)
    hn (iidBirthShortBlockLength n) hL
    (iidBirthDomain_boundedSafeProducer_short ring)

/-! ## Exact carrier factor -/

/-- Definitional carrier identity certifying the exact factor two over R91.
The repository deliberately has no `Fintype` dependency, so the comparison is
stated as the stronger type identity from which every finite-cardinality
interpretation immediately obtains multiplication by `|Bool|=2`. -/
theorem iidBirthState_exact_factor_two :
    IidBirthState psi kappa tau =
      (SealSweepState psi kappa tau × Bool) := by
  rfl

/-- Relative to the physical expiring carrier there are exactly three Boolean
products: the accepted lock, the R91 seal, and the birth barrier.  Thus every
finite-cardinality interpretation has exact factor `2³=8`. -/
theorem iidBirthState_exact_factor_eight :
    IidBirthState psi kappa tau =
      (((ExpiringAgentState psi kappa tau × Bool) × Bool) × Bool) := by
  rfl

end PPartialSealSweepIidBirthComplexitySol
end PPLLCompleteMultiLeaderCleanup
