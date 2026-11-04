import Leader.Wu.Seal.BirthBarrierShortBlocks

/-!
# Hostile audit consumers for the iid birth-barrier repair

This module checks the two semantic boundaries that the headline theorems do
not themselves expose.

* At `psi = 0`, the physical carrier contains a `Fin 0` label.  On every
  nonempty ring the entire configuration type is therefore empty, so any
  theorem universally quantified over configurations is vacuous on that
  parameter branch.
* At `0 < psi`, an explicit bounded physical state supplies a concrete
  zero-start configuration.  The final consumer instantiates the shortened
  domain theorem at that configuration and states the resulting pointwise
  failure count as `n * failures <= total`, with every protocol parameter
  explicit.

The module also replaces the syntactic carrier identity with a duplicate-free
exhaustive certificate, making the factors two and eight genuine finite-state
cardinality statements.
-/

namespace PPLLCompleteMultiLeaderCleanup
namespace PPartialSealSweepIidBirthHostileAudit

open PPLL PPLLResearchFormulation PPLLTraceConvergence
open PPLLExpiringComparisonRepair PPLLSchedulerBlocks
open PPLLClosedDomainSchedulerAmplificationSol
open PPartialMinimalLockRepairSol
open PPartialDynamicSweepLockSol
open PPartialDynamicSweepResetSol
open PPartialSealSweepOverlaySol
open PPartialSealSweepIidBirthRepairSol
open PPartialSealSweepIidBirthComplexitySol

set_option autoImplicit false

/-! ## The exact vacuous parameter branch -/

/-- On a nonempty ring there is no iid-birth configuration at `psi = 0`,
because every local physical state would contain an inhabitant of `Fin 0` as
its bounded label. -/
theorem iidBirthConfig_not_nonempty_at_zeroPsi
    (n kappa tau : Nat) (ring : DirectedRing n) :
    ¬ Nonempty (IidBirthConfig n 0 kappa tau) := by
  rintro ⟨C⟩
  let i : Fin n := ⟨0, ring.hn⟩
  exact Fin.elim0 ((C i).1.1.1.core.core.label)

/-! ## A concrete producer for every nonempty physical label type -/

/-- A completely explicit bounded physical follower.  Positivity of `psi` is
the only premise needed to fill the label field; every other bounded numeric
field has a canonical zero inhabitant. -/
def auditBoundedFollower
    (psi kappa : Nat) (hpsi : 0 < psi) :
    BoundedAgentState psi kappa where
  leader := false
  probe := false
  phase := false
  bit := false
  wait := false
  state := .none
  path := .bot
  reset := false
  carry := false
  count := ⟨0, Nat.succ_pos kappa⟩
  label := ⟨0, hpsi⟩
  h_field := false
  path2 := none
  path3 := none
  path4 := none
  path5 := none
  p := false
  p_carry := false
  reset_cmd := false
  echo := false
  signal_B := 0
  bullet := 0
  shield := false
  write_state := .none
  write := .none
  last := false
  last_set := false
  last_unset := false
  b_carry := false
  gen_ws := false
  ws_echo := false
  signal_ws := false

/-- Explicit inhabitant of the accepted physical-plus-lock carrier. -/
def auditMinimalLockFollower
    (psi kappa tau : Nat) (hpsi : 0 < psi) :
    MinimalLockState psi kappa tau :=
  (⟨⟨auditBoundedFollower psi kappa hpsi, false⟩,
      freshStall tau⟩,
    false)

/-- Concrete all-armed, all-closed, leaderless initialization. -/
def auditIidBirthZeroStart
    (n psi kappa tau : Nat) (hpsi : 0 < psi) :
    IidBirthConfig n psi kappa tau :=
  iidBirthUniformZeroStart
    (auditMinimalLockFollower psi kappa tau hpsi)

theorem auditIidBirthZeroStart_mem
    (n psi kappa tau : Nat) (hpsi : 0 < psi) :
    IidBirthZeroStart
      (auditIidBirthZeroStart n psi kappa tau hpsi) := by
  exact iidBirthUniformZeroStart_mem
    (auditMinimalLockFollower psi kappa tau hpsi)

theorem auditIidBirthZeroStart_domain
    (n psi kappa tau : Nat) (hpsi : 0 < psi) :
    IidBirthDomain
      (auditIidBirthZeroStart n psi kappa tau hpsi) := by
  exact Or.inl (auditIidBirthZeroStart_mem n psi kappa tau hpsi)

/-- The concrete start stays inside the advertised restart domain after every
finite exact schedule.  This consumes the local-step closure theorem at a real
witness rather than merely restating the closure predicate. -/
theorem auditIidBirthZeroStart_run_domain
    (n psi kappa tau : Nat)
    (ring : DirectedRing n) (hpsi : 0 < psi)
    (word : DetSchedule n) :
    IidBirthDomain
      (runLocalSchedule ring P_partialSealIidBirth
        (auditIidBirthZeroStart n psi kappa tau hpsi) word) := by
  exact localStepClosed_runLocalSchedule
    ring P_partialSealIidBirth IidBirthDomain
    (iidBirthDomain_localStepClosed ring)
    (auditIidBirthZeroStart_domain n psi kappa tau hpsi) word

/-! ## Singleton and concurrent-birth consumers -/

/-- The self-edge convention keeps the initiator output, so one birth from the
concrete singleton zero-start reaches semantic safety immediately. -/
theorem auditIidBirthZeroStart_singleton_step_isSafe
    (psi kappa tau : Nat) (hpsi : 0 < psi)
    (ring : DirectedRing 1) :
    PopulationProtocol.IsSafe
      (P_partialSealIidBirthProtocol psi kappa tau) ring
      (localStep ring P_partialSealIidBirth
        (auditIidBirthZeroStart 1 psi kappa tau hpsi) (0 : Fin 1))
      isLeaderOutput := by
  have hkernel := iidBirthZeroStart_localStep_singleton
    ring (auditIidBirthZeroStart 1 psi kappa tau hpsi)
    (auditIidBirthZeroStart_mem 1 psi kappa tau hpsi) (0 : Fin 1)
  exact iidBirthSingletonKernel_isSafe ring _ hkernel

/-- Two disjoint births from the concrete four-agent start remain in the
balanced positive branch, so concurrency is consumed at an inhabited state. -/
theorem auditIidBirthZeroStart_twoDisjoint_positive
    (psi kappa tau : Nat) (hpsi : 0 < psi) :
    IidBirthPositive
      (runLocalSchedule iidBirthLocalityRingFour P_partialSealIidBirth
        (auditIidBirthZeroStart 4 psi kappa tau hpsi)
        [(0 : Fin 4), (2 : Fin 4)]) := by
  exact iidBirth_twoDisjointPrefix_remains_positive
    (auditIidBirthZeroStart 4 psi kappa tau hpsi)
    (auditIidBirthZeroStart_mem 4 psi kappa tau hpsi)

/-! ## Genuine finite-state factor certificates -/

/-- Duplicate-free exhaustive certificate for the added barrier bit. -/
def auditIidBirthStateCertificate
    (psi kappa tau : Nat) :
    ExhaustiveList (IidBirthState psi kappa tau) :=
  ExhaustiveList.prod
    (sealSweepStateCertificate psi kappa tau)
    ExhaustiveList.bool

theorem auditIidBirthStateCertificate_values_nodup
    (psi kappa tau : Nat) :
    (auditIidBirthStateCertificate psi kappa tau).values.Nodup := by
  unfold auditIidBirthStateCertificate
  apply ExhaustiveList.values_nodup_prod
  · change (sweepLockStateCertificate psi kappa tau).values.Nodup
    unfold sweepLockStateCertificate
    apply ExhaustiveList.values_nodup_prod
    · unfold minimalLockStateCertificate P_partialStateCertificate
      change
        (ExhaustiveList.prod (expiringAgentState psi kappa tau)
          ExhaustiveList.bool).values.Nodup
      apply ExhaustiveList.values_nodup_prod
      · exact expiringAgentState_values_nodup psi kappa tau
      · exact ExhaustiveList.values_nodup_bool
    · exact ExhaustiveList.values_nodup_bool
  · exact ExhaustiveList.values_nodup_bool

/-- The new carrier has exactly twice the duplicate-free enumeration length
of the unchanged seal-sweep carrier. -/
theorem auditIidBirthStateCertificate_exact_factor_two
    (psi kappa tau : Nat) :
    (auditIidBirthStateCertificate psi kappa tau).values.length =
      (sealSweepStateCertificate psi kappa tau).values.length * 2 := by
  unfold auditIidBirthStateCertificate
  rw [ExhaustiveList.values_length_prod,
    ExhaustiveList.values_length_bool]

/-- Relative to the physical expiring carrier, the three Boolean products give
the genuine duplicate-free enumeration factor `2^3 = 8`. -/
theorem auditIidBirthStateCertificate_exact_factor_eight
    (psi kappa tau : Nat) :
    (auditIidBirthStateCertificate psi kappa tau).values.length =
      ((2 * (PPLLFinite.boundedAgentState psi kappa).values.length) *
        (tau + 1)) * 8 := by
  rw [auditIidBirthStateCertificate_exact_factor_two,
    sealSweepStateCertificate_values_length]
  omega

/-! ## Pointwise `1/n` consumer from the concrete zero start -/

/-- Fully instantiated shortened iid theorem.  The last conjunct is the exact
finite-count form of failure probability at most `1/n`: multiplying the number
of failing schedules by `n` is bounded by the total number of schedules.

Unlike the domain-level headline, this theorem supplies an explicit initial
configuration for every `0 < psi` and consumes its domain-membership proof. -/
theorem auditIidBirthZeroStart_explicit_oneOverN_short
    (n psi kappa tau : Nat)
    (ring : DirectedRing n) (hn : 1 < n) (hpsi : 0 < psi) :
    let L := iidBirthShortBlockLength n
    let blocks := (n - 1) * (n ^ L - 1) + 1
    let horizon := blocks * L
    let C := auditIidBirthZeroStart n psi kappa tau hpsi
    IidBirthDomain C ∧
      0 < horizon ∧
      n ^ (horizon - 1) < (allSchedules n horizon).length ∧
      n * ((allSchedules n horizon).length -
        stabilizingScheduleCount
          (P_partialSealIidBirthProtocol psi kappa tau) ring
          isLeaderOutput C horizon) ≤
        (allSchedules n horizon).length := by
  dsimp only
  let C := auditIidBirthZeroStart n psi kappa tau hpsi
  let L := iidBirthShortBlockLength n
  let blocks := (n - 1) * (n ^ L - 1) + 1
  let horizon := blocks * L
  have hdomain : IidBirthDomain C :=
    auditIidBirthZeroStart_domain n psi kappa tau hpsi
  have hheadline :=
    iidBirthDomain_explicitOneOverNSSLEOn_short
      (psi := psi) (kappa := kappa) (tau := tau) ring hn
  change 1 < n ∧ 0 < horizon ∧
      UniformFiniteHorizonSSLEOn
        (P_partialSealIidBirthProtocol psi kappa tau) ring
        isLeaderOutput IidBirthDomain horizon
        (1 * n ^ (horizon - 1)) at hheadline
  have hcount := hheadline.2.2 C hdomain
  have hfail :
      (allSchedules n horizon).length -
          stabilizingScheduleCount
            (P_partialSealIidBirthProtocol psi kappa tau) ring
            isLeaderOutput C horizon ≤
        n ^ (horizon - 1) := by
    omega
  have hbudgetStrict :
      n ^ (horizon - 1) < (allSchedules n horizon).length := by
    simpa using oneOverNFailure_budget_lt_total
      ring 1 horizon hheadline.1 hheadline.2.1
  have hfactor :
      n * n ^ (horizon - 1) = (allSchedules n horizon).length := by
    rw [allSchedules_length]
    calc
      n * n ^ (horizon - 1) = n ^ (horizon - 1) * n :=
        Nat.mul_comm _ _
      _ = n ^ ((horizon - 1) + 1) := by rw [Nat.pow_succ]
      _ = n ^ horizon := by congr 1; omega
  refine ⟨hdomain, hheadline.2.1, hbudgetStrict, ?_⟩
  have hscaled := Nat.mul_le_mul_left n hfail
  simpa only [hfactor] using hscaled

#print axioms iidBirthConfig_not_nonempty_at_zeroPsi
#print axioms auditIidBirthZeroStart_run_domain
#print axioms auditIidBirthZeroStart_singleton_step_isSafe
#print axioms auditIidBirthZeroStart_twoDisjoint_positive
#print axioms auditIidBirthStateCertificate_values_nodup
#print axioms auditIidBirthStateCertificate_exact_factor_eight
#print axioms auditIidBirthZeroStart_explicit_oneOverN_short

end PPartialSealSweepIidBirthHostileAudit
end PPLLCompleteMultiLeaderCleanup
