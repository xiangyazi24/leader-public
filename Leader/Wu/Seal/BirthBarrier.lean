import Leader.Wu.Seal.MixedNormalizer

/-!
# One-bit initialization barrier for iid seal-sweep convergence

The retiring birth rule cannot be restarted after an unlucky prefix: two
disjoint births on four agents can retire the whole ring with two leaders.
This module keeps the accepted seal-sweep transition after initialization and
adds exactly one outer Boolean.  `true` means that the site has not yet crossed
the initialization barrier; `false` means committed to the seal overlay.

Two uncommitted closed followers may create an open leader/ probe pair.  This
is deliberately the balanced `B,D` token pair used by the mixed-state proof,
not an all-retired terminal pair.  A committed initiator commits an
uncommitted responder without changing its physical or seal state.  Two
committed endpoints execute the exact R91 seal overlay.  Consequently
concurrent births are harmless: each adds one open leader and one open
follower, while all other enabled inner steps are exact overlay steps.

Strictly allowing only one birth is impossible for an endpoint-local
deterministic rule on a uniform ring of size at least four: after a birth on
edge zero, the disjoint edge two still sees the original pair.  The repair
therefore serializes *commitment*, not birth itself.  Once every site is
committed, the transition is definitionally the R91 overlay and the proved
mixed-state normalizer applies.
-/

namespace PPLLCompleteMultiLeaderCleanup
namespace PPartialSealSweepIidBirthRepairSol

open PPLL PPLLResearchFormulation PPLLTraceConvergence
open PPLLSchedulerBlocks PPLLClosedDomainSchedulerAmplificationSol
open PPLLNoCheckBirthConditionTwoGeometry
open PPartialMinimalLockRepairSol
open PPartialDynamicSweepLockSol
open PPartialDynamicSweepResetSol
open PPartialSealSweepOverlaySol
open PPartialSealSweepPositiveLandingSol
open PPartialSealSweepUniformSchedulerSol
open PPartialSealSweepMixedNormalizerSol

set_option autoImplicit false

variable {n psi kappa tau : Nat}

/-! ## Exact factor-two carrier and transition -/

/-- The sole new resource is the initialization-barrier bit. -/
abbrev IidBirthState (psi kappa tau : Nat) :=
  SealSweepState psi kappa tau × Bool

abbrev IidBirthConfig (n psi kappa tau : Nat) :=
  Fin n → IidBirthState psi kappa tau

/-- Forget only the new initialization bit. -/
def iidBirthErase
    (C : IidBirthConfig n psi kappa tau) :
    SealSweepConfig n psi kappa tau :=
  fun i => (C i).1

/-- Embed an R91 configuration wholly behind the barrier. -/
def iidBirthCommit
    (C : SealSweepConfig n psi kappa tau) :
    IidBirthConfig n psi kappa tau :=
  fun i => (C i, false)

@[simp] theorem iidBirthErase_commit
    (C : SealSweepConfig n psi kappa tau) :
    iidBirthErase (iidBirthCommit C) = C := by
  rfl

/-- Set the physical leader bit and open the existing seal. -/
def setIidBirthLeader
    (u : MinimalLockState psi kappa tau) :
    MinimalLockState psi kappa tau :=
  ({ u.1 with core :=
      { u.1.core with core :=
        { u.1.core.core with leader := true } } }, u.2)

@[simp] theorem setIidBirthLeader_leader
    (u : MinimalLockState psi kappa tau) :
    minimalLockLeader (setIidBirthLeader u) = true := by
  rfl

@[simp] theorem sweepLockLeader_setIidBirthLeader_closed
    (u : MinimalLockState psi kappa tau) :
    sweepLockLeader (setIidBirthLeader u, true) = true := by
  exact setIidBirthLeader_leader u

/-- Set the physical leader bit and open the existing seal. -/
def iidBirthOpenLeader
    (u : SealSweepState psi kappa tau) : SealSweepState psi kappa tau :=
  (setIidBirthLeader u.1, false)

/-- Preserve the physical follower and open the existing seal. -/
def iidBirthOpenFollower
    (u : SealSweepState psi kappa tau) : SealSweepState psi kappa tau :=
  (u.1, false)

@[simp] theorem iidBirthOpenLeader_leader
    (u : SealSweepState psi kappa tau) :
    sweepLockLeader (iidBirthOpenLeader u) = true := by
  rfl

@[simp] theorem iidBirthOpenLeader_open
    (u : SealSweepState psi kappa tau) :
    (iidBirthOpenLeader u).2 = false := by
  rfl

@[simp] theorem iidBirthOpenFollower_leader
    (u : SealSweepState psi kappa tau) :
    sweepLockLeader (iidBirthOpenFollower u) = sweepLockLeader u := by
  rfl

@[simp] theorem iidBirthOpenFollower_open
    (u : SealSweepState psi kappa tau) :
    (iidBirthOpenFollower u).2 = false := by
  rfl

/-- One-bit birth barrier.

* two committed endpoints execute exactly `P_partialSealSweep`;
* a committed initiator commits an uncommitted responder;
* the reverse orientation is inert;
* two uncommitted closed followers create one balanced open token pair.

The final guard matters only outside the intended domain.  In-domain every
uncommitted site is a closed follower. -/
def P_partialSealIidBirth
    (l r : IidBirthState psi kappa tau) :
    IidBirthState psi kappa tau × IidBirthState psi kappa tau :=
  if hl : l.2 = false then
    if hr : r.2 = false then
      let q := P_partialSealSweep l.1 r.1
      ((q.1, false), (q.2, false))
    else
      (l, (r.1, false))
  else if hr : r.2 = false then
    (l, r)
  else if sweepLockLeader l.1 = false ∧ l.1.2 = true ∧
      sweepLockLeader r.1 = false ∧ r.1.2 = true then
    ((iidBirthOpenLeader l.1, false),
      (iidBirthOpenFollower r.1, false))
  else
    (l, r)

/-- Packaged factor-two repair.  The new bit is observationally silent. -/
def P_partialSealIidBirthProtocol
    (psi kappa tau : Nat) : PopulationProtocol where
  Q := IidBirthState psi kappa tau
  Y := LeaderOutput
  transition := P_partialSealIidBirth
  output := fun s =>
    if sweepLockLeader s.1 then LeaderOutput.leader
    else LeaderOutput.follower

theorem P_partialSealIidBirth_committed
    (l r : IidBirthState psi kappa tau)
    (hl : l.2 = false) (hr : r.2 = false) :
    P_partialSealIidBirth l r =
      (((P_partialSealSweep l.1 r.1).1, false),
        ((P_partialSealSweep l.1 r.1).2, false)) := by
  simp [P_partialSealIidBirth, hl, hr]

theorem P_partialSealIidBirth_propagate
    (l r : IidBirthState psi kappa tau)
    (hl : l.2 = false) (hr : r.2 = true) :
    P_partialSealIidBirth l r = (l, (r.1, false)) := by
  simp [P_partialSealIidBirth, hl, hr]

theorem P_partialSealIidBirth_reverse_inert
    (l r : IidBirthState psi kappa tau)
    (hl : l.2 = true) (hr : r.2 = false) :
    P_partialSealIidBirth l r = (l, r) := by
  simp [P_partialSealIidBirth, hl, hr]

theorem P_partialSealIidBirth_birth
    (l r : IidBirthState psi kappa tau)
    (hlb : l.2 = true) (hrb : r.2 = true)
    (hl : sweepLockLeader l.1 = false) (hlc : l.1.2 = true)
    (hr : sweepLockLeader r.1 = false) (hrc : r.1.2 = true) :
    P_partialSealIidBirth l r =
      ((iidBirthOpenLeader l.1, false),
        (iidBirthOpenFollower r.1, false)) := by
  simp [P_partialSealIidBirth, hlb, hrb, hl, hlc, hr, hrc]

/-- Physical bounded-domain closure is inherited from the unchanged inner
carrier and the already verified leader setters. -/
theorem P_partialSealIidBirth_output_inProtocolDomain
    (l r : IidBirthState psi kappa tau) :
    let q := P_partialSealIidBirth l r
    q.1.1.1.1.core.erase.core.inProtocolDomain kappa ∧
      q.2.1.1.1.core.erase.core.inProtocolDomain kappa := by
  let q := P_partialSealIidBirth l r
  exact ⟨q.1.1.1.1.core.core.erase_inProtocolDomain,
    q.2.1.1.1.core.core.erase_inProtocolDomain⟩

/-! ## Barrier predicates and exact committed simulation -/

/-- Every site has crossed the initialization barrier. -/
def IidBirthAllCommitted
    (C : IidBirthConfig n psi kappa tau) : Prop :=
  ∀ i : Fin n, (C i).2 = false

/-- Every still-uncommitted site retains the authorized initialization
shape: a closed follower. -/
def IidBirthArmedClean
    (C : IidBirthConfig n psi kappa tau) : Prop :=
  ∀ i : Fin n, (C i).2 = true →
    sweepLockLeader (C i).1 = false ∧ (C i).1.2 = true

/-- The exact all-closed zero-leader initialization class. -/
def IidBirthZeroStart
    (C : IidBirthConfig n psi kappa tau) : Prop :=
  (∀ i : Fin n, (C i).2 = true) ∧
    SealSweepAllClosed (iidBirthErase C) ∧
    ¬ SealSweepHasLeader (iidBirthErase C)

/-- Live post-birth states carry R91's two primitive invariants and at least
one committed site from which the barrier can spread. -/
def IidBirthPositive
    (C : IidBirthConfig n psi kappa tau) : Prop :=
  IidBirthArmedClean C ∧
    SealSweepOpenBalanced (iidBirthErase C) ∧
    SealSweepHasLeader (iidBirthErase C) ∧
    ∃ i : Fin n, (C i).2 = false

/-- The self-edge birth on the one-agent ring keeps only the initiator output.
It is already a committed unique-leader kernel, but its inner open-token
balance is intentionally not the two-site `B,D` balance. -/
def IidBirthSingletonKernel
    (C : IidBirthConfig n psi kappa tau) : Prop :=
  n = 1 ∧ IidBirthAllCommitted C ∧
    SealSweepHasLeader (iidBirthErase C)

/-- Closed initialization/restart domain used by exact iid amplification. -/
def IidBirthDomain
    (C : IidBirthConfig n psi kappa tau) : Prop :=
  IidBirthZeroStart C ∨ IidBirthPositive C ∨
    IidBirthSingletonKernel C

/-- A concrete constructor for the authorized zero-start class from any
physical carrier state.  It clears the observable leader, closes the R91 seal,
and arms the new initialization bit everywhere. -/
def iidBirthUniformZeroStart
    (u : MinimalLockState psi kappa tau) :
    IidBirthConfig n psi kappa tau :=
  fun _ => ((clearMinimalLockLeader u, true), true)

theorem iidBirthUniformZeroStart_mem
    (u : MinimalLockState psi kappa tau) :
    IidBirthZeroStart (n := n) (iidBirthUniformZeroStart u) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i
    rfl
  · intro i
    rfl
  · rintro ⟨i, hi⟩
    change false = true at hi
    contradiction

theorem iidBirthUniformZeroStart_domain
    (u : MinimalLockState psi kappa tau) :
    IidBirthDomain (n := n) (iidBirthUniformZeroStart u) :=
  Or.inl (iidBirthUniformZeroStart_mem u)

theorem iidBirthAllCommitted_eq_commit_erase
    (C : IidBirthConfig n psi kappa tau)
    (hC : IidBirthAllCommitted C) :
    C = iidBirthCommit (iidBirthErase C) := by
  funext i
  apply Prod.ext
  · rfl
  · exact hC i

private theorem sealSweepOpenLeaderCount_eq_of_signature
    (A B : SealSweepConfig n psi kappa tau)
    (h : ∀ i : Fin n,
      (sweepLockLeader (A i) && !(A i).2) =
        (sweepLockLeader (B i) && !(B i).2)) :
    sealSweepOpenLeaderCount A = sealSweepOpenLeaderCount B := by
  unfold sealSweepOpenLeaderCount
  congr 1
  funext i
  change (if sweepLockLeader (A i) && !(A i).2 then 1 else 0) =
    if sweepLockLeader (B i) && !(B i).2 then 1 else 0
  rw [h i]

private theorem sealSweepOpenFollowerCount_eq_of_signature
    (A B : SealSweepConfig n psi kappa tau)
    (h : ∀ i : Fin n,
      (!sweepLockLeader (A i) && !(A i).2) =
        (!sweepLockLeader (B i) && !(B i).2)) :
    sealSweepOpenFollowerCount A = sealSweepOpenFollowerCount B := by
  unfold sealSweepOpenFollowerCount
  congr 1
  funext i
  change (if !sweepLockLeader (A i) && !(A i).2 then 1 else 0) =
    if !sweepLockLeader (B i) && !(B i).2 then 1 else 0
  rw [h i]

/-- Promote one closed follower to a closed leader without changing either
open-token count.  This auxiliary configuration lets a birth be viewed as an
ordinary R91 launch. -/
def iidBirthPromoteClosed
    (C : IidBirthConfig n psi kappa tau) (e : Fin n) :
    SealSweepConfig n psi kappa tau :=
  fun i => if i = e then
    (setIidBirthLeader (C e).1.1, true)
  else (C i).1

private theorem promoteClosed_balanced
    (C : IidBirthConfig n psi kappa tau) (e : Fin n)
    (heClosed : (C e).1.2 = true)
    (hbalanced : SealSweepOpenBalanced (iidBirthErase C)) :
    SealSweepOpenBalanced (iidBirthPromoteClosed C e) := by
  have hleaders : sealSweepOpenLeaderCount (iidBirthPromoteClosed C e) =
      sealSweepOpenLeaderCount (iidBirthErase C) := by
    apply sealSweepOpenLeaderCount_eq_of_signature
    intro i
    by_cases hi : i = e
    · subst i
      simp [iidBirthPromoteClosed, iidBirthErase, heClosed]
    · simp [iidBirthPromoteClosed, iidBirthErase, hi]
  have hfollowers : sealSweepOpenFollowerCount (iidBirthPromoteClosed C e) =
      sealSweepOpenFollowerCount (iidBirthErase C) := by
    apply sealSweepOpenFollowerCount_eq_of_signature
    intro i
    by_cases hi : i = e
    · subst i
      simp [iidBirthPromoteClosed, iidBirthErase, heClosed]
    · simp [iidBirthPromoteClosed, iidBirthErase, hi]
  unfold SealSweepOpenBalanced at *
  rw [hleaders, hfollowers]
  exact hbalanced

private theorem promoteClosed_hasLeader
    (C : IidBirthConfig n psi kappa tau) (e : Fin n) :
    SealSweepHasLeader (iidBirthPromoteClosed C e) := by
  refine ⟨e, ?_⟩
  simp [iidBirthPromoteClosed]

theorem iidBirthErase_localStep_committed
    (ring : DirectedRing n)
    (C : IidBirthConfig n psi kappa tau) (e : Fin n)
    (he : (C e).2 = false)
    (hj : (C (ring.rightNeighbor e)).2 = false) :
    iidBirthErase (localStep ring P_partialSealIidBirth C e) =
      localStep ring P_partialSealSweep (iidBirthErase C) e := by
  let j := ring.rightNeighbor e
  have hpair := P_partialSealIidBirth_committed
    (C e) (C j) he (by simpa [j] using hj)
  funext i
  by_cases hie : i = e
  · subst i
    simp [iidBirthErase, localStep, j, hpair]
  · by_cases hij : i = j
    · subst i
      simp [iidBirthErase, localStep, j, hie, hpair]
    · simp [iidBirthErase, localStep, j, hie, hij, hpair]

theorem iidBirthErase_localStep_propagate
    (ring : DirectedRing n)
    (C : IidBirthConfig n psi kappa tau) (e : Fin n)
    (he : (C e).2 = false)
    (hj : (C (ring.rightNeighbor e)).2 = true) :
    iidBirthErase (localStep ring P_partialSealIidBirth C e) =
      iidBirthErase C := by
  let j := ring.rightNeighbor e
  have hpair := P_partialSealIidBirth_propagate
    (C e) (C j) he (by simpa [j] using hj)
  funext i
  by_cases hie : i = e
  · subst i
    simp [iidBirthErase, localStep, j, hpair]
  · by_cases hij : i = j
    · subst i
      simp [iidBirthErase, localStep, j, hie, hpair]
    · simp [iidBirthErase, localStep, j, hie, hij, hpair]

theorem iidBirthErase_localStep_reverse_inert
    (ring : DirectedRing n)
    (C : IidBirthConfig n psi kappa tau) (e : Fin n)
    (he : (C e).2 = true)
    (hj : (C (ring.rightNeighbor e)).2 = false) :
    localStep ring P_partialSealIidBirth C e = C := by
  let j := ring.rightNeighbor e
  have hpair := P_partialSealIidBirth_reverse_inert
    (C e) (C j) he (by simpa [j] using hj)
  funext i
  by_cases hie : i = e
  · subst i
    simp [localStep, j, hpair]
  · by_cases hij : i = j
    · subst i
      simp [localStep, j, hie, hpair]
    · simp [localStep, j, hie, hij, hpair]

/-- A concurrent birth is exactly an R91 launch from the auxiliary promoted
configuration, hence preserves balance and leaves a leader. -/
theorem iidBirth_birth_inner_invariants
    (ring : DirectedRing n) (hn : 1 < n)
    (C : IidBirthConfig n psi kappa tau) (e : Fin n)
    (heBit : (C e).2 = true)
    (hjBit : (C (ring.rightNeighbor e)).2 = true)
    (heFollower : sweepLockLeader (C e).1 = false)
    (heClosed : (C e).1.2 = true)
    (hjFollower : sweepLockLeader (C (ring.rightNeighbor e)).1 = false)
    (hjClosed : (C (ring.rightNeighbor e)).1.2 = true)
    (hbalanced : SealSweepOpenBalanced (iidBirthErase C)) :
    let D := localStep ring P_partialSealIidBirth C e
    SealSweepOpenBalanced (iidBirthErase D) ∧
      SealSweepHasLeader (iidBirthErase D) := by
  let j := ring.rightNeighbor e
  have hje : j ≠ e := rightNeighbor_ne_self_of_one_lt ring hn e
  let A := iidBirthPromoteClosed C e
  have hAe : A e = (setIidBirthLeader (C e).1.1, true) := by
    simp [A, iidBirthPromoteClosed]
  have hAeLeader : sweepLockLeader (A e) = true := by
    rw [hAe]
    exact sweepLockLeader_setIidBirthLeader_closed _
  have hAeClosed : (A e).2 = true := by
    simp [A, iidBirthPromoteClosed]
  have hAj : A j = (C j).1 := by
    simp [A, iidBirthPromoteClosed, hje]
  have hAjFollower : sweepLockLeader (A j) = false := by
    rw [hAj]
    simpa [j] using hjFollower
  have hAjClosed : (A j).2 = true := by
    rw [hAj]
    simpa [j] using hjClosed
  have hbirth := P_partialSealIidBirth_birth
    (C e) (C j) heBit (by simpa [j] using hjBit)
      heFollower heClosed (by simpa [j] using hjFollower)
      (by simpa [j] using hjClosed)
  have hlaunch := P_partialSealSweep_launch
    (A e) (A j) hAeLeader hAeClosed hAjFollower hAjClosed
  let D := localStep ring P_partialSealIidBirth C e
  let B := localStep ring P_partialSealSweep A e
  have hDe : D e = (iidBirthOpenLeader (C e).1, false) := by
    simp only [D, localStep, if_pos]
    rw [hbirth]
  have hDj : D j = (iidBirthOpenFollower (C j).1, false) := by
    simp [D, localStep, j, hje, hbirth]
  have hBe : B e = iidBirthOpenLeader (C e).1 := by
    simp only [B, localStep, if_pos]
    rw [hlaunch, hAe]
    rfl
  have hBj : B j = iidBirthOpenFollower (C j).1 := by
    simp [B, localStep, j, hje, hlaunch]
    exact congrArg iidBirthOpenFollower hAj
  have herase : iidBirthErase D = B := by
    funext i
    by_cases hie : i = e
    · subst i
      rw [iidBirthErase, hDe, hBe]
    · by_cases hij : i = j
      · subst i
        rw [iidBirthErase, hDj, hBj]
      · have hAi : A i = (C i).1 := by
          simp [A, iidBirthPromoteClosed, hie]
        simp [D, B, iidBirthErase, localStep, j, hie, hij, hAi]
  have hAbalanced : SealSweepOpenBalanced A :=
    promoteClosed_balanced C e heClosed hbalanced
  have hAleader : SealSweepHasLeader A := promoteClosed_hasLeader C e
  have hBbalanced := sealSweepOpenBalanced_localStep ring A hAbalanced e
  have hBleader := sealSweepHasLeader_localStep ring A hAbalanced hAleader e
  dsimp only
  rw [herase]
  exact ⟨hBbalanced, hBleader⟩

/-! ## Step closure of the live initialization domain -/

theorem iidBirthArmedClean_localStep
    (ring : DirectedRing n)
    (C : IidBirthConfig n psi kappa tau)
    (hclean : IidBirthArmedClean C) (e : Fin n) :
    IidBirthArmedClean
      (localStep ring P_partialSealIidBirth C e) := by
  let j := ring.rightNeighbor e
  let D := localStep ring P_partialSealIidBirth C e
  cases he : (C e).2 with
  | false =>
      cases hj : (C j).2 with
      | false =>
          have hpair := P_partialSealIidBirth_committed
            (C e) (C j) he hj
          intro i hi
          change (D i).2 = true at hi
          change sweepLockLeader (D i).1 = false ∧ (D i).1.2 = true
          by_cases hie : i = e
          · subst i
            simp [D, localStep, j, hpair] at hi
          · by_cases hij : i = j
            · subst i
              simp [D, localStep, j, hie, hpair] at hi
            · have hDi : D i = C i := by
                simp [D, localStep, j, hie, hij]
              rw [hDi] at hi ⊢
              exact hclean i hi
      | true =>
          have hpair := P_partialSealIidBirth_propagate
            (C e) (C j) he hj
          intro i hi
          change (D i).2 = true at hi
          change sweepLockLeader (D i).1 = false ∧ (D i).1.2 = true
          by_cases hie : i = e
          · subst i
            simp [D, localStep, j, hpair, he] at hi
          · by_cases hij : i = j
            · subst i
              simp [D, localStep, j, hie, hpair] at hi
            · have hDi : D i = C i := by
                simp [D, localStep, j, hie, hij]
              rw [hDi] at hi ⊢
              exact hclean i hi
  | true =>
      cases hj : (C j).2 with
      | false =>
          have hself := iidBirthErase_localStep_reverse_inert
            ring C e he (by simpa [j] using hj)
          rw [hself]
          exact hclean
      | true =>
          have hce := hclean e he
          have hcj := hclean j hj
          have hpair := P_partialSealIidBirth_birth
            (C e) (C j) he hj hce.1 hce.2 hcj.1 hcj.2
          intro i hi
          change (D i).2 = true at hi
          change sweepLockLeader (D i).1 = false ∧ (D i).1.2 = true
          by_cases hie : i = e
          · subst i
            simp [D, localStep, j, hpair] at hi
          · by_cases hij : i = j
            · subst i
              simp [D, localStep, j, hie, hpair] at hi
            · have hDi : D i = C i := by
                simp [D, localStep, j, hie, hij]
              rw [hDi] at hi ⊢
              exact hclean i hi

theorem iidBirthPositive_localStep
    (ring : DirectedRing n)
    (C : IidBirthConfig n psi kappa tau)
    (hC : IidBirthPositive C) (e : Fin n) :
    IidBirthPositive
      (localStep ring P_partialSealIidBirth C e) := by
  let j := ring.rightNeighbor e
  let D := localStep ring P_partialSealIidBirth C e
  have hcleanD := iidBirthArmedClean_localStep ring C hC.1 e
  cases he : (C e).2 with
  | false =>
      cases hj : (C j).2 with
      | false =>
          have herase := iidBirthErase_localStep_committed
            ring C e he (by simpa [j] using hj)
          have hbalancedD : SealSweepOpenBalanced (iidBirthErase D) := by
            rw [herase]
            exact sealSweepOpenBalanced_localStep ring
              (iidBirthErase C) hC.2.1 e
          have hleaderD : SealSweepHasLeader (iidBirthErase D) := by
            rw [herase]
            exact sealSweepHasLeader_localStep ring
              (iidBirthErase C) hC.2.1 hC.2.2.1 e
          refine ⟨hcleanD, hbalancedD, hleaderD, e, ?_⟩
          simp [D, localStep, j,
            P_partialSealIidBirth_committed (C e) (C j) he hj]
      | true =>
          have herase := iidBirthErase_localStep_propagate
            ring C e he (by simpa [j] using hj)
          refine ⟨hcleanD, ?_, ?_, e, ?_⟩
          · rw [herase]
            exact hC.2.1
          · rw [herase]
            exact hC.2.2.1
          · simp [D, localStep, j,
              P_partialSealIidBirth_propagate (C e) (C j) he hj, he]
  | true =>
      cases hj : (C j).2 with
      | false =>
          have hself := iidBirthErase_localStep_reverse_inert
            ring C e he (by simpa [j] using hj)
          rw [hself]
          exact hC
      | true =>
          obtain ⟨root, hrootFalse⟩ := hC.2.2.2
          have hn : 1 < n := by
            have hre : root ≠ e := by
              intro hre
              subst root
              rw [he] at hrootFalse
              exact Bool.noConfusion hrootFalse
            have hval : root.val ≠ e.val := by
              intro hval
              exact hre (Fin.ext hval)
            have hrlt := root.isLt
            have helt := e.isLt
            omega
          have hce := hC.1 e he
          have hcj := hC.1 j hj
          have hinv := iidBirth_birth_inner_invariants
            ring hn C e he (by simpa [j] using hj)
              hce.1 hce.2 (by simpa [j] using hcj.1)
              (by simpa [j] using hcj.2) hC.2.1
          change SealSweepOpenBalanced (iidBirthErase D) ∧
            SealSweepHasLeader (iidBirthErase D) at hinv
          refine ⟨hcleanD, hinv.1, hinv.2, e, ?_⟩
          have hpair := P_partialSealIidBirth_birth
            (C e) (C j) he hj hce.1 hce.2 hcj.1 hcj.2
          simp [D, localStep, j, hpair]

private theorem iidBirth_localStep_pair
    (ring : DirectedRing n) (C : IidBirthConfig n psi kappa tau)
    (e : Fin n) :
    let j := ring.rightNeighbor e
    let q := P_partialSealIidBirth (C e) (C j)
    let D := localStep ring P_partialSealIidBirth C e
    D e = q.1 ∧
      (j ≠ e → D j = q.2) ∧
      ∀ i : Fin n, i ≠ e → i ≠ j → D i = C i := by
  dsimp only
  refine ⟨by simp [localStep], ?_, ?_⟩
  · intro hne
    simp [localStep, hne]
  · intro i hie hij
    simp [localStep, hie, hij]

/-- From a committed initiator, both updated endpoints remain committed. -/
theorem iidBirth_localStep_commits_right
    (ring : DirectedRing n) (hn : 1 < n)
    (C : IidBirthConfig n psi kappa tau) (e : Fin n)
    (he : (C e).2 = false) :
    let D := localStep ring P_partialSealIidBirth C e
    (D e).2 = false ∧
      (D (ring.rightNeighbor e)).2 = false ∧
      ∀ i : Fin n, i ≠ e → i ≠ ring.rightNeighbor e → D i = C i := by
  let j := ring.rightNeighbor e
  have hje : j ≠ e := rightNeighbor_ne_self_of_one_lt ring hn e
  cases hj : (C j).2 with
  | false =>
      have hpair := P_partialSealIidBirth_committed
        (C e) (C j) he hj
      dsimp only
      refine ⟨?_, ?_, ?_⟩
      · simp [localStep, j, hpair]
      · simp [localStep, j, hpair, hje]
      · intro i hie hij
        simp [localStep, j, hpair, hie, hij]
  | true =>
      have hpair := P_partialSealIidBirth_propagate
        (C e) (C j) he hj
      dsimp only
      refine ⟨?_, ?_, ?_⟩
      · simp [localStep, j, hpair, he]
      · simp [localStep, j, hpair, hje]
      · intro i hie hij
        simp [localStep, j, hpair, hie, hij]

theorem iidBirthZeroStart_armedClean
    (C : IidBirthConfig n psi kappa tau)
    (hC : IidBirthZeroStart C) :
    IidBirthArmedClean C := by
  have hfollowers : ∀ i : Fin n,
      sweepLockLeader (C i).1 = false := by
    intro i
    cases hi : sweepLockLeader (C i).1 with
    | false => rfl
    | true =>
        exact False.elim (hC.2.2 ⟨i, by simpa [iidBirthErase] using hi⟩)
  intro i hi
  exact ⟨hfollowers i, hC.2.1 i⟩

/-- On every nontrivial ring, the very first interaction from the authorized
zero start enters the balanced-positive branch of the closed domain. -/
theorem iidBirthZeroStart_localStep_positive
    (ring : DirectedRing n) (hn : 1 < n)
    (C : IidBirthConfig n psi kappa tau)
    (hC : IidBirthZeroStart C) (e : Fin n) :
    IidBirthPositive
      (localStep ring P_partialSealIidBirth C e) := by
  let j := ring.rightNeighbor e
  let D := localStep ring P_partialSealIidBirth C e
  have hclean := iidBirthZeroStart_armedClean C hC
  have hce := hclean e (hC.1 e)
  have hcj := hclean j (hC.1 j)
  have hinv := iidBirth_birth_inner_invariants
    ring hn C e (hC.1 e) (by simpa [j] using hC.1 j)
      hce.1 hce.2 hcj.1 hcj.2
      (allClosed_openBalanced (iidBirthErase C) hC.2.1)
  change SealSweepOpenBalanced (iidBirthErase D) ∧
    SealSweepHasLeader (iidBirthErase D) at hinv
  have hcleanD := iidBirthArmedClean_localStep ring C hclean e
  refine ⟨hcleanD, hinv.1, hinv.2, e, ?_⟩
  have hpair := P_partialSealIidBirth_birth
    (C e) (C j) (hC.1 e) (hC.1 j)
      hce.1 hce.2 hcj.1 hcj.2
  simp [D, localStep, j, hpair]

/-- The one-agent self-edge retains the leader-producing initiator output and
immediately enters the singleton committed kernel. -/
theorem iidBirthZeroStart_localStep_singleton
    (ring : DirectedRing 1)
    (C : IidBirthConfig 1 psi kappa tau)
    (hC : IidBirthZeroStart C) (e : Fin 1) :
    IidBirthSingletonKernel
      (localStep ring P_partialSealIidBirth C e) := by
  let j := ring.rightNeighbor e
  let D := localStep ring P_partialSealIidBirth C e
  have hclean := iidBirthZeroStart_armedClean C hC
  have hje : j = e := Subsingleton.elim _ _
  have hce := hclean e (hC.1 e)
  have hcj := hclean j (hC.1 j)
  have hpair := P_partialSealIidBirth_birth
    (C e) (C j) (hC.1 e) (hC.1 j)
      hce.1 hce.2 hcj.1 hcj.2
  have hpairSelf : P_partialSealIidBirth (C e) (C e) =
      ((iidBirthOpenLeader (C e).1, false),
        (iidBirthOpenFollower (C e).1, false)) := by
    simpa [hje] using hpair
  refine ⟨rfl, ?_, ?_⟩
  · intro i
    have hie : i = e := Subsingleton.elim _ _
    subst i
    simp [D, localStep, j, hje, hpairSelf]
  · refine ⟨e, ?_⟩
    simp [D, iidBirthErase, localStep, j, hje, hpairSelf]

private theorem iidBirth_singleton_step_eq
    (ring : DirectedRing n) (hn : n = 1)
    (C : IidBirthConfig n psi kappa tau)
    (hall : IidBirthAllCommitted C) (e : Fin n) :
    localStep ring P_partialSealIidBirth C e = C := by
  have hindices : ∀ a b : Fin n, a = b := by
    intro a b
    apply Fin.ext
    have ha := a.isLt
    have hb := b.isLt
    omega
  have hje : ring.rightNeighbor e = e := hindices _ _
  have heBit : (C e).2 = false := hall e
  have hpair := P_partialSealIidBirth_committed
    (C e) (C (ring.rightNeighbor e)) heBit
      (by rw [hje]; exact heBit)
  have hinner :
      (P_partialSealSweep (C e).1 (C e).1).1 = (C e).1 := by
    cases hc : (C e).1.2 with
    | false =>
        cases hl : sweepLockLeader (C e).1 <;>
          simp [P_partialSealSweep, hl, hc]
    | true =>
        cases hl : sweepLockLeader (C e).1 with
        | false => simp [P_partialSealSweep, hl, hc]
        | true =>
            rw [P_partialSealSweep_twoClosedLeaders
              (C e).1 (C e).1 hl hc hl hc]
            exact Prod.ext rfl hc.symm
  have hpairSelf : P_partialSealIidBirth (C e) (C e) =
      (((P_partialSealSweep (C e).1 (C e).1).1, false),
        ((P_partialSealSweep (C e).1 (C e).1).2, false)) := by
    simpa [hje] using hpair
  have htransition :
      (P_partialSealIidBirth (C e) (C e)).1 = C e := by
    rw [hpairSelf, hinner]
    exact Prod.ext rfl heBit.symm
  funext i
  have hie : i = e := hindices _ _
  subst i
  simp [localStep, hje, htransition]

theorem iidBirthSingletonKernel_localStep
    (ring : DirectedRing n)
    (C : IidBirthConfig n psi kappa tau)
    (hC : IidBirthSingletonKernel C) (e : Fin n) :
    IidBirthSingletonKernel
      (localStep ring P_partialSealIidBirth C e) := by
  rw [iidBirth_singleton_step_eq ring hC.1 C hC.2.1 e]
  exact hC

/-- The restart domain is closed under every exact local transition.  This is
the key property missing from the retiring proposal. -/
theorem iidBirthDomain_localStepClosed
    (ring : DirectedRing n) :
    LocalStepClosed ring
      (P_partialSealIidBirth (psi := psi) (kappa := kappa) (tau := tau))
      (IidBirthDomain (psi := psi) (kappa := kappa) (tau := tau)) := by
  intro C hC e
  rcases hC with hzero | hpositive | hsingleton
  · by_cases hn : n = 1
    · subst n
      exact Or.inr (Or.inr
        (iidBirthZeroStart_localStep_singleton ring C hzero e))
    · have hnTwo : 1 < n := by
        have hnPos := ring.hn
        omega
      exact Or.inr (Or.inl
        (iidBirthZeroStart_localStep_positive ring hnTwo C hzero e))
  · exact Or.inr (Or.inl
      (iidBirthPositive_localStep ring C hpositive e))
  · exact Or.inr (Or.inr
      (iidBirthSingletonKernel_localStep ring C hsingleton e))

/-! ## A bounded clockwise barrier producer -/

private theorem cwPos_ne_of_ne_below_iidBirth
    (ring : DirectedRing n) (start : Fin n)
    {a b : Nat} (ha : a < n) (hb : b < n) (hab : a ≠ b) :
    cwPos ring start a ≠ cwPos ring start b := by
  intro hpos
  apply hab
  have ha' := cwPos_bounded_unique ring start
    (cwPos ring start a) a ha rfl
  have hb' := cwPos_bounded_unique ring start
    (cwPos ring start a) b hb hpos.symm
  exact ha'.trans hb'.symm

/-- Once one committed site exists, the first `steps` clockwise edges commit
every visited offset.  Inner R91 steps may run inside an already committed
prefix, but they cannot reopen the barrier. -/
theorem iidBirth_commit_clockwise_prefix
    (ring : DirectedRing n) (hn : 1 < n)
    (C : IidBirthConfig n psi kappa tau) (root : Fin n)
    (hroot : (C root).2 = false)
    (steps : Nat) (hlt : steps < n) :
    let D := runLocalSchedule ring P_partialSealIidBirth C
      (clockwiseEdgeSchedule ring root steps)
    ∀ k : Nat, k ≤ steps →
      (D (cwPos ring root k)).2 = false := by
  dsimp only
  induction steps with
  | zero =>
      intro k hk
      have hkzero : k = 0 := by omega
      subst k
      simpa [clockwiseEdgeSchedule, runLocalSchedule] using hroot
  | succ s ih =>
      let D := runLocalSchedule ring P_partialSealIidBirth C
        (clockwiseEdgeSchedule ring root s)
      let e := cwPos ring root s
      let j := ring.rightNeighbor e
      let E := localStep ring P_partialSealIidBirth D e
      have hslt : s < n := by omega
      have hprev := ih hslt
      change ∀ k : Nat, k ≤ s →
        (D (cwPos ring root k)).2 = false at hprev
      have he : (D e).2 = false := by
        simpa [e] using hprev s (by omega)
      have hedge := iidBirth_localStep_commits_right ring hn D e he
      change (E e).2 = false ∧ (E j).2 = false ∧
        ∀ i : Fin n, i ≠ e → i ≠ j → E i = D i at hedge
      have hjpos : j = cwPos ring root (s + 1) := by
        simpa [j, e, Nat.add_assoc] using
          (cwPos_succ ring root s).symm
      have hrun :
          runLocalSchedule ring P_partialSealIidBirth C
              (clockwiseEdgeSchedule ring root (s + 1)) = E := by
        change runLocalSchedule ring P_partialSealIidBirth C
            (clockwiseEdgeSchedule ring root s ++ [e]) = E
        rw [PPLLSchedulerBlocks.runLocalSchedule_append]
        rfl
      rw [hrun]
      intro k hk
      by_cases hknew : k = s + 1
      · subst k
        rw [← hjpos]
        exact hedge.2.1
      · have hkprev : k ≤ s := by omega
        by_cases hkcurrent : k = s
        · subst k
          simpa [e] using hedge.1
        · have hklt : k < n := by omega
          have hke : cwPos ring root k ≠ e := by
            simpa [e] using cwPos_ne_of_ne_below_iidBirth
              ring root hklt hslt hkcurrent
          have hkj : cwPos ring root k ≠ j := by
            rw [hjpos]
            exact cwPos_ne_of_ne_below_iidBirth
              ring root hklt hlt hknew
          rw [hedge.2.2 (cwPos ring root k) hke hkj]
          exact hprev k hkprev

/-- A clockwise word of length `n-1` commits the entire ring from any
positive live state. -/
theorem iidBirthPositive_reaches_allCommitted
    (ring : DirectedRing n) (hn : 1 < n)
    (C : IidBirthConfig n psi kappa tau)
    (hC : IidBirthPositive C) :
    ∃ word : DetSchedule n,
      word.length = n - 1 ∧
      let D := runLocalSchedule ring P_partialSealIidBirth C word
      IidBirthAllCommitted D ∧ IidBirthPositive D := by
  obtain ⟨root, hroot⟩ := hC.2.2.2
  let word := clockwiseEdgeSchedule ring root (n - 1)
  let D := runLocalSchedule ring P_partialSealIidBirth C word
  have hprefix := iidBirth_commit_clockwise_prefix
    ring hn C root hroot (n - 1) (by omega)
  change ∀ k : Nat, k ≤ n - 1 →
    (D (cwPos ring root k)).2 = false at hprefix
  have hall : IidBirthAllCommitted D := by
    intro i
    let k := cwDist ring root i
    have hklt : k < n := cwDist_lt ring root i
    have hki : cwPos ring root k = i := cwPos_cwDist ring root i
    have hkBound : k ≤ n - 1 := by omega
    rw [← hki]
    exact hprefix k hkBound
  have hpositive : IidBirthPositive D := by
    apply localStepClosed_runLocalSchedule ring P_partialSealIidBirth
      IidBirthPositive
    · intro X hX e
      exact iidBirthPositive_localStep ring X hX e
    · exact hC
  exact ⟨word, clockwiseEdgeSchedule_length ring root (n - 1),
    hall, hpositive⟩

/-- From the authorized all-armed zero-leader start on a nontrivial ring, a
word of exactly `n` edges first creates a balanced pair and then commits every
site.  Thus the endpoint is the precise R91 interface: wholly committed,
open-token balanced, and positive. -/
theorem iidBirthZeroStart_reaches_allCommitted_positive
    (ring : DirectedRing n) (hn : 1 < n)
    (C : IidBirthConfig n psi kappa tau)
    (hC : IidBirthZeroStart C) :
    ∃ word : DetSchedule n,
      word.length = n ∧
      let D := runLocalSchedule ring P_partialSealIidBirth C word
      IidBirthAllCommitted D ∧ IidBirthPositive D := by
  let seed : Fin n := ⟨0, ring.hn⟩
  let C₁ := localStep ring P_partialSealIidBirth C seed
  have hC₁Positive : IidBirthPositive C₁ :=
    iidBirthZeroStart_localStep_positive ring hn C hC seed
  obtain ⟨tail, htailLength, hall, hpositive⟩ :=
    iidBirthPositive_reaches_allCommitted ring hn C₁ hC₁Positive
  refine ⟨seed :: tail, ?_, ?_⟩
  · simp only [List.length_cons]
    omega
  · change IidBirthAllCommitted
        (runLocalSchedule ring P_partialSealIidBirth C₁ tail) ∧
      IidBirthPositive
        (runLocalSchedule ring P_partialSealIidBirth C₁ tail)
    exact ⟨hall, hpositive⟩

/-! ## Exact simulation and safety after commitment -/

theorem iidBirthAllCommitted_localStep
    (ring : DirectedRing n)
    (C : IidBirthConfig n psi kappa tau)
    (hC : IidBirthAllCommitted C) (e : Fin n) :
    IidBirthAllCommitted
      (localStep ring P_partialSealIidBirth C e) := by
  let j := ring.rightNeighbor e
  have hpair := P_partialSealIidBirth_committed
    (C e) (C j) (hC e) (hC j)
  intro i
  by_cases hie : i = e
  · subst i
    simp [localStep, j, hpair]
  · by_cases hij : i = j
    · subst i
      simp [localStep, j, hie, hpair]
    · simp [localStep, j, hie, hij, hpair, hC i]

theorem iidBirth_committed_run_simulation
    (ring : DirectedRing n)
    (C : IidBirthConfig n psi kappa tau)
    (hC : IidBirthAllCommitted C) (word : DetSchedule n) :
    let D := runLocalSchedule ring P_partialSealIidBirth C word
    IidBirthAllCommitted D ∧
      iidBirthErase D =
        runLocalSchedule ring P_partialSealSweep (iidBirthErase C) word := by
  induction word generalizing C with
  | nil => exact ⟨hC, rfl⟩
  | cons e rest ih =>
      let C₁ := localStep ring P_partialSealIidBirth C e
      have hC₁ : IidBirthAllCommitted C₁ :=
        iidBirthAllCommitted_localStep ring C hC e
      have hstep : iidBirthErase C₁ =
          localStep ring P_partialSealSweep (iidBirthErase C) e :=
        iidBirthErase_localStep_committed ring C e
          (hC e) (hC (ring.rightNeighbor e))
      obtain ⟨hall, herase⟩ := ih C₁ hC₁
      refine ⟨hall, ?_⟩
      change iidBirthErase
          (runLocalSchedule ring P_partialSealIidBirth C₁ rest) =
        runLocalSchedule ring P_partialSealSweep
          (localStep ring P_partialSealSweep (iidBirthErase C) e) rest
      rw [herase, hstep]

theorem iidBirth_output_eq_sealSweep
    (u : IidBirthState psi kappa tau) :
    (P_partialSealIidBirthProtocol psi kappa tau).output u =
      (P_partialSealSweepProtocol psi kappa tau).output u.1 := by
  rfl

theorem iidBirthErase_reachable_committed
    (ring : DirectedRing n)
    (C D : IidBirthConfig n psi kappa tau)
    (hC : IidBirthAllCommitted C)
    (hreach : PopulationProtocol.Reachable
      (P_partialSealIidBirthProtocol psi kappa tau) ring C D) :
    IidBirthAllCommitted D ∧
      PopulationProtocol.Reachable
        (P_partialSealSweepProtocol psi kappa tau) ring
        (iidBirthErase C) (iidBirthErase D) := by
  let R : IidBirthConfig n psi kappa tau → Prop := fun X =>
    IidBirthAllCommitted X ∧
      PopulationProtocol.Reachable
        (P_partialSealSweepProtocol psi kappa tau) ring
        (iidBirthErase C) (iidBirthErase X)
  have hRclosed : PopulationProtocol.ClosedPred
      (P_partialSealIidBirthProtocol psi kappa tau) ring R := by
    intro X hX Y hstep
    obtain ⟨e, rfl⟩ := hstep
    have hYCommitted := iidBirthAllCommitted_localStep
      ring X hX.1 e
    have herase := iidBirthErase_localStep_committed ring X e
      (hX.1 e) (hX.1 (ring.rightNeighbor e))
    refine ⟨hYCommitted, hX.2.trans ?_⟩
    apply PopulationProtocol.OneStep.to_reachable
    exact ⟨e, herase⟩
  exact hRclosed.reachable
    ⟨hC, @PopulationProtocol.Reachable.refl n
      (P_partialSealSweepProtocol psi kappa tau) ring (iidBirthErase C)⟩
    hreach

/-- R91 semantic safety lifts without loss once all sites are committed. -/
theorem iidBirthAllCommitted_lift_isSafe
    (ring : DirectedRing n)
    (C : IidBirthConfig n psi kappa tau)
    (hC : IidBirthAllCommitted C)
    (hsafe : PopulationProtocol.IsSafe
      (P_partialSealSweepProtocol psi kappa tau) ring
      (iidBirthErase C) isLeaderOutput) :
    PopulationProtocol.IsSafe
      (P_partialSealIidBirthProtocol psi kappa tau) ring C
      isLeaderOutput := by
  constructor
  · change ∃ i : Fin n,
      isLeaderOutput
          ((P_partialSealSweepProtocol psi kappa tau).output
            (iidBirthErase C i)) = true ∧
        ∀ j : Fin n,
          isLeaderOutput
              ((P_partialSealSweepProtocol psi kappa tau).output
                (iidBirthErase C j)) = true → j = i
    exact hsafe.1
  · intro D hreach i
    obtain ⟨hDCommitted, hEraseReach⟩ :=
      iidBirthErase_reachable_committed ring C D hC hreach
    have hout := hsafe.2 (iidBirthErase D) hEraseReach i
    exact hout

/-- Every state in the one-agent committed kernel is already semantically
safe for the repaired protocol. -/
theorem iidBirthSingletonKernel_isSafe
    (ring : DirectedRing n)
    (C : IidBirthConfig n psi kappa tau)
    (hC : IidBirthSingletonKernel C) :
    PopulationProtocol.IsSafe
      (P_partialSealIidBirthProtocol psi kappa tau) ring C
      isLeaderOutput := by
  have hn : n = 1 := hC.1
  subst n
  have hfixed : ∀ D : IidBirthConfig 1 psi kappa tau,
      PopulationProtocol.Reachable
        (P_partialSealIidBirthProtocol psi kappa tau) ring C D → D = C := by
    intro D hreach
    have hclosed : PopulationProtocol.ClosedPred
        (P_partialSealIidBirthProtocol psi kappa tau) ring
        (fun X => X = C) := by
      intro X hX Y hstep
      subst X
      obtain ⟨e, rfl⟩ := hstep
      exact iidBirth_singleton_step_eq ring rfl C hC.2.1 e
    exact hclosed.reachable rfl hreach
  constructor
  · obtain ⟨root, hroot⟩ := hC.2.2
    refine ⟨root, ?_, ?_⟩
    · change isLeaderOutput
        ((P_partialSealSweepProtocol psi kappa tau).output
          (iidBirthErase C root)) = true
      simp [P_partialSealSweepProtocol, hroot, isLeaderOutput]
    · intro j hj
      exact Subsingleton.elim _ _
  · intro D hreach i
    rw [hfixed D hreach]

/-! ## Uniform landing bound and exact iid amplification -/

/-- From every nontrivial positive barrier state, first commit the remaining
sites and then run R91's balanced-positive landing word.  The two phases have
lengths `n-1` and at most `n²+3n`, respectively. -/
theorem iidBirthPositive_reaches_isSafe
    (ring : DirectedRing n) (hn : 1 < n)
    (C : IidBirthConfig n psi kappa tau)
    (hC : IidBirthPositive C) :
    ∃ word : DetSchedule n,
      word.length ≤ n * n + 4 * n - 1 ∧
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
    sealSweep_balancedPositive_reaches_isSafe_poly
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
  · simp only [List.length_append]
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

/-- The first edge births a balanced pair; the remaining uniform word is the
positive landing word above. -/
theorem iidBirthZeroStart_reaches_isSafe_nontrivial
    (ring : DirectedRing n) (hn : 1 < n)
    (C : IidBirthConfig n psi kappa tau)
    (hC : IidBirthZeroStart C) :
    ∃ word : DetSchedule n,
      word.length ≤ n * n + 4 * n ∧
      PopulationProtocol.IsSafe
        (P_partialSealIidBirthProtocol psi kappa tau) ring
        (runLocalSchedule ring P_partialSealIidBirth C word)
        isLeaderOutput := by
  let seed : Fin n := ⟨0, ring.hn⟩
  let D := localStep ring P_partialSealIidBirth C seed
  have hDPositive : IidBirthPositive D :=
    iidBirthZeroStart_localStep_positive ring hn C hC seed
  obtain ⟨tail, htailLength, htailSafe⟩ :=
    iidBirthPositive_reaches_isSafe ring hn D hDPositive
  refine ⟨seed :: tail, ?_, ?_⟩
  · simp only [List.length_cons]
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

/-- The one-agent self-edge birth is already a fixed unique-leader kernel. -/
theorem iidBirthZeroStart_reaches_isSafe_singleton
    (ring : DirectedRing 1)
    (C : IidBirthConfig 1 psi kappa tau)
    (hC : IidBirthZeroStart C) :
    ∃ word : DetSchedule 1,
      word.length ≤ 1 * 1 + 4 * 1 ∧
      PopulationProtocol.IsSafe
        (P_partialSealIidBirthProtocol psi kappa tau) ring
        (runLocalSchedule ring P_partialSealIidBirth C word)
        isLeaderOutput := by
  let seed : Fin 1 := ⟨0, by omega⟩
  have hkernel := iidBirthZeroStart_localStep_singleton
    ring C hC seed
  refine ⟨[seed], by simp, ?_⟩
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

/-- Uniform zero-start landing, including the self-edge ring. -/
theorem iidBirthZeroStart_reaches_isSafe
    (ring : DirectedRing n)
    (C : IidBirthConfig n psi kappa tau)
    (hC : IidBirthZeroStart C) :
    ∃ word : DetSchedule n,
      word.length ≤ n * n + 4 * n ∧
      PopulationProtocol.IsSafe
        (P_partialSealIidBirthProtocol psi kappa tau) ring
        (runLocalSchedule ring P_partialSealIidBirth C word)
        isLeaderOutput := by
  by_cases hn : n = 1
  · subst n
    exact iidBirthZeroStart_reaches_isSafe_singleton ring C hC
  · have hnTwo : 1 < n := by
      have hnPos := ring.hn
      omega
    exact iidBirthZeroStart_reaches_isSafe_nontrivial ring hnTwo C hC

/-- One common iid block accommodates birth, barrier propagation, mixed-state
normalization, and the final R91 positive landing. -/
def iidBirthBlockLength (n : Nat) : Nat := n * n + 4 * n

/-- Every nonsafe state in the closed repair domain has a favorable word of
the common block length. -/
theorem iidBirthDomain_boundedSafeProducer
    (ring : DirectedRing n) :
    BoundedSafeScheduleProducer ring P_partialSealIidBirth
      (IidBirthDomain (psi := psi) (kappa := kappa) (tau := tau))
      (fun C => PopulationProtocol.IsSafe
        (P_partialSealIidBirthProtocol psi kappa tau) ring C
        isLeaderOutput)
      (iidBirthBlockLength n) := by
  intro C hC _
  rcases hC with hzero | hpositive | hsingleton
  · obtain ⟨word, hlength, hsafe⟩ :=
      iidBirthZeroStart_reaches_isSafe ring C hzero
    exact ⟨word, by simpa [iidBirthBlockLength] using hlength, hsafe⟩
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
      refine ⟨[], by simp [iidBirthBlockLength], ?_⟩
      simpa only [runLocalSchedule] using
        (iidBirthSingletonKernel_isSafe ring C hkernel)
    · have hnTwo : 1 < n := by
        have hnPos := ring.hn
        omega
      obtain ⟨word, hlength, hsafe⟩ :=
        iidBirthPositive_reaches_isSafe ring hnTwo C hpositive
      refine ⟨word, ?_, hsafe⟩
      simp only [iidBirthBlockLength]
      omega
  · refine ⟨[], by simp [iidBirthBlockLength], ?_⟩
    simpa only [runLocalSchedule] using
      (iidBirthSingletonKernel_isSafe ring C hsingleton)

/-- Classical Boolean view of genuine Definition-1 safety.  It is used only
for exact finite scheduler counting. -/
noncomputable def iidBirthIsSafeTest
    (ring : DirectedRing n)
    (C : IidBirthConfig n psi kappa tau) : Bool := by
  classical
  exact if PopulationProtocol.IsSafe
      (P_partialSealIidBirthProtocol psi kappa tau) ring C isLeaderOutput
    then true else false

theorem iidBirthIsSafeTest_spec
    (ring : DirectedRing n)
    (C : IidBirthConfig n psi kappa tau) :
    iidBirthIsSafeTest ring C = true ↔
      PopulationProtocol.IsSafe
        (P_partialSealIidBirthProtocol psi kappa tau) ring C
        isLeaderOutput := by
  classical
  simp [iidBirthIsSafeTest]

/-- Exact iid repeated-block theorem.  Of the `n^(blocks*L)` schedules, at
most `(n^L-1)^blocks` can miss semantic safety, where `L=n²+4n`. -/
theorem iidBirthDomain_repeatedBlockSSLEOn
    (ring : DirectedRing n) :
    ∀ blocks,
      UniformFiniteHorizonSSLEOn
        (P_partialSealIidBirthProtocol psi kappa tau) ring
        isLeaderOutput
        (IidBirthDomain (psi := psi) (kappa := kappa) (tau := tau))
        (blocks * iidBirthBlockLength n)
        ((n ^ iidBirthBlockLength n - 1) ^ blocks) := by
  exact boundedIsSafeProducer_repeatedBlockSSLEOn
    (P_partialSealIidBirthProtocol psi kappa tau) ring
    isLeaderOutput
    (IidBirthDomain (psi := psi) (kappa := kappa) (tau := tau))
    (iidBirthIsSafeTest ring)
    (iidBirthIsSafeTest_spec ring)
    (iidBirthDomain_localStepClosed ring)
    (iidBirthBlockLength n)
    (iidBirthDomain_boundedSafeProducer ring)

/-- Explicit finite WHP corollary: with
`blocks=(n-1)(n^L-1)+1`, at most a `1/n` fraction of length-`blocks*L`
uniform iid schedules fail to reach semantic safety. -/
theorem iidBirthDomain_explicitOneOverNSSLEOn
    (ring : DirectedRing n) (hn : 1 < n) :
    let L := iidBirthBlockLength n
    let blocks := (n - 1) * (n ^ L - 1) + 1
    UniformOneOverNFailureAtHorizonOn
      (P_partialSealIidBirthProtocol psi kappa tau) ring
      isLeaderOutput
      (IidBirthDomain (psi := psi) (kappa := kappa) (tau := tau))
      1 (blocks * L) := by
  dsimp only
  have hL : 0 < iidBirthBlockLength n := by
    dsimp [iidBirthBlockLength]
    have hnPos := ring.hn
    omega
  exact boundedIsSafeProducer_explicitOneOverNSSLEOn
    (P_partialSealIidBirthProtocol psi kappa tau) ring
    isLeaderOutput
    (IidBirthDomain (psi := psi) (kappa := kappa) (tau := tau))
    (iidBirthIsSafeTest ring)
    (iidBirthIsSafeTest_spec ring)
    (iidBirthDomain_localStepClosed ring)
    hn (iidBirthBlockLength n) hL
    (iidBirthDomain_boundedSafeProducer ring)

/-! ## The exact locality obstruction to strict single birth -/

/-- The four-agent witness ring. -/
abbrev iidBirthLocalityRingFour : DirectedRing 4 := ⟨by omega⟩

/-- Uniform local state used to isolate endpoint locality from every
protocol-specific invariant. -/
def endpointLocalUniformFour {Q : Type} (q : Q) : Fin 4 → Q :=
  fun _ => q

/-- Execute the two disjoint directed edges `0→1` and `2→3`. -/
def endpointLocalTwoDisjointBirths {Q : Type}
    (T : Q → Q → Q × Q) (q : Q) : Fin 4 → Q :=
  runLocalSchedule iidBirthLocalityRingFour T
    (endpointLocalUniformFour q) [(0 : Fin 4), (2 : Fin 4)]

/-- Endpoint-local causality forces the disjoint edge to see the original
uniform pair.  Hence any rule whose left output births a leader on `(q,q)`
births leaders at both zero and two under the displayed two-edge prefix. -/
theorem endpointLocal_uniform_leftBirth_twoDisjoint
    {Q : Type} (T : Q → Q → Q × Q)
    (outputLeader : Q → Bool) (q : Q)
    (hbirth : outputLeader (T q q).1 = true) :
    outputLeader (endpointLocalTwoDisjointBirths T q (0 : Fin 4)) = true ∧
      outputLeader (endpointLocalTwoDisjointBirths T q (2 : Fin 4)) = true := by
  constructor
  · change outputLeader (T q q).1 = true
    exact hbirth
  · change outputLeader (T q q).1 = true
    exact hbirth

/-- In particular, strict uniqueness after that two-edge prefix is false.
This is only a local suppression obstruction; it says nothing against a
protocol, such as the repair above, that tolerates and later merges concurrent
births. -/
theorem endpointLocal_uniform_leftBirth_not_strictly_unique
    {Q : Type} (T : Q → Q → Q × Q)
    (outputLeader : Q → Bool) (q : Q)
    (hbirth : outputLeader (T q q).1 = true) :
    ¬ (∀ i j : Fin 4,
      outputLeader (endpointLocalTwoDisjointBirths T q i) = true →
      outputLeader (endpointLocalTwoDisjointBirths T q j) = true →
      i = j) := by
  intro hunique
  have htwo := endpointLocal_uniform_leftBirth_twoDisjoint
    T outputLeader q hbirth
  have hzeroTwo : (0 : Fin 4) = (2 : Fin 4) :=
    hunique 0 2 htwo.1 htwo.2
  exact (by decide : (0 : Fin 4) ≠ (2 : Fin 4)) hzeroTwo

/-- Two scheduled edges are causally serialized exactly when they share an
endpoint.  A strict one-birth design must at least exclude a second disjoint
birth before information from the first can reach it (or introduce a shared
nonlocal/asymmetric resource). -/
def BirthNoticeSerialized {m : Nat}
    (ring : DirectedRing m) (first second : Fin m) : Prop :=
  first = second ∨ first = ring.rightNeighbor second ∨
    ring.rightNeighbor first = second ∨
    ring.rightNeighbor first = ring.rightNeighbor second

theorem iidBirthLocalityRingFour_zero_two_not_serialized :
    ¬ BirthNoticeSerialized iidBirthLocalityRingFour
      (0 : Fin 4) (2 : Fin 4) := by
  simp [BirthNoticeSerialized, DirectedRing.rightNeighbor,
    iidBirthLocalityRingFour]

/-- The repaired transition remains inside its balanced-positive domain even
under the same two-disjoint-edge prefix.  Concurrent births are recoverable,
not absorbing. -/
theorem iidBirth_twoDisjointPrefix_remains_positive
    (C : IidBirthConfig 4 psi kappa tau)
    (hC : IidBirthZeroStart C) :
    IidBirthPositive
      (runLocalSchedule iidBirthLocalityRingFour
        P_partialSealIidBirth C [(0 : Fin 4), (2 : Fin 4)]) := by
  have hfirst := iidBirthZeroStart_localStep_positive
    iidBirthLocalityRingFour (by omega) C hC (0 : Fin 4)
  exact iidBirthPositive_localStep iidBirthLocalityRingFour
    (localStep iidBirthLocalityRingFour P_partialSealIidBirth C (0 : Fin 4))
    hfirst (2 : Fin 4)


end PPartialSealSweepIidBirthRepairSol
end PPLLCompleteMultiLeaderCleanup
