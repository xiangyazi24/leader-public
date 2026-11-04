import Leader.Wu.PartialProtocol.SweepLock

/-!
# Unbounded stale-seal counterfamilies for the dynamic sweep

The factor-four dynamic sweep deliberately makes every pair of sealed states
an identity pair.  Since the seal bit is ordinary arbitrary-initialized local
state, this freezes much more than the intended sealed one-leader kernel:
sealing any configuration with two current leader outputs produces a closed
bad trap, at every ring size at least two.

The first section isolates the exact locality principle behind this issue for
an arbitrary deterministic current-pair protocol.  Identity of packaged steps
on a nontrivial kernel word determines the local transition on every ordered
pair occurring in that word.  Consequently, any other word whose ordered edge
pairs are covered by such kernel occurrences is fixed too.  In particular,
the double cover of a nontrivial fixed unique-leader word is a fixed
two-leader word.

The converse needs the pair-coverage hypothesis.  A small Boolean rule below
fixes every nontrivial unique-leader configuration while resetting the absent
leader/leader pair.  Thus unique-leader-kernel identity alone does not force
arbitrary multi-leader configurations to be fixed.  These are scoped facts
about deterministic rules that inspect only the current ordered endpoint
states; they are not impossibility results for general population protocols.
-/

namespace PPLLCompleteMultiLeaderCleanup
namespace PPartialDynamicSweepCounterfamilySol

open PPLL PPLLResearchFormulation
open PPLLStaticDoubleCoverNoGo
open PPartialMinimalLockRepairSol
open PPartialMinimalLockStaleCounterexampleSol
open PPartialDynamicSweepLockSol

variable {n psi kappa tau : Nat}

/-! ## Generic current-pair locality lemmas -/

/-- If the ordered endpoint transition is identity, the corresponding
packaged ring step is identity.  This direction also holds for a self-edge. -/
theorem currentPair_step_eq_of_transition_eq
    (P : PopulationProtocol) (ring : DirectedRing n)
    (C : P.Configuration n) (e : Fin n)
    (hpair : P.transition (C e) (C (ring.rightNeighbor e)) =
      (C e, C (ring.rightNeighbor e))) :
    P.step ring C e = C := by
  funext i
  by_cases hie : i = e
  · subst i
    simp [PopulationProtocol.step, hpair]
  · by_cases hij : i = ring.rightNeighbor e
    · subst i
      simp [PopulationProtocol.step, hie, hpair]
    · simp [PopulationProtocol.step, hie, hij, hpair]

/-- On a nontrivial ring, identity of a packaged step recovers identity of
the complete ordered local transition.  Nontriviality is necessary because a
self-edge stores only the transition's first component. -/
theorem currentPair_transition_eq_of_step_eq
    (P : PopulationProtocol) (ring : DirectedRing n) (hn : 1 < n)
    (C : P.Configuration n) (e : Fin n)
    (hstep : P.step ring C e = C) :
    P.transition (C e) (C (ring.rightNeighbor e)) =
      (C e, C (ring.rightNeighbor e)) := by
  let j := ring.rightNeighbor e
  have hje : j ≠ e := rightNeighbor_ne_self_of_one_lt ring hn e
  have hleft :
      (P.transition (C e) (C j)).1 = C e := by
    have he := congrFun hstep e
    simpa [PopulationProtocol.step, j] using he
  have hright :
      (P.transition (C e) (C j)).2 = C j := by
    have hj := congrFun hstep j
    simpa [PopulationProtocol.step, j, hje] using hj
  exact Prod.ext hleft hright

/-- A current-state class is locally inert when the rule is identity on every
ordered pair drawn from the class. -/
def CurrentPairIdentityOn
    (P : PopulationProtocol) (S : P.Q → Prop) : Prop :=
  ∀ l r, S l → S r → P.transition l r = (l, r)

/-- A configuration entirely inside a locally inert state class is fixed on
every edge. -/
theorem currentPair_every_step_eq_of_identityOn
    (P : PopulationProtocol) (S : P.Q → Prop)
    (hidentity : CurrentPairIdentityOn P S)
    (ring : DirectedRing n) (C : P.Configuration n)
    (hC : ∀ i, S (C i)) :
    ∀ e, P.step ring C e = C := by
  intro e
  exact currentPair_step_eq_of_transition_eq P ring C e
    (hidentity (C e) (C (ring.rightNeighbor e))
      (hC e) (hC (ring.rightNeighbor e)))

/-- If every step from one configuration is identity, its reachable set is
the singleton containing that configuration. -/
theorem currentPair_reachable_eq_of_every_step_eq
    (P : PopulationProtocol) (ring : DirectedRing n)
    (C : P.Configuration n)
    (hfixed : ∀ e, P.step ring C e = C)
    {D : P.Configuration n}
    (hreach : PopulationProtocol.Reachable P ring C D) :
    D = C := by
  have hsingleton : PopulationProtocol.ClosedPred P ring (fun X => X = C) := by
    intro X hX Y hXY
    subst X
    obtain ⟨e, rfl⟩ := hXY
    exact hfixed e
  exact hsingleton.reachable rfl hreach

/-- Exact local-indistinguishability theorem.  Kernel words may vary with the
target edge.  If each ordered edge pair of `D` occurs on a nontrivial fixed
kernel word, determinism and current-pair locality force every step of `D` to
be identity. -/
theorem currentPair_every_step_eq_of_kernel_pairCoverage
    (P : PopulationProtocol)
    {A : Type} (size : A → Nat)
    (kernelRing : (a : A) → DirectedRing (size a))
    (kernelConfig : (a : A) → P.Configuration (size a))
    (kernelNontrivial : ∀ a, 1 < size a)
    (kernelFixed : ∀ (a : A) (e : Fin (size a)),
      P.step (kernelRing a) (kernelConfig a) e = kernelConfig a)
    (ring : DirectedRing n) (D : P.Configuration n)
    (hcovered : ∀ e : Fin n,
      ∃ (a : A) (s : Fin (size a)),
        kernelConfig a s = D e ∧
        kernelConfig a ((kernelRing a).rightNeighbor s) =
          D (ring.rightNeighbor e)) :
    ∀ e, P.step ring D e = D := by
  intro e
  obtain ⟨a, s, hleft, hright⟩ := hcovered e
  have hpair := currentPair_transition_eq_of_step_eq
    P (kernelRing a) (kernelNontrivial a) (kernelConfig a) s
      (kernelFixed a s)
  have htarget :
      P.transition (D e) (D (ring.rightNeighbor e)) =
        (D e, D (ring.rightNeighbor e)) := by
    simpa [hleft, hright] using hpair
  exact currentPair_step_eq_of_transition_eq P ring D e htarget

/-- Repeating a nontrivial fixed cyclic word twice introduces no new ordered
endpoint pair, so the doubled word is fixed edge-by-edge. -/
theorem currentPair_doubleCover_every_step_eq
    (P : PopulationProtocol) {m : Nat} (hm : 1 < m)
    (C : P.Configuration m)
    (hfixed : ∀ e : Fin m,
      P.step (cycleRing (by omega)) C e = C) :
    ∀ e : Fin (2 * m),
      P.step (doubleRing (by omega))
        (doubleCoverConfig P (by omega) C) e =
          doubleCoverConfig P (by omega) C := by
  intro e
  let hmpos : m > 0 := by omega
  let source := foldDouble hmpos e
  have hpair := currentPair_transition_eq_of_step_eq
    P (cycleRing hmpos) hm C source (hfixed source)
  apply currentPair_step_eq_of_transition_eq
  simpa [doubleCoverConfig, source,
    foldDouble_rightNeighbor hmpos e] using hpair

/-- A nontrivial fixed unique-leader word therefore yields a closed repeated
two-leader trap under the same ring-size-independent current-pair rule. -/
theorem currentPair_fixed_unique_doubleCover_trap
    (P : PopulationProtocol) (isLeader : P.Y → Bool)
    {m : Nat} (hm : 1 < m) (C : P.Configuration m)
    (hunique : UniqueLeaderOutput P m C isLeader)
    (hfixed : ∀ e : Fin m,
      P.step (cycleRing (by omega)) C e = C) :
    let hmpos : m > 0 := by omega
    let D := doubleCoverConfig P hmpos C
    HasTwoLeaderOutputs P isLeader D ∧
      (∀ e : Fin (2 * m), P.step (doubleRing hmpos) D e = D) ∧
      (∀ D' : P.Configuration (2 * m),
        PopulationProtocol.Reachable P (doubleRing hmpos) D D' → D' = D) ∧
      ¬ ∃ D' : P.Configuration (2 * m),
        PopulationProtocol.Reachable P (doubleRing hmpos) D D' ∧
          PopulationProtocol.IsSafe P (doubleRing hmpos) D' isLeader := by
  dsimp only
  let hmpos : m > 0 := by omega
  let D := doubleCoverConfig P hmpos C
  have htwo : HasTwoLeaderOutputs P isLeader D :=
    doubleCover_hasTwoLeaders P isLeader hmpos C hunique
  have hDfixed : ∀ e : Fin (2 * m),
      P.step (doubleRing hmpos) D e = D := by
    exact currentPair_doubleCover_every_step_eq P hm C hfixed
  refine ⟨htwo, hDfixed, ?_, ?_⟩
  · intro D' hreach
    exact currentPair_reachable_eq_of_every_step_eq
      P (doubleRing hmpos) D hDfixed hreach
  · rintro ⟨D', hreach, hsafe⟩
    have hD' := currentPair_reachable_eq_of_every_step_eq
      P (doubleRing hmpos) D hDfixed hreach
    subst D'
    exact hasTwoLeaders_not_unique P isLeader htwo hsafe.1

/-! ## Exact boundary: uncovered pairs are unconstrained -/

/-- A two-state local rule which is identity except on the ordered
leader/leader pair. -/
def missingLeaderPairTransition (l r : Bool) : Bool × Bool :=
  if l && r then (false, false) else (l, r)

def missingLeaderPairProtocol : PopulationProtocol where
  Q := Bool
  Y := Bool
  transition := missingLeaderPairTransition
  output := id

/-- On every nontrivial ring, every unique-leader configuration is fixed by
the missing-pair rule: no edge of such a configuration exposes two leaders. -/
theorem missingLeaderPair_unique_every_step_eq
    (ring : DirectedRing n) (hn : 1 < n)
    (C : missingLeaderPairProtocol.Configuration n)
    (hunique : UniqueLeaderOutput missingLeaderPairProtocol n C id) :
    ∀ e, missingLeaderPairProtocol.step ring C e = C := by
  obtain ⟨root, hroot, honly⟩ := hunique
  change C root = true at hroot
  change ∀ j, C j = true → j = root at honly
  intro e
  let j := ring.rightNeighbor e
  have hje : j ≠ e := rightNeighbor_ne_self_of_one_lt ring hn e
  have hnotBoth : ¬ (C e = true ∧ C j = true) := by
    rintro ⟨he, hj⟩
    exact hje ((honly j hj).trans (honly e he).symm)
  have hand : (C e && C j) = false := by
    cases he : C e <;> cases hj : C j <;> simp_all
  apply currentPair_step_eq_of_transition_eq
  simp [missingLeaderPairProtocol, missingLeaderPairTransition, j, hand]

/-- The all-leader word exposes precisely the pair absent from every
nontrivial unique-leader kernel and is not fixed by the same rule. -/
def missingLeaderPairAllLeaders
    (n : Nat) : missingLeaderPairProtocol.Configuration n :=
  fun _ => true

theorem missingLeaderPair_allLeaders_step_ne
    (ring : DirectedRing n) (e : Fin n) :
    missingLeaderPairProtocol.step ring
      (missingLeaderPairAllLeaders n) e ≠ missingLeaderPairAllLeaders n := by
  intro h
  have he := congrFun h e
  simp [PopulationProtocol.step, missingLeaderPairProtocol,
    missingLeaderPairTransition, missingLeaderPairAllLeaders] at he

/-! ## The factor-four dynamic sweep -/

/-- Seal every endpoint while preserving its complete physical state. -/
def sweepLockSealAll
    (C : SweepLockConfig n psi kappa tau) :
    SweepLockConfig n psi kappa tau :=
  fun i => ((C i).1, true)

@[simp] theorem sweepLockSealAll_phase
    (C : SweepLockConfig n psi kappa tau) (i : Fin n) :
    (sweepLockSealAll C i).2 = true := by
  rfl

@[simp] theorem sweepLockSealAll_leader
    (C : SweepLockConfig n psi kappa tau) (i : Fin n) :
    sweepLockLeader (sweepLockSealAll C i) = sweepLockLeader (C i) := by
  rfl

theorem sweepLockSealAll_output
    (hpsi : psi > 0) (kappa tau : Nat)
    (C : SweepLockConfig n psi kappa tau) (i : Fin n) :
    (P_partialSweepLockProtocol hpsi kappa tau).output
        (sweepLockSealAll C i) =
      (P_partialSweepLockProtocol hpsi kappa tau).output (C i) := by
  rfl

theorem sweepLockSealAll_allSealed
    (C : SweepLockConfig n psi kappa tau) :
    SweepLockAllSealed (sweepLockSealAll C) := by
  intro i
  rfl

/-- Sealing preserves every current leader output, hence preserves any chosen
pair of distinct leader positions. -/
theorem sweepLockSealAll_hasTwoLeaders
    (hpsi : psi > 0) (kappa tau : Nat)
    (C : SweepLockConfig n psi kappa tau)
    (htwo : HasTwoLeaderOutputs
      (P_partialSweepLockProtocol hpsi kappa tau) isLeaderOutput C) :
    HasTwoLeaderOutputs
      (P_partialSweepLockProtocol hpsi kappa tau) isLeaderOutput
      (sweepLockSealAll C) := by
  obtain ⟨i, j, hij, hi, hj⟩ := htwo
  refine ⟨i, j, hij, ?_, ?_⟩
  · rw [sweepLockSealAll_output hpsi kappa tau C i]
    exact hi
  · rw [sweepLockSealAll_output hpsi kappa tau C j]
    exact hj

/-- The actual factor-four rule satisfies the generic pairwise-identity
hypothesis on the complete sealed state class. -/
theorem sweepLock_currentPairIdentityOn_sealed
    (hpsi : psi > 0) (kappa tau : Nat) :
    CurrentPairIdentityOn
      (P_partialSweepLockProtocol hpsi kappa tau)
      (fun u => u.2 = true) := by
  intro l r hl hr
  exact P_partialSweepLock_eq_self_of_sealed
    hpsi kappa tau l r hl hr

/-- Every all-sealed configuration has singleton reachability.  No output or
leader-count assumption is used. -/
theorem sweepLock_allSealed_reachable_eq
    (hpsi : psi > 0) (kappa tau : Nat)
    (ring : DirectedRing n) (C : SweepLockConfig n psi kappa tau)
    (hsealed : SweepLockAllSealed C)
    {D : SweepLockConfig n psi kappa tau}
    (hreach : PopulationProtocol.Reachable
      (P_partialSweepLockProtocol hpsi kappa tau) ring C D) :
    D = C := by
  apply currentPair_reachable_eq_of_every_step_eq
    (P_partialSweepLockProtocol hpsi kappa tau) ring C
  · exact currentPair_every_step_eq_of_identityOn
      (P_partialSweepLockProtocol hpsi kappa tau)
      (fun u => u.2 = true)
      (sweepLock_currentPairIdentityOn_sealed hpsi kappa tau)
      ring C hsealed
  · exact hreach

/-- All-sealed configurations with at least two current leader outputs form a
closed bad trap. -/
def SweepLockSealedBad
    (hpsi : psi > 0) (kappa tau : Nat)
    (C : SweepLockConfig n psi kappa tau) : Prop :=
  SweepLockAllSealed C ∧
    HasTwoLeaderOutputs
      (P_partialSweepLockProtocol hpsi kappa tau) isLeaderOutput C

theorem sweepLockSealedBad_closed
    (hpsi : psi > 0) (kappa tau : Nat) (ring : DirectedRing n) :
    PopulationProtocol.ClosedPred
      (P_partialSweepLockProtocol hpsi kappa tau) ring
      (SweepLockSealedBad hpsi kappa tau) := by
  intro C hC D hstep
  obtain ⟨e, rfl⟩ := hstep
  rw [P_partialSweepLock_step_eq_of_allSealed
    hpsi kappa tau ring C hC.1 e]
  exact hC

theorem sweepLockSealedBad_not_unique
    (hpsi : psi > 0) (kappa tau : Nat)
    {C : SweepLockConfig n psi kappa tau}
    (hbad : SweepLockSealedBad hpsi kappa tau C) :
    ¬ UniqueLeaderOutput
      (P_partialSweepLockProtocol hpsi kappa tau) n C isLeaderOutput :=
  hasTwoLeaders_not_unique
    (P_partialSweepLockProtocol hpsi kappa tau) isLeaderOutput hbad.2

theorem sweepLockSealedBad_not_isSafe
    (hpsi : psi > 0) (kappa tau : Nat) (ring : DirectedRing n)
    {C : SweepLockConfig n psi kappa tau}
    (hbad : SweepLockSealedBad hpsi kappa tau C) :
    ¬ PopulationProtocol.IsSafe
      (P_partialSweepLockProtocol hpsi kappa tau) ring C isLeaderOutput := by
  intro hsafe
  exact sweepLockSealedBad_not_unique hpsi kappa tau hbad hsafe.1

/-- No execution from an all-sealed multi-leader trap can reach a safe
configuration. -/
theorem sweepLockSealedBad_cannot_reach_isSafe
    (hpsi : psi > 0) (kappa tau : Nat) (ring : DirectedRing n)
    {C : SweepLockConfig n psi kappa tau}
    (hbad : SweepLockSealedBad hpsi kappa tau C) :
    ¬ ∃ D : SweepLockConfig n psi kappa tau,
      PopulationProtocol.Reachable
          (P_partialSweepLockProtocol hpsi kappa tau) ring C D ∧
        PopulationProtocol.IsSafe
          (P_partialSweepLockProtocol hpsi kappa tau) ring D
          isLeaderOutput := by
  rintro ⟨D, hreach, hsafe⟩
  have hD := sweepLock_allSealed_reachable_eq
    hpsi kappa tau ring C hbad.1 hreach
  subst D
  exact sweepLockSealedBad_not_isSafe hpsi kappa tau ring hbad hsafe

/-- Strong parameterized counterfamily: for every `n ≥ 2`, sealing any
factor-four configuration that currently has at least two leader outputs
produces a closed singleton trap from which safety is unreachable. -/
theorem sweepLockSealAll_twoLeader_counterfamily
    (hpsi : psi > 0) (kappa tau : Nat) (hn : 2 ≤ n)
    (C : SweepLockConfig n psi kappa tau)
    (htwo : HasTwoLeaderOutputs
      (P_partialSweepLockProtocol hpsi kappa tau) isLeaderOutput C) :
    let ring : DirectedRing n := ⟨by omega⟩
    let D := sweepLockSealAll C
    SweepLockSealedBad hpsi kappa tau D ∧
      (∀ e : Fin n,
        (P_partialSweepLockProtocol hpsi kappa tau).step ring D e = D) ∧
      (∀ D' : SweepLockConfig n psi kappa tau,
        PopulationProtocol.Reachable
          (P_partialSweepLockProtocol hpsi kappa tau) ring D D' → D' = D) ∧
      ¬ ∃ D' : SweepLockConfig n psi kappa tau,
        PopulationProtocol.Reachable
            (P_partialSweepLockProtocol hpsi kappa tau) ring D D' ∧
          PopulationProtocol.IsSafe
            (P_partialSweepLockProtocol hpsi kappa tau) ring D'
            isLeaderOutput := by
  dsimp only
  let ring : DirectedRing n := ⟨by omega⟩
  let D := sweepLockSealAll C
  have hbad : SweepLockSealedBad hpsi kappa tau D :=
    ⟨sweepLockSealAll_allSealed C,
      sweepLockSealAll_hasTwoLeaders hpsi kappa tau C htwo⟩
  refine ⟨hbad, ?_, ?_, ?_⟩
  · exact P_partialSweepLock_step_eq_of_allSealed
      hpsi kappa tau ring D hbad.1
  · intro D' hreach
    exact sweepLock_allSealed_reachable_eq
      hpsi kappa tau ring D hbad.1 hreach
  · exact sweepLockSealedBad_cannot_reach_isSafe
      hpsi kappa tau ring hbad

/-! ## Explicit nonvacuous family at every size -/

private theorem sweepTrapHPsi : StalePsi > 0 := by
  decide

/-- A literal all-sealed, all-leader configuration on any population size. -/
def sweepLockAllLeaderConfig (n kappa tau : Nat) :
    SweepLockConfig n StalePsi kappa tau :=
  fun _ => ((staleLeaderPhysical kappa tau, true), true)

theorem sweepLockAllLeaderConfig_hasTwoLeaders
    (kappa tau : Nat) (hn : 2 ≤ n) :
    HasTwoLeaderOutputs
      (P_partialSweepLockProtocol sweepTrapHPsi kappa tau) isLeaderOutput
      (sweepLockAllLeaderConfig n kappa tau) := by
  let i : Fin n := ⟨0, by omega⟩
  let j : Fin n := ⟨1, by omega⟩
  refine ⟨i, j, ?_, ?_, ?_⟩
  · intro hij
    have hv := congrArg Fin.val hij
    change 0 = 1 at hv
    omega
  · rfl
  · rfl

/-- Fully explicit unbounded bad family, with no carried configuration or
leader-existence premise. -/
theorem sweepLockAllLeader_unbounded_counterfamily
    (n kappa tau : Nat) (hn : 2 ≤ n) :
    let ring : DirectedRing n := ⟨by omega⟩
    let C := sweepLockAllLeaderConfig n kappa tau
    SweepLockSealedBad sweepTrapHPsi kappa tau C ∧
      (∀ e : Fin n,
        (P_partialSweepLockProtocol sweepTrapHPsi kappa tau).step ring C e = C) ∧
      ¬ ∃ D : SweepLockConfig n StalePsi kappa tau,
        PopulationProtocol.Reachable
            (P_partialSweepLockProtocol sweepTrapHPsi kappa tau) ring C D ∧
          PopulationProtocol.IsSafe
            (P_partialSweepLockProtocol sweepTrapHPsi kappa tau) ring D
            isLeaderOutput := by
  dsimp only
  let ring : DirectedRing n := ⟨by omega⟩
  let C := sweepLockAllLeaderConfig n kappa tau
  have hbad : SweepLockSealedBad sweepTrapHPsi kappa tau C := by
    constructor
    · intro i
      rfl
    · exact sweepLockAllLeaderConfig_hasTwoLeaders kappa tau hn
  refine ⟨hbad, ?_, ?_⟩
  · exact P_partialSweepLock_step_eq_of_allSealed
      sweepTrapHPsi kappa tau ring C hbad.1
  · exact sweepLockSealedBad_cannot_reach_isSafe
      sweepTrapHPsi kappa tau ring hbad

end PPartialDynamicSweepCounterfamilySol
end PPLLCompleteMultiLeaderCleanup
