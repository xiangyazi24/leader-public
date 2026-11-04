import Leader.AAFJ.Centered.CoalescenceGlobal
import Leader.AAFJ.Centered.FixedBlockDescent
import Leader.AAFJ.Centered.TerminalRankOne

/-!
# Endpoint-retaining centered end-to-end stage composition

This module keeps the physical one-barrier endpoint of global coalescence and
provides a denominator-explicit finite-numerator bind.  A first stage with raw
horizon `T` and a continuation with raw horizon `U` is normalized by exactly
`n^(T+U)`.  Unused first-stage coordinates occur after the endpoint-dependent
continuation through `firstTerminalBindMass`.

The strict-rank cost theorem can already be attached to the retained global
endpoint.  The final sanitation stage still needs an endpoint-retaining
first-`Phi = 1` theorem; the public conditional consumer below states that
remaining premise as a uniform literal one-barrier continuation numerator.
-/

namespace AAFJPK
namespace CenteredRenewal
namespace EndToEndBind

open CoalescenceTrial
open CoalescenceGlobal
open BarrierAlgebra
open SingleBarrierSanitation
open CenteredFixedBlockDescent
open ComplexityConstants
open FiniteUniformStoppingTree
open PayloadFiniteStoppingTree
open FixedBlockStrongRankDescent
open TerminalRankOne
open RankBlockBind

set_option autoImplicit false

/-! ## Generic denominator-explicit endpoint bind -/

/-- Exact numerator for two consecutive stopped stages.  The first summand
charges every active first-stage interaction and appends all `U` continuation
coordinates.  The second starts the endpoint-dependent continuation at the
first successful terminal and puts unused first-stage coordinates after it. -/
def sequentialStageCostNumerator {A S F : Type} {n : Nat}
    (step : A -> Fin n -> PayloadNode A S F)
    (continuationCost : S -> Nat) (node : PayloadNode A S F)
    (T U : Nat) : Nat :=
  truncatedActiveCostNumerator (eraseStep step) node.erase T * n ^ U +
    firstTerminalBindMass step continuationCost node T

/-- A continuation bounded at denominator `n^U` remains bounded after the
first-terminal fold at the exact combined denominator `n^(T+U)`. -/
theorem firstTerminalBindMass_le_uniformContinuation
    {A S F : Type} {n U budget : Nat}
    (step : A -> Fin n -> PayloadNode A S F)
    (continuationCost : S -> Nat)
    (hcontinuation : forall endpoint,
      continuationCost endpoint <= n ^ U * budget) :
    forall (node : PayloadNode A S F) T,
      firstTerminalBindMass step continuationCost node T <=
        n ^ (T + U) * budget := by
  intro node T
  induction T generalizing node with
  | zero =>
      cases node with
      | active state => simp [firstTerminalBindMass]
      | failure endpoint => simp [firstTerminalBindMass]
      | success endpoint =>
          simpa [firstTerminalBindMass] using hcontinuation endpoint
  | succ T ih =>
      cases node with
      | failure endpoint => simp [firstTerminalBindMass]
      | success endpoint =>
          have hmul := Nat.mul_le_mul_left (n ^ (T + 1))
            (hcontinuation endpoint)
          simpa [firstTerminalBindMass, Nat.pow_add, Nat.mul_assoc] using hmul
      | active state =>
          simp only [firstTerminalBindMass]
          calc
            (List.ofFn (fun edge : Fin n =>
                firstTerminalBindMass step continuationCost
                  (step state edge) T)).sum <=
                (List.ofFn (fun _ : Fin n =>
                  n ^ (T + U) * budget)).sum :=
              ofFn_sum_le _ _ (fun edge => ih (step state edge))
            _ = n * (n ^ (T + U) * budget) :=
              ofFn_sum_const n _
            _ = n ^ ((T + 1) + U) * budget := by
              rw [show (T + 1) + U = (T + U) + 1 by omega,
                Nat.pow_succ]
              ac_rfl

/-- Additive stopped-stage composition with the two raw horizons visible in
both hypotheses and in the conclusion. -/
theorem sequentialStageCostNumerator_le_additiveBudgets
    {A S F : Type} {n T U firstBudget continuationBudget : Nat}
    (step : A -> Fin n -> PayloadNode A S F)
    (continuationCost : S -> Nat) (node : PayloadNode A S F)
    (hfirst : truncatedActiveCostNumerator (eraseStep step) node.erase T <=
      n ^ T * firstBudget)
    (hcontinuation : forall endpoint,
      continuationCost endpoint <= n ^ U * continuationBudget) :
    sequentialStageCostNumerator step continuationCost node T U <=
      n ^ (T + U) * (firstBudget + continuationBudget) := by
  have hfirstPadded := Nat.mul_le_mul_right (n ^ U) hfirst
  have hsecond := firstTerminalBindMass_le_uniformContinuation
    step continuationCost hcontinuation node T
  unfold sequentialStageCostNumerator
  calc
    truncatedActiveCostNumerator (eraseStep step) node.erase T * n ^ U +
        firstTerminalBindMass step continuationCost node T <=
      (n ^ T * firstBudget) * n ^ U +
        n ^ (T + U) * continuationBudget :=
      Nat.add_le_add hfirstPadded hsecond
    _ = n ^ (T + U) * (firstBudget + continuationBudget) := by
      rw [Nat.pow_add, Nat.mul_add]
      ac_rfl

/-! ## Generic state-dependent physical scheduler reindex -/

/-- A canonical proof state paired with the actual physical state whose view
it represents.  The relation is proof-relevant enough to transport active
children without reconstructing physical endpoints. -/
structure ReindexedStopState (P S : Type) (related : P -> S -> Prop) where
  physical : P
  canonical : S
  related_to_canonical : related physical canonical

/-- Forget the physical witness while preserving the stopped outcome. -/
def projectReindexedStopNode {P S : Type} {related : P -> S -> Prop} :
    StopNode (ReindexedStopState P S related) -> StopNode S
  | .active state => .active state.canonical
  | .success => .success
  | .failure => .failure

/-- Interpret each physical raw symbol through a state-dependent canonical
edge view, advancing the physical state in parallel whenever the canonical
machine remains active. -/
def reindexedStopStep {P S : Type} {n : Nat}
    (physicalStep : P -> Fin n -> P)
    (canonicalStep : S -> Fin n -> StopNode S)
    (edgeView : P -> Fin n -> Fin n) (related : P -> S -> Prop)
    (hactive : forall physical canonical,
      related physical canonical -> forall rawEdge next,
      canonicalStep canonical (edgeView physical rawEdge) = .active next ->
        related (physicalStep physical rawEdge) next) :
    ReindexedStopState P S related -> Fin n ->
      StopNode (ReindexedStopState P S related)
  | ⟨physical, canonical, hrelated⟩, rawEdge =>
      match hnode : canonicalStep canonical (edgeView physical rawEdge) with
      | .active next => .active
          ⟨physicalStep physical rawEdge, next,
            hactive physical canonical hrelated rawEdge next hnode⟩
      | .success => .success
      | .failure => .failure

theorem projectReindexedStopNode_step
    {P S : Type} {n : Nat}
    (physicalStep : P -> Fin n -> P)
    (canonicalStep : S -> Fin n -> StopNode S)
    (edgeView : P -> Fin n -> Fin n) (related : P -> S -> Prop)
    (hactive : forall physical canonical,
      related physical canonical -> forall rawEdge next,
      canonicalStep canonical (edgeView physical rawEdge) = .active next ->
        related (physicalStep physical rawEdge) next)
    (state : ReindexedStopState P S related) (rawEdge : Fin n) :
    projectReindexedStopNode
        (reindexedStopStep physicalStep canonicalStep edgeView related
          hactive state rawEdge) =
      canonicalStep state.canonical (edgeView state.physical rawEdge) := by
  rcases state with ⟨physical, canonical, hrelated⟩
  simp only [reindexedStopStep]
  split <;> simp_all [projectReindexedStopNode]

private theorem reindexListSum_eq_of_perm {xs ys : List Nat}
    (hperm : xs.Perm ys) : xs.sum = ys.sum := by
  induction hperm with
  | nil => rfl
  | cons _ _ ih => simp [ih]
  | swap => simpa [List.sum_cons] using Nat.add_left_comm ..
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

private theorem reindexNodup_ofFn_of_injective {n : Nat} {A : Type}
    (f : Fin n -> A) (hf : Function.Injective f) :
    (List.ofFn f).Nodup := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.ofFn_succ, List.nodup_cons]
      constructor
      · intro hmem
        rw [List.mem_ofFn] at hmem
        obtain ⟨i, hi⟩ := hmem
        have h := hf hi
        cases h
      · apply ih
        intro i j hij
        exact Fin.succ_inj.mp (hf hij)

/-- Exact finite uniform sums are invariant under an explicitly inverted
state-dependent edge view. -/
theorem ofFn_sum_reindex {n : Nat}
    (forward backward : Fin n -> Fin n)
    (hleft : forall edge, backward (forward edge) = edge)
    (hright : forall edge, forward (backward edge) = edge)
    (value : Fin n -> Nat) :
    (List.ofFn (fun edge => value (forward edge))).sum =
      (List.ofFn value).sum := by
  have hforwardInjective : Function.Injective forward := by
    intro x y hxy
    rw [← hleft x, ← hleft y, hxy]
  have hforwardNodup : (List.ofFn forward).Nodup :=
    reindexNodup_ofFn_of_injective forward hforwardInjective
  have hidNodup : (List.ofFn (fun edge : Fin n => edge)).Nodup :=
    reindexNodup_ofFn_of_injective (fun edge : Fin n => edge)
      (fun _ _ h => h)
  have hperm : (List.ofFn forward).Perm
      (List.ofFn (fun edge : Fin n => edge)) := by
    apply (List.perm_ext_iff_of_nodup hforwardNodup hidNodup).2
    intro edge
    constructor
    · intro _
      exact List.mem_ofFn.mpr ⟨edge, rfl⟩
    · intro _
      exact List.mem_ofFn.mpr ⟨backward edge, hright edge⟩
  have hmap := hperm.map value
  have hsum := reindexListSum_eq_of_perm hmap
  simpa [List.map_ofFn, Function.comp_def] using hsum

/-- State-dependent edge permutations preserve the complete truncated active
cost numerator, not only its expectation.  Thus the canonical proof tree and
the actual raw scheduler tree have identical multiplicity at every horizon. -/
theorem truncatedActiveCostNumerator_reindexedStopStep_eq
    {P S : Type} {n : Nat}
    (physicalStep : P -> Fin n -> P)
    (canonicalStep : S -> Fin n -> StopNode S)
    (edgeView edgeUnview : P -> Fin n -> Fin n)
    (hleft : forall physical edge,
      edgeUnview physical (edgeView physical edge) = edge)
    (hright : forall physical edge,
      edgeView physical (edgeUnview physical edge) = edge)
    (related : P -> S -> Prop)
    (hactive : forall physical canonical,
      related physical canonical -> forall rawEdge next,
      canonicalStep canonical (edgeView physical rawEdge) = .active next ->
        related (physicalStep physical rawEdge) next) :
    forall node T,
    truncatedActiveCostNumerator
        (reindexedStopStep physicalStep canonicalStep edgeView related hactive)
        node T =
      truncatedActiveCostNumerator canonicalStep
        (projectReindexedStopNode node) T := by
  intro node T
  induction T generalizing node with
  | zero => simp [truncatedActiveCostNumerator]
  | succ T ih =>
      cases node with
      | success => simp [truncatedActiveCostNumerator,
          projectReindexedStopNode]
      | failure => simp [truncatedActiveCostNumerator,
          projectReindexedStopNode]
      | active state =>
          simp only [truncatedActiveCostNumerator,
            projectReindexedStopNode]
          apply congrArg (n ^ (T + 1) + ·)
          calc
            (List.ofFn (fun rawEdge : Fin n =>
                truncatedActiveCostNumerator
                  (reindexedStopStep physicalStep canonicalStep edgeView
                    related hactive)
                  (reindexedStopStep physicalStep canonicalStep edgeView
                    related hactive state rawEdge) T)).sum =
                (List.ofFn (fun rawEdge : Fin n =>
                  truncatedActiveCostNumerator canonicalStep
                    (canonicalStep state.canonical
                      (edgeView state.physical rawEdge)) T)).sum := by
              apply ofFn_sum_eq
              intro rawEdge
              rw [ih]
              rw [projectReindexedStopNode_step]
            _ = (List.ofFn (fun canonicalEdge : Fin n =>
                truncatedActiveCostNumerator canonicalStep
                  (canonicalStep state.canonical canonicalEdge) T)).sum := by
              exact ofFn_sum_reindex
                (edgeView state.physical) (edgeUnview state.physical)
                (hleft state.physical) (hright state.physical)
                (fun canonicalEdge => truncatedActiveCostNumerator
                  canonicalStep
                  (canonicalStep state.canonical canonicalEdge) T)

/-! ## Payload-preserving global coalescence -/

/-- The global physical step with its one-barrier terminal payload retained. -/
noncomputable def globalPayloadStep {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (hn2 : 1 < n) (hndvd : ¬ k ∣ n) :
    GlobalActive hk ring hn2 -> Fin n ->
      PayloadNode (GlobalActive hk ring hn2)
        (OneBarrierEndpoint hk ring hn2) PEmpty :=
  fun state selected =>
    match globalStep hk ring hn2 hndvd state selected with
    | .active next => .active next
    | .oneBarrier endpoint => .success endpoint

/-- Erasing only the terminal payload recovers the exact global tree used by
the cubic coalescence Bellman theorem. -/
theorem eraseStep_globalPayloadStep {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (hn2 : 1 < n) (hndvd : ¬ k ∣ n) :
    eraseStep (globalPayloadStep hk ring hn2 hndvd) =
      globalErasedStep hk ring hn2 hndvd := by
  funext state selected
  unfold eraseStep globalPayloadStep globalErasedStep
  generalize hnode : globalStep hk ring hn2 hndvd state selected = node
  cases node <;> rfl

theorem globalPayloadStep_eq_success_iff {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (hn2 : 1 < n) (hndvd : ¬ k ∣ n)
    (state : GlobalActive hk ring hn2) (selected : Fin n)
    (endpoint : OneBarrierEndpoint hk ring hn2) :
    globalPayloadStep hk ring hn2 hndvd state selected = .success endpoint <->
      globalStep hk ring hn2 hndvd state selected = .oneBarrier endpoint := by
  unfold globalPayloadStep
  cases hstep : globalStep hk ring hn2 hndvd state selected with
  | active next => simp
  | oneBarrier actual => simp

/-- A retained success payload is the literal raw successor configuration. -/
theorem globalPayloadStep_success_config {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (hn2 : 1 < n) (hndvd : ¬ k ∣ n)
    (state : GlobalActive hk ring hn2) (selected : Fin n)
    (endpoint : OneBarrierEndpoint hk ring hn2)
    (hstep : globalPayloadStep hk ring hn2 hndvd state selected =
      .success endpoint) :
    endpoint.drop.config = rawStep hk ring state.config selected := by
  have hglobal := (globalPayloadStep_eq_success_iff hk ring hn2 hndvd
    state selected endpoint).mp hstep
  have hconfig := globalStep_config hk ring hn2 hndvd state selected
  rw [hglobal] at hconfig
  exact hconfig

/-- The cubic duration theorem is unchanged when its terminal endpoint is
retained rather than erased at the API boundary. -/
theorem canonical_global_payload_duration_le_three_cubic
    {n k M : Nat} (hk : 0 < k) (ring : DirectedRing n) (hn2 : 1 < n)
    (hndvd : ¬ k ∣ n) (hM2 : 2 <= M)
    (C : Config n k) (hcount : supportCount hk ring C = M) (T : Nat) :
    truncatedActiveCostNumerator
        (eraseStep (globalPayloadStep hk ring hn2 hndvd))
        (.active (GlobalActive.seed (hk := hk) (ring := ring) (hn2 := hn2)
          C M hM2 hcount)) T <=
      n ^ T * (3 * n ^ 3) := by
  rw [eraseStep_globalPayloadStep]
  have h := canonical_global_duration_le_three_cubic hk ring hn2 hndvd
    hM2 C hcount T
  simpa [Nat.mul_comm] using h

/-! ## The retained support-one payload is a literal one-barrier state -/

/-- Select the unique physical barrier from a configuration whose charged
support count is one. -/
noncomputable def countOneBarrier {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (C : Config n k)
    (hcount : supportCount hk ring C = 1) : Fin n :=
  Classical.choose (exists_barrier_of_barrierCount_eq_one hk ring C (by
    simpa [supportCount] using hcount))

theorem countOneBarrier_spec {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (C : Config n k)
    (hcount : supportCount hk ring C = 1) :
    BarrierAt hk ring (labelsOf C) (countOneBarrier hk ring C hcount) := by
  exact Classical.choose_spec
    (exists_barrier_of_barrierCount_eq_one hk ring C (by
      simpa [supportCount] using hcount))

/-- Cardinality one makes the selected barrier the exact unique-barrier
witness needed by the cut-rank process. -/
theorem countOneBarrier_oneBarrierAt {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (C : Config n k)
    (hcount : supportCount hk ring C = 1) :
    OneBarrierAt hk ring C (countOneBarrier hk ring C hcount) := by
  let support := barrierSupport hk ring (labelsOf C)
  have hlength : support.length = 1 := by
    simpa [support, supportCount, barrierCount] using hcount
  obtain ⟨only, honly⟩ := List.length_eq_one_iff.mp hlength
  intro edge
  constructor
  · intro hedge
    have hedgeMem : edge ∈ support := by
      exact (mem_barrierSupport_iff hk ring (labelsOf C) edge).2 hedge
    have hchosenMem : countOneBarrier hk ring C hcount ∈ support := by
      exact (mem_barrierSupport_iff hk ring (labelsOf C)
        (countOneBarrier hk ring C hcount)).2
        (countOneBarrier_spec hk ring C hcount)
    rw [honly] at hedgeMem hchosenMem
    simp only [List.mem_singleton] at hedgeMem hchosenMem
    exact hedgeMem.trans hchosenMem.symm
  · intro hedge
    subst edge
    exact countOneBarrier_spec hk ring C hcount

/-- Reify any physical support-one configuration as the exact literal state
consumed by fixed-block rank descent. -/
noncomputable def literalStateOfSupportCountOne {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (C : Config n k)
    (hcount : supportCount hk ring C = 1) : LiteralState hk ring where
  config := C
  barrier := countOneBarrier hk ring C hcount
  oneBarrier := countOneBarrier_oneBarrierAt hk ring C hcount

theorem oneBarrierEndpoint_supportCount_eq_one
    {n k : Nat} {hk : 0 < k} {ring : DirectedRing n} {hn2 : 1 < n}
    (endpoint : OneBarrierEndpoint hk ring hn2) :
    supportCount hk ring endpoint.drop.config = 1 := by
  simpa [SupportDropEndpoint.level] using endpoint.count_eq_one

/-- Exact conversion of the retained global endpoint; only its barrier
witness is chosen, while the physical configuration is definitionally
unchanged. -/
noncomputable def oneBarrierEndpointToLiteralState
    {n k : Nat} {hk : 0 < k} {ring : DirectedRing n} {hn2 : 1 < n}
    (endpoint : OneBarrierEndpoint hk ring hn2) : LiteralState hk ring :=
  literalStateOfSupportCountOne hk ring endpoint.drop.config
    (oneBarrierEndpoint_supportCount_eq_one endpoint)

@[simp] theorem oneBarrierEndpointToLiteralState_config
    {n k : Nat} {hk : 0 < k} {ring : DirectedRing n} {hn2 : 1 < n}
    (endpoint : OneBarrierEndpoint hk ring hn2) :
    (oneBarrierEndpointToLiteralState endpoint).config =
      endpoint.drop.config := rfl

/-! ## Coalescence followed by the proved strict-rank cost -/

/-- Block-rounded strict-rank cost started from the exact retained global
endpoint.  Its `J` block choices have raw scheduler denominator
`(n^H)^J = n^(H*J)`. -/
noncomputable def endpointRankDescentCost
    {n k : Nat} {hk : 0 < k} {ring : DirectedRing n} {hn2 : 1 < n}
    (hn3 : 3 <= n) (hndvd : ¬ k ∣ n)
    (endpoint : OneBarrierEndpoint hk ring hn2) (J : Nat) : Nat :=
  truncatedRoundedCostNumerator
    (literalStep hn3 hndvd) literalExcessRank (rankBlockHorizon n)
    (oneBarrierEndpointToLiteralState endpoint) J

theorem blockDenominator_eq_rawHorizon (n H J : Nat) :
    (n ^ H) ^ J = n ^ (H * J) := by
  exact (Nat.pow_mul n H J).symm

theorem endpointRankDescentCost_le
    {n k : Nat} {hk : 0 < k} {ring : DirectedRing n} {hn2 : 1 < n}
    (hn3 : 3 <= n) (hndvd : ¬ k ∣ n)
    (endpoint : OneBarrierEndpoint hk ring hn2) (J : Nat) :
    endpointRankDescentCost hn3 hndvd endpoint J <=
      n ^ (rankBlockHorizon n * J) * rankDescentBudget n := by
  rw [← blockDenominator_eq_rawHorizon]
  exact centeredPaddedRankDescent_truncatedCost_le_publishedBudget
    hk ring hn3 hndvd (oneBarrierEndpointToLiteralState endpoint) J

/-- Exact coalescence-plus-rank-descent numerator.  The two horizons remain
separate arguments of the generic bind and combine only in its denominator. -/
noncomputable def canonicalGlobalThenRankDescentNumerator
    {n k M : Nat} (hk : 0 < k) (ring : DirectedRing n) (hn3 : 3 <= n)
    (hndvd : ¬ k ∣ n) (hM2 : 2 <= M)
    (C : Config n k) (hcount : supportCount hk ring C = M)
    (T J : Nat) : Nat :=
  sequentialStageCostNumerator (globalPayloadStep hk ring (by omega) hndvd)
    (fun endpoint => endpointRankDescentCost hn3 hndvd endpoint J)
    (.active (GlobalActive.seed (hk := hk) (ring := ring) (hn2 := by omega)
      C M hM2 hcount)) T (rankBlockHorizon n * J)

/-- The physically connected coalescence and strict-rank phases have the
additive normalized budget `3*n^3 + rankDescentBudget n`. -/
theorem canonicalGlobalThenRankDescentNumerator_le
    {n k M : Nat} (hk : 0 < k) (ring : DirectedRing n) (hn3 : 3 <= n)
    (hndvd : ¬ k ∣ n) (hM2 : 2 <= M)
    (C : Config n k) (hcount : supportCount hk ring C = M)
    (T J : Nat) :
    canonicalGlobalThenRankDescentNumerator hk ring hn3 hndvd hM2
        C hcount T J <=
      n ^ (T + rankBlockHorizon n * J) *
        (3 * n ^ 3 + rankDescentBudget n) := by
  apply sequentialStageCostNumerator_le_additiveBudgets
  · exact canonical_global_payload_duration_le_three_cubic
      hk ring (by omega) hndvd hM2 C hcount T
  · intro endpoint
    exact endpointRankDescentCost_le hn3 hndvd endpoint J

/-! ## Exact consumer seam for the still-missing terminal endpoint bind -/

/-- Conditional all-state numerator after a multi-barrier start.  The sole
remaining semantic premise is a continuation numerator on every literal
one-barrier endpoint, normalized at the explicitly supplied raw horizon `U`.
It must include both strict-rank descent and final `Phi = 1` sanitation. -/
theorem canonicalGlobalThenOneBarrierContinuation_le_allStateBudget
    {n k M U : Nat} (hk : 0 < k) (ring : DirectedRing n) (hn3 : 3 <= n)
    (hndvd : ¬ k ∣ n) (hM2 : 2 <= M)
    (C : Config n k) (hcount : supportCount hk ring C = M)
    (continuationCost : LiteralState hk ring -> Nat)
    (hcontinuation : forall state,
      continuationCost state <= n ^ U * oneBarrierBudget n)
    (T : Nat) :
    sequentialStageCostNumerator (globalPayloadStep hk ring (by omega) hndvd)
        (fun endpoint => continuationCost
          (oneBarrierEndpointToLiteralState endpoint))
        (.active (GlobalActive.seed (hk := hk) (ring := ring)
          (hn2 := by omega) C M hM2 hcount)) T U <=
      n ^ (T + U) * allStateBudget n := by
  simpa [allStateBudget] using
    sequentialStageCostNumerator_le_additiveBudgets
      (globalPayloadStep hk ring (by omega) hndvd)
      (fun endpoint => continuationCost
        (oneBarrierEndpointToLiteralState endpoint))
      (.active (GlobalActive.seed (hk := hk) (ring := ring)
        (hn2 := by omega) C M hM2 hcount))
      (canonical_global_payload_duration_le_three_cubic
        hk ring (by omega) hndvd hM2 C hcount T)
      (fun endpoint => hcontinuation
        (oneBarrierEndpointToLiteralState endpoint))

theorem canonicalGlobalThenOneBarrierContinuation_le_540_cube
    {n k M U : Nat} (hk : 0 < k) (ring : DirectedRing n) (hn3 : 3 <= n)
    (hndvd : ¬ k ∣ n) (hM2 : 2 <= M)
    (C : Config n k) (hcount : supportCount hk ring C = M)
    (continuationCost : LiteralState hk ring -> Nat)
    (hcontinuation : forall state,
      continuationCost state <= n ^ U * oneBarrierBudget n)
    (T : Nat) :
    sequentialStageCostNumerator (globalPayloadStep hk ring (by omega) hndvd)
        (fun endpoint => continuationCost
          (oneBarrierEndpointToLiteralState endpoint))
        (.active (GlobalActive.seed (hk := hk) (ring := ring)
          (hn2 := by omega) C M hM2 hcount)) T U <=
      n ^ (T + U) * (540 * n ^ 3) := by
  exact Nat.le_trans
    (canonicalGlobalThenOneBarrierContinuation_le_allStateBudget
      hk ring hn3 hndvd hM2 C hcount continuationCost hcontinuation T)
    (Nat.mul_le_mul_left (n ^ (T + U))
      (allStateBudget_le_540_cube n hn3))

/-! ## Arbitrary initial support: direct one-barrier or coalescence -/

theorem supportCount_pos_of_not_dvd
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (hndvd : ¬ k ∣ n) (C : Config n k) :
    0 < supportCount hk ring C := by
  simpa [supportCount] using
    barrierCount_pos_of_not_dvd hk ring C hndvd

/-- Exact all-state two-stage numerator.  A support-one input starts the
one-barrier continuation immediately and places the unused `T` coalescence
coordinates after it.  Only support at least two runs the global payload tree. -/
noncomputable def allStateSequentialCostNumerator
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n) (hn3 : 3 <= n)
    (hndvd : ¬ k ∣ n) (C : Config n k)
    (continuationCost : LiteralState hk ring -> Nat) (T U : Nat) : Nat :=
  let M := supportCount hk ring C
  if hM1 : M = 1 then
    continuationCost (literalStateOfSupportCountOne hk ring C hM1) * n ^ T
  else
    have hMpos : 0 < M := supportCount_pos_of_not_dvd hk ring hndvd C
    have hM2 : 2 <= M := by omega
    sequentialStageCostNumerator
      (globalPayloadStep hk ring (by omega) hndvd)
      (fun endpoint => continuationCost
        (oneBarrierEndpointToLiteralState endpoint))
      (.active (GlobalActive.seed (hk := hk) (ring := ring)
        (hn2 := by omega) C M hM2 rfl)) T U

/-- Fully arbitrary centered initial configuration, conditional only on the
literal one-barrier continuation estimate.  The support-one branch and the
support-at-least-two branch use the same combined raw denominator. -/
theorem allStateSequentialCostNumerator_le_allStateBudget
    {n k U : Nat} (hk : 0 < k) (ring : DirectedRing n) (hn3 : 3 <= n)
    (hndvd : ¬ k ∣ n) (C : Config n k)
    (continuationCost : LiteralState hk ring -> Nat)
    (hcontinuation : forall state,
      continuationCost state <= n ^ U * oneBarrierBudget n)
    (T : Nat) :
    allStateSequentialCostNumerator hk ring hn3 hndvd C
        continuationCost T U <=
      n ^ (T + U) * allStateBudget n := by
  let M := supportCount hk ring C
  by_cases hM1 : M = 1
  · have hcost := hcontinuation
      (literalStateOfSupportCountOne hk ring C hM1)
    have hpadded := Nat.mul_le_mul_right (n ^ T) hcost
    calc
      allStateSequentialCostNumerator hk ring hn3 hndvd C
          continuationCost T U =
          continuationCost
            (literalStateOfSupportCountOne hk ring C hM1) * n ^ T := by
        simp [allStateSequentialCostNumerator, M, hM1]
      _ <= (n ^ U * oneBarrierBudget n) * n ^ T := hpadded
      _ = n ^ (T + U) * oneBarrierBudget n := by
        rw [Nat.pow_add]
        ac_rfl
      _ <= n ^ (T + U) * allStateBudget n :=
        Nat.mul_le_mul_left _ (by
          simp [allStateBudget])
  · have hMpos : 0 < M := supportCount_pos_of_not_dvd hk ring hndvd C
    have hM2 : 2 <= M := by omega
    rw [show allStateSequentialCostNumerator hk ring hn3 hndvd C
          continuationCost T U =
        sequentialStageCostNumerator
          (globalPayloadStep hk ring (by omega) hndvd)
          (fun endpoint => continuationCost
            (oneBarrierEndpointToLiteralState endpoint))
          (.active (GlobalActive.seed (hk := hk) (ring := ring)
            (hn2 := by omega) C M hM2 rfl)) T U by
      simp [allStateSequentialCostNumerator, M, hM1]]
    exact canonicalGlobalThenOneBarrierContinuation_le_allStateBudget
      hk ring hn3 hndvd hM2 C rfl continuationCost hcontinuation T

theorem allStateSequentialCostNumerator_le_540_cube
    {n k U : Nat} (hk : 0 < k) (ring : DirectedRing n) (hn3 : 3 <= n)
    (hndvd : ¬ k ∣ n) (C : Config n k)
    (continuationCost : LiteralState hk ring -> Nat)
    (hcontinuation : forall state,
      continuationCost state <= n ^ U * oneBarrierBudget n)
    (T : Nat) :
    allStateSequentialCostNumerator hk ring hn3 hndvd C
        continuationCost T U <=
      n ^ (T + U) * (540 * n ^ 3) := by
  exact Nat.le_trans
    (allStateSequentialCostNumerator_le_allStateBudget
      hk ring hn3 hndvd C continuationCost hcontinuation T)
    (Nat.mul_le_mul_left (n ^ (T + U))
      (allStateBudget_le_540_cube n hn3))

/-- Consumer variant spelling out the two still-to-be-connected one-barrier
budgets separately.  A future endpoint-retaining rank-to-terminal fold should
discharge exactly this premise, at one common raw horizon `U`. -/
theorem allStateSequentialCostNumerator_le_540_cube_of_rankTerminalBudgets
    {n k U : Nat} (hk : 0 < k) (ring : DirectedRing n) (hn3 : 3 <= n)
    (hndvd : ¬ k ∣ n) (C : Config n k)
    (rankThenTerminalCost : LiteralState hk ring -> Nat)
    (hrankTerminal : forall state,
      rankThenTerminalCost state <=
        n ^ U * (rankDescentBudget n + terminalBudget n))
    (T : Nat) :
    allStateSequentialCostNumerator hk ring hn3 hndvd C
        rankThenTerminalCost T U <=
      n ^ (T + U) * (540 * n ^ 3) := by
  apply allStateSequentialCostNumerator_le_540_cube
    hk ring hn3 hndvd C rankThenTerminalCost
  intro state
  simpa [oneBarrierBudget_eq_rankDescent_add_terminal] using
    hrankTerminal state

/-! ## Endpoint-retaining strict-rank-to-terminal block bind -/

/-! ### Exact literal-to-canonical terminal seam -/

/-- Vanishing excess rank is literally `Phi = 1`, not merely an abstract
zero-rank marker. -/
theorem literalExcessRank_zero_phi_one
    {n k : Nat} {hk : 0 < k} {ring : DirectedRing n}
    (state : LiteralState hk ring) (hzero : literalExcessRank state = 0) :
    literalPhiRank state = 1 := by
  have hone := literalPhiRank_one_le state
  simp only [literalExcessRank] at hzero
  omega

/-- The exact cut view of a physical rank-zero literal endpoint is valid
input to the canonical terminal rank-one process. -/
theorem literalRankOneCut
    {n k : Nat} {hk : 0 < k} {ring : DirectedRing n}
    (state : LiteralState hk ring) (hzero : literalExcessRank state = 0) :
    RankOneCut hk ring (cutView ring state.barrier state.config) := by
  exact
    { canonical := canonicalOneBarrier_cutView hk ring state.config
        state.barrier state.oneBarrier
      phiOne := by
        change literalPhiRank state = 1
        exact literalExcessRank_zero_phi_one state hzero }

/-- Initial canonical terminal node attached to the actual physical endpoint.
No configuration is reconstructed: its carrier is the endpoint's cut view. -/
noncomputable def literalTerminalInitialNode
    {n k : Nat} {hk : 0 < k} {ring : DirectedRing n}
    (state : LiteralState hk ring) (hzero : literalExcessRank state = 0) :
    StopNode (TerminalState hk ring) :=
  initialNode (cutView ring state.barrier state.config)
    (literalRankOneCut state hzero)

/-- The terminal Bellman potential starts within the published terminal
budget at every actual rank-zero endpoint. -/
theorem literalTerminalInitialNode_potential_le_terminalBudget
    {n k : Nat} {hk : 0 < k} {ring : DirectedRing n}
    (hn3 : 3 <= n) (state : LiteralState hk ring)
    (hzero : literalExcessRank state = 0) :
    terminalPotential (literalTerminalInitialNode state hzero) <=
      terminalBudget n := by
  exact Nat.le_trans
    (initialNode_potential_le_dirtyBudget hn3
      (cutView ring state.barrier state.config)
      (literalRankOneCut state hzero))
    (dirtyBudget_le_terminalBudget n)

/-- One physical raw edge and the state-dependent canonical edge describe the
same successor cut view.  This is the coordinate transport required by any
terminal stopping tree; the canonical edge is not the same `Fin n` numeral in
general. -/
theorem literalStep_cutView_eq_cutSuccessor
    {n k : Nat} {hk : 0 < k} {ring : DirectedRing n}
    (hn3 : 3 <= n) (hndvd : ¬ k ∣ n)
    (state : LiteralState hk ring) (rawEdge : Fin n) :
    cutView ring (literalStep hn3 hndvd state rawEdge).barrier
        (literalStep hn3 hndvd state rawEdge).config =
      Rank.cutSuccessor hk ring (cutView ring state.barrier state.config)
        (cutCoord ring state.barrier rawEdge) := by
  exact (cutSuccessor_cutView_at_cutCoord hk ring state.config
    state.barrier rawEdge).symm

/-- Total canonical terminal numerator on literal states.  It is zero away
from the terminal lane and otherwise starts from the exact cut view of the
physical endpoint.  This definition is the numerical consumer of the
terminal Bellman theorem; a separate reindex theorem connects it to raw
physical scheduler words. -/
noncomputable def literalTerminalCanonicalCostNumerator
    {n k : Nat} {hk : 0 < k} {ring : DirectedRing n}
    (terminalStep : TerminalState hk ring -> Fin n ->
      StopNode (TerminalState hk ring))
    (state : LiteralState hk ring) (U : Nat) : Nat :=
  if hzero : literalExcessRank state = 0 then
    truncatedActiveCostNumerator terminalStep
      (literalTerminalInitialNode state hzero) U
  else 0

/-- A scale-one terminal Bellman supersolution discharges the exact uniform
continuation premise required by the rank-zero block bind. -/
theorem literalTerminalCanonicalCostNumerator_le
    {n k U : Nat} {hk : 0 < k} {ring : DirectedRing n}
    (hn3 : 3 <= n)
    (terminalStep : TerminalState hk ring -> Fin n ->
      StopNode (TerminalState hk ring))
    (hsuper : NatBellmanSuperSolution terminalStep 1 terminalPotential)
    (state : LiteralState hk ring) (hzero : literalExcessRank state = 0) :
    literalTerminalCanonicalCostNumerator terminalStep state U <=
      n ^ U * terminalBudget n := by
  simp only [literalTerminalCanonicalCostNumerator, hzero, dite_true]
  have hcost := truncatedActiveCostNumerator_mul_le_of_natSuperSolution
    terminalStep 1 terminalPotential hsuper
    (literalTerminalInitialNode state hzero) U
  simp only [Nat.one_mul] at hcost
  exact Nat.le_trans hcost
    (Nat.mul_le_mul_left (n ^ U)
      (literalTerminalInitialNode_potential_le_terminalBudget hn3 state hzero))

private theorem sum_map_le_length_mul {A : Type} (xs : List A)
    (value : A -> Nat) (bound : Nat)
    (hvalue : forall x, x ∈ xs -> value x <= bound) :
    (xs.map value).sum <= xs.length * bound := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      have hx := hvalue x (by simp)
      have htail : forall y, y ∈ xs -> value y <= bound := by
        intro y hy
        exact hvalue y (by simp [hy])
      simp only [List.map_cons, List.sum_cons, List.length_cons,
        Nat.succ_mul]
      calc
        value x + (xs.map value).sum <=
            bound + xs.length * bound := Nat.add_le_add hx (ih htail)
        _ = xs.length * bound + bound := Nat.add_comm _ _

/-- Endpoint-weighted first-zero fold over exact raw scheduler blocks.  A
rank-zero endpoint starts its continuation immediately.  Whole unused block
coordinates are appended only after that continuation. -/
def firstRankZeroBlockBindMass {S : Type} {n : Nat}
    (step : S -> Fin n -> S) (rank : S -> Nat) (H : Nat)
    (continuationCost : S -> Nat) : S -> Nat -> Nat
  | state, 0 =>
      if rank state = 0 then continuationCost state else 0
  | state, J + 1 =>
      if rank state = 0 then
        (n ^ H) ^ (J + 1) * continuationCost state
      else
        ((allSchedules n H).map (fun word =>
          firstRankZeroBlockBindMass step rank H continuationCost
            (runWord step state word) J)).sum

/-- A uniform terminal estimate at denominator `n^U` survives the block-level
first-zero fold at exactly denominator `n^(H*J+U)`. -/
theorem firstRankZeroBlockBindMass_le_uniformContinuation
    {S : Type} {n H U terminalBudget : Nat}
    (step : S -> Fin n -> S) (rank : S -> Nat)
    (continuationCost : S -> Nat)
    (hcontinuation : forall state, rank state = 0 ->
      continuationCost state <= n ^ U * terminalBudget) :
    forall state J,
    firstRankZeroBlockBindMass step rank H continuationCost state J <=
      n ^ (H * J + U) * terminalBudget := by
  intro state J
  induction J generalizing state with
  | zero =>
      by_cases hzero : rank state = 0
      · simpa [firstRankZeroBlockBindMass, hzero] using
          hcontinuation state hzero
      · simp [firstRankZeroBlockBindMass, hzero]
  | succ J ih =>
      by_cases hzero : rank state = 0
      · have hmul := Nat.mul_le_mul_left ((n ^ H) ^ (J + 1))
          (hcontinuation state hzero)
        simp only [firstRankZeroBlockBindMass, hzero, if_pos]
        calc
          (n ^ H) ^ (J + 1) * continuationCost state <=
              (n ^ H) ^ (J + 1) *
                (n ^ U * terminalBudget) := hmul
          _ = n ^ (H * (J + 1) + U) * terminalBudget := by
            simp only [blockDenominator_eq_rawHorizon, Nat.mul_succ,
              Nat.pow_add]
            ac_rfl
      · simp only [firstRankZeroBlockBindMass, hzero, if_false]
        have hsum := sum_map_le_length_mul (allSchedules n H)
          (fun word => firstRankZeroBlockBindMass step rank H
            continuationCost (runWord step state word) J)
          (n ^ (H * J + U) * terminalBudget)
          (fun word _ => ih (runWord step state word))
        rw [allSchedules_length] at hsum
        calc
          ((allSchedules n H).map (fun word =>
              firstRankZeroBlockBindMass step rank H continuationCost
                (runWord step state word) J)).sum <=
              n ^ H * (n ^ (H * J + U) * terminalBudget) := hsum
          _ = n ^ (H * (J + 1) + U) * terminalBudget := by
            simp only [Nat.mul_succ, Nat.pow_add]
            ac_rfl

/-- Total rank-descent cost plus the endpoint-dependent terminal continuation
cost, both expanded to the same exact raw denominator. -/
def rankThenTerminalCostNumerator {S : Type} {n : Nat}
    (step : S -> Fin n -> S) (rank : S -> Nat) (H : Nat)
    (terminalCost : S -> Nat) (state : S) (J U : Nat) : Nat :=
  truncatedRoundedCostNumerator step rank H state J * n ^ U +
    firstRankZeroBlockBindMass step rank H terminalCost state J

theorem rankThenTerminalCostNumerator_le_additiveBudgets
    {S : Type} {n H J U rankBudget terminalBudget : Nat}
    (step : S -> Fin n -> S) (rank : S -> Nat)
    (terminalCost : S -> Nat) (state : S)
    (hrank : truncatedRoundedCostNumerator step rank H state J <=
      (n ^ H) ^ J * rankBudget)
    (hterminal : forall endpoint, rank endpoint = 0 ->
      terminalCost endpoint <= n ^ U * terminalBudget) :
    rankThenTerminalCostNumerator step rank H terminalCost state J U <=
      n ^ (H * J + U) * (rankBudget + terminalBudget) := by
  have hrankPadded := Nat.mul_le_mul_right (n ^ U) hrank
  have hterminalBind :
      firstRankZeroBlockBindMass step rank H terminalCost state J <=
        n ^ (H * J + U) * terminalBudget :=
    firstRankZeroBlockBindMass_le_uniformContinuation
      (H := H) step rank terminalCost hterminal state J
  unfold rankThenTerminalCostNumerator
  calc
    truncatedRoundedCostNumerator step rank H state J * n ^ U +
        firstRankZeroBlockBindMass step rank H terminalCost state J <=
      ((n ^ H) ^ J * rankBudget) * n ^ U +
        n ^ (H * J + U) * terminalBudget :=
      Nat.add_le_add hrankPadded hterminalBind
    _ = n ^ (H * J + U) * (rankBudget + terminalBudget) := by
      rw [blockDenominator_eq_rawHorizon, Nat.pow_add, Nat.mul_add]
      ac_rfl

/-- Centered specialization: strict-rank descent is fully discharged; only a
terminal numerator on actual `Phi = 1` literal endpoints remains a premise. -/
noncomputable def centeredRankThenTerminalCostNumerator
    {n k : Nat} {hk : 0 < k} {ring : DirectedRing n}
    (hn3 : 3 <= n) (hndvd : ¬ k ∣ n)
    (terminalCost : LiteralState hk ring -> Nat)
    (state : LiteralState hk ring) (J U : Nat) : Nat :=
  rankThenTerminalCostNumerator (literalStep hn3 hndvd) literalExcessRank
    (rankBlockHorizon n) terminalCost state J U

theorem centeredRankThenTerminalCostNumerator_le
    {n k U : Nat} {hk : 0 < k} {ring : DirectedRing n}
    (hn3 : 3 <= n) (hndvd : ¬ k ∣ n)
    (terminalCost : LiteralState hk ring -> Nat)
    (hterminal : forall state, literalExcessRank state = 0 ->
      terminalCost state <= n ^ U * terminalBudget n)
    (state : LiteralState hk ring) (J : Nat) :
    centeredRankThenTerminalCostNumerator hn3 hndvd terminalCost state J U <=
      n ^ (rankBlockHorizon n * J + U) *
        (rankDescentBudget n + terminalBudget n) := by
  apply rankThenTerminalCostNumerator_le_additiveBudgets
  · exact centeredPaddedRankDescent_truncatedCost_le_publishedBudget
      hk ring hn3 hndvd state J
  · exact hterminal

/-- All centered initial configurations now compose through coalescence and
strict-rank descent.  Discharging `hterminal` with the rank-one Bellman process
will make this theorem unconditional. -/
theorem allStateEndToEndCostNumerator_le_540_cube_of_terminalCost
    {n k U : Nat} (hk : 0 < k) (ring : DirectedRing n) (hn3 : 3 <= n)
    (hndvd : ¬ k ∣ n) (C : Config n k)
    (terminalCost : LiteralState hk ring -> Nat)
    (hterminal : forall state, literalExcessRank state = 0 ->
      terminalCost state <= n ^ U * terminalBudget n)
    (T J : Nat) :
    allStateSequentialCostNumerator hk ring hn3 hndvd C
        (fun state => centeredRankThenTerminalCostNumerator
          hn3 hndvd terminalCost state J U)
        T (rankBlockHorizon n * J + U) <=
      n ^ (T + (rankBlockHorizon n * J + U)) * (540 * n ^ 3) := by
  apply allStateSequentialCostNumerator_le_540_cube_of_rankTerminalBudgets
    hk ring hn3 hndvd C
  intro state
  exact centeredRankThenTerminalCostNumerator_le
    hn3 hndvd terminalCost hterminal state J

/-- Numerical all-state composition obtained from a concrete canonical
terminal stopped process.  Its raw physical interpretation is supplied by the
state-dependent cut-coordinate reindex theorem below the terminal producer;
the denominator itself is already the exact raw horizon sum. -/
noncomputable def allStateEndToEndCanonicalCostNumerator
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n) (hn3 : 3 <= n)
    (hndvd : ¬ k ∣ n) (C : Config n k)
    (terminalStep : TerminalState hk ring -> Fin n ->
      StopNode (TerminalState hk ring))
    (T J U : Nat) : Nat :=
  allStateSequentialCostNumerator hk ring hn3 hndvd C
    (fun state => centeredRankThenTerminalCostNumerator hn3 hndvd
      (fun endpoint =>
        literalTerminalCanonicalCostNumerator terminalStep endpoint U)
      state J U)
    T (rankBlockHorizon n * J + U)

/-- Exact consumer of the forthcoming terminal Bellman theorem: global
coalescence, strict-rank descent, and rank-one cleanup have total normalized
budget at most `540*n^3` for every triple of finite horizons. -/
theorem allStateEndToEndCanonicalCostNumerator_le_540_cube
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n) (hn3 : 3 <= n)
    (hndvd : ¬ k ∣ n) (C : Config n k)
    (terminalStep : TerminalState hk ring -> Fin n ->
      StopNode (TerminalState hk ring))
    (hsuper : NatBellmanSuperSolution terminalStep 1 terminalPotential)
    (T J U : Nat) :
    allStateEndToEndCanonicalCostNumerator hk ring hn3 hndvd C
        terminalStep T J U <=
      n ^ (T + (rankBlockHorizon n * J + U)) * (540 * n ^ 3) := by
  unfold allStateEndToEndCanonicalCostNumerator
  apply allStateEndToEndCostNumerator_le_540_cube_of_terminalCost
    hk ring hn3 hndvd C
  intro state hzero
  exact literalTerminalCanonicalCostNumerator_le
    hn3 terminalStep hsuper state hzero

end EndToEndBind
end CenteredRenewal
end AAFJPK
