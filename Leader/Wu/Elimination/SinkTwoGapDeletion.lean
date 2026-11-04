import Leader.Wu.Elimination.SinkTwoGapVictimProtection
import Leader.Wu.Elimination.SinkTwoGapStageCells
import Leader.Core.PredictableSerialRace
import Leader.Core.UniformBlockRenewalCost

open FiniteUniformStoppingTree
open LDSinkTwoGapNoResetKernel LDSinkTwoGapEntrance
open LDSinkGapCleanup LDTwoGapFrame PPLLRepair
open PredictableRenewalOverlap
open LDSinkTwoGapEntranceBellman

namespace LDSinkTwoGapDeletion

set_option autoImplicit false

noncomputable section

variable {n ψ : Nat}

/-! ## The actual domain of the available attempt laws -/

/-- Attempt2 supplies both raw rank facts on its invariant subtype.
This theorem deliberately does not extend their quantifiers to all AState. -/
theorem attempt2_raw_rank_on_invariant
    (hψ : ψ > 0) (F : TwoGapFrame n) (x : AState n ψ)
    (hi : AInvariant hψ F x) :
    (∀ e : Fin n,
      rawStoppedR F (attemptStepRaw hψ F x e) ≤ R F x) ∧
    (∃ e : Fin n,
      rawStoppedR F (attemptStepRaw hψ F x e) < R F x) := by
  constructor
  · intro e
    exact raw_nonincrease hψ F ⟨x, hi⟩ e
  · exact raw_strictDrop hψ F ⟨x, hi⟩

/-- The complete supplied absorption chain, on its justified domain. -/
theorem absorption_drop_on_invariant
    (hψ : ψ > 0) (F : TwoGapFrame n) (x : AState n ψ)
    (e : Fin n) (hi : AInvariant hψ F x)
    (hf : attemptStepRaw hψ F x e = .failure) :
    R F (advanceAState F x (attemptStepConf hψ F x e)) < R F x := by
  exact entranceAbsorptionResidual_of_blocked hψ F x e
    (blocked_of_invariant_failure hψ F
      (blockedProtectionResidual hψ F) x e hi hf)
    hi.attack hf

/-- UNDISCHARGED DOMAIN EXTENSION.
The existing EntranceAbsorptionResidual is quantified over every raw AState.
The checked blocked/protection chain proves its field on AInvariant only.
This hypothesis is precisely the remaining complementary domain; it is not
claimed to follow from AttemptLaws or from subtype continuation closure. -/
def AbsorptionOutsideInvariant
    (hψ : ψ > 0) (F : TwoGapFrame n) : Prop :=
  ∀ (x : AState n ψ) (e : Fin n),
    ¬ AInvariant hψ F x →
    attemptStepRaw hψ F x e = .failure →
    R F (advanceAState F x (attemptStepConf hψ F x e)) < R F x

/-- Assemble the global absorption record without discarding its domain. -/
theorem absorptionResidual_assembled
    (hψ : ψ > 0) (F : TwoGapFrame n)
    (hOutside : AbsorptionOutsideInvariant hψ F) :
    EntranceAbsorptionResidual hψ F := by
  classical
  refine ⟨?_⟩
  intro x e hf
  by_cases hi : AInvariant hψ F x
  · exact absorption_drop_on_invariant hψ F x e hi hf
  · exact hOutside x e hi hf

/-- CONDITIONAL GLOBAL BELLMAN ASSEMBLY.
`hRaw` is the existing global RawAttemptRankLaws record, retained as a named
hypothesis. The subtype theorem above is not a producer of that record.
`hOutside` is separately necessary for the supplied global absorption API.
Neither hypothesis is asserted here to hold on arbitrary malformed states. -/
theorem entranceBellman_assembled
    (hψ : ψ > 0) (F : TwoGapFrame n)
    (hRaw : RawAttemptRankLaws hψ F)
    (hOutside : AbsorptionOutsideInvariant hψ F) :
    EntranceBellman hψ F := by
  exact entranceBellman_of_raw_rank_laws hψ F hRaw
    (absorptionResidual_assembled hψ F hOutside)

/-! ## Exact success-count calculus -/

private theorem count_success {S : Type}
    (step : S → Fin n → StopNode S) (T : Nat) :
    successCount step .success T = n ^ T := by
  simp only [successCount, treeWeight_success, successWeight, Nat.mul_one]

private theorem count_failure {S : Type}
    (step : S → Fin n → StopNode S) (T : Nat) :
    successCount step .failure T = 0 := by
  simp only [successCount, treeWeight_failure, successWeight, Nat.mul_zero]

private theorem n_mul_count_le_succ {S : Type}
    (step : S → Fin n → StopNode S) :
    ∀ (z : StopNode S) (T : Nat),
      n * successCount step z T ≤ successCount step z (T + 1) := by
  intro z T
  induction T generalizing z with
  | zero =>
      cases z with
      | active s =>
          change 0 ≤ successCount step (.active s) 1
          exact Nat.zero_le _
      | failure =>
          change 0 ≤ successCount step (.failure : StopNode S) 1
          exact Nat.zero_le _
      | success =>
          simp only [count_success, Nat.pow_zero, Nat.pow_one, Nat.mul_one, Nat.zero_add]
          exact Nat.le_refl _
  | succ T ih =>
      change
        n * (List.ofFn (fun e : Fin n =>
          successCount step (stepNode step z e) T)).sum ≤
        (List.ofFn (fun e : Fin n =>
          successCount step (stepNode step z e) (T + 1))).sum
      rw [← ofFn_sum_mul_left]
      exact ofFn_sum_le _ _ (fun e => ih (stepNode step z e))

/-- Pad successful scheduler words with arbitrary further raw edges. -/
theorem successCount_padding {S : Type}
    (step : S → Fin n → StopNode S) (z : StopNode S) (U K : Nat) :
    n ^ K * successCount step z U ≤ successCount step z (U + K) := by
  induction K with
  | zero => simp
  | succ K ih =>
      calc
        n ^ (K + 1) * successCount step z U =
            n * (n ^ K * successCount step z U) := by
          rw [Nat.pow_succ]
          ac_rfl
        _ ≤ n * successCount step z (U + K) :=
          Nat.mul_le_mul_left n ih
        _ ≤ successCount step z ((U + K) + 1) :=
          n_mul_count_le_succ step z (U + K)
        _ = successCount step z (U + (K + 1)) := by
          rw [Nat.add_assoc]

private theorem mass_padding {S : Type}
    (step : S → Fin n → StopNode S) (z : StopNode S)
    (L H c : Nat)
    (hm : n ^ L ≤ c * successCount step z L) :
    n ^ L * n ^ H ≤ c * successCount step z (H + L) := by
  calc
    n ^ L * n ^ H = n ^ H * n ^ L := Nat.mul_comm _ _
    _ ≤ n ^ H * (c * successCount step z L) :=
      Nat.mul_le_mul_left (n ^ H) hm
    _ = c * (n ^ H * successCount step z L) := by ac_rfl
    _ ≤ c * successCount step z (L + H) :=
      Nat.mul_le_mul_left c (successCount_padding step z L H)
    _ = c * successCount step z (H + L) := by
      rw [Nat.add_comm L H]

/-! ## An explicit eager entrance-then-race transition -/

/-- Embed a race node, preserving both terminal classifications. -/
def inRace {E Q : Type} : StopNode Q → StopNode (Sum E Q)
  | .active q => .active (.inr q)
  | .success => .success
  | .failure => .failure

/-- One raw edge is used exactly once. An entrance success either stops
immediately or hands its post-state to the race on that same interaction.
The first race edge is the next raw interaction, not an extra handoff edge.
This is a one-attempt process: a race failure is still terminal failure. -/
def sequentialStep {E Q : Type}
    (entrance : E → Fin n → StopNode E)
    (race : Q → Fin n → StopNode Q)
    (handoff : E → Fin n → StopNode Q) :
    Sum E Q → Fin n → StopNode (Sum E Q)
  | .inl x, e =>
      match entrance x e with
      | .active y => .active (.inl y)
      | .success => inRace (handoff x e)
      | .failure => .failure
  | .inr q, e => inRace (race q e)

private theorem sequential_race_node {E Q : Type}
    (entrance : E → Fin n → StopNode E)
    (race : Q → Fin n → StopNode Q)
    (handoff : E → Fin n → StopNode Q)
    (z : StopNode Q) (e : Fin n) :
    stepNode (sequentialStep entrance race handoff) (inRace (E := E) z) e =
      inRace (E := E) (stepNode race z e) := by
  cases z <;> rfl

/-- Once in the race, the composed process has exactly the race's tree. -/
theorem sequential_race_count {E Q : Type}
    (entrance : E → Fin n → StopNode E)
    (race : Q → Fin n → StopNode Q)
    (handoff : E → Fin n → StopNode Q) :
    ∀ (z : StopNode Q) (T : Nat),
      successCount (sequentialStep entrance race handoff)
        (inRace (E := E) z) T = successCount race z T := by
  intro z T
  induction T generalizing z with
  | zero => cases z <;> rfl
  | succ T ih =>
      change
        (List.ofFn (fun e : Fin n =>
          successCount (sequentialStep entrance race handoff)
            (stepNode (sequentialStep entrance race handoff)
              (inRace (E := E) z) e) T)).sum =
        (List.ofFn (fun e : Fin n =>
          successCount race (stepNode race z e) T)).sum
      apply ofFn_sum_eq
      intro e
      rw [sequential_race_node]
      exact ih (stepNode race z e)

/-- First-handoff induction. Each successful entrance prefix receives an
L-edge race guarantee. Earlier handoffs are handled by absorbing-success
padding, so the race need not wait until the entrance horizon H. -/
theorem sequential_success_lower {E Q : Type}
    (entrance : E → Fin n → StopNode E)
    (race : Q → Fin n → StopNode Q)
    (handoff : E → Fin n → StopNode Q) (L c : Nat)
    (hHandoff : ∀ x e, entrance x e = .success →
      n ^ L ≤ c * successCount race (handoff x e) L) :
    ∀ (x : E) (H : Nat),
      n ^ L * successCount entrance (.active x) H ≤
        c * successCount (sequentialStep entrance race handoff)
          (.active (.inl x)) (H + L) := by
  intro x H
  induction H generalizing x with
  | zero =>
      change 0 ≤ c * successCount (sequentialStep entrance race handoff)
        (.active (.inl x)) (0 + L)
      exact Nat.zero_le _
  | succ H ih =>
      have hpoint : ∀ e : Fin n,
          n ^ L * successCount entrance (entrance x e) H ≤
            c * successCount (sequentialStep entrance race handoff)
              (sequentialStep entrance race handoff (.inl x) e) (H + L) := by
        intro e
        cases he : entrance x e with
        | active y =>
            simpa only [sequentialStep, he] using ih y
        | failure =>
            simp only [count_failure, Nat.mul_zero] <;>
              exact Nat.zero_le _
        | success =>
            have hp := mass_padding race (handoff x e) L H c
              (hHandoff x e he)
            simpa only [sequentialStep, he, count_success,
              sequential_race_count] using hp
      have hs := ofFn_sum_le _ _ hpoint
      rw [ofFn_sum_mul_left, ofFn_sum_mul_left] at hs
      have ht : (H + 1) + L = (H + L) + 1 := by omega
      rw [ht]
      exact hs

/-- Multiplication of the two scheduler-mass bounds, proved for the actual
sequential transition above. There is no assumed composition inequality. -/
theorem sequential_mass {E Q : Type}
    (entrance : E → Fin n → StopNode E)
    (race : Q → Fin n → StopNode Q)
    (handoff : E → Fin n → StopNode Q)
    (x : E) (H L p c : Nat)
    (hEntrance : n ^ H ≤ p * successCount entrance (.active x) H)
    (hHandoff : ∀ y e, entrance y e = .success →
      n ^ L ≤ c * successCount race (handoff y e) L) :
    n ^ (H + L) ≤
      (p * c) * successCount (sequentialStep entrance race handoff)
        (.active (.inl x)) (H + L) := by
  calc
    n ^ (H + L) = n ^ L * n ^ H := by
      rw [Nat.pow_add]
      ac_rfl
    _ ≤ n ^ L * (p * successCount entrance (.active x) H) :=
      Nat.mul_le_mul_left (n ^ L) hEntrance
    _ = p * (n ^ L * successCount entrance (.active x) H) := by
      ac_rfl
    _ ≤ p * (c * successCount (sequentialStep entrance race handoff)
        (.active (.inl x)) (H + L)) :=
      Nat.mul_le_mul_left p
        (sequential_success_lower entrance race handoff L c hHandoff x H)
    _ = (p * c) * successCount (sequentialStep entrance race handoff)
        (.active (.inl x)) (H + L) := by
      ac_rfl

/-! ## Instantiate the checked abstract serial race -/

/-- Recover the active-state type from a transition's type. This avoids
redeclaring or guessing the imported serial-race state type. -/
abbrev ActiveStateOf {S : Type} (_step : S → Fin n → StopNode S) : Type := S

/-- The data and distinct-edge premises of the already-proved serial race.
This package contains no new success-count assumption. -/
structure SerialData (n : Nat) where
  A : Type
  B : Type
  firstGood : A → Fin n
  firstBad : A → Fin n
  nextA : A → Fin n → A
  advance : A → B
  secondGood : B → Fin n
  secondBad : B → Fin n
  nextB : B → Fin n → B
  first_ne : ∀ a, firstGood a ≠ firstBad a
  second_ne : ∀ b, secondGood b ≠ secondBad b

def SerialData.step (D : SerialData n) :=
  serialRaceStep D.firstGood D.firstBad D.nextA D.advance
    D.secondGood D.secondBad D.nextB

abbrev SerialData.State (D : SerialData n) : Type :=
  ActiveStateOf D.step

def SerialData.start (D : SerialData n) (a : D.A) : D.State :=
  .first a

theorem SerialData.mass (D : SerialData n) (a : D.A) :
    n ^ (4 * n) ≤
      16 * successCount D.step (.active (D.start a)) (4 * n) := by
  exact serialRace_two_quarters_sixteenth_by_four_mul
    D.firstGood D.firstBad D.nextA D.advance
    D.secondGood D.secondBad D.nextB D.first_ne D.second_ne a

abbrev CompositeState (D : SerialData n) (ψ : Nat) : Type :=
  Sum (AState n ψ) D.State

/-- The total payload function is consulted only at a successful entrance.
An already-deleted tagged leader is not sent through an unnecessary race.
For the other successful branch, entrance_success_raceReady below supplies
the physical RaceReady fact. Relating its payload to real edges remains part
of ConcreteDeletionInterface; arbitrary SerialData alone does not do so. -/
def raceHandoff (hψ : ψ > 0) (F : TwoGapFrame n) (D : SerialData n)
    (ready : AState n ψ → Fin n → D.A)
    (x : AState n ψ) (e : Fin n) : StopNode D.State := by
  classical
  exact if NoResetSuccess F (attemptStepConf hψ F x e) then .success
    else .active (D.start (ready x e))

def fullStep (hψ : ψ > 0) (F : TwoGapFrame n) (D : SerialData n)
    (ready : AState n ψ → Fin n → D.A) :
    CompositeState D ψ → Fin n → StopNode (CompositeState D ψ) :=
  sequentialStep (entranceStep hψ F) D.step (raceHandoff hψ F D ready)

/-- A non-deletion entrance success really has the physical race entrance. -/
theorem entrance_success_raceReady
    (hψ : ψ > 0) (F : TwoGapFrame n) (x : AState n ψ) (e : Fin n)
    (he : entranceStep hψ F x e = .success)
    (hd : ¬ NoResetSuccess F (attemptStepConf hψ F x e)) :
    RaceReady F (attemptStepConf hψ F x e) := by
  have hh := (entranceStep_eq_success_iff hψ F x e).mp he
  change RaceReady F (attemptStepConf hψ F x e) ∨
    NoResetSuccess F (attemptStepConf hψ F x e) at hh
  rcases hh with hr | hs
  · exact hr
  · exact (hd hs).elim

private theorem raceHandoff_mass
    (hψ : ψ > 0) (F : TwoGapFrame n) (D : SerialData n)
    (ready : AState n ψ → Fin n → D.A) (x : AState n ψ) (e : Fin n) :
    n ^ (4 * n) ≤
      16 * successCount D.step (raceHandoff hψ F D ready x e) (4 * n) := by
  classical
  unfold raceHandoff
  split
  · rw [count_success]
    simpa only [Nat.one_mul] using
      (Nat.mul_le_mul_right (n ^ (4 * n)) (by decide : 1 ≤ 16))
  · exact D.mass (ready x e)

/-- The requested composed one-attempt mass, with H = 32*n*(a+b).
This is unconditional with respect to the abstract serial race after its
stated distinct-edge premises, but retains the entrance Bellman hypothesis.
It is not yet a claim that an arbitrary serial race implements K2. -/
theorem entrance_then_serial_mass
    (hψ : ψ > 0) (F : TwoGapFrame n) (D : SerialData n)
    (ready : AState n ψ → Fin n → D.A)
    (hSuper : EntranceBellman hψ F)
    (x : AState n ψ)
    (hrec : GapInvariant hψ F.recovery x.conf)
    (hatt : GapInvariant hψ F.attack x.conf) :
    n ^ (32 * n * (F.recovery.d + F.attack.d) + 4 * n) ≤
      32 * successCount (fullStep hψ F D ready) (.active (.inl x))
        (32 * n * (F.recovery.d + F.attack.d) + 4 * n) := by
  exact sequential_mass (entranceStep hψ F) D.step
    (raceHandoff hψ F D ready) x
    (32 * n * (F.recovery.d + F.attack.d)) (4 * n) 2 16
    (entrance_success_half hψ F hSuper x hrec hatt)
    (fun y e _ => raceHandoff_mass hψ F D ready y e)

/-! ## Concrete simulation and the separate renewal requirement -/

/-- A same-raw-edge forward simulation that can discard source failures.
The terminal field preserves successful leaves; the step field uses the
identical scheduler edge, so no resampling or extra physical time is hidden. -/
structure SuccessSimulation {U V : Type}
    (source : U → Fin n → StopNode U)
    (target : V → Fin n → StopNode V)
    (Rel : StopNode U → StopNode V → Prop) : Prop where
  terminal : ∀ u v, Rel u v → successWeight u ≤ successWeight v
  next : ∀ u v, Rel u v → ∀ e : Fin n,
    Rel (stepNode source u e) (stepNode target v e)

/-- Prove the scheduler-count consequence of the local simulation fields. -/
theorem successCount_le_of_simulation {U V : Type}
    (source : U → Fin n → StopNode U)
    (target : V → Fin n → StopNode V)
    (Rel : StopNode U → StopNode V → Prop)
    (hSim : SuccessSimulation source target Rel)
    (u : StopNode U) (v : StopNode V) (hRel : Rel u v) (T : Nat) :
    successCount source u T ≤ successCount target v T := by
  induction T generalizing u v with
  | zero => exact hSim.terminal u v hRel
  | succ T ih =>
      change
        (List.ofFn (fun e : Fin n =>
          successCount source (stepNode source u e) T)).sum ≤
        (List.ofFn (fun e : Fin n =>
          successCount target (stepNode target v e) T)).sum
      exact ofFn_sum_le _ _
        (fun e => ih _ _ (hSim.next u v hRel e))

/-- Generic nonterminal failure wrapper. `restart s e` must be the actual
post-configuration with any justified ghost update, not a free physical reset.
The wrapper by itself makes no claim about the renewal success probability. -/
def retryStep {S : Type} (step : S → Fin n → StopNode S)
    (restart : S → Fin n → S) (s : S) (e : Fin n) : StopNode S :=
  match step s e with
  | .failure => .active (restart s e)
  | z => z

/-- Failure is not absorbing when the explicit retry wrapper is used. -/
theorem retryStep_ne_failure {S : Type}
    (step : S → Fin n → StopNode S) (restart : S → Fin n → S)
    (s : S) (e : Fin n) : retryStep step restart s e ≠ .failure := by
  cases h : step s e <;> simp [retryStep, h]

/-- UNDISCHARGED UNIFORM RESTART COVERAGE.
Every active block state, not merely the initial one, must admit a related
entrance state satisfying both gap invariants. S can be a proved closed
reachable subtype. This is certificate reinitialization at the same raw time;
it does not authorize resetting the physical configuration. -/
def UniformEntranceStarts {S : Type}
    (hψ : ψ > 0) (F : TwoGapFrame n) (D : SerialData n)
    (Rel : StopNode (CompositeState D ψ) → StopNode S → Prop) : Prop :=
  ∀ s : S, ∃ x : AState n ψ,
    GapInvariant hψ F.recovery x.conf ∧
    GapInvariant hψ F.attack x.conf ∧
    Rel (.active (.inl x)) (.active s)

/-- UNDISCHARGED CONCRETE INSTANTIATION AND RENEWAL INTERFACE.
No instance of this structure is claimed for K2 in this file. Its simulation
connects the physical victim/return edges and the entrance handoff to the
abstract serial race. Its restart field covers intermediate race states as
well as entrance states. Its physical fields make terminal success imply a
real tagged deletion, and prevent free configuration resets on failed races.
There is no probability, composed-mass, or expected-cost field. -/
structure ConcreteDeletionInterface {S : Type}
    (hψ : ψ > 0) (F : TwoGapFrame n) (D : SerialData n)
    (ready : AState n ψ → Fin n → D.A)
    (blockStep : S → Fin n → StopNode S) where
  /-- Same-edge relation between the virtual attempt and physical block. -/
  rel : StopNode (CompositeState D ψ) → StopNode S → Prop
  /-- Missing concrete entrance/race simulation, stated locally. -/
  simulation : SuccessSimulation (fullStep hψ F D ready) blockStep rel
  /-- Uniform coverage required by the all-active-state block theorem. -/
  restart : UniformEntranceStarts hψ F D rel
  /-- Failed races continue. For retryStep use retryStep_ne_failure. -/
  noFailure : ∀ s e, blockStep s e ≠ .failure
  /-- Forget ghost state and retain the actual ring configuration. -/
  observe : S → AState n ψ
  /-- Every active successor is produced by exactly the selected K2 edge. -/
  physical_active : ∀ s e t, blockStep s e = .active t →
    (observe t).conf = attemptStepConf hψ F (observe s) e
  /-- Success is justified by an actual physical deletion on that edge. -/
  physical_success : ∀ s e, blockStep s e = .success →
    NoResetSuccess F (attemptStepConf hψ F (observe s) e)
  /-- The positional identity needed to identify the two gaps' three tags. -/
  shared : F.recovery.pos F.recovery.d = F.attack.pos 0

/-- Transfer the proved composed mass to every physical block state.
The transfer uses a one-step simulation, not an assumed count inequality. -/
theorem two_gap_block_mass {S : Type}
    (hψ : ψ > 0) (F : TwoGapFrame n) (D : SerialData n)
    (ready : AState n ψ → Fin n → D.A)
    (blockStep : S → Fin n → StopNode S)
    (hRaw : RawAttemptRankLaws hψ F)
    (hOutside : AbsorptionOutsideInvariant hψ F)
    (I : ConcreteDeletionInterface hψ F D ready blockStep) (s : S) :
    n ^ (32 * n * (F.recovery.d + F.attack.d) + 4 * n) ≤
      32 * successCount blockStep (.active s)
        (32 * n * (F.recovery.d + F.attack.d) + 4 * n) := by
  obtain ⟨x, hrec, hatt, hRel⟩ := I.restart s
  have hm := entrance_then_serial_mass hψ F D ready
    (entranceBellman_assembled hψ F hRaw hOutside) x hrec hatt
  have hc := successCount_le_of_simulation
    (fullStep hψ F D ready) blockStep I.rel I.simulation
    (.active (.inl x)) (.active s) hRel
    (32 * n * (F.recovery.d + F.attack.d) + 4 * n)
  exact Nat.le_trans hm (Nat.mul_le_mul_left 32 hc)

/-- The requested exact finite-horizon cost bound, conditional on the named
raw-domain extensions and the concrete simulation/renewal interface.
The block theorem is instantiated with q = 1, K = H + 4*n, and q' = 32.
Its all-state mass premise is proved above; its no-failure premise is explicit.
With physical realization, this stopping cost bounds time to tagged deletion;
no real-valued expectation or limit theorem is asserted by this Nat statement. -/
theorem two_gap_deletion_cost {S : Type}
    (hψ : ψ > 0) (F : TwoGapFrame n) (D : SerialData n)
    (ready : AState n ψ → Fin n → D.A)
    (blockStep : S → Fin n → StopNode S)
    (hRaw : RawAttemptRankLaws hψ F)
    (hOutside : AbsorptionOutsideInvariant hψ F)
    (I : ConcreteDeletionInterface hψ F D ready blockStep)
    (x : S) (T : Nat) :
    truncatedActiveCostNumerator blockStep (.active x) T ≤
      n ^ T * (2 * 32 *
        (32 * n * (F.recovery.d + F.attack.d) + 4 * n)) := by
  have hblock : ∀ s : S,
      n ^ (1 * (32 * n * (F.recovery.d + F.attack.d) + 4 * n)) ≤
        32 * successCount blockStep (.active s)
          (1 * (32 * n * (F.recovery.d + F.attack.d) + 4 * n)) := by
    intro s
    simpa only [Nat.one_mul] using
      (two_gap_block_mass hψ F D ready blockStep hRaw hOutside I s)
  have hc := UniformBlockRenewalCost.truncatedActiveCostNumerator_block_le
    (n := n) (q := 1)
    (K := 32 * n * (F.recovery.d + F.attack.d) + 4 * n) (q' := 32)
    blockStep (by decide) I.noFailure hblock x T
  simpa only [Nat.one_mul] using hc

/-- Under the physical fields of the same interface, a successful block edge
really deletes one of the three tagged leaders. This distinguishes physical
deletion from merely reaching RaceReady or winning an unrelated abstract race. -/
theorem block_success_deletes_one_of_three {S : Type}
    (hψ : ψ > 0) (F : TwoGapFrame n) (D : SerialData n)
    (ready : AState n ψ → Fin n → D.A)
    (blockStep : S → Fin n → StopNode S)
    (I : ConcreteDeletionInterface hψ F D ready blockStep)
    (s : S) (e : Fin n) (hs : blockStep s e = .success) :
    ((attemptStepConf hψ F (I.observe s) e)
      (F.recovery.pos 0)).leader = false ∨
    ((attemptStepConf hψ F (I.observe s) e)
      (F.attack.pos 0)).leader = false ∨
    ((attemptStepConf hψ F (I.observe s) e)
      (F.attack.pos F.attack.d)).leader = false := by
  exact (success2_covers_three F
    (attemptStepConf hψ F (I.observe s) e) I.shared).mp
      (I.physical_success s e hs)

#print axioms attempt2_raw_rank_on_invariant
#print axioms absorption_drop_on_invariant
#print axioms absorptionResidual_assembled
#print axioms entranceBellman_assembled
#print axioms successCount_padding
#print axioms sequential_race_count
#print axioms sequential_success_lower
#print axioms sequential_mass
#print axioms SerialData.mass
#print axioms entrance_success_raceReady
#print axioms entrance_then_serial_mass
#print axioms successCount_le_of_simulation
#print axioms retryStep_ne_failure
#print axioms two_gap_block_mass
#print axioms two_gap_deletion_cost
#print axioms block_success_deletes_one_of_three

end

end LDSinkTwoGapDeletion
