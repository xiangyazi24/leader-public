import Leader.Wu.Elimination.GapClosure
import Leader.Wu.RaceEntrance.ArrivalRaceMass

/-!
# A label-independent elimination component on the existing finite carrier

This is a new local row. It executes the actual `sinkKernelC` at modulus one
on `K2OutputSafety.signalView`, then writes only leader, shield, bullet and
signal_B into each old physical endpoint. Every other legacy and controller
field stays at its own old endpoint. No state field, scheduler symbol,
population-size parameter, or physical observer phase is added.

The exact observation commutes on every input. In particular this row need
not agree with the existing K2 row across incompatible physical labels. The
results below certify this elimination component; domain entry, birth rows,
and an assembled dispatcher are separate obligations.
-/

namespace LabelFreeElimination

open StateBoundUnifiedCell LDSinkBoundedKernel LDSinkGapCleanup LDSinkProtectedAbsorption
open LDSinkKernelC K2OutputSafety LDTwoGapFrame LDSinkTwoGapNoResetKernel
open LDSinkTwoGapDeletionWired LDSinkTwoGapReachInvariant LDSinkTwoGapEntrance
open FiniteUniformStoppingTree PPLLResearchFormulation
open PPLLNoCheckBirthConditionTwoPhysical PPLLNoCheckBirthOutputLegitimacy

set_option autoImplicit false

variable {ψ κ n : Nat}

/-- The existing four-field signal observation of one actual finite cell. -/
def observeCell (q : UCell ψ κ) : AgentState 1 := signalView q.legacy.erase

/-- Observe the physical configuration without altering it. -/
def observe (C : Fin n → UCell ψ κ) : Fin n → AgentState 1 :=
  fun i => observeCell (C i)

/-- Write exactly four signal fields, retaining every other field from q. -/
def putSignals (q : UCell ψ κ) (v : AgentState 1) : UCell ψ κ :=
  { q with legacy := { q.legacy with
      leader := v.leader, shield := v.shield, bullet := v.bullet,
      signal_B := v.signal_B } }

/-- New label-independent elimination row. Positivity retains the physical
parameter convention; execution only reads the existing four signal fields. -/
def eliminationRow (_hψ : 0 < ψ) (l r : UCell ψ κ) : UCell ψ κ × UCell ψ κ :=
  let q := sinkKernelC (by decide) (observeCell l) (observeCell r)
  (putSignals l q.1, putSignals r q.2)

@[simp] theorem signalView_idempotent (q : AgentState ψ) :
    signalView (signalView q) = signalView q := rfl

@[simp] theorem observe_putSignals (q : UCell ψ κ) (v : AgentState 1) :
    observeCell (putSignals q v) = signalView v := rfl

@[simp] theorem putSignals_twice (q : UCell ψ κ) (u v : AgentState 1) :
    putSignals (putSignals q u) v = putSignals q v := rfl

@[simp] theorem putSignals_self (q : UCell ψ κ) :
    putSignals q (observeCell q) = q := by
  cases q with
  | mk legacy control => cases legacy <;> rfl

/-- Restoring the four old signal fields restores the entire old cell.
This characterizes exact framing of all other fields, including all paths,
counts, label bits and every controller/traffic field. -/
theorem putSignals_restore (q : UCell ψ κ) (v : AgentState 1) :
    putSignals (putSignals q v) (observeCell q) = q := by
  cases q with
  | mk legacy control => cases legacy <;> rfl

/-- The modulus-one K2 output of normalized inputs is itself normalized.
This follows from the existing physical signal-kernel theorem, whose label
compatibility side condition is automatic at modulus one. -/
theorem shadow_kernel_normal (l r : UCell ψ κ) :
    (signalView (sinkKernelC (by decide) (observeCell l) (observeCell r)).1,
      signalView (sinkKernelC (by decide) (observeCell l) (observeCell r)).2) =
      sinkKernelC (by decide) (observeCell l) (observeCell r) := by
  have h := signal_kernel (by decide : 0 < 1) (observeCell l) (observeCell r)
    (Or.inl (Subsingleton.elim _ _))
  change (signalView (sinkKernelC (by decide) (observeCell l) (observeCell r)).1,
    signalView (sinkKernelC (by decide) (observeCell l) (observeCell r)).2) =
    sinkKernelC (by decide) (signalView (observeCell l)) (signalView (observeCell r)) at h
  exact h

/-- Exact single-row commutation on every local state, without assumptions
about physical labels, paths, counts, controller coherence or reachability. -/
theorem observe_row (hψ : 0 < ψ) (l r : UCell ψ κ) :
    (observeCell (eliminationRow hψ l r).1,
      observeCell (eliminationRow hψ l r).2) =
      sinkKernelC (by decide) (observeCell l) (observeCell r) := by
  exact shadow_kernel_normal l r

/-- Both complete non-signal payloads remain at their original endpoints. -/
theorem row_frame (hψ : 0 < ψ) (l r : UCell ψ κ) :
    putSignals (eliminationRow hψ l r).1 (observeCell l) = l ∧
      putSignals (eliminationRow hψ l r).2 (observeCell r) = r := by
  exact ⟨putSignals_restore l _, putSignals_restore r _⟩

/-- In particular the physical labels and complete controllers are framed. -/
theorem row_labels_control (hψ : 0 < ψ) (l r : UCell ψ κ) :
    (eliminationRow hψ l r).1.legacy.label = l.legacy.label ∧
    (eliminationRow hψ l r).2.legacy.label = r.legacy.label ∧
    (eliminationRow hψ l r).1.control = l.control ∧
    (eliminationRow hψ l r).2.control = r.control := ⟨rfl, rfl, rfl, rfl⟩

/-- Package the new local row with the existing physical leader output. -/
def protocol (hψ : 0 < ψ) (κ : Nat) : PopulationProtocol where
  Q := UCell ψ κ
  Y := Bool
  transition := eliminationRow hψ
  output := LDSinkUnifiedFinite.output

/-- The ordinary population-protocol edge step, with its original endpoint
priority and scheduler alphabet. The local row does not know n. -/
abbrev step (hψ : 0 < ψ) (ring : DirectedRing n)
    (C : Fin n → UCell ψ κ) (e : Fin n) : Fin n → UCell ψ κ :=
  (protocol hψ κ).step ring C e

/-- One physical edge is exactly one modulus-one K2 edge under observation. -/
theorem observe_step (hψ : 0 < ψ) (ring : DirectedRing n)
    (C : Fin n → UCell ψ κ) (e : Fin n) :
    observe (step hψ ring C e) = rawStep (by decide) ring (observe C) e := by
  have hq := observe_row hψ (C e) (C (ring.rightNeighbor e))
  funext i
  simp only [observe, step, PopulationProtocol.step, protocol, rawStep, updatePair]
  split
  · exact congrArg Prod.fst hq
  · split
    · exact congrArg Prod.snd hq
    · rfl

/-- Every non-signal field remains at its own physical site after an edge. -/
theorem step_frame (hψ : 0 < ψ) (ring : DirectedRing n)
    (C : Fin n → UCell ψ κ) (e i : Fin n) :
    putSignals (step hψ ring C e i) (observeCell (C i)) = C i := by
  unfold step PopulationProtocol.step protocol
  by_cases he : i = e
  · subst i
    simpa using (row_frame hψ (C e) (C (ring.rightNeighbor e))).1
  · by_cases hr : i = ring.rightNeighbor e
    · subst i
      simpa [he] using
        (row_frame hψ (C e) (C (ring.rightNeighbor e))).2
    · simp only [if_neg he, if_neg hr, putSignals_self]

/-- Entire physical words retain all original non-signal fields, with no
temporary label/bit/path/count/controller reset hidden between endpoints. -/
theorem run_frame (hψ : 0 < ψ) (ring : DirectedRing n)
    (C : Fin n → UCell ψ κ) (es : List (Fin n)) (i : Fin n) :
    putSignals (run (step hψ ring) C es i) (observeCell (C i)) = C i := by
  induction es generalizing C with
  | nil => exact putSignals_self (C i)
  | cons e es ih =>
      have h := congrArg (fun q => putSignals q (observeCell (C i)))
        (ih (step hψ ring C e))
      simpa only [putSignals_twice, step_frame, run] using h

/-- Full-word physical erasure preserves every scheduler choice and length. -/
theorem observe_run (hψ : 0 < ψ) (ring : DirectedRing n)
    (C : Fin n → UCell ψ κ) (es : List (Fin n)) :
    observe (run (step hψ ring) C es) =
      run (rawStep (by decide) ring) (observe C) es := by
  induction es generalizing C with
  | nil => rfl
  | cons e es ih => simp only [run, ih, observe_step]

/-- The complete physical output vector agrees with the shadow execution at
every word, even outside any safe or gap class. -/
theorem run_output_erasure (hψ : 0 < ψ) (ring : DirectedRing n)
    (C : Fin n → UCell ψ κ) (es : List (Fin n)) (i : Fin n) :
    LDSinkUnifiedFinite.output (run (step hψ ring) C es i) =
      (run (rawStep (by decide) ring) (observe C) es i).leader :=
  congrArg AgentState.leader (congrFun (observe_run hψ ring C es) i)

/-- The protocol type is definitionally the previously counted UCell. -/
theorem carrier_eq (hψ : 0 < ψ) : (protocol hψ κ).Q = UCell ψ κ := rfl

/-- Every local output lies in the existing complete carrier enumeration. -/
theorem row_enumerated (hψ : 0 < ψ) (l r : UCell ψ κ) :
    (eliminationRow hψ l r).1 ∈ allUCell ψ κ ∧
      (eliminationRow hψ l r).2 ∈ allUCell ψ κ :=
  ⟨enumeration_complete ψ κ _, enumeration_complete ψ κ _⟩

/-- The existing polynomial bound has no new factor. The modulus-one
observation is a proof map, not an extra stored state component. -/
theorem state_bound (hψ : 0 < ψ) (hκ : ψ ≤ κ + 1) :
    (allUCell ψ κ).length ≤ 4862332800 * 61931520000000 * (κ + 1) ^ 8 :=
  LDSinkUnifiedFinite.state_bound ψ κ hψ hκ

/-! ## Controller-only writes and output safety -/

/-- An ordinary write to an existing label and controller. Both new values
are arbitrary and none of the four elimination fields is changed. -/
def controllerWrite (q : UCell ψ κ) (label : Fin ψ)
    (control : ShortGapUnifiedNode.UNode) : UCell ψ κ :=
  { legacy := { q.legacy with label := label }, control := control }

/-- The actual projection forgets ordinary controller/label writes. -/
@[simp] theorem observe_controllerWrite (q : UCell ψ κ) (label : Fin ψ)
    (control : ShortGapUnifiedNode.UNode) :
    observeCell (controllerWrite q label control) = observeCell q := rfl

/-- Fixed controller/label writes commute with the whole elimination row,
not merely with a presumed closed predicate. -/
theorem controllerWrite_commutes (hψ : 0 < ψ) (l r : UCell ψ κ)
    (a b : Fin ψ) (u v : ShortGapUnifiedNode.UNode) :
    eliminationRow hψ (controllerWrite l a u) (controllerWrite r b v) =
      (controllerWrite (eliminationRow hψ l r).1 a u,
       controllerWrite (eliminationRow hψ l r).2 b v) := rfl

/-- Pull back the already proved RowSafe invariant at modulus one. No
condition is imposed on the real labels or controller fields. -/
def SignalSafe (ring : DirectedRing n) (C : Fin n → UCell ψ κ) : Prop :=
  RowSafe (by decide) ring (observe C)

/-- RowSafe closure transfers through the exact physical observation. -/
theorem signalSafe_step (hψ : 0 < ψ) (hn : 1 < n) (ring : DirectedRing n)
    (C : Fin n → UCell ψ κ) (hC : SignalSafe ring C) (e : Fin n) :
    SignalSafe ring (step hψ ring C e) := by
  unfold SignalSafe
  rw [observe_step]
  exact rowSafe_step (by decide) hn ring _ hC e

/-- On the actual pulled-back RowSafe set each physical output is unchanged. -/
theorem step_output (hψ : 0 < ψ) (ring : DirectedRing n)
    (C : Fin n → UCell ψ κ) (hC : SignalSafe ring C) (e i : Fin n) :
    LDSinkUnifiedFinite.output (step hψ ring C e i) = LDSinkUnifiedFinite.output (C i) :=
  (congrArg AgentState.leader (congrFun (observe_step hψ ring C e) i)).trans
    (rawStep_leader (by decide) ring (observe C) hC e i)

/-- The actual closed predicate is derived from the physical row. -/
theorem signalSafe_closed (hψ : 0 < ψ) (hn : 1 < n) (ring : DirectedRing n) :
    PopulationProtocol.ClosedPred (protocol hψ κ) ring (SignalSafe ring) := by
  intro C hC D hstep
  obtain ⟨e, rfl⟩ := hstep
  exact signalSafe_step hψ hn ring C hC e

/-- Semantic safety for the new finite elimination protocol, using the
existing IsSafe definition: unique output now and invariant output at every
reachable configuration. This is not a dispatcher safety theorem. -/
theorem isSafe (hψ : 0 < ψ) (hn : 1 < n) (ring : DirectedRing n)
    (C : Fin n → UCell ψ κ) (hC : SignalSafe ring C) :
    PopulationProtocol.IsSafe (protocol hψ κ) ring C id := by
  apply isSafe_of_operational_legitimacy (protocol hψ κ) ring id
    (SignalSafe ring) (signalSafe_closed hψ hn ring)
  · intro D hD
    exact hD.1.unique_leader
  · intro D hD E hstep i
    obtain ⟨e, rfl⟩ := hstep
    exact step_output hψ ring D hD e i
  · exact hC

/-! ## The real global gap class at shadow modulus one -/

/-- The full original physical audit fields, before the signal observation. -/
def physicalConfig (C : Fin n → UCell ψ κ) : Fin n → AgentState ψ :=
  eraseConfig (LDSinkUnifiedFinite.legacyConfig C)

/-- The already proved global class on the modulus-one observation. -/
def SignalGlobal (ring : DirectedRing n) (C : Fin n → UCell ψ κ) : Prop :=
  K2GlobalGapClosure.GlobalInvariant (by decide) ring (observe C)

/-- This class asks for the actual physical separation and signal order;
there is no condition on physical labels and hence no divisibility premise. -/
theorem signalGlobal_iff (ring : DirectedRing n) (C : Fin n → UCell ψ κ) :
    SignalGlobal ring C ↔
      K2GlobalGapClosure.Separated ring (physicalConfig C) ∧
      (∀ G : GapFrame n, GapEndpointsPresent G (physicalConfig C) →
        GapInteriorFollowers G (physicalConfig C) →
        GapSignalBelowBullets G (physicalConfig C)) := by
  constructor
  · intro h
    exact ⟨h.separated, h.signal⟩
  · rintro ⟨hsep, hsig⟩
    exact ⟨hsep, cyclicLabels_one ring (observe C), hsig⟩

/-- Every actual new-row edge preserves the pulled-back physical class. -/
theorem signalGlobal_step (hψ : 0 < ψ) (ring : DirectedRing n)
    (C : Fin n → UCell ψ κ) (hC : SignalGlobal ring C) (e : Fin n) :
    SignalGlobal ring (step hψ ring C e) := by
  unfold SignalGlobal
  rw [observe_step]
  exact K2GlobalGapClosure.global_step (by decide) ring _ hC e

/-- Global signal order and separation survive every physical word. -/
theorem signalGlobal_run (hψ : 0 < ψ) (ring : DirectedRing n)
    (C : Fin n → UCell ψ κ) (hC : SignalGlobal ring C) (es : List (Fin n)) :
    SignalGlobal ring (run (step hψ ring) C es) := by
  induction es generalizing C with
  | nil => exact hC
  | cons e es ih => exact ih _ (signalGlobal_step hψ ring C hC e)

/-- Signal-zero physical configurations provide the class on every ring,
with arbitrary stored labels, bullets and non-signal payloads. -/
theorem signalGlobal_of_signals_zero (ring : DirectedRing n)
    (C : Fin n → UCell ψ κ)
    (hsep : K2GlobalGapClosure.Separated ring (physicalConfig C))
    (hs : ∀ i, (C i).legacy.signal_B = 0) : SignalGlobal ring C :=
  K2GlobalGapClosure.global_of_signals_zero (by decide) ring (observe C) hsep
    (cyclicLabels_one ring (observe C)) hs

/-- Any actual pair of physical consecutive gaps yields the existing
GapPair at modulus one. Geometry and tagged endpoints are not copied. -/
theorem selected_gapPair (ring : DirectedRing n) (C : Fin n → UCell ψ κ)
    (hC : SignalGlobal ring C) (F : TwoGapFrame n)
    (hrE : GapEndpointsPresent F.recovery (physicalConfig C))
    (hrI : GapInteriorFollowers F.recovery (physicalConfig C))
    (haE : GapEndpointsPresent F.attack (physicalConfig C))
    (haI : GapInteriorFollowers F.attack (physicalConfig C)) (phase : APhase) :
    GapPair (by decide) F ⟨observe C, phase⟩ :=
  K2GlobalGapClosure.selected_gapPair (by decide) ring (observe C) hC F
    hrE hrI haE haI phase

/-! ## Exact simulation of the existing stopped physical deletion tree -/

/-- The real tagged deletion predicate observes only physical leader bits. -/
theorem success2_observe (F : TwoGapFrame n) (C : Fin n → UCell ψ κ) :
    NoResetSuccess F (physicalConfig C) ↔ NoResetSuccess F (observe C) := Iff.rfl

/-- The actual race entrance is unchanged by observation. -/
theorem raceReady_observe (F : TwoGapFrame n) (C : Fin n → UCell ψ κ) :
    RaceReady F (physicalConfig C) ↔ RaceReady F (observe C) := Iff.rfl

noncomputable section

/-- Stop the new physical finite-row process exactly on the existing
physical tagged-deletion predicate. No ghost phase occurs in its state. -/
def blockStep (hψ : 0 < ψ) (F : TwoGapFrame n)
    (C : Fin n → UCell ψ κ) (e : Fin n) : StopNode (Fin n → UCell ψ κ) := by
  classical
  let C' := step hψ F.attack.ring C e
  exact if NoResetSuccess F (physicalConfig C') then .success else .active C'

/-- The existing stopped audit may have either ghost phase. Its
configuration must equal the concrete signal observation; terminals agree. -/
def Observed : StopNode (Fin n → UCell ψ κ) → StopNode (AState n 1) → Prop
  | .active C, .active a => a.conf = observe C
  | .success, .success => True
  | .failure, .failure => True
  | _, _ => False

/-- Concrete single-edge simulation of the existing `physicalBlockStep`.
The equality follows from the actual row and physical stopping predicate. -/
theorem observed_step (hψ : 0 < ψ) (F : TwoGapFrame n)
    (u : StopNode (Fin n → UCell ψ κ)) (v : StopNode (AState n 1))
    (h : Observed u v) (e : Fin n) :
    Observed (stepNode (blockStep hψ F) u e)
      (stepNode (physicalBlockStep (by decide) F) v e) := by
  classical
  cases u with
  | success => cases v <;> simp_all [Observed, stepNode]
  | failure => cases v <;> simp_all [Observed, stepNode]
  | active C =>
    cases v with
    | success => exact h.elim
    | failure => exact h.elim
    | active a =>
      change a.conf = observe C at h
      have hp : attemptStepConf (by decide) F a e =
          observe (step hψ F.attack.ring C e) := by
        rw [attemptStepConf_eq_sinkStepC, h, observe_step]
        rfl
      simp only [stepNode, blockStep, physicalBlockStep_normal_form, hp,
        success2_observe]
      split
      · trivial
      · change (postState (by decide) F a e).conf =
          observe (step hψ F.attack.ring C e)
        exact hp

/-- Exact existing tree weights agree for any matching leaf observations.
Both trees keep their original n raw branches and terminal padding. -/
theorem observed_treeWeight (hψ : 0 < ψ) (F : TwoGapFrame n)
    (wf : StopNode (Fin n → UCell ψ κ) → Nat)
    (wa : StopNode (AState n 1) → Nat)
    (hw : ∀ u v, Observed u v → wf u = wa v)
    (u : StopNode (Fin n → UCell ψ κ)) (v : StopNode (AState n 1))
    (h : Observed u v) (T : Nat) :
    treeWeight (blockStep hψ F) wf u T =
      treeWeight (physicalBlockStep (by decide) F) wa v T := by
  induction T generalizing u v with
  | zero => exact hw u v h
  | succ T ih =>
    simp only [treeWeight]
    exact ofFn_sum_eq _ _ (fun e => ih _ _ (observed_step hψ F u v h e))

/-- Successful word counts are exactly the already checked physical K2
counts at modulus one, with the same finite horizon and actual endpoints. -/
theorem successCount_eq (hψ : 0 < ψ) (F : TwoGapFrame n)
    (C : Fin n → UCell ψ κ) (phase : APhase) (T : Nat) :
    successCount (blockStep hψ F) (.active C) T =
      successCount (physicalBlockStep (by decide) F) (.active ⟨observe C, phase⟩) T := by
  apply observed_treeWeight hψ F successWeight successWeight ?_
    (.active C) (.active ⟨observe C, phase⟩) (by rfl) T
  intro x y hxy
  cases x <;> cases y <;> simp_all [Observed, successWeight]

/-- Consume the proved actual 1/16 race mass, without an assumed mass or
simulation bound. The physical labels and controllers are unrestricted. -/
theorem race_mass (hψ : 0 < ψ) (F : TwoGapFrame n) (C : Fin n → UCell ψ κ)
    (hg : GapPair (by decide) F ⟨observe C, .transit⟩)
    (hr : RaceReady F (physicalConfig C)) :
    n ^ (4 * n) ≤ 16 * successCount (blockStep hψ F) (.active C) (4 * n) := by
  rw [successCount_eq hψ F C .transit]
  exact LDSinkTwoGapArrivalRaceMass.physical_race_mass (by decide) F _ hg hr

/-- A physical global class and an actually selected ready gap pair produce
the mass premise above, with no condition ψ divides n. -/
theorem selected_race_mass (hψ : 0 < ψ) (ring : DirectedRing n)
    (C : Fin n → UCell ψ κ) (hC : SignalGlobal ring C) (F : TwoGapFrame n)
    (hrE : GapEndpointsPresent F.recovery (physicalConfig C))
    (hrI : GapInteriorFollowers F.recovery (physicalConfig C))
    (haE : GapEndpointsPresent F.attack (physicalConfig C))
    (haI : GapInteriorFollowers F.attack (physicalConfig C))
    (hr : RaceReady F (physicalConfig C)) :
    n ^ (4 * n) ≤ 16 * successCount (blockStep hψ F) (.active C) (4 * n) :=
  race_mass hψ F C (selected_gapPair ring C hC F hrE hrI haE haI .transit) hr

end

/-! ## Nondivisible-label finite witnesses -/

namespace NondivisibleExample

/-- Two separated leaders with a travelling live bullet, physical labels
all equal to one, and the existing controller value from `finiteCut`. -/
def seed5 (i : Fin 5) : UCell 2 1 :=
  { legacy := { boundedCanonical (by decide) 1 i with
      label := 1
      leader := decide (i = 0 ∨ i = 2)
      shield := decide (i = 0)
      signal_B := 0
      bullet := if i = 4 then 2 else 0 }
    control := (finiteCut 0).control }

theorem ring5 : DirectedRing 5 := ⟨by decide⟩

/-- The real physical modulus does not divide the ring size. -/
theorem nondivisible5 : ¬ 2 ∣ 5 := by decide

/-- The new global class is inhabited despite incompatible physical labels. -/
theorem seed5_global : SignalGlobal ring5 seed5 := by
  apply signalGlobal_of_signals_zero
  · unfold K2GlobalGapClosure.Separated
    decide
  · intro i; rfl

/-- This same physical state is excluded by the old fully labeled global
class. The new result does not silently assert that the old class expanded. -/
theorem seed5_not_old_global :
    ¬ K2GlobalGapClosure.GlobalInvariant (by decide) ring5 (physicalConfig seed5) := by
  intro h
  exact nondivisible5 (K2GlobalGapClosure.global_requires_dvd (by decide) ring5 _ h)

/-- Across the mismatched follower edge, the new row moves the live bullet
and the old K2 row does not. This is a concrete difference in physical rows. -/
theorem different_rows :
    (step (by decide) ring5 seed5 3 3).legacy.bullet = 2 ∧
    (rawStep (by decide) ring5 (physicalConfig seed5) 3 3).bullet = 0 := by
  decide

/-- The same two raw scheduler edges move then delete a physical leader
under the new row; the old mismatched-label execution retains that leader. -/
theorem actual_deletion :
    (run (step (by decide) ring5) seed5 [3, 2] 2).legacy.leader = false ∧
    (run (rawStep (by decide) ring5) (physicalConfig seed5) [3, 2] 2).leader = true := by
  decide

/-- The observed safe set admits a surviving physical leader whose stored
label is one. The deleting row leaves a dummy bullet, which the actual safe
predicate permits. No physical label is reset to obtain safety. -/
theorem after_safe : SignalSafe ring5 (run (step (by decide) ring5) seed5 [3, 2]) := by
  let C := run (step (by decide) ring5) seed5 [3, 2]
  have hnolive : ∀ i, (observe C i).bullet ≠ 2 := by decide
  have hsafe : OutputSafeConfig (by decide) ring5 (observe C) := by
    refine
      { unique_leader := ?_
        leader_label_zero := ?_
        no_nonpeaceful_bullet := ?_
        no_free_barrier := ?_ }
    · unfold hasUniqueLeader
      decide
    · intro i _; exact Subsingleton.elim _ _
    · intro i hi
      exact False.elim (hnolive i hi)
    · intro i
      dsimp only
      intro hi
      exact False.elim (hi (Subsingleton.elim _ _))
  exact rowSafe_of_outputSafe (by decide) ring5 (observe C) hsafe

/-- The actual finite protocol, rather than a shadow-only declaration, has
semantic output safety at the concrete post-deletion physical state. -/
theorem after_isSafe :
    PopulationProtocol.IsSafe (protocol (by decide) 1) ring5
      (run (step (by decide) ring5) seed5 [3, 2]) id :=
  isSafe (by decide) (by decide) ring5 _ after_safe

/-- A real seven-agent ready race, again with physical modulus two and
arbitrary-label controller storage. -/
def seed7 (i : Fin 7) : UCell 2 1 :=
  { legacy := { boundedCanonical (by decide) 1 i with
      label := 1
      leader := decide (i = 0 ∨ i = 2 ∨ i = 4)
      shield := false
      signal_B := if i = 2 then 1 else 0
      bullet := if i = 3 then 2 else 0 }
    control := (finiteCut 0).control }

/-- Existing physical gap geometry, instantiated with lengths two and two. -/
def frame7 : TwoGapFrame 7 where
  recovery := ⟨⟨by decide⟩, 0, 2, by decide, by decide⟩
  attack := ⟨⟨by decide⟩, 2, 2, by decide, by decide⟩
  shared := by decide
  length_lt := by decide

theorem nondivisible7 : ¬ 2 ∣ 7 := by decide

/-- The exact existing GapPair hypotheses hold for this nondivisible
physical-label example. All finite gap obligations are discharged here. -/
theorem seed7_gapPair : GapPair (by decide) frame7 ⟨observe seed7, .transit⟩ := by
  constructor
  · refine ⟨⟨rfl, rfl⟩, ?_, ?_, ?_⟩
    · intro k hk hkd
      have : k = 1 := by change k < 2 at hkd; omega
      subst k
      decide
    · intro k _; exact Subsingleton.elim _ _
    · intro k j hk hkd hb _ _
      have hkd' : k ≤ 2 := hkd
      have hk' : k = 1 ∨ k = 2 := by omega
      rcases hk' with rfl | rfl <;> exact False.elim (hb rfl)
  · refine ⟨⟨rfl, rfl⟩, ?_, ?_, ?_⟩
    · intro k hk hkd
      have : k = 1 := by change k < 2 at hkd; omega
      subst k
      decide
    · intro k _; exact Subsingleton.elim _ _
    · intro k j hk _ _ hkj hjd
      have hjd' : j ≤ 2 := hjd
      have hj : j = 1 ∨ j = 2 := by omega
      rcases hj with rfl | rfl <;> rfl

/-- RaceReady is checked on the actual physical fields. -/
theorem seed7_ready : RaceReady frame7 (physicalConfig seed7) := by
  constructor
  · rfl
  · constructor
    · rfl
    · intro k hk hkd
      have hkd' : k ≤ 2 := hkd
      have hk' : k = 1 ∨ k = 2 := by omega
      rcases hk' with rfl | rfl <;> rfl

/-- A concrete nondivisible physical-label configuration consumes the
proved 1/16 mass theorem at the original 28-interaction horizon. -/
theorem seed7_race_mass :
    7 ^ (4 * 7) ≤
      16 * successCount (blockStep (by decide) frame7) (.active seed7) (4 * 7) :=
  race_mass (by decide) frame7 seed7 seed7_gapPair seed7_ready

end NondivisibleExample

end LabelFreeElimination
