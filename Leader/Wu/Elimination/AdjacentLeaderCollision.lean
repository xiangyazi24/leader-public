import Leader.Wu.Elimination.LabelFreeElimination

/-!
# Adjacent-leader collision on the existing finite carrier

This separately named elimination component extends the frozen label-free
row. The statements concern actual finite physical cells and ordinary ring
edges. They do not assert arbitrary-state stabilization or a full dispatcher.
-/

namespace AdjacentLeaderElimination

open StateBoundUnifiedCell LDSinkBoundedKernel LDSinkKernelC PPLLRepair
open K2OutputSafety LabelFreeElimination LDSinkGapCleanup
open LDSinkProtectedAbsorption LDSinkTwoGapEpochSuccessor PPLLNoCheckBirthConditionTwoGeometry
open PPLLResearchFormulation PPLLNoCheckBirthOutputLegitimacy
open FiniteUniformStoppingTree
open LDTwoGapFrame LDSinkTwoGapNoResetKernel LDSinkTwoGapDeletionWired LDSinkTwoGapReachInvariant
open LDSinkTwoGapEntrance

set_option autoImplicit false

variable {ψ κ n : Nat}

private theorem sum_indicator (e : Fin n) :
    (List.ofFn (fun i : Fin n => if i = e then 1 else 0)).sum = 1 := by
  induction n with
  | zero => exact Fin.elim0 e
  | succ n ih =>
      have hz : ∀ i : Fin n, i.succ ≠ (0 : Fin (n + 1)) := by
        intro i h
        have hv := congrArg Fin.val h
        change i.val + 1 = 0 at hv
        omega
      refine Fin.cases ?_ (fun j => ?_) e
      · simp [List.ofFn_succ, hz, FiniteUniformStoppingTree.ofFn_sum_const]
      · rw [List.ofFn_succ, List.sum_cons]
        have hh : (0 : Fin (n + 1)) ≠ j.succ := fun h => hz j h.symm
        simpa [hh] using ih j

/-- The proposed two-leader trap, stated using the actual K2 fields. -/
def Blocked (q : AgentState ψ) : Prop :=
  q.leader = true ∧ q.shield = true ∧ q.bullet = 2 ∧ q.signal_B = 0

/-- The claimed fixed pair is an identity of the actual kernel. -/
theorem old_kernel_fixed (hψ : 0 < ψ) (l r : AgentState ψ)
    (hl : Blocked l) (hr : Blocked r) : sinkKernelC hψ l r = (l, r) := by
  rcases hl with ⟨hlL, hlS, hlB, hlZ⟩
  rcases hr with ⟨hrL, hrS, hrB, hrZ⟩
  simp [sinkKernelC, eliminateLeadersNoCollisionFire, absorbProtectedMove,
    eliminateLeadersNoCollisionZeroLeaderEgressMove,
    eliminateLeadersNoCollisionSignalLeaderSink, dummyBulletSink,
    hlL, hlS, hlZ, hrL, hrS, hrB, hrZ]
  cases r
  simp_all

/-- No assumptions about physical labels, auxiliary data or controllers. -/
theorem old_row_fixed (hψ : 0 < ψ) (l r : UCell ψ κ)
    (hl : Blocked (observeCell l)) (hr : Blocked (observeCell r)) :
    eliminationRow hψ l r = (l, r) := by
  unfold eliminationRow
  rw [old_kernel_fixed (by decide) _ _ hl hr]
  simp

namespace FixedPoint

theorem ring2 : DirectedRing 2 := ⟨by decide⟩

/-- Actual modulus-one finite cells, with both leaders shielded and live. -/
def seed (i : Fin 2) : UCell 1 0 :=
  { legacy := { boundedCanonical (by decide) 0 i with
      leader := true, shield := true, bullet := 2, signal_B := 0 }
    control := (finiteCut 0).control }

theorem blocked (i : Fin 2) : Blocked (observeCell (seed i)) := by
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem old_step_fixed (e : Fin 2) :
    LabelFreeElimination.step (by decide) ring2 seed e = seed := by
  funext i
  unfold LabelFreeElimination.step PopulationProtocol.step LabelFreeElimination.protocol
  dsimp only
  rw [old_row_fixed (by decide) _ _ (blocked e) (blocked (ring2.rightNeighbor e))]
  split <;> rename_i hi
  · subst i; rfl
  · split
    · rename_i hi; subst i; rfl
    · rfl

theorem old_run_fixed (es : List (Fin 2)) :
    run (LabelFreeElimination.step (by decide) ring2) seed es = seed := by
  induction es with
  | nil => rfl
  | cons e es ih => simpa only [run, old_step_fixed] using ih

theorem two_leaders (i : Fin 2) : (seed i).legacy.leader = true := rfl

end FixedPoint

/-- Direct deletion alone, retained solely for the concrete failure witness. -/
def bareRow (hψ : 0 < ψ) (l r : UCell ψ κ) : UCell ψ κ × UCell ψ κ :=
  if l.legacy.leader = true ∧ r.legacy.leader = true then
    ({ l with legacy := { l.legacy with leader := false } }, r)
  else eliminationRow hψ l r

def bareProtocol (hψ : 0 < ψ) (κ : Nat) : PopulationProtocol where
  Q := UCell ψ κ
  Y := Bool
  transition := bareRow hψ
  output := LDSinkUnifiedFinite.output

namespace BareFailure

/-- Quiet, adjacent leaders; the losing leader carries a live bullet and
the survivor is unshielded. Physical labels and controller data are real. -/
def seed (i : Fin 2) : UCell 2 0 :=
  { legacy := { boundedCanonical (by decide) 0 i with
      leader := true, shield := false, signal_B := 0,
      bullet := if i = 0 then 2 else 0, label := 1 }
    control := (finiteCut 0).control }

theorem direct_deletion_leaves_danger :
    ((bareProtocol (by decide) 0).step FixedPoint.ring2 seed 0 0).legacy.leader = false ∧
    ((bareProtocol (by decide) 0).step FixedPoint.ring2 seed 0 0).legacy.bullet = 2 ∧
    ((bareProtocol (by decide) 0).step FixedPoint.ring2 seed 0 1).legacy.leader = true := by
  decide

/-- The reverse physical edge then deletes the survivor. This is output
instability, not merely failure of membership in a sufficient predicate. -/
theorem next_edge_deletes_survivor :
    ∀ i : Fin 2,
      (run ((bareProtocol (by decide) 0).step FixedPoint.ring2) seed [0, 1] i).legacy.leader =
        false := by
  decide

theorem after_not_isSafe :
    ¬ PopulationProtocol.IsSafe (bareProtocol (by decide) 0) FixedPoint.ring2
      ((bareProtocol (by decide) 0).step FixedPoint.ring2 seed 0) id := by
  intro h
  have hchange := h.2 _
    (PopulationProtocol.Reachable.step _ _ _ (.refl _) ⟨1, rfl⟩) 1
  change false = true at hchange
  cases hchange

end BareFailure

/-- Clear the losing leader's signal trail through the adjacent survivor,
and arm that survivor. Existing bullets are retained: a live losing bullet
now has a zero-signal path of length one to the shielded surviving leader.
The proofs below establish peacefulness, hence defuse it semantically. -/
def collisionRow (hψ : 0 < ψ) (l r : UCell ψ κ) : UCell ψ κ × UCell ψ κ :=
  if l.legacy.leader = true ∧ r.legacy.leader = true then
    (putSignals l { observeCell l with leader := false, signal_B := 0 },
      putSignals r { observeCell r with shield := true, signal_B := 0 })
  else eliminationRow hψ l r

def protocol (hψ : 0 < ψ) (κ : Nat) : PopulationProtocol where
  Q := UCell ψ κ
  Y := Bool
  transition := collisionRow hψ
  output := LDSinkUnifiedFinite.output

abbrev step (hψ : 0 < ψ) (ring : DirectedRing n)
    (C : Fin n → UCell ψ κ) (e : Fin n) : Fin n → UCell ψ κ :=
  (protocol hψ κ).step ring C e

theorem row_of_adjacent (hψ : 0 < ψ) (l r : UCell ψ κ)
    (hl : l.legacy.leader = true) (hr : r.legacy.leader = true) :
    collisionRow hψ l r =
      (putSignals l { observeCell l with leader := false, signal_B := 0 },
        putSignals r { observeCell r with shield := true, signal_B := 0 }) :=
  if_pos ⟨hl, hr⟩

theorem row_eq_old (hψ : 0 < ψ) (l r : UCell ψ κ)
    (h : ¬ (l.legacy.leader = true ∧ r.legacy.leader = true)) :
    collisionRow hψ l r = eliminationRow hψ l r := if_neg h

/-- Exact framing of every non-signal field at its original endpoint. -/
theorem row_frame (hψ : 0 < ψ) (l r : UCell ψ κ) :
    putSignals (collisionRow hψ l r).1 (observeCell l) = l ∧
      putSignals (collisionRow hψ l r).2 (observeCell r) = r := by
  unfold collisionRow
  split
  · exact ⟨putSignals_restore l _, putSignals_restore r _⟩
  · exact LabelFreeElimination.row_frame hψ l r

theorem row_labels_control (hψ : 0 < ψ) (l r : UCell ψ κ) :
    (collisionRow hψ l r).1.legacy.label = l.legacy.label ∧
    (collisionRow hψ l r).2.legacy.label = r.legacy.label ∧
    (collisionRow hψ l r).1.control = l.control ∧
    (collisionRow hψ l r).2.control = r.control := by
  unfold collisionRow
  split
  · exact ⟨rfl, rfl, rfl, rfl⟩
  · exact LabelFreeElimination.row_labels_control hψ l r

theorem step_frame (hψ : 0 < ψ) (ring : DirectedRing n)
    (C : Fin n → UCell ψ κ) (e i : Fin n) :
    putSignals (step hψ ring C e i) (observeCell (C i)) = C i := by
  simp only [step, PopulationProtocol.step, protocol]
  split
  · rename_i hi; subst i; exact (row_frame hψ _ _).1
  · split
    · rename_i hi; subst i; exact (row_frame hψ _ _).2
    · exact putSignals_self _

theorem run_frame (hψ : 0 < ψ) (ring : DirectedRing n)
    (C : Fin n → UCell ψ κ) (es : List (Fin n)) (i : Fin n) :
    putSignals (run (step hψ ring) C es i) (observeCell (C i)) = C i := by
  induction es generalizing C with
  | nil => exact putSignals_self _
  | cons e es ih =>
      have h := congrArg (fun q => putSignals q (observeCell (C i)))
        (ih (step hψ ring C e))
      simpa only [putSignals_twice, step_frame, run] using h

/-- Ordinary writes to arbitrary stored labels and full controllers commute
with the actual row. The guard reads only the existing leader bits. -/
theorem controllerWrite_commutes (hψ : 0 < ψ) (l r : UCell ψ κ)
    (a b : Fin ψ) (u v : ShortGapUnifiedNode.UNode) :
    collisionRow hψ (controllerWrite l a u) (controllerWrite r b v) =
      (controllerWrite (collisionRow hψ l r).1 a u,
        controllerWrite (collisionRow hψ l r).2 b v) := by
  unfold collisionRow
  change (if l.legacy.leader = true ∧ r.legacy.leader = true then _ else _) = _
  split <;> rfl

theorem carrier_eq (hψ : 0 < ψ) : (protocol hψ κ).Q = UCell ψ κ := rfl

theorem row_enumerated (hψ : 0 < ψ) (l r : UCell ψ κ) :
    (collisionRow hψ l r).1 ∈ allUCell ψ κ ∧
      (collisionRow hψ l r).2 ∈ allUCell ψ κ :=
  ⟨enumeration_complete ψ κ _, enumeration_complete ψ κ _⟩

theorem state_bound (hψ : 0 < ψ) (hκ : ψ ≤ κ + 1) :
    (allUCell ψ κ).length ≤ 4862332800 * 61931520000000 * (κ + 1) ^ 8 :=
  LabelFreeElimination.state_bound hψ hκ

/-- The exact old physical step whenever the new local guard is false. -/
theorem step_eq_old (hψ : 0 < ψ) (ring : DirectedRing n)
    (C : Fin n → UCell ψ κ) (e : Fin n)
    (h : ¬ ((C e).legacy.leader = true ∧
      (C (ring.rightNeighbor e)).legacy.leader = true)) :
    step hψ ring C e = LabelFreeElimination.step hψ ring C e := by
  funext i
  simp only [step, LabelFreeElimination.step, PopulationProtocol.step,
    protocol, LabelFreeElimination.protocol, row_eq_old hψ _ _ h]

theorem row_left_follower (hψ : 0 < ψ) (l r : UCell ψ κ)
    (hl : l.legacy.leader = false) :
    (collisionRow hψ l r).1.legacy.leader = false := by
  rw [row_eq_old hψ l r (by simp [hl])]
  exact kernelC_left_follower (by decide) (observeCell l) (observeCell r) hl

theorem row_right_leader (hψ : 0 < ψ) (l r : UCell ψ κ) :
    (collisionRow hψ l r).2.legacy.leader = r.legacy.leader := by
  unfold collisionRow
  split
  · rfl
  · exact kernelC_right_leader_eq (by decide) (observeCell l) (observeCell r)

/-- Neither the old row nor the collision creates a leader. -/
theorem step_follower (hψ : 0 < ψ) (ring : DirectedRing n)
    (C : Fin n → UCell ψ κ) (e i : Fin n) (hi : (C i).legacy.leader = false) :
    (step hψ ring C e i).legacy.leader = false := by
  simp only [step, PopulationProtocol.step, protocol]
  split
  · rename_i h; subst i; exact row_left_follower hψ _ _ hi
  · split
    · rename_i h; subst i; exact (row_right_leader hψ _ _).trans hi
    · exact hi

theorem step_leader_source (hψ : 0 < ψ) (ring : DirectedRing n)
    (C : Fin n → UCell ψ κ) (e i : Fin n)
    (hi : (step hψ ring C e i).legacy.leader = true) :
    (C i).legacy.leader = true := by
  cases h : (C i).legacy.leader
  · have := step_follower hψ ring C e i h; simp_all
  · rfl

theorem step_leader_away (hψ : 0 < ψ) (ring : DirectedRing n)
    (C : Fin n → UCell ψ κ) (e i : Fin n) (hi : i ≠ e) :
    (step hψ ring C e i).legacy.leader = (C i).legacy.leader := by
  simp only [step, PopulationProtocol.step, protocol, if_neg hi]
  split
  · rename_i hr; subst i; exact row_right_leader hψ _ _
  · rfl

/-- The existing separated predicate, with no new geometry. -/
theorem separated_step_eq_old (hψ : 0 < ψ) (ring : DirectedRing n)
    (C : Fin n → UCell ψ κ)
    (hs : K2GlobalGapClosure.Separated ring (observe C)) (e : Fin n) :
    step hψ ring C e = LabelFreeElimination.step hψ ring C e := by
  apply step_eq_old
  rintro ⟨hl, hr⟩
  have hh := hs e hl
  change (C (ring.rightNeighbor e)).legacy.leader = false at hh
  simp_all

theorem separated_step (hψ : 0 < ψ) (ring : DirectedRing n)
    (C : Fin n → UCell ψ κ)
    (hs : K2GlobalGapClosure.Separated ring (observe C)) (e : Fin n) :
    K2GlobalGapClosure.Separated ring (observe (step hψ ring C e)) := by
  intro i hi
  exact step_follower hψ ring C e _ (hs i (step_leader_source hψ ring C e i hi))

/-- Every scheduler word agrees exactly, including all old deletions and
all auxiliary physical fields. There is no clock or scheduler quotient. -/
theorem separated_run_eq_old (hψ : 0 < ψ) (ring : DirectedRing n)
    (C : Fin n → UCell ψ κ)
    (hs : K2GlobalGapClosure.Separated ring (observe C)) (es : List (Fin n)) :
    run (step hψ ring) C es = run (LabelFreeElimination.step hψ ring) C es := by
  induction es generalizing C with
  | nil => rfl
  | cons e es ih =>
      simp only [run]
      rw [ih _ (separated_step hψ ring C hs e), separated_step_eq_old hψ ring C hs e]

/-- Unique leadership makes the new guard impossible on a nontrivial ring. -/
theorem unique_step_eq_old (hψ : 0 < ψ) (hn : 1 < n) (ring : DirectedRing n)
    (C : Fin n → UCell ψ κ) (hu : hasUniqueLeader n (observe C)) (e : Fin n) :
    step hψ ring C e = LabelFreeElimination.step hψ ring C e := by
  apply step_eq_old
  rintro ⟨hl, hr⟩
  obtain ⟨p, _, honly⟩ := hu
  exact rightNeighbor_ne_self_of_one_lt ring hn e
    ((honly _ hr).trans (honly _ hl).symm)

/-- Every semantically safe old configuration remains safe for the new
protocol, even when no RowSafe membership certificate has been supplied. -/
theorem isSafe_of_old_isSafe (hψ : 0 < ψ) (hn : 1 < n) (ring : DirectedRing n)
    (C : Fin n → UCell ψ κ)
    (hC : PopulationProtocol.IsSafe (LabelFreeElimination.protocol hψ κ) ring C id) :
    PopulationProtocol.IsSafe (protocol hψ κ) ring C id := by
  have hreach : ∀ D, PopulationProtocol.Reachable (protocol hψ κ) ring C D →
      PopulationProtocol.Reachable (LabelFreeElimination.protocol hψ κ) ring C D := by
    intro D hD
    induction hD with
    | refl => exact .refl _
    | step D E _ hstep ih =>
        have hout := hC.2 D ih
        have hu : hasUniqueLeader n (observe D) := by
          obtain ⟨p, hp, honly⟩ := hC.1
          refine ⟨p, (hout p).trans hp, ?_⟩
          intro i hi
          exact honly i ((hout i).symm.trans hi)
        obtain ⟨e, rfl⟩ := hstep
        exact .step _ _ _ ih ⟨e, unique_step_eq_old hψ hn ring D hu e⟩
  exact ⟨hC.1, fun D hD => hC.2 D (hreach D hD)⟩

/-- The already checked signal-safe class is closed for this new row. -/
theorem signalSafe_step (hψ : 0 < ψ) (hn : 1 < n) (ring : DirectedRing n)
    (C : Fin n → UCell ψ κ) (hC : SignalSafe ring C) (e : Fin n) :
    SignalSafe ring (step hψ ring C e) := by
  rw [unique_step_eq_old hψ hn ring C hC.1.unique_leader e]
  exact LabelFreeElimination.signalSafe_step hψ hn ring C hC e

theorem step_output (hψ : 0 < ψ) (hn : 1 < n) (ring : DirectedRing n)
    (C : Fin n → UCell ψ κ) (hC : SignalSafe ring C) (e i : Fin n) :
    LDSinkUnifiedFinite.output (step hψ ring C e i) = LDSinkUnifiedFinite.output (C i) := by
  rw [unique_step_eq_old hψ hn ring C hC.1.unique_leader e]
  exact LabelFreeElimination.step_output hψ ring C hC e i

theorem signalSafe_closed (hψ : 0 < ψ) (hn : 1 < n) (ring : DirectedRing n) :
    PopulationProtocol.ClosedPred (protocol hψ κ) ring (SignalSafe ring) := by
  intro C hC D hstep
  obtain ⟨e, rfl⟩ := hstep
  exact signalSafe_step hψ hn ring C hC e

/-- Semantic output safety: every reachable physical configuration has the
same unique leader. No arming or future-closure assumption is supplied. -/
theorem isSafe (hψ : 0 < ψ) (hn : 1 < n) (ring : DirectedRing n)
    (C : Fin n → UCell ψ κ) (hC : SignalSafe ring C) :
    PopulationProtocol.IsSafe (protocol hψ κ) ring C id := by
  apply isSafe_of_operational_legitimacy (protocol hψ κ) ring id
    (SignalSafe ring) (signalSafe_closed hψ hn ring)
  · intro D hD; exact hD.1.unique_leader
  · intro D hD E hstep i
    obtain ⟨e, rfl⟩ := hstep
    exact step_output hψ hn ring D hD e i
  · exact hC

theorem signalSafe_run (hψ : 0 < ψ) (hn : 1 < n) (ring : DirectedRing n)
    (C : Fin n → UCell ψ κ) (hC : SignalSafe ring C) (es : List (Fin n)) :
    SignalSafe ring (run (step hψ ring) C es) := by
  induction es generalizing C with
  | nil => exact hC
  | cons e es ih => exact ih _ (signalSafe_step hψ hn ring C hC e)

/-- The collision successor uses the ordinary two-site physical update. -/
theorem step_of_adjacent (hψ : 0 < ψ) (ring : DirectedRing n)
    (C : Fin n → UCell ψ κ) (e : Fin n)
    (hl : (C e).legacy.leader = true)
    (hr : (C (ring.rightNeighbor e)).legacy.leader = true) :
    step hψ ring C e = fun i =>
      if i = e then putSignals (C e) { observeCell (C e) with leader := false, signal_B := 0 }
      else if i = ring.rightNeighbor e then
        putSignals (C (ring.rightNeighbor e))
          { observeCell (C (ring.rightNeighbor e)) with shield := true, signal_B := 0 }
      else C i := by
  funext i
  simp only [step, PopulationProtocol.step, protocol, row_of_adjacent hψ _ _ hl hr]

theorem adjacent_deletes_source (hψ : 0 < ψ) (ring : DirectedRing n)
    (C : Fin n → UCell ψ κ) (e : Fin n)
    (hl : (C e).legacy.leader = true)
    (hr : (C (ring.rightNeighbor e)).legacy.leader = true) :
    (step hψ ring C e e).legacy.leader = false := by
  rw [step_of_adjacent hψ ring C e hl hr]
  simp [putSignals]

/-- Every adjacent firing lowers the actual count by exactly one. -/
theorem adjacent_count_drop (hψ : 0 < ψ) (ring : DirectedRing n)
    (C : Fin n → UCell ψ κ) (e : Fin n)
    (hl : (C e).legacy.leader = true)
    (hr : (C (ring.rightNeighbor e)).legacy.leader = true) :
    K2GlobalGapClosure.physicalLeaderCount (observe (step hψ ring C e)) + 1 =
      K2GlobalGapClosure.physicalLeaderCount (observe C) := by
  have hd := adjacent_deletes_source hψ ring C e hl hr
  have heq : (fun i => if (observe C i).leader then 1 else 0) =
      (fun i => (if (observe (step hψ ring C e) i).leader then 1 else 0) +
        (if i = e then 1 else 0)) := by
    funext i
    change (if (C i).legacy.leader then 1 else 0) =
      (if (step hψ ring C e i).legacy.leader then 1 else 0) + (if i = e then 1 else 0)
    by_cases hi : i = e
    · subst i; simp [hl, hd]
    · rw [step_leader_away hψ ring C e i hi]; simp [hi]
  unfold K2GlobalGapClosure.physicalLeaderCount
  rw [heq, ofFn_sum_add, sum_indicator]

/-- The two old leaders are exactly the colliding endpoints. This is a
present-state condition, with no future or terminal assertion. -/
def LastPair (ring : DirectedRing n) (C : Fin n → UCell ψ κ) (e : Fin n) : Prop :=
  (C e).legacy.leader = true ∧ (C (ring.rightNeighbor e)).legacy.leader = true ∧
    ∀ i, (C i).legacy.leader = true → i = e ∨ i = ring.rightNeighbor e

theorem lastPair_unique (hψ : 0 < ψ) (hn : 1 < n) (ring : DirectedRing n)
    (C : Fin n → UCell ψ κ) (e : Fin n) (hC : LastPair ring C e) :
    hasUniqueLeader n (observe (step hψ ring C e)) := by
  have hne := rightNeighbor_ne_self_of_one_lt ring hn e
  refine ⟨ring.rightNeighbor e, ?_, ?_⟩
  · exact (step_leader_away hψ ring C e _ hne).trans hC.2.1
  · intro i hi
    rcases hC.2.2 i (step_leader_source hψ ring C e i hi) with he | hr
    · subst i
      have hd := adjacent_deletes_source hψ ring C e hC.1 hC.2.1
      change (step hψ ring C e e).legacy.leader = true at hi
      simp_all
    · exact hr

theorem adjacent_shield (hψ : 0 < ψ) (hn : 1 < n) (ring : DirectedRing n)
    (C : Fin n → UCell ψ κ) (e : Fin n)
    (hl : (C e).legacy.leader = true)
    (hr : (C (ring.rightNeighbor e)).legacy.leader = true) :
    (step hψ ring C e (ring.rightNeighbor e)).legacy.shield = true := by
  rw [step_of_adjacent hψ ring C e hl hr]
  simp [rightNeighbor_ne_self_of_one_lt ring hn e, putSignals]

/-- Both endpoint signals become zero; any pre-existing zero elsewhere is
preserved. Thus the repair cannot introduce a dirty peaceful-bullet trail. -/
theorem adjacent_signal_zero (hψ : 0 < ψ) (ring : DirectedRing n)
    (C : Fin n → UCell ψ κ) (e i : Fin n)
    (hl : (C e).legacy.leader = true)
    (hr : (C (ring.rightNeighbor e)).legacy.leader = true)
    (hi : i = e ∨ i = ring.rightNeighbor e ∨ (C i).legacy.signal_B = 0) :
    (step hψ ring C e i).legacy.signal_B = 0 := by
  rw [step_of_adjacent hψ ring C e hl hr]
  by_cases he : i = e
  · simp [he, putSignals]
  · by_cases hr : i = ring.rightNeighbor e
    · simp only [if_neg he, if_pos hr]; rfl
    · simp only [if_neg he, if_neg hr]
      exact hi.resolve_left he |>.resolve_left hr

/-- A concrete sufficient state condition for the existing signal safe set.
Any live bullets are allowed when every signal is zero and the sole leader
is shielded; the bounded clockwise witness is derived from actual geometry. -/
theorem safe_of_zero_signals (ring : DirectedRing n) (C : Fin n → UCell ψ κ)
    (hu : hasUniqueLeader n (observe C))
    (hs : ∀ i, (C i).legacy.leader = true → (C i).legacy.shield = true)
    (hz : ∀ i, (C i).legacy.signal_B = 0) : SignalSafe ring C := by
  have ho : OutputSafeConfig (by decide) ring (observe C) := by
    refine
      { unique_leader := hu
        leader_label_zero := ?_
        no_nonpeaceful_bullet := ?_
        no_free_barrier := ?_ }
    · intro i _; exact Subsingleton.elim _ _
    · intro i hi
      obtain ⟨p, hp, _⟩ := hu
      refine ⟨hi, cwDist ring i p, cwDist_lt ring i p, ?_, ?_, ?_, ?_⟩
      · change (observe C (cwPos ring i (cwDist ring i p))).isLeader
        rw [cwPos_cwDist]; exact hp
      · change (observe C (cwPos ring i (cwDist ring i p))).shield = true
        rw [cwPos_cwDist]; exact hs p hp
      · intro k _; exact hz _
      · intro k _; exact Subsingleton.elim _ _
    · intro i
      dsimp only
      intro hi
      exact False.elim (hi (Subsingleton.elim _ _))
  exact rowSafe_of_outputSafe (by decide) ring (observe C) ho

/-- Last-adjacent-pair cleanup on any nontrivial ring. All exterior signals
are zero; exterior bullets, physical labels and controllers are arbitrary.
The retained losing bullet is now peaceful, so the result is future-safe. -/
theorem lastPair_zero_safe (hψ : 0 < ψ) (hn : 1 < n) (ring : DirectedRing n)
    (C : Fin n → UCell ψ κ) (e : Fin n) (hC : LastPair ring C e)
    (hz : ∀ i, i ≠ e → i ≠ ring.rightNeighbor e → (C i).legacy.signal_B = 0) :
    SignalSafe ring (step hψ ring C e) := by
  have hu := lastPair_unique hψ hn ring C e hC
  apply safe_of_zero_signals ring _ hu
  · intro i hi
    have heq := hu.choose_spec.2 i hi
    have hr := hu.choose_spec.2 (ring.rightNeighbor e)
      ((step_leader_away hψ ring C e _ (rightNeighbor_ne_self_of_one_lt ring hn e)).trans
        hC.2.1)
    rw [heq.trans hr.symm]
    exact adjacent_shield hψ hn ring C e hC.1 hC.2.1
  · intro i
    apply adjacent_signal_zero hψ ring C e i hC.1 hC.2.1
    by_cases he : i = e
    · exact Or.inl he
    · by_cases hr : i = ring.rightNeighbor e
      · exact Or.inr (Or.inl hr)
      · exact Or.inr (Or.inr (hz i he hr))

theorem fin2_endpoints (ring : DirectedRing 2) (e i : Fin 2) :
    i = e ∨ i = ring.rightNeighbor e := by
  have heq : ring = FixedPoint.ring2 := Subsingleton.elim _ _
  subst ring
  rcases fin2_cases e with rfl | rfl <;>
    rcases fin2_cases i with rfl | rfl <;> decide

/-- On n=2 this service has no signal, shield or bullet precondition at all.
Both actual scheduler edges produce the checked closed signal safe class. -/
theorem n2_collision_safe (hψ : 0 < ψ) (ring : DirectedRing 2)
    (C : Fin 2 → UCell ψ κ) (hl : ∀ i, (C i).legacy.leader = true) (e : Fin 2) :
    SignalSafe ring (step hψ ring C e) := by
  apply lastPair_zero_safe hψ (by decide) ring C e
  · exact ⟨hl e, hl _, fun i _ => fin2_endpoints ring e i⟩
  · intro i he hr
    exact False.elim ((fin2_endpoints ring e i).elim he hr)

theorem n2_collision_isSafe (hψ : 0 < ψ) (ring : DirectedRing 2)
    (C : Fin 2 → UCell ψ κ) (hl : ∀ i, (C i).legacy.leader = true) (e : Fin 2) :
    PopulationProtocol.IsSafe (protocol hψ κ) ring (step hψ ring C e) id :=
  isSafe hψ (by decide) ring _ (n2_collision_safe hψ ring C hl e)

/-- Every nonempty physical scheduler word from two n=2 leaders reaches and
stays inside the proved safe class. This is stronger than a local count drop. -/
theorem n2_nonempty_run_safe (hψ : 0 < ψ) (ring : DirectedRing 2)
    (C : Fin 2 → UCell ψ κ) (hl : ∀ i, (C i).legacy.leader = true)
    (e : Fin 2) (es : List (Fin 2)) :
    SignalSafe ring (run (step hψ ring) C (e :: es)) :=
  signalSafe_run hψ (by decide) ring _ (n2_collision_safe hψ ring C hl e) es

/-- The collision retains both bullets, and every exterior bullet. -/
theorem adjacent_bullet (hψ : 0 < ψ) (ring : DirectedRing n)
    (C : Fin n → UCell ψ κ) (e i : Fin n)
    (hl : (C e).legacy.leader = true)
    (hr : (C (ring.rightNeighbor e)).legacy.leader = true) :
    (step hψ ring C e i).legacy.bullet = (C i).legacy.bullet := by
  rw [step_of_adjacent hψ ring C e hl hr]
  dsimp only
  split
  · rename_i hi; subst i; rfl
  · split
    · rename_i hi; subst i; rfl
    · rfl

private theorem adjacent_peaceful_of_path (hψ : 0 < ψ) (hn : 1 < n)
    (ring : DirectedRing n) (C : Fin n → UCell ψ κ) (e i : Fin n)
    (hl : (C e).legacy.leader = true)
    (hr : (C (ring.rightNeighbor e)).legacy.leader = true)
    (hb : (observe (step hψ ring C e) i).bullet = 2)
    (d : Nat) (hd : d < n) (ht : cwPos ring i d = ring.rightNeighbor e)
    (hz : ∀ k, k ≤ d → cwPos ring i k = e ∨
      cwPos ring i k = ring.rightNeighbor e ∨ (C (cwPos ring i k)).legacy.signal_B = 0) :
    isPeacefulBullet (by decide) ring (observe (step hψ ring C e)) i := by
  refine ⟨hb, d, hd, ?_, ?_, ?_, ?_⟩
  · change (step hψ ring C e (cwPos ring i d)).legacy.leader = true
    rw [ht]
    exact (step_leader_away hψ ring C e _ (rightNeighbor_ne_self_of_one_lt ring hn e)).trans hr
  · change (step hψ ring C e (cwPos ring i d)).legacy.shield = true
    rw [ht]
    exact adjacent_shield hψ hn ring C e hl hr
  · intro k hk
    exact adjacent_signal_zero hψ ring C e (cwPos ring i k) hl hr (hz k hk)
  · intro k _; exact Subsingleton.elim _ _

/-- Exterior live bullets already have actual peaceful paths to one of the
two leaders. Local bullets and signals are unrestricted: the row repairs
both endpoints. This is a present signal-path condition, not a closure field. -/
def ExteriorPeaceful (ring : DirectedRing n) (C : Fin n → UCell ψ κ) (e : Fin n) : Prop :=
  ∀ i, i ≠ e → i ≠ ring.rightNeighbor e → (observe C i).bullet = 2 →
    isPeacefulBullet (by decide) ring (observe C) i

/-- The removed leader's old peaceful paths extend by one actual clockwise
edge to the survivor. They cannot wrap a full ring, since their starting
bullet is not at the survivor. Local live bullets get length-one/zero paths.
This discharges the future-safety obligation without deleting either bullet. -/
theorem lastPair_peaceful_safe (hψ : 0 < ψ) (hn : 1 < n) (ring : DirectedRing n)
    (C : Fin n → UCell ψ κ) (e : Fin n) (hC : LastPair ring C e)
    (hp : ExteriorPeaceful ring C e) : SignalSafe ring (step hψ ring C e) := by
  have ho : OutputSafeConfig (by decide) ring (observe (step hψ ring C e)) := by
    refine
      { unique_leader := lastPair_unique hψ hn ring C e hC
        leader_label_zero := ?_
        no_nonpeaceful_bullet := ?_
        no_free_barrier := ?_ }
    · intro i _; exact Subsingleton.elim _ _
    · intro i hb
      by_cases hie : i = e
      · subst i
        apply adjacent_peaceful_of_path hψ hn ring C e e hC.1 hC.2.1 hb 1 hn
        · exact (cwPos_succ ring e 0).trans (congrArg ring.rightNeighbor (cwPos_zero ring e))
        · intro k hk
          have hk' : k = 0 ∨ k = 1 := by omega
          rcases hk' with rfl | rfl
          · exact Or.inl (cwPos_zero ring e)
          · exact Or.inr (Or.inl
              ((cwPos_succ ring e 0).trans (congrArg ring.rightNeighbor (cwPos_zero ring e))))
      · by_cases hir : i = ring.rightNeighbor e
        · subst i
          apply adjacent_peaceful_of_path hψ hn ring C e _ hC.1 hC.2.1 hb 0 ring.hn
          · exact cwPos_zero ring _
          · intro k hk
            have hk0 : k = 0 := by omega
            subst k
            exact Or.inr (Or.inl (cwPos_zero ring _))
        · have hpre : (observe C i).bullet = 2 := by
            change (C i).legacy.bullet = 2
            rw [← adjacent_bullet hψ ring C e i hC.1 hC.2.1]
            exact hb
          obtain ⟨_, d, hd, ht, _, hz, _⟩ := hp i hie hir hpre
          change (C (cwPos ring i d)).legacy.leader = true at ht
          rcases hC.2.2 _ ht with hte | htr
          · have ht' : cwPos ring i (d + 1) = ring.rightNeighbor e := by
              rw [cwPos_succ, hte]
            have hd' : d + 1 < n := by
              apply Classical.byContradiction
              intro hbad
              have heq : d + 1 = n := by omega
              have hcycle : cwPos ring i n = i := by
                apply Fin.ext
                simp [cwPos, Nat.mod_eq_of_lt i.isLt]
              rw [heq, hcycle] at ht'
              exact hir ht'
            apply adjacent_peaceful_of_path hψ hn ring C e i hC.1 hC.2.1 hb (d + 1) hd' ht'
            intro k hk
            by_cases hkd : k ≤ d
            · exact Or.inr (Or.inr (hz k hkd))
            · have hke : k = d + 1 := by omega
              subst k
              exact Or.inr (Or.inl ht')
          · apply adjacent_peaceful_of_path hψ hn ring C e i hC.1 hC.2.1 hb d hd htr
            intro k hk
            exact Or.inr (Or.inr (hz k hk))
    · intro i
      dsimp only
      intro hi
      exact False.elim (hi (Subsingleton.elim _ _))
  exact rowSafe_of_outputSafe (by decide) ring _ ho

theorem lastPair_peaceful_isSafe (hψ : 0 < ψ) (hn : 1 < n) (ring : DirectedRing n)
    (C : Fin n → UCell ψ κ) (e : Fin n) (hC : LastPair ring C e)
    (hp : ExteriorPeaceful ring C e) :
    PopulationProtocol.IsSafe (protocol hψ κ) ring (step hψ ring C e) id :=
  isSafe hψ hn ring _ (lastPair_peaceful_safe hψ hn ring C e hC hp)

noncomputable section

/-- Actual finite-row execution stopped only after entering the already
proved SignalSafe class. StopNode supplies ordinary terminal padding. -/
def safeStep (hψ : 0 < ψ) (ring : DirectedRing n)
    (C : Fin n → UCell ψ κ) (e : Fin n) : StopNode (Fin n → UCell ψ κ) := by
  classical
  let C' := step hψ ring C e
  exact if SignalSafe ring C' then .success else .active C'

theorem safeStep_success (hψ : 0 < ψ) (ring : DirectedRing n)
    (C : Fin n → UCell ψ κ) (e : Fin n) (hs : SignalSafe ring (step hψ ring C e)) :
    safeStep hψ ring C e = .success := by
  simp only [safeStep, if_pos hs]

/-- Padding a successful stopped leaf has the correct physical semantics:
every actual suffix stays SignalSafe and is semantically safe. -/
theorem safeStep_success_suffix (hψ : 0 < ψ) (hn : 1 < n) (ring : DirectedRing n)
    (C : Fin n → UCell ψ κ) (e : Fin n) (hs : safeStep hψ ring C e = .success)
    (es : List (Fin n)) :
    PopulationProtocol.IsSafe (protocol hψ κ) ring (run (step hψ ring) C (e :: es)) id := by
  have hsafe : SignalSafe ring (step hψ ring C e) := by
    classical
    unfold safeStep at hs
    dsimp only at hs
    split at hs
    · assumption
    · cases hs
  exact isSafe hψ hn ring _ (signalSafe_run hψ hn ring _ hsafe es)

/-- Exact full mass at every positive horizon: all 2^(T+1) physical words
from two n=2 leaders succeed after their first edge. -/
theorem n2_successCount (hψ : 0 < ψ) (ring : DirectedRing 2)
    (C : Fin 2 → UCell ψ κ) (hl : ∀ i, (C i).legacy.leader = true) (T : Nat) :
    successCount (safeStep hψ ring) (.active C) (T + 1) = 2 ^ (T + 1) := by
  change (List.ofFn (fun e : Fin 2 =>
    treeWeight (safeStep hψ ring) successWeight (safeStep hψ ring C e) T)).sum = _
  have heq := ofFn_sum_eq
    (fun e : Fin 2 => treeWeight (safeStep hψ ring) successWeight (safeStep hψ ring C e) T)
    (fun _ : Fin 2 => 2 ^ T) (fun e => by
      rw [safeStep_success hψ ring C e (n2_collision_safe hψ ring C hl e), treeWeight_success]
      simp [successWeight])
  rw [heq, FiniteUniformStoppingTree.ofFn_sum_const]
  simp [Nat.pow_succ, Nat.mul_comm]

/-- A single actual successful edge contributes n^T padded words. -/
theorem successCount_of_safe_edge (hψ : 0 < ψ) (ring : DirectedRing n)
    (C : Fin n → UCell ψ κ) (e : Fin n)
    (hs : SignalSafe ring (step hψ ring C e)) (T : Nat) :
    n ^ T ≤ successCount (safeStep hψ ring) (.active C) (T + 1) := by
  have hle := ofFn_sum_le
    (fun j : Fin n => n ^ T * (if j = e then 1 else 0))
    (fun j : Fin n => treeWeight (safeStep hψ ring) successWeight (safeStep hψ ring C j) T)
    (fun j => by
      by_cases hj : j = e
      · subst j
        rw [safeStep_success hψ ring C e hs, treeWeight_success]
        simp [successWeight]
      · simp [hj])
  rw [ofFn_sum_mul_left, sum_indicator, Nat.mul_one] at hle
  exact hle

/-- For a final adjacent pair with genuine exterior peaceful paths, the
same raw scheduler has success mass at least 1/n at every positive horizon.
No inequality is an input: the chosen physical firing and safe suffix prove it. -/
theorem lastPair_successCount (hψ : 0 < ψ) (hn : 1 < n) (ring : DirectedRing n)
    (C : Fin n → UCell ψ κ) (e : Fin n) (hC : LastPair ring C e)
    (hp : ExteriorPeaceful ring C e) (T : Nat) :
    n ^ T ≤ successCount (safeStep hψ ring) (.active C) (T + 1) :=
  successCount_of_safe_edge hψ ring C e (lastPair_peaceful_safe hψ hn ring C e hC hp) T

/-- The existing stopped tagged-deletion process, using the new physical
row. The stopping predicate and the underlying finite tree are unchanged. -/
def raceStep (hψ : 0 < ψ) (F : TwoGapFrame n)
    (C : Fin n → UCell ψ κ) (e : Fin n) : StopNode (Fin n → UCell ψ κ) := by
  classical
  let C' := step hψ F.attack.ring C e
  exact if NoResetSuccess F (physicalConfig C') then .success else .active C'

/-- Exact stopped-count simulation on the existing separated configurations,
including every original deletion, for the same scheduler and horizon. -/
theorem separated_race_count (hψ : 0 < ψ) (F : TwoGapFrame n)
    (C : Fin n → UCell ψ κ)
    (hs : K2GlobalGapClosure.Separated F.attack.ring (observe C)) (T : Nat) :
    successCount (raceStep hψ F) (.active C) T =
      successCount (LabelFreeElimination.blockStep hψ F) (.active C) T := by
  classical
  induction T generalizing C with
  | zero => rfl
  | succ T ih =>
      change (List.ofFn (fun e => treeWeight (raceStep hψ F) successWeight
        (raceStep hψ F C e) T)).sum =
        (List.ofFn (fun e => treeWeight (LabelFreeElimination.blockStep hψ F) successWeight
          (LabelFreeElimination.blockStep hψ F C e) T)).sum
      apply ofFn_sum_eq
      intro e
      have heq := separated_step_eq_old hψ F.attack.ring C hs e
      have hs' := separated_step hψ F.attack.ring C hs e
      rw [heq] at hs'
      simp only [raceStep, LabelFreeElimination.blockStep, heq]
      split
      · simp only [treeWeight_success]
      · exact ih _ hs'

/-- The checked 1/16 GapPair+RaceReady mass transfers on the separated
physical class. This is tagged deletion mass, not a semantic terminal claim. -/
theorem separated_race_mass (hψ : 0 < ψ) (F : TwoGapFrame n)
    (C : Fin n → UCell ψ κ)
    (hs : K2GlobalGapClosure.Separated F.attack.ring (observe C))
    (hg : GapPair (by decide) F ⟨observe C, .transit⟩)
    (hr : RaceReady F (physicalConfig C)) :
    n ^ (4 * n) ≤ 16 * successCount (raceStep hψ F) (.active C) (4 * n) := by
  rw [separated_race_count hψ F C hs]
  exact LabelFreeElimination.race_mass hψ F C hg hr

end

/-- Track a fixed adjacent physical pair until either endpoint ceases to be
a leader. The edge is a proof parameter, not stored in any agent. This is
deletion service, deliberately distinct from the safe-terminal stopped tree. -/
def pairStep (hψ : 0 < ψ) (ring : DirectedRing n) (e : Fin n)
    (C : Fin n → UCell ψ κ) (j : Fin n) : StopNode (Fin n → UCell ψ κ) :=
  let D := step hψ ring C j
  if (D e).legacy.leader = true ∧ (D (ring.rightNeighbor e)).legacy.leader = true
  then .active D else .success

/-- Its terminal is an actual missing leader at one of the fixed endpoints. -/
theorem pairStep_success_iff (hψ : 0 < ψ) (ring : DirectedRing n) (e : Fin n)
    (C : Fin n → UCell ψ κ) (j : Fin n) :
    pairStep hψ ring e C j = .success ↔
      (step hψ ring C j e).legacy.leader = false ∨
      (step hψ ring C j (ring.rightNeighbor e)).legacy.leader = false := by
  cases hl : (step hψ ring C j e).legacy.leader <;>
    cases hr : (step hψ ring C j (ring.rightNeighbor e)).legacy.leader <;>
    simp [pairStep, hl, hr]

/-- Selecting the actual adjacent edge always finishes this service. If
one endpoint was already deleted, no-follower-creation retains that success. -/
theorem pairStep_target (hψ : 0 < ψ) (ring : DirectedRing n) (e : Fin n)
    (C : Fin n → UCell ψ κ) : pairStep hψ ring e C e = .success := by
  apply (pairStep_success_iff hψ ring e C e).mpr
  cases hl : (C e).legacy.leader
  · exact Or.inl (step_follower hψ ring C e e hl)
  · cases hr : (C (ring.rightNeighbor e)).legacy.leader
    · exact Or.inr (step_follower hψ ring C e _ hr)
    · exact Or.inl (adjacent_deletes_source hψ ring C e hl hr)

private def pairPotential (n : Nat) : StopNode (Fin n → UCell ψ κ) → Nat
  | .active _ => n
  | .success => 0
  | .failure => 0

/-- The finite Bellman row is derived from the physical target firing and
nonnegative extra edges, rather than assumed as a protocol interface. -/
private theorem pair_super (hψ : 0 < ψ) (ring : DirectedRing n) (e : Fin n) :
    NatBellmanSuperSolution (pairStep (κ := κ) hψ ring e) 1 (pairPotential n) := by
  refine ⟨rfl, rfl, ?_⟩
  intro C
  have hh := ofFn_sum_le
    (fun j : Fin n => pairPotential n (pairStep hψ ring e C j) + n * (if j = e then 1 else 0))
    (fun _ : Fin n => n) (fun j => by
      by_cases hj : j = e
      · subst j
        rw [pairStep_target]
        simp [pairPotential]
      · simp only [if_neg hj, Nat.mul_zero, Nat.add_zero]
        cases pairStep hψ ring e C j <;> simp [pairPotential])
  rw [ofFn_sum_add, ofFn_sum_mul_left, sum_indicator, Nat.mul_one,
    FiniteUniformStoppingTree.ofFn_sum_const] at hh
  change 1 * n + (List.ofFn (fun j => pairPotential n (pairStep hψ ring e C j))).sum ≤ n * n
  omega

/-- Exact finite truncated-cost bound: after division by n^T the expected
active interactions before tagged-pair deletion are at most n. -/
theorem pair_truncated_cost (hψ : 0 < ψ) (ring : DirectedRing n) (e : Fin n)
    (C : Fin n → UCell ψ κ) (T : Nat) :
    truncatedActiveCostNumerator (pairStep hψ ring e) (.active C) T ≤ n ^ T * n := by
  simpa [pairPotential] using
    truncatedActiveCostNumerator_mul_le_of_natSuperSolution
      (pairStep hψ ring e) 1 (pairPotential n) (pair_super hψ ring e) (.active C) T

theorem pair_failureCount (hψ : 0 < ψ) (ring : DirectedRing n) (e : Fin n)
    (C : Fin n → UCell ψ κ) (T : Nat) :
    failureCount (pairStep hψ ring e) (.active C) T = 0 := by
  induction T generalizing C with
  | zero => rfl
  | succ T ih =>
      change (List.ofFn (fun j => treeWeight (pairStep hψ ring e) failureWeight
        (pairStep hψ ring e C j) T)).sum = 0
      have heq := ofFn_sum_eq
        (fun j => treeWeight (pairStep hψ ring e) failureWeight (pairStep hψ ring e C j) T)
        (fun _ : Fin n => 0) (fun j => by
          unfold pairStep
          dsimp only
          split
          · exact ih _
          · simp [treeWeight_success, failureWeight])
      rw [heq, FiniteUniformStoppingTree.ofFn_sum_const, Nat.mul_zero]

/-- At least half the real scheduler words delete one of a fixed adjacent
pair by 2*n. If both were initially leaders this is physical deletion; the
result does not identify that event with SignalSafe. -/
theorem pair_service_half (hψ : 0 < ψ) (ring : DirectedRing n) (e : Fin n)
    (C : Fin n → UCell ψ κ) :
    n ^ (2 * n) ≤ 2 * successCount (pairStep hψ ring e) (.active C) (2 * n) := by
  have hc := pair_truncated_cost hψ ring e C (2 * n)
  have ht := horizon_mul_activeCount_le_truncatedActiveCostNumerator
    (pairStep hψ ring e) (.active C) (2 * n)
  have hm : n * (2 * activeCount (pairStep hψ ring e) (.active C) (2 * n)) ≤
      n * n ^ (2 * n) := by
    calc
      _ = (2 * n) * activeCount (pairStep hψ ring e) (.active C) (2 * n) := by ac_rfl
      _ ≤ truncatedActiveCostNumerator (pairStep hψ ring e) (.active C) (2 * n) := ht
      _ ≤ n ^ (2 * n) * n := hc
      _ = _ := by ac_rfl
  have hh := Nat.le_of_mul_le_mul_left hm ring.hn
  have hp := node_count_partition (pairStep hψ ring e) (.active C) (2 * n)
  rw [pair_failureCount] at hp
  omega

namespace FieldNecessity

theorem ring3 : DirectedRing 3 := ⟨by decide⟩

/-- An ablation of exactly one additional collision write: 0 retains the
loser's signal, 1 retains the winner's signal, 2 retains the winner's shield.
This is only a comparison family, not the proposed protocol row. -/
def omittedRow (missing : Fin 3) (hψ : 0 < ψ) (l r : UCell ψ κ) :
    UCell ψ κ × UCell ψ κ :=
  let q := collisionRow hψ l r
  if l.legacy.leader = true ∧ r.legacy.leader = true then
    if missing = 0 then
      (putSignals q.1 { observeCell q.1 with signal_B := l.legacy.signal_B }, q.2)
    else if missing = 1 then
      (q.1, putSignals q.2 { observeCell q.2 with signal_B := r.legacy.signal_B })
    else
      (q.1, putSignals q.2 { observeCell q.2 with shield := r.legacy.shield })
  else q

def omittedProtocol (missing : Fin 3) : PopulationProtocol where
  Q := UCell 2 1
  Y := Bool
  transition := omittedRow missing (by decide)
  output := LDSinkUnifiedFinite.output

/-- Real labels are all one on n=3, psi=2. Local bullets/signals are
unrestricted by ExteriorPeaceful; no exterior live bullet occurs here. -/
def seed (missing : Fin 3) (i : Fin 3) : UCell 2 1 :=
  { legacy := { boundedCanonical (by decide) 1 i with
      leader := decide (i = 0 ∨ i = 1), label := 1, shield := false,
      bullet := if i = 0 then 2 else 0,
      signal_B := if (missing = 0 ∧ i = 0) ∨ (missing = 1 ∧ i = 1) then 1 else 0 }
    control := (finiteCut 0).control }

theorem nondivisible : ¬ 2 ∣ 3 := by decide

theorem lastPair (missing : Fin 3) : LastPair ring3 (seed missing) 0 := by
  rcases fin3_cases missing with rfl | rfl | rfl <;> unfold LastPair <;> decide

theorem exterior (missing : Fin 3) : ExteriorPeaceful ring3 (seed missing) 0 := by
  intro i he hr hb
  change (if i = 0 then (2 : Fin 3) else 0) = 2 at hb
  simp [he] at hb

/-- Each of the three added writes is necessary if bullets are retained and
the other two writes are kept: omitting it has an actual extinction word. -/
theorem omit_loser_signal_fails : ∀ i : Fin 3,
    (run ((omittedProtocol 0).step ring3) (seed 0) [0, 2, 0, 0, 1] i).legacy.leader = false := by
  decide

theorem omit_winner_signal_fails : ∀ i : Fin 3,
    (run ((omittedProtocol 1).step ring3) (seed 1) [0, 2, 0, 1] i).legacy.leader = false := by
  decide

theorem omit_winner_shield_fails : ∀ i : Fin 3,
    (run ((omittedProtocol 2).step ring3) (seed 2) [0, 2, 1] i).legacy.leader = false := by
  decide

/-- The actual row handles all three finite inputs and proves future output
safety while retaining the losing bullet. No physical label is normalized. -/
theorem repaired_safe (missing : Fin 3) :
    PopulationProtocol.IsSafe (protocol (by decide) 1) ring3
      (step (by decide) ring3 (seed missing) 0) id :=
  lastPair_peaceful_isSafe (by decide) (by decide) ring3 (seed missing) 0
    (lastPair missing) (exterior missing)

theorem retained_losing_bullet (missing : Fin 3) :
    (step (by decide) ring3 (seed missing) 0 0).legacy.bullet = 2 := by
  exact adjacent_bullet (by decide) ring3 (seed missing) 0 0
    (lastPair missing).1 (lastPair missing).2.1

end FieldNecessity

namespace ExteriorResidual

/-- Two adjacent leaders and one remote, signal-dirty live bullet. This
intentionally violates the exterior path hypothesis of the terminal lemma. -/
def seed (i : Fin 3) : UCell 2 1 :=
  { legacy := { boundedCanonical (by decide) 1 i with
      leader := decide (i = 0 ∨ i = 1), label := 1, shield := false,
      bullet := if i = 2 then 2 else 0,
      signal_B := if i = 2 then 1 else 0 }
    control := (finiteCut 0).control }

theorem lastPair : LastPair FieldNecessity.ring3 seed 0 := by unfold LastPair; decide

/-- Collision sanitation cannot repair arbitrary distant signal corruption.
The exact new row itself reaches zero leaders on this five-edge word. -/
theorem remote_dirty_extinction : ∀ i : Fin 3,
    (run (step (by decide) FieldNecessity.ring3) seed [0, 2, 0, 0, 1] i).legacy.leader = false := by
  decide

private theorem run_reachable (hψ : 0 < ψ) (ring : DirectedRing n)
    (C : Fin n → UCell ψ κ) (es : List (Fin n)) :
    PopulationProtocol.Reachable (protocol hψ κ) ring C (run (step hψ ring) C es) := by
  induction es generalizing C with
  | nil => exact .refl _
  | cons e es ih =>
      exact (PopulationProtocol.OneStep.to_reachable ⟨e, rfl⟩).trans (ih _)

/-- The limitation is semantic: after that collision the one remaining
leader is not safe under the actual new protocol. -/
theorem after_not_isSafe :
    ¬ PopulationProtocol.IsSafe (protocol (by decide) 1) FieldNecessity.ring3
      (step (by decide) FieldNecessity.ring3 seed 0) id := by
  intro h
  have heq := h.2 _ (run_reachable (by decide) FieldNecessity.ring3
    (step (by decide) FieldNecessity.ring3 seed 0) [2, 0, 0, 1]) 1
  change false = true at heq
  cases heq

end ExteriorResidual

end AdjacentLeaderElimination
