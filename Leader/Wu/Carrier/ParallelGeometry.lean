import Leader.Wu.Epoch.VoterPeriodColors

/-!
# Parallel geometry projection

The period-position repair need not own a separate protocol phase.  This file
couples it with an arbitrary control transition that may inspect both complete
endpoint states.  Every selected interaction repairs the responder position
and simultaneously runs the control row.  The position projection is exactly
`periodRepairStep`, independently of the control soup.

Consequently a successor grid is closed, and the existing finite-tree voter
bound applies unchanged to the full product protocol's position marginal.
The file deliberately imposes no convergence claim on the control row.
-/

namespace PPLLParallelGeometryLift

open PPLLResearchFormulation PPLLPeriodHColorVoter

set_option autoImplicit false
set_option warningAsError true

/-- One local state with exactly one stored `Fin h` position. -/
abbrev ParallelCell (h : Nat) (Control : Type) := Fin h × Control

/-- The position projection of a full configuration. -/
def positions {n h : Nat} {Control : Type}
    (q : Fin n -> ParallelCell h Control) : Fin n -> Fin h :=
  fun i => (q i).1

/-- A control row may inspect both complete endpoints, including their current
positions, but it returns only the two non-position control values. -/
abbrev ControlRow (h : Nat) (Control : Type) :=
  ParallelCell h Control -> ParallelCell h Control -> Control × Control

/-- One combined interaction.  The position row and arbitrary control row run
in parallel.  The initiator position is retained and the responder receives
its successor; no control output can alter either position. -/
def parallelStep {n h : Nat} {Control : Type} (hh : 0 < h)
    (ring : DirectedRing n) (control : ControlRow h Control)
    (q : Fin n -> ParallelCell h Control) (edge : Fin n) :
    Fin n -> ParallelCell h Control :=
  let out := control (q edge) (q (ring.rightNeighbor edge))
  fun i =>
    if i = edge then ((q edge).1, out.1)
    else if i = ring.rightNeighbor edge then
      (successorH hh (q edge).1, out.2)
    else q i

/-- The combined transition commutes exactly with position projection. -/
theorem positions_parallelStep {n h : Nat} {Control : Type} (hh : 0 < h)
    (ring : DirectedRing n) (control : ControlRow h Control)
    (q : Fin n -> ParallelCell h Control) (edge : Fin n) :
    positions (parallelStep hh ring control q edge) =
      periodRepairStep hh ring (positions q) edge := by
  funext i
  simp only [positions, parallelStep, periodRepairStep]
  by_cases hie : i = edge
  · simp [hie]
  · by_cases hir : i = ring.rightNeighbor edge
    · simp [hir]
    · simp [hie, hir]

/-- Position-grid legitimacy for the full product state. -/
def PositionGrid {n h : Nat} {Control : Type} (hh : 0 < h)
    (ring : DirectedRing n) (q : Fin n -> ParallelCell h Control) : Prop :=
  SuccessorGrid hh ring (positions q)

/-- Once the projected positions form a grid, every later combined step keeps
the same positions, even though the controls may continue changing. -/
theorem positions_parallelStep_eq_of_grid
    {n h : Nat} {Control : Type} (hh : 0 < h)
    (ring : DirectedRing n) (control : ControlRow h Control)
    (q : Fin n -> ParallelCell h Control) (hq : PositionGrid hh ring q)
    (edge : Fin n) :
    positions (parallelStep hh ring control q edge) = positions q := by
  rw [positions_parallelStep]
  exact periodRepairStep_eq_self_of_grid hh ring (positions q) hq edge

/-- The projected grid predicate is closed under every arbitrary control row. -/
theorem positionGrid_parallelStep
    {n h : Nat} {Control : Type} (hh : 0 < h)
    (ring : DirectedRing n) (control : ControlRow h Control)
    (q : Fin n -> ParallelCell h Control) (hq : PositionGrid hh ring q)
    (edge : Fin n) :
    PositionGrid hh ring (parallelStep hh ring control q edge) := by
  unfold PositionGrid
  rw [positions_parallelStep_eq_of_grid hh ring control q hq edge]
  exact hq

/-! ## Exact schedule projection -/

def runParallel {n h : Nat} {Control : Type} (hh : 0 < h)
    (ring : DirectedRing n) (control : ControlRow h Control) :
    (Fin n -> ParallelCell h Control) -> List (Fin n) ->
      (Fin n -> ParallelCell h Control)
  | q, [] => q
  | q, edge :: rest =>
      runParallel hh ring control (parallelStep hh ring control q edge) rest

def runPeriod {n h : Nat} (hh : 0 < h) (ring : DirectedRing n) :
    (Fin n -> Fin h) -> List (Fin n) -> (Fin n -> Fin h)
  | P, [] => P
  | P, edge :: rest =>
      runPeriod hh ring (periodRepairStep hh ring P edge) rest

/-- Every finite scheduler word has exactly the same position projection in
the product protocol and in the standalone period process. -/
theorem positions_runParallel {n h : Nat} {Control : Type} (hh : 0 < h)
    (ring : DirectedRing n) (control : ControlRow h Control)
    (q : Fin n -> ParallelCell h Control) (schedule : List (Fin n)) :
    positions (runParallel hh ring control q schedule) =
      runPeriod hh ring (positions q) schedule := by
  induction schedule generalizing q with
  | nil => rfl
  | cons edge rest ih =>
      simp only [runParallel, runPeriod]
      rw [ih, positions_parallelStep]

/-! ## Uniform-iid geometry bound for the product marginal -/

private theorem periodGridMissTree_zero_eq
    {n h : Nat} (hh : 0 < h) (hdvd : h ∣ n)
    (ring : DirectedRing n) (P : Fin n -> Fin h) :
    periodGridMissTree hh hdvd ring P 0 =
      @ite Nat (SuccessorGrid hh ring P) (Classical.propDecidable _) 0 1 := by
  unfold periodGridMissTree
  rw [finiteColorMissTree_zero]
  rw [show FiniteColorConsensus
        (offsetColors (periodCoordinate hh) P) = SuccessorGrid hh ring P from
    propext (successorGrid_iff_offset_consensus hh
      (Nat.le_of_dvd ring.hn hdvd) ring (periodCoordinate hh)
      (periodCoordinate_cyclic hh hdvd ring) P).symm]

private theorem periodGridMissTree_succ_eq
    {n h : Nat} (hh : 0 < h) (hdvd : h ∣ n)
    (ring : DirectedRing n) (P : Fin n -> Fin h) (t : Nat) :
    periodGridMissTree hh hdvd ring P (t + 1) =
      @ite Nat (SuccessorGrid hh ring P) (Classical.propDecidable _) 0
        ((List.ofFn (fun edge : Fin n =>
          periodGridMissTree hh hdvd ring
            (periodRepairStep hh ring P edge) t)).sum) := by
  unfold periodGridMissTree
  rw [finiteColorMissTree_succ]
  let coord : Fin n -> Fin h := periodCoordinate hh
  have hcoord : CyclicCoordinate hh ring coord :=
    periodCoordinate_cyclic hh hdvd ring
  rw [show FiniteColorConsensus (offsetColors coord P) =
      SuccessorGrid hh ring P from
    propext (successorGrid_iff_offset_consensus hh
      (Nat.le_of_dvd ring.hn hdvd) ring coord hcoord P).symm]
  have hchildren :
      (fun edge : Fin n => finiteColorMissTree
        (Nat.le_of_dvd ring.hn hdvd) ring
        (finiteColorStep ring (offsetColors coord P) edge) t) =
      (fun edge : Fin n => periodGridMissTree hh hdvd ring
        (periodRepairStep hh ring P edge) t) := by
    funext edge
    unfold periodGridMissTree
    rw [offsetColors_periodRepairStep hh ring coord hcoord]
  have hsums := congrArg (fun f => (List.ofFn f).sum) hchildren
  unfold periodGridMissTree at hsums
  by_cases hgrid : SuccessorGrid hh ring P
  · simp [hgrid]
  · rw [if_neg hgrid, if_neg hgrid]
    simpa [coord] using hsums

/-- Literal scheduler tree of the combined product, stopped at position-grid
entry.  Unlike `parallelGridMissTree` below, this definition executes the
arbitrary control row at every child. -/
noncomputable def rawParallelGridMissTree
    {n h : Nat} {Control : Type} (hh : 0 < h)
    (ring : DirectedRing n) (control : ControlRow h Control) :
    (Fin n -> ParallelCell h Control) -> Nat -> Nat
  | q, 0 =>
      @ite Nat (PositionGrid hh ring q) (Classical.propDecidable _) 0 1
  | q, t + 1 =>
      @ite Nat (PositionGrid hh ring q) (Classical.propDecidable _) 0
        ((List.ofFn (fun edge : Fin n =>
          rawParallelGridMissTree hh ring control
            (parallelStep hh ring control q edge) t)).sum)

noncomputable def parallelGridMissTree
    {n h : Nat} {Control : Type} (hh : 0 < h) (hdvd : h ∣ n)
    (ring : DirectedRing n) (q : Fin n -> ParallelCell h Control)
    (t : Nat) : Nat :=
  periodGridMissTree hh hdvd ring (positions q) t

/-- The full-state scheduler tree and standalone period tree have identical
miss counts at every horizon. -/
theorem rawParallelGridMissTree_eq
    {n h : Nat} {Control : Type} (hh : 0 < h) (hdvd : h ∣ n)
    (ring : DirectedRing n) (control : ControlRow h Control)
    (q : Fin n -> ParallelCell h Control) (t : Nat) :
    rawParallelGridMissTree hh ring control q t =
      parallelGridMissTree hh hdvd ring q t := by
  induction t generalizing q with
  | zero =>
      simp only [rawParallelGridMissTree, parallelGridMissTree]
      exact periodGridMissTree_zero_eq hh hdvd ring (positions q) |>.symm
  | succ t ih =>
      simp only [rawParallelGridMissTree, parallelGridMissTree]
      rw [periodGridMissTree_succ_eq hh hdvd ring (positions q) t]
      by_cases hgrid : PositionGrid hh ring q
      · have hsuccess : SuccessorGrid hh ring (positions q) := hgrid
        rw [if_pos hgrid, if_pos hsuccess]
      · have hsuccess : ¬SuccessorGrid hh ring (positions q) := hgrid
        rw [if_neg hgrid, if_neg hsuccess]
        have hchildren :
            (fun edge : Fin n => rawParallelGridMissTree hh ring control
              (parallelStep hh ring control q edge) t) =
            (fun edge : Fin n => periodGridMissTree hh hdvd ring
              (periodRepairStep hh ring (positions q) edge) t) := by
          funext edge
          rw [ih]
          unfold parallelGridMissTree
          rw [positions_parallelStep]
        rw [hchildren]

noncomputable def parallelGridWeightedMissTotal
    {n h : Nat} {Control : Type} (hh : 0 < h) (hdvd : h ∣ n)
    (ring : DirectedRing n) (q : Fin n -> ParallelCell h Control)
    (t : Nat) : Nat :=
  periodGridWeightedMissTotal hh hdvd ring (positions q) t

/-- Weighted survival sum computed from the literal full-state miss tree. -/
noncomputable def rawParallelGridWeightedMissTotal
    {n h : Nat} {Control : Type} (hh : 0 < h)
    (ring : DirectedRing n) (control : ControlRow h Control)
    (q : Fin n -> ParallelCell h Control) : Nat -> Nat
  | 0 => 0
  | t + 1 =>
      n * rawParallelGridWeightedMissTotal hh ring control q t +
        rawParallelGridMissTree hh ring control q t

private theorem periodGridWeightedMissTotal_succ_eq
    {n h : Nat} (hh : 0 < h) (hdvd : h ∣ n)
    (ring : DirectedRing n) (P : Fin n -> Fin h) (t : Nat) :
    periodGridWeightedMissTotal hh hdvd ring P (t + 1) =
      n * periodGridWeightedMissTotal hh hdvd ring P t +
        periodGridMissTree hh hdvd ring P t := by
  rfl

/-- The literal product tree has exactly the same weighted survival total as
the standalone period process. -/
theorem rawParallelGridWeightedMissTotal_eq
    {n h : Nat} {Control : Type} (hh : 0 < h) (hdvd : h ∣ n)
    (ring : DirectedRing n) (control : ControlRow h Control)
    (q : Fin n -> ParallelCell h Control) (t : Nat) :
    rawParallelGridWeightedMissTotal hh ring control q t =
      parallelGridWeightedMissTotal hh hdvd ring q t := by
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [rawParallelGridWeightedMissTotal]
      change _ = periodGridWeightedMissTotal hh hdvd ring (positions q) (t + 1)
      rw [periodGridWeightedMissTotal_succ_eq, ih,
        rawParallelGridMissTree_eq hh hdvd ring control q t]
      rfl

/-- Exact finite-horizon tail bound for the full protocol's position marginal. -/
theorem parallelGridMissTree_tail_moment
    {n h : Nat} {Control : Type} (hh : 0 < h) (hdvd : h ∣ n)
    (hn2 : 1 < n) (ring : DirectedRing n)
    (q : Fin n -> ParallelCell h Control) (t : Nat) :
    2 * (t + 1) * parallelGridMissTree hh hdvd ring q t <=
      n ^ t * n ^ 3 := by
  exact periodGridMissTree_tail_moment hh hdvd hn2 ring (positions q) t

/-- Division-free form of `E[min(T_grid,t)] <= n^3/2`, now for arbitrary
simultaneous control dynamics. -/
theorem parallelGrid_truncated_expectation_le_half_cube
    {n h : Nat} {Control : Type} (hh : 0 < h) (hdvd : h ∣ n)
    (hn2 : 1 < n) (ring : DirectedRing n)
    (q : Fin n -> ParallelCell h Control) (t : Nat) :
    2 * (n * parallelGridWeightedMissTotal hh hdvd ring q t) <=
      n ^ t * n ^ 3 := by
  exact periodGrid_truncated_expectation_le_half_cube
    hh hdvd hn2 ring (positions q) t

/-- The same expectation theorem stated for the tree that literally executes
the arbitrary control row. -/
theorem rawParallelGrid_truncated_expectation_le_half_cube
    {n h : Nat} {Control : Type} (hh : 0 < h) (hdvd : h ∣ n)
    (hn2 : 1 < n) (ring : DirectedRing n)
    (control : ControlRow h Control)
    (q : Fin n -> ParallelCell h Control) (t : Nat) :
    2 * (n * rawParallelGridWeightedMissTotal hh ring control q t) <=
      n ^ t * n ^ 3 := by
  rw [rawParallelGridWeightedMissTotal_eq hh hdvd ring control q t]
  exact parallelGrid_truncated_expectation_le_half_cube
    hh hdvd hn2 ring q t

#print axioms positions_parallelStep
#print axioms positionGrid_parallelStep
#print axioms positions_runParallel
#print axioms rawParallelGridMissTree_eq
#print axioms rawParallelGridWeightedMissTotal_eq
#print axioms parallelGridMissTree_tail_moment
#print axioms parallelGrid_truncated_expectation_le_half_cube
#print axioms rawParallelGrid_truncated_expectation_le_half_cube

end PPLLParallelGeometryLift
