import Leader.Wu.ShortGap.ChoiceStopping

/-!
# Short-gap candidate choice with charged concurrent rearm

This file instantiates the abstract restart interface with the smallest
macro-level rearm machine.  After a candidate-free uniform round, every
logical root owns one pending rearm obligation.  Scheduling that root's
placed physical edge clears its obligation.  Cleared obligations never
return, and completion re-enters the all-Race candidate round.

This is deliberately a macro quotient, not yet a literal radius-one carrier.
It proves that concurrency and repeated uniform outcomes cost only `n*m` in
the rearm layer.  A later physical refinement must replace each atomic clear
by current declaration/denial transport while preserving a polynomial reset
potential.
-/

namespace ShortGapChoiceRestart

open FiniteUniformStoppingTree
open PeriodHIncidenceChoice
open ShortGapChoiceStopping

set_option autoImplicit false

private theorem ofFn_sum_lt_of_single_lt
    {n : Nat} (f g : Fin n → Nat) (chosen : Fin n)
    (hle : ∀ i, f i ≤ g i) (hlt : f chosen < g chosen) :
    (List.ofFn f).sum < (List.ofFn g).sum := by
  induction n with
  | zero => exact Fin.elim0 chosen
  | succ n ih =>
      rw [List.ofFn_succ, List.sum_cons, List.ofFn_succ, List.sum_cons]
      by_cases hzero : chosen = 0
      · subst chosen
        have htail := ofFn_sum_le
          (fun i : Fin n => f i.succ) (fun i => g i.succ)
          (fun i => hle i.succ)
        omega
      · have hpos : 0 < chosen.val := by
          have hne : chosen.val ≠ 0 :=
            fun h => hzero (Fin.ext (by simpa using h))
          omega
        let previous : Fin n := ⟨chosen.val - 1, by omega⟩
        have hsucc : previous.succ = chosen :=
          Fin.ext (by simp [previous]; omega)
        have htail := ih
          (fun i : Fin n => f i.succ) (fun i => g i.succ) previous
          (fun i => hle i.succ) (by simpa only [hsucc] using hlt)
        have hhead := hle 0
        omega

/-- Pending rearm flags after a candidate-free uniform round. -/
structure AtomicRearmState (m : Nat) where
  pending : Fin m → Bool
  hasPending : ∃ root, pending root = true

/-- Number of roots whose two-denial rearm has not yet completed. -/
def pendingCount {m : Nat} (pending : Fin m → Bool) : Nat :=
  (List.ofFn (fun root => if pending root then 1 else 0)).sum

/-- One placed root port clears that root's macro rearm obligation. -/
def clearPending {n m : Nat} (P : Placement n m)
    (pending : Fin m → Bool) (edge : Fin n) : Fin m → Bool :=
  fun root => if P.root root = edge then false else pending root

private theorem clearPending_weight_le
    {n m : Nat} (P : Placement n m) (pending : Fin m → Bool)
    (edge : Fin n) (root : Fin m) :
    (if clearPending P pending edge root then 1 else 0) ≤
      (if pending root then 1 else 0) := by
  simp only [clearPending]
  split <;> simp

/-- Clearing one scheduler edge cannot create pending debt. -/
theorem pendingCount_clearPending_le
    {n m : Nat} (P : Placement n m) (pending : Fin m → Bool)
    (edge : Fin n) :
    pendingCount (clearPending P pending edge) ≤ pendingCount pending := by
  exact ofFn_sum_le _ _ (clearPending_weight_le P pending edge)

/-- The placed edge of any pending root strictly lowers the debt. -/
theorem pendingCount_clearPending_root_lt
    {n m : Nat} (P : Placement n m) (pending : Fin m → Bool)
    (root : Fin m) (hpending : pending root = true) :
    pendingCount (clearPending P pending (P.root root)) <
      pendingCount pending := by
  apply ofFn_sum_lt_of_single_lt _ _ root
  · exact clearPending_weight_le P pending (P.root root)
  · simp [clearPending, hpending]

/-- The macro rearm process stops only after every pending root has cleared. -/
noncomputable def atomicRearmStep
    {n m : Nat} (P : Placement n m) :
    AtomicRearmState m → Fin n → StopNode (AtomicRearmState m) :=
  fun state edge =>
    let next := clearPending P state.pending edge
    if hnext : ∃ root, next root = true then
      .active ⟨next, hnext⟩
    else .success

def atomicRearmPotential {n m : Nat} :
    StopNode (AtomicRearmState m) → Nat
  | .active state => n * pendingCount state.pending
  | .success => 0
  | .failure => 0

private theorem atomicRearmPotential_step_le
    {n m : Nat} (P : Placement n m)
    (state : AtomicRearmState m) (edge : Fin n) :
    atomicRearmPotential (n := n) (atomicRearmStep P state edge) ≤
      n * pendingCount (clearPending P state.pending edge) := by
  classical
  simp only [atomicRearmStep]
  split <;> simp [atomicRearmPotential]

/-- The exact child-sum inequality for pending macro obligations. -/
theorem pendingCount_clearPending_childSum
    {n m : Nat} (P : Placement n m) (state : AtomicRearmState m) :
    1 + (List.ofFn (fun edge : Fin n =>
      pendingCount (clearPending P state.pending edge))).sum ≤
        n * pendingCount state.pending := by
  obtain ⟨root, hpending⟩ := state.hasPending
  have hsumlt := ofFn_sum_lt_of_single_lt
    (fun edge : Fin n => pendingCount (clearPending P state.pending edge))
    (fun _ : Fin n => pendingCount state.pending) (P.root root)
    (fun edge => pendingCount_clearPending_le P state.pending edge)
    (pendingCount_clearPending_root_lt P state.pending root hpending)
  rw [ofFn_sum_const] at hsumlt
  omega

/-- The atomic concurrent rearm service has expected work at most `n` times
the number of initially pending roots. -/
theorem atomicRearm_natBellmanSuperSolution
    {n m : Nat} (P : Placement n m) :
    NatBellmanSuperSolution (atomicRearmStep P) 1
      (atomicRearmPotential (n := n)) := by
  refine ⟨rfl, rfl, ?_⟩
  intro state
  have hdebt := pendingCount_clearPending_childSum P state
  have hscaled := Nat.mul_le_mul_left n hdebt
  have hchildren :
      (List.ofFn (fun edge : Fin n =>
        atomicRearmPotential (n := n) (atomicRearmStep P state edge))).sum ≤
        n * (List.ofFn (fun edge : Fin n =>
          pendingCount (clearPending P state.pending edge))).sum := by
    calc
      (List.ofFn (fun edge : Fin n =>
          atomicRearmPotential (n := n)
            (atomicRearmStep P state edge))).sum ≤
        (List.ofFn (fun edge : Fin n =>
          n * pendingCount (clearPending P state.pending edge))).sum := by
            apply ofFn_sum_le
            intro edge
            exact atomicRearmPotential_step_le P state edge
      _ = n * (List.ofFn (fun edge : Fin n =>
          pendingCount (clearPending P state.pending edge))).sum :=
        ofFn_sum_mul_left n _
  calc
    1 * n + (List.ofFn (fun edge : Fin n =>
        atomicRearmPotential (n := n) (atomicRearmStep P state edge))).sum ≤
      n + n * (List.ofFn (fun edge : Fin n =>
        pendingCount (clearPending P state.pending edge))).sum := by
          simpa using Nat.add_le_add_left hchildren n
    _ = n * (1 + (List.ofFn (fun edge : Fin n =>
        pendingCount (clearPending P state.pending edge))).sum) := by
      rw [Nat.mul_add, Nat.mul_one]
    _ ≤ n * (n * pendingCount state.pending) := hscaled
    _ = n * atomicRearmPotential (n := n) (.active state) := rfl

theorem atomicRearmStep_ne_failure
    {n m : Nat} (P : Placement n m) :
    ∀ state edge, atomicRearmStep P state edge ≠ .failure := by
  classical
  intro state edge
  simp only [atomicRearmStep]
  split <;> simp

/-- Every root is initially waiting for its uniform-round denial discharge. -/
def allPendingAtomicRearmState {m : Nat} (hm : 0 < m) :
    AtomicRearmState m :=
  ⟨fun _ => true, ⟨⟨0, hm⟩, rfl⟩⟩

@[simp] theorem pendingCount_allPending {m : Nat} :
    pendingCount (fun _ : Fin m => true) = m := by
  simp [pendingCount, ofFn_sum_const]

@[simp] theorem atomicRearmPotential_allPending
    {n m : Nat} (hm : 0 < m) :
    atomicRearmPotential (n := n) (.active (allPendingAtomicRearmState hm)) =
      n * m := by
  simp [atomicRearmPotential, allPendingAtomicRearmState]

/-- Concrete macro-level implementation of the candidate rearm interface. -/
noncomputable def atomicCandidateRearmSpec
    {n m : Nat} (P : Placement n m) (hm : 0 < m) :
    CandidateRearmSpec n where
  State := AtomicRearmState m
  step := atomicRearmStep P
  start := allPendingAtomicRearmState hm
  potential := atomicRearmPotential (n := n)
  bellman := atomicRearm_natBellmanSuperSolution P
  noFailure := atomicRearmStep_ne_failure P

/-- Complete macro candidate process: bare incidence choice, charged uniform
rearm, and repetition until the first persistent candidate. -/
noncomputable def atomicCandidateRestartStep
    {n m : Nat} (ring : DirectedRing m) (P : Placement n m)
    (hm : 0 < m) :=
  (atomicCandidateRearmSpec P hm).restartStep ring P hm

/-- Repeated macro candidate rounds have expected work at most `3*n*m`: two
copies pay for the balanced candidate round and one pays all rearm flags. -/
theorem atomicCandidateRestart_truncatedCost_le
    {n m : Nat} (ring : DirectedRing m) (hm : 1 < m)
    (P : Placement n m) (hn : 1 < n) (T : Nat) :
    truncatedActiveCostNumerator
        (atomicCandidateRestartStep ring P (by omega))
        (.active (.round (allRaceCandidateDrainState ring (by omega)))) T ≤
      n ^ T * (3 * (n * m)) := by
  have hcost :=
    (atomicCandidateRearmSpec P (by omega)).allRace_truncatedCost_le
      ring hm P hn T
  simp only [atomicCandidateRestartStep, atomicCandidateRearmSpec,
    atomicRearmPotential_allPending] at hcost ⊢
  have hbudget : 3 * (n * m) = 2 * (n * m) + n * m := by omega
  rw [hbudget]
  exact hcost

/-- Exact reciprocal success tail for the complete macro process. -/
theorem atomicCandidateRestart_success_one_minus_inv_factor
    {n m factor : Nat} (ring : DirectedRing m) (hm : 1 < m)
    (P : Placement n m) (hn : 1 < n) :
    (factor - 1) * n ^ (factor * (3 * (n * m))) ≤
      factor * successCount
        (atomicCandidateRestartStep ring P (by omega))
        (.active (.round (allRaceCandidateDrainState ring (by omega))))
        (factor * (3 * (n * m))) := by
  have hsuccess :=
    CandidateRearmSpec.allRace_success_one_minus_inv_factor
      (atomicCandidateRearmSpec P (by omega)) ring hm P hn
      (factor := factor)
  simp only [atomicCandidateRestartStep, atomicCandidateRearmSpec,
    atomicRearmPotential_allPending] at hsuccess ⊢
  have hbudget : 3 * (n * m) = 2 * (n * m) + n * m := by omega
  rw [hbudget]
  exact hsuccess

#print axioms pendingCount_clearPending_root_lt
#print axioms atomicRearm_natBellmanSuperSolution
#print axioms atomicCandidateRestart_truncatedCost_le
#print axioms atomicCandidateRestart_success_one_minus_inv_factor

end ShortGapChoiceRestart
