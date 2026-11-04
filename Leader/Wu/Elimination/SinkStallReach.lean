import Leader.Wu.Elimination.SinkStallWitness


open LDSinkGapCleanup
open LDSinkStallWitness


namespace LDSinkStallReach


set_option autoImplicit false


/-!
Reach the fixed point by the literal scheduler word [2, 1].


Only two fields differ initially from the imported witness:
* agent 1 has no bullet;
* agent 2 has the positive absence signal.


The kernel, ring successor, full state records, and finite-word runner
are reused from the imported modules. No transition rule is modified.
-/


/-- Everything is inherited from `stall`, except these two specified fields. -/
def pre (i : Fin 6) : AgentState 1 :=
  match i.val with
  | 1 => { (stall i) with bullet := (0 : Fin 3) }
  | 2 => { (stall i) with signal_B := (1 : Fin 2) }
  | _ => stall i


/-- One literal whole-ring sink-kernel step, without a stopping condition. -/
def stallStep (C : Fin 6 → AgentState 1) (e : Fin 6) :
    Fin 6 → AgentState 1 :=
  updatePair C e (rightNeighbor e)
    (sinkKernel (by decide : 1 > 0)
      (C e) (C (rightNeighbor e)))


/-- Finite case enumeration (the corresponding helper in the imported module is private). -/
private theorem six_cases : ∀ i : Fin 6,
    i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 := by
  decide


/-- The exact leader, shield, label, signal, and bullet pattern of `pre`. -/
theorem pre_fields : ∀ i : Fin 6,
    (pre i).leader =
      (if i = 0 ∨ i = 2 ∨ i = 4 then true else false) ∧
    (pre i).shield = (pre i).leader ∧
    (pre i).label = 0 ∧
    (pre i).signal_B = (if i = 2 then 1 else 0) ∧
    (pre i).bullet = (if i = 3 ∨ i = 5 then 2 else 0) := by
  decide


/-- Concrete-field entrance certificate for recovery (0,1,2) and attack
(2,3,4), using the explicitly permitted alternative to packaging GapFrames.


The first two clauses give endpoint leaders and interior followers.
All labels are zero; with psi = 1 this supplies label alignment.
The next two clauses give the signal-below-bullets conditions on the
positive recovery and attack intervals, respectively. These quantified
implications are proved by explicitly enumerating both Fin 6 indices;
ordinary `decide` is used only on the resulting closed implications.
The last two clauses give recovery CleanReady's field pattern and the
attack GapBlocked field pattern (live at 3, none at 4, victim 2 shielded
or signalled). This theorem does not assert a packaged GapInvariant.
-/
theorem pre_is_two_gap_state :
    ((pre 0).leader = true ∧ (pre 2).leader = true ∧
      (pre 4).leader = true) ∧
    ((pre 1).leader = false ∧ (pre 3).leader = false) ∧
    (∀ i : Fin 6, (pre i).label = 0) ∧
    (∀ x y : Fin 6,
      1 ≤ x.val → x.val ≤ y.val → y.val ≤ 2 →
      0 < (pre x).bullet.val → (pre y).signal_B = 0) ∧
    (∀ x y : Fin 6,
      3 ≤ x.val → x.val ≤ y.val → y.val ≤ 4 →
      0 < (pre x).bullet.val → (pre y).signal_B = 0) ∧
    ((pre 2).signal_B = 1 ∧ (pre 1).bullet = 0 ∧
      (pre 2).bullet = 0) ∧
    ((pre 3).bullet = 2 ∧ (pre 4).bullet = 0 ∧
      ((pre 2).shield = true ∨ (pre 2).signal_B = 1)) := by
  refine ⟨by decide, by decide, ?_, ?_, ?_, by decide, by decide⟩
  · intro i
    rcases six_cases i with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rfl
  · intro x y
    rcases six_cases x with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases six_cases y with rfl | rfl | rfl | rfl | rfl | rfl <;>
        decide
  · intro x y
    rcases six_cases x with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases six_cases y with rfl | rfl | rfl | rfl | rfl | rfl <;>
        decide


/-- Edge (2,3): agent 2 fires as initiator, retaining its shield and
clearing its signal. The shield blocks the incoming live bullet at 3. -/
theorem pre_edge2_pair :
    sinkKernel (by decide : 1 > 0) (pre 2) (pre 3) =
      ({ (stall 2) with bullet := (2 : Fin 3) }, stall 3) := by
  rfl


/-- Edge (1,2), after edge 2: FIRE is now inert. MOVE transfers the live
bullet from agent 2 to agent 1, giving the two exact stall records. -/
theorem pre_edge1_pair :
    sinkKernel (by decide : 1 > 0)
        (stallStep pre 2 1) (stallStep pre 2 2) =
      (stall 1, stall 2) := by
  rfl


/-- Two literal updatePair applications: edge 2 followed by edge 1. -/
theorem pre_step2_step1 :
    stallStep (stallStep pre 2) 1 = stall := by
  funext i
  rcases six_cases i with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rfl


/-- The same equality in the imported scheduler-word interface. -/
theorem pre_run_step2_step1 :
    LDSinkStallWitness.run [2, 1] pre = stall :=
  pre_step2_step1


/-- Both explicitly requested differences from the final fixed point. -/
theorem pre_distinguishing_fields :
    (pre 2).signal_B = 1 ∧ (stall 2).signal_B = 0 ∧
    (pre 1).bullet = 0 ∧ (stall 1).bullet = 2 := by
  decide


/-- This is genuine reachability from a different configuration. -/
theorem pre_not_stall : pre ≠ stall := by
  intro h
  have hs := congrArg
    (fun C : Fin 6 → AgentState 1 => (C 2).signal_B) h
  exact (by decide : (1 : Fin 2) ≠ 0) hs


/-- Every scheduler suffix after the two-edge prefix remains at stall. -/
theorem pre_run_after_prefix (es : List (Fin 6)) :
    LDSinkStallWitness.run (2 :: 1 :: es) pre = stall := by
  calc
    LDSinkStallWitness.run (2 :: 1 :: es) pre =
        LDSinkStallWitness.run es (stallStep (stallStep pre 2) 1) := rfl
    _ = LDSinkStallWitness.run es stall :=
      congrArg (LDSinkStallWitness.run es) pre_step2_step1
    _ = stall := stall_run_fixed es


/-- No continuation after that prefix has a unique leader. -/
theorem pre_run_after_prefix_not_unique (es : List (Fin 6)) :
    ¬ ∃ leader : Fin 6, ∀ i : Fin 6,
      (LDSinkStallWitness.run (2 :: 1 :: es) pre i).leader = true ↔
        i = leader := by
  intro h
  exact stall_not_unique_leader ((pre_run_after_prefix es) ▸ h)


end LDSinkStallReach


#print axioms LDSinkStallReach.pre_fields
#print axioms LDSinkStallReach.pre_is_two_gap_state
#print axioms LDSinkStallReach.pre_edge2_pair
#print axioms LDSinkStallReach.pre_edge1_pair
#print axioms LDSinkStallReach.pre_step2_step1
#print axioms LDSinkStallReach.pre_run_step2_step1
#print axioms LDSinkStallReach.pre_distinguishing_fields
#print axioms LDSinkStallReach.pre_not_stall
#print axioms LDSinkStallReach.pre_run_after_prefix
#print axioms LDSinkStallReach.pre_run_after_prefix_not_unique
