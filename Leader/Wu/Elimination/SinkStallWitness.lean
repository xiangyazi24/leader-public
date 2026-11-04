import Leader.Wu.Elimination.SinkGapCleanup
open LDSinkGapCleanup


namespace LDSinkStallWitness


set_option autoImplicit false


/-!
A six-agent, three-leader fixed-point witness for the isolated sink kernel.


Even positions are shielded leaders with no bullet. Odd positions are
followers carrying live bullets. Every absence signal is zero.


The concrete pair equations below are proved by kernel reduction (`rfl`).
Only enumeration of Fin 6 and concrete field facts use ordinary `decide`.
No finiteness assumption on AgentState is needed; its Nat/Int fields are
fixed explicitly. No proof of eventual cleanup is assumed.
-/


/-- Neutral values for every field of the repository's full state record. -/
private def neutral : AgentState 1 where
  leader := false
  probe := false
  phase := false
  bit := false
  wait := false
  state := .none
  path := .bot
  reset := false
  carry := false
  count := 0
  label := ⟨0, by decide⟩
  h_field := false
  path2 := none
  path3 := none
  path4 := none
  path5 := none
  p := false
  p_carry := false
  reset_cmd := false
  echo := false
  signal_B := ⟨0, by decide⟩
  bullet := ⟨0, by decide⟩
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


private def shieldedLeader : AgentState 1 :=
  { neutral with leader := true, shield := true }


private def liveFollower : AgentState 1 :=
  { neutral with bullet := ⟨2, by decide⟩ }


/-- The six cases are explicit; the final branch is unreachable on Fin 6. -/
def stall (i : Fin 6) : AgentState 1 :=
  match i.val with
  | 0 => shieldedLeader
  | 1 => liveFollower
  | 2 => shieldedLeader
  | 3 => liveFollower
  | 4 => shieldedLeader
  | 5 => liveFollower
  | _ => neutral


/-- Clockwise successor, including the wraparound edge (5,0). -/
def rightNeighbor (e : Fin 6) : Fin 6 :=
  ⟨(e.val + 1) % 6, Nat.mod_lt _ (by decide)⟩


theorem rightNeighbor_eq_add_one (e : Fin 6) :
    rightNeighbor e = e + 1 := by
  rfl


/-- Finite equality enumeration, without the fin_cases tactic. -/
private theorem six_cases : ∀ e : Fin 6,
    e = 0 ∨ e = 1 ∨ e = 2 ∨ e = 3 ∨ e = 4 ∨ e = 5 := by
  decide


/-- The specified leader, bullet, shield, label, and signal pattern. -/
theorem stall_fields (i : Fin 6) :
    (stall i).label = 0 ∧
    (stall i).signal_B = 0 ∧
    ((stall i).leader = true ↔ i = 0 ∨ i = 2 ∨ i = 4) ∧
    ((stall i).bullet = 2 ↔ i = 1 ∨ i = 3 ∨ i = 5) ∧
    (stall i).shield = (stall i).leader := by
  rcases six_cases i with rfl | rfl | rfl | rfl | rfl | rfl <;>
    decide


/-- Every literal edge preserves both entire endpoint records.


On (0,1), (2,3), (4,5), the shield prevents the live hit and SIGNAL
keeps the live-bullet responder at zero signal.
On (1,2), (3,4), (5,0), the responder has no bullet, while the follower
initiator has zero signal. Neither endpoint's FIRE guard is enabled.
-/
theorem stall_pair_fixed (e : Fin 6) :
    sinkKernel (by decide : 1 > 0)
        (stall e) (stall (rightNeighbor e)) =
      (stall e, stall (rightNeighbor e)) := by
  rcases six_cases e with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rfl


/-- Updating the ring with any of its six kernel outputs changes no cell. -/
theorem stall_fixed : ∀ e : Fin 6,
    updatePair stall e (rightNeighbor e)
        (sinkKernel (by decide : 1 > 0)
          (stall e) (stall (rightNeighbor e))) = stall := by
  intro e
  rw [stall_pair_fixed e]
  funext k
  by_cases hki : k = e
  · subst k
    simp [updatePair]
  · by_cases hkj : k = rightNeighbor e
    · subst k
      simp [updatePair, hki]
    · simp [updatePair, hki, hkj]


/-- In particular, neither endpoint loses or gains its leader bit. -/
theorem stall_no_deletion : ∀ e : Fin 6,
    (sinkKernel (by decide : 1 > 0)
        (stall e) (stall (rightNeighbor e))).1.leader =
      (stall e).leader ∧
    (sinkKernel (by decide : 1 > 0)
        (stall e) (stall (rightNeighbor e))).2.leader =
      (stall (rightNeighbor e)).leader := by
  intro e
  constructor
  · exact congrArg
      (fun q : AgentState 1 × AgentState 1 => q.1.leader)
      (stall_pair_fixed e)
  · exact congrArg
      (fun q : AgentState 1 × AgentState 1 => q.2.leader)
      (stall_pair_fixed e)


/-- Execute an arbitrary finite word of raw ring edges. -/
def run : List (Fin 6) → (Fin 6 → AgentState 1) →
    (Fin 6 → AgentState 1)
  | [], C => C
  | e :: es, C =>
      run es (updatePair C e (rightNeighbor e)
        (sinkKernel (by decide : 1 > 0)
          (C e) (C (rightNeighbor e))))


/-- Permanent stall: every finite scheduler word preserves the witness. -/
theorem stall_run_fixed (es : List (Fin 6)) :
    run es stall = stall := by
  induction es with
  | nil => rfl
  | cons e es ih =>
      change run es (updatePair stall e (rightNeighbor e)
        (sinkKernel (by decide : 1 > 0)
          (stall e) (stall (rightNeighbor e)))) = stall
      rw [stall_fixed e]
      exact ih


/-- The fixed configuration is not a unique-leader configuration. -/
theorem stall_not_unique_leader :
    ¬ ∃ leader : Fin 6, ∀ i : Fin 6,
      (stall i).leader = true ↔ i = leader := by
  intro h
  obtain ⟨leader, hleader⟩ := h
  have h0 : (0 : Fin 6) = leader := (hleader 0).mp (by rfl)
  have h2 : (2 : Fin 6) = leader := (hleader 2).mp (by rfl)
  exact (by decide : (0 : Fin 6) ≠ 2) (h0.trans h2.symm)


end LDSinkStallWitness


#print axioms LDSinkStallWitness.rightNeighbor_eq_add_one
#print axioms LDSinkStallWitness.stall_fields
#print axioms LDSinkStallWitness.stall_pair_fixed
#print axioms LDSinkStallWitness.stall_fixed
#print axioms LDSinkStallWitness.stall_no_deletion
#print axioms LDSinkStallWitness.stall_run_fixed
#print axioms LDSinkStallWitness.stall_not_unique_leader
