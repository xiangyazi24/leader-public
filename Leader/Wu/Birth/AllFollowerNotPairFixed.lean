import Leader.Wu.Protocol.Repairs

/-! GAP30: the neutral all-follower configuration is not pair-fixed on the
full saturated no-collision row. At ψ = 1, κ = 2, n = 2, WAIT preparation
changes h_field and reset; the full row retains the h_field change.
This does not establish eventual safety or rule out a larger closed class. -/
namespace GAP30
open PPLL PPLLRepair
set_option autoImplicit false

/-- All fields neutral, including every signal and every leader bit. -/
def neutral : AgentState 1 where
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


abbrev hψ : 0 < 1 := by decide

/-- The two-agent all-follower, zero-signal configuration. -/
def followers : Fin 2 → AgentState 1 := fun _ => neutral

theorem ring : DirectedRing 2 := ⟨by decide⟩

/-- The label correction stage is unchanged: ψ = 1 has only label zero. -/
theorem pPsi_fixed : pPsi hψ neutral neutral = (neutral, neutral) := by rfl

/-- WAIT preparation is the first stage that changes this input. -/
theorem wait_changes :
    (waitSaturatedPrepare hψ neutral neutral).1.h_field = true ∧
    (waitSaturatedPrepare hψ neutral neutral).2.reset = true := by
  exact ⟨rfl, rfl⟩

/-- Exact state after the prefix through signal movement. -/
def beforeCheckLeft : AgentState 1 :=
  { neutral with state := .produce, h_field := true }

def beforeCheckRight : AgentState 1 :=
  { neutral with reset := true }

theorem beforeCheck_exact :
    ppllSaturatedBeforeCheck hψ 2 neutral neutral =
      (beforeCheckLeft, beforeCheckRight) := by
  rfl

/-- Exact state after CHECK, disappearance, comparison, and suppression. -/
def stableLeft : AgentState 1 :=
  { neutral with h_field := true }

def stableRight : AgentState 1 :=
  { neutral with reset := true }

theorem beforeEliminate_exact :
    ppllSaturatedBeforeEliminate hψ 2 neutral neutral =
      (stableLeft, stableRight) := by
  unfold ppllSaturatedBeforeEliminate
  rw [beforeCheck_exact]
  rfl

theorem beforeWrite_exact :
    ppllSaturatedBeforeWrite hψ 2 neutral neutral =
      (stableLeft, stableRight) := by
  unfold ppllSaturatedBeforeWrite
  rw [beforeEliminate_exact]
  rfl

/-- WRITE_SEQ additionally places the responder in its departure write state. -/
def finalRight : AgentState 1 :=
  { stableRight with write_state := .depart }

theorem full_exact :
    ppllSaturatedNoCollision hψ 2 neutral neutral =
      (stableLeft, finalRight) := by
  unfold ppllSaturatedNoCollision
  rw [beforeWrite_exact]
  rfl

/-- The h_field change survives every subsequent stage of the complete row. -/
theorem full_hfield (e : Fin 2) :
    (ppllSaturatedNoCollision hψ 2
      (followers e) (followers (ring.rightNeighbor e))).1.h_field = true := by
  have h := congrArg
    (fun q : AgentState 1 × AgentState 1 => q.1.h_field) full_exact
  simpa only [followers, stableLeft, neutral] using h

/-- Every edge fails the proposed pair fixed-point test, witnessed by h_field. -/
theorem followers_not_pair_fixed (e : Fin 2) :
    ppllSaturatedNoCollision hψ 2
      (followers e) (followers (ring.rightNeighbor e)) ≠
    (followers e, followers (ring.rightNeighbor e)) := by
  intro h
  have bad := congrArg (fun q : AgentState 1 × AgentState 1 => q.1.h_field) h
  have good := full_hfield e
  have input_false : (followers e).h_field = false := by rfl
  rw [good, input_false] at bad
  cases bad

#print axioms pPsi_fixed
#print axioms wait_changes
#print axioms beforeCheck_exact
#print axioms beforeEliminate_exact
#print axioms beforeWrite_exact
#print axioms full_exact
#print axioms full_hfield
#print axioms followers_not_pair_fixed
end GAP30
