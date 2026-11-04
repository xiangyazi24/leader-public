import Leader.Wu.Protocol.BoundedProtocol
import Init.Data.Fin.Lemmas
import Lean


set_option autoImplicit false
set_option Elab.async false


namespace ZZBoundedSafeWitness


open PopulationProtocol


def positiveOne : 0 < 1 := by decide


def ring1 : DirectedRing 1 := ⟨by decide⟩


def P1 : PopulationProtocol :=
  PPLLRepair.boundedProtocol positiveOne 0


/-- The original two-state local family; only h_field varies. -/
def cell1 (h : Bool) : BoundedAgentState 1 0 :=
  { leader := true
    probe := false
    phase := false
    bit := false
    wait := true
    state := .none
    path := .bot
    reset := false
    carry := false
    count := 0
    label := 0
    h_field := h
    path2 := none
    path3 := none
    path4 := none
    path5 := none
    p := false
    p_carry := false
    reset_cmd := false
    echo := false
    signal_B := 0
    bullet := 2
    shield := true
    write_state := .none
    write := .none
    last := false
    last_set := false
    last_unset := true
    b_carry := false
    gen_ws := true
    ws_echo := false
    signal_ws := true }


def cycle1 (h : Bool) : P1.Configuration 1 :=
  fun _ => cell1 h


def minimumWitness : P1.Configuration 1 := cycle1 false


/-- The same two closed local checks as in the original file. -/
theorem local_cycle (h : Bool) :
    (PPLLRepair.boundedTransition positiveOne 0
      (cell1 h) (cell1 h)).1 = cell1 (!h) := by
  cases h <;> decide +kernel


private theorem fin1_zero (i : Fin 1) : i = 0 := by
  apply Fin.ext
  have hi := i.isLt
  omega


/-- Prove the graph-step bridge before instantiating the wide transition.
The transition equality is at function level, not at computed-record level. -/
private theorem step_constant_fin1
    (P : PopulationProtocol) (ring : DirectedRing 1)
    (T : P.Q → P.Q → P.Q × P.Q)
    (hT : P.transition = T)
    (a b : P.Q) (hab : (T a a).1 = b) (e : Fin 1) :
    P.step ring (fun _ => a) e = (fun _ => b) := by
  funext i
  have hi : i = e := (fin1_zero i).trans (fin1_zero e).symm
  simpa only [PopulationProtocol.step, if_pos hi, hT] using hab


/-- Specialization only: no concrete step normalization here. -/
theorem step_cycle (h : Bool) (e : Fin 1) :
    P1.step ring1 (cycle1 h) e = cycle1 (!h) := by
  exact step_constant_fin1
    P1 ring1
    (PPLLRepair.boundedTransition positiveOne 0)
    rfl
    (cell1 h) (cell1 (!h))
    (local_cycle h) e


def CycleFamily (D : P1.Configuration 1) : Prop :=
  ∃ h : Bool, D = cycle1 h


theorem cycleFamily_closed : ClosedPred P1 ring1 CycleFamily := by
  intro C hC D hD
  rcases hC with ⟨h, rfl⟩
  rcases hD with ⟨e, rfl⟩
  exact ⟨!h, step_cycle h e⟩


theorem reachable_cycle {D : P1.Configuration 1}
    (hr : Reachable P1 ring1 minimumWitness D) : CycleFamily D := by
  exact ClosedPred.reachable cycleFamily_closed
    (show CycleFamily minimumWitness from ⟨false, rfl⟩) hr


/-- Both clauses of the repository's full semantic safety predicate. -/
theorem minimum_isSafe :
    P1.IsSafe ring1 minimumWitness isLeaderOutput := by
  constructor
  · refine ⟨(0 : Fin 1), ?_, ?_⟩
    · rfl
    · intro j _
      exact fin1_zero j
  · intro D hr i
    rcases reachable_cycle hr with ⟨h, rfl⟩
    rfl


theorem minimum_exists :
    ∃ C : P1.Configuration 1, P1.IsSafe ring1 C isLeaderOutput :=
  ⟨minimumWitness, minimum_isSafe⟩


-- Metadata audit only; this command does not construct any proof.
open Lean in
run_cmd do
  let allowed : Array Name :=
    #[``propext, ``Classical.choice, ``Quot.sound]
  let targets : Array Name :=
    #[``positiveOne, ``ring1, ``P1, ``cell1, ``cycle1,
      ``minimumWitness, ``local_cycle, ``fin1_zero,
      ``step_constant_fin1, ``step_cycle, ``CycleFamily,
      ``cycleFamily_closed, ``reachable_cycle,
      ``minimum_isSafe, ``minimum_exists]
  for declName in targets do
    let _ ← getConstInfo declName
    let used ← collectAxioms declName
    for ax in used do
      unless allowed.contains ax do
        throwError "Axiom audit rejected {declName}: {ax}"


end ZZBoundedSafeWitness


#print axioms ZZBoundedSafeWitness.positiveOne
#print axioms ZZBoundedSafeWitness.ring1
#print axioms ZZBoundedSafeWitness.P1
#print axioms ZZBoundedSafeWitness.cell1
#print axioms ZZBoundedSafeWitness.cycle1
#print axioms ZZBoundedSafeWitness.minimumWitness
#print axioms ZZBoundedSafeWitness.local_cycle
#print axioms ZZBoundedSafeWitness.step_cycle
#print axioms ZZBoundedSafeWitness.CycleFamily
#print axioms ZZBoundedSafeWitness.cycleFamily_closed
#print axioms ZZBoundedSafeWitness.reachable_cycle
#print axioms ZZBoundedSafeWitness.minimum_isSafe
#print axioms ZZBoundedSafeWitness.minimum_exists
