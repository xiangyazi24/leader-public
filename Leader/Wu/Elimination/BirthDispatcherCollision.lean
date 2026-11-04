import Leader.Wu.Comparison.ExpiringK2Projection
import Leader.Wu.Elimination.AdjacentLeaderCollision

/-! The fixed final physical stage and the local newborn initialization.
There is no writer, scheduler or transition-law parameter in these rows. -/

namespace K2BirthDispatcher

open PPLL PPLLResearchFormulation PPLLExpiringComparisonRepair
  LDSinkBoundedKernel LDSinkKernelC K2OutputSafety
  ExpiringK2Projection

set_option autoImplicit false
set_option pp.structureInstances false

variable {ψ κ τ n : Nat}

/-- A computed follower-to-leader event, with no stored event tag. -/
def newborn (old out : ExpiringAgentState ψ κ τ) : Bool :=
  !old.core.core.leader && out.core.core.leader

/-- Arm exactly a real new leader. The leader bit and every metadata field
come from the computed output, not from a restored or synthetic input. -/
def initializeNewborn (old out : ExpiringAgentState ψ κ τ) :
    ExpiringAgentState ψ κ τ :=
  if newborn old out then
    putSignals out { observeCell out with bullet := 2, shield := true, signal_B := 0 }
  else out

theorem initializeNewborn_leader (old out : ExpiringAgentState ψ κ τ) :
    (initializeNewborn old out).core.core.leader = out.core.core.leader := by
  unfold initializeNewborn
  split <;> rfl

theorem initializeNewborn_frame (old out : ExpiringAgentState ψ κ τ) :
    putSignals (initializeNewborn old out) (observeCell out) = out := by
  unfold initializeNewborn
  split
  · exact putSignals_restore out _
  · exact putSignals_self out

theorem initializeNewborn_of_false (old out : ExpiringAgentState ψ κ τ)
    (hb : newborn old out = false) : initializeNewborn old out = out := by
  simp only [initializeNewborn, hb, Bool.false_eq_true, if_false]

theorem initializeNewborn_exact (old out : ExpiringAgentState ψ κ τ)
    (hb : newborn old out = true) :
    out.core.core.leader = true ∧
    (initializeNewborn old out).core.core.leader = true ∧
    (initializeNewborn old out).core.core.bullet = 2 ∧
    (initializeNewborn old out).core.core.shield = true ∧
    (initializeNewborn old out).core.core.signal_B = 0 := by
  have hl : out.core.core.leader = true := by
    cases ho : old.core.core.leader <;> cases hn : out.core.core.leader <;>
      simp_all [newborn]
  simp only [initializeNewborn, hb, if_true]
  exact ⟨hl, hl, rfl, rfl, rfl⟩

/-- The exact adjacent-collision extension on the expiring carrier. A true
collision retains both bullets, deletes the left leader, shields the right
leader and clears both signals. Otherwise exactly one K2 row executes. -/
def collisionRow (hψ : 0 < ψ) (l r : ExpiringAgentState ψ κ τ) :
    ExpiringAgentState ψ κ τ × ExpiringAgentState ψ κ τ :=
  if l.core.core.leader = true ∧ r.core.core.leader = true then
    (putSignals l { observeCell l with leader := false, signal_B := 0 },
      putSignals r { observeCell r with shield := true, signal_B := 0 })
  else ExpiringK2Projection.row hψ l r

/-- A fixed four-field presentation of the existing adjacent row. Both
branches are later identified with the actual UCell implementation. -/
def shadowRow (l r : AgentState 1) : AgentState 1 × AgentState 1 :=
  let l := signalView l
  let r := signalView r
  if l.leader = true ∧ r.leader = true then
    ({ l with leader := false, signal_B := 0 },
      { r with shield := true, signal_B := 0 })
  else sinkKernelC (by decide) l r

theorem observe_collisionRow (hψ : 0 < ψ) (l r : ExpiringAgentState ψ κ τ) :
    (observeCell (collisionRow hψ l r).1, observeCell (collisionRow hψ l r).2) =
      shadowRow (observeCell l) (observeCell r) := by
  unfold collisionRow shadowRow
  dsimp only
  by_cases hb : l.core.core.leader = true ∧ r.core.core.leader = true
  · have hs : (signalView (observeCell l)).leader = true ∧
        (signalView (observeCell r)).leader = true := hb
    rw [if_pos hb, if_pos hs]
    rfl
  · have hs : ¬ ((signalView (observeCell l)).leader = true ∧
        (signalView (observeCell r)).leader = true) := hb
    rw [if_neg hb, if_neg hs]
    exact ExpiringK2Projection.observe_row hψ l r

/-- This observer is the frozen actual AdjacentLeaderElimination row on
arbitrary UCells; it does not introduce or select a controller value. -/
theorem adjacent_observe_row (hψ : 0 < ψ)
    (l r : StateBoundUnifiedCell.UCell ψ κ) :
    (LabelFreeElimination.observeCell (AdjacentLeaderElimination.collisionRow hψ l r).1,
      LabelFreeElimination.observeCell (AdjacentLeaderElimination.collisionRow hψ l r).2) =
      shadowRow (LabelFreeElimination.observeCell l) (LabelFreeElimination.observeCell r) := by
  unfold AdjacentLeaderElimination.collisionRow shadowRow
  dsimp only
  by_cases hb : l.legacy.leader = true ∧ r.legacy.leader = true
  · have hs : (signalView (LabelFreeElimination.observeCell l)).leader = true ∧
        (signalView (LabelFreeElimination.observeCell r)).leader = true := hb
    rw [if_pos hb, if_pos hs]
    rfl
  · have hs : ¬ ((signalView (LabelFreeElimination.observeCell l)).leader = true ∧
        (signalView (LabelFreeElimination.observeCell r)).leader = true) := hb
    rw [if_neg hb, if_neg hs]
    exact LabelFreeElimination.observe_row hψ l r

def shadowStep (ring : DirectedRing n) (C : Fin n → AgentState 1) (e : Fin n) :
    Fin n → AgentState 1 :=
  updatePair C e (ring.rightNeighbor e) (shadowRow (C e) (C (ring.rightNeighbor e)))

theorem adjacent_observe_step (hψ : 0 < ψ) (ring : DirectedRing n)
    (C : Fin n → StateBoundUnifiedCell.UCell ψ κ) (e : Fin n) :
    LabelFreeElimination.observe (AdjacentLeaderElimination.step hψ ring C e) =
      shadowStep ring (LabelFreeElimination.observe C) e := by
  have hq := adjacent_observe_row hψ (C e) (C (ring.rightNeighbor e))
  funext i
  simp only [LabelFreeElimination.observe, AdjacentLeaderElimination.step,
    PopulationProtocol.step, AdjacentLeaderElimination.protocol, shadowStep, updatePair]
  split
  · exact congrArg Prod.fst hq
  · split
    · exact congrArg Prod.snd hq
    · rfl

theorem adjacent_observe_run (hψ : 0 < ψ) (ring : DirectedRing n)
    (C : Fin n → StateBoundUnifiedCell.UCell ψ κ) (es : List (Fin n)) :
    LabelFreeElimination.observe (run (AdjacentLeaderElimination.step hψ ring) C es) =
      run (shadowStep ring) (LabelFreeElimination.observe C) es := by
  induction es generalizing C with
  | nil => rfl
  | cons e es ih => simp only [run, ih, adjacent_observe_step]

/-- The final collision/K2 stage changes no metadata or stall at all. -/
theorem collisionRow_frame (hψ : 0 < ψ) (l r : ExpiringAgentState ψ κ τ) :
    putSignals (collisionRow hψ l r).1 (observeCell l) = l ∧
      putSignals (collisionRow hψ l r).2 (observeCell r) = r := by
  unfold collisionRow
  split
  · exact ⟨putSignals_restore l _, putSignals_restore r _⟩
  · exact ExpiringK2Projection.row_frame hψ l r

theorem collisionRow_of_both (hψ : 0 < ψ) (l r : ExpiringAgentState ψ κ τ)
    (hl : l.core.core.leader = true) (hr : r.core.core.leader = true) :
    (collisionRow hψ l r).1.core.core.leader = false ∧
    (collisionRow hψ l r).2.core.core.leader = true ∧
    (collisionRow hψ l r).1.core.core.bullet = l.core.core.bullet ∧
    (collisionRow hψ l r).2.core.core.bullet = r.core.core.bullet ∧
    (collisionRow hψ l r).1.core.core.shield = l.core.core.shield ∧
    (collisionRow hψ l r).2.core.core.shield = true ∧
    (collisionRow hψ l r).1.core.core.signal_B = 0 ∧
    (collisionRow hψ l r).2.core.core.signal_B = 0 := by
  rw [collisionRow, if_pos ⟨hl, hr⟩]
  exact ⟨rfl, hr, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem collisionRow_of_not_both (hψ : 0 < ψ) (l r : ExpiringAgentState ψ κ τ)
    (h : ¬ (l.core.core.leader = true ∧ r.core.core.leader = true)) :
    collisionRow hψ l r = ExpiringK2Projection.row hψ l r := if_neg h

/-- The final stage is unconditional: arm the computed newborn endpoints,
then execute the one collision/K2 row. The first two arguments are only the
original endpoints used by the local event test, not restored output states. -/
def finalPhysical (hψ : 0 < ψ) (oldL oldR metaL metaR : ExpiringAgentState ψ κ τ) :
    ExpiringAgentState ψ κ τ × ExpiringAgentState ψ κ τ :=
  collisionRow hψ (initializeNewborn oldL metaL) (initializeNewborn oldR metaR)

theorem finalPhysical_frame (hψ : 0 < ψ)
    (oldL oldR metaL metaR : ExpiringAgentState ψ κ τ) :
    putSignals (finalPhysical hψ oldL oldR metaL metaR).1 (observeCell metaL) = metaL ∧
      putSignals (finalPhysical hψ oldL oldR metaL metaR).2 (observeCell metaR) = metaR := by
  have hf := collisionRow_frame hψ (initializeNewborn oldL metaL) (initializeNewborn oldR metaR)
  constructor
  · have h := congrArg (fun u => putSignals u (observeCell metaL)) hf.1
    simpa only [putSignals_twice, initializeNewborn_frame, finalPhysical] using h
  · have h := congrArg (fun u => putSignals u (observeCell metaR)) hf.2
    simpa only [putSignals_twice, initializeNewborn_frame, finalPhysical] using h

/-- Every comparison control, permit and timer in the computed metadata is
retained by the physical tail, also in the collision branch. -/
theorem finalPhysical_nonK2 (hψ : 0 < ψ)
    (oldL oldR metaL metaR : ExpiringAgentState ψ κ τ) :
    nonK2 (finalPhysical hψ oldL oldR metaL metaR).1 = nonK2 metaL ∧
      nonK2 (finalPhysical hψ oldL oldR metaL metaR).2 = nonK2 metaR := by
  have hf := finalPhysical_frame hψ oldL oldR metaL metaR
  constructor
  · simpa only [nonK2_putSignals] using congrArg nonK2 hf.1
  · simpa only [nonK2_putSignals] using congrArg nonK2 hf.2

theorem finalPhysical_of_no_birth (hψ : 0 < ψ)
    (oldL oldR metaL metaR : ExpiringAgentState ψ κ τ)
    (hl : newborn oldL metaL = false) (hr : newborn oldR metaR = false) :
    finalPhysical hψ oldL oldR metaL metaR = collisionRow hψ metaL metaR := by
  rw [finalPhysical, initializeNewborn_of_false oldL metaL hl,
    initializeNewborn_of_false oldR metaR hr]

end K2BirthDispatcher

#print axioms K2BirthDispatcher.initializeNewborn_exact
#print axioms K2BirthDispatcher.collisionRow_frame
#print axioms K2BirthDispatcher.observe_collisionRow
#print axioms K2BirthDispatcher.adjacent_observe_run
#print axioms K2BirthDispatcher.finalPhysical_nonK2
