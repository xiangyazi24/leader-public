import Leader.Wu.Protocol.StateBoundProductCell
import Leader.Wu.ShortGap.UnifiedNode

open ShortGapCaptureReservation
open ShortGapLiteralGapRows
open ShortGapSpliceCommit
open ShortGapCaptureCommitRows
open ShortGapUnifiedNode
open ShortGapStateCount
open PPLLStateBoundCarrier
open PPLLStateBoundFinalCell


/-!
# Unified final-cell state bound, with `OutControl` hardwired


This file uses the proved enumeration and coverage declarations from the
imported state-bound layer: `allCNode`, `allCNode_complete`,
`allCNode_length : allCNode.length = 39960`, `boundedAgentStateList`,
`boundedAgentStateList_complete`, `boundedAgentState_length`, and
`carrier_le_poly`.  In particular, the final coverage theorem requires no
external completeness hypotheses.


The unified-controller alphabets are explicit here.  Their exact list sizes are


* `OutControl`: 3;
* `CwPort`: 4;
* `SnapPhase`: 4 * 3 = 12;
* `Option SnapPhase`: 13;
* `SpliceCtl`: 6;
* `RetireWitness`: 2;
* `DeclFlush`: 3;
* `CommitCarrier`: 3;
* `UTraffic`: 4 + 3 + 12 + 1 = 20.


Thus the five splice fields multiply `CNode` by
`13 * 13 * 6 * 2 * 3 = 6084`, and `traffic` multiplies once more by 20.
The exact correction from `CNode` to `UNode` is therefore `121680`.
With `allCNode.length = 39960`, the unified controller has exactly
`39960 * 121680 = 4862332800` entries in this exhaustive enumeration.


Carrier audit: the E-Live elimination state is not a seventh independent
product factor.  `BoundedAgentState psi h` is the finite-by-construction form
of the 32-field `AgentState psi`; in particular it already contains `signal_B`,
`bullet`, `shield`, `label`, and replaces the unbounded `count : Nat` by
`count : Fin (h + 1)`.  Therefore `BoundedAgentState psi h × UNode` counts the
E-Live fields plus the unified short-gap controller.  The only remaining
carrier question is external to this counting lemma: if the assembled protocol
later wraps `UNode` in another structure with an additional stored physical
field, that later field must also be counted.  E-Live itself adds no such factor.
-/


set_option autoImplicit false


namespace StateBoundUnifiedCell


/-- Cartesian product of two explicit lists. -/
def enumProd {alpha beta : Type}
    (xs : List alpha) (ys : List beta) : List (alpha × beta) :=
  xs.flatMap (fun x => ys.map (fun y => (x, y)))


/-- Exact product length.  The nil case uses simplification because Lean's
`Nat.mul` recurses on its second argument, so `0 * n` is not definitionally
zero for a variable `n`. -/
theorem enumProd_length {alpha beta : Type} :
    ∀ (xs : List alpha) (ys : List beta),
      (enumProd xs ys).length = xs.length * ys.length := by
  intro xs
  induction xs with
  | nil =>
      intro ys
      simp [enumProd, Nat.succ_mul, Nat.add_comm]
  | cons x xs ih =>
      intro ys
      change (ys.map (fun y => (x, y)) ++ enumProd xs ys).length =
        (x :: xs).length * ys.length
      rw [List.length_append, List.length_map, ih ys]
      simp [List.length_cons, Nat.succ_mul, Nat.add_comm]


/-- Membership in both factors gives membership in the explicit product. -/
theorem mem_enumProd_of_mem {alpha beta : Type}
    {xs : List alpha} {ys : List beta} {x : alpha} {y : beta}
    (hx : x ∈ xs) (hy : y ∈ ys) :
    (x, y) ∈ enumProd xs ys := by
  unfold enumProd
  exact List.mem_flatMap_of_mem hx (List.mem_map_of_mem hy)


/-! ## Exact fixed alphabets -/


def allOutControl : List OutControl :=
  [.home, .proposal, .finalReady]


theorem allOutControl_length : allOutControl.length = 3 := by
  rfl


theorem allOutControl_complete (x : OutControl) : x ∈ allOutControl := by
  cases x <;> simp [allOutControl]


def allCwPort : List CwPort :=
  [.toSend, .waiting, .heldDenial, .heldCandidate]


theorem allCwPort_length : allCwPort.length = 4 := by
  rfl


theorem allCwPort_complete (x : CwPort) : x ∈ allCwPort := by
  cases x <;> simp [allCwPort]


def allSpliceCtl : List SpliceCtl :=
  [.inactive, .bridged, .drained, .adopted, .retired, .armed]


theorem allSpliceCtl_length : allSpliceCtl.length = 6 := by
  rfl


theorem allSpliceCtl_complete (x : SpliceCtl) : x ∈ allSpliceCtl := by
  cases x <;> simp [allSpliceCtl]


def allRetireWitness : List RetireWitness :=
  [.none, .token]


theorem allRetireWitness_length : allRetireWitness.length = 2 := by
  rfl


theorem allRetireWitness_complete (x : RetireWitness) :
    x ∈ allRetireWitness := by
  cases x <;> simp [allRetireWitness]


def allDeclFlush : List DeclFlush :=
  [.none, .unflushed, .flushed]


theorem allDeclFlush_length : allDeclFlush.length = 3 := by
  rfl


theorem allDeclFlush_complete (x : DeclFlush) : x ∈ allDeclFlush := by
  cases x <;> simp [allDeclFlush]


def allCommitCarrier : List CommitCarrier :=
  [.none, .commit, .committedBack]


theorem allCommitCarrier_length : allCommitCarrier.length = 3 := by
  rfl


theorem allCommitCarrier_complete (x : CommitCarrier) :
    x ∈ allCommitCarrier := by
  cases x <;> simp [allCommitCarrier]


/-! ## Snapshot enumeration -/


def allSnapPhase : List SnapPhase :=
  (enumProd allCwPort allOutControl).map
    (fun p => ({ cw := p.1, out := p.2 } : SnapPhase))


theorem allSnapPhase_length : allSnapPhase.length = 12 := by
  unfold allSnapPhase
  rw [List.length_map, enumProd_length, allCwPort_length,
    allOutControl_length]


theorem allSnapPhase_complete (x : SnapPhase) : x ∈ allSnapPhase := by
  rcases x with ⟨cw, out⟩
  unfold allSnapPhase
  exact List.mem_map_of_mem
    (mem_enumProd_of_mem (allCwPort_complete cw)
      (allOutControl_complete out))


def allOptionSnapPhase : List (Option SnapPhase) :=
  none :: allSnapPhase.map some


theorem allOptionSnapPhase_length : allOptionSnapPhase.length = 13 := by
  unfold allOptionSnapPhase
  rw [List.length_cons, List.length_map, allSnapPhase_length]


theorem allOptionSnapPhase_complete (x : Option SnapPhase) :
    x ∈ allOptionSnapPhase := by
  cases x with
  | none => simp [allOptionSnapPhase]
  | some s =>
      unfold allOptionSnapPhase
      exact List.Mem.tail none
        (List.mem_map_of_mem (allSnapPhase_complete s))


/-! ## Unified traffic enumeration -/


def allUTraffic : List UTraffic :=
  allCwPort.map UTraffic.selection ++
    allCommitCarrier.map UTraffic.capture ++
    allSnapPhase.map UTraffic.splice ++
    [UTraffic.empty]


theorem allUTraffic_length : allUTraffic.length = 20 := by
  simp only [allUTraffic, List.length_append, List.length_map,
    allCwPort_length, allCommitCarrier_length, allSnapPhase_length,
    List.length_cons, List.length_nil]


theorem allUTraffic_complete (x : UTraffic) : x ∈ allUTraffic := by
  cases x with
  | selection c =>
      have hc := allCwPort_complete c
      simp [allUTraffic, hc]
  | capture k =>
      have hk := allCommitCarrier_complete k
      simp [allUTraffic, hk]
  | splice s =>
      have hs := allSnapPhase_complete s
      simp [allUTraffic, hs]
  | empty =>
      simp [allUTraffic]


/-! ## Splice and unified-node enumeration -/


def allSNode : List SNode :=
  (enumProd
    (enumProd
      (enumProd
        (enumProd
          (enumProd allCNode allOptionSnapPhase)
          allOptionSnapPhase)
        allSpliceCtl)
      allRetireWitness)
    allDeclFlush).map
    (fun p =>
      ({ core := p.1.1.1.1.1
         bridge := p.1.1.1.1.2
         payload := p.1.1.1.2
         splice := p.1.1.2
         witness := p.1.2
         flush := p.2 } : SNode))


/-- The five physical splice fields multiply `CNode` by exactly 6084. -/
theorem allSNode_length :
    allSNode.length = allCNode.length * 6084 := by
  unfold allSNode
  simp only [List.length_map, enumProd_length,
    allOptionSnapPhase_length, allSpliceCtl_length,
    allRetireWitness_length, allDeclFlush_length]
  simp only [Nat.mul_assoc]


/-- Completeness is conditional only on the already-given `CNode` list being
complete. -/
theorem allSNode_complete
    (hCNode : ∀ x : CNode, x ∈ allCNode)
    (x : SNode) : x ∈ allSNode := by
  rcases x with ⟨core, bridge, payload, splice, witness, flush⟩
  unfold allSNode
  exact List.mem_map_of_mem
    (mem_enumProd_of_mem
      (mem_enumProd_of_mem
        (mem_enumProd_of_mem
          (mem_enumProd_of_mem
            (mem_enumProd_of_mem
              (hCNode core)
              (allOptionSnapPhase_complete bridge))
            (allOptionSnapPhase_complete payload))
          (allSpliceCtl_complete splice))
        (allRetireWitness_complete witness))
      (allDeclFlush_complete flush))


def allUNode : List UNode :=
  (enumProd allSNode allUTraffic).map
    (fun p =>
      ({ core := p.1.core
         bridge := p.1.bridge
         payload := p.1.payload
         splice := p.1.splice
         witness := p.1.witness
         flush := p.1.flush
         traffic := p.2 } : UNode))


/-- Exact controller correction from `CNode` to `UNode`. -/
theorem allUNode_length :
    allUNode.length = allCNode.length * 121680 := by
  unfold allUNode
  rw [List.length_map, enumProd_length, allSNode_length,
    allUTraffic_length]
  rw [Nat.mul_assoc]


/-- With the checked `allCNode.length = 39960`, the unified controller list has
exactly 4,862,332,800 entries. -/
theorem allUNode_length_exact : allUNode.length = 4862332800 := by
  rw [allUNode_length, allCNode_length]


theorem allUNode_complete
    (hCNode : ∀ x : CNode, x ∈ allCNode)
    (x : UNode) : x ∈ allUNode := by
  rcases x with
    ⟨core, bridge, payload, splice, witness, flush, traffic⟩
  have hs :
      ({ core := core
         bridge := bridge
         payload := payload
         splice := splice
         witness := witness
         flush := flush } : SNode) ∈ allSNode :=
    allSNode_complete hCNode _
  have ht : traffic ∈ allUTraffic := allUTraffic_complete traffic
  unfold allUNode
  exact List.mem_map_of_mem (mem_enumProd_of_mem hs ht)


/-! ## Old cell and corrected unified cell -/


/-- Same two-factor enumeration shape as the old capture-only final cell. -/
def allCell (psi h : Nat) : List (Cell psi h) :=
  (enumProd (boundedAgentStateList psi h) allCNode).map
    (fun p => ({ legacy := p.1, control := p.2 } : Cell psi h))


theorem allCell_length (psi h : Nat) :
    (allCell psi h).length =
      (boundedAgentStateList psi h).length * allCNode.length := by
  unfold allCell
  rw [List.length_map, enumProd_length]


theorem allCell_length_39960 (psi h : Nat) :
    (allCell psi h).length =
      (boundedAgentStateList psi h).length * 39960 := by
  rw [allCell_length, allCNode_length]


structure UCell (psi h : Nat) where
  legacy : BoundedAgentState psi h
  control : UNode


def allUCell (psi h : Nat) : List (UCell psi h) :=
  (enumProd (boundedAgentStateList psi h) allUNode).map
    (fun p => ({ legacy := p.1, control := p.2 } : UCell psi h))


theorem allUCell_length (psi h : Nat) :
    (allUCell psi h).length =
      (boundedAgentStateList psi h).length * allUNode.length := by
  unfold allUCell
  rw [List.length_map, enumProd_length]


theorem allUCell_length_exact (psi h : Nat) :
    (allUCell psi h).length =
      (boundedAgentStateList psi h).length * 4862332800 := by
  rw [allUCell_length, allUNode_length_exact]


theorem allUCell_complete
    (psi h : Nat)
    (hLegacy : ∀ x : BoundedAgentState psi h,
      x ∈ boundedAgentStateList psi h)
    (hCNode : ∀ x : CNode, x ∈ allCNode)
    (x : UCell psi h) : x ∈ allUCell psi h := by
  rcases x with ⟨legacy, control⟩
  unfold allUCell
  exact List.mem_map_of_mem
    (mem_enumProd_of_mem (hLegacy legacy)
      (allUNode_complete hCNode control))


/-- The counted list covers every physical unified cell.  Both component
coverage proofs come from their actual constructor enumerations. -/
theorem enumeration_complete (psi h : Nat) (x : UCell psi h) :
    x ∈ allUCell psi h :=
  allUCell_complete psi h
    (boundedAgentStateList_complete psi h)
    ShortGapStateCount.allCNode_complete x


/-- The corrected local carrier is exactly the old capture-cell enumeration
multiplied by 121,680. -/
theorem ucell_over_cell (psi h : Nat) :
    (allUCell psi h).length =
      (allCell psi h).length * 121680 := by
  rw [allUCell_length_exact, allCell_length_39960]
  rw [Nat.mul_assoc]


/-! ## Corrected polynomial capstone -/


/-- The degree-eight legacy bound is unchanged; only the absolute controller
constant changes from 39,960 to 4,862,332,800. -/
theorem unifiedCell_state_bound
    (psi h : Nat) (hpsiPos : 1 ≤ psi) (hpsiBound : psi ≤ h + 1) :
    (allUCell psi h).length ≤
      4862332800 * 61931520000000 * (h + 1) ^ 8 := by
  have hLegacy :
      (boundedAgentStateList psi h).length ≤
        61931520000000 * (h + 1) ^ 8 := by
    rw [boundedAgentState_length]
    exact carrier_le_poly h psi hpsiPos hpsiBound
  rw [allUCell_length_exact]
  calc
    (boundedAgentStateList psi h).length * 4862332800 =
        4862332800 * (boundedAgentStateList psi h).length :=
      Nat.mul_comm _ _
    _ ≤ 4862332800 * (61931520000000 * (h + 1) ^ 8) :=
      Nat.mul_le_mul_left _ hLegacy
    _ = 4862332800 * 61931520000000 * (h + 1) ^ 8 :=
      (Nat.mul_assoc _ _ _).symm


end StateBoundUnifiedCell


#print axioms StateBoundUnifiedCell.enumProd_length
#print axioms StateBoundUnifiedCell.mem_enumProd_of_mem
#print axioms StateBoundUnifiedCell.allOutControl_length
#print axioms StateBoundUnifiedCell.allOutControl_complete
#print axioms StateBoundUnifiedCell.allCwPort_length
#print axioms StateBoundUnifiedCell.allCwPort_complete
#print axioms StateBoundUnifiedCell.allSpliceCtl_length
#print axioms StateBoundUnifiedCell.allSpliceCtl_complete
#print axioms StateBoundUnifiedCell.allRetireWitness_length
#print axioms StateBoundUnifiedCell.allRetireWitness_complete
#print axioms StateBoundUnifiedCell.allDeclFlush_length
#print axioms StateBoundUnifiedCell.allDeclFlush_complete
#print axioms StateBoundUnifiedCell.allCommitCarrier_length
#print axioms StateBoundUnifiedCell.allCommitCarrier_complete
#print axioms StateBoundUnifiedCell.allSnapPhase_length
#print axioms StateBoundUnifiedCell.allSnapPhase_complete
#print axioms StateBoundUnifiedCell.allOptionSnapPhase_length
#print axioms StateBoundUnifiedCell.allOptionSnapPhase_complete
#print axioms StateBoundUnifiedCell.allUTraffic_length
#print axioms StateBoundUnifiedCell.allUTraffic_complete
#print axioms StateBoundUnifiedCell.allSNode_length
#print axioms StateBoundUnifiedCell.allSNode_complete
#print axioms StateBoundUnifiedCell.allUNode_length
#print axioms StateBoundUnifiedCell.allUNode_length_exact
#print axioms StateBoundUnifiedCell.allUNode_complete
#print axioms StateBoundUnifiedCell.allCell_length
#print axioms StateBoundUnifiedCell.allCell_length_39960
#print axioms StateBoundUnifiedCell.allUCell_length
#print axioms StateBoundUnifiedCell.allUCell_length_exact
#print axioms StateBoundUnifiedCell.allUCell_complete
#print axioms StateBoundUnifiedCell.enumeration_complete
#print axioms StateBoundUnifiedCell.ucell_over_cell
#print axioms StateBoundUnifiedCell.unifiedCell_state_bound
