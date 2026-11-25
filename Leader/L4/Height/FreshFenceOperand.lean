import Leader.L4.BStarCopyFenceSaturation

namespace L4.Height.FreshFenceOperand
open AllSizeProtocol BStarCopyFIFO BStarCopyCapacity BStarCopyMarkedLedger BStarCopyFenceSaturation
open BStarLongClaims BStarLongPackets BStarLongCommandData BStarLongPrep
open BStarLongFencePrefix

/-- Once all releases have entered the retaining region, the next inspected
cell has received a label. All earlier FENCE inspections left their mobiles
empty. The present cell may still be occupied. -/
theorem inspections_receive {L : Type} {plan : List L} {s : Ledger L}
    (P : Prefix plan s) (issued : s.release.pending=[])
    (boundary : OrderedBoundary s []) (j : Nat) (inside : j<plan.length)
    (earlier : ∀ k,k<j → (s.cells k).mobile=none) :
    (s.cells j).arrivals.length=plan.length-j ∧ ∃ a,(s.cells j).retained=some a := by
  have V := prefix_valid P
  have all : (s.cells 0).arrivals=plan := by
    have follows := V.follows
    change plan=s.release.released++s.release.pending at follows
    change (s.cells 0).arrivals++[]=s.release.released at boundary
    rw [issued,List.append_nil] at follows
    exact (List.append_nil _).symm.trans (boundary.trans follows.symm)
  have lower (i : Nat) (le : i≤j) : plan.length-i≤(s.cells i).arrivals.length := by
    induction i with
    | zero => simp [all]
    | succ i ih =>
      have old := ih (by omega)
      have held : (s.cells i).retained.toList.length≤1 := by
        cases h : (s.cells i).retained <;> simp
      have H := congrArg List.length (clean_custody (V.clean i))
      rw [earlier i (by omega)] at H
      simp only [List.length_append,Option.toList_none,List.length_nil,Nat.add_zero] at H
      rw [exact_handoff P i]
      omega
  have size := Nat.le_antisymm (prefix_cap P j inside) (lower j (Nat.le_refl _))
  refine ⟨size,?_⟩
  cases h : (s.cells j).retained with
  | some a => exact ⟨a,rfl⟩
  | none =>
    have no := (clean_retained (V.clean j)).mp h
    rw [no,List.length_nil] at size
    omega

/-- The first visit cannot fault on a missing retained operand. Its literal
old lane can advance immediately or can wait for its own mobile to depart. -/
theorem inspection_result {L : Type} {plan : List L} {s : Ledger L}
    (digits : L → BitVec 36) (P : Prefix plan s) (issued : s.release.pending=[])
    (boundary : OrderedBoundary s []) (j : Nat) (inside : j<plan.length)
    (earlier : ∀ k,k<j → (s.cells k).mobile=none) (lane : Lane)
    (image : Compatible digits (s.cells j) lane) (gate : lane.gate=true) (clean : lane.error=false) :
    (lane.mobile=.empty → fence lane true=.advance) ∧
    (lane.mobile≠.empty → fence lane true=.hold) := by
  obtain ⟨_,a,held⟩ := inspections_receive P issued boundary j inside earlier
  have data : lane.retained=.data (digits a) := by rw [image.2,held]; rfl
  refine ⟨fun empty => fence_good lane true gate clean empty (.inr ?_),
    fence_occupied lane true gate clean⟩
  rw [data]
  rfl

/-- The final pass, derived from the preceding pass prefix, authenticates the
whole word on the physical lanes. Duplicate payload bytes are allowed. -/
theorem forward_operand {L : Type} {plan : List L} {s : Ledger L}
    (digits : L → BitVec 36) (P : Prefix plan s) (positive : 0<plan.length)
    (issued : s.release.pending=[]) (boundary : OrderedBoundary s [])
    (lane : Nat → Lane) (image : ∀ j,j<plan.length → Compatible digits (s.cells j) (lane j))
    (earlier : ∀ k,k<plan.length-1 → (s.cells k).mobile=none)
    (g : Pair LongGeometry) (old : At Sheet → Lane) (a : At Sheet)
    (loc : old a=lane (plan.length-1)) (retaining : retains g a=true)
    (gate : (old a).gate=true) (clean : (old a).error=false) :
    Passed g old a ∧ laneRead lane 0 plan.length=plan.reverse.map (Digit9.data ∘ digits) := by
  have small : plan.length-1<plan.length := by omega
  have empty := terminal_empty P positive
  have mobile : (old a).mobile=.empty := by rw [loc,(image _ small).1,empty]; rfl
  have pass : Passed g old a := by
    unfold Passed
    rw [retaining]
    exact (inspection_result digits P issued boundary _ small earlier (old a) (by rw [loc]; exact image _ small)
      gate clean).1 mobile
  exact ⟨pass,(physical_terminal digits P positive boundary lane image g old a loc retaining pass).2.1⟩

#print axioms inspections_receive
#print axioms inspection_result
#print axioms forward_operand
end L4.Height.FreshFenceOperand
