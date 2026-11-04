import Leader.Wu.Protocol.StateBoundCarrier
import Leader.Wu.ShortGap.StateCount

set_option autoImplicit false

namespace PPLLStateBoundFinalCell

open PPLLStateBoundCarrier
open ShortGapCaptureCommitRows
open ShortGapStateCount

/-!
# Conservative final-cell state bound

This file uses the conservative **orthogonal product** counted in the
census: a physical cell simultaneously carries one bounded legacy P_PLL state
and one complete short-gap controller state.  This deliberately overcounts any
future tagged-sum implementation in which the two modes are mutually exclusive.

`ShortGapStateCount` exposes `allCNode : List CNode`, with
`allCNode_complete` and `allCNode_length = 39960`.

One interface fact is intentionally not fabricated here.  The current
`StateBoundCarrier` exports `boundedAgentStateList` and its exact length, but its
version deliberately does not export a theorem saying that every
`BoundedAgentState` occurs in that list.  Therefore `cellList_complete` below
states the exact composition lemma conditional on that missing S1 completeness
fact.  The exact list length and polynomial capstone are unconditional.
-/

/-- Conservative final local state: legacy lifecycle state times the complete
short-gap controller state. -/
structure Cell (psi h : Nat) where
  legacy : BoundedAgentState psi h
  control : CNode

private def enumProd {α β : Type} (xs : List α) (ys : List β) :
    List (α × β) :=
  xs.flatMap (fun x => ys.map (fun y => (x, y)))

private theorem enumProd_mem_of_mem
    {α β : Type} {xs : List α} {ys : List β} {x : α} {y : β}
    (hx : x ∈ xs) (hy : y ∈ ys) :
    (x, y) ∈ enumProd xs ys := by
  unfold enumProd
  apply List.mem_flatMap.mpr
  refine ⟨x, hx, ?_⟩
  apply List.mem_map.mpr
  exact ⟨y, hy, rfl⟩

private theorem enumProd_length {α β : Type} :
    ∀ (xs : List α) (ys : List β),
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

/-- The counted orthogonal product of the checked legacy carrier list and the
checked 39,960-state short-gap controller list. -/
def cellList (psi h : Nat) : List (Cell psi h) :=
  (enumProd (boundedAgentStateList psi h) allCNode).map
    (fun p => { legacy := p.1, control := p.2 })

/-- Exact completeness composition.  The short-gap premise is discharged by
`allCNode_complete`; the remaining premise is precisely the completeness theorem
that is not exported for `boundedAgentStateList`. -/
theorem cellList_complete
    {psi h : Nat}
    (hlegacy : ∀ a : BoundedAgentState psi h,
      a ∈ boundedAgentStateList psi h) :
    ∀ x : Cell psi h, x ∈ cellList psi h := by
  intro x
  rcases x with ⟨a, c⟩
  unfold cellList
  apply List.mem_map.mpr
  refine ⟨(a, c), ?_, rfl⟩
  exact enumProd_mem_of_mem (hlegacy a) (allCNode_complete c)

/-- Exact length of the conservative orthogonal product. -/
theorem cell_length (psi h : Nat) :
    (cellList psi h).length =
      39960 *
        (6606028800 * (h + 1) * psi * (2 * psi + 1) *
          (12 * psi * (psi + 1) + 1) * (4 * psi + 1) *
          (2 * psi + 3) ^ 2) := by
  unfold cellList
  rw [List.length_map, enumProd_length,
    boundedAgentState_length, allCNode_length]
  ac_rfl

/-- Final polynomial state bound for the conservative product.

The explicit constant is

`C = 39960 * 61931520000000 = 2474783539200000000`.

Keeping the first product form in the theorem avoids asking the kernel to
normalize an otherwise irrelevant 19-digit closed multiplication. -/
theorem finalCell_state_bound :
    ∀ h psi : Nat, 1 ≤ psi → psi ≤ h + 1 →
      (cellList psi h).length ≤
        (39960 * 61931520000000) * (h + 1) ^ 8 := by
  intro h psi hpsiPos hpsiBound
  rw [cell_length]
  have hcarrier := carrier_le_poly h psi hpsiPos hpsiBound
  simpa only [Nat.mul_assoc] using
    (Nat.mul_le_mul_left 39960 hcarrier)

/-- Ring size is absent from both factors of `Cell`; this useful formulation
records that changing an external `n` cannot change the counted final-cell list. -/
theorem cell_length_independent_of_n
    (n psi h : Nat) :
    (fun _n : Nat => (cellList psi h).length) n =
      39960 *
        (6606028800 * (h + 1) * psi * (2 * psi + 1) *
          (12 * psi * (psi + 1) + 1) * (4 * psi + 1) *
          (2 * psi + 3) ^ 2) := by
  simpa using cell_length psi h

#print axioms cellList_complete
#print axioms cell_length
#print axioms finalCell_state_bound
#print axioms cell_length_independent_of_n

end PPLLStateBoundFinalCell
