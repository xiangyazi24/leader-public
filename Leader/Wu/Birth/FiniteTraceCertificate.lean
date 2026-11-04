import Leader.Wu.Safety.CorrectedFormulation

set_option autoImplicit false

namespace BirthFiniteTraceCertificate

open PPLL PPLLResearchFormulation

/-! Small checked execution certificates avoid repeatedly reducing a large
protocol from time zero for every queried prefix. A row stores an edge and
both proposed endpoint outputs. The checker evaluates the supplied actual
transition on every current pair; the theorem joins those exact equalities
into the original runLocalSchedule. These rows are proof artifacts and are
never read by the population protocol itself. -/

abbrev Row (n : Nat) (Q : Type) := Fin n × Q × Q

/-- Update exactly the two physical endpoints from a proposed row. The
initiator is written last, agreeing with localStep even on a one-site ring. -/
def writeRow {n : Nat} {Q : Type} (ring : DirectedRing n) (C : Vector Q n)
    (row : Row n Q) : Vector Q n :=
  let j := ring.rightNeighbor row.1
  (C.set j.val row.2.2 j.isLt).set row.1.val row.2.1 row.1.isLt

/-- Every proposed row is checked against the same supplied transition.
The remaining input states are obtained only from already proposed rows. -/
def checkRows {n : Nat} {Q : Type} [DecidableEq Q]
    (ring : DirectedRing n) (T : Q → Q → Q × Q) : List (Row n Q) → Vector Q n → Bool
  | [], _ => true
  | row :: rest, C =>
      decide (T (C.get row.1) (C.get (ring.rightNeighbor row.1)) = row.2) &&
        checkRows ring T rest (writeRow ring C row)

/-- Replay the first t proposed rows, retaining the last state after the
finite table ends. Correctness is supplied by checkRows, not by this replay. -/
def rowPrefix {n : Nat} {Q : Type} (ring : DirectedRing n) :
    Nat → List (Row n Q) → Vector Q n → Vector Q n
  | 0, _, C => C
  | _ + 1, [], C => C
  | t + 1, row :: rest, C => rowPrefix ring t rest (writeRow ring C row)

private theorem writeRow_correct {n : Nat} {Q : Type} (ring : DirectedRing n)
    (T : Q → Q → Q × Q) (C : Vector Q n) (row : Row n Q)
    (h : T (C.get row.1) (C.get (ring.rightNeighbor row.1)) = row.2) :
    (writeRow ring C row).get = localStep ring T C.get row.1 := by
  funext i
  change (writeRow ring C row)[i.val] = _
  simp only [writeRow, Vector.getElem_set]
  by_cases he : i = row.1
  · subst i
    simp [localStep, h]
  · have hv : row.1.val ≠ i.val := fun h => he (Fin.ext h.symm)
    by_cases hj : i = ring.rightNeighbor row.1
    · subst i
      simp [hv, localStep, he, h]
    · have hvj : (ring.rightNeighbor row.1).val ≠ i.val := fun h => hj (Fin.ext h.symm)
      simp [hv, hvj, localStep, he, hj, Vector.get]

/-- A successful checker proves every prefix is an execution of the actual
transition. No checkpoint equality or future invariant is a hypothesis. -/
theorem rowPrefix_correct {n : Nat} {Q : Type} [DecidableEq Q]
    (ring : DirectedRing n) (T : Q → Q → Q × Q) (rows : List (Row n Q))
    (C : Vector Q n) (h : checkRows ring T rows C = true) (t : Nat) :
    (rowPrefix ring t rows C).get =
      runLocalSchedule ring T C.get ((rows.map Prod.fst).take t) := by
  induction rows generalizing C t with
  | nil => cases t <;> rfl
  | cons row rest ih =>
      cases t with
      | zero => rfl
      | succ t =>
          change
            (decide
                (T (C.get row.1)
                  (C.get (ring.rightNeighbor row.1)) = row.2) &&
              checkRows ring T rest (writeRow ring C row)) = true at h
          have hs := Bool.and_eq_true_iff.mp h
          have hp := of_decide_eq_true hs.1
          have hw := writeRow_correct ring T C row hp
          simpa only [rowPrefix, List.map_cons, List.take_succ_cons,
            runLocalSchedule, hw] using
              ih (writeRow ring C row) hs.2 t

def RowsValid {n : Nat} {Q : Type}
    (ring : DirectedRing n) (T : Q → Q → Q × Q) :
    List (Row n Q) → Vector Q n → Prop
  | [], _ => True
  | row :: rest, C =>
      T (C.get row.1) (C.get (ring.rightNeighbor row.1)) = row.2 ∧
        RowsValid ring T rest (writeRow ring C row)


theorem rowPrefix_correct_valid {n : Nat} {Q : Type}
    (ring : DirectedRing n) (T : Q → Q → Q × Q)
    (rows : List (Row n Q)) (C : Vector Q n)
    (h : RowsValid ring T rows C) (t : Nat) :
    (rowPrefix ring t rows C).get =
      runLocalSchedule ring T C.get ((rows.map Prod.fst).take t) := by
  induction rows generalizing C t with
  | nil => cases t <;> rfl
  | cons row rest ih =>
      change
        T (C.get row.1) (C.get (ring.rightNeighbor row.1)) = row.2 ∧
          RowsValid ring T rest (writeRow ring C row) at h
      cases t with
      | zero => rfl
      | succ t =>
          have hw := writeRow_correct ring T C row h.1
          simpa only [rowPrefix, List.map_cons, List.take_succ_cons,
            runLocalSchedule, hw] using
              ih (writeRow ring C row) h.2 t

#print axioms rowPrefix_correct

end BirthFiniteTraceCertificate
