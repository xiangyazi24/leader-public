import Leader.Core.Basic
import Init.Grind

/-!
# Exact residual work for one serialized five-pass lane

This file isolates the arithmetic part of the proposed PPLL paired-defect
transaction.  A lane of `ell` carrier cells executes

`ReqR ; Ack1L ; CommitR ; Ack2L ; ReleaseR`.

The four endpoint turns are real scheduled interactions.  The usual
`5 * ell` cell-rewrite count therefore is not, by itself, a unit-decreasing
rank for every useful physical interaction.  The rank below charges those
turns explicitly.  Its initial value is `5 * ell + 4`, and every listed
service decreases it by exactly one.  For a nonempty lane this is at most
`9 * ell`.

This is a semantic arithmetic module.  It does not assert that an arbitrary
physical configuration already has a unique canonical head, nor that dirty
states enter this serialized lifecycle.
-/

namespace PPLLFivePassResidual

set_option autoImplicit false

/-! ## The current `F*E*R*` lane -/

inductive LaneMark where
  | F
  | E
  | R
  deriving DecidableEq, Repr

/-- Unique cuts for the current word `F^a E^(b-a) R^(ell-b)`. -/
structure LaneCuts (ell : Nat) where
  a : Nat
  b : Nat
  a_le_b : a ≤ b
  b_le_length : b ≤ ell
  deriving DecidableEq, Repr

def markAt {ell : Nat} (c : LaneCuts ell) (i : Fin ell) : LaneMark :=
  if i.val < c.a then .F else if i.val < c.b then .E else .R

/-- `ReqR` changes the first `E` into `F`. -/
def reqMove {ell : Nat} (c : LaneCuts ell) (h : c.a < c.b) :
    LaneCuts ell where
  a := c.a + 1
  b := c.b
  a_le_b := by omega
  b_le_length := c.b_le_length

/-- `NackL` changes the last `F` into `E`. -/
def nackMove {ell : Nat} (c : LaneCuts ell) (h : 0 < c.a) :
    LaneCuts ell where
  a := c.a - 1
  b := c.b
  a_le_b := by
    have hab := c.a_le_b
    omega
  b_le_length := c.b_le_length

/-- `ReleaseR` changes the first `R` into `E`. -/
def releaseMove {ell : Nat} (c : LaneCuts ell) (h : c.b < ell) :
    LaneCuts ell where
  a := c.a
  b := c.b + 1
  a_le_b := by
    have hab := c.a_le_b
    omega
  b_le_length := by omega

/-- A left acknowledgement on a diagonal cut changes the last `F` to `R`. -/
def ackMove {ell : Nat} (c : LaneCuts ell) (hdiag : c.a = c.b)
    (hpos : 0 < c.a) : LaneCuts ell where
  a := c.a - 1
  b := c.b - 1
  a_le_b := by omega
  b_le_length := by
    have hb := c.b_le_length
    omega

/-- A right commit on a diagonal cut changes the first `R` to `F`. -/
def commitMove {ell : Nat} (c : LaneCuts ell) (hdiag : c.a = c.b)
    (hroom : c.b < ell) : LaneCuts ell where
  a := c.a + 1
  b := c.b + 1
  a_le_b := by omega
  b_le_length := by omega

theorem reqMove_boundary {ell : Nat} (c : LaneCuts ell) (h : c.a < c.b) :
    markAt c ⟨c.a, by
      have hb := c.b_le_length
      omega⟩ = .E ∧
      markAt (reqMove c h) ⟨c.a, by
        have hb := c.b_le_length
        omega⟩ = .F := by
  constructor <;> simp [markAt, reqMove] <;> omega

theorem nackMove_boundary {ell : Nat} (c : LaneCuts ell) (h : 0 < c.a) :
    markAt c ⟨c.a - 1, by
      have := c.a_le_b
      have := c.b_le_length
      omega⟩ = .F ∧
      markAt (nackMove c h) ⟨c.a - 1, by
        have := c.a_le_b
        have := c.b_le_length
        omega⟩ = .E := by
  have hab := c.a_le_b
  have hpred : c.a - 1 < c.a := by omega
  have hltb : c.a - 1 < c.b := by omega
  constructor
  · simp [markAt, hpred]
  · simp [markAt, nackMove, hltb]

theorem releaseMove_boundary {ell : Nat} (c : LaneCuts ell)
    (h : c.b < ell) :
    markAt c ⟨c.b, by omega⟩ = .R ∧
      markAt (releaseMove c h) ⟨c.b, by omega⟩ = .E := by
  have hab := c.a_le_b
  constructor <;> simp [markAt, releaseMove] <;> omega

theorem ackMove_boundary {ell : Nat} (c : LaneCuts ell)
    (hdiag : c.a = c.b) (hpos : 0 < c.a) :
    markAt c ⟨c.a - 1, by
      have := c.a_le_b
      have := c.b_le_length
      omega⟩ = .F ∧
      markAt (ackMove c hdiag hpos) ⟨c.a - 1, by
        have := c.a_le_b
        have := c.b_le_length
        omega⟩ = .R := by
  have hpred : c.a - 1 < c.a := by omega
  have hsub : c.a - 1 = c.b - 1 := by omega
  have hnot : ¬ c.a - 1 < c.b - 1 := by omega
  constructor
  · simp [markAt, hpred]
  · simp [markAt, ackMove, hnot]

theorem commitMove_boundary {ell : Nat} (c : LaneCuts ell)
    (hdiag : c.a = c.b) (hroom : c.b < ell) :
    markAt c ⟨c.a, by omega⟩ = .R ∧
      markAt (commitMove c hdiag hroom) ⟨c.a, by omega⟩ = .F := by
  constructor <;> simp [markAt, commitMove] <;> omega

/-! ## Exact serialized residual -/

/-- Pure phases of one successful serialized transaction. -/
inductive PurePhase where
  | req
  | ack1
  | commit
  | ack2
  | release
  | done
  deriving DecidableEq, Repr

/-- `pos` is a proof coordinate, not a proposed local-state field.

For the four first phases it is the size of the current `F` prefix.  During
`release` it is the size of the current `E` prefix. -/
structure PureState where
  phase : PurePhase
  pos : Nat
  deriving DecidableEq, Repr

/-- The coordinate is inside the lane; the terminal state has coordinate 0. -/
def Valid (ell : Nat) (s : PureState) : Prop :=
  s.pos ≤ ell ∧ (s.phase = .done → s.pos = 0)

/-- Exact remaining useful interactions, including endpoint turns. -/
def work (ell : Nat) : PureState → Nat
  | ⟨.req, a⟩ => 5 * ell + 4 - a
  | ⟨.ack1, a⟩ => 3 * ell + a + 3
  | ⟨.commit, a⟩ => 3 * ell + 2 - a
  | ⟨.ack2, a⟩ => ell + a + 1
  | ⟨.release, b⟩ => ell - b
  | ⟨.done, _⟩ => 0

/-- Literal useful services of the pure five-pass lifecycle.

The four `turn` constructors represent scheduled endpoint interactions.  The
final release cell leaves the state at `release ell`, whose work is already
zero; terminal observation itself is not charged as another interaction. -/
inductive Service (ell : Nat) : PureState → PureState → Prop
  | reqCell (a : Nat) (ha : a < ell) :
      Service ell ⟨.req, a⟩ ⟨.req, a + 1⟩
  | reqTurn :
      Service ell ⟨.req, ell⟩ ⟨.ack1, ell⟩
  | ack1Cell (a : Nat) (ha : 0 < a) (haell : a ≤ ell) :
      Service ell ⟨.ack1, a⟩ ⟨.ack1, a - 1⟩
  | ack1Turn :
      Service ell ⟨.ack1, 0⟩ ⟨.commit, 0⟩
  | commitCell (a : Nat) (ha : a < ell) :
      Service ell ⟨.commit, a⟩ ⟨.commit, a + 1⟩
  | commitTurn :
      Service ell ⟨.commit, ell⟩ ⟨.ack2, ell⟩
  | ack2Cell (a : Nat) (ha : 0 < a) (haell : a ≤ ell) :
      Service ell ⟨.ack2, a⟩ ⟨.ack2, a - 1⟩
  | ack2Turn :
      Service ell ⟨.ack2, 0⟩ ⟨.release, 0⟩
  | releaseCell (b : Nat) (hb : b < ell) :
      Service ell ⟨.release, b⟩ ⟨.release, b + 1⟩

theorem service_preserves_valid {ell : Nat} {s t : PureState}
    (hs : Valid ell s) (hst : Service ell s t) : Valid ell t := by
  cases hst <;> simp_all [Valid] <;> omega

/-- Every carrier rewrite and every endpoint turn consumes exactly one unit. -/
theorem work_eq_succ {ell : Nat} {s t : PureState}
    (hst : Service ell s t) : work ell s = work ell t + 1 := by
  cases hst <;> simp [work] <;> omega

theorem work_strictly_decreases {ell : Nat} {s t : PureState}
    (hst : Service ell s t) : work ell t < work ell s := by
  rw [work_eq_succ hst]
  omega

/-- Exact cost of a clean attempt before its first service. -/
theorem initial_work (ell : Nat) :
    work ell ⟨.req, 0⟩ = 5 * ell + 4 := by
  simp [work]

/-- Nonempty lanes absorb all four turn credits into a linear envelope. -/
theorem initial_work_le_nine_mul {ell : Nat} (hell : 0 < ell) :
    work ell ⟨.req, 0⟩ ≤ 9 * ell := by
  rw [initial_work]
  omega

/-- The zero-interior-cell case is not covered by the nonempty-lane bound.
It must be implemented by the separate adjacent-root shared-edge transition. -/
theorem empty_lane_initial_work : work 0 ⟨.req, 0⟩ = 4 := by
  decide

/-- Sum of the exact per-gap ranks.  Here each entry is the number of
interior carrier cells in one cyclic gap. -/
def totalWork (interiors : List Nat) : Nat :=
  (interiors.map fun ell => 5 * ell + 4).sum

/-- Number of physical scheduler-edge slots covered by the cyclic gaps.
Each gap contains its `ell` interior carrier edges and one boundary edge. -/
def totalSpan (interiors : List Nat) : Nat :=
  (interiors.map fun ell => ell + 1).sum

/-- Exact global accounting.  The four turn credits per gap fit inside five
charges for its boundary edge:

`sum_g (5 * ell_g + 4) + numberOfGaps = 5 * sum_g (ell_g + 1)`.

Thus the physical cyclic partition recovers the clean global `5 * n` bound,
even though the per-gap rank is not `5 * ell`. -/
theorem totalWork_add_length_eq_five_mul_totalSpan (interiors : List Nat) :
    totalWork interiors + interiors.length = 5 * totalSpan interiors := by
  induction interiors with
  | nil => simp [totalWork, totalSpan]
  | cons ell interiors ih =>
      simp only [totalWork, totalSpan, List.map_cons, List.sum_cons,
        List.length_cons] at ih ⊢
      omega

theorem totalWork_le_five_mul_totalSpan (interiors : List Nat) :
    totalWork interiors ≤ 5 * totalSpan interiors := by
  rw [← totalWork_add_length_eq_five_mul_totalSpan]
  omega

end PPLLFivePassResidual
