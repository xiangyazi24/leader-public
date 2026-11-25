import Leader.L4.BStarLongLayout
import Leader.L4.BStarLongRegisterData

/-! Source/numeric register allocation. This is only the finite
field allocator, not the compiler instruction list or the
semantic implementation of a primitive. -/
namespace L4.BStarLongRegisters
open AllSizeProtocol BStarTrace BStarLongLayout
open BStarLongRegisterData

def wordWidths : List Nat := nodeWidths.map (fun w => 4*w.1)
def scalarWidths : List Nat := nodeWidths.map Prod.snd

set_option maxRecDepth 4096 in
theorem manifest_registers : nodeWidths.length=474 ∧
    wordWidths.sum=728 ∧ scalarWidths.sum=369 := by decide

/-- Low address and width of a node in a descending list. Absent
and 0-width nodes have empty support; there is no in-band address. -/
def widthAt : List Nat → Nat → Nat
  | [],_ => 0
  | w::_,0 => w
  | _::ws,i+1 => widthAt ws i

def offsetAt (ws : List Nat) (i : Nat) : Nat := (ws.drop (i+1)).sum

theorem range_bound (ws : List Nat) (i : Nat) :
    offsetAt ws i+widthAt ws i≤ws.sum := by
  induction ws generalizing i with
  | nil => simp [offsetAt,widthAt]
  | cons w ws ih =>
    cases i with
    | zero => simp [offsetAt,widthAt,Nat.add_comm]
    | succ i => simp only [offsetAt,widthAt,List.drop_succ_cons,List.sum_cons] at *
                exact Nat.le_trans (ih i) (Nat.le_add_left _ _)

theorem slots_order (ws : List Nat) (i j : Nat) (h : i<j) :
    offsetAt ws j+widthAt ws j≤offsetAt ws i := by
  induction ws generalizing i j with
  | nil => simp [offsetAt,widthAt]
  | cons w ws ih =>
    cases i with
    | zero =>
      cases j with
      | zero => omega
      | succ j => simpa [offsetAt,widthAt] using range_bound ws j
    | succ i =>
      cases j with
      | zero => omega
      | succ j => exact ih i j (Nat.lt_of_succ_lt_succ h)

def numeric (i : Nat) : Field LW (widthAt wordWidths i) :=
  ⟨offsetAt wordWidths i,by
    have h := range_bound wordWidths i
    rw [manifest_registers.2.1] at h
    rw [production_long_width]
    omega⟩

def scalar (i : Nat) : Field LW (widthAt scalarWidths i) :=
  ⟨1764+offsetAt scalarWidths i,by
    have h := range_bound scalarWidths i
    rw [manifest_registers.2.2] at h
    rw [production_long_width]
    omega⟩

theorem numeric_distinct (i j : Nat) (h : i≠j) : Disjoint (numeric i) (numeric j) := by
  rcases Nat.lt_or_gt_of_ne h with H | H
  · exact Or.inr (slots_order wordWidths i j H)
  · exact Or.inl (slots_order wordWidths j i H)

theorem scalar_distinct (i j : Nat) (h : i≠j) : Disjoint (scalar i) (scalar j) := by
  rcases Nat.lt_or_gt_of_ne h with H | H
  · right
    have h := slots_order scalarWidths i j H
    simp only [scalar]
    omega
  · left
    have h := slots_order scalarWidths j i H
    simp only [scalar]
    omega

theorem numeric_scalar (i j : Nat) : Disjoint (numeric i) (scalar j) := by
  left
  have h := range_bound wordWidths i
  rw [manifest_registers.2.1] at h
  simp only [numeric,scalar]
  omega

theorem scalar_before_choice (i : Nat) :
    (scalar i).offset+widthAt scalarWidths i≤choice.offset := by
  have h := range_bound scalarWidths i
  rw [manifest_registers.2.2] at h
  simp only [scalar,choice]
  omega

private theorem not_live_at {ws : List Nat} (i : Nat) (h : ws.length≤i) :
    widthAt ws i=0 := by
  induction ws generalizing i with
  | nil => simp [widthAt]
  | cons w ws ih =>
    cases i with
    | zero => simp at h
    | succ i => exact ih i (by simpa using h)

/-- A spare CODE address does not point into any other field. -/
theorem spare (i : Nat) (h : 474≤i) :
    widthAt wordWidths i=0 ∧ widthAt scalarWidths i=0 := by
  constructor <;> apply not_live_at <;>
    simpa only [wordWidths,scalarWidths,List.length_map,manifest_registers.1] using h

theorem examples :
    widthAt scalarWidths 28=1 ∧ widthAt wordWidths 29=4 ∧
    widthAt scalarWidths 29=0 ∧ widthAt scalarWidths 195=1 ∧
    widthAt scalarWidths 263=1 := by decide

end L4.BStarLongRegisters
