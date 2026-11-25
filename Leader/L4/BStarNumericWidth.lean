import Leader.L4.BStarNumericWordFrame
import Leader.L4.BStarCmpReceipt

/-! Canonical live widths of the physical arithmetic payload. -/
namespace L4.BStarNumericWidth
open AllSizeProtocol BStarTrace BStarLongLayout BStarLongToken BStarLongCommand
  BStarLongRegisters BStarLongArithmetic BStarNumericCarry BStarLongSignatures
open L4.Compiler.Native

def codeKind : Code → Kind
  | .load q _ => if q.val=1 then .centerLoad else .unit
  | .mux .. => .mux
  | .add .. | .sub .. => .bitCarry
  | .shl3 .. => .shiftCarry
  | .cmp .. => .cmp
  | .scan5 .. => .scan
  | _ => .unit

private def rowMatches (j : Nat) : Bool :=
  (tourNodes[j]?.bind get).isSome &&
    decide (arithmetic[j]?=(tourNodes[j]?.bind get).map codeKind)

private theorem table : (List.range 395).all rowMatches=true := by decide +kernel

theorem kind_exact {op i : Nat} {c : Code} (L : 13≤op) (U : op<408)
    (N : nodeOf op=some i) (K : get i=some c) : arithKind op=some (codeKind c) := by
  have H : op-13<395 := by omega
  have T := List.all_eq_true.mp table _ (List.mem_range.mpr H)
  unfold nodeOf at N
  unfold arithKind
  rw [if_neg (Nat.not_lt.mpr L)] at N ⊢
  simp [rowMatches,N,K] at T
  exact T

theorem width_numeric {op n : Nat} (L : 13≤op) (U : op<408) :
    forwardWidth op n = (match arithKind op with
    | some .centerLoad => if n%4 != 3 then some 2 else none
    | some .mux | some .bitCarry => some 1
    | some .shiftCarry => some 3
    | some .cmp => some 2
    | some .scan => some 5
    | _ => some 0) := by
  have A : op≠admit := by unfold admit; omega
  have B : op≠bitOp := by unfold bitOp; omega
  have C : op≠acquire := by unfold acquire; omega
  have D : op≠copyLoad := by unfold copyLoad; omega
  have E : op≠stageOp := by unfold stageOp; omega
  have F : op≠sealOp := by unfold sealOp; omega
  have G : op≠commitOp := by unfold commitOp; omega
  unfold forwardWidth
  simp [A,B,C,D,E,F,G]
  generalize arithKind op = t
  cases t with
  | none => rfl
  | some a => cases a <;> rfl

private theorem widths : wordWidths.all (fun j => decide (j≤4))=true := by decide +kernel

private theorem widthAt_le (ws : List Nat) (H : ws.all (fun j => decide (j≤4))=true)
    (i : Nat) : widthAt ws i≤4 := by
  induction ws generalizing i with
  | nil => simp [widthAt]
  | cons a as ih =>
    simp only [List.all_cons,Bool.and_eq_true,decide_eq_true_eq] at H
    cases i with
    | zero => exact H.1
    | succ i => exact ih H.2 i

private theorem num_small (x : BitVec LW) (i : Nat) : num x i<16 :=
  Nat.lt_of_lt_of_le ((numeric i).read x).isLt
    (Nat.pow_le_pow_right (by decide) (widthAt_le _ widths _))

theorem digit_width (g : LongGeometry) (x : BitVec LW) (i : Nat) (c : Code)
    (p : Payload) (P : Numeric p) (N : nodeOf p.opcode.toNat=some i) (K : get i=some c)
    (k : Nat) (W : forwardWidth p.opcode.toNat p.argument.toNat=some k)
    (A : p.argument.toNat<2^k) (F : (physicalDigit g x i c p).2.fault=0) :
    let q := (physicalDigit g x i c p).2
    forwardWidth q.opcode.toNat q.argument.toNat=some k ∧ q.argument.toNat<2^k ∧
      q.race=p.race ∧ q.outcome=p.outcome := by
  have opcode := (digit_numeric g x i c p P F).2
  dsimp only
  rw [opcode,width_numeric P.2.1 P.2.2,kind_exact P.2.1 P.2.2 N K]
  rw [width_numeric P.2.1 P.2.2,kind_exact P.2.1 P.2.2 N K] at W
  cases c <;> simp [physicalDigit,codeKind,BitVec.toNat_ofNat] at F W A ⊢ <;> try exact ⟨W,A⟩
  case load q f =>
    cases E : digitLoad x q f p.argument.toNat <;> simp_all
  case add j l =>
    have h := num_small x j
    have h' := num_small x l
    subst k
    simp at A ⊢
    omega
  case sub j l =>
    subst k
    split <;> decide
  case shl3 j =>
    have h := num_small x j
    subst k
    simp at A ⊢
    omega
  case cmp j l =>
    subst k
    generalize Q : ((p.argument.toNat / 2 == 1) && (num x j == num x l)) = b
    generalize R : (if num x j = num x l then p.argument.toNat % 2 == 1 else decide (num x j < num x l)) = d
    cases b <;> cases d <;> decide
  case scan5 j =>
    have h := num_small x j
    subst k
    simp at A ⊢
    generalize (if g.axes.h6 = true then 0 else min 5 g.offset) = off
    split
    · have E : p.argument.toNat / 16 ≤ 1 := by omega
      omega
    · split
      · omega
      · omega

end L4.BStarNumericWidth
