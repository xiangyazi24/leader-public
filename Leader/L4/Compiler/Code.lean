import Leader.L4.Compiler.Interp

/-!
# The r-independent opcode layer of the native ALU program

This file fixes the contract shared by the stage modules of `generated_native`.

* `Code` has one constructor per opcode of the reference ALU emitter.
* `toInstr T bank` maps a `Code` to an interpreter instruction, given a table
  `T` of concrete digit-serial primitives and the three held banks.
* `PrimSem T bank` records the word denotation of each primitive. Every input
  word is read modulo `16 ^ r`, as the digit-serial primitives do. A concrete
  instance is proved separately from `Digits` / `DigitsWords`.
* `eval_prefix` and `eval_new` are the two generic lookup lemmas used by every
  stage lemma.

Comparison results are words: `1` when equal, `2` when less, `0` otherwise.
`cmpEq` and `cmpLt` and `phaseEq` are Boolean projections of a word register
through `BoolOp.wordEq`.
-/

namespace L4
namespace Compiler
namespace Native

open Interp

/-- The word constants that the reference emitter loads. -/
inductive ConstId
  | zero
  | one
  | p
  | bm1
  | max
  | eight
deriving Repr, DecidableEq

/-- The value of a constant at radix exponent `r` (`M = 16 ^ r`). -/
def ConstId.val (r : Nat) : ConstId → Nat
  | .zero => 0
  | .one => 1
  | .p => 16 ^ r / 2
  | .bm1 => 16 ^ (r - 2) - 1
  | .max => 16 ^ r - 1
  | .eight => 8

/-- One constructor per opcode of the reference emitter. Register arguments are indices of
earlier registers. Sides are `0 = L`, `1 = C`, `2 = R`. -/
inductive Code
  | load (side : Fin 3) (field : Fin 9)
  | header (side : Fin 3) (bit : Fin 9)
  | const (c : ConstId)
  | bconst (b : Bool)
  | maskB (a : Nat)
  | add (a b : Nat)
  | sub (a b : Nat)
  | shl3 (a : Nat)
  /-- word multiplexer with Boolean selector `q`: `a` if `q`, else `b` -/
  | mux (q a b : Nat)
  | cmp (a b : Nat)
  | cmpEq (c : Nat)
  | cmpLt (c : Nat)
  | not (a : Nat)
  | and (a b : Nat)
  | or (a b : Nat)
  /-- Boolean multiplexer: `a` if `q`, else `b` -/
  | bmux (q a b : Nat)
  | scan5 (a : Nat)
  | phaseEq (a j : Nat)
deriving Repr, DecidableEq

/-- The three held banks: nine raw words and nine header bits per side. -/
structure Bank where
  digits : Fin 3 → Fin 9 → Nat
  hdr : Fin 3 → Fin 9 → Bool

/-- The concrete digit-serial primitives used by the word opcodes. -/
structure PrimTable (r : Nat) where
  load : Fin 3 → Fin 9 → Primitive r
  const : ConstId → Primitive r
  maskB : Primitive r
  add : Primitive r
  sub : Primitive r
  shl3 : Primitive r
  mux : Primitive r
  cmp : Primitive r
  scan5 : Primitive r

def toInstr {r : Nat} (T : PrimTable r) (bank : Bank) : Code → Instr r
  | .load q i => .word (T.load q i) []
  | .header q i => .source (.literal (bank.hdr q i))
  | .const c => .word (T.const c) []
  | .bconst b => .source (.literal b)
  | .maskB a => .word T.maskB [a]
  | .add a b => .word T.add [a, b]
  | .sub a b => .word T.sub [a, b]
  | .shl3 a => .word T.shl3 [a]
  | .mux q a b => .word T.mux [q, a, b]
  | .cmp a b => .word T.cmp [a, b]
  | .cmpEq c => .source (.wordEq c 1)
  | .cmpLt c => .source (.wordEq c 2)
  | .not a => .source (.not a)
  | .and a b => .source (.and a b)
  | .or a b => .source (.or a b)
  | .bmux q a b => .source (.mux q a b)
  | .scan5 a => .word T.scan5 [a]
  | .phaseEq a j => .source (.wordEq a j)

/-- Word denotation of a primitive on argument values. -/
def den {r : Nat} (p : Primitive r) (vs : List Value) : Nat :=
  p.denotation (p.inputOf vs)

/-- The `k`-th argument read as a word modulo `16 ^ r`. -/
def argW (r : Nat) (vs : List Value) (k : Nat) : Nat :=
  (vs.getD k (.word 0)).asWord % 16 ^ r

/-- The `k`-th argument read as a Boolean. -/
def argB (vs : List Value) (k : Nat) : Bool :=
  (vs.getD k (.word 0)).asBool

/-- Comparison result encoded as a word. -/
def cmpCode (a b : Nat) : Nat :=
  if a = b then 1 else if a < b then 2 else 0

/-- Word denotations of the primitive table. -/
structure PrimSem {r : Nat} (T : PrimTable r) (bank : Bank) : Prop where
  load : ∀ q i vs, den (T.load q i) vs = bank.digits q i % 16 ^ r
  const : ∀ c vs, den (T.const c) vs = c.val r % 16 ^ r
  maskB : ∀ vs, den T.maskB vs = argW r vs 0 % 16 ^ (r - 2)
  add : ∀ vs, den T.add vs = (argW r vs 0 + argW r vs 1) % 16 ^ r
  sub : ∀ vs, den T.sub vs = (argW r vs 0 + 16 ^ r - argW r vs 1) % 16 ^ r
  shl3 : ∀ vs, den T.shl3 vs = (8 * argW r vs 0) % 16 ^ r
  mux : ∀ vs, den T.mux vs = (if argB vs 0 then argW r vs 1 else argW r vs 2)
  cmp : ∀ vs, den T.cmp vs = cmpCode (argW r vs 0) (argW r vs 1)
  scan5 : ∀ vs, den T.scan5 vs = argW r vs 0 % 32

/-- Run a list of codes from given registers. -/
def runCodes {r : Nat} (T : PrimTable r) (bank : Bank)
    (regs : List Value) (P : List Code) : List Value :=
  evalProgramAux regs (P.map (toInstr T bank))

theorem evalProgramAux_prefix {r : Nat} (regs : List Value) (P : List (Instr r)) :
    ∃ ext, evalProgramAux regs P = regs ++ ext := by
  induction P generalizing regs with
  | nil => exact ⟨[], by simp [evalProgramAux]⟩
  | cons x xs ih =>
      obtain ⟨ext, h⟩ := ih (regs ++ [evalInstr x regs])
      exact ⟨[evalInstr x regs] ++ ext, by
        rw [evalProgramAux_cons, h, List.append_assoc]⟩

theorem readReg_append_left (l ext : List Value) (i : Nat) (h : i < l.length) :
    readReg (l ++ ext) i = readReg l i := by
  unfold readReg
  rw [List.getElem?_append_left h]

/-- Registers computed before a program are unchanged by it. -/
theorem eval_prefix {r : Nat} (regs : List Value) (P : List (Instr r))
    (i : Nat) (h : i < regs.length) :
    readReg (evalProgramAux regs P) i = readReg regs i := by
  obtain ⟨ext, hext⟩ := evalProgramAux_prefix regs P
  rw [hext, readReg_append_left _ _ _ h]

/-- The register written by the `k`-th instruction. -/
theorem eval_new {r : Nat} (regs : List Value) (P : List (Instr r))
    (k : Nat) (hk : k < P.length) :
    readReg (evalProgramAux regs P) (regs.length + k) =
      evalInstr (P[k]'hk) (evalProgramAux regs (P.take k)) := by
  have hsplit : P = P.take k ++ (P[k]'hk :: P.drop (k + 1)) := by
    simp
  conv => lhs; rw [hsplit]
  rw [evalProgramAux_append, evalProgramAux_cons]
  have hlen : (evalProgramAux regs (P.take k)).length = regs.length + k := by
    rw [evalProgramAux_length, List.length_take]
    omega
  rw [eval_prefix]
  · unfold readReg
    rw [← hlen, List.getElem?_append_right (Nat.le_refl _)]
    simp
  · rw [List.length_append, hlen]
    simp

/-- `eval_new` for a run of codes. -/
theorem runCodes_new {r : Nat} (T : PrimTable r) (bank : Bank)
    (regs : List Value) (P : List Code) (k : Nat) (hk : k < P.length) :
    readReg (runCodes T bank regs P) (regs.length + k) =
      evalInstr (toInstr T bank (P[k]'hk)) (runCodes T bank regs (P.take k)) := by
  unfold runCodes
  have hk' : k < (P.map (toInstr T bank)).length := by simpa using hk
  rw [eval_new _ _ k hk', List.map_take]
  simp

theorem runCodes_prefix {r : Nat} (T : PrimTable r) (bank : Bank)
    (regs : List Value) (P : List Code) (i : Nat) (h : i < regs.length) :
    readReg (runCodes T bank regs P) i = readReg regs i :=
  eval_prefix _ _ _ h

theorem runCodes_append {r : Nat} (T : PrimTable r) (bank : Bank)
    (regs : List Value) (P Q : List Code) :
    runCodes T bank regs (P ++ Q) = runCodes T bank (runCodes T bank regs P) Q := by
  unfold runCodes
  rw [List.map_append, evalProgramAux_append]

theorem runCodes_length {r : Nat} (T : PrimTable r) (bank : Bank)
    (regs : List Value) (P : List Code) :
    (runCodes T bank regs P).length = regs.length + P.length := by
  unfold runCodes
  rw [evalProgramAux_length, List.length_map]


/-! ## Evaluation simp set

With `subst hlen` (so `base` becomes `regs.length`), `simp only [evalSimp-lemmas]`
evaluates a concrete stage trace symbolically: appended registers are read by
`readReg_append_len`, earlier ones by `readReg_append_left`. -/

theorem readReg_append_len (l ext : List Value) (j : Nat) :
    readReg (l ++ ext) (l.length + j) = readReg ext j := by
  unfold readReg
  rw [List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left]

theorem readReg_cons_zero (v : Value) (l : List Value) : readReg (v :: l) 0 = v := rfl

theorem readReg_cons_succ (v : Value) (l : List Value) (j : Nat) :
    readReg (v :: l) (j + 1) = readReg l j := rfl

theorem readReg_append_len_zero (l ext : List Value) :
    readReg (l ++ ext) l.length = readReg ext 0 := by
  simpa using readReg_append_len l ext 0

theorem readArgs_nil (regs : List Value) : readArgs regs [] = [] := rfl

theorem readArgs_cons (regs : List Value) (a : Nat) (as : List Nat) :
    readArgs regs (a :: as) = readReg regs a :: readArgs regs as := rfl

theorem evalInstr_word {r : Nat} (p : Primitive r) (args : List Nat) (regs : List Value) :
    evalInstr (.word p args) regs = .word (den p (readArgs regs args)) := rfl

theorem evalInstr_source {r : Nat} (op : BoolOp) (regs : List Value) :
    evalInstr (Instr.source (r := r) op) regs = .boolean (evalBoolOp op regs) := rfl

theorem runCodes_nil {r : Nat} (T : PrimTable r) (bank : Bank) (regs : List Value) :
    runCodes T bank regs [] = regs := rfl

theorem runCodes_cons {r : Nat} (T : PrimTable r) (bank : Bank) (regs : List Value)
    (c : Code) (P : List Code) :
    runCodes T bank regs (c :: P) =
      runCodes T bank (regs ++ [evalInstr (toInstr T bank c) regs]) P := rfl

theorem asWord_word (n : Nat) : (Value.word n).asWord = n := rfl
theorem asBool_boolean (b : Bool) : (Value.boolean b).asBool = b := rfl

theorem argW_cons_zero (r : Nat) (v : Value) (vs : List Value) :
    argW r (v :: vs) 0 = v.asWord % 16 ^ r := rfl
theorem argW_cons_succ (r : Nat) (v : Value) (vs : List Value) (k : Nat) :
    argW r (v :: vs) (k + 1) = argW r vs k := rfl
theorem argB_cons_zero (v : Value) (vs : List Value) : argB (v :: vs) 0 = v.asBool := rfl
theorem argB_cons_succ (v : Value) (vs : List Value) (k : Nat) :
    argB (v :: vs) (k + 1) = argB vs k := rfl

theorem cmpCode_eq_one (a b : Nat) : (cmpCode a b == 1) = decide (a = b) := by
  unfold cmpCode
  by_cases h : a = b
  · simp [h]
  · by_cases h' : a < b <;> simp [h, h']

theorem cmpCode_eq_two (a b : Nat) : (cmpCode a b == 2) = decide (a < b) := by
  unfold cmpCode
  by_cases h : a = b
  · subst h; simp
  · by_cases h' : a < b <;> simp [h, h']

end Native
end Compiler
end L4

#print axioms L4.Compiler.Native.eval_prefix
#print axioms L4.Compiler.Native.eval_new
#print axioms L4.Compiler.Native.runCodes_new
#print axioms L4.Compiler.Native.runCodes_append
