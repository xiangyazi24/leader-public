import Lean

namespace L4
namespace Compiler
namespace Interp

inductive RegType
  | word
  | boolean
deriving DecidableEq, Repr

inductive Value
  | word (n : Nat)
  | boolean (b : Bool)
deriving DecidableEq, Repr

def Value.type : Value → RegType
  | .word _ => .word
  | .boolean _ => .boolean

def Value.asBool : Value → Bool
  | .boolean b => b
  | _ => false

def Value.asWord : Value → Nat
  | .word n => n
  | _ => 0

abbrev DigitState := Nat

structure Primitive (r : Nat) where
  Input : Type
  Digit : Type
  inputOf : List Value → Input
  digit : Input → Fin r → Digit
  init : Input → DigitState
  step : Fin r → DigitState → Digit → DigitState
  Inv : Input → Nat → DigitState → Prop
  denotation : Input → Nat
  finish : DigitState → Nat
  inv_zero : ∀ x, Inv x 0 (init x)
  inv_step : ∀ x j (hj : j < r) s,
    Inv x j s →
    Inv x (j + 1) (step ⟨j, hj⟩ s (digit x ⟨j, hj⟩))
  inv_done : ∀ x s, Inv x r s → finish s = denotation x

def runPrefix (p : Primitive r) (x : p.Input) :
    (j : Nat) → j ≤ r → DigitState
  | 0, _ => p.init x
  | j + 1, h =>
      p.step ⟨j, Nat.lt_of_succ_le h⟩
        (runPrefix p x j (Nat.le_of_succ_le h))
        (p.digit x ⟨j, Nat.lt_of_succ_le h⟩)

theorem runPrefix_inv (p : Primitive r) (x : p.Input) :
    ∀ j (h : j ≤ r), p.Inv x j (runPrefix p x j h) := by
  intro j
  induction j with
  | zero =>
      intro h
      exact p.inv_zero x
  | succ j ih =>
      intro h
      apply p.inv_step x j (Nat.lt_of_succ_le h)
      exact ih (Nat.le_of_succ_le h)

theorem primitive_tour_correct (p : Primitive r) (x : p.Input) :
    p.finish (runPrefix p x r (Nat.le_refl r)) = p.denotation x :=
  p.inv_done x _ (runPrefix_inv p x r (Nat.le_refl r))

theorem primitive_initial_inv (p : Primitive r) (x : p.Input) :
    p.Inv x 0 (p.init x) :=
  p.inv_zero x

theorem primitive_step_inv (p : Primitive r) (x : p.Input)
    (j : Nat) (hj : j < r) (s : DigitState)
    (h : p.Inv x j s) :
    p.Inv x (j + 1) (p.step ⟨j, hj⟩ s (p.digit x ⟨j, hj⟩)) :=
  p.inv_step x j hj s h

theorem primitive_done (p : Primitive r) (x : p.Input)
    (s : DigitState) (h : p.Inv x r s) :
    p.finish s = p.denotation x :=
  p.inv_done x s h

inductive BoolOp
  | literal (b : Bool)
  | not (a : Nat)
  | and (a b : Nat)
  | or (a b : Nat)
  | mux (q a b : Nat)
  /-- Boolean projection of a word register: `true` iff register `a` holds the word `c`.
  Used for comparison results (encoded as words), phase tests and header reads. -/
  | wordEq (a c : Nat)
deriving Repr, DecidableEq

inductive Instr (r : Nat)
  | word (p : Primitive r) (args : List Nat)
  | source (op : BoolOp)

def Instr.resultType : Instr r → RegType
  | .word _ _ => .word
  | .source _ => .boolean

def BoolOp.refs : BoolOp → List Nat
  | .literal _ => []
  | .not a => [a]
  | .and a b => [a, b]
  | .or a b => [a, b]
  | .mux q a b => [q, a, b]
  | .wordEq a _ => [a]

def Instr.refs : Instr r → List Nat
  | .word _ args => args
  | .source op => op.refs

def WellFormed (P : List (Instr r)) : Prop :=
  ∀ pc (hpc : pc < P.length), ∀ a,
    a ∈ (P[pc]'hpc).refs → a < pc

def readReg (regs : List Value) (i : Nat) : Value :=
  regs[i]?.getD (.word 0)

def readArgs (regs : List Value) (args : List Nat) : List Value :=
  args.map (readReg regs)

def evalBoolOp (op : BoolOp) (regs : List Value) : Bool :=
  match op with
  | .literal b => b
  | .not a => !(readReg regs a).asBool
  | .and a b => (readReg regs a).asBool && (readReg regs b).asBool
  | .or a b => (readReg regs a).asBool || (readReg regs b).asBool
  | .mux q a b =>
      if (readReg regs q).asBool then
        (readReg regs a).asBool
      else
        (readReg regs b).asBool
  | .wordEq a c => (readReg regs a).asWord == c

def evalInstr (ins : Instr r) (regs : List Value) : Value :=
  match ins with
  | .word p args =>
      .word (p.denotation (p.inputOf (readArgs regs args)))
  | .source op => .boolean (evalBoolOp op regs)

def evalProgramAux (regs : List Value) : List (Instr r) → List Value
  | [] => regs
  | ins :: rest =>
      evalProgramAux (regs ++ [evalInstr ins regs]) rest

def evalProgram (P : List (Instr r)) : List Value :=
  evalProgramAux [] P

theorem evalProgramAux_cons (regs : List Value)
    (ins : Instr r) (rest : List (Instr r)) :
    evalProgramAux regs (ins :: rest) =
      evalProgramAux (regs ++ [evalInstr ins regs]) rest := rfl

theorem evalProgramAux_append
    (regs : List Value) (xs ys : List (Instr r)) :
    evalProgramAux regs (xs ++ ys) =
      evalProgramAux (evalProgramAux regs xs) ys := by
  induction xs generalizing regs with
  | nil => rfl
  | cons x xs ih =>
      simp [evalProgramAux, ih]

theorem evalProgramAux_length
    (regs : List Value) (xs : List (Instr r)) :
    (evalProgramAux regs xs).length = regs.length + xs.length := by
  induction xs generalizing regs with
  | nil => simp [evalProgramAux]
  | cons x xs ih =>
      simp [evalProgramAux, ih, List.length_append]
      omega

structure MState (r : Nat) where
  rest : List (Instr r)
  j : Nat
  acc : DigitState
  regs : List Value

def initHeadAcc (rest : List (Instr r)) (regs : List Value) :
    DigitState :=
  match rest with
  | .word p args :: _ => p.init (p.inputOf (readArgs regs args))
  | _ => 0

def initMachine (P : List (Instr r)) : MState r :=
  { rest := P, j := 0, acc := initHeadAcc P [], regs := [] }

def markStep (s : MState r) : MState r :=
  match s.rest with
  | [] => s
  | .source op :: tail =>
      let regs' := s.regs ++ [.boolean (evalBoolOp op s.regs)]
      { rest := tail, j := 0, acc := initHeadAcc tail regs', regs := regs' }
  | .word p args :: tail =>
      if hj : s.j < r then
        let x := p.inputOf (readArgs s.regs args)
        let k : Fin r := ⟨s.j, hj⟩
        let acc' := p.step k s.acc (p.digit x k)
        if hlast : s.j + 1 = r then
          let regs' := s.regs ++ [.word (p.finish acc')]
          { rest := tail, j := 0, acc := initHeadAcc tail regs', regs := regs' }
        else
          { s with j := s.j + 1, acc := acc' }
      else
        s

def runMarks (s : MState r) : Nat → MState r
  | 0 => s
  | n + 1 => markStep (runMarks s n)

def runMachine (P : List (Instr r)) (k : Nat) : MState r :=
  runMarks (initMachine P) k

def instrCost (r : Nat) (ins : Instr r) : Nat :=
  match ins with
  | .word _ _ => r
  | .source _ => 1

def programCost (P : List (Instr r)) : Nat :=
  (P.map (instrCost r)).sum

theorem programCost_eq_map_sum (P : List (Instr r)) :
    programCost P =
      (P.map (fun ins =>
        match ins with
        | .word _ _ => r
        | .source _ => 1)).sum := rfl

theorem markStep_source (regs : List Value) (op : BoolOp)
    (tail : List (Instr r)) :
    markStep
      ({ rest := .source op :: tail, j := 0,
         acc := initHeadAcc (.source op :: tail) regs, regs := regs } : MState r)
      =
      { rest := tail, j := 0,
        acc := initHeadAcc tail (regs ++ [.boolean (evalBoolOp op regs)]),
        regs := regs ++ [.boolean (evalBoolOp op regs)] } := by
  rfl

theorem markStep_word (regs : List Value) (p : Primitive r)
    (args : List Nat) (tail : List (Instr r))
    (hj : 0 < r) :
    markStep
      ({ rest := .word p args :: tail, j := 0,
         acc := p.init (p.inputOf (readArgs regs args)), regs := regs } : MState r)
      =
      if hlast : 0 + 1 = r then
        { rest := tail, j := 0,
          acc := initHeadAcc tail
            (regs ++ [.word (p.finish
              (p.step ⟨0, by omega⟩
                (p.init (p.inputOf (readArgs regs args)))
                (p.digit (p.inputOf (readArgs regs args)) ⟨0, by omega⟩)))]),
          regs := regs ++ [.word (p.finish
              (p.step ⟨0, by omega⟩
                (p.init (p.inputOf (readArgs regs args)))
                (p.digit (p.inputOf (readArgs regs args)) ⟨0, by omega⟩)))] }
      else
        { rest := .word p args :: tail, j := 1,
          acc := p.step ⟨0, by omega⟩
            (p.init (p.inputOf (readArgs regs args)))
            (p.digit (p.inputOf (readArgs regs args)) ⟨0, by omega⟩),
          regs := regs } := by
  simp [markStep, hj]

/-! ### Running the machine: one instruction at a time -/

theorem runMarks_add (s : MState r) (a b : Nat) :
    runMarks s (a + b) = runMarks (runMarks s a) b := by
  induction b with
  | zero => rfl
  | succ b ih =>
      show markStep (runMarks s (a + b)) = markStep (runMarks (runMarks s a) b)
      rw [ih]

/-- A clean machine state: the head instruction has not started yet. -/
def clean (rest : List (Instr r)) (regs : List Value) : MState r :=
  { rest := rest, j := 0, acc := initHeadAcc rest regs, regs := regs }

/-- While a word instruction is in progress, the accumulator is the primitive's prefix. -/
theorem word_partial (p : Primitive r) (args : List Nat) (tail : List (Instr r))
    (regs : List Value) :
    ∀ d (hd : d < r),
      runMarks (clean (.word p args :: tail) regs) d =
        { rest := .word p args :: tail, j := d,
          acc := runPrefix p (p.inputOf (readArgs regs args)) d (Nat.le_of_lt hd),
          regs := regs } := by
  intro d
  induction d with
  | zero => intro _; rfl
  | succ d ih =>
      intro hd
      show markStep (runMarks (clean (.word p args :: tail) regs) d) = _
      rw [ih (by omega)]
      have hj : d < r := by omega
      have hl : ¬ (d + 1 = r) := by omega
      simp only [markStep, dif_pos hj, dif_neg hl]
      rfl

/-- A word instruction finishes after exactly `r` marks and appends its denotation. -/
theorem word_full (hr : 0 < r) (p : Primitive r) (args : List Nat) (tail : List (Instr r))
    (regs : List Value) :
    runMarks (clean (.word p args :: tail) regs) r =
      clean tail (regs ++ [evalInstr (.word p args) regs]) := by
  obtain ⟨d, hd⟩ : ∃ d, r = d + 1 := ⟨r - 1, by omega⟩
  subst hd
  show markStep (runMarks (clean (.word p args :: tail) regs) d) = _
  rw [word_partial p args tail regs d (by omega)]
  have hj : d < d + 1 := by omega
  simp only [markStep, dif_pos hj, dif_pos rfl]
  have htour := primitive_tour_correct p (p.inputOf (readArgs regs args))
  have e : p.step ⟨d, hj⟩ (runPrefix p (p.inputOf (readArgs regs args)) d (Nat.le_of_lt hj))
      (p.digit (p.inputOf (readArgs regs args)) ⟨d, hj⟩) =
      runPrefix p (p.inputOf (readArgs regs args)) (d + 1) (Nat.le_refl (d + 1)) := rfl
  rw [e, htour]
  rfl

/-- A source instruction finishes after one mark. -/
theorem source_full (op : BoolOp) (tail : List (Instr r)) (regs : List Value) :
    runMarks (clean (.source op :: tail) regs) 1 =
      clean tail (regs ++ [evalInstr (Instr.source (r := r) op) regs]) := rfl

theorem instr_full (hr : 0 < r) (ins : Instr r) (tail : List (Instr r)) (regs : List Value) :
    runMarks (clean (ins :: tail) regs) (instrCost r ins) =
      clean tail (regs ++ [evalInstr ins regs]) := by
  cases ins with
  | word p args => exact word_full hr p args tail regs
  | source op => exact source_full op tail regs

/-- Running a whole instruction list for its total cost evaluates it. -/
theorem run_program (hr : 0 < r) : ∀ (P : List (Instr r)) (regs : List Value),
    runMarks (clean P regs) (programCost P) = clean [] (evalProgramAux regs P) := by
  intro P
  induction P with
  | nil => intro regs; rfl
  | cons ins tail ih =>
      intro regs
      have hc : programCost (ins :: tail) = instrCost r ins + programCost tail := by
        simp [programCost, List.map_cons, List.sum_cons]
      rw [hc, runMarks_add, instr_full hr, ih]
      rfl

/-- The machine, run for the program's total cost from the initial state, holds exactly
the registers of the SSA evaluation. -/
theorem machine_finish (hr : 0 < r) (P : List (Instr r)) :
    (runMachine P (programCost P)).regs = evalProgram P := by
  have h := run_program hr P []
  unfold runMachine initMachine
  show (runMarks (clean P []) (programCost P)).regs = _
  rw [h]
  rfl

/-- Once the program is finished, further marks change nothing. -/
theorem machine_stable (hr : 0 < r) (P : List (Instr r)) (k : Nat) :
    runMachine P (programCost P + k) = clean [] (evalProgram P) := by
  unfold runMachine
  rw [runMarks_add]
  show runMarks (runMarks (clean P []) (programCost P)) k = _
  rw [run_program hr P []]
  induction k with
  | zero => rfl
  | succ k ih =>
      show markStep (runMarks (clean [] (evalProgramAux [] P)) k) = _
      rw [ih]
      rfl

end Interp
end Compiler
end L4

