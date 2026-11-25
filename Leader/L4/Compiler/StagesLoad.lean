import Leader.L4.Compiler.Code

/-!
# Stages S0-S2 of `generated_native`: constants, one side's loads, successor

Stage lists follow the reference emitter's `build()` code by code. The proofs
use the evaluation simp set of `Code.lean`.
-/

namespace L4
namespace Compiler
namespace Native

open Interp

theorem pow16_pos' : ∀ k : Nat, 0 < 16 ^ k
  | 0 => by decide
  | k + 1 => by
      rw [Nat.pow_succ]
      have := pow16_pos' k
      omega

/-- S0: the seven initial constants Z, ONE, P, B-1, MAX, F, Y, in emitter order. -/
def stageConst : List Code :=
  [.const .zero, .const .one, .const .p, .const .bm1, .const .max,
   .bconst false, .bconst true]

theorem stageConst_spec {r : Nat} (hr : 3 ≤ r)
    (T : PrimTable r) (bank : Bank) (hT : PrimSem T bank)
    (regs : List Value) (base : Nat) (hlen : regs.length = base) :
    let out := runCodes T bank regs stageConst
    readReg out (base + 0) = .word 0 ∧
    readReg out (base + 1) = .word 1 ∧
    readReg out (base + 2) = .word (16 ^ r / 2) ∧
    readReg out (base + 3) = .word (16 ^ (r - 2) - 1) ∧
    readReg out (base + 4) = .word (16 ^ r - 1) ∧
    readReg out (base + 5) = .boolean false ∧
    readReg out (base + 6) = .boolean true := by
  subst hlen
  have hM := pow16_pos' r
  have h1 : 1 < 16 ^ r := by
    have : 16 ^ 1 ≤ 16 ^ r := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  have hP : 16 ^ r / 2 < 16 ^ r := Nat.div_lt_self hM (by decide)
  have hBm : 16 ^ (r - 2) - 1 < 16 ^ r := by
    have : 16 ^ (r - 2) ≤ 16 ^ r := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  have hMax : 16 ^ r - 1 < 16 ^ r := by omega
  simp only [stageConst, runCodes_cons, runCodes_nil, toInstr, evalInstr_word, evalInstr_source,
    evalBoolOp, readArgs_nil, List.append_assoc, List.cons_append,
    List.nil_append, readReg_append_len, hT.const, ConstId.val]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [readReg, Nat.mod_eq_of_lt hM, Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt hP,
      Nat.mod_eq_of_lt hBm, Nat.mod_eq_of_lt hMax]

/-- S1: one side's nine raw fields, nine header bits, the T normalization
`M("W", a(err, N(lt(T,P))), Z, T)`, and the six B-masks of old.x old.d old.p
curr.x curr.d curr.p. Offsets: loads 0-8, headers 9-17, normalization 18-22,
masks 23-28. -/
def stageSide (base : Nat) (q : Fin 3) (zIx pIx : Nat) : List Code :=
  [ .load q 0, .load q 1, .load q 2, .load q 3, .load q 4
  , .load q 5, .load q 6, .load q 7, .load q 8
  , .header q 0, .header q 1, .header q 2, .header q 3, .header q 4
  , .header q 5, .header q 6, .header q 7, .header q 8
  , .cmp (base + 0) pIx
  , .cmpLt (base + 18)
  , .not (base + 19)
  , .and (base + 9) (base + 20)
  , .mux (base + 21) zIx (base + 0)
  , .maskB (base + 1)
  , .maskB (base + 2)
  , .maskB (base + 4)
  , .maskB (base + 5)
  , .maskB (base + 6)
  , .maskB (base + 8) ]

/-- Output offset of each FIELDS entry after S1 (T normalized, x/d/p masked). -/
def sideOut (base : Nat) : Fin 9 → Nat
  | ⟨0, _⟩ => base + 22
  | ⟨1, _⟩ => base + 23
  | ⟨2, _⟩ => base + 24
  | ⟨3, _⟩ => base + 3
  | ⟨4, _⟩ => base + 25
  | ⟨5, _⟩ => base + 26
  | ⟨6, _⟩ => base + 27
  | ⟨7, _⟩ => base + 7
  | ⟨8, _⟩ => base + 28

abbrev raw (r : Nat) (bank : Bank) (q : Fin 3) (i : Fin 9) : Nat := bank.digits q i % 16 ^ r

theorem stageSide_spec {r : Nat} (hr : 3 ≤ r)
    (T : PrimTable r) (bank : Bank) (hT : PrimSem T bank)
    (regs : List Value) (base : Nat) (hlen : regs.length = base)
    (q : Fin 3) (zIx pIx : Nat) (hz : zIx < base) (hp : pIx < base)
    (hzv : readReg regs zIx = .word 0)
    (hpv : readReg regs pIx = .word (16 ^ r / 2)) :
    let out := runCodes T bank regs (stageSide base q zIx pIx)
    readReg out (sideOut base 0) =
        .word (if bank.hdr q 0 = true ∧ 16 ^ r / 2 ≤ raw r bank q 0 then 0
               else raw r bank q 0) ∧
    readReg out (sideOut base 1) = .word (raw r bank q 1 % 16 ^ (r - 2)) ∧
    readReg out (sideOut base 2) = .word (raw r bank q 2 % 16 ^ (r - 2)) ∧
    readReg out (sideOut base 3) = .word (raw r bank q 3) ∧
    readReg out (sideOut base 4) = .word (raw r bank q 4 % 16 ^ (r - 2)) ∧
    readReg out (sideOut base 5) = .word (raw r bank q 5 % 16 ^ (r - 2)) ∧
    readReg out (sideOut base 6) = .word (raw r bank q 6 % 16 ^ (r - 2)) ∧
    readReg out (sideOut base 7) = .word (raw r bank q 7) ∧
    readReg out (sideOut base 8) = .word (raw r bank q 8 % 16 ^ (r - 2)) ∧
    (∀ i : Fin 9, readReg out (base + 9 + i.val) = .boolean (bank.hdr q i)) := by
  subst hlen
  have hM := pow16_pos' r
  have hP : 16 ^ r / 2 < 16 ^ r := Nat.div_lt_self hM (by decide)
  simp only [stageSide, sideOut, raw, runCodes_cons, runCodes_nil, toInstr, evalInstr_word,
    evalInstr_source, evalBoolOp, readArgs_nil, readArgs_cons, List.append_assoc,
    List.cons_append, List.nil_append, readReg_append_len,
    readReg_append_left _ _ _ hz, readReg_append_left _ _ _ hp, hzv, hpv,
    hT.load, hT.cmp, hT.maskB, hT.mux]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [readReg, argW, argB, Value.asWord, Value.asBool, cmpCode_eq_two,
      Nat.mod_eq_of_lt hP]
  all_goals try simp [readReg, argW, Value.asWord]
  intro i
  match i with
  | ⟨0, _⟩ | ⟨1, _⟩ | ⟨2, _⟩ | ⟨3, _⟩ | ⟨4, _⟩ | ⟨5, _⟩ | ⟨6, _⟩ | ⟨7, _⟩ | ⟨8, _⟩ =>
    simp [Nat.add_assoc]

/-- S2: Ts = add(T, ONE); s = M("W", eq(T, MAX), P, Ts). -/
def stageSucc (base : Nat) (tIx oneIx pIx maxIx : Nat) : List Code :=
  [.add tIx oneIx, .cmp tIx maxIx, .cmpEq (base + 1), .mux (base + 2) pIx (base + 0)]

theorem stageSucc_spec {r : Nat} (hr : 3 ≤ r)
    (T : PrimTable r) (bank : Bank) (hT : PrimSem T bank)
    (regs : List Value) (base : Nat) (hlen : regs.length = base)
    (tIx oneIx pIx maxIx : Nat)
    (ht : tIx < base) (ho : oneIx < base) (hpp : pIx < base) (hmx : maxIx < base)
    (t : Nat) (htv : readReg regs tIx = .word t)
    (hov : readReg regs oneIx = .word 1)
    (hpv : readReg regs pIx = .word (16 ^ r / 2))
    (hmv : readReg regs maxIx = .word (16 ^ r - 1))
    (htlt : t < 16 ^ r) :
    let out := runCodes T bank regs (stageSucc base tIx oneIx pIx maxIx)
    readReg out (base + 0) = .word ((t + 1) % 16 ^ r) ∧
    readReg out (base + 3) = .word (if t = 16 ^ r - 1 then 16 ^ r / 2 else t + 1) := by
  subst hlen
  have hM := pow16_pos' r
  have h1 : 1 < 16 ^ r := by
    have : 16 ^ 1 ≤ 16 ^ r := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  have hP : 16 ^ r / 2 < 16 ^ r := Nat.div_lt_self hM (by decide)
  have hMax : 16 ^ r - 1 < 16 ^ r := by omega
  simp only [stageSucc, runCodes_cons, runCodes_nil, toInstr, evalInstr_word,
    evalInstr_source, evalBoolOp, readArgs_nil, readArgs_cons, List.append_assoc,
    List.cons_append, List.nil_append, readReg_append_len,
    readReg_append_left _ _ _ ht,
    readReg_append_left _ _ _ hpp, readReg_append_left _ _ _ hmx,
    htv, hov, hpv, hmv, hT.add, hT.cmp, hT.mux]
  refine ⟨?_, ?_⟩
  · simp [readReg, argW, Value.asWord, Nat.mod_eq_of_lt htlt, Nat.mod_eq_of_lt h1]
  · by_cases heq : t = 16 ^ r - 1
    · simp [readReg, argW, argB, Value.asWord, Value.asBool, cmpCode_eq_one, heq,
        Nat.mod_eq_of_lt hMax, Nat.mod_eq_of_lt hP]
    · have hlt : t + 1 < 16 ^ r := by omega
      simp [readReg, argW, argB, Value.asWord, Value.asBool, cmpCode_eq_one, heq,
        Nat.mod_eq_of_lt htlt, Nat.mod_eq_of_lt hMax, Nat.mod_eq_of_lt h1,
        Nat.mod_eq_of_lt hlt]

end Native
end Compiler
end L4

