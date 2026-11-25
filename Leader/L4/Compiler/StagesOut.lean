import Leader.L4.Compiler.StagesClock

/-!
# Stage S11c of `generated_native`: per-field output priority

`get(f)` in the emitter's `build()` is `_wins(k, (zero, zero, zero, v, C[f]))`, i.e.
four multiplexers per field, guards inc, clear, pro, reset from the inside out.
In the literal dump the delta = F outputs are nodes 305-368 (sixteen fields in
FIELDS[1:] then BITS[1:] order), the delta = T outputs nodes 410-473. The clock
word and error bit of each output are the S7 registers.
-/

namespace L4
namespace Compiler
namespace Native

open Interp

/-- One word field: `M(inc, v, c)`, then clear, pro, reset select zero. -/
def stageWinW (base rs pr cl ic z v c : Nat) : List Code :=
  [.mux ic v c, .mux cl z (base + 0), .mux pr z (base + 1), .mux rs z (base + 2)]

/-- One Boolean field: the same with BMUX and the constant F. -/
def stageWinB (base rs pr cl ic f v c : Nat) : List Code :=
  [.bmux ic v c, .bmux cl f (base + 0), .bmux pr f (base + 1), .bmux rs f (base + 2)]

theorem stageWinW_spec {r : Nat}
    (T : PrimTable r) (bank : Bank) (hT : PrimSem T bank)
    (regs : List Value) (base : Nat) (hlen : regs.length = base)
    (rs pr cl ic z v c : Nat)
    (hrs : rs < base) (hpr : pr < base) (hcl : cl < base) (hic : ic < base)
    (hz : z < base) (hv : v < base) (hc : c < base)
    (brs bpr bcl bic : Bool) (vv cv : Nat)
    (vrs : readReg regs rs = .boolean brs) (vpr : readReg regs pr = .boolean bpr)
    (vcl : readReg regs cl = .boolean bcl) (vic : readReg regs ic = .boolean bic)
    (vz : readReg regs z = .word 0) (vvv : readReg regs v = .word vv)
    (vcv : readReg regs c = .word cv) (bv : vv < 16 ^ r) (bc : cv < 16 ^ r) :
    readReg (runCodes T bank regs (stageWinW base rs pr cl ic z v c)) (base + 3) =
      .word (if brs then 0 else if bpr then 0 else if bcl then 0 else if bic then vv else cv) := by
  subst hlen
  simp only [stageWinW, runCodes_cons, runCodes_nil, toInstr, evalInstr_word, readArgs_nil,
    readArgs_cons, List.append_assoc, List.cons_append, List.nil_append, readReg_append_len,
    readReg_append_left _ _ _ hrs, readReg_append_left _ _ _ hpr, readReg_append_left _ _ _ hcl,
    readReg_append_left _ _ _ hic, readReg_append_left _ _ _ hz, readReg_append_left _ _ _ hv,
    readReg_append_left _ _ _ hc, vrs, vpr, vcl, vic, vz, vvv, vcv, hT.mux]
  cases brs <;> cases bpr <;> cases bcl <;> cases bic <;>
    simp [readReg, argW, argB, Value.asWord, Value.asBool, ite_mod', Nat.mod_mod,
      Nat.mod_eq_of_lt bv, Nat.mod_eq_of_lt bc]

theorem stageWinB_spec {r : Nat}
    (T : PrimTable r) (bank : Bank)
    (regs : List Value) (base : Nat) (hlen : regs.length = base)
    (rs pr cl ic f v c : Nat)
    (hrs : rs < base) (hpr : pr < base) (hcl : cl < base) (hic : ic < base)
    (hf : f < base) (hv : v < base) (hc : c < base)
    (brs bpr bcl bic bv bc : Bool)
    (vrs : readReg regs rs = .boolean brs) (vpr : readReg regs pr = .boolean bpr)
    (vcl : readReg regs cl = .boolean bcl) (vic : readReg regs ic = .boolean bic)
    (vf : readReg regs f = .boolean false) (vvv : readReg regs v = .boolean bv)
    (vcv : readReg regs c = .boolean bc) :
    readReg (runCodes T bank regs (stageWinB base rs pr cl ic f v c)) (base + 3) =
      .boolean (if brs then false else if bpr then false else if bcl then false
        else if bic then bv else bc) := by
  subst hlen
  simp only [stageWinB, runCodes_cons, runCodes_nil, toInstr, evalInstr_source, evalBoolOp,
    List.append_assoc, List.cons_append, List.nil_append, readReg_append_len,
    readReg_append_left _ _ _ hrs, readReg_append_left _ _ _ hpr, readReg_append_left _ _ _ hcl,
    readReg_append_left _ _ _ hic, readReg_append_left _ _ _ hf, readReg_append_left _ _ _ hv,
    readReg_append_left _ _ _ hc, vrs, vpr, vcl, vic, vf, vvv, vcv]
  cases brs <;> cases bpr <;> cases bcl <;> cases bic <;> simp [readReg, Value.asBool]

end Native
end Compiler
end L4

