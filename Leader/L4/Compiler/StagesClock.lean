import Leader.L4.Compiler.StagesLoad

/-!
# Stages S3-S7 of `generated_native`: clock guards and priority

Stage lists follow the reference emitter's `build()` code by code; they were
checked against the literal dump (`Literal.lean`, nodes 98-225, with base 98,
T = 58, E = 45, Ts = 94, s = 97, T_L = 29, err_L = 16, T_R = 87, err_R = 74).
-/

namespace L4
namespace Compiler
namespace Native

open Interp

theorem ite_mod' (c : Prop) [Decidable c] (a b m : Nat) :
    (if c then a else b) % m = if c then a % m else b % m := by
  by_cases h : c <;> simp [h]

theorem half_pred_mod {r : Nat} (hr : 3 ≤ r) :
    (16 ^ r / 2 + 16 ^ r - 1) % 16 ^ r = 16 ^ r / 2 - 1 := by
  have hM := pow16_pos' r
  have h16 : 16 ≤ 16 ^ r := by
    have : 16 ^ 1 ≤ 16 ^ r := Nat.pow_le_pow_right (by decide) (by omega)
    simpa using this
  have hP1 : 1 ≤ 16 ^ r / 2 := by omega
  have hPlt : 16 ^ r / 2 - 1 < 16 ^ r := by omega
  have : 16 ^ r / 2 + 16 ^ r - 1 = (16 ^ r / 2 - 1) + 16 ^ r := by omega
  rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt hPlt]

/-! ## S3: rootE, rootC, reset -/

def stageRoot (base t e ts z p mx uL eL uR eR : Nat) : List Code :=
  [ .cmp uL t, .cmpLt (base + 0), .and eL (base + 1), .not (base + 2)
  , .cmp uR t, .cmpLt (base + 4), .and eR (base + 5), .not (base + 6)
  , .and (base + 3) (base + 7)
  , .cmp t uL, .cmpLt (base + 9), .cmp ts uL, .cmpLt (base + 11), .and (base + 10) (base + 12)
  , .cmp t p, .cmpEq (base + 14), .cmp uL mx, .cmpEq (base + 16), .and (base + 15) (base + 17)
  , .not (base + 18), .and (base + 13) (base + 19)
  , .cmp t uR, .cmpLt (base + 21), .cmp ts uR, .cmpLt (base + 23), .and (base + 22) (base + 24)
  , .cmp t p, .cmpEq (base + 26), .cmp uR mx, .cmpEq (base + 28), .and (base + 27) (base + 29)
  , .not (base + 30), .and (base + 25) (base + 31)
  , .or (base + 20) (base + 32)
  , .bmux e (base + 8) (base + 33)
  , .cmp t z, .cmpEq (base + 35), .and e (base + 36), .not (base + 37), .and (base + 34) (base + 38) ]

abbrev rootEVal (tv uLv uRv : Nat) (bL bR : Bool) : Bool :=
  !(bL && decide (uLv < tv)) && !(bR && decide (uRv < tv))

abbrev rootCSide (r tv tsv uv : Nat) : Bool :=
  (decide (tv < uv) && decide (tsv < uv)) && !(decide (tv = 16 ^ r / 2) && decide (uv = 16 ^ r - 1))

abbrev resetVal (r tv tsv uLv uRv : Nat) (be bL bR : Bool) : Bool :=
  (if be then rootEVal tv uLv uRv bL bR else (rootCSide r tv tsv uLv || rootCSide r tv tsv uRv))
    && !(be && decide (tv = 0))

theorem stageRoot_spec {r : Nat} (hr : 3 ≤ r)
    (T : PrimTable r) (bank : Bank) (hT : PrimSem T bank)
    (regs : List Value) (base : Nat) (hlen : regs.length = base)
    (t e ts z p mx uL eL uR eR : Nat)
    (ht : t < base) (he : e < base) (hts : ts < base) (hz : z < base) (hp : p < base)
    (hmx : mx < base) (huL : uL < base) (heL : eL < base) (huR : uR < base) (heR : eR < base)
    (tv tsv uLv uRv : Nat) (be bL bR : Bool)
    (vt : readReg regs t = .word tv) (ve : readReg regs e = .boolean be)
    (vts : readReg regs ts = .word tsv) (vz : readReg regs z = .word 0)
    (vp : readReg regs p = .word (16 ^ r / 2)) (vmx : readReg regs mx = .word (16 ^ r - 1))
    (vuL : readReg regs uL = .word uLv) (veL : readReg regs eL = .boolean bL)
    (vuR : readReg regs uR = .word uRv) (veR : readReg regs eR = .boolean bR)
    (btv : tv < 16 ^ r) (btsv : tsv < 16 ^ r) (buL : uLv < 16 ^ r) (buR : uRv < 16 ^ r) :
    let out := runCodes T bank regs (stageRoot base t e ts z p mx uL eL uR eR)
    readReg out (base + 8) = .boolean (rootEVal tv uLv uRv bL bR) ∧
    readReg out (base + 33) = .boolean (rootCSide r tv tsv uLv || rootCSide r tv tsv uRv) ∧
    readReg out (base + 39) = .boolean (resetVal r tv tsv uLv uRv be bL bR) := by
  subst hlen
  have hM := pow16_pos' r
  have hP : 16 ^ r / 2 < 16 ^ r := Nat.div_lt_self hM (by decide)
  have hMax : 16 ^ r - 1 < 16 ^ r := by omega
  simp only [stageRoot, runCodes_cons, runCodes_nil, toInstr, evalInstr_word,
    evalInstr_source, evalBoolOp, readArgs_nil, readArgs_cons, List.append_assoc,
    List.cons_append, List.nil_append, readReg_append_len,
    readReg_append_left _ _ _ ht, readReg_append_left _ _ _ he, readReg_append_left _ _ _ hts,
    readReg_append_left _ _ _ hz, readReg_append_left _ _ _ hp, readReg_append_left _ _ _ hmx,
    readReg_append_left _ _ _ huL, readReg_append_left _ _ _ heL,
    readReg_append_left _ _ _ huR, readReg_append_left _ _ _ heR,
    vt, ve, vts, vz, vp, vmx, vuL, veL, vuR, veR, hT.cmp]
  refine ⟨?_, ?_, ?_⟩ <;>
    simp [readReg, argW, Value.asWord, Value.asBool, cmpCode_eq_one, cmpCode_eq_two,
      Nat.mod_eq_of_lt btv, Nat.mod_eq_of_lt btsv, Nat.mod_eq_of_lt buL, Nat.mod_eq_of_lt buR,
      Nat.mod_eq_of_lt hP, Nat.mod_eq_of_lt hMax, rootEVal, rootCSide, resetVal]

/-! ## S4: propagation candidates, minimum, pro -/

def stageProp (base t one p uL eL uR eR : Nat) : List Code :=
  [ .add uL one, .sub p one, .cmp uL (base + 1), .cmpLt (base + 2), .and eL (base + 3)
  , .cmp (base + 0) t, .cmpLt (base + 5), .and (base + 4) (base + 6), .mux (base + 7) (base + 0) t
  , .add uR one, .sub p one, .cmp uR (base + 10), .cmpLt (base + 11), .and eR (base + 12)
  , .cmp (base + 9) t, .cmpLt (base + 14), .and (base + 13) (base + 15), .mux (base + 16) (base + 9) t
  , .cmp (base + 8) (base + 17), .cmpLt (base + 18), .mux (base + 19) (base + 8) (base + 17)
  , .cmp (base + 20) t, .cmpLt (base + 21) ]

abbrev propVal (r tv uv : Nat) (b : Bool) : Nat :=
  if (b && decide (uv < 16 ^ r / 2 - 1)) && decide ((uv + 1) % 16 ^ r < tv)
  then (uv + 1) % 16 ^ r else tv

abbrev minVal (a b : Nat) : Nat := if a < b then a else b

theorem stageProp_spec {r : Nat} (hr : 3 ≤ r)
    (T : PrimTable r) (bank : Bank) (hT : PrimSem T bank)
    (regs : List Value) (base : Nat) (hlen : regs.length = base)
    (t one p uL eL uR eR : Nat)
    (ht : t < base) (hone : one < base) (hp : p < base)
    (huL : uL < base) (heL : eL < base) (huR : uR < base) (heR : eR < base)
    (tv uLv uRv : Nat) (bL bR : Bool)
    (vt : readReg regs t = .word tv) (vone : readReg regs one = .word 1)
    (vp : readReg regs p = .word (16 ^ r / 2))
    (vuL : readReg regs uL = .word uLv) (veL : readReg regs eL = .boolean bL)
    (vuR : readReg regs uR = .word uRv) (veR : readReg regs eR = .boolean bR)
    (btv : tv < 16 ^ r) (buL : uLv < 16 ^ r) (buR : uRv < 16 ^ r) :
    let out := runCodes T bank regs (stageProp base t one p uL eL uR eR)
    readReg out (base + 8) = .word (propVal r tv uLv bL) ∧
    readReg out (base + 17) = .word (propVal r tv uRv bR) ∧
    readReg out (base + 20) = .word (minVal (propVal r tv uLv bL) (propVal r tv uRv bR)) ∧
    readReg out (base + 22) =
      .boolean (decide (minVal (propVal r tv uLv bL) (propVal r tv uRv bR) < tv)) := by
  subst hlen
  have hM := pow16_pos' r
  have h1 : 1 < 16 ^ r := by
    have : 16 ^ 1 ≤ 16 ^ r := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  have hP : 16 ^ r / 2 < 16 ^ r := Nat.div_lt_self hM (by decide)
  have hsub := half_pred_mod hr
  have hPm1 : 16 ^ r / 2 - 1 < 16 ^ r := by omega
  simp only [stageProp, runCodes_cons, runCodes_nil, toInstr, evalInstr_word,
    evalInstr_source, evalBoolOp, readArgs_nil, readArgs_cons, List.append_assoc,
    List.cons_append, List.nil_append, readReg_append_len,
    readReg_append_left _ _ _ ht, readReg_append_left _ _ _ hone, readReg_append_left _ _ _ hp,
    readReg_append_left _ _ _ huL, readReg_append_left _ _ _ heL,
    readReg_append_left _ _ _ huR, readReg_append_left _ _ _ heR,
    vt, vone, vp, vuL, veL, vuR, veR, hT.cmp, hT.add, hT.sub, hT.mux]
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [readReg, argW, argB, Value.asWord, Value.asBool, cmpCode_eq_one, cmpCode_eq_two,
      Nat.mod_eq_of_lt btv, Nat.mod_eq_of_lt buL, Nat.mod_eq_of_lt buR,
      Nat.mod_eq_of_lt hP, Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt hPm1, hsub, ite_mod',
      Nat.mod_mod, propVal, minVal]

/-! ## S5: clear -/

def clearSide (o t ts one u eu : Nat) : List Code :=
  [ .add u one, .cmp u t, .cmpEq (o + 1), .cmp u t, .cmpLt (o + 3)
  , .cmp (o + 0) t, .cmpEq (o + 5), .and (o + 4) (o + 6), .or (o + 2) (o + 7)
  , .cmp t u, .cmpLt (o + 9), .cmp ts u, .cmpEq (o + 11), .and (o + 10) (o + 12)
  , .or (o + 8) (o + 13)
  , .cmp t u, .cmpLt (o + 15), .not (o + 16), .not eu, .or (o + 17) (o + 18)
  , .and (o + 14) (o + 19) ]

def stageClear (base t e ts one uL eL uR eR : Nat) : List Code :=
  clearSide base t ts one uL eL ++ clearSide (base + 21) t ts one uR eR ++
  [.and (base + 20) (base + 41), .and e (base + 42)]

abbrev clearSideVal (r tv tsv uv : Nat) (b : Bool) : Bool :=
  ((decide (uv = tv) || (decide (uv < tv) && decide ((uv + 1) % 16 ^ r = tv)))
      || (decide (tv < uv) && decide (tsv = uv)))
    && (!decide (tv < uv) || !b)

theorem stageClear_spec {r : Nat} (hr : 3 ≤ r)
    (T : PrimTable r) (bank : Bank) (hT : PrimSem T bank)
    (regs : List Value) (base : Nat) (hlen : regs.length = base)
    (t e ts one uL eL uR eR : Nat)
    (ht : t < base) (he : e < base) (hts : ts < base) (hone : one < base)
    (huL : uL < base) (heL : eL < base) (huR : uR < base) (heR : eR < base)
    (tv tsv uLv uRv : Nat) (be bL bR : Bool)
    (vt : readReg regs t = .word tv) (ve : readReg regs e = .boolean be)
    (vts : readReg regs ts = .word tsv) (vone : readReg regs one = .word 1)
    (vuL : readReg regs uL = .word uLv) (veL : readReg regs eL = .boolean bL)
    (vuR : readReg regs uR = .word uRv) (veR : readReg regs eR = .boolean bR)
    (btv : tv < 16 ^ r) (btsv : tsv < 16 ^ r) (buL : uLv < 16 ^ r) (buR : uRv < 16 ^ r) :
    let out := runCodes T bank regs (stageClear base t e ts one uL eL uR eR)
    readReg out (base + 43) =
      .boolean (be && (clearSideVal r tv tsv uLv bL && clearSideVal r tv tsv uRv bR)) := by
  subst hlen
  have hM := pow16_pos' r
  have h1 : 1 < 16 ^ r := by
    have : 16 ^ 1 ≤ 16 ^ r := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  simp only [stageClear, clearSide, List.cons_append, List.nil_append, Nat.add_assoc, runCodes_cons,
    runCodes_nil, toInstr, evalInstr_word, evalInstr_source, evalBoolOp, readArgs_nil,
    readArgs_cons, List.append_assoc, readReg_append_len,
    readReg_append_left _ _ _ ht, readReg_append_left _ _ _ he, readReg_append_left _ _ _ hts,
    readReg_append_left _ _ _ hone,
    readReg_append_left _ _ _ huL, readReg_append_left _ _ _ heL,
    readReg_append_left _ _ _ huR, readReg_append_left _ _ _ heR,
    vt, ve, vts, vone, vuL, veL, vuR, veR, hT.cmp, hT.add]
  simp [readReg, argW, Value.asWord, Value.asBool, cmpCode_eq_one, cmpCode_eq_two,
    Nat.mod_eq_of_lt btv, Nat.mod_eq_of_lt btsv, Nat.mod_eq_of_lt buL, Nat.mod_eq_of_lt buR,
    Nat.mod_eq_of_lt h1, Nat.mod_mod]

/-! ## S6: increment -/

def stageInc (base e t sv uL uR : Nat) : List Code :=
  [ .not e, .cmp uL t, .cmpEq (base + 1), .cmp uL sv, .cmpEq (base + 3), .or (base + 2) (base + 4)
  , .cmp uR t, .cmpEq (base + 6), .cmp uR sv, .cmpEq (base + 8), .or (base + 7) (base + 9)
  , .and (base + 5) (base + 10), .and (base + 0) (base + 11) ]

theorem stageInc_spec {r : Nat}
    (T : PrimTable r) (bank : Bank) (hT : PrimSem T bank)
    (regs : List Value) (base : Nat) (hlen : regs.length = base)
    (e t sv uL uR : Nat)
    (he : e < base) (ht : t < base) (hsv : sv < base) (huL : uL < base) (huR : uR < base)
    (be : Bool) (tv svv uLv uRv : Nat)
    (ve : readReg regs e = .boolean be) (vt : readReg regs t = .word tv)
    (vsv : readReg regs sv = .word svv)
    (vuL : readReg regs uL = .word uLv) (vuR : readReg regs uR = .word uRv)
    (btv : tv < 16 ^ r) (bsv : svv < 16 ^ r) (buL : uLv < 16 ^ r) (buR : uRv < 16 ^ r) :
    let out := runCodes T bank regs (stageInc base e t sv uL uR)
    readReg out (base + 12) =
      .boolean (!be && ((decide (uLv = tv) || decide (uLv = svv)) &&
        (decide (uRv = tv) || decide (uRv = svv)))) := by
  subst hlen
  simp only [stageInc, runCodes_cons, runCodes_nil, toInstr, evalInstr_word,
    evalInstr_source, evalBoolOp, readArgs_nil, readArgs_cons, List.append_assoc,
    List.cons_append, List.nil_append, readReg_append_len,
    readReg_append_left _ _ _ he, readReg_append_left _ _ _ ht, readReg_append_left _ _ _ hsv,
    readReg_append_left _ _ _ huL, readReg_append_left _ _ _ huR,
    ve, vt, vsv, vuL, vuR, hT.cmp]
  simp [readReg, argW, Value.asWord, Value.asBool, cmpCode_eq_one,
    Nat.mod_eq_of_lt btv, Nat.mod_eq_of_lt bsv, Nat.mod_eq_of_lt buL, Nat.mod_eq_of_lt buR]

/-! ## S7: priority (`_wins`) for err' and T' -/

def stagePrio (base rs pr cl ic e z f y pv t sv : Nat) : List Code :=
  [ .bmux ic f e, .bmux cl f (base + 0), .bmux pr y (base + 1), .bmux rs y (base + 2)
  , .mux ic sv t, .mux cl t (base + 4), .mux pr pv (base + 5), .mux rs z (base + 6) ]

theorem stagePrio_spec {r : Nat}
    (T : PrimTable r) (bank : Bank) (hT : PrimSem T bank)
    (regs : List Value) (base : Nat) (hlen : regs.length = base)
    (rs pr cl ic e z f y pv t sv : Nat)
    (hrs : rs < base) (hpr : pr < base) (hcl : cl < base) (hic : ic < base) (he : e < base)
    (hz : z < base) (hf : f < base) (hy : y < base) (hpv : pv < base) (ht : t < base)
    (hsv : sv < base)
    (brs bpr bcl bic be : Bool) (pvv tv svv : Nat)
    (vrs : readReg regs rs = .boolean brs) (vpr : readReg regs pr = .boolean bpr)
    (vcl : readReg regs cl = .boolean bcl) (vic : readReg regs ic = .boolean bic)
    (ve : readReg regs e = .boolean be) (vz : readReg regs z = .word 0)
    (vf : readReg regs f = .boolean false) (vy : readReg regs y = .boolean true)
    (vpv : readReg regs pv = .word pvv) (vt : readReg regs t = .word tv)
    (vsv : readReg regs sv = .word svv)
    (bpv : pvv < 16 ^ r) (btv : tv < 16 ^ r) (bsv : svv < 16 ^ r) :
    let out := runCodes T bank regs (stagePrio base rs pr cl ic e z f y pv t sv)
    readReg out (base + 3) =
      .boolean (if brs then true else if bpr then true else if bcl then false
        else if bic then false else be) ∧
    readReg out (base + 7) =
      .word (if brs then 0 else if bpr then pvv else if bcl then tv
        else if bic then svv else tv) := by
  subst hlen
  simp only [stagePrio, runCodes_cons, runCodes_nil, toInstr, evalInstr_word,
    evalInstr_source, evalBoolOp, readArgs_nil, readArgs_cons, List.append_assoc,
    List.cons_append, List.nil_append, readReg_append_len,
    readReg_append_left _ _ _ hrs, readReg_append_left _ _ _ hpr, readReg_append_left _ _ _ hcl,
    readReg_append_left _ _ _ hic, readReg_append_left _ _ _ he, readReg_append_left _ _ _ hz,
    readReg_append_left _ _ _ hf, readReg_append_left _ _ _ hy, readReg_append_left _ _ _ hpv,
    readReg_append_left _ _ _ ht, readReg_append_left _ _ _ hsv,
    vrs, vpr, vcl, vic, ve, vz, vf, vy, vpv, vt, vsv, hT.mux]
  refine ⟨?_, ?_⟩
  · cases brs <;> cases bpr <;> cases bcl <;> cases bic <;> simp [readReg, Value.asBool]
  · cases brs <;> cases bpr <;> cases bcl <;> cases bic <;>
      simp [readReg, argW, argB, Value.asWord, Value.asBool, ite_mod', Nat.mod_mod,
        Nat.mod_eq_of_lt bpv, Nat.mod_eq_of_lt btv, Nat.mod_eq_of_lt bsv]

end Native
end Compiler
end L4

#print axioms L4.Compiler.Native.stageRoot_spec
#print axioms L4.Compiler.Native.stageProp_spec
#print axioms L4.Compiler.Native.stageClear_spec
#print axioms L4.Compiler.Native.stageInc_spec
#print axioms L4.Compiler.Native.stagePrio_spec
