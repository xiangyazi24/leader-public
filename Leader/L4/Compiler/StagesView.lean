import Leader.L4.Compiler.StagesClock

/-!
# Stages S8-S10 of `generated_native`: phase bits, neighbour views, need

Lists follow the emitter's `build()` and equal the literal dump nodes 226-232 (S8),
233-242 and 243-252 (S9 for L and R), 253-263 (S10, NEED = 263).
-/

namespace L4
namespace Compiler
namespace Native

open Interp

/-! ## S8: phase = SCAN5(T), ph_j = (phase = j) for j < 6 -/

theorem nat_beq_decide (a b : Nat) : (a == b) = decide (a = b) := by
  by_cases h : a = b <;> simp [h]

def stagePhase (base t : Nat) : List Code :=
  [.scan5 t, .phaseEq (base + 0) 0, .phaseEq (base + 0) 1, .phaseEq (base + 0) 2,
   .phaseEq (base + 0) 3, .phaseEq (base + 0) 4, .phaseEq (base + 0) 5]

theorem stagePhase_spec {r : Nat}
    (T : PrimTable r) (bank : Bank) (hT : PrimSem T bank)
    (regs : List Value) (base : Nat) (hlen : regs.length = base)
    (t : Nat) (ht : t < base) (tv : Nat) (vt : readReg regs t = .word tv) (btv : tv < 16 ^ r) :
    let out := runCodes T bank regs (stagePhase base t)
    readReg out (base + 0) = .word (tv % 32) ∧
    readReg out (base + 1) = .boolean (decide (tv % 32 = 0)) ∧
    readReg out (base + 2) = .boolean (decide (tv % 32 = 1)) ∧
    readReg out (base + 3) = .boolean (decide (tv % 32 = 2)) ∧
    readReg out (base + 4) = .boolean (decide (tv % 32 = 3)) ∧
    readReg out (base + 5) = .boolean (decide (tv % 32 = 4)) ∧
    readReg out (base + 6) = .boolean (decide (tv % 32 = 5)) := by
  subst hlen
  simp only [stagePhase, runCodes_cons, runCodes_nil, toInstr, evalInstr_word,
    evalInstr_source, evalBoolOp, readArgs_nil, readArgs_cons, List.append_assoc,
    List.cons_append, List.nil_append, readReg_append_len, readReg_append_left _ _ _ ht,
    vt, hT.scan5]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [readReg, argW, Value.asWord, Nat.mod_eq_of_lt btv, nat_beq_decide]

/-! ## S9: the view of one neighbour y -/

/-- `same = eq(T_y, T)`, then MUX for x d z p and BMUX for H home role approve. -/
def stageView (base ty t cx cd cz cp cH chome crole capp ox od oz op oH ohome orole oapp : Nat) :
    List Code :=
  [ .cmp ty t, .cmpEq (base + 0)
  , .mux (base + 1) cx ox, .mux (base + 1) cd od, .mux (base + 1) cz oz, .mux (base + 1) cp op
  , .bmux (base + 1) cH oH, .bmux (base + 1) chome ohome, .bmux (base + 1) crole orole
  , .bmux (base + 1) capp oapp ]

theorem stageView_spec {r : Nat}
    (T : PrimTable r) (bank : Bank) (hT : PrimSem T bank)
    (regs : List Value) (base : Nat) (hlen : regs.length = base)
    (ty t cx cd cz cp cH chome crole capp ox od oz op oH ohome orole oapp : Nat)
    (hty : ty < base) (ht : t < base)
    (hcx : cx < base) (hcd : cd < base) (hcz : cz < base) (hcp : cp < base)
    (hcH : cH < base) (hchome : chome < base) (hcrole : crole < base) (hcapp : capp < base)
    (hox : ox < base) (hod : od < base) (hoz : oz < base) (hop : op < base)
    (hoH : oH < base) (hohome : ohome < base) (horole : orole < base) (hoapp : oapp < base)
    (tyv tv cxv cdv czv cpv oxv odv ozv opv : Nat)
    (bcH bchome bcrole bcapp boH bohome borole boapp : Bool)
    (vty : readReg regs ty = .word tyv) (vt : readReg regs t = .word tv)
    (vcx : readReg regs cx = .word cxv) (vcd : readReg regs cd = .word cdv)
    (vcz : readReg regs cz = .word czv) (vcp : readReg regs cp = .word cpv)
    (vcH : readReg regs cH = .boolean bcH) (vchome : readReg regs chome = .boolean bchome)
    (vcrole : readReg regs crole = .boolean bcrole) (vcapp : readReg regs capp = .boolean bcapp)
    (vox : readReg regs ox = .word oxv) (vod : readReg regs od = .word odv)
    (voz : readReg regs oz = .word ozv) (vop : readReg regs op = .word opv)
    (voH : readReg regs oH = .boolean boH) (vohome : readReg regs ohome = .boolean bohome)
    (vorole : readReg regs orole = .boolean borole) (voapp : readReg regs oapp = .boolean boapp)
    (btyv : tyv < 16 ^ r) (btv : tv < 16 ^ r)
    (bcx : cxv < 16 ^ r) (bcd : cdv < 16 ^ r) (bcz : czv < 16 ^ r) (bcp : cpv < 16 ^ r)
    (box : oxv < 16 ^ r) (bod : odv < 16 ^ r) (boz : ozv < 16 ^ r) (bop : opv < 16 ^ r) :
    let out := runCodes T bank regs (stageView base ty t cx cd cz cp cH chome crole capp
      ox od oz op oH ohome orole oapp)
    readReg out (base + 2) = .word (if tyv = tv then cxv else oxv) ∧
    readReg out (base + 3) = .word (if tyv = tv then cdv else odv) ∧
    readReg out (base + 4) = .word (if tyv = tv then czv else ozv) ∧
    readReg out (base + 5) = .word (if tyv = tv then cpv else opv) ∧
    readReg out (base + 6) = .boolean (if tyv = tv then bcH else boH) ∧
    readReg out (base + 7) = .boolean (if tyv = tv then bchome else bohome) ∧
    readReg out (base + 8) = .boolean (if tyv = tv then bcrole else borole) ∧
    readReg out (base + 9) = .boolean (if tyv = tv then bcapp else boapp) := by
  subst hlen
  simp only [stageView, runCodes_cons, runCodes_nil, toInstr, evalInstr_word,
    evalInstr_source, evalBoolOp, readArgs_nil, readArgs_cons, List.append_assoc,
    List.cons_append, List.nil_append, readReg_append_len,
    readReg_append_left _ _ _ hty, readReg_append_left _ _ _ ht,
    readReg_append_left _ _ _ hcx, readReg_append_left _ _ _ hcd,
    readReg_append_left _ _ _ hcz, readReg_append_left _ _ _ hcp,
    readReg_append_left _ _ _ hcH, readReg_append_left _ _ _ hchome,
    readReg_append_left _ _ _ hcrole, readReg_append_left _ _ _ hcapp,
    readReg_append_left _ _ _ hox, readReg_append_left _ _ _ hod,
    readReg_append_left _ _ _ hoz, readReg_append_left _ _ _ hop,
    readReg_append_left _ _ _ hoH, readReg_append_left _ _ _ hohome,
    readReg_append_left _ _ _ horole, readReg_append_left _ _ _ hoapp,
    vty, vt, vcx, vcd, vcz, vcp, vcH, vchome, vcrole, vcapp,
    vox, vod, voz, vop, voH, vohome, vorole, voapp, hT.cmp, hT.mux]
  by_cases hs : tyv = tv
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp [readReg, argW, argB, Value.asWord, Value.asBool, cmpCode_eq_one, hs,
        Nat.mod_eq_of_lt btv, Nat.mod_eq_of_lt bcx, Nat.mod_eq_of_lt bcd,
        Nat.mod_eq_of_lt bcz, Nat.mod_eq_of_lt bcp]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp [readReg, argW, argB, Value.asWord, Value.asBool, cmpCode_eq_one, hs,
        Nat.mod_eq_of_lt btyv, Nat.mod_eq_of_lt btv, Nat.mod_eq_of_lt box,
        Nat.mod_eq_of_lt bod, Nat.mod_eq_of_lt boz, Nat.mod_eq_of_lt bop]

/-! ## S10: need -/

def stageNeed (base rs pr cl ic ph1 vh vz z : Nat) : List Code :=
  [ .not rs, .not pr, .and (base + 0) (base + 1), .not cl, .and (base + 2) (base + 3)
  , .and (base + 4) ic, .and (base + 5) ph1, .and (base + 6) vh
  , .cmp vz z, .cmpEq (base + 8), .and (base + 7) (base + 9) ]

theorem stageNeed_spec {r : Nat}
    (T : PrimTable r) (bank : Bank) (hT : PrimSem T bank)
    (regs : List Value) (base : Nat) (hlen : regs.length = base)
    (rs pr cl ic ph1 vh vz z : Nat)
    (hrs : rs < base) (hpr : pr < base) (hcl : cl < base) (hic : ic < base)
    (hph1 : ph1 < base) (hvh : vh < base) (hvz : vz < base) (hz : z < base)
    (brs bpr bcl bic b1 bvh : Bool) (vzv : Nat)
    (vrs : readReg regs rs = .boolean brs) (vpr : readReg regs pr = .boolean bpr)
    (vcl : readReg regs cl = .boolean bcl) (vic : readReg regs ic = .boolean bic)
    (vph1 : readReg regs ph1 = .boolean b1) (vvh : readReg regs vh = .boolean bvh)
    (vvz : readReg regs vz = .word vzv) (vz0 : readReg regs z = .word 0)
    (bvz : vzv < 16 ^ r) :
    readReg (runCodes T bank regs (stageNeed base rs pr cl ic ph1 vh vz z)) (base + 10) =
      .boolean (!brs && !bpr && !bcl && bic && b1 && bvh && decide (vzv = 0)) := by
  subst hlen
  simp only [stageNeed, runCodes_cons, runCodes_nil, toInstr, evalInstr_word,
    evalInstr_source, evalBoolOp, readArgs_nil, readArgs_cons, List.append_assoc,
    List.cons_append, List.nil_append, readReg_append_len,
    readReg_append_left _ _ _ hrs, readReg_append_left _ _ _ hpr,
    readReg_append_left _ _ _ hcl, readReg_append_left _ _ _ hic,
    readReg_append_left _ _ _ hph1, readReg_append_left _ _ _ hvh,
    readReg_append_left _ _ _ hvz, readReg_append_left _ _ _ hz,
    vrs, vpr, vcl, vic, vph1, vvh, vvz, vz0, hT.cmp]
  cases brs <;> cases bpr <;> cases bcl <;> cases bic <;> cases b1 <;> cases bvh <;>
    simp [readReg, argW, Value.asWord, Value.asBool, cmpCode_eq_one, Nat.mod_eq_of_lt bvz]

end Native
end Compiler
end L4

#print axioms L4.Compiler.Native.stagePhase_spec
#print axioms L4.Compiler.Native.stageView_spec
#print axioms L4.Compiler.Native.stageNeed_spec
