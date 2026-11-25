import Leader.L4.Compiler.StagesClock

/-!
# Stage S11a-b of `generated_native`: the phase edits for one `delta`

The list follows the reference emitter's `build()`; for delta = F it equals
the literal dump nodes 264-304 (`Literal.lean`) with base 264. The
statements and proofs follow the recipe of `StagesLoad`.
-/

namespace L4
namespace Compiler
namespace Native

open Interp

def stageEdit (base rd one br rh vd vz z vh delta vhome f rx lx vrole vx lrole lp vp vapp rapp
    ph0 ph1 ph2 ph3 ph4 ph5 : Nat) : List Code :=
  [ .add rd one                                  -- 0
  , .cmp br (base + 0), .cmpLt (base + 1)        -- 1, 2
  , .mux (base + 2) br (base + 0)                -- 3
  , .mux rh one (base + 3)                       -- 4 dd
  , .shl3 vd, .const .eight                      -- 5, 6
  , .add (base + 5) (base + 6)                   -- 7 period
  , .cmp vz z, .cmpEq (base + 8)                 -- 8, 9 d0
  , .sub vz one                                  -- 10
  , .cmp (base + 7) (base + 10), .cmpLt (base + 11)  -- 11, 12
  , .mux (base + 12) (base + 7) (base + 10)      -- 13
  , .mux (base + 9) (base + 7) (base + 13)       -- 14
  , .mux vh (base + 14) z                        -- 15 dz
  , .bmux (base + 9) delta vhome                 -- 16
  , .bmux vh (base + 16) f                       -- 17 home
  , .sub rx one                                  -- 18
  , .mux rh br (base + 18)                       -- 19
  , .add lx one                                  -- 20
  , .mux vh z (base + 20)                        -- 21
  , .mux vrole (base + 19) (base + 21)           -- 22
  , .maskB (base + 22)                           -- 23 props
  , .cmp lx vx, .cmpLt (base + 24)               -- 24, 25
  , .not (base + 25)                             -- 26 change H
  , .bmux vh vhome lrole                         -- 27 change role
  , .cmp lp vp, .cmpLt (base + 28)               -- 28, 29
  , .or vh (base + 29)                           -- 30 change approve
  , .and vapp rapp                               -- 31
  , .mux (base + 31) vp vx                       -- 32 change x
  , .mux ph5 (base + 32) vx                      -- 33 new x
  , .mux ph1 (base + 4) vd                       -- 34 new d
  , .mux ph1 (base + 15) vz                      -- 35 new z
  , .mux ph3 (base + 23) vp                      -- 36 new p
  , .bmux ph0 (base + 26) vh                     -- 37 new H
  , .bmux ph1 (base + 17) vhome                  -- 38 new home
  , .bmux ph2 (base + 27) vrole                  -- 39 new role
  , .bmux ph4 (base + 30) vapp ]                 -- 40 new approve

abbrev ddVal (r rdv : Nat) (brh : Bool) : Nat :=
  if brh then 1 else
    if 16 ^ (r - 2) - 1 < (rdv + 1) % 16 ^ r then 16 ^ (r - 2) - 1 else (rdv + 1) % 16 ^ r

abbrev periodVal (r vdv : Nat) : Nat := (8 * vdv % 16 ^ r + 8) % 16 ^ r

abbrev dzVal (r vdv vzv : Nat) (bvh : Bool) : Nat :=
  if bvh then
    (if vzv = 0 then periodVal r vdv else
      if periodVal r vdv < (vzv + 16 ^ r - 1) % 16 ^ r then periodVal r vdv
      else (vzv + 16 ^ r - 1) % 16 ^ r)
  else 0

abbrev homeVal (vzv : Nat) (bvh bdelta bhome : Bool) : Bool :=
  if bvh then (if vzv = 0 then bdelta else bhome) else false

abbrev propsVal (r rxv lxv : Nat) (brole brh bvh : Bool) : Nat :=
  (if brole then (if brh then 16 ^ (r - 2) - 1 else (rxv + 16 ^ r - 1) % 16 ^ r)
   else (if bvh then 0 else (lxv + 1) % 16 ^ r)) % 16 ^ (r - 2)

theorem stageEdit_spec {r : Nat} (hr : 3 ≤ r)
    (T : PrimTable r) (bank : Bank) (hT : PrimSem T bank)
    (regs : List Value) (base : Nat) (hlen : regs.length = base)
    (rd one br rh vd vz z vh delta vhome f rx lx vrole vx lrole lp vp vapp rapp
      ph0 ph1 ph2 ph3 ph4 ph5 : Nat)
    (hrd : rd < base) (hone : one < base) (hbr : br < base) (hrh : rh < base)
    (hvd : vd < base) (hvz : vz < base) (hz : z < base) (hvh : vh < base)
    (hdelta : delta < base) (hvhome : vhome < base) (hf : f < base) (hrx : rx < base)
    (hlx : lx < base) (hvrole : vrole < base) (hvx : vx < base) (hlrole : lrole < base)
    (hlp : lp < base) (hvp : vp < base) (hvapp : vapp < base) (hrapp : rapp < base)
    (hph0 : ph0 < base) (hph1 : ph1 < base) (hph2 : ph2 < base) (hph3 : ph3 < base)
    (hph4 : ph4 < base) (hph5 : ph5 < base)
    (rdv vdv vzv rxv lxv vxv lpv vpv : Nat)
    (brh bvh bdelta bhome brole blrole bvapp brapp b0 b1 b2 b3 b4 b5 : Bool)
    (vrd : readReg regs rd = .word rdv) (vone : readReg regs one = .word 1)
    (vbr : readReg regs br = .word (16 ^ (r - 2) - 1)) (vrh : readReg regs rh = .boolean brh)
    (vvd : readReg regs vd = .word vdv) (vvz : readReg regs vz = .word vzv)
    (vz0 : readReg regs z = .word 0) (vvh : readReg regs vh = .boolean bvh)
    (vdelta : readReg regs delta = .boolean bdelta)
    (vvhome : readReg regs vhome = .boolean bhome) (vf : readReg regs f = .boolean false)
    (vrx : readReg regs rx = .word rxv) (vlx : readReg regs lx = .word lxv)
    (vvrole : readReg regs vrole = .boolean brole) (vvx : readReg regs vx = .word vxv)
    (vlrole : readReg regs lrole = .boolean blrole) (vlp : readReg regs lp = .word lpv)
    (vvp : readReg regs vp = .word vpv) (vvapp : readReg regs vapp = .boolean bvapp)
    (vrapp : readReg regs rapp = .boolean brapp)
    (vph0 : readReg regs ph0 = .boolean b0) (vph1 : readReg regs ph1 = .boolean b1)
    (vph2 : readReg regs ph2 = .boolean b2) (vph3 : readReg regs ph3 = .boolean b3)
    (vph4 : readReg regs ph4 = .boolean b4) (vph5 : readReg regs ph5 = .boolean b5)
    (brd : rdv < 16 ^ r) (bvd : vdv < 16 ^ r) (bvz : vzv < 16 ^ r) (brx : rxv < 16 ^ r)
    (blx : lxv < 16 ^ r) (bvx : vxv < 16 ^ r) (blp : lpv < 16 ^ r) (bvp : vpv < 16 ^ r) :
    let out := runCodes T bank regs (stageEdit base rd one br rh vd vz z vh delta vhome f
      rx lx vrole vx lrole lp vp vapp rapp ph0 ph1 ph2 ph3 ph4 ph5)
    readReg out (base + 4) = .word (ddVal r rdv brh) ∧
    readReg out (base + 7) = .word (periodVal r vdv) ∧
    readReg out (base + 15) = .word (dzVal r vdv vzv bvh) ∧
    readReg out (base + 17) = .boolean (homeVal vzv bvh bdelta bhome) ∧
    readReg out (base + 23) = .word (propsVal r rxv lxv brole brh bvh) ∧
    readReg out (base + 33) =
      .word (if b5 then (if bvapp && brapp then vpv else vxv) else vxv) ∧
    readReg out (base + 34) = .word (if b1 then ddVal r rdv brh else vdv) ∧
    readReg out (base + 35) = .word (if b1 then dzVal r vdv vzv bvh else vzv) ∧
    readReg out (base + 36) = .word (if b3 then propsVal r rxv lxv brole brh bvh else vpv) ∧
    readReg out (base + 37) = .boolean (if b0 then !decide (lxv < vxv) else bvh) ∧
    readReg out (base + 38) = .boolean (if b1 then homeVal vzv bvh bdelta bhome else bhome) ∧
    readReg out (base + 39) = .boolean (if b2 then (if bvh then bhome else blrole) else brole) ∧
    readReg out (base + 40) = .boolean (if b4 then (bvh || decide (lpv < vpv)) else bvapp) := by
  subst hlen
  have hM := pow16_pos' r
  have h1 : 1 < 16 ^ r := by
    have : 16 ^ 1 ≤ 16 ^ r := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  have h8 : 8 < 16 ^ r := by
    have : 16 ^ 1 ≤ 16 ^ r := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  have hBr : 16 ^ (r - 2) - 1 < 16 ^ r := by
    have : 16 ^ (r - 2) ≤ 16 ^ r := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  have hBM : ∀ a, a % 16 ^ (r - 2) % 16 ^ r = a % 16 ^ (r - 2) := by
    intro a
    have hB := pow16_pos' (r - 2)
    have : 16 ^ (r - 2) ≤ 16 ^ r := Nat.pow_le_pow_right (by decide) (by omega)
    exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt _ hB) this)
  simp only [stageEdit, runCodes_cons, runCodes_nil, toInstr, evalInstr_word,
    evalInstr_source, evalBoolOp, readArgs_nil, readArgs_cons, List.append_assoc,
    List.cons_append, List.nil_append, readReg_append_len,
    readReg_append_left _ _ _ hrd, readReg_append_left _ _ _ hone, readReg_append_left _ _ _ hbr,
    readReg_append_left _ _ _ hrh, readReg_append_left _ _ _ hvd, readReg_append_left _ _ _ hvz,
    readReg_append_left _ _ _ hz, readReg_append_left _ _ _ hvh,
    readReg_append_left _ _ _ hdelta, readReg_append_left _ _ _ hvhome,
    readReg_append_left _ _ _ hf, readReg_append_left _ _ _ hrx, readReg_append_left _ _ _ hlx,
    readReg_append_left _ _ _ hvrole, readReg_append_left _ _ _ hvx,
    readReg_append_left _ _ _ hlrole, readReg_append_left _ _ _ hlp,
    readReg_append_left _ _ _ hvp, readReg_append_left _ _ _ hvapp,
    readReg_append_left _ _ _ hrapp,
    readReg_append_left _ _ _ hph0, readReg_append_left _ _ _ hph1,
    readReg_append_left _ _ _ hph2, readReg_append_left _ _ _ hph3,
    readReg_append_left _ _ _ hph4, readReg_append_left _ _ _ hph5,
    vrd, vone, vbr, vrh, vvd, vvz, vz0, vvh, vdelta, vvhome, vf, vrx, vlx, vvrole, vvx,
    vlrole, vlp, vvp, vvapp, vrapp, vph0, vph1, vph2, vph3, vph4, vph5,
    hT.add, hT.sub, hT.shl3, hT.const, hT.mux, hT.cmp, hT.maskB]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [readReg, argW, argB, Value.asWord, Value.asBool, cmpCode_eq_one, cmpCode_eq_two,
      ConstId.val, ite_mod', Nat.mod_mod,
      Nat.mod_eq_of_lt brd, Nat.mod_eq_of_lt bvd, Nat.mod_eq_of_lt bvz, Nat.mod_eq_of_lt brx,
      Nat.mod_eq_of_lt blx, Nat.mod_eq_of_lt bvx, Nat.mod_eq_of_lt blp, Nat.mod_eq_of_lt bvp,
      Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h8, Nat.mod_eq_of_lt hBr,
      ddVal, periodVal, dzVal, homeVal, propsVal, hBM]
  all_goals (cases b2 <;> cases bvh <;> rfl)

end Native
end Compiler
end L4

#print axioms L4.Compiler.Native.stageEdit_spec
