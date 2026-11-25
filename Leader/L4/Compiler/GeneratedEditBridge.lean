import Leader.L4.Compiler.StagesEdit
import Leader.L4.Compiler.NativeSpec

/-! The mathematical bridge from the modular ALU edit to the independent
native row. Bounds are on decoded inputs, not arbitrary register values. -/
namespace L4.Compiler.Native
open Interp

theorem edit_modulus_factor (r : Nat) (hr : 3≤r) :
    modulus r=heightMod r*256 := by
  unfold modulus heightMod
  conv => lhs; rw [show r=r-2+2 by omega, Nat.pow_add]

theorem edit_positive (r : Nat) : 0<heightMod r := by
  exact Nat.pow_pos (by decide)

theorem edit_mod_height (r a : Nat) (hr : 3≤r) :
    a % modulus r % heightMod r = a % heightMod r := by
  apply Nat.mod_mod_of_dvd
  exact ⟨256,edit_modulus_factor r hr⟩

theorem dd_native (r rd : Nat) (hr : 3≤r) (hd : rd<heightMod r) (H : Bool) :
    ddVal r rd H=(if H then 1 else min (heightMod r-1) (rd+1)) := by
  have hm := edit_modulus_factor r hr
  have hp := edit_positive r
  have h : rd+1<modulus r := by omega
  change (if H then 1 else if heightMod r-1<(rd+1)%modulus r
      then heightMod r-1 else (rd+1)%modulus r)=_
  rw [Nat.mod_eq_of_lt h]
  cases H
  · simp only [Bool.false_eq_true,if_false,Nat.min_def]; split <;> split <;> omega
  · rfl

theorem period_native (r d : Nat) (hr : 3≤r) (hd : d<heightMod r) :
    periodVal r d=8*d+8 := by
  have hm := edit_modulus_factor r hr
  have hp := edit_positive r
  have h : 8*d+8<modulus r := by omega
  have h' : 8*d<modulus r := by omega
  change (8*d % modulus r+8)%modulus r=_
  rw [Nat.mod_eq_of_lt h',Nat.mod_eq_of_lt h]

theorem dec_mod (z m : Nat) (hz : 0<z) (hz' : z<m) :
    (z+m-1)%m=z-1 := by
  rw [show z+m-1=(z-1)+m by omega,Nat.add_mod_right]
  exact Nat.mod_eq_of_lt (by omega)

theorem dz_native (r d z : Nat) (hr : 3≤r) (hd : d<heightMod r) (hz : z<modulus r)
    (H : Bool) :
    dzVal r d z H=(if !H then 0 else if z=0 then 8*d+8 else min (8*d+8) (z-1)) := by
  change (if H then if z=0 then periodVal r d else
    if periodVal r d<(z+modulus r-1)%modulus r then periodVal r d
    else (z+modulus r-1)%modulus r else 0)=_
  rw [period_native r d hr hd]
  cases H
  · rfl
  · simp only [if_true,Bool.not_true,Bool.false_eq_true,if_false]
    split
    · rfl
    · rw [dec_mod z (modulus r) (by omega) hz]
      simp only [Nat.min_def]; split <;> split <;> omega

theorem subtract_height (r x : Nat) (hr : 3≤r) :
    (x+modulus r-1)%modulus r%heightMod r=(x+heightMod r-1)%heightMod r := by
  rw [edit_mod_height r _ hr]
  have hp := edit_positive r
  rw [edit_modulus_factor r hr,show x+heightMod r*256-1=
    (x+heightMod r-1)+heightMod r*255 by omega]
  simp

theorem props_native (r rx lx : Nat) (hr : 3≤r) (role rh h : Bool) :
    propsVal r rx lx role rh h =
      (if role then (if rh then heightMod r-1 else rx+heightMod r-1)
       else (if h then 0 else lx+1)) % heightMod r := by
  cases role <;> cases rh <;> cases h <;>
    simp only [propsVal,heightMod,Bool.false_eq_true,if_true,if_false]
  all_goals first
    | rfl
    | exact edit_mod_height r _ hr
    | exact subtract_height r rx hr

/-- Collect just the eight phase-edit postconditions of S11, before
the outer priority mux chooses hold, clear, propagate, reset, or inc. -/
def stagedEdit (r phase : Nat) (L C R : Snapshot) (δ : Bool) : Snapshot :=
  { x := if phase=5 then (if C.approve && R.approve then C.proposal else C.x) else C.x
    d := if phase=1 then ddVal r R.d R.anchor else C.d
    z := if phase=1 then dzVal r C.d C.z C.anchor else C.z
    proposal := if phase=3 then propsVal r R.x L.x C.role R.anchor C.anchor else C.proposal
    anchor := if phase=0 then !decide (L.x<C.x) else C.anchor
    home := if phase=1 then homeVal C.z C.anchor δ C.home else C.home
    role := if phase=2 then (if C.anchor then C.home else L.role) else C.role
    approve := if phase=4 then (C.anchor || decide (L.proposal<C.proposal)) else C.approve }

theorem stagedEdit_native (r phase : Nat) (hr : 3≤r)
    (L C R : Snapshot) (δ : Bool)
    (hd : C.d<heightMod r) (hrd : R.d<heightMod r) (hz : C.z<modulus r) :
    stagedEdit r phase L C R δ = phaseUpdate (heightMod r) phase L C R δ := by
  have hp : (!decide (L.x<C.x))=decide (C.x≤L.x) := by
    by_cases h : L.x<C.x
    · simp [h,show ¬C.x≤L.x by omega]
    · simp [h,show C.x≤L.x by omega]
  have ho : homeVal C.z C.anchor δ C.home =
      (C.anchor && (if C.z=0 then δ else C.home)) := by
    cases C.anchor <;> simp
  unfold stagedEdit
  rw [dd_native r _ hr hrd,dz_native r _ _ hr hd hz,props_native r _ _ hr,hp,ho]
  rcases phase with _|_|_|_|_|_|phase
  all_goals simp [phaseUpdate]

theorem native_record_bounds (r : Nat) (bank : Bank) (side : Fin 3) :
    let d := decodeBank r bank side
    d.tick < modulus r ∧
      (d.prior.x<heightMod r ∧ d.prior.d<heightMod r ∧ d.prior.z<modulus r ∧
        d.prior.proposal<heightMod r) ∧
      (d.curr.x<heightMod r ∧ d.curr.d<heightMod r ∧ d.curr.z<modulus r ∧
        d.curr.proposal<heightMod r) := by
  have hp : 0<modulus r := Nat.pow_pos (by decide)
  unfold decodeBank
  dsimp only
  constructor
  · split
    · exact hp
    · exact Nat.mod_lt _ hp
  all_goals repeat first | apply And.intro | exact Nat.mod_lt _ hp | exact Nat.mod_lt _ (edit_positive r)

#print axioms stagedEdit_native
#print axioms native_record_bounds
end L4.Compiler.Native
