import Leader.L4.Compiler.GeneratedView
import Leader.L4.Compiler.GeneratedBuild

/-! Literal input wiring of the two edit copies. High-level outputs
are the same phase update at two different constant delta registers. -/
namespace L4.Compiler.Native
open Interp

structure EditInput (r : Nat) (regs : List Value) (base phase : Nat)
    (L C R : Snapshot) (δ : Bool) : Prop where
  length : regs.length=base
  left : readSnapshot regs 235 236 237 238 239 240 241 242 L
  center : readSnapshot regs 62 63 43 64 50 51 52 53 C
  right : readSnapshot regs 245 246 247 248 249 250 251 252 R
  phases : readPhases regs phase
  zero : readReg regs 0=.word 0
  one : readReg regs 1=.word 1
  bound : readReg regs 3=.word (heightMod r-1)
  falseBit : readReg regs 5=.boolean false
  delta : readReg regs (if δ then 6 else 5)=.boolean δ

theorem stageEdit_snapshot {r : Nat} (hr : 3≤r)
    (T : PrimTable r) (bank : Bank) (hT : PrimSem T bank)
    (regs : List Value) (phase : Nat) (L C R : Snapshot) (δ : Bool)
    (h : EditInput r regs (editBase δ) phase L C R δ)
    (bL : snapshotBound r L) (bC : snapshotBound r C) (bR : snapshotBound r R)
    (hd : C.d<heightMod r) (hrd : R.d<heightMod r) :
    readSnapshot (runCodes T bank regs (buildEdit δ))
      (editBase δ+33) (editBase δ+34) (editBase δ+35) (editBase δ+36)
      (editBase δ+37) (editBase δ+38) (editBase δ+39) (editBase δ+40)
      (phaseUpdate (heightMod r) phase L C R δ) := by
  obtain ⟨lx,ld,lz,lp,lh,lhm,lr,la⟩ := h.left
  obtain ⟨cx,cd,cz,cp,ch,chm,cr,ca⟩ := h.center
  obtain ⟨rx,rd,rz,rp,rh,rhm,rr,ra⟩ := h.right
  obtain ⟨blx,bld,blz,blp⟩ := bL
  obtain ⟨bcx,bcd,bcz,bcp⟩ := bC
  obtain ⟨brx,brd,brz,brp⟩ := bR
  have S := stageEdit_spec hr T bank hT regs (editBase δ) h.length
    246 1 3 249 63 43 0 50 (if δ then 6 else 5) 51 5 245 235 52 62 241 238 64 53 252
    227 228 229 230 231 232
    (by cases δ <;> decide) (by cases δ <;> decide) (by cases δ <;> decide) (by cases δ <;> decide) (by cases δ <;> decide) (by cases δ <;> decide) (by cases δ <;> decide)
    (by cases δ <;> decide) (by cases δ <;> decide) (by cases δ <;> decide) (by cases δ <;> decide) (by cases δ <;> decide) (by cases δ <;> decide) (by cases δ <;> decide)
    (by cases δ <;> decide) (by cases δ <;> decide) (by cases δ <;> decide) (by cases δ <;> decide) (by cases δ <;> decide) (by cases δ <;> decide)
    (by cases δ <;> decide) (by cases δ <;> decide) (by cases δ <;> decide) (by cases δ <;> decide) (by cases δ <;> decide) (by cases δ <;> decide)
    R.d C.d C.z R.x L.x C.x L.proposal C.proposal
    R.anchor C.anchor δ C.home C.role L.role C.approve R.approve
    (decide (phase=0)) (decide (phase=1)) (decide (phase=2)) (decide (phase=3))
    (decide (phase=4)) (decide (phase=5))
    rd h.one h.bound rh cd cz h.zero ch h.delta chm h.falseBit rx lx cr cx lr lp cp ca ra
    (h.phases 0) (h.phases 1) (h.phases 2) (h.phases 3) (h.phases 4) (h.phases 5)
    brd bcd bcz brx blx bcx blp bcp
  rw [← stagedEdit_native r phase hr L C R δ hd hrd bcz]
  simpa only [readSnapshot,buildEdit,stagedEdit,decide_eq_true_eq] using S.2.2.2.2.2

theorem right_view_distance (r : Nat) (bank : Bank) (t : Nat) :
    (neighborView t (decodeBank r bank 2)).d<heightMod r := by
  unfold neighborView
  split
  · exact (native_record_bounds r bank 2).2.2.2.1
  · exact (native_record_bounds r bank 2).2.1.2.1

/-- All four phase-edited words are still legitimate full-width words.
Only distance/height/proposal have the stronger height bound. -/
theorem phaseUpdate_bounds (r phase : Nat) (hr : 3≤r) (L C R : Snapshot) (δ : Bool)
    (hC : snapshotBound r C)
    (hd : C.d<heightMod r) :
    snapshotBound r (phaseUpdate (heightMod r) phase L C R δ) := by
  obtain ⟨hx,hcd,hz,hp⟩ := hC
  have hM := edit_modulus_factor r hr
  have hB := edit_positive r
  have pM : 8*C.d+8<modulus r := by omega
  rcases phase with _|_|_|_|_|_|phase
  · exact ⟨hx,hcd,hz,hp⟩
  · refine ⟨hx,?_,?_,hp⟩
    · change (if R.anchor then 1 else min (heightMod r-1) (R.d+1))<modulus r
      split <;> omega
    · change (if !C.anchor then 0 else if C.z=0 then 8*C.d+8
          else min (8*C.d+8) (C.z-1))<modulus r
      split
      · omega
      · split <;> omega
  · exact ⟨hx,hcd,hz,hp⟩
  · refine ⟨hx,hcd,hz,?_⟩
    have hb := Nat.mod_lt (if C.role then if R.anchor then heightMod r - 1
      else R.x + heightMod r - 1 else if C.anchor then 0 else L.x + 1) hB
    exact Nat.lt_of_lt_of_le hb (by omega)
  · exact ⟨hx,hcd,hz,hp⟩
  · refine ⟨?_,hcd,hz,hp⟩
    change (if C.approve && R.approve then C.proposal else C.x)<modulus r
    split <;> assumption
  · exact ⟨hx,hcd,hz,hp⟩

#print axioms stageEdit_snapshot
#print axioms phaseUpdate_bounds
end L4.Compiler.Native
