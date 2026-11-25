import Leader.L4.Compiler.StagesLoad
import Leader.L4.Compiler.NativeSpec
import Leader.L4.Compiler.PrimInstance

/-! Generated S0–S2 at their literal register indices. The result is
stated against independent native decoded records, not raw stage expressions. -/
namespace L4.Compiler.Native
open Interp

def sideBase (q : Fin 3) : Nat := 7+29*q.val

def recordWord (x : NativeRecord) : Fin 9 → Nat
  | ⟨0,_⟩ => x.tick
  | ⟨1,_⟩ => x.prior.x
  | ⟨2,_⟩ => x.prior.d
  | ⟨3,_⟩ => x.prior.z
  | ⟨4,_⟩ => x.prior.proposal
  | ⟨5,_⟩ => x.curr.x
  | ⟨6,_⟩ => x.curr.d
  | ⟨7,_⟩ => x.curr.z
  | ⟨8,_⟩ => x.curr.proposal

def recordBit (x : NativeRecord) : Fin 9 → Bool
  | ⟨0,_⟩ => x.err
  | ⟨1,_⟩ => x.prior.anchor
  | ⟨2,_⟩ => x.prior.home
  | ⟨3,_⟩ => x.prior.role
  | ⟨4,_⟩ => x.prior.approve
  | ⟨5,_⟩ => x.curr.anchor
  | ⟨6,_⟩ => x.curr.home
  | ⟨7,_⟩ => x.curr.role
  | ⟨8,_⟩ => x.curr.approve

structure LoadConstants (r : Nat) (regs : List Value) : Prop where
  zero : readReg regs 0 = .word 0
  one : readReg regs 1 = .word 1
  half : readReg regs 2 = .word (modulus r / 2)
  bound : readReg regs 3 = .word (heightMod r - 1)
  max : readReg regs 4 = .word (modulus r - 1)
  ff : readReg regs 5 = .boolean false
  tt : readReg regs 6 = .boolean true

structure LoadSide (r : Nat) (bank : Bank) (regs : List Value) (q : Fin 3) : Prop where
  word : ∀ i, readReg regs (sideOut (sideBase q) i) = .word (recordWord (decodeBank r bank q) i)
  bit : ∀ i : Fin 9, readReg regs (sideBase q+9+i.val) = .boolean (recordBit (decodeBank r bank q) i)

structure LoadFacts (r : Nat) (bank : Bank) (regs : List Value) : Prop extends LoadConstants r regs where
  length : regs.length=98
  word : ∀ q i, readReg regs (sideOut (sideBase q) i) = .word (recordWord (decodeBank r bank q) i)
  bit : ∀ q (i : Fin 9), readReg regs (sideBase q+9+i.val) = .boolean (recordBit (decodeBank r bank q) i)
  succRaw : readReg regs 94 = .word (((decodeBank r bank 1).tick+1) % modulus r)
  succ : readReg regs 97 = .word (successor (modulus r) (decodeBank r bank 1).tick)

def loadCodes : List Code :=
  stageConst ++ stageSide 7 0 0 2 ++ stageSide 36 1 0 2 ++ stageSide 65 2 0 2 ++ stageSucc 94 58 1 2 4

private theorem const_run {r : Nat} (hr : 3≤r) (T : PrimTable r) (bank : Bank) (hT : PrimSem T bank) :
    LoadConstants r (runCodes T bank [] stageConst) := by
  obtain ⟨a,b,c,d,e,f,g⟩ := stageConst_spec hr T bank hT [] 0 rfl
  exact ⟨a,b,c,d,e,f,g⟩

private theorem LoadConstants.push {r : Nat} (T : PrimTable r) (bank : Bank)
    (regs : List Value) (P : List Code) (hlen : 7≤regs.length) (h : LoadConstants r regs) :
    LoadConstants r (runCodes T bank regs P) := by
  constructor <;> rw [runCodes_prefix T bank regs P _ (by omega)]
  · exact h.zero
  · exact h.one
  · exact h.half
  · exact h.bound
  · exact h.max
  · exact h.ff
  · exact h.tt

private theorem sideOut_bound (base : Nat) (i : Fin 9) :
    sideOut base i<base+29 := by
  match i with
  | ⟨0,_⟩ | ⟨1,_⟩ | ⟨2,_⟩ | ⟨3,_⟩ | ⟨4,_⟩ | ⟨5,_⟩ | ⟨6,_⟩ | ⟨7,_⟩ | ⟨8,_⟩ =>
    simp only [sideOut] <;> omega

private theorem LoadSide.push {r : Nat} (T : PrimTable r) (bank : Bank)
    (regs : List Value) (P : List Code) (q : Fin 3)
    (hlen : sideBase q+29≤regs.length) (H : LoadSide r bank regs q) :
    LoadSide r bank (runCodes T bank regs P) q := by
  constructor
  · intro i
    rw [runCodes_prefix T bank regs P _ (Nat.lt_of_lt_of_le (sideOut_bound _ _) hlen)]
    exact H.word i
  · intro i
    have hi := i.isLt
    rw [runCodes_prefix T bank regs P _ (by omega)]
    exact H.bit i

private theorem side_run {r : Nat} (hr : 3≤r) (T : PrimTable r) (bank : Bank) (hT : PrimSem T bank)
    (regs : List Value) (C : LoadConstants r regs) (q : Fin 3)
    (L : regs.length=sideBase q) :
    LoadSide r bank (runCodes T bank regs (stageSide (sideBase q) q 0 2)) q := by
  have B : 7≤sideBase q := by simp [sideBase]
  obtain ⟨a,b,c,d,e,f,g,h,j,H⟩ := stageSide_spec hr T bank hT regs (sideBase q) L q 0 2
    (by omega) (by omega) C.zero C.half
  constructor
  · intro i
    match i with
    | ⟨0,_⟩ =>
      by_cases K : 16 ^ r / 2 ≤ raw r bank q 0 <;>
        cases E : bank.hdr q 0 <;>
        simpa [recordWord,decodeBank,modulus,raw,K,E] using a
    | ⟨1,_⟩ => exact b
    | ⟨2,_⟩ => exact c
    | ⟨3,_⟩ => exact d
    | ⟨4,_⟩ => exact e
    | ⟨5,_⟩ => exact f
    | ⟨6,_⟩ => exact g
    | ⟨7,_⟩ => exact h
    | ⟨8,_⟩ => exact j
  · intro i
    match i with
    | ⟨0,_⟩ | ⟨1,_⟩ | ⟨2,_⟩ | ⟨3,_⟩ | ⟨4,_⟩ | ⟨5,_⟩ | ⟨6,_⟩ | ⟨7,_⟩ | ⟨8,_⟩ =>
      exact H _

private theorem tick_lt (r : Nat) (bank : Bank) (q : Fin 3) :
    (decodeBank r bank q).tick < modulus r := by
  unfold decodeBank
  dsimp only
  split
  · exact pow16_pos' _
  · exact Nat.mod_lt _ (pow16_pos' _)

theorem load_spec {r : Nat} (hr : 3≤r) (T : PrimTable r) (bank : Bank) (hT : PrimSem T bank) :
    LoadFacts r bank (runCodes T bank [] loadCodes) := by
  let l0 := runCodes T bank [] stageConst
  let l1 := runCodes T bank l0 (stageSide 7 0 0 2)
  let l2 := runCodes T bank l1 (stageSide 36 1 0 2)
  let l3 := runCodes T bank l2 (stageSide 65 2 0 2)
  let l4 := runCodes T bank l3 (stageSucc 94 58 1 2 4)
  have n0 : l0.length=7 := by rw [runCodes_length]; rfl
  have n1 : l1.length=36 := by rw [runCodes_length,n0]; rfl
  have n2 : l2.length=65 := by rw [runCodes_length,n1]; rfl
  have n3 : l3.length=94 := by rw [runCodes_length,n2]; rfl
  have n4 : l4.length=98 := by rw [runCodes_length,n3]; rfl
  have C0 := const_run hr T bank hT
  have C1 := C0.push T bank l0 (stageSide 7 0 0 2) (by rw [n0]; decide)
  have C2 := C1.push T bank l1 (stageSide 36 1 0 2) (by rw [n1]; decide)
  have C3 := C2.push T bank l2 (stageSide 65 2 0 2) (by rw [n2]; decide)
  have C4 := C3.push T bank l3 (stageSucc 94 58 1 2 4) (by rw [n3]; decide)
  have A0 : LoadSide r bank l1 0 := side_run hr T bank hT l0 C0 0 n0
  have B0 : LoadSide r bank l2 1 := side_run hr T bank hT l1 C1 1 n1
  have C0' : LoadSide r bank l3 2 := side_run hr T bank hT l2 C2 2 n2
  have A1 : LoadSide r bank l2 0 := A0.push T bank l1 (stageSide 36 1 0 2) 0 (by rw [n1]; decide)
  have A2 : LoadSide r bank l3 0 := A1.push T bank l2 (stageSide 65 2 0 2) 0 (by rw [n2]; decide)
  have B1 : LoadSide r bank l3 1 := B0.push T bank l2 (stageSide 65 2 0 2) 1 (by rw [n2]; decide)
  have A3 : LoadSide r bank l4 0 := A2.push T bank l3 (stageSucc 94 58 1 2 4) 0 (by rw [n3]; decide)
  have B2 : LoadSide r bank l4 1 := B1.push T bank l3 (stageSucc 94 58 1 2 4) 1 (by rw [n3]; decide)
  have C1' : LoadSide r bank l4 2 := C0'.push T bank l3 (stageSucc 94 58 1 2 4) 2 (by rw [n3]; decide)
  have tk : readReg l3 58 = .word (decodeBank r bank 1).tick := B1.word 0
  have S := stageSucc_spec hr T bank hT l3 94 n3 58 1 2 4
    (by decide) (by decide) (by decide) (by decide) _ tk C3.one C3.half C3.max (tick_lt r bank 1)
  simp only [loadCodes,runCodes_append]
  change LoadFacts r bank l4
  have side (q : Fin 3) : LoadSide r bank l4 q := by
    match q with
    | ⟨0,_⟩ => exact A3
    | ⟨1,_⟩ => exact B2
    | ⟨2,_⟩ => exact C1'
  exact ⟨C4,n4,fun q => (side q).word,fun q => (side q).bit,S.1,S.2⟩

/-- Literal-index facts instantiated at the accepted digit primitives. -/
theorem generated_load (r : Nat) (hr : 3≤r) (bank : Bank) :
    LoadFacts r bank (runCodes (PrimInstance.table r hr bank) bank [] loadCodes) :=
  load_spec hr _ bank (PrimInstance.semantics r hr bank)

#print axioms generated_load
end L4.Compiler.Native
