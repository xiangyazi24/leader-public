import Leader.L4.Compiler.StagesOut
import Leader.L4.Compiler.NativeSpec

namespace L4.Compiler.Native
open Interp

def outputBase (delta : Bool) : Nat := if delta then 410 else 305

def wordSources (delta : Bool) (i : Fin 8) : Nat × Nat :=
  let j := if delta then 402 else 297
  [(62,59),(63,60),(43,39),(64,61),(j,62),(j+1,63),(j+2,43),(j+3,64)].getD i.val (0,0)

def bitSources (delta : Bool) (i : Fin 8) : Nat × Nat :=
  let j := if delta then 406 else 301
  [(50,46),(51,47),(52,48),(53,49),(j,50),(j+1,51),(j+2,52),(j+3,53)].getD i.val (5,5)

def wordBase (delta : Bool) (i : Fin 8) := outputBase delta+4*i.val
def bitBase (delta : Bool) (i : Fin 8) := outputBase delta+32+4*i.val

def wordWindow (delta : Bool) (i : Fin 8) : List Code :=
  let p := wordSources delta i
  stageWinW (wordBase delta i) 137 160 204 217 0 p.1 p.2

def bitWindow (delta : Bool) (i : Fin 8) : List Code :=
  let p := bitSources delta i
  stageWinB (bitBase delta i) 137 160 204 217 5 p.1 p.2

def prefixRegs {r : Nat} (T : PrimTable r) (bank : Bank) (delta : Bool) :=
  runCodes T bank [] (literal.take (outputBase delta))

structure OutputFlags where
  reset : Bool
  protect : Bool
  clear : Bool
  install : Bool

def wins {α : Type} (g : OutputFlags) (z v c : α) : α :=
  if g.reset then z else if g.protect then z else if g.clear then z else if g.install then v else c

def outputSpec (g : OutputFlags) (editWords oldWords : Fin 8 → Nat)
    (editBits oldBits : Fin 8 → Bool) (tick : Nat) (err : Bool) : Output :=
  ⟨Fin.cases tick (fun i => wins g 0 (editWords i) (oldWords i)),
   Fin.cases err (fun i => wins g false (editBits i) (oldBits i))⟩

structure OutputInputs {r : Nat} (T : PrimTable r) (bank : Bank) (delta : Bool)
    (g : OutputFlags) (editWords oldWords : Fin 8 → Nat)
    (editBits oldBits : Fin 8 → Bool) (tick : Nat) (err : Bool) : Prop where
  reset : readReg (prefixRegs T bank delta) 137 = .boolean g.reset
  protect : readReg (prefixRegs T bank delta) 160 = .boolean g.protect
  clear : readReg (prefixRegs T bank delta) 204 = .boolean g.clear
  install : readReg (prefixRegs T bank delta) 217 = .boolean g.install
  zero : readReg (prefixRegs T bank delta) 0 = .word 0
  falseBit : readReg (prefixRegs T bank delta) 5 = .boolean false
  tickRead : readReg (prefixRegs T bank delta) 225 = .word tick
  errRead : readReg (prefixRegs T bank delta) 221 = .boolean err
  editWord : ∀ i, readReg (prefixRegs T bank delta) (wordSources delta i).1 = .word (editWords i)
  oldWord : ∀ i, readReg (prefixRegs T bank delta) (wordSources delta i).2 = .word (oldWords i)
  editBit : ∀ i, readReg (prefixRegs T bank delta) (bitSources delta i).1 = .boolean (editBits i)
  oldBit : ∀ i, readReg (prefixRegs T bank delta) (bitSources delta i).2 = .boolean (oldBits i)
  editBound : ∀ i, editWords i<16^r
  oldBound : ∀ i, oldWords i<16^r

private theorem splitWindow (base : Nat) (prog : List Code)
    (h : (literal.drop base).take 4=prog) :
    literal=(literal.take base++prog)++literal.drop (base+4) := by
  have H := (List.take_append_drop 4 (literal.drop base)).symm
  rw [h,List.drop_drop] at H
  calc
    literal=literal.take base++literal.drop base := (List.take_append_drop _ _).symm
    _=_ := by rw [H,List.append_assoc]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1200000 in
theorem wordLiteral (delta : Bool) (i : Fin 8) :
    literal=(literal.take (wordBase delta i) ++ wordWindow delta i) ++
      literal.drop (wordBase delta i+4) := by
  apply splitWindow
  revert i
  cases delta <;> decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1200000 in
theorem bitLiteral (delta : Bool) (i : Fin 8) :
    literal=(literal.take (bitBase delta i) ++ bitWindow delta i) ++
      literal.drop (bitBase delta i+4) := by
  apply splitWindow
  revert i
  cases delta <;> decide +kernel

private theorem keepPrefix {r : Nat} (T : PrimTable r) (bank : Bank)
    (a b k : Nat) (hab : a≤b) (ha : a≤literal.length) (hk : k<a) :
    readReg (runCodes T bank [] (literal.take b)) k =
      readReg (runCodes T bank [] (literal.take a)) k := by
  have E : literal.take b = literal.take a ++ (literal.take b).drop a := by
    have H : (literal.take b).take a=literal.take a := by rw [List.take_take,Nat.min_eq_left hab]
    rw [←H,List.take_append_drop]
  rw [E,runCodes_append]
  apply runCodes_prefix
  simpa [runCodes_length,List.length_take,Nat.min_eq_left ha] using hk

/-- Transport a completed earlier stage read to the fixed half's
output-window entry without replaying any read or stage. -/
theorem prefixRegs_read_of_take {r : Nat} (T : PrimTable r) (bank : Bank)
    (delta : Bool) (cut k : Nat) (ha : cut≤outputBase delta) (hk : k<cut) :
    readReg (prefixRegs T bank delta) k =
      readReg (runCodes T bank [] (literal.take cut)) k := by
  have H : outputBase delta≤literal.length := by
    rw [literal_length]
    cases delta <;> decide
  exact keepPrefix T bank cut _ k ha (Nat.le_trans ha H) hk

private theorem windowRead {r : Nat} (T : PrimTable r) (bank : Bank)
    (base : Nat) (prog : List Code) (hb : base≤literal.length) (hl : prog.length=4)
    (split : literal=(literal.take base++prog)++literal.drop (base+4)) :
    readReg (runCodes T bank [] literal) (base+3) =
      readReg (runCodes T bank (runCodes T bank [] (literal.take base)) prog) (base+3) := by
  conv => lhs; rw [split]
  rw [runCodes_append,runCodes_append]
  apply runCodes_prefix
  simp only [runCodes_length,List.length_nil,List.length_take,Nat.zero_add,Nat.min_eq_left hb,hl]
  omega

set_option maxRecDepth 4096 in
private theorem wordData (delta : Bool) (i : Fin 8) :
    outputBase delta≤wordBase delta i ∧ wordBase delta i≤literal.length ∧
      (wordSources delta i).1<outputBase delta ∧ (wordSources delta i).2<outputBase delta ∧
      (outIx delta).1 i.succ=wordBase delta i+3 := by
  revert i
  cases delta <;> decide +kernel

set_option maxRecDepth 4096 in
private theorem bitData (delta : Bool) (i : Fin 8) :
    outputBase delta≤bitBase delta i ∧ bitBase delta i≤literal.length ∧
      (bitSources delta i).1<outputBase delta ∧ (bitSources delta i).2<outputBase delta ∧
      (outIx delta).2 i.succ=bitBase delta i+3 := by
  revert i
  cases delta <;> decide +kernel

set_option maxRecDepth 4096 in
private theorem outBaseBounds (delta : Bool) :
    225<outputBase delta ∧ outputBase delta≤literal.length ∧
      (outIx delta).1 0=225 ∧ (outIx delta).2 0=221 := by
  cases delta <;> decide +kernel

theorem generated_word_field {r : Nat} (T : PrimTable r) (bank : Bank)
    (hT : PrimSem T bank) (delta : Bool) (g : OutputFlags)
    (ew ow : Fin 8 → Nat) (eb ob : Fin 8 → Bool) (tick : Nat) (err : Bool)
    (H : OutputInputs T bank delta g ew ow eb ob tick err) (i : Fin 8) :
    readReg (runCodes T bank [] literal) ((outIx delta).1 i.succ) =
      .word (wins g 0 (ew i) (ow i)) := by
  obtain ⟨h1,h2,h3,h4,hi⟩ := wordData delta i
  have ⟨h0,h5,_,_⟩ := outBaseBounds delta
  let b := wordBase delta i
  let regs := runCodes T bank [] (literal.take b)
  have L : regs.length=b := by simp [regs,runCodes_length,List.length_take,Nat.min_eq_left (show b≤literal.length from h2)]
  have K k (hk : k<outputBase delta) : readReg regs k=readReg (prefixRegs T bank delta) k :=
    keepPrefix T bank _ _ k h1 h5 hk
  rw [hi,windowRead T bank b (wordWindow delta i) h2 rfl (wordLiteral delta i)]
  exact stageWinW_spec T bank hT regs b L 137 160 204 217 0
    (wordSources delta i).1 (wordSources delta i).2
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    g.reset g.protect g.clear g.install (ew i) (ow i)
    ((K 137 (by omega)).trans H.reset) ((K 160 (by omega)).trans H.protect)
    ((K 204 (by omega)).trans H.clear) ((K 217 (by omega)).trans H.install)
    ((K 0 (by omega)).trans H.zero) ((K _ h3).trans (H.editWord i))
    ((K _ h4).trans (H.oldWord i)) (H.editBound i) (H.oldBound i)

theorem generated_bit_field {r : Nat} (T : PrimTable r) (bank : Bank)
    (delta : Bool) (g : OutputFlags)
    (ew ow : Fin 8 → Nat) (eb ob : Fin 8 → Bool) (tick : Nat) (err : Bool)
    (H : OutputInputs T bank delta g ew ow eb ob tick err) (i : Fin 8) :
    readReg (runCodes T bank [] literal) ((outIx delta).2 i.succ) =
      .boolean (wins g false (eb i) (ob i)) := by
  obtain ⟨h1,h2,h3,h4,hi⟩ := bitData delta i
  have ⟨h0,h5,_,_⟩ := outBaseBounds delta
  let b := bitBase delta i
  let regs := runCodes T bank [] (literal.take b)
  have L : regs.length=b := by simp [regs,runCodes_length,List.length_take,Nat.min_eq_left (show b≤literal.length from h2)]
  have K k (hk : k<outputBase delta) : readReg regs k=readReg (prefixRegs T bank delta) k :=
    keepPrefix T bank _ _ k h1 h5 hk
  rw [hi,windowRead T bank b (bitWindow delta i) h2 rfl (bitLiteral delta i)]
  exact stageWinB_spec T bank regs b L 137 160 204 217 5
    (bitSources delta i).1 (bitSources delta i).2
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    g.reset g.protect g.clear g.install (eb i) (ob i)
    ((K 137 (by omega)).trans H.reset) ((K 160 (by omega)).trans H.protect)
    ((K 204 (by omega)).trans H.clear) ((K 217 (by omega)).trans H.install)
    ((K 5 (by omega)).trans H.falseBit) ((K _ h3).trans (H.editBit i))
    ((K _ h4).trans (H.oldBit i))

private theorem output_ext (a b : Output) (hW : a.digits=b.digits) (hB : a.hdr=b.hdr) : a=b := by
  cases a; cases b
  simp_all

private theorem readOut_congr_fields (regs : List Value) (delta : Bool) (g : OutputFlags)
    (ew ow : Fin 8 → Nat) (eb ob : Fin 8 → Bool) (tick : Nat) (err : Bool)
    (hT : readReg regs ((outIx delta).1 0)=.word tick)
    (hE : readReg regs ((outIx delta).2 0)=.boolean err)
    (hW : ∀ i : Fin 8, readReg regs ((outIx delta).1 i.succ)=.word (wins g 0 (ew i) (ow i)))
    (hB : ∀ i : Fin 8, readReg regs ((outIx delta).2 i.succ)=.boolean (wins g false (eb i) (ob i))) :
    readOut regs delta=outputSpec g ew ow eb ob tick err := by
  apply output_ext
  · funext i
    refine Fin.cases ?_ (fun k => ?_) i
    · simpa only [readOut,outputSpec,Fin.cases_zero,asWord_word] using congrArg Value.asWord hT
    · simpa only [readOut,outputSpec,Fin.cases_succ,asWord_word] using congrArg Value.asWord (hW k)
  · funext i
    refine Fin.cases ?_ (fun k => ?_) i
    · simpa only [readOut,outputSpec,Fin.cases_zero,asBool_boolean] using congrArg Value.asBool hE
    · simpa only [readOut,outputSpec,Fin.cases_succ,asBool_boolean] using congrArg Value.asBool (hB k)

theorem generated_readOut {r : Nat} (T : PrimTable r) (bank : Bank)
    (hT : PrimSem T bank) (delta : Bool) (g : OutputFlags)
    (ew ow : Fin 8 → Nat) (eb ob : Fin 8 → Bool) (tick : Nat) (err : Bool)
    (H : OutputInputs T bank delta g ew ow eb ob tick err) :
    readOut (runCodes T bank [] literal) delta=outputSpec g ew ow eb ob tick err := by
  have ⟨h0,h5,hi,hj⟩ := outBaseBounds delta
  have keep k (hk : k<outputBase delta) :
      readReg (runCodes T bank [] literal) k=readReg (prefixRegs T bank delta) k := by
    have K := keepPrefix T bank (outputBase delta) literal.length k h5 h5 hk
    simpa [prefixRegs] using K
  apply readOut_congr_fields
  · exact (congrArg (readReg (runCodes T bank [] literal)) hi).trans
      ((keep 225 h0).trans H.tickRead)
  · exact (congrArg (readReg (runCodes T bank [] literal)) hj).trans
      ((keep 221 (by omega)).trans H.errRead)
  · exact generated_word_field T bank hT delta g ew ow eb ob tick err H
  · exact generated_bit_field T bank delta g ew ow eb ob tick err H

end L4.Compiler.Native
