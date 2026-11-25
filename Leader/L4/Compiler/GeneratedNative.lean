import Leader.L4.Compiler.GeneratedViewInput
import Leader.L4.Compiler.GeneratedEdit
import Leader.L4.Compiler.GeneratedOutput
import Leader.L4.Compiler.PrimInstance

/-! End-to-end stage composition for the exact emitter dump. This
module uses the accepted digit-serial primitive semantics and passes
typed register facts from one stage to the next. -/
namespace L4.Compiler.Native
open Interp

set_option linter.unusedSimpArgs false
set_option maxRecDepth 4096

def pairWords (prior curr : Snapshot) (i : Fin 8) : Nat :=
  [prior.x,prior.d,prior.z,prior.proposal,curr.x,curr.d,curr.z,curr.proposal].getD i.val 0

def pairBits (prior curr : Snapshot) (i : Fin 8) : Bool :=
  [prior.anchor,prior.home,prior.role,prior.approve,
    curr.anchor,curr.home,curr.role,curr.approve].getD i.val false

private theorem idx8 (i : Fin 8) :
    i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 ∨ i=7 := by
  decide +revert

private theorem pairWords_bound (r : Nat) (A B : Snapshot) (hA : snapshotBound r A)
    (hB : snapshotBound r B) (i : Fin 8) : pairWords A B i<modulus r := by
  obtain ⟨ax,ad,az,ap⟩ := hA
  obtain ⟨bx,bd,bz,bp⟩ := hB
  rcases idx8 i with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> assumption

def flagSet (r : Nat) (L C R : NativeRecord) : OutputFlags :=
  ⟨clockReset r L C R,clockProp r L C R,clockClear r L C R,clockInc r L C R⟩

private theorem encode_cases (rec : NativeRecord) :
    encodeOutput rec =
      ⟨Fin.cases rec.tick (pairWords rec.prior rec.curr),
       Fin.cases rec.err (pairBits rec.prior rec.curr)⟩ := by
  simp only [encodeOutput]
  congr 1
  · funext i
    refine Fin.cases rfl (fun j => ?_) i
    rcases idx8 j with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl
  · funext i
    refine Fin.cases rfl (fun j => ?_) i
    rcases idx8 j with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl

private theorem winner_output (g : OutputFlags) (C : NativeRecord)
    (E : Snapshot) (tick : Nat) (err : Bool) :
    outputSpec g (pairWords C.curr E) (pairWords C.prior C.curr)
      (pairBits C.curr E) (pairBits C.prior C.curr) tick err =
      encodeOutput ⟨tick,err,
        wins g {} C.curr C.prior,wins g {} E C.curr⟩ := by
  rw [encode_cases]
  have zW : pairWords {} {} = fun _ => 0 := by
    funext i
    rcases idx8 i with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl
  have zB : pairBits {} {} = fun _ => false := by
    funext i
    rcases idx8 i with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl
  obtain ⟨a,b,c,d⟩ := g
  cases a <;> cases b <;> cases c <;> cases d <;>
    simp only [outputSpec,wins,Bool.false_eq_true,if_false,if_true,zW,zB]

private theorem final_window_native (r : Nat) (L C R : NativeRecord) (δ : Bool)
    (hL : L.tick<modulus r) (hC : C.tick<modulus r) (hR : R.tick<modulus r) :
    let N := finishNative (heightMod r) L C R (nativeClock (modulus r) L C R) δ
    let E := phaseUpdate (heightMod r) (C.tick%32) (neighborView C.tick L) C.curr (neighborView C.tick R) δ
    outputSpec (flagSet r L C R) (pairWords C.curr E) (pairWords C.prior C.curr)
      (pairBits C.curr E) (pairBits C.prior C.curr) N.tick N.err = encodeOutput N := by
  dsimp only
  rw [winner_output,clock_spec r L C R hL hC hR]
  cases h1 : clockReset r L C R <;> cases h2 : clockProp r L C R <;>
    cases h3 : clockClear r L C R <;> cases h4 : clockInc r L C R <;>
    simp only [flagSet,wins,h1,h2,h3,h4,Bool.false_eq_true,if_false,if_true,finishNative]

private theorem need_native (r : Nat) (L C R : NativeRecord)
    (hL : L.tick<modulus r) (hC : C.tick<modulus r) (hR : R.tick<modulus r) :
    (!clockReset r L C R && !clockProp r L C R && !clockClear r L C R &&
      clockInc r L C R && decide (C.tick%32=1) && C.curr.anchor && decide (C.curr.z=0)) =
    pendingNeed (nativeClock (modulus r) L C R) C := by
  rw [clock_spec r L C R hL hC hR]
  cases h1 : clockReset r L C R <;> cases h2 : clockProp r L C R <;>
    cases h3 : clockClear r L C R <;> cases h4 : clockInc r L C R <;>
    simp [h1,h2,h3,h4,pendingNeed]

private theorem take_read {r : Nat} (T : PrimTable r) (bank : Bank)
    (a b k : Nat) (ab : a≤b) (bl : b≤literal.length) (hk : k<a) :
    readReg (runCodes T bank [] (literal.take b)) k =
      readReg (runCodes T bank [] (literal.take a)) k := by
  have P : literal.take b=literal.take a ++ (literal.take b).drop a := by
    conv => lhs; rw [←List.take_append_drop a (literal.take b)]
    rw [List.take_take,Nat.min_eq_left ab]
  rw [P,runCodes_append]
  apply runCodes_prefix
  rw [runCodes_length,List.length_take,Nat.min_eq_left (Nat.le_trans ab bl)]
  simpa using hk

private theorem load_take : loadCodes=literal.take 98 := by decide +kernel
private theorem view_take : loadClockCodes ++ viewCodes=literal.take 264 := by decide +kernel

private theorem edit_take (δ : Bool) :
    literal.take (outputBase δ) = literal.take (editBase δ) ++ buildEdit δ := by
  cases δ <;> decide +kernel

private theorem view_run {r : Nat} (hr : 3≤r) (T : PrimTable r) (bank : Bank) (hT : PrimSem T bank) :
    let L := decodeBank r bank 0
    let C := decodeBank r bank 1
    let R := decodeBank r bank 2
    ViewOutput r bank (runCodes T bank [] (literal.take 264))
      (clockReset r L C R) (clockProp r L C R) (clockClear r L C R) (clockInc r L C R) := by
  have E := view_input_after_clock hr T bank hT
  have V := view_spec T bank hT _ _ _ _ _ E
  rw [←runCodes_append,view_take] at V
  exact V

private theorem literal_len : literal.length=474 := literal_length

private theorem beforeEdit_lt (δ : Bool) : 264≤editBase δ ∧ editBase δ≤literal.length := by
  cases δ <;> decide +kernel

private theorem beforeOut_lt (δ : Bool) : editBase δ≤outputBase δ ∧ outputBase δ≤literal.length := by
  cases δ <;> decide +kernel

set_option maxHeartbeats 1800000 in
private theorem output_inputs_native {r : Nat} (hr : 3≤r) (T : PrimTable r) (bank : Bank)
    (hT : PrimSem T bank) (δ : Bool) :
    let L := decodeBank r bank 0
    let C := decodeBank r bank 1
    let R := decodeBank r bank 2
    let A := nativeClock (modulus r) L C R
    let N := finishNative (heightMod r) L C R A δ
    let E := phaseUpdate (heightMod r) (C.tick%32) (neighborView C.tick L) C.curr (neighborView C.tick R) δ
    OutputInputs T bank δ (flagSet r L C R)
      (pairWords C.curr E) (pairWords C.prior C.curr) (pairBits C.curr E) (pairBits C.prior C.curr)
      N.tick N.err := by
  let L := decodeBank r bank 0
  let C := decodeBank r bank 1
  let R := decodeBank r bank 2
  let LV := neighborView C.tick L
  let RV := neighborView C.tick R
  let P := runCodes T bank [] (literal.take (editBase δ))
  have S := load_spec hr T bank hT
  have K := clock_run hr T bank hT
  have V := view_run hr T bank hT
  have oldP (i : Nat) (h : i<98) : readReg P i=readReg (runCodes T bank [] loadCodes) i := by
    rw [load_take]
    exact take_read T bank 98 (editBase δ) i (by have := (beforeEdit_lt δ).1; omega) (beforeEdit_lt δ).2 h
  have viewP (i : Nat) (h : i<264) : readReg P i=readReg (runCodes T bank [] (literal.take 264)) i :=
    take_read T bank _ _ _ (beforeEdit_lt δ).1 (beforeEdit_lt δ).2 h
  have Vleft : readSnapshot P 235 236 237 238 239 240 241 242 LV := by
    simpa only [readSnapshot,viewP 235 (by decide),viewP 236 (by decide),viewP 237 (by decide),
      viewP 238 (by decide),viewP 239 (by decide),viewP 240 (by decide),viewP 241 (by decide),
      viewP 242 (by decide)] using V.left
  have Vright : readSnapshot P 245 246 247 248 249 250 251 252 RV := by
    simpa only [readSnapshot,viewP 245 (by decide),viewP 246 (by decide),viewP 247 (by decide),
      viewP 248 (by decide),viewP 249 (by decide),viewP 250 (by decide),viewP 251 (by decide),
      viewP 252 (by decide)] using V.right
  have Vcenter : readSnapshot P 62 63 43 64 50 51 52 53 C.curr := by
    refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩
    · exact (oldP 62 (by decide)).trans (S.word 1 5)
    · exact (oldP 63 (by decide)).trans (S.word 1 6)
    · exact (oldP 43 (by decide)).trans (S.word 1 7)
    · exact (oldP 64 (by decide)).trans (S.word 1 8)
    · exact (oldP 50 (by decide)).trans (S.bit 1 5)
    · exact (oldP 51 (by decide)).trans (S.bit 1 6)
    · exact (oldP 52 (by decide)).trans (S.bit 1 7)
    · exact (oldP 53 (by decide)).trans (S.bit 1 8)
  have hdelta : readReg P (if δ then 6 else 5)=.boolean δ := by
    cases δ
    · exact (oldP 5 (by decide)).trans S.ff
    · exact (oldP 6 (by decide)).trans S.tt
  have inP : EditInput r P (editBase δ) (C.tick%32) LV C.curr RV δ := by
    refine ⟨?_,Vleft,Vcenter,Vright,?_,(oldP 0 (by decide)).trans S.zero,
      (oldP 1 (by decide)).trans S.one,(oldP 3 (by decide)).trans S.bound,
      (oldP 5 (by decide)).trans S.ff,hdelta⟩
    · change (runCodes T bank [] (literal.take (editBase δ))).length=_
      rw [runCodes_length,List.length_take,Nat.min_eq_left (beforeEdit_lt δ).2]
      simp
    · intro j
      have h := j.isLt
      rw [viewP _ (by omega)]
      exact V.phase j
  have bC := snapshotBound_of_record r bank 1 false
  have dC := (native_record_bounds r bank 1).2.2.2.1
  have H := stageEdit_snapshot hr T bank hT P _ LV C.curr RV δ inP
    (neighborView_bounds r bank 0 C.tick) bC (neighborView_bounds r bank 2 C.tick)
    dC (right_view_distance r bank C.tick)
  have H' :
      readSnapshot (prefixRegs T bank δ)
        (editBase δ+33) (editBase δ+34) (editBase δ+35) (editBase δ+36)
        (editBase δ+37) (editBase δ+38) (editBase δ+39) (editBase δ+40)
        (phaseUpdate (heightMod r) (C.tick%32) LV C.curr RV δ) := by
    simpa only [prefixRegs,edit_take δ,runCodes_append] using H
  have fromClock i (hi : i<226) :
      readReg (prefixRegs T bank δ) i=readReg (runCodes T bank [] (literal.take 226)) i :=
    prefixRegs_read_of_take T bank δ 226 i (by cases δ <;> decide) hi
  have fromLoad i (hi : i<98) :
      readReg (prefixRegs T bank δ) i=readReg (runCodes T bank [] loadCodes) i := by
    rw [load_take]
    exact prefixRegs_read_of_take T bank δ 98 i (by cases δ <;> decide) hi
  obtain ⟨x,d,z,p,h,hm,rl,ap⟩ := H'
  refine ⟨(fromClock 137 (by decide)).trans K.reset,(fromClock 160 (by decide)).trans K.prop,
    (fromClock 204 (by decide)).trans K.clear,(fromClock 217 (by decide)).trans K.inc,
    (fromLoad 0 (by decide)).trans S.zero,(fromLoad 5 (by decide)).trans S.ff,
    (fromClock 225 (by decide)).trans (K.tick δ),(fromClock 221 (by decide)).trans (K.err δ),
    ?_,?_,?_,?_,?_,?_⟩
  · intro i
    rcases idx8 i with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact (fromLoad 62 (by decide)).trans (S.word 1 5)
    · exact (fromLoad 63 (by decide)).trans (S.word 1 6)
    · exact (fromLoad 43 (by decide)).trans (S.word 1 7)
    · exact (fromLoad 64 (by decide)).trans (S.word 1 8)
    · cases δ <;> exact x
    · cases δ <;> exact d
    · cases δ <;> exact z
    · cases δ <;> exact p
  · intro i
    rcases idx8 i with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact (fromLoad 59 (by decide)).trans (S.word 1 1)
    · exact (fromLoad 60 (by decide)).trans (S.word 1 2)
    · exact (fromLoad 39 (by decide)).trans (S.word 1 3)
    · exact (fromLoad 61 (by decide)).trans (S.word 1 4)
    · exact (fromLoad 62 (by decide)).trans (S.word 1 5)
    · exact (fromLoad 63 (by decide)).trans (S.word 1 6)
    · exact (fromLoad 43 (by decide)).trans (S.word 1 7)
    · exact (fromLoad 64 (by decide)).trans (S.word 1 8)
  · intro i
    rcases idx8 i with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact (fromLoad 50 (by decide)).trans (S.bit 1 5)
    · exact (fromLoad 51 (by decide)).trans (S.bit 1 6)
    · exact (fromLoad 52 (by decide)).trans (S.bit 1 7)
    · exact (fromLoad 53 (by decide)).trans (S.bit 1 8)
    · cases δ <;> exact h
    · cases δ <;> exact hm
    · cases δ <;> exact rl
    · cases δ <;> exact ap
  · intro i
    rcases idx8 i with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact (fromLoad 46 (by decide)).trans (S.bit 1 1)
    · exact (fromLoad 47 (by decide)).trans (S.bit 1 2)
    · exact (fromLoad 48 (by decide)).trans (S.bit 1 3)
    · exact (fromLoad 49 (by decide)).trans (S.bit 1 4)
    · exact (fromLoad 50 (by decide)).trans (S.bit 1 5)
    · exact (fromLoad 51 (by decide)).trans (S.bit 1 6)
    · exact (fromLoad 52 (by decide)).trans (S.bit 1 7)
    · exact (fromLoad 53 (by decide)).trans (S.bit 1 8)
  · exact pairWords_bound r _ _ bC (phaseUpdate_bounds r _ hr LV C.curr RV δ bC dC)
  · exact pairWords_bound r _ _ (snapshotBound_of_record r bank 1 true) bC

private theorem native_of_prim {r : Nat} (hr : 3≤r) (T : PrimTable r)
    (bank : Bank) (hT : PrimSem T bank) :
    let regs := runCodes T bank [] literal
    readNeed regs=(nativeSpec r bank).1 ∧ ∀ δ, readOut regs δ=(nativeSpec r bank).2 δ := by
  let L := decodeBank r bank 0
  let C := decodeBank r bank 1
  let R := decodeBank r bank 2
  have hL := (native_record_bounds r bank 0).1
  have hC := (native_record_bounds r bank 1).1
  have hR := (native_record_bounds r bank 2).1
  have V := view_run hr T bank hT
  constructor
  · have keep : readReg (runCodes T bank [] literal) 263 =
        readReg (runCodes T bank [] (literal.take 264)) 263 := by
      simpa only [List.take_length] using
        take_read T bank 264 literal.length 263 (by rw [literal_len]; decide) (Nat.le_refl _) (by decide)
    change (readReg (runCodes T bank [] literal) 263).asBool =
      pendingNeed (nativeClock (modulus r) L C R) C
    rw [keep,V.need]
    exact need_native r L C R hL hC hR
  · intro δ
    change readOut (runCodes T bank [] literal) δ =
      encodeOutput (finishNative (heightMod r) L C R (nativeClock (modulus r) L C R) δ)
    let N := finishNative (heightMod r) L C R (nativeClock (modulus r) L C R) δ
    let E := phaseUpdate (heightMod r) (C.tick%32) (neighborView C.tick L) C.curr (neighborView C.tick R) δ
    have P : OutputInputs T bank δ (flagSet r L C R)
        (pairWords C.curr E) (pairWords C.prior C.curr) (pairBits C.curr E) (pairBits C.prior C.curr)
        N.tick N.err := output_inputs_native hr T bank hT δ
    exact (generated_readOut T bank hT δ (flagSet r L C R)
      (pairWords C.curr E) (pairWords C.prior C.curr) (pairBits C.curr E)
      (pairBits C.prior C.curr) N.tick N.err P).trans (final_window_native r L C R δ hL hC hR)

/-- The exact 474-node instruction dump computes the independent row. -/
theorem generated_native (r : Nat) (hr : 3≤r) (bank : Bank) :
    let regs := runCodes (PrimInstance.table r hr bank) bank [] literal
    readNeed regs=(nativeSpec r bank).1 ∧ ∀ δ, readOut regs δ=(nativeSpec r bank).2 δ :=
  native_of_prim hr (PrimInstance.table r hr bank) bank (PrimInstance.semantics r hr bank)

/-- The assembled stage program has the same extensional behavior. -/
theorem assembled_native (r : Nat) (hr : 3≤r) (bank : Bank) :
    let regs := runCodes (PrimInstance.table r hr bank) bank [] build
    readNeed regs=(nativeSpec r bank).1 ∧ ∀ δ, readOut regs δ=(nativeSpec r bank).2 δ := by
  rw [build_eq_literal]
  exact generated_native r hr bank

/-- The cost-indexed serial tour machine has the same observable result
as the independent mathematical row. -/
theorem generated_native_tour (r : Nat) (hr : 3≤r) (bank : Bank) :
    let P := literal.map (toInstr (PrimInstance.table r hr bank) bank)
    let regs := (runMachine P (programCost P)).regs
    readNeed regs=(nativeSpec r bank).1 ∧ ∀ δ, readOut regs δ=(nativeSpec r bank).2 δ := by
  dsimp only
  rw [machine_finish (by omega)]
  exact generated_native r hr bank

end L4.Compiler.Native
