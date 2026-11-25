import Leader.L4.Compiler.GeneratedView
import Leader.L4.Compiler.GeneratedClock

/-! S8 inputs from the literal S0–S2 loads and S3–S7 flags. The small
bridge makes all retention obligations explicit at the actual indices. -/
namespace L4.Compiler.Native
open Interp

private theorem side_word_before98 (q : Fin 3) (i : Fin 9) :
    sideOut (sideBase q) i<98 := by
  have Q := q.isLt
  match i with
  | ⟨0,_⟩ | ⟨1,_⟩ | ⟨2,_⟩ | ⟨3,_⟩ | ⟨4,_⟩ | ⟨5,_⟩ | ⟨6,_⟩ | ⟨7,_⟩ | ⟨8,_⟩ =>
    simp only [sideOut,sideBase] <;> omega

private theorem side_bit_before98 (q : Fin 3) (i : Fin 9) :
    sideBase q+9+i.val<98 := by
  have Q := q.isLt
  have I := i.isLt
  simp only [sideBase]
  omega

/-- The clock flags may be obtained by any instruction segment satisfying
the stated literal clock register facts. All S0–S2 reads are retained
by append-only evaluation, not assumed a second time. -/
theorem view_input_of_clock_stage {r : Nat} (T : PrimTable r) (bank : Bank)
    (regs : List Value) (cs : List Code) (H : LoadFacts r bank regs)
    (K : ClockFacts r (decodeBank r bank 0) (decodeBank r bank 1) (decodeBank r bank 2)
      (runCodes T bank regs cs)) :
    ViewInput r bank (runCodes T bank regs cs)
      (clockReset r (decodeBank r bank 0) (decodeBank r bank 1) (decodeBank r bank 2))
      (clockProp r (decodeBank r bank 0) (decodeBank r bank 1) (decodeBank r bank 2))
      (clockClear r (decodeBank r bank 0) (decodeBank r bank 1) (decodeBank r bank 2))
      (clockInc r (decodeBank r bank 0) (decodeBank r bank 1) (decodeBank r bank 2)) := by
  let out := runCodes T bank regs cs
  have W (q : Fin 3) (i : Fin 9) :
      readReg out (sideOut (sideBase q) i) = .word (recordWord (decodeBank r bank q) i) := by
    rw [show readReg out (sideOut (sideBase q) i)=readReg regs (sideOut (sideBase q) i) from
      runCodes_prefix T bank regs cs _ (by rw [H.length]; exact side_word_before98 q i)]
    exact H.word q i
  have B (q : Fin 3) (i : Fin 9) :
      readReg out (sideBase q+9+i.val) = .boolean (recordBit (decodeBank r bank q) i) := by
    rw [show readReg out (sideBase q+9+i.val)=readReg regs (sideBase q+9+i.val) from
      runCodes_prefix T bank regs cs _ (by rw [H.length]; exact side_bit_before98 q i)]
    exact H.bit q i
  have Z : readReg out 0 = .word 0 :=
    (runCodes_prefix T bank regs cs 0 (by rw [H.length]; decide)).trans H.zero
  refine ⟨K.length,W 1 0,W 0 0,W 2 0,?_,?_,?_,?_,W 1 7,B 1 5,Z,K.reset,K.prop,K.clear,K.inc⟩
  · exact ⟨W 0 1,W 0 2,W 0 3,W 0 4,B 0 1,B 0 2,B 0 3,B 0 4⟩
  · exact ⟨W 0 5,W 0 6,W 0 7,W 0 8,B 0 5,B 0 6,B 0 7,B 0 8⟩
  · exact ⟨W 2 1,W 2 2,W 2 3,W 2 4,B 2 1,B 2 2,B 2 3,B 2 4⟩
  · exact ⟨W 2 5,W 2 6,W 2 7,W 2 8,B 2 5,B 2 6,B 2 7,B 2 8⟩

/-- Actual S0–S7 program, in direct native clock vocabulary. -/
theorem view_input_after_clock {r : Nat} (hr : 3≤r) (T : PrimTable r)
    (bank : Bank) (hT : PrimSem T bank) :
    let L := decodeBank r bank 0
    let C := decodeBank r bank 1
    let R := decodeBank r bank 2
    ViewInput r bank (runCodes T bank [] loadClockCodes)
      (clockReset r L C R) (clockProp r L C R) (clockClear r L C R) (clockInc r L C R) := by
  have K := clock_run hr T bank hT
  rw [←loadClockCodes_literal] at K
  unfold loadClockCodes at K ⊢
  simp only [runCodes_append] at K ⊢
  exact view_input_of_clock_stage T bank _ clockCodes (load_spec hr T bank hT) K

#print axioms view_input_after_clock
end L4.Compiler.Native
