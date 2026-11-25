import Leader.L4.BStarNativeLoadTours
import Leader.L4.BStarPhysicalWordSem

namespace L4.BStarNativeLoadWord
open AllSizeProtocol BStarTrace BStarLongRegisters BStarLongLayout BStarLongToken
open BStarLongArithmetic BStarPhysicalWordSem BStarPhysicalDigitSem
open BStarNativeLoadTours

theorem load_word_slots : ∀ q : Fin 3,∀ f : Fin 9,WordSlot (loadNode q f) := by
  change ∀ q : Fin 3,∀ f : Fin 9,widthAt wordWidths (loadNode q f)=4
  decide +kernel

/-- A healthy LOAD has exactly its designated readback and does not
change the payload, even on packed digits whose value is zero. -/
theorem digit_step (g : LongGeometry) (x : BitVec LW) (q : Fin 3) (f : Fin 9)
    (p : Payload)
    (H : (physicalDigit g x (loadNode q f) (.load q f) p).2.fault=0) :
    ∃ v, digitLoad x q f p.argument.toNat=some v ∧
      physicalDigit g x (loadNode q f) (.load q f) p=(writeNum (loadNode q f) v,p) := by
  cases E : digitLoad x q f p.argument.toNat with
  | none =>
    simp [physicalDigit,E] at H
  | some v =>
    exact ⟨v,rfl,by simp [physicalDigit,E]⟩

theorem digit_readback (g : LongGeometry) (x : BitVec LW) (q : Fin 3) (f : Fin 9)
    (p : Payload) (v : Fin 16)
    (read : digitLoad x q f p.argument.toNat=some v.val) :
    num ((physicalDigit g x (loadNode q f) (.load q f) p).1.apply x) (loadNode q f)=v.val := by
  simp only [physicalDigit,read]
  exact num_write_of_lt (load_word_slots q f) v.isLt _

#print axioms digit_step
#print axioms digit_readback
end L4.BStarNativeLoadWord
