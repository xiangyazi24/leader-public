import Leader.L4.BStarPhysicalWordSem
import Leader.L4.Compiler.DigitsWords

namespace L4.BStarNativeScanSem
open AllSizeProtocol BStarTrace BStarLongLayout BStarLongToken BStarLongArithmetic
open BStarPhysicalWordSem BStarPhysicalDigitSem
open L4.Compiler.Digits

/-- The exact old-row scan uses digit 0, the low bit of digit 1,
and then retains the same accumulator. Offset correctness concerns
only these first two cases; END bits are irrelevant. -/
theorem scan_value {r : Nat} {geom : Fin r → LongGeometry}
    {old updated : Fin r → BitVec LW} {i a : Nat} {tokens : Nat → Payload}
    (S : DigitSweep geom old updated i (.scan5 a) tokens) (ha : WordSlot a)
    (init : arg tokens 0=0) (hr : 2≤r)
    (pos : ∀ j, ScanPosition (geom j) j.val) :
    arg tokens r=val (readWord old a ha)%32 := by
  let w := readWord old a ha
  let first : Fin r := ⟨0,by omega⟩
  let second : Fin r := ⟨1,by omega⟩
  have A (j : Fin r) : (physicalDigit (geom j) (old j) i (.scan5 a) (tokens j.val)).2 =
      tokens (j.val+1) := congrArg Prod.snd (S.step j)
  have z₀ : arg tokens 1=(w first).val := by
    have E := congrArg (fun p : Payload => p.argument.toNat) (A first)
    have off₀ : off (geom first)=0 := (pos first).1.mpr rfl
    change (tokens 0).argument.toNat=0 at init
    unfold off at off₀
    simp only [physicalDigit,show first.val=0 from rfl,off₀,BEq.rfl,if_true,init,
      Nat.zero_div,Nat.zero_mul,Nat.zero_add,BitVec.toNat_ofNat] at E
    have small := num_lt ha (old first)
    rw [Nat.mod_eq_of_lt (by omega)] at E
    exact E.symm
  have z₁ : arg tokens 2=(w first).val+16*((w second).val%2) := by
    have E := congrArg (fun p : Payload => p.argument.toNat) (A second)
    have off₁ : off (geom second)=1 := (pos second).2.mpr rfl
    have small : (tokens 1).argument.toNat<16 := by rw [show (tokens 1).argument.toNat=(w first).val from z₀]; exact (w first).isLt
    unfold off at off₁
    simp only [physicalDigit,show second.val=1 from rfl,off₁,show ((1:Nat)==0)=false from rfl,
      Bool.false_eq_true,if_false,BEq.rfl,if_true,BitVec.toNat_ofNat,Nat.mod_eq_of_lt small] at E
    change ((tokens 1).argument.toNat+16*(num (old second) a%2))%2^34=(tokens 2).argument.toNat at E
    rw [Nat.mod_eq_of_lt (by omega)] at E
    exact E.symm.trans (by rw [show (tokens 1).argument.toNat=(w first).val from z₀]; rfl)
  have holds (j : Nat) (hj : j<r) (low : 2≤j) : arg tokens (j+1)=arg tokens j := by
    let k : Fin r := ⟨j,hj⟩
    have E := congrArg (fun p : Payload => p.argument.toNat) (A k)
    have no₀ : off (geom k)≠0 := fun r => by have U := (pos k).1.mp r; change j=0 at U; omega
    have no₁ : off (geom k)≠1 := fun r => by have U := (pos k).2.mp r; change j=1 at U; omega
    unfold off at no₀ no₁
    have small := (tokens j).argument.isLt
    simp only [physicalDigit,show ((if (geom k).axes.h6 then 0 else min 5 (geom k).offset)==0)=false from
      Bool.eq_false_iff.mpr (fun B => no₀ (beq_iff_eq.mp B)),
      show ((if (geom k).axes.h6 then 0 else min 5 (geom k).offset)==1)=false from
      Bool.eq_false_iff.mpr (fun B => no₁ (beq_iff_eq.mp B)),
      Bool.false_eq_true,if_false,BitVec.toNat_ofNat] at E
    change (tokens j).argument.toNat % 2^34=(tokens (j+1)).argument.toNat at E
    rw [Nat.mod_eq_of_lt small] at E
    exact E.symm
  have tail : ∀ t, 2≤t → t≤r → arg tokens t=arg tokens 2 := by
    intro t
    induction t with
    | zero => omega
    | succ t ih =>
      intro L U
      by_cases Q : t+1=2
      · rw [Q]
      · rw [holds t (by omega) (by omega)]
        exact ih (by omega) (by omega)
  have M := valJ_mod w 2 hr (r-2) (by omega)
  have E : val w=valJ w (2+(r-2)) (by omega) := by
    unfold val
    congr 1
    omega
  rw [tail r hr (Nat.le_refl _),z₁,←show val w % 256 % 32=val w %32 from
    Nat.mod_mod_of_dvd _ (by decide),E,M]
  rw [val_succ,val_succ]
  change (w first).val+16*((w second).val%2)=(0+1*(w first).val+16*(w second).val)%32
  have f := (w first).isLt
  omega

#print axioms scan_value
end L4.BStarNativeScanSem
