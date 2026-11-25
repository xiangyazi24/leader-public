import Leader.L4.BStarStageThroughCommit
import Leader.L4.BStarStageProvenance
import Leader.L4.BStarAliasRoster

namespace L4.BStarNativeStageHeaders
open AllSizeProtocol BStarTrace BStarLongLayout BStarLongWork BStarLongToken
open BStarStageCandidateWrite BStarStageThroughCommit BStarStageCandidateRetention
open BStarLongPublication BStarLongClaims BStarLongCommand
open BStarLongArithmetic BStarLongDoor
open L4.Compiler.Native L4.Compiler.Interp

def pushBit (a : Nat) (b : Bool) := a*2+b.toNat
def pack (bs : List Bool) : Nat := bs.foldl pushBit 0

private theorem pack_acc (bs : List Bool) (a : Nat) : bs.foldl pushBit a=2^bs.length*a+pack bs := by
  induction bs generalizing a with
  | nil => simp [pack]
  | cons b bs ih =>
    simp only [List.foldl_cons,List.length_cons,pack] at ih ⊢
    rw [ih (pushBit a b),ih (pushBit 0 b),Nat.pow_succ]
    simp only [pushBit,Nat.zero_mul,Nat.zero_add,Nat.mul_add,Nat.mul_assoc]
    rw [Nat.mul_comm a 2,Nat.add_assoc]

private theorem pack_cons (b : Bool) (bs : List Bool) :
    pack (b::bs)=2^bs.length*b.toNat+pack bs := by
  change bs.foldl pushBit (pushBit 0 b)=_
  rw [pack_acc]
  simp [pushBit]

private theorem pack_bound (bs : List Bool) : pack bs<2^bs.length := by
  induction bs with
  | nil => decide
  | cons b bs ih =>
    rw [pack_cons,List.length_cons,Nat.pow_succ]
    cases b <;> simp only [Bool.toNat_false,Bool.toNat_true,Nat.mul_zero,Nat.zero_add,Nat.mul_one] <;> omega

private theorem pack_bit (bs : List Bool) (i : Nat) (I : i<bs.length) :
    (pack bs).testBit (bs.length-1-i)=bs.getD i false := by
  induction bs generalizing i with
  | nil => simp at I
  | cons b bs ih =>
    rw [pack_cons,Nat.testBit_two_pow_mul_add _ (pack_bound bs)]
    cases i with
    | zero =>
      simp only [List.length_cons,Nat.add_sub_cancel,Nat.sub_zero,Nat.lt_irrefl,if_false,
        Nat.sub_self,List.getD_cons_zero]
      cases b <;> decide
    | succ i =>
      simp only [List.length_cons] at I ⊢
      have C : bs.length+1-1-(i+1)=bs.length-1-i := by omega
      rw [C,if_pos (by omega),ih i (by omega)]
      rfl

/-- The exact two candidate headers of the verified final register file,
in the high-to-low ordering used by the source packing and STAGE. -/
def headerBits (ys : List Value) : List Bool :=
  (BStarLongSignatures.outHeaders0++BStarLongSignatures.outHeaders1).map
    (fun j => (readReg ys j).asBool)

theorem header_count (ys : List Value) : (headerBits ys).length=18 := by
  simp only [headerBits,List.length_map]
  decide

theorem header_eq (ys : List Value) :
    (BStarLongSignatures.outHeaders0++BStarLongSignatures.outHeaders1).foldl
      (fun a j => a*2+((readReg ys j).asBool).toNat) 0=pack (headerBits ys) := by
  simp only [headerBits,pack,List.foldl_map,pushBit]

theorem low_headers (ys : List Value) (arg : Nat)
    (A : arg%2^18=pack (headerBits ys)) (which : Bool) (i : Fin 9) :
    argumentHeader arg which i = BitVec.ofBool (readReg ys ((outIx which).2 i)).asBool := by
  let j := (if which then 9 else 0)+i.val
  let bit := 9*(if which then 0 else 1)+(8-i.val)
  have hj : j<18 := by cases which <;> simp [j] <;> omega
  have hb : bit<18 := by cases which <;> simp [bit] <;> omega
  have ord : (headerBits ys).length-1-j=bit := by
    rw [header_count]
    cases which <;> simp [bit,j] <;> omega
  have E := pack_bit (headerBits ys) j (by rw [header_count]; exact hj)
  rw [ord,←A,Nat.testBit_mod_two_pow,decide_eq_true hb,Bool.true_and] at E
  have lookup : (headerBits ys).getD j false=(readReg ys ((outIx which).2 i)).asBool := by
    simp only [headerBits,List.getD_eq_getElem?_getD,List.getElem?_map]
    cases which with
    | false =>
      have eqJ : j=i.val := by simp [j]
      have K : j<BStarLongSignatures.outHeaders0.length := eqJ.symm ▸ i.isLt
      rw [List.getElem?_append_left K,eqJ]
      change _=(readReg ys (BStarLongSignatures.outHeaders0.getD i.val 0)).asBool
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (l:=BStarLongSignatures.outHeaders0) i.isLt]
      rfl
    | true =>
      have K : BStarLongSignatures.outHeaders0.length≤j := Nat.le_add_right 9 i.val
      rw [List.getElem?_append_right K]
      have J : j-BStarLongSignatures.outHeaders0.length=i.val := by
        change 9+i.val-9=i.val
        omega
      rw [J]
      change _=(readReg ys (BStarLongSignatures.outHeaders1.getD i.val 0)).asBool
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (l:=BStarLongSignatures.outHeaders1) i.isLt]
      rfl
  rw [lookup,Nat.testBit_eq_decide_div_mod_eq] at E
  apply BitVec.eq_of_toNat_eq
  change (BitVec.ofNat 1 (arg/2^bit)).toNat=
    (BitVec.ofBool (readReg ys ((outIx which).2 i)).asBool).toNat
  rw [BitVec.toNat_ofNat]
  cases H : (readReg ys ((outIx which).2 i)).asBool
  · rw [H] at E
    simp only [BitVec.ofBool_false]
    have B := Nat.mod_lt (arg/2^bit) (by decide : 0<2)
    have N := of_decide_eq_false E
    change arg/2^bit%2=0
    omega
  · rw [H] at E
    exact of_decide_eq_true E

/-- A healthy selected STAGE packet reuses the same mathematical header bits
from the exact post-PC407 register image, independently of its descriptor. -/
theorem decode_issued (ys : List Value) (x : BitVec LW) (pay : Payload)
    (stored : candidateHeaders.read x=BitVec.ofNat 18
      ((BStarLongSignatures.outHeaders0++BStarLongSignatures.outHeaders1).foldl
        (fun a j => a*2+((readReg ys j).asBool).toNat) 0))
    (issued : BStarStageProvenance.arg pay=
      (sourceDescriptor.read x).toNat*2^18+(candidateHeaders.read x).toNat)
    (which : Bool) (i : Fin 9) :
    argumentHeader pay.argument.toNat which i=
      BitVec.ofBool (readReg ys ((outIx which).2 i)).asBool := by
  apply low_headers ys
  have H := congrArg (fun a => a%(2^18)) issued
  change (pay.argument.toNat%2^25)%2^18=( _ + _ )%2^18 at H
  rw [Nat.mod_mod_of_dvd _ (by decide : (2:Nat)^18∣2^25)] at H
  rw [H,Nat.mul_comm ((sourceDescriptor.read x).toNat),Nat.add_comm,
    Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt (candidateHeaders.read x).isLt,stored,
    BitVec.toNat_ofNat,header_eq,Nat.mod_eq_of_lt]
  have bound := pack_bound (headerBits ys)
  rwa [header_count] at bound

end L4.BStarNativeStageHeaders
