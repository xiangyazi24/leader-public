import Leader.L4.BStarNativePackedRep
import Leader.L4.BStarStageThroughCommit
import Leader.L4.BStarNativeNumberRetention

namespace L4.BStarNativeStageDigits
open AllSizeProtocol BStarTrace BStarLongLayout BStarLongWork BStarLongToken
open BStarLongOutgoing BStarLongSignatures BStarLongArithmetic BStarLongRegisters
open BStarPhysicalDigitSem BStarPhysicalWordSem BStarNativeZeroHead
open BStarNativePackedRep BStarAliasRoster BStarNativeNumberRetention
open BStarGeneratedOwner BStarGeneratedBandScan BStarResetChartTouch
open BStarH6WordChart BStarAcquireVisitOrder BStarAcquireLiteralChain
open BStarStageThroughCommit BStarStageCandidateWrite BStarStageCandidateRetention
open BStarLongClaims BStarLongCommand BStarLongPublication
open L4.Compiler.Digits L4.Compiler.Native L4.Compiler.Interp
variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step B
local notation "run" => BStarResetSchedule.run step

set_option maxRecDepth 4096

/-- Every output digit register is a genuinely evaluated, four-bit
distributed slot, not one of the scalar SSA aliases. -/
theorem output_slot (which : Bool) (i : Fin 9) :
    ∃ j, j<395 ∧ start j=outIndex which i ∧ WordSlot (outIndex which i) := by
  let js (which : Bool) : List Nat :=
    if which then [159,334,338,342,346,350,354,358,362] else [159,234,238,242,246,250,254,258,262]
  have check (b : Bool) : (List.finRange 9).all (fun f =>
      let j := (js b).getD f.val 0
      decide (j<395) && (start j==outIndex b f) && decide (widthAt wordWidths (outIndex b f)=4))=true := by
    cases b <;> decide +kernel
  have V := List.all_eq_true.mp (check which) i (List.mem_finRange _)
  simp only [Bool.and_eq_true,decide_eq_true_eq,beq_iff_eq] at V
  exact ⟨_,V.1.1,V.1.2,V.2⟩

/-- One STAGE candidate physically assembled from its retained bank
nibbles, in the owner's canonical least-significant-first order. -/
def bankWord {width : Nat} (x : X) (sites : Fin width→Fin n) (bank : Fin 3) (i : Fin 9) :
    Word width := fun j => ⟨((bankDigit bank i).read (x (sites j)).long).toNat,
      ((bankDigit bank i).read (x (sites j)).long).isLt⟩

/-- If the candidate bank contains the actual packed STAGE digit at each
canonical site, its assembled value is already the checked compiler image. -/
theorem assembled {width : Nat} (x y : X) (root : Fin n) (sites : Fin width→Fin n)
    (regs : List Value) (P : PackedRep x root sites 395 regs) (selected : Fin 3)
    (which : Bool) (f : Fin 9)
    (copy : ∀ d, (bankDigit selected f).read (y (sites d)).long=readDigit (x (sites d)).long which f) :
    readReg regs (outIndex which f)=.word (val (bankWord y sites selected f)) := by
  obtain ⟨k,hk,E,slot⟩ := output_slot which f
  have R := P.numeric k hk (E.symm ▸ slot)
  simp only [E] at R
  have wordEq : bankWord y sites selected f=
      readWord (fun j => (x (sites j)).long) (outIndex which f) slot := by
    funext d
    apply Fin.ext
    change ((bankDigit selected f).read (y (sites d)).long).toNat=
      num (x (sites d)).long (outIndex which f)
    rw [copy d]
    change num (x (sites d)).long (outIndex which f)%16=_
    exact Nat.mod_eq_of_lt (num_lt slot _)
  rw [wordEq]
  exact R

/-- Retain one verified output register up to the real old STAGE
departure, on the same word. The prerequisite names the actual root
PC exclusion, not a synthetic no-writer assumption. -/
theorem old_digit {base initial : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    {w : List (Fin n)} {m : Mode}
    (T : GeneratedOwner hp base (fun j => S.getD j fall) len initial .idle w m)
    (pre tape post : List (Fin n)) (W : w=pre++tape++post)
    (i : Fin n) (j : Nat) (hj : j≤len) (loc : S.getD j fall=(i,1))
    (pcSafe : ∀ a e b,tape=a++e::b → 408≤pc (run initial (pre++a)) (S.getD 0 fall).1)
    (which : Bool) (f : Fin 9) :
    readDigit ((run (run initial pre) tape) i).long which f=
      readDigit (run initial pre i).long which f := by
  obtain ⟨k,hk,E,_⟩ := output_slot which f
  have node : nodeOf (13+k)=some (outIndex which f) := by rw [←E]; exact scheduled_node hk
  have R := retain_interval hp chart sep T pre tape post W i j hj loc (13+k)
    (outIndex which f) node (fun a e b W' => by have F := pcSafe a e b W'; omega)
  unfold readDigit
  rw [R]

/-- Actual selected STAGE writes, retained through the designated
COMMIT state, still read the checked final output at this owner site. -/
theorem retained_digit (old : X) (e : Fin n) (C : CommandClaim) (pay : Payload)
    (d : Descriptor) (which : Bool) (endSite origin : BitVec LW) (f : Fin 9) :
    let g := oldPair B old e
    let raw := ((old e).long,(old (rightNeighbor e)).long)
    C.source.occurrence.val=1 →
    (C,.advance pay)∈BStarBankTrace.offers g raw →
    pay.fault=0 → pay.opcode.toNat=stageOp →
    BStarLongPublication.decode (BitVec.ofNat 7 (pay.argument.toNat/2^18))=some d →
    (g.1.axes.h6=true → actual raw.1 d=true) →
    BankAt (candidate d which) endSite=BankAt (candidate d which) (step old e e).long →
    g.1.inside=true →
    readDigit raw.1 which f=readDigit origin which f →
    (bankDigit (candidate d which) f).read endSite=readDigit origin which f := by
  dsimp only
  intro center sel good op dec auth kept inside digits
  exact ((retained_values hp old e C pay d which endSite center sel good op dec auth kept).1 inside f).trans digits

#print axioms assembled
#print axioms old_digit
#print axioms retained_digit
end L4.BStarNativeStageDigits
