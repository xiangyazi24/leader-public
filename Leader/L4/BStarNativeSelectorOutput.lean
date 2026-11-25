import Leader.L4.BStarCommitRingLanding
import Leader.L4.BStarCommitReceiptAuth
import Leader.L4.BStarBitParity
import Leader.L4.BStarNativeStageDigits
import Leader.L4.Compiler.NativeSpec

namespace L4.BStarNativeSelectorOutput
open AllSizeProtocol BStarTrace BStarLongLayout BStarLongWork BStarLongToken
open BStarLongPublication BStarLongEvents BStarStageCandidateWrite
open BStarH6WordChart BStarNativeStageDigits BStarCommitReceiptAuth BStarGrantWriterHistory
open L4.Compiler.Native L4.Compiler.Interp L4.Compiler.Digits
variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step B

/-- Actual choice carried by the authenticated SEAL/BIT receipt.
When NEED is false it selects branch zero without a coin assumption. -/
def receiptChoice (desc : Descriptor) (receipt : Payload) : Bool :=
  desc.need && decide (receipt.argument.toNat%2=1)

theorem receipt_bank {op : Nat} {desc : Descriptor} {f : Payload} {b : Fin 3}
    (input : ReceiptBank op desc f b) : b=candidate desc (receiptChoice desc f) := by
  apply BStarBitParity.choice_index
  rcases input with ⟨code,need,parity,rfl⟩|⟨code,need,rfl⟩
  · exact .sealCase code need parity
  · exact .bit code need

/-- Read the physical selector after the one literal COMMIT, then read
its bank (not a candidate bank supplied by the caller). -/
def visible {width : Nat} (x : X) (center : Fin n) (sites : Fin width→Fin n) : Output :=
  let b := readSel (x center).long
  ⟨fun f => val (bankWord x sites b f),
   fun f => ((bankHeader b f).read (x center).long).getLsbD 0⟩

/-- If both banks were staged on the same attempt and the actual
publication carries its authenticated selecting receipt, the selected
physical image equals the specified native candidate for that receipt. -/
theorem chosen_output {width : Nat} (old : X) (mark center : Fin n)
    (sites : Fin width→Fin n) (ys : List Value) (desc : Descriptor)
    (op : Nat) (receipt : Payload) (pub : Publication)
    (publication : ¬NoPublication hp old mark center)
    (named : pub∈(longTrace (oldPair B old mark) ((old mark).long,(old (rightNeighbor mark)).long)).publications)
    (auth : ReceiptBank op desc receipt pub.bank)
    (staged : ∀ which (f : Fin 9),
      (readReg ys ((outIx which).1 f)).asWord=
        val (bankWord (step old mark) sites (candidate desc which) f) ∧
      (bankHeader (candidate desc which) f).read (step old mark center).long=
        BitVec.ofBool (readReg ys ((outIx which).2 f)).asBool) :
    visible (step old mark) center sites=readOut ys (receiptChoice desc receipt) := by
  obtain ⟨_,b,_,_,_,only,_,_,_,_,_,_,selected⟩ :=
    BStarCommitRingLanding.ring_landing hp old mark center publication
  rw [only,List.mem_singleton] at named
  have bank : b=pub.bank := (congrArg Publication.bank named).symm
  have pick : readSel (step old mark center).long=candidate desc (receiptChoice desc receipt) :=
    selected.trans (bank.trans (receipt_bank auth))
  unfold visible
  rw [pick]
  let which := receiptChoice desc receipt
  change Output.mk _ _=Output.mk _ _
  congr 1
  · funext f
    exact (staged which f).1.symm
  · funext f
    rw [(staged which f).2]
    cases (readReg ys ((outIx which).2 f)).asBool <;> rfl

/-- Connect the actual physical readout to the independently specified
native mathematical row, using its accepted compiler equality. -/
theorem selected_native {width : Nat} (old : X) (mark center : Fin n)
    (sites : Fin width→Fin n) (ys : List Value) (inputBank : Bank) (desc : Descriptor)
    (op : Nat) (receipt : Payload) (pub : Publication)
    (publication : ¬NoPublication hp old mark center)
    (named : pub∈(longTrace (oldPair B old mark) ((old mark).long,(old (rightNeighbor mark)).long)).publications)
    (auth : ReceiptBank op desc receipt pub.bank)
    (staged : ∀ which (f : Fin 9),
      (readReg ys ((outIx which).1 f)).asWord=
        val (bankWord (step old mark) sites (candidate desc which) f) ∧
      (bankHeader (candidate desc which) f).read (step old mark center).long=
        BitVec.ofBool (readReg ys ((outIx which).2 f)).asBool)
    (math : ∀ which, readOut ys which=(nativeSpec width inputBank).2 which) :
    visible (step old mark) center sites=(nativeSpec width inputBank).2 (receiptChoice desc receipt) :=
  (chosen_output hp old mark center sites ys desc op receipt pub publication named auth staged).trans (math _)

#print axioms selected_native
#print axioms chosen_output
end L4.BStarNativeSelectorOutput
