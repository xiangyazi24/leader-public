import Leader.L4.BStarNativeCompletePublication
import Leader.L4.NativeHeightRange
import Leader.L4.NativeUnisonBridge

namespace L4.BStarNativeDecodedPublication
open AllSizeProtocol BStarTrace BStarLongWork BStarLongLayout BStarLongArithmetic
open BStarH6WordChart BStarH6Ordinal BStarAcquireVisitOrder BStarAcquireLiteralChain
open BStarResetChartTouch BStarLongFixedRouting BStarCustodyCuts BStarGrantWriterHistory
open BStarNativeReceiptTape BStarNativePrefixInduction BStarNumericChartCoverage
open BStarGeneratedOwner BStarNativeInputAssembly BStarOperandBank
open BStarNativePhysicalOutput BStarNativeSelectorOutput BStarNativePackedRep
open BStarLongDoor BStarFinalCandidate BStarLongPublication BStarCommitReceiptAuth
open BStarLongToken BStarLongCommand
open L4.Compiler L4.Compiler.Native L4.Compiler.Interp

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step B
local notation "run" => BStarResetSchedule.run step


open NativeHeightObservation NativeHeightRange NativeUnisonBridge UnisonRows

/-- Put the selected physical image in the center port of the ordinary
incident decoder. Other ports are dummy: this only reads port 1. -/
def centerView (y : Output) : Bank :=
  ⟨fun q f => if q=1 then y.digits f else 0, fun q f => if q=1 then y.hdr f else false⟩

/-- At the same marked COMMIT as the physical byte theorem, the ordinary
incident decoder observes the exact native update. Its clock agrees
with the biased row on the normalized three actual input clocks. The
receipt parity here is an observed bit, not a fairness assumption. -/
theorem decoded_from_original_tape {base initial : X} (u v tail : List (Fin n))
    (cuts : CutFacts hp base initial u v) (hh : ∃ i,oldH6 B base i=true)
    (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (Q : X→Prop) (I : Q initial) (fiber : ∀ y,Q y→∀ i,Layout B base i=Layout B y i)
    (closed : ∀ y e,Q y→Q (step y e))
    (mark center : Fin n)
    (pub : ¬NoPublication hp (run initial ((u++v)++tail)) mark center)
    (hr : 3≤r)
    (flags : ∀ i,(longGeometry B (base i)).inside=decide (oldOrdinal B base hh i<r) ∧
      (longGeometry B (base i)).last=decide (oldOrdinal B base hh i+1=r))
    (notShort : ∀ j,oldH6 B base (rightNeighbor j)=true → r≤oldOrdinal B base hh j+1) :
    ∃ (o : Owners (oldH6 B base)) (S : List (Pos n)) (len : Nat) (fall : Pos n)
      (pre reset w entryWord compiler remainder rest : List (Fin n)),
      (u++v)++tail=(pre++reset)++(w++rest) ∧ w=entryWord++compiler++remainder ∧
      Chart hp base hh o S len fall ∧
      let old := run initial ((u++v)++tail)
      let origin := run initial (pre++reset)
      let source := (S.getD 0 fall).1
      let x := run origin entryWord
      let x408 := run x compiler
      let header := fun q : Fin 3 => (endpoint (oldH6 B base) hh o ⟨q.val,by omega⟩).1
      let bank : Bank := bankAt (r:=r) old header
      ∃ (L : (significantSites hp base (fun j => S.getD j fall) len).length=r)
        (pre407 : List (Fin n)) (mark407 : Fin n),
        compiler=pre407++[mark407] ∧
        Hit hp base (fun j=>S.getD j fall) len (run x pre407) mark407 407 ∧
        need.read (x408 source).long=BitVec.ofBool (nativeSpec r bank).1 ∧
        ∃ (H : BStarNativeActualLoadAccepted.CommitHandoff hp base old x408
            (fun j=>S.getD j fall) len remainder rest mark center)
          (preSelect : List (Fin n)) (select : Fin n) (afterSelect : List (Fin n))
          (op : Nat) (receipt : Payload),
          remainder=preSelect++select::afterSelect ∧
          bind (longGeometry B (run x408 preSelect source)) 0
            (atSite (run x408 preSelect source).long 0)=.reply receipt ∧
          ReceiptBank op H.descriptor receipt H.bank ∧

          let delta := (nativeSpec r bank).1 && decide (receipt.argument.toNat%2=1)
          let physical := visible (step old mark) center (digitSite hp base (fun j=>S.getD j fall) len r L)
          let observed := decodeBank r (centerView physical) 1
          let N := fun j => normalizeBiased (halfMod r) (rawClock r bank j)
          physical=(nativeSpec r bank).2 delta ∧
          observed=observe ((nativeSpec r bank).2 delta) ∧
          clock observed=(biasedRow (halfMod r) (N 0) (N 1) (N 2)).2 := by
  obtain ⟨o,S,len,fall,pre,reset,w,entryWord,compiler,remainder,rest,A,W,C,L,p,e,V,
    hit,need,H,preSelect,sel,afterSelect,op,receipt,split,reply,auth,output⟩ :=
    BStarNativeCompletePublication.from_original_tape hp u v tail cuts hh sep Q I fiber closed mark center pub hr flags notShort
  refine ⟨o,S,len,fall,pre,reset,w,entryWord,compiler,remainder,rest,A,W,C,L,p,e,V,
    hit,need,H,preSelect,sel,afterSelect,op,receipt,split,reply,auth,output,?_,?_⟩
  · apply native_exposure_roundtrip _ hr
    · simpa [centerView] using congrArg Output.digits output
    · simpa [centerView] using congrArg Output.hdr output
  · have rpos : 0<r := by omega
    have clockView (y : Output) : clock (observe y)=outputClock y := rfl
    have decoded := fun (bank : Bank) (delta : Bool) =>
      native_exposure_roundtrip r hr bank (centerView ((nativeSpec r bank).2 delta)) delta 1
        (by simp [centerView]) (by simp [centerView])
    rw [output,decoded,clockView]
    exact output_clock r rpos _ _

#print axioms decoded_from_original_tape
end L4.BStarNativeDecodedPublication
