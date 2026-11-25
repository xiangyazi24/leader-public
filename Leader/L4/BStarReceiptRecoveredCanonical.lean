import Leader.L4.BStarReceiptRecoveredDispatcher
import Leader.L4.BStarNativeDecodedPublication
import Leader.L4.BStarNativeLoadBankWords
import Leader.L4.BStarNativePhysicalOutput
import Leader.L4.BStarNativeDispatcherActual
import Leader.L4.BStarNativeCheckedOutput
import Leader.L4.BStarNativeUniqueHit
import Leader.L4.Compiler.GeneratedNative

namespace L4.BStarReceiptRecoveredCanonical
open AllSizeProtocol BStarTrace BStarLongWork BStarLongLayout BStarLongArithmetic
open BStarH6WordChart BStarH6Ordinal BStarAcquireVisitOrder BStarAcquireLiteralChain
open BStarResetChartTouch BStarLongFixedRouting BStarCustodyCuts BStarGrantWriterHistory
open BStarNativeReceiptTape BStarNativePrefixInduction BStarNumericChartCoverage
open BStarGeneratedOwner BStarNativeInputAssembly BStarOperandBank
open BStarNativePhysicalOutput BStarNativeSelectorOutput BStarNativePackedRep
open BStarLongDoor BStarFinalCandidate BStarLongPublication BStarCommitReceiptAuth
open BStarLongToken BStarLongCommand
open BStarOperandSites BStarNativeLoadBankWords
open BStarAcquireAnchors BStarLongFiberOwner
open L4.Compiler L4.Compiler.Native L4.Compiler.Interp

open BStarOwnerRecoveryPass

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step B
local notation "run" => BStarResetSchedule.run step

/-- A literal publication on the original custody-cut tape exposes the
native mathematical row of the three actually held input banks. Its
data choice is the parity of the actual SEAL/BIT reply, gated by the
native NEED; no independently chosen byte image or bit is used. -/
theorem canonical_from_original_tape_need {base initial : X} (u v tail : List (Fin n))
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
      Recovered hp base hh o (run initial pre) reset ∧
      Chart hp base hh o S len fall ∧
      let old := run initial ((u++v)++tail)
      let origin := run initial (pre++reset)
      let source := (S.getD 0 fall).1
      let x := run origin entryWord
      let x408 := run x compiler
      let header := fun q : Fin 3 => (endpoint (oldH6 B base) hh o ⟨q.val,by omega⟩).1
      let bank : Bank := bankAt (r:=r) old header
      ∃ (_L : (significantSites hp base (fun j => S.getD j fall) len).length=r)
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
          H.descriptor.need=(nativeSpec r bank).1 ∧
          visible (step old mark) center (sites (r:=r) center)=
            (nativeSpec r bank).2 ((nativeSpec r bank).1 && decide (receipt.argument.toNat%2=1)) := by
  dsimp only
  obtain ⟨o,S,len,fall,pre,reset,w,entryWord,compiler,remainder,rest,A,W,Rcredit,C,_,
    native,whole,band,stable,legal,L,siteEq,D,H407,⟨hand⟩⟩ :=
    BStarReceiptRecoveredDispatcher.before_publication hp u v tail cuts hh sep Q I fiber closed mark center pub
      (by omega) flags notShort
  let old := run initial ((u++v)++tail)
  let origin := run initial (pre++reset)
  let source := (S.getD 0 fall).1
  let x := run origin entryWord
  let x408 := run x compiler
  let header := fun q : Fin 3 => (endpoint (oldH6 B base) hh o ⟨q.val,by omega⟩).1
  let bank : Bank := bankAt (r:=r) old header
  let table := PrimInstance.table r hr bank
  let ys := runCodes table bank [] literal
  have K : (S.getD 0 fall).2=0 := congrArg Prod.snd C.root
  obtain ⟨pf,ef,cf,Hf⟩ := H407
  have legalHit (pre : List (Fin n)) (e : Fin n) (t : List (Fin n))
      (W : compiler=pre++e::t)
      (_ : Hit hp base (fun j=>S.getD j fall) len (run x pre) e 407) :=
    legal pre e t W
  obtain ⟨p,e,t,V,hit,P,_,N,headers,h,desc,descNeed⟩ :=
    BStarNativeCheckedOutput.actual_output hp C sep K whole band stable L table bank
      (D table (PrimInstance.semantics r hr bank)) native legalHit
  obtain ⟨pEq,eEq,_⟩ := BStarNativeUniqueHit.unique hp K sep whole band cf V Hf hit
  subst p; subst e
  have from407 : x408=step (run x pf) ef := by
    change run x compiler=_
    rw [cf,BStarResetSchedule.run_append]
    rfl
  have same : old=run x408 (remainder++rest) := by
    unfold old x408 x origin
    rw [A,W,List.append_assoc,List.append_assoc,List.append_assoc]
    simp only [BStarResetSchedule.run_append]
  have fixed (before : List (Fin n)) (i : Fin n) : Layout B (run x408 before) i=Layout B base i := by
    have E := stable (compiler++before) i
    rw [BStarResetSchedule.run_append] at E
    exact E.symm
  have nativeEq : readNeed ys=(nativeSpec r bank).1 ∧ ∀ δ, readOut ys δ=(nativeSpec r bank).2 δ :=
    generated_native r hr bank
  have mathNeed : (readReg ys BStarLongSignatures.needIx).asBool=(nativeSpec r bank).1 :=
    nativeEq.1
  have readyNeed : need.read (x408 source).long=BitVec.ofBool (nativeSpec r bank).1 :=
    from407.symm ▸ N.trans (congrArg BitVec.ofBool mathNeed)
  have PP := show PackedRep x408 source (digitSite hp base (fun j=>S.getD j fall) len r L) 395 ys from
    from407.symm ▸ P
  have headImage : candidateHeaders.read (x408 source).long=BitVec.ofNat 18
      ((BStarLongSignatures.outHeaders0++BStarLongSignatures.outHeaders1).foldl
        (fun a j => a*2+((readReg ys j).asBool).toNat) 0) := from407.symm ▸ headers
  obtain ⟨b,e,after,op,f,split,reply,auth,output⟩ :=
    actual_native_output hp C sep K hand same pub fixed L ys PP headImage bank nativeEq.2
  have wanted : BStarLongPublication.decode (sourceDescriptor.read (x408 source).long)=
      some (finalDesc (run x pf source).long h) := by
    rw [from407,desc]
    exact decode_final _ h
  obtain ⟨_,_,_,_,_,_,decode,_,_⟩ := BStarNativeCommitHandoff.selecting_receipt hp hand K sep
  have D := Option.some.inj (decode.symm.trans wanted)
  have needDesc := (congrArg Descriptor.need D).trans (descNeed.trans mathNeed)
  unfold receiptChoice at output
  rw [needDesc] at output
  have mem : S.getD hand.cursor fall∈S := by
    rw [←List.getElem_eq_getD (h:=show hand.cursor<S.length by
      rw [C.length]; exact Nat.lt_succ_of_le hand.cursor_le)]
    exact List.getElem_mem _
  have own := (C.entries _ mem).2
  rw [hand.atCenter] at own
  have own10 : commandOwner (oldH6 B base) center 10=o.val := own
  have center10 := (endpoint_spec (oldH6 B base) hh o 10).2.2 center hand.centerH6 own10
  have rootEq : (S.getD len fall).1=center :=
    congrArg Prod.fst (C.terminal.trans center10.symm)
  have sitesEq : digitSite hp base (fun j=>S.getD j fall) len r L=sites (r:=r) center := by
    funext j
    exact (siteEq j).trans ((congrArg (fun i=>BStarCopyRightStrip.addr i j.val) rootEq).trans (addr_site center j))
  rw [sitesEq] at output
  exact ⟨o,S,len,fall,pre,reset,w,entryWord,compiler,remainder,rest,A,W,Rcredit,C,
    L,pf,ef,cf,Hf,readyNeed,hand,b,e,after,op,f,split,reply,auth,needDesc,output⟩

end L4.BStarReceiptRecoveredCanonical
