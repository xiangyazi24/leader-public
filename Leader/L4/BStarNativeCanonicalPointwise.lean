import Leader.L4.BStarNativeCanonicalPublication
import Leader.L4.BStarNativePointwise

namespace L4.BStarNativeCanonicalPointwise
open AllSizeProtocol BStarTrace BStarLongWork BStarLongFixedRouting
open BStarH6WordChart BStarH6Ordinal BStarAcquireVisitOrder BStarAcquireLiteralChain
open BStarResetChartTouch BStarLongFiberOwner BStarCustodyCuts BStarGrantWriterHistory
open BStarNumericChartCoverage BStarNativeSelectorOutput BStarNativeDecodedPublication
open BStarOperandSites BStarOperandBank BStarLongClaims BStarLongEvents
open BStarCommitReceiptAuth BStarCutOperandReadout BStarLongCommand BStarLongToken
open L4.Compiler.Native NativeHeightObservation NativeUnisonBridge UnisonRows

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step B
local notation "run" => BStarResetSchedule.run step

open BStarNativePointwise BStarNativeCanonicalPublication NativeHeightRange

private theorem decode_view (hr : 3≤r) (bank : Bank) (delta : Bool) (y : Output)
    (E : y=(nativeSpec r bank).2 delta) :
    decodeBank r (centerView y) 1=observe ((nativeSpec r bank).2 delta) := by
  apply native_exposure_roundtrip _ hr
  · simpa [centerView] using congrArg Output.digits E
  · simpa [centerView] using congrArg Output.hdr E

/-- One actual raw mark: if silent, every old H6 record stutters;
otherwise the initiator publishes the exact chosen native row and
all other records stutter. The same literal geometry supplies the
canonical significant digits. The selecting receipt remains genuine. -/
theorem canonical_pointwise_at_mark {base initial : X} (u v tail : List (Fin n))
    (cuts : CutFacts hp base initial u v) (hh : ∃ i,oldH6 B base i=true)
    (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (Q : X→Prop) (I : Q initial) (fiber : ∀ y,Q y→∀ i,Layout B base i=Layout B y i)
    (closed : ∀ y e,Q y→Q (step y e))
    (mark : Fin n) (hr : 3≤r)
    (flags : ∀ i,(longGeometry B (base i)).inside=decide (oldOrdinal B base hh i<r) ∧
      (longGeometry B (base i)).last=decide (oldOrdinal B base hh i+1=r))
    (notShort : ∀ j,oldH6 B base (rightNeighbor j)=true → r≤oldOrdinal B base hh j+1) :
    let old := run initial ((u++v)++tail)
    let fresh := step old mark
    (∀ i,oldH6 B base i=true → i≠mark → readRecord fresh i=readRecord old i) ∧
    ((NoPublication hp old mark mark ∧
      ∀ i,oldH6 B base i=true → readRecord fresh i=readRecord old i) ∨
     (¬NoPublication hp old mark mark ∧ oldH6 B base mark=true ∧
      ∃ (o : Owners (oldH6 B base)) (receipt : BStarLongToken.Payload),
        let header := fun q : Fin 3 => (endpoint (oldH6 B base) hh o ⟨q.val,by omega⟩).1
        let bank := bankAt (r:=r) old header
        let delta := (nativeSpec r bank).1 && decide (receipt.argument.toNat%2=1)
        let N := fun j => normalizeBiased (halfMod r) (rawClock r bank j)
        header 1=mark ∧
        (∃ (before after : List (Fin n)) (select : Fin n) (op : Nat)
          (d : BStarLongPublication.Descriptor) (selectedBank : Fin 3),
          (u++v)++tail=before++select::after ∧
          let src := run initial before (header 0)
          bind (longGeometry B src) 0 (atSite src.long 0)=.reply receipt ∧
          ReceiptBank op d receipt selectedBank) ∧
        readRecord fresh mark=observe ((nativeSpec r bank).2 delta) ∧
        clock (readRecord fresh mark)=(biasedRow (halfMod r) (N 0) (N 1) (N 2)).2 ∧
        ∀ q, header q≠mark →
          (bankAt (r:=r) fresh header).digits q=bank.digits q ∧
          (bankAt (r:=r) fresh header).hdr q=bank.hdr q)) := by
  classical
  let old := run initial ((u++v)++tail)
  let fresh := step old mark
  have loc : ∀ i,oldH6 B base i=true →
    WordSites (oldH6 B base) i (sites (r:=r) i) := by
    intro i H
    exact (exact_sites hh i H notShort).2.2
  have frame := BStarOperandFrame.visible_pointwise hp u v tail cuts Q I closed fiber mark
    (sep mark) (sites (r:=r)) loc
  have readHold (i : Fin n) (hi : oldH6 B base i=true)
      (H : i≠mark ∨ NoPublication hp old mark mark) :
      readRecord fresh i=readRecord old i :=
    congrArg (fun y=>decodeBank r (centerView y) 1) (frame i hi H)
  refine ⟨fun i hi ne=>readHold i hi (.inl ne),?_⟩
  by_cases N : NoPublication hp old mark mark
  · exact .inl ⟨N,fun i hi=>readHold i hi (.inr N)⟩
  obtain ⟨o,S,len,fall,pre,reset,w,entryWord,compiler,remainder,rest,A,W,C,L,p,e,V,
    hit,need,H,preSelect,sel,afterSelect,op,receipt,split,reply,auth,output⟩ :=
    canonical_from_original_tape hp u v tail cuts hh sep Q I fiber closed mark mark N hr flags notShort
  have mem : S.getD H.cursor fall∈S := by
    rw [←List.getElem_eq_getD (h:=show H.cursor<S.length by rw [C.length]; exact Nat.lt_succ_of_le H.cursor_le)]
    exact List.getElem_mem _
  have own := (C.entries _ mem).2
  rw [H.atCenter] at own
  have mid : mark=(endpoint (oldH6 B base) hh o 1).1 :=
    congrArg Prod.fst ((endpoint_spec (oldH6 B base) hh o 1).2.2 mark H.centerH6 own)
  let header := fun q : Fin 3 => (endpoint (oldH6 B base) hh o ⟨q.val,by omega⟩).1
  refine .inr ⟨N,H.centerH6,o,receipt,mid.symm,?_,?_,?_,?_⟩
  · let before := ((pre++reset)++entryWord++compiler)++preSelect
    have source : (S.getD 0 fall).1=header 0 := congrArg Prod.fst C.root
    have oldAt : run initial before = run (run (run (run initial (pre++reset)) entryWord) compiler) preSelect := by
      simp only [before,BStarResetSchedule.run_append]
    refine ⟨before,afterSelect++rest,sel,op,H.descriptor,H.bank,?_,?_⟩
    · rw [A,W,split]
      simp only [before,List.append_assoc,List.cons_append]
    · let z := run (run (run (run initial (pre++reset)) entryWord) compiler) preSelect
      let received (y : X) (i : Fin n) : Prop :=
        bind (longGeometry B (y i)) 0 (atSite ((y i).long : BitVec LW) 0)=.reply receipt
      have R : received z (S.getD 0 fall).1 := reply
      have M : received z (header 0) := source ▸ R
      exact ⟨oldAt.symm ▸ M,auth⟩
  · exact decode_view hr _ _ _ output
  · let bank := bankAt (r:=r) old header
    let delta := (nativeSpec r bank).1 && decide (receipt.argument.toNat%2=1)
    have norm : readRecord fresh mark=observe ((nativeSpec r bank).2 delta) :=
      decode_view hr _ _ _ output
    let N := fun j => normalizeBiased (halfMod r) (rawClock r bank j)
    change clock (readRecord fresh mark)=(biasedRow (halfMod r) (N 0) (N 1) (N 2)).2
    rw [norm]
    exact output_clock r (by omega) bank delta
  · intro q ne
    have h := (endpoint_spec (oldH6 B base) hh o ⟨q.val,by omega⟩).1
    exact BStarOperandFrame.input_port_after_cuts hp u v tail cuts Q I closed fiber mark (sep mark)
      header q h (loc _ h) (no_off_initiator hp old mark _ ne)

#print axioms canonical_pointwise_at_mark
end L4.BStarNativeCanonicalPointwise
