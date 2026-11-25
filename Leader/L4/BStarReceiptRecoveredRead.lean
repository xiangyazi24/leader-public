import Leader.L4.BStarPhysicalReserved
import Leader.L4.BStarReceiptRecoveredCanonical
import Leader.L4.BStarRecoveredReveal
import Leader.L4.BStarNativeCanonicalPointwise
import Leader.L4.BStarReceiptChoice
import Leader.L4.BStarReceiptBitOrigin
import Leader.L4.BStarReceiptBitNoPrior
import Leader.L4.BStarReceiptKey
import Leader.L4.BStarReceiptStopSplit
import Leader.L4.BStarMarkCompletion

namespace L4.BStarReceiptRecoveredRead
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
open AllSizeProtocol BStarTrace BStarLongWork BStarLongFixedRouting
open BStarH6WordChart BStarH6Ordinal BStarAcquireVisitOrder BStarAcquireLiteralChain
open BStarResetChartTouch BStarLongFiberOwner BStarCustodyCuts BStarGrantWriterHistory
open BStarNumericChartCoverage BStarNativeSelectorOutput BStarNativeDecodedPublication
open BStarOperandSites BStarOperandBank BStarLongClaims BStarLongEvents
open BStarCommitReceiptAuth BStarCutOperandReadout BStarLongCommand BStarLongToken
open L4.Compiler.Native NativeHeightObservation NativeUnisonBridge UnisonRows
open BStarNativePointwise BStarNativeCanonicalPublication NativeHeightRange
open BStarAcquireAnchors BStarNativePortGeometry BStarNeedCompletionInvariant
open BStarMarkCompletion BStarClearanceOffset BStarClearanceRaceMark BStarBitParity
open BStarPhysicalPairLaw BStarPhysicalIncrementLedger BStarIncrementLedger BStarNativeNeedLift
open BStarFenceReceiverChart

open BStarOwnerRecoveryPass

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step B
local notation "run" => BStarResetSchedule.run step

/-- From a real native NEED publication, find its healthy physical BIT
on precisely the original word. The bit determines every visible native
field at this publication, not merely the staged bank number. -/

theorem physical_need_read {base initial : X} (u v tail : List (Fin n))
    (cuts : CutFacts hp base initial u v) (hh : ∃ i,oldH6 B base i=true)
    (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (Q : X→Prop) (I : Q initial) (fiber : ∀ y,Q y→∀ i,Layout B base i=Layout B y i)
    (closed : ∀ y e,Q y→Q (step y e))
    (offset : correct (oldH6 B base) hh 5 initial)
    (initialTime : Fin n→Nat)
    (mark : Fin n) (hi : oldH6 B base mark=true)
    (width : 5≤r)
    (flags : ∀ i,(longGeometry B (base i)).inside=decide (oldOrdinal B base hh i<r) ∧
      (longGeometry B (base i)).last=decide (oldOrdinal B base hh i+1=r))
    (notShort : ∀ j,oldH6 B base (rightNeighbor j)=true → r≤oldOrdinal B base hh j+1)
    (pub : ¬NoPublication hp (run initial ((u++v)++tail)) mark mark)
    (need : consults (r:=r) hh
      (fun i=>readRecord (r:=r) (run initial ((u++v)++tail)) i.val) ⟨mark,hi⟩=true) :
    ∃ (lead suffix : List (Fin n)) (side : Side) (gate : Fin n)
      (o : Owners (oldH6 B base)) (S : List (Pos n)) (len : Nat) (fall : Pos n) (j : Nat),
      ((u++v)++tail)=lead++incident gate side::suffix ∧
      BStarRecoveredReveal.Admitted hp base initial hh lead gate ∧
      BStarPhysicalReserved.admittedRead hp base initial hh initialTime ((u++v)++tail) lead.length =
        some (mark, firstBit side) ∧
      Chart hp base hh o S len fall ∧ j<len ∧ S.getD j fall=(gate,1) ∧
      commandOwner (oldH6 B base) mark 1=o.val ∧
      BStarBitOneObservation.Observes gate j (run initial lead) (.out j) (incident gate side) ∧
      BeforePublication hp (run initial lead) mark (incident gate side::suffix) ∧
      incAt hp base hh (run initial ((u++v)++tail)) mark=some mark ∧
      reveal hp base hh initial (ownerAt hp base hh) initialTime lead (incident gate side)=
        some ((mark,count initialTime (tapeInc hp base hh initial ((u++v)++tail)) mark ((u++v)++tail).length),firstBit side) ∧
      (fun i : Header (oldH6 B base)=>readRecord (r:=r) (step (run initial ((u++v)++tail)) mark) i.val)=
        activate (r:=r) hh (fun i=>readRecord (r:=r) (run initial ((u++v)++tail)) i.val)
          ⟨mark,hi⟩ (firstBit side) := by
  classical
  let old := run initial ((u++v)++tail)
  let before : Header (oldH6 B base)→NativeRecord := fun i=>readRecord (r:=r) old i.val
  let center : Header (oldH6 B base) := ⟨mark,hi⟩
  have hr : 3≤r := by omega
  obtain ⟨o,S,len,fall,pre,reset,w,entryWord,compiler,remainder,rest,A,W,Rcredit,C,L,f,e,V,
    hit,needFile,H,preSelect,sel,afterSelect,op,receipt,split,reply,auth,needDesc,output⟩ :=
      BStarReceiptRecoveredCanonical.canonical_from_original_tape_need hp u v tail cuts hh sep Q I fiber closed mark mark pub hr flags notShort
  let head := fun q : Fin 3 => (endpoint (oldH6 B base) hh o ⟨q.val,by omega⟩).1
  let bank := bankAt (r:=r) old head
  have mem : S.getD H.cursor fall∈S := by
    rw [←List.getElem_eq_getD (h:=show H.cursor<S.length by rw [C.length]; exact Nat.lt_succ_of_le H.cursor_le)]
    exact List.getElem_mem _
  have own := (C.entries _ mem).2
  rw [H.atCenter] at own
  have mid : mark=(endpoint (oldH6 B base) hh o 1).1 :=
    congrArg Prod.fst ((endpoint_spec (oldH6 B base) hh o 1).2.2 mark H.centerH6 own)
  have ports : ∀ q,decodeBank r bank q=before (neighborHeader hh center q) :=
    ports_are_neighbors old hh o center mid.symm
  have nativeNeed : (nativeSpec r bank).1=true := (consults_eq_nativeNeed hh before center bank ports).symm.trans need
  have N : H.descriptor.need=true := needDesc.trans nativeNeed
  let assembly := ((pre++reset)++entryWord)++compiler
  let x408 := run initial assembly
  have A0 : ((u++v)++tail)=assembly++(remainder++rest) := by
    rw [A,W]
    simp only [assembly,List.append_assoc]
  have E0 : x408=run (run (run initial (pre++reset)) entryWord) compiler := by
    simp only [x408,assembly,BStarResetSchedule.run_append]
  have stable (z : List (Fin n)) : Q (run initial z) := by
    have H : ∀ x (z : List (Fin n)), Q x→Q (run x z) := by
      intro x z
      induction z generalizing x with
      | nil => exact id
      | cons a z ih => intro h; exact ih _ (closed _ a h)
    exact H _ _ I
  have stableH6 (z : List (Fin n)) (i : Fin n) :
      oldH6 B (run initial z) i=oldH6 B base i :=
    (congrArg Prod.fst (fiber _ (stable z) i)).symm
  have off : correct (oldH6 B base) hh 5 x408 :=
    BStarNativeOffsetTrace.closed_word hp _ hh sep initial assembly offset
      (fun a b _=>funext (stableH6 a))
  have fixed : ∀ a b,remainder=a++b → ∀ i,oldH6 B (run x408 a) i=oldH6 B base i := by
    intro a b _ i
    rw [←BStarResetSchedule.run_append]
    exact stableH6 _ i
  obtain ⟨start,preFlight,spectators,residual,out,back,after,issue,arrive,turn,ack,j,p,f,side,
      split0,labels,nonIncident,J,idx,ord,busy,obs,front,fly,leave,returned,accepted,selectBank,parity⟩ :=
    BStarReceiptBitOrigin.from_handoff hp C sep H N width notShort (E0 ▸ fixed) (E0 ▸ off)
  let gate := digitFrom (S.getD len fall).1 4
  let frontLead := start++issue::(preFlight++arrive::spectators)
  let lead := assembly++frontLead
  let suffix := residual++gate::(out++turn::(back++ack::after))++rest
  have tape : ((u++v)++tail)=lead++incident gate side::suffix := by
    rw [A0,split0]
    simp [lead,frontLead,suffix,gate,List.append_assoc]
  have oldReadEq : run initial lead=
      run (step (run (step (run x408 start) issue) preFlight) arrive) spectators := by
    simp [lead,frontLead,x408,BStarResetSchedule.run_append,BStarResetSchedule.run]
  have descriptor : H.descriptor.valid=true := BStarBankCapture.decode_valid H.decoded
  have same := BStarReceiptChoice.receipt_bit_fixed descriptor auth selectBank
  have receiptParity : decide (receipt.argument.toNat%2=1)=firstBit side := by
    unfold receiptChoice at same
    rw [N,Bool.true_and,Bool.true_and] at same
    rw [same]
    change f.argument.toNat % 2=(firstBit side).toNat at parity
    rw [parity]
    cases firstBit side <;> decide
  have atRead : BStarBitOneObservation.Observes gate j (run initial lead) (.out j) (incident gate side) := by
    rw [oldReadEq,E0]
    exact obs
  have seen := (BStarReceiptBitOrigin.chart_reveal_known_side hp C H initialTime lead
    gate j (Nat.le_of_lt J) idx ord side atRead)
  have without : BeforePublication hp x408 mark (remainder++rest) :=
    BStarReceiptBitNoPrior.handoff_before_publication hp C Q (E0 ▸ stable assembly)
      fiber closed sep H |> fun R=>E0.symm ▸ R
  have B0 : remainder++rest=frontLead++incident gate side::suffix := by
    rw [split0]
    simp [frontLead,suffix,gate,List.append_assoc]
  have noEarlier : BeforePublication hp (run initial lead) mark (incident gate side::suffix) := by
    intro aa m bb split
    have full : remainder++rest=(frontLead++aa)++m::bb := by
      exact B0.trans ((congrArg (frontLead++·) split).trans (List.append_assoc _ _ _).symm)
    have H' : NoPublication hp (run x408 (frontLead++aa)) m mark :=
      without (frontLead++aa) m bb full
    have rerun : run x408 (frontLead++aa)=run (run initial lead) aa := by
      simp only [x408,lead,BStarResetSchedule.run_append]
    exact rerun ▸ H' 
  let tick := count initialTime (tapeInc hp base hh initial ((u++v)++tail)) mark ((u++v)++tail).length
  have eqCount : tick=count initialTime (tapeInc hp base hh initial lead) mark lead.length := by
    unfold tick
    rw [tape]
    exact BStarReceiptKey.count_before_publication hp base initial hh initialTime lead _ mark noEarlier
  have inc : incAt hp base hh old mark=some mark := by
    let C := before (neighborHeader hh center 1)
    let L := before (neighborHeader hh center 0)
    let R := before (neighborHeader hh center 2)
    have N : pendingNeed (nativeClock (modulus r) L C R) C=true := need
    have action := (need_iff (modulus r) L C R).mp N
    rw [incAt,dif_pos hi,if_neg pub]
    change (match nativeClock (modulus r) L C R with
      | .inc _ => some mark
      | _ => none)=some mark
    rw [action.1]
  have gateMem : (gate, (1 : Fin 11))∈S := by
    have inList : S.getD j fall∈S := by
      rw [←List.getElem_eq_getD (h:=show j<S.length by rw [C.length]; omega)]
      exact List.getElem_mem _
    have sameGate : S.getD j fall=(gate,1) := idx
    exact sameGate ▸ inList
  have ownGate : BStarAcquireLiteralChain.own (oldH6 B base) hh (gate,1)=o :=
    Subtype.ext (C.entries _ gateMem).2
  have admitted : BStarRecoveredReveal.Admitted hp base initial hh lead gate := by
    refine ⟨pre,reset,(entryWord++compiler)++frontLead,?_,ownGate.symm ▸ Rcredit⟩
    simp only [lead,assembly,List.append_assoc]
  have ready : BStarRecoveredReveal.Ready hp base initial hh lead gate := by
    obtain ⟨_,_,z,raw,hf,opc,hout,harg,race⟩ := atRead
    exact ⟨⟨ord,z,raw,hf,opc,race,hout,harg⟩,admitted⟩
  have admittedAt :
      BStarPhysicalReserved.admittedRead hp base initial hh initialTime ((u++v)++tail) lead.length =
        some (mark,firstBit side) := by
    rw [tape]
    unfold BStarPhysicalReserved.admittedRead
    rw [dif_pos (by simp),List.take_append_length,List.getElem_append_right (Nat.le_refl _)]
    simp only [Nat.sub_self,List.getElem_cons_zero]
    rw [BStarRecoveredReveal.reveal_incident hp base initial hh initialTime lead gate side ready,seen.1]
    rfl
  refine ⟨lead,suffix,side,gate,o,S,len,fall,j,tape,admitted,admittedAt,C,J,idx,own,atRead,noEarlier,inc,?_,?_⟩
  · change reveal hp base hh initial (ownerAt hp base hh) initialTime lead (incident gate side)=
        some ((mark,tick),firstBit side)
    rw [eqCount]
    exact seen.2
  · have output' : visible (step old mark) mark (sites (r:=r) mark)=
        (nativeSpec r bank).2 (firstBit side) := by
      rw [←receiptParity]
      have eq : ((nativeSpec r bank).1 && decide (receipt.argument.toNat%2=1)) =
          decide (receipt.argument.toNat%2=1) := by rw [nativeNeed,Bool.true_and]
      exact eq ▸ output
    have hhSite : ∀ i,oldH6 B base i=true → WordSites (oldH6 B base) i (sites (r:=r) i) :=
      fun i hi=> (exact_sites hh i hi notShort).2.2
    have frame := BStarOperandFrame.visible_pointwise hp u v tail cuts Q I closed fiber mark
      (sep mark) (sites (r:=r)) hhSite
    funext i
    by_cases E : i=center
    · subst i
      have O : readRecord (r:=r) (step old mark) mark=
          observe ((nativeSpec r bank).2 (firstBit side)) := by
        change decodeBank r (centerView (visible (step old mark) mark
          (sites (r:=r) mark))) 1=_
        apply native_exposure_roundtrip _ hr
        · simpa [centerView] using congrArg Output.digits output'
        · simpa [centerView] using congrArg Output.hdr output'
      change readRecord (r:=r) (step old mark) mark=activate (r:=r) hh before center (firstBit side) center
      unfold activate
      rw [if_pos rfl,O]
      unfold nativeSpec
      simp only [observe_encode]
      rw [ports 0,ports 1,ports 2]
    · have K : i.val≠mark := fun e=>E (Subtype.ext e)
      have F := congrArg (fun y=>decodeBank r (centerView y) 1) (frame i.val i.property (.inl K))
      change readRecord (r:=r) (step old mark) i.val=activate (r:=r) hh before center (firstBit side) i
      rw [activate,if_neg E]
      exact F

end L4.BStarReceiptRecoveredRead
