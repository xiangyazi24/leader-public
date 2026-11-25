import Leader.L4.BStarReceiptRecoveredRead
import Leader.L4.BStarReservationJoin

namespace L4.BStarActualReceiptReservation
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
open BStarFenceReceiverChart BStarAcquireRailCoverage BStarEpochLift BStarPhysicalReserved BStarReceiptKey

open BStarOwnerRecoveryPass

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step B
local notation "run" => BStarResetSchedule.run step

/-- A publication-free witness on a literal trailing word excludes exactly
the indexed old-state publications on that part of the full tape. -/
theorem no_publish_index {initial : X} (lead gap : List (Fin n)) (i : Fin n)
    (H : BeforePublication hp (run initial lead) i gap) :
    ∀ j, lead.length ≤ j → j < (lead++gap).length →
      ¬publishes hp initial (lead++gap) j i := by
  intro j h hj pub
  obtain ⟨_,P⟩ := pub
  let k := j-lead.length
  have K : k<gap.length := by simp only [List.length_append] at hj; omega
  have G : gap=gap.take k++gap[k]::gap.drop (k+1) := by
    rw [←List.drop_eq_getElem_cons K]
    exact (List.take_append_drop k gap).symm
  have T : (lead++gap).take j=lead++gap.take k := by
    rw [List.take_append,List.take_of_length_le h]
  have E : (lead++gap)[j]=gap[k] := List.getElem_append_right h
  rw [T,E,BStarResetSchedule.run_append] at P
  exact P (H _ _ _ G)

/-- Reindex an observed suffix reveal without changing its absolute key. -/
theorem suffix_uses_first (obs : List (Fin n)→Fin n→Option (Key n×Bool)) (key : Key n)
    (history future lead suffix : List (Fin n)) (e : Fin n) (b : Bool)
    (tape : history++future=lead++e::suffix) (atOrAfter : history.length≤lead.length)
    (raw : obs lead e=some (key,b))
    (unique : ∀ a f z a' f' z' c c',
      future=a++f::z → future=a'++f'::z' →
      obs (history++a) f=some (key,c) → obs (history++a') f'=some (key,c') →
      a.length=a'.length) :
    firstRaw obs key history future=some b := by
  obtain ⟨gap,G⟩ := List.prefix_of_prefix_length_le
    (show history <+: history++future from ⟨future,rfl⟩)
    (show lead <+: history++future from ⟨e::suffix,tape.symm⟩) atOrAfter
  have F : future=gap++e::suffix := by
    apply List.append_cancel_left (as := history)
    rw [tape,←G,List.append_assoc]
  have R : obs (history++gap) e=some (key,b) := by rw [G]; exact raw
  calc
    firstRaw obs key history future = firstRaw obs key history (gap++e::suffix) :=
      congrArg (firstRaw obs key history) F
    _ = some b := firstRaw_of_unique_position obs key history gap suffix e b R
      (fun a f z c E A => unique a f z gap e suffix c b (F.trans E) F A R)

/-- The real receipt at an authenticated NEED publication comes from
the stopped reservation if its read preceded the stop. Otherwise it
uses the first matching suffix reveal, provided that suffix has no
repeated reveal of its publication key. No pre-stop key uniqueness is
required; pre-stop separation uses actual publications instead. -/
theorem actual_receipt_at_stop {base initial : X} (u v tail : List (Fin n))
    (cuts : CutFacts hp base initial u v) (hh : ∃ i,oldH6 B base i=true)
    (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (Q : X→Prop) (I : Q initial) (fiber : ∀ y,Q y→∀ i,Layout B base i=Layout B y i)
    (closed : ∀ y e,Q y→Q (step y e))
    (offset : correct (oldH6 B base) hh 5 initial)
    (coherent : ∀ x,Q x → ∀ i,oldH6 B x i=true →
      BStarLongGrant.conflict (BStarGrantReaderHistory.ports x i)=false)
    (heads : ∀ i, let g := longGeometry B (base i); (!g.axes.h6 || g.inside)=true)
    (cont : ∀ i, let g := oldPair B base i; continuation g.1 g.2=true)
    (initialTime : Fin n→Nat)
    (mark : Fin n) (hi : oldH6 B base mark=true)
    (width : 5≤r)
    (flags : ∀ i,(longGeometry B (base i)).inside=decide (oldOrdinal B base hh i<r) ∧
      (longGeometry B (base i)).last=decide (oldOrdinal B base hh i+1=r))
    (notShort : ∀ j,oldH6 B base (rightNeighbor j)=true → r≤oldOrdinal B base hh j+1)
    (pub : ¬NoPublication hp (run initial ((u++v)++tail)) mark mark)
    (need : consults (r:=r) hh
      (fun i=>readRecord (r:=r) (run initial ((u++v)++tail)) i.val) ⟨mark,hi⟩=true)
    (history future : List (Fin n)) (split : ((u++v)++tail)=history++future)
    (uniqueSuffix : ∀ a e b a' e' b' c c',
      future=a++e::b → future=a'++e'::b' →
      reveal hp base hh initial (ownerAt hp base hh) initialTime (history++a) e =
        some ((mark,traceCount hp base initial hh initialTime (history++future) mark),c) →
      reveal hp base hh initial (ownerAt hp base hh) initialTime (history++a') e' =
        some ((mark,traceCount hp base initial hh initialTime (history++future) mark),c') →
      a.length=a'.length) :
    ∃ (lead suffix : List (Fin n)) (side : Side) (gate : Fin n),
      history++future=lead++incident gate side::suffix ∧
      admittedRead hp base initial hh initialTime (history++future) lead.length =
        some (mark, firstBit side) ∧
      ((lead.length<history.length ∧
        reserveAtKey hp base initial hh initialTime history mark
          (traceCount hp base initial hh initialTime (history++future) mark)=some (firstBit side)) ∨
       (history.length≤lead.length ∧
        firstRaw (reveal hp base hh initial (ownerAt hp base hh) initialTime)
          (mark,traceCount hp base initial hh initialTime (history++future) mark)
          history future=some (firstBit side))) ∧
      (fun i : Header (oldH6 B base)=>readRecord (r:=r) (step (run initial (history++future)) mark) i.val)=
        activate (r:=r) hh (fun i=>readRecord (r:=r) (run initial (history++future)) i.val)
          ⟨mark,hi⟩ (firstBit side) := by
  obtain ⟨lead,suffix,side,gate,o,S,len,fall,j,E,_,admitted,_,_,_,_,_,quiet,_,raw,update⟩ :=
    BStarReceiptRecoveredRead.physical_need_read hp u v tail cuts hh sep Q I fiber closed
      offset initialTime mark hi width flags notShort pub need
  rw [split] at E admitted raw update
  change reveal hp base hh initial (ownerAt hp base hh) initialTime lead (incident gate side) =
    some ((mark, traceCount hp base initial hh initialTime (history++future) mark),firstBit side) at raw
  refine ⟨lead,suffix,side,gate,E,admitted,?_,update⟩
  by_cases before : lead.length<history.length
  · refine .inl ⟨before,?_⟩
    apply BStarReservationJoin.reserved_of_admitted_old_receipt hp Q I fiber (fun x hx e=>closed x e hx) sep offset
      coherent heads cont initialTime history future mark lead.length (firstBit side) before admitted
    rw [E]
    exact no_publish_index hp lead _ mark quiet
  · have bound : history.length≤lead.length := Nat.le_of_not_gt before
    refine .inr ⟨bound,?_⟩
    exact suffix_uses_first _ _ history future lead suffix (incident gate side) (firstBit side)
      E bound raw uniqueSuffix

end L4.BStarActualReceiptReservation
