import Leader.L4.BStarSuffixReservation

namespace L4.BStarResolvedReceipt
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
open BStarSuffixReservation BStarActualReceiptReservation BStarFenceReceiverChart BStarAcquireRailCoverage BStarEpochLift BStarPhysicalReserved BStarReceiptKey

open BStarOwnerRecoveryPass

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step B
local notation "run" => BStarResetSchedule.run step

/-- A literal NEED publication after a stop at or beyond common
recovery uses the cut's still-pending bit or the first actual suffix
reveal. In the suffix case the reservation is provably absent at this
key. The returned bit determines the exact decoded activation. -/
theorem resolved_receipt {base initial : X} (u v tail : List (Fin n))
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
    (pastCut : (u++v) <+: history) :
    let key := traceCount hp base initial hh initialTime (history++future) mark
    let reserved := reserveAtKey hp base initial hh initialTime history mark key
    let fresh := firstRaw (reveal hp base hh initial (ownerAt hp base hh) initialTime)
      (mark,key) history future
    ∃ (bit : Bool),
      (reserved=some bit ∨ (reserved=none ∧ fresh=some bit)) ∧
      (fun i : Header (oldH6 B base)=>readRecord (r:=r) (step (run initial (history++future)) mark) i.val)=
        activate (r:=r) hh (fun i=>readRecord (r:=r) (run initial (history++future)) i.val)
          ⟨mark,hi⟩ bit := by
  dsimp only
  have hr : 3≤r := by omega
  have cutLe : (u++v).length≤history.length := pastCut.length_le
  have sepAll := separated_by_inc_or_early_pub hp u v tail cuts Q I fiber closed sep offset
    coherent heads cont hr flags notShort initialTime mark
  rw [split] at sepAll
  have sepStop : ∀ (a b : Nat) (c d : Bool), a<b → b<(history++future).length →
      admittedRead hp base initial hh initialTime (history++future) a=some (mark,c) →
      admittedRead hp base initial hh initialTime (history++future) b=some (mark,d) →
      ∃ j,a≤j ∧ j<b ∧ publishes hp initial (history++future) j mark ∧
        (history.length≤j → tapeInc hp base hh initial (history++future) j=some mark) := by
    intro a b c d ab blt A D
    obtain ⟨j,aj,jb,P,E⟩ := sepAll a b c d ab blt A D
    exact ⟨j,aj,jb,P,fun h=>E (Nat.le_trans cutLe h)⟩
  have unique := suffix_position_unique hp cuts initialTime history future mark
    (traceCount hp base initial hh initialTime (history++future) mark) pastCut (by
      intro a b c d late ab blt A D
      obtain ⟨j,aj,jb,_,E⟩ := sepStop a b c d ab blt A D
      exact ⟨j,aj,jb,E (Nat.le_trans late aj)⟩)
  obtain ⟨lead,suffix,side,gate,tape,A,H,update⟩ :=
    actual_receipt_at_stop hp u v tail cuts hh sep Q I fiber closed offset coherent heads cont
      initialTime mark hi width flags notShort pub need history future split unique
  refine ⟨firstBit side,?_,update⟩
  rcases H with ⟨_,old⟩|⟨late,fresh⟩
  · exact .inl old
  · refine .inr ⟨?_,fresh⟩
    have L : lead.length<(history++future).length := by rw [tape]; simp
    apply reserve_none_of_suffix_read hp initialTime history future mark sepStop
      lead.length (firstBit side) late L A
    exact BStarIncrementLedger.count_monotone _ _ _ (Nat.le_of_lt L)

end L4.BStarResolvedReceipt
