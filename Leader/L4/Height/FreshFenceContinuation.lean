import Leader.L4.Height.FreshCopyReceipt
import Leader.L4.Height.FreshFenceOperand
import Leader.L4.Height.FreshAttempt
import Leader.L4.Height.AdmissionTour
import Leader.L4.BStarCopyLeftFenceHold
import Leader.L4.BStarCopyRightWrappedFenceHold
import Leader.L4.BStarGeneratedPCAncestry
import Leader.L4.BStarCopyLeftGeometryWord
import Leader.L4.BStarCopyRightWrappedReturn
import Leader.L4.BStarClearanceMobileWeak

namespace L4.Height.FreshFenceContinuation
open AllSizeProtocol BStarTrace BStarLongWork BStarLongClaims BStarLongToken
open BStarLongCommand BStarLongCommandData BStarLongPrep BStarLongPackets
open BStarLongLiteral BStarLongEvents BStarLongTransport BStarResetQuiet
open BStarLongRouting BStarSeparatorControl
open BStarH6WordChart BStarAcquireVisitOrder BStarAcquireLiteralChain BStarResetChartTouch
open BStarAcquireAnchors BStarClearanceDataChart
open BStarGeneratedOwner BStarOwnerLaunchOrigin BStarSeparatingRail
open BStarResetMarkAdapter BStarResetRailRing BStarAcquireForwardTrace
open BStarLongDoor BStarGeneratedBandScan BStarLiteralPC BStarResetControllerProgress
open BStarLongFixedRouting BStarCopyFIFO BStarCopyMarkedLedger BStarCopyFenceSaturation BStarLongFencePrefix
open BStarCopyRightStrip (addr rail)
open BStarCopyLeftDeposit (headFirst)
open BStarCopyRightMark (stripWord)
open BStarCopyLeftFence (ldRead)
open BStarCopyRightFence (rdRead)

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step (n:=n) B
local notation "run" => BStarResetSchedule.run step

def unit (op : Nat) : Payload := ⟨0,BitVec.ofNat 9 op,0,0,0⟩

def fencePort : Sheet → Fin 11
  | .ls => 6
  | .ld => 7
  | .rs => 9
  | .rd => 10

def fenceAt (a : At Sheet) : At (Fin 11) := ⟨a.side,fencePort a.occurrence⟩

private def smallGeometry (h i l : Bool) : LongGeometry :=
  ⟨⟨false,false,false,false,false,h⟩,i,l,0,false⟩

/-- Every actual data hop has a matching selected command edge on the
same pair. Its projected FENCE inspections are in the same travel
order, including the `.ls` to `.ld` and `.rs` to `.rd` seam rows. -/
theorem data_follows_fence (g : Pair LongGeometry) (rsv : List (At Sheet)) (D : DataClaim)
    (mem : D∈orderedData g rsv) (v : At Sheet) (dest : D.destination=some v) :
    link (fenceAt D.source) (fenceAt v)∈orderedCommands g ∧
    fenceSheet (geometry g D.source.side) (fencePort D.source.occurrence)=some D.source.occurrence := by
  let check (g : Pair LongGeometry) (d : DataClaim) : Bool :=
    match d.destination with
    | none => true
    | some a => (orderedCommands g).contains (link (fenceAt d.source) (fenceAt a)) &&
        (fenceSheet (geometry g d.source.side) (fencePort d.source.occurrence)==some d.source.occurrence)
  have finite (I L H J : Bool) :
      let z := (smallGeometry false I L,smallGeometry H J false)
      (dataClaims z).all (check z)=true := by
    cases I <;> cases L <;> cases H <;> cases J <;> decide +kernel
  obtain ⟨l,r⟩ := g
  let z := (smallGeometry false l.inside l.last,smallGeometry r.axes.h6 r.inside false)
  have raw : D∈dataClaims z := BStarLongFenceTopology.selected_data_raw (l,r) rsv D mem
  have old := List.all_eq_true.mp (finite l.inside l.last r.axes.h6 r.inside) D raw
  have q : check z D=true := old
  simp only [check,dest,Bool.and_eq_true,List.contains_iff_mem,beq_iff_eq] at q
  exact ⟨q.1,by cases side : D.source.side <;> cases occ : D.source.occurrence <;> simpa [geometry,side,z,smallGeometry,fencePort,fenceSheet,occ] using q.2⟩

/-- The active physical lanes inspected strictly before the current
outward FENCE chart cursor. K7 padding has no inspection. -/
def Visited (base : X) (S : List (Pos n)) (fall : Pos n) (k : Nat) (i : Fin n) (sh : Sheet) : Prop :=
  (∃ j<k,S.getD j fall=(i,fencePort sh)) ∧
    fenceSheet (longGeometry B (base i)) (fencePort sh)=some sh

/-- An old selected incoming data claim comes from precisely the
preceding FENCE chart index, using its own projected command link. -/
theorem chart_data_predecessor {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall)
    (same : ∀ i,BStarLongFixedRouting.Layout B base i=BStarLongFixedRouting.Layout B x i)
    (e : Fin n) (rsv : List (At Sheet)) (D : DataClaim) (v : At Sheet)
    (mem : D∈orderedData (oldPair B x e) rsv) (dest : D.destination=some v)
    (j : Nat) (jS : j<S.length) (atJ : S.getD j fall=address e (fenceAt v)) :
    ∃ i,i+1=j ∧ S.getD i fall=address e (fenceAt D.source) ∧
      fenceSheet (longGeometry B (base (site e D.source.side)))
        (fencePort D.source.occurrence)=some D.source.occurrence := by
  let g := oldPair B x e
  let C := link (fenceAt D.source) (fenceAt v)
  obtain ⟨selected,mapped⟩ := data_follows_fence g _ D mem v dest
  have oldSelected : C∈orderedCommands (oldPair B base e) :=
    (BStarLongFixedRouting.command_eq B base x same e).symm ▸ selected
  let u : Pos n := address e (fenceAt D.source)
  let t : Pos n := address e (fenceAt v)
  have oldEdge : Edge B base u t := ⟨e,C,fenceAt v,oldSelected,rfl,rfl,rfl⟩
  have tMem : t∈S := by
    rw [←show S.getD j fall=t from atJ,←List.getElem_eq_getD (h:=jS)]
    exact List.getElem_mem _
  have active := (BStarAcquireChainEndpoints.link_endpoints _ C (fenceAt v) oldSelected rfl).1
  have geometryOld : geometry (oldPair B base e) D.source.side=
      longGeometry B (base (site e D.source.side)) := by
    cases side : D.source.side <;> rfl
  have geometryNew : geometry g D.source.side=longGeometry B (x (site e D.source.side)) := by
    cases side : D.source.side <;> rfl
  have owner := actual_command_owner B base e C (fenceAt v) oldSelected rfl
  have own : commandOwner (oldH6 B base) u.1 u.2=o.val := owner.trans (chart.entries _ tMem).2
  have uMem : u∈S := by
    apply chart.cover u _ own
    change BStarAcquireRailCoverage.active (geometry (oldPair B base e) D.source.side)
      (fencePort D.source.occurrence)=true at active
    rw [geometryOld] at active
    exact active
  obtain ⟨i,I,L,R⟩ := chart.edge _ _ uMem oldEdge
  have atI : S.getD i fall=u := (List.getElem_eq_getD _).symm.trans L
  have atNext : S.getD (i+1) fall=t := (List.getElem_eq_getD _).symm.trans R
  have index := (List.getD_inj I jS chart.nodup).mp (atNext.trans atJ.symm)
  have ws (v : Fin n) (sh : Sheet) :
      fenceSheet (longGeometry B (base v)) (fencePort sh)=
        fenceSheet (longGeometry B (x v)) (fencePort sh) := by
    have E := congrArg (fun f : Bool×Bool×Bool=>f.2.1) (same v)
    change (longGeometry B (base v)).inside=(longGeometry B (x v)).inside at E
    cases sh <;> simp [fencePort,fenceSheet,E]
  rw [geometryNew] at mapped
  exact ⟨i,index,atI,(ws _ _).trans mapped⟩

/-- The visited portion of the actual chart is closed under all old
selected incoming claims. Remaining prep exclusions can be discharged
from the actual opcode-11 owner or the data-only strip readiness. -/
theorem chart_region_scope {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall)
    (same : ∀ i,BStarLongFixedRouting.Layout B base i=BStarLongFixedRouting.Layout B x i)
    (e : Fin n) (k : Nat) (bound : k≤len+1)
    (prep : ∀ a : At Sheet,Visited hp base S fall k (site e a.side) a.occurrence →
      a∉reserved (round (oldPair B x e) ((x e).long,(x (rightNeighbor e)).long)).prep) :
    FrozenRegion hp (Visited hp base S fall k) x e := by
  refine ⟨prep,?_⟩
  intro D mem v member dest
  obtain ⟨⟨j,J,atJ⟩,_⟩ := member
  have card := chart.length
  obtain ⟨i,index,atI,mapped⟩ := chart_data_predecessor hp chart same e _ D v mem dest
    j (by omega) atJ
  exact ⟨⟨i,by omega,atI⟩,mapped⟩

/-- The actual late owner cannot reserve any chart-inspected sheet,
including RD on a padding site. The prep exclusion follows from the
history at the old cut and does not require a future FENCE result. -/
theorem late_visited_scope {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    {w : List (Fin n)} {m : Mode}
    (G : GeneratedOwner hp base (fun j=>S.getD j fall) len x .idle w m)
    (late : 11≤pc (run x w) (S.getD 0 fall).1)
    (layout : ∀ i,Layout B base i=Layout B (run x w) i)
    (e : Fin n) (k : Nat) (bound : k≤len+1) :
    FrozenRegion hp (Visited hp base S fall k) (run x w) e := by
  have cur := BStarGeneratedTapeCuts.at_end hp G
  apply chart_region_scope hp chart layout e k bound
  intro a Ha
  obtain ⟨⟨j,J,loc⟩,_⟩ := Ha
  have lenS := chart.length
  have inside : j<S.length := by omega
  have atJ : S.getD j fall∈S := by
    rw [←List.getElem_eq_getD (h:=inside)]
    exact List.getElem_mem _
  have own := (chart.entries _ atJ).2
  rw [loc] at own
  have sameOwner : dataOwner (oldH6 B base) (site e a.side) a.occurrence =
      commandOwner (oldH6 B base) (site e a.side) (fencePort a.occurrence) := by
    cases sh : a.occurrence <;> rfl
  have owner := sameOwner.trans own
  apply no_prep_late _ _ _ _ late
  intro offer win hit
  exact BStarCopyGateAuthority.winning_prep_pc hp chart sep G cur layout e offer
    (by rwa [hit]) win

/-- The return of the unchanged unit is consumed at the real source
mark. This supplies ISSUE11 after INJECT and ISSUE12 after FENCE. -/
theorem accept_unit {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (op : Nat) (copyOp : op=10 ∨ op=11)
    {w : List (Fin n)}
    (ret : BusyOnly hp base (fun j=>S.getD j fall) len op x (.back len) w (.back 0))
    (receipt : project (fun j=>S.getD j fall) x len=.reply (unit op))
    (ack : Fin n)
    (event : Event hp (fun j=>S.getD j fall) len (run x w) ack (.busy op (.back 0)) .idle) :
    BStarNativeReceiptTape.Hit hp base (fun j=>S.getD j fall) len (run x w) ack op := by
  apply FreshCopyReceipt.ordinary hp chart sep op _ _ ret receipt ack event <;>
    rcases copyOp with rfl|rfl <;> decide

/-- Readiness at an old cut follows from the actual accepted ENABLE and
its generated continuation. The phase is either past the final INJECT
release or already at opcode 11. Only the prefix ending at this old cut
is used, so the mark whose readiness is needed has no postcondition. -/
theorem ready_after_enable {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (w9 rest : List (Fin n)) (ack e : Fin n) (m : Mode)
    (G9 : GeneratedOwner hp base (fun j=>S.getD j fall) len x .idle w9 (.busy 9 (.back 0)))
    (event : Event hp (fun j=>S.getD j fall) len (run x w9) ack (.busy 9 (.back 0)) .idle)
    (accepted : pc (step (run x w9) ack) (S.getD 0 fall).1=10)
    (G : GeneratedOwner hp base (fun j=>S.getD j fall) len x .idle (w9++ack::rest) m)
    (valid : ∀ u v,w9++ack::rest=u++v →
      (∀ j,BStarLongFixedRouting.Layout B base j=BStarLongFixedRouting.Layout B (run x u) j) ∧
      Band (run x u) (S.getD 0 fall).1)
    (phase : BStarCopyLeftReturn.ReleasePast len m ∨ 11≤pc (run x (w9++ack::rest)) (S.getD 0 fall).1)
    (width lSeam rSeam rTail : Nat) (lbase rroot rbase : Fin n)
    (L : BStarCopyLeftStrip.Strip B base lbase lSeam width) (lroot : lbase=(S.getD 0 fall).1)
    (D : BStarCopyRightRetained.Dest B base rroot width)
    (R : BStarCopyRightWrappedGeometry.WrappedStrip B base rbase rSeam rTail)
    (join : addr rbase 0=addr rroot (width-1))
    (head : dataOwner (oldH6 B base) (addr rbase 0) (rail rSeam 0)=o.val) :
    BStarCopyLeftDataSweep.DataReady hp (run x (w9++ack::rest)) lbase e lSeam width ∧
    BStarCopyRightWrappedSweep.DataReady hp (run x (w9++ack::rest)) rroot rbase e width rSeam rTail := by
  let y := run x (w9++ack::rest)
  have lGate := BStarCopyLeftGeometryWord.left_gates_word hp chart sep w9 rest ack m G9 event
    accepted G valid lbase lSeam width L lroot rest [] (by simp)
  have rGate := BStarCopyRightWrappedGates.right_gates_word hp chart sep w9 rest ack m G9 event
    accepted G valid rroot rbase width rSeam rTail D R join head rest [] (by simp)
  rcases phase with past|late
  · have rPast : BStarCopyRightReturn.ReleasePast len m := past
    exact ⟨BStarCopyLeftReturn.ready_release_past hp chart sep _ m G past _ e _ _ L lroot lGate,
      BStarCopyRightWrappedReturn.ready_release_past hp chart sep _ m G rPast _ _ e _ _ _ D R join head rGate⟩
  · have now := BStarGeneratedTapeCuts.at_end hp G
    have same := (valid (w9++ack::rest) [] (List.append_nil _).symm).1
    have noPrep (slot : At Sheet)
        (own : dataOwner (oldH6 B base) (site e slot.side) slot.occurrence=o.val) :
        slot∉reserved (round (oldPair B y e) ((y e).long,(y (rightNeighbor e)).long)).prep := by
      apply no_prep_late _ _ _ _ late
      intro offer win E
      exact BStarCopyGateAuthority.winning_prep_pc hp chart sep G now same e offer (by rwa [E]) win
    have ownLeft := BStarCopyLeftReadyWord.all_owner hp chart lbase lSeam width L lroot
    have ownRD : dataOwner (oldH6 B base) (addr rroot (width-1)) .rd=o.val := by
      rwa [show rail rSeam 0=.rd from if_pos R.seam_pos,join] at head
    refine ⟨⟨lGate.strip,lGate.ld,lGate.ls,?_,?_⟩,⟨rGate.dest,rGate.strip,rGate.rd,rGate.up,?_,?_⟩⟩
    · intro j J side loc
      apply noPrep ⟨side,.ld⟩
      change dataOwner _ (site e side) .ld=o.val
      rw [loc,BStarCopyLeftFenceHold.address_add]
      have own := ownLeft (lSeam+j) (by omega)
      rwa [BStarCopyLeftStrip.rail,if_neg (by omega : ¬lSeam+j<lSeam)] at own
    · intro j J side loc
      apply noPrep ⟨side,.ls⟩
      change dataOwner _ (site e side) .ls=o.val
      rw [loc]
      have own := ownLeft j (by omega)
      rwa [BStarCopyLeftStrip.rail,if_pos J] at own
    · intro j J side loc
      apply noPrep ⟨side,.rd⟩
      change dataOwner _ (site e side) .rd=o.val
      rw [loc]
      exact (BStarCopyRightReady.dest_owner hp rroot width D j J).trans ownRD
    · intro j _ J side loc
      apply noPrep ⟨side,rail rSeam j⟩
      change dataOwner _ (site e side) (rail rSeam j)=o.val
      rw [loc]
      exact (BStarCopyRightWrappedReleaseClass.strip_same_owner R j J).trans head

private theorem fence_bound (g : LongGeometry) (k : Fin 11) :
    BStarLongCommand.bind g k (.forward (unit 11))=.forward (unit 11) := by
  simp [BStarLongCommand.bind,unit,gate,admit,bitOp,acquire,forwardWidth,
    arithKind,copyLoad,stageOp,sealOp,commitOp,cropped,low]

private theorem fence_carried (g : Pair LongGeometry) (raw : Pair (BitVec LW)) (C : CommandClaim) :
    BStarClearanceForward.carried g raw C (unit 11)=unit 11 := by
  have noNode : BStarLongArithmetic.nodeOf 11=none := by decide
  simp [unit,BStarClearanceForward.carried,BStarLongArithmetic.visit,noNode,
    BStarLongOutgoing.execute,BStarLongOutgoing.hold,stageOp,sealOp,commitOp]

private theorem fence_classify (g : Pair LongGeometry) (raw : Pair (BitVec LW))
    (C : CommandClaim) (nonDoor : C.kind≠.door) (old : readK raw C.source=.forward (unit 11)) :
    classifyOld g raw C=.advance (unit 11) := by
  change classify C _ (bound g (readK raw) C.source) _=.advance (unit 11)
  have boundOld : bound g (readK raw) C.source=.forward (unit 11) := by
    unfold bound
    rw [old]
    exact fence_bound _ _
  rw [boundOld]
  simp [unit,classify,nonDoor,depart,gate,admit,bitOp]

private theorem marked_fence_offer (g : Pair LongGeometry) (raw : Pair (BitVec LW))
    (C : CommandClaim) (mem : C∈orderedCommands g) (nonDoor : C.kind≠.door)
    (old : readK raw C.source=.forward (unit 11))
    (guard : checkFence g (view raw) C.source (unit 11)=.advance) :
    (C,.advance (unit 11))∈actualOffers g raw := by
  have eq := fence_classify g raw C nonDoor old
  have gatedC : (C,.advance (unit 11))∈gated g raw := by
    apply (gated_mem g raw C _).mpr
    refine ⟨mem,?_⟩
    unfold gatedAt
    rw [eq]
    simp only [checkOffer,guard]
  have noCancel : C.source∉(round g raw).faults := by
    intro fail
    change C.source∈prepFaults (view raw) (round g raw).prep at fail
    simp only [prepFaults,BStarResetNoFault.arb_no_losers g raw,List.map_nil,List.nil_append] at fail
    obtain ⟨a,chosen,origin⟩ := List.mem_map.mp fail
    obtain ⟨D,f,_,Q,_,bad,_,src,_,_⟩ :=
      BStarCopyOwnedFrozen.winner_origin g raw a (List.mem_filter.mp chosen).1
    have hD := (gated_mem g raw D _).mp Q
    have hC := (gated_mem g raw C _).mp gatedC
    have same := BStarResetNoFault.origin_unique g D C hD.1 hC.1 (src.symm.trans origin)
    subst D
    have equal := BStarLongCommand.Offer.advance.inj (hD.2.trans hC.2.symm)
    subst f
    simp [unit,prepOf] at bad
  have stays : cancel (round g raw).faults (C,.advance (unit 11))=(C,.advance (unit 11)) := by
    change (if C.source∈(round g raw).faults then
      (C,BStarLongCommand.Offer.advance failedPayload)
      else (C,BStarLongCommand.Offer.advance (unit 11)))=_
    exact if_neg noCancel
  have row : (C,.advance (unit 11))∈(round g raw).offered :=
    List.mem_map.mpr ⟨_,gatedC,stays⟩
  unfold actualOffers BStarLongGrant.run
  apply List.mem_map.mpr
  refine ⟨_,row,?_⟩
  by_cases small : C.source.occurrence.val<3 <;> simp [BStarLongGrant.update,unit,acquire,small]

/-- The prospective K10 guard physically turns the actual old unit.
The selected terminal and the old operand are used on the same mark. -/
theorem guarded_turn {x : X} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (turn : Fin n) (sep : turn≠rightNeighbor turn)
    (actual : onTerminal hp x turn (fun j=>S.getD j fall) len)
    (front : project (fun j=>S.getD j fall) x len=.forward (unit 11))
    (guard : ∀ C : CommandClaim, C∈orderedCommands (oldPair B x turn) →
      C.kind=.terminal → C.destination=none →
      S.getD len fall=address turn C.source →
      checkFence (oldPair B x turn) (view ((x turn).long,(x (rightNeighbor turn)).long))
        C.source (unit 11)=.advance) :
    project (fun j=>S.getD j fall) (step x turn) len=.reply (unit 11) := by
  obtain ⟨C,mem,kind,dest,port,loc⟩ := actual
  let g := oldPair B x turn
  let raw : Pair (BitVec LW) := ((x turn).long,(x (rightNeighbor turn)).long)
  have old : readK raw C.source=.forward (unit 11) :=
    (old_read x turn C.source).trans ((congrArg (atCursor x) loc).symm.trans front)
  have selected := marked_fence_offer g raw C mem (by rw [kind]; decide) old (guard C mem kind dest loc)
  have effect := terminal_finish g raw C (unit 11) dest selected
  have carries := fence_carried g raw C
  have f : readK (patchPair (longWork g raw) raw) C.source=.reply (unit 11) := by
    have H := (congrArg BStarLongToken.decode effect).trans (decode_encode _)
    change readK (patchPair (longWork g raw) raw) C.source=
      finish (BStarClearanceForward.carried g raw C (unit 11)) at H
    rw [carries] at H
    exact H.trans (by decide)
  have joined := BStarAcquireReturn.joined_reads k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
    (x turn,x (rightNeighbor turn)) C.source (by intro _ zero; omega)
  exact (congrArg (atCursor (step x turn)) loc).trans ((new_read B x turn sep C.source).symm.trans (joined.trans f))

private theorem fence_link (x : X) (e : Fin n) (sep : e≠rightNeighbor e)
    (C : CommandClaim) (v : AtK) (mem : C∈orderedCommands (oldPair B x e))
    (dest : C.destination=some v) (old : readK ((x e).long,(x (rightNeighbor e)).long) C.source=.forward (unit 11))
    (guard : checkFence (oldPair B x e) (view ((x e).long,(x (rightNeighbor e)).long))
      C.source (unit 11)=.advance) :
    atCursor (step x e) (address e v)=.forward (unit 11) := by
  let g := oldPair B x e
  let raw : Pair (BitVec LW) := ((x e).long,(x (rightNeighbor e)).long)
  have shape := BStarAcquireReturn.link_shape g C v mem dest
  have nonDoor : C.kind≠.door := by rw [shape.2.1]; decide
  have offer := marked_fence_offer g raw C mem nonDoor old guard
  obtain ⟨_,landed⟩ := BStarClearanceForward.move_lands g raw C (unit 11) v dest offer (Ne.symm shape.1)
  have arriveSame : arrive (geometry g v.side) v.occurrence (BStarClearanceForward.carried g raw C (unit 11))=
      .forward (unit 11) := by
    rw [fence_carried]
    simp [unit,arrive,gate,admit,bitOp]
  rw [arriveSame] at landed
  have saved : readK (patchPair (longWork g raw) raw) v=.forward (unit 11) :=
    (congrArg decode landed).trans (decode_encode _)
  have joined := BStarAcquireReturn.joined_reads k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
    (x e,x (rightNeighbor e)) v (fun _ k=>.inl (BStarAcquireJoinedHop.k0_dest g C v mem dest k).2)
  exact (new_read B x e sep v).symm.trans (joined.trans saved)

private theorem held_route (g : Pair LongGeometry) (raw : Pair (BitVec LW)) (a : AtK)
    (old : readK raw a=.forward (unit 11)) (keep : a∉discarded g)
    (mid : avoids a (middle g raw)) : avoids a (routing g raw) := by
  have boundOld : bound g (readK raw) a=.forward (unit 11) := by
    unfold bound
    rw [old]
    exact fence_bound _ _
  have quiet : observe a (geometry g a.side) (unit 11)=none := by
    simp [unit,observe,gate,admit,bitOp]
  rw [routing_parts]
  intro w hw eq
  obtain ⟨q,t⟩ := w
  change q=a at eq
  subst q
  rcases List.mem_append.mp hw with H|H
  · rcases List.mem_append.mp H with H|H
    · rcases List.mem_append.mp H with H|H
      · obtain ⟨q,_,Q⟩ := List.mem_filterMap.mp H
        dsimp only at Q
        split at Q
        · have E := congrArg Prod.fst (Option.some.inj Q)
          change q=a at E
          subst q
          rename_i faulty
          rw [boundOld] at faulty
          simp [isFault,unit] at faulty
        · contradiction
      · obtain ⟨q,h,Q⟩ := List.mem_map.mp H
        have E := congrArg Prod.fst Q
        change q=a at E
        subst q
        exact keep h
    · exact mid _ H rfl
  · obtain ⟨q,_,Q⟩ := List.mem_filterMap.mp H
    split at Q
    · contradiction
    · split at Q
      all_goals try contradiction
      rename_i f hf
      cases E : observe q (geometry g q.side) f with
      | none => simp [E] at Q
      | some v =>
        rw [E] at Q
        have S := congrArg Prod.fst (Option.some.inj Q)
        change q=a at S
        subst q
        rw [boundOld] at hf
        cases hf
        rw [quiet] at E
        contradiction

/-- An actual occupied-lane FENCE hold on the pointed outgoing edge
preserves the healthy bytes, even with independent traffic on the pair. -/
theorem fence_holds {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (e : Fin n) (sep : e≠rightNeighbor e) (k : Nat)
    (I : Current hp base (fun t=>S.getD t fall) len x (.busy 11 (.out k)))
    (front : project (fun t=>S.getD t fall) x k=.forward (unit 11))
    (C : CommandClaim) (mem : C∈orderedCommands (oldPair B x e)) (nonDoor : C.kind≠.door)
    (loc : S.getD k fall=address e C.source)
    (guard : checkFence (oldPair B x e) (view ((x e).long,(x (rightNeighbor e)).long))
      C.source (unit 11)=.hold) :
    project (fun t=>S.getD t fall) (step x e) k=.forward (unit 11) := by
  let g := oldPair B x e
  let raw : Pair (BitVec LW) := ((x e).long,(x (rightNeighbor e)).long)
  have old : readK raw C.source=.forward (unit 11) :=
    (old_read x e C.source).trans ((congrArg (atCursor x) loc).symm.trans front)
  have gates : gatedAt g raw C=.hold := by
    unfold gatedAt
    rw [fence_classify g raw C nonDoor old]
    have guardEq : checkFence g (view raw) C.source (unit 11)=.hold := guard
    simp [checkOffer,guardEq]
  obtain ⟨z,actual,eq⟩ : ∃ z : CmdOffer,z∈actualOffers g raw ∧ z.1=C := by
    apply List.mem_map.mp
    rwa [actualOffers_claims]
  have action := BStarAcquireNonRouting.actual_hold g raw z actual (by rwa [eq])
  have held : (C,.hold)∈actualOffers g raw := by
    cases z
    simp_all
  have frames := BStarSeparatorQuiet.frames_any hp chart I.1.1 e (.out k)
    (by intro eq; cases eq) I.2.1 I.1.2.1 I.1.2.2.1
  obtain ⟨keep,safe⟩ := frames.safe k I.2.1.1 C.source loc
  have mid := BStarResetQuietTable.hold_avoids g raw C held C.source (by simp [Claim.slots])
  have joined := BStarAcquireHistorySample.joined_silent k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
    (x e,x (rightNeighbor e)) C.source safe (held_route g raw C.source old keep mid)
  exact (congrArg (atCursor (step x e)) loc).trans ((new_read B x e sep C.source).symm.trans (joined.trans old))

def NoFenceFault (x : X) (e : Fin n) (a : Pos n) : Prop :=
  ∀ C : CommandClaim,C∈orderedCommands (oldPair B x e) → a=address e C.source →
    checkFence (oldPair B x e) (view ((x e).long,(x (rightNeighbor e)).long))
      C.source (unit 11)≠.fault

/-- This is the exact old-byte condition for a mapped inspection to
avoid fault. At an occupied slot the retained operand is unsampled. -/
theorem mapped_guard_nofault (g : Pair LongGeometry) (old : At Sheet→Lane)
    (a : AtK) (sh : Sheet)
    (mapped : fenceSheet (geometry g a.side) a.occurrence=some sh) :
    let s : At Sheet := ⟨a.side,sh⟩
    checkFence g old a (unit 11)≠.fault ↔
      (old s).gate=true ∧ (old s).error=false ∧
        ((old s).mobile≠.empty ∨ BStarLongPackets.retains g s=false ∨ validPayload (old s).retained=true) := by
  dsimp only
  simp only [checkFence,unit,mapped]
  change fence (old ⟨a.side,sh⟩) (BStarLongPackets.retains g ⟨a.side,sh⟩)≠.fault ↔ _
  let s : At Sheet := ⟨a.side,sh⟩
  change fence (old s) (BStarLongPackets.retains g s)≠.fault ↔ _
  cases G : (old s).gate <;> cases E : (old s).error <;>
    cases R : BStarLongPackets.retains g s <;> cases V : validPayload (old s).retained <;>
    by_cases M : (old s).mobile=.empty <;> simp_all [fence,s]

/-- For a retaining inspection the actual earlier physical drain,
compatible old ledger and clean gate force a genuine advance or hold,
before anything can depend on a future FENCE success. -/
theorem retaining_guard_nofault {T : Type} (digits : T→BitVec 36)
    {plan : List T} {s : Ledger T} (ledger : Prefix plan s)
    (emitted : s.release.pending=[]) (boundary : OrderedBoundary s [])
    (j : Nat) (bound : j<plan.length) (earlier : ∀ k,k<j → (s.cells k).mobile=none)
    (g : Pair LongGeometry) (old : At Sheet→Lane) (a : AtK) (sh : Sheet)
    (mapped : fenceSheet (geometry g a.side) a.occurrence=some sh)
    (compatible : Compatible digits (s.cells j) (old ⟨a.side,sh⟩))
    (opened : (old ⟨a.side,sh⟩).gate=true) (clean : (old ⟨a.side,sh⟩).error=false) :
    checkFence g old a (unit 11)≠.fault := by
  obtain ⟨_,tag,label⟩ := FreshFenceOperand.inspections_receive ledger emitted boundary j bound earlier
  have payload : (old ⟨a.side,sh⟩).retained=.data (digits tag) := by
    rw [compatible.2,label]; rfl
  apply (mapped_guard_nofault g old a sh mapped).mpr
  exact ⟨opened,clean,.inr (.inr (by rw [payload]; rfl))⟩

private theorem fence_advance {slots : Nat→Pos n} {x : X} {e : Fin n} {len k j : Nat}
    (E : Event hp slots len x e (.busy 11 (.out k)) (.busy 11 (.out j))) :
    Advance len (.out k) (.out j) := by
  cases E with
  | transit _ _ _ _ seen =>
    cases seen with
    | cons _ _ A _ rest => cases rest; exact A

/-- Carry the exact healthy unit through arbitrary original outward
marks. A selected guard hold physically parks it. A selected advance
carries it unchanged. Marks elsewhere preserve it through the checked
quiet-row lemma. -/
theorem guarded_busy_outward {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    {z d : Cursor} {w : List (Fin n)}
    (P : BusyOnly hp base (fun j=>S.getD j fall) len 11 x z w d) :
    ∀ k l,z=.out k → d=.out l →
      project (fun j=>S.getD j fall) x k=.forward (unit 11) →
      (∀ a e b,w=a++e::b → ∀ j,
        Current hp base (fun t=>S.getD t fall) len (run x a) (.busy 11 (.out j)) →
        NoFenceFault hp (run x a) e (S.getD j fall)) →
      project (fun j=>S.getD j fall) (run x w) l=.forward (unit 11) := by
  induction P with
  | nil _ =>
    intro k l K L F _
    have E := Cursor.out.inj (K.symm.trans L)
    subst l
    exact F
  | @cons x z d finish e w I E tail ih =>
    intro k l K L F good
    subst z
    obtain ⟨j,J⟩ := BStarAcquireHistorySample.busy_no_back_to_out hp tail ⟨l,L⟩
    subst d
    let slots := fun t=>S.getD t fall
    let g := oldPair B x e
    let raw : Pair (BitVec LW) := ((x e).long,(x (rightNeighbor e)).long)
    have later := fun a b c W=>good (e::a) b c (congrArg (List.cons e) W)
    have new := busy_start hp tail
    have unique : ∀ i≤len,anyTag.F (project slots (step x e) i)↔i=j :=
      BStarOwnerControlHistory.pointed_unique_forward _ _ _ new.2.1 new.2.2
    have safe : NoFenceFault hp x e (slots k) := good [] e w rfl k I
    have stay (held : project slots (step x e) k=.forward (unit 11)) :=
      ih k l (congrArg Cursor.out ((unique k I.2.1.1).mp ⟨_,held⟩).symm) L held later
    by_cases link : linkAt hp x e slots len k
    · obtain ⟨bound,C,v,mem,dest,source,target⟩ := link
      have kind := (BStarAcquireReturn.link_shape g C v mem dest).2.1
      have nonDoor : C.kind≠.door := by rw [kind]; decide
      have old : readK raw C.source=.forward (unit 11) :=
        (old_read x e C.source).trans ((congrArg (atCursor x) source).symm.trans F)
      cases check : checkFence g (view raw) C.source (unit 11) with
      | fault => exact (safe C mem source check).elim
      | hold => exact stay (fence_holds hp chart e (sep e) k I F C mem nonDoor source check)
      | advance =>
        have moved : project slots (step x e) (k+1)=.forward (unit 11) :=
          (congrArg (atCursor (step x e)) target).trans (fence_link hp x e (sep e) C v mem dest old check)
        have next := (unique (k+1) (by omega)).mp ⟨_,moved⟩
        exact ih (k+1) l (congrArg Cursor.out next.symm) L moved later
    · by_cases terminal : k=len ∧ onTerminal hp x e slots len
      · obtain ⟨eq,T⟩ := terminal
        subst k
        obtain ⟨C,mem,kind,dest,port,source⟩ := T
        have nonDoor : C.kind≠.door := by rw [kind]; decide
        cases check : checkFence g (view raw) C.source (unit 11) with
        | fault => exact (safe C mem source check).elim
        | hold => exact stay (fence_holds hp chart e (sep e) len I F C mem nonDoor source check)
        | advance =>
          have J : j=len := by
            have J := new.2.1.1
            have A := fence_advance hp E
            cases A <;> omega
          have receipt := guarded_turn hp e (sep e) ⟨C,mem,kind,dest,port,source⟩ F (by
            intro D dmem _ _ loc
            have K := address_inj e (sep e) (loc.symm.trans source)
            have same := BStarAcquireIncidence.same_claim g D C D.source dmem mem
              (by simp [Claim.slots]) (by simp [Claim.slots,K])
            subst D
            exact check)
          obtain ⟨p,P⟩ := new.2.1.2.1
          rw [J] at P
          exact Token.noConfusion (receipt.symm.trans P)
      · have frame := AdmissionTour.silent hp chart e (sep e) 11 k I.1 I.2.1 (unit 11) F rfl
          (fence_bound _ _) (by intro side; simp [unit,observe,gate,admit,bitOp])
          link (fun atEnd T=>terminal ⟨atEnd,T⟩)
        exact stay frame

/-- The real ISSUE11 launch installs the unit on the same generated
flight. Terminal health follows from the old pointed guard checks,
without reading a subsequent reply. -/
theorem terminal_fence_unit {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    {w : List (Fin n)}
    (G : GeneratedOwner hp base (fun j=>S.getD j fall) len x .idle w (.busy 11 (.out len)))
    (good : ∀ a e b,w=a++e::b → ∀ j,
      Current hp base (fun t=>S.getD t fall) len (run x a) (.busy 11 (.out j)) →
      NoFenceFault hp (run x a) e (S.getD j fall)) :
    project (fun j=>S.getD j fall) (run x w) len=.forward (unit 11) := by
  obtain ⟨pre,tour,launch,W,_,launched,op,P⟩ := from_idle hp G
  let old := run x pre
  let start := step old launch
  let root := (S.getD 0 fall).1
  have addr0 := (BStarResetChartService.root_header hp chart (busy_start hp P).1.1).2
  have initial : project (fun j=>S.getD j fall) start 0=.forward (unit 11) := by
    obtain ⟨_,a,arg,snap⟩ := launched
    have C : (ctrlOp.read (old root).long).toNat=11 := op
    change BStarLongDoor.initial (ctrlOp.read (old root).long).toNat (old root).long=some a at arg
    rw [C] at arg
    have A : a=0 := (Option.some.inj (show some 0=some a from arg)).symm
    subst a
    have point := congrArg (fun q : (Token×BitVec 2)×BitVec 9=>q.1.1) snap
    change atSite (start root).long 0=forward (ctrlOp.read (old root).long).toNat 0 at point
    rw [C] at point
    change atSite (start root).long (S.getD 0 fall).2=.forward (unit 11)
    rw [addr0]
    exact point
  have guardOnTour (a : List (Fin n)) (e : Fin n) (b : List (Fin n)) (E : tour=a++e::b)
      (j : Nat) (I : Current hp base (fun t=>S.getD t fall) len (run start a) (.busy 11 (.out j))) :
      NoFenceFault hp (run start a) e (S.getD j fall) := by
    have split : w=(pre++launch::a)++e::b := by rw [W,E,List.append_assoc,List.cons_append]
    have replay : run x (pre++launch::a)=run start a := by
      rw [BStarResetSchedule.run_append]; rfl
    have H := good (pre++launch::a) e b split j (replay.symm ▸ I)
    rwa [replay] at H
  have F := guarded_busy_outward hp chart sep P 0 len rfl rfl initial guardOnTour
  rw [W,BStarResetSchedule.run_append]
  exact F

theorem left_empty_labels {T : Type} (digits : T→BitVec 36) (x : X)
    (a : Fin n) (seam : Nat) (labels : Nat→Option T)
    (matchUp : BStarCopyLeftMark.UpstreamMatches digits x a seam labels)
    (empty : ∀ j<seam,(BStarCopyLeftMark.sample x a seam j).mobile=.empty) :
    headFirst seam labels=[] := by
  have H : BStarCopyLeftMark.upstreamWord seam labels=[] := by
    unfold BStarCopyLeftMark.upstreamWord
    apply List.flatMap_eq_nil_iff.mpr
    intro j mem
    have J := List.mem_range.mp mem
    have Q := (empty j J).symm.trans (matchUp j J)
    cases h : labels j with
    | none => rfl
    | some tag => rw [h] at Q; contradiction
  simp [headFirst,H]

theorem right_empty_labels {T : Type} (digits : T→BitVec 36) (x : X)
    (a : Fin n) (seam tail : Nat) (labels : Nat→Option T)
    (matchUp : BStarCopyRightMark.MobileMatches digits x a seam tail labels)
    (empty : ∀ j,0<j → j≤tail →
      (readLane (Sheet.index (rail seam j)) (x (addr a j)).long).mobile=.empty) :
    stripWord tail labels=[] := by
  unfold stripWord
  apply List.flatMap_eq_nil_iff.mpr
  intro j mem
  have J := List.mem_range'_1.mp mem
  have jp : 0<j := by omega
  have jt : j≤tail := by omega
  have Q := (empty j jp jt).symm.trans (matchUp j jp jt)
  cases h : labels j with
  | none => rfl
  | some tag => rw [h] at Q; contradiction

theorem right_image {T : Type} (digits : T→BitVec 36) (x : X)
    (root : Fin n) (width : Nat) (s : Ledger T)
    (M : BStarCopyRightRetained.RetainedMatches digits x root width s) :
    ∀ j,j<width → Compatible digits (s.cells j) (rdRead x root width j) := by
  intro j J
  have Q := M (width-1-j) (by omega)
  rw [show width-1-(width-1-j)=j by omega] at Q
  exact Q

private theorem encoded_good {T : Type} (digits : T→BitVec 36) (tag : Option T) :
    (encode digits tag).isBad=false := by
  cases tag <;> rfl

private theorem left_rd_error_frame (g : Pair LongGeometry) (raw : Pair (BitVec LW))
    (prep : BStarLongClaims.L .rd∉reserved (round g raw).prep)
    (donor : ∀ C∈orderedData g (reserved (round g raw).prep),
      C.destination=some (BStarLongClaims.L .rd) → (view raw C.source).mobile.isBad=false)
    (retained : (view raw (BStarLongClaims.L .rd)).retained.isBad=false)
    (clean : (view raw (BStarLongClaims.L .rd)).error=false) :
    (BStarCopyUpstreamCredit.post g raw (BStarLongClaims.L .rd)).error=false := by
  let v := BStarLongClaims.L Sheet.rd
  change (BStarCopyUpstreamCredit.post g raw v).error=false
  by_cases incoming : ∃ C∈orderedData g (reserved (round g raw).prep), C.destination=some v
  · obtain ⟨C,sel,loc⟩ := incoming
    have rawC := BStarLongFenceTopology.selected_data_raw _ _ _ sel
    obtain ⟨kind,ne⟩ : C.kind=.hop ∧ C.source≠v := by
      rcases (BStarCopyRightStrip.raw_rd_receive g C loc).mp rawC with ⟨_,J⟩|⟨_,_,J⟩ <;>
        rw [J] <;> exact ⟨rfl,by decide⟩
    have frame := BStarLongCopyFence.receiver_exact g raw C.source v C rfl loc kind sel ne
    change BStarCopyUpstreamCredit.post g raw v=_ at frame
    rw [frame]
    have good := donor C sel loc
    have was : (view raw v).error=false := clean
    have held : (view raw v).retained.isBad=false := retained
    unfold hopEffects
    split <;> try simp_all [typedLeaves]
    split <;> try simp_all
    split <;> try simp_all
    cases keep : BStarLongPackets.retains g v <;>
      simp_all [Leaf.put]
  · rw [BStarClearanceMobileWeak.quiet_lane g raw v prep]
    · exact clean
    · intro C sel H
      have noSource := (BStarCopyRightStrip.no_left_send g C
        (BStarLongFenceTopology.selected_data_raw _ _ _ sel)).1
      cases D : C.destination with
      | none => exact noSource (by simpa [Claim.slots,D,eq_comm] using H)
      | some dst =>
        have J : v=C.source ∨ v=dst := by simpa [Claim.slots,D] using H
        exact J.elim (fun S=>noSource S.symm) (fun S=>incoming ⟨C,sel,D.trans (congrArg some S.symm)⟩)

/-- The actual right terminal cannot newly acquire an error on a
data-only mark. END reads the empty final mobile. Its other incident
edge can only receive a label encoding, with valid old retained bytes. -/
theorem right_terminal_clean_mark {T : Type} (digits : T→BitVec 36)
    (x : X) (root base e : Fin n) (width seam tail : Nat)
    (join : addr base 0=addr root (width-1)) (sep : e≠rightNeighbor e)
    (plan : List T) (size : plan.length=width) (s : Ledger T) (labels : Nat→Option T)
    (P : OrderedPrefix plan s (stripWord tail labels))
    (image : BStarCopyRightRetained.RetainedMatches digits x root width s)
    (upstream : BStarCopyRightMark.MobileMatches digits x base seam tail labels)
    (ready : BStarCopyRightWrappedSweep.DataReady hp x root base e width seam tail)
    (clean : (readLane (Sheet.index .rd) (x root).long).error=false) :
    (readLane (Sheet.index .rd) (step x e root).long).error=false := by
  let g := oldPair B x e
  let raw : Pair (BitVec LW) := ((x e).long,(x (rightNeighbor e)).long)
  let v := BStarLongClaims.L Sheet.rd
  have zero : addr root 0=root := Fin.ext (Nat.mod_eq_of_lt root.isLt)
  have pos := ready.dest.pos
  by_cases E : e=root
  · have prep : v∉reserved (round g raw).prep := ready.rdPrep 0 pos .left (by rw [zero]; exact E)
    have readV : view raw v=readLane (Sheet.index .rd) (x root).long := by
      rw [BStarCopyRightMark.old_access]
      change (readLane (Sheet.index .rd) (x e).long)=_
      rw [E]
    have oldRet := (image 0 pos).2
    rw [zero] at oldRet
    have safeRet : (view raw v).retained.isBad=false := by
      rw [readV,oldRet]; exact encoded_good digits _
    have safe (C : DataClaim) (sel : C∈orderedData g (reserved (round g raw).prep))
        (loc : C.destination=some v) : (view raw C.source).mobile.isBad=false := by
      have rawC := BStarLongFenceTopology.selected_data_raw _ _ _ sel
      by_cases large : 1<width
      · have next : rightNeighbor e=addr root 1 := by
          rw [BStarCopyRightStrip.addr_next,zero,E]
        have outside : g.2.axes.h6=false := by
          change oldH6 B x (rightNeighbor e)=false
          rw [next]; exact ready.dest.body 1 (by decide) large
        have src := (BStarCopyRightStrip.raw_rd_receive g C loc).mp rawC
        have only : C=hop (BStarLongClaims.R .rd) v := by
          rcases src with ⟨_,H⟩|⟨H,_⟩
          · exact H
          · rw [outside] at H; contradiction
        rw [only,BStarCopyRightMark.old_access]
        change (readLane (Sheet.index .rd) (x (rightNeighbor e)).long).mobile.isBad=false
        rw [next,(image 1 large).1]
        exact encoded_good digits _
      · have w : width-1=0 := by omega
        have localBase : e=addr base 0 := by rw [join,w,zero,E]
        have tailPos : 0<tail := Nat.lt_of_lt_of_le ready.strip.seam_pos ready.strip.seam_le_tail
        have sheet : rail seam 0=.rd := if_pos ready.strip.seam_pos
        have loc' : C.destination=some (BStarLongClaims.L (rail seam 0)) := by rw [sheet]; exact loc
        have rawC' : C∈dataClaims (oldPair B x (addr base 0)) := localBase ▸ rawC
        have only := (BStarCopyRightWrappedGeometry.wrapped_raw_incoming ready.strip 0 tailPos C loc').mp rawC'
        rw [only,BStarCopyRightMark.old_access]
        change (readLane (Sheet.index (rail seam 1)) (x (rightNeighbor e)).long).mobile.isBad=false
        rw [localBase,←BStarCopyRightStrip.addr_next,upstream 1 (by decide) (by omega)]
        exact encoded_good digits _
    have patchClean := left_rd_error_frame g raw prep safe safeRet (by rwa [readV])
    have joined := BStarClearanceMobileJoined.joined_view k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
      (x e,x (rightNeighbor e))
    have F := congrFun joined v
    change view (Pair.map LargeSite.long (largePair B (x e,x (rightNeighbor e)))) v=
      BStarCopyUpstreamCredit.post g raw v at F
    rw [BStarCopyRightMark.new_access hp x e v sep] at F
    change readLane (Sheet.index .rd) (step x e e).long=BStarCopyUpstreamCredit.post g raw v at F
    rw [←E,F]
    exact patchClean
  · by_cases R : root=rightNeighbor e
    · have right : rightNeighbor e=addr root 0 := by rw [zero,←R]
      have keep := BStarCopyRightRetained.retained_header_frame hp digits x root e width ready.dest
        s plan (stripWord tail labels) size P image right sep (ready.rdPrep 0 pos .right right)
      rw [zero] at keep
      rwa [keep]
    · rwa [show step x e root=x root from by simp [AllSizeS1Geometry.step,Ne.symm E,R]]

/-- Same-word preservation of the right terminal error bit while the
ordered ledger continues to track all actual data labels. -/
theorem right_terminal_clean_word {T : Type} (digits : T→BitVec 36)
    (x : X) (w : List (Fin n)) (root base : Fin n) (width seam tail : Nat)
    (join : addr base 0=addr root (width-1)) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (plan : List T) (size : plan.length=width) (s : Ledger T) (labels : Nat→Option T)
    (P : OrderedPrefix plan s (stripWord tail labels))
    (image : BStarCopyRightRetained.RetainedMatches digits x root width s)
    (upstream : BStarCopyRightMark.MobileMatches digits x base seam tail labels)
    (ready : ∀ a e b,w=a++e::b → BStarCopyRightWrappedSweep.DataReady hp (run x a) root base e width seam tail)
    (clean : (readLane (Sheet.index .rd) (x root).long).error=false) :
    (readLane (Sheet.index .rd) (run x w root).long).error=false := by
  induction w generalizing x s labels with
  | nil => exact clean
  | cons e w ih =>
    have D := ready [] e w rfl
    have C := right_terminal_clean_mark hp digits x root base e width seam tail join (sep e) plan size
      s labels P image upstream D clean
    obtain ⟨t,label,_,Q,I,U⟩ := BStarCopyRightWrappedSweep.data_mark hp digits x root base e width seam tail
      D.dest D.strip join (sep e) s plan size labels P image upstream D.rdGate D.upGate D.rdPrep D.upPrep
    exact ih (step x e) t label Q I U (fun a b c H=>ready (e::a) b c (congrArg (List.cons e) H)) C

private theorem passed_on_ring_mark (x : X) (e : Fin n) (sep : e≠rightNeighbor e)
    (C : CommandClaim) (sh : Sheet)
    (mem : C∈orderedCommands (oldPair B x e))
    (mapped : fenceSheet (geometry (oldPair B x e) C.source.side) C.source.occurrence=some sh)
    (guard : checkFence (oldPair B x e) (view ((x e).long,(x (rightNeighbor e)).long))
      C.source (unit 11)=.advance)
    (noPrep : (⟨C.source.side,sh⟩ : At Sheet)∉reserved (round (oldPair B x e)
      ((x e).long,(x (rightNeighbor e)).long)).prep) :
    (readLane (Sheet.index sh) (step x e (site e C.source.side)).long).mobile=.empty := by
  let g := oldPair B x e
  let raw : Pair (BitVec LW) := ((x e).long,(x (rightNeighbor e)).long)
  let a : At Sheet := ⟨C.source.side,sh⟩
  have empty := passed_empty ((mapped_fence_passes g (view raw) C.source (unit 11) sh rfl rfl mapped).mp guard)
  have F := BStarLongFenceTopology.passing_lane_frames g raw C (unit 11) sh mem rfl rfl mapped guard noPrep
  have joined := BStarClearanceMobileJoined.joined_view k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
    (x e,x (rightNeighbor e))
  have H := (congrFun joined a).trans F
  rw [BStarCopyRightMark.new_access hp x e a sep] at H
  exact (congrArg Lane.mobile H).trans empty

/-- Frame a growing visited region on the same raw marks. Each newly
visited lane comes from a checked physical FENCE departure. Parked
marks only require the actual selected incoming claims to stay in the
already visited region, with no prep reservations on that region. -/
theorem passed_region_word (x : X) (w : List (Fin n))
    (region : Nat→Fin n→Sheet→Prop) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (init : ∀ i sh,region 0 i sh → (readLane (Sheet.index sh) (x i).long).mobile=.empty)
    (scope : ∀ a e b,w=a++e::b → FrozenRegion hp (region a.length) (run x a) e)
    (visits : ∀ a e b,w=a++e::b →
      let y := run x a
      let g := oldPair B y e
      let raw : Pair (BitVec LW) := ((y e).long,(y (rightNeighbor e)).long)
      ∀ i sh,region (a.length+1) i sh → region a.length i sh ∨
        ∃ C : CommandClaim,C∈orderedCommands g ∧ i=site e C.source.side ∧
          fenceSheet (geometry g C.source.side) C.source.occurrence=some sh ∧
          checkFence g (view raw) C.source (unit 11)=.advance ∧
          (⟨C.source.side,sh⟩ : At Sheet)∉reserved (round g raw).prep) :
    ∀ i sh,region w.length i sh → (readLane (Sheet.index sh) (run x w i).long).mobile=.empty := by
  induction w generalizing x region with
  | nil => exact init
  | cons e w ih =>
    have keep := region_frame hp (region 0) x e (sep e) (scope [] e w rfl) init
    have advance (i : Fin n) (sh : Sheet) (A : region 1 i sh) :
        (readLane (Sheet.index sh) (step x e i).long).mobile=.empty := by
      rcases visits [] e w rfl i sh A with old|⟨C,mem,loc,mapped,guard,prep⟩
      · exact (congrArg Lane.mobile (keep i sh old)).trans (init i sh old)
      · rw [loc]
        exact passed_on_ring_mark hp x e (sep e) C sh mem mapped guard prep
    exact ih (step x e) (fun j=>region (j+1)) advance
      (fun a b c F=>scope (e::a) b c (congrArg (List.cons e) F))
      (fun a b c F=>visits (e::a) b c (congrArg (List.cons e) F))

def VisitedEmpty (base : X) (S : List (Pos n)) (fall : Pos n) (k : Nat) (x : X) : Prop :=
  ∀ i sh,Visited hp base S fall k i sh → (readLane (Sheet.index sh) (x i).long).mobile=.empty

/-- Both actual physical stripping paths sit in the outward chart.
Before terminal K10, every upstream and earlier retaining position
has been visited, including a wrapped right upstream and width one. -/
theorem strip_ranks {base : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (width lSeam rSeam rTail : Nat) (positive : 0<width)
    (lbase rroot rbase : Fin n) (rAt : rroot=(S.getD len fall).1)
    (lJoin : addr lbase lSeam=rroot) (rJoin : addr rbase 0=addr rroot (width-1))
    (L : BStarCopyLeftStrip.Strip B base lbase lSeam width)
    (D : BStarCopyRightRetained.Dest B base rroot width)
    (R : BStarCopyRightWrappedGeometry.WrappedStrip B base rbase rSeam rTail)
    (inside : ∀ i,(longGeometry B (base i)).inside=decide (BStarH6Ordinal.oldOrdinal B base hh i<width))
    (notShort : ∀ j,oldH6 B base (rightNeighbor j)=true → width≤BStarH6Ordinal.oldOrdinal B base hh j+1) :
    ∃ last,last<len ∧
      (∀ i,i<lSeam+width → ∃ k,k+(lSeam+width-1-i)=last ∧
        S.getD k fall=(addr lbase i,fencePort (BStarCopyLeftStrip.rail lSeam i)) ∧
        fenceSheet (longGeometry B (base (addr lbase i))) (fencePort (BStarCopyLeftStrip.rail lSeam i))=
          some (BStarCopyLeftStrip.rail lSeam i)) ∧
      (∀ j,j<width → ∃ k,k+j=len ∧ S.getD k fall=(addr rroot j,fencePort .rd) ∧
        fenceSheet (longGeometry B (base (addr rroot j))) (fencePort .rd)=some .rd) ∧
      (∀ j,j≤rTail → ∃ k,k+j+(width-1)=len ∧ S.getD k fall=(addr rbase j,fencePort (rail rSeam j)) ∧
        fenceSheet (longGeometry B (base (addr rbase j))) (fencePort (rail rSeam j))=some (rail rSeam j)) := by
  let leftEnd := lSeam+width-1
  let leftSheet := BStarCopyLeftStrip.rail lSeam
  have length := chart.length
  obtain ⟨terminalPort,_,_,_,_,lastInside,_,k,K,atK⟩ :=
    BStarFenceReceiverChart.endpoints hp chart positive inside notShort
  have leftAddr : addr lbase leftEnd=BStarFenceReceiverChart.digitFrom (S.getD len fall).1 (width-1) := by
    rw [show leftEnd=lSeam+(width-1) by omega,←BStarCopyLeftFenceHold.address_add,lJoin,rAt,
      BStarCopyLeftFence.addr_digits]
  have leftType : leftSheet leftEnd=.ld := by
    exact if_neg (show ¬leftEnd<lSeam by omega)
  have mappedEnd : fenceSheet (longGeometry B (base (addr lbase leftEnd))) (fencePort (leftSheet leftEnd))=
      some (leftSheet leftEnd) := by
    rw [leftAddr,leftType]
    have in0 : (longGeometry B (base (BStarFenceReceiverChart.digitFrom (S.getD len fall).1 (width-1)))).inside=true := lastInside
    change (if (longGeometry B (base (BStarFenceReceiverChart.digitFrom (S.getD len fall).1 (width-1)))).inside then some Sheet.ld else none)=some Sheet.ld
    rw [in0]
    rfl
  have leftBefore : ∀ d,d≤leftEnd → ∃ l,l+d=k ∧
      S.getD l fall=(addr lbase (leftEnd-d),fencePort (leftSheet (leftEnd-d))) ∧
      fenceSheet (longGeometry B (base (addr lbase (leftEnd-d)))) (fencePort (leftSheet (leftEnd-d)))=
        some (leftSheet (leftEnd-d)) := by
    intro d
    induction d with
    | zero =>
      intro _
      simp only [Nat.sub_zero]
      exact ⟨k,rfl,by rw [leftAddr,leftType]; exact atK,mappedEnd⟩
    | succ d ih =>
      intro Bnd
      let i := leftEnd-(d+1)
      have nxt : i+1=leftEnd-d := by dsimp [i]; omega
      obtain ⟨j,J,atJ,_⟩ := ih (by omega)
      let e := addr lbase i
      let A := BStarLongClaims.R (leftSheet (i+1))
      let C := hop (BStarLongClaims.L (leftSheet i)) A
      have raw : C∈dataClaims (oldPair B base e) :=
        (BStarCopyLeftStrip.raw_hop L i (by dsimp [leftEnd] at *; omega) C rfl).mpr rfl
      have target : S.getD j fall=address e (fenceAt A) := by
        change _=(rightNeighbor (addr lbase i),fencePort (leftSheet (i+1)))
        rw [←BStarCopyRightStrip.addr_next,nxt]
        exact atJ
      obtain ⟨prev,rank,loc,mapped⟩ := chart_data_predecessor hp chart (fun _=>rfl) e [] C A
        (BStarCopyRightAuthority.raw_is_selected_empty _ _ raw) rfl j (by omega) target
      exact ⟨prev,by omega,loc,mapped⟩
  have rightDest : ∀ j,j<width → ∃ k,k+j=len ∧ S.getD k fall=(addr rroot j,fencePort .rd) ∧
      fenceSheet (longGeometry B (base (addr rroot j))) (fencePort .rd)=some .rd := by
    intro j
    induction j with
    | zero =>
      intro _
      refine ⟨len,by omega,?_,rfl⟩
      rw [show addr rroot 0=rroot from Fin.ext (Nat.mod_eq_of_lt rroot.isLt),rAt]
      exact Prod.ext rfl terminalPort
    | succ j ih =>
      intro jW
      obtain ⟨k,kLen,atK,_⟩ := ih (by omega)
      let e := addr rroot j
      let A := BStarLongClaims.L Sheet.rd
      let C := hop (BStarLongClaims.R .rd) A
      have nh : (oldPair B base e).2.axes.h6=false := by
        change oldH6 B base (rightNeighbor (addr rroot j))=false
        rw [←BStarCopyRightStrip.addr_next]
        exact D.body (j+1) (by omega) jW
      have raw : C∈dataClaims (oldPair B base e) := by simp [C,A,dataClaims,nh]
      obtain ⟨prev,rank,loc,mapped⟩ := chart_data_predecessor hp chart (fun _=>rfl) e [] C A
        (BStarCopyRightAuthority.raw_is_selected_empty _ _ raw) rfl k (by omega) atK
      change S.getD prev fall=(rightNeighbor (addr rroot j),fencePort .rd) at loc
      rw [←BStarCopyRightStrip.addr_next] at loc
      exact ⟨prev,by omega,loc,rfl⟩
  have rightUp : ∀ j,j≤rTail → ∃ k,k+j+(width-1)=len ∧
      S.getD k fall=(addr rbase j,fencePort (rail rSeam j)) ∧
      fenceSheet (longGeometry B (base (addr rbase j))) (fencePort (rail rSeam j))=some (rail rSeam j) := by
    intro j
    induction j with
    | zero =>
      intro _
      obtain ⟨k,Q,loc,mapped⟩ := rightDest (width-1) (by omega)
      have rd : rail rSeam 0=.rd := if_pos R.seam_pos
      exact ⟨k,by omega,by rw [rJoin,rd]; exact loc,by rw [rJoin,rd]; exact mapped⟩
    | succ j ih =>
      intro jT
      obtain ⟨k,kLen,atK,_⟩ := ih (by omega)
      let e := addr rbase j
      let A := BStarLongClaims.L (rail rSeam j)
      let C := hop (BStarLongClaims.R (rail rSeam (j+1))) A
      have raw : C∈dataClaims (oldPair B base e) :=
        (BStarCopyRightWrappedGeometry.wrapped_raw_incoming R j (by omega) C rfl).mpr rfl
      obtain ⟨prev,rank,loc,mapped⟩ := chart_data_predecessor hp chart (fun _=>rfl) e [] C A
        (BStarCopyRightAuthority.raw_is_selected_empty _ _ raw) rfl k (by omega) atK
      change S.getD prev fall=(rightNeighbor (addr rbase j),fencePort (rail rSeam (j+1))) at loc
      rw [←BStarCopyRightStrip.addr_next] at loc
      change fenceSheet (longGeometry B (base (site e .right))) (fencePort (rail rSeam (j+1)))=some (rail rSeam (j+1)) at mapped
      rw [show site e .right=addr rbase (j+1) from (BStarCopyRightStrip.addr_next rbase j).symm] at mapped
      exact ⟨prev,by omega,loc,mapped⟩
  refine ⟨k,K,?_,rightDest,rightUp⟩
  intro j J
  obtain ⟨i,N,T,M⟩ := leftBefore (leftEnd-j) (by omega)
  have eq : leftEnd-(leftEnd-j)=j := by dsimp [leftEnd]; omega
  rw [eq] at T M
  exact ⟨i,N,T,M⟩

theorem earlier_strip_visits {base : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (width lSeam rSeam rTail : Nat) (positive : 0<width)
    (lbase rroot rbase : Fin n) (rAt : rroot=(S.getD len fall).1)
    (lJoin : addr lbase lSeam=rroot) (rJoin : addr rbase 0=addr rroot (width-1))
    (L : BStarCopyLeftStrip.Strip B base lbase lSeam width)
    (D : BStarCopyRightRetained.Dest B base rroot width)
    (R : BStarCopyRightWrappedGeometry.WrappedStrip B base rbase rSeam rTail)
    (inside : ∀ i,(longGeometry B (base i)).inside=decide (BStarH6Ordinal.oldOrdinal B base hh i<width))
    (notShort : ∀ j,oldH6 B base (rightNeighbor j)=true → width≤BStarH6Ordinal.oldOrdinal B base hh j+1) :
    (∀ j<lSeam+width,Visited hp base S fall len (addr lbase j) (BStarCopyLeftStrip.rail lSeam j)) ∧
      (∀ j,0<j → j<width → Visited hp base S fall len (addr rroot j) .rd) ∧
      (∀ j,0<j → j≤rTail → Visited hp base S fall len (addr rbase j) (rail rSeam j)) := by
  obtain ⟨last,K,Ls,Rd,Up⟩ := strip_ranks hp chart width lSeam rSeam rTail positive lbase rroot rbase
    rAt lJoin rJoin L D R inside notShort
  refine ⟨?_,?_,?_⟩
  · intro j J
    obtain ⟨k,N,T,M⟩ := Ls j J
    exact ⟨⟨k,by omega,T⟩,M⟩
  · intro j pos J
    obtain ⟨k,N,T,M⟩ := Rd j J
    exact ⟨⟨k,by omega,T⟩,M⟩
  · intro j pos J
    obtain ⟨k,N,T,M⟩ := Up j J
    exact ⟨⟨k,by omega,T⟩,M⟩

/-- The healthy unit and the empty physical prefix are simultaneous
invariants of the real outward tape. A parked mark uses incoming closure.
A moving mark can add just the mapped old inspected lane, which stayed
empty on that mark. The prospective guard calculation receives the
actual previously visited empty region as its induction hypothesis. -/
theorem guarded_busy_visited {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    {z d : Cursor} {w : List (Fin n)}
    (P : BusyOnly hp base (fun j=>S.getD j fall) len 11 x z w d) :
    ∀ k l,z=.out k → d=.out l →
      project (fun j=>S.getD j fall) x k=.forward (unit 11) → VisitedEmpty hp base S fall k x →
      (∀ a e b,w=a++e::b → ∀ j,
        Current hp base (fun t=>S.getD t fall) len (run x a) (.busy 11 (.out j)) →
        ∀ q≤len+1,FrozenRegion hp (Visited hp base S fall q) (run x a) e) →
      (∀ a e b,w=a++e::b → ∀ j,
        Current hp base (fun t=>S.getD t fall) len (run x a) (.busy 11 (.out j)) →
        VisitedEmpty hp base S fall j (run x a) → NoFenceFault hp (run x a) e (S.getD j fall)) →
      project (fun j=>S.getD j fall) (run x w) l=.forward (unit 11) ∧
        VisitedEmpty hp base S fall l (run x w) := by
  induction P with
  | nil _ =>
    intro k l K L F empty _ _
    have E := Cursor.out.inj (K.symm.trans L)
    subst l
    exact ⟨F,empty⟩
  | @cons x z d finish e w I E tail ih =>
    intro k l K L F empty scope guard
    subst z
    obtain ⟨j,J⟩ := BStarAcquireHistorySample.busy_no_back_to_out hp tail ⟨l,L⟩
    subst d
    let slots := fun t=>S.getD t fall
    let g := oldPair B x e
    let raw : Pair (BitVec LW) := ((x e).long,(x (rightNeighbor e)).long)
    have new := busy_start hp tail
    have oldSafe := guard [] e w rfl k I empty
    have single : BusyOnly hp base slots len 11 x (.out k) [e] (.out j) := .cons I E (.nil new)
    have F' := guarded_busy_outward hp chart sep single k j rfl rfl F (by
      intro a mark b W i now
      cases a with
      | nil =>
        change e::[]=mark::b at W
        have h : e=mark := (List.cons.inj W).1
        subst mark
        have idx := (BStarOwnerControlHistory.pointed_unique_forward _ _ _ now.2.1 now.2.2 k I.2.1.1).mp ⟨_,F⟩
        subst i
        exact oldSafe
      | cons a rest =>
        have card := congrArg List.length W
        simp at card <;> omega)
    have frame := region_frame hp (Visited hp base S fall k) x e (sep e)
      (scope [] e w rfl k I k (by have := I.2.1.1; omega)) empty
    have keep : VisitedEmpty hp base S fall k (step x e) :=
      fun i sh member=>(congrArg Lane.mobile (frame i sh member)).trans (empty i sh member)
    have one := fence_advance hp E
    have expanded : VisitedEmpty hp base S fall j (step x e) := by
      cases one with
      | stay => exact keep
      | forward =>
        have stepBound : k<len := by have := new.2.1.1; omega
        intro i sh member
        obtain ⟨⟨q,Q,atQ⟩,mappedBase⟩ := member
        by_cases earlier : q<k
        · exact keep i sh ⟨⟨q,earlier,atQ⟩,mappedBase⟩
        have qk : q=k := by omega
        subst q
        obtain ⟨C,v,u,selected,dest,loc,_⟩ := BStarNumericChronology.ring_departure hp chart e (sep e)
          11 k stepBound I.1 I.2.1 I.2.2 (unit 11) F' rfl
        have mem : C∈orderedCommands g := by
          rw [←actualOffers_claims _ raw]
          exact List.mem_map.mpr ⟨(C,.advance u),selected,rfl⟩
        have kind := (BStarAcquireReturn.link_shape g C v mem dest).2.1
        have nonDoor : C.kind≠.door := by rw [kind]; decide
        have check : checkFence g (view raw) C.source (unit 11)=.advance := by
          cases act : checkFence g (view raw) C.source (unit 11) with
          | fault => exact (oldSafe C mem loc act).elim
          | advance => rfl
          | hold =>
            have F0 := fence_holds hp chart e (sep e) k I F C mem nonDoor loc act
            have contradictionAt := (BStarOwnerControlHistory.pointed_unique_forward _ _ _ new.2.1 new.2.2 k I.2.1.1).mp ⟨_,F0⟩
            omega
        have slot := atQ.symm.trans loc
        have siteEq : i=site e C.source.side := congrArg Prod.fst slot
        have port : fencePort sh=C.source.occurrence := congrArg Prod.snd slot
        have layout := congrArg (fun q : Bool×Bool×Bool=>q.2.1) (I.1.1 i)
        change (longGeometry B (base i)).inside=(longGeometry B (x i)).inside at layout
        have transferSheet : fenceSheet (longGeometry B (x i)) (fencePort sh)=some sh := by
          cases sh <;> simpa [fencePort,fenceSheet,←layout] using mappedBase
        have geometryAt : geometry g C.source.side=longGeometry B (x i) := by
          rw [siteEq]
          cases side : C.source.side <;> rfl
        have mapped : fenceSheet (geometry g C.source.side) C.source.occurrence=some sh := by
          rw [geometryAt,←port]
          exact transferSheet
        have nextScope := scope [] e w rfl k I (k+1) (by omega)
        have here : Visited hp base S fall (k+1) (site e C.source.side) sh := by
          rw [←siteEq]
          exact ⟨⟨k,Q,atQ⟩,mappedBase⟩
        have prep := nextScope.1 ⟨C.source.side,sh⟩ here
        rw [siteEq]
        exact passed_on_ring_mark hp x e (sep e) C sh mem mapped check prep
    exact ih j l rfl L F' expanded
      (fun a b c W=>scope (e::a) b c (congrArg (List.cons e) W))
      (fun a b c W=>guard (e::a) b c (congrArg (List.cons e) W))

/-- The real ISSUE11 launch has an empty visited set and a canonical
unit. Incoming closure and no-prep come from the same old generated
prefix at every mark, leaving only the prospective guard calculation. -/
theorem terminal_fence_visited {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    {w : List (Fin n)}
    (G : GeneratedOwner hp base (fun j=>S.getD j fall) len x .idle w (.busy 11 (.out len)))
    (guard : ∀ a e b,w=a++e::b → ∀ j,
      Current hp base (fun t=>S.getD t fall) len (run x a) (.busy 11 (.out j)) →
      VisitedEmpty hp base S fall j (run x a) → NoFenceFault hp (run x a) e (S.getD j fall)) :
    project (fun j=>S.getD j fall) (run x w) len=.forward (unit 11) ∧
      VisitedEmpty hp base S fall len (run x w) := by
  obtain ⟨pre,tour,launch,W,_,launched,op,P⟩ := from_idle hp G
  let old := run x pre
  let start := step old launch
  let root := (S.getD 0 fall).1
  have addr0 := (BStarResetChartService.root_header hp chart (busy_start hp P).1.1).2
  have initial : project (fun j=>S.getD j fall) start 0=.forward (unit 11) := by
    obtain ⟨_,a,arg,snap⟩ := launched
    have C : (ctrlOp.read (old root).long).toNat=11 := op
    change BStarLongDoor.initial (ctrlOp.read (old root).long).toNat (old root).long=some a at arg
    rw [C] at arg
    have A : a=0 := (Option.some.inj (show some 0=some a from arg)).symm
    subst a
    have point := congrArg (fun q : (Token×BitVec 2)×BitVec 9=>q.1.1) snap
    change atSite (start root).long 0=forward (ctrlOp.read (old root).long).toNat 0 at point
    rw [C] at point
    change atSite (start root).long (S.getD 0 fall).2=.forward (unit 11)
    rw [addr0]
    exact point
  have empty : VisitedEmpty hp base S fall 0 start := by
    rintro i sh ⟨⟨q,Q,_⟩,_⟩
    omega
  have split (a : List (Fin n)) (e : Fin n) (b : List (Fin n)) (E : tour=a++e::b) :
      w=(pre++launch::a)++e::b := by rw [W,E,List.append_assoc,List.cons_append]
  have replay (a : List (Fin n)) : run x (pre++launch::a)=run start a := by
    rw [BStarResetSchedule.run_append]; rfl
  have ready (a : List (Fin n)) (e : Fin n) (b : List (Fin n)) (E : tour=a++e::b)
      (j : Nat) (I : Current hp base (fun t=>S.getD t fall) len (run start a) (.busy 11 (.out j)))
      (q : Nat) (Q : q≤len+1) : FrozenRegion hp (Visited hp base S fall q) (run start a) e := by
    obtain ⟨m,G0,_⟩ := BStarCopyGateAuthority.history_prefix hp (pre++launch::a) (e::b) (split a e b E ▸ G)
    have late : 11≤pc (run x (pre++launch::a)) root := by
      rw [replay a]
      exact Nat.le_of_eq I.1.2.2.2.symm
    have layout : ∀ i,Layout B base i=Layout B (run x (pre++launch::a)) i := by
      rw [replay a]; exact I.1.1
    have R := late_visited_scope hp chart sep G0 late layout e q Q
    rwa [replay a] at R
  have physical (a : List (Fin n)) (e : Fin n) (b : List (Fin n)) (E : tour=a++e::b)
      (j : Nat) (I : Current hp base (fun t=>S.getD t fall) len (run start a) (.busy 11 (.out j)))
      (visited : VisitedEmpty hp base S fall j (run start a)) : NoFenceFault hp (run start a) e (S.getD j fall) := by
    have R := guard (pre++launch::a) e b (split a e b E) j ((replay a).symm ▸ I) ((replay a).symm ▸ visited)
    rwa [replay a] at R
  have F := guarded_busy_visited hp chart sep P 0 len rfl rfl initial empty ready physical
  rw [W,BStarResetSchedule.run_append]
  exact F

/-- Satisfy the physical old-region inputs of the FENCE terminal from
one visited-prefix invariant and the exact two original strips. -/
theorem earlier_strip_vacancy {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (width lSeam rSeam rTail : Nat) (positive : 0<width)
    (lbase rroot rbase : Fin n) (rAt : rroot=(S.getD len fall).1)
    (lJoin : addr lbase lSeam=rroot) (rJoin : addr rbase 0=addr rroot (width-1))
    (L : BStarCopyLeftStrip.Strip B base lbase lSeam width)
    (D : BStarCopyRightRetained.Dest B base rroot width)
    (R : BStarCopyRightWrappedGeometry.WrappedStrip B base rbase rSeam rTail)
    (inside : ∀ i,(longGeometry B (base i)).inside=decide (BStarH6Ordinal.oldOrdinal B base hh i<width))
    (notShort : ∀ j,oldH6 B base (rightNeighbor j)=true → width≤BStarH6Ordinal.oldOrdinal B base hh j+1)
    (H : VisitedEmpty hp base S fall len x) :
    (∀ j<lSeam,(BStarCopyLeftMark.sample x lbase lSeam j).mobile=.empty) ∧
    (∀ j,0<j → j≤rTail → (readLane (Sheet.index (rail rSeam j)) (x (addr rbase j)).long).mobile=.empty) ∧
    (∀ j<width,(ldRead x (addr lbase lSeam) j).mobile=.empty) ∧
    (∀ j,j<width-1 → (rdRead x rroot width j).mobile=.empty) := by
  obtain ⟨left,right,up⟩ := earlier_strip_visits hp chart width lSeam rSeam rTail positive lbase rroot rbase
    rAt lJoin rJoin L D R inside notShort
  refine ⟨?_,fun j pos bound=>H _ _ (up j pos bound),?_,?_⟩
  · intro j J
    exact H _ _ (left j (by omega))
  · intro j J
    unfold ldRead
    rw [BStarCopyLeftFenceHold.address_add]
    have M := left (lSeam+j) (by omega)
    rw [BStarCopyLeftStrip.rail,if_neg (by omega : ¬lSeam+j<lSeam)] at M
    exact H _ _ M
  · intro j J
    exact H _ _ (right (width-1-j) (by omega) (by omega))

private theorem receiver_drained {T : Type} (digits : T→BitVec 36)
    {plan : List T} {s : Ledger T} {upstream : List T}
    (P : OrderedPrefix plan s upstream) (emitted : s.release.pending=[])
    (emptyUp : upstream=[]) (width : Nat) (size : plan.length=width) (pos : 0<width)
    (lanes : Nat→Lane)
    (matchLane : ∀ j,j<width → Compatible digits (s.cells j) (lanes j))
    (earlier : ∀ j,j<width-1 → (lanes j).mobile=.empty) :
    (∃ d,(lanes (width-1)).retained=.data d) ∧
    (∀ j,j<width-1 → (s.cells j).mobile=none) := by
  obtain ⟨Q,boundary⟩ := ordered_prefix P
  have prior : ∀ j,j<width-1 → (s.cells j).mobile=none := by
    intro j J
    have H := (earlier j J).symm.trans (matchLane j (by omega)).1
    cases h : (s.cells j).mobile with
    | none => rfl
    | some tag => rw [h] at H; contradiction
  have B0 : OrderedBoundary s [] := emptyUp ▸ boundary
  have ⟨_,d,held⟩ := FreshFenceOperand.inspections_receive Q emitted B0 (width-1) (by omega)
    prior
  refine ⟨⟨digits d,?_⟩,prior⟩
  rw [(matchLane (width-1) (by omega)).2,held] <;> rfl

private theorem read_same (u v : Nat→Lane) (j len : Nat)
    (equal : ∀ i,j≤i → i<j+len → u i=v i) :
    laneRead u j len=laneRead v j len := by
  induction len generalizing j with
  | zero => rfl
  | succ len ih =>
    simp only [laneRead,equal j (Nat.le_refl _) (by omega)]
    rw [ih (j+1) (fun i low high=>equal i (by omega) (by omega))]

/-- Follow the two ledgers from the actual completed INJECT outward
cut to the FENCE turn and through the original reply consume. The
data readiness and previously drained regions are physical inputs.
The selected right terminal guard and the source acceptance follow
on the stated word. -/
theorem through_fence {L R : Type}
    (lDigits : L→BitVec 36) (rDigits : R→BitVec 36)
    {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (width lSeam rSeam rTail : Nat) (positive : 0<width)
    (lbase rroot rbase : Fin n) (rightRoot : rroot=(S.getD len fall).1)
    (join : addr rbase 0=addr rroot (width-1))
    (lPlan : List L) (rPlan : List R) (lSize : lPlan.length=width) (rSize : rPlan.length=width)
    (ls : Ledger L) (rs : Ledger R) (lLabels : Nat→Option L) (rLabels : Nat→Option R)
    (lEmitted : ls.release.pending=[]) (rEmitted : rs.release.pending=[])
    (lOrdered : OrderedPrefix lPlan ls (headFirst lSeam lLabels))
    (rOrdered : OrderedPrefix rPlan rs (stripWord rTail rLabels))
    (lRetained : BStarCopyLeftRetained.RetainedMatches lDigits x (addr lbase lSeam) width ls)
    (rRetained : BStarCopyRightRetained.RetainedMatches rDigits x rroot width rs)
    (lUp : BStarCopyLeftMark.UpstreamMatches lDigits x lbase lSeam lLabels)
    (rUp : BStarCopyRightMark.MobileMatches rDigits x rbase rSeam rTail rLabels)
    (w back : List (Fin n)) (turn ack : Fin n)
    (flight : GeneratedOwner hp base (fun j=>S.getD j fall) len x (.busy 10 (.out len)) w (.busy 11 (.out len)))
    (front : project (fun j=>S.getD j fall) (run x w) len=.forward (unit 11))
    (ret : BusyOnly hp base (fun j=>S.getD j fall) len 11
      (step (run x w) turn) (.back len) back (.back 0))
    (consume : Event hp (fun j=>S.getD j fall) len
      (run (step (run x w) turn) back) ack (.busy 11 (.back 0)) .idle)
    (lReady : ∀ a e b,w++turn::(back++[ack])=a++e::b →
      BStarCopyLeftDataSweep.DataReady hp (run x a) lbase e lSeam width)
    (rReady : ∀ a e b,w++turn::(back++[ack])=a++e::b →
      BStarCopyRightWrappedSweep.DataReady hp (run x a) rroot rbase e width rSeam rTail)
    (lPastUp : ∀ j<lSeam,(BStarCopyLeftMark.sample (run x w) lbase lSeam j).mobile=.empty)
    (rPastUp : ∀ j,0<j → j≤rTail →
      (readLane (Sheet.index (rail rSeam j)) (run x w (addr rbase j)).long).mobile=.empty)
    (lPast : ∀ j,j<width-1 → (ldRead (run x w) (addr lbase lSeam) j).mobile=.empty)
    (rPast : ∀ j,j<width-1 → (rdRead (run x w) rroot width j).mobile=.empty)
    (clean : (readLane (Sheet.index .rd) (x rroot).long).error=false) :
    let y := run (step (run x w) turn) back
    let z := step y ack
    BStarNativeReceiptTape.Hit hp base (fun j=>S.getD j fall) len y ack 11 ∧
      laneRead (ldRead z (addr lbase lSeam)) 0 width=lPlan.reverse.map (Digit9.data ∘ lDigits) ∧
      laneRead (rdRead z rroot width) 0 width=rPlan.reverse.map (Digit9.data ∘ rDigits) ∧
      (∀ i sh,BStarCopyLeftFenceHold.Region lbase lSeam width i sh →
        (readLane (Sheet.index sh) (z i).long).mobile=.empty) ∧
      (∀ i sh,BStarCopyRightWrappedFenceHold.Region rroot rbase width rSeam rTail i sh →
        (readLane (Sheet.index sh) (z i).long).mobile=.empty) := by
  let old := run x w
  let tail := turn::(back++[ack])
  have lPre (a : List (Fin n)) (e : Fin n) (b : List (Fin n)) (E : w=a++e::b) :
      BStarCopyLeftDataSweep.DataReady hp (run x a) lbase e lSeam width :=
    lReady a e (b++tail) (by rw [E,List.append_assoc,List.cons_append])
  have rPre (a : List (Fin n)) (e : Fin n) (b : List (Fin n)) (E : w=a++e::b) :
      BStarCopyRightWrappedSweep.DataReady hp (run x a) rroot rbase e width rSeam rTail :=
    rReady a e (b++tail) (by rw [E,List.append_assoc,List.cons_append])
  have terminalClean : (rdRead old rroot width (width-1)).error=false := by
    unfold rdRead
    rw [Nat.sub_self,show addr rroot 0=rroot from Fin.ext (Nat.mod_eq_of_lt rroot.isLt)]
    exact right_terminal_clean_word hp rDigits x w rroot rbase width rSeam rTail join sep
      rPlan rSize rs rLabels rOrdered rRetained rUp rPre clean
  obtain ⟨l,rLabel,lRel,lOrd,lRet,lMatch⟩ := BStarCopyLeftDataSweep.data_word hp lDigits x w
    lbase lSeam width sep lPlan lSize ls lLabels lOrdered lRetained lUp lPre
  obtain ⟨rr,rLabels',rRel,rOrd,rRet,rMatch⟩ := BStarCopyRightWrappedSweep.data_word hp rDigits x w
    rroot rbase width rSeam rTail join sep rPlan rSize rs rLabels rOrdered rRetained rUp rPre
  have lNil := left_empty_labels lDigits old lbase lSeam rLabel lMatch lPastUp
  have rNil := right_empty_labels rDigits old rbase rSeam rTail rLabels' rMatch rPastUp
  have lDone := (congrArg BStarCopyInjection.ReleaseHistory.pending lRel).trans lEmitted
  have rDone := (congrArg BStarCopyInjection.ReleaseHistory.pending rRel).trans rEmitted
  have ⟨lHas,_⟩ := receiver_drained lDigits lOrd lDone lNil width lSize positive
    (ldRead old (addr lbase lSeam)) lRet lPast
  obtain ⟨lMobile,lImage,_,_⟩ := BStarCopyLeftFence.saturate_left lDigits old (addr lbase lSeam)
    width lPlan lSize positive lOrd lRet lHas
  have matchR := right_image rDigits old rroot width rr rRet
  obtain ⟨rHas,rEarlier⟩ := receiver_drained rDigits rOrd rDone rNil width rSize positive
    (rdRead old rroot width) matchR rPast
  obtain ⟨rMobile,rImage,_,_⟩ := BStarCopyRightFence.saturate_right rDigits old rroot width rPlan
    rSize positive rOrd rRet rHas
  have onPort : ∀ C : CommandClaim, C∈orderedCommands (oldPair B old turn) →
      C.kind=.terminal → C.destination=none →
      S.getD len fall=address turn C.source →
      checkFence (oldPair B old turn) (view ((old turn).long,(old (rightNeighbor turn)).long))
        C.source (unit 11)=.advance := by
    intro C mem kind dest loc
    let g := oldPair B old turn
    let raw : Pair (BitVec LW) := ((old turn).long,(old (rightNeighbor turn)).long)
    have nonDoor : C.kind≠.door := by rw [kind]; decide
    have port : C.source.occurrence=10 :=
      Fin.ext (BStarAcquireChainEndpoints.terminal g C mem dest nonDoor).2.2.2
    let a : At Sheet := ⟨C.source.side,.rd⟩
    have atRoot : site turn C.source.side=rroot := (congrArg Prod.fst loc).symm.trans rightRoot.symm
    have zero : addr rroot 0=rroot := Fin.ext (Nat.mod_eq_of_lt rroot.isLt)
    have tailIndex : width-1-(width-1)=0 := by omega
    have pairView : view raw a=readLane (Sheet.index .rd) (old (site turn C.source.side)).long := by
      cases side : C.source.side <;> simp [a,raw,view,lane,BStarTrace.lane,site,side]
    have laneAt : view raw a=rdRead old rroot width (width-1) := by
      rw [pairView,atRoot]
      unfold rdRead
      rw [tailIndex,zero]
    have R := rReady w turn (back++[ack]) rfl
    have openGate : (view raw a).gate=true := by
      rw [laneAt,rdRead,tailIndex]
      exact R.rdGate 0 positive
    have inside : (geometry g C.source.side).inside=true := by
      have H := R.dest.inside 0 positive
      rw [zero,←atRoot] at H
      cases side : C.source.side <;> simpa [g,geometry,oldPair,site,side] using H
    have retains : BStarLongPackets.retains g a=true := by
      cases side : C.source.side <;> simp_all [BStarLongPackets.retains,a,geometry]
    have portPassed : Passed g (view raw) a := by
      obtain ⟨ordered,bd⟩ := ordered_prefix rOrd
      have B0 : OrderedBoundary rr [] := rNil ▸ bd
      have pass := FreshFenceOperand.forward_operand rDigits ordered (by omega) rDone B0
        (rdRead old rroot width) (by rw [rSize]; exact matchR)
        (by rw [rSize]; exact rEarlier)
        g (view raw) a (by rw [rSize]; exact laneAt) retains openGate (by rw [laneAt]; exact terminalClean)
      exact pass.1
    have sheet : fenceSheet (geometry g C.source.side) C.source.occurrence=some .rd := by
      rw [port] <;> rfl
    exact (mapped_fence_passes g (view raw) C.source (unit 11) .rd rfl rfl sheet).mpr portPassed
  have chosen : onTerminal hp old turn (fun j=>S.getD j fall) len := by
    obtain ⟨C,f,move,kind,dst,port,loc⟩ := BStarStageTerminalHealth.selected_turn
      hp chart turn (sep turn) 11 (BStarGeneratedTapeCuts.at_end hp flight) (busy_start hp ret)
    have mem : C∈orderedCommands (oldPair B old turn) := by
      rw [←actualOffers_claims _ ((old turn).long,(old (rightNeighbor turn)).long)]
      exact List.mem_map.mpr ⟨(C,.advance f),move,rfl⟩
    exact ⟨C,mem,kind,dst,port,loc⟩
  have receipt := guarded_turn hp turn (sep turn) chosen front onPort
  have H := accept_unit hp chart sep 11 (.inr rfl) ret receipt ack consume
  have lLate (a : List (Fin n)) (e : Fin n) (b : List (Fin n)) (E : tail=a++e::b) :
      BStarCopyLeftDataSweep.DataReady hp (run old a) lbase e lSeam width := by
    have J := lReady (w++a) e b (by change w++tail=_; rw [E,List.append_assoc])
    rwa [BStarResetSchedule.run_append] at J
  have rLate (a : List (Fin n)) (e : Fin n) (b : List (Fin n)) (E : tail=a++e::b) :
      BStarCopyRightWrappedSweep.DataReady hp (run old a) rroot rbase e width rSeam rTail := by
    have J := rReady (w++a) e b (by change w++tail=_; rw [E,List.append_assoc])
    rwa [BStarResetSchedule.run_append] at J
  have lFrame := BStarCopyLeftFenceHold.drained_after hp lDigits old lbase lSeam width rLabel
    lMobile lMatch lNil tail sep lLate
  have lEmpty := BStarCopyLeftFenceHold.drained_old lDigits old lbase lSeam width rLabel
    lMobile lMatch lNil
  have rEmpty := BStarCopyRightWrappedFenceHold.drained_old rDigits old rroot rbase width rSeam rTail
    rLabels' rMobile rMatch rNil
  have rFrame := BStarCopyFenceSaturation.drained_word_frame hp
    (BStarCopyRightWrappedFenceHold.Region rroot rbase width rSeam rTail)
    old tail sep rEmpty
    (fun a e b E=>BStarCopyRightWrappedFenceHold.ready_frozen hp (run old a) rroot rbase e width
      rSeam rTail join (rLate a e b E))
  have lRead : laneRead (ldRead (run old tail) (addr lbase lSeam)) 0 width=
      lPlan.reverse.map (Digit9.data ∘ lDigits) :=
    (read_same _ _ 0 width (fun j _ J=>lFrame _ .ld (BStarCopyLeftFenceHold.ld_member lbase lSeam width j
      (by omega)))).trans lImage
  have rRead : laneRead (rdRead (run old tail) rroot width) 0 width=
      rPlan.reverse.map (Digit9.data ∘ rDigits) :=
    (read_same _ _ 0 width (fun j _ J=>rFrame _ .rd (.inl ⟨width-1-j,by omega,rfl,rfl⟩))).trans rImage
  have lDrain : ∀ i sh,BStarCopyLeftFenceHold.Region lbase lSeam width i sh →
      (readLane (Sheet.index sh) (run old tail i).long).mobile=.empty :=
    fun i sh member=>(congrArg Lane.mobile (lFrame i sh member)).trans (lEmpty i sh member)
  have rDrain : ∀ i sh,BStarCopyRightWrappedFenceHold.Region rroot rbase width rSeam rTail i sh →
      (readLane (Sheet.index sh) (run old tail i).long).mobile=.empty :=
    fun i sh member=>(congrArg Lane.mobile (rFrame i sh member)).trans (rEmpty i sh member)
  have final : run old tail=step (run (step old turn) back) ack := by
    change run (step old turn) (back++[ack])=_
    rw [BStarResetSchedule.run_append] <;> rfl
  rw [final] at lRead rRead lDrain rDrain
  exact ⟨H,lRead,rRead,lDrain,rDrain⟩

#print axioms accept_unit
#print axioms data_follows_fence
#print axioms chart_data_predecessor
#print axioms chart_region_scope
#print axioms late_visited_scope
#print axioms ready_after_enable
#print axioms guarded_turn
#print axioms fence_holds
#print axioms mapped_guard_nofault
#print axioms retaining_guard_nofault
#print axioms guarded_busy_outward
#print axioms terminal_fence_unit
#print axioms right_terminal_clean_mark
#print axioms right_terminal_clean_word
#print axioms passed_region_word
#print axioms guarded_busy_visited
#print axioms terminal_fence_visited
#print axioms earlier_strip_vacancy
#print axioms through_fence
end L4.Height.FreshFenceContinuation
