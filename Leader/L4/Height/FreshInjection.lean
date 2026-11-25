import Leader.L4.BStarCopyDownstream
import Leader.L4.BStarCopyLeftReleaseOrder
import Leader.L4.BStarResetNoFault

namespace L4.Height.FreshInjection
open AllSizeProtocol BStarTrace BStarLongClaims BStarLongWork BStarLongToken
open BStarLongCommand BStarLongCommandData BStarLongPrep BStarLongPackets
open BStarLongLiteral BStarLongTransport BStarLongEvents
open BStarH6WordChart BStarAcquireAnchors BStarAcquireVisitOrder BStarAcquireForwardTrace
open BStarAcquireLiteralChain BStarResetChartTouch BStarLongFixedRouting
open BStarResetMarkAdapter BStarResetRailRing BStarGeneratedOwner BStarOwnerLaunchOrigin
open BStarSeparatingRail BStarSeparatorControl BStarCopyInjection BStarCopyEntryGates
open BStarCopyDownstream BStarClearanceDataChart BStarClearanceSource BStarLongDoor

set_option maxRecDepth 4096
set_option maxHeartbeats 1500000

/-- ISSUE10 carries a unit packet. Its command bindings and terminal
format are independent of the old data bytes. -/
theorem inject_unit_packet (g : LongGeometry) (j : Fin 11) :
    let f : Payload := ⟨0,10,0,0,0⟩
    bind g j (.forward f)=.forward f ∧ depart g j f=some f ∧
      arrive g j f=.forward f ∧ finish f=.reply f ∧ bind g j (.reply f)=.reply f := by
  simp [BStarLongCommand.bind,depart,arrive,finish,gate,admit,bitOp,acquire,
    forwardWidth,replyWidth,arithKind,copyLoad,stageOp,sealOp,commitOp,cropped,low]

private theorem same_prep_lane (L : List BStarLongPrep.Offer)
    (unique : (L.map (fun a=>a.claim.lane)).Nodup)
    (a b : BStarLongPrep.Offer) (A : a∈L) (B : b∈L)
    (same : a.claim.lane=b.claim.lane) : a=b := by
  induction L with
  | nil => contradiction
  | cons p L ih =>
    simp only [List.map_cons] at unique
    have N := List.nodup_cons.mp unique
    rcases List.mem_cons.mp A with atHead|inTail
    · subst a
      rcases List.mem_cons.mp B with rfl|inTail'
      · rfl
      · exact (N.1 (List.mem_map.mpr ⟨b,inTail',same.symm⟩)).elim
    · rcases List.mem_cons.mp B with atHead|inTail'
      · subst b
        exact (N.1 (List.mem_map.mpr ⟨a,inTail,same⟩)).elim
      · exact ih N.2 inTail inTail'

/-- On a selected non-door opcode-10 source the pre-preparation
offer is exactly the healthy old bound payload. -/
theorem gated_inject (g : Pair LongGeometry) (raw : Pair (BitVec LW))
    (C : CommandClaim) (f : Payload)
    (mem : C∈orderedCommands g) (nonDoor : C.kind≠.door)
    (old : bound g (readK raw) C.source=.forward f)
    (opcode : f.opcode.toNat=10) :
    (C,.advance f)∈gated g raw := by
  have E : classifyOld g raw C=.advance f := by
    change classify C _ (bound g (readK raw) C.source) _=.advance f
    rw [old]
    simp [classify,nonDoor,depart,gate,opcode,admit,bitOp]
  apply (gated_mem g raw C (.advance f)).mpr
  refine ⟨mem,?_⟩
  unfold gatedAt
  rw [E]
  simp [checkOffer,checkFence,opcode]

/-- Both source occurrences have a selected preparation. The literal
prep list is already injective on its lanes. -/
theorem inject_wins (g : Pair LongGeometry) (raw : Pair (BitVec LW))
    (C : CommandClaim) (f : Payload) (s : Side) (rev : Bool)
    (mem : C∈orderedCommands g) (nonDoor : C.kind≠.door)
    (origin : C.source=⟨s,sourceOccurrence rev⟩)
    (old : bound g (readK raw) C.source=.forward f)
    (healthy : f.fault=0) (opcode : f.opcode.toNat=10)
    (inside : (geometry g s).inside=true) :
    injection s rev∈(arbitration (round g raw).prep).1 := by
  have candidate : injection s rev∈(round g raw).prep :=
    literal_offer g raw C f s rev mem nonDoor origin old healthy opcode inside
  exact exclusive_winner _ _ candidate
    (fun z M E=>same_prep_lane _ (BStarResetNoFault.prep_lanes_nodup g raw) z _ M candidate E)

private theorem inject_prep_origin (g : Pair LongGeometry) (raw : Pair (BitVec LW))
    (C : CommandClaim) (f : Payload) (s : Side) (rev : Bool)
    (origin : C.source=⟨s,sourceOccurrence rev⟩)
    (opcode : f.opcode.toNat=10)
    (inside : (geometry g s).inside=true)
    (gatedC : (C,.advance f)∈gated g raw)
    (a : BStarLongPrep.Offer) (win : a∈(arbitration (round g raw).prep).1)
    (fromC : a.claim.origin=C.source) :
    a.claim.op=.inject ∧ a.claim.lane=⟨s,sourceLane rev⟩ := by
  obtain ⟨D,p,_,before,_,prep,_,src,side,sheet⟩ := BStarCopyOwnedFrozen.winner_origin g raw a win
  obtain ⟨memC,offerC⟩ := (gated_mem g raw C (.advance f)).mp gatedC
  obtain ⟨memD,offerD⟩ := (gated_mem g raw D (.advance p)).mp before
  have eq : D=C := BStarResetNoFault.origin_unique g D C memD memC (src.symm.trans fromC)
  subst D
  have same := BStarLongCommand.Offer.advance.inj (offerD.trans offerC.symm)
  subst p
  have op : a.claim.op=.inject := by
    rw [opcode] at prep
    exact (Option.some.inj prep).symm
  rw [op,origin] at sheet
  have ln : a.claim.lane.occurrence=sourceLane rev := by
    cases rev <;> simpa [sourceOccurrence,sourceLane,prepSites,inside] using sheet
  have sd : a.claim.lane.side=s := side.trans (congrArg At.side origin)
  have laneEq : a.claim.lane=⟨s,sourceLane rev⟩ := by
    calc
      a.claim.lane=⟨a.claim.lane.side,a.claim.lane.occurrence⟩ := rfl
      _=⟨s,sourceLane rev⟩ := by rw [sd,ln]
  exact ⟨op,laneEq⟩

/-- The unique preparation of the selected source cannot cancel
its command. This is checked on the old lane fields. -/
theorem inject_not_cancelled (g : Pair LongGeometry) (raw : Pair (BitVec LW))
    (C : CommandClaim) (f : Payload) (s : Side) (rev : Bool) (value : BitVec 36)
    (origin : C.source=⟨s,sourceOccurrence rev⟩)
    (opcode : f.opcode.toNat=10) (inside : (geometry g s).inside=true)
    (gatedC : (C,.advance f)∈gated g raw)
    (enabled : (view raw ⟨s,sourceLane rev⟩).gate=true)
    (frozen : (view raw ⟨s,sourceLane rev⟩).frozen=.data value)
    (vacant : (view raw ⟨s,sourceLane rev⟩).mobile=.empty) :
    C.source∉(round g raw).faults := by
  intro F
  change C.source∈prepFaults (view raw) (round g raw).prep at F
  simp only [prepFaults,BStarResetNoFault.arb_no_losers g raw,List.map_nil,List.nil_append] at F
  obtain ⟨a,M,fromC⟩ := List.mem_map.mp F
  obtain ⟨win,bad⟩ := List.mem_filter.mp M
  obtain ⟨op,laneEq⟩ := inject_prep_origin g raw C f s rev origin opcode inside gatedC a win fromC
  simp [selectedEffects,op,laneEq,effects,enabled,frozen,vacant,validPayload] at bad

theorem actual_inject_offer (g : Pair LongGeometry) (raw : Pair (BitVec LW))
    (C : CommandClaim) (f : Payload)
    (gatedC : (C,.advance f)∈gated g raw) (opcode : f.opcode.toNat=10)
    (ok : C.source∉(round g raw).faults) :
    (C,.advance f)∈actualOffers g raw := by
  have unchanged : cancel (round g raw).faults (C,.advance f)=(C,.advance f) := by
    change (if C.source∈(round g raw).faults then (C,BStarLongCommand.Offer.advance failedPayload) else (C,BStarLongCommand.Offer.advance f))=(C,BStarLongCommand.Offer.advance f)
    exact if_neg ok
  have old : (C,.advance f)∈(round g raw).offered :=
    List.mem_map.mpr ⟨(C,.advance f),gatedC,unchanged⟩
  unfold actualOffers BStarLongGrant.run
  apply List.mem_map.mpr
  refine ⟨(C,.advance f),old,?_⟩
  by_cases j : C.source.occurrence.val<3 <;> simp [BStarLongGrant.update,j,opcode,acquire]

private theorem inject_carried (g : Pair LongGeometry) (raw : Pair (BitVec LW))
    (C : CommandClaim) (f : Payload) (opcode : f.opcode.toNat=10) :
    BStarClearanceForward.carried g raw C f=f := by
  have node : BStarLongArithmetic.nodeOf 10=none := by decide
  simp [BStarClearanceForward.carried,BStarLongArithmetic.visit,node,BStarLongOutgoing.execute,
    BStarLongOutgoing.hold,opcode,stageOp,sealOp,commitOp]

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step (n:=n) B
local notation "run" => BStarResetSchedule.run step

/-- The selected INJECT writes Trail and the unchanged healthy
payload at the two actual command addresses. -/
theorem inject_command_link (x : X) (e : Fin n) (sep : e≠rightNeighbor e)
    (C : CommandClaim) (dst : AtK) (f : Payload)
    (mem : C∈orderedCommands (oldPair B x e)) (hd : C.destination=some dst)
    (opcode : f.opcode.toNat=10)
    (offer : (C,.advance f)∈actualOffers (oldPair B x e) ((x e).long,(x (rightNeighbor e)).long)) :
    atCursor (step x e) (address e C.source)=.trail ∧
      atCursor (step x e) (address e dst)=.forward f := by
  let g := oldPair B x e
  let raw : Pair (BitVec LW) := ((x e).long,(x (rightNeighbor e)).long)
  have shape := BStarAcquireReturn.link_shape g C dst mem hd
  have safeSource : C.source.side=.right → C.source.occurrence.val=0 →
      g.2.axes.h6=false ∨ LongDoorGuard.valid manifest raw.2=true :=
    fun s k=>(shape.2.2 s k).elim
  have safeDest : dst.side=.right → dst.occurrence.val=0 →
      g.2.axes.h6=false ∨ LongDoorGuard.valid manifest raw.2=true :=
    fun _ k=>.inl (BStarAcquireJoinedHop.k0_dest g C dst mem hd k).2
  obtain ⟨old,arrived⟩ := BStarClearanceForward.move_lands g raw C f dst hd offer (Ne.symm shape.1)
  have after : arrive (geometry g dst.side) dst.occurrence (BStarClearanceForward.carried g raw C f)=.forward f := by
    rw [inject_carried g raw C f opcode]
    simp [arrive,opcode,gate,admit,bitOp]
  rw [after] at arrived
  have one := BStarAcquireReturn.joined_reads _ _ _ _ _ _ _ _ _ hp (x e,x (rightNeighbor e)) C.source safeSource
  have two := BStarAcquireReturn.joined_reads _ _ _ _ _ _ _ _ _ hp (x e,x (rightNeighbor e)) dst safeDest
  have old' : readK (patchPair (longWork g raw) raw) C.source=.trail :=
    (congrArg decode old).trans (decode_encode _)
  have new' : readK (patchPair (longWork g raw) raw) dst=.forward f :=
    (congrArg decode arrived).trans (decode_encode _)
  exact ⟨(new_read B x e sep C.source).symm.trans (one.trans old'),
    (new_read B x e sep dst).symm.trans (two.trans new')⟩

/-- At an actual generated unvisited K5/LS or K2/RS source, the
same physical mark deposits the frozen payload and advances its
own healthy opcode-10 front without changing it. -/
theorem departure_at_cut {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall)
    (e : Fin n) (sep : e≠rightNeighbor e)
    (j : Nat) (cur : Current hp base (fun k=>S.getD k fall) len x (.busy 10 (.out j)))
    (C : CommandClaim) (dst : AtK) (f : Payload) (s : Side) (rev : Bool) (value : BitVec 36)
    (mem : C∈orderedCommands (oldPair B x e)) (hd : C.destination=some dst)
    (src : C.source=⟨s,sourceOccurrence rev⟩)
    (atJ : S.getD j fall=(site e s,sourceOccurrence rev))
    (old : bound (oldPair B x e) (readK ((x e).long,(x (rightNeighbor e)).long)) C.source=.forward f)
    (healthy : f.fault=0) (opcode : f.opcode.toNat=10)
    (inside : (geometry (oldPair B x e) s).inside=true)
    (enabled : (readLane (Sheet.index (sourceLane rev)) (x (site e s)).long).gate=true)
    (frozen : (readLane (Sheet.index (sourceLane rev)) (x (site e s)).long).frozen=.data value)
    (cut : CutVacant x S fall len j rev) :
    let g := oldPair B x e
    let raw := ((x e).long,(x (rightNeighbor e)).long)
    let ln := readLane (Sheet.index (sourceLane rev)) (step x e (site e s)).long
    (C,.advance f)∈actualOffers g raw ∧ injection s rev∈(arbitration (round g raw).prep).1 ∧
      atCursor (step x e) (address e C.source)=.trail ∧
      atCursor (step x e) (address e dst)=.forward f ∧
      ln.mobile=.data value ∧ ln.frozen=.empty := by
  dsimp only
  let g := oldPair B x e
  let raw : Pair (BitVec LW) := ((x e).long,(x (rightNeighbor e)).long)
  have boundJ := cur.2.1.1
  have vacancy := cut (site e s) ⟨j,Nat.le_refl _,boundJ,atJ⟩
  have oldView : view raw ⟨s,sourceLane rev⟩ =
      readLane (Sheet.index (sourceLane rev)) (x (site e s)).long := by cases s <;> rfl
  have nDoor : C.kind≠.door := by rw [(BStarAcquireReturn.link_shape g C dst mem hd).2.1]; decide
  have gatedC := gated_inject g raw C f mem nDoor old opcode
  have safe := inject_not_cancelled g raw C f s rev value src opcode inside gatedC
    (by simpa only [oldView] using enabled) (by simpa only [oldView] using frozen)
    (by simpa only [oldView] using vacancy)
  have still := actual_inject_offer g raw C f gatedC opcode safe
  have win : injection s rev∈(arbitration (round g raw).prep).1 := by
    cases rev with
    | false =>
      have length := chart.length
      have inChart : S.getD j fall∈S := by
        rw [←List.getElem_eq_getD (h:=show j<S.length by omega)]
        exact List.getElem_mem _
      have owner := (chart.entries _ inChart).2
      rw [atJ] at owner
      have laneOwner : dataOwner (oldH6 B base) (site e s) .ls=o.val := owner
      have ptr : address e C.source=S.getD j fall := by rw [src,atJ] <;> rfl
      exact BStarCopyLeftReleaseOrder.pointed_inject_wins hp chart cur.1.1 e sep C f s j laneOwner
        cur.2.1 cur.2.2 ptr src opcode gatedC healthy inside
    | true =>
      exact inject_wins g raw C f s true mem nDoor src old healthy opcode inside
  have fields := BStarCopyOperand.ring_inject hp x e sep s rev value win enabled frozen vacancy
  have tokens := inject_command_link hp x e sep C dst f mem hd opcode still
  exact ⟨still,win,tokens.1,tokens.2,congrArg Lane.mobile fields,congrArg Lane.frozen fields⟩

/-- The old vacancy of a generated INJECT is produced at the original
ISSUE10 cut. No intermediate vacancy assumption is needed. -/
theorem generated_departure {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    {w : List (Fin n)} {j : Nat}
    (history : GeneratedOwner hp base (fun k=>S.getD k fall) len x .idle w (.busy 10 (.out j)))
    (layout : ∀ a b,w=a++b → ∀ i,Layout B base i=Layout B (run x a) i)
    (emptyAtIssue : ∀ a e b,w=a++e::b →
      Launch ((run x a) (S.getD 0 fall).1).long ((step (run x a) e) (S.getD 0 fall).1).long →
      (ctrlOp.read ((run x a) (S.getD 0 fall).1).long).toNat=10 →
      MobilesEmpty hp base (run x a) o.val)
    (e : Fin n) (C : CommandClaim) (dst : AtK) (f : Payload)
    (s : Side) (rev : Bool) (value : BitVec 36) :
    let y := run x w
    let g := oldPair B y e
    let raw := ((y e).long,(y (rightNeighbor e)).long)
    let ln := Sheet.index (sourceLane rev)
    C∈orderedCommands g → C.destination=some dst →
    C.source=⟨s,sourceOccurrence rev⟩ → S.getD j fall=(site e s,sourceOccurrence rev) →
    bound g (readK raw) C.source=.forward f →
    f.fault=0 → f.opcode.toNat=10 → (geometry g s).inside=true →
    (readLane ln (y (site e s)).long).gate=true →
    (readLane ln (y (site e s)).long).frozen=.data value →
    let after := readLane ln (step y e (site e s)).long
    (C,.advance f)∈actualOffers g raw ∧ injection s rev∈(arbitration (round g raw).prep).1 ∧
      atCursor (step y e) (address e C.source)=.trail ∧
      atCursor (step y e) (address e dst)=.forward f ∧
      after.mobile=.data value ∧ after.frozen=.empty := by
  dsimp only
  intro mem hd src atJ old healthy opcode inside enabled frozen
  have cut := generated_cut_vacant hp chart sep history rev layout emptyAtIssue
  have current := BStarGeneratedTapeCuts.at_end hp history
  exact departure_at_cut hp chart e (sep e) j current C dst f s rev value
    mem hd src atJ old healthy opcode inside enabled frozen cut

/-- The busy-flight version exposes the next chart token and the exact
source lane update after a selected directed link. -/
theorem busy_landing {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    {w : List (Fin n)} {j : Nat}
    (history : BusyOnly hp base (fun k=>S.getD k fall) len 10 x (.out 0) w (.out j))
    (empty : MobilesEmpty hp base x o.val)
    (e : Fin n) (C : CommandClaim) (dst : AtK) (f : Payload)
    (s : Side) (rev : Bool) (value : BitVec 36) :
    let y := run x w
    let g := oldPair B y e
    let raw := ((y e).long,(y (rightNeighbor e)).long)
    let ln := Sheet.index (sourceLane rev)
    C∈orderedCommands g → C.destination=some dst →
    C.source=⟨s,sourceOccurrence rev⟩ → S.getD j fall=(site e s,sourceOccurrence rev) →
    S.getD (j+1) fall=address e dst →
    bound g (readK raw) C.source=.forward f →
    f.fault=0 → f.opcode.toNat=10 → (geometry g s).inside=true →
    (readLane ln (y (site e s)).long).gate=true →
    (readLane ln (y (site e s)).long).frozen=.data value →
    let after := readLane ln (step y e (site e s)).long
    project (fun k=>S.getD k fall) (step y e) (j+1)=.forward f ∧
      after.mobile=.data value ∧ after.frozen=.empty := by
  dsimp only
  intro mem hd src atJ next old healthy opcode inside enabled frozen
  have cut := busy_cut_vacant hp chart sep history rev 0 j rfl rfl
    (cut_from_owner_empty hp chart rev empty)
  have current := BStarAcquireHistoryReturn.busy_end hp history
  have ⟨_,win,_,landed,_,_⟩ := departure_at_cut hp chart e (sep e) j current C dst f s rev value
    mem hd src atJ old healthy opcode inside enabled frozen cut
  have token : project (fun k=>S.getD k fall) (step (run x w) e) (j+1)=.forward f :=
    (congrArg (atCursor (step (run x w) e)) next).trans landed
  exact ⟨token,busy_cut_inject hp chart sep history empty e s rev value atJ win enabled frozen⟩

end L4.Height.FreshInjection
