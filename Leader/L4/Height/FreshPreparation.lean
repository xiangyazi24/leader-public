import Leader.L4.BStarCopyDownstream
import Leader.L4.BStarCopyCleanupOriginal
import Leader.L4.BStarCopyRightReadyWord
import Leader.L4.BStarCopyLeftLoadToInject
import Leader.L4.BStarCopyRightLoadToInject

namespace L4.Height.FreshPreparation
open AllSizeProtocol BStarTrace BStarLongClaims BStarLongWork BStarLongToken
open BStarLongCommand BStarLongCommandData BStarLongPrep BStarLongPackets
open BStarH6WordChart BStarLongFixedRouting BStarResetChartTouch BStarAcquireVisitOrder
open BStarAcquireLiteralChain BStarAcquireAnchors BStarClearanceDataChart
open BStarResetMarkAdapter BStarResetRailRing BStarGeneratedOwner BStarOwnerLaunchOrigin
open BStarCopyInjection BStarCopyEntryGates BStarCopyDownstream BStarCopyOwnedFrozen
open BStarCopyOperand BStarLongFiberOwner
open BStarCopyCleanupWindow BStarCopyCleanupFrame BStarCopyCleanupOriginal
open BStarSeparatingRail BStarSeparatorControl BStarResetSchedule
open BStarCopyAttemptBand BStarGeneratedBandScan BStarLongDoor BStarClearanceSource
open BStarLongTransport BStarLongEvents BStarAcquireForwardTrace BStarResetChartIndex

set_option maxRecDepth 4096
set_option maxHeartbeats 1600000

/-- An offered STOP, CLEAR or ENABLE cannot be cancelled. This is
independent of lane contents, including errors from an older attempt. -/
theorem setup_no_cancel (g : Pair LongGeometry) (raw : Pair (BitVec LW))
    (C : CommandClaim) (f : Payload)
    (op : f.opcode.toNat=6 ∨ f.opcode.toNat=7 ∨ f.opcode.toNat=9)
    (mem : (C,.advance f)∈gated g raw) :
    C.source∉(round g raw).faults := by
  intro F
  change C.source∈prepFaults (view raw) (round g raw).prep at F
  simp only [prepFaults,BStarResetNoFault.arb_no_losers g raw,List.map_nil,List.nil_append] at F
  obtain ⟨a,M,origin⟩ := List.mem_map.mp F
  obtain ⟨win,bad⟩ := List.mem_filter.mp M
  obtain ⟨D,q,_,Dmem,_,kind,_,source,_,_⟩ := winner_origin g raw a win
  have Cg := (BStarLongLiteral.gated_mem g raw C _).mp mem
  have Dg := (BStarLongLiteral.gated_mem g raw D _).mp Dmem
  have same := BStarResetNoFault.origin_unique g D C Dg.1 Cg.1 (source.symm.trans origin)
  subst D
  have eq := BStarLongCommand.Offer.advance.inj (Dg.2.trans Cg.2.symm)
  subst q
  rcases op with stop|clear|enable
  · have E : a.claim.op=.stop := (Option.some.inj ((show prepOf f.opcode.toNat=some .stop by simp [stop,prepOf]).symm.trans kind)).symm
    simp [selectedEffects,E,effects] at bad
  · have E : a.claim.op=.clear := (Option.some.inj ((show prepOf f.opcode.toNat=some .clear by simp [clear,prepOf]).symm.trans kind)).symm
    simp [selectedEffects,E,effects] at bad
  · have E : a.claim.op=.enable := (Option.some.inj ((show prepOf f.opcode.toNat=some .enable by simp [enable,prepOf]).symm.trans kind)).symm
    simp [selectedEffects,E,effects] at bad

private def geomOf (h i l : Bool) : LongGeometry :=
  ⟨⟨false,false,false,false,false,h⟩,i,l,0,false⟩

/-- A selected data source is always active. This is needed when a
vacancy proof starts from the physical CLEAR image of active sheets. -/
theorem selected_source_active (g : Pair LongGeometry) (rsv : List (At Sheet))
    (d : DataClaim) (M : d∈orderedData g rsv) :
    activeSheet (geometry g d.source.side) d.source.occurrence=true := by
  let test (g : Pair LongGeometry) (d : DataClaim) :=
    activeSheet (geometry g d.source.side) d.source.occurrence
  have all (I L H J : Bool) :
      (dataClaims (geomOf false I L,geomOf H J false)).all
        (test (geomOf false I L,geomOf H J false))=true := by
    cases I <;> cases L <;> cases H <;> cases J <;> decide +kernel
  obtain ⟨a,b⟩ := g
  let small := (geomOf false a.inside a.last,geomOf b.axes.h6 b.inside false)
  have raw := BStarLongFenceTopology.selected_data_raw (a,b) rsv d M
  change d∈dataClaims small at raw
  have active := List.all_eq_true.mp (all a.inside a.last b.axes.h6 b.inside) d raw
  cases H : d.source.side <;> cases S : d.source.occurrence <;>
    simp [test,geometry,activeSheet,geomOf,H,S] at active ⊢ <;> exact active

private theorem prep_source (g : LongGeometry) (j : Fin 11) (rev : Bool)
    (H : sourceLane rev∈prepSites g j .inject) : j=sourceOccurrence rev := by
  have all (inside rev : Bool) :
      ∀ j : Fin 11, sourceLane rev∈prepSites (geomOf false inside false) j .inject →
        j=sourceOccurrence rev := by
    cases inside <;> cases rev <;> decide +kernel
  exact all g.inside rev j H

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step (n:=n) B
local notation "run" => BStarResetSchedule.run step

private theorem active_of_layout {base x : X} (i : Fin n) (sh : Sheet)
    (layout : Layout B base i=Layout B x i) :
    activeSheet (longGeometry B (base i)) sh=activeSheet (longGeometry B (x i)) sh := by
  have inside := congrArg (fun v : Bool×Bool×Bool=>v.2.1) layout
  cases sh <;> first | rfl | exact inside

/-- Only unvisited active sources require a vacant mobile. Inactive OUT
RS slots are not targets of CLEAR and receive no selected data claim. -/
def ActiveVacancy (base x : X) (S : List (Pos n)) (fall : Pos n)
    (len cut : Nat) (rev : Bool) : Prop :=
  ∀ i, Unvisited S fall len cut rev i →
    activeSheet (longGeometry B (base i)) (sourceLane rev)=true →
    (readLane (Sheet.index (sourceLane rev)) (x i).long).mobile=.empty

private theorem no_pending_inject {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (e : Fin n) (sep : e≠rightNeighbor e)
    (rev : Bool) (k k' : Nat)
    (old : Current hp base (fun j=>S.getD j fall) len x (.busy 10 (.out k)))
    (post : Current hp base (fun j=>S.getD j fall) len (step x e) (.busy 10 (.out k')))
    (mono : k≤k') (a : At Sheet) (shr : a.occurrence=sourceLane rev)
    (pending : Unvisited S fall len k' rev (site e a.side)) :
    ∀ pr∈(arbitration (round (oldPair B x e) ((x e).long,(x (rightNeighbor e)).long)).prep).1,
      pr.claim.lane=a → pr.claim.op≠.inject := by
  intro pr win lane op
  let g := oldPair B x e
  let raw : Pair (BitVec LW) := ((x e).long,(x (rightNeighbor e)).long)
  obtain ⟨C,_,q,_,move,_,_,_,side,sites⟩ := winner_origin g raw pr win
  have sideEq : C.source.side=a.side := side.symm.trans (congrArg At.side lane)
  have idx : C.source.occurrence=sourceOccurrence rev := by
    rw [op,lane,shr] at sites
    exact prep_source _ _ rev sites
  obtain ⟨j,kj,jLen,atJ⟩ := pending
  have atC : S.getD j fall=address e C.source := by rw [atJ]; simp [address,idx,sideEq]
  have L := chart.length
  have memS : S.getD j fall∈S := by
    rw [←List.getElem_eq_getD (h:=show j<S.length by omega)]
    exact List.getElem_mem _
  have own : commandOwner (oldH6 B base) (site e C.source.side) C.source.occurrence=o.val := by
    have own := (chart.entries _ memS).2
    rwa [atC] at own
  obtain ⟨d,eq,atD⟩ := actual_owner_departure hp chart old.1.1 e C q (.out k) move own old.2.1 old.2.2
  have kd := Cursor.out.inj eq
  subst d
  have sameJ := (List.getD_inj (by have := old.2.1.1; omega) (by omega) chart.nodup).mp (atD.trans atC.symm)
  have afterJ : j=k' := by omega
  have hmem : C∈orderedCommands g := by
    rw [←actualOffers_claims g raw]
    exact List.mem_map.mpr ⟨_,move,rfl⟩
  have dest : ∃ d,C.destination=some d := by
    rcases selected_endpoint_or_link B base x hh old.1.1 o e C hmem own with H|H|⟨d,h,_⟩
    · have E := (selected_door g C hmem H.1).1
      rw [E] at idx
      cases rev <;> contradiction
    · have noDoor : C.kind≠.door := by rw [H.1]; decide
      have J := (BStarAcquireChainEndpoints.terminal g C hmem H.2.1 noDoor).2.2.2
      rw [idx] at J
      cases rev <;> contradiction
    · exact ⟨d,h⟩
  obtain ⟨z,dst⟩ := dest
  have shp := BStarAcquireReturn.link_shape g C z hmem dst
  have work := (BStarClearanceForward.move_lands g raw C q z dst move (Ne.symm shp.1)).1
  have joined := BStarAcquireReturn.joined_reads k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
    (x e,x (rightNeighbor e)) C.source (fun h z=>(shp.2.2 h z).elim)
  have rawT : readK (patchPair (longWork g raw) raw) C.source=.trail :=
    (congrArg BStarLongToken.decode work).trans (decode_encode _)
  have atT := (new_read B x e sep C.source).symm.trans (joined.trans rawT)
  obtain ⟨live,F⟩ := post.2.1.2.1
  change atCursor (step x e) (S.getD k' fall)=.forward live at F
  rw [←afterJ,atC,atT] at F
  cases F

/-- Active pending vacancy survives every actual outward step. A
selected incoming source is active and later on the command chart. -/
theorem active_vacancy_step {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (e : Fin n) (sep : e≠rightNeighbor e)
    (k k' : Nat) (rev : Bool)
    (old : Current hp base (fun j=>S.getD j fall) len x (.busy 10 (.out k)))
    (post : Current hp base (fun j=>S.getD j fall) len (step x e) (.busy 10 (.out k')))
    (mono : k≤k') (V : ActiveVacancy hp base x S fall len k rev) :
    ActiveVacancy hp base (step x e) S fall len k' rev := by
  intro i pending active
  have earlier (i : Fin n) {a b : Nat} (ab : a≤b) (H : Unvisited S fall len b rev i) :
      Unvisited S fall len a rev i := by
    obtain ⟨j,J,L,A⟩ := H
    exact ⟨j,Nat.le_trans ab J,L,A⟩
  have empty := V i (earlier i mono pending) active
  have touched (s : Side) (loc : site e s=i) :
      (readLane (Sheet.index (sourceLane rev)) (step x e i).long).mobile=.empty := by
    subst i
    let a : At Sheet := ⟨s,sourceLane rev⟩
    let g := oldPair B x e
    let raw : Pair (BitVec LW) := ((x e).long,(x (rightNeighbor e)).long)
    have noIn (d : DataClaim) (mem : d∈orderedData g (reserved (round g raw).prep))
        (D : d.destination=some a) : (view raw d.source).mobile=.empty := by
      obtain ⟨same,later⟩ := incoming_later hp chart old.1.1 e rev k'
        (reserved (round g raw).prep) d a mem D rfl pending
      have activeCurrent := selected_source_active g _ d mem
      rw [same] at activeCurrent
      have atSource : activeSheet (longGeometry B (x (site e d.source.side))) (sourceLane rev)=true := by
        cases H : d.source.side <;> simpa [g,geometry,oldPair,site,H] using activeCurrent
      have activeBase := (active_of_layout hp (site e d.source.side) (sourceLane rev)
        (old.1.1 _)).trans atSource
      have empty := V (site e d.source.side) (earlier _ (by omega) later) activeBase
      cases ds : d.source.side <;> simpa [view,site,lane,BStarTrace.lane,raw,ds,same] using empty
    have H := pair_vacancy_local hp (x e,x (rightNeighbor e)) a
      (by cases s <;> exact empty)
      (no_pending_inject hp chart e sep rev k k' old post mono a rfl pending) noIn
    cases s <;> simpa [a,Pair.map,view,site,lane,BStarTrace.lane,AllSizeS1Geometry.step,Ne.symm sep] using H
  by_cases l : i=e
  · exact touched .left l.symm
  · by_cases r : i=rightNeighbor e
    · exact touched .right r.symm
    · rwa [show step x e i=x i from by simp [AllSizeS1Geometry.step,l,r]]

private theorem from_drained {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (rev : Bool)
    (same : ∀ i,Layout B base i=Layout B x i)
    (empty : DrainedOwner hp base x o.val) :
    ActiveVacancy hp base x S fall len 0 rev := by
  intro i pending active
  obtain ⟨j,_,h,J⟩ := pending
  have L := chart.length
  have mem : S.getD j fall∈S := by
    rw [←List.getElem_eq_getD (h:=show j<S.length by omega)]
    exact List.getElem_mem _
  have own := (chart.entries _ mem).2
  rw [J] at own
  have dataOwn : dataOwner (oldH6 B base) i (sourceLane rev)=o.val := by
    have sameDispl : dataDispl (sourceLane rev)=cmdDispl (sourceOccurrence rev) := by
      cases rev <;> decide
    unfold dataOwner
    rw [sameDispl]
    exact own
  exact (empty i (sourceLane rev)
    ((active_of_layout hp i (sourceLane rev) (same i)).symm.trans active) dataOwn).1

theorem busy_active_vacancy {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    {z d : Cursor} {w : List (Fin n)}
    (H : BusyOnly hp base (fun j=>S.getD j fall) len 10 x z w d)
    (rev : Bool) :
    ∀ k l, z=.out k → d=.out l → ActiveVacancy hp base x S fall len k rev →
      ActiveVacancy hp base (run x w) S fall len l rev := by
  revert sep
  induction H with
  | nil _ =>
    intro _ k l oldOut newOut V
    have eq := Cursor.out.inj (oldOut.symm.trans newOut)
    subst l
    exact V
  | @cons raw z d final e w I E tail ih =>
    intro sep k l Z D V
    subst z
    obtain ⟨j,N⟩ := BStarAcquireHistorySample.busy_no_back_to_out hp tail ⟨l,D⟩
    subst d
    have adv : Advance len (.out k) (.out j) := by
      cases E with
      | transit _ _ _ _ seen =>
        cases seen with
        | cons _ _ K _ rest => cases rest; exact K
    have mono : k≤j := by cases adv <;> omega
    exact ih sep j l rfl D (active_vacancy_step hp chart e (sep e) k j rev I (busy_start hp tail) mono V)

/-- The genuine ENABLE tour has opened every active owned lane by the
specified generated PC10 cut. The same open gates persist into INJECT. -/
theorem gates_after_enable {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    {m : Mode} {w : List (Fin n)}
    (G : GeneratedOwner hp base (fun j=>S.getD j fall) len x .idle w m)
    (scope : ∀ a b,w=a++b →
      (∀ i,Layout B base i=Layout B (run x a) i) ∧ Band (run x a) (S.getD 0 fall).1)
    (init : pc x (S.getD 0 fall).1=6)
    (done : 10≤pc (run x w) (S.getD 0 fall).1) :
    ∀ i sh, activeSheet (longGeometry B (base i)) sh=true →
      dataOwner (oldH6 B base) i sh=o.val →
      (readLane (Sheet.index sh) (run x w i).long).gate=true := by
  obtain ⟨pre,ack,tail,W,H,event,accepted⟩ :=
    BStarCopyCleanupCuts.accepted_cut hp chart sep G scope 9 (by omega) (by omega)
  intro i sh active own
  obtain ⟨before,e,after,offer,E,ena,loc,lane,win⟩ :=
    BStarCopyRightReadyWord.enabled_after_accept9 hp chart sep H event accepted i sh active own
  have marked : w=before++e::(after++ack::tail) := by
    rw [W,E,List.append_assoc,List.cons_append]
  have enabled : BStarCopyRightReady.EnabledOn hp x w i sh :=
    ⟨before,e,after++ack::tail,offer,marked,ena,loc,lane,win⟩
  exact BStarCopyRightReady.gate_from_enabled hp chart sep w m G scope i sh own enabled

/-- STOP, CLEAR and ENABLE give a drained, open active owner footprint
at the actual idle ISSUE10 cut. Inactive lane fields play no part. -/
theorem drained_and_open_at_issue {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    {w : List (Fin n)}
    (G : GeneratedOwner hp base (fun j=>S.getD j fall) len x .idle w .idle)
    (scope : ∀ a b,w=a++b →
      (∀ i,Layout B base i=Layout B (run x a) i) ∧ Band (run x a) (S.getD 0 fall).1)
    (init : pc x (S.getD 0 fall).1=6)
    (done : pc (run x w) (S.getD 0 fall).1=10) :
    DrainedOwner hp base (run x w) o.val ∧
      ∀ i sh,activeSheet (longGeometry B (base i)) sh=true →
        dataOwner (oldH6 B base) i sh=o.val →
        (readLane (Sheet.index sh) (run x w i).long).gate=true := by
  exact ⟨drained_original_issue10 hp chart sep G scope (by omega) done,
    gates_after_enable hp chart sep G scope init (by omega)⟩

/-- The literal launch reads an idle owner chart. It cannot put any
mobile into its own active COPY footprint on the launch mark. -/
theorem launch_preserves_drain {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (e : Fin n) (sep : e≠rightNeighbor e)
    (oldLayout : ∀ i,Layout B base i=Layout B x i)
    (newLayout : ∀ i,Layout B base i=Layout B (step x e) i)
    (idle : Current hp base (fun j=>S.getD j fall) len x .idle)
    (drained : DrainedOwner hp base x o.val) :
    DrainedOwner hp base (step x e) o.val := by
  apply BStarCopyDrainedHistory.drained_step hp e sep o.val oldLayout newLayout drained
  intro a win owner
  have A := safe_idle hp chart oldLayout e (site e a.claim.lane.side) a.claim.lane.occurrence owner idle.2
  have E : a.claim.lane=⟨a.claim.lane.side,a.claim.lane.occurrence⟩ := rfl
  rcases A a.claim.lane.side rfl a win E with H|H|H <;> rw [H] <;> decide

/-- A generated ongoing INJECT sees open gates and empty mobiles at all
its unvisited active source positions. The actual CLEAR footprint is
sufficient even when inactive bytes were arbitrary at ISSUE6. -/
theorem active_sources_on_inject {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    {w : List (Fin n)} {j : Nat}
    (history : GeneratedOwner hp base (fun k=>S.getD k fall) len x .idle w (.busy 10 (.out j)))
    (scope : ∀ a b,w=a++b →
      (∀ i,Layout B base i=Layout B (run x a) i) ∧ Band (run x a) (S.getD 0 fall).1)
    (init : pc x (S.getD 0 fall).1=6) (rev : Bool) :
    ActiveVacancy hp base (run x w) S fall len j rev ∧
      ∀ i sh,activeSheet (longGeometry B (base i)) sh=true →
        dataOwner (oldH6 B base) i sh=o.val →
        (readLane (Sheet.index sh) (run x w i).long).gate=true := by
  have now := BStarGeneratedTapeCuts.at_end hp history
  have opened := gates_after_enable hp chart sep history scope init
    (Nat.le_of_eq now.1.2.2.2.symm)
  refine ⟨?_,opened⟩
  obtain ⟨pre,suffix,launch,W,_,L,P,Bu⟩ := from_idle hp history
  obtain ⟨m,G,old⟩ := BStarCopyGateAuthority.history_prefix hp pre (launch::suffix) (W ▸ history)
  have oldIdle : m=.idle := by
    cases m with
    | idle => rfl
    | busy op z =>
      exact ((by decide : (1:Nat)≠2) (L.1.2.symm.trans old.1.2.2.1)).elim
  subst m
  have preScope (a b : List (Fin n)) (E : pre=a++b) :
      (∀ i,Layout B base i=Layout B (run x a) i) ∧ Band (run x a) (S.getD 0 fall).1 :=
    scope a (b++launch::suffix) (by rw [W,E,List.append_assoc])
  have oldLayout := (scope pre (launch::suffix) W).1
  have newLayout : ∀ i,Layout B base i=Layout B (step (run x pre) launch) i := by
    have Q := (scope (pre++[launch]) suffix (by rw [W,List.append_assoc] <;> rfl)).1
    rwa [BStarResetSchedule.run_append] at Q
  have empty := drained_original_issue10 hp chart sep G preScope (by omega) P
  have postDrain := launch_preserves_drain hp chart launch (sep launch) oldLayout newLayout old empty
  have vac := busy_active_vacancy hp chart sep Bu rev 0 j rfl rfl
    (from_drained hp chart rev newLayout postDrain)
  rw [W,BStarResetSchedule.run_append]
  exact vac

/-- The earlier selected LOAD and current INJECT run on the same tape.
At an active INJECT source they give the frozen captured bank digit,
an open gate, and a vacant old mobile. No outcome of INJECT is used. -/
theorem prepared_from_load {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (lead wLoad middle wInject : List (Fin n)) (load : Fin n) (s : Side) (rev : Bool)
    (C : CommandClaim) (k j : Nat) (kl : k≤len) (jl : j≤len)
    (loadLoc : address load C.source=S.getD k fall)
    (loadSource : C.source=⟨s,if rev then 2 else 0⟩)
    (injectLoc : S.getD j fall=(site load s,sourceOccurrence rev))
    (sameRight : rev=true → j=k)
    (selected : C∈orderedCommands (oldPair B (run x lead) load))
    (noDoor : C.kind≠.door)
    (advanced : rev=true → ∃ f, (C,.advance f)∈actualOffers (oldPair B (run x lead) load)
      (((run x lead) load).long,((run x lead) (rightNeighbor load)).long))
    (inside : (geometry (oldPair B (run x lead) load) s).inside=true)
    (own : dataOwner (oldH6 B base) (site load s) (sourceLane rev)=o.val)
    (active : activeSheet (longGeometry B (base (site load s))) (sourceLane rev)=true)
    (before : GeneratedOwner hp base (fun t=>S.getD t fall) len x .idle lead (.busy 8 (.out k)))
    (loadEvent : Event hp (fun t=>S.getD t fall) len (run x lead) load
      (.busy 8 (.out k)) (.busy 8 (.out (k+1))))
    (restLoad : BusyOnly hp base (fun t=>S.getD t fall) len 8 (step (run x lead) load)
      (.out (k+1)) wLoad (.back 0))
    (M : BStarCopyRightLoadToInject.OwnMiddle hp base x (fun t=>S.getD t fall) len
      ((lead++[load])++wLoad) middle)
    (bInject : BusyOnly hp base (fun t=>S.getD t fall) len 10
      (run x (((lead++[load])++wLoad)++middle)) (.out 0) wInject (.out j))
    (history : GeneratedOwner hp base (fun t=>S.getD t fall) len x .idle
      ((((lead++[load])++wLoad)++middle)++wInject) (.busy 10 (.out j)))
    (scope : ∀ a b, ((((lead++[load])++wLoad)++middle)++wInject)=a++b →
      (∀ i,Layout B base i=Layout B (run x a) i) ∧ Band (run x a) (S.getD 0 fall).1)
    (init : pc x (S.getD 0 fall).1=6) :
    let old := readLane (Sheet.index (sourceLane rev))
      (run x ((((lead++[load])++wLoad)++middle)++wInject) (site load s)).long
    old.gate=true ∧ old.mobile=.empty ∧
      ∃ (pre post : List (Fin n)) (launch : Fin n) (bank : Fin 3),
        lead=pre++launch::post ∧ launch=RearTrace.predecessor (S.getD 0 fall).1 ∧
        bank.val=(captures.read ((run x pre) (S.getD 0 fall).1).long).toNat /
          (if rev then 1 else 16) % 4 ∧
        old.frozen=oldBankPacket ((run x lead) (site load s)).long bank := by
  dsimp only
  obtain ⟨empty,openGates⟩ := active_sources_on_inject hp chart sep history scope init rev
  exact ⟨openGates _ _ active own,empty _ ⟨j,Nat.le_refl _,jl,injectLoc⟩ active,by
    have fiber (a b : List (Fin n)) (W : ((((lead++[load])++wLoad)++middle)++wInject)=a++b) :
        ∀ i,Layout B base i=Layout B (run x a) i := (scope a b W).1
    cases rev with
    | false =>
      obtain ⟨pre,post,launch,bank,E,L,Q,F⟩ := BStarCopyLeftLoadToInject.original_to_inject hp chart sep
        lead wLoad middle wInject load s C k j kl jl injectLoc loadLoc loadSource selected noDoor
        inside own before loadEvent restLoad M bInject fiber
      exact ⟨pre,post,launch,bank,E,L,Q,F⟩
    | true =>
      have atRight := sameRight rfl
      subst j
      obtain ⟨f,win⟩ := advanced rfl
      obtain ⟨pre,post,launch,bank,E,L,Q,F⟩ := BStarCopyRightLoadToInject.original_to_inject hp chart sep
        lead wLoad middle wInject load s C f k kl loadLoc loadSource selected noDoor
        win inside own before loadEvent restLoad M bInject fiber
      exact ⟨pre,post,launch,bank,E,L,by simpa using Q,F⟩⟩

end L4.Height.FreshPreparation
