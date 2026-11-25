import Leader.L4.BStarCopyLeftRecovered
import Leader.L4.BStarCopyRightWrappedPostAck
import Leader.L4.BStarCopyLeftPreinject
import Leader.L4.BStarCopyRightPreinject
import Leader.L4.BStarCopyRightSetupMiddle
import Leader.L4.BStarCopySetupReplay
import Leader.L4.BStarCopyLeftReleaseCapture
import Leader.L4.BStarCopyRightWrappedLoadCoverage
import Leader.L4.Height.FreshInjection
import Leader.L4.Height.FreshPreparation
import Leader.L4.Height.AdmissionTour

namespace L4.Height.FreshOrderedPrefix
open AllSizeProtocol BStarTrace BStarLongWork BStarLongClaims BStarLongToken
open BStarLongCommand BStarLongEvents BStarLongPackets BStarLongTransport
open BStarH6WordChart BStarAcquireVisitOrder BStarAcquireLiteralChain BStarAcquireAnchors
open BStarLongFixedRouting BStarResetMarkAdapter BStarClearanceDataChart
open BStarGeneratedOwner BStarOwnerLaunchOrigin BStarSeparatingRail BStarGeneratedBandScan
open BStarCopyFenceCuts BStarCopyFenceSaturation BStarCopyMarkedLedger
open BStarCopyRightStrip (addr rail)
open BStarCopyLeftDeposit (headFirst)
open BStarCopyLeftPending (pending)
open BStarCopyRightMark (stripWord)
open BStarCopyRightMixed (planOf)
open BStarLongCommandData BStarLongPrep BStarLongLiteral BStarResetQuiet
open BStarCopyInjection (sourceLane sourceOccurrence)
open BStarResetSchedule (Seen)
open BStarSeparatorControl (anyTag)
open BStarResetRailRing (old_read new_read)
open BStarResetChartTouch BStarAcquireForwardTrace
open BStarLongDoor BStarClearanceSource
open BStarLongFiberOwner (cmdDispl dataDispl)
open BStarCopyRightLoadToInject (OwnMiddle)

set_option maxRecDepth 4096
set_option maxHeartbeats 2400000

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step (n:=n) B
local notation "run" => BStarResetSchedule.run step

private theorem append_generated {base x : X} {slots : Nat→Pos n} {len : Nat}
    {a b c : Mode} {u v : List (Fin n)}
    (P : GeneratedOwner hp base slots len x a u b)
    (Q : GeneratedOwner hp base slots len (run x u) b v c) :
    GeneratedOwner hp base slots len x a (u++v) c := by
  induction P with
  | endpoint _ => exact Q
  | next I E _ ih => exact .next I E (ih Q)

private theorem split_busy {base x : X} {slots : Nat→Pos n} {len op : Nat}
    {z d : Cursor} (u v : List (Fin n))
    (P : BusyOnly hp base slots len op x z (u++v) d) :
    ∃ mid, BusyOnly hp base slots len op x z u mid ∧
      BusyOnly hp base slots len op (run x u) mid v d := by
  induction u generalizing x z with
  | nil => exact ⟨z,.nil (busy_start hp P),P⟩
  | cons e u ih =>
    cases P with
    | cons I E tail =>
      obtain ⟨mid,left,right⟩ := ih tail
      exact ⟨mid,.cons I E left,right⟩

/-- An actual selected departure determines the endpoint of the
same busy tape prefix. The location alone never identifies its time. -/
theorem prefix_to_release {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall)
    {z d : Cursor} {u v : List (Fin n)} (e : Fin n)
    (P : BusyOnly hp base (fun j=>S.getD j fall) len 10 x z (u++e::v) d)
    (j : Nat) (jL : j≤len) (C : CommandClaim) (f : Payload)
    (position : S.getD j fall=address e C.source)
    (move : (C,.advance f)∈actualOffers (oldPair B (run x u) e)
      (((run x u) e).long,((run x u) (rightNeighbor e)).long)) :
    BusyOnly hp base (fun t=>S.getD t fall) len 10 x z u (.out j) := by
  obtain ⟨mid,left,_⟩ := split_busy hp u (e::v) P
  have current := BStarAcquireHistoryReturn.busy_end hp left
  have L := chart.length
  have mem : S.getD j fall∈S := by
    rw [←List.getElem_eq_getD (h:=show j<S.length by omega)]
    exact List.getElem_mem _
  have own := (chart.entries _ mem).2
  rw [position] at own
  obtain ⟨k,K,loc⟩ := BStarCopyOwnedFrozen.actual_owner_departure hp chart current.1.1
    e C f mid move own current.2.1 current.2.2
  subst mid
  have kL := current.2.1.1
  have eq := (List.getD_inj (show k<S.length by omega) (show j<S.length by omega)
    chart.nodup).mp (loc.trans position.symm)
  subst k
  exact left

/-- The digit table is sampled at the genuine INJECT launch. A
source's unresolved frozen field is never used as a release label. -/
def frozenDigit (a : Lane) : BitVec 36 :=
  match a.frozen with
  | .data d => d
  | _ => 0

private theorem read_frozen {a b : Lane} (same : a.frozen=b.frozen)
    (valid : ∃ d : BitVec 36,a.frozen=.data d) :
    a.frozen=.data (frozenDigit b) := by
  obtain ⟨d,V⟩ := valid
  have old := same.symm.trans V
  simp [frozenDigit,old,V]

/-- The concrete opcode-10 command is a unit message. -/
def injectUnit : Payload := ⟨0,10,0,0,0⟩

private theorem inject_source {g : LongGeometry} {j : Fin 11} {sh : Sheet}
    (M : sh∈prepSites g j .inject) :
    g.inside=true ∧ ∃ rev : Bool, j=sourceOccurrence rev := by
  by_cases inside : g.inside=true
  · refine ⟨inside,?_⟩
    by_cases left : j=5
    · exact ⟨false,left⟩
    · by_cases right : j=2
      · exact ⟨true,right⟩
      · simp [prepSites,inside,left,right] at M
  · have N := Bool.eq_false_iff.mpr inside
    simp [prepSites,N] at M

/-- The original port is ready on its old immutable pair if it is a
source cell. This is evaluated before the command can be cancelled. -/
def ReadyPort (g : Pair LongGeometry) (raw : Pair (BitVec LW)) (C : CommandClaim) : Prop :=
  ∀ rev, C.source.occurrence=sourceOccurrence rev →
    (geometry g C.source.side).inside=true →
    let a := view raw ⟨C.source.side,sourceLane rev⟩
    a.gate=true ∧ a.mobile=.empty ∧ ∃ d : BitVec 36,a.frozen=.data d

/-- On a selected ordinary or prepared opcode-10 row, the old source
unit survives preparation. The argument obtains the actual provenance
of a putative cancelling offer without using any postmark token. -/
theorem unit_offer (g : Pair LongGeometry) (raw : Pair (BitVec LW))
    (C : CommandClaim) (mem : C∈orderedCommands g) (nonDoor : C.kind≠.door)
    (old : readK raw C.source=.forward injectUnit)
    (before : ReadyPort g raw C) :
    (C,.advance injectUnit)∈actualOffers g raw := by
  have boundOld : bound g (readK raw) C.source=.forward injectUnit := by
    unfold bound
    rw [old]
    exact (FreshInjection.inject_unit_packet _ _).1
  have gatedC := FreshInjection.gated_inject g raw C injectUnit mem nonDoor boundOld rfl
  apply FreshInjection.actual_inject_offer g raw C injectUnit gatedC rfl
  intro fault
  change C.source∈prepFaults (view raw) (round g raw).prep at fault
  have saved := fault
  simp only [prepFaults,BStarResetNoFault.arb_no_losers g raw,List.map_nil,List.nil_append] at fault
  obtain ⟨a,found,origin⟩ := List.mem_map.mp fault
  obtain ⟨D,f,_,HD,_,op,_,src,_,siteMem⟩ :=
    BStarCopyOwnedFrozen.winner_origin g raw a (List.mem_filter.mp found).1
  have gateD := (gated_mem g raw D _).mp HD
  have gateC := (gated_mem g raw C _).mp gatedC
  have same := BStarResetNoFault.origin_unique g D C gateD.1 gateC.1 (src.symm.trans origin)
  subst D
  have samePayload := BStarLongCommand.Offer.advance.inj (gateD.2.trans gateC.2.symm)
  subst f
  have inj : a.claim.op=.inject :=
    (Option.some.inj (show some .inject=some a.claim.op from op)).symm
  rw [inj] at siteMem
  obtain ⟨ins,rev,source⟩ := inject_source siteMem
  obtain ⟨openGate,empty,value,frozen⟩ := before rev source ins
  have originEq : C.source=⟨C.source.side,sourceOccurrence rev⟩ := by
    calc
      C.source=⟨C.source.side,C.source.occurrence⟩ := rfl
      _=⟨C.source.side,sourceOccurrence rev⟩ := by rw [source]
  exact FreshInjection.inject_not_cancelled g raw C injectUnit C.source.side rev value
    originEq rfl ins gatedC openGate frozen empty saved

/-- The licensed old source advances the unit on this actual joined
link. No healthy postcondition at its target is assumed. -/
theorem unit_link (x : X) (e : Fin n) (sep : e≠rightNeighbor e)
    (C : CommandClaim) (dst : AtK)
    (selected : C∈orderedCommands (oldPair B x e)) (dest : C.destination=some dst)
    (old : readK ((x e).long,(x (rightNeighbor e)).long) C.source=.forward injectUnit)
    (ready : ReadyPort (oldPair B x e) ((x e).long,(x (rightNeighbor e)).long) C) :
    atCursor (step x e) (address e dst)=.forward injectUnit := by
  let g := oldPair B x e
  let raw : Pair (BitVec LW) := ((x e).long,(x (rightNeighbor e)).long)
  have nonDoor : C.kind≠.door := by
    rw [(BStarAcquireReturn.link_shape g C dst selected dest).2.1]
    decide
  exact (FreshInjection.inject_command_link hp x e sep C dst injectUnit selected dest rfl
    (unit_offer g raw C selected nonDoor old ready)).2

theorem unit_turn {x : X} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (e : Fin n) (sep : e≠rightNeighbor e)
    (T : onTerminal hp x e (fun j=>S.getD j fall) len)
    (F : project (fun j=>S.getD j fall) x len=.forward injectUnit) :
    project (fun j=>S.getD j fall) (step x e) len=.reply injectUnit := by
  obtain ⟨C,mem,kind,dst,occ,pos⟩ := T
  let g := oldPair B x e
  let raw : Pair (BitVec LW) := ((x e).long,(x (rightNeighbor e)).long)
  have old : readK raw C.source=.forward injectUnit :=
    (old_read x e C.source).trans ((congrArg (atCursor x) pos).symm.trans F)
  have ready : ReadyPort g raw C := by
    intro rev source _
    have j := congrArg Fin.val source
    rw [occ] at j
    cases rev with
    | false => exact ((by decide : (10:Nat)≠5) j).elim
    | true => exact ((by decide : (10:Nat)≠2) j).elim
  have sel := unit_offer g raw C mem (by rw [kind]; decide) old ready
  have post := terminal_finish g raw C injectUnit dst sel
  have joined := BStarAcquireReturn.joined_reads k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
    (x e,x (rightNeighbor e)) C.source (by intro _ zero; omega)
  have carried : BStarClearanceForward.carried g raw C injectUnit=injectUnit := by
    have node : BStarLongArithmetic.nodeOf 10=none := by decide
    simp [injectUnit,BStarClearanceForward.carried,BStarLongArithmetic.visit,node,
      BStarLongOutgoing.execute,BStarLongOutgoing.hold,stageOp,sealOp,commitOp]
  have read : readK (patchPair (longWork g raw) raw) C.source=.reply injectUnit := by
    have H := (congrArg BStarLongToken.decode post).trans (decode_encode _)
    change readK (patchPair (longWork g raw) raw) C.source=
      finish (BStarClearanceForward.carried g raw C injectUnit) at H
    rw [carried] at H
    exact H.trans ((FreshInjection.inject_unit_packet (geometry g C.source.side) C.source.occurrence).2.2.2.1)
  exact (congrArg (atCursor (step x e)) pos).trans
    ((new_read B x e sep C.source).symm.trans (joined.trans read))

private theorem one_advance {slots : Nat→Pos n} {x : X} {e : Fin n} {len k j : Nat}
    (E : Event hp slots len x e (.busy 10 (.out k)) (.busy 10 (.out j))) :
    Advance len (.out k) (.out j) := by
  cases E with
  | transit _ _ _ _ S =>
    cases S with
    | cons _ _ A _ rest => cases rest; exact A

/-- The unconditioned unit is carried to the end of any outward
prefix whose selected release sites have their old physical inputs.
This uses the actual old mark order and no successful terminal byte. -/
theorem unit_busy_outward {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    {z d : Cursor} {w : List (Fin n)}
    (P : BusyOnly hp base (fun j=>S.getD j fall) len 10 x z w d) :
    ∀ k l,z=.out k → d=.out l →
      project (fun j=>S.getD j fall) x k=.forward injectUnit →
      (∀ pre e post,w=pre++e::post → ∀ j,
        Current hp base (fun t=>S.getD t fall) len (run x pre) (.busy 10 (.out j)) →
        ∀ C : CommandClaim, C∈orderedCommands (oldPair B (run x pre) e) →
          S.getD j fall=address e C.source →
          ReadyPort (oldPair B (run x pre) e)
            (((run x pre) e).long,((run x pre) (rightNeighbor e)).long) C) →
      project (fun j=>S.getD j fall) (run x w) l=.forward injectUnit := by
  induction P with
  | nil _ =>
    intro k l K L F _
    have eq := Cursor.out.inj (K.symm.trans L)
    subst l
    exact F
  | @cons x z d final e w I E tail ih =>
    intro k l K L F before
    subst z
    obtain ⟨j,J⟩ := BStarAcquireHistorySample.busy_no_back_to_out hp tail ⟨l,L⟩
    subst d
    let slots := fun t=>S.getD t fall
    have later := fun pre mark post W=>before (e::pre) mark post (congrArg (List.cons e) W)
    have new := busy_start hp tail
    have unique : ∀ i≤len, anyTag.F (project slots (step x e) i) ↔ i=j :=
      BStarOwnerControlHistory.pointed_unique_forward _ _ _ new.2.1 new.2.2
    by_cases go : linkAt hp x e slots len k
    · obtain ⟨bound,C,dest,mem,dst,source,target⟩ := go
      have old : readK ((x e).long,(x (rightNeighbor e)).long) C.source=.forward injectUnit :=
        (old_read x e C.source).trans ((congrArg (atCursor x) source).symm.trans F)
      have moved : project slots (step x e) (k+1)=.forward injectUnit :=
        (congrArg (atCursor (step x e)) target).trans
          (unit_link hp x e (sep e) C dest mem dst old (before [] e w rfl k I C mem source))
      have eq := (unique (k+1) (by omega)).mp ⟨_,moved⟩
      exact ih (k+1) l (congrArg Cursor.out eq.symm) L moved later
    · have noT : k=len → ¬onTerminal hp x e slots len := by
        intro atEnd T
        have jEq : j=len := by
          have jl := new.2.1.1
          have A := one_advance hp E
          cases A <;> omega
        have corner : project slots x len=.forward injectUnit := by
          rw [←atEnd]; exact F
        have reply := unit_turn hp e (sep e) T corner
        obtain ⟨p,oldPoint⟩ := new.2.1.2.1
        rw [jEq] at oldPoint
        exact Token.noConfusion (reply.symm.trans oldPoint)
      have frame := AdmissionTour.silent hp chart e (sep e) 10 k I.1 I.2.1 injectUnit F rfl
        (FreshInjection.inject_unit_packet _ _).1
        (by intro s; simp [injectUnit,observe,gate,admit,bitOp])
        go noT
      have eq := (unique k I.2.1.1).mp ⟨_,frame⟩
      exact ih k l (congrArg Cursor.out eq.symm) L frame later

/-- The real CLEAR and ENABLE supply vacancy and the open gate.
The remaining local input is the frozen data from the original LOAD. -/
theorem ready_from_preparation {base origin : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    {w : List (Fin n)} {k : Nat}
    (G : GeneratedOwner hp base (fun j=>S.getD j fall) len origin .idle w (.busy 10 (.out k)))
    (scope : LiveAt hp chart origin w) (init : pc origin (S.getD 0 fall).1=6)
    (e : Fin n) (C : CommandClaim) (ptr : S.getD k fall=address e C.source)
    (hasFrozen : ∀ rev, C.source.occurrence=sourceOccurrence rev →
      (geometry (oldPair B (run origin w) e) C.source.side).inside=true →
      ∃ d : BitVec 36,(readLane (Sheet.index (sourceLane rev))
        (run origin w (site e C.source.side)).long).frozen=.data d) :
    ReadyPort (oldPair B (run origin w) e)
      (((run origin w) e).long,((run origin w) (rightNeighbor e)).long) C := by
  intro rev source inside
  let x := run origin w
  let i := site e C.source.side
  have cur := BStarGeneratedTapeCuts.at_end hp G
  have L := chart.length
  have kL := cur.2.1.1
  have mem : S.getD k fall∈S := by
    rw [←List.getElem_eq_getD (h:=show k<S.length by omega)]
    exact List.getElem_mem _
  have loc : S.getD k fall=(i,sourceOccurrence rev) := ptr.trans (Prod.ext rfl source)
  have owner := (chart.entries _ mem).2
  rw [loc] at owner
  have displ : dataDispl (sourceLane rev)=cmdDispl (sourceOccurrence rev) := by
    cases rev <;> decide
  have laneOwner : dataOwner (oldH6 B base) i (sourceLane rev)=o.val := by
    unfold dataOwner
    rw [displ]
    exact owner
  have inNow : (longGeometry B (x i)).inside=true := by
    cases H : C.source.side <;> simpa [x,i,H,oldPair,geometry,site] using inside
  have same := congrArg (fun q : Bool×Bool×Bool=>q.2.1) (cur.1.1 i)
  have active : activeSheet (longGeometry B (base i)) (sourceLane rev)=true := by
    cases rev
    · rfl
    · exact same.trans inNow
  obtain ⟨vacant,openGate⟩ := FreshPreparation.active_sources_on_inject hp chart sep G scope init rev
  let localOld := view ((x e).long,(x (rightNeighbor e)).long) ⟨C.source.side,sourceLane rev⟩
  change localOld.gate=true ∧ localOld.mobile=.empty ∧ ∃ d : BitVec 36,localOld.frozen=.data d
  have viewEq : localOld=readLane (Sheet.index (sourceLane rev)) (x i).long := by
    cases H : C.source.side <;> simp [localOld,view,lane,BStarTrace.lane,i,site,H]
  rw [viewEq]
  exact ⟨openGate i (sourceLane rev) active laneOwner,
    vacant i ⟨k,Nat.le_refl _,kL,loc⟩ active,hasFrozen rev source inside⟩

/-- The actual outward tape from the genuine launch preserves the
unit at the terminal before any terminal turn or acknowledgement. -/
theorem terminal_unit_of_issue {base origin : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    {w : List (Fin n)}
    (G : GeneratedOwner hp base (fun j=>S.getD j fall) len origin .idle w (.busy 10 (.out len)))
    (ready : ∀ a e b,w=a++e::b → ∀ k,
      Current hp base (fun j=>S.getD j fall) len (run origin a) (.busy 10 (.out k)) →
      ∀ C : CommandClaim, C∈orderedCommands (oldPair B (run origin a) e) →
        S.getD k fall=address e C.source →
        ReadyPort (oldPair B (run origin a) e)
          (((run origin a) e).long,((run origin a) (rightNeighbor e)).long) C) :
    project (fun j=>S.getD j fall) (run origin w) len=.forward injectUnit := by
  obtain ⟨pre,tour,launch,W,_,launched,op,P⟩ := from_idle hp G
  let old := run origin pre
  let start := step old launch
  let root := (S.getD 0 fall).1
  have addr0 := (BStarResetChartService.root_header hp chart (busy_start hp P).1.1).2
  have initial : project (fun j=>S.getD j fall) start 0=.forward injectUnit := by
    obtain ⟨_,a,arg,snap⟩ := launched
    have C : (ctrlOp.read (old root).long).toNat=10 := op
    change BStarLongDoor.initial (ctrlOp.read (old root).long).toNat (old root).long=some a at arg
    rw [C] at arg
    have A : a=0 := (Option.some.inj (show some 0=some a from arg)).symm
    subst a
    have point := congrArg (fun q : (Token×BitVec 2)×BitVec 9=>q.1.1) snap
    change atSite (start root).long 0=forward (ctrlOp.read (old root).long).toNat 0 at point
    rw [C] at point
    change atSite (start root).long (S.getD 0 fall).2=.forward injectUnit
    rw [addr0]
    exact point
  have readyOnTour (a : List (Fin n)) (e : Fin n) (b : List (Fin n)) (E : tour=a++e::b)
      (k : Nat) (I : Current hp base (fun j=>S.getD j fall) len (run start a) (.busy 10 (.out k)))
      (C : CommandClaim) (M : C∈orderedCommands (oldPair B (run start a) e))
      (ptr : S.getD k fall=address e C.source) :
      ReadyPort (oldPair B (run start a) e)
        (((run start a) e).long,((run start a) (rightNeighbor e)).long) C := by
    have split : w=(pre++launch::a)++e::b := by
      rw [W,E,List.append_assoc,List.cons_append]
    have replay : run origin (pre++launch::a)=run start a := by
      rw [BStarResetSchedule.run_append]; rfl
    have H := ready (pre++launch::a) e b split k (replay.symm ▸ I) C (replay.symm ▸ M) ptr
    rwa [replay] at H
  have F := unit_busy_outward hp chart sep P 0 len rfl rfl initial readyOnTour
  rw [W,BStarResetSchedule.run_append]
  exact F

/-- Recover the completed LOAD, intervening ENABLE, and INJECT prefix
on the one actual tape from ISSUE6. The genuine op8 consume is the
only cut used to build the interstage frame. -/
theorem load_middle_from_issue {base origin : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    {w : List (Fin n)} {k : Nat}
    (G : GeneratedOwner hp base (fun j=>S.getD j fall) len origin .idle w (.busy 10 (.out k)))
    (scope : LiveAt hp chart origin w) (init : pc origin (S.getD 0 fall).1=6) :
    ∃ wLoad middle u, w=(wLoad++middle)++u ∧
      OwnMiddle hp base origin (fun j=>S.getD j fall) len wLoad middle ∧
      BusyOnly hp base (fun j=>S.getD j fall) len 10 (run origin (wLoad++middle)) (.out 0) u (.out k) := by
  obtain ⟨lead,launch,u,W,GI,VI,L,door,op,P⟩ := BStarCopySetupReplay.issue_cut hp chart G scope
  obtain ⟨wLoad,ack,post,D,G8,hit,after,_⟩ :=
    BStarCopyFenceCuts.ack_at hp chart sep GI VI 8 (by omega) (by omega)
  have early : GeneratedOwner hp base (fun j=>S.getD j fall) len
      (run origin wLoad) (.busy 8 (.back 0)) (ack::post) .idle :=
    .next hit.1 hit.2.1 after
  have eq : run origin lead=run (run origin wLoad) (ack::post) := by
    rw [D,BStarResetSchedule.run_append]
  have localScope : LiveAt hp chart (run origin wLoad) (ack::post) :=
    (BStarCopyFenceCuts.split_live hp chart (D ▸ VI)).2
  have mid := BStarCopyRightSetupMiddle.middle_from_actual_cuts hp chart sep wLoad (ack::post) launch
    G8 early localScope (eq ▸ op) door (eq ▸ L) (eq ▸ busy_start hp P)
  have replay : wLoad++((ack::post)++[launch])=lead++[launch] := by rw [D,List.append_assoc]
  refine ⟨wLoad,(ack::post)++[launch],u,?_,mid,?_⟩
  · rw [W,replay,List.append_assoc] <;> rfl
  · rw [replay,BStarResetSchedule.run_append]
    exact P

private theorem busy_generated {base x : X} {slots : Nat→Pos n} {len op : Nat}
    {z d : Cursor} {w : List (Fin n)} (P : BusyOnly hp base slots len op x z w d) :
    GeneratedOwner hp base slots len x (.busy op z) w (.busy op d) := by
  induction P with
  | nil I => exact .endpoint I
  | cons I E _ ih => exact .next I E ih

/-- Every pending active left source at its K5 cut holds data from its
own original K0 LOAD. The field is transported across the actual
LOAD tail and ENABLE, with no future opcode-10 success premise. -/
theorem left_frozen_of_issue {base origin : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    {w : List (Fin n)} {k : Nat}
    (G : GeneratedOwner hp base (fun j=>S.getD j fall) len origin .idle w (.busy 10 (.out k)))
    (scope : LiveAt hp chart origin w) (init : pc origin (S.getD 0 fall).1=6)
    (a : Fin n) (seam width i : Nat) (strip : BStarCopyLeftStrip.Strip B base a seam width)
    (root : a=(S.getD 0 fall).1) (inside : (longGeometry B (base (addr a i))).inside=true)
    (range : i<seam) (ptr : S.getD k fall=(addr a i,5)) :
    ∃ digit : BitVec 36,(BStarCopyLeftMark.sample (run origin w) a seam i).frozen=.data digit := by
  obtain ⟨wLoad,middle,u,W,M,P⟩ := load_middle_from_issue hp chart sep G scope init
  obtain ⟨pre,issue,suffix,bank,W8,door,_,L,op,every⟩ :=
    BStarCopyLeftReleaseCapture.common_bank_and_cuts hp chart sep a seam width strip root M.start8
  obtain ⟨before,rest,j,U,jL,J,part,tail,mark,frozen⟩ := every i range inside
  let lead := pre++issue::before
  let e := addr a i
  let x := step (run origin pre) issue
  obtain ⟨mode,Gpre,cur⟩ := BStarCopyGateAuthority.history_prefix hp pre (issue::suffix) (W8 ▸ M.start8)
  have oldIdle : mode=.idle := by
    cases mode with
    | idle => rfl
    | busy op z => exact ((by decide : (1:Nat)≠2) (L.1.2.symm.trans cur.1.2.2.1)).elim
  subst mode
  have launchEvent := Event.launch (hp:=hp) (addr:=fun j=>S.getD j fall) (len:=len) door L
  rw [op] at launchEvent
  have load := append_generated hp Gpre (.next cur launchEvent (busy_generated hp part))
  have replay : run origin lead=run x before := by
    dsimp only [lead,x]
    rw [BStarResetSchedule.run_append]
    rfl
  have tape : wLoad=(lead++[e])++rest := by
    rw [W8,U]
    simp [lead,e,List.append_assoc]
  have own := BStarCopyLeftReadyWord.all_owner hp chart a seam width strip root i (by omega)
  rw [BStarCopyLeftStrip.rail,if_pos range] at own
  have kL := (BStarGeneratedTapeCuts.at_end hp G).2.1.1
  have fiber (q z : List (Fin n)) (E : ((((lead++[e])++rest)++middle)++u)=q++z) :
      ∀ v,Layout B base v=Layout B (run origin q) v :=
    (scope q z (by rwa [W,tape])).1
  have frame := BStarCopyLeftReleaseCapture.frame_after_exact_load hp chart sep lead rest middle u
    e j k (Nat.le_of_lt jL) kL ptr J own load (replay.symm ▸ mark) (replay.symm ▸ tail)
    (tape ▸ M) ((congrArg (·++middle) tape) ▸ P) fiber
  rw [←tape,←W,replay] at frame
  have F := frame.trans frozen
  unfold BStarCopyLeftMark.sample
  rw [BStarCopyLeftStrip.rail,if_pos range]
  exact ⟨_,F⟩

/-- The wrapped right source uses the original selected K2 LOAD at
the same chart index as its later INJECT. Equal packed bytes at other
sites cannot supply the witness. -/
theorem right_frozen_of_issue {base origin : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    {w : List (Fin n)} {k : Nat}
    (G : GeneratedOwner hp base (fun j=>S.getD j fall) len origin .idle w (.busy 10 (.out k)))
    (scope : LiveAt hp chart origin w) (init : pc origin (S.getD 0 fall).1=6)
    (a : Fin n) (seam tail i : Nat) (strip : BStarCopyRightWrappedGeometry.WrappedStrip B base a seam tail)
    (owner : dataOwner (oldH6 B base) (addr a 0) (rail seam 0)=o.val)
    (lo : seam≤i) (hi : i≤tail) (ptr : S.getD k fall=(addr a i,2)) :
    ∃ digit : BitVec 36,(BStarCopyRightDeposit.lanes (run origin w) (addr a i) .rs).frozen=.data digit := by
  obtain ⟨wLoad,middle,u,W,M,P⟩ := load_middle_from_issue hp chart sep G scope init
  obtain ⟨lead,e,rest,j,C,p,W8,jL,J,markAt,src,nd,H,event,restLoad,advanced,inside⟩ :=
    BStarCopyRightWrappedLoadCoverage.original_rs_load_visit hp chart sep a seam tail strip owner M.start8 i lo hi
  have lenChart := chart.length
  have kL := (BStarGeneratedTapeCuts.at_end hp G).2.1.1
  have eq := (List.getD_inj (show j<S.length by omega) (show k<S.length by omega) chart.nodup).mp
    (J.trans ptr.symm)
  subst j e
  let e := addr a i
  have tape : wLoad=(lead++[e])++rest := W8.trans (by simp [e,List.append_assoc])
  have loc : address e C.source=S.getD k fall := by rw [src,ptr] <;> rfl
  have own := (BStarCopyRightWrappedReleaseClass.strip_same_owner strip i hi).trans owner
  rw [show rail seam i=.rs from if_neg (Nat.not_lt_of_ge lo)] at own
  have selected : C∈orderedCommands (oldPair B (run origin lead) e) := by
    rw [←actualOffers_claims _ (((run origin lead) e).long,((run origin lead) (rightNeighbor e)).long)]
    exact List.mem_map.mpr ⟨_,advanced,rfl⟩
  have fiber (q z : List (Fin n)) (E : ((((lead++[e])++rest)++middle)++u)=q++z) :
      ∀ v,Layout B base v=Layout B (run origin q) v :=
    (scope q z (by rwa [W,tape])).1
  obtain ⟨_,_,_,bank,_,_,_,F⟩ := BStarCopyRightLoadToInject.original_to_inject hp chart sep
    lead rest middle u e .left C p k kL loc src selected nd advanced inside own H event restLoad
    (tape ▸ M) ((congrArg (·++middle) tape) ▸ P) fiber
  rw [←tape,←W] at F
  exact ⟨_,F⟩

private theorem prefix_at_front {base origin : X} {S : List (Pos n)} {len : Nat}
    {fall : Pos n} {d : Mode} (pre tail : List (Fin n)) (k : Nat)
    (G : GeneratedOwner hp base (fun j=>S.getD j fall) len origin .idle (pre++tail) d)
    (cur : Current hp base (fun j=>S.getD j fall) len (run origin pre) (.busy 10 (.out k))) :
    GeneratedOwner hp base (fun j=>S.getD j fall) len origin .idle pre (.busy 10 (.out k)) := by
  obtain ⟨mode,P,old⟩ := BStarCopyGateAuthority.history_prefix hp pre tail G
  cases mode with
  | idle =>
    exact ((by decide : (1:Nat)≠2) (old.1.2.symm.trans cur.1.2.2.1)).elim
  | busy op z =>
    have eq : op=10 := old.1.2.2.2.symm.trans cur.1.2.2.2
    subst op
    cases z with
    | back j =>
      exact (BStarOwnerControlHistory.pointed_backward_no_forward _ _ _ old.2.1 k
        cur.2.1.1 cur.2.1.2.1).elim
    | out j =>
      have K := (BStarOwnerControlHistory.pointed_unique_forward _ _ _ old.2.1 old.2.2 k
        cur.2.1.1).mp cur.2.1.2.1
      subst j
      exact P

/-- Recover both ordered prefixes at the end of the same actual
outward INJECT. The old slots are initialized by the real CLEAR and
ENABLE. The original LOAD certifies each actual release, and its
label's bytes come from the frozen field at the INJECT launch. -/
theorem ordered_from_issue {base origin : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    {w : List (Fin n)}
    (G : GeneratedOwner hp base (fun j=>S.getD j fall) len origin .idle w (.busy 10 (.out len)))
    (scope : LiveAt hp chart origin w) (init : pc origin (S.getD 0 fall).1=6)
    (lroot : Fin n) (lSeam : Nat) (lStrip : BStarCopyLeftStrip.Strip B base lroot lSeam r)
    (lRoot : lroot=(S.getD 0 fall).1) (lSize : r≤lSeam)
    (lFlag : ∀ j<lSeam,(longGeometry B (base (addr lroot j))).inside=true ↔ j<r)
    (rroot rbase : Fin n) (rSeam rTail : Nat)
    (rStrip : BStarCopyRightWrappedGeometry.WrappedStrip B base rbase rSeam rTail)
    (rDest : BStarCopyRightRetained.Dest B base rroot r)
    (rJoin : addr rbase 0=addr rroot (r-1))
    (rOwner : dataOwner (oldH6 B base) (addr rbase 0) (rail rSeam 0)=o.val)
    (rSize : rTail+1=rSeam+r)
    (leftCover : ∀ i,dataOwner (oldH6 B base) i .ls=o.val →
      (longGeometry B (base i)).inside=true → ∃ j,j<lSeam ∧ i=addr lroot j)
    (rightCover : ∀ i,dataOwner (oldH6 B base) i .rs=o.val →
      (longGeometry B (base i)).inside=true → ∃ j,rSeam≤j ∧ j≤rTail ∧ i=addr rbase j) :
    ∃ lead launch tour, w=lead++launch::tour ∧
      project (fun j=>S.getD j fall) (run origin w) len=.forward injectUnit ∧
      let before := run origin (lead++[launch])
      let fin := run origin w
      let lDigits := fun i=>frozenDigit (BStarCopyLeftMark.sample before lroot lSeam i)
      let rDigits := fun i=>frozenDigit (BStarCopyRightDeposit.lanes before (addr rbase (rSeam+i)) .rs)
      (∃ t : Ledger Nat, ∃ q : Nat→Option Nat,
        t.release.pending=[] ∧ OrderedPrefix (pending id r) t (headFirst lSeam q) ∧
        BStarCopyLeftRetained.RetainedMatches lDigits fin (addr lroot lSeam) r t ∧
        BStarCopyLeftMark.UpstreamMatches lDigits fin lroot lSeam q) ∧
      (∃ t : Ledger Nat, ∃ q : Nat→Option Nat,
        t.release.pending=[] ∧ OrderedPrefix (planOf (fun i=>i-rSeam) rSeam rTail) t (stripWord rTail q) ∧
        BStarCopyRightRetained.RetainedMatches rDigits fin rroot r t ∧
        BStarCopyRightMark.MobileMatches rDigits fin rbase rSeam rTail q) := by
  have F : project (fun j=>S.getD j fall) (run origin w) len=.forward injectUnit := by
    apply terminal_unit_of_issue hp chart sep G
    intro pre e tail W k old C _ ptr
    have hist := prefix_at_front hp pre (e::tail) k (W ▸ G) old
    have scopeCut : LiveAt hp chart origin pre :=
      fun u v E=>scope u (v++e::tail) (by rw [W,E,List.append_assoc])
    apply ready_from_preparation hp chart sep hist scopeCut init e C ptr
    intro rev port inside
    let i := site e C.source.side
    let x := run origin pre
    have loc : S.getD k fall=(i,sourceOccurrence rev) := ptr.trans (Prod.ext rfl port)
    have length := chart.length
    have kL := old.2.1.1
    have mem : S.getD k fall∈S := by
      rw [←List.getElem_eq_getD (h:=show k<S.length by omega)]
      exact List.getElem_mem _
    have O := (chart.entries _ mem).2
    rw [loc] at O
    have d : dataDispl (sourceLane rev)=cmdDispl (sourceOccurrence rev) := by
      cases rev <;> decide
    have owns : dataOwner (oldH6 B base) i (sourceLane rev)=o.val := by
      unfold dataOwner
      rw [d]
      exact O
    have inNow : (longGeometry B (x i)).inside=true := by
      cases H : C.source.side <;> simpa [x,i,H,oldPair,geometry,site] using inside
    have same := congrArg (fun q : Bool×Bool×Bool=>q.2.1) (old.1.1 i)
    have inBase : (longGeometry B (base i)).inside=true := same.trans inNow
    cases rev with
    | false =>
      obtain ⟨j,range,A⟩ := leftCover i owns inBase
      have location : S.getD k fall=(addr lroot j,5) := by simpa [A,sourceOccurrence] using loc
      have active : (longGeometry B (base (addr lroot j))).inside=true := by rwa [A] at inBase
      have H := left_frozen_of_issue hp chart sep hist scopeCut init lroot lSeam r j
        lStrip lRoot active range location
      change ∃ d : BitVec 36,(readLane (Sheet.index .ls) (x i).long).frozen=.data d
      rw [A]
      simpa [BStarCopyLeftMark.sample,BStarCopyLeftStrip.rail,range] using H
    | true =>
      obtain ⟨j,lo,hi,A⟩ := rightCover i owns inBase
      have location : S.getD k fall=(addr rbase j,2) := by simpa [A,sourceOccurrence] using loc
      have H := right_frozen_of_issue hp chart sep hist scopeCut init rbase rSeam rTail j
        rStrip rOwner lo hi location
      change ∃ d : BitVec 36,(readLane (Sheet.index .rs) (x i).long).frozen=.data d
      rw [A]
      exact H
  obtain ⟨lead,tour,launch,W,door,L,oldPC,P⟩ := from_idle hp G
  let start := lead++[launch]
  let x := run origin start
  have total : w=start++tour := by
    rw [W]
    simp [start,List.append_assoc]
  have startEq : x=step (run origin lead) launch := by
    dsimp only [x,start]
    rw [BStarResetSchedule.run_append]
    rfl
  obtain ⟨mode,Gpre,I⟩ := BStarCopyGateAuthority.history_prefix hp lead (launch::tour) (W ▸ G)
  have idle : mode=.idle := by
    cases mode with
    | idle => rfl
    | busy op z =>
      exact ((by decide : (1:Nat)≠2) (L.1.2.symm.trans I.1.2.2.1)).elim
  subst mode
  have tourP : BusyOnly hp base (fun j=>S.getD j fall) len 10 x (.out 0) tour (.out len) :=
    startEq.symm ▸ P
  have launchEvent := Event.launch (hp:=hp) (addr:=fun j=>S.getD j fall) (len:=len) door L
  rw [oldPC] at launchEvent
  have Gstart : GeneratedOwner hp base (fun j=>S.getD j fall) len origin .idle start (.busy 10 (.out 0)) :=
    append_generated hp Gpre (.next I launchEvent (.endpoint (busy_start hp P)))
  have preValid : LiveAt hp chart origin lead :=
    fun a b E=>scope a (b++launch::tour) (by rw [W,E,List.append_assoc])
  obtain ⟨w9,ack,gap,W9,G9,E9,N9⟩ :=
    BStarCopyCleanupCuts.accepted_cut hp chart sep Gpre preValid 9 (by rw [init]; decide)
      (by change 9<pc (run origin lead) (S.getD 0 fall).1; change pc (run origin lead) (S.getD 0 fall).1=10 at oldPC; rw [oldPC]; decide)
  have enableCut : start=w9++ack::(gap++[launch]) := by
    simp only [start,W9,List.append_assoc,List.cons_append]
  have flyValid : LiveAt hp chart origin (start++tour) := fun a b E=>scope a b (total.trans E)
  have endWord : run origin w=run x tour := by rw [total,BStarResetSchedule.run_append]
  have atEnd : project (fun j=>S.getD j fall) (run x tour) len=.forward injectUnit := endWord ▸ F
  have layout (a b : List (Fin n)) (H : tour=a++b) :
      ∀ i,Layout B base i=Layout B (run x a) i := by
    have F := (scope (start++a) b (by rw [total,H,←List.append_assoc])).1
    rwa [BStarResetSchedule.run_append] at F
  have ownedL := BStarCopyLeftReadyWord.all_owner hp chart lroot lSeam r lStrip lRoot
  let lDigits := fun i=>frozenDigit (BStarCopyLeftMark.sample x lroot lSeam i)
  let rDigits := fun i=>frozenDigit (BStarCopyRightDeposit.lanes x (addr rbase (rSeam+i)) .rs)
  have frozenL (a : List (Fin n)) (e : Fin n) (b : List (Fin n)) (E : tour=a++e::b)
      (m : Mode) (R : BStarCopyLeftReleaseClass.ReleaseAt hp (run x a) e lroot lSeam
        (fun j=>S.getD j fall) len m) :
      (BStarCopyLeftMark.sample (run x a) lroot lSeam R.i).frozen=.data (lDigits R.i) := by
    obtain ⟨C,p,src,move⟩ := R.advance
    have hit : S.getD R.k fall=address e C.source := by
      rw [R.ptr,src,←R.markAt] <;> rfl
    have pre := prefix_to_release hp chart e (E ▸ tourP) R.k (Nat.le_of_lt R.strict) C p hit move
    have O : dataOwner (oldH6 B base) (addr lroot R.i) .ls=o.val := by
      simpa [BStarCopyLeftStrip.rail,R.range] using ownedL R.i (by have := R.range; omega)
    have before := BStarCopyLeftPreinject.frozen_pc10_prefix hp chart sep (addr lroot R.i)
      R.k (Nat.le_of_lt R.strict) R.ptr O start rfl Gstart pre
      (fun u mark v A=>layout u ((mark::v)++e::b) (by rw [E,A,List.append_assoc]))
    have replay : run origin (start++a)=run x a := BStarResetSchedule.run_append ..
    have M : w=(start++a)++e::b := by rw [total,E,←List.append_assoc]
    have hist := append_generated hp Gstart (busy_generated hp pre)
    have scopeCut : LiveAt hp chart origin (start++a) :=
      fun u v Eq=>scope u (v++e::b) (by rw [M,Eq,List.append_assoc])
    have same := congrArg (fun q : Bool×Bool×Bool=>q.2.1) (layout a (e::b) E (addr lroot R.i))
    have inside : (longGeometry B (base (addr lroot R.i))).inside=true :=
      same.trans (BStarCopyLeftReleaseOrder.release_inside hp R)
    have H := left_frozen_of_issue hp chart sep hist scopeCut init lroot lSeam r R.i
      lStrip lRoot inside R.range R.ptr
    rw [replay] at H
    apply read_frozen _ H
    simpa [BStarCopyLeftMark.sample,BStarCopyLeftStrip.rail,R.range] using before
  have frozenR (a : List (Fin n)) (e : Fin n) (b : List (Fin n)) (E : tour=a++e::b)
      (m : Mode) (R : BStarCopyRightReleaseClass.ReleaseAt hp (run x a) e rbase rSeam rTail
        (fun j=>S.getD j fall) len m) :
      (BStarCopyRightDeposit.lanes (run x a) (addr rbase R.i) .rs).frozen=.data (rDigits (R.i-rSeam)) := by
    obtain ⟨C,p,src,move⟩ := R.advance
    have hit : S.getD R.k fall=address e C.source := by
      rw [R.ptr,src,←R.markAt] <;> rfl
    have pre := prefix_to_release hp chart e (E ▸ tourP) R.k (Nat.le_of_lt R.strict) C p hit move
    have O := (BStarCopyRightWrappedReleaseClass.strip_same_owner rStrip R.i R.range.2).trans rOwner
    rw [show rail rSeam R.i=.rs from if_neg (Nat.not_lt_of_ge R.range.1)] at O
    have before := BStarCopyRightPreinject.frozen_pc10_prefix hp chart sep (addr rbase R.i)
      R.k (Nat.le_of_lt R.strict) R.ptr O start rfl Gstart pre
      (fun u mark v A=>layout u ((mark::v)++e::b) (by rw [E,A,List.append_assoc]))
    have replay : run origin (start++a)=run x a := BStarResetSchedule.run_append ..
    have M : w=(start++a)++e::b := by rw [total,E,←List.append_assoc]
    have hist := append_generated hp Gstart (busy_generated hp pre)
    have scopeCut : LiveAt hp chart origin (start++a) :=
      fun u v Eq=>scope u (v++e::b) (by rw [M,Eq,List.append_assoc])
    have H := right_frozen_of_issue hp chart sep hist scopeCut init rbase rSeam rTail
      R.i rStrip rOwner R.range.1 R.range.2 R.ptr
    rw [replay] at H
    have j : rSeam+(R.i-rSeam)=R.i := by have := R.range.1; omega
    unfold rDigits
    rw [j]
    exact read_frozen before H
  have left := BStarCopyLeftRecovered.recovered_left_outward hp chart sep lDigits lroot lSeam r
    lStrip lRoot lSize lFlag start tour lead launch rfl Gpre (Nat.le_of_eq init)
    oldPC Gstart tourP w9 (gap++[launch]) ack enableCut G9 E9 N9 (total ▸ G)
    flyValid injectUnit atEnd rfl rfl frozenL
  have right := BStarCopyRightWrappedPostAck.post_ack_outward hp chart sep rbase rSeam rTail
    rStrip rOwner rSize rDigits start tour Gstart tourP frozenR rroot rDest rJoin lead launch
    rfl Gpre (Nat.le_of_eq init) oldPC w9 (gap++[launch]) ack enableCut G9 E9 N9
    (total ▸ G) flyValid injectUnit atEnd rfl rfl
  refine ⟨lead,launch,tour,W,F,?_⟩
  change _ ∧ _
  rw [endWord]
  exact ⟨left,right⟩

#print axioms prefix_to_release
#print axioms ordered_from_issue
#print axioms unit_offer
#print axioms unit_link
#print axioms unit_busy_outward
#print axioms ready_from_preparation
#print axioms terminal_unit_of_issue
#print axioms left_frozen_of_issue
#print axioms right_frozen_of_issue
end L4.Height.FreshOrderedPrefix
