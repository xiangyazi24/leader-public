import Leader.L4.BStarCopyEntryGates
import Leader.L4.BStarCopyOwnedFrozen
import Leader.L4.BStarAcquireHistoryReturn

namespace L4.BStarCopyDownstream
set_option maxRecDepth 4096
open AllSizeProtocol BStarTrace BStarLongClaims BStarLongWork BStarLongToken
open BStarLongCommand BStarLongCommandData BStarLongPrep BStarLongPackets
open BStarH6WordChart BStarLongFixedRouting BStarResetChartTouch BStarAcquireVisitOrder
open BStarAcquireLiteralChain BStarResetChartIndex BStarAcquireAnchors BStarClearanceDataChart
open BStarCopyInjection BStarCopyOperand BStarCopyEntryGates BStarLongFiberOwner
open BStarResetMarkAdapter BStarResetRailRing BStarGeneratedOwner BStarSeparatingRail

private def geo (h i l : Bool) : LongGeometry :=
  ⟨⟨false,false,false,false,false,h⟩,i,l,0,false⟩

/-- Incoming LS/RS data travels strictly opposite the inject command;
neither a seam nor the other copy direction can be an alias for a
source-sheet receiver. This checks the literal selected demands even
in the presence of arbitrary reservations. -/
theorem opposite_selected (g : Pair LongGeometry) (rsv : List (At Sheet))
    (d : DataClaim) (a : At Sheet) (rev : Bool)
    (mem : d∈orderedData g rsv) (D : d.destination=some a)
    (sh : a.occurrence=sourceLane rev) :
    d.source.occurrence=sourceLane rev ∧
    link ⟨a.side,sourceOccurrence rev⟩ ⟨d.source.side,sourceOccurrence rev⟩∈orderedCommands g := by
  let test (g : Pair LongGeometry) (rev : Bool) (d : DataClaim) : Bool :=
    match d.destination with
    | none => true
    | some a => if a.occurrence=sourceLane rev then
        d.source.occurrence==sourceLane rev &&
          (orderedCommands g).contains
            (link ⟨a.side,sourceOccurrence rev⟩ ⟨d.source.side,sourceOccurrence rev⟩)
      else true
  have cert (I L H J rev : Bool) :
      (dataClaims (geo false I L,geo H J false)).all
        (test (geo false I L,geo H J false) rev)=true := by
    cases I <;> cases L <;> cases H <;> cases J <;> cases rev <;> decide +kernel
  obtain ⟨g₁,g₂⟩ := g
  let g' := (geo false g₁.inside g₁.last,geo g₂.axes.h6 g₂.inside false)
  have raw := BStarLongFenceTopology.selected_data_raw (g₁,g₂) rsv d mem
  change d∈dataClaims g' at raw
  have H := List.all_eq_true.mp (cert g₁.inside g₁.last g₂.axes.h6 g₂.inside rev) d raw
  unfold test at H
  rw [D] at H
  dsimp only at H
  rw [if_pos sh] at H
  have Q := Bool.and_eq_true_iff.mp H
  exact ⟨beq_iff_eq.mp Q.1,List.contains_iff_mem.mp Q.2⟩

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "P" => production k₁ k₂ t₂ J₁ J₂ r c p c₁
local notation "X" => Fin n → LargeSite P
local notation "step" => AllSizeS1Geometry.step (n:=n) B
local notation "play" => BStarResetSchedule.run step

def Unvisited (S : List (Pos n)) (fall : Pos n) (len cut : Nat) (rev : Bool) (i : Fin n) : Prop :=
  ∃ j, cut≤j ∧ j≤len ∧ S.getD j fall=(i,sourceOccurrence rev)

theorem incoming_later {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall)
    (same : ∀ i, BStarLongFixedRouting.Layout B base i=BStarLongFixedRouting.Layout B x i)
    (e : Fin n) (rev : Bool) (cut : Nat) (rsv : List (At Sheet))
    (d : DataClaim) (a : At Sheet)
    (mem : d∈orderedData (oldPair B x e) rsv) (D : d.destination=some a)
    (sh : a.occurrence=sourceLane rev)
    (untouched : Unvisited S fall len cut rev (site e a.side)) :
    d.source.occurrence=sourceLane rev ∧
    Unvisited S fall len (cut+1) rev (site e d.source.side) := by
  obtain ⟨j,cutJ,jLen,J⟩ := untouched
  obtain ⟨sameSheet,back⟩ := opposite_selected (oldPair B x e) rsv d a rev mem D sh
  have back' := command_eq B x base (fun i => (same i).symm) e ▸ back
  let u : Pos n := (site e a.side,sourceOccurrence rev)
  let v : Pos n := (site e d.source.side,sourceOccurrence rev)
  have E : Edge B base u v := ⟨e,_,_,back',rfl,rfl,rfl⟩
  have L := chart.length
  have jm : j<S.length := by omega
  have uS : u∈S := by
    change (site e a.side,sourceOccurrence rev)∈S
    rw [←J,←List.getElem_eq_getD (h:=jm)]; exact List.getElem_mem _
  obtain ⟨q,qLen,U,V⟩ := chart.edge u v uS E
  have qEq : q=j := by
    apply (List.getD_inj (by omega) jm chart.nodup).mp
    rw [←List.getElem_eq_getD (h:=show q<S.length by omega),U,J]
  subst q
  exact ⟨sameSheet,j+1,by omega,by omega,(List.getElem_eq_getD _).symm.trans V⟩

open BStarCopyOwnedFrozen BStarLongEvents BStarLongTransport BStarAcquireForwardTrace
open BStarSeparatorControl BStarResetQuiet BStarOwnerLaunchOrigin BStarResetSchedule

private theorem inject_site (g : LongGeometry) (j : Fin 11) (rev : Bool)
    (H : sourceLane rev∈prepSites g j .inject) : j=sourceOccurrence rev := by
  have all (i rev : Bool) :
      ∀ j : Fin 11, sourceLane rev∈prepSites (geo false i false) j .inject →
        j=sourceOccurrence rev := by
    cases i <;> cases rev <;> decide +kernel
  exact all g.inside rev j H

private theorem inject_at_pending {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (e : Fin n)
    (sep : e≠rightNeighbor e) (rev : Bool) (k k' : Nat) (op : Nat)
    (old : Current hp base (fun j => S.getD j fall) len x (.busy op (.out k)))
    (post : Current hp base (fun j => S.getD j fall) len (step x e) (.busy op (.out k')))
    (mono : k≤k') (a : At Sheet)
    (shr : a.occurrence=sourceLane rev)
    (pending : Unvisited S fall len k' rev (site e a.side)) :
    ∀ pr∈(arbitration (round (oldPair B x e) ((x e).long,(x (rightNeighbor e)).long)).prep).1,
      pr.claim.lane=a → pr.claim.op≠.inject := by
  intro pr win lane H
  let g := oldPair B x e
  let raw : Pair (BitVec LW) := ((x e).long,(x (rightNeighbor e)).long)
  obtain ⟨C,f,q,_,move,_,_,origin,side,sites⟩ := winner_origin g raw pr win
  have sideEq : C.source.side=a.side := side.symm.trans (congrArg At.side lane)
  have idx : C.source.occurrence=sourceOccurrence rev := by
    rw [H,lane,shr] at sites
    exact inject_site _ _ rev sites
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
  have shp := (BStarAcquireReturn.link_shape g C z hmem dst)
  have work := (BStarClearanceForward.move_lands g raw C q z dst move (Ne.symm shp.1)).1
  have joined := BStarAcquireReturn.joined_reads k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
    (x e,x (rightNeighbor e)) C.source (fun h z => (shp.2.2 h z).elim)
  have rawT : readK (patchPair (longWork g raw) raw) C.source=.trail :=
    (congrArg BStarLongToken.decode work).trans (decode_encode _)
  have atT := (new_read B x e sep C.source).symm.trans (joined.trans rawT)
  obtain ⟨live,F⟩ := post.2.1.2.1
  change atCursor (step x e) (S.getD k' fall)=.forward live at F
  rw [←afterJ,atC,atT] at F
  cases F

def CutVacant (x : X) (S : List (Pos n)) (fall : Pos n) (len cut : Nat) (rev : Bool) : Prop :=
  ∀ i, Unvisited S fall len cut rev i →
    (readLane (Sheet.index (sourceLane rev)) (x i).long).mobile=.empty

/-- On the actual ring step, all source lanes ahead of the new outward
cursor remain vacant. Foreign winning prep cannot alias this owner;
a successful or faulted injection at the old cursor leaves Trail,
so that occurrence cannot remain in the unvisited suffix. -/
theorem cut_vacant_step {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (e : Fin n) (sep : e≠rightNeighbor e)
    (op k k' : Nat) (rev : Bool)
    (old : Current hp base (fun j => S.getD j fall) len x (.busy op (.out k)))
    (post : Current hp base (fun j => S.getD j fall) len (step x e) (.busy op (.out k')))
    (mono : k≤k') (V : CutVacant x S fall len k rev) :
    CutVacant (step x e) S fall len k' rev := by
  intro i pending
  have enlarge (i : Fin n) {a b : Nat} (e : a≤b) (H : Unvisited S fall len b rev i) :
      Unvisited S fall len a rev i := by
    obtain ⟨j,J,L,A⟩ := H
    exact ⟨j,Nat.le_trans e J,L,A⟩
  have empty := V i (enlarge i mono pending)
  have touched (s : Side) (loc : site e s=i) :
      (readLane (Sheet.index (sourceLane rev)) (step x e i).long).mobile=.empty := by
    subst i
    let a : At Sheet := ⟨s,sourceLane rev⟩
    let g := oldPair B x e
    let raw : Pair (BitVec LW) := ((x e).long,(x (rightNeighbor e)).long)
    have noIn (d : DataClaim) (mem : d∈orderedData g (reserved (round g raw).prep))
        (D : d.destination=some a) : (view raw d.source).mobile=.empty := by
      obtain ⟨same,L⟩ := incoming_later hp chart old.1.1 e rev k'
        (reserved (round g raw).prep) d a mem D rfl pending
      have empty := V (site e d.source.side) (enlarge _ (by omega) L)
      cases ds : d.source.side <;> simpa [view,site,lane,BStarTrace.lane,raw,ds,same] using empty
    have H := pair_vacancy_local hp (x e,x (rightNeighbor e)) a
      (by cases s <;> exact empty)
      (inject_at_pending hp chart e sep rev k k' op old post mono a rfl pending) noIn
    cases s <;> simpa [a,Pair.map,view,site,lane,BStarTrace.lane,AllSizeS1Geometry.step,Ne.symm sep] using H
  by_cases l : i=e
  · exact touched .left l.symm
  · by_cases r : i=rightNeighbor e
    · exact touched .right r.symm
    · rwa [show step x e i=x i from by simp [AllSizeS1Geometry.step,l,r]]

theorem cut_from_owner_empty {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (rev : Bool)
    (empty : MobilesEmpty hp base x o.val) :
    CutVacant x S fall len 0 rev := by
  intro i pending
  obtain ⟨j,_,h,J⟩ := pending
  have L := chart.length
  have mem : S.getD j fall∈S := by
    rw [←List.getElem_eq_getD (h:=show j<S.length by omega)]
    exact List.getElem_mem _
  have own := (chart.entries _ mem).2
  rw [J] at own
  have same : dataDispl (sourceLane rev)=cmdDispl (sourceOccurrence rev) := by cases rev <;> decide
  apply empty
  unfold dataOwner
  rw [same]
  exact own

/-- Full actual tape preservation on every busy PC10 outward prefix.
Internal and simultaneously active foreign marks are included. No
monotonicity or non-injection premise is supplied by the caller. -/
theorem busy_cut_vacant {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    {z d : Cursor} {w : List (Fin n)}
    (hist : BusyOnly hp base (fun j => S.getD j fall) len 10 x z w d)
    (rev : Bool) :
    ∀ j k, z=.out j → d=.out k → CutVacant x S fall len j rev →
      CutVacant (play x w) S fall len k rev := by
  induction hist with
  | nil _ =>
    intro j k J K E
    exact (Cursor.out.inj (J.symm.trans K)) ▸ E
  | @cons raw z d fin e w I event rest ih =>
    intro j k J K V
    subst z
    obtain ⟨j',J'⟩ := BStarAcquireHistorySample.busy_no_back_to_out hp rest ⟨k,K⟩
    subst d
    have monotone : j≤j' := by
      cases event with
      | transit _ _ _ _ H =>
        cases H with
        | cons _ _ adv _ endW =>
          cases endW
          cases adv <;> omega
    have V' := cut_vacant_step hp chart e (sep e) 10 j j' rev I (busy_start hp rest) monotone V
    exact ih j' k rfl K V'

/-- Even after prior injections further downstream, the actual selected
INJECT at the present cursor finds its old mobile empty. Given the
previously established gate and frozen packet, the physical row
releases that exact original packet. -/
theorem busy_cut_inject {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    {w : List (Fin n)} {j : Nat}
    (hist : BusyOnly hp base (fun j => S.getD j fall) len 10 x (.out 0) w (.out j))
    (empty : MobilesEmpty hp base x o.val)
    (e : Fin n) (s : Side) (rev : Bool) (value : BitVec 36) :
    let y := play x w
    let i := site e s
    let ln := Sheet.index (sourceLane rev)
    S.getD j fall=(i,sourceOccurrence rev) →
    BStarCopyInjection.injection s rev∈
      (arbitration (round (oldPair B y e) ((y e).long,(y (rightNeighbor e)).long)).prep).1 →
    (readLane ln (y i).long).gate=true →
    (readLane ln (y i).long).frozen=.data value →
    let out := readLane ln (step y e i).long
    out.mobile=.data value ∧ out.frozen=.empty := by
  dsimp only
  intro atJ win gate frozen
  have bound := (BStarAcquireHistoryReturn.busy_end hp hist).2.1.1
  have v := busy_cut_vacant hp chart sep hist rev 0 j rfl rfl (cut_from_owner_empty hp chart rev empty)
  have vacant := v (site e s) ⟨j,by omega,bound,atJ⟩
  have H := ring_inject hp (play x w) e (sep e) s rev value win gate frozen vacant
  exact ⟨congrArg Lane.mobile H,congrArg Lane.frozen H⟩

open BStarLongDoor BStarClearanceSource

/-- Actual clean launch mark cannot introduce a mobile into the own
vacant rail from another owner, even with arbitrary foreign activity. -/
theorem issue_keeps_empty {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (e : Fin n) (sep : e≠rightNeighbor e)
    (layout : ∀ r, BStarLongFixedRouting.Layout B base r=BStarLongFixedRouting.Layout B x r)
    (idle : Current hp base (fun k => S.getD k fall) len x .idle)
    (empty : MobilesEmpty hp base x o.val) :
    MobilesEmpty hp base (step x e) o.val := by
  apply ring_mobiles_empty hp base x e o.val sep
    (funext (fun i => (congrArg Prod.fst (layout i)).symm)) empty
  intro a win own
  have A := safe_idle hp chart layout e (site e a.claim.lane.side) a.claim.lane.occurrence own idle.2
  have Eq : a.claim.lane=⟨a.claim.lane.side,a.claim.lane.occurrence⟩ := by cases a.claim.lane; rfl
  rcases A a.claim.lane.side rfl a win Eq with S|S|S <;> rw [S] <;> decide

private theorem addressed_launch {base x : X} {addr : Nat → Pos n} {len op : Nat}
    {start : Mode} {w : List (Fin n)} {z : Cursor}
    (hist : GeneratedOwner hp base addr len x start w (.busy op z)) :
    (∃ (pre post : List (Fin n)) (e : Fin n),
      w=pre++e::post ∧
      Current hp base addr len (play x pre) .idle ∧
      Launch ((play x pre) (addr 0).1).long ((step (play x pre) e) (addr 0).1).long ∧
      (ctrlOp.read ((play x pre) (addr 0).1).long).toNat=op ∧
      BusyOnly hp base addr len op (step (play x pre) e) (.out 0) post z) ∨
    ∃ init, start=.busy op init ∧ BusyOnly hp base addr len op x init w z := by
  generalize K : Mode.busy op z = dest at hist
  induction hist with
  | endpoint I =>
    cases K
    exact .inr ⟨z,rfl,.nil I⟩
  | next I T rest ih =>
    rcases ih K with ⟨pre,post,d,eq,idle,L,pc,busy⟩|⟨init,eq,busy⟩
    · exact .inl ⟨_::pre,post,d,congrArg (List.cons _) eq,idle,L,pc,busy⟩
    · subst eq
      cases T with
      | launch _ L => exact .inl ⟨[],_,_,rfl,I,L,rfl,busy⟩
      | transit _ _ _ live S => exact .inr ⟨_,rfl,.cons I (.transit op _ _ live S) busy⟩
      | arrived_hold _ ne => exact .inr ⟨.back 0,rfl,.cons I (.arrived_hold op ne) busy⟩

/-- GeneratedOwner source-to-all-releases vacancy. Only the settled
owner-empty boundary immediately before the actual ISSUE10 is needed;
the source launch mark and all subsequent held/stay/foreign marks are
handled by the literal proof. -/
theorem generated_cut_vacant {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    {w : List (Fin n)} {j : Nat}
    (hist : GeneratedOwner hp base (fun k => S.getD k fall) len x .idle w (.busy 10 (.out j)))
    (rev : Bool)
    (layout : ∀ a b, w=a++b →
      ∀ i,BStarLongFixedRouting.Layout B base i=BStarLongFixedRouting.Layout B (play x a) i)
    (emptyAtIssue : ∀ a e b, w=a++e::b →
      Launch ((play x a) (S.getD 0 fall).1).long ((step (play x a) e) (S.getD 0 fall).1).long →
      (ctrlOp.read ((play x a) (S.getD 0 fall).1).long).toNat=10 →
      MobilesEmpty hp base (play x a) o.val)
    : CutVacant (play x w) S fall len j rev := by
  rcases addressed_launch hp hist with ⟨pre,post,e,eq,idle,L,pc,busy⟩|⟨_,bad,_⟩
  · have E := issue_keeps_empty hp chart e (sep e) (layout pre (e::post) eq) idle
      (emptyAtIssue pre e post eq L pc)
    have V := busy_cut_vacant hp chart sep busy rev 0 j rfl rfl (cut_from_owner_empty hp chart rev E)
    rw [eq,BStarResetSchedule.run_append]
    exact V
  · cases bad

end L4.BStarCopyDownstream
