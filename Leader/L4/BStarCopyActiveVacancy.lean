import Leader.L4.BStarCopyDownstream
import Leader.L4.BStarCopyPaddingFrame
import Leader.L4.BStarCopyOwnedFrozen
import Leader.L4.BStarAcquireHistoryReturn

namespace L4.BStarCopyActiveVacancy
open BStarCopyDownstream BStarOwnerLaunchOrigin
open AllSizeProtocol BStarTrace BStarLongClaims BStarLongWork BStarLongToken
open BStarLongCommand BStarLongCommandData BStarLongPrep BStarLongPackets
open BStarH6WordChart BStarLongFixedRouting BStarResetChartTouch BStarAcquireVisitOrder
open BStarAcquireLiteralChain BStarResetChartIndex BStarAcquireAnchors BStarClearanceDataChart
open BStarCopyInjection BStarCopyOperand BStarCopyEntryGates BStarLongFiberOwner
open BStarResetMarkAdapter BStarResetRailRing BStarGeneratedOwner BStarSeparatingRail

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "P" => production k₁ k₂ t₂ J₁ J₂ r c p c₁
local notation "X" => Fin n → LargeSite P
local notation "step" => AllSizeS1Geometry.step (n:=n) B
local notation "play" => BStarResetSchedule.run step

def ActiveOwnerEmpty (base x : X) (o : Int) : Prop :=
  ∀ i sh, activeSheet (longGeometry B (x i)) sh=true →
    dataOwner (oldH6 B base) i sh=o →
    (readLane (Sheet.index sh) (x i).long).mobile=.empty

def ActiveCutVacant (x : X) (S : List (Pos n)) (fall : Pos n) (len cut : Nat) (rev : Bool) : Prop :=
  ∀ i, Unvisited S fall len cut rev i →
    activeSheet (longGeometry B (x i)) (sourceLane rev)=true →
    (readLane (Sheet.index (sourceLane rev)) (x i).long).mobile=.empty

private def geo (h i l : Bool) : LongGeometry :=
  ⟨⟨false,false,false,false,false,h⟩,i,l,0,false⟩

open BStarCopyOwnedFrozen BStarLongEvents BStarLongTransport BStarAcquireForwardTrace
open BStarSeparatorControl BStarResetQuiet BStarOwnerLaunchOrigin BStarResetSchedule

private theorem inject_site (g : LongGeometry) (j : Fin 11) (rev : Bool)
    (H : sourceLane rev∈prepSites g j .inject) : j=sourceOccurrence rev := by
  have all (i rev : Bool) :
      ∀ j : Fin 11, sourceLane rev∈prepSites (geo false i false) j .inject →
        j=sourceOccurrence rev := by
    cases i <;> cases rev <;> decide +kernel
  exact all g.inside rev j H

private theorem active_inject_at_pending {base x : X} {hh : ∃ i,oldH6 B base i=true}
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

theorem active_step {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (e : Fin n) (sep : e≠rightNeighbor e)
    (op k k' : Nat) (rev : Bool)
    (old : Current hp base (fun j => S.getD j fall) len x (.busy op (.out k)))
    (post : Current hp base (fun j => S.getD j fall) len (step x e) (.busy op (.out k')))
    (mono : k≤k') (V : ActiveCutVacant hp x S fall len k rev) :
    ActiveCutVacant hp (step x e) S fall len k' rev := by
  intro i pending active
  have enlarge (i : Fin n) {a b : Nat} (e : a≤b) (H : Unvisited S fall len b rev i) :
      Unvisited S fall len a rev i := by
    obtain ⟨j,J,L,A⟩ := H
    exact ⟨j,Nat.le_trans e J,L,A⟩
  have empty := V i (enlarge i mono pending) (by
    have E := congrArg (fun t : Bool×Bool×Bool => t.2.1) ((old.1.1 i).symm.trans (post.1.1 i))
    change (longGeometry B (x i)).inside=(longGeometry B (step x e i)).inside at E
    cases rev
    · rfl
    · exact E.trans active)
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
      have acS : activeSheet (longGeometry B (x (site e d.source.side))) (sourceLane rev)=true := by
        cases Hr : rev
        · rfl
        · have hpad : d.source.occurrence=.ld ∨ d.source.occurrence=.rs :=
            .inr (by simpa [sourceLane,Hr] using same)
          have I := BStarCopyPaddingFrame.data_active g _ d d.source mem
            (by simp [Claim.slots,D]) hpad
          cases side : d.source.side <;> simpa [g,oldPair,geometry,site,side,sourceLane,activeSheet] using I
      have empty := V (site e d.source.side) (enlarge _ (by omega) L) acS
      cases ds : d.source.side <;> simpa [view,site,lane,BStarTrace.lane,raw,ds,same] using empty
    have H := pair_vacancy_local hp (x e,x (rightNeighbor e)) a
      (by cases s <;> exact empty)
      (active_inject_at_pending hp chart e sep rev k k' op old post mono a rfl pending) noIn
    cases s <;> simpa [a,Pair.map,view,site,lane,BStarTrace.lane,AllSizeS1Geometry.step,Ne.symm sep] using H
  by_cases l : i=e
  · exact touched .left l.symm
  · by_cases r : i=rightNeighbor e
    · exact touched .right r.symm
    · rwa [show step x e i=x i from by simp [AllSizeS1Geometry.step,l,r]]

theorem active_from_owner_empty {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (rev : Bool)
    (empty : ActiveOwnerEmpty hp base x o.val) :
    ActiveCutVacant hp x S fall len 0 rev := by
  intro i pending active
  obtain ⟨j,_,h,J⟩ := pending
  have L := chart.length
  have mem : S.getD j fall∈S := by
    rw [←List.getElem_eq_getD (h:=show j<S.length by omega)]
    exact List.getElem_mem _
  have own := (chart.entries _ mem).2
  rw [J] at own
  have same : dataDispl (sourceLane rev)=cmdDispl (sourceOccurrence rev) := by cases rev <;> decide
  apply empty i (sourceLane rev) active
  unfold dataOwner
  rw [same]
  exact own

/-- Full actual tape preservation on every busy PC10 outward prefix.
Internal and simultaneously active foreign marks are included. No
monotonicity or non-injection premise is supplied by the caller. -/
theorem busy_active_vacant {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    {z d : Cursor} {w : List (Fin n)}
    (hist : BusyOnly hp base (fun j => S.getD j fall) len 10 x z w d)
    (rev : Bool) :
    ∀ j k, z=.out j → d=.out k → ActiveCutVacant hp x S fall len j rev →
      ActiveCutVacant hp (play x w) S fall len k rev := by
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
    have V' := active_step hp chart e (sep e) 10 j j' rev I (busy_start hp rest) monotone V
    exact ih j' k rfl K V'

end L4.BStarCopyActiveVacancy
