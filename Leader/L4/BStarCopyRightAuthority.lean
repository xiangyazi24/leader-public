import Leader.L4.BStarCopyRightK2

namespace L4.BStarCopyRightAuthority
open AllSizeProtocol BStarTrace BStarLongWork BStarH6WordChart BStarLongClaims
open BStarCopyRightStrip BStarCopyRightDeposit BStarCopyDownstream
open BStarLongPackets BStarLongPrep BStarLongCommandData
open BStarClearanceDataChart BStarAcquireVisitOrder BStarAcquireAnchors
open BStarAcquireLiteralChain BStarResetChartIndex BStarResetChartTouch
open BStarCopyOwnedFrozen BStarAcquireHistoryReturn BStarSeparatorControl
open BStarResetMarkAdapter BStarResetQuiet

private def geo (h i l : Bool) : LongGeometry :=
  ⟨⟨false,false,false,false,false,h⟩,i,l,0,false⟩

theorem raw_is_selected_empty (g : Pair LongGeometry) (d : DataClaim)
    (m : d∈dataClaims g) : d∈orderedData g [] := by
  have A (I L H J : Bool) :
      (dataClaims (geo false I L,geo H J false)).all (fun c =>
        (orderedData (geo false I L,geo H J false) []).contains c)=true := by
    cases I <;> cases L <;> cases H <;> cases J <;> decide +kernel
  exact List.contains_iff_mem.mp (List.all_eq_true.mp
    (A g.1.inside g.1.last g.2.axes.h6 g.2.inside) d m)

theorem strip_same_owner {a : LargeParams} {n : Nat} {b : LargeRows a}
    {x : Fin n→LargeSite a} {base : Fin n} {seam tail : Nat}
    (C : Strip b x base seam tail) :
    ∀ i≤tail, dataOwner (oldH6 b x) (addr base i) (rail seam i)=
      dataOwner (oldH6 b x) (addr base 0) (rail seam 0) := by
  intro i
  induction i with
  | zero => simp
  | succ i IH =>
    intro it
    let edge := addr base i
    let dst := L (rail seam i)
    let cl := hop (R (rail seam (i+1))) dst
    have M : cl∈dataClaims (oldPair b x edge) := (raw_incoming C i (by omega) cl rfl).mpr rfl
    have H := reserved_hop_owner b x edge [] cl dst (raw_is_selected_empty _ _ M) rfl
    change dataOwner (oldH6 b x) (rightNeighbor (addr base i)) (rail seam (i+1)) =
      dataOwner (oldH6 b x) (addr base i) (rail seam i) at H
    rw [←addr_next] at H
    exact H.trans (IH (by omega))

#print axioms strip_same_owner

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)

open BStarResetSchedule BStarSeparatingRail BStarGeneratedOwner

/-- Any winning prep on the right upstream strip must depart from the
one actual command cursor of this owner. Since prep is same-site and
strip addresses are distinct, no physical sibling slot may reserve. -/
theorem no_competing_from_pointed {base x : X}
    {hh : ∃ i,oldH6 B base i=true} {o : Owners (oldH6 B base)}
    {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall)
    (same : ∀ i, BStarLongFixedRouting.Layout B base i=BStarLongFixedRouting.Layout B x i)
    (e a : Fin n) (seam tail i cursor : Nat) (it : i≤tail)
    (C : Strip B base a seam tail)
    (ownerHead : dataOwner (oldH6 B base) (addr a 0) (rail seam 0)=o.val)
    (atIssue : (S.getD cursor fall).1=addr a i)
    (good : Good anyTag len (project (fun j => S.getD j fall) x) (.out cursor))
    (clean : OutClean len (project (fun j => S.getD j fall) x) (.out cursor)) :
    NoPrepExcept hp x e a seam tail i := by
  intro j side jp jt ne atSlot H
  obtain ⟨offer,win,lane⟩ := List.mem_map.mp H
  obtain ⟨q,f,v,_,chosen,_,_,origin,owner⟩ := winner_owner hp x e offer win
  have eq : oldH6 B x=oldH6 B base := funext (fun a => (congrArg Prod.fst (same a)).symm)
  have O := (strip_same_owner C j jt).trans ownerHead
  rw [eq,lane] at owner
  change commandOwner (oldH6 B base) (site e q.source.side) q.source.occurrence =
    dataOwner (oldH6 B base) (site e side) (rail seam j) at owner
  rw [atSlot,O] at owner
  obtain ⟨k,E,idx⟩ := actual_owner_departure hp chart same e q v (.out cursor) chosen owner good clean
  have K := Cursor.out.inj E
  subst k
  have first := congrArg Prod.fst idx
  change (S.getD cursor fall).1=site e q.source.side at first
  have siteEq : offer.claim.lane.side=q.source.side := by
    obtain ⟨Q,_,_,_,_,_,_,originQ,sideQ,_⟩ := winner_origin (oldPair B x e)
      ((x e).long,(x (rightNeighbor e)).long) offer win
    have originSide : offer.claim.lane.side=offer.claim.origin.side :=
      sideQ.trans (congrArg At.side originQ).symm
    exact originSide.trans (congrArg At.side origin)
  have sideEq : side=q.source.side := (congrArg At.side lane).symm.trans siteEq
  rw [←sideEq,atIssue,atSlot] at first
  exact ne ((addr_inj a (Nat.lt_of_le_of_lt it C.tail_lt)
    (Nat.lt_of_le_of_lt jt C.tail_lt) first).symm)

#print axioms no_competing_from_pointed
end L4.BStarCopyRightAuthority
