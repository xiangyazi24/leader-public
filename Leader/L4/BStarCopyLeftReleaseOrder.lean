import Leader.L4.BStarCopyLeftReleaseClass
import Leader.L4.BStarCopyLeftOneCapture

namespace L4.BStarCopyLeftReleaseOrder
open AllSizeProtocol BStarTrace BStarLongWork BStarH6WordChart BStarLongClaims
open BStarLongPackets BStarLongPrep BStarLongCommandData BStarCopyOwnedFrozen
open BStarLongCommand
open BStarCopyLeftStrip BStarCopyLeftInjectionMark BStarCopyLeftReleaseClass
open BStarCopyLeftDeposit BStarCopyLeftK5Past BStarCopyDownstream
open BStarAcquireVisitOrder BStarAcquireLiteralChain BStarResetChartTouch BStarAcquireAnchors
open BStarGeneratedOwner BStarSeparatingRail BStarResetMarkAdapter BStarOwnerLaunchOrigin
open BStarCopyRightStrip (addr)

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "ring" => AllSizeS1Geometry.step (n:=n) B

/-- K5 is chart-owned at every source LS address, including the OUT
part (which is transparent to the source INJECT prep). -/
theorem k5_ordinal {base : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall) (a : Fin n) (seam width i : Nat)
    (strip : Strip B base a seam width) (root : a=(S.getD 0 fall).1) (hi : i<seam) :
    ∃ k<len,S.getD k fall=(addr a i,5) := by
  have O := (endpoint_spec (oldH6 B base) hh o 0).2.1
  rw [←C.root,←root] at O
  have own : commandOwner (oldH6 B base) (addr a i) 5=o.val := by
    unfold commandOwner at O ⊢
    rw [ls_same_word hp strip hh i hi]
    exact O
  obtain ⟨k,kl,eq⟩ := List.getElem_of_mem (C.cover (addr a i,5) rfl own)
  have idx : S.getD k fall=(addr a i,5) := (List.getElem_eq_getD (h:=kl) fall).symm.trans eq
  have b := C.length
  have ne : k≠len := by
    intro E
    subst k
    have K := congrArg Prod.snd (C.terminal.symm.trans idx)
    change (10 : Fin 11)=5 at K
    contradiction
  exact ⟨k,by omega,idx⟩

/-- At a real PC10 release, the pre-mark geometric source must be
INSIDE even if a dirty elsewhere offer shares the same raw mark. -/
theorem release_inside {x : X} {e a : Fin n} {seam len : Nat}
    {slot : Nat→Pos n} {m : Mode} (E : ReleaseAt hp x e a seam slot len m) :
    (longGeometry B (x (addr a E.i))).inside=true := by
  obtain ⟨c,_,_,_,_,_,_,src,side,M⟩ := winner_origin (oldPair B x e)
    ((x e).long,(x (rightNeighbor e)).long) _ E.win
  have r : c.source.side=.right := side.symm
  have H : (geometry (oldPair B x e) c.source.side).inside=true := by
    change .ls∈prepSites (geometry (oldPair B x e) c.source.side) c.source.occurrence .inject at M
    cases I : (geometry (oldPair B x e) c.source.side).inside
    · simp [prepSites,I] at M
    · rfl
  rw [r] at H
  change (longGeometry B (x (rightNeighbor e))).inside=true at H
  rwa [E.markAt] at H

/-- The selected K5 INJECT cannot be an outward stutter. On the same
actual busy tape its pre-mark source ordinal is irrevocably passed. -/
theorem release_before_later {base x : X} {e a : Fin n} {seam len : Nat}
    {slot : Nat→Pos n} {m : Mode} (R0 : ReleaseAt hp x e a seam slot len m)
    (sep : e≠rightNeighbor e) {z : Cursor} {w : List (Fin n)} {j : Nat}
    (evt : Event hp slot len x e (.busy 10 (.out R0.k)) (.busy 10 z))
    (rest : BusyOnly hp base slot len 10 (ring x e) z w (.out j)) : R0.k<j := by
  obtain ⟨c,f,src,chosen⟩ := R0.advance
  have ptr : address e c.source=slot R0.k := by
    rw [src,R0.ptr]
    exact Prod.ext R0.markAt rfl
  exact k5_no_depart_before_cut hp e sep c f (by rw [src]; rfl) ptr chosen evt rest

/-- The busy K5 visits occur in decreasing physical LS index:
neighboring digits are consecutive chart entries, including entry
into the original source H6. -/
theorem k5_chart_successor {base : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall) (a : Fin n) (seam width i k : Nat)
    (strip : Strip B base a seam width) (hi : i+1<seam)
    (kl : k≤len) (atK : S.getD k fall=(addr a (i+1),5)) :
    k<len ∧ S.getD (k+1) fall=(addr a i,5) := by
  have right := BStarCopyRightStrip.addr_next a i
  have body : (oldPair B base (addr a i)).2.axes.h6=false := by
    change oldH6 B base (rightNeighbor (addr a i))=false
    rw [←right]
    exact strip.ls_body _ (by omega) hi
  have edge : Edge B base (addr a (i+1),5) (addr a i,5) :=
    ⟨addr a i,link (R 5) (L 5),L 5,k5_body _ body,rfl,Prod.ext right rfl,rfl⟩
  have lenS := C.length
  have mem : (addr a (i+1),5)∈S := by
    rw [←atK,←List.getElem_eq_getD (h:=show k<S.length by omega)]
    exact List.getElem_mem _
  obtain ⟨j,jl,E,F⟩ := C.edge _ _ mem edge
  have Q : k=j := (List.getD_inj (by omega) (by omega) C.nodup).mp
    (atK.trans (E.symm.trans (List.getElem_eq_getD _)))
  subst j
  exact ⟨by omega,(List.getElem_eq_getD _).symm.trans F⟩

open BStarLongFiberOwner BStarLongToken BStarLongEvents
open BStarClearanceDataChart BStarLongLiteral
open BStarAcquireForwardTrace BStarSeparatorControl

theorem pointed_inject_exclusive {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall)
    (same : ∀ i, BStarLongFixedRouting.Layout B base i=BStarLongFixedRouting.Layout B x i)
    (e : Fin n) (sep : e≠rightNeighbor e) (C : CommandClaim) (f0 : Payload)
    (s : Side) (j : Nat)
    (laneOwner : dataOwner (oldH6 B base) (site e s) .ls=o.val)
    (G : Good anyTag len (project (fun j => S.getD j fall) x) (.out j))
    (out : OutClean len (project (fun j => S.getD j fall) x) (.out j))
    (ptr : address e C.source=S.getD j fall)
    (source : C.source=⟨s,5⟩)
    (op10 : f0.opcode.toNat=10)
    (select : (C,.advance f0)∈
        gated (oldPair B x e) ((x e).long,(x (rightNeighbor e)).long)) :
    let raw : Pair (BitVec LW) := ((x e).long,(x (rightNeighbor e)).long)
    ∀ a∈(round (oldPair B x e) raw).prep, a.claim.lane=⟨s,.ls⟩ →
      a=BStarCopyInjection.injection s false := by
  dsimp only
  intro a ma lane
  let g := oldPair B x e
  let raw : Pair (BitVec LW) := ((x e).long,(x (rightNeighbor e)).long)
  obtain ⟨D,f,q,gate,move,op,fault,fmem,orig,side,lanes⟩ := candidate_origin g raw a ma
  have E : (⟨D.source.side,a.claim.lane.occurrence⟩ : At Sheet)=a.claim.lane := by
    generalize Q : a.claim.lane=v at side ⊢
    obtain ⟨a,b⟩ := v
    exact congrArg (fun k => At.mk k b) side.symm
  have oEq : physicalOwner (oldH6 B x) e cmdDispl D.source =
      physicalOwner (oldH6 B x) e dataDispl a.claim.lane := by
    rw [physical_pair_owner,physical_pair_owner,←E]
    exact prep_owner g _ _ _ _ _ lanes
  have L : oldH6 B x=oldH6 B base := funext fun i => (congrArg Prod.fst (same i)).symm
  rw [L,lane] at oEq
  have ownD : commandOwner (oldH6 B base) (site e D.source.side) D.source.occurrence=o.val :=
    oEq.trans laneOwner
  obtain ⟨k,J,atD⟩ := actual_owner_departure hp chart same e D q (.out j) move ownD G out
  have kj := Cursor.out.inj J
  subst k
  have eqSource : C.source=D.source := address_inj e sep (ptr.trans atD)
  have cmem := ((gated_mem g raw C _).mp select).1
  have dmem := ((gated_mem g raw D _).mp gate).1
  have club := BStarAcquireIncidence.same_claim g C D C.source cmem dmem
    (by simp [Claim.slots]) (by simp [Claim.slots,eqSource])
  subst D
  have F := Offer.advance.inj (((gated_mem g raw C _).mp gate).2.trans
    ((gated_mem g raw C _).mp select).2.symm)
  subst f
  have O : a.claim.op=.inject := by
    rw [op10] at op
    exact (Option.some.inj op).symm
  have Q : a.claim=⟨.inject,⟨s,5⟩,⟨s,.ls⟩⟩ := by
    have J : a.claim=⟨a.claim.op,a.claim.origin,a.claim.lane⟩ := by cases a.claim; rfl
    exact J.trans (by rw [O,orig,source,lane])
  have V : a.payload=.empty := by
    simp only [fieldOffers,fault,bne_self_eq_false,op10,prepOf] at fmem
    obtain ⟨_,_,W⟩ := List.mem_map.mp fmem
    exact (congrArg BStarLongPrep.Offer.payload W).symm
  have Z : a=⟨a.claim,a.payload⟩ := by cases a; rfl
  rw [Z,Q,V]
  rfl

theorem pointed_inject_wins {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall)
    (same : ∀ i, BStarLongFixedRouting.Layout B base i=BStarLongFixedRouting.Layout B x i)
    (e : Fin n) (sep : e≠rightNeighbor e) (C : CommandClaim) (f0 : Payload)
    (s : Side) (j : Nat)
    (laneOwner : dataOwner (oldH6 B base) (site e s) .ls=o.val)
    (G : Good anyTag len (project (fun j => S.getD j fall) x) (.out j))
    (out : OutClean len (project (fun j => S.getD j fall) x) (.out j))
    (ptr : address e C.source=S.getD j fall)
    (source : C.source=⟨s,5⟩)
    (op10 : f0.opcode.toNat=10)
    (select : (C,.advance f0)∈
        gated (oldPair B x e) ((x e).long,(x (rightNeighbor e)).long))  
    (healthy : f0.fault=0) (inside : (geometry (oldPair B x e) s).inside=true) :
    BStarCopyInjection.injection s false∈(arbitration (round (oldPair B x e)
      ((x e).long,(x (rightNeighbor e)).long)).prep).1 := by
  let g := oldPair B x e
  let raw : Pair (BitVec LW) := ((x e).long,(x (rightNeighbor e)).long)
  let a := BStarCopyInjection.injection s false
  have candidate : a∈(round g raw).prep := by
    apply List.mem_flatMap.mpr
    refine ⟨(C,.advance f0),select,?_⟩
    change a∈fieldOffers g raw C.source f0
    rw [source]
    simp [a,BStarCopyInjection.injection,BStarCopyInjection.sourceOccurrence,
      BStarCopyInjection.sourceLane,fieldOffers,healthy,op10,prepOf,prepClaims,prepSites]
    exact inside
  apply BStarCopyInjection.exclusive_winner a _ candidate
  intro z M H
  exact pointed_inject_exclusive hp chart same e sep C f0 s j laneOwner G out ptr source op10 select z M H

end L4.BStarCopyLeftReleaseOrder
