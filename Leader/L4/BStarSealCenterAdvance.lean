import Leader.L4.BStarSealHealthyFlight

namespace L4.BStarSealCenterAdvance
open AllSizeProtocol BStarTrace BStarLongClaims BStarLongWork BStarLongToken
open BStarLongCommand BStarLongEvents BStarLongTransport BStarLongLiteral BStarLongLayout
open BStarH6WordChart BStarAcquireVisitOrder BStarAcquireForwardTrace BStarAcquireLiteralChain
open BStarLongFixedRouting BStarResetChartTouch BStarResetMarkAdapter BStarResetRailRing
open BStarSeparatingRail BStarGeneratedOwner BStarSealHealthyHop BStarSealHealthyFlight
open BStarLongPublication BStarSealParity

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step (n:=n) B

/-- The selected SEAL's accepted physical departure is a genuine
owner cursor advance, with the exact healthy outgoing polarity at the
actual next chart slot. No later outward or return proof is assumed. -/
theorem accepted_step {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall)
    (Q : X→Prop) (fiber : ∀ x,Q x→∀ i,Layout B base i=Layout B x i)
    (closed : ∀ x,Q x→∀ e,Q (step x e)) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (qx : Q x) (i : Fin n) (j : Nat) (J : j<len)
    (loc : S.getD j fall=(i,1)) (head : oldH6 B base i=true)
    (cur : Current hp base (fun t=>S.getD t fall) len x (.busy sealOp (.out j)))
    (pay : Payload) (W : Well pay) (d : Descriptor)
    (sel : let g := oldPair B x i
      (centerLink g,.advance pay)∈actualOffers g ((x i).long,(x (rightNeighbor i)).long))
    (decoded : BStarLongPublication.decode (BitVec.ofNat 7 (pay.argument.toNat/2))=some d)
    (auth : BStarLongOutgoing.actual (x i).long d=true)
    (stageEq : readOptional (stage.read (x i).long)=some d) :
    ∃ v, Event hp (fun t=>S.getD t fall) len x i (.busy sealOp (.out j)) (.busy sealOp (.out (j+1))) ∧
      Current hp base (fun t=>S.getD t fall) len (step x i) (.busy sealOp (.out (j+1))) ∧
      project (fun t=>S.getD t fall) (step x i) (j+1)=.forward v ∧
      Well v ∧ parity v=d.need.toNat := by
  let g := oldPair B x i
  let K := centerLink g
  let a : AtK := R (if g.2.axes.h6 then 2 else 1)
  let addr := fun t=>S.getD t fall
  have D : K.destination=some a := rfl
  have idx : addr j=address i K.source := loc
  have forward : Edge B x (address i K.source) (address i a) :=
    ⟨i,K,a,center_mem g,D,rfl,rfl⟩
  have sz := C.length
  have mem : addr j∈S := by
    change S.getD j fall∈S
    rw [←List.getElem_eq_getD (h:=show j<S.length by omega)]
    exact List.getElem_mem _
  obtain ⟨k,hk,src,dst⟩ := C.edge _ _ (idx ▸ mem)
    ((edge_fixed B base x (fiber x qx) _ _).mpr forward)
  have sk : S.getD k fall=address i K.source := (List.getElem_eq_getD _).symm.trans src
  have ident : k=j := (List.getD_inj (by omega) (by omega) C.nodup).mp (sk.trans idx.symm)
  subst k
  have next : addr (j+1)=address i a := (List.getElem_eq_getD _).symm.trans dst
  have h : (geometry g K.source.side).axes.h6=true :=
    (congrArg Prod.fst (fiber x qx i)).symm.trans head
  obtain ⟨v,H,vW,vpar⟩ := joined_accepted_seal hp (x i,x (rightNeighbor i)) K a pay d W
    rfl h D sel decoded auth stageEq
  have post : project addr (step x i) (j+1)=.forward v :=
    (congrArg (atCursor (step x i)) next).trans ((new_read B x i (sep i) a).symm.trans H)
  obtain ⟨_,event,cur'⟩ := current_step hp C Q fiber closed sep qx i (.busy sealOp (.out j)) cur
  cases event with
  | transit _ _ d live seen =>
    cases seen with
    | cons M go adv gd tail =>
      cases tail
      cases adv with
      | stay =>
        have empty := cur'.2.2 (j+1) (by omega) J
        exact Token.noConfusion (empty.symm.trans post)
      | forward =>
        exact ⟨v,.transit _ _ _ live (.cons M go (.forward j) gd (.nil _ _)),cur',post,vW,vpar⟩
      | turn => omega

#print axioms accepted_step
end L4.BStarSealCenterAdvance
