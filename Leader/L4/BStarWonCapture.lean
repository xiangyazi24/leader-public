import Leader.L4.BStarGrantBirth
import Leader.L4.BStarReleaseOrigin
import Leader.L4.BStarAcquireHop

namespace L4.BStarWonCapture
open AllSizeProtocol BStarTrace BStarLongWork BStarLongClaims BStarLongToken
open BStarLongGrant BStarLongCommandData BStarLongCommand BStarReleaseOrigin
open BStarH6WordChart BStarGrantBirth BStarLongEvents

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)

/-- A won acquisition has both a real old forward origin and the
exact selected payload carrying the sampled old selector/header.
This still does not identify the origin as genuinely issued. -/
theorem won_capture (x : X) (e i : Fin n) (j : Fin 3) (winAt : WonAt hp x e i j) :
    let g := oldPair B x e
    let raw : Pair (BitVec LW) := ((x e).long,(x (rightNeighbor e)).long)
    ∃ C p q,
      C∈orderedCommands g ∧ site e C.source.side=i ∧ C.source.occurrence.val=j.val ∧
      oldTokens raw C.source=.forward q ∧ HealthyOp acquire q ∧
      (C,.advance p)∈(round g raw).offered ∧
      (C,.advance (capture (x i).long j p true))∈actualOffers g raw := by
  obtain ⟨s,H,header,W,E,p,P,sideEq,indexEq,fault,opc⟩ := winAt
  let g := oldPair B x e
  let raw : Pair (BitVec LW) := ((x e).long,(x (rightNeighbor e)).long)
  let O := (round g raw).offered
  have ask : requested O s j acquire=true := by
    apply List.any_eq_true.mpr
    exact ⟨(E,.advance p),P,by simp [sideEq,indexEq,fault,opc]⟩
  obtain ⟨C,p₁,q,mem,S,J,A,ok,old,oldOk⟩ := pre_grant_acquire_origin g raw s j ask
  have Sd : site e C.source.side=i := (congrArg (site e) S).trans H
  have h : C.source.occurrence.val<3 := J ▸ j.isLt
  have hc : (⟨C.source.occurrence.val,h⟩ : Fin 3)=j := Fin.ext J
  have Old : BStarLongGrant.atOld raw C.source.side=(x i).long := by
    rw [←Sd]
    cases U : C.source.side <;> rfl
  have update : BStarLongGrant.update g raw O (C,.advance p₁)=
      (C,.advance (capture (x i).long j p₁ true)) := by
    rw [BStarAcquireHop.grant_update_exact g raw O C p₁ ok.1 ok.2]
    unfold BStarAcquireHop.argUpdate
    rw [dif_pos h]
    have header' : (geometry g C.source.side).axes.h6=true := S.symm ▸ header
    simp only [header',hc]
    unfold BStarAcquireHop.won
    rw [S,W]
    rw [←S]
    simpa only [if_true] using (congrArg (fun a : BitVec LW => (C,Offer.advance (capture a j p₁ true))) Old)
  refine ⟨C,p₁,q,mem,Sd,J,old,oldOk,A,?_⟩
  unfold actualOffers BStarLongGrant.run
  exact List.mem_map.mpr ⟨_,A,update⟩

#print axioms won_capture
end L4.BStarWonCapture
