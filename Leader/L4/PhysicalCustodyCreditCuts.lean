import Leader.L4.BStarCustodyCuts

namespace L4.PhysicalCustodyCreditCuts
open BStarCustodyCuts
open AllSizeProtocol BStarTrace BStarLongClaims BStarLongWork BStarLongTransport
open BStarH6WordChart BStarAcquireVisitOrder BStarAcquireAnchors BStarAcquireRailCoverage
open BStarAcquireLiteralChain BStarLongFiberOwner BStarLongFixedRouting BStarResetChartTouch
open BStarResetMarkAdapter BStarGeneratedOwner BStarLongCommand BStarLongDoor
open BStarClearanceSource BStarLongEvents BStarGrantBirth BStarFirstCut BStarResetNoAcquire
open BStarBodyStageProvenance BStarClearanceOffset BStarOwnerRecoveryPass

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step B
local notation "run" => BStarResetSchedule.run step

/-- Extract the full shared custody contract from two families of credits on
one word. This does not synthesize a favorable word or impose a scheduler. -/
theorem cuts_of_credits {base x : X} (hh : ∃ i,oldH6 B base i=true)
    (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (Q : X → Prop) (I : Q x) (closed : ∀ y e,Q y → Q (step y e))
    (fiber : ∀ y, Q y → ∀ i, Layout B base i=Layout B y i)
    (owners : List (Owners (oldH6 B base)))
    (cover : ∀ i : Fin n, ∀ j : Fin 3, ∃ o∈owners, commandOwner (oldH6 B base) i (slot j)=o.val)
    (u v : List (Fin n))
    (first : ∀ o∈owners, ∃ a b,a<b ∧ b≤u.length ∧
      BStarRecoveryPass.Credit step (Recovered hp base hh) o x (u++v) a b)
    (second : ∀ o∈owners, ∃ a b,u.length≤a ∧ a<b ∧
      BStarRecoveryPass.Credit step (Recovered hp base hh) o x (u++v) a b) :
    CutFacts hp base x u v := by
  refine ⟨?_,?_,?_,?_⟩
  · intro tail e i center hdr
    obtain ⟨o,M,own⟩ := cover center 1
    obtain ⟨a,b,_,B0,C⟩ := first o M
    have atA := BStarRecoveryPass.credit_prefix step C B0
    exact BStarStageAfterCut.body_authority_after_credit hp sep Q I fiber closed
      (BStarRecoveryPass.credit_append step atA tail) e i center hdr own
  · intro tail i j live
    obtain ⟨o,M,own⟩ := cover i j
    obtain ⟨a,b,N,L,C⟩ := second o M
    obtain ⟨lead,e,t,T,H,W⟩ := credit_grant hp sep (BStarRecoveryPass.credit_append step C tail)
      i j Q closed I (fun _ _ Iz Rh => recovered_zero hp sep Q Iz fiber closed Rh i j own) live
    exact ⟨lead,e,t,T,by omega,W⟩
  · intro tail e i pub
    obtain ⟨o,M,own⟩ := cover i 1
    obtain ⟨a,b,lower,order,credit⟩ := second o M
    obtain ⟨p,door,q,root,W,after,L⟩ :=
      BStarPublicationBirth.commit_after_credit hp sep Q I fiber closed
        (BStarRecoveryPass.credit_append step credit tail) e i own pub
    exact ⟨p,door,q,root,W,by omega,L⟩
  · intro witness i j
    obtain ⟨o,M,own⟩ := cover i j
    obtain ⟨a,b,N,L,C⟩ := second o M
    exact ⟨o,a,b,own,N,L,C⟩

end L4.PhysicalCustodyCreditCuts
