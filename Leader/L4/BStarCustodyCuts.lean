import Leader.L4.BStarStageAfterCut
import Leader.L4.BStarPublicationBirth
import Leader.L4.BStarCutOperandReadout

namespace L4.BStarCustodyCuts
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

/-- Both cuts are witnessed on one shared physical tape. No proof
below is allowed to choose a separate favorable recovery for a grant,
a Stage writer, or a publication. -/
structure CutFacts (base x : X) (u v : List (Fin n)) : Prop where
  body : ∀ tail e i center, oldH6 B base center=true →
    BodyAuthority hp (run x (u++tail)) e i center
  grant : ∀ tail i j, bit (run x ((u++v)++tail)) i j≠0 →
    BirthAfter hp x ((u++v)++tail) i j (u.length+1)
  commit : ∀ tail e i, ¬ BStarGrantWriterHistory.NoPublication hp (run x ((u++v)++tail)) e i →
    ∃ pre door post root, ((u++v)++tail)=pre++door::post ∧ u.length<pre.length ∧
      let z := run x pre
      door=RearTrace.predecessor root ∧
        Launch (z root).long (step z door root).long ∧ (ctrlOp.read (z root).long).toNat=commitOp
  recovery : ∀ (hh : ∃ i,oldH6 B base i=true) (i : Fin n) (j : Fin 3),
    ∃ (o : Owners (oldH6 B base)) (a b : Nat), commandOwner (oldH6 B base) i (slot j)=o.val ∧
      u.length≤a ∧ a<b ∧
      BStarRecoveryPass.Credit step (Recovered hp base hh) o x (u++v) a b

/-- Simultaneous physical custody cuts on a settled fixed lower
fibre. In the absence of a native-value transfer proof we do not
equate the actual publication with the numerical specification. -/
theorem compatible_cuts {base x : X} (hh : ∃ i,oldH6 B base i=true)
    (charts : ∀ o : Owners (oldH6 B base), ∃ S len fall, Chart hp base hh o S len fall)
    (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (head : ∀ i, let g := longGeometry B (base i); (!g.axes.h6 || g.inside)=true)
    (cont : ∀ i, let g := oldPair B base i; continuation g.1 g.2=true)
    (Q : X → Prop) (closed : ∀ y e, Q y → Q (step y e))
    (fiber : ∀ y, Q y → ∀ i, Layout B base i=Layout B y i)
    (heads : ∀ y, Q y → ∀ i, let g := longGeometry B (y i); (!g.axes.h6 || g.inside)=true)
    (conts : ∀ y, Q y → ∀ i, let g := oldPair B y i; continuation g.1 g.2=true)
    (cb : correct (oldH6 B base) hh 5 base)
    (owners : List (Owners (oldH6 B base)))
    (cover : ∀ i : Fin n, ∀ j : Fin 3, ∃ o∈owners, commandOwner (oldH6 B base) i (slot j)=o.val)
    (I : Q x) (cx : correct (oldH6 B base) hh 5 x) :
    ∃ u v, Q (run x u) ∧ Q (run x (u++v)) ∧ CutFacts hp base x u v := by
  obtain ⟨u,v,U,V,A,F⟩ := two_recoveries hp hh charts sep head cont Q closed fiber heads conts cb owners I cx
  refine ⟨u,v,U.1,V.1,?_,?_,?_,?_⟩
  · intro tail e i center hdr
    obtain ⟨o,M,own⟩ := cover center 1
    obtain ⟨a,b,_,B0,C⟩ := A o M
    have atA := BStarRecoveryPass.credit_prefix step C B0
    exact BStarStageAfterCut.body_authority_after_credit hp sep Q I fiber closed
      (BStarRecoveryPass.credit_append step atA tail) e i center hdr own
  · intro tail i j live
    obtain ⟨o,M,own⟩ := cover i j
    obtain ⟨a,b,N,L,C⟩ := F o M
    obtain ⟨lead,e,t,T,H,W⟩ := credit_grant hp sep (BStarRecoveryPass.credit_append step C tail)
      i j Q closed I (fun _ _ Iz Rh => recovered_zero hp sep Q Iz fiber closed Rh i j own) live
    exact ⟨lead,e,t,T,by omega,W⟩
  · intro tail e i pub
    obtain ⟨o,M,own⟩ := cover i 1
    obtain ⟨a,b,lower,order,credit⟩ := F o M
    obtain ⟨p,door,q,root,W,after,L⟩ :=
      BStarPublicationBirth.commit_after_credit hp sep Q I fiber closed
        (BStarRecoveryPass.credit_append step credit tail) e i own pub
    exact ⟨p,door,q,root,W,by omega,L⟩
  · intro witness i j
    obtain ⟨o,M,own⟩ := cover i j
    obtain ⟨a,b,N,L,C⟩ := F o M
    exact ⟨o,a,b,own,N,L,C⟩

end L4.BStarCustodyCuts
