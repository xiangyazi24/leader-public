import Leader.L4.Height.StageSealPreserve
import Leader.L4.BStarFirstDoorService
import Leader.L4.BStarCommitGeneratedTail

namespace L4.Height.StageScopedLaunch
open AllSizeProtocol BStarTrace BStarLongClaims BStarLongWork BStarLongToken
open BStarLongCommand BStarLongDoor BStarLongLayout BStarLongPublication BStarGeneratedOwner
open BStarAcquireLiteralChain BStarAcquireVisitOrder BStarH6WordChart BStarLongFixedRouting
open BStarResetChartTouch BStarResetChartService BStarResetMarkAdapter
variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step (n:=n) B

/-- The real incoming mark of a legal clean ISSUE408 produces the
authentic out-zero payload and preserves the original source descriptor. -/
theorem actual_launch_at_door {base x : X} {hh : ∃ j,oldH6 B base j=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall)
    (Q : X→Prop) (fiber : ∀ x,Q x→∀ i,Layout B base i=Layout B x i)
    (closed : ∀ x,Q x→∀ e,Q (step x e)) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (qx : Q x) (I : Current hp base (fun j=>S.getD j fall) len x .idle)
    (d : Descriptor) (e : Fin n) (own : e=RearTrace.predecessor (S.getD 0 fall).1)
    (pc : (ctrlOp.read (x (S.getD 0 fall).1).long).toNat=stageOp)
    (D : BStarLongPublication.decode (sourceDescriptor.read (x (S.getD 0 fall).1).long)=some d) :
    let adr := fun j=>S.getD j fall
    let source := (x (adr 0).1).long
    Event hp adr len x e .idle (.busy stageOp (.out 0)) ∧
    Current hp base adr len (step x e) (.busy stageOp (.out 0)) ∧
    project adr (step x e) 0=.forward (BStarStageIssue.payload source) ∧
    sourceDescriptor.read (step x e (adr 0).1).long=sourceDescriptor.read source := by
  dsimp only
  let adr := fun j=>S.getD j fall
  let raw : BitVec LW := (x (adr 0).1).long
  have legal : ∃ a,initial stageOp raw=some a := by
    rw [BStarStageIssue.stage_initial,show BStarLongPublication.decode (sourceDescriptor.read raw)=some d from D]
    exact ⟨_,rfl⟩
  obtain ⟨E,J,F⟩ := BStarFirstDoorService.legal_issue_at_door hp C Q fiber closed sep qx I _ e own pc legal
  have ⟨head,slot⟩ := root_header hp C (fiber _ qx)
  have frame := (BStarCommitGeneratedTail.generated_flight hp (addr:=adr) slot head (sep e) I E
    (pc.symm ▸ (by decide : stageOp≠1))
    (by rintro ⟨_,Z,_⟩; cases Z) (fun _=>.inl (by intro Z; cases Z))).2
  have canon := (StageSealPreserve.actual_stage_launch _ _ pc F d D).1
  have payload : project adr (step x e) 0=.forward (BStarStageIssue.payload (x (adr 0).1).long) := by
    change (BStarLongToken.atSite (step x e (adr 0).1).long (adr 0).2)=_
    rw [slot]
    exact canon
  exact ⟨E,J,payload,frame⟩

#print axioms actual_launch_at_door
end L4.Height.StageScopedLaunch
