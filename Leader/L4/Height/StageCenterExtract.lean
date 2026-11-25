import Leader.L4.Height.StageActualBusy
import Leader.L4.BStarStageHopExtract
import Leader.L4.BStarAcquireAckAncestry

namespace L4.Height.StageCenterExtract
open AllSizeProtocol BStarTrace BStarLongWork BStarLongClaims BStarLongToken
open BStarLongCommand BStarLongDoor BStarLongLayout BStarLongPublication BStarLongLiteral BStarLongEvents
open BStarH6WordChart BStarAcquireVisitOrder BStarAcquireLiteralChain BStarResetChartTouch BStarResetMarkAdapter
open BStarGeneratedOwner BStarOwnerLaunchOrigin BStarStageProvenance BStarStageCandidateJoined
open BStarLongFixedRouting StageActualBusy StageScopedReplay BStarSeparatingRail
variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step (n:=n) B
local notation "play" => BStarResetSchedule.run step

/-- The healthy original STAGE tape really crosses this center on its
outgoing physical mark, with the original issued descriptor. -/
theorem stage_center_mark {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall) (Q : X→Prop)
    (fiber : ∀ x,Q x→∀ i,Layout B base i=Layout B x i)
    (closed : ∀ x,Q x→∀ e,Q (step x e)) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (source : BitVec LW) (d : Descriptor)
    (D : BStarLongPublication.decode (sourceDescriptor.read source)=some d)
    (k : Nat) (K : k<len) (i : Fin n) (loc : S.getD k fall=(i,1))
    {w : List (Fin n)}
    (T : BusyOnly hp base (fun j=>S.getD j fall) len stageOp x (.out 0) w (.back 0))
    (qx : Q x) (wire : Wire (fun j=>S.getD j fall) x source (.out 0))
    (auth : PrefixAuth hp base x (fun j=>S.getD j fall) len 0 source d w) :
    ∃ pre post, w=pre++i::post ∧
      BusyOnly hp base (fun j=>S.getD j fall) len stageOp x (.out 0) pre (.out k) ∧
      let y := play x pre
      Event hp (fun j=>S.getD j fall) len y i (.busy stageOp (.out k)) (.busy stageOp (.out (k+1))) ∧
      ∃ pay, (centerLink (oldPair B y i),.advance pay)∈actualOffers (oldPair B y i)
        ((y i).long,(y (rightNeighbor i)).long) ∧
        Stage pay ∧ BStarStageDescriptorHistory.descOfStage pay=some d := by
  obtain ⟨u,t,v,W,O,turn,_⟩ := BStarAcquireAckAncestry.split_turn hp T
  have F := wire_of_busy hp C Q fiber closed sep source d D O qx wire (fun j eq=>by
    have E : j=0 := (Cursor.out.inj eq).symm
    subst j
    exact auth.take hp u (t::v) W)
  obtain ⟨pre,e,post,U,history,ev,_after,claim,a,q,sel,_dest,atSrc,_atDst,healthy,argEq⟩ :=
    BStarStageHopExtract.find_stage_departure hp C sep O k (BStarStageIssue.payload source)
      ⟨rfl,rfl⟩ 0 len rfl rfl (Nat.zero_le _) K (Nat.le_refl _) F
  let y := play x pre
  let gg := oldPair B y e
  have mem : claim∈orderedCommands gg := by
    rw [←actualOffers_claims gg ((y e).long,(y (rightNeighbor e)).long)]
    exact List.mem_map.mpr ⟨_,sel,rfl⟩
  have one : claim.source.occurrence.val=1 :=
    congrArg (fun z : Pos n=>z.2.val) (atSrc.symm.trans loc)
  have same : claim=centerLink gg := by
    have H : claim∈(orderedCommands gg).filter centerClaim :=
      List.mem_filter.mpr ⟨mem,by simp [centerClaim,one]⟩
    rw [one_center_claim] at H
    exact List.mem_singleton.mp H
  have ei : e=i := by
    have eq := congrArg Prod.fst (atSrc.symm.trans loc)
    rw [same] at eq
    exact eq
  subst e claim
  refine ⟨pre,post++t::v,by rw [W,U,List.append_assoc,List.cons_append],history,ev,q,sel,healthy,?_⟩
  have E := descriptor_of_arg argEq
  exact E.trans ((BStarStageIssue.issued_descriptor source).trans D)

end L4.Height.StageCenterExtract
