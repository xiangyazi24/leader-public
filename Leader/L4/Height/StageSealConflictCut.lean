import Leader.L4.Height.StageSealOriginal
import Leader.L4.Height.StageWriterCoherence
namespace L4.Height.StageSealConflictCut
open AllSizeProtocol BStarTrace BStarLongWork BStarLongClaims BStarLongToken
open BStarLongCommand BStarLongDoor BStarLongLayout BStarLongPublication
open BStarH6WordChart BStarAcquireVisitOrder BStarAcquireLiteralChain BStarResetChartTouch
open BStarGeneratedOwner BStarLongGrant BStarGrantReaderHistory BStarLongLandingFrame BStarLongFiberOwner BStarPublicationBirth BStarGrantBirth BStarAcquireAnchors
variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step (n:=n) B
local notation "play" => BStarResetSchedule.run step
open BStarAcquireHistoryReturn BStarGeneratedTapeCuts BStarOwnerLaunchOrigin
open BStarSeparatingRail BStarAcquireForwardTrace BStarSealParity BStarResetMarkAdapter BStarClearanceSource BStarSealHealthyHop BStarLongFixedRouting
open BStarLongLiteral BStarLongEvents BStarLongTransport StageSealExactFrame StageActualBusy StageScopedReplay

theorem conflict_at_center {base origin x : X} {hh : ∃ j,oldH6 B base j=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall) (Q : X→Prop)
    (fiber : ∀ y,Q y→∀ j,Layout B base j=Layout B y j)
    (closed : ∀ y,Q y→∀ e,Q (step y e)) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (i : Fin n) (own : commandOwner (oldH6 B base) i 1=o.val)
    (k : Nat) (K : k<len) (idx : S.getD k fall=(i,1)) (head : oldH6 B base i=true)
    (lead : List (Fin n)) (landed : play origin lead=x)
    (G : GeneratedOwner hp base (fun j=>S.getD j fall) len origin .idle lead (.busy stageOp (.out 0)))
    (source : BitVec LW) (d : Descriptor)
    (D : BStarLongPublication.decode (sourceDescriptor.read source)=some d)
    {w : List (Fin n)}
    (qx : Q x) (wire : Wire (fun j=>S.getD j fall) x source (.out 0))
    (auth : PrefixAuth hp base x (fun j=>S.getD j fall) len 0 source d w)
    (qOrigin : Q origin)
    (early : (ctrlOp.read (origin (S.getD 0 fall).1).long).toNat<6)
    : ∀ u v,w=u++i::v →
      BusyOnly hp base (fun j=>S.getD j fall) len stageOp x (.out 0) u (.out k) →
      conflict (ports (play x u) i)=false := by
  intro u v W U
  let old := play x u
  let geom := oldPair B old i
  let claim := centerLink geom
  let pay := BStarStageIssue.payload source
  let raw := ((old i).long,(old (rightNeighbor i)).long)
  have resolved := wire_of_busy hp C Q fiber closed sep source d D U qx wire (by
    intro j eq
    have Z : j=0 := (Cursor.out.inj eq).symm
    subst j
    exact auth.take hp u (i::v) W)
  have rawF : readK raw claim.source=.forward pay := by
    change atSite (old i).long 1=_
    change atCursor old (S.getD k fall)=_ at resolved
    rw [idx] at resolved
    exact resolved
  have selected : (claim,.advance pay)∈actualOffers geom raw := by
    apply StageHealthyHop.bound_stage_selected _ _ _ _ (center_mem _) (show Cmd.link≠Cmd.door by decide) _ rfl
    unfold bound
    rw [rawF]
    exact BStarStageIssue.bound_forward_exact _ _ source d D
  have ancestry := generated_append hp G (landed.symm ▸ busy_generated hp U)
  have O : play origin (lead++u)=old := by rw [BStarResetSchedule.run_append,landed]
  have pass : (BStarBankTrace.beforeOutgoing geom raw claim pay).2=pay := by
    unfold BStarBankTrace.beforeOutgoing BStarLongArithmetic.visit
    split
    · rfl
    · rw [show pay.opcode.toNat=stageOp from rfl,show BStarLongArithmetic.nodeOf stageOp=none by decide]
  have canonical : BStarStageProvenance.Stage pay := ⟨rfl,rfl⟩
  have desc : BStarStageDescriptorHistory.descOfStage pay=some d :=
    (BStarStageIssue.issued_descriptor source).trans D
  have live := StageWriterCoherence.stage_coherent hp C Q qOrigin fiber (fun y e q=>closed y q e) sep ancestry
    (at_end hp ancestry) early k (Nat.le_of_lt K) i claim pay idx i head own d
  rw [O] at live
  exact live selected (pass.symm ▸ canonical) (pass.symm ▸ desc)

#print axioms conflict_at_center
end L4.Height.StageSealConflictCut
