import Leader.L4.BStarSealPositiveTerminal
import Leader.L4.Height.StageHealthyHop
import Leader.L4.Height.StageReplyForm
namespace L4.Height.StagePositiveTerminal
open AllSizeProtocol BStarTrace BStarLongClaims BStarLongWork BStarLongToken
open BStarLongCommand BStarLongEvents BStarLongTransport BStarLongRouting
open BStarH6WordChart BStarAcquireVisitOrder BStarAcquireLiteralChain BStarResetChartTouch BStarResetMarkAdapter
open BStarSeparatingRail BStarSeparatorControl BStarSeparatorQuiet BStarGeneratedOwner
open BStarOwnerLaunchOrigin BStarAcquireForwardTrace BStarAcquireHistorySample
open BStarLongFixedRouting BStarResetChartService BStarResetQuiet BStarResetQuietTable
open BStarSealHealthyHop BStarLongDoor
open BStarClearanceForward BStarLongLayout

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step (n:=n) B
local notation "play" => BStarResetSchedule.run step

/-- The nominated physical STAGE terminal starts its canonical zero-argument reply. -/
theorem nominated_turn {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall)
    (Q : X→Prop) (fiber : ∀ x,Q x→∀ i,Layout B base i=Layout B x i)
    (closed : ∀ x,Q x→∀ e,Q (step x e)) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (qx : Q x) (e : Fin n) (source : BitVec LW) (d : BStarLongPublication.Descriptor)
    (D : BStarLongPublication.decode (sourceDescriptor.read source)=some d)
    (cur : Current hp base (fun j=>S.getD j fall) len x (.busy stageOp (.out len)))
    (old : project (fun j=>S.getD j fall) x len= .forward (BStarStageIssue.payload source))
    (mark : onTerminal hp x e (fun j=>S.getD j fall) len) :
    Event hp (fun j=>S.getD j fall) len x e (.busy stageOp (.out len)) (.busy stageOp (.back len)) ∧
    Current hp base (fun j=>S.getD j fall) len (step x e) (.busy stageOp (.back len)) ∧
      project (fun j=>S.getD j fall) (step x e) len=.reply L4.Height.StageReplyForm.reply := by
  let pay := BStarStageIssue.payload source
  obtain ⟨K,mem,kind,dest,at10,idx⟩ := mark
  let g := oldPair B x e
  let raw : Pair (BitVec LW) := ((x e).long,(x (rightNeighbor e)).long)
  have addr : readK raw K.source=.forward pay :=
    (BStarResetRailRing.old_read x e K.source).trans ((congrArg (atCursor x) idx).symm.trans old)
  have sel : (K,.advance pay)∈actualOffers g raw := by
    apply L4.Height.StageHealthyHop.bound_stage_selected g raw K pay mem (by rw [kind]; decide) _ rfl
    unfold bound
    rw [addr]
    exact BStarStageIssue.bound_forward_exact _ _ source d D
  have valid : K.source=R 0 → g.2.axes.h6=true → LongDoorGuard.valid manifest raw.2=true := by
    intro J _
    rw [J] at at10
    contradiction
  have lands := BStarResetRailRing.new_read B x e (sep e) K.source
  change BStarLongToken.decode (readRaw _ K.source)=_ at lands
  erw [joined_work_raw _ _ _ _ _ _ _ _ _ hp (x e,x (rightNeighbor e)) K.source valid] at lands
  change BStarLongToken.decode (readRaw (patchPair (longWork g raw) raw) K.source)=_ at lands
  rw [terminal_finish g raw K pay dest sel,BStarLongToken.decode_encode] at lands
  change finish (carried g raw K pay)=atCursor (step x e) (address e K.source) at lands
  have eq : carried g raw K pay=pay := by
    unfold carried BStarLongArithmetic.visit
    have M : (K.source.occurrence.val != 1)=true := bne_iff_ne.mpr (by omega)
    simp only [M,Bool.true_or,if_true]
    rw [BStarLongOutgoing.noncenter_hold _ _ _ _ (by omega)]
    rfl
  rw [eq,L4.Height.StageReplyForm.finish_exact pay rfl rfl,←idx] at lands
  obtain ⟨m,E,I⟩ := current_step hp C Q fiber closed sep qx e (.busy stageOp (.out len)) cur
  cases E with
  | transit _ _ d live seen =>
    cases seen with
    | cons M go A G tail =>
      cases tail
      cases A with
      | stay _ =>
        obtain ⟨q,U⟩ := I.2.1.2.1
        exact Token.noConfusion (U.symm.trans lands.symm)
      | forward _ =>
        have bound := I.2.1.1
        omega
      | turn =>
        exact ⟨.transit _ _ _ live (.cons M go .turn G (.nil _ _)),I,lands.symm⟩

#print axioms nominated_turn
end L4.Height.StagePositiveTerminal
