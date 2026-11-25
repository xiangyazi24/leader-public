import Leader.L4.BStarSealCenterAdvance

namespace L4.Height.SealHealthyEntry
open AllSizeProtocol BStarTrace BStarLongClaims BStarLongWork BStarLongToken
open BStarLongCommand BStarLongDoor BStarLongLayout BStarLongPublication
open BStarH6WordChart BStarAcquireVisitOrder BStarAcquireForwardTrace BStarAcquireLiteralChain
open BStarLongFixedRouting BStarResetChartTouch BStarResetMarkAdapter BStarGeneratedOwner
open BStarAcquireHistoryReturn BStarCommitIssue BStarSealHealthyHop BStarSealParity
open BStarOwnerLaunchOrigin BStarAcquireHistorySample BStarResetControllerEntry BStarClearanceSource
variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step (n:=n) B
local notation "play" => BStarResetSchedule.run step

/-- From the actual ISSUE409 and its busy prefix, derive a healthy selected
SEAL and the outgoing packet, without assuming a successful later ACK or
publication. Old writer authority and the STAGE latch are still explicitly required. -/
theorem actual_seal_of_stage {base start : X} {hh : ∃ i, oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall)
    (Q : X→Prop) (fiber : ∀ x,Q x→∀ i,Layout B base i=Layout B x i)
    (closed : ∀ x,Q x→∀ e,Q (step x e)) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (door i : Fin n) (w : List (Fin n)) (k : Nat) (bound : k<len)
    (loc : S.getD k fall=(i,1)) (head : oldH6 B base i=true)
    (op : (ctrlOp.read (start (S.getD 0 fall).1).long).toNat=sealOp)
    (launch : Launch (start (S.getD 0 fall).1).long ((step start door) (S.getD 0 fall).1).long)
    (T : BusyOnly hp base (fun j=>S.getD j fall) len sealOp (step start door) (.out 0) w (.out k))
    (d : Descriptor)
    (decoded : BStarLongPublication.decode (sourceDescriptor.read (start (S.getD 0 fall).1).long)=some d)
    (qx : Q (play (step start door) w))
    (auth : BStarLongOutgoing.actual (play (step start door) w i).long d=true)
    (staged : readOptional (stage.read (play (step start door) w i).long)=some d) :
    let addr := fun j=>S.getD j fall
    let x := play (step start door) w
    ∃ v, Event hp addr len x i (.busy sealOp (.out k)) (.busy sealOp (.out (k+1))) ∧
      Current hp base addr len (step x i) (.busy sealOp (.out (k+1))) ∧
      project addr (step x i) (k+1)=.forward v ∧ Well v ∧ parity v=d.need.toNat := by
  obtain ⟨p,W,sel,D⟩ := BStarSealHealthyFlight.selected_at_center hp C sep door i w k bound loc head op launch T d decoded
  exact BStarSealCenterAdvance.accepted_step hp C Q fiber closed sep qx i k bound loc head
    (busy_end hp T) p W d sel D auth staged

#print axioms actual_seal_of_stage
end L4.Height.SealHealthyEntry
