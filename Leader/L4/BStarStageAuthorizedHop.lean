import Leader.L4.BStarStageGuardFromHop
import Leader.L4.BStarStageFrom407
import Leader.L4.BStarStageArgFrom407

namespace L4.BStarStageAuthorizedHop
open AllSizeProtocol BStarTrace BStarLongWork BStarLongClaims BStarLongToken
open BStarLongTransport BStarLongEvents BStarLongLiteral BStarLongRouting BStarLongCommand
open BStarAcquireVisitOrder BStarAcquireLiteralChain BStarAcquireForwardTrace BStarH6WordChart
open BStarResetChartTouch BStarResetMarkAdapter BStarResetRailRing BStarSeparatingRail
open BStarGeneratedOwner BStarOwnerLaunchOrigin BStarAcquireRailCoverage BStarAcquireAnchors
open BStarStageCandidateRetention BStarBankTrace BStarStageProvenance
open BStarLongFiberOwner BStarGeneratedTapeCuts BStarCommitTailScan
open BStarStageAckExtract BStarStageHopExtract BStarClearanceSource BStarLongDoor

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step B
local notation "run" => BStarResetSchedule.run step
local notation "pc" => BStarGeneratedBandScan.pc

open BStarStageHopExtract BStarStageGuardFromHop BStarLongPublication
open BStarResetSchedule BStarSeparatorControl BStarAcquireHistorySample

private theorem single_advance {x : X} {addr : Nat → Pos n} {len : Nat} {e : Fin n}
    {z d : Cursor} (seen : Seen step (project addr) anyTag len x z [e] d) :
    Advance len z d := by
  cases seen with
  | cons _ _ t _ tail => cases tail; exact t

/-- Every chosen chart position strictly before the terminal is crossed
once on its exact actual healthy outward STAGE flight. Extract its
original raw split, old and new owner modes, offer and unchanged
effective argument; no independent favorable route is chosen. -/
theorem find {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    {w : List (Fin n)} {z d : Cursor}
    (T : BusyOnly hp base (fun j => S.getD j fall) len stageOp x z w d)
    (k : Nat) (pay : Payload) (healthy : Stage pay) :
    ∀ f l, z=.out f → d=.out l → f≤k → k<l → l≤len →
      project (fun j => S.getD j fall) (run x w) l=.forward pay →
      ∃ pre e post, w=pre++e::post ∧
        BusyOnly hp base (fun j => S.getD j fall) len stageOp x (.out f) pre (.out k) ∧
        let old := run x pre
        let raw := ((old e).long,(old (rightNeighbor e)).long)
        Event hp (fun j => S.getD j fall) len old e (.busy stageOp (.out k)) (.busy stageOp (.out (k+1))) ∧
        BusyOnly hp base (fun j => S.getD j fall) len stageOp (step old e) (.out (k+1)) post (.out l) ∧
        ∃ K a q, (K,.advance q)∈actualOffers (oldPair B old e) raw ∧
          K.destination=some a ∧ S.getD k fall=address e K.source ∧
          S.getD (k+1) fall=address e a ∧ Stage q ∧ arg q=arg pay ∧
          (K.source=L 1 → ∀ D, BStarLongPublication.decode (descriptorBits q)=some D →
            oldH6 B old e=true → BStarLongOutgoing.actual (old e).long D=true) := by
  induction T with
  | nil I =>
    intro f l F L fk kl _ _
    have := Cursor.out.inj (F.symm.trans L)
    omega
  | @cons x z next d e w I E tail ih =>
    intro f l F L fk kl le ok
    subst z
    obtain ⟨j,J⟩ := busy_no_back_to_out hp tail ⟨l,L⟩
    subst next
    have A : Advance len (.out f) (.out j) := by
      cases E with
      | transit _ _ _ _ seen => exact single_advance hp seen
    cases A with
    | stay =>
      obtain ⟨pre,m,post,R,lead,ev,after,sel⟩ := ih f l rfl L fk kl le ok
      exact ⟨e::pre,m,post,congrArg (List.cons e) R,.cons I E lead,ev,after,sel⟩
    | forward =>
      by_cases eq : f=k
      · subst f
        obtain ⟨j,hj,q,Q,Sq,eqArg⟩ :=
          BStarStageOwnerOrigin.busy_origin hp C sep tail l le pay ok healthy
        have W := busy_start hp tail
        have eq := (BStarOwnerControlHistory.pointed_unique_forward _ len _ W.2.1 W.2.2 j hj).mp ⟨q,Q⟩
        subst j
        obtain ⟨K,a,v,sel,dest,src,arr,vh,varg⟩ :=
          chart_hop hp C e (sep e) k (by omega) I q Q Sq
        refine ⟨[],e,w,rfl,.nil I,E,L ▸ tail,K,a,v,sel,dest,src,arr,vh,varg.trans eqArg,?_⟩
        intro source D desc head
        have land := (new_read B x e (sep e) a).trans
          ((congrArg (BStarAcquireForwardTrace.atCursor (step x e)) arr).symm.trans Q)
        exact authorized _ _ _ _ _ _ _ _ _ hp (x e,x (rightNeighbor e)) K a v q D
          dest source sel land vh Sq desc head
      · obtain ⟨pre,m,post,R,lead,ev,after,sel⟩ := ih (f+1) l rfl L (by omega) kl le ok
        exact ⟨e::pre,m,post,congrArg (List.cons e) R,.cons I E lead,ev,after,sel⟩

#print axioms find
end L4.BStarStageAuthorizedHop
