import Leader.L4.BStarStageAckExtract

namespace L4.BStarStageHopExtract
open AllSizeProtocol BStarTrace BStarLongClaims BStarLongToken BStarLongCommand
open BStarLongTransport BStarLongEvents BStarLongWork BStarLongLiteral BStarLongCommandData
open BStarClearanceForward BStarResetQuiet BStarResetQuietTable

open BStarStageProvenance

open BStarLongRouting

private theorem failed (p : Payload) : Back p failedPayload := by
  intro H
  exact (show (1 : BitVec 1)≠0 by decide) H.1 |>.elim

private theorem no_gate (g : LongGeometry) (j : Fin 11) (p : Payload) (H : Stage p) :
    gate p.opcode.toNat j g=false := by
  rw [H.2]
  simp [gate,stageOp,admit,bitOp]

private theorem arrive_back (g : LongGeometry) (j : Fin 11) (p q : Payload)
    (H : arrive g j p=.forward q) : Back p q := by
  unfold arrive at H
  split at H
  · rename_i A
    cases H
    intro S
    have T : Stage p := S
    simp [no_gate g j p T] at A
  · cases H; exact Back.refl _

private theorem outgoing_back (g : LongGeometry) (j : Fin 11) (x : BitVec LW) (p q : Payload)
    (H : (BStarLongOutgoing.execute g j x p).carried=.forward q) :
    Back p q := by
  intro F
  unfold BStarLongOutgoing.execute at H
  dsimp only at H
  repeat' first
    | (change (Token.forward p) = .forward q at H; cases H; exact ⟨F,rfl⟩)
    | (change fault false = .forward q at H; unfold fault at H; cases H; exact ((show (1 : BitVec 1)≠0 by decide) F.1).elim)
    | split at H
  cases H
  have sealGuard := ‹(p.opcode.toNat == sealOp && g.axes.h6)=true›
  have S : p.opcode.toNat=stageOp := F.2
  simp [S,stageOp,sealOp] at sealGuard

private theorem carried_back (g : Pair LongGeometry) (x : Pair (BitVec LW))
    (c : CommandClaim) (p : Payload) : Back p (carried g x c p) := by
  unfold carried
  dsimp only
  split
  · rename_i q E
    exact (before_outgoing_back _ _ _ _).trans (outgoing_back _ _ _ _ q E)
  all_goals exact failed _

theorem joined_hop_offer (k₁ k₂ t₂ J₁ J₂ r n p c₁ : Nat) (hp : 0<p)
    (x : Pair (LargeSite (production k₁ k₂ t₂ J₁ J₂ r n p c₁)))
    (c : CommandClaim) (a : AtK) (offer after : Payload) :
    let b := bStar k₁ k₂ t₂ J₁ J₂ r n p c₁ hp
    let g := Pair.map (longGeometry b) x
    let raw : Pair (BitVec LW) := Pair.map LargeSite.long x
    let y : Pair (BitVec LW) := Pair.map LargeSite.long (largePair b x)
    c.destination=some a → (c,.advance offer)∈actualOffers g raw →
    readK y a=.forward after → Stage after →
    Stage offer ∧ arg offer=arg after := by
  dsimp only
  intro dst sel land healthy
  let b := bStar k₁ k₂ t₂ J₁ J₂ r n p c₁ hp
  let g := Pair.map (longGeometry b) x
  let raw : Pair (BitVec LW) := Pair.map LargeSite.long x
  let y : Pair (BitVec LW) := Pair.map LargeSite.long (largePair b x)
  have hm : c∈orderedCommands g := by
    rw [←actualOffers_claims g raw]
    exact List.mem_map.mpr ⟨_,sel,rfl⟩
  have ne := (BStarAcquireReturn.link_shape g c a hm dst).1
  have V : a=R 0 → g.2.axes.h6=true → LongDoorGuard.valid manifest raw.2=true := by
    intro E Z
    have J : a.occurrence.val=0 := congrArg (fun z : AtK => z.occurrence.val) E
    have H := (BStarAcquireJoinedHop.k0_dest g c a hm dst J).2
    simp [Z] at H
  have A := (move_lands g raw c offer a dst sel (Ne.symm ne)).2
  have Arr : arrive (geometry g a.side) a.occurrence (carried g raw c offer)=.forward after := by
    change decode (readRaw y a)=.forward after at land
    erw [joined_work_raw _ _ _ _ _ _ _ _ _ hp x a V,A,decode_encode] at land
    exact land
  exact ((carried_back g raw c offer).trans (arrive_back _ _ _ _ Arr)) healthy

open BStarH6WordChart BStarAcquireVisitOrder BStarAcquireAnchors BStarAcquireLiteralChain
open BStarResetChartTouch BStarGeneratedOwner BStarLongFixedRouting BStarLongFiberOwner
open BStarOwnerLaunchOrigin BStarSeparatingRail BStarResetSchedule BStarResetRailRing
open BStarSeparatorControl
open BStarResetMarkAdapter BStarAcquireHistorySample

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step B
local notation "run" => BStarResetSchedule.run step

/-- Exact owner-chart hop reconstructed from the actual healthy successor
and old outward cursor. The selected offer, not merely the next held
token, is a healthy STAGE with the same effective argument. -/
theorem chart_hop {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall) (e : Fin n) (sep : e≠rightNeighbor e)
    (k : Nat) (hk : k<len)
    (old : Current hp base (fun j => S.getD j fall) len x (.busy stageOp (.out k)))
    (pay : Payload) (new : project (fun j => S.getD j fall) (step x e) (k+1)=.forward pay)
    (healthy : Stage pay) :
    let g := oldPair B x e
    let raw := ((x e).long,(x (rightNeighbor e)).long)
    ∃ K a q, (K,.advance q)∈actualOffers g raw ∧ K.destination=some a ∧
      S.getD k fall=address e K.source ∧ S.getD (k+1) fall=address e a ∧
      Stage q ∧ arg q=arg pay := by
  obtain ⟨K,a,q,sel,dst,src,newAddr⟩ :=
    BStarNumericChronology.ring_departure hp C e sep stageOp k hk old.1 old.2.1 old.2.2
      pay new healthy.1
  have land := (new_read B x e sep a).trans ((congrArg (BStarAcquireForwardTrace.atCursor (step x e)) newAddr).symm.trans new)
  exact ⟨K,a,q,sel,dst,src,newAddr,joined_hop_offer _ _ _ _ _ _ _ _ _ hp
    (x e,x (rightNeighbor e)) K a q pay dst sel land healthy⟩

private theorem single_advance {x : X} {addr : Nat → Pos n} {len : Nat} {e : Fin n}
    {z d : Cursor} (seen : Seen step (project addr) anyTag len x z [e] d) :
    Advance len z d := by
  cases seen with
  | cons _ _ t _ tail => cases tail; exact t

/-- Every chosen chart position strictly before the terminal is crossed
once on its exact actual healthy outward STAGE flight. Extract its
original raw split, old and new owner modes, offer and unchanged
effective argument; no independent favorable route is chosen. -/
theorem find_stage_departure {base x : X} {hh : ∃ i,oldH6 B base i=true}
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
          S.getD (k+1) fall=address e a ∧ Stage q ∧ arg q=arg pay := by
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
        exact ⟨[],e,w,rfl,.nil I,E,L ▸ tail,K,a,v,sel,dest,src,arr,vh,varg.trans eqArg⟩
      · obtain ⟨pre,m,post,R,lead,ev,after,sel⟩ := ih (f+1) l rfl L (by omega) kl le ok
        exact ⟨e::pre,m,post,congrArg (List.cons e) R,.cons I E lead,ev,after,sel⟩

#print axioms chart_hop
#print axioms find_stage_departure
#print axioms joined_hop_offer
end L4.BStarStageHopExtract
