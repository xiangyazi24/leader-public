import Leader.L4.Height.AdmissionTour
import Leader.L4.BStarOutwardSelectedLink
import Leader.L4.BStarAdmissionObservationBound

namespace L4.BStarAdmissionTraceBound
open AllSizeProtocol BStarTrace BStarLongWork BStarLongDoor BStarLongCommand
open BStarLongToken BStarH6WordChart BStarAcquireVisitOrder BStarAcquireLiteralChain
open BStarLongClaims BStarAcquireAnchors BStarResetChartTouch BStarLongFixedRouting
open BStarResetMarkAdapter BStarSeparatingRail BStarResetSchedule BStarGeneratedOwner
open BStarResetChartService BStarOwnerLaunchOrigin BStarOutwardSelectedLink BStarClearanceOffset
open L4.Height.AdmissionTour BStarAdmissionObservationBound

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step (n:=n) B
local notation "run" => BStarResetSchedule.run step

private theorem keep_word (Q : X → Prop)
    (closed : ∀ x,Q x → ∀ e,Q (step x e)) (w : List (Fin n)) (x : X)
    (H : Q x) : Q (run x w) := by
  induction w generalizing x with
  | nil => exact H
  | cons e w ih => exact ih _ (closed _ H _)

theorem actual_tour_bound {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall)
    (Q : X→Prop) (fiber : ∀ x,Q x→∀ i,Layout B base i=Layout B x i)
    (closed : ∀ x,Q x→∀ e,Q (step x e))
    (ready : ∀ x,Q x→correct (oldH6 B base) hh 5 x)
    (sep : ∀ e : Fin n,e≠rightNeighbor e) (qx : Q x)
    (i : Fin n) (k : Nat) (K : k+1<len) (loc : S.getD (k+1) fall=(i,1))
    (ord : BStarH6Ordinal.oldOrdinal B base hh i=2)
    (w : List (Fin n))
    (T : GeneratedOwner hp base (fun j=>S.getD j fall) len x .idle w (.busy admit (.back 0)))
    (ack : Fin n)
    (E : Event hp (fun j=>S.getD j fall) len (run x w) ack (.busy admit (.back 0)) .idle) :
    ∃ (launchPre before gap middle after : List (Fin n)) (door enter first other : Fin n) (s t : Side),
      w=launchPre++door::(before++enter::(gap++first::(middle++other::after))) ∧
      (∀ e∈gap,∀ u,BStarAcquireDoorHistory.siteOf e u≠i) ∧
      BStarAcquireDoorHistory.siteOf first s=i ∧ t≠s ∧ BStarAcquireDoorHistory.siteOf other t=i ∧
      (∀ e∈middle,∀ u,BStarAcquireDoorHistory.siteOf e u=i→u=s) ∧
      (let addr := fun j=>S.getD j fall
       let old := run x launchPre
       let launched := step old door
       let departs := run launched before
       let arrives := run x (launchPre++door::(before++[enter]))
       let oldFirst := run x (launchPre++door::(before++enter::gap))
       door=RearTrace.predecessor (addr 0).1 ∧
       BStarClearanceSource.Launch (old (addr 0).1).long (launched (addr 0).1).long ∧
       (ctrlOp.read (old (addr 0).1).long).toNat=admit ∧
       BusyOnly hp base addr len admit launched (.out 0) before (.out k) ∧
       Current hp base addr len departs (.busy admit (.out k)) ∧
       linkAt hp departs enter addr len k ∧
       Current hp base addr len arrives (.busy admit (.out (k+1))) ∧
       BusyOnly hp base addr len admit arrives (.out (k+1)) gap (.out (k+1)) ∧
       Current hp base addr len oldFirst (.busy admit (.out (k+1))) ∧
       BStarLongCommand.bind (longGeometry B (oldFirst i)) 1 (atSite (oldFirst i).long 1)=.forward (atGate 1)) ∧
      (BStarResetControllerEntry.snapshot (step (run x w) ack (S.getD 0 fall).1).long =
        ((.empty,1),BitVec.ofNat 9 (if s==.left then acquire else 412))) ∧
      let site := run x w (S.getD 0 fall).1
      BStarLongCommand.bind (longGeometry B site) 0 (atSite site.long 0)=.reply (packet true (s==.left)) := by
  let addr := fun j=>S.getD j fall
  obtain ⟨lead,door,before,enter,tail,W,D,L,pc,P,departCur,arriveCur,link,busy⟩ :=
    from_idle_crossing hp C sep (show k<len by omega) T
  let old := run x lead
  let started := step old door
  let arrives := step (run started before) enter
  have qo : Q old := keep_word hp Q closed lead x qx
  have qs := closed old qo door
  have qa : Q arrives := closed _ (keep_word hp Q closed before _ qs) enter
  have scope (y : X) (qy : Q y) (j : Nat) (J : j≤len) :
      gate admit (addr j).2 (longGeometry B (y (addr j).1))=true ↔ j=k+1 := by
    apply admit_gate_scope hp C
      (fun i=>(congrArg Prod.fst (fiber y qy i)).symm) (ready y qy)
      (k+1) (by omega) (congrArg Prod.snd loc) _ j J
    rw [loc]
    exact ord
  have F := admission_from_ready_issue_to_gate hp C sep door pc L k P
    (fun a b _ j J=>scope _ (keep_word hp Q closed a _ qs) j J) enter link
  obtain ⟨gap,middle,after,first,other,s,t,V,quiet,firstAt,diff,otherAt,holds,gapBusy,preCur,bindPre,ret,front⟩ :=
    gate_observations_for_return_bound hp C Q fiber closed ready sep qa i (k+1) (by omega) loc ord busy F
  let settled := step (run (step (run arrives gap) first) middle) other
  have rt : run x w=run settled after := by
    rw [W,BStarResetSchedule.run_append]
    change run started (before++enter::tail)=_
    rw [BStarResetSchedule.run_append]
    change run arrives tail=_
    rw [V,BStarResetSchedule.run_append]
    change run (step (run arrives gap) first) (middle++other::after)=_
    rw [BStarResetSchedule.run_append]
    rfl
  have qb : Q settled := closed _ (keep_word hp Q closed middle _
    (closed _ (keep_word hp Q closed gap _ qa) first)) other
  have shape (j : Nat) (J : some (k+1)=some j) :
      j<len ∧ true=true ∧ (addr j).2=1 := by
    cases J
    exact ⟨K,rfl,congrArg Prod.snd loc⟩
  have G : project addr settled (k+1)=.forward (resolved true (s==.left) (some (k+1)) (k+1)) := by
    rw [resolved,if_pos rfl]
    exact front
  have out := resolved_consumes hp C sep true (s==.left) (some (k+1)) (k+1)
    shape ret (fun j J => (Option.some.inj J) ▸ Nat.le_refl (k+1))
    (fun pre _ _ j J => by
      rw [show opcode true=admit from rfl,scope _ (keep_word hp Q closed pre _ qb) j J,Option.some.injEq]
      exact eq_comm) G ack (rt ▸ E)
  refine ⟨lead,before,gap,middle,after,door,enter,first,other,s,t,by rw [W,V],quiet,
    firstAt,diff,otherAt,holds,?_⟩
  refine ⟨?_,?_⟩
  · have A : run x (lead++door::(before++[enter]))=arrives := by
      rw [BStarResetSchedule.run_append]
      change run started (before++[enter])=_
      rw [BStarResetSchedule.run_append]
      rfl
    have F : run x (lead++door::(before++enter::gap))=run arrives gap := by
      rw [BStarResetSchedule.run_append]
      change run started (before++enter::gap)=_
      rw [BStarResetSchedule.run_append]
      rfl
    dsimp only
    rw [A,F]
    exact ⟨D,L,pc,P,departCur,link,arriveCur,gapBusy,preCur,bindPre⟩
  · rw [rt]
    exact out

end L4.BStarAdmissionTraceBound
