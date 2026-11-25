import Leader.L4.BStarRRELHold
import Leader.L4.BStarNativeReceiptTape
import Leader.L4.BStarGeneratedTapeCuts
import Leader.L4.BStarSerialResetHealth
import Leader.L4.BStarOwnerLaunchOrigin

namespace L4.BStarRRELExtract
open AllSizeProtocol BStarTrace BStarLongWork BStarLongDoor BStarLongCommand
open BStarLongToken BStarH6WordChart BStarAcquireVisitOrder BStarAcquireLiteralChain
open BStarAcquireAnchors BStarResetChartTouch BStarLongFixedRouting
open BStarResetMarkAdapter BStarSeparatingRail BStarResetSchedule BStarSeparatorControl
open BStarGeneratedOwner BStarResetChartService BStarOwnerLaunchOrigin BStarGeneratedTapeCuts BStarForwardProvenance
open BStarResetHealthyService BStarResetTaggedRows BStarResetCycle BStarSerialResetHealth
open BStarClearanceSource

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step (n:=n) B
local notation "run" => BStarResetSchedule.run step

private theorem holds_away {base x : X} {addr : Nat→Pos n} {len op : Nat} {w : List (Fin n)}
    {d : Cursor} (T : BusyOnly hp base addr len op x (.back 0) w d) :
    ∀ e∈w,e≠RearTrace.predecessor (addr 0).1 := by
  generalize E : Cursor.back 0 = z at T
  induction T with
  | nil => simp
  | @cons x1 z1 d1 endC e1 w1 I Evt tail ih =>
    subst z1
    cases Evt with
    | transit _ _ _ live _ => exact (live rfl).elim
    | arrived_hold _ away =>
      intro e M
      rcases List.mem_cons.mp M with eq|M
      · exact eq.symm ▸ away
      · exact ih rfl e M

theorem healthy_first_return {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall)
    (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (Q : X → Prop) (init : Q x)
    (fiber : ∀ x,Q x → ∀ i,Layout B base i=Layout B x i)
    (closed : ∀ x e,Q x → Q (step x e))
    {z : Cursor} {w : List (Fin n)}
    (T : BusyOnly hp base (fun j => S.getD j fall) len 2 x z w (.back 0))
    (G : Good (healthyTag 2) len (project (fun j=>S.getD j fall) x) z) :
    ∃ pre hold, w=pre++hold ∧
      Seen step (project (fun j=>S.getD j fall)) (healthyTag 2) len x z pre (.back 0) ∧
      project (fun j=>S.getD j fall) (run x pre) 0=finish (resetPayload 2) ∧
      ∀ e∈hold,e≠RearTrace.predecessor (S.getD 0 fall).1 := by
  generalize D : Cursor.back 0 = last at T
  induction T with
  | nil I =>
    cases D
    exact ⟨[],[],rfl,.nil _ _,G.2.1,by simp⟩
  | @cons x z d endC e w I E tail ih =>
    cases E with
    | arrived_hold _ away =>
      subst endC
      refine ⟨[],e::w,rfl,.nil _ _,G.2.1,?_⟩
      intro a M
      rcases List.mem_cons.mp M with eq|M
      · exact eq.symm ▸ away
      · exact holds_away hp tail a M
    | transit op z d live _ =>
      let m := (healthyService hp C (fiber x init) e (sep e) 2 (by decide)
        z live G I.1.2.1 I.1.2.2.1).mark
      obtain ⟨d',adv,next⟩ := lift_mark m z live G
      have eq := healthy_matches next (busy_start hp tail).2.1
      subst d'
      obtain ⟨pre,hold,W,F,H,A⟩ := ih (closed _ _ init) next D
      exact ⟨e::pre,hold,congrArg (List.cons e) W,.cons live m adv next F,H,A⟩

#print axioms healthy_first_return

open BStarRRELHold BStarResetNoAcquire BStarGrantBirth

private theorem keep_word (Q : X → Prop)
    (closed : ∀ a e,Q a → Q (step a e)) (w : List (Fin n)) (x : X)
    (H : Q x) : Q (run x w) := by
  induction w generalizing x with
  | nil => exact H
  | cons e w ih => exact ih _ (closed _ _ H)

theorem generated_rrel_grant_zero {base x : X} {hh : ∃ withH,oldH6 B base withH=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall)
    (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (Q : X → Prop) (init : Q x)
    (fiber : ∀ x,Q x → ∀ i,Layout B base i=Layout B x i)
    (closed : ∀ x e,Q x → Q (step x e))
    (w : List (Fin n)) (e i : Fin n) (j : Fin 3)
    (own : commandOwner (oldH6 B base) i (slot j)=o.val)
    (T : GeneratedOwner hp base (fun k=>S.getD k fall) len x .idle w (.busy 2 (.back 0)))
    (hit : BStarNativeReceiptTape.Hit hp base (fun k=>S.getD k fall) len (run x w) e 2) :
    bit (run x w) i j=0 ∧ bit (step (run x w) e) i j=0 := by
  let adr := fun k => S.getD k fall
  let root := (adr 0).1
  let door := RearTrace.predecessor root
  obtain ⟨pre,post,launch,W,atDoor,launches,pc2,busy⟩ := from_idle hp T
  change launch=door at atDoor
  subst launch
  obtain ⟨m,head,_⟩ := BStarGeneratedTapeCuts.split hp pre (door::post) (W ▸ T)
  let y := run x pre
  have mode := idle_of_issue hp (at_end hp head) launches.1
  subst m
  have clean := (at_end hp head).2
  have qy : Q y := keep_word hp Q closed pre x init
  let z := step y door
  have qz : Q z := closed _ _ qy
  obtain ⟨HDR,K⟩ := root_header hp C (fiber _ qy)
  have D : rightNeighbor door=root := RearTrace.right_predecessor root
  have ph := launches.1.2
  have good := genuine_wait hp y door (sep door) 2 (by decide)
    (D.symm ▸ HDR) (D.symm ▸ ph) (D.symm ▸ pc2)
  rw [D] at good
  have F : project adr z 0=.forward (resetPayload 2) :=
    (congrArg (BStarAcquireForwardTrace.atCursor z) (show adr 0=(root,0) from Prod.ext rfl K)).trans good.1
  have G : Good (healthyTag 2) len (project adr z) (.out 0) :=
    ⟨Nat.zero_le _,F,fun _ H => (Nat.not_lt_zero _ H).elim⟩
  obtain ⟨flight,hold,E,seen,reply,foreign⟩ :=
    healthy_first_return hp C sep Q qz fiber closed busy G
  obtain ⟨Qz,CleanZ,zero⟩ :=
    first_arrival_zero hp C sep Q qy fiber closed clean flight i j own ph pc2 seen reply
  have bars := hold_then_ack_zero hp C sep Q Qz fiber closed CleanZ i j own zero hold foreign
  have exp : run x w=run (run z flight) hold := by
    rw [W,BStarResetSchedule.run_append]
    change run z post=_
    rw [E,BStarResetSchedule.run_append]
  have eDoor : e=door := hit.2.2.2.2.1
  rw [exp,eDoor]
  exact bars

#print axioms generated_rrel_grant_zero
end L4.BStarRRELExtract
