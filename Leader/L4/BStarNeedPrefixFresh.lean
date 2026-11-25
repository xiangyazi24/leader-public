import Leader.L4.BStarNeedTailService
import Leader.L4.BStarNeedOneRead

namespace L4.BStarNeedPrefixFresh
set_option maxRecDepth 4096
set_option maxHeartbeats 1500000

open AllSizeProtocol BStarTrace BStarLongClaims BStarLongWork BStarLongToken
open BStarLongCommand BStarLongEvents BStarH6WordChart BStarAcquireVisitOrder
open BStarAcquireLiteralChain BStarResetChartTouch BStarResetMarkAdapter BStarLongFixedRouting
open BStarSeparatingRail BStarGeneratedOwner BStarOwnerLaunchOrigin BStarAcquireForwardTrace
open BStarLongDoor BStarLongLayout BStarResetChartService BStarClearanceSource
open BStarH6Ordinal BStarClearanceOffset BStarBitParity BStarClearanceRaceMark BStarStageCandidateWrite
open BStarLongLiteral BStarLongPublication BStarLongLandingFrame BStarSealHealthyHop BStarAcquireAnchors
open BStarNeedServicePlan BStarNeedPrefix BStarNeedOneRead BStarNeedQuietRead BStarGrantWriterHistory
open BStarFirstDoorService

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step (n:=n) B
local notation "play" => BStarResetSchedule.run step

/-- Old-state observation predicate; no controller mode, future
continued execution or success is given in this raw premise. -/
def RawFirstRead (addr : Nat→Pos n) (g : Nat) (x : X) (e : Fin n) : Prop :=
  ∃ p : Payload, project addr x g=.forward p ∧
    p.fault=0 ∧ p.opcode.toNat=bitOp ∧ p.race=1 ∧ p.outcome=0 ∧ p.argument=0 ∧
    (e=incident (addr g).1 .left ∨ e=incident (addr g).1 .right)

def RawAtMostOne (addr : Nat→Pos n) (g : Nat) (x : X) (w : List (Fin n)) : Prop :=
  ∀ u e v u' e' v', w=u++e::v → w=u'++e'::v' → u.length<u'.length →
    RawFirstRead addr g (play x u) e → ¬RawFirstRead addr g (play x u') e'

theorem raw_read_is_owned {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (g : Nat) (G : g≤len) {m : Mode} (w : List (Fin n)) (e : Fin n)
    (T : GeneratedOwner hp base (fun j=>S.getD j fall) len x .idle w m)
    (raw : RawFirstRead (fun j=>S.getD j fall) g (play x w) e) :
    FirstRead hp base (fun j=>S.getD j fall) len g (play x w) e := by
  have now := BStarGeneratedTapeCuts.at_end hp T
  obtain ⟨p,W,F,OP,R,U,A,incidentMark⟩ := raw
  have correct := (healthy_forward_origin hp C sep T now g G p W bitOp F OP).1
  exact ⟨correct ▸ now,p,W,F,OP,R,U,A,incidentMark⟩

theorem prefix_keeps_one {base x : X} {addr : Nat→Pos n} {len g : Nat}
    {w full : List (Fin n)} (pre : w<+:full)
    (one : AtMostOne hp base addr len g x full) : AtMostOne hp base addr len g x w := by
  obtain ⟨tail,W⟩ := pre
  intro u e v u' e' v' L R middle oneRead twoRead
  have A : full=u++e::(v++tail) := by rw [←W,L,List.append_assoc,List.cons_append]
  have B' : full=u'++e'::(v'++tail) := by rw [←W,R,List.append_assoc,List.cons_append]
  exact one u e (v++tail) u' e' (v'++tail) A B' middle oneRead twoRead

/-- On an arbitrary finite raw prefix after a genuine accepted NEED
SEAL and before this center's first publication, there cannot be two
old-state fresh observations. There is no service-cover premise on
the input prefix: append the fixed cover only in the proof, then
project the prefix of the exact actual completing itinerary. -/
theorem unfinished_need_at_most_one {base origin : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall) (Q : X→Prop)
    (fiber : ∀ x,Q x→∀ i,Layout B base i=Layout B x i)
    (closed : ∀ x,Q x→∀ e,Q (step x e)) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (i : Fin n) (k : Nat) (K : k<len) (idx : S.getD k fall=(i,1)) (head : oldH6 B base i=true)
    (own : commandOwner (oldH6 B base) i 1=o.val)
    (bSite : Fin n) (g : Nat) (G : 0<g ∧ g<len)
    (gateIdx : S.getD g fall=(bSite,1)) (ord : oldOrdinal B base hh bSite=4)
    (lead : List (Fin n))
    (history : GeneratedOwner hp base (fun j=>S.getD j fall) len origin .idle lead (.busy sealOp (.out k)))
    (pay : Payload) (well : Well pay) (d : Descriptor) (need : d.need=true)
    (oldFacts : let x := play origin lead
      Q x ∧ correct (oldH6 B base) hh 5 x ∧ BStarLongGrant.conflict (BStarGrantReaderHistory.ports x i)=false ∧
      BStarLongPublication.decode (sourceDescriptor.read (x (S.getD 0 fall).1).long)=some d ∧
      BStarLongPublication.decode (BitVec.ofNat 7 (pay.argument.toNat/2))=some d ∧
      BStarLongOutgoing.actual (x i).long d=true ∧ readOptional (stage.read (x i).long)=some d ∧
      (centerLink (oldPair B x i),.advance pay)∈actualOffers (oldPair B x i)
        ((x i).long,(x (rightNeighbor i)).long))
    (P : Plan hp base (fun j=>S.getD j fall) len k g)
    (w : List (Fin n)) (noPub : BeforePublication hp (step (play origin lead) i) i w) :
    RawAtMostOne hp (fun j=>S.getD j fall) g (step (play origin lead) i) w := by
  let x0 := play origin lead
  let x := step x0 i
  let serviceLabels := service hp P i bSite
  have cover : serviceLabels.Sublist (w++serviceLabels) :=
    List.sublist_append_of_sublist_right (List.Sublist.refl _)
  obtain ⟨pre,tail,gate,s,W,_,_,_,Trace,pub,_⟩ := BStarNeedTailService.need_tail_publishes_trace
    hp C Q fiber closed sep i k K idx head own bSite g G gateIdx ord lead history
    pay well d need oldFacts P (w++serviceLabels) cover
  have stops : ¬NoPublication hp (play x pre) i i := by
    intro N
    exact N .left rfl ⟨.left,candidate d (firstBit s)⟩ (by rw [pub]; simp) rfl
  have proper := prefix_before_first_publish hp x i w serviceLabels pre tail W stops noPub
  obtain ⟨q0,off0,_,_,D,A,T,sel⟩ := oldFacts
  have qx : Q x := closed _ q0 i
  have ready : correct (oldH6 B base) hh 5 x :=
    BStarClearanceOffset.stable hp _ hh x0 i (sep i)
      (fun j=>(congrArg Prod.fst (fiber x0 q0 j)).symm)
      (BStarClearanceOffsetMask.leftFrame hp x0 i) off0
  have one := prefix_keeps_one hp proper
    (matched_at_most_one hp C Q fiber closed sep bSite g G.2 gateIdx ord qx ready k pre Trace)
  have cur := BStarGeneratedTapeCuts.at_end hp history
  obtain ⟨_,seedMark,seedCur,_,_,_⟩ :=
    BStarSealCenterAdvance.accepted_step hp C Q fiber closed sep q0 i k K idx head cur pay well d sel D A T
  have seedEvent : GeneratedOwner hp base (fun j=>S.getD j fall) len x0
      (.busy sealOp (.out k)) [i] (.busy sealOp (.out (k+1))) :=
    .next cur seedMark (.endpoint seedCur)
  have fullLead := generated_append hp history seedEvent
  have landed : play origin (lead++[i])=x := by rw [BStarResetSchedule.run_append]; rfl
  have each (u : List (Fin n)) (edge : Fin n)
      (R : RawFirstRead (fun j=>S.getD j fall) g (play x u) edge) :
      FirstRead hp base (fun j=>S.getD j fall) len g (play x u) edge := by
    obtain ⟨m,G',_,_⟩ := generated_word hp C Q fiber closed sep u (.busy sealOp (.out (k+1))) qx seedCur
    have Gfull := generated_append hp fullLead (landed.symm ▸ G')
    have aligned : play origin ((lead++[i])++u)=play x u := by
      rw [BStarResetSchedule.run_append,landed]
    exact aligned ▸ raw_read_is_owned hp C sep g (Nat.le_of_lt G.2) ((lead++[i])++u) edge Gfull
      (aligned.symm ▸ R)
  intro u e v u' e' v' L R order first second
  exact one u e v u' e' v' L R order (each u e first) (each u' e' second)

#print axioms raw_read_is_owned
#print axioms unfinished_need_at_most_one
end L4.BStarNeedPrefixFresh
