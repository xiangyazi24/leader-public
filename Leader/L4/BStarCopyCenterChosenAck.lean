import Leader.L4.BStarCanonicalAttemptBank

namespace L4.BStarCopyCenterChosenAck
open AllSizeProtocol BStarTrace BStarLongWork BStarLongClaims BStarLongTransport
open BStarH6WordChart BStarAcquireVisitOrder BStarAcquireAnchors BStarAcquireLiteralChain
open BStarLongFiberOwner BStarLongFixedRouting BStarResetChartTouch
open BStarGeneratedOwner BStarGeneratedTapeCuts BStarLongDoor BStarLongCommand
open BStarClearanceSource BStarOwnerLaunchOrigin BStarSeparatingRail BStarLongLayout
open BStarAcquireAckWindow BStarGrantBirth BStarGrantWriterHistory
open BStarOwnedGrantLife BStarAttemptSafety BStarPostCutAttempt BStarLongGrant
open BStarAcquireLatch BStarAcquireReadout BStarWriterTransferWindow BStarCommitTailScan
open BStarCommitOperands
set_option maxRecDepth 4096
variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step B
local notation "run" => BStarResetSchedule.run step
local notation "pc" => BStarGeneratedBandScan.pc

theorem selected_center_from_ack {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall) (Q : X → Prop) (I : Q x)
    (fiber : ∀ y,Q y → ∀ i,Layout B base i=Layout B y i)
    (closed : ∀ y e,Q y → Q (step y e)) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (w flight : List (Fin n)) (door center : Fin n) (k : Nat) (K : k≤len)
    (loc : S.getD k fall=(center,1))
    (centerHead : oldH6 B base center=true)
    (centerOwner : commandOwner (oldH6 B base) center 1=o.val)
    (G : GeneratedOwner hp base (fun j=>S.getD j fall) len x .idle w .idle)
    (lead tail : List (Fin n)) (ack : Fin n)
    (W : w=lead++ack::tail)
    (AG : GeneratedOwner hp base (fun j=>S.getD j fall) len x .idle lead (.busy acquire (.back 0)))
    (AE : Event hp (fun j=>S.getD j fall) len (run x lead) ack (.busy acquire (.back 0)) .idle)
    (A6 : pc (step (run x lead) ack) (S.getD 0 fall).1=6)
    (P : PreIssue hp (S.getD 0 fall).1 (step (run x lead) ack) tail)
    (launch : Launch (run x w (S.getD 0 fall).1).long (step (run x w) door (S.getD 0 fall).1).long)
    (op : pc (run x w) (S.getD 0 fall).1=411)
    (F : BusyOnly hp base (fun j=>S.getD j fall) len commitOp (step (run x w) door) (.out 0) flight (.out k)) :
    let header := (endpoint (oldH6 B base) hh o 1).1
    ∃ A : Acquisition hp x [] w header 1,
      (∃ b,lead=A.lead++A.mark::b) ∧
      ((capturedSelector 1).read (step (run x lead) ack (S.getD 0 fall).1).long).toNat =
        (BStarLongPublication.readSel (run x A.lead header).long).val := by
  let header := (endpoint (oldH6 B base) hh o 1).1
  have centerEq : center=header :=
    congrArg Prod.fst ((endpoint_spec (oldH6 B base) hh o 1).2.2 center centerHead centerOwner)
  have all := BStarCanonicalAttemptBank.wins_from_chosen_ack hp C Q I fiber closed sep w flight
    door center k K loc centerOwner G lead tail ack W AG AE A6 P launch op F
  obtain ⟨pre,post,suffix,birth,i,v,Ack,Cut,owned,head,won,life,_,sel,_,fields,prior⟩ := all (1 : Fin 3)
  have siteEq : i=header :=
    congrArg Prod.fst ((endpoint_spec (oldH6 B base) hh o 1).2.2 i head owned)
  subst i
  rw [centerEq] at prior
  let throughAck := post++ack::tail
  have short : w=pre++birth::throughAck := by
    rw [W,Ack]
    simp only [throughAck,List.append_assoc,List.cons_append]
  have extend : suffix=throughAck++door::flight := by
    have eq : pre++birth::suffix=pre++birth::(throughAck++door::flight) := by
      rw [←Cut,short,List.append_assoc,List.cons_append]
    exact (List.cons.inj (List.append_cancel_left eq)).2
  have shortLife : Continuous hp (step (run x pre) birth) header 1 throughAck := by
    intro a b E
    exact life a (b++door::flight) (by rw [extend,E,List.append_assoc])
  have shortPrior : BeforePublication hp (step (run x pre) birth) header throughAck := by
    intro a e b E
    exact prior a e (b++door::flight) (by rw [extend,E,List.append_assoc,List.cons_append])
  let A := Acquisition.writer hp x [] w header pre birth throughAck short (Nat.zero_le _) won shortLife shortPrior
  have cap := (congrArg Prod.fst fields).trans (congrArg Fin.val sel)
  exact ⟨A,⟨post,Ack⟩,cap⟩

end L4.BStarCopyCenterChosenAck
