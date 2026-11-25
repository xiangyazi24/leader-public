import Leader.L4.BStarStageThroughCommit
import Leader.L4.BStarAcquireAckAncestry

namespace L4.BStarStageAckExtract
open AllSizeProtocol BStarTrace BStarLongWork BStarLongClaims
open BStarH6WordChart BStarAcquireVisitOrder BStarAcquireAnchors BStarAcquireLiteralChain
open BStarResetChartTouch BStarGeneratedOwner BStarLongFixedRouting BStarLongFiberOwner
open BStarLongCommand BStarLongDoor BStarClearanceSource BStarOwnerLaunchOrigin
open BStarGeneratedTapeCuts BStarCommitTailScan BStarCommitGeneratedTail
open BStarStageCandidateRetention BStarStagePast BStarSeparatingRail

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step B
local notation "run" => BStarResetSchedule.run step
local notation "pc" => BStarGeneratedBandScan.pc

private theorem foreign_pc (x : X) (i e : Fin n)
    (h : oldH6 B x i=true) (ne : rightNeighbor e≠i) :
    pc (step x e) i=pc x i := by
  by_cases E : i=e
  · subst i
    let pair := (x e,x (rightNeighbor e))
    have h' : (oldHeaders B pair.1).h6=true := h
    have t := BStarResetWaitRing.joined_left k₁ k₂ t₂ J₁ J₂ r c p c₁ hp pair h'
    unfold BStarGeneratedBandScan.pc
    simp only [AllSizeS1Geometry.step,if_true]
    exact congrArg (fun y : BitVec 2 × BitVec 9 => y.2.toNat) t
  · unfold BStarGeneratedBandScan.pc
    simp only [AllSizeS1Geometry.step,if_neg E,if_neg (Ne.symm ne)]

open BStarGeneratedPCAncestry BStarStageSourceFrame BStarResetControllerEntry

private theorem bad_issue_pc {x : X} {addr : Nat → Pos n} {e : Fin n}
    (h : oldH6 B x (addr 0).1=true)
    (sep : e≠rightNeighbor e) (I : BStarClearanceSource.Issue (x (addr 0).1).long)
    (E : e=RearTrace.predecessor (addr 0).1)
    (bad : initial (pc x (addr 0).1) (x (addr 0).1).long=none) :
    pc (step x e) (addr 0).1=0 := by
  have R : rightNeighbor e=(addr 0).1 := E ▸ RearTrace.right_predecessor _
  let pair := (x e,x (rightNeighbor e))
  have hdr : (oldHeaders B pair.2).h6=true := by change oldH6 B x (rightNeighbor e)=true; rwa [R]
  have valid : LongDoorGuard.valid manifest pair.2.long=true := by
    change LongDoorGuard.valid manifest (x (rightNeighbor e)).long=true
    rw [R]; exact I.1
  have phase : (ctrlPhase.read pair.2.long).toNat=1 := by
    change (ctrlPhase.read (x (rightNeighbor e)).long).toNat=1
    rw [R]; exact I.2
  have A := exact_issue_any_token k₁ k₂ t₂ J₁ J₂ r c p c₁ hp pair hdr valid phase
  have bad' : initial (ctrlOp.read pair.2.long).toNat pair.2.long=none := by
    change initial (pc x (rightNeighbor e)) (x (rightNeighbor e)).long=none
    rwa [R]
  rw [bad'] at A
  have eq : step x e (addr 0).1=(largePair B pair).2 := by
    rw [←R]; simp only [AllSizeS1Geometry.step,if_neg (Ne.symm sep),if_true,pair]
  exact congrArg (fun t : _ × BitVec 9 => t.2.toNat) (eq ▸ A)


open BStarLongToken BStarStageProvenance

/-- Exact decomposition of the generated physical PreBand at its
first exit from PC408. A foreign mark or a launch cannot be the
exit. The exit is a generated Stage ACK and has a literal healthy
Stage reply in the old source door. -/
theorem first_stage_ack {base x : X} {addr : Nat → Pos n} {len : Nat} {a d : Mode}
    {w : List (Fin n)} (T : GeneratedOwner hp base addr len x a w d)
    (K : (addr 0).2=0) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (band : PreBand hp x (addr 0).1 w)
    (first : pc x (addr 0).1=408) (endPC : 409≤pc (run x w) (addr 0).1) :
    ∃ lead e post, w=lead++e::post ∧
      GeneratedOwner hp base addr len x a lead (.busy stageOp (.back 0)) ∧
      let old := run x lead
      let new := step old e
      pc old (addr 0).1=408 ∧ pc new (addr 0).1=409 ∧
      Event hp addr len old e (.busy stageOp (.back 0)) .idle ∧
      (∃ f, bind (longGeometry B (old (addr 0).1)) 0 (atSite (old (addr 0).1).long 0)=.reply f ∧ Stage f) ∧
      GeneratedOwner hp base addr len new .idle post d := by
  induction T with
  | endpoint I =>
    simp only [BStarResetSchedule.run] at endPC
    rw [first] at endPC
    exact (by decide : ¬ (409:Nat)≤408) endPC |>.elim
  | @next x a e w b d I E T ih =>
    have header := (band [] (e::w) rfl).1
    have band' : PreBand hp (step x e) (addr 0).1 w := by
      intro u v W
      exact band (e::u) v (congrArg (List.cons e) W)
    by_cases same : pc (step x e) (addr 0).1=408
    · obtain ⟨p,m,t,W,G,old,new,evt,F,rest⟩ := ih band' same endPC
      exact ⟨e::p,m,t,congrArg (List.cons e) W,.next I E G,old,new,evt,F,rest⟩
    have lo : 408≤pc (step x e) (addr 0).1 := (band' [] w rfl).2.1
    have hi : pc (step x e) (addr 0).1≤410 := (band' [] w rfl).2.2
    have endCase : pc (step x e) (addr 0).1=409 ∨ pc (step x e) (addr 0).1=410 := by omega
    have away (Q : e≠RearTrace.predecessor (addr 0).1) : False := by
      have F : rightNeighbor e≠(addr 0).1 := fun Z =>
        Q ((RearTrace.predecessor_right e).symm.trans (congrArg RearTrace.predecessor Z))
      exact same ((foreign_pc hp x (addr 0).1 e header F).trans first)
    cases E with
    | idle_hold ne => exact (away ne).elim
    | bad_issue own bad =>
      have D := bad_issue_pc hp header (sep e) I.1 own bad
      exact ((by decide : ¬ (408:Nat)≤0) (D ▸ lo)).elim
    | launch _ L =>
      have D : pc (step x e) (addr 0).1=pc x (addr 0).1 :=
        congrArg (fun t : _ × BitVec 9 => t.2.toNat) L.2.choose_spec.2
      exact (same (D.trans first)).elim
    | transit op z v live seen =>
      have new := at_start hp T
      have D : pc (step x e) (addr 0).1=pc x (addr 0).1 := new.1.2.2.2.trans I.1.2.2.2.symm
      exact (same (D.trans first)).elim
    | arrived_hold _ ne => exact (away ne).elim
    | consume op own empty =>
      have oldPC : op=408 := I.1.2.2.2.symm.trans first
      subst op
      have ev := Event.consume stageOp own empty
      obtain ⟨_,f,F,H,O,_,_,contra,_⟩ :=
        consume_tail hp K header (sep e) I ev (endCase.imp id Or.inl)
      have C : pc (step x e) (addr 0).1=409 :=
        endCase.resolve_right (fun D => (by decide : (408:Nat)≠409) (contra D))
      exact ⟨[],e,w,rfl,.endpoint I,first,C,ev,⟨f,F,H,O⟩,T⟩

/-- The first Stage ACK in the exact band comes from a Stage issue and
a completed outward/return tour on that same marked word. This is the
chronology needed to find the physical K1 departures; it does not yet
infer back-propagation of a healthy reply to every outgoing packet. -/
theorem stage_tour {base x : X} {addr : Nat → Pos n} {len : Nat} {d : Mode}
    {w : List (Fin n)} (T : GeneratedOwner hp base addr len x .idle w d)
    (K : (addr 0).2=0) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (band : PreBand hp x (addr 0).1 w)
    (first : pc x (addr 0).1=408) (endPC : 409≤pc (run x w) (addr 0).1) :
    ∃ lead turn back ack post f, w=lead++turn::(back++ack::post) ∧
      Found hp base addr len stageOp x lead (.out len) ∧
      let atTurn := run x lead
      let atAck := run (step atTurn turn) back
      Event hp addr len atTurn turn (.busy stageOp (.out len)) (.busy stageOp (.back len)) ∧
      BusyOnly hp base addr len stageOp (step atTurn turn) (.back len) back (.back 0) ∧
      Event hp addr len atAck ack (.busy stageOp (.back 0)) .idle ∧
      bind (longGeometry B (atAck (addr 0).1)) 0 (atSite (atAck (addr 0).1).long 0)=.reply f ∧
      Stage f ∧ pc (step atAck ack) (addr 0).1=409 ∧
      GeneratedOwner hp base addr len (step atAck ack) .idle post d ∧
      PreBand hp (step atAck ack) (addr 0).1 post := by
  obtain ⟨tape,ack,post,U,G,_,PC,E,⟨f,R,H⟩,T'⟩ := first_stage_ack hp T K sep band first endPC
  obtain ⟨lead,turn,back,V,found,event,ret⟩ :=
    BStarAcquireAckAncestry.found_split_turn hp (from_idle hp G)
  have split : w=lead++turn::(back++ack::post) := by
    rw [U,V,List.append_assoc,List.cons_append]
  have runEq : run x tape=run (step (run x lead) turn) back := by
    rw [V,BStarResetSchedule.run_append]; rfl
  rw [runEq] at PC E R T'
  refine ⟨lead,turn,back,ack,post,f,split,found,event,ret,E,R,H,PC,T',?_⟩
  intro u v W
  have B0 : w=(tape++ack::u)++v := by rw [U,W,List.append_assoc,List.cons_append]
  have out := band (tape++ack::u) v B0
  rw [BStarResetSchedule.run_append,runEq] at out
  exact out

#print axioms stage_tour
#print axioms first_stage_ack
end L4.BStarStageAckExtract
