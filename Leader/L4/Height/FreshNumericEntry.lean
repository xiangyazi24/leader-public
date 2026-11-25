import Leader.L4.Height.FreshNumericStop
import Leader.L4.Height.FreshAdmissionStart
import Leader.L4.BStarFreshSetup12Flight
import Leader.L4.BStarFreshNumericOperandSeed

namespace L4.Height.FreshNumericEntry
open AllSizeProtocol PhysicalCustody ProductionCustody ProductionCycles FreshFirstAcquire
open BStarH6WordChart BStarAcquireVisitOrder BStarAcquireLiteralChain BStarResetChartTouch
open BStarGeneratedOwner BStarSteeredLikelihood BStarFreshNumericOperands
open BStarOwnerLaunchOrigin BStarTrace BStarFreshNumeric BStarLongClaims BStarLongPackets

variable {s n : Nat} {x : Raw s n} (g : CustodyWitness x)
local notation "hp" => (show 0<2 by decide)
local notation "h" => oldH6 (rows s) g.base

/-- Following the drained FENCE receipt through the real initializing
command preserves both operands. Any later RESET2 must pass idle ISSUE408.
The only data hypotheses are at ISSUE12, before the native program. -/
theorem stage_after_fence (P : Production g) (o : Owners h) (a : Word n) (rrel : Fin n)
    (paid : accepted g o a rrel) {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp g.base g.hh o S len fall) (lead w : Word n) :
    let z := rawNext s (rawRun x a) rrel
    let slot := fun j=>S.getD j fall
    let root := (slot 0).1
    let y := rawRun z lead
    GeneratedOwner hp g.base slot len z .idle lead .idle →
    PC y root=12 → PC (rawRun y w) root=2 →
    (∀ i sh,ActiveOwner hp g.base o.val i sh →
      (readLane (Sheet.index sh) (y i).long).mobile=.empty) →
    (∀ k≤len,(slot k).2.val=1 → (longGeometry (rows s) (g.base (slot k).1)).inside=true →
      operands (y (slot k).1).long) →
    ∃ pre post,w=pre++post ∧ GeneratedOwner hp g.base slot len y .idle pre .idle ∧
      PC (rawRun y pre) root=408 := by
  dsimp only
  let z := rawNext s (rawRun x a) rrel
  let slot := fun j=>S.getD j fall
  let root := (slot 0).1
  let y := rawRun z lead
  intro history atStart atEnd drained retained
  have q := g.closed _ rrel (ready_run P a).1
  have qy := keep g z lead q
  obtain ⟨u,e,v,W,old,new,previous⟩ := first_outside (·=12) y root w atStart
    (by rw [show PC (rawRun y w) root=2 from atEnd]; decide)
  obtain ⟨G,M,after⟩ := FreshAdmissionStart.return_state_of_change g P C qy
    (BStarGeneratedTapeCuts.at_end hp history) u e 12
    (fun bad=>by have impossible : (some 0 : Option Nat)=none := bad; cases impossible) old new
  obtain ⟨before,flight,launch,U,own,offer,op,route⟩ := from_idle hp G
  have receiptEq : rawRun y u=rawRun (rawRun y before) (launch::flight) := by
    rw [U]; exact BStarResetSchedule.run_append (rawNext s) y before (launch::flight)
  have initReceipt := BStarFreshSetup12Flight.actual_to_13 hp C (separation P) launch e flight op
    (.launch own offer) route (receiptEq ▸ M)
  change PC (rawNext s (rawRun (rawRun y before) (launch::flight)) e) root=13 at initReceipt
  rw [←receiptEq] at initReceipt
  let cut := u++[e]
  have tape : w=cut++v := by simp only [W,cut,List.append_assoc,List.singleton_append]
  have same : rawRun y cut=rawNext s (rawRun y u) e :=
    BStarResetSchedule.run_append (rawNext s) y u [e]
  have idle : Current hp g.base slot len (rawRun y cut) .idle := same.symm ▸ after
  have mark : GeneratedOwner hp g.base slot len (rawRun y u) (.busy 12 (.back 0)) [e] .idle :=
    .next (BStarGeneratedTapeCuts.at_end hp G) M (.endpoint after)
  have initTour := FreshGeneratedGlue.generated_append hp G mark
  have joined := FreshGeneratedGlue.generated_append hp history initTour
  have frame := BStarFreshNumericOperandPrefix.prefix_frame hp C (separation P) lead cut .idle joined
    (fun t f b eq=>⟨g.fiber _ (keep g y t qy),Nat.le_of_lt
      (show 11<PC (rawRun y t) root by rw [show PC (rawRun y t) root=12 from previous t f b eq]; decide)⟩) drained
  let seed := rawRun z (lead++cut)
  have replay : seed=rawRun y cut := BStarResetSchedule.run_append (rawNext s) z lead cut
  have qSeed := keep g z (lead++cut) q
  obtain ⟨last,T,_,_⟩ := generated_word hp C g.Q g.fiber (fun p ok j=>g.closed p j ok)
    (separation P) v .idle qSeed (replay.symm ▸ idle)
  have atThirteen : PC seed root=13 := by rw [replay,same]; exact initReceipt
  have join (a b : Word n) : rawRun y (a++b)=rawRun (rawRun y a) b :=
    BStarResetSchedule.run_append (rawNext s) y a b
  have atReset : PC (rawRun seed v) root=2 := by
    rw [replay,←join cut v,←tape]
    exact atEnd
  have sameLane (i sh) (own : ActiveOwner hp g.base o.val i sh) :
      readLane (Sheet.index sh) (seed i).long=readLane (Sheet.index sh) (y i).long := by
    rw [replay]
    exact frame i sh own
  obtain ⟨pre,post,V,subword,stage⟩ := FreshNumericStop.issue_before_reset P o a rrel paid C
    (lead++cut) v last joined T atThirteen atReset
    (fun i sh own=>by rw [sameLane i sh own]; exact drained i sh own)
    (by
      intro k hk one ins
      obtain ⟨L,R⟩ := operand_owner hp C hk one ins
      obtain ⟨⟨l,hl⟩,r,hr⟩ := retained k hk one ins
      exact ⟨⟨l,(congrArg Lane.retained (sameLane _ .ld L)).trans hl⟩,
        r,(congrArg Lane.retained (sameLane _ .rd R)).trans hr⟩)
  have late : GeneratedOwner hp g.base slot len (rawRun y cut) .idle pre .idle := replay ▸ subword
  have split : w=(cut++pre)++post :=
    tape.trans ((congrArg (fun l=>cut++l) V).trans (List.append_assoc ..).symm)
  refine ⟨cut++pre,post,split,FreshGeneratedGlue.generated_append hp initTour late,?_⟩
  change PC (rawRun y (cut++pre)) root=408
  rw [join cut pre,←replay]
  exact stage

end L4.Height.FreshNumericEntry
