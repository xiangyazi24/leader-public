import Leader.L4.Height.FreshFirstAcquire
import Leader.L4.Height.FreshCaptureSelectors
import Leader.L4.BStarNumericDrainedBand
import Leader.L4.Height.FreshGeneratedGlue

namespace L4.Height.FreshNumericStop
open AllSizeProtocol PhysicalCustody ProductionCustody ProductionCycles FreshFirstAcquire
open BStarH6WordChart BStarAcquireVisitOrder BStarAcquireLiteralChain BStarResetChartTouch
open BStarGeneratedOwner BStarGeneratedBandScan BStarSteeredLikelihood BStarFreshNumericOperands
open BStarTrace BStarFreshNumeric BStarResetChartService BStarFreshNumericOperandPrefix
open BStarForwardNumericBand BStarLongClaims BStarLongPackets BStarLongLayout

variable {s n : Nat} {x : Raw s n} {g : CustodyWitness x}
local notation "hp" => (show 0<2 by decide)
local notation "h" => oldH6 (rows s) g.base

/-- From a real released target and drained ISSUE13 with both retained tags,
every finite continuation that reaches the next RREL must first enter idle
ISSUE408. Later selector legality and tag health are derived on that tape. -/
theorem issue_before_reset (P : Production g) (o : Owners h) (a : Word n) (rrel : Fin n)
    (paid : accepted g o a rrel) {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp g.base g.hh o S len fall) (lead w : Word n) (b : Mode) :
    let z := rawNext s (rawRun x a) rrel
    let addr := fun j=>S.getD j fall
    let root := (addr 0).1
    let y := rawRun z lead
    GeneratedOwner hp g.base addr len z .idle lead .idle →
    GeneratedOwner hp g.base addr len y .idle w b →
    PC y root=13 → PC (rawRun y w) root=2 →
    (∀ i sh,ActiveOwner hp g.base o.val i sh →
      (readLane (Sheet.index sh) (y i).long).mobile=.empty) →
    (∀ k≤len,(addr k).2.val=1 → (longGeometry (rows s) (g.base (addr k).1)).inside=true →
      operands (y (addr k).1).long) →
    ∃ pre post,w=pre++post ∧ GeneratedOwner hp g.base addr len y .idle pre .idle ∧
      PC (rawRun y pre) root=408 := by
  dsimp only
  let z := rawNext s (rawRun x a) rrel
  let addr := fun j=>S.getD j fall
  let root := (addr 0).1
  let y := rawRun z lead
  intro seed tour atStart atEnd drained retained
  let within := fun k : Nat=>13≤k ∧ k<408
  obtain ⟨u,e,v,W,_,exit,previous⟩ := first_outside within y root w
    (by rw [show PC y root=13 from atStart]; decide)
    (by rw [show PC (rawRun y w) root=2 from atEnd]; decide)
  let short := u++[e]
  have decomp : w=short++v := by simp only [short,W,List.append_assoc,List.singleton_append]
  obtain ⟨last,priorTape,_⟩ := BStarGeneratedTapeCuts.split hp short v (decomp ▸ tour)
  have joined := FreshGeneratedGlue.generated_append hp seed priorTape
  have q := g.closed _ rrel (ready_run P a).1
  have source : root=(endpoint h g.hh o 0).1 := congrArg Prod.fst C.root
  have initial : Live addr y .idle :=
    ⟨(by change 13≤PC y root ∧ PC y root<408; rw [show PC y root=13 from atStart]; decide),
      fun _ _ impossible=>by cases impossible⟩
  obtain ⟨pre,post,m,E,history,_,_,stop⟩ := stopped_word hp C (separation P) priorTape initial (by
    intro cut f t tape earlier
    have bounds := previous cut f t tape
    have runEq : rawRun z (lead++cut)=rawRun y cut :=
      BStarResetSchedule.run_append (rawNext s) z lead cut
    have good : Band (rawRun z (lead++cut)) (endpoint h g.hh o 0).1 := by
      rw [←source,runEq]
      change 6≤PC (rawRun y cut) root ∧ PC (rawRun y cut) root≤408
      change 13≤PC (rawRun y cut) root ∧ PC (rawRun y cut) root<408 at bounds
      omega
    have center := (FreshCaptureSelectors.legal_on_band P o a rrel paid (lead++cut) good).1 1
    rw [←source,runEq] at center
    have lay := g.fiber _ (keep g y cut (keep g z lead q))
    refine ⟨(root_header hp C lay).1,center,?_⟩
    intro k hk one inside
    let i := (addr k).1
    have ins : (longGeometry (rows s) (g.base i)).inside=true :=
      (congrArg (fun u : Bool × Bool × Bool=>u.2.1) (lay i)).trans inside
    obtain ⟨L,R⟩ := operand_owner hp C hk one ins
    have splitAt : lead++short=(lead++cut)++(f::t) := by rw [tape,List.append_assoc]
    obtain ⟨mode,G,_⟩ := BStarGeneratedTapeCuts.split hp (lead++cut) (f::t) (splitAt ▸ joined)
    have frame := prefix_frame hp C (separation P) lead cut mode G
      (fun q' f' t' M=>⟨g.fiber _ (keep g y q' (keep g z lead q)),earlier q' f' t' M⟩) drained
    obtain ⟨⟨l,hl⟩,d,hd⟩ := retained k hk one ins
    exact ⟨⟨l,(congrArg Lane.retained (frame i .ld L)).trans hl⟩,
      d,(congrArg Lane.retained (frame i .rd R)).trans hd⟩)
  rcases stop with ⟨mode,pc⟩|⟨rfl,live⟩
  · subst m
    exact ⟨pre,post++v,by rw [decomp,E,List.append_assoc],history,pc⟩
  · have same : short=pre := by simpa using E
    have state : rawRun y pre=rawNext s (rawRun y u) e := by
      rw [←same]
      exact BStarResetSchedule.run_append (rawNext s) y u [e]
    exact (exit (state ▸ live.1)).elim

#print axioms issue_before_reset
end L4.Height.FreshNumericStop
