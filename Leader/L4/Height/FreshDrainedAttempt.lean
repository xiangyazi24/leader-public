import Leader.L4.Height.FreshFenceSeed
import Leader.L4.Height.FreshFenceSplice
import Leader.L4.Height.FreshStoppedFence
import Leader.L4.Height.FreshOrderedAttempt
import Leader.L4.Height.FreshNumericEntry
import Leader.L4.BStarNeedPrefix

namespace L4.Height.FreshDrainedAttempt
open AllSizeProtocol PhysicalCustody ProductionCustody ProductionCycles FreshFirstAcquire
open BStarLongWork BStarTrace BStarLongClaims BStarLongPackets BStarFreshNumeric BStarFreshNumericOperands
open BStarAcquireAnchors BStarH6WordChart BStarResetChartTouch BStarGeneratedOwner BStarCopyFenceCuts
open BStarAcquireLiteralChain BStarAcquireVisitOrder BStarSteeredLikelihood BStarOwnerLaunchOrigin

variable {s n : Nat} {x : Raw s n} {g : CustodyWitness x}
local notation "hp" => (show 0<2 by decide)
local notation "h" => oldH6 (rows s) g.base

private theorem run_join (z : Raw s n) (u v : Word n) : rawRun z (u++v)=rawRun (rawRun z u) v :=
  BStarResetSchedule.run_append (rawNext s) z u v

private theorem live_across {o : Owners h} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp g.base g.hh o S len fall) (y : Raw s n) (u v : Word n) (e : Fin n)
    (early : LiveAt hp C y u) (late : LiveAt hp C (rawNext s (rawRun y u) e) v) :
    LiveAt hp C y (u++e::v) := by
  intro a b eq
  rcases List.append_eq_append_iff.mp eq with ⟨t,A,V⟩|⟨t,A,_⟩
  · cases t with
    | nil => rw [A,List.append_nil]; exact early u [] (List.append_nil _).symm
    | cons f t =>
      obtain ⟨rfl,K⟩ := List.cons.inj V
      rw [A,BStarResetSchedule.run_append]
      exact late t b K
  · exact early a t A

/-- A real ISSUE6 and observed INJECT return lead to a drained and
tagged ISSUE12 on that same suffix when the target later reaches RESET2. -/
theorem after_inject (P : Production g) {o : Owners h} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp g.base g.hh o S len fall) (y : Raw s n) (qy : g.Q y)
    (front back later : Word n) (turn ack : Fin n) :
    let slot := fun j=>S.getD j fall
    let root := (slot 0).1
    let f := rawRun y front
    let old := rawRun (rawNext s f turn) back
    let z := rawNext s old ack
    GeneratedOwner hp g.base slot len y .idle front (.busy 10 (.out len)) →
    PC y root=6 → LiveAt hp C y (front++turn::back) →
    BStarNativeReceiptTape.Hit hp g.base slot len old ack 10 →
    Current hp g.base slot len z .idle → PC (rawRun z later) root=2 →
    ∃ cut rest,later=cut++rest ∧
      let fin := rawRun z cut
      Current hp g.base slot len fin .idle ∧ PC fin root=12 ∧
      (∀ i sh,ActiveOwner hp g.base o.val i sh → (readLane (Sheet.index sh) (fin i).long).mobile=.empty) ∧
      (∀ k≤len,(slot k).2.val=1 → (longGeometry (rows s) (g.base (slot k).1)).inside=true →
        operands (fin (slot k).1).long) := by
  dsimp only
  let slot := fun j=>S.getD j fall
  let root := (slot 0).1
  let f := rawRun y front
  let old := rawRun (rawNext s f turn) back
  let z := rawNext s old ack
  intro G pc live H idle reset
  have qf := keep g y front qy
  have qz := g.closed _ ack (keep g _ back (g.closed _ turn qf))
  obtain ⟨pre,t,ret,e,post,W,F,M,R,A,after,bands⟩ :=
    FreshStoppedFence.first_fence_return P C z qz later idle H.2.2.2.1 reset
  let mid := turn::(back++ack::pre)
  have same : rawRun f mid=rawRun z pre := run_join (rawNext s f turn) back (ack::pre)
  obtain ⟨m,T,_,last⟩ := generated_word hp C g.Q g.fiber (fun p ok j=>g.closed p j ok)
    (separation P) mid _ qf (BStarGeneratedTapeCuts.at_end hp G)
  have atEnd : Current hp g.base slot len (rawRun z pre) (.busy 11 (.out len)) := BStarGeneratedTapeCuts.at_end hp F
  have mode := current_mode_unique hp _ _ last (same.symm ▸ atEnd)
  subst m
  have oldEq : rawRun y (front++turn::back)=old := run_join y front (turn::back)
  have scopedBands := live_across C y (front++turn::back) (pre++t::ret) ack live (oldEq.symm ▸ bands)
  have full : LiveAt hp C y (front++(mid++t::ret)) := by
    simpa only [mid,List.append_assoc,List.cons_append] using scopedBands
  obtain ⟨ls,a,rs,top,L,join,low,flags,strip,D,head,own,size,coverL,coverR⟩ :=
    FreshStripGeometry.strips_cover P C
  obtain ⟨lead,door,tour,_,receipt,imgL,imgR,drainL,drainR⟩ :=
    FreshFenceSplice.fence_from_issue hp C (separation P) ls rs top (radius_pos P)
      root (slot len).1 a rfl rfl join head L low flags D strip own size coverL coverR
      g.flags g.notShort front mid ret t e G T (same.symm ▸ M) (same.symm ▸ R) (same.symm ▸ A) full pc
  change BStarResetSchedule.run (AllSizeS1Geometry.step (rows s)) (BStarResetSchedule.run (AllSizeS1Geometry.step (rows s)) y front) mid=rawRun z pre at same
  unfold PhysicalCustody.rows at same
  rw [same] at receipt imgL imgR drainL drainR
  rw [join] at imgL
  have seeds := FreshFenceSeed.from_images P C _ ls rs top a _ _ L join D strip head size
    drainL drainR imgL imgR
  let cut := pre++t::(ret++[e])
  have finalEq : rawRun z cut=rawNext s (rawRun (rawNext s (rawRun z pre) t) ret) e := by
    rw [show cut=pre++t::(ret++[e]) from rfl,run_join]
    exact run_join (rawNext s (rawRun z pre) t) ret [e]
  refine ⟨cut,post,by simp only [cut,W,List.append_assoc,List.cons_append,List.nil_append],?_⟩
  rw [finalEq]
  exact ⟨after,receipt.2.2.2.1,seeds⟩

/-- On the actual stopped policy word, a further target RREL after the
five release cuts forces idle ISSUE408 if no strict publication was recorded. -/
theorem stage_on_stopped_history (P : Production g) (i : Header h) (base w : Word n)
    (z : History s n) (actual : Consistent x (policy g i) i.val z)
    (cuts : Releases g (ProductionClients.serviceOwner g i) 5 base) (nextR : Fin n)
    (last : accepted g (ProductionClients.serviceOwner g i) (base++w) nextR)
    (suffix : z.emitted=(base++w)++[nextR]) (miss : ¬z.published) :
    let target := ProductionClients.serviceOwner g i
    ∃ S len fall, Chart hp g.base g.hh target S len fall ∧
      ∃ pre post,w=pre++post ∧
        GeneratedOwner hp g.base (fun k=>S.getD k fall) len (rawRun x base) .idle pre .idle ∧
        PC (rawRun x (base++pre)) (S.getD 0 fall).1=408 := by
  dsimp only
  let target := ProductionClients.serviceOwner g i
  obtain ⟨u,acq,lead,door,out,t,tail,S,len,fall,W,C,released,issue,G,_turn,_live,_unit,
    ⟨back,ack,later,H,_,hit,after,scope⟩,_⟩ :=
    FreshOrderedAttempt.on_stopped_history g P i base w z actual cuts nextR last suffix miss
  let slot := fun k=>S.getD k fall
  let root := (slot 0).1
  let front := lead++door::out
  let y := rawNext s (rawRun x (base++u)) acq
  let old := rawRun (rawNext s (rawRun y front) t) back
  let zAfter := rawNext s old ack
  let priorTape := u++acq::(front++t::(back++[ack]))
  have splitW : w=priorTape++later := by simp only [W,H,priorTape,front,List.append_assoc,List.cons_append,
    List.nil_append]
  have replay : rawRun (rawRun x base) priorTape=zAfter := by
    dsimp only [priorTape,zAfter,old,y]
    rw [run_join (rawRun x base) u,run_join x base u]
    change rawRun (rawNext s (rawRun (rawRun x base) u) acq) (front++t::(back++[ack]))=_
    rw [run_join]
    exact run_join _ back [ack]
  have rootID : root=(endpoint h g.hh target 0).1 := congrArg Prod.fst C.root
  have endPC : PC (rawRun zAfter later) root=2 := by
    rw [←replay,←run_join,←splitW,←run_join,rootID]
    exact last.2.1
  have qy : g.Q y := g.closed _ acq (ready_run P (base++u)).1
  obtain ⟨cut,rest,sub,atFence,pcFence,drained,retained⟩ :=
    after_inject P C y qy front back later t ack G issue scope hit after endPC
  let upto := priorTape++cut
  have total : w=upto++rest := by simp only [splitW,sub,upto,List.append_assoc]
  obtain ⟨a,rrel,baseEq,paid⟩ := FreshConflicts.target_release g target cuts
  let start := rawNext s (rawRun x a) rrel
  have init : rawRun x base=start := by rw [baseEq]; exact run_join x a [rrel]
  have cutEq : rawRun start upto=rawRun zAfter cut := by rw [←init,run_join,replay]
  have initialQ := g.closed _ rrel (ready_run P a).1
  obtain ⟨m,tour,_,cur⟩ := generated_word hp C g.Q g.fiber (fun p ok j=>g.closed p j ok)
    (separation P) upto .idle initialQ (init ▸ released)
  have idMode := current_mode_unique hp _ _ cur (cutEq.symm ▸ atFence)
  subst m
  have stop : PC (rawRun (rawRun start upto) rest) root=2 := by
    rw [cutEq,←run_join,←sub]; exact endPC
  obtain ⟨pre,post,V,T,stage⟩ := FreshNumericEntry.stage_after_fence g P target a rrel paid C upto rest
    tour (cutEq.symm ▸ pcFence) stop (cutEq.symm ▸ drained) (cutEq.symm ▸ retained)
  refine ⟨S,len,fall,C,upto++pre,post,by simp only [total,V,List.append_assoc],?_,?_⟩
  · rw [init]
    exact BStarNeedPrefix.generated_append hp tour T
  · rw [run_join x base,init,run_join]; exact stage

end L4.Height.FreshDrainedAttempt
