import Leader.L4.Height.FreshSetupProgress
import Leader.L4.Height.GateResidence
import Leader.L4.BStarCopyFenceCuts

namespace L4.Height.FreshInjectEntry
open AllSizeProtocol PhysicalCustody ProductionCustody ProductionCycles FreshFirstAcquire
open BStarLongDoor BStarH6WordChart BStarResetChartTouch BStarGeneratedOwner
open BStarAcquireLiteralChain BStarAcquireVisitOrder BStarSteeredLikelihood BStarOwnerLaunchOrigin

variable {s n : Nat} {x : Raw s n} {g : CustodyWitness x}
local notation "hp" => (show 0<2 by decide)
local notation "h" => oldH6 (rows s) g.base

/-- Between an actual ISSUE6 and a later RREL, the literal word has a cut at
the end of outward INJECT. Every earlier state stays in the active band,
including the old terminal. These are the trace inputs for ordered_from_issue. -/
theorem front_before_reset (P : Production g) (o : Owners h) (a : Word n) (rrel : Fin n)
    (paid : accepted g o a rrel) {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp g.base g.hh o S len fall) (lead w : Word n) :
    let z := rawNext s (rawRun x a) rrel
    let slot := fun j=>S.getD j fall
    let root := (slot 0).1
    let y := rawRun z lead
    Current hp g.base slot len z .idle → Current hp g.base slot len y .idle →
    PC y root=6 → PC (rawRun y w) root=2 →
    ∃ front turn tail,w=front++turn::tail ∧
      GeneratedOwner hp g.base slot len y .idle front (.busy 10 (.out len)) ∧
      Event hp slot len (rawRun y front) turn (.busy 10 (.out len)) (.busy 10 (.back len)) ∧
      BStarCopyFenceCuts.LiveAt hp C y front ∧
      ∃ back ack rest,tail=back++ack::rest ∧
        BusyOnly hp g.base slot len 10 (rawNext s (rawRun y front) turn) (.back len) back (.back 0) ∧
        Event hp slot len (rawRun (rawNext s (rawRun y front) turn) back) ack
          (.busy 10 (.back 0)) .idle ∧
        Current hp g.base slot len (rawNext s (rawRun (rawNext s (rawRun y front) turn) back) ack) .idle ∧
        BStarCopyFenceCuts.LiveAt hp C y (front++turn::back) := by
  dsimp only
  let z := rawNext s (rawRun x a) rrel
  let slot := fun j=>S.getD j fall
  let root := (slot 0).1
  let y := rawRun z lead
  intro released idle issue reset
  have q := g.closed _ rrel (ready_run P a).1
  have qy := keep g z lead q
  let within := fun k : Nat=>6≤k ∧ k≤10
  obtain ⟨u,e,v,W,old,exit,previous⟩ := first_outside within y root w
    (by rw [show PC y root=6 from issue]; decide) (by rw [show PC (rawRun y w) root=2 from reset]; decide)
  let k := PC (rawRun y u) root
  have bounds : 6≤k ∧ k≤10 := old
  have changed : PC (rawNext s (rawRun y u) e) root≠k := fun eq=>exit (eq ▸ old)
  have ten : k=10 := by
    apply Classical.byContradiction
    intro no
    have hi : k<10 := by omega
    have eq : rawRun z (lead++u)=rawRun y u := BStarResetSchedule.run_append (rawNext s) z lead u
    have fact := FreshSetupProgress.setup_change P o a rrel paid C released (lead++u) e
    change 6≤PC (rawRun z (lead++u)) root → _ at fact
    rw [eq] at fact
    have hit := fact bounds.1 hi changed
    have next : PC (rawNext s (rawRun y u) e) root=k+1 := hit.2.2.2.1
    apply exit
    rw [next]
    change 6≤k+1 ∧ k+1≤10
    omega
  have differs : PC (rawNext s (rawRun y u) e) root≠10 := ten ▸ changed
  obtain ⟨hist,consume,after⟩ := FreshAdmissionStart.return_state_of_change g P C qy idle u e 10
    (fun no=>Option.some_ne_none 0 (show some 0=none from no)) ten differs
  obtain ⟨pre,tour,door,issued,_,_,_,flight⟩ := from_idle hp hist
  obtain ⟨out,turn,ret,T,outbound,terminal,back⟩ := BStarAcquireAckAncestry.split_turn hp flight
  let front := pre++door::out
  have cut : u=front++turn::ret := by
    simp only [front,issued,T,List.append_assoc,List.cons_append]
  have state : rawRun y front=rawRun (rawNext s (rawRun y pre) door) out :=
    BStarResetSchedule.run_append (rawNext s) y pre (door::out)
  obtain ⟨m,G,_⟩ := BStarGeneratedTapeCuts.split hp front (turn::ret) (cut ▸ hist)
  have physical := BStarAcquireHistoryReturn.busy_end hp outbound
  let turnedAt := rawRun (rawNext s (rawRun y pre) door) out
  change Current hp g.base slot len turnedAt (.busy 10 (.out len)) at physical
  change Event hp slot len turnedAt turn (.busy 10 (.out len)) (.busy 10 (.back len)) at terminal
  change BusyOnly hp g.base slot len 10 (rawNext s turnedAt turn) (.back len) ret (.back 0) at back
  have chartState : rawRun y front=turnedAt := state
  rw [←chartState] at physical terminal back
  have same := current_mode_unique hp _ _ (BStarGeneratedTapeCuts.at_end hp G) physical
  subst m
  have beforeAck : rawRun y u=rawRun (rawNext s (rawRun y front) turn) ret := by
    rw [cut]
    exact BStarResetSchedule.run_append (rawNext s) y front (turn::ret)
  have full : BStarCopyFenceCuts.LiveAt hp C y u := by
    intro p t V
    refine ⟨g.fiber _ (keep g y p qy),?_⟩
    have someMark : ∃ f b,u++[e]=p++f::b := by
      rw [V]
      cases t with
      | nil => exact ⟨e,[],by simp⟩
      | cons j t => exact ⟨j,t++[e],by simp⟩
    obtain ⟨f,b,E⟩ := someMark
    have B := previous p f b E
    change 6≤PC (rawRun y p) root ∧ PC (rawRun y p) root≤10 at B
    change 6≤PC (rawRun y p) root ∧ PC (rawRun y p) root≤408
    omega
  rw [cut] at full
  exact ⟨front,turn,ret++e::v,by rw [W,cut,List.append_assoc]; rfl,G,terminal,
    (BStarCopyFenceCuts.split_live hp C full).1,ret,e,v,rfl,back,beforeAck ▸ consume,
    beforeAck ▸ after,full⟩

end L4.Height.FreshInjectEntry
