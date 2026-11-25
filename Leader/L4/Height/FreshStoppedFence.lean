import Leader.L4.Height.FreshInjectEntry

namespace L4.Height.FreshStoppedFence
open AllSizeProtocol PhysicalCustody ProductionCustody ProductionCycles FreshFirstAcquire
open BStarLongDoor BStarH6WordChart BStarResetChartTouch BStarGeneratedOwner
open BStarAcquireLiteralChain BStarAcquireVisitOrder BStarSteeredLikelihood BStarOwnerLaunchOrigin
open BStarCopyFenceCuts

variable {s n : Nat} {x : Raw s n} {g : CustodyWitness x}
local notation "hp" => (show 0<2 by decide)
local notation "h" => oldH6 (rows s) g.base

/-- A generated continuation from idle ISSUE11 to the next RESET2
contains a real outward FENCE turn and a real return. Every old mark
through that return stays on the original FENCE band. -/
theorem first_fence_return (P : Production g) {o : Owners h} {S : List (Pos n)} {len : Nat}
    {fall : Pos n} (C : Chart hp g.base g.hh o S len fall)
    (y : Raw s n) (qy : g.Q y) (w : Word n) :
    let slot := fun j=>S.getD j fall
    let root := (slot 0).1
    Current hp g.base slot len y .idle → PC y root=11 → PC (rawRun y w) root=2 →
    ∃ pre turn back ack post,w=pre++turn::(back++ack::post) ∧
      GeneratedOwner hp g.base slot len y .idle pre (.busy 11 (.out len)) ∧
      Event hp slot len (rawRun y pre) turn (.busy 11 (.out len)) (.busy 11 (.back len)) ∧
      BusyOnly hp g.base slot len 11 (rawNext s (rawRun y pre) turn) (.back len) back (.back 0) ∧
      Event hp slot len (rawRun (rawNext s (rawRun y pre) turn) back) ack (.busy 11 (.back 0)) .idle ∧
      Current hp g.base slot len (rawNext s (rawRun (rawNext s (rawRun y pre) turn) back) ack) .idle ∧
      LiveAt hp C y (pre++turn::back) := by
  dsimp only
  let slot := fun j => S.getD j fall
  let root := (S.getD 0 fall).1
  intro idle issue reset
  obtain ⟨u,e,v,W,old,exit,previous⟩ := first_outside (·=11) y root w issue
    (by rw [show PC (rawRun y w) root=2 from reset]; decide)
  obtain ⟨hist,consume,after⟩ := FreshAdmissionStart.return_state_of_change g P C qy idle u e 11
    (fun no=>Option.some_ne_none 0 (show some 0=none from no)) old exit
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
  change Current hp g.base slot len turnedAt (.busy 11 (.out len)) at physical
  change Event hp slot len turnedAt turn (.busy 11 (.out len)) (.busy 11 (.back len)) at terminal
  change BusyOnly hp g.base slot len 11 (rawNext s turnedAt turn) (.back len) ret (.back 0) at back
  have chartState : rawRun y front=turnedAt := state
  rw [←chartState] at physical terminal back
  have same := current_mode_unique hp _ _ (BStarGeneratedTapeCuts.at_end hp G) physical
  subst m
  have beforeAck : rawRun y u=rawRun (rawNext s (rawRun y front) turn) ret := by
    rw [cut]
    exact BStarResetSchedule.run_append (rawNext s) y front (turn::ret)
  refine ⟨front,turn,ret,e,v,by rw [W,cut,List.append_assoc]; rfl,G,terminal,back,
    beforeAck ▸ consume,beforeAck ▸ after,?_⟩
  rw [←cut]
  intro a t eq
  refine ⟨g.fiber _ (keep g y a qy),?_⟩
  have existsMark : ∃ f b,u++[e]=a++f::b := by
    rw [eq]
    cases t with
    | nil => exact ⟨e,[],by simp⟩
    | cons j t => exact ⟨j,t++[e],by simp⟩
  obtain ⟨f,b,A⟩ := existsMark
  change 6≤PC (rawRun y a) root ∧ PC (rawRun y a) root≤408
  rw [show PC (rawRun y a) root=11 from previous a f b A]
  decide

#print axioms first_fence_return
end L4.Height.FreshStoppedFence
