import Leader.L4.BStarGeneratedTapeCuts
import Leader.L4.BStarCommitTailScan
import Leader.L4.BStarGeneratedIdleStage
import Leader.L4.BStarRetainedActualSamples

namespace L4.BStarAttemptCuts
set_option maxRecDepth 8192
set_option maxHeartbeats 2800000
open AllSizeProtocol BStarTrace BStarLongClaims BStarLongWork BStarH6WordChart
open BStarAcquireVisitOrder BStarAcquireAnchors BStarAcquireLiteralChain
open BStarResetChartTouch BStarGeneratedOwner BStarLongFixedRouting
open BStarLongCommand BStarLongDoor BStarClearanceSource BStarOwnerLaunchOrigin
open BStarGeneratedTapeCuts BStarCommitTailScan BStarCommitGeneratedTail

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step B
local notation "run" => BStarResetSchedule.run step
local notation "pc" => BStarGeneratedBandScan.pc

/-- The source's actual successful ACQUIRE and the bank-selecting
receipt occur on one generated attempt, even if an arbitrarily
long earlier prefix contained reboots and failed attempts. -/
theorem attempt_cuts {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall) (Q : X → Prop) (I : Q x)
    (fiber : ∀ y,Q y → ∀ i,Layout B base i=Layout B y i)
    (closed : ∀ y e,Q y → Q (step y e)) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    {w : List (Fin n)}
    (T : GeneratedOwner hp base (fun j => S.getD j fall) len x .idle w .idle)
    (early : pc x (S.getD 0 fall).1<6)
    (last : pc (run x w) (S.getD 0 fall).1=411) :
    let addr := fun j => S.getD j fall
    let root := (addr 0).1
    ∃ (lead mid late hold : List (Fin n)) (accept pick : Fin n) (op : Nat),
      w=lead++accept::(mid++pick::hold) ∧
      GeneratedOwner hp base addr len x .idle lead (.busy acquire (.back 0)) ∧
      Event hp addr len (run x lead) accept (.busy acquire (.back 0)) .idle ∧
      pc (step (run x lead) accept) root=6 ∧
      (∃ first finish,
        mid=first++finish ∧
        let half := run (step (run x lead) accept) first
        let old := run half finish
        pc half root=408 ∧
        BStarGeneratedBandScan.LiveWord hp root (step (run x lead) accept) first ∧
        finish=late ∧ BeforeChoice hp base addr len half finish ∧ PreBand hp half root finish ∧
        Current hp base addr len old (.busy op (.back 0)) ∧
        Event hp addr len old pick (.busy op (.back 0)) .idle ∧
        pc (step old pick) root=411 ∧
        GeneratedOwner hp base addr len (step old pick) .idle hold .idle ∧
        TailBand hp (step old pick) root hold ∧
        (∀ e∈hold,rightNeighbor e≠root)) := by
  dsimp only
  let addr := fun j => S.getD j fall
  let root := (addr 0).1
  change pc x root<6 at early
  have A : (addr 0).2=0 := (root_cuts hp C Q I closed fiber []).2
  rcases last_stage_entry hp A sep T (fun u _ _ => (root_cuts hp C Q I closed fiber u).1) last with
    band | ⟨pre,finish,post,W,prev,advance,pc408,rest,good⟩
  · have L := (band [] w rfl).2.1
    change 408≤pc x root at L
    omega
  let s := step (run x pre) finish
  have fin : pc (run s post) root=411 := by
    have H : run x w=run s post := by
      rw [W,BStarResetSchedule.run_append]
      rfl
    rw [←H]; exact last
  obtain ⟨late,pick,hold,op,F,choice,preband,old,consume,pc411,done⟩ :=
    first_411 hp A sep rest good (show pc s root<411 from (show pc s root=408 from pc408) ▸ (by decide : 408<411)) fin
  let endA := pre++[finish]
  have WL : w=endA++post := by simp only [endA,W,List.append_assoc,List.singleton_append]
  have splitT : GeneratedOwner hp base addr len x .idle (endA++post) .idle := WL ▸ T
  obtain ⟨m,first,remain⟩ := BStarGeneratedTapeCuts.split hp endA post splitT
  have heq : run x endA=s := by simp only [endA,s,BStarResetSchedule.run_append]; rfl
  have CM := at_start hp remain
  rw [heq] at CM
  have m0 : m=.idle := idle_of_issue hp CM (at_start hp rest).1
  subst m
  have P : pc (run x endA) root=408 := heq ▸ pc408
  have origin := BStarGeneratedIdleStage.capture_origin_from_early hp C Q I fiber closed sep first early P
  obtain ⟨lead,accept,mid,V,G,E,pc6,live⟩ :=
    BStarRetainedActualSamples.origin_consume hp C Q I fiber closed sep (at_start hp T) endA origin
  let half := run (step (run x lead) accept) mid
  have H : half=s := by
    rw [←heq,V,BStarResetSchedule.run_append]
    rfl
  have sub : TailBand hp (step (run s late) pick) root hold := by
    intro u v eq
    have U : post=(late++pick::u)++v := by rw [F,eq]; simp only [List.append_assoc,List.cons_append]
    have q := good (late++pick::u) v U
    rw [BStarResetSchedule.run_append] at q
    exact q
  dsimp only [half] at H
  have foreign := ready_411_foreign hp A sep done sub rfl rfl pc411
  refine ⟨lead,mid++late,late,hold,accept,pick,op,?_,G,E,pc6,
    mid,late,rfl,?_,live,rfl,?_,?_,?_,?_,?_,?_,?_,foreign⟩
  · rw [WL,V,F]; simp only [List.append_assoc,List.cons_append]
  · exact H.symm ▸ pc408
  · exact H.symm ▸ choice
  · exact H.symm ▸ preband
  · exact H.symm ▸ old
  · exact H.symm ▸ consume
  · exact H.symm ▸ pc411
  · exact H.symm ▸ done
  · exact H.symm ▸ sub

end L4.BStarAttemptCuts
