import Leader.L4.BStarReleaseLatch
import Leader.L4.BStarPhysicalPhase
import Leader.L4.BStarRRELExtract

namespace L4.BStarReleaseGrantSplice
open AllSizeProtocol BStarTrace BStarLongWork BStarH6WordChart
open BStarAcquireVisitOrder BStarAcquireLiteralChain BStarResetChartTouch
open BStarGeneratedOwner BStarGeneratedTapeCuts BStarGeneratedBandScan
open BStarGrantBirth BStarResetNoAcquire BStarLongFixedRouting BStarAcquireAnchors

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step (n:=n) B
local notation "play" => BStarResetSchedule.run step

private theorem same_run (x : X) (a : List (Fin n)) :
    BStarReleaseLatch.run step x a=play x a := by
  induction a generalizing x with
  | nil => rfl
  | cons e a ih => exact ih (step x e)

set_option maxHeartbeats 1500000 in
theorem first_release_grants {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (Q : X→Prop) (I : Q x)
    (layout : ∀ q,Q q→∀ i,BStarLongFixedRouting.Layout B base i=BStarLongFixedRouting.Layout B q i)
    (closed : ∀ q,Q q→∀ e,Q (step q e))
    (idle : Current hp base (fun j => S.getD j fall) len x .idle)
    (cut : Nat) (a : List (Fin n)) (e i : Fin n) (j : Fin 3)
    (own : commandOwner (oldH6 B base) i (BStarResetNoAcquire.slot j)=o.val) :
    let root := (S.getD 0 fall).1
    let ended := BStarReleaseLatch.after step (fun z=>pc z root) cut x
    ended a=false → ended (a++[e])=true →
      cut≤a.length ∧ bit (play x a) i j=0 ∧ bit (step (play x a) e) i j=0 := by
  dsimp only
  intro old new
  obtain ⟨K,P,N⟩ := BStarReleaseLatch.first_release_mark step (fun z=>pc z (S.getD 0 fall).1)
    cut x a e old new
  rw [same_run hp] at P N
  obtain ⟨before,trace,qa,cur⟩ := generated_word hp chart Q layout closed sep a .idle I idle
  obtain ⟨after,ev,post⟩ := current_step hp chart Q layout closed sep qa e before cur
  obtain ⟨head,slot⟩ := root_cuts hp chart Q I (fun y f P=>closed y P f) layout a
  have hit := BStarPhysicalPhase.rrel_stop hp (base:=base) (x:=play x a) (addr:=fun j=>S.getD j fall) (len:=len) (a:=before) (b:=after) e slot head (sep e) cur post ev P N
  refine ⟨K,?_⟩
  exact BStarRRELExtract.generated_rrel_grant_zero hp chart sep Q I layout
    (fun z f q=>closed z q f) a e i j own (hit.1 ▸ trace) hit.2.2

end L4.BStarReleaseGrantSplice
