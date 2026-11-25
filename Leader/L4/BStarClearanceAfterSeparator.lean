import Leader.L4.BStarClearanceResidual
import Leader.L4.BStarResetHealthyCycle

namespace L4.BStarClearanceAfterSeparator
set_option maxRecDepth 4096
open AllSizeProtocol BStarTrace BStarLongWork BStarLongTransport BStarLongToken
open BStarH6WordChart BStarAcquireVisitOrder BStarAcquireAnchors BStarAcquireRailCoverage
open BStarAcquireLiteralChain BStarLongFiberOwner BStarLongFixedRouting BStarResetChartTouch
open BStarResetMarkAdapter BStarResetChartService BStarResetSchedule BStarSeparatingRail
open BStarSeparatorControl BStarClearanceSource BStarClearancePhysical BStarClearanceOffset
open BStarLongDoor

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step B

open BStarClearanceResidual BStarClearanceSettled BStarResetHealthyCycle
open BStarLongCommand

theorem reach_clean_after_resets {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall)
    (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (head : ∀ i, let g := longGeometry B (base i); (!g.axes.h6 || g.inside)=true)
    (cont : ∀ i, let g := oldPair B base i; continuation g.1 g.2=true)
    (Q : X → Prop) (closed : ∀ y e, Q y → Q (step y e))
    (same : ∀ y, Q y → ∀ i, Layout B base i=Layout B y i)
    (heads : ∀ y, Q y → ∀ i, let g := longGeometry B (y i); (!g.axes.h6 || g.inside)=true)
    (conts : ∀ y, Q y → ∀ i, let g := oldPair B y i; continuation g.1 g.2=true)
    (cb : correct (oldH6 B base) hh 5 base) (I : Q x)
    (cx : correct (oldH6 B base) hh 5 x) :
    let addr := fun j => S.getD j fall
    let root := (addr 0).1
    let door := RearTrace.predecessor root
    let pc := fun y : X => (ctrlOp.read (y root).long).toNat
    let Inv := Boundary Q (oldH6 B base) hh addr len
    ∃ (u : List (Fin n)) (arg : Nat) (v residual w₀ w₁ w₂ : List (Fin n))
      (k : Nat) (y₁ y₂ y₃ : X),
      let before := BStarResetSchedule.run step x u
      let launched := step before door
      let returned := BStarResetSchedule.run step launched v
      let consumed := step returned door
      let zero := BStarResetSchedule.run step consumed residual
      let whole := u ++ (door::(v++[door])) ++ residual ++ w₀ ++ w₁ ++ w₂
      Launch (before root).long (launched root).long ∧
      project addr launched 0=forward (pc before) arg ∧
      Seen step (project addr) anyTag len launched (.out 0) v (.back 0) ∧
      Clean (project addr) anyTag len returned ∧ Inv consumed ∧ k≤412 ∧
      BStarControllerLoop.FiniteAttempts step Inv pc consumed zero k residual ∧ Inv zero ∧ pc zero=0 ∧
      Stage hp addr len 0 zero w₀ y₁ ∧ Stage hp addr len 1 y₁ w₁ y₂ ∧
      Stage hp addr len 2 y₂ w₂ y₃ ∧
      BStarResetSchedule.run step x whole=y₃ ∧
      Q y₃ ∧ correct (oldH6 B base) hh 5 y₃ ∧
      (∀ j≤len, project addr y₃ j=.empty) ∧
      (ctrlPhase.read (y₃ root).long).toNat=1 ∧ pc y₃=3 ∧
      (w₀++w₁++w₂).length≤3*(n*(2*len+1)+2) := by
  dsimp only
  let addr := fun j => S.getD j fall
  let root := (addr 0).1
  let door := RearTrace.predecessor root
  let P := fun y : X => Q y ∧ correct (oldH6 B base) hh 5 y
  have pcstep (y : X) (e : Fin n) (J : P y) : P (step y e) :=
    settled_step hp (oldH6 B base) hh sep Q closed
      (fun q h i => (congrArg Prod.fst (same q h i)).symm) y e J
  obtain ⟨u,arg,v,H⟩ := BStarClearanceAttempt.arbitrary_attempt hp chart sep head cont
    Q closed same heads conts cb I cx
  let before := BStarResetSchedule.run step x u
  let launched := step before door
  let returned := BStarResetSchedule.run step launched v
  let consumed := step returned door
  obtain ⟨launch,_,F,seen,clean,_,Qc,Hc,Ec,Ph,next,range,eq⟩ := H
  have L : next<413 := range.elim (fun h => h.symm ▸ (by decide : (0 : Nat)<413)) And.right
  have bc : Boundary Q (oldH6 B base) hh addr len consumed :=
    ⟨Qc,Hc,legal_issue _ Ph (eq.symm ▸ L),Ec⟩
  obtain ⟨k,residual,K,tries,bz,op0⟩ := to_issue_zero hp chart sep head cont
    Q closed same heads conts cb bc
  let zero := BStarResetSchedule.run step consumed residual
  obtain ⟨w₀,w₁,w₂,y₁,y₂,y₃,A,D,G,Q₃,E₃,P₃,O₃,Bd⟩ :=
    three_resets hp chart P (fun q h => same q h.1) (fun q h e => pcstep q e h) sep head cont
      (show P zero from ⟨bz.lower,bz.offset⟩) bz.issue.2 op0
  refine ⟨u,arg,v,residual,w₀,w₁,w₂,k,y₁,y₂,y₃,launch,F,seen,clean,bc,K,tries,bz,op0,
    A,D,G,?_,Q₃.1,Q₃.2,E₃,P₃,O₃,Bd⟩
  obtain ⟨_,_,Aeq,_,_,_,_⟩ := A
  obtain ⟨_,_,Deq,_,_,_,_⟩ := D
  obtain ⟨_,_,Geq,_,_,_,_⟩ := G
  simp only [BStarResetSchedule.run_append]
  rw [Geq,Deq,Aeq]
  have path : BStarResetSchedule.run step before (door::(v++[door]))=consumed := by
    change BStarResetSchedule.run step launched (v++[door])=consumed
    rw [BStarResetSchedule.run_append]
    rfl
  change BStarResetSchedule.run step (BStarResetSchedule.run step
    (BStarResetSchedule.run step (BStarResetSchedule.run step
      (BStarResetSchedule.run step before (door::(v++[door]))) residual) w₀) w₁) w₂ = _
  rw [path]

end L4.BStarClearanceAfterSeparator
