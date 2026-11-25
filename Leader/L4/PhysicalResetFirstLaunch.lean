import Leader.L4.PhysicalEligibleReply
import Leader.L4.ResetReturnIID
import Leader.L4.ResidualIssueIID

namespace L4.PhysicalResetFirstLaunch
open AllSizeProtocol BStarTrace PhysicalCustody BStarLongWork BStarLongClaims
open BStarH6WordChart BStarAcquireLiteralChain BStarLongFixedRouting
open BStarLongDoor BStarSeparatingRail BStarClearanceResidual
open PhysicalEligibleReply BStarAcquireVisitOrder BStarResetChartTouch BStarResetChartService BStarAcquireAnchors

local notation "hp" => (show 0<2 by decide)

/-- A whole clean ISSUE chart waits for its first actual source mark.
Non-door marks need not be disjoint; this is a clock, not a replay race. -/
theorem first_reset_launch_expected {s n : Nat} {base x : Raw s n}
    {hh : ∃ i,oldH6 (rows s) base i=true}
    {o : Owners (oldH6 (rows s) base)} {S : List (Pos n)} {len op : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall)
    (Q : Raw s n→Prop) (fiber : ∀ y,Q y→∀ j,Layout (rows s) base j=Layout (rows s) y j)
    (closed : ∀ y e,Q y→Q (rawNext s y e)) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (H : op<3) (qx : Q x) (init : Ready (fun j=>S.getD j fall) len op x) :
    let addr := fun j=>S.getD j fall
    let door := RearTrace.predecessor (addr 0).1
    Height.IIDExpectedHittingTimeAtMost ResetReturnIID.appendTape
      (fun w=>∃ pre,w=pre++[door] ∧ door∉pre ∧
        (Q (rawRun x pre) ∧ Ready addr len op (rawRun x pre)) ∧
        (Q (rawRun x w) ∧ Launched base addr len op (rawRun x w))) [] n := by
  dsimp only
  let addr := fun j=>S.getD j fall
  let door := RearTrace.predecessor (addr 0).1
  let Stop : List (Fin n)→Prop := fun w=>∃ pre,w=pre++[door] ∧ door∉pre ∧
    (Q (rawRun x pre) ∧ Ready addr len op (rawRun x pre)) ∧
    (Q (rawRun x w) ∧ Launched base addr len op (rawRun x w))
  let Live : List (Fin n)→Nat→Prop := fun w k=>k=1 ∧ door∉w
  have advance (w : List (Fin n)) (k : Nat) (L : Live w k) : ∃ d : Fin n, ∀ e : Fin n,
      Stop (ResetReturnIID.appendTape w e) ∨
        ∃ j, Live (ResetReturnIID.appendTape w e) j ∧ j≤k ∧ (e=d→j<k) := by
    refine ⟨door,fun e=>?_⟩
    obtain ⟨rfl,N⟩ := L
    by_cases E : e=door
    · subst e
      left
      have pre := ready_gap C Q fiber closed sep w (fun e M E=>N (show door ∈ w from by change e = door at E; rwa [E] at M)) qx init
      refine ⟨w,rfl,N,pre,?_⟩
      change Q (BStarResetSchedule.run (rawNext s) x (w++[door])) ∧
        Launched base addr len op (BStarResetSchedule.run (rawNext s) x (w++[door]))
      rw [BStarResetSchedule.run_append]
      exact ⟨closed _ _ pre.1,PhysicalEligibleReply.launch C Q fiber closed sep H pre.1 pre.2⟩
    · right
      refine ⟨1,⟨rfl,?_⟩,Nat.le_refl _,fun h=>(E h).elim⟩
      simpa [ResetReturnIID.appendTape, E, Ne.symm E] using N
  simpa only [Nat.mul_one] using
    ResetReturnIID.iid_of_relational_rank ResetReturnIID.appendTape Stop Live
      (fun _ _ q=>q.1.symm ▸ Nat.one_pos) advance [] 1 (.inr ⟨rfl,by simp⟩)

/-- A residual-controller ISSUE0 boundary is exactly the readiness
needed by the first RESET0 physical launch clock. -/
theorem first_reset0_launch_of_boundary {s n : Nat} {base x : Raw s n}
    {hh : ∃ i,oldH6 (rows s) base i=true}
    {o : Owners (oldH6 (rows s) base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall)
    (Q : Raw s n→Prop) (fiber : ∀ y,Q y→∀ j,Layout (rows s) base j=Layout (rows s) y j)
    (closed : ∀ y e,Q y→Q (rawNext s y e)) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (I : Boundary Q (oldH6 (rows s) base) hh (fun j=>S.getD j fall) len x)
    (zero : (ctrlOp.read (x (S.getD 0 fall).1).long).toNat=0) :
    let addr := fun j=>S.getD j fall
    let door := RearTrace.predecessor (addr 0).1
    Height.IIDExpectedHittingTimeAtMost ResetReturnIID.appendTape
      (fun w=>∃ pre,w=pre++[door] ∧ door∉pre ∧
        (Q (rawRun x pre) ∧ Ready addr len 0 (rawRun x pre)) ∧
        (Q (rawRun x w) ∧ Launched base addr len 0 (rawRun x w))) [] n := by
  exact first_reset_launch_expected C Q fiber closed sep (by decide) I.lower
    ⟨I.clean,I.issue.2,zero⟩

#print axioms first_reset0_launch_of_boundary
#print axioms first_reset_launch_expected
end L4.PhysicalResetFirstLaunch
