import Leader.L4.PhysicalResetFirstLaunch
import Leader.L4.PhysicalReceiptCut
import Leader.L4.PhysicalHealthyReturnClock

namespace L4.PhysicalResetFirstReceipt
open AllSizeProtocol BStarTrace PhysicalCustody BStarLongWork BStarLongClaims
open BStarH6WordChart BStarAcquireLiteralChain BStarLongFixedRouting
open BStarLongDoor BStarSeparatingRail BStarClearanceResidual
open BStarAcquireVisitOrder BStarResetChartTouch BStarResetChartService BStarAcquireAnchors
open BStarResetSchedule BStarResetMarkAdapter BStarResetHealthyService BStarAcquireRailCoverage
open PhysicalEligibleReply PhysicalReceiptCut
open ControllerTapeIID (expected_after_prefix)
local notation "hp" => (show 0<2 by decide)
local notation "append" => ResetReturnIID.appendTape

/-- Actual typed receipt reached after a physical launch. The Seen
journey ends at this precise sampled cut, with no eligible gap yet. -/
theorem healthy_exact_receipt_clock {s n : Nat} {base x : Raw s n}
    {hh : ∃ i,oldH6 (rows s) base i=true}
    {o : Owners (oldH6 (rows s) base)} {S : List (Pos n)} {len op : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall)
    (Q : Raw s n→Prop) (fiber : ∀ y,Q y→∀ j,Layout (rows s) base j=Layout (rows s) y j)
    (closed : ∀ y e,Q y→Q (rawNext s y e)) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (head : ∀ i, let g := longGeometry (rows s) (base i); (!g.axes.h6 || g.inside)=true)
    (cont : ∀ i, let g := oldPair (rows s) base i; continuation g.1 g.2=true)
    (H : op<3) (qx : Q x) (L : Launched base (fun j=>S.getD j fall) len op x) :
    let addr := fun j=>S.getD j fall
    Height.IIDExpectedHittingTimeAtMost append
      (fun w=>Seen (rawNext s) (project addr) (healthyTag op) len x (.out 0) w (.back 0) ∧
        Q (rawRun x w) ∧ Eligible base addr len op (rawRun x w)) [] (n*(2*len+1)) := by
  dsimp only
  apply expected_after_prefix _ _ [] _ _
    (stopped_exact_receipt (PhysicalHealthyReturnClock.healthy_return_of_actual_launch
      C Q fiber closed sep head cont H qx L))
  intro w h
  obtain ⟨J,⟨q,W⟩,K⟩ := h
  exact ⟨J,q,eligible_of_waiting_clean W K⟩

def FirstResetReceiptCut {s n : Nat} (base x : Raw s n)
    (Q : Raw s n→Prop) (addr : Nat→Pos n) (len op : Nat) (w : List (Fin n)) : Prop :=
  let door := RearTrace.predecessor (addr 0).1
  ∃ pre tour,w=pre++door::tour ∧ door∉pre ∧
    let old := rawRun x pre
    let seed := rawNext s old door
    Q old ∧ Ready addr len op old ∧ Q seed ∧ Launched base addr len op seed ∧
    Seen (rawNext s) (project addr) (healthyTag op) len seed (.out 0) tour (.back 0) ∧
    Q (rawRun x w) ∧ Eligible base addr len op (rawRun x w)

/-- Whole RESET0 setup from the residual clean boundary through first
door and first healthy return. No incident wins are charged here. -/
theorem first_reset0_receipt_of_boundary {s n : Nat} {base x : Raw s n}
    {hh : ∃ i,oldH6 (rows s) base i=true}
    {o : Owners (oldH6 (rows s) base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall) (hn : 0<n)
    (Q : Raw s n→Prop) (fiber : ∀ y,Q y→∀ j,Layout (rows s) base j=Layout (rows s) y j)
    (closed : ∀ y e,Q y→Q (rawNext s y e)) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (head : ∀ i, let g := longGeometry (rows s) (base i); (!g.axes.h6 || g.inside)=true)
    (cont : ∀ i, let g := oldPair (rows s) base i; continuation g.1 g.2=true)
    (I : Boundary Q (oldH6 (rows s) base) hh (fun j=>S.getD j fall) len x)
    (zero : (ctrlOp.read (x (S.getD 0 fall).1).long).toNat=0) :
    Height.IIDExpectedHittingTimeAtMost append
      (FirstResetReceiptCut base x Q (fun j=>S.getD j fall) len 0) [] (n+n*(2*len+1)) := by
  let addr := fun j=>S.getD j fall
  let door := RearTrace.predecessor (addr 0).1
  let A : List (Fin n) → Prop := fun w=>∃ pre,w=pre++[door] ∧ door∉pre ∧
    (Q (rawRun x pre) ∧ Ready addr len 0 (rawRun x pre)) ∧
    (Q (rawRun x w) ∧ Launched base addr len 0 (rawRun x w))
  let P := FirstResetReceiptCut base x Q addr len 0
  have first : Height.IIDExpectedHittingTimeAtMost append A [] n :=
    PhysicalResetFirstLaunch.first_reset0_launch_of_boundary C Q fiber closed sep I zero
  apply Height.iid_stage_le append hn [] A P n (n*(2*len+1))
    (expected_after_prefix _ _ [] _ (fun _ h=>.inl h) first)
  intro tape found
  obtain ⟨pre,E,N,⟨q,R⟩,W⟩ := found
  rw [E] at W ⊢
  let seed := rawNext s (rawRun x pre) door
  have atCut : rawRun x (pre++[door])=seed := by
    exact BStarResetSchedule.run_append (rawNext s) x pre [door]
  rw [atCut] at W
  apply expected_after_prefix _ P (pre++[door]) _ _
    (healthy_exact_receipt_clock C Q fiber closed sep head cont (by decide) W.1 W.2)
  intro tour H
  obtain ⟨J,Q0,E0⟩:=H
  have split : (pre++[door])++tour=pre++door::tour := by simp [List.append_assoc]
  have playback : rawRun x ((pre++[door])++tour)=rawRun seed tour := by
    change BStarResetSchedule.run (rawNext s) x ((pre++[door])++tour)=_
    rw [BStarResetSchedule.run_append]
    change rawRun (rawRun x (pre++[door])) tour=_
    rw [atCut]
  exact ⟨pre,tour,split,N,q,R,W.1,W.2,J,by rwa [playback],by rwa [playback]⟩

end L4.PhysicalResetFirstReceipt
