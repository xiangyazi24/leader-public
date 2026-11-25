import Leader.L4.PhysicalResetFirstReceipt
import Leader.L4.OrderedRaceTape

namespace L4.PhysicalHealthyRaces
open AllSizeProtocol BStarTrace PhysicalCustody BStarLongWork BStarLongClaims
open BStarH6WordChart BStarAcquireLiteralChain BStarLongFixedRouting
open BStarLongDoor BStarSeparatingRail BStarClearanceResidual
open BStarAcquireVisitOrder BStarResetChartTouch BStarResetChartService BStarAcquireAnchors
open BStarResetSchedule BStarResetMarkAdapter BStarResetHealthyService BStarAcquireRailCoverage
open PhysicalEligibleReply PhysicalResetFirstReceipt
local notation "hp" => (show 0<2 by decide)

def ArrivedHealthy {s n : Nat} (base x : Raw s n) (Q : Raw s n→Prop)
    (addr : Nat→Pos n) (len op : Nat) (w : List (Fin n)) : Prop :=
  Seen (rawNext s) (project addr) (healthyTag op) len x (.out 0) w (.back 0) ∧
    Q (rawRun x w) ∧ Eligible base addr len op (rawRun x w)

/-- Run the healthy tour, then an incident race at the exact typed receipt.
Instantiate k=2 for a middle RESET and k=1 for the final consume. -/
theorem healthy_race_expected {s n : Nat} {base x : Raw s n}
    {hh : ∃ i,oldH6 (rows s) base i=true}
    {o : Owners (oldH6 (rows s) base)} {S : List (Pos n)} {len op : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall)
    (Q : Raw s n→Prop) (fiber : ∀ y,Q y→∀ j,Layout (rows s) base j=Layout (rows s) y j)
    (closed : ∀ y e,Q y→Q (rawNext s y e)) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (head : ∀ i, let g := longGeometry (rows s) (base i); (!g.axes.h6 || g.inside)=true)
    (cont : ∀ i, let g := oldPair (rows s) base i; continuation g.1 g.2=true)
    (H : op<3) (qx : Q x) (L : Launched base (fun j=>S.getD j fall) len op x)
    (hn : 0<n) (k : Nat) (hk : 0<k) :
    let A := ArrivedHealthy base x Q (fun j=>S.getD j fall) len op
    let d := RearTrace.predecessor (S.getD 0 fall).1
    Height.IIDExpectedHittingTimeAtMost (OrderedRaceTape.tick A d k)
      OrderedRaceTape.done (OrderedRaceTape.enter A k []) (n*(2*len+1)+n*k) := by
  dsimp only
  exact OrderedRaceTape.combined_expected hn _ _ k hk _ 
    (healthy_exact_receipt_clock C Q fiber closed sep head cont H qx L)

/-- Accepting the two-door race produces the next authentic launch on
the actual tape, plus the disjoint split needed by the common replay. -/
theorem healthy_middle_accept {s n : Nat} {base x : Raw s n}
    {hh : ∃ i,oldH6 (rows s) base i=true}
    {o : Owners (oldH6 (rows s) base)} {S : List (Pos n)} {len op : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall)
    (Q : Raw s n→Prop) (fiber : ∀ y,Q y→∀ j,Layout (rows s) base j=Layout (rows s) y j)
    (closed : ∀ y e,Q y→Q (rawNext s y e)) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (H : op<2) (tour tail : List (Fin n)) :
    let addr := fun j=>S.getD j fall
    let d := RearTrace.predecessor (addr 0).1
    let A := ArrivedHealthy base x Q addr len op
    OrderedRaceTape.valid A d 2 (.racing tour tail .accept) →
    A tour ∧ ∃ a b rest, tail=a++d::(b++d::rest) ∧
      (∀ e∈a,DisjointMarks e d) ∧ (∀ e∈b,DisjointMarks e d) ∧
      (let y := rawRun x (tour++(a++d::(b++[d])))
       Q y ∧ Launched base addr len (op+1) y) := by
  dsimp only
  intro V
  let addr := fun j=>S.getD j fall
  let d := RearTrace.predecessor (addr 0).1
  let A := ArrivedHealthy base x Q addr len op
  obtain ⟨h,accept⟩ := OrderedRaceTape.accepted_split A d 2 (by decide) tour tail V
  obtain ⟨a,b,rest,E,D1,D2,Y⟩ := PhysicalHealthyReturnClock.next_healthy_on_actual_doublet
    C Q fiber closed sep H h.1.2.1 h.1.2.2 tail accept
  refine ⟨h.1,a,b,rest,E,D1,D2,?_⟩
  change Q (BStarResetSchedule.run (rawNext s) x (tour++(a++d::(b++[d])))) ∧
    Launched base addr len (op+1) (BStarResetSchedule.run (rawNext s) x (tour++(a++d::(b++[d]))))
  rw [BStarResetSchedule.run_append]
  exact Y

/-- Accepting the final single-door race really consumes the typed
reply at the sampled mark. Skipped labels are disjoint and uncredited. -/
theorem healthy_final_accept {s n : Nat} {base x : Raw s n}
    {hh : ∃ i,oldH6 (rows s) base i=true}
    {o : Owners (oldH6 (rows s) base)} {S : List (Pos n)} {len op : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall)
    (Q : Raw s n→Prop) (fiber : ∀ y,Q y→∀ j,Layout (rows s) base j=Layout (rows s) y j)
    (closed : ∀ y e,Q y→Q (rawNext s y e)) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (H : op<3) (tour tail : List (Fin n)) :
    let addr := fun j=>S.getD j fall
    let d := RearTrace.predecessor (addr 0).1
    let A := ArrivedHealthy base x Q addr len op
    OrderedRaceTape.valid A d 1 (.racing tour tail .accept) →
    A tour ∧ ∃ gap rest, tail=gap++d::rest ∧ (∀ e∈gap,DisjointMarks e d) ∧
      (let y := rawRun x (tour++(gap++[d]))
       Q y ∧ Ready addr len (op+1) y) := by
  dsimp only
  intro V
  let addr := fun j=>S.getD j fall
  let d := RearTrace.predecessor (addr 0).1
  let A := ArrivedHealthy base x Q addr len op
  obtain ⟨h,accept⟩ := OrderedRaceTape.accepted_split A d 1 (by decide) tour tail V
  obtain ⟨gap,rest,E,D⟩ := PhysicalRacePrefixes.one_gap ((PhysicalRacePrefixes.accepted_iff d 1 tail).mp accept)
  obtain ⟨q,live⟩ := eligible_gap C Q fiber closed sep H gap D h.1.2.1 h.1.2.2
  refine ⟨h.1,gap,rest,E,D,?_⟩
  change Q (BStarResetSchedule.run (rawNext s) x (tour++(gap++[d]))) ∧
    Ready addr len (op+1) (BStarResetSchedule.run (rawNext s) x (tour++(gap++[d])))
  rw [BStarResetSchedule.run_append,BStarResetSchedule.run_append]
  exact ⟨closed _ _ q,PhysicalEligibleReply.consume C H sep live⟩

/-- First RESET0 launch and return, followed on the same tape by its
two incident wins. The initial unrestricted first door costs n, and
is not an additional race. -/
theorem first_reset0_doublet_expected {s n : Nat} {base x : Raw s n}
    {hh : ∃ i,oldH6 (rows s) base i=true}
    {o : Owners (oldH6 (rows s) base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall) (hn : 0<n)
    (Q : Raw s n→Prop) (fiber : ∀ y,Q y→∀ j,Layout (rows s) base j=Layout (rows s) y j)
    (closed : ∀ y e,Q y→Q (rawNext s y e)) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (head : ∀ i, let g := longGeometry (rows s) (base i); (!g.axes.h6 || g.inside)=true)
    (cont : ∀ i, let g := oldPair (rows s) base i; continuation g.1 g.2=true)
    (I : Boundary Q (oldH6 (rows s) base) hh (fun j=>S.getD j fall) len x)
    (zero : (ctrlOp.read (x (S.getD 0 fall).1).long).toNat=0) :
    let A := FirstResetReceiptCut base x Q (fun j=>S.getD j fall) len 0
    let d := RearTrace.predecessor (S.getD 0 fall).1
    Height.IIDExpectedHittingTimeAtMost (OrderedRaceTape.tick A d 2)
      OrderedRaceTape.done (OrderedRaceTape.enter A 2 []) ((n+n*(2*len+1))+n*2) := by
  dsimp only
  exact OrderedRaceTape.combined_expected hn _ _ 2 (by decide) _
    (first_reset0_receipt_of_boundary C hn Q fiber closed sep head cont I zero)

/-- At a successful first RESET0 doublet, retain the exact initial
launch/return history plus the disjoint split and actual RESET1 launch. -/
theorem first_reset0_doublet_accept {s n : Nat} {base x : Raw s n}
    {hh : ∃ i,oldH6 (rows s) base i=true}
    {o : Owners (oldH6 (rows s) base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall)
    (Q : Raw s n→Prop) (fiber : ∀ y,Q y→∀ j,Layout (rows s) base j=Layout (rows s) y j)
    (closed : ∀ y e,Q y→Q (rawNext s y e)) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (tour tail : List (Fin n)) :
    let addr := fun j=>S.getD j fall
    let d := RearTrace.predecessor (addr 0).1
    let A := FirstResetReceiptCut base x Q addr len 0
    OrderedRaceTape.valid A d 2 (.racing tour tail .accept) →
    A tour ∧ ∃ a b rest, tail=a++d::(b++d::rest) ∧
      (∀ e∈a,DisjointMarks e d) ∧ (∀ e∈b,DisjointMarks e d) ∧
      (let y := rawRun x (tour++(a++d::(b++[d])))
       Q y ∧ Launched base addr len 1 y) := by
  dsimp only
  intro V
  let addr := fun j=>S.getD j fall
  let d := RearTrace.predecessor (addr 0).1
  let A := FirstResetReceiptCut base x Q addr len 0
  obtain ⟨h,accept⟩ := OrderedRaceTape.accepted_split A d 2 (by decide) tour tail V
  obtain ⟨pre,route,eq,noD,q0,R,q1,L,J,q2,el⟩ := h.1
  obtain ⟨a,b,rest,E,D1,D2,Y⟩ := PhysicalHealthyReturnClock.next_healthy_on_actual_doublet
    C Q fiber closed sep (by decide : 0<2) q2 el tail accept
  refine ⟨h.1,a,b,rest,E,D1,D2,?_⟩
  change Q (BStarResetSchedule.run (rawNext s) x (tour++(a++d::(b++[d])))) ∧
    Launched base addr len 1 (BStarResetSchedule.run (rawNext s) x (tour++(a++d::(b++[d]))))
  rw [BStarResetSchedule.run_append]
  exact Y

end L4.PhysicalHealthyRaces
