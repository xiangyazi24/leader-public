import Leader.L4.PhysicalRacePrefixes
import Leader.L4.ResetReturnIID

namespace L4.PhysicalHealthyReturnClock
open AllSizeProtocol BStarTrace PhysicalCustody BStarLongWork BStarLongClaims
open BStarLongToken BStarLongDoor BStarLongCommand BStarH6WordChart
open BStarAcquireVisitOrder BStarAcquireLiteralChain BStarAcquireAnchors
open BStarLongFixedRouting BStarAcquireForwardTrace BStarResetChartTouch
open BStarResetChartService BStarResetMarkAdapter BStarResetRailRing
open BStarResetSchedule BStarSeparatingRail BStarAcquireWaitControl
open BStarResetHealthyService BStarAcquireRailCoverage BStarResetChartNomination
open PhysicalEligibleReply BStarSeparatingProgress BStarResetCycle

local notation "hp" => (show 0<2 by decide)

/-- Clock starts at the actual post-race launch cut, where the reset's
typed forward marker and waiting control have already been checked.
It does not linearize or commute the clock's future IID labels. -/
theorem healthy_return_of_actual_launch {s n : Nat} {base y : Raw s n}
    {hh : ∃ i,oldH6 (rows s) base i=true}
    {o : Owners (oldH6 (rows s) base)} {S : List (Pos n)} {len op : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall)
    (Q : Raw s n→Prop) (fiber : ∀ y,Q y→∀ j,Layout (rows s) base j=Layout (rows s) y j)
    (closed : ∀ y e,Q y→Q (rawNext s y e)) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (head : ∀ i, let g := longGeometry (rows s) (base i); (!g.axes.h6 || g.inside)=true)
    (cont : ∀ i, let g := oldPair (rows s) base i; continuation g.1 g.2=true)
    (H : op<3) (qy : Q y) (L : Launched base (fun j=>S.getD j fall) len op y) :
    let addr := fun j=>S.getD j fall
    let root := (addr 0).1
    Height.IIDExpectedHittingTimeAtMost ResetReturnIID.appendTape
      (Stopped (rawNext s) (project addr) (healthyTag op) len
        (fun z=>Q z ∧ Waiting hp base root op z) y (.out 0)) [] (n*(2*len+1)) := by
  dsimp only
  obtain ⟨eOf,F,T⟩ := fixed_nominations hp C head cont
  have A := healthy_adapter_on hp C Q fiber (fun y q e=>closed y e q) sep op H eOf F T
  have good : Good (healthyTag op) len (project (fun j=>S.getD j fall) y) (.out 0) :=
    ⟨Nat.zero_le _,L.2,fun _ h=>(Nat.not_lt_zero _ h).elim⟩
  exact ResetReturnIID.clean_return_expected A y (.out 0) ⟨qy,L.1.1⟩ good

/-- The two doors on a successful physical doublet really consume the
old typed reply and launch the next healthy reset at the sampled cut.
This is stronger than merely having an equal commuted endpoint. -/
theorem next_healthy_on_actual_doublet {s n : Nat} {base y : Raw s n}
    {hh : ∃ i,oldH6 (rows s) base i=true}
    {o : Owners (oldH6 (rows s) base)} {S : List (Pos n)} {len op : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall)
    (Q : Raw s n→Prop) (fiber : ∀ y,Q y→∀ j,Layout (rows s) base j=Layout (rows s) y j)
    (closed : ∀ y e,Q y→Q (rawNext s y e)) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (H : op<2) (qy : Q y) (live : Eligible base (fun j=>S.getD j fall) len op y)
    (w : List (Fin n))
    (accept : PhysicalDoorRace.accepted (RearTrace.predecessor (S.getD 0 fall).1) 2 w=1) :
    let addr := fun j=>S.getD j fall
    let door := RearTrace.predecessor (addr 0).1
    ∃ a b tail, w=a++door::(b++door::tail) ∧
      (∀ e∈a,DisjointMarks e door) ∧ (∀ e∈b,DisjointMarks e door) ∧
      (let cut := rawRun y (a++door::(b++[door]))
       Q cut ∧ Launched base addr len (op+1) cut) := by
  dsimp only
  let d := RearTrace.predecessor (S.getD 0 fall).1
  obtain ⟨a,b,tail,rfl,A,B⟩ := PhysicalRacePrefixes.two_gaps
    ((PhysicalRacePrefixes.accepted_iff d 2 w).1 accept)
  obtain ⟨qa,l⟩ := eligible_gap C Q fiber closed sep (by omega) a A qy live
  have D := PhysicalEligibleReply.consume C (by omega) sep l
  have qd := closed _ d qa
  obtain ⟨qb,R⟩ := ready_gap C Q fiber closed sep b
    (fun e E=>(B e E).1) qd D
  have launch := PhysicalEligibleReply.launch C Q fiber closed sep (by omega) qb R
  refine ⟨a,b,tail,rfl,A,B,?_⟩
  have EQ : rawRun y (a++d::(b++[d]))=rawNext s (rawRun (rawNext s (rawRun y a) d) b) d := by
    change BStarResetSchedule.run (rawNext s) y (a++d::(b++[d]))=_
    rw [BStarResetSchedule.run_append]
    change BStarResetSchedule.run (rawNext s) (rawNext s (rawRun y a) d) (b++[d])=_
    rw [BStarResetSchedule.run_append]
    rfl
  rw [EQ]
  exact ⟨closed _ d qb,launch⟩

end L4.PhysicalHealthyReturnClock
