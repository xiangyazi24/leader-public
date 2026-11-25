import Leader.L4.PhysicalEligibleSeen
import Leader.L4.BStarSeparatorReceipt

namespace L4.PhysicalEligibleReply
open AllSizeProtocol BStarTrace PhysicalCustody BStarLongWork BStarLongClaims
open BStarLongToken BStarLongDoor BStarLongCommand BStarH6WordChart
open BStarAcquireVisitOrder BStarAcquireLiteralChain BStarAcquireAnchors
open BStarLongFixedRouting BStarAcquireForwardTrace BStarResetChartTouch
open BStarResetChartService BStarResetMarkAdapter BStarResetRailRing
open BStarResetSchedule BStarSeparatingRail BStarAcquireWaitControl
open BStarGeneratedOwner BStarClearanceSource BStarSeparatorControl
local notation "hp" => (show 0<2 by decide)

/-- Arbitrary-op separator reply: none of the disjoint waiting marks
may alter the exact reply or spoil the remainder of this chart. -/
theorem separator_gap {s n : Nat} {base y : Raw s n} {hh : ∃ i,oldH6 (rows s) base i=true}
    {o : Owners (oldH6 (rows s) base)} {S : List (Pos n)} {len op : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall)
    (Q : Raw s n→Prop) (fiber : ∀ y,Q y→∀ j,Layout (rows s) base j=Layout (rows s) y j)
    (closed : ∀ y e,Q y→Q (rawNext s y e)) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (gap : List (Fin n))
    (ind : ∀ e∈gap,DisjointMarks e (RearTrace.predecessor (S.getD 0 fall).1))
    (q : Q y) (wait : Waiting hp base (S.getD 0 fall).1 op y)
    (clean : Clean (project (fun j=>S.getD j fall)) anyTag len y) :
    let addr := fun j=>S.getD j fall
    Waiting hp base (addr 0).1 op (rawRun y gap) ∧
    Clean (project addr) anyTag len (rawRun y gap) ∧
    project addr (rawRun y gap) 0=project addr y 0 := by
  dsimp only
  let addr := fun j=>S.getD j fall
  let root := (addr 0).1
  induction gap generalizing y with
  | nil => exact ⟨wait,clean,rfl⟩
  | cons e w ih =>
    have A := away_of_disjoint root e (ind e List.mem_cons_self)
    have E : rawNext s y e root=y root := by
      simp only [rawNext,AllSizeS1Geometry.step,if_neg (Ne.symm A.2.2),if_neg (Ne.symm A.2.1)]
    have H : project addr (rawNext s y e) 0=project addr y 0 := by
      change atSite (rawNext s y e root).long (addr 0).2=_
      rw [E]
      rfl
    have q' := closed _ e q
    have W : Waiting hp base root op (rawNext s y e) := by
      refine ⟨fiber _ q',?_,?_,?_⟩
      · rw [E]; exact wait.2.1
      · rw [E]; exact wait.2.2.1
      · rw [E]; exact wait.2.2.2
    have L := (arrived_nonown hp C (fiber _ q) e (sep e) A.1 clean).1
    obtain ⟨a,b,c⟩ := ih (fun f F=>ind f (List.mem_cons_of_mem _ F)) q' W L
    exact ⟨a,b,c.trans H⟩

/-- A successful one-door separator wait bubbles the actual consume
to the replay's front and leaves the first real boundary at that cut. -/
theorem separator_replay {s n : Nat} {base y : Raw s n} {hh : ∃ i,oldH6 (rows s) base i=true}
    {o : Owners (oldH6 (rows s) base)} {S : List (Pos n)} {len op : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall)
    (Q : Raw s n→Prop) (fiber : ∀ y,Q y→∀ j,Layout (rows s) base j=Layout (rows s) y j)
    (closed : ∀ y e,Q y→Q (rawNext s y e)) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (gap tail : List (Fin n))
    (ind : ∀ e∈gap,DisjointMarks e (RearTrace.predecessor (S.getD 0 fall).1))
    (q : Q y) (wait : Waiting hp base (S.getD 0 fall).1 op y)
    (clean : Clean (project (fun j=>S.getD j fall)) anyTag len y) :
    let addr := fun j=>S.getD j fall
    let root := (addr 0).1
    let door := RearTrace.predecessor root
    Commuted (gap++door::tail) (door::(gap++tail)) ∧
    (∀ a b,gap=a++b → Waiting hp base root op (rawRun y a) ∧
      Clean (project addr) anyTag len (rawRun y a) ∧
      project addr (rawRun y a) 0=project addr y 0) ∧
    ∃ pc,(pc=0 ∨ (op<pc ∧ pc<413)) ∧
      Ready addr len pc (rawNext s y door) ∧ Ready addr len pc (rawNext s (rawRun y gap) door) := by
  dsimp only
  let root := (S.getD 0 fall).1
  let door := RearTrace.predecessor root
  obtain ⟨empty,phase,pc,inRange,atPc⟩ := BStarSeparatorReceipt.consume hp C op sep wait clean
  have R : Ready (fun j=>S.getD j fall) len pc (rawNext s y door) := ⟨empty,phase,atPc⟩
  have replay := bubble_door gap tail door ind
  have raw := rawRun_of_commuted y (bubble_door gap [] door ind)
  have exactEnd : rawNext s (rawRun y gap) door = rawRun (rawNext s y door) gap := by
    have A : rawRun y (gap++[door])=rawNext s (rawRun y gap) door :=
      BStarResetSchedule.run_append _ _ _ _
    rw [←A]
    have T : rawRun y (gap++[door])=rawRun y (door::gap) := by simpa only [List.append_nil] using raw
    exact T
  have retain := ready_gap C Q fiber closed sep gap (fun e E=>(away_of_disjoint root e (ind e E)).1)
    (closed _ door q) R
  refine ⟨replay,?_,pc,inRange,R,exactEnd.symm ▸ retain.2⟩
  intro a b E
  exact separator_gap C Q fiber closed sep a
    (fun e mem=>ind e (E.symm ▸ List.mem_append_left b mem)) q wait clean

end L4.PhysicalEligibleReply
