import Leader.L4.BStarPaceChartLedger
import Leader.L4.BStarGeneratedTapeCuts
import Leader.L4.BStarPaceChronology
import Leader.L4.BStarOwnerLaunchOrigin

namespace L4.BStarRepeatedPace
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
open AllSizeProtocol BStarTrace BStarLongClaims BStarLongWork BStarLongToken
open BStarH6WordChart BStarAcquireVisitOrder BStarAcquireAnchors BStarAcquireLiteralChain
open BStarLongFixedRouting BStarResetMarkAdapter BStarResetChartTouch BStarResetChartService
open BStarSeparatingRail BStarGeneratedOwner BStarOwnerLaunchOrigin BStarOwnerControlHistory
open BStarPaceChronology BStarLongDoor BStarLongCommand BStarClearanceSource
open BStarCommitGeneratedTail BStarGeneratedTapeCuts BStarLongToken

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step (n:=n) B
local notation "run" => BStarResetSchedule.run step

def Ready4 (addr : Nat→Pos n) (x : X) (m : Mode) : Prop :=
  m=.idle ∧ (ctrlOp.read (x (addr 0).1).long).toNat=admit

private theorem step_ready4 {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (same : ∀ j,Layout B base j=Layout B x j)
    {a : Mode} {e : Fin n}
    (cur : Current hp base (fun j=>S.getD j fall) len x a)
    (event : Event hp (fun j=>S.getD j fall) len x e a .idle)
    (H : (ctrlOp.read (step x e (S.getD 0 fall).1).long).toNat=admit) :
    Ready4 (fun j=>S.getD j fall) x a ∨ a=.busy 3 (.back 0) := by
  cases event with
  | idle_hold away =>
    have F := idle_nonown hp C same cur.2 e (sep e) away
    have P := congrArg (fun c : BitVec 2×BitVec 9=>c.2.toNat) F.2
    have PC : (ctrlOp.read (step x e (S.getD 0 fall).1).long).toNat =
        (ctrlOp.read (x (S.getD 0 fall).1).long).toNat := P
    exact .inl ⟨rfl,PC.symm.trans H⟩
  | bad_issue own bad =>
    rcases idle_launch_or_hold hp C same cur.2 sep e cur.1 with A|A|A
    · exact (A.1 own).elim
    · have pc := congrArg (fun c : (Token×BitVec 2)×BitVec 9=>c.2.toNat) A.2.2.1
      have Z : (ctrlOp.read (step x e (S.getD 0 fall).1).long).toNat=0 := pc
      exact ((by decide : admit≠0) (H.symm.trans Z)).elim
    · obtain ⟨_,v,_⟩ := A.2.1.2
      have impossible := bad.symm.trans v
      cases impossible
  | consume op eq E' =>
    have root := root_header hp C same
    have ev : Event hp (fun j=>S.getD j fall) len x e (.busy op (.back 0)) .idle := .consume op eq E'
    have P := actual_consume_to_admit hp (base:=base) (x:=x) (addr:=fun j=>S.getD j fall)
      (len:=len) (op:=op) (e:=e) root.2 root.1 (sep e) cur ev H
    exact .inr (congrArg (fun p=>Mode.busy p (.back 0)) P.1)

/-- Invert exact generation of a ready ADMIT source. If it was not
already ready at the query cut, an earlier actual matching PACE consume
occurs strictly inside its prefix. -/
theorem ready4_origin {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (layout : ∀ p j,Layout B base j=Layout B (run x p) j)
    {a : Mode} {w : List (Fin n)}
    (G : GeneratedOwner hp base (fun j=>S.getD j fall) len x a w .idle)
    (E : Ready4 (fun j=>S.getD j fall) (run x w) .idle) :
    Ready4 (fun j=>S.getD j fall) x a ∨
      ∃ pre ack rest, w=pre++ack::rest ∧
        GeneratedOwner hp base (fun j=>S.getD j fall) len x a pre (.busy 3 (.back 0)) ∧
        Event hp (fun j=>S.getD j fall) len (run x pre) ack (.busy 3 (.back 0)) .idle ∧
        Current hp base (fun j=>S.getD j fall) len (step (run x pre) ack) .idle := by
  let addr := fun j=>S.getD j fall
  induction w generalizing x a with
  | nil =>
    cases G
    exact .inl E
  | cons e w ih =>
    cases G with
    | next cur event tail =>
      have Ly : ∀ p j,Layout B base j=Layout B (run (step x e) p) j :=
        fun p j=>layout (e::p) j
      have now : ∀ j, Layout B base j=Layout B x j := layout []
      rcases ih Ly tail E with inheritance|⟨pre,ack,rest,eq,G,Ev,after⟩
      · obtain ⟨mode,H⟩ := inheritance
        cases mode
        rcases step_ready4 hp C sep now cur event H with R|R
        · exact .inl R
        · cases R
          exact .inr ⟨[],e,w,rfl,.endpoint cur,event,at_start hp tail⟩
      · exact .inr ⟨e::pre,ack,rest,congrArg (List.cons e) eq,.next cur event G,Ev,after⟩

private theorem busy_consume {base x : X} {addr : Nat→Pos n} {len op : Nat}
    {z d : Cursor} {tour : List (Fin n)}
    (busy : BusyOnly hp base addr len op x z tour d)
    (ack : Fin n)
    (event : Event hp addr len (run x tour) ack (.busy op d) .idle)
    (after : Current hp base addr len (step (run x tour) ack) .idle) :
    GeneratedOwner hp base addr len x (.busy op z) (tour++[ack]) .idle := by
  induction busy with
  | nil cur => exact .next cur event (.endpoint after)
  | cons I E _ ih => exact .next I E (ih event after)

/-- Between one actual ADMIT launch and the next ready ADMIT point,
a new PACE launch and its matching consume genuinely occur in order.
The returned PACE interval starts after that new launch and includes
its matching acknowledgement; it is not an inherited tour. -/
theorem between_admits {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (layout : ∀ p j,Layout B base j=Layout B (run x p) j)
    {w : List (Fin n)}
    (G : GeneratedOwner hp base (fun j=>S.getD j fall) len x (.busy admit (.out 0)) w .idle)
    (E : Ready4 (fun j=>S.getD j fall) (run x w) .idle) :
    ∃ lead issue tour ack rest,
      w=lead++issue::(tour++ack::rest) ∧
      let y := run x lead
      issue=RearTrace.predecessor (S.getD 0 fall).1 ∧
      Launch (y (S.getD 0 fall).1).long ((step y issue) (S.getD 0 fall).1).long ∧
      (ctrlOp.read (y (S.getD 0 fall).1).long).toNat=3 ∧
      GeneratedOwner hp base (fun j=>S.getD j fall) len (step y issue)
        (.busy 3 (.out 0)) (tour++[ack]) .idle := by
  let addr := fun j=>S.getD j fall
  rcases ready4_origin hp C sep layout G E with old|⟨pre,ack,rest,W,T,H,after⟩
  · cases old.1
  · rcases extract hp T with F|⟨z,eq,_⟩
    · obtain ⟨lead,tour,issue,P,legal,L,op,Bs⟩ := F
      have cut : run x pre=run (step (run x lead) issue) tour := by
        rw [P,BStarResetSchedule.run_append]
        rfl
      rw [cut] at H after
      refine ⟨lead,issue,tour,ack,rest,?_,legal,L,op,busy_consume hp Bs ack H after⟩
      rw [W,P,List.append_assoc]
      rfl
    · cases eq

#print axioms ready4_origin
#print axioms between_admits
end L4.BStarRepeatedPace

