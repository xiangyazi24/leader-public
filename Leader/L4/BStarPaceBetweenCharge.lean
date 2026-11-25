import Leader.L4.BStarRepeatedPace
import Leader.L4.BStarPaceSteeredCharge

namespace L4.BStarPaceBetweenCharge
open AllSizeProtocol BStarTrace BStarLongClaims BStarLongWork BStarLongToken
open BStarH6WordChart BStarAcquireVisitOrder BStarAcquireAnchors BStarAcquireLiteralChain
open BStarLongFixedRouting BStarResetMarkAdapter BStarResetChartTouch
open BStarSeparatingRail BStarGeneratedOwner BStarLongCommand BStarRepeatedPace
open BStarPaceLedger BStarPaceCount BStarPaceChartLedger BStarPaceSteeredCharge

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step (n:=n) B
local notation "run" => BStarResetSchedule.run step

/-- The actual raw interval after one own ADMIT launch and before the
next on this chart must pay one complete PACE traversal. A launch or
partial PACE carried in from before the observed first ADMIT is not
charged. No assumption about the decision on either ADMIT is needed. -/
theorem actual_between_charge {base initial : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (layout : ∀ p j,Layout B base j=Layout B (run initial p) j)
    (a w : List (Fin n))
    (G : GeneratedOwner hp base (fun j=>S.getD j fall) len
      (run initial a) (.busy admit (.out 0)) w .idle)
    (E : Ready4 (fun j=>S.getD j fall) (run initial (a++w)) .idle) :
    len≤charges (rawCharge hp base initial (fun j=>S.getD j fall) len) a w := by
  let x := run initial a
  let f := rawCharge hp base initial (fun j=>S.getD j fall) len
  have ly p j : Layout B base j=Layout B (run x p) j := by
    dsimp [x]
    rw [←BStarResetSchedule.run_append]
    exact layout (a++p) j
  have R : Ready4 (fun j=>S.getD j fall) (run x w) .idle := by
    dsimp [x]
    rwa [←BStarResetSchedule.run_append]
  obtain ⟨lead,issue,tour,ack,rest,same,_,_,_,tourAck⟩ :=
    between_admits hp C sep ly G R
  have prep : run initial (a++(lead++[issue]))=step (run x lead) issue := by
    rw [BStarResetSchedule.run_append,BStarResetSchedule.run_append]
    rfl
  have literal : GeneratedOwner hp base (fun j=>S.getD j fall) len
      (run initial (a++(lead++[issue]))) (.busy 3 (.out 0)) (tour++[ack]) .idle := by
    rw [prep]
    exact tourAck
  have charged : len≤charges f (a++(lead++[issue])) (tour++[ack]) :=
    actual_complete_pace_charge hp C sep _ _ literal
  have W : w=((lead++[issue])++(tour++[ack]))++rest := by
    rw [same]
    simp only [List.append_assoc,List.cons_append,List.nil_append]
  change len≤charges f a w
  rw [W,charges_append,charges_append]
  omega

/-- A list of disjoint physical intervals between one ADMIT issue and
the next ready ISSUE4 cut. The initial opportunity is not in this count. -/
inductive PaidIntervals (base initial : X) (addr : Nat→Pos n) (len : Nat) :
    List (Fin n)→List (Fin n)→Nat→Prop
  | nil (a w) : PaidIntervals base initial addr len a w 0
  | cons {a gap tour rest k}
      (trail : GeneratedOwner hp base addr len (run initial (a++gap))
        (.busy admit (.out 0)) tour .idle)
      (ready : Ready4 addr (run initial ((a++gap)++tour)) .idle)
      (tail : PaidIntervals base initial addr len ((a++gap)++tour) rest k) :
      PaidIntervals base initial addr len a ((gap++tour)++rest) (k+1)

theorem intervals_charge {base initial : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (layout : ∀ p j,Layout B base j=Layout B (run initial p) j)
    {a w : List (Fin n)} {k : Nat}
    (intervals : PaidIntervals hp base initial (fun j=>S.getD j fall) len a w k) :
    len*k≤charges (rawCharge hp base initial (fun j=>S.getD j fall) len) a w := by
  apply total_completed
  induction intervals with
  | nil a w => exact .zero a w
  | cons trail ready _ ih =>
    exact .more (actual_between_charge hp C sep layout _ _ trail ready) ih

/-- Execute candidate labels by the predictable played-label map. The
unmodified candidate prefix, not the already redirected trace, is
presented to the next steering decision. -/
def playedWord {n : Nat} (redirect : List (Fin n)→Fin n→Option (Fin n)) :
    List (Fin n)→List (Fin n)→List (Fin n)
  | _,[] => []
  | a,e::w => (redirect a e).getD e :: playedWord redirect (a++[e]) w

/-- The expected-count candidate charge and the literal played trace
charge are exactly the same, provided the prefix map is a causal replay. -/
theorem charges_candidate_eq (base initial : X) (addr : Nat→Pos n) (len : Nat)
    (played : List (Fin n)→List (Fin n)) (redirect : List (Fin n)→Fin n→Option (Fin n))
    (compat : ∀ a e,played (a++[e])=played a++[(redirect a e).getD e])
    (a w : List (Fin n)) :
    charges (candidateCharge hp base initial addr len played redirect) a w =
      charges (rawCharge hp base initial addr len) (played a) (playedWord redirect a w) := by
  induction w generalizing a with
  | nil => rfl
  | cons e w ih =>
    rw [charges,playedWord,charges,ih,compat]
    rfl

/-- The disjoint literal intervals on the played raw word are paid by
the candidate-word charge used in the two-label probability bound. -/
theorem intervals_candidate_charge {base initial : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (layout : ∀ p j,Layout B base j=Layout B (run initial p) j)
    (played : List (Fin n)→List (Fin n)) (redirect : List (Fin n)→Fin n→Option (Fin n))
    (compat : ∀ a e,played (a++[e])=played a++[(redirect a e).getD e])
    {a w : List (Fin n)} {k : Nat}
    (intervals : PaidIntervals hp base initial (fun j=>S.getD j fall) len
      (played a) (playedWord redirect a w) k) :
    len*k≤charges (candidateCharge hp base initial (fun j=>S.getD j fall) len played redirect) a w := by
  rw [charges_candidate_eq hp base initial _ _ played redirect compat]
  exact intervals_charge hp C sep layout intervals

#print axioms intervals_charge
#print axioms charges_candidate_eq
#print axioms intervals_candidate_charge
#print axioms actual_between_charge
end L4.BStarPaceBetweenCharge

