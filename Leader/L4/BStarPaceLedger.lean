import Leader.L4.BStarGeneratedOwner
import Leader.L4.BStarPaceCount

namespace L4.BStarPaceLedger
open BStarSeparatingRail BStarResetSchedule BStarPaceCount

def outwardCredit (len : Nat) : Cursor → Nat
  | .out k => k
  | .back _ => len

def forwardΔ : Cursor → Cursor → Nat
  | .out k, .out j => if j=k+1 then 1 else 0
  | _, _ => 0

theorem telescope {len : Nat} {c d : Cursor} (a : Advance len c d) :
    outwardCredit len c+forwardΔ c d=outwardCredit len d := by
  cases a with
  | stay c => cases c <;> simp [outwardCredit,forwardΔ]
  | forward k => simp [outwardCredit,forwardΔ]
  | turn => rfl
  | reverse k => rfl

/-- On the literal finite marked word, any predicate recognizing each forward
advance must charge at least the net outward progress. The predicate sees
the entire old prefix; turning and returning never create forward credit. -/
theorem seen_charge {X : Type} {n : Nat} {step : X → Fin n → X} {track : X → Track}
    {tag : Tag} {len : Nat} {x : X} {u : List (Fin n)} {c d : Cursor}
    (trace : Seen step track tag len x c u d)
    (charge : List (Fin n) → Fin n → Nat) (a : List (Fin n))
    (witness : ∀ (p v : List (Fin n)) (e : Fin n) (s t : Cursor),
      u=p++e::v →
      Seen step track tag len x c p s →
      Seen step track tag len (BStarResetSchedule.run step x p) s [e] t →
      forwardΔ s t ≤ charge (a++p) e) :
    outwardCredit len d ≤ outwardCredit len c+charges charge a u := by
  induction trace generalizing a with
  | nil => simp [charges]
  | @cons y e w c d f L M A G next ih =>
    have H := witness [] w e c d rfl (.nil _ _)
      (.cons L M A G (.nil _ _))
    simp only [List.append_nil] at H
    have T := ih (a++[e]) (fun p v m b z E pre one => by
      have J := witness (e::p) v m b z (congrArg (List.cons e) E)
        (.cons L M A G pre) one
      simpa only [List.append_assoc,List.singleton_append] using J)
    have D := telescope A
    simp only [charges]
    omega

/-- The completed round needs len distinct outbound marks on its own word,
before any later launch or any exclusion accounting. -/
theorem complete_pace_charge {X : Type} {n : Nat} {step : X → Fin n → X}
    {track : X → Track} {tag : Tag} {len : Nat} {x : X} {u : List (Fin n)}
    (trace : Seen step track tag len x (.out 0) u (.back 0))
    (charge : List (Fin n) → Fin n → Nat) (a : List (Fin n))
    (witness : ∀ (p v : List (Fin n)) (e : Fin n) (s t : Cursor),
      u=p++e::v →
      Seen step track tag len x (.out 0) p s →
      Seen step track tag len (BStarResetSchedule.run step x p) s [e] t →
      forwardΔ s t ≤ charge (a++p) e) :
    len ≤ charges charge a u := by
  simpa [outwardCredit] using seen_charge trace charge a witness

theorem charges_append {n : Nat} (charge : List (Fin n) → Fin n → Nat)
    (a u v : List (Fin n)) :
    charges charge a (u++v)=charges charge a u+charges charge (a++u) v := by
  induction u generalizing a with
  | nil => simp [charges]
  | cons e u ih =>
    rw [List.cons_append,charges,charges,ih]
    simp only [List.append_assoc,List.singleton_append,Nat.add_assoc]

/-- A history contains k completed disjoint charged PACE intervals.
Gaps can contain arbitrary marks, but no mark belongs to two intervals. -/
inductive Completed {n : Nat} (charge : List (Fin n) → Fin n → Nat) (width : Nat) :
    List (Fin n) → List (Fin n) → Nat → Prop
  | zero (a v) : Completed charge width a v 0
  | more {a gap run tail k}
      (earned : width ≤ charges charge (a++gap) run)
      (rest : Completed charge width ((a++gap)++run) tail k) :
      Completed charge width a ((gap++run)++tail) (k+1)

theorem total_completed {n width k : Nat} {charge : List (Fin n) → Fin n → Nat}
    {a u : List (Fin n)} (h : Completed charge width a u k) :
    width*k ≤ charges charge a u := by
  induction h with
  | zero => simp
  | @more a gap run tail k earned rest ih =>
    rw [charges_append charge a (gap++run),charges_append charge a gap,Nat.mul_add,Nat.mul_one]
    rw [List.append_assoc] at ih
    omega

section Physical
open AllSizeProtocol BStarTrace BStarLongWork BStarAcquireLiteralChain
open BStarGeneratedOwner BStarAcquireAnchors
open BStarAcquireVisitOrder BStarResetMarkAdapter BStarSeparatorControl

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step B

/-- If the same generated owner eventually consumes a busy command, the
entire actual outward/return trace through the first source arrival is a
prefix of the very same word. No fairness or supplied suffix is assumed. -/
theorem consumed_round_prefix {base x : X} {addr : Nat → Pos n} {len op : Nat}
    {u : List (Fin n)} {z : Cursor}
    (G : GeneratedOwner hp base addr len x (.busy op z) u .idle) :
    ∃ pre rest, u=pre++rest ∧ Seen step (project addr) anyTag len x z pre (.back 0) := by
  induction u generalizing x z with
  | nil =>
    cases G
  | cons e w ih =>
    by_cases here : z=.back 0
    · subst z
      exact ⟨[],e::w,rfl,.nil _ _⟩
    · cases G with
      | next _ E tail =>
        cases E with
        | transit op z d live one =>
          obtain ⟨pre,rest,eq,T⟩ := ih tail
          exact ⟨e::pre,rest,congrArg (List.cons e) eq,one.append T⟩
        | arrived_hold _ _ => exact (here rfl).elim
        | consume _ _ _ => exact (here rfl).elim

end Physical

end L4.BStarPaceLedger

