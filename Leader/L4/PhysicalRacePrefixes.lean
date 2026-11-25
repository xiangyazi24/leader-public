import Leader.L4.PhysicalDoorRace
import Leader.L4.PhysicalSeparatorGap
import Leader.L4.AdaptiveDoorCredit

namespace L4.PhysicalRacePrefixes
open PhysicalCustody PhysicalDoorRace ProjectedDoor BStarTrace

/-- Retain the exact gaps and unused suffix of a successful incident
race. The constructor forces every skipped label to be disjoint from
both endpoints, not merely different from the door label. -/
inductive AcceptedPrefix {n : Nat} (d : Fin n) : Nat → List (Fin n) → Prop
  | done (tail : List (Fin n)) : AcceptedPrefix d 0 tail
  | door {k : Nat} {w : List (Fin n)} (H : AcceptedPrefix d k w) :
      AcceptedPrefix d (k+1) (d::w)
  | disjoint {k : Nat} {w : List (Fin n)} {e : Fin n}
      (D : DisjointMarks e d) (H : AcceptedPrefix d (k+1) w) :
      AcceptedPrefix d (k+1) (e::w)

theorem disjoint_symm {n : Nat} {d e : Fin n} (D : DisjointMarks d e) :
    DisjointMarks e d := ⟨Ne.symm D.1,Ne.symm D.2.2.1,Ne.symm D.2.1,Ne.symm D.2.2.2⟩

theorem accepted_iff {n : Nat} (d : Fin n) (k : Nat) (w : List (Fin n)) :
    accepted d k w=1 ↔ AcceptedPrefix d k w := by
  constructor
  · induction w generalizing k with
    | nil =>
      cases k with
      | zero => exact fun _=>.done []
      | succ k => simp [accepted]
    | cons e w ih =>
      cases k with
      | zero => exact fun _=>.done _
      | succ k =>
        intro H
        by_cases D : DisjointMarks d e
        · apply AcceptedPrefix.disjoint (disjoint_symm D)
          exact ih _ (by simpa [accepted,D] using H)
        · by_cases E : e=d
          · subst e
            exact .door (ih _ (by simpa [accepted,D] using H))
          · simp [accepted,D,E] at H
  · intro H
    induction H with
    | done tail => cases tail <;> rfl
    | door H ih => simpa [accepted,show ¬DisjointMarks d d from fun D=>D.1 rfl] using ih
    | disjoint D H ih => simpa [accepted,disjoint_symm D] using ih

theorem one_gap {n : Nat} {d : Fin n} {w : List (Fin n)}
    (H : AcceptedPrefix d 1 w) :
    ∃ gap tail,w=gap++d::tail ∧ ∀ e∈gap,DisjointMarks e d := by
  induction w with
  | nil => cases H
  | cons e w ih =>
    cases H with
    | door => exact ⟨[],w,rfl,by simp⟩
    | disjoint D H =>
      obtain ⟨g,t,rfl,K⟩ := ih H
      exact ⟨e::g,t,rfl,fun a A=>(List.mem_cons.mp A).elim (fun T=>T ▸ D) (K a)⟩

theorem two_gaps {n : Nat} {d : Fin n} {w : List (Fin n)}
    (H : AcceptedPrefix d 2 w) :
    ∃ g₁ g₂ tail,w=g₁++d::(g₂++d::tail) ∧
      (∀ e∈g₁,DisjointMarks e d) ∧ (∀ e∈g₂,DisjointMarks e d) := by
  induction w with
  | nil => cases H
  | cons e w ih =>
    cases H with
    | door H =>
      obtain ⟨g,t,rfl,K⟩ := one_gap H
      exact ⟨[],g,t,rfl,by simp,K⟩
    | disjoint D H =>
      obtain ⟨g,h,t,rfl,K,L⟩ := ih H
      exact ⟨e::g,h,t,rfl,fun a A=>(List.mem_cons.mp A).elim (fun T=>T ▸ D) (K a),L⟩

/-- The two incident competitors are exactly the neighboring marks. -/
theorem disjoint_iff_not_incident {n : Nat} (d e : Fin n) :
    DisjointMarks e d ↔ e≠d ∧ e≠RearTrace.predecessor d ∧ e≠rightNeighbor d := by
  constructor
  · rintro ⟨a,b,c,_⟩
    exact ⟨a,fun E=>c (by rw [E,RearTrace.right_predecessor]),b⟩
  · rintro ⟨a,b,c⟩
    refine ⟨a,c,?_,?_⟩
    · intro E
      exact b (by rw [←E,RearTrace.predecessor_right])
    · intro E
      apply a
      simpa only [RearTrace.predecessor_right] using congrArg RearTrace.predecessor E

/-- A physical door race obeys the local six-race score inequality
provided the winner advances the credit and disjoint marks retain it. -/
theorem literal_door_local_law {α : Type} {n : Nat} (hn : 4≤n)
    (next : α→Fin n→α) (score : α→Nat) (x : α) (d : Fin n)
    (winner : 3*score x≤score (next x d))
    (disjoint : ∀ e,DisjointMarks e d→score x≤score (next x e)) :
    AdaptiveDoorCredit.LocalLaw next score x := by
  obtain ⟨a,b,c⟩ : RearTrace.predecessor d≠d ∧
      RearTrace.predecessor d≠rightNeighbor d ∧ d≠rightNeighbor d := by
    simpa only [RearTrace.right_predecessor] using barrierBondsDistinct hn (RearTrace.predecessor d)
  exact .inr ⟨d,RearTrace.predecessor d,rightNeighbor d,Ne.symm a,c,b,winner,
    fun e E A B=>disjoint e ((disjoint_iff_not_incident d e).2 ⟨E,A,B⟩)⟩

end L4.PhysicalRacePrefixes
