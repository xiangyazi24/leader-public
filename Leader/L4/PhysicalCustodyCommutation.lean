import Leader.L4.PhysicalCustody

namespace L4.PhysicalCustody
open AllSizeProtocol BStarTrace

def DisjointMarks {n : Nat} (a b : Fin n) : Prop :=
  a≠b ∧ a≠rightNeighbor b ∧ rightNeighbor a≠b ∧ rightNeighbor a≠rightNeighbor b

theorem rawNext_disjoint_commute {s n : Nat} (x : Raw s n) (a b : Fin n)
    (H : DisjointMarks a b) :
    rawNext s (rawNext s x a) b=rawNext s (rawNext s x b) a := by
  obtain ⟨h₁,h₂,h₃,h₄⟩ := H
  funext i
  unfold rawNext AllSizeS1Geometry.step
  simp only [if_neg h₁,if_neg h₂,if_neg h₃,if_neg h₄,if_neg (Ne.symm h₁),
    if_neg (Ne.symm h₂),if_neg (Ne.symm h₃),if_neg (Ne.symm h₄)]
  by_cases E : i=a
  · subst i; simp [h₁,h₂]
  by_cases E' : i=rightNeighbor a
  · subst i; simp [E,h₃,h₄]
  by_cases F : i=b
  · subst i; simp [E,E']
  by_cases F' : i=rightNeighbor b
  · subst i; simp [E,E',F]
  simp [E,E',F,F']

inductive Commuted {n : Nat} : List (Fin n) → List (Fin n) → Prop where
  | refl (w) : Commuted w w
  | swap (u v : List (Fin n)) (a b : Fin n) (H : DisjointMarks a b) :
      Commuted (u++a::b::v) (u++b::a::v)
  | trans {u v w} : Commuted u v → Commuted v w → Commuted u w

theorem rawRun_of_commuted {s n : Nat} (x : Raw s n) {u v : List (Fin n)}
    (H : Commuted u v) : rawRun x u=rawRun x v := by
  induction H with
  | refl => rfl
  | trans _ _ I J => exact I.trans J
  | swap u v a b H =>
    unfold rawRun
    rw [BStarResetSchedule.run_append,BStarResetSchedule.run_append]
    change rawRun (rawNext s (rawNext s (rawRun x u) a) b) v=
      rawRun (rawNext s (rawNext s (rawRun x u) b) a) v
    exact congrArg (fun z=>rawRun z v) (rawNext_disjoint_commute (rawRun x u) a b H)

theorem commute_prefix {n : Nat} (p : List (Fin n)) {u v : List (Fin n)}
    (H : Commuted u v) : Commuted (p++u) (p++v) := by
  induction H with
  | refl => exact .refl _
  | trans _ _ A B => exact .trans A B
  | swap u v a b H =>
    simpa only [List.append_assoc] using Commuted.swap (p++u) v a b H

theorem bubble_door {n : Nat} (w v : List (Fin n)) (d : Fin n)
    (H : ∀ e∈w,DisjointMarks e d) :
    Commuted (w++d::v) (d::(w++v)) := by
  induction w with
  | nil => exact .refl _
  | cons a w ih =>
    have P := commute_prefix [a] (ih (fun e mem=>H e (List.mem_cons_of_mem _ mem)))
    exact Commuted.trans P (.swap [] (w++v) a d (H a List.mem_cons_self))

theorem adjacent_door_replay {s n : Nat} (x : Raw s n)
    (p w v : List (Fin n)) (d : Fin n)
    (H : ∀ e∈w,DisjointMarks e d) :
    rawRun x (p++d::(w++d::v))=rawRun x (p++d::d::(w++v)) := by
  apply rawRun_of_commuted
  simpa only [List.append_assoc,List.singleton_append] using
    commute_prefix (p++[d]) (bubble_door w v d H)

end L4.PhysicalCustody
