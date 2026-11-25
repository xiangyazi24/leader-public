import Leader.L4.BStarNativePortGeometry

/-! Literal publication histories on the raw ordered-mark tape. -/

namespace L4.BStarRawPublicationHistory

open AllSizeProtocol BStarGrantWriterHistory BStarNativePortGeometry BStarTrace BStarLongWork
open Classical

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0 < p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step B
local notation "run" => BStarResetSchedule.run step

/-- Retain the initiator of every actual native publication, including
a successful activation that leaves the selected decoded record unchanged. -/
noncomputable def publicationSites (x : X) : List (Fin n) → List (Fin n)
  | [] => []
  | e :: w =>
    let tail := publicationSites (step x e) w
    if NoPublication hp x e e then tail else e :: tail

/-- A publication witnessed by the pre-mark state on the original word. -/
def Publishes (x : X) (i : Fin n) (w : List (Fin n)) : Prop :=
  ∃ pre post : List (Fin n), w = pre ++ i :: post ∧
    ¬ NoPublication hp (run x pre) i i

theorem publicationSites_append (x : X) (u v : List (Fin n)) :
    publicationSites hp x (u ++ v) =
      publicationSites hp x u ++ publicationSites hp (run x u) v := by
  induction u generalizing x with
  | nil => rfl
  | cons e u ih =>
    simp only [List.cons_append, publicationSites, BStarResetSchedule.run]
    rw [ih]
    split <;> rfl

theorem publishes_cons (x : X) (i e : Fin n) (w : List (Fin n)) :
    Publishes hp x i (e::w) ↔ (e=i ∧ ¬ NoPublication hp x i i) ∨
      Publishes hp (step x e) i w := by
  constructor
  · rintro ⟨pre, post, eq, hit⟩
    cases pre with
    | nil =>
      exact .inl ⟨(List.cons.inj eq).1,hit⟩
    | cons a pre =>
      have E := List.cons.inj eq
      exact .inr ⟨pre,post,E.2,E.1.symm ▸ hit⟩
  · rintro (⟨rfl,hit⟩ | ⟨pre,post,eq,hit⟩)
    · exact ⟨[],w,rfl,hit⟩
    · exact ⟨e::pre,post,congrArg (List.cons e) eq,hit⟩

theorem mem_publicationSites_iff (x : X) (i : Fin n) (w : List (Fin n)) :
    i ∈ publicationSites hp x w ↔ Publishes hp x i w := by
  induction w generalizing x with
  | nil => simp [Publishes, publicationSites]
  | cons e w ih =>
    rw [publishes_cons, publicationSites]
    by_cases h : NoPublication hp x e e
    · rw [if_pos h, ih]
      exact ⟨Or.inr,fun H => H.elim (fun ⟨E,F⟩ => False.elim (F (E ▸ h))) id⟩
    · rw [if_neg h, List.mem_cons, ih]
      constructor
      · rintro (rfl | H)
        · exact .inl ⟨rfl,h⟩
        · exact .inr H
      · rintro (⟨E,_⟩ | H)
        · exact .inl E.symm
        · exact .inr H

theorem publishes_append (x : X) (i : Fin n) (u v : List (Fin n)) :
    Publishes hp x i (u++v) ↔ Publishes hp x i u ∨ Publishes hp (run x u) i v := by
  simp only [← mem_publicationSites_iff, publicationSites_append, List.mem_append]

/-- Inclusive wait; an empty prefix never witnesses service. If no
success occurs, all the available marks are charged. -/
noncomputable def publicationWait (x : X) (i : Fin n) : List (Fin n) → Nat
  | [] => 0
  | e :: w =>
    if e = i ∧ ¬ NoPublication hp x i i then 1
    else 1 + publicationWait (step x e) i w

theorem publicationWait_le_length (x : X) (i : Fin n) (w : List (Fin n)) :
    publicationWait hp x i w ≤ w.length := by
  induction w generalizing x with
  | nil => exact Nat.le_refl _
  | cons e w ih =>
    rw [publicationWait]
    split
    · simp
    · simpa only [List.length_cons, Nat.add_comm 1] using Nat.succ_le_succ (ih (step x e))

theorem publicationWait_no_success (x : X) (i : Fin n) (w : List (Fin n))
    (quiet : ¬ Publishes hp x i w) : publicationWait hp x i w = w.length := by
  induction w generalizing x with
  | nil => rfl
  | cons e w ih =>
    have H := (publishes_cons hp x i e w)
    rw [publicationWait, if_neg (fun F => quiet (H.2 (.inl F))),
      ih _ (fun F => quiet (H.2 (.inr F)))]
    exact Nat.add_comm _ _

/-- At every strict prefix budget, the finite wait detects service
on that prefix. The strict budget condition is essential because
an unsuccessful full word and a success at its last mark have equal wait. -/
theorem take_publishes_iff_wait_le (x : X) (i : Fin n) (w : List (Fin n))
    (k : Nat) (hk : k < w.length) :
    Publishes hp x i (w.take k) ↔ publicationWait hp x i w ≤ k := by
  induction w generalizing x k with
  | nil => simp at hk
  | cons e w ih =>
    cases k with
    | zero =>
      rw [List.take_zero]
      constructor
      · intro H
        simp [Publishes] at H
      · intro H
        rw [publicationWait] at H
        split at H <;> omega
    | succ k =>
      rw [List.take_succ_cons, publishes_cons, publicationWait]
      by_cases h : e = i ∧ ¬ NoPublication hp x i i
      · simp [h]
      · rw [if_neg h, or_iff_right h]
        have H := ih (step x e) k (by simpa using hk)
        rw [H]
        omega

/-- The first successful mark has a genuine pre-state and consumes a
positive number of raw letters, even if the decoded state stutters. -/
theorem publishes_first_split (x : X) (i : Fin n) (w : List (Fin n))
    (h : Publishes hp x i w) :
    ∃ pre post, w = pre ++ i :: post ∧ ¬ Publishes hp x i pre ∧
      ¬ NoPublication hp (run x pre) i i ∧ publicationWait hp x i w = pre.length+1 := by
  induction w generalizing x with
  | nil => simp [Publishes] at h
  | cons e w ih =>
    by_cases now : e = i ∧ ¬ NoPublication hp x i i
    · obtain ⟨rfl, now⟩ := now
      exact ⟨[],w,rfl,by simp [Publishes],now,by simp [publicationWait,now]⟩
    · obtain ⟨pre,post,eq,quiet,hit,delay⟩ :=
        ih (step x e) (((publishes_cons hp x i e w).1 h).resolve_left now)
      refine ⟨e::pre,post,congrArg (List.cons e) eq,?_,hit,?_⟩
      · intro H
        exact quiet (((publishes_cons hp x i e pre).1 H).resolve_left now)
      · rw [publicationWait, if_neg now, delay]
        simp only [List.length_cons]
        omega

#print axioms publishes_first_split

#print axioms mem_publicationSites_iff
#print axioms publishes_append
#print axioms take_publishes_iff_wait_le

end L4.BStarRawPublicationHistory
