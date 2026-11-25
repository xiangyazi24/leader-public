import Leader.L4.PhysicalCustody

namespace L4.Height.RawServiceCore
open PhysicalCustody BStarGrantWriterHistory

/-- The old initiator executes an authorized COMMIT at a positive prefix. -/
def publishes {s n : Nat} (x : Raw s n) (i : Fin n) (w : List (Fin n)) : Prop :=
  ∃ pre post : List (Fin n), w = pre ++ i :: post ∧
    ¬ NoPublication (show 0 < 2 by decide) (rawRun x pre) i i

theorem publishes_nil {s n : Nat} (x : Raw s n) (i : Fin n) :
    ¬ publishes x i [] := by
  rintro ⟨pre, post, h, _⟩
  have := congrArg List.length h
  simp at this

theorem publishes_cons {s n : Nat} (x : Raw s n) (i e : Fin n)
    (w : List (Fin n)) : publishes x i (e :: w) ↔
    (e = i ∧ ¬ NoPublication (show 0 < 2 by decide) x i i) ∨
    publishes (rawNext s x e) i w := by
  constructor
  · rintro ⟨pre, post, h, p⟩
    cases pre with
    | nil => exact Or.inl ⟨(List.cons.inj h).1, p⟩
    | cons a u =>
      obtain ⟨rfl, q⟩ := List.cons.inj h
      exact Or.inr ⟨u, post, q, p⟩
  · rintro (⟨rfl, p⟩ | ⟨pre, post, h, p⟩)
    · exact ⟨[], w, rfl, p⟩
    · exact ⟨e :: pre, post, congrArg (e :: ·) h, p⟩

theorem publishes_append_one {s n : Nat} (x : Raw s n) (i e : Fin n)
    (v : List (Fin n)) : publishes x i (v ++ [e]) ↔ publishes x i v ∨
    (e = i ∧ ¬ NoPublication (show 0 < 2 by decide) (rawRun x v) i i) := by
  induction v generalizing x with
  | nil => simp [publishes_cons, publishes_nil, rawRun, BStarResetSchedule.run]
  | cons a v ih =>
    simp only [List.cons_append, publishes_cons, ih, or_assoc, rawRun, BStarResetSchedule.run]

end L4.Height.RawServiceCore
