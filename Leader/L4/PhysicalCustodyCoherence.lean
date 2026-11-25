import Leader.L4.PhysicalCustody

namespace L4.PhysicalCustody
open AllSizeProtocol BStarTrace BStarLongWork
local notation "hp" => (show 0<2 by decide)

def GrantClean {s n : Nat} (x : Raw s n) (i : Fin n) : Prop :=
  BStarLongGrant.conflict (BStarGrantReaderHistory.ports x i)=false

theorem grant_site_next {s n : Nat} (x : Raw s n) (e i : Fin n)
    (sep : e≠rightNeighbor e)
    (H : GrantClean x i ∨ i=e ∨ i=rightNeighbor e) : GrantClean (rawNext s x e) i := by
  by_cases A : i=e
  · subst i
    exact BStarGrantReaderHistory.mark_coherent hp x e sep .left
  by_cases B : i=rightNeighbor e
  · subst i
    exact BStarGrantReaderHistory.mark_coherent hp x e sep .right
  have eq : rawNext s x e i=x i := by
    unfold rawNext AllSizeS1Geometry.step
    simp [A,B]
  unfold GrantClean BStarGrantReaderHistory.ports at *
  rw [eq]
  exact H.resolve_right (by simp [A,B])

theorem grant_coherent_closed {s n : Nat} (x : Raw s n) (e : Fin n)
    (sep : e≠rightNeighbor e) (H : ∀ i, GrantClean x i) :
    ∀ i, GrantClean (rawNext s x e) i :=
  fun i => grant_site_next x e i sep (.inl (H i))

theorem grant_site_after_word {s n : Nat} (x : Raw s n) (w : List (Fin n))
    (sep : ∀ e : Fin n,e≠rightNeighbor e) (i : Fin n)
    (H : GrantClean x i ∨ ∃ e∈w,i=e ∨ i=rightNeighbor e) :
    GrantClean (rawRun x w) i := by
  induction w generalizing x with
  | nil =>
    rcases H with A|⟨e,he,_⟩
    · exact A
    · cases he
  | cons e w ih =>
    apply ih (rawNext s x e)
    rcases H with A|⟨f,hf,h⟩
    · exact .inl (grant_site_next x e i (sep e) (.inl A))
    · rcases List.mem_cons.mp hf with rfl|hf
      · exact .inl (grant_site_next x f i (sep f) (.inr h))
      · exact .inr ⟨f,hf,h⟩

theorem grant_coherent_after_cover {s n : Nat} (x : Raw s n) (w : List (Fin n))
    (sep : ∀ e : Fin n,e≠rightNeighbor e) (full : ∀ e,e∈w) :
    ∀ i, GrantClean (rawRun x w) i :=
  fun i => grant_site_after_word x w sep i (.inr ⟨i,full i,.inl rfl⟩)

end L4.PhysicalCustody
