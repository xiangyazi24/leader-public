import Leader.L4.Statement

/-! H5/D₁₂ product handoff: the product and public provider see the
same raw labels. The relevant domain is forward closed, not reset or
conditioned at subsequent marks. -/
namespace L4.RootedProduct
open Classical

/-- Ordered common marks on a possibly enriched product state. -/
def runProduct {α : Type} {n : Nat} (next : α → Fin n → α)
    (x : α) : List (Fin n) → α
  | [] => x
  | e::w => runProduct next (next x e) w

/-- Semantic product safety: the same physical leader under every
continuation, measured by the product's displayed bit. -/
def ProductSafe {α : Type} {n : Nat} (next : α → Fin n → α)
    (display : α → Fin n → Bool) (x : α) : Prop :=
  ∃ i : Fin n, ∀ (w : List (Fin n)) (j : Fin n),
    display (runProduct next x w) j=true ↔ j=i

/-- Single-mark commutation lifts to every continuation on a closed
domain, without requiring commutation on the discarded pre-cut states. -/
theorem run_commutes {α β : Type} {n : Nat} (next : α → Fin n → α)
    (other : β → Fin n → β) (proj : α → β) (D : α → Prop)
    (closed : ∀ x e, D x → D (next x e))
    (comm : ∀ x e, D x → proj (next x e)=other (proj x) e)
    (w : List (Fin n)) (x : α) (hx : D x) :
    D (runProduct next x w) ∧
      proj (runProduct next x w)=runProduct other (proj x) w := by
  induction w generalizing x with
  | nil => exact ⟨hx,rfl⟩
  | cons e w ih =>
    obtain ⟨hc,hp⟩ := ih (next x e) (closed x e hx)
    exact ⟨hc,hp.trans (congrArg (fun y => runProduct other y w) (comm x e hx))⟩

/-- M3. When product displays the public leader bit, semantic
safe-one-leader is exactly the pullback on the closed handoff domain. -/
theorem safe_of_proj {α : Type} {p c n : Nat} (next : α → Fin n → α)
    (proj : α → Config p c n) (display : α → Fin n → Bool) (D : α → Prop)
    (closed : ∀ x e, D x → D (next x e))
    (comm : ∀ x e, D x → proj (next x e)=step (proj x) e)
    (bits : ∀ x j, D x → display x j=(proj x j).leader)
    (x : α) (hx : D x) :
    ProductSafe next display x ↔ SafeOneLeader (proj x) := by
  have publicRun (y : Config p c n) (w : List (Fin n)) :
      runProduct step y w=run y w := by
    induction w generalizing y with
    | nil => rfl
    | cons e w ih => exact ih (step y e)
  have bit (w : List (Fin n)) (j : Fin n) :
      display (runProduct next x w) j=(run (proj x) w j).leader := by
    obtain ⟨hb,hp⟩ := run_commutes next step proj D closed comm w x hx
    rw [bits _ j hb,hp,publicRun]
  constructor <;> rintro ⟨i,hi⟩ <;> refine ⟨i,fun w j => ?_⟩
  · rw [←bit]; exact hi w j
  · rw [bit]; exact hi w j

/-- Exact integer numerator, using the same n^t denominator for both
systems. This compares first hits, not only endpoints. -/
theorem iidHitCost_eq_of_proj {α β : Type} {n : Nat} (next : α → Fin n → α)
    (other : β → Fin n → β) (proj : α → β) (D P : α → Prop) (Q : β → Prop)
    (closed : ∀ x e, D x → D (next x e))
    (comm : ∀ x e, D x → proj (next x e)=other (proj x) e)
    (target : ∀ x, D x → (P x ↔ Q (proj x)))
    (t : Nat) (x : α) (hx : D x) :
    iidHitCost next P t x=iidHitCost other Q t (proj x) := by
  induction t generalizing x with
  | zero => rfl
  | succ t ih =>
    by_cases hq : Q (proj x)
    · rw [iidHitCost_of_target next P x ((target x hx).mpr hq),
          iidHitCost_of_target other Q (proj x) hq]
    · have hp : ¬P x := fun h => hq ((target x hx).mp h)
      simp only [iidHitCost,hp,hq,if_false]
      congr 3
      funext e
      rw [ih (next x e) (closed x e hx),comm x e hx]

/-- Transfer the rooted public bound at an actual D₁₂ cut without
extra quantitative costs. The physical product commutation, closure,
display map, and public rooted premise must be supplied separately. -/
theorem public_mean_to_product {α : Type} {p c n : Nat} (next : α → Fin n → α)
    (proj : α → Config p c n) (display : α → Fin n → Bool) (D : α → Prop)
    (closed : ∀ x e, D x → D (next x e))
    (comm : ∀ x e, D x → proj (next x e)=step (proj x) e)
    (bits : ∀ x j, D x → display x j=(proj x j).leader)
    (x : α) (hx : D x) (B : Nat)
    (mean : IIDExpectedHittingTimeAtMost step SafeOneLeader (proj x) B) :
    IIDExpectedHittingTimeAtMost next (ProductSafe next display) x B := by
  intro t
  rw [iidHitCost_eq_of_proj next step proj D _ SafeOneLeader closed comm
    (safe_of_proj next proj display D closed comm bits) t x hx]
  exact mean t

end L4.RootedProduct

#print axioms L4.RootedProduct.safe_of_proj
#print axioms L4.RootedProduct.iidHitCost_eq_of_proj
#print axioms L4.RootedProduct.public_mean_to_product
