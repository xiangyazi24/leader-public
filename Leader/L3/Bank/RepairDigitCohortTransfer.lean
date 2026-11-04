import Leader.L3.ProbStages

/-!
# T23 item 1: first-hit cost transfer along a simulation

`costNumeratorSimLe`: if a relation `Sim` between a real chain and a model chain is preserved by
every letter while the real target is not hit, and a model target state forces the real target,
then the real first-hit cost is at most the model one, for every horizon.

Corollaries: the projection form (`f ∘ next' = next ∘ f` on a class) and the ghost form (the
real chain carries a proof-only ghost; the target reads only the physical state).
-/

namespace L3.CohortTransfer

set_option autoImplicit false

open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree

/-- Cost transfer along a simulation relation. -/
theorem costNumeratorSimLe {X Y : Type} {n : Nat} (next' : X → Fin n → X)
    (next : Y → Fin n → Y) (Sim : X → Y → Prop) (Good' : X → Prop) (Good : Y → Prop)
    (hstep : ∀ x y e, Sim x y → ¬ Good' x → Sim (next' x e) (next y e))
    (hgood : ∀ x y, Sim x y → Good y → Good' x) :
    ∀ T x y, Sim x y → costNumerator next' Good' x T ≤ costNumerator next Good y T := by
  classical
  intro T
  induction T with
  | zero => intro x y _; simp
  | succ T ih =>
    intro x y hxy
    by_cases hx : Good' x
    · rw [costNumerator_terminal next' Good' x hx]
      exact Nat.zero_le _
    · have hy : ¬ Good y := fun hy => hx (hgood x y hxy hy)
      rw [costNumerator_succ next' Good' x hx T, costNumerator_succ next Good y hy T]
      exact Nat.add_le_add_left
        (ofFn_sum_le _ _ (fun e => ih _ _ (hstep x y e hxy hx))) _

/-- Cost transfer along a projection that commutes with the letters, on a class closed off the
real target. -/
theorem costNumeratorProjectLe {X Y : Type} {n : Nat} (next' : X → Fin n → X)
    (next : Y → Fin n → Y) (f : X → Y) (hf : ∀ x e, f (next' x e) = next (f x) e)
    (Cls : X → Prop) (Good' : X → Prop) (Good : Y → Prop)
    (hcl : ∀ x e, Cls x → ¬ Good' x → Cls (next' x e))
    (hgood : ∀ x, Cls x → Good (f x) → Good' x) :
    ∀ x, Cls x → ∀ T, costNumerator next' Good' x T ≤ costNumerator next Good (f x) T :=
  fun x hx T => costNumeratorSimLe next' next (fun x y => Cls x ∧ f x = y) Good' Good
    (fun x y e h hg => ⟨hcl x e h.1 hg, by rw [hf, h.2]⟩)
    (fun x y h hy => hgood x h.1 (h.2 ▸ hy)) T x (f x) ⟨hx, rfl⟩

/-- Ghost form: the real chain `next` on `Z` is run together with a proof-only ghost on `G`;
the real target reads only `Z`. A simulation of the pair by a model chain bounds the real cost
from `z` by the model cost from any related model state. -/
theorem costNumeratorGhostSimLe {Z G Y : Type} {n : Nat} (next : Z → Fin n → Z)
    (ghost : Z → G → Fin n → G) (nextY : Y → Fin n → Y) (Sim : Z × G → Y → Prop)
    (Good' : Z → Prop) (Good : Y → Prop)
    (hstep : ∀ z g y e, Sim (z, g) y → ¬ Good' z → Sim (next z e, ghost z g e) (nextY y e))
    (hgood : ∀ z g y, Sim (z, g) y → Good y → Good' z) :
    ∀ T z g y, Sim (z, g) y → costNumerator next Good' z T ≤ costNumerator nextY Good y T := by
  intro T z g y h
  have heq := L3.Prob.costNumerator_ghost_eq next
    (fun (w : Z × G) e => (next w.1 e, ghost w.1 w.2 e)) (fun _ _ => rfl) Good' (z, g) T
  rw [← heq]
  exact costNumeratorSimLe (fun (w : Z × G) e => (next w.1 e, ghost w.1 w.2 e)) nextY Sim
    (fun w => Good' w.1) Good (fun w y e hw hg => hstep w.1 w.2 y e hw hg)
    (fun w y hw hy => hgood w.1 w.2 y hw hy) T (z, g) y h

end L3.CohortTransfer

#print axioms L3.CohortTransfer.costNumeratorSimLe
#print axioms L3.CohortTransfer.costNumeratorProjectLe
#print axioms L3.CohortTransfer.costNumeratorGhostSimLe
