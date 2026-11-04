import Leader.Wu.Coherence.WriterLeaseMass

set_option autoImplicit false
set_option Elab.async false

/-!
# Generic rank-descent row sum

`R2WriterLeaseMass` proves the repository's one worked unconditional mass bound, and
the hinge of that proof is a `private` lemma `rank_row_sum` stated only for `scrubRank`
and `scrubStep`.  Because it is private and concrete, it has never been reusable.

This file exports exactly that hinge, abstracted over an arbitrary step function on an
arbitrary type.  The two helper lemmas it needs are already public.
-/

namespace ZZMassTemplate

/-- Bounded non-increase plus one strictly descending letter gives the row sum that
the Bellman layer consumes.  Generic abstraction of `R2WriterLeaseMass.rank_row_sum`. -/
theorem rank_row_sum_generic
    {S : Type} {n : Nat}
    (step : S → Fin n → S)
    (Good : S → Prop)
    (rank : S → Nat)
    (hmono : ∀ x e, rank (step x e) ≤ rank x)
    (hdesc : ∀ x, Good x → ∃ e, rank (step x e) < rank x) :
    ∀ x, Good x →
      (List.ofFn (fun e => rank (step x e))).sum + 1 ≤ n * rank x := by
  intro x hx
  obtain ⟨e, he⟩ := hdesc x hx
  have hs := B9SpliceTableV10d.ofFn_sum_split
    (fun i => rank (step x i))
    (fun _ => rank x)
    e
    (fun i _ => hmono x i)
  rw [FiniteUniformStoppingTree.ofFn_sum_const] at hs
  omega

end ZZMassTemplate

#print axioms ZZMassTemplate.rank_row_sum_generic
