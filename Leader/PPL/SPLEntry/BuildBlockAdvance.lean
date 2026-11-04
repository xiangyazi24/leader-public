import Leader.PPL.SPLEntry.BuildGappedAssembly

namespace PPL.Convergence.L18

set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false

open PPL
open PPL.Probability

/-!
The block row is a direct P_PL-prime statement.  The prime Lemma-4 core below
is deliberately quantified over the complete gapped scheduler chunk, not only
the selected-word prefix.

On the non-hit branch it records separately:

* preservation of every already repaired pair through all inserted and
  trailing prime interactions; and
* construction of the current pair b at the endpoint.

This is exactly the information needed to extend BuildPrefix b to
BuildPrefix (b+1).

There is no kappa hypothesis.  The kappa=0 counterexample refutes
a full-P_PL/P_PL-prime field-agreement transfer, not this direct prime
semantics.
-/

/--
Direct prime-run Lemma-4 core for one L18 construction block.

The existing full-P_PL lemma4 core remains an explicit input because a future
proof may reuse its combinatorial/lineage content, but this proposition does
not assert a false field-by-field coupling between full P_PL and P_PL-prime.

Crucially, schedule is the entire gapped chunk.  Therefore hkeep.1 below is
the frame theorem for all already repaired pairs even after the selected
Lemma-4 word has finished and arbitrary later prime interactions occur.
-/
def L18PrimeLemma4Core : Prop :=
  PPL.lemma4_deterministic_core →
  ∀ {n psi kappa : Nat}
    (hn3 : 3 ≤ n)
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (root : Fin n)
    (b : Nat)
    (C : Config n psi kappa)
    (schedule : DetSchedule n),
    b < l18BlockCount n psi →
    L18BuildPrefixAt ring root b C →
    (PPL.lemma4Word ring
      (shiftRight ring root (b * psi)) psi).Sublist schedule →
    let D := runPPrime ring C schedule
    l18HitsSPL ring root C schedule = true ∨
      (L18BuildPrefixAt ring root b D ∧
        L18BuildPairOK ring root D b)

/--
Pure prefix extension.

The old prefix supplies CDL, no-risky, and every pair strictly below b.
The new block certificate supplies pair b.  No protocol semantics occur here.
-/
theorem l18BuildPrefixAt_succ_of_pair
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (root : Fin n)
    (b : Nat)
    (C : Config n psi kappa)
    (hprefix : L18BuildPrefixAt ring root b C)
    (hpair : L18BuildPairOK ring root C b) :
    L18BuildPrefixAt ring root (b + 1) C := by
  unfold L18BuildPrefixAt at hprefix ⊢
  refine ⟨hprefix.1, ⟨hprefix.2.1, ?_⟩⟩
  intro seg hseg
  by_cases hlt : seg.val < b
  · exact hprefix.2.2 seg hlt
  · have heq : seg.val = b := by
      omega
    rw [heq]
    exact hpair

/--
block-row closure from the direct prime Lemma-4 core.

The hlemma4 parameter in L18BuildBlockAdvanceRow is consumed only by
L18PrimeLemma4Core.  No kappa positivity or Theorem-1 parameter assumption is
needed.
-/
theorem l18BuildBlockAdvanceRow_of_primeLemma4Core
    (hprime : L18PrimeLemma4Core) :
    L18BuildBlockAdvanceRow := by
  unfold L18BuildBlockAdvanceRow
  intro n psi kappa
  intro hn3 hpsi
  intro ring root b C schedule hlemma4
  intro hb hprefix hsub

  have h :=
    hprime hlemma4
      hn3 hpsi ring root b C schedule
      hb hprefix hsub

  dsimp only at h

  rcases h with hhit | hkeep
  · exact .inl hhit
  · exact
      .inr
        (l18BuildPrefixAt_succ_of_pair
          ring root b
          (runPPrime ring C schedule)
          hkeep.1 hkeep.2)

end PPL.Convergence.L18

#print axioms PPL.Convergence.L18.l18BuildPrefixAt_succ_of_pair
#print axioms PPL.Convergence.L18.l18BuildBlockAdvanceRow_of_primeLemma4Core
