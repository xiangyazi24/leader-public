import Leader.L3.MainTheorem
import Leader.L3.Prime.RenewalSharp

/-!
# L3 tail bound (`research/paper/l3/main.tex`, Corollary `cor:tail`)

The expectation bound of `L3Headline` is uniform over all initial configurations, so restarting
at block boundaries gives a geometric tail: for every `k`, the probability of not having entered
the closed one-leader class `G` within `2 B k` global interactions is at most `2^-k`, where
`B = linearLeaseBound n` is the headline expectation bound. With `k = ceil(alpha log2 n)` this is
the paper's `P{T > ceil(2 C(q) n^2) ceil(alpha log2 n)} <= n^-alpha`.

Core Lean only; no `sorry`, `axiom`, `native_decide`.
-/

namespace L3

set_option autoImplicit false

/-- `L3Headline` together with the block tail bound for the same closed class `G`. -/
def L3HeadlineWithTail {n : Nat} (ring : DirectedRing n) : Prop :=
  let q := ceilLogTwo n
  (∃ N : Nat, N ≤ stateBudget (compileAdvice q).s ∧
     ∃ decode : Fin N → Agent (compileAdvice q),
       (∀ i j, decode i = decode j → i = j) ∧ (∀ a, ∃ i, decode i = a)) ∧
  ∃ G : (protocol q).Configuration n → Prop,
    PopulationProtocol.ClosedPred (protocol q) ring G ∧
    (∀ C, G C → PopulationProtocol.IsSafe (protocol q) ring C (fun b => b)) ∧
    (∀ C0 : (protocol q).Configuration n,
      UniformFirstHit.ExpectedHittingTimeAtMost
        (fun D e => (protocol q).step ring D e) G C0
        ((linearLeaseBound n : Nat) : Rat)) ∧
    (∀ (C0 : (protocol q).Configuration n) (k : Nat),
      (2 : Rat) ^ k *
        UniformFirstHit.survivalProb (fun D e => (protocol q).step ring D e) G C0
          (2 * linearLeaseBound n * k) ≤ 1)

/-- Corollary `cor:tail`: the uniform expectation bound gives the block tail. -/
theorem l3HeadlineWithTailOf {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (h : L3Headline ring) : L3HeadlineWithTail ring := by
  unfold L3HeadlineWithTail
  unfold L3Headline at h
  dsimp only at h ⊢
  obtain ⟨hstates, G, hclosed, hsafe, hmean⟩ := h
  refine ⟨hstates, G, hclosed, hsafe, hmean, ?_⟩
  exact UniformFirstHit.survivalProb_blocks_of_expected
    (fun D e => (protocol (ceilLogTwo n)).step ring D e) G (by omega)
    (linearLeaseBound n) hmean

/-- **thm:main with `cor:tail`** for `n ≥ 5`: expectation and block tail, on every band. -/
theorem l3MainTheoremWithTail {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n) :
    L3HeadlineWithTail ring :=
  l3HeadlineWithTailOf ring hn (l3MainTheorem.1 ring hn)

end L3

#print axioms L3.l3HeadlineWithTailOf
#print axioms L3.l3MainTheoremWithTail
