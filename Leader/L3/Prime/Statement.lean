import Leader.L3.Headline.Statement

/-!
# L3-PRIME headline statement (proposition only)

`L3PrimeHeadline ring` is `thm:l3prime` of
`research/method-review/l3-prime/L3PRIME-TRANSFER.tex` for one ring size `n ≥ 5`.  The protocol
is `protocol q` of `Leader/L3/Protocol.lean` with the compiler `compileAdvice` of
`Leader/L3/Params.lean`, which since the L3-PRIME change selects `K = 2q - t_s` on the signed band
`s ≥ 40000` ((P1)-(P2)) and the original L3 record below it.

Clauses, with `q = ceil(log2 n)`, `psi = ceil(log2 q)`, `s = max 2 psi = (compileAdvice q).s`:
0. state count (T3.3): the local alphabet is in bijection with `Fin N`, `N ≤ stateBudget s`;
1. a class `G` closed under every edge (hence every edge word);
2. every configuration of `G` has exactly one leader output, frozen along every reachable
   configuration (`IsSafe`);
3. (T3.4) from every Cartesian configuration the first entrance time into `G` under the uniform
   i.i.d. edge scheduler is a.s. finite with expectation at most `C n^2 s`,
   `C = 32652734400000000`;
4. (T3.5, block form) from every Cartesian configuration and every `k`,
   `P(T_G > 2 C n^2 s k) ≤ 2^(-k)`.  With `k = ceil(alpha log2 n)` this is the paper's
   `P(T_G > ceil(2 C n^2 s) ceil(alpha log2 n)) ≤ n^(-alpha)`.
The `n = 4` clause of `thm:l3prime` is the separate four-state rule (`L3FourAgentHeadline`).
-/

namespace L3

set_option autoImplicit false

/-- The constant `C` of (T3.4). -/
def l3PrimeConstant : Nat := 32652734400000000

/-- The expected-time bound `C n^2 s` of (T3.4), `s = (compileAdvice q).s = max 2 psi`. -/
def l3PrimeBound (n : Nat) : Nat :=
  l3PrimeConstant * (compileAdvice (ceilLogTwo n)).s * n ^ 2

/-- The L3-PRIME headline proposition for ring size `n` (clauses 0-4 of the module docstring). -/
def L3PrimeHeadline {n : Nat} (ring : DirectedRing n) : Prop :=
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
        ((l3PrimeBound n : Nat) : Rat)) ∧
    (∀ (C0 : (protocol q).Configuration n) (k : Nat),
      (2 : Rat) ^ k *
        UniformFirstHit.survivalProb
          (fun D e => (protocol q).step ring D e) G C0 (2 * l3PrimeBound n * k) ≤ 1)

end L3
