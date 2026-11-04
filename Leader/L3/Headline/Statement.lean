import Leader.L3.Protocol
import Leader.Wu.Scheduler.UniformFirstHitExpectation

/-!
# L3 headline statement (proposition only; no proof yet)

`L3Headline ring` is `thm:main` of `research/paper/l3/main.tex` (the linear-lease cubic theorem,
`thm:linear-lease` of `appendices/renewal.tex:1439`) for one ring size `n ≥ 5`, in the form fixed by
`research/lean-l3/PLAN.md` §2 v2:

0. state count (`prop:states`): the local alphabet `Agent (compileAdvice q)` is in bijection with
   `Fin N` for some `N ≤ stateBudget s`;
1. there is a class `G` of configurations closed under every edge (hence every edge word);
2. every configuration of `G` has exactly one leader output, frozen along every reachable
   configuration (`IsSafe`);
3. from every Cartesian configuration the first entrance time into `G` under the uniform i.i.d.
   edge scheduler is a.s. finite with expectation at most `linearLeaseBound n`.

The advice is `q = ceil(log2 n)` and `psi = ceil(log2 q)` (`main.tex:98-101`); the two constant
cases are `158046 n^2` for `q ≤ 32` (equivalently `psi ≤ 5`) and `20407959 psi^3 n^2` otherwise.
-/

namespace L3

set_option autoImplicit false

/-- `prop:states` (`renewal.tex:1356`):
`97086427103232 · 201 · a A^2 B^2 (64s+2)(34s+3)(s+1)^2(8s+5)(s+13)(13(s+13)+1)` with
`a = 2^floor(log2 s)`, `A = 2 + 2a`, `B = 2 + 4a`. -/
def stateBudget (s : Nat) : Nat :=
  let a := 2 ^ floorLogTwo s
  let A := 2 + 2 * a
  let B := 2 + 4 * a
  97086427103232 * 201 * a * A ^ 2 * B ^ 2 * (64 * s + 2) * (34 * s + 3) * (s + 1) ^ 2 *
    (8 * s + 5) * (s + 13) * (13 * (s + 13) + 1)

/-- The expected-time bound of `thm:linear-lease`: `158046 n^2` for `q ≤ 32`,
`20407959 psi^3 n^2` for `psi ≥ 6`. -/
def linearLeaseBound (n : Nat) : Nat :=
  if ceilLogTwo n ≤ 32 then 158046 * n ^ 2
  else 20407959 * ceilLogTwo (ceilLogTwo n) ^ 3 * n ^ 2

/-- The L3 headline proposition for ring size `n` (clauses 0-3 of the module docstring). -/
def L3Headline {n : Nat} (ring : DirectedRing n) : Prop :=
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
        ((linearLeaseBound n : Nat) : Rat))

end L3
