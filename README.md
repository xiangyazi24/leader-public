# Leader: Lean 4 formalization of self-stabilizing leader election on rings

Lean 4 (`leanprover/lean4:v4.33.0`, core only, no Mathlib) formalization of self-stabilizing leader election
in population protocols on directed rings.

## L3: logarithmic advice

`L3.l3PrimeMainTheorem` (`Leader/L3/Prime/MainTheorem.lean`):

```lean
theorem l3PrimeMainTheorem :
    (∀ {n : Nat} (ring : DirectedRing n), 5 ≤ n → L3PrimeHeadline ring) ∧
    (∀ ring : DirectedRing 4, L3FourAgentHeadline ring)
```

For a ring of `n ≥ 5` agents with advice `q = ⌈log₂ n⌉`, `ψ = ⌈log₂ q⌉` and `s = max 2 ψ`, `L3PrimeHeadline ring`
(`Leader/L3/Prime/Statement.lean`) states:

0. the local state set of the protocol is in bijection with `Fin N` for some `N ≤ stateBudget s`;
1. there is a class `G` of configurations closed under every interaction;
2. every configuration in `G` has exactly one leader output, frozen along every reachable configuration;
3. from every configuration, the first entrance time into `G` under the uniform random edge scheduler is
   almost surely finite, with expectation at most `C n² s`, `C = 32652734400000000`;
4. from every configuration and every `k`, the probability that `G` has not been entered within `2 C n² s k`
   interactions is at most `2^-k` (`L3.l3PrimePolyTail` gives the `n^-α` form).

The case `n = 4` is covered by a separate four-state protocol (`Leader/L3/FourAgent.lean`).
The earlier statement `L3.l3MainTheorem` (`Leader/L3/MainTheorem.lean`) bounds the same protocol family by
`158046 n²` for `q ≤ 32` and `20407959 ψ³ n²` otherwise.

`#print axioms` reports `propext`, `Classical.choice`, `Quot.sound` only for both theorems. The development
contains no `sorry`, no `axiom` declarations and no `native_decide`.

## L4: doubly logarithmic advice

`L4.AllSizeHeadline.allSize_fast` (`Leader/L4/AllSizeHeadline.lean`):

```lean
theorem allSize_fast :
    (∀ s : Nat, ∃ card : Nat,
      Nonempty (L4.ExactCoding (compactDeployment s).Site (Fin card)) ∧
      card ≤ 2^2976*(s+2)^20) ∧
    (∀ n (hn : 4 ≤ n),
      (compactDeployment (ceilingLogTwo (ceilingLogTwo n))).Expected boundedEncode boundedDecode n hn
        L4.PhysicalCustodyProduction.K_custody
        (patrolAllowance L4.WindowCappedPublic.coefficient))
```

The protocol `compactDeployment s` takes one advice value `s`, the same at every agent. The theorem states:

1. for every advice `s`, the site alphabet has an exact coding (`L4.ExactCoding`: both inverse maps) with `Fin card`,
   where `card ≤ 2^2976 (s+2)^20`;
2. for every ring size `n ≥ 4`, with advice `s = ⌈log₂ ⌈log₂ n⌉⌉` (`ceilingLogTwo`), from every initial
   configuration, under the uniform random edge scheduler on the directed ring, the expected number of interactions
   until one fixed site is the sole leader output on every continuation (`Permanent`,
   `Leader/L4/Height/AllSizeSpine.lean`) is at most `compactTimeCoeff g (2^32) patrol * n²`, an absolute constant times
   `n²` (`Deployment.Expected`, `Leader/L4/Height/AllSizeWirePart18.lean`, with `g = K_custody` and
   `patrol = patrolAllowance coefficient`). The expectation is `UniformFirstHit.ExpectedHittingTimeAtMost`
   (`Leader/Wu/Scheduler/UniformFirstHitExpectation.lean`): the first hitting time is almost surely finite and every
   partial sum of its expectation series is at most the bound.

`#print axioms L4.AllSizeHeadline.allSize_fast` reports `propext`, `Classical.choice`, `Quot.sound` only.

The protocol has two branches. For bounded advice `s ≤ 5` every site runs a fixed 48-bit constant-state modular
election. For `s ≥ 6` a site holds a packed word whose width is logarithmic in `s`; this branch is composed of a
custody layer, a unison clock and an anchor election. The leader output in this branch is a private reference bit
of the packed state.

## Layout

| directory | content |
|---|---|
| `Leader/Core` | population-protocol framework: configurations, steps, closed predicates, safety, schedulers |
| `Leader/L3` | the logarithmic-advice protocol and its main theorems above |
| `Leader/L4` | the doubly logarithmic advice protocol and `allSize_fast` above |
| `Leader/Wu` | formalization of the P_PLL protocol of Cheng-Hung Wu's 2024 master's thesis (National Taiwan University): the protocol, its safety and convergence arguments, repairs, and machine-checked counterexamples to printed steps |
| `Leader/AAFJ` | the ring leader-election protocol of Angluin, Aspnes, Fischer and Jiang, *Self-stabilizing population protocols* (TAAS 2008): barrier constructions, fair executions, and counterexamples to printed steps |
| `Leader/PPL` | the protocol P_PL of Yokota, Sudo, Ooshita and Masuzawa, *A near time-optimal population protocol for self-stabilizing leader election on rings with a poly-logarithmic number of states* (PODC 2023): correctness and expected-time analysis |

`AxiomCheck.lean` prints the axioms of the main results of each part.

## Building

```sh
lake build            # the Leader library: 3062 modules (L3, L4 and their imports)
lake env lean AxiomCheck.lean
```

The executables in `lakefile.toml` are simulators used to test conjectures; they are not part of any proof.
