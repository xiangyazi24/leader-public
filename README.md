# Leader: Lean 4 formalization of self-stabilizing leader election on rings

Lean 4 (`leanprover/lean4:v4.33.0`, core only, no Mathlib) formalization of self-stabilizing leader election
in population protocols on directed rings.

## Main theorem

`L3.l3MainTheorem` (`Leader/L3/MainTheorem.lean`):

```lean
theorem l3MainTheorem :
    (∀ {n : Nat} (ring : DirectedRing n), 5 ≤ n → L3Headline ring) ∧
    (∀ ring : DirectedRing 4, L3FourAgentHeadline ring)
```

For a ring of `n ≥ 5` agents with advice `q = ⌈log₂ n⌉` and `ψ = ⌈log₂ q⌉`, `L3Headline ring`
(`Leader/L3/Headline/Statement.lean`) states:

0. the local state set of the protocol is finite, of size at most an explicit bound (`stateBudget`);
1. there is a class `G` of configurations closed under every interaction;
2. every configuration in `G` has exactly one leader output, frozen along every reachable configuration;
3. from every configuration, the first entrance time into `G` under the uniform random edge scheduler is
   almost surely finite, with expectation at most `158046 n²` when `q ≤ 32` and `20407959 ψ³ n²` otherwise.

The case `n = 4` is covered by a separate four-state protocol (`Leader/L3/FourAgent.lean`).

`#print axioms L3.l3MainTheorem` reports `propext`, `Classical.choice`, `Quot.sound` only. The development
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
   `Leader/L4/Height/G9Spine.lean`) is at most `compactTimeCoeff g (2^32) patrol * n²`, an absolute constant times
   `n²` (`Deployment.Expected`, `Leader/L4/Height/G9WirePart18.lean`, with `g = K_custody` and
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
| `Leader/L3` | the protocol and the main theorem above |
| `Leader/L4` | the doubly logarithmic advice protocol and `allSize_fast` above |
| `Leader/Wu` | formalization of the P_PLL protocol of Cheng-Hung Wu's 2024 master's thesis (National Taiwan University): the protocol, its safety and convergence arguments, repairs, and machine-checked counterexamples to printed steps |
| `Leader/AAFJ` | the ring leader-election protocol of Angluin, Aspnes, Fischer and Jiang, *Self-stabilizing population protocols* (TAAS 2008): barrier constructions, fair executions, and counterexamples to printed steps |
| `Leader/PPL` | the protocol P_PL of Yokota, Sudo, Ooshita and Masuzawa, *A near time-optimal population protocol for self-stabilizing leader election on rings with a poly-logarithmic number of states* (PODC 2023): correctness and expected-time analysis |

`AxiomCheck.lean` prints the axioms of the main results of each part.

## Building

```sh
lake build            # all 4691 modules; the 2812 modules outside Leader/L4 take about 2 CPU-hours from scratch
lake env lean AxiomCheck.lean
```

The executables in `lakefile.toml` are simulators used to test conjectures; they are not part of any proof.
