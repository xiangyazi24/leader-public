import Leader.L4.PhysicalPublicSuffix
import Leader.L4.Height.ObserverPublic

namespace L4.PhysicalPublic
open PhysicalCustody
noncomputable def cpub : Nat := ObserverPublic.coefficient

theorem packed_suffix_at_cpub {s n : Nat} (hn : 4 ≤ n) (x : Raw s n) (hx : Marked x) :
    Height.IIDExpectedHittingTimeAtMost (rawNext s) PackedElected x (cpub*n^2) :=
  packed_suffix (coefficient := cpub) ObserverPublic.rooted_mean hn x hx

theorem bounded_suffix_at_cpub {n : Nat} (hn : 4 ≤ n) (hN : n ≤ boundedN)
    (x : BoundedRaw n) :
    Height.IIDExpectedHittingTimeAtMost boundedNext BoundedElected x (cpub*n^2) :=
  bounded_suffix (coefficient := cpub) ObserverPublic.rooted_mean hn hN x

theorem public_suffixes :
    ∃ cpub : Nat,
      (∀ {s n : Nat}, 4 ≤ n → ∀ x : Raw s n, Marked x →
        Height.IIDExpectedHittingTimeAtMost (rawNext s) PackedElected x (cpub*n^2)) ∧
      (∀ {n : Nat}, 4 ≤ n → n ≤ boundedN → ∀ x : BoundedRaw n,
        Height.IIDExpectedHittingTimeAtMost boundedNext BoundedElected x (cpub*n^2)) :=
  ⟨cpub, packed_suffix_at_cpub, bounded_suffix_at_cpub⟩

end L4.PhysicalPublic
