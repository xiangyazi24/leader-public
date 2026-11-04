import Leader.Wu.Birth.ShortDoneTerminalFirstHit
import Leader.Wu.Scheduler.FixedSpanRenewalPayload

/-!
# Exact finite no-hit counting on original scheduler words

Starting from an arbitrary literally leaderless full input and on a
non-singleton ring, `LeaderlessAlong` and the observer's `NoBirthAlong` are
pointwise equivalent on every finite original scheduler word.  Therefore their
0/1 indicators have exactly the same `wordSum` over all `n^T` raw words.

No probability lower bound, conditioned scheduler, runtime switch, or
permanent-survival statement is used here.
-/

namespace BirthShortDoneTerminalNoHitCount

open PPLL PPLLResearchFormulation PPLLExpiringComparisonRepair K2OutputSafety
open K2BirthDispatcher ExpiringK2Projection LDSinkBoundedKernel
open BirthShortDoneTerminalFirstHit

set_option autoImplicit false
set_option Elab.async false
set_option pp.structureInstances false

variable {ψ width κ τ n : Nat}

/-- On `n >= 2`, an original physical word has no physical positive prefix
iff every metadata birth event on that same word is false, provided the actual
full input starts literally leaderless. -/
theorem leaderlessAlong_iff_noBirthAlong
    (hψ : 0 < ψ) (hwidth : 0 < width) (hle : width ≤ ψ)
    (ring : DirectedRing n) (hn : 1 < n)
    (C : Fin n → ExpiringAgentState ψ κ τ)
    (h0 : Leaderless C) (es : List (Fin n)) :
    LeaderlessAlong hψ hwidth hle ring C es ↔
      BirthShortDoneTerminalObserver.NoBirthAlong
        hψ hwidth hle ring C es := by
  constructor
  · intro hz
    exact noBirthAlong_of_leaderlessAlong
      hψ hwidth hle ring hn C es hz
  · intro hb
    exact leaderlessAlong_of_noBirthAlong
      hψ hwidth hle ring C es h0 hb

/-- Unit indicator for literal physical no-hit along the whole original word.
Because `LeaderlessAlong` recurses through the successor, this includes the
actual terminal state after the last symbol. -/
noncomputable def physicalNoHitBit
    (hψ : 0 < ψ) (hwidth : 0 < width) (hle : width ≤ ψ)
    (ring : DirectedRing n)
    (C : Fin n → ExpiringAgentState ψ κ τ)
    (es : List (Fin n)) : Nat := by
  classical
  exact if LeaderlessAlong hψ hwidth hle ring C es then 1 else 0

/-- Unit indicator that every observer birth event on the same original word
is false. -/
noncomputable def noBirthBit
    (hψ : 0 < ψ) (hwidth : 0 < width) (hle : width ≤ ψ)
    (ring : DirectedRing n)
    (C : Fin n → ExpiringAgentState ψ κ τ)
    (es : List (Fin n)) : Nat := by
  classical
  exact if BirthShortDoneTerminalObserver.NoBirthAlong
    hψ hwidth hle ring C es then 1 else 0

/-- Pointwise equality of the two finite-word indicators. -/
theorem physicalNoHitBit_eq_noBirthBit
    (hψ : 0 < ψ) (hwidth : 0 < width) (hle : width ≤ ψ)
    (ring : DirectedRing n) (hn : 1 < n)
    (C : Fin n → ExpiringAgentState ψ κ τ)
    (h0 : Leaderless C) (es : List (Fin n)) :
    physicalNoHitBit hψ hwidth hle ring C es =
      noBirthBit hψ hwidth hle ring C es := by
  classical
  unfold physicalNoHitBit noBirthBit
  have hiff := leaderlessAlong_iff_noBirthAlong
    hψ hwidth hle ring hn C h0 es
  by_cases hz : LeaderlessAlong hψ hwidth hle ring C es
  · have hb : BirthShortDoneTerminalObserver.NoBirthAlong
        hψ hwidth hle ring C es := hiff.mp hz
    rw [if_pos hz, if_pos hb]
  · have hb : ¬ BirthShortDoneTerminalObserver.NoBirthAlong
        hψ hwidth hle ring C es := by
      intro hb
      exact hz (hiff.mpr hb)
    rw [if_neg hz, if_neg hb]

/-- Exact equality after indexing every original length-`T` scheduler word by
`Fin (n^T)`.  This is the word-for-word counting statement before packaging it
back as `wordSum`. -/
theorem rawWord_noHit_sum_eq_noBirth_sum
    (hψ : 0 < ψ) (hwidth : 0 < width) (hle : width ≤ ψ)
    (ring : DirectedRing n) (hn : 1 < n)
    (C : Fin n → ExpiringAgentState ψ κ τ)
    (h0 : Leaderless C) (T : Nat) :
    (List.ofFn (fun i : Fin (n ^ T) =>
      physicalNoHitBit hψ hwidth hle ring C
        (FixedSpanRenewalPayload.rawWord n T i))).sum =
    (List.ofFn (fun i : Fin (n ^ T) =>
      noBirthBit hψ hwidth hle ring C
        (FixedSpanRenewalPayload.rawWord n T i))).sum := by
  exact FiniteUniformStoppingTree.ofFn_sum_eq _ _ (fun i =>
    physicalNoHitBit_eq_noBirthBit
      hψ hwidth hle ring hn C h0
        (FixedSpanRenewalPayload.rawWord n T i))

/-- Exact finite original-word counting equivalence in the repository's
`wordSum` API.  Later probability producers may divide either side by the same
uniform denominator `n^T`; no probability inequality is asserted here. -/
theorem physicalNoHit_wordSum_eq_noBirth_wordSum
    (hψ : 0 < ψ) (hwidth : 0 < width) (hle : width ≤ ψ)
    (ring : DirectedRing n) (hn : 1 < n)
    (C : Fin n → ExpiringAgentState ψ κ τ)
    (h0 : Leaderless C) (T : Nat) :
    FixedSpanRenewalPayload.wordSum n T
        (physicalNoHitBit hψ hwidth hle ring C) =
      FixedSpanRenewalPayload.wordSum n T
        (noBirthBit hψ hwidth hle ring C) := by
  rw [← FixedSpanRenewalPayload.rawWord_sum n T
      (physicalNoHitBit hψ hwidth hle ring C),
    ← FixedSpanRenewalPayload.rawWord_sum n T
      (noBirthBit hψ hwidth hle ring C)]
  exact rawWord_noHit_sum_eq_noBirth_sum
    hψ hwidth hle ring hn C h0 T

#print axioms BirthShortDoneTerminalNoHitCount.leaderlessAlong_iff_noBirthAlong
#print axioms BirthShortDoneTerminalNoHitCount.physicalNoHitBit_eq_noBirthBit
#print axioms BirthShortDoneTerminalNoHitCount.physicalNoHit_wordSum_eq_noBirth_wordSum

end BirthShortDoneTerminalNoHitCount
