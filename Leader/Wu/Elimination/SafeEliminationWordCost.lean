import Leader.Wu.Scheduler.LeaderCountExpectedCost
import Leader.Wu.Elimination.SinkBoundedKernel

set_option autoImplicit false

namespace K2FiniteSafeEliminationExpected

open LDSinkBoundedKernel FiniteUniformStoppingTree LeaderCountExpectedCost

/-- Literal structural word recursion. The scheduler step and stopping
predicate are parameters; the physical instantiation occurs in the consumer. -/
def rawCost {S : Type} {n : Nat} (next : S → Fin n → S) (halt : S → Prop)
    [DecidablePred halt] : S → List (Fin n) → Nat
  | _, [] => 0
  | C, e :: es => if halt C then 0 else 1 + rawCost next halt (next C e) es

/-- The physical stopping-tree sum enumerates the same literal full words,
with exactly the existing finite-product enumeration and multiplicities. -/
theorem wordSum_run {S : Type} {n : Nat} (next : S → Fin n → S)
    (w : S → Nat) (C : S) (T : Nat) :
    FixedSpanRenewalPayload.wordSum n T (fun es => w (run next C es)) =
      LeaderCountDyadicTail.wordSum next w C T := by
  induction T generalizing C with
  | zero => simp [FixedSpanRenewalPayload.wordSum, allSchedules, run]
  | succ T ih =>
      rw [FixedSpanRenewalPayload.wordSum_succ, LeaderCountDyadicTail.wordSum_succ]
      exact ofFn_sum_eq _ _ (fun e => ih (next C e))

/-- A successful payload is exactly the physical endpoint of the first
count-one prefix. Every strictly earlier prefix has a different count.
This is wordwise and requires no probability or closure premise. -/
theorem payload_first_hit {S : Type} {n : Nat} (next : S → Fin n → S)
    (count : S → Nat) (C D : S) (es : List (Fin n))
    (hy : FixedSpanRenewalPayload.runPayload (physicalPayload next count)
      (haltAt count C) es = .success D) :
    ∃ u v, es = u ++ v ∧ D = run next C u ∧ count D = 1 ∧
      ∀ t, t < u.length → count (run next C (u.take t)) ≠ 1 := by
  induction es generalizing C with
  | nil =>
      change haltAt count C = .success D at hy
      unfold haltAt at hy
      split at hy
      next hc =>
        cases hy
        exact ⟨[], [], rfl, rfl, hc, fun _ h => (Nat.not_lt_zero _ h).elim⟩
      next hc => cases hy
  | cons e es ih =>
      by_cases hc : count C = 1
      · rw [haltAt, if_pos hc, FixedSpanRenewalPayload.runPayload_success] at hy
        cases hy
        exact ⟨[], e :: es, rfl, rfl, hc, fun _ h => (Nat.not_lt_zero _ h).elim⟩
      · have he : FixedSpanRenewalPayload.runPayload (physicalPayload next count)
            (haltAt count C) (e :: es) =
            FixedSpanRenewalPayload.runPayload (physicalPayload next count)
              (haltAt count (next C e)) es := by
          rw [haltAt, if_neg hc]
          rfl
        rw [he] at hy
        obtain ⟨u, v, huv, hD, hd, hp⟩ := ih (next C e) hy
        refine ⟨e :: u, v, by rw [huv]; rfl, hD, hd, ?_⟩
        intro t ht
        cases t with
        | zero => exact hc
        | succ t =>
            exact hp t (by simpa only [List.length_cons, Nat.succ_lt_succ_iff] using ht)

end K2FiniteSafeEliminationExpected

#print axioms K2FiniteSafeEliminationExpected.rawCost
#print axioms K2FiniteSafeEliminationExpected.wordSum_run
#print axioms K2FiniteSafeEliminationExpected.payload_first_hit
