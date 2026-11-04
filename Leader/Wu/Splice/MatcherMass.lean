import Leader.Wu.Splice.TripleHitWords
import Leader.Wu.Scheduler.FixedSpanRenewalPayload

set_option autoImplicit false

/-! # Mass of progress words: at least 1/64 of the length-`6n` scheduler words make progress

The three-hit count `successCount` is the number of scheduler words absorbed in success along
the matcher run, so the 1/64 bound of `triple_sixty_fourth` is a bound on the number of words
that, from a leaderless safe non-clear configuration, contain a physical service (a B7 step of
the projected word) or drop the pair weight of the chosen edge. -/

namespace B9SpliceMatcherMass

open FiniteUniformStoppingTree ThreePortSerialCount B9SpliceTripleHitBridge
  FixedSpanRenewalPayload B9SpliceTripleHitWords
open Q11593SpliceControllerDesign B9SpliceControllerR1Table B9SpliceControllerR1TableV6
  B9SpliceControllerR1TableV7 B9SpliceTableV10e B9SpliceV10eTransparency
  B9SpliceV10eWordProjection B9SpliceV10eProjectionLetter B9SpliceV10ePairWeight

variable {n psi width kappa tau : Nat}

theorem runNode_eq_runStopped {S : Type} (step : S → Fin n → StopNode S) (w : List (Fin n)) :
    ∀ x : StopNode S, runNode step x w = runStopped step x w := by
  induction w with
  | nil => intro x; rfl
  | cons e w ih => intro x; exact ih _

/-- The success count is the number of words absorbed in success along the run. -/
theorem wordSum_success_eq_successCount {S : Type} (step : S → Fin n → StopNode S) (T : Nat) :
    ∀ x : StopNode S,
      wordSum n T (fun u => successWeight (runStopped step x u)) = successCount step x T := by
  induction T with
  | zero =>
    intro x
    simp [wordSum, allSchedules, runStopped, successCount, treeWeight]
  | succ T ih =>
    intro x
    rw [wordSum_succ]
    unfold successCount treeWeight
    apply ofFn_sum_eq
    intro e
    exact ih (stepNode step x e)

theorem sum_map_le {A : Type} (l : List A) (f g : A → Nat) (h : ∀ x, f x ≤ g x) :
    (l.map f).sum ≤ (l.map g).sum := by
  induction l with
  | nil => exact Nat.le_refl 0
  | cons x l ih =>
    simp only [List.map_cons, List.sum_cons]
    exact Nat.add_le_add (h x) ih

theorem wordSum_mono (T : Nat) (f g : List (Fin n) → Nat) (h : ∀ u, f u ≤ g u) :
    wordSum n T f ≤ wordSum n T g := by
  unfold wordSum
  exact sum_map_le _ _ _ (fun u => h u.reverse)

/-- Indicator that a scheduler word from `C` contains a physical service or drops the pair
weight of `e` at some prefix. -/
noncomputable def progressBit (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau) (e : Fin n)
    (u : List (Fin n)) : Nat := by
  classical
  exact if (1 ≤ physCount hpsi hwidth hle ring u C ∨
      ∃ w' : List (Fin n), w' <+: u ∧
        pairWeight ring (serveWord hpsi hwidth hle ring w' C) e < pairWeight ring C e)
    then 1 else 0

/-- From any leaderless safe non-clear configuration on a ring with `n ≥ 3` there is an edge
such that at least a 1/64 fraction of the `n^(6n)` scheduler words of length `6n` contain a
physical service or drop that edge's pair weight. -/
theorem progress_mass (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (ring : DirectedRing n) (hn : 3 ≤ n) (C : R1ConfigV6 n psi kappa tau)
    (hlead : ∀ i, (C i).carrier.splice.base.core.core.leader = false)
    (hS : SpliceSafeV7 hpsi ring C) (hclear : ¬ RolesClearV7 C) :
    ∃ e : Fin n, n ^ (6 * n) ≤ 64 * wordSum n (6 * n) (progressBit hpsi hwidth hle ring C e) := by
  obtain ⟨e, he⟩ := matcher_success_progress hpsi hwidth hle ring hn C hlead hS hclear
  refine ⟨e, ?_⟩
  have h64 := triple_sixty_fourth (ports ring hn e) hn
  rw [← wordSum_success_eq_successCount] at h64
  have hmono : wordSum n (6 * n)
      (fun u => successWeight (runStopped (tripleStep (ports ring hn e)) (.active .zero) u)) ≤
      wordSum n (6 * n) (progressBit hpsi hwidth hle ring C e) := by
    apply wordSum_mono
    intro u
    unfold progressBit
    by_cases hs : runStopped (tripleStep (ports ring hn e)) (.active .zero) u = .success
    · have hg := he u (by rw [runNode_eq_runStopped]; exact hs)
      rw [hs, if_pos hg]
      exact Nat.le_refl 1
    · have : successWeight (runStopped (tripleStep (ports ring hn e)) (.active .zero) u) = 0 := by
        cases hr : runStopped (tripleStep (ports ring hn e)) (.active .zero) u with
        | active s => rfl
        | success => exact absurd hr hs
        | failure => rfl
      rw [this]
      exact Nat.zero_le _
  omega

end B9SpliceMatcherMass
