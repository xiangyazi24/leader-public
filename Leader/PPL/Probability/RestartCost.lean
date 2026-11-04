import Leader.Wu.Elimination.ArbitraryInputExpectedCost

/-!
# Generic finite-word Markov and restart wrappers for P_PL

This file is protocol-independent.  In particular it never instantiates the
K2 transition.  It only adapts the repository's generic exact finite-word
first-hit accounting to closed invariants.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PPL.Probability

open K2ArbitraryElimination.FiniteAccounting
open LeaderCountDyadicTail

variable {S : Type} {n : Nat}

/-- Restrict a physical transition to a forward-closed invariant. -/
def restartRestrictStep
    (next : S → Fin n → S) (I : S → Prop)
    (hI : ∀ x e, I x → I (next x e)) :
    {x : S // I x} → Fin n → {x : S // I x} :=
  fun x e => ⟨next x.1 e, hI x.1 e x.2⟩

/-- Read the same target predicate on the invariant subtype. -/
def restartRestrictTarget
    (P I : S → Prop) : {x : S // I x} → Prop :=
  fun x => P x.1

/-- Restricting to a closed invariant preserves the exact endpoint miss
numerator on every raw horizon. -/
theorem restartRestrict_missWordSum
    (next : S → Fin n → S) (P I : S → Prop)
    (hI : ∀ x e, I x → I (next x e)) :
    ∀ T x (hx : I x),
      wordSum
          (restartRestrictStep next I hI)
          (miss (restartRestrictTarget P I))
          ⟨x, hx⟩ T =
        wordSum next (miss P) x T := by
  classical
  intro T
  induction T with
  | zero =>
      intro x hx
      simp [miss, restartRestrictTarget]
      split <;> simp_all
  | succ T ih =>
      intro x hx
      rw [wordSum_succ, wordSum_succ]
      exact FiniteUniformStoppingTree.ofFn_sum_eq _ _ (fun e => by
        simpa [restartRestrictStep] using
          ih (next x e) (hI x e hx))

/-- Restricting to a closed invariant preserves the exact first-hit cost
numerator on every raw horizon. -/
theorem restartRestrict_costNumerator
    (next : S → Fin n → S) (P I : S → Prop)
    (hI : ∀ x e, I x → I (next x e)) :
    ∀ T x (hx : I x),
      costNumerator
          (restartRestrictStep next I hI)
          (restartRestrictTarget P I)
          ⟨x, hx⟩ T =
        costNumerator next P x T := by
  classical
  intro T
  induction T with
  | zero =>
      intro x hx
      rfl
  | succ T ih =>
      intro x hx
      by_cases hp : P x
      · have hp' :
            restartRestrictTarget P I ⟨x, hx⟩ := by
          simpa [restartRestrictTarget] using hp
        rw [
          costNumerator_terminal
            (restartRestrictStep next I hI)
            (restartRestrictTarget P I)
            ⟨x, hx⟩ hp' (T + 1),
          costNumerator_terminal next P x hp (T + 1)
        ]
      · have hp' :
            ¬ restartRestrictTarget P I ⟨x, hx⟩ := by
          simpa [restartRestrictTarget] using hp
        rw [
          costNumerator_succ
            (restartRestrictStep next I hI)
            (restartRestrictTarget P I)
            ⟨x, hx⟩ hp' T,
          costNumerator_succ next P x hp T
        ]
        rw [FiniteUniformStoppingTree.ofFn_sum_eq _ _ (fun e => by
          simpa [restartRestrictStep] using
            ih (next x e) (hI x e hx))]

/-- A word whose endpoint still misses a closed target has paid all T units
of first-hit cost.  This is the raw-word analogue of
FiniteUniformStoppingTree.horizon_mul_activeCount_le_truncatedActiveCostNumerator. -/
theorem horizon_mul_missCount_le_costNumerator
    (next : S → Fin n → S) (P : S → Prop)
    (hP : ∀ x e, P x → P (next x e)) :
    ∀ T x,
      T * wordSum next (miss P) x T ≤
        costNumerator next P x T := by
  classical
  intro T
  induction T with
  | zero =>
      intro x
      simp
  | succ T ih =>
      intro x
      change
        (T + 1) * wordSum next (miss P) x (T + 1) ≤
          costNumerator next P x (T + 1)
      by_cases hx : P x
      · rw [
          miss_zero next P hP x hx (T + 1),
          costNumerator_terminal next P x hx (T + 1)
        ]
        simp
      · rw [
          wordSum_succ,
          costNumerator_succ next P x hx T
        ]
        have htail :
            T *
                (List.ofFn (fun e : Fin n =>
                  wordSum next (miss P) (next x e) T)).sum ≤
              (List.ofFn (fun e : Fin n =>
                costNumerator next P (next x e) T)).sum := by
          calc
            T *
                (List.ofFn (fun e : Fin n =>
                  wordSum next (miss P) (next x e) T)).sum =
                (List.ofFn (fun e : Fin n =>
                  T * wordSum next (miss P) (next x e) T)).sum := by
              exact (FiniteUniformStoppingTree.ofFn_sum_mul_left T _).symm
            _ ≤
                (List.ofFn (fun e : Fin n =>
                  costNumerator next P (next x e) T)).sum := by
              exact FiniteUniformStoppingTree.ofFn_sum_le _ _ (fun e => ih (next x e))
        have hmass := miss_mass_le next P x (T + 1)
        rw [wordSum_succ] at hmass
        rw [Nat.add_mul, Nat.one_mul]
        omega

/-- Exact geometric half-block amplification on every actual retained
endpoint in I.  This is just the non-target-premise wrapper around the
existing repeat_miss theorem; no independent-attempt premise occurs. -/
theorem repeat_half_block_miss
    (next : S → Fin n → S) (P I : S → Prop)
    (hP : ∀ x e, P x → P (next x e))
    (hI : ∀ x e, I x → I (next x e))
    (B : Nat)
    (hb : ∀ x, I x → ¬ P x →
      2 * wordSum next (miss P) x B ≤ n ^ B)
    (x : S) (hxI : I x) (j : Nat) :
    2 ^ j * wordSum next (miss P) x (j * B) ≤
      n ^ (j * B) := by
  classical
  have hbAll :
      ∀ y, I y →
        2 * wordSum next (miss P) y B ≤ n ^ B := by
    intro y hyI
    by_cases hyP : P y
    · rw [miss_zero next P hP y hyP B]
      simp
    · exact hb y hyI hyP
  exact
    repeat_miss next P I hI hP B 2 hbAll x hxI j

/-- Invariant-local half-block restart.

If every non-target state in I has at most half the scheduler mass still
missing after B raw steps, every truncated first-hit cost from I is bounded
by 2*B normalized interactions.

The proof invokes cost_le_two_blocks on the closed invariant subtype.
The exact constant is 2*B. -/
theorem half_block_restart
    (next : S → Fin n → S) (P I : S → Prop)
    (hP : ∀ x e, P x → P (next x e))
    (hI : ∀ x e, I x → I (next x e))
    (B : Nat) (hB : 0 < B)
    (hb : ∀ x, I x → ¬ P x →
      2 * wordSum next (miss P) x B ≤ n ^ B) :
    ∀ T x, I x →
      costNumerator next P x T ≤ n ^ T * (2 * B) := by
  classical
  have hPI :
      ∀ (x : {x : S // I x}) (e : Fin n),
        restartRestrictTarget P I x →
          restartRestrictTarget P I
            (restartRestrictStep next I hI x e) := by
    intro x e hxP
    change P x.1 at hxP
    change P (next x.1 e)
    exact hP x.1 e hxP
  have hbI :
      ∀ x : {x : S // I x},
        2 *
            wordSum
              (restartRestrictStep next I hI)
              (miss (restartRestrictTarget P I))
              x B ≤
          n ^ B := by
    intro x
    rcases x with ⟨x, hxI⟩
    by_cases hxP : P x
    · have hxPI :
          restartRestrictTarget P I ⟨x, hxI⟩ := by
        simpa [restartRestrictTarget] using hxP
      rw [
        miss_zero
          (restartRestrictStep next I hI)
          (restartRestrictTarget P I)
          hPI ⟨x, hxI⟩ hxPI B
      ]
      simp
    · rw [
        restartRestrict_missWordSum
          next P I hI B x hxI
      ]
      exact hb x hxI hxP
  intro T x hxI
  have h :=
    cost_le_two_blocks
      (restartRestrictStep next I hI)
      (restartRestrictTarget P I)
      hPI B hB hbI T ⟨x, hxI⟩
  rw [
    restartRestrict_costNumerator
      next P I hI T x hxI
  ] at h
  exact h

/-- Exact Nat Markov-to-half conversion for the raw costNumerator interface.

A uniform first-hit cost envelope M on non-target states in I gives a
half-miss block at the literal horizon B = 2*M. -/
theorem markov_to_half_block
    (next : S → Fin n → S) (P I : S → Prop)
    (hP : ∀ x e, P x → P (next x e))
    (M : Nat) (hM : 0 < M)
    (hcost : ∀ x, I x → ¬ P x → ∀ T,
      costNumerator next P x T ≤ n ^ T * M) :
    ∀ x, I x →
      2 * wordSum next (miss P) x (2 * M) ≤
        n ^ (2 * M) := by
  intro x hxI
  by_cases hxP : P x
  · rw [miss_zero next P hP x hxP (2 * M)]
    simp
  · have hL : 0 < 2 * M := by
      omega
    have hcharge :=
      horizon_mul_missCount_le_costNumerator
        next P hP (2 * M) x
    have hdelay :
        1 * costNumerator next P x (2 * M) ≤
          M * n ^ (2 * M) := by
      calc
        1 * costNumerator next P x (2 * M) =
            costNumerator next P x (2 * M) := by
          simp
        _ ≤ n ^ (2 * M) * M :=
          hcost x hxI hxP (2 * M)
        _ = M * n ^ (2 * M) :=
          Nat.mul_comm _ _
    have hscale :
        2 * M ≤ (2 * M) * 1 := by
      simp
    exact
      FiniteUniformStoppingTree.two_mul_le_of_scaled_delay
        (L := 2 * M)
        (miss := wordSum next (miss P) x (2 * M))
        (delay := costNumerator next P x (2 * M))
        (den := 1)
        (num := M)
        (total := n ^ (2 * M))
        hL (by omega) hcharge hdelay hscale

/-- Uniform cost -> Markov half block -> invariant-local restart.
The exact composed restart constant is 4*M. -/
theorem restart_cost_of_uniform_bound
    (next : S → Fin n → S) (P I : S → Prop)
    (hP : ∀ x e, P x → P (next x e))
    (hI : ∀ x e, I x → I (next x e))
    (M : Nat) (hM : 0 < M)
    (hcost : ∀ x, I x → ¬ P x → ∀ T,
      costNumerator next P x T ≤ n ^ T * M) :
    ∀ T x, I x →
      costNumerator next P x T ≤ n ^ T * (4 * M) := by
  have hb :=
    markov_to_half_block next P I hP M hM hcost
  have hrestart :=
    half_block_restart
      next P I hP hI (2 * M) (by omega)
      (fun x hxI _ => hb x hxI)
  intro T x hxI
  have h := hrestart T x hxI
  rw [show 2 * (2 * M) = 4 * M by omega] at h
  exact h

/-- Potential-valued Markov adapter.

If the per-state first-hit cost envelope is Phi(x), and Phi(x) is uniformly
bounded by PhiMax on non-target states of I, the uniform half block is
B = 2*PhiMax. -/
theorem markov_to_half_block_of_potential
    (next : S → Fin n → S) (P I : S → Prop)
    (hP : ∀ x e, P x → P (next x e))
    (Phi : S → Nat) (PhiMax : Nat) (hPhiMax : 0 < PhiMax)
    (hPhi : ∀ x, I x → ¬ P x → Phi x ≤ PhiMax)
    (hcost : ∀ x, I x → ¬ P x → ∀ T,
      costNumerator next P x T ≤ n ^ T * Phi x) :
    ∀ x, I x →
      2 * wordSum next (miss P) x (2 * PhiMax) ≤
        n ^ (2 * PhiMax) := by
  have hcostUniform :
      ∀ x, I x → ¬ P x → ∀ T,
        costNumerator next P x T ≤ n ^ T * PhiMax := by
    intro x hxI hxP T
    exact Nat.le_trans
      (hcost x hxI hxP T)
      (Nat.mul_le_mul_left _ (hPhi x hxI hxP))
  exact
    markov_to_half_block
      next P I hP PhiMax hPhiMax hcostUniform

/-- Potential-valued Markov/restart composition.

At B = 2*PhiMax, half_block_restart gives the exact composed constant
4*PhiMax. -/
theorem restart_cost_of_potential_bound
    (next : S → Fin n → S) (P I : S → Prop)
    (hP : ∀ x e, P x → P (next x e))
    (hI : ∀ x e, I x → I (next x e))
    (Phi : S → Nat) (PhiMax : Nat) (hPhiMax : 0 < PhiMax)
    (hPhi : ∀ x, I x → ¬ P x → Phi x ≤ PhiMax)
    (hcost : ∀ x, I x → ¬ P x → ∀ T,
      costNumerator next P x T ≤ n ^ T * Phi x) :
    ∀ T x, I x →
      costNumerator next P x T ≤ n ^ T * (4 * PhiMax) := by
  have hb :=
    markov_to_half_block_of_potential
      next P I hP Phi PhiMax hPhiMax hPhi hcost
  have hrestart :=
    half_block_restart
      next P I hP hI (2 * PhiMax) (by omega)
      (fun x hxI _ => hb x hxI)
  intro T x hxI
  have h := hrestart T x hxI
  rw [show 2 * (2 * PhiMax) = 4 * PhiMax by omega] at h
  exact h

end PPL.Probability

#print axioms PPL.Probability.restartRestrict_missWordSum
#print axioms PPL.Probability.restartRestrict_costNumerator
#print axioms PPL.Probability.horizon_mul_missCount_le_costNumerator
#print axioms PPL.Probability.repeat_half_block_miss
#print axioms PPL.Probability.half_block_restart
#print axioms PPL.Probability.markov_to_half_block
#print axioms PPL.Probability.restart_cost_of_uniform_bound
#print axioms PPL.Probability.markov_to_half_block_of_potential
#print axioms PPL.Probability.restart_cost_of_potential_bound
