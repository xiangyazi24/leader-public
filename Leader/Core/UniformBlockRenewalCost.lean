import Leader.Core.UniformBlockRenewal

namespace UniformBlockRenewalCost

open FiniteUniformStoppingTree
open UniformBlockRenewal

set_option autoImplicit false

/-! ## Active mass between block boundaries -/

private theorem treeWeight_add_horizon_cost
    {S : Type} {n : Nat}
    (step : S → Fin n → StopNode S)
    (weight : StopNode S → Nat) :
    ∀ x T T',
      treeWeight step weight x (T + T') =
        treeWeight step
          (fun y => treeWeight step weight y T') x T := by
  intro x T T'
  induction T generalizing x with
  | zero => rw [Nat.zero_add]; rfl
  | succ T ih =>
      simp only [Nat.succ_add, treeWeight]
      exact ofFn_sum_eq _ _ (fun e => ih (stepNode step x e))

private theorem activeCount_add_cost
    {S : Type} {n : Nat}
    (step : S → Fin n → StopNode S) (x : StopNode S) (T T' : Nat) :
    activeCount step x (T + T') =
      treeWeight step (fun y => activeCount step y T') x T := by
  simpa only [activeCount] using
    (treeWeight_add_horizon_cost step activeWeight x T T')

private theorem activeCount_le_pow_mul_activeWeight_cost
    {S : Type} {n : Nat} (step : S → Fin n → StopNode S) :
    ∀ x K,
      activeCount step x K ≤ n ^ K * activeWeight x := by
  intro x K
  cases x with
  | success =>
      simp [activeCount, treeWeight_success, activeWeight]
  | failure =>
      simp [activeCount, treeWeight_failure, activeWeight]
  | active s =>
      have hpartition := node_count_partition step (.active s) K
      simp only [activeWeight, Nat.mul_one]
      omega

private theorem activeCount_add_le_cost
    {S : Type} {n : Nat}
    (step : S → Fin n → StopNode S) (x : StopNode S) (T K : Nat) :
    activeCount step x (T + K) ≤
      n ^ K * activeCount step x T := by
  rw [activeCount_add_cost step x T K]
  calc
    treeWeight step (fun y => activeCount step y K) x T ≤
        treeWeight step (fun y => n ^ K * activeWeight y) x T :=
      treeWeight_mono step
        (fun y => activeCount step y K)
        (fun y => n ^ K * activeWeight y)
        (fun y => activeCount_le_pow_mul_activeWeight_cost step y K)
        x T
    _ = n ^ K * treeWeight step activeWeight x T :=
      treeWeight_mul_left step (n ^ K) activeWeight x T
    _ = n ^ K * activeCount step x T := rfl

/-- Extend the geometric block-tail estimate from the exact block boundary
`m * B` to every later horizon. -/
theorem activeCount_block_le
    {S : Type} {n K q q' : Nat}
    (step : S → Fin n → StopNode S)
    (hq' : 0 < q')
    (hnoFailure : ∀ state edge, step state edge ≠ .failure)
    (hblock : ∀ s : S,
      n ^ (q * K) ≤
        q' * successCount step (.active s) (q * K))
    (s₀ : S) (m T : Nat)
    (hT : m * (q * K) ≤ T) :
    q' ^ m * activeCount step (.active s₀) T ≤
      (q' - 1) ^ m * n ^ T := by
  obtain ⟨R, hR⟩ := Nat.exists_eq_add_of_le hT
  have hfuture :=
    activeCount_add_le_cost step (.active s₀) (m * (q * K)) R
  have htail :
      q' ^ m * activeCount step (.active s₀) (m * (q * K)) ≤
        (q' - 1) ^ m * n ^ (m * (q * K)) := by
    simpa [retry] using
      (UniformBlockRenewal.block_tail
        step hq' hnoFailure hblock s₀ m)
  rw [hR]
  calc
    q' ^ m *
        activeCount step (.active s₀) (m * (q * K) + R) ≤
      q' ^ m *
        (n ^ R * activeCount step (.active s₀) (m * (q * K))) :=
      Nat.mul_le_mul_left _ hfuture
    _ = n ^ R *
        (q' ^ m * activeCount step (.active s₀) (m * (q * K))) := by
      ac_rfl
    _ ≤ n ^ R *
        ((q' - 1) ^ m * n ^ (m * (q * K))) :=
      Nat.mul_le_mul_left _ htail
    _ = (q' - 1) ^ m * n ^ (m * (q * K) + R) := by
      rw [Nat.pow_add]
      ac_rfl

/-! ## Truncated-cost algebra -/

/-- Exact one-horizon increment identity.  This is the division-free form of
`E[min(τ,T+1)] = E[min(τ,T)] + P(τ>T)`. -/
theorem truncatedActiveCostNumerator_succ_eq
    {S : Type} {n : Nat} (step : S → Fin n → StopNode S) :
    ∀ (x : StopNode S) T,
      truncatedActiveCostNumerator step x (T + 1) =
        n * truncatedActiveCostNumerator step x T +
          n * activeCount step x T := by
  intro x T
  induction T generalizing x with
  | zero =>
      cases x <;>
        simp [truncatedActiveCostNumerator, activeCount, treeWeight,
          activeWeight, ofFn_sum_const]
  | succ T ih =>
      cases x with
      | success =>
          simp [truncatedActiveCostNumerator, activeCount,
            treeWeight_success, activeWeight]
      | failure =>
          simp [truncatedActiveCostNumerator, activeCount,
            treeWeight_failure, activeWeight]
      | active s =>
          have hsum :
              (List.ofFn (fun e : Fin n =>
                truncatedActiveCostNumerator step (step s e) (T + 1))).sum =
                n * (List.ofFn (fun e : Fin n =>
                  truncatedActiveCostNumerator step (step s e) T)).sum +
                n * (List.ofFn (fun e : Fin n =>
                  activeCount step (step s e) T)).sum := by
            calc
              (List.ofFn (fun e : Fin n =>
                  truncatedActiveCostNumerator step
                    (step s e) (T + 1))).sum =
                (List.ofFn (fun e : Fin n =>
                  n * truncatedActiveCostNumerator step (step s e) T +
                    n * activeCount step (step s e) T)).sum := by
                  exact ofFn_sum_eq _ _ (fun e => ih (step s e))
              _ =
                  (List.ofFn (fun e : Fin n =>
                    n * truncatedActiveCostNumerator step (step s e) T)).sum +
                  (List.ofFn (fun e : Fin n =>
                    n * activeCount step (step s e) T)).sum :=
                ofFn_sum_add _ _
              _ = n * (List.ofFn (fun e : Fin n =>
                    truncatedActiveCostNumerator step (step s e) T)).sum +
                  n * (List.ofFn (fun e : Fin n =>
                    activeCount step (step s e) T)).sum := by
                rw [ofFn_sum_mul_left, ofFn_sum_mul_left]
          simp only [truncatedActiveCostNumerator, Nat.succ_eq_add_one]
          rw [hsum]
          simp only [activeCount, treeWeight, stepNode]
          simp only [Nat.pow_succ, Nat.mul_add]
          ac_rfl

/-- Concatenate `K` more raw scheduler steps.  Every one of the `K` added
interactions is charged only on words still active at the original horizon. -/
theorem truncatedActiveCostNumerator_add_le
    {S : Type} {n : Nat} (step : S → Fin n → StopNode S) :
    ∀ (x : StopNode S) T K,
      truncatedActiveCostNumerator step x (T + K) ≤
        n ^ K * truncatedActiveCostNumerator step x T +
          K * n ^ K * activeCount step x T := by
  intro x T K
  induction K with
  | zero => simp
  | succ K ih =>
      rw [Nat.add_succ, truncatedActiveCostNumerator_succ_eq]
      have hactive := activeCount_add_le_cost step x T K
      calc
        n * truncatedActiveCostNumerator step x (T + K) +
            n * activeCount step x (T + K) ≤
          n * (n ^ K * truncatedActiveCostNumerator step x T +
            K * n ^ K * activeCount step x T) +
            n * (n ^ K * activeCount step x T) :=
          Nat.add_le_add
            (Nat.mul_le_mul_left n ih)
            (Nat.mul_le_mul_left n hactive)
        _ = n ^ Nat.succ K * truncatedActiveCostNumerator step x T +
            Nat.succ K * n ^ Nat.succ K * activeCount step x T := by
          rw [Nat.pow_succ]
          simp only [Nat.succ_eq_add_one, Nat.mul_add, Nat.add_mul,
            Nat.one_mul]
          ac_rfl

/-! ## Natural geometric credit -/

/-- The scaled sum of block-survival terms accumulated before block `m`. -/
def geometricCredit (q' : Nat) : Nat → Nat
  | 0 => 0
  | m + 1 =>
      q' * geometricCredit q' m + q' * (q' - 1) ^ m

/-- Telescoping identity for the natural geometric sum. -/
theorem geometricCredit_add_tail
    (q' m : Nat) (hq' : 0 < q') :
    geometricCredit q' m + q' * (q' - 1) ^ m =
      q' ^ Nat.succ m := by
  induction m with
  | zero =>
      simp [geometricCredit]
  | succ m ih =>
      have hpred : 1 + (q' - 1) = q' := by omega
      have hpow :
          (q' - 1) ^ m + (q' - 1) ^ Nat.succ m =
            q' * (q' - 1) ^ m := by
        rw [Nat.pow_succ]
        calc
          (q' - 1) ^ m + (q' - 1) ^ m * (q' - 1) =
              (q' - 1) ^ m * (1 + (q' - 1)) := by
            rw [Nat.mul_add]
            simp
          _ = (q' - 1) ^ m * q' := by rw [hpred]
          _ = q' * (q' - 1) ^ m := Nat.mul_comm _ _
      rw [geometricCredit]
      calc
        q' * geometricCredit q' m + q' * (q' - 1) ^ m +
            q' * (q' - 1) ^ Nat.succ m =
          q' * (geometricCredit q' m +
            ((q' - 1) ^ m + (q' - 1) ^ Nat.succ m)) := by
          simp only [Nat.mul_add]
          ac_rfl
        _ = q' * (geometricCredit q' m + q' * (q' - 1) ^ m) := by
          rw [hpow]
        _ = q' * q' ^ Nat.succ m := by rw [ih]
        _ = q' ^ Nat.succ (Nat.succ m) := by
          simp [Nat.pow_succ, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]

/-- In particular the accumulated geometric credit is at most the next power
of `q'`. -/
theorem geometricCredit_le_pow_succ
    (q' m : Nat) (hq' : 0 < q') :
    geometricCredit q' m ≤ q' ^ Nat.succ m := by
  have h := geometricCredit_add_tail q' m hq'
  omega

private theorem block_boundary_cost_scaled
    {S : Type} {n B q' : Nat}
    (step : S → Fin n → StopNode S) (x : StopNode S)
    (htail : ∀ m,
      q' ^ m * activeCount step x (m * B) ≤
        (q' - 1) ^ m * n ^ (m * B)) :
    ∀ m,
      q' ^ m * truncatedActiveCostNumerator step x (m * B) ≤
        n ^ (m * B) * B * geometricCredit q' m := by
  intro m
  induction m with
  | zero =>
      simp [truncatedActiveCostNumerator, geometricCredit]
  | succ m ih =>
      have hcost :=
        truncatedActiveCostNumerator_add_le step x (m * B) B
      have htailm := htail m
      calc
        q' ^ Nat.succ m *
            truncatedActiveCostNumerator step x (Nat.succ m * B) =
          q' ^ Nat.succ m *
            truncatedActiveCostNumerator step x (m * B + B) := by
          rw [Nat.succ_mul]
        _ ≤ q' ^ Nat.succ m *
            (n ^ B * truncatedActiveCostNumerator step x (m * B) +
              B * n ^ B * activeCount step x (m * B)) :=
          Nat.mul_le_mul_left _ hcost
        _ = q' * n ^ B *
              (q' ^ m * truncatedActiveCostNumerator step x (m * B)) +
            q' * B * n ^ B *
              (q' ^ m * activeCount step x (m * B)) := by
          rw [Nat.pow_succ, Nat.mul_add]
          ac_rfl
        _ ≤ q' * n ^ B *
              (n ^ (m * B) * B * geometricCredit q' m) +
            q' * B * n ^ B *
              ((q' - 1) ^ m * n ^ (m * B)) :=
          Nat.add_le_add
            (Nat.mul_le_mul_left (q' * n ^ B) ih)
            (Nat.mul_le_mul_left (q' * B * n ^ B) htailm)
        _ = n ^ (Nat.succ m * B) * B *
              geometricCredit q' (Nat.succ m) := by
          rw [geometricCredit, Nat.succ_mul, Nat.pow_add]
          simp only [Nat.mul_add]
          ac_rfl

/-- At exact block boundaries the truncated expected-cost numerator already
has the stronger `q' * B` bound. -/
theorem truncatedActiveCostNumerator_block_boundary_le
    {S : Type} {n B q' : Nat}
    (step : S → Fin n → StopNode S) (x : StopNode S)
    (hq' : 0 < q')
    (htail : ∀ m,
      q' ^ m * activeCount step x (m * B) ≤
        (q' - 1) ^ m * n ^ (m * B))
    (m : Nat) :
    truncatedActiveCostNumerator step x (m * B) ≤
      n ^ (m * B) * (q' * B) := by
  have hscaled := block_boundary_cost_scaled step x htail m
  have hgeom := geometricCredit_le_pow_succ q' m hq'
  have hupper :
      q' ^ m * truncatedActiveCostNumerator step x (m * B) ≤
        n ^ (m * B) * B * q' ^ Nat.succ m :=
    Nat.le_trans hscaled
      (Nat.mul_le_mul_left (n ^ (m * B) * B) hgeom)
  have hmul :
      q' ^ m * truncatedActiveCostNumerator step x (m * B) ≤
        q' ^ m * (n ^ (m * B) * (q' * B)) := by
    calc
      q' ^ m * truncatedActiveCostNumerator step x (m * B) ≤
          n ^ (m * B) * B * q' ^ Nat.succ m := hupper
      _ = q' ^ m * (n ^ (m * B) * (q' * B)) := by
        rw [Nat.pow_succ]
        ac_rfl
  exact Nat.le_of_mul_le_mul_left hmul (Nat.pow_pos hq')

private theorem normalized_truncated_cost_of_horizon_le
    {S : Type} {n T U bound : Nat}
    (step : S → Fin n → StopNode S) (x : StopNode S)
    (hn : 0 < n) (hTU : T ≤ U)
    (hU : truncatedActiveCostNumerator step x U ≤ n ^ U * bound) :
    truncatedActiveCostNumerator step x T ≤ n ^ T * bound := by
  obtain ⟨R, hR⟩ := Nat.exists_eq_add_of_le hTU
  subst U
  have hmono :=
    pow_mul_truncatedActiveCostNumerator_le_add step x T R
  have hbound :
      truncatedActiveCostNumerator step x (T + R) ≤
        n ^ R * (n ^ T * bound) := by
    calc
      truncatedActiveCostNumerator step x (T + R) ≤
          n ^ (T + R) * bound := hU
      _ = n ^ R * (n ^ T * bound) := by
        rw [Nat.pow_add]
        ac_rfl
  have hscaled := Nat.le_trans hmono hbound
  exact Nat.le_of_mul_le_mul_left hscaled (Nat.pow_pos hn)

/-- Full geometric-tail-to-expected-cost conversion.  This proves the stronger
normalized bound `E[min(τ,T)] ≤ q' * B` for `B = q * K`. -/
theorem truncatedActiveCostNumerator_block_geometric_le
    {S : Type} {n K q q' : Nat}
    (step : S → Fin n → StopNode S)
    (hq' : 0 < q')
    (hnoFailure : ∀ state edge, step state edge ≠ .failure)
    (hblock : ∀ s : S,
      n ^ (q * K) ≤
        q' * successCount step (.active s) (q * K))
    (s₀ : S) (T : Nat) :
    truncatedActiveCostNumerator step (.active s₀) T ≤
      n ^ T * (q' * (q * K)) := by
  have hB : 0 < q * K := by
    by_cases hzero : q * K = 0
    · have hs := hblock s₀
      rw [hzero] at hs
      have hbad : (1 : Nat) ≤ 0 := by
        simpa [successCount, treeWeight, successWeight] using hs
      omega
    · omega
  have htail : ∀ m,
      q' ^ m * activeCount step (.active s₀) (m * (q * K)) ≤
        (q' - 1) ^ m * n ^ (m * (q * K)) := by
    intro m
    simpa [retry] using
      (UniformBlockRenewal.block_tail
        step hq' hnoFailure hblock s₀ m)
  have hboundary :=
    truncatedActiveCostNumerator_block_boundary_le
      (step := step) (x := (.active s₀))
      (B := q * K) (q' := q') hq' htail T
  by_cases hnzero : n = 0
  · subst n
    cases T with
    | zero =>
        simp [truncatedActiveCostNumerator]
    | succ T =>
        have htriv :=
          truncatedActiveCostNumerator_add_le
            (step := step) (.active s₀) 0 (Nat.succ T)
        simpa [truncatedActiveCostNumerator, activeCount, treeWeight,
          activeWeight] using htriv
  · have hn : 0 < n := Nat.pos_of_ne_zero hnzero
    have hB1 : 1 ≤ q * K := by omega
    have hTU : T ≤ T * (q * K) := by
      have hmul := Nat.mul_le_mul_left T hB1
      simpa using hmul
    exact normalized_truncated_cost_of_horizon_le
      (step := step) (x := (.active s₀))
      (hn := hn) (hTU := hTU) hboundary

/-- Requested looser interface: for `2 ≤ q'`, the normalized truncated
expected time is at most `2 * q' * B`, uniformly in the horizon. -/
theorem truncatedActiveCostNumerator_block_le
    {S : Type} {n K q q' : Nat}
    (step : S → Fin n → StopNode S)
    (hq' : 2 ≤ q')
    (hnoFailure : ∀ state edge, step state edge ≠ .failure)
    (hblock : ∀ s : S,
      n ^ (q * K) ≤
        q' * successCount step (.active s) (q * K))
    (s₀ : S) (T : Nat) :
    truncatedActiveCostNumerator step (.active s₀) T ≤
      n ^ T * (2 * q' * (q * K)) := by
  have hstrong :=
    truncatedActiveCostNumerator_block_geometric_le
      step (by omega : 0 < q') hnoFailure hblock s₀ T
  calc
    truncatedActiveCostNumerator step (.active s₀) T ≤
        n ^ T * (q' * (q * K)) := hstrong
    _ ≤ n ^ T * (2 * q' * (q * K)) := by
      exact Nat.mul_le_mul_left (n ^ T) (by
        have hz := Nat.mul_le_mul_right (q' * (q * K))
          (show 1 ≤ 2 by decide)
        simpa [Nat.mul_assoc] using hz)

#print axioms activeCount_block_le
#print axioms truncatedActiveCostNumerator_succ_eq
#print axioms truncatedActiveCostNumerator_add_le
#print axioms geometricCredit_add_tail
#print axioms truncatedActiveCostNumerator_block_boundary_le
#print axioms truncatedActiveCostNumerator_block_geometric_le
#print axioms truncatedActiveCostNumerator_block_le

end UniformBlockRenewalCost
