import Leader.Core.BalancedFailureRestart
import Leader.Core.BellmanWhp


namespace UniformBlockRenewal


open FiniteUniformStoppingTree


set_option autoImplicit false


/-- The retry process is the same one-step stopped transition. -/
def retry {S : Type} {n : Nat}
    (step : S → Fin n → StopNode S) : S → Fin n → StopNode S :=
  step


/-- One-step entrance-class closure is unchanged by the `retry` wrapper. -/
theorem retry_active_closed
    {S : Type} {n : Nat}
    (step : S → Fin n → StopNode S) (E : S → Prop)
    (hE : ∀ s, E s → ∀ (e : Fin n) (s' : S),
      step s e = .active s' → E s') :
    ∀ s, E s → ∀ (e : Fin n) (s' : S),
      retry step s e = .active s' → E s' := by
  simpa [retry] using hE


/-- Split a stopped scheduler tree at two successive horizons. -/
private theorem treeWeight_add_horizon
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


/-- Horizon splitting specialized to active leaf mass. -/
private theorem activeCount_add
    {S : Type} {n : Nat}
    (step : S → Fin n → StopNode S) (x : StopNode S) (T T' : Nat) :
    activeCount step x (T + T') =
      treeWeight step (fun y => activeCount step y T') x T := by
  simpa only [activeCount] using
    (treeWeight_add_horizon step activeWeight x T T')


/-- A pointwise block contraction lifts through an arbitrary active frontier. -/
private theorem factor_mul_activeCount_add_block_le
    {S : Type} {n L factor residual : Nat}
    (step : S → Fin n → StopNode S)
    (hblock : ∀ y,
      factor * activeCount step y L ≤
        residual * n ^ L * activeWeight y)
    (x : StopNode S) (T : Nat) :
    factor * activeCount step x (T + L) ≤
      residual * n ^ L * activeCount step x T := by
  rw [activeCount_add step x T L]
  calc
    factor * treeWeight step (fun y => activeCount step y L) x T =
        treeWeight step (fun y => factor * activeCount step y L) x T :=
      (treeWeight_mul_left step factor
        (fun y => activeCount step y L) x T).symm
    _ ≤ treeWeight step
          (fun y => residual * n ^ L * activeWeight y) x T :=
      treeWeight_mono step
        (fun y => factor * activeCount step y L)
        (fun y => residual * n ^ L * activeWeight y)
        hblock x T
    _ = residual * n ^ L * treeWeight step activeWeight x T :=
      treeWeight_mul_left step (residual * n ^ L) activeWeight x T
    _ = residual * n ^ L * activeCount step x T := rfl


/-- H2 plus absence of failure gives the one-block division-free contraction
`q' * active ≤ (q' - 1) * total` at every stopped node. -/
private theorem block_active_contraction
    {S : Type} {n L q' : Nat}
    (step : S → Fin n → StopNode S)
    (hq' : 0 < q')
    (hnoFailure : ∀ state edge, step state edge ≠ .failure)
    (hsuccess : ∀ s : S,
      n ^ L ≤ q' * successCount step (.active s) L) :
    ∀ y,
      q' * activeCount step y L ≤
        (q' - 1) * n ^ L * activeWeight y := by
  intro y
  cases y with
  | success =>
      simp [activeCount, activeWeight, treeWeight_success]
  | failure =>
      simp [activeCount, activeWeight, treeWeight_failure]
  | active s =>
      have hfailure :=
        BalancedFailureRestart.failureCount_eq_zero_of_step_ne_failure
          step hnoFailure s L
      have hpartition := node_count_partition step (.active s) L
      have hsum :
          activeCount step (.active s) L +
            successCount step (.active s) L = n ^ L := by
        omega
      have hsucc := hsuccess s
      obtain ⟨r, hr⟩ :=
        Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hq')
      subst q'
      simp only [Nat.add_sub_cancel, Nat.succ_eq_add_one] at hsucc ⊢
      rw [← hsum] at hsucc ⊢
      rw [Nat.mul_add]
      simp only [Nat.add_mul, Nat.one_mul, activeWeight, Nat.mul_one] at hsucc ⊢
      omega


/-- Iterating a uniform block contraction gives a geometric active tail. -/
private theorem geometric_tail_of_block_contraction
    {S : Type} {n L factor residual : Nat}
    (step : S → Fin n → StopNode S)
    (hblock : ∀ y,
      factor * activeCount step y L ≤
        residual * n ^ L * activeWeight y)
    (x : StopNode S) :
    ∀ m,
      factor ^ m * activeCount step x (m * L) ≤
        residual ^ m * n ^ (m * L) := by
  intro m
  induction m with
  | zero =>
      cases x <;> simp [activeCount, treeWeight, activeWeight]
  | succ m ih =>
      have hstep :=
        factor_mul_activeCount_add_block_le
          step hblock x (m * L)
      calc
        factor ^ Nat.succ m *
            activeCount step x (Nat.succ m * L) =
          factor ^ m *
            (factor * activeCount step x (m * L + L)) := by
              simp only [Nat.pow_succ, Nat.succ_mul]
              ac_rfl
        _ ≤ factor ^ m *
              (residual * n ^ L * activeCount step x (m * L)) :=
          Nat.mul_le_mul_left _ hstep
        _ = residual * n ^ L *
              (factor ^ m * activeCount step x (m * L)) := by
          ac_rfl
        _ ≤ residual * n ^ L *
              (residual ^ m * n ^ (m * L)) :=
          Nat.mul_le_mul_left _ ih
        _ = residual ^ Nat.succ m *
              n ^ (Nat.succ m * L) := by
          rw [Nat.pow_succ, Nat.succ_mul, Nat.pow_add]
          ac_rfl


/-- Geometric block tail from the stated global success-mass hypothesis H2. -/
theorem block_tail
    {S : Type} {n K q q' : Nat}
    (step : S → Fin n → StopNode S)
    (hq' : 0 < q')
    (hnoFailure : ∀ state edge, step state edge ≠ .failure)
    (hblock : ∀ s : S,
      n ^ (q * K) ≤
        q' * successCount step (.active s) (q * K))
    (s₀ : S) (m : Nat) :
    q' ^ m *
        activeCount (retry step) (.active s₀) (m * (q * K)) ≤
      (q' - 1) ^ m * n ^ (m * (q * K)) := by
  have hpoint :=
    block_active_contraction
      (step := step) (L := q * K) (q' := q')
      hq' hnoFailure hblock
  have htail :=
    geometric_tail_of_block_contraction
      (step := step) (L := q * K)
      (factor := q') (residual := q' - 1)
      hpoint (.active s₀) m
  simpa [retry] using htail


/-- WHP-style arithmetic corollary: any scaled geometric budget can be
cancelled against the positive factor `q'^m`. -/
theorem block_tail_whp
    {S : Type} {n K q q' : Nat}
    (step : S → Fin n → StopNode S)
    (hq' : 0 < q')
    (hnoFailure : ∀ state edge, step state edge ≠ .failure)
    (hblock : ∀ s : S,
      n ^ (q * K) ≤
        q' * successCount step (.active s) (q * K))
    (s₀ : S) (m budget : Nat)
    (hbudget :
      (q' - 1) ^ m * n ^ (m * (q * K)) ≤ q' ^ m * budget) :
    activeCount (retry step) (.active s₀) (m * (q * K)) ≤ budget := by
  have htail := block_tail step hq' hnoFailure hblock s₀ m
  have hmul :
      q' ^ m * activeCount (retry step) (.active s₀) (m * (q * K)) ≤
        q' ^ m * budget :=
    Nat.le_trans htail hbudget
  exact Nat.le_of_mul_le_mul_left hmul (Nat.pow_pos hq')


/-- H1 alone already gives the stronger whole-process Bellman certificate:
`retry` is definitionally `step`, so the original potential itself works. -/
theorem retry_bellman_strong
    {S : Type} {n K : Nat}
    (step : S → Fin n → StopNode S)
    (E : S → Prop) (W : StopNode S → Nat)
    (hsuper : NatBellmanSuperSolution step 1 W)
    (hbound : ∀ x, W x ≤ K) :
    ∃ U : StopNode S → Nat,
      NatBellmanSuperSolution (retry step) 1 U ∧
        ∀ s, E s → U (.active s) ≤ K := by
  refine ⟨W, ?_, ?_⟩
  · simpa [retry] using hsuper
  · intro s _
    exact hbound (.active s)


/-- Requested renewal API with the explicit coefficient `q'' = q * q'`.
The no-failure, block-success, and entrance-closure hypotheses are retained in
this interface, although the Bellman conclusion itself is already implied by
H1 and is therefore stronger than what renewal is needed to prove. -/
theorem retry_bellman
    {S : Type} {n K q q' : Nat}
    (step : S → Fin n → StopNode S)
    (E : S → Prop) (W : StopNode S → Nat)
    (hsuper : NatBellmanSuperSolution step 1 W)
    (hbound : ∀ x, W x ≤ K)
    (_hnoFailure : ∀ state edge, step state edge ≠ .failure)
    (_hblock : ∀ s : S,
      n ^ (q * K) ≤
        q' * successCount step (.active s) (q * K))
    (_hE : ∀ s, E s → ∀ (e : Fin n) (s' : S),
      step s e = .active s' → E s')
    (hq : 0 < q) (hq' : 0 < q') :
    ∃ U : StopNode S → Nat,
      NatBellmanSuperSolution (retry step) 1 U ∧
        ∀ s, E s → U (.active s) ≤ (q * q') * K := by
  obtain ⟨U, hU, hUK⟩ :=
    retry_bellman_strong step E W hsuper hbound
  have hq1 : 1 ≤ q := by omega
  have hq'1 : 1 ≤ q' := by omega
  have hfactor : 1 ≤ q * q' := by
    calc
      1 ≤ q := hq1
      _ = q * 1 := by simp
      _ ≤ q * q' := Nat.mul_le_mul_left q hq'1
  have hscale : K ≤ (q * q') * K := by
    simpa using (Nat.mul_le_mul_right K hfactor)
  refine ⟨U, hU, ?_⟩
  intro s hs
  exact Nat.le_trans (hUK s hs) hscale


#print axioms retry_active_closed
#print axioms block_tail
#print axioms block_tail_whp
#print axioms retry_bellman_strong
#print axioms retry_bellman


end UniformBlockRenewal
