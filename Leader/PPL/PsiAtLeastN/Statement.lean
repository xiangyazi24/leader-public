import Leader.PPL.PsiAtLeastN.SafeTarget
import Leader.PPL.MainTheorem.PaperForm

/-!
# Paper-form Theorem 1 over the whole psi window, with the safe target (F.1b)

Paper Theorem 1 allows `log n ≤ psi ≤ log n + O(1)`, which for small `n`
includes `psi ≥ n`.  There the target `S_PL` is not reachable from a closed
class (ERRATA S3.14, `RiskyClass.lean`), so the whole-window statement is
made with the safe target `Theorem1SafeTarget` (`SafeTarget.lean`), which
contains `S_PL` and is closed and safe for every `n ≥ 3`, `psi ≥ 2`.

* `theorem1ReachesSafeTarget`, `theorem1SafeFailureNumerator`,
  `theorem1SafeCostNumerator`: the exact prefix test, failure numerator and
  truncated first-hit cost numerator of `Theorem1Statement`, with
  `Theorem1SafeTarget` in place of `SPL` (same `n^T` scheduler words).
* `Theorem1PsiAtLeastNStatement s` (**open**): whp and expected-cost bounds
  for reaching the safe target on `3 ≤ n ≤ psi ≤ log2 n + s`, with the same
  horizon `theorem1Horizon n psi` and constant 64.
* `Theorem1PaperFormSafeTarget s`: paper-form Theorem 1 on the whole window
  `psi ≤ log2 n + s` (no `psi < n`), with the safe target, the exact state
  count and the horizon bound.
* `theorem1PaperFormSafeTarget_of_psiAtLeastN`: the second follows from the
  first.  The `psi < n` half is `theorem1PaperForm_proved`, transported by
  monotonicity in the target (`SPL ⊆ Theorem1SafeTarget`):
  `theorem1SafeFailureNumerator_le` and `theorem1SafeCostNumerator_le`.
* `theorem1SafeWhp_of_le_64`: the whp clause is trivial for `n ≤ 64`
  (the bound `64 · n^H / n ≥ n^H`).  Since `n ≤ psi ≤ log2 n + s` forces
  `n ≤ 64` whenever `s ≤ 58`, the open whp content of
  `Theorem1PsiAtLeastNStatement s` is empty for `s ≤ 58`; the open content
  there is the expected-cost clause.
-/

namespace PPL.PsiAtLeastN

set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false

instance instDecidableTheorem1SafeTarget {n psi kappa : Nat}
    (ring : DirectedRing n) (C : Config n psi kappa) :
    Decidable (Theorem1SafeTarget ring C) := by
  unfold Theorem1SafeTarget
  infer_instance

/-- Exact prefix-hitting test for the safe target. -/
def theorem1ReachesSafeTarget
    {n psi kappa : Nat}
    (ring : DirectedRing n) :
    Config n psi kappa → DetSchedule n → Bool
  | C, [] =>
      decide (Theorem1SafeTarget ring C)
  | C, e :: rest =>
      decide (Theorem1SafeTarget ring C) ||
        theorem1ReachesSafeTarget ring
          (PopulationProtocol.step (protocol psi kappa) ring C e)
          rest

/-- Exact uniform-scheduler failure numerator for the safe target. -/
def theorem1SafeFailureNumerator
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (T : Nat) : Nat :=
  (allSchedules n T).countP
    (fun word => !(theorem1ReachesSafeTarget ring C word))

/-- Exact truncated first-hit cost numerator for the safe target. -/
noncomputable def theorem1SafeCostNumerator
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (T : Nat) : Nat :=
  K2ArbitraryElimination.FiniteAccounting.costNumerator
    (fun D e =>
      PopulationProtocol.step (protocol psi kappa) ring D e)
    (Theorem1SafeTarget ring)
    C T

/-! ## Monotonicity in the target -/

theorem spl_subset_theorem1SafeTarget
    {n psi kappa : Nat} {ring : DirectedRing n}
    {C : Config n psi kappa} (h : SPL ring C) :
    Theorem1SafeTarget ring C :=
  Or.inl h

theorem theorem1ReachesSafeTarget_of_reachesSPL
    {n psi kappa : Nat} (ring : DirectedRing n) :
    forall (C : Config n psi kappa) (word : DetSchedule n),
      theorem1ReachesSPL ring C word = true ->
        theorem1ReachesSafeTarget ring C word = true := by
  intro C word
  induction word generalizing C with
  | nil =>
      intro h
      simp only [theorem1ReachesSPL, decide_eq_true_eq] at h
      simp only [theorem1ReachesSafeTarget, decide_eq_true_eq]
      exact spl_subset_theorem1SafeTarget h
  | cons e rest ih =>
      intro h
      simp only [theorem1ReachesSPL, Bool.or_eq_true, decide_eq_true_eq] at h
      simp only [theorem1ReachesSafeTarget, Bool.or_eq_true, decide_eq_true_eq]
      rcases h with h | h
      · exact Or.inl (spl_subset_theorem1SafeTarget h)
      · exact Or.inr (ih _ h)

/-- The safe-target failure numerator is at most the `S_PL` one. -/
theorem theorem1SafeFailureNumerator_le
    {n psi kappa : Nat} (ring : DirectedRing n)
    (C : Config n psi kappa) (T : Nat) :
    theorem1SafeFailureNumerator ring C T <=
      theorem1FailureNumerator ring C T := by
  unfold theorem1SafeFailureNumerator theorem1FailureNumerator
  apply List.countP_mono_left
  intro word _ h
  cases hs : theorem1ReachesSPL ring C word with
  | false => rfl
  | true =>
      have := theorem1ReachesSafeTarget_of_reachesSPL ring C word hs
      rw [this] at h
      exact absurd h (by simp)

/-- First-hit cost is antitone in the target. -/
theorem costWord_antitone_target
    {S : Type} {n : Nat} (next : S → Fin n → S) (P P' : S → Prop)
    (hPP : forall x, P x -> P' x) :
    forall (x : S) (es : List (Fin n)),
      K2ArbitraryElimination.FiniteAccounting.costWord next P' x es <=
        K2ArbitraryElimination.FiniteAccounting.costWord next P x es := by
  classical
  intro x es
  induction es generalizing x with
  | nil =>
      simp [K2ArbitraryElimination.FiniteAccounting.costWord,
        K2FiniteSafeEliminationExpected.rawCost]
  | cons e es ih =>
      simp only [K2ArbitraryElimination.FiniteAccounting.costWord,
        K2FiniteSafeEliminationExpected.rawCost]
      by_cases h' : P' x
      · rw [if_pos h']
        exact Nat.zero_le _
      · have h : ¬ P x := fun hp => h' (hPP x hp)
        rw [if_neg h', if_neg h]
        have := ih (next x e)
        simp only [K2ArbitraryElimination.FiniteAccounting.costWord] at this
        exact Nat.add_le_add_left this 1

private theorem sum_map_le_sum_map
    {A : Type} (xs : List A) (f g : A → Nat)
    (h : forall x, f x <= g x) :
    (xs.map f).sum <= (xs.map g).sum := by
  induction xs with
  | nil => exact Nat.le_refl _
  | cons x xs ih =>
      simp only [List.map_cons, List.sum_cons]
      exact Nat.add_le_add (h x) ih

/-- The safe-target cost numerator is at most the `S_PL` one. -/
theorem theorem1SafeCostNumerator_le
    {n psi kappa : Nat} (ring : DirectedRing n)
    (C : Config n psi kappa) (T : Nat) :
    theorem1SafeCostNumerator ring C T <=
      theorem1CostNumerator ring C T := by
  unfold theorem1SafeCostNumerator theorem1CostNumerator
  unfold K2ArbitraryElimination.FiniteAccounting.costNumerator
  unfold FixedSpanRenewalPayload.wordSum
  apply sum_map_le_sum_map
  intro u
  exact costWord_antitone_target _ (SPL ring) (Theorem1SafeTarget ring)
    (fun _ h => spl_subset_theorem1SafeTarget h) C u.reverse

/-- For `n ≤ 64` the whp clause holds for any target: the failure numerator
is at most `n^H`. -/
theorem theorem1SafeWhp_of_le_64
    {n psi kappa : Nat} (hn64 : n <= 64) (ring : DirectedRing n)
    (C : Config n psi kappa) (H : Nat) :
    n * theorem1SafeFailureNumerator ring C H <= 64 * n ^ H := by
  have hle : theorem1SafeFailureNumerator ring C H <= n ^ H := by
    unfold theorem1SafeFailureNumerator
    rw [← allSchedules_length n H]
    exact List.countP_le_length
  exact Nat.mul_le_mul hn64 hle

/-! ## The open `psi ≥ n` statement and the whole-window paper form -/

/-- **Open (F.1b, part c).**  On `3 ≤ n ≤ psi ≤ log2 n + s`, the safe target
is reached within the Theorem-1 horizon with failure probability at most
`64/n`, and the truncated expected hitting time is at most
`cExpected · H`. -/
def Theorem1PsiAtLeastNStatement (s : Nat) : Prop :=
  Exists fun cExpected : Nat =>
    And (0 < cExpected)
      (forall {n psi : Nat},
        3 <= n ->
        2 <= psi ->
        n <= psi ->
        psi <= Nat.log2 n + s ->
        forall
          (ring : DirectedRing n)
          (C0 : Config n psi (theorem1Kappa psi)),
          let H := theorem1Horizon n psi
          And
            (n * theorem1SafeFailureNumerator ring C0 H <= 64 * n ^ H)
            (forall T : Nat,
              theorem1SafeCostNumerator ring C0 T <=
                n ^ T * (cExpected * H)))

/-- Paper-form Theorem 1 on the whole window `psi ≤ log2 n + s` (no
`psi < n`), with the safe target: safety of the target, whp and expected
cost of reaching it, the exact state count and the horizon bound. -/
def Theorem1PaperFormSafeTarget (s : Nat) : Prop :=
  Exists fun cExpected : Nat =>
    And (0 < cExpected)
      (And (32 * theorem1C17 + 352 <= theorem1C1)
        (And (theorem1C1 % 16 = 0)
          (forall {n psi : Nat},
            3 <= n ->
            2 <= psi ->
            n <= 2 ^ psi ->
            psi <= Nat.log2 n + s ->
            forall
              (ring : DirectedRing n)
              (C0 : Config n psi (theorem1Kappa psi)),
              let H := theorem1Horizon n psi
              And
                (forall C : Config n psi (theorem1Kappa psi),
                  Theorem1SafeTarget ring C ->
                    PopulationProtocol.IsSafe
                      (protocol psi (theorem1Kappa psi))
                      ring C PPL.Safety.SPL.output)
                (And
                  (n * theorem1SafeFailureNumerator ring C0 H <=
                    64 * n ^ H)
                  (And
                    (forall T : Nat,
                      theorem1SafeCostNumerator ring C0 T <=
                        n ^ T * (cExpected * H))
                    (And
                      (Exists fun N : Nat =>
                        And
                          (N <= 10 ^ 21 * (Nat.log2 n + s + 1) ^ 6)
                          (Exists fun decode :
                              Fin N -> (protocol psi (theorem1Kappa psi)).Q =>
                            And
                              (Function.Injective decode)
                              (Function.Surjective decode)))
                      (H <= 10 ^ 9 * 2 ^ s * n ^ 2 *
                        (Nat.log2 n + s + 1))))))))

/-- **Reduction.**  The whole-window paper form follows from the open
`psi ≥ n` statement; the `psi < n` half is proved
(`theorem1PaperForm_proved`), transported to the larger target. -/
theorem theorem1PaperFormSafeTarget_of_psiAtLeastN
    (s : Nat) (hge : Theorem1PsiAtLeastNStatement s) :
    Theorem1PaperFormSafeTarget s := by
  obtain ⟨c1, hc1, h1, h2, hlt⟩ := theorem1PaperForm_proved s
  obtain ⟨c2, hc2, hgeBody⟩ := hge
  refine ⟨c1 + c2, by omega, h1, h2, ?_⟩
  intro n psi hn3 hpsi hnpow hwin ring C0
  have hsafe :
      forall C : Config n psi (theorem1Kappa psi),
        Theorem1SafeTarget ring C ->
          PopulationProtocol.IsSafe
            (protocol psi (theorem1Kappa psi))
            ring C PPL.Safety.SPL.output :=
    fun C hC => theorem1SafeTarget_isSafe hn3 hpsi ring C hC
  have hcount :
      Exists fun N : Nat =>
        And
          (N <= 10 ^ 21 * (Nat.log2 n + s + 1) ^ 6)
          (Exists fun decode :
              Fin N -> (protocol psi (theorem1Kappa psi)).Q =>
            And
              (Function.Injective decode)
              (Function.Surjective decode)) := by
    refine
      ⟨(PPLv2.states psi (theorem1Kappa psi)).values.length, ?_,
        theorem1_stateCount_exact psi⟩
    have h := theorem1_stateCount_le s n psi hn3 hpsi hwin
    rw [theorem1StateD_eq] at h
    exact h
  have hhor :
      theorem1Horizon n psi <=
        10 ^ 9 * 2 ^ s * n ^ 2 * (Nat.log2 n + s + 1) := by
    have h := theorem1Horizon_le s n psi hn3 hpsi hnpow hwin
    rw [theorem1HorizonA_eq] at h
    exact h
  by_cases hsmall : psi < n
  · obtain ⟨_, hwhp, hcost, _, _⟩ :=
      hlt hn3 hpsi hnpow hwin hsmall ring C0
    refine ⟨hsafe, ?_, ?_, hcount, hhor⟩
    · exact Nat.le_trans
        (Nat.mul_le_mul_left n
          (theorem1SafeFailureNumerator_le ring C0 _))
        hwhp
    · intro T
      refine Nat.le_trans (theorem1SafeCostNumerator_le ring C0 T) ?_
      refine Nat.le_trans (hcost T) ?_
      exact Nat.mul_le_mul_left _
        (Nat.mul_le_mul_right _ (by omega))
  · have hle : n <= psi := by omega
    obtain ⟨hwhp, hcost⟩ := hgeBody hn3 hpsi hle hwin ring C0
    refine ⟨hsafe, hwhp, ?_, hcount, hhor⟩
    intro T
    refine Nat.le_trans (hcost T) ?_
    exact Nat.mul_le_mul_left _
      (Nat.mul_le_mul_right _ (by omega))

end PPL.PsiAtLeastN

#print axioms PPL.PsiAtLeastN.theorem1SafeFailureNumerator_le
#print axioms PPL.PsiAtLeastN.theorem1SafeCostNumerator_le
#print axioms PPL.PsiAtLeastN.theorem1SafeWhp_of_le_64
#print axioms PPL.PsiAtLeastN.theorem1PaperFormSafeTarget_of_psiAtLeastN
