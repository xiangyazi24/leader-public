import Leader.PPL.Elim.AttemptRetryModerate


/-!
# LD(736): moderate retry stage lift


Truth audit of the concrete kernel:


* `.junk` always steps to `.success`.
* `.attackCR`, `.targetCR`, `.dummyWait`, and `.stuck` never produce
  `.retry`.
* `.vulnerable` never produces `.retry`; its unique failure port is
  `targetPhase = .ready ∧ e = R_j F`, and that branch enters `.recovery`.
* `.recovery` is the only stage whose step can produce `.retry`, namely
  when `nextB targetPhase = .ready`.


Hence every completed retry lies downstream of a vulnerable failure.  There
is no bypass path.


What is still not stored by `ModerateAttemptState` is the proof payload
needed to identify the first vulnerable state with the File-5
`VulnerableState`: the two `PhaseHolds` witnesses and
`targetUnshielded`.  The generic finite-prefix splice is proved below; the
only remaining physical obligation is the final per-stage relation
`ModerateFirstVulnerableSpliceSpec`.
-/


namespace PPL.Convergence.LDLocal


set_option autoImplicit false
set_option Elab.async false


open FiniteUniformStoppingTree


/-! ## Generic retry/failure comparison -/


/-- Every retry numerator is bounded by the full scheduler mass. -/
theorem retryCount_le_pow
    {A S : Type} {n : Nat}
    (K : RetryKernel A S n) :
    ∀ x T, retryCount K x T ≤ n ^ T := by
  intro x T
  induction T generalizing x with
  | zero =>
      cases x <;> simp [retryCount]
  | succ T ih =>
      cases x with
      | success =>
          simp [retryCount]
      | retry s =>
          simp [retryCount]
      | active a =>
          simp only [retryCount]
          calc
            (List.ofFn (fun e : Fin n =>
                retryCount K (K.step a e) T)).sum
                ≤
              (List.ofFn (fun _ : Fin n => n ^ T)).sum :=
                ofFn_sum_le _ _ (fun e => ih (K.step a e))
            _ = n * n ^ T :=
              ofFn_sum_const n (n ^ T)
            _ = n ^ (T + 1) := by
              rw [Nat.pow_succ]
              ac_rfl


private theorem moderateLift_sum_ofFn_zero :
    ∀ m : Nat, (List.ofFn (fun _ : Fin m => (0 : Nat))).sum = 0
  | 0 => rfl
  | m + 1 => by
      rw [List.ofFn_succ, List.sum_cons, moderateLift_sum_ofFn_zero m]

theorem failureCount_success_eq_zero
    {V : Type} {n : Nat}
    (step : V → Fin n → StopNode V) :
    ∀ T, failureCount step (.success) T = 0 := by
  intro T
  induction T with
  | zero =>
      rfl
  | succ T ih =>
      change
        (List.ofFn (fun _ : Fin n =>
          failureCount step (.success) T)).sum = 0
      rw [ofFn_sum_eq _ (fun _ : Fin n => 0) (fun _ => ih)]
      exact moderateLift_sum_ofFn_zero n


theorem failureCount_failure_eq_pow
    {V : Type} {n : Nat}
    (step : V → Fin n → StopNode V) :
    ∀ T, failureCount step (.failure) T = n ^ T := by
  intro T
  induction T with
  | zero =>
      rfl
  | succ T ih =>
      change
        (List.ofFn (fun _ : Fin n =>
          failureCount step (.failure) T)).sum = n ^ (T + 1)
      rw [ofFn_sum_eq _ (fun _ : Fin n => n ^ T) (fun _ => ih),
        ofFn_sum_const, Nat.pow_succ]
      ac_rfl


/-- A relation between an attempt state and a stopped vulnerable state.
Success and active vulnerable children must be reproduced exactly by the
attempt kernel.  No condition is needed on a vulnerable failure child:
the failure leaf already contributes the entire remaining scheduler mass,
which dominates any later recovery/retry behavior. -/
structure RetryFailureSimulation
    {A S V : Type} {n : Nat}
    (K : RetryKernel A S n)
    (vstep : V → Fin n → StopNode V)
    (rel : A → V → Prop) : Prop where
  success :
    ∀ a v e,
      rel a v →
      vstep v e = .success →
      K.step a e = .success
  active :
    ∀ a v e v',
      rel a v →
      vstep v e = .active v' →
      ∃ a',
        K.step a e = .active a' ∧
        rel a' v'


/-- A related concrete attempt subtree has no more completed retries than
the failure mass of the vulnerable stopped tree.  Recovery after a vulnerable
failure is charged by `retryCount_le_pow`. -/
theorem retryCount_le_failureCount_of_sim
    {A S V : Type} {n : Nat}
    (K : RetryKernel A S n)
    (vstep : V → Fin n → StopNode V)
    (rel : A → V → Prop)
    (hsim : RetryFailureSimulation K vstep rel) :
    ∀ a v,
      rel a v →
      ∀ T,
        retryCount K (.active a) T ≤
          failureCount vstep (.active v) T := by
  intro a v hrel T
  induction T generalizing a v with
  | zero =>
      exact Nat.le_refl _
  | succ T ih =>
      change
        (List.ofFn (fun e : Fin n =>
          retryCount K (K.step a e) T)).sum ≤
        (List.ofFn (fun e : Fin n =>
          failureCount vstep (vstep v e) T)).sum
      apply ofFn_sum_le
      intro e
      cases hv : vstep v e with
      | success =>
          have hk :=
            hsim.success a v e hrel hv
          rw [hk]
          exact
            Nat.le_of_eq
              (by
                rw [failureCount_success_eq_zero vstep T]
                cases T <;> rfl)
      | failure =>
          have hp :=
            retryCount_le_pow K (K.step a e) T
          rw [failureCount_failure_eq_pow vstep T]
          exact hp
      | active v' =>
          obtain ⟨a', hk, hr⟩ :=
            hsim.active a v e v' hrel hv
          rw [hk]
          exact ih a' v' hr


/-! ## Generic first-entry finite-prefix splice -/


/-- Preparation prefixes contribute no retry.  When a first vulnerable entry
is reached, the related vulnerable failure tree supplies the entire retry
budget for the rest of the horizon.  This is the finite-prefix splice needed
by the concrete moderate monitor. -/
theorem retryCount_splice_first_entry
    {A S V : Type} {n q c : Nat}
    (K : RetryKernel A S n)
    (vstep : V → Fin n → StopNode V)
    (pre : A → Prop)
    (rel : A → V → Prop)
    (entry : V → Prop)
    (hsim : RetryFailureSimulation K vstep rel)
    (hpre :
      ∀ a e,
        pre a →
        K.step a e = .success ∨
          ∃ a',
            K.step a e = .active a' ∧
              (pre a' ∨
                ∃ v,
                  entry v ∧ rel a' v))
    (hentry :
      ∀ v,
        entry v →
        ∀ T,
          q * failureCount vstep (.active v) T ≤
            c * n ^ T) :
    ∀ a,
      pre a →
      ∀ T,
        q * retryCount K (.active a) T ≤
          c * n ^ T := by
  intro a ha T
  induction T generalizing a with
  | zero =>
      simp [retryCount]
  | succ T ih =>
      change
        q *
            (List.ofFn (fun e : Fin n =>
              retryCount K (K.step a e) T)).sum ≤
          c * n ^ (T + 1)
      have hchild :
          ∀ e : Fin n,
            q * retryCount K (K.step a e) T ≤
              c * n ^ T := by
        intro e
        rcases hpre a e ha with hs | ⟨a', hs, hnext⟩
        · rw [hs]
          simp [retryCount]
        · rw [hs]
          rcases hnext with hpre' | ⟨v, hentryV, hrel⟩
          · exact ih a' hpre'
          · have hdom :=
              retryCount_le_failureCount_of_sim
                K vstep rel hsim a' v hrel T
            exact
              Nat.le_trans
                (Nat.mul_le_mul_left q hdom)
                (hentry v hentryV T)
      calc
        q *
            (List.ofFn (fun e : Fin n =>
              retryCount K (K.step a e) T)).sum =
          (List.ofFn (fun e : Fin n =>
            q * retryCount K (K.step a e) T)).sum :=
              (ofFn_sum_mul_left q _).symm
        _ ≤
          (List.ofFn
            (fun _ : Fin n => c * n ^ T)).sum :=
              ofFn_sum_le _ _ hchild
        _ = n * (c * n ^ T) :=
          ofFn_sum_const n (c * n ^ T)
        _ = c * n ^ (T + 1) := by
          rw [Nat.pow_succ]
          ac_rfl


/-! ## One remaining concrete per-stage obligation -/


/-- Physical stage relation still to discharge.


The intended witness `pre` contains exactly junk/stuck and the preparation
stages before first vulnerable entry.  It excludes recovery.  The relation
`rel a x` identifies a concrete `.vulnerable` attempt state with its
`VulnerableState` proof payload.


The final clause says one pre-entry letter either succeeds, remains pre-entry,
or enters a genuine Dummy(0) vulnerable state.  In particular it rules out a
retry or a direct recovery edge before vulnerable failure.


The `RetryFailureSimulation` fields are then proved from
`moderateStep` versus `vulnerableStep`; the vulnerable failure branch may
enter recovery because the generic simulation deliberately charges that whole
continuation to the failure leaf.
-/
def ModerateFirstVulnerableSpliceSpec : Prop :=
  ∀ (hSealed : SealedStepSpec),
    ∀ {n : Nat} (ring : DirectedRing n)
      {C0 : Config n} (F : TripleFrame ring C0),
      2 ≤ F.b →
      ∃ pre : ModerateAttemptState ring F → Prop,
        ∃ rel :
            ModerateAttemptState ring F →
              VulnerableState F → Prop,
          (∀ s,
            pre
              ((moderateAttemptKernel ring F).start s)) ∧
          RetryFailureSimulation
            (moderateAttemptKernel ring F)
            (vulnerableStep hSealed F)
            rel ∧
          (∀ a e,
            pre a →
            (moderateAttemptKernel ring F).step a e =
                .success ∨
              ∃ a',
                (moderateAttemptKernel ring F).step a e =
                    .active a' ∧
                  (pre a' ∨
                    ∃ x : VulnerableState F,
                      x.targetPhase = .dummy 0 ∧
                      rel a' x))


/-- The full finite-prefix lift from the one remaining concrete stage relation. -/
theorem moderateVulnerableStageLift
    (hStage : ModerateFirstVulnerableSpliceSpec) :
    ModerateVulnerableStageLiftSpec := by
  intro hSealed
  intro n ring C0 F hb hvulnerable s T
  rcases hStage hSealed ring F hb with
    ⟨pre, rel, hstart, hsim, hpre⟩
  exact
    retryCount_splice_first_entry
      (K := moderateAttemptKernel ring F)
      (vstep := vulnerableStep hSealed F)
      (pre := pre)
      (rel := rel)
      (entry := fun x => x.targetPhase = .dummy 0)
      (q := 96)
      (c := 95)
      hsim
      hpre
      (fun x hx U => hvulnerable x hx U)
      ((moderateAttemptKernel ring F).start s)
      (hstart s)
      T


/-- Consequently all probability/counting work is already enough;
only `ModerateFirstVulnerableSpliceSpec` remains physical. -/
theorem moderateAttemptRetryMassSpec_proved
    (hStage : ModerateFirstVulnerableSpliceSpec) :
    ModerateAttemptRetryMassSpec :=
  moderateAttemptRetryMass_of_vulnerableStageLift
    (moderateVulnerableStageLift hStage)


#print axioms PPL.Convergence.LDLocal.retryCount_le_pow
#print axioms PPL.Convergence.LDLocal.retryCount_le_failureCount_of_sim
#print axioms PPL.Convergence.LDLocal.retryCount_splice_first_entry
#print axioms PPL.Convergence.LDLocal.moderateVulnerableStageLift
#print axioms PPL.Convergence.LDLocal.moderateAttemptRetryMassSpec_proved


end PPL.Convergence.LDLocal
