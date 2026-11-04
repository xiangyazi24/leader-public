import Leader.L3.Headline.Stages

/-!
The real-state retry shell and finite-word F.1-F.4 transfer are
proved below. The SMALL/BANK origin reference is an explicit
remaining implementation obligation. No agent state is changed.
Already-generated starts are handled at zero cost, not charged
an artificial attempt. Retry seeds are nonterminal rooted states.
-/

namespace L3.HeadlineRenewal

open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree
open PPL.Convergence.LDLocal (AttemptNode RetryKernel retryCount)

set_option autoImplicit false
set_option Elab.async false

abbrev RootedSeed {n : Nat} (ring : DirectedRing n) :=
  { C : HeadlineConfiguration n // headlineRooted ring C }

def rootedSuccessor {n : Nat}
    (ring : DirectedRing n) (hn : 5 <= n)
    (seed : RootedSeed ring) (e : Fin n) : RootedSeed ring :=
  ⟨headlinePhysicalNext ring seed.val e,
    headlineStagesRootedStep ring hn seed.val e seed.property⟩

def rootedTrialRelation {n : Nat} {H : Type}
    (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (a : RootedSeed ring × H) : Prop :=
  a.1.val = C

/-- The physical target wins a tie with the observed retry cut. -/
noncomputable def rootedTrialStep {n : Nat} {H : Type}
    (ring : DirectedRing n) (hn : 5 <= n)
    (advance : RootedSeed ring × H -> Fin n -> H)
    (cut : RootedSeed ring × H -> Fin n -> Bool)
    (a : RootedSeed ring × H) (e : Fin n) :
    AttemptNode (RootedSeed ring × H) (RootedSeed ring) := by
  classical
  exact if headlineGeneratedTarget ring
      (rootedSuccessor ring hn a.1 e).val then
    .success
  else if cut a e = true then
    .retry (rootedSuccessor ring hn a.1 e)
  else
    .active (rootedSuccessor ring hn a.1 e, advance a e)

/-- All completed retries are valid nonterminal restarts. -/
theorem rootedTrialRetryNonterminal {n : Nat} {H : Type}
    (ring : DirectedRing n) (hn : 5 <= n)
    (advance : RootedSeed ring × H -> Fin n -> H)
    (cut : RootedSeed ring × H -> Fin n -> Bool)
    (a : RootedSeed ring × H) (e : Fin n)
    (seed : RootedSeed ring)
    (hstep : rootedTrialStep ring hn advance cut a e = .retry seed) :
    ¬ headlineGeneratedTarget ring seed.val := by
  classical
  unfold rootedTrialStep at hstep
  split at hstep
  · cases hstep
  · rename_i hnot
    split at hstep
    · cases hstep
      exact hnot
    · cases hstep

noncomputable def rootedTrialKernel {n : Nat} {H : Type}
    (ring : DirectedRing n) (hn : 5 <= n)
    (initial : RootedSeed ring -> H)
    (advance : RootedSeed ring × H -> Fin n -> H)
    (cut : RootedSeed ring × H -> Fin n -> Bool) :
    RetryKernel (RootedSeed ring × H) (RootedSeed ring) n :=
  { start := fun seed => (seed, initial seed)
    step := rootedTrialStep ring hn advance cut
    valid := fun seed => ¬ headlineGeneratedTarget ring seed.val
    retry_valid := by
      intro a e seed hstep
      exact rootedTrialRetryNonterminal ring hn advance cut a e seed hstep }

/-- Retry carries the complete actual post-service configuration. -/
theorem rootedTrialRetryPayload {n : Nat} {H : Type}
    (ring : DirectedRing n) (hn : 5 <= n)
    (advance : RootedSeed ring × H -> Fin n -> H)
    (cut : RootedSeed ring × H -> Fin n -> Bool)
    (a : RootedSeed ring × H) (e : Fin n)
    (seed : RootedSeed ring)
    (hstep : rootedTrialStep ring hn advance cut a e = .retry seed) :
    seed.val = headlinePhysicalNext ring a.1.val e := by
  classical
  unfold rootedTrialStep at hstep
  split at hstep
  · cases hstep
  · split at hstep
    · cases hstep
      rfl
    · cases hstep

/-- No word-safety assertion is required for physical retry fidelity. -/
theorem rootedTrialSimulation {n : Nat} {H : Type}
    (ring : DirectedRing n) (hn : 5 <= n)
    (initial : RootedSeed ring -> H)
    (advance : RootedSeed ring × H -> Fin n -> H)
    (cut : RootedSeed ring × H -> Fin n -> Bool) :
    Prob.RetrySimulation (rootedTrialKernel ring hn initial advance cut)
      (headlinePhysicalNext ring) (headlineGeneratedTarget ring)
      (rootedTrialRelation (H := H) ring) := by
  classical
  intro C a hrel hnot e
  change a.1.val = C at hrel
  subst hrel
  cases hs : (rootedTrialKernel ring hn initial advance cut).step a e with
  | success =>
      have hs' : rootedTrialStep ring hn advance cut a e = .success := hs
      unfold rootedTrialStep at hs'
      split at hs'
      · rename_i hhit
        exact hhit
      · split at hs' <;> cases hs'
  | active b =>
      have hs' : rootedTrialStep ring hn advance cut a e = .active b := hs
      unfold rootedTrialStep at hs'
      split at hs'
      · cases hs'
      · split at hs'
        · cases hs'
        · cases hs'
          rfl
  | retry seed =>
      have hs' : rootedTrialStep ring hn advance cut a e = .retry seed := hs
      unfold rootedTrialStep at hs'
      split at hs'
      · cases hs'
      · split at hs'
        · cases hs'
          rfl
        · cases hs'

/-! ## Abstract integer arithmetic for F.2 and F.4 -/

theorem originSliceArithmetic
    (n d V A mass events : Nat)
    (hd : 0 < d) (hnd : n <= d)
    (h : (d * d * V) * events <= mass * (A * n ^ 2 + n)) :
    (V * d) * events <= (A * d + 1) * mass := by
  have hsize : A * n ^ 2 + n <= A * d ^ 2 + d :=
    Nat.add_le_add
      (Nat.mul_le_mul_left A (Nat.pow_le_pow_left hnd 2)) hnd
  have hscaled : d * ((V * d) * events) <=
      d * ((A * d + 1) * mass) := by
    calc
      d * ((V * d) * events) = (d * d * V) * events := by ac_rfl
      _ <= mass * (A * n ^ 2 + n) := h
      _ <= mass * (A * d ^ 2 + d) := Nat.mul_le_mul_left mass hsize
      _ = d * ((A * d + 1) * mass) := by
        simp only [Nat.pow_succ, Nat.pow_zero, Nat.one_mul,
          Nat.mul_add, Nat.add_mul, Nat.mul_one]
        ac_rfl
  exact Nat.le_of_mul_le_mul_left hscaled hd

theorem originScaleFactor (q k : Nat) :
    2 ^ (2 * q + k) = 2 ^ q * 2 ^ q * 2 ^ k := by
  have he : 2 * q + k = q + q + k := by omega
  rw [he, Nat.pow_add, Nat.pow_add]

theorem renewalMarginFacts (A V d : Nat)
    (hAV : A < V) (hd : 1 < d) :
    A * d + 1 < V * d ∧
      V * d - (A * d + 1) = (V - A) * d - 1 := by
  have hsplit : (V - A) * d + A * d = V * d := by
    rw [← Nat.add_mul, Nat.sub_add_cancel (Nat.le_of_lt hAV)]
  have hone : 1 <= V - A := by omega
  have hprod : d <= (V - A) * d := by
    have hh := Nat.mul_le_mul_right d hone
    simpa only [Nat.one_mul] using hh
  constructor <;> omega

private theorem leMulCeiling (a d : Nat) (hd : 0 < d) :
    a <= d * Prob.ceilNat a d := by
  have he : d * (a / d) + a % d = a := by
    simpa only [Nat.mul_comm] using Nat.div_add_mod a d
  have hr := Nat.mod_lt a hd
  by_cases hz : a % d = 0
  · simp only [Prob.ceilNat, if_pos hz, Nat.add_zero]
    omega
  · simp only [Prob.ceilNat, if_neg hz, Nat.mul_add, Nat.mul_one]
    omega

private theorem ceilingLeOfMul (a d R : Nat)
    (hd : 0 < d) (h : a <= d * R) :
    Prob.ceilNat a d <= R := by
  have he : d * (a / d) + a % d = a := by
    simpa only [Nat.mul_comm] using Nat.div_add_mod a d
  have hmul : d * (a / d) <= d * R := by omega
  have hquot : a / d <= R := Nat.le_of_mul_le_mul_left hmul hd
  by_cases hz : a % d = 0
  · simpa only [Prob.ceilNat, if_pos hz, Nat.add_zero] using hquot
  · have hne : a / d ≠ R := by
      intro hh
      rw [hh] at he
      omega
    have hsucc : a / d + 1 <= R := by omega
    simpa only [Prob.ceilNat, if_neg hz] using hsucc

def renewalCoefficient (A V d : Nat) : Nat :=
  Prob.ceilNat (A * V * d) ((V - A) * d - 1)

theorem renewalCoefficientPays (A V d : Nat)
    (hAV : A < V) (hd : 1 < d) :
    A * V * d <= ((V - A) * d - 1) * renewalCoefficient A V d := by
  have hf := renewalMarginFacts A V d hAV hd
  have hpositive : 0 < (V - A) * d - 1 := by omega
  exact leMulCeiling (A * V * d) ((V - A) * d - 1) hpositive

/-- Move n squared outside the scalar ceiling, without rounding
    each stage independently or discarding the minus-one margin. -/
theorem renewalPopulationCeiling (A V d n R : Nat)
    (hAV : A < V) (hd : 1 < d)
    (hR : A * V * d <= ((V - A) * d - 1) * R) :
    Prob.renewalCeiling (A * n ^ 2) (A * d + 1) (V * d) <=
      R * n ^ 2 := by
  have hf := renewalMarginFacts A V d hAV hd
  have hpositive : 0 < (V - A) * d - 1 := by omega
  unfold Prob.renewalCeiling
  rw [hf.2]
  apply ceilingLeOfMul _ _ _ hpositive
  calc
    (A * n ^ 2) * (V * d) = (A * V * d) * n ^ 2 := by ac_rfl
    _ <= (((V - A) * d - 1) * R) * n ^ 2 :=
      Nat.mul_le_mul_right (n ^ 2) hR
    _ = ((V - A) * d - 1) * (R * n ^ 2) := by ac_rfl

/-! ## Exact remaining producer/reference interfaces

Reference may be a subtype containing a valid genealogy invariant.
No claim is made that the fields below implement the paper reference.
Only nonterminal rooted seeds are charged an attempt.
-/

structure RootedReferenceData {n : Nat} (ring : DirectedRing n) where
  Memory : Type
  Reference : Type
  Origin : Type
  initialMemory : RootedSeed ring -> Memory
  memoryNext : RootedSeed ring × Memory -> Fin n -> Memory
  cut : RootedSeed ring × Memory -> Fin n -> Bool
  referenceNext : Reference -> Fin n -> Reference
  referenceStop : Reference -> Prop
  referenceStart : RootedSeed ring -> Reference
  spawn : Reference -> Fin n -> List Origin
  win : Origin -> List (Fin n) -> Bool

noncomputable def referenceKernel {n : Nat}
    (ring : DirectedRing n) (hn : 5 <= n)
    (D : RootedReferenceData ring) :
    RetryKernel (RootedSeed ring × D.Memory) (RootedSeed ring) n :=
  rootedTrialKernel ring hn D.initialMemory D.memoryNext D.cut

/-- Wordwise min(reference hit, divergence) domination. -/
def ReferenceAttemptDomination {n : Nat}
    (ring : DirectedRing n) (hn : 5 <= n)
    (D : RootedReferenceData ring) : Prop :=
  ∀ seed : RootedSeed ring,
    ¬ headlineGeneratedTarget ring seed.val ->
    ∀ word : List (Fin n),
      costWord (Prob.attemptStepper (referenceKernel ring hn D))
        (fun z => Prob.attemptGood z ∨ Prob.attemptFail z)
        (.active ((referenceKernel ring hn D).start seed)) word <=
      costWord D.referenceNext D.referenceStop (D.referenceStart seed) word

/-- First uncompleted concrete event-attribution obligation. -/
def ReferenceRetryCoverage {n : Nat}
    (ring : DirectedRing n) (hn : 5 <= n)
    (D : RootedReferenceData ring) : Prop :=
  ∀ seed : RootedSeed ring,
    ¬ headlineGeneratedTarget ring seed.val ->
    ∀ word : List (Fin n),
      Prob.retryFirstWord (referenceKernel ring hn D)
        (.active ((referenceKernel ring hn D).start seed)) word <=
      Prob.originEventWord D.referenceNext D.referenceStop D.spawn D.win
        (D.referenceStart seed) word

def ReferenceOriginCharge {n : Nat}
    (ring : DirectedRing n) (D : RootedReferenceData ring) : Prop :=
  ∀ seed : RootedSeed ring,
    ¬ headlineGeneratedTarget ring seed.val ->
    ∀ word : List (Fin n),
      Prob.originsWord D.referenceNext D.referenceStop D.spawn
        (D.referenceStart seed) word <=
      costWord D.referenceNext D.referenceStop (D.referenceStart seed) word + n

def ReferenceOriginRarity {n : Nat}
    (ring : DirectedRing n) (D : RootedReferenceData ring)
    (k : Nat) : Prop :=
  Prob.OriginRarity D.referenceStop D.spawn D.win
    1 (2 ^ (2 * ceilLogTwo n + k))

def ReferenceClock {n : Nat}
    (ring : DirectedRing n) (D : RootedReferenceData ring)
    (A : Nat) : Prop :=
  ∀ seed : RootedSeed ring,
    ¬ headlineGeneratedTarget ring seed.val ->
    ∀ T : Nat,
      costNumerator D.referenceNext D.referenceStop
        (D.referenceStart seed) T <= n ^ T * (A * n ^ 2)

structure RootedReferenceCertificate {n : Nat}
    (ring : DirectedRing n) (hn : 5 <= n)
    (D : RootedReferenceData ring) (A k : Nat) : Prop where
  domination : ReferenceAttemptDomination ring hn D
  coverage : ReferenceRetryCoverage ring hn D
  charge : ReferenceOriginCharge ring D
  rarity : ReferenceOriginRarity ring D k
  clock : ReferenceClock ring D A

private theorem wordSumMonotone {n : Nat} (T : Nat)
    (f g : List (Fin n) -> Nat)
    (h : ∀ word : List (Fin n), f word <= g word) :
    Prob.scheduleSum n T f <= Prob.scheduleSum n T g := by
  change FixedSpanRenewalPayload.wordSum n T f <=
    FixedSpanRenewalPayload.wordSum n T g
  rw [← FixedSpanRenewalPayload.rawWord_sum n T f,
    ← FixedSpanRenewalPayload.rawWord_sum n T g]
  exact ofFn_sum_le _ _ (fun i => h _)

theorem referenceAttemptCost {n : Nat}
    (ring : DirectedRing n) (hn : 5 <= n)
    (D : RootedReferenceData ring)
    (h : ReferenceAttemptDomination ring hn D)
    (seed : RootedSeed ring)
    (hnot : ¬ headlineGeneratedTarget ring seed.val) (T : Nat) :
    costNumerator (Prob.attemptStepper (referenceKernel ring hn D))
      (fun z => Prob.attemptGood z ∨ Prob.attemptFail z)
      (.active ((referenceKernel ring hn D).start seed)) T <=
    costNumerator D.referenceNext D.referenceStop
      (D.referenceStart seed) T := by
  change Prob.scheduleSum n T
      (costWord (Prob.attemptStepper (referenceKernel ring hn D))
        (fun z => Prob.attemptGood z ∨ Prob.attemptFail z)
        (.active ((referenceKernel ring hn D).start seed))) <=
    Prob.scheduleSum n T
      (costWord D.referenceNext D.referenceStop (D.referenceStart seed))
  exact wordSumMonotone T _ _ (h seed hnot)

theorem referenceRetryCount {n : Nat}
    (ring : DirectedRing n) (hn : 5 <= n)
    (D : RootedReferenceData ring)
    (h : ReferenceRetryCoverage ring hn D)
    (seed : RootedSeed ring)
    (hnot : ¬ headlineGeneratedTarget ring seed.val) (T : Nat) :
    retryCount (referenceKernel ring hn D)
      (.active ((referenceKernel ring hn D).start seed)) T <=
    Prob.originEventNumerator D.referenceNext D.referenceStop D.spawn D.win
      (D.referenceStart seed) T := by
  rw [Prob.retryCount_eq_wordSum]
  exact wordSumMonotone T _ _ (h seed hnot)

/-- F.1 followed by F.2, without origin/clock independence. -/
theorem referenceOriginMass {n : Nat}
    (ring : DirectedRing n) (hn : 5 <= n)
    (D : RootedReferenceData ring) (A k : Nat)
    (h : RootedReferenceCertificate ring hn D A k)
    (seed : RootedSeed ring)
    (hnot : ¬ headlineGeneratedTarget ring seed.val) (T : Nat) :
    (2 ^ k * 2 ^ ceilLogTwo n) *
      Prob.originEventNumerator D.referenceNext D.referenceStop D.spawn D.win
        (D.referenceStart seed) T <=
    (A * 2 ^ ceilLogTwo n + 1) * n ^ T := by
  have hraw := Prob.origin_counting_budget_le
    D.referenceNext D.referenceStop D.spawn D.win
    1 (2 ^ (2 * ceilLogTwo n + k)) n (A * n ^ 2)
    h.rarity (D.referenceStart seed) (h.charge seed hnot)
    (h.clock seed hnot) T
  have hscaled :
      (2 ^ ceilLogTwo n * 2 ^ ceilLogTwo n * 2 ^ k) *
        Prob.originEventNumerator D.referenceNext D.referenceStop
          D.spawn D.win (D.referenceStart seed) T <=
      n ^ T * (A * n ^ 2 + n) := by
    simpa only [originScaleFactor, Nat.one_mul] using hraw
  exact originSliceArithmetic n (2 ^ ceilLogTwo n) (2 ^ k) A
    (n ^ T)
    (Prob.originEventNumerator D.referenceNext D.referenceStop
      D.spawn D.win (D.referenceStart seed) T)
    (Nat.two_pow_pos _) (ceilLogTwo_spec n (by omega)).2 hscaled

theorem referenceRetryMass {n : Nat}
    (ring : DirectedRing n) (hn : 5 <= n)
    (D : RootedReferenceData ring) (A k : Nat)
    (h : RootedReferenceCertificate ring hn D A k)
    (seed : RootedSeed ring)
    (hnot : ¬ headlineGeneratedTarget ring seed.val) (T : Nat) :
    (2 ^ k * 2 ^ ceilLogTwo n) *
      retryCount (referenceKernel ring hn D)
        (.active ((referenceKernel ring hn D).start seed)) T <=
    (A * 2 ^ ceilLogTwo n + 1) * n ^ T := by
  exact Nat.le_trans
    (Nat.mul_le_mul_left (2 ^ k * 2 ^ ceilLogTwo n)
      (referenceRetryCount ring hn D h.coverage seed hnot T))
    (referenceOriginMass ring hn D A k h seed hnot T)

/-! ## Conditional real-cost theorem -/

theorem rootedCostFromReference {n : Nat}
    (ring : DirectedRing n) (hn : 5 <= n)
    (D : RootedReferenceData ring) (A k R : Nat)
    (h : RootedReferenceCertificate ring hn D A k)
    (hmargin : A < 2 ^ k)
    (hreserve : A * 2 ^ k * 2 ^ ceilLogTwo n <=
      ((2 ^ k - A) * 2 ^ ceilLogTwo n - 1) * R) :
    ∀ C : HeadlineConfiguration n, headlineRooted ring C ->
      ∀ T : Nat,
        costNumerator (headlinePhysicalNext ring)
          (headlineGeneratedTarget ring) C T <= n ^ T * (R * n ^ 2) := by
  classical
  have hpopulation := (ceilLogTwo_spec n (by omega)).2
  have hd : 1 < 2 ^ ceilLogTwo n := by omega
  have hnum : A * 2 ^ ceilLogTwo n + 1 <
      2 ^ k * 2 ^ ceilLogTwo n :=
    (renewalMarginFacts A (2 ^ k) (2 ^ ceilLogTwo n) hmargin hd).1
  have hsimulation :
      Prob.RetrySimulation (referenceKernel ring hn D)
        (headlinePhysicalNext ring) (headlineGeneratedTarget ring)
        (rootedTrialRelation (H := D.Memory) ring) :=
    rootedTrialSimulation ring hn D.initialMemory D.memoryNext D.cut
  have hattempt : ∀ seed : RootedSeed ring,
      (referenceKernel ring hn D).valid seed -> ∀ T : Nat,
      costNumerator (Prob.attemptStepper (referenceKernel ring hn D))
        (fun z => Prob.attemptGood z ∨ Prob.attemptFail z)
        (.active ((referenceKernel ring hn D).start seed)) T <=
      n ^ T * (A * n ^ 2) := by
    intro seed hvalid T
    exact Nat.le_trans
      (referenceAttemptCost ring hn D h.domination seed hvalid T)
      (h.clock seed hvalid T)
  have hretry : ∀ seed : RootedSeed ring,
      (referenceKernel ring hn D).valid seed -> ∀ T : Nat,
      (2 ^ k * 2 ^ ceilLogTwo n) *
        retryCount (referenceKernel ring hn D)
          (.active ((referenceKernel ring hn D).start seed)) T <=
      (A * 2 ^ ceilLogTwo n + 1) * n ^ T := by
    intro seed hvalid T
    exact referenceRetryMass ring hn D A k h seed hvalid T
  intro C hC T
  by_cases hterminal : headlineGeneratedTarget ring C
  · rw [costNumerator_terminal (headlinePhysicalNext ring)
      (headlineGeneratedTarget ring) C hterminal T]
    exact Nat.zero_le _
  · have hcost := Prob.costNumerator_renewal_le
      (headlinePhysicalNext ring) (headlineGeneratedTarget ring)
      (referenceKernel ring hn D) (rootedTrialRelation (H := D.Memory) ring)
      hsimulation (A * n ^ 2) (A * 2 ^ ceilLogTwo n + 1)
      (2 ^ k * 2 ^ ceilLogTwo n) hnum hattempt hretry
      C (⟨C, hC⟩ : RootedSeed ring) hterminal rfl T
    exact Nat.le_trans hcost
      (Nat.mul_le_mul_left (n ^ T)
        (renewalPopulationCeiling A (2 ^ k) (2 ^ ceilLogTwo n) n R
          hmargin hd hreserve))

/-- The exact paper ceiling, before any selected-table calibration. -/
theorem rootedCostWithExactCeiling {n : Nat}
    (ring : DirectedRing n) (hn : 5 <= n)
    (D : RootedReferenceData ring) (A k : Nat)
    (h : RootedReferenceCertificate ring hn D A k)
    (hmargin : A < 2 ^ k) :
    ∀ C : HeadlineConfiguration n, headlineRooted ring C ->
      ∀ T : Nat,
        costNumerator (headlinePhysicalNext ring)
          (headlineGeneratedTarget ring) C T <=
        n ^ T * (renewalCoefficient A (2 ^ k) (2 ^ ceilLogTwo n) * n ^ 2) := by
  have hpopulation := (ceilLogTwo_spec n (by omega)).2
  have hd : 1 < 2 ^ ceilLogTwo n := by omega
  exact rootedCostFromReference ring hn D A k
    (renewalCoefficient A (2 ^ k) (2 ^ ceilLogTwo n)) h hmargin
    (renewalCoefficientPays A (2 ^ k) (2 ^ ceilLogTwo n) hmargin hd)

/-- The production pin is fixed. This is not a word-safety-only
    premise: the producer and reference clock obligations remain. -/
def RootedReferenceRealization {n : Nat}
    (ring : DirectedRing n) (hn : 5 <= n) : Prop :=
  ∃ (D : RootedReferenceData ring) (A : Nat),
    RootedReferenceCertificate ring hn D A
      (compileAdvice (ceilLogTwo n)).kappa ∧
    A < 2 ^ (compileAdvice (ceilLogTwo n)).kappa ∧
    A * 2 ^ (compileAdvice (ceilLogTwo n)).kappa * 2 ^ ceilLogTwo n <=
      ((2 ^ (compileAdvice (ceilLogTwo n)).kappa - A) *
        2 ^ ceilLogTwo n - 1) * headlineRenewalRate n

/-- Exact reduction, not an assertion that realization holds. -/
theorem stageRootedRenewalCost_of_referenceRealization {n : Nat}
    (ring : DirectedRing n) (hn : 5 <= n)
    (h : RootedReferenceRealization ring hn) :
    StageRootedRenewalCost ring := by
  obtain ⟨D, A, hcertificate, hmargin, hreserve⟩ := h
  intro C hC T
  exact rootedCostFromReference ring hn D A
    (compileAdvice (ceilLogTwo n)).kappa (headlineRenewalRate n)
    hcertificate hmargin hreserve C hC T

end L3.HeadlineRenewal

/-!
The token recomputation below suppresses only NEW grant production.
It retains OLD grants, their motion, FIRE, leader sinks, and every
non-token output of the literal transition. SMALL has a concrete
observer: once a site has a post-cut zero start, all subsequent
runs there are post-cut. BANK cannot use this bit: ordinary worker
returns and inherited waiting slots require their own genealogy.
-/

namespace L3.HeadlineRenewal

open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree
open PPL.Convergence.LDLocal (AttemptNode RetryKernel retryCount)

set_option autoImplicit false
set_option Elab.async false

/-- Appendix F's token row with the new grant contribution disabled.
OLD-token FIRE, all sinks, fresh requests, HOLD and token motion
are recomputed in their original order, not replaced by grant=false. -/
def renewalNoNewGrantTokens (c : Compiled) (x y : Agent c) :
    TokPair × TokPair × TokMeta :=
  tokenStep x y
    (transition c x y).1.certNative
    (transition c x y).2.certNative
    (fireSelect x y (postEInfo x y).eX (postEInfo x y).eY)
    (dccStep x y (certificateStep c x y).2.2).request false

/-- The reference differs only in the physical token-owner output
on a service whose producer observer says to suppress fresh output. -/
def renewalMaskedPair (c : Compiled) (suppress : Bool)
    (x y : Agent c) : Agent c × Agent c :=
  if suppress then
    ({ (transition c x y).1 with
        req := (renewalNoNewGrantTokens c x y).1.req
        grant := (renewalNoNewGrantTokens c x y).1.grant },
     { (transition c x y).2 with
        req := (renewalNoNewGrantTokens c x y).2.1.req
        grant := (renewalNoNewGrantTokens c x y).2.1.grant })
  else transition c x y

/-- Equality of this projection is equality of EVERY non-token
field, including SMALL, BANK, certificate and native coordinates. -/
def renewalForgetTokens {c : Compiled} (x : Agent c) : Agent c :=
  { x with req := false, grant := false }

theorem renewalMaskedPairFrames (c : Compiled) (suppress : Bool)
    (x y : Agent c) :
    renewalForgetTokens (renewalMaskedPair c suppress x y).1 =
      renewalForgetTokens (transition c x y).1 ∧
    renewalForgetTokens (renewalMaskedPair c suppress x y).2 =
      renewalForgetTokens (transition c x y).2 := by
  cases suppress <;> constructor <;> rfl

theorem renewalMaskedPairOff (c : Compiled) (x y : Agent c) :
    renewalMaskedPair c false x y = transition c x y := by
  rfl

/-- The SAME physical edge and source-priority convention as step. -/
def renewalMaskedStep {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (e : Fin n) (suppress : Bool) :
    HeadlineConfiguration n :=
  fun i =>
    if i = e then
      (renewalMaskedPair (compileAdvice (ceilLogTwo n)) suppress
        (C e) (C (ring.rightNeighbor e))).1
    else if i = ring.rightNeighbor e then
      (renewalMaskedPair (compileAdvice (ceilLogTwo n)) suppress
        (C e) (C (ring.rightNeighbor e))).2
    else C i

theorem renewalMaskedStepOff {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (e : Fin n) :
    renewalMaskedStep ring C e false = headlinePhysicalNext ring C e := by
  rfl

/-- SMALL initiator sanitation is selected from the OLD parseRun. -/
def renewalSmallInvalid (k : Nat) (s : Small) : Bool :=
  match parseRun s with
  | none => false
  | some j => decide (k ≤ j)

/-- One bit records whether this site has had a genuine post-cut
SMALL zero start. It is proof memory, not part of Agent. -/
abbrev RenewalSmallMemory (n : Nat) := Fin n → Bool

/-- Complete physical reference state plus its SMALL origin memory. -/
abbrev RenewalSmallReference (n : Nat) :=
  HeadlineConfiguration n × RenewalSmallMemory n

/-- Every responder service restarts SMALL; an invalid initiator
also starts at zero, WITHOUT counting the creating service as a head. -/
def renewalSmallMemoryNext {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (seen : RenewalSmallMemory n)
    (e : Fin n) : RenewalSmallMemory n :=
  fun i =>
    if i = e then
      seen e || renewalSmallInvalid (compileAdvice (ceilLogTwo n)).K
        (C e).small
    else if i = ring.rightNeighbor e then true
    else seen i

/-- Suppression uses the OLD site's origin bit and literal success.
A newly created zero start cannot be mistaken for an inherited win. -/
def renewalSmallCut {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (seen : RenewalSmallMemory n)
    (e : Fin n) : Bool :=
  seen e &&
    (smallPair (C e) (C (ring.rightNeighbor e))
      (compileAdvice (ceilLogTwo n)).K).2.2

/-- The extra allowance is spent only once at a site not yet reset.
This is distinct from the recurring responder zero start. -/
def renewalSmallExtra {n : Nat}
    (C : HeadlineConfiguration n) (seen : RenewalSmallMemory n)
    (e : Fin n) : Bool :=
  !seen e && renewalSmallInvalid (compileAdvice (ceilLogTwo n)).K
    (C e).small

/-- Each list occurrence is an origin instance at THIS service.
Its site determines the later two-edge race; occurrences at the
same site at different services are still counted separately. -/
def renewalSmallSpawn {n : Nat} (ring : DirectedRing n)
    (r : RenewalSmallReference n) (e : Fin n) : List (Fin n) :=
  ring.rightNeighbor e ::
    (if renewalSmallExtra r.1 r.2 e then [e] else [])

/-- The creating service is excluded. This consumes only the suffix.
An incoming reset kills this SMALL origin; unrelated edges frame it.
This raw-incident race is NOT the BANK armed-decision event. -/
def renewalSmallWin {n : Nat} (ring : DirectedRing n)
    (root : Fin n) : Nat → List (Fin n) → Bool
  | 0, _ => true
  | _ + 1, [] => false
  | k + 1, e :: word =>
      if e = root then renewalSmallWin ring root k word
      else if ring.rightNeighbor e = root then false
      else renewalSmallWin ring root (k + 1) word

/-- Appendix F reference service, not a frozen private process. -/
def renewalSmallNext {n : Nat} (ring : DirectedRing n)
    (r : RenewalSmallReference n) (e : Fin n) :
    RenewalSmallReference n :=
  (renewalMaskedStep ring r.1 e (renewalSmallCut ring r.1 r.2 e),
   renewalSmallMemoryNext ring r.1 r.2 e)

/-- The reference's OWN first physical generated-target hit. -/
def renewalSmallStop {n : Nat} (ring : DirectedRing n)
    (r : RenewalSmallReference n) : Prop :=
  headlineGeneratedTarget ring r.1

/-- Every initial producer record is inherited at the attempt cut. -/
def renewalSmallStart {n : Nat} (ring : DirectedRing n)
    (seed : RootedSeed ring) : RenewalSmallReference n :=
  (seed.val, fun _ => false)

def renewalSmallInitialMemory {n : Nat} (ring : DirectedRing n) :
    RootedSeed ring → RenewalSmallMemory n :=
  fun _ _ => false

def renewalSmallTrialAdvance {n : Nat} (ring : DirectedRing n)
    (a : RootedSeed ring × RenewalSmallMemory n) (e : Fin n) :
    RenewalSmallMemory n :=
  renewalSmallMemoryNext ring a.1.val a.2 e

def renewalSmallTrialCut {n : Nat} (ring : DirectedRing n)
    (a : RootedSeed ring × RenewalSmallMemory n) (e : Fin n) : Bool :=
  renewalSmallCut ring a.1.val a.2 e

/-- CONCRETE SMALL slice of the requested data. No field is a
postulated observer or an arbitrary Next/Stop parameter. The
branch premise is essential to its physical interpretation. -/
def smallRootedReferenceData {n : Nat} (ring : DirectedRing n)
    (_hsmall : (compileAdvice (ceilLogTwo n)).useSmall = true) :
    RootedReferenceData ring :=
  { Memory := RenewalSmallMemory n
    Reference := RenewalSmallReference n
    Origin := Fin n
    initialMemory := renewalSmallInitialMemory ring
    memoryNext := renewalSmallTrialAdvance ring
    cut := renewalSmallTrialCut ring
    referenceNext := renewalSmallNext ring
    referenceStop := renewalSmallStop ring
    referenceStart := renewalSmallStart ring
    spawn := renewalSmallSpawn ring
    win := fun root word => renewalSmallWin ring root
      (compileAdvice (ceilLogTwo n)).K word }

/-- Even a nearly successful inherited RUN is retained on the first
service: the fresh bit is read BEFORE this service's zero starts. -/
theorem renewalSmallFirstPhysical {n : Nat} (ring : DirectedRing n)
    (seed : RootedSeed ring) (e : Fin n) :
    (renewalSmallNext ring (renewalSmallStart ring seed) e).1 =
      headlinePhysicalNext ring seed.val e := by
  exact renewalMaskedStepOff ring seed.val e

theorem renewalSmallPhysicalBeforeCut {n : Nat}
    (ring : DirectedRing n) (r : RenewalSmallReference n) (e : Fin n)
    (hcut : renewalSmallCut ring r.1 r.2 e = false) :
    (renewalSmallNext ring r e).1 = headlinePhysicalNext ring r.1 e := by
  exact (congrArg (renewalMaskedStep ring r.1 e) hcut).trans
    (renewalMaskedStepOff ring r.1 e)

/-- Source-row check for the recurring origin. -/
theorem renewalSmallResponderZero (c : Compiled) (x y : Agent c) :
    (smallPair x y c.K).2.1 = smallRunZero := by
  cases hx : x.small <;> cases hy : y.small <;>
    simp [smallPair, parseRun, hx, hy] <;>
    (repeat' split) <;> rfl

/-- These are the unspent, once-only initiating-sanitation allowances. -/
def renewalSmallRemaining {n : Nat} (seen : RenewalSmallMemory n) : Nat :=
  (List.ofFn (fun i : Fin n => if seen i then 0 else 1)).sum

private theorem renewalSpikeSum (n : Nat) :
    ∀ (a : Fin n) (v : Nat),
      (List.ofFn (fun i : Fin n => if i = a then v else 0)).sum = v := by
  induction n with
  | zero =>
      intro a
      exact Fin.elim0 a
  | succ n ih =>
      intro a v
      refine Fin.cases ?_ ?_ a
      · rw [List.ofFn_succ, List.sum_cons]
        have hp (i : Fin n) :
            (if i.succ = (0 : Fin (n + 1)) then v else 0) = 0 := by
          have hne : i.succ ≠ (0 : Fin (n + 1)) := by
            intro he
            have hv := congrArg Fin.val he
            change i.val + 1 = 0 at hv
            omega
          exact if_neg hne
        have ht :
            (List.ofFn (fun i : Fin n =>
              if i.succ = (0 : Fin (n + 1)) then v else 0)).sum = 0 := by
          have hh := ofFn_sum_eq _ (fun _ : Fin n => 0) hp
          simpa only [ofFn_sum_const, Nat.mul_zero] using hh
        rw [if_pos rfl, ht, Nat.add_zero]
      · intro a
        rw [List.ofFn_succ, List.sum_cons]
        have hne : (0 : Fin (n + 1)) ≠ a.succ := by
          intro he
          have hv := congrArg Fin.val he
          change 0 = a.val + 1 at hv
          omega
        rw [if_neg hne, Nat.zero_add]
        have hp (i : Fin n) :
            (if i.succ = a.succ then v else 0) =
              (if i = a then v else 0) := by
          simp only [Fin.succ_inj]
        rw [ofFn_sum_eq _ _ hp]
        exact ih a v

theorem renewalSmallRemainingInitial (n : Nat) :
    renewalSmallRemaining (fun _ : Fin n => false) = n := by
  simp [renewalSmallRemaining, ofFn_sum_const]

/-- One extra source origin consumes one unspent allowance; every
other memory update only decreases the remaining allowance. -/
theorem renewalSmallRemainingStep {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (seen : RenewalSmallMemory n)
    (e : Fin n) :
    renewalSmallRemaining (renewalSmallMemoryNext ring C seen e) +
      Prob.indicator (renewalSmallExtra C seen e) ≤
    renewalSmallRemaining seen := by
  have hp (i : Fin n) :
      (if renewalSmallMemoryNext ring C seen e i then 0 else 1) +
        (if i = e then Prob.indicator (renewalSmallExtra C seen e) else 0) ≤
      (if seen i then 0 else 1) := by
    by_cases hi : i = e
    · subst i
      cases hs : seen e <;>
        cases hv : renewalSmallInvalid (compileAdvice (ceilLogTwo n)).K
          (C e).small <;>
        simp [renewalSmallMemoryNext, renewalSmallExtra,
          Prob.indicator, hs, hv]
    · by_cases hj : i = ring.rightNeighbor e
      · subst i
        cases hs : seen (ring.rightNeighbor e) <;>
          simp [renewalSmallMemoryNext, hi, hs]
      · simp [renewalSmallMemoryNext, hi, hj]
  have hh := ofFn_sum_le _ _ hp
  rw [ofFn_sum_add, renewalSpikeSum] at hh
  exact hh

theorem renewalSmallSpawnLength {n : Nat} (ring : DirectedRing n)
    (r : RenewalSmallReference n) (e : Fin n) :
    (renewalSmallSpawn ring r e).length =
      1 + Prob.indicator (renewalSmallExtra r.1 r.2 e) := by
  cases hx : renewalSmallExtra r.1 r.2 e <;>
    simp [renewalSmallSpawn, Prob.indicator, hx]

private theorem renewalWordCostCons {S : Type} {n : Nat}
    (next : S → Fin n → S) (P : S → Prop) (x : S)
    (e : Fin n) (word : List (Fin n)) (hx : ¬ P x) :
    costWord next P x (e :: word) =
      1 + costWord next P (next x e) word := by
  classical
  simp only [costWord, K2FiniteSafeEliminationExpected.rawCost, if_neg hx]

/-- F.1's pathwise charging statement for this actual SMALL
observer. The final entering-target service is included. -/
theorem renewalSmallOriginsBudget {n : Nat} (ring : DirectedRing n) :
    ∀ (word : List (Fin n)) (r : RenewalSmallReference n),
      Prob.originsWord (renewalSmallNext ring) (renewalSmallStop ring)
        (renewalSmallSpawn ring) r word ≤
      costWord (renewalSmallNext ring) (renewalSmallStop ring) r word +
        renewalSmallRemaining r.2 := by
  classical
  intro word
  induction word with
  | nil =>
      intro r
      change 0 ≤ 0 + renewalSmallRemaining r.2
      omega
  | cons e word ih =>
      intro r
      by_cases hs : renewalSmallStop ring r
      · rw [Prob.originsWord, if_pos hs]
        exact Nat.zero_le _
      · have ht := ih (renewalSmallNext ring r e)
        have hp := renewalSmallRemainingStep ring r.1 r.2 e
        have hp' :
            renewalSmallRemaining (renewalSmallNext ring r e).2 +
              Prob.indicator (renewalSmallExtra r.1 r.2 e) ≤
            renewalSmallRemaining r.2 := hp
        rw [Prob.originsWord, if_neg hs, renewalSmallSpawnLength,
          renewalWordCostCons (renewalSmallNext ring)
            (renewalSmallStop ring) r e word hs]
        omega

theorem smallReferenceOriginCharge {n : Nat} (ring : DirectedRing n)
    (hsmall : (compileAdvice (ceilLogTwo n)).useSmall = true) :
    ReferenceOriginCharge ring (smallRootedReferenceData ring hsmall) := by
  intro seed _ word
  have h := renewalSmallOriginsBudget ring word
    (renewalSmallStart ring seed)
  have hz : renewalSmallRemaining (renewalSmallStart ring seed).2 = n :=
    renewalSmallRemainingInitial n
  rw [hz] at h
  exact h

/-- Stronger induction statement for the concrete SMALL attempt.
The OLD physical state must be nonterminal; an active attempt
is not charged when its starting seed already belongs to G. -/
theorem renewalSmallAttemptWord {n : Nat} (ring : DirectedRing n)
    (hn : 5 ≤ n) :
    ∀ (word : List (Fin n))
      (a : RootedSeed ring × RenewalSmallMemory n),
      ¬ headlineGeneratedTarget ring a.1.val →
      costWord
        (Prob.attemptStepper (rootedTrialKernel ring hn
          (renewalSmallInitialMemory ring) (renewalSmallTrialAdvance ring)
          (renewalSmallTrialCut ring)))
        (fun z => Prob.attemptGood z ∨ Prob.attemptFail z)
        (.active a) word ≤
      costWord (renewalSmallNext ring) (renewalSmallStop ring)
        (a.1.val, a.2) word := by
  classical
  intro word
  induction word with
  | nil =>
      intro a _
      exact Nat.le_refl 0
  | cons e word ih =>
      intro a hnot
      have hactive : ¬
          (Prob.attemptGood (.active a :
            AttemptNode (RootedSeed ring × RenewalSmallMemory n)
              (RootedSeed ring)) ∨
           Prob.attemptFail (.active a :
            AttemptNode (RootedSeed ring × RenewalSmallMemory n)
              (RootedSeed ring))) := by
        intro h
        rcases h with h | h
        · exact h
        · exact h
      have hrefnot : ¬ renewalSmallStop ring (a.1.val, a.2) := hnot
      rw [renewalWordCostCons _ _
          (AttemptNode.active a :
            AttemptNode (RootedSeed ring × RenewalSmallMemory n)
              (RootedSeed ring)) e word hactive,
        renewalWordCostCons _ _ (a.1.val, a.2) e word hrefnot]
      change 1 + costWord _ _
          ((rootedTrialKernel ring hn (renewalSmallInitialMemory ring)
            (renewalSmallTrialAdvance ring)
            (renewalSmallTrialCut ring)).step a e) word ≤
        1 + costWord (renewalSmallNext ring) (renewalSmallStop ring)
          (renewalSmallNext ring (a.1.val, a.2) e) word
      cases hs : (rootedTrialKernel ring hn
          (renewalSmallInitialMemory ring) (renewalSmallTrialAdvance ring)
          (renewalSmallTrialCut ring)).step a e with
      | success =>
          rw [costWord_terminal _ _ (AttemptNode.success : AttemptNode (RootedSeed ring × RenewalSmallMemory n) (RootedSeed ring))
            (by exact Or.inl True.intro) word]
          exact Nat.add_le_add_left (Nat.zero_le _) 1
      | retry seed =>
          rw [costWord_terminal _ _ (AttemptNode.retry seed : AttemptNode (RootedSeed ring × RenewalSmallMemory n) (RootedSeed ring))
            (by exact Or.inr True.intro) word]
          exact Nat.add_le_add_left (Nat.zero_le _) 1
      | active b =>
          have hs' : rootedTrialStep ring hn
              (renewalSmallTrialAdvance ring) (renewalSmallTrialCut ring)
              a e = .active b := hs
          unfold rootedTrialStep at hs'
          split at hs'
          · cases hs'
          · rename_i hnext
            split at hs'
            · cases hs'
            · rename_i hnocut
              cases hs'
              have hcut : renewalSmallTrialCut ring a e = false := by
                cases hc : renewalSmallTrialCut ring a e with
                | false => rfl
                | true => exact False.elim (hnocut hc)
              have href : renewalSmallNext ring (a.1.val, a.2) e =
                  ((rootedSuccessor ring hn a.1 e).val,
                    renewalSmallTrialAdvance ring a e) := by
                apply Prod.ext
                · exact renewalSmallPhysicalBeforeCut ring (a.1.val, a.2) e hcut
                · rfl
              have ht := ih
                (rootedSuccessor ring hn a.1 e,
                  renewalSmallTrialAdvance ring a e) hnext
              rw [← href] at ht
              exact Nat.add_le_add_left ht 1

theorem smallReferenceAttemptDomination {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hsmall : (compileAdvice (ceilLogTwo n)).useSmall = true) :
    ReferenceAttemptDomination ring hn (smallRootedReferenceData ring hsmall) := by
  intro seed hnot word
  exact renewalSmallAttemptWord ring hn word
    (seed, renewalSmallInitialMemory ring seed) hnot

/-- Exact outstanding finite-word suffix estimate for the SMALL
slice. It is NOT an event-attribution hypothesis and is not proved
here. The BANK analogue must use adapted ARMED decisions instead. -/
def SmallReferenceSuffixBound {n : Nat}
    (ring : DirectedRing n) : Prop :=
  ∀ (root : Fin n) (T : Nat),
    2 ^ (2 * ceilLogTwo n + (compileAdvice (ceilLogTwo n)).kappa) *
      Prob.scheduleSum n T
        (fun word => Prob.indicator
          (renewalSmallWin ring root (compileAdvice (ceilLogTwo n)).K word)) ≤
      n ^ T

/-- Exact specialized full-machine remainder, with no fabricated
BANK data or no-suppression replacement inserted as its witness. -/
def BankReferenceRealizationRequired {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n) : Prop :=
  (compileAdvice (ceilLogTwo n)).useSmall = false →
    RootedReferenceRealization ring hn

end L3.HeadlineRenewal


/-!
Concrete BANK origin observer.
No protocol field or alternate physical transition is added.

Literal Base.bankPair first-match order:
role repair; nonroot mode / nondigit token sanitation;
incoming root grant, armed reset, or WAIT tick;
outgoing root grant/change/wrong-neighbor/RESET launch;
matching RL, AL, CL0/CL1; mismatching return;
ARMED increment/IR launch; CSTART comparison launch;
width-one turn and WAIT tick;
nonroot changed role; top IR erasure; source RR; top RR;
RL retreat; collision; top CR turn; AL/CL return; IR/CR advance.
Only pending-RL acceptance births a completed zero origin.
-/

namespace L3.HeadlineRenewal

open Classical
open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree
open PPL.Convergence.LDLocal (AttemptNode RetryKernel retryCount)

set_option autoImplicit false
set_option Elab.async false

/-- Receipt IDs and completed origin IDs use their creating service. -/
structure RenewalBankReceipt (n : Nat) where
  service : Nat
  root : Fin n
  deriving DecidableEq, Repr

structure RenewalBankOrigin (n : Nat) where
  service : Nat
  root : Fin n
  receipt : RenewalBankReceipt n
  deriving DecidableEq, Repr

/-- The Boolean discriminates controller from worker entrance atoms. -/
abbrev RenewalBankAtom (n : Nat) := Fin n × Bool

structure RenewalBankPayload (n : Nat) where
  atoms : List (RenewalBankAtom n)
  origin : Option (RenewalBankOrigin n)
  heads : Nat

inductive RenewalBankWorker (n : Nat) where
  | empty
  | pending (receipt : RenewalBankReceipt n)
  | payload (value : RenewalBankPayload n)

inductive RenewalBankController (n : Nat) where
  | empty
  | active (value : RenewalBankPayload n)
  | waiting (atoms : List (RenewalBankAtom n))

structure RenewalBankSite (n : Nat) where
  worker : RenewalBankWorker n
  controller : RenewalBankController n

structure RenewalBankMemory (n : Nat) where
  service : Nat
  sites : Fin n → RenewalBankSite n

abbrev RenewalBankReference (n : Nat) :=
  HeadlineConfiguration n × RenewalBankMemory n

def renewalBankEntrancePayload {n : Nat}
    (site : Fin n) (controller : Bool) : RenewalBankPayload n :=
  { atoms := [(site, controller)], origin := none, heads := 0 }

def renewalBankWaitingAtoms {n : Nat}
    (c : RenewalBankController n) : List (RenewalBankAtom n) :=
  match c with
  | .waiting atoms => atoms
  | _ => []

def renewalBankActivePayload {n : Nat}
    (c : RenewalBankController n) (site : Fin n) :
    RenewalBankPayload n :=
  match c with
  | .active p => p
  | _ => renewalBankEntrancePayload site true

def renewalBankWorkerPayload {n : Nat}
    (w : RenewalBankWorker n) (site : Fin n) :
    RenewalBankPayload n :=
  match w with
  | .payload p => p
  | _ => renewalBankEntrancePayload site false

/-- Only independently inherited waiting atoms are merged on return. -/
def renewalBankReturned {n : Nat}
    (c : RenewalBankController n)
    (w : RenewalBankWorker n) (site : Fin n) :
    RenewalBankPayload n :=
  { (renewalBankWorkerPayload w site) with
    atoms := (renewalBankWorkerPayload w site).atoms ++
      renewalBankWaitingAtoms c }

def renewalBankHead {n : Nat}
    (p : RenewalBankPayload n) : RenewalBankPayload n :=
  { p with heads := if p.origin.isSome then p.heads + 1 else 0 }

/-- A slot expires only when a service actually ticks the wait row. -/
def renewalBankWaitSlot {n : Nat}
    (mode : Mode) (lease : Nat)
    (c : RenewalBankController n) : RenewalBankController n :=
  if isWaitMode mode then
    if 1 < lease then c else .empty
  else c

/-- Initial RR/RL tokens are inherited, never pending receipts. An
initial role-zero active or waiting slot has its own distinct atom. -/
def renewalBankInitialSite {n : Nat}
    (C : HeadlineConfiguration n) (i : Fin n) :
    RenewalBankSite n :=
  { worker :=
      if (C i).tok = .E then .empty
      else .payload (renewalBankEntrancePayload i false)
    controller :=
      if (C i).pack.val = 0 then
        match (C i).mode with
        | .ARMED => .active (renewalBankEntrancePayload i true)
        | .CSTART => .active (renewalBankEntrancePayload i true)
        | .RWAIT => .waiting [(i, true)]
        | .IWAIT => .waiting [(i, true)]
        | .CWAIT => .waiting [(i, true)]
        | .RESET => .empty
      else .empty }

def renewalBankInitialMemory {n : Nat} (ring : DirectedRing n)
    (seed : RootedSeed ring) : RenewalBankMemory n :=
  { service := 0
    sites := renewalBankInitialSite seed.val }

/-- OLD-pair BANK observer. Every mutation follows the same priority
as Base.bankPair. Source RR transfers its receipt over any OLD
responder label; neither that overwrite nor ordinary collision
copies or creates an origin. Generated waits own no payload. -/
def renewalBankPairMemory {n : Nat}
    (c : Compiled) (m : RenewalBankMemory n)
    (e dest : Fin n) (x y : Agent c) :
    RenewalBankSite n × RenewalBankSite n := Id.run do
  let bx := bankCell x x.pack.val
  let cy := bankCell y y.pack.val
  let postRole := packNext x.pack.val y.pack.val c.b
  let changed := postRole != cy.role
  let mut sx := m.sites e
  let mut sy := m.sites dest
  if changed then
    sy := { worker := .empty, controller := .empty }
  if bx.role != 0 then
    sx := { sx with controller := .empty }
  if postRole != 0 then
    sy := { sy with controller := .empty }
  if !(1 ≤ bx.role && bx.role ≤ c.b) then
    sx := { sx with worker := .empty }
  if !(1 ≤ postRole && postRole ≤ c.b) then
    sy := { sy with worker := .empty }
  if postRole == 0 && !changed then
    if cy.grant || cy.mode == .ARMED then
      sy := { sy with controller := .empty }
    else
      sy := { sy with controller :=
        renewalBankWaitSlot cy.mode cy.lease sy.controller }
  if bx.role == 0 then
    if bx.grant then
      sx := { sx with controller := .empty }
      if !changed && postRole == 1 then
        sy := { sy with worker := .empty }
      return (sx, sy)
    if changed then
      if bx.mode == .ARMED || bx.mode == .CSTART then
        sx := { sx with controller := .empty }
      else
        sx := { sx with controller :=
          renewalBankWaitSlot bx.mode bx.lease sx.controller }
      return (sx, sy)
    if postRole != 1 then
      sx := { sx with controller :=
        renewalBankWaitSlot bx.mode bx.lease sx.controller }
      return (sx, sy)
    if bx.mode == .RESET then
      sx := { sx with controller := .waiting [] }
      sy := { sy with worker :=
        (.pending { service := m.service, root := e }) }
      return (sx, sy)
    if isRetTok cy.tok then
      let oldWorker := sy.worker
      sy := { sy with worker := .empty }
      if cy.tok == .RL && bx.mode == .RWAIT then
        match oldWorker with
        | .pending receipt =>
            sx := { sx with controller := .active ({ atoms := renewalBankWaitingAtoms sx.controller, origin := some { service := m.service, root := e, receipt := receipt }, heads := 0 }) }
        | _ =>
            sx := { sx with controller := .active (renewalBankReturned sx.controller oldWorker dest) }
        return (sx, sy)
      if cy.tok == .AL && bx.mode == .IWAIT then
        sx := { sx with controller := .active (renewalBankReturned sx.controller oldWorker dest) }
        return (sx, sy)
      if (cy.tok == .CL0 || cy.tok == .CL1) &&
          bx.mode == .CWAIT then
        if cy.tok == .CL0 then
          sx := { sx with controller := .active (renewalBankReturned sx.controller oldWorker dest) }
        else
          sx := { sx with controller := .empty }
        return (sx, sy)
      sx := { sx with controller :=
        renewalBankWaitSlot bx.mode bx.lease sx.controller }
      return (sx, sy)
    if bx.mode == .ARMED then
      if cy.tok != .E then
        sx := { sx with controller := .empty }
        sy := { sy with worker := .empty }
        return (sx, sy)
      if cy.bit == false then
        sx := { sx with controller := .active (renewalBankHead (renewalBankActivePayload sx.controller e)) }
        return (sx, sy)
      sy := { sy with worker := .payload (renewalBankHead (renewalBankActivePayload sx.controller e)) }
      sx := { sx with controller := .waiting [] }
      return (sx, sy)
    if bx.mode == .CSTART then
      if cy.tok != .E then
        sx := { sx with controller := .empty }
        sy := { sy with worker := .empty }
        return (sx, sy)
      sy := { sy with worker := .payload (renewalBankActivePayload sx.controller e) }
      sx := { sx with controller := .waiting [] }
      return (sx, sy)
    if c.b == 1 then
      if cy.tok == .IR then
        sy := { sy with worker := .empty }
    sx := { sx with controller :=
      renewalBankWaitSlot bx.mode bx.lease sx.controller }
    return (sx, sy)
  if changed then
    if 1 ≤ bx.role && bx.role < c.b &&
        (bx.tok == .IR || bx.tok == .CR0 || bx.tok == .CR1) then
      sx := { sx with worker := .empty }
    return (sx, sy)
  if bx.role == c.b && bx.tok == .IR then
    sx := { sx with worker := .empty }
  if postRole == c.b && cy.tok == .IR then
    sy := { sy with worker := .empty }
  if 1 ≤ bx.role && bx.role < c.b && postRole == bx.role + 1 then
    if bx.tok == .RR then
      sy := { sy with worker := sx.worker }
      sx := { sx with worker := .empty }
      return (sx, sy)
    if postRole == c.b && cy.tok == .RR then
      sx := { sx with worker := sy.worker }
      sy := { sy with worker := .empty }
      return (sx, sy)
    if cy.tok == .RL then
      sx := { sx with worker := sy.worker }
      sy := { sy with worker := .empty }
      return (sx, sy)
    if bx.tok != .E &&
        (if postRole == c.b && cy.tok == .IR then false
         else cy.tok != .E) then
      sx := { sx with worker := .empty }
      sy := { sy with worker := .empty }
      return (sx, sy)
    if postRole == c.b && (cy.tok == .CR0 || cy.tok == .CR1) then
      sx := { sx with worker := sy.worker }
      sy := { sy with worker := .empty }
      return (sx, sy)
    if cy.tok == .AL || cy.tok == .CL0 || cy.tok == .CL1 then
      sx := { sx with worker := sy.worker }
      sy := { sy with worker := .empty }
      return (sx, sy)
    if bx.tok == .IR then
      sy := { sy with worker := sx.worker }
      sx := { sx with worker := .empty }
      return (sx, sy)
    if bx.tok == .CR0 || bx.tok == .CR1 then
      sy := { sy with worker := sx.worker }
      sx := { sx with worker := .empty }
      return (sx, sy)
  return (sx, sy)

/-- The memory reads OLD physical records, even when the resulting
reference physical step masks newly produced grant. -/
def renewalBankMemoryNext {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (m : RenewalBankMemory n)
    (e : Fin n) : RenewalBankMemory n :=
  { service := m.service + 1
    sites := fun i =>
      if i = e then
        (renewalBankPairMemory (compileAdvice (ceilLogTwo n))
          m e (ring.rightNeighbor e)
          (C e) (C (ring.rightNeighbor e))).1
      else if i = ring.rightNeighbor e then
        (renewalBankPairMemory (compileAdvice (ceilLogTwo n))
          m e (ring.rightNeighbor e)
          (C e) (C (ring.rightNeighbor e))).2
      else m.sites i }

/-- The only fresh birth is an OLD matching RL in RWAIT with a
worker carrying a receipt. A matching inherited RL spawns nothing. -/
def renewalBankBirth {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (m : RenewalBankMemory n)
    (e : Fin n) : Option (RenewalBankOrigin n) :=
  if Counter.resetRootRow
      (bankCell (C e) (C e).pack.val)
      (bankCell (C (ring.rightNeighbor e))
        (C (ring.rightNeighbor e)).pack.val)
      (packNext (C e).pack.val (C (ring.rightNeighbor e)).pack.val
        (compileAdvice (ceilLogTwo n)).b)
      (compileAdvice (ceilLogTwo n)).b = .resetReturn then
    match (m.sites (ring.rightNeighbor e)).worker with
    | .pending receipt =>
        some { service := m.service, root := e, receipt := receipt }
    | _ => none
  else none

/-- An OLD CL1 is fresh precisely when it has an actual completed
origin and no inherited atom in the worker or independent wait. -/
def renewalBankFreshPayer {n : Nat}
    (c : RenewalBankController n) (w : RenewalBankWorker n) : Bool :=
  match c, w with
  | .waiting inherited, .payload p =>
      inherited.isEmpty && p.atoms.isEmpty && p.origin.isSome
  | _, _ => false

/-- The first factor is the literal OLD BANK-success guard
(BaseTokenFrame.baseBankSuccessBit when useSmall=false). -/
def renewalBankCut {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (m : RenewalBankMemory n)
    (e : Fin n) : Bool :=
  bankSuccess
    (bankCell (C e) (C e).pack.val)
    (bankCell (C (ring.rightNeighbor e))
      (C (ring.rightNeighbor e)).pack.val)
    (packNext (C e).pack.val (C (ring.rightNeighbor e)).pack.val
      (compileAdvice (ceilLogTwo n)).b)
    (compileAdvice (ceilLogTwo n)).b &&
  renewalBankFreshPayer (m.sites e).controller
    (m.sites (ring.rightNeighbor e)).worker

def renewalBankNext {n : Nat} (ring : DirectedRing n)
    (r : RenewalBankReference n) (e : Fin n) :
    RenewalBankReference n :=
  (renewalMaskedStep ring r.1 e (renewalBankCut ring r.1 r.2 e),
   renewalBankMemoryNext ring r.1 r.2 e)

def renewalBankStop {n : Nat} (ring : DirectedRing n)
    (r : RenewalBankReference n) : Prop :=
  headlineGeneratedTarget ring r.1

def renewalBankStart {n : Nat} (ring : DirectedRing n)
    (seed : RootedSeed ring) : RenewalBankReference n :=
  (seed.val, renewalBankInitialMemory ring seed)

def renewalBankTrialAdvance {n : Nat} (ring : DirectedRing n)
    (a : RootedSeed ring × RenewalBankMemory n) (e : Fin n) :
    RenewalBankMemory n :=
  renewalBankMemoryNext ring a.1.val a.2 e

def renewalBankTrialCut {n : Nat} (ring : DirectedRing n)
    (a : RootedSeed ring × RenewalBankMemory n) (e : Fin n) : Bool :=
  renewalBankCut ring a.1.val a.2 e

/-- Birth snapshots are on the Origin API only; the stored
identifiers are not recursively nested reference states. -/
structure RenewalBankBorn (n : Nat) where
  identity : RenewalBankOrigin n
  afterBirth : RenewalBankReference n

def renewalBankSpawn {n : Nat} (ring : DirectedRing n)
    (r : RenewalBankReference n) (e : Fin n) :
    List (RenewalBankBorn n) :=
  match renewalBankBirth ring r.1 r.2 e with
  | none => []
  | some o => [{ identity := o, afterBirth := renewalBankNext ring r e }]

def renewalBankPayloadReached {n : Nat}
    (o : RenewalBankOrigin n) (K : Nat)
    (p : RenewalBankPayload n) : Bool :=
  decide (p.origin = some o ∧ K ≤ p.heads)

def renewalBankSiteReached {n : Nat}
    (o : RenewalBankOrigin n) (K : Nat)
    (site : RenewalBankSite n) : Bool :=
  (match site.worker with
   | .payload p => renewalBankPayloadReached o K p
   | _ => false) ||
  (match site.controller with
   | .active p => renewalBankPayloadReached o K p
   | _ => false)

def renewalBankReached {n : Nat}
    (o : RenewalBankOrigin n) (K : Nat)
    (m : RenewalBankMemory n) : Bool :=
  (List.ofFn (fun i : Fin n =>
    renewalBankSiteReached o K (m.sites i))).any (fun x => x)

/-- Concrete broad K-head suffix event, without a rarity claim. -/
def renewalBankWinWord {n : Nat}
    (ring : DirectedRing n) (o : RenewalBankOrigin n) (K : Nat) :
    List (Fin n) → RenewalBankReference n → Bool
  | [], r => renewalBankReached o K r.2
  | e :: word, r =>
      renewalBankReached o K r.2 ||
        renewalBankWinWord ring o K word (renewalBankNext ring r e)

def renewalBankWin {n : Nat} (ring : DirectedRing n)
    (born : RenewalBankBorn n) (word : List (Fin n)) : Bool :=
  renewalBankWinWord ring born.identity
    (compileAdvice (ceilLogTwo n)).K word born.afterBirth

/-- Concrete BANK reference data, not a postulated transition. -/
def bankRootedReferenceData {n : Nat} (ring : DirectedRing n)
    (_hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) :
    RootedReferenceData ring :=
  { Memory := RenewalBankMemory n
    Reference := RenewalBankReference n
    Origin := RenewalBankBorn n
    initialMemory := renewalBankInitialMemory ring
    memoryNext := renewalBankTrialAdvance ring
    cut := renewalBankTrialCut ring
    referenceNext := renewalBankNext ring
    referenceStop := renewalBankStop ring
    referenceStart := renewalBankStart ring
    spawn := renewalBankSpawn ring
    win := renewalBankWin ring }

/-- Off-mask equality is the existing real headlinePhysicalNext. -/
theorem renewalBankPhysicalBeforeCut {n : Nat}
    (ring : DirectedRing n) (r : RenewalBankReference n) (e : Fin n)
    (hcut : renewalBankCut ring r.1 r.2 e = false) :
    (renewalBankNext ring r e).1 = headlinePhysicalNext ring r.1 e := by
  exact (congrArg (renewalMaskedStep ring r.1 e) hcut).trans
    (renewalMaskedStepOff ring r.1 e)

theorem renewalBankSpawnLengthLeOne {n : Nat}
    (ring : DirectedRing n) (r : RenewalBankReference n)
    (e : Fin n) :
    (renewalBankSpawn ring r e).length ≤ 1 := by
  cases hb : renewalBankBirth ring r.1 r.2 e with
  | none =>
      simp [renewalBankSpawn, hb]
  | some o =>
      simp [renewalBankSpawn, hb]

/-- Each stopped path allocates no more origins than paid services. -/
theorem renewalBankOriginsBudget {n : Nat} (ring : DirectedRing n) :
    ∀ (word : List (Fin n)) (r : RenewalBankReference n),
      Prob.originsWord (renewalBankNext ring) (renewalBankStop ring)
        (renewalBankSpawn ring) r word ≤
      costWord (renewalBankNext ring) (renewalBankStop ring)
        r word := by
  classical
  intro word
  induction word with
  | nil =>
      intro r
      change 0 ≤ 0
      exact Nat.le_refl 0
  | cons e word ih =>
      intro r
      by_cases hs : renewalBankStop ring r
      · rw [Prob.originsWord, if_pos hs]
        exact Nat.zero_le _
      · have ht := ih (renewalBankNext ring r e)
        have hb := renewalBankSpawnLengthLeOne ring r e
        rw [Prob.originsWord, if_neg hs,
          renewalWordCostCons (renewalBankNext ring)
            (renewalBankStop ring) r e word hs]
        omega

/-- F.1 origin charge, stronger than the requested cost+n. -/
theorem bankReferenceOriginCharge {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) :
    ReferenceOriginCharge ring (bankRootedReferenceData ring hbank) := by
  intro seed _ word
  have h := renewalBankOriginsBudget ring word
    (renewalBankStart ring seed)
  change Prob.originsWord (renewalBankNext ring)
      (renewalBankStop ring) (renewalBankSpawn ring)
      (renewalBankStart ring seed) word ≤
    costWord (renewalBankNext ring) (renewalBankStop ring)
      (renewalBankStart ring seed) word + n
  omega

/-- The same physical-edge finite-word domination as SMALL. -/
theorem renewalBankAttemptWord {n : Nat} (ring : DirectedRing n)
    (hn : 5 ≤ n) :
    ∀ (word : List (Fin n))
      (a : RootedSeed ring × RenewalBankMemory n),
      ¬ headlineGeneratedTarget ring a.1.val →
      costWord
        (Prob.attemptStepper (rootedTrialKernel ring hn
          (renewalBankInitialMemory ring)
          (renewalBankTrialAdvance ring)
          (renewalBankTrialCut ring)))
        (fun z => Prob.attemptGood z ∨ Prob.attemptFail z)
        (.active a) word ≤
      costWord (renewalBankNext ring) (renewalBankStop ring)
        (a.1.val, a.2) word := by
  classical
  intro word
  induction word with
  | nil =>
      intro a _
      exact Nat.le_refl 0
  | cons e word ih =>
      intro a hnot
      have hactive : ¬
          (Prob.attemptGood (.active a :
            AttemptNode (RootedSeed ring × RenewalBankMemory n)
              (RootedSeed ring)) ∨
           Prob.attemptFail (.active a :
            AttemptNode (RootedSeed ring × RenewalBankMemory n)
              (RootedSeed ring))) := by
        intro h
        rcases h with h | h
        · exact h
        · exact h
      have hrefnot : ¬ renewalBankStop ring (a.1.val, a.2) := hnot
      rw [renewalWordCostCons _ _
          (AttemptNode.active a :
            AttemptNode (RootedSeed ring × RenewalBankMemory n)
              (RootedSeed ring)) e word hactive,
        renewalWordCostCons _ _ (a.1.val, a.2) e word hrefnot]
      change 1 + costWord _ _
          ((rootedTrialKernel ring hn (renewalBankInitialMemory ring)
            (renewalBankTrialAdvance ring)
            (renewalBankTrialCut ring)).step a e) word ≤
        1 + costWord (renewalBankNext ring) (renewalBankStop ring)
          (renewalBankNext ring (a.1.val, a.2) e) word
      cases hs : (rootedTrialKernel ring hn
          (renewalBankInitialMemory ring)
          (renewalBankTrialAdvance ring)
          (renewalBankTrialCut ring)).step a e with
      | success =>
          rw [costWord_terminal _ _
            (AttemptNode.success :
              AttemptNode (RootedSeed ring × RenewalBankMemory n)
                (RootedSeed ring))
            (by exact Or.inl True.intro) word]
          exact Nat.add_le_add_left (Nat.zero_le _) 1
      | retry seed =>
          rw [costWord_terminal _ _
            (AttemptNode.retry seed :
              AttemptNode (RootedSeed ring × RenewalBankMemory n)
                (RootedSeed ring))
            (by exact Or.inr True.intro) word]
          exact Nat.add_le_add_left (Nat.zero_le _) 1
      | active b =>
          have hs' : rootedTrialStep ring hn
              (renewalBankTrialAdvance ring) (renewalBankTrialCut ring)
              a e = .active b := hs
          unfold rootedTrialStep at hs'
          split at hs'
          · cases hs'
          · rename_i hnext
            split at hs'
            · cases hs'
            · rename_i hnocut
              cases hs'
              have hcut : renewalBankTrialCut ring a e = false := by
                cases hc : renewalBankTrialCut ring a e with
                | false => rfl
                | true => exact False.elim (hnocut hc)
              have href : renewalBankNext ring (a.1.val, a.2) e =
                  ((rootedSuccessor ring hn a.1 e).val,
                    renewalBankTrialAdvance ring a e) := by
                apply Prod.ext
                · exact renewalBankPhysicalBeforeCut ring
                    (a.1.val, a.2) e hcut
                · rfl
              have ht := ih
                (rootedSuccessor ring hn a.1 e,
                  renewalBankTrialAdvance ring a e) hnext
              rw [← href] at ht
              exact Nat.add_le_add_left ht 1

theorem bankReferenceAttemptDomination {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) :
    ReferenceAttemptDomination ring hn
      (bankRootedReferenceData ring hbank) := by
  intro seed hnot word
  exact renewalBankAttemptWord ring hn word
    (seed, renewalBankInitialMemory ring seed) hnot

end L3.HeadlineRenewal


/-!
Necessary horizon-zero condition for BANK origin rarity.

This does NOT claim bankReferenceOriginRarity.
The current RootedReferenceData.Reference is the unrestricted product
of physical configuration and ghost memory. Prob.OriginRarity quantifies
over all such states. An arbitrary ghost may already contain the freshly
allocated origin's identifier with K heads on a different site. Since
renewalBankWinWord tests its post-birth snapshot even on an empty suffix,
the requested global rarity statement is false without a valid-state
refinement of the Reference carrier.

The source BANK rows themselves do not create this bad ancestry from
renewalBankInitialMemory. The issue is the unrestricted quantifier, not
the paper's probability bound for genuinely spawned zero origins.
-/

namespace L3.HeadlineRenewal

set_option autoImplicit false

/-- The empty suffix is a genuine test of the post-birth snapshot. -/
theorem renewalBankWinEmpty {n : Nat}
    (ring : DirectedRing n) (born : RenewalBankBorn n) :
    renewalBankWin ring born [] =
      renewalBankReached born.identity
        (compileAdvice (ceilLogTwo n)).K born.afterBirth.2 := by
  rfl

/-- In particular, a forged already-reached origin wins on no edges. -/
theorem renewalBankWinAlreadyReached {n : Nat}
    (ring : DirectedRing n) (born : RenewalBankBorn n)
    (h : renewalBankReached born.identity
      (compileAdvice (ceilLogTwo n)).K born.afterBirth.2 = true) :
    renewalBankWin ring born [] = true := by
  rw [renewalBankWinEmpty]
  exact h

/-- Necessary, but not sufficient, condition for unrestricted rarity:
a spawn from a nonterminal reference state must not already have K
heads in its post-birth snapshot. The original BANK memory type does
not enforce this condition. -/
def RenewalBankNoInstantBirth {n : Nat}
    (ring : DirectedRing n) : Prop :=
  ∀ (r : RenewalBankReference n), ¬ renewalBankStop ring r →
    ∀ (e : Fin n) (born : RenewalBankBorn n),
      born ∈ renewalBankSpawn ring r e →
        renewalBankReached born.identity
          (compileAdvice (ceilLogTwo n)).K born.afterBirth.2 = false

/-- A formal reduction: the requested OriginRarity would force the
missing snapshot condition already at T=0. -/
theorem renewalBankRarityRequiresNoInstantBirth {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hden : 1 <
      2 ^ (2 * ceilLogTwo n +
        (compileAdvice (ceilLogTwo n)).kappa))
    (hrare : ReferenceOriginRarity ring
      (bankRootedReferenceData ring hbank)
      (compileAdvice (ceilLogTwo n)).kappa) :
    RenewalBankNoInstantBirth ring := by
  intro r hnot e born hmem
  have hconcrete :
      Prob.OriginRarity (renewalBankStop ring)
        (renewalBankSpawn ring) (renewalBankWin ring)
        1 (2 ^ (2 * ceilLogTwo n +
          (compileAdvice (ceilLogTwo n)).kappa)) := hrare
  have hmass :
      (2 ^ (2 * ceilLogTwo n +
        (compileAdvice (ceilLogTwo n)).kappa)) *
        Prob.indicator (renewalBankWin ring born []) ≤ 1 := by
    simpa [Prob.scheduleSum, FixedSpanRenewalPayload.wordSum,
      allSchedules] using hconcrete r hnot e born hmem 0
  have hnowin : renewalBankWin ring born [] = false := by
    cases hw : renewalBankWin ring born [] with
    | false =>
        rfl
    | true =>
        have hsmall :
            2 ^ (2 * ceilLogTwo n +
              (compileAdvice (ceilLogTwo n)).kappa) ≤ 1 := by
          simpa [Prob.indicator, hw] using hmass
        omega
  exact (renewalBankWinEmpty ring born).symm.trans hnowin

/-- Exact existential witness excluded by OriginRarity.
It is easy to realize in an unrestricted Cartesian ghost snapshot:
on edge e -> rightNeighbor e the physical records have root
RWAIT/no grant and first-digit RL/unchanged role; the digit carries
PendingReset receipt lam. At an unrelated physical site z, store an
active payload with the same would-be origin identifier
{service := m.service, root := e, receipt := lam} and heads := K.
The selected edge accepts lam and frames z. Then this proposition
holds with a born snapshot which already contains K heads. -/
def RenewalBankReusedOriginWitness {n : Nat}
    (ring : DirectedRing n) : Prop :=
  ∃ (r : RenewalBankReference n) (e : Fin n)
      (born : RenewalBankBorn n),
    ¬ renewalBankStop ring r ∧
    born ∈ renewalBankSpawn ring r e ∧
    renewalBankReached born.identity
      (compileAdvice (ceilLogTwo n)).K born.afterBirth.2 = true

/-- A witness immediately contradicts the requested unrestricted
OriginRarity, without appealing to any probabilistic limit. -/
theorem renewalBankRarityBlockedByReusedOrigin {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hden : 1 <
      2 ^ (2 * ceilLogTwo n +
        (compileAdvice (ceilLogTwo n)).kappa))
    (hwitness : RenewalBankReusedOriginWitness ring) :
    ¬ ReferenceOriginRarity ring
      (bankRootedReferenceData ring hbank)
      (compileAdvice (ceilLogTwo n)).kappa := by
  intro hrare
  obtain ⟨r, e, born, hnot, hmem, hwin⟩ := hwitness
  have hclean := renewalBankRarityRequiresNoInstantBirth
    ring hbank hden hrare
  have hfalse := hclean r hnot e born hmem
  rw [hwin] at hfalse
  cases hfalse

/-- The actual history class needed by a valid-snapshot reference.
This is a proof-only ancestry predicate, not a new protocol field.
To use it in Prob.OriginRarity, the Reference carrier must be
restricted to this class (or spawn must reject unvalidated states).
Merely proving it of initial runs does not restrict the existing
universal quantifier. -/
inductive RenewalBankCausalReference {n : Nat}
    (ring : DirectedRing n) : RenewalBankReference n → Prop
  | initial (seed : RootedSeed ring) :
      RenewalBankCausalReference ring (renewalBankStart ring seed)
  | step (r : RenewalBankReference n) (e : Fin n) :
      RenewalBankCausalReference ring r →
      RenewalBankCausalReference ring (renewalBankNext ring r e)

end L3.HeadlineRenewal


namespace L3.HeadlineRenewal

open Classical
open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree
open PPL.Convergence.LDLocal (AttemptNode RetryKernel retryCount)

set_option autoImplicit false
set_option Elab.async false

/-!
A stamp rank stores zero for an
empty/atom-only field and origin.service+1 or receipt.service+1
for an occupied field. Thus rank <= memory.service expresses
exactly that every stored origin or pending receipt was made at
an earlier service. No head counter bound is imposed.
-/

def renewalBankPayloadStamp {n : Nat}
    (p : RenewalBankPayload n) : Nat :=
  match p.origin with
  | none => 0
  | some o => o.service + 1

def renewalBankWorkerStamp {n : Nat} :
    RenewalBankWorker n → Nat
  | .empty => 0
  | .pending receipt => receipt.service + 1
  | .payload p => renewalBankPayloadStamp p

def renewalBankControllerStamp {n : Nat} :
    RenewalBankController n → Nat
  | .empty => 0
  | .waiting _ => 0
  | .active p => renewalBankPayloadStamp p

def renewalBankSiteStamp {n : Nat}
    (site : RenewalBankSite n) : Nat :=
  max (renewalBankWorkerStamp site.worker)
    (renewalBankControllerStamp site.controller)

/-- Strictly older origin/receipt timestamps at all sites,
including both worker and controller locations. Waiting slots
contain only inherited atoms and have zero stamp. -/
def RenewalBankValid {n : Nat}
    (r : RenewalBankReference n) : Prop :=
  ∀ i : Fin n,
    renewalBankSiteStamp (r.2.sites i) ≤ r.2.service

theorem renewalBankValidStart {n : Nat}
    (ring : DirectedRing n) (seed : RootedSeed ring) :
    RenewalBankValid (renewalBankStart ring seed) := by
  intro i
  change renewalBankSiteStamp
    (renewalBankInitialSite seed.val i) ≤ 0
  cases hm : (seed.val i).mode <;>
    by_cases ht : (seed.val i).tok = BTok.E <;>
    by_cases hp : (seed.val i).pack = 0 <;>
    simp [renewalBankSiteStamp, renewalBankWorkerStamp,
      renewalBankControllerStamp, renewalBankPayloadStamp,
      renewalBankInitialSite, renewalBankEntrancePayload, hm, ht, hp]

private theorem renewalBankWorkerPayloadStamp_le {n : Nat}
    (w : RenewalBankWorker n) (i : Fin n) :
    renewalBankPayloadStamp (renewalBankWorkerPayload w i) ≤
      renewalBankWorkerStamp w := by
  cases w with
  | empty =>
      simp [renewalBankWorkerPayload, renewalBankWorkerStamp,
        renewalBankPayloadStamp, renewalBankEntrancePayload]
  | pending receipt =>
      simp [renewalBankWorkerPayload, renewalBankWorkerStamp,
        renewalBankPayloadStamp, renewalBankEntrancePayload]
  | payload p =>
      exact Nat.le_refl _

private theorem renewalBankActivePayloadStamp_le {n : Nat}
    (c : RenewalBankController n) (i : Fin n) :
    renewalBankPayloadStamp (renewalBankActivePayload c i) ≤
      renewalBankControllerStamp c := by
  cases c with
  | empty =>
      simp [renewalBankActivePayload, renewalBankControllerStamp,
        renewalBankPayloadStamp, renewalBankEntrancePayload]
  | waiting atoms =>
      simp [renewalBankActivePayload, renewalBankControllerStamp,
        renewalBankPayloadStamp, renewalBankEntrancePayload]
  | active p =>
      exact Nat.le_refl _

private theorem renewalBankReturnedStamp {n : Nat}
    (c : RenewalBankController n)
    (w : RenewalBankWorker n) (i : Fin n) :
    renewalBankPayloadStamp (renewalBankReturned c w i) =
      renewalBankPayloadStamp (renewalBankWorkerPayload w i) := by
  rfl

private theorem renewalBankHeadStamp {n : Nat}
    (p : RenewalBankPayload n) :
    renewalBankPayloadStamp (renewalBankHead p) =
      renewalBankPayloadStamp p := by
  rfl

private theorem renewalBankWaitStampLe {n : Nat}
    (mode : Mode) (lease : Nat) (c : RenewalBankController n) :
    renewalBankControllerStamp (renewalBankWaitSlot mode lease c) ≤
      renewalBankControllerStamp c := by
  unfold renewalBankWaitSlot
  split
  · split
    · exact Nat.le_refl _
    · exact Nat.zero_le _
  · exact Nat.le_refl _

private theorem renewalBankFreshOriginStamp {n : Nat}
    (s : Nat) (root : Fin n) (receipt : RenewalBankReceipt n)
    (atoms : List (RenewalBankAtom n)) (heads : Nat) :
    renewalBankPayloadStamp
      ({ atoms := atoms, origin := some { service := s, root := root, receipt := receipt }, heads := heads } : RenewalBankPayload n) = s + 1 := by
  rfl

private theorem renewalBankFreshReceiptStamp {n : Nat}
    (s : Nat) (root : Fin n) :
    renewalBankWorkerStamp
      (.pending { service := s, root := root } :
        RenewalBankWorker n) = s + 1 := by
  rfl

/-!
An explicit two-field shape for every BANK pair-row output.

The worker and controller alternatives deliberately permit combinations
that never occur simultaneously. This makes the shape stable under
separate worker/controller erasures and transfers without asserting any
new property of the physical protocol.
-/

inductive RenewalBankWorkerShape {n : Nat}
    (m : RenewalBankMemory n) (e dest : Fin n) :
    RenewalBankWorker n → Prop where
  | source :
      RenewalBankWorkerShape m e dest (m.sites e).worker
  | target :
      RenewalBankWorkerShape m e dest (m.sites dest).worker
  | cleared :
      RenewalBankWorkerShape m e dest .empty
  | pending :
      RenewalBankWorkerShape m e dest
        (.pending { service := m.service, root := e })
  | sourcePayload :
      RenewalBankWorkerShape m e dest
        (.payload (renewalBankActivePayload (m.sites e).controller e))
  | sourceHead :
      RenewalBankWorkerShape m e dest
        (.payload (renewalBankHead
          (renewalBankActivePayload (m.sites e).controller e)))
  | entrancePayload :
      RenewalBankWorkerShape m e dest
        (.payload (renewalBankEntrancePayload e true))
  | entranceHead :
      RenewalBankWorkerShape m e dest
        (.payload (renewalBankHead (renewalBankEntrancePayload e true)))

inductive RenewalBankControllerShape {n : Nat}
    (m : RenewalBankMemory n) (e dest : Fin n) :
    RenewalBankController n → Prop where
  | source :
      RenewalBankControllerShape m e dest (m.sites e).controller
  | target :
      RenewalBankControllerShape m e dest (m.sites dest).controller
  | cleared :
      RenewalBankControllerShape m e dest .empty
  | waiting :
      RenewalBankControllerShape m e dest (.waiting [])
  | fresh (receipt : RenewalBankReceipt n)
      (atoms : List (RenewalBankAtom n)) :
      RenewalBankControllerShape m e dest
        (.active
          { atoms := atoms
            origin := some
              { service := m.service, root := e, receipt := receipt }
            heads := 0 })
  | returnedTarget (atoms : List (RenewalBankAtom n)) :
      RenewalBankControllerShape m e dest
        (.active
          { (renewalBankWorkerPayload
              (m.sites dest).worker dest) with atoms := atoms })
  | returnedEmpty (atoms : List (RenewalBankAtom n)) :
      RenewalBankControllerShape m e dest
        (.active
          { (renewalBankEntrancePayload dest false) with atoms := atoms })
  | sourceHead :
      RenewalBankControllerShape m e dest
        (.active (renewalBankHead
          (renewalBankActivePayload (m.sites e).controller e)))
  | entranceHead :
      RenewalBankControllerShape m e dest
        (.active (renewalBankHead (renewalBankEntrancePayload e true)))

/-- A site is obtained by independently selecting one of the
explicitly enumerated worker and controller BANK row outputs.
Waiting atoms never carry an origin. -/
def RenewalBankSiteShape {n : Nat}
    (m : RenewalBankMemory n) (e dest : Fin n)
    (s : RenewalBankSite n) : Prop :=
  RenewalBankWorkerShape m e dest s.worker ∧
    RenewalBankControllerShape m e dest s.controller

attribute [simp]
  RenewalBankWorkerShape.source
  RenewalBankWorkerShape.target
  RenewalBankWorkerShape.cleared
  RenewalBankWorkerShape.pending
  RenewalBankWorkerShape.sourcePayload
  RenewalBankWorkerShape.sourceHead
  RenewalBankWorkerShape.entrancePayload
  RenewalBankWorkerShape.entranceHead
  RenewalBankControllerShape.source
  RenewalBankControllerShape.target
  RenewalBankControllerShape.cleared
  RenewalBankControllerShape.waiting
  RenewalBankControllerShape.fresh
  RenewalBankControllerShape.returnedTarget
  RenewalBankControllerShape.returnedEmpty
  RenewalBankControllerShape.sourceHead
  RenewalBankControllerShape.entranceHead

/-- A returned OLD worker, with arbitrary waiting atoms merged,
has one of the declared controller shapes. -/
@[simp] private theorem renewalBankControllerShapeReturnedTarget {n : Nat}
    (m : RenewalBankMemory n) (e dest : Fin n)
    (c : RenewalBankController n) :
    RenewalBankControllerShape m e dest
      (.active (renewalBankReturned c (m.sites dest).worker dest)) := by
  exact RenewalBankControllerShape.returnedTarget
    ((renewalBankWorkerPayload (m.sites dest).worker dest).atoms ++
      renewalBankWaitingAtoms c)

/-- A returned erased/pending-free worker has the fallback
entrance payload with no origin. -/
@[simp] private theorem renewalBankControllerShapeReturnedEmpty {n : Nat}
    (m : RenewalBankMemory n) (e dest : Fin n)
    (c : RenewalBankController n) :
    RenewalBankControllerShape m e dest
      (.active (renewalBankReturned c .empty dest)) := by
  exact RenewalBankControllerShape.returnedEmpty
    ((renewalBankEntrancePayload dest false).atoms ++
      renewalBankWaitingAtoms c)

/-- Every permitted worker field has an OLD or current-service
timestamp. -/
private theorem renewalBankWorkerShapeBound {n : Nat}
    (m : RenewalBankMemory n) (e dest : Fin n)
    (w : RenewalBankWorker n)
    (he : renewalBankSiteStamp (m.sites e) ≤ m.service)
    (hd : renewalBankSiteStamp (m.sites dest) ≤ m.service)
    (hw : RenewalBankWorkerShape m e dest w) :
    renewalBankWorkerStamp w ≤ m.service + 1 := by
  cases hw with
  | source =>
      have h := Nat.le_max_left
        (renewalBankWorkerStamp (m.sites e).worker)
        (renewalBankControllerStamp (m.sites e).controller)
      unfold renewalBankSiteStamp at he
      omega
  | target =>
      have h := Nat.le_max_left
        (renewalBankWorkerStamp (m.sites dest).worker)
        (renewalBankControllerStamp (m.sites dest).controller)
      unfold renewalBankSiteStamp at hd
      omega
  | cleared =>
      simp [renewalBankWorkerStamp]
  | pending =>
      exact Nat.le_refl _
  | sourcePayload =>
      have hs := renewalBankActivePayloadStamp_le (m.sites e).controller e
      have hc := Nat.le_max_right
        (renewalBankWorkerStamp (m.sites e).worker)
        (renewalBankControllerStamp (m.sites e).controller)
      unfold renewalBankSiteStamp at he
      change renewalBankPayloadStamp
        (renewalBankActivePayload (m.sites e).controller e) ≤
          m.service + 1
      omega
  | sourceHead =>
      have hs := renewalBankActivePayloadStamp_le (m.sites e).controller e
      have hc := Nat.le_max_right
        (renewalBankWorkerStamp (m.sites e).worker)
        (renewalBankControllerStamp (m.sites e).controller)
      unfold renewalBankSiteStamp at he
      change renewalBankPayloadStamp
        (renewalBankHead
          (renewalBankActivePayload (m.sites e).controller e)) ≤
            m.service + 1
      rw [renewalBankHeadStamp]
      omega
  | entrancePayload =>
      simp [renewalBankWorkerStamp,
        renewalBankPayloadStamp, renewalBankEntrancePayload]
  | entranceHead =>
      simp [renewalBankWorkerStamp, renewalBankHead,
        renewalBankPayloadStamp, renewalBankEntrancePayload]

/-- Every permitted controller field has an OLD or current-service
timestamp, independently of its inherited waiting atoms. -/
private theorem renewalBankControllerShapeBound {n : Nat}
    (m : RenewalBankMemory n) (e dest : Fin n)
    (c : RenewalBankController n)
    (he : renewalBankSiteStamp (m.sites e) ≤ m.service)
    (hd : renewalBankSiteStamp (m.sites dest) ≤ m.service)
    (hc : RenewalBankControllerShape m e dest c) :
    renewalBankControllerStamp c ≤ m.service + 1 := by
  cases hc with
  | source =>
      have h := Nat.le_max_right
        (renewalBankWorkerStamp (m.sites e).worker)
        (renewalBankControllerStamp (m.sites e).controller)
      unfold renewalBankSiteStamp at he
      omega
  | target =>
      have h := Nat.le_max_right
        (renewalBankWorkerStamp (m.sites dest).worker)
        (renewalBankControllerStamp (m.sites dest).controller)
      unfold renewalBankSiteStamp at hd
      omega
  | cleared =>
      simp [renewalBankControllerStamp]
  | waiting =>
      simp [renewalBankControllerStamp]
  | fresh receipt atoms =>
      exact Nat.le_refl _
  | returnedTarget atoms =>
      have hs := renewalBankWorkerPayloadStamp_le
        (m.sites dest).worker dest
      have hw := Nat.le_max_left
        (renewalBankWorkerStamp (m.sites dest).worker)
        (renewalBankControllerStamp (m.sites dest).controller)
      unfold renewalBankSiteStamp at hd
      change renewalBankPayloadStamp
        { (renewalBankWorkerPayload (m.sites dest).worker dest)
          with atoms := atoms } ≤ m.service + 1
      change renewalBankPayloadStamp
        (renewalBankWorkerPayload (m.sites dest).worker dest) ≤
          m.service + 1
      omega
  | returnedEmpty atoms =>
      simp [renewalBankControllerStamp, renewalBankPayloadStamp,
        renewalBankEntrancePayload]
  | sourceHead =>
      have hs := renewalBankActivePayloadStamp_le
        (m.sites e).controller e
      have hw := Nat.le_max_right
        (renewalBankWorkerStamp (m.sites e).worker)
        (renewalBankControllerStamp (m.sites e).controller)
      unfold renewalBankSiteStamp at he
      change renewalBankPayloadStamp
        (renewalBankHead
          (renewalBankActivePayload (m.sites e).controller e)) ≤
            m.service + 1
      rw [renewalBankHeadStamp]
      omega
  | entranceHead =>
      simp [renewalBankControllerStamp, renewalBankHead,
        renewalBankPayloadStamp, renewalBankEntrancePayload]

private theorem renewalBankSiteShapeBound {n : Nat}
    (m : RenewalBankMemory n) (e dest : Fin n)
    (s : RenewalBankSite n)
    (he : renewalBankSiteStamp (m.sites e) ≤ m.service)
    (hd : renewalBankSiteStamp (m.sites dest) ≤ m.service)
    (hs : RenewalBankSiteShape m e dest s) :
    renewalBankSiteStamp s ≤ m.service + 1 := by
  have hw := renewalBankWorkerShapeBound m e dest s.worker he hd hs.1
  have hc := renewalBankControllerShapeBound m e dest s.controller he hd hs.2
  unfold renewalBankSiteStamp
  omega

/-!
The proof below splits the guards on the *site-shaped* result,
not on the already evaluated worker/controller stamp. In each leaf
the source and destination sites are literal record updates.
-/
/-- A site-shape proposition distributes over a conditional site. -/
private theorem renewalBankSiteShapeIf {n : Nat}
    (m : RenewalBankMemory n) (e dest : Fin n)
    (guard : Prop) [Decidable guard]
    (sa sb : RenewalBankSite n) :
    RenewalBankSiteShape m e dest (if guard then sa else sb) ↔
      (if guard then RenewalBankSiteShape m e dest sa
       else RenewalBankSiteShape m e dest sb) := by
  by_cases hg : guard
  · simp [hg]
  · simp [hg]

/-- A worker-shape proposition distributes over a conditional worker. -/
private theorem renewalBankWorkerShapeIf {n : Nat}
    (m : RenewalBankMemory n) (e dest : Fin n)
    (guard : Prop) [Decidable guard]
    (wa wb : RenewalBankWorker n) :
    RenewalBankWorkerShape m e dest (if guard then wa else wb) ↔
      (if guard then RenewalBankWorkerShape m e dest wa
       else RenewalBankWorkerShape m e dest wb) := by
  by_cases hg : guard
  · simp [hg]
  · simp [hg]

/-- A controller-shape proposition distributes over a conditional controller. -/
private theorem renewalBankControllerShapeIf {n : Nat}
    (m : RenewalBankMemory n) (e dest : Fin n)
    (guard : Prop) [Decidable guard]
    (ca cb : RenewalBankController n) :
    RenewalBankControllerShape m e dest (if guard then ca else cb) ↔
      (if guard then RenewalBankControllerShape m e dest ca
       else RenewalBankControllerShape m e dest cb) := by
  by_cases hg : guard
  · simp [hg]
  · simp [hg]

/-- Both sites produced by accepting an RL receipt have the declared
BANK shape, regardless of whether the old destination worker was
pending, empty, or carrying a payload. -/
private theorem renewalBankAcceptShape {n : Nat}
    (m : RenewalBankMemory n) (e dest : Fin n) :
    RenewalBankSiteShape m e dest
      ((match (m.sites dest).worker with
        | .pending receipt =>
            ({ worker := .empty,
               controller := .active
                 { atoms := renewalBankWaitingAtoms (m.sites e).controller,
                   origin := some
                     { service := m.service, root := e, receipt := receipt },
                   heads := 0 } },
             { worker := .empty, controller := .empty })
        | _ =>
            ({ worker := .empty,
               controller := .active
                 (renewalBankReturned (m.sites e).controller
                   (m.sites dest).worker dest) },
             { worker := .empty, controller := .empty }))
        : RenewalBankSite n × RenewalBankSite n).1 ∧
    RenewalBankSiteShape m e dest
      ((match (m.sites dest).worker with
        | .pending receipt =>
            ({ worker := .empty,
               controller := .active
                 { atoms := renewalBankWaitingAtoms (m.sites e).controller,
                   origin := some
                     { service := m.service, root := e, receipt := receipt },
                   heads := 0 } },
             { worker := .empty, controller := .empty })
        | _ =>
            ({ worker := .empty,
               controller := .active
                 (renewalBankReturned (m.sites e).controller
                   (m.sites dest).worker dest) },
             { worker := .empty, controller := .empty }))
        : RenewalBankSite n × RenewalBankSite n).2 := by
  have hreturned :
      RenewalBankControllerShape m e dest
        (.active (renewalBankReturned (m.sites e).controller
          (m.sites dest).worker dest)) :=
    renewalBankControllerShapeReturnedTarget m e dest
      (m.sites e).controller
  cases hw : (m.sites dest).worker with
  | empty =>
      simp only [hw] at hreturned ⊢
      exact ⟨⟨.cleared, hreturned⟩, ⟨.cleared, .cleared⟩⟩
  | pending receipt =>
      simp only [hw] at hreturned ⊢
      exact ⟨⟨.cleared,
        .fresh receipt (renewalBankWaitingAtoms (m.sites e).controller)⟩,
        ⟨.cleared, .cleared⟩⟩
  | payload p =>
      simp only [hw] at hreturned ⊢
      exact ⟨⟨.cleared, hreturned⟩, ⟨.cleared, .cleared⟩⟩

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 12000 in
private theorem renewalBankPairShape {n : Nat}
    (c : Compiled) (m : RenewalBankMemory n)
    (e dest : Fin n) (x y : Agent c) :
    RenewalBankSiteShape m e dest
      (renewalBankPairMemory c m e dest x y).1 ∧
      RenewalBankSiteShape m e dest
        (renewalBankPairMemory c m e dest x y).2 := by
  unfold renewalBankPairMemory
  simp only [Id.run, bind, pure, apply_ite Prod.fst,
    apply_ite Prod.snd, renewalBankSiteShapeIf]
  simp [RenewalBankSiteShape, renewalBankWaitSlot,
    renewalBankWorkerShapeIf, renewalBankControllerShapeIf]
  all_goals (repeat' (first | split | (intro) | (refine And.intro ?_ ?_)))
  all_goals simp_all [RenewalBankSiteShape, renewalBankWaitSlot,
    renewalBankWorkerShapeIf, renewalBankControllerShapeIf]
  all_goals
    repeat' intro
    first
    | exact (renewalBankAcceptShape m e dest).1
    | exact (renewalBankAcceptShape m e dest).2

private theorem renewalBankPairStampBound {n : Nat}
    (c : Compiled) (m : RenewalBankMemory n)
    (e dest : Fin n) (x y : Agent c)
    (he : renewalBankSiteStamp (m.sites e) ≤ m.service)
    (hd : renewalBankSiteStamp (m.sites dest) ≤ m.service) :
    renewalBankSiteStamp
        (renewalBankPairMemory c m e dest x y).1 ≤
        m.service + 1 ∧
      renewalBankSiteStamp
        (renewalBankPairMemory c m e dest x y).2 ≤
        m.service + 1 := by
  have hs := renewalBankPairShape c m e dest x y
  exact ⟨renewalBankSiteShapeBound m e dest _ he hd hs.1,
    renewalBankSiteShapeBound m e dest _ he hd hs.2⟩

/-- Preservation at every actual BANK reference step.
The responder/source precedence also covers n = 1. -/
theorem renewalBankValidNext {n : Nat}
    (ring : DirectedRing n)
    (r : RenewalBankReference n) (e : Fin n)
    (h : RenewalBankValid r) :
    RenewalBankValid (renewalBankNext ring r e) := by
  intro i
  have hp := renewalBankPairStampBound
    (compileAdvice (ceilLogTwo n)) r.2 e (ring.rightNeighbor e)
    (r.1 e) (r.1 (ring.rightNeighbor e))
    (h e) (h (ring.rightNeighbor e))
  change renewalBankSiteStamp
      (if i = e then
        (renewalBankPairMemory
          (compileAdvice (ceilLogTwo n)) r.2 e
          (ring.rightNeighbor e)
          (r.1 e) (r.1 (ring.rightNeighbor e))).1
       else if i = ring.rightNeighbor e then
        (renewalBankPairMemory
          (compileAdvice (ceilLogTwo n)) r.2 e
          (ring.rightNeighbor e)
          (r.1 e) (r.1 (ring.rightNeighbor e))).2
       else r.2.sites i) ≤ r.2.service + 1
  split
  · exact hp.1
  · split
    · exact hp.2
    · have ho := h i
      omega

/-- The valid subset is closed, even though the unrestricted
Cartesian memory class is not suitable for OriginRarity. -/
def bankValidRootedReferenceData {n : Nat}
    (ring : DirectedRing n)
    (_hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) :
    RootedReferenceData ring :=
  { Memory := RenewalBankMemory n
    Reference := {r : RenewalBankReference n // RenewalBankValid r}
    Origin := RenewalBankBorn n
    initialMemory := renewalBankInitialMemory ring
    memoryNext := renewalBankTrialAdvance ring
    cut := renewalBankTrialCut ring
    referenceNext := fun r e =>
      ⟨renewalBankNext ring r.val e,
        renewalBankValidNext ring r.val e r.property⟩
    referenceStop := fun r => renewalBankStop ring r.val
    referenceStart := fun seed =>
      ⟨renewalBankStart ring seed,
        renewalBankValidStart ring seed⟩
    spawn := fun r e => renewalBankSpawn ring r.val e
    win := renewalBankWin ring }

/-- Cost of a valid run is exactly cost of its unrestricted
projection, with no conditional coupling assumption. -/
private theorem renewalBankValidCostProjection {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) :
    ∀ (word : List (Fin n))
      (r : (bankValidRootedReferenceData ring hbank).Reference),
      costWord
        (bankValidRootedReferenceData ring hbank).referenceNext
        (bankValidRootedReferenceData ring hbank).referenceStop r word =
      costWord (renewalBankNext ring) (renewalBankStop ring)
        r.val word := by
  classical
  intro word
  induction word with
  | nil =>
      intro r
      rfl
  | cons e word ih =>
      intro r
      by_cases hs : renewalBankStop ring r.val
      · have hvalid :
            (bankValidRootedReferenceData ring hbank).referenceStop r :=
          hs
        exact (costWord_terminal _ _ r hvalid (e :: word)).trans
          (costWord_terminal _ _ _ hs (e :: word)).symm
      · have hvalid :
            ¬ (bankValidRootedReferenceData ring hbank).referenceStop r :=
          hs
        rw [renewalWordCostCons _ _ r e word hvalid,
          renewalWordCostCons _ _ r.val e word hs]
        exact congrArg (fun q : Nat => 1 + q)
          (ih ((bankValidRootedReferenceData ring hbank).referenceNext r e))

/-- The same exact projection for the count of pre-edge births. -/
private theorem renewalBankValidOriginsProjection {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) :
    ∀ (word : List (Fin n))
      (r : (bankValidRootedReferenceData ring hbank).Reference),
      Prob.originsWord
        (bankValidRootedReferenceData ring hbank).referenceNext
        (bankValidRootedReferenceData ring hbank).referenceStop
        (bankValidRootedReferenceData ring hbank).spawn r word =
      Prob.originsWord
        (renewalBankNext ring) (renewalBankStop ring)
        (renewalBankSpawn ring) r.val word := by
  classical
  intro word
  induction word with
  | nil =>
      intro r
      rfl
  | cons e word ih =>
      intro r
      by_cases hs : renewalBankStop ring r.val
      · have hvalid :
            (bankValidRootedReferenceData ring hbank).referenceStop r :=
          hs
        rw [Prob.originsWord, if_pos hvalid,
          Prob.originsWord, if_pos hs]
      · have hvalid :
            ¬ (bankValidRootedReferenceData ring hbank).referenceStop r :=
          hs
        rw [Prob.originsWord, if_neg hvalid,
          Prob.originsWord, if_neg hs]
        exact congrArg
          (fun q : Nat => (renewalBankSpawn ring r.val e).length + q)
          (ih ((bankValidRootedReferenceData ring hbank).referenceNext r e))

/-- F.1 is unchanged after restricting Reference to valid ghosts. -/
theorem bankValidReferenceOriginCharge {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) :
    ReferenceOriginCharge ring
      (bankValidRootedReferenceData ring hbank) := by
  intro seed hnot word
  rw [renewalBankValidOriginsProjection ring hbank word
        ((bankValidRootedReferenceData ring hbank).referenceStart seed),
      renewalBankValidCostProjection ring hbank word
        ((bankValidRootedReferenceData ring hbank).referenceStart seed)]
  exact bankReferenceOriginCharge ring hbank seed hnot word

/-- The trial uses the same unrestricted Memory type.
Its one-step domination is unaffected by the Reference subtype. -/
theorem bankValidReferenceAttemptDomination {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) :
    ReferenceAttemptDomination ring hn
      (bankValidRootedReferenceData ring hbank) := by
  intro seed hnot word
  rw [renewalBankValidCostProjection ring hbank word
        ((bankValidRootedReferenceData ring hbank).referenceStart seed)]
  exact renewalBankAttemptWord ring hn word
    (seed, renewalBankInitialMemory ring seed) hnot

/-- Still open: a valid birth snapshot cannot have already
reached the required K heads at the exact creating service.
The time-stamp invariant rules out an OLD duplicate, but the
formal row bridge to this K-head fact is separate. -/
def RenewalBankValidNoInstantBirth {n : Nat}
    (ring : DirectedRing n) : Prop :=
  ∀ (r : {r : RenewalBankReference n // RenewalBankValid r}),
    ¬ renewalBankStop ring r.val →
    ∀ (e : Fin n) (born : RenewalBankBorn n),
      born ∈ renewalBankSpawn ring r.val e →
        renewalBankReached born.identity
          (compileAdvice (ceilLogTwo n)).K born.afterBirth.2 = false

end L3.HeadlineRenewal

/-!
BANK birth-snapshot certificate.

The stamp invariant excludes the newly allocated origin identifier
from every OLD worker and controller field. The BANK output-shape
invariant enumerates every changed field. Its only new-origin
controller alternative is the pending-RL acceptance row, whose
head count is literally zero. Thus a birth cannot have K heads
at the service that creates it.

This certificate does not assert the future-suffix probability bound.
-/

namespace L3.HeadlineRenewal

open Classical

set_option autoImplicit false
set_option Elab.async false

private theorem renewalBankThresholdPositive (n : Nat) :
    0 < (compileAdvice (ceilLogTwo n)).K := by
  change 0 < 2 * ceilLogTwo n + productionKappa (ceilLogTwo n)
  by_cases hq : ceilLogTwo n = 0
  · simp [hq, productionKappa, finiteKappa]
  · omega

private theorem renewalBankOldPayloadNoHit {n : Nat}
    (m : RenewalBankMemory n) (o : RenewalBankOrigin n)
    (K : Nat) (p : RenewalBankPayload n)
    (ho : o.service = m.service)
    (hp : renewalBankPayloadStamp p ≤ m.service) :
    renewalBankPayloadReached o K p = false := by
  have hneq : p.origin ≠ some o := by
    intro heq
    have hstamp : o.service + 1 ≤ m.service := by
      simpa [renewalBankPayloadStamp, heq] using hp
    omega
  simp [renewalBankPayloadReached, hneq]

private theorem renewalBankOldWorkerNoHit {n : Nat}
    (m : RenewalBankMemory n) (o : RenewalBankOrigin n)
    (K : Nat) (w : RenewalBankWorker n)
    (ho : o.service = m.service)
    (hw : renewalBankWorkerStamp w ≤ m.service) :
    (match (generalizing := false) w with
     | .payload p => renewalBankPayloadReached o K p
     | _ => false) = false := by
  cases w with
  | empty => rfl
  | pending receipt => rfl
  | payload p =>
      exact renewalBankOldPayloadNoHit m o K p ho hw

private theorem renewalBankOldControllerNoHit {n : Nat}
    (m : RenewalBankMemory n) (o : RenewalBankOrigin n)
    (K : Nat) (c : RenewalBankController n)
    (ho : o.service = m.service)
    (hc : renewalBankControllerStamp c ≤ m.service) :
    (match (generalizing := false) c with
     | .active p => renewalBankPayloadReached o K p
     | _ => false) = false := by
  cases c with
  | empty => rfl
  | waiting atoms => rfl
  | active p =>
      exact renewalBankOldPayloadNoHit m o K p ho hc

private theorem renewalBankOldSiteNoHit {n : Nat}
    (m : RenewalBankMemory n) (o : RenewalBankOrigin n)
    (K : Nat) (site : RenewalBankSite n)
    (ho : o.service = m.service)
    (hs : renewalBankSiteStamp site ≤ m.service) :
    renewalBankSiteReached o K site = false := by
  have hw : renewalBankWorkerStamp site.worker ≤ m.service :=
    Nat.le_trans (Nat.le_max_left _ _) hs
  have hc : renewalBankControllerStamp site.controller ≤ m.service :=
    Nat.le_trans (Nat.le_max_right _ _) hs
  unfold renewalBankSiteReached
  rw [renewalBankOldWorkerNoHit m o K site.worker ho hw,
    renewalBankOldControllerNoHit m o K site.controller ho hc]
  rfl

/-- No worker alternative of an actual BANK pair can carry a
current-service completed origin: worker transfers are OLD,
pending is a receipt, and entrance payloads have no origin. -/
private theorem renewalBankWorkerShapeNoBirthHit {n : Nat}
    (m : RenewalBankMemory n) (e dest : Fin n)
    (o : RenewalBankOrigin n) (K : Nat)
    (ho : o.service = m.service)
    (he : renewalBankSiteStamp (m.sites e) ≤ m.service)
    (hd : renewalBankSiteStamp (m.sites dest) ≤ m.service)
    (w : RenewalBankWorker n)
    (hs : RenewalBankWorkerShape m e dest w) :
    (match (generalizing := false) w with
     | .payload p => renewalBankPayloadReached o K p
     | _ => false) = false := by
  have hsource : renewalBankWorkerStamp (m.sites e).worker ≤ m.service :=
    Nat.le_trans (Nat.le_max_left _ _) he
  have htarget : renewalBankWorkerStamp (m.sites dest).worker ≤ m.service :=
    Nat.le_trans (Nat.le_max_left _ _) hd
  have hcontroller :
      renewalBankControllerStamp (m.sites e).controller ≤ m.service :=
    Nat.le_trans (Nat.le_max_right _ _) he
  have hactive :
      renewalBankPayloadStamp
        (renewalBankActivePayload (m.sites e).controller e) ≤
        m.service :=
    Nat.le_trans
      (renewalBankActivePayloadStamp_le (m.sites e).controller e)
      hcontroller
  cases hs with
  | source =>
      exact renewalBankOldWorkerNoHit m o K (m.sites e).worker ho hsource
  | target =>
      exact renewalBankOldWorkerNoHit m o K (m.sites dest).worker ho htarget
  | cleared => rfl
  | pending => rfl
  | sourcePayload =>
      exact renewalBankOldPayloadNoHit m o K
        (renewalBankActivePayload (m.sites e).controller e) ho hactive
  | sourceHead =>
      have hhead :
          renewalBankPayloadStamp
            (renewalBankHead
              (renewalBankActivePayload (m.sites e).controller e)) ≤
            m.service := by
        rw [renewalBankHeadStamp]
        exact hactive
      exact renewalBankOldPayloadNoHit m o K _ ho hhead
  | entrancePayload =>
      simp [renewalBankPayloadReached, renewalBankEntrancePayload]
  | entranceHead =>
      simp [renewalBankPayloadReached, renewalBankHead,
        renewalBankEntrancePayload]

/-- The only current-service origin in a controller shape is
the literal pending-RL acceptance output with heads = 0.
Every returned or inherited origin has an OLD stamp. -/
private theorem renewalBankControllerShapeNoBirthHit {n : Nat}
    (m : RenewalBankMemory n) (e dest : Fin n)
    (o : RenewalBankOrigin n) (K : Nat)
    (ho : o.service = m.service) (hK : 0 < K)
    (he : renewalBankSiteStamp (m.sites e) ≤ m.service)
    (hd : renewalBankSiteStamp (m.sites dest) ≤ m.service)
    (c : RenewalBankController n)
    (hs : RenewalBankControllerShape m e dest c) :
    (match (generalizing := false) c with
     | .active p => renewalBankPayloadReached o K p
     | _ => false) = false := by
  have hsource :
      renewalBankControllerStamp (m.sites e).controller ≤ m.service :=
    Nat.le_trans (Nat.le_max_right _ _) he
  have htarget :
      renewalBankControllerStamp (m.sites dest).controller ≤ m.service :=
    Nat.le_trans (Nat.le_max_right _ _) hd
  have hworker :
      renewalBankWorkerStamp (m.sites dest).worker ≤ m.service :=
    Nat.le_trans (Nat.le_max_left _ _) hd
  have hactive :
      renewalBankPayloadStamp
        (renewalBankActivePayload (m.sites e).controller e) ≤
        m.service :=
    Nat.le_trans
      (renewalBankActivePayloadStamp_le (m.sites e).controller e)
      hsource
  cases hs with
  | source =>
      exact renewalBankOldControllerNoHit m o K
        (m.sites e).controller ho hsource
  | target =>
      exact renewalBankOldControllerNoHit m o K
        (m.sites dest).controller ho htarget
  | cleared => rfl
  | waiting => rfl
  | fresh receipt atoms =>
      have hn : ¬ K ≤ 0 := by omega
      simp [renewalBankPayloadReached, hn]
  | returnedTarget atoms =>
      have hreturned :
          renewalBankPayloadStamp
            (renewalBankWorkerPayload (m.sites dest).worker dest) ≤
            m.service :=
        Nat.le_trans
          (renewalBankWorkerPayloadStamp_le
            (m.sites dest).worker dest) hworker
      have hupdated :
          renewalBankPayloadStamp
            { (renewalBankWorkerPayload (m.sites dest).worker dest)
                with atoms := atoms } ≤ m.service := hreturned
      exact renewalBankOldPayloadNoHit m o K _ ho hupdated
  | returnedEmpty atoms =>
      simp [renewalBankPayloadReached, renewalBankEntrancePayload]
  | sourceHead =>
      have hhead :
          renewalBankPayloadStamp
            (renewalBankHead
              (renewalBankActivePayload (m.sites e).controller e)) ≤
            m.service := by
        rw [renewalBankHeadStamp]
        exact hactive
      exact renewalBankOldPayloadNoHit m o K _ ho hhead
  | entranceHead =>
      simp [renewalBankPayloadReached, renewalBankHead,
        renewalBankEntrancePayload]

private theorem renewalBankShapedSiteNoBirthHit {n : Nat}
    (m : RenewalBankMemory n) (e dest : Fin n)
    (o : RenewalBankOrigin n) (K : Nat)
    (ho : o.service = m.service) (hK : 0 < K)
    (he : renewalBankSiteStamp (m.sites e) ≤ m.service)
    (hd : renewalBankSiteStamp (m.sites dest) ≤ m.service)
    (site : RenewalBankSite n)
    (hs : RenewalBankSiteShape m e dest site) :
    renewalBankSiteReached o K site = false := by
  unfold renewalBankSiteReached
  rw [renewalBankWorkerShapeNoBirthHit m e dest o K ho he hd
      site.worker hs.1,
    renewalBankControllerShapeNoBirthHit m e dest o K ho hK he hd
      site.controller hs.2]
  rfl

/-- All sites in the post-service BANK memory exclude a K-headed
origin whose service ID is the service being performed. This
includes source/destination aliasing and every framed site. -/
private theorem renewalBankAfterServiceNoBirthHit {n : Nat}
    (ring : DirectedRing n) (r : RenewalBankReference n)
    (hv : RenewalBankValid r) (e i : Fin n)
    (o : RenewalBankOrigin n) (K : Nat)
    (ho : o.service = r.2.service) (hK : 0 < K) :
    renewalBankSiteReached o K
      ((renewalBankNext ring r e).2.sites i) = false := by
  have he := hv e
  have hd := hv (ring.rightNeighbor e)
  have hpair := renewalBankPairShape
    (compileAdvice (ceilLogTwo n)) r.2 e (ring.rightNeighbor e)
    (r.1 e) (r.1 (ring.rightNeighbor e))
  change renewalBankSiteReached o K
    (if i = e then
      (renewalBankPairMemory (compileAdvice (ceilLogTwo n))
        r.2 e (ring.rightNeighbor e)
        (r.1 e) (r.1 (ring.rightNeighbor e))).1
     else if i = ring.rightNeighbor e then
      (renewalBankPairMemory (compileAdvice (ceilLogTwo n))
        r.2 e (ring.rightNeighbor e)
        (r.1 e) (r.1 (ring.rightNeighbor e))).2
     else r.2.sites i) = false
  split
  · exact renewalBankShapedSiteNoBirthHit r.2 e
      (ring.rightNeighbor e) o K ho hK he hd _ hpair.1
  · split
    · exact renewalBankShapedSiteNoBirthHit r.2 e
        (ring.rightNeighbor e) o K ho hK he hd _ hpair.2
    · exact renewalBankOldSiteNoHit r.2 o K (r.2.sites i) ho (hv i)

private theorem renewalBankBirthService {n : Nat}
    (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (m : RenewalBankMemory n)
    (e : Fin n) (o : RenewalBankOrigin n)
    (hb : renewalBankBirth ring C m e = some o) :
    o.service = m.service := by
  unfold renewalBankBirth at hb
  split at hb
  · split at hb <;> cases hb <;> rfl
  · cases hb

private theorem renewalBankFalseOfFn (n : Nat) :
    (List.ofFn (fun _ : Fin n => false)).any (fun b => b) = false := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [List.ofFn_succ]
      simpa using ih

private theorem renewalBankReachedFalseOfSites {n : Nat}
    (m : RenewalBankMemory n) (o : RenewalBankOrigin n)
    (K : Nat)
    (h : ∀ i : Fin n,
      renewalBankSiteReached o K (m.sites i) = false) :
    renewalBankReached o K m = false := by
  unfold renewalBankReached
  have hf :
      (fun i : Fin n => renewalBankSiteReached o K (m.sites i)) =
        (fun _ : Fin n => false) := by
    funext i
    exact h i
  rw [hf]
  exact renewalBankFalseOfFn n

/-- BANK birth is zero-headed at the exact creating service,
on the valid genealogy subtype. No assumption on Stop is used
by the local invariant, but the interface retains Stop. -/
theorem renewalBankValidNoInstantBirth {n : Nat}
    (ring : DirectedRing n) :
    RenewalBankValidNoInstantBirth ring := by
  intro r _ e born hmem
  cases hb : renewalBankBirth ring r.val.1 r.val.2 e with
  | none =>
      simp [renewalBankSpawn, hb] at hmem
  | some o =>
      have hborn :
          born =
            { identity := o
              afterBirth := renewalBankNext ring r.val e } := by
        simpa [renewalBankSpawn, hb] using hmem
      subst born
      have ho : o.service = r.val.2.service :=
        renewalBankBirthService ring r.val.1 r.val.2 e o hb
      have hK : 0 < (compileAdvice (ceilLogTwo n)).K :=
        renewalBankThresholdPositive n
      apply renewalBankReachedFalseOfSites
      intro i
      exact renewalBankAfterServiceNoBirthHit ring r.val
        r.property e i o (compileAdvice (ceilLogTwo n)).K ho hK

/-- Horizon-zero consequence for the valid reference's Born API. -/
theorem renewalBankValidBirthEmptySuffix {n : Nat}
    (ring : DirectedRing n)
    (r : {r : RenewalBankReference n // RenewalBankValid r})
    (hnot : ¬ renewalBankStop ring r.val)
    (e : Fin n) (born : RenewalBankBorn n)
    (hmem : born ∈ renewalBankSpawn ring r.val e) :
    renewalBankWin ring born [] = false := by
  rw [renewalBankWinEmpty]
  exact renewalBankValidNoInstantBirth ring r hnot e born hmem

/-- Any witness of the formerly identified reused-origin obstruction
belongs to the unrestricted Cartesian ghost class, not to Valid. -/
theorem renewalBankReusedOriginInvalid {n : Nat}
    (ring : DirectedRing n)
    (r : RenewalBankReference n) (e : Fin n)
    (born : RenewalBankBorn n)
    (hnot : ¬ renewalBankStop ring r)
    (hmem : born ∈ renewalBankSpawn ring r e)
    (hreach : renewalBankReached born.identity
      (compileAdvice (ceilLogTwo n)).K born.afterBirth.2 = true) :
    ¬ RenewalBankValid r := by
  intro hv
  have hfalse := renewalBankValidNoInstantBirth ring
    (⟨r, hv⟩ : {r : RenewalBankReference n // RenewalBankValid r})
    hnot e born hmem
  rw [hreach] at hfalse
  cases hfalse

end L3.HeadlineRenewal

/-!
Finite-word potential reduction.

The theorem renewalPotentialWordBound proves the finite-horizon first-hit
inequality from an integer one-step supermartingale. It does NOT assume
that the potential survives after the winning event: the induction
stops the first-hit computation at any already-winning state.

A new origin's service is strictly older than every suffix state.
This prevents the tracked identity from being freshly allocated again.
The proposed BANK potential sums the capped powers of *all* instances
of that origin, rather than silently assuming a unique instance in an
arbitrary valid Cartesian reference state.

The concrete BANK one-service drift and exact birth mass remain open.
No unconditional ReferenceOriginRarity is asserted here.
-/

namespace L3.HeadlineRenewal

open Classical
open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree

set_option autoImplicit false
set_option Elab.async false

/-- The same current-or-later Boolean recursion as renewalBankWinWord. -/
def renewalPotentialWordWin {S : Type} {n : Nat}
    (next : S → Fin n → S) (win : S → Bool) :
    List (Fin n) → S → Bool
  | [], s => win s
  | e :: word, s =>
      win s || renewalPotentialWordWin next win word (next s e)

private theorem renewalPotentialWordsConstant (n T : Nat) :
    Prob.scheduleSum n T (fun _ => 1) = n ^ T := by
  change FixedSpanRenewalPayload.wordSum n T (fun _ => 1) = n ^ T
  rw [← FixedSpanRenewalPayload.rawWord_sum n T (fun _ => 1)]
  simpa only [Nat.mul_one] using ofFn_sum_const (n ^ T) 1

/-- Finite-word first-hit supermartingale inequality. The conclusion
does not require the potential to remain high after a previous hit.
This is the direct finite-word (no stopping-time API) version of the
per-origin conditional upper bound. -/
theorem renewalPotentialWordBound {S : Type} {n : Nat}
    (next : S → Fin n → S) (win : S → Bool)
    (weight : S → Nat) (den : Nat)
    (hstep : ∀ s,
      (List.ofFn (fun e : Fin n => weight (next s e))).sum ≤
        n * weight s)
    (hwin : ∀ s, den * Prob.indicator (win s) ≤ weight s) :
    ∀ s T,
      den * Prob.scheduleSum n T
        (fun word => Prob.indicator
          (renewalPotentialWordWin next win word s)) ≤
      weight s * n ^ T := by
  intro s T
  induction T generalizing s with
  | zero =>
      simpa [Prob.scheduleSum, FixedSpanRenewalPayload.wordSum,
        allSchedules, renewalPotentialWordWin] using hwin s
  | succ T ih =>
      cases hw : win s with
      | true =>
          have hf :
              (fun word : List (Fin n) =>
                Prob.indicator
                  (renewalPotentialWordWin next win word s)) =
              (fun _ => 1) := by
            funext word
            cases word with
            | nil =>
                simp [renewalPotentialWordWin, hw, Prob.indicator]
            | cons e word =>
                simp [renewalPotentialWordWin, hw, Prob.indicator]
          have hd : den ≤ weight s := by
            have h := hwin s
            simpa [Prob.indicator, hw] using h
          rw [hf, renewalPotentialWordsConstant]
          exact Nat.mul_le_mul_right (n ^ (T + 1)) hd
      | false =>
          have hrec :
              Prob.scheduleSum n (T + 1)
                (fun word => Prob.indicator
                  (renewalPotentialWordWin next win word s)) =
              (List.ofFn (fun e : Fin n =>
                Prob.scheduleSum n T
                  (fun word => Prob.indicator
                    (renewalPotentialWordWin next win word
                      (next s e))))).sum := by
            change FixedSpanRenewalPayload.wordSum n (T + 1) _ = _
            rw [FixedSpanRenewalPayload.wordSum_succ]
            simp [renewalPotentialWordWin, hw]
          have hrow (e : Fin n) :
              den * Prob.scheduleSum n T
                (fun word => Prob.indicator
                  (renewalPotentialWordWin next win word
                    (next s e))) ≤
              n ^ T * weight (next s e) := by
            have h := ih (next s e)
            simpa only [Nat.mul_comm (weight (next s e)) (n ^ T)]
              using h
          have hsum := ofFn_sum_le
            (fun e : Fin n =>
              den * Prob.scheduleSum n T
                (fun word => Prob.indicator
                  (renewalPotentialWordWin next win word
                    (next s e))))
            (fun e : Fin n => n ^ T * weight (next s e))
            hrow
          rw [ofFn_sum_mul_left, ofFn_sum_mul_left] at hsum
          rw [hrec]
          calc
            den * (List.ofFn (fun e : Fin n =>
              Prob.scheduleSum n T
                (fun word => Prob.indicator
                  (renewalPotentialWordWin next win word
                    (next s e))))).sum ≤
                n ^ T *
                  (List.ofFn (fun e : Fin n =>
                    weight (next s e))).sum := hsum
            _ ≤ n ^ T * (n * weight s) :=
                Nat.mul_le_mul_left (n ^ T) (hstep s)
            _ = weight s * n ^ (T + 1) := by
                rw [Nat.pow_succ]
                ac_rfl

/-- Every future state of a tracked completed origin has a strictly
greater BANK service counter than the origin's allocation service. -/
def RenewalBankFuture {n : Nat} (o : RenewalBankOrigin n) : Type :=
  {r : RenewalBankReference n // o.service < r.2.service}

def renewalBankFutureNext {n : Nat}
    (ring : DirectedRing n) (o : RenewalBankOrigin n)
    (r : RenewalBankFuture o) (e : Fin n) :
    RenewalBankFuture o := by
  refine ⟨renewalBankNext ring r.val e, ?_⟩
  change o.service < r.val.2.service + 1
  exact Nat.lt_succ_of_lt r.property

theorem renewalBankBirthFuture {n : Nat}
    (ring : DirectedRing n) (r : RenewalBankReference n)
    (e : Fin n) (born : RenewalBankBorn n)
    (hmem : born ∈ renewalBankSpawn ring r e) :
    born.identity.service < born.afterBirth.2.service := by
  cases hb : renewalBankBirth ring r.1 r.2 e with
  | none =>
      simp [renewalBankSpawn, hb] at hmem
  | some o =>
      have hborn :
          born =
            { identity := o
              afterBirth := renewalBankNext ring r e } := by
        simpa [renewalBankSpawn, hb] using hmem
      subst born
      have hs := renewalBankBirthService ring r.1 r.2 e o hb
      change o.service < r.2.service + 1
      omega

/-- A tracked origin cannot be allocated a second time on its suffix:
new allocations carry the *current* service number. -/
theorem renewalBankFutureNoRebirth {n : Nat}
    (ring : DirectedRing n) (o : RenewalBankOrigin n)
    (r : RenewalBankFuture o) (e : Fin n) :
    renewalBankBirth ring r.val.1 r.val.2 e ≠ some o := by
  intro hb
  have hs := renewalBankBirthService ring r.val.1 r.val.2 e o hb
  have ha := r.property
  omega

/-- The age-restricted process has exactly the original BANK winning
event, including a hit at time zero. -/
theorem renewalBankFutureWinEq {n : Nat}
    (ring : DirectedRing n) (o : RenewalBankOrigin n) (K : Nat) :
    ∀ (word : List (Fin n)) (r : RenewalBankFuture o),
      renewalPotentialWordWin
        (renewalBankFutureNext ring o)
        (fun s : RenewalBankFuture o =>
          renewalBankReached o K s.val.2)
        word r =
      renewalBankWinWord ring o K word r.val := by
  intro word
  induction word with
  | nil =>
      intro r
      rfl
  | cons e word ih =>
      intro r
      change (renewalBankReached o K r.val.2 ||
          renewalPotentialWordWin
            (renewalBankFutureNext ring o)
            (fun s : RenewalBankFuture o =>
              renewalBankReached o K s.val.2)
            word (renewalBankFutureNext ring o r e)) =
        (renewalBankReached o K r.val.2 ||
          renewalBankWinWord ring o K word
            (renewalBankNext ring r.val e))
      exact congrArg
        (fun b : Bool => renewalBankReached o K r.val.2 || b)
        (ih (renewalBankFutureNext ring o r e))

/-- Capped power weight for one occurrence, including arbitrary
well-stamped ghosts that might contain duplicate old occurrences. -/
def renewalBankPayloadWeight {n : Nat}
    (o : RenewalBankOrigin n) (K : Nat)
    (p : RenewalBankPayload n) : Nat :=
  if p.origin = some o then 2 ^ (Nat.min K p.heads) else 0

def renewalBankWorkerWeight {n : Nat}
    (o : RenewalBankOrigin n) (K : Nat) :
    RenewalBankWorker n → Nat
  | .payload p => renewalBankPayloadWeight o K p
  | _ => 0

def renewalBankControllerWeight {n : Nat}
    (o : RenewalBankOrigin n) (K : Nat) :
    RenewalBankController n → Nat
  | .active p => renewalBankPayloadWeight o K p
  | _ => 0

def renewalBankSiteWeight {n : Nat}
    (o : RenewalBankOrigin n) (K : Nat)
    (s : RenewalBankSite n) : Nat :=
  renewalBankWorkerWeight o K s.worker +
    renewalBankControllerWeight o K s.controller

def renewalBankOriginPotential {n : Nat}
    (o : RenewalBankOrigin n) (K : Nat)
    (m : RenewalBankMemory n) : Nat :=
  (List.ofFn (fun i : Fin n =>
    renewalBankSiteWeight o K (m.sites i))).sum

/-- Literal fresh BANK payload has one unit of potential. Showing that
there are no *other* instances in the birth snapshot is separate. -/
theorem renewalBankFreshPayloadWeight {n : Nat}
    (o : RenewalBankOrigin n) (K : Nat)
    (atoms : List (RenewalBankAtom n)) :
    renewalBankPayloadWeight o K
      { atoms := atoms, origin := some o, heads := 0 } = 1 := by
  simp [renewalBankPayloadWeight]

/-- Exact F.2 reduction. This is deliberately conditional: it does not
infer a BANK drift inequality merely from the stamp invariant.
The three concrete premises are (a) one-service expected potential
nonincrease, (b) threshold domination, (c) total newborn potential
at most one. The age subtype removes all same-ID future births. -/
theorem renewalBankValidRarityOfPotential {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (weight : (o : RenewalBankOrigin n) → RenewalBankFuture o → Nat)
    (hstep : ∀ (o : RenewalBankOrigin n) (r : RenewalBankFuture o),
      (List.ofFn (fun e : Fin n =>
        weight o (renewalBankFutureNext ring o r e))).sum ≤
        n * weight o r)
    (hwin : ∀ (o : RenewalBankOrigin n) (r : RenewalBankFuture o),
      2 ^ (2 * ceilLogTwo n +
        (compileAdvice (ceilLogTwo n)).kappa) *
        Prob.indicator (renewalBankReached o
          (compileAdvice (ceilLogTwo n)).K r.val.2) ≤
        weight o r)
    (hbirth :
      ∀ (r : {r : RenewalBankReference n // RenewalBankValid r})
        (e : Fin n) (born : RenewalBankBorn n)
        (hmem : born ∈ renewalBankSpawn ring r.val e),
        weight born.identity
          ⟨born.afterBirth,
            renewalBankBirthFuture ring r.val e born hmem⟩ ≤ 1) :
    ReferenceOriginRarity ring
      (bankValidRootedReferenceData ring hbank)
      (compileAdvice (ceilLogTwo n)).kappa := by
  intro r _ e born hmem T
  have hfut := renewalBankBirthFuture ring r.val e born hmem
  have hmass :=
    renewalPotentialWordBound
      (renewalBankFutureNext ring born.identity)
      (fun s : RenewalBankFuture born.identity =>
        renewalBankReached born.identity
          (compileAdvice (ceilLogTwo n)).K s.val.2)
      (weight born.identity)
      (2 ^ (2 * ceilLogTwo n +
        (compileAdvice (ceilLogTwo n)).kappa))
      (hstep born.identity) (hwin born.identity)
      ⟨born.afterBirth, hfut⟩ T
  have heq :
      (fun word : List (Fin n) =>
        Prob.indicator
          (renewalPotentialWordWin
            (renewalBankFutureNext ring born.identity)
            (fun s : RenewalBankFuture born.identity =>
              renewalBankReached born.identity
                (compileAdvice (ceilLogTwo n)).K s.val.2)
            word ⟨born.afterBirth, hfut⟩)) =
      (fun word : List (Fin n) =>
        Prob.indicator (renewalBankWin ring born word)) := by
    funext word
    exact congrArg Prob.indicator
      (renewalBankFutureWinEq ring born.identity
        (compileAdvice (ceilLogTwo n)).K word ⟨born.afterBirth, hfut⟩)
  rw [heq] at hmass
  have hb : weight born.identity ⟨born.afterBirth, hfut⟩ ≤ 1 :=
    hbirth r e born hmem
  have htotal := Nat.le_trans hmass
    (Nat.mul_le_mul_right (n ^ T) hb)
  exact htotal

end L3.HeadlineRenewal


/-!
F.2 discharge.

The threshold premise is proved for all memories, with no validity
hypothesis. The stamp premise excludes a newly allocated origin from
all pre-birth worker/controller payloads, and hence from every
non-endpoint site in its one-service successor.

The remaining pair-endpoint mass bound and the averaged one-service
drift are NOT stated as theorems here.
-/

namespace L3.HeadlineRenewal

open Classical
open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree

set_option autoImplicit false
set_option Elab.async false

/-- A Boolean union can be charged by the sum of its indicators. -/
private theorem renewalBankIndicatorOrBound
    (a b : Bool) (den : Nat) :
    den * Prob.indicator (a || b) ≤
      den * Prob.indicator a + den * Prob.indicator b := by
  cases a <;> cases b <;> simp [Prob.indicator] <;> omega

/-- One matching payload above the threshold carries its full capped
weight, and all other payloads satisfy the bound vacuously. -/
private theorem renewalBankPayloadReachWeightBound {n : Nat}
    (o : RenewalBankOrigin n) (K : Nat)
    (p : RenewalBankPayload n) :
    2 ^ K * Prob.indicator (renewalBankPayloadReached o K p) ≤
      renewalBankPayloadWeight o K p := by
  by_cases hmatch : p.origin = some o
  · by_cases hcap : K ≤ p.heads
    · have hmin : Nat.min K p.heads = K := Nat.min_eq_left hcap
      simp [renewalBankPayloadReached, renewalBankPayloadWeight,
        Prob.indicator, hmatch, hcap, hmin]
    · simp [renewalBankPayloadReached, renewalBankPayloadWeight,
        Prob.indicator, hmatch, hcap]
  · simp [renewalBankPayloadReached, renewalBankPayloadWeight,
      Prob.indicator, hmatch]

private theorem renewalBankWorkerReachWeightBound {n : Nat}
    (o : RenewalBankOrigin n) (K : Nat)
    (w : RenewalBankWorker n) :
    2 ^ K * Prob.indicator
        (match w with
         | .payload p => renewalBankPayloadReached o K p
         | _ => false) ≤
      renewalBankWorkerWeight o K w := by
  cases w with
  | empty => simp [renewalBankWorkerWeight, Prob.indicator]
  | pending receipt => simp [renewalBankWorkerWeight, Prob.indicator]
  | payload p => exact renewalBankPayloadReachWeightBound o K p

private theorem renewalBankControllerReachWeightBound {n : Nat}
    (o : RenewalBankOrigin n) (K : Nat)
    (c : RenewalBankController n) :
    2 ^ K * Prob.indicator
        (match c with
         | .active p => renewalBankPayloadReached o K p
         | _ => false) ≤
      renewalBankControllerWeight o K c := by
  cases c with
  | empty => simp [renewalBankControllerWeight, Prob.indicator]
  | waiting atoms => simp [renewalBankControllerWeight, Prob.indicator]
  | active p => exact renewalBankPayloadReachWeightBound o K p

/-- A single reached site is paid by its worker plus controller weight.
The two fields may both be occupied; no uniqueness premise is used. -/
private theorem renewalBankSiteReachWeightBound {n : Nat}
    (o : RenewalBankOrigin n) (K : Nat)
    (s : RenewalBankSite n) :
    2 ^ K * Prob.indicator (renewalBankSiteReached o K s) ≤
      renewalBankSiteWeight o K s := by
  change
    2 ^ K * Prob.indicator
      ((match s.worker with
        | .payload p => renewalBankPayloadReached o K p
        | _ => false) ||
       (match s.controller with
        | .active p => renewalBankPayloadReached o K p
        | _ => false)) ≤
      renewalBankWorkerWeight o K s.worker +
        renewalBankControllerWeight o K s.controller
  exact Nat.le_trans
    (renewalBankIndicatorOrBound
      (match s.worker with
       | .payload p => renewalBankPayloadReached o K p
       | _ => false)
      (match s.controller with
       | .active p => renewalBankPayloadReached o K p
       | _ => false) (2 ^ K))
    (Nat.add_le_add
      (renewalBankWorkerReachWeightBound o K s.worker)
      (renewalBankControllerReachWeightBound o K s.controller))

/-- Finite-list reduction of a Boolean OR event to a sum of
nonnegative coordinate weights, without selecting a witness index. -/
private theorem renewalBankOfFnAnyWeightBound {α : Type}
    (pred : α → Bool) (wt : α → Nat) (den : Nat)
    (h : ∀ x : α, den * Prob.indicator (pred x) ≤ wt x) :
    ∀ (m : Nat) (f : Fin m → α),
      den * Prob.indicator
        ((List.ofFn (fun i : Fin m => pred (f i))).any (fun b => b)) ≤
      (List.ofFn (fun i : Fin m => wt (f i))).sum := by
  intro m
  induction m with
  | zero =>
      intro f
      change den * Prob.indicator false ≤ 0
      simp [Prob.indicator]
  | succ m ih =>
      intro f
      have hevent :
          (List.ofFn (fun i : Fin (m + 1) => pred (f i))).any
              (fun b => b) =
            (pred (f 0) ||
              (List.ofFn (fun i : Fin m => pred (f i.succ))).any
                (fun b => b)) := by
        rw [List.ofFn_succ]
        rfl
      have hsum :
          (List.ofFn (fun i : Fin (m + 1) => wt (f i))).sum =
            wt (f 0) +
              (List.ofFn (fun i : Fin m => wt (f i.succ))).sum := by
        rw [List.ofFn_succ, List.sum_cons]
      rw [hevent, hsum]
      exact Nat.le_trans
        (renewalBankIndicatorOrBound
          (pred (f 0))
          ((List.ofFn (fun i : Fin m => pred (f i.succ))).any
            (fun b => b)) den)
        (Nat.add_le_add (h (f 0))
          (ih (fun i : Fin m => f i.succ)))

/-- F.2 threshold domination: ANY occurrence at K heads yields
2^K units in the total potential. No hypotheses on the memory are
required, including no uniqueness of the origin. -/
theorem renewalBankOriginPotentialReachedBound {n : Nat}
    (o : RenewalBankOrigin n) (K : Nat)
    (m : RenewalBankMemory n) :
    2 ^ K * Prob.indicator (renewalBankReached o K m) ≤
      renewalBankOriginPotential o K m := by
  change 2 ^ K * Prob.indicator
      ((List.ofFn (fun i : Fin n =>
        renewalBankSiteReached o K (m.sites i))).any (fun b => b)) ≤
    (List.ofFn (fun i : Fin n =>
      renewalBankSiteWeight o K (m.sites i))).sum
  exact renewalBankOfFnAnyWeightBound
    (fun s : RenewalBankSite n => renewalBankSiteReached o K s)
    (fun s : RenewalBankSite n => renewalBankSiteWeight o K s)
    (2 ^ K) (renewalBankSiteReachWeightBound o K) n m.sites

/-- Exact specialization of hwin to the installed F.2 threshold.
The equality K = 2*q + kappa is definitional in Compiled. -/
theorem renewalBankOriginPotentialHwin {n : Nat}
    (o : RenewalBankOrigin n) (r : RenewalBankFuture o) :
    2 ^ (2 * ceilLogTwo n +
        (compileAdvice (ceilLogTwo n)).kappa) *
      Prob.indicator (renewalBankReached o
        (compileAdvice (ceilLogTwo n)).K r.val.2) ≤
      renewalBankOriginPotential o
        (compileAdvice (ceilLogTwo n)).K r.val.2 := by
  change 2 ^ (compileAdvice (ceilLogTwo n)).K *
      Prob.indicator (renewalBankReached o
        (compileAdvice (ceilLogTwo n)).K r.val.2) ≤
      renewalBankOriginPotential o
        (compileAdvice (ceilLogTwo n)).K r.val.2
  exact renewalBankOriginPotentialReachedBound o
    (compileAdvice (ceilLogTwo n)).K r.val.2

/-- A pre-service stamped payload cannot carry an identity created
at or after that service. -/
private theorem renewalBankOldPayloadOriginAbsent {n : Nat}
    (p : RenewalBankPayload n) (o : RenewalBankOrigin n)
    (service : Nat)
    (hstamp : renewalBankPayloadStamp p ≤ service)
    (hservice : service ≤ o.service) :
    p.origin ≠ some o := by
  intro heq
  have hlate : o.service + 1 ≤ service := by
    simpa only [renewalBankPayloadStamp, heq] using hstamp
  omega

private theorem renewalBankOldWorkerWeightZero {n : Nat}
    (o : RenewalBankOrigin n) (K service : Nat)
    (w : RenewalBankWorker n)
    (hstamp : renewalBankWorkerStamp w ≤ service)
    (hservice : service ≤ o.service) :
    renewalBankWorkerWeight o K w = 0 := by
  cases w with
  | empty => rfl
  | pending receipt => rfl
  | payload p =>
      have hp : renewalBankPayloadStamp p ≤ service := hstamp
      have hneq := renewalBankOldPayloadOriginAbsent
        p o service hp hservice
      simp [renewalBankWorkerWeight, renewalBankPayloadWeight, hneq]

private theorem renewalBankOldControllerWeightZero {n : Nat}
    (o : RenewalBankOrigin n) (K service : Nat)
    (c : RenewalBankController n)
    (hstamp : renewalBankControllerStamp c ≤ service)
    (hservice : service ≤ o.service) :
    renewalBankControllerWeight o K c = 0 := by
  cases c with
  | empty => rfl
  | waiting atoms => rfl
  | active p =>
      have hp : renewalBankPayloadStamp p ≤ service := hstamp
      have hneq := renewalBankOldPayloadOriginAbsent
        p o service hp hservice
      simp [renewalBankControllerWeight, renewalBankPayloadWeight, hneq]

/-- Stamp exclusion applies separately to both old fields at a site. -/
theorem renewalBankOldSiteWeightZero {n : Nat}
    (o : RenewalBankOrigin n) (K service : Nat)
    (s : RenewalBankSite n)
    (hstamp : renewalBankSiteStamp s ≤ service)
    (hservice : service ≤ o.service) :
    renewalBankSiteWeight o K s = 0 := by
  have hw : renewalBankWorkerStamp s.worker ≤ service :=
    Nat.le_trans (Nat.le_max_left _ _) hstamp
  have hc : renewalBankControllerStamp s.controller ≤ service :=
    Nat.le_trans (Nat.le_max_right _ _) hstamp
  change renewalBankWorkerWeight o K s.worker +
    renewalBankControllerWeight o K s.controller = 0
  rw [renewalBankOldWorkerWeightZero o K service s.worker hw hservice,
    renewalBankOldControllerWeightZero o K service
      s.controller hc hservice]

/-- Every old site of a valid reference has zero potential for an
identity allocated at the current service. -/
theorem renewalBankValidNewOriginNoOldWeight {n : Nat}
    (r : {r : RenewalBankReference n // RenewalBankValid r})
    (o : RenewalBankOrigin n) (K : Nat)
    (ho : o.service = r.val.2.service) (i : Fin n) :
    renewalBankSiteWeight o K (r.val.2.sites i) = 0 := by
  exact renewalBankOldSiteWeightZero o K r.val.2.service
    (r.val.2.sites i) (r.property i) (by omega)

/-- The only constructor that can insert the newly created ID has
heads zero, so that individual controller contributes at most one. -/
private theorem renewalBankFreshControllerWeightLeOne {n : Nat}
    (o : RenewalBankOrigin n) (K service : Nat)
    (root : Fin n) (receipt : RenewalBankReceipt n)
    (atoms : List (RenewalBankAtom n)) :
    renewalBankControllerWeight o K
      (.active ⟨atoms, some ⟨service, root, receipt⟩, 0⟩) ≤ 1 := by
  by_cases heq :
      (some (⟨service, root, receipt⟩ : RenewalBankOrigin n)) = some o
  · simp [renewalBankControllerWeight, renewalBankPayloadWeight, heq]
  · simp [renewalBankControllerWeight, renewalBankPayloadWeight, heq]

/-- At a valid birth, no unchanged non-endpoint site can hold the
newly stamped identity. This does not yet bound the two endpoint
projections of renewalBankPairMemory. -/
theorem renewalBankValidBirthAwayWeightZero {n : Nat}
    (ring : DirectedRing n)
    (r : {r : RenewalBankReference n // RenewalBankValid r})
    (e i : Fin n) (born : RenewalBankBorn n) (K : Nat)
    (hmem : born ∈ renewalBankSpawn ring r.val e)
    (hi : i ≠ e) (hj : i ≠ ring.rightNeighbor e) :
    renewalBankSiteWeight born.identity K
      (born.afterBirth.2.sites i) = 0 := by
  cases hb : renewalBankBirth ring r.val.1 r.val.2 e with
  | none =>
      simp [renewalBankSpawn, hb] at hmem
  | some o =>
      have hborn :
          born =
            { identity := o
              afterBirth := renewalBankNext ring r.val e } := by
        simpa [renewalBankSpawn, hb] using hmem
      subst born
      have ho : o.service = r.val.2.service :=
        renewalBankBirthService ring r.val.1 r.val.2 e o hb
      have hold :
          renewalBankSiteWeight o K (r.val.2.sites i) = 0 :=
        renewalBankValidNewOriginNoOldWeight r o K ho i
      change renewalBankSiteWeight o K
        (if i = e then
          (renewalBankPairMemory
            (compileAdvice (ceilLogTwo n)) r.val.2 e
            (ring.rightNeighbor e) (r.val.1 e)
            (r.val.1 (ring.rightNeighbor e))).1
         else if i = ring.rightNeighbor e then
          (renewalBankPairMemory
            (compileAdvice (ceilLogTwo n)) r.val.2 e
            (ring.rightNeighbor e) (r.val.1 e)
            (r.val.1 (ring.rightNeighbor e))).2
         else r.val.2.sites i) = 0
      rw [if_neg hi, if_neg hj]
      exact hold

/-- The head row never more than doubles the tracked capped weight.
This is the local numerical component of the still-open edge drift. -/
theorem renewalBankPayloadHeadWeightBound {n : Nat}
    (o : RenewalBankOrigin n) (K : Nat)
    (p : RenewalBankPayload n) :
    renewalBankPayloadWeight o K (renewalBankHead p) ≤
      2 * renewalBankPayloadWeight o K p := by
  have hpow :
      2 ^ min K (p.heads + 1) ≤
        2 * (2 ^ min K p.heads) := by
    by_cases hk : K ≤ p.heads
    · rw [Nat.min_eq_left hk,
        Nat.min_eq_left (by omega : K ≤ p.heads + 1)]
      have hpos := Nat.two_pow_pos K
      omega
    · have hlo : p.heads ≤ K := by omega
      have hhi : p.heads + 1 ≤ K := by omega
      rw [Nat.min_eq_right hlo, Nat.min_eq_right hhi,
        Nat.pow_succ]
      omega
  by_cases hmatch : p.origin = some o
  · simpa [renewalBankHead, renewalBankPayloadWeight, hmatch]
      using hpow
  · simp [renewalBankHead, renewalBankPayloadWeight, hmatch]

end L3.HeadlineRenewal


/-!
BANK origin-mass birth certificate and a
two-endpoint reduction of the remaining one-service drift.

The birth result uses the literal
pending-RL BANK row and the stamp invariant; it does not assume
that there is only one preexisting occurrence of a tracked origin.
The drift result below is conditional on one explicit two-endpoint
mass-and-ARMED-credit inequality. That local row theorem is NOT
claimed, so this section does not claim unconditional F.2 rarity.
-/

namespace L3.HeadlineRenewal

open Classical
open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree

set_option autoImplicit false
set_option Elab.async false

/-- Inverting the actual Counter diagnostic, not an assumed trace:
the only reset-return row has a role-zero, grant-free RWAIT source
and a role-one RL responder with unchanged PACK role. -/
private theorem renewalBankResetReturnFields
    (x y : BankCell) (postRole b : Nat)
    (hrow : Counter.resetRootRow x y postRole b =
      .resetReturn) :
    x.role = 0 ∧ x.grant = false ∧
      postRole = y.role ∧ postRole = 1 ∧
      x.mode = .RWAIT ∧ y.tok = .RL := by
  have hroot : x.role = 0 := by
    by_cases hx : x.role = 0
    · exact hx
    · have hbad :
          Counter.resetRootRow x y postRole b =
            .notRoot := by
        simp [Counter.resetRootRow, hx]
      rw [hbad] at hrow
      cases hrow
  have hgrant : x.grant = false := by
    cases hg : x.grant with
    | false => rfl
    | true =>
        have hbad :
            Counter.resetRootRow x y postRole b =
              .grantExit := by
          simp [Counter.resetRootRow, hroot, hg]
        rw [hbad] at hrow
        cases hrow
  have hsame : postRole = y.role := by
    by_cases hs : postRole = y.role
    · exact hs
    · have hbad :
          Counter.resetRootRow x y postRole b =
            .changedRole := by
        simp [Counter.resetRootRow, hroot, hgrant, hs]
      rw [hbad] at hrow
      cases hrow
  have hone : postRole = 1 := by
    by_cases hs : postRole = 1
    · exact hs
    · have hnotY : y.role ≠ 1 := by
        intro hy
        exact hs (hsame.trans hy)
      have hbad :
          Counter.resetRootRow x y postRole b =
            .wrongNeighbor := by
        simp [Counter.resetRootRow, hroot, hgrant,
          hsame, hnotY]
      rw [hbad] at hrow
      cases hrow
  have hother : y.tok = .RL ∧ x.mode = .RWAIT := by
    have hdestRole : y.role = 1 := hsame.symm.trans hone
    cases ht : y.tok <;> cases hm : x.mode <;>
      simp [Counter.resetRootRow, hroot, hgrant,
        hsame, hdestRole, ht, hm, isRetTok] at hrow ⊢
    all_goals (split at hrow <;> cases hrow)
  exact ⟨hroot, hgrant, hsame, hone,
    hother.2, hother.1⟩

/-- The reset-return branch flag follows from a genuine BANK birth.
The actual pending-receipt match is dealt with in the next lemma. -/
private theorem renewalBankBirthIsResetReturn {n : Nat}
    (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (m : RenewalBankMemory n) (e : Fin n)
    (o : RenewalBankOrigin n)
    (hbirth : renewalBankBirth ring C m e = some o) :
    Counter.resetRootRow
      (bankCell (C e) (C e).pack.val)
      (bankCell (C (ring.rightNeighbor e))
        (C (ring.rightNeighbor e)).pack.val)
      (packNext (C e).pack.val
        (C (ring.rightNeighbor e)).pack.val
        (compileAdvice (ceilLogTwo n)).b)
      (compileAdvice (ceilLogTwo n)).b =
        .resetReturn := by
  unfold renewalBankBirth at hbirth
  split at hbirth
  · assumption
  · cases hbirth

/-- A genuine new BANK identity is present in exactly the source
controller field of the resulting pair, with heads zero. The
responder worker and both other fields are empty. In particular
there is no second controller copy at the responder. -/
private theorem renewalBankBirthPairExact {n : Nat}
    (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (m : RenewalBankMemory n) (e : Fin n)
    (o : RenewalBankOrigin n)
    (hbirth : renewalBankBirth ring C m e = some o) :
    renewalBankPairMemory
      (compileAdvice (ceilLogTwo n)) m e
      (ring.rightNeighbor e)
      (C e) (C (ring.rightNeighbor e)) =
    (⟨.empty, .active
      ⟨renewalBankWaitingAtoms (m.sites e).controller,
        some o, 0⟩⟩,
     ⟨.empty, .empty⟩) := by
  have hreset := renewalBankBirthIsResetReturn
    ring C m e o hbirth
  obtain ⟨hrole, hgrant, hsame, hone, hmode, htok⟩ :=
    renewalBankResetReturnFields
      (bankCell (C e) (C e).pack.val)
      (bankCell (C (ring.rightNeighbor e))
        (C (ring.rightNeighbor e)).pack.val)
      (packNext (C e).pack.val
        (C (ring.rightNeighbor e)).pack.val
        (compileAdvice (ceilLogTwo n)).b)
      (compileAdvice (ceilLogTwo n)).b hreset
  have hwidth : 1 ≤ (compileAdvice (ceilLogTwo n)).b := by
    change 1 ≤ (compileAdvice (ceilLogTwo n)).s + 11
    omega
  have hdestRole :
      (bankCell (C (ring.rightNeighbor e))
        (C (ring.rightNeighbor e)).pack.val).role = 1 :=
    hsame.symm.trans hone
  cases hw : (m.sites (ring.rightNeighbor e)).worker with
  | empty =>
      simp [renewalBankBirth, hreset, hw] at hbirth
  | payload p =>
      simp [renewalBankBirth, hreset, hw] at hbirth
  | pending receipt =>
      have ho : o =
          { service := m.service, root := e,
            receipt := receipt } := by
        have hh := hbirth
        simp [renewalBankBirth, hreset, hw] at hh
        exact hh.symm
      subst o
      simp [renewalBankPairMemory, hrole, hgrant,
        hsame, hone, hdestRole, hmode, htok, hw, hwidth,
        isRetTok]

/-- The complete post-birth origin potential is a single spike of
height one, rather than just a bound on one fresh controller. The
valid stamp excludes all other sites; the exact pair row excludes
a duplicate at either serviced site. -/
theorem renewalBankOriginPotentialHbirth {n : Nat}
    (hn : 5 ≤ n) (ring : DirectedRing n)
    (r : {r : RenewalBankReference n // RenewalBankValid r})
    (e : Fin n) (born : RenewalBankBorn n)
    (hmem : born ∈ renewalBankSpawn ring r.val e) :
    renewalBankOriginPotential born.identity
      (compileAdvice (ceilLogTwo n)).K born.afterBirth.2 ≤ 1 := by
  cases hb : renewalBankBirth ring r.val.1 r.val.2 e with
  | none =>
      simp [renewalBankSpawn, hb] at hmem
  | some o =>
      have hborn :
          born =
            { identity := o
              afterBirth := renewalBankNext ring r.val e } := by
        simpa [renewalBankSpawn, hb] using hmem
      subst born
      have hp := renewalBankBirthPairExact
        ring r.val.1 r.val.2 e o hb
      have ho : o.service = r.val.2.service :=
        renewalBankBirthService ring r.val.1 r.val.2 e o hb
      have hne : ring.rightNeighbor e ≠ e :=
        EWord.rightNeighborDifferent ring (by omega : 2 ≤ n) e
      have hsite (i : Fin n) :
          renewalBankSiteWeight o
            (compileAdvice (ceilLogTwo n)).K
            ((renewalBankNext ring r.val e).2.sites i) =
            if i = e then 1 else 0 := by
        by_cases hi : i = e
        · subst i
          change renewalBankSiteWeight o
            (compileAdvice (ceilLogTwo n)).K
            (if e = e then
              (renewalBankPairMemory
                (compileAdvice (ceilLogTwo n)) r.val.2
                e (ring.rightNeighbor e)
                (r.val.1 e)
                (r.val.1 (ring.rightNeighbor e))).1
             else if e = ring.rightNeighbor e then
              (renewalBankPairMemory
                (compileAdvice (ceilLogTwo n)) r.val.2
                e (ring.rightNeighbor e)
                (r.val.1 e)
                (r.val.1 (ring.rightNeighbor e))).2
             else r.val.2.sites e) =
            (if e = e then 1 else 0)
          rw [if_pos rfl, hp]
          simp [renewalBankSiteWeight, renewalBankWorkerWeight,
            renewalBankControllerWeight, renewalBankPayloadWeight]
        · by_cases hj : i = ring.rightNeighbor e
          · subst i
            change renewalBankSiteWeight o
              (compileAdvice (ceilLogTwo n)).K
              (if ring.rightNeighbor e = e then
                (renewalBankPairMemory
                  (compileAdvice (ceilLogTwo n)) r.val.2
                  e (ring.rightNeighbor e)
                  (r.val.1 e)
                  (r.val.1 (ring.rightNeighbor e))).1
               else if ring.rightNeighbor e = ring.rightNeighbor e then
                (renewalBankPairMemory
                  (compileAdvice (ceilLogTwo n)) r.val.2
                  e (ring.rightNeighbor e)
                  (r.val.1 e)
                  (r.val.1 (ring.rightNeighbor e))).2
               else r.val.2.sites (ring.rightNeighbor e)) =
              (if ring.rightNeighbor e = e then 1 else 0)
            simp [hne, hp, renewalBankSiteWeight,
              renewalBankWorkerWeight, renewalBankControllerWeight]
          · have hold : renewalBankSiteWeight o
                (compileAdvice (ceilLogTwo n)).K
                (r.val.2.sites i) = 0 :=
              renewalBankValidNewOriginNoOldWeight r o
                (compileAdvice (ceilLogTwo n)).K ho i
            change renewalBankSiteWeight o
              (compileAdvice (ceilLogTwo n)).K
              (if i = e then
                (renewalBankPairMemory
                  (compileAdvice (ceilLogTwo n)) r.val.2
                  e (ring.rightNeighbor e)
                  (r.val.1 e)
                  (r.val.1 (ring.rightNeighbor e))).1
               else if i = ring.rightNeighbor e then
                (renewalBankPairMemory
                  (compileAdvice (ceilLogTwo n)) r.val.2
                  e (ring.rightNeighbor e)
                  (r.val.1 e)
                  (r.val.1 (ring.rightNeighbor e))).2
               else r.val.2.sites i) =
              (if i = e then 1 else 0)
            rw [if_neg hi, if_neg hj, if_neg hi]
            exact hold
      change
        (List.ofFn (fun i : Fin n =>
          renewalBankSiteWeight o
            (compileAdvice (ceilLogTwo n)).K
            ((renewalBankNext ring r.val e).2.sites i))).sum ≤ 1
      rw [ofFn_sum_eq
        (fun i : Fin n => renewalBankSiteWeight o
          (compileAdvice (ceilLogTwo n)).K
          ((renewalBankNext ring r.val e).2.sites i))
        (fun i : Fin n => if i = e then 1 else 0)
        hsite, renewalSpikeSum]
      exact Nat.le_refl 1

/-! ## Exact remaining local row inequality for hstep.

The ARMED source is allowed one extra copy of its OLD controller
weight (head increment). The incoming edge erases an ARMED
destination's OLD controller weight. The two credits cancel when
summed round the ring. The local inequality must account for
worker transfers and collisions without creating duplicate mass.
-/

def renewalBankArmedWeight {n : Nat}
    (o : RenewalBankOrigin n) (K : Nat)
    (r : RenewalBankReference n) (i : Fin n) : Nat :=
  if (bankCell (r.1 i) (r.1 i).pack.val).mode == .ARMED then
    renewalBankControllerWeight o K (r.2.sites i).controller
  else 0

/-- This local two-site inequality is the only new producer
required by the reduction below. It is deliberately a DEFINITION,
not a claimed theorem. -/
def RenewalBankPairMassDrift {n : Nat}
    (ring : DirectedRing n) (o : RenewalBankOrigin n)
    (K : Nat) (r : RenewalBankReference n) : Prop :=
  ∀ e : Fin n,
    renewalBankSiteWeight o K
        (renewalBankPairMemory
          (compileAdvice (ceilLogTwo n)) r.2 e
          (ring.rightNeighbor e)
          (r.1 e) (r.1 (ring.rightNeighbor e))).1 +
      renewalBankSiteWeight o K
        (renewalBankPairMemory
          (compileAdvice (ceilLogTwo n)) r.2 e
          (ring.rightNeighbor e)
          (r.1 e) (r.1 (ring.rightNeighbor e))).2 +
      renewalBankArmedWeight o K r (ring.rightNeighbor e) ≤
    renewalBankSiteWeight o K (r.2.sites e) +
      renewalBankSiteWeight o K
        (r.2.sites (ring.rightNeighbor e)) +
      renewalBankArmedWeight o K r e

/-- Cancellation without subtraction for one distinguished entry. -/
private theorem renewalBankBalanceOne {n : Nat}
    (f g : Fin n → Nat) (j : Fin n)
    (hother : ∀ i : Fin n, i ≠ j → f i = g i) :
    (List.ofFn f).sum + g j =
      (List.ofFn g).sum + f j := by
  induction n with
  | zero =>
      exact Fin.elim0 j
  | succ n ih =>
      rw [List.ofFn_succ, List.sum_cons,
        List.ofFn_succ, List.sum_cons]
      by_cases hjzero : j = 0
      · subst j
        have htail :
            (List.ofFn (fun i : Fin n => f i.succ)).sum =
              (List.ofFn (fun i : Fin n => g i.succ)).sum := by
          apply ofFn_sum_eq
          intro i
          apply hother i.succ
          intro hb
          have hv := congrArg Fin.val hb
          change i.val + 1 = 0 at hv
          omega
        rw [htail]
        omega
      · have hjpos : 0 < j.val := by
          have hne : j.val ≠ 0 := by
            intro hh
            apply hjzero
            exact Fin.ext hh
          omega
        have hjsucc :
            (⟨j.val - 1, by omega⟩ : Fin n).succ = j := by
          apply Fin.ext
          change j.val - 1 + 1 = j.val
          omega
        have hhead : f 0 = g 0 :=
          hother 0 (Ne.symm hjzero)
        have htail := ih
          (fun i : Fin n => f i.succ)
          (fun i : Fin n => g i.succ)
          (⟨j.val - 1, by omega⟩ : Fin n)
          (by
            intro i hij
            apply hother i.succ
            intro hb
            apply hij
            apply Fin.ext
            have hv := congrArg Fin.val hb
            change i.val + 1 = j.val at hv
            change i.val = j.val - 1
            omega)
        rw [hjsucc] at htail
        rw [hhead]
        omega

/-- Two distinguished entries, without a set-valued summation API
and without a potentially negative correction to the total sum. -/
private theorem renewalBankBalanceTwo {n : Nat}
    (f g : Fin n → Nat) (a b : Fin n)
    (hab : a ≠ b)
    (hother : ∀ i : Fin n,
      i ≠ a → i ≠ b → f i = g i) :
    (List.ofFn f).sum + g a + g b =
      (List.ofFn g).sum + f a + f b := by
  have ha :
      (List.ofFn
        (fun i : Fin n => if i = a then f i else g i)).sum +
          g a = (List.ofFn g).sum + f a := by
    have hh := renewalBankBalanceOne
      (fun i : Fin n => if i = a then f i else g i)
      g a (by
        intro i hia
        simp [hia])
    simpa using hh
  have hb :
      (List.ofFn f).sum + g b =
        (List.ofFn
          (fun i : Fin n => if i = a then f i else g i)).sum +
          f b := by
    have hh := renewalBankBalanceOne f
      (fun i : Fin n => if i = a then f i else g i)
      b (by
        intro i hib
        by_cases hia : i = a
        · subst i
          simp
        · simp [hia, hother i hia hib])
    simpa [Ne.symm hab] using hh
  omega

/-- Right-neighbor rotation permutes the directed-ring scheduler
edges, so the ARMED credit cancels in the full edge sum. -/
private theorem renewalBankRightNeighborSum {n : Nat}
    (ring : DirectedRing n) (f : Fin n → Nat) :
    (List.ofFn (fun e : Fin n =>
      f (ring.rightNeighbor e))).sum =
    (List.ofFn f).sum := by
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero
    (Nat.ne_of_gt ring.hn)
  subst n
  rw [show List.ofFn
      (fun e : Fin (k + 1) => f (ring.rightNeighbor e)) =
    (List.ofFn (fun i : Fin k =>
      f (ring.rightNeighbor i.castSucc))) ++
      [f (ring.rightNeighbor (Fin.last k))] from
    List.ofFn_succ_last]
  rw [List.sum_append, List.sum_cons, List.sum_nil,
    Nat.add_zero, List.ofFn_succ, List.sum_cons]
  have hlast : ring.rightNeighbor (Fin.last k) = 0 := by
    apply Fin.ext
    simp [DirectedRing.rightNeighbor]
  have hsucc : ∀ i : Fin k,
      ring.rightNeighbor i.castSucc = i.succ := by
    intro i
    apply Fin.ext
    simp [DirectedRing.rightNeighbor,
      Nat.mod_eq_of_lt (by omega : i.val + 1 < k + 1)]
  rw [hlast]
  have hf :
      (fun i : Fin k => f (ring.rightNeighbor i.castSucc)) =
        (fun i : Fin k => f i.succ) := by
    funext i
    rw [hsucc]
  rw [hf]
  omega

/-- The entire hstep now reduces to the literal BANK pair-row
mass inequality. This part is independent of validity; if the
row lemma proves true on unrestricted ghost references, no
additional uniqueness assumption is needed. -/
theorem renewalBankOriginPotentialHstepOfPairMassDrift
    {n : Nat} (hn : 5 ≤ n)
    (ring : DirectedRing n)
    (o : RenewalBankOrigin n) (K : Nat)
    (r : RenewalBankFuture o)
    (hpair : RenewalBankPairMassDrift ring o K r.val) :
    (List.ofFn (fun e : Fin n =>
      renewalBankOriginPotential o K
        (renewalBankFutureNext ring o r e).val.2)).sum ≤
    n * renewalBankOriginPotential o K r.val.2 := by
  have hne (e : Fin n) :
      ring.rightNeighbor e ≠ e :=
    EWord.rightNeighborDifferent ring (by omega : 2 ≤ n) e
  have hper (e : Fin n) :
      renewalBankOriginPotential o K
          (renewalBankFutureNext ring o r e).val.2 +
        renewalBankArmedWeight o K r.val
          (ring.rightNeighbor e) ≤
      renewalBankOriginPotential o K r.val.2 +
        renewalBankArmedWeight o K r.val e := by
    have hbalance := renewalBankBalanceTwo
      (fun i : Fin n =>
        renewalBankSiteWeight o K
          ((renewalBankFutureNext ring o r e).val.2.sites i))
      (fun i : Fin n =>
        renewalBankSiteWeight o K (r.val.2.sites i))
      e (ring.rightNeighbor e) (Ne.symm (hne e))
      (by
        intro i hi hj
        change renewalBankSiteWeight o K
          (if i = e then
            (renewalBankPairMemory
              (compileAdvice (ceilLogTwo n)) r.val.2
              e (ring.rightNeighbor e)
              (r.val.1 e) (r.val.1 (ring.rightNeighbor e))).1
           else if i = ring.rightNeighbor e then
            (renewalBankPairMemory
              (compileAdvice (ceilLogTwo n)) r.val.2
              e (ring.rightNeighbor e)
              (r.val.1 e) (r.val.1 (ring.rightNeighbor e))).2
           else r.val.2.sites i) =
          renewalBankSiteWeight o K (r.val.2.sites i)
        rw [if_neg hi, if_neg hj])
    have hsource :
        renewalBankSiteWeight o K
          ((renewalBankFutureNext ring o r e).val.2.sites e) =
        renewalBankSiteWeight o K
          (renewalBankPairMemory
            (compileAdvice (ceilLogTwo n)) r.val.2
            e (ring.rightNeighbor e)
            (r.val.1 e) (r.val.1 (ring.rightNeighbor e))).1 := by
      change renewalBankSiteWeight o K
        (if e = e then
          (renewalBankPairMemory
            (compileAdvice (ceilLogTwo n)) r.val.2
            e (ring.rightNeighbor e)
            (r.val.1 e) (r.val.1 (ring.rightNeighbor e))).1
         else if e = ring.rightNeighbor e then
          (renewalBankPairMemory
            (compileAdvice (ceilLogTwo n)) r.val.2
            e (ring.rightNeighbor e)
            (r.val.1 e) (r.val.1 (ring.rightNeighbor e))).2
         else r.val.2.sites e) =
        renewalBankSiteWeight o K
          (renewalBankPairMemory
            (compileAdvice (ceilLogTwo n)) r.val.2
            e (ring.rightNeighbor e)
            (r.val.1 e) (r.val.1 (ring.rightNeighbor e))).1
      rw [if_pos rfl]
    have hdest :
        renewalBankSiteWeight o K
          ((renewalBankFutureNext ring o r e).val.2.sites
            (ring.rightNeighbor e)) =
        renewalBankSiteWeight o K
          (renewalBankPairMemory
            (compileAdvice (ceilLogTwo n)) r.val.2
            e (ring.rightNeighbor e)
            (r.val.1 e) (r.val.1 (ring.rightNeighbor e))).2 := by
      change renewalBankSiteWeight o K
        (if ring.rightNeighbor e = e then
          (renewalBankPairMemory
            (compileAdvice (ceilLogTwo n)) r.val.2
            e (ring.rightNeighbor e)
            (r.val.1 e) (r.val.1 (ring.rightNeighbor e))).1
         else if ring.rightNeighbor e = ring.rightNeighbor e then
          (renewalBankPairMemory
            (compileAdvice (ceilLogTwo n)) r.val.2
            e (ring.rightNeighbor e)
            (r.val.1 e) (r.val.1 (ring.rightNeighbor e))).2
         else r.val.2.sites (ring.rightNeighbor e)) =
        renewalBankSiteWeight o K
          (renewalBankPairMemory
            (compileAdvice (ceilLogTwo n)) r.val.2
            e (ring.rightNeighbor e)
            (r.val.1 e) (r.val.1 (ring.rightNeighbor e))).2
      rw [if_neg (hne e), if_pos rfl]
    rw [hsource, hdest] at hbalance
    have hlocal := hpair e
    change
      renewalBankOriginPotential o K
          (renewalBankFutureNext ring o r e).val.2 +
        renewalBankSiteWeight o K (r.val.2.sites e) +
        renewalBankSiteWeight o K
          (r.val.2.sites (ring.rightNeighbor e)) =
      renewalBankOriginPotential o K r.val.2 +
        renewalBankSiteWeight o K
          (renewalBankPairMemory
            (compileAdvice (ceilLogTwo n)) r.val.2
            e (ring.rightNeighbor e)
            (r.val.1 e) (r.val.1 (ring.rightNeighbor e))).1 +
        renewalBankSiteWeight o K
          (renewalBankPairMemory
            (compileAdvice (ceilLogTwo n)) r.val.2
            e (ring.rightNeighbor e)
            (r.val.1 e) (r.val.1 (ring.rightNeighbor e))).2
      at hbalance
    omega
  have hsum := ofFn_sum_le
    (fun e : Fin n =>
      renewalBankOriginPotential o K
          (renewalBankFutureNext ring o r e).val.2 +
        renewalBankArmedWeight o K r.val (ring.rightNeighbor e))
    (fun e : Fin n =>
      renewalBankOriginPotential o K r.val.2 +
        renewalBankArmedWeight o K r.val e)
    hper
  rw [ofFn_sum_add, ofFn_sum_add,
    renewalBankRightNeighborSum ring
      (renewalBankArmedWeight o K r.val),
    ofFn_sum_const] at hsum
  omega

/-- The BANK hbirth producer and the previous hwin theorem reduce
F.2 origin rarity to a single still-unproved pair-row drift
property. No implicit global drift or uniqueness assumption
is introduced. -/
theorem renewalBankValidRarityOfOriginPotentialOfPairMassDrift
    {n : Nat} (hn : 5 ≤ n)
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hpair : ∀ (o : RenewalBankOrigin n)
      (r : RenewalBankFuture o),
      RenewalBankPairMassDrift ring o
        (compileAdvice (ceilLogTwo n)).K r.val) :
    ReferenceOriginRarity ring
      (bankValidRootedReferenceData ring hbank)
      (compileAdvice (ceilLogTwo n)).kappa := by
  apply renewalBankValidRarityOfPotential ring hbank
    (fun o r => renewalBankOriginPotential o
      (compileAdvice (ceilLogTwo n)).K r.val.2)
  · intro o r
    exact renewalBankOriginPotentialHstepOfPairMassDrift
      hn ring o (compileAdvice (ceilLogTwo n)).K r (hpair o r)
  · intro o r
    exact renewalBankOriginPotentialHwin o r
  · intro r e born hmem
    exact renewalBankOriginPotentialHbirth hn ring r e born hmem

/-! ## Source/return/credit inequalities for BANK row audit -/

/-- A nonactive controller yields an untracked entrance payload;
an active controller returns exactly its old payload. -/
theorem renewalBankActivePayloadWeightLe {n : Nat}
    (o : RenewalBankOrigin n) (K : Nat)
    (i : Fin n) (c : RenewalBankController n) :
    renewalBankPayloadWeight o K
        (renewalBankActivePayload c i) ≤
      renewalBankControllerWeight o K c := by
  cases c with
  | empty =>
      simp [renewalBankActivePayload, renewalBankEntrancePayload,
        renewalBankPayloadWeight, renewalBankControllerWeight]
  | waiting atoms =>
      simp [renewalBankActivePayload, renewalBankEntrancePayload,
        renewalBankPayloadWeight, renewalBankControllerWeight]
  | active p =>
      exact Nat.le_refl _

/-- Return merges atoms but retains the OLD worker's origin
and head count. There is no mass duplication at this assignment. -/
theorem renewalBankReturnedWeightLe {n : Nat}
    (o : RenewalBankOrigin n) (K : Nat)
    (i : Fin n) (c : RenewalBankController n)
    (w : RenewalBankWorker n) :
    renewalBankControllerWeight o K
      (.active (renewalBankReturned c w i)) ≤
      renewalBankWorkerWeight o K w := by
  cases w with
  | empty =>
      simp [renewalBankControllerWeight, renewalBankWorkerWeight,
        renewalBankReturned, renewalBankWorkerPayload,
        renewalBankEntrancePayload, renewalBankPayloadWeight]
  | pending receipt =>
      simp [renewalBankControllerWeight, renewalBankWorkerWeight,
        renewalBankReturned, renewalBankWorkerPayload,
        renewalBankEntrancePayload, renewalBankPayloadWeight]
  | payload p =>
      simp [renewalBankControllerWeight, renewalBankWorkerWeight,
        renewalBankReturned, renewalBankWorkerPayload,
        renewalBankPayloadWeight]
      exact Nat.le_refl _

/-- Head increments cost at most double the source controller
weight; the incoming-erasure credit is still to be verified
against the full BANK pair row. -/
theorem renewalBankActiveHeadWeightLe {n : Nat}
    (o : RenewalBankOrigin n) (K : Nat)
    (i : Fin n) (c : RenewalBankController n) :
    renewalBankPayloadWeight o K
        (renewalBankHead (renewalBankActivePayload c i)) ≤
      2 * renewalBankControllerWeight o K c := by
  calc
    renewalBankPayloadWeight o K
        (renewalBankHead (renewalBankActivePayload c i)) ≤
      2 * renewalBankPayloadWeight o K
        (renewalBankActivePayload c i) :=
      renewalBankPayloadHeadWeightBound o K
        (renewalBankActivePayload c i)
    _ ≤ 2 * renewalBankControllerWeight o K c :=
      Nat.mul_le_mul_left 2
        (renewalBankActivePayloadWeightLe o K i c)

/-- A wait tick leaves the controller untouched or erases it. -/
theorem renewalBankWaitSlotWeightLe {n : Nat}
    (o : RenewalBankOrigin n) (K : Nat)
    (mode : Mode) (lease : Nat)
    (c : RenewalBankController n) :
    renewalBankControllerWeight o K
        (renewalBankWaitSlot mode lease c) ≤
      renewalBankControllerWeight o K c := by
  unfold renewalBankWaitSlot
  split
  · split
    · exact Nat.le_refl _
    · exact Nat.zero_le _
  · exact Nat.le_refl _

/-- A fresh zero-head controller minted in a later service cannot
have the OLD origin's identity; it has strictly larger service. -/
theorem renewalBankLaterFreshWeightZero {n : Nat}
    (o : RenewalBankOrigin n) (K service : Nat)
    (root : Fin n) (receipt : RenewalBankReceipt n)
    (atoms : List (RenewalBankAtom n))
    (hfuture : o.service < service) :
    renewalBankControllerWeight o K
      (.active
        { atoms := atoms
          origin := some
            { service := service, root := root, receipt := receipt }
          heads := 0 }) = 0 := by
  have hdifferent :
      ({ service := service, root := root, receipt := receipt } :
        RenewalBankOrigin n) ≠ o := by
    intro he
    have hs := congrArg RenewalBankOrigin.service he
    dsimp at hs
    omega
  simp [renewalBankControllerWeight, renewalBankPayloadWeight,
    hdifferent]


end L3.HeadlineRenewal

/-!
Pointwise BANK pair mass audit.

The full RenewalBankPairMassDrift
for every physical pair remains open; the statements here verify
the critical ARMED-source and ARMED-destination rows, ordinary
worker moves/collisions, and the future-age reset-return row.
All use the literal renewalBankPairMemory and its actual priority.
No unrelated protocol step is introduced.
-/

namespace L3.HeadlineRenewal

open Classical
open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree

set_option autoImplicit false
set_option Elab.async false

/-- The root-ARMED accounting credit, independent of ring geometry.
This is exactly renewalBankArmedWeight on an actual endpoint. -/
def renewalBankArmedSiteCredit {n : Nat} {c : Compiled}
    (o : RenewalBankOrigin n) (K : Nat)
    (x : Agent c) (s : RenewalBankSite n) : Nat :=
  if x.mode == .ARMED then
    renewalBankControllerWeight o K s.controller
  else 0

/-- The exact two-site inequality before fixing a physical ring. -/
def RenewalBankPairLocalBound {n : Nat}
    (o : RenewalBankOrigin n) (K : Nat) (c : Compiled)
    (m : RenewalBankMemory n) (e dest : Fin n)
    (x y : Agent c) : Prop :=
  renewalBankSiteWeight o K
      (renewalBankPairMemory c m e dest x y).1 +
    renewalBankSiteWeight o K
      (renewalBankPairMemory c m e dest x y).2 +
    renewalBankArmedSiteCredit o K y (m.sites dest) ≤
  renewalBankSiteWeight o K (m.sites e) +
    renewalBankSiteWeight o K (m.sites dest) +
    renewalBankArmedSiteCredit o K x (m.sites e)

private theorem renewalBankSiteCreditLe {n : Nat} {c : Compiled}
    (o : RenewalBankOrigin n) (K : Nat)
    (x : Agent c) (s : RenewalBankSite n) :
    renewalBankArmedSiteCredit o K x s ≤
      renewalBankControllerWeight o K s.controller := by
  cases h : (x.mode == .ARMED) <;>
    simp [renewalBankArmedSiteCredit, h]

/-- A source worker moving to the destination overwrites the latter
worker and clears its own slot; even if both old slots were full,
this move cannot copy tracked origin mass. -/
theorem renewalBankWorkerMoveForwardMass {n : Nat}
    (o : RenewalBankOrigin n) (K : Nat)
    (a b : RenewalBankSite n) :
    renewalBankSiteWeight o K { a with worker := .empty } +
      renewalBankSiteWeight o K { b with worker := a.worker } ≤
    renewalBankSiteWeight o K a +
      renewalBankSiteWeight o K b := by
  simp only [renewalBankSiteWeight, renewalBankWorkerWeight]
  omega

/-- The reverse move, including RL, top RR and return tokens,
has the same nonduplication property. -/
theorem renewalBankWorkerMoveBackwardMass {n : Nat}
    (o : RenewalBankOrigin n) (K : Nat)
    (a b : RenewalBankSite n) :
    renewalBankSiteWeight o K { a with worker := b.worker } +
      renewalBankSiteWeight o K { b with worker := .empty } ≤
    renewalBankSiteWeight o K a +
      renewalBankSiteWeight o K b := by
  simp only [renewalBankSiteWeight, renewalBankWorkerWeight]
  omega

/-- Collision/overwrite that erases both workers is nonexpansive. -/
theorem renewalBankWorkerCollisionMass {n : Nat}
    (o : RenewalBankOrigin n) (K : Nat)
    (a b : RenewalBankSite n) :
    renewalBankSiteWeight o K { a with worker := .empty } +
      renewalBankSiteWeight o K { b with worker := .empty } ≤
    renewalBankSiteWeight o K a +
      renewalBankSiteWeight o K b := by
  simp only [renewalBankSiteWeight, renewalBankWorkerWeight]
  omega

/-- Consuming the target worker as a returned source controller
does not duplicate its origin; unrelated waiting atoms carry none. -/
theorem renewalBankWorkerReturnMass {n : Nat}
    (o : RenewalBankOrigin n) (K : Nat)
    (site : Fin n) (a b : RenewalBankSite n) :
    renewalBankSiteWeight o K
        { worker := .empty,
          controller := .active
            (renewalBankReturned a.controller b.worker site) } +
      renewalBankSiteWeight o K
        { worker := .empty, controller := .empty } ≤
    renewalBankSiteWeight o K a +
      renewalBankSiteWeight o K b := by
  have h := renewalBankReturnedWeightLe o K site
    a.controller b.worker
  simp only [renewalBankSiteWeight, renewalBankWorkerWeight,
    renewalBankControllerWeight] at *
  omega

/-- Exact ARMED root-to-role-one row, an empty responder token
and zero bit: the origin head increments at the root. Its old
worker is erased and the old responder worker is retained. -/
private theorem renewalBankArmedIdlePairExact {n : Nat}
    (c : Compiled) (m : RenewalBankMemory n)
    (e dest : Fin n) (x y : Agent c)
    (hb : 0 < c.b)
    (hx : x.pack.val = 0) (hy : y.pack.val = 1)
    (hg : x.grant = false)
    (hm : x.mode = .ARMED)
    (ht : y.tok = .E) (hbit : y.bit = false) :
    renewalBankPairMemory c m e dest x y =
      ({ worker := .empty,
         controller := .active
           (renewalBankHead
             (renewalBankActivePayload (m.sites e).controller e)) },
       { worker := (m.sites dest).worker, controller := .empty }) := by
  have hp : packNext x.pack.val y.pack.val c.b = 1 := by
    rw [hx]
    simp [packNext, hb]
  have hpzero : packNext 0 1 c.b = 1 := by
    simpa only [hx, hy] using hp
  have hbz : c.b ≠ 0 := Nat.pos_iff_ne_zero.mp hb
  simp [renewalBankPairMemory, bankCell, hx, hy, hg, hm,
    ht, hbit, hb, hbz, hpzero, isWaitMode, isRetTok]

/-- Exact ARMED root-to-role-one row with bit one: the incremented
head moves to the target worker and the source becomes waiting. -/
private theorem renewalBankArmedWorkPairExact {n : Nat}
    (c : Compiled) (m : RenewalBankMemory n)
    (e dest : Fin n) (x y : Agent c)
    (hb : 0 < c.b)
    (hx : x.pack.val = 0) (hy : y.pack.val = 1)
    (hg : x.grant = false)
    (hm : x.mode = .ARMED)
    (ht : y.tok = .E) (hbit : y.bit = true) :
    renewalBankPairMemory c m e dest x y =
      ({ worker := .empty, controller := .waiting [] },
       { worker := .payload
           (renewalBankHead
             (renewalBankActivePayload (m.sites e).controller e)),
         controller := .empty }) := by
  have hp : packNext x.pack.val y.pack.val c.b = 1 := by
    rw [hx]
    simp [packNext, hb]
  have hpzero : packNext 0 1 c.b = 1 := by
    simpa only [hx, hy] using hp
  have hbz : c.b ≠ 0 := Nat.pos_iff_ne_zero.mp hb
  simp [renewalBankPairMemory, bankCell, hx, hy, hg, hm,
    ht, hbit, hb, hbz, hpzero, isWaitMode, isRetTok]

/-- The two possible head updates are each paid by the source
ARMED controller credit. The destination ARMED credit is paid by
erasing its old controller on this unchanged role-one edge. -/
theorem renewalBankArmedHeadPairMass {n : Nat}
    (o : RenewalBankOrigin n) (K : Nat)
    (c : Compiled) (m : RenewalBankMemory n)
    (e dest : Fin n) (x y : Agent c)
    (hb : 0 < c.b)
    (hx : x.pack.val = 0) (hy : y.pack.val = 1)
    (hg : x.grant = false)
    (hm : x.mode = .ARMED)
    (ht : y.tok = .E) :
    RenewalBankPairLocalBound o K c m e dest x y := by
  have hhead := renewalBankActiveHeadWeightLe
    o K e (m.sites e).controller
  have htarget := renewalBankSiteCreditLe
    o K y (m.sites dest)
  have hsource :
      renewalBankArmedSiteCredit o K x (m.sites e) =
        renewalBankControllerWeight o K
          (m.sites e).controller := by
    simp [renewalBankArmedSiteCredit, hm]
  cases hbit : y.bit with
  | false =>
      have hp := renewalBankArmedIdlePairExact
        c m e dest x y hb hx hy hg hm ht hbit
      unfold RenewalBankPairLocalBound
      rw [hp, hsource]
      simp only [renewalBankSiteWeight, renewalBankWorkerWeight,
        renewalBankControllerWeight] at hhead htarget hsource ⊢
      omega
  | true =>
      have hp := renewalBankArmedWorkPairExact
        c m e dest x y hb hx hy hg hm ht hbit
      unfold RenewalBankPairLocalBound
      rw [hp, hsource]
      simp only [renewalBankSiteWeight, renewalBankWorkerWeight,
        renewalBankControllerWeight] at hhead htarget hsource ⊢
      omega

/-- On an incoming ARMED destination with old role zero, a source
in the spacer role b+1 cannot preserve any controller/worker.
The actual reference pair erases both sites. -/
private theorem renewalBankIncomingArmedPairExact {n : Nat}
    (c : Compiled) (m : RenewalBankMemory n)
    (e dest : Fin n) (x y : Agent c)
    (hx : x.pack.val = c.b + 1)
    (hy : y.pack.val = 0)
    (hm : y.mode = .ARMED) :
    renewalBankPairMemory c m e dest x y =
      ({ worker := .empty, controller := .empty },
       { worker := .empty, controller := .empty }) := by
  have hp : packNext x.pack.val y.pack.val c.b = 0 := by
    rw [hx]
    simp [packNext]
  have hpzero : packNext (c.b + 1) 0 c.b = 0 := by
    simpa only [hx, hy] using hp
  have hnotSourceZero : c.b + 1 ≠ 0 := by omega
  have hnotSourceInside : ¬ c.b + 1 ≤ c.b := by omega
  have hnotTop : c.b + 1 ≠ c.b := by omega
  simp [renewalBankPairMemory, bankCell, hx, hy, hm,
    hpzero, hnotSourceZero, hnotSourceInside, hnotTop,
    isWaitMode]

/-- The incoming ARMED erasure pays the full destination debit,
even if the old source and destination ghost records both have
tracked mass. It does not require a valid-stamp hypothesis. -/
theorem renewalBankIncomingArmedPairMass {n : Nat}
    (o : RenewalBankOrigin n) (K : Nat)
    (c : Compiled) (m : RenewalBankMemory n)
    (e dest : Fin n) (x y : Agent c)
    (hx : x.pack.val = c.b + 1)
    (hy : y.pack.val = 0)
    (hm : y.mode = .ARMED) :
    RenewalBankPairLocalBound o K c m e dest x y := by
  have hp := renewalBankIncomingArmedPairExact
    c m e dest x y hx hy hm
  have ht := renewalBankSiteCreditLe o K y (m.sites dest)
  unfold RenewalBankPairLocalBound
  rw [hp]
  simp only [renewalBankSiteWeight, renewalBankWorkerWeight,
    renewalBankControllerWeight] at ht ⊢
  omega

/-- The reset-return row uses the OLD target worker. A pending
receipt mints an origin at the present service; an ordinary worker
is consumed and promoted, never copied. -/
private theorem renewalBankResetReturnPairExactLocal {n : Nat}
    (c : Compiled) (m : RenewalBankMemory n)
    (e dest : Fin n) (x y : Agent c)
    (hb : 0 < c.b)
    (hx : x.pack.val = 0) (hy : y.pack.val = 1)
    (hg : x.grant = false)
    (hm : x.mode = .RWAIT)
    (ht : y.tok = .RL) :
    renewalBankPairMemory c m e dest x y =
      ({ worker := .empty,
         controller :=
           match (m.sites dest).worker with
           | .pending receipt =>
               .active
                 { atoms := renewalBankWaitingAtoms
                     (m.sites e).controller
                   origin := some
                     { service := m.service, root := e,
                       receipt := receipt }
                   heads := 0 }
           | w => .active
               (renewalBankReturned (m.sites e).controller w dest) },
       { worker := .empty, controller := .empty }) := by
  have hp : packNext x.pack.val y.pack.val c.b = 1 := by
    rw [hx]
    simp [packNext, hb]
  have hpzero : packNext 0 1 c.b = 1 := by
    simpa only [hx, hy] using hp
  have hbz : c.b ≠ 0 := Nat.pos_iff_ne_zero.mp hb
  cases hw : (m.sites dest).worker with
  | empty =>
      simp [renewalBankPairMemory, bankCell,
        hx, hy, hg, hm, ht, hb, hbz, hpzero, hw, isRetTok]
  | pending receipt =>
      simp [renewalBankPairMemory, bankCell,
        hx, hy, hg, hm, ht, hb, hbz, hpzero, hw, isRetTok]
  | payload p =>
      simp [renewalBankPairMemory, bankCell,
        hx, hy, hg, hm, ht, hb, hbz, hpzero, hw, isRetTok]

/-- A later reset return cannot mint the already tracked origin.
Every other return conserves weight by consuming the old worker. -/
private theorem renewalBankResetReturnControllerWeightLe {n : Nat}
    (o : RenewalBankOrigin n) (K : Nat)
    (m : RenewalBankMemory n) (e dest : Fin n)
    (hfuture : o.service < m.service) :
    renewalBankControllerWeight o K
      (match (m.sites dest).worker with
       | .pending receipt =>
           .active
             { atoms := renewalBankWaitingAtoms
                 (m.sites e).controller
               origin := some
                 { service := m.service, root := e,
                   receipt := receipt }
               heads := 0 }
       | w => .active
           (renewalBankReturned (m.sites e).controller w dest)) ≤
      renewalBankWorkerWeight o K (m.sites dest).worker := by
  cases hw : (m.sites dest).worker with
  | empty =>
      simp [renewalBankReturned, renewalBankWorkerPayload,
        renewalBankWorkerWeight, renewalBankControllerWeight,
        renewalBankPayloadWeight, renewalBankEntrancePayload]
  | pending receipt =>
      have hzero := renewalBankLaterFreshWeightZero o K
        m.service e receipt
        (renewalBankWaitingAtoms (m.sites e).controller) hfuture
      simpa only [hw, renewalBankWorkerWeight, hzero] using
        (Nat.le_refl 0)
  | payload p =>
      simpa only [hw] using
        renewalBankReturnedWeightLe o K dest
          (m.sites e).controller (.payload p)

/-- The strict-age future assumption is exactly what makes the
reset-return row nonexpansive. No uniqueness hypothesis is used. -/
theorem renewalBankResetReturnPairMass {n : Nat}
    (o : RenewalBankOrigin n) (K : Nat)
    (c : Compiled) (m : RenewalBankMemory n)
    (e dest : Fin n) (x y : Agent c)
    (hfuture : o.service < m.service)
    (hb : 0 < c.b)
    (hx : x.pack.val = 0) (hy : y.pack.val = 1)
    (hg : x.grant = false)
    (hm : x.mode = .RWAIT)
    (ht : y.tok = .RL) :
    RenewalBankPairLocalBound o K c m e dest x y := by
  have hp := renewalBankResetReturnPairExactLocal
    c m e dest x y hb hx hy hg hm ht
  have hnew := renewalBankResetReturnControllerWeightLe
    o K m e dest hfuture
  have hdest := renewalBankSiteCreditLe o K y (m.sites dest)
  have hsource :
      renewalBankArmedSiteCredit o K x (m.sites e) = 0 := by
    simp [renewalBankArmedSiteCredit, hm]
  unfold RenewalBankPairLocalBound
  rw [hp, hsource]
  simp only [renewalBankSiteWeight, renewalBankWorkerWeight,
    renewalBankControllerWeight] at hnew hdest ⊢
  omega

/-- Translate a checked pair row to one edge of the exact
RenewalBankPairMassDrift, without claiming all edges are checked. -/
theorem renewalBankPairLocalAtFuture {n : Nat}
    (ring : DirectedRing n) (o : RenewalBankOrigin n)
    (K : Nat) (r : RenewalBankFuture o) (e : Fin n)
    (hlocal : RenewalBankPairLocalBound o K
      (compileAdvice (ceilLogTwo n)) r.val.2
      e (ring.rightNeighbor e)
      (r.val.1 e) (r.val.1 (ring.rightNeighbor e))) :
    renewalBankSiteWeight o K
        (renewalBankPairMemory
          (compileAdvice (ceilLogTwo n)) r.val.2 e
          (ring.rightNeighbor e)
          (r.val.1 e) (r.val.1 (ring.rightNeighbor e))).1 +
      renewalBankSiteWeight o K
        (renewalBankPairMemory
          (compileAdvice (ceilLogTwo n)) r.val.2 e
          (ring.rightNeighbor e)
          (r.val.1 e) (r.val.1 (ring.rightNeighbor e))).2 +
      renewalBankArmedWeight o K r.val (ring.rightNeighbor e) ≤
    renewalBankSiteWeight o K (r.val.2.sites e) +
      renewalBankSiteWeight o K
        (r.val.2.sites (ring.rightNeighbor e)) +
      renewalBankArmedWeight o K r.val e := by
  exact hlocal

/-- The exact local-to-global interface, without changing the
existing rarity consumer or assuming that each row holds. -/
theorem renewalBankPairMassDriftOfLocalBounds {n : Nat}
    (ring : DirectedRing n) (o : RenewalBankOrigin n)
    (K : Nat) (r : RenewalBankFuture o)
    (hrows : ∀ e : Fin n,
      RenewalBankPairLocalBound o K
        (compileAdvice (ceilLogTwo n)) r.val.2
        e (ring.rightNeighbor e)
        (r.val.1 e) (r.val.1 (ring.rightNeighbor e))) :
    RenewalBankPairMassDrift ring o K r.val := by
  intro e
  exact renewalBankPairLocalAtFuture ring o K r e (hrows e)

end L3.HeadlineRenewal

/-!
Further exact BANK pair rows. This section intentionally makes no exhaustive drift claim.
-/

namespace L3.HeadlineRenewal

open Classical

set_option autoImplicit false
set_option Elab.async false

/-- An exact pair erasure pays the destination ARMED credit from its
old controller, regardless of both old worker records. -/
private theorem renewalBankErasedPairLocalMass {n : Nat}
    (o : RenewalBankOrigin n) (K : Nat)
    (c : Compiled) (m : RenewalBankMemory n)
    (e dest : Fin n) (x y : Agent c)
    (hpair : renewalBankPairMemory c m e dest x y =
      ({ worker := .empty, controller := .empty },
       { worker := .empty, controller := .empty })) :
    RenewalBankPairLocalBound o K c m e dest x y := by
  have htarget := renewalBankSiteCreditLe o K y (m.sites dest)
  unfold RenewalBankPairLocalBound
  rw [hpair]
  simp only [renewalBankSiteWeight, renewalBankWorkerWeight,
    renewalBankControllerWeight] at htarget ⊢
  omega

/-- Interior unchanged nonroot RR transports the source worker forward.
The strict upper bound keeps both roles below the top boundary. -/
private theorem renewalBankInteriorForwardPairExact {n : Nat}
    (c : Compiled) (m : RenewalBankMemory n)
    (e dest : Fin n) (x y : Agent c) (r : Nat)
    (hfirst : 1 ≤ r) (hnext : r + 1 < c.b)
    (hx : x.pack.val = r) (hy : y.pack.val = r + 1)
    (ht : x.tok = .RR) :
    renewalBankPairMemory c m e dest x y =
      ({ worker := .empty, controller := .empty },
       { worker := (m.sites e).worker, controller := .empty }) := by
  have hlt : r < c.b := by omega
  have hle : r ≤ c.b := by omega
  have hnextLe : r + 1 ≤ c.b := by omega
  have hnz : r ≠ 0 := by omega
  have htop : r ≠ c.b := by omega
  have hnextTop : r + 1 ≠ c.b := by omega
  have hp : packNext r (r + 1) c.b = r + 1 := by
    simp [packNext, hlt]
  simp [renewalBankPairMemory, bankCell, hx, hy, hp,
    ht, hfirst, hlt, hle, hnext, hnextLe, hnz, htop, hnextTop]

theorem renewalBankInteriorForwardPairMass {n : Nat}
    (o : RenewalBankOrigin n) (K : Nat)
    (c : Compiled) (m : RenewalBankMemory n)
    (e dest : Fin n) (x y : Agent c) (r : Nat)
    (hfirst : 1 ≤ r) (hnext : r + 1 < c.b)
    (hx : x.pack.val = r) (hy : y.pack.val = r + 1)
    (ht : x.tok = .RR) :
    RenewalBankPairLocalBound o K c m e dest x y := by
  have hpair := renewalBankInteriorForwardPairExact
    c m e dest x y r hfirst hnext hx hy ht
  have htarget := renewalBankSiteCreditLe o K y (m.sites dest)
  unfold RenewalBankPairLocalBound
  rw [hpair]
  simp only [renewalBankSiteWeight, renewalBankWorkerWeight,
    renewalBankControllerWeight] at htarget ⊢
  omega

/-- An interior RL responder transports its old worker backward, unless
source RR has already taken priority. -/
private theorem renewalBankInteriorBackwardPairExact {n : Nat}
    (c : Compiled) (m : RenewalBankMemory n)
    (e dest : Fin n) (x y : Agent c) (r : Nat)
    (hfirst : 1 ≤ r) (hnext : r + 1 < c.b)
    (hx : x.pack.val = r) (hy : y.pack.val = r + 1)
    (hnoRR : x.tok ≠ .RR) (ht : y.tok = .RL) :
    renewalBankPairMemory c m e dest x y =
      ({ worker := (m.sites dest).worker, controller := .empty },
       { worker := .empty, controller := .empty }) := by
  have hlt : r < c.b := by omega
  have hle : r ≤ c.b := by omega
  have hnextLe : r + 1 ≤ c.b := by omega
  have hnz : r ≠ 0 := by omega
  have htop : r ≠ c.b := by omega
  have hnextTop : r + 1 ≠ c.b := by omega
  have hp : packNext r (r + 1) c.b = r + 1 := by
    simp [packNext, hlt]
  simp [renewalBankPairMemory, bankCell, hx, hy, hp,
    hnoRR, ht, hfirst, hlt, hle, hnext, hnextLe,
    hnz, htop, hnextTop]

theorem renewalBankInteriorBackwardPairMass {n : Nat}
    (o : RenewalBankOrigin n) (K : Nat)
    (c : Compiled) (m : RenewalBankMemory n)
    (e dest : Fin n) (x y : Agent c) (r : Nat)
    (hfirst : 1 ≤ r) (hnext : r + 1 < c.b)
    (hx : x.pack.val = r) (hy : y.pack.val = r + 1)
    (hnoRR : x.tok ≠ .RR) (ht : y.tok = .RL) :
    RenewalBankPairLocalBound o K c m e dest x y := by
  have hpair := renewalBankInteriorBackwardPairExact
    c m e dest x y r hfirst hnext hx hy hnoRR ht
  have htarget := renewalBankSiteCreditLe o K y (m.sites dest)
  unfold RenewalBankPairLocalBound
  rw [hpair]
  simp only [renewalBankSiteWeight, renewalBankWorkerWeight,
    renewalBankControllerWeight] at htarget ⊢
  omega

/-- Two empty tokens in an unchanged interior nonroot pair leave both
old workers alone and sanitize both controllers. -/
private theorem renewalBankInteriorIdlePairExact {n : Nat}
    (c : Compiled) (m : RenewalBankMemory n)
    (e dest : Fin n) (x y : Agent c) (r : Nat)
    (hfirst : 1 ≤ r) (hnext : r + 1 < c.b)
    (hx : x.pack.val = r) (hy : y.pack.val = r + 1)
    (htx : x.tok = .E) (hty : y.tok = .E) :
    renewalBankPairMemory c m e dest x y =
      ({ worker := (m.sites e).worker, controller := .empty },
       { worker := (m.sites dest).worker, controller := .empty }) := by
  have hlt : r < c.b := by omega
  have hle : r ≤ c.b := by omega
  have hnextLe : r + 1 ≤ c.b := by omega
  have hnz : r ≠ 0 := by omega
  have htop : r ≠ c.b := by omega
  have hnextTop : r + 1 ≠ c.b := by omega
  have hp : packNext r (r + 1) c.b = r + 1 := by
    simp [packNext, hlt]
  simp [renewalBankPairMemory, bankCell, hx, hy, hp,
    htx, hty, hfirst, hlt, hle, hnext, hnextLe,
    hnz, htop, hnextTop]

theorem renewalBankInteriorIdlePairMass {n : Nat}
    (o : RenewalBankOrigin n) (K : Nat)
    (c : Compiled) (m : RenewalBankMemory n)
    (e dest : Fin n) (x y : Agent c) (r : Nat)
    (hfirst : 1 ≤ r) (hnext : r + 1 < c.b)
    (hx : x.pack.val = r) (hy : y.pack.val = r + 1)
    (htx : x.tok = .E) (hty : y.tok = .E) :
    RenewalBankPairLocalBound o K c m e dest x y := by
  have hpair := renewalBankInteriorIdlePairExact
    c m e dest x y r hfirst hnext hx hy htx hty
  have htarget := renewalBankSiteCreditLe o K y (m.sites dest)
  unfold RenewalBankPairLocalBound
  rw [hpair]
  simp only [renewalBankSiteWeight, renewalBankWorkerWeight,
    renewalBankControllerWeight] at htarget ⊢
  omega

/-- With both tokens occupied, and without a higher-priority RR or RL
transfer, the interior nonroot collision erases both workers. -/
private theorem renewalBankInteriorCollisionPairExact {n : Nat}
    (c : Compiled) (m : RenewalBankMemory n)
    (e dest : Fin n) (x y : Agent c) (r : Nat)
    (hfirst : 1 ≤ r) (hnext : r + 1 < c.b)
    (hx : x.pack.val = r) (hy : y.pack.val = r + 1)
    (hnoRR : x.tok ≠ .RR) (hnoRL : y.tok ≠ .RL)
    (hxBusy : x.tok ≠ .E) (hyBusy : y.tok ≠ .E) :
    renewalBankPairMemory c m e dest x y =
      ({ worker := .empty, controller := .empty },
       { worker := .empty, controller := .empty }) := by
  have hlt : r < c.b := by omega
  have hle : r ≤ c.b := by omega
  have hnextLe : r + 1 ≤ c.b := by omega
  have hnz : r ≠ 0 := by omega
  have htop : r ≠ c.b := by omega
  have hnextTop : r + 1 ≠ c.b := by omega
  have hp : packNext r (r + 1) c.b = r + 1 := by
    simp [packNext, hlt]
  simp [renewalBankPairMemory, bankCell, hx, hy, hp,
    hnoRR, hnoRL, hxBusy, hyBusy, hfirst, hlt, hle,
    hnext, hnextLe, hnz, htop, hnextTop]

theorem renewalBankInteriorCollisionPairMass {n : Nat}
    (o : RenewalBankOrigin n) (K : Nat)
    (c : Compiled) (m : RenewalBankMemory n)
    (e dest : Fin n) (x y : Agent c) (r : Nat)
    (hfirst : 1 ≤ r) (hnext : r + 1 < c.b)
    (hx : x.pack.val = r) (hy : y.pack.val = r + 1)
    (hnoRR : x.tok ≠ .RR) (hnoRL : y.tok ≠ .RL)
    (hxBusy : x.tok ≠ .E) (hyBusy : y.tok ≠ .E) :
    RenewalBankPairLocalBound o K c m e dest x y := by
  exact renewalBankErasedPairLocalMass o K c m e dest x y
    (renewalBankInteriorCollisionPairExact c m e dest x y
      r hfirst hnext hx hy hnoRR hnoRL hxBusy hyBusy)

/-- A changed responder role prevents the nonroot source from entering
any token branch; source worker is retained only if in worker range. -/
private theorem renewalBankChangedInsidePairExact {n : Nat}
    (c : Compiled) (m : RenewalBankMemory n)
    (e dest : Fin n) (x y : Agent c)
    (hnonroot : x.pack.val ≠ 0)
    (hfirst : 1 ≤ x.pack.val) (hupper : x.pack.val ≤ c.b)
    (hchanged : packNext x.pack.val y.pack.val c.b ≠ y.pack.val) :
    renewalBankPairMemory c m e dest x y =
      ({ worker := (m.sites e).worker, controller := .empty },
       { worker := .empty, controller := .empty }) ∨
    renewalBankPairMemory c m e dest x y =
      ({ worker := .empty, controller := .empty },
       { worker := .empty, controller := .empty }) := by
  simp [renewalBankPairMemory, bankCell, hnonroot,
    hfirst, hupper, hchanged]
  split <;> simp

private theorem renewalBankChangedOutsidePairExact {n : Nat}
    (c : Compiled) (m : RenewalBankMemory n)
    (e dest : Fin n) (x y : Agent c)
    (hnonroot : x.pack.val ≠ 0)
    (houtside : ¬ x.pack.val ≤ c.b)
    (hchanged : packNext x.pack.val y.pack.val c.b ≠ y.pack.val) :
    renewalBankPairMemory c m e dest x y =
      ({ worker := .empty, controller := .empty },
       { worker := .empty, controller := .empty }) := by
  simp [renewalBankPairMemory, bankCell, hnonroot,
    houtside, hchanged]

/-- Entire changed-role class with a nonzero source role: sanitation
erases destination mass and never duplicates source worker mass. -/
theorem renewalBankChangedNonrootPairMass {n : Nat}
    (o : RenewalBankOrigin n) (K : Nat)
    (c : Compiled) (m : RenewalBankMemory n)
    (e dest : Fin n) (x y : Agent c)
    (hnonroot : x.pack.val ≠ 0)
    (hchanged : packNext x.pack.val y.pack.val c.b ≠ y.pack.val) :
    RenewalBankPairLocalBound o K c m e dest x y := by
  by_cases hupper : x.pack.val ≤ c.b
  · have hfirst : 1 ≤ x.pack.val := by omega
    rcases renewalBankChangedInsidePairExact
      c m e dest x y hnonroot hfirst hupper hchanged with hpair | hpair
    · have htarget := renewalBankSiteCreditLe o K y (m.sites dest)
      unfold RenewalBankPairLocalBound
      rw [hpair]
      simp only [renewalBankSiteWeight, renewalBankWorkerWeight,
        renewalBankControllerWeight] at htarget ⊢
      omega
    · exact renewalBankErasedPairLocalMass o K c m e dest x y hpair
  · exact renewalBankErasedPairLocalMass o K c m e dest x y
      (renewalBankChangedOutsidePairExact c m e dest x y
        hnonroot hupper hchanged)

/-- A changed-role root selection with grant clears both local records. -/
private theorem renewalBankChangedRootGrantPairExact {n : Nat}
    (c : Compiled) (m : RenewalBankMemory n)
    (e dest : Fin n) (x y : Agent c)
    (hx : x.pack.val = 0) (hg : x.grant = true)
    (hchanged : packNext x.pack.val y.pack.val c.b ≠ y.pack.val) :
    renewalBankPairMemory c m e dest x y =
      ({ worker := .empty, controller := .empty },
       { worker := .empty, controller := .empty }) := by
  have hchangedZero : packNext 0 y.pack.val c.b ≠ y.pack.val := by
    simpa only [hx] using hchanged
  simp [renewalBankPairMemory, bankCell, hx, hg, hchangedZero]

/-- A changed-role root launch (ARMED or CSTART) is cancelled before
any new worker or head can be created. -/
private theorem renewalBankChangedRootLaunchPairExact {n : Nat}
    (c : Compiled) (m : RenewalBankMemory n)
    (e dest : Fin n) (x y : Agent c)
    (hx : x.pack.val = 0) (hg : x.grant = false)
    (hmode : x.mode = .ARMED ∨ x.mode = .CSTART)
    (hchanged : packNext x.pack.val y.pack.val c.b ≠ y.pack.val) :
    renewalBankPairMemory c m e dest x y =
      ({ worker := .empty, controller := .empty },
       { worker := .empty, controller := .empty }) := by
  have hchangedZero : packNext 0 y.pack.val c.b ≠ y.pack.val := by
    simpa only [hx] using hchanged
  cases hmode with
  | inl hm =>
      simp [renewalBankPairMemory, bankCell, hx, hg,
        hm, hchangedZero]
  | inr hm =>
      simp [renewalBankPairMemory, bankCell, hx, hg,
        hm, hchangedZero]

/-- For other non-grant root modes, a changed role ticks only the
source waiting slot and erases the entire old responder record. -/
private theorem renewalBankChangedRootWaitPairExact {n : Nat}
    (c : Compiled) (m : RenewalBankMemory n)
    (e dest : Fin n) (x y : Agent c)
    (hx : x.pack.val = 0) (hg : x.grant = false)
    (hna : x.mode ≠ .ARMED) (hnc : x.mode ≠ .CSTART)
    (hchanged : packNext x.pack.val y.pack.val c.b ≠ y.pack.val) :
    renewalBankPairMemory c m e dest x y =
      ({ worker := .empty,
         controller := renewalBankWaitSlot x.mode x.lease.val
           (m.sites e).controller },
       { worker := .empty, controller := .empty }) := by
  have hchangedZero : packNext 0 y.pack.val c.b ≠ y.pack.val := by
    simpa only [hx] using hchanged
  simp [renewalBankPairMemory, bankCell, hx, hg,
    hna, hnc, hchangedZero]

/-- The whole changed-role root class, including grant, cancelled
ARMED/CSTART and ordinary wait-slot sanitation. -/
theorem renewalBankChangedRootPairMass {n : Nat}
    (o : RenewalBankOrigin n) (K : Nat)
    (c : Compiled) (m : RenewalBankMemory n)
    (e dest : Fin n) (x y : Agent c)
    (hx : x.pack.val = 0)
    (hchanged : packNext x.pack.val y.pack.val c.b ≠ y.pack.val) :
    RenewalBankPairLocalBound o K c m e dest x y := by
  cases hg : x.grant with
  | true =>
      exact renewalBankErasedPairLocalMass o K c m e dest x y
        (renewalBankChangedRootGrantPairExact c m e dest x y
          hx hg hchanged)
  | false =>
      by_cases hm : x.mode = .ARMED ∨ x.mode = .CSTART
      · exact renewalBankErasedPairLocalMass o K c m e dest x y
          (renewalBankChangedRootLaunchPairExact c m e dest x y
            hx hg hm hchanged)
      · have hna : x.mode ≠ .ARMED := by
          intro he
          exact hm (Or.inl he)
        have hnc : x.mode ≠ .CSTART := by
          intro he
          exact hm (Or.inr he)
        have hpair := renewalBankChangedRootWaitPairExact
          c m e dest x y hx hg hna hnc hchanged
        have hwait := renewalBankWaitSlotWeightLe o K
          x.mode x.lease.val (m.sites e).controller
        have htarget := renewalBankSiteCreditLe o K y (m.sites dest)
        unfold RenewalBankPairLocalBound
        rw [hpair]
        simp only [renewalBankSiteWeight, renewalBankWorkerWeight,
          renewalBankControllerWeight] at hwait htarget ⊢
        omega

/-- All role-change sanitation edges, with no service-age premise.
This class makes no new origin and does not depend on validity. -/
theorem renewalBankChangedRolePairMass {n : Nat}
    (o : RenewalBankOrigin n) (K : Nat)
    (c : Compiled) (m : RenewalBankMemory n)
    (e dest : Fin n) (x y : Agent c)
    (hchanged : packNext x.pack.val y.pack.val c.b ≠ y.pack.val) :
    RenewalBankPairLocalBound o K c m e dest x y := by
  by_cases hx : x.pack.val = 0
  · exact renewalBankChangedRootPairMass
      o K c m e dest x y hx hchanged
  · exact renewalBankChangedNonrootPairMass
      o K c m e dest x y hx hchanged

end L3.HeadlineRenewal

/-!
Further BANK boundary, root, and return rows.
-/

namespace L3.HeadlineRenewal

open Classical

set_option autoImplicit false
set_option Elab.async false

/-- The destination role-zero sanitation rule pays any ARMED credit.
In a non-ARMED case its surviving wait slot only loses weight. -/
private theorem renewalBankTargetWaitCreditLe {n : Nat} {c : Compiled}
    (o : RenewalBankOrigin n) (K : Nat)
    (y : Agent c) (s : RenewalBankSite n) :
    renewalBankControllerWeight o K
        (if y.grant || y.mode == .ARMED then .empty
         else renewalBankWaitSlot y.mode y.lease.val s.controller) +
      renewalBankArmedSiteCredit o K y s ≤
    renewalBankControllerWeight o K s.controller := by
  have hw := renewalBankWaitSlotWeightLe o K y.mode
    y.lease.val s.controller
  cases hg : y.grant <;> cases hm : y.mode <;>
    simp [renewalBankArmedSiteCredit, hg, hm,
      renewalBankControllerWeight] at * <;>
    first | exact hw | omega

/-- The top-to-spacer pair is either erased or retains the old source
worker. Top IR has first priority and erases that source worker. -/
private theorem renewalBankTopSpacerPairExact {n : Nat}
    (c : Compiled) (m : RenewalBankMemory n)
    (e dest : Fin n) (x y : Agent c)
    (hb : 0 < c.b)
    (hx : x.pack.val = c.b)
    (hy : y.pack.val = c.b + 1) :
    renewalBankPairMemory c m e dest x y =
      ({ worker := .empty, controller := .empty },
       { worker := .empty, controller := .empty }) ∨
    renewalBankPairMemory c m e dest x y =
      ({ worker := (m.sites e).worker, controller := .empty },
       { worker := .empty, controller := .empty }) := by
  have hbz : c.b ≠ 0 := Nat.pos_iff_ne_zero.mp hb
  have houtside : ¬ c.b + 1 ≤ c.b := by omega
  have hp : packNext c.b (c.b + 1) c.b = c.b + 1 := by
    simp [packNext]
  by_cases hir : x.tok = .IR
  · left
    simp [renewalBankPairMemory, bankCell, hx, hy, hb,
      hbz, houtside, hp, hir]
  · right
    simp [renewalBankPairMemory, bankCell, hx, hy, hb,
      hbz, houtside, hp, hir]

theorem renewalBankTopSpacerPairMass {n : Nat}
    (o : RenewalBankOrigin n) (K : Nat)
    (c : Compiled) (m : RenewalBankMemory n)
    (e dest : Fin n) (x y : Agent c)
    (hb : 0 < c.b)
    (hx : x.pack.val = c.b)
    (hy : y.pack.val = c.b + 1) :
    RenewalBankPairLocalBound o K c m e dest x y := by
  have htarget := renewalBankSiteCreditLe o K y (m.sites dest)
  rcases renewalBankTopSpacerPairExact c m e dest x y
    hb hx hy with hpair | hpair
  · exact renewalBankErasedPairLocalMass o K c m e dest x y hpair
  · unfold RenewalBankPairLocalBound
    rw [hpair]
    simp only [renewalBankSiteWeight, renewalBankWorkerWeight,
      renewalBankControllerWeight] at htarget ⊢
    omega

/-- From the top role into role zero, top IR erases the source worker;
every other token keeps it. The old role-zero target may retain only
a waiting controller, except when grant or ARMED erases that slot. -/
private theorem renewalBankTopZeroPairExact {n : Nat}
    (c : Compiled) (m : RenewalBankMemory n)
    (e dest : Fin n) (x y : Agent c)
    (hb : 0 < c.b)
    (hx : x.pack.val = c.b) (hy : y.pack.val = 0) :
    renewalBankPairMemory c m e dest x y =
      ({ worker := .empty, controller := .empty },
       { worker := .empty,
         controller :=
           if y.grant || y.mode == .ARMED then .empty
           else renewalBankWaitSlot y.mode y.lease.val
             (m.sites dest).controller }) ∨
    renewalBankPairMemory c m e dest x y =
      ({ worker := (m.sites e).worker, controller := .empty },
       { worker := .empty,
         controller :=
           if y.grant || y.mode == .ARMED then .empty
           else renewalBankWaitSlot y.mode y.lease.val
             (m.sites dest).controller }) := by
  have hbz : c.b ≠ 0 := Nat.pos_iff_ne_zero.mp hb
  have hp : packNext c.b 0 c.b = 0 := by
    simp [packNext]
  by_cases hir : x.tok = .IR
  · left
    cases hg : y.grant <;> cases hm : y.mode <;>
      simp [renewalBankPairMemory, bankCell, hx, hy,
        hb, hbz, hp, hir, hg, hm]
  · right
    cases hg : y.grant <;> cases hm : y.mode <;>
      simp [renewalBankPairMemory, bankCell, hx, hy,
        hb, hbz, hp, hir, hg, hm]

theorem renewalBankTopZeroPairMass {n : Nat}
    (o : RenewalBankOrigin n) (K : Nat)
    (c : Compiled) (m : RenewalBankMemory n)
    (e dest : Fin n) (x y : Agent c)
    (hb : 0 < c.b)
    (hx : x.pack.val = c.b) (hy : y.pack.val = 0) :
    RenewalBankPairLocalBound o K c m e dest x y := by
  have htarget := renewalBankTargetWaitCreditLe
    o K y (m.sites dest)
  rcases renewalBankTopZeroPairExact c m e dest x y
    hb hx hy with hpair | hpair
  · unfold RenewalBankPairLocalBound
    rw [hpair]
    simp only [renewalBankSiteWeight, renewalBankWorkerWeight,
      renewalBankControllerWeight] at htarget ⊢
    omega
  · unfold RenewalBankPairLocalBound
    rw [hpair]
    simp only [renewalBankSiteWeight, renewalBankWorkerWeight,
      renewalBankControllerWeight] at htarget ⊢
    omega

/-- The spacer-to-zero edge erases the old source record and the old
destination worker, leaving at most its non-ARMED waiting slot. -/
private theorem renewalBankSpacerZeroPairExact {n : Nat}
    (c : Compiled) (m : RenewalBankMemory n)
    (e dest : Fin n) (x y : Agent c)
    (hx : x.pack.val = c.b + 1) (hy : y.pack.val = 0) :
    renewalBankPairMemory c m e dest x y =
      ({ worker := .empty, controller := .empty },
       { worker := .empty,
         controller :=
           if y.grant || y.mode == .ARMED then .empty
           else renewalBankWaitSlot y.mode y.lease.val
             (m.sites dest).controller }) := by
  have hnz : c.b + 1 ≠ 0 := by omega
  have houtside : ¬ c.b + 1 ≤ c.b := by omega
  have hp : packNext (c.b + 1) 0 c.b = 0 := by
    simp [packNext]
  cases hg : y.grant <;> cases hm : y.mode <;>
    simp [renewalBankPairMemory, bankCell, hx, hy,
      hnz, houtside, hp, hg, hm]

theorem renewalBankSpacerZeroPairMass {n : Nat}
    (o : RenewalBankOrigin n) (K : Nat)
    (c : Compiled) (m : RenewalBankMemory n)
    (e dest : Fin n) (x y : Agent c)
    (hx : x.pack.val = c.b + 1) (hy : y.pack.val = 0) :
    RenewalBankPairLocalBound o K c m e dest x y := by
  have hpair := renewalBankSpacerZeroPairExact
    c m e dest x y hx hy
  have htarget := renewalBankTargetWaitCreditLe
    o K y (m.sites dest)
  unfold RenewalBankPairLocalBound
  rw [hpair]
  simp only [renewalBankSiteWeight, renewalBankWorkerWeight,
    renewalBankControllerWeight] at htarget ⊢
  omega

/-- Root grant exits on the unchanged edge from role zero to role one,
erasing both old ghost records, including the target worker. -/
private theorem renewalBankRootGrantPairExact {n : Nat}
    (c : Compiled) (m : RenewalBankMemory n)
    (e dest : Fin n) (x y : Agent c)
    (hb : 0 < c.b)
    (hx : x.pack.val = 0) (hy : y.pack.val = 1)
    (hg : x.grant = true) :
    renewalBankPairMemory c m e dest x y =
      ({ worker := .empty, controller := .empty },
       { worker := .empty, controller := .empty }) := by
  have hbz : c.b ≠ 0 := Nat.pos_iff_ne_zero.mp hb
  have hp : packNext 0 1 c.b = 1 := by
    simp [packNext, hb]
  simp [renewalBankPairMemory, bankCell, hx, hy,
    hb, hbz, hp, hg]

theorem renewalBankRootGrantPairMass {n : Nat}
    (o : RenewalBankOrigin n) (K : Nat)
    (c : Compiled) (m : RenewalBankMemory n)
    (e dest : Fin n) (x y : Agent c)
    (hb : 0 < c.b)
    (hx : x.pack.val = 0) (hy : y.pack.val = 1)
    (hg : x.grant = true) :
    RenewalBankPairLocalBound o K c m e dest x y := by
  exact renewalBankErasedPairLocalMass o K c m e dest x y
    (renewalBankRootGrantPairExact c m e dest x y hb hx hy hg)

/-- The first root RESET selection writes a pending receipt to the
responder, never a weighted origin payload. This branch precedes
isRetTok, so no hypothesis on the old responder token is needed. -/
private theorem renewalBankRootResetPairExact {n : Nat}
    (c : Compiled) (m : RenewalBankMemory n)
    (e dest : Fin n) (x y : Agent c)
    (hb : 0 < c.b)
    (hx : x.pack.val = 0) (hy : y.pack.val = 1)
    (hg : x.grant = false) (hm : x.mode = .RESET) :
    renewalBankPairMemory c m e dest x y =
      ({ worker := .empty, controller := .waiting [] },
       { worker := .pending { service := m.service, root := e },
         controller := .empty }) := by
  have hbz : c.b ≠ 0 := Nat.pos_iff_ne_zero.mp hb
  have hp : packNext 0 1 c.b = 1 := by
    simp [packNext, hb]
  simp [renewalBankPairMemory, bankCell, hx, hy,
    hb, hbz, hp, hg, hm]

theorem renewalBankRootResetPairMass {n : Nat}
    (o : RenewalBankOrigin n) (K : Nat)
    (c : Compiled) (m : RenewalBankMemory n)
    (e dest : Fin n) (x y : Agent c)
    (hb : 0 < c.b)
    (hx : x.pack.val = 0) (hy : y.pack.val = 1)
    (hg : x.grant = false) (hm : x.mode = .RESET) :
    RenewalBankPairLocalBound o K c m e dest x y := by
  have hpair := renewalBankRootResetPairExact
    c m e dest x y hb hx hy hg hm
  have htarget := renewalBankSiteCreditLe o K y (m.sites dest)
  have hsource :
      renewalBankArmedSiteCredit o K x (m.sites e) = 0 := by
    simp [renewalBankArmedSiteCredit, hm]
  unfold RenewalBankPairLocalBound
  rw [hpair, hsource]
  simp only [renewalBankSiteWeight, renewalBankWorkerWeight,
    renewalBankControllerWeight] at htarget ⊢
  omega

/-- CSTART with an empty responder token moves the origin from the
controller into the responder worker, without a head increment. -/
private theorem renewalBankRootCstartPairExact {n : Nat}
    (c : Compiled) (m : RenewalBankMemory n)
    (e dest : Fin n) (x y : Agent c)
    (hb : 0 < c.b)
    (hx : x.pack.val = 0) (hy : y.pack.val = 1)
    (hg : x.grant = false) (hm : x.mode = .CSTART)
    (ht : y.tok = .E) :
    renewalBankPairMemory c m e dest x y =
      ({ worker := .empty, controller := .waiting [] },
       { worker := .payload
           (renewalBankActivePayload (m.sites e).controller e),
         controller := .empty }) := by
  have hbz : c.b ≠ 0 := Nat.pos_iff_ne_zero.mp hb
  have hp : packNext 0 1 c.b = 1 := by
    simp [packNext, hb]
  simp [renewalBankPairMemory, bankCell, hx, hy,
    hb, hbz, hp, hg, hm, ht, isRetTok]

theorem renewalBankRootCstartPairMass {n : Nat}
    (o : RenewalBankOrigin n) (K : Nat)
    (c : Compiled) (m : RenewalBankMemory n)
    (e dest : Fin n) (x y : Agent c)
    (hb : 0 < c.b)
    (hx : x.pack.val = 0) (hy : y.pack.val = 1)
    (hg : x.grant = false) (hm : x.mode = .CSTART)
    (ht : y.tok = .E) :
    RenewalBankPairLocalBound o K c m e dest x y := by
  have hpair := renewalBankRootCstartPairExact
    c m e dest x y hb hx hy hg hm ht
  have hactive := renewalBankActivePayloadWeightLe
    o K e (m.sites e).controller
  have htarget := renewalBankSiteCreditLe o K y (m.sites dest)
  have hsource :
      renewalBankArmedSiteCredit o K x (m.sites e) = 0 := by
    simp [renewalBankArmedSiteCredit, hm]
  unfold RenewalBankPairLocalBound
  rw [hpair, hsource]
  simp only [renewalBankSiteWeight, renewalBankWorkerWeight,
    renewalBankControllerWeight] at hactive htarget ⊢
  omega

/-- A return-token CSTART row consumes the old responder worker,
but cannot be a matching return: only IWAIT/AL or CWAIT/CL can
promote workers, and RWAIT/RL can mint a receipt. -/
private theorem renewalBankRootCstartReturnPairExact {n : Nat}
    (c : Compiled) (m : RenewalBankMemory n)
    (e dest : Fin n) (x y : Agent c)
    (hb : 0 < c.b)
    (hx : x.pack.val = 0) (hy : y.pack.val = 1)
    (hg : x.grant = false) (hm : x.mode = .CSTART)
    (ht : isRetTok y.tok = true) :
    renewalBankPairMemory c m e dest x y =
      ({ worker := .empty, controller := (m.sites e).controller },
       { worker := .empty, controller := .empty }) := by
  have hbz : c.b ≠ 0 := Nat.pos_iff_ne_zero.mp hb
  have hp : packNext 0 1 c.b = 1 := by
    simp [packNext, hb]
  simp [renewalBankPairMemory, bankCell, hx, hy,
    hb, hbz, hp, hg, hm, ht, renewalBankWaitSlot, isWaitMode]

theorem renewalBankRootCstartReturnPairMass {n : Nat}
    (o : RenewalBankOrigin n) (K : Nat)
    (c : Compiled) (m : RenewalBankMemory n)
    (e dest : Fin n) (x y : Agent c)
    (hb : 0 < c.b)
    (hx : x.pack.val = 0) (hy : y.pack.val = 1)
    (hg : x.grant = false) (hm : x.mode = .CSTART)
    (ht : isRetTok y.tok = true) :
    RenewalBankPairLocalBound o K c m e dest x y := by
  have hpair := renewalBankRootCstartReturnPairExact
    c m e dest x y hb hx hy hg hm ht
  have htarget := renewalBankSiteCreditLe o K y (m.sites dest)
  have hsource :
      renewalBankArmedSiteCredit o K x (m.sites e) = 0 := by
    simp [renewalBankArmedSiteCredit, hm]
  unfold RenewalBankPairLocalBound
  rw [hpair, hsource]
  simp only [renewalBankSiteWeight, renewalBankWorkerWeight,
    renewalBankControllerWeight] at htarget ⊢
  omega

/-- A nonempty, nonreturn responder token aborts CSTART and
erases both records. -/
private theorem renewalBankRootCstartCollisionPairExact {n : Nat}
    (c : Compiled) (m : RenewalBankMemory n)
    (e dest : Fin n) (x y : Agent c)
    (hb : 0 < c.b)
    (hx : x.pack.val = 0) (hy : y.pack.val = 1)
    (hg : x.grant = false) (hm : x.mode = .CSTART)
    (hret : isRetTok y.tok = false) (hbusy : y.tok ≠ .E) :
    renewalBankPairMemory c m e dest x y =
      ({ worker := .empty, controller := .empty },
       { worker := .empty, controller := .empty }) := by
  have hbz : c.b ≠ 0 := Nat.pos_iff_ne_zero.mp hb
  have hp : packNext 0 1 c.b = 1 := by
    simp [packNext, hb]
  simp [renewalBankPairMemory, bankCell, hx, hy,
    hb, hbz, hp, hg, hm, hret, hbusy]

theorem renewalBankRootCstartCollisionPairMass {n : Nat}
    (o : RenewalBankOrigin n) (K : Nat)
    (c : Compiled) (m : RenewalBankMemory n)
    (e dest : Fin n) (x y : Agent c)
    (hb : 0 < c.b)
    (hx : x.pack.val = 0) (hy : y.pack.val = 1)
    (hg : x.grant = false) (hm : x.mode = .CSTART)
    (hret : isRetTok y.tok = false) (hbusy : y.tok ≠ .E) :
    RenewalBankPairLocalBound o K c m e dest x y := by
  exact renewalBankErasedPairLocalMass o K c m e dest x y
    (renewalBankRootCstartCollisionPairExact c m e dest x y
      hb hx hy hg hm hret hbusy)

end L3.HeadlineRenewal

/-!
BANK root/nonroot row closure.
No transition, memory field, or mathematical assumption is changed.
-/

namespace L3.HeadlineRenewal

open Classical

set_option autoImplicit false
set_option Elab.async false

/-- On an unchanged root wait row, an ordinary nonreturn token
retains the target worker, except for the width-one IR cleanup.
These are the only two outcomes. -/
private theorem renewalBankRootWaitingNonreturnPairExact {n : Nat}
    (c : Compiled) (m : RenewalBankMemory n)
    (e dest : Fin n) (x y : Agent c)
    (hb : 0 < c.b)
    (hx : x.pack.val = 0) (hy : y.pack.val = 1)
    (hg : x.grant = false)
    (hmode : x.mode = .RWAIT ∨ x.mode = .IWAIT ∨
      x.mode = .CWAIT)
    (hret : isRetTok y.tok = false) :
    renewalBankPairMemory c m e dest x y =
      ({ worker := .empty,
         controller := renewalBankWaitSlot x.mode x.lease.val
           (m.sites e).controller },
       { worker := .empty, controller := .empty }) ∨
    renewalBankPairMemory c m e dest x y =
      ({ worker := .empty,
         controller := renewalBankWaitSlot x.mode x.lease.val
           (m.sites e).controller },
       { worker := (m.sites dest).worker, controller := .empty }) := by
  have hbz : c.b ≠ 0 := Nat.pos_iff_ne_zero.mp hb
  have hp : packNext 0 1 c.b = 1 := by
    simp [packNext, hb]
  rcases hmode with hm | hm | hm
  all_goals
    by_cases hwidth : c.b = 1
    · have hp1 : packNext 0 1 1 = 1 := by
        have h := hp
        rw [hwidth] at h
        exact h
      by_cases hir : y.tok = .IR
      · left
        simp [renewalBankPairMemory, bankCell, hx, hy,
          hb, hbz, hp, hp1, hg, hm, hret, hwidth, hir,
          isWaitMode, isRetTok]
      · right
        simp [renewalBankPairMemory, bankCell, hx, hy,
          hb, hbz, hp, hp1, hg, hm, hret, hwidth, hir,
          isWaitMode]
    · right
      simp [renewalBankPairMemory, bankCell, hx, hy,
        hb, hbz, hp, hg, hm, hret, hwidth,
        isWaitMode]

theorem renewalBankRootWaitingNonreturnPairMass {n : Nat}
    (o : RenewalBankOrigin n) (K : Nat)
    (c : Compiled) (m : RenewalBankMemory n)
    (e dest : Fin n) (x y : Agent c)
    (hb : 0 < c.b)
    (hx : x.pack.val = 0) (hy : y.pack.val = 1)
    (hg : x.grant = false)
    (hmode : x.mode = .RWAIT ∨ x.mode = .IWAIT ∨
      x.mode = .CWAIT)
    (hret : isRetTok y.tok = false) :
    RenewalBankPairLocalBound o K c m e dest x y := by
  have hpair := renewalBankRootWaitingNonreturnPairExact
    c m e dest x y hb hx hy hg hmode hret
  have hwait := renewalBankWaitSlotWeightLe o K
    x.mode x.lease.val (m.sites e).controller
  have htarget := renewalBankSiteCreditLe o K y (m.sites dest)
  rcases hpair with hpair | hpair
  · unfold RenewalBankPairLocalBound
    rw [hpair]
    simp only [renewalBankSiteWeight, renewalBankWorkerWeight,
      renewalBankControllerWeight] at hwait htarget ⊢
    omega
  · unfold RenewalBankPairLocalBound
    rw [hpair]
    simp only [renewalBankSiteWeight, renewalBankWorkerWeight,
      renewalBankControllerWeight] at hwait htarget ⊢
    omega

/-- IWAIT/AL and CWAIT/CL0 both consume the old responder worker
and reconstitute its origin in the source controller. -/
private theorem renewalBankRootReturnPromotePairExact {n : Nat}
    (c : Compiled) (m : RenewalBankMemory n)
    (e dest : Fin n) (x y : Agent c)
    (hb : 0 < c.b)
    (hx : x.pack.val = 0) (hy : y.pack.val = 1)
    (hg : x.grant = false)
    (hmatch : (x.mode = .IWAIT ∧ y.tok = .AL) ∨
      (x.mode = .CWAIT ∧ y.tok = .CL0)) :
    renewalBankPairMemory c m e dest x y =
      ({ worker := .empty,
         controller := .active
           (renewalBankReturned (m.sites e).controller
             (m.sites dest).worker dest) },
       { worker := .empty, controller := .empty }) := by
  have hbz : c.b ≠ 0 := Nat.pos_iff_ne_zero.mp hb
  have hp : packNext 0 1 c.b = 1 := by
    simp [packNext, hb]
  rcases hmatch with ⟨hm, ht⟩ | ⟨hm, ht⟩
  · simp [renewalBankPairMemory, bankCell, hx, hy,
      hb, hbz, hp, hg, hm, ht, isRetTok]
  · simp [renewalBankPairMemory, bankCell, hx, hy,
      hb, hbz, hp, hg, hm, ht, isRetTok]

theorem renewalBankRootReturnPromotePairMass {n : Nat}
    (o : RenewalBankOrigin n) (K : Nat)
    (c : Compiled) (m : RenewalBankMemory n)
    (e dest : Fin n) (x y : Agent c)
    (hb : 0 < c.b)
    (hx : x.pack.val = 0) (hy : y.pack.val = 1)
    (hg : x.grant = false)
    (hmatch : (x.mode = .IWAIT ∧ y.tok = .AL) ∨
      (x.mode = .CWAIT ∧ y.tok = .CL0)) :
    RenewalBankPairLocalBound o K c m e dest x y := by
  have hpair := renewalBankRootReturnPromotePairExact
    c m e dest x y hb hx hy hg hmatch
  have hnew := renewalBankReturnedWeightLe o K dest
    (m.sites e).controller (m.sites dest).worker
  have htarget := renewalBankSiteCreditLe o K y (m.sites dest)
  unfold RenewalBankPairLocalBound
  rw [hpair]
  simp only [renewalBankSiteWeight, renewalBankWorkerWeight,
    renewalBankControllerWeight] at hnew htarget ⊢
  omega

/-- CWAIT/CL1 is the terminal return and discards both records. -/
private theorem renewalBankRootReturnSuccessPairExact {n : Nat}
    (c : Compiled) (m : RenewalBankMemory n)
    (e dest : Fin n) (x y : Agent c)
    (hb : 0 < c.b)
    (hx : x.pack.val = 0) (hy : y.pack.val = 1)
    (hg : x.grant = false)
    (hm : x.mode = .CWAIT) (ht : y.tok = .CL1) :
    renewalBankPairMemory c m e dest x y =
      ({ worker := .empty, controller := .empty },
       { worker := .empty, controller := .empty }) := by
  have hbz : c.b ≠ 0 := Nat.pos_iff_ne_zero.mp hb
  have hp : packNext 0 1 c.b = 1 := by
    simp [packNext, hb]
  simp [renewalBankPairMemory, bankCell, hx, hy,
    hb, hbz, hp, hg, hm, ht, isRetTok]

theorem renewalBankRootReturnSuccessPairMass {n : Nat}
    (o : RenewalBankOrigin n) (K : Nat)
    (c : Compiled) (m : RenewalBankMemory n)
    (e dest : Fin n) (x y : Agent c)
    (hb : 0 < c.b)
    (hx : x.pack.val = 0) (hy : y.pack.val = 1)
    (hg : x.grant = false)
    (hm : x.mode = .CWAIT) (ht : y.tok = .CL1) :
    RenewalBankPairLocalBound o K c m e dest x y := by
  exact renewalBankErasedPairLocalMass o K c m e dest x y
    (renewalBankRootReturnSuccessPairExact
      c m e dest x y hb hx hy hg hm ht)


/-- A nonmatching return erases the responder worker and ticks only
the source wait slot. RESET is excluded: its launch has higher priority. -/
private theorem renewalBankRootReturnUnmatchedPairExact {n : Nat}
    (c : Compiled) (m : RenewalBankMemory n)
    (e dest : Fin n) (x y : Agent c)
    (hb : 0 < c.b)
    (hx : x.pack.val = 0) (hy : y.pack.val = 1)
    (hg : x.grant = false)
    (hreset : x.mode ≠ .RESET)
    (hret : isRetTok y.tok = true)
    (hrl : ¬ (y.tok = .RL ∧ x.mode = .RWAIT))
    (hal : ¬ (y.tok = .AL ∧ x.mode = .IWAIT))
    (hcl : ¬ ((y.tok = .CL0 ∨ y.tok = .CL1) ∧
      x.mode = .CWAIT)) :
    renewalBankPairMemory c m e dest x y =
      ({ worker := .empty,
         controller := renewalBankWaitSlot x.mode x.lease.val
           (m.sites e).controller },
       { worker := .empty, controller := .empty }) := by
  have hbz : c.b ≠ 0 := Nat.pos_iff_ne_zero.mp hb
  have hp : packNext 0 1 c.b = 1 := by
    simp [packNext, hb]
  cases hm : x.mode <;> cases ht : y.tok <;>
    simp [renewalBankPairMemory, bankCell, hx, hy,
      hb, hbz, hp, hg, hm, ht, isRetTok,
      renewalBankWaitSlot, isWaitMode] at *

theorem renewalBankRootReturnUnmatchedPairMass {n : Nat}
    (o : RenewalBankOrigin n) (K : Nat)
    (c : Compiled) (m : RenewalBankMemory n)
    (e dest : Fin n) (x y : Agent c)
    (hb : 0 < c.b)
    (hx : x.pack.val = 0) (hy : y.pack.val = 1)
    (hg : x.grant = false)
    (hreset : x.mode ≠ .RESET)
    (hret : isRetTok y.tok = true)
    (hrl : ¬ (y.tok = .RL ∧ x.mode = .RWAIT))
    (hal : ¬ (y.tok = .AL ∧ x.mode = .IWAIT))
    (hcl : ¬ ((y.tok = .CL0 ∨ y.tok = .CL1) ∧
      x.mode = .CWAIT)) :
    RenewalBankPairLocalBound o K c m e dest x y := by
  have hpair := renewalBankRootReturnUnmatchedPairExact
    c m e dest x y hb hx hy hg hreset hret hrl hal hcl
  have hwait := renewalBankWaitSlotWeightLe o K
    x.mode x.lease.val (m.sites e).controller
  have htarget := renewalBankSiteCreditLe o K y (m.sites dest)
  unfold RenewalBankPairLocalBound
  rw [hpair]
  simp only [renewalBankSiteWeight, renewalBankWorkerWeight,
    renewalBankControllerWeight] at hwait htarget ⊢
  omega

/-- The remaining ARMED failure: a nonempty nonreturn responder
token erases both sites without duplicating the tracked origin. -/
private theorem renewalBankRootArmedCollisionPairExact {n : Nat}
    (c : Compiled) (m : RenewalBankMemory n)
    (e dest : Fin n) (x y : Agent c)
    (hb : 0 < c.b)
    (hx : x.pack.val = 0) (hy : y.pack.val = 1)
    (hg : x.grant = false) (hm : x.mode = .ARMED)
    (hret : isRetTok y.tok = false) (hbusy : y.tok ≠ .E) :
    renewalBankPairMemory c m e dest x y =
      ({ worker := .empty, controller := .empty },
       { worker := .empty, controller := .empty }) := by
  have hbz : c.b ≠ 0 := Nat.pos_iff_ne_zero.mp hb
  have hp : packNext 0 1 c.b = 1 := by
    simp [packNext, hb]
  simp [renewalBankPairMemory, bankCell, hx, hy,
    hb, hbz, hp, hg, hm, hret, hbusy]

theorem renewalBankRootArmedCollisionPairMass {n : Nat}
    (o : RenewalBankOrigin n) (K : Nat)
    (c : Compiled) (m : RenewalBankMemory n)
    (e dest : Fin n) (x y : Agent c)
    (hb : 0 < c.b)
    (hx : x.pack.val = 0) (hy : y.pack.val = 1)
    (hg : x.grant = false) (hm : x.mode = .ARMED)
    (hret : isRetTok y.tok = false) (hbusy : y.tok ≠ .E) :
    RenewalBankPairLocalBound o K c m e dest x y := by
  exact renewalBankErasedPairLocalMass o K c m e dest x y
    (renewalBankRootArmedCollisionPairExact c m e dest x y
      hb hx hy hg hm hret hbusy)

/-- An unchanged nonroot interior pair (including a top responder)
has exactly six possible worker arrangements. The token cases include
all RR/IR/CR/AL/CL and mixed-token priorities, including pre-transfer
top IR clearance. Controllers are always empty on these rows. -/
private theorem renewalBankInteriorAnyTokensPairExact {n : Nat}
    (c : Compiled) (m : RenewalBankMemory n)
    (e dest : Fin n) (x y : Agent c) (r : Nat)
    (hfirst : 1 ≤ r) (hlt : r < c.b)
    (hx : x.pack.val = r) (hy : y.pack.val = r + 1) :
    renewalBankPairMemory c m e dest x y =
      ({ worker := (m.sites e).worker, controller := .empty },
       { worker := (m.sites dest).worker, controller := .empty }) ∨
    renewalBankPairMemory c m e dest x y =
      ({ worker := .empty, controller := .empty },
       { worker := (m.sites dest).worker, controller := .empty }) ∨
    renewalBankPairMemory c m e dest x y =
      ({ worker := (m.sites e).worker, controller := .empty },
       { worker := .empty, controller := .empty }) ∨
    renewalBankPairMemory c m e dest x y =
      ({ worker := .empty, controller := .empty },
       { worker := .empty, controller := .empty }) ∨
    renewalBankPairMemory c m e dest x y =
      ({ worker := .empty, controller := .empty },
       { worker := (m.sites e).worker, controller := .empty }) ∨
    renewalBankPairMemory c m e dest x y =
      ({ worker := (m.sites dest).worker, controller := .empty },
       { worker := .empty, controller := .empty }) := by
  have hle : r ≤ c.b := by omega
  have hnz : r ≠ 0 := by omega
  have htop : r ≠ c.b := by omega
  have hnextLe : r + 1 ≤ c.b := by omega
  have hnextPos : 1 ≤ r + 1 := by omega
  have hnextNz : r + 1 ≠ 0 := by omega
  have hp : packNext r (r + 1) c.b = r + 1 := by
    simp [packNext, hlt]
  have hbz : c.b ≠ 0 := by omega
  by_cases hnextTop : r + 1 = c.b
  · have hpTop : packNext r c.b c.b = c.b := by
      have h := hp
      rw [hnextTop] at h
      exact h
    cases hxt : x.tok <;> cases hyt : y.tok <;>
      simp [renewalBankPairMemory, bankCell, hx, hy,
        hfirst, hlt, hle, hnz, htop, hnextLe, hnextPos,
        hnextNz, hp, hpTop, hbz, hnextTop, hxt, hyt]
  · cases hxt : x.tok <;> cases hyt : y.tok <;>
      simp [renewalBankPairMemory, bankCell, hx, hy,
        hfirst, hlt, hle, hnz, htop, hnextLe, hnextPos,
        hnextNz, hp, hnextTop, hxt, hyt]

theorem renewalBankInteriorAnyTokensPairMass {n : Nat}
    (o : RenewalBankOrigin n) (K : Nat)
    (c : Compiled) (m : RenewalBankMemory n)
    (e dest : Fin n) (x y : Agent c) (r : Nat)
    (hfirst : 1 ≤ r) (hlt : r < c.b)
    (hx : x.pack.val = r) (hy : y.pack.val = r + 1) :
    RenewalBankPairLocalBound o K c m e dest x y := by
  have hpair := renewalBankInteriorAnyTokensPairExact
    c m e dest x y r hfirst hlt hx hy
  have htarget := renewalBankSiteCreditLe o K y (m.sites dest)
  rcases hpair with hpair | hpair | hpair | hpair | hpair | hpair
  all_goals
    unfold RenewalBankPairLocalBound
    rw [hpair]
    simp only [renewalBankSiteWeight, renewalBankWorkerWeight,
      renewalBankControllerWeight] at htarget ⊢
    omega


/-- The complete unchanged-root transition class. RESET precedes
returns; RWAIT/RL may create a pending receipt, paid only under
strict origin age; all other return matches transfer or erase mass. -/
private theorem renewalBankRootUnchangedPairMass {n : Nat}
    (o : RenewalBankOrigin n) (K : Nat)
    (c : Compiled) (m : RenewalBankMemory n)
    (e dest : Fin n) (x y : Agent c)
    (hfuture : o.service < m.service)
    (hb : 0 < c.b)
    (hx : x.pack.val = 0) (hy : y.pack.val = 1) :
    RenewalBankPairLocalBound o K c m e dest x y := by
  cases hg : x.grant with
  | true =>
      exact renewalBankRootGrantPairMass
        o K c m e dest x y hb hx hy hg
  | false =>
      cases hm : x.mode with
      | RESET =>
          exact renewalBankRootResetPairMass
            o K c m e dest x y hb hx hy hg hm
      | ARMED =>
          by_cases he : y.tok = .E
          · exact renewalBankArmedHeadPairMass
              o K c m e dest x y hb hx hy hg hm he
          · cases hret : isRetTok y.tok with
            | false =>
                exact renewalBankRootArmedCollisionPairMass
                  o K c m e dest x y hb hx hy hg hm hret he
            | true =>
                have hreset : x.mode ≠ .RESET := by simp [hm]
                have hrl : ¬ (y.tok = .RL ∧ x.mode = .RWAIT) := by
                  simp [hm]
                have hal : ¬ (y.tok = .AL ∧ x.mode = .IWAIT) := by
                  simp [hm]
                have hcl : ¬ ((y.tok = .CL0 ∨ y.tok = .CL1) ∧
                    x.mode = .CWAIT) := by
                  simp [hm]
                exact renewalBankRootReturnUnmatchedPairMass
                  o K c m e dest x y hb hx hy hg
                  hreset hret hrl hal hcl
      | CSTART =>
          by_cases he : y.tok = .E
          · exact renewalBankRootCstartPairMass
              o K c m e dest x y hb hx hy hg hm he
          · cases hret : isRetTok y.tok with
            | true =>
                exact renewalBankRootCstartReturnPairMass
                  o K c m e dest x y hb hx hy hg hm hret
            | false =>
                exact renewalBankRootCstartCollisionPairMass
                  o K c m e dest x y hb hx hy hg hm hret he
      | RWAIT =>
          cases hret : isRetTok y.tok with
          | false =>
              exact renewalBankRootWaitingNonreturnPairMass
                o K c m e dest x y hb hx hy hg
                (Or.inl hm) hret
          | true =>
              by_cases hrlTok : y.tok = .RL
              · exact renewalBankResetReturnPairMass
                  o K c m e dest x y hfuture hb hx hy hg hm hrlTok
              · have hreset : x.mode ≠ .RESET := by simp [hm]
                have hrl : ¬ (y.tok = .RL ∧ x.mode = .RWAIT) := by
                  intro hh
                  exact hrlTok hh.1
                have hal : ¬ (y.tok = .AL ∧ x.mode = .IWAIT) := by
                  simp [hm]
                have hcl : ¬ ((y.tok = .CL0 ∨ y.tok = .CL1) ∧
                    x.mode = .CWAIT) := by
                  simp [hm]
                exact renewalBankRootReturnUnmatchedPairMass
                  o K c m e dest x y hb hx hy hg
                  hreset hret hrl hal hcl
      | IWAIT =>
          cases hret : isRetTok y.tok with
          | false =>
              exact renewalBankRootWaitingNonreturnPairMass
                o K c m e dest x y hb hx hy hg
                (Or.inr (Or.inl hm)) hret
          | true =>
              by_cases halTok : y.tok = .AL
              · exact renewalBankRootReturnPromotePairMass
                  o K c m e dest x y hb hx hy hg
                  (Or.inl ⟨hm, halTok⟩)
              · have hreset : x.mode ≠ .RESET := by simp [hm]
                have hrl : ¬ (y.tok = .RL ∧ x.mode = .RWAIT) := by
                  simp [hm]
                have hal : ¬ (y.tok = .AL ∧ x.mode = .IWAIT) := by
                  intro hh
                  exact halTok hh.1
                have hcl : ¬ ((y.tok = .CL0 ∨ y.tok = .CL1) ∧
                    x.mode = .CWAIT) := by
                  simp [hm]
                exact renewalBankRootReturnUnmatchedPairMass
                  o K c m e dest x y hb hx hy hg
                  hreset hret hrl hal hcl
      | CWAIT =>
          cases hret : isRetTok y.tok with
          | false =>
              exact renewalBankRootWaitingNonreturnPairMass
                o K c m e dest x y hb hx hy hg
                (Or.inr (Or.inr hm)) hret
          | true =>
              by_cases hclZero : y.tok = .CL0
              · exact renewalBankRootReturnPromotePairMass
                  o K c m e dest x y hb hx hy hg
                  (Or.inr ⟨hm, hclZero⟩)
              · by_cases hclOne : y.tok = .CL1
                · exact renewalBankRootReturnSuccessPairMass
                    o K c m e dest x y hb hx hy hg hm hclOne
                · have hreset : x.mode ≠ .RESET := by simp [hm]
                  have hrl : ¬ (y.tok = .RL ∧ x.mode = .RWAIT) := by
                    simp [hm]
                  have hal : ¬ (y.tok = .AL ∧ x.mode = .IWAIT) := by
                    simp [hm]
                  have hcl : ¬ ((y.tok = .CL0 ∨ y.tok = .CL1) ∧
                      x.mode = .CWAIT) := by
                    intro hh
                    cases hh.1 with
                    | inl htok => exact hclZero htok
                    | inr htok => exact hclOne htok
                  exact renewalBankRootReturnUnmatchedPairMass
                    o K c m e dest x y hb hx hy hg
                    hreset hret hrl hal hcl


/-- Unchanged nonroot pairs: inside b, top b, and spacer b+1.
All top-to-zero role-zero destination waits are already accounted
for by the three boundary mass lemmas. -/
private theorem renewalBankNonrootUnchangedPairMass {n : Nat}
    (o : RenewalBankOrigin n) (K : Nat)
    (c : Compiled) (m : RenewalBankMemory n)
    (e dest : Fin n) (x y : Agent c)
    (hb : 0 < c.b)
    (hx : x.pack.val ≠ 0)
    (hunchanged : packNext x.pack.val y.pack.val c.b =
      y.pack.val) :
    RenewalBankPairLocalBound o K c m e dest x y := by
  by_cases hinside : x.pack.val < c.b
  · have hfirst : 1 ≤ x.pack.val := by omega
    have hp :
        packNext x.pack.val y.pack.val c.b =
          x.pack.val + 1 := by
      simp [packNext, hinside]
    have hy : y.pack.val = x.pack.val + 1 := by omega
    exact renewalBankInteriorAnyTokensPairMass
      o K c m e dest x y x.pack.val
      hfirst hinside rfl hy
  · by_cases htop : x.pack.val = c.b
    · by_cases hyzero : y.pack.val = 0
      · exact renewalBankTopZeroPairMass
          o K c m e dest x y hb htop hyzero
      · have hp :
            packNext c.b y.pack.val c.b = c.b + 1 := by
          simp [packNext, hyzero]
        have hysp : y.pack.val = c.b + 1 := by
          rw [htop] at hunchanged
          omega
        exact renewalBankTopSpacerPairMass
          o K c m e dest x y hb htop hysp
    · have hupper := x.pack.isLt
      have hxsp : x.pack.val = c.b + 1 := by omega
      have hp :
          packNext (c.b + 1) y.pack.val c.b = 0 := by
        simp [packNext]
      have hyzero : y.pack.val = 0 := by
        rw [hxsp] at hunchanged
        omega
      exact renewalBankSpacerZeroPairMass
        o K c m e dest x y hxsp hyzero

/-- Exhaustive BANK two-site potential drift for a completed origin
strictly older than the current service. Role changes use the proved
sanitation split; unchanged roles divide into root and nonroot rows.
No state-validity or ghost-uniqueness assumption is added. -/
theorem renewalBankPairLocalBoundAll {n : Nat}
    (o : RenewalBankOrigin n) (K : Nat)
    (c : Compiled) (m : RenewalBankMemory n)
    (e dest : Fin n) (x y : Agent c)
    (hfuture : o.service < m.service) :
    RenewalBankPairLocalBound o K c m e dest x y := by
  have hb : 0 < c.b := by
    unfold Compiled.b
    omega
  by_cases hunchanged :
      packNext x.pack.val y.pack.val c.b = y.pack.val
  · by_cases hx : x.pack.val = 0
    · have hp : packNext 0 y.pack.val c.b = 1 := by
        simp [packNext, hb]
      have hy : y.pack.val = 1 := by
        rw [hx] at hunchanged
        omega
      exact renewalBankRootUnchangedPairMass
        o K c m e dest x y hfuture hb hx hy
    · exact renewalBankNonrootUnchangedPairMass
        o K c m e dest x y hb hx hunchanged
  · exact renewalBankChangedRolePairMass
      o K c m e dest x y hunchanged

/-- All concrete future-reference pair mass drift inequalities on
the physical directed ring. No altered protocol step is used. -/
theorem renewalBankFuturePairMassDrift {n : Nat}
    (ring : DirectedRing n) (o : RenewalBankOrigin n)
    (K : Nat) (r : RenewalBankFuture o) :
    RenewalBankPairMassDrift ring o K r.val := by
  apply renewalBankPairMassDriftOfLocalBounds ring o K r
  intro e
  exact renewalBankPairLocalBoundAll
    o K (compileAdvice (ceilLogTwo n)) r.val.2
    e (ring.rightNeighbor e)
    (r.val.1 e) (r.val.1 (ring.rightNeighbor e)) r.property

/-- F.2 origin-rarity conclusion using the existing mass-potential
hstep and hwin/hbirth consumers; no assumed drift hypothesis. -/
theorem renewalBankValidRarityOfOriginPotential {n : Nat}
    (hn : 5 ≤ n)
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) :
    ReferenceOriginRarity ring
      (bankValidRootedReferenceData ring hbank)
      (compileAdvice (ceilLogTwo n)).kappa := by
  exact renewalBankValidRarityOfOriginPotentialOfPairMassDrift
    hn ring hbank
    (fun o r => renewalBankFuturePairMassDrift ring o
      (compileAdvice (ceilLogTwo n)).K r)

end L3.HeadlineRenewal


/-!
Reference ceiling and conditional spatial realization.

The genuinely outstanding obligations are the causal retry-origin
attribution (ReferenceRetryCoverage) and the decorated reference
clock (ReferenceClock). Neither follows from origin rarity alone.

This section proves the selected coefficient margins and gives explicit
composition interfaces without claiming those open producers.
-/

namespace L3.HeadlineRenewal

open Classical

set_option autoImplicit false
set_option Elab.async false

/-- F.7/F.34: the *reference*, rather than renewal, rate. -/
def renewalBankReferenceCeiling (n : Nat) : Nat :=
  headlineReferenceRate (ceilLogTwo n)

/-- The exact integer reserve follows from a strict per-service
coefficient surplus, provided the scheduler denominator pays one
copy of the coefficient R. -/
private theorem renewalBankReserveFromSlack (A V R d : Nat)
    (hmargin : A < V)
    (hslack : A * V < (V - A) * R)
    (hR : R ≤ d) :
    A * V * d ≤ ((V - A) * d - 1) * R := by
  have hgap : 0 < V - A := by omega
  have hRpos : 0 < R := by
    by_cases hz : R = 0
    · rw [hz, Nat.mul_zero] at hslack
      omega
    · omega
  have hd : 0 < d := by omega
  have hden : 0 < (V - A) * d := Nat.mul_pos hgap hd
  have hunit : A * V + 1 ≤ (V - A) * R := by omega
  have hsum : A * V * d + R ≤ ((V - A) * d) * R := by
    calc
      A * V * d + R ≤ A * V * d + d :=
        Nat.add_le_add_left hR _
      _ = (A * V + 1) * d := by
        rw [Nat.add_mul, Nat.one_mul]
      _ ≤ ((V - A) * R) * d :=
        Nat.mul_le_mul_right d hunit
      _ = ((V - A) * d) * R := by ac_rfl
  have hsubtract :
      (((V - A) * d - 1) * R) + R =
        ((V - A) * d) * R := by
    calc
      (((V - A) * d - 1) * R) + R =
          (((V - A) * d - 1) + 1) * R := by
        rw [Nat.add_mul, Nat.one_mul]
      _ = ((V - A) * d) * R := by
        rw [Nat.sub_add_cancel (by omega : 1 ≤ (V - A) * d)]
  omega

/-- For the large-width ledger, the conservative reserve
3 A(A+1) works as soon as d >= 3 and V <= 2(A+1). -/
private theorem renewalBankReserveLarge (A V d : Nat)
    (hmargin : A < V)
    (hupper : V ≤ 2 * (A + 1))
    (hd : 3 ≤ d) :
    A * V * d ≤
      ((V - A) * d - 1) * (3 * A * (A + 1)) := by
  have hsource :
      A * V * d ≤ (A * (2 * (A + 1))) * d :=
    Nat.mul_le_mul_right d (Nat.mul_le_mul_left A hupper)
  have hgap : 1 ≤ V - A := by omega
  have hgapd : d ≤ (V - A) * d := by
    simpa only [Nat.one_mul] using
      (Nat.mul_le_mul_right d hgap)
  have hsub : d - 1 ≤ (V - A) * d - 1 := by omega
  have hcoeff : 2 * d ≤ 3 * (d - 1) := by omega
  have hfactor := Nat.mul_le_mul_right (A * (A + 1)) hcoeff
  have hlast := Nat.mul_le_mul_right (3 * A * (A + 1)) hsub
  calc
    A * V * d ≤ (A * (2 * (A + 1))) * d := hsource
    _ = (2 * d) * (A * (A + 1)) := by ac_rfl
    _ ≤ (3 * (d - 1)) * (A * (A + 1)) := hfactor
    _ = (d - 1) * (3 * A * (A + 1)) := by ac_rfl
    _ ≤ ((V - A) * d - 1) * (3 * A * (A + 1)) := hlast

/-- F.35, for s >= 17: the selected pin is the first power
of two at or above A_s+1, and is strictly below 2(A_s+1). -/
private theorem renewalBankLargePinMargins (s : Nat)
    (hs : 17 ≤ s) :
    557 * s + 119981 < 2 ^ kappaDot s ∧
      2 ^ kappaDot s < 2 * (557 * s + 119982) := by
  have htwo : s ≠ 2 := by omega
  have hthree : s ≠ 3 := by omega
  have hfour : s ≠ 4 := by omega
  have hfive : s ≠ 5 := by omega
  have hsmall : ¬ s ≤ 5 := by omega
  have hsix : s ≠ 6 := by omega
  have hkappa :
      kappaDot s = ceilLogTwo (557 * s + 119982) := by
    simp [kappaDot, htwo, hthree, hfour, hfive, hsmall, hsix]
  have hspec := ceilLogTwo_spec (557 * s + 119982)
    (by omega : 2 ≤ 557 * s + 119982)
  have hpos : 1 ≤ ceilLogTwo (557 * s + 119982) := by
    have h := ceilLogTwo_ge_two (557 * s + 119982)
      (by omega : 3 ≤ 557 * s + 119982)
    omega
  have hpower :
      (2 : Nat) ^ ceilLogTwo (557 * s + 119982) =
        2 * 2 ^ (ceilLogTwo (557 * s + 119982) - 1) := by
    calc
      (2 : Nat) ^ ceilLogTwo (557 * s + 119982) =
          2 ^ ((ceilLogTwo (557 * s + 119982) - 1) + 1) := by
        rw [Nat.sub_add_cancel hpos]
      _ = 2 * 2 ^ (ceilLogTwo (557 * s + 119982) - 1) := by
        rw [Nat.pow_succ]
        ac_rfl
  rw [hkappa]
  constructor
  · omega
  · rw [hpower]
    omega

/-- For spatial advice q>=80, the finite s=7..16 table has
strict integer coefficient surplus. For s>=17 the polynomial
ledger and F.35 supply a uniform reserve. -/
private theorem renewalBankSpatialReserveAtWidth (s q : Nat)
    (hs : 7 ≤ s) (hq : 80 ≤ q) :
    557 * s + 119981 < 2 ^ kappaDot s ∧
      (557 * s + 119981) * 2 ^ kappaDot s * 2 ^ q ≤
        ((2 ^ kappaDot s - (557 * s + 119981)) *
          2 ^ q - 1) * (headlineLargeLedger s).2.1 := by
  by_cases hsmall : s ≤ 16
  · have hfinite :
        ∀ i : Fin 17, 7 ≤ i.val →
          (557 * i.val + 119981 < 2 ^ kappaDot i.val) ∧
          ((557 * i.val + 119981) * 2 ^ kappaDot i.val <
            (2 ^ kappaDot i.val - (557 * i.val + 119981)) *
              (headlineLargeLedger i.val).2.1) ∧
          (headlineLargeLedger i.val).2.1 ≤ 2 ^ 24 := by
      decide +kernel
    have hbound : s < 17 := by omega
    obtain ⟨hmargin, hslack, hRsmall⟩ :=
      hfinite ⟨s, hbound⟩ hs
    have hp := Nat.pow_le_pow_right
      (by omega : 0 < (2 : Nat)) (by omega : 24 ≤ q)
    have hR : (headlineLargeLedger s).2.1 ≤ 2 ^ q :=
      Nat.le_trans hRsmall hp
    exact ⟨hmargin,
      renewalBankReserveFromSlack
        (557 * s + 119981) (2 ^ kappaDot s)
        (headlineLargeLedger s).2.1 (2 ^ q)
        hmargin hslack hR⟩
  · have htail : 17 ≤ s := by omega
    have hpin := renewalBankLargePinMargins s htail
    have hR :
        (headlineLargeLedger s).2.1 =
          3 * (557 * s + 119981) * (557 * s + 119982) := by
      simp [headlineLargeLedger, hsmall]
    have hqpow := Nat.pow_le_pow_right
      (by omega : 0 < (2 : Nat)) (by omega : 2 ≤ q)
    have hfour : (2 : Nat) ^ 2 = 4 := by decide
    have hd : 3 ≤ 2 ^ q := by omega
    constructor
    · exact hpin.1
    · rw [hR]
      exact renewalBankReserveLarge
        (557 * s + 119981) (2 ^ kappaDot s) (2 ^ q)
        hpin.1 (Nat.le_of_lt hpin.2) hd

/-- F.7/F.34/F.35 and the chosen F.10/F.36/F.37 renewal ledger:
both exact arithmetic conjuncts of RootedReferenceRealization
hold on the spatial (BANK) compiler branch. -/
theorem renewalBankSpatialMargins (n : Nat)
    (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) :
    renewalBankReferenceCeiling n <
        2 ^ (compileAdvice (ceilLogTwo n)).kappa ∧
      renewalBankReferenceCeiling n *
          2 ^ (compileAdvice (ceilLogTwo n)).kappa *
          2 ^ ceilLogTwo n ≤
        ((2 ^ (compileAdvice (ceilLogTwo n)).kappa -
            renewalBankReferenceCeiling n) *
          2 ^ ceilLogTwo n - 1) * headlineRenewalRate n := by
  have hq : 80 ≤ ceilLogTwo n := by
    change decide (ceilLogTwo n ≤ qStar) = false at hbank
    have hnot := of_decide_eq_false hbank
    have hstar : qStar = 79 := rfl
    omega
  have hqspec := (ceilLogTwo_spec (ceilLogTwo n)
    (by omega : 2 ≤ ceilLogTwo n)).2
  have hseven : 7 ≤ ceilLogTwo (ceilLogTwo n) := by
    by_cases hsix : ceilLogTwo (ceilLogTwo n) ≤ 6
    · have hp := Nat.pow_le_pow_right
        (by omega : 0 < (2 : Nat)) hsix
      have h64 : (2 : Nat) ^ 6 = 64 := by decide
      omega
    · omega
  have hnot32 : ¬ ceilLogTwo n ≤ 32 := by omega
  have hnot6 : ceilLogTwo (ceilLogTwo n) ≠ 6 := by omega
  have hmax :
      max 2 (ceilLogTwo (ceilLogTwo n)) =
        ceilLogTwo (ceilLogTwo n) := by omega
  have hA :
      renewalBankReferenceCeiling n =
        557 * ceilLogTwo (ceilLogTwo n) + 119981 := by
    simp [renewalBankReferenceCeiling, headlineReferenceRate,
      hnot32, hnot6]
  have hkappa :
      (compileAdvice (ceilLogTwo n)).kappa =
        kappaDot (ceilLogTwo (ceilLogTwo n)) := by
    change productionKappa (ceilLogTwo n) =
      kappaDot (ceilLogTwo (ceilLogTwo n))
    simp [productionKappa, paddedS, sourceTOfQ,
      hnot32, hmax]
  have hR :
      headlineRenewalRate n =
        (headlineLargeLedger (ceilLogTwo (ceilLogTwo n))).2.1 := by
    simp [headlineRenewalRate, headlineSelectedLedger, hnot32]
  have hband := renewalBankSpatialReserveAtWidth
    (ceilLogTwo (ceilLogTwo n)) (ceilLogTwo n) hseven hq
  simpa only [hA, hkappa, hR] using hband

/-- An exact clock producer for the decorated BANK reference.
Its five premises are the paper's sigma_B, sigma_G, sigma_1,
sigma_p, and prepared-to-generated substage estimates on the
same valid-reference transition. None is silently transferred
from a frozen or physically unmasked process. -/
theorem renewalBankReferenceClockOfStages {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (rooted inheritedGone grantFree singleton prepared :
      (bankValidRootedReferenceData ring hbank).Reference → Prop)
    (hstart : ∀ seed : RootedSeed ring,
      ¬ headlineGeneratedTarget ring seed.val →
        rooted ((bankValidRootedReferenceData ring hbank).referenceStart seed))
    (hOld : StageInheritedAuthorityExtinction
      (bankValidRootedReferenceData ring hbank).referenceNext
      rooted inheritedGone (ceilLogTwo n))
    (hDrain : StageReferenceGrantDrain
      (bankValidRootedReferenceData ring hbank).referenceNext
      inheritedGone grantFree)
    (hSingle : StageReferenceSingleton
      (bankValidRootedReferenceData ring hbank).referenceNext
      grantFree singleton)
    (hPrep : StageReferencePreparation
      (bankValidRootedReferenceData ring hbank).referenceNext
      singleton prepared)
    (hFinish : StageReferenceGeneratedFinish
      (bankValidRootedReferenceData ring hbank).referenceNext
      prepared
      (bankValidRootedReferenceData ring hbank).referenceStop
      (headlineReferenceFinishRate (ceilLogTwo n))) :
    ReferenceClock ring (bankValidRootedReferenceData ring hbank)
      (renewalBankReferenceCeiling n) := by
  have hthree : 3 ≤ ceilLogTwo n := ceilLogTwo_ge_three n hn
  have hstages := headlineReferenceStagesCompose
    (bankValidRootedReferenceData ring hbank).referenceNext
    rooted inheritedGone grantFree singleton prepared
    (bankValidRootedReferenceData ring hbank).referenceStop
    (ceilLogTwo n) hthree (by omega : 0 < n)
    hOld hDrain hSingle hPrep hFinish
  intro seed hnot T
  exact (UniformFirstHit.expectedHittingTimeAtMost_iff_cost
    (bankValidRootedReferenceData ring hbank).referenceNext
    (bankValidRootedReferenceData ring hbank).referenceStop
    (by omega : 0 < n)
    ((bankValidRootedReferenceData ring hbank).referenceStart seed)
    (renewalBankReferenceCeiling n * n ^ 2)).1
    (hstages _ (hstart seed hnot)) T

/-- The precise remaining two-input realization interface.
Domination, charge and rarity are proved; the arithmetic margins
are above. Causal retry coverage and the own-reference clock
are kept as distinct, explicit hypotheses. -/
theorem renewalBankSpatialRealizationOfCoverageAndClock {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hcoverage : ReferenceRetryCoverage ring hn
      (bankValidRootedReferenceData ring hbank))
    (hclock : ReferenceClock ring
      (bankValidRootedReferenceData ring hbank)
      (renewalBankReferenceCeiling n)) :
    RootedReferenceRealization ring hn := by
  have hmargins := renewalBankSpatialMargins n hn hbank
  refine ⟨bankValidRootedReferenceData ring hbank,
    renewalBankReferenceCeiling n, ?_, hmargins.1, hmargins.2⟩
  exact {
    domination := bankValidReferenceAttemptDomination ring hn hbank
    coverage := hcoverage
    charge := bankValidReferenceOriginCharge ring hbank
    rarity := renewalBankValidRarityOfOriginPotential hn ring hbank
    clock := hclock }

/-- Thus the only missing BANK-input predicates for the physical
StageRootedRenewalCost are retry coverage and reference clock. -/
theorem renewalBankSpatialStageCostOfCoverageAndClock {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hcoverage : ReferenceRetryCoverage ring hn
      (bankValidRootedReferenceData ring hbank))
    (hclock : ReferenceClock ring
      (bankValidRootedReferenceData ring hbank)
      (renewalBankReferenceCeiling n)) :
    StageRootedRenewalCost ring := by
  exact stageRootedRenewalCost_of_referenceRealization ring hn
    (renewalBankSpatialRealizationOfCoverageAndClock
      ring hn hbank hcoverage hclock)

end L3.HeadlineRenewal


/-!
Native projection and reference-stage transfer bridges.

The NativeLift and ReferencePreparation D.21/H.1 clocks have not been
imported in the source. Their bridge premises are left explicit.
This file asserts neither a pure-native clock for the BANK reference
nor a closed grant-free/inherited-authority invariant.
-/

namespace L3.HeadlineRenewal

open Classical
open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree

set_option autoImplicit false
set_option Elab.async false

/-- Masking does not change the native coordinates at either endpoint.
The fresh-grant/no-grant branch changes only request/grant fields. -/
private theorem renewalBankMaskedNativePairFrame
    (c : Compiled) (suppress : Bool) (x y : Agent c) :
    (renewalMaskedPair c suppress x y).1.certNative =
      (transition c x y).1.certNative ∧
    (renewalMaskedPair c suppress x y).2.certNative =
      (transition c x y).2.certNative := by
  cases suppress <;> exact ⟨rfl, rfl⟩

/-- Rewriting both branches of a mapped `if` on a plain function type;
used where the configuration type blocks `rw [if_pos]`. -/
private theorem renewalBankIteMapPos {α β : Type} (f : α → β)
    (c : Prop) [Decidable c] (x y z : α) (hc : c)
    (h : f x = f y) :
    f (if c then x else z) = f (if c then y else z) := by
  rw [if_pos hc, if_pos hc]
  exact h

private theorem renewalBankIteMapNeg {α β : Type} (f : α → β)
    (c : Prop) [Decidable c] (x y z : α) (hc : ¬ c) :
    f (if c then x else z) = f (if c then y else z) := by
  rw [if_neg hc, if_neg hc]

/-- A full selected-edge update, including fresh suppression,
has the same native projection as the actual unmasked step.
This is a projection statement, not equality of full configurations. -/
theorem renewalBankMaskedNativeFrame {n : Nat}
    (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (e : Fin n) (suppress : Bool) :
    nativeProjection (renewalMaskedStep ring C e suppress) =
      nativeProjection (headlinePhysicalNext ring C e) := by
  cases suppress with
  | false =>
      rw [renewalMaskedStepOff]
  | true =>
      have hframe :
          nativeProjection (renewalMaskedStep ring C e true) =
            nativeProjection (renewalMaskedStep ring C e false) := by
        funext i
        change
          (if i = e then
             (renewalMaskedPair (compileAdvice (ceilLogTwo n)) true
               (C e) (C (ring.rightNeighbor e))).1
           else if i = ring.rightNeighbor e then
             (renewalMaskedPair (compileAdvice (ceilLogTwo n)) true
               (C e) (C (ring.rightNeighbor e))).2
           else C i).certNative =
          (if i = e then
             (renewalMaskedPair (compileAdvice (ceilLogTwo n)) false
               (C e) (C (ring.rightNeighbor e))).1
           else if i = ring.rightNeighbor e then
             (renewalMaskedPair (compileAdvice (ceilLogTwo n)) false
               (C e) (C (ring.rightNeighbor e))).2
           else C i).certNative
        by_cases he : i = e
        · rw [if_pos he, if_pos he]
          exact (renewalBankMaskedNativePairFrame
            (compileAdvice (ceilLogTwo n)) true
            (C e) (C (ring.rightNeighbor e))).1
        · rw [if_neg he, if_neg he]
          by_cases hj : i = ring.rightNeighbor e
          · refine renewalBankIteMapPos _ _ _ _ _ hj ?_
            exact (renewalBankMaskedNativePairFrame
              (compileAdvice (ceilLogTwo n)) true
              (C e) (C (ring.rightNeighbor e))).2
          · exact renewalBankIteMapNeg _ _ _ _ _ hj
      rw [renewalMaskedStepOff] at hframe
      exact hframe

/-- The decorated BANK reference has the physical native projection
even on a selected edge that suppresses a genuinely fresh grant. -/
theorem renewalBankReferenceNativeFrame {n : Nat}
    (ring : DirectedRing n) (r : RenewalBankReference n)
    (e : Fin n) :
    nativeProjection (renewalBankNext ring r e).1 =
      nativeProjection (headlinePhysicalNext ring r.1 e) := by
  exact renewalBankMaskedNativeFrame ring r.1 e
    (renewalBankCut ring r.1 r.2 e)

/-- The exact single-edge remaining premise for a nativeE transfer.
No-grant (or no-FIRE) hypotheses must justify the RHS separately. -/
theorem renewalBankNativeStepOfPhysicalNativeStep {n : Nat}
    (ring : DirectedRing n) (r : RenewalBankReference n)
    (e : Fin n)
    (hphysical :
      nativeProjection (headlinePhysicalNext ring r.1 e) =
        nativeE ring (nativeProjection r.1) e) :
    nativeProjection (renewalBankNext ring r e).1 =
      nativeE ring (nativeProjection r.1) e := by
  exact (renewalBankReferenceNativeFrame ring r e).trans hphysical

/-- Native view on the exact valid BANK reference subtype. -/
def renewalBankValidNativeView {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : (bankValidRootedReferenceData ring hbank).Reference) :
    TripleNativeState n :=
  nativeProjection z.val.1

/-- A BANK valid-reference step has the same native projection as
the actual unmasked Cartesian service, without any no-FIRE premise. -/
theorem renewalBankValidNativeFrame {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : (bankValidRootedReferenceData ring hbank).Reference)
    (e : Fin n) :
    renewalBankValidNativeView ring hbank
        ((bankValidRootedReferenceData ring hbank).referenceNext z e) =
      nativeProjection (headlinePhysicalNext ring z.val.1 e) := by
  change nativeProjection (renewalBankNext ring z.val e).1 =
    nativeProjection (headlinePhysicalNext ring z.val.1 e)
  exact renewalBankReferenceNativeFrame ring z.val e

/-- Native equality along every scheduler word of a closed reference
subclass. This does not grant closure of that subclass automatically. -/
theorem renewalBankValidProjectedCostWord {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (P : TripleNativeState n → Prop)
    (H : (bankValidRootedReferenceData ring hbank).Reference → Prop)
    (hstep : ∀ z, H z → ∀ e : Fin n,
      renewalBankValidNativeView ring hbank
        ((bankValidRootedReferenceData ring hbank).referenceNext z e) =
      nativeE ring (renewalBankValidNativeView ring hbank z) e)
    (hclosed : ∀ z, H z → ∀ e : Fin n,
      H ((bankValidRootedReferenceData ring hbank).referenceNext z e)) :
    ∀ word : List (Fin n),
      ∀ z : (bankValidRootedReferenceData ring hbank).Reference,
      H z →
      costWord
          (bankValidRootedReferenceData ring hbank).referenceNext
          (fun a => P (renewalBankValidNativeView ring hbank a))
          z word =
        costWord (nativeE ring) P
          (renewalBankValidNativeView ring hbank z) word := by
  intro word
  induction word with
  | nil =>
      intro z _
      rfl
  | cons e tail ih =>
      intro z hz
      by_cases hp : P (renewalBankValidNativeView ring hbank z)
      · rw [costWord_terminal _ _ z hp (e :: tail),
          costWord_terminal _ _
            (renewalBankValidNativeView ring hbank z) hp (e :: tail)]
      · rw [renewalWordCostCons _ _ z e tail hp,
          renewalWordCostCons _ _
            (renewalBankValidNativeView ring hbank z) e tail hp]
        have htail := ih
          ((bankValidRootedReferenceData ring hbank).referenceNext z e)
          (hclosed z hz e)
        rw [hstep z hz e] at htail
        exact congrArg (fun v : Nat => 1 + v) htail

/-- Equality of *finite-horizon numerators*, not merely an equality
of unnormalized expectations, on the same actual iid scheduler. -/
theorem renewalBankValidProjectedCostNumerator {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (P : TripleNativeState n → Prop)
    (H : (bankValidRootedReferenceData ring hbank).Reference → Prop)
    (hstep : ∀ z, H z → ∀ e : Fin n,
      renewalBankValidNativeView ring hbank
        ((bankValidRootedReferenceData ring hbank).referenceNext z e) =
      nativeE ring (renewalBankValidNativeView ring hbank z) e)
    (hclosed : ∀ z, H z → ∀ e : Fin n,
      H ((bankValidRootedReferenceData ring hbank).referenceNext z e))
    (z : (bankValidRootedReferenceData ring hbank).Reference)
    (hz : H z) (T : Nat) :
    costNumerator
        (bankValidRootedReferenceData ring hbank).referenceNext
        (fun a => P (renewalBankValidNativeView ring hbank a)) z T =
      costNumerator (nativeE ring) P
        (renewalBankValidNativeView ring hbank z) T := by
  change Prob.scheduleSum n T
      (costWord (bankValidRootedReferenceData ring hbank).referenceNext
        (fun a => P (renewalBankValidNativeView ring hbank a)) z) =
    Prob.scheduleSum n T
      (costWord (nativeE ring) P
        (renewalBankValidNativeView ring hbank z))
  have hwords :
      (costWord (bankValidRootedReferenceData ring hbank).referenceNext
          (fun a => P (renewalBankValidNativeView ring hbank a)) z) =
        (costWord (nativeE ring) P
          (renewalBankValidNativeView ring hbank z)) := by
    funext word
    exact renewalBankValidProjectedCostWord
      ring hbank P H hstep hclosed word z hz
  rw [hwords]

/-- An exact stage-sigma_1 transfer interface. The numerical D.21
clock is to be supplied for the native view, and its closed nativeE
simulation must be proved for the same BANK reference class H. -/
theorem renewalBankProjectedSingletonStageOfNativeCost {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (P : TripleNativeState n → Prop)
    (H : (bankValidRootedReferenceData ring hbank).Reference → Prop)
    (hstep : ∀ z, H z → ∀ e : Fin n,
      renewalBankValidNativeView ring hbank
        ((bankValidRootedReferenceData ring hbank).referenceNext z e) =
      nativeE ring (renewalBankValidNativeView ring hbank z) e)
    (hclosed : ∀ z, H z → ∀ e : Fin n,
      H ((bankValidRootedReferenceData ring hbank).referenceNext z e))
    (hnative : ∀ z, H z → ∀ T,
      costNumerator (nativeE ring) P
        (renewalBankValidNativeView ring hbank z) T ≤
      n ^ T * (4917 * n ^ 2)) :
    StageReferenceSingleton
      (bankValidRootedReferenceData ring hbank).referenceNext
      H (fun z => P (renewalBankValidNativeView ring hbank z)) := by
  intro z hz
  apply (UniformFirstHit.expectedHittingTimeAtMost_iff_cost
    (bankValidRootedReferenceData ring hbank).referenceNext
    (fun a => P (renewalBankValidNativeView ring hbank a))
    (by omega : 0 < n) z (4917 * n ^ 2)).2
  intro T
  rw [renewalBankValidProjectedCostNumerator
    ring hbank P H hstep hclosed z hz T]
  exact hnative z hz T

/-- H.1's doubled 10n²+n numerator is at most the paper 6n²
budget; this preserves the unrounded incident-edge contribution. -/
theorem renewalBankDoubledPreparationSix
    (n T cost : Nat) (hn : 1 ≤ n)
    (h : 2 * cost ≤ n ^ T * (10 * n ^ 2 + n)) :
    cost ≤ n ^ T * (6 * n ^ 2) := by
  have hsquare : n ≤ n ^ 2 := by
    calc
      n = n * 1 := by omega
      _ ≤ n * n := Nat.mul_le_mul_left n hn
      _ = n ^ 2 := by rw [Nat.pow_two]
  have hcoeff : 10 * n ^ 2 + n ≤ 12 * n ^ 2 := by omega
  have hscaled : 2 * cost ≤ 2 * (n ^ T * (6 * n ^ 2)) := by
    calc
      2 * cost ≤ n ^ T * (10 * n ^ 2 + n) := h
      _ ≤ n ^ T * (12 * n ^ 2) :=
        Nat.mul_le_mul_left (n ^ T) hcoeff
      _ = n ^ T * ((2 * 6) * n ^ 2) := by rfl
      _ = 2 * (n ^ T * (6 * n ^ 2)) := by ac_rfl
  exact Nat.le_of_mul_le_mul_left hscaled (by omega : 0 < (2 : Nat))

/-- Exact sigma_p transfer interface for the genuinely native H.1
target. Candidate-zero and decorated-authority predicates are not
inferred from this native projection alone. -/
theorem renewalBankProjectedPreparationStageOfNativeDoubled {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (P : TripleNativeState n → Prop)
    (H : (bankValidRootedReferenceData ring hbank).Reference → Prop)
    (hstep : ∀ z, H z → ∀ e : Fin n,
      renewalBankValidNativeView ring hbank
        ((bankValidRootedReferenceData ring hbank).referenceNext z e) =
      nativeE ring (renewalBankValidNativeView ring hbank z) e)
    (hclosed : ∀ z, H z → ∀ e : Fin n,
      H ((bankValidRootedReferenceData ring hbank).referenceNext z e))
    (hnative : ∀ z, H z → ∀ T,
      2 * costNumerator (nativeE ring) P
        (renewalBankValidNativeView ring hbank z) T ≤
      n ^ T * (10 * n ^ 2 + n)) :
    StageReferencePreparation
      (bankValidRootedReferenceData ring hbank).referenceNext
      H (fun z => P (renewalBankValidNativeView ring hbank z)) := by
  intro z hz
  apply (UniformFirstHit.expectedHittingTimeAtMost_iff_cost
    (bankValidRootedReferenceData ring hbank).referenceNext
    (fun a => P (renewalBankValidNativeView ring hbank a))
    (by omega : 0 < n) z (6 * n ^ 2)).2
  intro T
  rw [renewalBankValidProjectedCostNumerator
    ring hbank P H hstep hclosed z hz T]
  exact renewalBankDoubledPreparationSix n T
    (costNumerator (nativeE ring) P
      (renewalBankValidNativeView ring hbank z) T)
    (by omega : 1 ≤ n) (hnative z hz T)

end L3.HeadlineRenewal
