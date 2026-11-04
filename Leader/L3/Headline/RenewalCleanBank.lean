import Leader.L3.Bank.FinishCleanWord
import Leader.L3.Headline.Clean
import Leader.L3.Grant.DrainStageTransfer
import Leader.L3.Bank.WindowInv

/-!
R14 on the clean target, BANK branch.

Part A.  The rooted retry shell and the renewal cost theorem
(`HeadlineRenewal.lean` lines 23-145 and 245-500) are restated for an
arbitrary terminal class `G` (suffix `At`).  The proofs are the installed
ones; none of them uses a property of the old target beyond its role as
the stop of the trial and of the reference.

Part B.  The valid BANK reference with the same physical next, masked
coupling, memory, spawn and win, and `referenceStop := Gclean`
(`bankCleanRootedReferenceData`).  Domination, origin charge and origin
rarity are re-proved on it by the installed arguments (rarity and the
source witness never read the stop).  The clock comes from the installed
sigma_G / sigma_1 / sigma_p stages and `bankCleanFinishReference`; retry
coverage from the installed K-head threshold through a copy of
`BankRetryCoverage.lean`.
-/

namespace L3.HeadlineRenewalCleanBank

open L3
open L3.HeadlineRenewal
open L3.RenewalReferenceClock
open L3.GrantDrainEntrance
open L3.BankRetryCoverage
open Classical
open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree
open PPL.Convergence.LDLocal (AttemptNode RetryKernel retryCount)

set_option autoImplicit false
set_option Elab.async false

/-! ## Part A: the renewal shell for an arbitrary terminal class -/

/-- The physical target wins a tie with the observed retry cut. -/
noncomputable def rootedTrialStepAt {n : Nat} {H : Type}
    (ring : DirectedRing n) (G : HeadlineConfiguration n → Prop) (hn : 5 <= n)
    (advance : RootedSeed ring × H -> Fin n -> H)
    (cut : RootedSeed ring × H -> Fin n -> Bool)
    (a : RootedSeed ring × H) (e : Fin n) :
    AttemptNode (RootedSeed ring × H) (RootedSeed ring) := by
  classical
  exact if G
      (rootedSuccessor ring hn a.1 e).val then
    .success
  else if cut a e = true then
    .retry (rootedSuccessor ring hn a.1 e)
  else
    .active (rootedSuccessor ring hn a.1 e, advance a e)

/-- All completed retries are valid nonterminal restarts. -/
theorem rootedTrialRetryNonterminalAt {n : Nat} {H : Type}
    (ring : DirectedRing n) (G : HeadlineConfiguration n → Prop) (hn : 5 <= n)
    (advance : RootedSeed ring × H -> Fin n -> H)
    (cut : RootedSeed ring × H -> Fin n -> Bool)
    (a : RootedSeed ring × H) (e : Fin n)
    (seed : RootedSeed ring)
    (hstep : rootedTrialStepAt ring G hn advance cut a e = .retry seed) :
    ¬ G seed.val := by
  classical
  unfold rootedTrialStepAt at hstep
  split at hstep
  · cases hstep
  · rename_i hnot
    split at hstep
    · cases hstep
      exact hnot
    · cases hstep

noncomputable def rootedTrialKernelAt {n : Nat} {H : Type}
    (ring : DirectedRing n) (G : HeadlineConfiguration n → Prop) (hn : 5 <= n)
    (initial : RootedSeed ring -> H)
    (advance : RootedSeed ring × H -> Fin n -> H)
    (cut : RootedSeed ring × H -> Fin n -> Bool) :
    RetryKernel (RootedSeed ring × H) (RootedSeed ring) n :=
  { start := fun seed => (seed, initial seed)
    step := rootedTrialStepAt ring G hn advance cut
    valid := fun seed => ¬ G seed.val
    retry_valid := by
      intro a e seed hstep
      exact rootedTrialRetryNonterminalAt ring G hn advance cut a e seed hstep }

/-- No word-safety assertion is required for physical retry fidelity. -/
theorem rootedTrialSimulationAt {n : Nat} {H : Type}
    (ring : DirectedRing n) (G : HeadlineConfiguration n → Prop) (hn : 5 <= n)
    (initial : RootedSeed ring -> H)
    (advance : RootedSeed ring × H -> Fin n -> H)
    (cut : RootedSeed ring × H -> Fin n -> Bool) :
    Prob.RetrySimulation (rootedTrialKernelAt ring G hn initial advance cut)
      (headlinePhysicalNext ring) (G)
      (rootedTrialRelation (H := H) ring) := by
  classical
  intro C a hrel hnot e
  change a.1.val = C at hrel
  subst hrel
  cases hs : (rootedTrialKernelAt ring G hn initial advance cut).step a e with
  | success =>
      have hs' : rootedTrialStepAt ring G hn advance cut a e = .success := hs
      unfold rootedTrialStepAt at hs'
      split at hs'
      · rename_i hhit
        exact hhit
      · split at hs' <;> cases hs'
  | active b =>
      have hs' : rootedTrialStepAt ring G hn advance cut a e = .active b := hs
      unfold rootedTrialStepAt at hs'
      split at hs'
      · cases hs'
      · split at hs'
        · cases hs'
        · cases hs'
          rfl
  | retry seed =>
      have hs' : rootedTrialStepAt ring G hn advance cut a e = .retry seed := hs
      unfold rootedTrialStepAt at hs'
      split at hs'
      · cases hs'
      · split at hs'
        · cases hs'
          rfl
        · cases hs'

noncomputable def referenceKernelAt {n : Nat}
    (ring : DirectedRing n) (G : HeadlineConfiguration n → Prop) (hn : 5 <= n)
    (D : RootedReferenceData ring) :
    RetryKernel (RootedSeed ring × D.Memory) (RootedSeed ring) n :=
  rootedTrialKernelAt ring G hn D.initialMemory D.memoryNext D.cut

/-- Wordwise min(reference hit, divergence) domination. -/
def ReferenceAttemptDominationAt {n : Nat}
    (ring : DirectedRing n) (G : HeadlineConfiguration n → Prop) (hn : 5 <= n)
    (D : RootedReferenceData ring) : Prop :=
  ∀ seed : RootedSeed ring,
    ¬ G seed.val ->
    ∀ word : List (Fin n),
      costWord (Prob.attemptStepper (referenceKernelAt ring G hn D))
        (fun z => Prob.attemptGood z ∨ Prob.attemptFail z)
        (.active ((referenceKernelAt ring G hn D).start seed)) word <=
      costWord D.referenceNext D.referenceStop (D.referenceStart seed) word

/-- First uncompleted concrete event-attribution obligation. -/
def ReferenceRetryCoverageAt {n : Nat}
    (ring : DirectedRing n) (G : HeadlineConfiguration n → Prop) (hn : 5 <= n)
    (D : RootedReferenceData ring) : Prop :=
  ∀ seed : RootedSeed ring,
    ¬ G seed.val ->
    ∀ word : List (Fin n),
      Prob.retryFirstWord (referenceKernelAt ring G hn D)
        (.active ((referenceKernelAt ring G hn D).start seed)) word <=
      Prob.originEventWord D.referenceNext D.referenceStop D.spawn D.win
        (D.referenceStart seed) word

def ReferenceOriginChargeAt {n : Nat}
    (ring : DirectedRing n) (G : HeadlineConfiguration n → Prop) (D : RootedReferenceData ring) : Prop :=
  ∀ seed : RootedSeed ring,
    ¬ G seed.val ->
    ∀ word : List (Fin n),
      Prob.originsWord D.referenceNext D.referenceStop D.spawn
        (D.referenceStart seed) word <=
      costWord D.referenceNext D.referenceStop (D.referenceStart seed) word + n

def ReferenceClockAt {n : Nat}
    (ring : DirectedRing n) (G : HeadlineConfiguration n → Prop) (D : RootedReferenceData ring)
    (A : Nat) : Prop :=
  ∀ seed : RootedSeed ring,
    ¬ G seed.val ->
    ∀ T : Nat,
      costNumerator D.referenceNext D.referenceStop
        (D.referenceStart seed) T <= n ^ T * (A * n ^ 2)

structure RootedReferenceCertificateAt {n : Nat}
    (ring : DirectedRing n) (G : HeadlineConfiguration n → Prop) (hn : 5 <= n)
    (D : RootedReferenceData ring) (A k : Nat) : Prop where
  domination : ReferenceAttemptDominationAt ring G hn D
  coverage : ReferenceRetryCoverageAt ring G hn D
  charge : ReferenceOriginChargeAt ring G D
  rarity : ReferenceOriginRarity ring D k
  clock : ReferenceClockAt ring G D A

private theorem wordSumMonotoneAt {n : Nat} (T : Nat)
    (f g : List (Fin n) -> Nat)
    (h : ∀ word : List (Fin n), f word <= g word) :
    Prob.scheduleSum n T f <= Prob.scheduleSum n T g := by
  change FixedSpanRenewalPayload.wordSum n T f <=
    FixedSpanRenewalPayload.wordSum n T g
  rw [← FixedSpanRenewalPayload.rawWord_sum n T f,
    ← FixedSpanRenewalPayload.rawWord_sum n T g]
  exact ofFn_sum_le _ _ (fun i => h _)

theorem referenceAttemptCostAt {n : Nat}
    (ring : DirectedRing n) (G : HeadlineConfiguration n → Prop) (hn : 5 <= n)
    (D : RootedReferenceData ring)
    (h : ReferenceAttemptDominationAt ring G hn D)
    (seed : RootedSeed ring)
    (hnot : ¬ G seed.val) (T : Nat) :
    costNumerator (Prob.attemptStepper (referenceKernelAt ring G hn D))
      (fun z => Prob.attemptGood z ∨ Prob.attemptFail z)
      (.active ((referenceKernelAt ring G hn D).start seed)) T <=
    costNumerator D.referenceNext D.referenceStop
      (D.referenceStart seed) T := by
  change Prob.scheduleSum n T
      (costWord (Prob.attemptStepper (referenceKernelAt ring G hn D))
        (fun z => Prob.attemptGood z ∨ Prob.attemptFail z)
        (.active ((referenceKernelAt ring G hn D).start seed))) <=
    Prob.scheduleSum n T
      (costWord D.referenceNext D.referenceStop (D.referenceStart seed))
  exact wordSumMonotoneAt T _ _ (h seed hnot)

theorem referenceRetryCountAt {n : Nat}
    (ring : DirectedRing n) (G : HeadlineConfiguration n → Prop) (hn : 5 <= n)
    (D : RootedReferenceData ring)
    (h : ReferenceRetryCoverageAt ring G hn D)
    (seed : RootedSeed ring)
    (hnot : ¬ G seed.val) (T : Nat) :
    retryCount (referenceKernelAt ring G hn D)
      (.active ((referenceKernelAt ring G hn D).start seed)) T <=
    Prob.originEventNumerator D.referenceNext D.referenceStop D.spawn D.win
      (D.referenceStart seed) T := by
  rw [Prob.retryCount_eq_wordSum]
  exact wordSumMonotoneAt T _ _ (h seed hnot)

/-- F.1 followed by F.2, without origin/clock independence. -/
theorem referenceOriginMassAt {n : Nat}
    (ring : DirectedRing n) (G : HeadlineConfiguration n → Prop) (hn : 5 <= n)
    (D : RootedReferenceData ring) (A k : Nat)
    (h : RootedReferenceCertificateAt ring G hn D A k)
    (seed : RootedSeed ring)
    (hnot : ¬ G seed.val) (T : Nat) :
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

theorem referenceRetryMassAt {n : Nat}
    (ring : DirectedRing n) (G : HeadlineConfiguration n → Prop) (hn : 5 <= n)
    (D : RootedReferenceData ring) (A k : Nat)
    (h : RootedReferenceCertificateAt ring G hn D A k)
    (seed : RootedSeed ring)
    (hnot : ¬ G seed.val) (T : Nat) :
    (2 ^ k * 2 ^ ceilLogTwo n) *
      retryCount (referenceKernelAt ring G hn D)
        (.active ((referenceKernelAt ring G hn D).start seed)) T <=
    (A * 2 ^ ceilLogTwo n + 1) * n ^ T := by
  exact Nat.le_trans
    (Nat.mul_le_mul_left (2 ^ k * 2 ^ ceilLogTwo n)
      (referenceRetryCountAt ring G hn D h.coverage seed hnot T))
    (referenceOriginMassAt ring G hn D A k h seed hnot T)

theorem rootedCostFromReferenceAt {n : Nat}
    (ring : DirectedRing n) (G : HeadlineConfiguration n → Prop) (hn : 5 <= n)
    (D : RootedReferenceData ring) (A k R : Nat)
    (h : RootedReferenceCertificateAt ring G hn D A k)
    (hmargin : A < 2 ^ k)
    (hreserve : A * 2 ^ k * 2 ^ ceilLogTwo n <=
      ((2 ^ k - A) * 2 ^ ceilLogTwo n - 1) * R) :
    ∀ C : HeadlineConfiguration n, headlineRooted ring C ->
      ∀ T : Nat,
        costNumerator (headlinePhysicalNext ring)
          (G) C T <= n ^ T * (R * n ^ 2) := by
  classical
  have hpopulation := (ceilLogTwo_spec n (by omega)).2
  have hd : 1 < 2 ^ ceilLogTwo n := by omega
  have hnum : A * 2 ^ ceilLogTwo n + 1 <
      2 ^ k * 2 ^ ceilLogTwo n :=
    (renewalMarginFacts A (2 ^ k) (2 ^ ceilLogTwo n) hmargin hd).1
  have hsimulation :
      Prob.RetrySimulation (referenceKernelAt ring G hn D)
        (headlinePhysicalNext ring) (G)
        (rootedTrialRelation (H := D.Memory) ring) :=
    rootedTrialSimulationAt ring G hn D.initialMemory D.memoryNext D.cut
  have hattempt : ∀ seed : RootedSeed ring,
      (referenceKernelAt ring G hn D).valid seed -> ∀ T : Nat,
      costNumerator (Prob.attemptStepper (referenceKernelAt ring G hn D))
        (fun z => Prob.attemptGood z ∨ Prob.attemptFail z)
        (.active ((referenceKernelAt ring G hn D).start seed)) T <=
      n ^ T * (A * n ^ 2) := by
    intro seed hvalid T
    exact Nat.le_trans
      (referenceAttemptCostAt ring G hn D h.domination seed hvalid T)
      (h.clock seed hvalid T)
  have hretry : ∀ seed : RootedSeed ring,
      (referenceKernelAt ring G hn D).valid seed -> ∀ T : Nat,
      (2 ^ k * 2 ^ ceilLogTwo n) *
        retryCount (referenceKernelAt ring G hn D)
          (.active ((referenceKernelAt ring G hn D).start seed)) T <=
      (A * 2 ^ ceilLogTwo n + 1) * n ^ T := by
    intro seed hvalid T
    exact referenceRetryMassAt ring G hn D A k h seed hvalid T
  intro C hC T
  by_cases hterminal : G C
  · rw [costNumerator_terminal (headlinePhysicalNext ring)
      (G) C hterminal T]
    exact Nat.zero_le _
  · have hcost := Prob.costNumerator_renewal_le
      (headlinePhysicalNext ring) (G)
      (referenceKernelAt ring G hn D) (rootedTrialRelation (H := D.Memory) ring)
      hsimulation (A * n ^ 2) (A * 2 ^ ceilLogTwo n + 1)
      (2 ^ k * 2 ^ ceilLogTwo n) hnum hattempt hretry
      C (⟨C, hC⟩ : RootedSeed ring) hterminal rfl T
    exact Nat.le_trans hcost
      (Nat.mul_le_mul_left (n ^ T)
        (renewalPopulationCeiling A (2 ^ k) (2 ^ ceilLogTwo n) n R
          hmargin hd hreserve))

/-- The production pin is fixed. This is not a word-safety-only
    premise: the producer and reference clock obligations remain. -/
def RootedReferenceRealizationAt {n : Nat}
    (ring : DirectedRing n) (G : HeadlineConfiguration n → Prop) (hn : 5 <= n) : Prop :=
  ∃ (D : RootedReferenceData ring) (A : Nat),
    RootedReferenceCertificateAt ring G hn D A
      (compileAdvice (ceilLogTwo n)).kappa ∧
    A < 2 ^ (compileAdvice (ceilLogTwo n)).kappa ∧
    A * 2 ^ (compileAdvice (ceilLogTwo n)).kappa * 2 ^ ceilLogTwo n <=
      ((2 ^ (compileAdvice (ceilLogTwo n)).kappa - A) *
        2 ^ ceilLogTwo n - 1) * headlineRenewalRate n

/-! ## Part B: the valid BANK reference stopped at Gclean -/

/-- The reference stop at a terminal class `G` of the configuration.
Consumer: `bankCleanRootedReferenceData` and the clean copies. -/
def renewalBankStopAt {n : Nat} (G : HeadlineConfiguration n → Prop)
    (r : RenewalBankReference n) : Prop :=
  G r.1

/-- The valid BANK reference of `bankValidRootedReferenceData` with its
stop replaced by `Gclean`.  Consumer: `bankCleanRealization`. -/
def bankCleanRootedReferenceData {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) :
    RootedReferenceData ring :=
  { bankValidRootedReferenceData ring hbank with
    referenceStop := fun r =>
      renewalBankStopAt (headlineCleanTarget ring) r.val }

private theorem renewalWordCostConsClean {S : Type} {n : Nat}
    (next : S → Fin n → S) (P : S → Prop) (x : S)
    (e : Fin n) (word : List (Fin n)) (hx : ¬ P x) :
    costWord next P x (e :: word) =
      1 + costWord next P (next x e) word := by
  classical
  simp only [costWord, K2FiniteSafeEliminationExpected.rawCost, if_neg hx]

/-- Each stopped path allocates no more origins than paid services. -/
theorem renewalBankOriginsBudgetClean {n : Nat} (ring : DirectedRing n) :
    ∀ (word : List (Fin n)) (r : RenewalBankReference n),
      Prob.originsWord (renewalBankNext ring) (renewalBankStopAt (headlineCleanTarget ring))
        (renewalBankSpawn ring) r word ≤
      costWord (renewalBankNext ring) (renewalBankStopAt (headlineCleanTarget ring))
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
      by_cases hs : renewalBankStopAt (headlineCleanTarget ring) r
      · rw [Prob.originsWord, if_pos hs]
        exact Nat.zero_le _
      · have ht := ih (renewalBankNext ring r e)
        have hb := renewalBankSpawnLengthLeOne ring r e
        rw [Prob.originsWord, if_neg hs,
          renewalWordCostConsClean (renewalBankNext ring)
            (renewalBankStopAt (headlineCleanTarget ring)) r e word hs]
        omega

/-- The same physical-edge finite-word domination as SMALL. -/
theorem renewalBankAttemptWordClean {n : Nat} (ring : DirectedRing n)
    (hn : 5 ≤ n) :
    ∀ (word : List (Fin n))
      (a : RootedSeed ring × RenewalBankMemory n),
      ¬ headlineCleanTarget ring a.1.val →
      costWord
        (Prob.attemptStepper (rootedTrialKernelAt ring (headlineCleanTarget ring) hn
          (renewalBankInitialMemory ring)
          (renewalBankTrialAdvance ring)
          (renewalBankTrialCut ring)))
        (fun z => Prob.attemptGood z ∨ Prob.attemptFail z)
        (.active a) word ≤
      costWord (renewalBankNext ring) (renewalBankStopAt (headlineCleanTarget ring))
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
      have hrefnot : ¬ renewalBankStopAt (headlineCleanTarget ring) (a.1.val, a.2) := hnot
      rw [renewalWordCostConsClean _ _
          (AttemptNode.active a :
            AttemptNode (RootedSeed ring × RenewalBankMemory n)
              (RootedSeed ring)) e word hactive,
        renewalWordCostConsClean _ _ (a.1.val, a.2) e word hrefnot]
      change 1 + costWord _ _
          ((rootedTrialKernelAt ring (headlineCleanTarget ring) hn (renewalBankInitialMemory ring)
            (renewalBankTrialAdvance ring)
            (renewalBankTrialCut ring)).step a e) word ≤
        1 + costWord (renewalBankNext ring) (renewalBankStopAt (headlineCleanTarget ring))
          (renewalBankNext ring (a.1.val, a.2) e) word
      cases hs : (rootedTrialKernelAt ring (headlineCleanTarget ring) hn
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
          have hs' : rootedTrialStepAt ring (headlineCleanTarget ring) hn
              (renewalBankTrialAdvance ring) (renewalBankTrialCut ring)
              a e = .active b := hs
          unfold rootedTrialStepAt at hs'
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

/-- Cost of a valid run is exactly cost of its unrestricted
projection, with no conditional coupling assumption. -/
private theorem renewalBankValidCostProjectionClean {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) :
    ∀ (word : List (Fin n))
      (r : (bankCleanRootedReferenceData ring hbank).Reference),
      costWord
        (bankCleanRootedReferenceData ring hbank).referenceNext
        (bankCleanRootedReferenceData ring hbank).referenceStop r word =
      costWord (renewalBankNext ring) (renewalBankStopAt (headlineCleanTarget ring))
        r.val word := by
  classical
  intro word
  induction word with
  | nil =>
      intro r
      rfl
  | cons e word ih =>
      intro r
      by_cases hs : renewalBankStopAt (headlineCleanTarget ring) r.val
      · have hvalid :
            (bankCleanRootedReferenceData ring hbank).referenceStop r :=
          hs
        exact (costWord_terminal _ _ r hvalid (e :: word)).trans
          (costWord_terminal _ _ _ hs (e :: word)).symm
      · have hvalid :
            ¬ (bankCleanRootedReferenceData ring hbank).referenceStop r :=
          hs
        rw [renewalWordCostConsClean _ _ r e word hvalid,
          renewalWordCostConsClean _ _ r.val e word hs]
        exact congrArg (fun q : Nat => 1 + q)
          (ih ((bankCleanRootedReferenceData ring hbank).referenceNext r e))

/-- The same exact projection for the count of pre-edge births. -/
private theorem renewalBankValidOriginsProjectionClean {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) :
    ∀ (word : List (Fin n))
      (r : (bankCleanRootedReferenceData ring hbank).Reference),
      Prob.originsWord
        (bankCleanRootedReferenceData ring hbank).referenceNext
        (bankCleanRootedReferenceData ring hbank).referenceStop
        (bankCleanRootedReferenceData ring hbank).spawn r word =
      Prob.originsWord
        (renewalBankNext ring) (renewalBankStopAt (headlineCleanTarget ring))
        (renewalBankSpawn ring) r.val word := by
  classical
  intro word
  induction word with
  | nil =>
      intro r
      rfl
  | cons e word ih =>
      intro r
      by_cases hs : renewalBankStopAt (headlineCleanTarget ring) r.val
      · have hvalid :
            (bankCleanRootedReferenceData ring hbank).referenceStop r :=
          hs
        rw [Prob.originsWord, if_pos hvalid,
          Prob.originsWord, if_pos hs]
      · have hvalid :
            ¬ (bankCleanRootedReferenceData ring hbank).referenceStop r :=
          hs
        rw [Prob.originsWord, if_neg hvalid,
          Prob.originsWord, if_neg hs]
        exact congrArg
          (fun q : Nat => (renewalBankSpawn ring r.val e).length + q)
          (ih ((bankCleanRootedReferenceData ring hbank).referenceNext r e))

/-- F.1 is unchanged after restricting Reference to valid ghosts. -/
theorem bankValidReferenceOriginChargeClean {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) :
    ReferenceOriginChargeAt ring (headlineCleanTarget ring)
      (bankCleanRootedReferenceData ring hbank) := by
  intro seed hnot word
  rw [renewalBankValidOriginsProjectionClean ring hbank word
        ((bankCleanRootedReferenceData ring hbank).referenceStart seed),
      renewalBankValidCostProjectionClean ring hbank word
        ((bankCleanRootedReferenceData ring hbank).referenceStart seed)]
  have h := renewalBankOriginsBudgetClean ring word (renewalBankStart ring seed)
  exact Nat.le_trans h (Nat.le_add_right _ _)

/-- The trial uses the same unrestricted Memory type.
Its one-step domination is unaffected by the Reference subtype. -/
theorem bankValidReferenceAttemptDominationClean {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) :
    ReferenceAttemptDominationAt ring (headlineCleanTarget ring) hn
      (bankCleanRootedReferenceData ring hbank) := by
  intro seed hnot word
  rw [renewalBankValidCostProjectionClean ring hbank word
        ((bankCleanRootedReferenceData ring hbank).referenceStart seed)]
  exact renewalBankAttemptWordClean ring hn word
    (seed, renewalBankInitialMemory ring seed) hnot

/-- Exact F.2 reduction. This is deliberately conditional: it does not
infer a BANK drift inequality merely from the stamp invariant.
The three concrete premises are (a) one-service expected potential
nonincrease, (b) threshold domination, (c) total newborn potential
at most one. The age subtype removes all same-ID future births. -/
theorem renewalBankCleanRarityOfPotential {n : Nat}
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
      (bankCleanRootedReferenceData ring hbank)
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

/-- The BANK hbirth producer and the previous hwin theorem reduce
F.2 origin rarity to a single still-unproved pair-row drift
property. No implicit global drift or uniqueness assumption
is introduced. -/
theorem renewalBankCleanRarityOfPairMassDrift
    {n : Nat} (hn : 5 ≤ n)
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hpair : ∀ (o : RenewalBankOrigin n)
      (r : RenewalBankFuture o),
      RenewalBankPairMassDrift ring o
        (compileAdvice (ceilLogTwo n)).K r.val) :
    ReferenceOriginRarity ring
      (bankCleanRootedReferenceData ring hbank)
      (compileAdvice (ceilLogTwo n)).kappa := by
  apply renewalBankCleanRarityOfPotential ring hbank
    (fun o r => renewalBankOriginPotential o
      (compileAdvice (ceilLogTwo n)).K r.val.2)
  · intro o r
    exact renewalBankOriginPotentialHstepOfPairMassDrift
      hn ring o (compileAdvice (ceilLogTwo n)).K r (hpair o r)
  · intro o r
    exact renewalBankOriginPotentialHwin o r
  · intro r e born hmem
    exact renewalBankOriginPotentialHbirth hn ring r e born hmem

/-- F.2 origin-rarity conclusion using the existing mass-potential
hstep and hwin/hbirth consumers; no assumed drift hypothesis. -/
theorem renewalBankCleanRarity {n : Nat}
    (hn : 5 ≤ n)
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) :
    ReferenceOriginRarity ring
      (bankCleanRootedReferenceData ring hbank)
      (compileAdvice (ceilLogTwo n)).kappa := by
  exact renewalBankCleanRarityOfPairMassDrift
    hn ring hbank
    (fun o r => renewalBankFuturePairMassDrift ring o
      (compileAdvice (ceilLogTwo n)).K r)

/-- An exact clock producer for the decorated BANK reference.
Its five premises are the paper's sigma_B, sigma_G, sigma_1,
sigma_p, and prepared-to-generated substage estimates on the
same valid-reference transition. None is silently transferred
from a frozen or physically unmasked process. -/
theorem renewalBankReferenceClockOfStagesClean {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (rooted inheritedGone grantFree singleton prepared :
      (bankCleanRootedReferenceData ring hbank).Reference → Prop)
    (hstart : ∀ seed : RootedSeed ring,
      ¬ headlineCleanTarget ring seed.val →
        rooted ((bankCleanRootedReferenceData ring hbank).referenceStart seed))
    (hOld : StageInheritedAuthorityExtinction
      (bankCleanRootedReferenceData ring hbank).referenceNext
      rooted inheritedGone (ceilLogTwo n))
    (hDrain : StageReferenceGrantDrain
      (bankCleanRootedReferenceData ring hbank).referenceNext
      inheritedGone grantFree)
    (hSingle : StageReferenceSingleton
      (bankCleanRootedReferenceData ring hbank).referenceNext
      grantFree singleton)
    (hPrep : StageReferencePreparation
      (bankCleanRootedReferenceData ring hbank).referenceNext
      singleton prepared)
    (hFinish : StageReferenceGeneratedFinish
      (bankCleanRootedReferenceData ring hbank).referenceNext
      prepared
      (bankCleanRootedReferenceData ring hbank).referenceStop
      (headlineReferenceFinishRate (ceilLogTwo n))) :
    ReferenceClockAt ring (headlineCleanTarget ring) (bankCleanRootedReferenceData ring hbank)
      (renewalBankReferenceCeiling n) := by
  have hthree : 3 ≤ ceilLogTwo n := ceilLogTwo_ge_three n hn
  have hstages := headlineReferenceStagesCompose
    (bankCleanRootedReferenceData ring hbank).referenceNext
    rooted inheritedGone grantFree singleton prepared
    (bankCleanRootedReferenceData ring hbank).referenceStop
    (ceilLogTwo n) hthree (by omega : 0 < n)
    hOld hDrain hSingle hPrep hFinish
  intro seed hnot T
  exact (UniformFirstHit.expectedHittingTimeAtMost_iff_cost
    (bankCleanRootedReferenceData ring hbank).referenceNext
    (bankCleanRootedReferenceData ring hbank).referenceStop
    (by omega : 0 < n)
    ((bankCleanRootedReferenceData ring hbank).referenceStart seed)
    (renewalBankReferenceCeiling n * n ^ 2)).1
    (hstages _ (hstart seed hnot)) T

/-- The BANK reference clock with R8 and R9 discharged: what remains
is the rooted start, the sigma_B producer into rooted and
InheritedAuthorityExtinct (R7), and the prepared-to-generated finish
(R10). -/
theorem renewalBankCleanClockOfOldAndFinish {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (rooted : (bankCleanRootedReferenceData ring hbank).Reference → Prop)
    (hstart : ∀ seed : RootedSeed ring,
      ¬ headlineCleanTarget ring seed.val →
        rooted ((bankCleanRootedReferenceData ring hbank).referenceStart seed))
    (hOld : StageInheritedAuthorityExtinction
      (bankCleanRootedReferenceData ring hbank).referenceNext
      rooted
      (fun z => headlineRooted ring z.val.1 ∧
        InheritedAuthorityExtinct ring hbank z)
      (ceilLogTwo n))
    (hFinish : StageReferenceGeneratedFinish
      (bankCleanRootedReferenceData ring hbank).referenceNext
      (BankPreparedAtSomeRoot ring hbank)
      (bankCleanRootedReferenceData ring hbank).referenceStop
      (headlineReferenceFinishRate (ceilLogTwo n))) :
    ReferenceClockAt ring (headlineCleanTarget ring) (bankCleanRootedReferenceData ring hbank)
      (renewalBankReferenceCeiling n) := by
  exact renewalBankReferenceClockOfStagesClean ring hn hbank
    rooted
    (fun z => headlineRooted ring z.val.1 ∧
      InheritedAuthorityExtinct ring hbank z)
    (BankPostInheritedGrantDrain ring hbank)
    (BankAnyPostInheritedSingleton ring hbank)
    (BankPreparedAtSomeRoot ring hbank)
    hstart hOld
    (bankReferenceGrantDrainStage ring hn hbank)
    (bankSingletonStageWithInheritedInvariant ring hn hbank)
    (bankPreparationStageWithInheritedInvariant ring hn hbank)
    hFinish

/-! ## Retry coverage on the clean reference (copy of BankRetryCoverage.lean) -/

/-- The valid reference at the end of the actual BANK edge word. -/
private def bankRefAfterClean {n : Nat} (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) :
    (bankCleanRootedReferenceData ring hbank).Reference →
    List (Fin n) →
    (bankCleanRootedReferenceData ring hbank).Reference
  | r, [] => r
  | r, e :: es =>
      bankRefAfterClean ring hbank
        ((bankCleanRootedReferenceData ring hbank).referenceNext r e) es

/-- The reference target has not been visited, including at the
end of the prefix. This is the same open-word convention as SMALL. -/
private def bankRefOpenClean {n : Nat} (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) :
    (bankCleanRootedReferenceData ring hbank).Reference →
    List (Fin n) → Prop
  | r, [] =>
      ¬ (bankCleanRootedReferenceData ring hbank).referenceStop r
  | r, e :: es =>
      ¬ (bankCleanRootedReferenceData ring hbank).referenceStop r ∧
      bankRefOpenClean ring hbank
        ((bankCleanRootedReferenceData ring hbank).referenceNext r e) es

private theorem bankRefOpenPrefixClean {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) :
    ∀ (u v : List (Fin n))
      (r : (bankCleanRootedReferenceData ring hbank).Reference),
      bankRefOpenClean ring hbank r (u ++ v) →
      bankRefOpenClean ring hbank r u := by
  intro u
  induction u with
  | nil =>
      intro v r hh
      cases v with
      | nil => exact hh
      | cons e es => exact hh.1
  | cons e es ih =>
      intro v r hh
      exact ⟨hh.1, ih v
        ((bankCleanRootedReferenceData ring hbank).referenceNext r e)
        hh.2⟩

/-- Valid-state projection has the exact unrestricted BANK history.
In particular validity never restarts the source, receipt, or clock. -/
private theorem bankRefAfterProjectionClean {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) :
    ∀ (word : List (Fin n))
      (r : (bankCleanRootedReferenceData ring hbank).Reference),
      (bankRefAfterClean ring hbank r word).val =
        rbRun ring r.val word := by
  intro word
  induction word with
  | nil =>
      intro r
      rfl
  | cons e es ih =>
      intro r
      change (bankRefAfterClean ring hbank
        ((bankCleanRootedReferenceData ring hbank).referenceNext r e)
        es).val =
        rbRun ring (renewalBankNext ring r.val e) es
      exact ih ((bankCleanRootedReferenceData ring hbank).referenceNext r e)

/-- The precise BANK source-history statement. At a first retry cut
after an open prefix u, a *genuinely spawned* earlier completed
origin for the successful root must win on the authentic intervening
suffix, including the success edge. The birth is an actual old-state
renewalBankSpawn, not a post-hoc receipt identifier. -/
def BankRunSourceWitnessClean {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) : Prop :=
  ∀ (seed : RootedSeed ring) (u : List (Fin n)) (e : Fin n),
    bankRefOpenClean ring hbank
      ((bankCleanRootedReferenceData ring hbank).referenceStart seed) u →
    renewalBankCut ring
      (bankRefAfterClean ring hbank
        ((bankCleanRootedReferenceData ring hbank).referenceStart seed) u).val.1
      (bankRefAfterClean ring hbank
        ((bankCleanRootedReferenceData ring hbank).referenceStart seed) u).val.2
      e = true →
    ∃ (p : List (Fin n)) (f : Fin n) (tail : List (Fin n))
      (born : RenewalBankBorn n),
      u = p ++ f :: tail ∧
      born ∈ renewalBankSpawn ring
        (bankRefAfterClean ring hbank
          ((bankCleanRootedReferenceData ring hbank).referenceStart seed) p).val f ∧
      born.identity.root = e ∧
      renewalBankWin ring born (tail ++ [e]) = true

/-- A completed origin in the exact OLD birth log has a
literal creating BANK edge and an authentic scheduler suffix.
No existential time stamp or fabricated post-state is used. -/
private theorem bankBirthHistoryDecomposesClean {n : Nat}
    (ring : DirectedRing n) :
    ∀ (word : List (Fin n)) (r : RenewalBankReference n)
      (o : RenewalBankOrigin n),
      o ∈ rbBirths ring r word →
      ∃ (pre : List (Fin n)) (f : Fin n)
        (tail : List (Fin n)),
        word = pre ++ f :: tail ∧
        renewalBankBirth ring
          (rbRun ring r pre).1 (rbRun ring r pre).2 f = some o := by
  intro word
  induction word with
  | nil =>
      intro r o hmem
      cases hmem
  | cons e es ih =>
      intro r o hmem
      change o ∈
        (match renewalBankBirth ring r.1 r.2 e with
         | none => []
         | some x => [x]) ++
        rbBirths ring (renewalBankNext ring r e) es at hmem
      rcases List.mem_append.mp hmem with hnow | hlater
      · cases hb : renewalBankBirth ring r.1 r.2 e with
        | none =>
            simp [hb] at hnow
        | some x =>
            have hx : o = x := by
              simpa [hb] using hnow
            subst o
            exact ⟨[], e, es, rfl, hb⟩
      · obtain ⟨p, f, tail, hwords, hbirth⟩ :=
          ih (renewalBankNext ring r e) o hlater
        refine ⟨e :: p, f, tail, ?_, ?_⟩
        · rw [hwords]
          rfl
        · change renewalBankBirth ring
            (rbRun ring (renewalBankNext ring r e) p).1
            (rbRun ring (renewalBankNext ring r e) p).2 f = some o
          exact hbirth

/-- A payload with the recorded origin and at least K heads at
one actual worker site makes the broad BANK reachability flag true. -/
private theorem bankReachedOfWorkerClean {n : Nat}
    (m : RenewalBankMemory n) (o : RenewalBankOrigin n)
    (K : Nat) (i : Fin n) (p : RenewalBankPayload n)
    (hw : (m.sites i).worker = .payload p)
    (ho : p.origin = some o)
    (hK : K ≤ p.heads) :
    renewalBankReached o K m = true := by
  have hsite :
      renewalBankSiteReached o K (m.sites i) = true := by
    simp [renewalBankSiteReached, renewalBankPayloadReached,
      hw, ho, hK]
  unfold renewalBankReached
  rw [List.any_eq_true]
  refine ⟨true, ?_, rfl⟩
  exact List.mem_ofFn.mpr ⟨i, hsite⟩

/-- If the actual memory has reached K heads after a word, that
word has a true BANK origin win, even if an earlier cut already won. -/
private theorem bankWinWordOfEndReachedClean {n : Nat}
    (ring : DirectedRing n) (o : RenewalBankOrigin n)
    (K : Nat) :
    ∀ (word : List (Fin n)) (r : RenewalBankReference n),
      renewalBankReached o K (rbRun ring r word).2 = true →
      renewalBankWinWord ring o K word r = true := by
  intro word
  induction word with
  | nil =>
      intro r hh
      exact hh
  | cons e es ih =>
      intro r hh
      have ht := ih (renewalBankNext ring r e) hh
      change (renewalBankReached o K r.2 ||
        renewalBankWinWord ring o K es
          (renewalBankNext ring r e)) = true
      rw [ht]
      cases renewalBankReached o K r.2 <;> rfl

private theorem bankWinAppendTrueClean {n : Nat}
    (ring : DirectedRing n) (o : RenewalBankOrigin n)
    (K : Nat) :
    ∀ (u v : List (Fin n)) (r : RenewalBankReference n),
      renewalBankWinWord ring o K u r = true →
      renewalBankWinWord ring o K (u ++ v) r = true := by
  intro u
  induction u with
  | nil =>
      intro v r hh
      cases v with
      | nil => exact hh
      | cons e es =>
          change renewalBankReached o K r.2 = true at hh
          change (renewalBankReached o K r.2 ||
            renewalBankWinWord ring o K es
              (renewalBankNext ring r e)) = true
          rw [hh]
          rfl
  | cons e es ih =>
      intro v r hh
      change (renewalBankReached o K r.2 ||
        renewalBankWinWord ring o K es
          (renewalBankNext ring r e)) = true at hh
      change (renewalBankReached o K r.2 ||
        renewalBankWinWord ring o K (es ++ v)
          (renewalBankNext ring r e)) = true
      have hdisj :
          renewalBankReached o K r.2 = true ∨
          renewalBankWinWord ring o K es
            (renewalBankNext ring r e) = true := by
        simpa only [Bool.or_eq_true] using hh
      rcases hdisj with hfront | htail
      · rw [hfront]
        rfl
      · have hafter := ih v (renewalBankNext ring r e) htail
        rw [hafter]
        simp

private theorem bankValidReferenceStartValClean {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) :
    ((bankCleanRootedReferenceData ring hbank).referenceStart seed).val =
      renewalBankStart ring seed := by
  rfl

theorem bankRunSourceWitnessOfHeadThresholdClean {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hthreshold : BankCutGenuineHeadThreshold ring hbank) :
    BankRunSourceWitnessClean ring hbank := by
  intro seed u e hopen hcut
  have hstart := bankValidReferenceStartValClean ring hbank seed
  have hprojection := bankRefAfterProjectionClean ring hbank u
    ((bankCleanRootedReferenceData ring hbank).referenceStart seed)
  rw [hstart] at hprojection
  have hraw : renewalBankCut ring
      (rbRun ring (renewalBankStart ring seed) u).1
      (rbRun ring (renewalBankStart ring seed) u).2 e = true := by
    rw [← hprojection]
    exact hcut
  obtain ⟨p, o, hworker, horigin, hborn, hroot, hheads⟩ :=
    bankFreshCutLoggedOrigin ring hn hbank seed u e hraw
  obtain ⟨pfx, f, tail, hword, hbirth⟩ :=
    bankBirthHistoryDecomposesClean ring u
      (renewalBankStart ring seed) o hborn
  have hKcount :=
    hthreshold seed u e p o hraw hworker horigin
  have hK : (compileAdvice (ceilLogTwo n)).K ≤ p.heads := by
    rw [hheads]
    exact hKcount
  have hReached : renewalBankReached o
      (compileAdvice (ceilLogTwo n)).K
      (rbRun ring (renewalBankStart ring seed) u).2 = true :=
    bankReachedOfWorkerClean
      (rbRun ring (renewalBankStart ring seed) u).2
      o (compileAdvice (ceilLogTwo n)).K
      (ring.rightNeighbor e) p hworker horigin hK
  have hRunTail :
      rbRun ring
        (renewalBankNext ring
          (rbRun ring (renewalBankStart ring seed) pfx) f)
        tail =
      rbRun ring (renewalBankStart ring seed) u := by
    rw [hword, rbRunAppend]
    rfl
  have hWinTail : renewalBankWinWord ring o
      (compileAdvice (ceilLogTwo n)).K tail
      (renewalBankNext ring
        (rbRun ring (renewalBankStart ring seed) pfx) f) = true := by
    apply bankWinWordOfEndReachedClean
    rw [hRunTail]
    exact hReached
  have hWinSuffix : renewalBankWin ring
      { identity := o
        afterBirth := renewalBankNext ring
          (rbRun ring (renewalBankStart ring seed) pfx) f }
      (tail ++ [e]) = true := by
    exact bankWinAppendTrueClean ring o
      (compileAdvice (ceilLogTwo n)).K
      tail [e]
      (renewalBankNext ring
        (rbRun ring (renewalBankStart ring seed) pfx) f)
      hWinTail
  refine ⟨pfx, f, tail,
    { identity := o
      afterBirth := renewalBankNext ring
        (rbRun ring (renewalBankStart ring seed) pfx) f },
    hword, ?_, hroot, hWinSuffix⟩
  have hpreProj := bankRefAfterProjectionClean ring hbank pfx
    ((bankCleanRootedReferenceData ring hbank).referenceStart seed)
  rw [hpreProj, hstart]
  simp [renewalBankSpawn, hbirth]

/-- A single genuine born identity with a passing win test
contributes a positive summand, regardless of other births. -/
private theorem bankBornListPositiveClean {A : Type}
    (os : List A) (f : A → Bool) (a : A)
    (hmem : a ∈ os) (hwin : f a = true) :
    0 < (os.map (fun o => Prob.indicator (f o))).sum := by
  induction os with
  | nil => cases hmem
  | cons x xs ih =>
      rcases List.mem_cons.mp hmem with he | ht
      · subst x
        simp only [List.map_cons, List.sum_cons]
        have hh : Prob.indicator (f a) = 1 := by
          simp [Prob.indicator, hwin]
        omega
      · simp only [List.map_cons, List.sum_cons]
        have hh := ih ht
        omega

private theorem bankSuccessfulOriginClean {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (born : RenewalBankBorn n) :
    ∀ (u : List (Fin n))
      (r : (bankCleanRootedReferenceData ring hbank).Reference)
      (e : Fin n) (v : List (Fin n)),
      bankRefOpenClean ring hbank r u →
      born ∈ (bankCleanRootedReferenceData ring hbank).spawn
        (bankRefAfterClean ring hbank r u) e →
      (bankCleanRootedReferenceData ring hbank).win born v = true →
      0 < Prob.successfulOriginsWord
        (bankCleanRootedReferenceData ring hbank).referenceNext
        (bankCleanRootedReferenceData ring hbank).referenceStop
        (bankCleanRootedReferenceData ring hbank).spawn
        (bankCleanRootedReferenceData ring hbank).win
        r (u ++ e :: v) := by
  intro u
  induction u with
  | nil =>
      intro r e v hopen hmem hwin
      have hh := bankBornListPositiveClean
        ((bankCleanRootedReferenceData ring hbank).spawn r e)
        (fun o => (bankCleanRootedReferenceData ring hbank).win o v)
        born hmem hwin
      change 0 < (if (bankCleanRootedReferenceData ring hbank).referenceStop r
        then 0
        else (((bankCleanRootedReferenceData ring hbank).spawn r e).map
          (fun o => Prob.indicator
            ((bankCleanRootedReferenceData ring hbank).win o v))).sum +
          Prob.successfulOriginsWord
            (bankCleanRootedReferenceData ring hbank).referenceNext
            (bankCleanRootedReferenceData ring hbank).referenceStop
            (bankCleanRootedReferenceData ring hbank).spawn
            (bankCleanRootedReferenceData ring hbank).win
            ((bankCleanRootedReferenceData ring hbank).referenceNext r e) v)
      rw [if_neg hopen]
      omega
  | cons f fs ih =>
      intro r e v hopen hmem hwin
      have hh := ih
        ((bankCleanRootedReferenceData ring hbank).referenceNext r f)
        e v hopen.2 hmem hwin
      change 0 < (if (bankCleanRootedReferenceData ring hbank).referenceStop r
        then 0
        else (((bankCleanRootedReferenceData ring hbank).spawn r f).map
          (fun o => Prob.indicator
            ((bankCleanRootedReferenceData ring hbank).win o
              (fs ++ e :: v)))).sum +
          Prob.successfulOriginsWord
            (bankCleanRootedReferenceData ring hbank).referenceNext
            (bankCleanRootedReferenceData ring hbank).referenceStop
            (bankCleanRootedReferenceData ring hbank).spawn
            (bankCleanRootedReferenceData ring hbank).win
            ((bankCleanRootedReferenceData ring hbank).referenceNext r f)
            (fs ++ e :: v))
      rw [if_neg hopen.1]
      omega

/-- The actual rooted BANK retry shell, not an invented trial step. -/
private noncomputable def bankRetryKernelClean {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) :
    RetryKernel (RootedSeed ring × RenewalBankMemory n)
      (RootedSeed ring) n :=
  referenceKernelAt ring (headlineCleanTarget ring) hn (bankCleanRootedReferenceData ring hbank)

private theorem bankRetryFirstLeOneClean {A Seed : Type} {n : Nat}
    (K : RetryKernel A Seed n) :
    ∀ (word : List (Fin n)) (z : AttemptNode A Seed),
      Prob.retryFirstWord K z word ≤ 1 := by
  intro word
  induction word with
  | nil =>
      intro z
      cases z <;> simp [Prob.retryFirstWord]
  | cons e es ih =>
      intro z
      cases z with
      | success => simp [Prob.retryFirstWord]
      | retry seed => simp [Prob.retryFirstWord]
      | active a =>
          change Prob.retryFirstWord K (K.step a e) es ≤ 1
          exact ih (K.step a e)

/-- Cut extraction, as for SMALL: the first retry has a literal
pre-edge BANK cut, a stop-free earlier reference pfx, and no
physical/ref memory divergence before that cut. -/
private theorem bankRetryFirstHasCutClean {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) :
    ∀ (word : List (Fin n))
      (a : RootedSeed ring × RenewalBankMemory n)
      (r : (bankCleanRootedReferenceData ring hbank).Reference),
      r.val = (a.1.val, a.2) →
      ¬ (bankCleanRootedReferenceData ring hbank).referenceStop r →
      Prob.retryFirstWord (bankRetryKernelClean ring hn hbank)
        (.active a) word = 1 →
      ∃ (u : List (Fin n)) (e : Fin n) (v : List (Fin n)),
        word = u ++ e :: v ∧
        bankRefOpenClean ring hbank r u ∧
        renewalBankCut ring
          (bankRefAfterClean ring hbank r u).val.1
          (bankRefAfterClean ring hbank r u).val.2 e = true := by
  intro word
  induction word with
  | nil =>
      intro a r hre hnot hretry
      change (0 : Nat) = 1 at hretry
      cases hretry
  | cons e es ih =>
      intro a r hre hnot hretry
      change Prob.retryFirstWord
        (bankRetryKernelClean ring hn hbank)
        ((bankRetryKernelClean ring hn hbank).step a e) es = 1 at hretry
      cases hs : (bankRetryKernelClean ring hn hbank).step a e with
      | success =>
          rw [hs] at hretry
          simp [Prob.retryFirstWord] at hretry
      | retry seed =>
          have hs' : rootedTrialStepAt ring (headlineCleanTarget ring) hn
              (renewalBankTrialAdvance ring)
              (renewalBankTrialCut ring) a e = .retry seed := hs
          unfold rootedTrialStepAt at hs'
          split at hs'
          · cases hs'
          · rename_i hnext
            split at hs'
            · rename_i hcut
              have hc : renewalBankCut ring r.val.1 r.val.2 e =
                  true := by
                rw [hre]
                change renewalBankTrialCut ring a e = true
                exact hcut
              exact ⟨[], e, es, rfl, hnot, hc⟩
            · cases hs'
      | active b =>
          rw [hs] at hretry
          have hs' : rootedTrialStepAt ring (headlineCleanTarget ring) hn
              (renewalBankTrialAdvance ring)
              (renewalBankTrialCut ring) a e = .active b := hs
          unfold rootedTrialStepAt at hs'
          split at hs'
          · cases hs'
          · rename_i hnext
            split at hs'
            · cases hs'
            · rename_i hnocut
              cases hs'
              have hc : renewalBankTrialCut ring a e = false := by
                cases htest : renewalBankTrialCut ring a e with
                | false => rfl
                | true => exact False.elim (hnocut htest)
              have href :
                  ((bankCleanRootedReferenceData ring hbank).referenceNext r e).val =
                    ((rootedSuccessor ring hn a.1 e).val,
                      renewalBankTrialAdvance ring a e) := by
                change renewalBankNext ring r.val e = _
                rw [hre]
                apply Prod.ext
                · exact renewalBankPhysicalBeforeCut ring
                    (a.1.val, a.2) e hc
                · rfl
              have hstay :
                  ¬ (bankCleanRootedReferenceData ring hbank).referenceStop
                    ((bankCleanRootedReferenceData ring hbank).referenceNext r e) := by
                change ¬ renewalBankStopAt (headlineCleanTarget ring)
                  (((bankCleanRootedReferenceData ring hbank).referenceNext r e).val)
                rw [href]
                exact hnext
              obtain ⟨u, f, v, hword, hopen, hcut⟩ :=
                ih (rootedSuccessor ring hn a.1 e,
                    renewalBankTrialAdvance ring a e)
                  ((bankCleanRootedReferenceData ring hbank).referenceNext r e)
                  href hstay hretry
              refine ⟨e :: u, f, v, ?_, ?_, ?_⟩
              · exact congrArg (List.cons e) hword
              · exact ⟨hnot, hopen⟩
              · exact hcut

theorem bankReferenceRetryCoverageOfSourceWitnessClean {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hsource : BankRunSourceWitnessClean ring hbank) :
    ReferenceRetryCoverageAt ring (headlineCleanTarget ring) hn
      (bankCleanRootedReferenceData ring hbank) := by
  intro seed hnot word
  change Prob.retryFirstWord (bankRetryKernelClean ring hn hbank)
      (.active (seed, renewalBankInitialMemory ring seed)) word ≤
    Prob.originEventWord
      (bankCleanRootedReferenceData ring hbank).referenceNext
      (bankCleanRootedReferenceData ring hbank).referenceStop
      (bankCleanRootedReferenceData ring hbank).spawn
      (bankCleanRootedReferenceData ring hbank).win
      ((bankCleanRootedReferenceData ring hbank).referenceStart seed) word
  by_cases hz :
      Prob.retryFirstWord (bankRetryKernelClean ring hn hbank)
        (.active (seed, renewalBankInitialMemory ring seed)) word = 0
  · rw [hz]
    exact Nat.zero_le _
  · have hle :=
      bankRetryFirstLeOneClean (bankRetryKernelClean ring hn hbank)
        word (.active (seed, renewalBankInitialMemory ring seed))
    have hretry :
        Prob.retryFirstWord (bankRetryKernelClean ring hn hbank)
          (.active (seed, renewalBankInitialMemory ring seed)) word = 1 := by
      omega
    have hstart :
        ¬ (bankCleanRootedReferenceData ring hbank).referenceStop
          ((bankCleanRootedReferenceData ring hbank).referenceStart seed) := hnot
    obtain ⟨u, e, v, hword, hopen, hcut⟩ :=
      bankRetryFirstHasCutClean ring hn hbank word
        (seed, renewalBankInitialMemory ring seed)
        ((bankCleanRootedReferenceData ring hbank).referenceStart seed)
        rfl hstart hretry
    obtain ⟨p, f, tail, born, hp, hbirth, hroot, hwin⟩ :=
      hsource seed u e hopen hcut
    have hpopen :
        bankRefOpenClean ring hbank
          ((bankCleanRootedReferenceData ring hbank).referenceStart seed)
          p := by
      have hfull : bankRefOpenClean ring hbank
          ((bankCleanRootedReferenceData ring hbank).referenceStart seed)
          (p ++ f :: tail) := by
        rw [← hp]
        exact hopen
      exact bankRefOpenPrefixClean ring hbank p (f :: tail)
        ((bankCleanRootedReferenceData ring hbank).referenceStart seed)
        hfull
    have hmem :
        born ∈ (bankCleanRootedReferenceData ring hbank).spawn
          (bankRefAfterClean ring hbank
            ((bankCleanRootedReferenceData ring hbank).referenceStart seed)
            p) f := hbirth
    have hwinLong :
        renewalBankWin ring born (tail ++ e :: v) = true := by
      have hh := bankWinAppendTrueClean ring born.identity
        (compileAdvice (ceilLogTwo n)).K
        (tail ++ [e]) v born.afterBirth hwin
      change renewalBankWinWord ring born.identity
        (compileAdvice (ceilLogTwo n)).K
        (tail ++ e :: v) born.afterBirth = true
      simpa only [List.append_assoc, List.singleton_append] using hh
    have hpos := bankSuccessfulOriginClean ring hbank born p
      ((bankCleanRootedReferenceData ring hbank).referenceStart seed)
      f (tail ++ e :: v) hpopen hmem hwinLong
    have hlist :
        u ++ e :: v = p ++ f :: (tail ++ e :: v) := by
      rw [hp]
      simp only [List.append_assoc, List.cons_append]
    have hpositive :
        0 < Prob.successfulOriginsWord
          (bankCleanRootedReferenceData ring hbank).referenceNext
          (bankCleanRootedReferenceData ring hbank).referenceStop
          (bankCleanRootedReferenceData ring hbank).spawn
          (bankCleanRootedReferenceData ring hbank).win
          ((bankCleanRootedReferenceData ring hbank).referenceStart seed)
          word := by
      rw [hword, hlist]
      exact hpos
    have hevent :
        Prob.originEventWord
          (bankCleanRootedReferenceData ring hbank).referenceNext
          (bankCleanRootedReferenceData ring hbank).referenceStop
          (bankCleanRootedReferenceData ring hbank).spawn
          (bankCleanRootedReferenceData ring hbank).win
          ((bankCleanRootedReferenceData ring hbank).referenceStart seed)
          word = 1 := by
      unfold Prob.originEventWord
      split
      · rename_i he
        omega
      · rfl
    rw [hretry, hevent]
    exact Nat.le_refl 1

/-- Exact one-premise reduction of the BANK causal coverage
obligation. The premise is the previously defined, still-OPEN
physical K-head threshold; the retry-first word induction and
all receipt/origin transports have been discharged separately. -/
theorem bankReferenceRetryCoverageOfHeadThresholdClean {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hthreshold : BankCutGenuineHeadThreshold ring hbank) :
    ReferenceRetryCoverageAt ring (headlineCleanTarget ring) hn
      (bankCleanRootedReferenceData ring hbank) := by
  exact bankReferenceRetryCoverageOfSourceWitnessClean
    ring hn hbank
    (bankRunSourceWitnessOfHeadThresholdClean
      ring hn hbank hthreshold)

/-! ## The clean BANK realization and the clean R14 -/

/-- The clean BANK reference clock: R7 (rooted start and sigma_B, as in
`renewalBankReferenceClockOfOldAndFinish`) and the clean finish.
Consumer: `bankCleanRealization`. -/
theorem bankCleanReferenceClock {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hdigit : BankCleanDigitHalfOnDrain ring hbank)
    (rooted : (bankCleanRootedReferenceData ring hbank).Reference → Prop)
    (hstart : ∀ seed : RootedSeed ring,
      ¬ headlineCleanTarget ring seed.val →
        rooted ((bankCleanRootedReferenceData ring hbank).referenceStart seed))
    (hOld : StageInheritedAuthorityExtinction
      (bankCleanRootedReferenceData ring hbank).referenceNext
      rooted
      (fun z => headlineRooted ring z.val.1 ∧
        InheritedAuthorityExtinct ring hbank z)
      (ceilLogTwo n)) :
    ReferenceClockAt ring (headlineCleanTarget ring)
      (bankCleanRootedReferenceData ring hbank)
      (renewalBankReferenceCeiling n) :=
  renewalBankCleanClockOfOldAndFinish ring hn hbank rooted hstart hOld
    (bankCleanFinishReference ring hn hbank hdigit)

/-- The clean BANK realization: domination, charge, rarity proved here,
coverage from the K-head threshold, the clock from R7 and the clean
finish.  Consumer: `bankCleanStageRootedRenewalCost`. -/
theorem bankCleanRealization {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hcoverage : ReferenceRetryCoverageAt ring (headlineCleanTarget ring) hn
      (bankCleanRootedReferenceData ring hbank))
    (hclock : ReferenceClockAt ring (headlineCleanTarget ring)
      (bankCleanRootedReferenceData ring hbank)
      (renewalBankReferenceCeiling n)) :
    RootedReferenceRealizationAt ring (headlineCleanTarget ring) hn := by
  have hmargins := renewalBankSpatialMargins n hn hbank
  refine ⟨bankCleanRootedReferenceData ring hbank,
    renewalBankReferenceCeiling n, ?_, hmargins.1, hmargins.2⟩
  exact {
    domination := bankValidReferenceAttemptDominationClean ring hn hbank
    coverage := hcoverage
    charge := bankValidReferenceOriginChargeClean ring hbank
    rarity := renewalBankCleanRarity hn ring hbank
    clock := hclock }

/-- The BANK case of the clean R14.  Open premises: the digit half-stage
(R10c), the K-head threshold of the old R11 (unchanged statement, it does
not mention the stop), and R7 (rooted start and sigma_B, unchanged
except that the start is quantified over non-Gclean seeds).
Consumer: `l3HeadlineOfRequestAndCleanRenewal` (HeadlineClean, BANK
branch). -/
theorem bankCleanStageRootedRenewalCost {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hdigit : BankCleanDigitHalfOnDrain ring hbank)
    (hthreshold : L3.BankRetryCoverage.BankCutGenuineHeadThreshold ring hbank)
    (rooted : (bankCleanRootedReferenceData ring hbank).Reference → Prop)
    (hstart : ∀ seed : RootedSeed ring,
      ¬ headlineCleanTarget ring seed.val →
        rooted ((bankCleanRootedReferenceData ring hbank).referenceStart seed))
    (hOld : StageInheritedAuthorityExtinction
      (bankCleanRootedReferenceData ring hbank).referenceNext
      rooted
      (fun z => headlineRooted ring z.val.1 ∧
        InheritedAuthorityExtinct ring hbank z)
      (ceilLogTwo n)) :
    StageCleanRootedRenewalCost ring := by
  obtain ⟨D, A, hcertificate, hmargin, hreserve⟩ :=
    bankCleanRealization ring hn hbank
      (bankReferenceRetryCoverageOfHeadThresholdClean ring hn hbank hthreshold)
      (bankCleanReferenceClock ring hn hbank hdigit rooted hstart hOld)
  intro C hC T
  exact rootedCostFromReferenceAt ring (headlineCleanTarget ring) hn D A
    (compileAdvice (ceilLogTwo n)).kappa (headlineRenewalRate n)
    hcertificate hmargin hreserve C hC T

/-- The same with the old R11 row table (`BankWindowRows`) in place of
the K-head threshold.  Consumer: the clean headline assembly. -/
theorem bankCleanStageRootedRenewalCostOfWindowRows {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hdigit : BankCleanDigitHalfOnDrain ring hbank)
    (hrows : L3.BankWindow.BankWindowRows ring)
    (rooted : (bankCleanRootedReferenceData ring hbank).Reference → Prop)
    (hstart : ∀ seed : RootedSeed ring,
      ¬ headlineCleanTarget ring seed.val →
        rooted ((bankCleanRootedReferenceData ring hbank).referenceStart seed))
    (hOld : StageInheritedAuthorityExtinction
      (bankCleanRootedReferenceData ring hbank).referenceNext
      rooted
      (fun z => headlineRooted ring z.val.1 ∧
        InheritedAuthorityExtinct ring hbank z)
      (ceilLogTwo n)) :
    StageCleanRootedRenewalCost ring :=
  bankCleanStageRootedRenewalCost ring hn hbank hdigit
    (L3.BankWindow.bankCutGenuineHeadThresholdOfWindowInv ring hn hbank
      (fun seed pre => L3.BankWindow.bankWindowInvWordOfRows
        ring hn hbank hrows seed pre))
    rooted hstart hOld

end L3.HeadlineRenewalCleanBank

#print axioms L3.HeadlineRenewalCleanBank.rootedTrialRetryNonterminalAt
#print axioms L3.HeadlineRenewalCleanBank.rootedTrialSimulationAt
#print axioms L3.HeadlineRenewalCleanBank.referenceAttemptCostAt
#print axioms L3.HeadlineRenewalCleanBank.referenceRetryCountAt
#print axioms L3.HeadlineRenewalCleanBank.referenceOriginMassAt
#print axioms L3.HeadlineRenewalCleanBank.referenceRetryMassAt
#print axioms L3.HeadlineRenewalCleanBank.rootedCostFromReferenceAt
#print axioms L3.HeadlineRenewalCleanBank.renewalBankOriginsBudgetClean
#print axioms L3.HeadlineRenewalCleanBank.renewalBankAttemptWordClean
#print axioms L3.HeadlineRenewalCleanBank.bankValidReferenceOriginChargeClean
#print axioms L3.HeadlineRenewalCleanBank.bankValidReferenceAttemptDominationClean
#print axioms L3.HeadlineRenewalCleanBank.renewalBankCleanRarityOfPotential
#print axioms L3.HeadlineRenewalCleanBank.renewalBankCleanRarityOfPairMassDrift
#print axioms L3.HeadlineRenewalCleanBank.renewalBankCleanRarity
#print axioms L3.HeadlineRenewalCleanBank.renewalBankReferenceClockOfStagesClean
#print axioms L3.HeadlineRenewalCleanBank.renewalBankCleanClockOfOldAndFinish
#print axioms L3.HeadlineRenewalCleanBank.bankRunSourceWitnessOfHeadThresholdClean
#print axioms L3.HeadlineRenewalCleanBank.bankReferenceRetryCoverageOfSourceWitnessClean
#print axioms L3.HeadlineRenewalCleanBank.bankReferenceRetryCoverageOfHeadThresholdClean
#print axioms L3.HeadlineRenewalCleanBank.bankCleanReferenceClock
#print axioms L3.HeadlineRenewalCleanBank.bankCleanRealization
#print axioms L3.HeadlineRenewalCleanBank.bankCleanStageRootedRenewalCost
#print axioms L3.HeadlineRenewalCleanBank.bankCleanStageRootedRenewalCostOfWindowRows
