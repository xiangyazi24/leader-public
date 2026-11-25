import Leader.L3.Headline.Renewal

/-!
L3-PRIME s5: generic nomination, sharp origin/renewal, and block-tail lemmas.
UNCOMPILED DRAFT. No compiler run or axioms audit has been claimed.
-/

namespace L3.Prob

set_option autoImplicit false
set_option Elab.async false

open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree

private theorem sharpScheduleSum_zero {n : Nat}
    (f : List (Fin n) → Nat) :
    scheduleSum n 0 f = f [] := by
  simp [scheduleSum, FixedSpanRenewalPayload.wordSum, allSchedules]

private theorem sharpScheduleSum_succ {n : Nat}
    (T : Nat) (f : List (Fin n) → Nat) :
    scheduleSum n (T + 1) f =
      (List.ofFn (fun e : Fin n =>
        scheduleSum n T (fun w => f (e :: w)))).sum :=
  FixedSpanRenewalPayload.wordSum_succ n T f

private theorem sharpScheduleSum_const {n : Nat} (T c : Nat) :
    scheduleSum n T (fun _ => c) = n ^ T * c := by
  change FixedSpanRenewalPayload.wordSum n T (fun _ => c) = _
  rw [← FixedSpanRenewalPayload.rawWord_sum n T (fun _ => c)]
  exact ofFn_sum_const (n ^ T) c

private theorem sharpScheduleSum_add {n : Nat} (T : Nat)
    (f g : List (Fin n) → Nat) :
    scheduleSum n T (fun w => f w + g w) =
      scheduleSum n T f + scheduleSum n T g := by
  change FixedSpanRenewalPayload.wordSum n T (fun w => f w + g w) =
    FixedSpanRenewalPayload.wordSum n T f +
      FixedSpanRenewalPayload.wordSum n T g
  rw [← FixedSpanRenewalPayload.rawWord_sum n T (fun w => f w + g w),
      ← FixedSpanRenewalPayload.rawWord_sum n T f,
      ← FixedSpanRenewalPayload.rawWord_sum n T g]
  exact ofFn_sum_add _ _

private theorem sharpIndicatorListCount {A : Type}
    (xs : List A) (p : A → Bool) :
    (xs.map (fun a => indicator (p a))).sum = xs.countP p := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
      rw [List.map_cons, List.sum_cons, List.countP_cons, ih]
      cases hp : p a <;> simp [indicator, hp, Nat.add_comm]

private theorem sharpNominationCount {n : Nat} (p : Fin n → Bool) :
    (List.ofFn (fun e : Fin n => indicator (p e))).sum =
      (List.finRange n).countP p := by
  have hmap :
      (List.ofFn (fun e : Fin n => indicator (p e))) =
        (List.finRange n).map (fun e => indicator (p e)) := by
    unfold List.finRange
    rw [List.map_ofFn]
    rfl
  calc
    (List.ofFn (fun e : Fin n => indicator (p e))).sum =
        ((List.finRange n).map (fun e => indicator (p e))).sum :=
      congrArg List.sum hmap
    _ = (List.finRange n).countP p :=
      sharpIndicatorListCount (List.finRange n) p

open Classical in
noncomputable def nominatedWord {S : Type} {n : Nat}
    (next : S → Fin n → S) (Stop : S → Prop)
    (nom : S → Fin n → Bool) :
    S → List (Fin n) → Nat
  | _, [] => 0
  | x, e :: w =>
      if Stop x then 0
      else indicator (nom x e) +
        nominatedWord next Stop nom (next x e) w

/-- The stopped nomination count is at most 1/m of the stopped cost,
    at each finite horizon, under a pre-state per-row cardinality bound. -/
theorem nominated_numerator_le {S : Type} {n : Nat}
    (next : S → Fin n → S) (Stop : S → Prop)
    (nom : S → Fin n → Bool) (Inv : S → Prop) (m : Nat)
    (hinv : ∀ x e, Inv x → ¬ Stop x → Inv (next x e))
    (hcard : ∀ x, Inv x → ¬ Stop x →
      m * ((List.finRange n).countP (fun e => nom x e)) ≤ n)
    (x : S) (hx : Inv x) (T : Nat) :
    m * scheduleSum n T (nominatedWord next Stop nom x) ≤
      costNumerator next Stop x T := by
  classical
  have hmain : ∀ t : Nat, ∀ y : S, Inv y →
      m * scheduleSum n t (nominatedWord next Stop nom y) ≤
        costNumerator next Stop y t := by
    intro t
    induction t with
    | zero =>
        intro y hy
        simp [sharpScheduleSum_zero, nominatedWord, costNumerator_zero]
    | succ t ih =>
        intro y hy
        by_cases hstop : Stop y
        · have hzero :
              scheduleSum n (t + 1) (nominatedWord next Stop nom y) = 0 := by
            have hstep (e : Fin n) :
                scheduleSum n t
                  (fun w => nominatedWord next Stop nom y (e :: w)) = 0 := by
              have hf :
                  (fun w => nominatedWord next Stop nom y (e :: w)) =
                    (fun _ => 0) := by
                funext w
                simp only [nominatedWord, if_pos hstop]
              rw [hf, sharpScheduleSum_const]
              simp
            calc
              scheduleSum n (t + 1) (nominatedWord next Stop nom y) =
                  (List.ofFn (fun e : Fin n =>
                    scheduleSum n t
                      (fun w => nominatedWord next Stop nom y (e :: w)))).sum :=
                sharpScheduleSum_succ t _
              _ = (List.ofFn (fun _ : Fin n => 0)).sum :=
                ofFn_sum_eq _ _ hstep
              _ = 0 := by rw [ofFn_sum_const]; simp
          rw [hzero]
          exact Nat.zero_le _
        · have hdecomp :
              scheduleSum n (t + 1) (nominatedWord next Stop nom y) =
                n ^ t * (List.ofFn (fun e : Fin n =>
                  indicator (nom y e))).sum +
                (List.ofFn (fun e : Fin n =>
                  scheduleSum n t
                    (nominatedWord next Stop nom (next y e)))).sum := by
            rw [sharpScheduleSum_succ]
            have hrow (e : Fin n) :
                scheduleSum n t
                    (fun w => nominatedWord next Stop nom y (e :: w)) =
                  n ^ t * indicator (nom y e) +
                    scheduleSum n t
                      (nominatedWord next Stop nom (next y e)) := by
              have hf :
                  (fun w => nominatedWord next Stop nom y (e :: w)) =
                    (fun w => indicator (nom y e) +
                      nominatedWord next Stop nom (next y e) w) := by
                funext w
                simp only [nominatedWord, if_neg hstop]
              rw [hf, sharpScheduleSum_add, sharpScheduleSum_const]
            rw [ofFn_sum_eq _ _ hrow, ofFn_sum_add,
              ofFn_sum_mul_left]
          have hcard' :
              m * (List.ofFn (fun e : Fin n =>
                indicator (nom y e))).sum ≤ n := by
            rw [sharpNominationCount (fun e : Fin n => nom y e)]
            exact hcard y hy hstop
          have hfirst :
              n ^ t * (m * (List.ofFn (fun e : Fin n =>
                indicator (nom y e))).sum) ≤ n ^ (t + 1) := by
            calc
              _ ≤ n ^ t * n := Nat.mul_le_mul_left _ hcard'
              _ = n ^ (t + 1) := by rw [Nat.pow_succ]
          have htail :
              m * (List.ofFn (fun e : Fin n =>
                scheduleSum n t
                  (nominatedWord next Stop nom (next y e)))).sum ≤
                (List.ofFn (fun e : Fin n =>
                  costNumerator next Stop (next y e) t)).sum := by
            have hs := ofFn_sum_le
              (fun e : Fin n => m * scheduleSum n t
                (nominatedWord next Stop nom (next y e)))
              (fun e : Fin n => costNumerator next Stop (next y e) t)
              (fun e => ih (next y e) (hinv y e hy hstop))
            rwa [ofFn_sum_mul_left] at hs
          calc
            m * scheduleSum n (t + 1)
                (nominatedWord next Stop nom y) =
                n ^ t * (m * (List.ofFn (fun e : Fin n =>
                  indicator (nom y e))).sum) +
                m * (List.ofFn (fun e : Fin n =>
                  scheduleSum n t
                    (nominatedWord next Stop nom (next y e)))).sum := by
              rw [hdecomp, Nat.mul_add]
              ac_rfl
            _ ≤ n ^ (t + 1) +
                  (List.ofFn (fun e : Fin n =>
                    costNumerator next Stop (next y e) t)).sum :=
              Nat.add_le_add hfirst htail
            _ = costNumerator next Stop y (t + 1) :=
              (costNumerator_succ next Stop y hstop t).symm
  exact hmain T x hx

/-- The numerator-level sharp charge composes with origin rarity without
    any independence assumption or future-stop conditioning. -/
theorem origin_counting_sharp_le {S O : Type} {n : Nat}
    (next : S → Fin n → S) (Stop : S → Prop)
    (spawn : S → Fin n → List O) (win : O → List (Fin n) → Bool)
    (num den : Nat) (hrare : OriginRarity Stop spawn win num den)
    (x : S) (cnum cden J B : Nat)
    (hcharge : ∀ T,
      cden * originsNumerator next Stop spawn x T ≤
        cden * (n ^ T * J) +
          cnum * costNumerator next Stop x T)
    (hcost : ∀ T, costNumerator next Stop x T ≤ n ^ T * B) :
    ∀ T,
      (den * cden) *
          originEventNumerator next Stop spawn win x T ≤
        num * (n ^ T * (cden * J + cnum * B)) := by
  intro T
  have hrareT :=
    origin_counting_le next Stop spawn win num den hrare x T
  have hcharged :
      cden * originsNumerator next Stop spawn x T ≤
        n ^ T * (cden * J + cnum * B) := by
    calc
      cden * originsNumerator next Stop spawn x T ≤
          cden * (n ^ T * J) +
            cnum * costNumerator next Stop x T := hcharge T
      _ ≤ cden * (n ^ T * J) + cnum * (n ^ T * B) :=
        Nat.add_le_add_left (Nat.mul_le_mul_left cnum (hcost T)) _
      _ = n ^ T * (cden * J + cnum * B) := by
        rw [Nat.mul_add]
        ac_rfl
  calc
    (den * cden) * originEventNumerator next Stop spawn win x T =
        cden * (den * originEventNumerator next Stop spawn win x T) := by
      ac_rfl
    _ ≤ cden * (num * originsNumerator next Stop spawn x T) :=
      Nat.mul_le_mul_left cden hrareT
    _ = num * (cden * originsNumerator next Stop spawn x T) := by
      ac_rfl
    _ ≤ num * (n ^ T * (cden * J + cnum * B)) :=
      Nat.mul_le_mul_left num hcharged

end L3.Prob

namespace L3.HeadlineRenewal

set_option autoImplicit false
set_option Elab.async false

open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree
open PPL.Convergence.LDLocal (retryCount)

/-- Sharp F.1 charge (T2.1): average origins ≤ n + (cnum/cden)
    times average stopped reference cost, in crossed numerators. -/
def ReferenceOriginChargeSharp {n : Nat} (ring : DirectedRing n)
    (D : RootedReferenceData ring) (cnum cden : Nat) : Prop :=
  ∀ seed : RootedSeed ring,
    ¬ headlineGeneratedTarget ring seed.val → ∀ T : Nat,
      cden * Prob.originsNumerator D.referenceNext D.referenceStop
        D.spawn (D.referenceStart seed) T ≤
        cden * (n ^ T * n) +
          cnum * costNumerator D.referenceNext D.referenceStop
            (D.referenceStart seed) T

structure RootedReferenceCertificateSharp {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (D : RootedReferenceData ring) (A K cnum cden : Nat) : Prop where
  domination : ReferenceAttemptDomination ring hn D
  coverage : ReferenceRetryCoverage ring hn D
  charge : ReferenceOriginChargeSharp ring D cnum cden
  rarity : Prob.OriginRarity D.referenceStop D.spawn D.win 1 (2 ^ K)
  clock : ReferenceClock ring D A

private theorem sharpCeilingLeOfMul (a d R : Nat)
    (hd : 0 < d) (h : a ≤ d * R) :
    Prob.ceilNat a d ≤ R := by
  have he : d * (a / d) + a % d = a := by
    simpa only [Nat.mul_comm] using Nat.div_add_mod a d
  have hmul : d * (a / d) ≤ d * R := by omega
  have hquot : a / d ≤ R := Nat.le_of_mul_le_mul_left hmul hd
  by_cases hz : a % d = 0
  · simpa only [Prob.ceilNat, if_pos hz, Nat.add_zero] using hquot
  · have hne : a / d ≠ R := by
      intro hh
      rw [hh] at he
      omega
    have hsucc : a / d + 1 ≤ R := by omega
    simpa only [Prob.ceilNat, if_neg hz] using hsucc

/-- Sharp retry factor num/den, with
    num = cden*n + cnum*(A*n^2), den = 2^K*cden. -/
theorem rootedCostFromReferenceSharp {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (D : RootedReferenceData ring) (A K cnum cden R : Nat)
    (h : RootedReferenceCertificateSharp ring hn D A K cnum cden)
    (hrho : cden * n + cnum * (A * n ^ 2) < 2 ^ K * cden)
    (hreserve :
      (A * n ^ 2) * (2 ^ K * cden) ≤
        (2 ^ K * cden -
          (cden * n + cnum * (A * n ^ 2))) * (R * n ^ 2)) :
    ∀ C : HeadlineConfiguration n, headlineRooted ring C → ∀ T : Nat,
      costNumerator (headlinePhysicalNext ring)
        (headlineGeneratedTarget ring) C T ≤ n ^ T * (R * n ^ 2) := by
  classical
  have hsimulation :
      Prob.RetrySimulation (referenceKernel ring hn D)
        (headlinePhysicalNext ring) (headlineGeneratedTarget ring)
        (rootedTrialRelation (H := D.Memory) ring) :=
    rootedTrialSimulation ring hn D.initialMemory D.memoryNext D.cut
  have hattempt : ∀ seed : RootedSeed ring,
      (referenceKernel ring hn D).valid seed → ∀ T : Nat,
      costNumerator
        (Prob.attemptStepper (referenceKernel ring hn D))
        (fun z => Prob.attemptGood z ∨ Prob.attemptFail z)
        (.active ((referenceKernel ring hn D).start seed)) T ≤
          n ^ T * (A * n ^ 2) := by
    intro seed hvalid T
    exact Nat.le_trans
      (referenceAttemptCost ring hn D h.domination seed hvalid T)
      (h.clock seed hvalid T)
  have hretry : ∀ seed : RootedSeed ring,
      (referenceKernel ring hn D).valid seed → ∀ T : Nat,
      (2 ^ K * cden) *
        retryCount (referenceKernel ring hn D)
          (.active ((referenceKernel ring hn D).start seed)) T ≤
        (cden * n + cnum * (A * n ^ 2)) * n ^ T := by
    intro seed hvalid T
    have hcover :=
      referenceRetryCount ring hn D h.coverage seed hvalid T
    have hmass := Prob.origin_counting_sharp_le
      D.referenceNext D.referenceStop D.spawn D.win
      1 (2 ^ K) h.rarity (D.referenceStart seed)
      cnum cden n (A * n ^ 2)
      (h.charge seed hvalid) (h.clock seed hvalid)
    calc
      (2 ^ K * cden) *
          retryCount (referenceKernel ring hn D)
            (.active ((referenceKernel ring hn D).start seed)) T ≤
        (2 ^ K * cden) *
          Prob.originEventNumerator D.referenceNext D.referenceStop
            D.spawn D.win (D.referenceStart seed) T :=
        Nat.mul_le_mul_left _ hcover
      _ ≤ 1 * (n ^ T * (cden * n + cnum * (A * n ^ 2))) :=
        hmass T
      _ = (cden * n + cnum * (A * n ^ 2)) * n ^ T := by
        simp only [Nat.one_mul]
        ac_rfl
  have hceil :
      Prob.renewalCeiling
        (A * n ^ 2)
        (cden * n + cnum * (A * n ^ 2))
        (2 ^ K * cden) ≤ R * n ^ 2 := by
    change Prob.ceilNat
      ((A * n ^ 2) * (2 ^ K * cden))
      (2 ^ K * cden -
        (cden * n + cnum * (A * n ^ 2))) ≤ R * n ^ 2
    exact sharpCeilingLeOfMul _ _ _ (by omega) hreserve
  intro C hC T
  by_cases hterminal : headlineGeneratedTarget ring C
  · rw [costNumerator_terminal (headlinePhysicalNext ring)
      (headlineGeneratedTarget ring) C hterminal T]
    exact Nat.zero_le _
  · have hcost := Prob.costNumerator_renewal_le
      (headlinePhysicalNext ring) (headlineGeneratedTarget ring)
      (referenceKernel ring hn D)
      (rootedTrialRelation (H := D.Memory) ring)
      hsimulation
      (A * n ^ 2)
      (cden * n + cnum * (A * n ^ 2))
      (2 ^ K * cden) hrho hattempt hretry
      C (⟨C, hC⟩ : RootedSeed ring) hterminal rfl T
    exact Nat.le_trans hcost
      (Nat.mul_le_mul_left (n ^ T) hceil)

end L3.HeadlineRenewal

namespace UniformFirstHit

set_option autoImplicit false
set_option Elab.async false

open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

/-- Finite-word tower inequality: after any surviving prefix of length b,
    a further m-letter block succeeds with probability at least 1/2. -/
private theorem sharpSurvivalBlockStep {S : Type} {n : Nat}
    (next : S → Fin n → S) (P : S → Prop) (m : Nat)
    (hblock : ∀ y : S,
      2 * survivalNumerator next P y m ≤ n ^ m) :
    ∀ (x : S) (b : Nat),
      2 * survivalNumerator next P x (b + m) ≤
        n ^ m * survivalNumerator next P x b := by
  classical
  intro x b
  induction b generalizing x with
  | zero =>
      by_cases hp : P x
      · rw [Nat.zero_add,
          survivalNumerator_of_target next P x hp m,
          survivalNumerator_of_target next P x hp 0]
        simp
      · rw [Nat.zero_add,
          survivalNumerator_zero_of_not next P x hp]
        simpa only [Nat.mul_one] using hblock x
  | succ b ih =>
      by_cases hp : P x
      · rw [survivalNumerator_of_target next P x hp (b + 1 + m),
          survivalNumerator_of_target next P x hp (b + 1)]
        simp
      · rw [show b + 1 + m = b + m + 1 by omega,
          survivalNumerator_succ_of_not next P x hp (b + m),
          survivalNumerator_succ_of_not next P x hp b]
        have hs := ofFn_sum_le
          (fun e : Fin n =>
            2 * survivalNumerator next P (next x e) (b + m))
          (fun e : Fin n =>
            n ^ m * survivalNumerator next P (next x e) b)
          (fun e => ih (next x e))
        rwa [ofFn_sum_mul_left, ofFn_sum_mul_left] at hs

/-- Block tail from a uniform half-success bound at all actual states. -/
theorem survival_blocks_le {S : Type} {n : Nat}
    (next : S → Fin n → S) (P : S → Prop)
    (hn : 0 < n) (m : Nat)
    (hblock : ∀ y : S,
      2 * survivalNumerator next P y m ≤ n ^ m) :
    ∀ (x : S) (k : Nat),
      2 ^ k * survivalNumerator next P x (m * k) ≤
        n ^ (m * k) := by
  classical
  intro x k
  induction k with
  | zero =>
      have hf : survivalNumerator next P x 0 ≤ 1 := by
        by_cases hp : P x
        · rw [survivalNumerator_of_target next P x hp 0]
          omega
        · rw [survivalNumerator_zero_of_not next P x hp]
          exact Nat.le_refl 1
      simpa using hf
  | succ k ih =>
      have hs :=
        sharpSurvivalBlockStep next P m hblock x (m * k)
      calc
        2 ^ (k + 1) *
            survivalNumerator next P x (m * (k + 1)) =
          2 ^ k *
            (2 * survivalNumerator next P x (m * k + m)) := by
            rw [Nat.mul_succ, Nat.pow_succ]
            ac_rfl
        _ ≤ 2 ^ k *
              (n ^ m * survivalNumerator next P x (m * k)) :=
          Nat.mul_le_mul_left _ hs
        _ = n ^ m *
              (2 ^ k * survivalNumerator next P x (m * k)) := by
          ac_rfl
        _ ≤ n ^ m * n ^ (m * k) :=
          Nat.mul_le_mul_left _ ih
        _ = n ^ (m * (k + 1)) := by
          rw [Nat.mul_succ, Nat.pow_add]
          ac_rfl

/-- The sum of a zero vector of length `m`. -/
private theorem sharpSumOfFnZero (m : Nat) :
    (List.ofFn (fun _ : Fin m => (0 : Nat))).sum = 0 := by
  induction m with
  | zero => rfl
  | succ m ih =>
      rw [List.ofFn_succ, List.sum_cons, ih]

/-- Uniform mean B at every state gives probability at most 2^(-k)
    of surviving k consecutive blocks of length 2B. Includes B=0. -/
theorem survivalProb_blocks_of_expected {S : Type} {n : Nat}
    (next : S → Fin n → S) (P : S → Prop)
    (hn : 0 < n) (B : Nat)
    (hmean : ∀ y : S,
      ExpectedHittingTimeAtMost next P y (B : Rat)) :
    ∀ (x : S) (k : Nat),
      (2 : Rat) ^ k * survivalProb next P x (2 * B * k) ≤ 1 := by
  classical
  have hcost (y : S) (T : Nat) :
      costNumerator next P y T ≤ n ^ T * B :=
    (expectedHittingTimeAtMost_iff_cost next P hn y B).1 (hmean y) T
  have hblock : ∀ y : S,
      2 * survivalNumerator next P y (2 * B) ≤ n ^ (2 * B) := by
    intro y
    by_cases hzero : B = 0
    · have hy : P y := by
        refine Classical.byContradiction (fun hnot => ?_)
        have hone : costNumerator next P y 1 = n := by
          rw [show 1 = 0 + 1 by omega,
              costNumerator_succ next P y hnot 0]
          simp [costNumerator_zero]
          exact sharpSumOfFnZero n
        have hz : n ≤ 0 := by
          have hb := hcost y 1
          rw [hone, hzero] at hb
          simpa using hb
        omega
      rw [hzero]
      simp [survivalNumerator_of_target next P y hy 0]
    · have hpos : 0 < B := by omega
      have hm := survival_mul_le_cost next P y (2 * B)
      have hc := hcost y (2 * B)
      have hs :
          B * (2 * survivalNumerator next P y (2 * B)) ≤
            B * n ^ (2 * B) := by
        calc
          B * (2 * survivalNumerator next P y (2 * B)) =
              (2 * B) * survivalNumerator next P y (2 * B) := by
            ac_rfl
          _ ≤ costNumerator next P y (2 * B) := hm
          _ ≤ n ^ (2 * B) * B := hc
          _ = B * n ^ (2 * B) := by ac_rfl
      exact Nat.le_of_mul_le_mul_left hs hpos
  intro x k
  have hnats :=
    survival_blocks_le next P hn (2 * B) hblock x k
  have hrat :=
    (survivalProb_bound_iff next P hn x (2 ^ k) (2 * B * k)).2 hnats
  simpa only [Rat.natCast_pow, Rat.natCast_ofNat] using hrat

end UniformFirstHit
