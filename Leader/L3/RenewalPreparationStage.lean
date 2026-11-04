import Leader.L3.RenewalReferenceClock

/-!
BANK reference candidate preparation.

The decorated reference suppresses only the OLD request/grant
owner of fresh BANK production. Its native/candidate projection
is the literal birth-free candidate step after authority extinction
and grant drain. All clock statements below are first-hit statements
on the original valid BANK reference scheduler.
-/

namespace L3.RenewalReferenceClock

open L3.HeadlineRenewal
open L3.ReferencePreparationTrail
open L3.ReferencePreparationCandidate
open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree

set_option autoImplicit false
set_option Elab.async false

/-- The same sitewise candidate projection that was certified in
ReferencePreparation, on the original stamped BANK reference. -/
def bankValidCandidateView {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank) : Fin n → NativeCand :=
  physicalCandidates z.val.1

/-- This is an exact non-token projection. The masked row changes
only request and grant; in particular SAN/K2/PROM/DP and the
native E fields are not re-evaluated under the mask. -/
theorem bankMaskedCandidatePairFrame
    (c : Compiled) (suppress : Bool) (x y : Agent c) :
    NativeCand.ofAgent (renewalMaskedPair c suppress x y).1 =
      NativeCand.ofAgent (transition c x y).1 ∧
    NativeCand.ofAgent (renewalMaskedPair c suppress x y).2 =
      NativeCand.ofAgent (transition c x y).2 := by
  cases suppress <;> exact ⟨rfl, rfl⟩

/-- Congruence of a map through a two-level if on a plain type.
Stated generically so that no branch mentions a configuration
(rewriting the if inside a HeadlineConfiguration term fails). -/
private theorem bankCandIteTwoFrame {A B : Type} (f : A → B)
    (P Q : Prop) [Decidable P] [Decidable Q] (x x' y y' z : A)
    (hx : f x = f x') (hy : f y = f y') :
    f (if P then x else if Q then y else z) =
      f (if P then x' else if Q then y' else z) := by
  by_cases hp : P
  · rw [if_pos hp, if_pos hp]
    exact hx
  · rw [if_neg hp, if_neg hp]
    by_cases hq : Q
    · rw [if_pos hq, if_pos hq]
      exact hy
    · rw [if_neg hq, if_neg hq]

/-- The candidate analogue of renewalBankMaskedNativeFrame.
The explicit if expression is on the actual finite-index
function, not a rewrite of headlinePhysicalNext. -/
theorem bankMaskedCandidateFrame {n : Nat}
    (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (e : Fin n) (suppress : Bool) :
    physicalCandidates (renewalMaskedStep ring C e suppress) =
      physicalCandidates (headlinePhysicalNext ring C e) := by
  cases suppress with
  | false =>
      exact congrArg physicalCandidates
        (renewalMaskedStepOff ring C e)
  | true =>
      have hframe :
          physicalCandidates (renewalMaskedStep ring C e true) =
            physicalCandidates (renewalMaskedStep ring C e false) := by
        funext i
        change NativeCand.ofAgent
            (if i = e then
              (renewalMaskedPair (compileAdvice (ceilLogTwo n)) true
                (C e) (C (ring.rightNeighbor e))).1
             else if i = ring.rightNeighbor e then
              (renewalMaskedPair (compileAdvice (ceilLogTwo n)) true
                (C e) (C (ring.rightNeighbor e))).2
             else C i) =
          NativeCand.ofAgent
            (if i = e then
              (renewalMaskedPair (compileAdvice (ceilLogTwo n)) false
                (C e) (C (ring.rightNeighbor e))).1
             else if i = ring.rightNeighbor e then
              (renewalMaskedPair (compileAdvice (ceilLogTwo n)) false
                (C e) (C (ring.rightNeighbor e))).2
             else C i)
        exact bankCandIteTwoFrame NativeCand.ofAgent _ _ _ _ _ _ _
          (bankMaskedCandidatePairFrame
            (compileAdvice (ceilLogTwo n)) true
            (C e) (C (ring.rightNeighbor e))).1
          (bankMaskedCandidatePairFrame
            (compileAdvice (ceilLogTwo n)) true
            (C e) (C (ring.rightNeighbor e))).2
      have hoff := renewalMaskedStepOff ring C e
      rw [hoff] at hframe
      exact hframe

theorem bankReferenceCandidateFrame {n : Nat}
    (ring : DirectedRing n)
    (r : RenewalBankReference n) (e : Fin n) :
    physicalCandidates (renewalBankNext ring r e).1 =
      physicalCandidates (headlinePhysicalNext ring r.1 e) := by
  exact bankMaskedCandidateFrame ring r.1 e
    (renewalBankCut ring r.1 r.2 e)

/-- Validity is a ghost restriction, not a different physical
selected-edge transition. -/
theorem bankValidCandidateFrame {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank) (e : Fin n) :
    bankValidCandidateView ring hbank
        ((bankValidRootedReferenceData ring hbank).referenceNext z e) =
      physicalCandidates (headlinePhysicalNext ring z.val.1 e) := by
  change physicalCandidates (renewalBankNext ring z.val e).1 =
    physicalCandidates (headlinePhysicalNext ring z.val.1 e)
  exact bankReferenceCandidateFrame ring z.val e

/-- No-FIRE at any current grant-free reference cut, using only
the physical OLD grant guard. This holds independently of
unrestricted request and candidate fields. -/
theorem bankPostInheritedNoFireOn {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank)
    (hz : BankPostInheritedGrantDrain ring hbank z)
    (e : Fin n) :
    NativeLiftNoFireOn ring z.val.1 e := by
  exact (bankAfterGrantDrainNoFire ring hbank z hz.1) e

/-- The reference's exact candidate successor is Phi_e after
inherited-authority extinction and grant drain. The no-FIRE
projection is proved for the unmasked physical step first;
the BANK mask is then eliminated by its candidate frame. -/
theorem bankPostInheritedCandidateStep {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank)
    (hz : BankPostInheritedGrantDrain ring hbank z)
    (e : Fin n) :
    bankValidCandidateView ring hbank
        ((bankValidRootedReferenceData ring hbank).referenceNext z e) =
      birthFreeCandidateStep ring
        (bankValidCandidateView ring hbank z) e := by
  have hphysical := noFirePhysicalStep hn ring z.val.1 e
    (bankPostInheritedNoFireOn ring hbank z hz e)
  exact (bankValidCandidateFrame ring hbank z e).trans hphysical

/-- The exact birth-free candidate projection of the whole
post-inherited singleton class. No extra C_native or H_cand
premise is imposed on the start. -/
theorem bankPostInheritedSingletonCandidateStep {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (root : Fin n) (z : BankReferenceState ring hbank)
    (hz : BankPostInheritedSingleton ring hbank root z)
    (e : Fin n) :
    bankValidCandidateView ring hbank
        ((bankValidRootedReferenceData ring hbank).referenceNext z e) =
      birthFreeCandidateStep ring
        (bankValidCandidateView ring hbank z) e := by
  exact bankPostInheritedCandidateStep ring hn hbank z hz.1 e

/-- Its first native component is the already native view. -/
theorem bankValidCandidateNativeView {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank) :
    candidateNative (bankValidCandidateView ring hbank z) =
      renewalBankValidNativeView ring hbank z := by
  rfl

/-- Abstract projected first-hit equality over ANY closed
valid-reference subclass. It is an equality of finite-horizon
numerators on the same IID edge alphabet, not only of means
or of isolated successful words. -/
theorem bankCandidateProjectedCostNumerator {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (P : (Fin n → NativeCand) → Prop)
    (H : BankReferenceState ring hbank → Prop)
    (hstep : ∀ z, H z → ∀ e : Fin n,
      bankValidCandidateView ring hbank
        ((bankValidRootedReferenceData ring hbank).referenceNext z e) =
        birthFreeCandidateStep ring
          (bankValidCandidateView ring hbank z) e)
    (hclosed : ∀ z, H z → ∀ e : Fin n,
      H ((bankValidRootedReferenceData ring hbank).referenceNext z e)) :
    ∀ T (z : BankReferenceState ring hbank), H z →
      costNumerator
          (bankValidRootedReferenceData ring hbank).referenceNext
          (fun a => P (bankValidCandidateView ring hbank a)) z T =
        costNumerator (birthFreeCandidateStep ring) P
          (bankValidCandidateView ring hbank z) T := by
  classical
  intro T
  induction T with
  | zero =>
      intro z _
      simp only [costNumerator_zero]
  | succ T ih =>
      intro z hz
      by_cases hp : P (bankValidCandidateView ring hbank z)
      · rw [costNumerator_terminal
          (bankValidRootedReferenceData ring hbank).referenceNext
          (fun a => P (bankValidCandidateView ring hbank a))
          z hp (T + 1),
          costNumerator_terminal (birthFreeCandidateStep ring)
            P (bankValidCandidateView ring hbank z) hp (T + 1)]
      · rw [costNumerator_succ
          (bankValidRootedReferenceData ring hbank).referenceNext
          (fun a => P (bankValidCandidateView ring hbank a))
          z hp T,
          costNumerator_succ (birthFreeCandidateStep ring)
            P (bankValidCandidateView ring hbank z) hp T]
        congr 1
        exact ofFn_sum_eq _ _ (fun e => by
          have hh := ih
            ((bankValidRootedReferenceData ring hbank).referenceNext z e)
            (hclosed z hz e)
          rw [hstep z hz e] at hh
          exact hh)

/-- One-leader native preparedness with all bullets absent and
all signals one is in C_native. The proof includes the literal
I-sector uniqueness and trail clauses, not merely a signal shape.
No shield assumption is needed because there is no live bullet. -/
theorem bankNativePreparedClean {n : Nat}
    (hn : 5 ≤ n) (ring : DirectedRing n)
    (root : Fin n) (N : TripleNativeState n)
    (h : ReferencePreparationNativePreparedAt root N) :
    C_native ring N := by
  have hbullet (i : Fin n) :
      (N i).b = (0 : Fin 3) := (h.2.2 i).1
  have hsignal (i : Fin n) :
      (N i).sg = true := (h.2.2 i).2
  have hplus : PPlus ring N := by
    refine ⟨⟨root, h.1⟩, ?_⟩
    intro v hv
    have hb : (0 : Fin 3) ≠ (2 : Fin 3) := by decide
    exact False.elim (hb ((hbullet v).symm.trans hv))
  refine ⟨⟨hplus, ?_⟩, ?_⟩
  · intro p d _
    constructor
    · intro a b _ _ ha _
      exact False.elim (ha (hbullet _))
    · intro a _ ha k _
      exact False.elim (ha (hbullet _))
  · intro p d hd
    right
    refine ⟨?_, ?_, ?_⟩
    · intro k _ hk
      exact hk (hbullet _)
    · refine ⟨⟨1, by omega⟩, Nat.le_refl 1, hd.1, ?_, ?_⟩
      · intro k hk hcut
        have hk1 : k.val < 1 := hcut
        exact False.elim (by omega : False)
      · intro k _ _
        exact hsignal _
    · intro _ k _ _
      exact hsignal _

/-- The candidate target implies the full native clean factor
and the empty generated-candidate subfamily, not only the native
all-one cut. This holds at the literal physical reference state. -/
theorem bankCandidateTargetPreparedCore {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (root : Fin n) (z : BankReferenceState ring hbank)
    (hz : BankPostInheritedSingleton ring hbank root z)
    (htarget : CandidateReturnTarget root
      (bankValidCandidateView ring hbank z)) :
    ReferencePreparationPreparedCore ring z.val.1 ∧
      InheritedAuthorityExtinct ring hbank z ∧
      H_cand ring (bankValidCandidateView ring hbank z) := by
  have hnative :
      ReferencePreparationNativePreparedAt root
        (nativeProjection z.val.1) := htarget.1
  have hclean : C_native ring (nativeProjection z.val.1) :=
    bankNativePreparedClean hn ring root
      (nativeProjection z.val.1) hnative
  have hprotected : Protected ring (nativeProjection z.val.1) :=
    hclean.1.1
  have hcore : ReferencePreparationPreparedCore ring z.val.1 :=
    nativePreparedPhysicalCandidateHandoff ring root z.val.1
      hnative hprotected hz.1.1.2 hclean htarget.2
  exact ⟨hcore, hz.1.2,
    referencePreparation_prepared_has_candidate_history ring z.val.1 hcore⟩

/-- Sharper, unrounded H.1 finite-horizon budget for the actual
valid BANK reference after sigma_G and sigma_1. The singleton
class is the suffix-closed one, and all candidate fields
are arbitrary on entry. -/
theorem bankPostInheritedCandidatePreparationDoubledCost {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (root : Fin n) (z : BankReferenceState ring hbank)
    (hz : BankPostInheritedSingleton ring hbank root z)
    (T : Nat) :
    2 * costNumerator
      (bankValidRootedReferenceData ring hbank).referenceNext
      (fun a => CandidateReturnTarget root
        (bankValidCandidateView ring hbank a)) z T ≤
      n ^ T * (10 * n ^ 2 + n) := by
  have hcost := bankCandidateProjectedCostNumerator
    ring hbank (CandidateReturnTarget root)
    (BankPostInheritedSingleton ring hbank root)
    (fun a ha e => bankPostInheritedSingletonCandidateStep
      ring hn hbank root a ha e)
    (bankPostInheritedSingletonClosed ring hn hbank root)
    T z hz
  rw [hcost]
  have hroot :
      Rooted ring root
        (candidateNative (bankValidCandidateView ring hbank z)) := by
    rw [bankValidCandidateNativeView ring hbank z]
    exact hz.2
  exact candidateSingletonPreparationDoubledCost hn ring root
    (bankValidCandidateView ring hbank z) hroot T

/-- The requested sigma_p stage in the precise StageReferencePreparation
interface of renewalBankReferenceClockOfStages. The stage includes
native readiness AND EmptyCandidates, on the SAME reference cut. -/
theorem bankPostInheritedCandidatePreparationStage {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (root : Fin n) :
    StageReferencePreparation
      (bankValidRootedReferenceData ring hbank).referenceNext
      (BankPostInheritedSingleton ring hbank root)
      (fun z => CandidateReturnTarget root
        (bankValidCandidateView ring hbank z)) := by
  intro z hz
  apply (UniformFirstHit.expectedHittingTimeAtMost_iff_cost
    (bankValidRootedReferenceData ring hbank).referenceNext
    (fun a => CandidateReturnTarget root
      (bankValidCandidateView ring hbank a))
    (by omega : 0 < n) z (6 * n ^ 2)).2
  intro T
  exact renewalBankDoubledPreparationSix n T
    (costNumerator
      (bankValidRootedReferenceData ring hbank).referenceNext
      (fun a => CandidateReturnTarget root
        (bankValidCandidateView ring hbank a)) z T)
    (by omega : 1 ≤ n)
    (bankPostInheritedCandidatePreparationDoubledCost
      ring hn hbank root z hz T)

/-- The singleton suffix class is stable along any actually
revealed reference word, with no presumed last grant-producing
service chosen in hindsight. -/
theorem bankPostInheritedSingletonWordClosed {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (root : Fin n) :
    ∀ (edges : List (Fin n)) (z : BankReferenceState ring hbank),
      BankPostInheritedSingleton ring hbank root z →
      BankPostInheritedSingleton ring hbank root
        (bankValidAuthorityRun ring hbank z edges) := by
  intro edges
  induction edges with
  | nil =>
      intro z hz
      exact hz
  | cons e es ih =>
      intro z hz
      change BankPostInheritedSingleton ring hbank root
        (bankValidAuthorityRun ring hbank
          ((bankValidRootedReferenceData ring hbank).referenceNext z e) es)
      exact ih
        ((bankValidRootedReferenceData ring hbank).referenceNext z e)
        (bankPostInheritedSingletonClosed ring hn hbank root z hz e)

/-- At any actually stopped sigma_p reference word, the native
clean singleton, grant-free physical state, candidate-zero class,
generated H_cand history, and inherited-authority extinction
hold simultaneously. There is no additional endpoint C_native
assumption or replacement process. -/
theorem bankPostInheritedCandidatePreparedWord {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (root : Fin n)
    (z : BankReferenceState ring hbank)
    (hz : BankPostInheritedSingleton ring hbank root z)
    (edges : List (Fin n))
    (htarget : CandidateReturnTarget root
      (bankValidCandidateView ring hbank
        (bankValidAuthorityRun ring hbank z edges))) :
    ReferencePreparationPreparedCore ring
        (bankValidAuthorityRun ring hbank z edges).val.1 ∧
      InheritedAuthorityExtinct ring hbank
        (bankValidAuthorityRun ring hbank z edges) ∧
      H_cand ring (bankValidCandidateView ring hbank
        (bankValidAuthorityRun ring hbank z edges)) := by
  exact bankCandidateTargetPreparedCore ring hn hbank root
    (bankValidAuthorityRun ring hbank z edges)
    (bankPostInheritedSingletonWordClosed
      ring hn hbank root edges z hz) htarget

end L3.RenewalReferenceClock


/-!
Composable BANK sigma_1 and sigma_p endpoints and
small same-reference wrappers.

The two endpoint targets explicitly retain the suffix-closed
post-inherited invariant; target strengthening costs no further
first-hit time on that closed class. The initial entrance is a
genuine rooted seed, not an arbitrary timestamp-valid ghost.
-/

namespace L3.RenewalReferenceClock

open L3.HeadlineRenewal
open L3.ReferencePreparationTrail
open L3.ReferencePreparationCandidate
open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree
open Classical

set_option autoImplicit false
set_option Elab.async false

/-! L1: OLD fresh-payer identity and live worker membership. -/

/-- A real suppressed BANK success has no inherited entrance atom
in either of its OLD payer records, and the worker has a completed
origin. This does not imply any quantitative K-head statement. -/
theorem rbCutFreshPayload {n : Nat}
    (ring : DirectedRing n)
    (r : RenewalBankReference n) (e : Fin n)
    (hcut : renewalBankCut ring r.1 r.2 e = true) :
    ∃ p : RenewalBankPayload n, ∃ o : RenewalBankOrigin n,
      (r.2.sites e).controller = .waiting [] ∧
      (r.2.sites (ring.rightNeighbor e)).worker = .payload p ∧
      p.atoms = [] ∧ p.origin = some o := by
  have hf :
      renewalBankFreshPayer (r.2.sites e).controller
        (r.2.sites (ring.rightNeighbor e)).worker = true :=
    by
      unfold renewalBankCut at hcut
      simp only [Bool.and_eq_true] at hcut
      exact hcut.2
  cases hc : (r.2.sites e).controller with
  | empty =>
      simp [renewalBankFreshPayer, hc] at hf
  | active p =>
      simp [renewalBankFreshPayer, hc] at hf
  | waiting atoms =>
      cases hw : (r.2.sites (ring.rightNeighbor e)).worker with
      | empty =>
          simp [renewalBankFreshPayer, hc, hw] at hf
      | pending rho =>
          simp [renewalBankFreshPayer, hc, hw] at hf
      | payload p =>
          cases ha : atoms with
          | nil =>
              cases hb : p.atoms with
              | nil =>
                  cases ho : p.origin with
                  | none =>
                      simp [renewalBankFreshPayer, hc, hw,
                        ha, hb, ho] at hf
                  | some o =>
                      refine ⟨p, o, ?_, ?_, ?_, ?_⟩ <;>
                        first
                        | rfl
                        | exact hw
                        | exact hb
                        | exact ho
                        | (rw [ha] at hc; exact hc)
              | cons a tail =>
                  simp [renewalBankFreshPayer, hc, hw,
                    ha, hb] at hf
          | cons a tail =>
              simp [renewalBankFreshPayer, hc, hw, ha] at hf

/-- A worker payload belongs to the actual two-field live list. -/
theorem rbWorkerPayloadMem {n : Nat}
    (m : RenewalBankMemory n) (i : Fin n)
    (p : RenewalBankPayload n)
    (hw : (m.sites i).worker = .payload p) :
    p ∈ rbLivePayloads m := by
  unfold rbLivePayloads
  apply List.mem_flatMap.mpr
  refine ⟨i, List.mem_finRange i, ?_⟩
  unfold rbSiteLivePayloads
  apply List.mem_append.mpr
  left
  rw [hw]
  simp

/-! L2: actual logged birth and broad-win prefix extraction. -/

/-- Every logged birth was made at a specific OLD selected service
of this exact word. The suffix begins AFTER the creating service. -/
theorem rbBirthMemSplit {n : Nat}
    (ring : DirectedRing n)
    (r : RenewalBankReference n)
    (word : List (Fin n)) (o : RenewalBankOrigin n)
    (ho : o ∈ rbBirths ring r word) :
    ∃ pre : List (Fin n), ∃ e : Fin n, ∃ post : List (Fin n),
      word = pre ++ e :: post ∧
      renewalBankBirth ring
        (rbRun ring r pre).1 (rbRun ring r pre).2 e = some o := by
  revert ho
  induction word generalizing r with
  | nil =>
      intro ho
      simp [rbBirths] at ho
  | cons e tail ih =>
      intro ho
      have ho' := ho
      simp only [rbBirths] at ho'
      rcases List.mem_append.mp ho' with hfirst | htail
      · cases hb : renewalBankBirth ring r.1 r.2 e with
        | none =>
            simp [hb] at hfirst
        | some born =>
            have hbo : o = born := by
              simpa [hb] using hfirst
            subst hbo
            refine ⟨[], e, tail, ?_, ?_⟩
            · rfl
            · simpa only [rbRun] using hb
      · obtain ⟨pre, e', post, hword, hbirth⟩ :=
          ih (renewalBankNext ring r e) htail
        refine ⟨e :: pre, e', post, ?_, ?_⟩
        · simpa only [List.cons_append] using
            congrArg (List.cons e) hword
        · simpa only [rbRun] using hbirth

/-- A K-headed identity at an OLD prefix already wins on the whole
suffix. No stop-time or future-survival condition is imposed. -/
theorem rbWinWordOfReachedPrefix {n : Nat}
    (ring : DirectedRing n)
    (o : RenewalBankOrigin n) (K : Nat)
    (r : RenewalBankReference n)
    (pre suffix : List (Fin n))
    (hhit : renewalBankReached o K (rbRun ring r pre).2 = true) :
    renewalBankWinWord ring o K (pre ++ suffix) r = true := by
  revert hhit
  induction pre generalizing r with
  | nil =>
      intro hhit
      cases suffix with
      | nil =>
          simpa only [List.nil_append, rbRun,
            renewalBankWinWord] using hhit
      | cons e tail =>
          simp only [rbRun] at hhit
          simp only [List.nil_append, renewalBankWinWord, hhit,
            Bool.true_or]
  | cons e tail ih =>
      intro hhit
      have htail : renewalBankReached o K
          (rbRun ring (renewalBankNext ring r e) tail).2 = true := by
        simpa only [rbRun] using hhit
      have hrec := ih (renewalBankNext ring r e) htail
      rw [List.cons_append]
      simp only [renewalBankWinWord, hrec, Bool.or_true]

/-! L3: the valid-subtype projection is not a second process. -/

theorem bankValidAuthorityRunVal {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank)
    (word : List (Fin n)) :
    (bankValidAuthorityRun ring hbank z word).val =
      rbRun ring z.val word := by
  induction word generalizing z with
  | nil =>
      rfl
  | cons e tail ih =>
      change
        (bankValidAuthorityRun ring hbank
          ((bankValidRootedReferenceData ring hbank).referenceNext z e)
          tail).val =
        rbRun ring (renewalBankNext ring z.val e) tail
      exact ih _

private theorem rbValidSuccessfulOriginsProjection {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) :
    ∀ (word : List (Fin n)) (z : BankReferenceState ring hbank),
      Prob.successfulOriginsWord
        (bankValidRootedReferenceData ring hbank).referenceNext
        (bankValidRootedReferenceData ring hbank).referenceStop
        (bankValidRootedReferenceData ring hbank).spawn
        (bankValidRootedReferenceData ring hbank).win z word =
      Prob.successfulOriginsWord
        (renewalBankNext ring) (renewalBankStop ring)
        (renewalBankSpawn ring) (renewalBankWin ring) z.val word := by
  intro word
  induction word with
  | nil =>
      intro z
      rfl
  | cons e tail ih =>
      intro z
      have htail :=
        ih ((bankValidRootedReferenceData ring hbank).referenceNext z e)
      change
        (if renewalBankStop ring z.val then 0 else
          ((renewalBankSpawn ring z.val e).map
            (fun born => Prob.indicator (renewalBankWin ring born tail))).sum +
          Prob.successfulOriginsWord
            (bankValidRootedReferenceData ring hbank).referenceNext
            (bankValidRootedReferenceData ring hbank).referenceStop
            (bankValidRootedReferenceData ring hbank).spawn
            (bankValidRootedReferenceData ring hbank).win
            ((bankValidRootedReferenceData ring hbank).referenceNext z e)
            tail) =
        (if renewalBankStop ring z.val then 0 else
          ((renewalBankSpawn ring z.val e).map
            (fun born => Prob.indicator (renewalBankWin ring born tail))).sum +
          Prob.successfulOriginsWord
            (renewalBankNext ring) (renewalBankStop ring)
            (renewalBankSpawn ring) (renewalBankWin ring)
            (renewalBankNext ring z.val e) tail)
      split
      · rfl
      · exact congrArg (fun v : Nat =>
          ((renewalBankSpawn ring z.val e).map
            (fun born => Prob.indicator (renewalBankWin ring born tail))).sum +
          v) htail

theorem rbValidOriginEventProjection {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : (bankValidRootedReferenceData ring hbank).Reference)
    (word : List (Fin n)) :
    Prob.originEventWord
        (bankValidRootedReferenceData ring hbank).referenceNext
        (bankValidRootedReferenceData ring hbank).referenceStop
        (bankValidRootedReferenceData ring hbank).spawn
        (bankValidRootedReferenceData ring hbank).win z word =
      Prob.originEventWord
        (renewalBankNext ring) (renewalBankStop ring)
        (renewalBankSpawn ring) (renewalBankWin ring)
        z.val word := by
  unfold Prob.originEventWord
  rw [rbValidSuccessfulOriginsProjection ring hbank word z]

/-! L4: zero-cost target strengthening on the actual closed class. -/

theorem costNumeratorTargetOnClosed {m : Nat} {S : Type}
    (next : S → Fin m → S) (I P Q : S → Prop)
    (hstep : ∀ x, I x → ∀ e, I (next x e))
    (hstop : ∀ x, I x → Q x → P x) :
    ∀ T x, I x →
      costNumerator next P x T ≤ costNumerator next Q x T := by
  classical
  intro T
  induction T with
  | zero =>
      intro x hx
      simp only [costNumerator_zero]
      exact Nat.le_refl 0
  | succ T ih =>
      intro x hx
      by_cases hp : P x
      · rw [costNumerator_terminal next P x hp (T + 1)]
        exact Nat.zero_le _
      · have hq : ¬ Q x := by
          intro h
          exact hp (hstop x hx h)
        rw [costNumerator_succ next P x hp T,
          costNumerator_succ next Q x hq T]
        exact Nat.add_le_add_left
          (ofFn_sum_le
            (fun e : Fin m => costNumerator next P (next x e) T)
            (fun e : Fin m => costNumerator next Q (next x e) T)
            (fun e => ih (next x e) (hstep x hx e))) _

/-! L5: sigma_1, with an existential native physical root. -/

theorem nativeLiftSingletonHasRoot {n : Nat}
    (ring : DirectedRing n)
    (N : TripleNativeState n)
    (hprotected : PPlus ring N)
    (hsingle : nativeLiftSingleton N) :
    ∃ root : Fin n,
      ReferencePreparationTrail.Rooted ring root N := by
  have hlen := native_lift_pplus_singleton_exact
    ring N hprotected hsingle
  obtain ⟨root, hlist⟩ := List.length_eq_one_iff.mp hlen
  have hroot : (N root).l = true :=
    (native_lift_leader_sites_mem N root).mp
      (by rw [hlist]; simp)
  have huniq : ∀ i : Fin n, (N i).l = true → i = root := by
    intro i hi
    have hmem := (native_lift_leader_sites_mem N i).mpr hi
    rw [hlist] at hmem
    simpa using hmem
  exact ⟨root, hroot, huniq, hprotected⟩

def BankAnyPostInheritedSingleton {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank) : Prop :=
  ∃ root : Fin n, BankPostInheritedSingleton ring hbank root z

/-- Same 4917*n² sigma_1 cost, but the target keeps rootedness,
grant-freeness and the entire inherited-extinct suffix. -/
theorem bankSingletonStageWithInheritedInvariant {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) :
    StageReferenceSingleton
      (bankValidRootedReferenceData ring hbank).referenceNext
      (BankPostInheritedGrantDrain ring hbank)
      (BankAnyPostInheritedSingleton ring hbank) := by
  intro z hz
  have hraw :=
    bankPostInheritedSingletonStage ring hn hbank z hz
  apply (UniformFirstHit.expectedHittingTimeAtMost_iff_cost
    (bankValidRootedReferenceData ring hbank).referenceNext
    (BankAnyPostInheritedSingleton ring hbank)
    (by omega : 0 < n) z (4917 * n ^ 2)).2
  intro T
  have hcost :=
    (UniformFirstHit.expectedHittingTimeAtMost_iff_cost
      (bankValidRootedReferenceData ring hbank).referenceNext
      (fun a => nativeLiftSingleton
        (renewalBankValidNativeView ring hbank a))
      (by omega : 0 < n) z (4917 * n ^ 2)).1 hraw T
  have hstrength := costNumeratorTargetOnClosed
    (bankValidRootedReferenceData ring hbank).referenceNext
    (BankPostInheritedGrantDrain ring hbank)
    (BankAnyPostInheritedSingleton ring hbank)
    (fun a => nativeLiftSingleton
      (renewalBankValidNativeView ring hbank a))
    (bankPostInheritedGrantDrainClosed ring hn hbank)
    (by
      intro a ha hs
      have hP : PPlus ring
          (renewalBankValidNativeView ring hbank a) := ha.1.1.1
      obtain ⟨root, hr⟩ :=
        nativeLiftSingletonHasRoot ring
          (renewalBankValidNativeView ring hbank a) hP hs
      exact ⟨root, ha, hr⟩)
    T z hz
  exact Nat.le_trans hstrength hcost

/-! L6: sigma_p, retaining the same fixed native root. -/

def BankPreparedAtSomeRoot {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank) : Prop :=
  ∃ root : Fin n,
    BankPostInheritedSingleton ring hbank root z ∧
      CandidateReturnTarget root (bankValidCandidateView ring hbank z)

/-- Same 6*n² sigma_p cost on the original valid reference;
the fixed root and both post-inherited factors survive to the hit. -/
theorem bankPreparationStageWithInheritedInvariant {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) :
    StageReferencePreparation
      (bankValidRootedReferenceData ring hbank).referenceNext
      (BankAnyPostInheritedSingleton ring hbank)
      (BankPreparedAtSomeRoot ring hbank) := by
  intro z hz
  obtain ⟨root, hroot⟩ := hz
  have hraw :=
    bankPostInheritedCandidatePreparationStage
      ring hn hbank root z hroot
  apply (UniformFirstHit.expectedHittingTimeAtMost_iff_cost
    (bankValidRootedReferenceData ring hbank).referenceNext
    (BankPreparedAtSomeRoot ring hbank)
    (by omega : 0 < n) z (6 * n ^ 2)).2
  intro T
  have hcost :=
    (UniformFirstHit.expectedHittingTimeAtMost_iff_cost
      (bankValidRootedReferenceData ring hbank).referenceNext
      (fun a => CandidateReturnTarget root
        (bankValidCandidateView ring hbank a))
      (by omega : 0 < n) z (6 * n ^ 2)).1 hraw T
  have hstrength := costNumeratorTargetOnClosed
    (bankValidRootedReferenceData ring hbank).referenceNext
    (BankPostInheritedSingleton ring hbank root)
    (BankPreparedAtSomeRoot ring hbank)
    (fun a => CandidateReturnTarget root
      (bankValidCandidateView ring hbank a))
    (bankPostInheritedSingletonClosed ring hn hbank root)
    (by
      intro a ha htarget
      exact ⟨root, ha, htarget⟩)
    T z hroot
  exact Nat.le_trans hstrength hcost

theorem bankPreparedAtSomeRootCore {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank)
    (hz : BankPreparedAtSomeRoot ring hbank z) :
    ReferencePreparationPreparedCore ring z.val.1 ∧
      InheritedAuthorityExtinct ring hbank z ∧
      H_cand ring (bankValidCandidateView ring hbank z) := by
  obtain ⟨root, hroot, htarget⟩ := hz
  exact bankCandidateTargetPreparedCore ring hn hbank root
    z hroot htarget

/-! L7: actual rooted-seed entrance, plus the 2n stock census. -/

def BankAttemptEntrance {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank) : Prop :=
  ∃ seed : RootedSeed ring,
    ¬ headlineGeneratedTarget ring seed.val ∧
      z = (bankValidRootedReferenceData ring hbank).referenceStart seed

theorem bankAttemptEntranceStart {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring)
    (hnot : ¬ headlineGeneratedTarget ring seed.val) :
    BankAttemptEntrance ring hbank
      ((bankValidRootedReferenceData ring hbank).referenceStart seed) := by
  exact ⟨seed, hnot, rfl⟩

private theorem rbInitialInheritedSiteLe {n : Nat}
    (C : HeadlineConfiguration n) (i : Fin n) :
    bankInheritedSiteAtomCount (renewalBankInitialSite C i) ≤ 2 := by
  by_cases ht : (C i).tok = .E <;>
    by_cases hr : (C i).pack.val = 0 <;>
    cases hm : (C i).mode <;>
    simp [bankInheritedSiteAtomCount, bankInheritedWorkerAtomCount,
      bankInheritedControllerAtomCount, bankInheritedPayloadAtomCount,
      renewalBankInitialSite, renewalBankEntrancePayload,
      ht, hr, hm] <;> omega

private theorem rbSumOfBoundedTwo :
    ∀ xs : List Nat, (∀ x, x ∈ xs → x ≤ 2) →
      xs.sum ≤ 2 * xs.length := by
  intro xs
  induction xs with
  | nil =>
      intro _
      simp
  | cons a tail ih =>
      intro h
      have ha : a ≤ 2 := h a (by simp)
      have htail : ∀ x, x ∈ tail → x ≤ 2 := by
        intro x hx
        exact h x (by simp [hx])
      have ht := ih htail
      simp only [List.sum_cons, List.length_cons]
      omega

private theorem rbFoldlSum (xs : List Nat) :
    ∀ acc, xs.foldl (fun total amount => total + amount) acc =
      acc + xs.sum := by
  induction xs with
  | nil =>
      intro acc
      rfl
  | cons a tail ih =>
      intro acc
      simp only [List.foldl_cons, List.sum_cons]
      rw [ih]
      omega

/-- There are at most two inherited entrance atoms per physical
site at service zero. The census does not imply extinction. -/
theorem bankInheritedInitialAtomCountLe {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) :
    bankInheritedStateAtomCount ring hbank
        ((bankValidRootedReferenceData ring hbank).referenceStart seed) ≤
      2 * n := by
  change
    (List.ofFn (fun i : Fin n =>
      bankInheritedSiteAtomCount
        (renewalBankInitialSite seed.val i))).foldl
          (fun total amount => total + amount) 0 ≤ 2 * n
  rw [rbFoldlSum]
  simp only [Nat.zero_add]
  have hmem : ∀ x, x ∈
      (List.ofFn (fun i : Fin n =>
        bankInheritedSiteAtomCount (renewalBankInitialSite seed.val i))) →
      x ≤ 2 := by
    intro x hx
    rw [List.mem_ofFn] at hx
    obtain ⟨i, rfl⟩ := hx
    exact rbInitialInheritedSiteLe seed.val i
  have hbound := rbSumOfBoundedTwo
    (List.ofFn (fun i : Fin n =>
      bankInheritedSiteAtomCount (renewalBankInitialSite seed.val i)))
    hmem
  simpa only [List.length_ofFn] using hbound

end L3.RenewalReferenceClock
