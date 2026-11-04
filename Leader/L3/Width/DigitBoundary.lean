import Leader.L3.Width.DigitBand

/-!
# The R10c boundary stage on an abstract reference

`bankCleanBoundaryStage` (BankRepairDigitBoundaryClean) proved once over a reference: label
extinction of every inherited base label of the audit restarted at the clean start, then the
leading and final receipt flush on the layout-values class.  The reference additionally
supplies three facts the old proof read off the BANK classes (`WidthBoundaryReference`): a
singleton root is the W fixed root, the clean start carries `CleanWord`, and a clean start
with a W fixed root is a singleton.

The band facts of the BANK proof are replaced by the leading width `t + (2^t - 1) ≤ n`
(`t = (compileAdvice q).t`) and the charge is stated in `t`
(`widthBoundaryCharge`): label extinction `2n·2(q + L_t + 2)` plus the leading flush
`2n·2J_t` and the final flush `2n·(F + R + U + r)`, `r = 2^t - 1`.

The final region needs two delimiters `L - R`, `L` (`R = 2^t - 1`), i.e. `first + R < n`.
When that fails (only one delimiter: at `q = 3`, `n ∈ {5, 6, 7}` for some delimiter offsets)
there is no complete block, so the final boundary holds vacuously
(`widthCleanBoundaryFinalVacuous`) and the final flush costs nothing beyond the leading one.

Instance: SMALL (`smallWidthBoundaryStage`, every SMALL ring `n ≥ 5`).  BANK keeps
`widthDigitBoundaryStageBank` (WidthDigitCuts).  On SMALL the charge is
`n · widthBoundarySliceNumerator q ≤ widthBoundarySlice q · n²` (`widthBoundaryChargeSlice`), and
`bandWidthBoundaryStageSmall` gives the boundary premise at the band reference for any slice
table dominating `widthBoundarySlice`.
-/

namespace L3.WidthDigit

open L3
open L3.HeadlineRenewal
open L3.RenewalReferenceClock
open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree
open L3.AcceptedReceipts.WordEntrance.CleanWorker
open UniformFirstHit

set_option autoImplicit false

/-- A digit reference with the three facts the boundary proof reads.  Consumer:
`widthDigitBoundaryStageOfReference`. -/
structure WidthBoundaryReference {n : Nat} (ring : DirectedRing n)
    extends WidthDigitReference ring where
  singletonFixed : ∀ root z, singleton root z → WFixedRoot ring root (piW (phys z))
  startClean : ∀ z, start z → CleanWord ring (piW (phys z))
  singletonOfStart : ∀ root z, start z → WFixedRoot ring root (piW (phys z)) →
    singleton root z

/-- Consumer: `smallWidthBoundaryStage`. -/
def smallWidthBoundaryReference {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hsmall : (compileAdvice (ceilLogTwo n)).useSmall = true) :
    WidthBoundaryReference ring :=
  { smallWidthDigitReference ring hn hsmall with
    singletonFixed := fun _ _ h => h.2
    startClean := fun _ h => h.2.1.2
    singletonOfStart := fun _ _ h hf => ⟨h.1, hf⟩ }

/-! ### Width facts in `t` -/

/-- Consumer: `widthBoundaryDigitNonRootStopOfWordValues`. -/
theorem widthBoundaryDigitTaps {n : Nat} (hn : 5 ≤ n) :
    2 ≤ (compileAdvice (ceilLogTwo n)).t ∧
      (IsPrimitive (compileAdvice (ceilLogTwo n)).t
          (compileAdvice (ceilLogTwo n)).taps ∨
        ∀ j, (compileAdvice (ceilLogTwo n)).taps j = false) ∧
      2 * (2 ^ (compileAdvice (ceilLogTwo n)).t - 1) +
          (compileAdvice (ceilLogTwo n)).t - 2 ≤
        bankRepairDigitLeadingLength (compileAdvice (ceilLogTwo n)).t := by
  have ht2 : 2 ≤ (compileAdvice (ceilLogTwo n)).t :=
    compileAdvice_t_ge_two _ (ringQ_facts n hn).1
  refine ⟨ht2, ?_, ?_⟩
  · left
    exact tapTablePrimitive _ ht2
  · unfold bankRepairDigitLeadingLength bankRepairDigitRadius
    exact Nat.le_refl _

/-- Consumer: `widthCleanBoundaryLabelTasks`. -/
theorem widthBoundaryDigitLeadingLengthPos {n : Nat} (hn : 5 ≤ n) :
    1 ≤ bankRepairDigitLeadingLength (compileAdvice (ceilLogTwo n)).t := by
  have ht2 : 2 ≤ (compileAdvice (ceilLogTwo n)).t :=
    compileAdvice_t_ge_two _ (ringQ_facts n hn).1
  have hp := bankRepairDigitPowLower (compileAdvice (ceilLogTwo n)).t
  unfold bankRepairDigitLeadingLength bankRepairDigitRadius
  omega

/-- Consumer: the two flush regions. -/
theorem widthBoundaryDigitSpanTwo {n : Nat} (hn : 5 ≤ n) :
    2 ≤ digitSpan (compileAdvice (ceilLogTwo n)) := by
  have ht2 : 2 ≤ (compileAdvice (ceilLogTwo n)).t :=
    compileAdvice_t_ge_two _ (ringQ_facts n hn).1
  have hp := bankRepairDigitPowLower (compileAdvice (ceilLogTwo n)).t
  unfold digitSpan
  omega

/-- The label-extinction charge in `t`.  Consumer: `widthCleanBoundaryExtinctionClock`. -/
def widthBoundaryExtinctionCharge (n : Nat) : Nat :=
  2 * (n * (2 * (ceilLogTwo n +
    bankRepairDigitLeadingLength (compileAdvice (ceilLogTwo n)).t + 2)))

/-- The receipt-flush charge in `t`: leading region plus final region.  Consumer:
`widthCleanBoundaryFlushClock`. -/
def widthBoundaryFlushCharge (n : Nat) : Nat :=
  2 * (n * (2 * bankRepairDigitBoundaryServices (compileAdvice (ceilLogTwo n)).t)) +
  2 * (n * (bankRepairDigitForwardCount (bankRepairDigitRadius (compileAdvice (ceilLogTwo n)).t) +
    bankRepairDigitReturnCount (bankRepairDigitRadius (compileAdvice (ceilLogTwo n)).t) +
    bankRepairDigitSettledCount (bankRepairDigitRadius (compileAdvice (ceilLogTwo n)).t) +
    bankRepairDigitRadius (compileAdvice (ceilLogTwo n)).t))

/-- The boundary charge in `t`.  Consumer: `widthDigitBoundaryStageOfReference`. -/
def widthBoundaryCharge (n : Nat) : Nat :=
  widthBoundaryExtinctionCharge n + widthBoundaryFlushCharge n

/-! ### The ported coupled-audit and label machinery -/

/-- Every observer word projects to the reference word.
Consumer: `widthCleanBoundaryRetiredOfReceipt`. -/
theorem widthBoundaryDigitBoundaryAuditFirst {n : Nat}
    {ring : DirectedRing n} (ref : WidthBoundaryReference ring) (start : ref.State)
    (audit : DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (word : List (Fin n)) :
    (word.foldl (widthDigitAuditNext ref.toWidthDigitReference)
      (start, audit)).1 =
      word.foldl (ref.next) start := by
  induction word generalizing start audit with
  | nil =>
      rfl
  | cons e rest ih =>
      change
        (rest.foldl (widthDigitAuditNext ref.toWidthDigitReference)
          (ref.next start e,
            digitAuditStep ring (piD (ref.phys start)) audit e)).1 =
        rest.foldl (ref.next)
          (ref.next start e)
      exact ih (ref.next start e)
        (digitAuditStep ring (piD (ref.phys start)) audit e)

/-- The corresponding terminal predicate is closed along the
SAME coupled actual bankRepairNext / OLD digit-audit replay.
Consumer: `widthBoundaryDigitInheritedLabelUnionTailOfTasks`, `widthBoundaryDigitAllBaseLabelsGoneClosed`. -/
theorem widthBoundaryDigitInheritedLabelRetiredBankStep
    {n : Nat}
    (hn : 2 ≤ n)
    {ring : DirectedRing n} (ref : WidthBoundaryReference ring) (site : Fin n)
    (z : ref.State ×
      DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (e : Fin n)
    (hret : bankRepairDigitInheritedLabelRetired
      site z.2.current) :
    bankRepairDigitInheritedLabelRetired site
      (widthDigitAuditNext ref.toWidthDigitReference z e).2.current := by
  exact bankRepairDigitInheritedLabelRetiredStep hn ring
    (piD (ref.phys z.1)) z.2 site e hret

/-- Summing uniform bounds for independent labels does NOT gain
a logarithm: the cost is multiplied by the number of labels.
Consumer: `widthBoundaryDigitInitialLabelWeightCap`. -/
theorem widthBoundaryDigitListMapSumBound
    {Label : Type} (sites : List Label)
    (cost : Label → Nat) (cap : Nat) :
    (∀ site, site ∈ sites → cost site ≤ cap) →
      (sites.map cost).sum ≤ sites.length * cap := by
  induction sites with
  | nil =>
      intro hcost
      simp
  | cons site rest ih =>
      intro hcost
      have hsite : cost site ≤ cap := hcost site (by simp)
      have htail : ∀ other, other ∈ rest → cost other ≤ cap := by
        intro other hmem
        exact hcost other (by simp [hmem])
      have hbound := ih htail
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      rw [Nat.succ_mul]
      omega

/-- The actual same-word audit prefix from ONE specified R-fold
clean start. Keeping a fixed entrance avoids silently choosing
a fresh incompatible inherited-label identity at later cuts.
Consumer: `widthBoundaryDigitOneLabelReachableStep`, `WidthBoundaryDigitSingleInheritedLabelTasks`, `widthBoundaryDigitInheritedLabelUnionTailOfTasks`. -/
def WidthBoundaryDigitOneLabelReachableFrom
    {n : Nat}
    {ring : DirectedRing n} (ref : WidthBoundaryReference ring) (start : ref.State)
    (z : ref.State ×
      DigitAudit (compileAdvice (ceilLogTwo n)) n) : Prop :=
  ∃ word : List (Fin n),
    word.foldl (widthDigitAuditNext ref.toWidthDigitReference)
      (start, digitAuditInitial (piD (ref.phys start))) = z

/-- Consumer: `widthBoundaryDigitInheritedLabelUnionTailOfTasks`, `widthBoundaryDigitLabelReachStep`, `widthBoundaryDigitLabelReachableInv`. -/
theorem widthBoundaryDigitOneLabelReachableStep
    {n : Nat}
    {ring : DirectedRing n} (ref : WidthBoundaryReference ring) (start : ref.State)
    (z : ref.State ×
      DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (e : Fin n)
    (hz : WidthBoundaryDigitOneLabelReachableFrom
      ref start z) :
    WidthBoundaryDigitOneLabelReachableFrom ref start
      (widthDigitAuditNext ref.toWidthDigitReference z e) := by
  obtain ⟨word, hword⟩ := hz
  refine ⟨word ++ [e], ?_⟩
  rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
  exact congrArg
    (fun w => widthDigitAuditNext ref.toWidthDigitReference w e)
    hword

/-- This is ONE inherited base identity only, not a global
potential for all packet authority or the boundary cut.
Its promised task count decreases on a nominated actual edge
and does not increase on other edges. The budget is L_s:
the paper's SEEK followed by ZERO lifetime, NOT J_s, which is
an aggregate packet ledger per leading lane.

The origin/parent/away lemmas do not prove this interface:
they do not quantify a strictly decreasing remaining distance for
all collision and top/beta first-match rows.
Consumer: `widthBoundaryDigitInitialLabelWeightCap`, `widthBoundaryDigitInheritedLabelUnionTailOfTasks`, `widthBoundaryDigitAllBaseSurvivalTailOfTasks`. -/
def WidthBoundaryDigitSingleInheritedLabelTasks
    {n : Nat}
    {ring : DirectedRing n} (ref : WidthBoundaryReference ring) (start : ref.State)
    (site : Fin n) : Prop :=
  ∃ remaining :
      (ref.State ×
        DigitAudit (compileAdvice (ceilLogTwo n)) n) → Nat,
    (∀ z,
      WidthBoundaryDigitOneLabelReachableFrom ref start z →
      ¬ bankRepairDigitInheritedLabelRetired site z.2.current →
      ∀ e : Fin n,
        remaining (widthDigitAuditNext ref.toWidthDigitReference z e) ≤ remaining z) ∧
    (∀ z,
      WidthBoundaryDigitOneLabelReachableFrom ref start z →
      ¬ bankRepairDigitInheritedLabelRetired site z.2.current →
      ∃ e : Fin n,
        remaining (widthDigitAuditNext ref.toWidthDigitReference z e) + 1 ≤ remaining z) ∧
    remaining (start, digitAuditInitial (piD (ref.phys start))) ≤
      bankRepairDigitLeadingLength ((compileAdvice (ceilLogTwo n)).t)

/-- Initial payload is at most n*2^L for n possible
inherited identities, even when some are initially absent.
Consumer: `widthBoundaryDigitInheritedLabelUnionTailOfTasks`. -/
theorem widthBoundaryDigitInitialLabelWeightCap
    {n : Nat}
    {ring : DirectedRing n} (ref : WidthBoundaryReference ring) (start : ref.State)
    (hcert : ∀ site : Fin n,
      WidthBoundaryDigitSingleInheritedLabelTasks ref start site) :
    ((List.ofFn (fun site : Fin n => site)).map (fun site =>
      bankRepairDigitLivePowWeight
        (fun z : ref.State ×
          DigitAudit (compileAdvice (ceilLogTwo n)) n =>
          bankRepairDigitInheritedLabelAlive site z.2.current)
        (Classical.choose (hcert site))
        (start, digitAuditInitial (piD (ref.phys start))))).sum ≤
      n * 2 ^ bankRepairDigitLeadingLength
        ((compileAdvice (ceilLogTwo n)).t) := by
  classical
  have hcap : ∀ site : Fin n,
      bankRepairDigitLivePowWeight
        (fun z : ref.State ×
          DigitAudit (compileAdvice (ceilLogTwo n)) n =>
          bankRepairDigitInheritedLabelAlive site z.2.current)
        (Classical.choose (hcert site))
        (start, digitAuditInitial (piD (ref.phys start))) ≤
        2 ^ bankRepairDigitLeadingLength
          ((compileAdvice (ceilLogTwo n)).t) := by
    intro site
    have hs := (Classical.choose_spec (hcert site)).2.2
    by_cases ha : bankRepairDigitInheritedLabelAlive site
        (digitAuditInitial (piD (ref.phys start))).current
    · simp only [bankRepairDigitLivePowWeight, if_pos ha]
      exact Nat.pow_le_pow_right
        (by omega : 0 < (2 : Nat)) hs
    · simp [bankRepairDigitLivePowWeight, ha]
  have hsum := widthBoundaryDigitListMapSumBound
    (List.ofFn (fun site : Fin n => site))
    (fun site =>
      bankRepairDigitLivePowWeight
        (fun z : ref.State ×
          DigitAudit (compileAdvice (ceilLogTwo n)) n =>
          bankRepairDigitInheritedLabelAlive site z.2.current)
        (Classical.choose (hcert site))
        (start, digitAuditInitial (piD (ref.phys start))))
    (2 ^ bankRepairDigitLeadingLength
      ((compileAdvice (ceilLogTwo n)).t))
    (fun site _ => hcap site)
  simpa using hsum

/-- For EACH fixed R-fold entrance, the n possible OLD inherited
label identities share the same physical edge word.
Their all-label ALIVE union has an exponentially decreasing tail
with initial factor n*2^L. This replaces the incorrect max<=sum
mean strategy without asserting the still-unproved local tasks.
Consumer: `widthBoundaryDigitAllBaseSurvivalTailOfTasks`. -/
theorem widthBoundaryDigitInheritedLabelUnionTailOfTasks
    {n : Nat}
    (hn : 2 ≤ n)
    {ring : DirectedRing n} (ref : WidthBoundaryReference ring) (start : ref.State)
    (hcert : ∀ site : Fin n,
      WidthBoundaryDigitSingleInheritedLabelTasks ref start site)
    (t : Nat) :
    2 ^ t *
      bankRepairDigitAliveWordCount
        (widthDigitAuditNext ref.toWidthDigitReference)
        (fun z : ref.State ×
          DigitAudit (compileAdvice (ceilLogTwo n)) n =>
          ∃ site : Fin n,
            bankRepairDigitInheritedLabelAlive site z.2.current)
        (start, digitAuditInitial (piD (ref.phys start))) t ≤
      (n * 2 ^ bankRepairDigitLeadingLength
        ((compileAdvice (ceilLogTwo n)).t)) *
        (2 * n - 1) ^ t := by
  classical
  have hstart :
      WidthBoundaryDigitOneLabelReachableFrom ref start
        (start, digitAuditInitial (piD (ref.phys start))) :=
    ⟨[], rfl⟩
  have htail := bankRepairDigitUnionTailOfLabelRanks
    (by omega : 1 ≤ n)
    (widthDigitAuditNext ref.toWidthDigitReference)
    (List.ofFn (fun site : Fin n => site))
    (WidthBoundaryDigitOneLabelReachableFrom ref start)
    (fun site z =>
      bankRepairDigitInheritedLabelAlive site z.2.current)
    (fun site => Classical.choose (hcert site))
    (fun z e hz =>
      widthBoundaryDigitOneLabelReachableStep
        ref start z e hz)
    (fun site z e hret =>
      widthBoundaryDigitInheritedLabelRetiredBankStep
        hn ref site z e hret)
    (fun site z hz ha e =>
      (Classical.choose_spec (hcert site)).1 z hz
        (fun hno => hno ha) e)
    (fun site z hz ha =>
      (Classical.choose_spec (hcert site)).2.1 z hz
        (fun hno => hno ha))
    (start, digitAuditInitial (piD (ref.phys start))) hstart t
  have hcap := widthBoundaryDigitInitialLabelWeightCap
    ref start hcert
  have hmul := Nat.mul_le_mul_left ((2 * n - 1) ^ t) hcap
  have hlist : ∀ z : ref.State ×
      DigitAudit (compileAdvice (ceilLogTwo n)) n,
      (∃ site : Fin n,
        site ∈ List.ofFn (fun i : Fin n => i) ∧
        bankRepairDigitInheritedLabelAlive site z.2.current) ↔
      (∃ site : Fin n,
        bankRepairDigitInheritedLabelAlive site z.2.current) := by
    intro z
    constructor
    · intro h
      obtain ⟨site, _, ha⟩ := h
      exact ⟨site, ha⟩
    · intro h
      obtain ⟨site, ha⟩ := h
      exact ⟨site, List.mem_ofFn.mpr ⟨site, rfl⟩, ha⟩
  have hword :
      bankRepairDigitAliveWordCount
        (widthDigitAuditNext ref.toWidthDigitReference)
        (fun z : ref.State ×
          DigitAudit (compileAdvice (ceilLogTwo n)) n =>
          ∃ site, site ∈ List.ofFn
            (fun i : Fin n => i) ∧
            bankRepairDigitInheritedLabelAlive site z.2.current)
        (start, digitAuditInitial (piD (ref.phys start))) t =
      bankRepairDigitAliveWordCount
        (widthDigitAuditNext ref.toWidthDigitReference)
        (fun z : ref.State ×
          DigitAudit (compileAdvice (ceilLogTwo n)) n =>
          ∃ site : Fin n,
            bankRepairDigitInheritedLabelAlive site z.2.current)
        (start, digitAuditInitial (piD (ref.phys start))) t := by
    exact congrArg
      (fun P =>
        bankRepairDigitAliveWordCount
          (widthDigitAuditNext ref.toWidthDigitReference) P
          (start, digitAuditInitial (piD (ref.phys start))) t)
      (funext (fun z =>
        propext (hlist z)))
  rw [hword] at htail
  exact Nat.le_trans htail (by
    simpa only [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
      using hmul)

/-- Consumer: `widthBoundaryDigitAllBaseSurvivalTailOfTasks`, `widthBoundaryDigitAllGoneWord`. -/
theorem widthBoundaryDigitAllBaseLabelsGoneClosed
    {n : Nat}
    (hn : 2 ≤ n)
    {ring : DirectedRing n} (ref : WidthBoundaryReference ring) (z : ref.State ×
      DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (e : Fin n)
    (hz : widthDigitAllBaseLabelsGone ref.toWidthDigitReference z) :
    widthDigitAllBaseLabelsGone ref.toWidthDigitReference
      (widthDigitAuditNext ref.toWidthDigitReference z e) := by
  intro hnew
  obtain ⟨site, halive⟩ := hnew
  have hret : bankRepairDigitInheritedLabelRetired site z.2.current := by
    intro hold
    exact hz ⟨site, hold⟩
  exact (widthBoundaryDigitInheritedLabelRetiredBankStep
    hn ref site z e hret) halive

/-- The geometric union bound is the exact survival numerator
of the first hit of all inherited labels retired, because
individual retirement is absorbing on the actual edge tape.
Consumer: `widthBoundaryDigitAllBaseCostLogarithmicOfTasks`. -/
theorem widthBoundaryDigitAllBaseSurvivalTailOfTasks
    {n : Nat}
    (hn : 2 ≤ n)
    {ring : DirectedRing n} (ref : WidthBoundaryReference ring) (start : ref.State)
    (hcert : ∀ site : Fin n,
      WidthBoundaryDigitSingleInheritedLabelTasks ref start site)
    (t : Nat) :
    2 ^ t * survivalNumerator
      (widthDigitAuditNext ref.toWidthDigitReference)
      (widthDigitAllBaseLabelsGone ref.toWidthDigitReference)
      (start, digitAuditInitial (piD (ref.phys start))) t ≤
      (n * 2 ^ bankRepairDigitLeadingLength
        ((compileAdvice (ceilLogTwo n)).t)) *
        (2 * n - 1) ^ t := by
  have hsurv := bankRepairDigitSurvivalEqualsAliveWordCount
    (widthDigitAuditNext ref.toWidthDigitReference)
    (widthDigitAllBaseLabelsGone ref.toWidthDigitReference)
    (fun z e hz =>
      widthBoundaryDigitAllBaseLabelsGoneClosed hn ref z e hz)
    (start, digitAuditInitial (piD (ref.phys start))) t
  have heq :
      (fun z : ref.State ×
          DigitAudit (compileAdvice (ceilLogTwo n)) n =>
          ¬ widthDigitAllBaseLabelsGone ref.toWidthDigitReference z) =
        (fun z : ref.State ×
          DigitAudit (compileAdvice (ceilLogTwo n)) n =>
          ∃ site : Fin n,
            bankRepairDigitInheritedLabelAlive site z.2.current) := by
    classical
    funext z
    apply propext
    simp [widthDigitAllBaseLabelsGone]
  rw [heq] at hsurv
  rw [hsurv]
  exact widthBoundaryDigitInheritedLabelUnionTailOfTasks
    hn ref start hcert t

/-- First-hit bound for the TRUE coupled reference/audit process,
assuming only the n local inherited-label task certificates.
The bound is logarithmic in n and L_s, NOT n^2*L_s.
Consumer: `widthCleanBoundaryExtinctionClock`. -/
theorem widthBoundaryDigitAllBaseCostLogarithmicOfTasks
    {n : Nat}
    (hn : 2 ≤ n)
    {ring : DirectedRing n} (ref : WidthBoundaryReference ring) (start : ref.State)
    (hcert : ∀ site : Fin n,
      WidthBoundaryDigitSingleInheritedLabelTasks ref start site) :
    ∀ T,
      costNumerator
        (widthDigitAuditNext ref.toWidthDigitReference)
        (widthDigitAllBaseLabelsGone ref.toWidthDigitReference)
        (start, digitAuditInitial (piD (ref.phys start))) T ≤
      n ^ T * (2 * n * (ceilLogTwo n +
        bankRepairDigitLeadingLength
          ((compileAdvice (ceilLogTwo n)).t) + 2)) := by
  have hqpos : 1 ≤ ceilLogTwo n := by
    have hq := ceilLogTwo_eq n hn
    omega
  have hpositive :
      1 ≤ ceilLogTwo n + bankRepairDigitLeadingLength
        ((compileAdvice (ceilLogTwo n)).t) := by omega
  have hpow := bankRepairDigitCeilLogTwoPower
    (ceilLogTwo n + bankRepairDigitLeadingLength
      ((compileAdvice (ceilLogTwo n)).t)) hpositive
  have hA := bankRepairDigitLabelTailPowerEnvelope n
    (bankRepairDigitLeadingLength ((compileAdvice (ceilLogTwo n)).t))
  have htail : ∀ t,
      2 ^ t * survivalNumerator
        (widthDigitAuditNext ref.toWidthDigitReference)
        (widthDigitAllBaseLabelsGone ref.toWidthDigitReference)
        (start, digitAuditInitial (piD (ref.phys start))) t ≤
      2 ^ (ceilLogTwo n + bankRepairDigitLeadingLength
        ((compileAdvice (ceilLogTwo n)).t)) *
        (2 * n - 1) ^ t := by
    intro t
    have hs := widthBoundaryDigitAllBaseSurvivalTailOfTasks
      hn ref start hcert t
    exact Nat.le_trans hs
      (Nat.mul_le_mul_right ((2 * n - 1) ^ t) hA)
  intro T
  have hcost := bankRepairDigitCostFromGeometricTail
    (by omega : 1 ≤ n)
    (widthDigitAuditNext ref.toWidthDigitReference)
    (widthDigitAllBaseLabelsGone ref.toWidthDigitReference)
    (start, digitAuditInitial (piD (ref.phys start)))
    (2 ^ (ceilLogTwo n + bankRepairDigitLeadingLength
      ((compileAdvice (ceilLogTwo n)).t)))
    htail T
  rw [hpow] at hcost
  exact hcost

/-- Consumer: `widthBoundaryDigitLabelReachableInv`, `widthBoundaryDigitSingleInheritedLabelTasksOfFrozenInit`. -/
theorem widthBoundaryDigitLabelReachStep {n : Nat}
    {ring : DirectedRing n} (ref : WidthBoundaryReference ring) (start : ref.State) (R B : Fin n → Bool)
    (hgeo : ∀ z, WidthBoundaryDigitOneLabelReachableFrom ref start z →
      ref.drained z.1 ∧
      (∀ i, (piD (ref.phys z.1) i).word.native.l = R i) ∧
      (∀ i, (piD (ref.phys z.1) i).word.beta = B i))
    (z : ref.State ×
      DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (hz : WidthBoundaryDigitOneLabelReachableFrom ref start z)
    (e : Fin n) :
    piD (ref.phys (widthDigitAuditNext ref.toWidthDigitReference z e).1) =
        phiD ring (piD (ref.phys z.1)) e ∧
      (∀ i, (piD (ref.phys z.1) i).word.native.l = R i) ∧
      (∀ i, (phiD ring (piD (ref.phys z.1)) e i).word.beta = B i) := by
  obtain ⟨hfire, hR, _⟩ := hgeo z hz
  obtain ⟨_, _, hB'⟩ := hgeo _
    (widthBoundaryDigitOneLabelReachableStep ref start z e hz)
  have hproj : piD (ref.phys (widthDigitAuditNext ref.toWidthDigitReference z e).1) =
      phiD ring (piD (ref.phys z.1)) e :=
    ref.digitStep z.1 hfire e
  refine ⟨hproj, hR, ?_⟩
  intro i
  rw [← hproj]
  exact hB' i

/-- Consumer: `widthBoundaryDigitSingleInheritedLabelTasksOfFrozenInit`. -/
theorem widthBoundaryDigitLabelReachableInv {n : Nat}
    (hn : 2 ≤ n) {ring : DirectedRing n} (ref : WidthBoundaryReference ring) (start : ref.State) (site : Fin n)
    (R B : Fin n → Bool) (L : Nat)
    (hgeo : ∀ z, WidthBoundaryDigitOneLabelReachableFrom ref start z →
      ref.drained z.1 ∧
      (∀ i, (piD (ref.phys z.1) i).word.native.l = R i) ∧
      (∀ i, (piD (ref.phys z.1) i).word.beta = B i))
    (hinit : bankRepairDigitLabelInvariant ring R B L site
      (piD (ref.phys start)) (digitGhostInitial (piD (ref.phys start)))) :
    ∀ z, WidthBoundaryDigitOneLabelReachableFrom ref start z →
      bankRepairDigitLabelInvariant ring R B L site
        (piD (ref.phys z.1)) z.2.current := by
  have key : ∀ (word : List (Fin n)) z0,
      WidthBoundaryDigitOneLabelReachableFrom ref start z0 →
      bankRepairDigitLabelInvariant ring R B L site
        (piD (ref.phys z0.1)) z0.2.current →
      bankRepairDigitLabelInvariant ring R B L site
        (piD (ref.phys (word.foldl (widthDigitAuditNext ref.toWidthDigitReference)
          z0).1))
        (word.foldl (widthDigitAuditNext ref.toWidthDigitReference)
          z0).2.current := by
    intro word
    induction word with
    | nil => intro z0 _ h; exact h
    | cons a l ih =>
        intro z0 hz0 hinv
        apply ih _ (widthBoundaryDigitOneLabelReachableStep ref start
          z0 a hz0)
        obtain ⟨hproj, hR, hB⟩ := widthBoundaryDigitLabelReachStep ref
          start R B hgeo z0 hz0 a
        rw [hproj]
        exact bankRepairDigitLabelStepInv hn ring R B L (piD (ref.phys z0.1))
          z0.2.current (z0.2.clock + 1) a site hR hB hinv
  rintro z ⟨word, rfl⟩
  exact key word _ ⟨[], rfl⟩ hinit

/-- The post-inherited root fixes every native leader bit.
Consumer: `widthCleanBoundaryFrozen`. -/
theorem widthBoundaryDigitRootedLeader {n : Nat}
    {ring : DirectedRing n} (ref : WidthBoundaryReference ring) (root : Fin n) (z : ref.State)
    (hs : ref.singleton root z) (i : Fin n) :
    ((ref.phys z) i).l = decide (i = root) := by
  have h1 : ((ref.phys z) root).l = true := (ref.singletonFixed root z hs).1
  have h2 : ∀ j : Fin n, ((ref.phys z) j).l = true → j = root :=
    (ref.singletonFixed root z hs).2.1
  by_cases hi : i = root
  · subst hi
    simp [h1]
  · cases h : ((ref.phys z) i).l
    · simp [hi]
    · exact absurd (h2 i h) hi

/-- The digit-stage invariant from a produced entrance.
Consumer: `widthBoundaryDigitProducedInvStep`, `widthBoundaryDigitProducedReachableInv`. -/
def WidthBoundaryDigitProducedInv {n : Nat}
    {ring : DirectedRing n} (ref : WidthBoundaryReference ring) (root : Fin n) (B : Fin n → Bool)
    (z : ref.State) : Prop :=
  ref.singleton root z ∧
    AcceptedReceipts.QWord ring (piW (ref.phys z)) ∧
    ∀ i, ((ref.phys z) i).beta = B i

/-- Consumer: `widthBoundaryDigitProducedReachableInv`. -/
theorem widthBoundaryDigitProducedInvStep {n : Nat}
    {ring : DirectedRing n} (ref : WidthBoundaryReference ring) (root : Fin n) (B : Fin n → Bool)
    (z : ref.State)
    (hz : WidthBoundaryDigitProducedInv ref root B z) (e : Fin n) :
    WidthBoundaryDigitProducedInv ref root B
      (ref.next z e) := by
  obtain ⟨hs, hq, hb⟩ := hz
  have hproj := ref.wordStep z (ref.singletonDrained root z hs) e
  refine ⟨ref.singletonClosed root z hs e, ?_, ?_⟩
  · rw [hproj]
    exact (AcceptedReceipts.qword_step ring _ hq e).2
  · intro i
    have hv := congrArg Prod.snd
      (AcceptedReceipts.qword_visible_fixed ring _ hq e i)
    have hi : ((ref.phys (ref.next z e)) i).beta =
        (phiW ring (piW (ref.phys z)) e i).beta :=
      congrArg (fun S => (S i).beta) hproj
    rw [hi]
    exact hv.trans (hb i)

/-- Consumer: `widthCleanBoundaryFrozen`. -/
theorem widthBoundaryDigitProducedReachableInv {n : Nat}
    {ring : DirectedRing n} (ref : WidthBoundaryReference ring) (start : ref.State) (root : Fin n)
    (hs : ref.singleton root start)
    (hq : AcceptedReceipts.QWord ring (piW (ref.phys start))) :
    ∀ z, WidthBoundaryDigitOneLabelReachableFrom ref start z →
      WidthBoundaryDigitProducedInv ref root
        (fun i => ((ref.phys start) i).beta) z.1 := by
  have key : ∀ (word : List (Fin n))
      (z0 : ref.State ×
        DigitAudit (compileAdvice (ceilLogTwo n)) n),
      WidthBoundaryDigitProducedInv ref root
        (fun i => ((ref.phys start) i).beta) z0.1 →
      WidthBoundaryDigitProducedInv ref root
        (fun i => ((ref.phys start) i).beta)
        (word.foldl (widthDigitAuditNext ref.toWidthDigitReference) z0).1 := by
    intro word
    induction word with
    | nil => intro z0 h; exact h
    | cons e rest ih =>
        intro z0 h
        exact ih (widthDigitAuditNext ref.toWidthDigitReference z0 e)
          (widthBoundaryDigitProducedInvStep ref root _ z0.1 h e)
  rintro z ⟨word, rfl⟩
  exact key word _ ⟨hs, hq, fun _ => rfl⟩

/-- T3 from frozen bits and any initial label invariant.
Consumer: `widthCleanBoundaryLabelTasks`. -/
theorem widthBoundaryDigitSingleInheritedLabelTasksOfFrozenInit
    {n : Nat} (hn : 2 ≤ n)
    {ring : DirectedRing n} (ref : WidthBoundaryReference ring) (start : ref.State)
    (site : Fin n) (R B : Fin n → Bool)
    (hfr : ∀ z, WidthBoundaryDigitOneLabelReachableFrom ref start z →
      ref.drained z.1 ∧
      (∀ i, (piD (ref.phys z.1) i).word.native.l = R i) ∧
      (∀ i, (piD (ref.phys z.1) i).word.beta = B i))
    (hinit : bankRepairDigitLabelInvariant ring R B
      (bankRepairDigitLeadingLength ((compileAdvice (ceilLogTwo n)).t)) site
      (piD (ref.phys start)) (digitGhostInitial (piD (ref.phys start)))) :
    WidthBoundaryDigitSingleInheritedLabelTasks ref start site := by
  have hinv := widthBoundaryDigitLabelReachableInv hn ref start site
    R B _ hfr hinit
  have hcost : ∀ z, WidthBoundaryDigitOneLabelReachableFrom ref start z →
      ∀ h, (z.2.current h).base = some (.inherited site) → ∀ e : Fin n,
      bankRepairDigitLabelRemaining ring R B
          (bankRepairDigitLeadingLength ((compileAdvice (ceilLogTwo n)).t)) site
          (piD (ref.phys (widthDigitAuditNext ref.toWidthDigitReference z e).1))
          (widthDigitAuditNext ref.toWidthDigitReference z e).2.current +
        (if e = h then 1 else 0) ≤
      bankRepairDigitLabelRemaining ring R B
          (bankRepairDigitLeadingLength ((compileAdvice (ceilLogTwo n)).t)) site
          (piD (ref.phys z.1)) z.2.current := by
    intro z hz h hh e
    obtain ⟨hproj, hR, hB⟩ := widthBoundaryDigitLabelReachStep ref
      start R B hfr z hz e
    rw [hproj]
    exact bankRepairDigitLabelStepCost hn ring R B _ (piD (ref.phys z.1))
      z.2.current (z.2.clock + 1) e site h hR hB (hinv z hz) hh
  refine ⟨fun z => bankRepairDigitLabelRemaining ring R B
      (bankRepairDigitLeadingLength ((compileAdvice (ceilLogTwo n)).t)) site
      (piD (ref.phys z.1)) z.2.current, ?_, ?_, ?_⟩
  · intro z hz hret e
    obtain ⟨h, hh⟩ : bankRepairDigitInheritedLabelAlive site z.2.current :=
      Classical.byContradiction fun hA => hret hA
    exact Nat.le_trans (Nat.le_add_right _ _) (hcost z hz h hh e)
  · intro z hz hret
    obtain ⟨h, hh⟩ : bankRepairDigitInheritedLabelAlive site z.2.current :=
      Classical.byContradiction fun hA => hret hA
    refine ⟨h, ?_⟩
    have := hcost z hz h hh h
    rw [if_pos rfl] at this
    exact this
  · show bankRepairDigitLabelRemaining ring R B
        (bankRepairDigitLeadingLength ((compileAdvice (ceilLogTwo n)).t)) site
        (piD (ref.phys start)) (digitGhostInitial (piD (ref.phys start))) ≤ _
    by_cases hA : bankRepairDigitInheritedLabelAlive site
        (digitGhostInitial (piD (ref.phys start)))
    · obtain ⟨h, hh⟩ := hA
      obtain ⟨_, hc, hu⟩ := hinit h hh
      rw [bankRepairDigitLabelRemainingHost ring R B _ site _ _ h hh hu]
      exact hc
    · rw [bankRepairDigitLabelRemainingDead ring R B _ site _ _ hA]
      exact Nat.zero_le _

/-- The weakest extra fact the label needs: the stop clause at
`site` unless `site` is the root.
Consumer: `widthBoundaryDigitNonRootStopOfWordValues`. -/
def WidthBoundaryDigitNonRootStop {n : Nat}
    {ring : DirectedRing n} (ref : WidthBoundaryReference ring) (start : ref.State) (site : Fin n) : Prop :=
  (piD (ref.phys start) site).word.native.l = false →
  (piD (ref.phys start) site).top.wBase ≠ .NONE →
    ∃ k, 1 ≤ k ∧
      k ≤ bankRepairDigitLeadingLength ((compileAdvice (ceilLogTwo n)).t) ∧
      bankRepairDigitLabelStop ring
        (fun i => (piD (ref.phys start) i).word.native.l)
        (fun i => (piD (ref.phys start) i).word.beta) site
        (bankRepairDigitBaseSeek (piD (ref.phys start) site).top.wBase) k

/-- T7 (b): the certificate-word equations of the visible word at the
native root give the stop clause at every site.
Consumer: `widthCleanBoundaryLabelTasks`. -/
theorem widthBoundaryDigitNonRootStopOfWordValues {n : Nat} (hn : 5 ≤ n)
    {ring : DirectedRing n} (ref : WidthBoundaryReference ring) (start : ref.State) (root : Fin n)
    (hroot : ((ref.phys start) root).l = true)
    (hv : AcceptedReceipts.WordEntrance.CleanWorker.CleanWorkerWordValues
      ring root (piW (ref.phys start)))
    (site : Fin n) :
    WidthBoundaryDigitNonRootStop ref start site := by
  intro hl _
  obtain ⟨ht2, htaps, hL⟩ := widthBoundaryDigitTaps hn
  obtain ⟨a, ha⟩ : ∃ a, a = PPL.cyclicOffset ring root site := ⟨_, rfl⟩
  have hsite : PPL.shiftRight ring root a = site := by
    rw [ha]
    exact bankRepairDigitShiftOffset ring root site
  have han : a < n := by
    rw [ha]
    exact Nat.mod_lt _ ring.hn
  have ha1 : 1 ≤ a := by
    by_cases h0 : a = 0
    · exfalso
      have hs : site = root := by
        rw [← hsite, h0]
        exact bankRepairDigitShiftZero ring root
      rw [hs] at hl
      have h' : ((ref.phys start) root).l = false := hl
      rw [hroot] at h'
      exact absurd h' (by decide)
    · omega
  have hwalk : ∀ k, bankRepairDigitRightWalk ring k site =
      PPL.shiftRight ring root (a + k) := by
    intro k
    rw [← hsite]
    exact bankRepairDigitShiftWalk ring root a k
  by_cases hreach :
      n ≤ a + bankRepairDigitLeadingLength ((compileAdvice (ceilLogTwo n)).t)
  · refine ⟨n - a, by omega, by omega, Or.inl ?_⟩
    rw [hwalk, show a + (n - a) = n by omega, bankRepairDigitShiftFull ring root]
    exact hroot
  · obtain ⟨k, hk1, hkL, hb, k', hk1', hk', hb'⟩ :=
      bankRepairDigitOffsetStop n (compileAdvice (ceilLogTwo n)).t
        (compileAdvice (ceilLogTwo n)).taps
        (fun k => AcceptedReceipts.WordEntrance.CleanWorker.cwBit ring root
          (piW (ref.phys start)) k)
        (fun k => AcceptedReceipts.WordEntrance.CleanWorker.cwMarker ring root
          (piW (ref.phys start)) k)
        ht2 htaps
        (fun k h1 h2 => hv.recurrence ⟨k, h2⟩ h1)
        (fun k h1 h2 => hv.laterNonzero ⟨k, h2⟩ h1)
        (fun k h1 h2 => hv.markers ⟨k, h2⟩ h1)
        _ hL a ha1 (by omega)
    refine ⟨k, hk1, hkL, Or.inr ⟨?_, Or.inr ⟨k', hk1', hk', ?_⟩⟩⟩
    · rw [hwalk]
      exact hb
    · rw [hwalk]
      exact hb'

/-- Run invariant of the coupled reference x audit chain at a fixed root.
Consumer: `widthBoundaryDigitBoundaryAuditInvariantInitial`, `widthBoundaryDigitBoundaryAuditInvariantStep`, `widthBoundaryDigitBoundaryAuditInvariantWord`. -/
def WidthBoundaryDigitBoundaryAuditInvariant {n : Nat} {ring : DirectedRing n} (ref : WidthBoundaryReference ring) (root : Fin n)
    (p : ref.State ×
      DigitAudit (compileAdvice (ceilLogTwo n)) n) : Prop :=
  ref.singleton root p.1 ∧
  DigitAt ring p.2 p.2.clock (piD (ref.phys p.1)) p.2.current ∧
  ∀ i, BankRepairDigitBaseGhostSound ring root
    (piD (ref.phys p.1) i).top.wBase (p.2.current i).base

/-- Consumer: `widthBoundaryDigitBoundaryAuditInvariantRun`. -/
theorem widthBoundaryDigitBoundaryAuditInvariantInitial {n : Nat}
    {ring : DirectedRing n} (ref : WidthBoundaryReference ring) (root : Fin n)
    (start : ref.State)
    (h : ref.singleton root start) :
    WidthBoundaryDigitBoundaryAuditInvariant ref root
      (start, digitAuditInitial (piD (ref.phys start))) := by
  refine ⟨h, Or.inl ⟨rfl, rfl, rfl⟩, ?_⟩
  intro i
  change BankRepairDigitBaseGhostSound ring root ((ref.phys start) i).wBase
    (if ((ref.phys start) i).wBase == WBase.NONE then none
      else some (DigitBaseOrigin.inherited i))
  unfold BankRepairDigitBaseGhostSound
  cases ((ref.phys start) i).wBase <;> simp

/-- Consumer: `widthBoundaryDigitBoundaryAuditInvariantWord`. -/
theorem widthBoundaryDigitBoundaryAuditInvariantStep {n : Nat}
    {ring : DirectedRing n} (ref : WidthBoundaryReference ring) (hn : 5 ≤ n) (root : Fin n)
    (p : ref.State ×
      DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (hp : WidthBoundaryDigitBoundaryAuditInvariant ref root p)
    (e : Fin n) :
    WidthBoundaryDigitBoundaryAuditInvariant ref root
      (widthDigitAuditNext ref.toWidthDigitReference p e) := by
  obtain ⟨hs, _hat, hsound⟩ := hp
  have hproj := ref.digitStep p.1 (ref.singletonDrained root p.1 hs) e
  have hroot : ∀ i, (piD (ref.phys p.1) i).word.native.l = true → i = root :=
    fun i hi => (ref.singletonFixed root p.1 hs).2.1 i hi
  refine ⟨ref.singletonClosed root p.1 hs e, ?_, ?_⟩
  · exact Or.inr ⟨_, List.Mem.head _, rfl, hproj, rfl⟩
  · intro i
    change BankRepairDigitBaseGhostSound ring root
      (piD (ref.phys (ref.next p.1 e)) i).top.wBase
      (digitGhostStep ring (piD (ref.phys p.1)) p.2.current (p.2.clock + 1) e i).base
    rw [hproj]
    exact bankRepairDigitBaseGhostSoundStep (by omega) ring root _ _ _ e
      (Nat.succ_pos _) hroot hsound i

/-- Consumer: `widthBoundaryDigitBoundaryAuditInvariantRun`. -/
theorem widthBoundaryDigitBoundaryAuditInvariantWord {n : Nat}
    {ring : DirectedRing n} (ref : WidthBoundaryReference ring) (hn : 5 ≤ n) (root : Fin n)
    (word : List (Fin n)) :
    ∀ p : ref.State ×
        DigitAudit (compileAdvice (ceilLogTwo n)) n,
      WidthBoundaryDigitBoundaryAuditInvariant ref root p →
      WidthBoundaryDigitBoundaryAuditInvariant ref root
        (word.foldl (widthDigitAuditNext ref.toWidthDigitReference) p) := by
  induction word with
  | nil => intro p hp; exact hp
  | cons e rest ih =>
      intro p hp
      exact ih _ (widthBoundaryDigitBoundaryAuditInvariantStep ref hn root p hp e)

/-- Consumer: `widthBoundaryDigitBoundaryWFixedRootOfSingleton`. -/
theorem widthBoundaryDigitSingletonWordFold {n : Nat}
    {ring : DirectedRing n} (ref : WidthBoundaryReference ring) (root : Fin n)
    (word : List (Fin n)) :
    ∀ z : ref.State,
      ref.singleton root z →
      ref.singleton root
        (word.foldl (ref.next) z) := by
  induction word with
  | nil => intro z hz; exact hz
  | cons e rest ih =>
      intro z hz
      exact ih _ (ref.singletonClosed root z hz e)

/-- Consumer: `widthBoundaryDigitBoundaryBaseExtinctOfSingleton`, `widthCleanBoundaryRetiredOfReceipt`. -/
theorem widthBoundaryDigitBoundaryAuditInvariantRun {n : Nat}
    {ring : DirectedRing n} (ref : WidthBoundaryReference ring) (hn : 5 ≤ n) (root : Fin n)
    (start : ref.State)
    (hs : ref.singleton root start)
    (word : List (Fin n)) :
    WidthBoundaryDigitBoundaryAuditInvariant ref root
      (word.foldl (widthDigitAuditNext ref.toWidthDigitReference)
        (start, digitAuditInitial (piD (ref.phys start)))) :=
  widthBoundaryDigitBoundaryAuditInvariantWord ref hn root word _
    (widthBoundaryDigitBoundaryAuditInvariantInitial ref root start hs)

/-- Piece `WFixedRoot` at a fixed singleton root.
Consumer: `widthCleanBoundaryLeadingStable`, `widthCleanBoundaryLeadingTasks`, `widthCleanBoundaryRetiredOfReceipt`. -/
theorem widthBoundaryDigitBoundaryWFixedRootOfSingleton {n : Nat}
    {ring : DirectedRing n} (ref : WidthBoundaryReference ring) (root : Fin n)
    (start : ref.State)
    (hs : ref.singleton root start)
    (word : List (Fin n)) :
    WFixedRoot ring root
      (piW (ref.phys (word.foldl (ref.next) start))) :=
  ref.singletonFixed root _ (widthBoundaryDigitSingletonWordFold ref root word start hs)

/-- Piece base extinction: once every inherited label is gone, the audit
witnesses `DigitBaseExtinct` at the singleton root at the current clock.
Consumer: `widthCleanBoundaryRetiredOfReceipt`. -/
theorem widthBoundaryDigitBoundaryBaseExtinctOfSingleton {n : Nat}
    {ring : DirectedRing n} (ref : WidthBoundaryReference ring) (hn : 5 ≤ n) (root : Fin n)
    (start : ref.State)
    (hs : ref.singleton root start)
    (word : List (Fin n))
    (hgone : widthDigitAllBaseLabelsGone ref.toWidthDigitReference
      (word.foldl (widthDigitAuditNext ref.toWidthDigitReference)
        (start, digitAuditInitial (piD (ref.phys start))))) :
    DigitBaseExtinct ring root
      (word.foldl (widthDigitAuditNext ref.toWidthDigitReference)
        (start, digitAuditInitial (piD (ref.phys start)))).2 0
      (word.foldl (widthDigitAuditNext ref.toWidthDigitReference)
        (start, digitAuditInitial (piD (ref.phys start)))).2.clock := by
  obtain ⟨_, hat, hsound⟩ :=
    widthBoundaryDigitBoundaryAuditInvariantRun ref hn root start hs word
  refine ⟨Nat.zero_le _, _, _, hat, ?_⟩
  intro i
  rcases hsound i with ⟨hw, hg⟩ | ⟨hw, ⟨s, hg⟩ | ⟨born, hborn, hg⟩⟩
  · exact Or.inl ⟨hw, hg⟩
  · exact absurd ⟨s, i, hg⟩ hgone
  · exact Or.inr ⟨born, hborn, hw, hg⟩

/-- Consumer: `widthBoundaryDigitLayoutValuesStep`, `widthBoundaryDigitLeadDataStep`, `widthCleanBoundaryLeadingStable`. -/
theorem widthBoundaryDigitLayoutFixedStep {n : Nat}
    {ring : DirectedRing n} (ref : WidthBoundaryReference ring) (root : Fin n)
    (z : ref.State)
    (hz : WidthDigitLayoutFixed ref.toWidthDigitReference root z) (e : Fin n) :
    WidthDigitLayoutFixed ref.toWidthDigitReference root (ref.next z e) := by
  refine ⟨ref.singletonClosed root z hz.1 e, ?_⟩
  rw [ref.wordStep z (ref.singletonDrained root z hz.1) e]
  exact (AcceptedReceipts.qword_step ring _ hz.2 e).2

/-- The layout-fixed class together with the word equations at its root.
Consumer: `widthBoundaryDigitLayoutValuesStep`, `widthBoundaryDigitLayoutValuesWord`, `widthBoundaryCleanLayoutValuesOfSingleton`. -/
def WidthBoundaryDigitLayoutValues {n : Nat}
    {ring : DirectedRing n} (ref : WidthBoundaryReference ring) (root : Fin n)
    (z : ref.State) : Prop :=
  WidthDigitLayoutFixed ref.toWidthDigitReference root z ∧
    CleanWorkerWordValues ring root (piW (ref.phys z))

/-- Consumer: `widthBoundaryDigitLayoutValuesWord`. -/
theorem widthBoundaryDigitLayoutValuesStep {n : Nat}
    {ring : DirectedRing n} (ref : WidthBoundaryReference ring) (root : Fin n)
    (z : ref.State)
    (hz : WidthBoundaryDigitLayoutValues ref root z) (e : Fin n) :
    WidthBoundaryDigitLayoutValues ref root (ref.next z e) := by
  refine ⟨widthBoundaryDigitLayoutFixedStep ref root z hz.1 e, ?_⟩
  rw [ref.wordStep z (ref.singletonDrained root z hz.1.1) e]
  have hnb := (AcceptedReceipts.qword_step ring _ hz.1.2 e).1
  exact cleanWorkerWordValues_congr ring root _ _
    (fun i => Classical.byContradiction (fun hne => hnb ⟨i, hne⟩)) hz.2

/-- Consumer: `widthCleanBoundaryLayoutWord`. -/
theorem widthBoundaryDigitLayoutValuesWord {n : Nat}
    {ring : DirectedRing n} (ref : WidthBoundaryReference ring) (root : Fin n)
    (word : List (Fin n)) :
    ∀ z : ref.State,
      WidthBoundaryDigitLayoutValues ref root z →
      WidthBoundaryDigitLayoutValues ref root
        (word.foldl (ref.next) z) := by
  induction word with
  | nil => intro z hz; exact hz
  | cons e rest ih =>
      intro z hz
      exact ih _ (widthBoundaryDigitLayoutValuesStep ref root z hz e)

/-- Lifting a projected-ring stable predicate to the reference chain on the
layout-fixed class (no FIRE, no visible marker change, fixed leader).
Consumer: `widthCleanBoundaryLeadingStable`. -/
theorem widthBoundaryDigitBankStepOf {n : Nat}
    {ring : DirectedRing n} (ref : WidthBoundaryReference ring) (hn : 5 ≤ n) (root : Fin n)
    (P : (Fin n → ProjD (compileAdvice (ceilLogTwo n))) → Prop)
    (hP : ∀ (S : Fin n → ProjD (compileAdvice (ceilLogTwo n))) (e : Fin n),
      (∀ i, (S i).word.native.l = true ↔ i = root) →
      (pairW (S e).word (S (ring.rightNeighbor e)).word).1.beta = (S e).word.beta →
      (pairW (S e).word (S (ring.rightNeighbor e)).word).2.beta =
        (S (ring.rightNeighbor e)).word.beta →
      P S → P (phiD ring S e))
    (z : ref.State)
    (hz : WidthDigitLayoutFixed ref.toWidthDigitReference root z) (e : Fin n)
    (h : P (piD (ref.phys z))) :
    P (piD (ref.phys (ref.next z e))) := by
  rw [ref.digitStep z (ref.singletonDrained root z hz.1) e]
  have hnb := (AcceptedReceipts.qword_step ring _ hz.2 e).1
  have hvis : ∀ i, AcceptedReceipts.wordVisible (phiW ring (piW (ref.phys z)) e) i =
      AcceptedReceipts.wordVisible (piW (ref.phys z)) i := by
    intro i
    exact Classical.byContradiction (fun hne => hnb ⟨i, hne⟩)
  have hne : ring.rightNeighbor e ≠ e := bankRepairDigitRightNe ring (by omega) e
  have hbX := congrArg Prod.snd (hvis e)
  have hbY := congrArg Prod.snd (hvis (ring.rightNeighbor e))
  simp only [AcceptedReceipts.wordVisible, phiW, projectedEdge, if_pos rfl,
    if_neg hne] at hbX hbY
  have hroot : ∀ i, (piD (ref.phys z) i).word.native.l = true ↔ i = root := by
    intro i
    constructor
    · exact fun hi => (ref.singletonFixed root z hz.1).2.1 i hi
    · rintro rfl; exact (ref.singletonFixed i z hz.1).1
  exact hP (piD (ref.phys z)) e hroot hbX hbY h

/-- The leading half of the receipt at the actual (W fixed) leader.
Consumer: `widthCleanBoundaryLeadingStable`, `widthCleanBoundaryLeadingTasks`, `widthCleanBoundaryFinalTasks`. -/
def WidthBoundaryDigitLeaderLeading {n : Nat}
    {ring : DirectedRing n} (ref : WidthBoundaryReference ring) (z : ref.State) : Prop :=
  ∃ root : Fin n, WFixedRoot ring root (piW (ref.phys z)) ∧
    DigitLeadingBoundary ring root (piD (ref.phys z))

/-- A region task certificate: on every state reachable from `start`, a rank
that never increases before `target` and drops on one nominated edge, with
initial rank at most `budget`.
Consumer: `widthBoundaryDigitRegionClockOfTasks`, `widthCleanBoundaryLeadingTasks`, `widthCleanBoundaryFinalTasks`. -/
def WidthBoundaryDigitRegionTasks {n : Nat}
    {ring : DirectedRing n} (ref : WidthBoundaryReference ring) (start target : ref.State → Prop) (budget : Nat) : Prop :=
  ∃ (rank : ref.State → Nat)
    (chosen : ref.State → Fin n),
    (∀ z₀ (word : List (Fin n)), start z₀ →
      ¬ target (word.foldl (ref.next) z₀) →
      rank (ref.next (word.foldl (ref.next) z₀)
          (chosen (word.foldl (ref.next) z₀))) + 1 ≤
        rank (word.foldl (ref.next) z₀)) ∧
    (∀ z₀ (word : List (Fin n)), start z₀ →
      ¬ target (word.foldl (ref.next) z₀) → ∀ e : Fin n,
      rank (ref.next (word.foldl (ref.next) z₀) e) ≤
        rank (word.foldl (ref.next) z₀)) ∧
    (∀ z, start z → rank z ≤ budget)

/-- Consumer: `widthCleanBoundaryFlushClock`. -/
theorem widthBoundaryDigitRegionClockOfTasks {n : Nat}
    {ring : DirectedRing n} (ref : WidthBoundaryReference ring) (start target : ref.State → Prop) (budget : Nat)
    (htasks : WidthBoundaryDigitRegionTasks ref start target budget) :
    BankRepairDigitChargedStage (ref.next) start target
      (2 * (n * budget)) := by
  obtain ⟨rank, chosen, hdrop, hnoninc, hcap⟩ := htasks
  intro z hz T
  let Reach : ref.State → Prop := fun y =>
    ∃ w : List (Fin n), y = w.foldl (ref.next) z
  have hsplit : ∀ y, ¬ (target y ∨ ¬ Reach y) → Reach y ∧ ¬ target y := fun y h =>
    ⟨Classical.byContradiction (fun hb => h (Or.inr hb)), fun ha => h (Or.inl ha)⟩
  have hcost := L3.Prob.costNumerator_le_of_nominated_edge
    (ref.next) (fun y => target y ∨ ¬ Reach y) rank chosen
    (fun y hy => by
      obtain ⟨⟨w, rfl⟩, ht⟩ := hsplit y hy
      exact hdrop z w hz ht)
    (fun y hy => by
      obtain ⟨⟨w, rfl⟩, ht⟩ := hsplit y hy
      exact hnoninc z w hz ht) z T
  have htransfer := bankRepairDigitCostTransfer (ref.next)
    (ref.next) target (fun y => target y ∨ ¬ Reach y) T z z
    (fun w hw => hw.resolve_right (fun hn' => hn' ⟨w, rfl⟩))
  have hle : costNumerator (ref.next) target z T ≤
      n ^ T * (n * budget) :=
    Nat.le_trans htransfer (Nat.le_trans hcost
      (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (hcap z hz))))
  calc
    2 * costNumerator (ref.next) target z T ≤
        2 * (n ^ T * (n * budget)) := Nat.mul_le_mul_left 2 hle
    _ = n ^ T * (2 * (n * budget)) := Nat.mul_left_comm _ _ _

/-- Consumer: `widthCleanBoundaryRetiredOfReceipt`. -/
theorem widthBoundaryDigitAllGoneWord {n : Nat} (hn : 5 ≤ n)
    {ring : DirectedRing n} (ref : WidthBoundaryReference ring) :
    ∀ (w : List (Fin n)) (a : ref.State ×
        DigitAudit (compileAdvice (ceilLogTwo n)) n),
      widthDigitAllBaseLabelsGone ref.toWidthDigitReference a →
      widthDigitAllBaseLabelsGone ref.toWidthDigitReference
        (w.foldl (widthDigitAuditNext ref.toWidthDigitReference) a) := by
  intro w
  induction w with
  | nil => intro a h; exact h
  | cons e rest ih =>
      intro a h
      exact ih _ (widthBoundaryDigitAllBaseLabelsGoneClosed (by omega) ref a e h)


/-- The layout/value class at the clean W
root.  This is the old digit geometry's actual QWord and
CleanWorkerWordValues content, not its monitor provenance.
Consumer: `widthCleanBoundaryRoot`. -/
theorem widthBoundaryCleanLayoutValuesOfSingleton {n : Nat}
    {ring : DirectedRing n} (ref : WidthBoundaryReference ring) (root : Fin n) (z : ref.State)
    (hsingle : ref.singleton root z)
    (hword : CleanWord ring (piW (ref.phys z))) :
    WidthBoundaryDigitLayoutValues ref root z := by
  have hw : CleanWord ring (piW (ref.phys z)) := hword
  obtain ⟨r, hfixed, hvalues, hquiet⟩ := hw
  have heq : root = r := hfixed.2.1 root (ref.singletonFixed root z hsingle).1
  refine ⟨⟨hsingle, hquiet⟩, ?_⟩
  rw [heq]
  exact hvalues

/-- Layout data of the leading rank: fixed leader `root` and first delimiter `first`.
Consumer: `widthBoundaryDigitLeadDataStep`, `widthBoundaryDigitLeadDataUnique`, `widthBoundaryDigitFinRank`. -/
def WidthBoundaryDigitLeadData {n : Nat} {ring : DirectedRing n} (ref : WidthBoundaryReference ring) (root : Fin n) (first : Nat)
    (z : ref.State) : Prop :=
  WidthDigitLayoutFixed ref.toWidthDigitReference root z ∧ 0 < first ∧ first < n ∧
    ∀ k : Nat, 0 < k → k < n →
      ((piD (ref.phys z) (digitSite ring root k)).word.beta = true ↔
        first ≤ k ∧ (k - first) % digitSpan (compileAdvice (ceilLogTwo n)) = 0)

/-- Consumer: `widthBoundaryDigitLeadDataStep`, `widthCleanBoundaryLeadingTasks`, `widthCleanBoundaryFinalTasks`. -/
theorem widthBoundaryDigitLeadBankEdge {n : Nat} {ring : DirectedRing n} (ref : WidthBoundaryReference ring) (hn : 5 ≤ n) (root : Fin n)
    (z : ref.State) (hz : WidthDigitLayoutFixed ref.toWidthDigitReference root z)
    (e : Fin n) :
    piD (ref.phys (ref.next z e)) = phiD ring (piD (ref.phys z)) e ∧
    (∀ i, (piD (ref.phys z) i).word.native.l = true ↔ i = root) ∧
    (pairW (piD (ref.phys z) e).word (piD (ref.phys z) (ring.rightNeighbor e)).word).1.beta =
      (piD (ref.phys z) e).word.beta ∧
    (pairW (piD (ref.phys z) e).word (piD (ref.phys z) (ring.rightNeighbor e)).word).2.beta =
      (piD (ref.phys z) (ring.rightNeighbor e)).word.beta := by
  refine ⟨ref.digitStep z (ref.singletonDrained root z hz.1) e, ?_⟩
  have hnb := (AcceptedReceipts.qword_step ring _ hz.2 e).1
  have hvis : ∀ i, AcceptedReceipts.wordVisible (phiW ring (piW (ref.phys z)) e) i =
      AcceptedReceipts.wordVisible (piW (ref.phys z)) i := by
    intro i
    exact Classical.byContradiction (fun hne => hnb ⟨i, hne⟩)
  have hne : ring.rightNeighbor e ≠ e := bankRepairDigitRightNe ring (by omega) e
  have hbX := congrArg Prod.snd (hvis e)
  have hbY := congrArg Prod.snd (hvis (ring.rightNeighbor e))
  simp only [AcceptedReceipts.wordVisible, phiW, projectedEdge, if_pos rfl,
    if_neg hne] at hbX hbY
  refine ⟨fun i => ⟨fun hi => (ref.singletonFixed root z hz.1).2.1 i hi, ?_⟩, hbX, hbY⟩
  rintro rfl
  exact (ref.singletonFixed i z hz.1).1

/-- Consumer: `widthCleanBoundaryLeadingTasks`, `widthCleanBoundaryFinalTasks`. -/
theorem widthBoundaryDigitLeadDataStep {n : Nat} {ring : DirectedRing n} (ref : WidthBoundaryReference ring) (hn : 5 ≤ n) (root : Fin n) (first : Nat)
    (z : ref.State) (hd : WidthBoundaryDigitLeadData ref root first z)
    (e : Fin n) :
    WidthBoundaryDigitLeadData ref root first (ref.next z e) := by
  obtain ⟨hL, h0, h1, hb⟩ := hd
  obtain ⟨heq, _, hbX, hbY⟩ := widthBoundaryDigitLeadBankEdge ref hn root z hL e
  refine ⟨widthBoundaryDigitLayoutFixedStep ref root z hL e, h0, h1, fun k hk0 hkn => ?_⟩
  rw [heq, (bankRepairDigitPhiDAt ring (by omega) (piD (ref.phys z)) e hbX hbY).2.2.2]
  exact hb k hk0 hkn

/-- Consumer: `widthBoundaryDigitFinRankEq`, `widthBoundaryDigitLeadRankEq`. -/
theorem widthBoundaryDigitLeadDataUnique {n : Nat} {ring : DirectedRing n} (ref : WidthBoundaryReference ring) (root root' : Fin n)
    (first first' : Nat) (z : ref.State)
    (h : WidthBoundaryDigitLeadData ref root first z)
    (h' : WidthBoundaryDigitLeadData ref root' first' z) :
    root' = root ∧ first' = first := by
  have hr : root' = root :=
    (ref.singletonFixed root z h.1.1).2.1 root' (ref.singletonFixed root' z h'.1.1).1
  subst hr
  obtain ⟨_, h0, h1, hb⟩ := h
  obtain ⟨_, h0', h1', hb'⟩ := h'
  have a := ((hb first' h0' h1').1 ((hb' first' h0' h1').2
    ⟨Nat.le_refl _, by rw [Nat.sub_self, Nat.zero_mod]⟩)).1
  have b := ((hb' first h0 h1).1 ((hb first h0 h1).2
    ⟨Nat.le_refl _, by rw [Nat.sub_self, Nat.zero_mod]⟩)).1
  exact ⟨rfl, by omega⟩

open Classical in
/-- The final rank of a reference state (zero off the layout class).
Consumer: `widthBoundaryDigitFinRankEq`, `widthBoundaryDigitFinChosen`, `widthBoundaryDigitFinChosenSpec`. -/
noncomputable def widthBoundaryDigitFinRank {n : Nat} {ring : DirectedRing n} (ref : WidthBoundaryReference ring) (z : ref.State) : Nat :=
  if h : ∃ (root : Fin n) (first : Nat), WidthBoundaryDigitLeadData ref root first z then
    bankRepairDigitFinalRankOf ring (Classical.choose h)
      (digitSpan (compileAdvice (ceilLogTwo n)))
      (bankRepairDigitLastDelim (digitSpan (compileAdvice (ceilLogTwo n)))
        (Classical.choose (Classical.choose_spec h)) n)
      (piD (ref.phys z))
  else 0

/-- Consumer: `widthCleanBoundaryFinalTasks`. -/
theorem widthBoundaryDigitFinRankEq {n : Nat} {ring : DirectedRing n} (ref : WidthBoundaryReference ring) (root : Fin n) (first : Nat)
    (z : ref.State) (h : WidthBoundaryDigitLeadData ref root first z) :
    widthBoundaryDigitFinRank ref z =
      bankRepairDigitFinalRankOf ring root (digitSpan (compileAdvice (ceilLogTwo n)))
        (bankRepairDigitLastDelim (digitSpan (compileAdvice (ceilLogTwo n))) first n)
        (piD (ref.phys z)) := by
  have hex : ∃ (r : Fin n) (f : Nat), WidthBoundaryDigitLeadData ref r f z :=
    ⟨root, first, h⟩
  unfold widthBoundaryDigitFinRank
  rw [dif_pos hex]
  obtain ⟨e1, e2⟩ := widthBoundaryDigitLeadDataUnique ref _ _ _ _ z h
    (Classical.choose_spec (Classical.choose_spec hex))
  rw [e2, e1]

/-- The nominated edge: a dropping edge when one exists.
Consumer: `widthBoundaryDigitFinChosenSpec`, `widthCleanBoundaryFinalTasks`. -/
noncomputable def widthBoundaryDigitFinChosen {n : Nat} {ring : DirectedRing n} (ref : WidthBoundaryReference ring) (e0 : Fin n)
    (z : ref.State) : Fin n :=
  if h : ∃ e : Fin n, widthBoundaryDigitFinRank ref (ref.next z e) + 1 ≤
      widthBoundaryDigitFinRank ref z then Classical.choose h else e0

/-- Consumer: `widthCleanBoundaryFinalTasks`. -/
theorem widthBoundaryDigitFinChosenSpec {n : Nat} {ring : DirectedRing n} (ref : WidthBoundaryReference ring) (e0 : Fin n)
    (z : ref.State)
    (h : ∃ e : Fin n, widthBoundaryDigitFinRank ref (ref.next z e) + 1 ≤
      widthBoundaryDigitFinRank ref z) :
    widthBoundaryDigitFinRank ref
        (ref.next z (widthBoundaryDigitFinChosen ref e0 z)) + 1 ≤
      widthBoundaryDigitFinRank ref z := by
  unfold widthBoundaryDigitFinChosen
  rw [dif_pos h]
  exact Classical.choose_spec h

open Classical in
/-- The leading rank of a reference state (zero off the layout class).
Consumer: `widthBoundaryDigitLeadRankEq`, `widthBoundaryDigitLeadChosen`, `widthBoundaryDigitLeadChosenSpec`. -/
noncomputable def widthBoundaryDigitLeadRank {n : Nat} {ring : DirectedRing n} (ref : WidthBoundaryReference ring) (z : ref.State) : Nat :=
  if h : ∃ (root : Fin n) (first : Nat), WidthBoundaryDigitLeadData ref root first z then
    bankRepairDigitLeadRankOf ring (Classical.choose h)
      (digitSpan (compileAdvice (ceilLogTwo n))) (Classical.choose (Classical.choose_spec h))
      (piD (ref.phys z))
  else 0

/-- Consumer: `widthCleanBoundaryLeadingTasks`. -/
theorem widthBoundaryDigitLeadRankEq {n : Nat} {ring : DirectedRing n} (ref : WidthBoundaryReference ring) (root : Fin n) (first : Nat)
    (z : ref.State) (h : WidthBoundaryDigitLeadData ref root first z) :
    widthBoundaryDigitLeadRank ref z =
      bankRepairDigitLeadRankOf ring root (digitSpan (compileAdvice (ceilLogTwo n))) first
        (piD (ref.phys z)) := by
  have hex : ∃ (r : Fin n) (f : Nat), WidthBoundaryDigitLeadData ref r f z :=
    ⟨root, first, h⟩
  unfold widthBoundaryDigitLeadRank
  rw [dif_pos hex]
  obtain ⟨e1, e2⟩ := widthBoundaryDigitLeadDataUnique ref _ _ _ _ z h
    (Classical.choose_spec (Classical.choose_spec hex))
  rw [e2, e1]

/-- The nominated edge: a dropping edge when one exists.
Consumer: `widthBoundaryDigitLeadChosenSpec`, `widthCleanBoundaryLeadingTasks`. -/
noncomputable def widthBoundaryDigitLeadChosen {n : Nat} {ring : DirectedRing n} (ref : WidthBoundaryReference ring) (e0 : Fin n)
    (z : ref.State) : Fin n :=
  if h : ∃ e : Fin n, widthBoundaryDigitLeadRank ref (ref.next z e) + 1 ≤
      widthBoundaryDigitLeadRank ref z then Classical.choose h else e0

/-- Consumer: `widthCleanBoundaryLeadingTasks`. -/
theorem widthBoundaryDigitLeadChosenSpec {n : Nat} {ring : DirectedRing n} (ref : WidthBoundaryReference ring) (e0 : Fin n)
    (z : ref.State)
    (h : ∃ e : Fin n, widthBoundaryDigitLeadRank ref (ref.next z e) + 1 ≤
      widthBoundaryDigitLeadRank ref z) :
    widthBoundaryDigitLeadRank ref
        (ref.next z (widthBoundaryDigitLeadChosen ref e0 z)) + 1 ≤
      widthBoundaryDigitLeadRank ref z := by
  unfold widthBoundaryDigitLeadChosen
  rw [dif_pos h]
  exact Classical.choose_spec h


/-! ### The boundary stage at the clean start -/

/-- The clean start has a singleton root with the layout values (`QWord` and the root word
values).  Consumer: `widthCleanBoundaryRetiredOfReceipt`, `widthCleanBoundaryFlushClock`. -/
theorem widthCleanBoundaryRoot {n : Nat} {ring : DirectedRing n}
    (ref : WidthBoundaryReference ring) (z : ref.State) (hz : ref.start z) :
    ∃ root, ref.singleton root z ∧ WidthBoundaryDigitLayoutValues ref root z := by
  obtain ⟨root, hfixed, _, _⟩ := ref.startClean z hz
  have hs : ref.singleton root z := ref.singletonOfStart root z hz hfixed
  exact ⟨root, hs, widthBoundaryCleanLayoutValuesOfSingleton ref root z hs (ref.startClean z hz)⟩

/-- Along the one-label audit from a singleton start with `QWord`: drained, leader bits and
delimiters frozen.  Consumer: `widthCleanBoundaryLabelTasks`. -/
theorem widthCleanBoundaryFrozen {n : Nat} {ring : DirectedRing n}
    (ref : WidthBoundaryReference ring) (start : ref.State)
    (root : Fin n) (hs : ref.singleton root start)
    (hq : AcceptedReceipts.QWord ring (piW (ref.phys start))) :
    ∀ z, WidthBoundaryDigitOneLabelReachableFrom ref start z →
      ref.drained z.1 ∧
      (∀ i, (piD (ref.phys z.1) i).word.native.l = (piD (ref.phys start) i).word.native.l) ∧
      (∀ i, (piD (ref.phys z.1) i).word.beta = (piD (ref.phys start) i).word.beta) := by
  intro z hz
  obtain ⟨hzs, -, hzb⟩ := widthBoundaryDigitProducedReachableInv ref start root hs hq z hz
  refine ⟨ref.singletonDrained root z.1 hzs, ?_, hzb⟩
  intro i
  show ((ref.phys z.1) i).l = ((ref.phys start) i).l
  rw [widthBoundaryDigitRootedLeader ref root z.1 hzs i,
    widthBoundaryDigitRootedLeader ref root start hs i]

/-- The single-inherited-label tasks at every site of a clean start.  Consumer:
`widthCleanBoundaryExtinctionClock`. -/
theorem widthCleanBoundaryLabelTasks {n : Nat} {ring : DirectedRing n}
    (ref : WidthBoundaryReference ring) (hn : 5 ≤ n) (z : ref.State) (hz : ref.start z) :
    ∀ site, WidthBoundaryDigitSingleInheritedLabelTasks ref z site := by
  obtain ⟨root, hfixed, hvalues, hq⟩ := ref.startClean z hz
  have hs : ref.singleton root z := ref.singletonOfStart root z hz hfixed
  intro site
  exact widthBoundaryDigitSingleInheritedLabelTasksOfFrozenInit (by omega) ref z site _ _
    (widthCleanBoundaryFrozen ref z root hs hq)
    (bankRepairDigitLabelInitialInvExempt ring _ _ _ (widthBoundaryDigitLeadingLengthPos hn)
      site _ (widthBoundaryDigitNonRootStopOfWordValues hn ref z root hfixed.1 hvalues site))

/-- **Label extinction from the clean start** into the gone cut, at the extinction charge.
Consumer: `widthDigitBoundaryStageOfReference`. -/
theorem widthCleanBoundaryExtinctionClock {n : Nat} {ring : DirectedRing n}
    (ref : WidthBoundaryReference ring) (hn : 5 ≤ n) :
    BankRepairDigitChargedStage ref.next ref.start
      (WidthDigitGoneCut ref.toWidthDigitReference) (widthBoundaryExtinctionCharge n) := by
  intro z hz T
  have hcost := widthBoundaryDigitAllBaseCostLogarithmicOfTasks (by omega : 2 ≤ n) ref z
    (widthCleanBoundaryLabelTasks ref hn z hz) T
  have htr := bankRepairDigitCostTransfer
      ref.next (widthDigitAuditNext ref.toWidthDigitReference)
      (WidthDigitGoneCut ref.toWidthDigitReference)
      (widthDigitAllBaseLabelsGone ref.toWidthDigitReference) T _ _
      (fun word hg => ⟨z, word, hz, hg, rfl⟩)
  refine Nat.le_trans (Nat.mul_le_mul_left 2 (Nat.le_trans htr hcost)) (Nat.le_of_eq ?_)
  unfold widthBoundaryExtinctionCharge
  ac_rfl

/-- The layout-values class at some root.  Consumer: the two flush regions. -/
def WidthCleanBoundaryLayout {n : Nat} {ring : DirectedRing n}
    (ref : WidthBoundaryReference ring) (z : ref.State) : Prop :=
  ∃ root, WidthBoundaryDigitLayoutValues ref root z

/-- The layout-values class is closed under words.  Consumer: the two flush regions. -/
theorem widthCleanBoundaryLayoutWord {n : Nat} {ring : DirectedRing n}
    (ref : WidthBoundaryReference ring) (z : ref.State)
    (hz : WidthCleanBoundaryLayout ref z) (word : List (Fin n)) :
    WidthCleanBoundaryLayout ref (word.foldl ref.next z) := by
  obtain ⟨root, h⟩ := hz
  exact ⟨root, widthBoundaryDigitLayoutValuesWord ref root word z h⟩

/-- The delimiters of a layout-values state.  Consumer: `widthCleanBoundaryLeadData`,
`widthCleanBoundaryFinData`. -/
theorem widthCleanBoundaryDelimiters {n : Nat} {ring : DirectedRing n}
    (ref : WidthBoundaryReference ring) (hn : 5 ≤ n)
    (root : Fin n) (z : ref.State) (hL : WidthBoundaryDigitLayoutValues ref root z) :
    ∃ first : Nat,
      (compileAdvice (ceilLogTwo n)).t ≤ first ∧
      first < (compileAdvice (ceilLogTwo n)).t + digitSpan (compileAdvice (ceilLogTwo n)) ∧
      ∀ k : Nat, 0 < k → k < n →
        ((piD (ref.phys z) (digitSite ring root k)).word.beta = true ↔
          first ≤ k ∧ (k - first) % digitSpan (compileAdvice (ceilLogTwo n)) = 0) := by
  have hq := ringQ_facts n hn
  have ht : 2 ≤ (compileAdvice (ceilLogTwo n)).t :=
    compileAdvice_t_ge_two (ceilLogTwo n) hq.1
  have hprim := tapTablePrimitive (compileAdvice (ceilLogTwo n)).t ht
  obtain ⟨d, hd, hk⟩ := bankRepairDigitDelimiterLayout ring root _ hL.2 (by omega) hprim
  refine ⟨(compileAdvice (ceilLogTwo n)).t + d, by omega, ?_, fun k h0 hkn => ?_⟩
  · unfold digitSpan; omega
  · rw [bankRepairDigitSiteShift]
    exact hk k h0 hkn

/-- Lead data on the layout-values class.  Consumer: `widthCleanBoundaryLeadingTasks`. -/
theorem widthCleanBoundaryLeadData {n : Nat} {ring : DirectedRing n}
    (ref : WidthBoundaryReference ring) (hn : 5 ≤ n)
    (hlead : (compileAdvice (ceilLogTwo n)).t +
      digitSpan (compileAdvice (ceilLogTwo n)) ≤ n)
    (z : ref.State) (hz : WidthCleanBoundaryLayout ref z) :
    ∃ (root : Fin n) (first : Nat), WidthBoundaryDigitLeadData ref root first z ∧
      first + 1 ≤ (compileAdvice (ceilLogTwo n)).t +
        digitSpan (compileAdvice (ceilLogTwo n)) := by
  obtain ⟨root, hL⟩ := hz
  obtain ⟨first, ht, hf, hb⟩ := widthCleanBoundaryDelimiters ref hn root z hL
  have ht2 := compileAdvice_t_ge_two (ceilLogTwo n) (ringQ_facts n hn).1
  exact ⟨root, first, ⟨hL.1, by omega, by omega, hb⟩, by omega⟩

/-- Final-region data on the layout-values class.  Consumer: `widthCleanBoundaryFinalTasks`. -/
theorem widthCleanBoundaryFinData {n : Nat} {ring : DirectedRing n}
    (ref : WidthBoundaryReference ring) (hn : 5 ≤ n)
    (hlead : (compileAdvice (ceilLogTwo n)).t +
      digitSpan (compileAdvice (ceilLogTwo n)) ≤ n)
    (z : ref.State) (hz : WidthCleanBoundaryLayout ref z) :
    ∃ (root : Fin n) (first : Nat), WidthBoundaryDigitLeadData ref root first z ∧
      2 ≤ first := by
  obtain ⟨root, hL⟩ := hz
  obtain ⟨first, ht, hf, hb⟩ := widthCleanBoundaryDelimiters ref hn root z hL
  have ht2 := compileAdvice_t_ge_two (ceilLogTwo n) (ringQ_facts n hn).1
  exact ⟨root, first, ⟨hL.1, by omega, by omega, hb⟩, by omega⟩

/-- With a single delimiter (`n ≤ first + R`, `R = 2^t - 1`) there is no complete block, so
the final boundary holds vacuously.  This is the case of the small rings `n < t + 2R`
(at `q = 3`: `n ∈ {5, 6, 7}`).  Consumer: `widthCleanBoundaryFinalTasks`. -/
theorem widthCleanBoundaryFinalVacuous {n : Nat} {ring : DirectedRing n}
    (ref : WidthBoundaryReference ring) (root : Fin n) (first : Nat) (z : ref.State)
    (hd : WidthBoundaryDigitLeadData ref root first z)
    (hw : n ≤ first + digitSpan (compileAdvice (ceilLogTwo n))) :
    DigitFinalBoundary ring root (piD (ref.phys z)) := by
  unfold DigitFinalBoundary
  intro source last hblock
  exfalso
  obtain ⟨⟨⟨h0, hlt, hbeta⟩, -⟩, hend⟩ := hblock
  have hge := ((hd.2.2.2 source h0 hlt).1 hbeta).1
  omega

/-- The leading half of the receipt is never lost on the layout-values class.  Consumer:
`widthCleanBoundaryFinalTasks`. -/
theorem widthCleanBoundaryLeadingStable {n : Nat} {ring : DirectedRing n}
    (ref : WidthBoundaryReference ring) (hn : 5 ≤ n) (z : ref.State)
    (hz : WidthCleanBoundaryLayout ref z)
    (hrec : WidthBoundaryDigitLeaderLeading ref z) (word : List (Fin n)) :
    WidthBoundaryDigitLeaderLeading ref (word.foldl ref.next z) := by
  obtain ⟨root, hL⟩ := hz
  obtain ⟨r, hW, hr⟩ := hrec
  have hrr : r = root := (ref.singletonFixed root z hL.1.1).2.1 r hW.1
  subst hrr
  refine ⟨r, widthBoundaryDigitBoundaryWFixedRootOfSingleton ref r z hL.1.1 word, ?_⟩
  have key : ∀ (w : List (Fin n)) (y : ref.State),
      WidthDigitLayoutFixed ref.toWidthDigitReference r y →
      DigitLeadingBoundary ring r (piD (ref.phys y)) →
      DigitLeadingBoundary ring r (piD (ref.phys (w.foldl ref.next y))) := by
    intro w
    induction w with
    | nil => intro y _ h; exact h
    | cons e rest ih =>
        intro y hy h
        exact ih _ (widthBoundaryDigitLayoutFixedStep ref r y hy e)
          (widthBoundaryDigitBankStepOf ref hn r (DigitLeadingBoundary ring r)
            (fun S e hroot hbX hbY h => bankRepairDigitLeadingStep ring (by omega) r S e
              (bankRepairDigitLaneRowFactsHold _) hroot hbX hbY h) y hy e h)
  exact key word z hL.1 hr

/-- **Leading region** on the layout-values class, at budget `2 J_t`.  Consumer:
`widthCleanBoundaryFlushClock`. -/
theorem widthCleanBoundaryLeadingTasks {n : Nat} {ring : DirectedRing n}
    (ref : WidthBoundaryReference ring) (hn : 5 ≤ n)
    (hlead : (compileAdvice (ceilLogTwo n)).t +
      digitSpan (compileAdvice (ceilLogTwo n)) ≤ n) :
    WidthBoundaryDigitRegionTasks ref (WidthCleanBoundaryLayout ref)
      (fun z => WidthCleanBoundaryLayout ref z ∧ WidthBoundaryDigitLeaderLeading ref z)
      (2 * bankRepairDigitBoundaryServices (compileAdvice (ceilLogTwo n)).t) := by
  have hR := widthBoundaryDigitSpanTwo hn
  refine ⟨widthBoundaryDigitLeadRank ref,
    widthBoundaryDigitLeadChosen ref ⟨0, by omega⟩, ?_, ?_, ?_⟩
  · intro z₀ word hz₀ hnt
    have hz := widthCleanBoundaryLayoutWord ref z₀ hz₀ word
    generalize word.foldl ref.next z₀ = z at hz hnt ⊢
    obtain ⟨root, first, hd, -⟩ := widthCleanBoundaryLeadData ref hn hlead z hz
    apply widthBoundaryDigitLeadChosenSpec
    have hnb : ¬ DigitLeadingBoundary ring root (piD (ref.phys z)) := fun hb =>
      hnt ⟨hz, root,
        widthBoundaryDigitBoundaryWFixedRootOfSingleton ref root z hd.1.1 [], hb⟩
    have hedge := fun e => widthBoundaryDigitLeadBankEdge ref hn root z hd.1 e
    obtain ⟨k, _, hdrop⟩ := bankRepairDigitLeadRankDrop ring (by omega) root (piD (ref.phys z))
      (digitSpan (compileAdvice (ceilLogTwo n))) first hR hd.2.1 hd.2.2.1 (hedge root).2.1
      hd.2.2.2
      (fun k _ => ⟨(hedge (digitSite ring root k)).2.2.1, (hedge (digitSite ring root k)).2.2.2⟩)
      hnb
    refine ⟨digitSite ring root k, ?_⟩
    rw [widthBoundaryDigitLeadRankEq ref root first _
        (widthBoundaryDigitLeadDataStep ref hn root first z hd _),
      widthBoundaryDigitLeadRankEq ref root first z hd, (hedge _).1]
    exact hdrop
  · intro z₀ word hz₀ _ e
    have hz := widthCleanBoundaryLayoutWord ref z₀ hz₀ word
    generalize word.foldl ref.next z₀ = z at hz ⊢
    obtain ⟨root, first, hd, -⟩ := widthCleanBoundaryLeadData ref hn hlead z hz
    obtain ⟨k, hk, rfl⟩ := bankRepairDigitSiteSurj ring root e
    have hedge := fun e => widthBoundaryDigitLeadBankEdge ref hn root z hd.1 e
    rw [widthBoundaryDigitLeadRankEq ref root first _
        (widthBoundaryDigitLeadDataStep ref hn root first z hd _),
      widthBoundaryDigitLeadRankEq ref root first z hd, (hedge _).1]
    exact bankRepairDigitLeadRankStep ring (by omega) root (piD (ref.phys z))
      (digitSpan (compileAdvice (ceilLogTwo n))) first hR hd.2.2.1 (hedge root).2.1 hd.2.2.2
      k hk (hedge _).2.2.1 (hedge _).2.2.2
  · intro z hz
    obtain ⟨root, first, hd, hfle⟩ := widthCleanBoundaryLeadData ref hn hlead z hz
    rw [widthBoundaryDigitLeadRankEq ref root first z hd]
    have hb := bankRepairDigitLeadRankOfBound ring root (piD (ref.phys z))
      (digitSpan (compileAdvice (ceilLogTwo n))) first (by omega) hd.2.1
    have hA : first - 1 ≤ bankRepairDigitLeadingRecords (compileAdvice (ceilLogTwo n)).t := by
      unfold bankRepairDigitLeadingRecords bankRepairDigitRadius
      unfold digitSpan at hfle
      omega
    exact Nat.le_trans hb (bankRepairDigitLeadBudgetFits _ _ hA)

/-- **Final region** on the layout-values class, at budget `F + R + U + r` with
`r = 2^t - 1`.  Consumer: `widthCleanBoundaryFlushClock`. -/
theorem widthCleanBoundaryFinalTasks {n : Nat} {ring : DirectedRing n}
    (ref : WidthBoundaryReference ring) (hn : 5 ≤ n)
    (hlead : (compileAdvice (ceilLogTwo n)).t +
      digitSpan (compileAdvice (ceilLogTwo n)) ≤ n) :
    WidthBoundaryDigitRegionTasks ref
      (fun z => WidthCleanBoundaryLayout ref z ∧ WidthBoundaryDigitLeaderLeading ref z)
      (fun z => WidthCleanBoundaryLayout ref z ∧ WidthDigitLeaderReceipt ref.toWidthDigitReference z)
      (bankRepairDigitForwardCount (bankRepairDigitRadius (compileAdvice (ceilLogTwo n)).t) +
        bankRepairDigitReturnCount (bankRepairDigitRadius (compileAdvice (ceilLogTwo n)).t) +
        bankRepairDigitSettledCount (bankRepairDigitRadius (compileAdvice (ceilLogTwo n)).t) +
        bankRepairDigitRadius (compileAdvice (ceilLogTwo n)).t) := by
  have hR := widthBoundaryDigitSpanTwo hn
  refine ⟨widthBoundaryDigitFinRank ref,
    widthBoundaryDigitFinChosen ref ⟨0, by omega⟩, ?_, ?_, ?_⟩
  · intro z₀ word hz₀ hnt
    have hz := widthCleanBoundaryLayoutWord ref z₀ hz₀.1 word
    have hls := widthCleanBoundaryLeadingStable ref hn z₀ hz₀.1 hz₀.2 word
    generalize word.foldl ref.next z₀ = z at hz hls hnt ⊢
    obtain ⟨root, first, hd, hf2⟩ := widthCleanBoundaryFinData ref hn hlead z hz
    obtain ⟨r', hW, hlb⟩ := hls
    have hr : r' = root := (ref.singletonFixed root z hd.1.1).2.1 r' hW.1
    subst hr
    by_cases hw : first + digitSpan (compileAdvice (ceilLogTwo n)) + 1 ≤ n
    · have hedge := fun e => widthBoundaryDigitLeadBankEdge ref hn r' z hd.1 e
      obtain ⟨hRL, hLn, _, hbS, hbL, hbF, hmax⟩ := bankRepairDigitFinLayout ring r'
        (piD (ref.phys z)) (digitSpan (compileAdvice (ceilLogTwo n))) first hR hf2 hw hd.2.2.2
      have hnf : ¬ DigitFinalBoundary ring r' (piD (ref.phys z)) := fun hf =>
        hnt ⟨hz, r', hW, hlb, hf⟩
      apply widthBoundaryDigitFinChosenSpec
      obtain ⟨lane0, j0, hj0, hbad⟩ := bankRepairDigitFinalFailing ring r' (piD (ref.phys z)) _
        hLn hbL hmax hnf
      obtain ⟨k, _, hdrop⟩ := bankRepairDigitFinalRankDrop ring (by omega) r' (piD (ref.phys z))
        (digitSpan (compileAdvice (ceilLogTwo n)))
        (bankRepairDigitLastDelim (digitSpan (compileAdvice (ceilLogTwo n))) first n)
        hR hRL hLn (hedge r').2.1 hbS hbL hbF
        (fun k _ => ⟨(hedge (digitSite ring r' k)).2.2.1, (hedge (digitSite ring r' k)).2.2.2⟩)
        lane0 j0 hj0 hbad
      refine ⟨digitSite ring r' k, ?_⟩
      rw [widthBoundaryDigitFinRankEq ref r' first _
          (widthBoundaryDigitLeadDataStep ref hn r' first z hd _),
        widthBoundaryDigitFinRankEq ref r' first z hd, (hedge _).1]
      exact hdrop
    · exact absurd ⟨hz, r', hW, hlb,
        widthCleanBoundaryFinalVacuous ref r' first z hd (by omega)⟩ hnt
  · intro z₀ word hz₀ hnt e
    have hz := widthCleanBoundaryLayoutWord ref z₀ hz₀.1 word
    have hls := widthCleanBoundaryLeadingStable ref hn z₀ hz₀.1 hz₀.2 word
    generalize word.foldl ref.next z₀ = z at hz hls hnt ⊢
    obtain ⟨root, first, hd, hf2⟩ := widthCleanBoundaryFinData ref hn hlead z hz
    by_cases hw : first + digitSpan (compileAdvice (ceilLogTwo n)) + 1 ≤ n
    · obtain ⟨k, hk, rfl⟩ := bankRepairDigitSiteSurj ring root e
      have hedge := fun e => widthBoundaryDigitLeadBankEdge ref hn root z hd.1 e
      obtain ⟨hRL, hLn, _, hbS, hbL, hbF, _⟩ := bankRepairDigitFinLayout ring root
        (piD (ref.phys z)) (digitSpan (compileAdvice (ceilLogTwo n))) first hR hf2 hw hd.2.2.2
      rw [widthBoundaryDigitFinRankEq ref root first _
          (widthBoundaryDigitLeadDataStep ref hn root first z hd _),
        widthBoundaryDigitFinRankEq ref root first z hd, (hedge _).1]
      exact bankRepairDigitFinalRankStep ring (by omega) root (piD (ref.phys z))
        (digitSpan (compileAdvice (ceilLogTwo n)))
        (bankRepairDigitLastDelim (digitSpan (compileAdvice (ceilLogTwo n))) first n)
        hR hRL hLn (hedge root).2.1 hbS hbL hbF
        (fun k _ => ⟨(hedge (digitSite ring root k)).2.2.1, (hedge (digitSite ring root k)).2.2.2⟩)
        k hk
    · exfalso
      obtain ⟨r', hW, hlb⟩ := hls
      have hr : r' = root := (ref.singletonFixed root z hd.1.1).2.1 r' hW.1
      subst hr
      exact hnt ⟨hz, r', hW, hlb, widthCleanBoundaryFinalVacuous ref r' first z hd (by omega)⟩
  · intro z hz
    obtain ⟨root, first, hd, hf2⟩ := widthCleanBoundaryFinData ref hn hlead z hz.1
    have hfn : first < n := hd.2.2.1
    have hnL : n - bankRepairDigitLastDelim (digitSpan (compileAdvice (ceilLogTwo n))) first n ≤
        digitSpan (compileAdvice (ceilLogTwo n)) := by
      unfold bankRepairDigitLastDelim
      have h1 := Nat.div_add_mod (n - 1 - first) (digitSpan (compileAdvice (ceilLogTwo n)))
      have h2 := Nat.mod_lt (n - 1 - first)
        (by omega : 0 < digitSpan (compileAdvice (ceilLogTwo n)))
      generalize (n - 1 - first) / digitSpan (compileAdvice (ceilLogTwo n)) = d at h1 ⊢
      generalize (n - 1 - first) % digitSpan (compileAdvice (ceilLogTwo n)) = r at h1 h2
      generalize digitSpan (compileAdvice (ceilLogTwo n)) * d = sd at h1 ⊢
      omega
    rw [widthBoundaryDigitFinRankEq ref root first z hd]
    have h1 := bankRepairDigitFinalRankLe ring root (digitSpan (compileAdvice (ceilLogTwo n)))
      (bankRepairDigitLastDelim (digitSpan (compileAdvice (ceilLogTwo n))) first n)
      (piD (ref.phys z))
    have h2 := bankRepairDigitFinalBudget (digitSpan (compileAdvice (ceilLogTwo n)))
      (n - bankRepairDigitLastDelim (digitSpan (compileAdvice (ceilLogTwo n))) first n)
      (by omega) hnL
    exact Nat.le_trans h1 h2

/-- A state reachable from the gone cut with the leader receipt is in the boundary cut (the
audit restarted at the clean start keeps every label gone and its invariant).  Consumer:
`widthCleanBoundaryFlushClock`. -/
theorem widthCleanBoundaryRetiredOfReceipt {n : Nat} {ring : DirectedRing n}
    (ref : WidthBoundaryReference ring) (hn : 5 ≤ n) (z : ref.State)
    (hz : WidthDigitGoneReachable ref.toWidthDigitReference z)
    (hrec : WidthDigitLeaderReceipt ref.toWidthDigitReference z) :
    WidthDigitBoundaryRetiredCut ref.toWidthDigitReference z := by
  obtain ⟨_, word', ⟨start, word, hst, hg, rfl⟩, rfl⟩ := hz
  obtain ⟨root, hs, -⟩ := widthCleanBoundaryRoot ref start hst
  rw [← List.foldl_append] at hrec ⊢
  have hg' : widthDigitAllBaseLabelsGone ref.toWidthDigitReference
      ((word ++ word').foldl (widthDigitAuditNext ref.toWidthDigitReference)
        (start, digitAuditInitial (piD (ref.phys start)))) := by
    rw [List.foldl_append]
    exact widthBoundaryDigitAllGoneWord hn ref word' _ hg
  generalize word ++ word' = w at hrec hg' ⊢
  obtain ⟨r, hW, hr⟩ := hrec
  have hr' : r = root :=
    (widthBoundaryDigitBoundaryWFixedRootOfSingleton ref root start hs w).2.1 r hW.1
  subst hr'
  have hinv := widthBoundaryDigitBoundaryAuditInvariantRun ref hn r start hs w
  have hfirst := widthBoundaryDigitBoundaryAuditFirst ref start
    (digitAuditInitial (piD (ref.phys start))) w
  have hat := hinv.2.1
  rw [hfirst] at hat
  refine ⟨start, w, r,
    (w.foldl (widthDigitAuditNext ref.toWidthDigitReference)
      (start, digitAuditInitial (piD (ref.phys start)))).2, hst, ?_,
    widthBoundaryDigitBoundaryWFixedRootOfSingleton ref r start hs w,
    hat, hr,
    widthBoundaryDigitBoundaryBaseExtinctOfSingleton ref hn r start hs w hg'⟩
  exact Prod.ext hfirst rfl

/-- **The receipt flush from the gone cut** at the flush charge, landing in the boundary cut on
a state still reachable from the gone cut.  Consumer: `widthDigitBoundaryStageOfReference`. -/
theorem widthCleanBoundaryFlushClock {n : Nat} {ring : DirectedRing n}
    (ref : WidthBoundaryReference ring) (hn : 5 ≤ n)
    (hlead : (compileAdvice (ceilLogTwo n)).t +
      digitSpan (compileAdvice (ceilLogTwo n)) ≤ n) :
    BankRepairDigitChargedStage ref.next (WidthDigitGoneCut ref.toWidthDigitReference)
      (fun z => WidthDigitBoundaryRetiredCut ref.toWidthDigitReference z ∧
        WidthDigitGoneReachable ref.toWidthDigitReference z)
      (widthBoundaryFlushCharge n) := by
  have hleadClock := widthBoundaryDigitRegionClockOfTasks ref _ _ _
    (widthCleanBoundaryLeadingTasks ref hn hlead)
  have hfin := widthBoundaryDigitRegionClockOfTasks ref _ _ _
    (widthCleanBoundaryFinalTasks ref hn hlead)
  have h := bankRepairDigitZeroCompose ref.next _ _ _ _ _ hleadClock hfin
  intro z hz T
  have hzl : WidthCleanBoundaryLayout ref z := by
    obtain ⟨start, word, hst, -, hzeq⟩ := id hz
    obtain ⟨root, -, hL⟩ := widthCleanBoundaryRoot ref start hst
    rw [hzeq]
    exact widthCleanBoundaryLayoutWord ref start ⟨root, hL⟩ word
  have htr := bankRepairDigitCostTransfer ref.next ref.next
    (fun y => WidthDigitBoundaryRetiredCut ref.toWidthDigitReference y ∧
      WidthDigitGoneReachable ref.toWidthDigitReference y)
    (fun y => WidthCleanBoundaryLayout ref y ∧ WidthDigitLeaderReceipt ref.toWidthDigitReference y)
    T z z
    (fun w hw => ⟨widthCleanBoundaryRetiredOfReceipt ref hn _ ⟨z, w, hz, rfl⟩ hw.2,
      z, w, hz, rfl⟩)
  exact Nat.le_trans (Nat.mul_le_mul_left 2 htr) (h z hzl T)

/-- **The R10c boundary stage on a boundary reference**: from the clean start, the boundary
cut with the drain retained, at `widthBoundaryCharge n`, given the leading
width `t + (2^t - 1) ≤ n`.  Consumer: `smallWidthBoundaryStage`. -/
theorem widthDigitBoundaryStageOfReference {n : Nat} {ring : DirectedRing n}
    (ref : WidthBoundaryReference ring) (hn : 5 ≤ n)
    (hlead : (compileAdvice (ceilLogTwo n)).t +
      digitSpan (compileAdvice (ceilLogTwo n)) ≤ n) :
    WidthDigitBoundaryStage ref.toWidthDigitReference (widthBoundaryCharge n) :=
  widthCleanDigitChargedCarryDrain ref.toWidthDigitReference _ _ _ ref.startDrained
    (bankRepairDigitZeroCompose ref.next _ _ _ _ _
      (widthCleanBoundaryExtinctionClock ref hn)
      (widthCleanBoundaryFlushClock ref hn hlead))

/-! ### SMALL -/

/-- On SMALL: the leading width `t + (2^t - 1) ≤ n` and `t ≤ 17` (tight at `q = 3`,
`t = 2`, `n = 5`).  Consumer: `smallWidthBoundaryStage`. -/
theorem widthBoundaryWidthSmall {n : Nat} (hn : 5 ≤ n)
    (hsmall : (compileAdvice (ceilLogTwo n)).useSmall = true) :
    (compileAdvice (ceilLogTwo n)).t + digitSpan (compileAdvice (ceilLogTwo n)) ≤ n ∧
      (compileAdvice (ceilLogTwo n)).t ≤ 17 := by
  obtain ⟨hlo, hhi⟩ := L3.SmallFinishClean.smallDigitSliceBounds hn hsmall
  have hpop := (ceilLogTwo_spec n (by omega : 2 ≤ n)).1
  unfold digitSpan
  generalize ceilLogTwo n = q at hlo hhi hpop ⊢
  by_cases h32 : q ≤ 32
  · rw [compileAdvice_t_finite q hlo h32]
    unfold finiteCertWidth
    by_cases h4 : q ≤ 4
    · rw [if_pos h4]
      have e2 : (2 : Nat) ^ 2 = 4 := by decide
      omega
    · rw [if_neg h4]
      have h5 : 2 ^ 4 ≤ 2 ^ (q - 1) := Nat.pow_le_pow_right (by omega) (by omega)
      have e4 : (2 : Nat) ^ 4 = 16 := by decide
      by_cases h16 : q ≤ 16
      · rw [if_pos h16]
        have e3 : (2 : Nat) ^ 3 = 8 := by decide
        omega
      · rw [if_neg h16]
        have h17' : 2 ^ 16 ≤ 2 ^ (q - 1) := Nat.pow_le_pow_right (by omega) (by omega)
        have e5 : (2 : Nat) ^ 5 = 32 := by decide
        have e16 : (2 : Nat) ^ 16 = 65536 := by decide
        omega
  · rw [compileAdvice_t_large q (by omega)]
    have hc := ceilLogTwo_spec q (by omega)
    have e7 : (2 : Nat) ^ 7 = 128 := by decide
    have hc7 : ceilLogTwo q ≤ 7 := by
      by_cases h : ceilLogTwo q ≤ 7
      · exact h
      · have : 2 ^ 7 ≤ 2 ^ (ceilLogTwo q - 1) := Nat.pow_le_pow_right (by omega) (by omega)
        omega
    have hp : 2 ^ ceilLogTwo q ≤ 2 ^ 7 := Nat.pow_le_pow_right (by omega) hc7
    have h32' : 2 ^ 32 ≤ 2 ^ (q - 1) := Nat.pow_le_pow_right (by omega) (by omega)
    have e32 : (2 : Nat) ^ 32 = 4294967296 := by decide
    omega

/-- **The boundary stage on SMALL** (every SMALL ring) at `widthBoundaryCharge n`.
Consumer: `bandWidthBoundaryStageSmall`. -/
theorem smallWidthBoundaryStage {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hsmall : (compileAdvice (ceilLogTwo n)).useSmall = true) :
    WidthDigitBoundaryStage (smallWidthDigitReference ring hn hsmall)
      (widthBoundaryCharge n) :=
  widthDigitBoundaryStageOfReference (smallWidthBoundaryReference ring hn hsmall) hn
    (widthBoundaryWidthSmall hn hsmall).1

/-! ### The SMALL slice coefficient of the boundary charge -/

/-- The boundary charge per site at slice `q`: `widthBoundaryCharge n = n * this`.
Consumer: `widthBoundarySlice`, `widthBoundaryChargeEq`. -/
def widthBoundarySliceNumerator (q : Nat) : Nat :=
  2 * (2 * (q + bankRepairDigitLeadingLength (compileAdvice q).t + 2)) +
    (2 * (2 * bankRepairDigitBoundaryServices (compileAdvice q).t) +
      2 * (bankRepairDigitForwardCount (bankRepairDigitRadius (compileAdvice q).t) +
        bankRepairDigitReturnCount (bankRepairDigitRadius (compileAdvice q).t) +
        bankRepairDigitSettledCount (bankRepairDigitRadius (compileAdvice q).t) +
        bankRepairDigitRadius (compileAdvice q).t))

/-- The least ring size of slice `q`: `2^(q-1) + 1`.  Consumer:
`widthBoundarySlice`. -/
def widthBoundarySliceWidth (q : Nat) : Nat := 2 ^ (q - 1) + 1

/-- The `n²` coefficient of the boundary charge at slice `q`: the numerator divided by the
least ring size of the slice, rounded up.  Consumer: `widthBoundaryChargeSlice` and the
SMALL boundary table `b` of `l3HeadlineOfCleanBranches`. -/
def widthBoundarySlice (q : Nat) : Nat :=
  (widthBoundarySliceNumerator q + widthBoundarySliceWidth q - 1) / widthBoundarySliceWidth q

/-- Consumer: `widthBoundaryChargeSlice`. -/
theorem widthBoundaryChargeEq (n : Nat) :
    widthBoundaryCharge n = n * widthBoundarySliceNumerator (ceilLogTwo n) := by
  have key : ∀ a j f : Nat,
      2 * (n * (2 * a)) + (2 * (n * (2 * j)) + 2 * (n * f)) =
        n * (2 * (2 * a) + (2 * (2 * j) + 2 * f)) := by
    intro a j f
    rw [Nat.mul_add, Nat.mul_add, Nat.mul_left_comm n 2 (2 * a),
      Nat.mul_left_comm n 2 (2 * j), Nat.mul_left_comm n 2 f]
  unfold widthBoundaryCharge widthBoundaryExtinctionCharge widthBoundaryFlushCharge
    widthBoundarySliceNumerator
  exact key _ _ _

/-- The boundary charge is at most `widthBoundarySlice q · n²`.
Consumer: `bandWidthBoundaryStageSmall`. -/
theorem widthBoundaryChargeSlice {n : Nat} (hn : 5 ≤ n) :
    widthBoundaryCharge n ≤ widthBoundarySlice (ceilLogTwo n) * n ^ 2 := by
  rw [widthBoundaryChargeEq]
  have hpop := (ringQ_facts n hn).2.1
  have hm : widthBoundarySliceWidth (ceilLogTwo n) ≤ n := by
    unfold widthBoundarySliceWidth
    omega
  have hpos : 0 < widthBoundarySliceWidth (ceilLogTwo n) := Nat.succ_pos _
  have hK : widthBoundarySliceNumerator (ceilLogTwo n) ≤
      widthBoundarySlice (ceilLogTwo n) * widthBoundarySliceWidth (ceilLogTwo n) := by
    unfold widthBoundarySlice
    generalize widthBoundarySliceNumerator (ceilLogTwo n) = K
    generalize widthBoundarySliceWidth (ceilLogTwo n) = m at hpos ⊢
    have h1 := Nat.div_add_mod (K + m - 1) m
    have h2 := Nat.mod_lt (K + m - 1) hpos
    generalize (K + m - 1) / m = d at h1 ⊢
    generalize (K + m - 1) % m = r at h1 h2
    rw [Nat.mul_comm]
    generalize m * d = md at h1 ⊢
    omega
  calc n * widthBoundarySliceNumerator (ceilLogTwo n)
      ≤ n * (widthBoundarySlice (ceilLogTwo n) * widthBoundarySliceWidth (ceilLogTwo n)) :=
        Nat.mul_le_mul_left n hK
    _ ≤ n * (widthBoundarySlice (ceilLogTwo n) * n) :=
        Nat.mul_le_mul_left n (Nat.mul_le_mul_left _ hm)
    _ = widthBoundarySlice (ceilLogTwo n) * n ^ 2 := by
        rw [Nat.pow_two, Nat.mul_comm n, Nat.mul_assoc]

/-- **The SMALL boundary premise at the band reference**, at any slice table `b` dominating
`widthBoundarySlice`.  Consumer: `l3HeadlineOfCleanBranches`. -/
theorem bandWidthBoundaryStageSmall {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (b : Nat → Nat)
    (hb : widthBoundarySlice (ceilLogTwo n) ≤ b (ceilLogTwo n))
    (hsmall : (compileAdvice (ceilLogTwo n)).useSmall = true) :
    WidthDigitBoundaryStage (bandWidthDigitReference ring hn)
      (widthDigitBandCharge n b (bankRepairDigitBoundaryMicroCharge n)) := by
  rw [bandWidthDigitReferenceSmall ring hn hsmall, widthDigitBandChargeSmall _ _ hsmall]
  exact bankRepairDigitChargedMono _ _ _
    (Nat.le_trans (widthBoundaryChargeSlice hn) (Nat.mul_le_mul_right _ hb))
    (smallWidthBoundaryStage ring hn hsmall)

end L3.WidthDigit

#print axioms L3.WidthDigit.widthDigitBoundaryStageOfReference
#print axioms L3.WidthDigit.widthBoundaryWidthSmall
#print axioms L3.WidthDigit.smallWidthBoundaryStage
#print axioms L3.WidthDigit.widthBoundaryChargeSlice
#print axioms L3.WidthDigit.bandWidthBoundaryStageSmall
