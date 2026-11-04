import Leader.L3.Bank.RepairDigitStructuralClean
import Leader.L3.Bank.RepairDigitEntryClose
import Leader.L3.Bank.RepairDigitFiveTransfer
import Leader.PPL.Probability.RestartCost

/-!
# R10c: the all-pairs strict clock from per-pair strict clocks

The structural clock `WidthDigitStructuralClock` (first strict completion of every complete pair
in both lanes, on the audit restarted at the clean start) is Lemma e-max of repair.tex
(`lem:e-max`, lines 1420-1465) over the per-pair Lemma e-packet (`lem:e-packet`, 1187-1417).

* The per-pair clock is stated once, for both bands, as `WidthStrictPairClock ref c`: from every
  first-zero continuation, the first strict completion of pair `i` on `lane` (on the audit
  restarted at the clean start) costs at most `c`, uniformly over the state. This is Lemma
  e-packet (`cohortStrictFromScratch`); it is NOT proved here.
* `simultaneousOfUniform` (generic): uniform per-goal cost envelopes `c` of `K` persistent goals
  on a closed class give all `K` goals at doubled cost `3 j (2 c) + 2` once `4 K ≤ 2^j`
  (Markov to a half block, `repeat_half_block_miss`, then the union bound of
  `entrySimultaneousCost`). This is Lemma e-max's `ln (40 m)` with the logarithm paid once.
* `widthStructuralClockOfPairs` (BANK): `WidthStrictPairClock` gives
  `WidthDigitStructuralClock` at `3 ((ceilLogTwo n + 3) (2 c)) + 2`, with the `2 n` (pair, lane)
  obligations, the first strict completions chosen by least terminal time, and the first
  structural cut by least cut (`existsFirst`).

Lane-level shape (research/lean-l3/wip/r10c-mc/scratch_rank.py): the shortest distance
to a strict completion is NOT a rank (no-edge-raises fails on 68 transitions at `R = 2` and
14938 at `R = 3`, with jumps up to 10 and 21 letters), so a monotone-rank proof of the per-pair
clock in the style of the first-zero rank does not exist; the paper's proof is phased with one
fair race (renewal trial), charge `n h(r)`, `h(r) = 12 r^4 + 40 r^3 + 18 r^2 + 36 r + 10`.
-/

namespace L3.DigitCohortScratch

open L3
open L3.HeadlineRenewal
open L3.RenewalReferenceClock
open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree
open LeaderCountDyadicTail
open L3.CohortTail
open L3.CohortSites
open L3.FiveTransfer
open L3.ValueWaveClose
open L3.WidthDigit
open L3.DigitPairsClean
open L3.DigitStructuralClean

set_option autoImplicit false

/-! ### Least witnesses -/

/-- A satisfiable predicate on `Nat` has a least witness. Consumer: the first strict
completion and the first structural cut of `widthStructuralClockOfPairs`. -/
theorem existsFirst (p : Nat → Prop) (h : ∃ t, p t) :
    ∃ t, p t ∧ ∀ s, s < t → ¬ p s := by
  have key : ∀ N t, t ≤ N → p t → ∃ u, p u ∧ ∀ s, s < u → ¬ p s := by
    intro N
    induction N with
    | zero =>
      intro t ht hp
      exact ⟨t, hp, fun s hs => absurd hs (by omega)⟩
    | succ N ih =>
      intro t ht hp
      rcases Classical.em (∃ s, s < t ∧ p s) with ⟨s, hs, hps⟩ | hno
      · exact ih s (by omega) hps
      · exact ⟨t, hp, fun s hs hps => hno ⟨s, hs, hps⟩⟩
  obtain ⟨t, ht⟩ := h
  exact key t t (Nat.le_refl t) ht

/-- A recorded completion gives a first strict completion. Consumer:
`widthStructuralClockOfPairs`. -/
theorem firstStrictOfCompletion {c : Compiled} {n : Nat} (ring : DirectedRing n)
    (A : DigitAudit c n) (root : Fin n) (source target : Nat) (lane : DigitLane) (cut : Nat)
    (h : ∃ tm, DigitCompletion ring A root source target lane cut tm) :
    ∃ tm, DigitFirstStrictCompletion ring A root source target lane cut tm := by
  obtain ⟨t0, ⟨tm, htm, rfl⟩, hmin⟩ := existsFirst
    (fun t => ∃ tm, DigitCompletion ring A root source target lane cut tm ∧ tm.time = t)
    (by obtain ⟨tm, htm⟩ := h; exact ⟨tm.time, tm, htm, rfl⟩)
  refine ⟨tm, htm, fun other ho => ?_⟩
  rcases Nat.lt_or_ge other.time tm.time with hlt | hge
  · exact absurd ⟨other, ho, rfl⟩ (hmin other.time hlt)
  · exact hge

/-! ### Lemma e-max on a closed class -/

/-- The doubled block ceiling is at most `3 M + 2`. Consumer: `simultaneousOfUniform`. -/
theorem ceilingDoubleLe (M : Nat) : 2 * L3.Prob.renewalCeiling M 1 4 ≤ 3 * M + 2 := by
  unfold L3.Prob.renewalCeiling L3.Prob.ceilNat
  have : (4 : Nat) - 1 = 3 := rfl
  rw [this]
  split <;> omega

/-- **Lemma e-max from uniform per-goal clocks**: on a closed class, `K` persistent goals,
each with a uniform first-hit cost envelope `c` off its goal, are all met at doubled cost
`3 j (2 c) + 2` once `4 K ≤ 2^j`. No independence: Markov gives a half block of `2 c` letters
for each goal, `j` restarted blocks give the miss `2^{-j} ≤ 1 / (4K)`, and the union bound
inside one block of `entrySimultaneousCost` pays all goals. Consumer:
`widthStructuralClockOfPairs`. -/
theorem simultaneousOfUniform {S : Type} {n K : Nat} (next : S → Fin n → S) (P : S → Prop)
    (Good : Fin K → S → Prop) (c j : Nat) (hc : 0 < c) (hj : 0 < j) (hK : 0 < K)
    (hKj : 4 * K ≤ 2 ^ j)
    (hcl : ∀ x e, P x → P (next x e))
    (hg : ∀ i x e, Good i x → Good i (next x e))
    (hcost : ∀ i x, P x → ¬ Good i x → ∀ T,
      costNumerator next (Good i) x T ≤ n ^ T * c) :
    ∀ x, P x → ∀ T,
      2 * costNumerator next (fun y => ∀ i, Good i y) x T ≤ n ^ T * (3 * (j * (2 * c)) + 2) := by
  have hb : ∀ i x, P x →
      4 * K * wordSum next (miss (Good i)) x (j * (2 * c)) ≤ n ^ (j * (2 * c)) := by
    intro i x hx
    have hhalf := PPL.Probability.markov_to_half_block next (Good i) P (hg i) c hc (hcost i)
    have hrep := PPL.Probability.repeat_half_block_miss next (Good i) P (hg i) hcl (2 * c)
      (fun y hy _ => hhalf y hy) x hx j
    exact Nat.le_trans (Nat.mul_le_mul_right _ hKj) hrep
  intro x hx T
  have h := L3.DigitEntryClose.entrySimultaneousCost next P Good (j * (2 * c))
    (Nat.mul_pos hj (by omega)) hK hcl hg hb x hx T
  calc 2 * costNumerator next (fun y => ∀ i, Good i y) x T
      ≤ 2 * (n ^ T * L3.Prob.renewalCeiling (j * (2 * c)) 1 4) := Nat.mul_le_mul_left 2 h
    _ = n ^ T * (2 * L3.Prob.renewalCeiling (j * (2 * c)) 1 4) := Nat.mul_left_comm _ _ _
    _ ≤ n ^ T * (3 * (j * (2 * c)) + 2) := Nat.mul_le_mul_left _ (ceilingDoubleLe _)

/-! ### The per-pair obligation, generic -/

section Generic

variable {n : Nat} {ring : DirectedRing n} (ref : WidthDigitReference ring)

/-- Pair `i` (from the first delimiter of the audit start) has a strict completion on `lane`
in the audit restarted at the clean start, if it is a complete interior pair. Consumer:
`WidthStrictPairClock`, `widthStructuralClockOfPairs`. -/
def WidthPairDone (root : Fin n) (i : Nat) (lane : DigitLane)
    (x : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n) : Prop :=
  ∀ first, DigitFirstDelimiter ring root x.2.start first →
    first + i * valueSpan n + 2 * valueSpan n < n →
    ∃ tm, DigitCompletion ring x.2 root (first + i * valueSpan n)
      (first + i * valueSpan n + valueSpan n) lane 0 tm

/-- The obligation persists. Consumer: `widthStructuralClockOfPairs`. -/
theorem widthPairDoneStep (root : Fin n) (i : Nat) (lane : DigitLane)
    (x : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n) (e : Fin n)
    (h : WidthPairDone ref root i lane x) :
    WidthPairDone ref root i lane (widthDigitAuditNext ref x e) := by
  intro first hf hend
  obtain ⟨tm, htm⟩ := h first hf hend
  exact ⟨tm, completionStep ring _ x.2 e root _ _ lane 0 tm htm⟩

/-- **Lemma e-packet, stated for both bands** (`cohortStrictFromScratch`): from every
first-zero continuation of the audit restarted at the clean start, the first strict completion
of pair `i` on `lane` costs at most `c`, uniformly over the state. Consumer:
`widthStructuralClockOfPairs` (BANK). -/
def WidthStrictPairClock (c : Nat) : Prop :=
  ∀ (root : Fin n) (i : Nat) (lane : DigitLane)
    (x : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n),
    WidthZeroRun ref root x → ¬ WidthPairDone ref root i lane x → ∀ T,
      costNumerator (widthDigitAuditNext ref) (WidthPairDone ref root i lane) x T ≤ n ^ T * c

end Generic

/-! ### Audit monotonicity of the two covers -/

/-- The two base covers survive an extension of the audit (same start, more frames, later
clock) at the same cut. Consumer: `widthStructuralClockOfPairs`. -/
theorem coversExtend {c : Compiled} {n : Nat} (ring : DirectedRing n) (root : Fin n)
    (A A' : DigitAudit c n) (hstart : A'.start = A.start)
    (hsub : ∀ f, f ∈ A.frames → f ∈ A'.frames) (hclk : A.clock ≤ A'.clock)
    (boundary retired cut : Nat) (h : DigitTwoBaseCovers ring root A boundary retired cut) :
    DigitTwoBaseCovers ring root A' boundary retired cut := by
  rcases h with ⟨hext, hret, hclock, hrest⟩
  refine ⟨bankRepairDigitZeroExtinctMono ring root A A' hstart hsub boundary retired hext, hret,
    Nat.le_trans hclock hclk, ?_⟩
  rcases hrest with hempty |
    ⟨b1, b2, l1, l2, c1, c2, hb1, hb2, hl1, hl2, hll1, hll2, hprop⟩
  · left
    rw [hstart]
    exact hempty
  · right
    refine ⟨b1, b2, l1, l2, c1, c2, hb1, hb2,
      bankRepairDigitZeroLineageMono ring root A A' hsub hl1,
      bankRepairDigitZeroLineageMono ring root A A' hsub hl2, hll1, hll2, fun site hw => ?_⟩
    rw [hstart] at hw
    obtain ⟨p1, p2, hp1, hp2, ht⟩ := hprop site hw
    exact ⟨p1, p2,
      bankRepairDigitZeroCoverMono ring root A A' hsub boundary retired cut cut (Nat.le_refl _)
        c1 c1 (fun _ h => h) site p1 hp1,
      bankRepairDigitZeroCoverMono ring root A A' hsub boundary retired cut cut (Nat.le_refl _)
        c2 c2 (fun _ h => h) site p2 hp2, ht⟩

/-! ### BANK: the structural clock from the per-pair clocks -/

/-- The lane of an obligation index. Consumer: `widthStructuralClockOfPairs`. -/
def laneOf (d : Nat) : DigitLane := if d % 2 = 0 then .writer else .comparison

/-- The code of a lane. Consumer: `widthStructuralClockOfPairs`. -/
def laneCode : DigitLane → Nat
  | .writer => 0
  | .comparison => 1

/-- Decoding the obligation index `2 i + code`. Consumer: `widthStructuralClockOfPairs`. -/
theorem laneDecode (i : Nat) (lane : DigitLane) :
    (2 * i + laneCode lane) / 2 = i ∧ laneOf (2 * i + laneCode lane) = lane := by
  cases lane
  · refine ⟨show (2 * i + 0) / 2 = i by omega, ?_⟩
    show (if (2 * i + 0) % 2 = 0 then DigitLane.writer else DigitLane.comparison) =
      DigitLane.writer
    rw [if_pos (by omega)]
  · refine ⟨show (2 * i + 1) / 2 = i by omega, ?_⟩
    show (if (2 * i + 1) % 2 = 0 then DigitLane.writer else DigitLane.comparison) =
      DigitLane.comparison
    rw [if_neg (by omega)]

section Bank

variable {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
  (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)

/-- The coupled continuations of one first-zero state that are first-zero continuations.
Consumer: `widthStructuralClockOfPairs`. -/
def scratchClass (root : Fin n)
    (x0 x : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n) : Prop :=
  WidthZeroRun (bankWidthDigitReference ring hn hbank) root x ∧
    ∃ w : List (Fin n), x = w.foldl (bankRepairDigitBoundaryAuditNext ring hbank) x0

/-- The obligation `d = 2 i + code`: pair `i` on the lane of `d`. Consumer:
`widthStructuralClockOfPairs`. -/
def scratchGood (root : Fin n) (d : Fin (2 * n))
    (x : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n) : Prop :=
  WidthPairDone (bankWidthDigitReference ring hn hbank) root (d.val / 2) (laneOf d.val) x

include hn in
/-- `8 n ≤ 2^(ceilLogTwo n + 3)`. Consumer: `widthStructuralClockOfPairs`. -/
theorem pairCountLog : 4 * (2 * n) ≤ 2 ^ (ceilLogTwo n + 3) := by
  have h := (ceilLogTwo_spec n (by omega)).2
  rw [Nat.pow_add]
  have : (2 : Nat) ^ 3 = 8 := rfl
  rw [this]
  omega

/-- **The structural clock on BANK from Lemma e-packet**: if every interior pair has a
uniform strict clock `c` on both lanes from every first-zero continuation of the clean audit,
then the first hit of the clean structural cut from the clean first-zero cut costs at most
`3 ((ceilLogTwo n + 3) (2 c)) + 2`. The `2 n` (pair, lane) obligations are composed by
`simultaneousOfUniform`; at the all-done state the first strict completions (least terminal
time) and the first structural cut (least cut) are chosen. Consumer: the R10c premise
`WidthDigitStructuralClock` at BANK (`widthDigitValueWaveOfStructural`). -/
theorem widthStructuralClockOfPairs (c : Nat)
    (hc : 0 < c) (hpair : WidthStrictPairClock (bankWidthDigitReference ring hn hbank) c) :
    WidthDigitStructuralClock (bankWidthDigitReference ring hn hbank)
      (3 * ((ceilLogTwo n + 3) * (2 * c)) + 2) := by
  intro z hz T
  obtain ⟨start, word, root, audit, retired, ⟨hD, hC⟩, hfold, hW, hDA, hcov, hBd, -⟩ := hz
  have hfold' : word.foldl (bankRepairDigitBoundaryAuditNext ring hbank)
      (start, digitAuditInitial (piD start.val.1)) = (z, audit) := hfold
  have hP0 : scratchClass ring hn hbank root (z, audit) (z, audit) := ⟨⟨start, word, [], (z, audit), retired, ⟨hD, hC⟩, hfold, hW, hDA,
    hcov, hBd, rfl⟩, [], rfl⟩
  have hcl : ∀ x e, scratchClass ring hn hbank root (z, audit) x →
      scratchClass ring hn hbank root (z, audit) (bankRepairDigitBoundaryAuditNext ring hbank x e) := by
    rintro x e ⟨hx, w, rfl⟩
    exact ⟨widthZeroRunStep (bankWidthDigitReference ring hn hbank) root _ hx e, w ++ [e],
      by rw [List.foldl_append]; rfl⟩
  have hsim := simultaneousOfUniform (bankRepairDigitBoundaryAuditNext ring hbank)
    (scratchClass ring hn hbank root (z, audit)) (scratchGood ring hn hbank root) c
    (ceilLogTwo n + 3) hc (by omega) (by omega) (pairCountLog hn) hcl
    (fun d x e h => widthPairDoneStep (bankWidthDigitReference ring hn hbank) root _ _ x e h)
    (fun d x hx hng T => hpair root _ _ x hx.1 hng T) (z, audit) hP0 T
  -- the singleton root and the delimiter layout of the start
  obtain ⟨root0, hs, hV⟩ := bankCleanBoundaryRoot ring hbank start hD hC
  have hsz := bankRepairDigitSingletonWordFold ring hn hbank root0 word start hs
  have hz1 : z = word.foldl (bankRepairNext ring hbank) start := by
    have := bankRepairDigitBoundaryAuditFirst ring hbank start
      (digitAuditInitial (piD start.val.1)) word
    rw [hfold'] at this
    exact this
  have hW' : WFixedRoot ring root (piW (word.foldl (bankRepairNext ring hbank) start).val.1) := by
    rw [← hz1]; exact hW
  have hr : root = root0 := hsz.2.2.1 root hW'.1
  subst hr
  obtain ⟨first0, ht, -, hb⟩ := bankCleanBoundaryDelimiters ring hbank hn root start hV
  have ht2 : 2 ≤ (compileAdvice (ceilLogTwo n)).t :=
    compileAdvice_t_ge_two (ceilLogTwo n) (ringQ_facts n hn).1
  have hR := valueSpanTwo hn
  -- the all-done coupled states are structural cuts
  have hB : ∀ x, (scratchClass ring hn hbank root (z, audit) x ∧
      ∀ d, scratchGood ring hn hbank root d x) →
      WidthDigitStructuralCut (bankWidthDigitReference ring hn hbank) x.1 := by
    rintro x ⟨⟨-, w, hw⟩, hgood⟩
    have hxfold : (word ++ w).foldl (bankRepairDigitBoundaryAuditNext ring hbank)
        (start, digitAuditInitial (piD start.val.1)) = x := by
      rw [List.foldl_append, hfold']
      exact hw.symm
    have hx1 : x.1 = (word ++ w).foldl (bankRepairNext ring hbank) start := by
      rw [← hxfold]
      exact bankRepairDigitBoundaryAuditFirst ring hbank start _ (word ++ w)
    have hinv := bankRepairDigitBoundaryAuditInvariantRun ring hn hbank root start hs (word ++ w)
    rw [hxfold] at hinv
    have hstartx : x.2.start = piD start.val.1 := by
      rw [← hxfold]
      exact bankAuditStart ring hbank (word ++ w) _
    have hsubf : ∀ f, f ∈ audit.frames → f ∈ x.2.frames := by
      intro f hf
      rw [hw]
      exact bankRepairDigitZeroFramesWord ring hbank w (z, audit) f hf
    have hclk : audit.clock ≤ x.2.clock := by
      rw [hw, bankRepairDigitZeroClockWord ring hbank w]
      exact Nat.le_add_right _ _
    have haudst : audit.start = piD start.val.1 := by
      have := bankAuditStart ring hbank word (start, digitAuditInitial (piD start.val.1))
      rw [hfold'] at this
      exact this
    -- the structural predicate at the current clock
    have hSA : DigitStructuralAt ring root x.2 x.2.clock := by
      refine ⟨Nat.le_refl _, fun source target lane hpair => ?_⟩
      rw [hstartx] at hpair
      obtain ⟨⟨⟨hs0, hsn, hsb⟩, -, -, -, -⟩, -⟩ := hpair.1
      obtain ⟨hfs, hmod⟩ := (hb source hs0 hsn).1 hsb
      have htg := hpair.2.1
      have hend2 := hpair.2.2.2
      generalize hRv : valueSpan n = R at hR
      have hRd : digitSpan (compileAdvice (ceilLogTwo n)) = R := hRv
      rw [hRd] at hmod htg hend2
      have hsrc : source = first0 + (source - first0) / R * R := by
        have := Nat.div_add_mod (source - first0) R
        rw [hmod, Nat.add_zero, Nat.mul_comm] at this
        omega
      generalize (source - first0) / R = i at hsrc
      have hiR : i ≤ i * R := Nat.le_mul_of_pos_right i (by omega)
      have hin : i < n := by omega
      obtain ⟨hdiv, hlane⟩ := laneDecode i lane
      have hidx : 2 * i + laneCode lane < 2 * n := by
        cases lane
        · show 2 * i + 0 < 2 * n
          omega
        · show 2 * i + 1 < 2 * n
          omega
      have hg' : WidthPairDone (bankWidthDigitReference ring hn hbank) root i lane x := by
        have h1 : WidthPairDone (bankWidthDigitReference ring hn hbank) root
            ((2 * i + laneCode lane) / 2) (laneOf (2 * i + laneCode lane)) x :=
          hgood ⟨2 * i + laneCode lane, hidx⟩
        rw [hdiv, hlane] at h1
        exact h1
      have hfd : DigitFirstDelimiter ring root x.2.start first0 := by
        rw [hstartx]
        exact firstDelimOf ring root (piD start.val.1) first0 hb (by omega)
          (by omega)
      have hc := hg' first0 hfd (by rw [hRv]; omega)
      rw [hRv, ← hsrc] at hc
      rw [htg]
      obtain ⟨tm, htm⟩ := firstStrictOfCompletion ring x.2 root source (source + R) lane 0 hc
      exact ⟨tm, htm, htm.1.2.2.2.2.2.1⟩
    obtain ⟨structural, hst, hmin⟩ := existsFirst (DigitStructuralAt ring root x.2) ⟨_, hSA⟩
    refine ⟨start, word ++ w, root, x.2, retired, audit.clock, structural, ⟨hD, hC⟩, hxfold, ?_,
      hinv.2.1, ?_, digitBoundaryAtMono ring root audit x.2 (by rw [hstartx, haudst]) hsubf retired hBd,
      ⟨hst, hmin⟩⟩
    · show WFixedRoot ring root (piW x.1.val.1)
      rw [hx1]
      exact bankRepairDigitBoundaryWFixedRootOfSingleton ring hn hbank root start hs (word ++ w)
    · exact coversExtend ring root audit x.2 (by rw [hstartx, haudst]) hsubf hclk 0 retired
        audit.clock hcov
  have hstop := costNumeratorTargetOnClosed (bankRepairDigitBoundaryAuditNext ring hbank)
    (scratchClass ring hn hbank root (z, audit))
    (fun x => scratchClass ring hn hbank root (z, audit) x ∧ ∀ d, scratchGood ring hn hbank root d x)
    (fun y => ∀ d, scratchGood ring hn hbank root d y) (fun x hx e => hcl x e hx)
    (fun x hx hq => ⟨hx, hq⟩) T (z, audit) hP0
  have hproj := L3.Projection.costProjectLe (bankRepairNext ring hbank)
    (bankRepairDigitBoundaryAuditNext ring hbank) Prod.fst (fun _ _ => rfl)
    (WidthDigitStructuralCut (bankWidthDigitReference ring hn hbank))
    (fun x => scratchClass ring hn hbank root (z, audit) x ∧ ∀ d, scratchGood ring hn hbank root d x)
    hB (z, audit) T
  exact Nat.le_trans (Nat.mul_le_mul_left 2 (Nat.le_trans hproj hstop)) hsim

end Bank

end L3.DigitCohortScratch

#print axioms L3.DigitCohortScratch.existsFirst
#print axioms L3.DigitCohortScratch.firstStrictOfCompletion
#print axioms L3.DigitCohortScratch.ceilingDoubleLe
#print axioms L3.DigitCohortScratch.simultaneousOfUniform
#print axioms L3.DigitCohortScratch.widthPairDoneStep
#print axioms L3.DigitCohortScratch.coversExtend
#print axioms L3.DigitCohortScratch.laneDecode
#print axioms L3.DigitCohortScratch.pairCountLog
#print axioms L3.DigitCohortScratch.widthStructuralClockOfPairs
