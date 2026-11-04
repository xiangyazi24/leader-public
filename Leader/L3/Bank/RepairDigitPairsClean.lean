import Leader.L3.Bank.RepairDigitFirstZeroClean
import Leader.L3.Bank.RepairDigitEntryBridge
import Leader.L3.Width.DigitCuts

/-!
# R10c: the interior pairs at the clean first-zero cut

`WidthFirstZeroPairs` asks, at every first-zero state of the audit restarted at the clean start,
the lift data `WidthPairPin` of every interior writer pair: the complete pair on the audit start
(`PairIn`), a cycle ghost with the window invariant `WinInvD` (whose fourth clause is
`CohortCycIn` of the pair's current lane) and `UseReach`.

This module proves, at the BANK instance:

* `pairInOfDelims`, `cleanPairIn`: `PairIn` of every interior pair, for every first delimiter of
  the audit start, on every run from a clean start;
* the quiet first-zero run (`zeroAimInBlock`, `quietStep`, `quietCovers`, `cleanFirstZeroQuiet`):
  from every clean gone cut the first-zero cut is reached by a word whose letters are sites of the
  first block `[0, first + R)` only;
* on that run nothing happens at a pair beyond the first block: `cleanFirstZeroNoCompletion`
  (no `DigitCompletion` of the pair in the restarted audit unless its source site was scheduled
  before the gone cut) and `laneFrozen` (its lane does not move);
* `firstZeroPairsForcesCyc`: hence `WidthFirstZeroPairs` at BANK implies that at every clean gone
  cut every interior writer pair beyond the first block already has its lane in a cycle class
  `CohortCycIn`; the premise is a statement about the lanes at the gone cut, not a consequence
  of the first-zero passes;
* `cleanStructuralCyc`: at a clean structural cut (`DigitStructuralAt` on the restarted audit)
  every interior pair of both lanes is in `CohortCyc` (group 6 bridge `firstStrictCyc` at the
  clean start), and `winInvDAtCycStart`: `WinInvD` holds at every cycle start (`lam = 0`) of a
  layout state with frame order and the distinct correspondence.
-/

namespace L3.DigitPairsClean

open L3
open L3.HeadlineRenewal
open L3.RenewalReferenceClock
open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree
open L3.WidthDigit
open L3.CohortSites
open L3.CohortDomination
open L3.Rearm
open L3.CohortWindow
open L3.CohortClose
open L3.CohortIdentity
open L3.GhostBridge
open L3.Correspondence
open L3.ValueWaveClose
open L3.PairBlock
open L3.BlockEntry
open L3.DigitEntryPhase
open L3.DigitEntryBridge

set_option autoImplicit false

/-! ### Frames are written only at scheduled edges -/

section Frames

variable {n : Nat} {ring : DirectedRing n} (ref : WidthDigitReference ring)

/-- Every frame of the final audit is an old frame or sits at a letter of the word. Consumer:
`widthNoCompletionOfQuiet`. -/
theorem widthFramesScheduled : ∀ (word : List (Fin n))
    (q : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (f : DigitFrame (compileAdvice (ceilLogTwo n)) n),
    f ∈ (word.foldl (widthDigitAuditNext ref) q).2.frames → f ∈ q.2.frames ∨ f.edge ∈ word := by
  intro word
  induction word with
  | nil => intro q f hf; exact Or.inl hf
  | cons a rest ih =>
    intro q f hf
    rcases ih (widthDigitAuditNext ref q a) f hf with h | h
    · rcases List.mem_cons.mp h with h' | h'
      · right
        rw [h']
        exact List.mem_cons.mpr (Or.inl rfl)
      · exact Or.inl h'
    · exact Or.inr (List.mem_cons.mpr (Or.inr h))

/-- The audit start never changes along a run. Consumer: `cleanPairIn`,
`firstZeroPairsForcesCyc`, `cleanStructuralCyc`. -/
theorem widthAuditStart : ∀ (word : List (Fin n))
    (q : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n),
    (word.foldl (widthDigitAuditNext ref) q).2.start = q.2.start := by
  intro word
  induction word with
  | nil => intro q; rfl
  | cons a rest ih => intro q; exact ih _

end Frames

/-- The audit start never changes along a BANK coupled run. Consumer: `cleanPairIn`,
`firstZeroPairsForcesCyc`, `cleanStructuralCyc`. -/
theorem bankAuditStart {n : Nat} (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) : ∀ (word : List (Fin n))
    (q : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n),
    (word.foldl (bankRepairDigitBoundaryAuditNext ring hbank) q).2.start = q.2.start := by
  intro word
  induction word with
  | nil => intro q; rfl
  | cons a rest ih => intro q; exact ih _

/-- A completion has a recorded sample at the source site. Consumer:
`widthNoCompletionOfQuiet`. -/
theorem completionSampleFrame {c : Compiled} {n : Nat} (ring : DirectedRing n) (A : DigitAudit c n)
    (root : Fin n) (source target : Nat) (lane : DigitLane) (cut : Nat)
    (tm : DigitTerminal c n) (h : DigitCompletion ring A root source target lane cut tm) :
    ∃ f, f ∈ A.frames ∧ f.edge = digitSite ring root source := by
  obtain ⟨_, _, _, _, _, _, hpos, _, samples, _, _, hrest⟩ := h
  obtain ⟨_, _, _, hall, _⟩ := hrest
  obtain ⟨⟨f, hf, -, hfe, -⟩, -, hsite, -⟩ := hall ⟨0, hpos⟩
  refine ⟨f, hf, ?_⟩
  rw [hfe, hsite]
  rfl

section Quiet

variable {n : Nat} {ring : DirectedRing n} (ref : WidthDigitReference ring)

/-- No completion of a pair whose source site carries no old frame and is not a letter of the
word. Consumer: `cleanFirstZeroNoCompletion`. -/
theorem widthNoCompletionOfQuiet (word : List (Fin n))
    (q : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n) (root : Fin n)
    (source target : Nat) (lane : DigitLane) (cut : Nat)
    (tm : DigitTerminal (compileAdvice (ceilLogTwo n)) n)
    (h0 : ∀ f, f ∈ q.2.frames → f.edge ≠ digitSite ring root source)
    (hw : digitSite ring root source ∉ word) :
    ¬ DigitCompletion ring (word.foldl (widthDigitAuditNext ref) q).2 root source target lane cut
      tm := by
  intro hc
  obtain ⟨f, hf, he⟩ := completionSampleFrame ring _ root source target lane cut tm hc
  rcases widthFramesScheduled ref word q f hf with h | h
  · exact h0 f h he
  · exact hw (he ▸ h)

end Quiet

/-! ### Delimiter layout: complete pairs and cohort layouts -/

section Delims

variable {c : Compiled} {n : Nat} (ring : DirectedRing n) (root : Fin n) (S : Fin n → ProjD c)
  (first : Nat)

/-- A block of the periodic delimiter layout is complete. Consumer: `pairInOfDelims`. -/
theorem completeBlockOfDelims
    (hb : ∀ k, 0 < k → k < n →
      ((S (digitSite ring root k)).word.beta = true ↔ first ≤ k ∧ (k - first) % digitSpan c = 0))
    (m : Nat) (hm : m % digitSpan c = 0) (h0 : 0 < first + m)
    (hend : first + m + digitSpan c < n) (hR : 1 ≤ digitSpan c) :
    DigitCompleteBlock ring root S (first + m) := by
  refine ⟨⟨⟨h0, by omega, ?_⟩, by omega, by omega, fun _ => ?_, fun k hk1 hk2 => ?_⟩, hend⟩
  · exact (hb _ h0 (by omega)).2 ⟨by omega, by rw [show first + m - first = m by omega]; exact hm⟩
  · exact (hb _ (by omega) hend).2 ⟨by omega, by
      rw [show first + m + digitSpan c - first = m + digitSpan c by omega, Nat.add_mod_right]
      exact hm⟩
  · cases hbeta : (S (digitSite ring root k)).word.beta with
    | false => rfl
    | true =>
      exfalso
      have h := ((hb k (by omega) (by omega)).1 hbeta).2
      have hj : k - first - m < digitSpan c := by omega
      have key : (m + (k - first - m)) % digitSpan c = k - first - m := by
        rw [Nat.add_mod, hm, Nat.zero_add, Nat.mod_mod, Nat.mod_eq_of_lt hj]
      rw [show k - first = m + (k - first - m) by omega, key] at h
      omega

/-- **`PairIn` from the delimiter layout**: the pair `(first + m, first + m + R)` with
`R ∣ m` is complete. Consumer: `cleanPairIn`, `cleanStructuralCyc`. -/
theorem pairInOfDelims
    (hb : ∀ k, 0 < k → k < n →
      ((S (digitSite ring root k)).word.beta = true ↔ first ≤ k ∧ (k - first) % digitSpan c = 0))
    (m : Nat) (hm : m % digitSpan c = 0) (h0 : 0 < first + m)
    (hend : first + m + 2 * digitSpan c < n) (hR : 1 ≤ digitSpan c) :
    DigitCompletePair ring root S (first + m) (first + m + digitSpan c) := by
  refine ⟨completeBlockOfDelims ring root S first hb m hm h0 (by omega) hR, rfl, ?_⟩
  have h := completeBlockOfDelims ring root S first hb (m + digitSpan c)
    (by rw [Nat.add_mod_right]; exact hm) (by omega) (by omega) hR
  rwa [← Nat.add_assoc] at h

/-- The first delimiter of the periodic layout is `first`. Consumer: `cleanPairIn`,
`firstZeroPairsForcesCyc`, `cleanStructuralCyc`. -/
theorem firstDelimEq
    (hb : ∀ k, 0 < k → k < n →
      ((S (digitSite ring root k)).word.beta = true ↔ first ≤ k ∧ (k - first) % digitSpan c = 0))
    (h0 : 0 < first) (hn' : first < n) (f : Nat) (hf : DigitFirstDelimiter ring root S f) :
    f = first := by
  obtain ⟨⟨hf0, hfn, hfb⟩, hmin⟩ := hf
  have h1 := ((hb f hf0 hfn).1 hfb).1
  rcases Nat.lt_or_ge first f with h | h
  · have hfalse := hmin first h0 h
    have htrue := (hb first h0 hn').2 ⟨Nat.le_refl _, by rw [Nat.sub_self]; exact Nat.zero_mod _⟩
    rw [hfalse] at htrue
    cases htrue
  · omega

/-- `first` is the first delimiter of the periodic layout. Consumer:
`firstZeroPairsForcesCyc`. -/
theorem firstDelimOf
    (hb : ∀ k, 0 < k → k < n →
      ((S (digitSite ring root k)).word.beta = true ↔ first ≤ k ∧ (k - first) % digitSpan c = 0))
    (h0 : 0 < first) (hn' : first < n) : DigitFirstDelimiter ring root S first := by
  refine ⟨⟨h0, hn', (hb first h0 hn').2 ⟨Nat.le_refl _, by
    rw [Nat.sub_self]; exact Nat.zero_mod _⟩⟩, fun k hk0 hk => ?_⟩
  cases hbeta : (S (digitSite ring root k)).word.beta with
  | false => rfl
  | true =>
    have := ((hb k hk0 (by omega)).1 hbeta).1
    omega

end Delims

section BankDelims

variable {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
  (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)

/-- The cohort layout of a pair of the periodic layout at a layout-fixed state. Consumer:
`firstZeroPairsForcesCyc`, `cleanStructuralCyc`. -/
theorem cohortLayoutOfDelims (root : Fin n) (first : Nat) (z : BankReferenceState ring hbank)
    (hLF : BankRepairDigitLayoutFixed ring hbank root z)
    (hb : ∀ k, 0 < k → k < n →
      ((piD z.val.1 (digitSite ring root k)).word.beta = true ↔
        first ≤ k ∧ (k - first) % digitSpan (compileAdvice (ceilLogTwo n)) = 0))
    (m : Nat) (hm : m % digitSpan (compileAdvice (ceilLogTwo n)) = 0) (h2 : 2 ≤ first + m)
    (hend : first + m + 2 * digitSpan (compileAdvice (ceilLogTwo n)) < n) :
    CohortLayout ring hbank root (first + m) (digitSpan (compileAdvice (ceilLogTwo n))) z := by
  have hR := bankRepairDigitLeadSpanTwo hbank
  generalize digitSpan (compileAdvice (ceilLogTwo n)) = R at hb hm hend hR ⊢
  refine ⟨hLF, ?_, ?_, ?_, fun k hk0 hk2 hkR => ?_⟩
  · exact (hb _ (by omega) (by omega)).2
      ⟨by omega, by rw [show first + m - first = m by omega]; exact hm⟩
  · exact (hb _ (by omega) (by omega)).2
      ⟨by omega, by rw [show first + m + R - first = m + R by omega, Nat.add_mod_right]; exact hm⟩
  · exact (hb _ (by omega) (by omega)).2
      ⟨by omega, by
        rw [show first + m + 2 * R - first = m + R + R by omega, Nat.add_mod_right,
          Nat.add_mod_right]
        exact hm⟩
  · cases hbeta : (piD z.val.1 (digitSite ring root (first + m + k))).word.beta with
    | false => rfl
    | true =>
      exfalso
      have h := ((hb _ (by omega) (by omega)).1 hbeta).2
      rw [show first + m + k - first = m + k by omega, Nat.add_mod, hm, Nat.zero_add,
        Nat.mod_mod] at h
      by_cases hk : k < R
      · rw [Nat.mod_eq_of_lt hk] at h
        omega
      · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)] at h
        omega

include hn in
/-- The cohort layout is closed under words. Consumer: `firstZeroPairsForcesCyc`. -/
theorem cohortLayoutWord (root : Fin n) (lane : DigitLane) (src R : Nat) (hR : 2 ≤ R)
    (hsrc : 2 ≤ src) (hend : src + 2 * R < n) : ∀ (w : List (Fin n)) (z : BankReferenceState ring hbank),
    CohortLayout ring hbank root src R z →
    CohortLayout ring hbank root src R (w.foldl (bankRepairNext ring hbank) z) := by
  intro w
  induction w with
  | nil => intro z h; exact h
  | cons e rest ih =>
    intro z h
    exact ih _ (cohortBankStep ring hn hbank root lane src R hR hsrc hend z h e).1

include hn in
/-- **The lane of a pair does not move on letters before its source.** Consumer:
`firstZeroPairsForcesCyc`. -/
theorem laneFrozen (root : Fin n) (lane : DigitLane) (src R : Nat) (hR : 2 ≤ R)
    (hsrc : 2 ≤ src) (hend : src + 2 * R < n) : ∀ (w : List (Fin n)) (z : BankReferenceState ring hbank),
    CohortLayout ring hbank root src R z →
    (∀ e, e ∈ w → ∃ k, k < src ∧ e = digitSite ring root k) →
    cohortProj ring root lane src R (piD (w.foldl (bankRepairNext ring hbank) z).val.1) =
      cohortProj ring root lane src R (piD z.val.1) := by
  intro w
  induction w with
  | nil => intro z _ _; rfl
  | cons e rest ih =>
    intro z h hw
    obtain ⟨hz', hst⟩ := cohortBankStep ring hn hbank root lane src R hR hsrc hend z h e
    have hnone : cohortEdgeOf root src R e = none := by
      obtain ⟨k, hk, rfl⟩ := hw e (List.mem_cons.mpr (Or.inl rfl))
      unfold cohortEdgeOf
      rw [cohortIdxSite ring root k (by omega), if_neg (fun h => absurd h.1 (by omega))]
    have h2 := ih _ hz' (fun x hx => hw x (List.mem_cons.mpr (Or.inr hx)))
    rw [hnone] at hst
    exact h2.trans hst

include hn in
/-- **`PairIn` on every run from a clean start**: for the W fixed root of the final state, every
first delimiter of the audit start, and every interior pair of it. Consumer: the `PairIn` clause
of `WidthPairPin` at BANK (`WidthFirstZeroPairs`), `cleanStructuralCyc`. -/
theorem cleanPairIn
    (start : BankReferenceState ring hbank) (hD : BankPostInheritedGrantDrain ring hbank start)
    (hC : BankCleanRFold ring hbank start) (word : List (Fin n)) (root : Fin n)
    (hW : WFixedRoot ring root (piW (word.foldl (bankRepairDigitBoundaryAuditNext ring hbank)
      (start, digitAuditInitial (piD start.val.1))).1.val.1))
    (first : Nat) (hf : DigitFirstDelimiter ring root
      (word.foldl (bankRepairDigitBoundaryAuditNext ring hbank)
        (start, digitAuditInitial (piD start.val.1))).2.start first)
    (i : Nat) (h2 : 2 ≤ first + i * valueSpan n)
    (hend : first + i * valueSpan n + 2 * valueSpan n < n) :
    PairIn ring root (first + i * valueSpan n) (valueSpan n)
      (word.foldl (bankRepairDigitBoundaryAuditNext ring hbank)
        (start, digitAuditInitial (piD start.val.1))).2 := by
  obtain ⟨root0, hs, hV⟩ := bankCleanBoundaryRoot ring hbank start hD hC
  have hsz := bankRepairDigitSingletonWordFold ring hn hbank root0 word start hs
  rw [bankRepairDigitBoundaryAuditFirst] at hW
  have hr : root = root0 := hsz.2.2.1 root hW.1
  subst hr
  obtain ⟨first0, ht, -, hb⟩ := bankCleanBoundaryDelimiters ring hbank hn root start hV
  have hst := bankAuditStart ring hbank word (start, digitAuditInitial (piD start.val.1))
  unfold PairIn
  rw [hst] at hf ⊢
  have ht2 : 2 ≤ (compileAdvice (ceilLogTwo n)).t :=
    compileAdvice_t_ge_two (ceilLogTwo n) (ringQ_facts n hn).1
  have hfe := firstDelimEq ring root (piD start.val.1) first0 hb (by omega)
    (by have := hf.1.2.1; have := (hb _ hf.1.1 hf.1.2.1).1 hf.1.2.2; omega) first hf
  subst hfe
  have hR := bankRepairDigitLeadSpanTwo hbank
  have hm : (i * valueSpan n) % digitSpan (compileAdvice (ceilLogTwo n)) = 0 :=
    Nat.mul_mod_left i _
  exact pairInOfDelims ring root (piD start.val.1) first hb (i * valueSpan n) hm (by omega) hend
    (by omega)

end BankDelims

/-! ### The quiet first-zero run -/

section Rank

/-- The nominated edge of a valid phase record is a site of the first block. Consumer:
`quietStep`. -/
theorem zeroAimInBlock {c : Compiled} {n : Nat} {ring : DirectedRing n} {root : Fin n}
    {R first stop E r0 : Nat} {S : Fin n → ProjD c} {A : DigitAudit c n}
    (hF : BankRepairDigitZeroFrame ring root R first stop E r0 S A)
    (d : BankRepairDigitZeroPhase n) (hd : BankRepairDigitZeroValid ring root first E r0 A d) :
    ∃ k, k < E ∧ bankRepairDigitZeroAim ring root S d = digitSite ring root k := by
  have hE := hF.endTwo
  have hpend : ∃ k, k < E ∧ bankRepairDigitZeroPendAim ring root S = digitSite ring root k := by
    unfold bankRepairDigitZeroPendAim
    split
    · exact ⟨0, by omega, rfl⟩
    · exact ⟨1, by omega, rfl⟩
  cases d with
  | pendOne => exact hpend
  | runOne h b l ch =>
    exact ⟨h, (show BankRepairDigitZeroRun ring root first E r0 r0 A h b l ch from hd).headEnd, rfl⟩
  | pendTwo b l st ch => exact hpend
  | runTwo b l st ch h b' l' ch' =>
    exact ⟨h, (show BankRepairDigitZeroDone ring root first E r0 r0 A b l st ch ∧
      BankRepairDigitZeroRun ring root first E r0 st A h b' l' ch' from hd).2.headEnd, rfl⟩
  | done b l st ch b' l' st' ch' => exact ⟨0, by omega, rfl⟩

variable {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
  (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)

include hn in
/-- Off the target, a first-block letter lowers the first-zero rank. Consumer:
`quietCovers`. -/
theorem quietStep (root : Fin n) (first r0 : Nat)
    (q : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (hF : BankRepairDigitZeroFrame ring root (digitSpan (compileAdvice (ceilLogTwo n))) first
      (first + digitSpan (compileAdvice (ceilLogTwo n)))
      (first + digitSpan (compileAdvice (ceilLogTwo n))) r0 (piD q.1.val.1) q.2)
    (hLD : BankRepairDigitLeadData ring hbank root first q.1)
    (hnc : ¬ DigitTwoBaseCovers ring root q.2 0 r0 q.2.clock) :
    ∃ e k, k < first + digitSpan (compileAdvice (ceilLogTwo n)) ∧ e = digitSite ring root k ∧
      bankRepairDigitZeroPairRank ring hbank root first r0
          (bankRepairDigitBoundaryAuditNext ring hbank q e) + 1 ≤
        bankRepairDigitZeroPairRank ring hbank root first r0 q := by
  obtain ⟨d0, hd0, hc0⟩ := bankRepairDigitZeroRankAch ring root first
    (first + digitSpan (compileAdvice (ceilLogTwo n))) r0 (piD q.1.val.1) q.2
  have hpos : 0 < bankRepairDigitZeroCost ring root
      (first + digitSpan (compileAdvice (ceilLogTwo n))) (piD q.1.val.1) d0 := by
    rcases Nat.eq_zero_or_pos (bankRepairDigitZeroCost ring root
      (first + digitSpan (compileAdvice (ceilLogTwo n))) (piD q.1.val.1) d0) with h | h
    · exact absurd (bankRepairDigitZeroCostZero hF d0 hd0 h) hnc
    · exact h
  obtain ⟨k, hk, hak⟩ := zeroAimInBlock hF d0 hd0
  obtain ⟨d', hd', -, hdrop⟩ := bankRepairDigitZeroPhaseStep hF d0 hd0
    (bankRepairDigitZeroAim ring root (piD q.1.val.1) d0)
  refine ⟨bankRepairDigitZeroAim ring root (piD q.1.val.1) d0, k, hk, hak, ?_⟩
  rw [bankRepairDigitZeroPairRankStep ring hn hbank root first r0 q hLD]
  have h1 := bankRepairDigitZeroRankLe ring root first
    (first + digitSpan (compileAdvice (ceilLogTwo n))) r0
    (phiD ring (piD q.1.val.1) (bankRepairDigitZeroAim ring root (piD q.1.val.1) d0)) _ d' hd'
  have h2 := hdrop rfl hpos
  unfold bankRepairDigitZeroPairRank
  omega

include hn in
/-- **The quiet run reaches the two covers**: with the rank frame on every continuation, from
every continuation of rank at most `m` a word of first-block letters reaches the covers.
Consumer: `cleanFirstZeroQuiet`. -/
theorem quietCovers (root : Fin n) (first r0 : Nat)
    (p : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (hreach : ∀ w : List (Fin n),
      BankRepairDigitZeroFrame ring root (digitSpan (compileAdvice (ceilLogTwo n))) first
        (first + digitSpan (compileAdvice (ceilLogTwo n)))
        (first + digitSpan (compileAdvice (ceilLogTwo n))) r0
        (piD (w.foldl (bankRepairDigitBoundaryAuditNext ring hbank) p).1.val.1)
        (w.foldl (bankRepairDigitBoundaryAuditNext ring hbank) p).2 ∧
      BankRepairDigitLeadData ring hbank root first
        (w.foldl (bankRepairDigitBoundaryAuditNext ring hbank) p).1) :
    ∀ (m : Nat) (w0 : List (Fin n)),
      bankRepairDigitZeroPairRank ring hbank root first r0
        (w0.foldl (bankRepairDigitBoundaryAuditNext ring hbank) p) ≤ m →
      ∃ w : List (Fin n),
        (∀ e, e ∈ w → ∃ k, k < first + digitSpan (compileAdvice (ceilLogTwo n)) ∧
          e = digitSite ring root k) ∧
        DigitTwoBaseCovers ring root
          ((w0 ++ w).foldl (bankRepairDigitBoundaryAuditNext ring hbank) p).2 0 r0
          ((w0 ++ w).foldl (bankRepairDigitBoundaryAuditNext ring hbank) p).2.clock := by
  intro m
  induction m with
  | zero =>
    intro w0 hm
    by_cases hc : DigitTwoBaseCovers ring root
        (w0.foldl (bankRepairDigitBoundaryAuditNext ring hbank) p).2 0 r0
        (w0.foldl (bankRepairDigitBoundaryAuditNext ring hbank) p).2.clock
    · exact ⟨[], fun e he => absurd he List.not_mem_nil, by rw [List.append_nil]; exact hc⟩
    · obtain ⟨e, k, -, -, hdr⟩ := quietStep ring hn hbank root first r0 _ (hreach w0).1
        (hreach w0).2 hc
      omega
  | succ m ih =>
    intro w0 hm
    by_cases hc : DigitTwoBaseCovers ring root
        (w0.foldl (bankRepairDigitBoundaryAuditNext ring hbank) p).2 0 r0
        (w0.foldl (bankRepairDigitBoundaryAuditNext ring hbank) p).2.clock
    · exact ⟨[], fun e he => absurd he List.not_mem_nil, by rw [List.append_nil]; exact hc⟩
    · obtain ⟨e, k, hk, hek, hdr⟩ := quietStep ring hn hbank root first r0 _ (hreach w0).1
        (hreach w0).2 hc
      have hfold : (w0 ++ [e]).foldl (bankRepairDigitBoundaryAuditNext ring hbank) p =
          bankRepairDigitBoundaryAuditNext ring hbank
            (w0.foldl (bankRepairDigitBoundaryAuditNext ring hbank) p) e := by
        rw [List.foldl_append]
        rfl
      obtain ⟨w, hw, hcov⟩ := ih (w0 ++ [e]) (by rw [hfold]; omega)
      refine ⟨e :: w, fun x hx => ?_, ?_⟩
      · rcases List.mem_cons.mp hx with h | h
        · exact ⟨k, hk, h.trans hek⟩
        · exact hw x h
      · have he : w0 ++ e :: w = (w0 ++ [e]) ++ w := by simp
        rw [he]
        exact hcov

include hn in
/-- **The quiet first-zero run from a clean gone cut**: from every clean start and every word
to its gone cut there is a continuation by first-block letters (`[0, first + R)`, `R` the span)
reaching the two base covers; its final state is a clean first-zero cut state. Consumer:
`cleanFirstZeroNoCompletion`, `firstZeroPairsForcesCyc`. -/
theorem cleanFirstZeroQuiet
    (start : BankReferenceState ring hbank) (hD : BankPostInheritedGrantDrain ring hbank start)
    (hC : BankCleanRFold ring hbank start) (word : List (Fin n))
    (hg : bankRepairDigitAllBaseLabelsGone ring hbank
      (word.foldl (bankRepairDigitBoundaryAuditNext ring hbank)
        (start, digitAuditInitial (piD start.val.1)))) :
    ∃ (root : Fin n) (first : Nat), BankRepairDigitLeadData ring hbank root first start ∧
      2 ≤ first ∧
      ∃ (w : List (Fin n)) (r0 : Nat),
        (∀ e, e ∈ w → ∃ k, k < first + digitSpan (compileAdvice (ceilLogTwo n)) ∧
          e = digitSite ring root k) ∧
        WFixedRoot ring root (piW ((word ++ w).foldl (bankRepairDigitBoundaryAuditNext ring hbank)
          (start, digitAuditInitial (piD start.val.1))).1.val.1) ∧
        DigitAt ring ((word ++ w).foldl (bankRepairDigitBoundaryAuditNext ring hbank)
            (start, digitAuditInitial (piD start.val.1))).2
          ((word ++ w).foldl (bankRepairDigitBoundaryAuditNext ring hbank)
            (start, digitAuditInitial (piD start.val.1))).2.clock
          (piD ((word ++ w).foldl (bankRepairDigitBoundaryAuditNext ring hbank)
            (start, digitAuditInitial (piD start.val.1))).1.val.1)
          ((word ++ w).foldl (bankRepairDigitBoundaryAuditNext ring hbank)
            (start, digitAuditInitial (piD start.val.1))).2.current ∧
        DigitTwoBaseCovers ring root
          ((word ++ w).foldl (bankRepairDigitBoundaryAuditNext ring hbank)
            (start, digitAuditInitial (piD start.val.1))).2 0 r0
          ((word ++ w).foldl (bankRepairDigitBoundaryAuditNext ring hbank)
            (start, digitAuditInitial (piD start.val.1))).2.clock := by
  obtain ⟨root, hss, hV⟩ := bankCleanBoundaryRoot ring hbank start hD hC
  obtain ⟨first, hd, hf2, hw, -⟩ := bankRepairDigitZeroDelims ring hn hbank root start hV
  have hblock := (bankRepairDigitZeroGeomOf ring hn hbank root first start hd hf2
    hw).toBankRepairDigitZeroBlock
  have hi0 := bankRepairDigitZeroInvWord ring hn hbank root first hf2 hw _ word _
    (bankRepairDigitZeroInvInitial ring hbank root first start hd)
  have hext0 := bankRepairDigitBoundaryBaseExtinctOfSingleton ring hn hbank root start hss word hg
  have hreach : ∀ w : List (Fin n),
      BankRepairDigitZeroFrame ring root (digitSpan (compileAdvice (ceilLogTwo n))) first
        (first + digitSpan (compileAdvice (ceilLogTwo n)))
        (first + digitSpan (compileAdvice (ceilLogTwo n)))
        (word.foldl (bankRepairDigitBoundaryAuditNext ring hbank)
          (start, digitAuditInitial (piD start.val.1))).2.clock
        (piD (w.foldl (bankRepairDigitBoundaryAuditNext ring hbank)
          (word.foldl (bankRepairDigitBoundaryAuditNext ring hbank)
            (start, digitAuditInitial (piD start.val.1)))).1.val.1)
        (w.foldl (bankRepairDigitBoundaryAuditNext ring hbank)
          (word.foldl (bankRepairDigitBoundaryAuditNext ring hbank)
            (start, digitAuditInitial (piD start.val.1)))).2 ∧
      BankRepairDigitLeadData ring hbank root first
        (w.foldl (bankRepairDigitBoundaryAuditNext ring hbank)
          (word.foldl (bankRepairDigitBoundaryAuditNext ring hbank)
            (start, digitAuditInitial (piD start.val.1)))).1 := fun w => by
    have hiq := bankRepairDigitZeroInvWord ring hn hbank root first hf2 hw _ w _ hi0
    refine ⟨bankRepairDigitZeroFrameOf ring hn hbank root first hf2 hw _ hblock _ hiq
      (bankRepairDigitZeroGoneWord hn ring hbank w _ hg) _
      (bankRepairDigitZeroExtinctMono ring root _ _ (by rw [hiq.2.2.2, hi0.2.2.2])
        (fun f hf => bankRepairDigitZeroFramesWord ring hbank w _ f hf) 0 _ hext0) ?_, hiq.2.1⟩
    rw [bankRepairDigitZeroClockWord ring hbank w]
    omega
  obtain ⟨w, hwb, hcov⟩ := quietCovers ring hn hbank root first _ _ hreach _ [] (Nat.le_refl _)
  rw [List.nil_append] at hcov
  have hiq := bankRepairDigitZeroInvWord ring hn hbank root first hf2 hw _ w _ hi0
  have hfa : (word ++ w).foldl (bankRepairDigitBoundaryAuditNext ring hbank)
      (start, digitAuditInitial (piD start.val.1)) =
      w.foldl (bankRepairDigitBoundaryAuditNext ring hbank)
        (word.foldl (bankRepairDigitBoundaryAuditNext ring hbank)
          (start, digitAuditInitial (piD start.val.1))) := by rw [List.foldl_append]
  refine ⟨root, first, hd, hf2, w, (word.foldl (bankRepairDigitBoundaryAuditNext ring hbank)
    (start, digitAuditInitial (piD start.val.1))).2.clock, hwb, ?_, ?_, ?_⟩
  · have hfix := bankRepairDigitBoundaryWFixedRootOfSingleton ring hn hbank root start hss
      (word ++ w)
    rw [bankRepairDigitBoundaryAuditFirst]
    exact hfix
  · rw [hfa]
    exact hiq.1.2.1
  · rw [hfa]
    exact hcov

include hn in
/-- **No completion beyond the first block at the quiet first-zero cut**: on the quiet run of
`cleanFirstZeroQuiet`, a pair of the delimiter layout beyond the first block (`i ≥ 1`) whose
source site is not a letter of the word to the gone cut has no `DigitCompletion` in the audit
restarted at the clean start. So the first-zero cut does not provide the completions of the
group 6 bridge; they belong to the structural cut (`DigitStructuralAt`). Consumer: the R10c
ledger (group 6 interface: completions come from the structural stage). -/
theorem cleanFirstZeroNoCompletion
    (start : BankReferenceState ring hbank) (hD : BankPostInheritedGrantDrain ring hbank start)
    (hC : BankCleanRFold ring hbank start) (word : List (Fin n))
    (hg : bankRepairDigitAllBaseLabelsGone ring hbank
      (word.foldl (bankRepairDigitBoundaryAuditNext ring hbank)
        (start, digitAuditInitial (piD start.val.1)))) :
    ∃ (root : Fin n) (first : Nat), BankRepairDigitLeadData ring hbank root first start ∧
      ∃ w : List (Fin n),
        BankCleanFirstZeroCut ring hbank ((word ++ w).foldl (bankRepairDigitBoundaryAuditNext ring hbank)
          (start, digitAuditInitial (piD start.val.1))).1 ∧
        ∀ i, 1 ≤ i → first + i * valueSpan n < n →
          digitSite ring root (first + i * valueSpan n) ∉ word →
          ∀ (target : Nat) (lane : DigitLane) (cut : Nat)
            (tm : DigitTerminal (compileAdvice (ceilLogTwo n)) n),
          ¬ DigitCompletion ring ((word ++ w).foldl (bankRepairDigitBoundaryAuditNext ring hbank)
            (start, digitAuditInitial (piD start.val.1))).2 root (first + i * valueSpan n) target
            lane cut tm := by
  obtain ⟨root, first, hd, hf2, w, r0, hwb, hW, hDA, hcov⟩ :=
    cleanFirstZeroQuiet ring hn hbank start hD hC word hg
  refine ⟨root, first, hd, w, ⟨start, word ++ w, root,
    ((word ++ w).foldl (bankRepairDigitBoundaryAuditNext ring hbank)
      (start, digitAuditInitial (piD start.val.1))).2, r0, hD, hC, rfl, hW, hDA, hcov⟩,
    fun i hi hin hnw target lane cut tm => ?_⟩
  have hle : valueSpan n ≤ i * valueSpan n := by
    have h := Nat.mul_le_mul_right (valueSpan n) hi
    rwa [Nat.one_mul] at h
  have hnm : digitSite ring root (first + i * valueSpan n) ∉ word ++ w := by
    intro hm
    rcases List.mem_append.mp hm with h1 | h1
    · exact hnw h1
    · obtain ⟨k, hk, hek⟩ := hwb _ h1
      have hkn : k < n := by unfold valueSpan at hle hin; omega
      have hkk := bankRepairDigitSiteInj ring root hkn hin hek.symm
      unfold valueSpan at hle hkk
      omega
  have h := widthNoCompletionOfQuiet (bankWidthDigitReference ring hn hbank) (word ++ w)
    (start, digitAuditInitial (piD start.val.1)) root (first + i * valueSpan n) target lane cut tm
    (fun f hf => absurd hf List.not_mem_nil) hnm
  rw [widthDigitAuditNextBank] at h
  exact h

/-- **`WidthFirstZeroPairs` at BANK is a statement about the lanes at the gone cut**: if it
holds, then at every clean gone cut every interior writer pair beyond the first block already
has its lane in a cycle class `CohortCycIn` (the lane is the one of the quiet first-zero cut,
`laneFrozen`). Consumer: the R10c truth check of `WidthFirstZeroPairs` (a lane of a clean gone
cut outside every cycle class refutes it). -/
theorem firstZeroPairsForcesCyc
    (hpairs : WidthFirstZeroPairs (bankWidthDigitReference ring hn hbank))
    (start : BankReferenceState ring hbank) (hD : BankPostInheritedGrantDrain ring hbank start)
    (hC : BankCleanRFold ring hbank start) (word : List (Fin n))
    (hg : bankRepairDigitAllBaseLabelsGone ring hbank
      (word.foldl (bankRepairDigitBoundaryAuditNext ring hbank)
        (start, digitAuditInitial (piD start.val.1)))) :
    ∃ (root : Fin n) (first : Nat), BankRepairDigitLeadData ring hbank root first start ∧
      ∀ i, 1 ≤ i → first + i * valueSpan n + 2 * valueSpan n < n →
        ∃ (g : (Nat → Nat) × Nat) (o : Nat), CohortCycIn (valueSpan n) g.2
          (cohortProj ring root DigitLane.writer (first + i * valueSpan n) (valueSpan n)
            (piD (word.foldl (bankRepairNext ring hbank) start).val.1)) g o := by
  obtain ⟨root, first, hd, hf2, w, r0, hwb, hW, hDA, hcov⟩ :=
    cleanFirstZeroQuiet ring hn hbank start hD hC word hg
  refine ⟨root, first, hd, fun i hi hend => ?_⟩
  have hP := hpairs start (word ++ w) root
    ((word ++ w).foldl (bankRepairDigitBoundaryAuditNext ring hbank)
      (start, digitAuditInitial (piD start.val.1))).1
    ((word ++ w).foldl (bankRepairDigitBoundaryAuditNext ring hbank)
      (start, digitAuditInitial (piD start.val.1))).2 r0 ⟨hD, hC⟩ rfl hW hDA hcov
  have hst := bankAuditStart ring hbank (word ++ w) (start, digitAuditInitial (piD start.val.1))
  have hfd : DigitFirstDelimiter ring root
      ((word ++ w).foldl (bankRepairDigitBoundaryAuditNext ring hbank)
        (start, digitAuditInitial (piD start.val.1))).2.start first := by
    rw [hst]
    exact firstDelimOf ring root (piD start.val.1) first hd.2.2.2 hd.2.1 hd.2.2.1
  have hle : valueSpan n ≤ i * valueSpan n := by
    have h := Nat.mul_le_mul_right (valueSpan n) hi
    rwa [Nat.one_mul] at h
  obtain ⟨-, g, hwin, -⟩ := hP first hfd i (Nat.zero_le _) (by omega) hend
  obtain ⟨o, hcyc⟩ := hwin.2.2.2.1
  refine ⟨g, o, ?_⟩
  have hR := valueSpanTwo hn
  have hlay0 := cohortLayoutOfDelims ring hbank root first start hd.1 hd.2.2.2 (i * valueSpan n)
    (Nat.mul_mod_left i _) (by omega) hend
  have hlay := cohortLayoutWord ring hn hbank root DigitLane.writer (first + i * valueSpan n)
    (valueSpan n) hR (by omega) hend word start hlay0
  have hfz := laneFrozen ring hn hbank root DigitLane.writer (first + i * valueSpan n)
    (valueSpan n) hR (by omega) hend w _ hlay (fun e he => by
      obtain ⟨k, hk, hek⟩ := hwb e he
      exact ⟨k, by unfold valueSpan at hle ⊢; omega, hek⟩)
  have hZ : ((word ++ w).foldl (bankRepairDigitBoundaryAuditNext ring hbank)
      (start, digitAuditInitial (piD start.val.1))).1 =
      w.foldl (bankRepairNext ring hbank) (word.foldl (bankRepairNext ring hbank) start) := by
    rw [bankRepairDigitBoundaryAuditFirst, List.foldl_append]
  have hc : CohortCycIn (valueSpan n) g.2
      (cohortProj ring root DigitLane.writer (first + i * valueSpan n) (valueSpan n)
        (piD ((word ++ w).foldl (bankRepairDigitBoundaryAuditNext ring hbank)
          (start, digitAuditInitial (piD start.val.1))).1.val.1)) g o := hcyc
  rw [hZ, hfz] at hc
  exact hc

end Rank

/-! ### The structural cut and the window entry -/

section Structural

variable {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
  (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)

include hn in
/-- **At a clean structural cut every interior pair is in the cycle class**: on the audit
restarted at a clean start, if every complete pair has a first strict completion in both lanes
(`DigitStructuralAt`), then for every first delimiter of the audit start every interior pair is
complete and its lane (either lane) is in `CohortCyc` (group 6 bridge `firstStrictCyc` at the
clean start, whose cohort layout comes from the delimiter layout). Consumer: the clean entry
stage (structural cut to the pinned window `WinInvD ∧ UseReach`, `winInvDAtCycStart`). -/
theorem cleanStructuralCyc
    (start : BankReferenceState ring hbank) (hD : BankPostInheritedGrantDrain ring hbank start)
    (hC : BankCleanRFold ring hbank start) (word : List (Fin n)) (root : Fin n)
    (hW : WFixedRoot ring root (piW (word.foldl (bankRepairDigitBoundaryAuditNext ring hbank)
      (start, digitAuditInitial (piD start.val.1))).1.val.1))
    (structural : Nat)
    (hS : DigitStructuralAt ring root (word.foldl (bankRepairDigitBoundaryAuditNext ring hbank)
      (start, digitAuditInitial (piD start.val.1))).2 structural)
    (first : Nat) (hf : DigitFirstDelimiter ring root
      (word.foldl (bankRepairDigitBoundaryAuditNext ring hbank)
        (start, digitAuditInitial (piD start.val.1))).2.start first)
    (i : Nat) (lane : DigitLane) (h2 : 2 ≤ first + i * valueSpan n)
    (hend : first + i * valueSpan n + 2 * valueSpan n < n) :
    PairIn ring root (first + i * valueSpan n) (valueSpan n)
        (word.foldl (bankRepairDigitBoundaryAuditNext ring hbank)
          (start, digitAuditInitial (piD start.val.1))).2 ∧
      CohortCyc (valueSpan n) (cohortProj ring root lane (first + i * valueSpan n) (valueSpan n)
        (piD (word.foldl (bankRepairDigitBoundaryAuditNext ring hbank)
          (start, digitAuditInitial (piD start.val.1))).1.val.1)) := by
  have hpair := cleanPairIn ring hn hbank start hD hC word root hW first hf i h2 hend
  refine ⟨hpair, ?_⟩
  obtain ⟨tm, htm, -⟩ := hS.2 _ _ lane hpair
  obtain ⟨root0, hs, hV⟩ := bankCleanBoundaryRoot ring hbank start hD hC
  have hsz := bankRepairDigitSingletonWordFold ring hn hbank root0 word start hs
  have hW' := hW
  rw [bankRepairDigitBoundaryAuditFirst] at hW'
  have hr : root = root0 := hsz.2.2.1 root hW'.1
  subst hr
  obtain ⟨first0, ht, -, hb⟩ := bankCleanBoundaryDelimiters ring hbank hn root start hV
  have hst := bankAuditStart ring hbank word (start, digitAuditInitial (piD start.val.1))
  rw [hst] at hf
  have ht2 : 2 ≤ (compileAdvice (ceilLogTwo n)).t :=
    compileAdvice_t_ge_two (ceilLogTwo n) (ringQ_facts n hn).1
  have hfe := firstDelimEq ring root (piD start.val.1) first0 hb (by omega)
    (by have := hf.1.2.1; have := (hb _ hf.1.1 hf.1.2.1).1 hf.1.2.2; omega) first hf
  subst hfe
  have hR := valueSpanTwo hn
  have hlay := cohortLayoutOfDelims ring hbank root first start hV.1 hb (i * valueSpan n)
    (Nat.mul_mod_left i _) h2 hend
  exact firstStrictCyc ring hn hbank root lane (first + i * valueSpan n) (valueSpan n) hR h2 hend
    start hlay word rfl 0 tm htm

/-- **The window invariant at a cycle start**: at a layout state with frame order and the
distinct correspondence, a lane in the cycle class with the chosen ghost `lam = 0` (nothing
crossed) carries `WinInvD` with the ghost `(0, j)` (empty window from the current clock). This
is `winInvDEntry` without the packed settlement: the pinned window is entered at the first cycle
start after the structural cut. Consumer: the clean entry stage (`WidthPairPin`'s `WinInvD`
clause). -/
theorem winInvDAtCycStart (root : Fin n) (lane : DigitLane) (src R : Nat)
    (Base : Bool → DigitAtom n → Prop)
    (z : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (hz : CohortLayout ring hbank root src R z.1) (hfo : AuditFrameOrder z.2)
    (hgd : GhostCorrDistinct ring root lane src R Base (piD z.1.val.1) z.2) (j o : Nat)
    (hc : CohortCycIn R j (cohortProj ring root lane src R (piD z.1.val.1)) ((fun _ => 0), j) o)
    (chi : Nat → DigitExport (compileAdvice (ceilLogTwo n)) n) :
    WinInvD ring hbank root lane src R Base z ((fun _ => 0), j) :=
  ⟨hz, hfo, hgd, ⟨o, hc⟩, chi, _, cycWinStart ring root lane src R z.2 hfo chi,
    chiAtomsStart ring root lane src R Base _ chi⟩

end Structural

end L3.DigitPairsClean

#print axioms L3.DigitPairsClean.widthFramesScheduled
#print axioms L3.DigitPairsClean.widthAuditStart
#print axioms L3.DigitPairsClean.bankAuditStart
#print axioms L3.DigitPairsClean.completionSampleFrame
#print axioms L3.DigitPairsClean.widthNoCompletionOfQuiet
#print axioms L3.DigitPairsClean.pairInOfDelims
#print axioms L3.DigitPairsClean.firstDelimEq
#print axioms L3.DigitPairsClean.firstDelimOf
#print axioms L3.DigitPairsClean.cohortLayoutOfDelims
#print axioms L3.DigitPairsClean.laneFrozen
#print axioms L3.DigitPairsClean.cleanPairIn
#print axioms L3.DigitPairsClean.zeroAimInBlock
#print axioms L3.DigitPairsClean.quietStep
#print axioms L3.DigitPairsClean.quietCovers
#print axioms L3.DigitPairsClean.cleanFirstZeroQuiet
#print axioms L3.DigitPairsClean.cleanFirstZeroNoCompletion
#print axioms L3.DigitPairsClean.firstZeroPairsForcesCyc
#print axioms L3.DigitPairsClean.cleanStructuralCyc
#print axioms L3.DigitPairsClean.winInvDAtCycStart
