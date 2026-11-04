import Leader.L3.Small.DigitTables
import Leader.L3.Width.DigitCloseKeep

/-!
# The R10c first-zero clock on an abstract reference

`bankCleanFirstZeroGoneStage` (BankRepairDigitFirstZeroClean, on BANK) proved once over a
`WidthBoundaryReference`: from every state reachable from the gone cut, the audit of the clean
start is continued, the first-zero rank `bankRepairDigitZeroRank` (BankRepairDigitFirstZeroRank,
band-free: it reads only the projected D ring and the audit) is evaluated on the coupled pair,
never increases, drops on a nominated edge off the target, and starts below `2 E + 2`.

The BANK proof fixed the first block as `[first, first + R]` (`R = 2^t - 1`), which needs a
second delimiter (`first + R + 1 ≤ n`, BANK band width).  Here the block stops at
`widthFirstZeroStop n first = min (first + R) n` (the next delimiter, or the root) and the rank
end is `widthFirstZeroEnd n first = min (first + R) (n - 1)`; the rank geometry
(`BankRepairDigitZeroBlock`) already allows a block ending at the root.  So the clock holds on
every ring with the leading width `t + R ≤ n`, in particular on every SMALL ring.

The charge is `widthFirstZeroCharge n = 2 n · 2 (t + 2R)` (since `E < t + 2R`).

* `widthDigitFirstZeroClockOfReference`: `WidthDigitFirstZeroClock` at `widthFirstZeroCharge n`;
* BANK: `widthDigitFirstZeroClockBankOfReference`, at `bankRepairDigitFirstZeroMicroCharge n`;
* SMALL: `smallWidthFirstZeroClock`, and `bandWidthFirstZeroClockSmall` at the SMALL slice table
  `smallDigitZeroTable q · n²` (`widthFirstZeroChargeSlice`).
-/

namespace L3.WidthDigit

open L3
open L3.HeadlineRenewal
open L3.RenewalReferenceClock
open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree

set_option autoImplicit false

/-- The stop of the first block: the next delimiter `first + R`, or the root.  Consumer:
`WidthFirstZeroInv`, `widthFirstZeroGeomOf`. -/
def widthFirstZeroStop (n first : Nat) : Nat :=
  min (first + digitSpan (compileAdvice (ceilLogTwo n))) n

/-- The end of the first-zero rank: `min (first + R) (n - 1)`.  Consumer:
`widthFirstZeroPairRank`, `widthFirstZeroFrameOf`. -/
def widthFirstZeroEnd (n first : Nat) : Nat :=
  min (first + digitSpan (compileAdvice (ceilLogTwo n))) (n - 1)

/-- The first-zero charge in `t`: `2 n · 2 (t + 2R)`, `R = 2^t - 1`.  Consumer:
`widthDigitFirstZeroClockOfReference`. -/
def widthFirstZeroCharge (n : Nat) : Nat :=
  2 * (n * (2 * ((compileAdvice (ceilLogTwo n)).t +
    2 * digitSpan (compileAdvice (ceilLogTwo n)))))

/-- BANK as a boundary reference.  Consumer: `widthDigitFirstZeroClockBankOfReference`. -/
def bankWidthBoundaryReference {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) :
    WidthBoundaryReference ring :=
  { bankWidthDigitReference ring hn hbank with
    singletonFixed := fun _ _ h => h.2
    startClean := fun _ h => h.2.1.2
    singletonOfStart := fun _ _ h hf => ⟨h.1, hf⟩ }

section Generic

variable {n : Nat} {ring : DirectedRing n}

/-- The rank geometry from the layout data, with the block stopping at the next delimiter or
the root.  Consumer: `widthFirstZeroInvStep`, `widthFirstZeroFrameOf`. -/
theorem widthFirstZeroGeomOf (ref : WidthBoundaryReference ring) (hn : 5 ≤ n) (root : Fin n)
    (first : Nat) (z : ref.State) (hd : WidthBoundaryDigitLeadData ref root first z)
    (hf2 : 2 ≤ first) :
    BankRepairDigitZeroGeom ring root (digitSpan (compileAdvice (ceilLogTwo n))) first
      (widthFirstZeroStop n first) (piD (ref.phys z)) := by
  have hR := widthBoundaryDigitSpanTwo hn
  have hedge := fun e => widthBoundaryDigitLeadBankEdge ref hn root z hd.1 e
  have hfn : first < n := hd.2.2.1
  exact
    { layout := hd.2.2.2
      firstTwo := hf2
      firstStop := by unfold widthFirstZeroStop; omega
      stopSize := by unfold widthFirstZeroStop; omega
      stopSpan := by unfold widthFirstZeroStop; omega
      stopEdge := fun h => by unfold widthFirstZeroStop at h ⊢; omega
      size := hn
      rootIff := (hedge root).2.1
      betaX := fun e => (hedge e).2.2.1
      betaY := fun e => (hedge e).2.2.2 }

/-- Audit invariant, layout data, launch layout and the audit start.  Consumer:
`widthFirstZeroInvWord`, `widthFirstZeroFrameOf`. -/
def WidthFirstZeroInv (ref : WidthBoundaryReference ring) (root : Fin n) (first : Nat)
    (st : Fin n → ProjD (compileAdvice (ceilLogTwo n)))
    (q : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n) : Prop :=
  WidthBoundaryDigitBoundaryAuditInvariant ref root q ∧
  WidthBoundaryDigitLeadData ref root first q.1 ∧
  BankRepairDigitZeroLaunchLayout ring root first (widthFirstZeroStop n first)
    (piD (ref.phys q.1)) q.2.current ∧
  q.2.start = st

/-- Consumer: `widthFirstZeroInvWord`. -/
theorem widthFirstZeroInvStep (ref : WidthBoundaryReference ring) (hn : 5 ≤ n) (root : Fin n)
    (first : Nat) (hf2 : 2 ≤ first) (st : Fin n → ProjD (compileAdvice (ceilLogTwo n)))
    (q : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (h : WidthFirstZeroInv ref root first st q) (e : Fin n) :
    WidthFirstZeroInv ref root first st (widthDigitAuditNext ref.toWidthDigitReference q e) := by
  obtain ⟨hA, hd, hL, hs⟩ := h
  have hedge := widthBoundaryDigitLeadBankEdge ref hn root q.1 hd.1 e
  refine ⟨widthBoundaryDigitBoundaryAuditInvariantStep ref hn root q hA e,
    widthBoundaryDigitLeadDataStep ref hn root first q.1 hd e, ?_, hs⟩
  show BankRepairDigitZeroLaunchLayout ring root first (widthFirstZeroStop n first)
    (piD (ref.phys (ref.next q.1 e)))
    (digitGhostStep ring (piD (ref.phys q.1)) q.2.current (q.2.clock + 1) e)
  rw [hedge.1]
  exact bankRepairDigitZeroLaunchStep ring root _ first _ (piD (ref.phys q.1)) q.2.current
    (q.2.clock + 1) e (widthFirstZeroGeomOf ref hn root first q.1 hd hf2) hA.2.2 hL

/-- Consumer: `widthDigitFirstZeroClockOfReference`. -/
theorem widthFirstZeroInvWord (ref : WidthBoundaryReference ring) (hn : 5 ≤ n) (root : Fin n)
    (first : Nat) (hf2 : 2 ≤ first) (st : Fin n → ProjD (compileAdvice (ceilLogTwo n)))
    (word : List (Fin n)) :
    ∀ q : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n,
      WidthFirstZeroInv ref root first st q →
      WidthFirstZeroInv ref root first st
        (word.foldl (widthDigitAuditNext ref.toWidthDigitReference) q) := by
  induction word with
  | nil => intro q h; exact h
  | cons e rest ih =>
      intro q h
      exact ih _ (widthFirstZeroInvStep ref hn root first hf2 st q h e)

/-- Consumer: `widthDigitFirstZeroClockOfReference`. -/
theorem widthFirstZeroInvInitial (ref : WidthBoundaryReference ring) (root : Fin n)
    (first : Nat) (start : ref.State) (hd : WidthBoundaryDigitLeadData ref root first start) :
    WidthFirstZeroInv ref root first (piD (ref.phys start))
      (start, digitAuditInitial (piD (ref.phys start))) := by
  refine ⟨widthBoundaryDigitBoundaryAuditInvariantInitial ref root start hd.1.1, hd, ?_, rfl⟩
  intro k _ born hb
  exfalso
  change (if (piD (ref.phys start) (digitSite ring root k)).top.wBase == WBase.NONE then none
    else some (DigitBaseOrigin.inherited (digitSite ring root k))) = _ at hb
  split at hb <;> simp at hb

/-- Consumer: `widthDigitFirstZeroClockOfReference`. -/
theorem widthFirstZeroClockWord (ref : WidthBoundaryReference ring) (word : List (Fin n)) :
    ∀ q : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n,
      (word.foldl (widthDigitAuditNext ref.toWidthDigitReference) q).2.clock =
        q.2.clock + word.length := by
  induction word with
  | nil => intro q; rfl
  | cons e rest ih =>
      intro q
      rw [List.foldl_cons, ih, List.length_cons]
      show q.2.clock + 1 + rest.length = q.2.clock + (rest.length + 1)
      omega

/-- Consumer: `widthDigitFirstZeroClockOfReference`. -/
theorem widthFirstZeroFramesWord (ref : WidthBoundaryReference ring) (word : List (Fin n)) :
    ∀ (q : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n) f,
      f ∈ q.2.frames →
      f ∈ (word.foldl (widthDigitAuditNext ref.toWidthDigitReference) q).2.frames := by
  induction word with
  | nil => intro q f hf; exact hf
  | cons e rest ih =>
      intro q f hf
      exact ih _ f (bankRepairDigitZeroStepSub ring (piD (ref.phys q.1)) q.2 e f hf)

/-- The rank frame at a coupled state.  Consumer: `widthDigitFirstZeroClockOfReference`. -/
theorem widthFirstZeroFrameOf (ref : WidthBoundaryReference ring) (hn : 5 ≤ n) (root : Fin n)
    (first : Nat) (hf2 : 2 ≤ first) (st : Fin n → ProjD (compileAdvice (ceilLogTwo n)))
    (hblock : BankRepairDigitZeroBlock ring root (digitSpan (compileAdvice (ceilLogTwo n))) first
      (widthFirstZeroStop n first) st)
    (q : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (hinv : WidthFirstZeroInv ref root first st q)
    (hgone : widthDigitAllBaseLabelsGone ref.toWidthDigitReference q) (r0 : Nat)
    (hext : DigitBaseExtinct ring root q.2 0 r0) (hr : r0 ≤ q.2.clock) :
    BankRepairDigitZeroFrame ring root (digitSpan (compileAdvice (ceilLogTwo n))) first
      (widthFirstZeroStop n first) (widthFirstZeroEnd n first) r0 (piD (ref.phys q.1)) q.2 := by
  obtain ⟨hA, hd, hL, hs⟩ := hinv
  have hR := widthBoundaryDigitSpanTwo hn
  have hfn : first < n := hd.2.2.1
  exact
    { geom := widthFirstZeroGeomOf ref hn root first q.1 hd hf2
      start := by rw [hs]; exact hblock
      endStop := by unfold widthFirstZeroEnd widthFirstZeroStop; omega
      endSize := by unfold widthFirstZeroEnd; omega
      endWrit := fun k hk hk1 => by unfold widthFirstZeroEnd; unfold widthFirstZeroStop at hk; omega
      endTwo := by unfold widthFirstZeroEnd; omega
      extinct := hext
      retired := hr
      toks := bankRepairDigitZeroToksOf ring root first _ (piD (ref.phys q.1)) q.2.current hA.2.2
        (fun i s h => hgone ⟨s, i, h⟩) hL }

/-- The first-zero rank of a coupled state.  Consumer: `widthFirstZeroPairCost`. -/
noncomputable def widthFirstZeroPairRank (ref : WidthBoundaryReference ring) (root : Fin n)
    (first r0 : Nat) (q : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n) : Nat :=
  bankRepairDigitZeroRank ring root first (widthFirstZeroEnd n first) r0 (piD (ref.phys q.1)) q.2

/-- Consumer: `widthFirstZeroPairCost`. -/
theorem widthFirstZeroPairRankStep (ref : WidthBoundaryReference ring) (hn : 5 ≤ n)
    (root : Fin n) (first r0 : Nat)
    (q : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (hd : WidthBoundaryDigitLeadData ref root first q.1) (e : Fin n) :
    widthFirstZeroPairRank ref root first r0 (widthDigitAuditNext ref.toWidthDigitReference q e) =
      bankRepairDigitZeroRank ring root first (widthFirstZeroEnd n first) r0
        (phiD ring (piD (ref.phys q.1)) e) (digitAuditStep ring (piD (ref.phys q.1)) q.2 e) := by
  unfold widthFirstZeroPairRank
  show bankRepairDigitZeroRank ring root first (widthFirstZeroEnd n first) r0
      (piD (ref.phys (ref.next q.1 e))) (digitAuditStep ring (piD (ref.phys q.1)) q.2 e) = _
  rw [(widthBoundaryDigitLeadBankEdge ref hn root q.1 hd.1 e).1]

open Classical in
/-- The nominated edge: a dropping edge when one exists.  Consumer: `widthFirstZeroPairCost`. -/
noncomputable def widthFirstZeroPairChosen (ref : WidthBoundaryReference ring) (root : Fin n)
    (first r0 : Nat) (e0 : Fin n)
    (q : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n) : Fin n :=
  if h : ∃ e : Fin n, widthFirstZeroPairRank ref root first r0
      (widthDigitAuditNext ref.toWidthDigitReference q e) + 1 ≤
      widthFirstZeroPairRank ref root first r0 q then Classical.choose h else e0

/-- Consumer: `widthFirstZeroPairCost`. -/
theorem widthFirstZeroPairChosenSpec (ref : WidthBoundaryReference ring) (root : Fin n)
    (first r0 : Nat) (e0 : Fin n)
    (q : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (h : ∃ e : Fin n, widthFirstZeroPairRank ref root first r0
      (widthDigitAuditNext ref.toWidthDigitReference q e) + 1 ≤
      widthFirstZeroPairRank ref root first r0 q) :
    widthFirstZeroPairRank ref root first r0
        (widthDigitAuditNext ref.toWidthDigitReference q
          (widthFirstZeroPairChosen ref root first r0 e0 q)) + 1 ≤
      widthFirstZeroPairRank ref root first r0 q := by
  unfold widthFirstZeroPairChosen
  rw [dif_pos h]
  exact Classical.choose_spec h

/-- The cost bound on the coupled chain from a frame on every reachable coupled state.
Consumer: `widthDigitFirstZeroClockOfReference`. -/
theorem widthFirstZeroPairCost (ref : WidthBoundaryReference ring) (hn : 5 ≤ n) (root : Fin n)
    (first r0 : Nat) (p : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (hreach : ∀ w : List (Fin n),
      BankRepairDigitZeroFrame ring root (digitSpan (compileAdvice (ceilLogTwo n))) first
        (widthFirstZeroStop n first) (widthFirstZeroEnd n first) r0
        (piD (ref.phys (w.foldl (widthDigitAuditNext ref.toWidthDigitReference) p).1))
        (w.foldl (widthDigitAuditNext ref.toWidthDigitReference) p).2 ∧
      WidthBoundaryDigitLeadData ref root first
        (w.foldl (widthDigitAuditNext ref.toWidthDigitReference) p).1)
    (T : Nat) :
    costNumerator (widthDigitAuditNext ref.toWidthDigitReference)
      (fun q => DigitTwoBaseCovers ring root q.2 0 r0 q.2.clock) p T ≤
      n ^ T * (n * (2 * widthFirstZeroEnd n first + 2)) := by
  classical
  have hsplit : ∀ q : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n,
      ¬ (DigitTwoBaseCovers ring root q.2 0 r0 q.2.clock ∨
        ¬ ∃ w : List (Fin n), q = w.foldl (widthDigitAuditNext ref.toWidthDigitReference) p) →
      (∃ w : List (Fin n), q = w.foldl (widthDigitAuditNext ref.toWidthDigitReference) p) ∧
        ¬ DigitTwoBaseCovers ring root q.2 0 r0 q.2.clock := fun q h =>
    ⟨Classical.byContradiction (fun hb => h (Or.inr hb)), fun ha => h (Or.inl ha)⟩
  have hcost := L3.Prob.costNumerator_le_of_nominated_edge
    (widthDigitAuditNext ref.toWidthDigitReference)
    (fun q => DigitTwoBaseCovers ring root q.2 0 r0 q.2.clock ∨
      ¬ ∃ w : List (Fin n), q = w.foldl (widthDigitAuditNext ref.toWidthDigitReference) p)
    (widthFirstZeroPairRank ref root first r0)
    (widthFirstZeroPairChosen ref root first r0 ⟨0, by omega⟩)
    (fun q hq => by
      obtain ⟨⟨w, rfl⟩, ht⟩ := hsplit q hq
      apply widthFirstZeroPairChosenSpec
      obtain ⟨e, he⟩ := bankRepairDigitZeroRankDrop (hreach w).1 ht
      refine ⟨e, ?_⟩
      rw [widthFirstZeroPairRankStep ref hn root first r0 _ (hreach w).2 e]
      exact he)
    (fun q hq e => by
      obtain ⟨⟨w, rfl⟩, _⟩ := hsplit q hq
      rw [widthFirstZeroPairRankStep ref hn root first r0 _ (hreach w).2 e]
      exact bankRepairDigitZeroRankStep (hreach w).1 e) p T
  have htr := bankRepairDigitCostTransfer (widthDigitAuditNext ref.toWidthDigitReference)
    (widthDigitAuditNext ref.toWidthDigitReference)
    (fun q => DigitTwoBaseCovers ring root q.2 0 r0 q.2.clock)
    (fun q => DigitTwoBaseCovers ring root q.2 0 r0 q.2.clock ∨
      ¬ ∃ w : List (Fin n), q = w.foldl (widthDigitAuditNext ref.toWidthDigitReference) p) T p p
    (fun w hw => hw.resolve_right (fun hn' => hn' ⟨w, rfl⟩))
  have hup := bankRepairDigitZeroRankUpper ring root first (widthFirstZeroEnd n first) r0
    (piD (ref.phys p.1)) p.2
  exact Nat.le_trans htr (Nat.le_trans hcost
    (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hup)))

/-- Two passes over the first block fit the first-zero charge in `t`.  Consumer:
`widthDigitFirstZeroClockOfReference`. -/
theorem widthFirstZeroBudget (first : Nat)
    (hft : first < (compileAdvice (ceilLogTwo n)).t + digitSpan (compileAdvice (ceilLogTwo n)))
    (T : Nat) :
    2 * (n ^ T * (n * (2 * widthFirstZeroEnd n first + 2))) ≤ n ^ T * widthFirstZeroCharge n := by
  have hE : 2 * widthFirstZeroEnd n first + 2 ≤
      2 * ((compileAdvice (ceilLogTwo n)).t + 2 * digitSpan (compileAdvice (ceilLogTwo n))) := by
    unfold widthFirstZeroEnd
    omega
  unfold widthFirstZeroCharge
  calc 2 * (n ^ T * (n * (2 * widthFirstZeroEnd n first + 2)))
      ≤ 2 * (n ^ T * (n * (2 * ((compileAdvice (ceilLogTwo n)).t +
          2 * digitSpan (compileAdvice (ceilLogTwo n)))))) :=
        Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hE))
    _ = n ^ T * (2 * (n * (2 * ((compileAdvice (ceilLogTwo n)).t +
          2 * digitSpan (compileAdvice (ceilLogTwo n)))))) := Nat.mul_left_comm _ _ _

/-- **The R10c first-zero clock on a boundary reference**: from the boundary cut reachable
from the gone cut, the first hit of the first-zero cut costs at most `widthFirstZeroCharge n`,
given the leading width `t + R ≤ n`.  Consumer:
`widthDigitFirstZeroClockBankOfReference`, `smallWidthFirstZeroClock`. -/
theorem widthDigitFirstZeroClockOfReference (ref : WidthBoundaryReference ring) (hn : 5 ≤ n)
    (hlead : (compileAdvice (ceilLogTwo n)).t + digitSpan (compileAdvice (ceilLogTwo n)) ≤ n) :
    WidthDigitFirstZeroClock ref.toWidthDigitReference (widthFirstZeroCharge n) := by
  rintro z ⟨hr, hz⟩ T
  obtain ⟨_, w', ⟨start, word, hst, hg0, rfl⟩, rfl⟩ := hz
  -- the retirement is the clock of the boundary-retired state: move the gone cut there
  have hg := widthBoundaryDigitAllGoneWord hn ref w' _ hg0
  rw [← List.foldl_append] at hg hr
  rw [← List.foldl_append]
  generalize word ++ w' = word at hg hr ⊢
  have hL0 : WidthDigitLeaderReceipt ref.toWidthDigitReference (word.foldl ref.next start) := by
    obtain ⟨_, _, r', _, _, _, hW', _, hB', _⟩ := hr
    exact ⟨r', hW', hB'⟩
  obtain ⟨root, hss, hV⟩ := widthCleanBoundaryRoot ref start hst
  obtain ⟨first, ht, hft, hb⟩ := widthCleanBoundaryDelimiters ref hn root start hV
  have ht2 := compileAdvice_t_ge_two (ceilLogTwo n) (ringQ_facts n hn).1
  have hd : WidthBoundaryDigitLeadData ref root first start := ⟨hV.1, by omega, by omega, hb⟩
  have hf2 : 2 ≤ first := by omega
  have hblock := (widthFirstZeroGeomOf ref hn root first start hd hf2).toBankRepairDigitZeroBlock
  have hi0 := widthFirstZeroInvWord ref hn root first hf2 _ word _
    (widthFirstZeroInvInitial ref root first start hd)
  have hext0 := widthBoundaryDigitBoundaryBaseExtinctOfSingleton ref hn root start hss word hg
  -- the boundary receipt at the retirement
  have hxfst : (word.foldl (widthDigitAuditNext ref.toWidthDigitReference)
      (start, digitAuditInitial (piD (ref.phys start)))).1 = word.foldl ref.next start :=
    widthBoundaryDigitBoundaryAuditFirst ref start _ word
  have hBd0 : DigitBoundaryAt ring root
      (word.foldl (widthDigitAuditNext ref.toWidthDigitReference)
        (start, digitAuditInitial (piD (ref.phys start)))).2
      (word.foldl (widthDigitAuditNext ref.toWidthDigitReference)
        (start, digitAuditInitial (piD (ref.phys start)))).2.clock := by
    obtain ⟨r', hW', hB'⟩ := hL0
    have hfixq := widthBoundaryDigitBoundaryWFixedRootOfSingleton ref root start hss word
    have hrr : r' = root := hfixq.2.1 r' hW'.1
    subst hrr
    refine ⟨_, _, hi0.1.2.1, ?_⟩
    rw [hxfst]
    exact hB'
  have hpc := widthFirstZeroPairCost ref hn root first
    (word.foldl (widthDigitAuditNext ref.toWidthDigitReference)
      (start, digitAuditInitial (piD (ref.phys start)))).2.clock
    (word.foldl (widthDigitAuditNext ref.toWidthDigitReference)
      (start, digitAuditInitial (piD (ref.phys start))))
    (fun w => by
      have hiq := widthFirstZeroInvWord ref hn root first hf2 _ w _ hi0
      refine ⟨widthFirstZeroFrameOf ref hn root first hf2 _ hblock _ hiq
        (widthBoundaryDigitAllGoneWord hn ref w _ hg) _
        (bankRepairDigitZeroExtinctMono ring root _ _ (by rw [hiq.2.2.2, hi0.2.2.2])
          (fun f hf => widthFirstZeroFramesWord ref w _ f hf) 0 _ hext0) ?_, hiq.2.1⟩
      rw [widthFirstZeroClockWord ref w]
      omega) T
  have htr := bankRepairDigitCostTransfer ref.next
    (widthDigitAuditNext ref.toWidthDigitReference)
    (WidthDigitFirstZeroCut ref.toWidthDigitReference)
    (fun q => DigitTwoBaseCovers ring root q.2 0
      (word.foldl (widthDigitAuditNext ref.toWidthDigitReference)
        (start, digitAuditInitial (piD (ref.phys start)))).2.clock q.2.clock) T
    (word.foldl ref.next start)
    (word.foldl (widthDigitAuditNext ref.toWidthDigitReference)
      (start, digitAuditInitial (piD (ref.phys start))))
    (fun w hcov => by
      have hiq := widthFirstZeroInvWord ref hn root first hf2 _ w _ hi0
      refine ⟨start, word ++ w, root, _, _, hst, ?_, ?_, ?_, hcov, ?_, ?_⟩
      · rw [List.foldl_append]
        refine Prod.ext ?_ rfl
        rw [widthBoundaryDigitBoundaryAuditFirst, widthBoundaryDigitBoundaryAuditFirst]
      · have hfix := widthBoundaryDigitBoundaryWFixedRootOfSingleton ref root start hss
          (word ++ w)
        rw [List.foldl_append] at hfix
        exact hfix
      · have hat := hiq.1.2.1
        rw [widthBoundaryDigitBoundaryAuditFirst, widthBoundaryDigitBoundaryAuditFirst] at hat
        exact hat
      · exact digitBoundaryAtMono ring root _ _ (by rw [hiq.2.2.2, hi0.2.2.2])
          (fun f hf => widthFirstZeroFramesWord ref w _ f hf) _ hBd0
      · exact L3.CloseKeep.leaderWord ref hn start hst word hL0 w)
  exact Nat.le_trans (Nat.mul_le_mul_left 2 (Nat.le_trans htr hpc))
    (widthFirstZeroBudget first hft T)

end Generic

/-! ### BANK -/

/-- On BANK the first-zero charge in `t` is at most the first-zero micro-charge.  Consumer:
`widthDigitFirstZeroClockBankOfReference`. -/
theorem widthFirstZeroChargeBank {n : Nat}
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) :
    widthFirstZeroCharge n ≤ bankRepairDigitFirstZeroMicroCharge n := by
  have ht2 := compileAdvice_t_ge_two (ceilLogTwo n)
    (by have := bankRepairBankBand hbank; omega)
  have hp := bankRepairDigitPowLower (compileAdvice (ceilLogTwo n)).t
  have hR : 1 ≤ digitSpan (compileAdvice (ceilLogTwo n)) := by unfold digitSpan; omega
  have h := bankRepairDigitZeroBudget hbank
    ((compileAdvice (ceilLogTwo n)).t + digitSpan (compileAdvice (ceilLogTwo n)) - 1)
    (by omega) 0
  simp only [Nat.pow_zero, Nat.one_mul] at h
  have heq : 2 * ((compileAdvice (ceilLogTwo n)).t + digitSpan (compileAdvice (ceilLogTwo n)) -
      1 + digitSpan (compileAdvice (ceilLogTwo n))) + 2 =
      2 * ((compileAdvice (ceilLogTwo n)).t + 2 * digitSpan (compileAdvice (ceilLogTwo n))) := by
    omega
  rw [heq] at h
  unfold widthFirstZeroCharge
  exact h

/-- **The first-zero clock on BANK through the generic proof**, at the BANK first-zero
micro-charge: BANK is an instance of `widthDigitFirstZeroClockOfReference`.  Consumer:
`L3.WriterCore.bankWriterDigitHalfOfMoment`. -/
theorem widthDigitFirstZeroClockBankOfReference {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    :
    WidthDigitFirstZeroClock (bankWidthDigitReference ring hn hbank)
      (bankRepairDigitFirstZeroMicroCharge n) :=
  bankRepairDigitChargedMono _ _ _ (widthFirstZeroChargeBank hbank)
    (widthDigitFirstZeroClockOfReference (bankWidthBoundaryReference ring hn hbank) hn
      (bankRepairDigitLeadWidth hn hbank))

/-! ### SMALL -/

/-- **The first-zero clock on SMALL** (every SMALL ring) at `widthFirstZeroCharge n`.
Consumer: `bandWidthFirstZeroClockSmall`. -/
theorem smallWidthFirstZeroClock {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hsmall : (compileAdvice (ceilLogTwo n)).useSmall = true) :
    WidthDigitFirstZeroClock (smallWidthDigitReference ring hn hsmall)
      (widthFirstZeroCharge n) :=
  widthDigitFirstZeroClockOfReference (smallWidthBoundaryReference ring hn hsmall) hn
    (widthBoundaryWidthSmall hn hsmall).1

/-- The per-site first-zero numerator `4 (t + 2R)` is at most `z_q · N_q` on the finite
slices.  Consumer: `widthFirstZeroChargeSlice`. -/
theorem widthFirstZeroSliceFinite :
    ∀ i : Fin 33, 3 ≤ i.val →
      2 * (2 * ((compileAdvice i.val).t + 2 * digitSpan (compileAdvice i.val))) ≤
        smallDigitZeroFinite i.val * (2 ^ (i.val - 1) + 1) := by
  decide

/-- On SMALL the first-zero charge is at most the slice table `smallDigitZeroTable q · n²`.
Consumer: `bandWidthFirstZeroClockSmall`. -/
theorem widthFirstZeroChargeSlice {n : Nat} (hn : 5 ≤ n)
    (hsmall : (compileAdvice (ceilLogTwo n)).useSmall = true) :
    widthFirstZeroCharge n ≤ smallDigitZeroTable (ceilLogTwo n) * n ^ 2 := by
  obtain ⟨hlo, hhi⟩ := L3.SmallFinishClean.smallDigitSliceBounds hn hsmall
  have hpop := (ringQ_facts n hn).2.1
  -- the per-site numerator is at most `z_q · N_q ≤ z_q · n`
  have hsite : 2 * (2 * ((compileAdvice (ceilLogTwo n)).t +
      2 * digitSpan (compileAdvice (ceilLogTwo n)))) ≤ smallDigitZeroTable (ceilLogTwo n) * n := by
    refine Nat.le_trans ?_ (Nat.mul_le_mul_left _ (show 2 ^ (ceilLogTwo n - 1) + 1 ≤ n by omega))
    generalize ceilLogTwo n = q at hlo hhi ⊢
    unfold smallDigitZeroTable
    by_cases h32 : q ≤ 32
    · rw [if_pos h32]
      exact widthFirstZeroSliceFinite ⟨q, by omega⟩ hlo
    · rw [if_neg h32]
      have ht : (compileAdvice q).t = ceilLogTwo q := compileAdvice_t_large q (by omega)
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
      have hz1 : 1 ≤ smallDigitZeroFormula q := by
        unfold smallDigitZeroFormula
        rw [Nat.le_div_iff_mul_le (Nat.succ_pos _)]
        have hp1 : 1 ≤ 2 ^ (compileAdvice q).t - 1 := by
          rw [ht]
          have := Nat.pow_le_pow_right (show 0 < 2 by omega)
            (show 1 ≤ ceilLogTwo q by have := ceilLogTwo_ge_two q (by omega); omega)
          omega
        have : 1 ≤ 6 * (2 ^ (compileAdvice q).t - 1) * (3 + (q + (compileAdvice q).t + 2)) :=
          Nat.mul_pos (Nat.mul_pos (by omega) hp1) (by omega)
        omega
      unfold digitSpan
      rw [ht]
      calc 2 * (2 * (ceilLogTwo q + 2 * (2 ^ ceilLogTwo q - 1)))
          ≤ 1 * (2 ^ (q - 1) + 1) := by omega
        _ ≤ smallDigitZeroFormula q * (2 ^ (q - 1) + 1) := Nat.mul_le_mul_right _ hz1
  unfold widthFirstZeroCharge
  calc 2 * (n * (2 * ((compileAdvice (ceilLogTwo n)).t +
        2 * digitSpan (compileAdvice (ceilLogTwo n)))))
      = n * (2 * (2 * ((compileAdvice (ceilLogTwo n)).t +
          2 * digitSpan (compileAdvice (ceilLogTwo n))))) := Nat.mul_left_comm _ _ _
    _ ≤ n * (smallDigitZeroTable (ceilLogTwo n) * n) := Nat.mul_le_mul_left n hsite
    _ = smallDigitZeroTable (ceilLogTwo n) * n ^ 2 := by
        rw [Nat.pow_two, Nat.mul_comm n, Nat.mul_assoc]

/-- **The SMALL first-zero premise at the band reference** at the slice table
`smallDigitZeroTable`.  Consumer: `l3HeadlineOfCleanBranches`. -/
theorem bandWidthFirstZeroClockSmall {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hsmall : (compileAdvice (ceilLogTwo n)).useSmall = true) :
    WidthDigitFirstZeroClock (bandWidthDigitReference ring hn)
      (widthDigitBandCharge n smallDigitZeroTable (bankRepairDigitFirstZeroMicroCharge n)) := by
  rw [bandWidthDigitReferenceSmall ring hn hsmall, widthDigitBandChargeSmall _ _ hsmall]
  exact bankRepairDigitChargedMono _ _ _ (widthFirstZeroChargeSlice hn hsmall)
    (smallWidthFirstZeroClock ring hn hsmall)

end L3.WidthDigit

#print axioms L3.WidthDigit.widthDigitFirstZeroClockOfReference
#print axioms L3.WidthDigit.widthDigitFirstZeroClockBankOfReference
#print axioms L3.WidthDigit.smallWidthFirstZeroClock
#print axioms L3.WidthDigit.widthFirstZeroChargeSlice
#print axioms L3.WidthDigit.bandWidthFirstZeroClockSmall
