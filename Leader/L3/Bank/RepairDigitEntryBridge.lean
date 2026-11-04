import Leader.L3.Bank.RepairDigitUseTrack
import Leader.L3.Bank.RepairDigitEntryPhase

/-!
# R10c group 6, step 4: from a recorded strict completion to the cycle class

The lane-level phase of the strict cohort (`L3.DigitEntryPhase`) needs one fact per letter
(`StrictGo`) and a start (the tail just sampled). This module produces both from the audit of a
coupled BANK x audit run started at `digitAuditInitial`, and concludes
`strictCompletionCyc` / `firstStrictCyc`: if the final audit of the run of a word from a layout
state `z0` records a (first) strict completion of the pair `(src, src + R)` on `lane`, the
masked lane of the final state is in the cycle class `CohortCyc R`.

* runs: `runAt` (prefix states), `runFrames`, `frameTime` (a recorded frame with time `t + 1`
  is the frame `frameAt` of letter `t` at the prefix state `t`), the lane trace `laneAt` with
  its lane letters `keAt` (`laneAtStep`), the correspondence with identity at every prefix
  (`runAtCorr`);
* rows of one letter: `srcRows`/`srcRowsBank` (source outputs), `carryOrigin` (target
  ledgers), `inOrigin` (the delimiter input), `sampleStep`, `delExport`, `delRecv`,
  `termLedger`;
* the three phases: `tailRun` (tail sweep, step 4b), `inputBack` and `carryChain` (step 4c:
  the strict input and the strict ledger, by backward persistence `carryBack` and creation
  `carryCreate`), glued by `bottomGlue` and `strictTraceUpTo`.

Consumer: the entry stage `StructuralCut → EntryCut 0` (group 6, `BlockEntry.PairPin`).
-/

namespace L3.DigitEntryBridge

set_option autoImplicit false
set_option linter.unusedSectionVars false

open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree
open L3.RenewalReferenceClock
open L3.CohortDomination
open L3.CohortTail
open L3.CohortSites
open L3.CohortEntry
open L3.PacketClass
open L3.CohortStages
open L3.Rearm
open L3.Recording
open L3.GhostBridge
open L3.Correspondence
open L3.CohortIdentity
open L3.CohortWindow
open L3.CohortClose
open L3.ValueLedger
open L3.UseRows
open L3.UseCells
open L3.UseTrack
open L3.DigitEntryPhase

/-! ### Prefix states of a coupled run -/

section Runs

variable {n : Nat} (ring : DirectedRing n)
  (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)

/-- The state after the first `t` letters of `word`. -/
def runAt (q : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (word : List (Fin n)) (t : Nat) :
    BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n :=
  (word.take t).foldl (bankRepairDigitBoundaryAuditNext ring hbank) q

/-- The frame that the audit letter `e` prepends at the state `x`. -/
def frameAt (x : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (e : Fin n) : DigitFrame (compileAdvice (ceilLogTwo n)) n :=
  ⟨x.2.clock + 1, e, piD x.1.val.1, x.2.current, svcAt ring (piD x.1.val.1) x.2 e⟩

/-- One more letter. Consumer: `laneAtStep` and the group 6 assembly. -/
theorem runAtSucc : ∀ (word : List (Fin n))
    (q : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (t : Nat) (e : Fin n), word[t]? = some e →
    runAt ring hbank q word (t + 1) =
      bankRepairDigitBoundaryAuditNext ring hbank (runAt ring hbank q word t) e := by
  intro word
  induction word with
  | nil => intro q t e h; simp at h
  | cons a rest ih =>
    intro q t e h
    cases t with
    | zero =>
      simp at h
      subst h
      rfl
    | succ t =>
      have h' : rest[t]? = some e := by simpa using h
      exact ih _ t e h'

/-- The clock counts the letters. Consumer: `frameTime`. -/
theorem runAtClock : ∀ (word : List (Fin n))
    (q : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (t : Nat), t ≤ word.length → (runAt ring hbank q word t).2.clock = q.2.clock + t := by
  intro word
  induction word with
  | nil =>
    intro q t h
    have : t = 0 := by simp at h; omega
    subst this
    rfl
  | cons a rest ih =>
    intro q t h
    cases t with
    | zero => rfl
    | succ t =>
      have := ih (bankRepairDigitBoundaryAuditNext ring hbank q a) t (by simp at h; omega)
      show (runAt ring hbank (bankRepairDigitBoundaryAuditNext ring hbank q a) rest t).2.clock = _
      rw [this]
      show q.2.clock + 1 + t = q.2.clock + (t + 1)
      omega

/-- Past the end of the word the prefix state is the final state. Consumer: `laneAtStep`,
`exportUnique`, `strictCompletionCyc`. -/
theorem runAtLen (word : List (Fin n))
    (q : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (t : Nat) (h : word.length ≤ t) :
    runAt ring hbank q word t = word.foldl (bankRepairDigitBoundaryAuditNext ring hbank) q := by
  unfold runAt
  rw [List.take_of_length_le h]

/-- **Fold lemma (step 4a).** Every frame of the final audit is an initial frame or the
one-step frame of the letter `t` at the prefix state `t`. Consumer: `frameTime` and the group 6
assembly (recorded samples, exports and terminals become letters of the run). -/
theorem runFrames : ∀ (word : List (Fin n))
    (q : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (f : DigitFrame (compileAdvice (ceilLogTwo n)) n),
    f ∈ (word.foldl (bankRepairDigitBoundaryAuditNext ring hbank) q).2.frames →
    f ∈ q.2.frames ∨ ∃ t e, word[t]? = some e ∧ f = frameAt ring hbank (runAt ring hbank q word t) e := by
  intro word
  induction word with
  | nil => intro q f hf; exact Or.inl hf
  | cons a rest ih =>
    intro q f hf
    rcases ih (bankRepairDigitBoundaryAuditNext ring hbank q a) f hf with h | ⟨t, e, h1, h2⟩
    · rcases auditFrameMemStepCases ring (piD q.1.val.1) q.2 a f h with h3 | h3
      · exact Or.inl h3
      · exact Or.inr ⟨0, a, rfl, h3⟩
    · exact Or.inr ⟨t + 1, e, by simpa using h1, h2⟩

/-- Frames are never dropped. Consumer: `runFramesAtEnd`. -/
theorem framesMono : ∀ (word : List (Fin n))
    (q : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (f : DigitFrame (compileAdvice (ceilLogTwo n)) n), f ∈ q.2.frames →
    f ∈ (word.foldl (bankRepairDigitBoundaryAuditNext ring hbank) q).2.frames := by
  intro word
  induction word with
  | nil => intro q f h; exact h
  | cons a rest ih =>
    intro q f h
    exact ih _ f (auditFrameMemStep ring (piD q.1.val.1) q.2 a f h)

/-- Frames of a prefix state survive to the final audit. Consumer: the group 6 assembly
(provenance of a tracked atom read in the final audit). -/
theorem runFramesAtEnd (word : List (Fin n))
    (q : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (t : Nat) (f : DigitFrame (compileAdvice (ceilLogTwo n)) n)
    (h : f ∈ (runAt ring hbank q word t).2.frames) :
    f ∈ (word.foldl (bankRepairDigitBoundaryAuditNext ring hbank) q).2.frames := by
  have e : (word.drop t).foldl (bankRepairDigitBoundaryAuditNext ring hbank)
      (runAt ring hbank q word t) = word.foldl (bankRepairDigitBoundaryAuditNext ring hbank) q := by
    unfold runAt
    rw [← List.foldl_append, List.take_append_drop]
  rw [← e]
  exact framesMono ring hbank _ _ f h

/-- A recorded frame of a run from a frameless start at clock `0` is the one-step frame of
letter `time - 1`. Consumer: the group 6 assembly. -/
theorem frameTime (word : List (Fin n))
    (q : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (h0 : q.2.frames = []) (hc : q.2.clock = 0) (f : DigitFrame (compileAdvice (ceilLogTwo n)) n)
    (hf : f ∈ (word.foldl (bankRepairDigitBoundaryAuditNext ring hbank) q).2.frames) :
    ∃ t e, word[t]? = some e ∧ f.time = t + 1 ∧
      f = frameAt ring hbank (runAt ring hbank q word t) e := by
  rcases runFrames ring hbank word q f hf with h | ⟨t, e, h1, h2⟩
  · rw [h0] at h
    exact absurd h List.not_mem_nil
  · refine ⟨t, e, h1, ?_, h2⟩
    have ht : t < word.length := by
      rcases Nat.lt_or_ge t word.length with h | h
      · exact h
      · rw [List.getElem?_eq_none_iff.mpr h] at h1
        cases h1
    rw [h2]
    show (runAt ring hbank q word t).2.clock + 1 = t + 1
    rw [runAtClock ring hbank word q t (by omega), hc]
    omega

end Runs

/-! ### The lane trace of one interior pair -/

section Trace

variable {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
  (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) (root : Fin n) (lane : DigitLane)
  (src R : Nat) (hR : 2 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n)

/-- The coupled start at an arbitrary BANK state. -/
def startOf (z0 : BankReferenceState ring hbank) :
    BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n :=
  (z0, digitAuditInitial (piD z0.val.1))

/-- The masked lane of the pair at prefix `t`. -/
def laneAt (z0 : BankReferenceState ring hbank) (word : List (Fin n)) (t : Nat) : CohortLane :=
  cohortProj ring root lane src R (piD (runAt ring hbank (startOf ring hbank z0) word t).1.val.1)

/-- The lane letter of letter `t` (`none` past the end of the word). -/
def keAt (word : List (Fin n)) (t : Nat) : Option Nat :=
  (word[t]?).bind (cohortEdgeOf root src R)

include hn hR hsrc hend in
/-- Layout and the correspondence with identity at every prefix. Consumer: every row lemma of
the group 6 assembly. -/
theorem runAtCorr (z0 : BankReferenceState ring hbank) (hz : CohortLayout ring hbank root src R z0)
    (word : List (Fin n)) (t : Nat) :
    CohortLayout ring hbank root src R (runAt ring hbank (startOf ring hbank z0) word t).1 ∧
      GhostCorrDistinct ring root lane src R (InheritedOk lane)
        (piD (runAt ring hbank (startOf ring hbank z0) word t).1.val.1)
        (runAt ring hbank (startOf ring hbank z0) word t).2 :=
  ghostCorrDistinctFromStart ring hn hbank root lane src R hR hsrc hend z0 hz (word.take t)

include hn hR hsrc hend in
/-- The lane trace moves by the lane letters. Consumer: `strictTraceRun` in the group 6
assembly. -/
theorem laneAtStep (z0 : BankReferenceState ring hbank) (hz : CohortLayout ring hbank root src R z0)
    (word : List (Fin n)) (t : Nat) :
    laneAt ring hbank root lane src R z0 word (t + 1) =
      cohortLaneStep R (laneAt ring hbank root lane src R z0 word t) (keAt root src R word t) := by
  cases h : word[t]? with
  | none =>
    have hl : word.length ≤ t := List.getElem?_eq_none_iff.mp h
    have e1 : runAt ring hbank (startOf ring hbank z0) word (t + 1) =
        runAt ring hbank (startOf ring hbank z0) word t := by
      rw [runAtLen ring hbank _ _ (t + 1) (by omega), runAtLen ring hbank _ _ t hl]
    unfold laneAt keAt
    rw [e1, h]
    rfl
  | some e =>
    unfold laneAt keAt
    rw [runAtSucc ring hbank word _ t e h, h]
    exact (cohortBankStep ring hn hbank root lane src R hR hsrc hend _
      (runAtCorr ring hn hbank root lane src R hR hsrc hend z0 hz word t).1 e).2

end Trace

/-! ### Source outputs of one letter -/

section Rows

variable {c : Compiled} {n : Nat}

/-- The source-output rows of one letter on the drawn pair edge `ke`, with the letter's stamp:
cells off the edge are untouched, a Pipe edge moves the outputs by `ghostPipe`, the delimiter
edge moves the last source output by `ghostDel`. -/
def OutH (R : Nat) (s : CohortLane) (ke : Option Nat) (stamp : DigitStamp n)
    (o o' : Nat → DigitOutGhost n) : Prop :=
  (∀ q, q < R → (∀ k, ke = some k → q ≠ k ∧ q ≠ k + 1) → o' q = o q) ∧
  (∀ k, ke = some k → k + 1 < R →
    (o' k, o' (k + 1)) = ghostPipe stamp (decide (k = 0)) (s.out k) (s.out (k + 1)) (o k)
      (o (k + 1))) ∧
  (ke = some (R - 1) → ∃ gyi,
    o' (R - 1) = (ghostDel stamp (s.out (R - 1)) (s.inp R) (s.live R) (o (R - 1)) gyi).1)

/-- **Source rows of one letter** on the projected ring (layout hypotheses of
`cohortProjStep`). Consumer: `srcRowsBank`. -/
theorem srcRows (ring : DirectedRing n) (hn : 2 ≤ n) (root : Fin n)
    (S : Fin n → ProjD c) (R src : Nat) (hR : 2 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n)
    (hroot : ∀ i, (S i).word.native.l = true ↔ i = root)
    (hb0 : (S (digitSite ring root src)).word.beta = true)
    (hbR : (S (digitSite ring root (src + R))).word.beta = true)
    (hbF : ∀ k, 0 < k → k < 2 * R → k ≠ R →
      (S (digitSite ring root (src + k))).word.beta = false)
    (lane : DigitLane) (A : DigitAudit c n)
    (j : Nat) (hj : j < n)
    (hbX : (pairW (S (digitSite ring root j)).word
      (S (digitSite ring root (j + 1))).word).1.beta = (S (digitSite ring root j)).word.beta)
    (hbY : (pairW (S (digitSite ring root j)).word
      (S (digitSite ring root (j + 1))).word).2.beta =
        (S (digitSite ring root (j + 1))).word.beta) :
    OutH R (cohortProj ring root lane src R S) (cohortEdgeOf root src R (digitSite ring root j))
      (DigitStamp.mk (A.clock + 1) (digitSite ring root j) lane)
      (fun q => (laneCells ring root lane src A.current q).out)
      (fun q => (laneCells ring root lane src
        (digitAuditStep ring S A (digitSite ring root j)).current q).out) := by
  by_cases hin : src ≤ j ∧ j < src + 2 * R
  · obtain ⟨k, rfl⟩ : ∃ k, j = src + k := ⟨j - src, by omega⟩
    have hke : cohortEdgeOf root src R (digitSite ring root (src + k)) = some k :=
      cohortEdgeOfSite ring root src R hend k (by omega)
    have hfr : ∀ q, q ≠ k → q ≠ k + 1 → q < 2 * R →
        laneCells ring root lane src
          (digitAuditStep ring S A (digitSite ring root (src + k))).current q =
        laneCells ring root lane src A.current q := by
      intro q hq1 hq2 hq
      unfold laneCells
      rw [curFar]
      · intro he
        exact hq1 (by have := bankRepairDigitSiteInj ring root (by omega) (by omega) he; omega)
      · intro he
        rw [← bankRepairDigitSiteSucc] at he
        exact hq2 (by have := bankRepairDigitSiteInj ring root (by omega) (by omega) he; omega)
    have hx : laneCells ring root lane src
        (digitAuditStep ring S A (digitSite ring root (src + k))).current k =
        laneGhost lane (svcAt ring S A (digitSite ring root (src + k))).x := by
      unfold laneCells
      rw [curX]
    have hy : laneCells ring root lane src
        (digitAuditStep ring S A (digitSite ring root (src + k))).current (k + 1) =
        laneGhost lane (svcAt ring S A (digitSite ring root (src + k))).y := by
      unfold laneCells
      rw [show digitSite ring root (src + (k + 1)) =
        ring.rightNeighbor (digitSite ring root (src + k)) from rfl, curY ring hn]
    have hlx := bankRepairDigitSiteNonroot ring root S hroot (src + k) (by omega) (by omega)
    have hly := bankRepairDigitSiteNonroot ring root S hroot (src + k + 1) (by omega) (by omega)
    refine ⟨fun q hq hne => ?_, fun k' hk' h1 => ?_, fun hk => ?_⟩
    · obtain ⟨n1, n2⟩ := hne k hke
      exact congrArg DigitLaneGhost.out (hfr q n1 n2 (by omega))
    · rw [hke] at hk'
      have hkk : k = k' := Option.some.inj hk'
      subst hkk
      have hbx : (S (digitSite ring root (src + k))).word.beta = decide (k = 0) := by
        by_cases hk0 : k = 0
        · rw [decide_eq_true hk0, hk0]
          exact hb0
        · rw [decide_eq_false hk0]
          exact hbF k (by omega) (by omega) (by omega)
      have hmX : laneMarkerX lane (S (digitSite ring root (src + k)))
          (S (digitSite ring root (src + k + 1))) = decide (k = 0) := by
        rw [laneMarkerXBeta lane _ _ hbX]
        exact hbx
      have hmy : laneMarkerY lane (S (digitSite ring root (src + k)))
          (S (digitSite ring root (src + k + 1))) = false := by
        rw [laneMarkerYBeta lane _ _ hbY]
        exact hbF (k + 1) (by omega) (by omega) (by omega)
      show ((laneCells ring root lane src
          (digitAuditStep ring S A (digitSite ring root (src + k))).current k).out,
        (laneCells ring root lane src
          (digitAuditStep ring S A (digitSite ring root (src + k))).current (k + 1)).out) = _
      rw [hx, hy, projOut ring root lane src R S k (by omega),
        projOut ring root lane src R S (k + 1) h1, ← hmX]
      exact rowPipeD lane (A.clock + 1) (digitSite ring root (src + k))
        (ring.rightNeighbor (digitSite ring root (src + k)))
        (S (digitSite ring root (src + k))) (S (digitSite ring root (src + k + 1)))
        (A.current (digitSite ring root (src + k)))
        (A.current (digitSite ring root (src + k + 1))) hlx hly hmy
    · rw [hke] at hk
      have hk1 : k = R - 1 := Option.some.inj hk
      subst hk1
      have hmx : laneMarkerX lane (S (digitSite ring root (src + (R - 1))))
          (S (digitSite ring root (src + (R - 1) + 1))) = false := by
        rw [laneMarkerXBeta lane _ _ hbX]
        exact hbF (R - 1) (by omega) (by omega) (by omega)
      have hmy : laneMarkerY lane (S (digitSite ring root (src + (R - 1))))
          (S (digitSite ring root (src + (R - 1) + 1))) = true := by
        rw [laneMarkerYBeta lane _ _ hbY, show src + (R - 1) + 1 = src + R by omega]
        exact hbR
      have hrow := rowDelD lane (A.clock + 1) (digitSite ring root (src + (R - 1)))
        (ring.rightNeighbor (digitSite ring root (src + (R - 1))))
        (S (digitSite ring root (src + (R - 1)))) (S (digitSite ring root (src + (R - 1) + 1)))
        (A.current (digitSite ring root (src + (R - 1))))
        (A.current (digitSite ring root (src + (R - 1) + 1))) hlx hly hmx hmy
      refine ⟨(laneGhost lane (A.current (digitSite ring root (src + (R - 1) + 1)))).input, ?_⟩
      show (laneCells ring root lane src
          (digitAuditStep ring S A (digitSite ring root (src + (R - 1)))).current (R - 1)).out = _
      rw [hx, projOut ring root lane src R S (R - 1) (by omega),
        projIn ring root lane src R S R (Nat.le_refl R) (by omega),
        projLive ring root lane src R S R (Nat.le_refl R) (by omega),
        show src + R = src + (R - 1) + 1 by omega]
      exact congrArg Prod.fst hrow.1
  · have hke : cohortEdgeOf root src R (digitSite ring root j) = none := by
      unfold cohortEdgeOf
      rw [cohortIdxSite ring root j hj, if_neg hin]
    refine ⟨fun q hq _ => ?_, (fun k hk => by rw [hke] at hk; cases hk),
      (fun hk => by rw [hke] at hk; cases hk)⟩
    have farNe : ∀ q, q < 2 * R → src + q ≠ j → src + q ≠ j + 1 →
        laneCells ring root lane src (digitAuditStep ring S A (digitSite ring root j)).current q =
        laneCells ring root lane src A.current q := by
      intro q hq n1 n2
      unfold laneCells
      rw [curFar]
      · intro he
        exact n1 (bankRepairDigitSiteInj ring root (by omega) hj he)
      · intro he
        rw [← bankRepairDigitSiteSucc] at he
        by_cases hjn : j + 1 < n
        · exact n2 (bankRepairDigitSiteInj ring root (by omega) hjn he)
        · rw [show j + 1 = n by omega, bankRepairDigitSiteN] at he
          have := bankRepairDigitSiteInj ring root (k := src + q) (m := 0) (by omega) (by omega) he
          omega
    by_cases h1 : j + 1 = src ∧ q = 0
    · obtain ⟨h1, hq0⟩ := h1
      have hlx := bankRepairDigitSiteNonroot ring root S hroot j (by omega) (by omega)
      have hly := bankRepairDigitSiteNonroot ring root S hroot (j + 1) (by omega) (by omega)
      have hmy : laneMarkerY lane (S (digitSite ring root j))
          (S (digitSite ring root (j + 1))) = true := by
        rw [laneMarkerYBeta lane _ _ hbY, h1]
        exact hb0
      show (laneCells ring root lane src
        (digitAuditStep ring S A (digitSite ring root j)).current q).out =
        (laneCells ring root lane src A.current q).out
      rw [hq0]
      unfold laneCells
      rw [show digitSite ring root (src + 0) = ring.rightNeighbor (digitSite ring root j) by
        rw [← h1]; rfl, curY ring hn]
      exact rowEntryD lane (A.clock + 1) (digitSite ring root j)
        (ring.rightNeighbor (digitSite ring root j)) (S (digitSite ring root j))
        (S (digitSite ring root (j + 1))) (A.current (digitSite ring root j))
        (A.current (digitSite ring root (j + 1))) hlx hly hmy
    · exact congrArg DigitLaneGhost.out
        (farNe q (by omega) (by omega) (fun h => h1 ⟨by omega, by omega⟩))

/-- A sample is recorded only by a letter reading an unread slot. Consumer: `sampleU`. -/
theorem replaySampleU (lane : DigitLane) (time : Nat) (source destination : Fin n)
    (x y : DigitLaneView c) (gx gy : DigitLaneGhost c n) (s : DigitSample c n)
    (h : (digitLaneReplay lane time source destination x y gx gy).sample = some s) :
    x.out.isU = true := by
  cases hxo : x.out <;> simp [digitLaneReplay, hxo, OutTok.isU, OutTok.isD, OutTok.isE] at h ⊢
  all_goals (repeat' split at h) <;> simp_all

/-- A recorded sample of a letter: the letter's left cell held an unread slot. Consumer: the
start of the tail sweep in the group 6 assembly. -/
theorem sampleU (ring : DirectedRing n) (S : Fin n → ProjD c) (A : DigitAudit c n) (e : Fin n)
    (lane : DigitLane) (s : DigitSample c n)
    (h : (digitReceiptLane lane (svcAt ring S A e)).sample = some s) :
    bankRepairDigitOutShOf (bankRepairDigitLaneOut lane (S e).top) = .U := by
  unfold svcAt at h
  rw [serviceLane] at h
  have hu := replaySampleU lane _ _ _ _ _ _ _ s h
  rw [laneViewOut] at hu
  cases hx : bankRepairDigitLaneOut lane (S e).top <;>
    simp_all [OutTok.isU, bankRepairDigitOutShOf]

end Rows

/-! ### Ledgers on the right cell of a Fin edge -/

section CarryRows

variable {c : Compiled} {n : Nat}

/-- The left ledger a success extends (`oldCarry` of the replay). -/
def oldLedger (stamp : DigitStamp n) (g : Option (DigitCarryGhost c n)) : DigitCarryGhost c n :=
  g.getD { inherited := some (.missing stamp .carry), uses := [] }

/-- The right ledger of a replay is kept, or (on a live left carry) it is the left ledger with
one more use stamped by the letter. Consumer: `carryYD`. -/
theorem replayCarryYCases (lane : DigitLane) (time : Nat) (source destination : Fin n)
    (x y : DigitLaneView c) (gx gy : DigitLaneGhost c n)
    (hlx : x.leader = false) (hly : y.leader = false) :
    (digitLaneReplay lane time source destination x y gx gy).y.carry = gy.carry ∨
    (x.carryLive = true ∧ ∃ u : DigitUse c n, u.time = time ∧
      (digitLaneReplay lane time source destination x y gx gy).y.carry =
        some ⟨(oldLedger ⟨time, source, lane⟩ gx.carry).inherited,
          (oldLedger ⟨time, source, lane⟩ gx.carry).uses ++ [u]⟩) := by
  cases hxc : x.carryLive
  · exact Or.inl (replayCarryYKeep lane time source destination x y gx gy hlx hly hxc)
  · simp [digitLaneReplay, hlx, hly, hxc, oldLedger]
    (repeat' split) <;> simp_all

/-- The right-cell ledger row of a Fin edge on the lane replay. Consumer: `carryYRing`. -/
theorem carryYD (lane : DigitLane) (t : Nat) (e d : Fin n) (X Y : ProjD c)
    (gx gy : DigitGhost c n) (hlx : X.word.native.l = false) (hly : Y.word.native.l = false) :
    (laneGhost lane (digitService t e d X Y gx gy).y).carry = (laneGhost lane gy).carry ∨
    (bankRepairDigitLaneLive lane X.top = true ∧ ∃ u : DigitUse c n, u.time = t ∧
      (laneGhost lane (digitService t e d X Y gx gy).y).carry =
        some ⟨(oldLedger ⟨t, e, lane⟩ (laneGhost lane gx).carry).inherited,
          (oldLedger ⟨t, e, lane⟩ (laneGhost lane gx).carry).uses ++ [u]⟩) := by
  have h := replayCarryYCases lane t e d (digitLaneView lane X (laneMarkerX lane X Y))
    (digitLaneView lane Y (laneMarkerY lane X Y)) (laneGhost lane gx) (laneGhost lane gy)
    (by rw [laneViewLeader]; exact hlx) (by rw [laneViewLeader]; exact hly)
  rw [laneViewLive] at h
  rw [serviceLaneY, serviceLane]
  exact h

/-- The right ledger of a Fin edge on the ring. Consumer: `carryOrigin`. -/
theorem carryYRing (ring : DirectedRing n) (hn : 2 ≤ n) (root : Fin n)
    (S : Fin n → ProjD c) (R src : Nat) (hsrc : 2 ≤ src) (hend : src + 2 * R < n)
    (hroot : ∀ i, (S i).word.native.l = true ↔ i = root)
    (lane : DigitLane) (A : DigitAudit c n) (k : Nat) (hRk : R ≤ k) (hk2 : k + 1 < 2 * R) :
    (laneCells ring root lane src
        (digitAuditStep ring S A (digitSite ring root (src + k))).current (k + 1)).carry =
      (laneCells ring root lane src A.current (k + 1)).carry ∨
    ((cohortProj ring root lane src R S).live k = true ∧ ∃ u : DigitUse c n,
      u.time = A.clock + 1 ∧
      (laneCells ring root lane src
          (digitAuditStep ring S A (digitSite ring root (src + k))).current (k + 1)).carry =
        some ⟨(oldLedger ⟨A.clock + 1, digitSite ring root (src + k), lane⟩
            (laneCells ring root lane src A.current k).carry).inherited,
          (oldLedger ⟨A.clock + 1, digitSite ring root (src + k), lane⟩
            (laneCells ring root lane src A.current k).carry).uses ++ [u]⟩) := by
  have hy : laneCells ring root lane src
      (digitAuditStep ring S A (digitSite ring root (src + k))).current (k + 1) =
      laneGhost lane (svcAt ring S A (digitSite ring root (src + k))).y := by
    unfold laneCells
    rw [show digitSite ring root (src + (k + 1)) =
      ring.rightNeighbor (digitSite ring root (src + k)) from rfl, curY ring hn]
  have hlx := bankRepairDigitSiteNonroot ring root S hroot (src + k) (by omega) (by omega)
  have hly := bankRepairDigitSiteNonroot ring root S hroot (src + k + 1) (by omega) (by omega)
  rw [hy, projLive ring root lane src R S k hRk (by omega)]
  exact carryYD lane (A.clock + 1) (digitSite ring root (src + k))
    (ring.rightNeighbor (digitSite ring root (src + k)))
    (S (digitSite ring root (src + k))) (S (digitSite ring root (src + k + 1)))
    (A.current (digitSite ring root (src + k)))
    (A.current (digitSite ring root (src + k + 1))) hlx hly

end CarryRows

/-! ### One coupled letter: origins of outputs, inputs and ledgers -/

section Bank

variable {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
  (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) (root : Fin n) (lane : DigitLane)
  (src R : Nat) (hR : 2 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n)

include hn hR hsrc hend in
/-- Source rows on the coupled chain. Consumer: the tail sweep of the group 6 assembly. -/
theorem srcRowsBank
    (z : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (hz : CohortLayout ring hbank root src R z.1) (e : Fin n) :
    OutH R (cohortProj ring root lane src R (piD z.1.val.1)) (cohortEdgeOf root src R e)
      (DigitStamp.mk (z.2.clock + 1) e lane)
      (fun q => (laneCells ring root lane src z.2.current q).out)
      (fun q => (laneCells ring root lane src
        (bankRepairDigitBoundaryAuditNext ring hbank z e).2.current q).out) := by
  obtain ⟨hL, hb0, hbR, hb2R, hbF⟩ := hz
  obtain ⟨-, hroot, hbX, hbY⟩ := bankRepairDigitLeadBankEdge ring hn hbank root z.1 hL e
  obtain ⟨jx, hj, rfl⟩ := bankRepairDigitSiteSurj ring root e
  exact srcRows ring (by omega) root (piD z.1.val.1) R src hR hsrc hend hroot hb0 hbR hbF lane
    z.2 jx hj hbX hbY

include hn hR hsrc hend in
/-- **Ledger origin** of one coupled letter on a target cell: kept, launched at `R` (one use
reading the input of `R`), or a success from the cell below (one more use); new uses are stamped
by the letter. Consumer: `carryBack` in the group 6 assembly. -/
theorem carryOrigin (Base : Bool → DigitAtom n → Prop)
    (z : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (hz : CohortLayout ring hbank root src R z.1)
    (hc : GhostCorr ring root lane src R Base (piD z.1.val.1) z.2) (e : Fin n)
    (q : Nat) (hRq : R ≤ q) (hq : q < 2 * R) (K : DigitCarryGhost (compileAdvice (ceilLogTwo n)) n)
    (hK : caA ring root lane src (bankRepairDigitBoundaryAuditNext ring hbank z e).2 q = some K) :
    caA ring root lane src z.2 q = some K ∨
    (q = R ∧ cohortEdgeOf root src R e = some R ∧
      ∃ u : DigitUse (compileAdvice (ceilLogTwo n)) n, u.time = z.2.clock + 1 ∧
        u.operand = inA ring root lane src z.2 R ∧ K = ⟨none, [u]⟩) ∨
    (R < q ∧ cohortEdgeOf root src R e = some (q - 1) ∧
      ∃ (L : DigitCarryGhost (compileAdvice (ceilLogTwo n)) n)
        (u : DigitUse (compileAdvice (ceilLogTwo n)) n),
        caA ring root lane src z.2 (q - 1) = some L ∧ u.time = z.2.clock + 1 ∧
          K = ⟨L.inherited, L.uses ++ [u]⟩) := by
  obtain ⟨hL, hb0, hbR, hb2R, hbF⟩ := hz
  obtain ⟨-, hroot, hbX, hbY⟩ := bankRepairDigitLeadBankEdge ring hn hbank root z.1 hL e
  obtain ⟨jx, hj, rfl⟩ := bankRepairDigitSiteSurj ring root e
  have hrows := tgtRows ring (by omega) root (piD z.1.val.1) R src hR hsrc hend hroot hbR hb2R
    hbF lane z.2 jx hj hbX hbY
  change (laneCells ring root lane src (digitAuditStep ring (piD z.1.val.1) z.2
    (digitSite ring root jx)).current q).carry = some K at hK
  unfold caA inA
  rcases hke : cohortEdgeOf root src R (digitSite ring root jx) with _ | k
  · left
    have := congrArg DigitLaneGhost.carry (hrows.1 q hRq hq (by rw [hke]; simp) (by rw [hke]; simp))
    rw [this] at hK
    exact hK
  · have hjk := edgeOfSome ring root src R jx k hj hke
    by_cases hkq : k = q
    · subst hkq
      by_cases hk2 : k + 1 < 2 * R
      · obtain ⟨-, hX, -, -⟩ := hrows.2.2.1 k hke hRq hk2
        rcases hX with h | h | ⟨h1, -, u, hu1, hu2, hu3⟩
        · rw [h] at hK
          cases hK
        · left
          rw [← hK, h]
        · right; left
          rw [hu3] at hK
          refine ⟨h1, by rw [h1], u, hu1, by rw [hu2, h1], (Option.some.inj hK).symm⟩
      · have hkt : k = 2 * R - 1 := by omega
        obtain ⟨-, hX, -⟩ := hrows.2.2.2 (by rw [hke, hkt])
        rw [hkt] at hK ⊢
        rcases hX with h | h
        · rw [h] at hK
          cases hK
        · left
          rw [← hK, h]
    · by_cases hkq1 : k + 1 = q
      · subst hkq1
        by_cases hkR : k + 1 = R
        · have hk' : k = R - 1 := by omega
          obtain ⟨-, hcR⟩ := hrows.2.1 (by rw [hke, hk'])
          left
          rw [show k + 1 = R from hkR] at hK ⊢
          rw [← hK, hcR]
        · subst hjk
          rcases carryYRing ring (by omega) root (piD z.1.val.1) R src hsrc hend hroot lane z.2 k
            (by omega) hq with h | ⟨hl, u, hu1, hu2⟩
          · left
            rw [← hK, h]
          · right; right
            obtain ⟨L, hLk⟩ : ∃ L, (laneCells ring root lane src z.2.current k).carry = some L := by
              have h3 := (hc.2 k (by omega) (by omega)).2
              rw [hl] at h3
              exact Option.isSome_iff_exists.mp h3.symm
            rw [hu2, hLk] at hK
            refine ⟨by omega, by simp, L, u, by simp [hLk], hu1, ?_⟩
            exact (Option.some.inj hK).symm
      · left
        have := congrArg DigitLaneGhost.carry (hrows.1 q hRq hq
          (by rw [hke]; intro h; exact hkq (Option.some.inj h))
          (by rw [hke]; intro h; have := Option.some.inj h; omega))
        rw [this] at hK
        exact hK

include hn hR hsrc hend in
/-- **Input origin** at the target delimiter cell `R`: kept, or delivered by the delimiter edge,
which then records an export of that atom stamped by the letter. Consumer: `inputBack` in the
group 6 assembly. -/
theorem inOrigin
    (z : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (hz : CohortLayout ring hbank root src R z.1) (e : Fin n) (x : DigitAtom n)
    (hx : inA ring root lane src (bankRepairDigitBoundaryAuditNext ring hbank z e).2 R = some x) :
    inA ring root lane src z.2 R = some x ∨
    (cohortEdgeOf root src R e = some (R - 1) ∧
      ∃ ex : DigitExport (compileAdvice (ceilLogTwo n)) n,
        (digitReceiptLane lane (svcAt ring (piD z.1.val.1) z.2 e)).exported = some ex ∧
        ex.operand = some x ∧ ex.time = z.2.clock + 1 ∧ ex.lane = lane ∧ ex.source = e) := by
  obtain ⟨hL, hb0, hbR, hb2R, hbF⟩ := hz
  obtain ⟨-, hroot, hbX, hbY⟩ := bankRepairDigitLeadBankEdge ring hn hbank root z.1 hL e
  obtain ⟨jx, hj, rfl⟩ := bankRepairDigitSiteSurj ring root e
  have hrows := tgtRows ring (by omega) root (piD z.1.val.1) R src hR hsrc hend hroot hbR hb2R
    hbF lane z.2 jx hj hbX hbY
  change (laneCells ring root lane src (digitAuditStep ring (piD z.1.val.1) z.2
    (digitSite ring root jx)).current R).input = some x at hx
  unfold inA
  rcases hke : cohortEdgeOf root src R (digitSite ring root jx) with _ | k
  · left
    have := congrArg DigitLaneGhost.input
      (hrows.1 R (Nat.le_refl R) (by omega) (by rw [hke]; simp) (by rw [hke]; simp))
    rw [this] at hx
    exact hx
  · by_cases hk1 : k = R - 1
    · subst hk1
      have hjk := edgeOfSome ring root src R jx (R - 1) hj hke
      subst hjk
      obtain ⟨hin, -⟩ := hrows.2.1 hke
      rw [hin] at hx
      rcases delInSome _ _ _ _ _ _ x hx with h | ⟨hE, hk, ⟨T, hD⟩, hat⟩
      · exact Or.inl h
      · right
        refine ⟨rfl, ?_⟩
        have hdel := delEdgeFacts ring root (piD z.1.val.1) R src hR hend hroot hbR hbF lane z.2
          hbX hbY
        obtain ⟨ex, hex, hl, hs, ht⟩ := hdel.2 T hD hE hk
        refine ⟨ex, hex, ?_, ht, hl, hs⟩
        rw [delOperand ring root (piD z.1.val.1) R src hR hend hroot hbR hbF lane z.2 hbX hbY ex hex]
        exact hat
    · by_cases hkR : k = R
      · subst hkR
        obtain ⟨hin, -⟩ := hrows.2.2.1 k hke (Nat.le_refl k) (by omega)
        have h1 := congrArg Prod.fst hin
        simp only [ghostFinIn] at h1
        rw [h1] at hx
        exact Or.inl (finInXSome _ _ _ _ _ _ x hx)
      · left
        have := congrArg DigitLaneGhost.input (hrows.1 R (Nat.le_refl R) (by omega)
          (by rw [hke]; intro h; exact hkR (Option.some.inj h))
          (by rw [hke]; intro h; exact hk1 (Option.some.inj h)))
        rw [this] at hx
        exact hx

end Bank

/-! ### The tail packet under one letter (lane level) -/

section Tail

variable {n : Nat}

/-- A tracked tail packet ghost corresponds to a data packet. Consumer: `physTail`. -/
theorem outPacketD {Ok : Bool → DigitAtom n → Prop} {o : BankRepairDigitOutSh}
    {g : DigitOutGhost n} {a : DigitAtom n} (hc : OutCorr Ok o g) (hg : g = .packet (some a)) :
    ∃ T, o = .D T ∧ Ok T a := by
  subst hg
  cases o with
  | E => cases hc
  | U => simp [OutCorr, DigitOutGhost.obligation] at hc
  | D T => exact ⟨T, rfl, hc⟩

/-- **The tail packet under one letter**: the tracked atom `a` of a tail packet at source cell
`p` stays (and the cell still holds a tail packet), hops to the next source cell (and the cell
becomes the unread slot), or is offered to an empty carry-free target delimiter. Consumer: the
tail sweep of the group 6 assembly. -/
theorem srcStep {R : Nat} {s : CohortLane} {ke : Option Nat} {stamp : DigitStamp n}
    {o o' : Nat → DigitOutGhost n} (h : OutH R s ke stamp o o') {p : Nat} (hp : p < R)
    {a : DigitAtom n} (ho : o p = .packet (some a)) (hs : s.out p = .D true) :
    (o' p = .packet (some a) ∧ cohortTok R (cohortLaneStep R s ke) p = .pkt true) ∨
    (p + 1 < R ∧ o' (p + 1) = .packet (some a) ∧
      cohortTok R (cohortLaneStep R s ke) p = .other) ∨
    (p + 1 = R ∧ ke = some (R - 1) ∧ s.inp R = .E ∧ s.live R = false) := by
  have hx : cohortTokOut (s.out p) = .pkt true := by rw [hs]; rfl
  cases ke with
  | none =>
    left
    refine ⟨by rw [h.1 p hp (fun k hk => by cases hk)]; exact ho, ?_⟩
    show cohortTok R s p = _
    rw [cohortTokSrc s hp]
    exact hx
  | some k =>
    show _ ∨ _ ∨ _
    by_cases hk : k = p
    · subst hk
      by_cases h1 : k + 1 < R
      · have hpipe := h.2.1 k rfl h1
        obtain ⟨e1, -⟩ := cohortTokPipe R k s h1
        cases hy : s.out (k + 1) with
        | E =>
          right; left
          rw [hs, hy] at hpipe
          simp only [ghostPipe, ho, DigitOutGhost.atom] at hpipe
          refine ⟨h1, (Prod.mk.inj hpipe).2, ?_⟩
          show cohortTok R (cohortEdge R s k) k = _
          rw [e1, hs, hy]
          rfl
        | U =>
          left
          rw [hs, hy] at hpipe
          refine ⟨by rw [(Prod.mk.inj hpipe).1]; exact ho, ?_⟩
          show cohortTok R (cohortEdge R s k) k = _
          rw [e1, hs, hy]
          rfl
        | D T' =>
          left
          rw [hs, hy] at hpipe
          refine ⟨by rw [(Prod.mk.inj hpipe).1]; exact ho, ?_⟩
          show cohortTok R (cohortEdge R s k) k = _
          rw [e1, hs, hy]
          rfl
      · have hkR : k = R - 1 := by omega
        obtain ⟨gyi, hdel⟩ := h.2.2 (by rw [hkR])
        rw [← hkR, hs] at hdel
        obtain ⟨e1, -⟩ := cohortTokDel R k s (by omega)
        have hkR1 : k + 1 = R := by omega
        cases hl : s.live R with
        | true =>
          left
          rw [hl] at hdel
          refine ⟨by rw [hdel]; exact ho, ?_⟩
          show cohortTok R (cohortEdge R s k) k = _
          rw [e1, hs, hkR1, hl]
          rfl
        | false =>
          cases hi : s.inp R with
          | E => exact Or.inr (Or.inr ⟨hkR1, by rw [hkR], rfl, rfl⟩)
          | X =>
            left
            rw [hl, hi] at hdel
            refine ⟨by rw [hdel]; exact ho, ?_⟩
            show cohortTok R (cohortEdge R s k) k = _
            rw [e1, hs, hkR1, hl, hi]
            rfl
          | P T' =>
            left
            rw [hl, hi] at hdel
            refine ⟨by rw [hdel]; exact ho, ?_⟩
            show cohortTok R (cohortEdge R s k) k = _
            rw [e1, hs, hkR1, hl, hi]
            rfl
          | S T' =>
            left
            rw [hl, hi] at hdel
            refine ⟨by rw [hdel]; exact ho, ?_⟩
            show cohortTok R (cohortEdge R s k) k = _
            rw [e1, hs, hkR1, hl, hi]
            rfl
    · left
      by_cases hk1 : p = k + 1
      · subst hk1
        have h1 : k + 1 < R := hp
        have hpipe := h.2.1 k rfl h1
        obtain ⟨-, e2⟩ := cohortTokPipe R k s h1
        rw [hs] at hpipe
        refine ⟨?_, ?_⟩
        · have h2 := (Prod.mk.inj hpipe).2
          rw [h2]
          cases s.out k <;> simp [ho]
        · show cohortTok R (cohortEdge R s k) (k + 1) = _
          rw [e2, hs]
          cases s.out k <;> simp [bankRepairDigitPipeStep, cohortTokOut]
      · refine ⟨by rw [h.1 p hp (fun k' hk' => by
          cases hk'; exact ⟨fun h => hk h.symm, hk1⟩)]; exact ho, ?_⟩
        show cohortTok R (cohortEdge R s k) p = _
        rw [cohortTokFrame R k p s (fun h => hk h.symm) hk1, cohortTokSrc s hp]
        exact hx

end Tail

/-! ### The bottom of the strict region along a trace (lane level) -/

section Glue

variable {R : Nat}

/-- Strict track up to a horizon: the phase holds at time `K` when `StrictGo` holds at every
letter before `K`. Consumer: `strictCompletionCyc`. -/
theorem strictTraceUpTo (hR : 2 ≤ R) (st : Nat → CohortLane) (ke : Nat → Option Nat)
    (hst : ∀ t, st (t + 1) = cohortLaneStep R (st t) (ke t)) (p0 : Nat)
    (h0 : StrictPhase R (st 0) p0) :
    ∀ K, (∀ t, t < K → StrictGo R (st (t + 1)) (strictTrack R st p0 t)) →
      StrictPhase R (st K) (strictTrack R st p0 K) := by
  intro K
  induction K with
  | zero => intro _; exact h0
  | succ K ih =>
    intro hgo
    have hK := ih (fun t ht => hgo t (by omega))
    have e : strictTrack R st p0 (K + 1) = strictNext R (st (K + 1)) (strictTrack R st p0 K) :=
      rfl
    have hg := hgo K (by omega)
    rw [e]
    rw [hst K] at hg ⊢
    exact strictPhaseStep hR hK (ke K) hg

/-- The tracked cell never decreases along a trace. Consumer: `strictCompletionCyc`. -/
theorem strictTrackMono (st : Nat → CohortLane) (p0 : Nat) :
    ∀ t d, strictTrack R st p0 t ≤ strictTrack R st p0 (t + d) := by
  intro t d
  induction d with
  | zero => exact Nat.le_refl _
  | succ d ih =>
    have := (strictNextBound (R := R) (st (t + d + 1)) (strictTrack R st p0 (t + d))).1
    exact Nat.le_trans ih this

/-- **The bottom along the target phase.** The bottom sits at `R + m` from time `V m` to
`V (m + 1)`: its cell stays non-empty strictly inside the interval, empties at `V (m + 1)`,
where the next cell holds the live carry (or the pair ends). Then the track is `R + m` at
`V m`, and `StrictGo` holds at every letter of the target phase. Consumer:
`strictCompletionCyc`. -/
theorem bottomGlue (st : Nat → CohortLane) (p0 : Nat) (V : Nat → Nat)
    (h0 : strictTrack R st p0 (V 0) = R) (hV : ∀ m, m < R → V m < V (m + 1))
    (hne : ∀ m, m < R → ∀ t, V m < t → t < V (m + 1) → cohortTok R (st t) (R + m) ≠ .empty)
    (hmv : ∀ m, m < R → cohortTok R (st (V (m + 1))) (R + m) = .empty ∧
      (m + 1 < R → (st (V (m + 1))).live (R + m + 1) = true)) :
    (∀ m, m ≤ R → strictTrack R st p0 (V m) = R + m) ∧
      ∀ t, V 0 ≤ t → t < V R → StrictGo R (st (t + 1)) (strictTrack R st p0 t) := by
  have inner : ∀ m, m < R → strictTrack R st p0 (V m) = R + m →
      (∀ d, V m + d < V (m + 1) → strictTrack R st p0 (V m + d) = R + m) := by
    intro m hm hstart d
    induction d with
    | zero => intro _; exact hstart
    | succ d ih =>
      intro hd
      have h1 := ih (by omega)
      show strictNext R (st (V m + d + 1)) (strictTrack R st p0 (V m + d)) = R + m
      rw [h1]
      unfold strictNext
      rw [if_neg (by omega), if_neg (fun hc => hne m hm (V m + d + 1) (by omega) hd hc.2)]
  have next : ∀ m, m < R → strictTrack R st p0 (V m) = R + m →
      strictTrack R st p0 (V (m + 1)) = R + m + 1 := by
    intro m hm hstart
    have hv := hV m hm
    obtain ⟨d, hd⟩ : ∃ d, V (m + 1) = V m + d + 1 := ⟨V (m + 1) - V m - 1, by omega⟩
    have h1 := inner m hm hstart d (by omega)
    rw [hd]
    show strictNext R (st (V m + d + 1)) (strictTrack R st p0 (V m + d)) = R + m + 1
    rw [h1]
    unfold strictNext
    have hemp := (hmv m hm).1
    rw [hd] at hemp
    rw [if_neg (by omega), if_pos ⟨by omega, hemp⟩]
  have hall : ∀ m, m ≤ R → strictTrack R st p0 (V m) = R + m := by
    intro m
    induction m with
    | zero => intro _; rw [h0]; omega
    | succ m ih =>
      intro hm
      rw [next m (by omega) (ih (by omega))]
      omega
  refine ⟨hall, ?_⟩
  have hgo : ∀ m, m ≤ R → ∀ t, V 0 ≤ t → t < V m →
      StrictGo R (st (t + 1)) (strictTrack R st p0 t) := by
    intro m
    induction m with
    | zero => intro _ t h1 h2; omega
    | succ m ih =>
      intro hm t h1 h2
      by_cases ht : t < V m
      · exact ih (by omega) t h1 ht
      · have hval : strictTrack R st p0 t = R + m := by
          have := inner m (by omega) (hall m (by omega)) (t - V m) (by omega)
          rw [show V m + (t - V m) = t by omega] at this
          exact this
        rw [hval]
        intro _ _ hemp
        by_cases ht1 : t + 1 < V (m + 1)
        · exact absurd hemp (hne m (by omega) (t + 1) (by omega) ht1)
        · have he : t + 1 = V (m + 1) := by omega
          by_cases hm1 : m + 1 < R
          · right
            rw [he]
            exact (hmv m (by omega)).2 hm1
          · left
            omega
  exact fun t h1 h2 => hgo R (Nat.le_refl R) t h1 h2

end Glue

/-! ### Physical consequences of the correspondence -/

section Phys

variable {c : Compiled} {n : Nat}

/-- A tracked input makes a target cell non-empty. Consumer: `inputNe`. -/
theorem tokInNe {Ok : Bool → DigitAtom n → Prop} {i : BankRepairDigitInSh} {l : Bool}
    {a : DigitAtom n} (hc : InCorr Ok i (some a)) : cohortTokIn i l ≠ .empty := by
  cases l <;> cases i <;> simp_all [InCorr, cohortTokIn]

/-- A live carry leaves its cell empty when its own edge is drawn. Consumer:
`strictCompletionCyc`. -/
theorem liveVacate {R k : Nat} {s : CohortLane} (hRk : R ≤ k) (hk : k < 2 * R)
    (hl : s.live k = true) : cohortTok R (cohortEdge R s k) k = .empty := by
  by_cases h2 : k + 1 < 2 * R
  · rw [(cohortTokFin R k s hRk h2).1, hl]
    generalize decide (k = R) = b
    generalize s.inp (k + 1) = iy
    generalize s.live (k + 1) = ky
    cases ky <;> cases iy <;> simp [bankRepairDigitFinStep, cohortTokIn]
  · rw [cohortTokTerm R k s (by omega), hl]
    simp [cohortTermStep, cohortTokIn]

/-- The tracked tail atom carries the tail bit of its recorded sample. Consumer: `physTail`. -/
theorem tailBit {R src : Nat} (ring : DirectedRing n) (root : Fin n) (lane : DigitLane)
    (A Af : DigitAudit c n) (hfin : ∀ f, f ∈ A.frames → f ∈ Af.frames)
    (hfo : AuditFrameOrder Af) (s0 : DigitSample c n) (hs0 : DigitRecordedSample Af s0)
    (htl : s0.tail = true) (T : Bool)
    (hok : GhostOk ring root lane src R (InheritedOk lane) A T (.sampled s0.id)) : T = true := by
  rcases hok with ⟨site, slot, h⟩ | ⟨s, hs, hrec, htail, -⟩
  · cases h
  · obtain ⟨f, hf, h1⟩ := hrec
    have hs' : s = s0 := sampleUnique Af hfo s s0 ⟨f, hfin f hf, h1⟩ hs0
      (DigitAtom.sampled.inj hs).symm
    rw [← htail, hs', htl]

end Phys

/-! ### More rows on the coupled chain -/

section Bank2

variable {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
  (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) (root : Fin n) (lane : DigitLane)
  (src R : Nat) (hR : 2 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n)

/-- The site of a drawn pair edge. Consumer: `delExport`, `delRecv`, `inputBack`, `tailRun`,
`sampleStep`. -/
theorem edgeSite (e : Fin n) (k : Nat) (h : cohortEdgeOf root src R e = some k) :
    e = digitSite ring root (src + k) := by
  obtain ⟨jx, hj, rfl⟩ := bankRepairDigitSiteSurj ring root e
  rw [edgeOfSome ring root src R jx k hj h]

include hn hR hsrc hend in
/-- The delimiter-edge export of one coupled letter. Consumer: the tail sweep. -/
theorem delExport
    (z : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (hz : CohortLayout ring hbank root src R z.1) (e : Fin n)
    (hke : cohortEdgeOf root src R e = some (R - 1)) (T : Bool)
    (hD : (cohortProj ring root lane src R (piD z.1.val.1)).out (R - 1) = .D T)
    (hE : (cohortProj ring root lane src R (piD z.1.val.1)).inp R = .E)
    (hL : (cohortProj ring root lane src R (piD z.1.val.1)).live R = false) :
    ∃ ex : DigitExport (compileAdvice (ceilLogTwo n)) n,
      (digitReceiptLane lane (svcAt ring (piD z.1.val.1) z.2 e)).exported = some ex ∧
      ex.operand = (laneCells ring root lane src z.2.current (R - 1)).out.atom ∧
      ex.time = z.2.clock + 1 ∧ ex.lane = lane ∧
      ex.source = digitSite ring root (src + (R - 1)) := by
  obtain ⟨hL', hb0, hbR, hb2R, hbF⟩ := hz
  obtain ⟨-, hroot, hbX, hbY⟩ := bankRepairDigitLeadBankEdge ring hn hbank root z.1 hL' e
  have he := edgeSite ring root src R e (R - 1) hke
  subst he
  obtain ⟨ex, hex, hl, hs, ht⟩ :=
    (delEdgeFacts ring root (piD z.1.val.1) R src hR hend hroot hbR hbF lane z.2 hbX hbY).2 T hD
      hE hL
  exact ⟨ex, hex, delOperand ring root (piD z.1.val.1) R src hR hend hroot hbR hbF lane z.2 hbX
    hbY ex hex, ht, hl, hs⟩

include hn hR hsrc hend in
/-- The terminal receipt of the last pair edge records the live last cell's ledger. Consumer: `strictCompletionCyc`. -/
theorem termLedger
    (z : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (hz : CohortLayout ring hbank root src R z.1) (e : Fin n)
    (hke : cohortEdgeOf root src R e = some (2 * R - 1))
    (U : DigitTerminal (compileAdvice (ceilLogTwo n)) n)
    (hU : (digitReceiptLane lane (svcAt ring (piD z.1.val.1) z.2 e)).terminal = some U) :
    (cohortProj ring root lane src R (piD z.1.val.1)).live (2 * R - 1) = true ∧
      U.ledger = caA ring root lane src z.2 (2 * R - 1) := by
  obtain ⟨hL, hb0, hbR, hb2R, hbF⟩ := hz
  obtain ⟨-, hroot, hbX, hbY⟩ := bankRepairDigitLeadBankEdge ring hn hbank root z.1 hL e
  obtain ⟨jx, hj, rfl⟩ := bankRepairDigitSiteSurj ring root e
  have hrows := tgtRows ring (by omega) root (piD z.1.val.1) R src hR hsrc hend hroot hbR hb2R
    hbF lane z.2 jx hj hbX hbY
  exact (hrows.2.2.2 hke).2.2 U hU

include hn hR hsrc hend in
/-- A recorded sample at the source border: the read slot becomes the tail packet carrying the
fresh sampled atom. Consumer: the start of the tail sweep. -/
theorem sampleStep
    (z : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (hz : CohortLayout ring hbank root src R z.1) (e : Fin n)
    (hke : cohortEdgeOf root src R e = some 0)
    (s : DigitSample (compileAdvice (ceilLogTwo n)) n)
    (hs : (digitReceiptLane lane (svcAt ring (piD z.1.val.1) z.2 e)).sample = some s) :
    (laneCells ring root lane src (bankRepairDigitBoundaryAuditNext ring hbank z e).2.current
        0).out = .packet (some (.sampled ⟨z.2.clock + 1, e, lane⟩)) ∧
      (cohortProj ring root lane src R
        (piD (bankRepairDigitBoundaryAuditNext ring hbank z e).1.val.1)).out 0 = .D true := by
  have hU := sampleU ring (piD z.1.val.1) z.2 e lane s hs
  have he := edgeSite ring root src R e 0 hke
  have h0 : (cohortProj ring root lane src R (piD z.1.val.1)).out 0 = .U := by
    rw [projOut ring root lane src R _ 0 (by omega), ← he]
    exact hU
  have hpipe := (srcRowsBank ring hn hbank root lane src R hR hsrc hend z hz e).2.1 0 hke
    (by omega)
  rw [h0] at hpipe
  refine ⟨(Prod.mk.inj hpipe).1, ?_⟩
  show (cohortProj ring root lane src R (piD (bankRepairNext ring hbank z.1 e).val.1)).out 0 = _
  rw [(cohortBankStep ring hn hbank root lane src R hR hsrc hend z.1 hz e).2, hke]
  show (cohortEdge R _ 0).out 0 = _
  unfold cohortEdge
  rw [if_pos (by omega)]
  simp [cohortUpd, h0, bankRepairDigitPipeStep]

end Bank2


/-! ### Small facts used by the assembly -/

section Small

/-- Equal lists with one appended element: equal prefixes and equal last elements. Consumer:
`carryBack`, `carryCreate`. -/
theorem lastEq {α : Type _} {l l' : List α} {a b : α} (h : l ++ [a] = l' ++ [b]) :
    l = l' ∧ a = b := by
  have h2 := List.append_inj' h rfl
  exact ⟨h2.1, (List.cons.inj h2.2).1⟩

/-- A defined lookup is in range. Consumer: `strictCompletionCyc`. -/
theorem ltOfGet {α : Type _} {l : List α} {t : Nat} {a : α} (h : l[t]? = some a) :
    t < l.length := by
  rcases Nat.lt_or_ge t l.length with h' | h'
  · exact h'
  · rw [List.getElem?_eq_none_iff.mpr h'] at h
    cases h

/-- A delimiter edge that accepts a data packet into an empty carry-free input leaves no tail
packet at the delimiter cell. Consumer: `tailRun` (the tracked cell reaches `R` at the export
letter). -/
theorem delVacate {R k : Nat} {s : CohortLane} (h : k + 1 = R) {T : Bool} (hD : s.out k = .D T)
    (hE : s.inp R = .E) (hL : s.live R = false) :
    cohortTok R (cohortEdge R s k) k ≠ .pkt true := by
  rw [(cohortTokDel R k s h).1, h, hD, hE, hL]
  cases T <;> simp [bankRepairDigitDelStep, cohortTokOut]

/-- The tracked atom of a source cell is its output atom. Consumer: `tailRun`. -/
theorem trackedSrc {c : Compiled} {n : Nat} (ring : DirectedRing n) (root : Fin n)
    (lane : DigitLane) (src R : Nat) (A : DigitAudit c n) (q : Nat) (hq : q < R) :
    tracked ring root lane src R A q = (laneCells ring root lane src A.current q).out.atom := by
  unfold tracked trackedAt
  rw [if_pos hq]

/-- The receipts of a completion, indexed by `Nat`: the terminal with its ledger, the tail
sample with its export, and the ledger's uses with their times. Consumer:
`strictCompletionCyc`. -/
theorem completionData {c : Compiled} {n : Nat} (ring : DirectedRing n) (A : DigitAudit c n)
    (root : Fin n) (src R : Nat) (lane : DigitLane) (cut : Nat) (tm : DigitTerminal c n)
    (hRd : digitSpan c = R) (h : DigitCompletion ring A root src (src + R) lane cut tm) :
    ∃ (L : DigitCarryGhost c n) (s0 : DigitSample c n) (x0 : DigitExport c n)
      (uz : Nat → DigitUse c n),
      DigitRecordedTerminal A tm ∧ tm.lane = lane ∧
      tm.source = digitSite ring root (src + R + (R - 1)) ∧
      tm.ledger = some L ∧ L.inherited = none ∧ L.uses.length = R ∧
      DigitRecordedSample A s0 ∧ s0.id.lane = lane ∧ s0.id.site = digitSite ring root (src + 0) ∧
      s0.tail = true ∧
      DigitRecordedExport A x0 ∧ x0.lane = lane ∧ x0.source = digitSite ring root (src + (R - 1)) ∧
      x0.operand = some (.sampled s0.id) ∧ s0.id.time < x0.time ∧ x0.time < (uz 0).time ∧
      (uz 0).operand = some (.sampled s0.id) ∧
      (∀ m, m < R → L.uses[m]? = some (uz m) ∧ 0 < (uz m).time ∧ (uz m).time < tm.time) ∧
      (∀ m, m + 1 < R → (uz m).time < (uz (m + 1)).time) := by
  subst hRd
  dsimp only [DigitCompletion] at h
  obtain ⟨-, hTrec, hTl, hTsrc, -, -, hpos, L, smp, exs, us, hL, hLi, hLlen, hall, hord, -⟩ := h
  obtain ⟨uz, huz⟩ : ∃ uz : Nat → DigitUse c n, ∀ m (hm : m < digitSpan c), uz m = us ⟨m, hm⟩ :=
    ⟨fun m => if hm : m < digitSpan c then us ⟨m, hm⟩ else us ⟨0, hpos⟩, fun m hm => dif_pos hm⟩
  obtain ⟨h1, h2, h3, -, h5, h6, h7, h8, -, h10, -, -, -, -, h15, -, -, h18, h19, -⟩ :=
    hall ⟨0, hpos⟩
  refine ⟨L, smp ⟨0, hpos⟩, exs ⟨0, hpos⟩, uz, hTrec, hTl, hTsrc, hL, hLi, hLlen, h1, h2, h3,
    by rw [h5]; rfl, h6, h7, h8, h10, h18, by rw [huz 0 hpos]; exact h19,
    by rw [huz 0 hpos]; exact h15, ?_, ?_⟩
  · intro m hm
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, h13, -, -, -, -, -, h19', h20⟩ := hall ⟨m, hm⟩
    rw [huz m hm]
    exact ⟨h13, by omega, h20⟩
  · intro m hm
    rw [huz m (by omega), huz (m + 1) hm]
    exact (hord ⟨m, by omega⟩ ⟨m + 1, hm⟩ (by show m < m + 1; omega)).2

end Small

/-! ### The coupled run from one start -/

section Assembly

variable {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
  (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) (root : Fin n) (lane : DigitLane)
  (src R : Nat) (hR : 2 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n)
  (z0 : BankReferenceState ring hbank) (hz : CohortLayout ring hbank root src R z0)
  (w : List (Fin n))

/-- The clock of a prefix state is its length. Consumer: every row of the assembly. -/
theorem qClock (t : Nat) (ht : t ≤ w.length) :
    (runAt ring hbank (startOf ring hbank z0) w t).2.clock = t := by
  rw [runAtClock ring hbank w _ t ht]
  show 0 + t = t
  omega

/-- The letter at an index inside the word. Consumer: every row of the assembly. -/
theorem qStep (t : Nat) (ht : t < w.length) :
    ∃ e, w[t]? = some e ∧
      runAt ring hbank (startOf ring hbank z0) w (t + 1) =
        bankRepairDigitBoundaryAuditNext ring hbank (runAt ring hbank (startOf ring hbank z0) w t) e ∧
      keAt root src R w t = cohortEdgeOf root src R e := by
  refine ⟨w[t], List.getElem?_eq_getElem ht,
    runAtSucc ring hbank w _ t _ (List.getElem?_eq_getElem ht), ?_⟩
  unfold keAt
  rw [List.getElem?_eq_getElem ht]
  rfl

/-- The lane letter of a known letter. Consumer: `strictCompletionCyc`, `tailRun`. -/
theorem keAtOf {t : Nat} {e : Fin n} (h : w[t]? = some e) :
    keAt root src R w t = cohortEdgeOf root src R e := by
  unfold keAt
  rw [h]
  rfl

/-- The frame a letter prepends. Consumer: `recExport`. -/
theorem frameAtMem (z : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (e : Fin n) :
    frameAt ring hbank z e ∈ (bankRepairDigitBoundaryAuditNext ring hbank z e).2.frames :=
  List.mem_cons.mpr (Or.inl rfl)

/-- An export of the receipt of letter `t` is recorded in the final audit. Consumer:
`inputBack`, `tailRun`. -/
theorem recExport (t : Nat) (ht : t < w.length) (e : Fin n) (he : w[t]? = some e)
    (x : DigitExport (compileAdvice (ceilLogTwo n)) n)
    (hx : (digitReceiptLane x.lane
      (svcAt ring (piD (runAt ring hbank (startOf ring hbank z0) w t).1.val.1)
        (runAt ring hbank (startOf ring hbank z0) w t).2 e)).exported = some x)
    (htime : x.time = t + 1) (hs : x.source = e) :
    DigitRecordedExport
      (w.foldl (bankRepairDigitBoundaryAuditNext ring hbank) (startOf ring hbank z0)).2 x := by
  refine ⟨frameAt ring hbank (runAt ring hbank (startOf ring hbank z0) w t) e,
    runFramesAtEnd ring hbank w _ (t + 1) _ ?_, ?_, hs.symm, hx⟩
  · rw [runAtSucc ring hbank w _ t e he]
    exact frameAtMem ring hbank _ e
  · show (runAt ring hbank (startOf ring hbank z0) w t).2.clock + 1 = x.time
    rw [qClock ring hbank z0 w t (by omega), htime]

include hn hR hsrc hend hz in
/-- Exports on the delimiter edge carrying the same sample are equal (final audit). Consumer:
`strictCompletionCyc`. -/
theorem exportUnique (x y : DigitExport (compileAdvice (ceilLogTwo n)) n) (sid : DigitStamp n)
    (hx : DigitRecordedExport
      (w.foldl (bankRepairDigitBoundaryAuditNext ring hbank) (startOf ring hbank z0)).2 x)
    (hy : DigitRecordedExport
      (w.foldl (bankRepairDigitBoundaryAuditNext ring hbank) (startOf ring hbank z0)).2 y)
    (hox : OnEdge ring root lane src R x) (hoy : OnEdge ring root lane src R y)
    (h1 : x.operand = some (.sampled sid)) (h2 : y.operand = some (.sampled sid)) : x = y := by
  have hc := (runAtCorr ring hn hbank root lane src R hR hsrc hend z0 hz w w.length).2
  rw [runAtLen ring hbank w _ w.length (Nat.le_refl _)] at hc
  exact hc.2.2.2.2.2 x y sid hx hy hox hoy h1 h2

include hn hR hsrc hend hz in
/-- The lane letter moves the lane trace by its edge. Consumer: `tailRun`,
`strictCompletionCyc`. -/
theorem laneEdge (t k : Nat) (hk : keAt root src R w t = some k) :
    laneAt ring hbank root lane src R z0 w (t + 1) =
      cohortEdge R (laneAt ring hbank root lane src R z0 w t) k := by
  rw [laneAtStep ring hn hbank root lane src R hR hsrc hend z0 hz w t, hk]
  rfl

include hn hR hsrc hend hz in
/-- A ledger on a target cell makes the cell live and non-empty. Consumer:
`strictCompletionCyc`. -/
theorem liveOf (t q : Nat) (h1 : R ≤ q) (h2 : q < 2 * R)
    (K : DigitCarryGhost (compileAdvice (ceilLogTwo n)) n)
    (hK : caA ring root lane src (runAt ring hbank (startOf ring hbank z0) w t).2 q = some K) :
    cohortTok R (laneAt ring hbank root lane src R z0 w t) q ≠ .empty ∧
      (laneAt ring hbank root lane src R z0 w t).live q = true := by
  have hc := ((runAtCorr ring hn hbank root lane src R hR hsrc hend z0 hz w t).2.1.2 q h1 h2).2
  have hl : (laneAt ring hbank root lane src R z0 w t).live q = true := by
    unfold laneAt
    rw [hc]
    show (caA ring root lane src _ q).isSome = true
    rw [hK]
    rfl
  refine ⟨?_, hl⟩
  rw [cohortTokTgt _ h1, hl]
  simp [cohortTokIn]

include hn hR hsrc hend hz in
/-- A tracked input on a target cell makes the cell non-empty. Consumer:
`strictCompletionCyc`. -/
theorem inputNe (t q : Nat) (h1 : R ≤ q) (h2 : q < 2 * R) (a : DigitAtom n)
    (ha : inA ring root lane src (runAt ring hbank (startOf ring hbank z0) w t).2 q = some a) :
    cohortTok R (laneAt ring hbank root lane src R z0 w t) q ≠ .empty := by
  have hc := ((runAtCorr ring hn hbank root lane src R hR hsrc hend z0 hz w t).2.1.2 q h1 h2).1
  change InCorr _ _ (inA ring root lane src _ q) at hc
  rw [ha] at hc
  unfold laneAt
  rw [cohortTokTgt _ h1]
  exact tokInNe hc

include hn hR hsrc hend hz in
/-- A source cell whose output ghost is the tail sample holds the physical tail packet.
Consumer: `tailRun`. -/
theorem physTail (s0 : DigitSample (compileAdvice (ceilLogTwo n)) n)
    (hs0 : DigitRecordedSample
      (w.foldl (bankRepairDigitBoundaryAuditNext ring hbank) (startOf ring hbank z0)).2 s0)
    (htl : s0.tail = true) (t p : Nat) (hp : p < R)
    (ho : (laneCells ring root lane src (runAt ring hbank (startOf ring hbank z0) w t).2.current
      p).out = .packet (some (.sampled s0.id))) :
    (laneAt ring hbank root lane src R z0 w t).out p = .D true := by
  have hc := (runAtCorr ring hn hbank root lane src R hR hsrc hend z0 hz w t).2.1
  obtain ⟨T, hT, hok⟩ := outPacketD (hc.1 p hp) ho
  have hfo := (auditFrameOrderWord ring hbank w (startOf ring hbank z0)
    (auditFrameOrderInitial (piD z0.val.1))).1
  have := tailBit ring root lane _ _ (fun f hf => runFramesAtEnd ring hbank w _ t f hf) hfo s0 hs0
    htl T hok
  subst this
  exact hT

include hn hR hsrc hend in
/-- The delimiter-edge export of a coupled letter: its operand is the delimiter cell's output
atom, and the physical edge accepted a data packet into an empty carry-free input. Consumer:
`tailRun`. -/
theorem delRecv (z : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (hzl : CohortLayout ring hbank root src R z.1) (e : Fin n)
    (hke : cohortEdgeOf root src R e = some (R - 1)) (x : DigitExport (compileAdvice (ceilLogTwo n)) n)
    (hx : (digitReceiptLane lane (svcAt ring (piD z.1.val.1) z.2 e)).exported = some x) :
    x.operand = (laneCells ring root lane src z.2.current (R - 1)).out.atom ∧
      ∃ T, (cohortProj ring root lane src R (piD z.1.val.1)).out (R - 1) = .D T ∧
        (cohortProj ring root lane src R (piD z.1.val.1)).inp R = .E ∧
        (cohortProj ring root lane src R (piD z.1.val.1)).live R = false := by
  obtain ⟨hL', hb0, hbR, hb2R, hbF⟩ := hzl
  obtain ⟨-, hroot, hbX, hbY⟩ := bankRepairDigitLeadBankEdge ring hn hbank root z.1 hL' e
  have he := edgeSite ring root src R e (R - 1) hke
  subst he
  have hdel := delEdgeFacts ring root (piD z.1.val.1) R src hR hend hroot hbR hbF lane z.2 hbX hbY
  exact ⟨delOperand ring root (piD z.1.val.1) R src hR hend hroot hbR hbF lane z.2 hbX hbY x hx,
    hdel.1 x hx⟩

include hn hR hsrc hend hz in
/-- Ledger uses on target cells are stamped no later than the prefix. Consumer:
`carryCreate`. -/
theorem carryTB : ∀ t, t ≤ w.length → ∀ q (K : DigitCarryGhost (compileAdvice (ceilLogTwo n)) n),
    R ≤ q → q < 2 * R →
    caA ring root lane src (runAt ring hbank (startOf ring hbank z0) w t).2 q = some K →
    ∀ u, u ∈ K.uses → u.time ≤ t := by
  intro t
  induction t with
  | zero =>
    intro _ q K _ _ hK u hu
    exfalso
    change (laneGhost lane (digitGhostInitial (piD z0.val.1)
      (digitSite ring root (src + q)))).carry = some K at hK
    rw [laneGhostInitial] at hK
    simp only [DigitLaneGhost.initial] at hK
    split at hK
    · rw [← Option.some.inj hK] at hu
      exact absurd hu List.not_mem_nil
    · cases hK
  | succ t ih =>
    intro ht q K hRq hq hK u hu
    obtain ⟨e, -, hstep, -⟩ := qStep ring hbank root src R z0 w t (by omega)
    rw [hstep] at hK
    have hcor := runAtCorr ring hn hbank root lane src R hR hsrc hend z0 hz w t
    have hclk := qClock ring hbank z0 w t (by omega)
    rcases carryOrigin ring hn hbank root lane src R hR hsrc hend (InheritedOk lane) _ hcor.1
      hcor.2.1 e q hRq hq K hK with h | ⟨-, -, u', hu1, -, rfl⟩ | ⟨hRq', -, L, u', hL, hu1, rfl⟩
    · exact Nat.le_succ_of_le (ih (by omega) q K hRq hq h u hu)
    · simp at hu
      subst hu
      omega
    · rcases List.mem_append.mp hu with hu | hu
      · exact Nat.le_succ_of_le (ih (by omega) (q - 1) L (by omega) (by omega) hL u hu)
      · simp at hu
        subst hu
        omega

include hn hR hsrc hend hz in
/-- **Backward persistence of a ledger**: a ledger whose last use has time `u` has sat at its
cell since `u` (a letter that creates or extends a ledger stamps its own time last). Consumer:
`carryChain`. -/
theorem carryBack (t' q : Nat) (ht' : t' ≤ w.length) (hRq : R ≤ q) (hq : q < 2 * R)
    (K : DigitCarryGhost (compileAdvice (ceilLogTwo n)) n)
    (l : List (DigitUse (compileAdvice (ceilLogTwo n)) n))
    (u : DigitUse (compileAdvice (ceilLogTwo n)) n) (hKu : K.uses = l ++ [u])
    (hK : caA ring root lane src (runAt ring hbank (startOf ring hbank z0) w t').2 q = some K) :
    ∀ d, u.time + d ≤ t' →
      caA ring root lane src (runAt ring hbank (startOf ring hbank z0) w (t' - d)).2 q =
        some K := by
  intro d
  induction d with
  | zero => intro _; exact hK
  | succ d ih =>
    intro hd
    have h1 := ih (by omega)
    rw [show t' - d = t' - (d + 1) + 1 by omega] at h1
    obtain ⟨e, -, hstep, -⟩ := qStep ring hbank root src R z0 w (t' - (d + 1)) (by omega)
    rw [hstep] at h1
    have hcor := runAtCorr ring hn hbank root lane src R hR hsrc hend z0 hz w (t' - (d + 1))
    have hclk := qClock ring hbank z0 w (t' - (d + 1)) (by omega)
    rcases carryOrigin ring hn hbank root lane src R hR hsrc hend (InheritedOk lane) _ hcor.1
      hcor.2.1 e q hRq hq K h1 with h | ⟨-, -, u', hu1, -, hK'⟩ | ⟨-, -, L, u', -, hu1, hK'⟩
    · exact h
    · exfalso
      have h3 : [] ++ [u'] = l ++ [u] := by rw [← hKu]; subst hK'; rfl
      have h5 := (lastEq h3).2
      subst h5
      omega
    · exfalso
      have h3 : L.uses ++ [u'] = l ++ [u] := by rw [← hKu]; subst hK'; rfl
      have h5 := (lastEq h3).2
      subst h5
      omega

include hn hR hsrc hend hz in
/-- **Creation of a ledger** at the time of its last use: launched at `R` by the letter before
(reading the input of `R`), or extended from the cell below. Consumer: `carryChain`. -/
theorem carryCreate (q : Nat) (hRq : R ≤ q) (hq : q < 2 * R)
    (K : DigitCarryGhost (compileAdvice (ceilLogTwo n)) n)
    (l : List (DigitUse (compileAdvice (ceilLogTwo n)) n))
    (u : DigitUse (compileAdvice (ceilLogTwo n)) n) (hKu : K.uses = l ++ [u]) (hu0 : 0 < u.time)
    (hul : u.time ≤ w.length)
    (hK : caA ring root lane src (runAt ring hbank (startOf ring hbank z0) w u.time).2 q = some K) :
    (q = R ∧ keAt root src R w (u.time - 1) = some R ∧ l = [] ∧ K.inherited = none ∧
      u.operand =
        inA ring root lane src (runAt ring hbank (startOf ring hbank z0) w (u.time - 1)).2 R) ∨
    (R < q ∧ keAt root src R w (u.time - 1) = some (q - 1) ∧
      caA ring root lane src (runAt ring hbank (startOf ring hbank z0) w (u.time - 1)).2 (q - 1) =
        some ⟨K.inherited, l⟩) := by
  have e1 : u.time = u.time - 1 + 1 := by omega
  rw [e1] at hK
  obtain ⟨e, -, hstep, hke⟩ := qStep ring hbank root src R z0 w (u.time - 1) (by omega)
  rw [hstep] at hK
  rw [hke]
  have hcor := runAtCorr ring hn hbank root lane src R hR hsrc hend z0 hz w (u.time - 1)
  have hclk := qClock ring hbank z0 w (u.time - 1) (by omega)
  rcases carryOrigin ring hn hbank root lane src R hR hsrc hend (InheritedOk lane) _ hcor.1
    hcor.2.1 e q hRq hq K hK with h | ⟨hqR, hkR, u', hu1, hu2, hK'⟩ | ⟨hRq', hk1, L, u', hL, hu1, hK'⟩
  · exfalso
    have := carryTB ring hn hbank root lane src R hR hsrc hend z0 hz w (u.time - 1) (by omega) q K
      hRq hq h u (by rw [hKu]; simp)
    omega
  · left
    have h3 : [] ++ [u'] = l ++ [u] := by rw [← hKu]; subst hK'; rfl
    obtain ⟨h4, h5⟩ := lastEq h3
    subst h5
    exact ⟨hqR, hkR, h4.symm, by subst hK'; rfl, hu2⟩
  · right
    have h3 : L.uses ++ [u'] = l ++ [u] := by rw [← hKu]; subst hK'; rfl
    obtain ⟨h4, -⟩ := lastEq h3
    subst hK' h4
    exact ⟨hRq', hk1, hL⟩

include hn hR hsrc hend hz in
/-- **The strict carry chain (step 4c, carry half).** From the recorded terminal ledger (`R`
uses, no inherited carry) back to the launch: the ledger of the first `m + 1` uses sits at
`R + m` from use `m` until the letter before use `m + 1` (the terminal for `m = R - 1`), that
letter draws the edge `R + m`, and use `0` read the input of cell `R` one letter before it.
Consumer: `strictCompletionCyc`. -/
theorem carryChain (Lu : List (DigitUse (compileAdvice (ceilLogTwo n)) n))
    (uz : Nat → DigitUse (compileAdvice (ceilLogTwo n)) n) (T : Nat)
    (hlen : Lu.length = R) (hLu : ∀ m, m < R → Lu[m]? = some (uz m))
    (hpos : ∀ m, m < R → 0 < (uz m).time) (hbelow : ∀ m, m < R → (uz m).time < T)
    (hinc : ∀ m, m + 1 < R → (uz m).time < (uz (m + 1)).time) (hT : T ≤ w.length)
    (hterm : caA ring root lane src (runAt ring hbank (startOf ring hbank z0) w (T - 1)).2
      (2 * R - 1) = some ⟨none, Lu⟩)
    (hkT : keAt root src R w (T - 1) = some (2 * R - 1)) :
    (∀ m, m < R → ∀ t, (uz m).time ≤ t → t + 1 ≤ (if m + 1 < R then (uz (m + 1)).time else T) →
      caA ring root lane src (runAt ring hbank (startOf ring hbank z0) w t).2 (R + m) =
        some ⟨none, Lu.take (m + 1)⟩) ∧
    (∀ m, m < R →
      keAt root src R w ((if m + 1 < R then (uz (m + 1)).time else T) - 1) = some (R + m)) ∧
    (uz 0).operand =
      inA ring root lane src (runAt ring hbank (startOf ring hbank z0) w ((uz 0).time - 1)).2 R := by
  have htake : ∀ m, m < R → Lu.take (m + 1) = Lu.take m ++ [uz m] := by
    intro m hm
    rw [List.take_add_one, hLu m hm]
    rfl
  have hwin : ∀ m, m < R → (uz m).time < (if m + 1 < R then (uz (m + 1)).time else T) ∧
      (if m + 1 < R then (uz (m + 1)).time else T) ≤ T := by
    intro m hm
    split
    · exact ⟨hinc m (by assumption), Nat.le_of_lt (hbelow (m + 1) (by assumption))⟩
    · exact ⟨hbelow m hm, Nat.le_refl T⟩
  have key : ∀ d m, m + d + 1 = R →
      caA ring root lane src (runAt ring hbank (startOf ring hbank z0) w
        ((if m + 1 < R then (uz (m + 1)).time else T) - 1)).2 (R + m) =
          some ⟨none, Lu.take (m + 1)⟩ ∧
      keAt root src R w ((if m + 1 < R then (uz (m + 1)).time else T) - 1) = some (R + m) := by
    intro d
    induction d with
    | zero =>
      intro m hm
      rw [if_neg (by omega), show R + m = 2 * R - 1 by omega, List.take_of_length_le (by omega)]
      exact ⟨hterm, hkT⟩
    | succ d ih =>
      intro m hm
      obtain ⟨h1, -⟩ := ih (m + 1) (by omega)
      obtain ⟨hw1, hw2⟩ := hwin (m + 1) (by omega)
      generalize (if m + 1 + 1 < R then (uz (m + 1 + 1)).time else T) = W at h1 hw1 hw2
      have hb := carryBack ring hn hbank root lane src R hR hsrc hend z0 hz w (W - 1) (R + (m + 1))
        (by omega) (by omega) (by omega) ⟨none, Lu.take (m + 1 + 1)⟩ (Lu.take (m + 1)) (uz (m + 1))
        (htake (m + 1) (by omega)) h1 (W - 1 - (uz (m + 1)).time) (by omega)
      rw [show W - 1 - (W - 1 - (uz (m + 1)).time) = (uz (m + 1)).time by omega] at hb
      rw [if_pos (by omega)]
      rcases carryCreate ring hn hbank root lane src R hR hsrc hend z0 hz w (R + (m + 1))
        (by omega) (by omega) ⟨none, Lu.take (m + 1 + 1)⟩ (Lu.take (m + 1)) (uz (m + 1))
        (htake (m + 1) (by omega)) (hpos (m + 1) (by omega)) (by omega) hb with
        ⟨hq, -⟩ | ⟨-, hk, hc⟩
      · omega
      · rw [show R + (m + 1) - 1 = R + m by omega] at hk hc
        exact ⟨hc, hk⟩
  refine ⟨?_, fun m hm => (key (R - 1 - m) m (by omega)).2, ?_⟩
  · intro m hm t h1 h2
    obtain ⟨hc, -⟩ := key (R - 1 - m) m (by omega)
    obtain ⟨hw1, hw2⟩ := hwin m hm
    generalize (if m + 1 < R then (uz (m + 1)).time else T) = W at hc hw1 hw2 h2
    have hb := carryBack ring hn hbank root lane src R hR hsrc hend z0 hz w (W - 1) (R + m)
      (by omega) (by omega) (by omega) ⟨none, Lu.take (m + 1)⟩ (Lu.take m) (uz m) (htake m hm) hc
      (W - 1 - t) (by omega)
    rwa [show W - 1 - (W - 1 - t) = t by omega] at hb
  · obtain ⟨hc, -⟩ := key (R - 1) 0 (by omega)
    obtain ⟨hw1, hw2⟩ := hwin 0 (by omega)
    generalize (if 0 + 1 < R then (uz (0 + 1)).time else T) = W at hc hw1 hw2
    have hb := carryBack ring hn hbank root lane src R hR hsrc hend z0 hz w (W - 1) (R + 0)
      (by omega) (by omega) (by omega) ⟨none, Lu.take (0 + 1)⟩ (Lu.take 0) (uz 0)
      (htake 0 (by omega)) hc (W - 1 - (uz 0).time) (by omega)
    rw [show W - 1 - (W - 1 - (uz 0).time) = (uz 0).time by omega] at hb
    rcases carryCreate ring hn hbank root lane src R hR hsrc hend z0 hz w (R + 0) (by omega)
      (by omega) ⟨none, Lu.take (0 + 1)⟩ (Lu.take 0) (uz 0) (htake 0 (by omega)) (hpos 0 (by omega))
      (by omega) hb with ⟨-, -, -, -, hop⟩ | ⟨hq, -⟩
    · exact hop
    · omega

include hn hR hsrc hend hz in
/-- **The strict input (step 4c, input half).** The tail atom stays the input of cell `R`
from its export until the letter of use `0`: the only letter that delivers it is its own
delimiter export, which is unique. Consumer: `strictCompletionCyc`. -/
theorem inputBack (sid : DigitStamp n) (e0 u0 : Nat) (hu0 : u0 ≤ w.length) (he0 : e0 < u0)
    (hin : inA ring root lane src (runAt ring hbank (startOf ring hbank z0) w (u0 - 1)).2 R =
      some (.sampled sid))
    (huniq : ∀ x : DigitExport (compileAdvice (ceilLogTwo n)) n,
      DigitRecordedExport
        (w.foldl (bankRepairDigitBoundaryAuditNext ring hbank) (startOf ring hbank z0)).2 x →
      OnEdge ring root lane src R x → x.operand = some (.sampled sid) → x.time = e0) :
    ∀ t, e0 ≤ t → t ≤ u0 - 1 →
      inA ring root lane src (runAt ring hbank (startOf ring hbank z0) w t).2 R =
        some (.sampled sid) := by
  have key : ∀ d, e0 + d ≤ u0 - 1 →
      inA ring root lane src (runAt ring hbank (startOf ring hbank z0) w (u0 - 1 - d)).2 R =
        some (.sampled sid) := by
    intro d
    induction d with
    | zero => intro _; exact hin
    | succ d ih =>
      intro hd
      have h1 := ih (by omega)
      rw [show u0 - 1 - d = u0 - 1 - (d + 1) + 1 by omega] at h1
      obtain ⟨e, he, hstep, -⟩ := qStep ring hbank root src R z0 w (u0 - 1 - (d + 1)) (by omega)
      rw [hstep] at h1
      have hzt := (runAtCorr ring hn hbank root lane src R hR hsrc hend z0 hz w
        (u0 - 1 - (d + 1))).1
      rcases inOrigin ring hn hbank root lane src R hR hsrc hend _ hzt e _ h1 with
        h | ⟨hkR, x, hx, hxo, hxt, hxl, hxs⟩
      · exact h
      · exfalso
        have hrec := recExport ring hbank z0 w (u0 - 1 - (d + 1)) (by omega) e he x
          (by rw [hxl]; exact hx)
          (by rw [hxt, qClock ring hbank z0 w (u0 - 1 - (d + 1)) (by omega)]) hxs
        have hon : OnEdge ring root lane src R x :=
          ⟨hxl, by rw [hxs]; exact edgeSite ring root src R e (R - 1) hkR⟩
        have := huniq x hrec hon hxo
        rw [hxt, qClock ring hbank z0 w (u0 - 1 - (d + 1)) (by omega)] at this
        omega
  intro t h1 h2
  have := key (u0 - 1 - t) (by omega)
  rwa [show u0 - 1 - (u0 - 1 - t) = t by omega] at this

include hn hR hsrc hend hz in
/-- **The tail sweep (step 4b).** From the sample letter of the tail atom `a₀` to its export
letter, the tracked cell of the lane trace started at the sample (`p₀ = 0`) holds the output
ghost `a₀` and stays below `R` (a delimiter export of `a₀` before its recorded one would be a
second export of the same sample); at the export letter the tracked cell is the delimiter cell
and moves to `R`. Consumer: `strictCompletionCyc`. -/
theorem tailRun (st : Nat → CohortLane) (ts : Nat)
    (hst : ∀ r, st r = laneAt ring hbank root lane src R z0 w (ts + 1 + r))
    (s0 : DigitSample (compileAdvice (ceilLogTwo n)) n)
    (hs0 : DigitRecordedSample
      (w.foldl (bankRepairDigitBoundaryAuditNext ring hbank) (startOf ring hbank z0)).2 s0)
    (htl : s0.tail = true) (hsl : s0.id.lane = lane) (es : Fin n) (hes : w[ts]? = some es)
    (hσ : s0.id.time = ts + 1) (hsite : es = digitSite ring root (src + 0))
    (hsamp : (digitReceiptLane lane
      (svcAt ring (piD (runAt ring hbank (startOf ring hbank z0) w ts).1.val.1)
        (runAt ring hbank (startOf ring hbank z0) w ts).2 es)).sample = some s0)
    (hsite' : s0.id.site = es) (x0 : DigitExport (compileAdvice (ceilLogTwo n)) n) (tx : Nat)
    (ex : Fin n) (hexw : w[tx]? = some ex) (hx0t : x0.time = tx + 1)
    (hexe : ex = digitSite ring root (src + (R - 1)))
    (hxr : (digitReceiptLane lane
      (svcAt ring (piD (runAt ring hbank (startOf ring hbank z0) w tx).1.val.1)
        (runAt ring hbank (startOf ring hbank z0) w tx).2 ex)).exported = some x0)
    (hxo : x0.operand = some (.sampled s0.id))
    (huniq : ∀ x : DigitExport (compileAdvice (ceilLogTwo n)) n,
      DigitRecordedExport
        (w.foldl (bankRepairDigitBoundaryAuditNext ring hbank) (startOf ring hbank z0)).2 x →
      OnEdge ring root lane src R x → x.operand = some (.sampled s0.id) → x.time = x0.time)
    (hlt : ts < tx) (htx : tx < w.length) :
    cohortTok R (st 0) 0 = .pkt true ∧ (∀ r, ts + 1 + r ≤ tx → strictTrack R st 0 r < R) ∧
      strictTrack R st 0 (tx - ts) = R := by
  have hzs := (runAtCorr ring hn hbank root lane src R hR hsrc hend z0 hz w ts).1
  have hke0 : cohortEdgeOf root src R es = some 0 := by
    rw [hsite]
    exact cohortEdgeOfSite ring root src R hend 0 (by omega)
  obtain ⟨hg0, hp0⟩ := sampleStep ring hn hbank root lane src R hR hsrc hend _ hzs es hke0 s0 hsamp
  have hstep0 := runAtSucc ring hbank w (startOf ring hbank z0) ts es hes
  have hid : s0.id = ⟨ts + 1, es, lane⟩ := by rw [← hσ, ← hsite', ← hsl]
  rw [qClock ring hbank z0 w ts (by omega), ← hid, ← hstep0] at hg0
  rw [← hstep0] at hp0
  have htok0 : cohortTok R (st 0) 0 = .pkt true := by
    rw [hst, cohortTokSrc _ (by omega : 0 < R)]
    show cohortTokOut ((cohortProj ring root lane src R
      (piD (runAt ring hbank (startOf ring hbank z0) w (ts + 1)).1.val.1)).out 0) = _
    rw [hp0]
    rfl
  have J : ∀ r, ts + 1 + r ≤ tx → strictTrack R st 0 r < R ∧
      (laneCells ring root lane src (runAt ring hbank (startOf ring hbank z0) w (ts + 1 + r)).2.current
        (strictTrack R st 0 r)).out = .packet (some (.sampled s0.id)) := by
    intro r
    induction r with
    | zero => intro _; exact ⟨by show 0 < R; omega, hg0⟩
    | succ r ih =>
      intro hr
      obtain ⟨hp, ho⟩ := ih (by omega)
      have ht : ts + 1 + r < w.length := by omega
      obtain ⟨e, he, hstep, hke⟩ := qStep ring hbank root src R z0 w (ts + 1 + r) ht
      have hzt := (runAtCorr ring hn hbank root lane src R hR hsrc hend z0 hz w (ts + 1 + r)).1
      have hph := physTail ring hn hbank root lane src R hR hsrc hend z0 hz w s0 hs0 htl
        (ts + 1 + r) _ hp ho
      have hrows := srcRowsBank ring hn hbank root lane src R hR hsrc hend _ hzt e
      rw [← hstep] at hrows
      have hst1 : st (r + 1) = cohortLaneStep R (st r) (cohortEdgeOf root src R e) := by
        rw [hst, hst, ← hke]
        exact laneAtStep ring hn hbank root lane src R hR hsrc hend z0 hz w (ts + 1 + r)
      have htr : strictTrack R st 0 (r + 1) = strictNext R (st (r + 1)) (strictTrack R st 0 r) :=
        rfl
      rcases srcStep hrows hp ho hph with ⟨ho', htok⟩ | ⟨hp1, ho', htok⟩ | ⟨hp1, hkR, hE, hL⟩
      · have htok' : cohortTok R (st (r + 1)) (strictTrack R st 0 r) = .pkt true := by
          rw [hst1, hst]
          exact htok
        have e1 : strictTrack R st 0 (r + 1) = strictTrack R st 0 r := by
          rw [htr]
          unfold strictNext
          rw [if_pos hp, if_pos htok']
        rw [e1]
        exact ⟨hp, ho'⟩
      · have htok' : cohortTok R (st (r + 1)) (strictTrack R st 0 r) = .other := by
          rw [hst1, hst]
          exact htok
        have e1 : strictTrack R st 0 (r + 1) = strictTrack R st 0 r + 1 := by
          rw [htr]
          unfold strictNext
          rw [if_pos hp, if_neg (by rw [htok']; intro h; cases h)]
        rw [e1]
        exact ⟨hp1, ho'⟩
      · exfalso
        have hD : (cohortProj ring root lane src R
            (piD (runAt ring hbank (startOf ring hbank z0) w (ts + 1 + r)).1.val.1)).out (R - 1) =
              .D true := by
          rw [show R - 1 = strictTrack R st 0 r by omega]
          exact hph
        obtain ⟨x, hx, hxo', hxt, hxl, hxs⟩ :=
          delExport ring hn hbank root lane src R hR hsrc hend _ hzt e hkR true hD hE hL
        have hrec := recExport ring hbank z0 w (ts + 1 + r) ht e he x (by rw [hxl]; exact hx)
          (by rw [hxt, qClock ring hbank z0 w (ts + 1 + r) (by omega)])
          (by rw [hxs]; exact (edgeSite ring root src R e (R - 1) hkR).symm)
        have hop : x.operand = some (.sampled s0.id) := by
          rw [hxo', show R - 1 = strictTrack R st 0 r by omega, ho]
          rfl
        have := huniq x hrec ⟨hxl, hxs⟩ hop
        rw [hxt, qClock ring hbank z0 w (ts + 1 + r) (by omega), hx0t] at this
        omega
  refine ⟨htok0, fun r hr => (J r hr).1, ?_⟩
  obtain ⟨hp, ho⟩ := J (tx - ts - 1) (by omega)
  rw [show ts + 1 + (tx - ts - 1) = tx by omega] at ho
  have hzx := runAtCorr ring hn hbank root lane src R hR hsrc hend z0 hz w tx
  have hkx : cohortEdgeOf root src R ex = some (R - 1) := by
    rw [hexe]
    exact cohortEdgeOfSite ring root src R hend (R - 1) (by omega)
  obtain ⟨hxo', T, hD, hE, hL⟩ :=
    delRecv ring hn hbank root lane src R hR hsrc hend _ hzx.1 ex hkx x0 hxr
  have hpR : strictTrack R st 0 (tx - ts - 1) = R - 1 := by
    apply hzx.2.2.1 _ _ s0.id
    · rw [trackedSrc ring root lane src R _ _ hp, ho]
      rfl
    · rw [trackedSrc ring root lane src R _ _ (by omega), ← hxo', hxo]
  rw [show tx - ts = tx - ts - 1 + 1 by omega]
  show strictNext R (st (tx - ts - 1 + 1)) (strictTrack R st 0 (tx - ts - 1)) = R
  have hst2 : st (tx - ts - 1 + 1) =
      cohortEdge R (laneAt ring hbank root lane src R z0 w tx) (R - 1) := by
    rw [hst, show ts + 1 + (tx - ts - 1 + 1) = tx + 1 by omega]
    exact laneEdge ring hn hbank root lane src R hR hsrc hend z0 hz w tx (R - 1)
      (by rw [keAtOf root src R w hexw]; exact hkx)
  have hv : cohortTok R (cohortEdge R (laneAt ring hbank root lane src R z0 w tx) (R - 1)) (R - 1) ≠
      .pkt true := delVacate (show R - 1 + 1 = R by omega) hD hE hL
  unfold strictNext
  rw [hpR, if_pos (by omega : R - 1 < R), hst2, if_neg hv]
  omega

include hn hR hsrc hend hz in
/-- **Group 6, step 4: a recorded strict completion puts the lane in the cycle class.**
Along the coupled BANK x audit run of any word from a layout state `z0` (audit started at
`digitAuditInitial`), if the final audit records a strict completion of the pair (`src`,
`src + R`) on `lane`, then the masked lane of the final state is in the cycle class
`CohortCyc R`. The tracked phase of `L3.DigitEntryPhase` is followed from the tail sample: the
tail sweep (`tailRun`) up to its recorded export, then the bottom of the strict region
(`bottomGlue`) with the input (`inputBack`) and the strict ledger (`carryChain`) up to the
recorded terminal, then the cycle class to the end of the word. Consumer: the entry stage
`StructuralCut → EntryCut 0` (group 6, `BlockEntry.PairPin`) and the clean-route digit
boundary stage (`BankRepairDigitClean`, entrance `BankPostInheritedGrantDrain ∧
BankCleanRFold`), each at a layout state where the audit restarts. -/
theorem strictCompletionCyc (hRd : digitSpan (compileAdvice (ceilLogTwo n)) = R) (cut : Nat)
    (tm : DigitTerminal (compileAdvice (ceilLogTwo n)) n)
    (hcomp : DigitCompletion ring (w.foldl (bankRepairDigitBoundaryAuditNext ring hbank)
      (startOf ring hbank z0)).2 root src (src + R) lane cut tm) :
    CohortCyc R (cohortProj ring root lane src R
      (piD (w.foldl (bankRepairDigitBoundaryAuditNext ring hbank) (startOf ring hbank z0)).1.val.1)) := by
  obtain ⟨L, s0, x0, uz, hTrec, hTl, hTsrc, hTL, hLi, hLlen, hs0, hsl, hss, htl, hx0, hxl, hxs,
    hxo, hsx, hxu, huo, huses, hinc⟩ := completionData ring _ root src R lane cut tm hRd hcomp
  have h0 : (startOf ring hbank z0).2.frames = [] := rfl
  have hc0 : (startOf ring hbank z0).2.clock = 0 := rfl
  obtain ⟨fs, hfs, hfst, hfse, hfsr, -⟩ := id hs0
  obtain ⟨ts, es, hes, hts, rfl⟩ := frameTime ring hbank w _ h0 hc0 fs hfs
  obtain ⟨fx, hfx, hfxt, hfxe, hfxr⟩ := id hx0
  obtain ⟨tx, ex, hexw, htxt, rfl⟩ := frameTime ring hbank w _ h0 hc0 fx hfx
  obtain ⟨fT, hfT, hfTt, hfTe, hfTr⟩ := id hTrec
  obtain ⟨tT, eT, heT, htTt, rfl⟩ := frameTime ring hbank w _ h0 hc0 fT hfT
  have hσ : s0.id.time = ts + 1 := hfst.symm.trans hts
  have hx0t : x0.time = tx + 1 := hfxt.symm.trans htxt
  have hTt : tm.time = tT + 1 := hfTt.symm.trans htTt
  have hts' := ltOfGet hes
  have htx' := ltOfGet hexw
  have htT' := ltOfGet heT
  have huniq : ∀ x : DigitExport (compileAdvice (ceilLogTwo n)) n,
      DigitRecordedExport
        (w.foldl (bankRepairDigitBoundaryAuditNext ring hbank) (startOf ring hbank z0)).2 x →
      OnEdge ring root lane src R x → x.operand = some (.sampled s0.id) → x.time = x0.time :=
    fun x hx hon hop => by
      rw [exportUnique ring hn hbank root lane src R hR hsrc hend z0 hz w x x0 s0.id hx hx0 hon
        ⟨hxl, hxs⟩ hop hxo]
  have hsite' : s0.id.site = es := hfse.symm
  have hsamp : (digitReceiptLane lane
      (svcAt ring (piD (runAt ring hbank (startOf ring hbank z0) w ts).1.val.1)
        (runAt ring hbank (startOf ring hbank z0) w ts).2 es)).sample = some s0 := by
    rw [← hsl]
    exact hfsr
  have hxr : (digitReceiptLane lane
      (svcAt ring (piD (runAt ring hbank (startOf ring hbank z0) w tx).1.val.1)
        (runAt ring hbank (startOf ring hbank z0) w tx).2 ex)).exported = some x0 := by
    rw [← hxl]
    exact hfxr
  have hTr : (digitReceiptLane lane
      (svcAt ring (piD (runAt ring hbank (startOf ring hbank z0) w tT).1.val.1)
        (runAt ring hbank (startOf ring hbank z0) w tT).2 eT)).terminal = some tm := by
    rw [← hTl]
    exact hfTr
  have hexe : ex = digitSite ring root (src + (R - 1)) := hfxe.trans hxs
  have heTe : eT = digitSite ring root (src + R + (R - 1)) := hfTe.trans hTsrc
  -- the lane trace from the sample
  obtain ⟨st, hst⟩ : ∃ st : Nat → CohortLane,
      ∀ r, st r = laneAt ring hbank root lane src R z0 w (ts + 1 + r) := ⟨_, fun _ => rfl⟩
  obtain ⟨htok0, hbefore, hV0⟩ := tailRun ring hn hbank root lane src R hR hsrc hend z0 hz w st
    ts hst s0 hs0 htl hsl es hes hσ (hsite'.symm.trans hss) hsamp hsite' x0 tx ex hexw hx0t hexe
    hxr hxo huniq (by omega) htx'
  -- the terminal ledger
  have hkT : cohortEdgeOf root src R eT = some (2 * R - 1) := by
    rw [heTe, show src + R + (R - 1) = src + (2 * R - 1) by omega]
    exact cohortEdgeOfSite ring root src R hend (2 * R - 1) (by omega)
  obtain ⟨-, hled⟩ := termLedger ring hn hbank root lane src R hR hsrc hend _
    (runAtCorr ring hn hbank root lane src R hR hsrc hend z0 hz w tT).1 eT hkT tm hTr
  have hLe : L = ⟨none, L.uses⟩ := by
    cases L
    simp only at hLi
    subst hLi
    rfl
  have hterm : caA ring root lane src (runAt ring hbank (startOf ring hbank z0) w (tm.time - 1)).2
      (2 * R - 1) = some ⟨none, L.uses⟩ := by
    rw [show tm.time - 1 = tT by omega, ← hled, hTL, ← hLe]
  have hkT' : keAt root src R w (tm.time - 1) = some (2 * R - 1) := by
    rw [show tm.time - 1 = tT by omega, keAtOf root src R w heT]
    exact hkT
  obtain ⟨hcar, hkey, hop0⟩ := carryChain ring hn hbank root lane src R hR hsrc hend z0 hz w
    L.uses uz tm.time hLlen (fun m hm => (huses m hm).1) (fun m hm => (huses m hm).2.1)
    (fun m hm => (huses m hm).2.2) hinc (by omega) hterm hkT'
  have hu0T := (huses 0 (by omega)).2.2
  have hinp := inputBack ring hn hbank root lane src R hR hsrc hend z0 hz w s0.id x0.time
    (uz 0).time (by omega) hxu (by rw [← hop0, huo]) huniq
  -- the window ends
  obtain ⟨Va, hVa⟩ : ∃ Va : Nat → Nat, ∀ m,
      Va m = if m = 0 then x0.time else if m < R then (uz m).time else tm.time := ⟨_, fun _ => rfl⟩
  have hVs : ∀ m, m < R → Va (m + 1) = if m + 1 < R then (uz (m + 1)).time else tm.time := by
    intro m _
    rw [hVa, if_neg (by omega)]
  have hVlo : ∀ m, m < R → (uz m).time < Va (m + 1) ∧ Va (m + 1) ≤ tm.time := by
    intro m hm
    rw [hVs m hm]
    split
    · exact ⟨hinc m (by assumption), Nat.le_of_lt (huses (m + 1) (by assumption)).2.2⟩
    · exact ⟨(huses m hm).2.2, Nat.le_refl _⟩
  have hV0e : Va 0 = x0.time := by rw [hVa, if_pos rfl]
  have hVm : ∀ m, 0 < m → m < R → Va m = (uz m).time := by
    intro m h1 h2
    rw [hVa, if_neg (by omega), if_pos h2]
  have hVR : Va R = tm.time := by rw [hVa, if_neg (by omega), if_neg (by omega)]
  have hVinc : ∀ m, m < R → Va m < Va (m + 1) := by
    intro m hm
    by_cases h : m = 0
    · subst h
      rw [hV0e]
      have := (hVlo 0 hm).1
      omega
    · rw [hVm m (by omega) hm]
      exact (hVlo m hm).1
  have hVge : ∀ m, m ≤ R → x0.time ≤ Va m := by
    intro m
    induction m with
    | zero => intro _; rw [hV0e]; exact Nat.le_refl _
    | succ m ih =>
      intro hm
      have := ih (by omega)
      have := hVinc m (by omega)
      omega
  obtain ⟨V, hV⟩ : ∃ V : Nat → Nat, ∀ m, V m = Va m - (ts + 1) := ⟨_, fun _ => rfl⟩
  have hstAbs : ∀ t, ts + 1 ≤ t → st (t - (ts + 1)) = laneAt ring hbank root lane src R z0 w t := by
    intro t h
    rw [hst, show ts + 1 + (t - (ts + 1)) = t by omega]
  -- the bottom of the strict region
  have h0' : strictTrack R st 0 (V 0) = R := by
    rw [hV, hV0e, hx0t, show tx + 1 - (ts + 1) = tx - ts by omega]
    exact hV0
  have hVV : ∀ m, m < R → V m < V (m + 1) := by
    intro m hm
    rw [hV, hV]
    have := hVinc m hm
    have := hVge m (by omega)
    omega
  have hne : ∀ m, m < R → ∀ t, V m < t → t < V (m + 1) →
      cohortTok R (st t) (R + m) ≠ .empty := by
    intro m hm t h1 h2
    rw [hV] at h1 h2
    have hge := hVge m (by omega)
    rw [hst]
    by_cases hm0 : m = 0
    · subst hm0
      rw [hV0e] at h1
      by_cases hu : ts + 1 + t < (uz 0).time
      · exact inputNe ring hn hbank root lane src R hR hsrc hend z0 hz w (ts + 1 + t) (R + 0)
          (by omega) (by omega) _ (hinp (ts + 1 + t) (by omega) (by omega))
      · have hc := hcar 0 hm (ts + 1 + t) (by omega) (by rw [← hVs 0 hm]; omega)
        exact (liveOf ring hn hbank root lane src R hR hsrc hend z0 hz w (ts + 1 + t) (R + 0)
          (by omega) (by omega) _ hc).1
    · rw [hVm m (by omega) hm] at h1
      have hc := hcar m hm (ts + 1 + t) (by omega) (by rw [← hVs m hm]; omega)
      exact (liveOf ring hn hbank root lane src R hR hsrc hend z0 hz w (ts + 1 + t) (R + m)
        (by omega) (by omega) _ hc).1
  have hmv : ∀ m, m < R → cohortTok R (st (V (m + 1))) (R + m) = .empty ∧
      (m + 1 < R → (st (V (m + 1))).live (R + m + 1) = true) := by
    intro m hm
    obtain ⟨hlo, hhi⟩ := hVlo m hm
    have hge := hVge (m + 1) (by omega)
    rw [hV, hstAbs _ (by omega)]
    have hk := hkey m hm
    rw [← hVs m hm] at hk
    have hcm := hcar m hm (Va (m + 1) - 1) (by omega) (by rw [← hVs m hm]; omega)
    have hl := (liveOf ring hn hbank root lane src R hR hsrc hend z0 hz w (Va (m + 1) - 1) (R + m)
      (by omega) (by omega) _ hcm).2
    have he := laneEdge ring hn hbank root lane src R hR hsrc hend z0 hz w (Va (m + 1) - 1) (R + m) hk
    rw [show Va (m + 1) - 1 + 1 = Va (m + 1) by omega] at he
    refine ⟨by rw [he]; exact liveVacate (by omega) (by omega) hl, fun hm1 => ?_⟩
    have hV1 : Va (m + 1) = (uz (m + 1)).time := hVm (m + 1) (by omega) hm1
    have hc1 := hcar (m + 1) hm1 (Va (m + 1)) (Nat.le_of_eq hV1.symm)
      (by rw [← hVs (m + 1) hm1]; have := (hVlo (m + 1) hm1).1; omega)
    exact (liveOf ring hn hbank root lane src R hR hsrc hend z0 hz w (Va (m + 1)) (R + (m + 1))
      (by omega) (by omega) _ hc1).2
  obtain ⟨hall', hgo⟩ := bottomGlue (R := R) st 0 V h0' hVV hne hmv
  -- every letter
  have hVRv : V R = tm.time - (ts + 1) := by rw [hV, hVR]
  have hV0v : V 0 = tx - ts := by rw [hV, hV0e, hx0t]; omega
  have hgoAll : ∀ t, t < w.length - (ts + 1) → StrictGo R (st (t + 1)) (strictTrack R st 0 t) := by
    intro t _
    by_cases h1 : t < V 0
    · intro hp
      have := hbefore t (by omega)
      omega
    · by_cases h2 : t < V R
      · exact hgo t (by omega) h2
      · intro _ hp2
        have hm := strictTrackMono (R := R) st 0 (V R) (t - V R)
        rw [show V R + (t - V R) = t by omega, hall' R (Nat.le_refl R)] at hm
        omega
  have hstep : ∀ t, st (t + 1) = cohortLaneStep R (st t) (keAt root src R w (ts + 1 + t)) := by
    intro t
    rw [hst, hst]
    exact laneAtStep ring hn hbank root lane src R hR hsrc hend z0 hz w (ts + 1 + t)
  have hst0 : StrictPhase R (st 0) 0 := by
    unfold StrictPhase
    rw [if_pos (by omega)]
    exact tailSampleStart hR htok0
  have hph := strictTraceUpTo hR st (fun t => keAt root src R w (ts + 1 + t)) hstep 0 hst0
    (w.length - (ts + 1)) hgoAll
  have hm := strictTrackMono (R := R) st 0 (V R) (w.length - (ts + 1) - V R)
  rw [show V R + (w.length - (ts + 1) - V R) = w.length - (ts + 1) by omega,
    hall' R (Nat.le_refl R)] at hm
  have hcyc := strictPhaseCyc hph (by omega)
  rw [hst, show ts + 1 + (w.length - (ts + 1)) = w.length by omega] at hcyc
  rw [← runAtLen ring hbank w (startOf ring hbank z0) w.length (Nat.le_refl _)]
  exact hcyc

include hn hR hsrc hend hz in
/-- The first strict completion. Consumer: the entry stage `StructuralCut → EntryCut 0`
(group 6), whose receipts name `DigitFirstStrictCompletion`. -/
theorem firstStrictCyc (hRd : digitSpan (compileAdvice (ceilLogTwo n)) = R) (cut : Nat)
    (tm : DigitTerminal (compileAdvice (ceilLogTwo n)) n)
    (hcomp : DigitFirstStrictCompletion ring (w.foldl (bankRepairDigitBoundaryAuditNext ring hbank)
      (startOf ring hbank z0)).2 root src (src + R) lane cut tm) :
    CohortCyc R (cohortProj ring root lane src R
      (piD (w.foldl (bankRepairDigitBoundaryAuditNext ring hbank) (startOf ring hbank z0)).1.val.1)) :=
  strictCompletionCyc ring hn hbank root lane src R hR hsrc hend z0 hz w hRd cut tm hcomp.1

end Assembly

end L3.DigitEntryBridge

#print axioms L3.DigitEntryBridge.runFrames
#print axioms L3.DigitEntryBridge.frameTime
#print axioms L3.DigitEntryBridge.srcRows
#print axioms L3.DigitEntryBridge.carryOrigin
#print axioms L3.DigitEntryBridge.inOrigin
#print axioms L3.DigitEntryBridge.srcStep
#print axioms L3.DigitEntryBridge.bottomGlue
#print axioms L3.DigitEntryBridge.carryChain
#print axioms L3.DigitEntryBridge.inputBack
#print axioms L3.DigitEntryBridge.tailRun
#print axioms L3.DigitEntryBridge.strictCompletionCyc
#print axioms L3.DigitEntryBridge.firstStrictCyc
