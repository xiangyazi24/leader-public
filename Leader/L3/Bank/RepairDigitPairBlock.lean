import Leader.L3.Bank.RepairDigitBlockCuts

/-!
# T35, generic part: the five-cohort block with no anchor

T30–T34's per-block clock (`FiveInvOn`, `OldCompletionOn`, `HCloseOn`, `UseFactOn`,
`pinCoupledBlockReach`, `BlockCuts.runCoupledBlock`) threads a recorded **anchor**
`AnchorIn after A` (a completion of the pair at or before `after`). Its only consumer is
`CloseReceipt.completionOfReceipt`, which reads off the anchor nothing but its first field: the
complete pair `DigitCompletePair ring root A.start src (src + R)` on the audit start (the
geometry needed for the `DigitCompletion` of the next terminal, and `digitSpan = R`).

This module redoes the chain with that static fact in place of the anchor:

* `PairIn A`: the complete pair on the audit start; `anchorPair`: every anchor gives it. It is
  constant along the audit (`digitAuditStep` keeps `start`).
* `completionOfPair`: `completionOfReceipt` from the pair.
* `OldCompletionPair`, `oldCompletionPairReach`: the completion obligation on `UseReach` states
  with the pair premise, with no other premise (the receipt `receiptOfPins` never used the
  anchor).
* `FiveInvPair`, `fiveInvPairStep`, `fiveGoodPair`: `FiveInvOn` and its step / goodness with the
  pair in place of the anchor.
* `runPairBlock`: `BlockCuts.runCoupledBlock` with the pair premise: the block starts at **any**
  `WinInvD ∧ UseReach` state of counter `0` of a complete pair, `after` = any time `≤ clock`
  (e.g. the clock itself), with no recorded completion of the pair.
-/

namespace L3.PairBlock

set_option autoImplicit false

open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree
open L3.RenewalReferenceClock
open L3.CohortStages
open L3.CohortTransfer
open L3.CohortLedger
open L3.FiveTransfer
open L3.Projection
open L3.CohortDomination
open L3.CohortTail
open L3.CohortSites
open L3.CohortEntry
open L3.PacketClass
open L3.Rearm
open L3.Recording
open L3.GhostBridge
open L3.Correspondence
open L3.CohortIdentity
open L3.CohortWindow
open L3.CohortClose
open L3.CohortOrder
open L3.BlockStart
open L3.FiveClose
open L3.HClose
open L3.CloseReceipt
open L3.FiveReach
open L3.ValueCorr
open L3.ValueLedger
open L3.SitePin
open L3.UseRows
open L3.UseCells
open L3.UseTrack
open L3.BlockCuts

section Pair

variable {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
  (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) (root : Fin n) (lane : DigitLane)
  (src R : Nat) (hR : 2 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n)
  (Base : Bool → DigitAtom n → Prop)

/-- The complete pair `(src, src + R)` on the audit start. -/
def PairIn (A : DigitAudit (compileAdvice (ceilLogTwo n)) n) : Prop :=
  DigitCompletePair ring root A.start src (src + R)

/-- An anchor gives the complete pair. Consumer: the T35 report (the anchor premise of T30–T34
is stronger than what the chain uses: `runPairBlock` applies wherever `runCoupledBlock` does). -/
theorem anchorPair (after : Nat) (A : DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (h : AnchorIn ring root lane src R after A) : PairIn ring root src R A := by
  obtain ⟨t, ht, -⟩ := h
  exact ht.1

include hn hR hsrc hend in
/-- **`completionOfReceipt` from the complete pair** (no anchor): the receipt of a terminal
recorded after a just-closed cycle start makes it a `DigitCompletion`. Consumer:
`oldCompletionPairReach`. -/
theorem completionOfPair
    (wc : (BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n) ×
      ((Nat → Nat) × Nat)) (word : List (Fin n))
    (U : DigitTerminal (compileAdvice (ceilLogTwo n)) n)
    (hjc : JustClosed ring hbank root lane src R Base wc)
    (hpair : PairIn ring root src R wc.1.2)
    (hU : DigitRecordedTerminal (word.foldl (windowNext ring hbank root lane src R) wc).1.2 U)
    (hUl : U.lane = lane) (hUs : U.source = digitSite ring root (src + (2 * R - 1)))
    (hr : CloseReceipt ring hbank root lane src R wc U) :
    DigitCompletion ring (word.foldl (windowNext ring hbank root lane src R) wc).1.2 root src
      (src + R) lane 0 U := by
  obtain ⟨chi, ⟨hrec, hinc, hextra⟩, ⟨samp, hsamp⟩, hUd, L, hL, hLi, hLl, hLu, huse⟩ := hr
  have hspan : digitSpan (compileAdvice (ceilLogTwo n)) = R := by
    have := hpair.2.1
    omega
  have hstart : (word.foldl (windowNext ring hbank root lane src R) wc).1.2.start =
      wc.1.2.start :=
    auditFold ring hbank root lane src R (fun A => A.start = wc.1.2.start)
      (fun S A e hA => hA) word wc rfl
  have hfo0 : AuditFrameOrder wc.1.2 :=
    (justClosedStart ring hn hbank root lane src R hR hsrc hend Base wc hjc).1.2.1
  have hfo : AuditFrameOrder (word.foldl (windowNext ring hbank root lane src R) wc).1.2 :=
    auditFold ring hbank root lane src R AuditFrameOrder
      (fun S A e hA => auditFrameOrderStep ring S A e hA) word wc hfo0
  have hclk : U.time ≤ (word.foldl (windowNext ring hbank root lane src R) wc).1.2.clock := by
    obtain ⟨f, hf, hft, -⟩ := hU
    rw [← hft]
    exact (hfo.2.1 f hf).2
  have hrecF : ∀ i, i < R →
      DigitRecordedExport (word.foldl (windowNext ring hbank root lane src R) wc).1.2 (chi i) :=
    fun i hi => auditFold ring hbank root lane src R (fun A => DigitRecordedExport A (chi i))
      (fun S A e hA => recordedExportStep ring S A e _ hA) word wc (hrec i hi).1
  have hsampF : ∀ i, i < R →
      DigitRecordedSample (word.foldl (windowNext ring hbank root lane src R) wc).1.2 (samp i) :=
    fun i hi => auditFold ring hbank root lane src R (fun A => DigitRecordedSample A (samp i))
      (fun S A e hA => recordedSampleStep ring S A e _ hA) word wc (hsamp i hi).1
  have hchiT : ∀ i, i < R → (chi i).time ≤ wc.1.2.clock :=
    fun i hi => recordedTimeLe wc.1.2 hfo0 (chi i) (hrec i hi).1
  refine ⟨by rw [hstart]; exact hpair, hU, hUl, ?_, ?_, hclk, by omega, L,
    fun j => samp (R - 1 - j.val), fun j => chi (R - 1 - j.val),
    fun j => L.uses[j.val]'(by have := j.isLt; omega), hL, hLi, by omega, ?_, ?_, ?_⟩
  · rw [hUs]
    exact congrArg (digitSite ring root) (by omega)
  · rw [hUd]
    exact congrArg (digitSite ring root) (by omega)
  · intro j
    have hj := j.isLt
    have hjR : j.val < R := by omega
    have hi : R - 1 - j.val < R := by omega
    have hback : R - 1 - (R - 1 - j.val) = j.val := by omega
    obtain ⟨-, s2, s3, s4, s5, s6, s7, s8, s9⟩ := hsamp (R - 1 - j.val) hi
    rw [hback] at s4 s9
    obtain ⟨-, ⟨x1, x2⟩, x3⟩ := hrec (R - 1 - j.val) hi
    have hget : L.uses[j.val]? = some (L.uses[j.val]'(by omega)) :=
      List.getElem?_eq_getElem (by omega)
    obtain ⟨u1, u2, u3, u4⟩ := huse j.val _ hget
    obtain ⟨v1, v2, -⟩ := hLu j.val _ hget
    have hct := hchiT (R - 1 - j.val) hi
    refine ⟨hsampF _ hi, s3, s4, s5, s9, hrecF _ hi, x1,
      x2.trans (congrArg (digitSite ring root) (by omega)), x3, s2, s7, s8, hget, v1,
      u1.trans s2, u2.trans s7, u3.trans s8, s6, Nat.lt_of_le_of_lt hct u4, v2⟩
  · intro i j hij
    have hj := j.isLt
    have hgi : L.uses[i.val]? = some (L.uses[i.val]'(by have := i.isLt; omega)) :=
      List.getElem?_eq_getElem (by have := i.isLt; omega)
    have hgj : L.uses[j.val]? = some (L.uses[j.val]'(by omega)) :=
      List.getElem?_eq_getElem (by omega)
    exact ⟨hinc (R - 1 - j.val) (R - 1 - i.val) (by omega) (by omega),
      (hLu j.val _ hgj).2.2 i.val _ hij hgi⟩
  · intro other ho o1 o2 o3 o4 o5
    have e0 : R - 1 - (digitSpan (compileAdvice (ceilLogTwo n)) - 1) = 0 := by omega
    have e1 : R - 1 - 0 = R - 1 := by omega
    have o4' : (chi 0).time ≤ other.time := by
      have h4 := o4
      dsimp only at h4
      rw [e0] at h4
      exact h4
    have o5' : other.time ≤ (chi (R - 1)).time := by
      have h5 := o5
      dsimp only at h5
      rw [e1] at h5
      exact h5
    obtain ⟨i, hi, rfl⟩ := hextra word other ho
      ⟨o1, o2.trans (congrArg (digitSite ring root) (by omega))⟩ o4' o5'
    refine ⟨⟨R - 1 - i, by omega⟩, ?_⟩
    show chi i = chi (R - 1 - (R - 1 - i))
    rw [show R - 1 - (R - 1 - i) = i by omega]

/-- **`OldCompletionOn` with the complete pair in place of the anchor** (and no `after`). -/
def OldCompletionPair
    (Reach : (BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n) ×
      ((Nat → Nat) × Nat) → Prop) : Prop :=
  ∀ (wc : (BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n) ×
      ((Nat → Nat) × Nat)) (word : List (Fin n))
    (U : DigitTerminal (compileAdvice (ceilLogTwo n)) n),
    Reach wc → JustClosed ring hbank root lane src R Base wc →
    PairIn ring root src R wc.1.2 →
    (word.foldl (windowNext ring hbank root lane src R) wc).2.2 = wc.2.2 →
    OrderInv ring hbank root lane src R (word.foldl (windowNext ring hbank root lane src R) wc).1
      (word.foldl (windowNext ring hbank root lane src R) wc).2 wc.1.2.clock →
    DigitRecordedTerminal (word.foldl (windowNext ring hbank root lane src R) wc).1.2 U →
    U.lane = lane → U.source = digitSite ring root (src + (2 * R - 1)) →
    wc.1.2.clock < U.time →
    DigitCompletion ring (word.foldl (windowNext ring hbank root lane src R) wc).1.2 root src
      (src + R) lane 0 U

include hn hR hsrc hend in
/-- **The completion obligation on `UseReach` states from the complete pair, with no other
premise** (T33's `hCloseOnPinReach` + `oldCompletionOn`, whose receipt never read the anchor).
Consumer: `runPairBlock`. -/
theorem oldCompletionPairReach :
    OldCompletionPair ring hbank root lane src R Base (UseReach ring hbank root lane src R) := by
  intro wc word U hre hjc hp hcnt _ hU hUl hUs hUt
  obtain ⟨hwd, -⟩ := justClosedStart ring hn hbank root lane src R hR hsrc hend Base wc hjc
  obtain ⟨chi, hcore, hpin, -, huse⟩ :=
    useFactReach ring hn hbank root lane src R hR hsrc hend Base wc word hre hjc hcnt
  have hreF := pinReachRun ring hn hbank root lane src R hR hsrc hend Base word wc hwd hre.1
  exact completionOfPair ring hn hbank root lane src R hR hsrc hend Base wc word U hjc hp hU hUl
    hUs (receiptOfPins ring hbank root lane src R hR wc word U hre.1.1.1 hwd.2.1 hre.1.1.2.2.1
      hwd.2.2.1.2.2.2.1 hreF.1.2 hU hUl hUs chi hcore hpin (huse U hU hUl hUs hUt))

/-- **The five-cohort invariant with the complete pair**: `FiveInvOn` with `PairIn` (now and at
the cycle start) in place of the anchor. -/
def FiveInvPair
    (Reach : (BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n) ×
      ((Nat → Nat) × Nat) → Prop) (after : Nat)
    (w : (BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n) ×
      ((Nat → Nat) × Nat)) : Prop :=
  Reach w ∧ PairIn ring root src R w.1.2 ∧
  ((w.2.2 = 0 ∧ after ≤ w.1.2.clock) ∨
  (1 ≤ w.2.2 ∧ ∃ (wc : (BankReferenceState ring hbank ×
      DigitAudit (compileAdvice (ceilLogTwo n)) n) × ((Nat → Nat) × Nat)) (word : List (Fin n)),
    Reach wc ∧ JustClosed ring hbank root lane src R Base wc ∧
    w = word.foldl (windowNext ring hbank root lane src R) wc ∧ wc.2.2 = w.2.2 ∧
    OrderInv ring hbank root lane src R w.1 w.2 wc.1.2.clock ∧ after ≤ wc.1.2.clock ∧
    PairIn ring root src R wc.1.2 ∧
    FwdIn ring root src (src + R) lane w.1.2 (w.2.2 - 1) after wc.1.2.clock))

include hn hR hsrc hend in
/-- `FiveInvPair` is carried by every letter (`FiveReach.fiveInvOnStep` with the pair).
Consumer: `runPairBlock`. -/
theorem fiveInvPairStep
    (Reach : (BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n) ×
      ((Nat → Nat) × Nat) → Prop) (after : Nat)
    (hReach : ∀ w e, WinInvD ring hbank root lane src R Base w.1 w.2 → Reach w →
      Reach (windowNext ring hbank root lane src R w e))
    (hcomp : OldCompletionPair ring hbank root lane src R Base Reach)
    (w : (BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n) ×
      ((Nat → Nat) × Nat)) (e : Fin n)
    (hw : WinInvD ring hbank root lane src R Base w.1 w.2)
    (hi : FiveInvPair ring hbank root lane src R Base Reach after w) :
    FiveInvPair ring hbank root lane src R Base Reach after
      (windowNext ring hbank root lane src R w e) := by
  obtain ⟨hre, hp, hi⟩ := hi
  have hre' := hReach w e hw hre
  have hclk : (windowNext ring hbank root lane src R w e).1.2.clock = w.1.2.clock + 1 := rfl
  have hp' : PairIn ring root src R (windowNext ring hbank root lane src R w e).1.2 := hp
  refine ⟨hre', hp', ?_⟩
  rcases hi with ⟨h0, ha⟩ | ⟨h1, wc, word, hrc, hjc, hweq, hcnt, hord, haft, hpc, hfwd⟩
  · rcases (winInvDStep ring hn hbank root lane src R hR hsrc hend Base w.1 w.2 hw e).2 with
      hs | ⟨hs, -⟩
    · left
      refine ⟨?_, by rw [hclk]; omega⟩
      show (windowGhost ring hbank root lane src R w.1 w.2 e).2 = 0
      rw [hs, h0]
    · right
      have hjc' : JustClosed ring hbank root lane src R Base
          (windowNext ring hbank root lane src R w e) := ⟨w, e, hw, rfl, hs⟩
      obtain ⟨hwd, hst⟩ := justClosedStart ring hn hbank root lane src R hR hsrc hend Base _ hjc'
      refine ⟨?_, windowNext ring hbank root lane src R w e, [], hre', hjc', rfl, rfl,
        ⟨hwd.1, Nat.le_refl _, 0, hst, fun h => by omega⟩, by rw [hclk]; omega, hp', ?_⟩
      · show 1 ≤ (windowGhost ring hbank root lane src R w.1 w.2 e).2
        rw [hs]
        omega
      · show FwdIn ring root src (src + R) lane _
          ((windowGhost ring hbank root lane src R w.1 w.2 e).2 - 1) after _
        rw [hs, h0]
        exact trivial
  · rcases orderInvStep ring hn hbank root lane src R hR hsrc hend w.1 w.2 wc.1.2.clock hord e
      with ⟨hs, hord'⟩ | ⟨hs, hord', hterm⟩
    · right
      refine ⟨?_, wc, word ++ [e], hrc, hjc, ?_, ?_, hord', haft, hpc, ?_⟩
      · show 1 ≤ (windowGhost ring hbank root lane src R w.1 w.2 e).2
        rw [hs]
        exact h1
      · rw [List.foldl_append, ← hweq]
        rfl
      · show wc.2.2 = (windowGhost ring hbank root lane src R w.1 w.2 e).2
        rw [hs, hcnt]
      · show FwdIn ring root src (src + R) lane (digitAuditStep ring (piD w.1.1.val.1) w.1.2 e)
          ((windowGhost ring hbank root lane src R w.1 w.2 e).2 - 1) after wc.1.2.clock
        rw [hs]
        exact fwdInStep ring root src (src + R) lane _ _ _ _ _ _ hfwd
    · right
      have hjc' : JustClosed ring hbank root lane src R Base
          (windowNext ring hbank root lane src R w e) := ⟨w, e, hw, rfl, hs⟩
      obtain ⟨U, hU, hUl, hUs, hUt, hUc⟩ := hterm
      have hcU := hcomp wc word U hrc hjc hpc (by rw [← hweq]; exact hcnt.symm)
        (by rw [← hweq]; exact hord) (by rw [← hweq]; exact hU) hUl hUs hUt
      rw [← hweq] at hcU
      have h01 := hord.2.1
      refine ⟨?_, windowNext ring hbank root lane src R w e, [], hre', hjc', rfl, rfl, hord',
        by show after ≤ w.1.2.clock + 1; omega, hp', ?_⟩
      · show 1 ≤ (windowGhost ring hbank root lane src R w.1 w.2 e).2
        rw [hs]
        omega
      · show FwdIn ring root src (src + R) lane (digitAuditStep ring (piD w.1.1.val.1) w.1.2 e)
          ((windowGhost ring hbank root lane src R w.1 w.2 e).2 - 1) after (w.1.2.clock + 1)
        rw [hs, Nat.add_sub_cancel]
        have hlen : w.2.2 = (w.2.2 - 1) + 1 := by omega
        rw [hlen]
        exact fwdInAppend ring root src (src + R) lane U
          (completionStep ring (piD w.1.1.val.1) w.1.2 e root src (src + R) lane 0 U hcU)
          (w.2.2 - 1) after wc.1.2.clock (w.1.2.clock + 1)
          (fwdInStep ring root src (src + R) lane _ _ _ _ _ _ hfwd) haft hUt (by omega)
          (by omega)

/-- When the old cohort of cycle `5` is gone, five chained completions after `after` are
recorded (`FiveReach.fiveGoodOn` with the pair). Consumer: `runPairBlock`. -/
theorem fiveGoodPair
    (Reach : (BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n) ×
      ((Nat → Nat) × Nat) → Prop) (after : Nat)
    (hcomp : OldCompletionPair ring hbank root lane src R Base Reach)
    (w : (BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n) ×
      ((Nat → Nat) × Nat))
    (hi : FiveInvPair ring hbank root lane src R Base Reach after w)
    (hb : CohortLayout ring hbank root src R w.1.1 ∧
      CohortCycOld R 5 (2 * R + 1) (cohortProj ring root lane src R (piD w.1.1.val.1)) w.2) :
    FwdChain ring w.1.2 root src (src + R) lane 5 after := by
  obtain ⟨-, hold⟩ := hb
  obtain ⟨-, -, hi⟩ := hi
  rcases hi with ⟨h0, -⟩ | ⟨-, wc, word, hrc, hjc, hweq, hcnt, hord, haft, hpc, hfwd⟩
  · rcases hold with ⟨o', -, hin⟩ | hst
    · have := hin.1
      omega
    · have := hst.1
      omega
  · rcases hold with ⟨o', ho', hin⟩ | hst
    · have h5 : w.2.2 = 5 := hin.1
      have hle := cohortOldLe hin.2.1.1
      have hoe : o' = 2 * R + 1 := by omega
      subst hoe
      have hord0 := hord
      obtain ⟨-, h01, o, hino, hterm⟩ := hord
      obtain ⟨U, hU, hUl, hUs, hUt, hUc⟩ := hterm (cycPhaseDone hin hino)
      have hcU := hcomp wc word U hrc hjc hpc (by rw [← hweq]; exact hcnt.symm)
        (by rw [← hweq]; exact hord0) (by rw [← hweq]; exact hU) hUl hUs hUt
      rw [← hweq] at hcU
      rw [h5] at hfwd
      exact fwdInChain ring root src (src + R) lane _ 5 after _
        (fwdInAppend ring root src (src + R) lane U hcU 4 after wc.1.2.clock (w.1.2.clock + 1)
          hfwd haft hUt (by omega) (by omega))
    · have h6 : w.2.2 = 6 := hst.1
      rw [h6] at hfwd
      exact fwdInChain ring root src (src + R) lane _ 5 after _ hfwd

include hn hR hsrc hend in
/-- **The per-block clock with no anchor**: `BlockCuts.runCoupledBlock` with the complete pair
`PairIn` in place of `AnchorIn after`. From any coupled start with the strengthened window
invariant, `UseReach`, counter `0`, `after ≤ clock` and the complete pair on the audit start, and
a carried invariant `Carry`, the first state with five chained completions after `after` (seen
with `Carry`) costs `≤ 200 n R` doubled. Consumer: `BankRepairDigitBlockEntry`
(`entryBlockStage`). -/
theorem runPairBlock (after : Nat) (P Q : BankReferenceState ring hbank → Prop)
    (Carry : (BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n) ×
      ((Nat → Nat) × Nat) → Prop)
    (hcarry : ∀ w e, WinInvD ring hbank root lane src R Base w.1 w.2 → Carry w →
      Carry (windowNext ring hbank root lane src R w e))
    (hA : ∀ z, P z → ∃ w : (BankReferenceState ring hbank ×
        DigitAudit (compileAdvice (ceilLogTwo n)) n) × ((Nat → Nat) × Nat),
      w.1.1 = z ∧ WinInvD ring hbank root lane src R Base w.1 w.2 ∧
        UseReach ring hbank root lane src R w ∧ w.2.2 = 0 ∧
        after ≤ w.1.2.clock ∧ PairIn ring root src R w.1.2 ∧ Carry w)
    (hB : ∀ w : (BankReferenceState ring hbank ×
        DigitAudit (compileAdvice (ceilLogTwo n)) n) × ((Nat → Nat) × Nat),
      FwdChain ring w.1.2 root src (src + R) lane 5 after → Carry w → Q w.1.1) :
    CoupledBlock ring hbank P Q (200 * n * R) :=
  windowCoupledBlock ring hn hbank root lane src R hR hsrc hend Base P Q
    (fun w => FiveInvPair ring hbank root lane src R Base (UseReach ring hbank root lane src R)
      after w ∧ Carry w)
    (fun w => FwdChain ring w.1.2 root src (src + R) lane 5 after ∧ Carry w)
    (fun w e hw hi _ => ⟨fiveInvPairStep ring hn hbank root lane src R hR hsrc hend Base
        (UseReach ring hbank root lane src R) after
        (fun v e' hv h => useReachStep ring hn hbank root lane src R hR hsrc hend Base v e' hv h)
        (oldCompletionPairReach ring hn hbank root lane src R hR hsrc hend Base) w e hw hi.1,
      hcarry w e hw hi.2⟩)
    (fun w _ hi hb => ⟨fiveGoodPair ring hbank root lane src R Base
        (UseReach ring hbank root lane src R) after
        (oldCompletionPairReach ring hn hbank root lane src R hR hsrc hend Base) w hi.1 hb,
      hi.2⟩)
    (fun z hz => by
      obtain ⟨w, hz, hw, hu, hc, haft, hp, hcar⟩ := hA z hz
      exact ⟨w, hz, hw, ⟨⟨hu, hp, Or.inl ⟨hc, haft⟩⟩, hcar⟩, hc⟩)
    (fun w hg => hB w hg.1 hg.2)

end Pair

end L3.PairBlock

#print axioms L3.PairBlock.anchorPair
#print axioms L3.PairBlock.completionOfPair
#print axioms L3.PairBlock.oldCompletionPairReach
#print axioms L3.PairBlock.fiveInvPairStep
#print axioms L3.PairBlock.fiveGoodPair
#print axioms L3.PairBlock.runPairBlock
