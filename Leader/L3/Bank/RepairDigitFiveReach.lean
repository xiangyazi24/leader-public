import Leader.L3.Bank.RepairDigitCloseReceipt

/-!
# T31 item 4: the five-cohort transfer on reachable cycle starts

T30's `FiveInv` / `fiveCloseCharge` consume `OldCompletion` over **every** just-closed state.
The receipt (`HCloseFact`) can only be proved on states whose audit satisfies an invariant
`Reach` that the coupled chain carries (for instance `ExactReach`: every frame carries its
literal service; see `L3.CloseReceipt`). This module redoes the five-cohort invariant with
`Reach` recorded at the current state and at the cycle start, so the charge consumes
`OldCompletionOn Reach` (and hence `HCloseOn Reach`).

* `FiveInvOn Reach after`: `Reach` now, and T30's `FiveInv` clauses with `Reach` at the cycle
  start `wc`.
* `fiveInvOnStep`, `fiveGoodOn`: as T30's `fiveInvStep`, `fiveGood`.
* `fiveReachCharge`, `fiveReachChargeOfClose`, `fiveReachCohortCharge`,
  `fiveReachCoupledBlock`: T30's charges with `OldCompletionOn Reach`.
* `ExactReach`: `FramesExact` on the coupled chain, carried by every letter (`exactReachStep`).
-/

namespace L3.FiveReach

set_option autoImplicit false

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
open L3.CohortTransfer
open L3.CohortClose
open L3.CohortLedger
open L3.CohortOrder
open L3.FiveTransfer
open L3.BlockStart
open L3.Projection
open L3.FiveClose
open L3.HClose
open L3.CloseReceipt

section Five

variable {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
  (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) (root : Fin n) (lane : DigitLane)
  (src R : Nat) (hR : 2 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n)
  (Base : Bool → DigitAtom n → Prop)
  (Reach : (BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n) ×
      ((Nat → Nat) × Nat) → Prop)

/-- Exact frames on the coupled chain. -/
def ExactReach
    (w : (BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n) ×
      ((Nat → Nat) × Nat)) : Prop :=
  FramesExact ring w.1.2

theorem exactReachStep
    (w : (BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n) ×
      ((Nat → Nat) × Nat)) (e : Fin n) (h : ExactReach ring hbank w) :
    ExactReach ring hbank (windowNext ring hbank root lane src R w e) :=
  framesExactStep ring (piD w.1.1.val.1) w.1.2 e h

/-- **The five-cohort invariant on reachable states**: `Reach` now; entrance cycle, or a cycle
started at a just-closed state `wc` satisfying `Reach`, as in T30's `FiveInv`. -/
def FiveInvOn (after : Nat)
    (w : (BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n) ×
      ((Nat → Nat) × Nat)) : Prop :=
  Reach w ∧
  ((w.2.2 = 0 ∧ after ≤ w.1.2.clock ∧ AnchorIn ring root lane src R after w.1.2) ∨
  (1 ≤ w.2.2 ∧ ∃ (wc : (BankReferenceState ring hbank ×
      DigitAudit (compileAdvice (ceilLogTwo n)) n) × ((Nat → Nat) × Nat)) (word : List (Fin n)),
    Reach wc ∧ JustClosed ring hbank root lane src R Base wc ∧
    w = word.foldl (windowNext ring hbank root lane src R) wc ∧ wc.2.2 = w.2.2 ∧
    OrderInv ring hbank root lane src R w.1 w.2 wc.1.2.clock ∧ after ≤ wc.1.2.clock ∧
    AnchorIn ring root lane src R after wc.1.2 ∧ AnchorIn ring root lane src R after w.1.2 ∧
    FwdIn ring root src (src + R) lane w.1.2 (w.2.2 - 1) after wc.1.2.clock))

include hn hR hsrc hend in
/-- `FiveInvOn` is carried by every letter (T30's `fiveInvStep` with `Reach`). -/
theorem fiveInvOnStep (after : Nat)
    (hReach : ∀ w e, WinInvD ring hbank root lane src R Base w.1 w.2 → Reach w →
      Reach (windowNext ring hbank root lane src R w e))
    (hcomp : OldCompletionOn ring hbank root lane src R Base Reach after)
    (w : (BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n) ×
      ((Nat → Nat) × Nat)) (e : Fin n)
    (hw : WinInvD ring hbank root lane src R Base w.1 w.2)
    (hi : FiveInvOn ring hbank root lane src R Base Reach after w) :
    FiveInvOn ring hbank root lane src R Base Reach after
      (windowNext ring hbank root lane src R w e) := by
  obtain ⟨hre, hi⟩ := hi
  have hre' := hReach w e hw hre
  have hclk : (windowNext ring hbank root lane src R w e).1.2.clock = w.1.2.clock + 1 := rfl
  refine ⟨hre', ?_⟩
  rcases hi with ⟨h0, ha, hanc⟩ |
      ⟨h1, wc, word, hrc, hjc, hweq, hcnt, hord, haft, hancc, hanc, hfwd⟩
  · rcases (winInvDStep ring hn hbank root lane src R hR hsrc hend Base w.1 w.2 hw e).2 with
      hs | ⟨hs, -⟩
    · left
      refine ⟨?_, by rw [hclk]; omega, anchorInStep ring root lane src R after _ _ e hanc⟩
      show (windowGhost ring hbank root lane src R w.1 w.2 e).2 = 0
      rw [hs, h0]
    · right
      have hjc' : JustClosed ring hbank root lane src R Base
          (windowNext ring hbank root lane src R w e) := ⟨w, e, hw, rfl, hs⟩
      obtain ⟨hwd, hst⟩ := justClosedStart ring hn hbank root lane src R hR hsrc hend Base _ hjc'
      refine ⟨?_, windowNext ring hbank root lane src R w e, [], hre', hjc', rfl, rfl,
        ⟨hwd.1, Nat.le_refl _, 0, hst, fun h => by omega⟩, by rw [hclk]; omega,
        anchorInStep ring root lane src R after _ _ e hanc,
        anchorInStep ring root lane src R after _ _ e hanc, ?_⟩
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
      refine ⟨?_, wc, word ++ [e], hrc, hjc, ?_, ?_, hord', haft, hancc,
        anchorInStep ring root lane src R after _ _ e hanc, ?_⟩
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
      have hcU := hcomp wc word U hrc hjc hancc haft (by rw [← hweq]; exact hcnt.symm)
        (by rw [← hweq]; exact hord) (by rw [← hweq]; exact hU) hUl hUs hUt
      rw [← hweq] at hcU
      have h01 := hord.2.1
      refine ⟨?_, windowNext ring hbank root lane src R w e, [], hre', hjc', rfl, rfl, hord',
        by show after ≤ w.1.2.clock + 1; omega,
        anchorInStep ring root lane src R after _ _ e hanc,
        anchorInStep ring root lane src R after _ _ e hanc, ?_⟩
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
recorded (T30's `fiveGood` with `Reach`). -/
theorem fiveGoodOn (after : Nat)
    (hcomp : OldCompletionOn ring hbank root lane src R Base Reach after)
    (w : (BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n) ×
      ((Nat → Nat) × Nat))
    (hi : FiveInvOn ring hbank root lane src R Base Reach after w)
    (hb : CohortLayout ring hbank root src R w.1.1 ∧
      CohortCycOld R 5 (2 * R + 1) (cohortProj ring root lane src R (piD w.1.1.val.1)) w.2) :
    FwdChain ring w.1.2 root src (src + R) lane 5 after := by
  obtain ⟨-, hold⟩ := hb
  obtain ⟨-, hi⟩ := hi
  rcases hi with ⟨h0, -⟩ | ⟨-, wc, word, hrc, hjc, hweq, hcnt, hord, haft, hancc, -, hfwd⟩
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
      have hcU := hcomp wc word U hrc hjc hancc haft (by rw [← hweq]; exact hcnt.symm)
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
/-- **The five-cohort charge on reachable states**: from a block start satisfying `Reach`, the
first state with five chained completions after `after` costs `≤ 200 n R` doubled, given
`OldCompletionOn Reach`. -/
theorem fiveReachCharge (after : Nat)
    (hReach : ∀ w e, WinInvD ring hbank root lane src R Base w.1 w.2 → Reach w →
      Reach (windowNext ring hbank root lane src R w e))
    (hcomp : OldCompletionOn ring hbank root lane src R Base Reach after)
    (w : (BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n) ×
      ((Nat → Nat) × Nat))
    (hw : WinInvD ring hbank root lane src R Base w.1 w.2) (hre : Reach w) (h0 : w.2.2 = 0)
    (hafter : after ≤ w.1.2.clock) (hanc : AnchorIn ring root lane src R after w.1.2) (T : Nat) :
    2 * costNumerator (windowNext ring hbank root lane src R)
        (fun v => FwdChain ring v.1.2 root src (src + R) lane 5 after) w T ≤
      n ^ T * (200 * n * R) :=
  blockCharge ring hn hbank root lane src R hR hsrc hend Base
    (FiveInvOn ring hbank root lane src R Base Reach after)
    (fun v => FwdChain ring v.1.2 root src (src + R) lane 5 after)
    (fun v e hv hi _ => fiveInvOnStep ring hn hbank root lane src R hR hsrc hend Base Reach after
      hReach hcomp v e hv hi) 0
    (fun v _ hi hb => fiveGoodOn ring hbank root lane src R Base Reach after hcomp v hi hb) w hw
    ⟨hre, Or.inl ⟨h0, hafter, hanc⟩⟩ h0 T

include hn hR hsrc hend in
/-- The same charge from the restricted receipt `HCloseOn Reach`. -/
theorem fiveReachChargeOfClose (after : Nat)
    (hReach : ∀ w e, WinInvD ring hbank root lane src R Base w.1 w.2 → Reach w →
      Reach (windowNext ring hbank root lane src R w e))
    (h : HCloseOn ring hbank root lane src R Base Reach after)
    (w : (BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n) ×
      ((Nat → Nat) × Nat))
    (hw : WinInvD ring hbank root lane src R Base w.1 w.2) (hre : Reach w) (h0 : w.2.2 = 0)
    (hafter : after ≤ w.1.2.clock) (hanc : AnchorIn ring root lane src R after w.1.2) (T : Nat) :
    2 * costNumerator (windowNext ring hbank root lane src R)
        (fun v => FwdChain ring v.1.2 root src (src + R) lane 5 after) w T ≤
      n ^ T * (200 * n * R) :=
  fiveReachCharge ring hn hbank root lane src R hR hsrc hend Base Reach after hReach
    (oldCompletionOn ring hn hbank root lane src R hR hsrc hend Base Reach after h)
    w hw hre h0 hafter hanc T

include hn hR hsrc hend in
/-- The charge for `∃ last, DigitFiveCohortCompletions … after last`, given T27's `hrank`. -/
theorem fiveReachCohortCharge (after : Nat)
    (hReach : ∀ w e, WinInvD ring hbank root lane src R Base w.1 w.2 → Reach w →
      Reach (windowNext ring hbank root lane src R w e))
    (hcomp : OldCompletionOn ring hbank root lane src R Base Reach after)
    (hrank : ∀ (A : DigitAudit (compileAdvice (ceilLogTwo n)) n)
      (first second third fourth last : DigitTerminal (compileAdvice (ceilLogTwo n)) n),
      DigitNextCompletion ring A root src (src + R) lane after first →
      DigitNextCompletion ring A root src (src + R) lane first.time second →
      DigitNextCompletion ring A root src (src + R) lane second.time third →
      DigitNextCompletion ring A root src (src + R) lane third.time fourth →
      DigitNextCompletion ring A root src (src + R) lane fourth.time last →
      ∃ (anchor : DigitTerminal (compileAdvice (ceilLogTwo n)) n) (anchorTail : DigitStamp n)
        (firstRank : Nat),
        DigitAnchor ring A root src (src + R) lane anchor anchorTail ∧
        anchor.time ≤ after ∧ 0 < firstRank ∧
        DigitSerialTerminalRanks A lane (digitSite ring root src) anchor anchorTail
          firstRank [first, second, third, fourth, last])
    (w : (BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n) ×
      ((Nat → Nat) × Nat))
    (hw : WinInvD ring hbank root lane src R Base w.1 w.2) (hre : Reach w) (h0 : w.2.2 = 0)
    (hafter : after ≤ w.1.2.clock) (hanc : AnchorIn ring root lane src R after w.1.2) (T : Nat) :
    2 * costNumerator (windowNext ring hbank root lane src R)
        (fun v => ∃ last, DigitFiveCohortCompletions ring v.1.2 root src (src + R) lane after last)
        w T ≤ n ^ T * (200 * n * R) :=
  Nat.le_trans (Nat.mul_le_mul_left 2 (costTargetMono _
      (fun v => FwdChain ring v.1.2 root src (src + R) lane 5 after) _
      (fun v h => fiveCohortOfFwd h (hrank v.1.2)) w T))
    (fiveReachCharge ring hn hbank root lane src R hR hsrc hend Base Reach after hReach hcomp w
      hw hre h0 hafter hanc T)

include hn hR hsrc hend in
/-- **The per-block clock on reachable states** (T30 item 5 form). -/
theorem fiveReachCoupledBlock (after : Nat)
    (hReach : ∀ w e, WinInvD ring hbank root lane src R Base w.1 w.2 → Reach w →
      Reach (windowNext ring hbank root lane src R w e))
    (hcomp : OldCompletionOn ring hbank root lane src R Base Reach after)
    (P Q : BankReferenceState ring hbank → Prop)
    (hA : ∀ z, P z → ∃ w : (BankReferenceState ring hbank ×
        DigitAudit (compileAdvice (ceilLogTwo n)) n) × ((Nat → Nat) × Nat),
      w.1.1 = z ∧ (WinInvD ring hbank root lane src R Base w.1 w.2 ∧
        FiveInvOn ring hbank root lane src R Base Reach after w ∧ w.2.2 = 0))
    (hB : ∀ w : (BankReferenceState ring hbank ×
        DigitAudit (compileAdvice (ceilLogTwo n)) n) × ((Nat → Nat) × Nat),
      FwdChain ring w.1.2 root src (src + R) lane 5 after → Q w.1.1) :
    CoupledBlock ring hbank P Q (200 * n * R) :=
  windowCoupledBlock ring hn hbank root lane src R hR hsrc hend Base P Q
    (FiveInvOn ring hbank root lane src R Base Reach after)
    (fun v => FwdChain ring v.1.2 root src (src + R) lane 5 after)
    (fun v e hv hi _ => fiveInvOnStep ring hn hbank root lane src R hR hsrc hend Base Reach after
      hReach hcomp v e hv hi)
    (fun v _ hi hb => fiveGoodOn ring hbank root lane src R Base Reach after hcomp v hi hb) hA hB

end Five

end L3.FiveReach

#print axioms L3.FiveReach.exactReachStep
#print axioms L3.FiveReach.fiveInvOnStep
#print axioms L3.FiveReach.fiveGoodOn
#print axioms L3.FiveReach.fiveReachCharge
#print axioms L3.FiveReach.fiveReachChargeOfClose
#print axioms L3.FiveReach.fiveReachCohortCharge
#print axioms L3.FiveReach.fiveReachCoupledBlock
