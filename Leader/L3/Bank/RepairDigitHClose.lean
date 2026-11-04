import Leader.L3.Bank.RepairDigitFiveClose

/-!
# T30 item 2: the hclose receipt and the assembly of `DigitCompletion`

T30's open obligation `OldCompletion` (FiveClose) asks that a terminal recorded on the terminal
edge in a cycle started at a just-closed state `wc` be a `DigitCompletion` of the pair. This
module reduces it (`oldCompletionOfClose`) to the exact receipt fact `HCloseFact`.

`HCloseFact` asks for a previous window `chi` (the crossings closed at `wc`) with three parts:
* `ChiPrev`: the window clauses of T28's `windowClosingD` / `justClosedWindow`, plus the
  crossings' destination;
* `ChiSampled`: crossing `chi i` carries a recorded sample of source cell `src + (R - 1 - i)`, with
  that sample's value and tail. This is the sample exactness that T27's provenance `GhostOk`
  (base atom, or a sample at *some* source cell) does not give;
* `CloseUses`, the hclose fact proper: the terminal's ledger is clean, its `j`-th use comes after
  the cycle start, and that use carries the operand, value and tail of `chi (R - 1 - j)`.

Everything else in `DigitCompletion` is proved here: the pair and the span (from the anchor
completion), the terminal's recording and time, the reverse export order and forward use order,
sample < export < use < terminal, and no extra export.

`terminalCleanUses`: the length and use-order part of `CloseUses` follows from T28's `LedgerOk`
once the ledger is clean.
-/

namespace L3.HClose

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
open L3.FiveClose

/-! ### The ledger side of a clean terminal -/

section Ledger

variable {c : Compiled} {n : Nat}

/-- A clean terminal ledger on the terminal edge has `R` uses aimed at the target cells in
order, before the terminal (T28 `LedgerOk`). -/
theorem terminalCleanUses (ring : DirectedRing n) (root : Fin n) (lane : DigitLane)
    (src R : Nat) (hR : 2 ≤ R) (A : DigitAudit c n) (h : LedgerOk ring root lane src R A)
    (T : DigitTerminal c n) (hT : DigitRecordedTerminal A T) (hl : T.lane = lane)
    (hs : T.source = digitSite ring root (src + (2 * R - 1))) (L : DigitCarryGhost c n)
    (hL : T.ledger = some L) (hclean : L.inherited = none) :
    L.uses.length = R ∧ UsesOk ring root src R T.time L.uses := by
  rcases h.2 T hT hl hs L hL with hi | ⟨-, hlen, hu⟩
  · exact absurd hclean hi
  · exact ⟨by omega, hu⟩

end Ledger

section Close

variable {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
  (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) (root : Fin n) (lane : DigitLane)
  (src R : Nat) (hR : 2 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n)
  (Base : Bool → DigitAtom n → Prop)

/-- Audit facts preserved by every letter persist along the coupled chain. -/
theorem auditFold (P : DigitAudit (compileAdvice (ceilLogTwo n)) n → Prop)
    (hP : ∀ S A e, P A → P (digitAuditStep ring S A e)) :
    ∀ (word : List (Fin n))
      (w : (BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n) ×
        ((Nat → Nat) × Nat)),
      P w.1.2 → P (word.foldl (windowNext ring hbank root lane src R) w).1.2
  | [], _, h => h
  | e :: word, w, h =>
      auditFold P hP word (windowNext ring hbank root lane src R w e)
        (hP (piD w.1.1.val.1) w.1.2 e h)

/-- The previous window at a just-closed state `wc`: its crossings are recorded on the delimiter
edge into the target block start, with increasing times, and no other export lies between the
first and the last crossing along any continuation (T28 `windowClosingD`, plus destinations). -/
def ChiPrev (wc : (BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n) ×
      ((Nat → Nat) × Nat))
    (chi : Nat → DigitExport (compileAdvice (ceilLogTwo n)) n) : Prop :=
  (∀ i, i < R → DigitRecordedExport wc.1.2 (chi i) ∧ OnEdge ring root lane src R (chi i) ∧
    (chi i).destination = digitSite ring root (src + R)) ∧
  (∀ a b, a < b → b < R → (chi a).time < (chi b).time) ∧
  ∀ (word : List (Fin n)) (x : DigitExport (compileAdvice (ceilLogTwo n)) n),
    DigitRecordedExport (word.foldl (windowNext ring hbank root lane src R) wc).1.2 x →
    OnEdge ring root lane src R x → (chi 0).time ≤ x.time → x.time ≤ (chi (R - 1)).time →
    ∃ i, i < R ∧ x = chi i

/-- **Sample exactness** of a window: crossing `chi i` carries a positive-stamped recorded sample
`samp i` of source cell `src + (R - 1 - i)`, stamped before the crossing, with the sample's value
and tail, the tail set exactly at the last crossing. -/
def ChiSampled (A : DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (chi : Nat → DigitExport (compileAdvice (ceilLogTwo n)) n) : Prop :=
  ∃ samp : Nat → DigitSample (compileAdvice (ceilLogTwo n)) n,
    ∀ i, i < R →
      DigitRecordedSample A (samp i) ∧ (chi i).operand = some (.sampled (samp i).id) ∧
      (samp i).id.lane = lane ∧ (samp i).id.site = digitSite ring root (src + (R - 1 - i)) ∧
      0 < (samp i).id.time ∧ (samp i).id.time < (chi i).time ∧
      (chi i).value = (samp i).value ∧ (chi i).tail = (samp i).tail ∧
      (samp i).tail = decide (R - 1 - i = 0)

/-- **The hclose receipt** (T30 item 2): the terminal goes into the cell after the target
block, and its ledger is clean with `R` uses aimed at the target cells in increasing time
(the shape T28's `LedgerOk` gives a clean ledger, `terminalCleanUses`). Use `j`, made after
the cycle start `t0`, carries the operand, value and tail of the crossing `chi (R - 1 - j)` of
the window that closed one cycle earlier. -/
def CloseUses (t0 : Nat) (U : DigitTerminal (compileAdvice (ceilLogTwo n)) n)
    (chi : Nat → DigitExport (compileAdvice (ceilLogTwo n)) n) : Prop :=
  U.destination = digitSite ring root (src + 2 * R) ∧
  ∃ L : DigitCarryGhost (compileAdvice (ceilLogTwo n)) n,
    U.ledger = some L ∧ L.inherited = none ∧ L.uses.length = R ∧
    UsesOk ring root src R U.time L.uses ∧
    ∀ j (u : DigitUse (compileAdvice (ceilLogTwo n)) n), L.uses[j]? = some u →
      u.operand = (chi (R - 1 - j)).operand ∧ u.value = (chi (R - 1 - j)).value ∧
      u.tail = (chi (R - 1 - j)).tail ∧ t0 < u.time

/-- **The exact missing fact** for T30 item 3, in the shape of `OldCompletion`. At every old-phase
terminal of a cycle started at a just-closed state `wc`, there is a window `chi` closed at `wc`
that is sampled exactly and whose crossings the terminal's uses carry. -/
def HCloseFact (after : Nat) : Prop :=
  ∀ (wc : (BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n) ×
      ((Nat → Nat) × Nat)) (word : List (Fin n))
    (U : DigitTerminal (compileAdvice (ceilLogTwo n)) n),
    JustClosed ring hbank root lane src R Base wc →
    AnchorIn ring root lane src R after wc.1.2 → after ≤ wc.1.2.clock →
    (word.foldl (windowNext ring hbank root lane src R) wc).2.2 = wc.2.2 →
    OrderInv ring hbank root lane src R (word.foldl (windowNext ring hbank root lane src R) wc).1
      (word.foldl (windowNext ring hbank root lane src R) wc).2 wc.1.2.clock →
    DigitRecordedTerminal (word.foldl (windowNext ring hbank root lane src R) wc).1.2 U →
    U.lane = lane → U.source = digitSite ring root (src + (2 * R - 1)) →
    wc.1.2.clock < U.time →
    ∃ chi : Nat → DigitExport (compileAdvice (ceilLogTwo n)) n,
      ChiPrev ring hbank root lane src R wc chi ∧ ChiSampled ring root lane src R wc.1.2 chi ∧
      CloseUses ring root src R wc.1.2.clock U chi

include hn hR hsrc hend in
/-- **Assembly of `DigitCompletion`**: the hclose receipt discharges the open obligation of the
five-cohort transfer. -/
theorem oldCompletionOfClose (after : Nat)
    (h : HCloseFact ring hbank root lane src R Base after) :
    OldCompletion ring hbank root lane src R Base after := by
  intro wc word U hjc hanc haft hcnt hord hU hUl hUs hUt
  obtain ⟨chi, ⟨hrec, hinc, hextra⟩, ⟨samp, hsamp⟩, hUd, L, hL, hLi, hLl, hLu, huse⟩ :=
    h wc word U hjc hanc haft hcnt hord hU hUl hUs hUt
  obtain ⟨t, ht, -⟩ := hanc
  have hpair := ht.1
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

include hn hR hsrc hend in
/-- The five-cohort charge (T30 item 3) with the open obligation replaced by the hclose
receipt. -/
theorem fiveCloseChargeOfClose (after : Nat)
    (h : HCloseFact ring hbank root lane src R Base after)
    (w : (BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n) ×
      ((Nat → Nat) × Nat))
    (hw : WinInvD ring hbank root lane src R Base w.1 w.2) (h0 : w.2.2 = 0)
    (hafter : after ≤ w.1.2.clock) (hanc : AnchorIn ring root lane src R after w.1.2) (T : Nat) :
    2 * costNumerator (windowNext ring hbank root lane src R)
        (fun v => FwdChain ring v.1.2 root src (src + R) lane 5 after) w T ≤
      n ^ T * (200 * n * R) :=
  fiveCloseCharge ring hn hbank root lane src R hR hsrc hend Base after
    (oldCompletionOfClose ring hn hbank root lane src R hR hsrc hend Base after h)
    w hw h0 hafter hanc T

end Close

end L3.HClose

#print axioms L3.HClose.terminalCleanUses
#print axioms L3.HClose.oldCompletionOfClose
#print axioms L3.HClose.fiveCloseChargeOfClose
