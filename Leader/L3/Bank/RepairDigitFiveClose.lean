import Leader.L3.Bank.RepairDigitCohortOrder
import Leader.L3.Bank.RepairDigitFiveTransfer
import Leader.L3.Bank.RepairDigitProjection

/-!
# T30 item 3: the five-cohort transfer with recorded terminals

One interior complete pair and one lane, on the coupled chain `windowNext` (BANK × audit ×
cycle ghost), from a block start with arrival counter `0` (any phase; T30 item 1).

* `FwdIn A K b t1`: `K` completions (cut `0`) with increasing terminal times in `(b, t1)`.
  Unlike T27's `FwdChain` it records that **every chain terminal is before `t1`**, so a terminal
  recorded after the current cycle start can be appended (`fwdInAppend`). This avoids the
  clock trap of `fwdChainExtend` (whose clock bound fails at a closing letter, where the old
  cohort's terminal is already recorded).
* `genPhaseDone`: the old phase of the generated class is unique at the end: a lane in phase
  `o ≤ 2R` is not also in phase `2R + 1` with the same chosen ghost. So the model's "old cohort
  gone" agrees with the phase carried by T28's `OrderInv`.
* `FiveInv after`: in the entrance cycle (counter `0`) only `after ≤ clock`; from the entrance
  closing letter on, the current cycle's start state `wc` is `JustClosed` (T30 item 1), the
  state is reached from `wc` by a word without closing letters, T28's `OrderInv` holds with cycle
  start `clock(wc)`, and `FwdIn (counter - 1) after clock(wc)`.
* `OldCompletion`: **the one open obligation** (T30 item 2 plus the assembly): in a cycle started
  at a just-closed state `wc`, a terminal on the terminal edge recorded after `clock(wc)` is a
  `DigitCompletion`.
* `fiveInvStep`, `fiveGood`: `FiveInv` is carried by every letter; when the old cohort of cycle
  `5` is gone, `FwdChain 5 after` holds.
* `fiveCloseCharge`: from every block start the first `FwdChain 5 after` costs `≤ 200 n R`
  doubled (entrance `39 n R`, four cycles, the fifth old phase). `fiveCohortCloseCharge`: the
  same for `∃ last, DigitFiveCohortCompletions … after last` given T27's `hrank`.
  `fiveCoupledBlock`: the per-block clock in the form of T30 item 5.
-/

namespace L3.FiveClose

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
open L3.CohortOrder
open L3.FiveTransfer
open L3.BlockStart
open L3.Projection

/-! ### Completion chains bounded above -/

section Chains

variable {c : Compiled} {n : Nat}

/-- `K` completions with strictly increasing terminal times, all in `(b, t1)`. -/
def FwdIn (ring : DirectedRing n) (root : Fin n) (source target : Nat) (lane : DigitLane)
    (A : DigitAudit c n) : Nat → Nat → Nat → Prop
  | 0, _, _ => True
  | K + 1, b, t1 => ∃ t : DigitTerminal c n, DigitCompletion ring A root source target lane 0 t ∧
      b < t.time ∧ t.time < t1 ∧ FwdIn ring root source target lane A K t.time t1

variable (ring : DirectedRing n) (root : Fin n) (source target : Nat) (lane : DigitLane)

theorem fwdInSucc (A : DigitAudit c n) (K b t1 : Nat) :
    FwdIn ring root source target lane A (K + 1) b t1 =
      ∃ t : DigitTerminal c n, DigitCompletion ring A root source target lane 0 t ∧
        b < t.time ∧ t.time < t1 ∧ FwdIn ring root source target lane A K t.time t1 := rfl

theorem fwdInChain (A : DigitAudit c n) :
    ∀ K b t1, FwdIn ring root source target lane A K b t1 →
      FwdChain ring A root source target lane K b := by
  intro K
  induction K with
  | zero => intro _ _ _; exact trivial
  | succ K ih =>
      intro b t1 h
      rw [fwdInSucc] at h
      rw [fwdChainSucc]
      obtain ⟨t, ht, hb, -, hr⟩ := h
      exact ⟨t, ht, hb, ih _ _ hr⟩

theorem fwdInStep (S : Fin n → ProjD c) (A : DigitAudit c n) (e : Fin n) :
    ∀ K b t1, FwdIn ring root source target lane A K b t1 →
      FwdIn ring root source target lane (digitAuditStep ring S A e) K b t1 := by
  intro K
  induction K with
  | zero => intro _ _ _; exact trivial
  | succ K ih =>
      intro b t1 h
      rw [fwdInSucc] at h
      rw [fwdInSucc]
      obtain ⟨t, ht, hb, ht1, hr⟩ := h
      exact ⟨t, completionStep ring S A e root source target lane 0 t ht, hb, ht1, ih _ _ hr⟩

/-- **Append**: a chain below `t0` extends by a completion stamped after `t0` (and before
`t1 ≥ t0`). -/
theorem fwdInAppend {A : DigitAudit c n} (u : DigitTerminal c n)
    (hu : DigitCompletion ring A root source target lane 0 u) :
    ∀ K b t0 t1, FwdIn ring root source target lane A K b t0 → b ≤ t0 → t0 < u.time →
      u.time < t1 → t0 ≤ t1 → FwdIn ring root source target lane A (K + 1) b t1 := by
  intro K
  induction K with
  | zero =>
      intro b t0 t1 _ hb hu0 hu1 _
      rw [fwdInSucc]
      exact ⟨u, hu, by omega, hu1, trivial⟩
  | succ K ih =>
      intro b t0 t1 h hb hu0 hu1 h01
      rw [fwdInSucc] at h
      rw [fwdInSucc]
      obtain ⟨t, ht, htb, ht0, hr⟩ := h
      exact ⟨t, ht, htb, by omega, ih t.time t0 t1 hr (by omega) hu0 hu1 h01⟩

end Chains

/-! ### The old phase is unique at the end -/

section Phase

variable {R o : Nat} {s : CohortLane} {lam : Nat → Nat}

/-- A lane of the generated class in old phase `o ≤ 2R` cannot carry the same chosen cohort
below cell `2R` with all of the old region empty: the old cohort's arrived packet (settlement)
or its live carry (carry phase) occupies a cell the chosen cohort does not. -/
theorem genPhaseDone (h : CohortGen R s lam o) (ho : o ≤ 2 * R)
    (hc : CohortChosen R s lam (2 * R)) : False := by
  have hR := h.2.two
  have hpre := cohortGenPre h ho
  by_cases hoR : o ≤ R
  · have hold := h.1
    rw [cohortOldSettle hoR] at hold
    have hlow := h.2.low
    rw [cohortBottomSettle hoR] at hlow
    have ht := hc.gap (2 * R - 1) (by omega) (by omega)
      (fun i hi he => by have := hlow i hi; omega)
    have ha := hold.1 0 (by omega)
    rw [Nat.sub_zero] at ha
    rcases ha with ha | ha <;> rw [ht] at ha <;> cases ha
  · have hold := h.1
    rw [cohortOldCarry (by omega) ho, cohortCarryMid (by omega) (by omega)] at hold
    have hlive := hold.1
    rw [show R + (o - R) - 1 = o - 1 by omega] at hlive
    have hlow := h.2.low
    rw [cohortBottomCarry (by omega)] at hlow
    have ht := hc.gap (o - 1) (by omega) (by omega)
      (fun i hi he => by have := hlow i hi; omega)
    rw [cohortTokTgt s (by omega : R ≤ o - 1)] at ht
    unfold cohortTokIn at ht
    rw [hlive] at ht
    simp at ht

/-- The cycle class in phase `2R + 1` and in phase `o` (same lane, same ghost) forces
`o = 2R + 1`. -/
theorem cycPhaseDone {j o' : Nat} {g : (Nat → Nat) × Nat}
    (h1 : CohortCycIn R j s g (2 * R + 1)) (h2 : CohortCycIn R o' s g o) : o = 2 * R + 1 := by
  have hle := cohortOldLe h2.2.1.1
  rcases Nat.lt_or_ge o (2 * R + 1) with hlt | hge
  · have hc := h1.2.1.2
    rw [cohortBottomCarry (by omega), show 2 * R + 1 - 1 = 2 * R by omega] at hc
    exact (genPhaseDone h2.2.1 (by omega) hc).elim
  · omega

end Phase

/-! ### The five-cohort invariant on the coupled chain -/

section Five

variable {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
  (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) (root : Fin n) (lane : DigitLane)
  (src R : Nat) (hR : 2 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n)
  (Base : Bool → DigitAtom n → Prop)

/-- A completion of the pair (cut `0`) with terminal at or before `after` is recorded: the
anchor side of the block (the cohorts after it were read inside the audit). -/
def AnchorIn (after : Nat) (A : DigitAudit (compileAdvice (ceilLogTwo n)) n) : Prop :=
  ∃ t : DigitTerminal (compileAdvice (ceilLogTwo n)) n,
    DigitCompletion ring A root src (src + R) lane 0 t ∧ t.time ≤ after

theorem anchorInStep (after : Nat) (S : Fin n → ProjD (compileAdvice (ceilLogTwo n)))
    (A : DigitAudit (compileAdvice (ceilLogTwo n)) n) (e : Fin n)
    (h : AnchorIn ring root lane src R after A) :
    AnchorIn ring root lane src R after (digitAuditStep ring S A e) := by
  obtain ⟨t, ht, hle⟩ := h
  exact ⟨t, completionStep ring S A e root src (src + R) lane 0 t ht, hle⟩

/-- **The open obligation** (T30 item 2 and the assembly of `DigitCompletion`): in a cycle
started at a just-closed state `wc` after the anchor and not closed since, a terminal on the
terminal edge recorded after the cycle start `clock(wc)` is a completion of the pair. -/
def OldCompletion (after : Nat) : Prop :=
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
    DigitCompletion ring (word.foldl (windowNext ring hbank root lane src R) wc).1.2 root src
      (src + R) lane 0 U

/-- **The five-cohort invariant** with recorded terminals: entrance cycle (counter `0`), or a
cycle started at a just-closed state `wc` with the order invariant at cycle start `clock(wc)`
and `counter - 1` completions after `after`, every terminal before `clock(wc)`. -/
def FiveInv (after : Nat)
    (w : (BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n) ×
      ((Nat → Nat) × Nat)) : Prop :=
  (w.2.2 = 0 ∧ after ≤ w.1.2.clock ∧ AnchorIn ring root lane src R after w.1.2) ∨
  (1 ≤ w.2.2 ∧ ∃ (wc : (BankReferenceState ring hbank ×
      DigitAudit (compileAdvice (ceilLogTwo n)) n) × ((Nat → Nat) × Nat)) (word : List (Fin n)),
    JustClosed ring hbank root lane src R Base wc ∧
    w = word.foldl (windowNext ring hbank root lane src R) wc ∧ wc.2.2 = w.2.2 ∧
    OrderInv ring hbank root lane src R w.1 w.2 wc.1.2.clock ∧ after ≤ wc.1.2.clock ∧
    AnchorIn ring root lane src R after wc.1.2 ∧ AnchorIn ring root lane src R after w.1.2 ∧
    FwdIn ring root src (src + R) lane w.1.2 (w.2.2 - 1) after wc.1.2.clock)

include hn hR hsrc hend in
/-- `FiveInv` is carried by every letter. At a closing letter in cycle `j ≥ 1` the old cohort's
terminal (T28's `orderClosing`, recorded after the cycle start) is appended through
`OldCompletion`. -/
theorem fiveInvStep (after : Nat) (hcomp : OldCompletion ring hbank root lane src R Base after)
    (w : (BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n) ×
      ((Nat → Nat) × Nat)) (e : Fin n)
    (hw : WinInvD ring hbank root lane src R Base w.1 w.2)
    (hi : FiveInv ring hbank root lane src R Base after w) :
    FiveInv ring hbank root lane src R Base after (windowNext ring hbank root lane src R w e) := by
  have hclk : (windowNext ring hbank root lane src R w e).1.2.clock = w.1.2.clock + 1 := rfl
  rcases hi with ⟨h0, ha, hanc⟩ | ⟨h1, wc, word, hjc, hweq, hcnt, hord, haft, hancc, hanc, hfwd⟩
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
      refine ⟨?_, windowNext ring hbank root lane src R w e, [], hjc', rfl, rfl,
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
      refine ⟨?_, wc, word ++ [e], hjc, ?_, ?_, hord', haft, hancc,
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
      have hcU := hcomp wc word U hjc hancc haft (by rw [← hweq]; exact hcnt.symm)
        (by rw [← hweq]; exact hord) (by rw [← hweq]; exact hU) hUl hUs hUt
      rw [← hweq] at hcU
      have h01 := hord.2.1
      refine ⟨?_, windowNext ring hbank root lane src R w e, [], hjc', rfl, rfl, hord',
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

/-- When the old cohort of cycle `5` is gone (the model target of item 1's block), five chained
completions after `after` are recorded. -/
theorem fiveGood (after : Nat) (hcomp : OldCompletion ring hbank root lane src R Base after)
    (w : (BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n) ×
      ((Nat → Nat) × Nat))
    (hi : FiveInv ring hbank root lane src R Base after w)
    (hb : CohortLayout ring hbank root src R w.1.1 ∧
      CohortCycOld R 5 (2 * R + 1) (cohortProj ring root lane src R (piD w.1.1.val.1)) w.2) :
    FwdChain ring w.1.2 root src (src + R) lane 5 after := by
  obtain ⟨-, hold⟩ := hb
  rcases hi with ⟨h0, -⟩ | ⟨-, wc, word, hjc, hweq, hcnt, hord, haft, hancc, -, hfwd⟩
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
      have hcU := hcomp wc word U hjc hancc haft (by rw [← hweq]; exact hcnt.symm)
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
/-- **The five-cohort transfer with recorded terminals**: from a block start (strengthened window
invariant, arrival counter `0`, `after ≤ clock`), the first state with five chained completions
after `after` costs `≤ 200 n R` doubled on `windowNext`, given the open obligation
`OldCompletion`. -/
theorem fiveCloseCharge (after : Nat) (hcomp : OldCompletion ring hbank root lane src R Base after)
    (w : (BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n) ×
      ((Nat → Nat) × Nat))
    (hw : WinInvD ring hbank root lane src R Base w.1 w.2) (h0 : w.2.2 = 0)
    (hafter : after ≤ w.1.2.clock) (hanc : AnchorIn ring root lane src R after w.1.2) (T : Nat) :
    2 * costNumerator (windowNext ring hbank root lane src R)
        (fun v => FwdChain ring v.1.2 root src (src + R) lane 5 after) w T ≤
      n ^ T * (200 * n * R) :=
  blockCharge ring hn hbank root lane src R hR hsrc hend Base
    (FiveInv ring hbank root lane src R Base after)
    (fun v => FwdChain ring v.1.2 root src (src + R) lane 5 after)
    (fun v e hv hi _ => fiveInvStep ring hn hbank root lane src R hR hsrc hend Base after hcomp
      v e hv hi) 0
    (fun v _ hi hb => fiveGood ring hbank root lane src R Base after hcomp v hi hb) w hw
    (Or.inl ⟨h0, hafter, hanc⟩) h0 T

include hn hR hsrc hend in
/-- The same charge for `∃ last, DigitFiveCohortCompletions … after last`, given T27's anchor /
serial-rank receipts `hrank`. -/
theorem fiveCohortCloseCharge (after : Nat)
    (hcomp : OldCompletion ring hbank root lane src R Base after)
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
    (hw : WinInvD ring hbank root lane src R Base w.1 w.2) (h0 : w.2.2 = 0)
    (hafter : after ≤ w.1.2.clock) (hanc : AnchorIn ring root lane src R after w.1.2) (T : Nat) :
    2 * costNumerator (windowNext ring hbank root lane src R)
        (fun v => ∃ last, DigitFiveCohortCompletions ring v.1.2 root src (src + R) lane after last)
        w T ≤ n ^ T * (200 * n * R) :=
  Nat.le_trans (Nat.mul_le_mul_left 2 (costTargetMono _
      (fun v => FwdChain ring v.1.2 root src (src + R) lane 5 after) _
      (fun v h => fiveCohortOfFwd h (hrank v.1.2)) w T))
    (fiveCloseCharge ring hn hbank root lane src R hR hsrc hend Base after hcomp w hw h0 hafter
      hanc T)

include hn hR hsrc hend in
/-- **The per-block clock** (T30 item 5 form): every physical block start lifting to a block
start of `FiveInv`, and five chained completions projecting into the block finish, give a
coupled block of charge `200 n R`. -/
theorem fiveCoupledBlock (after : Nat) (hcomp : OldCompletion ring hbank root lane src R Base after)
    (P Q : BankReferenceState ring hbank → Prop)
    (hA : ∀ z, P z → ∃ w : (BankReferenceState ring hbank ×
        DigitAudit (compileAdvice (ceilLogTwo n)) n) × ((Nat → Nat) × Nat),
      w.1.1 = z ∧ (WinInvD ring hbank root lane src R Base w.1 w.2 ∧
        FiveInv ring hbank root lane src R Base after w ∧ w.2.2 = 0))
    (hB : ∀ w : (BankReferenceState ring hbank ×
        DigitAudit (compileAdvice (ceilLogTwo n)) n) × ((Nat → Nat) × Nat),
      FwdChain ring w.1.2 root src (src + R) lane 5 after → Q w.1.1) :
    CoupledBlock ring hbank P Q (200 * n * R) :=
  windowCoupledBlock ring hn hbank root lane src R hR hsrc hend Base P Q
    (FiveInv ring hbank root lane src R Base after)
    (fun v => FwdChain ring v.1.2 root src (src + R) lane 5 after)
    (fun v e hv hi _ => fiveInvStep ring hn hbank root lane src R hR hsrc hend Base after hcomp
      v e hv hi)
    (fun v _ hi hb => fiveGood ring hbank root lane src R Base after hcomp v hi hb) hA hB

end Five

end L3.FiveClose

#print axioms L3.FiveClose.fwdInAppend
#print axioms L3.FiveClose.genPhaseDone
#print axioms L3.FiveClose.cycPhaseDone
#print axioms L3.FiveClose.fiveInvStep
#print axioms L3.FiveClose.fiveGood
#print axioms L3.FiveClose.fiveCloseCharge
#print axioms L3.FiveClose.fiveCohortCloseCharge
#print axioms L3.FiveClose.fiveCoupledBlock
