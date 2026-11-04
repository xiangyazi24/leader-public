import Leader.L3.Bank.RepairDigitCohortWindow

/-!
# T27 item 4: completion chains and the ghost-sim transfer to `DigitFiveCohortCompletions`

* `completionStep`: a `DigitCompletion` survives every audit letter (receipts persist; the
  no-extra-export clause only looks at exports no later than the completion's terminal).
* `FwdChain A K b`: `K` completions (cut `0`) with strictly increasing terminal times, all after
  `b`. It survives audit letters (`fwdChainStep`), is antitone in `b`, extends by a completion
  stamped after the clock (`fwdChainExtend`), and five of them give the five chained
  `DigitNextCompletion`s of `DigitFiveCohortCompletions` (`fiveNextOfFwd`, via F4).
* `ghostSimTransfer`: `costNumeratorGhostSimLe` on (BANK × audit) × `cohortCycleGhost` with the
  window invariant `WinInv` and any audit-side receipt count `Rec g.2` carried by every letter:
  the first hit of `Rec K` costs at most `K · 39 n R` (doubled), from the cycle-`0` start.
* `fiveCohortTransfer`: the same bound for `∃ last, DigitFiveCohortCompletions …` with
  `K = 5`, given a receipt count whose fifth level yields the five completions.
-/

namespace L3.FiveTransfer

set_option autoImplicit false

open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree
open L3.RenewalReferenceClock
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
open L3.CohortTransfer

/-! ### Completions persist -/

section Completions

variable {c : Compiled} {n : Nat}

/-- A completion survives every audit letter. -/
theorem completionStep (ring : DirectedRing n) (S : Fin n → ProjD c) (A : DigitAudit c n)
    (e : Fin n) (root : Fin n) (source target : Nat) (lane : DigitLane) (cut : Nat)
    (terminal : DigitTerminal c n)
    (h : DigitCompletion ring A root source target lane cut terminal) :
    DigitCompletion ring (digitAuditStep ring S A e) root source target lane cut terminal := by
  obtain ⟨hp, ht, hl, hs, hd, hclk, pos, ledger, samples, exports, uses, h1, h2, h3, hj, hij,
    hother⟩ := h
  refine ⟨hp, ?_, hl, hs, hd, ?_, pos, ledger, samples, exports, uses, h1, h2, h3, ?_, hij, ?_⟩
  · obtain ⟨f, hf, a, b, d⟩ := ht
    exact ⟨f, auditFrameMemStep ring S A e f hf, a, b, d⟩
  · show terminal.time ≤ A.clock + 1
    omega
  · intro j
    obtain ⟨s1, s2, s3, s4, s5, x1, x2, x3, x4, x5, x6, x7, u1, u2, u3, u4, u5, t1, t2, t3⟩ :=
      hj j
    exact ⟨recordedSampleStep ring S A e _ s1, s2, s3, s4, s5,
      recordedExportStep ring S A e _ x1, x2, x3, x4, x5, x6, x7, u1, u2, u3, u4, u5, t1, t2, t3⟩
  · intro other ho o1 o2 o3 o4 o5
    rcases recordedExportStepCases ring S A e other ho with h | ⟨ht', -, -⟩
    · exact hother other h o1 o2 o3 o4 o5
    · exfalso
      obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, t2, t3⟩ := hj ⟨0, pos⟩
      omega

/-- `K` completions with strictly increasing terminal times, all after `b`. -/
def FwdChain (ring : DirectedRing n) (A : DigitAudit c n) (root : Fin n) (source target : Nat)
    (lane : DigitLane) : Nat → Nat → Prop
  | 0, _ => True
  | K + 1, b => ∃ t : DigitTerminal c n, DigitCompletion ring A root source target lane 0 t ∧
      b < t.time ∧ FwdChain ring A root source target lane K t.time

theorem fwdChainSucc (ring : DirectedRing n) (A : DigitAudit c n) (root : Fin n)
    (source target : Nat) (lane : DigitLane) (K b : Nat) :
    FwdChain ring A root source target lane (K + 1) b =
      ∃ t : DigitTerminal c n, DigitCompletion ring A root source target lane 0 t ∧
        b < t.time ∧ FwdChain ring A root source target lane K t.time := rfl

variable {ring : DirectedRing n} {root : Fin n} {source target : Nat} {lane : DigitLane}

theorem fwdChainAnti {A : DigitAudit c n} :
    ∀ K b b', b' ≤ b → FwdChain ring A root source target lane K b →
      FwdChain ring A root source target lane K b' := by
  intro K
  induction K with
  | zero => intro _ _ _ _; exact trivial
  | succ K _ =>
      intro b b' hle h
      rw [fwdChainSucc] at h
      rw [fwdChainSucc]
      obtain ⟨t, ht, hb, hr⟩ := h
      exact ⟨t, ht, by omega, hr⟩

theorem fwdChainStep (S : Fin n → ProjD c) (A : DigitAudit c n) (e : Fin n) :
    ∀ K b, FwdChain ring A root source target lane K b →
      FwdChain ring (digitAuditStep ring S A e) root source target lane K b := by
  intro K
  induction K with
  | zero => intro _ _; exact trivial
  | succ K ih =>
      intro b h
      rw [fwdChainSucc] at h
      rw [fwdChainSucc]
      obtain ⟨t, ht, hb, hr⟩ := h
      exact ⟨t, completionStep ring S A e root source target lane 0 t ht, hb, ih _ hr⟩

/-- A chain extends by one completion stamped after the old clock, in any audit where the old
completions persist. -/
theorem fwdChainExtend {A A' : DigitAudit c n}
    (hmono : ∀ u, DigitCompletion ring A root source target lane 0 u →
      DigitCompletion ring A' root source target lane 0 u)
    (t : DigitTerminal c n) (ht : DigitCompletion ring A' root source target lane 0 t)
    (hlt : A.clock < t.time) :
    ∀ K b, FwdChain ring A root source target lane K b → b ≤ A.clock →
      FwdChain ring A' root source target lane (K + 1) b := by
  intro K
  induction K with
  | zero =>
      intro b _ hb
      rw [fwdChainSucc]
      exact ⟨t, ht, by omega, trivial⟩
  | succ K ih =>
      intro b h hb
      rw [fwdChainSucc] at h
      rw [fwdChainSucc]
      obtain ⟨u, hu, hbu, hr⟩ := h
      exact ⟨u, hmono u hu, hbu, ih u.time hr hu.2.2.2.2.2.1⟩

/-- F4 on a chain: the first link is a `DigitNextCompletion`, and the rest of the chain follows
it. -/
theorem nextOfFwd {A : DigitAudit c n} {K b : Nat}
    (h : FwdChain ring A root source target lane (K + 1) b) :
    ∃ t', DigitNextCompletion ring A root source target lane b t' ∧
      FwdChain ring A root source target lane K t'.time := by
  rw [fwdChainSucc] at h
  obtain ⟨t, ht, hb, hr⟩ := h
  obtain ⟨t', ht'⟩ := nextCompletionExists ring A root source target lane b t ht hb
  exact ⟨t', ht', fwdChainAnti K _ _ (ht'.2.2 t ht hb) hr⟩

/-- Five chained completions after `after` give the five chained next completions of
`DigitFiveCohortCompletions`. -/
theorem fiveNextOfFwd {A : DigitAudit c n} {after : Nat}
    (h : FwdChain ring A root source target lane 5 after) :
    ∃ first second third fourth last : DigitTerminal c n,
      DigitNextCompletion ring A root source target lane after first ∧
      DigitNextCompletion ring A root source target lane first.time second ∧
      DigitNextCompletion ring A root source target lane second.time third ∧
      DigitNextCompletion ring A root source target lane third.time fourth ∧
      DigitNextCompletion ring A root source target lane fourth.time last := by
  obtain ⟨t1, h1, r1⟩ := nextOfFwd h
  obtain ⟨t2, h2, r2⟩ := nextOfFwd r1
  obtain ⟨t3, h3, r3⟩ := nextOfFwd r2
  obtain ⟨t4, h4, r4⟩ := nextOfFwd r3
  obtain ⟨t5, h5, -⟩ := nextOfFwd r4
  exact ⟨t1, t2, t3, t4, t5, h1, h2, h3, h4, h5⟩

/-- `DigitFiveCohortCompletions` from five chained completions and the anchor / serial-rank
receipts of the resulting next completions. -/
theorem fiveCohortOfFwd {A : DigitAudit c n} {after : Nat}
    (h : FwdChain ring A root source target lane 5 after)
    (hrank : ∀ first second third fourth last : DigitTerminal c n,
      DigitNextCompletion ring A root source target lane after first →
      DigitNextCompletion ring A root source target lane first.time second →
      DigitNextCompletion ring A root source target lane second.time third →
      DigitNextCompletion ring A root source target lane third.time fourth →
      DigitNextCompletion ring A root source target lane fourth.time last →
      ∃ (anchor : DigitTerminal c n) (anchorTail : DigitStamp n) (firstRank : Nat),
        DigitAnchor ring A root source target lane anchor anchorTail ∧
        anchor.time ≤ after ∧ 0 < firstRank ∧
        DigitSerialTerminalRanks A lane (digitSite ring root source) anchor anchorTail
          firstRank [first, second, third, fourth, last]) :
    ∃ last, DigitFiveCohortCompletions ring A root source target lane after last := by
  obtain ⟨t1, t2, t3, t4, t5, h1, h2, h3, h4, h5⟩ := fiveNextOfFwd h
  obtain ⟨an, at', fr, ha, hat, hfr, hs⟩ := hrank t1 t2 t3 t4 t5 h1 h2 h3 h4 h5
  exact ⟨t5, t1, t2, t3, t4, an, at', fr, h1, h2, h3, h4, h5, ha, hat, hfr, hs⟩

end Completions

/-! ### The transfer on (BANK × audit) × cycle ghost -/

section Transfer

variable {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
  (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) (root : Fin n) (lane : DigitLane)
  (src R : Nat) (hR : 2 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n)

include hn hR hsrc hend in
/-- **Ghost-sim transfer**: let `Rec j` be a receipt count on the coupled state carried by every
letter together with the arrival counter of the cycle ghost (on the window invariant). From the
cycle-`0` start, the first hit of `Rec K` on the coupled chain `bankRepairDigitBoundaryAuditNext`
costs at most `K · 39 n R` (doubled), the T25 bound of `cohortCycleChainCharge`. -/
theorem ghostSimTransfer
    (Rec : Nat → BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n →
      Prop)
    (hrec : ∀ z g e, WinInv ring hbank root lane src R z g → Rec g.2 z →
      Rec (windowGhost ring hbank root lane src R z g e).2
        (bankRepairDigitBoundaryAuditNext ring hbank z e))
    (K : Nat) (z : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (hw : WinInv ring hbank root lane src R z ((fun _ => 0), 0))
    (hst : CohortCycStart R 0 (cohortProj ring root lane src R (piD z.1.val.1))
      ((fun _ => 0), 0))
    (h0 : Rec 0 z) (T : Nat) :
    2 * costNumerator (bankRepairDigitBoundaryAuditNext ring hbank) (Rec K) z T ≤
      n ^ T * (K * (39 * n * R)) := by
  have hstep : ∀ (z : BankReferenceState ring hbank ×
        DigitAudit (compileAdvice (ceilLogTwo n)) n) (g : (Nat → Nat) × Nat)
      (y : BankReferenceState ring hbank × ((Nat → Nat) × Nat)) (e : Fin n),
      (y = (z.1, g) ∧ WinInv ring hbank root lane src R z g ∧ Rec g.2 z) → ¬ Rec K z →
      (cohortCycleNext ring hbank root lane src R y e =
          ((bankRepairDigitBoundaryAuditNext ring hbank z e).1,
            windowGhost ring hbank root lane src R z g e) ∧
        WinInv ring hbank root lane src R (bankRepairDigitBoundaryAuditNext ring hbank z e)
          (windowGhost ring hbank root lane src R z g e) ∧
        Rec (windowGhost ring hbank root lane src R z g e).2
          (bankRepairDigitBoundaryAuditNext ring hbank z e)) := by
    intro z g y e h _
    obtain ⟨rfl, hw, hr⟩ := h
    exact ⟨rfl, (winInvStep ring hn hbank root lane src R hR hsrc hend z g hw e).1,
      hrec z g e hw hr⟩
  have hgood : ∀ (z : BankReferenceState ring hbank ×
        DigitAudit (compileAdvice (ceilLogTwo n)) n) (g : (Nat → Nat) × Nat)
      (y : BankReferenceState ring hbank × ((Nat → Nat) × Nat)),
      (y = (z.1, g) ∧ WinInv ring hbank root lane src R z g ∧ Rec g.2 z) →
      (CohortLayout ring hbank root src R y.1 ∧
        CohortCycStart R K (cohortProj ring root lane src R (piD y.1.val.1)) y.2) → Rec K z := by
    intro z g y h hy
    obtain ⟨rfl, -, hr⟩ := h
    have hk : g.2 = K := hy.2.1
    rw [← hk]
    exact hr
  have hsim := costNumeratorGhostSimLe (bankRepairDigitBoundaryAuditNext ring hbank)
    (windowGhost ring hbank root lane src R) (cohortCycleNext ring hbank root lane src R)
    (fun w y => y = (w.1.1, w.2) ∧ WinInv ring hbank root lane src R w.1 w.2 ∧ Rec w.2.2 w.1)
    (Rec K)
    (fun y => CohortLayout ring hbank root src R y.1 ∧
      CohortCycStart R K (cohortProj ring root lane src R (piD y.1.val.1)) y.2)
    hstep hgood T z ((fun _ => 0), 0) (z.1, ((fun _ => 0), 0)) ⟨rfl, hw, h0⟩
  have hcost := cohortCycleChainCharge ring hn hbank root lane src R hR hsrc hend K
    (z.1, ((fun _ => 0), 0)) ⟨hw.1, hst⟩ T
  exact Nat.le_trans (Nat.mul_le_mul_left 2 hsim) hcost

/-- First-hit cost is antitone in the target. -/
theorem costTargetMono {X : Type} (next : X → Fin n → X) (P Q : X → Prop)
    (hPQ : ∀ x, P x → Q x) (x : X) (T : Nat) :
    costNumerator next Q x T ≤ costNumerator next P x T :=
  costNumeratorSimLe next next (fun a b => a = b) Q P (fun a b e h _ => by rw [h])
    (fun a b h hb => by subst h; exact hPQ a hb) T x x rfl

include hn hR hsrc hend in
/-- **Transfer to `DigitFiveCohortCompletions`**: given a receipt count `Rec` carried by every
letter with the cycle ghost's arrival counter, whose fifth level yields
`DigitFiveCohortCompletions` on the pair `(src, src + R)` after `after`, the first hit of
`∃ last, DigitFiveCohortCompletions … after last` on the coupled chain costs at most
`5 · 39 n R` (doubled) from the cycle-`0` start. This is the charge for the `hc` argument of
`DigitValueChain.next` (Target.lean:2269). -/
theorem fiveCohortTransfer
    (Rec : Nat → BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n →
      Prop)
    (hrec : ∀ z g e, WinInv ring hbank root lane src R z g → Rec g.2 z →
      Rec (windowGhost ring hbank root lane src R z g e).2
        (bankRepairDigitBoundaryAuditNext ring hbank z e))
    (after : Nat)
    (hfive : ∀ z, Rec 5 z →
      ∃ last, DigitFiveCohortCompletions ring z.2 root src (src + R) lane after last)
    (z : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (hw : WinInv ring hbank root lane src R z ((fun _ => 0), 0))
    (hst : CohortCycStart R 0 (cohortProj ring root lane src R (piD z.1.val.1))
      ((fun _ => 0), 0))
    (h0 : Rec 0 z) (T : Nat) :
    2 * costNumerator (bankRepairDigitBoundaryAuditNext ring hbank)
        (fun z => ∃ last, DigitFiveCohortCompletions ring z.2 root src (src + R) lane after last)
        z T ≤ n ^ T * (5 * (39 * n * R)) :=
  Nat.le_trans (Nat.mul_le_mul_left 2 (costTargetMono _ (Rec 5) _ hfive z T))
    (ghostSimTransfer ring hn hbank root lane src R hR hsrc hend Rec hrec 5 z hw hst h0 T)

include hn hR hsrc hend in
/-- **Concrete form with the completion chain.** The receipt count is `FwdChain (g.2 - 1)` after
`after` (the cohort closing cycle `j` reaches its terminal only after the closing letter, so the
count lags the arrival counter by one). Every letter keeps it (`fwdChainStep`) except possibly a
closing letter; the single obligation `hclose` asks that when a letter advances the counter from
`j` to `j + 1`, the new audit records `j` chained completions after `after`. With the anchor /
serial-rank receipts `hrank`, the sixth arrival yields `DigitFiveCohortCompletions`, at cost
`6 · 39 n R` (doubled). -/
theorem chainTransfer (after : Nat)
    (hclose : ∀ z g e, WinInv ring hbank root lane src R z g →
      FwdChain ring z.2 root src (src + R) lane (g.2 - 1) after →
      (windowGhost ring hbank root lane src R z g e).2 = g.2 + 1 →
      FwdChain ring (bankRepairDigitBoundaryAuditNext ring hbank z e).2 root src (src + R) lane
        g.2 after)
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
    (z : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (hw : WinInv ring hbank root lane src R z ((fun _ => 0), 0))
    (hst : CohortCycStart R 0 (cohortProj ring root lane src R (piD z.1.val.1))
      ((fun _ => 0), 0)) (T : Nat) :
    2 * costNumerator (bankRepairDigitBoundaryAuditNext ring hbank)
        (fun z => ∃ last, DigitFiveCohortCompletions ring z.2 root src (src + R) lane after last)
        z T ≤ n ^ T * (6 * (39 * n * R)) := by
  let Rec : Nat → BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n →
      Prop := fun j z => FwdChain ring z.2 root src (src + R) lane (j - 1) after
  have hrec : ∀ z g e, WinInv ring hbank root lane src R z g → Rec g.2 z →
      Rec (windowGhost ring hbank root lane src R z g e).2
        (bankRepairDigitBoundaryAuditNext ring hbank z e) := by
    intro z g e hw hr
    rcases (winInvStep ring hn hbank root lane src R hR hsrc hend z g hw e).2 with hs | ⟨hs, -⟩
    · show FwdChain ring (digitAuditStep ring (piD z.1.val.1) z.2 e) root src (src + R) lane
        ((windowGhost ring hbank root lane src R z g e).2 - 1) after
      rw [hs]
      exact fwdChainStep (piD z.1.val.1) z.2 e _ _ hr
    · show FwdChain ring (bankRepairDigitBoundaryAuditNext ring hbank z e).2 root src (src + R)
        lane ((windowGhost ring hbank root lane src R z g e).2 - 1) after
      rw [hs, Nat.add_sub_cancel]
      exact hclose z g e hw hr hs
  have hfive : ∀ z, Rec 6 z →
      ∃ last, DigitFiveCohortCompletions ring z.2 root src (src + R) lane after last :=
    fun z h => fiveCohortOfFwd h (hrank z.2)
  exact Nat.le_trans (Nat.mul_le_mul_left 2 (costTargetMono _ (Rec 6) _ hfive z T))
    (ghostSimTransfer ring hn hbank root lane src R hR hsrc hend Rec hrec 6 z hw hst trivial T)

end Transfer

end L3.FiveTransfer

#print axioms L3.FiveTransfer.completionStep
#print axioms L3.FiveTransfer.fiveCohortOfFwd
#print axioms L3.FiveTransfer.ghostSimTransfer
#print axioms L3.FiveTransfer.fiveCohortTransfer
#print axioms L3.FiveTransfer.chainTransfer
