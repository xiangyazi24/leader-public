import Leader.L3.StageM.EntryCyc
import Leader.L3.Width.DigitWriterOrder

/-!
# Succession: no border tail between the tails of consecutive completions

`DigitSerialTerminalRanks` for consecutive next completions needs that no border tail is sampled
strictly between their tail samples.  The proof runs the pinned cycle chain (`widthWindowNext`,
`WidthWinInvD`, `WidthUseReach`) from the state right after the export of the earlier completion's
tail sample (`wCycStartAtTail`, the state of `L3.StageMEntryCyc.wCycStartOfCompletion` with the
time named):

* `borderExportDone`: an export on the delimiter edge carrying a border sample closes the current
  cycle (the crossed slot is the tail slot, and the tail crossing is the grid done);
* `closeEdgeLow`: a closing letter is a source-block letter, so no terminal is recorded by it;
* `headExport`: a terminal recorded in a cycle after a closure reads the operand of the closed
  window's last crossing, later than the pin;
* `CycFacts`, `cycFactsStep`: the run invariant: the first closure `t1` after the pin; every head
  terminal after `t1` reads a sample exported after the pin; between two border exports after the
  pin a completion lies after `t1` (`widthOrderInvStep`, `widthOldCompletionPairReach`);
* `noTailBetween`: for consecutive completions, no recorded border sample lies strictly between
  their tails: such a sample would be exported between the two tail exports, hence a completion
  between the two terminals, against "next".

Model check: research/lean-l3/ledgers/close-mc.py clauses `fifo`, `c_next`, `c_term` (R <= 3).
-/

namespace L3.WriterCycle

set_option autoImplicit false
set_option linter.unusedSectionVars false

open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree
open L3
open L3.RenewalReferenceClock
open L3.WidthDigit
open L3.WidthWave
open L3.WidthPacketMoment
open L3.WidthPacketMomentCutEntry
open L3.WidthPacketMomentCompare
open L3.WidthPacketMomentGroupCompletion
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
open L3.SitePin
open L3.DigitEntryPhase
open L3.ValueWaveClose
open L3.StageMEntry
open L3.StageMEntryPin
open L3.StageMEntryRun
open L3.StageMEntryCarryRows
open L3.StageMEntryPack
open L3.StageMEntryCyc
open L3.PairBlock
open L3.FiveTransfer
open L3.TailChain
open L3.TailAhead
open L3.CloseRank
open L3.CloseOrder
open L3.WriterOrder
open L3.CohortOrder

/-! ### The chain letters -/

section Chain

variable {n : Nat} {ring : DirectedRing n} (ref : WidthDigitReference ring)
    (hfix : ∀ (root : Fin n) (z : ref.State), ref.singleton root z →
      WFixedRoot ring root (piW (ref.phys z))) (hn : 5 ≤ n)
  (root : Fin n) (lane : DigitLane)
  (src R : Nat) (hR : 2 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n)
  (Base : Bool → DigitAtom n → Prop)

/-- A recorded export on the delimiter edge, after `T`, carrying a border sample.  Consumer:
`CycFacts`, `noTailBetween`. -/
def BorderExport (A : DigitAudit (compileAdvice (ceilLogTwo n)) n) (T : Nat)
    (x : DigitExport (compileAdvice (ceilLogTwo n)) n) : Prop :=
  DigitRecordedExport A x ∧ OnEdge ring root lane src R x ∧ T < x.time ∧
    ∃ sid : DigitStamp n, x.operand = some (.sampled sid) ∧ sid.site = digitSite ring root src

/-- The ghost of one chain letter: a closing letter restarts it and raises the counter, any other
letter is the generated ghost with the same counter.  Consumer: `cycFactsStep`. -/
theorem windowGhostCases
    (w : (ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n) × ((Nat → Nat) × Nat))
    (e : Fin n) :
    (gridDone R R (cohortGenStep R (cohortProj ring root lane src R (piD (ref.phys w.1.1))) w.2.1
        (cohortEdgeOf root src R e)) ∧
      (widthWindowNext ref root lane src R w e).2 = ((fun _ => 0), w.2.2 + 1)) ∨
    (¬ gridDone R R (cohortGenStep R (cohortProj ring root lane src R (piD (ref.phys w.1.1))) w.2.1
        (cohortEdgeOf root src R e)) ∧
      (widthWindowNext ref root lane src R w e).2 =
        (cohortGenStep R (cohortProj ring root lane src R (piD (ref.phys w.1.1))) w.2.1
          (cohortEdgeOf root src R e), w.2.2)) := by
  have hg : (widthWindowNext ref root lane src R w e).2 =
      cohortCycleGhost R (cohortProj ring root lane src R (piD (ref.phys w.1.1))) w.2
        (cohortEdgeOf root src R e) := rfl
  rw [hg]
  unfold cohortCycleGhost
  by_cases hd : gridDone R R (cohortGenStep R (cohortProj ring root lane src R (piD (ref.phys w.1.1)))
      w.2.1 (cohortEdgeOf root src R e))
  · left
    exact ⟨hd, if_pos hd⟩
  · right
    exact ⟨hd, if_neg hd⟩

/-- **A closing letter is a source-block letter**: the tail slot hops at its own cell, below `R`.
Consumer: `cycFactsStep` (a closing letter records no terminal on the terminal edge). -/
theorem closeEdgeLow
    (w : (ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n) × ((Nat → Nat) × Nat))
    (hw : WidthWinInvD ref root lane src R Base w.1 w.2) (e : Fin n)
    (hd : gridDone R R (cohortGenStep R (cohortProj ring root lane src R (piD (ref.phys w.1.1)))
      w.2.1 (cohortEdgeOf root src R e))) :
    ∃ k, k < R ∧ cohortEdgeOf root src R e = some k := by
  obtain ⟨-, -, -, ⟨o, hcyc⟩, -⟩ := hw
  obtain ⟨-, hg, -, hnd⟩ := hcyc
  have ht := tailLt hg.2 hnd
  have hge := hd (R - 1) (by omega)
  rcases genStepCases (R := R) (s := cohortProj ring root lane src R (piD (ref.phys w.1.1)))
      (lam := w.2.1) (cohortEdgeOf root src R e) (R - 1) with h | ⟨hk, -⟩
  · omega
  · refine ⟨_, ?_, hk⟩
    unfold cohortPos
    omega

include hfix hn hR hsrc hend in
/-- **An export of a border sample closes the cycle**: if the letter does not complete the grid,
the export is a crossed slot of the window, whose sample sits at its home cell (`ChiInv`), so the
slot is the tail slot, and a crossed tail slot completes the grid.  Consumer: `cycFactsStep`. -/
theorem borderExportDone
    (w : (ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n) × ((Nat → Nat) × Nat))
    (hw : WidthWinInvD ref root lane src R Base w.1 w.2)
    (hp : WidthPinState ref root lane src R w) (e : Fin n)
    (hnd : ¬ gridDone R R (cohortGenStep R (cohortProj ring root lane src R (piD (ref.phys w.1.1)))
      w.2.1 (cohortEdgeOf root src R e)))
    (x : DigitExport (compileAdvice (ceilLogTwo n)) n)
    (hx : DigitRecordedExport (digitAuditStep ring (piD (ref.phys w.1.1)) w.1.2 e) x)
    (ho : OnEdge ring root lane src R x) (ht : w.1.2.clock < x.time) (sid : DigitStamp n)
    (hop : x.operand = some (.sampled sid)) (hsi : sid.site = digitSite ring root src) : False := by
  obtain ⟨-, -, hWs, hXs⟩ := widthWindowPinFacts ref hfix hn root lane src R hR hsrc hend Base w hw e
  obtain ⟨hC, -, chi, t0, hcw, hci, -⟩ := hp
  have hw' := hWs chi t0 hcw
  have hci' := hXs chi hC hci
  obtain ⟨i, hi, hc, rfl⟩ := hw'.2.1 x hx ho (by have := hcw.1; omega)
  obtain ⟨a, ha, s, h1, -, -, h4, -⟩ := hci' i hi hc
  rw [ha, h1] at hop
  simp only [Option.some.injEq, DigitAtom.sampled.injEq] at hop
  rw [hop, hsi] at h4
  have hR0 := bankRepairDigitSiteInj ring root (by omega) (by omega) h4
  have hiR : i = R - 1 := by omega
  subst hiR
  obtain ⟨-, hg, hY, hnd0⟩ := (show CohortCycIn R w.2.2 (cohortProj ring root lane src R
    (piD (ref.phys w.1.1))) w.2 _ from hw.2.2.2.1.choose_spec)
  obtain ⟨o', -, hg', -, -⟩ := cohortGenStepClosed hg hY hnd0 (cohortEdgeOf root src R e)
  apply hnd
  intro i hi
  have h5 := chosenChain hg'.2 i (R - 1) (by omega) (by omega)
  have h6 : R ≤ cohortPos R (cohortGenStep R (cohortProj ring root lane src R
      (piD (ref.phys w.1.1))) w.2.1 (cohortEdgeOf root src R e)) (R - 1) := hc
  unfold cohortPos at h6
  omega

include hfix hn hR hsrc hend in
/-- **The head of a terminal in a cycle after a closure** is the operand of the closed window's
last crossing, which is the latest export at the closure, hence later than any earlier mark `T`
crossed by an export before the closure.  Consumer: `cycFactsStep`. -/
theorem headExport (T : Nat)
    (wc : (ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n) × ((Nat → Nat) × Nat))
    (word : List (Fin n)) (hre : WidthUseReach ref root lane src R wc)
    (hjc : WidthJustClosed ref root lane src R Base wc)
    (hcnt : (word.foldl (widthWindowNext ref root lane src R) wc).2.2 = wc.2.2)
    (hlb : ∃ x' : DigitExport (compileAdvice (ceilLogTwo n)) n, DigitRecordedExport wc.1.2 x' ∧
      OnEdge ring root lane src R x' ∧ T < x'.time)
    (U : DigitTerminal (compileAdvice (ceilLogTwo n)) n)
    (hU : DigitRecordedTerminal (word.foldl (widthWindowNext ref root lane src R) wc).1.2 U)
    (hl : U.lane = lane) (hs : U.source = digitSite ring root (src + (2 * R - 1)))
    (ht : wc.1.2.clock < U.time) (s0 : DigitStamp n)
    (hh : ∃ (L : DigitCarryGhost (compileAdvice (ceilLogTwo n)) n)
      (u : DigitUse (compileAdvice (ceilLogTwo n)) n), U.ledger = some L ∧
      L.uses.head? = some u ∧ u.operand = some (.sampled s0)) :
    ∃ x : DigitExport (compileAdvice (ceilLogTwo n)) n, DigitRecordedExport wc.1.2 x ∧
      OnEdge ring root lane src R x ∧ T < x.time ∧ x.operand = some (.sampled s0) := by
  obtain ⟨chi, hcore, -, hlat, huse⟩ := widthUseFactReach ref hfix hn root lane src R hR hsrc hend
    Base wc word hre hjc hcnt
  obtain ⟨L, hL, -, hall⟩ := huse U hU hl hs ht
  obtain ⟨L', u, hL', hu, hop⟩ := hh
  have hLL : L' = L := Option.some.inj (hL'.symm.trans hL)
  subst hLL
  have hu0 : L'.uses[0]? = some u := by
    have e : L'.uses.head? = L'.uses[0]? := by cases L'.uses <;> rfl
    exact e.symm.trans hu
  have hopc := (hall 0 u hu0).1
  rw [show R - 1 - 0 = R - 1 by omega] at hopc
  obtain ⟨x', hx', ho', ht'⟩ := hlb
  have hle := hlat x' hx' ho'
  obtain ⟨h1, h2⟩ := hcore.1 (R - 1) (by omega)
  exact ⟨chi (R - 1), h1, h2, by omega, by rw [← hopc]; exact hop⟩

/-- A recorded export stays recorded along the chain.  Consumer: `cycFactsStep`. -/
theorem exportChainFold : ∀ (word : List (Fin n))
    (wc : (ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n) × ((Nat → Nat) × Nat))
    (x : DigitExport (compileAdvice (ceilLogTwo n)) n), DigitRecordedExport wc.1.2 x →
    DigitRecordedExport (word.foldl (widthWindowNext ref root lane src R) wc).1.2 x := by
  intro word
  induction word with
  | nil => intro wc x h; exact h
  | cons e rest ih =>
    intro wc x h
    exact ih _ x (L3.CohortIdentity.recordedExportStep ring _ _ e x h)

/-- **Every head terminal after `t1` reads a sample exported after `T`.**  Consumer: `CycFacts`. -/
def HeadAfter (A : DigitAudit (compileAdvice (ceilLogTwo n)) n) (T t1 : Nat) : Prop :=
  ∀ (U : DigitTerminal (compileAdvice (ceilLogTwo n)) n) (s0 : DigitStamp n),
    DigitRecordedTerminal A U → U.lane = lane →
    U.source = digitSite ring root (src + (2 * R - 1)) → t1 < U.time →
    (∃ (L : DigitCarryGhost (compileAdvice (ceilLogTwo n)) n)
      (u : DigitUse (compileAdvice (ceilLogTwo n)) n), U.ledger = some L ∧
      L.uses.head? = some u ∧ u.operand = some (.sampled s0)) →
    ∃ x : DigitExport (compileAdvice (ceilLogTwo n)) n, DigitRecordedExport A x ∧
      OnEdge ring root lane src R x ∧ T < x.time ∧ x.operand = some (.sampled s0)

/-- **Between two border exports after `T` lies a completion after `t1`.**  Consumer: `CycFacts`. -/
def CompletionBetween (A : DigitAudit (compileAdvice (ceilLogTwo n)) n) (T t1 : Nat) : Prop :=
  ∀ x1 x2 : DigitExport (compileAdvice (ceilLogTwo n)) n,
    BorderExport (ring := ring) root lane src R A T x1 →
    BorderExport (ring := ring) root lane src R A T x2 → x1.time < x2.time →
    ∃ U : DigitTerminal (compileAdvice (ceilLogTwo n)) n,
      DigitCompletion ring A root src (src + R) lane 0 U ∧ t1 < U.time ∧ U.time < x2.time

/-- **The cycle facts after the pin `T`**: the window invariant, the use track and the window with
its start not before `T`; a border export after `T` means a closure happened; and after the first
closure `t1` (with the current closure `wc`) `HeadAfter` and `CompletionBetween`.  Consumer:
`cycFactsStep`, `noTailBetween`. -/
def CycFacts (T : Nat)
    (w : (ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n) × ((Nat → Nat) × Nat)) : Prop :=
  WidthWinInvD ref root lane src R Base w.1 w.2 ∧ WidthUseReach ref root lane src R w ∧
  PairIn ring root src R w.1.2 ∧ T ≤ w.1.2.clock ∧
  (∃ (chi : Nat → DigitExport (compileAdvice (ceilLogTwo n)) n) (t0 : Nat),
    CycWin ring root lane src R w.1.2 w.2.1 chi t0 ∧ T ≤ t0) ∧
  (∀ x, BorderExport (ring := ring) root lane src R w.1.2 T x → 1 ≤ w.2.2) ∧
  (1 ≤ w.2.2 → ∃ (t1 : Nat)
    (wc : (ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n) × ((Nat → Nat) × Nat))
    (word : List (Fin n)),
    T < t1 ∧ t1 ≤ wc.1.2.clock ∧ WidthUseReach ref root lane src R wc ∧
    WidthJustClosed ref root lane src R Base wc ∧
    w = word.foldl (widthWindowNext ref root lane src R) wc ∧ wc.2.2 = w.2.2 ∧
    WidthOrderInv ref root lane src R w.1 w.2 wc.1.2.clock ∧ PairIn ring root src R wc.1.2 ∧
    (∃ x' : DigitExport (compileAdvice (ceilLogTwo n)) n, DigitRecordedExport wc.1.2 x' ∧
      OnEdge ring root lane src R x' ∧ T < x'.time) ∧
    HeadAfter (ring := ring) root lane src R w.1.2 T t1 ∧
    CompletionBetween (ring := ring) root lane src R w.1.2 T t1)

include hfix hn hR hsrc hend in
/-- **Every chain letter keeps the cycle facts.**  Consumer: `cycFactsFold`. -/
theorem cycFactsStep (T : Nat)
    (w : (ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n) × ((Nat → Nat) × Nat))
    (h : CycFacts ref root lane src R Base T w) (e : Fin n) :
    CycFacts ref root lane src R Base T (widthWindowNext ref root lane src R w e) := by
  obtain ⟨hw, hre, hp, hTc, ⟨chi, t0, hcw, hTt⟩, hc1, hmain⟩ := h
  have hwd' := (widthWinInvDStep ref hfix hn root lane src R hR hsrc hend Base w.1 w.2 hw e).1
  have hre' := widthUseReachStep ref hfix hn root lane src R hR hsrc hend Base w e hw hre
  have hp' : PairIn ring root src R (widthWindowNext ref root lane src R w e).1.2 := hp
  have hfo := hw.2.1
  have hfo' : AuditFrameOrder (digitAuditStep ring (piD (ref.phys w.1.1)) w.1.2 e) :=
    auditFrameOrderStep ring (piD (ref.phys w.1.1)) w.1.2 e hfo
  have hclk : (digitAuditStep ring (piD (ref.phys w.1.1)) w.1.2 e).clock = w.1.2.clock + 1 := rfl
  have hA : (widthWindowNext ref root lane src R w e).1.2 =
      digitAuditStep ring (piD (ref.phys w.1.1)) w.1.2 e := rfl
  obtain ⟨-, -, hWs, -⟩ := widthWindowPinFacts ref hfix hn root lane src R hR hsrc hend Base w hw e
  have hw' := hWs chi t0 hcw
  have htermLe : ∀ U : DigitTerminal (compileAdvice (ceilLogTwo n)) n,
      DigitRecordedTerminal (digitAuditStep ring (piD (ref.phys w.1.1)) w.1.2 e) U →
      U.time ≤ w.1.2.clock + 1 := by
    intro U hU
    obtain ⟨f, hf, hft, -⟩ := hU
    have := (hfo'.2.1 f hf).2
    rw [hclk] at this
    omega
  -- a new export is the letter's
  have hxCases : ∀ x : DigitExport (compileAdvice (ceilLogTwo n)) n,
      DigitRecordedExport (digitAuditStep ring (piD (ref.phys w.1.1)) w.1.2 e) x →
      DigitRecordedExport w.1.2 x ∨ x.time = w.1.2.clock + 1 := by
    intro x hx
    rcases recordedExportStepCases ring _ _ _ x hx with h1 | ⟨h1, -⟩
    · exact Or.inl h1
    · exact Or.inr h1
  have hxLe : ∀ x : DigitExport (compileAdvice (ceilLogTwo n)) n,
      DigitRecordedExport (digitAuditStep ring (piD (ref.phys w.1.1)) w.1.2 e) x →
      x.time ≤ w.1.2.clock + 1 := fun x hx => recordedTimeLe _ hfo' x hx
  have hxOldLe : ∀ x : DigitExport (compileAdvice (ceilLogTwo n)) n,
      DigitRecordedExport w.1.2 x → x.time ≤ w.1.2.clock := fun x hx => recordedTimeLe _ hfo x hx
  rcases windowGhostCases ref root lane src R w e with ⟨hd, hg⟩ | ⟨hnd, hg⟩
  · -- a closing letter
    have hg2 : (widthWindowNext ref root lane src R w e).2.2 = w.2.2 + 1 := by rw [hg]
    have hg1 : (widthWindowNext ref root lane src R w e).2.1 = fun _ => 0 := by rw [hg]
    have hjc' : WidthJustClosed ref root lane src R Base (widthWindowNext ref root lane src R w e) :=
      ⟨w, e, hw, rfl, hg2⟩
    obtain ⟨hwd, hst⟩ := widthJustClosedStart ref hfix hn root lane src R hR hsrc hend Base _ hjc'
    have hall : ∀ i, i < R → R ≤ cohortPos R (cohortGenStep R
        (cohortProj ring root lane src R (piD (ref.phys w.1.1))) w.2.1 (cohortEdgeOf root src R e)) i := by
      intro i hi
      have := hd i hi
      unfold cohortPos
      omega
    obtain ⟨hxr, hxo, hxt⟩ := hw'.2.2.1 (R - 1) (by omega) (hall _ (by omega))
    have hord0 : WidthOrderInv ref root lane src R (widthWindowNext ref root lane src R w e).1
        (widthWindowNext ref root lane src R w e).2
        (widthWindowNext ref root lane src R w e).1.2.clock :=
      ⟨hwd.1, Nat.le_refl _, 0, hst, fun h => by omega⟩
    refine ⟨hwd', hre', hp', by rw [hA, hclk]; omega,
      ⟨chi, w.1.2.clock + 1, ?_, by omega⟩, fun _ _ => by rw [hg2]; omega, fun _ => ?_⟩
    · rw [hg1, hA]
      exact cycWinStart ring root lane src R _ hfo' chi
    · rcases Nat.eq_zero_or_pos w.2.2 with h0 | hpos
      · refine ⟨w.1.2.clock + 1, widthWindowNext ref root lane src R w e, [], by omega,
          Nat.le_refl _, hre', hjc', rfl, rfl, hord0, hp', ⟨_, hxr, hxo, by omega⟩, ?_, ?_⟩
        · intro U s0 hU _ _ hlt _
          have := htermLe U hU
          omega
        · intro x1 x2 h1 h2 hlt
          rcases hxCases x1 h1.1 with hold | hnew
          · have := hc1 x1 ⟨hold, h1.2.1, h1.2.2.1, h1.2.2.2⟩
            omega
          · have := hxLe x2 h2.1
            omega
      · obtain ⟨t1, wc, word, ht1, ht1c, hrc, hjc, hweq, hcnt, hord, hpc, hlb, hH, hC⟩ := hmain hpos
        have hwcle := hord.2.1
        refine ⟨t1, widthWindowNext ref root lane src R w e, [], ht1, ?_, hre', hjc', rfl, rfl,
          hord0, hp', ⟨_, hxr, hxo, by omega⟩, ?_, ?_⟩
        · show t1 ≤ w.1.2.clock + 1
          omega
        · intro U s0 hU hl hs hlt hh
          rcases recordedTerminalStepCases ring _ _ _ U hU with hold | ⟨-, hsite, -⟩
          · obtain ⟨x, h1, h2, h3, h4⟩ := hH U s0 hold hl hs hlt hh
            exact ⟨x, L3.CohortIdentity.recordedExportStep ring _ _ e x h1, h2, h3, h4⟩
          · exfalso
            obtain ⟨k, hk, hke⟩ := closeEdgeLow ref root lane src R Base w hw e hd
            rw [← hsite, hs, cohortEdgeOfSite ring root src R hend (2 * R - 1) (by omega)] at hke
            have := Option.some.inj hke
            omega
        · intro x1 x2 h1 h2 hlt
          have hx1old : DigitRecordedExport w.1.2 x1 := by
            rcases hxCases x1 h1.1 with hold | hnew
            · exact hold
            · have := hxLe x2 h2.1
              omega
          rcases widthOrderInvStep ref hfix hn root lane src R hR hsrc hend w.1 w.2 wc.1.2.clock hord
            e with ⟨hs, -⟩ | ⟨-, -, hterm⟩
          · exfalso
            have : (widthWindowNext ref root lane src R w e).2.2 = w.2.2 := hs
            omega
          · rcases hxCases x2 h2.1 with hold | hnew
            · obtain ⟨U, h3, h4, h5⟩ := hC x1 x2 ⟨hx1old, h1.2.1, h1.2.2.1, h1.2.2.2⟩
                ⟨hold, h2.2.1, h2.2.2.1, h2.2.2.2⟩ hlt
              exact ⟨U, completionStep ring _ _ e root _ _ lane 0 U h3, h4, h5⟩
            · obtain ⟨U, hU, hUl, hUs, hUt, hUc⟩ := hterm
              have hcU := widthOldCompletionPairReach ref hfix hn root lane src R hR hsrc hend Base
                wc word U hrc hjc hpc (by rw [← hweq]; exact hcnt.symm)
                (by rw [← hweq]; exact hord) (by rw [← hweq]; exact hU) hUl hUs hUt
              rw [← hweq] at hcU
              exact ⟨U, completionStep ring _ _ e root _ _ lane 0 U hcU, by omega, by omega⟩
  · -- a letter inside the cycle
    have hg2 : (widthWindowNext ref root lane src R w e).2.2 = w.2.2 := by rw [hg]
    have hg1 : (widthWindowNext ref root lane src R w e).2.1 =
        cohortGenStep R (cohortProj ring root lane src R (piD (ref.phys w.1.1))) w.2.1
          (cohortEdgeOf root src R e) := by rw [hg]
    have hnoNew : ∀ x, BorderExport (ring := ring) root lane src R
        (digitAuditStep ring (piD (ref.phys w.1.1)) w.1.2 e) T x → DigitRecordedExport w.1.2 x := by
      intro x hx
      rcases hxCases x hx.1 with hold | hnew
      · exact hold
      · exfalso
        obtain ⟨hxr, hxo, -, sid, hop, hsi⟩ := hx
        exact borderExportDone ref hfix hn root lane src R hR hsrc hend Base w hw hre.1.2 e hnd x hxr
          hxo (by omega) sid hop hsi
    refine ⟨hwd', hre', hp', by rw [hA, hclk]; omega, ⟨chiNext ring root lane src R (piD (ref.phys w.1.1)) w.1.2 e w.2.1 chi, t0, ?_, hTt⟩,
      fun x hx => ?_, fun hpos => ?_⟩
    · rw [hg1, hA]
      exact hw'
    · rw [hg2]
      exact hc1 x ⟨hnoNew x hx, hx.2.1, hx.2.2.1, hx.2.2.2⟩
    · rw [hg2] at hpos
      obtain ⟨t1, wc, word, ht1, ht1c, hrc, hjc, hweq, hcnt, hord, hpc, hlb, hH, hC⟩ := hmain hpos
      have hwcle := hord.2.1
      have hfold : widthWindowNext ref root lane src R w e =
          (word ++ [e]).foldl (widthWindowNext ref root lane src R) wc := by
        rw [List.foldl_append, ← hweq]
        rfl
      rcases widthOrderInvStep ref hfix hn root lane src R hR hsrc hend w.1 w.2 wc.1.2.clock hord e with
        ⟨-, hord'⟩ | ⟨hs, -⟩
      · refine ⟨t1, wc, word ++ [e], ht1, ht1c, hrc, hjc, hfold, by rw [hg2, hcnt], hord', hpc, hlb,
          ?_, ?_⟩
        · intro U s0 hU hl hs hlt hh
          rw [hA] at hU ⊢
          rcases recordedTerminalStepCases ring _ _ _ U hU with hold | ⟨htU, -, -⟩
          · obtain ⟨x, h1, h2, h3, h4⟩ := hH U s0 hold hl hs hlt hh
            exact ⟨x, L3.CohortIdentity.recordedExportStep ring _ _ e x h1, h2, h3, h4⟩
          · have hcnt' : ((word ++ [e]).foldl (widthWindowNext ref root lane src R) wc).2.2 = wc.2.2 := by
              rw [← hfold, hg2, hcnt]
            obtain ⟨x, h1, h2, h3, h4⟩ := headExport ref hfix hn root lane src R hR hsrc hend Base T wc
              (word ++ [e]) hrc hjc hcnt' hlb U (by rw [← hfold]; exact hU) hl hs (by omega) s0 hh
            have hxf := exportChainFold ref root lane src R (word ++ [e]) wc x h1
            rw [← hfold] at hxf
            exact ⟨x, hxf, h2, h3, h4⟩
        · intro x1 x2 h1 h2 hlt
          rw [hA] at h1 h2 ⊢
          have hx2 := hnoNew x2 h2
          have hx1 : DigitRecordedExport w.1.2 x1 := by
            rcases hxCases x1 h1.1 with hold | hnew
            · exact hold
            · have := hxOldLe x2 hx2
              omega
          obtain ⟨U, h3, h4, h5⟩ := hC x1 x2 ⟨hx1, h1.2.1, h1.2.2.1, h1.2.2.2⟩
            ⟨hx2, h2.2.1, h2.2.2.1, h2.2.2.2⟩ hlt
          exact ⟨U, completionStep ring _ _ e root _ _ lane 0 U h3, h4, h5⟩
      · exfalso
        have : (widthWindowNext ref root lane src R w e).2.2 = w.2.2 + 1 := hs
        omega

include hfix hn hR hsrc hend in
/-- The cycle facts along every chain word.  Consumer: `noTailBetween`. -/
theorem cycFactsFold (T : Nat) : ∀ (word : List (Fin n))
    (w : (ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n) × ((Nat → Nat) × Nat)),
    CycFacts ref root lane src R Base T w →
    CycFacts ref root lane src R Base T (word.foldl (widthWindowNext ref root lane src R) w) := by
  intro word
  induction word with
  | nil => intro w h; exact h
  | cons e rest ih =>
    intro w h
    exact ih _ (cycFactsStep ref hfix hn root lane src R hR hsrc hend Base T w h e)

/-- The chain projects to the coupled run.  Consumer: `noTailBetween`. -/
theorem windowFoldFst : ∀ (word : List (Fin n))
    (w : (ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n) × ((Nat → Nat) × Nat)),
    (word.foldl (widthWindowNext ref root lane src R) w).1 =
      word.foldl (widthDigitAuditNext ref) w.1 := by
  intro word
  induction word with
  | nil => intro w; rfl
  | cons e rest ih =>
    intro w
    exact ih _

end Chain

/-! ### The pin at the tail export -/

section Coupled

variable {n : Nat} {ring : DirectedRing n} (ref : WidthBoundaryReference ring) (hn : 5 ≤ n)
  (root : Fin n) (lane : DigitLane) (src R : Nat) (hR : 2 ≤ R) (hsrc : 2 ≤ src)
  (hend : src + 2 * R < n)
  (q0 : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n)
  (hq0 : L3.WidthPacketMomentCutEntry.WidthRunInv ring ref root lane src R q0)
  (hi0 : q0.2 = digitAuditInitial (piD (ref.phys q0.1))) (hc0 : q0.2.clock = 0)
  (W : List (Fin n))

include hn hR hsrc hend hq0 hi0 hc0 in
/-- **`L3.StageMEntryCyc.wCycStartOfCompletion` with the time named**: on the coupled run of `W`, a
recorded completion of the pair has its tail export `x` (carrying the stamp `sid` read by the first
use of the ledger), and at the prefix `x.time` the cycle witness `lam = 0`, counter `0`, old phase
`0`, with the chosen home cells read at their own cells.  Same proof.  Consumer: `noTailBetween`. -/
theorem wCycStartAtTail (hRd : digitSpan (compileAdvice (ceilLogTwo n)) = R) (cut : Nat)
    (tm : DigitTerminal (compileAdvice (ceilLogTwo n)) n)
    (hcomp : DigitCompletion ring (wRunAt ref.toWidthDigitReference q0 W W.length).2 root src
      (src + R) lane cut tm) :
    ∃ (x : DigitExport (compileAdvice (ceilLogTwo n)) n) (sid : DigitStamp n),
      DigitRecordedExport (wRunAt ref.toWidthDigitReference q0 W W.length).2 x ∧
      OnEdge ring root lane src R x ∧ x.operand = some (.sampled sid) ∧ x.time ≤ W.length ∧
      (∃ (L : DigitCarryGhost (compileAdvice (ceilLogTwo n)) n)
        (u : DigitUse (compileAdvice (ceilLogTwo n)) n), tm.ledger = some L ∧
        L.uses.head? = some u ∧ u.operand = some (.sampled sid)) ∧
      CohortCycIn R 0 (wLane ref root lane src R q0 W x.time) ((fun _ => 0), 0) 0 ∧
      ChosenInv R (SPin ring root lane src (wRunAt ref.toWidthDigitReference q0 W x.time).2)
        (tracked ring root lane src R (wRunAt ref.toWidthDigitReference q0 W x.time).2)
        (fun _ => 0) := by
  obtain ⟨L, sm, xm, uz, hTrec, hTl, hTsrc, hTL, hLi, hLlen, hrow, hord⟩ :=
    completionRows ring _ root src R lane cut tm hRd hcomp
  have hf0 : q0.2.frames = [] := by rw [hi0]; rfl
  obtain ⟨hs0, hsl0, hss0, htl0, hx0, hxl0, hxs0, hxo0, -, -, hsx0, -, -⟩ := hrow 0 (by omega)
  -- the sample letter of the tail
  obtain ⟨fs, hfs, hfst, hfse, hfsr, -⟩ := id hs0
  rw [wRunAtLen ref.toWidthDigitReference W q0 W.length (Nat.le_refl _)] at hfs
  obtain ⟨ts, es, hes, hts, rfl⟩ := wFrameTime ref.toWidthDigitReference W q0 hf0 hc0 fs hfs
  -- the export letter of the tail
  obtain ⟨tx, ex, hexw, hx0t, hexs, hxr⟩ := wExportLetter ref q0 hi0 hc0 W (xm 0) hx0
  rw [hxl0] at hxr
  -- the terminal letter
  obtain ⟨fT, hfT, hfTt, hfTe, hfTr⟩ := id hTrec
  rw [wRunAtLen ref.toWidthDigitReference W q0 W.length (Nat.le_refl _)] at hfT
  obtain ⟨tT, eT, heT, htTt, rfl⟩ := wFrameTime ref.toWidthDigitReference W q0 hf0 hc0 fT hfT
  have hσ : (sm 0).id.time = ts + 1 := hfst.symm.trans hts
  have hTt : tm.time = tT + 1 := hfTt.symm.trans htTt
  have htx := getLt hexw
  have htT := getLt heT
  have hsamp : (digitReceiptLane lane
      (svcAt ring (piD (ref.phys (wRunAt ref.toWidthDigitReference q0 W ts).1))
        (wRunAt ref.toWidthDigitReference q0 W ts).2 es)).sample = some (sm 0) := by
    rw [← hsl0]
    exact hfsr
  have hTr : (digitReceiptLane lane
      (svcAt ring (piD (ref.phys (wRunAt ref.toWidthDigitReference q0 W tT).1))
        (wRunAt ref.toWidthDigitReference q0 W tT).2 eT)).terminal = some tm := by
    rw [← hTl]
    exact hfTr
  have hsite' : (sm 0).id.site = es := hfse.symm
  have hexe : ex = digitSite ring root (src + (R - 1)) := hexs.trans hxs0
  have heTe : eT = digitSite ring root (src + R + (R - 1)) := hfTe.trans hTsrc
  have huniq : ∀ x : DigitExport (compileAdvice (ceilLogTwo n)) n,
      DigitRecordedExport (wRunAt ref.toWidthDigitReference q0 W W.length).2 x →
      OnEdge ring root lane src R x → x.operand = some (.sampled (sm 0).id) →
      x.time = (xm 0).time :=
    fun x hx hon hop => by
      rw [wExportUnique ref hn root lane src R hR hsrc hend q0 hq0 W W.length x (xm 0) (sm 0).id
        hx hx0 hon ⟨hxl0, hxs0⟩ hop hxo0]
  -- the tail sweep (chosen half)
  obtain ⟨st, hst⟩ : ∃ st : Nat → CohortLane,
      ∀ r, st r = wLane ref root lane src R q0 W (ts + 1 + r) := ⟨_, fun _ => rfl⟩
  obtain ⟨htok0, hbefore, hV0⟩ := wTailRun ref hn root lane src R hR hsrc hend q0 hq0 hc0 W st
    ts hst (sm 0) hs0 (by rw [htl0]; rfl) hsl0 es hes hσ (hsite'.symm.trans hss0) hsamp hsite'
    (xm 0) tx ex hexw hx0t hexe hxr hxo0 huniq (by omega) htx
  obtain ⟨hY, hocc, hYT⟩ := wSweepAtExport ref hn root lane src R hR hsrc hend q0 hq0 W st ts tx
    hst (by omega) htx htok0 hbefore hV0
  have hchosen := (strictLaneOfExport hR hY hocc).2.1
  -- the strict ledger (old half)
  have hkT : cohortEdgeOf root src R eT = some (2 * R - 1) := by
    rw [heTe, show src + R + (R - 1) = src + (2 * R - 1) by omega]
    exact cohortEdgeOfSite ring root src R hend (2 * R - 1) (by omega)
  obtain ⟨-, hled⟩ := wTermLedger ref hn root lane src R hR hsrc hend _
    (wInvAt ref hn root lane src R hR hsrc hend q0 hq0 W tT).1.1 eT hkT tm hTr
  have hLe : L = ⟨none, L.uses⟩ := by
    cases L
    simp only at hLi
    subst hLi
    rfl
  have hterm : caA ring root lane src (wRunAt ref.toWidthDigitReference q0 W (tm.time - 1)).2
      (2 * R - 1) = some ⟨none, L.uses⟩ := by
    rw [show tm.time - 1 = tT by omega, ← hled, hTL, ← hLe]
  have hkT' : wKe root src R W (tm.time - 1) = some (2 * R - 1) := by
    rw [show tm.time - 1 = tT by omega, wKeOf root src R W heT]
    exact hkT
  have hinc : ∀ m, m + 1 < R → (uz m).time < (uz (m + 1)).time :=
    fun m hm => (hord m (m + 1) (by omega) hm).2
  have hupos : ∀ m, m < R → 0 < (uz m).time := by
    intro m hm
    obtain ⟨-, -, -, -, -, -, -, -, -, -, h1, h2, -⟩ := hrow m hm
    omega
  obtain ⟨-, -, -, hop⟩ := wCarryChain ref hn root lane src R hR hsrc hend q0 hq0 hi0 hc0 W L.uses
    uz tm.time hLlen (fun m hm => (hrow m hm).2.2.2.2.2.2.2.2.1) hupos
    (fun m hm => (hrow m hm).2.2.2.2.2.2.2.2.2.2.2.2) hinc (by omega) hterm hkT'
  have hut : ∀ m, m < R → tx + 1 ≤ (uz m).time - 1 ∧ (uz m).time - 1 ≤ W.length := by
    intro m hm
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, h1, h2⟩ := hrow m hm
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, h3, -⟩ := hrow 0 (by omega)
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · subst h0
      omega
    · have := (hord 0 m h0 hm).2
      omega
  have huse : ∀ m, m < R → inA ring root lane src
      (wRunAt ref.toWidthDigitReference q0 W ((uz m).time - 1)).2 (R + m) =
        some (.sampled (sm m).id) := by
    intro m hm
    rw [← (hop m hm).1]
    exact (hrow m hm).2.2.2.2.2.2.2.2.2.1
  obtain ⟨harr, htop⟩ := wPackedAtExport ref hn root lane src R hR hsrc hend q0 hq0 hi0 hc0 W sm
    (fun m hm => (hrow m hm).1) (fun m hm => (hrow m hm).2.2.2.1) xm
    (fun m hm => (hrow m hm).2.2.2.2.1)
    (fun m hm => ⟨(hrow m hm).2.2.2.2.2.1, (hrow m hm).2.2.2.2.2.2.1⟩)
    (fun m hm => (hrow m hm).2.2.2.2.2.2.2.1) (fun i j hij hj => (hord i j hij hj).1) tx hx0t htx
    (fun m => (uz m).time - 1) hut huse (fun m h0 hm => (hop m hm).2 h0)
  have hhd : L.uses.head? = some (uz 0) := by
    have e : L.uses.head? = L.uses[0]? := by cases L.uses <;> rfl
    exact e.trans (hrow 0 (by omega)).2.2.2.2.2.2.2.2.1
  rw [wRunAtLen ref.toWidthDigitReference W q0 W.length (Nat.le_refl _)]
  refine ⟨xm 0, (sm 0).id, ?_, ⟨hxl0, hxs0⟩, hxo0, by omega,
    ⟨L, uz 0, hTL, hhd, (hrow 0 (by omega)).2.2.2.2.2.2.2.2.2.1⟩, ?_, ?_⟩
  · have hx := hx0
    rw [wRunAtLen ref.toWidthDigitReference W q0 W.length (Nat.le_refl _)] at hx
    exact hx
  · rw [hx0t]
    refine ⟨rfl, ⟨?_, ?_⟩, ?_, ?_⟩
    · show CohortOldAt R 0 _
      unfold CohortOldAt
      rw [if_pos (Nat.zero_le R)]
      exact ⟨harr, htop, fun i hi => absurd hi (Nat.not_lt_zero i)⟩
    · have hb : cohortBottom R 0 = R := by
        unfold cohortBottom
        rw [if_pos (Nat.zero_le R)]
      rw [hb]
      exact hchosen
    · exact fun q hq _ => absurd hq (Nat.not_lt_zero q)
    · intro h
      have h' : R ≤ 0 := h 0 (by omega)
      omega
  · rw [hx0t]
    exact chosenOfYoungTail hYT

include hn hR hsrc hend hq0 hi0 hc0 in
/-- **Succession**: on the coupled run of `W`, between the tail samples of a completion `T` and
of the next completion `T'` of the pair, no border sample is recorded.  Run the cycle chain from
the state right after the export of `T`'s tail (`wCycStartAtTail`, `CycFacts`).  A border sample
`β` in between is exported between the two tail exports (`ExpBefore`, `BorderChain`), so between
those exports lies a completion `U` after the first closure (`CompletionBetween`), and `T` is at
or before the first closure (`HeadAfter` and export uniqueness): `U` contradicts "next".
Consumer: `tailCauseOfNext`. -/
theorem noTailBetween (hRd : digitSpan (compileAdvice (ceilLogTwo n)) = R)
    (T T' : DigitTerminal (compileAdvice (ceilLogTwo n)) n) (s s' : DigitStamp n)
    (hT : DigitCompletion ring (wRunAt ref.toWidthDigitReference q0 W W.length).2 root src (src + R)
      lane 0 T)
    (hT' : DigitCompletion ring (wRunAt ref.toWidthDigitReference q0 W W.length).2 root src
      (src + R) lane 0 T')
    (hnext : ∀ other : DigitTerminal (compileAdvice (ceilLogTwo n)) n,
      DigitCompletion ring (wRunAt ref.toWidthDigitReference q0 W W.length).2 root src (src + R)
        lane 0 other → T.time < other.time → T'.time ≤ other.time)
    (hs : ∀ (L : DigitCarryGhost (compileAdvice (ceilLogTwo n)) n)
      (v : DigitUse (compileAdvice (ceilLogTwo n)) n), T.ledger = some L →
      L.uses.head? = some v → v.operand = some (.sampled s))
    (hs' : ∀ (L : DigitCarryGhost (compileAdvice (ceilLogTwo n)) n)
      (v : DigitUse (compileAdvice (ceilLogTwo n)) n), T'.ledger = some L →
      L.uses.head? = some v → v.operand = some (.sampled s'))
    (β : DigitSample (compileAdvice (ceilLogTwo n)) n)
    (hβ : DigitRecordedSample (wRunAt ref.toWidthDigitReference q0 W W.length).2 β)
    (hβs : β.id.site = digitSite ring root src) (hβl : β.id.lane = lane)
    (h1 : s.time < β.id.time) (h2 : β.id.time < s'.time) : False := by
  subst hRd
  obtain ⟨x, sid, hxr, hxo, hxop, hxle, ⟨L0, u0, hL0, hu0, huop⟩, hcyc, hch⟩ :=
    wCycStartAtTail ref hn root lane src (digitSpan (compileAdvice (ceilLogTwo n))) hR hsrc hend q0 hq0 hi0 hc0 W rfl 0 T hT
  have hsid : sid = s := by
    have e := huop.symm.trans (hs L0 u0 hL0 hu0)
    simp only [Option.some.injEq, DigitAtom.sampled.injEq] at e
    exact e
  subst hsid
  obtain ⟨⟨hlay, hfo, hfe, hval, hgd⟩, hpair⟩ :=
    wInvAt ref hn root lane src (digitSpan (compileAdvice (ceilLogTwo n))) hR hsrc hend q0 hq0 W x.time
  have hclk := wClock ref q0 hc0 W x.time hxle
  have hreach : WidthPinReach ref.toWidthDigitReference root lane src (digitSpan (compileAdvice (ceilLogTwo n)))
      (wRunAt ref.toWidthDigitReference q0 W x.time, ((fun _ => 0), 0)) := by
    refine ⟨⟨hfe, hval⟩, hch, fun q hq => absurd hq (Nat.not_lt_zero q), fun _ => x, _,
      cycWinStart ring root lane src (digitSpan (compileAdvice (ceilLogTwo n))) _ hfo (fun _ => x), fun i hi hc' => ?_, fun h1 => ?_⟩
    · have hpos : cohortPos (digitSpan (compileAdvice (ceilLogTwo n))) (fun _ => 0) i =
          digitSpan (compileAdvice (ceilLogTwo n)) - 1 - i := rfl
      dsimp only at hc'
      omega
    · dsimp only at h1
      omega
  have hwd0 := widthWinInvDAtCycStart ref.toWidthDigitReference root lane src (digitSpan (compileAdvice (ceilLogTwo n))) (InheritedOk lane)
    (wRunAt ref.toWidthDigitReference q0 W x.time) hlay hfo hgd 0 0 hcyc (fun _ => x)
  have hu0' := widthUseReachOfStart ref.toWidthDigitReference root lane src (digitSpan (compileAdvice (ceilLogTwo n))) _ hreach hfo rfl rfl
  have hF0 : CycFacts ref.toWidthDigitReference root lane src (digitSpan (compileAdvice (ceilLogTwo n))) (InheritedOk lane) x.time
      (wRunAt ref.toWidthDigitReference q0 W x.time, ((fun _ => 0), 0)) := by
    refine ⟨hwd0, hu0', hpair, by show x.time ≤ (wRunAt ref.toWidthDigitReference q0 W x.time).2.clock; omega,
      ⟨fun _ => x, _, cycWinStart ring root lane src (digitSpan (compileAdvice (ceilLogTwo n))) _ hfo (fun _ => x), by show x.time ≤ (wRunAt ref.toWidthDigitReference q0 W x.time).2.clock; omega⟩,
      fun y hy => ?_, fun h => absurd (show 1 ≤ 0 from h) (by omega)⟩
    have h3 := recordedTimeLe _ hfo y hy.1
    have h4 := hy.2.2.1
    omega
  have hF := cycFactsFold ref.toWidthDigitReference ref.singletonFixed hn root lane src (digitSpan (compileAdvice (ceilLogTwo n))) hR hsrc hend
    (InheritedOk lane) x.time (W.drop x.time) _ hF0
  have hfinal : ((W.drop x.time).foldl (widthWindowNext ref.toWidthDigitReference root lane src
      (digitSpan (compileAdvice (ceilLogTwo n))))
      (wRunAt ref.toWidthDigitReference q0 W x.time, ((fun _ => 0), 0))).1 =
      wRunAt ref.toWidthDigitReference q0 W W.length := by
    rw [windowFoldFst ref.toWidthDigitReference root lane src (digitSpan (compileAdvice (ceilLogTwo n))) (W.drop x.time) _]
    show (W.drop x.time).foldl (widthDigitAuditNext ref.toWidthDigitReference)
      (wRunAt ref.toWidthDigitReference q0 W x.time) = _
    rw [wRunAtSplit, wRunAtLen ref.toWidthDigitReference W q0 W.length (Nat.le_refl _)]
  obtain ⟨-, -, -, -, -, hc1, hmain⟩ := hF
  -- the run invariants at the end
  have hEnd := laneRunFold ref hn root lane src (digitSpan (compileAdvice (ceilLogTwo n))) hR hsrc hend W q0 hq0
    (by rw [hi0]; exact laneRunInitial ref root lane src (digitSpan (compileAdvice (ceilLogTwo n))) hR q0.1)
  rw [← wRunAtLen ref.toWidthDigitReference W q0 W.length (Nat.le_refl _)] at hEnd
  obtain ⟨⟨⟨-, hfoF, -, -, hgdF⟩, -⟩, htail, hah, -⟩ := hEnd
  -- the rows of `T'` and the tail of `T`
  obtain ⟨-, -, -, -, -, -, pos, ledger, samples, exports, uses, hled, -, -, hall, -, -⟩ := id hT'
  obtain ⟨r0, l0, si0, -, -, rx0, xl0, xs0, xd0, xo0, -, -, ui0, -, uo0, -, -, -, hxu, hut⟩ :=
    hall ⟨0, pos⟩
  have si0' : (samples ⟨0, pos⟩).id.site = digitSite ring root src := by
    rw [si0]
    rfl
  have hhead : ledger.uses.head? = some (uses ⟨0, pos⟩) := by
    have e : ledger.uses.head? = ledger.uses[0]? := by cases ledger.uses <;> rfl
    exact e.trans ui0
  have hid' : (samples ⟨0, pos⟩).id = s' := by
    have e := uo0.symm.trans (hs' ledger _ hled hhead)
    simp only [Option.some.injEq, DigitAtom.sampled.injEq] at e
    exact e
  obtain ⟨ss, hssr, hssi, hssl, -, -, La, ua, hLa, hua, hoa, -⟩ :=
    completionTail ring _ root src _ lane 0 T hT
  have hss : ss.id = sid := by
    have e := hoa.symm.trans (hs La ua hLa hua)
    simp only [Option.some.injEq, DigitAtom.sampled.injEq] at e
    exact e
  -- the export of `β`
  obtain ⟨-, hchβ, -⟩ := htail β.id ⟨β, hβ, rfl⟩ hβs hβl
  obtain ⟨-, rho, tl, hcs, -, -, -, -, -, hlat⟩ := hchβ (samples ⟨0, pos⟩) r0 si0' l0
    (by rw [hid']; exact h2)
  have hle := hlat β hβ hβs hβl (by rw [hid']; exact h2)
  obtain ⟨-, -, hexβ⟩ := hah.2.2 β.id ⟨β, hβ, rfl⟩ hβs hβl
  obtain ⟨xβ, hxβ, hoβ, hopβ, htβ⟩ := hexβ (exports ⟨0, pos⟩) (samples ⟨0, pos⟩) rx0
    ⟨⟨xl0, xs0⟩, xd0⟩ xo0 r0 rho tl hcs hle
  -- it comes after the export of `sid`
  have hsidsite : sid.site = digitSite ring root src := by rw [← hss]; exact hssi
  have hsidlane : sid.lane = lane := by rw [← hss]; exact hssl
  obtain ⟨-, hchs, -⟩ := htail sid ⟨ss, hssr, hss⟩ hsidsite hsidlane
  obtain ⟨-, rho2, tl2, hcs2, -, -, -, -, -, hlat2⟩ := hchs β hβ hβs hβl h1
  have hle2 := hlat2 ss hssr hssi hssl (by rw [hss]; exact h1)
  obtain ⟨-, -, hexs⟩ := hah.2.2 sid ⟨ss, hssr, hss⟩ hsidsite hsidlane
  obtain ⟨x0, hx0, ho0, hop0, ht0⟩ := hexs xβ β hxβ hoβ hopβ hβ rho2 tl2 hcs2
    (by rw [← hss]; exact hle2)
  have hx0e : x0 = x := hgdF.2.2.2.2.2 x0 x sid hx0 hxr ho0.1 hxo hop0 hxop
  subst hx0e
  have hB1 : BorderExport (ring := ring) root lane src (digitSpan (compileAdvice (ceilLogTwo n))) _ x0.time xβ :=
    ⟨hxβ, hoβ.1, ht0, β.id, hopβ, hβs⟩
  have hB2 : BorderExport (ring := ring) root lane src (digitSpan (compileAdvice (ceilLogTwo n))) _ x0.time (exports ⟨0, pos⟩) :=
    ⟨rx0, ⟨xl0, xs0⟩, by omega, (samples ⟨0, pos⟩).id, xo0, si0'⟩
  have hpos1 := hc1 xβ (by rw [hfinal]; exact hB1)
  obtain ⟨t1, _, _, -, -, -, -, -, -, -, -, -, hH, hC⟩ := hmain hpos1
  rw [hfinal] at hH hC
  obtain ⟨U, hU, htU, hltU⟩ := hC xβ _ hB1 hB2 htβ
  have hTle : T.time ≤ t1 := by
    rcases Nat.lt_or_ge t1 T.time with hlt | hge
    · exfalso
      obtain ⟨y, hy, hoy, hty, hopy⟩ := hH T sid hT.2.1 hT.2.2.1
        (by rw [hT.2.2.2.1]; congr 1; omega) hlt ⟨L0, u0, hL0, hu0, huop⟩
      have := hgdF.2.2.2.2.2 y x0 sid hy hx0 hoy ho0.1 hopy hop0
      rw [this] at hty
      omega
    · exact hge
  have := hnext U hU (by omega)
  omega

include hn hR hsrc hend hq0 hi0 hc0 in
/-- **The cause tail of the next completion's tail is the tail of the completion before it**:
`BorderChain` names the latest earlier border sample as the cause tail, and `noTailBetween` leaves
only `T`'s tail.  Consumer: `L3.WriterOrderedClose` (consecutive ranks). -/
theorem tailCauseOfNext (hRd : digitSpan (compileAdvice (ceilLogTwo n)) = R)
    (T T' : DigitTerminal (compileAdvice (ceilLogTwo n)) n) (s s' : DigitStamp n)
    (hT : DigitCompletion ring (wRunAt ref.toWidthDigitReference q0 W W.length).2 root src (src + R)
      lane 0 T)
    (hT' : DigitCompletion ring (wRunAt ref.toWidthDigitReference q0 W W.length).2 root src
      (src + R) lane 0 T')
    (hnext : ∀ other : DigitTerminal (compileAdvice (ceilLogTwo n)) n,
      DigitCompletion ring (wRunAt ref.toWidthDigitReference q0 W W.length).2 root src (src + R)
        lane 0 other → T.time < other.time → T'.time ≤ other.time)
    (hs : ∀ (L : DigitCarryGhost (compileAdvice (ceilLogTwo n)) n)
      (v : DigitUse (compileAdvice (ceilLogTwo n)) n), T.ledger = some L →
      L.uses.head? = some v → v.operand = some (.sampled s))
    (hs' : ∀ (L : DigitCarryGhost (compileAdvice (ceilLogTwo n)) n)
      (v : DigitUse (compileAdvice (ceilLogTwo n)) n), T'.ledger = some L →
      L.uses.head? = some v → v.operand = some (.sampled s'))
    (hlt : s.time < s'.time)
    (ss : DigitSample (compileAdvice (ceilLogTwo n)) n)
    (hssr : DigitRecordedSample (wRunAt ref.toWidthDigitReference q0 W W.length).2 ss)
    (hss : ss.id = s) (hssi : ss.id.site = digitSite ring root src) (hssl : ss.id.lane = lane)
    (sp : DigitSample (compileAdvice (ceilLogTwo n)) n)
    (hspr : DigitRecordedSample (wRunAt ref.toWidthDigitReference q0 W W.length).2 sp)
    (hsp : sp.id = s') (hspi : sp.id.site = digitSite ring root src) (hspl : sp.id.lane = lane)
    (rho tl : DigitStamp n) (hc : sp.cause = some (.afterTail rho (some (.sampled tl)))) :
    tl = s := by
  have hEnd := laneRunFold ref hn root lane src R hR hsrc hend W q0 hq0
    (by rw [hi0]; exact laneRunInitial ref root lane src R hR q0.1)
  rw [← wRunAtLen ref.toWidthDigitReference W q0 W.length (Nat.le_refl _)] at hEnd
  obtain ⟨⟨⟨-, hfoF, -, -, -⟩, -⟩, htail, -⟩ := hEnd
  have hsi : s.site = digitSite ring root src := by rw [← hss]; exact hssi
  have hsl : s.lane = lane := by rw [← hss]; exact hssl
  obtain ⟨-, hchs, -⟩ := htail s ⟨ss, hssr, hss⟩ hsi hsl
  obtain ⟨-, rho1, tl1, hc1, hr1, -, -, h3, h4, hlat⟩ := hchs sp hspr hspi hspl
    (by rw [hsp]; exact hlt)
  rw [hc] at hc1
  simp only [Option.some.injEq, DigitUnread.afterTail.injEq, DigitAtom.sampled.injEq] at hc1
  obtain ⟨-, rfl⟩ := hc1
  have hle : s.time ≤ tl.time := by
    rw [← hss]
    exact hlat ss hssr hssi hssl (by rw [hss, hsp]; exact hlt)
  rcases tailRankedCases hr1 with he | ⟨p, hpid, hps, -, hpr, hpl, -⟩
  · exact he
  · rcases Nat.lt_or_ge s.time tl.time with hlt2 | hge
    · exfalso
      have hle3 : p.id.time < s'.time := by
        rw [hpid, ← hsp]
        omega
      exact noTailBetween ref hn root lane src R hR hsrc hend q0 hq0 hi0 hc0 W hRd T T' s s' hT hT'
        hnext hs hs' p hpr hps hpl (by rw [hpid]; exact hlt2) hle3
    · exact stampEq (by omega) (by rw [hsi, ← hpid, hps]) (by rw [hsl, ← hpid, hpl])

end Coupled

end L3.WriterCycle

#print axioms L3.WriterCycle.windowGhostCases
#print axioms L3.WriterCycle.closeEdgeLow
#print axioms L3.WriterCycle.borderExportDone
#print axioms L3.WriterCycle.headExport
#print axioms L3.WriterCycle.exportChainFold
#print axioms L3.WriterCycle.cycFactsStep
#print axioms L3.WriterCycle.cycFactsFold
#print axioms L3.WriterCycle.windowFoldFst
#print axioms L3.WriterCycle.wCycStartAtTail
#print axioms L3.WriterCycle.noTailBetween
#print axioms L3.WriterCycle.tailCauseOfNext
