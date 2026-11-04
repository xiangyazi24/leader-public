import Leader.L3.Width.DigitQuietEntryPairBundle
import Leader.L3.Width.DigitQuietEntryValuesUses
import Leader.L3.Width.DigitWriterCurrentQuiet
import Leader.L3.StageM.EntryComparison

/-!
# The value step of one pair of the writer chain

On the audit fold of a clean start, for a complete pair with five writer completions after `after`,
if the source digits are quiet from `after` on and the target cells hold no `ZERO` label from `after`
on, then the pin bundle holds from the terminal of the fourth completion on (`bundleAtFourth`), the
uses of the fifth have the source digits as values (`terminalUsesOfBundle`), they are clean
(`useClean`), every later write to a target cell stores the same digit (`targetWriteOfBundle`), so
the target cells are quiet from the fifth terminal on and the target block is the successor of the
source block (`writerPairStep`).

Consumer: `L3.QuietEntryValues.chainFacts` (WidthDigitQuietEntryValuesChain).

Paper: research/lean-l3/ledgers/R10c-qdigit-notes.md section 9.
-/

namespace L3.QuietEntryValues

open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree
open L3
open L3.AcceptedReceipts
open L3.DigitQuiet
open L3.QuietEntryPair
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
open L3.ValueCorr
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
open L3.ClosePersist
open L3.CloseBoundary
open L3.PairBlock
open L3.FiveTransfer
open L3.TailChain
open L3.TailAhead
open L3.TermEntry
open L3.CurrentWin
open L3.CloseCurrent
open L3.CloseEntry
open L3.CloseRank
open L3.CloseOrder
open L3.WriterOrder
open L3.CohortOrder
open L3.WriterCurrent
open L3.WriterAged

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-! ### States along a word -/

section States

variable {n : Nat} {ring : DirectedRing n} (ref : WidthDigitReference ring) (start : ref.State)
  (w : List (Fin n))

/-- The successor of a prefix state.  Consumer: `bundleLater`, `digitPhi`. -/
theorem stateStep (k : Nat) (hk : k < w.length) :
    ∃ e, stateAt ref start w (k + 1) = widthDigitAuditNext ref (stateAt ref start w k) e :=
  ⟨w[k], wRunAtSucc ref w _ k w[k] (List.getElem?_eq_getElem hk)⟩

/-- A letter acts on the digit projection by `phiD`.  Consumer: `targetHold`, `useClean`. -/
theorem digitPhi (hd : ref.drained start) (k : Nat) (hk : k < w.length) :
    ∃ e, piD (ref.phys (stateAt ref start w (k + 1)).1) =
      phiD ring (piD (ref.phys (stateAt ref start w k).1)) e := by
  obtain ⟨e, he⟩ := stateStep ref start w k hk
  refine ⟨e, ?_⟩
  rw [he]
  exact ref.digitStep _ (drained_fold ref (w.take k) (start, _) hd) e

/-- A prefix of a prefix.  Consumer: `samplesCurrentAt`. -/
theorem stateTake (k k' : Nat) (h : k' ≤ k) :
    stateAt ref start (w.take k) k' = stateAt ref start w k' := by
  unfold stateAt
  rw [List.take_take, Nat.min_eq_left h]

/-- A digit quiet on `[m, b)` is the same at `b`.  Consumer: `samplesCurrentAt`. -/
theorem digitAtConst (i : Fin n) (m b : Nat) (hmb : m ≤ b)
    (hq : ∀ t, m ≤ t → t < b → digitAt ref start w (t + 1) i = digitAt ref start w t i) :
    digitAt ref start w b i = digitAt ref start w m i := by
  have key : ∀ d, digitAt ref start w (m + d) i = digitAt ref start w m i ∨ b < m + d := by
    intro d
    induction d with
    | zero => exact Or.inl rfl
    | succ d ih =>
      rcases ih with ih | ih
      · by_cases h : m + d < b
        · left
          rw [← Nat.add_assoc, hq (m + d) (by omega) h]
          exact ih
        · exact Or.inr (by omega)
      · exact Or.inr (by omega)
  rcases key (b - m) with h | h
  · rwa [show m + (b - m) = b by omega] at h
  · omega

/-- **`SamplesCurrent` at a prefix state** from the quiet source digits.  Consumer:
`writerPairStep`. -/
theorem samplesCurrentAt (hd : ref.drained start) (root : Fin n) (lane : DigitLane)
    (src R after k : Nat) (hk : k ≤ w.length)
    (hstat : ∀ j, j < R → ∀ t, after ≤ t → t < w.length →
      digitAt ref start w (t + 1) (digitSite ring root (src + j)) =
        digitAt ref start w t (digitSite ring root (src + j))) :
    SamplesCurrent ring root lane src R after (stateAt ref start w k).2
      (piD (ref.phys (stateAt ref start w k).1)) := by
  intro s hrec hl ht q hq hsite
  obtain ⟨f, hf, hft, hfe, -, hfv⟩ := hrec
  obtain ⟨h1, h2, h3, -⟩ := frameLink ref start (w.take k) hd f hf
  have hlen : (w.take k).length = k := by
    rw [List.length_take]
    omega
  rw [hlen] at h2
  rw [hft, stateTake ref start w k _ (by omega)] at h3
  rw [hfv, hfe, hsite, h3]
  have := digitAtConst ref start w (digitSite ring root (src + q)) (s.id.time - 1) k (by omega)
    (fun t h4 h5 => hstat q hq t (by omega) (by omega))
  exact this.symm

end States

section Bundle

variable {n : Nat} {ring : DirectedRing n} (ref : WidthBoundaryReference ring) (hn : 5 ≤ n)
  (start : ref.State) (hst : ref.start start)
  (w : List (Fin n)) (root : Fin n) (hs : ref.singleton root start)
  (lane : DigitLane) (src : Nat)

/-- A completion of the end of a run is one of any earlier state with a clock no earlier than its
terminal.  Consumer: `bundleAtFourth`. -/
theorem completionFoldBack (root : Fin n) (source target : Nat) (lane : DigitLane) (cut : Nat)
    (T : DigitTerminal (compileAdvice (ceilLogTwo n)) n) :
    ∀ (word : List (Fin n))
      (y : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n),
      DigitCompletion ring (word.foldl (widthDigitAuditNext ref.toWidthDigitReference) y).2 root
        source target lane cut T →
      T.time ≤ y.2.clock → DigitCompletion ring y.2 root source target lane cut T := by
  intro word
  induction word with
  | nil => intro y h _; exact h
  | cons e rest ih =>
    intro y h ht
    have h1 := ih (widthDigitAuditNext ref.toWidthDigitReference y e) h
      (by show T.time ≤ y.2.clock + 1; omega)
    exact completionBack ring _ _ e root source target lane cut T h1 ht

/-- The clock of a prefix state.  Consumer: `bundleAtFourth`. -/
theorem clockAt (k : Nat) (hk : k ≤ w.length) :
    (stateAt ref.toWidthDigitReference start w k).2.clock = k := by
  have := clockFold ref.toWidthDigitReference (w.take k)
    (start, digitAuditInitial (piD (ref.phys start)))
  have h2 : (w.take k).length = k := by
    rw [List.length_take]
    omega
  rw [h2] at this
  unfold stateAt
  rw [this]
  show 0 + k = k
  omega

include hn hst hs in
/-- **The bundle at the terminal state of a completion whose tail is not older than `after`**, on
either lane: the pin of the word, the class and the age of the terminal letter
(`L3.WriterAged.terminalEntry`).  Consumer: `bundleAtFourth` and the comparison half of `pairs`. -/
theorem bundleAtTerminal (hsp : DigitCompletePair ring root (piD (ref.phys start)) src
      (src + digitSpan (compileAdvice (ceilLogTwo n))))
    (after cut : Nat) (U : DigitTerminal (compileAdvice (ceilLogTwo n)) n)
    (hU : DigitCompletion ring (w.foldl (widthDigitAuditNext ref.toWidthDigitReference)
      (start, digitAuditInitial (piD (ref.phys start)))).2 root src
      (src + digitSpan (compileAdvice (ceilLogTwo n))) lane cut U)
    (hclk : U.time = (w.foldl (widthDigitAuditNext ref.toWidthDigitReference)
      (start, digitAuditInitial (piD (ref.phys start)))).2.clock)
    (sigma : DigitStamp n) (hsi : sigma.site = digitSite ring root src) (hsl : sigma.lane = lane)
    (hh : ∀ (L : DigitCarryGhost (compileAdvice (ceilLogTwo n)) n)
      (v : DigitUse (compileAdvice (ceilLogTwo n)) n), U.ledger = some L →
      L.uses.head? = some v → v.operand = some (.sampled sigma))
    (hage : after ≤ sigma.time) (hcut : after ≤ U.time) :
    ∃ g : (Nat → Nat) × Nat,
      PairBundle ref.toWidthDigitReference root lane src (digitSpan (compileAdvice (ceilLogTwo n)))
        after U.time ((w.foldl (widthDigitAuditNext ref.toWidthDigitReference)
          (start, digitAuditInitial (piD (ref.phys start)))), g) := by
  obtain ⟨root0, hs0, hL⟩ := widthCleanBoundaryRoot ref start hst
  have hr : root = root0 :=
    (ref.singletonFixed root0 start hs0).2.1 root (ref.singletonFixed root start hs).1
  subst hr
  obtain ⟨hsrc, hend, hlay⟩ := pairLayoutStart ref hn root start hL src hsp
  have hR : 2 ≤ digitSpan (compileAdvice (ceilLogTwo n)) := valueSpanTwo hn
  have hq0 : L3.WidthPacketMomentCutEntry.WidthRunInv ring ref root lane src
      (digitSpan (compileAdvice (ceilLogTwo n)))
      (start, digitAuditInitial (piD (ref.phys start))) :=
    ⟨widthPairInvInitial ring ref hn root lane _ _ start hlay, hsp⟩
  obtain ⟨hclass, hwin⟩ := terminalEntry ref hn root lane src _ hR hsrc hend _ hq0 rfl rfl w rfl cut
    U hU sigma hsi hsl hh hclk
  have hW := widthBoundaryDigitBoundaryWFixedRootOfSingleton ref root start hs w
  obtain ⟨-, -, g, hw, hu⟩ := lanePairPinOfWord ref hn root lane start hst w hW src cut U hend hU
  have hb := pairBundleStart ref.toWidthDigitReference root lane src _ after _ g hw hu hclass
    (winAgeMono hage hwin) (by rw [← hclk]; exact hcut)
  rw [← hclk] at hb
  exact ⟨_, hb⟩

/-! ### The bundle along the word -/

include hn in
/-- **The bundle from a state on.**  Consumer: `writerPairStep`. -/
theorem bundleLater (R : Nat) (hR : 2 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n) (after born t : Nat)
    (hb : ∃ g, PairBundle ref.toWidthDigitReference root lane src R after born
      (stateAt ref.toWidthDigitReference start w t, g)) :
    ∀ d, t + d ≤ w.length → ∃ g, PairBundle ref.toWidthDigitReference root lane src R after born
      (stateAt ref.toWidthDigitReference start w (t + d), g) := by
  intro d
  induction d with
  | zero => intro _; exact hb
  | succ d ih =>
    intro hd
    obtain ⟨g, hg⟩ := ih (by omega)
    obtain ⟨e, he⟩ := stateStep ref.toWidthDigitReference start w (t + d) (by omega)
    refine ⟨(widthWindowNext ref.toWidthDigitReference root lane src R
      (stateAt ref.toWidthDigitReference start w (t + d), g) e).2, ?_⟩
    rw [← Nat.add_assoc, he]
    exact pairBundleStep ref.toWidthDigitReference ref.singletonFixed hn root lane src R hR hsrc hend
      after born _ e hg

end Bundle

/-! ### Settled inputs and writes on the target -/

section Write

variable {c : Compiled} {R : Nat} {s : CohortLane} {tv sv : Nat → DigitLaneView c}
  {Dp : Nat → Fin c.topA} {j o : Nat} {g : (Nat → Nat) × Nat}

/-- A settled target input without a live carry holds the source digit of its offset.  Consumer:
`targetWriteOfBundle`. -/
theorem settledVal (hT : ScanTie R s tv sv) (hV : ScanVals R g.1 tv sv Dp)
    (hcyc : CohortCycIn R j s g o) {k : Nat} (hk : k < R) (hl : (tv k).carryLive = false)
    {v : Fin c.topA} {t : Bool} (hin : (tv k).input = .S v t) : v = Dp k := by
  obtain ⟨-, ⟨-, hch⟩, -, -⟩ := hcyc
  by_cases hc : ∃ i, i < R ∧ cohortPos R g.1 i = R + k
  · obtain ⟨i, hi, hp⟩ := hc
    rcases hch.pkt i hi with h | ⟨h, hlam⟩ | ⟨-, hlam⟩
    · rw [hp, tokTarget hT hk, hl, hin] at h
      simp [cohortTokIn, bankRepairDigitInShOf] at h
    · have hv := hV.targetChosen i hi k hk hp v t (Or.inr hin)
      unfold cohortPos at hp
      rw [show R - 1 - i = k by omega] at hv
      exact hv
    · unfold cohortPos at hp
      omega
  · exact hV.targetOff k hk (fun i hi he => hc ⟨i, hi, he⟩) v t (Or.inr hin)

end Write

section TargetWrite

variable {n : Nat} {ring : DirectedRing n} (ref : WidthDigitReference ring)
  (hfix : ∀ (root : Fin n) (z : ref.State), ref.singleton root z →
    WFixedRoot ring root (piW (ref.phys z))) (hn : 5 ≤ n)
  (root : Fin n) (src R : Nat) (hsrcEnd : src + 2 * R < n)

include hfix hn hsrcEnd in
/-- **Every write to a target cell in the bundle stores the same digit**: a change of the digit at
the cell at offset `m`, with no `ZERO` label, is an advance (an old carry at `m - 1`, with its
carry-in bit, and a settled input with the source digit `m`) or a launch at the delimiter.
Consumer: `targetHold`. -/
theorem targetWriteOfBundle (after born : Nat)
    (y : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n) (g : (Nat → Nat) × Nat)
    (h : PairBundle ref root DigitLane.writer src R after born (y, g))
    (hDig : SamplesCurrent ring root DigitLane.writer src R after y.2 (piD (ref.phys y.1)))
    (hC : CarryBits R (fun k => view ring root (piD (ref.phys y.1)) DigitLane.writer (src + R + k))
      (fun k => (piD (ref.phys y.1) (digitSite ring root (src + k))).top.d))
    (m : Nat) (hm : m < R)
    (hZ : (piD (ref.phys y.1) (digitSite ring root (src + R + m))).top.wBase ≠ .ZERO) (e : Fin n)
    (hch : (phiD ring (piD (ref.phys y.1)) e (digitSite ring root (src + R + m))).top.d ≠
      (piD (ref.phys y.1) (digitSite ring root (src + R + m))).top.d) :
    (phiD ring (piD (ref.phys y.1)) e (digitSite ring root (src + R + m))).top.d =
      (compileAdvice (ceilLogTwo n)).digitMod
        (((piD (ref.phys y.1) (digitSite ring root (src + m))).top.d).val +
          (if carryInto (fun k => (piD (ref.phys y.1) (digitSite ring root (src + k))).top.d) m
            then 1 else 0)) := by
  have hne : ring.rightNeighbor e ≠ e := bankRepairDigitRightNe ring (by omega) e
  have hV := scanValsOfBundle ref root DigitLane.writer src R after born (y, g) h hDig hC
  have hT := scanTieOfProj (root := root) (lane := DigitLane.writer) (src := src) (R := R)
    (ring := ring) (piD (ref.phys y.1))
  obtain ⟨⟨hlay, -, -, ⟨o, hcyc⟩, -⟩, -⟩ := h
  obtain ⟨hL, hb0, hbR, hb2R, hbF⟩ := hlay
  obtain ⟨-, -, hbX, hbY⟩ := widthLeadEdge ref hfix hn root y.1 hL e
  have hval : ∀ (v : Fin (compileAdvice (ceilLogTwo n)).topA) (t : Bool),
      (piD (ref.phys y.1) (digitSite ring root (src + R + m))).top.wCarry = .OFF →
      (piD (ref.phys y.1) (digitSite ring root (src + R + m))).top.wIn = .S v t →
      v = (piD (ref.phys y.1) (digitSite ring root (src + m))).top.d := by
    intro v t hoff hs
    refine settledVal (j := g.2) (o := o) hT hV hcyc hm ?_ hs
    show (piD (ref.phys y.1) (digitSite ring root (src + R + m))).top.wCarry.isW = false
    rw [hoff]
    rfl
  rcases phiChange ring _ e _ hne hZ hch with ⟨hi, cc, v, t, hb2, hw, hoff, hs, -, hnew, -⟩ |
    ⟨hi, v, t, -, hb1, hoff, hs, -, hnew, -⟩
  · rw [hbY, ← hi] at hb2
    have hm0 : m ≠ 0 := by
      intro h0
      subst h0
      rw [show src + R + 0 = src + R by omega, hbR] at hb2
      cases hb2
    obtain ⟨j, hj, rfl⟩ := bankRepairDigitSiteSurj ring root e
    rw [← bankRepairDigitSiteSucc] at hi
    have hjm : j + 1 = src + R + m := by
      by_cases hjn : j + 1 < n
      · exact (bankRepairDigitSiteInj ring root (by omega) hjn hi).symm
      · rw [show j + 1 = n by omega, bankRepairDigitSiteN] at hi
        have := bankRepairDigitSiteInj ring root (k := src + R + m) (m := 0) (by omega) (by omega) hi
        omega
    have hjv : j = src + R + (m - 1) := by omega
    subst hjv
    have hlive : (view ring root (piD (ref.phys y.1)) DigitLane.writer
        (src + R + (m - 1))).carryLive = true := by
      show (piD (ref.phys y.1) (digitSite ring root (src + R + (m - 1)))).top.wCarry.isW = true
      rw [hw]
      rfl
    have hbit := (hC (m - 1) (by omega) hlive).1
    have hcc : cc = carryInto
        (fun k => (piD (ref.phys y.1) (digitSite ring root (src + k))).top.d) m := by
      rw [show m - 1 + 1 = m by omega] at hbit
      have e1 : (view ring root (piD (ref.phys y.1)) DigitLane.writer
          (src + R + (m - 1))).carryBit = cc := by
        show wcC (piD (ref.phys y.1) (digitSite ring root (src + R + (m - 1)))).top.wCarry = cc
        rw [hw]
        rfl
      rw [← e1]
      exact hbit
    rw [hnew, hval v t hoff hs, hcc]
  · rw [hbX, ← hi] at hb1
    have hm0 : m = 0 := by
      refine Classical.byContradiction fun h0 => ?_
      have := hbF (R + m) (by omega) (by omega) (by omega)
      rw [← Nat.add_assoc, hb1] at this
      cases this
    subst hm0
    rw [hnew, hval v t hoff hs]
    rfl

end TargetWrite


/-! ### The value step -/

section Cong

variable {c : Compiled}

/-- `carryInto` reads the digits below its argument.  Consumer: `targetHold`. -/
theorem carryIntoCongr (Dp Dq : Nat → Fin c.topA) (m : Nat) (h : ∀ k, k < m → Dp k = Dq k) :
    carryInto Dp m = carryInto Dq m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [carryInto, carryInto, ih (fun k hk => h k (by omega)), h m (by omega)]

end Cong

section Dirty

variable {n : Nat} {ring : DirectedRing n} (ref : WidthDigitReference ring) (start : ref.State)
  (w : List (Fin n))

/-- **The dirty invariant from a state on**, while the site has no `ZERO` label.  Consumer:
`writerPairStep`. -/
theorem dirtyRun (hn2 : 2 ≤ n) (hd : ref.drained start) (i : Fin n) (t : Nat)
    (h0 : DirtyInv (piD (ref.phys (stateAt ref start w t).1) i)) :
    ∀ d, t + d ≤ w.length →
      (∀ k, t ≤ k → k < t + d → (piD (ref.phys (stateAt ref start w k).1) i).top.wBase ≠ .ZERO) →
      DirtyInv (piD (ref.phys (stateAt ref start w (t + d)).1) i) := by
  intro d
  induction d with
  | zero => intro _ _; exact h0
  | succ d ih =>
    intro hd1 hZ
    have hi := ih (by omega) (fun k h1 h2 => hZ k h1 (by omega))
    obtain ⟨e, he⟩ := digitPhi ref start w hd (t + d) (by omega)
    rw [← Nat.add_assoc, he]
    exact dirtyInvStep ring _ e i (bankRepairDigitRightNe ring hn2 e) (hZ (t + d) (by omega) (by omega)) hi

end Dirty

section Late

variable {c : Compiled} {n : Nat} {ring : DirectedRing n}

/-- **Every use of a completion is later than its tail sample.**  Consumer: `writerPairStep`. -/
theorem useLate (A : DigitAudit c n) (root : Fin n) (src target : Nat) (lane : DigitLane) (cut : Nat)
    (T : DigitTerminal c n) (h : DigitCompletion ring A root src target lane cut T)
    (sigma : DigitStamp n)
    (hh : ∀ (L : DigitCarryGhost c n) (v : DigitUse c n), T.ledger = some L →
      L.uses.head? = some v → v.operand = some (.sampled sigma))
    (L : DigitCarryGhost c n) (hL : T.ledger = some L) (m : Nat) (u : DigitUse c n)
    (hu : L.uses[m]? = some u) : sigma.time < u.time ∧ u.time < T.time := by
  obtain ⟨-, -, -, -, -, -, pos, ledger, samples, exports, uses, h1, -, h3, hj, hord, -⟩ := h
  have hLe : L = ledger := by
    rw [hL] at h1
    exact Option.some.inj h1
  subst hLe
  have hm : m < digitSpan c := by
    have := (List.getElem?_eq_some_iff.mp hu).1
    omega
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, u1, -, -, -, -, -, -, a3⟩ := hj ⟨m, hm⟩
  have hum : u = uses ⟨m, hm⟩ := by
    rw [hu] at u1
    exact Option.some.inj u1
  subst hum
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, v1, -, v3, -, -, a1, a2, -⟩ := hj ⟨0, pos⟩
  have hhead : L.uses.head? = some (uses ⟨0, pos⟩) := by
    have e : L.uses.head? = L.uses[0]? := by cases L.uses <;> rfl
    exact e.trans v1
  have hs := hh L _ hL hhead
  rw [v3] at hs
  have hid : (samples ⟨0, pos⟩).id = sigma := by
    simpa using hs
  refine ⟨?_, a3⟩
  rw [← hid]
  have hle : (uses ⟨0, pos⟩).time ≤ (uses ⟨m, hm⟩).time := by
    by_cases hm0 : m = 0
    · subst hm0
      exact Nat.le_refl _
    · exact Nat.le_of_lt (hord ⟨0, pos⟩ ⟨m, hm⟩ (by show 0 < m; omega)).2
  omega

end Late

section Step

variable {n : Nat} {ring : DirectedRing n} (ref : WidthBoundaryReference ring) (hn : 5 ≤ n)

include hn in
/-- **The value step of a pair of the chain.**  Consumer: `chainFacts`. -/
theorem writerPairStep (start : ref.State) (hst : ref.start start) (w : List (Fin n)) (root : Fin n)
    (hs : ref.singleton root start) (src : Nat)
    (hsp : DigitCompletePair ring root (piD (ref.phys start)) src
      (src + digitSpan (compileAdvice (ceilLogTwo n)))) (after : Nat)
    (T : DigitTerminal (compileAdvice (ceilLogTwo n)) n)
    (hT : DigitFiveCompletions ring (w.foldl (widthDigitAuditNext ref.toWidthDigitReference)
      (start, digitAuditInitial (piD (ref.phys start)))).2 root src
      (src + digitSpan (compileAdvice (ceilLogTwo n))) DigitLane.writer after T)
    (hstat : ∀ j, j < digitSpan (compileAdvice (ceilLogTwo n)) → ∀ t, after ≤ t → t < w.length →
      digitAt ref.toWidthDigitReference start w (t + 1) (digitSite ring root (src + j)) =
        digitAt ref.toWidthDigitReference start w t (digitSite ring root (src + j)))
    (hZero : ∀ j, j < digitSpan (compileAdvice (ceilLogTwo n)) → ∀ t, after ≤ t → t ≤ w.length →
      (piD (ref.phys (stateAt ref.toWidthDigitReference start w t).1)
        (digitSite ring root (src + digitSpan (compileAdvice (ceilLogTwo n)) + j))).top.wBase ≠
          .ZERO) :
    (∀ j, j < digitSpan (compileAdvice (ceilLogTwo n)) → ∀ t, T.time ≤ t → t < w.length →
      digitAt ref.toWidthDigitReference start w (t + 1)
          (digitSite ring root (src + digitSpan (compileAdvice (ceilLogTwo n)) + j)) =
        digitAt ref.toWidthDigitReference start w t
          (digitSite ring root (src + digitSpan (compileAdvice (ceilLogTwo n)) + j))) ∧
    valueBlockID ring root
        (digitValueView (piD (ref.phys (w.foldl (widthDigitAuditNext ref.toWidthDigitReference)
          (start, digitAuditInitial (piD (ref.phys start)))).1)))
        (src + digitSpan (compileAdvice (ceilLogTwo n))) =
      (valueBlockID ring root
        (digitValueView (piD (ref.phys (w.foldl (widthDigitAuditNext ref.toWidthDigitReference)
          (start, digitAuditInitial (piD (ref.phys start)))).1))) src + 1) %
        (compileAdvice (ceilLogTwo n)).topA ^ digitSpan (compileAdvice (ceilLogTwo n)) ∧
    (∀ j, j < digitSpan (compileAdvice (ceilLogTwo n)) →
      digitAt ref.toWidthDigitReference start w w.length
          (digitSite ring root (src + digitSpan (compileAdvice (ceilLogTwo n)) + j)) =
        (compileAdvice (ceilLogTwo n)).digitMod
          ((digitAt ref.toWidthDigitReference start w w.length (digitSite ring root (src + j))).val +
            (if carryInto (fun k => digitAt ref.toWidthDigitReference start w w.length
              (digitSite ring root (src + k))) j then 1 else 0))) ∧
    (∃ (born : Nat) (g : (Nat → Nat) × Nat), PairBundle ref.toWidthDigitReference root
        DigitLane.writer src (digitSpan (compileAdvice (ceilLogTwo n))) after born
        (stateAt ref.toWidthDigitReference start w w.length, g)) ∧
    SamplesCurrent ring root DigitLane.writer src (digitSpan (compileAdvice (ceilLogTwo n))) after
      (stateAt ref.toWidthDigitReference start w w.length).2
      (piD (ref.phys (stateAt ref.toWidthDigitReference start w w.length).1)) := by
  have hd : ref.toWidthDigitReference.drained start := ref.startDrained start hst
  have hn2 : 2 ≤ n := by omega
  have hR : 2 ≤ digitSpan (compileAdvice (ceilLogTwo n)) := valueSpanTwo hn
  obtain ⟨root0, hs0, hL0⟩ := widthCleanBoundaryRoot ref start hst
  have hr : root = root0 :=
    (ref.singletonFixed root0 start hs0).2.1 root (ref.singletonFixed root start hs).1
  subst hr
  obtain ⟨hsrc, hend, hlay⟩ := pairLayoutStart ref hn root start hL0 src hsp
  have hq0 : L3.WidthPacketMomentCutEntry.WidthRunInv ring ref root DigitLane.writer src
      (digitSpan (compileAdvice (ceilLogTwo n)))
      (start, digitAuditInitial (piD (ref.phys start))) :=
    ⟨widthPairInvInitial ring ref hn root DigitLane.writer _ _ start hlay, hsp⟩
  obtain ⟨t1, t2, t3, t4, h1, h2, h3, h4, h5⟩ := hT
  have htail : ∀ N : DigitTerminal (compileAdvice (ceilLogTwo n)) n,
      DigitCompletion ring
        (w.foldl (widthDigitAuditNext ref.toWidthDigitReference)
          (start, digitAuditInitial (piD (ref.phys start)))).2 root src
        (src + digitSpan (compileAdvice (ceilLogTwo n))) DigitLane.writer 0 N →
      ∃ s : DigitStamp n, s.site = digitSite ring root src ∧ s.lane = DigitLane.writer ∧
        ∀ (L : DigitCarryGhost (compileAdvice (ceilLogTwo n)) n)
          (v : DigitUse (compileAdvice (ceilLogTwo n)) n), N.ledger = some L →
          L.uses.head? = some v → v.operand = some (.sampled s) := by
    intro N hN
    obtain ⟨s, -, h2', h3', -, -, L, v, hL', hv, hop, hall⟩ :=
      completionTail ring _ root src _ DigitLane.writer 0 N hN
    exact ⟨s.id, h2', h3', hall⟩
  obtain ⟨s1, si1, sl1, hd1⟩ := htail t1 h1.1
  obtain ⟨s2, si2, sl2, hd2⟩ := htail t2 h2.1
  obtain ⟨s3, si3, sl3, hd3⟩ := htail t3 h3.1
  obtain ⟨s4, si4, sl4, hd4⟩ := htail t4 h4.1
  have a1 := h1.2.1
  have a2 := h2.2.1
  have a3 := h3.2.1
  have a4 := h4.2.1
  have a5 := h5.2.1
  have hlate := fourthTailLate ref hn root DigitLane.writer src _ hR hsrc hend _ hq0 rfl rfl w rfl
    t1 t2 t3 t4 s1 s2 s3 s4 h1.1 h2.1 h3.1 h4.1 a2 a3 a4 si1 sl1 si2 sl2 si3 sl3 si4 sl4 hd1 hd2 hd3
    hd4
  have hclkw := clockAt ref start w w.length (Nat.le_refl _)
  have hclkEnd : (w.foldl (widthDigitAuditNext ref.toWidthDigitReference)
      (start, digitAuditInitial (piD (ref.phys start)))).2.clock = w.length := by
    have := hclkw
    unfold stateAt at this
    rw [List.take_length] at this
    exact this
  have ht4le : t4.time ≤ w.length := by
    have := completionTimeLe ring _ h4.1
    omega
  have hTle : T.time ≤ w.length := by
    have := completionTimeLe ring _ h5.1
    omega
  -- the bundle from the terminal of the fourth completion on
  have hb4 : ∃ g, PairBundle ref.toWidthDigitReference root DigitLane.writer src
      (digitSpan (compileAdvice (ceilLogTwo n))) after t4.time
      (stateAt ref.toWidthDigitReference start w t4.time, g) := by
    have hc4 := clockAt ref start w t4.time ht4le
    have hback : DigitCompletion ring (stateAt ref.toWidthDigitReference start w t4.time).2 root src
        (src + digitSpan (compileAdvice (ceilLogTwo n))) DigitLane.writer 0 t4 := by
      refine completionFoldBack ref root src _ DigitLane.writer 0 t4 (w.drop t4.time) _ ?_
        (Nat.le_of_eq hc4.symm)
      have hsplit := wRunAtSplit ref.toWidthDigitReference w
        (start, digitAuditInitial (piD (ref.phys start))) t4.time
      have hst' : stateAt ref.toWidthDigitReference start w t4.time =
          wRunAt ref.toWidthDigitReference (start, digitAuditInitial (piD (ref.phys start))) w
            t4.time := rfl
      rw [hst', hsplit]
      exact h4.1
    exact bundleAtTerminal ref hn start hst (w.take t4.time) root hs DigitLane.writer src hsp
      after 0 t4 hback hc4.symm s4 si4 sl4 hd4 (by omega) (by omega)
  have hbk : ∀ k, t4.time ≤ k → k ≤ w.length → ∃ g, PairBundle ref.toWidthDigitReference root
      DigitLane.writer src (digitSpan (compileAdvice (ceilLogTwo n))) after t4.time
      (stateAt ref.toWidthDigitReference start w k, g) := by
    intro k h1k h2k
    have := bundleLater ref hn start w root DigitLane.writer src _ hR hsrc hend after t4.time t4.time
      hb4 (k - t4.time) (by omega)
    rwa [show t4.time + (k - t4.time) = k by omega] at this
  have hsk : ∀ k, k ≤ w.length → SamplesCurrent ring root DigitLane.writer src
      (digitSpan (compileAdvice (ceilLogTwo n))) after
      (stateAt ref.toWidthDigitReference start w k).2
      (piD (ref.phys (stateAt ref.toWidthDigitReference start w k).1)) :=
    fun k hk => samplesCurrentAt ref.toWidthDigitReference start w hd root DigitLane.writer src _
      after k hk hstat
  have hallk : ∀ k, L3.CarryAll (piD (ref.phys (stateAt ref.toWidthDigitReference start w k).1))
      (stateAt ref.toWidthDigitReference start w k).2.current := fun k =>
    (auditCarryInv_fold ref.toWidthDigitReference (w.take k)
      (start, digitAuditInitial (piD (ref.phys start))) hd (auditCarryInv_initial ring _)).2.1
  -- the source digits at the end
  have hDp : ∀ k, after ≤ k → k ≤ w.length → ∀ j, j < digitSpan (compileAdvice (ceilLogTwo n)) →
      digitAt ref.toWidthDigitReference start w k (digitSite ring root (src + j)) =
        digitAt ref.toWidthDigitReference start w w.length (digitSite ring root (src + j)) := by
    intro k h1k h2k j hj
    exact (digitAtConst ref.toWidthDigitReference start w _ k w.length h2k
      (fun t h3 h4 => hstat j hj t (by omega) h4)).symm
  -- the ledger of the fifth completion
  obtain ⟨L, sm, xm, uz, hTrec, hTl, hTsrc, hTL, hLi, hLlen, -, -⟩ :=
    completionRows ring _ root src _ DigitLane.writer 0 T rfl h5.1
  have hf0 : (start, digitAuditInitial (piD (ref.phys start))).2.frames = [] := rfl
  have hc0 : (start, digitAuditInitial (piD (ref.phys start))).2.clock = 0 := rfl
  obtain ⟨fT, hfT, hfTt, hfTe, hfTr⟩ := id hTrec
  obtain ⟨tT, eT, heT, htTt, rfl⟩ := wFrameTime ref.toWidthDigitReference w _ hf0 hc0 fT hfT
  have hTtime : T.time = tT + 1 := hfTt.symm.trans htTt
  have htTlt : tT < w.length := by omega
  have hTr : (digitReceiptLane DigitLane.writer
      (svcAt ring (piD (ref.phys (wRunAt ref.toWidthDigitReference
        (start, digitAuditInitial (piD (ref.phys start))) w tT).1))
        (wRunAt ref.toWidthDigitReference (start, digitAuditInitial (piD (ref.phys start))) w tT).2
        eT)).terminal = some T := by
    rw [← hTl]
    exact hfTr
  have heTe : eT = digitSite ring root (src + (2 * digitSpan (compileAdvice (ceilLogTwo n)) - 1)) := by
    rw [show src + (2 * digitSpan (compileAdvice (ceilLogTwo n)) - 1) =
      src + digitSpan (compileAdvice (ceilLogTwo n)) +
        (digitSpan (compileAdvice (ceilLogTwo n)) - 1) by omega]
    exact hfTe.trans hTsrc
  have hkT : cohortEdgeOf root src (digitSpan (compileAdvice (ceilLogTwo n))) eT =
      some (2 * digitSpan (compileAdvice (ceilLogTwo n)) - 1) := by
    rw [heTe]
    exact cohortEdgeOfSite ring root src _ hend _ (by omega)
  obtain ⟨gT, hgT⟩ := hbk tT (by omega) (by omega)
  obtain ⟨hlive, hled⟩ := wTermLedger ref hn root DigitLane.writer src _ hR hsrc hend
    (wRunAt ref.toWidthDigitReference (start, digitAuditInitial (piD (ref.phys start))) w tT)
    hgT.1.1 eT hkT T hTr
  have hLq : caA ring root DigitLane.writer src (stateAt ref.toWidthDigitReference start w tT).2
      (2 * digitSpan (compileAdvice (ceilLogTwo n)) - 1) = some L := hled.symm.trans hTL
  have hc1 := cycleOfLive ref.toWidthDigitReference root src _ DigitLane.writer after t4.time _ hgT
    (2 * digitSpan (compileAdvice (ceilLogTwo n)) - 1) (by omega) (by omega) hlive
  obtain ⟨-, -, hvT⟩ := ledgerValsOfBundle ref.toWidthDigitReference root src _ DigitLane.writer after
    t4.time _ hgT (hsk tT (by omega)) hc1 _ (by omega) (by omega) L hLq
  have hvals : ∀ m (u : DigitUse (compileAdvice (ceilLogTwo n)) n), L.uses[m]? = some u →
      u.value = digitAt ref.toWidthDigitReference start w w.length (digitSite ring root (src + m)) ∧
        t4.time < u.time := by
    intro m u hm
    obtain ⟨e1, e2⟩ := hvT m u hm
    have hmlt : m < digitSpan (compileAdvice (ceilLogTwo n)) := by
      have := (List.getElem?_eq_some_iff.mp hm).1
      omega
    exact ⟨e1.trans (hDp tT (by omega) (by omega) m hmlt), e2⟩
  have hinvEnd := (auditCarryInv_fold ref.toWidthDigitReference w
    (start, digitAuditInitial (piD (ref.phys start))) hd (auditCarryInv_initial ring _)).2
  have hch := writerTerminalChain hinvEnd T hTrec hTl L hTL hLi
  let Dp : Nat → Fin (compileAdvice (ceilLogTwo n)).topA := fun k =>
    digitAt ref.toWidthDigitReference start w w.length (digitSite ring root (src + k))
  have hcin := carryInOfChain Dp hch (fun m u hm => (hvals m u hm).1)
  obtain ⟨L', hL', htgts⟩ := usesTarget_of_completion ring _ root src _ DigitLane.writer 0 T h5.1
  have hLL : L' = L := by
    rw [hTL] at hL'
    exact (Option.some.inj hL').symm
  subst hLL
  obtain ⟨L4, hL4, htgt4⟩ := usesTarget_of_completion ring _ root src _ DigitLane.writer 0 t4 h4.1
  have hrec4 := h4.1.2.1
  have hTl4 := h4.1.2.2.1
  -- each target cell holds its digit from the use of the fifth completion on
  have hhold : ∀ j, j < digitSpan (compileAdvice (ceilLogTwo n)) →
      ∀ u : DigitUse (compileAdvice (ceilLogTwo n)) n, L'.uses[j]? = some u →
      ∀ d, u.time + d ≤ w.length →
        digitAt ref.toWidthDigitReference start w (u.time + d)
            (digitSite ring root (src + digitSpan (compileAdvice (ceilLogTwo n)) + j)) =
          (compileAdvice (ceilLogTwo n)).digitMod ((Dp j).val + (if carryInto Dp j then 1 else 0)) := by
    intro j hj u hu d
    obtain ⟨hut, hutTg⟩ : u.target = digitSite ring root (src + digitSpan (compileAdvice (ceilLogTwo n)) + j) ∧ True := by
      obtain ⟨u', h1', h2'⟩ := htgts j hj
      rw [hu] at h1'
      rw [Option.some.inj h1']
      exact ⟨h2', trivial⟩
    have hlt := useLate _ root src _ DigitLane.writer 0 T h5.1
    obtain ⟨hv, hb⟩ := hvals j u hu
    have hmem : u ∈ L'.uses := List.mem_iff_getElem?.mpr ⟨j, hu⟩
    obtain ⟨σ5, -, -, hd5⟩ := htail T h5.1
    obtain ⟨-, huT⟩ := useLate _ root src _ DigitLane.writer 0 T h5.1 σ5 hd5 L' hTL j u hu
    induction d with
    | zero =>
      intro _
      obtain ⟨f, hf, hft, hcase⟩ := terminalUsesFramed ref.toWidthDigitReference hn2 start hd w T hTrec
        hTl L' hTL u hmem
      obtain ⟨f1, f2, f3, f4⟩ := frameLink ref.toWidthDigitReference start w hd f hf
      -- the previous service of the cell: the use of the fourth completion
      obtain ⟨u4, hu4, hu4t⟩ := htgt4 j hj
      have hmem4 : u4 ∈ L4.uses := List.mem_iff_getElem?.mpr ⟨j, hu4⟩
      obtain ⟨σ4a, hσ4b⟩ := useLate _ root src _ DigitLane.writer 0 t4 h4.1 s4 hd4 L4 hL4 j u4 hu4
      obtain ⟨g4, g4m, g4t, -, g4E⟩ := terminalUsesEmptied ref.toWidthDigitReference hn2 start hd w t4
        hrec4 hTl4 L4 hL4 u4 hmem4
      obtain ⟨-, -, -, g4n⟩ := frameLink ref.toWidthDigitReference start w hd g4 g4m
      have hd0 : DirtyInv (piD (ref.phys (stateAt ref.toWidthDigitReference start w u4.time).1)
          (digitSite ring root (src + digitSpan (compileAdvice (ceilLogTwo n)) + j))) := by
        intro _ v t
        rw [← g4t, g4n, ← hu4t, g4E]
        intro hc
        cases hc
      have hrun := dirtyRun ref.toWidthDigitReference start w hn2 hd _ u4.time hd0
        (u.time - 1 - u4.time) (by omega)
        (fun k h1k h2k => hZero j hj k (by omega) (by omega))
      rw [show u4.time + (u.time - 1 - u4.time) = u.time - 1 by omega] at hrun
      obtain ⟨g5, g5m, g5t, ⟨v5, t5, hS⟩, -⟩ := terminalUsesEmptied ref.toWidthDigitReference hn2 start
        hd w T hTrec hTl L' hTL u hmem
      obtain ⟨-, -, g5o, -⟩ := frameLink ref.toWidthDigitReference start w hd g5 g5m
      have hclean : (piD (ref.phys (stateAt ref.toWidthDigitReference start w (u.time - 1)).1)
          (digitSite ring root (src + digitSpan (compileAdvice (ceilLogTwo n)) + j))).top.topDirty ≠
            true := by
        intro hdt
        refine hrun hdt v5 t5 ?_
        rw [g5o, g5t, hut] at hS
        exact hS
      have f4' := f4
      rw [f3, hft] at f4'
      have hdig : digitAt ref.toWidthDigitReference start w u.time
          (digitSite ring root (src + digitSpan (compileAdvice (ceilLogTwo n)) + j)) =
          (phiD ring (piD (ref.phys (stateAt ref.toWidthDigitReference start w (u.time - 1)).1))
            f.edge (digitSite ring root (src + digitSpan (compileAdvice (ceilLogTwo n)) + j))).top.d := by
        unfold digitAt
        rw [f4']
      rw [f3, hft, hut] at hcase
      rcases hcase with hc | hc | hc
      · rw [Nat.add_zero, hdig, hc, hv, hcin j u hu]
      · exact absurd hc hclean
      · exact absurd hc (hZero j hj _ (by omega) (by omega))
    | succ d ih =>
      intro hd1
      have hi := ih (by omega)
      have hkl : u.time + d < w.length := by omega
      obtain ⟨e, he⟩ := digitPhi ref.toWidthDigitReference start w hd (u.time + d) hkl
      rw [← Nat.add_assoc]
      have hgoal : digitAt ref.toWidthDigitReference start w (u.time + d + 1)
          (digitSite ring root (src + digitSpan (compileAdvice (ceilLogTwo n)) + j)) =
          (phiD ring (piD (ref.phys (stateAt ref.toWidthDigitReference start w (u.time + d)).1)) e
            (digitSite ring root (src + digitSpan (compileAdvice (ceilLogTwo n)) + j))).top.d := by
        unfold digitAt
        rw [he]
      rw [hgoal]
      by_cases hch : (phiD ring (piD (ref.phys (stateAt ref.toWidthDigitReference start w (u.time + d)).1)) e
            (digitSite ring root (src + digitSpan (compileAdvice (ceilLogTwo n)) + j))).top.d =
          (piD (ref.phys (stateAt ref.toWidthDigitReference start w (u.time + d)).1)
            (digitSite ring root (src + digitSpan (compileAdvice (ceilLogTwo n)) + j))).top.d
      · rw [hch]
        exact hi
      · obtain ⟨g, hg⟩ := hbk (u.time + d) (by omega) (by omega)
        have hw := targetWriteOfBundle ref.toWidthDigitReference ref.singletonFixed hn root src _ hend
          after t4.time _ g hg (hsk _ (by omega))
          (carryBitsWriter ref.toWidthDigitReference root src _ after t4.time _ hg (hsk _ (by omega))
            (hallk _)) j hj (hZero j hj _ (by omega) (by omega)) e hch
        rw [hw]
        have e1 : (piD (ref.phys (stateAt ref.toWidthDigitReference start w (u.time + d)).1)
            (digitSite ring root (src + j))).top.d = Dp j :=
          hDp (u.time + d) (by omega) (by omega) j hj
        have e2 : carryInto (fun k => (piD (ref.phys (stateAt ref.toWidthDigitReference start w
            (u.time + d)).1) (digitSite ring root (src + k))).top.d) j = carryInto Dp j :=
          carryIntoCongr _ _ j fun k hk => hDp (u.time + d) (by omega) (by omega) k (by omega)
        rw [e1, e2]
  refine ⟨fun j hj t h1t h2t => ?_, ?_, fun j hj => ?_,
    ⟨t4.time, hbk w.length ht4le (Nat.le_refl _)⟩, hsk w.length (Nat.le_refl _)⟩
  · obtain ⟨u, hu, -⟩ := htgts j hj
    obtain ⟨σ5, -, -, hd5⟩ := htail T h5.1
    obtain ⟨-, huT⟩ := useLate _ root src _ DigitLane.writer 0 T h5.1 σ5 hd5 L' hTL j u hu
    have e1 := hhold j hj u hu (t - u.time) (by omega)
    have e2 := hhold j hj u hu (t + 1 - u.time) (by omega)
    rw [show u.time + (t - u.time) = t by omega] at e1
    rw [show u.time + (t + 1 - u.time) = t + 1 by omega] at e2
    rw [e1, e2]
  · have hendv : ∀ i, (digitValueView (piD (ref.phys (w.foldl (widthDigitAuditNext
        ref.toWidthDigitReference) (start, digitAuditInitial (piD (ref.phys start)))).1)) i).2 =
        digitAt ref.toWidthDigitReference start w w.length i := by
      intro i
      simp [digitValueView, digitAt, stateAt, List.take_length]
    refine blockValue_succ_of_cells (ring := ring) (root := root) _ src _ hch hLlen ?_ ?_
    · intro j hj
      obtain ⟨u, hu, -⟩ := htgts j hj
      rw [hendv]
      have e1 : ledgerIn L'.uses j = (u.value).val := by
        unfold ledgerIn
        rw [hu]
        rfl
      rw [e1, (hvals j u hu).1]
    · intro j hj
      obtain ⟨u, hu, hut⟩ := htgts j hj
      obtain ⟨σ5, -, -, hd5⟩ := htail T h5.1
      obtain ⟨-, huT⟩ := useLate _ root src _ DigitLane.writer 0 T h5.1 σ5 hd5 L' hTL j u hu
      rw [hendv, ledgerOut_of_get _ j u hu]
      have e := hhold j hj u hu (w.length - u.time) (by omega)
      rw [show u.time + (w.length - u.time) = w.length by omega] at e
      rw [e, (hvals j u hu).1, hcin j u hu]
      rfl
  · obtain ⟨u, hu, -⟩ := htgts j hj
    obtain ⟨σ5, -, -, hd5⟩ := htail T h5.1
    obtain ⟨-, huT⟩ := useLate _ root src _ DigitLane.writer 0 T h5.1 σ5 hd5 L' hTL j u hu
    have e := hhold j hj u hu (w.length - u.time) (by omega)
    rw [show u.time + (w.length - u.time) = w.length by omega] at e
    exact e

end Step

end L3.QuietEntryValues

#print axioms L3.QuietEntryValues.samplesCurrentAt
#print axioms L3.QuietEntryValues.bundleAtTerminal
#print axioms L3.QuietEntryValues.bundleLater
#print axioms L3.QuietEntryValues.settledVal
#print axioms L3.QuietEntryValues.targetWriteOfBundle
#print axioms L3.QuietEntryValues.writerPairStep
