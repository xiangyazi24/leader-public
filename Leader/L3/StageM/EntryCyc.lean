import Leader.L3.StageM.EntryPack
import Leader.L3.Width.DigitFirstZero
import Leader.L3.Width.DigitBand

/-!
# The pinned cycle start after a strict completion, and the headline premise `hpin`

`WidthCycStartAfterStrict` (`L3.StageMEntryPin`) asks, on a first-zero run with a strict
completion (cut `0`) of an interior writer pair, for an earlier state of the run with the run
invariant of the pair and a pinned cycle start. The state is the one right after the export of
the strict cohort's tail sample:

* `completionRows`: the rows of a recorded completion, indexed by `Nat`.
* `wCycStartOfCompletion`: on a coupled run from a start with the run invariant and the initial
  audit, a recorded completion of the pair gives, right after the tail export, `lam = 0` as a cycle
  witness with counter `0` at old phase `0` (`CohortCycIn R 0`; chosen half by
  `strictLaneOfExport` from the sweep `wSweepAtExport`, old half `wPackedAtExport`) and the chosen
  home cells read at their own cells (`ChosenInv`, `chosenOfYoungTail`).
* `cycStartAfterStrict`: `WidthCycStartAfterStrict` at every boundary reference (the pair is
  aligned with the first delimiter of the clean start, so `widthCleanRunStart` gives the run
  invariant at the start).
* `bandPinAfterStrict`: the headline premise `hpin` (`pinAfterStrictOfCycStart`, both bands).
-/

namespace L3.StageMEntryCyc

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

section Generic

/-- An index with an entry is inside the list. Consumer: `wCycStartOfCompletion`. -/
theorem getLt {α : Type} {l : List α} {t : Nat} {e : α} (h : l[t]? = some e) : t < l.length := by
  rcases Nat.lt_or_ge t l.length with h' | h'
  · exact h'
  · rw [List.getElem?_eq_none_iff.mpr h'] at h
    cases h

/-- **The rows of a recorded completion**, indexed by `Nat` (sample, export and use `m` of the
pair, `m < R`), with the reverse export order and the forward use order. Consumer:
`wCycStartOfCompletion`. -/
theorem completionRows {c : Compiled} {n : Nat} (ring : DirectedRing n) (A : DigitAudit c n)
    (root : Fin n) (src R : Nat) (lane : DigitLane) (cut : Nat) (tm : DigitTerminal c n)
    (hRd : digitSpan c = R) (h : DigitCompletion ring A root src (src + R) lane cut tm) :
    ∃ (L : DigitCarryGhost c n) (sm : Nat → DigitSample c n) (xm : Nat → DigitExport c n)
      (uz : Nat → DigitUse c n),
      DigitRecordedTerminal A tm ∧ tm.lane = lane ∧
      tm.source = digitSite ring root (src + R + (R - 1)) ∧
      tm.ledger = some L ∧ L.inherited = none ∧ L.uses.length = R ∧
      (∀ m, m < R →
        DigitRecordedSample A (sm m) ∧ (sm m).id.lane = lane ∧
        (sm m).id.site = digitSite ring root (src + m) ∧ (sm m).tail = decide (m = 0) ∧
        DigitRecordedExport A (xm m) ∧ (xm m).lane = lane ∧
        (xm m).source = digitSite ring root (src + (R - 1)) ∧
        (xm m).operand = some (.sampled (sm m).id) ∧
        L.uses[m]? = some (uz m) ∧ (uz m).operand = some (.sampled (sm m).id) ∧
        (sm m).id.time < (xm m).time ∧ (xm m).time < (uz m).time ∧ (uz m).time < tm.time) ∧
      (∀ i j, i < j → j < R → (xm j).time < (xm i).time ∧ (uz i).time < (uz j).time) := by
  subst hRd
  dsimp only [DigitCompletion] at h
  obtain ⟨-, hTrec, hTl, hTsrc, -, -, hpos, L, smp, exs, us, hL, hLi, hLlen, hall, hord, -⟩ := h
  refine ⟨L, fun m => if hm : m < digitSpan c then smp ⟨m, hm⟩ else smp ⟨0, hpos⟩,
    fun m => if hm : m < digitSpan c then exs ⟨m, hm⟩ else exs ⟨0, hpos⟩,
    fun m => if hm : m < digitSpan c then us ⟨m, hm⟩ else us ⟨0, hpos⟩,
    hTrec, hTl, hTsrc, hL, hLi, hLlen, ?_, ?_⟩
  · intro m hm
    obtain ⟨h1, h2, h3, -, h5, h6, h7, h8, -, h10, -, -, h13, -, h15, -, -, h18, h19, h20⟩ :=
      hall ⟨m, hm⟩
    simp only [dif_pos hm]
    exact ⟨h1, h2, h3, h5, h6, h7, h8, h10, h13, h15, h18, h19, h20⟩
  · intro i j hij hj
    simp only [dif_pos hj, dif_pos (show i < digitSpan c by omega)]
    exact hord ⟨i, by omega⟩ ⟨j, hj⟩ hij

end Generic

section Coupled

variable {n : Nat} {ring : DirectedRing n} (ref : WidthBoundaryReference ring) (hn : 5 ≤ n)
  (root : Fin n) (lane : DigitLane) (src R : Nat) (hR : 2 ≤ R) (hsrc : 2 ≤ src)
  (hend : src + 2 * R < n)
  (q0 : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n)
  (hq0 : WidthRunInv ring ref root lane src R q0)
  (hi0 : q0.2 = digitAuditInitial (piD (ref.phys q0.1))) (hc0 : q0.2.clock = 0)
  (W : List (Fin n))

include hn hR hsrc hend hq0 hi0 hc0 in
/-- **A pinned cycle start after the tail export.** On the coupled run of `W` from a start with the
run invariant of the pair and the initial audit, a recorded completion of the pair `(src, src + R)`
gives, right after the export of the strict tail sample, `lam = 0` with counter `0` as a cycle
witness at old phase `0` (chosen half: `wTailRun`, `wSweepAtExport`, `strictLaneOfExport`; old
half: the strict ledger `wCarryChain` and `wPackedAtExport`) and the chosen home cells read at
their own cells (`chosenOfYoungTail`). Consumer: `cycStartAfterStrict`. -/
theorem wCycStartOfCompletion (hRd : digitSpan (compileAdvice (ceilLogTwo n)) = R) (cut : Nat)
    (tm : DigitTerminal (compileAdvice (ceilLogTwo n)) n)
    (hcomp : DigitCompletion ring (wRunAt ref.toWidthDigitReference q0 W W.length).2 root src
      (src + R) lane cut tm) :
    ∃ t, t ≤ W.length ∧
      CohortCycIn R 0 (wLane ref root lane src R q0 W t) ((fun _ => 0), 0) 0 ∧
      ChosenInv R (SPin ring root lane src (wRunAt ref.toWidthDigitReference q0 W t).2)
        (tracked ring root lane src R (wRunAt ref.toWidthDigitReference q0 W t).2) (fun _ => 0) := by
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
  refine ⟨tx + 1, htx, ⟨rfl, ⟨?_, ?_⟩, ?_, ?_⟩, chosenOfYoungTail hYT⟩
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

end Coupled

section Boundary

variable {n : Nat} {ring : DirectedRing n} (ref : WidthBoundaryReference ring) (hn : 5 ≤ n)

include hn in
/-- **`WidthCycStartAfterStrict` at a boundary reference.** A strict completion of the writer pair
at `src` on a first-zero run: `src` is a delimiter of the clean start, hence `first + i * R` for the
first delimiter `first`, so the start has the run invariant of the pair (`widthCleanRunStart`); the
whole run from the start then has the pinned cycle start right after the tail export
(`wCycStartOfCompletion`). Consumer: `bandPinAfterStrict`. -/
theorem cycStartAfterStrict :
    WidthCycStartAfterStrict ref := by
  intro root x hx src tm h2 hend hcomp
  obtain ⟨start, word0, word, y, _, hs, hy, hW, -, -, -, hxw⟩ := hx
  have hR := valueSpanTwo hn
  have hst : x.2.start = piD (ref.phys start) := by
    rw [← hxw, widthFoldStart ring ref word y, ← hy, widthFoldStart ring ref word0]
    rfl
  have hW' : WFixedRoot ring root (piW (ref.phys (word0.foldl ref.next start))) := by
    have h1 := widthAuditFoldFst ref.toWidthDigitReference word0
      (start, digitAuditInitial (piD (ref.phys start)))
    rw [hy] at h1
    rw [← h1]
    exact hW
  -- the pair is aligned with the first delimiter of the start
  obtain ⟨root0, hs0, hL⟩ := widthCleanBoundaryRoot ref start hs
  have hsw := widthSingletonFold ring ref root0 word0 start hs0
  have hfix := ref.singletonFixed root0 _ hsw
  have hr : root = root0 := hfix.2.1 root hW'.1
  subst hr
  obtain ⟨first0, ht, -, hb⟩ := widthCleanBoundaryDelimiters ref hn root start hL
  have ht2 : 2 ≤ (compileAdvice (ceilLogTwo n)).t :=
    compileAdvice_t_ge_two (ceilLogTwo n) (ringQ_facts n hn).1
  obtain ⟨⟨⟨⟨⟨-, -, hbeta⟩, -⟩, -⟩, -⟩, -⟩ := id hcomp
  rw [hst] at hbeta
  obtain ⟨hfs, hmod⟩ := (hb src (by omega) (by omega)).1 hbeta
  have hf : DigitFirstDelimiter ring root (piD (ref.phys start)) first0 := by
    refine ⟨⟨by omega, by omega, (hb first0 (by omega) (by omega)).2 ⟨Nat.le_refl _, by simp⟩⟩,
      fun k hk1 hk2 => ?_⟩
    cases hbk : (piD (ref.phys start) (digitSite ring root k)).word.beta with
    | false => rfl
    | true =>
      exfalso
      have := ((hb k hk1 (by omega)).1 hbk).1
      omega
  obtain ⟨i, hi⟩ : ∃ i, src = first0 + i * valueSpan n := by
    refine ⟨(src - first0) / valueSpan n, ?_⟩
    have h1 := Nat.div_add_mod (src - first0) (valueSpan n)
    rw [show (src - first0) % valueSpan n = 0 from hmod, Nat.add_zero, Nat.mul_comm] at h1
    rw [h1]
    omega
  have hend' : first0 + i * valueSpan n + 2 * valueSpan n < n := by
    rw [← hi]
    exact hend
  obtain ⟨-, hI⟩ := widthCleanRunStart ring ref hn root DigitLane.writer start hs word0 hW'
    first0 hf i hend'
  have hq0 : WidthRunInv ring ref root DigitLane.writer src (valueSpan n)
      (start, digitAuditInitial (piD (ref.phys start))) := by
    rw [hi]
    exact hI
  -- the whole run from the start
  have hxW : (word0 ++ word).foldl (widthDigitAuditNext ref.toWidthDigitReference)
      (start, digitAuditInitial (piD (ref.phys start))) = x := by
    rw [List.foldl_append, hy, hxw]
  have hxEnd : wRunAt ref.toWidthDigitReference (start, digitAuditInitial (piD (ref.phys start)))
      (word0 ++ word) (word0 ++ word).length = x := by
    rw [wRunAtLen ref.toWidthDigitReference _ _ _ (Nat.le_refl _), hxW]
  rw [← hxEnd] at hcomp
  obtain ⟨t, -, hcyc, hch⟩ := wCycStartOfCompletion ref hn root DigitLane.writer src (valueSpan n)
    hR h2 hend (start, digitAuditInitial (piD (ref.phys start))) hq0 rfl rfl (word0 ++ word) rfl 0
    tm hcomp
  refine ⟨wRunAt ref.toWidthDigitReference (start, digitAuditInitial (piD (ref.phys start)))
      (word0 ++ word) t, (word0 ++ word).drop t, ?_,
    wInvAt ref hn root DigitLane.writer src (valueSpan n) hR h2 hend _ hq0 (word0 ++ word) t,
    ⟨0, hcyc⟩, hch⟩
  rw [wRunAtSplit ref.toWidthDigitReference (word0 ++ word) _ t]
  exact hxW

end Boundary

/-- **The headline premise `hpin`**: `WidthPinAfterStrict` at the band reference (SMALL and BANK
through their boundary references, `pinAfterStrictOfCycStart` with `cycStartAfterStrict`).
Consumer: `hpin` of `l3HeadlineOfCleanBranches`. -/
theorem bandPinAfterStrict {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    :
    WidthPinAfterStrict (bandWidthDigitReference ring hn) := by
  by_cases hs : (compileAdvice (ceilLogTwo n)).useSmall = true
  · rw [bandWidthDigitReferenceSmall ring hn hs]
    exact pinAfterStrictOfCycStart (smallWidthBoundaryReference ring hn hs) hn
      (cycStartAfterStrict (smallWidthBoundaryReference ring hn hs) hn)
  · have hb : (compileAdvice (ceilLogTwo n)).useSmall = false := by
      cases hh : (compileAdvice (ceilLogTwo n)).useSmall
      · rfl
      · exact absurd hh hs
    rw [bandWidthDigitReferenceBank ring hn hb]
    exact pinAfterStrictOfCycStart (bankWidthBoundaryReference ring hn hb) hn
      (cycStartAfterStrict (bankWidthBoundaryReference ring hn hb) hn)

end L3.StageMEntryCyc

#print axioms L3.StageMEntryCyc.completionRows
#print axioms L3.StageMEntryCyc.wCycStartOfCompletion
#print axioms L3.StageMEntryCyc.cycStartAfterStrict
#print axioms L3.StageMEntryCyc.bandPinAfterStrict
