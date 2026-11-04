import Leader.L3.Width.DigitWriterCurrentCyc
import Leader.L3.Width.DigitWriterOrder

/-!
# The writer-lane age core: the tail of a late completion is stamped after the cut

`L3.WriterCurrent.WriterAgedCore`: at the terminal state of the fifth next writer completion after
`after`, every tracked atom and every operand of a target ledger is a sample stamped after `after`.
The comparison lane's entry (`L3.CloseTerm.entryCoreOfBarrier`) has `restart < sigma.time` in the
definition of its completion; the writer completions after `after` have cut `0`, so the new content
is the age of the tail sample.  The barrier machinery of `L3.TermEntry` is generic in the lane.

The counting argument, at the state just before the terminal letter of the first completion `T1`:
the live last carry is the barrier of the tail `s1` at the last target cell, and behind it the shape
is a chosen cohort and its younger cohort (`BarShape`), which leaves two cells for a border tail:
the chosen cohort's tail cell and the delimiter (`tailAtPositions`).  A later completion's tail
stamped by that state still has a barrier location there, since a barrier location only hops, stays
or is created by its own border read (`barBack`, from `L3.TermEntry.barAtBack`).  So the tails of
`T2`, `T3`, `T4` cannot all be stamped by then (`fourthTailLate`), and the tail of `T4`, hence of the
fifth completion, is stamped after `after`.  The terminal letter then gives the cycle class and
`WinAge` of that tail (`terminalEntry`, from `L3.TermEntry.termEntryRing`).

Clause (A2c) of the core is the age half of the ledger clause of `WinAge`, the class carried along
later letters.  At this terminal state no target ledger is held (`L3.TermEntry.termEntry`), so the
clause holds with no ledger to check.
-/

namespace L3.WriterAged

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
open L3.TermEntry
open L3.CurrentWin
open L3.CloseCurrent
open L3.CloseEntry
open L3.CloseRank
open L3.CloseOrder
open L3.WriterOrder
open L3.CohortOrder

/-! ### The tail cells behind a last-cell barrier -/

section Shape

variable {c : Compiled} {n : Nat} {R : Nat}

/-- **Behind a live last carry two cells can hold a border tail**: every barrier location is the
carry's own, or a source packet at the delimiter or at the chosen cohort's tail cell `p`.  Consumer:
`fourthTailLate`. -/
theorem tailAtPositions (hR : 2 ≤ R) {s : CohortLane} {g : Nat → DigitLaneGhost c n}
    {sigma : DigitStamp n} (hsh : BarShape R s (2 * R - 1)) (hlive : s.live (2 * R - 1) = true)
    (L : DigitCarryGhost c n) (u : DigitUse c n) (hL : (g (2 * R - 1)).carry = some L)
    (hu : L.uses.head? = some u) (hop : u.operand = some (.sampled sigma)) :
    ∃ p : Nat, ∀ (tau : DigitStamp n) (q : Nat), BarAt R s g tau q →
      tau = sigma ∨ ((q = 0 ∨ q = p) ∧ (g q).out.atom = some (.sampled tau)) := by
  obtain ⟨lam, hch, hY⟩ := hsh.2 (by omega)
  have hpre := chosenTailLt hch (by omega)
  have hposLast : cohortPos R lam (R - 1) = lam (R - 1) := by
    unfold cohortPos
    omega
  have key : ∀ q, q < 2 * R - 1 → lam (R - 1) < q → cohortTok R s q ≠ .pkt true := by
    intro q h1 h2 ht
    by_cases hex : ∃ i, i < R ∧ cohortPos R lam i = q
    · obtain ⟨i, hi, hpi⟩ := hex
      rcases hch.pkt i hi with h3 | ⟨h3, -⟩ | ⟨h3, -⟩
      · rw [hpi, ht] at h3
        have h4 : cohortTail R i = true := (CohortTok.pkt.inj h3).symm
        have h5 : i + 1 = R := of_decide_eq_true h4
        have h6 : i = R - 1 := by omega
        subst h6
        rw [hposLast] at hpi
        omega
      · rw [hpi, ht] at h3
        cases h3
      · rw [hpi, ht] at h3
        cases h3
    · rw [hch.gap q h1 h2 (fun i hi he => hex ⟨i, hi, he⟩)] at ht
      cases ht
  refine ⟨lam (R - 1), fun tau q h => ?_⟩
  rcases h with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3, h4, -⟩ | ⟨h1, h2, -⟩ | ⟨h1, h2, h3, L', u', h4, -, h6, h7⟩
  · refine Or.inr ⟨?_, h3⟩
    have htok : cohortTok R s q = .pkt true := by
      rw [cohortTokSrc s h1, h2]
      rfl
    rcases Nat.lt_trichotomy q (lam (R - 1)) with hlt | he | hgt
    · rcases hY q hlt h1 with h5 | h5
      · rw [htok] at h5
        cases h5
      · rw [htok] at h5
        have h6 : decide (q = 0) = true := (CohortTok.pkt.inj h5).symm
        exact Or.inl (of_decide_eq_true h6)
    · exact Or.inr he
    · exact absurd htok (key q (by omega) hgt)
  · exfalso
    by_cases hq : q = 2 * R - 1
    · subst hq
      rw [hlive] at h3
      cases h3
    · have htok : cohortTok R s q = .pkt true := by
        rw [cohortTokTgt s h1, h4, h3]
        rfl
      exact key q (by omega) (by omega) htok
  · exfalso
    subst h1
    obtain ⟨-, h5⟩ := barTgt hsh (by omega) (by omega) q (Nat.le_refl _) (by omega)
    rcases h5 with h5 | ⟨T, h5⟩ <;> rw [h2] at h5 <;> cases h5
  · by_cases hq : q = 2 * R - 1
    · subst hq
      have e1 : L' = L := Option.some.inj (h4.symm.trans hL)
      subst e1
      have e2 : u' = u := Option.some.inj (h6.symm.trans hu)
      subst e2
      have e3 := h7.symm.trans hop
      simp only [Option.some.injEq, DigitAtom.sampled.injEq] at e3
      exact Or.inl e3
    · exfalso
      obtain ⟨h5, -⟩ := barTgt hsh (by omega) (by omega) q h1 (by omega)
      rw [h3] at h5
      cases h5

end Shape

/-! ### The run -/

section Run

variable {n : Nat} {ring : DirectedRing n} (ref : WidthBoundaryReference ring) (hn : 5 ≤ n)
  (root : Fin n) (lane : DigitLane) (src R : Nat) (hR : 2 ≤ R) (hsrc : 2 ≤ src)
  (hend : src + 2 * R < n)
  (q0 : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n)
  (hq0 : L3.WidthPacketMomentCutEntry.WidthRunInv ring ref root lane src R q0)
  (hi0 : q0.2 = digitAuditInitial (piD (ref.phys q0.1))) (hc0 : q0.2.clock = 0)
  (W : List (Fin n))

include hn hR hsrc hend hq0 hi0 in
/-- The lane run invariants at every prefix.  Consumer: `barBackStep`, `fourthTailLate`. -/
theorem laneRunAt (t : Nat) :
    LaneRun ring root lane src R (piD (ref.phys (wRunAt ref.toWidthDigitReference q0 W t).1))
      (wRunAt ref.toWidthDigitReference q0 W t).2 :=
  (laneRunFold ref hn root lane src R hR hsrc hend (W.take t) q0 hq0
    (by rw [hi0]; exact laneRunInitial ref root lane src R hR q0.1)).2

/-- The barrier location of `sigma` at cell `q` at the prefix `t`.  Consumer: `barBack`,
`completionBar`, `fourthTailLate`. -/
def BarPrefix (t : Nat) (sigma : DigitStamp n) (q : Nat) : Prop :=
  BarAt R (wLane ref root lane src R q0 W t)
    (laneCells ring root lane src (wRunAt ref.toWidthDigitReference q0 W t).2.current) sigma q

include hn hR hsrc hend hq0 hi0 hc0 in
/-- **A barrier location one letter back**: a stamp not newer than the prefix `t` has a barrier
location at `t` if it has one at `t + 1` (`L3.TermEntry.barAtBack`; the border read is excluded by
the stamp's time).  Consumer: `barBack`. -/
theorem barBackStep (t : Nat) (ht : t < W.length) (sigma : DigitStamp n)
    (hsi : sigma.site = digitSite ring root src) (hsl : sigma.lane = lane) (hold : sigma.time ≤ t)
    (q : Nat) (h : BarPrefix ref root lane src R q0 W (t + 1) sigma q) :
    ∃ q', BarPrefix ref root lane src R q0 W t sigma q' := by
  obtain ⟨e, -, hst, -⟩ := wStepAt ref root src R q0 W t ht
  have hclk := wClock ref q0 hc0 W t (Nat.le_of_lt ht)
  obtain ⟨⟨hl0, -, -, -, hg⟩, -⟩ := wInvAt ref hn root lane src R hR hsrc hend q0 hq0 W t
  obtain ⟨-, -, ⟨hne, hbt, -⟩, -, -⟩ := laneRunAt ref hn root lane src R hR hsrc hend q0 hq0 hi0 W t
  unfold BarPrefix wLane at h
  rw [hst] at h
  unfold BarPrefix wLane
  generalize wRunAt ref.toWidthDigitReference q0 W t = y at hl0 hg hne hbt h hclk ⊢
  obtain ⟨hL0, hb0, hbR, hb2R, hbF⟩ := hl0
  obtain ⟨heq, hroot, hbX, hbY⟩ := widthLeadEdge ref.toWidthDigitReference ref.singletonFixed hn
    root y.1 hL0 e
  obtain ⟨j, hj, rfl⟩ := bankRepairDigitSiteSurj ring root e
  have h' : BarAt R (cohortProj ring root lane src R (piD (ref.phys (ref.next y.1 (digitSite ring root j)))))
      (laneCells ring root lane src (digitAuditStep ring (piD (ref.phys y.1)) y.2
        (digitSite ring root j)).current) sigma q := h
  rw [heq, cohortProjStep ring (by omega) root (piD (ref.phys y.1)) R src hR hsrc hend hroot hb0 hbR
    hb2R hbF lane j hj hbX hbY] at h'
  have hrows := laneRowsRing ring (by omega) root (piD (ref.phys y.1)) R src hR hsrc hend hroot hb0
    hbR hb2R hbF lane y.2 j hj hbX hbY hg.1
  have hT : ∀ T, GhostOk ring root lane src R (InheritedOk lane) y.2 T (.sampled sigma) → T = true := by
    intro T hok
    rcases hok with hb | ⟨smp, hid, hrec, htail, -⟩
    · exact absurd hb (inheritedNoSample lane T sigma)
    · have hsid : smp.id = sigma := by
        simp only [DigitAtom.sampled.injEq] at hid
        exact hid.symm
      rw [← htail]
      exact hbt smp hrec (by rw [hsid]; exact hsi) (by rw [hsid]; exact hsl)
  rcases barAtBack hR _ hrows hg.1 hne hT q h' with ⟨he, -⟩ | h0 | ⟨-, -, -, h1, -, -⟩
  · exfalso
    rw [he] at hold
    simp only at hold
    omega
  · exact ⟨q, h0⟩
  · exact ⟨q - 1, h1⟩

include hn hR hsrc hend hq0 hi0 hc0 in
/-- **A barrier location back to any prefix at or after the stamp.**  Consumer: `fourthTailLate`. -/
theorem barBack (sigma : DigitStamp n) (hsi : sigma.site = digitSite ring root src)
    (hsl : sigma.lane = lane) (t : Nat) (hold : sigma.time ≤ t) (d : Nat) :
    t + d ≤ W.length → ∀ q, BarPrefix ref root lane src R q0 W (t + d) sigma q →
      ∃ q', BarPrefix ref root lane src R q0 W t sigma q' := by
  induction d with
  | zero => intro _ q h; exact ⟨q, h⟩
  | succ d ih =>
    intro hle q h
    obtain ⟨q', h'⟩ := barBackStep ref hn root lane src R hR hsrc hend q0 hq0 hi0 hc0 W (t + d)
      (by omega) sigma hsi hsl (by omega) q h
    exact ih (by omega) q' h'

include hn hR hsrc hend hq0 hi0 hc0 in
/-- **A completion's tail is at the last target cell just before its terminal letter**: the terminal
is letter `U.time - 1` of the word, and the carry there is the completion's clean ledger.  Consumer:
`fourthTailLate`. -/
theorem completionBar (hRd : digitSpan (compileAdvice (ceilLogTwo n)) = R) (cut : Nat)
    (U : DigitTerminal (compileAdvice (ceilLogTwo n)) n)
    (hU : DigitCompletion ring (W.foldl (widthDigitAuditNext ref.toWidthDigitReference) q0).2 root src
      (src + R) lane cut U) (sigma : DigitStamp n)
    (hh : ∀ (L : DigitCarryGhost (compileAdvice (ceilLogTwo n)) n)
      (v : DigitUse (compileAdvice (ceilLogTwo n)) n), U.ledger = some L →
      L.uses.head? = some v → v.operand = some (.sampled sigma)) :
    ∃ (tT : Nat) (eT : Fin n), W[tT]? = some eT ∧ U.time = tT + 1 ∧
      eT = digitSite ring root (src + (2 * R - 1)) ∧
      (wLane ref root lane src R q0 W tT).live (2 * R - 1) = true ∧
      ∃ (L : DigitCarryGhost (compileAdvice (ceilLogTwo n)) n)
        (v : DigitUse (compileAdvice (ceilLogTwo n)) n),
        (laneCells ring root lane src (wRunAt ref.toWidthDigitReference q0 W tT).2.current
          (2 * R - 1)).carry = some L ∧ L.inherited = none ∧ L.uses.head? = some v ∧
        v.operand = some (.sampled sigma) := by
  obtain ⟨L, sm, xm, uz, hTrec, hTl, hTsrc, hTL, hLi, -, hrow, -⟩ :=
    completionRows ring _ root src R lane cut U hRd hU
  have hf0 : q0.2.frames = [] := by rw [hi0]; rfl
  obtain ⟨fT, hfT, hfTt, hfTe, hfTr⟩ := id hTrec
  obtain ⟨tT, eT, heT, htTt, rfl⟩ := wFrameTime ref.toWidthDigitReference W q0 hf0 hc0 fT hfT
  have hTr : (digitReceiptLane lane
      (svcAt ring (piD (ref.phys (wRunAt ref.toWidthDigitReference q0 W tT).1))
        (wRunAt ref.toWidthDigitReference q0 W tT).2 eT)).terminal = some U := by
    rw [← hTl]
    exact hfTr
  have heTe : eT = digitSite ring root (src + (2 * R - 1)) := by
    rw [show src + (2 * R - 1) = src + R + (R - 1) by omega]
    exact hfTe.trans hTsrc
  have hkT : cohortEdgeOf root src R eT = some (2 * R - 1) := by
    rw [heTe]
    exact cohortEdgeOfSite ring root src R hend (2 * R - 1) (by omega)
  obtain ⟨hlive, hled⟩ := wTermLedger ref hn root lane src R hR hsrc hend _
    (wInvAt ref hn root lane src R hR hsrc hend q0 hq0 W tT).1.1 eT hkT U hTr
  have hhd : L.uses.head? = some (uz 0) := by
    have e : L.uses.head? = L.uses[0]? := by cases L.uses <;> rfl
    exact e.trans (hrow 0 (by omega)).2.2.2.2.2.2.2.2.1
  exact ⟨tT, eT, heT, hfTt.symm.trans htTt, heTe, hlive, L, uz 0, hled.symm.trans hTL, hLi, hhd,
    hh L (uz 0) hTL hhd⟩

include hn hR hsrc hend hq0 hi0 in
/-- **Later completions have strictly later tails** (`OrderRun`, `HeadDead`).  Consumer:
`fourthTailLate`, `writerAgedCoreOf`. -/
theorem tailLt (hRd : digitSpan (compileAdvice (ceilLogTwo n)) = R) (cut0 cut : Nat)
    (T0 T : DigitTerminal (compileAdvice (ceilLogTwo n)) n) (s0 s : DigitStamp n)
    (hT0 : DigitCompletion ring (W.foldl (widthDigitAuditNext ref.toWidthDigitReference) q0).2 root src
      (src + R) lane cut0 T0)
    (hT : DigitCompletion ring (W.foldl (widthDigitAuditNext ref.toWidthDigitReference) q0).2 root src
      (src + R) lane cut T) (hlt : T0.time < T.time)
    (h0 : ∀ (L : DigitCarryGhost (compileAdvice (ceilLogTwo n)) n)
      (v : DigitUse (compileAdvice (ceilLogTwo n)) n), T0.ledger = some L →
      L.uses.head? = some v → v.operand = some (.sampled s0))
    (h1 : ∀ (L : DigitCarryGhost (compileAdvice (ceilLogTwo n)) n)
      (v : DigitUse (compileAdvice (ceilLogTwo n)) n), T.ledger = some L →
      L.uses.head? = some v → v.operand = some (.sampled s)) :
    s0.time < s.time := by
  subst hRd
  obtain ⟨-, -, -, ⟨-, hI2⟩, -, hD2⟩ := (laneRunFold ref hn root lane src _ hR hsrc hend W q0 hq0
    (by rw [hi0]; exact laneRunInitial ref root lane src _ hR q0.1)).2
  have hh0 := termHeadOfCompletion ring _ root src lane cut0 T0 s0 hT0 h0
  have hh1 := termHeadOfCompletion ring _ root src lane cut T s hT h1
  rcases Nat.lt_or_ge s0.time s.time with hl | hge
  · exact hl
  · exfalso
    have hle2 := hI2 T0 s0 T s hh0 hh1 hlt
    have he : s0 = s := stampEq (by omega) (by rw [hh0.2.2.2.1, hh1.2.2.2.1])
      (by rw [hh0.2.2.2.2.1, hh1.2.2.2.2.1])
    rw [← he] at hh1
    exact hD2 T0 T s0 hh0 hh1 hlt

include hn hR hsrc hend hq0 hi0 hc0 in
/-- **The tail of the fourth of four completions is stamped by no state before the first terminal
letter**: just before that letter, the tails of the three later completions would each have a
barrier location, at distinct cells, and only two cells are available (`tailAtPositions`).  Consumer:
`writerAgedCoreOf`. -/
theorem fourthTailLate (hRd : digitSpan (compileAdvice (ceilLogTwo n)) = R)
    (T1 T2 T3 T4 : DigitTerminal (compileAdvice (ceilLogTwo n)) n)
    (s1 s2 s3 s4 : DigitStamp n)
    (h1 : DigitCompletion ring (W.foldl (widthDigitAuditNext ref.toWidthDigitReference) q0).2 root src
      (src + R) lane 0 T1)
    (h2 : DigitCompletion ring (W.foldl (widthDigitAuditNext ref.toWidthDigitReference) q0).2 root src
      (src + R) lane 0 T2)
    (h3 : DigitCompletion ring (W.foldl (widthDigitAuditNext ref.toWidthDigitReference) q0).2 root src
      (src + R) lane 0 T3)
    (h4 : DigitCompletion ring (W.foldl (widthDigitAuditNext ref.toWidthDigitReference) q0).2 root src
      (src + R) lane 0 T4)
    (hlt12 : T1.time < T2.time) (hlt23 : T2.time < T3.time) (hlt34 : T3.time < T4.time)
    (si1 : s1.site = digitSite ring root src) (sl1 : s1.lane = lane)
    (si2 : s2.site = digitSite ring root src) (sl2 : s2.lane = lane)
    (si3 : s3.site = digitSite ring root src) (sl3 : s3.lane = lane)
    (si4 : s4.site = digitSite ring root src) (sl4 : s4.lane = lane)
    (hd1 : ∀ (L : DigitCarryGhost (compileAdvice (ceilLogTwo n)) n)
      (v : DigitUse (compileAdvice (ceilLogTwo n)) n), T1.ledger = some L →
      L.uses.head? = some v → v.operand = some (.sampled s1))
    (hd2 : ∀ (L : DigitCarryGhost (compileAdvice (ceilLogTwo n)) n)
      (v : DigitUse (compileAdvice (ceilLogTwo n)) n), T2.ledger = some L →
      L.uses.head? = some v → v.operand = some (.sampled s2))
    (hd3 : ∀ (L : DigitCarryGhost (compileAdvice (ceilLogTwo n)) n)
      (v : DigitUse (compileAdvice (ceilLogTwo n)) n), T3.ledger = some L →
      L.uses.head? = some v → v.operand = some (.sampled s3))
    (hd4 : ∀ (L : DigitCarryGhost (compileAdvice (ceilLogTwo n)) n)
      (v : DigitUse (compileAdvice (ceilLogTwo n)) n), T4.ledger = some L →
      L.uses.head? = some v → v.operand = some (.sampled s4)) :
    T1.time - 1 < s4.time := by
  have hs12 := tailLt ref hn root lane src R hR hsrc hend q0 hq0 hi0 W hRd 0 0 T1 T2 s1 s2 h1 h2 hlt12
    hd1 hd2
  have hs23 := tailLt ref hn root lane src R hR hsrc hend q0 hq0 hi0 W hRd 0 0 T2 T3 s2 s3 h2 h3 hlt23
    hd2 hd3
  have hs34 := tailLt ref hn root lane src R hR hsrc hend q0 hq0 hi0 W hRd 0 0 T3 T4 s3 s4 h3 h4 hlt34
    hd3 hd4
  obtain ⟨t, e1, he1, ht1, -, hlive, L, v, hL, hi, hu, hop⟩ :=
    completionBar ref hn root lane src R hR hsrc hend q0 hq0 hi0 hc0 W hRd 0 T1 h1 s1 hd1
  have htlen : t < W.length := getLt he1
  obtain ⟨-, -, ⟨-, -, hinv⟩, -, -⟩ := laneRunAt ref hn root lane src R hR hsrc hend q0 hq0 hi0 W t
  have hat : BarPrefix ref root lane src R q0 W t s1 (2 * R - 1) :=
    Or.inr (Or.inr (Or.inr ⟨by omega, by omega, hlive, L, v, hL, hi, hu, hop⟩))
  obtain ⟨hsh, -, -⟩ := hinv s1 si1 sl1 _ hat
  obtain ⟨p, hp⟩ := tailAtPositions hR hsh hlive L v hL hu hop
  rcases Nat.lt_or_ge t s4.time with hgt | hle
  · omega
  exfalso
  have later : ∀ (Tj : DigitTerminal (compileAdvice (ceilLogTwo n)) n) (sj : DigitStamp n),
      DigitCompletion ring (W.foldl (widthDigitAuditNext ref.toWidthDigitReference) q0).2 root src
        (src + R) lane 0 Tj → T1.time < Tj.time → s1.time < sj.time → sj.time ≤ t →
      sj.site = digitSite ring root src → sj.lane = lane →
      (∀ (L : DigitCarryGhost (compileAdvice (ceilLogTwo n)) n)
        (v : DigitUse (compileAdvice (ceilLogTwo n)) n), Tj.ledger = some L →
        L.uses.head? = some v → v.operand = some (.sampled sj)) →
      ∃ q, (q = 0 ∨ q = p) ∧ (laneCells ring root lane src
        (wRunAt ref.toWidthDigitReference q0 W t).2.current q).out.atom = some (.sampled sj) := by
    intro Tj sj hj hlt hage hle' hsi hsl hdj
    obtain ⟨tj, ej, hej, htj, -, hlivej, Lj, vj, hLj, hij, huj, hopj⟩ :=
      completionBar ref hn root lane src R hR hsrc hend q0 hq0 hi0 hc0 W hRd 0 Tj hj sj hdj
    have hjlen : tj < W.length := getLt hej
    have hatj : BarPrefix ref root lane src R q0 W tj sj (2 * R - 1) :=
      Or.inr (Or.inr (Or.inr ⟨by omega, by omega, hlivej, Lj, vj, hLj, hij, huj, hopj⟩))
    have htj' : tj = t + (tj - t) := by omega
    rw [htj'] at hatj
    obtain ⟨q, hq⟩ := barBack ref hn root lane src R hR hsrc hend q0 hq0 hi0 hc0 W sj hsi hsl t hle'
      (tj - t) (by omega) _ hatj
    rcases hp sj q hq with he | ⟨hq1, hq2⟩
    · rw [he] at hage
      exact absurd hage (Nat.lt_irrefl _)
    · exact ⟨q, hq1, hq2⟩
  obtain ⟨q2, hq2, ha2⟩ := later T2 s2 h2 hlt12 hs12 (by omega) si2 sl2 hd2
  obtain ⟨q3, hq3, ha3⟩ := later T3 s3 h3 (by omega) (by omega) (by omega) si3 sl3 hd3
  obtain ⟨q4, hq4, ha4⟩ := later T4 s4 h4 (by omega) (by omega) (by omega) si4 sl4 hd4
  have distinct : ∀ (a b : DigitStamp n) (qa qb : Nat),
      (laneCells ring root lane src (wRunAt ref.toWidthDigitReference q0 W t).2.current
        qa).out.atom = some (.sampled a) →
      (laneCells ring root lane src (wRunAt ref.toWidthDigitReference q0 W t).2.current
        qb).out.atom = some (.sampled b) → a.time < b.time → qa ≠ qb := by
    intro a b qa qb ha hb hl he
    subst he
    have e := ha.symm.trans hb
    simp only [Option.some.injEq, DigitAtom.sampled.injEq] at e
    rw [e] at hl
    exact Nat.lt_irrefl _ hl
  have n23 := distinct s2 s3 q2 q3 ha2 ha3 hs23
  have n24 := distinct s2 s4 q2 q4 ha2 ha4 (by omega)
  have n34 := distinct s3 s4 q3 q4 ha3 ha4 hs34
  rcases hq2 with hq2 | hq2 <;> rcases hq3 with hq3 | hq3 <;> rcases hq4 with hq4 | hq4 <;> omega

include hn hR hsrc hend hq0 hi0 hc0 in
/-- **The terminal letter at the end of the word**: on a word ending with the terminal letter of a
completion, the masked lane is in the cycle class and `WinAge` of the completion's tail holds
(`L3.TermEntry.termEntryRing`).  Consumer: `writerAgedCoreOf`. -/
theorem terminalEntry (hRd : digitSpan (compileAdvice (ceilLogTwo n)) = R) (cut : Nat)
    (U : DigitTerminal (compileAdvice (ceilLogTwo n)) n)
    (hU : DigitCompletion ring (W.foldl (widthDigitAuditNext ref.toWidthDigitReference) q0).2 root src
      (src + R) lane cut U) (sigma : DigitStamp n)
    (hsi : sigma.site = digitSite ring root src) (hsl : sigma.lane = lane)
    (hh : ∀ (L : DigitCarryGhost (compileAdvice (ceilLogTwo n)) n)
      (v : DigitUse (compileAdvice (ceilLogTwo n)) n), U.ledger = some L →
      L.uses.head? = some v → v.operand = some (.sampled sigma))
    (hUc : U.time = (W.foldl (widthDigitAuditNext ref.toWidthDigitReference) q0).2.clock) :
    (∃ lam : Nat → Nat, CohortCycIn R 0 (cohortProj ring root lane src R
      (piD (ref.phys (W.foldl (widthDigitAuditNext ref.toWidthDigitReference) q0).1))) (lam, 0)
        (2 * R + 1)) ∧
    WinAge ring root lane src R sigma.time (cohortProj ring root lane src R
      (piD (ref.phys (W.foldl (widthDigitAuditNext ref.toWidthDigitReference) q0).1)))
      (W.foldl (widthDigitAuditNext ref.toWidthDigitReference) q0).2 := by
  obtain ⟨t, e, he, ht, heS, hlive, L, v, hL, hi, hu, hop⟩ :=
    completionBar ref hn root lane src R hR hsrc hend q0 hq0 hi0 hc0 W hRd cut U hU sigma hh
  have htlen : t < W.length := getLt he
  have hfin := wClock ref q0 hc0 W W.length (Nat.le_refl _)
  rw [wRunAtLen ref.toWidthDigitReference W q0 W.length (Nat.le_refl _)] at hfin
  have htl : t + 1 = W.length := by omega
  have hend' : W.foldl (widthDigitAuditNext ref.toWidthDigitReference) q0 =
      widthDigitAuditNext ref.toWidthDigitReference (wRunAt ref.toWidthDigitReference q0 W t) e := by
    rw [← wRunAtLen ref.toWidthDigitReference W q0 (t + 1) (by omega)]
    exact wRunAtSucc ref.toWidthDigitReference W q0 t e he
  rw [hend']
  subst heS
  obtain ⟨⟨hl0, -, -, -, hg⟩, -⟩ := wInvAt ref hn root lane src R hR hsrc hend q0 hq0 W t
  obtain ⟨-, -, hbar, -, -⟩ := laneRunAt ref hn root lane src R hR hsrc hend q0 hq0 hi0 W t
  have hlive' : (cohortProj ring root lane src R
      (piD (ref.phys (wRunAt ref.toWidthDigitReference q0 W t).1))).live (2 * R - 1) = true := hlive
  generalize wRunAt ref.toWidthDigitReference q0 W t = y at hl0 hg hbar hlive' hL ⊢
  obtain ⟨hL0, hb0, hbR, hb2R, hbF⟩ := hl0
  obtain ⟨heq, hroot, hbX, hbY⟩ := widthLeadEdge ref.toWidthDigitReference ref.singletonFixed
    hn root y.1 hL0 (digitSite ring root (src + (2 * R - 1)))
  obtain ⟨-, hg'⟩ := widthGhostCorrDistinctStep ref.toWidthDigitReference ref.singletonFixed
    hn root lane src R hR hsrc hend (InheritedOk lane) y ⟨hL0, hb0, hbR, hb2R, hbF⟩ hg
    (digitSite ring root (src + (2 * R - 1)))
  have hg2 : GhostCorrDistinct ring root lane src R (InheritedOk lane)
      (phiD ring (piD (ref.phys y.1)) (digitSite ring root (src + (2 * R - 1))))
      (digitAuditStep ring (piD (ref.phys y.1)) y.2 (digitSite ring root (src + (2 * R - 1)))) := by
    have h' : GhostCorrDistinct ring root lane src R (InheritedOk lane)
        (piD (ref.phys (ref.next y.1 (digitSite ring root (src + (2 * R - 1))))))
        (digitAuditStep ring (piD (ref.phys y.1)) y.2 (digitSite ring root (src + (2 * R - 1)))) := hg'
    rw [heq] at h'
    exact h'
  obtain ⟨hcyc, hage⟩ := termEntryRing ring (by omega) root (piD (ref.phys y.1)) _ src hR hsrc hend
    hroot hb0 hbR hb2R hbF lane (InheritedOk lane) y.2 hbX hbY hg hg2 hbar sigma hsi hsl hlive' L v
    hL hi hu hop
  refine ⟨?_, ?_⟩
  · show ∃ lam : Nat → Nat, CohortCycIn R 0 (cohortProj ring root lane src R
      (piD (ref.phys (ref.next y.1 (digitSite ring root (src + (2 * R - 1))))))) (lam, 0) (2 * R + 1)
    rw [heq]
    exact hcyc
  · show WinAge ring root lane src R sigma.time (cohortProj ring root lane src R
      (piD (ref.phys (ref.next y.1 (digitSite ring root (src + (2 * R - 1)))))))
      (digitAuditStep ring (piD (ref.phys y.1)) y.2 (digitSite ring root (src + (2 * R - 1))))
    rw [heq]
    exact hage

end Run

/-! ### The core -/

section Core

variable {n : Nat} {ring : DirectedRing n}

/-- **`L3.WriterCurrent.WriterAgedCore` on every boundary reference.**  The tail of the
fourth completion after `after` is stamped after the first of them ends, so after `after`
(`fourthTailLate`); the fifth's tail is later still (`tailLt`), and its terminal letter gives
`WinAge` of that tail (`terminalEntry`).  Consumer: `L3.WriterCurrent.writersCurrentOfAgedCore`,
`L3.WriterCurrent.writerEntryCoreOfAgedCore`. -/
theorem writerAgedCoreOf (ref : WidthBoundaryReference ring) (hn : 5 ≤ n)
    :
    L3.WriterCurrent.WriterAgedCore ref.toWidthDigitReference := by
  intro root start u source after T hst hs hpair hT hTc
  obtain ⟨root0, hs0, hL⟩ := widthCleanBoundaryRoot ref start hst
  have hr : root = root0 :=
    (ref.singletonFixed root0 start hs0).2.1 root (ref.singletonFixed root start hs).1
  subst hr
  obtain ⟨hsrc, hend, hlay⟩ := pairLayoutStart ref hn root start hL source hpair
  have hR : 2 ≤ digitSpan (compileAdvice (ceilLogTwo n)) := valueSpanTwo hn
  have hq0 : WidthRunInv ring ref root DigitLane.writer source
      (digitSpan (compileAdvice (ceilLogTwo n)))
      (start, digitAuditInitial (piD (ref.phys start))) :=
    ⟨widthPairInvInitial ring ref hn root DigitLane.writer _ _ start hlay, hpair⟩
  obtain ⟨t1, t2, t3, t4, h1, h2, h3, h4, h5⟩ := hT
  have tailOf : ∀ N : DigitTerminal (compileAdvice (ceilLogTwo n)) n,
      DigitCompletion ring
        (u.foldl (widthDigitAuditNext ref.toWidthDigitReference)
          (start, digitAuditInitial (piD (ref.phys start)))).2 root source
        (source + digitSpan (compileAdvice (ceilLogTwo n))) DigitLane.writer 0 N →
      ∃ s : DigitStamp n, s.site = digitSite ring root source ∧ s.lane = DigitLane.writer ∧
        ∀ (L : DigitCarryGhost (compileAdvice (ceilLogTwo n)) n)
          (v : DigitUse (compileAdvice (ceilLogTwo n)) n), N.ledger = some L →
          L.uses.head? = some v → v.operand = some (.sampled s) := by
    intro N hN
    obtain ⟨s, -, h2', h3', -, -, L, v, hL', hv, hop, hall⟩ :=
      completionTail ring _ root source _ DigitLane.writer 0 N hN
    exact ⟨s.id, h2', h3', hall⟩
  obtain ⟨s1, si1, sl1, hd1⟩ := tailOf t1 h1.1
  obtain ⟨s2, si2, sl2, hd2⟩ := tailOf t2 h2.1
  obtain ⟨s3, si3, sl3, hd3⟩ := tailOf t3 h3.1
  obtain ⟨s4, si4, sl4, hd4⟩ := tailOf t4 h4.1
  obtain ⟨s5, si5, sl5, hd5⟩ := tailOf T h5.1
  have a1 := h1.2.1
  have hlate := fourthTailLate ref hn root DigitLane.writer source _ hR hsrc hend _ hq0 rfl rfl u rfl
    t1 t2 t3 t4 s1 s2 s3 s4 h1.1 h2.1 h3.1 h4.1 h2.2.1 h3.2.1 h4.2.1 si1 sl1 si2 sl2 si3 sl3 si4 sl4
    hd1 hd2 hd3 hd4
  have h45 := tailLt ref hn root DigitLane.writer source _ hR hsrc hend _ hq0 rfl u rfl 0 0 t4 T s4 s5
    h4.1 h5.1 h5.2.1 hd4 hd5
  have hage : after < s5.time := by omega
  obtain ⟨-, hwin⟩ := terminalEntry ref hn root DigitLane.writer source _ hR hsrc hend _ hq0 rfl rfl u
    rfl 0 T h5.1 s5 si5 sl5 hd5 hTc
  have hwin' := winAgeMono (Nat.le_of_lt hage) hwin
  obtain ⟨-, hA1, hA2⟩ := hwin'
  refine ⟨hA1, fun q hq1 hq2 L hL' use huse => ?_⟩
  obtain ⟨-, -, hall⟩ := hA2 q hq1 hq2 L hL'
  obtain ⟨-, id, hop, ha, -⟩ := hall use huse
  exact ⟨id, hop, ha⟩

/-- `L3.WriterCurrent.WriterEntryCore` on every boundary reference.  Consumer:
`L3.WriterCurrent.writerEntryOfCore`. -/
theorem writerEntryCoreOf (ref : WidthBoundaryReference ring) (hn : 5 ≤ n)
    :
    L3.WriterCurrent.WriterEntryCore ref.toWidthDigitReference :=
  L3.WriterCurrent.writerEntryCoreOfAgedCore ref hn (writerAgedCoreOf ref hn)

/-- **`DigitWritersCurrent` at the writer comparison cut, at every boundary reference**:
`L3.WriterCurrent.writersCurrentOfAgedCore` with the core proved.  Consumer: the writer comparison
certificate (the entrance of the quiet class, R10c-qdigit-notes section 5). -/
theorem writersCurrentOfReceipts (ref : WidthBoundaryReference ring) (hn : 5 ≤ n)
    (start : ref.State) (word : List (Fin n)) (root : Fin n) (z : ref.State)
    (audit : DigitAudit (compileAdvice (ceilLogTwo n)) n) (retired restart : Nat)
    (hst : ref.start start)
    (hfold : word.foldl (widthDigitAuditNext ref.toWidthDigitReference)
      (start, digitAuditInitial (piD (ref.phys start))) = (z, audit))
    (hW : WFixedRoot ring root (piW (ref.phys z)))
    (hrec : L3.WriterValueCuts.WidthWriterValueReceipts ring root audit retired restart) :
    ∃ (structural first baseCut last : Nat) (cuts : List (Nat × Nat)),
      DigitValueChain ring root audit structural first baseCut last restart cuts ∧
      DigitWritersCurrent ring root audit (piD (ref.phys z)) audit.current structural audit.clock
        cuts :=
  L3.WriterCurrent.writersCurrentOfAgedCore ref hn (writerAgedCoreOf ref hn) start word root
    z audit retired restart hst hfold hW hrec

end Core

end L3.WriterAged

#print axioms L3.WriterAged.tailAtPositions
#print axioms L3.WriterAged.barBackStep
#print axioms L3.WriterAged.barBack
#print axioms L3.WriterAged.completionBar
#print axioms L3.WriterAged.tailLt
#print axioms L3.WriterAged.fourthTailLate
#print axioms L3.WriterAged.terminalEntry
#print axioms L3.WriterAged.writerAgedCoreOf
#print axioms L3.WriterAged.writerEntryCoreOf
#print axioms L3.WriterAged.writersCurrentOfReceipts
