import Leader.L3.Width.DigitQuietEntryPairScan
import Leader.L3.Width.DigitWriterAged

/-!
# The pin bundle of one pair and `PairQuiet`

`PairBundle`: the pin bundle of one lane of a pair on the coupled chain with its cycle ghost, with
`WinAge … after`, and with the old cohort described: in cycle `0` the old cohort is gone, and from
cycle `1` on the ledgers of the target cells read the operands of a pinned closed window
(`L3.WidthWave.WidthRunInv`).  It is closed under every letter (`pairBundleStep`), and it starts at
a terminal state of a completion (`pairBundleStart`, with the ghost relabelled to cycle `0`).

`pairQuietOfBundle`: a state in the bundle whose recorded samples after `after` read the current
source digits (`SamplesCurrent`) passes the pipeline scan, given the carry bits of the lane
(`CarryBits`).  `carryBitsWriter` gives them on the writer lane.

Consumer: `L3.QuietEntryPair.writerPairQuiet` (WidthDigitQuietEntryPairWriter).

Paper: research/lean-l3/ledgers/R10c-qdigit-notes.md section 7.3 items 2 and 3.
-/

namespace L3.QuietEntryPair

open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree
open L3
open L3.DigitQuiet
open L3.RenewalReferenceClock
open L3.WidthDigit
open L3.WidthWave
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
open L3.CurrentWin
open L3.CloseCurrent
open L3.TermEntry

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-! ### The old cohort is gone in the class of a terminal state -/

section Old

variable {R j o : Nat} {s : CohortLane} {lam : Nat → Nat} {g : (Nat → Nat) × Nat}

/-- A target cell of a lane with no old cohort holds no unread or live token.  Consumer: `oldGone`,
`carryBitsWriter`. -/
theorem noOtherOfGone (hA : CohortCycIn R j s (lam, j) (2 * R + 1)) {q : Nat} (h1 : R ≤ q)
    (h2 : q < 2 * R) : cohortTok R s q ≠ .other := by
  obtain ⟨-, ⟨-, hch0⟩, -, -⟩ := hA
  have hch : CohortChosen R s lam (cohortBottom R (2 * R + 1)) := hch0
  have hR := hch.two
  rw [cohortBottomCarry (by omega), show 2 * R + 1 - 1 = 2 * R by omega] at hch
  intro hot
  by_cases hc : ∃ i, i < R ∧ cohortPos R lam i = q
  · obtain ⟨i, hi, hp⟩ := hc
    rcases hch.pkt i hi with h | ⟨h, -⟩ | ⟨-, hl⟩
    · rw [hp, hot] at h
      cases h
    · rw [hp, hot] at h
      cases h
    · unfold cohortPos at hp
      omega
  · have := targetGap hch h1 h2 (fun i hi he => hc ⟨i, hi, he⟩)
    rw [hot] at this
    cases this

/-- **The old cohort is gone**: the class of a terminal state (`L3.WriterAged.terminalEntry`)
excludes every old phase.  Consumer: `pairBundleStart`. -/
theorem oldGone (hA : CohortCycIn R 0 s (lam, 0) (2 * R + 1)) (hB : CohortCycIn R j s g o) :
    o = 2 * R + 1 := by
  obtain ⟨-, ⟨hold, hch'⟩, -, -⟩ := hB
  have hle := cohortOldLe hold
  have hother := fun {q : Nat} (h1 : R ≤ q) (h2 : q < 2 * R) => noOtherOfGone hA h1 h2
  obtain ⟨-, ⟨-, hch0⟩, -, hnd0⟩ := hA
  have hch : CohortChosen R s lam (cohortBottom R (2 * R + 1)) := hch0
  have hnd : ¬ gridDone R R lam := hnd0
  have hR := hch.two
  rw [cohortBottomCarry (by omega), show 2 * R + 1 - 1 = 2 * R by omega] at hch
  have htail : lam (R - 1) < R := by
    refine Nat.lt_of_not_ge fun hge => hnd fun i hi => ?_
    have := chosenChain hch i (R - 1) (by omega) (by omega)
    omega
  have hposl : cohortPos R lam (R - 1) = lam (R - 1) := by
    unfold cohortPos
    omega
  by_cases h1 : o ≤ R
  · exfalso
    rw [cohortOldSettle h1] at hold
    have ha := hold.1 (R - 1) (by omega)
    rw [show 2 * R - 1 - (R - 1) = R by omega] at ha
    have htl : cohortTail R (R - 1) = true := by
      unfold cohortTail
      simp
      omega
    rw [htl] at ha
    by_cases hc : ∃ i, i < R ∧ cohortPos R lam i = R
    · obtain ⟨i, hi, hp⟩ := hc
      have hit : cohortTail R i = true → i = R - 1 := by
        unfold cohortTail
        simp
        omega
      have hne : i ≠ R - 1 := by
        intro he
        rw [he, hposl] at hp
        omega
      rcases hch.pkt i hi with h | ⟨h, -⟩ | ⟨-, hl⟩
      · rw [hp] at h
        rcases ha with ha | ha <;> rw [h] at ha <;>
          first
            | (injection ha with ha'; exact hne (hit ha'))
            | cases ha
      · rw [hp] at h
        rcases ha with ha | ha <;> rw [h] at ha <;>
          first
            | (injection ha with ha'; exact hne (hit ha'))
            | cases ha
      · unfold cohortPos at hp
        omega
    · have hg := targetGap hch (Nat.le_refl R) (by omega) (fun i hi he => hc ⟨i, hi, he⟩)
      rcases ha with ha | ha <;> rw [hg] at ha <;> cases ha
  · by_cases h2 : o ≤ 2 * R
    · exfalso
      rw [cohortOldCarry (by omega) h2] at hold
      unfold CohortCarry at hold
      rw [if_neg (by omega), if_pos (by omega)] at hold
      refine hother (q := R + (o - R) - 1) (by omega) (by omega) ?_
      rw [cohortTokTgt s (by omega), hold.1]
      rfl
    · omega

end Old

/-! ### The bundle -/

section Bundle

variable {n : Nat} {ring : DirectedRing n} (ref : WidthDigitReference ring)
  (hfix : ∀ (root : Fin n) (z : ref.State), ref.singleton root z →
    WFixedRoot ring root (piW (ref.phys z))) (hn : 5 ≤ n)
  (root : Fin n) (lane : DigitLane) (src R : Nat) (hR : 2 ≤ R) (hsrc : 2 ≤ src)
  (hend : src + 2 * R < n)

/-- **The pin bundle of one lane of a pair at `after`**, on the coupled chain.  Consumer:
`pairBundleStep`, `scanValsOfBundle`, `carryBitsWriter`. -/
def PairBundle (after born : Nat)
    (w : (ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n) × ((Nat → Nat) × Nat)) : Prop :=
  WidthWinInvD ref root lane src R (InheritedOk lane) w.1 w.2 ∧
  WidthUseReach ref root lane src R w ∧
  WinAge ring root lane src R after (cohortProj ring root lane src R (piD (ref.phys w.1.1))) w.1.2 ∧
  after ≤ w.1.2.clock ∧ born ≤ w.1.2.clock ∧
  (w.2.2 = 0 →
    CohortCycIn R 0 (cohortProj ring root lane src R (piD (ref.phys w.1.1))) w.2 (2 * R + 1)) ∧
  (1 ≤ w.2.2 → ∃ (chi : Nat → DigitExport (compileAdvice (ceilLogTwo n)) n) (t1 : Nat), born ≤ t1 ∧
    L3.ValueLedger.SitePin ring root lane src R w.1.2 chi ∧
    L3.WidthWave.WidthRunInv ref root lane src R t1 chi w)

include hfix hn hR hsrc hend in
/-- **The bundle is carried by every letter.**  Consumer: `pairBundleRun`. -/
theorem pairBundleStep (after born : Nat)
    (w : (ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n) × ((Nat → Nat) × Nat))
    (e : Fin n) (h : PairBundle ref root lane src R after born w) :
    PairBundle ref root lane src R after born (widthWindowNext ref root lane src R w e) := by
  obtain ⟨hw, hu, hage, hcut, hborn, h0, h1⟩ := h
  have hw' := (widthWinInvDStep ref hfix hn root lane src R hR hsrc hend (InheritedOk lane) w.1 w.2
    hw e).1
  have hu' := widthUseReachStep ref hfix hn root lane src R hR hsrc hend (InheritedOk lane) w e hw hu
  have hw0 := hw
  obtain ⟨hlay, hfo, hgc, ⟨o, hcyc⟩, -⟩ := hw
  have hproj := (widthCohortStep ref hfix hn root lane src R hR hsrc hend w.1.1 hlay e).2
  have hcnt := widthCountStep ref root lane src R w e
  refine ⟨hw', hu', ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨hL, hb0, hbR, hb2R, hbF⟩ := hlay
    obtain ⟨heq, hroot, hbX, hbY⟩ := widthLeadEdge ref hfix hn root w.1.1 hL e
    show WinAge ring root lane src R after
      (cohortProj ring root lane src R (piD (ref.phys (ref.next w.1.1 e))))
      (digitAuditStep ring (piD (ref.phys w.1.1)) w.1.2 e)
    rw [heq]
    obtain ⟨j, hj, rfl⟩ := bankRepairDigitSiteSurj ring root e
    exact winAgeStep ring (by omega) root (piD (ref.phys w.1.1)) R src hR hsrc hend hroot hb0 hbR
      hb2R hbF lane (InheritedOk lane) (inheritedNoSample lane) w.1.2 j hj hbX hbY after hcut hgc
      hcyc hage
  · show after ≤ w.1.2.clock + 1
    omega
  · show born ≤ w.1.2.clock + 1
    omega
  · intro h2
    have hw2 : w.2.2 = 0 := by omega
    have hc0 := h0 hw2
    show CohortCycIn R 0 (cohortProj ring root lane src R (piD (ref.phys (ref.next w.1.1 e))))
      (widthWindowNext ref root lane src R w e).2 (2 * R + 1)
    rw [hproj]
    rcases cohortCycStep hc0 (cohortEdgeOf root src R e) with ⟨o', ho, h', -⟩ | h'
    · have := cohortOldLe h'.2.1.1
      have ho' : o' = 2 * R + 1 := by omega
      rw [ho'] at h'
      exact h'
    · exfalso
      have : (widthWindowNext ref root lane src R w e).2.2 = 0 + 1 := h'.1
      omega
  · intro h2
    by_cases hsame : (widthWindowNext ref root lane src R w e).2.2 = w.2.2
    · obtain ⟨chi, t1, hb1, hp, hr⟩ := h1 (by omega)
      refine ⟨chi, t1, hb1, fun i hi => ?_,
        widthRunInvStep ref hfix hn root lane src R hR hsrc hend (InheritedOk lane) t1 chi w e hw0
          hsame hr⟩
      obtain ⟨s, h3, h4, h5, h6, h7⟩ := hp i hi
      exact ⟨s, h3, recordedSampleStep ring _ _ e s h4, h5, h6, h7⟩
    · have hc1 : (widthWindowNext ref root lane src R w e).2.2 = w.2.2 + 1 := by omega
      have hjc : WidthJustClosed ref root lane src R (InheritedOk lane)
          (widthWindowNext ref root lane src R w e) := ⟨w, e, hw0, rfl, hc1⟩
      obtain ⟨-, chi', t0, hcw, -, -, hlast⟩ := hu'
      obtain ⟨chi, ⟨-, hpin, -⟩, hold⟩ := hlast h2
      refine ⟨chi, _, ?_, hpin,
        widthRunInvStart ref hfix hn root lane src R hR hsrc hend (InheritedOk lane) _ hjc chi hold⟩
      show born ≤ w.1.2.clock + 1
      omega

include hfix hn hR hsrc hend in
/-- The bundle along a word.  Consumer: `L3.QuietEntryPair.writerPairQuiet`. -/
theorem pairBundleRun (after born : Nat) (word : List (Fin n)) :
    ∀ w : (ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n) × ((Nat → Nat) × Nat),
      PairBundle ref root lane src R after born w →
      PairBundle ref root lane src R after born
        (word.foldl (widthWindowNext ref root lane src R) w) := by
  induction word with
  | nil => intro w h; exact h
  | cons e rest ih =>
    intro w h
    exact ih _ (pairBundleStep ref hfix hn root lane src R hR hsrc hend after born w e h)

/-- **The bundle at a terminal state**: a pin with any ghost, the class and the age of the terminal
state (`L3.WriterAged.terminalEntry`).  The ghost is relabelled to cycle `0`.  Consumer:
`L3.QuietEntryPair.writerPairQuiet`. -/
theorem pairBundleStart (after : Nat)
    (y : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n) (g : (Nat → Nat) × Nat)
    (hw : WidthWinInvD ref root lane src R (InheritedOk lane) y g)
    (hu : WidthUseReach ref root lane src R (y, g))
    (hclass : ∃ lam : Nat → Nat, CohortCycIn R 0
      (cohortProj ring root lane src R (piD (ref.phys y.1))) (lam, 0) (2 * R + 1))
    (hage : WinAge ring root lane src R after
      (cohortProj ring root lane src R (piD (ref.phys y.1))) y.2)
    (hcut : after ≤ y.2.clock) :
    PairBundle ref root lane src R after y.2.clock (y, (g.1, 0)) := by
  obtain ⟨hlay, hfo, hgc, ⟨o, hcyc⟩, chi, t0, hcw, ha⟩ := hw
  obtain ⟨lam, hA⟩ := hclass
  have ho : o = 2 * R + 1 := oldGone hA hcyc
  subst ho
  have hcyc0 : CohortCycIn R 0 (cohortProj ring root lane src R (piD (ref.phys y.1))) (g.1, 0)
      (2 * R + 1) := ⟨rfl, hcyc.2.1, hcyc.2.2.1, hcyc.2.2.2⟩
  exact ⟨⟨hlay, hfo, hgc, ⟨_, hcyc0⟩, chi, t0, hcw, ha⟩,
    widthUseReachReset ref root lane src R y g hu, hage, hcut, Nat.le_refl _, fun _ => hcyc0,
    fun h => absurd h (Nat.not_succ_le_zero 0)⟩

end Bundle

/-! ### Values -/

section Values

variable {c : Compiled} {n : Nat}

/-- **The samples read the current digits**: every recorded sample of the lane at a source cell
stamped after `after` holds the current digit of its site.  Consumer: `scanValsOfBundle`; producer:
`L3.QuietEntryPair.samplesCurrentOfStatic`. -/
def SamplesCurrent (ring : DirectedRing n) (root : Fin n) (lane : DigitLane) (src R after : Nat)
    (A : DigitAudit c n) (S : Fin n → ProjD c) : Prop :=
  ∀ s : DigitSample c n, DigitRecordedSample A s → s.id.lane = lane → after < s.id.time →
    ∀ q, q < R → s.id.site = digitSite ring root (src + q) →
      s.value = (S (digitSite ring root (src + q))).top.d

variable {ring : DirectedRing n} {root : Fin n} {lane : DigitLane} {src R after : Nat}
  {A : DigitAudit c n} {S : Fin n → ProjD c}

/-- A pinned aged atom with a value: the value is the current digit at the pin.  Consumer:
`scanValsOfBundle`, `carryBitsWriter`. -/
theorem pinnedVal (hDig : SamplesCurrent ring root lane src R after A S) {o : Nat} (ho : o < R)
    {a : DigitAtom n} (hp : SPin ring root lane src A o a) (hage : AgedAtom after a)
    {val : Fin c.topA} {T : Bool} (hsv : AtomSV A (some a) val T) :
    val = (S (digitSite ring root (src + o))).top.d := by
  obtain ⟨s', rfl, -, hl, hsite, -⟩ := hp
  obtain ⟨id, he, ht⟩ := hage
  have hid : id = s'.id := by
    simp only [DigitAtom.sampled.injEq] at he
    exact he.symm
  subst hid
  obtain ⟨s, hrec, hsid, hv, -⟩ := hsv _ rfl
  rw [← hv]
  exact hDig s hrec (by rw [hsid]; exact hl) (by rw [hsid]; exact ht) o ho (by rw [hsid]; exact hsite)

end Values

section Scan

variable {n : Nat} {ring : DirectedRing n} (ref : WidthDigitReference ring)
  (root : Fin n) (lane : DigitLane) (src R : Nat)

/-- The views of the pair project to the masked lane.  Consumer: `pairQuietOfBundle`. -/
theorem scanTieOfProj (S : Fin n → ProjD (compileAdvice (ceilLogTwo n))) :
    ScanTie R (cohortProj ring root lane src R S)
      (fun h => view ring root S lane (src + R + h)) (fun h => view ring root S lane (src + h)) := by
  refine ⟨fun k hk => ?_, fun k hk => ?_, fun k hk => ?_⟩
  · rw [projOut ring root lane src R S k hk]
    rw [(bankRepairDigitEndpointViewLane lane S _).2.1.symm]
    rfl
  · rw [projIn ring root lane src R S (R + k) (by omega) (by omega), Nat.add_assoc]
    rw [(bankRepairDigitEndpointViewLane lane S _).1.symm]
    rfl
  · rw [projLive ring root lane src R S (R + k) (by omega) (by omega), Nat.add_assoc]
    rw [(bankRepairDigitEndpointViewLane lane S _).2.2.symm]
    rfl

/-- The carry bits of the lane at a state.  Consumer: `scanValsOfBundle`; producer:
`carryBitsWriter`. -/
def CarryBits (R : Nat) (tv : Nat → DigitLaneView (compileAdvice (ceilLogTwo n)))
    (Dp : Nat → Fin (compileAdvice (ceilLogTwo n)).topA) : Prop :=
  ∀ k, k < R → (tv k).carryLive = true →
    (tv k).carryBit = carryInto Dp (k + 1) ∧ (tv k).carryError = false

/-- **The token values of the scan from the bundle.**  Consumer: `pairQuietOfBundle`. -/
theorem scanValsOfBundle (after born : Nat)
    (w : (ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n) × ((Nat → Nat) × Nat))
    (h : PairBundle ref root lane src R after born w)
    (hDig : SamplesCurrent ring root lane src R after w.1.2 (piD (ref.phys w.1.1)))
    (hC : CarryBits R (fun k => view ring root (piD (ref.phys w.1.1)) lane (src + R + k))
      (fun k => (piD (ref.phys w.1.1) (digitSite ring root (src + k))).top.d)) :
    ScanVals R w.2.1 (fun k => view ring root (piD (ref.phys w.1.1)) lane (src + R + k))
      (fun k => view ring root (piD (ref.phys w.1.1)) lane (src + k))
      (fun k => (piD (ref.phys w.1.1) (digitSite ring root (src + k))).top.d) := by
  obtain ⟨hw, hu, hage, -, -, h0, h1⟩ := h
  obtain ⟨-, -, hgc, ⟨o, hcyc⟩, -⟩ := hw
  obtain ⟨⟨⟨-, hval⟩, hCh, hY, -⟩, chi, t0, -, hci, hcur, -⟩ := hu
  obtain ⟨hvc, -, huv, -⟩ := hval
  have hT := scanTieOfProj (root := root) (lane := lane) (src := src) (R := R) (ring := ring)
    (piD (ref.phys w.1.1))
  generalize hS : piD (ref.phys w.1.1) = S at *
  have hinTok : ∀ k, k < R → ∀ val tail,
      ((view ring root S lane (src + R + k)).input = .P val tail ∨
        (view ring root S lane (src + R + k)).input = .S val tail) →
      AtomSV w.1.2 (laneCells ring root lane src w.1.2.current (R + k)).input val tail ∧
      ∃ b, (laneCells ring root lane src w.1.2.current (R + k)).input = some b := by
    intro k hk val tail hin
    have hvci := hvc.2 (R + k) (by omega) (by omega)
    have hcor := (hgc.1.2 (R + k) (by omega) (by omega)).1
    rw [hT.inp k hk] at hcor
    rw [← Nat.add_assoc] at hvci
    have hlaneIn : bankRepairDigitLaneIn lane (S (digitSite ring root (src + R + k))).top =
        (view ring root S lane (src + R + k)).input :=
      (bankRepairDigitEndpointViewLane lane S _).1.symm
    rw [hlaneIn] at hvci
    rcases hin with hin | hin
    · rw [hin] at hvci hcor
      exact ⟨hvci, optSome hcor⟩
    · rw [hin] at hvci hcor
      exact ⟨hvci, optSome hcor⟩
  have hagedIn : ∀ k, k < R → ∀ b,
      (laneCells ring root lane src w.1.2.current (R + k)).input = some b → AgedAtom after b := by
    intro k hk b hb
    refine hage.2.1 (R + k) b ?_
    unfold trackedAt
    rw [if_neg (by omega), if_pos (by omega)]
    exact hb
  have houtTok : ∀ q, q < R → ∀ val tail,
      (view ring root S lane (src + q)).out = .D val tail →
      AtomSV w.1.2 (laneCells ring root lane src w.1.2.current q).out.atom val tail ∧
      ∃ b, (laneCells ring root lane src w.1.2.current q).out.atom = some b ∧
        tracked ring root lane src R w.1.2 q = some b := by
    intro q hq val tail ho
    have hvco := hvc.1 q hq
    have hcor := hgc.1.1 q hq
    rw [hT.out q hq] at hcor
    have hlaneO : bankRepairDigitLaneOut lane (S (digitSite ring root (src + q))).top =
        (view ring root S lane (src + q)).out :=
      (bankRepairDigitEndpointViewLane lane S _).2.1.symm
    rw [hlaneO, ho] at hvco
    rw [ho] at hcor
    obtain ⟨b, hb⟩ := optSome hcor
    refine ⟨hvco, b, hb, ?_⟩
    unfold tracked trackedAt
    rw [if_pos hq]
    exact hb
  have hagedOut : ∀ q b, tracked ring root lane src R w.1.2 q = some b → AgedAtom after b :=
    fun q b hb => hage.2.1 q b hb
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro i hi k hk hp val tail hin
    obtain ⟨hsv, b, hb⟩ := hinTok k hk val tail hin
    obtain ⟨a, ha, hpin⟩ := hci i hi (by omega)
    have hcu := hcur i hi (by omega)
    rw [ha, hp] at hcu
    have hab : b = a := by
      have h2 : (laneCells ring root lane src w.1.2.current (R + k)).input = some a := hcu
      rw [hb] at h2
      exact Option.some.inj h2
    subst hab
    rw [hb] at hsv
    exact pinnedVal hDig (by omega) hpin (hagedIn k hk b hb) hsv
  · intro k hk hne val tail hin
    obtain ⟨hsv, b, hb⟩ := hinTok k hk val tail hin
    by_cases hc0 : w.2.2 = 0
    · exfalso
      have hc := h0 hc0
      obtain ⟨-, ⟨-, hch⟩, -, -⟩ := hc
      have hR := hch.two
      rw [cohortBottomCarry (by omega), show 2 * R + 1 - 1 = 2 * R by omega] at hch
      have hg := targetGap hch (show R ≤ R + k by omega) (by omega) hne
      rw [tokTarget hT hk] at hg
      cases hl : (view ring root S lane (src + R + k)).carryLive with
      | true => rw [hl] at hg; simp [cohortTokIn] at hg
      | false =>
        rw [hl] at hg
        rcases hin with hin | hin <;> rw [hin] at hg <;> simp [cohortTokIn, bankRepairDigitInShOf] at hg
    · obtain ⟨chi', t1, -, hpinA, -, hold, -, -⟩ := h1 (by omega)
      have hoa := hold (R + k) (by omega) (by omega) hne b (by exact hb)
      obtain ⟨s, h3, h4, h5, h6, h7⟩ := hpinA (2 * R - 1 - (R + k)) (by omega)
      rw [show R - 1 - (2 * R - 1 - (R + k)) = k by omega] at h6 h7
      rw [h3] at hoa
      have hbs : b = .sampled s.id := Option.some.inj hoa
      subst hbs
      rw [hb] at hsv
      exact pinnedVal hDig hk ⟨s, rfl, h4, h5, h6, h7⟩ (hagedIn k hk _ hb) hsv
  · intro i hi hp val tail ho
    obtain ⟨hsv, b, hb, htr⟩ := houtTok _ hp val tail ho
    rw [hb] at hsv
    exact pinnedVal hDig (by omega) (hCh i hi hp b htr) (hagedOut _ b htr) hsv
  · intro q hq hl val tail ho
    obtain ⟨hsv, b, hb, htr⟩ := houtTok q hq val tail ho
    rw [hb] at hsv
    exact pinnedVal hDig hq (hY q hl hq b htr) (hagedOut q b htr) hsv
  · intro k hk hl
    obtain ⟨h2, h3⟩ := hC k hk hl
    refine ⟨?_, h2, h3⟩
    have hlE := hage.1 (R + k) (by omega) (by omega) (by rw [hT.live k hk]; exact hl)
    rw [hT.inp k hk] at hlE
    cases hin : (view ring root S lane (src + R + k)).input with
    | E => rfl
    | X => rw [hin] at hlE; cases hlE
    | P val tail => rw [hin] at hlE; cases hlE
    | S val tail => rw [hin] at hlE; cases hlE

/-- **`PairQuiet` from the bundle**, on one lane.  Consumer:
`L3.QuietEntryPair.writerPairQuiet`. -/
theorem pairQuietOfBundle (after born : Nat) (hRd : digitSpan (compileAdvice (ceilLogTwo n)) = R)
    (w : (ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n) × ((Nat → Nat) × Nat))
    (h : PairBundle ref root lane src R after born w)
    (hDig : SamplesCurrent ring root lane src R after w.1.2 (piD (ref.phys w.1.1)))
    (hC : CarryBits R (fun k => view ring root (piD (ref.phys w.1.1)) lane (src + R + k))
      (fun k => (piD (ref.phys w.1.1) (digitSite ring root (src + k))).top.d)) :
    PairQuiet ring root (piD (ref.phys w.1.1)) lane src (src + digitSpan (compileAdvice (ceilLogTwo n))) := by
  subst hRd
  obtain ⟨o, hcyc⟩ := h.1.2.2.2.1
  exact scanOfCycle (scanTieOfProj (ring := ring) root lane src _ _) hcyc
    (scanValsOfBundle ref root lane src _ after born w h hDig hC)

end Scan

section Carry

variable {c : Compiled} {n : Nat}

/-- A carry chain over the uses `Dp 0, Dp 1, …` has the carry-in of the next offset.  Consumer:
`carryBitsWriter`. -/
theorem carryOfChain {cc : Bool} {us : List (DigitUse c n)} (Dp : Nat → Fin c.topA)
    (h : L3.CarryChain c.topA cc us)
    (hv : ∀ m (u : DigitUse c n), us[m]? = some u → u.value = Dp m) :
    cc = carryInto Dp us.length := by
  induction h with
  | nil => rfl
  | @snoc cc us u h hu ih =>
    have hih := ih (fun m v hm => hv m v (by
      rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp hm).1]
      exact hm))
    have hl := hv us.length u (by simp)
    rw [List.length_append, List.length_singleton, carryInto, ← hih, hl]
    by_cases he : (Dp us.length).val + 1 = c.topA <;> simp [he]

/-- The carry-in of each use of a carry chain over the uses `Dp 0, Dp 1, …`.  Consumer:
`L3.QuietEntryValues.terminalUsesOfBundle`. -/
theorem carryInOfChain {cc : Bool} {us : List (DigitUse c n)} (Dp : Nat → Fin c.topA)
    (h : L3.CarryChain c.topA cc us)
    (hv : ∀ m (u : DigitUse c n), us[m]? = some u → u.value = Dp m) :
    ∀ m (u : DigitUse c n), us[m]? = some u → u.carryIn = carryInto Dp m := by
  induction h with
  | nil => intro m u hm; simp at hm
  | @snoc cc us u h hu ih =>
    have hv' : ∀ m (v : DigitUse c n), us[m]? = some v → v.value = Dp m := fun m v hm => hv m v (by
      rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp hm).1]
      exact hm)
    intro m v hm
    rcases Nat.lt_or_ge m us.length with hlt | hge
    · rw [List.getElem?_append_left hlt] at hm
      exact ih hv' m v hm
    · have hlen := (List.getElem?_eq_some_iff.mp hm).1
      simp only [List.length_append, List.length_singleton] at hlen
      have hme : m = us.length := by omega
      subst hme
      simp at hm
      subst hm
      rw [hu]
      exact carryOfChain Dp h hv'

end Carry

section WriterCarry

variable {n : Nat} {ring : DirectedRing n} (ref : WidthDigitReference ring)
  (root : Fin n) (src R : Nat)

/-- **The values of a target ledger in the bundle**: from cycle `1` on, the ledger of a target cell
is clean with one use per cell passed, its `m`-th use has the current source digit `m` as value and
was made after `born`.  Consumer: `carryBitsWriter`,
`L3.QuietEntryValues.terminalUsesOfBundle`. -/
theorem ledgerValsOfBundle (lane : DigitLane) (after born : Nat)
    (w : (ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n) × ((Nat → Nat) × Nat))
    (h : PairBundle ref root lane src R after born w)
    (hDig : SamplesCurrent ring root lane src R after w.1.2 (piD (ref.phys w.1.1)))
    (hc1 : 1 ≤ w.2.2) (q : Nat) (hq1 : R ≤ q) (hq2 : q < 2 * R)
    (L : DigitCarryGhost (compileAdvice (ceilLogTwo n)) n)
    (hLq : caA ring root lane src w.1.2 q = some L) :
    L.inherited = none ∧ L.uses.length = q + 1 - R ∧
      ∀ m (u : DigitUse (compileAdvice (ceilLogTwo n)) n), L.uses[m]? = some u →
        u.value = (piD (ref.phys w.1.1) (digitSite ring root (src + m))).top.d ∧ born < u.time := by
  obtain ⟨-, hu, hage, -, -, -, h1⟩ := h
  obtain ⟨⟨⟨-, hval⟩, -, -, -⟩, -⟩ := hu
  obtain ⟨-, -, huv, -⟩ := hval
  obtain ⟨chi, t1, hb1, hpinA, -, -, hled, -⟩ := h1 hc1
  obtain ⟨hinh, hlen, huse⟩ := hled q hq1 hq2 L hLq
  obtain ⟨-, -, hAged⟩ := hage
  obtain ⟨-, -, hUA⟩ := hAged q hq1 hq2 L hLq
  refine ⟨hinh, hlen, fun m u hm => ?_⟩
  have hmlt : m < q + 1 - R := by
    have := (List.getElem?_eq_some_iff.mp hm).1
    omega
  obtain ⟨hop, ht⟩ := huse m u hm
  have hmem : u ∈ L.uses := List.mem_iff_getElem?.mpr ⟨m, hm⟩
  obtain ⟨s, h3, h4, h5, h6, h7⟩ := hpinA (R - 1 - m) (by omega)
  rw [show R - 1 - (R - 1 - m) = m by omega] at h6 h7
  rw [h3] at hop
  obtain ⟨-, id, hop2, hage2, -⟩ := hUA u hmem
  have hid : s.id = id := by
    rw [hop] at hop2
    simpa using hop2
  have hsv := huv.1 q hq1 hq2 L hLq u hmem
  rw [hop] at hsv
  exact ⟨pinnedVal hDig (by omega) ⟨s, rfl, h4, h5, h6, h7⟩ ⟨id, by rw [hid], hage2⟩ hsv, by omega⟩

/-- A live target cell is in cycle `1` or later: in cycle `0` the old cohort is gone.  Consumer:
`carryBitsWriter`, `L3.QuietEntryValues.terminalUsesOfBundle`. -/
theorem cycleOfLive (lane : DigitLane) (after born : Nat)
    (w : (ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n) × ((Nat → Nat) × Nat))
    (h : PairBundle ref root lane src R after born w) (q : Nat) (hq1 : R ≤ q) (hq2 : q < 2 * R)
    (hl : (cohortProj ring root lane src R (piD (ref.phys w.1.1))).live q = true) : 1 ≤ w.2.2 := by
  obtain ⟨-, -, -, -, -, h0, -⟩ := h
  refine Nat.pos_of_ne_zero fun hc0 => ?_
  have hc := h0 hc0
  have hc' : CohortCycIn R 0 (cohortProj ring root lane src R (piD (ref.phys w.1.1)))
      (w.2.1, 0) (2 * R + 1) := ⟨rfl, hc.2.1, hc.2.2.1, hc.2.2.2⟩
  refine noOtherOfGone hc' hq1 hq2 ?_
  rw [cohortTokTgt _ hq1, hl]
  rfl

/-- **The carry bits on the writer lane**: a live target carry is the old cohort's (none lives in
cycle `0`), its ledger reads the pinned operands of the closed window in order, each value is the
current source digit, and the carry chain folds them to the carry-in bit.  Consumer:
`L3.QuietEntryValues`. -/
theorem carryBitsWriter (after born : Nat)
    (w : (ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n) × ((Nat → Nat) × Nat))
    (h : PairBundle ref root DigitLane.writer src R after born w)
    (hDig : SamplesCurrent ring root DigitLane.writer src R after w.1.2 (piD (ref.phys w.1.1)))
    (hall : L3.CarryAll (piD (ref.phys w.1.1)) w.1.2.current) :
    CarryBits R (fun k => view ring root (piD (ref.phys w.1.1)) DigitLane.writer (src + R + k))
      (fun k => (piD (ref.phys w.1.1) (digitSite ring root (src + k))).top.d) := by
  intro k hk hl
  have hT := scanTieOfProj (root := root) (lane := DigitLane.writer) (src := src) (R := R)
    (ring := ring) (piD (ref.phys w.1.1))
  refine ⟨?_, rfl⟩
  have hc1 := cycleOfLive ref root src R DigitLane.writer after born w h (R + k) (by omega)
    (by omega) (by rw [hT.live k hk]; exact hl)
  have hsite : digitSite ring root (src + R + k) = digitSite ring root (src + (R + k)) := by
    rw [Nat.add_assoc]
  have hcar := hall (digitSite ring root (src + R + k))
  cases hwc : (piD (ref.phys w.1.1) (digitSite ring root (src + R + k))).top.wCarry with
  | OFF =>
    exfalso
    simp [view, digitEndpointView, digitLaneView, hwc, WCarry.isW] at hl
  | W cc =>
    rw [hwc] at hcar
    obtain ⟨L, hL, hch⟩ := hcar
    have hLq : caA ring root DigitLane.writer src w.1.2 (R + k) = some L := by
      unfold caA laneCells laneGhost
      rw [← hsite]
      exact hL
    obtain ⟨hinh, hlen, hv⟩ := ledgerValsOfBundle ref root src R DigitLane.writer after born w h hDig
      hc1 (R + k) (by omega) (by omega) L hLq
    have := carryOfChain (fun m => (piD (ref.phys w.1.1) (digitSite ring root (src + m))).top.d)
      (hch hinh) (fun m u hm => (hv m u hm).1)
    rw [hlen, show R + k + 1 - R = k + 1 by omega] at this
    simpa [view, digitEndpointView, digitLaneView, hwc, wcC] using this

end WriterCarry

end L3.QuietEntryPair

#print axioms L3.QuietEntryPair.oldGone
#print axioms L3.QuietEntryPair.pairBundleStep
#print axioms L3.QuietEntryPair.pairBundleRun
#print axioms L3.QuietEntryPair.pairBundleStart
#print axioms L3.QuietEntryPair.scanValsOfBundle
#print axioms L3.QuietEntryPair.pairQuietOfBundle
#print axioms L3.QuietEntryPair.ledgerValsOfBundle
#print axioms L3.QuietEntryPair.cycleOfLive
#print axioms L3.QuietEntryPair.carryBitsWriter
