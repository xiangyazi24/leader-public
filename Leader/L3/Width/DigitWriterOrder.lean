import Leader.L3.Width.DigitCloseOrder
import Leader.L3.Width.PacketMomentCutEntry

/-!
# The run invariants on any lane, and the strict completion tail order

`L3.CloseRank.rankRunWidth`, `L3.CloseTerm.barRunWidth` and `L3.CloseOrder.orderRunWidth` are stated
for the comparison lane, but their step lemmas are generic in the lane.  This module packages them
once for every lane and adds what the writer value chain needs beyond `CompletionTailOrder`:

* `headOnlyLast`, `headDeadAfter`: at a head terminal letter the head `s0` is at the last target
  cell only, and after the letter it is at no barrier location;
* `HeadDead`: a head of a recorded head terminal is at no barrier location, and no two head
  terminals at different times share a head;
* `LaneRun`, `laneRunInitial`, `laneRunStep`, `laneRunFold`: `TailInv` for every stamp, `AheadRun`,
  `BarRun`, `OrderRun`, `HeadDead` along every coupled word from a run-invariant start;
* `CompletionTailOrderStrict`, `completionTailOrderStrict`: **the standalone statement**: of two
  completions of a complete pair of a clean start, on any lane, with different terminal times, the
  later terminal has the strictly later tail sample.
-/

namespace L3.WriterOrder

set_option autoImplicit false

open L3
open L3.RenewalReferenceClock
open L3.WidthDigit
open L3.ValueWaveClose
open L3.CompareStage
open L3.CohortDomination
open L3.CohortSites
open L3.CohortEntry
open L3.CohortTail
open L3.PacketClass
open L3.Rearm
open L3.GhostBridge
open L3.Correspondence
open L3.CohortIdentity
open L3.CohortLedger
open L3.ValueLedger
open L3.UseRows
open L3.UseCells
open L3.UseTrack
open L3.CurrentWin
open L3.CohortWindow
open L3.CloseCurrent
open L3.CloseEntry
open L3.WidthWave
open L3.TailChain
open L3.TailAhead
open L3.TermEntry
open L3.CloseTerm
open L3.CloseRank
open L3.CloseOrder
open L3.WidthPacketMomentGroupCompletion

/-! ### On the lane cells -/

section Lane

variable {c : Compiled} {n : Nat} {R : Nat}

/-- **The head of a completing carry is at the last target cell only** (`BarInv` at location C):
behind it every tracked atom is stamped strictly after it and no target cell is live.  Consumer:
`headDeadAfter`. -/
theorem headOnlyLast (hR : 2 ≤ R) {s : CohortLane} {g : Nat → DigitLaneGhost c n}
    {s0 : DigitStamp n} {clock : Nat} (h : BarInv R s g s0 clock)
    (hlive : s.live (2 * R - 1) = true) (L : DigitCarryGhost c n) (u : DigitUse c n)
    (hL : (g (2 * R - 1)).carry = some L) (hi : L.inherited = none)
    (hu : L.uses.head? = some u) (hop : u.operand = some (.sampled s0)) :
    ∀ q, BarAt R s g s0 q → q = 2 * R - 1 := by
  have hat : BarAt R s g s0 (2 * R - 1) :=
    Or.inr (Or.inr (Or.inr ⟨by omega, by omega, hlive, L, u, hL, hi, hu, hop⟩))
  obtain ⟨hsh, -, hage⟩ := h _ hat
  have hold : ∀ p, p < 2 * R - 1 → trackedAt R g p ≠ some (.sampled s0) := by
    intro p hp ht
    obtain ⟨id, hid, hlt'⟩ := hage p _ hp ht
    cases hid
    exact Nat.lt_irrefl _ hlt'
  intro q hq
  by_cases hq' : q = 2 * R - 1
  · exact hq'
  · exfalso
    rcases hq with ⟨h1, -, h3⟩ | ⟨h1, h2, h3, -, h5⟩ | ⟨-, -, h3⟩ |
        ⟨h1, h2, h3, L', u', h4, -, h6, h7⟩
    · apply hold q (by omega)
      unfold trackedAt
      rw [if_pos h1]
      exact h3
    · apply hold q (by omega)
      unfold trackedAt
      rw [if_neg (by omega), if_pos h2]
      exact h5
    · apply hold R (by omega)
      unfold trackedAt
      rw [if_neg (by omega), if_pos (by omega)]
      exact h3
    · have hd := (barTgt hsh (by omega) (by omega) q h1 (by omega)).1
      rw [hd] at h3
      cases h3

/-- **After the head terminal letter the head is at no barrier location**: a location after the
letter comes from one before it, which is the last target cell, whose carry the letter clears.
Consumer: `headDeadStep`. -/
theorem headDeadAfter (hR : 2 ≤ R) {stamp s0 : DigitStamp n} {s : CohortLane}
    {g g' : Nat → DigitLaneGhost c n} {Ok : Bool → DigitAtom n → Prop} {clock : Nat}
    (hrows : LaneRows R stamp s g g' (some (2 * R - 1))) (hcorr : PureCorr R Ok s g)
    (hne : CleanNe R g) (hT : ∀ T, Ok T (.sampled s0) → T = true) (hfresh : s0 ≠ stamp)
    (h : BarInv R s g s0 clock) (hlive : s.live (2 * R - 1) = true) (L : DigitCarryGhost c n)
    (u : DigitUse c n) (hL : (g (2 * R - 1)).carry = some L) (hi : L.inherited = none)
    (hu : L.uses.head? = some u) (hop : u.operand = some (.sampled s0)) :
    ∀ q, ¬ BarAt R (cohortLaneStep R s (some (2 * R - 1))) g' s0 q := by
  intro q hq
  have honly := headOnlyLast hR h hlive L u hL hi hu hop
  have hstep : cohortLaneStep R s (some (2 * R - 1)) = cohortEdge R s (2 * R - 1) := rfl
  obtain ⟨e1, e2⟩ := edgeTermRaw R (2 * R - 1) s (by omega) (by omega)
  have hT1 : (cohortEdge R s (2 * R - 1)).inp (2 * R - 1) = .E := by
    rw [e1, hlive]
    rfl
  have hT2 : (cohortEdge R s (2 * R - 1)).live (2 * R - 1) = false := by
    rw [e2, hlive]
    rfl
  rcases barAtBack hR _ hrows hcorr hne hT q hq with ⟨hss, -⟩ | hpre | ⟨h0, -, hq2, hpre, -, -⟩
  · exact hfresh hss
  · have hq1 := honly q hpre
    subst hq1
    rw [hstep] at hq
    rcases hq with ⟨h1, -, -⟩ | ⟨-, -, -, h4, -⟩ | ⟨h1, -, -⟩ | ⟨-, -, h3, -⟩
    · omega
    · rw [hT1] at h4
      cases h4
    · omega
    · rw [hT2] at h3
      cases h3
  · have hq1 := honly (q - 1) hpre
    omega

end Lane

/-! ### On the projected ring -/

section Ring

variable {c : Compiled} {n : Nat}

/-- **The head terminals' heads are dead**: the head of a recorded head terminal is at no barrier
location, and two head terminals with one head are at one time.  Consumer: `LaneRun`,
`completionTailOrderStrict`. -/
def HeadDead (ring : DirectedRing n) (root : Fin n) (lane : DigitLane) (src R : Nat)
    (S : Fin n → ProjD c) (A : DigitAudit c n) : Prop :=
  (∀ (U : DigitTerminal c n) (s0 : DigitStamp n), TermHead ring root lane src R A U s0 →
    ∀ q, ¬ BarAt R (cohortProj ring root lane src R S) (laneCells ring root lane src A.current)
      s0 q) ∧
  (∀ (U0 U : DigitTerminal c n) (s : DigitStamp n), TermHead ring root lane src R A U0 s →
    TermHead ring root lane src R A U s → U0.time < U.time → False)

/-- No terminal is recorded at the audit start.  Consumer: `laneRunInitial`. -/
theorem headDeadInitial (ring : DirectedRing n) (root : Fin n) (lane : DigitLane) (src R : Nat)
    (S : Fin n → ProjD c) : HeadDead ring root lane src R S (digitAuditInitial S) := by
  have hno : ∀ (U : DigitTerminal c n) (s0 : DigitStamp n),
      ¬ TermHead ring root lane src R (digitAuditInitial S) U s0 := by
    intro U s0 h
    obtain ⟨f, hf, -⟩ := h.1
    exact absurd hf List.not_mem_nil
  exact ⟨fun U s0 h => absurd h (hno U s0), fun U0 _ s h _ _ => absurd h (hno U0 s)⟩

/-- **Every letter keeps `HeadDead`.**  Consumer: `laneRunStep`. -/
theorem headDeadStep (ring : DirectedRing n) (hn : 2 ≤ n) (root : Fin n)
    (S : Fin n → ProjD c) (R src : Nat) (hR : 2 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n)
    (hroot : ∀ i, (S i).word.native.l = true ↔ i = root)
    (hb0 : (S (digitSite ring root src)).word.beta = true)
    (hbR : (S (digitSite ring root (src + R))).word.beta = true)
    (hb2R : (S (digitSite ring root (src + 2 * R))).word.beta = true)
    (hbF : ∀ k, 0 < k → k < 2 * R → k ≠ R →
      (S (digitSite ring root (src + k))).word.beta = false)
    (lane : DigitLane) (Base : Bool → DigitAtom n → Prop)
    (hnb : ∀ T (id : DigitStamp n), ¬ Base T (.sampled id)) (A : DigitAudit c n)
    (j : Nat) (hj : j < n)
    (hbX : (pairW (S (digitSite ring root j)).word
      (S (digitSite ring root (j + 1))).word).1.beta = (S (digitSite ring root j)).word.beta)
    (hbY : (pairW (S (digitSite ring root j)).word
      (S (digitSite ring root (j + 1))).word).2.beta =
        (S (digitSite ring root (j + 1))).word.beta)
    (hgc : GhostCorrDistinct ring root lane src R Base S A) (hfo : AuditFrameOrder A)
    (hbar : BarRun ring root lane src R S A) (ho : OrderRun ring root lane src R S A)
    (h : HeadDead ring root lane src R S A) :
    HeadDead ring root lane src R (phiD ring S (digitSite ring root j))
      (digitAuditStep ring S A (digitSite ring root j)) := by
  obtain ⟨hne, hbt, hinv⟩ := hbar
  obtain ⟨hD1, hD2⟩ := h
  have hrows := laneRowsRing ring hn root S R src hR hsrc hend hroot hb0 hbR hb2R hbF lane A j
    hj hbX hbY hgc.1
  have hproj := cohortProjStep ring hn root S R src hR hsrc hend hroot hb0 hbR hb2R hbF lane j
    hj hbX hbY
  have hTb : ∀ sigma : DigitStamp n, sigma.site = digitSite ring root src → sigma.lane = lane →
      ∀ T, GhostOk ring root lane src R Base A T (.sampled sigma) → T = true := by
    intro sigma hsi hl T hok
    rcases hok with hb | ⟨smp, hid, hrec, htail, -⟩
    · exact absurd hb (hnb T sigma)
    · have hsid : smp.id = sigma := by
        simp only [DigitAtom.sampled.injEq] at hid
        exact hid.symm
      rw [← htail]
      exact hbt smp hrec (by rw [hsid]; exact hsi) (by rw [hsid]; exact hl)
  have hfreshOf : ∀ sigma : DigitStamp n, sigma.time ≤ A.clock →
      sigma ≠ DigitStamp.mk (A.clock + 1) (digitSite ring root j) lane := by
    intro sigma ht he
    subst he
    exact absurd ht (Nat.not_succ_le_self _)
  -- a head terminal after the letter was recorded before it, or by the letter
  have hnew : ∀ (U : DigitTerminal c n) (s0 : DigitStamp n),
      TermHead ring root lane src R (digitAuditStep ring S A (digitSite ring root j)) U s0 →
      TermHead ring root lane src R A U s0 ∨
      (U.time = A.clock + 1 ∧ j = src + (2 * R - 1) ∧
        BarAt R (cohortProj ring root lane src R S) (laneCells ring root lane src A.current) s0
          (2 * R - 1) ∧ s0.site = digitSite ring root src ∧ s0.lane = lane ∧
        (cohortProj ring root lane src R S).live (2 * R - 1) = true ∧
        ∃ (L : DigitCarryGhost c n) (u : DigitUse c n),
          (laneCells ring root lane src A.current (2 * R - 1)).carry = some L ∧
          L.inherited = none ∧ L.uses.head? = some u ∧ u.operand = some (.sampled s0)) := by
    intro U s0 hU
    obtain ⟨hrec, hl, hsrcU, hsi0, hl0, L, u, hL, hi, hu, hop⟩ := hU
    rcases recordedTerminalStepCases ring S A _ U hrec with hold | ⟨ht, hsite, hterm⟩
    · exact Or.inl ⟨hold, hl, hsrcU, hsi0, hl0, L, u, hL, hi, hu, hop⟩
    · right
      have hjj : j = src + (2 * R - 1) :=
        bankRepairDigitSiteInj ring root hj (by omega) (by rw [← hsite, hsrcU])
      subst hjj
      rw [hl] at hterm
      unfold svcAt at hterm
      obtain ⟨hlive, hledger⟩ := termLiveD lane _ _ _ _ _ _ _ U hterm
      have hlive' : (cohortProj ring root lane src R S).live (2 * R - 1) = true := by
        rw [projLive ring root lane src R S (2 * R - 1) (by omega) (by omega)]
        exact hlive
      have hLc : (laneCells ring root lane src A.current (2 * R - 1)).carry = some L :=
        hledger.symm.trans hL
      exact ⟨ht, rfl, Or.inr (Or.inr (Or.inr ⟨by omega, by omega, hlive', L, u, hLc, hi, hu, hop⟩)),
        hsi0, hl0, hlive', L, u, hLc, hi, hu, hop⟩
  have hold : ∀ U : DigitTerminal c n, DigitRecordedTerminal A U → U.time ≤ A.clock := by
    intro U hU
    obtain ⟨f, hf, hft, -⟩ := hU
    have := (hfo.2.1 f hf).2
    omega
  refine ⟨fun U s0 hU q => ?_, fun U0 U s hU0 hU hlt => ?_⟩
  · rcases hnew U s0 hU with hpre | ⟨-, hjj, -, hsi, hl, hlive, L, u, hLc, hi, hu, hop⟩
    · have ht := (ho.1 U s0 hpre).1
      rw [hproj]
      exact deadStep hR _ hrows hgc.1 hne (hTb s0 hpre.2.2.2.1 hpre.2.2.2.2.1) (hfreshOf s0 ht)
        (hD1 U s0 hpre) q
    · subst hjj
      have hat : BarAt R (cohortProj ring root lane src R S)
          (laneCells ring root lane src A.current) s0 (2 * R - 1) :=
        Or.inr (Or.inr (Or.inr ⟨by omega, by omega, hlive, L, u, hLc, hi, hu, hop⟩))
      have ht := (hinv s0 hsi hl _ hat).2.1
      have hke := cohortEdgeOfSite ring root src R hend (2 * R - 1) (by omega)
      rw [hproj, hke]
      rw [hke] at hrows
      exact headDeadAfter hR hrows hgc.1 hne (hTb s0 hsi hl) (hfreshOf s0 ht) (hinv s0 hsi hl) hlive
        L u hLc hi hu hop q
  · rcases hnew U0 s hU0 with hpre0 | ⟨ht0, -⟩
    · rcases hnew U s hU with hpre | ⟨-, -, hat, -⟩
      · exact hD2 U0 U s hpre0 hpre hlt
      · exact hD1 U0 s hpre0 _ hat
    · rcases hnew U s hU with hpre | ⟨ht, -⟩
      · have := hold U hpre.1
        omega
      · omega

/-- **The run invariants of one pair on one lane**: `TailInv` for every stamp, `AheadRun`,
`BarRun`, `OrderRun` and `HeadDead`.  Consumer: `laneRunStep`, `completionTailOrderStrict`,
`L3.WriterCycle`. -/
def LaneRun (ring : DirectedRing n) (root : Fin n) (lane : DigitLane) (src R : Nat)
    (S : Fin n → ProjD c) (A : DigitAudit c n) : Prop :=
  (∀ sigma0 : DigitStamp n, TailInv ring root lane src R sigma0 S A) ∧
  AheadRun ring root lane src R S A ∧
  BarRun ring root lane src R S A ∧
  OrderRun ring root lane src R S A ∧
  HeadDead ring root lane src R S A

end Ring

section Width

variable {n : Nat} {ring : DirectedRing n} (ref : WidthBoundaryReference ring) (hn : 5 ≤ n)
  (root : Fin n) (lane : DigitLane) (src R : Nat) (hR : 2 ≤ R) (hsrc : 2 ≤ src)
  (hend : src + 2 * R < n)

include hR in
/-- The run invariants at the audit start.  Consumer: `completionTailOrderStrict`,
`L3.WriterCycle`. -/
theorem laneRunInitial (z : ref.State) :
    LaneRun ring root lane src R (piD (ref.phys z)) (digitAuditInitial (piD (ref.phys z))) :=
  ⟨fun sigma0 => tailInvInitial ring root lane src R _ sigma0,
    aheadRunInitial ring root lane src _ _,
    barRunInitial ring root _ _ _ hR _ _ (inheritedNoSample lane)
      (ghostCorrDistinctInitial ring root lane src R _).1,
    orderRunInitial ring root lane src R _, headDeadInitial ring root lane src R _⟩

include hn hR hsrc hend in
/-- **Every coupled letter keeps the run invariants**, on the run invariant of the pair.  Consumer:
`laneRunFold`. -/
theorem laneRunStep (x : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (hx : L3.WidthPacketMomentCutEntry.WidthRunInv ring ref root lane src R x)
    (h : LaneRun ring root lane src R (piD (ref.phys x.1)) x.2) (e : Fin n) :
    LaneRun ring root lane src R
      (piD (ref.phys (widthDigitAuditNext ref.toWidthDigitReference x e).1))
      (widthDigitAuditNext ref.toWidthDigitReference x e).2 := by
  obtain ⟨⟨-, -, -, -, hg'⟩, -⟩ := L3.WidthPacketMomentCutEntry.widthRunInvStep ring ref hn root
    lane src R hR hsrc hend x hx e
  obtain ⟨⟨hl, hfo, -, -, hg⟩, -⟩ := hx
  obtain ⟨htail, hah, hbar, hord, hdead⟩ := h
  obtain ⟨hL0, hb0, hbR, hb2R, hbF⟩ := hl
  obtain ⟨heq, hroot, hbX, hbY⟩ := widthLeadEdge ref.toWidthDigitReference ref.singletonFixed hn
    root x.1 hL0 e
  obtain ⟨j, hj, rfl⟩ := bankRepairDigitSiteSurj ring root e
  have hg2 : GhostCorrDistinct ring root lane src R (InheritedOk lane)
      (phiD ring (piD (ref.phys x.1)) (digitSite ring root j))
      (digitAuditStep ring (piD (ref.phys x.1)) x.2 (digitSite ring root j)) := by
    have h' : GhostCorrDistinct ring root lane src R (InheritedOk lane)
        (piD (ref.phys (ref.next x.1 (digitSite ring root j))))
        (digitAuditStep ring (piD (ref.phys x.1)) x.2 (digitSite ring root j)) := hg'
    rw [heq] at h'
    exact h'
  show LaneRun ring root lane src R (piD (ref.phys (ref.next x.1 (digitSite ring root j))))
    (digitAuditStep ring (piD (ref.phys x.1)) x.2 (digitSite ring root j))
  rw [heq]
  exact ⟨fun sigma0 => tailInvStep ring (by omega) root (piD (ref.phys x.1)) _ src hR hsrc
      hend hroot hb0 hbR hb2R hbF lane (InheritedOk lane) x.2 j hj hbX hbY sigma0 hfo hg
      (htail sigma0),
    aheadRunStep ring (by omega) root (piD (ref.phys x.1)) _ src hR hsrc hend hroot hb0 hbR hb2R
      hbF lane (InheritedOk lane) x.2 j hj hbX hbY hfo hg hg2 hah,
    barRunStep ring (by omega) root (piD (ref.phys x.1)) _ src hR hsrc hend hroot hb0 hbR hb2R
      hbF lane (InheritedOk lane) (inheritedNoSample lane) x.2 j hj hbX hbY hg hg2 hbar,
    orderRunStep ring (by omega) root (piD (ref.phys x.1)) _ src hR hsrc hend hroot hb0 hbR hb2R
      hbF lane (InheritedOk lane) (inheritedNoSample lane) x.2 j hj hbX hbY hg hfo hbar hord,
    headDeadStep ring (by omega) root (piD (ref.phys x.1)) _ src hR hsrc hend hroot hb0 hbR hb2R
      hbF lane (InheritedOk lane) (inheritedNoSample lane) x.2 j hj hbX hbY hg hfo hbar hord
      hdead⟩

include hn hR hsrc hend in
/-- **Along every word**: the run invariant of the pair and the run invariants.  Consumer:
`completionTailOrderStrict`, `L3.WriterCycle`. -/
theorem laneRunFold : ∀ (u : List (Fin n))
    (x : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n),
    L3.WidthPacketMomentCutEntry.WidthRunInv ring ref root lane src R x →
    LaneRun ring root lane src R (piD (ref.phys x.1)) x.2 →
    L3.WidthPacketMomentCutEntry.WidthRunInv ring ref root lane src R
      (u.foldl (widthDigitAuditNext ref.toWidthDigitReference) x) ∧
    LaneRun ring root lane src R
      (piD (ref.phys (u.foldl (widthDigitAuditNext ref.toWidthDigitReference) x).1))
      (u.foldl (widthDigitAuditNext ref.toWidthDigitReference) x).2 := by
  intro u
  induction u with
  | nil => intro x h1 h2; exact ⟨h1, h2⟩
  | cons e rest ih =>
    intro x h1 h2
    exact ih _ (L3.WidthPacketMomentCutEntry.widthRunInvStep ring ref hn root lane src R hR hsrc
      hend x h1 e) (laneRunStep ref hn root lane src R hR hsrc hend x h1 h2 e)

end Width

section Top

variable {n : Nat} {ring : DirectedRing n}

/-- **The strict completion tail order, on one lane.**  On the clean run from a start with
singleton `root`, of two completions of a complete pair of the start on `lane`, a strictly later
terminal has a strictly later tail sample (`s0`, `s`: the stamps read by the first use of each
ledger).  Consumer: `L3.WriterCycle` (the writer value chain) and the writer currentness of the
comparison-entry certificate. -/
def CompletionTailOrderStrict (ref : WidthDigitReference ring) (lane : DigitLane) : Prop :=
  ∀ (root : Fin n) (start : ref.State) (u : List (Fin n)) (source cut0 cut : Nat)
    (T0 T : DigitTerminal (compileAdvice (ceilLogTwo n)) n) (s0 s : DigitStamp n),
    ref.start start → ref.singleton root start →
    DigitCompletePair ring root (piD (ref.phys start)) source
      (source + digitSpan (compileAdvice (ceilLogTwo n))) →
    DigitCompletion ring
      (u.foldl (widthDigitAuditNext ref) (start, digitAuditInitial (piD (ref.phys start)))).2
      root source (source + digitSpan (compileAdvice (ceilLogTwo n))) lane cut0 T0 →
    DigitCompletion ring
      (u.foldl (widthDigitAuditNext ref) (start, digitAuditInitial (piD (ref.phys start)))).2
      root source (source + digitSpan (compileAdvice (ceilLogTwo n))) lane cut T →
    T0.time < T.time →
    (∀ (L : DigitCarryGhost (compileAdvice (ceilLogTwo n)) n)
      (v : DigitUse (compileAdvice (ceilLogTwo n)) n), T0.ledger = some L →
      L.uses.head? = some v → v.operand = some (.sampled s0)) →
    (∀ (L : DigitCarryGhost (compileAdvice (ceilLogTwo n)) n)
      (v : DigitUse (compileAdvice (ceilLogTwo n)) n), T.ledger = some L →
      L.uses.head? = some v → v.operand = some (.sampled s)) →
    s0.time < s.time

/-- A completion is a head terminal of its tail stamp.  Consumer: `completionTailOrderStrict`,
`L3.WriterCycle`. -/
theorem termHeadOfCompletion {c : Compiled} (ring : DirectedRing n) (A : DigitAudit c n)
    (root : Fin n) (source : Nat) (lane : DigitLane) (cut : Nat) (U : DigitTerminal c n)
    (sg : DigitStamp n) (hU : DigitCompletion ring A root source (source + digitSpan c) lane cut U)
    (hh : ∀ (L : DigitCarryGhost c n) (v : DigitUse c n), U.ledger = some L →
      L.uses.head? = some v → v.operand = some (.sampled sg)) :
    TermHead ring root lane source (digitSpan c) A U sg := by
  obtain ⟨smp, -, hsi, hl, -, -, L, v, hLU, hv, hop, -⟩ :=
    completionTail ring A root source _ lane cut U hU
  have e : smp.id = sg := by
    have e' := (hh L v hLU hv).symm.trans hop
    simp only [Option.some.injEq, DigitAtom.sampled.injEq] at e'
    exact e'.symm
  obtain ⟨-, hrec, hlane, hsrcT, -, -, -, L', -, -, -, hL', hinh, -⟩ := hU
  have hLL : L' = L := Option.some.inj (hL'.symm.trans hLU)
  subst hLL
  refine ⟨hrec, hlane, ?_, by rw [← e]; exact hsi, by rw [← e]; exact hl, L', v, hLU, hinh, hv,
    by rw [hop, e]⟩
  rw [hsrcT]
  congr 1
  omega

/-- Two border stamps with one time, site and lane are equal.  Consumer:
`completionTailOrderStrict`, `L3.WriterCycle`. -/
theorem stampEq {s0 s : DigitStamp n} (ht : s0.time = s.time) (hs : s0.site = s.site)
    (hl : s0.lane = s.lane) : s0 = s := by
  cases s0
  cases s
  simp only at ht hs hl
  subst ht
  subst hs
  subst hl
  rfl

/-- **`CompletionTailOrderStrict`** at every boundary reference, on every lane:
`OrderRun` orders the heads, and `HeadDead` excludes one head at two terminal times.  Consumer:
`L3.WriterCycle`. -/
theorem completionTailOrderStrict (ref : WidthBoundaryReference ring) (hn : 5 ≤ n)
    (lane : DigitLane) :
    CompletionTailOrderStrict ref.toWidthDigitReference lane := by
  intro root start u source cut0 cut T0 T s0 s hst hs hpair hT0 hT hlt h0 h1
  obtain ⟨root0, hs0, hL⟩ := widthCleanBoundaryRoot ref start hst
  have hr : root = root0 :=
    (ref.singletonFixed root0 start hs0).2.1 root (ref.singletonFixed root start hs).1
  subst hr
  obtain ⟨hsrc, hend, hlay⟩ := pairLayoutStart ref hn root start hL source hpair
  have hR : 2 ≤ digitSpan (compileAdvice (ceilLogTwo n)) := valueSpanTwo hn
  obtain ⟨-, -, -, -, ⟨-, hI2⟩, -, hD2⟩ := laneRunFold ref hn root lane source _ hR hsrc hend u
    (start, digitAuditInitial (piD (ref.phys start)))
    ⟨widthPairInvInitial ring ref hn root lane source _ start hlay, hpair⟩
    (laneRunInitial ref root lane source _ hR start)
  have hh0 := termHeadOfCompletion ring _ root source lane cut0 T0 s0 hT0 h0
  have hh1 := termHeadOfCompletion ring _ root source lane cut T s hT h1
  rcases Nat.lt_or_ge s0.time s.time with hl | hge
  · exact hl
  · exfalso
    have hle := hI2 T0 s0 T s hh0 hh1 hlt
    have he : s0 = s := stampEq (by omega) (by rw [hh0.2.2.2.1, hh1.2.2.2.1])
      (by rw [hh0.2.2.2.2.1, hh1.2.2.2.2.1])
    subst he
    exact hD2 T0 T s0 hh0 hh1 hlt

end Top

end L3.WriterOrder

#print axioms L3.WriterOrder.headOnlyLast
#print axioms L3.WriterOrder.headDeadAfter
#print axioms L3.WriterOrder.headDeadStep
#print axioms L3.WriterOrder.laneRunInitial
#print axioms L3.WriterOrder.laneRunStep
#print axioms L3.WriterOrder.laneRunFold
#print axioms L3.WriterOrder.termHeadOfCompletion
#print axioms L3.WriterOrder.completionTailOrderStrict
