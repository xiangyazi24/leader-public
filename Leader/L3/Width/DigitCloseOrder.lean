import Leader.L3.Width.DigitCloseRank
import Leader.L3.Width.DigitFirstZero
import Leader.L3.Width.DigitBand

/-!
# The completion tail order, proved: a later completion has a later tail

`L3.CloseRank.widthComparisonCloseOfOrder` reduces `WidthComparisonClose` to
`CompletionTailOrder`: of two comparison completions of a complete pair on the clean run, the
later terminal reads a tail sample no older than the earlier one's.  This module proves it from
the barrier invariant `L3.TermEntry.BarInv`, with no new target-side invariant:

* `deadOfHead`: at a terminal letter, the completing tail `s0` sits at the last target cell as
  the first use of a clean live carry.  Behind it (`BarInv`) every tracked atom is sampled after
  `s0` and no target cell is live, so no border tail older than `s0` is at any barrier location;
* `deadStep`: a border tail at no barrier location stays so (`barAtBack`: a location after a
  letter comes from a location before it, or from the letter's own border read);
* `OrderRun`: every recorded head terminal (terminal edge, clean ledger, head `s0`) has every
  older border tail at no barrier location, and head terminals come in the order of their heads;
  `orderRunStep` keeps it: a new head terminal's head is at a barrier location just before its
  letter, so it is no older than the head of any earlier one;
* `completionTailOrder`: `CompletionTailOrder` for every boundary reference, and
  `widthComparisonClose`: `WidthComparisonClose` itself.

Model check: research/lean-l3/ledgers/close-mc.py clauses `c_next` and `fifo` (close-family-notes
sections 9 and 13).
-/

namespace L3.CloseOrder

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

/-! ### On the lane cells -/

section Lane

variable {c : Compiled} {n : Nat} {R : Nat}

/-- **No older tail survives a completing head**: if the last target cell holds a clean live
carry whose first use reads the border tail `s0`, then no border tail older than `s0` is at any
barrier location (behind `s0` every tracked atom is sampled after `s0` and no target cell is
live; at the last cell the ledger head is `s0`).  Consumer: `orderRunStep`. -/
theorem deadOfHead (hR : 2 ≤ R) {s : CohortLane} {g : Nat → DigitLaneGhost c n}
    {s0 sigma : DigitStamp n} {clock : Nat} (h : BarInv R s g s0 clock)
    (hlive : s.live (2 * R - 1) = true) (L : DigitCarryGhost c n) (u : DigitUse c n)
    (hL : (g (2 * R - 1)).carry = some L) (hi : L.inherited = none)
    (hu : L.uses.head? = some u) (hop : u.operand = some (.sampled s0))
    (hlt : sigma.time < s0.time) : ∀ q, ¬ BarAt R s g sigma q := by
  have hat : BarAt R s g s0 (2 * R - 1) :=
    Or.inr (Or.inr (Or.inr ⟨by omega, by omega, hlive, L, u, hL, hi, hu, hop⟩))
  obtain ⟨hsh, -, hage⟩ := h _ hat
  have hold : ∀ p, p < 2 * R - 1 → trackedAt R g p ≠ some (.sampled sigma) := by
    intro p hp ht
    obtain ⟨id, hid, hlt'⟩ := hage p _ hp ht
    cases hid
    omega
  intro q hq
  rcases hq with ⟨h1, -, h3⟩ | ⟨h1, h2, h3, -, h5⟩ | ⟨-, -, h3⟩ |
      ⟨h1, h2, h3, L', u', h4, -, h6, h7⟩
  · apply hold q (by omega)
    unfold trackedAt
    rw [if_pos h1]
    exact h3
  · by_cases hq : q = 2 * R - 1
    · subst hq
      rw [hlive] at h3
      cases h3
    · apply hold q (by omega)
      unfold trackedAt
      rw [if_neg (by omega), if_pos h2]
      exact h5
  · apply hold R (by omega)
    unfold trackedAt
    rw [if_neg (by omega), if_pos (by omega)]
    exact h3
  · by_cases hq : q = 2 * R - 1
    · subst hq
      rw [hL] at h4
      cases h4
      rw [hu] at h6
      cases h6
      rw [hop] at h7
      simp only [Option.some.injEq, DigitAtom.sampled.injEq] at h7
      rw [h7] at hlt
      omega
    · have hd := (barTgt hsh (by omega) (by omega) q h1 (by omega)).1
      rw [hd] at h3
      cases h3

/-- **A border tail at no barrier location stays so** under every letter that does not read it
(`barAtBack`).  Consumer: `orderRunStep`. -/
theorem deadStep (hR : 2 ≤ R) {stamp sigma : DigitStamp n} {s : CohortLane}
    {g g' : Nat → DigitLaneGhost c n} {Ok : Bool → DigitAtom n → Prop} (ke : Option Nat)
    (hrows : LaneRows R stamp s g g' ke) (hcorr : PureCorr R Ok s g)
    (hne : CleanNe R g) (hT : ∀ T, Ok T (.sampled sigma) → T = true)
    (hfresh : sigma ≠ stamp) (h : ∀ q, ¬ BarAt R s g sigma q) :
    ∀ q, ¬ BarAt R (cohortLaneStep R s ke) g' sigma q := by
  intro q hq
  rcases barAtBack hR ke hrows hcorr hne hT q hq with ⟨hss, -⟩ | hpre | ⟨-, -, -, hpre, -⟩
  · exact hfresh hss
  · exact h q hpre
  · exact h (q - 1) hpre

end Lane

/-! ### The order run on the projected ring -/

section Ring

variable {c : Compiled} {n : Nat}

/-- **A head terminal** of a pair and lane: a recorded terminal on the terminal edge
`src + 2R - 1` whose clean ledger's first use reads the border-tail stamp `s0`.  Consumer:
`OrderRun`, `completionTailOrder`. -/
def TermHead (ring : DirectedRing n) (root : Fin n) (lane : DigitLane) (src R : Nat)
    (A : DigitAudit c n) (U : DigitTerminal c n) (s0 : DigitStamp n) : Prop :=
  DigitRecordedTerminal A U ∧ U.lane = lane ∧
  U.source = digitSite ring root (src + (2 * R - 1)) ∧
  s0.site = digitSite ring root src ∧ s0.lane = lane ∧
  ∃ (L : DigitCarryGhost c n) (u : DigitUse c n), U.ledger = some L ∧ L.inherited = none ∧
    L.uses.head? = some u ∧ u.operand = some (.sampled s0)

/-- **The order run invariant**: for every head terminal with head `s0`, `s0` is stamped by the
clock and every border tail older than `s0` is at no barrier location; and of two head
terminals the later one has the later (or equal) head.  Consumer: `orderRunStep`,
`completionTailOrder`. -/
def OrderRun (ring : DirectedRing n) (root : Fin n) (lane : DigitLane) (src R : Nat)
    (S : Fin n → ProjD c) (A : DigitAudit c n) : Prop :=
  (∀ (U : DigitTerminal c n) (s0 : DigitStamp n), TermHead ring root lane src R A U s0 →
    s0.time ≤ A.clock ∧
    ∀ sigma : DigitStamp n, sigma.site = digitSite ring root src → sigma.lane = lane →
      sigma.time < s0.time →
      ∀ q, ¬ BarAt R (cohortProj ring root lane src R S) (laneCells ring root lane src A.current)
        sigma q) ∧
  (∀ (U0 : DigitTerminal c n) (s0 : DigitStamp n) (U : DigitTerminal c n) (s : DigitStamp n),
    TermHead ring root lane src R A U0 s0 → TermHead ring root lane src R A U s →
    U0.time < U.time → s0.time ≤ s.time)

/-- **The order run at the audit start** (no terminal is recorded).  Consumer:
`orderRunWidth`. -/
theorem orderRunInitial (ring : DirectedRing n) (root : Fin n) (lane : DigitLane) (src R : Nat)
    (S : Fin n → ProjD c) : OrderRun ring root lane src R S (digitAuditInitial S) := by
  have hno : ∀ (U : DigitTerminal c n) (s0 : DigitStamp n),
      ¬ TermHead ring root lane src R (digitAuditInitial S) U s0 := by
    intro U s0 h
    obtain ⟨f, hf, -⟩ := h.1
    exact absurd hf List.not_mem_nil
  exact ⟨fun U s0 h => absurd h (hno U s0), fun U0 s0 _ _ h _ _ => absurd h (hno U0 s0)⟩

/-- **Every letter keeps the order run** (projected ring, layout hypotheses of `cohortProjStep`,
the correspondence, the frame order and the barrier run before the letter).  A head terminal
recorded by the letter has its head at the last target cell just before it: by `deadOfHead`
every older border tail is then at no barrier location, and by the invariant of any earlier
head terminal its head is no older than that terminal's.  Consumer: `orderRunWidth`. -/
theorem orderRunStep (ring : DirectedRing n) (hn : 2 ≤ n) (root : Fin n)
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
    (hbar : BarRun ring root lane src R S A) (h : OrderRun ring root lane src R S A) :
    OrderRun ring root lane src R (phiD ring S (digitSite ring root j))
      (digitAuditStep ring S A (digitSite ring root j)) := by
  obtain ⟨hne, hbt, hinv⟩ := hbar
  obtain ⟨hI1, hI2⟩ := h
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
  have hdead : ∀ sigma : DigitStamp n, sigma.site = digitSite ring root src →
      sigma.lane = lane → sigma.time ≤ A.clock →
      (∀ q, ¬ BarAt R (cohortProj ring root lane src R S)
        (laneCells ring root lane src A.current) sigma q) →
      ∀ q, ¬ BarAt R (cohortProj ring root lane src R (phiD ring S (digitSite ring root j)))
        (laneCells ring root lane src (digitAuditStep ring S A (digitSite ring root j)).current)
        sigma q := by
    intro sigma hsi hl ht hd
    rw [hproj]
    refine deadStep hR _ hrows hgc.1 hne (hTb sigma hsi hl) (fun he => ?_) hd
    subst he
    exact absurd ht (Nat.not_succ_le_self _)
  have hnew : ∀ (U : DigitTerminal c n) (s0 : DigitStamp n),
      TermHead ring root lane src R (digitAuditStep ring S A (digitSite ring root j)) U s0 →
      TermHead ring root lane src R A U s0 ∨
      (U.time = A.clock + 1 ∧
        BarAt R (cohortProj ring root lane src R S) (laneCells ring root lane src A.current) s0
          (2 * R - 1) ∧ s0.time ≤ A.clock ∧
        ∀ sigma : DigitStamp n, sigma.time < s0.time →
          ∀ q, ¬ BarAt R (cohortProj ring root lane src R S)
            (laneCells ring root lane src A.current) sigma q) := by
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
      have hat : BarAt R (cohortProj ring root lane src R S)
          (laneCells ring root lane src A.current) s0 (2 * R - 1) :=
        Or.inr (Or.inr (Or.inr ⟨by omega, by omega, hlive', L, u, hLc, hi, hu, hop⟩))
      exact ⟨ht, hat, (hinv s0 hsi0 hl0 _ hat).2.1, fun sigma hlt =>
        deadOfHead hR (hinv s0 hsi0 hl0) hlive' L u hLc hi hu hop hlt⟩
  have hold : ∀ U : DigitTerminal c n, DigitRecordedTerminal A U → U.time ≤ A.clock := by
    intro U hU
    obtain ⟨f, hf, hft, -⟩ := hU
    have := (hfo.2.1 f hf).2
    omega
  refine ⟨fun U s0 hU => ?_, fun U0 s0 U s hU0 hU hlt => ?_⟩
  · rcases hnew U s0 hU with hpre | ⟨-, -, ht, hd⟩
    · obtain ⟨ht, hd⟩ := hI1 U s0 hpre
      exact ⟨by show s0.time ≤ A.clock + 1; omega,
        fun sigma hsi hl hlt => hdead sigma hsi hl (by omega) (hd sigma hsi hl hlt)⟩
    · exact ⟨by show s0.time ≤ A.clock + 1; omega,
        fun sigma hsi hl hlt => hdead sigma hsi hl (by omega) (hd sigma hlt)⟩
  · have hsi := hU.2.2.2.1
    have hsl := hU.2.2.2.2.1
    rcases hnew U0 s0 hU0 with hpre0 | ⟨ht0, -, -, -⟩
    · rcases hnew U s hU with hpre | ⟨-, hat, -, -⟩
      · exact hI2 U0 s0 U s hpre0 hpre hlt
      · rcases Nat.lt_or_ge s.time s0.time with hlt' | hge
        · exact absurd hat ((hI1 U0 s0 hpre0).2 s hsi hsl hlt' (2 * R - 1))
        · exact hge
    · rcases hnew U s hU with hpre | ⟨ht, -, -, -⟩
      · have := hold U hpre.1
        omega
      · omega

end Ring

/-! ### The clean run -/

variable {n : Nat} {ring : DirectedRing n}

/-- **The order run on the clean run**: along every word from a clean start, the order run of a
complete pair of the start on the comparison lane.  Consumer: `completionTailOrder`. -/
theorem orderRunWidth (ref : WidthBoundaryReference ring) (hn : 5 ≤ n)
    (root : Fin n) (start : ref.State)
    (hL : WidthBoundaryDigitLayoutValues ref root start) (source : Nat)
    (hpair : DigitCompletePair ring root (piD (ref.phys start)) source
      (source + digitSpan (compileAdvice (ceilLogTwo n)))) (u : List (Fin n)) :
    OrderRun ring root DigitLane.comparison source (digitSpan (compileAdvice (ceilLogTwo n)))
      (piD (ref.phys (u.foldl (widthDigitAuditNext ref.toWidthDigitReference)
        (start, digitAuditInitial (piD (ref.phys start)))).1))
      (u.foldl (widthDigitAuditNext ref.toWidthDigitReference)
        (start, digitAuditInitial (piD (ref.phys start)))).2 := by
  obtain ⟨hsrc, hend, -⟩ := pairLayoutStart ref hn root start hL source hpair
  have hR : 2 ≤ digitSpan (compileAdvice (ceilLogTwo n)) := valueSpanTwo hn
  have key : ∀ (m : Nat) (u : List (Fin n)), u.length = m →
      OrderRun ring root DigitLane.comparison source (digitSpan (compileAdvice (ceilLogTwo n)))
        (piD (ref.phys (u.foldl (widthDigitAuditNext ref.toWidthDigitReference)
          (start, digitAuditInitial (piD (ref.phys start)))).1))
        (u.foldl (widthDigitAuditNext ref.toWidthDigitReference)
          (start, digitAuditInitial (piD (ref.phys start)))).2 := by
    intro m
    induction m with
    | zero =>
      intro u hu
      have hnil : u = [] := List.eq_nil_of_length_eq_zero hu
      subst hnil
      exact orderRunInitial ring root DigitLane.comparison source _ _
    | succ m ih =>
      intro u hu
      rcases List.eq_nil_or_concat u with hnil | ⟨u', e, hcat⟩
      · subst hnil
        simp at hu
      · subst hcat
        have hlen : u'.length = m := by
          simp only [List.concat_eq_append, List.length_append, List.length_cons,
            List.length_nil] at hu
          omega
        have ih' := ih u' hlen
        obtain ⟨⟨hl, hg, -⟩, hfo, hbar⟩ := barRunWidth ref hn root start hL source hpair u'
        simp only [List.concat_eq_append, List.foldl_append, List.foldl_cons, List.foldl_nil]
        generalize u'.foldl (widthDigitAuditNext ref.toWidthDigitReference)
          (start, digitAuditInitial (piD (ref.phys start))) = y at ih' hl hg hfo hbar ⊢
        obtain ⟨hL0, hb0, hbR, hb2R, hbF⟩ := hl
        obtain ⟨heq, hroot, hbX, hbY⟩ := widthLeadEdge ref.toWidthDigitReference
          ref.singletonFixed hn root y.1 hL0 e
        obtain ⟨j, hj, rfl⟩ := bankRepairDigitSiteSurj ring root e
        show OrderRun ring root DigitLane.comparison source
          (digitSpan (compileAdvice (ceilLogTwo n)))
          (piD (ref.phys (ref.next y.1 (digitSite ring root j))))
          (digitAuditStep ring (piD (ref.phys y.1)) y.2 (digitSite ring root j))
        rw [heq]
        exact orderRunStep ring (by omega) root (piD (ref.phys y.1)) _ source hR hsrc hend hroot
          hb0 hbR hb2R hbF DigitLane.comparison (InheritedOk DigitLane.comparison)
          (inheritedNoSample DigitLane.comparison) y.2 j hj hbX hbY hg hfo hbar ih'
  exact key u.length u rfl

/-- **The completion tail order** (any boundary reference): of two comparison
completions of a complete pair on the clean run, the later terminal reads a tail sample no older
than the earlier one's.  Both terminals are head terminals; distinct times are ordered by
`orderRunWidth`, equal times name one frame and hence one terminal.  Consumer:
`widthComparisonClose`. -/
theorem completionTailOrder (ref : WidthBoundaryReference ring) (hn : 5 ≤ n)
    :
    CompletionTailOrder ref.toWidthDigitReference := by
  intro root start u source cut0 cut T0 T s0 s hst hs hpair hT0 hT hle h0 h1
  obtain ⟨root0, hs0, hL⟩ := widthCleanBoundaryRoot ref start hst
  have hr : root = root0 :=
    (ref.singletonFixed root0 start hs0).2.1 root (ref.singletonFixed root start hs).1
  subst hr
  obtain ⟨-, hfo, -⟩ := barRunWidth ref hn root start hL source hpair u
  obtain ⟨-, hI2⟩ := orderRunWidth ref hn root start hL source hpair u
  generalize u.foldl (widthDigitAuditNext ref.toWidthDigitReference)
    (start, digitAuditInitial (piD (ref.phys start))) = y at hfo hI2 hT0 hT
  have head : ∀ (cut' : Nat) (U : DigitTerminal (compileAdvice (ceilLogTwo n)) n)
      (sg : DigitStamp n),
      DigitCompletion ring y.2 root source (source + digitSpan (compileAdvice (ceilLogTwo n)))
        DigitLane.comparison cut' U →
      (∀ (L : DigitCarryGhost (compileAdvice (ceilLogTwo n)) n)
        (v : DigitUse (compileAdvice (ceilLogTwo n)) n), U.ledger = some L →
        L.uses.head? = some v → v.operand = some (.sampled sg)) →
      TermHead ring root DigitLane.comparison source (digitSpan (compileAdvice (ceilLogTwo n)))
        y.2 U sg := by
    intro cut' U sg hU hh
    obtain ⟨smp, -, hsi, hl, -, -, L, v, hLU, hv, hop, -⟩ :=
      completionTail ring y.2 root source _ DigitLane.comparison cut' U hU
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
  have hh0 := head cut0 T0 s0 hT0 h0
  have hh1 := head cut T s hT h1
  rcases Nat.lt_or_ge T0.time T.time with hlt | hge
  · exact hI2 T0 s0 T s hh0 hh1 hlt
  · have htime : T0.time = T.time := by omega
    obtain ⟨f0, hf0, ht0, -, hr0⟩ := hh0.1
    obtain ⟨f1, hf1, ht1, -, hr1⟩ := hh1.1
    have hff : f0 = f1 := auditFrameTimeInj y.2 hfo f0 f1 hf0 hf1 (by rw [ht0, ht1, htime])
    subst hff
    rw [hh0.2.1] at hr0
    rw [hh1.2.1] at hr1
    have hTT : T0 = T := Option.some.inj (hr0.symm.trans hr1)
    subst hTT
    obtain ⟨-, -, -, -, -, L, v, hLv, -, hv, hop⟩ := hh0
    have e := (h1 L v hLv hv).symm.trans hop
    simp only [Option.some.injEq, DigitAtom.sampled.injEq] at e
    rw [e]
    exact Nat.le_refl _

/-- **`WidthComparisonClose`** for every boundary reference.  Consumer: the SMALL
premise `hcmpClose` of `l3HeadlineOfCleanBranches` (Leader/L3/Headline/CleanAssembly.lean) and the
BANK premise of `L3.PacketMomentCompareBank.hcompareBankOfStage`. -/
theorem widthComparisonClose (ref : WidthBoundaryReference ring) (hn : 5 ≤ n)
    :
    WidthComparisonClose ref.toWidthDigitReference :=
  widthComparisonCloseOfOrder ref hn (completionTailOrder ref hn)

/-- **The headline premise `hcmpClose`**: `WidthComparisonClose` at the band reference (SMALL and
BANK through their boundary references, `widthComparisonClose`).  Consumer: `hcmpClose` of
`l3HeadlineOfCleanBranches` (Leader/L3/Headline/CleanAssembly.lean). -/
theorem bandWidthComparisonClose (ring : DirectedRing n) (hn : 5 ≤ n)
    :
    WidthComparisonClose (bandWidthDigitReference ring hn) := by
  by_cases hs : (compileAdvice (ceilLogTwo n)).useSmall = true
  · rw [bandWidthDigitReferenceSmall ring hn hs]
    exact widthComparisonClose (smallWidthBoundaryReference ring hn hs) hn
  · have hb : (compileAdvice (ceilLogTwo n)).useSmall = false := by
      cases hh : (compileAdvice (ceilLogTwo n)).useSmall
      · rfl
      · exact absurd hh hs
    rw [bandWidthDigitReferenceBank ring hn hb]
    exact widthComparisonClose (bankWidthBoundaryReference ring hn hb) hn

end L3.CloseOrder

#print axioms L3.CloseOrder.deadOfHead
#print axioms L3.CloseOrder.deadStep
#print axioms L3.CloseOrder.orderRunInitial
#print axioms L3.CloseOrder.orderRunStep
#print axioms L3.CloseOrder.orderRunWidth
#print axioms L3.CloseOrder.completionTailOrder
#print axioms L3.CloseOrder.widthComparisonClose
#print axioms L3.CloseOrder.bandWidthComparisonClose
