import Leader.L3.Bank.RepairDigitTailAhead
import Leader.L3.Width.DigitCloseTerm

/-!
# Clause (R) of the comparison close, reduced to the completion tail order

`L3.CloseTerm.widthComparisonCloseOfRanks` leaves clause (R): the first strict comparison
completion after `restart` of every complete pair has an anchor and is `DigitTerminalRanked`.
This module proves (R) from one target-side fact, `CompletionTailOrder` (a later completion of a
pair has a tail sample no older than an earlier one's), and everything else on the clean run:

* `rankRunWidth`: along every clean-run word, `PairBase`, the frame order, `TailInv` for every
  border-tail stamp (`L3.TailChain`) and `AheadRun` (`L3.TailAhead`);
* `completionCutZero`, `minTerminal`, `anchorOfFirst`, `completionTail`: the anchor is the first
  strict completion with cut 0, which exists below every completion; its tail sample is the
  anchor tail;
* `sameTailRanked`: two completions of a pair with one tail sample have the same samples
  (export uniqueness and the consecutive-export clauses), so the later one is rank 0;
* `clauseROfOrder`: a later tail gives rank `k + 1` by `L3.TailAhead.groupCause`, the same tail
  rank 0; `widthComparisonCloseOfOrder`: `WidthComparisonClose` from `CompletionTailOrder`.
-/

namespace L3.CloseRank

set_option autoImplicit false

open L3
open L3.RenewalReferenceClock
open L3.WidthDigit
open L3.ValueWaveClose
open L3.CompareStage
open L3.CohortDomination
open L3.CohortSites
open L3.Rearm
open L3.GhostBridge
open L3.Correspondence
open L3.CohortIdentity
open L3.CohortLedger
open L3.ValueLedger
open L3.UseRows
open L3.UseTrack
open L3.CurrentWin
open L3.CloseCurrent
open L3.CloseEntry
open L3.WidthWave
open L3.TailChain
open L3.TailAhead
open L3.CloseTerm

/-! ### The anchor and the tail of a completion -/

section Generic

variable {c : Compiled} {n : Nat}

/-- A completion after `cut` is a completion after 0. Consumer: `clauseROfOrder`. -/
theorem completionCutZero (ring : DirectedRing n) (A : DigitAudit c n) (root : Fin n)
    (source target : Nat) (lane : DigitLane) (cut : Nat) (T : DigitTerminal c n)
    (h : DigitCompletion ring A root source target lane cut T) :
    DigitCompletion ring A root source target lane 0 T := by
  obtain ⟨a1, a2, a3, a4, a5, a6, pos, L, sm, ex, us, l1, l2, l3, hall, hord, hoth⟩ := h
  refine ⟨a1, a2, a3, a4, a5, a6, pos, L, sm, ex, us, l1, l2, l3, fun j => ?_, hord, hoth⟩
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19,
    b20⟩ := hall j
  exact ⟨b1, b2, b3, by omega, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18,
    b19, b20⟩

/-- A terminal of least time exists below every terminal of a predicate. Consumer:
`clauseROfOrder`. -/
theorem minTerminal (P : DigitTerminal c n → Prop) :
    ∀ (m : Nat) (T : DigitTerminal c n), T.time ≤ m → P T →
      ∃ T0, P T0 ∧ ∀ o, P o → T0.time ≤ o.time := by
  intro m
  induction m with
  | zero =>
    intro T hT hP
    exact ⟨T, hP, fun o _ => by omega⟩
  | succ m ih =>
    intro T hT hP
    rcases Classical.em (∃ o, P o ∧ o.time < T.time) with h | h
    · obtain ⟨o, ho, hlt⟩ := h
      exact ih o (by omega) ho
    · exact ⟨T, hP, fun o ho => Nat.le_of_not_lt fun hlt => h ⟨o, ho, hlt⟩⟩

/-- **The tail sample of a completion**: use 0 reads the recorded border sample of the group,
stamped after the cut. Consumer: `anchorOfFirst`, `clauseROfOrder`. -/
theorem completionTail (ring : DirectedRing n) (A : DigitAudit c n) (root : Fin n)
    (source target : Nat) (lane : DigitLane) (cut : Nat) (T : DigitTerminal c n)
    (h : DigitCompletion ring A root source target lane cut T) :
    ∃ s : DigitSample c n, DigitRecordedSample A s ∧ s.id.site = digitSite ring root source ∧
      s.id.lane = lane ∧ s.tail = true ∧ cut < s.id.time ∧
      ∃ (L : DigitCarryGhost c n) (u : DigitUse c n), T.ledger = some L ∧
        L.uses.head? = some u ∧ u.operand = some (.sampled s.id) ∧
        ∀ (L' : DigitCarryGhost c n) (u' : DigitUse c n), T.ledger = some L' →
          L'.uses.head? = some u' → u'.operand = some (.sampled s.id) := by
  obtain ⟨-, -, -, -, -, -, pos, L, sm, _ex, us, hl, -, -, hall, -, -⟩ := h
  obtain ⟨r0, l0, si0, hc0, t0, -, -, -, -, -, -, -, ui0, -, uo0, -, -, -, -, -⟩ := hall ⟨0, pos⟩
  have hhead : L.uses.head? = some (us ⟨0, pos⟩) := by
    have e : L.uses.head? = L.uses[0]? := by cases L.uses <;> rfl
    exact e.trans ui0
  refine ⟨sm ⟨0, pos⟩, r0, by rw [si0]; rfl, l0, by simp [t0], hc0, L, us ⟨0, pos⟩, hl,
    hhead, uo0, fun L' u' hl' hh' => ?_⟩
  have hLL : L' = L := Option.some.inj (hl'.symm.trans hl)
  subst hLL
  have huu : u' = us ⟨0, pos⟩ := Option.some.inj (hh'.symm.trans hhead)
  subst huu
  exact uo0

/-- **The anchor**: the first strict completion with cut 0, its tail sample the anchor tail.
Consumer: `clauseROfOrder`. -/
theorem anchorOfFirst (ring : DirectedRing n) (A : DigitAudit c n) (root : Fin n)
    (source target : Nat) (lane : DigitLane) (T0 : DigitTerminal c n)
    (h : DigitFirstStrictCompletion ring A root source target lane 0 T0) :
    ∃ s : DigitSample c n, DigitAnchor ring A root source target lane T0 s.id ∧
      DigitRecordedSample A s ∧ s.id.site = digitSite ring root source ∧ s.id.lane = lane ∧
      ∀ (L : DigitCarryGhost c n) (u : DigitUse c n), T0.ledger = some L →
        L.uses.head? = some u → u.operand = some (.sampled s.id) := by
  obtain ⟨s, hr, hsi, hl, ht, -, L, u, hL, hh, ho, hall⟩ :=
    completionTail ring A root source target lane 0 T0 h.1
  exact ⟨s, ⟨h, L, u, s, hL, hh, ho, hr, rfl, hl, hsi, ht⟩, hr, hsi, hl, hall⟩

/-- A member of a ledger list. Consumer: `sameTailRanked`. -/
theorem memOfGetElem {α : Type} (l : List α) (i : Nat) (a : α) (h : l[i]? = some a) : a ∈ l := by
  rw [List.getElem?_eq_some_iff] at h
  obtain ⟨hi, he⟩ := h
  rw [← he]
  exact List.getElem_mem hi

/-- **One tail, one group**: two completions of a pair whose tail samples coincide consume the
same samples (their tail exports coincide by export uniqueness; each export of one group lies in
the other's consecutive export interval, so it is the other's export at the same offset), hence
the second is rank 0 from the first. Consumer: `clauseROfOrder`. -/
theorem sameTailRanked (ring : DirectedRing n) (root : Fin n) (lane : DigitLane) (src : Nat)
    (hend : src + 2 * digitSpan c < n) (Base : Bool → DigitAtom n → Prop)
    (S : Fin n → ProjD c) (A : DigitAudit c n)
    (hgd : GhostCorrDistinct ring root lane src (digitSpan c) Base S A)
    (cut0 cut : Nat) (T0 T : DigitTerminal c n)
    (hT0 : DigitCompletion ring A root src (src + digitSpan c) lane cut0 T0)
    (hT : DigitCompletion ring A root src (src + digitSpan c) lane cut T) (sigma : DigitStamp n)
    (h0 : ∀ (L : DigitCarryGhost c n) (u : DigitUse c n), T0.ledger = some L →
      L.uses.head? = some u → u.operand = some (.sampled sigma))
    (h1 : ∀ (L : DigitCarryGhost c n) (u : DigitUse c n), T.ledger = some L →
      L.uses.head? = some u → u.operand = some (.sampled sigma)) :
    DigitTerminalRanked A lane (digitSite ring root src) T0 sigma T := by
  obtain ⟨-, -, -, -, -, -, pos0, L0, sm0, ex0, us0, hl0, -, -, hall0, hord0, hoth0⟩ := hT0
  obtain ⟨-, -, -, -, -, -, pos, L, sm, ex, us, hl, hinh, hlen, hall, hord, hoth⟩ := hT
  have hh0 : L0.uses.head? = some (us0 ⟨0, pos0⟩) := by
    have e : L0.uses.head? = L0.uses[0]? := by cases L0.uses <;> rfl
    exact e.trans (hall0 ⟨0, pos0⟩).2.2.2.2.2.2.2.2.2.2.2.2.1
  have hh : L.uses.head? = some (us ⟨0, pos⟩) := by
    have e : L.uses.head? = L.uses[0]? := by cases L.uses <;> rfl
    exact e.trans (hall ⟨0, pos⟩).2.2.2.2.2.2.2.2.2.2.2.2.1
  have t0 : (sm0 ⟨0, pos0⟩).id = sigma := by
    have e := ((hall0 ⟨0, pos0⟩).2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).symm.trans
      (h0 L0 _ hl0 hh0)
    simp only [Option.some.injEq, DigitAtom.sampled.injEq] at e
    exact e
  have t1 : (sm ⟨0, pos⟩).id = sigma := by
    have e := ((hall ⟨0, pos⟩).2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).symm.trans (h1 L _ hl hh)
    simp only [Option.some.injEq, DigitAtom.sampled.injEq] at e
    exact e
  -- the tail exports coincide
  obtain ⟨-, -, -, -, -, rx0, xl0, xs0, -, xo0, -⟩ := hall0 ⟨0, pos0⟩
  obtain ⟨-, -, -, -, -, rx1, xl1, xs1, -, xo1, -⟩ := hall ⟨0, pos⟩
  have hx0 : ex ⟨0, pos⟩ = ex0 ⟨0, pos0⟩ :=
    hgd.2.2.2.2.2 _ _ sigma rx1 rx0 ⟨xl1, xs1⟩ ⟨xl0, xs0⟩ (by rw [xo1, t1]) (by rw [xo0, t0])
  -- every export of a group lies between its last and its tail export
  have inter : ∀ (e : Fin (digitSpan c) → DigitExport c n),
      (∀ i j : Fin (digitSpan c), i.val < j.val → (e j).time < (e i).time) →
      ∀ j : Fin (digitSpan c), (e ⟨digitSpan c - 1, by omega⟩).time ≤ (e j).time ∧
        (e j).time ≤ (e ⟨0, pos⟩).time := by
    intro e hord' j
    have hjlt := j.isLt
    refine ⟨?_, ?_⟩
    · by_cases hjl : j.val = digitSpan c - 1
      · have hjj : j = ⟨digitSpan c - 1, by omega⟩ := Fin.ext hjl
        rw [hjj]
        exact Nat.le_refl _
      · exact Nat.le_of_lt (hord' j ⟨digitSpan c - 1, by omega⟩ (by show j.val < digitSpan c - 1; omega))
    · by_cases hj0 : j.val = 0
      · have hjj : j = ⟨0, pos⟩ := Fin.ext hj0
        rw [hjj]
        exact Nat.le_refl _
      · exact Nat.le_of_lt (hord' ⟨0, pos⟩ j (by show 0 < j.val; omega))
  have i0 := inter ex0 (fun i j h => (hord0 i j h).1)
  have i1 := inter ex (fun i j h => (hord i j h).1)
  -- the same sample at every offset
  have key : ∀ j : Fin (digitSpan c), (sm j).id = (sm0 j).id := by
    intro j
    have hjlt := j.isLt
    rcases Nat.lt_or_ge (ex ⟨digitSpan c - 1, by omega⟩).time
        (ex0 ⟨digitSpan c - 1, by omega⟩).time with hlt | hge
    · obtain ⟨-, -, -, -, -, rxj, xlj, xsj, xdj, xoj, -⟩ := hall0 j
      have a1 := (i0 j).1
      have a2 := (i0 j).2
      obtain ⟨j', hj'⟩ := hoth (ex0 j) rxj xlj xsj xdj (by omega)
        (by rw [hx0]; exact a2)
      obtain ⟨-, -, sij', -, -, -, -, -, -, xoj', -⟩ := hall j'
      have hj'lt := j'.isLt
      have e2 : (ex0 j).operand = some (.sampled (sm j').id) := by rw [hj']; exact xoj'
      have e := xoj.symm.trans e2
      simp only [Option.some.injEq, DigitAtom.sampled.injEq] at e
      have sij := (hall0 j).2.2.1
      have hs : digitSite ring root (src + j.val) = digitSite ring root (src + j'.val) := by
        rw [← sij, ← sij', e]
      have := bankRepairDigitSiteInj ring root (by omega) (by omega) hs
      have hjj : j' = j := Fin.ext (by omega)
      rw [hjj] at e
      exact e.symm
    · obtain ⟨-, -, -, -, -, rxj, xlj, xsj, xdj, xoj, -⟩ := hall j
      have a1 := (i1 j).1
      have a2 := (i1 j).2
      obtain ⟨j', hj'⟩ := hoth0 (ex j) rxj xlj xsj xdj (by omega)
        (by rw [← hx0]; exact a2)
      obtain ⟨-, -, sij', -, -, -, -, -, -, xoj', -⟩ := hall0 j'
      have hj'lt := j'.isLt
      have e2 : (ex j).operand = some (.sampled (sm0 j').id) := by rw [hj']; exact xoj'
      have e := xoj.symm.trans e2
      simp only [Option.some.injEq, DigitAtom.sampled.injEq] at e
      have sij := (hall j).2.2.1
      have hs : digitSite ring root (src + j.val) = digitSite ring root (src + j'.val) := by
        rw [← sij, ← sij', e]
      have := bankRepairDigitSiteInj ring root (by omega) (by omega) hs
      have hjj : j' = j := Fin.ext (by omega)
      rw [hjj] at e
      exact e
  refine ⟨L, 0, hl, hinh, fun h => ?_, fun use hu => ?_⟩
  · rw [h] at hlen
    simp at hlen
    omega
  · obtain ⟨i, hi, hget⟩ := List.mem_iff_getElem.mp hu
    have hj : i < digitSpan c := by rw [← hlen]; exact hi
    obtain ⟨rj, lj, -, -, -, -, -, -, -, -, -, -, uij, -, uoj, -, -, -, -, -⟩ := hall ⟨i, hj⟩
    have h' : L.uses[i]? = some use := by rw [List.getElem?_eq_getElem hi, hget]
    have hu' : us ⟨i, hj⟩ = use := Option.some.inj (uij.symm.trans h')
    rw [← hu', uoj]
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, uij0, -, uoj0, -, -, -, -, -⟩ := hall0 ⟨i, hj⟩
    exact ⟨sm ⟨i, hj⟩, rfl, rj, lj, Or.inl ⟨rfl, L0, us0 ⟨i, hj⟩, hl0,
      memOfGetElem L0.uses i _ uij0, by rw [uoj0, key ⟨i, hj⟩]⟩⟩

end Generic

/-! ### The clean run -/

variable {n : Nat} {ring : DirectedRing n}

/-- **The rank run on the clean run**: along every word from a clean start, the routine part of
the window class, the frame order, `TailInv` for every border-tail stamp and `AheadRun`, for a
complete pair of the start on the comparison lane. Consumer: `clauseROfOrder`. -/
theorem rankRunWidth (ref : WidthBoundaryReference ring) (hn : 5 ≤ n)
    (root : Fin n) (start : ref.State)
    (hL : WidthBoundaryDigitLayoutValues ref root start) (source : Nat)
    (hpair : DigitCompletePair ring root (piD (ref.phys start)) source
      (source + digitSpan (compileAdvice (ceilLogTwo n)))) (u : List (Fin n)) :
    PairBase ref.toWidthDigitReference root source (digitSpan (compileAdvice (ceilLogTwo n)))
      (u.foldl (widthDigitAuditNext ref.toWidthDigitReference)
        (start, digitAuditInitial (piD (ref.phys start)))) ∧
    AuditFrameOrder (u.foldl (widthDigitAuditNext ref.toWidthDigitReference)
        (start, digitAuditInitial (piD (ref.phys start)))).2 ∧
    (∀ sigma0 : DigitStamp n, TailInv ring root DigitLane.comparison source
      (digitSpan (compileAdvice (ceilLogTwo n))) sigma0
      (piD (ref.phys (u.foldl (widthDigitAuditNext ref.toWidthDigitReference)
        (start, digitAuditInitial (piD (ref.phys start)))).1))
      (u.foldl (widthDigitAuditNext ref.toWidthDigitReference)
        (start, digitAuditInitial (piD (ref.phys start)))).2) ∧
    AheadRun ring root DigitLane.comparison source (digitSpan (compileAdvice (ceilLogTwo n)))
      (piD (ref.phys (u.foldl (widthDigitAuditNext ref.toWidthDigitReference)
        (start, digitAuditInitial (piD (ref.phys start)))).1))
      (u.foldl (widthDigitAuditNext ref.toWidthDigitReference)
        (start, digitAuditInitial (piD (ref.phys start)))).2 := by
  obtain ⟨hsrc, hend, hlay⟩ := pairLayoutStart ref hn root start hL source hpair
  have hR : 2 ≤ digitSpan (compileAdvice (ceilLogTwo n)) := valueSpanTwo hn
  have h0 : PairBase ref.toWidthDigitReference root source
      (digitSpan (compileAdvice (ceilLogTwo n))) (start, digitAuditInitial (piD (ref.phys start))) ∧
      AuditFrameOrder (start, digitAuditInitial (piD (ref.phys start))).2 ∧
      (∀ sigma0 : DigitStamp n, TailInv ring root DigitLane.comparison source
        (digitSpan (compileAdvice (ceilLogTwo n))) sigma0
        (piD (ref.phys (start, digitAuditInitial (piD (ref.phys start))).1))
        (start, digitAuditInitial (piD (ref.phys start))).2) ∧
      AheadRun ring root DigitLane.comparison source (digitSpan (compileAdvice (ceilLogTwo n)))
        (piD (ref.phys (start, digitAuditInitial (piD (ref.phys start))).1))
        (start, digitAuditInitial (piD (ref.phys start))).2 :=
    ⟨⟨hlay, ghostCorrDistinctInitial ring root _ _ _ _,
      ⟨valCorrInitial ring root _ _ _ _, exportValInitial ring root _ _ _ _,
        useValInitial ring root _ _ _ _, ledgerOkInitial ring root _ _ _ _⟩⟩,
      auditFrameOrderInitial _,
      fun sigma0 => tailInvInitial ring root DigitLane.comparison source _ _ sigma0,
      aheadRunInitial ring root DigitLane.comparison source _ _⟩
  generalize (start, digitAuditInitial (piD (ref.phys start))) = y at h0
  induction u generalizing y with
  | nil => exact h0
  | cons e rest ih =>
    apply ih
    obtain ⟨⟨hl, hg, hv⟩, hfo, htail, hah⟩ := h0
    obtain ⟨hl', hg'⟩ := widthGhostCorrDistinctStep ref.toWidthDigitReference ref.singletonFixed hn
      root DigitLane.comparison source _ hR hsrc hend (InheritedOk DigitLane.comparison) y hl hg e
    refine ⟨⟨hl', hg', widthValInvStep ref.toWidthDigitReference ref.singletonFixed hn root
      DigitLane.comparison source _ hR hsrc hend y hl hv e⟩, auditFrameOrderStep ring _ y.2 e hfo,
      ?_⟩
    obtain ⟨hL0, hb0, hbR, hb2R, hbF⟩ := hl
    obtain ⟨heq, hroot, hbX, hbY⟩ := widthLeadEdge ref.toWidthDigitReference ref.singletonFixed hn
      root y.1 hL0 e
    obtain ⟨j, hj, rfl⟩ := bankRepairDigitSiteSurj ring root e
    have hg2 : GhostCorrDistinct ring root DigitLane.comparison source
        (digitSpan (compileAdvice (ceilLogTwo n))) (InheritedOk DigitLane.comparison)
        (phiD ring (piD (ref.phys y.1)) (digitSite ring root j))
        (digitAuditStep ring (piD (ref.phys y.1)) y.2 (digitSite ring root j)) := by
      have h' : GhostCorrDistinct ring root DigitLane.comparison source
          (digitSpan (compileAdvice (ceilLogTwo n))) (InheritedOk DigitLane.comparison)
          (piD (ref.phys (ref.next y.1 (digitSite ring root j))))
          (digitAuditStep ring (piD (ref.phys y.1)) y.2 (digitSite ring root j)) := hg'
      rw [heq] at h'
      exact h'
    show (∀ sigma0 : DigitStamp n, TailInv ring root DigitLane.comparison source
        (digitSpan (compileAdvice (ceilLogTwo n))) sigma0
        (piD (ref.phys (ref.next y.1 (digitSite ring root j))))
        (digitAuditStep ring (piD (ref.phys y.1)) y.2 (digitSite ring root j))) ∧
      AheadRun ring root DigitLane.comparison source (digitSpan (compileAdvice (ceilLogTwo n)))
        (piD (ref.phys (ref.next y.1 (digitSite ring root j))))
        (digitAuditStep ring (piD (ref.phys y.1)) y.2 (digitSite ring root j))
    rw [heq]
    exact ⟨fun sigma0 => tailInvStep ring (by omega) root (piD (ref.phys y.1)) _ source hR hsrc
      hend hroot hb0 hbR hb2R hbF DigitLane.comparison (InheritedOk DigitLane.comparison) y.2 j hj
      hbX hbY sigma0 hfo hg (htail sigma0),
      aheadRunStep ring (by omega) root (piD (ref.phys y.1)) _ source hR hsrc hend hroot hb0 hbR
        hb2R hbF DigitLane.comparison (InheritedOk DigitLane.comparison) y.2 j hj hbX hbY hfo hg
        hg2 hah⟩

/-- **The completion tail order** (the first missing fact of clause (R), target side): on the
clean run from a start, of two comparison completions of a complete pair of the start, the later
terminal has a tail sample no older than the earlier one's (completions occur in the order their
groups were exported).  Model check: research/lean-l3/ledgers/close-mc.py `c_next` (consecutive
completions after the anchor have ranks 0, 1, 2, ...; R ≤ 3).  Consumer: `clauseROfOrder`. -/
def CompletionTailOrder (ref : WidthDigitReference ring) : Prop :=
  ∀ (root : Fin n) (start : ref.State) (u : List (Fin n)) (source cut0 cut : Nat)
    (T0 T : DigitTerminal (compileAdvice (ceilLogTwo n)) n) (s0 s : DigitStamp n),
    ref.start start → ref.singleton root start →
    DigitCompletePair ring root (piD (ref.phys start)) source
      (source + digitSpan (compileAdvice (ceilLogTwo n))) →
    DigitCompletion ring
      (u.foldl (widthDigitAuditNext ref) (start, digitAuditInitial (piD (ref.phys start)))).2
      root source (source + digitSpan (compileAdvice (ceilLogTwo n))) DigitLane.comparison cut0 T0 →
    DigitCompletion ring
      (u.foldl (widthDigitAuditNext ref) (start, digitAuditInitial (piD (ref.phys start)))).2
      root source (source + digitSpan (compileAdvice (ceilLogTwo n))) DigitLane.comparison cut T →
    T0.time ≤ T.time →
    (∀ (L : DigitCarryGhost (compileAdvice (ceilLogTwo n)) n)
      (v : DigitUse (compileAdvice (ceilLogTwo n)) n), T0.ledger = some L →
      L.uses.head? = some v → v.operand = some (.sampled s0)) →
    (∀ (L : DigitCarryGhost (compileAdvice (ceilLogTwo n)) n)
      (v : DigitUse (compileAdvice (ceilLogTwo n)) n), T.ledger = some L →
      L.uses.head? = some v → v.operand = some (.sampled s)) →
    s0.time ≤ s.time

/-- **Clause (R) from the completion tail order** (any boundary reference): the
anchor is the first strict completion with cut 0; a later tail gives rank `k + 1`
(`groupCause`), the same tail rank 0 (`sameTailRanked`).  Consumer:
`widthComparisonCloseOfOrder`. -/
theorem clauseROfOrder (ref : WidthBoundaryReference ring) (hn : 5 ≤ n)
    (hO : CompletionTailOrder ref.toWidthDigitReference) :
    ∀ (root : Fin n) (restart : Nat)
      (x : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n) (w : List (Fin n)),
      WidthStableRun ref.toWidthDigitReference root restart x →
      (∀ i, WidthComparePairDone ref.toWidthDigitReference root restart i
        (w.foldl (widthDigitAuditNext ref.toWidthDigitReference) x)) →
      ∀ source target : Nat,
        DigitCompletePair ring root
          (w.foldl (widthDigitAuditNext ref.toWidthDigitReference) x).2.start source target →
        ∀ terminal, DigitFirstStrictCompletion ring
          (w.foldl (widthDigitAuditNext ref.toWidthDigitReference) x).2 root source target
          .comparison restart terminal →
        ∃ (anchor : DigitTerminal (compileAdvice (ceilLogTwo n)) n) (anchorTail : DigitStamp n),
          DigitAnchor ring (w.foldl (widthDigitAuditNext ref.toWidthDigitReference) x).2 root
            source target .comparison anchor anchorTail ∧
          DigitTerminalRanked (w.foldl (widthDigitAuditNext ref.toWidthDigitReference) x).2
            .comparison (digitSite ring root source) anchor anchorTail terminal := by
  intro root restart x w hx _ source target hpair terminal hT
  obtain ⟨start, word, retired, hst, hfold, hW, -, -, -⟩ := hx
  obtain ⟨root0, hs, hL⟩ := widthCleanBoundaryRoot ref start hst
  have hx1 : x.1 = word.foldl ref.next start := by
    have := widthBoundaryDigitBoundaryAuditFirst ref start
      (digitAuditInitial (piD (ref.phys start))) word
    rw [hfold] at this
    exact this
  rw [hx1] at hW
  have hr : root = root0 :=
    (widthBoundaryDigitBoundaryWFixedRootOfSingleton ref root0 start hs word).2.1 root hW.1
  subst hr
  let init : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n :=
    (start, digitAuditInitial (piD (ref.phys start)))
  have hy : (word ++ w).foldl (widthDigitAuditNext ref.toWidthDigitReference) init =
      w.foldl (widthDigitAuditNext ref.toWidthDigitReference) x := by
    rw [List.foldl_append, hfold]
  rw [← hy] at hpair hT ⊢
  have hstart : ((word ++ w).foldl (widthDigitAuditNext ref.toWidthDigitReference) init).2.start =
      piD (ref.phys start) := by
    rw [L3.WriterReceipts.widthAuditStartFold]
    rfl
  rw [hstart] at hpair
  have htg := hpair.2.1
  subst htg
  obtain ⟨hsrc, hend, -⟩ := pairLayoutStart ref hn root start hL source hpair
  obtain ⟨⟨-, hg, -⟩, hfo, htail, hah⟩ := rankRunWidth ref hn root start hL source hpair
    (word ++ w)
  generalize hA : ((word ++ w).foldl (widthDigitAuditNext ref.toWidthDigitReference) init) = y
    at hg hfo htail hah hT ⊢
  -- the anchor
  have hT0' := completionCutZero ring y.2 root source _ DigitLane.comparison restart terminal hT.1
  obtain ⟨T0, hP0, hmin⟩ := minTerminal
    (fun o => DigitCompletion ring y.2 root source
      (source + digitSpan (compileAdvice (ceilLogTwo n))) DigitLane.comparison 0 o)
    terminal.time terminal (Nat.le_refl _) hT0'
  obtain ⟨s0, hanc, hr0, hsi0, hl0, htail0⟩ := anchorOfFirst ring y.2 root source _
    DigitLane.comparison T0 ⟨hP0, hmin⟩
  obtain ⟨s, hr1, hsi1, hl1, -, hcut1, L1, u1, hL1, hh1, ho1, htail1⟩ :=
    completionTail ring y.2 root source _ DigitLane.comparison restart terminal hT.1
  refine ⟨T0, s0.id, hanc, ?_⟩
  have hle : s0.id.time ≤ s.id.time := by
    have := hO root start (word ++ w) source 0 restart T0 terminal s0.id s.id hst hs hpair
      (by rw [hA]; exact hP0) (by rw [hA]; exact hT.1) (hmin terminal hT0') htail0 htail1
    exact this
  rcases Nat.lt_or_ge s0.id.time s.id.time with hlt | hge
  · exact groupCause ring root DigitLane.comparison source hend (InheritedOk DigitLane.comparison)
      (piD (ref.phys y.1)) y.2 hfo hg htail hah restart terminal hT.1 s0.id ⟨s0, hr0, rfl⟩ hsi0 hl0
      (fun L v id hL hv hop => by
        have e := (htail1 L v hL hv).symm.trans hop
        simp only [Option.some.injEq, DigitAtom.sampled.injEq] at e
        rw [← e]
        exact hlt) T0
  · have hst' : s0.id = s.id := by
      have ht : s0.id.time = s.id.time := by omega
      have hs1 : s0.id.site = s.id.site := by rw [hsi0, hsi1]
      have hl2 : s0.id.lane = s.id.lane := by rw [hl0, hl1]
      cases h0 : s0.id
      cases h1 : s.id
      rw [h0, h1] at ht hs1 hl2
      simp only at ht hs1 hl2
      subst ht
      subst hs1
      subst hl2
      rfl
    exact sameTailRanked ring root DigitLane.comparison source hend
      (InheritedOk DigitLane.comparison) (piD (ref.phys y.1)) y.2 hg 0 restart T0 terminal hP0
      hT.1 s0.id htail0 (by rw [hst']; exact htail1)

/-- **`WidthComparisonClose` from the completion tail order** (any boundary reference).
Consumer: the BANK premise of `L3.PacketMomentCompareBank.hcompareBankOfStage` and
the SMALL premise `hcmpCloseSmall` of `l3HeadlineOfCleanBranches`, once `CompletionTailOrder`
is produced. -/
theorem widthComparisonCloseOfOrder (ref : WidthBoundaryReference ring) (hn : 5 ≤ n)
    (hO : CompletionTailOrder ref.toWidthDigitReference) :
    WidthComparisonClose ref.toWidthDigitReference :=
  widthComparisonCloseOfRanks ref hn (clauseROfOrder ref hn hO)

end L3.CloseRank

#print axioms L3.CloseRank.completionCutZero
#print axioms L3.CloseRank.minTerminal
#print axioms L3.CloseRank.completionTail
#print axioms L3.CloseRank.anchorOfFirst
#print axioms L3.CloseRank.sameTailRanked
#print axioms L3.CloseRank.rankRunWidth
#print axioms L3.CloseRank.clauseROfOrder
#print axioms L3.CloseRank.widthComparisonCloseOfOrder
