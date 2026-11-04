import Leader.L3.Width.DigitQuietEntryValuesChain

/-!
# The first block holds zero from the base value cut on

From the boundary receipt at the retirement (closed under letters) no writer launch and no writer
advance touches a first-writable cell after the retirement, so a digit of such a cell changes only by
a base write.  After the first cover "dirty implies digit zero" holds at the cell (`zeroDirtyStep`,
`zeroDirtyOfBase`), after the second the digit is zero (`zeroOfBase`) and stays (`zeroKeep`).

* `firstBlockZeroOfCovers`: `FirstBlockZero` from `DigitBoundaryAt … retired` and the two covers.

Consumer: `L3.QuietEntryValues.quietOfCut` (WidthDigitQuietEntryValuesFinal).

Paper: research/lean-l3/ledgers/R10c-qdigit-notes.md section 9.
-/

namespace L3.QuietEntryValues

open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree
open L3
open L3.AcceptedReceipts
open L3.DigitQuiet
open L3.RenewalReferenceClock
open L3.WidthDigit
open L3.WidthWave
open L3.WriterCurrent
open L3.WriterValueCuts

set_option autoImplicit false
set_option linter.unusedSectionVars false

section Rows

variable {c : Compiled} {n : Nat} (ring : DirectedRing n) (S : Fin n → ProjD c) (e i : Fin n)

/-- The hypotheses of a cell of the first segment at one letter: not a leader, no advance into it and
no launch at it.  Consumer: `zeroCore`, `boundaryCell`. -/
structure CellQuiet : Prop where
  ne : ring.rightNeighbor e ≠ e
  li : (S i).word.native.l = false
  ly : i = e → (S (ring.rightNeighbor e)).word.native.l = false
  adv : i = ring.rightNeighbor e → ∀ cc, (S e).top.wCarry ≠ .W cc
  lau : i = e → (pairW (S e).word (S (ring.rightNeighbor e)).word).1.beta = true →
    (S i).top.wCarry = .OFF → ∀ v T, (S i).top.wIn ≠ .S v T

variable {ring S e i}

/-- **The digit of a quiet cell changes only by a base write.**  Consumer: `zeroDirtyStep`,
`zeroKeep`. -/
theorem zeroCore (h : CellQuiet ring S e i) :
    ((phiD ring S e) i).top.d = (S i).top.d ∨
      (i = e ∧ (S i).top.wBase = .ZERO ∧
        ((phiD ring S e) i).top.d =
          (if (S i).top.topDirty = true then (S i).top.d else c.zeroDigit)) := by
  by_cases hz : (S i).top.wBase = .ZERO
  · by_cases hie : i = e
    · subst hie
      right
      exact ⟨rfl, hz, writerBaseWrite ring S i h.li (h.ly rfl) hz⟩
    · left
      by_cases hij : i = ring.rightNeighbor e
      · subst hij
        refine Classical.byContradiction fun hch => ?_
        rw [phiD_at_right ring S e h.ne] at hch
        obtain ⟨cc, -, -, -, -, -, h4, -⟩ := liveTop_y_change c (S e).lift
          (S (ring.rightNeighbor e)).lift (pairW (S e).word (S (ring.rightNeighbor e)).word).1.beta
          (pairW (S e).word (S (ring.rightNeighbor e)).word).2.beta hch
        exact h.adv rfl cc h4
      · rw [phiD_at_other ring S e i hie hij]
  · left
    refine Classical.byContradiction fun hch => ?_
    rcases phiChange ring S e i h.ne hz hch with
      ⟨hi, cc, -, -, -, h2, -⟩ | ⟨hi, v, T, -, h2, h3, h4, -⟩
    · exact h.adv hi cc h2
    · exact h.lau hi h2 h3 v T h4

/-- The new dirty bit of a touched cell, through `phiD`.  Consumer: `zeroDirtyStep`. -/
theorem phiDirty (hne : ring.rightNeighbor e ≠ e) (ht : i = e ∨ i = ring.rightNeighbor e) :
    ((phiD ring S e) i).top.topDirty =
      (if (S i).top.topDirty = true then false else (((phiD ring S e) i).top.d != (S i).top.d)) := by
  rcases ht with ht | ht
  · subst ht
    rw [phiD_at_left]
    exact liveTop_dirty_x c (S i).lift (S (ring.rightNeighbor i)).lift
      (pairW (S i).word (S (ring.rightNeighbor i)).word).1.beta
      (pairW (S i).word (S (ring.rightNeighbor i)).word).2.beta
  · subst ht
    rw [phiD_at_right ring S e hne]
    exact liveTop_dirty_y c (S e).lift (S (ring.rightNeighbor e)).lift
      (pairW (S e).word (S (ring.rightNeighbor e)).word).1.beta
      (pairW (S e).word (S (ring.rightNeighbor e)).word).2.beta

/-- Dirty implies digit zero.  Consumer: `zeroDirtyStep`, `firstBlockZeroOfCovers`. -/
def ZeroDirty (x : ProjD c) : Prop := x.top.topDirty = true → x.top.d = c.zeroDigit

/-- **"Dirty implies digit zero" is carried by a quiet letter.**  Consumer:
`firstBlockZeroOfCovers`. -/
theorem zeroDirtyStep (h : CellQuiet ring S e i) (hz : ZeroDirty (S i)) :
    ZeroDirty ((phiD ring S e) i) := by
  intro hd
  by_cases ht : i = e ∨ i = ring.rightNeighbor e
  · have hnew := phiDirty (S := S) h.ne ht
    rw [hd] at hnew
    cases hod : (S i).top.topDirty with
    | true => rw [hod] at hnew; simp at hnew
    | false =>
      rw [hod] at hnew
      rcases zeroCore h with hs | ⟨-, -, hb⟩
      · rw [hs] at hnew
        simp at hnew
      · rw [hb, hod]
        simp
  · have ho : (phiD ring S e) i = S i :=
      phiD_at_other ring S e i (fun h1 => ht (Or.inl h1)) (fun h1 => ht (Or.inr h1))
    rw [ho] at hd ⊢
    exact hz hd

/-- **A base proposal establishes "dirty implies digit zero".**  Consumer:
`firstBlockZeroOfCovers`. -/
theorem zeroDirtyOfBase (h : CellQuiet ring S e e) (hb : (S e).top.wBase = .ZERO) :
    ZeroDirty ((phiD ring S e) e) := by
  intro hd
  have hnew := phiDirty (S := S) (i := e) h.ne (Or.inl rfl)
  rw [hd] at hnew
  have hw := writerBaseWrite ring S e h.li (h.ly rfl) hb
  cases hod : (S e).top.topDirty with
  | true => rw [hod] at hnew; simp at hnew
  | false =>
    rw [hw, hod]
    simp

/-- **A second base proposal stores zero.**  Consumer: `firstBlockZeroOfCovers`. -/
theorem zeroOfBase (h : CellQuiet ring S e e) (hb : (S e).top.wBase = .ZERO)
    (hz : ZeroDirty (S e)) : ((phiD ring S e) e).top.d = c.zeroDigit := by
  rw [writerBaseWrite ring S e h.li (h.ly rfl) hb]
  cases hod : (S e).top.topDirty with
  | true =>
    simp only [if_true]
    exact hz hod
  | false => simp

/-- **A zero digit stays zero under a quiet letter.**  Consumer: `firstBlockZeroOfCovers`. -/
theorem zeroKeep (h : CellQuiet ring S e i) (hz : (S i).top.d = c.zeroDigit) :
    ((phiD ring S e) i).top.d = c.zeroDigit := by
  rcases zeroCore h with hs | ⟨-, -, hb⟩
  · rw [hs, hz]
  · rw [hb]
    cases hod : (S i).top.topDirty with
    | true =>
      simp only [if_true]
      exact hz
    | false => simp

end Rows

section Boundary

variable {c : Compiled} {n : Nat} {ring : DirectedRing n}

/-- The left neighbour of a site.  Consumer: `boundaryCell`. -/
theorem leftOfSite (root e : Fin n) (hn : 2 ≤ n) (k : Nat) (hk : k < n)
    (h : digitSite ring root (k + 1) = ring.rightNeighbor e) (hk1 : k + 1 < n) :
    e = digitSite ring root k := by
  obtain ⟨j, hj, rfl⟩ := bankRepairDigitSiteSurj ring root e
  have hs : ring.rightNeighbor (digitSite ring root j) = digitSite ring root (j + 1) := rfl
  rw [hs] at h
  by_cases hjn : j + 1 < n
  · have := bankRepairDigitSiteInj ring root hk1 hjn h
    have hjk : j = k := by omega
    rw [hjk]
  · have hjE : j + 1 = n := by omega
    rw [hjE, bankRepairDigitSiteN ring root] at h
    have h0 : digitSite ring root 0 = root := rfl
    have := bankRepairDigitSiteInj ring root hk1 (show 0 < n by omega) (h.trans h0.symm)
    omega

/-- **The leading boundary makes every first-writable cell quiet at every letter.**  Consumer:
`firstBlockZeroOfCovers`. -/
theorem boundaryCell (root : Fin n) (hn : 2 ≤ n) (S : Fin n → ProjD c)
    (hroot : ∀ i, (S i).word.native.l = true ↔ i = root) (e : Fin n)
    (hbX : (pairW (S e).word (S (ring.rightNeighbor e)).word).1.beta = (S e).word.beta)
    (first stop : Nat) (hf2 : 2 ≤ first) (hseg : DigitFirstSegment ring root S first stop)
    (hlead : ∀ (lane : DigitLane) (k : Nat), 0 < k → k < first →
      (digitEndpointView lane S (digitSite ring root k)).carryLive = false)
    (hsegc : ∀ (lane : DigitLane) (k : Nat), first ≤ k → k < stop →
      DigitLastCarryInert n k (digitEndpointView lane S (digitSite ring root k)) ∨
        ((digitEndpointView lane S (digitSite ring root k)).carryLive = false ∧
          (if k = first then (digitEndpointView lane S (digitSite ring root k)).input = .E
           else DigitLeadingInput (digitEndpointView lane S (digitSite ring root k)).input)))
    (k : Nat) (hk1 : first ≤ k) (hk2 : k < stop) (hk3 : k + 1 < n) :
    CellQuiet ring S e (digitSite ring root k) := by
  have hne : ring.rightNeighbor e ≠ e := bankRepairDigitRightNe ring hn e
  have hnotroot : ∀ m, 0 < m → m < n → (S (digitSite ring root m)).word.native.l = false := by
    intro m h0 hm
    cases hl : (S (digitSite ring root m)).word.native.l with
    | false => rfl
    | true =>
      have := (hroot _).1 hl
      have h00 : digitSite ring root 0 = root := rfl
      have := bankRepairDigitSiteInj ring root hm (show 0 < n by omega) (this.trans h00.symm)
      omega
  refine ⟨hne, hnotroot k (by omega) (by omega), ?_, ?_, ?_⟩
  · intro hie
    have : ring.rightNeighbor e = digitSite ring root (k + 1) := by
      rw [← hie]
      rfl
    rw [this]
    exact hnotroot (k + 1) (by omega) hk3
  · intro hi cc hw
    have hk0 : 0 < k := by omega
    obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
    have hem := leftOfSite root e hn m (by omega) hi (by omega)
    subst hem
    have hlive : (digitEndpointView DigitLane.writer S (digitSite ring root m)).carryLive = true := by
      simp [digitEndpointView, digitLaneView, hw, WCarry.isW]
    rcases Nat.lt_or_ge m first with hm | hm
    · have := hlead DigitLane.writer m (by omega) hm
      rw [hlive] at this
      cases this
    · rcases hsegc DigitLane.writer m hm (by omega) with hin | ⟨hc, -⟩
      · have := hin.1
        omega
      · rw [hlive] at hc
        cases hc
  · intro hie hb hw v T hs
    subst hie
    rw [hbX] at hb
    have hkf : k = first := by
      obtain ⟨-, hlt, hle, -, hnone⟩ := hseg.2
      rcases Nat.lt_or_ge first k with h | h
      · have := hnone k h hk2
        rw [hb] at this
        cases this
      · omega
    subst hkf
    rcases hsegc DigitLane.writer k (Nat.le_refl _) hk2 with hin | ⟨-, hE⟩
    · have := hin.1
      omega
    · rw [if_pos rfl] at hE
      have hE' : (S (digitSite ring root k)).top.wIn = .E := by
        simpa [digitEndpointView, digitLaneView] using hE
      rw [hE'] at hs
      cases hs

/-- A proposal comes from a `ZERO` label.  Consumer: `firstBlockZeroOfCovers`. -/
theorem proposalBase (time : Nat) (source dest : Fin n) (x y : ProjD c) (b : Bool)
    (gx gy : Option (DigitBaseOrigin n)) (p : DigitZeroProposal n)
    (h : (digitBaseReplay time source dest x y b gx gy).proposal = some p) :
    x.top.wBase = .ZERO := by
  unfold digitBaseReplay at h
  simp only at h
  split at h
  · simp at h
  · split at h
    · simp at h
    · split at h
      · rename_i hz
        simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at hz
        exact hz.2
      · split at h <;> simp at h

end Boundary

variable {n : Nat} {ring : DirectedRing n} (ref : WidthBoundaryReference ring) (hn : 5 ≤ n)

/-- The state of the audit at a time of a `DigitAt` is the state of the run.  Consumer:
`firstBlockZeroOfCovers`. -/
theorem digitAtState (start : ref.State) (hst : ref.start start) (w : List (Fin n)) (cut : Nat)
    (S : Fin n → ProjD (compileAdvice (ceilLogTwo n)))
    (G : Fin n → DigitGhost (compileAdvice (ceilLogTwo n)) n)
    (h : DigitAt ring (w.foldl (widthDigitAuditNext ref.toWidthDigitReference)
      (start, digitAuditInitial (piD (ref.phys start)))).2 cut S G) :
    cut ≤ w.length ∧ S = piD (ref.phys (stateAt ref.toWidthDigitReference start w cut).1) := by
  rcases h with ⟨h0, hS, -⟩ | ⟨f, hf, h1, h2, -⟩
  · refine ⟨by omega, ?_⟩
    subst h0
    rw [hS, L3.WriterReceipts.widthAuditStartFold]
    rfl
  · obtain ⟨-, f2, -, f4⟩ := frameLink ref.toWidthDigitReference start w
      (ref.startDrained start hst) f hf
    subst h1
    exact ⟨f2, by rw [h2, f4]⟩

/-- The layout class along the run.  Consumer: `firstBlockZeroOfCovers`. -/
theorem layoutAt (start : ref.State) (w : List (Fin n)) (root : Fin n)
    (h0 : WidthDigitLayoutFixed ref.toWidthDigitReference root start) (k : Nat) (hk : k ≤ w.length) :
    WidthDigitLayoutFixed ref.toWidthDigitReference root
      (stateAt ref.toWidthDigitReference start w k).1 := by
  induction k with
  | zero => exact h0
  | succ k ih =>
    obtain ⟨e, he⟩ := stateStep ref.toWidthDigitReference start w k (by omega)
    rw [he]
    exact widthBoundaryDigitLayoutFixedStep ref root _ (ih (by omega)) e

include hn in
/-- One letter from a layout state, in the projected ring: the visible bits are fixed.  Consumer:
`firstBlockZeroOfCovers`. -/
theorem layoutLetter (root : Fin n) (z : ref.State)
    (hz : WidthDigitLayoutFixed ref.toWidthDigitReference root z) (e : Fin n) :
    (pairW (piD (ref.phys z) e).word (piD (ref.phys z) (ring.rightNeighbor e)).word).1.beta =
        (piD (ref.phys z) e).word.beta ∧
      (pairW (piD (ref.phys z) e).word (piD (ref.phys z) (ring.rightNeighbor e)).word).2.beta =
        (piD (ref.phys z) (ring.rightNeighbor e)).word.beta ∧
      (∀ i, (piD (ref.phys z) i).word.native.l = true ↔ i = root) := by
  have hnb := (AcceptedReceipts.qword_step ring _ hz.2 e).1
  have hvis : ∀ i, AcceptedReceipts.wordVisible (phiW ring (piW (ref.phys z)) e) i =
      AcceptedReceipts.wordVisible (piW (ref.phys z)) i := by
    intro i
    exact Classical.byContradiction (fun hne => hnb ⟨i, hne⟩)
  have hne : ring.rightNeighbor e ≠ e := bankRepairDigitRightNe ring (by omega) e
  have hbX := congrArg Prod.snd (hvis e)
  have hbY := congrArg Prod.snd (hvis (ring.rightNeighbor e))
  simp only [AcceptedReceipts.wordVisible, phiW, projectedEdge, if_pos rfl,
    if_neg hne] at hbX hbY
  refine ⟨hbX, hbY, fun i => ⟨fun hi => (ref.singletonFixed root z hz.1).2.1 i hi, ?_⟩⟩
  rintro rfl
  exact (ref.singletonFixed i z hz.1).1

include hn in
/-- The leading boundary is kept by a letter from a layout state.  Consumer:
`firstBlockZeroOfCovers`. -/
theorem boundaryLetter (root : Fin n) (z : ref.State)
    (hz : WidthDigitLayoutFixed ref.toWidthDigitReference root z) (e : Fin n)
    (h : DigitLeadingBoundary ring root (piD (ref.phys z))) :
    DigitLeadingBoundary ring root (piD (ref.phys (ref.next z e))) :=
  widthBoundaryDigitBankStepOf ref hn root (DigitLeadingBoundary ring root)
    (fun S e hroot hbX hbY h => bankRepairDigitLeadingStep ring (by omega) root S e
      (bankRepairDigitLaneRowFactsHold _) hroot hbX hbY h) z hz e h

include hn in
/-- The delimiters are kept by a letter from a layout state.  Consumer: `firstBlockZeroOfCovers`. -/
theorem betaLetter (root : Fin n) (z : ref.State)
    (hz : WidthDigitLayoutFixed ref.toWidthDigitReference root z) (e i : Fin n) :
    (piD (ref.phys (ref.next z e)) i).word.beta = (piD (ref.phys z) i).word.beta := by
  rw [ref.digitStep z (ref.singletonDrained root z hz.1) e]
  obtain ⟨hbX, hbY, -⟩ := layoutLetter ref hn root z hz e
  exact (bankRepairDigitPhiDAt ring (by omega) _ e hbX hbY).2.2.2 i

/-- The first segment depends only on the delimiters.  Consumer: `firstBlockZeroOfCovers`. -/
theorem segmentCongr {c : Compiled} {S T : Fin n → ProjD c} (root : Fin n)
    (hb : ∀ i, (S i).word.beta = (T i).word.beta) {first stop : Nat}
    (h : DigitFirstSegment ring root S first stop) : DigitFirstSegment ring root T first stop := by
  obtain ⟨⟨⟨h0, h1, h2⟩, h3⟩, ⟨h4, h5, h6⟩, h7, h8, h9, h10⟩ := h
  refine ⟨⟨⟨h0, h1, by rw [← hb]; exact h2⟩, fun k a b' => by rw [← hb]; exact h3 k a b'⟩,
    ⟨h4, h5, by rw [← hb]; exact h6⟩, h7, h8, fun a => by rw [← hb]; exact h9 a,
    fun k a b' => by rw [← hb]; exact h10 k a b'⟩

/-- The stop of a first segment is unique.  Consumer: `firstBlockZeroOfCovers`. -/
theorem stopUnique {c : Compiled} {S : Fin n → ProjD c} (root : Fin n) {first stop stop' : Nat}
    (h : DigitFirstSegment ring root S first stop) (h' : DigitFirstSegment ring root S first stop') :
    stop = stop' := by
  obtain ⟨-, -, a1, a2, a3, a4⟩ := h
  obtain ⟨-, -, b1, b2, b3, b4⟩ := h'
  rcases Nat.lt_trichotomy stop stop' with hl | he | hl
  · have := b4 stop a1 hl
    rw [a3 (by omega)] at this
    cases this
  · exact he
  · have := a4 stop' b1 hl
    rw [b3 (by omega)] at this
    cases this

include hn in
/-- **The first block holds zero from the base value cut on.**  Consumer: `quietOfCut`. -/
theorem firstBlockZeroOfCovers (start : ref.State) (hst : ref.start start) (w : List (Fin n))
    (root : Fin n) (hs : ref.singleton root start) (first stop retired baseCut : Nat)
    (hseg : DigitFirstSegment ring root (piD (ref.phys start)) first stop)
    (hbd : DigitBoundaryAt ring root (w.foldl (widthDigitAuditNext ref.toWidthDigitReference)
      (start, digitAuditInitial (piD (ref.phys start)))).2 retired)
    (hcov : DigitTwoBaseCovers ring root (w.foldl (widthDigitAuditNext ref.toWidthDigitReference)
      (start, digitAuditInitial (piD (ref.phys start)))).2 0 retired baseCut) :
    FirstBlockZero ref start w root first stop baseCut := by
  intro k hk1 hk2 hk3 t ht1 ht2
  have hn2 : 2 ≤ n := by omega
  have hd : ref.toWidthDigitReference.drained start := ref.startDrained start hst
  obtain ⟨root0, hs0, hV⟩ := widthCleanBoundaryRoot ref start hst
  have hr : root = root0 :=
    (ref.singletonFixed root0 start hs0).2.1 root (ref.singletonFixed root start hs).1
  subst hr
  obtain ⟨f0, htf, hft, hb0⟩ := widthCleanBoundaryDelimiters ref hn root start hV
  have ht2' := compileAdvice_t_ge_two (ceilLogTwo n) (ringQ_facts n hn).1
  have hff : first = f0 := by
    have hf := hseg.1
    have h1 := ((hb0 first hf.1.1 hf.1.2.1).1 hf.1.2.2).1
    rcases Nat.lt_or_ge f0 first with h | h
    · have h2 := hf.2 f0 (by omega) h
      have h3 := (hb0 f0 (by omega) (by omega)).2 ⟨Nat.le_refl _, by simp⟩
      rw [h2] at h3
      cases h3
    · omega
  subst hff
  have hf2 : 2 ≤ first := by omega
  have hlay := layoutAt ref start w root hV.1
  have hbeta : ∀ m, m ≤ w.length → ∀ i,
      (piD (ref.phys (stateAt ref.toWidthDigitReference start w m).1) i).word.beta =
        (piD (ref.phys start) i).word.beta := by
    intro m
    induction m with
    | zero => intro _ _; rfl
    | succ m ih =>
      intro hm i
      obtain ⟨e, he⟩ := stateStep ref.toWidthDigitReference start w m (by omega)
      rw [he]
      exact (betaLetter ref hn root _ (hlay m (by omega)) e i).trans (ih (by omega) i)
  obtain ⟨S, G, hat, hrec⟩ := hbd
  obtain ⟨hrle, hSeq⟩ := digitAtState ref start hst w retired S G hat
  have hLB : ∀ d, retired + d ≤ w.length → DigitLeadingBoundary ring root
      (piD (ref.phys (stateAt ref.toWidthDigitReference start w (retired + d)).1)) := by
    intro d
    induction d with
    | zero =>
      intro _
      rw [Nat.add_zero, ← hSeq]
      exact hrec.1
    | succ d ih =>
      intro hm
      obtain ⟨e, he⟩ := stateStep ref.toWidthDigitReference start w (retired + d) (by omega)
      rw [← Nat.add_assoc, he]
      exact boundaryLetter ref hn root _ (hlay _ (by omega)) e (ih (by omega))
  -- the cell is quiet at every letter from the retirement on
  have hq : ∀ m e, retired ≤ m → m < w.length → CellQuiet ring
      (piD (ref.phys (stateAt ref.toWidthDigitReference start w m).1)) e
      (digitSite ring root k) := by
    intro m e h1 h2
    have hB := hLB (m - retired) (by omega)
    rw [show retired + (m - retired) = m by omega] at hB
    obtain ⟨f', s', hseg', hlead', hsegc'⟩ := hB
    have hsegS := segmentCongr root (hbeta m (by omega)) hseg'
    have hff' : f' = first := L3.ValueWaveClose.firstDelimUnique ring root _ hsegS.1 hseg.1
    subst hff'
    have hss' : s' = stop := stopUnique root hsegS hseg
    subst hss'
    obtain ⟨hbX, -, hroot⟩ := layoutLetter ref hn root _ (hlay m (by omega)) e
    exact boundaryCell root hn2 _ hroot e hbX f' s' hf2 hseg'
      (fun lane k' h0 hk' => (hlead' lane k' h0 hk').2.1)
      (fun lane k' h0 hk' => hsegc' lane k' h0 hk') k hk1 hk2 hk3
  -- the two proposals at the cell
  obtain ⟨-, -, -, hrest⟩ := hcov
  have hstartA : (w.foldl (widthDigitAuditNext ref.toWidthDigitReference)
      (start, digitAuditInitial (piD (ref.phys start)))).2.start = piD (ref.phys start) :=
    L3.WriterReceipts.widthAuditStartFold ref.toWidthDigitReference w _
  have hwrit : DigitFirstWritable ring root
      (w.foldl (widthDigitAuditNext ref.toWidthDigitReference)
        (start, digitAuditInitial (piD (ref.phys start)))).2.start (digitSite ring root k) := by
    rw [hstartA]
    exact ⟨first, stop, k, hseg, hk1, hk2, hk3, rfl⟩
  rcases hrest with hno | ⟨b1, b2, l1, l2, c1, c2, -, -, -, -, -, -, hprop⟩
  · exact absurd hwrit (hno _)
  obtain ⟨p1, p2, hc1, hc2, hlt⟩ := hprop _ hwrit
  have hinv := (auditCarryInv_fold ref.toWidthDigitReference w
    (start, digitAuditInitial (piD (ref.phys start))) hd (auditCarryInv_initial ring _)).2
  have hprp : ∀ p : DigitZeroProposal n, DigitActualZeroProposal
      (w.foldl (widthDigitAuditNext ref.toWidthDigitReference)
        (start, digitAuditInitial (piD (ref.phys start)))).2 p → p.site = digitSite ring root k →
      1 ≤ p.time ∧ p.time ≤ w.length ∧
      (piD (ref.phys (stateAt ref.toWidthDigitReference start w (p.time - 1)).1)
        (digitSite ring root k)).top.wBase = .ZERO ∧
      piD (ref.phys (stateAt ref.toWidthDigitReference start w p.time).1) =
        phiD ring (piD (ref.phys (stateAt ref.toWidthDigitReference start w (p.time - 1)).1))
          (digitSite ring root k) := by
    rintro p ⟨f, hf, hfp, hft, hfs⟩ hsite
    obtain ⟨f1, f2, f3, f4⟩ := frameLink ref.toWidthDigitReference start w hd f hf
    have hre := (hinv.2 f hf).2
    rw [hre] at hfp
    have hb : (f.old f.edge).top.wBase = .ZERO := proposalBase _ _ _ _ _ _ _ _ _ hfp
    have hedge : f.edge = digitSite ring root k := hfs.symm.trans hsite
    rw [hedge, f3, ← hft] at hb
    rw [← hft] at f1 f2 f3 f4
    rw [f3, hedge] at f4
    exact ⟨f1, f2, hb, f4⟩
  obtain ⟨t1a, t1b, t1z, t1n⟩ := hprp p1 hc1.1 hc1.2.1
  obtain ⟨t2a, t2b, t2z, t2n⟩ := hprp p2 hc2.1 hc2.2.1
  have hr1 := hc1.2.2.1
  have hr2 := hc2.2.2.1
  have hc2t := hc2.2.2.2.1
  have hDZ : ∀ d, p1.time + d ≤ w.length →
      ZeroDirty (piD (ref.phys (stateAt ref.toWidthDigitReference start w (p1.time + d)).1)
        (digitSite ring root k)) := by
    intro d
    induction d with
    | zero =>
      intro _
      rw [Nat.add_zero, t1n]
      exact zeroDirtyOfBase (hq (p1.time - 1) _ (by omega) (by omega)) t1z
    | succ d ih =>
      intro hm
      obtain ⟨e, he⟩ := digitPhi ref.toWidthDigitReference start w hd (p1.time + d) (by omega)
      rw [← Nat.add_assoc, he]
      exact zeroDirtyStep (hq _ e (by omega) (by omega)) (ih (by omega))
  have hZ : ∀ d, p2.time + d ≤ w.length →
      (piD (ref.phys (stateAt ref.toWidthDigitReference start w (p2.time + d)).1)
        (digitSite ring root k)).top.d = (compileAdvice (ceilLogTwo n)).zeroDigit := by
    intro d
    induction d with
    | zero =>
      intro _
      rw [Nat.add_zero, t2n]
      have hdz := hDZ (p2.time - 1 - p1.time) (by omega)
      rw [show p1.time + (p2.time - 1 - p1.time) = p2.time - 1 by omega] at hdz
      exact zeroOfBase (hq (p2.time - 1) _ (by omega) (by omega)) t2z hdz
    | succ d ih =>
      intro hm
      obtain ⟨e, he⟩ := digitPhi ref.toWidthDigitReference start w hd (p2.time + d) (by omega)
      rw [← Nat.add_assoc, he]
      exact zeroKeep (hq _ e (by omega) (by omega)) (ih (by omega))
  have := hZ (t - p2.time) (by omega)
  rw [show p2.time + (t - p2.time) = t by omega] at this
  exact this

end L3.QuietEntryValues

#print axioms L3.QuietEntryValues.zeroCore
#print axioms L3.QuietEntryValues.boundaryCell
#print axioms L3.QuietEntryValues.firstBlockZeroOfCovers
