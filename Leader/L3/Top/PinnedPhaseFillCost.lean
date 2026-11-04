import Leader.L3.Top.PinnedPhaseFillPort

/-!
# Q7 (P.12 preparation, lemma 3): the fill stage costs at most `n * (2 r^2 + 4 r + 2)`

From a pinned labelled state whose window holds only empty, pending and settled non-tail
packets, a settled tail forms (a misplaced cut away from the border, an aligned window at the
border) within `n * (2 r^2 + 4 r + 2)`.

Consumer: `Leader/L3/TopPinnedPhaseFill.lean`.
-/

namespace L3
namespace MarkedCells

open Classical
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

set_option autoImplicit false
set_option linter.unusedSimpArgs false

/-- The pending weight only reads the first `r` registers.

Consumer: `fillPhi_congr`. -/
theorem fwAll_congr (r : Nat) (c c' : Nat → Cell) (h : ∀ j, j < r → c j = c' j) :
    fwAll r c = fwAll r c' := by
  unfold fwAll
  apply wsum_congr
  intro k hk
  simp [fwt, h k hk]

/-- The first pending tail only reads the first `r` registers.

Consumer: `fillPhi_congr`. -/
theorem fpos_congr' (r : Nat) (c c' : Nat → Cell) (h : ∀ j, j < r → c j = c' j) :
    fpos r c = fpos r c' := by
  unfold fpos
  apply firstS_congr
  intro k hk
  simp [h k hk]

/-- The weight from the first pending tail only reads the first `r` registers.

Consumer: `fillPhi_congr`. -/
theorem fwPt_congr (r : Nat) (c c' : Nat → Cell) (h : ∀ j, j < r → c j = c' j) :
    fwPt r c = fwPt r c' := by
  unfold fwPt
  rw [fpos_congr' r c c' h]
  apply wsum_congr
  intro k hk
  simp [fwt, h k hk]

/-- The potential only reads the first `r` registers and tokens.

Consumer: `fill_cost_row`. -/
theorem fillPhi_congr (r : Nat) (c c' : Nat → Cell) (src src' : Nat → Tok) (a : Nat)
    (hc : ∀ j, j < r → c j = c' j) (hs : ∀ i, i < r → src i = src' i) :
    fillPhi r c src a = fillPhi r c' src' a := by
  unfold fillPhi
  rw [fcnt_congr r c c' hc, fwAll_congr r c c' hc, fwPt_congr r c c' hc, dist_congr r src src' hs]

/-- The fill shape only reads the first `r` registers.

Consumer: `fill_cost_row`. -/
theorem fillShape_congr (r : Nat) (c c' : Nat → Cell) (h : ∀ j, j < r → c j = c' j)
    (hs : FillShape r c) : FillShape r c' := by
  obtain ⟨m, hm, hreg, hblk⟩ := hs
  refine ⟨m, hm, ?_, ?_⟩
  · intro j hj; rw [← h j (by omega)]; exact hreg j hj
  · intro j hj1 hj2; rw [← h j hj2]; exact hblk j hj1 hj2

/-- The exit shape only reads the first `r` registers.

Consumer: `fill_cost_row`. -/
theorem exitShape_congr (r : Nat) (c c' : Nat → Cell) (h : ∀ j, j < r → c j = c' j) (h0 : Nat)
    (hs : ExitShape r c h0) : ExitShape r c' h0 := by
  obtain ⟨hh, hl, hm, hr⟩ := hs
  refine ⟨hh, ?_, ?_, ?_⟩
  · intro j hj; rw [← h j (by omega)]; exact hl j hj
  · rw [← h h0 (by omega)]; exact hm
  · intro j hj1 hj2; rw [← h j hj2]; exact hr j hj1 hj2

/-- A fill window has no front and no live carry.

Consumer: `fill_cost_row`. -/
theorem puFree_of_fill {r : Nat} {c : Nat → Cell} (hs : FillShape r c) : puFree r c := by
  intro j hj
  have hk := fill_kind hs j hj
  refine ⟨hk.1, ?_⟩
  rcases hk.2 with h | h | h | h <;> rw [h] <;> decide

/-- An exit window has no front and no live carry.

Consumer: `fill_cost_row`. -/
theorem puFree_of_exit {r : Nat} {c : Nat → Cell} {h0 : Nat} (hs : ExitShape r c h0) :
    puFree r c := by
  intro j hj
  obtain ⟨hh, hl, hm, hr⟩ := hs
  by_cases h1 : j < h0
  · refine ⟨(hl j h1).1, ?_⟩
    rcases (hl j h1).2 with h | h | h <;> rw [h] <;> decide
  · by_cases h2 : j = h0
    · subst h2; rw [hm]; simp
    · rw [hr j (by omega) hj]; simp

/-- **The pinned labelled state with respect to a fixed permanent cut.**

Consumer: `topFillStage`. -/
def PuPinAt {n : Nat} (ring : DirectedRing n) (C : HeadlineConfiguration n) (s : Fin n)
    (Y0 Z : TopFixedTraceState n) : Prop :=
  topFreshTailPermanentCut ring C s Y0 ∧ MarkedFrom ring C Y0 Z ∧
    topClockNoOldPending s Z Y0.1.2.clock ∧ PuLinv s Z Y0.1.2.clock ∧ PuAllAt s Z Y0.1.2.clock

/-- A labelled state with respect to a cut is a pinned labelled state.

Consumer: `topFillStage`. -/
theorem pupin_of_at {n : Nat} {ring : DirectedRing n} {C : HeadlineConfiguration n} {s : Fin n}
    {Y0 Z : TopFixedTraceState n} (h : PuPinAt ring C s Y0 Z) : PuPin ring C s Z :=
  ⟨Y0, h⟩

/-- **A letter keeps the labelled state** when the successor window is free.

Consumer: `fill_cost_row`. -/
theorem pupinAt_next {n : Nat} (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (s : Fin n) (hg : WinGeo ring C s) (Y0 Y : TopFixedTraceState n) (e : Fin n)
    (hP : PuPinAt ring C s Y0 Y)
    (hfree : puFree (topClockSpan n) (cellOf s (topFixedTraceNext ring C Y e))) :
    PuPinAt ring C s Y0 (topFixedTraceNext ring C Y e) := by
  obtain ⟨hcut, hfrom, hold, hl, ha⟩ := hP
  have hreach : topClockReached ring C Y := markedFrom_reached ring C Y0 Y hfrom
  have hclock : Y0.1.2.clock ≤ Y.1.2.clock := markedFrom_clock ring C Y0 Y hcut.1 hfrom
  have hfrom' := markedFrom_next ring C Y0 Y e hfrom
  have hnone := pinned_hnone ring C s Y0 _ hcut hfrom'
  exact ⟨hcut, hfrom', noOld_next ring C s hg Y0.1.2.clock Y hreach hclock e hold,
    pulinv_step ring C s hg _ Y hreach hclock e hnone hfree hl,
    pulinv_all_step ring C s hg _ Y hreach hclock e hnone hfree hl ha⟩

/-- A cell `{e, off}` at the border means the border accepts.

Consumer: `fill_cost_row`. -/
theorem accOf_of_cell {n : Nat} (s : Fin n) (Z : TopFixedTraceState n)
    (h : cellOf s Z 0 = { i := .e, c := .off }) : accOf s Z = true := by
  unfold accOf
  unfold cellOf siteCell at h
  have h1 := congrArg Cell.i h
  have h2 := congrArg Cell.c h
  simp only at h1 h2
  have h3 : (Z.1.1 (winSite s 0)).qCarry = .OFF := (absCar_off _ _).1 h2
  rcases hq : (Z.1.1 (winSite s 0)).qIn with _ | _ | ⟨v, t⟩ | ⟨v, t⟩ <;> rw [hq] at h1 <;>
    (try cases t) <;> simp [absIn] at h1
  rw [h3]; rfl

/-- **Every letter is a step of the fill regime.**

Consumer: `topFillStage`. -/
theorem fill_concrete_step {n : Nat} (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (s : Fin n) (hg : WinGeo ring C s) (Y0 Z : TopFixedTraceState n) (hP : PuPinAt ring C s Y0 Z)
    (hs : FillShape (topClockSpan n) (cellOf s Z)) (e : Fin n) :
    ∃ (c' : Nat → Cell) (src' : Nat → Tok) (a' : Nat),
      FillStep (topClockSpan n) (cellOf s Z) (srcOf s Z) (aOf s Z Y0.1.2.clock) c' src' a' ∧
      Realized ring C s Y0.1.2.clock Z e c' src' a' := by
  have hr3 := span_ge_three hg.hn
  obtain ⟨hcut, hfrom, hold, hl, ha⟩ := hP
  have hreach : topClockReached ring C Z := markedFrom_reached ring C Y0 Z hfrom
  have hclock : Y0.1.2.clock ≤ Z.1.2.clock := markedFrom_clock ring C Y0 Z hcut.1 hfrom
  obtain ⟨hreach0, hgen, anchor, hanchor, htime, hfuture⟩ := hcut
  have hpureZ : topClockConcretePureStream s Z anchor := by
    obtain ⟨w, hw⟩ := hfrom
    rw [hw]; exact hfuture w
  have hpureN : topClockConcretePureStream s (topFixedTraceNext ring C Z e) anchor := by
    obtain ⟨w, hw⟩ := markedFrom_next ring C Y0 Z e hfrom
    rw [hw]; exact hfuture w
  have hI := fillInv_of_pu s Z anchor hpureZ (by rw [htime]; exact hl) (by rw [htime]; exact ha) hs
  rw [htime] at hI
  have hle := hI.2
  by_cases hwin : ∃ p, p < topClockSpan n ∧ e = winSite s p
  · obtain ⟨p, hp, rfl⟩ := hwin
    by_cases hp1 : p + 1 < topClockSpan n
    · exact ⟨_, _, _, FillStep.edge p hp1, real_edge ring C s hg Z hreach _ hs p hp1⟩
    · have hpe : p = topClockSpan n - 1 := by omega
      subst hpe
      exact ⟨_, _, _, FillStep.term, real_term ring C s hg Z hreach _ hs hle⟩
  · by_cases hsrc : ∃ j, j < topClockSpan n ∧ e = certSite s j
    · obtain ⟨j, hj, rfl⟩ := hsrc
      by_cases hj1 : j + 1 < topClockSpan n
      · exact ⟨_, _, _, FillStep.srcEdge j hj1 (accOf s Z), real_src ring C s hg Z hreach _ j hj1⟩
      · have hje : j = topClockSpan n - 1 := by omega
        subst hje
        by_cases hDa : (srcOf s Z (topClockSpan n - 1)).isD = true ∧ accOf s Z = true
        · obtain ⟨hemp, t, ht, hreal⟩ := real_port_accept ring C s hg Z hreach
            Y0.1.2.clock hclock anchor htime hpureN hle hDa.1 hDa.2
          exact ⟨_, _, _, FillStep.accept t hemp hDa.1 ht, hreal⟩
        · refine ⟨_, _, _, FillStep.clean (accOf s Z) ?_, real_port_clean ring C s hg Z hreach _ hs hDa⟩
          intro hD
          cases hacc : accOf s Z
          · rfl
          · exact absurd ⟨hD, hacc⟩ hDa
    · refine ⟨_, _, _, FillStep.frame, real_frame ring C s hg Z hreach _ e ?_ ?_⟩
      · intro p hp h; exact hwin ⟨p, hp, h⟩
      · intro j hj h; exact hsrc ⟨j, hj, h⟩

/-- The potential of a state, with respect to a permanent cut.

Consumer: `topFillStage`. -/
noncomputable def fillPot {n : Nat} (s : Fin n) (τ : Nat) (Z : TopFixedTraceState n) : Nat :=
  fillPhi (topClockSpan n) (cellOf s Z) (srcOf s Z) (aOf s Z τ)

/-- The fill invariant of a pinned labelled state with the fill shape.

Consumer: `fill_row`. -/
theorem fillInv_at {n : Nat} (ring : DirectedRing n) (C : HeadlineConfiguration n) (s : Fin n)
    (Y0 Z : TopFixedTraceState n) (hP : PuPinAt ring C s Y0 Z)
    (hs : FillShape (topClockSpan n) (cellOf s Z)) :
    FillInv (topClockSpan n) (cellOf s Z) (aOf s Z Y0.1.2.clock) ∧
    aOf s Z Y0.1.2.clock < topClockSpan n := by
  obtain ⟨hcut, hfrom, hold, hl, ha⟩ := hP
  obtain ⟨hreach0, hgen, anchor, hanchor, htime, hfuture⟩ := hcut
  have hpureZ : topClockConcretePureStream s Z anchor := by
    obtain ⟨w, hw⟩ := hfrom
    rw [hw]; exact hfuture w
  have hI := fillInv_of_pu s Z anchor hpureZ (by rw [htime]; exact hl) (by rw [htime]; exact ha) hs
  rw [htime] at hI
  refine ⟨hI.1, ?_⟩
  unfold aOf
  apply Nat.mod_lt
  obtain ⟨m, hm, _⟩ := hs
  omega

/-- **One row of the fill stage**: every letter leaves the regime by a settled tail, or keeps it
without raising the potential.

Consumer: `topFillStage`. -/
theorem fill_row {n : Nat} (ring : DirectedRing n) (C : HeadlineConfiguration n) (s : Fin n)
    (hg : WinGeo ring C s) (Y0 Z : TopFixedTraceState n) (hP : PuPinAt ring C s Y0 Z)
    (hs : FillShape (topClockSpan n) (cellOf s Z)) (e : Fin n) :
    (PuPinAt ring C s Y0 (topFixedTraceNext ring C Z e) ∧
      ∃ h, ExitShape (topClockSpan n) (cellOf s (topFixedTraceNext ring C Z e)) h ∧
        h = aOf s Z Y0.1.2.clock ∧
        aOf s (topFixedTraceNext ring C Z e) Y0.1.2.clock = aOf s Z Y0.1.2.clock) ∨
    (PuPinAt ring C s Y0 (topFixedTraceNext ring C Z e) ∧
      FillShape (topClockSpan n) (cellOf s (topFixedTraceNext ring C Z e)) ∧
      fillPot s Y0.1.2.clock (topFixedTraceNext ring C Z e) ≤ fillPot s Y0.1.2.clock Z ∧
      (aOf s Z Y0.1.2.clock ≠ topClockSpan n - 1 →
        aOf s (topFixedTraceNext ring C Z e) Y0.1.2.clock = aOf s Z Y0.1.2.clock)) := by
  have hr3 := span_ge_three hg.hn
  obtain ⟨c', src', a', hstep, hreal⟩ := fill_concrete_step ring C s hg Y0 Z hP hs e
  obtain ⟨hFI, haL⟩ := fillInv_at ring C s Y0 Z hP hs
  rcases fill_step (topClockSpan n) hr3 (cellOf s Z) (srcOf s Z) _ haL hFI hstep with
    ⟨j, hj, hex, hja, haa⟩ | ⟨ha', hFI', hle, hkeep⟩
  · left
    have hex' := exitShape_congr (topClockSpan n) c' _ (fun i hi => (hreal.1 i hi).symm) j hex
    exact ⟨pupinAt_next ring C s hg Y0 Z e hP (puFree_of_exit hex'), j, hex', hja,
      by rw [hreal.2.2, haa]⟩
  · right
    have hs' := fillShape_congr (topClockSpan n) c' _ (fun i hi => (hreal.1 i hi).symm) hFI'.1
    refine ⟨pupinAt_next ring C s hg Y0 Z e hP (puFree_of_fill hs'), hs', ?_, ?_⟩
    · unfold fillPot
      rw [fillPhi_congr _ _ c' _ src' _ hreal.1 hreal.2.1, hreal.2.2]
      exact hle
    · intro hne
      rw [hreal.2.2]
      exact hkeep hne

/-- The anchor facts of a pinned labelled state.

Consumer: `fill_drop`. -/
theorem pin_facts {n : Nat} (ring : DirectedRing n) (C : HeadlineConfiguration n) (s : Fin n)
    (Y0 Z : TopFixedTraceState n) (hP : PuPinAt ring C s Y0 Z)
    (hs : FillShape (topClockSpan n) (cellOf s Z)) (e : Fin n) :
    ∃ anchor : DigitExport (compileAdvice (ceilLogTwo n)) n,
      anchor.time = Y0.1.2.clock ∧
      topClockConcretePureStream s (topFixedTraceNext ring C Z e) anchor ∧
      Y0.1.2.clock ≤ Z.1.2.clock ∧ topClockReached ring C Z ∧
      fcnt (topClockSpan n) (cellOf s Z) ≤ (paQ s Z Y0.1.2.clock).length := by
  obtain ⟨hcut, hfrom, hold, hl, ha⟩ := hP
  have hreach : topClockReached ring C Z := markedFrom_reached ring C Y0 Z hfrom
  have hclock : Y0.1.2.clock ≤ Z.1.2.clock := markedFrom_clock ring C Y0 Z hcut.1 hfrom
  obtain ⟨hreach0, hgen, anchor, hanchor, htime, hfuture⟩ := hcut
  have hpureZ : topClockConcretePureStream s Z anchor := by
    obtain ⟨w, hw⟩ := hfrom
    rw [hw]; exact hfuture w
  have hpureN : topClockConcretePureStream s (topFixedTraceNext ring C Z e) anchor := by
    obtain ⟨w, hw⟩ := markedFrom_next ring C Y0 Z e hfrom
    rw [hw]; exact hfuture w
  have hI := fillInv_of_pu s Z anchor hpureZ (by rw [htime]; exact hl) (by rw [htime]; exact ha) hs
  rw [htime] at hI
  exact ⟨anchor, htime, hpureN, hclock, hreach, hI.2⟩

/-- **The nominated letter of the fill stage.**

Consumer: `topFillStage`. -/
noncomputable def fillChosen {n : Nat} (s : Fin n) (Z : TopFixedTraceState n) : Fin n :=
  match lastP (cellOf s Z) (topClockSpan n) with
  | some q => winSite s q
  | none =>
      if dist (topClockSpan n) (srcOf s Z) = 0 then certSite s (topClockSpan n - 1)
      else certSite s (srcIdx (topClockSpan n) (srcOf s Z))

/-- **The nominated letter lowers the potential** (or forms the settled tail).

Consumer: `topFillStage`. -/
theorem fill_drop {n : Nat} (ring : DirectedRing n) (C : HeadlineConfiguration n) (s : Fin n)
    (hg : WinGeo ring C s) (Y0 Z : TopFixedTraceState n) (hP : PuPinAt ring C s Y0 Z)
    (hs : FillShape (topClockSpan n) (cellOf s Z)) :
    (PuPinAt ring C s Y0 (topFixedTraceNext ring C Z (fillChosen s Z)) ∧
      ∃ h, ExitShape (topClockSpan n)
        (cellOf s (topFixedTraceNext ring C Z (fillChosen s Z))) h ∧
        h = aOf s Z Y0.1.2.clock ∧
        aOf s (topFixedTraceNext ring C Z (fillChosen s Z)) Y0.1.2.clock =
          aOf s Z Y0.1.2.clock) ∨
    fillPot s Y0.1.2.clock (topFixedTraceNext ring C Z (fillChosen s Z)) + 1 ≤
      fillPot s Y0.1.2.clock Z := by
  have hr3 := span_ge_three hg.hn
  obtain ⟨hFI, haL⟩ := fillInv_at ring C s Y0 Z hP hs
  have hok : ∀ e, (∃ anchor : DigitExport (compileAdvice (ceilLogTwo n)) n,
      anchor.time = Y0.1.2.clock ∧
      topClockConcretePureStream s (topFixedTraceNext ring C Z e) anchor ∧
      Y0.1.2.clock ≤ Z.1.2.clock ∧ topClockReached ring C Z ∧
      fcnt (topClockSpan n) (cellOf s Z) ≤ (paQ s Z Y0.1.2.clock).length) :=
    fun e => pin_facts ring C s Y0 Z hP hs e
  obtain ⟨_, _, _, hclock, hreach, hle⟩ := hok (fillChosen s Z)
  -- exits transfer
  have hexit : ∀ (e : Fin n) (c' : Nat → Cell) (j : Nat) (a' : Nat),
      (∀ i, i < topClockSpan n → cellOf s (topFixedTraceNext ring C Z e) i = c' i) →
      aOf s (topFixedTraceNext ring C Z e) Y0.1.2.clock = a' →
      a' = aOf s Z Y0.1.2.clock →
      ExitShape (topClockSpan n) c' j → j = aOf s Z Y0.1.2.clock →
      (PuPinAt ring C s Y0 (topFixedTraceNext ring C Z e) ∧
        ∃ h, ExitShape (topClockSpan n) (cellOf s (topFixedTraceNext ring C Z e)) h ∧
          h = aOf s Z Y0.1.2.clock ∧
          aOf s (topFixedTraceNext ring C Z e) Y0.1.2.clock = aOf s Z Y0.1.2.clock) := by
    intro e c' j a' hc haa hapa hex hja
    have hex' := exitShape_congr (topClockSpan n) c' _ (fun i hi => (hc i hi).symm) j hex
    exact ⟨pupinAt_next ring C s hg Y0 Z e hP (puFree_of_exit hex'), j, hex', hja,
      by rw [haa, hapa]⟩
  rcases hq : lastP (cellOf s Z) (topClockSpan n) with _ | q
  · -- no pending packet
    have hnp := lastP_none (cellOf s Z) (topClockSpan n) hq
    by_cases hd : dist (topClockSpan n) (srcOf s Z) = 0
    · have hch : fillChosen s Z = certSite s (topClockSpan n - 1) := by
        unfold fillChosen; rw [hq]; simp [hd]
      rw [hch]
      obtain ⟨h0, _, hdrop⟩ := fill_port_accept (topClockSpan n) hr3 (cellOf s Z) (srcOf s Z) _
        haL hFI hnp hd
      have hD := (dist_zero_iff (topClockSpan n) (by omega) (srcOf s Z)).1 hd
      have hacc := accOf_of_cell s Z h0
      obtain ⟨anchor, hanch, hpureN, _, _, _⟩ := pin_facts ring C s Y0 Z hP hs
        (certSite s (topClockSpan n - 1))
      obtain ⟨hemp, t, ht, hreal⟩ := real_port_accept ring C s hg Z hreach Y0.1.2.clock hclock
        anchor hanch hpureN hle hD hacc
      right
      subst ht
      unfold fillPot
      rw [fillPhi_congr _ _ _ _ _ _ hreal.1 hreal.2.1, hreal.2.2]
      have hpa : setOne (cellOf s Z) 0 (portAccept
          (decide ((aOf s Z Y0.1.2.clock + fcnt (topClockSpan n) (cellOf s Z)) % topClockSpan n =
            topClockSpan n - 1)) (cellOf s Z 0)) =
          stC (cellOf s Z) 0 { i := (if decide ((aOf s Z Y0.1.2.clock +
            fcnt (topClockSpan n) (cellOf s Z)) % topClockSpan n = topClockSpan n - 1)
            then .pt else .pn), c := .off } := by
        unfold portAccept stC
        rw [if_pos hemp]
      rw [hpa]
      exact hdrop
    · have hch : fillChosen s Z = certSite s (srcIdx (topClockSpan n) (srcOf s Z)) := by
        unfold fillChosen; rw [hq]; simp [hd]
      rw [hch]
      obtain ⟨hjr, hdrop⟩ := fill_src_drop (topClockSpan n) hr3 (cellOf s Z) (srcOf s Z) _
        hFI hnp hd (accOf s Z)
      right
      by_cases hj1 : srcIdx (topClockSpan n) (srcOf s Z) + 1 < topClockSpan n
      · have hreal := real_src ring C s hg Z hreach Y0.1.2.clock
          (srcIdx (topClockSpan n) (srcOf s Z)) hj1
        unfold fillPot
        rw [fillPhi_congr _ _ _ _ _ _ hreal.1 hreal.2.1, hreal.2.2]
        exact hdrop
      · have hje : srcIdx (topClockSpan n) (srcOf s Z) = topClockSpan n - 1 := by omega
        rw [hje] at hdrop ⊢
        have hnot : ¬ ((srcOf s Z (topClockSpan n - 1)).isD = true ∧ accOf s Z = true) := by
          intro h
          exact hd ((dist_zero_iff (topClockSpan n) (by omega) (srcOf s Z)).2 h.1)
        have hreal := real_port_clean ring C s hg Z hreach Y0.1.2.clock hs hnot
        have hk0 := fill_kind hs 0 (by omega)
        have hcl : ∀ j, j < topClockSpan n →
            cellOf s (topFixedTraceNext ring C Z (certSite s (topClockSpan n - 1))) j =
              cellOf s Z j := by
          intro j hj
          rw [hreal.1 j hj]
          by_cases hj0 : j = 0
          · subst hj0; simp [setOne, pu_port_clean _ hk0.1]
          · simp [setOne, hj0]
        unfold fillPot
        rw [fillPhi_congr _ _ _ _ _ _ hcl hreal.2.1, hreal.2.2]
        exact hdrop
  · obtain ⟨hqr, hqP, hright⟩ := lastP_some _ _ _ hq
    have hch : fillChosen s Z = winSite s q := by
      unfold fillChosen; rw [hq]
    rw [hch]
    by_cases hq1 : q + 1 < topClockSpan n
    · have hreal := real_edge ring C s hg Z hreach Y0.1.2.clock hs q hq1
      rcases fill_win_edge (topClockSpan n) hr3 (cellOf s Z) (srcOf s Z) _ haL hFI q hq1 hqP
        hright with ⟨j, hj, hex, hja⟩ | ⟨_, hlt⟩
      · left; exact hexit _ _ j _ hreal.1 hreal.2.2 rfl hex hja
      · right
        unfold fillPot
        rw [fillPhi_congr _ _ _ _ _ _ hreal.1 hreal.2.1, hreal.2.2]
        exact hlt
    · have hqe : q = topClockSpan n - 1 := by omega
      subst hqe
      have hreal := real_term ring C s hg Z hreach Y0.1.2.clock hs hle
      obtain ⟨_, _, hlt⟩ := fill_win_term (topClockSpan n) hr3 (cellOf s Z) (srcOf s Z) _ haL
        hFI hqP
      right
      unfold fillPot
      rw [fillPhi_congr _ _ _ _ _ _ hreal.1 hreal.2.1, hreal.2.2]
      exact hlt

/-- A pointwise smaller weight has a smaller sum.

Consumer: `fillPot_le`. -/
theorem wsum_mono (f g : Nat → Nat) (h : ∀ k, f k ≤ g k) : ∀ a, wsum f a ≤ wsum g a
  | 0 => Nat.le_refl _
  | a + 1 => by
      have := wsum_mono f g h a
      have := h a
      simp only [wsum]
      omega

/-- The pending weight is at most `r` times the flag count.

Consumer: `fillPot_le`. -/
theorem fwAll_le (r : Nat) (c : Nat → Cell) : fwAll r c ≤ r * fcnt r c := by
  unfold fwAll fcnt
  have key : ∀ a, wsum (fwt r c) a ≤ r * wsum (fl c) a := by
    intro a
    induction a with
    | zero => simp [wsum]
    | succ a ih =>
        simp only [wsum]
        have h1 : fwt r c a ≤ r * fl c a := by
          unfold fwt fl
          by_cases hP : (c a).i.isP = true
          · have : puNonE (c a).i = true := by simp [puNonE, hP]
            simp [hP, this]
          · simp [hP]
        rw [Nat.mul_add]
        omega
  exact key r

/-- The weight from the pending tail on is at most the pending weight.

Consumer: `fillPot_le`. -/
theorem fwPt_le (r : Nat) (c : Nat → Cell) : fwPt r c ≤ fwAll r c := by
  unfold fwPt fwAll
  apply wsum_mono
  intro k
  by_cases h : fpos r c ≤ k <;> simp [h]

/-- **The potential is at most `2 r^2 + 4 r + 2`.**

Consumer: `topFillStage`. -/
theorem fillPot_le (r : Nat) (c : Nat → Cell) (src : Nat → Tok) (a : Nat) :
    fillPhi r c src a ≤ 2 * r * r + 4 * r + 2 := by
  have hw := fwAll_le r c
  have hd := dist_le r src
  have hp := fcnt_le r c
  unfold fillPhi
  by_cases h : fcnt r c ≤ ftail r a
  · rw [if_pos h]
    have ht : ftail r a ≤ r := by unfold ftail; split <;> omega
    obtain ⟨K, hK⟩ : ∃ K, ftail r a = fcnt r c + K := ⟨ftail r a - fcnt r c, by omega⟩
    have hK' : ftail r a - fcnt r c = K := by omega
    rw [hK']
    have h1 : r * fcnt r c ≤ (2 * r + 2) * fcnt r c := Nat.mul_le_mul_right _ (by omega)
    have h2 : K * (2 * r + 2) + fcnt r c * (2 * r + 2) = (fcnt r c + K) * (2 * r + 2) := by
      rw [Nat.add_mul]; omega
    have h3 : (fcnt r c + K) * (2 * r + 2) ≤ r * (2 * r + 2) := Nat.mul_le_mul_right _ (by omega)
    have h4 : (2 * r + 2) * fcnt r c = fcnt r c * (2 * r + 2) := Nat.mul_comm _ _
    have h5 : r * (2 * r + 2) = 2 * r * r + 2 * r := by
      rw [Nat.mul_add, Nat.mul_comm r (2 * r)]; omega
    omega
  · rw [if_neg h]
    have h1 := fwPt_le r c
    have h2 : r * fcnt r c ≤ r * r := Nat.mul_le_mul_left _ hp
    have h3 : r * r ≤ 2 * r * r := by
      have : 2 * r * r = r * r + r * r := by rw [Nat.mul_assoc, Nat.two_mul]
      omega
    omega

/-- **The fill stage**: from a pinned labelled state whose window has the fill shape, a settled
tail forms within mean `n * (2 r^2 + 4 r + 2)`.

Consumer: `Leader/L3/TopPinnedPhaseFill.lean`. -/
theorem topFillStage {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n) (C : HeadlineConfiguration n)
    (s : Fin n) (hl : ∀ i : Fin n, (C i).l = false)
    (hbad : HeadlineDigit.BadCompletePair C s) (Y0 Z0 : TopFixedTraceState n)
    (hP : PuPinAt ring C s Y0 Z0) (hs : FillShape (topClockSpan n) (cellOf s Z0)) :
    UniformFirstHit.ExpectedHittingTimeAtMost (topFixedTraceNext ring C)
      (fun Y => PuPinAt ring C s Y0 Y ∧ ∃ h, ExitShape (topClockSpan n) (cellOf s Y) h) Z0
      ((n * (2 * topClockSpan n * topClockSpan n + 4 * topClockSpan n + 2) : Nat) : Rat) := by
  classical
  have hg : WinGeo ring C s := ⟨hn, hl, hbad⟩
  have hn0 : 0 < n := by omega
  have hr3 := span_ge_three hn
  apply (UniformFirstHit.expectedHittingTimeAtMost_iff_cost (topFixedTraceNext ring C) _ hn0 Z0
    (n * (2 * topClockSpan n * topClockSpan n + 4 * topClockSpan n + 2))).2
  intro T
  let I : TopFixedTraceState n → Prop := fun Y =>
    PuPinAt ring C s Y0 Y ∧ (FillShape (topClockSpan n) (cellOf s Y) ∨
      ∃ h, ExitShape (topClockSpan n) (cellOf s Y) h)
  let P : TopFixedTraceState n → Prop := fun Y =>
    PuPinAt ring C s Y0 Y ∧ ∃ h, ExitShape (topClockSpan n) (cellOf s Y) h
  have hfill : ∀ x, I x → ¬ P x → FillShape (topClockSpan n) (cellOf s x) := by
    intro x hx hnot
    rcases hx.2 with hf | ⟨h, hex⟩
    · exact hf
    · exact absurd ⟨hx.1, h, hex⟩ hnot
  have hmain := topFinalCostOfRows (topFixedTraceNext ring C) I P (fillPot s Y0.1.2.clock)
    (fillChosen s)
    (by
      intro x hx hnot e
      have hf := hfill x hx hnot
      rcases fill_row ring C s hg Y0 x hx.1 hf e with ⟨h1, h2⟩ | ⟨h1, h2, _⟩
      · obtain ⟨h, hh, _⟩ := h2
        exact ⟨h1, Or.inr ⟨h, hh⟩⟩
      · exact ⟨h1, Or.inl h2⟩)
    (by
      intro x hx hnot
      have hf := hfill x hx hnot
      obtain ⟨hFI, haL⟩ := fillInv_at ring C s Y0 x hx.1 hf
      exact fill_pos (topClockSpan n) hr3 _ _ _ haL hFI)
    (by
      intro x hx hnot e
      have hf := hfill x hx hnot
      rcases fill_row ring C s hg Y0 x hx.1 hf e with h | ⟨_, _, h3, _⟩
      · obtain ⟨h1, h, hh, _⟩ := h
        exact Or.inl ⟨h1, h, hh⟩
      · exact Or.inr h3)
    (by
      intro x hx hnot
      have hf := hfill x hx hnot
      rcases fill_drop ring C s hg Y0 x hx.1 hf with h | h
      · obtain ⟨h1, h, hh, _⟩ := h
        exact Or.inl ⟨h1, h, hh⟩
      · exact Or.inr h)
    Z0 ⟨hP, Or.inl hs⟩ T
  have hb : fillPot s Y0.1.2.clock Z0 ≤
      2 * topClockSpan n * topClockSpan n + 4 * topClockSpan n + 2 := fillPot_le _ _ _ _
  exact Nat.le_trans hmain (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hb))

/-- **The aligned fill stage**: when the residue of the oldest outstanding serial is zero, the
settled tail forms at the border, i.e. an aligned window, within mean `n * (2 r^2 + 4 r + 2)`.

Consumer: `Leader/L3/Top/PinnedPhaseFavourable.lean`. -/
theorem topFillStageAligned {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (C : HeadlineConfiguration n) (s : Fin n) (hl : ∀ i : Fin n, (C i).l = false)
    (hbad : HeadlineDigit.BadCompletePair C s) (Y0 Z0 : TopFixedTraceState n)
    (hP : PuPinAt ring C s Y0 Z0) (hs : FillShape (topClockSpan n) (cellOf s Z0))
    (h0 : aOf s Z0 Y0.1.2.clock = 0) :
    UniformFirstHit.ExpectedHittingTimeAtMost (topFixedTraceNext ring C)
      (fun Y => PuPinAt ring C s Y0 Y ∧ ExitShape (topClockSpan n) (cellOf s Y) 0) Z0
      ((n * (2 * topClockSpan n * topClockSpan n + 4 * topClockSpan n + 2) : Nat) : Rat) := by
  classical
  have hg : WinGeo ring C s := ⟨hn, hl, hbad⟩
  have hn0 : 0 < n := by omega
  have hr3 := span_ge_three hn
  apply (UniformFirstHit.expectedHittingTimeAtMost_iff_cost (topFixedTraceNext ring C) _ hn0 Z0
    (n * (2 * topClockSpan n * topClockSpan n + 4 * topClockSpan n + 2))).2
  intro T
  let I : TopFixedTraceState n → Prop := fun Y =>
    PuPinAt ring C s Y0 Y ∧ aOf s Y Y0.1.2.clock = 0 ∧
      (FillShape (topClockSpan n) (cellOf s Y) ∨ ExitShape (topClockSpan n) (cellOf s Y) 0)
  let P : TopFixedTraceState n → Prop := fun Y =>
    PuPinAt ring C s Y0 Y ∧ ExitShape (topClockSpan n) (cellOf s Y) 0
  have hfill : ∀ x, I x → ¬ P x → FillShape (topClockSpan n) (cellOf s x) := by
    intro x hx hnot
    rcases hx.2.2 with hf | hex
    · exact hf
    · exact absurd ⟨hx.1, hex⟩ hnot
  have hmain := topFinalCostOfRows (topFixedTraceNext ring C) I P (fillPot s Y0.1.2.clock)
    (fillChosen s)
    (by
      intro x hx hnot e
      have hf := hfill x hx hnot
      have hnr : aOf s x Y0.1.2.clock ≠ topClockSpan n - 1 := by rw [hx.2.1]; omega
      rcases fill_row ring C s hg Y0 x hx.1 hf e with ⟨h1, h, hh, hja, haa⟩ | ⟨h1, h2, _, hkeep⟩
      · have hh0 : h = 0 := by rw [hja, hx.2.1]
        subst hh0
        exact ⟨h1, by rw [haa, hx.2.1], Or.inr hh⟩
      · exact ⟨h1, by rw [hkeep hnr, hx.2.1], Or.inl h2⟩)
    (by
      intro x hx hnot
      have hf := hfill x hx hnot
      obtain ⟨hFI, haL⟩ := fillInv_at ring C s Y0 x hx.1 hf
      exact fill_pos (topClockSpan n) hr3 _ _ _ haL hFI)
    (by
      intro x hx hnot e
      have hf := hfill x hx hnot
      rcases fill_row ring C s hg Y0 x hx.1 hf e with ⟨h1, h, hh, hja, haa⟩ | ⟨_, _, h3, _⟩
      · have hh0 : h = 0 := by rw [hja, hx.2.1]
        subst hh0
        exact Or.inl ⟨h1, hh⟩
      · exact Or.inr h3)
    (by
      intro x hx hnot
      have hf := hfill x hx hnot
      rcases fill_drop ring C s hg Y0 x hx.1 hf with ⟨h1, h, hh, hja, haa⟩ | h
      · have hh0 : h = 0 := by rw [hja, hx.2.1]
        subst hh0
        exact Or.inl ⟨h1, hh⟩
      · exact Or.inr h)
    Z0 ⟨hP, h0, Or.inl hs⟩ T
  have hb : fillPot s Y0.1.2.clock Z0 ≤
      2 * topClockSpan n * topClockSpan n + 4 * topClockSpan n + 2 := fillPot_le _ _ _ _
  exact Nat.le_trans hmain (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hb))

end MarkedCells
end L3

#print axioms L3.MarkedCells.topFillStageAligned

#print axioms L3.MarkedCells.fill_concrete_step
#print axioms L3.MarkedCells.fill_row
#print axioms L3.MarkedCells.fill_drop
