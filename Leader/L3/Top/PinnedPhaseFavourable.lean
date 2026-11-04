import Leader.L3.Top.PinnedPhaseAssemble
import Leader.L3.Top.PinnedPhaseCount

/-!
# Q7 (P.12--P.13 favourable): the pending suffix is aligned after the front clears

At a misplaced cut with the settled bookkeeping the accepted queue has `|Q| = (number of pending
registers) + r * m` (the pending reading starts at the serial after the tail, which is `0 mod r`).
The front clearing stage keeps `|Q| - (number of pending registers)`, so at the first cleared
window the residue `aOf` is zero and the fill stage ends aligned.

Consumer: `topStopFavourablePhase`.
-/

namespace L3
namespace MarkedCells

open Classical
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

set_option autoImplicit false
set_option linter.unusedSimpArgs false

/-- A sum that vanishes from `h` on stops at `h`.

Consumer: `misplaced_count`. -/
theorem wsum_stop (f : Nat → Nat) (h : Nat) :
    ∀ r, h ≤ r → (∀ k, h ≤ k → k < r → f k = 0) → wsum f r = wsum f h := by
  intro r
  induction r with
  | zero => intro h1 _; have : h = 0 := by omega
            subst this; rfl
  | succ r ih =>
      intro h1 hz
      by_cases hh : h = r + 1
      · subst hh; rfl
      · simp only [wsum]
        rw [ih (by omega) (fun k hk1 hk2 => hz k hk1 (by omega)), hz r (by omega) (by omega)]
        rfl

/-- **A misplaced labelled cut has `|Q| = pending + r * m`.**

Consumer: `favourable_count`. -/
theorem misplaced_count {n : Nat} (s : Fin n) (Y : TopFixedTraceState n)
    (anchor : DigitExport (compileAdvice (ceilLogTwo n)) n)
    (hpure : topClockConcretePureStream s Y anchor)
    (hinv : PuLinv s Y anchor.time) (hall : PuAllAt s Y anchor.time)
    (h : Nat) (hh1 : 1 ≤ h) (hh2 : h + 1 < topClockSpan n)
    (hleft : ∀ j, j < h → (cellOf s Y j).i = .e ∨ (cellOf s Y j).i = .pt ∨ (cellOf s Y j).i = .pn)
    (htail : (cellOf s Y h).i = .st)
    (hright : ∀ j, h < j → j < topClockSpan n → (cellOf s Y j).i = .sn) :
    ∃ m, (paQ s Y anchor.time).length = pendCnt (topClockSpan n) (cellOf s Y) +
      topClockSpan n * m := by
  obtain ⟨hfree, hI, k0, hk0, hlist⟩ := hinv
  have hr : 3 ≤ topClockSpan n := by omega
  have hnonE : ∀ j, h ≤ j → j < topClockSpan n → puNonE (cellOf s Y j).i = true := by
    intro j h1 h2
    by_cases hjh : j = h
    · subst hjh; rw [htail]; rfl
    · rw [hright j (by omega) h2]; rfl
  have hflag : ∀ j, h ≤ j → j < topClockSpan n → paFlagSettled s Y anchor.time j = true :=
    fun j h1 h2 => hall j h2 (hnonE j h1 h2)
  have hsamp := labelled_sample s Y anchor hpure k0 hlist h hflag h (Nat.le_refl _) (by omega)
  obtain ⟨sT, hrecT, hlaneT, hsiteT, htailT, hatomT, htokT⟩ := hsamp
  obtain ⟨vT, hqT⟩ := (qIn_of_cell s Y h).1 htail
  have hsT : sT.tail = true := by
    rw [hqT] at htokT
    simp only [puTok] at htokT
    exact (InTok.P.inj htokT).2.symm
  have hmodT : (k0 + (topClockSpan n - 1 - h)) % topClockSpan n = topClockSpan n - 1 := by
    rw [hsT] at htailT
    by_cases hc : (k0 + (topClockSpan n - 1 - h)) % topClockSpan n = topClockSpan n - 1
    · exact hc
    · rw [if_neg hc] at htailT; exact absurd htailT (by decide)
  have hmod0 : (k0 + (topClockSpan n - h)) % topClockSpan n = 0 := by
    have := mod_succ_zero _ _ (by omega) hmodT
    have e : k0 + (topClockSpan n - 1 - h) + 1 = k0 + (topClockSpan n - h) := by omega
    rw [e] at this
    exact this
  obtain ⟨L, hL, hsplit⟩ := ordLab_split_all (paFlagSettled s Y anchor.time) (paLabSettled s Y)
    h (topClockSpan n) (by omega) hflag
  have h2 : ordLab (paFlagSettled s Y anchor.time) (paLabSettled s Y) (topClockSpan n) =
      L ++ ordLab (paFlagSettled s Y anchor.time) (paLabSettled s Y) h := hsplit
  rw [hlist] at h2
  have hlen := congrArg List.length h2
  simp only [List.length_drop, List.length_append] at hlen
  -- the reading below `h` counts the pending registers
  have hpend : (ordLab (paFlagSettled s Y anchor.time) (paLabSettled s Y) h).length =
      pendCnt (topClockSpan n) (cellOf s Y) := by
    rw [ordLab_length]
    unfold pendCnt
    rw [wsum_stop (pl (cellOf s Y)) h (topClockSpan n) (by omega)
      (fun k hk1 hk2 => by
        unfold pl
        rcases Nat.eq_or_lt_of_le hk1 with hkh | hkh
        · subst hkh; rw [htail]; rfl
        · rw [hright k hkh hk2]; rfl)]
    apply wsum_congr
    intro k hk
    unfold pl
    have hkr : k < topClockSpan n := by omega
    have hiff : paFlagSettled s Y anchor.time k = true ↔ (cellOf s Y k).i.isP = true := by
      constructor
      · intro hk'
        have := hI k hkr hk'
        rcases hleft k hk with h' | h' | h' <;> rw [h'] at this ⊢ <;> simp [puNonE, Inp.isP, Inp.isS] at this ⊢
      · intro hk'
        apply hall k hkr
        simp [puNonE, hk']
    by_cases hP : (cellOf s Y k).i.isP = true
    · simp [hiff.2 hP, hP]
    · have : ¬ paFlagSettled s Y anchor.time k = true := fun hh => hP (hiff.1 hh)
      simp [this, hP]
  refine ⟨(k0 + (topClockSpan n - h)) / topClockSpan n, ?_⟩
  have hdiv := Nat.mod_add_div (k0 + (topClockSpan n - h)) (topClockSpan n)
  rw [hmod0] at hdiv
  omega

/-- **A cleared window with the count relation is an aligned fill start.**

Consumer: `topAlignedClear`. -/
theorem clr_to_start {n : Nat} (ring : DirectedRing n) (C : HeadlineConfiguration n) (s : Fin n)
    (hg : WinGeo ring C s) (Y0 Y : TopFixedTraceState n)
    (hcut : topFreshTailPermanentCut ring C s Y0) (hfrom : MarkedFrom ring C Y0 Y)
    (hold : topClockNoOldPending s Y Y0.1.2.clock)
    (hcount : ∃ m, (paQ s Y Y0.1.2.clock).length = pendCnt (topClockSpan n) (cellOf s Y) +
      topClockSpan n * m)
    (hc : Clr (topClockSpan n) (cellOf s Y)) :
    PuPinAt ring C s Y0 Y ∧ FillShape (topClockSpan n) (cellOf s Y) ∧
      aOf s Y Y0.1.2.clock = 0 := by
  have hr3 := span_ge_three hg.hn
  have hreach : topClockReached ring C Y := markedFrom_reached ring C Y0 Y hfrom
  have hnone := pinned_hnone ring C s Y0 Y hcut hfrom
  have hcells : ∀ j, j < topClockSpan n → (cellOf s Y j).c = .off ∧
      ((cellOf s Y j).i = .e ∨ (cellOf s Y j).i = .pt ∨ (cellOf s Y j).i = .pn) := by
    intro j hj
    obtain ⟨hep, hoff⟩ := hc j hj
    refine ⟨hoff, ?_⟩
    rcases hep with h | h
    · exact Or.inl h
    · rcases hx : (cellOf s Y j).i with _ | _ | _ | _ | _ | _ <;> rw [hx] at h <;>
        simp [Inp.isP] at h ⊢
  have hfree : puFree (topClockSpan n) (cellOf s Y) := by
    intro j hj
    refine ⟨(hcells j hj).1, ?_⟩
    rcases (hcells j hj).2 with h' | h' | h' <;> rw [h'] <;> decide
  have hnoS : ∀ j, j < topClockSpan n → (cellOf s Y j).i.isS = false := by
    intro j hj
    rcases (hcells j hj).2 with h' | h' | h' <;> rw [h'] <;> rfl
  have hPin : PuPinAt ring C s Y0 Y :=
    ⟨hcut, hfrom, hold, pulinv_of_noS ring C s hg Y0.1.2.clock Y hreach hnone hfree hnoS,
      pulinv_all_of_noS s Y Y0.1.2.clock hold hnoS⟩
  refine ⟨hPin, ⟨0, by omega, fun j hj => hcells j (by omega), fun j hj1 hj2 => by omega⟩, ?_⟩
  obtain ⟨m, hm⟩ := hcount
  have hfc : fcnt (topClockSpan n) (cellOf s Y) = pendCnt (topClockSpan n) (cellOf s Y) := by
    unfold fcnt pendCnt
    apply wsum_congr
    intro k hk
    unfold fl pl
    have := hnoS k hk
    by_cases hP : (cellOf s Y k).i.isP = true
    · simp [hP, puNonE]
    · simp [hP, puNonE, this]
  unfold aOf
  rw [hfc, hm]
  have : pendCnt (topClockSpan n) (cellOf s Y) + topClockSpan n * m -
      pendCnt (topClockSpan n) (cellOf s Y) = topClockSpan n * m := by omega
  rw [this]
  exact Nat.mul_mod_right _ _

/-- **The aligned clearing stage**: from a front window whose queue satisfies
`|Q| = pending + r * m` the front clears the window within mean `n * r`, and the cleared window is
an aligned fill start (zero residue).

Consumer: `topStopFavourablePhase`. -/
theorem topAlignedClear {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (C : HeadlineConfiguration n) (s : Fin n) (hl : ∀ i : Fin n, (C i).l = false)
    (hbad : HeadlineDigit.BadCompletePair C s) (Y0 Z : TopFixedTraceState n)
    (hcut : topFreshTailPermanentCut ring C s Y0) (hfrom : MarkedFrom ring C Y0 Z)
    (hold : topClockNoOldPending s Z Y0.1.2.clock)
    (hcount : ∃ m, (paQ s Z Y0.1.2.clock).length = pendCnt (topClockSpan n) (cellOf s Z) +
      topClockSpan n * m)
    (hfs : ∃ p, FS (topClockSpan n) p (cellOf s Z)) :
    UniformFirstHit.ExpectedHittingTimeAtMost (topFixedTraceNext ring C)
      (fun Y => PuPinAt ring C s Y0 Y ∧ FillShape (topClockSpan n) (cellOf s Y) ∧
        aOf s Y Y0.1.2.clock = 0) Z ((n * topClockSpan n : Nat) : Rat) := by
  classical
  have hg : WinGeo ring C s := ⟨hn, hl, hbad⟩
  have hn0 : 0 < n := by omega
  have hr3 := span_ge_three hn
  apply (UniformFirstHit.expectedHittingTimeAtMost_iff_cost (topFixedTraceNext ring C) _ hn0 Z
    (n * topClockSpan n)).2
  intro T
  let T' : TopFixedTraceState n → Prop := fun Y =>
    PuPinAt ring C s Y0 Y ∧ FillShape (topClockSpan n) (cellOf s Y) ∧
      aOf s Y Y0.1.2.clock = 0
  let I : TopFixedTraceState n → Prop := fun Y =>
    (MarkedFrom ring C Y0 Y ∧ topClockNoOldPending s Y Y0.1.2.clock ∧
      (∃ m, (paQ s Y Y0.1.2.clock).length = pendCnt (topClockSpan n) (cellOf s Y) +
        topClockSpan n * m) ∧ ∃ q, FS (topClockSpan n) q (cellOf s Y)) ∨ T' Y
  let Φ : TopFixedTraceState n → Nat := fun Y => frontWork (topClockSpan n) (cellOf s Y)
  let chosen : TopFixedTraceState n → Fin n := fun Y =>
    if hh : ∃ q, FS (topClockSpan n) q (cellOf s Y) then winSite s (Classical.choose hh) else s
  obtain ⟨p0, hp0⟩ := hfs
  -- the successor of a front window
  have hstep : ∀ Y e, MarkedFrom ring C Y0 Y → topClockNoOldPending s Y Y0.1.2.clock →
      (∃ m, (paQ s Y Y0.1.2.clock).length = pendCnt (topClockSpan n) (cellOf s Y) +
        topClockSpan n * m) → ∀ q, FS (topClockSpan n) q (cellOf s Y) →
      (MarkedFrom ring C Y0 (topFixedTraceNext ring C Y e) ∧
        topClockNoOldPending s (topFixedTraceNext ring C Y e) Y0.1.2.clock ∧
        (∃ m, (paQ s (topFixedTraceNext ring C Y e) Y0.1.2.clock).length =
          pendCnt (topClockSpan n) (cellOf s (topFixedTraceNext ring C Y e)) +
            topClockSpan n * m)) := by
    intro Y e hY hoY hcY q hq
    have hreach : topClockReached ring C Y := markedFrom_reached ring C Y0 Y hY
    have hclock : Y0.1.2.clock ≤ Y.1.2.clock := markedFrom_clock ring C Y0 Y hcut.1 hY
    refine ⟨markedFrom_next ring C Y0 Y e hY,
      noOld_next ring C s hg Y0.1.2.clock Y hreach hclock e hoY, ?_⟩
    obtain ⟨m, hm⟩ := hcY
    have hc := fs_count_step ring C s hg Y hreach Y0.1.2.clock hclock q hq e
    exact ⟨m, by omega⟩
  have hcost := topFinalCostOfRows (topFixedTraceNext ring C) I T' Φ chosen
    (by
      intro Y hI hnot e
      rcases hI with ⟨hY, hoY, hcY, q, hq⟩ | hT
      · have hreach : topClockReached ring C Y := markedFrom_reached ring C Y0 Y hY
        obtain ⟨hY', hoY', hcY'⟩ := hstep Y e hY hoY hcY q hq
        rcases fs_step_machine ring C s hg Y hreach q hq e with hC | ⟨q', hq', _, _⟩
        · exact Or.inr (clr_to_start ring C s hg Y0 _ hcut hY' hoY' hcY' hC)
        · exact Or.inl ⟨hY', hoY', hcY', q', hq'⟩
      · exact absurd hT hnot)
    (by
      intro Y hI hnot
      rcases hI with ⟨hY, hoY, hcY, q, hq⟩ | hT
      · have h1 := wsum_ge_at (wX (cellOf s Y)) (topClockSpan n) q hq.1
        have h2 : wX (cellOf s Y) q = 1 := by unfold wX; rw [hq.2.2.1]; simp
        show 0 < wsum (wX (cellOf s Y)) (topClockSpan n)
        omega
      · exact absurd hT hnot)
    (by
      intro Y hI hnot e
      rcases hI with ⟨hY, hoY, hcY, q, hq⟩ | hT
      · have hreach : topClockReached ring C Y := markedFrom_reached ring C Y0 Y hY
        obtain ⟨hY', hoY', hcY'⟩ := hstep Y e hY hoY hcY q hq
        rcases fs_step_machine ring C s hg Y hreach q hq e with hC | ⟨q', hq', hw, _⟩
        · exact Or.inl (clr_to_start ring C s hg Y0 _ hcut hY' hoY' hcY' hC)
        · exact Or.inr hw
      · exact absurd hT hnot)
    (by
      intro Y hI hnot
      rcases hI with ⟨hY, hoY, hcY, q, hq⟩ | hT
      · have hreach : topClockReached ring C Y := markedFrom_reached ring C Y0 Y hY
        have hex : ∃ q, FS (topClockSpan n) q (cellOf s Y) := ⟨q, hq⟩
        have hsel : chosen Y = winSite s (Classical.choose hex) := by
          show (if hh : ∃ q, FS (topClockSpan n) q (cellOf s Y) then
            winSite s (Classical.choose hh) else s) = _
          rw [dif_pos hex]
        have hspec := Classical.choose_spec hex
        obtain ⟨hY', hoY', hcY'⟩ := hstep Y (chosen Y) hY hoY hcY q hq
        rw [hsel] at hY' hoY' hcY' ⊢
        rcases fs_step_machine ring C s hg Y hreach _ hspec (winSite s (Classical.choose hex)) with
          hC | ⟨q', hq', hw, hd⟩
        · exact Or.inl (clr_to_start ring C s hg Y0 _ hcut hY' hoY' hcY' hC)
        · exact Or.inr (hd rfl)
      · exact absurd hT hnot)
    Z (Or.inl ⟨hfrom, hold, hcount, p0, hp0⟩) T
  refine Nat.le_trans hcost ?_
  apply Nat.mul_le_mul_left
  apply Nat.mul_le_mul_left
  have := wsum_le_below (wX (cellOf s Z)) 1 (topClockSpan n) (fun k _ => by
    unfold wX; split <;> omega)
  show wsum (wX (cellOf s Z)) (topClockSpan n) ≤ _
  omega

end MarkedCells
end L3

#print axioms L3.MarkedCells.topAlignedClear

#print axioms L3.MarkedCells.misplaced_count
#print axioms L3.MarkedCells.clr_to_start
