import Leader.L3.Top.SettledPotentialTrace

/-!
# Q7 (P.8--P.10): a strict drop at every front-free state with a settled input

Consumer: `Leader/L3/Top/SettledPotentialPhase.lean`.
-/

namespace L3
namespace MarkedCells

open Classical
set_option autoImplicit false
set_option linter.unusedSimpArgs false

/-- An empty carry-free border cell is an offer of acceptance.

Consumer: `th_strict`. -/
theorem acc_of_borderCell {n : Nat} (s : Fin n) (Z : TopFixedTraceState n)
    (h : cellOf s Z 0 = { i := .e, c := .off }) : accOf s Z = true := by
  have h' : siteCell Z (winSite s 0) = { i := .e, c := .off } := h
  have hi : absIn (Z.1.1 (winSite s 0)).qIn = .e := congrArg Cell.i h'
  have hc : (siteCell Z (winSite s 0)).c = .off := congrArg Cell.c h'
  have hoff := siteCell_offMatch Z (winSite s 0)
  unfold OffMatch at hoff
  have hq : (Z.1.1 (winSite s 0)).qCarry = .OFF := hoff.1 hc
  have hqi : (Z.1.1 (winSite s 0)).qIn = .E := by
    cases hh : (Z.1.1 (winSite s 0)).qIn with
    | E => rfl
    | X => rw [hh] at hi; simp [absIn] at hi
    | P v t => rw [hh] at hi; cases t <;> simp [absIn] at hi
    | S v t => rw [hh] at hi; cases t <;> simp [absIn] at hi
  unfold accOf
  rw [hqi, hq]
  rfl

/-- **Accepting a sampled token lowers the measure** of an unfed window.

Consumer: `th_strict`. -/
theorem port_accept_gv {n : Nat} (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (s : Fin n) (hg : WinGeo ring C s) (Z : TopFixedTraceState n)
    (hreach : topClockReached ring C Z) (hfe : FEnv (topClockSpan n) (cellOf s Z))
    (hd0 : dist (topClockSpan n) (srcOf s Z) = 0) (hacc : accOf s Z = true)
    (hnc : ¬ ConsAt (topClockSpan n) (cellOf s Z)) :
    Gv (topClockSpan n) (cellOf s (topFixedTraceNext ring C Z (certSite s (topClockSpan n - 1)))) <
      Gv (topClockSpan n) (cellOf s Z) := by
  have hr3 := span_ge_three hg.hn
  have hw : ¬ ∃ p, p < topClockSpan n ∧ certSite s (topClockSpan n - 1) = winSite s p :=
    fun ⟨p, _, hp⟩ => winSite_ne_portSite hg.hn s p ‹_› hp.symm
  have hshape := link_shape ring C s Z hg hreach _ hw
  obtain ⟨v, t, hD⟩ := terminal_sampled ring C s hg Z hreach hd0
  have hpl := (topSettledSourceDeliver ring C s hg).2.2.2.2 Z hreach v t hD hacc
  have hc0 := cell0_of_acc s Z hacc
  have hpend : cellOf s (topFixedTraceNext ring C Z (certSite s (topClockSpan n - 1))) 0 =
      { i := (if t = true then Inp.pt else Inp.pn), c := Car.off } := hpl.1
  rcases hshape with hag | hag | ⟨t', hag⟩
  · exfalso
    have := hag 0 (by omega)
    rw [hpend, hc0] at this
    cases t <;> simp at this
  · exfalso
    have := hag 0 (by omega)
    rw [hpend] at this
    simp only [setOne, if_true, portClean, hc0] at this
    cases t <;> simp at this
  · have hp' : (if t' = true then Inp.pt else Inp.pn).isP = true := by cases t' <;> rfl
    have e1 : portAccept t' (cellOf s Z 0) =
        { i := (if t' = true then Inp.pt else Inp.pn), c := .off } := by
      unfold portAccept; rw [if_pos hc0]
    have hg2 := gv_accept (topClockSpan n) (cellOf s Z) hfe (by omega) _ hp' hc0
    have hag2 : ∀ k, k < topClockSpan n →
        cellOf s (topFixedTraceNext ring C Z (certSite s (topClockSpan n - 1))) k =
        setOne (cellOf s Z) 0 { i := (if t' = true then Inp.pt else Inp.pn), c := .off } k := by
      intro k hk; rw [hag k hk, e1]
    have hGv := Gv_congr (topClockSpan n) _ _ (samePat_of_eq _ _ _ hag2)
    have := hg2.2.2 hnc
    omega

/-- A window edge whose pure result lowers the charge or the measure.

Consumer: `th_strict`. -/
theorem strict_of_res {n : Nat} (ring : DirectedRing n) (C : HeadlineConfiguration n) (s : Fin n)
    (hg : WinGeo ring C s) (Z : TopFixedTraceState n) (hreach : topClockReached ring C Z)
    (d : Nat → Prop) (e : Fin n) (h : ColourInv s Z d)
    (hbar : Barrier (topClockSpan n) (cellOf s Z)) (hex : SettledAt s Z)
    (hM : Mn (topClockSpan n) (cellOf s Z) d = 0) (R : Nat → Cell)
    (hR : ∀ j, j < topClockSpan n → cellOf s (topFixedTraceNext ring C Z e) j = R j)
    (hdrop : At (topClockSpan n) R < At (topClockSpan n) (cellOf s Z) ∨
      Gv (topClockSpan n) R + 1 ≤ Gv (topClockSpan n) (cellOf s Z)) :
    charge (topClockSpan n) (act (topClockSpan n) (cellOf s (topFixedTraceNext ring C Z e))
        (colourNext ring C s Z e d)) <
      charge (topClockSpan n) (act (topClockSpan n) (cellOf s Z) d) ∨
    (Mn (topClockSpan n) (cellOf s (topFixedTraceNext ring C Z e)) (colourNext ring C s Z e d) = 0 ∧
      Th s (topFixedTraceNext ring C Z e) < Th s Z) := by
  rcases th_step ring C s hg Z hreach d e h hbar hex hM with h1 | ⟨hM', _, hc⟩
  · exact Or.inl h1
  · obtain ⟨_, hd'⟩ := mn_zero_facts _ _ _ hM'
    obtain ⟨_, hd0⟩ := mn_zero_facts _ _ _ hM
    have hAt' := charge_eq_At (topClockSpan n) (cellOf s (topFixedTraceNext ring C Z e))
      (colourNext ring C s Z e d) hd'
    have hAt0 := charge_eq_At (topClockSpan n) (cellOf s Z) d hd0
    have hAtR : At (topClockSpan n) (cellOf s (topFixedTraceNext ring C Z e)) =
        At (topClockSpan n) R := by
      unfold At; rw [act_congr _ _ _ _ hR]
    rcases hdrop with hlt | hlt
    · left
      rw [hAt', hAt0, hAtR]; exact hlt
    · right
      refine ⟨hM', hc (Or.inl ?_)⟩
      rw [Gv_congr _ _ _ (samePat_of_eq _ _ _ hR)]
      omega

/-- **A strict drop.**  From a front-free reached state with a settled input some edge lowers
the active charge, or leaves the front debt zero and lowers the supply potential.

Consumer: `Leader/L3/Top/SettledPotentialPhase.lean`. -/
theorem th_strict {n : Nat} (ring : DirectedRing n) (C : HeadlineConfiguration n) (s : Fin n)
    (hg : WinGeo ring C s) (Z : TopFixedTraceState n) (hreach : topClockReached ring C Z)
    (d : Nat → Prop) (h : ColourInv s Z d)
    (hbar : Barrier (topClockSpan n) (cellOf s Z)) (hex : SettledAt s Z)
    (hM : Mn (topClockSpan n) (cellOf s Z) d = 0) :
    ∃ e : Fin n,
      charge (topClockSpan n) (act (topClockSpan n) (cellOf s (topFixedTraceNext ring C Z e))
          (colourNext ring C s Z e d)) <
        charge (topClockSpan n) (act (topClockSpan n) (cellOf s Z) d) ∨
      (Mn (topClockSpan n) (cellOf s (topFixedTraceNext ring C Z e)) (colourNext ring C s Z e d)
          = 0 ∧ Th s (topFixedTraceNext ring C Z e) < Th s Z) := by
  have hr3 := span_ge_three hg.hn
  have hfe := fenv_machine s Z d h hbar hex hM
  rcases nominate_pure (topClockSpan n) (cellOf s Z) hfe (by omega) with
    ⟨p, hp1, hnx, hdrop⟩ | ⟨hnx, hdrop⟩ | ⟨hc0, hnc⟩
  · refine ⟨winSite s p, strict_of_res ring C s hg Z hreach d _ h hbar hex hM
      (EdgeRes (topClockSpan n) p (cellOf s Z)) ?_ hdrop⟩
    intro j hj
    rw [link_window ring C s Z hg hreach p (by omega) j hj]
    unfold edgeStep EdgeRes; rw [if_pos hp1]
  · refine ⟨winSite s (topClockSpan n - 1), strict_of_res ring C s hg Z hreach d _ h hbar hex hM
      (TermRes (topClockSpan n) (cellOf s Z)) ?_ (Or.inr hdrop)⟩
    intro j hj
    rw [link_window ring C s Z hg hreach (topClockSpan n - 1) (by omega) j hj]
    unfold edgeStep TermRes; rw [if_neg (by omega)]
  · by_cases hd : dist (topClockSpan n) (srcOf s Z) = 0
    · refine ⟨certSite s (topClockSpan n - 1), ?_⟩
      have hacc := acc_of_borderCell s Z hc0
      rcases th_step ring C s hg Z hreach d (certSite s (topClockSpan n - 1)) h hbar hex hM with
        h1 | ⟨hM', _, hc⟩
      · exact Or.inl h1
      · exact Or.inr ⟨hM', hc (Or.inl (port_accept_gv ring C s hg Z hreach hfe hd hacc hnc))⟩
    · obtain ⟨hidx, hlt⟩ := (topSettledSourceDeliver ring C s hg).2.2.2.1 Z hreach hd
      refine ⟨certSite s (srcIdx (topClockSpan n) (srcOf s Z)), ?_⟩
      rcases th_step ring C s hg Z hreach d _ h hbar hex hM with h1 | ⟨hM', _, hc⟩
      · exact Or.inl h1
      · exact Or.inr ⟨hM', hc (Or.inr ⟨hnc, by omega⟩)⟩

end MarkedCells
end L3

#print axioms L3.MarkedCells.th_strict
#print axioms L3.MarkedCells.port_accept_gv
#print axioms L3.MarkedCells.acc_of_borderCell
