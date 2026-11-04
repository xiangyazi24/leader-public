import Leader.L3.Top.SettledPotentialStep

/-!
# Q7 (P.8--P.10): one real edge from a front-free state

From a front-free reached state with a settled input, one edge either lowers the active charge
or keeps the state front-free without raising the supply potential `Th`.

Consumer: `Leader/L3/Top/SettledPotentialPhase.lean`.
-/

namespace L3
namespace MarkedCells

open Classical
set_option autoImplicit false
set_option linter.unusedSimpArgs false

/-- The border register of the target window offers acceptance exactly when its cell is empty
and carry-free.

Consumer: `th_step`. -/
theorem cell0_of_acc {n : Nat} (s : Fin n) (Z : TopFixedTraceState n) (h : accOf s Z = true) :
    cellOf s Z 0 = { i := .e, c := .off } := by
  unfold accOf at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  have hq : (Z.1.1 (winSite s 0)).qIn = .E := by
    cases hh : (Z.1.1 (winSite s 0)).qIn <;> simp_all [InTok.isE]
  have hc : (Z.1.1 (winSite s 0)).qCarry = .OFF := by
    cases hh : (Z.1.1 (winSite s 0)).qCarry <;> simp_all [QCarry.isOff]
  have hoff := siteCell_offMatch Z (winSite s 0)
  unfold OffMatch at hoff
  have hco : (siteCell Z (winSite s 0)).c = .off := hoff.2 hc
  unfold cellOf
  rcases hcell : siteCell Z (winSite s 0) with ⟨a, b⟩
  rw [hcell] at hco
  simp only at hco
  have ha : a = .e := by
    have h3 : (siteCell Z (winSite s 0)).i = absIn (Z.1.1 (winSite s 0)).qIn := rfl
    rw [hcell] at h3
    simp only at h3
    rw [h3, hq]; rfl
  rw [ha, hco]

/-- A sampled token at the source terminal is a sampled output of the terminal register.

Consumer: `th_step`. -/
theorem terminal_sampled {n : Nat} (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (s : Fin n) (hg : WinGeo ring C s) (Z : TopFixedTraceState n)
    (hreach : topClockReached ring C Z) (h : dist (topClockSpan n) (srcOf s Z) = 0) :
    ∃ (v : Fin (compileAdvice (ceilLogTwo n)).topA) (t : Bool),
      (Z.1.1 (certSite s (topClockSpan n - 1))).qOut = .D v t := by
  have h2 := (topSettledSourceDeliver ring C s hg).2.1 Z hreach
  have h3 := (h2.1 h)
  cases ho : (Z.1.1 (certSite s (topClockSpan n - 1))).qOut with
  | E => rw [ho] at h3; simp [absOut] at h3
  | U => rw [ho] at h3; simp [absOut] at h3
  | D v t => exact ⟨v, t, rfl⟩

/-- **One edge from a front-free state.**  Either the active charge falls, or the front debt
stays zero and the supply potential does not rise.

Consumer: `Leader/L3/Top/SettledPotentialPhase.lean`. -/
theorem th_step {n : Nat} (ring : DirectedRing n) (C : HeadlineConfiguration n) (s : Fin n)
    (hg : WinGeo ring C s) (Z : TopFixedTraceState n) (hreach : topClockReached ring C Z)
    (d : Nat → Prop) (e : Fin n) (h : ColourInv s Z d)
    (hbar : Barrier (topClockSpan n) (cellOf s Z)) (hex : SettledAt s Z)
    (hM : Mn (topClockSpan n) (cellOf s Z) d = 0) :
    charge (topClockSpan n) (act (topClockSpan n) (cellOf s (topFixedTraceNext ring C Z e))
        (colourNext ring C s Z e d)) <
      charge (topClockSpan n) (act (topClockSpan n) (cellOf s Z) d) ∨
    (Mn (topClockSpan n) (cellOf s (topFixedTraceNext ring C Z e)) (colourNext ring C s Z e d) = 0 ∧
      Th s (topFixedTraceNext ring C Z e) ≤ Th s Z ∧
      ((Gv (topClockSpan n) (cellOf s (topFixedTraceNext ring C Z e)) <
          Gv (topClockSpan n) (cellOf s Z) ∨
        (¬ ConsAt (topClockSpan n) (cellOf s Z) ∧
          dist (topClockSpan n) (srcOf s (topFixedTraceNext ring C Z e)) <
            dist (topClockSpan n) (srcOf s Z))) →
        Th s (topFixedTraceNext ring C Z e) < Th s Z)) := by
  have hr3 := span_ge_three hg.hn
  obtain ⟨hb', hch⟩ := charge_step_machine ring C s hg Z hreach d e h hbar hex
  obtain ⟨_, hpot⟩ := pot_step_machine ring C s hg Z hreach d e h hbar hex
  by_cases hlt : charge (topClockSpan n) (act (topClockSpan n)
      (cellOf s (topFixedTraceNext ring C Z e)) (colourNext ring C s Z e d)) <
      charge (topClockSpan n) (act (topClockSpan n) (cellOf s Z) d)
  · exact Or.inl hlt
  right
  have heqA : charge (topClockSpan n) (act (topClockSpan n)
      (cellOf s (topFixedTraceNext ring C Z e)) (colourNext ring C s Z e d)) =
      charge (topClockSpan n) (act (topClockSpan n) (cellOf s Z) d) := by omega
  have hM' : Mn (topClockSpan n) (cellOf s (topFixedTraceNext ring C Z e))
      (colourNext ring C s Z e d) = 0 := by
    unfold Pot at hpot
    rw [heqA] at hpot
    omega
  refine ⟨hM', ?_⟩
  have hfe := fenv_machine s Z d h hbar hex hM
  obtain ⟨hnx', hd'⟩ := mn_zero_facts _ _ _ hM'
  obtain ⟨_, hd0⟩ := mn_zero_facts _ _ _ hM
  have hAt' := charge_eq_At (topClockSpan n) (cellOf s (topFixedTraceNext ring C Z e))
    (colourNext ring C s Z e d) hd'
  have hAt0 := charge_eq_At (topClockSpan n) (cellOf s Z) d hd0
  have hnlt : ¬ At (topClockSpan n) (cellOf s (topFixedTraceNext ring C Z e)) <
      At (topClockSpan n) (cellOf s Z) := by
    rw [← hAt', ← hAt0]; exact hlt
  -- the supply potential
  have key : GoodNext (topClockSpan n) (cellOf s Z) (cellOf s (topFixedTraceNext ring C Z e)) →
      dist (topClockSpan n) (srcOf s (topFixedTraceNext ring C Z e)) ≤
        dist (topClockSpan n) (srcOf s Z) →
      (Th s (topFixedTraceNext ring C Z e) ≤ Th s Z ∧
      ((Gv (topClockSpan n) (cellOf s (topFixedTraceNext ring C Z e)) <
          Gv (topClockSpan n) (cellOf s Z) ∨
        (¬ ConsAt (topClockSpan n) (cellOf s Z) ∧
          dist (topClockSpan n) (srcOf s (topFixedTraceNext ring C Z e)) <
            dist (topClockSpan n) (srcOf s Z))) →
        Th s (topFixedTraceNext ring C Z e) < Th s Z)) := by
    intro g hd
    unfold Th
    exact ⟨th_le_good _ _ _ _ _ g hd, th_lt_good _ _ _ _ _ g hd⟩
  by_cases hw : ∃ p, p < topClockSpan n ∧ e = winSite s p
  · obtain ⟨p, hp, rfl⟩ := hw
    have hag := link_window ring C s Z hg hreach p hp
    have hdist : dist (topClockSpan n) (srcOf s (topFixedTraceNext ring C Z (winSite s p))) ≤
        dist (topClockSpan n) (srcOf s Z) := by
      rcases dist_next ring C s hg Z hreach (winSite s p) with h1 | ⟨_, h2, _⟩
      · exact h1
      · exact absurd h2 (winSite_ne_portSite hg.hn s p hp)
    by_cases hp1 : p + 1 < topClockSpan n
    · have he : edgeStep (topClockSpan n) (cellOf s Z) p = EdgeRes (topClockSpan n) p (cellOf s Z) := by
        unfold edgeStep EdgeRes; rw [if_pos hp1]
      have hag' : ∀ j, j < topClockSpan n →
          cellOf s (topFixedTraceNext ring C Z (winSite s p)) j =
            EdgeRes (topClockSpan n) p (cellOf s Z) j := by
        intro j hj; rw [hag j hj, he]
      have hnx2 : ∀ k, k < topClockSpan n → (EdgeRes (topClockSpan n) p (cellOf s Z) k).i ≠ .x := by
        intro k hk; rw [← hag' k hk]; exact hnx' k hk
      have hge := edge_gv (topClockSpan n) p (cellOf s Z) hfe hp1 hnx2
      have hAtE : At (topClockSpan n) (EdgeRes (topClockSpan n) p (cellOf s Z)) =
          At (topClockSpan n) (cellOf s (topFixedTraceNext ring C Z (winSite s p))) := by
        unfold At; rw [act_congr _ _ _ _ hag']
      rcases hge with hge | hge
      · exact absurd (by rw [← hAtE]; exact hge) hnlt
      · exact key (goodNext_congr _ _ _ _ (fun k hk => (hag' k hk).symm) hge) hdist
    · have hpr : p + 1 = topClockSpan n := by omega
      have he : edgeStep (topClockSpan n) (cellOf s Z) p = TermRes (topClockSpan n) (cellOf s Z) := by
        unfold edgeStep TermRes
        rw [if_neg hp1]
      have hag' : ∀ j, j < topClockSpan n →
          cellOf s (topFixedTraceNext ring C Z (winSite s p)) j =
            TermRes (topClockSpan n) (cellOf s Z) j := by
        intro j hj; rw [hag j hj, he]
      have hnx2 : ∀ k, k < topClockSpan n → (TermRes (topClockSpan n) (cellOf s Z) k).i ≠ .x := by
        intro k hk; rw [← hag' k hk]; exact hnx' k hk
      have hgt := term_gv (topClockSpan n) (cellOf s Z) hfe (by omega) hnx2
      have hgood : GoodNext (topClockSpan n) (cellOf s Z) (TermRes (topClockSpan n) (cellOf s Z)) := by
        rcases hgt with hgt | ⟨hgt, hnc⟩
        · have : TermRes (topClockSpan n) (cellOf s Z) = cellOf s Z := hgt
          rw [this]; exact ⟨Nat.le_refl _, fun hh => hh⟩
        · have hgt2 : Gv (topClockSpan n) (TermRes (topClockSpan n) (cellOf s Z)) + 1 =
              Gv (topClockSpan n) (cellOf s Z) := hgt
          exact ⟨by omega, fun hh => absurd hh hnc⟩
      exact key (goodNext_congr _ _ _ _ (fun k hk => (hag' k hk).symm) hgood) hdist
  · -- an edge outside the window
    have hshape := link_shape ring C s Z hg hreach e hw
    have hgp := good_port (topClockSpan n) (cellOf s Z) hfe (by omega)
    rcases dist_next ring C s hg Z hreach e with hdist | ⟨hd0, hport, hacc⟩
    · rcases hshape with hag | hag | ⟨t, hag⟩
      · exact key (goodNext_congr _ _ _ _ (fun k hk => (hag k hk).symm) (hgp true).1) hdist
      · exact key (goodNext_congr _ _ _ _ (fun k hk => (hag k hk).symm) (hgp true).2.1) hdist
      · exact key (goodNext_congr _ _ _ _ (fun k hk => (hag k hk).symm) (hgp t).2.2) hdist
    · -- the port edge accepts a sampled token
      unfold Th
      obtain ⟨v, t, hD⟩ := terminal_sampled ring C s hg Z hreach hd0
      have hpl := (topSettledSourceDeliver ring C s hg).2.2.2.2 Z hreach v t hD hacc
      have hc0 := cell0_of_acc s Z hacc
      have hport' : certSite s (topClockSpan n - 1) = e := hport.symm
      rw [hport'] at hpl
      have hpend : cellOf s (topFixedTraceNext ring C Z e) 0 =
          { i := (if t = true then Inp.pt else Inp.pn), c := Car.off } := hpl.1
      have hdl := dist_le (topClockSpan n) (srcOf s (topFixedTraceNext ring C Z e))
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
        have hag2 : ∀ k, k < topClockSpan n → cellOf s (topFixedTraceNext ring C Z e) k =
            setOne (cellOf s Z) 0 { i := (if t' = true then Inp.pt else Inp.pn), c := .off } k := by
          intro k hk; rw [hag k hk, e1]
        have hGv : Gv (topClockSpan n) (cellOf s (topFixedTraceNext ring C Z e)) =
            Gv (topClockSpan n) (setOne (cellOf s Z) 0
              { i := (if t' = true then Inp.pt else Inp.pn), c := .off }) :=
          Gv_congr _ _ _ (samePat_of_eq _ _ _ hag2)
        have hCc := consAt_congr (topClockSpan n) _ _ hag2
        by_cases hc : ConsAt (topClockSpan n) (cellOf s Z)
        · have hc' := hCc.2 (hg2.1.2 hc)
          have hh2 := hg2.2.1 hc
          rw [if_pos hc', if_pos hc, hGv]
          refine ⟨by omega, fun hcond => ?_⟩
          rcases hcond with h1 | ⟨h1, _⟩
          · omega
          · exact absurd hc h1
        · have hc' : ¬ ConsAt (topClockSpan n) (cellOf s (topFixedTraceNext ring C Z e)) :=
            fun hh => hc (hg2.1.1 (hCc.1 hh))
          rw [if_neg hc', if_neg hc, hGv]
          have := hg2.2.2 hc
          rw [hd0]
          exact ⟨by omega, fun _ => by omega⟩

end MarkedCells
end L3

#print axioms L3.MarkedCells.th_step
