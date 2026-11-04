import Leader.L3.Top.SettledWorkPotTerm

/-!
# Q7 (P.6--P.7): the lexicographic potential `(A, M)` along the fixed trace

`Pot = A * (3 r + 1) + M` with `A` the charge of the active settled inputs and `M = 2 D + X`
the front debt (`D` doomed inputs, `X` erasure fronts).  Along any scheduler word from a
coloured cut, as long as a settled input stands, `Pot` never rises.

Consumer: `Leader/L3/TopSettledWork.lean` (not yet written): P.9--P.10.
-/

namespace L3
namespace MarkedCells

open Classical

set_option autoImplicit false
set_option linter.unusedSimpArgs false

/-- A count is at most the range.

Consumer: `Mn_le`. -/
theorem cnt_le (P : Nat → Bool) : ∀ r, cnt P r ≤ r
  | 0 => Nat.le_refl _
  | k + 1 => by
      have := cnt_le P k
      simp only [cnt]; split <;> omega

/-- The front debt is at most `3 r`.

Consumer: `pot_step_machine`. -/
theorem Mn_le (r : Nat) (cells : Nat → Cell) (d : Nat → Prop) : Mn r cells d ≤ 3 * r := by
  have h1 := cnt_le (fun k => decide (d k)) r
  have h2 := cnt_le (fun k => decide ((cells k).i = .x)) r
  unfold Mn Dn Xn; omega

/-- The front count only depends on the first `r` registers.

Consumer: `pot_congr`. -/
theorem Xn_cong (r : Nat) (c1 c2 : Nat → Cell) (h : ∀ j, j < r → c1 j = c2 j) :
    Xn r c1 = Xn r c2 := by
  unfold Xn
  have : ∀ m, m ≤ r → cnt (fun k => decide ((c1 k).i = .x)) m =
      cnt (fun k => decide ((c2 k).i = .x)) m := by
    intro m
    induction m with
    | zero => intro _; rfl
    | succ m ih =>
        intro hm
        simp only [cnt]
        rw [ih (by omega)]
        simp [h m (by omega)]
  exact this r (Nat.le_refl _)

/-- The front debt only depends on the first `r` registers.

Consumer: `pot_step_machine`. -/
theorem Mn_cong (r : Nat) (c1 c2 : Nat → Cell) (d : Nat → Prop)
    (h : ∀ j, j < r → c1 j = c2 j) : Mn r c1 d = Mn r c2 d := by
  unfold Mn; rw [Xn_cong r c1 c2 h]

/-- The lexicographic potential.

Consumer: `pot_step_machine`. -/
noncomputable def Pot (r : Nat) (cells : Nat → Cell) (d : Nat → Prop) : Nat :=
  charge r (act r cells d) * (3 * r + 1) + Mn r cells d

/-- The potential only depends on the first `r` registers.

Consumer: `pot_step_machine`. -/
theorem pot_congr (r : Nat) (c1 c2 : Nat → Cell) (d : Nat → Prop)
    (h : ∀ j, j < r → c1 j = c2 j) : Pot r c1 d = Pot r c2 d := by
  unfold Pot
  rw [act_congr r c1 c2 d h, Mn_cong r c1 c2 d h]

/-- Arithmetic of the lexicographic comparison.

Consumer: `pot_step_machine`. -/
theorem pot_le_of (r A A' M M' : Nat) (hM' : M' ≤ 3 * r) (h : A' < A ∨ (A' ≤ A ∧ M' ≤ M)) :
    A' * (3 * r + 1) + M' ≤ A * (3 * r + 1) + M := by
  rcases h with h | ⟨h1, h2⟩
  · have : (A' + 1) * (3 * r + 1) ≤ A * (3 * r + 1) :=
      Nat.mul_le_mul_right _ h
    rw [Nat.succ_mul] at this
    omega
  · have := Nat.mul_le_mul_right (3 * r + 1) h1
    omega

/-- **One selected edge does not raise the potential, and keeps the barrier.**

Consumer: `pot_word`. -/
theorem pot_step_machine {n : Nat} (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (s : Fin n) (hg : WinGeo ring C s) (Z : TopFixedTraceState n)
    (hreach : topClockReached ring C Z) (d : Nat → Prop) (e : Fin n)
    (h : ColourInv s Z d) (hbar : Barrier (topClockSpan n) (cellOf s Z))
    (hex : SettledAt s Z) :
    Barrier (topClockSpan n) (cellOf s (topFixedTraceNext ring C Z e)) ∧
    Pot (topClockSpan n) (cellOf s (topFixedTraceNext ring C Z e)) (colourNext ring C s Z e d) ≤
      Pot (topClockSpan n) (cellOf s Z) d := by
  obtain ⟨hb', hch⟩ := charge_step_machine ring C s hg Z hreach d e h hbar hex
  refine ⟨hb', ?_⟩
  obtain ⟨hinv, hni, hcov, hlt⟩ := h
  have hr3 := span_ge_three hg.hn
  have hr2 : 2 ≤ topClockSpan n := by omega
  unfold Pot
  by_cases hw : ∃ p, p < topClockSpan n ∧ e = winSite s p
  · obtain ⟨p, hp, rfl⟩ := hw
    have hidx := edgeIdx_window hg.hn s p hp
    have hag := link_window ring C s Z hg hreach p hp
    have hcol : colourNext ring C s Z (winSite s p) d =
        colourGen (topClockSpan n) (cellOf s Z) (edgeStep (topClockSpan n) (cellOf s Z) p) d
          (some p) := by
      unfold colourNext
      rw [hidx]
      exact colourGen_congr _ _ _ _ _ _ hag
    rw [hcol] at hch ⊢
    rw [act_congr _ _ _ _ hag] at hch
    rw [act_congr _ _ _ _ hag, Mn_cong _ _ _ _ hag]
    by_cases hp1 : p + 1 < topClockSpan n
    · have he : edgeStep (topClockSpan n) (cellOf s Z) p =
          setTwo (cellOf s Z) p
            (pair (decide (p = 0)) false (cellOf s Z p) (cellOf s Z (p + 1))).1
            (pair (decide (p = 0)) false (cellOf s Z p) (cellOf s Z (p + 1))).2 := by
        unfold edgeStep; rw [if_pos hp1]
      rw [he] at hch ⊢
      have hep := edge_pot _ _ d p hp1 hinv hni
      refine pot_le_of _ _ _ _ _ (Mn_le _ _ _) ?_
      rcases hep with h1 | h1
      · exact Or.inl h1
      · exact Or.inr ⟨hch, h1⟩
    · have hpr : p + 1 = topClockSpan n := by omega
      have hp0 : p ≠ 0 := by omega
      have he : edgeStep (topClockSpan n) (cellOf s Z) p =
          setOne (cellOf s Z) p
            (pair false true (cellOf s Z p) { i := .e, c := .off }).1 := by
        unfold edgeStep
        rw [if_neg hp1]
        have : topClockSpan n - 1 = p := by omega
        rw [this]
      rw [he] at hch ⊢
      have hep := term_pot _ _ d p hpr hp0 hinv hni hbar hex
      refine pot_le_of _ _ _ _ _ (Mn_le _ _ _) ?_
      rcases hep with h1 | h1
      · exact Or.inl h1
      · exact Or.inr ⟨hch, h1⟩
  · have hidx := edgeIdx_other s e hw
    have hcol : colourNext ring C s Z e d = colourGen (topClockSpan n) (cellOf s Z)
        (cellOf s (topFixedTraceNext ring C Z e)) d none := by
      unfold colourNext; rw [hidx]
    rw [hcol] at hch ⊢
    rcases link_shape ring C s Z hg hreach e hw with hag | hag | ⟨t, hag⟩
    · have hcg : colourGen (topClockSpan n) (cellOf s Z)
          (cellOf s (topFixedTraceNext ring C Z e)) d none =
          colourGen (topClockSpan n) (cellOf s Z) (cellOf s Z) d none :=
        colourGen_congr _ _ _ _ _ _ hag
      rw [hcg] at hch ⊢
      rw [act_congr _ _ _ _ hag] at hch
      rw [act_congr _ _ _ _ hag, Mn_cong _ _ _ _ hag]
      have hep := port_pot (topClockSpan n) (cellOf s Z) (cellOf s Z) d (fun k hk => hk)
      exact pot_le_of _ _ _ _ _ (Mn_le _ _ _) (Or.inr ⟨hch, hep⟩)
    · have hcg : colourGen (topClockSpan n) (cellOf s Z)
          (cellOf s (topFixedTraceNext ring C Z e)) d none =
          colourGen (topClockSpan n) (cellOf s Z)
            (setOne (cellOf s Z) 0 (portClean (cellOf s Z 0))) d none :=
        colourGen_congr _ _ _ _ _ _ hag
      rw [hcg] at hch ⊢
      rw [act_congr _ _ _ _ hag] at hch
      rw [act_congr _ _ _ _ hag, Mn_cong _ _ _ _ hag]
      have hep := port_pot (topClockSpan n) (cellOf s Z)
        (setOne (cellOf s Z) 0 (portClean (cellOf s Z 0))) d (by
          intro k hk
          unfold setOne at hk
          by_cases h1 : k = 0
          · subst h1
            simp only [if_true] at hk
            unfold portClean at hk
            by_cases hc : (cellOf s Z 0).c = .off
            · simp [hc] at hk; exact hk
            · simp [hc] at hk
          · simp [h1] at hk; exact hk)
      exact pot_le_of _ _ _ _ _ (Mn_le _ _ _) (Or.inr ⟨hch, hep⟩)
    · have hcg : colourGen (topClockSpan n) (cellOf s Z)
          (cellOf s (topFixedTraceNext ring C Z e)) d none =
          colourGen (topClockSpan n) (cellOf s Z)
            (setOne (cellOf s Z) 0 (portAccept t (cellOf s Z 0))) d none :=
        colourGen_congr _ _ _ _ _ _ hag
      rw [hcg] at hch ⊢
      rw [act_congr _ _ _ _ hag] at hch
      rw [act_congr _ _ _ _ hag, Mn_cong _ _ _ _ hag]
      have hep := port_pot (topClockSpan n) (cellOf s Z)
        (setOne (cellOf s Z) 0 (portAccept t (cellOf s Z 0))) d (by
          intro k hk
          unfold setOne at hk
          by_cases h1 : k = 0
          · subst h1
            simp only [if_true] at hk
            unfold portAccept at hk
            by_cases hc : cellOf s Z 0 = { i := .e, c := .off }
            · rw [if_pos hc] at hk
              split at hk <;> simp at hk
            · rw [if_neg hc] at hk; exact hk
          · simp [h1] at hk; exact hk)
      exact pot_le_of _ _ _ _ _ (Mn_le _ _ _) (Or.inr ⟨hch, hep⟩)

/-- **The potential along a word.**

Consumer: `pot_after_coloured`. -/
theorem pot_word {n : Nat} (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (s : Fin n) (hg : WinGeo ring C s) :
    ∀ (w : List (Fin n)) (Z : TopFixedTraceState n), topClockReached ring C Z →
      ∀ d, ColourInv s Z d → Barrier (topClockSpan n) (cellOf s Z) →
      (∀ k, k < w.length → SettledAt s ((w.take k).foldl (topFixedTraceNext ring C) Z)) →
      Pot (topClockSpan n) (cellOf s (w.foldl (topFixedTraceNext ring C) Z))
          (colourWord ring C s Z d w) ≤ Pot (topClockSpan n) (cellOf s Z) d := by
  intro w
  induction w with
  | nil => intro Z _ d _ _ _; exact Nat.le_refl _
  | cons e rest ih =>
      intro Z hreach d h hbar hsett
      have h0 : SettledAt s Z := by simpa using hsett 0 (by simp)
      obtain ⟨hb', hch⟩ := pot_step_machine ring C s hg Z hreach d e h hbar h0
      have hrest := ih (topFixedTraceNext ring C Z e) (topClockReachedNext ring C Z e hreach)
        (colourNext ring C s Z e d) (cover_step_machine ring C s hg Z hreach d e h) hb'
        (by
          intro k hk
          have := hsett (k + 1) (by simp; omega)
          simpa using this)
      exact Nat.le_trans hrest hch

/-- **P.6--P.7 (monotone potential).**  From a coloured cut with every settled input active,
along any word that keeps a settled input before each edge, the lexicographic potential
`A (3 r + 1) + M` never exceeds `r^2 (3 r + 1) + 3 r`.

Consumer: `Leader/L3/TopSettledWork.lean` (not yet written). -/
theorem pot_after_coloured {n : Nat} (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (s : Fin n) (hg : WinGeo ring C s) (Y0 : TopFixedTraceState n)
    (hcol : topClockConcreteColoured ring C s Y0) (w : List (Fin n))
    (hsett : ∀ k, k < w.length →
      SettledAt s ((w.take k).foldl (topFixedTraceNext ring C) Y0)) :
    Pot (topClockSpan n) (cellOf s (w.foldl (topFixedTraceNext ring C) Y0))
        (colourWord ring C s Y0 allActive w) ≤
      topClockSpan n * topClockSpan n * (3 * topClockSpan n + 1) + 3 * topClockSpan n := by
  obtain ⟨hreach, _, hbar, hgap, _, _⟩ := hcol
  have h0 : ColourInv s Y0 allActive := by
    refine ⟨inv_reached ring C s hg Y0 hreach, noInh_of_gap s Y0 hgap, ?_, ?_⟩
    · intro u hu; exact absurd hu (by simp [allActive])
    · intro u hu; exact absurd hu (by simp [allActive])
  have h1 := pot_word ring C s hg w Y0 hreach allActive h0 (barrier_of_moving s Y0 hbar) hsett
  have h2 := charge_le (act (topClockSpan n) (cellOf s Y0) allActive) (topClockSpan n)
  have h3 := Mn_le (topClockSpan n) (cellOf s Y0) allActive
  have h4 := Nat.mul_le_mul_right (3 * topClockSpan n + 1) h2
  unfold Pot at h1 ⊢
  omega

end MarkedCells
end L3

#print axioms L3.MarkedCells.pot_after_coloured
