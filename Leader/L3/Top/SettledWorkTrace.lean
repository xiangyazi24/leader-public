import Leader.L3.Top.SettledWorkRank
import Leader.L3.Top.SettledCover

/-!
# Q7 (P.6): the charge of the active settled inputs along the fixed trace

From a coloured cut, as long as a settled input stands, the charge
`A = sum over active components [a, b] of (b + 1)` of the history colouring is nonincreasing
along every scheduler word (paper (P.6), "nonincreasing up to the first time no settled
input remains").  The step theorem treats every selected edge (window edge, terminal
edge, port, outside the window); the word theorem iterates it.

Consumer: `Leader/L3/TopSettledWork.lean` (not yet written): the P.7--P.10 potentials.
-/

namespace L3
namespace MarkedCells

open Classical

set_option autoImplicit false
set_option linter.unusedSimpArgs false

/-- The active set only depends on the first `r` registers.

Consumer: `charge_step_machine`. -/
theorem act_congr (r : Nat) (c1 c2 : Nat → Cell) (d : Nat → Prop)
    (h : ∀ j, j < r → c1 j = c2 j) : act r c1 d = act r c2 d := by
  funext k
  unfold act
  by_cases hk : k < r
  · rw [h k hk]
  · simp [hk]

/-- The barrier only depends on the first `r` registers.

Consumer: `charge_step_machine`. -/
theorem barrier_cong (r : Nat) (c1 c2 : Nat → Cell) (h : ∀ j, j < r → c1 j = c2 j)
    (hb : Barrier r c1) : Barrier r c2 := by
  intro i j hi hj hP hobs
  rw [← h i hi] at hP
  rw [← h j hj] at hobs
  exact hb i j hi hj hP hobs

/-- A settled input stands in the target window.

Consumer: `charge_step_machine`. -/
def SettledAt {n : Nat} (s : Fin n) (Z : TopFixedTraceState n) : Prop :=
  ∃ j, j < topClockSpan n ∧ (cellOf s Z j).i.isS = true

/-- **One selected edge does not raise the charge, and keeps the barrier.**

Consumer: `charge_word`. -/
theorem charge_step_machine {n : Nat} (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (s : Fin n) (hg : WinGeo ring C s) (Z : TopFixedTraceState n)
    (hreach : topClockReached ring C Z) (d : Nat → Prop) (e : Fin n)
    (h : ColourInv s Z d) (hbar : Barrier (topClockSpan n) (cellOf s Z))
    (hex : SettledAt s Z) :
    Barrier (topClockSpan n) (cellOf s (topFixedTraceNext ring C Z e)) ∧
    charge (topClockSpan n) (act (topClockSpan n) (cellOf s (topFixedTraceNext ring C Z e))
        (colourNext ring C s Z e d)) ≤
      charge (topClockSpan n) (act (topClockSpan n) (cellOf s Z) d) := by
  obtain ⟨hinv, hni, hcov, hlt⟩ := h
  have hr3 := span_ge_three hg.hn
  have hr2 : 2 ≤ topClockSpan n := by omega
  by_cases hw : ∃ p, p < topClockSpan n ∧ e = winSite s p
  · obtain ⟨p, hp, rfl⟩ := hw
    have hidx := edgeIdx_window hg.hn s p hp
    have hag := link_window ring C s Z hg hreach p hp
    have hstep := edgeStep_step (topClockSpan n) (cellOf s Z) p hp
    have hcol : colourNext ring C s Z (winSite s p) d =
        colourGen (topClockSpan n) (cellOf s Z) (edgeStep (topClockSpan n) (cellOf s Z) p) d
          (some p) := by
      unfold colourNext
      rw [hidx]
      exact colourGen_congr _ _ _ _ _ _ hag
    refine ⟨barrier_cong _ _ _ (fun j hj => (hag j hj).symm)
      (barrier_step _ hr2 _ _ hbar hni hstep), ?_⟩
    rw [hcol, act_congr _ _ _ _ hag]
    by_cases hp1 : p + 1 < topClockSpan n
    · have he : edgeStep (topClockSpan n) (cellOf s Z) p =
          setTwo (cellOf s Z) p
            (pair (decide (p = 0)) false (cellOf s Z p) (cellOf s Z (p + 1))).1
            (pair (decide (p = 0)) false (cellOf s Z p) (cellOf s Z (p + 1))).2 := by
        unfold edgeStep; rw [if_pos hp1]
      rw [he]
      exact edge_charge _ _ d p hp1 hinv hni hcov
    · have hpr : p + 1 = topClockSpan n := by omega
      have hp0 : p ≠ 0 := by omega
      have he : edgeStep (topClockSpan n) (cellOf s Z) p =
          setOne (cellOf s Z) p
            (pair false true (cellOf s Z p) { i := .e, c := .off }).1 := by
        unfold edgeStep
        rw [if_neg hp1]
        have : topClockSpan n - 1 = p := by omega
        rw [this]
      rw [he]
      exact term_charge _ _ d p hpr hp0 hinv hni hbar hex
  · have hidx := edgeIdx_other s e hw
    have hcol : colourNext ring C s Z e d = colourGen (topClockSpan n) (cellOf s Z)
        (cellOf s (topFixedTraceNext ring C Z e)) d none := by
      unfold colourNext; rw [hidx]
    rw [hcol]
    rcases link_shape ring C s Z hg hreach e hw with hag | hag | ⟨t, hag⟩
    · have hcg : colourGen (topClockSpan n) (cellOf s Z)
          (cellOf s (topFixedTraceNext ring C Z e)) d none =
          colourGen (topClockSpan n) (cellOf s Z) (cellOf s Z) d none :=
        colourGen_congr _ _ _ _ _ _ hag
      rw [hcg, act_congr _ _ _ _ hag]
      refine ⟨barrier_cong _ _ _ (fun j hj => (hag j hj).symm) hbar, ?_⟩
      refine act_same_case _ _ _ d none ?_ (fun k hk => hk) (fun m hm => hm)
      intro k hk
      exact ((act_iff _ _ d k).1 hk).2.1
    · have hcg : colourGen (topClockSpan n) (cellOf s Z)
          (cellOf s (topFixedTraceNext ring C Z e)) d none =
          colourGen (topClockSpan n) (cellOf s Z)
            (setOne (cellOf s Z) 0 (portClean (cellOf s Z 0))) d none :=
        colourGen_congr _ _ _ _ _ _ hag
      rw [hcg, act_congr _ _ _ _ hag]
      refine ⟨barrier_cong _ _ _ (fun j hj => (hag j hj).symm)
        (barrier_step _ hr2 _ _ hbar hni Step.clean), ?_⟩
      exact port_charge _ hr2 _ _ d hinv hni (Or.inl rfl)
    · have hcg : colourGen (topClockSpan n) (cellOf s Z)
          (cellOf s (topFixedTraceNext ring C Z e)) d none =
          colourGen (topClockSpan n) (cellOf s Z)
            (setOne (cellOf s Z) 0 (portAccept t (cellOf s Z 0))) d none :=
        colourGen_congr _ _ _ _ _ _ hag
      rw [hcg, act_congr _ _ _ _ hag]
      refine ⟨barrier_cong _ _ _ (fun j hj => (hag j hj).symm)
        (barrier_step _ hr2 _ _ hbar hni (Step.accept t)), ?_⟩
      exact port_charge _ hr2 _ _ d hinv hni (Or.inr ⟨t, rfl⟩)

/-- The concrete moving barrier is the abstract barrier of the cells.

Consumer: `charge_after_coloured`. -/
theorem barrier_of_moving {n : Nat} (s : Fin n) (Y : TopFixedTraceState n)
    (h : topClockConcreteMovingBarrier s Y) : Barrier (topClockSpan n) (cellOf s Y) := by
  intro i j hi hj hP hobs
  have := h ⟨i, hi⟩ ⟨j, hj⟩
    (by
      unfold topClockConcreteInputAt
      have h1 := siteCell_isP Y (winSite s i)
      unfold cellOf at hP
      rw [h1] at hP; exact hP)
    (by
      have h2 := (siteCell_obC Y (winSite s j)).1 hobs
      unfold topClockConcreteInputAt topClockConcreteCarryAt
      rcases h2 with h2 | h2 | h2
      · exact Or.inl h2
      · exact Or.inr (Or.inl h2)
      · exact Or.inr (Or.inr h2))
  exact this

/-- **The charge along a word.**  As long as a settled input stands before each selected
edge, the charge of the active settled inputs does not rise, and the barrier is kept.

Consumer: `charge_after_coloured`. -/
theorem charge_word {n : Nat} (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (s : Fin n) (hg : WinGeo ring C s) :
    ∀ (w : List (Fin n)) (Z : TopFixedTraceState n), topClockReached ring C Z →
      ∀ d, ColourInv s Z d → Barrier (topClockSpan n) (cellOf s Z) →
      (∀ k, k < w.length → SettledAt s ((w.take k).foldl (topFixedTraceNext ring C) Z)) →
      charge (topClockSpan n) (act (topClockSpan n)
          (cellOf s (w.foldl (topFixedTraceNext ring C) Z)) (colourWord ring C s Z d w)) ≤
        charge (topClockSpan n) (act (topClockSpan n) (cellOf s Z) d) := by
  intro w
  induction w with
  | nil => intro Z _ d _ _ _; exact Nat.le_refl _
  | cons e rest ih =>
      intro Z hreach d h hbar hsett
      have h0 : SettledAt s Z := by simpa using hsett 0 (by simp)
      obtain ⟨hb', hch⟩ := charge_step_machine ring C s hg Z hreach d e h hbar h0
      have hrest := ih (topFixedTraceNext ring C Z e) (topClockReachedNext ring C Z e hreach)
        (colourNext ring C s Z e d) (cover_step_machine ring C s hg Z hreach d e h) hb'
        (by
          intro k hk
          have := hsett (k + 1) (by simp; omega)
          simpa using this)
      exact Nat.le_trans hrest hch

/-- The charge is at most `r^2`.

Consumer: `charge_after_coloured`. -/
theorem charge_le (a : Nat → Bool) : ∀ k, charge k a ≤ k * k
  | 0 => Nat.le_refl _
  | k + 1 => by
      have := charge_le a k
      simp only [charge]
      split <;> (have : k * k + k + 1 ≤ (k + 1) * (k + 1) := by
                   rw [Nat.add_mul, Nat.mul_add]; omega
                 omega)

/-- **P.6 (monotone charge).**  From a coloured cut with every settled input active, along any
word that keeps a settled input before each edge, the charge of the history colouring is at
most its initial value, which is at most `r^2`.

Consumer: `Leader/L3/TopSettledWork.lean` (not yet written). -/
theorem charge_after_coloured {n : Nat} (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (s : Fin n) (hg : WinGeo ring C s) (Y0 : TopFixedTraceState n)
    (hcol : topClockConcreteColoured ring C s Y0) (w : List (Fin n))
    (hsett : ∀ k, k < w.length →
      SettledAt s ((w.take k).foldl (topFixedTraceNext ring C) Y0)) :
    charge (topClockSpan n) (act (topClockSpan n)
        (cellOf s (w.foldl (topFixedTraceNext ring C) Y0)) (colourWord ring C s Y0 allActive w)) ≤
      topClockSpan n * topClockSpan n := by
  have hcol' := hcol
  obtain ⟨hreach, _, hbar, hgap, _, _⟩ := hcol
  have h0 : ColourInv s Y0 allActive := by
    refine ⟨inv_reached ring C s hg Y0 hreach, noInh_of_gap s Y0 hgap, ?_, ?_⟩
    · intro u hu; exact absurd hu (by simp [allActive])
    · intro u hu; exact absurd hu (by simp [allActive])
  exact Nat.le_trans (charge_word ring C s hg w Y0 hreach allActive h0
    (barrier_of_moving s Y0 hbar) hsett) (charge_le _ _)

end MarkedCells
end L3

#print axioms L3.MarkedCells.charge_after_coloured
