import Leader.L3.Top.PinnedPhaseStatic

/-!
# Q7 (P.12 preparation, lemma 2): the aligned completion costs at most `n * (r + 1)`

From an aligned labelled state the border edge launches the carry, the host moves one register per
service of its own edge, and the retiring service records a strict cyclic comparison terminal,
which is a strict stop when no earlier prefix is one.  The potential is the one of the carry sweep:
`r + 1` while aligned, `r - k` with the host at `k`.

Consumer: `Leader/L3/TopPinnedPhaseFill.lean`.
-/

namespace L3
namespace MarkedCells

open Classical
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

set_option autoImplicit false
set_option linter.unusedSimpArgs false

/-- **The launch of an aligned labelled window**: the static data of the window and the sweep
invariant with the host at the border one service later.

Consumer: `aligned_strict_cost`. -/
theorem sweep_init {n : Nat} (ring : DirectedRing n) (C : HeadlineConfiguration n) (s : Fin n)
    (hg : WinGeo ring C s) (Y0 Yl : TopFixedTraceState n) (hP : PuPinAt ring C s Y0 Yl)
    (hA : AlignShape (topClockSpan n) (cellOf s Yl)) :
    ∃ (sam : Nat → DigitSample (compileAdvice (ceilLogTwo n)) n)
      (exs : Nat → DigitExport (compileAdvice (ceilLogTwo n)) n),
      SweepStatic s Yl sam exs ∧
      (∀ j, 1 ≤ j → j < topClockSpan n → (sam j).tail = false) ∧
      SweepDyn ring C s Yl sam 0 (topFixedTraceNext ring C Yl (winSite s 0)) := by
  have hn2 : 2 ≤ n := by have := hg.hn; omega
  have hr3 := span_ge_three hg.hn
  obtain ⟨sam, exs, hstat, htails, hreg⟩ := static_of_aligned ring C s hg Y0 Yl hP hA
  refine ⟨sam, exs, hstat, htails, ?_⟩
  have hreach : topClockReached ring C Yl := markedFrom_reached ring C Y0 Yl hP.2.1
  have hself : MarkedFrom ring C Yl Yl := ⟨[], by rw [List.append_nil]; exact hreach⟩
  have hnext : ring.rightNeighbor (winSite s 0) = winSite s 1 := winSite_next ring s 0
  have hxl := agent_l ring C s hg Yl hreach (winSite s 0)
  have hyl := agent_l ring C s hg Yl hreach (ring.rightNeighbor (winSite s 0))
  have hxb : (Yl.1.1 (winSite s 0)).beta = true := by
    rw [agent_beta ring C Yl hreach, winSite_beta ring C s hg.hbad 0 (by omega)]
    simp
  have hyb : (Yl.1.1 (ring.rightNeighbor (winSite s 0))).beta = false := by
    rw [hnext, agent_beta ring C Yl hreach, winSite_beta ring C s hg.hbad 1 (by omega)]
    simp
  have h0 := hreg 0 (by omega)
  have h1 := hreg 1 (by omega)
  have hs0 : (Yl.1.1 (winSite s 0)).qIn.isS = true := by rw [h0.1]; rfl
  obtain ⟨u, hc, ht, htg, hop, hval, htl⟩ :=
    trace_launch_full ring C Yl (winSite s 0) hxl hyl hxb h0.2.1 hs0
  obtain ⟨k1, k2, k3⟩ := launch_resp_keep ring hn2 C Yl (winSite s 0) hxl hyl
    (sam 0).value (sam 0).tail (sam 1).value (sam 1).tail h0.1 h0.2.1 hxb
    (by rw [hnext]; exact h1.1) (by rw [hnext]; exact h1.2.1) hyb
  rw [hnext] at k1 k2 k3
  refine ⟨hreach, markedFrom_next ring C Yl Yl _ hself,
    (carry_next_align ring C s hg Yl hreach hA (winSite s 0)).1 rfl, ?_, ?_⟩
  · refine ⟨[u], hc, rfl, ?_, ?_, List.pairwise_singleton _ _⟩
    · intro j hj
      have hj0 : j = 0 := by omega
      subst hj0
      refine ⟨u, rfl, htg, ?_, ?_, ?_⟩
      · rw [hop]; exact h0.2.2
      · rw [hval, h0.1]; rfl
      · rw [htl, h0.1]; rfl
    · intro a ha
      rw [List.mem_singleton] at ha
      subst ha
      rw [next_clock, ht]
      omega
  · intro j hj1 hj2
    by_cases hj : j = 1
    · subst hj
      refine ⟨k1, k2, ?_⟩
      rw [k3]; exact h1.2.2
    · have hne1 : winSite s j ≠ winSite s 0 := fun h =>
        absurd (winSite_inj hg.hn s j 0 (by omega) (by omega) h) (by omega)
      have hne2 : winSite s j ≠ ring.rightNeighbor (winSite s 0) := by
        rw [hnext]
        intro h
        exact absurd (winSite_inj hg.hn s j 1 (by omega) (by omega) h) (by omega)
      exact regdata_away ring C s sam Yl j (winSite s 0) hne1 hne2 (hreg j hj2)

/-- The aligned labelled state.

Consumer: `aligned_strict_cost`. -/
def AlignReg {n : Nat} (ring : DirectedRing n) (C : HeadlineConfiguration n) (s : Fin n)
    (Y0 Y : TopFixedTraceState n) : Prop :=
  PuPinAt ring C s Y0 Y ∧ AlignShape (topClockSpan n) (cellOf s Y)

/-- The state of the sweep, with the static data of its launch state.

Consumer: `aligned_strict_cost`. -/
def SweepReg {n : Nat} (ring : DirectedRing n) (C : HeadlineConfiguration n) (s : Fin n)
    (Y : TopFixedTraceState n) : Prop :=
  ∃ (Yl : TopFixedTraceState n) (sam : Nat → DigitSample (compileAdvice (ceilLogTwo n)) n)
    (exs : Nat → DigitExport (compileAdvice (ceilLogTwo n)) n) (k : Nat),
    k < topClockSpan n ∧ SweepStatic s Yl sam exs ∧
    (∀ j, 1 ≤ j → j < topClockSpan n → (sam j).tail = false) ∧
    SweepDyn ring C s Yl sam k Y

/-- **One row of the sweep**: a letter ends in a strict stop, or keeps the aligned or sweeping
state without raising the potential, and the nominated letter lowers it.

Consumer: `aligned_strict_cost`. -/
theorem sweep_row {n : Nat} (ring : DirectedRing n) (C : HeadlineConfiguration n) (s : Fin n)
    (hg : WinGeo ring C s) (Y0 x : TopFixedTraceState n)
    (hx : AlignReg ring C s Y0 x ∨ SweepReg ring C s x) (hN : NoPrefixStop ring C s x)
    (e : Fin n) :
    topFixedStrictStop ring C s (topFixedTraceNext ring C x e) ∨
    ((AlignReg ring C s Y0 (topFixedTraceNext ring C x e) ∨
        SweepReg ring C s (topFixedTraceNext ring C x e)) ∧
      carryPhi s (topFixedTraceNext ring C x e) ≤ carryPhi s x ∧
      (e = winSite s (if AlignShape (topClockSpan n) (cellOf s x) then 0
          else topClockSpan n - carryPhi s x) →
        carryPhi s (topFixedTraceNext ring C x e) + 1 ≤ carryPhi s x)) := by
  have hr3 := span_ge_three hg.hn
  rcases hx with ⟨hP, hA⟩ | ⟨Yl, sam, exs, k, hk, hstat, htails, hD⟩
  · -- aligned
    have hreach : topClockReached ring C x := markedFrom_reached ring C Y0 x hP.2.1
    have hnext := carry_next_align ring C s hg x hreach hA e
    right
    rw [if_pos hA]
    by_cases he : e = winSite s 0
    · obtain ⟨sam, exs, hstat, htails, hD⟩ := sweep_init ring C s hg Y0 x hP hA
      subst he
      have hk0 := hnext.1 rfl
      refine ⟨Or.inr ⟨x, sam, exs, 0, by omega, hstat, htails, hD⟩, ?_, fun _ => ?_⟩ <;>
        rw [carry_phi_align s x hA, carry_phi_carry s _ 0 hk0] <;> omega
    · have hA' := hnext.2 he
      have hfree : puFree (topClockSpan n) (cellOf s (topFixedTraceNext ring C x e)) := by
        intro j hj
        by_cases hj0 : j = 0
        · subst hj0; rw [hA'.2.1]; simp
        · rw [hA'.2.2 j hj (by omega)]; simp
      refine ⟨Or.inl ⟨pupinAt_next ring C s hg Y0 x e hP hfree, hA'⟩, ?_, fun h => absurd h he⟩
      rw [carry_phi_align s x hA, carry_phi_align s _ hA']
      exact Nat.le_refl _
  · -- sweeping
    have hreach : topClockReached ring C x := markedFrom_reached ring C Yl x hD.2.1
    have hshape := hD.2.2.1
    have hna : ¬ AlignShape (topClockSpan n) (cellOf s x) := fun ha => align_not_carry _ _ _ ha hshape
    have hch : topClockSpan n - carryPhi s x = k := by
      rw [carry_phi_carry s x k hshape]; omega
    rw [if_neg hna, hch]
    have hnext := carry_next_carry ring C s hg x hreach k hshape e
    by_cases he : e = winSite s k
    · by_cases hk1 : k + 1 < topClockSpan n
      · right
        have hD' := sweep_adv ring C s hg Yl x sam k htails hD hk1
        subst he
        refine ⟨Or.inr ⟨Yl, sam, exs, k + 1, hk1, hstat, htails, hD'⟩, ?_, fun _ => ?_⟩ <;>
          rw [carry_phi_carry s x k hshape, carry_phi_carry s _ (k + 1) (hnext.1 rfl hk1)] <;> omega
      · left
        have hke : k = topClockSpan n - 1 := by omega
        subst he
        rw [hke] at hD ⊢
        exact sweep_strict ring C s hg Yl x sam exs hstat hD hN
    · right
      have hD' := sweep_keep ring C s hg Yl x sam k htails hD e he
      refine ⟨Or.inr ⟨Yl, sam, exs, k, hk, hstat, htails, hD'⟩, ?_, fun h => absurd h he⟩
      rw [carry_phi_carry s x k hshape, carry_phi_carry s _ k (hnext.2.2 he)]
      exact Nat.le_refl _

/-- **The aligned completion costs at most `n * (r + 1)`.**

Consumer: `Leader/L3/TopPinnedPhaseFill.lean`. -/
theorem aligned_strict_cost {n : Nat} (ring : DirectedRing n) (C : HeadlineConfiguration n) (s : Fin n)
    (hg : WinGeo ring C s) (Y0 x : TopFixedTraceState n) (hx : AlignReg ring C s Y0 x)
    (hN : NoPrefixStop ring C s x ∨ topFixedStrictStop ring C s x) :
    ∀ T, costNumerator (topFixedTraceNext ring C) (topFixedStrictStop ring C s) x T ≤
      n ^ T * (n * (topClockSpan n + 1)) := by
  have hr3 := span_ge_three hg.hn
  let I : TopFixedTraceState n → Prop := fun Y =>
    (NoPrefixStop ring C s Y ∨ topFixedStrictStop ring C s Y) ∧
      (AlignReg ring C s Y0 Y ∨ SweepReg ring C s Y ∨ topFixedStrictStop ring C s Y)
  have hmain := topFinalCostOfRows (topFixedTraceNext ring C) I (topFixedStrictStop ring C s)
    (carryPhi s)
    (fun Y => winSite s (if AlignShape (topClockSpan n) (cellOf s Y) then 0
      else topClockSpan n - carryPhi s Y))
    (by
      intro y hy hnot e
      have hNy : NoPrefixStop ring C s y := by
        rcases hy.1 with h | h
        · exact h
        · exact absurd h hnot
      have hAy : AlignReg ring C s Y0 y ∨ SweepReg ring C s y := by
        rcases hy.2 with h | h | h
        · exact Or.inl h
        · exact Or.inr h
        · exact absurd h hnot
      refine ⟨?_, ?_⟩
      · by_cases hst : topFixedStrictStop ring C s (topFixedTraceNext ring C y e)
        · exact Or.inr hst
        · exact Or.inl (noPrefixStop_next ring C s y e hNy hst)
      · rcases sweep_row ring C s hg Y0 y hAy hNy e with h | ⟨h, _⟩
        · exact Or.inr (Or.inr h)
        · rcases h with h | h
          · exact Or.inl h
          · exact Or.inr (Or.inl h))
    (by
      intro y hy hnot
      have hAy : AlignReg ring C s Y0 y ∨ SweepReg ring C s y := by
        rcases hy.2 with h | h | h
        · exact Or.inl h
        · exact Or.inr h
        · exact absurd h hnot
      rcases hAy with ⟨_, hA⟩ | ⟨Yl, sam, exs, k, hk, _, _, hD⟩
      · rw [carry_phi_align s y hA]; omega
      · rw [carry_phi_carry s y k hD.2.2.1]; omega)
    (by
      intro y hy hnot e
      have hNy : NoPrefixStop ring C s y := by
        rcases hy.1 with h | h
        · exact h
        · exact absurd h hnot
      have hAy : AlignReg ring C s Y0 y ∨ SweepReg ring C s y := by
        rcases hy.2 with h | h | h
        · exact Or.inl h
        · exact Or.inr h
        · exact absurd h hnot
      rcases sweep_row ring C s hg Y0 y hAy hNy e with h | ⟨_, h2, _⟩
      · exact Or.inl h
      · exact Or.inr h2)
    (by
      intro y hy hnot
      have hNy : NoPrefixStop ring C s y := by
        rcases hy.1 with h | h
        · exact h
        · exact absurd h hnot
      have hAy : AlignReg ring C s Y0 y ∨ SweepReg ring C s y := by
        rcases hy.2 with h | h | h
        · exact Or.inl h
        · exact Or.inr h
        · exact absurd h hnot
      rcases sweep_row ring C s hg Y0 y hAy hNy
          (winSite s (if AlignShape (topClockSpan n) (cellOf s y) then 0
            else topClockSpan n - carryPhi s y)) with h | ⟨_, _, h3⟩
      · exact Or.inl h
      · exact Or.inr (h3 rfl))
  intro T
  have h1 := hmain x ⟨hN, Or.inl hx⟩ T
  rw [carry_phi_align s x hx.2] at h1
  exact h1

end MarkedCells
end L3

#print axioms L3.MarkedCells.sweep_init
#print axioms L3.MarkedCells.sweep_row
#print axioms L3.MarkedCells.aligned_strict_cost
