import Leader.L3.Top.MarkedDebtRows
import Leader.L3.Top.SettledCoverStep

/-!
# Q7 (P.6): the history colouring on the fixed trace and the front-cover theorem

`colourWord` folds the colour step along the word after a cut.  The theorem
`cover_after_coloured` shows: from a coloured cut with every settled input active, the
front-cover invariant (iii) holds at every state reached along any continuation word.
The invariant is not vacuous: its doomed set is the history colouring, not an
existential one.

Consumer: `Leader/L3/TopSettledWork.lean`.
-/

namespace L3
namespace MarkedCells

open Classical

set_option autoImplicit false

/-- Edges outside the window act as the frame, the port cleanup or the port acceptance.

Consumer: `cover_step_machine`. -/
theorem link_shape {n : Nat} (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (s : Fin n) (Z : TopFixedTraceState n) (hg : WinGeo ring C s)
    (hreach : topClockReached ring C Z) (e : Fin n)
    (hnw : ¬ ∃ p, p < topClockSpan n ∧ e = winSite s p) :
    (∀ j, j < topClockSpan n → cellOf s (topFixedTraceNext ring C Z e) j = cellOf s Z j) ∨
    (∀ j, j < topClockSpan n → cellOf s (topFixedTraceNext ring C Z e) j =
      setOne (cellOf s Z) 0 (portClean (cellOf s Z 0)) j) ∨
    ∃ t, ∀ j, j < topClockSpan n → cellOf s (topFixedTraceNext ring C Z e) j =
      setOne (cellOf s Z) 0 (portAccept t (cellOf s Z 0)) j := by
  have hfrz := publicFrozen_reached ring C Z hreach
  have hn2 : 2 ≤ n := by have := hg.hn; omega
  have hr3 := span_ge_three hg.hn
  have hrn := span_lt_n hg.hn
  by_cases hb : e = certSite s (topClockSpan n - 1)
  · have hy : ring.rightNeighbor e = winSite s 0 := by
      rw [hb, rn_certSite]
      unfold winSite
      congr 1
      omega
    have hxl : (Z.1.1 e).l = false := by rw [(hfrz _).1]; exact hg.hl _
    have hyl : (Z.1.1 (ring.rightNeighbor e)).l = false := by
      rw [(hfrz _).1]; exact hg.hl _
    have hyb : (Z.1.1 (ring.rightNeighbor e)).beta = true := by
      rw [hy, (hfrz _).2, winSite_beta ring C s hg.hbad 0 (by omega)]
      simp
    have hresp := siteCell_responder_terminal ring hn2 C Z e hxl hyl hyb
    rw [hy] at hresp
    have haway : ∀ j, 0 < j → j < topClockSpan n →
        cellOf s (topFixedTraceNext ring C Z e) j = cellOf s Z j := by
      intro j hj0 hj
      unfold cellOf
      apply siteCell_away
      · intro h
        rw [hb] at h
        unfold winSite at h
        have := certSite_inj_close s (topClockSpan n - 1) (topClockSpan n + j) (by omega)
          (by omega) h.symm
        omega
      · rw [hy]
        intro h
        have := winSite_inj hg.hn s j 0 (by omega) (by omega) h
        omega
    rcases hresp with hc | ⟨t, hc⟩
    · right; left
      intro j hj
      by_cases hj0 : j = 0
      · subst hj0; simp only [setOne, if_true]; exact hc
      · simp only [setOne, if_neg hj0]; exact haway j (by omega) hj
    · right; right
      refine ⟨t, ?_⟩
      intro j hj
      by_cases hj0 : j = 0
      · subst hj0; simp only [setOne, if_true]; exact hc
      · simp only [setOne, if_neg hj0]; exact haway j (by omega) hj
  · left
    intro j hj
    unfold cellOf
    apply siteCell_away
    · intro h; exact hnw ⟨j, hj, h.symm⟩
    · intro h
      by_cases hj0 : j = 0
      · subst hj0
        apply hb
        apply certSite_pred ring s e (topClockSpan n - 1)
        rw [← h]
        unfold winSite
        congr 1
        omega
      · apply hnw
        refine ⟨j - 1, by omega, ?_⟩
        apply certSite_pred ring s e (topClockSpan n + (j - 1))
        rw [← h]
        unfold winSite
        congr 1
        omega

/-! ### The colouring along a word -/

/-- The window register hit by the edge `e`, if any.

Consumer: `cover_after_coloured`. -/
noncomputable def edgeIdx {n : Nat} (s : Fin n) (e : Fin n) : Option Nat :=
  if h : ∃ p, p < topClockSpan n ∧ e = winSite s p then some (Classical.choose h) else none

/-- One colour step along the fixed trace.

Consumer: `colourWord`. -/
noncomputable def colourNext {n : Nat} (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (s : Fin n) (Z : TopFixedTraceState n) (e : Fin n) (d : Nat → Prop) : Nat → Prop :=
  colourGen (topClockSpan n) (cellOf s Z) (cellOf s (topFixedTraceNext ring C Z e)) d
    (edgeIdx s e)

/-- The colouring of the trace obtained by running the word `w` from the cut `Z`.

Consumer: `cover_after_coloured`. -/
noncomputable def colourWord {n : Nat} (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (s : Fin n) : TopFixedTraceState n → (Nat → Prop) → List (Fin n) → (Nat → Prop)
  | _, d, [] => d
  | Z, d, e :: w =>
      colourWord ring C s (topFixedTraceNext ring C Z e) (colourNext ring C s Z e d) w

/-- The colouring of the coloured cut: every settled input is active.

Consumer: `cover_after_coloured`. -/
def allActive : Nat → Prop := fun _ => False

/-- Auxiliary fact `colourGen_congr` of the colouring.

Consumer: `cover_after_coloured`. -/
theorem colourGen_congr (r : Nat) (cells c1 c2 : Nat → Cell) (d : Nat → Prop)
    (po : Option Nat) (h : ∀ j, j < r → c1 j = c2 j) :
    colourGen r cells c1 d po = colourGen r cells c2 d po := by
  funext k
  unfold colourGen
  apply propext
  constructor
  · rintro ⟨hk, h1, h2, h3⟩
    exact ⟨hk, by rw [← h k hk]; exact h1, h2, h3⟩
  · rintro ⟨hk, h1, h2, h3⟩
    exact ⟨hk, by rw [h k hk]; exact h1, h2, h3⟩

/-- Auxiliary fact `cover_congr` of the colouring.

Consumer: `cover_after_coloured`. -/
theorem cover_congr (r : Nat) (c1 c2 : Nat → Cell) (d : Nat → Prop)
    (h : ∀ j, j < r → c1 j = c2 j) (hd : ∀ u, d u → u < r)
    (hc : Cover r c1 d) : Cover r c2 d := by
  intro u hu
  have hur := hd u hu
  obtain ⟨h0, h1, h2⟩ := hc u hu
  refine ⟨h0, by rw [← h u hur]; exact h1, ?_⟩
  rw [← h (u - 1) (by omega)]
  exact h2

/-- Auxiliary fact `colourGen_lt` of the colouring.

Consumer: `cover_after_coloured`. -/
theorem colourGen_lt (r : Nat) (cells c1 : Nat → Cell) (d : Nat → Prop) (po : Option Nat) :
    ∀ u, colourGen r cells c1 d po u → u < r := fun _ h => h.1

/-- Auxiliary fact `noInh_congr` of the colouring.

Consumer: `cover_after_coloured`. -/
theorem noInh_congr (r : Nat) (c1 c2 : Nat → Cell) (h : ∀ j, j < r → c1 j = c2 j)
    (hn : NoInh r c1) : NoInh r c2 := by
  intro j hj
  rw [← h j hj]
  exact hn j hj

/-- Auxiliary fact `edgeIdx_window` of the colouring.

Consumer: `cover_after_coloured`. -/
theorem edgeIdx_window {n : Nat} (hn : 5 ≤ n) (s : Fin n) (p : Nat) (hp : p < topClockSpan n) :
    edgeIdx s (winSite s p) = some p := by
  have hex : ∃ q, q < topClockSpan n ∧ winSite s p = winSite s q := ⟨p, hp, rfl⟩
  unfold edgeIdx
  rw [dif_pos hex]
  have hs := Classical.choose_spec hex
  have := winSite_inj hn s p (Classical.choose hex) (by omega) (by omega) hs.2
  exact congrArg some this.symm

/-- Auxiliary fact `edgeIdx_other` of the colouring.

Consumer: `cover_after_coloured`. -/
theorem edgeIdx_other {n : Nat} (s : Fin n) (e : Fin n)
    (h : ¬ ∃ p, p < topClockSpan n ∧ e = winSite s p) : edgeIdx s e = none := by
  unfold edgeIdx
  rw [dif_neg h]

/-- The joint invariant of a colouring along the trace.

Consumer: `cover_after_coloured`. -/
def ColourInv {n : Nat} (s : Fin n) (Z : TopFixedTraceState n) (d : Nat → Prop) : Prop :=
  Inv (topClockSpan n) (cellOf s Z) ∧ NoInh (topClockSpan n) (cellOf s Z) ∧
    Cover (topClockSpan n) (cellOf s Z) d ∧ (∀ u, d u → u < topClockSpan n)

/-- One edge preserves the colouring invariant.

Consumer: `cover_word`. -/
theorem cover_step_machine {n : Nat} (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (s : Fin n) (hg : WinGeo ring C s) (Z : TopFixedTraceState n)
    (hreach : topClockReached ring C Z) (d : Nat → Prop) (e : Fin n)
    (h : ColourInv s Z d) :
    ColourInv s (topFixedTraceNext ring C Z e) (colourNext ring C s Z e d) := by
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
    rw [ColourInv, hcol]
    refine ⟨inv_congr _ _ _ (fun j hj => (hag j hj).symm)
        (inv_step _ hr2 _ _ hinv hstep),
      noInh_congr _ _ _ (fun j hj => (hag j hj).symm) (noInh_step _ _ _ hni hstep),
      cover_congr _ _ _ _ (fun j hj => (hag j hj).symm) (fun u hu => hu.1)
        (cover_edge_step _ p hr2 hp _ d hinv hni hcov),
      fun u hu => hu.1⟩
  · have hidx := edgeIdx_other s e hw
    have hcol : colourNext ring C s Z e d = colourGen (topClockSpan n) (cellOf s Z)
        (cellOf s (topFixedTraceNext ring C Z e)) d none := by
      unfold colourNext; rw [hidx]
    rw [ColourInv, hcol]
    rcases link_shape ring C s Z hg hreach e hw with hag | hag | ⟨t, hag⟩
    · have hcg : colourGen (topClockSpan n) (cellOf s Z)
          (cellOf s (topFixedTraceNext ring C Z e)) d none =
          colourGen (topClockSpan n) (cellOf s Z) (cellOf s Z) d none :=
        colourGen_congr _ _ _ _ _ _ hag
      rw [hcg]
      refine ⟨inv_congr _ _ _ (fun j hj => (hag j hj).symm) hinv,
        noInh_congr _ _ _ (fun j hj => (hag j hj).symm) hni,
        cover_congr _ _ _ _ (fun j hj => (hag j hj).symm) (fun u hu => hu.1)
          (cover_port _ hr2 _ _ d hinv hni hcov (Or.inl rfl)),
        fun u hu => hu.1⟩
    · have hcg : colourGen (topClockSpan n) (cellOf s Z)
          (cellOf s (topFixedTraceNext ring C Z e)) d none =
          colourGen (topClockSpan n) (cellOf s Z)
            (setOne (cellOf s Z) 0 (portClean (cellOf s Z 0))) d none :=
        colourGen_congr _ _ _ _ _ _ hag
      rw [hcg]
      refine ⟨inv_congr _ _ _ (fun j hj => (hag j hj).symm)
          (inv_step _ hr2 _ _ hinv Step.clean),
        noInh_congr _ _ _ (fun j hj => (hag j hj).symm) (noInh_step _ _ _ hni Step.clean),
        cover_congr _ _ _ _ (fun j hj => (hag j hj).symm) (fun u hu => hu.1)
          (cover_port _ hr2 _ _ d hinv hni hcov (Or.inr (Or.inl rfl))),
        fun u hu => hu.1⟩
    · have hcg : colourGen (topClockSpan n) (cellOf s Z)
          (cellOf s (topFixedTraceNext ring C Z e)) d none =
          colourGen (topClockSpan n) (cellOf s Z)
            (setOne (cellOf s Z) 0 (portAccept t (cellOf s Z 0))) d none :=
        colourGen_congr _ _ _ _ _ _ hag
      rw [hcg]
      refine ⟨inv_congr _ _ _ (fun j hj => (hag j hj).symm)
          (inv_step _ hr2 _ _ hinv (Step.accept t)),
        noInh_congr _ _ _ (fun j hj => (hag j hj).symm) (noInh_step _ _ _ hni (Step.accept t)),
        cover_congr _ _ _ _ (fun j hj => (hag j hj).symm) (fun u hu => hu.1)
          (cover_port _ hr2 _ _ d hinv hni hcov (Or.inr (Or.inr ⟨t, rfl⟩))),
        fun u hu => hu.1⟩

/-- The colouring invariant along every word.

Consumer: `cover_after_coloured`. -/
theorem cover_word {n : Nat} (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (s : Fin n) (hg : WinGeo ring C s) :
    ∀ (w : List (Fin n)) (Z : TopFixedTraceState n), topClockReached ring C Z →
      ∀ d, ColourInv s Z d →
        ColourInv s (w.foldl (topFixedTraceNext ring C) Z) (colourWord ring C s Z d w) := by
  intro w
  induction w with
  | nil => intro Z _ d h; exact h
  | cons e rest ih =>
      intro Z hreach d h
      exact ih _ (topClockReachedNext ring C Z e hreach) _
        (cover_step_machine ring C s hg Z hreach d e h)

/-- A coloured cut has no inherited carry.

Consumer: `cover_after_coloured`. -/
theorem noInh_of_gap {n : Nat} (s : Fin n) (Y : TopFixedTraceState n)
    (hgap : topClockConcreteGeneratedCarryGap s Y) :
    NoInh (topClockSpan n) (cellOf s Y) := by
  intro j hj
  unfold cellOf siteCell
  simp only
  rcases hq : (Y.1.1 (winSite s j)).qCarry with _ | ⟨a, b⟩
  · simp [absCar]
  · have hL : (topClockConcreteCarryAt s Y ⟨j, hj⟩).isL = true := by
      unfold topClockConcreteCarryAt winSite at *
      simp [hq, QCarry.isL]
    obtain ⟨_, _, _, ledger, hl, hi⟩ := hgap ⟨j, hj⟩ hL
    simp only [winSite] at hl ⊢
    rw [hl]
    simp [absCar, hi]

/-- **The front cover (paper (iii)), with the history colouring.**  From a coloured cut,
with every settled input active, the cover invariant holds at every state reached along
any continuation word: every doomed input has an erasure front, or a doomed input, on its
left.

Consumer: `Leader/L3/TopSettledWork.lean`. -/
theorem cover_after_coloured {n : Nat} (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (s : Fin n) (hg : WinGeo ring C s) (Y0 : TopFixedTraceState n)
    (hcol : topClockConcreteColoured ring C s Y0) (w : List (Fin n)) :
    ColourInv s (w.foldl (topFixedTraceNext ring C) Y0) (colourWord ring C s Y0 allActive w) := by
  obtain ⟨hreach, _, _, hgap, _, _⟩ := hcol
  apply cover_word ring C s hg w Y0 hreach
  refine ⟨inv_reached ring C s hg Y0 hreach, noInh_of_gap s Y0 hgap, ?_, ?_⟩
  · intro u hu; exact absurd hu (by simp [allActive])
  · intro u hu; exact absurd hu (by simp [allActive])

/-- Unfolding the cover: a doomed input is the right end of a run of doomed settled inputs
whose left end has an erasure front immediately to its left.

Consumer: `Leader/L3/TopSettledWork.lean`. -/
theorem cover_run (r : Nat) (cells : Nat → Cell) (d : Nat → Prop) (hc : Cover r cells d) :
    ∀ u, d u → ∃ left, left < u ∧ (cells left).i = .x ∧
      ∀ k, left < k → k ≤ u → d k ∧ (cells k).i.isS = true := by
  intro u
  induction u using Nat.strongRecOn with
  | _ u ih =>
      intro hu
      obtain ⟨h0, hS, hleft⟩ := hc u hu
      rcases hleft with hx | hd
      · refine ⟨u - 1, by omega, hx, ?_⟩
        intro k hk1 hk2
        have : k = u := by omega
        subst this
        exact ⟨hu, hS⟩
      · obtain ⟨left, hl, hx, hk⟩ := ih (u - 1) (by omega) hd
        refine ⟨left, by omega, hx, ?_⟩
        intro k hk1 hk2
        by_cases hku : k = u
        · subst hku; exact ⟨hu, hS⟩
        · exact hk k hk1 (by omega)

end MarkedCells
end L3

#print axioms L3.MarkedCells.cover_step_machine
#print axioms L3.MarkedCells.cover_word
#print axioms L3.MarkedCells.cover_after_coloured
#print axioms L3.MarkedCells.cover_run
#print axioms L3.MarkedCells.link_shape
