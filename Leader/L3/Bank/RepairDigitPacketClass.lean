import Leader.L3.Bank.RepairDigitCohortEntry

/-!
# T24 item 1: the generated packet class on one lane

One interior complete pair and one lane, as in `BankRepairDigitCohortDomination` (cells `q < R`
are source outputs, cells `R ≤ q < 2R` target inputs with their carry-live bits).

The class `CohortGen R s lam o` describes several cohorts at once (repair.tex Lemma e-current):

* the OLD cohort in phase `o` (`CohortOldAt`): `o ≤ R` settlement with the top `o` operands
  settled (T23 `CohortSettling`, the cohort sits at its destinations); `R < o ≤ 2R` its carry is
  live at target offset `o - R - 1` with settled operands above (T23 `CohortCarry`, launch and
  consumption); `o = 2R + 1` the terminal edge has fired and the old cohort is gone. The old
  region is the cells from `cohortBottom R o` upward.
* the CHOSEN cohort strictly below the old region (`CohortChosen`): packet `i` (source offset
  `R - 1 - i`) has made `lam i` hops; it is a packet with its tail bit, or settled at its
  destination (only with a settled packet ahead of it), or an UNREAD slot (`U`, token `other`)
  at its source cell with no hop yet. Every other cell between the chosen tail and the old region
  is empty.
* YOUNGER slots: all cells behind the chosen tail are unconstrained.

`cohortGenEdge`: the class is closed under every `cohortEdge` letter (the old phase can only go
up, the ghost `cohortGenGhost` counts the hops), at every state where the chosen tail has not yet
reached its destination (`lam (R - 1) < R`; this holds before (E), `cohortGenPre`,
`chosenUnreadPre`). Once the chosen cohort has arrived it is itself the next old cohort and T23's
settlement / carry stages take over. Materialized packets stay materialized, and an edge at a
packet's cell materializes it.

`cohortGenPost` (E): when the old cohort is gone (`o = 2R + 1`) and every chosen slot has
materialized, `CohortPostStrict R s lam ∧ CohortSettledTop R s` (T22's class and T23's entry
clause) with the same ghost `lam`.

`cohortGenEntry`: an arrived old cohort (`CohortSettling R 0`) with the chosen cohort rearmed in
the source (every source cell unread or a materialized packet that has not moved) is in the class
at phase `0`.
-/

namespace L3.PacketClass

set_option autoImplicit false
set_option linter.unusedSectionVars false

open L3.RenewalReferenceClock
open L3.CohortTail
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting
open L3.CohortDomination
open L3.CohortEntry

/-! ### Literal-row facts -/

theorem cohortPipeRead (bx : Bool) (ox oy : BankRepairDigitOutSh)
    (hx : cohortTokOut ox = .other) :
    cohortTokOut (bankRepairDigitPipeStep bx ox oy).1 = .pkt bx ∧
      (bankRepairDigitPipeStep bx ox oy).2 = oy := by
  cases ox <;> simp_all [cohortTokOut, bankRepairDigitPipeStep]

theorem cohortDelRead (ox : BankRepairDigitOutSh) (iy : BankRepairDigitInSh) (ky : Bool)
    (hx : cohortTokOut ox = .other) :
    cohortTokOut (bankRepairDigitDelStep ox iy ky).1 = .pkt false ∧
      cohortTokIn (bankRepairDigitDelStep ox iy ky).2.1 (bankRepairDigitDelStep ox iy ky).2.2 =
        cohortTokIn iy ky := by
  cases ox <;> cases iy <;> cases ky <;>
    simp_all [cohortTokOut, cohortTokIn, bankRepairDigitDelStep]

theorem cohortPipePktOther (bx : Bool) (ox oy : BankRepairDigitOutSh) (T : Bool)
    (hx : cohortTokOut ox = .pkt T) (hy : cohortTokOut oy = .other) :
    cohortTokOut (bankRepairDigitPipeStep bx ox oy).1 = .pkt T ∧
      cohortTokOut (bankRepairDigitPipeStep bx ox oy).2 = .other := by
  cases bx <;> cases ox <;> cases oy <;> simp_all [cohortTokOut, bankRepairDigitPipeStep]

theorem cohortDelPktOther (ox : BankRepairDigitOutSh) (iy : BankRepairDigitInSh) (ky T : Bool)
    (hx : cohortTokOut ox = .pkt T) (hy : cohortTokIn iy ky = .other) :
    cohortTokOut (bankRepairDigitDelStep ox iy ky).1 = .pkt T ∧
      cohortTokIn (bankRepairDigitDelStep ox iy ky).2.1 (bankRepairDigitDelStep ox iy ky).2.2 =
        .other := by
  cases ox <;> cases iy <;> cases ky <;>
    simp_all [cohortTokOut, cohortTokIn, bankRepairDigitDelStep]

theorem cohortFinPktOther (bx : Bool) (ix : BankRepairDigitInSh) (kx : Bool)
    (iy : BankRepairDigitInSh) (ky T : Bool)
    (hx : cohortTokIn ix kx = .pkt T) (hy : cohortTokIn iy ky = .other) :
    cohortTokIn (bankRepairDigitFinStep bx ix kx iy ky).1
        (bankRepairDigitFinStep bx ix kx iy ky).2.1 = .pkt T ∧
      cohortTokIn (bankRepairDigitFinStep bx ix kx iy ky).2.2.1
        (bankRepairDigitFinStep bx ix kx iy ky).2.2.2 = .other := by
  cases bx <;> cases ix <;> cases kx <;> cases iy <;> cases ky <;>
    simp_all [cohortTokIn, bankRepairDigitFinStep]

/-- An unread slot is served on its own edge: it becomes a packet whose tail bit is the source
border bit; the cell ahead keeps its token. -/
theorem cohortEdgeRead (R k : Nat) (s : CohortLane) (hR : 2 ≤ R) (hk : k < R)
    (hx : cohortTok R s k = .other) :
    cohortTok R (cohortEdge R s k) k = .pkt (decide (k = 0)) ∧
      cohortTok R (cohortEdge R s k) (k + 1) = cohortTok R s (k + 1) := by
  by_cases h1 : k + 1 < R
  · obtain ⟨e1, e2⟩ := cohortTokPipe R k s h1
    rw [cohortTokSrc s hk] at hx
    obtain ⟨m1, m2⟩ := cohortPipeRead (decide (k = 0)) _ (s.out (k + 1)) hx
    rw [e1, e2, m1, m2, cohortTokSrc s h1]
    exact ⟨rfl, rfl⟩
  · have h2 : k + 1 = R := by omega
    obtain ⟨e1, e2⟩ := cohortTokDel R k s h2
    rw [cohortTokSrc s hk] at hx
    obtain ⟨m1, m2⟩ := cohortDelRead _ (s.inp (k + 1)) (s.live (k + 1)) hx
    have hd : decide (k = 0) = false := decide_eq_false (by omega)
    rw [e1, e2, m1, m2, cohortTokTgt s (by omega : R ≤ k + 1), hd]
    exact ⟨rfl, rfl⟩

theorem cohortEdgePktOther (R k : Nat) (s : CohortLane) (T : Bool) (hk : k + 1 < 2 * R)
    (hx : cohortTok R s k = .pkt T) (hy : cohortTok R s (k + 1) = .other) :
    cohortTok R (cohortEdge R s k) k = .pkt T ∧
      cohortTok R (cohortEdge R s k) (k + 1) = .other := by
  by_cases h1 : k + 1 < R
  · have hk0 : k < R := by omega
    obtain ⟨e1, e2⟩ := cohortTokPipe R k s h1
    rw [cohortTokSrc s hk0] at hx
    rw [cohortTokSrc s h1] at hy
    obtain ⟨m1, m2⟩ := cohortPipePktOther (decide (k = 0)) _ _ T hx hy
    rw [e1, e2, m1, m2]
    exact ⟨rfl, rfl⟩
  · by_cases h2 : k + 1 = R
    · have hk0 : k < R := by omega
      obtain ⟨e1, e2⟩ := cohortTokDel R k s h2
      rw [cohortTokSrc s hk0] at hx
      rw [cohortTokTgt s (by omega : R ≤ k + 1)] at hy
      obtain ⟨m1, m2⟩ := cohortDelPktOther _ _ _ T hx hy
      rw [e1, e2, m1, m2]
      exact ⟨rfl, rfl⟩
    · have hRk : R ≤ k := by omega
      obtain ⟨e1, e2⟩ := cohortTokFin R k s hRk hk
      rw [cohortTokTgt s hRk] at hx
      rw [cohortTokTgt s (by omega : R ≤ k + 1)] at hy
      obtain ⟨m1, m2⟩ := cohortFinPktOther (decide (k = R)) _ _ _ _ T hx hy
      rw [e1, e2, m1, m2]
      exact ⟨rfl, rfl⟩

/-- A packet behind an occupied cell stays (a settled cell ahead of a target packet is excluded,
since there the packet may settle). -/
theorem cohortEdgeKeepPkt (R k : Nat) (s : CohortLane) (T : Bool) (hk : k + 1 < 2 * R)
    (hx : cohortTok R s k = .pkt T) (hy : cohortTok R s (k + 1) ≠ .empty)
    (hs : ∀ T', cohortTok R s (k + 1) = .settled T' → k < R) :
    cohortTok R (cohortEdge R s k) k = .pkt T := by
  cases hyt : cohortTok R s (k + 1) with
  | empty => exact absurd hyt hy
  | pkt T' => exact (cohortEdgeOcc R k s T T' hk hx hyt).1
  | settled T' =>
    have hkR := hs T' hyt
    rcases (cohortEdgeSet R k s T T' hk hx hyt).1 with h1 | h1
    · exact h1
    · rw [cohortTokSrc _ hkR] at h1
      exact absurd h1 (cohortTokOutNe _ _)
  | other => exact (cohortEdgePktOther R k s T hk hx hyt).1

/-! ### The chosen cohort below the old region -/

/-- The chosen cohort, strictly below cell `c` (the bottom of the old region). -/
structure CohortChosen (R : Nat) (s : CohortLane) (lam : Nat → Nat) (c : Nat) : Prop where
  two : 2 ≤ R
  cle : c ≤ 2 * R
  le : ∀ i, i < R → lam i ≤ R
  mono : ∀ i, i + 1 < R → lam (i + 1) ≤ lam i
  low : ∀ i, i < R → cohortPos R lam i < c
  pkt : ∀ i, i < R →
    cohortTok R s (cohortPos R lam i) = .pkt (cohortTail R i) ∨
      (cohortTok R s (cohortPos R lam i) = .settled (cohortTail R i) ∧ lam i = R) ∨
      (cohortTok R s (cohortPos R lam i) = .other ∧ lam i = 0)
  top : ∀ i, 0 < i → i < R →
    cohortTok R s (cohortPos R lam i) = .settled (cohortTail R i) →
      cohortTok R s (cohortPos R lam (i - 1)) = .settled (cohortTail R (i - 1))
  gap : ∀ q, q < c → lam (R - 1) < q → (∀ i, i < R → cohortPos R lam i ≠ q) →
    cohortTok R s q = .empty

/-- The ghost hop counter of the generated class: a packet (not an unread slot) hops when its
own edge is drawn and the cell ahead is empty. -/
def cohortGenGhost (R : Nat) (s : CohortLane) (lam : Nat → Nat) (k : Nat) (i : Nat) : Nat :=
  if i < R ∧ lam i < R ∧ cohortPos R lam i = k ∧ cohortTok R s k ≠ .other ∧
      cohortTok R s (k + 1) = .empty then lam i + 1 else lam i

section Chosen

variable {R c : Nat} {s : CohortLane} {lam : Nat → Nat}

theorem chosenChain (h : CohortChosen R s lam c) :
    ∀ a b, a ≤ b → b < R → lam b ≤ lam a := by
  intro a b hab hb
  induction b with
  | zero =>
    have : a = 0 := by omega
    subst this
    exact Nat.le_refl _
  | succ b ih =>
    rcases Nat.eq_or_lt_of_le hab with he | hlt
    · subst he
      exact Nat.le_refl _
    · exact Nat.le_trans (h.mono b hb) (ih (by omega) (by omega))

theorem chosenPosLt (h : CohortChosen R s lam c) {a b : Nat} (hab : a < b) (hb : b < R) :
    cohortPos R lam b < cohortPos R lam a := by
  have := chosenChain h a b (Nat.le_of_lt hab) hb
  unfold cohortPos
  omega

theorem chosenPosInj (h : CohortChosen R s lam c) {a b : Nat} (ha : a < R) (hb : b < R)
    (he : cohortPos R lam a = cohortPos R lam b) : a = b := by
  rcases Nat.lt_trichotomy a b with hab | hab | hab
  · have := chosenPosLt h hab hb
    omega
  · exact hab
  · have := chosenPosLt h hab ha
    omega

theorem chosenPosTail (h : CohortChosen R s lam c) {i : Nat} (hi : i < R) :
    lam (R - 1) ≤ cohortPos R lam i := by
  have := chosenChain h i (R - 1) (by omega) (by omega)
  unfold cohortPos
  omega

theorem chosenOcc (h : CohortChosen R s lam c) {j : Nat} (hj : j < R) :
    cohortTok R s (cohortPos R lam j) ≠ .empty := by
  intro he
  rcases h.pkt j hj with h1 | ⟨h1, -⟩ | ⟨h1, -⟩ <;> rw [h1] at he <;> cases he

/-- An unread chosen slot forces the chosen tail to be short of its destination. -/
theorem chosenUnreadPre (h : CohortChosen R s lam c) {i : Nat} (hi : i < R)
    (hu : cohortTok R s (cohortPos R lam i) = .other) : lam (R - 1) < R := by
  have hR := h.two
  have hc := chosenChain h i (R - 1) (by omega) (by omega)
  rcases h.pkt i hi with h1 | ⟨h1, -⟩ | ⟨-, h1⟩
  · rw [h1] at hu
    cases hu
  · rw [h1] at hu
    cases hu
  · omega

theorem chosenExtend {c' : Nat} (h : CohortChosen R s lam c) (hcc : c ≤ c') (hc' : c' ≤ 2 * R)
    (hnew : ∀ q, c ≤ q → q < c' → cohortTok R s q = .empty) : CohortChosen R s lam c' := by
  refine ⟨h.two, hc', h.le, h.mono, fun i hi => Nat.lt_of_lt_of_le (h.low i hi) hcc, h.pkt,
    h.top, ?_⟩
  intro q hq hlq hnq
  by_cases hqc : q < c
  · exact h.gap q hqc hlq hnq
  · exact hnew q (by omega) hq

theorem genGhostSame {k : Nat}
    (hno : ∀ j, j < R → lam j < R → cohortPos R lam j = k → cohortTok R s k ≠ .other →
      cohortTok R s (k + 1) = .empty → False) :
    cohortGenGhost R s lam k = lam := by
  funext j
  unfold cohortGenGhost
  rw [if_neg]
  rintro ⟨hj, hl, he, ho, hf⟩
  exact hno j hj hl he ho hf

theorem genGhostMove (h : CohortChosen R s lam c) {i k : Nat} (hi : i < R) (hlt : lam i < R)
    (hpi : cohortPos R lam i = k) (hx : cohortTok R s k ≠ .other)
    (hfree : cohortTok R s (k + 1) = .empty) :
    cohortGenGhost R s lam k = cohortUpd lam i (lam i + 1) := by
  funext j
  unfold cohortGenGhost cohortUpd
  by_cases hji : j = i
  · subst hji
    rw [if_pos ⟨hi, hlt, hpi, hx, hfree⟩, if_pos rfl]
  · rw [if_neg hji, if_neg]
    rintro ⟨hj, -, he, -, -⟩
    exact hji (chosenPosInj h hj hi (he.trans hpi.symm))

/-- A change confined to cell `k` and to cells behind the chosen tail, keeping a packet at `k`
a packet (or settled at its destination with a settled packet ahead), keeping a gap cell `k`
empty and a settled cell `k` settled, stays in the class; materialized packets stay
materialized and the packet at `k` (if any) is materialized. -/
theorem chosenRetok {s' : CohortLane} {k : Nat} (h : CohortChosen R s lam c)
    (hframe : ∀ q, q < c → lam (R - 1) ≤ q → q ≠ k → cohortTok R s' q = cohortTok R s q)
    (hgapk : (∀ i, i < R → cohortPos R lam i ≠ k) → lam (R - 1) < k → k < c →
      cohortTok R s' k = .empty)
    (hpk : ∀ i, i < R → cohortPos R lam i = k →
      cohortTok R s' k = .pkt (cohortTail R i) ∨
        (cohortTok R s' k = .settled (cohortTail R i) ∧ lam i = R ∧
          (0 < i → cohortTok R s' (cohortPos R lam (i - 1)) =
            .settled (cohortTail R (i - 1)))))
    (hkeep : ∀ j, j < R → cohortPos R lam j = k → ∀ T, cohortTok R s k = .settled T →
      cohortTok R s' k = .settled T) :
    CohortChosen R s' lam c ∧
      ∀ i, i < R → (cohortPos R lam i = k ∨ cohortTok R s (cohortPos R lam i) ≠ .other) →
        cohortTok R s' (cohortPos R lam i) ≠ .other := by
  have hR := h.two
  have hfr : ∀ i, i < R → cohortPos R lam i ≠ k →
      cohortTok R s' (cohortPos R lam i) = cohortTok R s (cohortPos R lam i) :=
    fun i hi hk => hframe _ (h.low i hi) (chosenPosTail h hi) hk
  refine ⟨⟨hR, h.cle, h.le, h.mono, h.low, ?_, ?_, ?_⟩, ?_⟩
  · intro i hi
    by_cases hk : cohortPos R lam i = k
    · rcases hpk i hi hk with h1 | ⟨h1, h2, -⟩
      · rw [hk]
        exact Or.inl h1
      · rw [hk]
        exact Or.inr (Or.inl ⟨h1, h2⟩)
    · rw [hfr i hi hk]
      exact h.pkt i hi
  · intro i hi0 hi hs
    by_cases hk : cohortPos R lam i = k
    · rw [hk] at hs
      rcases hpk i hi hk with h1 | ⟨-, -, h3⟩
      · rw [h1] at hs
        cases hs
      · exact h3 hi0
    · rw [hfr i hi hk] at hs
      have ht := h.top i hi0 hi hs
      by_cases hk' : cohortPos R lam (i - 1) = k
      · have := hkeep (i - 1) (by omega) hk' _ (by rw [← hk']; exact ht)
        rw [hk']
        exact this
      · rw [hfr (i - 1) (by omega) hk']
        exact ht
  · intro q hq hlq hnq
    by_cases hk : q = k
    · subst hk
      exact hgapk hnq hlq hq
    · rw [hframe q hq (Nat.le_of_lt hlq) hk]
      exact h.gap q hq hlq hnq
  · intro i hi hor
    by_cases hk : cohortPos R lam i = k
    · rw [hk]
      rcases hpk i hi hk with h1 | ⟨h1, -, -⟩ <;> rw [h1] <;> intro hc <;> cases hc
    · rw [hfr i hi hk]
      rcases hor with h1 | h1
      · exact absurd h1 hk
      · exact h1

/-- Packet `i` hops from its cell into the empty cell ahead, inside the chosen region. -/
theorem chosenMovePres {s' : CohortLane} {i : Nat} (h : CohortChosen R s lam c)
    (hi : i < R) (hlt : lam i < R) (hc1 : cohortPos R lam i + 1 < c)
    (hx : cohortTok R s (cohortPos R lam i) = .pkt (cohortTail R i))
    (hfree : cohortTok R s (cohortPos R lam i + 1) = .empty)
    (hframe : ∀ q, q ≠ cohortPos R lam i → q ≠ cohortPos R lam i + 1 →
      cohortTok R s' q = cohortTok R s q)
    (hnew : cohortTok R s' (cohortPos R lam i + 1) = .pkt (cohortTail R i))
    (hold : cohortTok R s' (cohortPos R lam i) =
      if cohortPos R lam i < R ∧ cohortTail R i = true then .other else .empty) :
    CohortChosen R s' (cohortUpd lam i (lam i + 1)) c ∧
      ∀ j, j < R → (cohortPos R lam j = cohortPos R lam i ∨
          cohortTok R s (cohortPos R lam j) ≠ .other) →
        cohortTok R s' (cohortPos R (cohortUpd lam i (lam i + 1)) j) ≠ .other := by
  have hR := h.two
  have hupd : ∀ j, j ≠ i → cohortUpd lam i (lam i + 1) j = lam j := fun j hj => by
    simp [cohortUpd, hj]
  have hupdi : cohortUpd lam i (lam i + 1) i = lam i + 1 := by simp [cohortUpd]
  have hposj : ∀ j, j ≠ i →
      cohortPos R (cohortUpd lam i (lam i + 1)) j = cohortPos R lam j := by
    intro j hj
    unfold cohortPos
    rw [hupd j hj]
  have hposi : cohortPos R (cohortUpd lam i (lam i + 1)) i = cohortPos R lam i + 1 := by
    unfold cohortPos
    rw [hupdi]
    omega
  have hne1 : ∀ j, j < R → j ≠ i → cohortPos R lam j ≠ cohortPos R lam i :=
    fun j hj hji he => hji (chosenPosInj h hj hi he)
  have hne2 : ∀ j, j < R → cohortPos R lam j ≠ cohortPos R lam i + 1 := fun j hj he =>
    chosenOcc h hj (by rw [he]; exact hfree)
  have hfr : ∀ j, j < R → j ≠ i →
      cohortTok R s' (cohortPos R lam j) = cohortTok R s (cohortPos R lam j) :=
    fun j hj hji => hframe _ (hne1 j hj hji) (hne2 j hj)
  refine ⟨⟨hR, h.cle, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro j hj
    by_cases hji : j = i
    · subst hji
      rw [hupdi]
      omega
    · rw [hupd j hji]
      exact h.le j hj
  · intro j hj
    by_cases hji : j = i
    · subst hji
      rw [hupd (j + 1) (by omega), hupdi]
      have := h.mono j hj
      omega
    · by_cases hj1 : j + 1 = i
      · have hfree' : cohortTok R s (cohortPos R lam (j + 1) + 1) = .empty := by
          rw [hj1]
          exact hfree
        have hlt' := chosenPosLt h (show j < j + 1 by omega) hj
        have hne : cohortPos R lam j ≠ cohortPos R lam (j + 1) + 1 := by
          intro he
          exact chosenOcc h (show j < R by omega) (by rw [he]; exact hfree')
        rw [hupd j hji, hj1, hupdi, ← hj1]
        unfold cohortPos at hlt' hne
        omega
      · rw [hupd j hji, hupd (j + 1) hj1]
        exact h.mono j hj
  · intro j hj
    by_cases hji : j = i
    · subst hji
      rw [hposi]
      exact hc1
    · rw [hposj j hji]
      exact h.low j hj
  · intro j hj
    by_cases hji : j = i
    · subst hji
      rw [hposi, hnew]
      exact Or.inl rfl
    · rw [hposj j hji, hupd j hji, hfr j hj hji]
      exact h.pkt j hj
  · intro j hj0 hj hs
    by_cases hji : j = i
    · subst hji
      rw [hposi, hnew] at hs
      cases hs
    · rw [hposj j hji, hfr j hj hji] at hs
      have ht := h.top j hj0 hj hs
      by_cases hj1 : j - 1 = i
      · rw [hj1, hx] at ht
        cases ht
      · rw [hposj (j - 1) hj1, hfr (j - 1) (by omega) hj1]
        exact ht
  · intro q hq hlq hnq
    by_cases hq1 : q = cohortPos R lam i
    · subst hq1
      rw [hold]
      have hnt : ¬ (cohortPos R lam i < R ∧ cohortTail R i = true) := by
        rintro ⟨-, ht⟩
        have hiR : i + 1 = R := by simpa [cohortTail] using ht
        have e : R - 1 = i := by omega
        rw [e, hupdi] at hlq
        unfold cohortPos at hlq
        omega
      rw [if_neg hnt]
    · by_cases hq2 : q = cohortPos R lam i + 1
      · exact absurd (hposi.trans hq2.symm) (hnq i hi)
      · rw [hframe q hq1 hq2]
        apply h.gap q hq
        · have hge : lam (R - 1) ≤ cohortUpd lam i (lam i + 1) (R - 1) := by
            by_cases hR1 : R - 1 = i
            · rw [hR1, hupdi]
              omega
            · rw [hupd _ hR1]
              exact Nat.le_refl _
          omega
        · intro j hj he
          by_cases hji : j = i
          · subst hji
            exact hq1 he.symm
          · exact hnq j hj ((hposj j hji).trans he)
  · intro j hj hor
    by_cases hji : j = i
    · subst hji
      rw [hposi, hnew]
      intro hc
      cases hc
    · rw [hposj j hji, hfr j hj hji]
      rcases hor with h1 | h1
      · exact absurd h1 (hne1 j hj hji)
      · exact h1

/-- The chosen part under one edge: the old region is only seen through its bottom cell `c`,
which is occupied, and settled only at the target delimiter. -/
theorem chosenEdge (h : CohortChosen R s lam c) (hpre : lam (R - 1) < R)
    (hbot : c < 2 * R → cohortTok R s c ≠ .empty ∧ ∀ T, cohortTok R s c = .settled T → c ≤ R)
    (k : Nat) :
    CohortChosen R (cohortEdge R s k) (cohortGenGhost R s lam k) c ∧
      ∀ i, i < R → (cohortPos R lam i = k ∨ cohortTok R s (cohortPos R lam i) ≠ .other) →
        cohortTok R (cohortEdge R s k) (cohortPos R (cohortGenGhost R s lam k) i) ≠ .other := by
  have hR := h.two
  have hc2 := h.cle
  have hpT : cohortPos R lam (R - 1) = lam (R - 1) := by
    unfold cohortPos
    omega
  by_cases hfar : c ≤ k
  · have hno : ∀ j, j < R → cohortPos R lam j ≠ k := fun j hj hpj => by
      have := h.low j hj
      omega
    rw [genGhostSame (fun j hj _ hpj _ _ => hno j hj hpj)]
    apply chosenRetok h
    · intro q hq _ hqk
      exact cohortTokFrame R k q s hqk (by omega)
    · intro _ _ hk
      omega
    · intro i hi hpi
      exact absurd hpi (hno i hi)
    · intro j hj hpj
      exact absurd hpj (hno j hj)
  have hkc : k < c := by omega
  by_cases hp : ∃ i, i < R ∧ cohortPos R lam i = k
  · obtain ⟨i, hi, hpi⟩ := hp
    have huniq : ∀ j, j < R → cohortPos R lam j = k → j = i :=
      fun j hj hpj => chosenPosInj h hj hi (hpj.trans hpi.symm)
    have hpk := h.pkt i hi
    rw [hpi] at hpk
    rcases hpk with hpkt | ⟨hset, hlamR⟩ | ⟨hoth, hl0⟩
    · have hxo : cohortTok R s k ≠ .other := by
        rw [hpkt]
        intro hc
        cases hc
      have hxs : ∀ T, cohortTok R s k ≠ .settled T := by
        intro T
        rw [hpkt]
        intro hc
        cases hc
      by_cases hk1 : k + 1 < c
      · by_cases hfree : cohortTok R s (k + 1) = .empty
        · have hlt : lam i < R := by
            rcases Nat.lt_or_ge (lam i) R with hl | hl
            · exact hl
            · exfalso
              have hli := h.le i hi
              have hi0 : i ≠ 0 := by
                intro he
                subst he
                unfold cohortPos at hpi
                omega
              have hlt2 := chosenPosLt h (show i - 1 < i by omega) hi
              have hle2 := h.le (i - 1) (by omega)
              have he : cohortPos R lam (i - 1) = k + 1 := by
                unfold cohortPos at hlt2 hpi ⊢
                omega
              exact chosenOcc h (show i - 1 < R by omega) (by rw [he]; exact hfree)
          rw [genGhostMove h hi hlt hpi hxo hfree]
          obtain ⟨e1, e2⟩ := cohortEdgeMove R k s _ (by omega) hpkt hfree
          subst hpi
          exact chosenMovePres h hi hlt hk1 hpkt hfree
            (fun q h1 h2 => cohortTokFrame R _ q s h1 h2) e1 e2
        · rw [genGhostSame (fun _ _ _ _ _ hf => hfree hf)]
          obtain ⟨j, hj, hpj⟩ : ∃ j, j < R ∧ cohortPos R lam j = k + 1 :=
            Classical.byContradiction fun hne => hfree (h.gap (k + 1) hk1
              (by have := chosenPosTail h hi; omega)
              (fun j hj hpj => hne ⟨j, hj, hpj⟩))
          have hji : j < i := by
            rcases Nat.lt_or_ge j i with hl | hl
            · exact hl
            · exfalso
              rcases Nat.eq_or_lt_of_le hl with he | he
              · rw [← he] at hpj
                omega
              · have := chosenPosLt h he hj
                omega
          have hch := chosenChain h j i (Nat.le_of_lt hji) hi
          have hj1 : j = i - 1 := by
            unfold cohortPos at hpi hpj
            omega
          have hpkj := h.pkt j hj
          rw [hpj] at hpkj
          rcases hpkj with hpj' | ⟨hsj, hlj⟩ | ⟨hoj, -⟩
          · obtain ⟨e1, e2⟩ := cohortEdgeOcc R k s _ _ (by omega) hpkt hpj'
            apply chosenRetok h
            · intro q _ _ hqk
              by_cases hq1 : q = k + 1
              · rw [hq1, e2, hpj']
              · exact cohortTokFrame R k q s hqk hq1
            · intro hno
              exact absurd hpi (hno i hi)
            · intro i' hi' hpi'
              rw [huniq i' hi' hpi']
              exact Or.inl e1
            · intro _ _ _ T hs
              exact absurd hs (hxs T)
          · obtain ⟨e1, e2⟩ := cohortEdgeSet R k s _ _ (by omega) hpkt hsj
            have hlamR : lam i = R := by
              have := h.le i hi
              unfold cohortPos at hpi hpj
              omega
            apply chosenRetok h
            · intro q _ _ hqk
              by_cases hq1 : q = k + 1
              · rw [hq1, e2, hsj]
              · exact cohortTokFrame R k q s hqk hq1
            · intro hno
              exact absurd hpi (hno i hi)
            · intro i' hi' hpi'
              rw [huniq i' hi' hpi']
              rcases e1 with e1 | e1
              · exact Or.inl e1
              · refine Or.inr ⟨e1, hlamR, fun _ => ?_⟩
                rw [← hj1, hpj, e2]
            · intro _ _ _ T hs
              exact absurd hs (hxs T)
          · obtain ⟨e1, e2⟩ := cohortEdgePktOther R k s _ (by omega) hpkt hoj
            apply chosenRetok h
            · intro q _ _ hqk
              by_cases hq1 : q = k + 1
              · rw [hq1, e2, hoj]
              · exact cohortTokFrame R k q s hqk hq1
            · intro hno
              exact absurd hpi (hno i hi)
            · intro i' hi' hpi'
              rw [huniq i' hi' hpi']
              exact Or.inl e1
            · intro _ _ _ T hs
              exact absurd hs (hxs T)
      · have hk1c : k + 1 = c := by omega
        by_cases hc2R : c < 2 * R
        · obtain ⟨hne, hcs⟩ := hbot hc2R
          have e1 := cohortEdgeKeepPkt R k s _ (by omega) hpkt (by rw [hk1c]; exact hne)
            (fun T' hs => by
              rw [hk1c] at hs
              have := hcs T' hs
              omega)
          rw [genGhostSame (fun _ _ _ _ _ hf => hne (by rw [← hk1c]; exact hf))]
          apply chosenRetok h
          · intro q hq _ hqk
            exact cohortTokFrame R k q s hqk (by omega)
          · intro hno
            exact absurd hpi (hno i hi)
          · intro i' hi' hpi'
            rw [huniq i' hi' hpi']
            exact Or.inl e1
          · intro _ _ _ T hs
            exact absurd hs (hxs T)
        · have hk' : k + 1 = 2 * R := by omega
          have hli := h.le i hi
          have hi0 : i = 0 := by
            unfold cohortPos at hpi
            omega
          have hlam0 : lam i = R := by
            unfold cohortPos at hpi
            omega
          have htail : cohortTail R i = false := by
            simp [cohortTail]
            omega
          rw [htail] at hpkt
          have e1 := cohortEdgeTerm R k s hk' hpkt
          rw [genGhostSame (fun j hj hl hpj _ _ => by
            have := huniq j hj hpj
            subst this
            omega)]
          apply chosenRetok h
          · intro q hq _ hqk
            exact cohortTokFrame R k q s hqk (by omega)
          · intro hno
            exact absurd hpi (hno i hi)
          · intro i' hi' hpi'
            rw [huniq i' hi' hpi', htail]
            exact Or.inr ⟨e1, hlam0, fun h0 => absurd hi0 (by omega)⟩
          · intro _ _ _ T hs
            exact absurd hs (hxs T)
    · have hiR : i + 1 ≠ R := by
        intro he
        have e : R - 1 = i := by omega
        rw [e] at hpre
        omega
      have htail : cohortTail R i = false := by
        simp [cohortTail]
        exact hiR
      rw [htail] at hset
      have hkR : k ≠ R := by
        unfold cohortPos at hpi
        omega
      obtain ⟨e1, e2⟩ := cohortEdgeStay R k s hkR hset
      rw [genGhostSame (fun j hj hl hpj _ _ => by
        have := huniq j hj hpj
        subst this
        omega)]
      apply chosenRetok h
      · intro q hq _ hqk
        by_cases hq1 : q = k + 1
        · subst hq1
          exact e2 (by omega)
        · exact cohortTokFrame R k q s hqk hq1
      · intro hno
        exact absurd hpi (hno i hi)
      · intro i' hi' hpi'
        rw [huniq i' hi' hpi', htail]
        refine Or.inr ⟨e1, hlamR, fun hi0 => ?_⟩
        have hs' : cohortTok R s (cohortPos R lam i) = .settled (cohortTail R i) := by
          rw [hpi, htail]
          exact hset
        have ht := h.top i hi0 hi hs'
        have hl1 := h.le (i - 1) (by omega)
        have hc1 := chosenChain h (i - 1) i (by omega) hi
        have hp1 : cohortPos R lam (i - 1) = k + 1 := by
          unfold cohortPos at hpi ⊢
          omega
        have hlow := h.low (i - 1) (by omega)
        rw [hp1] at ht ⊢
        rw [e2 (by omega)]
        exact ht
      · intro _ _ _ T hs
        rw [hset] at hs
        rw [← hs]
        exact e1
    · have hkR : k < R := by
        unfold cohortPos at hpi
        omega
      obtain ⟨e1, e2⟩ := cohortEdgeRead R k s hR hkR hoth
      rw [genGhostSame (fun _ _ _ _ ho _ => ho hoth)]
      have htl : decide (k = 0) = cohortTail R i := by
        unfold cohortTail
        by_cases hk0 : k = 0
        · rw [decide_eq_true hk0,
            decide_eq_true (show i + 1 = R by unfold cohortPos at hpi; omega)]
        · rw [decide_eq_false hk0,
            decide_eq_false (show ¬ (i + 1 = R) by unfold cohortPos at hpi; omega)]
      apply chosenRetok h
      · intro q _ _ hqk
        by_cases hq1 : q = k + 1
        · rw [hq1, e2]
        · exact cohortTokFrame R k q s hqk hq1
      · intro hno
        exact absurd hpi (hno i hi)
      · intro i' hi' hpi'
        rw [huniq i' hi' hpi', ← htl]
        exact Or.inl e1
      · intro _ _ _ T hs
        rw [hoth] at hs
        cases hs
  · have hno : ∀ j, j < R → cohortPos R lam j ≠ k := fun j hj hpj => hp ⟨j, hj, hpj⟩
    rw [genGhostSame (fun j hj _ hpj _ _ => hno j hj hpj)]
    by_cases hbeh : k < lam (R - 1)
    · have hkR : k < R := by omega
      apply chosenRetok h
      · intro q _ hlq hqk
        by_cases hq1 : q = k + 1
        · subst hq1
          have he : k + 1 = cohortPos R lam (R - 1) := by omega
          have hpkT := h.pkt (R - 1) (by omega)
          rw [← he] at hpkT
          rcases hpkT with h1 | ⟨h1, -⟩ | ⟨-, h1⟩
          · exact cohortEdgeBehind R k s _ hkR (Or.inl h1)
          · exact cohortEdgeBehind R k s _ hkR (Or.inr h1)
          · omega
        · exact cohortTokFrame R k q s hqk hq1
      · intro _ hlt _
        omega
      · intro i' hi' hpi'
        exact absurd hpi' (hno i' hi')
      · intro j hj hpj
        exact absurd hpj (hno j hj)
    · have hgt : lam (R - 1) < k := by
        rcases Nat.lt_or_ge (lam (R - 1)) k with hl | hl
        · exact hl
        · exfalso
          exact hno (R - 1) (by omega) (by omega)
      have hemp := h.gap k hkc hgt hno
      obtain ⟨e1, e2⟩ := cohortEdgeEmpty R k s (by omega) hemp
      apply chosenRetok h
      · intro q hq _ hqk
        by_cases hq1 : q = k + 1
        · subst hq1
          exact e2 (by omega)
        · exact cohortTokFrame R k q s hqk hq1
      · intro _ _ _
        exact e1
      · intro i' hi' hpi'
        exact absurd hpi' (hno i' hi')
      · intro j hj hpj
        exact absurd hpj (hno j hj)

end Chosen

/-! ### The old cohort -/

/-- The bottom cell of the old region in phase `o`. -/
def cohortBottom (R o : Nat) : Nat := if o ≤ R then R else o - 1

/-- The old cohort in phase `o`: settlement (`o ≤ R`), carry (`R < o ≤ 2R`), gone
(`o = 2R + 1`). -/
def CohortOldAt (R o : Nat) (s : CohortLane) : Prop :=
  if o ≤ R then CohortSettling R o s
  else if o ≤ 2 * R then CohortCarry R (o - R) s
  else o = 2 * R + 1

/-- The nominated edge of old phase `o`. -/
def cohortOldEdge (R o : Nat) : Nat :=
  if o < R then 2 * R - 1 - o else if o = R then R else o - 1

section Old

variable {R o : Nat} {s : CohortLane}

theorem cohortBottomSettle (ho : o ≤ R) : cohortBottom R o = R := by
  unfold cohortBottom
  rw [if_pos ho]

theorem cohortBottomCarry (ho : R < o) : cohortBottom R o = o - 1 := by
  unfold cohortBottom
  rw [if_neg (by omega)]

theorem cohortOldSettle (ho : o ≤ R) : CohortOldAt R o s = CohortSettling R o s := by
  unfold CohortOldAt
  rw [if_pos ho]

theorem cohortOldCarry (h1 : R < o) (h2 : o ≤ 2 * R) :
    CohortOldAt R o s = CohortCarry R (o - R) s := by
  unfold CohortOldAt
  rw [if_neg (by omega), if_pos h2]

theorem cohortOldDone (h : 2 * R < o) : CohortOldAt R o s = (o = 2 * R + 1) := by
  unfold CohortOldAt
  rw [if_neg (by omega), if_neg (by omega)]

theorem cohortOldLe (h : CohortOldAt R o s) : o ≤ 2 * R + 1 := by
  by_cases h1 : o ≤ 2 * R
  · omega
  · rw [cohortOldDone (by omega)] at h
    omega

theorem cohortBottomLe (ho : o ≤ 2 * R + 1) : cohortBottom R o ≤ 2 * R := by
  unfold cohortBottom
  split <;> omega

theorem cohortBottomMono {o' : Nat} (h : o ≤ o') : cohortBottom R o ≤ cohortBottom R o' := by
  unfold cohortBottom
  split <;> split <;> omega

theorem cohortOldBottom (hR : 2 ≤ R) (h : CohortOldAt R o s) (hlt : cohortBottom R o < 2 * R) :
    cohortTok R s (cohortBottom R o) ≠ .empty ∧
      ∀ T, cohortTok R s (cohortBottom R o) = .settled T → cohortBottom R o ≤ R := by
  by_cases h1 : o ≤ R
  · rw [cohortBottomSettle h1]
    rw [cohortOldSettle h1] at h
    have := h.1 (R - 1) (by omega)
    rw [show 2 * R - 1 - (R - 1) = R by omega] at this
    refine ⟨?_, fun _ _ => Nat.le_refl R⟩
    rcases this with h2 | h2 <;> rw [h2] <;> intro hc <;> cases hc
  · have h2 : o ≤ 2 * R := by
      rw [cohortBottomCarry (by omega)] at hlt
      omega
    rw [cohortBottomCarry (by omega)]
    rw [cohortOldCarry (by omega) h2, cohortCarryMid (by omega) (by omega)] at h
    have hl := h.1
    rw [show R + (o - R) - 1 = o - 1 by omega] at hl
    rw [cohortTokTgt s (by omega : R ≤ o - 1), hl]
    refine ⟨?_, fun T hc => ?_⟩
    · simp [cohortTokIn]
    · simp [cohortTokIn] at hc

theorem cohortSettlingAll {j : Nat} {T : Bool} (h : CohortSettling R j s)
    (hs : cohortTok R s R = .settled T) : CohortSettling R R s := by
  refine ⟨h.1, h.2.1, fun i _ hi => ?_⟩
  obtain ⟨T', hT'⟩ := cohortTopChain h.2.1 (R - 1 - i) R (Nat.le_refl R) (by omega) ⟨T, hs⟩
  rw [show R + (R - 1 - i) = 2 * R - 1 - i by omega] at hT'
  rcases h.1 i hi with h1 | h1
  · rw [h1] at hT'
    cases hT'
  · exact h1

theorem cohortSettlingOfCarry (h : CohortCarry R 0 s) : CohortSettling R R s := by
  rw [cohortCarryZero] at h
  refine ⟨fun i hi => Or.inr (h i hi), ?_, fun i _ hi => h i hi⟩
  intro q hRq hq1 _
  refine ⟨cohortTail R (2 * R - 1 - (q + 1)), ?_⟩
  have := h (2 * R - 1 - (q + 1)) (by omega)
  rw [show 2 * R - 1 - (2 * R - 1 - (q + 1)) = q + 1 by omega] at this
  exact this

theorem cohortCarryOfSettling (h : CohortSettling R R s) : CohortCarry R 0 s := by
  rw [cohortCarryZero]
  exact fun i hi => h.2.2 i hi hi

/-- The carry leaves its host empty when it moves on (or retires). -/
theorem cohortCarryVacate (hR : 2 ≤ R) {j : Nat} (hj1 : 1 ≤ j) (hjR : j ≤ R)
    (h : CohortCarry R j s) :
    cohortTok R (cohortEdge R s (R + j - 1)) (R + j - 1) = .empty := by
  rw [cohortCarryMid (by omega) hjR] at h
  by_cases hj : j < R
  · have hc1 : R + j - 1 + 1 < 2 * R := by omega
    have hy := h.2 (R + j - 1 + 1) (by omega) hc1
    rw [cohortTokTgt s (by omega : R ≤ R + j - 1 + 1)] at hy
    obtain ⟨ly, iy⟩ := cohortTokInSettled hy
    rw [(cohortTokFin R (R + j - 1) s (by omega) hc1).1, h.1, ly, iy]
    simp [bankRepairDigitFinStep, cohortTokIn]
  · have e : R + j - 1 = 2 * R - 1 := by omega
    rw [e]
    rw [e] at h
    exact cohortCarryLast hR h.1

/-- The old phase under one edge: it can only go up, and the cells it releases are empty. -/
theorem cohortOldEdgeStep (hR : 2 ≤ R) (h : CohortOldAt R o s) (k : Nat) :
    ∃ o', o ≤ o' ∧ CohortOldAt R o' (cohortEdge R s k) ∧
      ∀ q, cohortBottom R o ≤ q → q < cohortBottom R o' →
        cohortTok R (cohortEdge R s k) q = .empty := by
  by_cases h1 : o ≤ R
  · rw [cohortOldSettle h1] at h
    by_cases hRs : ∃ T, cohortTok R s R = .settled T
    · obtain ⟨T, hT⟩ := hRs
      have hall := cohortCarryOfSettling (cohortSettlingAll h hT)
      rw [cohortCarryZero] at hall
      by_cases hk : k = R
      · refine ⟨R + 1, by omega, ?_, ?_⟩
        · rw [hk, cohortOldCarry (by omega) (by omega), cohortCarryMid (by omega) (by omega),
            show R + (R + 1 - R) - 1 = R by omega]
          exact cohortLaunch hR hall
        · intro q h2 h3
          rw [cohortBottomSettle h1] at h2
          rw [cohortBottomCarry (by omega)] at h3
          omega
      · refine ⟨R, h1, ?_, ?_⟩
        · rw [cohortOldSettle (Nat.le_refl R)]
          apply cohortSettlingOfCarry
          rw [cohortCarryZero]
          intro i hi
          rw [cohortAllTok hR hall k hk _ (by omega) (by omega)]
          exact hall i hi
        · intro q h2 h3
          rw [cohortBottomSettle h1] at h2
          rw [cohortBottomSettle (Nat.le_refl R)] at h3
          omega
    · have hRn : ∀ T, cohortTok R s R ≠ .settled T := fun T hT => hRs ⟨T, hT⟩
      refine ⟨o, Nat.le_refl o, ?_, fun q h2 h3 => absurd h3 (by omega)⟩
      rw [cohortOldSettle h1]
      exact cohortSettlingEdge hR h hRn k
  · by_cases h2 : o ≤ 2 * R
    · rw [cohortOldCarry (by omega) h2] at h
      have hj1 : 1 ≤ o - R := by omega
      have hjR : o - R ≤ R := by omega
      by_cases hk : k = R + (o - R) - 1
      · subst hk
        refine ⟨o + 1, by omega, ?_, ?_⟩
        · by_cases hj : o - R < R
          · rw [cohortOldCarry (by omega) (by omega), cohortCarryMid (by omega) (by omega),
              show R + (o + 1 - R) - 1 = R + (o - R) - 1 + 1 by omega]
            have h' := h
            rw [cohortCarryMid (by omega) hjR] at h'
            exact cohortCarryMove (R + (o - R) - 1) (by omega) (by omega) h'
          · rw [cohortOldDone (by omega)]
            omega
        · intro q h3 h4
          rw [cohortBottomCarry (by omega)] at h3
          rw [cohortBottomCarry (by omega)] at h4
          have hq : q = R + (o - R) - 1 := by omega
          rw [hq]
          exact cohortCarryVacate hR hj1 hjR h
      · refine ⟨o, Nat.le_refl o, ?_, fun q h3 h4 => absurd h4 (by omega)⟩
        rw [cohortOldCarry (by omega) h2]
        rw [cohortCarryMid (by omega) hjR] at h ⊢
        exact cohortCarryKeep (R + (o - R) - 1) (by omega) (by omega) h k hk
    · refine ⟨o, Nat.le_refl o, ?_, fun q h3 h4 => absurd h4 (by omega)⟩
      rw [cohortOldDone (by omega)] at h ⊢
      exact h

/-- The nominated edge of a phase `o ≤ 2R` advances the old cohort to phase `o + 1` (in
settlement, unless the next operand is already settled). -/
theorem cohortOldAdvance (hR : 2 ≤ R) (ho : o ≤ 2 * R) (h : CohortOldAt R o s)
    (hn : o < R → ¬ CohortOldAt R (o + 1) s) :
    CohortOldAt R (o + 1) (cohortEdge R s (cohortOldEdge R o)) ∧
      ∀ q, cohortBottom R o ≤ q → q < cohortBottom R (o + 1) →
        cohortTok R (cohortEdge R s (cohortOldEdge R o)) q = .empty := by
  by_cases h1 : o < R
  · have he : cohortOldEdge R o = 2 * R - 1 - o := by
      unfold cohortOldEdge
      rw [if_pos h1]
    rw [he, cohortOldSettle (by omega)]
    rw [cohortOldSettle (by omega)] at h
    have hn' := hn h1
    rw [cohortOldSettle (by omega)] at hn'
    refine ⟨(cohortSettlingStage hR o).2 s h hn', fun q h2 h3 => ?_⟩
    rw [cohortBottomSettle (by omega)] at h2
    rw [cohortBottomSettle (by omega)] at h3
    omega
  · by_cases h2 : o = R
    · have he : cohortOldEdge R o = R := by
        unfold cohortOldEdge
        rw [if_neg h1, if_pos h2]
      rw [he]
      rw [cohortOldSettle (by omega), h2] at h
      have hall := cohortCarryOfSettling h
      rw [cohortCarryZero] at hall
      refine ⟨?_, fun q h3 h4 => ?_⟩
      · rw [cohortOldCarry (by omega) (by omega), cohortCarryMid (by omega) (by omega),
          show R + (o + 1 - R) - 1 = R by omega]
        exact cohortLaunch hR hall
      · rw [cohortBottomSettle (by omega)] at h3
        rw [cohortBottomCarry (by omega)] at h4
        omega
    · have he : cohortOldEdge R o = R + (o - R) - 1 := by
        unfold cohortOldEdge
        rw [if_neg h1, if_neg h2]
        omega
      rw [he]
      rw [cohortOldCarry (by omega) ho] at h
      have hj1 : 1 ≤ o - R := by omega
      have hjR : o - R ≤ R := by omega
      refine ⟨?_, fun q h3 h4 => ?_⟩
      · by_cases hj : o - R < R
        · rw [cohortOldCarry (by omega) (by omega), cohortCarryMid (by omega) (by omega),
            show R + (o + 1 - R) - 1 = R + (o - R) - 1 + 1 by omega]
          have h' := h
          rw [cohortCarryMid (by omega) hjR] at h'
          exact cohortCarryMove (R + (o - R) - 1) (by omega) (by omega) h'
        · rw [cohortOldDone (by omega)]
          omega
      · rw [cohortBottomCarry (by omega)] at h3
        rw [cohortBottomCarry (by omega)] at h4
        have hq : q = R + (o - R) - 1 := by omega
        rw [hq]
        exact cohortCarryVacate hR hj1 hjR h

theorem cohortOldEdgeLt (hR : 2 ≤ R) (ho : o ≤ 2 * R) : cohortOldEdge R o < 2 * R := by
  unfold cohortOldEdge
  split
  · omega
  · split <;> omega

end Old

/-! ### The generated class -/

/-- The generated packet class: the old cohort in phase `o`, the chosen cohort below it with
ghost hop counts `lam`, younger slots unconstrained behind the chosen tail. -/
def CohortGen (R : Nat) (s : CohortLane) (lam : Nat → Nat) (o : Nat) : Prop :=
  CohortOldAt R o s ∧ CohortChosen R s lam (cohortBottom R o)

section Gen

variable {R o : Nat} {s : CohortLane} {lam : Nat → Nat}

/-- Before the old cohort is gone the chosen tail is short of its destination. -/
theorem cohortGenPre (h : CohortGen R s lam o) (ho : o ≤ 2 * R) : lam (R - 1) < R := by
  have hR := h.2.two
  have hb : cohortBottom R o ≤ 2 * R - 1 := by
    unfold cohortBottom
    split <;> omega
  have hl := h.2.low 0 (by omega)
  have hc := chosenChain h.2 0 (R - 1) (by omega) (by omega)
  unfold cohortPos at hl
  omega

theorem cohortGenOfOld (h : CohortGen R s lam o) (hpre : lam (R - 1) < R) (k o' : Nat)
    (ho : o ≤ o') (hold : CohortOldAt R o' (cohortEdge R s k))
    (hnew : ∀ q, cohortBottom R o ≤ q → q < cohortBottom R o' →
      cohortTok R (cohortEdge R s k) q = .empty) :
    CohortGen R (cohortEdge R s k) (cohortGenGhost R s lam k) o' ∧
      ∀ i, i < R → (cohortPos R lam i = k ∨ cohortTok R s (cohortPos R lam i) ≠ .other) →
        cohortTok R (cohortEdge R s k) (cohortPos R (cohortGenGhost R s lam k) i) ≠ .other := by
  have hR := h.2.two
  obtain ⟨hc, hm⟩ := chosenEdge h.2 hpre (cohortOldBottom hR h.1) k
  exact ⟨⟨hold, chosenExtend hc (cohortBottomMono ho) (cohortBottomLe (cohortOldLe hold)) hnew⟩,
    hm⟩

/-- Closure under every edge letter (while the chosen tail is short of its destination): the
old phase only goes up, materialized packets stay materialized, and the packet at the drawn
edge's cell is materialized afterwards. -/
theorem cohortGenEdge (h : CohortGen R s lam o) (hpre : lam (R - 1) < R) (k : Nat) :
    ∃ o', o ≤ o' ∧ CohortGen R (cohortEdge R s k) (cohortGenGhost R s lam k) o' ∧
      ∀ i, i < R → (cohortPos R lam i = k ∨ cohortTok R s (cohortPos R lam i) ≠ .other) →
        cohortTok R (cohortEdge R s k) (cohortPos R (cohortGenGhost R s lam k) i) ≠ .other := by
  obtain ⟨o', ho, hold, hnew⟩ := cohortOldEdgeStep h.2.two h.1 k
  exact ⟨o', ho, cohortGenOfOld h hpre k o' ho hold hnew⟩

/-- The nominated old-phase edge advances the phase. -/
theorem cohortGenAdvance (h : CohortGen R s lam o) (ho : o ≤ 2 * R)
    (hn : o < R → ¬ CohortOldAt R (o + 1) s) :
    CohortGen R (cohortEdge R s (cohortOldEdge R o))
      (cohortGenGhost R s lam (cohortOldEdge R o)) (o + 1) := by
  obtain ⟨hold, hnew⟩ := cohortOldAdvance h.2.two ho h.1 hn
  exact (cohortGenOfOld h (cohortGenPre h ho) _ (o + 1) (by omega) hold hnew).1

theorem cohortPosZero (R i : Nat) : cohortPos R (fun _ => 0) i = R - 1 - i := by
  show R - 1 - i + 0 = R - 1 - i
  omega

/-- Entry: the old cohort has arrived and the chosen cohort is rearmed in the source (every
source cell is unread or a packet that has not moved, the tail at the source border). -/
theorem cohortGenEntry (hR : 2 ≤ R) (h : CohortSettling R 0 s)
    (hsrc : ∀ q, q < R → cohortTok R s q = .other ∨ cohortTok R s q = .pkt (decide (q = 0))) :
    CohortGen R s (fun _ => 0) 0 := by
  refine ⟨by rw [cohortOldSettle (Nat.zero_le _)]; exact h, ?_⟩
  rw [cohortBottomSettle (Nat.zero_le _)]
  refine ⟨hR, by omega, fun _ _ => Nat.zero_le _, fun _ _ => Nat.le_refl _, ?_, ?_, ?_, ?_⟩
  · intro i hi
    rw [cohortPosZero]
    omega
  · intro i hi
    rw [cohortPosZero]
    rcases hsrc (R - 1 - i) (by omega) with h1 | h1
    · exact Or.inr (Or.inr ⟨h1, rfl⟩)
    · left
      rw [h1]
      congr 1
      unfold cohortTail
      by_cases hi0 : R - 1 - i = 0
      · rw [decide_eq_true hi0, decide_eq_true (show i + 1 = R by omega)]
      · rw [decide_eq_false hi0, decide_eq_false (show ¬ (i + 1 = R) by omega)]
  · intro i _ hi hs
    rw [cohortPosZero, cohortTokSrc s (by omega)] at hs
    exact absurd hs (cohortTokOutNe _ _)
  · intro q hq _ hnq
    exfalso
    exact hnq (R - 1 - q) (by omega) (by rw [cohortPosZero]; omega)

/-- (E) at the lane level: once the old cohort is gone and every chosen slot has materialized,
the chosen cohort is post-strict with the same ghost, and the settled operands form a top run. -/
theorem cohortGenPost (h : CohortGen R s lam (2 * R + 1))
    (hm : ∀ i, i < R → cohortTok R s (cohortPos R lam i) ≠ .other) :
    CohortPostStrict R s lam ∧ CohortSettledTop R s := by
  have hc := h.2
  have hR := hc.two
  have hb : cohortBottom R (2 * R + 1) = 2 * R := by
    rw [cohortBottomCarry (by omega)]
    omega
  rw [hb] at hc
  have hpkt : ∀ i, i < R →
      cohortTok R s (cohortPos R lam i) = .pkt (cohortTail R i) ∨
        (cohortTok R s (cohortPos R lam i) = .settled (cohortTail R i) ∧ lam i = R) := by
    intro i hi
    rcases hc.pkt i hi with h1 | h1 | ⟨h1, -⟩
    · exact Or.inl h1
    · exact Or.inr h1
    · exact absurd h1 (hm i hi)
  refine ⟨⟨hR, hc.le, hc.mono, hpkt, hc.gap⟩, ?_⟩
  intro q hRq hq1 hex
  obtain ⟨T, hT⟩ := hex
  have hpT : cohortPos R lam (R - 1) = lam (R - 1) := by
    unfold cohortPos
    omega
  have hlR := hc.le (R - 1) (by omega)
  obtain ⟨i, hi, hpi⟩ : ∃ i, i < R ∧ cohortPos R lam i = q := by
    refine Classical.byContradiction fun hne => ?_
    have hlt : lam (R - 1) < q := by
      rcases Nat.lt_or_ge (lam (R - 1)) q with hl | hl
      · exact hl
      · exact (hne ⟨R - 1, by omega, by omega⟩).elim
    rw [hc.gap q (by omega) hlt (fun i hi hpi => hne ⟨i, hi, hpi⟩)] at hT
    cases hT
  rcases hpkt i hi with h1 | ⟨h1, hl⟩
  · rw [hpi, hT] at h1
    cases h1
  · have hi0 : 0 < i := by
      unfold cohortPos at hpi
      omega
    have ht := hc.top i hi0 hi h1
    have hl1 := hc.le (i - 1) (by omega)
    have hc1 := chosenChain hc (i - 1) i (by omega) hi
    have hp1 : cohortPos R lam (i - 1) = q + 1 := by
      unfold cohortPos at hpi ⊢
      omega
    rw [hp1] at ht
    exact ⟨_, ht⟩

end Gen

end L3.PacketClass

#print axioms L3.PacketClass.cohortPipeRead
#print axioms L3.PacketClass.cohortDelRead
#print axioms L3.PacketClass.cohortPipePktOther
#print axioms L3.PacketClass.cohortDelPktOther
#print axioms L3.PacketClass.cohortFinPktOther
#print axioms L3.PacketClass.cohortEdgeRead
#print axioms L3.PacketClass.cohortEdgePktOther
#print axioms L3.PacketClass.cohortEdgeKeepPkt
#print axioms L3.PacketClass.chosenChain
#print axioms L3.PacketClass.chosenPosLt
#print axioms L3.PacketClass.chosenPosInj
#print axioms L3.PacketClass.chosenPosTail
#print axioms L3.PacketClass.chosenOcc
#print axioms L3.PacketClass.chosenUnreadPre
#print axioms L3.PacketClass.chosenExtend
#print axioms L3.PacketClass.genGhostSame
#print axioms L3.PacketClass.genGhostMove
#print axioms L3.PacketClass.chosenRetok
#print axioms L3.PacketClass.chosenMovePres
#print axioms L3.PacketClass.chosenEdge
#print axioms L3.PacketClass.cohortBottomSettle
#print axioms L3.PacketClass.cohortBottomCarry
#print axioms L3.PacketClass.cohortOldSettle
#print axioms L3.PacketClass.cohortOldCarry
#print axioms L3.PacketClass.cohortOldDone
#print axioms L3.PacketClass.cohortOldLe
#print axioms L3.PacketClass.cohortBottomLe
#print axioms L3.PacketClass.cohortBottomMono
#print axioms L3.PacketClass.cohortOldBottom
#print axioms L3.PacketClass.cohortSettlingAll
#print axioms L3.PacketClass.cohortSettlingOfCarry
#print axioms L3.PacketClass.cohortCarryOfSettling
#print axioms L3.PacketClass.cohortCarryVacate
#print axioms L3.PacketClass.cohortOldEdgeStep
#print axioms L3.PacketClass.cohortOldAdvance
#print axioms L3.PacketClass.cohortOldEdgeLt
#print axioms L3.PacketClass.cohortGenPre
#print axioms L3.PacketClass.cohortGenOfOld
#print axioms L3.PacketClass.cohortGenEdge
#print axioms L3.PacketClass.cohortGenAdvance
#print axioms L3.PacketClass.cohortPosZero
#print axioms L3.PacketClass.cohortGenEntry
#print axioms L3.PacketClass.cohortGenPost
