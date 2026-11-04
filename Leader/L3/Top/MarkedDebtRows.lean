import Leader.L3.Top.MarkedLink
import Leader.L3.Top.MarkedGood
import Leader.L3.Top.ClockCuts
import Leader.L3.Top.MarkedDebt

/-!
# Q7: the marked-debt phase P.4--P.5 from the physical window rows

The potential is the abstract rank `rank (topClockSpan n)` of the window cells.
This module proves, at every eligible entrance:

* the invariants of a fresh carry along every reached fixed trace;
* the four rows (start, positive, nonincrease, nominated edge) on the states
  that extend a permanent first-tail cut;
* `topClockMarkedDebtPhase_holds : TopClockMarkedDebtPhase ring C s
  (topClockMarkedClasses ring C s)`.

Consumer: `TopClockPhaseBundle.marked` (TopClockAssembly).
-/

namespace L3
namespace MarkedCells

set_option autoImplicit false

open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

/-- The rank reads only the first `r` registers.

Consumer: `topClockMarkedDebtPhase_holds`. -/
theorem rank_congr (r : Nat) (c1 c2 : Nat → Cell) (h : ∀ j, j < r → c1 j = c2 j) :
    rank r c1 = rank r c2 := by
  unfold rank
  exact (scan_congr r c2 c1 r 0 false false (fun i _ hi => h i (by omega))).1

/-- The invariants read only the first `r` registers.

Consumer: `topClockMarkedDebtPhase_holds`. -/
theorem inv_congr (r : Nat) (c1 c2 : Nat → Cell) (h : ∀ j, j < r → c1 j = c2 j)
    (hi : Inv r c1) : Inv r c2 := by
  obtain ⟨hA, hU⟩ := hi
  constructor
  · intro j hj hf
    rw [← h j hj] at hf
    obtain ⟨h1, h2⟩ := hA j hj hf
    refine ⟨by rw [← h j hj]; exact h1, ?_⟩
    intro i hii
    rw [← h i (by omega)]
    exact h2 i hii
  · intro j k hj hk hfj hfk
    rw [← h j hj] at hfj
    rw [← h k hk] at hfk
    exact hU j k hj hk hfj hfk

/-- The trace component of a folded word.

Consumer: `topClockMarkedDebtPhase_holds`. -/
theorem topFixedTraceRun_snd_word {n : Nat} (ring : DirectedRing n) (C : HeadlineConfiguration n) :
    ∀ (w : List (Fin n)) (Z : TopFixedTraceState n),
      (w.foldl (topFixedTraceNext ring C) Z).2 = Z.2 ++ w := by
  intro w
  induction w with
  | nil => intro Z; simp
  | cons e rest ih =>
      intro Z
      simp only [List.foldl_cons]
      rw [ih]
      simp [topFixedTraceNext]

/-- The trace component of a run.

Consumer: `topClockMarkedDebtPhase_holds`. -/
theorem topFixedTraceRun_snd {n : Nat} (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (w : List (Fin n)) : (topFixedTraceRun ring C w).2 = w := by
  unfold topFixedTraceRun
  rw [topFixedTraceRun_snd_word]
  simp

/-- States that extend a permanent first-tail cut along the fixed word.

Consumer: `topClockMarkedDebtPhase_holds`. -/
def MarkedDown {n : Nat} (ring : DirectedRing n) (C : HeadlineConfiguration n) (s : Fin n)
    (Y : TopFixedTraceState n) : Prop :=
  ∃ Y0 : TopFixedTraceState n, topFreshTailPermanentCut ring C s Y0 ∧
    ∃ w : List (Fin n), Y = topFixedTraceRun ring C (Y0.2 ++ w)

/-- A permanent first-tail cut extends itself.

Consumer: `topClockMarkedDebtPhase_holds`. -/
theorem markedDown_start {n : Nat} (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (s : Fin n) (Y0 : TopFixedTraceState n) (h : topFreshTailPermanentCut ring C s Y0) :
    MarkedDown ring C s Y0 := by
  refine ⟨Y0, h, [], ?_⟩
  rw [List.append_nil]
  exact h.1

/-- The class of extensions is closed under edges.

Consumer: `topClockMarkedDebtPhase_holds`. -/
theorem markedDown_next {n : Nat} (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (s : Fin n) (Y : TopFixedTraceState n) (e : Fin n) (h : MarkedDown ring C s Y) :
    MarkedDown ring C s (topFixedTraceNext ring C Y e) := by
  obtain ⟨Y0, hY0, w, hw⟩ := h
  refine ⟨Y0, hY0, w ++ [e], ?_⟩
  rw [← List.append_assoc, topFixedTraceRunAppendWord ring C (Y0.2 ++ w) [e], ← hw]
  rfl

/-- Extensions of a cut are reached cuts.

Consumer: `topClockMarkedDebtPhase_holds`. -/
theorem markedDown_reached {n : Nat} (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (s : Fin n) (Y : TopFixedTraceState n) (h : MarkedDown ring C s Y) :
    topClockReached ring C Y := by
  obtain ⟨Y0, _, w, hw⟩ := h
  unfold topClockReached
  rw [hw, topFixedTraceRun_snd]

/-- Extensions of a permanent cut are pure.

Consumer: `topClockMarkedDebtPhase_holds`. -/
theorem markedDown_pure {n : Nat} (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (s : Fin n) (Y : TopFixedTraceState n) (h : MarkedDown ring C s Y) :
    topClockConcretePureCohorts s Y := by
  obtain ⟨Y0, hY0, w, hw⟩ := h
  rw [hw]
  exact topClockPureCohortsOfPermanent ring C s Y0 hY0 w

/-! ### The invariants hold along every reached trace -/

theorem inv_initial {n : Nat} (C : HeadlineConfiguration n) (s : Fin n) :
    Inv (topClockSpan n)
      (cellOf s (((C, digitAuditInitial (piD C)), []) : TopFixedTraceState n)) := by
  have hnf : ∀ j, (cellOf s (((C, digitAuditInitial (piD C)), []) : TopFixedTraceState n) j).c
      ≠ .fresh := by
    intro j
    unfold cellOf siteCell
    simp only
    cases hq : (C (winSite s j)).qCarry with
    | OFF => simp [absCar]
    | L a b =>
        simp [absCar, digitAuditInitial, digitGhostInitial, DigitGhost.initial,
          DigitLaneGhost.initial, digitLaneView, piD, ProjD.ofAgent, hq, QCarry.isL]
  constructor
  · intro j _ hf; exact absurd hf (hnf j)
  · intro j k _ _ hf; exact absurd hf (hnf j)

/-- The invariants along a word.

Consumer: `topClockMarkedDebtPhase_holds`. -/
theorem inv_word {n : Nat} (ring : DirectedRing n) (C : HeadlineConfiguration n) (s : Fin n)
    (hg : WinGeo ring C s) :
    ∀ (w : List (Fin n)) (Z : TopFixedTraceState n), topClockReached ring C Z →
      Inv (topClockSpan n) (cellOf s Z) →
      Inv (topClockSpan n) (cellOf s (w.foldl (topFixedTraceNext ring C) Z)) := by
  intro w
  induction w with
  | nil => intro Z _ h; exact h
  | cons e rest ih =>
      intro Z hreach hinv
      simp only [List.foldl_cons]
      apply ih _ (topClockReachedNext ring C Z e hreach)
      obtain ⟨cells', hstep, hagree⟩ := link_step ring C s Z hg hreach e
      have hr3 := span_ge_three hg.hn
      exact inv_congr _ _ _ (fun j hj => (hagree j hj).symm)
        (inv_step _ (by omega) _ _ hinv hstep)

/-- The invariants at every reached cut.

Consumer: `topClockMarkedDebtPhase_holds`. -/
theorem inv_reached {n : Nat} (ring : DirectedRing n) (C : HeadlineConfiguration n) (s : Fin n)
    (hg : WinGeo ring C s) (Z : TopFixedTraceState n) (h : topClockReached ring C Z) :
    Inv (topClockSpan n) (cellOf s Z) := by
  have h0 := inv_word ring C s hg Z.2 (((C, digitAuditInitial (piD C)), []))
    (by unfold topClockReached; rfl) (inv_initial C s)
  unfold topClockReached at h
  rw [h]
  exact h0

/-! ### From the abstract cells back to the physical registers -/

theorem siteCell_isP {n : Nat} (Z : TopFixedTraceState n) (v : Fin n) :
    (siteCell Z v).i.isP = (Z.1.1 v).qIn.isP := by
  rcases h : (Z.1.1 v).qIn with _ | _ | ⟨a, t⟩ | ⟨a, t⟩ <;> (try cases t) <;>
    simp [siteCell, absIn, Inp.isP, InTok.isP, h]

/-- A live carry has a nonzero class.

Consumer: `topClockMarkedDebtPhase_holds`. -/
theorem absCar_L_ne_off {c : Compiled} {n : Nat} (a b : Bool)
    (g : Option (DigitCarryGhost c n)) : absCar (QCarry.L a b) g ≠ Car.off := by
  rcases g with _ | l
  · simp [absCar]
  · simp only [absCar]
    by_cases h : l.inherited.isNone = true
    · simp [h]
    · simp [h]

/-- A site cell has a live carry exactly when the register does.

Consumer: `topClockMarkedDebtPhase_holds`. -/
theorem siteCell_carry_on {n : Nat} (Z : TopFixedTraceState n) (v : Fin n) :
    (siteCell Z v).c ≠ .off ↔ (Z.1.1 v).qCarry.isL = true := by
  unfold siteCell
  simp only
  rcases hq : (Z.1.1 v).qCarry with _ | ⟨c, e⟩
  · simp [absCar, QCarry.isL]
  · simp [absCar_L_ne_off, QCarry.isL]

/-- An obstacle cell is a settled input, a front, or a live carry.

Consumer: `topClockMarkedDebtPhase_holds`. -/
theorem siteCell_obC {n : Nat} (Z : TopFixedTraceState n) (v : Fin n) :
    obC (siteCell Z v) = true ↔
      ((Z.1.1 v).qIn.isS = true ∨ (Z.1.1 v).qIn = .X ∨ (Z.1.1 v).qCarry.isL = true) := by
  have hc := siteCell_carry_on Z v
  unfold obC
  rw [← isS_link Z v]
  have hx : (siteCell Z v).i = .x ↔ (Z.1.1 v).qIn = .X := by
    rcases h : (Z.1.1 v).qIn with _ | _ | ⟨a, t⟩ | ⟨a, t⟩ <;> (try cases t) <;>
      simp [siteCell, absIn, h]
  simp only [Bool.or_eq_true, decide_eq_true_eq]
  rw [hx, hc]
  simp [or_assoc]

/-- An empty cell is an empty register.

Consumer: `topClockMarkedDebtPhase_holds`. -/
theorem siteCell_e {n : Nat} (Z : TopFixedTraceState n) (v : Fin n) :
    (siteCell Z v).i = .e ↔ (Z.1.1 v).qIn = .E := by
  rcases h : (Z.1.1 v).qIn with _ | _ | ⟨a, t⟩ | ⟨a, t⟩ <;> (try cases t) <;>
    simp [siteCell, absIn, h]

/-- An empty or pending cell is an empty or pending register.

Consumer: `topClockMarkedDebtPhase_holds`. -/
theorem siteCell_ep {n : Nat} (Z : TopFixedTraceState n) (v : Fin n) :
    EP (siteCell Z v) ↔
      ((Z.1.1 v).qIn.isE = true ∨ (Z.1.1 v).qIn.isP = true) := by
  unfold EP
  rw [siteCell_e, siteCell_isP]
  rcases h : (Z.1.1 v).qIn with _ | _ | ⟨a, t⟩ | ⟨a, t⟩ <;> simp [InTok.isE, h]

/-- A fresh cell has a ledger without inheritance.

Consumer: `topClockMarkedDebtPhase_holds`. -/
theorem siteCell_fresh {n : Nat} (Z : TopFixedTraceState n) (v : Fin n)
    (h : (siteCell Z v).c = .fresh) :
    ∃ ledger : DigitCarryGhost (compileAdvice (ceilLogTwo n)) n,
      (Z.1.2.current v).comparison.carry = some ledger ∧ ledger.inherited = none := by
  unfold siteCell at h
  simp only at h
  rcases hq : (Z.1.1 v).qCarry with _ | ⟨c, e⟩
  · rw [hq] at h; simp [absCar] at h
  · rw [hq] at h
    simp only [absCar] at h
    rcases hg : (Z.1.2.current v).comparison.carry with _ | l
    · rw [hg] at h; simp at h
    · rw [hg] at h
      simp only at h
      refine ⟨l, rfl, ?_⟩
      by_cases hl : l.inherited.isNone = true
      · exact Option.isNone_iff_eq_none.mp hl
      · simp [hl] at h

/-! ### Rank zero is the coloured cut -/

theorem rank_zero_coloured {n : Nat} (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (s : Fin n) (hg : WinGeo ring C s) (Y : TopFixedTraceState n)
    (hdown : MarkedDown ring C s Y) (h0 : rank (topClockSpan n) (cellOf s Y) = 0) :
    topClockConcreteColoured ring C s Y := by
  have hreach := markedDown_reached ring C s Y hdown
  have hinv := inv_reached ring C s hg Y hreach
  have hr3 := span_ge_three hg.hn
  have hbar := rank_zero_barrier _ _ h0
  have hgap := rank_zero_gap _ _ hinv h0
  rw [topClockColouredIff]
  refine ⟨hreach, markedDown_pure ring C s Y hdown, ?_, ?_, ?_⟩
  · -- the moving barrier
    intro i j hP hobs
    have := hbar i.val j.val i.isLt j.isLt
      (by
        have h1 := siteCell_isP Y (certSite s (topClockSpan n + i.val))
        unfold topClockConcreteInputAt at hP
        unfold cellOf winSite
        rw [h1]; exact hP)
      (by
        unfold cellOf winSite
        apply (siteCell_obC Y _).mpr
        unfold topClockConcreteInputAt topClockConcreteCarryAt at hobs
        rcases hobs with h | h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr h))
    exact this
  · -- the generated carry gap
    intro j hL
    have hon : (cellOf s Y j.val).c ≠ .off := by
      unfold cellOf winSite
      exact (siteCell_carry_on Y _).mpr hL
    obtain ⟨hfresh, hhost, hleft, huniq⟩ := hgap j.val j.isLt hon
    refine ⟨?_, ?_, ?_, ?_⟩
    · unfold topClockConcreteInputAt
      unfold cellOf winSite at hhost
      exact (siteCell_e Y _).mp hhost
    · intro i hij
      unfold topClockConcreteInputAt
      have := hleft i.val hij
      unfold cellOf winSite at this
      exact (siteCell_ep Y _).mp this
    · intro k hk
      apply Fin.ext
      apply huniq k.val k.isLt
      unfold cellOf winSite
      exact (siteCell_carry_on Y _).mpr hk
    · have hf : (siteCell Y (certSite s (topClockSpan n + j.val))).c = .fresh := by
        unfold cellOf winSite at hfresh
        exact hfresh
      exact siteCell_fresh Y _ hf
  · -- no terminal reseed
    intro e ⟨j, hj⟩ hnew
    obtain ⟨cells', hstep, hagree⟩ := link_step ring C s Y hg hreach e
    have hlast : topClockSpan n - 1 < topClockSpan n := by omega
    have hnewS : (cells' (topClockSpan n - 1)).i.isS = true := by
      rw [← hagree _ hlast]
      unfold cellOf winSite
      rw [isS_link]
      have : topClockSpan n + (topClockSpan n - 1) = topClockSpan n + (topClockSpan n - 1) := rfl
      exact hnew
    have hS : ∃ q, q < topClockSpan n ∧ (cellOf s Y q).i.isS = true := by
      refine ⟨j.val, j.isLt, ?_⟩
      unfold cellOf winSite
      rw [isS_link]
      exact hj
    have := noReseed_abstract (topClockSpan n) (by omega) _ _ hbar hS hstep hnewS
    unfold cellOf winSite at this
    rw [isS_link] at this
    exact this

/-- The nominated edge of a state: the edge of the register chosen by the abstract
rightmost-obstruction argument.

Consumer: `TopClockPhaseBundle.marked` (TopClockAssembly). -/
noncomputable def chosenEdge {n : Nat} (s : Fin n) (Y : TopFixedTraceState n) : Fin n :=
  open Classical in
  if h : ∃ p, p < topClockSpan n ∧
      rank (topClockSpan n) (edgeStep (topClockSpan n) (cellOf s Y) p) + 1 ≤
        rank (topClockSpan n) (cellOf s Y) then
    winSite s (Classical.choose h)
  else s

/-- The rank is at most `topClockR r`.

Consumer: `topClockMarkedDebtPhase_holds`. -/
theorem rank_start_bound (r : Nat) (cells : Nat → Cell) :
    rank r cells ≤ topClockR r := by
  have h := rank_le r cells
  unfold topClockR
  have e : r * (4 * r + 4) = 4 * r ^ 2 + 4 * r := by
    rw [Nat.pow_two, Nat.mul_add, Nat.mul_comm r (4 * r), Nat.mul_assoc, Nat.mul_comm r 4]
  omega

/-- **P.4--P.5.**  At every eligible entrance, from every strict stop or permanent
first-tail cut, the expected time to a strict stop or coloured cut is at most
`n * R(r)`: the marked debt is the abstract rank of the target window, which no
edge raises, which the rightmost-obstruction edge lowers, and which is zero exactly on
the coloured cut.

Consumer: `TopClockPhaseBundle.marked` (TopClockAssembly). -/
theorem topClockMarkedDebtPhase_holds {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (s : Fin n) (hg : WinGeo ring C s) :
    TopClockMarkedDebtPhase ring C s (topClockMarkedClasses ring C s) := by
  classical
  intro Z hZ
  have hn : 0 < n := by have := hg.hn; omega
  have hr3 := span_ge_three hg.hn
  apply (UniformFirstHit.expectedHittingTimeAtMost_iff_cost
    (topFixedTraceNext ring C)
    (topClockStopOr ring C s (topClockMarkedClasses ring C s).coloured)
    hn Z (n * topClockR (topClockSpan n))).2
  intro T
  by_cases hstop : topClockStopOr ring C s (topClockMarkedClasses ring C s).coloured Z
  · rw [costNumerator_terminal _ _ Z hstop T]
    exact Nat.zero_le _
  · have hfirst : (topClockMarkedClasses ring C s).firstTail Z := by
      rcases hZ with h | h
      · exact absurd (Or.inl h) hstop
      · exact h
    have hdown := markedDown_start ring C s Z hfirst
    have hcost := topMarkedCostOfRows
      (topFixedTraceNext ring C)
      (MarkedDown ring C s)
      (topClockStopOr ring C s (topClockMarkedClasses ring C s).coloured)
      (fun Y => rank (topClockSpan n) (cellOf s Y))
      (chosenEdge s)
      (fun Y hY e => markedDown_next ring C s Y e hY)
      (by
        intro Y hY hnot
        by_cases h0 : rank (topClockSpan n) (cellOf s Y) = 0
        · exfalso
          exact hnot (Or.inr ((topClockMarkedClasses_coloured ring C s Y).mpr
            (rank_zero_coloured ring C s hg Y hY h0)))
        · omega)
      (by
        intro Y hY _ e
        right
        have hreach := markedDown_reached ring C s Y hY
        obtain ⟨cells', hstep, hagree⟩ := link_step ring C s Y hg hreach e
        have h1 := rank_step_le _ (by omega) _ _ hstep
        have h2 := rank_congr (topClockSpan n) (cellOf s (topFixedTraceNext ring C Y e))
          cells' hagree
        show rank (topClockSpan n) (cellOf s (topFixedTraceNext ring C Y e)) ≤ _
        omega)
      (by
        intro Y hY hnot
        right
        have hreach := markedDown_reached ring C s Y hY
        have hpos : 0 < rank (topClockSpan n) (cellOf s Y) := by
          by_cases h0 : rank (topClockSpan n) (cellOf s Y) = 0
          · exfalso
            exact hnot (Or.inr ((topClockMarkedClasses_coloured ring C s Y).mpr
              (rank_zero_coloured ring C s hg Y hY h0)))
          · omega
        have hex := rank_progress (topClockSpan n) (by omega) (cellOf s Y) hpos
        have hex' : ∃ p, p < topClockSpan n ∧
            rank (topClockSpan n) (edgeStep (topClockSpan n) (cellOf s Y) p) + 1 ≤
              rank (topClockSpan n) (cellOf s Y) := hex
        have hsel : chosenEdge s Y = winSite s (Classical.choose hex') := by
          unfold chosenEdge
          rw [dif_pos hex']
        have hspec := Classical.choose_spec hex'
        rw [hsel]
        have hagree := link_window ring C s Y hg hreach _ hspec.1
        have h2 := rank_congr (topClockSpan n)
          (cellOf s (topFixedTraceNext ring C Y (winSite s (Classical.choose hex'))))
          (edgeStep (topClockSpan n) (cellOf s Y) (Classical.choose hex')) hagree
        show rank (topClockSpan n)
          (cellOf s (topFixedTraceNext ring C Y (winSite s (Classical.choose hex')))) + 1 ≤ _
        omega)
      Z hdown T
    exact Nat.le_trans hcost
      (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (rank_start_bound _ _)))

/-- **P.4--P.5 at an eligible entrance.**  The phase at exactly the hypotheses of
`TopClockAllPhaseProps`: `5 ≤ n`, no leader, and a bad complete block pair at `s`.

Consumer: `TopClockPhaseBundle.marked` (TopClockAssembly). -/
theorem topClockMarkedDebtPhase_eligible {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (C : HeadlineConfiguration n) (s : Fin n) (hl : ∀ i : Fin n, (C i).l = false)
    (hbad : HeadlineDigit.BadCompletePair C s) :
    TopClockMarkedDebtPhase ring C s (topClockMarkedClasses ring C s) :=
  topClockMarkedDebtPhase_holds ring C s ⟨hn, hl, hbad⟩

end MarkedCells
end L3

#print axioms L3.MarkedCells.rank_step_le
#print axioms L3.MarkedCells.inv_step
#print axioms L3.MarkedCells.rank_progress
#print axioms L3.MarkedCells.rank_zero_coloured
#print axioms L3.MarkedCells.topClockMarkedDebtPhase_holds
#print axioms L3.MarkedCells.topClockMarkedDebtPhase_eligible
