import Leader.L3.Bank.RepairDigitCohortLedger

/-!
# T28 item 3: the old cohort's terminal precedes the next arrival

On the cycle class the old cohort's phase `o` reaches `2R + 1` (gone) from `2R` only through the
terminal edge `2R - 1` (`oldEdgeStepRef`, `genStepClosedRef`), whose live carry records a terminal
receipt. A closing letter (the chosen grid completes) is a hop of a chosen slot, at a cell
`≤ 2R - 2` (`closingHop`), and needs the old cohort gone (`cohortGenArrived`). Hence
(`orderInvStep`, `orderClosing`): **in every cycle, a terminal receipt on the terminal edge
`src + 2R - 1 → src + 2R` is recorded after the cycle start and strictly before the closing
letter**, i.e. cohort `j`'s terminal (the old cohort of cycle `j`) is recorded before cohort
`j + 1` (the chosen cohort of cycle `j`) arrives.
-/

namespace L3.CohortOrder

set_option autoImplicit false

open L3.RenewalReferenceClock
open L3.CohortDomination
open L3.CohortTail
open L3.CohortSites
open L3.CohortEntry
open L3.PacketClass
open L3.Rearm
open L3.Recording
open L3.GhostBridge
open L3.Correspondence
open L3.CohortIdentity
open L3.CohortWindow

/-! ### The old phase under one edge, with the exit edge -/

section Phase

variable {R o : Nat} {s : CohortLane}

/-- `cohortOldEdgeStep`, recording that the phase leaves `≤ 2R` only from `2R` by the edge
`2R - 1`. -/
theorem oldEdgeStepRef (hR : 2 ≤ R) (h : CohortOldAt R o s) (k : Nat) :
    ∃ o', o ≤ o' ∧ CohortOldAt R o' (cohortEdge R s k) ∧
      (∀ q, cohortBottom R o ≤ q → q < cohortBottom R o' →
        cohortTok R (cohortEdge R s k) q = .empty) ∧
      (o' ≤ 2 * R ∨ o = 2 * R + 1 ∨ (o = 2 * R ∧ k = 2 * R - 1)) := by
  by_cases h1 : o ≤ R
  · rw [cohortOldSettle h1] at h
    by_cases hRs : ∃ T, cohortTok R s R = .settled T
    · obtain ⟨T, hT⟩ := hRs
      have hall := cohortCarryOfSettling (cohortSettlingAll h hT)
      rw [cohortCarryZero] at hall
      by_cases hk : k = R
      · refine ⟨R + 1, by omega, ?_, ?_, Or.inl (by omega)⟩
        · rw [hk, cohortOldCarry (by omega) (by omega), cohortCarryMid (by omega) (by omega),
            show R + (R + 1 - R) - 1 = R by omega]
          exact cohortLaunch hR hall
        · intro q h2 h3
          rw [cohortBottomSettle h1] at h2
          rw [cohortBottomCarry (by omega)] at h3
          omega
      · refine ⟨R, h1, ?_, ?_, Or.inl (by omega)⟩
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
      refine ⟨o, Nat.le_refl o, ?_, fun q h2 h3 => absurd h3 (by omega), Or.inl (by omega)⟩
      rw [cohortOldSettle h1]
      exact cohortSettlingEdge hR h hRn k
  · by_cases h2 : o ≤ 2 * R
    · rw [cohortOldCarry (by omega) h2] at h
      have hj1 : 1 ≤ o - R := by omega
      have hjR : o - R ≤ R := by omega
      by_cases hk : k = R + (o - R) - 1
      · subst hk
        by_cases hj : o - R < R
        · refine ⟨o + 1, by omega, ?_, ?_, Or.inl (by omega)⟩
          · rw [cohortOldCarry (by omega) (by omega), cohortCarryMid (by omega) (by omega),
              show R + (o + 1 - R) - 1 = R + (o - R) - 1 + 1 by omega]
            have h' := h
            rw [cohortCarryMid (by omega) hjR] at h'
            exact cohortCarryMove (R + (o - R) - 1) (by omega) (by omega) h'
          · intro q h3 h4
            rw [cohortBottomCarry (by omega)] at h3
            rw [cohortBottomCarry (by omega)] at h4
            have hq : q = R + (o - R) - 1 := by omega
            rw [hq]
            exact cohortCarryVacate hR hj1 hjR h
        · refine ⟨o + 1, by omega, ?_, ?_, Or.inr (Or.inr ⟨by omega, by omega⟩)⟩
          · rw [cohortOldDone (by omega)]
            omega
          · intro q h3 h4
            rw [cohortBottomCarry (by omega)] at h3
            rw [cohortBottomCarry (by omega)] at h4
            have hq : q = R + (o - R) - 1 := by omega
            rw [hq]
            exact cohortCarryVacate hR hj1 hjR h
      · refine ⟨o, Nat.le_refl o, ?_, fun q h3 h4 => absurd h4 (by omega), Or.inl h2⟩
        rw [cohortOldCarry (by omega) h2]
        rw [cohortCarryMid (by omega) hjR] at h ⊢
        exact cohortCarryKeep (R + (o - R) - 1) (by omega) (by omega) h k hk
    · refine ⟨o, Nat.le_refl o, ?_, fun q h3 h4 => absurd h4 (by omega), Or.inr (Or.inl ?_)⟩
      · rw [cohortOldDone (by omega)] at h ⊢
        exact h
      · rw [cohortOldDone (by omega)] at h
        exact h

/-- `cohortGenStepClosed` with the exit information of the old phase. -/
theorem genStepClosedRef {lam : Nat → Nat} (h : CohortGen R s lam o)
    (hY : CohortYounger R s (lam (R - 1))) (hnd : ¬ gridDone R R lam) (ke : Option Nat) :
    ∃ o', o ≤ o' ∧ CohortGen R (cohortLaneStep R s ke) (cohortGenStep R s lam ke) o' ∧
      CohortYounger R (cohortLaneStep R s ke) (cohortGenStep R s lam ke (R - 1)) ∧
      (o' ≤ 2 * R ∨ o = 2 * R + 1 ∨ (o = 2 * R ∧ ke = some (2 * R - 1))) := by
  have hR := h.2.two
  by_cases hpre : lam (R - 1) < R
  · cases ke with
    | none =>
      refine ⟨o, Nat.le_refl _, h, hY, ?_⟩
      have := cohortOldLe h.1
      by_cases ho : o ≤ 2 * R
      · exact Or.inl ho
      · exact Or.inr (Or.inl (by omega))
    | some k =>
      obtain ⟨o', ho, hold, hnew, hx⟩ := oldEdgeStepRef hR h.1 k
      refine ⟨o', ho, (cohortGenOfOld h hpre k o' ho hold hnew).1, youngerGen h.2 hpre hY k, ?_⟩
      rcases hx with hx | hx | ⟨hx1, hx2⟩
      · exact Or.inl hx
      · exact Or.inr (Or.inl hx)
      · exact Or.inr (Or.inr ⟨hx1, by rw [hx2]⟩)
  · obtain ⟨o', ho, hg, hY', -⟩ := cohortGenStepClosed h hY hnd ke
    exact ⟨o', ho, hg, hY', Or.inr (Or.inl (cohortGenArrived h hpre).1)⟩

/-- A closing letter is a hop of a chosen slot, never the terminal edge. -/
theorem closingHop {lam : Nat → Nat} (hR : 2 ≤ R) (hnd : ¬ gridDone R R lam) (ke : Option Nat)
    (hd : gridDone R R (cohortGenStep R s lam ke)) : ke ≠ some (2 * R - 1) := by
  have hex : ∃ i, i < R ∧ lam i < R := by
    apply Classical.byContradiction
    intro hne
    apply hnd
    intro i hi
    apply Nat.le_of_not_lt
    intro hl
    exact hne ⟨i, hi, hl⟩
  obtain ⟨i, hi, hl⟩ := hex
  rcases genStepCases (R := R) (s := s) (lam := lam) ke i with h | ⟨hk, -, -, -, -, -⟩
  · have := hd i hi
    omega
  · intro hke
    rw [hke] at hk
    have hk' := Option.some.inj hk
    unfold cohortPos at hk'
    omega

end Phase

/-! ### Terminals since the cycle start -/

section Terms

variable {c : Compiled} {n : Nat}

/-- A terminal receipt on the terminal edge of the pair, recorded after `t0`. -/
def TermSince (ring : DirectedRing n) (root : Fin n) (lane : DigitLane) (src R : Nat)
    (A : DigitAudit c n) (t0 : Nat) : Prop :=
  ∃ T : DigitTerminal c n, DigitRecordedTerminal A T ∧ T.lane = lane ∧
    T.source = digitSite ring root (src + (2 * R - 1)) ∧ t0 < T.time ∧ T.time ≤ A.clock

theorem termSinceStep (ring : DirectedRing n) (root : Fin n) (lane : DigitLane) (src R : Nat)
    (S : Fin n → ProjD c) (A : DigitAudit c n) (e : Fin n) (t0 : Nat)
    (h : TermSince ring root lane src R A t0) :
    TermSince ring root lane src R (digitAuditStep ring S A e) t0 := by
  obtain ⟨T, ⟨f, hf, h1, h2, h3⟩, hl, hs, ht, hc⟩ := h
  exact ⟨T, ⟨f, auditFrameMemStep ring S A e f hf, h1, h2, h3⟩, hl, hs, ht,
    by show T.time ≤ A.clock + 1; omega⟩

/-- The terminal edge with a live carry records a terminal receipt at the letter. -/
theorem termNow (ring : DirectedRing n) (root : Fin n)
    (S : Fin n → ProjD c) (R src : Nat) (hR : 2 ≤ R) (hend : src + 2 * R < n)
    (hroot : ∀ i, (S i).word.native.l = true ↔ i = root)
    (hb2R : (S (digitSite ring root (src + 2 * R))).word.beta = true)
    (lane : DigitLane) (A : DigitAudit c n)
    (hbY : (pairW (S (digitSite ring root (src + (2 * R - 1)))).word
      (S (digitSite ring root (src + (2 * R - 1) + 1))).word).2.beta =
        (S (digitSite ring root (src + (2 * R - 1) + 1))).word.beta)
    (hkx : bankRepairDigitLaneLive lane (S (digitSite ring root (src + (2 * R - 1)))).top = true)
    (t0 : Nat) (ht0 : t0 ≤ A.clock) :
    TermSince ring root lane src R
      (digitAuditStep ring S A (digitSite ring root (src + (2 * R - 1)))) t0 := by
  have hlx := bankRepairDigitSiteNonroot ring root S hroot (src + (2 * R - 1)) (by omega)
    (by omega)
  have hly := bankRepairDigitSiteNonroot ring root S hroot (src + (2 * R - 1) + 1) (by omega)
    (by omega)
  have hmy : laneMarkerY lane (S (digitSite ring root (src + (2 * R - 1))))
      (S (digitSite ring root (src + (2 * R - 1) + 1))) = true := by
    rw [laneMarkerYBeta lane _ _ hbY, show src + (2 * R - 1) + 1 = src + 2 * R by omega]
    exact hb2R
  have hrec := recordTerminalD lane (A.clock + 1) (digitSite ring root (src + (2 * R - 1)))
    (ring.rightNeighbor (digitSite ring root (src + (2 * R - 1))))
    (S (digitSite ring root (src + (2 * R - 1))))
    (S (digitSite ring root (src + (2 * R - 1) + 1)))
    (A.current (digitSite ring root (src + (2 * R - 1))))
    (A.current (digitSite ring root (src + (2 * R - 1) + 1))) hlx hly hmy hkx
  refine ⟨DigitTerminal.mk (A.clock + 1) lane (digitSite ring root (src + (2 * R - 1)))
    (ring.rightNeighbor (digitSite ring root (src + (2 * R - 1)))) _ _ _,
    ⟨DigitFrame.mk (A.clock + 1) (digitSite ring root (src + (2 * R - 1))) S A.current
    (svcAt ring S A (digitSite ring root (src + (2 * R - 1)))),
    List.mem_cons.mpr (Or.inl rfl), rfl, rfl, hrec⟩, rfl, rfl, by show t0 < A.clock + 1; omega,
    by show A.clock + 1 ≤ A.clock + 1; omega⟩

end Terms

/-! ### The order invariant on the coupled chain -/

section OrderRun

variable {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
  (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) (root : Fin n) (lane : DigitLane)
  (src R : Nat) (hR : 2 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n)

/-- The order invariant with cycle start `t0`: layout, the cycle class in some old phase `o`,
and once the old cohort is gone (`o = 2R + 1`) a terminal receipt recorded since `t0`. -/
def OrderInv (z : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (g : (Nat → Nat) × Nat) (t0 : Nat) : Prop :=
  CohortLayout ring hbank root src R z.1 ∧ t0 ≤ z.2.clock ∧
  ∃ o, CohortCycIn R g.2 (cohortProj ring root lane src R (piD z.1.val.1)) g o ∧
    (o = 2 * R + 1 → TermSince ring root lane src R z.2 t0)

include hn hR hsrc hend in
/-- **Order step**: every letter keeps the order invariant. A non-closing letter keeps the cycle
start; a closing letter (arrival counter `j → j + 1`) starts the next cycle at the new clock, and
**before it a terminal receipt on the terminal edge was recorded after the cycle start**. -/
theorem orderInvStep
    (z : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (g : (Nat → Nat) × Nat) (t0 : Nat) (h : OrderInv ring hbank root lane src R z g t0)
    (e : Fin n) :
    ((windowGhost ring hbank root lane src R z g e).2 = g.2 ∧
      OrderInv ring hbank root lane src R (bankRepairDigitBoundaryAuditNext ring hbank z e)
        (windowGhost ring hbank root lane src R z g e) t0) ∨
    ((windowGhost ring hbank root lane src R z g e).2 = g.2 + 1 ∧
      OrderInv ring hbank root lane src R (bankRepairDigitBoundaryAuditNext ring hbank z e)
        (windowGhost ring hbank root lane src R z g e) (z.2.clock + 1) ∧
      TermSince ring root lane src R z.2 t0) := by
  obtain ⟨hlay, ht0, o, ⟨hm, hg, hY, hnd⟩, hterm⟩ := h
  obtain ⟨hlay', hproj⟩ := cohortBankStep ring hn hbank root lane src R hR hsrc hend z.1 hlay e
  have hlay0 := hlay
  obtain ⟨hL, hb0, hbR, hb2R, hbF⟩ := hlay0
  obtain ⟨-, hroot, hbX, hbY⟩ := bankRepairDigitLeadBankEdge ring hn hbank root z.1 hL e
  obtain ⟨jx, hj, rfl⟩ := bankRepairDigitSiteSurj ring root e
  obtain ⟨o', ho, hg', hY', hx⟩ := genStepClosedRef hg hY hnd
    (cohortEdgeOf root src R (digitSite ring root jx))
  have hclk : (bankRepairDigitBoundaryAuditNext ring hbank z (digitSite ring root jx)).2.clock =
      z.2.clock + 1 := rfl
  have hnext : (bankRepairDigitBoundaryAuditNext ring hbank z (digitSite ring root jx)).2 =
      digitAuditStep ring (piD z.1.val.1) z.2 (digitSite ring root jx) := rfl
  have hprj : cohortProj ring root lane src R
      (piD (bankRepairDigitBoundaryAuditNext ring hbank z (digitSite ring root jx)).1.val.1) =
      cohortLaneStep R (cohortProj ring root lane src R (piD z.1.val.1))
        (cohortEdgeOf root src R (digitSite ring root jx)) := hproj
  unfold windowGhost cohortCycleGhost
  by_cases hd : gridDone R R (cohortGenStep R (cohortProj ring root lane src R (piD z.1.val.1))
      g.1 (cohortEdgeOf root src R (digitSite ring root jx)))
  · rw [if_pos hd]
    right
    obtain ⟨a, b, d⟩ := cohortGenDoneStart hg' hY' hd
    have hoo : o' = 2 * R + 1 := by
      have hl := hd (R - 1) (by omega)
      exact (cohortGenArrived hg' (by omega)).1
    have hT : TermSince ring root lane src R z.2 t0 := by
      rcases hx with hx | hx | ⟨-, hx⟩
      · omega
      · exact hterm hx
      · exact absurd hx (closingHop hR hnd _ hd)
    refine ⟨rfl, ⟨hlay', by rw [hclk]; omega, 0, ?_, fun h0 => by omega⟩, hT⟩
    rw [hprj]
    exact ⟨rfl, a, b, d⟩
  · rw [if_neg hd]
    left
    refine ⟨rfl, hlay', by rw [hclk]; omega, o', ?_, fun h2 => ?_⟩
    · rw [hprj]
      exact ⟨hm, hg', hY', hd⟩
    · rw [hnext]
      rcases hx with hx | hx | ⟨hx1, hx2⟩
      · omega
      · exact termSinceStep ring root lane src R _ _ _ _ (hterm hx)
      · have hje : jx = src + (2 * R - 1) := edgeOfSome ring root src R jx _ hj hx2
        subst hje
        have hold := hg.1
        rw [hx1, cohortOldCarry (by omega) (by omega), cohortCarryMid (by omega) (by omega)]
          at hold
        have hlive := hold.1
        rw [show R + (2 * R - R) - 1 = 2 * R - 1 by omega,
          projLive ring root lane src R (piD z.1.val.1) (2 * R - 1) (by omega) (by omega)]
          at hlive
        exact termNow ring root (piD z.1.val.1) R src hR hend hroot hb2R lane z.2 hbY hlive t0
          ht0

/-- The next cycle start along the chain: kept on a non-closing letter, the new clock on a
closing letter. -/
noncomputable def orderNext
    (w : ((BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n) ×
      ((Nat → Nat) × Nat)) × Nat) (e : Fin n) :
    ((BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n) ×
      ((Nat → Nat) × Nat)) × Nat :=
  open Classical in
  (windowNext ring hbank root lane src R w.1 e,
    if (windowGhost ring hbank root lane src R w.1.1 w.1.2 e).2 = w.1.2.2 then w.2
    else w.1.1.2.clock + 1)

include hn hR hsrc hend in
/-- The order invariant along every coupled word (with the cycle start carried along). -/
theorem orderInvRun (word : List (Fin n)) :
    ∀ w : ((BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n) ×
      ((Nat → Nat) × Nat)) × Nat,
      OrderInv ring hbank root lane src R w.1.1 w.1.2 w.2 →
      OrderInv ring hbank root lane src R
        (word.foldl (orderNext ring hbank root lane src R) w).1.1
        (word.foldl (orderNext ring hbank root lane src R) w).1.2
        (word.foldl (orderNext ring hbank root lane src R) w).2 := by
  induction word with
  | nil => intro w h; exact h
  | cons e rest ih =>
      intro w h
      apply ih
      rcases orderInvStep ring hn hbank root lane src R hR hsrc hend w.1.1 w.1.2 w.2 h e with
        ⟨h1, h2⟩ | ⟨h1, h2, -⟩
      · show OrderInv ring hbank root lane src R _ _
          (if (windowGhost ring hbank root lane src R w.1.1 w.1.2 e).2 = w.1.2.2 then w.2
            else w.1.1.2.clock + 1)
        rw [if_pos h1]
        exact h2
      · show OrderInv ring hbank root lane src R _ _
          (if (windowGhost ring hbank root lane src R w.1.1 w.1.2 e).2 = w.1.2.2 then w.2
            else w.1.1.2.clock + 1)
        rw [if_neg (by omega)]
        exact h2

include hR in
/-- The order invariant at the T24 cycle entry, with the cycle start at the clock. -/
theorem orderInvEntry
    (z : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (hz : CohortLayout ring hbank root src R z.1)
    (hset : CohortSettling R 0 (cohortProj ring root lane src R (piD z.1.val.1)))
    (hyng : ∀ q, q < R →
      cohortTok R (cohortProj ring root lane src R (piD z.1.val.1)) q = .other ∨
      cohortTok R (cohortProj ring root lane src R (piD z.1.val.1)) q = .pkt (decide (q = 0))) :
    OrderInv ring hbank root lane src R z ((fun _ => 0), 0) z.2.clock :=
  ⟨hz, Nat.le_refl _, 0, cohortCycEntry hR hset hyng, fun h0 => by omega⟩

include hn hR hsrc hend in
/-- **Item 3 on the coupled chain**: at a closing letter from a state of the order invariant
with cycle start `t0`, a terminal receipt on the terminal edge was recorded after `t0` and no
later than the clock before the closing letter (so strictly before the arrival). -/
theorem orderClosing
    (z : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (g : (Nat → Nat) × Nat) (t0 : Nat) (h : OrderInv ring hbank root lane src R z g t0)
    (e : Fin n) (hcl : (windowGhost ring hbank root lane src R z g e).2 = g.2 + 1) :
    TermSince ring root lane src R z.2 t0 := by
  rcases orderInvStep ring hn hbank root lane src R hR hsrc hend z g t0 h e with
    ⟨h1, -⟩ | ⟨-, -, h3⟩
  · omega
  · exact h3

end OrderRun

end L3.CohortOrder

#print axioms L3.CohortOrder.oldEdgeStepRef
#print axioms L3.CohortOrder.orderInvStep
#print axioms L3.CohortOrder.orderInvRun
#print axioms L3.CohortOrder.orderClosing
