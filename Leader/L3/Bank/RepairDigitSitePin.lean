import Leader.L3.Bank.RepairDigitValueLedger

/-!
# T32 items 2 and 4: the site pin of the crossings

Atoms follow their slots on the source cells of the pair:

* a fresh sample appears at the left cell `k` of the drawn edge only when that cell's output is
  unread (`U`), and it is stamped at the site `src + k` (`trackedPinStep`, with the row facts
  `pipeExtra`, `delExtra`);
* an atom moves from cell `k` into cell `k + 1` only when `k + 1` was empty, and a hopping packet
  leaves no atom behind.

Hence (`chosenStep`, `youngStep`) the chosen slot `i` on a source cell carries an atom of class
`P (R - 1 - i)` and a younger cell `q` behind the chosen tail carries an atom of class `P q`, for
any class `P` containing the fresh samples. When the chosen grid completes every source cell is a
younger cell, so the next chosen cohort starts pinned (`chosenRestart`).
-/

namespace L3.SitePin

set_option autoImplicit false

open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree
open L3.RenewalReferenceClock
open L3.CohortStages
open L3.CohortTransfer
open L3.CohortLedger
open L3.FiveTransfer
open L3.Projection
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
open L3.CohortClose
open L3.CohortOrder
open L3.BlockStart
open L3.FiveClose
open L3.HClose
open L3.CloseReceipt
open L3.FiveReach
open L3.ValueCorr
open L3.ValueLedger

/-! ### Row facts -/

section Rows

variable {n : Nat}

theorem pipeExtra (stamp : DigitStamp n) (bx : Bool) (ox oy : BankRepairDigitOutSh)
    (gxo gyo xo yo : DigitOutGhost n) (h : (xo, yo) = ghostPipe stamp bx ox oy gxo gyo) :
    (xo.atom = some (.sampled stamp) → ox = .U ∨ gxo.atom = some (.sampled stamp)) ∧
    (oy ≠ .E → yo.atom = gyo.atom) ∧
    (∀ T, ox = .D T → oy = .E → xo.atom = none) := by
  have h1 : xo = (ghostPipe stamp bx ox oy gxo gyo).1 := congrArg Prod.fst h
  have h2 : yo = (ghostPipe stamp bx ox oy gxo gyo).2 := congrArg Prod.snd h
  subst h1 h2
  refine ⟨fun hh => ?_, fun hh => ?_, fun T' hx hy => ?_⟩
  · rcases ox with _ | _ | T <;> rcases oy with _ | _ | T' <;> cases bx <;> (try cases T) <;>
      simp_all [ghostPipe, DigitOutGhost.atom]
  · rcases ox with _ | _ | T <;> rcases oy with _ | _ | T' <;> cases bx <;> (try cases T) <;>
      simp_all [ghostPipe, DigitOutGhost.atom]
  · subst hx hy
    cases T' <;> simp [ghostPipe, DigitOutGhost.atom]

theorem delExtra (stamp : DigitStamp n) (ox : BankRepairDigitOutSh) (iy : BankRepairDigitInSh)
    (ky : Bool) (gxo : DigitOutGhost n) (gyi : Option (DigitAtom n)) (xo : DigitOutGhost n)
    (yi : Option (DigitAtom n)) (h : (xo, yi) = ghostDel stamp ox iy ky gxo gyi) :
    (xo.atom = some (.sampled stamp) → ox = .U ∨ gxo.atom = some (.sampled stamp)) ∧
    (∀ T, ox = .D T → iy = .E → ky = false → xo.atom = none) := by
  have h1 : xo = (ghostDel stamp ox iy ky gxo gyi).1 := congrArg Prod.fst h
  subst h1
  refine ⟨fun hh => ?_, fun T' hx hy hk => ?_⟩
  · rcases ox with _ | _ | T <;> rcases iy with _ | _ | T' | T' <;> cases ky <;> (try cases T) <;>
      simp_all [ghostDel, DigitOutGhost.atom]
  · subst hx hy hk
    cases T' <;> simp [ghostDel, DigitOutGhost.atom]

theorem outEmptyOf {o : BankRepairDigitOutSh} (h : cohortTokOut o = .empty) : o = .E := by
  cases o <;> simp_all [cohortTokOut]

theorem outPktOf {o : BankRepairDigitOutSh} {T : Bool} (h : cohortTokOut o = .pkt T) :
    o = .D T := by
  cases o <;> simp_all [cohortTokOut]

theorem inEmptyOf {i : BankRepairDigitInSh} {l : Bool} (h : cohortTokIn i l = .empty) :
    i = .E ∧ l = false := by
  cases l <;> cases i <;> simp_all [cohortTokIn]

end Rows

/-! ### The tracked step with the drawn cell explicit -/

section Tracked

variable {c : Compiled} {n : Nat}

/-- The fresh stamp of a letter on pair edge `k` at clock `t`. -/
def stampAt (ring : DirectedRing n) (root : Fin n) (lane : DigitLane) (src t k : Nat) :
    DigitStamp n :=
  DigitStamp.mk (t + 1) (digitSite ring root (src + k)) lane

/-- **Tracked step, explicit cell**: as `trackedStep`, with the fresh sample stamped at the site of
cell `k`; the fresh sample appears only on an unread output; an atom enters cell `k + 1` only if
it was empty; a hopping packet leaves no atom; and the drawn pair edge is `k`. -/
theorem trackedPinStep (ring : DirectedRing n) (hn : 2 ≤ n) (root : Fin n)
    (S : Fin n → ProjD c) (R src : Nat) (hR : 2 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n)
    (hroot : ∀ i, (S i).word.native.l = true ↔ i = root)
    (hb0 : (S (digitSite ring root src)).word.beta = true)
    (hbR : (S (digitSite ring root (src + R))).word.beta = true)
    (hb2R : (S (digitSite ring root (src + 2 * R))).word.beta = true)
    (hbF : ∀ k, 0 < k → k < 2 * R → k ≠ R →
      (S (digitSite ring root (src + k))).word.beta = false)
    (lane : DigitLane) (A : DigitAudit c n)
    (j : Nat) (hj : j < n)
    (hbX : (pairW (S (digitSite ring root j)).word
      (S (digitSite ring root (j + 1))).word).1.beta = (S (digitSite ring root j)).word.beta)
    (hbY : (pairW (S (digitSite ring root j)).word
      (S (digitSite ring root (j + 1))).word).2.beta =
        (S (digitSite ring root (j + 1))).word.beta) :
    ∃ k, (∀ q, q ≠ k → q ≠ k + 1 →
        tracked ring root lane src R (digitAuditStep ring S A (digitSite ring root j)) q =
        tracked ring root lane src R A q) ∧
      MoveOk (tracked ring root lane src R A k) (tracked ring root lane src R A (k + 1))
        (tracked ring root lane src R (digitAuditStep ring S A (digitSite ring root j)) k)
        (tracked ring root lane src R (digitAuditStep ring S A (digitSite ring root j)) (k + 1))
        (some (.sampled (stampAt ring root lane src A.clock k))) ∧
      (k < R → tracked ring root lane src R (digitAuditStep ring S A (digitSite ring root j)) k =
          some (.sampled (stampAt ring root lane src A.clock k)) →
        (cohortProj ring root lane src R S).out k = .U ∨
          tracked ring root lane src R A k =
            some (.sampled (stampAt ring root lane src A.clock k))) ∧
      (k + 1 < R → (cohortProj ring root lane src R S).out (k + 1) ≠ .E →
        tracked ring root lane src R (digitAuditStep ring S A (digitSite ring root j)) (k + 1) =
          tracked ring root lane src R A (k + 1)) ∧
      (k < R → ∀ T, (cohortProj ring root lane src R S).out k = .D T →
        cohortTok R (cohortProj ring root lane src R S) (k + 1) = .empty →
        tracked ring root lane src R (digitAuditStep ring S A (digitSite ring root j)) k =
          none) ∧
      (∀ k', cohortEdgeOf root src R (digitSite ring root j) = some k' → k' = k) ∧
      (k < R → j = src + k) := by
  unfold tracked stampAt
  by_cases hin : src ≤ j ∧ j < src + 2 * R
  · obtain ⟨k, rfl⟩ : ∃ k, j = src + k := ⟨j - src, by omega⟩
    have hfr : ∀ q, q ≠ k → q ≠ k + 1 → q < 2 * R →
        laneCells ring root lane src
          (digitAuditStep ring S A (digitSite ring root (src + k))).current q =
        laneCells ring root lane src A.current q := by
      intro q hq1 hq2 hq
      unfold laneCells
      rw [curFar]
      · intro he
        exact hq1 (by have := bankRepairDigitSiteInj ring root (by omega) (by omega) he; omega)
      · intro he
        rw [← bankRepairDigitSiteSucc] at he
        exact hq2 (by have := bankRepairDigitSiteInj ring root (by omega) (by omega) he; omega)
    have hx : laneCells ring root lane src
        (digitAuditStep ring S A (digitSite ring root (src + k))).current k =
        laneGhost lane (svcAt ring S A (digitSite ring root (src + k))).x := by
      unfold laneCells
      rw [curX]
    have hy : laneCells ring root lane src
        (digitAuditStep ring S A (digitSite ring root (src + k))).current (k + 1) =
        laneGhost lane (svcAt ring S A (digitSite ring root (src + k))).y := by
      unfold laneCells
      rw [show digitSite ring root (src + (k + 1)) =
        ring.rightNeighbor (digitSite ring root (src + k)) from rfl, curY ring hn]
    have hlx := bankRepairDigitSiteNonroot ring root S hroot (src + k) (by omega) (by omega)
    have hly := bankRepairDigitSiteNonroot ring root S hroot (src + k + 1) (by omega) (by omega)
    have hK : ∀ k', cohortEdgeOf root src R (digitSite ring root (src + k)) = some k' →
        k' = k := by
      intro k' hk'
      rw [cohortEdgeOfSite ring root src R hend k (by omega)] at hk'
      exact (Option.some.inj hk').symm
    have hmyP : k + 1 < R → laneMarkerY lane (S (digitSite ring root (src + k)))
        (S (digitSite ring root (src + k + 1))) = false := by
      intro h1
      rw [laneMarkerYBeta lane _ _ hbY]
      exact hbF (k + 1) (by omega) (by omega) (by omega)
    have hmxD : k + 1 = R → laneMarkerX lane (S (digitSite ring root (src + k)))
        (S (digitSite ring root (src + k + 1))) = false := by
      intro h2
      rw [laneMarkerXBeta lane _ _ hbX]
      exact hbF k (by omega) (by omega) (by omega)
    have hmyD : k + 1 = R → laneMarkerY lane (S (digitSite ring root (src + k)))
        (S (digitSite ring root (src + k + 1))) = true := by
      intro h2
      rw [laneMarkerYBeta lane _ _ hbY, show src + k + 1 = src + R by omega]
      exact hbR
    refine ⟨k, trackedFrame R k _ _ hfr, ?_, ?_, ?_, ?_, hK, fun _ => rfl⟩
    · by_cases h1 : k + 1 < R
      · -- Pipe
        have hk0 : k < R := by omega
        simp only [trackedAt, hk0, h1, ↓reduceIte]
        rw [hx, hy]
        exact pipeMoveOf _ _ _ _ _ _ _ _ (rowPipeD lane (A.clock + 1)
          (digitSite ring root (src + k)) (ring.rightNeighbor (digitSite ring root (src + k)))
          (S (digitSite ring root (src + k))) (S (digitSite ring root (src + k + 1)))
          (A.current (digitSite ring root (src + k)))
          (A.current (digitSite ring root (src + k + 1))) hlx hly (hmyP h1))
      · by_cases h2 : k + 1 = R
        · -- Del
          have hk0 : k < R := by omega
          have hk1 : ¬ k + 1 < R := by omega
          have hk2 : k + 1 < 2 * R := by omega
          simp only [trackedAt, hk0, hk1, hk2, ↓reduceIte]
          rw [hx, hy]
          exact delMoveOf _ _ _ _ _ _ _ _ (rowDelD lane (A.clock + 1)
            (digitSite ring root (src + k)) (ring.rightNeighbor (digitSite ring root (src + k)))
            (S (digitSite ring root (src + k))) (S (digitSite ring root (src + k + 1)))
            (A.current (digitSite ring root (src + k)))
            (A.current (digitSite ring root (src + k + 1))) hlx hly (hmxD h2) (hmyD h2)).1
        · by_cases h3 : k + 1 < 2 * R
          · -- Fin
            have hk0 : ¬ k < R := by omega
            have hk1 : ¬ k + 1 < R := by omega
            have hk2 : k < 2 * R := by omega
            have hmy : laneMarkerY lane (S (digitSite ring root (src + k)))
                (S (digitSite ring root (src + k + 1))) = false := by
              rw [laneMarkerYBeta lane _ _ hbY]
              exact hbF (k + 1) (by omega) (by omega) (by omega)
            simp only [trackedAt, hk0, hk1, hk2, h3, ↓reduceIte]
            rw [hx, hy]
            exact finMoveOf _ _ _ _ _ _ _ _ _ _ (rowFinD lane (A.clock + 1)
              (digitSite ring root (src + k)) (ring.rightNeighbor (digitSite ring root (src + k)))
              (S (digitSite ring root (src + k))) (S (digitSite ring root (src + k + 1)))
              (A.current (digitSite ring root (src + k)))
              (A.current (digitSite ring root (src + k + 1))) hlx hly hmy).1
          · -- Term
            have hk0 : ¬ k < R := by omega
            have hk1 : ¬ k + 1 < R := by omega
            have hk2 : k < 2 * R := by omega
            have hmx : laneMarkerX lane (S (digitSite ring root (src + k)))
                (S (digitSite ring root (src + k + 1))) = false := by
              rw [laneMarkerXBeta lane _ _ hbX]
              exact hbF k (by omega) (by omega) (by omega)
            have hmy : laneMarkerY lane (S (digitSite ring root (src + k)))
                (S (digitSite ring root (src + k + 1))) = true := by
              rw [laneMarkerYBeta lane _ _ hbY, show src + k + 1 = src + 2 * R by omega]
              exact hb2R
            simp only [trackedAt, hk0, hk1, hk2, h3, ↓reduceIte]
            rw [hx]
            exact termMoveOf _ _ _ _ _ (rowTermD lane (A.clock + 1)
              (digitSite ring root (src + k)) (ring.rightNeighbor (digitSite ring root (src + k)))
              (S (digitSite ring root (src + k))) (S (digitSite ring root (src + k + 1)))
              (A.current (digitSite ring root (src + k)))
              (A.current (digitSite ring root (src + k + 1))) hlx hly hmx hmy).1
    · intro hk hnew
      rw [projOut ring root lane src R S k hk]
      simp only [trackedAt, hk, ↓reduceIte] at hnew ⊢
      rw [hx] at hnew
      by_cases h1 : k + 1 < R
      · exact (pipeExtra _ _ _ _ _ _ _ _ (rowPipeD lane (A.clock + 1)
          (digitSite ring root (src + k)) (ring.rightNeighbor (digitSite ring root (src + k)))
          (S (digitSite ring root (src + k))) (S (digitSite ring root (src + k + 1)))
          (A.current (digitSite ring root (src + k)))
          (A.current (digitSite ring root (src + k + 1))) hlx hly (hmyP h1))).1 hnew
      · have h2 : k + 1 = R := by omega
        exact (delExtra _ _ _ _ _ _ _ _ (rowDelD lane (A.clock + 1)
          (digitSite ring root (src + k)) (ring.rightNeighbor (digitSite ring root (src + k)))
          (S (digitSite ring root (src + k))) (S (digitSite ring root (src + k + 1)))
          (A.current (digitSite ring root (src + k)))
          (A.current (digitSite ring root (src + k + 1))) hlx hly (hmxD h2) (hmyD h2)).1).1 hnew
    · intro h1 hne
      rw [projOut ring root lane src R S (k + 1) h1] at hne
      simp only [trackedAt, h1, ↓reduceIte]
      rw [hy]
      exact (pipeExtra _ _ _ _ _ _ _ _ (rowPipeD lane (A.clock + 1)
        (digitSite ring root (src + k)) (ring.rightNeighbor (digitSite ring root (src + k)))
        (S (digitSite ring root (src + k))) (S (digitSite ring root (src + k + 1)))
        (A.current (digitSite ring root (src + k)))
        (A.current (digitSite ring root (src + k + 1))) hlx hly (hmyP h1))).2.1 hne
    · intro hk T hD hE
      rw [projOut ring root lane src R S k hk] at hD
      simp only [trackedAt, hk, ↓reduceIte]
      rw [hx]
      by_cases h1 : k + 1 < R
      · rw [cohortTokSrc _ h1, projOut ring root lane src R S (k + 1) h1] at hE
        exact (pipeExtra _ _ _ _ _ _ _ _ (rowPipeD lane (A.clock + 1)
          (digitSite ring root (src + k)) (ring.rightNeighbor (digitSite ring root (src + k)))
          (S (digitSite ring root (src + k))) (S (digitSite ring root (src + k + 1)))
          (A.current (digitSite ring root (src + k)))
          (A.current (digitSite ring root (src + k + 1))) hlx hly (hmyP h1))).2.2 T hD
          (outEmptyOf hE)
      · have h2 : k + 1 = R := by omega
        rw [cohortTokTgt _ (by omega), projIn ring root lane src R S (k + 1) (by omega) (by omega),
          projLive ring root lane src R S (k + 1) (by omega) (by omega)] at hE
        obtain ⟨hi, hl⟩ := inEmptyOf hE
        exact (delExtra _ _ _ _ _ _ _ _ (rowDelD lane (A.clock + 1)
          (digitSite ring root (src + k)) (ring.rightNeighbor (digitSite ring root (src + k)))
          (S (digitSite ring root (src + k))) (S (digitSite ring root (src + k + 1)))
          (A.current (digitSite ring root (src + k)))
          (A.current (digitSite ring root (src + k + 1))) hlx hly (hmxD h2) (hmyD h2)).1).2 T hD
          hi hl
  · have farNe : ∀ q, q < 2 * R → src + q ≠ j → src + q ≠ j + 1 →
        laneCells ring root lane src (digitAuditStep ring S A (digitSite ring root j)).current q =
        laneCells ring root lane src A.current q := by
      intro q hq n1 n2
      unfold laneCells
      rw [curFar]
      · intro he
        exact n1 (bankRepairDigitSiteInj ring root (by omega) hj he)
      · intro he
        rw [← bankRepairDigitSiteSucc] at he
        by_cases hjn : j + 1 < n
        · exact n2 (bankRepairDigitSiteInj ring root (by omega) hjn he)
        · rw [show j + 1 = n by omega, bankRepairDigitSiteN] at he
          have := bankRepairDigitSiteInj ring root (k := src + q) (m := 0) (by omega) (by omega) he
          omega
    have h2R : ¬ 2 * R < R := by omega
    have h2R' : ¬ 2 * R < 2 * R := by omega
    have h2R1 : ¬ 2 * R + 1 < R := by omega
    have h2R1' : ¬ 2 * R + 1 < 2 * R := by omega
    refine ⟨2 * R, fun q hq1 hq2 => ?_, ?_, fun h => absurd h h2R, fun h => absurd h h2R1,
      fun h => absurd h h2R, fun k' hk' => ?_, fun h => absurd h h2R⟩
    · by_cases hq : q < 2 * R
      · by_cases h1 : j + 1 = src
        · by_cases hq0 : q = 0
          · rw [hq0]
            have hlx := bankRepairDigitSiteNonroot ring root S hroot j (by omega) (by omega)
            have hly := bankRepairDigitSiteNonroot ring root S hroot (j + 1) (by omega) (by omega)
            have hmy : laneMarkerY lane (S (digitSite ring root j))
                (S (digitSite ring root (j + 1))) = true := by
              rw [laneMarkerYBeta lane _ _ hbY, h1]
              exact hb0
            have h0 : 0 < R := by omega
            simp only [trackedAt, h0, ↓reduceIte]
            unfold laneCells
            rw [show digitSite ring root (src + 0) = ring.rightNeighbor (digitSite ring root j) by
              rw [← h1]; rfl, curY ring hn]
            exact congrArg DigitOutGhost.atom (rowEntryD lane (A.clock + 1) (digitSite ring root j)
              (ring.rightNeighbor (digitSite ring root j)) (S (digitSite ring root j))
              (S (digitSite ring root (j + 1))) (A.current (digitSite ring root j))
              (A.current (digitSite ring root (j + 1))) hlx hly hmy)
          · unfold trackedAt
            rw [farNe q hq (by omega) (by omega)]
        · unfold trackedAt
          rw [farNe q hq (by omega) (by omega)]
      · have hq' : ¬ q < R := by omega
        simp only [trackedAt, hq, hq', ↓reduceIte]
    · simp only [trackedAt, h2R, h2R', h2R1, h2R1', ↓reduceIte]
      intro x
      simp
    · exfalso
      unfold cohortEdgeOf at hk'
      rw [cohortIdxSite ring root j hj, if_neg hin] at hk'
      cases hk'

end Tracked

/-! ### Slot classes on the source cells -/

section Abstract

variable {n : Nat}

/-- Chosen slot `i` on a source cell carries an atom of class `P (R - 1 - i)`. -/
def ChosenInv (R : Nat) (P : Nat → DigitAtom n → Prop) (tr : Nat → Option (DigitAtom n))
    (lam : Nat → Nat) : Prop :=
  ∀ i, i < R → cohortPos R lam i < R → ∀ a, tr (cohortPos R lam i) = some a → P (R - 1 - i) a

/-- A younger cell `q` behind the chosen tail carries an atom of class `P q`. -/
def YoungInv (R : Nat) (P : Nat → DigitAtom n → Prop) (tr : Nat → Option (DigitAtom n))
    (lam : Nat → Nat) : Prop :=
  ∀ q, q < lam (R - 1) → q < R → ∀ a, tr q = some a → P q a

variable {R c t k : Nat} {s : CohortLane} {lam : Nat → Nat} {ke : Option Nat}
  {tr tr' : Nat → Option (DigitAtom n)} {f : DigitStamp n} {P P' : Nat → DigitAtom n → Prop}

theorem chosenNe (hch : CohortChosen R s lam c) {i : Nat} (hi : i < R) :
    cohortTok R s (cohortPos R lam i) ≠ .empty := by
  rcases hch.pkt i hi with h | ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;> intro hc <;> cases hc

theorem freshNot (hTB : TimeBound tr t) (hft : f.time = t + 1) (q : Nat) :
    tr q ≠ some (.sampled f) := by
  intro h
  have := hTB q f h
  omega

/-- **Younger cells keep their class**: a younger cell's atom never moves (the cell ahead is
occupied), the tail's hop leaves no atom, and a fresh read at cell `q` is of class `P' q`. -/
theorem youngStep (hch : CohortChosen R s lam c) (hY : CohortYounger R s (lam (R - 1)))
    (hTB : TimeBound tr t) (hft : f.time = t + 1)
    (hfr : ∀ q, q ≠ k → q ≠ k + 1 → tr' q = tr q)
    (hm : MoveOk (tr k) (tr (k + 1)) (tr' k) (tr' (k + 1)) (some (.sampled f)))
    (hF : k < R → tr' k = some (.sampled f) → s.out k = .U ∨ tr k = some (.sampled f))
    (hM : k + 1 < R → s.out (k + 1) ≠ .E → tr' (k + 1) = tr (k + 1))
    (hH : k < R → ∀ T, s.out k = .D T → cohortTok R s (k + 1) = .empty → tr' k = none)
    (hK : ∀ k', ke = some k' → k' = k)
    (hPP : ∀ q a, P q a → P' q a) (hfresh : k < R → s.out k = .U → P' k (.sampled f))
    (h : YoungInv R P tr lam) : YoungInv R P' tr' (cohortGenStep R s lam ke) := by
  have hR := hch.two
  intro q hq hqR x hx
  have key : tr q = some x → P' q x := by
    intro hold
    by_cases hlt : q < lam (R - 1)
    · exact hPP _ _ (h q hlt hqR x hold)
    · exfalso
      rcases genStepCases (R := R) (s := s) (lam := lam) ke (R - 1) with h1 |
          ⟨hke, -, -, hno, hemp, h1⟩
      · rw [h1] at hq
        omega
      · have hpos : cohortPos R lam (R - 1) = q := by
          rw [h1] at hq
          unfold cohortPos
          omega
        rw [hpos] at hke hno hemp
        have hqk := hK q hke
        subst hqk
        rw [cohortTokSrc s hqR] at hno
        have htok : ∃ T, s.out q = .D T := by
          rcases hch.pkt (R - 1) (by omega) with h2 | ⟨h2, -⟩ | ⟨h2, -⟩
          · rw [hpos, cohortTokSrc s hqR] at h2
            exact ⟨_, outPktOf h2⟩
          · rw [hpos, cohortTokSrc s hqR] at h2
            exact absurd h2 (cohortTokOutNe _ _)
          · rw [hpos, cohortTokSrc s hqR] at h2
            exact absurd h2 hno
        obtain ⟨T, hT⟩ := htok
        rw [hH hqR T hT hemp] at hx
        cases hx
  rcases moveOrigin hfr hm q x hx with ⟨p, -, hpx, hpq⟩ | ⟨hqk, hfx⟩
  · by_cases hpq' : p = q
    · rw [hpq'] at hpx
      exact key hpx
    · obtain ⟨hq1, -, -⟩ := hpq hpq'
      by_cases hE1 : s.out (k + 1) = .E
      · exfalso
        have htk : cohortTok R s q = .empty := by
          rw [cohortTokSrc s hqR, hq1, hE1]
          rfl
        by_cases hlt : q < lam (R - 1)
        · rcases hY q hlt hqR with h2 | h2 <;> rw [htk] at h2 <;> cases h2
        · apply chosenNe hch (i := R - 1) (by omega)
          have hle : cohortGenStep R s lam ke (R - 1) ≤ lam (R - 1) + 1 := by
            rcases genStepCases (R := R) (s := s) (lam := lam) ke (R - 1) with h1 |
                ⟨-, -, -, -, -, h1⟩ <;> omega
          have hpos : cohortPos R lam (R - 1) = q := by
            unfold cohortPos
            omega
          rw [hpos]
          exact htk
      · have h2 := hM (by omega) hE1
        rw [← hq1] at h2
        rw [h2] at hx
        exact key hx
  · have hfx' : x = .sampled f := (Option.some.inj hfx).symm
    subst hfx'
    rw [hqk] at hx ⊢
    rcases hF (by omega) hx with hU | hT
    · exact hfresh (by omega) hU
    · exact absurd hT (freshNot hTB hft k)

/-- **Chosen slots keep their class** on the source cells: a slot's atom stays with it or moves
with its hop; a fresh read happens only at an unread slot (`lam i = 0`, cell `R - 1 - i`). -/
theorem chosenStep (hch : CohortChosen R s lam c)
    (hE : ∀ q, q < R → cohortTok R s q = .empty → tr q = none)
    (hTB : TimeBound tr t) (hft : f.time = t + 1)
    (hfr : ∀ q, q ≠ k → q ≠ k + 1 → tr' q = tr q)
    (hm : MoveOk (tr k) (tr (k + 1)) (tr' k) (tr' (k + 1)) (some (.sampled f)))
    (hF : k < R → tr' k = some (.sampled f) → s.out k = .U ∨ tr k = some (.sampled f))
    (hM : k + 1 < R → s.out (k + 1) ≠ .E → tr' (k + 1) = tr (k + 1))
    (hPP : ∀ q a, P q a → P' q a) (hfresh : k < R → s.out k = .U → P' k (.sampled f))
    (h : ChosenInv R P tr lam) : ChosenInv R P' tr' (cohortGenStep R s lam ke) := by
  intro i hi hq' x hx
  rcases genStepCases (R := R) (s := s) (lam := lam) ke i with hN | ⟨-, -, -, -, hemp, hH1⟩
  · have hpos : cohortPos R (cohortGenStep R s lam ke) i = cohortPos R lam i := by
      unfold cohortPos
      rw [hN]
    rw [hpos] at hx hq'
    rcases moveOrigin hfr hm _ x hx with ⟨p, -, hpx, hpq⟩ | ⟨hqk, hfx⟩
    · by_cases hpq' : p = cohortPos R lam i
      · rw [hpq'] at hpx
        exact hPP _ _ (h i hi hq' x hpx)
      · obtain ⟨hq1, -, -⟩ := hpq hpq'
        by_cases hE1 : s.out (k + 1) = .E
        · exfalso
          apply chosenNe hch hi
          rw [cohortTokSrc s hq', hq1, hE1]
          rfl
        · have h2 := hM (by omega) hE1
          rw [← hq1] at h2
          rw [h2] at hx
          exact hPP _ _ (h i hi hq' x hx)
    · have hfx' : x = .sampled f := (Option.some.inj hfx).symm
      subst hfx'
      rw [hqk] at hx hq'
      rcases hF hq' hx with hU | hT
      · have hlam : lam i = 0 := by
          rcases hch.pkt i hi with h2 | ⟨h2, -⟩ | ⟨-, h2⟩
          · rw [hqk, cohortTokSrc s hq', hU] at h2
            simp [cohortTokOut] at h2
          · rw [hqk, cohortTokSrc s hq', hU] at h2
            simp [cohortTokOut] at h2
          · exact h2
        have hk : R - 1 - i = k := by
          unfold cohortPos at hqk
          omega
        rw [hk]
        exact hfresh hq' hU
      · exact absurd hT (freshNot hTB hft k)
  · have hpos : cohortPos R (cohortGenStep R s lam ke) i = cohortPos R lam i + 1 := by
      unfold cohortPos
      rw [hH1]
      omega
    rw [hpos] at hx hq'
    rcases moveOrigin hfr hm _ x hx with ⟨p, -, hpx, hpq⟩ | ⟨hqk, hfx⟩
    · by_cases hpq' : p = cohortPos R lam i + 1
      · exfalso
        rw [hpq', hE _ hq' hemp] at hpx
        cases hpx
      · obtain ⟨hq1, hpk, -⟩ := hpq hpq'
        have hk : cohortPos R lam i = k := by omega
        rw [hpk, ← hk] at hpx
        exact hPP _ _ (h i hi (by omega) x hpx)
    · exfalso
      have hfx' : x = .sampled f := (Option.some.inj hfx).symm
      subst hfx'
      rw [hqk] at hx hq'
      rcases hF hq' hx with hU | hT
      · rw [hqk, cohortTokSrc s hq', hU] at hemp
        simp [cohortTokOut] at hemp
      · exact freshNot hTB hft k hT

/-- When the chosen grid completes every source cell is a younger cell: the next chosen cohort
(`lam = 0`) starts in class. -/
theorem chosenRestart (hR : 2 ≤ R) (h : YoungInv R P tr lam) (hd : gridDone R R lam) :
    ChosenInv R P tr (fun _ => 0) := by
  intro i hi _ a ha
  have hp : cohortPos R (fun _ => 0) i = R - 1 - i := rfl
  rw [hp] at ha
  have := hd (R - 1) (by omega)
  exact h (R - 1 - i) (by omega) (by omega) a ha

theorem youngRestart : YoungInv R P tr (fun _ => 0) := by
  intro q hq
  exact absurd hq (Nat.not_lt_zero q)

end Abstract

/-! ### The pinned class: recorded samples of this lane at the slot's source site -/

section Concrete

variable {c : Compiled} {n : Nat}

/-- The pinned class of origin cell `q`: a recorded sample of this lane read at site `src + q`,
with the tail bit set exactly at cell `0`. -/
def SPin (ring : DirectedRing n) (root : Fin n) (lane : DigitLane) (src : Nat)
    (A : DigitAudit c n) (q : Nat) (a : DigitAtom n) : Prop :=
  ∃ s : DigitSample c n, a = .sampled s.id ∧ DigitRecordedSample A s ∧ s.id.lane = lane ∧
    s.id.site = digitSite ring root (src + q) ∧ s.tail = decide (q = 0)

theorem sPinStep (ring : DirectedRing n) (root : Fin n) (lane : DigitLane) (src : Nat)
    (S : Fin n → ProjD c) (A : DigitAudit c n) (e : Fin n) :
    ∀ q a, SPin ring root lane src A q a →
      SPin ring root lane src (digitAuditStep ring S A e) q a := by
  intro q a ⟨s, h1, h2, h3, h4, h5⟩
  exact ⟨s, h1, recordedSampleStep ring S A e s h2, h3, h4, h5⟩

/-- Crossed slot `i` exported an atom of class `P (R - 1 - i)`. -/
def ChiInv (R : Nat) (P : Nat → DigitAtom n → Prop) (chi : Nat → DigitExport c n)
    (lam : Nat → Nat) : Prop :=
  ∀ i, i < R → R ≤ cohortPos R lam i → ∃ a, (chi i).operand = some a ∧ P (R - 1 - i) a

theorem emptyNone (ring : DirectedRing n) (root : Fin n) (lane : DigitLane) (src R : Nat)
    (Base : Bool → DigitAtom n → Prop) (S : Fin n → ProjD c) (A : DigitAudit c n)
    (hcorr : GhostCorr ring root lane src R Base S A) (q : Nat) (hq : q < R)
    (h : cohortTok R (cohortProj ring root lane src R S) q = .empty) :
    tracked ring root lane src R A q = none := by
  unfold GhostCorr at hcorr
  rw [cohortTokSrc _ hq] at h
  have h2 := hcorr.1 q hq
  rw [outEmptyOf h] at h2
  have h3 : (laneCells ring root lane src A.current q).out = .empty := h2
  unfold tracked trackedAt
  rw [if_pos hq, h3]
  rfl

theorem pktSome (ring : DirectedRing n) (root : Fin n) (lane : DigitLane) (src R : Nat)
    (Base : Bool → DigitAtom n → Prop) (S : Fin n → ProjD c) (A : DigitAudit c n)
    (hcorr : GhostCorr ring root lane src R Base S A) (q : Nat) (hq : q < R) (T : Bool)
    (h : (cohortProj ring root lane src R S).out q = .D T) :
    tracked ring root lane src R A q ≠ none := by
  unfold GhostCorr at hcorr
  have h2 := hcorr.1 q hq
  rw [h] at h2
  unfold tracked trackedAt
  rw [if_pos hq]
  intro hn
  have h3 : optOk (GhostOk ring root lane src R Base A T)
      (laneCells ring root lane src A.current q).out.atom := h2
  rw [hn] at h3
  exact h3

/-- A fresh read at source cell `k` is pinned at `k`. -/
theorem freshSPin (ring : DirectedRing n) (root : Fin n) (S : Fin n → ProjD c) (R src : Nat)
    (hsrc : 2 ≤ src) (hend : src + 2 * R < n)
    (hroot : ∀ i, (S i).word.native.l = true ↔ i = root)
    (hb0 : (S (digitSite ring root src)).word.beta = true)
    (hbF : ∀ k, 0 < k → k < 2 * R → k ≠ R →
      (S (digitSite ring root (src + k))).word.beta = false)
    (lane : DigitLane) (A : DigitAudit c n) (k : Nat) (hk : k < R)
    (hbX : (pairW (S (digitSite ring root (src + k))).word
      (S (digitSite ring root (src + k + 1))).word).1.beta =
        (S (digitSite ring root (src + k))).word.beta)
    (hU : (cohortProj ring root lane src R S).out k = .U) :
    SPin ring root lane src (digitAuditStep ring S A (digitSite ring root (src + k))) k
      (.sampled (stampAt ring root lane src A.clock k)) := by
  have hlx := bankRepairDigitSiteNonroot ring root S hroot (src + k) (by omega) (by omega)
  have hly := bankRepairDigitSiteNonroot ring root S hroot (src + k + 1) (by omega) (by omega)
  rw [projOut ring root lane src R S k hk] at hU
  obtain ⟨s, h1, h2, h3⟩ := freshSample ring S A (digitSite ring root (src + k)) lane hlx hly hU
  refine ⟨s, by rw [h1]; rfl, h3, by rw [h1], by rw [h1], ?_⟩
  rw [h2]
  have hm : laneMarkerX lane (S (digitSite ring root (src + k)))
      (S (digitSite ring root (src + k + 1))) = (S (digitSite ring root (src + k))).word.beta :=
    laneMarkerXBeta lane _ _ hbX
  refine hm.trans ?_
  by_cases hk0 : k = 0
  · subst hk0
    simpa using hb0
  · rw [hbF k (by omega) (by omega) (by omega)]
    simp [hk0]

/-- **One letter on the source cells**: the younger cells and the chosen slots keep the pinned
class. -/
theorem letterPin (ring : DirectedRing n) (hn : 2 ≤ n) (root : Fin n)
    (S : Fin n → ProjD c) (R src : Nat) (hR : 2 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n)
    (hroot : ∀ i, (S i).word.native.l = true ↔ i = root)
    (hb0 : (S (digitSite ring root src)).word.beta = true)
    (hbR : (S (digitSite ring root (src + R))).word.beta = true)
    (hb2R : (S (digitSite ring root (src + 2 * R))).word.beta = true)
    (hbF : ∀ k, 0 < k → k < 2 * R → k ≠ R →
      (S (digitSite ring root (src + k))).word.beta = false)
    (lane : DigitLane) (Base : Bool → DigitAtom n → Prop) (A : DigitAudit c n)
    (j : Nat) (hj : j < n)
    (hbX : (pairW (S (digitSite ring root j)).word
      (S (digitSite ring root (j + 1))).word).1.beta = (S (digitSite ring root j)).word.beta)
    (hbY : (pairW (S (digitSite ring root j)).word
      (S (digitSite ring root (j + 1))).word).2.beta =
        (S (digitSite ring root (j + 1))).word.beta)
    (hgd : GhostCorrDistinct ring root lane src R Base S A)
    {lam : Nat → Nat} {c0 : Nat}
    (hch : CohortChosen R (cohortProj ring root lane src R S) lam c0)
    (hY : CohortYounger R (cohortProj ring root lane src R S) (lam (R - 1))) :
    (YoungInv R (SPin ring root lane src A) (tracked ring root lane src R A) lam →
      YoungInv R (SPin ring root lane src (digitAuditStep ring S A (digitSite ring root j)))
        (tracked ring root lane src R (digitAuditStep ring S A (digitSite ring root j)))
        (cohortGenStep R (cohortProj ring root lane src R S) lam
          (cohortEdgeOf root src R (digitSite ring root j)))) ∧
    (ChosenInv R (SPin ring root lane src A) (tracked ring root lane src R A) lam →
      ChosenInv R (SPin ring root lane src (digitAuditStep ring S A (digitSite ring root j)))
        (tracked ring root lane src R (digitAuditStep ring S A (digitSite ring root j)))
        (cohortGenStep R (cohortProj ring root lane src R S) lam
          (cohortEdgeOf root src R (digitSite ring root j)))) := by
  obtain ⟨k, hfr, hm, hF, hM, hH, hK, hJ⟩ := trackedPinStep ring hn root S R src hR hsrc hend
    hroot hb0 hbR hb2R hbF lane A j hj hbX hbY
  have hTB : TimeBound (tracked ring root lane src R A) A.clock := hgd.2.2.1
  have hE := emptyNone ring root lane src R Base S A hgd.1
  have hft : (stampAt ring root lane src A.clock k).time = A.clock + 1 := rfl
  have hfresh : k < R → (cohortProj ring root lane src R S).out k = .U →
      SPin ring root lane src (digitAuditStep ring S A (digitSite ring root j)) k
        (.sampled (stampAt ring root lane src A.clock k)) := by
    intro hk hU
    have hjk := hJ hk
    subst hjk
    exact freshSPin ring root S R src hsrc hend hroot hb0 hbF lane A k hk hbX hU
  have hPP := sPinStep ring root lane src S A (digitSite ring root j)
  exact ⟨youngStep hch hY hTB hft hfr hm hF hM hH hK hPP hfresh,
    chosenStep hch hE hTB hft hfr hm hF hM hPP hfresh⟩

/-- **Crossings keep the class**: the slot crossing at the delimiter cell exports the atom of
that cell (`delOperand`), which is the slot's atom. -/
theorem chiInvStep (ring : DirectedRing n) (root : Fin n) (lane : DigitLane) (src R : Nat)
    (Base : Bool → DigitAtom n → Prop) (S : Fin n → ProjD c) (A : DigitAudit c n) (e : Fin n)
    (ke : Option Nat)
    (hedge : ke = some (R - 1) → e = digitSite ring root (src + (R - 1)))
    (hdel : e = digitSite ring root (src + (R - 1)) →
      DelFacts ring lane S A e (cohortProj ring root lane src R S) R)
    (hop : e = digitSite ring root (src + (R - 1)) → ∀ x : DigitExport c n,
      (digitReceiptLane lane (svcAt ring S A e)).exported = some x →
      x.operand = (laneCells ring root lane src A.current (R - 1)).out.atom)
    (hcorr : GhostCorr ring root lane src R Base S A)
    {lam : Nat → Nat} {c0 : Nat}
    (hch : CohortChosen R (cohortProj ring root lane src R S) lam c0)
    {P P' : Nat → DigitAtom n → Prop} (hPP : ∀ q a, P q a → P' q a)
    (hC : ChosenInv R P (tracked ring root lane src R A) lam)
    (chi : Nat → DigitExport c n) (h : ChiInv R P chi lam) :
    ChiInv R P' (chiNext ring root lane src R S A e lam chi)
      (cohortGenStep R (cohortProj ring root lane src R S) lam ke) := by
  have hR := hch.two
  intro i hi hc
  by_cases hc0 : R ≤ cohortPos R lam i
  · have he : chiNext ring root lane src R S A e lam chi i = chi i := by
      unfold chiNext
      exact if_neg (fun hh => by have := hh.1; omega)
    rw [he]
    obtain ⟨a, h1, h2⟩ := h i hi hc0
    exact ⟨a, h1, hPP _ _ h2⟩
  · rcases genStepCases (R := R) (s := cohortProj ring root lane src R S) (lam := lam) ke i with
      hN | ⟨hke, -, -, hno, hemp, hH1⟩
    · exfalso
      unfold cohortPos at hc hc0
      rw [hN] at hc
      omega
    · have hpos : cohortPos R lam i = R - 1 := by
        unfold cohortPos at hc hc0 ⊢
        rw [hH1] at hc
        omega
      have he := hedge (by rw [← hpos]; exact hke)
      have hR1 : R - 1 < R := by omega
      rw [hpos] at hno hemp
      have hT : ∃ T, (cohortProj ring root lane src R S).out (R - 1) = .D T := by
        rcases hch.pkt i hi with h2 | ⟨h2, -⟩ | ⟨h2, -⟩
        · rw [hpos, cohortTokSrc _ hR1] at h2
          exact ⟨_, outPktOf h2⟩
        · rw [hpos, cohortTokSrc _ hR1] at h2
          exact absurd h2 (cohortTokOutNe _ _)
        · rw [hpos] at h2
          exact absurd h2 hno
      obtain ⟨T, hT⟩ := hT
      rw [show R - 1 + 1 = R by omega, cohortTokTgt _ (Nat.le_refl R)] at hemp
      obtain ⟨hi1, hl1⟩ := inEmptyOf hemp
      obtain ⟨x, hx, -⟩ := (hdel he).2 T hT hi1 hl1
      have hchi : chiNext ring root lane src R S A e lam chi i = x := by
        unfold chiNext
        rw [if_pos ⟨hpos, he⟩, hx]
        rfl
      rw [hchi]
      have hopx := hop he x hx
      have hsome := pktSome ring root lane src R Base S A hcorr (R - 1) hR1 T hT
      have htr : tracked ring root lane src R A (R - 1) =
          (laneCells ring root lane src A.current (R - 1)).out.atom := by
        unfold tracked trackedAt
        rw [if_pos hR1]
      cases ha : tracked ring root lane src R A (R - 1) with
      | none => exact absurd ha hsome
      | some a =>
        refine ⟨a, by rw [hopx, ← htr, ha], ?_⟩
        exact hPP _ _ (hC i hi (by rw [hpos]; exact hR1) a (by rw [hpos]; exact ha))

end Concrete

/-! ### The pin invariant on the coupled chain -/

section Window

variable {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
  (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) (root : Fin n) (lane : DigitLane)
  (src R : Nat) (hR : 2 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n)
  (Base : Bool → DigitAtom n → Prop)

include hn hR hsrc hend in
/-- **One coupled letter**: the pinned classes of the younger cells, of the chosen slots and of
the crossings, and the window, all move to the generated ghost `cohortGenStep` of the letter. -/
theorem windowPinFacts
    (w : (BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n) ×
      ((Nat → Nat) × Nat))
    (hw : WinInvD ring hbank root lane src R Base w.1 w.2) (e : Fin n) :
    (YoungInv R (SPin ring root lane src w.1.2) (tracked ring root lane src R w.1.2) w.2.1 →
      YoungInv R (SPin ring root lane src (digitAuditStep ring (piD w.1.1.val.1) w.1.2 e))
        (tracked ring root lane src R (digitAuditStep ring (piD w.1.1.val.1) w.1.2 e))
        (cohortGenStep R (cohortProj ring root lane src R (piD w.1.1.val.1)) w.2.1
          (cohortEdgeOf root src R e))) ∧
    (ChosenInv R (SPin ring root lane src w.1.2) (tracked ring root lane src R w.1.2) w.2.1 →
      ChosenInv R (SPin ring root lane src (digitAuditStep ring (piD w.1.1.val.1) w.1.2 e))
        (tracked ring root lane src R (digitAuditStep ring (piD w.1.1.val.1) w.1.2 e))
        (cohortGenStep R (cohortProj ring root lane src R (piD w.1.1.val.1)) w.2.1
          (cohortEdgeOf root src R e))) ∧
    (∀ (chi : Nat → DigitExport (compileAdvice (ceilLogTwo n)) n) (t0 : Nat),
      CycWin ring root lane src R w.1.2 w.2.1 chi t0 →
      CycWin ring root lane src R (digitAuditStep ring (piD w.1.1.val.1) w.1.2 e)
        (cohortGenStep R (cohortProj ring root lane src R (piD w.1.1.val.1)) w.2.1
          (cohortEdgeOf root src R e))
        (chiNext ring root lane src R (piD w.1.1.val.1) w.1.2 e w.2.1 chi) t0) ∧
    (∀ chi : Nat → DigitExport (compileAdvice (ceilLogTwo n)) n,
      ChosenInv R (SPin ring root lane src w.1.2) (tracked ring root lane src R w.1.2) w.2.1 →
      ChiInv R (SPin ring root lane src w.1.2) chi w.2.1 →
      ChiInv R (SPin ring root lane src (digitAuditStep ring (piD w.1.1.val.1) w.1.2 e))
        (chiNext ring root lane src R (piD w.1.1.val.1) w.1.2 e w.2.1 chi)
        (cohortGenStep R (cohortProj ring root lane src R (piD w.1.1.val.1)) w.2.1
          (cohortEdgeOf root src R e))) := by
  obtain ⟨hlay, hfo, hgd, ⟨o, hcyc⟩, -⟩ := hw
  obtain ⟨hL, hb0, hbR, hb2R, hbF⟩ := hlay
  obtain ⟨-, hroot, hbX, hbY⟩ := bankRepairDigitLeadBankEdge ring hn hbank root w.1.1 hL e
  obtain ⟨jx, hj, rfl⟩ := bankRepairDigitSiteSurj ring root e
  have hedge : cohortEdgeOf root src R (digitSite ring root jx) = some (R - 1) →
      digitSite ring root jx = digitSite ring root (src + (R - 1)) := fun hk => by
    rw [edgeOfSome ring root src R jx (R - 1) hj hk]
  have hkeDel : digitSite ring root jx = digitSite ring root (src + (R - 1)) →
      cohortEdgeOf root src R (digitSite ring root jx) = some (R - 1) := fun he => by
    rw [he]
    exact cohortEdgeOfSite ring root src R hend (R - 1) (by omega)
  have hdel : digitSite ring root jx = digitSite ring root (src + (R - 1)) →
      DelFacts ring lane (piD w.1.1.val.1) w.1.2 (digitSite ring root jx)
        (cohortProj ring root lane src R (piD w.1.1.val.1)) R := by
    intro he
    have hjeq : jx = src + (R - 1) := bankRepairDigitSiteInj ring root hj (by omega) he
    subst hjeq
    exact delEdgeFacts ring root (piD w.1.1.val.1) R src hR hend hroot hbR hbF lane w.1.2 hbX hbY
  have hop : digitSite ring root jx = digitSite ring root (src + (R - 1)) →
      ∀ x : DigitExport (compileAdvice (ceilLogTwo n)) n,
        (digitReceiptLane lane (svcAt ring (piD w.1.1.val.1) w.1.2
          (digitSite ring root jx))).exported = some x →
        x.operand = (laneCells ring root lane src w.1.2.current (R - 1)).out.atom := by
    intro he
    have hjeq : jx = src + (R - 1) := bankRepairDigitSiteInj ring root hj (by omega) he
    subst hjeq
    exact delOperand ring root (piD w.1.1.val.1) R src hR hend hroot hbR hbF lane w.1.2 hbX hbY
  have hch := hcyc.2.1.2
  have hY := hcyc.2.2.1
  obtain ⟨hYs, hCs⟩ := letterPin ring (by omega) root (piD w.1.1.val.1) R src hR hsrc hend hroot
    hb0 hbR hb2R hbF lane Base w.1.2 jx hj hbX hbY hgd hch hY
  refine ⟨hYs, hCs, fun chi t0 hcw => ?_, fun chi hC hci => ?_⟩
  · exact cycWinStep ring root lane src R (piD w.1.1.val.1) w.1.2 hfo (digitSite ring root jx)
      (cohortProj ring root lane src R (piD w.1.1.val.1))
      (cohortEdgeOf root src R (digitSite ring root jx)) hedge hkeDel hdel hcyc chi t0 hcw
  · exact chiInvStep ring root lane src R Base (piD w.1.1.val.1) w.1.2 (digitSite ring root jx)
      (cohortEdgeOf root src R (digitSite ring root jx)) hedge hdel hop hgd.1 hch
      (sPinStep ring root lane src (piD w.1.1.val.1) w.1.2 (digitSite ring root jx)) hC chi hci

/-- The younger cells of a coupled state are pinned. -/
def YInv
    (w : (BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n) ×
      ((Nat → Nat) × Nat)) : Prop :=
  YoungInv R (SPin ring root lane src w.1.2) (tracked ring root lane src R w.1.2) w.2.1

/-- The window `chi` closed last: the core window clauses, the site pin, and every
delimiter-edge export up to the current cycle start `t0` is no later than its last crossing. -/
def LastClose
    (w : (BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n) ×
      ((Nat → Nat) × Nat))
    (chi : Nat → DigitExport (compileAdvice (ceilLogTwo n)) n) (t0 : Nat) : Prop :=
  ChiCore ring hbank root lane src R w chi ∧ SitePin ring root lane src R w.1.2 chi ∧
  ∀ x : DigitExport (compileAdvice (ceilLogTwo n)) n, DigitRecordedExport w.1.2 x →
    OnEdge ring root lane src R x → x.time ≤ t0 → x.time ≤ (chi (R - 1)).time

/-- **The pin invariant**: chosen slots and younger cells pinned, a current window whose crossings
are pinned, and (after the first arrival) the last closed window with its site pin. -/
def PinState
    (w : (BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n) ×
      ((Nat → Nat) × Nat)) : Prop :=
  ChosenInv R (SPin ring root lane src w.1.2) (tracked ring root lane src R w.1.2) w.2.1 ∧
  YInv ring hbank root lane src R w ∧
  ∃ (chi : Nat → DigitExport (compileAdvice (ceilLogTwo n)) n) (t0 : Nat),
    CycWin ring root lane src R w.1.2 w.2.1 chi t0 ∧
    ChiInv R (SPin ring root lane src w.1.2) chi w.2.1 ∧
    (1 ≤ w.2.2 → ∃ chiOld, LastClose ring hbank root lane src R w chiOld t0)

theorem chiCoreStep
    (w : (BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n) ×
      ((Nat → Nat) × Nat)) (e : Fin n)
    (chi : Nat → DigitExport (compileAdvice (ceilLogTwo n)) n)
    (h : ChiCore ring hbank root lane src R w chi) :
    ChiCore ring hbank root lane src R (windowNext ring hbank root lane src R w e) chi := by
  obtain ⟨h1, h2, h3⟩ := h
  exact ⟨fun i hi => ⟨recordedExportStep ring (piD w.1.1.val.1) w.1.2 e _ (h1 i hi).1,
    (h1 i hi).2⟩, h2, fun word x hx ho ha hb => h3 (e :: word) x hx ho ha hb⟩

theorem sitePinStep (S : Fin n → ProjD (compileAdvice (ceilLogTwo n)))
    (A : DigitAudit (compileAdvice (ceilLogTwo n)) n) (e : Fin n)
    (chi : Nat → DigitExport (compileAdvice (ceilLogTwo n)) n)
    (h : SitePin ring root lane src R A chi) :
    SitePin ring root lane src R (digitAuditStep ring S A e) chi := by
  intro i hi
  obtain ⟨s, h1, h2, h3⟩ := h i hi
  exact ⟨s, h1, recordedSampleStep ring S A e s h2, h3⟩

include hn hR hsrc hend in
/-- **`PinState` is carried by every letter**; a closing letter records the closed window with
its site pin as the last closed window. -/
theorem pinStateStep
    (w : (BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n) ×
      ((Nat → Nat) × Nat))
    (hw : WinInvD ring hbank root lane src R Base w.1 w.2)
    (h : PinState ring hbank root lane src R w) (e : Fin n) :
    PinState ring hbank root lane src R (windowNext ring hbank root lane src R w e) := by
  obtain ⟨hYs, hCs, hWs, hXs⟩ :=
    windowPinFacts ring hn hbank root lane src R hR hsrc hend Base w hw e
  have hfo' : AuditFrameOrder (digitAuditStep ring (piD w.1.1.val.1) w.1.2 e) :=
    auditFrameOrderStep ring (piD w.1.1.val.1) w.1.2 e hw.2.1
  obtain ⟨hC, hYi, chi, t0, hcw, hci, hlast⟩ := h
  have hw' := hWs chi t0 hcw
  have hci' := hXs chi hC hci
  have hY' := hYs hYi
  have hC' := hCs hC
  have hA : (windowNext ring hbank root lane src R w e).1.2 =
      digitAuditStep ring (piD w.1.1.val.1) w.1.2 e := rfl
  have hg : (windowNext ring hbank root lane src R w e).2 =
      cohortCycleGhost R (cohortProj ring root lane src R (piD w.1.1.val.1)) w.2
        (cohortEdgeOf root src R e) := rfl
  unfold PinState YInv LastClose
  rw [hA, hg]
  unfold cohortCycleGhost
  by_cases hd : gridDone R R (cohortGenStep R (cohortProj ring root lane src R (piD w.1.1.val.1))
      w.2.1 (cohortEdgeOf root src R e))
  · rw [if_pos hd]
    dsimp only
    have hall : ∀ i, i < R → R ≤ cohortPos R (cohortGenStep R
        (cohortProj ring root lane src R (piD w.1.1.val.1)) w.2.1 (cohortEdgeOf root src R e)) i := by
      intro i hi
      have := hd i hi
      unfold cohortPos
      omega
    refine ⟨chosenRestart hR hY' hd, youngRestart, chi, _,
      cycWinStart ring root lane src R _ hfo' chi, ?_, fun _ =>
        ⟨chiNext ring root lane src R (piD w.1.1.val.1) w.1.2 e w.2.1 chi, ?_, ?_, ?_⟩⟩
    · intro i hi hc
      have hp : cohortPos R (fun _ => 0) i = R - 1 - i := rfl
      omega
    · refine ⟨fun i hi => ⟨(hw'.2.2.1 i hi (hall i hi)).1, (hw'.2.2.1 i hi (hall i hi)).2.1⟩,
        fun a b hab hb => hw'.2.2.2 a b hab hb (hall b hb), fun word x hx ho h1 h2 => ?_⟩
      exact noExtraExport ring root lane src R hR _ _ hfo'
        (exportsBackRun ring hbank root lane src R word _) _ _ t0 hw' hd x hx ho h1 h2
    · intro i hi
      obtain ⟨a, ha, s, h1, h2, h3, h4, h5⟩ := hci' i hi (hall i hi)
      exact ⟨s, by rw [ha, h1], h2, h3, h4, h5⟩
    · intro x hx ho _
      by_cases hxt : t0 < x.time
      · obtain ⟨i, hi, -, rfl⟩ := hw'.2.1 x hx ho hxt
        rcases Nat.lt_or_ge i (R - 1) with hlt | hge
        · exact Nat.le_of_lt (hw'.2.2.2 i (R - 1) hlt (by omega) (hall _ (by omega)))
        · have hiR : i = R - 1 := by omega
          subst hiR
          exact Nat.le_refl _
      · have := (hw'.2.2.1 (R - 1) (by omega) (hall _ (by omega))).2.2
        omega
  · rw [if_neg hd]
    dsimp only
    refine ⟨hC', hY', _, t0, hw', hci', fun h1 => ?_⟩
    obtain ⟨chiOld, hcore, hpin, hlat⟩ := hlast h1
    refine ⟨chiOld, chiCoreStep ring hbank root lane src R w e chiOld hcore,
      sitePinStep ring root lane src R _ _ _ chiOld hpin, fun x hx ho ht => ?_⟩
    rcases recordedExportStepCases ring (piD w.1.1.val.1) w.1.2 _ x hx with hx' | ⟨hxt, -, -⟩
    · exact hlat x hx' ho ht
    · have := hcw.1
      omega

include hn hR hsrc hend in
theorem pinStateRun (word : List (Fin n)) :
    ∀ w : (BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n) ×
      ((Nat → Nat) × Nat),
      WinInvD ring hbank root lane src R Base w.1 w.2 → PinState ring hbank root lane src R w →
      PinState ring hbank root lane src R (word.foldl (windowNext ring hbank root lane src R) w) := by
  induction word with
  | nil => intro w _ h; exact h
  | cons e rest ih =>
      intro w hw h
      exact ih _ (winInvDStep ring hn hbank root lane src R hR hsrc hend Base w.1 w.2 hw e).1
        (pinStateStep ring hn hbank root lane src R hR hsrc hend Base w hw h e)

include hn hR hsrc hend in
/-- **Item 4, carried part**: the younger cells are pinned recorded samples along every letter
(they are read inside the run, from the unread cells the chosen tail leaves behind). -/
theorem yInvStep
    (w : (BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n) ×
      ((Nat → Nat) × Nat))
    (hw : WinInvD ring hbank root lane src R Base w.1 w.2)
    (h : YInv ring hbank root lane src R w) (e : Fin n) :
    YInv ring hbank root lane src R (windowNext ring hbank root lane src R w e) := by
  have hY' := (windowPinFacts ring hn hbank root lane src R hR hsrc hend Base w hw e).1 h
  have hA : (windowNext ring hbank root lane src R w e).1.2 =
      digitAuditStep ring (piD w.1.1.val.1) w.1.2 e := rfl
  have hg : (windowNext ring hbank root lane src R w e).2 =
      cohortCycleGhost R (cohortProj ring root lane src R (piD w.1.1.val.1)) w.2
        (cohortEdgeOf root src R e) := rfl
  unfold YInv
  rw [hA, hg]
  unfold cohortCycleGhost
  by_cases hd : gridDone R R (cohortGenStep R (cohortProj ring root lane src R (piD w.1.1.val.1))
      w.2.1 (cohortEdgeOf root src R e))
  · rw [if_pos hd]
    exact youngRestart
  · rw [if_neg hd]
    exact hY'

/-- At a cycle start (`lam = 0`) there is no younger cell. -/
theorem yInvStart
    (w : (BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n) ×
      ((Nat → Nat) × Nat)) (h0 : w.2.1 = fun _ => 0) :
    YInv ring hbank root lane src R w := by
  unfold YInv
  rw [h0]
  exact youngRestart

include hn hR hsrc hend in
/-- **Item 4, entrance part**: the letter that completes an arrival hands the younger cells over
as the next chosen cohort, so the state after it (arrival counter relabelled `0`) satisfies the
pin invariant. Every cohort whose younger phase ran inside the window chain therefore carries
only pinned recorded samples (no base atom). -/
theorem pinStateOfClose
    (w : (BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n) ×
      ((Nat → Nat) × Nat))
    (hw : WinInvD ring hbank root lane src R Base w.1 w.2)
    (h : YInv ring hbank root lane src R w) (e : Fin n)
    (hcl : (windowNext ring hbank root lane src R w e).2.2 = w.2.2 + 1) :
    (windowNext ring hbank root lane src R w e).2.1 = (fun _ => 0) ∧
    PinState ring hbank root lane src R
      ((windowNext ring hbank root lane src R w e).1,
        ((windowNext ring hbank root lane src R w e).2.1, 0)) := by
  have hY' := (windowPinFacts ring hn hbank root lane src R hR hsrc hend Base w hw e).1 h
  have hfo' : AuditFrameOrder (digitAuditStep ring (piD w.1.1.val.1) w.1.2 e) :=
    auditFrameOrderStep ring (piD w.1.1.val.1) w.1.2 e hw.2.1
  obtain ⟨-, -, -, -, chi0, -⟩ := hw
  have hA : (windowNext ring hbank root lane src R w e).1.2 =
      digitAuditStep ring (piD w.1.1.val.1) w.1.2 e := rfl
  have hg : (windowNext ring hbank root lane src R w e).2 =
      cohortCycleGhost R (cohortProj ring root lane src R (piD w.1.1.val.1)) w.2
        (cohortEdgeOf root src R e) := rfl
  rw [hg] at hcl ⊢
  unfold cohortCycleGhost at hcl ⊢
  by_cases hd : gridDone R R (cohortGenStep R (cohortProj ring root lane src R (piD w.1.1.val.1))
      w.2.1 (cohortEdgeOf root src R e))
  · rw [if_pos hd]
    refine ⟨rfl, ?_⟩
    unfold PinState YInv
    dsimp only
    rw [hA]
    refine ⟨chosenRestart hR hY' hd, youngRestart, chi0, _,
      cycWinStart ring root lane src R _ hfo' _, ?_, fun h1 => absurd h1 (by omega)⟩
    intro i hi hc
    have hp : cohortPos R (fun _ => 0) i = R - 1 - i := rfl
    omega
  · rw [if_neg hd] at hcl
    dsimp only at hcl
    omega

/-- The reach predicate of the receipt: exact frames, the value invariant, the pin invariant. -/
def PinReach
    (w : (BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n) ×
      ((Nat → Nat) × Nat)) : Prop :=
  ValReach ring hbank root lane src R w ∧ PinState ring hbank root lane src R w

include hn hR hsrc hend in
theorem pinReachStep
    (w : (BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n) ×
      ((Nat → Nat) × Nat)) (e : Fin n)
    (hw : WinInvD ring hbank root lane src R Base w.1 w.2)
    (h : PinReach ring hbank root lane src R w) :
    PinReach ring hbank root lane src R (windowNext ring hbank root lane src R w e) :=
  ⟨valReachStep ring hn hbank root lane src R hR hsrc hend Base w e hw h.1,
    pinStateStep ring hn hbank root lane src R hR hsrc hend Base w hw h.2 e⟩

include hn hR hsrc hend in
theorem pinReachRun (word : List (Fin n)) :
    ∀ w : (BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n) ×
      ((Nat → Nat) × Nat),
      WinInvD ring hbank root lane src R Base w.1 w.2 → PinReach ring hbank root lane src R w →
      PinReach ring hbank root lane src R (word.foldl (windowNext ring hbank root lane src R) w) := by
  induction word with
  | nil => intro w _ h; exact h
  | cons e rest ih =>
      intro w hw h
      exact ih _ (winInvDStep ring hn hbank root lane src R hR hsrc hend Base w.1 w.2 hw e).1
        (pinReachStep ring hn hbank root lane src R hR hsrc hend Base w e hw h)

/-- A just-closed state is a cycle start after at least one arrival. -/
theorem justClosedLam
    (wc : (BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n) ×
      ((Nat → Nat) × Nat))
    (h : JustClosed ring hbank root lane src R Base wc) :
    wc.2.1 = (fun _ => 0) ∧ 1 ≤ wc.2.2 := by
  obtain ⟨w0, e, -, rfl, hcl⟩ := h
  refine ⟨?_, by omega⟩
  have hcl' : (cohortCycleGhost R (cohortProj ring root lane src R (piD w0.1.1.val.1)) w0.2
      (cohortEdgeOf root src R e)).2 = w0.2.2 + 1 := hcl
  show (cohortCycleGhost R (cohortProj ring root lane src R (piD w0.1.1.val.1)) w0.2
      (cohortEdgeOf root src R e)).1 = fun _ => 0
  unfold cohortCycleGhost at hcl' ⊢
  by_cases hd : gridDone R R (cohortGenStep R (cohortProj ring root lane src R (piD w0.1.1.val.1))
      w0.2.1 (cohortEdgeOf root src R e))
  · rw [if_pos hd]
  · rw [if_neg hd] at hcl'
    dsimp only at hcl'
    omega

/-- **At a reachable block entrance** the last closed window is the window closed there: core
clauses, site pin, and no delimiter-edge export recorded after its last crossing. -/
theorem lastCloseAt
    (wc : (BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n) ×
      ((Nat → Nat) × Nat))
    (hre : PinReach ring hbank root lane src R wc)
    (hjc : JustClosed ring hbank root lane src R Base wc) :
    ∃ chi : Nat → DigitExport (compileAdvice (ceilLogTwo n)) n,
      ChiCore ring hbank root lane src R wc chi ∧ SitePin ring root lane src R wc.1.2 chi ∧
      ∀ x : DigitExport (compileAdvice (ceilLogTwo n)) n, DigitRecordedExport wc.1.2 x →
        OnEdge ring root lane src R x → x.time ≤ (chi (R - 1)).time := by
  obtain ⟨hlam, h1⟩ := justClosedLam ring hbank root lane src R Base wc hjc
  obtain ⟨-, -, -, chi', t0, hcw, -, hlast⟩ := hre
  obtain ⟨chi, hcore, hpin, hlat⟩ := hlast h1
  refine ⟨chi, hcore, hpin, fun x hx ho => hlat x hx ho ?_⟩
  rcases Nat.lt_or_ge t0 x.time with hlt | hge
  · exfalso
    obtain ⟨i, hi, hc, -⟩ := hcw.2.1 x hx ho hlt
    rw [hlam] at hc
    have hp : cohortPos R (fun _ => 0) i = R - 1 - i := rfl
    omega
  · exact hge

/-- **Item 3 (the remaining fact)**: at a reachable block entrance, the terminal of the old
cohort has a clean ledger whose `j`-th use, made after the entrance, reads the operand of the
crossing `chi (R - 1 - j)` of the window closed there. -/
def UseFact (after : Nat) : Prop :=
  ∀ (wc : (BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n) ×
      ((Nat → Nat) × Nat)) (word : List (Fin n))
    (U : DigitTerminal (compileAdvice (ceilLogTwo n)) n),
    PinReach ring hbank root lane src R wc → JustClosed ring hbank root lane src R Base wc →
    AnchorIn ring root lane src R after wc.1.2 → after ≤ wc.1.2.clock →
    (word.foldl (windowNext ring hbank root lane src R) wc).2.2 = wc.2.2 →
    OrderInv ring hbank root lane src R (word.foldl (windowNext ring hbank root lane src R) wc).1
      (word.foldl (windowNext ring hbank root lane src R) wc).2 wc.1.2.clock →
    DigitRecordedTerminal (word.foldl (windowNext ring hbank root lane src R) wc).1.2 U →
    U.lane = lane → U.source = digitSite ring root (src + (2 * R - 1)) →
    wc.1.2.clock < U.time →
    ∀ chi : Nat → DigitExport (compileAdvice (ceilLogTwo n)) n,
      ChiCore ring hbank root lane src R wc chi → SitePin ring root lane src R wc.1.2 chi →
      (∀ x : DigitExport (compileAdvice (ceilLogTwo n)) n, DigitRecordedExport wc.1.2 x →
        OnEdge ring root lane src R x → x.time ≤ (chi (R - 1)).time) →
      UseTrack R wc.1.2.clock U chi

include hn hR hsrc hend in
/-- **Item 5**: the restricted receipt `HCloseOn` on `PinReach` states, from the operand tracking
of item 3. `ChiSampled` comes from the site pin; `CloseUses` from `UseTrack` and the value
invariant, through `receiptOfPins`. -/
theorem hCloseOnPin (after : Nat) (hUse : UseFact ring hbank root lane src R Base after) :
    HCloseOn ring hbank root lane src R Base (PinReach ring hbank root lane src R) after := by
  intro wc word U hre hjc hanc haft hcnt hord hU hUl hUs hUt
  obtain ⟨hwd, -⟩ := justClosedStart ring hn hbank root lane src R hR hsrc hend Base wc hjc
  obtain ⟨chi, hcore, hpin, hlat⟩ :=
    lastCloseAt ring hbank root lane src R Base wc hre hjc
  have hreF := pinReachRun ring hn hbank root lane src R hR hsrc hend Base word wc hwd hre
  exact receiptOfPins ring hbank root lane src R hR wc word U hre.1.1 hwd.2.1 hre.1.2.2.1
    hwd.2.2.1.2.2.2.1 hreF.1.2 hU hUl hUs chi hcore hpin
    (hUse wc word U hre hjc hanc haft hcnt hord hU hUl hUs hUt chi hcore hpin hlat)

include hn hR hsrc hend in
/-- The completion obligation of the five-cohort transfer on `PinReach` states. -/
theorem oldCompletionPin (after : Nat) (hUse : UseFact ring hbank root lane src R Base after) :
    OldCompletionOn ring hbank root lane src R Base (PinReach ring hbank root lane src R) after :=
  oldCompletionOn ring hn hbank root lane src R hR hsrc hend Base _ after
    (hCloseOnPin ring hn hbank root lane src R hR hsrc hend Base after hUse)

include hn hR hsrc hend in
/-- **The per-block clock on `PinReach` states** (T31's `fiveReachCoupledBlock` with
`Reach := PinReach`), from the operand tracking of item 3. -/
theorem pinCoupledBlock (after : Nat) (hUse : UseFact ring hbank root lane src R Base after)
    (P Q : BankReferenceState ring hbank → Prop)
    (hA : ∀ z, P z → ∃ w : (BankReferenceState ring hbank ×
        DigitAudit (compileAdvice (ceilLogTwo n)) n) × ((Nat → Nat) × Nat),
      w.1.1 = z ∧ (WinInvD ring hbank root lane src R Base w.1 w.2 ∧
        FiveInvOn ring hbank root lane src R Base (PinReach ring hbank root lane src R) after w ∧
        w.2.2 = 0))
    (hB : ∀ w : (BankReferenceState ring hbank ×
        DigitAudit (compileAdvice (ceilLogTwo n)) n) × ((Nat → Nat) × Nat),
      FwdChain ring w.1.2 root src (src + R) lane 5 after → Q w.1.1) :
    CoupledBlock ring hbank P Q (200 * n * R) :=
  fiveReachCoupledBlock ring hn hbank root lane src R hR hsrc hend Base
    (PinReach ring hbank root lane src R) after
    (fun w e hw h => pinReachStep ring hn hbank root lane src R hR hsrc hend Base w e hw h)
    (oldCompletionPin ring hn hbank root lane src R hR hsrc hend Base after hUse) P Q hA hB

end Window

end L3.SitePin

#print axioms L3.SitePin.trackedPinStep
#print axioms L3.SitePin.youngStep
#print axioms L3.SitePin.chosenStep
#print axioms L3.SitePin.letterPin
#print axioms L3.SitePin.chiInvStep
#print axioms L3.SitePin.pinStateStep
#print axioms L3.SitePin.pinStateRun
#print axioms L3.SitePin.yInvStep
#print axioms L3.SitePin.pinStateOfClose
#print axioms L3.SitePin.pinReachRun
#print axioms L3.SitePin.lastCloseAt
#print axioms L3.SitePin.hCloseOnPin
#print axioms L3.SitePin.oldCompletionPin
#print axioms L3.SitePin.pinCoupledBlock
