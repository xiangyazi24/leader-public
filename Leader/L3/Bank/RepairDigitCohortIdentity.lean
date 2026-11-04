import Leader.L3.Bank.RepairDigitCorrespondence

/-!
# T27 items 1-3: cohort identity (M1-M3) and the no-extra-export clause (F3)

M1 (`GhostCorrDistinct`): the T26 correspondence plus
* the sampled atoms on the tracked cells (outputs of source cells, inputs of target cells) are
  pairwise distinct, and stamped no later than the clock;
* every recorded export on the delimiter edge of the pair carries a sample stamped before it;
* no sampled atom still on a source cell has been exported on the delimiter edge;
* a sample id is exported at most once on the delimiter edge.
-/

namespace L3.CohortIdentity

set_option autoImplicit false

open L3.RenewalReferenceClock
open L3.CohortDomination
open L3.CohortSites
open L3.CohortEntry
open L3.Rearm
open L3.Recording
open L3.GhostBridge
open L3.Correspondence

/-! ### Two-cell moves -/

section Moves

variable {n : Nat}

/-- A two-cell move of atoms: the new left atom is the old left one or the fresh one; the new
right atom is the old right one, or the old left one moved out of the left cell. -/
def MoveOk (a b a' b' f : Option (DigitAtom n)) : Prop :=
  ∀ x, (a' = some x → a = some x ∨ f = some x) ∧
    (b' = some x → b = some x ∨ (a = some x ∧ a' ≠ some x))

/-- Sampled atoms sit in at most one cell. -/
def SampDistinct (at' : Nat → Option (DigitAtom n)) : Prop :=
  ∀ q q' (id : DigitStamp n), at' q = some (.sampled id) → at' q' = some (.sampled id) → q = q'

/-- Sampled atoms are stamped no later than `t`. -/
def TimeBound (at' : Nat → Option (DigitAtom n)) (t : Nat) : Prop :=
  ∀ q (id : DigitStamp n), at' q = some (.sampled id) → id.time ≤ t

theorem pipeMoveOf (stamp : DigitStamp n) (bx : Bool) (ox oy : BankRepairDigitOutSh)
    (gxo gyo xo yo : DigitOutGhost n) (h : (xo, yo) = ghostPipe stamp bx ox oy gxo gyo) :
    MoveOk gxo.atom gyo.atom xo.atom yo.atom (some (.sampled stamp)) := by
  have h1 : xo = (ghostPipe stamp bx ox oy gxo gyo).1 := congrArg Prod.fst h
  have h2 : yo = (ghostPipe stamp bx ox oy gxo gyo).2 := congrArg Prod.snd h
  subst h1 h2
  intro x
  constructor <;> intro hh <;>
    rcases ox with _ | _ | T <;> rcases oy with _ | _ | T' <;> cases bx <;> (try cases T) <;>
    simp_all [ghostPipe, DigitOutGhost.atom]

theorem delMoveOf (stamp : DigitStamp n) (ox : BankRepairDigitOutSh) (iy : BankRepairDigitInSh)
    (ky : Bool) (gxo : DigitOutGhost n) (gyi : Option (DigitAtom n)) (xo : DigitOutGhost n)
    (yi : Option (DigitAtom n)) (h : (xo, yi) = ghostDel stamp ox iy ky gxo gyi) :
    MoveOk gxo.atom gyi xo.atom yi (some (.sampled stamp)) := by
  have h1 : xo = (ghostDel stamp ox iy ky gxo gyi).1 := congrArg Prod.fst h
  have h2 : yi = (ghostDel stamp ox iy ky gxo gyi).2 := congrArg Prod.snd h
  subst h1 h2
  intro x
  constructor <;> intro hh <;>
    rcases ox with _ | _ | T <;> rcases iy with _ | _ | T' | T' <;> cases ky <;> (try cases T) <;>
    simp_all [ghostDel, DigitOutGhost.atom]

theorem finMoveOf (bx : Bool) (ix : BankRepairDigitInSh) (kx : Bool) (iy : BankRepairDigitInSh)
    (ky : Bool) (gxi gyi xi yi f : Option (DigitAtom n))
    (h : (xi, yi) = ghostFinIn bx ix kx iy ky gxi gyi) : MoveOk gxi gyi xi yi f := by
  have h1 : xi = finInX bx ix kx iy ky gxi := congrArg Prod.fst h
  have h2 : yi = finInY ix kx iy ky gxi gyi := congrArg Prod.snd h
  subst h1 h2
  intro x
  constructor <;> intro hh <;>
    rcases ix with _ | _ | T | T <;> rcases iy with _ | _ | T' | T' <;> cases kx <;> cases ky <;>
    cases bx <;> simp_all [finInX, finInY, finInYFree, finXP, finYX, finYP, shS]

theorem termMoveOf (ix : BankRepairDigitInSh) (kx : Bool) (gxi xi f : Option (DigitAtom n))
    (h : xi = ghostTermIn ix kx gxi) : MoveOk gxi none xi none f := by
  subst h
  intro x
  constructor <;> intro hh <;>
    rcases ix with _ | _ | T | T <;> cases kx <;> (try cases T) <;> simp_all [ghostTermIn]

/-- Where a new atom came from. -/
theorem moveOrigin {old new : Nat → Option (DigitAtom n)} {k : Nat} {f : Option (DigitAtom n)}
    (hfr : ∀ q, q ≠ k → q ≠ k + 1 → new q = old q)
    (hm : MoveOk (old k) (old (k + 1)) (new k) (new (k + 1)) f) (q : Nat) (x : DigitAtom n)
    (h : new q = some x) :
    (∃ p, p ≤ q ∧ old p = some x ∧ (p ≠ q → q = k + 1 ∧ p = k ∧ new k ≠ some x)) ∨
      (q = k ∧ f = some x) := by
  by_cases h1 : q = k
  · rw [h1] at h
    rcases (hm x).1 h with h2 | h2
    · exact Or.inl ⟨q, Nat.le_refl q, by rw [h1]; exact h2, fun hne => absurd rfl hne⟩
    · exact Or.inr ⟨h1, h2⟩
  · by_cases h2 : q = k + 1
    · rw [h2] at h
      rcases (hm x).2 h with h3 | ⟨h3, h4⟩
      · exact Or.inl ⟨q, Nat.le_refl q, by rw [h2]; exact h3, fun hne => absurd rfl hne⟩
      · exact Or.inl ⟨k, by omega, h3, fun _ => ⟨h2, rfl, h4⟩⟩
    · rw [hfr q h1 h2] at h
      exact Or.inl ⟨q, Nat.le_refl q, h, fun hne => absurd rfl hne⟩

/-- **Distinctness step**: a two-cell move with a fresh sample stamped `t + 1` keeps the sampled
atoms distinct and bounded by the new clock. -/
theorem distinctStep {old new : Nat → Option (DigitAtom n)} {k t : Nat} (stamp : DigitStamp n)
    (hst : stamp.time = t + 1) (hD : SampDistinct old) (hT : TimeBound old t)
    (hfr : ∀ q, q ≠ k → q ≠ k + 1 → new q = old q)
    (hm : MoveOk (old k) (old (k + 1)) (new k) (new (k + 1)) (some (.sampled stamp))) :
    SampDistinct new ∧ TimeBound new (t + 1) := by
  have fresh : ∀ id : DigitStamp n, some (DigitAtom.sampled stamp) = some (.sampled id) →
      ∀ p, old p ≠ some (.sampled id) := by
    intro id hf p hp
    have he : stamp = id := DigitAtom.sampled.inj (Option.some.inj hf)
    have := hT p id hp
    rw [← he] at this
    omega
  constructor
  · intro q q' id h1 h2
    rcases moveOrigin hfr hm q _ h1 with ⟨p, hp, hp1, hp2⟩ | ⟨hq, hf⟩ <;>
      rcases moveOrigin hfr hm q' _ h2 with ⟨p', hp', hp1', hp2'⟩ | ⟨hq', hf'⟩
    · have hpp := hD p p' id hp1 hp1'
      by_cases e1 : p = q
      · by_cases e2 : p' = q'
        · omega
        · obtain ⟨_, a2, a3⟩ := hp2' e2
          exact absurd (by rw [← a2, ← hpp, e1]; exact h1) a3
      · obtain ⟨a1, a2, a3⟩ := hp2 e1
        by_cases e2 : p' = q'
        · exact absurd (by rw [← a2, hpp, e2]; exact h2) a3
        · obtain ⟨b1, -, -⟩ := hp2' e2
          omega
    · exact absurd hp1 (fresh id hf' p)
    · exact absurd hp1' (fresh id hf p')
    · omega
  · intro q id h1
    rcases moveOrigin hfr hm q _ h1 with ⟨p, -, hp1, -⟩ | ⟨-, hf⟩
    · have := hT p id hp1
      omega
    · have he : stamp = id := DigitAtom.sampled.inj (Option.some.inj hf)
      rw [← he, hst]
      exact Nat.le_refl _

end Moves

/-! ### Tracked atoms on the ring -/

section Tracked

variable {c : Compiled} {n : Nat}

/-- The tracked atom of cell `q`: the output atom of a source cell, the input atom of a target
cell, nothing elsewhere. -/
def trackedAt (R : Nat) (g : Nat → DigitLaneGhost c n) (q : Nat) : Option (DigitAtom n) :=
  if q < R then (g q).out.atom else if q < 2 * R then (g q).input else none

theorem trackedFrame (R k : Nat) (g g' : Nat → DigitLaneGhost c n)
    (hfr : ∀ q, q ≠ k → q ≠ k + 1 → q < 2 * R → g' q = g q) :
    ∀ q, q ≠ k → q ≠ k + 1 → trackedAt R g' q = trackedAt R g q := by
  intro q h1 h2
  unfold trackedAt
  by_cases hq : q < 2 * R
  · rw [hfr q h1 h2 hq]
  · have hq' : ¬ q < R := by omega
    simp only [hq, hq', ↓reduceIte]

theorem delAcceptTrue (ox : BankRepairDigitOutSh) (iy : BankRepairDigitInSh) (ky : Bool)
    (h : delAccept ox iy ky = true) : ∃ T, ox = .D T ∧ iy = .E ∧ ky = false := by
  rcases ox with _ | _ | T <;> rcases iy with _ | _ | T' | T' <;> cases ky <;>
    simp_all [delAccept]

/-- The delimiter-edge export on record fields: its operand is the source ghost's atom, it is
stamped with the letter's time, and the source cell's atom has left. -/
theorem delExportD (lane : DigitLane) (t : Nat) (e d : Fin n) (X Y : ProjD c)
    (gx gy : DigitGhost c n) (hlx : X.word.native.l = false) (hly : Y.word.native.l = false)
    (hmx : laneMarkerX lane X Y = false) (hmy : laneMarkerY lane X Y = true)
    (x : DigitExport c n)
    (hx : (digitReceiptLane lane (digitService t e d X Y gx gy)).exported = some x) :
    x.operand = (laneGhost lane gx).out.atom ∧ x.time = t ∧
      (laneGhost lane (digitService t e d X Y gx gy).x).out.atom = none := by
  have h3 := (replayDel lane t e d (digitLaneView lane X (laneMarkerX lane X Y))
    (digitLaneView lane Y (laneMarkerY lane X Y)) (laneGhost lane gx) (laneGhost lane gy)
    (by rw [laneViewLeader]; exact hlx) (by rw [laneViewLeader]; exact hly)
    (by rw [laneViewMarker]; exact hmx) (by rw [laneViewMarker]; exact hmy)).2.2
  rw [laneViewOutSh, laneViewInSh, laneViewLive, ← serviceLane, hx] at h3
  have h4 : delAccept (bankRepairDigitOutShOf (bankRepairDigitLaneOut lane X.top))
      (bankRepairDigitInShOf (bankRepairDigitLaneIn lane Y.top))
      (bankRepairDigitLaneLive lane Y.top) = true := by
    rw [← h3]
    rfl
  obtain ⟨T, hD, hE, hk⟩ := delAcceptTrue _ _ _ h4
  obtain ⟨ex, e1, e2, e3, -⟩ := recordDeliveryD lane t e d X Y gx gy hlx hly hmy hD hE hk
  have hxe : x = ex := Option.some.inj (hx.symm.trans e1)
  have hr := (rowDelD lane t e d X Y gx gy hlx hly hmx hmy).1
  rw [hD, hE, hk] at hr
  have h5 : (laneGhost lane (digitService t e d X Y gx gy).x).out =
      (ghostDel (DigitStamp.mk t e lane) (.D T) .E false (laneGhost lane gx).out
        (laneGhost lane gy).input).1 := congrArg Prod.fst hr
  refine ⟨by rw [hxe, e2], by rw [hxe, e3], ?_⟩
  rw [h5]
  cases T <;> simp [ghostDel, DigitOutGhost.atom]

/-- **Tracked step**: one letter moves the tracked atoms across at most two adjacent cells, with
the letter's fresh sample as the only new atom. -/
theorem trackedStep (ring : DirectedRing n) (hn : 2 ≤ n) (root : Fin n)
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
        trackedAt R (laneCells ring root lane src
          (digitAuditStep ring S A (digitSite ring root j)).current) q =
        trackedAt R (laneCells ring root lane src A.current) q) ∧
      MoveOk (trackedAt R (laneCells ring root lane src A.current) k)
        (trackedAt R (laneCells ring root lane src A.current) (k + 1))
        (trackedAt R (laneCells ring root lane src
          (digitAuditStep ring S A (digitSite ring root j)).current) k)
        (trackedAt R (laneCells ring root lane src
          (digitAuditStep ring S A (digitSite ring root j)).current) (k + 1))
        (some (.sampled (DigitStamp.mk (A.clock + 1) (digitSite ring root j) lane))) := by
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
    refine ⟨k, trackedFrame R k _ _ hfr, ?_⟩
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
    by_cases h1 : k + 1 < R
    · -- Pipe
      have hk0 : k < R := by omega
      have hmy : laneMarkerY lane (S (digitSite ring root (src + k)))
          (S (digitSite ring root (src + k + 1))) = false := by
        rw [laneMarkerYBeta lane _ _ hbY]
        exact hbF (k + 1) (by omega) (by omega) (by omega)
      simp only [trackedAt, hk0, h1, ↓reduceIte]
      rw [hx, hy]
      exact pipeMoveOf _ _ _ _ _ _ _ _ (rowPipeD lane (A.clock + 1)
        (digitSite ring root (src + k)) (ring.rightNeighbor (digitSite ring root (src + k)))
        (S (digitSite ring root (src + k))) (S (digitSite ring root (src + k + 1)))
        (A.current (digitSite ring root (src + k)))
        (A.current (digitSite ring root (src + k + 1))) hlx hly hmy)
    · by_cases h2 : k + 1 = R
      · -- Del
        have hk0 : k < R := by omega
        have hk1 : ¬ k + 1 < R := by omega
        have hk2 : k + 1 < 2 * R := by omega
        have hmx : laneMarkerX lane (S (digitSite ring root (src + k)))
            (S (digitSite ring root (src + k + 1))) = false := by
          rw [laneMarkerXBeta lane _ _ hbX]
          exact hbF k (by omega) (by omega) (by omega)
        have hmy : laneMarkerY lane (S (digitSite ring root (src + k)))
            (S (digitSite ring root (src + k + 1))) = true := by
          rw [laneMarkerYBeta lane _ _ hbY, show src + k + 1 = src + R by omega]
          exact hbR
        simp only [trackedAt, hk0, hk1, hk2, ↓reduceIte]
        rw [hx, hy]
        exact delMoveOf _ _ _ _ _ _ _ _ (rowDelD lane (A.clock + 1)
          (digitSite ring root (src + k)) (ring.rightNeighbor (digitSite ring root (src + k)))
          (S (digitSite ring root (src + k))) (S (digitSite ring root (src + k + 1)))
          (A.current (digitSite ring root (src + k)))
          (A.current (digitSite ring root (src + k + 1))) hlx hly hmx hmy).1
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
    refine ⟨2 * R, fun q hq1 hq2 => ?_, ?_⟩
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

end Tracked

/-! ### M1: the distinct correspondence -/

section Distinct

variable {c : Compiled} {n : Nat}

/-- An export on the delimiter edge `src + R - 1 → src + R` of this lane. -/
def OnEdge (ring : DirectedRing n) (root : Fin n) (lane : DigitLane) (src R : Nat)
    (x : DigitExport c n) : Prop :=
  x.lane = lane ∧ x.source = digitSite ring root (src + (R - 1))

/-- The tracked atoms of the current audit ghosts. -/
def tracked (ring : DirectedRing n) (root : Fin n) (lane : DigitLane) (src R : Nat)
    (A : DigitAudit c n) : Nat → Option (DigitAtom n) :=
  trackedAt R (laneCells ring root lane src A.current)

/-- **M1**: the correspondence, with distinct sampled atoms on the tracked cells, stamps bounded
by the clock, exports on the delimiter edge carrying earlier samples, no exported sample still on
a source cell, and every sample exported at most once on the delimiter edge. -/
def GhostCorrDistinct (ring : DirectedRing n) (root : Fin n) (lane : DigitLane) (src R : Nat)
    (Base : Bool → DigitAtom n → Prop) (S : Fin n → ProjD c) (A : DigitAudit c n) : Prop :=
  GhostCorr ring root lane src R Base S A ∧
  SampDistinct (tracked ring root lane src R A) ∧
  TimeBound (tracked ring root lane src R A) A.clock ∧
  (∀ (x : DigitExport c n) (id : DigitStamp n), DigitRecordedExport A x →
    OnEdge ring root lane src R x → x.operand = some (.sampled id) →
    id.time < x.time ∧ x.time ≤ A.clock) ∧
  (∀ q (id : DigitStamp n) (x : DigitExport c n), q < R →
    tracked ring root lane src R A q = some (.sampled id) →
    DigitRecordedExport A x → OnEdge ring root lane src R x → x.operand ≠ some (.sampled id)) ∧
  (∀ (x y : DigitExport c n) (id : DigitStamp n), DigitRecordedExport A x →
    DigitRecordedExport A y → OnEdge ring root lane src R x → OnEdge ring root lane src R y →
    x.operand = some (.sampled id) → y.operand = some (.sampled id) → x = y)

theorem recordedExportStepCases (ring : DirectedRing n) (S : Fin n → ProjD c)
    (A : DigitAudit c n) (e : Fin n) (x : DigitExport c n)
    (h : DigitRecordedExport (digitAuditStep ring S A e) x) :
    DigitRecordedExport A x ∨
      (x.time = A.clock + 1 ∧ x.source = e ∧
        (digitReceiptLane x.lane (svcAt ring S A e)).exported = some x) := by
  obtain ⟨f, hf, h1, h2, h3⟩ := h
  rcases auditFrameMemStepCases ring S A e f hf with hf' | hf'
  · exact Or.inl ⟨f, hf', h1, h2, h3⟩
  · subst hf'
    exact Or.inr ⟨h1.symm, h2.symm, h3⟩

theorem recordedExportStep (ring : DirectedRing n) (S : Fin n → ProjD c)
    (A : DigitAudit c n) (e : Fin n) (x : DigitExport c n) (h : DigitRecordedExport A x) :
    DigitRecordedExport (digitAuditStep ring S A e) x := by
  obtain ⟨f, hf, h1, h2, h3⟩ := h
  exact ⟨f, auditFrameMemStep ring S A e f hf, h1, h2, h3⟩

/-- **M1 step**: every letter preserves the distinct correspondence (projected ring, layout
hypotheses of `cohortProjStep`). -/
theorem ghostCorrDistinctStep (ring : DirectedRing n) (hn : 2 ≤ n) (root : Fin n)
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
    (h : GhostCorrDistinct ring root lane src R Base S A) :
    GhostCorrDistinct ring root lane src R Base (phiD ring S (digitSite ring root j))
      (digitAuditStep ring S A (digitSite ring root j)) := by
  obtain ⟨hc, hD, hT, hE1, hE2, hE3⟩ := h
  obtain ⟨k, hfr, hm⟩ := trackedStep ring hn root S R src hR hsrc hend hroot hb0 hbR hb2R hbF
    lane A j hj hbX hbY
  obtain ⟨hD', hT'⟩ := distinctStep (DigitStamp.mk (A.clock + 1) (digitSite ring root j) lane)
    rfl hD hT hfr hm
  have newExp : ∀ x : DigitExport c n, OnEdge ring root lane src R x →
      x.source = digitSite ring root j →
      (digitReceiptLane x.lane (svcAt ring S A (digitSite ring root j))).exported = some x →
      x.operand = tracked ring root lane src R A (R - 1) ∧ x.time = A.clock + 1 ∧
      tracked ring root lane src R (digitAuditStep ring S A (digitSite ring root j)) (R - 1) =
        none ∧
      (∀ q, q < R - 1 →
        tracked ring root lane src R (digitAuditStep ring S A (digitSite ring root j)) q =
          tracked ring root lane src R A q) := by
    intro x ho hs hr
    have hjeq : j = src + (R - 1) :=
      bankRepairDigitSiteInj ring root hj (by omega) (hs.symm.trans ho.2)
    subst hjeq
    rw [ho.1] at hr
    have hlx := bankRepairDigitSiteNonroot ring root S hroot (src + (R - 1)) (by omega) (by omega)
    have hly := bankRepairDigitSiteNonroot ring root S hroot (src + (R - 1) + 1) (by omega)
      (by omega)
    have hmx : laneMarkerX lane (S (digitSite ring root (src + (R - 1))))
        (S (digitSite ring root (src + (R - 1) + 1))) = false := by
      rw [laneMarkerXBeta lane _ _ hbX]
      exact hbF (R - 1) (by omega) (by omega) (by omega)
    have hmy : laneMarkerY lane (S (digitSite ring root (src + (R - 1))))
        (S (digitSite ring root (src + (R - 1) + 1))) = true := by
      rw [laneMarkerYBeta lane _ _ hbY, show src + (R - 1) + 1 = src + R by omega]
      exact hbR
    obtain ⟨o1, o2, o3⟩ := delExportD lane (A.clock + 1) (digitSite ring root (src + (R - 1)))
      (ring.rightNeighbor (digitSite ring root (src + (R - 1))))
      (S (digitSite ring root (src + (R - 1)))) (S (digitSite ring root (src + (R - 1) + 1)))
      (A.current (digitSite ring root (src + (R - 1))))
      (A.current (digitSite ring root (src + (R - 1) + 1))) hlx hly hmx hmy x hr
    have hR1 : R - 1 < R := by omega
    refine ⟨?_, o2, ?_, ?_⟩
    · rw [o1]
      simp only [tracked, trackedAt, laneCells, hR1, ↓reduceIte]
    · simp only [tracked, trackedAt, laneCells, hR1, ↓reduceIte]
      rw [curX]
      exact o3
    · intro q hq
      have hq' : q < R := by omega
      simp only [tracked, trackedAt, laneCells, hq', ↓reduceIte]
      rw [curFar]
      · intro he
        have := bankRepairDigitSiteInj ring root (by omega) (by omega) he
        omega
      · intro he
        rw [← bankRepairDigitSiteSucc] at he
        have := bankRepairDigitSiteInj ring root (by omega) (by omega) he
        omega
  refine ⟨ghostCorrStep ring hn root S R src hR hsrc hend hroot hb0 hbR hb2R hbF lane Base A j hj
    hbX hbY hc, hD', hT', ?_, ?_, ?_⟩
  · intro x id hx ho hop
    show id.time < x.time ∧ x.time ≤ A.clock + 1
    rcases recordedExportStepCases ring S A _ x hx with hx' | ⟨_, hs, hr⟩
    · have := hE1 x id hx' ho hop
      omega
    · obtain ⟨o1, o2, -, -⟩ := newExp x ho hs hr
      rw [hop] at o1
      have := hT (R - 1) id o1.symm
      omega
  · intro q id x hq hnew hx ho hop
    rcases moveOrigin hfr hm q _ hnew with ⟨p, hp, hp1, -⟩ | ⟨_, hf⟩
    · rcases recordedExportStepCases ring S A _ x hx with hx' | ⟨_, hs, hr⟩
      · exact hE2 p id x (by omega) hp1 hx' ho hop
      · obtain ⟨o1, -, o3, o4⟩ := newExp x ho hs hr
        rw [hop] at o1
        by_cases hqR : q = R - 1
        · rw [hqR, o3] at hnew
          cases hnew
        · have hnew' := hnew
          rw [o4 q (by omega)] at hnew'
          have := hD q (R - 1) id hnew' o1.symm
          omega
    · have he : DigitStamp.mk (A.clock + 1) (digitSite ring root j) lane = id :=
        DigitAtom.sampled.inj (Option.some.inj hf)
      have hid : id.time = A.clock + 1 := by rw [← he]
      rcases recordedExportStepCases ring S A _ x hx with hx' | ⟨_, hs, hr⟩
      · have := hE1 x id hx' ho hop
        omega
      · obtain ⟨o1, -, -, -⟩ := newExp x ho hs hr
        rw [hop] at o1
        have := hT (R - 1) id o1.symm
        omega
  · intro x y id hx hy hox hoy hopx hopy
    rcases recordedExportStepCases ring S A _ x hx with hx' | ⟨_, hsx, hrx⟩ <;>
      rcases recordedExportStepCases ring S A _ y hy with hy' | ⟨_, hsy, hry⟩
    · exact hE3 x y id hx' hy' hox hoy hopx hopy
    · obtain ⟨o1, -, -, -⟩ := newExp y hoy hsy hry
      rw [hopy] at o1
      exact absurd hopx (hE2 (R - 1) id x (by omega) o1.symm hx' hox)
    · obtain ⟨o1, -, -, -⟩ := newExp x hox hsx hrx
      rw [hopx] at o1
      exact absurd hopy (hE2 (R - 1) id y (by omega) o1.symm hy' hoy)
    · rw [hox.1] at hrx
      rw [hoy.1] at hry
      exact Option.some.inj (hrx.symm.trans hry)

end Distinct

/-! ### M1 along the coupled run -/

section DistinctRun

variable {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
  (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) (root : Fin n) (lane : DigitLane)
  (src R : Nat) (hR : 2 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n)
  (Base : Bool → DigitAtom n → Prop)

include hn hR hsrc hend in
theorem ghostCorrDistinctBankStep
    (z : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (hz : CohortLayout ring hbank root src R z.1)
    (hc : GhostCorrDistinct ring root lane src R Base (piD z.1.val.1) z.2) (e : Fin n) :
    CohortLayout ring hbank root src R (bankRepairDigitBoundaryAuditNext ring hbank z e).1 ∧
    GhostCorrDistinct ring root lane src R Base
      (piD (bankRepairDigitBoundaryAuditNext ring hbank z e).1.val.1)
      (bankRepairDigitBoundaryAuditNext ring hbank z e).2 := by
  refine ⟨(cohortBankStep ring hn hbank root lane src R hR hsrc hend z.1 hz e).1, ?_⟩
  obtain ⟨hL, hb0, hbR, hb2R, hbF⟩ := hz
  obtain ⟨heq, hroot, hbX, hbY⟩ := bankRepairDigitLeadBankEdge ring hn hbank root z.1 hL e
  show GhostCorrDistinct ring root lane src R Base (piD (bankRepairNext ring hbank z.1 e).val.1)
    (digitAuditStep ring (piD z.1.val.1) z.2 e)
  rw [heq]
  obtain ⟨j, hj, rfl⟩ := bankRepairDigitSiteSurj ring root e
  exact ghostCorrDistinctStep ring (by omega) root (piD z.1.val.1) R src hR hsrc hend hroot hb0
    hbR hb2R hbF lane Base z.2 j hj hbX hbY hc

include hn hR hsrc hend in
/-- **M1 run**: along every coupled word the layout and the distinct correspondence persist. -/
theorem ghostCorrDistinctRun (word : List (Fin n)) :
    ∀ z : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n,
      CohortLayout ring hbank root src R z.1 →
      GhostCorrDistinct ring root lane src R Base (piD z.1.val.1) z.2 →
      CohortLayout ring hbank root src R
        (word.foldl (bankRepairDigitBoundaryAuditNext ring hbank) z).1 ∧
      GhostCorrDistinct ring root lane src R Base
        (piD (word.foldl (bankRepairDigitBoundaryAuditNext ring hbank) z).1.val.1)
        (word.foldl (bankRepairDigitBoundaryAuditNext ring hbank) z).2 := by
  induction word with
  | nil => intro z h1 h2; exact ⟨h1, h2⟩
  | cons e rest ih =>
      intro z h1 h2
      obtain ⟨a, b⟩ :=
        ghostCorrDistinctBankStep ring hn hbank root lane src R hR hsrc hend Base z h1 h2 e
      exact ih _ a b

include hn hR hsrc hend in
/-- **M1 from the cycle entry**: at a coupled layout state with the distinct correspondence
whose masked lane is at the T24 entry, the first cycle starts and the distinct correspondence
holds along every continuation. -/
theorem ghostCorrDistinctCycEntry
    (z : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (hz : CohortLayout ring hbank root src R z.1)
    (hc : GhostCorrDistinct ring root lane src R Base (piD z.1.val.1) z.2)
    (hset : CohortSettling R 0 (cohortProj ring root lane src R (piD z.1.val.1)))
    (hyng : ∀ q, q < R →
      cohortTok R (cohortProj ring root lane src R (piD z.1.val.1)) q = .other ∨
      cohortTok R (cohortProj ring root lane src R (piD z.1.val.1)) q = .pkt (decide (q = 0))) :
    CohortCycStart R 0 (cohortProj ring root lane src R (piD z.1.val.1)) ((fun _ => 0), 0) ∧
    ∀ word : List (Fin n),
      CohortLayout ring hbank root src R
        (word.foldl (bankRepairDigitBoundaryAuditNext ring hbank) z).1 ∧
      GhostCorrDistinct ring root lane src R Base
        (piD (word.foldl (bankRepairDigitBoundaryAuditNext ring hbank) z).1.val.1)
        (word.foldl (bankRepairDigitBoundaryAuditNext ring hbank) z).2 :=
  ⟨cohortCycEntry hR hset hyng,
    fun word => ghostCorrDistinctRun ring hn hbank root lane src R hR hsrc hend Base word z hz hc⟩

end DistinctRun

/-! ### M1 at the audit start -/

section DistinctInitial

variable {c : Compiled} {n : Nat}

theorem initialNotSampled (lane : DigitLane) (i : Fin n) (v : DigitLaneView c)
    (id : DigitStamp n) :
    (DigitLaneGhost.initial (c := c) lane i v).out.atom ≠ some (.sampled id) ∧
    (DigitLaneGhost.initial (c := c) lane i v).input ≠ some (.sampled id) := by
  cases h : v.out <;> cases h' : v.input <;>
    simp [DigitLaneGhost.initial, h, h', DigitOutGhost.atom]

theorem trackedInitial (ring : DirectedRing n) (root : Fin n) (lane : DigitLane) (src R : Nat)
    (S : Fin n → ProjD c) (q : Nat) (id : DigitStamp n) :
    tracked ring root lane src R (digitAuditInitial S) q ≠ some (.sampled id) := by
  unfold tracked trackedAt laneCells
  by_cases h1 : q < R
  · rw [if_pos h1]
    show (laneGhost lane (digitGhostInitial S (digitSite ring root (src + q)))).out.atom ≠ _
    rw [laneGhostInitial]
    exact (initialNotSampled lane _ _ id).1
  · rw [if_neg h1]
    by_cases h2 : q < 2 * R
    · rw [if_pos h2]
      show (laneGhost lane (digitGhostInitial S (digitSite ring root (src + q)))).input ≠ _
      rw [laneGhostInitial]
      exact (initialNotSampled lane _ _ id).2
    · rw [if_neg h2]
      intro h
      cases h

theorem noExportInitial (S : Fin n → ProjD c) (x : DigitExport c n) :
    ¬ DigitRecordedExport (digitAuditInitial S) x := by
  intro h
  obtain ⟨f, hf, -⟩ := h
  exact absurd hf (List.not_mem_nil)

/-- M1 holds at the audit start with the inherited atoms as base. -/
theorem ghostCorrDistinctInitial (ring : DirectedRing n) (root : Fin n) (lane : DigitLane)
    (src R : Nat) (S : Fin n → ProjD c) :
    GhostCorrDistinct ring root lane src R (InheritedOk lane) S (digitAuditInitial S) :=
  ⟨ghostCorrInitial ring root lane src R S,
    fun q _ id h _ => absurd h (trackedInitial ring root lane src R S q id),
    fun q id h => absurd h (trackedInitial ring root lane src R S q id),
    fun x _ hx _ _ => absurd hx (noExportInitial S x),
    fun _ _ x _ _ hx _ _ => absurd hx (noExportInitial S x),
    fun x _ _ hx _ _ _ _ _ => absurd hx (noExportInitial S x)⟩

/-- M1 along every coupled word from the audit start in the layout class. -/
theorem ghostCorrDistinctFromStart {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) (root : Fin n) (lane : DigitLane)
    (src R : Nat) (hR : 2 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n)
    (z : BankReferenceState ring hbank) (hz : CohortLayout ring hbank root src R z)
    (word : List (Fin n)) :
    let w := word.foldl (bankRepairDigitBoundaryAuditNext ring hbank)
      (z, digitAuditInitial (piD z.val.1))
    CohortLayout ring hbank root src R w.1 ∧
      GhostCorrDistinct ring root lane src R (InheritedOk lane) (piD w.1.val.1) w.2 :=
  ghostCorrDistinctRun ring hn hbank root lane src R hR hsrc hend (InheritedOk lane) word
    (z, digitAuditInitial (piD z.val.1)) hz (ghostCorrDistinctInitial ring root lane src R _)

end DistinctInitial

end L3.CohortIdentity

#print axioms L3.CohortIdentity.ghostCorrDistinctStep
#print axioms L3.CohortIdentity.ghostCorrDistinctRun
#print axioms L3.CohortIdentity.ghostCorrDistinctCycEntry
