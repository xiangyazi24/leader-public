import Leader.L3.Bank.RepairDigitPacketQueueRows

/-!
# Lemma e-packet: the audit ghosts of one pair lane across one coupled letter

The ghost rows (`L3.GhostBridge.ghostPipe`, `ghostDel`, `ghostFinIn`, `ghostTermIn`) read on the
lane ghosts `laneCells` of one interior pair, on the coupled BANK x audit chain
`widthDigitAuditNext (bankWidthDigitReference ring hn hbank)`, from a layout state:

* `cellsFar`: a pair edge `k` leaves every other cell's ghost alone;
* `cellsPipe`, `cellsDel`, `cellsFin`, `cellsTerm`: the two ghosts of the edge are the ghost rows
  of the masked shapes, with the stamp `(clock + 1, site of k, lane)` and the border bits of the
  layout;
* `cellsRead`: a read of `U` on a source edge records a sample with that stamp and the border bit;
* `cellsOff`: a letter off the pair leaves every tracked output ghost, and every ghost but the
  entry cell's, alone.

The same plumbing as `L3.Correspondence.ghostCorrStep` and `L3.DigitPacketQueueRows`, stated once
for every per-cell ghost invariant. Consumer: `L3.PacketMomentLabels` (I1, I2) and the carry ghost
of the aligned completion (I3).
-/

namespace L3.PacketMomentCells

set_option autoImplicit false

open L3
open L3.RenewalReferenceClock
open L3.CohortDomination
open L3.CohortSites
open L3.Correspondence
open L3.GhostBridge
open L3.WidthDigit
open L3.DigitPacketTransport

variable {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
  (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) (root : Fin n) (lane : DigitLane)
  (src R : Nat)

/-- The next coupled state. -/
abbrev nxt (x : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (e : Fin n) : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n :=
  widthDigitAuditNext (bankWidthDigitReference ring hn hbank) x e

/-- The stamp of a letter at pair offset `k`. -/
abbrev stampAt (x : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (k : Nat) : DigitStamp n :=
  DigitStamp.mk (x.2.clock + 1) (digitSite ring root (src + k)) lane

include hn in
/-- **A pair edge leaves the other cells' ghosts alone.** Consumer: the per-cell invariants. -/
theorem cellsFar (hend : src + 2 * R < n)
    (x : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (k : Nat) (hk : k < 2 * R) (q : Nat) (hq : q < 2 * R) (h1 : q ≠ k) (h2 : q ≠ k + 1) :
    laneCells ring root lane src (nxt ring hn hbank x (digitSite ring root (src + k))).2.current q =
      laneCells ring root lane src x.2.current q := by
  show laneGhost lane ((digitAuditStep ring (piD x.1.val.1) x.2
    (digitSite ring root (src + k))).current (digitSite ring root (src + q))) = _
  rw [curFar]
  · rfl
  · intro he
    exact h1 (by have := bankRepairDigitSiteInj ring root (by omega) (by omega) he; omega)
  · intro he
    rw [← bankRepairDigitSiteSucc] at he
    exact h2 (by have := bankRepairDigitSiteInj ring root (by omega) (by omega) he; omega)

include hn in
/-- The two ghosts of a pair edge come from the service receipt. -/
theorem cellsXY (x : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (k : Nat) :
    laneCells ring root lane src (nxt ring hn hbank x (digitSite ring root (src + k))).2.current k =
      laneGhost lane (svcAt ring (piD x.1.val.1) x.2 (digitSite ring root (src + k))).x ∧
    laneCells ring root lane src (nxt ring hn hbank x (digitSite ring root (src + k))).2.current
        (k + 1) =
      laneGhost lane (svcAt ring (piD x.1.val.1) x.2 (digitSite ring root (src + k))).y := by
  constructor
  · show laneGhost lane ((digitAuditStep ring (piD x.1.val.1) x.2
      (digitSite ring root (src + k))).current (digitSite ring root (src + k))) = _
    rw [curX]
  · show laneGhost lane ((digitAuditStep ring (piD x.1.val.1) x.2
      (digitSite ring root (src + k))).current (digitSite ring root (src + (k + 1)))) = _
    rw [show digitSite ring root (src + (k + 1)) =
      ring.rightNeighbor (digitSite ring root (src + k)) from rfl, curY ring (by omega)]

/-- The layout facts at a pair edge: no leader at either end, and the border bits. -/
theorem edgeFacts (hsrc : 2 ≤ src) (hend : src + 2 * R < n)
    (x : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (hx : CohortLayout ring hbank root src R x.1) (k : Nat) (hk : k < 2 * R) :
    (piD x.1.val.1 (digitSite ring root (src + k))).word.native.l = false ∧
    (piD x.1.val.1 (digitSite ring root (src + k + 1))).word.native.l = false ∧
    laneMarkerX lane (piD x.1.val.1 (digitSite ring root (src + k)))
        (piD x.1.val.1 (digitSite ring root (src + k + 1))) = decide (k = 0 ∨ k = R) ∧
    laneMarkerY lane (piD x.1.val.1 (digitSite ring root (src + k)))
        (piD x.1.val.1 (digitSite ring root (src + k + 1))) = decide (k + 1 = R ∨ k + 1 = 2 * R) := by
  have hn5 : 5 ≤ n := by omega
  obtain ⟨hL, hb0, hbR, hb2R, hbF⟩ := hx
  obtain ⟨-, hroot, hbX, hbY⟩ := bankRepairDigitLeadBankEdge ring hn5 hbank root x.1 hL
    (digitSite ring root (src + k))
  have hbX' : (pairW (piD x.1.val.1 (digitSite ring root (src + k))).word
      (piD x.1.val.1 (digitSite ring root (src + k + 1))).word).1.beta =
      (piD x.1.val.1 (digitSite ring root (src + k))).word.beta := hbX
  have hbY' : (pairW (piD x.1.val.1 (digitSite ring root (src + k))).word
      (piD x.1.val.1 (digitSite ring root (src + k + 1))).word).2.beta =
      (piD x.1.val.1 (digitSite ring root (src + k + 1))).word.beta := hbY
  refine ⟨bankRepairDigitSiteNonroot ring root (piD x.1.val.1) hroot (src + k) (by omega)
    (by omega), bankRepairDigitSiteNonroot ring root (piD x.1.val.1) hroot (src + k + 1) (by omega)
    (by omega), ?_, ?_⟩
  · rw [laneMarkerXBeta lane _ _ hbX']
    by_cases h0 : k = 0
    · subst h0; rw [decide_eq_true (Or.inl rfl)]; exact hb0
    · by_cases hkR : k = R
      · subst hkR; rw [decide_eq_true (Or.inr rfl)]; exact hbR
      · rw [decide_eq_false (by omega)]; exact hbF k (by omega) (by omega) hkR
  · rw [laneMarkerYBeta lane _ _ hbY']
    by_cases h1 : k + 1 = R
    · rw [decide_eq_true (Or.inl h1), show src + k + 1 = src + R by omega]; exact hbR
    · by_cases h2 : k + 1 = 2 * R
      · rw [decide_eq_true (Or.inr h2), show src + k + 1 = src + 2 * R by omega]; exact hb2R
      · rw [decide_eq_false (by omega)]; exact hbF (k + 1) (by omega) (by omega) h1

include hn in
/-- **A Pipe edge on the two source ghosts.** Consumer: the per-cell invariants. -/
theorem cellsPipe (_hR : 2 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n)
    (x : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (hx : CohortLayout ring hbank root src R x.1) (k : Nat) (h1 : k + 1 < R) :
    ((laneCells ring root lane src (nxt ring hn hbank x (digitSite ring root (src + k))).2.current
        k).out,
      (laneCells ring root lane src (nxt ring hn hbank x (digitSite ring root (src + k))).2.current
        (k + 1)).out) =
    ghostPipe (stampAt ring hbank root lane src x k) (decide (k = 0))
      ((laneOfState ring hbank root lane src R x).out k)
      ((laneOfState ring hbank root lane src R x).out (k + 1))
      (laneCells ring root lane src x.2.current k).out
      (laneCells ring root lane src x.2.current (k + 1)).out := by
  obtain ⟨hlx, hly, hmX, hmY⟩ := edgeFacts ring hbank root lane src R hsrc hend x hx k (by omega)
  obtain ⟨hx', hy'⟩ := cellsXY ring hn hbank root lane src x k
  rw [hx', hy', show laneOfState ring hbank root lane src R x =
      cohortProj ring root lane src R (piD x.1.val.1) from rfl,
    projOut ring root lane src R _ k (by omega), projOut ring root lane src R _ (k + 1) h1]
  have hm0 : decide (k = 0) = laneMarkerX lane (piD x.1.val.1 (digitSite ring root (src + k)))
      (piD x.1.val.1 (digitSite ring root (src + k + 1))) := by
    rw [hmX]; by_cases h0 : k = 0 <;> simp [h0] <;> omega
  rw [hm0]
  exact rowPipeD lane (x.2.clock + 1) (digitSite ring root (src + k))
    (ring.rightNeighbor (digitSite ring root (src + k)))
    (piD x.1.val.1 (digitSite ring root (src + k))) (piD x.1.val.1 (digitSite ring root (src + k + 1)))
    (x.2.current (digitSite ring root (src + k)))
    (x.2.current (digitSite ring root (src + k + 1))) hlx hly
    (by rw [hmY]; simp; omega)

include hn in
/-- **The delivery edge on the port output and the border input.** Consumer: the per-cell
invariants. -/
theorem cellsDel (hR : 2 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n)
    (x : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (hx : CohortLayout ring hbank root src R x.1) (k : Nat) (h2 : k + 1 = R) :
    ((laneCells ring root lane src (nxt ring hn hbank x (digitSite ring root (src + k))).2.current
        k).out,
      (laneCells ring root lane src (nxt ring hn hbank x (digitSite ring root (src + k))).2.current
        (k + 1)).input) =
    ghostDel (stampAt ring hbank root lane src x k)
      ((laneOfState ring hbank root lane src R x).out k)
      ((laneOfState ring hbank root lane src R x).inp (k + 1))
      ((laneOfState ring hbank root lane src R x).live (k + 1))
      (laneCells ring root lane src x.2.current k).out
      (laneCells ring root lane src x.2.current (k + 1)).input ∧
    (laneCells ring root lane src (nxt ring hn hbank x (digitSite ring root (src + k))).2.current
        (k + 1)).carry = (laneCells ring root lane src x.2.current (k + 1)).carry := by
  obtain ⟨hlx, hly, hmX, hmY⟩ := edgeFacts ring hbank root lane src R hsrc hend x hx k (by omega)
  obtain ⟨hx', hy'⟩ := cellsXY ring hn hbank root lane src x k
  rw [hx', hy', show laneOfState ring hbank root lane src R x =
      cohortProj ring root lane src R (piD x.1.val.1) from rfl,
    projOut ring root lane src R _ k (by omega),
    projIn ring root lane src R _ (k + 1) (by omega) (by omega),
    projLive ring root lane src R _ (k + 1) (by omega) (by omega)]
  exact rowDelD lane (x.2.clock + 1) (digitSite ring root (src + k))
    (ring.rightNeighbor (digitSite ring root (src + k)))
    (piD x.1.val.1 (digitSite ring root (src + k))) (piD x.1.val.1 (digitSite ring root (src + k + 1)))
    (x.2.current (digitSite ring root (src + k)))
    (x.2.current (digitSite ring root (src + k + 1))) hlx hly
    (by rw [hmX]; simp; omega) (by rw [hmY]; simp; omega)

include hn in
/-- **An input-motion edge on the two target input ghosts.** Consumer: the per-cell
invariants. -/
theorem cellsFin (_hR : 2 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n)
    (x : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (hx : CohortLayout ring hbank root src R x.1) (k : Nat) (hk : R ≤ k) (h3 : k + 1 < 2 * R) :
    ((laneCells ring root lane src (nxt ring hn hbank x (digitSite ring root (src + k))).2.current
        k).input,
      (laneCells ring root lane src (nxt ring hn hbank x (digitSite ring root (src + k))).2.current
        (k + 1)).input) =
    ghostFinIn (decide (k = R))
      ((laneOfState ring hbank root lane src R x).inp k)
      ((laneOfState ring hbank root lane src R x).live k)
      ((laneOfState ring hbank root lane src R x).inp (k + 1))
      ((laneOfState ring hbank root lane src R x).live (k + 1))
      (laneCells ring root lane src x.2.current k).input
      (laneCells ring root lane src x.2.current (k + 1)).input := by
  obtain ⟨hlx, hly, hmX, hmY⟩ := edgeFacts ring hbank root lane src R hsrc hend x hx k (by omega)
  obtain ⟨hx', hy'⟩ := cellsXY ring hn hbank root lane src x k
  obtain ⟨hI, -, -⟩ := rowFinD lane (x.2.clock + 1) (digitSite ring root (src + k))
    (ring.rightNeighbor (digitSite ring root (src + k)))
    (piD x.1.val.1 (digitSite ring root (src + k))) (piD x.1.val.1 (digitSite ring root (src + k + 1)))
    (x.2.current (digitSite ring root (src + k)))
    (x.2.current (digitSite ring root (src + k + 1))) hlx hly (by rw [hmY]; simp; omega)
  have hm0 : laneMarkerX lane (piD x.1.val.1 (digitSite ring root (src + k)))
      (piD x.1.val.1 (digitSite ring root (src + k + 1))) = decide (k = R) := by
    rw [hmX]; by_cases h0 : k = R <;> simp [h0] <;> omega
  rw [hm0] at hI
  rw [hx', hy', show laneOfState ring hbank root lane src R x =
      cohortProj ring root lane src R (piD x.1.val.1) from rfl,
    projIn ring root lane src R _ k hk (by omega), projLive ring root lane src R _ k hk (by omega),
    projIn ring root lane src R _ (k + 1) (by omega) h3,
    projLive ring root lane src R _ (k + 1) (by omega) h3]
  exact hI

include hn in
/-- **The terminal edge on the last target input ghost.** Consumer: the per-cell invariants. -/
theorem cellsTerm (_hR : 2 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n)
    (x : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (hx : CohortLayout ring hbank root src R x.1) (k : Nat) (h4 : k + 1 = 2 * R) :
    (laneCells ring root lane src (nxt ring hn hbank x (digitSite ring root (src + k))).2.current
        k).input =
    ghostTermIn ((laneOfState ring hbank root lane src R x).inp k)
      ((laneOfState ring hbank root lane src R x).live k)
      (laneCells ring root lane src x.2.current k).input := by
  obtain ⟨hlx, hly, hmX, hmY⟩ := edgeFacts ring hbank root lane src R hsrc hend x hx k (by omega)
  obtain ⟨hx', -⟩ := cellsXY ring hn hbank root lane src x k
  obtain ⟨t1, -⟩ := rowTermD lane (x.2.clock + 1) (digitSite ring root (src + k))
    (ring.rightNeighbor (digitSite ring root (src + k)))
    (piD x.1.val.1 (digitSite ring root (src + k))) (piD x.1.val.1 (digitSite ring root (src + k + 1)))
    (x.2.current (digitSite ring root (src + k)))
    (x.2.current (digitSite ring root (src + k + 1))) hlx hly
    (by rw [hmX]; simp; omega) (by rw [hmY]; simp; omega)
  rw [hx', show laneOfState ring hbank root lane src R x =
      cohortProj ring root lane src R (piD x.1.val.1) from rfl,
    projIn ring root lane src R _ k (by omega) (by omega),
    projLive ring root lane src R _ k (by omega) (by omega)]
  exact t1

include hn in
/-- **A read on a source edge records its sample**, with the stamp of the letter and the border
bit as tail. Consumer: the per-cell invariants (fresh labels). -/
theorem cellsRead (_hR : 2 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n)
    (x : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (hx : CohortLayout ring hbank root src R x.1) (k : Nat) (h1 : k + 1 ≤ R)
    (hU : (laneOfState ring hbank root lane src R x).out k = .U) :
    ∃ smp : DigitSample (compileAdvice (ceilLogTwo n)) n, smp.id = stampAt ring hbank root lane src x k ∧
      smp.tail = decide (k = 0) ∧
      DigitRecordedSample (nxt ring hn hbank x (digitSite ring root (src + k))).2 smp := by
  obtain ⟨hlx, hly, hmX, -⟩ := edgeFacts ring hbank root lane src R hsrc hend x hx k (by omega)
  rw [show laneOfState ring hbank root lane src R x =
      cohortProj ring root lane src R (piD x.1.val.1) from rfl,
    projOut ring root lane src R _ k (by omega)] at hU
  obtain ⟨smp, hid, htl, hrec⟩ := freshSample ring (piD x.1.val.1) x.2
    (digitSite ring root (src + k)) lane hlx hly hU
  have hmX' : laneMarkerX lane (piD x.1.val.1 (digitSite ring root (src + k)))
      (piD x.1.val.1 (ring.rightNeighbor (digitSite ring root (src + k)))) =
      decide (k = 0 ∨ k = R) := hmX
  refine ⟨smp, hid, ?_, hrec⟩
  rw [htl, hmX']
  by_cases h0 : k = 0 <;> simp [h0] <;> omega

include hn in
/-- **A letter off the pair** leaves every tracked output ghost alone, and every ghost but the
entry cell's. Consumer: the per-cell invariants. -/
theorem cellsOff (hR : 2 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n)
    (x : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (hx : CohortLayout ring hbank root src R x.1) (e : Fin n) (he : cohortEdgeOf root src R e = none)
    (q : Nat) (hq : q < 2 * R) :
    (laneCells ring root lane src (nxt ring hn hbank x e).2.current q).out =
        (laneCells ring root lane src x.2.current q).out ∧
      (q ≠ 0 → laneCells ring root lane src (nxt ring hn hbank x e).2.current q =
        laneCells ring root lane src x.2.current q) := by
  have hn5 : 5 ≤ n := by omega
  obtain ⟨j, hj, rfl⟩ := bankRepairDigitSiteSurj ring root e
  have hin : ¬ (src ≤ j ∧ j < src + 2 * R) := by
    intro h
    unfold cohortEdgeOf at he
    rw [cohortIdxSite ring root j hj, if_pos h] at he
    cases he
  have farNe : ∀ q, q < 2 * R → src + q ≠ j → src + q ≠ j + 1 →
      laneCells ring root lane src (nxt ring hn hbank x (digitSite ring root j)).2.current q =
      laneCells ring root lane src x.2.current q := by
    intro q hq n1 n2
    show laneGhost lane ((digitAuditStep ring (piD x.1.val.1) x.2
      (digitSite ring root j)).current (digitSite ring root (src + q))) = _
    rw [curFar]
    · rfl
    · intro he
      exact n1 (bankRepairDigitSiteInj ring root (by omega) hj he)
    · intro he
      rw [← bankRepairDigitSiteSucc] at he
      by_cases hjn : j + 1 < n
      · exact n2 (bankRepairDigitSiteInj ring root (by omega) hjn he)
      · rw [show j + 1 = n by omega, bankRepairDigitSiteN] at he
        have := bankRepairDigitSiteInj ring root (k := src + q) (m := 0) (by omega) (by omega) he
        omega
  by_cases h1 : j + 1 = src ∧ q = 0
  · obtain ⟨h1, rfl⟩ := h1
    refine ⟨?_, fun h => absurd rfl h⟩
    obtain ⟨hL, hb0, -, -, -⟩ := hx
    obtain ⟨-, hroot, -, hbY⟩ := bankRepairDigitLeadBankEdge ring hn5 hbank root x.1 hL
      (digitSite ring root j)
    have hbY' : (pairW (piD x.1.val.1 (digitSite ring root j)).word
        (piD x.1.val.1 (digitSite ring root (j + 1))).word).2.beta =
        (piD x.1.val.1 (digitSite ring root (j + 1))).word.beta := hbY
    have hlx := bankRepairDigitSiteNonroot ring root (piD x.1.val.1) hroot j (by omega) (by omega)
    have hly := bankRepairDigitSiteNonroot ring root (piD x.1.val.1) hroot (j + 1) (by omega)
      (by omega)
    have hmy : laneMarkerY lane (piD x.1.val.1 (digitSite ring root j))
        (piD x.1.val.1 (digitSite ring root (j + 1))) = true := by
      rw [laneMarkerYBeta lane _ _ hbY', h1]
      exact hb0
    show (laneGhost lane ((digitAuditStep ring (piD x.1.val.1) x.2
      (digitSite ring root j)).current (digitSite ring root (src + 0)))).out = _
    rw [show digitSite ring root (src + 0) = ring.rightNeighbor (digitSite ring root j) by
      rw [← h1]; rfl, curY ring (by omega)]
    refine (rowEntryD lane (x.2.clock + 1) (digitSite ring root j)
      (ring.rightNeighbor (digitSite ring root j)) (piD x.1.val.1 (digitSite ring root j))
      (piD x.1.val.1 (digitSite ring root (j + 1))) (x.2.current (digitSite ring root j))
      (x.2.current (digitSite ring root (j + 1))) hlx hly hmy).trans ?_
    unfold laneCells
    rw [← h1]
  · have hfar := farNe q hq (by omega) (by omega)
    exact ⟨by rw [hfar], fun _ => hfar⟩

end L3.PacketMomentCells

#print axioms L3.PacketMomentCells.cellsFar
#print axioms L3.PacketMomentCells.cellsPipe
#print axioms L3.PacketMomentCells.cellsDel
#print axioms L3.PacketMomentCells.cellsFin
#print axioms L3.PacketMomentCells.cellsTerm
#print axioms L3.PacketMomentCells.cellsRead
#print axioms L3.PacketMomentCells.cellsOff
