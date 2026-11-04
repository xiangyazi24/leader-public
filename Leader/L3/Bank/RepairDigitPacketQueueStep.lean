import Leader.L3.Bank.RepairDigitPacketQueue

/-!
# Lemma e-packet, fourth clause: the step, part 1 (bookkeeping and the far edges)

* `recordedExportStep`: after one audit letter the recorded exports are the old ones and the new
  frame's export (stamped `clock + 1`, source the drawn edge).
* `delExportOff`: a letter whose edge is not the delimiter source site adds no delimiter export.
* `queueFrame`: the clause is carried with the same witness `χ` when the target shapes, the
  target input ghosts and the delimiter exports do not change.
* `queueFar`: on the coupled BANK x audit chain, every letter whose edge has both endpoints off the
  target and is not the delimiter edge (source motion inside the pair, and every edge outside
  `[src + R - 1, src + 2R)`) preserves `QueueAt` with the same `χ`.
-/

namespace L3.DigitPacketQueueStep

set_option autoImplicit false

open L3
open L3.RenewalReferenceClock
open L3.CohortDomination
open L3.CohortSites
open L3.Correspondence
open L3.GhostBridge
open L3.WidthDigit
open L3.DigitPacketRelease
open L3.DigitPacketTransport
open L3.DigitPacketQueue

variable {c : Compiled} {n : Nat}

/-- **Export bookkeeping.** Consumer: `delExportOff` and the export row. -/
theorem recordedExportStep (ring : DirectedRing n) (S : Fin n → ProjD c) (A : DigitAudit c n)
    (e : Fin n) (y : DigitExport c n) :
    DigitRecordedExport (digitAuditStep ring S A e) y ↔
      DigitRecordedExport A y ∨ (y.time = A.clock + 1 ∧ y.source = e ∧
        (digitReceiptLane y.lane (svcAt ring S A e)).exported = some y) := by
  constructor
  · rintro ⟨f, hf, h1, h2, h3⟩
    rcases List.mem_cons.mp hf with hf | hf
    · subst hf
      exact Or.inr ⟨h1.symm, h2.symm, h3⟩
    · exact Or.inl ⟨f, hf, h1, h2, h3⟩
  · rintro (⟨f, hf, h1, h2, h3⟩ | ⟨h1, h2, h3⟩)
    · exact ⟨f, List.mem_cons_of_mem _ hf, h1, h2, h3⟩
    · exact ⟨_, List.mem_cons_self .., h1.symm, h2.symm, h3⟩

/-- A letter off the delimiter source site adds no delimiter export. Consumer: `queueFar`. -/
theorem delExportOff (ring : DirectedRing n) (root : Fin n) (lane : DigitLane) (src R : Nat)
    (S : Fin n → ProjD c) (A : DigitAudit c n) (e : Fin n)
    (he : e ≠ digitSite ring root (src + (R - 1))) (y : DigitExport c n) :
    DelExport ring root lane src R (digitAuditStep ring S A e) y ↔
      DelExport ring root lane src R A y := by
  unfold DelExport
  rw [recordedExportStep]
  constructor
  · rintro ⟨h | ⟨_, h2, _⟩, h3, h4, h5⟩
    · exact ⟨h, h3, h4, h5⟩
    · exact absurd (h2.symm.trans h4) he
  · rintro ⟨h, h3, h4, h5⟩
    exact ⟨Or.inl h, h3, h4, h5⟩

/-- **Frame.** Unchanged target shapes, target input ghosts and delimiter exports carry the
clause with the same witness. Consumer: `queueFar`. -/
theorem queueFrame (ring : DirectedRing n) (root : Fin n) (lane : DigitLane) (src R : Nat)
    (S S' : Fin n → ProjD c) (A A' : DigitAudit c n) (χ : Nat → DigitExport c n)
    (hinp : ∀ q, R ≤ q → q < 2 * R →
      (cohortProj ring root lane src R S').inp q = (cohortProj ring root lane src R S).inp q)
    (hgh : ∀ q, R ≤ q → q < 2 * R →
      (laneCells ring root lane src A'.current q).input =
        (laneCells ring root lane src A.current q).input)
    (hex : ∀ y, DelExport ring root lane src R A' y ↔ DelExport ring root lane src R A y)
    (h : QueueAt ring root lane src R S A χ) : QueueAt ring root lane src R S' A' χ := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨fun q hq1 hq2 hp => ?_, fun q q' hq hlt hq' hp hp' => ?_,
    fun q y hq1 hq2 hp hy ht => ?_⟩
  · rw [hinp q hq1 hq2] at hp
    obtain ⟨a, b⟩ := h1 q hq1 hq2 hp
    exact ⟨(hex _).2 a, by rw [hgh q hq1 hq2]; exact b⟩
  · rw [hinp q hq (by omega)] at hp
    rw [hinp q' (by omega) hq'] at hp'
    exact h2 q q' hq hlt hq' hp hp'
  · rw [hinp q hq1 hq2] at hp
    obtain ⟨q', a, b, d, e⟩ := h3 q y hq1 hq2 hp ((hex y).1 hy) ht
    exact ⟨q', a, b, by rw [hinp q' a b]; exact d, e⟩

/-- Distinct offsets below `n` are distinct sites. Consumer: `queueFar`. -/
theorem siteNe (ring : DirectedRing n) (root : Fin n) (a b : Nat) (ha : a < n) (hb : b < n)
    (h : a ≠ b) : digitSite ring root a ≠ digitSite ring root b := by
  intro he
  have e1 := bankRepairDigitSiteVal ring root a
  have e2 := bankRepairDigitSiteVal ring root b
  rw [he] at e1
  have hr := root.isLt
  have : (root.val + a) % n = (root.val + b) % n := by rw [← e1, ← e2]
  by_cases h1 : root.val + a < n <;> by_cases h2 : root.val + b < n
  · rw [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2] at this; omega
  · rw [Nat.mod_eq_of_lt h1, Nat.mod_eq_sub_mod (by omega),
      Nat.mod_eq_of_lt (show root.val + b - n < n by omega)] at this; omega
  · rw [Nat.mod_eq_of_lt h2, Nat.mod_eq_sub_mod (by omega),
      Nat.mod_eq_of_lt (show root.val + a - n < n by omega)] at this; omega
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (show root.val + a - n < n by omega),
      Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (show root.val + b - n < n by omega)]
      at this; omega

/-- The right neighbour of the site at offset `j` is the site at offset `j + 1` (mod `n`).
Consumer: `queueFar`. -/
theorem siteSucc (ring : DirectedRing n) (root : Fin n) (j : Nat) :
    ring.rightNeighbor (digitSite ring root j) = digitSite ring root (j + 1) := rfl

/-- **The far edges.** On the coupled chain, a letter at offset `j` whose endpoints are both off
the target and which is not the delimiter edge preserves the clause with the same `χ`: source
motion inside the pair (`src ≤ j`, `j + 1 < src + R`), everything left of the pair, and everything
at or after the next delimiter. Consumer: `queueStep` (the composed step of the clause). -/
theorem queueFar (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) (root : Fin n) (lane : DigitLane)
    (src R : Nat) (hR : 2 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n)
    (x : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (hx : CohortLayout ring hbank root src R x.1) (j : Nat) (hj : j < n)
    (hfar : j + 1 < src + R ∨ src + 2 * R ≤ j) (χ : Nat → DigitExport _ n)
    (h : QueueAt ring root lane src R (piD x.1.val.1) x.2 χ) :
    QueueAt ring root lane src R
      (piD (widthDigitAuditNext (bankWidthDigitReference ring hn hbank) x
        (digitSite ring root j)).1.val.1)
      (widthDigitAuditNext (bankWidthDigitReference ring hn hbank) x (digitSite ring root j)).2 χ := by
  have hlane := (laneStep ring hn hbank root lane src R hR hsrc hend x hx (digitSite ring root j)).2
  -- the lane's target cells do not move
  have hinp : ∀ q, R ≤ q → q < 2 * R →
      (laneOfState ring hbank root lane src R
        (widthDigitAuditNext (bankWidthDigitReference ring hn hbank) x
          (digitSite ring root j))).inp q = (laneOfState ring hbank root lane src R x).inp q := by
    intro q _ _
    rw [hlane]
    unfold cohortEdgeOf
    rw [cohortIdxSite ring root j hj]
    by_cases hin : src ≤ j ∧ j < src + 2 * R
    · rw [if_pos hin]
      show (cohortEdge R _ (j - src)).inp q = _
      rw [(edgePipe R (j - src) _ (by omega)).1]
    · rw [if_neg hin]
      rfl
  refine queueFrame ring root lane src R _ _ _ _ χ hinp ?_ ?_ h
  · intro q hq1 hq2
    have h1 : digitSite ring root (src + q) ≠ digitSite ring root j :=
      siteNe ring root _ _ (by omega) hj (by omega)
    have h2 : digitSite ring root (src + q) ≠ ring.rightNeighbor (digitSite ring root j) := by
      rw [siteSucc]
      by_cases hjn : j + 1 < n
      · exact siteNe ring root _ _ (by omega) hjn (by omega)
      · have hj1 : j + 1 = n := by omega
        intro he
        have e1 := bankRepairDigitSiteVal ring root (src + q)
        have e2 := bankRepairDigitSiteVal ring root (j + 1)
        rw [he, e2, hj1, Nat.add_mod_right] at e1
        have hr := root.isLt
        rw [Nat.mod_eq_of_lt hr] at e1
        by_cases h3 : root.val + (src + q) < n
        · rw [Nat.mod_eq_of_lt h3] at e1; omega
        · rw [Nat.mod_eq_sub_mod (by omega),
            Nat.mod_eq_of_lt (show root.val + (src + q) - n < n by omega)] at e1; omega
    show (laneGhost lane ((digitAuditStep ring (piD x.1.val.1) x.2 (digitSite ring root j)).current
      (digitSite ring root (src + q)))).input = (laneGhost lane (x.2.current
      (digitSite ring root (src + q)))).input
    rw [curFar ring (piD x.1.val.1) x.2 _ _ h1 h2]
  · intro y
    exact delExportOff ring root lane src R (piD x.1.val.1) x.2 (digitSite ring root j)
      (siteNe ring root _ _ hj (by omega) (by omega)) y

end L3.DigitPacketQueueStep

#print axioms L3.DigitPacketQueueStep.recordedExportStep
#print axioms L3.DigitPacketQueueStep.delExportOff
#print axioms L3.DigitPacketQueueStep.queueFrame
#print axioms L3.DigitPacketQueueStep.siteNe
#print axioms L3.DigitPacketQueueStep.siteSucc
#print axioms L3.DigitPacketQueueStep.queueFar
