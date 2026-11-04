import Leader.L3.Bank.RepairDigitSitePin

/-!
# T33, rows: the target cells of one letter, with ledgers

The literal rows of one audit letter on the target cells `R ≤ q < 2R` of the pair, with the
ghost inputs (`ghostDel`, `ghostFinIn`, `ghostTermIn`) and the carry ledgers exposed:

* a launch (only at the marker cell `R`, on a settled input) creates a clean ledger with one use
  reading the cell's input atom, stamped now (`carryXD`);
* a live carry moving onto a settled cell appends one use reading that cell's input atom
  (`recordCarryUseD`), otherwise the right ledger is kept (`carryYKeepD`);
* a terminal receipt is recorded only from a live last cell, with that cell's ledger
  (`termLiveD`).

`tgtRows` collects them on the ring.
-/

namespace L3.UseRows

set_option autoImplicit false

open L3.RenewalReferenceClock
open L3.CohortDomination
open L3.CohortSites
open L3.GhostBridge
open L3.Correspondence
open L3.CohortIdentity
open L3.CohortLedger
open L3.CohortWindow

/-! ### Replay rows -/

section Replay

variable {c : Compiled} {n : Nat} (lane : DigitLane) (time : Nat) (source destination : Fin n)
  (x y : DigitLaneView c) (gx gy : DigitLaneGhost c n)

/-- Left ledger of the replay: retired, kept, or launched at a marker on a settled input with one
use reading the left input atom. -/
theorem replayCarryXCases (hlx : x.leader = false) (hly : y.leader = false) :
    (digitLaneReplay lane time source destination x y gx gy).x.carry = none ∨
    (digitLaneReplay lane time source destination x y gx gy).x.carry = gx.carry ∨
    (x.marker = true ∧ x.input.isS = true ∧ ∃ u : DigitUse c n, u.time = time ∧
      u.operand = gx.input ∧
      (digitLaneReplay lane time source destination x y gx gy).x.carry =
        some (DigitCarryGhost.mk none [u])) := by
  cases hxc : x.carryLive <;> cases hxm : x.marker <;>
    simp [digitLaneReplay, hlx, hly, hxc, hxm] <;> (repeat' split) <;> simp_all

/-- Without a live left carry the right ledger is kept. -/
theorem replayCarryYKeep (hlx : x.leader = false) (hly : y.leader = false)
    (hxc : x.carryLive = false) :
    (digitLaneReplay lane time source destination x y gx gy).y.carry = gy.carry := by
  simp [digitLaneReplay, hlx, hly, hxc] <;> (repeat' split) <;> simp_all

/-- A terminal receipt comes from a live left carry and records its ledger. -/
theorem replayTermLive (t : DigitTerminal c n)
    (h : (digitLaneReplay lane time source destination x y gx gy).terminal = some t) :
    x.carryLive = true ∧ t.ledger = gx.carry := by
  refine ⟨?_, (replayTerminal lane time source destination x y gx gy t h).1⟩
  cases hxc : x.carryLive
  · simp [digitLaneReplay, hxc] at h
  · rfl

end Replay

/-! ### The rows on the record fields -/

section RowsD

variable {c : Compiled} {n : Nat} (lane : DigitLane) (t : Nat) (e d : Fin n) (X Y : ProjD c)
  (gx gy : DigitGhost c n)

theorem shSOfIsS {A : Nat} (i : InTok A) (h : i.isS = true) :
    shS (bankRepairDigitInShOf i) = true := by
  cases i <;> simp_all [InTok.isS, bankRepairDigitInShOf, shS]

theorem carryXD (hlx : X.word.native.l = false) (hly : Y.word.native.l = false) :
    (laneGhost lane (digitService t e d X Y gx gy).x).carry = none ∨
    (laneGhost lane (digitService t e d X Y gx gy).x).carry = (laneGhost lane gx).carry ∨
    (laneMarkerX lane X Y = true ∧
      shS (bankRepairDigitInShOf (bankRepairDigitLaneIn lane X.top)) = true ∧
      ∃ u : DigitUse c n, u.time = t ∧ u.operand = (laneGhost lane gx).input ∧
        (laneGhost lane (digitService t e d X Y gx gy).x).carry =
          some (DigitCarryGhost.mk none [u])) := by
  have h := replayCarryXCases lane t e d (digitLaneView lane X (laneMarkerX lane X Y))
    (digitLaneView lane Y (laneMarkerY lane X Y)) (laneGhost lane gx) (laneGhost lane gy)
    (by rw [laneViewLeader]; exact hlx) (by rw [laneViewLeader]; exact hly)
  rw [laneViewMarker, laneViewIn] at h
  rw [serviceLaneX, serviceLane]
  rcases h with h | h | ⟨h1, h2, h3⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr ⟨h1, shSOfIsS _ h2, h3⟩)

theorem carryYKeepD (hlx : X.word.native.l = false) (hly : Y.word.native.l = false)
    (hkx : bankRepairDigitLaneLive lane X.top = false) :
    (laneGhost lane (digitService t e d X Y gx gy).y).carry = (laneGhost lane gy).carry := by
  rw [serviceLaneY, serviceLane]
  exact replayCarryYKeep lane t e d _ _ (laneGhost lane gx) (laneGhost lane gy)
    (by rw [laneViewLeader]; exact hlx) (by rw [laneViewLeader]; exact hly)
    (by rw [laneViewLive]; exact hkx)

theorem termLiveD (T : DigitTerminal c n)
    (h : (digitReceiptLane lane (digitService t e d X Y gx gy)).terminal = some T) :
    bankRepairDigitLaneLive lane X.top = true ∧ T.ledger = (laneGhost lane gx).carry := by
  rw [serviceLane] at h
  have h2 := replayTermLive lane t e d _ _ _ _ T h
  rw [laneViewLive] at h2
  exact h2

end RowsD

/-! ### The target rows on the ring -/

section Ring

variable {c : Compiled} {n : Nat}

/-- **Target rows of one letter**: target cells off the drawn edge are untouched; the delimiter
edge moves the input of cell `R` by `ghostDel` and keeps its ledger; a Fin edge moves the inputs
by `ghostFinIn`, retires, keeps or launches (at `R`) the left ledger, keeps the right ledger
unless the left carry is live, and appends a use on a live carry onto a settled cell; the
terminal edge moves the last input by `ghostTermIn` and records a terminal only from a live last
cell, with its ledger. -/
theorem tgtRows (ring : DirectedRing n) (hn : 2 ≤ n) (root : Fin n)
    (S : Fin n → ProjD c) (R src : Nat) (hR : 2 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n)
    (hroot : ∀ i, (S i).word.native.l = true ↔ i = root)
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
    (∀ q, R ≤ q → q < 2 * R → cohortEdgeOf root src R (digitSite ring root j) ≠ some q →
      cohortEdgeOf root src R (digitSite ring root j) ≠ some (q - 1) →
      laneCells ring root lane src (digitAuditStep ring S A (digitSite ring root j)).current q =
        laneCells ring root lane src A.current q) ∧
    (cohortEdgeOf root src R (digitSite ring root j) = some (R - 1) →
      (laneCells ring root lane src
          (digitAuditStep ring S A (digitSite ring root j)).current R).input =
        (ghostDel (DigitStamp.mk (A.clock + 1) (digitSite ring root j) lane)
          ((cohortProj ring root lane src R S).out (R - 1))
          ((cohortProj ring root lane src R S).inp R)
          ((cohortProj ring root lane src R S).live R)
          (laneCells ring root lane src A.current (R - 1)).out
          (laneCells ring root lane src A.current R).input).2 ∧
      (laneCells ring root lane src
          (digitAuditStep ring S A (digitSite ring root j)).current R).carry =
        (laneCells ring root lane src A.current R).carry) ∧
    (∀ k, cohortEdgeOf root src R (digitSite ring root j) = some k → R ≤ k → k + 1 < 2 * R →
      ((laneCells ring root lane src
          (digitAuditStep ring S A (digitSite ring root j)).current k).input,
        (laneCells ring root lane src
          (digitAuditStep ring S A (digitSite ring root j)).current (k + 1)).input) =
        ghostFinIn (decide (k = R)) ((cohortProj ring root lane src R S).inp k)
          ((cohortProj ring root lane src R S).live k)
          ((cohortProj ring root lane src R S).inp (k + 1))
          ((cohortProj ring root lane src R S).live (k + 1))
          (laneCells ring root lane src A.current k).input
          (laneCells ring root lane src A.current (k + 1)).input ∧
      ((laneCells ring root lane src
          (digitAuditStep ring S A (digitSite ring root j)).current k).carry = none ∨
        (laneCells ring root lane src
          (digitAuditStep ring S A (digitSite ring root j)).current k).carry =
          (laneCells ring root lane src A.current k).carry ∨
        (k = R ∧ shS ((cohortProj ring root lane src R S).inp k) = true ∧
          ∃ u : DigitUse c n, u.time = A.clock + 1 ∧
            u.operand = (laneCells ring root lane src A.current k).input ∧
            (laneCells ring root lane src
              (digitAuditStep ring S A (digitSite ring root j)).current k).carry =
              some (DigitCarryGhost.mk none [u]))) ∧
      ((cohortProj ring root lane src R S).live k = false →
        (laneCells ring root lane src
          (digitAuditStep ring S A (digitSite ring root j)).current (k + 1)).carry =
          (laneCells ring root lane src A.current (k + 1)).carry) ∧
      ((cohortProj ring root lane src R S).live k = true →
        (cohortProj ring root lane src R S).live (k + 1) = false →
        ∀ T, (cohortProj ring root lane src R S).inp (k + 1) = .S T →
        ∀ L, (laneCells ring root lane src A.current k).carry = some L →
        ∃ u : DigitUse c n, u.time = A.clock + 1 ∧
          u.operand = (laneCells ring root lane src A.current (k + 1)).input ∧
          (laneCells ring root lane src
            (digitAuditStep ring S A (digitSite ring root j)).current (k + 1)).carry =
            some (DigitCarryGhost.mk L.inherited (L.uses ++ [u])))) ∧
    (cohortEdgeOf root src R (digitSite ring root j) = some (2 * R - 1) →
      (laneCells ring root lane src
          (digitAuditStep ring S A (digitSite ring root j)).current (2 * R - 1)).input =
        ghostTermIn ((cohortProj ring root lane src R S).inp (2 * R - 1))
          ((cohortProj ring root lane src R S).live (2 * R - 1))
          (laneCells ring root lane src A.current (2 * R - 1)).input ∧
      ((laneCells ring root lane src
          (digitAuditStep ring S A (digitSite ring root j)).current (2 * R - 1)).carry = none ∨
        (laneCells ring root lane src
          (digitAuditStep ring S A (digitSite ring root j)).current (2 * R - 1)).carry =
          (laneCells ring root lane src A.current (2 * R - 1)).carry) ∧
      ∀ T, (digitReceiptLane lane (svcAt ring S A (digitSite ring root j))).terminal = some T →
        (cohortProj ring root lane src R S).live (2 * R - 1) = true ∧
          T.ledger = (laneCells ring root lane src A.current (2 * R - 1)).carry) := by
  by_cases hin : src ≤ j ∧ j < src + 2 * R
  · obtain ⟨k, rfl⟩ : ∃ k, j = src + k := ⟨j - src, by omega⟩
    have hke : cohortEdgeOf root src R (digitSite ring root (src + k)) = some k :=
      cohortEdgeOfSite ring root src R hend k (by omega)
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
    refine ⟨fun q h1 h2 hne1 hne2 => ?_, fun hk => ?_, fun k' hk' hRk hk2 => ?_, fun hk => ?_⟩
    · rw [hke] at hne1 hne2
      refine hfr q (fun h => hne1 (by rw [h])) (fun h => hne2 (by rw [h]; simp)) h2
    · -- Delimiter edge
      rw [hke] at hk
      have hk1 : k = R - 1 := Option.some.inj hk
      subst hk1
      have hmx : laneMarkerX lane (S (digitSite ring root (src + (R - 1))))
          (S (digitSite ring root (src + (R - 1) + 1))) = false := by
        rw [laneMarkerXBeta lane _ _ hbX]
        exact hbF (R - 1) (by omega) (by omega) (by omega)
      have hmy : laneMarkerY lane (S (digitSite ring root (src + (R - 1))))
          (S (digitSite ring root (src + (R - 1) + 1))) = true := by
        rw [laneMarkerYBeta lane _ _ hbY, show src + (R - 1) + 1 = src + R by omega]
        exact hbR
      have hrow := rowDelD lane (A.clock + 1) (digitSite ring root (src + (R - 1)))
        (ring.rightNeighbor (digitSite ring root (src + (R - 1))))
        (S (digitSite ring root (src + (R - 1)))) (S (digitSite ring root (src + (R - 1) + 1)))
        (A.current (digitSite ring root (src + (R - 1))))
        (A.current (digitSite ring root (src + (R - 1) + 1))) hlx hly hmx hmy
      have hyR : laneCells ring root lane src
          (digitAuditStep ring S A (digitSite ring root (src + (R - 1)))).current R =
          laneGhost lane (svcAt ring S A (digitSite ring root (src + (R - 1)))).y := by
        have h := hy
        rw [show R - 1 + 1 = R by omega] at h
        exact h
      have hcR : laneCells ring root lane src A.current R =
          laneGhost lane (A.current (digitSite ring root (src + (R - 1) + 1))) := by
        unfold laneCells
        rw [show src + (R - 1) + 1 = src + R by omega]
      rw [hyR, hcR, projOut ring root lane src R S (R - 1) (by omega),
        projIn ring root lane src R S R (Nat.le_refl R) (by omega),
        projLive ring root lane src R S R (Nat.le_refl R) (by omega),
        show src + R = src + (R - 1) + 1 by omega]
      exact ⟨congrArg Prod.snd hrow.1, hrow.2⟩
    · -- Fin edge
      rw [hke] at hk'
      have hkk : k = k' := Option.some.inj hk'
      subst hkk
      have hmy : laneMarkerY lane (S (digitSite ring root (src + k)))
          (S (digitSite ring root (src + k + 1))) = false := by
        rw [laneMarkerYBeta lane _ _ hbY]
        exact hbF (k + 1) (by omega) (by omega) (by omega)
      have hmxk : laneMarkerX lane (S (digitSite ring root (src + k)))
          (S (digitSite ring root (src + k + 1))) = decide (k = R) := by
        rw [laneMarkerXBeta lane _ _ hbX]
        by_cases h : k = R
        · subst h
          simp [hbR]
        · rw [hbF k (by omega) (by omega) h]
          simp [h]
      have hrow := rowFinD lane (A.clock + 1) (digitSite ring root (src + k))
        (ring.rightNeighbor (digitSite ring root (src + k)))
        (S (digitSite ring root (src + k))) (S (digitSite ring root (src + k + 1)))
        (A.current (digitSite ring root (src + k)))
        (A.current (digitSite ring root (src + k + 1))) hlx hly hmy
      rw [hmxk] at hrow
      refine ⟨?_, ?_, fun hkx => ?_, fun hkx hky T hT L hL => ?_⟩
      · rw [hx, hy, projIn ring root lane src R S k hRk (by omega),
          projLive ring root lane src R S k hRk (by omega),
          projIn ring root lane src R S (k + 1) (by omega) hk2,
          projLive ring root lane src R S (k + 1) (by omega) hk2]
        exact hrow.1
      · rcases carryXD lane (A.clock + 1) (digitSite ring root (src + k))
          (ring.rightNeighbor (digitSite ring root (src + k)))
          (S (digitSite ring root (src + k))) (S (digitSite ring root (src + k + 1)))
          (A.current (digitSite ring root (src + k)))
          (A.current (digitSite ring root (src + k + 1))) hlx hly with
          h | h | ⟨hm, hs, u, hu1, hu2, hu3⟩
        · left
          rw [hx]
          exact h
        · right; left
          rw [hx]
          exact h
        · right; right
          rw [hmxk] at hm
          refine ⟨by simpa using hm, ?_, u, hu1, hu2, by rw [hx]; exact hu3⟩
          rw [projIn ring root lane src R S k hRk (by omega)]
          exact hs
      · rw [projLive ring root lane src R S k hRk (by omega)] at hkx
        rw [hy]
        exact carryYKeepD lane (A.clock + 1) (digitSite ring root (src + k))
          (ring.rightNeighbor (digitSite ring root (src + k)))
          (S (digitSite ring root (src + k))) (S (digitSite ring root (src + k + 1)))
          (A.current (digitSite ring root (src + k)))
          (A.current (digitSite ring root (src + k + 1))) hlx hly hkx
      · rw [projLive ring root lane src R S k hRk (by omega)] at hkx
        rw [projLive ring root lane src R S (k + 1) (by omega) hk2] at hky
        rw [projIn ring root lane src R S (k + 1) (by omega) hk2] at hT
        have hrec := recordCarryUseD lane (A.clock + 1) (digitSite ring root (src + k))
          (ring.rightNeighbor (digitSite ring root (src + k)))
          (S (digitSite ring root (src + k))) (S (digitSite ring root (src + k + 1)))
          (A.current (digitSite ring root (src + k)))
          (A.current (digitSite ring root (src + k + 1))) hlx hly hmy hkx hky hT L hL
        rw [hy]
        refine ⟨_, ?_, ?_, hrec⟩ <;> rfl
    · -- Terminal edge
      rw [hke] at hk
      have hk1 : k = 2 * R - 1 := Option.some.inj hk
      subst hk1
      have hmx : laneMarkerX lane (S (digitSite ring root (src + (2 * R - 1))))
          (S (digitSite ring root (src + (2 * R - 1) + 1))) = false := by
        rw [laneMarkerXBeta lane _ _ hbX]
        exact hbF (2 * R - 1) (by omega) (by omega) (by omega)
      have hmy : laneMarkerY lane (S (digitSite ring root (src + (2 * R - 1))))
          (S (digitSite ring root (src + (2 * R - 1) + 1))) = true := by
        rw [laneMarkerYBeta lane _ _ hbY, show src + (2 * R - 1) + 1 = src + 2 * R by omega]
        exact hb2R
      have hrow := rowTermD lane (A.clock + 1) (digitSite ring root (src + (2 * R - 1)))
        (ring.rightNeighbor (digitSite ring root (src + (2 * R - 1))))
        (S (digitSite ring root (src + (2 * R - 1))))
        (S (digitSite ring root (src + (2 * R - 1) + 1)))
        (A.current (digitSite ring root (src + (2 * R - 1))))
        (A.current (digitSite ring root (src + (2 * R - 1) + 1))) hlx hly hmx hmy
      refine ⟨?_, ?_, fun T hT => ?_⟩
      · rw [hx, projIn ring root lane src R S (2 * R - 1) (by omega) (by omega),
          projLive ring root lane src R S (2 * R - 1) (by omega) (by omega)]
        exact hrow.1
      · rcases carryXD lane (A.clock + 1) (digitSite ring root (src + (2 * R - 1)))
          (ring.rightNeighbor (digitSite ring root (src + (2 * R - 1))))
          (S (digitSite ring root (src + (2 * R - 1))))
          (S (digitSite ring root (src + (2 * R - 1) + 1)))
          (A.current (digitSite ring root (src + (2 * R - 1))))
          (A.current (digitSite ring root (src + (2 * R - 1) + 1))) hlx hly with
          h | h | ⟨hm, -⟩
        · left
          rw [hx]
          exact h
        · right
          rw [hx]
          exact h
        · rw [hmx] at hm
          cases hm
      · have h2 := termLiveD lane (A.clock + 1) (digitSite ring root (src + (2 * R - 1)))
          (ring.rightNeighbor (digitSite ring root (src + (2 * R - 1))))
          (S (digitSite ring root (src + (2 * R - 1))))
          (S (digitSite ring root (src + (2 * R - 1) + 1)))
          (A.current (digitSite ring root (src + (2 * R - 1))))
          (A.current (digitSite ring root (src + (2 * R - 1) + 1))) T hT
        rw [projLive ring root lane src R S (2 * R - 1) (by omega) (by omega)]
        exact h2
  · have hnone : cohortEdgeOf root src R (digitSite ring root j) = none := by
      unfold cohortEdgeOf
      rw [cohortIdxSite ring root j hj, if_neg hin]
    have farNe : ∀ q, q < 2 * R → src + q ≠ j → src + q ≠ j + 1 →
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
    rw [hnone]
    refine ⟨fun q h1 h2 _ _ => farNe q h2 (by omega) (by omega), fun h => ?_,
      fun k h => ?_, fun h => ?_⟩ <;> cases h

end Ring

end L3.UseRows

#print axioms L3.UseRows.tgtRows
