import Leader.L3.Bank.RepairDigitPacketMomentCarry
import Leader.L3.Width.PacketMomentLaneGhosts

/-!
# Lemma e-packet, I3, at a boundary reference: the carry ledger of the aligned group

Generic form of the coupled part of `L3.PacketMomentCarry` (BankRepairDigitPacketMomentCarry) at
an arbitrary `WidthBoundaryReference`, by the port of `L3.WidthPacketMomentAudit` (state type,
`ref.phys`, `WidthCohortLayout`, `widthLaneOfState`, `widthLaneStep`, the `width` cell lemmas,
`L3.WidthPacketMoment.widthFinishMoment`); the replay rows, the settled-row lemmas, `isSIOf`,
`getAppendOne` and `CleanUses` are used as they are. From the aligned group, `ADone` is reached in
`WidthFinInv` with the bound `w^{R+1}` (`widthFinishCarryMoment`), so a terminal is recorded whose
clean ledger's `m`-th use reads the atom of target cell `R + m` after the group was formed
(`widthFinishTerminal`). `bankFinishCarryMomentCheck` checks the port at BANK.
-/

namespace L3.WidthPacketMomentCarry

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

open L3
open L3.PacketMoment
open L3.RenewalReferenceClock
open L3.CohortDomination
open L3.CohortSites
open L3.Correspondence
open L3.GhostBridge
open L3.WidthDigit
open L3.DigitPacketTransport
open L3.PacketMomentRelease
open L3.PacketMomentPending
open L3.PacketMomentV
open L3.PacketMomentVSerial
open L3.PacketMomentFinish
open L3.PacketMomentLabels
open L3.PacketMomentGroupLabels
open L3.PacketMomentCarry
open L3.WidthWave
open L3.WidthPacketMoment
open L3.WidthPacketMomentAudit

section Ported

variable {n : Nat} (ring : DirectedRing n) (ref : WidthBoundaryReference ring) (hn : 5 ≤ n)
  (root : Fin n) (lane : DigitLane) (src R : Nat)

include hn

/-- **The right ledger of a pair edge is kept** off the move and the launch. Consumer:
`widthFinInvStep`. -/
theorem widthCarryKeepY (_hR : 2 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n)
    (x : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (hx : WidthCohortLayout ref.toWidthDigitReference root src R x.1) (k : Nat) (hk : k < 2 * R)
    (h : k + 1 = R ∨ (R ≤ k ∧ (widthLaneOfState ref.toWidthDigitReference root lane src R x).live k = false)) :
    (laneCells ring root lane src (widthNxt ring ref x (digitSite ring root (src + k))).2.current
        (k + 1)).carry = (laneCells ring root lane src x.2.current (k + 1)).carry := by
  obtain ⟨hlx, hly, -, hmY⟩ := widthEdgeFacts ring ref hn root lane src R hsrc hend x hx k hk
  obtain ⟨-, hy'⟩ := widthCellsXY ring ref hn root lane src x k
  rw [hy']
  unfold svcAt
  rw [serviceLaneY, serviceLane]
  refine replayKeepY lane _ _ _ _ _ _ _ (by rw [laneViewLeader]; exact hlx)
    (by rw [laneViewLeader]; exact hly) ?_
  rcases h with h | ⟨hk', hl⟩
  · right
    rw [laneViewMarker]
    have hmY' : laneMarkerY lane (piD (ref.phys x.1) (digitSite ring root (src + k)))
        (piD (ref.phys x.1) (ring.rightNeighbor (digitSite ring root (src + k)))) =
        decide (k + 1 = R ∨ k + 1 = 2 * R) := hmY
    rw [hmY']
    simp [h]
  · left
    rw [laneViewLive]
    have := projLive ring root lane src R (piD (ref.phys x.1)) k hk' hk
    rw [← this]
    exact hl

/-- **The launch** at the border cell `R`. Consumer: `widthFinInvStep`. -/
theorem widthCarryLaunch (hR : 2 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n)
    (x : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (hx : WidthCohortLayout ref.toWidthDigitReference root src R x.1)
    (hl : (widthLaneOfState ref.toWidthDigitReference root lane src R x).live R = false)
    (hS : isSI ((widthLaneOfState ref.toWidthDigitReference root lane src R x).inp R) = true) :
    ∃ u : DigitUse (compileAdvice (ceilLogTwo n)) n,
      (laneCells ring root lane src (widthNxt ring ref x (digitSite ring root (src + R))).2.current
          R).carry = some (DigitCarryGhost.mk none [u]) ∧
        u.operand = (laneCells ring root lane src x.2.current R).input ∧
        u.time = x.2.clock + 1 := by
  obtain ⟨hlx, hly, hmX, -⟩ := widthEdgeFacts ring ref hn root lane src R hsrc hend x hx R (by omega)
  obtain ⟨hx', -⟩ := widthCellsXY ring ref hn root lane src x R
  rw [hx']
  unfold svcAt
  rw [serviceLaneX, serviceLane]
  refine replayLaunch lane _ _ _ _ _ _ _ (by rw [laneViewLeader]; exact hlx)
    (by rw [laneViewLeader]; exact hly) ?_ ?_ ?_
  · rw [laneViewLive]
    rw [← projLive ring root lane src R (piD (ref.phys x.1)) R (Nat.le_refl _) (by omega)]
    exact hl
  · rw [laneViewMarker]
    have hmX' : laneMarkerX lane (piD (ref.phys x.1) (digitSite ring root (src + R)))
        (piD (ref.phys x.1) (ring.rightNeighbor (digitSite ring root (src + R)))) =
        decide (R = 0 ∨ R = R) := hmX
    rw [hmX']
    simp
  · rw [laneViewIn, ← isSIOf]
    rw [← projIn ring root lane src R (piD (ref.phys x.1)) R (Nat.le_refl _) (by omega)]
    exact hS

/-- **The move**: the live carry on cell `k` consumes the settled right cell, appending a use
that reads its input, stamped now. Consumer: `widthFinInvStep`. -/
theorem widthCarryMove (_hR : 2 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n)
    (x : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (hx : WidthCohortLayout ref.toWidthDigitReference root src R x.1) (k : Nat) (hk : R ≤ k) (hk2 : k + 1 < 2 * R)
    (hl : (widthLaneOfState ref.toWidthDigitReference root lane src R x).live k = true)
    (hl' : (widthLaneOfState ref.toWidthDigitReference root lane src R x).live (k + 1) = false) (T : Bool)
    (hS : (widthLaneOfState ref.toWidthDigitReference root lane src R x).inp (k + 1) = .S T)
    (L : DigitCarryGhost (compileAdvice (ceilLogTwo n)) n)
    (hL : (laneCells ring root lane src x.2.current k).carry = some L) :
    ∃ u : DigitUse (compileAdvice (ceilLogTwo n)) n,
      (laneCells ring root lane src (widthNxt ring ref x (digitSite ring root (src + k))).2.current
          (k + 1)).carry = some (DigitCarryGhost.mk L.inherited (L.uses ++ [u])) ∧
        u.operand = (laneCells ring root lane src x.2.current (k + 1)).input ∧
        u.time = x.2.clock + 1 := by
  obtain ⟨hlx, hly, -, hmY⟩ := widthEdgeFacts ring ref hn root lane src R hsrc hend x hx k (by omega)
  obtain ⟨-, hy'⟩ := widthCellsXY ring ref hn root lane src x k
  rw [hy']
  unfold svcAt
  have hmY' : laneMarkerY lane (piD (ref.phys x.1) (digitSite ring root (src + k)))
      (piD (ref.phys x.1) (ring.rightNeighbor (digitSite ring root (src + k)))) = false := by
    have h0 : laneMarkerY lane (piD (ref.phys x.1) (digitSite ring root (src + k)))
        (piD (ref.phys x.1) (ring.rightNeighbor (digitSite ring root (src + k)))) =
        decide (k + 1 = R ∨ k + 1 = 2 * R) := hmY
    rw [h0]; simp; omega
  have hkx : bankRepairDigitLaneLive lane (piD (ref.phys x.1) (digitSite ring root (src + k))).top =
      true := by
    rw [← projLive ring root lane src R (piD (ref.phys x.1)) k hk (by omega)]; exact hl
  have hky : bankRepairDigitLaneLive lane
      (piD (ref.phys x.1) (ring.rightNeighbor (digitSite ring root (src + k)))).top = false := by
    have := projLive ring root lane src R (piD (ref.phys x.1)) (k + 1) (by omega) hk2
    rw [← hl']
    exact this.symm
  have hiy : bankRepairDigitInShOf (bankRepairDigitLaneIn lane
      (piD (ref.phys x.1) (ring.rightNeighbor (digitSite ring root (src + k)))).top) = .S T := by
    have := projIn ring root lane src R (piD (ref.phys x.1)) (k + 1) (by omega) hk2
    rw [← hS]
    exact this.symm
  rw [recordCarryUseD lane (x.2.clock + 1) (digitSite ring root (src + k))
    (ring.rightNeighbor (digitSite ring root (src + k)))
    (piD (ref.phys x.1) (digitSite ring root (src + k)))
    (piD (ref.phys x.1) (ring.rightNeighbor (digitSite ring root (src + k))))
    (x.2.current (digitSite ring root (src + k)))
    (x.2.current (ring.rightNeighbor (digitSite ring root (src + k)))) hlx hly hmY' hkx hky hiy L hL]
  exact ⟨_, rfl, rfl, rfl⟩

/-- **The terminal**: the live carry on the last cell records a terminal on the terminal edge
with its ledger. Consumer: `widthFinInvStep`. -/
theorem widthCarryTerminal (_hR : 2 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n)
    (x : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (hx : WidthCohortLayout ref.toWidthDigitReference root src R x.1) (k : Nat) (hk : k + 1 = 2 * R)
    (hl : (widthLaneOfState ref.toWidthDigitReference root lane src R x).live k = true) :
    ∃ U : DigitTerminal (compileAdvice (ceilLogTwo n)) n,
      DigitRecordedTerminal (widthNxt ring ref x (digitSite ring root (src + k))).2 U ∧
        U.lane = lane ∧ U.source = digitSite ring root (src + k) ∧ U.time = x.2.clock + 1 ∧
        U.ledger = (laneCells ring root lane src x.2.current k).carry := by
  obtain ⟨hlx, hly, -, hmY⟩ := widthEdgeFacts ring ref hn root lane src R hsrc hend x hx k (by omega)
  have hmY' : laneMarkerY lane (piD (ref.phys x.1) (digitSite ring root (src + k)))
      (piD (ref.phys x.1) (ring.rightNeighbor (digitSite ring root (src + k)))) = true := by
    have h0 : laneMarkerY lane (piD (ref.phys x.1) (digitSite ring root (src + k)))
        (piD (ref.phys x.1) (ring.rightNeighbor (digitSite ring root (src + k)))) =
        decide (k + 1 = R ∨ k + 1 = 2 * R) := hmY
    rw [h0]; simp; omega
  have hkx : bankRepairDigitLaneLive lane (piD (ref.phys x.1) (digitSite ring root (src + k))).top =
      true := by
    rw [← projLive ring root lane src R (piD (ref.phys x.1)) k (by omega) (by omega)]; exact hl
  have ht := recordTerminalD lane (x.2.clock + 1) (digitSite ring root (src + k))
    (ring.rightNeighbor (digitSite ring root (src + k)))
    (piD (ref.phys x.1) (digitSite ring root (src + k)))
    (piD (ref.phys x.1) (ring.rightNeighbor (digitSite ring root (src + k))))
    (x.2.current (digitSite ring root (src + k)))
    (x.2.current (ring.rightNeighbor (digitSite ring root (src + k)))) hlx hly hmY' hkx
  exact ⟨DigitTerminal.mk (x.2.clock + 1) lane (digitSite ring root (src + k))
    (ring.rightNeighbor (digitSite ring root (src + k)))
    (laneGhost lane (x.2.current (digitSite ring root (src + k)))).carry
    (digitLaneView lane (piD (ref.phys x.1) (digitSite ring root (src + k)))
      (laneMarkerX lane (piD (ref.phys x.1) (digitSite ring root (src + k)))
        (piD (ref.phys x.1) (ring.rightNeighbor (digitSite ring root (src + k)))))).carryBit
    (digitLaneView lane (piD (ref.phys x.1) (digitSite ring root (src + k)))
      (laneMarkerX lane (piD (ref.phys x.1) (digitSite ring root (src + k)))
        (piD (ref.phys x.1) (ring.rightNeighbor (digitSite ring root (src + k)))))).carryError,
    ⟨_, List.mem_cons_self .., rfl, rfl, ht⟩, rfl, rfl, rfl, rfl⟩

/-- **A settled target input that stays settled keeps its atom**, under every coupled letter.
Consumer: `widthFinInvStep`. -/
theorem widthSettledAtomKeep (hR : 2 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n)
    (x : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (hx : WidthCohortLayout ref.toWidthDigitReference root src R x.1) (e : Fin n) (q : Nat) (hq1 : R ≤ q)
    (hq2 : q < 2 * R) (h0 : isSI ((widthLaneOfState ref.toWidthDigitReference root lane src R x).inp q) = true)
    (h1 : isSI ((widthLaneOfState ref.toWidthDigitReference root lane src R (widthNxt ring ref x e)).inp q) = true) :
    (laneCells ring root lane src (widthNxt ring ref x e).2.current q).input =
      (laneCells ring root lane src x.2.current q).input := by
  have hls := (widthLaneStep ref.toWidthDigitReference ref.singletonFixed hn root lane src R hR hsrc hend x hx e).2
  rw [hls] at h1
  rcases hE : cohortEdgeOf root src R e with _ | k
  · exact congrArg DigitLaneGhost.input
      ((widthCellsOff ring ref hn root lane src R hR hsrc hend x hx e hE q hq2).2 (by omega))
  · obtain ⟨hk, rfl⟩ := edgeOfSome ring root src R e k hE
    rw [hE] at h1
    simp only [cohortLaneStep] at h1
    by_cases hqk : q ≠ k ∧ q ≠ k + 1
    · exact congrArg DigitLaneGhost.input
        (widthCellsFar ring ref hn root lane src R hend x k hk q hq2 hqk.1 hqk.2)
    · by_cases e1 : k + 1 < R
      · exfalso; omega
      · by_cases e2 : k + 1 = R
        · have hq : q = k + 1 := by omega
          subst hq
          obtain ⟨hg, -⟩ := widthCellsDel ring ref hn root lane src R hR hsrc hend x hx k e2
          have hg2 := congrArg Prod.snd hg
          dsimp only at hg2
          rw [hg2]
          refine delKeepY _ _ _ _ _ _ h0 ?_
          have : (cohortEdge R (widthLaneOfState ref.toWidthDigitReference root lane src R x) k).inp (k + 1) =
              (bankRepairDigitDelStep ((widthLaneOfState ref.toWidthDigitReference root lane src R x).out k)
                ((widthLaneOfState ref.toWidthDigitReference root lane src R x).inp (k + 1))
                ((widthLaneOfState ref.toWidthDigitReference root lane src R x).live (k + 1))).2.1 := by
            unfold cohortEdge; rw [if_neg e1, if_pos e2]
            show cohortUpd _ (k + 1) _ (k + 1) = _
            simp [cohortUpd]
          rw [← this]; exact h1
        · by_cases e3 : k + 1 < 2 * R
          · have hinp : (cohortEdge R (widthLaneOfState ref.toWidthDigitReference root lane src R x) k).inp =
                cohortUpd (cohortUpd (widthLaneOfState ref.toWidthDigitReference root lane src R x).inp k
                  (bankRepairDigitFinStep (decide (k = R))
                    ((widthLaneOfState ref.toWidthDigitReference root lane src R x).inp k)
                    ((widthLaneOfState ref.toWidthDigitReference root lane src R x).live k)
                    ((widthLaneOfState ref.toWidthDigitReference root lane src R x).inp (k + 1))
                    ((widthLaneOfState ref.toWidthDigitReference root lane src R x).live (k + 1))).1) (k + 1)
                  (bankRepairDigitFinStep (decide (k = R))
                    ((widthLaneOfState ref.toWidthDigitReference root lane src R x).inp k)
                    ((widthLaneOfState ref.toWidthDigitReference root lane src R x).live k)
                    ((widthLaneOfState ref.toWidthDigitReference root lane src R x).inp (k + 1))
                    ((widthLaneOfState ref.toWidthDigitReference root lane src R x).live (k + 1))).2.2.1 := by
              unfold cohortEdge; rw [if_neg e1, if_neg e2, if_pos e3]
            have hg := widthCellsFin ring ref hn root lane src R hR hsrc hend x hx k (by omega) e3
            have hg1 := congrArg Prod.fst hg
            have hg2 := congrArg Prod.snd hg
            dsimp only [ghostFinIn] at hg1 hg2
            rw [hinp] at h1
            by_cases hq : q = k
            · subst hq
              simp only [cohortUpd, show q ≠ q + 1 by omega, if_false, if_true] at h1
              rw [hg1]
              exact finKeepX _ _ _ _ _ _ h0 h1
            · have hq' : q = k + 1 := by omega
              subst hq'
              simp only [cohortUpd, if_true] at h1
              rw [hg2]
              exact finKeepY _ _ _ _ _ _ _ h0 h1
          · have e4 : k + 1 = 2 * R := by omega
            have hq : q = k := by omega
            subst hq
            have hinp : (cohortEdge R (widthLaneOfState ref.toWidthDigitReference root lane src R x) q).inp =
                cohortUpd (widthLaneOfState ref.toWidthDigitReference root lane src R x).inp q
                  (cohortTermStep ((widthLaneOfState ref.toWidthDigitReference root lane src R x).inp q)
                    ((widthLaneOfState ref.toWidthDigitReference root lane src R x).live q)).1 := by
              unfold cohortEdge; rw [if_neg e1, if_neg e2, if_neg e3, if_pos e4]
            rw [hinp] at h1
            simp only [cohortUpd, if_true] at h1
            rw [widthCellsTerm ring ref hn root lane src R hR hsrc hend x hx q e4]
            exact termKeep _ _ _ h0 h1

/-! ### The ledger of the aligned group -/

/-- **A terminal of the group**: recorded on the terminal edge after `t0`, with a clean ledger
of `R` uses reading `op`. Consumer: `widthFinishTerminal`, the aligned completion. -/
def WidthTermDone (t0 : Nat) (op : Nat → Option (DigitAtom n))
    (x : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n) : Prop :=
  ∃ U : DigitTerminal (compileAdvice (ceilLogTwo n)) n,
    DigitRecordedTerminal x.2 U ∧ U.lane = lane ∧
      U.source = digitSite ring root (src + (2 * R - 1)) ∧ t0 < U.time ∧
      ∃ L, U.ledger = some L ∧ CleanUses t0 op R L

/-- **The finish phase with its ledger.** Consumer: `widthFinishCarryMoment`. -/
def WidthFinInv (t0 : Nat) (op : Nat → Option (DigitAtom n))
    (x : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n) : Prop :=
  WidthCohortLayout ref.toWidthDigitReference root src R x.1 ∧ t0 ≤ x.2.clock ∧
    ((AGroup R (widthLaneOfState ref.toWidthDigitReference root lane src R x) ∧
        ∀ j, j < R → (laneCells ring root lane src x.2.current (R + j)).input = op j) ∨
      (∃ j, ARun R j (widthLaneOfState ref.toWidthDigitReference root lane src R x) ∧
        (∀ q, j < q → q < 2 * R → (laneCells ring root lane src x.2.current q).input = op (q - R)) ∧
        ∃ L, (laneCells ring root lane src x.2.current j).carry = some L ∧
          CleanUses t0 op (j + 1 - R) L) ∨
      (ADone R (widthLaneOfState ref.toWidthDigitReference root lane src R x) ∧
        WidthTermDone ring ref root lane src R t0 op x))

/-- **One letter of the finish phase keeps the ledger invariant**: the launch starts a clean
ledger reading the border cell, each move appends a use reading the next settled cell, the
terminal records the ledger; every other letter keeps the carry and the settled atoms.
Consumer: `widthFinishCarryMoment`. -/
theorem widthFinInvStep (hR : 2 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n) (t0 : Nat)
    (op : Nat → Option (DigitAtom n))
    (x : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n) (e : Fin n)
    (h : WidthFinInv ring ref root lane src R t0 op x)
    (hnd : ¬ ADone R (widthLaneOfState ref.toWidthDigitReference root lane src R x)) :
    WidthFinInv ring ref root lane src R t0 op (widthNxt ring ref x e) := by
  obtain ⟨hx, ht0, hcase⟩ := h
  obtain ⟨h1, hls⟩ := widthLaneStep ref.toWidthDigitReference ref.singletonFixed hn root lane src R hR hsrc hend x hx e
  have hclk : (widthNxt ring ref x e).2.clock = x.2.clock + 1 := rfl
  refine ⟨h1, by rw [hclk]; omega, ?_⟩
  have hkeep := fun q hq1 hq2 h0 h1' =>
    widthSettledAtomKeep ring ref hn root lane src R hR hsrc hend x hx e q hq1 hq2 h0 h1'
  rcases hcase with ⟨hg, hops⟩ | ⟨j, hj, hops, L, hL, hcl⟩ | ⟨hd, _⟩
  · -- the aligned group
    obtain ⟨_, hgc⟩ := hg
    have gS : ∀ q, R ≤ q → q < 2 * R →
        isSI ((widthLaneOfState ref.toWidthDigitReference root lane src R x).inp q) = true := by
      intro q h1 h2
      have hq := hgc q h1 h2
      by_cases h0 : q = R
      · rw [hq.2.1 (by omega)]; rfl
      · rw [hq.2.2.1 (by omega)]; rfl
    rcases hE : cohortEdgeOf root src R e with _ | k
    · left
      have hs : widthLaneOfState ref.toWidthDigitReference root lane src R (widthNxt ring ref x e) =
          widthLaneOfState ref.toWidthDigitReference root lane src R x := by rw [hls, hE]; rfl
      refine ⟨by rw [hs]; exact ⟨by omega, hgc⟩, fun j hj => ?_⟩
      rw [((widthCellsOff ring ref hn root lane src R hR hsrc hend x hx e hE (R + j)
        (by omega)).2 (by omega))]
      exact hops j hj
    · obtain ⟨hk, rfl⟩ := edgeOfSome ring root src R e k hE
      have hs : widthLaneOfState ref.toWidthDigitReference root lane src R
          (widthNxt ring ref x (digitSite ring root (src + k))) =
          cohortEdge R (widthLaneOfState ref.toWidthDigitReference root lane src R x) k := by rw [hls, hE]; rfl
      obtain ⟨gl, gn⟩ := groupStep R hR _ k ⟨by omega, hgc⟩
      by_cases hkR : k = R
      · subst hkR
        have hrun := gl rfl
        right; left
        refine ⟨k, by rw [hs]; exact hrun, fun q hq1 hq2 => ?_, ?_⟩
        · rw [hkeep q (by omega) hq2 (gS q (by omega) hq2) (by
            rw [hs, (hrun.2.2 q (by omega) hq2).2.2.2 hq1]; rfl)]
          rw [← hops (q - k) (by omega), show k + (q - k) = q by omega]
        · obtain ⟨u, hu, huo, hut⟩ := widthCarryLaunch ring ref hn root lane src k hR hsrc hend x hx
            (hgc k (Nat.le_refl _) (by omega)).1 (gS k (Nat.le_refl _) (by omega))
          refine ⟨_, hu, rfl, by simp, fun i w hw => ?_⟩
          have hi : i = 0 ∧ w = u := by
            rcases i with _ | i
            · simp at hw; exact ⟨rfl, hw.symm⟩
            · simp at hw
          obtain ⟨rfl, rfl⟩ := hi
          refine ⟨by rw [huo, ← hops 0 (by omega)]; rfl, by rw [hut]; omega⟩
      · left
        have hg' := gn hkR
        refine ⟨by rw [hs]; exact hg', fun j hj => ?_⟩
        rw [hkeep (R + j) (by omega) (by omega) (gS (R + j) (by omega) (by omega)) (by
          rw [hs]
          obtain ⟨_, hgc'⟩ := hg'
          have hq := hgc' (R + j) (by omega) (by omega)
          by_cases h0 : R + j = R
          · rw [hq.2.1 (by omega)]; rfl
          · rw [hq.2.2.1 (by omega)]; rfl)]
        exact hops j hj
  · -- the carry on cell j
    obtain ⟨hj1, hj2, hjc⟩ := hj
    have runS : ∀ (s : CohortLane) (j' : Nat), ARun R j' s → ∀ q, j' < q → q < 2 * R →
        isSI (s.inp q) = true := by
      intro s j' hr q h1 h2
      rw [(hr.2.2 q (by have := hr.1; omega) h2).2.2.2 h1]; rfl
    rcases hE : cohortEdgeOf root src R e with _ | k
    · right; left
      have hs : widthLaneOfState ref.toWidthDigitReference root lane src R (widthNxt ring ref x e) =
          widthLaneOfState ref.toWidthDigitReference root lane src R x := by rw [hls, hE]; rfl
      have hoff := fun q hq => (widthCellsOff ring ref hn root lane src R hR hsrc hend x hx e hE q hq)
      refine ⟨j, by rw [hs]; exact ⟨hj1, hj2, hjc⟩, fun q hq1 hq2 => ?_, L, ?_, hcl⟩
      · rw [(hoff q hq2).2 (by omega)]; exact hops q hq1 hq2
      · rw [(hoff j hj2).2 (by omega)]; exact hL
    · obtain ⟨hk, rfl⟩ := edgeOfSome ring root src R e k hE
      have hs : widthLaneOfState ref.toWidthDigitReference root lane src R
          (widthNxt ring ref x (digitSite ring root (src + k))) =
          cohortEdge R (widthLaneOfState ref.toWidthDigitReference root lane src R x) k := by rw [hls, hE]; rfl
      obtain ⟨r1, r2, r3⟩ := runStep R hR _ j k ⟨hj1, hj2, hjc⟩
      have hjj := hjc j hj1 hj2
      by_cases hkj : k = j
      · subst hkj
        by_cases hk2 : k + 1 < 2 * R
        · right; left
          have hrun := r1 rfl hk2
          have hS1 := (hjc (k + 1) (by omega) hk2).2.2.2 (by omega)
          obtain ⟨u, hu, huo, hut⟩ := widthCarryMove ring ref hn root lane src R hR hsrc hend x hx k
            hj1 hk2 (hjj.1 rfl).1 ((hjc (k + 1) (by omega) hk2).2.1 (by omega)) false hS1 L hL
          refine ⟨k + 1, by rw [hs]; exact hrun, fun q hq1 hq2 => ?_, _, hu, ?_⟩
          · rw [hkeep q (by omega) hq2 (runS _ k ⟨hj1, hj2, hjc⟩ q (by omega) hq2) (by
              rw [hs]; exact runS _ (k + 1) hrun q hq1 hq2)]
            exact hops q (by omega) hq2
          · obtain ⟨hc1, hc2, hc3⟩ := hcl
            refine ⟨hc1, by simp [hc2]; omega, fun i w hw => ?_⟩
            rcases getAppendOne L.uses u i w hw with hw' | ⟨hi, rfl⟩
            · exact hc3 i w hw'
            · refine ⟨?_, by rw [hut]; omega⟩
              rw [huo, hops (k + 1) (by omega) hk2, hi, hc2]
        · right; right
          have hk2' : k + 1 = 2 * R := by omega
          refine ⟨by rw [hs]; exact r2 rfl hk2', ?_⟩
          obtain ⟨U, hU, hUl, hUs, hUt, hUL⟩ := widthCarryTerminal ring ref hn root lane src R hR hsrc
            hend x hx k hk2' (hjj.1 rfl).1
          refine ⟨U, hU, hUl, by rw [hUs, show k = 2 * R - 1 by omega], by rw [hUt]; omega, L,
            by rw [hUL, hL], ?_⟩
          rw [show R = k + 1 - R by omega]
          exact hcl
      · right; left
        have hrun := r3 hkj
        refine ⟨j, by rw [hs]; exact hrun, fun q hq1 hq2 => ?_, L, ?_, hcl⟩
        · rw [hkeep q (by omega) hq2 (runS _ j ⟨hj1, hj2, hjc⟩ q hq1 hq2) (by
            rw [hs]; exact runS _ j hrun q hq1 hq2)]
          exact hops q hq1 hq2
        · by_cases hk1 : k + 1 = j
          · subst hk1
            rw [widthCarryKeepY ring ref hn root lane src R hR hsrc hend x hx k hk (by
              by_cases hkR : k + 1 = R
              · exact Or.inl hkR
              · exact Or.inr ⟨by omega, (hjc k (by omega) (by omega)).2.1 (by omega)⟩)]
            exact hL
          · rw [widthCellsFar ring ref hn root lane src R hend x k hk j hj2 (Ne.symm hkj) (Ne.symm hk1)]
            exact hL
  · exact absurd hd hnd

/-- **The finish phase reaches its terminal with the ledger**, with the bound of
`finishMomentCoupled`. Consumer: the aligned completion. -/
theorem widthFinishCarryMoment (hR : 2 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n) (N : Nat)
    (hN : n < N) (t0 : Nat) (op : Nat → Option (DigitAtom n))
    (x : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (h : WidthFinInv ring ref root lane src R t0 op x)
    (hg : AGroup R (widthLaneOfState ref.toWidthDigitReference root lane src R x)) :
    MomentBoundQ (widthDigitAuditNext (ref.toWidthDigitReference))
      (fun y => ADone R (widthLaneOfState ref.toWidthDigitReference root lane src R y) ∧
        WidthFinInv ring ref root lane src R t0 op y) N
      (N ^ (R + 1)) ((N - n) ^ (R + 1)) x :=
  momentKeepUntil _ _ _ N _ _
    (fun y e hy hnd => widthFinInvStep ring ref hn root lane src R hR hsrc hend t0 op y e hy hnd) x h
    (widthFinishMoment ref.toWidthDigitReference ref.singletonFixed hn root lane src R hsrc hend N hN hR x h.1 hg)

/-- **Start of the finish phase**: the aligned group with its own atoms and clock. Consumer:
`widthFinishCarryMoment`. -/
theorem widthFinInvStart
    (x : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (hx : WidthCohortLayout ref.toWidthDigitReference root src R x.1)
    (hg : AGroup R (widthLaneOfState ref.toWidthDigitReference root lane src R x)) :
    WidthFinInv ring ref root lane src R x.2.clock
      (fun j => (laneCells ring root lane src x.2.current (R + j)).input) x :=
  ⟨hx, Nat.le_refl _, Or.inl ⟨hg, fun _ _ => rfl⟩⟩

/-- **At the end of the finish phase the terminal is recorded with the ledger.** Consumer: the
aligned completion. -/
theorem widthFinishTerminal (hR : 1 ≤ R) (t0 : Nat) (op : Nat → Option (DigitAtom n))
    (y : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (hd : ADone R (widthLaneOfState ref.toWidthDigitReference root lane src R y))
    (h : WidthFinInv ring ref root lane src R t0 op y) :
    WidthTermDone ring ref root lane src R t0 op y := by
  rcases h.2.2 with ⟨hg, _⟩ | ⟨j, hj, _⟩ | ⟨_, ht⟩
  · exact absurd hd (groupNotDone R hR _ hg)
  · exact absurd hd (runNotDone R j _ hj)
  · exact ht

end Ported

/-- **Port check**: at the BANK boundary reference the generic finish with its ledger is
`L3.PacketMomentCarry.finishCarryMoment`. Consumer: none in the chain; it checks the port. -/
theorem bankFinishCarryMomentCheck {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) (root : Fin n) (lane : DigitLane)
    (src R : Nat) (hR : 2 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n) (N : Nat)
    (hN : n < N) (t0 : Nat) (op : Nat → Option (DigitAtom n))
    (x : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (h : FinInv ring hbank root lane src R t0 op x)
    (hg : AGroup R (laneOfState ring hbank root lane src R x)) :
    MomentBoundQ (widthDigitAuditNext (bankWidthDigitReference ring hn hbank))
      (fun y => ADone R (laneOfState ring hbank root lane src R y) ∧
        FinInv ring hbank root lane src R t0 op y) N
      (N ^ (R + 1)) ((N - n) ^ (R + 1)) x :=
  widthFinishCarryMoment ring (bankWidthBoundaryReference ring hn hbank) hn root lane src R hR hsrc
    hend N hN t0 op x h hg

end L3.WidthPacketMomentCarry

#print axioms L3.WidthPacketMomentCarry.widthCarryKeepY
#print axioms L3.WidthPacketMomentCarry.widthCarryLaunch
#print axioms L3.WidthPacketMomentCarry.widthCarryMove
#print axioms L3.WidthPacketMomentCarry.widthCarryTerminal
#print axioms L3.WidthPacketMomentCarry.widthSettledAtomKeep
#print axioms L3.WidthPacketMomentCarry.widthFinInvStep
#print axioms L3.WidthPacketMomentCarry.widthFinishCarryMoment
#print axioms L3.WidthPacketMomentCarry.widthFinInvStart
#print axioms L3.WidthPacketMomentCarry.widthFinishTerminal
#print axioms L3.WidthPacketMomentCarry.bankFinishCarryMomentCheck
