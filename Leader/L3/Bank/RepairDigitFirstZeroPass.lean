import Leader.L3.Bank.RepairDigitFirstZero

/-!
# T19: the first-zero stage, pass layer

Abstract projected-ring layer of the first-zero rank. A *pass* is an obligation that rides a
root-launched base token through the first block: it starts at a fresh root launch into site 1,
moves with the token, and on a collision transfers to the token ahead (`DigitBaseLineage`). The
obligation advances by exactly one site whenever the edge at its head site fires, and every
other edge leaves it in place. A ZERO head proposes at its site when it fires, so a pass that
reaches the end of the first block has covered every first-writable site.

`BankRepairDigitZeroData` lists the five phases (pass one pending / running, pass two pending /
running, target), each with a cost; no edge raises the least cost and the edge at the head (or
the launch edge, or the edge clearing site 1) lowers it.
-/

namespace L3.RenewalReferenceClock

open L3.HeadlineRenewal
open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree

set_option autoImplicit false

/-! ### Block layout and ring geometry -/

/-- The delimiter layout: first block `[first, stop)`, `stop = min (first + R) n`. -/
structure BankRepairDigitZeroBlock {c : Compiled} {n : Nat} (ring : DirectedRing n)
    (root : Fin n) (R first stop : Nat) (S : Fin n → ProjD c) : Prop where
  layout : ∀ k, 0 < k → k < n →
    ((S (digitSite ring root k)).word.beta = true ↔ first ≤ k ∧ (k - first) % R = 0)
  firstTwo : 2 ≤ first
  firstStop : first < stop
  stopSize : stop ≤ n
  stopSpan : stop ≤ first + R
  stopEdge : stop < n → stop = first + R

/-- The layout plus the fixed leader and beta-stable rows. -/
structure BankRepairDigitZeroGeom {c : Compiled} {n : Nat} (ring : DirectedRing n)
    (root : Fin n) (R first stop : Nat) (S : Fin n → ProjD c) extends
    BankRepairDigitZeroBlock ring root R first stop S : Prop where
  size : 5 ≤ n
  rootIff : ∀ i, (S i).word.native.l = true ↔ i = root
  betaX : ∀ e, (pairW (S e).word (S (ring.rightNeighbor e)).word).1.beta = (S e).word.beta
  betaY : ∀ e, (pairW (S e).word (S (ring.rightNeighbor e)).word).2.beta =
    (S (ring.rightNeighbor e)).word.beta

theorem bankRepairDigitZeroBetaPre {c : Compiled} {n : Nat} (ring : DirectedRing n)
    (root : Fin n) (R first stop : Nat) (S : Fin n → ProjD c)
    (hb : BankRepairDigitZeroBlock ring root R first stop S) (k : Nat) (h0 : 0 < k)
    (hk : k < first) : (S (digitSite ring root k)).word.beta = false := by
  have := hb.firstStop
  have := hb.stopSize
  cases hbt : (S (digitSite ring root k)).word.beta with
  | false => rfl
  | true =>
      have := ((hb.layout k h0 (by omega)).1 hbt).1
      omega

theorem bankRepairDigitZeroBetaInner {c : Compiled} {n : Nat} (ring : DirectedRing n)
    (root : Fin n) (R first stop : Nat) (S : Fin n → ProjD c)
    (hb : BankRepairDigitZeroBlock ring root R first stop S) (k : Nat) (h0 : first < k)
    (hk : k < stop) : (S (digitSite ring root k)).word.beta = false := by
  have := hb.stopSize
  have := hb.stopSpan
  cases hbt : (S (digitSite ring root k)).word.beta with
  | false => rfl
  | true =>
      have h := ((hb.layout k (by omega) (by omega)).1 hbt).2
      rw [Nat.mod_eq_of_lt (show k - first < R by omega)] at h
      omega

theorem bankRepairDigitZeroBetaFirst {c : Compiled} {n : Nat} (ring : DirectedRing n)
    (root : Fin n) (R first stop : Nat) (S : Fin n → ProjD c)
    (hb : BankRepairDigitZeroBlock ring root R first stop S) :
    (S (digitSite ring root first)).word.beta = true := by
  have := hb.firstTwo
  have := hb.firstStop
  have := hb.stopSize
  exact (hb.layout first (by omega) (by omega)).2
    ⟨Nat.le_refl _, by rw [Nat.sub_self, Nat.zero_mod]⟩

theorem bankRepairDigitZeroBetaStop {c : Compiled} {n : Nat} (ring : DirectedRing n)
    (root : Fin n) (R first stop : Nat) (S : Fin n → ProjD c)
    (hb : BankRepairDigitZeroBlock ring root R first stop S) (h : stop < n) :
    (S (digitSite ring root stop)).word.beta = true := by
  have := hb.firstStop
  exact (hb.layout stop (by omega) h).2
    ⟨by omega, by rw [hb.stopEdge h, Nat.add_sub_cancel_left, Nat.mod_self]⟩

/-- A non-leader destination is not the wrap-around to the leader. -/
theorem bankRepairDigitZeroSuccNonroot {c : Compiled} {n : Nat} (ring : DirectedRing n)
    (root : Fin n) (R first stop : Nat) (S : Fin n → ProjD c)
    (hg : BankRepairDigitZeroGeom ring root R first stop S) (k : Nat) (hk : k < n)
    (hl : (S (ring.rightNeighbor (digitSite ring root k))).word.native.l = false) :
    k + 1 < n := by
  rcases Nat.lt_or_ge (k + 1) n with h | h
  · exact h
  · exfalso
    have hkn : k + 1 = n := by omega
    have hr : ring.rightNeighbor (digitSite ring root k) = root := by
      show digitSite ring root (k + 1) = root
      rw [hkn]
      exact bankRepairDigitSiteN ring root
    rw [hr, (hg.rootIff root).2 rfl] at hl
    cases hl

/-- The newest audit frame. -/
theorem bankRepairDigitZeroHead {c : Compiled} {n : Nat} (ring : DirectedRing n)
    (S : Fin n → ProjD c) (A : DigitAudit c n) (e : Fin n) :
    ∃ f, f ∈ (digitAuditStep ring S A e).frames ∧ f.time = A.clock + 1 ∧ f.edge = e ∧
      f.receipt.base = digitBaseReplay (A.clock + 1) e (ring.rightNeighbor e) (S e)
        (S (ring.rightNeighbor e)) (workerW (S e).word (S (ring.rightNeighbor e)).word).betaY
        (A.current e).base (A.current (ring.rightNeighbor e)).base :=
  ⟨_, List.Mem.head _, rfl, rfl, rfl⟩

/-! ### Token layout -/

/-- Root-launched tokens: SEEK in the leading prefix, ZERO in the first block. -/
def BankRepairDigitZeroLaunchLayout {c : Compiled} {n : Nat} (ring : DirectedRing n)
    (root : Fin n) (first stop : Nat) (S : Fin n → ProjD c) (G : Fin n → DigitGhost c n) :
    Prop :=
  ∀ k, k < n → ∀ born, (G (digitSite ring root k)).base =
      some (.rootLaunch born root (ring.rightNeighbor root)) →
    0 < k ∧ k < stop ∧ (k < first → (S (digitSite ring root k)).top.wBase = .SEEK) ∧
      (first ≤ k → (S (digitSite ring root k)).top.wBase = .ZERO)

/-- After retirement: every token is root-launched and placed by the layout. -/
structure BankRepairDigitZeroToks {c : Compiled} {n : Nat} (ring : DirectedRing n)
    (root : Fin n) (first stop : Nat) (S : Fin n → ProjD c) (G : Fin n → DigitGhost c n) :
    Prop where
  place : ∀ k, k < n → (S (digitSite ring root k)).top.wBase ≠ .NONE →
    0 < k ∧ k < stop ∧ (k < first → (S (digitSite ring root k)).top.wBase = .SEEK) ∧
      (first ≤ k → (S (digitSite ring root k)).top.wBase = .ZERO)
  label : ∀ i, (S i).top.wBase ≠ .NONE → ∃ born, 0 < born ∧
    (G i).base = some (.rootLaunch born root (ring.rightNeighbor root))
  empty : ∀ i, (S i).top.wBase = .NONE → (G i).base = none

theorem bankRepairDigitZeroToksOf {c : Compiled} {n : Nat} (ring : DirectedRing n)
    (root : Fin n) (first stop : Nat) (S : Fin n → ProjD c) (G : Fin n → DigitGhost c n)
    (hsound : ∀ i, BankRepairDigitBaseGhostSound ring root (S i).top.wBase (G i).base)
    (hgone : ∀ i s, (G i).base ≠ some (.inherited s))
    (hL : BankRepairDigitZeroLaunchLayout ring root first stop S G) :
    BankRepairDigitZeroToks ring root first stop S G := by
  have hlab : ∀ i, (S i).top.wBase ≠ .NONE → ∃ born, 0 < born ∧
      (G i).base = some (.rootLaunch born root (ring.rightNeighbor root)) := by
    intro i hw
    rcases hsound i with ⟨h1, _⟩ | ⟨_, ⟨s, hs⟩ | ⟨born, hb, hgb⟩⟩
    · exact absurd h1 hw
    · exact absurd hs (hgone i s)
    · exact ⟨born, hb, hgb⟩
  refine ⟨fun k hk hw => ?_, hlab, fun i hw => ?_⟩
  · obtain ⟨born, _, hb⟩ := hlab _ hw
    exact hL k hk born hb
  · rcases hsound i with ⟨_, h2⟩ | ⟨h1, _⟩
    · exact h2
    · exact absurd hw h1

/-- One edge preserves the launch layout. -/
theorem bankRepairDigitZeroLaunchStep {c : Compiled} {n : Nat} (ring : DirectedRing n)
    (root : Fin n) (R first stop : Nat) (S : Fin n → ProjD c) (G : Fin n → DigitGhost c n)
    (time : Nat) (e : Fin n) (hg : BankRepairDigitZeroGeom ring root R first stop S)
    (hsound : ∀ i, BankRepairDigitBaseGhostSound ring root (S i).top.wBase (G i).base)
    (hL : BankRepairDigitZeroLaunchLayout ring root first stop S G) :
    BankRepairDigitZeroLaunchLayout ring root first stop (phiD ring S e)
      (digitGhostStep ring S G time e) := by
  obtain ⟨j, hj, rfl⟩ := bankRepairDigitSiteSurj ring root e
  have hn := hg.size
  have h2 := hg.firstTwo
  have h3 := hg.firstStop
  have h4 := hg.stopSize
  obtain ⟨_, hwy, hgx, hgy, _, hrest⟩ := bankRepairDigitZeroEdge ring (by omega) S G time
    (digitSite ring root j) (hg.betaX _) (hg.betaY _)
  intro k hk born hb
  by_cases ha : digitSite ring root k = digitSite ring root j
  · exfalso
    rw [ha, hgx] at hb
    rcases bankRepairDigitZeroReplayX time (digitSite ring root j)
        (ring.rightNeighbor (digitSite ring root j)) (S (digitSite ring root j))
        (S (ring.rightNeighbor (digitSite ring root j)))
        (S (ring.rightNeighbor (digitSite ring root j))).word.beta
        (G (digitSite ring root j)).base
        (G (ring.rightNeighbor (digitSite ring root j))).base with h | ⟨hw, h⟩
    · rw [h] at hb
      cases hb
    · rw [h] at hb
      rcases hsound (digitSite ring root j) with ⟨_, h0⟩ | ⟨h1, _⟩
      · rw [h0] at hb
        cases hb
      · exact h1 hw
  · by_cases hb' : digitSite ring root k = ring.rightNeighbor (digitSite ring root j)
    · rw [hb'] at hb ⊢
      rw [hgy] at hb
      rw [hwy]
      rcases bankRepairDigitZeroRowY time (digitSite ring root j)
          (ring.rightNeighbor (digitSite ring root j)) (S (digitSite ring root j))
          (S (ring.rightNeighbor (digitSite ring root j))) (S (digitSite ring root j)).word.beta
          (S (ring.rightNeighbor (digitSite ring root j))).word.beta
          (G (digitSite ring root j)).base
          (G (ring.rightNeighbor (digitSite ring root j))).base with
        ⟨hw, hgg⟩ | ⟨hxl, _, _, hw, _⟩ | ⟨hxl, hyl, hxw, hbY, _, hw, hgg⟩ |
          ⟨hxl, hyl, hxw, _, hw, hgg⟩
      · rw [hgg] at hb
        rw [hw]
        have h := hL k hk born (by rw [hb']; exact hb)
        rw [hb'] at h
        exact h
      · have hjr : digitSite ring root j = root := (hg.rootIff _).1 hxl
        have hj0 : j = 0 :=
          bankRepairDigitSiteInj ring root (k := j) (m := 0) hj (by omega) hjr
        subst hj0
        have hk1 : k = 1 :=
          bankRepairDigitSiteInj ring root (k := k) (m := 1) hk (by omega) hb'
        subst hk1
        exact ⟨by omega, by omega, fun _ => hw, fun h => absurd h (by omega)⟩
      · rw [hgg] at hb
        have hold := hL j hj born hb
        have hjf : first ≤ j := by
          rcases Nat.lt_or_ge j first with h | h
          · rw [hold.2.2.1 h] at hxw
            cases hxw
          · exact h
        have hj1 := bankRepairDigitZeroSuccNonroot ring root R first stop S hg j hj hyl
        have hk1 : k = j + 1 :=
          bankRepairDigitSiteInj ring root (k := k) (m := j + 1) hk hj1 hb'
        subst hk1
        have hjs : j + 1 < stop := by
          rcases Nat.lt_or_ge (j + 1) stop with h | h
          · exact h
          · exfalso
            have hse : j + 1 = stop := by omega
            have hbt := bankRepairDigitZeroBetaStop ring root R first stop S
              hg.toBankRepairDigitZeroBlock (by omega)
            rw [← hse] at hbt
            have hbt' : (S (ring.rightNeighbor (digitSite ring root j))).word.beta = true := hbt
            rw [hbt'] at hbY
            cases hbY
        exact ⟨by omega, hjs, fun h => absurd h (by omega), fun _ => hw⟩
      · rw [hgg] at hb
        have hold := hL j hj born hb
        have hjf : j < first := by
          rcases Nat.lt_or_ge j first with h | h
          · exact h
          · rw [hold.2.2.2 h] at hxw
            cases hxw
        have hj1 := bankRepairDigitZeroSuccNonroot ring root R first stop S hg j hj hyl
        have hk1 : k = j + 1 :=
          bankRepairDigitSiteInj ring root (k := k) (m := j + 1) hk hj1 hb'
        subst hk1
        refine ⟨by omega, by omega, fun h => ?_, fun h => ?_⟩
        · have hbf : (S (ring.rightNeighbor (digitSite ring root j))).word.beta = false :=
            bankRepairDigitZeroBetaPre ring root R first stop S hg.toBankRepairDigitZeroBlock
              (j + 1) (by omega) h
          rw [hw, hbf]
          rfl
        · have hjf' : j + 1 = first := by omega
          have hbt := bankRepairDigitZeroBetaFirst ring root R first stop S
            hg.toBankRepairDigitZeroBlock
          rw [← hjf'] at hbt
          have hbt' : (S (ring.rightNeighbor (digitSite ring root j))).word.beta = true := hbt
          rw [hw, hbt']
          rfl
    · obtain ⟨hS, hG⟩ := hrest _ ha hb'
      rw [hG] at hb
      rw [hS]
      exact hL k hk born hb

end L3.RenewalReferenceClock
