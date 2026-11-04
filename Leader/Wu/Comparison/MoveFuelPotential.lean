import Leader.Wu.Comparison.MoveFuelRepair

/-!
# Global potential carried by non-refreshing comparison fuel

The transport-fuel repair is best understood as a finite global reservoir, not
as an authenticated path lineage.  This file proves the exact local potential
law: every full interaction weakly decreases the sum of endpoint fuel, and a
positive physical SIGMOVE transfer decreases it strictly.  It also proves that
all-zero fuel is closed.

These facts expose the liveness tradeoff under arbitrary initialization.  The
current transition has no fuel source, so an all-zero start can never execute a
positive-fuel comparison transfer.  Any future birth grant must be modeled as a
new potential-creation event and bounded separately.
-/

namespace PPLLMoveFuelPotential

open PPLL PPLLRepair PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
  PPLLMoveFuelComparisonRepair

attribute [local irreducible]
  authorizedPPsi authorizedGenSig authorizedCleanSig authorizedEliminateSig
  authorizedCheckSig authorizedDisappear authorizedCompareSig authorizedReconcile
  suppressSig eliminateLeadersNoCollision writeSeq

/-- Sum of the two physical endpoint fuel values. -/
def pairMoveFuel (l r : MoveFuelAuthorizedAgentState ψ μ) : Nat :=
  l.moveFuel.val + r.moveFuel.val

/-- A generic `keepFuel` wrapper preserves endpoint fuel sum exactly. -/
theorem keepFuel_pairMoveFuel
    (f : AuthorizedAgentState ψ → AuthorizedAgentState ψ →
      AuthorizedAgentState ψ × AuthorizedAgentState ψ)
    (l r : MoveFuelAuthorizedAgentState ψ μ) :
    let q := keepFuel f l r
    pairMoveFuel q.1 q.2 = pairMoveFuel l r := by
  rfl

/-- Fuel-aware SIGMOVE never increases the local pair reservoir. -/
theorem moveFuelAuthorizedSigMove_pair_le
    (hψ : ψ > 0) (l r : MoveFuelAuthorizedAgentState ψ μ) :
    let q := moveFuelAuthorizedSigMove hψ l r
    pairMoveFuel q.1 q.2 ≤ pairMoveFuel l r := by
  unfold moveFuelAuthorizedSigMove
  dsimp only
  split
  · split
    · simp [pairMoveFuel, zeroMoveFuel]
    · simp [pairMoveFuel, zeroMoveFuel, decMoveFuel]
      omega
  · simp [pairMoveFuel]

/-- A detected positive path transfer strictly decreases endpoint fuel sum,
regardless of the receiver's overwritten host fuel. -/
theorem moveFuelAuthorizedSigMove_pair_lt_of_positive
    (hψ : ψ > 0) (l r : MoveFuelAuthorizedAgentState ψ μ)
    (hmoved :
      let q := authorizedSigMove hψ l.core r.core
      pathMovedRight l.core.core r.core.core q.1.core q.2.core = true)
    (hpos : 0 < l.moveFuel.val) :
    let q := moveFuelAuthorizedSigMove hψ l r
    pairMoveFuel q.1 q.2 < pairMoveFuel l r := by
  have hq := moveFuelSigMove_positive_transfer hψ l r hmoved hpos
  dsimp only at hq ⊢
  unfold pairMoveFuel
  omega

/-- Every stage before specialized SIGMOVE preserves both input fuel values. -/
theorem moveFuelBeforeSigMove_fuels
    (hψ : ψ > 0) (κ : Nat)
    (l r : MoveFuelAuthorizedAgentState ψ μ) :
    let q := moveFuelBeforeSigMove hψ κ l r
    q.1.moveFuel = l.moveFuel ∧ q.2.moveFuel = r.moveFuel := by
  unfold moveFuelBeforeSigMove
  simp [keepFuel]

/-- The full repair has exactly the fuel sum produced by its specialized
SIGMOVE prefix; every suffix stage is fuel-framed. -/
theorem moveFuelAuthorizedRepair_pair_eq_beforeCheck
    (hψ : ψ > 0) (κ : Nat)
    (l r : MoveFuelAuthorizedAgentState ψ μ) :
    let q0 := moveFuelBeforeCheck hψ κ l r
    let q := moveFuelAuthorizedRepair hψ κ l r
    pairMoveFuel q.1 q.2 = pairMoveFuel q0.1 q0.2 := by
  unfold moveFuelAuthorizedRepair
  simp [keepFuel, pairMoveFuel]

/-- Every complete interaction weakly decreases the endpoint fuel reservoir. -/
theorem moveFuelAuthorizedRepair_pair_le
    (hψ : ψ > 0) (κ : Nat)
    (l r : MoveFuelAuthorizedAgentState ψ μ) :
    let q := moveFuelAuthorizedRepair hψ κ l r
    pairMoveFuel q.1 q.2 ≤ pairMoveFuel l r := by
  let pre := moveFuelBeforeSigMove hψ κ l r
  have hpre := moveFuelBeforeSigMove_fuels hψ κ l r
  have hsig := moveFuelAuthorizedSigMove_pair_le hψ pre.1 pre.2
  have hfull := moveFuelAuthorizedRepair_pair_eq_beforeCheck hψ κ l r
  change pairMoveFuel
      (moveFuelAuthorizedRepair hψ κ l r).1
      (moveFuelAuthorizedRepair hψ κ l r).2 ≤ pairMoveFuel l r
  rw [hfull]
  change pairMoveFuel
      (moveFuelAuthorizedSigMove hψ pre.1 pre.2).1
      (moveFuelAuthorizedSigMove hψ pre.1 pre.2).2 ≤ pairMoveFuel l r
  exact Nat.le_trans hsig (by
    unfold pairMoveFuel
    rw [hpre.1, hpre.2]
    exact Nat.le_refl _)

/-- Zero fuel is closed under the complete interaction at both endpoints. -/
theorem moveFuelAuthorizedRepair_zero_closed
    (hψ : ψ > 0) (κ : Nat)
    (l r : MoveFuelAuthorizedAgentState ψ μ)
    (hl : l.moveFuel.val = 0) (hr : r.moveFuel.val = 0) :
    let q := moveFuelAuthorizedRepair hψ κ l r
    q.1.moveFuel.val = 0 ∧ q.2.moveFuel.val = 0 := by
  have hle := moveFuelAuthorizedRepair_pair_le hψ κ l r
  dsimp only at hle ⊢
  unfold pairMoveFuel at hle
  omega

/-- Every agent in a configuration has zero transport fuel. -/
def AllMoveFuelZero
    (C : Fin n → MoveFuelAuthorizedAgentState ψ μ) : Prop :=
  ∀ i, (C i).moveFuel.val = 0

/-- One complete local interaction preserves an all-zero fuel configuration. -/
theorem allMoveFuelZero_localStep
    (hψ : ψ > 0) (κ : Nat) (ring : DirectedRing n)
    (C : Fin n → MoveFuelAuthorizedAgentState ψ μ)
    (hC : AllMoveFuelZero C) (e : Fin n) :
    AllMoveFuelZero
      (PPLLResearchFormulation.localStep ring
        (moveFuelAuthorizedRepair hψ κ) C e) := by
  let j := ring.rightNeighbor e
  let q := moveFuelAuthorizedRepair hψ κ (C e) (C j)
  have hq := moveFuelAuthorizedRepair_zero_closed hψ κ
    (C e) (C j) (hC e) (hC j)
  intro i
  change (if i = e then q.1 else if i = j then q.2 else C i).moveFuel.val = 0
  by_cases hie : i = e
  · simpa [hie] using hq.1
  · by_cases hij : i = j
    · subst i
      simpa [hie, q] using hq.2
    · simpa [hie, hij] using hC i

/-- Every finite scheduler word preserves the all-zero fuel vector. -/
theorem allMoveFuelZero_runLocalSchedule
    (hψ : ψ > 0) (κ : Nat) (ring : DirectedRing n)
    (C : Fin n → MoveFuelAuthorizedAgentState ψ μ)
    (hC : AllMoveFuelZero C) (s : DetSchedule n) :
    AllMoveFuelZero
      (PPLLResearchFormulation.runLocalSchedule ring
        (moveFuelAuthorizedRepair hψ κ) C s) := by
  induction s generalizing C with
  | nil => exact hC
  | cons e rest ih =>
      exact ih _ (allMoveFuelZero_localStep hψ κ ring C hC e)

end PPLLMoveFuelPotential
