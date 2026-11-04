import Leader.L3.Bank.RepairDigitValueWave
import Leader.L3.Bank.RepairDigitBlockStart

/-!
# T30 item 5: moving charges from a coupled chain to `bankRepairNext`

The cohort costs are proved on coupled chains (`bankRepairDigitBoundaryAuditNext`, BANK × audit;
`windowNext`, BANK × audit × cycle ghost), while the R10c clock runs on `bankRepairNext`.

* `costProjectLe`: for any chain `next'` whose projection `π` commutes with the letters, and a
  coupled target `Q` whose states project into a physical target `P`, the physical first-hit cost
  of `P` from `π x` is at most the coupled first-hit cost of `Q` from `x`.
* `chargedProject`: a charged stage `A → B` of the coupled chain gives a charged stage `P → Q`
  of `bankRepairNext` when every `P` state lifts to an `A` state and `B` projects into `Q`.
* `CoupledBlock`, `chargedOfCoupledBlock`: the per-block clock as consumed by
  `bankRepairDigitValueWaveOfBlockClocks`; `valueWaveOfCoupledBlocks`: the value-wave clock from
  coupled block stages of charge `200 n R` with `K R ≤ n` blocks (`blockFit`).
* `windowCoupledBlock`: T30 item 1's `blockCharge` (on `windowNext`) as a `CoupledBlock`.
* `winInvDReset`: the cycle ghost's arrival counter can be reset to `0` at a block start.
* `windowRunStep`: the coupled run form of `BankRepairDigitValuesStableCut` extends along
  `windowNext`.
-/

namespace L3.Projection

set_option autoImplicit false

open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree
open L3.RenewalReferenceClock
open L3.CohortDomination
open L3.CohortTail
open L3.CohortSites
open L3.CohortEntry
open L3.PacketClass
open L3.CohortStages
open L3.Rearm
open L3.Recording
open L3.GhostBridge
open L3.Correspondence
open L3.CohortIdentity
open L3.CohortWindow
open L3.CohortTransfer
open L3.CohortClose
open L3.BlockStart

/-! ### The generic projection -/

/-- **Projection of first-hit cost**: physical cost from the projection is at most the coupled
cost, when the projection commutes with the letters and the coupled target projects into the
physical one. -/
theorem costProjectLe {S X : Type} {n : Nat} (next : S → Fin n → S) (next' : X → Fin n → X)
    (π : X → S) (hπ : ∀ x e, π (next' x e) = next (π x) e) (P : S → Prop) (Q : X → Prop)
    (hQ : ∀ x, Q x → P (π x)) (x : X) (T : Nat) :
    costNumerator next P (π x) T ≤ costNumerator next' Q x T :=
  costNumeratorSimLe next next' (fun s x => π x = s) P Q
    (fun s x e h _ => by rw [hπ, h]) (fun s x h hq => h ▸ hQ x hq) T (π x) x rfl

/-- **Projection of a charged stage**. -/
theorem chargedProject {S X : Type} {n : Nat} (next : S → Fin n → S) (next' : X → Fin n → X)
    (π : X → S) (hπ : ∀ x e, π (next' x e) = next (π x) e) (A B : X → Prop) (P Q : S → Prop)
    (c : Nat) (hA : ∀ z, P z → ∃ x, π x = z ∧ A x) (hB : ∀ x, B x → Q (π x))
    (h : BankRepairDigitChargedStage next' A B c) : BankRepairDigitChargedStage next P Q c := by
  intro z hz T
  obtain ⟨x, rfl, hx⟩ := hA z hz
  exact Nat.le_trans (Nat.mul_le_mul_left 2 (costProjectLe next next' π hπ Q B hB x T))
    (h x hx T)

/-! ### The coupled chains project to `bankRepairNext` -/

section Chains

variable {n : Nat} (ring : DirectedRing n)
  (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)

theorem auditProject
    (z : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (e : Fin n) :
    (bankRepairDigitBoundaryAuditNext ring hbank z e).1 = bankRepairNext ring hbank z.1 e := rfl

theorem windowProject (root : Fin n) (lane : DigitLane) (src R : Nat)
    (w : (BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n) ×
      ((Nat → Nat) × Nat)) (e : Fin n) :
    (windowNext ring hbank root lane src R w e).1.1 = bankRepairNext ring hbank w.1.1 e := rfl

/-- The coupled run form (as in `BankRepairDigitValuesStableCut`) extends along `windowNext`. -/
theorem windowRunStep (root : Fin n) (lane : DigitLane) (src R : Nat)
    (start : BankReferenceState ring hbank) (word : List (Fin n))
    (w : (BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n) ×
      ((Nat → Nat) × Nat))
    (h : word.foldl (bankRepairDigitBoundaryAuditNext ring hbank)
      (start, digitAuditInitial (piD start.val.1)) = w.1) (e : Fin n) :
    (word ++ [e]).foldl (bankRepairDigitBoundaryAuditNext ring hbank)
      (start, digitAuditInitial (piD start.val.1)) = (windowNext ring hbank root lane src R w e).1 := by
  rw [List.foldl_append, h]
  rfl

/-! ### The per-block clock in the consumed form -/

/-- A block stage `P → Q` of the R10c clock, charged on some coupled chain projecting to
`bankRepairNext`. -/
def CoupledBlock (P Q : BankReferenceState ring hbank → Prop) (c : Nat) : Prop :=
  ∃ (X : Type) (next' : X → Fin n → X) (π : X → BankReferenceState ring hbank)
    (A B : X → Prop),
    (∀ x e, π (next' x e) = bankRepairNext ring hbank (π x) e) ∧
    (∀ z, P z → ∃ x, π x = z ∧ A x) ∧ (∀ x, B x → Q (π x)) ∧
    BankRepairDigitChargedStage next' A B c

theorem chargedOfCoupledBlock (P Q : BankReferenceState ring hbank → Prop) (c : Nat)
    (h : CoupledBlock ring hbank P Q c) :
    BankRepairDigitChargedStage (bankRepairNext ring hbank) P Q c := by
  obtain ⟨X, next', π, A, B, hπ, hA, hB, hc⟩ := h
  exact chargedProject _ next' π hπ A B P Q c hA hB hc

/-- `K` blocks of `200 n R` fit the value-wave charge `200 n^2` when `K R ≤ n`. -/
theorem blockFit {K R : Nat} (hK : K * R ≤ n) :
    K * (200 * n * R) ≤ bankRepairDigitValueWaveMicroCharge n := by
  unfold bankRepairDigitValueWaveMicroCharge
  calc K * (200 * n * R) = 200 * n * (K * R) := by ac_rfl
    _ ≤ 200 * n * n := Nat.mul_le_mul_left _ hK
    _ = 200 * n ^ 2 := by rw [Nat.pow_two, Nat.mul_assoc]

/-- **The value-wave clock from coupled block stages**: block stages `P j → P (j + 1)`, each
charged `200 n R` on a coupled chain, `K R ≤ n` blocks, the first-zero cut inside `P 0` and
`P K` inside the value cut. -/
theorem valueWaveOfCoupledBlocks (P : Nat → BankReferenceState ring hbank → Prop) (K R : Nat)
    (h0 : ∀ z, BankRepairDigitFirstZeroCut ring hbank z → P 0 z)
    (hblock : ∀ j, CoupledBlock ring hbank (P j) (P (j + 1)) (200 * n * R))
    (hlast : ∀ z, P K z → BankRepairDigitValuesStableCut ring hbank z)
    (hK : K * R ≤ n) :
    BankRepairDigitValueWaveClock ring hbank :=
  bankRepairDigitValueWaveOfBlockClocks ring hbank P K (200 * n * R) h0
    (fun j => chargedOfCoupledBlock ring hbank _ _ _ (hblock j)) hlast (blockFit hK)

end Chains

/-! ### The block of item 1 as a coupled block -/

section Window

variable {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
  (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) (root : Fin n) (lane : DigitLane)
  (src R : Nat) (hR : 2 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n)
  (Base : Bool → DigitAtom n → Prop)

/-- The arrival counter of the cycle ghost is free: it can be reset at a block start. -/
theorem winInvDReset
    (z : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (g : (Nat → Nat) × Nat) (h : WinInvD ring hbank root lane src R Base z g) (j : Nat) :
    WinInvD ring hbank root lane src R Base z (g.1, j) := by
  obtain ⟨h1, h2, h3, ⟨o, -, hg, hy, hd⟩, h5⟩ := h
  exact ⟨h1, h2, h3, ⟨o, rfl, hg, hy, hd⟩, h5⟩

include hn hR hsrc hend in
/-- **Item 1's block as the consumed per-block clock**: if every physical block-start state lifts
to a coupled state with the strengthened window invariant, the invariant `Inv` and arrival
counter `0`; `Inv` is carried off `Good`; the old cohort of cycle `5` being gone forces `Good`;
and `Good` projects into the block finish: the block stage costs `≤ 200 n R` doubled on
`bankRepairNext`. -/
theorem windowCoupledBlock
    (P Q : BankReferenceState ring hbank → Prop)
    (Inv Good : (BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n) ×
      ((Nat → Nat) × Nat) → Prop)
    (hinv : ∀ w e, WinInvD ring hbank root lane src R Base w.1 w.2 → Inv w → ¬ Good w →
      Inv (windowNext ring hbank root lane src R w e))
    (hgood : ∀ w, WinInvD ring hbank root lane src R Base w.1 w.2 → Inv w →
      (CohortLayout ring hbank root src R w.1.1 ∧
        CohortCycOld R 5 (2 * R + 1) (cohortProj ring root lane src R (piD w.1.1.val.1)) w.2) →
      Good w)
    (hA : ∀ z, P z → ∃ w : (BankReferenceState ring hbank ×
        DigitAudit (compileAdvice (ceilLogTwo n)) n) × ((Nat → Nat) × Nat),
      w.1.1 = z ∧ (WinInvD ring hbank root lane src R Base w.1 w.2 ∧ Inv w ∧ w.2.2 = 0))
    (hB : ∀ w, Good w → Q w.1.1) :
    CoupledBlock ring hbank P Q (200 * n * R) :=
  ⟨_, windowNext ring hbank root lane src R, fun w => w.1.1,
    fun w => WinInvD ring hbank root lane src R Base w.1 w.2 ∧ Inv w ∧ w.2.2 = 0, Good,
    fun _ _ => rfl, hA, hB,
    fun w hw T => blockCharge ring hn hbank root lane src R hR hsrc hend Base Inv Good hinv 0
      hgood w hw.1 hw.2.1 hw.2.2 T⟩

end Window

end L3.Projection

#print axioms L3.Projection.costProjectLe
#print axioms L3.Projection.chargedProject
#print axioms L3.Projection.chargedOfCoupledBlock
#print axioms L3.Projection.blockFit
#print axioms L3.Projection.valueWaveOfCoupledBlocks
#print axioms L3.Projection.windowRunStep
#print axioms L3.Projection.winInvDReset
#print axioms L3.Projection.windowCoupledBlock
