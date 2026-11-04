import Leader.L3.Bank.RepairDigitBoundaryClean
import Leader.L3.Bank.RepairDigitBlockEntry
import Leader.L3.Small.FinishClean

/-!
# The R10c digit wave on an abstract reference

The R10c digit cuts read a reference state only through

* its physical configuration (`piD`, `piW` of it),
* the successor, which on the drained class moves the D and W projections by the physical
  `phiD`, `phiW` step,
* the clean start at which the digit audit is (re)started,
* the drained class (grant drain on BANK, the grant-free guard on SMALL), closed and
  FIRE-free,
* the fixed native singleton root, closed under the successor.

`WidthDigitReference` packages exactly these.  The start field is the CLEAN start
(BANK: `BankPostInheritedGrantDrain ∧ BankCleanRFold`; SMALL: `SmallCleanRFoldOnGuard`); the
old `BankRepairRFoldEstablished` start is unreachable from the clean entrance
(BankRepairDigitBoundaryClean) and is not used.

Instances: `bankWidthDigitReference` (masked BANK reference, `bankRepairNext`) and
`smallWidthDigitReference` (`renewalSmallNext`, `SmallRepairGuard`).
-/

namespace L3.WidthDigit

open L3
open L3.HeadlineRenewal
open L3.RenewalReferenceClock
open L3.SmallFinishRepair
open L3.SmallRepairStages
open L3.SmallCandidatePreparation
open L3.SmallFinishClean

set_option autoImplicit false

/-- An abstract reference for the R10c digit wave.  Consumer: every generic cut of
WidthDigitCuts and the generic clean core of WidthDigitCleanCore. -/
structure WidthDigitReference {n : Nat} (ring : DirectedRing n) where
  /-- The reference state. -/
  State : Type
  /-- Its physical configuration. -/
  phys : State → HeadlineConfiguration n
  /-- The reference successor. -/
  next : State → Fin n → State
  /-- The clean start at which the digit audit is started. -/
  start : State → Prop
  /-- The drained class. -/
  drained : State → Prop
  /-- The drained class with a fixed native singleton root. -/
  singleton : Fin n → State → Prop
  startDrained : ∀ z, start z → drained z
  drainedClosed : ∀ z, drained z → ∀ e : Fin n, drained (next z e)
  drainedNoFire : ∀ z, drained z → ∀ e : Fin n,
    oldFire (phys z e) (phys z (ring.rightNeighbor e)) = none
  digitStep : ∀ z, drained z → ∀ e : Fin n,
    piD (phys (next z e)) = phiD ring (piD (phys z)) e
  wordStep : ∀ z, drained z → ∀ e : Fin n,
    piW (phys (next z e)) = phiW ring (piW (phys z)) e
  singletonDrained : ∀ root z, singleton root z → drained z
  singletonClosed : ∀ root z, singleton root z → ∀ e : Fin n,
    singleton root (next z e)

/-! ### BANK -/

/-- The masked BANK reference with the clean start.  Consumer: the BANK identities of
WidthDigitCuts and `bankWidthDigitCausalCore` (WidthDigitCleanCore). -/
def bankWidthDigitReference {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) :
    WidthDigitReference ring where
  State := BankReferenceState ring hbank
  phys := fun z => z.val.1
  next := bankRepairNext ring hbank
  start := fun z => BankPostInheritedGrantDrain ring hbank z ∧ BankCleanRFold ring hbank z
  drained := BankPostInheritedGrantDrain ring hbank
  singleton := BankPostInheritedSingleton ring hbank
  startDrained := fun _ h => h.1
  drainedClosed := bankPostInheritedGrantDrainClosed ring hn hbank
  drainedNoFire := fun z hz e => bankRepairCloseNoFireOfDrain ring hbank z hz e
  digitStep := fun z hz e => bankRepairDigitMaskedProjectionOfNoFire ring hbank z e
    (bankRepairCloseNoFireOfDrain ring hbank z hz e)
  wordStep := fun z hz e => bankRepairDigitWordProjectionOfNoFire ring hbank z e
    (bankRepairCloseNoFireOfDrain ring hbank z hz e)
  singletonDrained := fun _ _ h => h.1
  singletonClosed := fun root => bankPostInheritedSingletonClosed ring hn hbank root

/-! ### SMALL -/

/-- The SMALL reference `renewalSmallNext` with the clean start `SmallCleanRFoldOnGuard` and
the guard `SmallRepairGuard`.  Consumer: `smallCleanDigitHalfOfWidthCore`
(WidthDigitCleanCore). -/
def smallWidthDigitReference {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hsmall : (compileAdvice (ceilLogTwo n)).useSmall = true) :
    WidthDigitReference ring where
  State := RenewalSmallReference n
  phys := fun r => r.1
  next := renewalSmallNext ring
  start := SmallCleanRFoldOnGuard ring
  drained := SmallRepairGuard ring
  singleton := SmallCandidateSingletonAtRoot ring
  startDrained := fun _ h => h.1
  drainedClosed := fun r hr e => smallRepairGuardStep ring hn hsmall r hr e
  drainedNoFire := fun r hr e => smallRepairOldNoFire ring r hr e
  digitStep := fun r hr e => smallRepairDigitPhiStep ring (by omega) r hr e
  wordStep := fun r hr e => smallRepairWordPhiStep ring (by omega) r hr e
  singletonDrained := fun _ _ h => h.1
  singletonClosed := fun root r h e =>
    smallCandidateSingletonAtRootClosed ring hn hsmall root r h e

end L3.WidthDigit
