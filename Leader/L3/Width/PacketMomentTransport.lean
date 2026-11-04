import Leader.L3.Width.WaveCore
import Leader.L3.Bank.RepairDigitPacketMomentRelease

/-!
# Lemma e-packet at a digit reference: transport of the lane moments

The e-packet moment chain (`Leader/L3/BankRepairDigitPacketMoment*.lean`) proves every phase on
the T22 lane (`L3.CohortDomination.cohortLaneStep`, rows of the digit layer `phiD`) and carries
it to the coupled chain `widthDigitAuditNext (bankWidthDigitReference ring hn hbank)` through one
BANK fact, `L3.DigitPacketTransport.laneStep` (= `L3.CohortSites.cohortBankStep`: on the layout
class the masked projection moves by the lane step of the drawn pair edge). Its generic form is
`L3.WidthWave.widthCohortStep`, at every digit reference whose singleton class fixes the word root
(`hfix`, the `singletonFixed` field of a `WidthBoundaryReference`; SMALL:
`(smallWidthBoundaryReference ring hn hs).singletonFixed`).

This module restates the transport layer at an arbitrary `WidthDigitReference`:

* `widthLaneOfState`, `widthLaneStep`: the lane of one pair of a coupled state, and its step;
* `widthLaneCost`: the first-hit cost transport (generic `laneCost`);
* `widthLaneTransfer`: a lane moment bound `E[z^T] ≤ w^p` on any lane chain that projects to the
  lane step gives the coupled bound `w^B` for `p ≤ B` (the common tail of every `…Coupled`
  theorem of the chain);
* `bankLaneStepCheck`: the BANK instance is `L3.DigitPacketTransport.laneStep`.
-/

namespace L3.WidthPacketMoment

set_option autoImplicit false

open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree
open L3
open L3.PairMoment
open L3.PacketMoment
open L3.RenewalReferenceClock
open L3.CohortDomination
open L3.CohortSites
open L3.WidthDigit
open L3.DigitPacketRelease
open L3.PacketMomentRelease
open L3.WidthWave
open L3.CohortTransfer

/-- **The lane of one pair of a coupled state** at a digit reference (generic
`L3.DigitPacketTransport.laneOfState`). Consumer: `widthLaneStep`, `widthLaneTransfer`, the
phases of `L3.WidthPacketMoment` (WidthPacketMomentPhases). -/
def widthLaneOfState {n : Nat} {ring : DirectedRing n} (ref : WidthDigitReference ring)
    (root : Fin n) (lane : DigitLane) (src R : Nat)
    (x : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n) : CohortLane :=
  cohortProj ring root lane src R (piD (ref.phys x.1))

/-- **One coupled letter at a digit reference**: the layout class is closed and the lane moves by
the pair edge (generic `L3.DigitPacketTransport.laneStep`, from `widthCohortStep`). Consumer:
`widthLaneCost`, `widthLaneTransfer`, the step lemmas of WidthPacketMomentPhases. -/
theorem widthLaneStep {n : Nat} {ring : DirectedRing n} (ref : WidthDigitReference ring)
    (hfix : ∀ (root : Fin n) (z : ref.State), ref.singleton root z →
      WFixedRoot ring root (piW (ref.phys z))) (hn : 5 ≤ n)
    (root : Fin n) (lane : DigitLane) (src R : Nat) (hR : 2 ≤ R) (hsrc : 2 ≤ src)
    (hend : src + 2 * R < n)
    (x : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (hx : WidthCohortLayout ref root src R x.1) (e : Fin n) :
    WidthCohortLayout ref root src R (widthDigitAuditNext ref x e).1 ∧
      widthLaneOfState ref root lane src R (widthDigitAuditNext ref x e) =
        cohortLaneStep R (widthLaneOfState ref root lane src R x) (cohortEdgeOf root src R e) :=
  widthCohortStep ref hfix hn root lane src R hR hsrc hend x.1 hx e

/-- **Transport of a lane clock** at a digit reference (generic
`L3.DigitPacketTransport.laneCost`). Consumer: the first-moment phases at the band reference
(release clock, `WidthStrictPairClock`). -/
theorem widthLaneCost {n : Nat} {ring : DirectedRing n} (ref : WidthDigitReference ring)
    (hfix : ∀ (root : Fin n) (z : ref.State), ref.singleton root z →
      WFixedRoot ring root (piW (ref.phys z))) (hn : 5 ≤ n)
    (root : Fin n) (lane : DigitLane) (src R : Nat) (hR : 2 ≤ R) (hsrc : 2 ≤ src)
    (hend : src + 2 * R < n) (Good : CohortLane → Prop)
    (x : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (hx : WidthCohortLayout ref root src R x.1) (T : Nat) :
    costNumerator (widthDigitAuditNext ref)
        (fun y => Good (widthLaneOfState ref root lane src R y)) x T ≤
      costNumerator (releaseNext R (cohortEdgeOf root src R)) Good
        (widthLaneOfState ref root lane src R x) T :=
  costNumeratorSimLe (widthDigitAuditNext ref) (releaseNext R (cohortEdgeOf root src R))
    (fun y s => WidthCohortLayout ref root src R y.1 ∧ widthLaneOfState ref root lane src R y = s)
    (fun y => Good (widthLaneOfState ref root lane src R y)) Good
    (fun y s e hys _ => by
      obtain ⟨hl, hs⟩ := hys
      obtain ⟨h1, h2⟩ := widthLaneStep ref hfix hn root lane src R hR hsrc hend y hl e
      refine ⟨h1, ?_⟩
      rw [h2, hs]
      rfl)
    (fun y s hys hg => by
      rw [hys.2]
      exact hg) T x _ ⟨hx, rfl⟩

/-- **Transport of a lane moment** at a digit reference. On any lane chain `next'` whose
projection `pr` moves by the lane step, a bound `E[z^T] ≤ w^p` (`w = N/(N-n)`) for a target read
on the projection gives the coupled bound `w^B` for every `B ≥ p`, uniformly over the reference
state and the audit. Consumer: every moment phase of WidthPacketMomentPhases. -/
theorem widthLaneTransfer {n : Nat} {ring : DirectedRing n} (ref : WidthDigitReference ring)
    (hfix : ∀ (root : Fin n) (z : ref.State), ref.singleton root z →
      WFixedRoot ring root (piW (ref.phys z))) (hn : 5 ≤ n)
    (root : Fin n) (lane : DigitLane) (src R : Nat) (hR : 2 ≤ R) (hsrc : 2 ≤ src)
    (hend : src + 2 * R < n) {X : Type} (next' : X → Fin n → X) (pr : X → CohortLane)
    (hpr : ∀ z e, pr (next' z e) = cohortLaneStep R (pr z) (cohortEdgeOf root src R e))
    (G : CohortLane → Prop) (N p B : Nat) (hN : n < N) (hpB : p ≤ B)
    (x : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (hx : WidthCohortLayout ref root src R x.1) (z : X)
    (hz : pr z = widthLaneOfState ref root lane src R x)
    (h : MomentBoundQ next' (fun z => G (pr z)) N (N ^ p) ((N - n) ^ p) z) :
    MomentBoundQ (widthDigitAuditNext ref) (fun y => G (widthLaneOfState ref root lane src R y))
      N (N ^ B) ((N - n) ^ B) x := by
  have hco := momentSimQ (widthDigitAuditNext ref) next'
    (fun y z => WidthCohortLayout ref root src R y.1 ∧
      widthLaneOfState ref root lane src R y = pr z)
    (fun y => G (widthLaneOfState ref root lane src R y)) (fun z => G (pr z)) N _ _
    (fun y z e hyz _ => by
      obtain ⟨hl, hs⟩ := hyz
      obtain ⟨h1, h2⟩ := widthLaneStep ref hfix hn root lane src R hR hsrc hend y hl e
      refine ⟨h1, ?_⟩
      rw [h2, hs, hpr])
    (fun y z hyz hg => by rw [hyz.2]; exact hg) x z ⟨hx, hz.symm⟩ h
  refine momentQCross _ _ N _ _ _ _ x (Nat.pow_pos (by omega)) ?_ hco
  exact powCross N n _ _ hpB

/-- The transport on the lane chain itself (`pr = id`). Consumer: the phases of
WidthPacketMomentPhases on `releaseNext`. -/
theorem widthLaneMoment {n : Nat} {ring : DirectedRing n} (ref : WidthDigitReference ring)
    (hfix : ∀ (root : Fin n) (z : ref.State), ref.singleton root z →
      WFixedRoot ring root (piW (ref.phys z))) (hn : 5 ≤ n)
    (root : Fin n) (lane : DigitLane) (src R : Nat) (hR : 2 ≤ R) (hsrc : 2 ≤ src)
    (hend : src + 2 * R < n) (G : CohortLane → Prop) (N p B : Nat) (hN : n < N) (hpB : p ≤ B)
    (x : ref.State × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (hx : WidthCohortLayout ref root src R x.1)
    (h : MomentBoundQ (releaseNext R (cohortEdgeOf root src R)) G N (N ^ p) ((N - n) ^ p)
      (widthLaneOfState ref root lane src R x)) :
    MomentBoundQ (widthDigitAuditNext ref) (fun y => G (widthLaneOfState ref root lane src R y))
      N (N ^ B) ((N - n) ^ B) x :=
  widthLaneTransfer ref hfix hn root lane src R hR hsrc hend
    (releaseNext R (cohortEdgeOf root src R)) id (fun _ _ => rfl) G N p B hN hpB x hx _ rfl h

/-- **Port check**: at the BANK reference (`hfix` from the BANK singleton class) the generic step
is `L3.DigitPacketTransport.laneStep`. Consumer: none in the chain; it checks the port. -/
theorem bankLaneStepCheck {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) (root : Fin n) (lane : DigitLane)
    (src R : Nat) (hR : 2 ≤ R) (hsrc : 2 ≤ src) (hend : src + 2 * R < n)
    (x : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (hx : CohortLayout ring hbank root src R x.1) (e : Fin n) :
    CohortLayout ring hbank root src R
        (widthDigitAuditNext (bankWidthDigitReference ring hn hbank) x e).1 ∧
      L3.DigitPacketTransport.laneOfState ring hbank root lane src R
          (widthDigitAuditNext (bankWidthDigitReference ring hn hbank) x e) =
        cohortLaneStep R (L3.DigitPacketTransport.laneOfState ring hbank root lane src R x)
          (cohortEdgeOf root src R e) :=
  widthLaneStep (bankWidthDigitReference ring hn hbank) (fun _ _ h => h.2) hn root lane src R
    hR hsrc hend x hx e

end L3.WidthPacketMoment

#print axioms L3.WidthPacketMoment.widthLaneStep
#print axioms L3.WidthPacketMoment.widthLaneCost
#print axioms L3.WidthPacketMoment.widthLaneTransfer
#print axioms L3.WidthPacketMoment.widthLaneMoment
#print axioms L3.WidthPacketMoment.bankLaneStepCheck
