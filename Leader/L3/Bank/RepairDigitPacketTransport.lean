import Leader.L3.Bank.RepairDigitPacketOrder
import Leader.L3.Width.DigitCuts

/-!
# Lemma e-packet: transport of the lane clocks to the coupled BANK x audit chain

The phases of Lemma e-packet are proved on the T22 lane (`L3.CohortDomination.cohortLaneStep`):
`L3.DigitPacketRelease.releaseClock`, `L3.DigitPacketOrder.orderStep`. On the layout class
`CohortLayout` the masked projection `cohortProj` of a BANK state moves by exactly that lane step
(`L3.CohortSites.cohortBankStep`), and the coupled chain `widthDigitAuditNext` of the BANK width
reference moves its BANK component by `bankRepairNext`. So every lane-level first-hit cost bounds
the coupled cost of the projected target (`laneCost`, a simulation, no re-proof), the release
clock holds on the coupled chain (`releaseCoupled`), and the packet-order invariant is carried
along every coupled word (`orderCoupled`, `orderCoupledWord`). The audit component is untouched
by these statements; ghost-level phases add their clauses on top of the same projection.
-/

namespace L3.DigitPacketTransport

set_option autoImplicit false

open L3
open L3.RenewalReferenceClock
open L3.CohortDomination
open L3.CohortSites
open L3.CohortTransfer
open L3.WidthDigit
open L3.DigitPacketRelease
open L3.DigitPacketOrder
open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree

variable {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
  (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)

/-- The lane of one pair of a coupled state. Consumer: `laneCost`, `releaseCoupled`,
`orderCoupled`. -/
def laneOfState (root : Fin n) (lane : DigitLane) (src R : Nat)
    (x : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n) :
    CohortLane :=
  cohortProj ring root lane src R (piD x.1.val.1)

/-- One coupled letter: the layout class is closed and the lane moves by the pair edge.
Consumer: `laneCost`, `orderCoupled`. -/
theorem laneStep (root : Fin n) (lane : DigitLane) (src R : Nat) (hR : 2 ≤ R) (hsrc : 2 ≤ src)
    (hend : src + 2 * R < n)
    (x : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (hx : CohortLayout ring hbank root src R x.1) (e : Fin n) :
    CohortLayout ring hbank root src R (widthDigitAuditNext (bankWidthDigitReference ring hn hbank) x e).1 ∧
      laneOfState ring hbank root lane src R
          (widthDigitAuditNext (bankWidthDigitReference ring hn hbank) x e) =
        cohortLaneStep R (laneOfState ring hbank root lane src R x) (cohortEdgeOf root src R e) :=
  cohortBankStep ring hn hbank root lane src R hR hsrc hend x.1 hx e

/-- **Transport of a lane clock.** For every lane target, the coupled first-hit cost of the
projected target is at most the lane first-hit cost from the projected state. Consumer:
`releaseCoupled` and every later phase of Lemma e-packet. -/
theorem laneCost (root : Fin n) (lane : DigitLane) (src R : Nat) (hR : 2 ≤ R) (hsrc : 2 ≤ src)
    (hend : src + 2 * R < n) (Good : CohortLane → Prop)
    (x : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (hx : CohortLayout ring hbank root src R x.1) (T : Nat) :
    costNumerator (widthDigitAuditNext (bankWidthDigitReference ring hn hbank))
        (fun y => Good (laneOfState ring hbank root lane src R y)) x T ≤
      costNumerator (releaseNext R (cohortEdgeOf root src R)) Good
        (laneOfState ring hbank root lane src R x) T :=
  costNumeratorSimLe (widthDigitAuditNext (bankWidthDigitReference ring hn hbank))
    (releaseNext R (cohortEdgeOf root src R))
    (fun y s => CohortLayout ring hbank root src R y.1 ∧ laneOfState ring hbank root lane src R y = s)
    (fun y => Good (laneOfState ring hbank root lane src R y)) Good
    (fun y s e hys _ => by
      obtain ⟨hl, hs⟩ := hys
      obtain ⟨h1, h2⟩ := laneStep ring hn hbank root lane src R hR hsrc hend y hl e
      refine ⟨h1, ?_⟩
      rw [h2, hs]
      rfl)
    (fun y s hys hg => by
      rw [hys.2]
      exact hg) T x _ ⟨hx, rfl⟩

/-- **The release phase on the coupled chain.** From every coupled state of the layout class,
the border of the pair's target is free at charge `n R (2R+2)`. Consumer: the distinguished-tail
phase `F` of Lemma e-packet (`WidthStrictPairClock`). -/
theorem releaseCoupled (root : Fin n) (lane : DigitLane) (src R : Nat) (hR : 2 ≤ R)
    (hsrc : 2 ≤ src) (hend : src + 2 * R < n)
    (x : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (hx : CohortLayout ring hbank root src R x.1) (T : Nat) :
    costNumerator (widthDigitAuditNext (bankWidthDigitReference ring hn hbank))
        (fun y => BorderFree R (laneOfState ring hbank root lane src R y)) x T ≤
      n ^ T * (n * (R * (2 * R + 2))) :=
  Nat.le_trans (laneCost ring hn hbank root lane src R hR hsrc hend (BorderFree R) x hx T)
    (releaseClock hR (fun k => digitSite ring root (src + k)) (cohortEdgeOf root src R)
      (fun k hk => cohortEdgeOfSite ring root src R hend k hk) _ T)

/-- **The packet-order invariant along one coupled letter.** Consumer: `orderCoupledWord`. -/
theorem orderCoupled (root : Fin n) (lane : DigitLane) (src R : Nat) (hR : 2 ≤ R)
    (hsrc : 2 ≤ src) (hend : src + 2 * R < n)
    (x : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n)
    (hx : CohortLayout ring hbank root src R x.1)
    (ho : PacketOrder R (laneOfState ring hbank root lane src R x)) (e : Fin n) :
    CohortLayout ring hbank root src R (widthDigitAuditNext (bankWidthDigitReference ring hn hbank) x e).1 ∧
      PacketOrder R (laneOfState ring hbank root lane src R
        (widthDigitAuditNext (bankWidthDigitReference ring hn hbank) x e)) := by
  obtain ⟨h1, h2⟩ := laneStep ring hn hbank root lane src R hR hsrc hend x hx e
  refine ⟨h1, ?_⟩
  rw [h2]
  obtain ⟨m, hm⟩ := ho
  cases cohortEdgeOf root src R e with
  | none => exact ⟨m, hm⟩
  | some k => exact orderStep R m k _ hR hm

/-- **The packet-order invariant along every coupled word.** Consumer: the settled-empty and
renewal-trial phases of Lemma e-packet on the coupled chain. -/
theorem orderCoupledWord (root : Fin n) (lane : DigitLane) (src R : Nat) (hR : 2 ≤ R)
    (hsrc : 2 ≤ src) (hend : src + 2 * R < n) :
    ∀ (w : List (Fin n))
      (x : BankReferenceState ring hbank × DigitAudit (compileAdvice (ceilLogTwo n)) n),
      CohortLayout ring hbank root src R x.1 →
      PacketOrder R (laneOfState ring hbank root lane src R x) →
      CohortLayout ring hbank root src R
          (w.foldl (widthDigitAuditNext (bankWidthDigitReference ring hn hbank)) x).1 ∧
        PacketOrder R (laneOfState ring hbank root lane src R
          (w.foldl (widthDigitAuditNext (bankWidthDigitReference ring hn hbank)) x)) := by
  intro w
  induction w with
  | nil => intro x hx ho; exact ⟨hx, ho⟩
  | cons e w ih =>
    intro x hx ho
    obtain ⟨h1, h2⟩ := orderCoupled ring hn hbank root lane src R hR hsrc hend x hx ho e
    exact ih _ h1 h2

end L3.DigitPacketTransport

#print axioms L3.DigitPacketTransport.laneStep
#print axioms L3.DigitPacketTransport.laneCost
#print axioms L3.DigitPacketTransport.releaseCoupled
#print axioms L3.DigitPacketTransport.orderCoupled
#print axioms L3.DigitPacketTransport.orderCoupledWord
