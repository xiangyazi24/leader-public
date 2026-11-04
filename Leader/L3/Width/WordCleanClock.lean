import Leader.L3.Width.WordCleanTransport
import Leader.L3.Small.FinishRepair

/-!
# Width W clean clock, part 6: the SMALL clock with no width premise

`smallWordCleanWordClockOfSmall`: on every SMALL ring with 5 ≤ n, from
every SMALL reference state at the prepared cut, the projected W chain
reaches the clean-word entrance target `BankWordCleanWordTarget` within
(440t + 275)n², t = `smallRepairWidth n`.  This is the width layer
(WidthWordClean*) instantiated at the SMALL start; it covers the whole
SMALL band, including 9 ≤ ceilLogTwo n ≤ 16 where t = 3 and ψ = 4, and
replaces the earlier t = ψ port (SmallWordClean*, retired).  The budget is the natural t-form: five width
blocks, 5 · 11(8t + 5)n² = (440t + 275)n² (`widthWordRenewalFiveCoefficient`).
-/

namespace L3.RenewalReferenceClock

open Classical
open L3.HeadlineRenewal
open L3.SmallRenewal
open L3.SmallCandidatePreparation
open L3.SmallFinishRepair
open L3.ReferencePreparationTrail
open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree

set_option autoImplicit false
set_option Elab.async false

/-- The SMALL W first-hit clock to the clean-word entrance target, with
the (440t + 275)n² budget of `SmallWordProjectedClock`, from every SMALL
reference state at the prepared cut.  Consumer: the SMALL clean finish
composition (the clean-target analogue of
`smallRepairWordStageOfProjectedClock`), then the headline with
G := Gclean (CleanTargetClosure). -/
def SmallWordCleanWordClock {n : Nat}
    (ring : DirectedRing n) : Prop :=
  ∀ r : RenewalSmallReference n,
    SmallPreparedAtSomeRoot ring r →
    ∀ T : Nat,
      costNumerator (phiW ring)
        (BankWordCleanWordTarget ring) (piW r.1) T ≤
      n ^ T * ((440 * smallRepairWidth n + 275) * n ^ 2)

/-- The SMALL prepared cut gives the width start class: the native root
of `SmallCandidateSingletonAtRoot` is the W fixed root of `piW r.1`.
Consumer: `smallWordCleanWordClockOfSmall`. -/
theorem widthWordPreparedSerializerRoot {n : Nat}
    (ring : DirectedRing n)
    (hsmallFive : 5 ≤ n)
    (r : RenewalSmallReference n)
    (hr : SmallPreparedAtSomeRoot ring r) :
    ∃ root : Fin n,
      WidthWordSerializerRootClass ring hsmallFive root (piW r.1) := by
  obtain ⟨root, hfixed, _⟩ := hr
  refine ⟨root, ?_⟩
  have hroot : Rooted ring root (smallReferenceNativeView r) := hfixed.2
  change WFixedRoot ring root (piW r.1)
  exact hroot

/-- The SMALL clean W clock at 5 ≤ n on SMALL, with no width premise:
the argument of `bankWordCleanWordClockOfTransport` on the width layer,
with the transport discharged by the width row transport.  Consumer: the
SMALL clean finish composition, then the headline with G := Gclean. -/
theorem smallWordCleanWordClockOfSmall {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hsmall : (compileAdvice (ceilLogTwo n)).useSmall = true) :
    SmallWordCleanWordClock ring := by
  intro r hr T
  have htrans := widthGeneratedControlTransportOfRows ring hn hn
    (widthWordRowTransport ring hn hn)
  obtain ⟨root, hs⟩ := widthWordPreparedSerializerRoot ring hn r hr
  have hcompletionCost := widthWordEpochCompletionFiveCostHolds
    ring hn hn root (piW r.1) hs T
  have hmono := costNumerator_target_mono_on
    (bankWordEpochNext ring root)
    (BankWordEpochReachable ring root (piW r.1))
    BankWordRenewalCompleted
    (fun q : BankWordEpochState n =>
      BankWordCleanWordTarget ring q.2.1)
    (fun q hq e =>
      bankWordEpochReachableNext
        ring root (piW r.1) q hq e)
    (fun q hq hcomplete =>
      widthWordCompletionCleanWordTarget ring hn hn htrans root
        (piW r.1) hs q hq hcomplete)
    T (bankWordEpochStart (piW r.1)) ⟨[], rfl⟩
  have hmap := costNumerator_map_eq
    (bankWordEpochNext ring root)
    (phiW ring)
    (fun q : BankWordEpochState n => q.2.1)
    (by intro q e; exact bankWordEpochPhysicalNext ring root q e)
    (BankWordCleanWordTarget ring)
    T (bankWordEpochStart (piW r.1))
  rw [hmap] at hmono
  exact Nat.le_trans hmono hcompletionCost

end L3.RenewalReferenceClock

#print axioms L3.RenewalReferenceClock.widthWordPreparedSerializerRoot
#print axioms L3.RenewalReferenceClock.smallWordCleanWordClockOfSmall
