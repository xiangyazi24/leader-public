import Leader.L3.Width.PacketMomentLoop

/-!
# Lemma e-max: the attempt loop of one pair at its own budgets, for every `R ≥ 3`

The attempt loop of one pair (`L3.WidthPacketMoment.attemptLoopBlock`) has three budgets:

* `B_p = uBudget R + 2R + (R+2)(2R+2)`: one attempt from the attempt class (phases U, retirement,
  the renewal trial) to its outcome;
* `B_s = R + 1`: the aligned outcome to its `DigitCompletion`. The receipt is a property of the
  state at the end of the finish phase (`ADone`): the terminal with its clean ledger (I3,
  `L3.WidthPacketMomentCarry.widthFinishTerminal`), the samples (I1, `widthGroupSamples`) and the
  held exports (I2b) are all recorded by then, so no letter is spent after the finish
  (`L3.PacketMomentAfter`, and the R10c worker's `groupDoneMoment`, with the bound
  `w^{R+1}` of the finish);
* `B_a = afterBudget R + (R + 1) = 2R² + 8R + 5`: after the outgoing race edge, the front, the
  cleared window, the aligned trial and the finish.

`successBudgetLe`: `B_s ≤ C_R`. `attemptLoopPair`: the loop at `C = C_R` with these budgets closes at
`E[z^τ] ≤ 6` for every `R ≥ 3` and `N ≥ n (2C_R + 1)`, with every budget condition discharged
(`prepBlockFit`, `finishBlockFit`, `afterBudgetShort`, `pairClockMid`); it covers the SMALL slice
`r = 3` (`C_3 = 442`) that `attemptLoopWide` (`C ≥ 4000`) does not.
-/

namespace L3.WidthPacketMoment

set_option autoImplicit false

open L3.PacketMoment
open L3.PacketMomentU
open L3.PacketMomentV
open L3.PacketMomentAfter
open L3.RenewalReferenceClock

/-- **The success budget fits the pair clock**: `R + 1 ≤ C_R`. Consumer: `attemptLoopPair`. -/
theorem successBudgetLe (R : Nat) : R + 1 ≤ bankRepairDigitPairClock R := by
  unfold bankRepairDigitPairClock
  omega

/-- **The attempt loop of one pair at its own budgets, for every `R ≥ 3`.** One attempt from `A`
reaches `Q` within `w^{B_p}`, `B_p = uBudget R + 2R + (R+2)(2R+2)`; at `Q` the target holds, or the
aligned completion follows within `w^{R+1}`, or a race starts whose outgoing letter is followed by
the target within `w^{2R² + 8R + 5}` (`afterBudget R + (R + 1)`) and whose incoming letter returns
to `A`. At `C = C_R` and `N ≥ n (2C_R + 1)`, `E[z^τ] ≤ 6` from every state of `A`. Consumer: the
per-pair moment of Lemma e-max at the band reference (SMALL and BANK), in place of
`L3.PacketMomentWide.attemptLoopWide`. -/
theorem attemptLoopPair {S : Type} {n : Nat} (next : S → Fin n → S) (P A Q : S → Prop)
    (N R : Nat) (hn : 2 ≤ n) (hR : 3 ≤ R)
    (hN : n * (2 * bankRepairDigitPairClock R + 1) ≤ N)
    (hprep : ∀ x, A x → MomentBoundQ next Q N (N ^ (uBudget R + 2 * R + (R + 2) * vK R))
      ((N - n) ^ (uBudget R + 2 * R + (R + 2) * vK R)) x)
    (hQ : ∀ y, Q y → P y ∨ MomentBoundQ next P N (N ^ (R + 1)) ((N - n) ^ (R + 1)) y ∨
      ∃ (Pend : S → Prop) (ea eb : Fin n), Pend y ∧ ea ≠ eb ∧
        (∀ x, Pend x → ¬ P x → ∀ e, e ≠ ea → e ≠ eb → Pend (next x e)) ∧
        (∀ x, Pend x → ¬ P x → MomentBoundQ next P N (N ^ (afterBudget R + (R + 1)))
          ((N - n) ^ (afterBudget R + (R + 1))) (next x ea)) ∧
        (∀ x, Pend x → ¬ P x → A (next x eb))) :
    ∀ x, A x → MomentBoundQ next P N (6 * (N - n) ^ bankRepairDigitPairClock R)
      ((N - n) ^ bankRepairDigitPairClock R) x :=
  attemptLoopBlock next P A Q N (bankRepairDigitPairClock R) _ (R + 1) _ hn
    (pairClockMid R (by omega)) hN (successBudgetLe R) (prepBlockFit R hR)
    (finishBlockFit R (by omega)) (afterBudgetShort R hR) hprep hQ

end L3.WidthPacketMoment

#print axioms L3.WidthPacketMoment.successBudgetLe
#print axioms L3.WidthPacketMoment.attemptLoopPair
