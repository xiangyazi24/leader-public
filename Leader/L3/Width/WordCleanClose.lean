import Leader.L3.Width.WordCleanFrontier

/-!
# Width W clean clock, part 3: lineage and soft-lap closure

Ported BankWordRenewalClose and BankWordRenewalSoftClose declarations.
Every declaration is the width port of the BANK declaration named in its
docstring (via SmallWordClean*): band premise `5 ≤ n`, start class
`WidthWordSerializerRootClass` (the fixed physical root), renewal
constants in the compiled width t; see WidthWordCleanBand.
-/

namespace L3.RenewalReferenceClock

open Classical

set_option autoImplicit false
set_option Elab.async false

section
open Classical
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

/-- Width port of `bankWordRootStartCountNextLapCost`: the BANK band premise is replaced by `5 ≤ n`, and the renewal constants are those of the compiled width t (lease 8t+4, quota 2t+1). Consumer: `widthWordEpochGenuineCostOfLapCount`.
 From any reachable state the next root S1 costs at most n(5n-4):
the restart clock transferred to the counter.  Consumer: one lap. -/
theorem widthWordRootStartCountNextLapCost {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hsmallFive : 5 ≤ n)
    (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hs : WidthWordSerializerRootClass ring hsmallFive root s)
    (y : BankWordEpochState n)
    (hy : BankWordEpochReachable ring root s y) (T : Nat) :
    costNumerator (bankWordEpochNext ring root)
      (fun w => bankWordRootStartCount root y <
        bankWordRootStartCount root w) y T ≤
      n ^ T * (n * (5 * n - 4)) := by
  rw [bankWordRootStartCountRestartCostEq ring root
    (bankWordRootStartCount root y) T y rfl]
  exact widthWordEpochRestartSOneCost ring hn hsmallFive root s hs y hy T

end

section
open Classical
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

/-- Width port of `bankWordEpochGenuineCostOfLapCount`: the BANK band premise is replaced by `5 ≤ n`, and the renewal constants are those of the compiled width t (lease 8t+4, quota 2t+1). Consumer: `widthWordEpochPostSOneWorkerClockOfLapCount`, `widthWordRenewalFreshAttemptCostOfLineageStep`.
 Chain of at most `L+2` laps, each paid by the restart clock.
Consumer: `widthWordEpochPostSOneWorkerClockOfLapCount`. -/
theorem widthWordEpochGenuineCostOfLapCount {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hsmallFive : 5 ≤ n)
    (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hs : WidthWordSerializerRootClass ring hsmallFive root s)
    (hlap : WidthWordEpochLapCount ring root s)
    (z₀ : BankWordEpochState n)
    (hz₀ : BankWordEpochReachable ring root s z₀)
    (hstop : BankWordEpochSOneReached z₀) (T : Nat) :
    costNumerator (bankWordEpochNext ring root)
      (fun y => (bankWordHardEpochLedger ring root z₀).hardEpochs <
        (bankWordHardEpochLedger ring root y).hardEpochs) z₀ T ≤
      n ^ T * ((widthWordRenewalLease n + 2) * (n * (5 * n - 4))) := by
  have hD : ∀ x, BankWordEpochReachableFrom ring root z₀ x → ∀ e,
      BankWordEpochReachableFrom ring root z₀
        (bankWordEpochNext ring root x e) :=
    fun x hx e => bankWordEpochReachableFromNext ring root z₀ x hx e
  have hchain : ∀ j : Nat, ∀ y : BankWordEpochState n,
      BankWordEpochReachableFrom ring root z₀ y →
      bankWordRootStartCount root z₀ + (widthWordRenewalLease n + 2) ≤
        bankWordRootStartCount root y + j →
      ∀ U : Nat,
        costNumerator (bankWordEpochNext ring root)
          (fun w => (bankWordHardEpochLedger ring root z₀).hardEpochs <
            (bankWordHardEpochLedger ring root w).hardEpochs) y U ≤
        n ^ U * (j * (n * (5 * n - 4))) := by
    intro j
    induction j with
    | zero =>
        intro y hy hcount U
        have hA := hlap z₀ hz₀ hstop y hy (by simpa using hcount)
        rw [costNumerator_terminal (bankWordEpochNext ring root) _ y hA U]
        exact Nat.zero_le _
    | succ j ih =>
        intro y hy hcount U
        by_cases hA : (bankWordHardEpochLedger ring root z₀).hardEpochs <
            (bankWordHardEpochLedger ring root y).hardEpochs
        · rw [costNumerator_terminal (bankWordEpochNext ring root) _ y hA U]
          exact Nat.zero_le _
        · have hstage := costNumerator_stage_le_on
            (bankWordEpochNext ring root)
            (BankWordEpochReachableFrom ring root z₀)
            (fun w => bankWordRootStartCount root y <
              bankWordRootStartCount root w)
            (fun w => (bankWordHardEpochLedger ring root z₀).hardEpochs <
              (bankWordHardEpochLedger ring root w).hardEpochs)
            hD y hy (n * (5 * n - 4)) (j * (n * (5 * n - 4)))
            (fun V => by
              calc
                costNumerator (bankWordEpochNext ring root)
                    (fun w => bankWordRootStartCount root y <
                        bankWordRootStartCount root w ∨
                      (bankWordHardEpochLedger ring root z₀).hardEpochs <
                        (bankWordHardEpochLedger ring root w).hardEpochs)
                    y V ≤
                  costNumerator (bankWordEpochNext ring root)
                    (fun w => bankWordRootStartCount root y <
                      bankWordRootStartCount root w) y V :=
                  costNumerator_target_mono_on
                    (bankWordEpochNext ring root)
                    (BankWordEpochReachableFrom ring root z₀) _ _ hD
                    (fun w _ hw => Or.inl hw) V y hy
                _ ≤ n ^ V * (n * (5 * n - 4)) :=
                  widthWordRootStartCountNextLapCost ring hn hsmallFive root s hs
                    y (bankWordEpochReachableOfFrom ring root s z₀ y hz₀ hy)
                    V)
            (fun w hw hcw V => ih w hw (by omega) V)
          have hmul : n * (5 * n - 4) + j * (n * (5 * n - 4)) =
              (j + 1) * (n * (5 * n - 4)) := by
            rw [Nat.add_mul, Nat.one_mul, Nat.add_comm]
          rw [← hmul]
          exact hstage U
  exact hchain (widthWordRenewalLease n + 2) z₀
    (bankWordEpochReachableFromSelf ring root z₀) (Nat.le_refl _) T

end

section
open Classical
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

/-- Width port of `bankWordEpochPostSOneWorkerClockOfLapCount`: the BANK band premise is replaced by `5 ≤ n`, and the renewal constants are those of the compiled width t (lease 8t+4, quota 2t+1). Consumer: `widthWordEpochPostSOneWorkerClockOfLineageStep`.
 The consumer's W-stage clock from the lap count: the first ghost
launch is no later than the first genuine acceptance (entrance lemma),
which costs at most `(L+2) n(5n-4)` by the lap chain.
Consumer: `widthWordProjectedOneEpochCostOfWorkerClock`. -/
theorem widthWordEpochPostSOneWorkerClockOfLapCount {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hsmallFive : 5 ≤ n)
    (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hs : WidthWordSerializerRootClass ring hsmallFive root s)
    (hlap : WidthWordEpochLapCount ring root s) :
    WidthWordEpochPostSOneWorkerClock ring root s := by
  intro z₀ hz₀ hstop T
  have hD : ∀ x, BankWordEpochReachableFrom ring root z₀ x → ∀ e,
      BankWordEpochReachableFrom ring root z₀
        (bankWordEpochNext ring root x e) :=
    fun x hx e => bankWordEpochReachableFromNext ring root z₀ x hx e
  have hentr : ∀ x, BankWordEpochReachableFrom ring root z₀ x →
      ¬ ((bankWordHardEpochLedger ring root z₀).hardEpochs <
        (bankWordHardEpochLedger ring root x).hardEpochs) →
      ∀ e, (bankWordHardEpochLedger ring root z₀).hardEpochs <
        (bankWordHardEpochLedger ring root
          (bankWordEpochNext ring root x e)).hardEpochs →
      BankWordEpochWorkerLaunched (bankWordEpochNext ring root x e) := by
    intro x hx hnot e hnext
    have hx' := bankWordEpochReachableOfFrom ring root s z₀ x hz₀ hx
    have hinc : (bankWordHardEpochLedger ring root x).hardEpochs <
        (bankWordHardEpochLedger ring root
          (bankWordEpochNext ring root x e)).hardEpochs := by
      omega
    exact bankWordEpochLaunchedOfGenuine ring root s x hx' e
      (bankWordHardEpochGenuineOfCountIncrease ring root x e hinc)
  calc
    costNumerator (bankWordEpochNext ring root)
        BankWordEpochWorkerLaunched z₀ T ≤
      costNumerator (bankWordEpochNext ring root)
        (fun y => (bankWordHardEpochLedger ring root z₀).hardEpochs <
          (bankWordHardEpochLedger ring root y).hardEpochs) z₀ T :=
      costNumerator_entrance_le_on (bankWordEpochNext ring root)
        (BankWordEpochReachableFrom ring root z₀) _ _ hD hentr T z₀
        (bankWordEpochReachableFromSelf ring root z₀)
        (Nat.lt_irrefl _)
    _ ≤ n ^ T * ((widthWordRenewalLease n + 2) * (n * (5 * n - 4))) :=
      widthWordEpochGenuineCostOfLapCount ring hn hsmallFive root s hs hlap
        z₀ hz₀ hstop T
    _ ≤ n ^ T * (6 * n ^ 2 +
        (8 * (compileAdvice (ceilLogTwo n)).t + 5) * (5 * n ^ 2 + 2 * n)) := by
      have hL : 8 * (compileAdvice (ceilLogTwo n)).t + 5 =
          widthWordRenewalLease n + 1 := by
        unfold widthWordRenewalLease
        omega
      rw [hL]
      exact Nat.mul_le_mul_left _
        (bankWordEpochLapBudgetArithmetic n (widthWordRenewalLease n))

end

section
open Classical
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

/-- Width port of `bankWordEpochFixedRoot`: the BANK band premise is replaced by `5 ≤ n`, and the renewal constants are those of the compiled width t (lease 8t+4, quota 2t+1). Consumer: `widthGeneratedControlTransportOfRows`, `widthWordCompletionCleanWordTarget`, `widthWordCompletionFutureWave`. -/
theorem widthWordEpochFixedRoot {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hsmallFive : 5 ≤ n)
    (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hs : WidthWordSerializerRootClass ring hsmallFive root s)
    (z : BankWordEpochState n)
    (hz : BankWordEpochReachable ring root s z) :
    WFixedRoot ring root z.2.1 :=
  (widthWordSerializerRootClassClosed ring hn hsmallFive root).1 _
    (widthWordEpochReachablePhysicalRootClass ring hn hsmallFive root s hs z hz)

end

section
open Classical
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

/-- Width port of `bankWordEpochFixedRootNext`: the BANK band premise is replaced by `5 ≤ n`, and the renewal constants are those of the compiled width t (lease 8t+4, quota 2t+1). Consumer: `widthWordCompletionFutureWave`, `widthWordEpochLapInvariantStep`, `widthWordEpochPostLatchRootFactsStep`. -/
theorem widthWordEpochFixedRootNext {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hsmallFive : 5 ≤ n)
    (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hs : WidthWordSerializerRootClass ring hsmallFive root s)
    (z : BankWordEpochState n)
    (hz : BankWordEpochReachable ring root s z) (e : Fin n) :
    WFixedRoot ring root (phiW ring z.2.1 e) := by
  have h := widthWordEpochFixedRoot ring hn hsmallFive root s hs
    (bankWordEpochNext ring root z e)
    (bankWordEpochReachableNext ring root s z hz e)
  rw [bankWordEpochPhysicalNext] at h
  exact h

end

section
open Classical
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

/-- Width port of `bankWordEpochPostLatchRootFactsStep`: the BANK band premise is replaced by `5 ≤ n`, and the renewal constants are those of the compiled width t (lease 8t+4, quota 2t+1). Consumer: `widthWordEpochPostLatchRootFactsReachable`. -/
theorem widthWordEpochPostLatchRootFactsStep {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hsmallFive : 5 ≤ n)
    (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hs : WidthWordSerializerRootClass ring hsmallFive root s)
    (z : BankWordEpochState n)
    (hz : BankWordEpochReachable ring root s z) (e : Fin n)
    (hF : BankWordEpochPostLatchRootFacts root z) :
    BankWordEpochPostLatchRootFacts root (bankWordEpochNext ring root z e) := by
  intro hstop'
  have hn2 : 2 ≤ n := by omega
  have hfixed := widthWordEpochFixedRootNext ring hn hsmallFive root s hs z hz e
  have hrunB := widthWordEpochSOneRunningBReachable ring root hn hsmallFive s hs z hz
  by_cases hstop : BankWordEpochSOneReached z
  · obtain ⟨hW, hSix⟩ := hF hstop
    rcases clockPostTrichotomy ring root z.2.1 e hn2 hfixed with
      ⟨he, hpx, hpy⟩ | ⟨hj, hpx, hpy⟩ | ⟨hne, hnj, hpx, hpy⟩
    · subst e
      rw [bankWordEpochRootOutgoingRecord, pairW_ser_left]
      cases hc : (z.2.1 root).ser.cert with
      | IDLE =>
          obtain ⟨_, hcert, _, _⟩ :=
            bankWordRootOutgoingIdleRows _ _ hpx hpy hc
          rw [hcert]
          exact ⟨(fun h => by cases h),
            fun _ => bankWordEpochEverSixNext ring root z root (hSix (Or.inl hc))⟩
      | REQUESTED =>
          obtain ⟨_, hcert, _, _, hzero, hpos⟩ :=
            bankWordRootOutgoingStartRows _ _ hpx hpy hc
          rw [hcert]
          refine ⟨fun _ => ?_, (fun h => by rcases h with h | h <;> cases h)⟩
          by_cases hl : (z.2.1 root).siLease.val = 0
          · exact Or.inr (hzero hl)
          · exact Or.inl (hpos (Nat.pos_of_ne_zero hl))
      | RUNNING =>
          have hb : (z.2.1 root).ser.phase = .B := hrunB.2 hstop hc
          by_cases hG : (z.2.1 root).ser.out = .DONE ∧
              (z.2.1 (ring.rightNeighbor root)).ser.phase = .F
          · obtain ⟨hrow, hcert, _, _⟩ :=
              bankWordRootOutgoingFinishRows _ _ hpx hpy hc hb hG.1 hG.2
            rw [hcert]
            exact ⟨(fun h => by cases h),
              fun _ => bankWordEpochEverSixOfRow ring root z root rfl hrow⟩
          · obtain ⟨_, hcert, _, hw, _, _⟩ :=
              bankWordRootOutgoingRunningFrameRows _ _ hpx hpy hc hb hG
            rw [hcert, hw]
            exact ⟨fun _ => hW hc, (fun h => by rcases h with h | h <;> cases h)⟩
    · have hne : root ≠ e := by
        rw [← hj]
        exact clockNeighborDifferent ring hn2 e
      rw [hj] at hpx hpy
      rw [bankWordEpochRootIncomingRecord ring root z e hj hne, pairW_ser_right]
      obtain ⟨_, hidle, hkeep⟩ := bankWordRootIncomingRows (z.2.1 e) (z.2.1 root) hpx hpy
      by_cases hc : (z.2.1 root).ser.cert = .IDLE
      · rw [hidle hc]
        exact ⟨(fun h => by cases h),
          fun _ => bankWordEpochEverSixNext ring root z e (hSix (Or.inl hc))⟩
      · rw [hkeep hc]
        exact ⟨hW, fun h => bankWordEpochEverSixNext ring root z e (hSix h)⟩
    · rw [bankWordHardEpochRootRemoteFrame ring root z e (Ne.symm hne) (Ne.symm hnj)]
      exact ⟨hW, fun h => bankWordEpochEverSixNext ring root z e (hSix h)⟩
  · -- the latch edge itself: the synchronized active observer stops at a root S1
    have hnode : ∃ w, z.1 = .active w := by
      cases hz1 : z.1 with
      | stopped =>
          exact absurd (show BankWordEpochSOneReached z by
            change clockSerializerIsStopped z.1
            rw [hz1]
            exact True.intro) hstop
      | active w => exact ⟨w, rfl⟩
    obtain ⟨w, hw⟩ := hnode
    have hweq : w = z.2.1 := hrunB.1 w hw
    have hserv : clockSerializerSOneService ring root z.2.1 e := by
      have h := hstop'
      change clockSerializerIsStopped
        (clockSerializerSOneOnlyNext ring root z.1 e) at h
      rw [hw, hweq] at h
      exact (clockSerializerSOneOnlyStopIff ring root z.2.1 e).mp h
    obtain ⟨he, hrow⟩ := hserv
    subst e
    have hpost := clockPostOutgoing ring root z.2.1 root hn2 hfixed rfl
    have hreq : (z.2.1 root).ser.cert = .REQUESTED :=
      ((clockSerializerSOneIffRequested ring root z.2.1 hn2 hfixed root).mp
        (And.intro rfl hrow)).2
    obtain ⟨_, hcert, _, _, hzero, hpos⟩ :=
      bankWordRootOutgoingStartRows _ _ hpost.1 hpost.2 hreq
    rw [bankWordEpochRootOutgoingRecord, pairW_ser_left, hcert]
    refine ⟨fun _ => ?_, (fun h => by rcases h with h | h <;> cases h)⟩
    by_cases hl : (z.2.1 root).siLease.val = 0
    · exact Or.inr (hzero hl)
    · exact Or.inl (hpos (Nat.pos_of_ne_zero hl))

end

section
open Classical
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

/-- Width port of `bankWordEpochPostLatchRootFactsReachable`: the BANK band premise is replaced by `5 ≤ n`, and the renewal constants are those of the compiled width t (lease 8t+4, quota 2t+1). Consumer: `widthWordEpochLapCountOfLineageStep`, `widthWordEpochLapInvariantStep`. -/
theorem widthWordEpochPostLatchRootFactsReachable {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hsmallFive : 5 ≤ n)
    (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hs : WidthWordSerializerRootClass ring hsmallFive root s)
    (z : BankWordEpochState n)
    (hz : BankWordEpochReachable ring root s z) :
    BankWordEpochPostLatchRootFacts root z := by
  obtain ⟨word, hword⟩ := hz
  rw [← hword]
  have key : ∀ (w : List (Fin n)) (a : BankWordEpochState n),
      BankWordEpochReachable ring root s a →
      BankWordEpochPostLatchRootFacts root a →
      BankWordEpochPostLatchRootFacts root (bankWordEpochRun ring root a w) := by
    intro w
    induction w with
    | nil => intro a _ h; exact h
    | cons e rest ih =>
        intro a ha h
        exact ih _ (bankWordEpochReachableNext ring root s a ha e)
          (widthWordEpochPostLatchRootFactsStep ring hn hsmallFive root s hs a ha e h)
  exact key word (bankWordEpochStart s) ⟨[], rfl⟩ ((fun h => by cases h))

end

section
open Classical
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

/-- Width port of `bankWordRenewalLineageQuietOfEverSix`: the BANK band premise is replaced by `5 ≤ n`, and the renewal constants are those of the compiled width t (lease 8t+4, quota 2t+1). Consumer: `widthWordEpochLapInvariantStep`.
 Once a root S6 has been observed, the J-W lineage holds at every
later reachable state: vacuous right after the S6 (root IDLE), then
carried by the lineage step.  Consumer: genuineness of the hard S6
that ends a post-S6 hard wave. -/
theorem widthWordRenewalLineageQuietOfEverSix {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hsmallFive : 5 ≤ n)
    (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hs : WidthWordSerializerRootClass ring hsmallFive root s)
    (hstep : BankWordRenewalLineageQuietStep ring root s)
    (z : BankWordEpochState n)
    (hz : BankWordEpochReachable ring root s z)
    (hsix : BankWordEpochEverSix root z) :
    BankWordRenewalFrontierWaveLineageQuiet ring root z := by
  have hn2 : 2 ≤ n := by omega
  obtain ⟨word, hword⟩ := hz
  rw [← hword] at hsix ⊢
  have key : ∀ (w : List (Fin n)) (a : BankWordEpochState n),
      BankWordEpochReachable ring root s a →
      (BankWordEpochEverSix root a →
        BankWordRenewalFrontierWaveLineageQuiet ring root a) →
      (BankWordEpochEverSix root (bankWordEpochRun ring root a w) →
        BankWordRenewalFrontierWaveLineageQuiet ring root
          (bankWordEpochRun ring root a w)) := by
    intro w
    induction w with
    | nil => intro a _ h; exact h
    | cons e rest ih =>
        intro a ha h
        apply ih (bankWordEpochNext ring root a e)
          (bankWordEpochReachableNext ring root s a ha e)
        intro hsix'
        rcases bankWordEpochEverSixNextCases ring root a e hsix' with hold | ⟨he, hrow⟩
        · exact hstep a ha (h hold) e
        · subst e
          have hfixed := widthWordEpochFixedRootNext ring hn hsmallFive root s hs a ha root
          have hpost := clockPostOutgoing ring root a.2.1 root hn2 hfixed rfl
          have hidle : ((bankWordEpochNext ring root a root).2.1 root).ser.cert = .IDLE := by
            rw [bankWordEpochRootOutgoingRecord, pairW_ser_left]
            exact bankWordRootOutgoingSixIdle _ _ hpost.1 hpost.2 hrow
          exact bankWordRenewalLineageQuietOfIdle ring root _ hidle
  refine key word (bankWordEpochStart s) ⟨[], rfl⟩ ?_ hsix
  intro h
  obtain ⟨r, hr, _, _⟩ := h
  simp [bankWordEpochStart, wOriginInitial] at hr

end

section
open Classical
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

/-- Width port of `bankWordEpochLapInvariantStep`: the BANK band premise is replaced by `5 ≤ n`, and the renewal constants are those of the compiled width t (lease 8t+4, quota 2t+1). Consumer: `widthWordEpochLapInvariantFrom`. -/
theorem widthWordEpochLapInvariantStep {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hsmallFive : 5 ≤ n)
    (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hs : WidthWordSerializerRootClass ring hsmallFive root s)
    (hstep : BankWordRenewalLineageQuietStep ring root s)
    (z₀ : BankWordEpochState n)
    (hz₀ : BankWordEpochReachable ring root s z₀)
    (hstop : BankWordEpochSOneReached z₀)
    (y : BankWordEpochState n)
    (hy : BankWordEpochReachableFrom ring root z₀ y) (e : Fin n)
    (hinv : BankWordEpochLapInvariant ring root z₀ y) :
    BankWordEpochLapInvariant ring root z₀ (bankWordEpochNext ring root y e) := by
  intro hE'
  have hn2 : 2 ≤ n := by omega
  have hyR : BankWordEpochReachable ring root s y :=
    bankWordEpochReachableOfFrom ring root s z₀ y hz₀ hy
  have hEy : (bankWordHardEpochLedger ring root y).hardEpochs =
      (bankWordHardEpochLedger ring root z₀).hardEpochs := by
    have h1 := bankWordHardEpochCountMono ring root y e
    have h2 := bankWordHardEpochCountFrom ring root z₀ y hy
    omega
  obtain ⟨hI, hC, hV⟩ := hinv hEy
  have hstopy : BankWordEpochSOneReached y :=
    bankWordEpochSOneReachedFrom ring root z₀ y hy hstop
  obtain ⟨hW, hSix⟩ :=
    widthWordEpochPostLatchRootFactsReachable ring hn hsmallFive root s hs y hyR hstopy
  have hrunB := (widthWordEpochSOneRunningBReachable ring root hn hsmallFive s hs y hyR).2 hstopy
  have hfixed := widthWordEpochFixedRootNext ring hn hsmallFive root s hs y hyR e
  have hcnt := bankWordRootStartCountNext ring root y e
  rcases clockPostTrichotomy ring root y.2.1 e hn2 hfixed with
    ⟨he, hpx, hpy⟩ | ⟨hj, hpx, hpy⟩ | ⟨hne, hnj, hpx, hpy⟩
  · subst e
    rw [bankWordEpochRootOutgoingRecord, pairW_ser_left,
      bankWordRootOutgoingLease _ _ hpy, hcnt]
    cases hc : (y.2.1 root).ser.cert with
    | IDLE =>
        obtain ⟨hrowne, hcert, hha, hsa⟩ :=
          bankWordRootOutgoingIdleRows _ _ hpx hpy hc
        have hno : ¬ clockSerializerSOneService ring root y.2.1 root :=
          fun h => hrowne h.2
        rw [hcert, hha, hsa, bankWordHardEpochSourceLeaseQuiet, if_neg hno]
        refine ⟨fun _ => ?_, (fun h => by cases h), (fun h => by cases h)⟩
        have := hI (Or.inl hc)
        omega
    | REQUESTED =>
        obtain ⟨hrow, hcert, hha, hsa, hzero, hpos⟩ :=
          bankWordRootOutgoingStartRows _ _ hpx hpy hc
        have hyes : clockSerializerSOneService ring root y.2.1 root :=
          And.intro rfl hrow
        have hIy := hI (Or.inr hc)
        have hsixy := hSix (Or.inr hc)
        rw [hcert, hha, hsa, bankWordHardEpochSourceLeaseQuiet, if_pos hyes]
        by_cases hl : (y.2.1 root).siLease.val = 0
        · rw [hzero hl]
          refine ⟨(fun h => by rcases h with h | h <;> cases h),
            (fun _ h => by cases h), fun _ _ => ⟨by omega, ?_⟩⟩
          exact Or.inr (bankWordEpochEverSixNext ring root y root hsixy)
        · rw [hpos (Nat.pos_of_ne_zero hl)]
          exact ⟨(fun h => by rcases h with h | h <;> cases h),
            fun _ _ => ⟨by omega, by omega⟩, (fun _ h => by cases h)⟩
    | RUNNING =>
        have hb : (y.2.1 root).ser.phase = .B := hrunB hc
        by_cases hG : (y.2.1 root).ser.out = .DONE ∧
            (y.2.1 (ring.rightNeighbor root)).ser.phase = .F
        · obtain ⟨hrow, hcert, hsoft, hhard⟩ :=
            bankWordRootOutgoingFinishRows _ _ hpx hpy hc hb hG.1 hG.2
          have hno : ¬ clockSerializerSOneService ring root y.2.1 root := by
            intro h
            obtain ⟨_, h2⟩ := h
            rw [hrow] at h2
            exact absurd h2 (by decide)
          rw [hcert, if_neg hno]
          rcases hW hc with hw | hw
          · obtain ⟨hsa, hha⟩ := hsoft hw
            rw [hha, hsa, bankWordEpochSoftAcceptanceLeaseRow]
            refine ⟨fun _ => ?_, (fun h => by cases h), (fun h => by cases h)⟩
            have := hC hc hw
            omega
          · have hha := hhard hw
            by_cases hgen : bankWordHardEpochGenuine ring root
                (bankWordEpochSelectedReceipt ring y root)
                (bankWordHardEpochLedger ring root y) = true
            · exfalso
              have h1 := bankWordHardEpochCountNext ring root y root
              rw [if_pos hgen] at h1
              omega
            · have hnotsix : ¬ BankWordEpochEverSix root y := by
                intro hsix
                exact hgen (widthWordRenewalFrontierWaveHardAcceptGenuine
                  ring root s hn hsmallFive hs y hyR
                  (widthWordRenewalLineageQuietOfEverSix
                    ring hn hsmallFive root s hs hstep y hyR hsix).wave hha)
              have hcnt0 : bankWordRootStartCount root y =
                  bankWordRootStartCount root z₀ := by
                rcases (hV hc hw).2 with h | h
                · exact h
                · exact absurd h hnotsix
              rw [hha, bankWordEpochHardAcceptanceReloadsLease]
              refine ⟨fun _ => by omega, (fun h => by cases h), (fun h => by cases h)⟩
        · obtain ⟨hrowne, hcert, _, hwph, hha, hsa⟩ :=
            bankWordRootOutgoingRunningFrameRows _ _ hpx hpy hc hb hG
          have hno : ¬ clockSerializerSOneService ring root y.2.1 root :=
            fun h => hrowne h.2
          rw [hcert, hwph, hha, hsa, bankWordHardEpochSourceLeaseQuiet, if_neg hno]
          refine ⟨(fun h => by rcases h with h | h <;> cases h),
            fun _ hw => ?_, fun _ hw => ⟨?_, ?_⟩⟩
          · have := hC hc hw
            omega
          · have := (hV hc hw).1
            omega
          · rcases (hV hc hw).2 with h | h
            · exact Or.inl (by omega)
            · exact Or.inr (bankWordEpochEverSixNext ring root y root h)
  · have hne : root ≠ e := by
      rw [← hj]
      exact clockNeighborDifferent ring hn2 e
    rw [hj] at hpx hpy
    obtain ⟨hha, hidle, hkeep⟩ := bankWordRootIncomingRows (y.2.1 e) (y.2.1 root) hpx hpy
    have hlease : (pairW (y.2.1 e) (y.2.1 root)).2.siLease.val ≤
        (y.2.1 root).siLease.val := by
      show (leasePair (compileAdvice (ceilLogTwo n))
        (y.2.1 e).siLease (y.2.1 root).siLease
        (serW (y.2.1 e) (y.2.1 root)).hard.hardAccept
        (serW (y.2.1 e) (y.2.1 root)).hard.softAccept
        (workerW (y.2.1 e) (y.2.1 root)).done).2.val ≤ _
      rw [hha]
      exact bankWordIncomingLeaseLe _ _ _ _ _
    have hno : ¬ clockSerializerSOneService ring root y.2.1 e :=
      fun h => hne h.1.symm
    rw [bankWordEpochRootIncomingRecord ring root y e hj hne, hcnt, if_neg hno]
    rw [pairW_ser_right]
    by_cases hc : (y.2.1 root).ser.cert = .IDLE
    · rw [hidle hc]
      refine ⟨fun _ => ?_, (fun h => by cases h), (fun h => by cases h)⟩
      have := hI (Or.inl hc)
      omega
    · rw [hkeep hc]
      refine ⟨fun h => ?_, fun h1 h2 => ?_, fun h1 h2 => ⟨?_, ?_⟩⟩
      · have := hI h
        omega
      · have := hC h1 h2
        omega
      · have := (hV h1 h2).1
        omega
      · rcases (hV h1 h2).2 with h | h
        · exact Or.inl (by omega)
        · exact Or.inr (bankWordEpochEverSixNext ring root y e h)
  · have hno : ¬ clockSerializerSOneService ring root y.2.1 e :=
      fun h => hne h.1
    rw [bankWordHardEpochRootRemoteFrame ring root y e (Ne.symm hne) (Ne.symm hnj),
      hcnt, if_neg hno]
    refine ⟨fun h => ?_, fun h1 h2 => ?_, fun h1 h2 => ⟨?_, ?_⟩⟩
    · have := hI h
      omega
    · have := hC h1 h2
      omega
    · have := (hV h1 h2).1
      omega
    · rcases (hV h1 h2).2 with h | h
      · exact Or.inl (by omega)
      · exact Or.inr (bankWordEpochEverSixNext ring root y e h)

end

section
open Classical
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

/-- Width port of `bankWordEpochLapInvariantFrom`: the BANK band premise is replaced by `5 ≤ n`, and the renewal constants are those of the compiled width t (lease 8t+4, quota 2t+1). Consumer: `widthWordEpochLapCountOfLineageStep`. -/
theorem widthWordEpochLapInvariantFrom {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hsmallFive : 5 ≤ n)
    (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hs : WidthWordSerializerRootClass ring hsmallFive root s)
    (hstep : BankWordRenewalLineageQuietStep ring root s)
    (z₀ : BankWordEpochState n)
    (hz₀ : BankWordEpochReachable ring root s z₀)
    (hstop : BankWordEpochSOneReached z₀)
    (y : BankWordEpochState n)
    (hy : BankWordEpochReachableFrom ring root z₀ y) :
    BankWordEpochLapInvariant ring root z₀ y := by
  obtain ⟨w, hw⟩ := hy
  rw [← hw]
  have key : ∀ (w : List (Fin n)) (a : BankWordEpochState n),
      BankWordEpochReachableFrom ring root z₀ a →
      BankWordEpochLapInvariant ring root z₀ a →
      BankWordEpochLapInvariant ring root z₀ (bankWordEpochRun ring root a w) := by
    intro w
    induction w with
    | nil => intro a _ h; exact h
    | cons e rest ih =>
        intro a ha h
        exact ih _ (bankWordEpochReachableFromNext ring root z₀ a ha e)
          (widthWordEpochLapInvariantStep ring hn hsmallFive root s hs hstep
            z₀ hz₀ hstop a ha e h)
  exact key w z₀ (bankWordEpochReachableFromSelf ring root z₀)
    (bankWordEpochLapInvariantSelf ring root z₀)

end

section
open Classical
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

/-- Width port of `bankWordEpochLapCountOfLineageStep`: the BANK band premise is replaced by `5 ≤ n`, and the renewal constants are those of the compiled width t (lease 8t+4, quota 2t+1). Consumer: `widthWordEpochPostSOneWorkerClockOfLineageStep`, `widthWordRenewalFreshAttemptCostOfLineageStep`.
 DET from the lap invariant: in every root state `d ≤ L + 1`, so
`L + 2` root S1 services force a genuine acceptance.
Consumer: `widthWordEpochPostSOneWorkerClockOfLineageStep`. -/
theorem widthWordEpochLapCountOfLineageStep {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hsmallFive : 5 ≤ n)
    (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hs : WidthWordSerializerRootClass ring hsmallFive root s)
    (hstep : BankWordRenewalLineageQuietStep ring root s) :
    WidthWordEpochLapCount ring root s := by
  intro z₀ hz₀ hstop z hz hcount
  have hinv := widthWordEpochLapInvariantFrom ring hn hsmallFive root s hs hstep
    z₀ hz₀ hstop z hz
  have hmono := bankWordHardEpochCountFrom ring root z₀ z hz
  rcases Nat.lt_or_ge (bankWordHardEpochLedger ring root z₀).hardEpochs
    (bankWordHardEpochLedger ring root z).hardEpochs with h | h
  · exact h
  · exfalso
    have hEq : (bankWordHardEpochLedger ring root z).hardEpochs =
        (bankWordHardEpochLedger ring root z₀).hardEpochs :=
      Nat.le_antisymm h hmono
    obtain ⟨hI, hC, hV⟩ := hinv hEq
    have hLdef : widthWordRenewalLease n =
        (compileAdvice (ceilLogTwo n)).siLeaseMax := by
      unfold widthWordRenewalLease
      exact (widthWordHardEpochBankLeaseMaximum hsmallFive).symm
    rw [hLdef] at hcount
    have hzR : BankWordEpochReachable ring root s z :=
      bankWordEpochReachableOfFrom ring root s z₀ z hz₀ hz
    have hstopz := bankWordEpochSOneReachedFrom ring root z₀ z hz hstop
    obtain ⟨hW, _⟩ :=
      widthWordEpochPostLatchRootFactsReachable ring hn hsmallFive root s hs z hzR hstopz
    cases hc : (z.2.1 root).ser.cert with
    | IDLE =>
        have := hI (Or.inl hc)
        omega
    | REQUESTED =>
        have := hI (Or.inr hc)
        omega
    | RUNNING =>
        rcases hW hc with hw | hw
        · have := hC hc hw
          omega
        · have := (hV hc hw).1
          omega

end

section
open Classical
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

/-- Width port of `bankWordEpochPostSOneWorkerClockOfLineageStep`: the BANK band premise is replaced by `5 ≤ n`, and the renewal constants are those of the compiled width t (lease 8t+4, quota 2t+1). Consumer: `widthWordEpochPostSOneWorkerClockOfMovingRows`.
 R10a W-stage clock from the J-W lineage step alone.
Consumer: `widthWordProjectedOneEpochCostOfWorkerClock` /
`bankWordProjectedOneEpochExpectedOfWorkerClock`. -/
theorem widthWordEpochPostSOneWorkerClockOfLineageStep {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hsmallFive : 5 ≤ n)
    (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hs : WidthWordSerializerRootClass ring hsmallFive root s)
    (hstep : BankWordRenewalLineageQuietStep ring root s) :
    WidthWordEpochPostSOneWorkerClock ring root s :=
  widthWordEpochPostSOneWorkerClockOfLapCount ring hn hsmallFive root s hs
    (widthWordEpochLapCountOfLineageStep ring hn hsmallFive root s hs hstep)

end

section
open Classical
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

/-- Width port of `bankWordRenewalFreshAttemptCostOfLineageStep`: the BANK band premise is replaced by `5 ≤ n`, and the renewal constants are those of the compiled width t (lease 8t+4, quota 2t+1). Consumer: `widthWordRenewalFreshAttemptCostOfMovingRows`.
 The renewal attempt cost `hcost` of BankWordRenewalFresh, from
the J-W lineage step alone: every fresh attempt ends (completion or
the next genuine acceptance) within one block B.
Consumer: `bankWordRenewalFreshFiveCostOfBounds`. -/
theorem widthWordRenewalFreshAttemptCostOfLineageStep {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hsmallFive : 5 ≤ n)
    (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hs : WidthWordSerializerRootClass ring hsmallFive root s)
    (hstep : BankWordRenewalLineageQuietStep ring root s) :
    WidthWordRenewalFreshAttemptCost ring root s := by
  intro seed T
  have hnc := bankWordRenewalFreshNotCompleted ring root s seed
  calc
    costNumerator
        (L3.Prob.attemptStepper (bankWordRenewalFreshKernel ring root s))
        (fun q => L3.Prob.attemptGood q ∨ L3.Prob.attemptFail q)
        (.active seed.1) T ≤
      costNumerator (bankWordRenewalNext ring root s)
        (fun v : BankWordRenewalPostSOne ring root s =>
          BankWordRenewalCompleted v.1 ∨
          (bankWordHardEpochLedger ring root seed.1.1).hardEpochs <
            (bankWordHardEpochLedger ring root v.1).hardEpochs) seed.1 T :=
      bankWordRenewalFreshAttemptCostLe ring root s seed T seed.1 hnc
        (Nat.le_refl _)
    _ ≤ costNumerator (bankWordRenewalNext ring root s)
        (fun v : BankWordRenewalPostSOne ring root s =>
          (bankWordHardEpochLedger ring root seed.1.1).hardEpochs <
            (bankWordHardEpochLedger ring root v.1).hardEpochs) seed.1 T :=
      L3.Prob.costNumerator_target_mono (bankWordRenewalNext ring root s)
        (fun v : BankWordRenewalPostSOne ring root s =>
          (bankWordHardEpochLedger ring root seed.1.1).hardEpochs <
            (bankWordHardEpochLedger ring root v.1).hardEpochs)
        (fun v : BankWordRenewalPostSOne ring root s =>
          BankWordRenewalCompleted v.1 ∨
          (bankWordHardEpochLedger ring root seed.1.1).hardEpochs <
            (bankWordHardEpochLedger ring root v.1).hardEpochs)
        (fun v h => Or.inr h) seed.1 T
    _ = costNumerator (bankWordEpochNext ring root)
        (fun y => (bankWordHardEpochLedger ring root seed.1.1).hardEpochs <
          (bankWordHardEpochLedger ring root y).hardEpochs) seed.1.1 T :=
      costNumerator_map_eq (bankWordRenewalNext ring root s)
        (bankWordEpochNext ring root) Subtype.val (fun _ _ => rfl)
        (fun y => (bankWordHardEpochLedger ring root seed.1.1).hardEpochs <
          (bankWordHardEpochLedger ring root y).hardEpochs) T seed.1
    _ ≤ n ^ T * ((widthWordRenewalLease n + 2) * (n * (5 * n - 4))) :=
      widthWordEpochGenuineCostOfLapCount ring hn hsmallFive root s hs
        (widthWordEpochLapCountOfLineageStep ring hn hsmallFive root s hs hstep)
        seed.1.1 seed.1.2.1 seed.1.2.2 T
    _ ≤ n ^ T * widthWordRenewalBlock n := by
      unfold widthWordRenewalBlock
      exact Nat.mul_le_mul_left _
        (bankWordEpochLapBlockArithmetic n (widthWordRenewalLease n))

end

section
open Classical
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

/-- Width port of `bankWordRenewalLineageQuietStepOfMovingRows`: the BANK band premise is replaced by `5 ≤ n`, and the renewal constants are those of the compiled width t (lease 8t+4, quota 2t+1). Consumer: `widthWordEpochPostSOneWorkerClockOfMovingRows`, `widthWordRenewalFreshAttemptCostOfMovingRows`.
 Every edge class other than the two residues is already closed:
incoming root (any row), root-outgoing at a REQUESTED / IDLE /
nonvalidating root, the S6 guard, the stationary B/DONE+B root pair,
SR at a C/F root, and internal edges with an inactive root, an
unvisited suffix or a stationary covered pair.
Consumer: `widthWordEpochPostSOneWorkerClockOfMovingRows`. -/
theorem widthWordRenewalLineageQuietStepOfMovingRows {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hsmallFive : 5 ≤ n)
    (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hs : WidthWordSerializerRootClass ring hsmallFive root s)
    (hroot : BankWordRenewalLineageRootMovingStep ring root s)
    (hint : BankWordRenewalLineageInternalMovingStep ring root s) :
    BankWordRenewalLineageQuietStep ring root s := by
  intro z hz hwave e
  have hn2 : 2 ≤ n := by omega
  have hfixed := widthWordEpochFixedRootNext ring hn hsmallFive root s hs z hz e
  rcases clockPostTrichotomy ring root z.2.1 e hn2 hfixed with
    ⟨he, hpx, hpy⟩ | ⟨hj, hpx, hpy⟩ | ⟨hne, hnj, hpx, hpy⟩
  · subst e
    have hidleNext : ((bankWordEpochNext ring root z root).2.1 root).ser.cert =
        .IDLE → BankWordRenewalFrontierWaveLineageQuiet ring root
          (bankWordEpochNext ring root z root) := by
      intro hidle
      apply bankWordRenewalLineageQuietOfNonvalidating
      · rw [hidle]
        exact fun h => by cases h
      · rw [hidle]
        exact fun h => by cases h.1
    have hrecovery : ((z.2.1 root).ser.cert = .IDLE ∨
          (z.2.1 root).ser.cert = .RUNNING) →
        ((z.2.1 root).ser.phase = .C ∨ (z.2.1 root).ser.phase = .F) →
        BankWordRenewalFrontierWaveLineageQuiet ring root
          (bankWordEpochNext ring root z root) := by
      intro hc hp
      apply hidleNext
      rw [bankWordEpochRootOutgoingRecord, pairW_ser_left]
      exact (serRootOutgoingRecovery _ _ hpx hpy hc hp).2.1
    by_cases hreq : (z.2.1 root).ser.cert = .REQUESTED
    · exact widthWordRenewalWaveRootOutgoingKnownRowsStep ring root s hn hsmallFive hs
        z hz hwave (Or.inl hreq)
    · have hcases : (z.2.1 root).ser.cert = .IDLE ∨
          (z.2.1 root).ser.cert = .RUNNING := by
        cases hc : (z.2.1 root).ser.cert with
        | IDLE => exact Or.inl rfl
        | REQUESTED => exact absurd hc hreq
        | RUNNING => exact Or.inr rfl
      by_cases hb : (z.2.1 root).ser.phase = .B
      · by_cases hG : (z.2.1 root).ser.out = .DONE ∧
            (z.2.1 (ring.rightNeighbor root)).ser.phase = .F
        · exact widthWordRenewalWaveRootOutgoingKnownRowsStep ring root s hn hsmallFive hs
            z hz hwave (Or.inr (Or.inl ⟨hreq, hb, hG.1, hG.2⟩))
        · rcases hcases with hc | hc
          · apply hidleNext
            rw [bankWordEpochRootOutgoingRecord, pairW_ser_left]
            exact (bankWordRootOutgoingIdleRows _ _ hpx hpy hc).2.1
          · by_cases hV : (z.2.1 root).ser.wphase = .VALIDATING
            · by_cases hDB : (z.2.1 root).ser.out = .DONE ∧
                  (z.2.1 (ring.rightNeighbor root)).ser.phase = .B
              · exact widthWordRenewalWaveRootOutgoingKnownRowsStep ring root s
                  hn hsmallFive hs z hz hwave
                  (Or.inr (Or.inr ⟨hc, hb, hDB.1, hDB.2⟩))
              · exact hroot z hz hwave hc hV hb hG hDB
            · obtain ⟨_, hcert, _, hwph, _, _⟩ :=
                bankWordRootOutgoingRunningFrameRows _ _ hpx hpy hc hb hG
              apply bankWordRenewalLineageQuietOfNonvalidating
              · rw [bankWordEpochRootOutgoingRecord, pairW_ser_left, hcert]
                exact fun h => by cases h
              · rw [bankWordEpochRootOutgoingRecord, pairW_ser_left, hwph]
                exact fun h => hV h.2
      · have hp : (z.2.1 root).ser.phase = .C ∨ (z.2.1 root).ser.phase = .F := by
          cases hp : (z.2.1 root).ser.phase with
          | C => exact Or.inl rfl
          | B => exact absurd hp hb
          | F => exact Or.inr rfl
        exact hrecovery hcases hp
  · exact widthWordRenewalWaveRootIncomingStep ring root e s hn hsmallFive hs z hz hj hwave
  · by_cases hV : (z.2.1 root).ser.cert = .RUNNING ∧
        (z.2.1 root).ser.wphase = .VALIDATING
    · by_cases hunv : ∀ g : L3.EWord.ValidationGhost,
          L3.EWord.ValidationShape ring root z.2.1 g →
          L3.EWord.validationEdgeClass ring root g e = .unvisitedSuffix
      · exact widthWordRenewalWaveInternalUnvisitedQuietStep ring root e s hn hsmallFive hs
          z hz hne hnj hwave hunv
      · by_cases hDB : (z.2.1 e).ser.phase = .B ∧ (z.2.1 e).ser.out = .DONE ∧
            (z.2.1 (ring.rightNeighbor e)).ser.phase = .B
        · exact widthWordRenewalWaveInternalCoveredDoneQuietStep ring root e s hn hsmallFive hs
            z hz hne hnj hwave hDB.1 hDB.2.1 hDB.2.2
        · exact hint z hz hwave hV.1 hV.2 e hne hnj hunv hDB
    · exact bankWordRenewalWaveInternalInactiveQuietStep ring root e z hne hnj hwave hV

end

section
open Classical
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

/-- Width port of `bankWordEpochPostSOneWorkerClockOfMovingRows`: the BANK band premise is replaced by `5 ≤ n`, and the renewal constants are those of the compiled width t (lease 8t+4, quota 2t+1). Consumer: `widthWordEpochPostSOneWorkerClockOfInternalRows`.
 R10a W-stage clock from the two residual J-W moving-row facts.
Consumer: `widthWordProjectedOneEpochCostOfWorkerClock`. -/
theorem widthWordEpochPostSOneWorkerClockOfMovingRows {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hsmallFive : 5 ≤ n)
    (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hs : WidthWordSerializerRootClass ring hsmallFive root s)
    (hroot : BankWordRenewalLineageRootMovingStep ring root s)
    (hint : BankWordRenewalLineageInternalMovingStep ring root s) :
    WidthWordEpochPostSOneWorkerClock ring root s :=
  widthWordEpochPostSOneWorkerClockOfLineageStep ring hn hsmallFive root s hs
    (widthWordRenewalLineageQuietStepOfMovingRows ring hn hsmallFive root s hs hroot hint)

end

section
open Classical
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

/-- Width port of `bankWordRenewalFreshAttemptCostOfMovingRows`: the BANK band premise is replaced by `5 ≤ n`, and the renewal constants are those of the compiled width t (lease 8t+4, quota 2t+1). Consumer: `widthWordRenewalFreshAttemptCostHolds`.
 The renewal attempt cost from the two residual J-W facts.
Consumer: `bankWordRenewalFreshFiveCostOfBounds`. -/
theorem widthWordRenewalFreshAttemptCostOfMovingRows {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hsmallFive : 5 ≤ n)
    (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hs : WidthWordSerializerRootClass ring hsmallFive root s)
    (hroot : BankWordRenewalLineageRootMovingStep ring root s)
    (hint : BankWordRenewalLineageInternalMovingStep ring root s) :
    WidthWordRenewalFreshAttemptCost ring root s :=
  widthWordRenewalFreshAttemptCostOfLineageStep ring hn hsmallFive root s hs
    (widthWordRenewalLineageQuietStepOfMovingRows ring hn hsmallFive root s hs hroot hint)

end

section

/-- Width port of `bankWordRenewalLineageRootMovingStepHolds`: the BANK band premise is replaced by `5 ≤ n`, and the renewal constants are those of the compiled width t (lease 8t+4, quota 2t+1). Consumer: `widthWordEpochPostSOneWorkerClockOfInternalRows`, `widthWordRenewalFreshAttemptCostHolds`.
 The root residue of the J-W step holds on the represented BANK root class:
a root-outgoing edge at a RUNNING/VALIDATING root preserves the quiet lineage
(`widthWordRenewalWaveRootOutgoingActiveQuietStep`, which needs neither the
phase-B nor the two non-DONE guards of the residue).
Consumer: `widthWordEpochPostSOneWorkerClockOfMovingRows` (its `hroot`). -/
theorem widthWordRenewalLineageRootMovingStepHolds {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hsmallFive : 5 ≤ n)
    (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hs : WidthWordSerializerRootClass ring hsmallFive root s) :
    BankWordRenewalLineageRootMovingStep ring root s := by
  intro z hz hwave hrun hval _ _ _
  exact widthWordRenewalWaveRootOutgoingActiveQuietStep
    ring root s hn hsmallFive hs z hz hwave ⟨hrun, hval⟩

end

section

/-- Width port of `bankWordEpochPostSOneWorkerClockOfInternalRows`: the BANK band premise is replaced by `5 ≤ n`, and the renewal constants are those of the compiled width t (lease 8t+4, quota 2t+1). Consumer: `widthWordEpochPostSOneWorkerClockHolds`.
 The W-stage clock with the root residue discharged: only the internal
moving rows remain. Consumer: BOARD R10a (`hworker` of the BankRepairWord
consumers). -/
theorem widthWordEpochPostSOneWorkerClockOfInternalRows {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hsmallFive : 5 ≤ n)
    (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hs : WidthWordSerializerRootClass ring hsmallFive root s)
    (hint : BankWordRenewalLineageInternalMovingStep ring root s) :
    WidthWordEpochPostSOneWorkerClock ring root s :=
  widthWordEpochPostSOneWorkerClockOfMovingRows ring hn hsmallFive root s hs
    (widthWordRenewalLineageRootMovingStepHolds ring hn hsmallFive root s hs) hint

end

section
open Classical

/-- Width port of `bankWordRenewalWaveInternalReturnRootLineageStep`: the BANK band premise is replaced by `5 ≤ n`, and the renewal constants are those of the compiled width t (lease 8t+4, quota 2t+1). Consumer: `widthWordRenewalWaveInternalReturnMoveQuietStep`.
 RETURN geometry only reads serializer records at the named
cyclic sites. This transports any candidate RETURN witness
backward across a physical serializer frame.
Consumer: quietness preservation at covered S2R and incoming S5. -/
theorem widthWordRenewalWaveInternalReturnRootLineageStep {n : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hn : 5 ≤ n)
    (hsmallFive : 5 ≤ n)
    (hs : WidthWordSerializerRootClass ring hsmallFive root s)
    (z : BankWordEpochState n)
    (hz : BankWordEpochReachable ring root s z)
    (hwave : BankWordRenewalFrontierWaveLineageQuiet ring root z)
    (hactive : (z.2.1 root).ser.cert = .RUNNING ∧
      (z.2.1 root).ser.wphase = .VALIDATING)
    (g : L3.EWord.ValidationGhost)
    (hg : g = Classical.choose (hwave.wave.2 hactive))
    (hr : L3.EWord.ReturnShape ring root z.2.1 g)
    (hp : 1 < g.pivot)
    (he : e = L3.EWord.site ring root (g.pivot - 1)) :
    BankWordRenewalFrontierTicketLineage ring root
      (bankWordEpochNext ring root z e) := by
  have hspec := Classical.choose_spec (hwave.wave.2 hactive)
  rw [← hg] at hspec
  obtain ⟨req, stamp, hshape, hsites⟩ := hspec
  have hreturnRootCovered : 0 < g.scrub := by
    rw [hr.covered]
    have hbound := hr.pivotBound
    omega
  have hreturnSourceCovered : g.pivot - 1 < g.scrub := by
    rw [hr.covered]
    have hbound := hr.pivotBound
    omega
  have hreturnPivotCovered : g.pivot < g.scrub := by
    rw [hr.covered]
    exact hr.pivotBound
  have hrootDone := hr.completed
    (⟨0, (show 0 < n by omega)⟩ : Fin n)
    hr.pivotPositive
  have hbRoot : (z.2.1 root).ser.phase = .B := by
    simpa only [L3.EWord.siteZero] using hrootDone.1
  have hdRoot : (z.2.1 root).ser.out = .DONE := by
    simpa only [L3.EWord.siteZero] using hrootDone.2.1
  have hvalidRoot :
      (z.2.1 root).ser.wphase = .VALIDATING := hactive.2
  have hpIndex : g.pivot - 1 < n := by
    exact Nat.lt_of_le_of_lt (Nat.sub_le g.pivot 1)
      hr.pivotBound
  have hpPred : g.pivot - 1 < g.pivot := by omega
  have hsourceOld := hr.completed
    (⟨g.pivot - 1, hpIndex⟩ : Fin n)
    (by simpa only [Fin.val_mk] using hpPred)
  have hb : (z.2.1 e).ser.phase = .B := by
    rw [he]
    exact hsourceOld.1
  have hd : (z.2.1 e).ser.out = .DONE := by
    rw [he]
    exact hsourceOld.2.1
  have hvalid : (z.2.1 e).ser.wphase = .VALIDATING := by
    rw [he]
    exact hsourceOld.2.2
  have hresponder :
      ring.rightNeighbor e =
        L3.EWord.site ring root g.pivot := by
    have ht := L3.EWord.validationParentNeighbor
      ring root (g.pivot - 1) e he
    have hidx : g.pivot - 1 + 1 = g.pivot := by omega
    rw [hidx] at ht
    exact ht
  have hf : (z.2.1 (ring.rightNeighbor e)).ser.phase =
      .F := by
    rw [hresponder]
    exact hr.leftmostF
  have hsourceOldTicket :
      BankWordRenewalFrontierWaveSiteTicket ring root z
        req stamp (⟨g.pivot - 1, hpIndex⟩ : Fin n)
        .done := by
    have ht := (hsites
      (⟨g.pivot - 1, hpIndex⟩ : Fin n)
      (by simpa only [Fin.val_mk] using hreturnSourceCovered)).1
      ⟨by simpa only [Fin.val_mk] using hsourceOld.1,
       by simpa only [Fin.val_mk] using hsourceOld.2.2⟩
    have hdSite :
        (z.2.1
          (L3.EWord.site ring root (g.pivot - 1))).ser.out =
            .DONE := hsourceOld.2.1
    simpa [Fin.val_mk, hdSite] using ht
  have htargetOldTicket :
      BankWordRenewalFrontierWaveSiteTicket ring root z
        req stamp (⟨g.pivot, hr.pivotBound⟩ : Fin n)
        .returned := by
    exact (hsites
      (⟨g.pivot, hr.pivotBound⟩ : Fin n)
      (by simpa only [Fin.val_mk] using hreturnPivotCovered)).2.2.2.2
      ⟨by simpa only [Fin.val_mk] using hr.leftmostF,
       hr.isReturn,
       by simp only [Fin.val_mk]; exact Nat.le_refl g.pivot⟩
  obtain ⟨parent, htParent, hreqParent, hstampParent⟩ :=
    hsourceOldTicket
  obtain ⟨child, htChild, hreqChild, hstampChild⟩ :=
    htargetOldTicket
  have htParentAtE :
      wTicketAt .done
        ((bankWordHardEpochLedger ring root z).validation e) =
          some parent := by
    rw [he]
    simpa only [Fin.val_mk] using htParent
  have htChildAtResp :
      wTicketAt .returned
        ((bankWordHardEpochLedger ring root z).validation
          (ring.rightNeighbor e)) = some child := by
    rw [hresponder]
    simpa only [Fin.val_mk] using htChild
  have heNotRoot : e ≠ root := by
    rw [he]
    exact L3.EWord.validationPositiveSiteNotRoot
      ring root (g.pivot - 1) hpIndex (by omega)
  have hrespNotRoot : ring.rightNeighbor e ≠ root := by
    rw [hresponder]
    exact L3.EWord.validationPositiveSiteNotRoot
      ring root g.pivot hr.pivotBound hr.pivotPositive
  have hclass := widthWordEpochReachablePhysicalRootClass
    ring hn hsmallFive root s hs z hz
  have hfixed : WFixedRoot ring root
      (phiW ring z.2.1 e) :=
    ((widthWordSerializerRootClassClosed ring hn hsmallFive root).2
      z.2.1 hclass e).2
  have hpost := clockPostInternal ring root z.2.1 e
    (by omega : 2 ≤ n) hfixed heNotRoot hrespNotRoot
  have hrow :
      (bankWordEpochSelectedReceipt ring z e).serializer.row =
        "S2N" :=
    (L3.EWord.validationReturnMoveSerializer
      (z.2.1 e) (z.2.1 (ring.rightNeighbor e))
      hpost.1 hpost.2 hb hd hf).1
  have hjoined := bankWordRenewalWaveReturnMoveTicketStep
    ring root e z (by omega : 2 ≤ n) parent child
    hrow hd hf htParentAtE htChildAtResp
    (hreqParent.trans hreqChild.symm)
    (hstampParent.trans hstampChild.symm)
  have hrootSer :
      ((bankWordEpochNext ring root z e).2.1 root).ser =
        (z.2.1 root).ser := by
    change ((phiW ring z.2.1 e) root).ser =
      (z.2.1 root).ser
    exact phiW_ser_remote ring z.2.1 e root
      heNotRoot.symm hrespNotRoot.symm
  have hrootLedger :
      (bankWordHardEpochLedger ring root
        (bankWordEpochNext ring root z e)).validation root =
      (bankWordHardEpochLedger ring root z).validation root :=
    bankWordRenewalFrontierWaveTicketRemoteFrame
      ring root z e root heNotRoot.symm hrespNotRoot.symm
  have hrootOldTicket :
      BankWordRenewalFrontierWaveSiteTicket ring root z
        req stamp (⟨0, (show 0 < n by omega)⟩ : Fin n)
        .done := by
    have ht := (hsites
      (⟨0, (show 0 < n by omega)⟩ : Fin n)
      (by simpa only [Fin.val_mk] using hreturnRootCovered)).1
      ⟨by simpa only [Fin.val_mk, L3.EWord.siteZero] using hbRoot,
       by simpa only [Fin.val_mk, L3.EWord.siteZero] using
           hvalidRoot⟩
    simpa [Fin.val_mk, L3.EWord.siteZero, hdRoot] using ht
  obtain ⟨rootTicket, htRoot, hreqRoot, hstampRoot⟩ :=
    hrootOldTicket
  have htRootNew :
      wTicketAt .done
        ((bankWordHardEpochLedger ring root
          (bankWordEpochNext ring root z e)).validation root) =
        some rootTicket := by
    rw [hrootLedger]
    simpa only [Fin.val_mk, L3.EWord.siteZero] using htRoot
  have hnewFirstB : 2 < g.pivot →
      ((bankWordEpochNext ring root z e).2.1
        (ring.rightNeighbor root)).ser.phase = .B := by
    intro hlt
    have hfirstOld :
        (z.2.1 (ring.rightNeighbor root)).ser.phase = .B := by
      simpa only [L3.EWord.siteOne] using
        (hr.completed
          (⟨1, (show 1 < n by omega)⟩ : Fin n)
          (by simpa only [Fin.val_mk] using
            (show 1 < g.pivot by omega))).1
    have hpBound : g.pivot - 1 + 1 < n := by
      have ht := hr.pivotBound
      omega
    have hnotLeft : 1 ≠ g.pivot - 1 := by omega
    have hnotRight : 1 ≠ (g.pivot - 1) + 1 := by omega
    have hfr := L3.EWord.validationParentFrame
      ring root z.2.1 (g.pivot - 1) e
      hpBound he 1 (by omega : 1 < n)
      hnotLeft hnotRight
    change ((phiW ring z.2.1 e)
      (ring.rightNeighbor root)).ser.phase = .B
    rw [← L3.EWord.siteOne, hfr]
    exact hfirstOld
  unfold BankWordRenewalFrontierTicketLineage
  refine ⟨?_, ?_, ?_⟩
  · intro hnew
    have hold : (z.2.1 root).ser.cert = .REQUESTED := by
      simpa only [hrootSer] using hnew
    rw [hactive.1] at hold
    cases hold
  · intro hnew
    have hwrong :
        ((bankWordEpochNext ring root z e).2.1 root).ser.out =
          .WAIT := hnew.2.2.2.1
    rw [hrootSer, hdRoot] at hwrong
    cases hwrong
  · intro hnew
    by_cases htwo : g.pivot = 2
    · have hfirst : e = ring.rightNeighbor root := by
        simpa [htwo, L3.EWord.siteOne] using he
      have htFirstNew :
          wTicketAt .returned
            ((bankWordHardEpochLedger ring root
              (bankWordEpochNext ring root z e)).validation
                (ring.rightNeighbor root)) =
            some { parent with stage := .returned } := by
        rw [← hfirst, hjoined.1]
        rfl
      refine ⟨rootTicket, { parent with stage := .returned },
        htRootNew, htFirstNew, ?_, ?_⟩
      · exact hreqRoot.trans hreqParent.symm
      · exact hstampRoot.trans hstampParent.symm
    · have hlt : 2 < g.pivot := by
        have hpositive := hp
        omega
      have hwrong :
          ((bankWordEpochNext ring root z e).2.1
            (ring.rightNeighbor root)).ser.phase = .F :=
        hnew.2.2.2.2
      rw [hnewFirstB hlt] at hwrong
      cases hwrong

end

section
open Classical

/-- Width port of `bankWordRenewalWaveInternalReturnMoveQuietStep`: the BANK band premise is replaced by `5 ≤ n`, and the renewal constants are those of the compiled width t (lease 8t+4, quota 2t+1). Consumer: `widthWordRenewalWaveInternalReturnCoveredQuietStep`. -/
theorem widthWordRenewalWaveInternalReturnMoveQuietStep {n : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hn : 5 ≤ n)
    (hsmallFive : 5 ≤ n)
    (hs : WidthWordSerializerRootClass ring hsmallFive root s)
    (z : BankWordEpochState n)
    (hz : BankWordEpochReachable ring root s z)
    (hwave : BankWordRenewalFrontierWaveLineageQuiet ring root z)
    (hactive : (z.2.1 root).ser.cert = .RUNNING ∧
      (z.2.1 root).ser.wphase = .VALIDATING)
    (g : L3.EWord.ValidationGhost)
    (hg : g = Classical.choose (hwave.wave.2 hactive))
    (hr : L3.EWord.ReturnShape ring root z.2.1 g)
    (hp : 1 < g.pivot)
    (he : e = L3.EWord.site ring root (g.pivot - 1)) :
    BankWordRenewalFrontierWaveLineageQuiet ring root
      (bankWordEpochNext ring root z e) := by
  have hspec := Classical.choose_spec (hwave.wave.2 hactive)
  rw [← hg] at hspec
  obtain ⟨req, stamp, hshape, hsites⟩ := hspec
  have hreturnSourceCovered : g.pivot - 1 < g.scrub := by
    rw [hr.covered]
    have hbound := hr.pivotBound
    omega
  have hreturnPivotCovered : g.pivot < g.scrub := by
    rw [hr.covered]
    exact hr.pivotBound
  have hbase := widthWordRenewalWaveInternalReturnRootLineageStep
    ring root e s hn hsmallFive hs z hz hwave hactive
    g hg hr hp he
  have hbound : g.pivot - 1 < n := by
    exact Nat.lt_of_le_of_lt (Nat.sub_le g.pivot 1)
      hr.pivotBound
  have hpred : g.pivot - 1 < g.pivot := by omega
  have hsourceOld := hr.completed
    (⟨g.pivot - 1, hbound⟩ : Fin n)
    (by simpa only [Fin.val_mk] using hpred)
  have hb : (z.2.1 e).ser.phase = .B := by
    rw [he]
    exact hsourceOld.1
  have hd : (z.2.1 e).ser.out = .DONE := by
    rw [he]
    exact hsourceOld.2.1
  have hresponder :
      ring.rightNeighbor e = L3.EWord.site ring root g.pivot := by
    have ht := L3.EWord.validationParentNeighbor
      ring root (g.pivot - 1) e he
    have hidx : g.pivot - 1 + 1 = g.pivot := by omega
    rw [hidx] at ht
    exact ht
  have hf : (z.2.1 (ring.rightNeighbor e)).ser.phase = .F := by
    rw [hresponder]
    exact hr.leftmostF
  have hsourceOldTicket :
      BankWordRenewalFrontierWaveSiteTicket ring root z
        req stamp (⟨g.pivot - 1, hbound⟩ : Fin n)
        .done := by
    have hlt : g.pivot - 1 < g.scrub := hreturnSourceCovered
    have ht := (hsites
      (⟨g.pivot - 1, hbound⟩ : Fin n)
      (by simpa only [Fin.val_mk] using hlt)).1
      ⟨by simpa only [Fin.val_mk] using hsourceOld.1,
       by simpa only [Fin.val_mk] using hsourceOld.2.2⟩
    simpa [Fin.val_mk, hsourceOld.2.1] using ht
  have htargetOldTicket :
      BankWordRenewalFrontierWaveSiteTicket ring root z
        req stamp (⟨g.pivot, hr.pivotBound⟩ : Fin n)
        .returned := by
    have hlt : g.pivot < g.scrub := hreturnPivotCovered
    exact (hsites
      (⟨g.pivot, hr.pivotBound⟩ : Fin n)
      (by simpa only [Fin.val_mk] using hlt)).2.2.2.2
      ⟨by simpa only [Fin.val_mk] using hr.leftmostF,
       hr.isReturn,
       by simp only [Fin.val_mk]; exact Nat.le_refl g.pivot⟩
  obtain ⟨parent, htParent, hreqParent, hstampParent⟩ :=
    hsourceOldTicket
  obtain ⟨child, htChild, hreqChild, hstampChild⟩ :=
    htargetOldTicket
  have htParentAtE :
      wTicketAt .done
        ((bankWordHardEpochLedger ring root z).validation e) =
          some parent := by
    rw [he]
    simpa only [Fin.val_mk] using htParent
  have htChildAtResp :
      wTicketAt .returned
        ((bankWordHardEpochLedger ring root z).validation
          (ring.rightNeighbor e)) = some child := by
    rw [hresponder]
    simpa only [Fin.val_mk] using htChild
  have heNotRoot : e ≠ root := by
    rw [he]
    exact L3.EWord.validationPositiveSiteNotRoot
      ring root (g.pivot - 1) hbound (by omega)
  have hrespNotRoot : ring.rightNeighbor e ≠ root := by
    rw [hresponder]
    exact L3.EWord.validationPositiveSiteNotRoot
      ring root g.pivot hr.pivotBound hr.pivotPositive
  have hclass := widthWordEpochReachablePhysicalRootClass
    ring hn hsmallFive root s hs z hz
  have hfixed : WFixedRoot ring root (phiW ring z.2.1 e) :=
    ((widthWordSerializerRootClassClosed ring hn hsmallFive root).2
      z.2.1 hclass e).2
  have hpost := clockPostInternal ring root z.2.1 e
    (by omega : 2 ≤ n) hfixed heNotRoot hrespNotRoot
  have hrow := L3.EWord.validationReturnMoveSerializer
    (z.2.1 e) (z.2.1 (ring.rightNeighbor e))
    hpost.1 hpost.2 hb hd hf
  have hrowAt :
      (bankWordEpochSelectedReceipt ring z e).serializer.row =
        "S2N" := hrow.1
  have hjoined := bankWordRenewalWaveReturnMoveTicketStep
    ring root e z (by omega : 2 ≤ n) parent child
    hrowAt hd hf htParentAtE htChildAtResp
    (hreqParent.trans hreqChild.symm)
    (hstampParent.trans hstampChild.symm)
  have hne : ring.rightNeighbor e ≠ e :=
    clockNeighborDifferent ring (by omega : 2 ≤ n) e
  have hsourceF :
      ((bankWordEpochNext ring root z e).2.1 e).ser.phase =
        .F := by
    change ((phiW ring z.2.1 e) e).ser.phase = .F
    rw [phiW_ser_source]
    exact hrow.2.1
  have htargetF :
      ((bankWordEpochNext ring root z e).2.1
        (ring.rightNeighbor e)).ser.phase = .F := by
    change ((phiW ring z.2.1 e)
      (ring.rightNeighbor e)).ser.phase = .F
    rw [phiW_ser_target ring z.2.1 e hne, hrow.2.2.2]
    exact hf
  have hsourceTicketNew :
      BankWordRenewalFrontierWaveSiteTicket ring root
        (bankWordEpochNext ring root z e) req stamp
        (⟨g.pivot - 1, hbound⟩ : Fin n) .returned := by
    unfold BankWordRenewalFrontierWaveSiteTicket
    refine ⟨{ parent with stage := .returned }, ?_, ?_, ?_⟩
    · simp only [Fin.val_mk, ← he, hjoined.1, wTicketAt]
      rfl
    · exact hreqParent
    · exact hstampParent
  have htargetTicketNew :
      BankWordRenewalFrontierWaveSiteTicket ring root
        (bankWordEpochNext ring root z e) req stamp
        (⟨g.pivot, hr.pivotBound⟩ : Fin n) .returned := by
    unfold BankWordRenewalFrontierWaveSiteTicket
    refine ⟨child, ?_, hreqChild, hstampChild⟩
    · simpa only [Fin.val_mk, ← hresponder, hjoined.2]
        using htChildAtResp
  have hno : (serW (z.2.1 e)
      (z.2.1 (ring.rightNeighbor e))).hard.hardAccept =
        false := L3.EWord.nonrootNoAccept
          (z.2.1 e) (z.2.1 (ring.rightNeighbor e)) hpost.1
  have hstart : (serW (z.2.1 e)
      (z.2.1 (ring.rightNeighbor e))).hard.hardS1 =
        false := L3.EWord.nonrootHardStartFalse
          (z.2.1 e) (z.2.1 (ring.rightNeighbor e)) hpost.1
  have hghost := L3.EWord.validationReturnMoveGhost
    ring root z.2.1 g e hstart hr.isReturn hp he
    hb hd hf hrow.1
  have hshapeNew :
      L3.EWord.ValidationShape ring root
        (bankWordEpochNext ring root z e).2.1
          { g with pivot := g.pivot - 1 } := by
    have ht := (L3.EWord.validationTransport
      (c := compileAdvice (ceilLogTwo n)) ring root)
      z.2.1 g e hshape hfixed hno
    rw [hghost] at ht
    exact ht
  have hnewWave :
      BankWordRenewalFrontierWaveLineage ring root
        (bankWordEpochNext ring root z e) := by
    refine ⟨hbase, ?_⟩
    intro hactiveNew
    refine ⟨{ g with pivot := g.pivot - 1 }, req, stamp,
      hshapeNew, ?_⟩
    intro k hk
    by_cases hsrcIndex : k.val = g.pivot - 1
    · have hsite :
          L3.EWord.site ring root k.val = e := by
        rw [hsrcIndex, ← he]
      have hindex : k =
          (⟨g.pivot - 1, hbound⟩ : Fin n) := by
        apply Fin.ext
        simpa only [Fin.val_mk] using hsrcIndex
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · intro h
        have hwrong := h.1
        rw [hsite, hsourceF] at hwrong
        cases hwrong
      · intro h
        have hwrong := h.1
        rw [hsite, hsourceF] at hwrong
        cases hwrong
      · intro h
        have hwrong := h.1
        rw [hsite, hsourceF] at hwrong
        cases hwrong
      · intro h
        have hwrong := h.1
        rw [hsite, hsourceF] at hwrong
        cases hwrong
      · intro h
        rw [hindex]
        exact hsourceTicketNew
    · by_cases hdstIndex : k.val = g.pivot
      · have hsite :
            L3.EWord.site ring root k.val =
              ring.rightNeighbor e := by
          rw [hdstIndex, ← hresponder]
        have hindex : k =
            (⟨g.pivot, hr.pivotBound⟩ : Fin n) := by
          apply Fin.ext
          simpa only [Fin.val_mk] using hdstIndex
        refine ⟨?_, ?_, ?_, ?_, ?_⟩
        · intro h
          have hwrong := h.1
          rw [hsite, htargetF] at hwrong
          cases hwrong
        · intro h
          have hwrong := h.1
          rw [hsite, htargetF] at hwrong
          cases hwrong
        · intro h
          have hwrong := h.1
          rw [hsite, htargetF] at hwrong
          cases hwrong
        · intro h
          have hwrong := h.1
          rw [hsite, htargetF] at hwrong
          cases hwrong
        · intro h
          rw [hindex]
          exact htargetTicketNew
      · have hsrcNe :
            L3.EWord.site ring root k.val ≠ e := by
          intro h
          have hsame :
              L3.EWord.site ring root k.val =
                L3.EWord.site ring root (g.pivot - 1) := by
            rw [← he]
            exact h
          have heq := L3.EWord.validationSiteInjective
            ring root k.val (g.pivot - 1) k.isLt hbound hsame
          exact hsrcIndex heq
        have hdstNe :
            L3.EWord.site ring root k.val ≠
              ring.rightNeighbor e := by
          intro h
          have hsame :
              L3.EWord.site ring root k.val =
                L3.EWord.site ring root g.pivot := by
            rw [← hresponder]
            exact h
          have heq := L3.EWord.validationSiteInjective
            ring root k.val g.pivot k.isLt hr.pivotBound hsame
          exact hdstIndex heq
        have hserFrame :
            ((bankWordEpochNext ring root z e).2.1
              (L3.EWord.site ring root k.val)).ser =
              (z.2.1 (L3.EWord.site ring root k.val)).ser := by
          change ((phiW ring z.2.1 e)
            (L3.EWord.site ring root k.val)).ser =
            (z.2.1 (L3.EWord.site ring root k.val)).ser
          exact phiW_ser_remote ring z.2.1 e
            (L3.EWord.site ring root k.val) hsrcNe hdstNe
        have hticketFrame := bankWordRenewalFrontierWaveTicketRemoteFrame
          ring root z e (L3.EWord.site ring root k.val)
          hsrcNe hdstNe
        have hkOld : k.val < g.scrub := by
          rw [hr.covered]
          exact k.isLt
        obtain ⟨hB, hP, hI, hL, hF⟩ := hsites k hkOld
        refine ⟨?_, ?_, ?_, ?_, ?_⟩
        · intro h
          have ht := hB (by simpa only [hserFrame] using h)
          simpa only [BankWordRenewalFrontierWaveSiteTicket,
            hserFrame, hticketFrame] using ht
        · intro h
          have ht := hP (by simpa only [hserFrame] using h)
          simpa only [BankWordRenewalFrontierWaveSiteTicket,
            hserFrame, hticketFrame] using ht
        · intro h
          have ht := hI (by simpa only [hserFrame] using h)
          simpa only [BankWordRenewalFrontierWaveSiteTicket,
            hserFrame, hticketFrame] using ht
        · intro h
          have ht := hL (by simpa only [hserFrame] using h)
          simpa only [BankWordRenewalFrontierWaveSiteTicket,
            hserFrame, hticketFrame] using ht
        · intro h
          have hphase :
              (z.2.1 (L3.EWord.site ring root k.val)).ser.phase =
                .F := by
            simpa only [hserFrame] using h.1
          have hge : g.pivot ≤ k.val := by
            by_cases hsmall : k.val < g.pivot
            · have holdB := (hr.completed k hsmall).1
              rw [hphase] at holdB
              cases holdB
            · omega
          have ht := hF ⟨hphase, hr.isReturn, hge⟩
          simpa only [BankWordRenewalFrontierWaveSiteTicket,
            hserFrame, hticketFrame] using ht
  exact bankWordRenewalWaveReturnMoveQuietUpgrade
    ring root e z (by omega : 2 ≤ n) g hwave hactive
    hshape hr hp he hfixed hpost.1 hpost.2 hb hd hf
    hnewWave

end

section
open Classical

/-- Width port of `bankWordRenewalWaveInternalFrontierInternalQuietStep`: the BANK band premise is replaced by `5 ≤ n`, and the renewal constants are those of the compiled width t (lease 8t+4, quota 2t+1). Consumer: `widthWordRenewalWaveInternalFrontierParentQuietStep`. -/
theorem widthWordRenewalWaveInternalFrontierInternalQuietStep {n : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hn : 5 ≤ n)
    (hsmallFive : 5 ≤ n)
    (hs : WidthWordSerializerRootClass ring hsmallFive root s)
    (z : BankWordEpochState n)
    (hz : BankWordEpochReachable ring root s z)
    (hwave : BankWordRenewalFrontierWaveLineageQuiet ring root z)
    (hactive : (z.2.1 root).ser.cert = .RUNNING ∧
      (z.2.1 root).ser.wphase = .VALIDATING)
    (g : L3.EWord.ValidationGhost)
    (hg : g = Classical.choose (hwave.wave.2 hactive))
    (hf : L3.EWord.ForwardShape ring root z.2.1 g)
    (hp : 0 < g.pivot)
    (he : e = L3.EWord.site ring root g.pivot)
    (hw : (z.2.1 e).ser.out = .WAIT)
    (hc : (z.2.1 (ring.rightNeighbor e)).ser.phase = .C)
    (hi : (z.2.1 (ring.rightNeighbor e)).ser.probe =
      .INTERNAL_OK) :
    BankWordRenewalFrontierWaveLineageQuiet ring root
      (bankWordEpochNext ring root z e) := by
  have hspec := Classical.choose_spec (hwave.wave.2 hactive)
  rw [← hg] at hspec
  obtain ⟨req, stamp, hshape, hsites⟩ := hspec
  have hwaitAt :
      (z.2.1 (L3.EWord.site ring root g.pivot)).ser.out =
        .WAIT := by rw [← he]; exact hw
  have hwaitOb := L3.EWord.validationFrontierWaitObligation
    ring root z.2.1 g hf hwaitAt
  have hscrub : g.scrub = g.pivot + 2 := hwaitOb.1
  have hchildInternal := L3.EWord.validationFrontierWaitInternalWitness
    ring root z.2.1 g hf hwaitAt
    (by
      have hj := L3.EWord.validationParentNeighbor
        ring root g.pivot e he
      rw [← hj]
      exact hi)
  have hbound : g.pivot + 2 < n := hchildInternal.2
  have hpBound : g.pivot < n := by omega
  have hchildSite : ring.rightNeighbor e =
      L3.EWord.site ring root (g.pivot + 1) :=
    L3.EWord.validationParentNeighbor ring root g.pivot e he
  have hb : (z.2.1 e).ser.phase = .B := by
    rw [he]
    exact hf.parentB
  have hv : (z.2.1 e).ser.wphase = .VALIDATING := by
    rw [he]
    exact hf.parentValidating
  have hchildValid :
      (z.2.1 (ring.rightNeighbor e)).ser.wphase =
        .VALIDATING := by
    have hpc := hwaitOb.2
    unfold L3.EWord.pendingChild at hpc
    rcases hpc.2 with hpend | hinter | hleaf
    · have hwrong :
          (z.2.1 (ring.rightNeighbor e)).ser.probe =
            .PENDING := by
        rw [hchildSite]
        exact hpend.1
      rw [hi] at hwrong
      cases hwrong
    · rw [hchildSite]
      exact hinter.2.2
    · have hwrong :
          (z.2.1 (ring.rightNeighbor e)).ser.probe =
            .LEAF_OK := by
        rw [hchildSite]
        exact hleaf.2.1
      rw [hi] at hwrong
      cases hwrong
  have holdSource :
      BankWordRenewalFrontierWaveSiteTicket ring root z
        req stamp (⟨g.pivot, hpBound⟩ : Fin n) .waiting := by
    have hk : g.pivot < g.scrub := by rw [hscrub]; omega
    have ht := (hsites
      (⟨g.pivot, hpBound⟩ : Fin n)
      (by simpa only [Fin.val_mk] using hk)).1
      ⟨by simpa only [Fin.val_mk] using hf.parentB,
       by simpa only [Fin.val_mk] using hf.parentValidating⟩
    simpa [Fin.val_mk, hwaitAt] using ht
  have holdChild :
      BankWordRenewalFrontierWaveSiteTicket ring root z
        req stamp
        (⟨g.pivot + 1, hf.pivotBound⟩ : Fin n)
        .observedInternal := by
    have hk : g.pivot + 1 < g.scrub := by rw [hscrub]; omega
    exact (hsites
      (⟨g.pivot + 1, hf.pivotBound⟩ : Fin n)
      (by simpa only [Fin.val_mk] using hk)).2.2.1
      ⟨by simpa only [Fin.val_mk, ← hchildSite] using hc,
       by simpa only [Fin.val_mk, ← hchildSite] using hi,
       by simpa only [Fin.val_mk, ← hchildSite] using hchildValid⟩
  obtain ⟨parent, htParent, hpReq, hpStamp⟩ := holdSource
  obtain ⟨child, htChild, hcReq, hcStamp⟩ := holdChild
  have htSourceAtE :
      wTicketAt .waiting
        ((bankWordHardEpochLedger ring root z).validation e) =
          some parent := by
    rw [he]
    simpa only [Fin.val_mk] using htParent
  have htChildAtResp :
      wTicketAt .observedInternal
        ((bankWordHardEpochLedger ring root z).validation
          (ring.rightNeighbor e)) = some child := by
    rw [hchildSite]
    simpa only [Fin.val_mk] using htChild
  have heNotRoot : e ≠ root := by
    rw [he]
    exact L3.EWord.validationPositiveSiteNotRoot
      ring root g.pivot hpBound hp
  have htargetNotRoot : ring.rightNeighbor e ≠ root := by
    rw [hchildSite]
    exact L3.EWord.validationPositiveSiteNotRoot
      ring root (g.pivot + 1) hf.pivotBound (by omega)
  have hclass := widthWordEpochReachablePhysicalRootClass
    ring hn hsmallFive root s hs z hz
  have hfixed : WFixedRoot ring root (phiW ring z.2.1 e) :=
    ((widthWordSerializerRootClassClosed ring hn hsmallFive root).2
      z.2.1 hclass e).2
  have hpost := clockPostInternal ring root z.2.1 e
    (by omega : 2 ≤ n) hfixed heNotRoot htargetNotRoot
  have hpairSer := L3.EWord.validationParentInternalWrite
    (z.2.1 e) (z.2.1 (ring.rightNeighbor e))
    hpost.2 (by intro h; rw [hpost.1] at h; cases h)
    hb hw hv hc hi
  have hrow :
      (bankWordEpochSelectedReceipt ring z e).serializer.row =
        "S2N" := by
    change (serW (z.2.1 e)
      (z.2.1 (ring.rightNeighbor e))).row = "S2N"
    simp [serW, serializerStep, ProjW.lift,
      hpost.1, hpost.2, hb]
  have hjoined := bankWordRenewalWaveInternalAdmissionTicketStep
    ring root e z (by omega : 2 ≤ n) parent child
    hrow hw hc hi htSourceAtE htChildAtResp
    (hpReq.trans hcReq.symm) (hpStamp.trans hcStamp.symm)
  have hne : ring.rightNeighbor e ≠ e :=
    clockNeighborDifferent ring (by omega : 2 ≤ n) e
  have hsrcSer :
      ((bankWordEpochNext ring root z e).2.1 e).ser =
        { (z.2.1 e).ser with out := .DONE } := by
    change ((phiW ring z.2.1 e) e).ser =
      { (z.2.1 e).ser with out := .DONE }
    rw [phiW_ser_source]
    exact hpairSer.1
  have hdstSer :
      ((bankWordEpochNext ring root z e).2.1
        (ring.rightNeighbor e)).ser =
        { (z.2.1 (ring.rightNeighbor e)).ser with
          phase := .B, out := .NEW, probe := .NONE,
          wphase := .VALIDATING } := by
    change ((phiW ring z.2.1 e)
      (ring.rightNeighbor e)).ser =
        { (z.2.1 (ring.rightNeighbor e)).ser with
          phase := .B, out := .NEW, probe := .NONE,
          wphase := .VALIDATING }
    rw [phiW_ser_target ring z.2.1 e hne]
    exact hpairSer.2
  have hsrcB :
      ((bankWordEpochNext ring root z e).2.1 e).ser.phase = .B := by
    rw [hsrcSer]
    exact hb
  have hsrcDone :
      ((bankWordEpochNext ring root z e).2.1 e).ser.out = .DONE := by
    rw [hsrcSer]
  have hdstB :
      ((bankWordEpochNext ring root z e).2.1
        (ring.rightNeighbor e)).ser.phase = .B := by
    rw [hdstSer]
  have hdstNew :
      ((bankWordEpochNext ring root z e).2.1
        (ring.rightNeighbor e)).ser.out = .NEW := by
    rw [hdstSer]
  have hsrcTicket :
      BankWordRenewalFrontierWaveSiteTicket ring root
        (bankWordEpochNext ring root z e) req stamp
        (⟨g.pivot, hpBound⟩ : Fin n) .done := by
    unfold BankWordRenewalFrontierWaveSiteTicket
    refine ⟨{ parent with stage := .done }, ?_, hpReq, hpStamp⟩
    simp only [Fin.val_mk, ← he, hjoined.1, wTicketAt]
    rfl
  have hdstTicket :
      BankWordRenewalFrontierWaveSiteTicket ring root
        (bankWordEpochNext ring root z e) req stamp
        (⟨g.pivot + 1, hf.pivotBound⟩ : Fin n)
        .broadcaster := by
    unfold BankWordRenewalFrontierWaveSiteTicket
    refine ⟨{ parent with stage := .broadcaster }, ?_, hpReq, hpStamp⟩
    simp only [Fin.val_mk, ← hchildSite, hjoined.2, wTicketAt]
    rfl
  have hrootSer :
      ((bankWordEpochNext ring root z e).2.1 root).ser =
        (z.2.1 root).ser := by
    change ((phiW ring z.2.1 e) root).ser =
      (z.2.1 root).ser
    exact phiW_ser_remote ring z.2.1 e root
      heNotRoot.symm htargetNotRoot.symm
  have hrootDone : (z.2.1 root).ser.out = .DONE := by
    have hdone := hf.completed
      (⟨0, (show 0 < n by omega)⟩ : Fin n) hp
    simpa only [L3.EWord.siteZero] using hdone.2.1
  have hfirstB :
      ((bankWordEpochNext ring root z e).2.1
        (ring.rightNeighbor root)).ser.phase = .B := by
    by_cases hone : g.pivot = 1
    · have hfirst : e = ring.rightNeighbor root := by
        simpa [hone, L3.EWord.siteOne] using he
      rw [← hfirst, hsrcB]
    · have hlt : 1 < g.pivot := by omega
      have hfirstOld :
          (z.2.1 (ring.rightNeighbor root)).ser.phase = .B := by
        simpa only [L3.EWord.siteOne] using
          (hf.completed
            (⟨1, (show 1 < n by omega)⟩ : Fin n) hlt).1
      have hfirstFrame := L3.EWord.validationParentFrame
        ring root z.2.1 g.pivot e hf.pivotBound he
        1 (by omega : 1 < n) (by omega) (by omega)
      change ((phiW ring z.2.1 e)
        (ring.rightNeighbor root)).ser.phase = .B
      rw [← L3.EWord.siteOne, hfirstFrame]
      exact hfirstOld
  have hbase :
      BankWordRenewalFrontierTicketLineage ring root
        (bankWordEpochNext ring root z e) := by
    unfold BankWordRenewalFrontierTicketLineage
    refine ⟨?_, ?_, ?_⟩
    · intro h
      have hold : (z.2.1 root).ser.cert = .REQUESTED := by
        simpa only [hrootSer] using h
      rw [hactive.1] at hold
      cases hold
    · intro h
      have hwrong :
          ((bankWordEpochNext ring root z e).2.1 root).ser.out =
            .WAIT := h.2.2.2.1
      rw [hrootSer, hrootDone] at hwrong
      cases hwrong
    · intro h
      have hwrong :
          ((bankWordEpochNext ring root z e).2.1
            (ring.rightNeighbor root)).ser.phase = .F :=
          h.2.2.2.2
      rw [hfirstB] at hwrong
      cases hwrong
  have hno : (serW (z.2.1 e)
      (z.2.1 (ring.rightNeighbor e))).hard.hardAccept =
      false := L3.EWord.nonrootNoAccept
        (z.2.1 e) (z.2.1 (ring.rightNeighbor e)) hpost.1
  have hstart := L3.EWord.validationParentHardStartFalse
    ring root z.2.1 g e hshape hfixed
  have hghost := L3.EWord.validationGhostParentInternalEq
    ring root z.2.1 g e hstart hf.isForward he
    hb hw hc hi
  have hshapeNew :
      L3.EWord.ValidationShape ring root
        (bankWordEpochNext ring root z e).2.1
          { g with pivot := g.pivot + 1 } := by
    have ht := (L3.EWord.validationTransport
      (c := compileAdvice (ceilLogTwo n)) ring root)
      z.2.1 g e hshape hfixed hno
    rw [hghost] at ht
    exact ht
  have hfNew :
      L3.EWord.ForwardShape ring root
        (bankWordEpochNext ring root z e).2.1
          { g with pivot := g.pivot + 1 } := by
    rcases hshapeNew.stageShape with hF | hR
    · exact hF
    · have hwrong : ({ g with pivot := g.pivot + 1 }).stage =
          .forward := hf.isForward
      rw [hR.isReturn] at hwrong
      cases hwrong
  have hnewWave :
      BankWordRenewalFrontierWaveLineage ring root
        (bankWordEpochNext ring root z e) := by
    refine ⟨hbase, ?_⟩
    intro hactiveNew
    refine ⟨{ g with pivot := g.pivot + 1 }, req, stamp,
      hshapeNew, ?_⟩
    intro k hk
    by_cases hsrcIndex : k.val = g.pivot
    · have hsite : L3.EWord.site ring root k.val = e := by
        rw [hsrcIndex, ← he]
      have hindex : k = (⟨g.pivot, hpBound⟩ : Fin n) := by
        apply Fin.ext
        simpa only [Fin.val_mk] using hsrcIndex
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · intro h
        rw [hindex]
        simpa [Fin.val_mk, ← he, hsrcDone] using hsrcTicket
      · intro h
        have hwrong := h.1
        rw [hsite, hsrcB] at hwrong
        cases hwrong
      · intro h
        have hwrong := h.1
        rw [hsite, hsrcB] at hwrong
        cases hwrong
      · intro h
        have hwrong := h.1
        rw [hsite, hsrcB] at hwrong
        cases hwrong
      · intro h
        have hwrong := h.1
        rw [hsite, hsrcB] at hwrong
        cases hwrong
    · by_cases hdstIndex : k.val = g.pivot + 1
      · have hsite : L3.EWord.site ring root k.val =
            ring.rightNeighbor e := by
          rw [hdstIndex, ← hchildSite]
        have hindex : k =
            (⟨g.pivot + 1, hf.pivotBound⟩ : Fin n) := by
          apply Fin.ext
          simpa only [Fin.val_mk] using hdstIndex
        refine ⟨?_, ?_, ?_, ?_, ?_⟩
        · intro h
          rw [hindex]
          simpa [Fin.val_mk, ← hchildSite, hdstNew] using hdstTicket
        · intro h
          have hwrong := h.1
          rw [hsite, hdstB] at hwrong
          cases hwrong
        · intro h
          have hwrong := h.1
          rw [hsite, hdstB] at hwrong
          cases hwrong
        · intro h
          have hwrong := h.1
          rw [hsite, hdstB] at hwrong
          cases hwrong
        · intro h
          have hwrong := h.1
          rw [hsite, hdstB] at hwrong
          cases hwrong
      · have hsrcNe : L3.EWord.site ring root k.val ≠ e := by
          intro h
          have hsame : L3.EWord.site ring root k.val =
              L3.EWord.site ring root g.pivot := by
            rw [← he]
            exact h
          have heq := L3.EWord.validationSiteInjective
            ring root k.val g.pivot k.isLt hpBound hsame
          exact hsrcIndex heq
        have hdstNe : L3.EWord.site ring root k.val ≠
            ring.rightNeighbor e := by
          intro h
          have hsame : L3.EWord.site ring root k.val =
              L3.EWord.site ring root (g.pivot + 1) := by
            rw [← hchildSite]
            exact h
          have heq := L3.EWord.validationSiteInjective
            ring root k.val (g.pivot + 1) k.isLt
            hf.pivotBound hsame
          exact hdstIndex heq
        have hser :
            ((bankWordEpochNext ring root z e).2.1
              (L3.EWord.site ring root k.val)).ser =
            (z.2.1 (L3.EWord.site ring root k.val)).ser := by
          change ((phiW ring z.2.1 e)
            (L3.EWord.site ring root k.val)).ser =
            (z.2.1 (L3.EWord.site ring root k.val)).ser
          exact phiW_ser_remote ring z.2.1 e
            (L3.EWord.site ring root k.val) hsrcNe hdstNe
        have ht := bankWordRenewalFrontierWaveTicketRemoteFrame
          ring root z e (L3.EWord.site ring root k.val)
          hsrcNe hdstNe
        obtain ⟨hB, hP, hI, hL, hF⟩ := hsites k hk
        refine ⟨?_, ?_, ?_, ?_, ?_⟩
        · intro h
          have htOld := hB (by simpa only [hser] using h)
          simpa only [BankWordRenewalFrontierWaveSiteTicket,
            hser, ht] using htOld
        · intro h
          have htOld := hP (by simpa only [hser] using h)
          simpa only [BankWordRenewalFrontierWaveSiteTicket,
            hser, ht] using htOld
        · intro h
          have htOld := hI (by simpa only [hser] using h)
          simpa only [BankWordRenewalFrontierWaveSiteTicket,
            hser, ht] using htOld
        · intro h
          have htOld := hL (by simpa only [hser] using h)
          simpa only [BankWordRenewalFrontierWaveSiteTicket,
            hser, ht] using htOld
        · intro h
          have hbelow : k.val < g.pivot := by
            have hkScrub : k.val < g.scrub := hk
            have hkPivot : k.val < g.pivot + 2 := by
              rw [hscrub] at hkScrub
              exact hkScrub
            omega
          have hdone := (hf.completed k hbelow).1
          have hphase :
              (z.2.1 (L3.EWord.site ring root k.val)).ser.phase =
                .F := by
            simpa only [hser] using h.1
          rw [hphase] at hdone
          cases hdone
  refine ⟨hnewWave, ?_⟩
  intro hactiveNew gnew hreturn k hk hc
  exact False.elim (bankWordRenewalWaveForwardExcludesReturnStage
    ring root (bankWordEpochNext ring root z e).2.1
    { g with pivot := g.pivot + 1 } gnew hfNew hreturn)

end

section
open Classical

/-- Width port of `bankWordRenewalWaveInternalFrontierLeafQuietStep`: the BANK band premise is replaced by `5 ≤ n`, and the renewal constants are those of the compiled width t (lease 8t+4, quota 2t+1). Consumer: `widthWordRenewalWaveInternalFrontierParentQuietStep`. -/
theorem widthWordRenewalWaveInternalFrontierLeafQuietStep {n : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hn : 5 ≤ n)
    (hsmallFive : 5 ≤ n)
    (hs : WidthWordSerializerRootClass ring hsmallFive root s)
    (z : BankWordEpochState n)
    (hz : BankWordEpochReachable ring root s z)
    (hwave : BankWordRenewalFrontierWaveLineageQuiet ring root z)
    (hactive : (z.2.1 root).ser.cert = .RUNNING ∧
      (z.2.1 root).ser.wphase = .VALIDATING)
    (g : L3.EWord.ValidationGhost)
    (hg : g = Classical.choose (hwave.wave.2 hactive))
    (hf : L3.EWord.ForwardShape ring root z.2.1 g)
    (he : e = L3.EWord.site ring root g.pivot)
    (hw : (z.2.1 e).ser.out = .WAIT)
    (hc : (z.2.1 (ring.rightNeighbor e)).ser.phase = .C)
    (hl : (z.2.1 (ring.rightNeighbor e)).ser.probe =
      .LEAF_OK) :
    BankWordRenewalFrontierWaveLineageQuiet ring root
      (bankWordEpochNext ring root z e) := by
  have hspec := Classical.choose_spec (hwave.wave.2 hactive)
  rw [← hg] at hspec
  obtain ⟨req, stamp, hshape, hsites⟩ := hspec
  have hparentWait :
      (z.2.1 (L3.EWord.site ring root g.pivot)).ser.out =
        .WAIT := by rw [← he]; exact hw
  have hchildSite : ring.rightNeighbor e =
      L3.EWord.site ring root (g.pivot + 1) :=
    L3.EWord.validationParentNeighbor ring root g.pivot e he
  have hchildProbe :
      (z.2.1 (L3.EWord.site ring root (g.pivot + 1))).ser.probe =
        .LEAF_OK := by
    rw [← hchildSite]
    exact hl
  have hleafWitness := L3.EWord.validationFrontierWaitLeafWitness
    ring root z.2.1 g hf hparentWait hchildProbe
  have hscrub : g.scrub = g.pivot + 2 := hleafWitness.1
  have hlast : g.pivot + 2 = n := hleafWitness.2.1
  have hchildOff :
      (z.2.1 (ring.rightNeighbor e)).ser.wphase = .OFF := by
    rw [hchildSite]
    exact hleafWitness.2.2
  have hpBound : g.pivot < n := by
    have ht := hf.pivotBound
    omega
  have hpPositive : 0 < g.pivot := by omega
  have hpBeyondFirst : 1 < g.pivot := by
    have ht := hn
    omega
  have hb : (z.2.1 e).ser.phase = .B := by
    rw [he]
    exact hf.parentB
  have hv : (z.2.1 e).ser.wphase = .VALIDATING := by
    rw [he]
    exact hf.parentValidating
  have holdSource :
      BankWordRenewalFrontierWaveSiteTicket ring root z
        req stamp (⟨g.pivot, hpBound⟩ : Fin n) .waiting := by
    have hk : g.pivot < g.scrub := by rw [hscrub]; omega
    have ht := (hsites
      (⟨g.pivot, hpBound⟩ : Fin n)
      (by simpa only [Fin.val_mk] using hk)).1
      ⟨by simpa only [Fin.val_mk] using hf.parentB,
       by simpa only [Fin.val_mk] using hf.parentValidating⟩
    simpa [Fin.val_mk, hparentWait] using ht
  have holdChild :
      BankWordRenewalFrontierWaveSiteTicket ring root z
        req stamp (⟨g.pivot + 1, hf.pivotBound⟩ : Fin n)
        .observedLeaf := by
    have hk : g.pivot + 1 < g.scrub := by rw [hscrub]; omega
    exact (hsites
      (⟨g.pivot + 1, hf.pivotBound⟩ : Fin n)
      (by simpa only [Fin.val_mk] using hk)).2.2.2.1
      ⟨by simpa only [Fin.val_mk, ← hchildSite] using hc,
       by simpa only [Fin.val_mk, ← hchildSite] using hl⟩
  obtain ⟨parent, htParent, hpReq, hpStamp⟩ := holdSource
  obtain ⟨child, htChild, hcReq, hcStamp⟩ := holdChild
  have htParentAtE :
      wTicketAt .waiting
        ((bankWordHardEpochLedger ring root z).validation e) =
          some parent := by
    rw [he]
    simpa only [Fin.val_mk] using htParent
  have htChildAtResp :
      wTicketAt .observedLeaf
        ((bankWordHardEpochLedger ring root z).validation
          (ring.rightNeighbor e)) = some child := by
    rw [hchildSite]
    simpa only [Fin.val_mk] using htChild
  have heNotRoot : e ≠ root := by
    rw [he]
    exact L3.EWord.validationPositiveSiteNotRoot
      ring root g.pivot hpBound hpPositive
  have htargetNotRoot : ring.rightNeighbor e ≠ root := by
    rw [hchildSite]
    exact L3.EWord.validationPositiveSiteNotRoot
      ring root (g.pivot + 1) hf.pivotBound (by omega)
  have hclass := widthWordEpochReachablePhysicalRootClass
    ring hn hsmallFive root s hs z hz
  have hfixed : WFixedRoot ring root (phiW ring z.2.1 e) :=
    ((widthWordSerializerRootClassClosed ring hn hsmallFive root).2
      z.2.1 hclass e).2
  have hpost := clockPostInternal ring root z.2.1 e
    (by omega : 2 ≤ n) hfixed heNotRoot htargetNotRoot
  have hpairSer := L3.EWord.validationParentLeafWrite
    (z.2.1 e) (z.2.1 (ring.rightNeighbor e))
    hpost.2 (by intro h; rw [hpost.1] at h; cases h)
    hb hw hc hl
  have hrow :
      (bankWordEpochSelectedReceipt ring z e).serializer.row =
        "S2N" := by
    change (serW (z.2.1 e)
      (z.2.1 (ring.rightNeighbor e))).row = "S2N"
    simp [serW, serializerStep, ProjW.lift,
      hpost.1, hpost.2, hb]
  have hjoined := bankWordRenewalWaveInternalLeafTicketStep
    ring root e z (by omega : 2 ≤ n) parent child
    hrow hw hc hl htParentAtE htChildAtResp
    (hpReq.trans hcReq.symm) (hpStamp.trans hcStamp.symm)
  have hne : ring.rightNeighbor e ≠ e :=
    clockNeighborDifferent ring (by omega : 2 ≤ n) e
  have hsrcSer :
      ((bankWordEpochNext ring root z e).2.1 e).ser =
        { (z.2.1 e).ser with out := .DONE } := by
    change ((phiW ring z.2.1 e) e).ser =
      { (z.2.1 e).ser with out := .DONE }
    rw [phiW_ser_source]
    exact hpairSer.1
  have hdstSer :
      ((bankWordEpochNext ring root z e).2.1
        (ring.rightNeighbor e)).ser =
        { (z.2.1 (ring.rightNeighbor e)).ser with
          phase := .F, probe := .NONE } := by
    change ((phiW ring z.2.1 e)
      (ring.rightNeighbor e)).ser =
        { (z.2.1 (ring.rightNeighbor e)).ser with
          phase := .F, probe := .NONE }
    rw [phiW_ser_target ring z.2.1 e hne]
    exact hpairSer.2
  have hsrcB :
      ((bankWordEpochNext ring root z e).2.1 e).ser.phase = .B := by
    rw [hsrcSer]
    exact hb
  have hsrcDone :
      ((bankWordEpochNext ring root z e).2.1 e).ser.out = .DONE := by
    rw [hsrcSer]
  have hdstF :
      ((bankWordEpochNext ring root z e).2.1
        (ring.rightNeighbor e)).ser.phase = .F := by
    rw [hdstSer]
  have hsrcTicket :
      BankWordRenewalFrontierWaveSiteTicket ring root
        (bankWordEpochNext ring root z e) req stamp
        (⟨g.pivot, hpBound⟩ : Fin n) .done := by
    unfold BankWordRenewalFrontierWaveSiteTicket
    refine ⟨{ parent with stage := .done }, ?_, hpReq, hpStamp⟩
    simp only [Fin.val_mk, ← he, hjoined.1, wTicketAt]
    rfl
  have hdstTicket :
      BankWordRenewalFrontierWaveSiteTicket ring root
        (bankWordEpochNext ring root z e) req stamp
        (⟨g.pivot + 1, hf.pivotBound⟩ : Fin n)
        .returned := by
    unfold BankWordRenewalFrontierWaveSiteTicket
    refine ⟨{ parent with stage := .returned }, ?_, hpReq, hpStamp⟩
    simp only [Fin.val_mk, ← hchildSite, hjoined.2, wTicketAt]
    rfl
  have hrootSer :
      ((bankWordEpochNext ring root z e).2.1 root).ser =
        (z.2.1 root).ser := by
    change ((phiW ring z.2.1 e) root).ser =
      (z.2.1 root).ser
    exact phiW_ser_remote ring z.2.1 e root
      heNotRoot.symm htargetNotRoot.symm
  have hrootDone : (z.2.1 root).ser.out = .DONE := by
    have hdone := hf.completed
      (⟨0, (show 0 < n by omega)⟩ : Fin n) hpPositive
    simpa only [L3.EWord.siteZero] using hdone.2.1
  have hfirstOldB :
      (z.2.1 (ring.rightNeighbor root)).ser.phase = .B := by
    simpa only [L3.EWord.siteOne] using
      (hf.completed
        (⟨1, (show 1 < n by omega)⟩ : Fin n) hpBeyondFirst).1
  have hfirstFrame := L3.EWord.validationParentFrame
    ring root z.2.1 g.pivot e hf.pivotBound he
    1 (by omega : 1 < n) (by omega) (by omega)
  have hfirstB :
      ((bankWordEpochNext ring root z e).2.1
        (ring.rightNeighbor root)).ser.phase = .B := by
    change ((phiW ring z.2.1 e)
      (ring.rightNeighbor root)).ser.phase = .B
    rw [← L3.EWord.siteOne, hfirstFrame]
    exact hfirstOldB
  have hbase :
      BankWordRenewalFrontierTicketLineage ring root
        (bankWordEpochNext ring root z e) := by
    unfold BankWordRenewalFrontierTicketLineage
    refine ⟨?_, ?_, ?_⟩
    · intro h
      have hold : (z.2.1 root).ser.cert = .REQUESTED := by
        simpa only [hrootSer] using h
      rw [hactive.1] at hold
      cases hold
    · intro h
      have hwrong :
          ((bankWordEpochNext ring root z e).2.1 root).ser.out =
            .WAIT := h.2.2.2.1
      rw [hrootSer, hrootDone] at hwrong
      cases hwrong
    · intro h
      have hwrong :
          ((bankWordEpochNext ring root z e).2.1
            (ring.rightNeighbor root)).ser.phase = .F :=
          h.2.2.2.2
      rw [hfirstB] at hwrong
      cases hwrong
  have hno : (serW (z.2.1 e)
      (z.2.1 (ring.rightNeighbor e))).hard.hardAccept =
      false := L3.EWord.nonrootNoAccept
        (z.2.1 e) (z.2.1 (ring.rightNeighbor e)) hpost.1
  have hstart := L3.EWord.validationParentHardStartFalse
    ring root z.2.1 g e hshape hfixed
  have hghost := L3.EWord.validationGhostParentLeafEq
    ring root z.2.1 g e hstart hf.isForward he
    hb hw hc hl
  have hshapeNew :
      L3.EWord.ValidationShape ring root
        (bankWordEpochNext ring root z e).2.1
          { g with stage := .returning, pivot := g.pivot + 1 } := by
    have ht := (L3.EWord.validationTransport
      (c := compileAdvice (ceilLogTwo n)) ring root)
      z.2.1 g e hshape hfixed hno
    rw [hghost] at ht
    exact ht
  have hrNew :
      L3.EWord.ReturnShape ring root
        (bankWordEpochNext ring root z e).2.1
          { g with stage := .returning, pivot := g.pivot + 1 } := by
    rcases hshapeNew.stageShape with hF | hR
    · have hwrong : L3.EWord.ValidationStage.returning =
          .forward := by
        simpa only using hF.isForward
      cases hwrong
    · exact hR
  have hnewWave :
      BankWordRenewalFrontierWaveLineage ring root
        (bankWordEpochNext ring root z e) := by
    refine ⟨hbase, ?_⟩
    intro hactiveNew
    refine ⟨{ g with stage := .returning, pivot := g.pivot + 1 },
      req, stamp, hshapeNew, ?_⟩
    intro k hk
    by_cases hsrcIndex : k.val = g.pivot
    · have hsite : L3.EWord.site ring root k.val = e := by
        rw [hsrcIndex, ← he]
      have hindex : k = (⟨g.pivot, hpBound⟩ : Fin n) := by
        apply Fin.ext
        simpa only [Fin.val_mk] using hsrcIndex
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · intro h
        rw [hindex]
        simpa [Fin.val_mk, ← he, hsrcDone] using hsrcTicket
      · intro h
        have hwrong := h.1
        rw [hsite, hsrcB] at hwrong
        cases hwrong
      · intro h
        have hwrong := h.1
        rw [hsite, hsrcB] at hwrong
        cases hwrong
      · intro h
        have hwrong := h.1
        rw [hsite, hsrcB] at hwrong
        cases hwrong
      · intro h
        have hwrong := h.1
        rw [hsite, hsrcB] at hwrong
        cases hwrong
    · by_cases hdstIndex : k.val = g.pivot + 1
      · have hsite : L3.EWord.site ring root k.val =
            ring.rightNeighbor e := by
          rw [hdstIndex, ← hchildSite]
        have hindex : k =
            (⟨g.pivot + 1, hf.pivotBound⟩ : Fin n) := by
          apply Fin.ext
          simpa only [Fin.val_mk] using hdstIndex
        refine ⟨?_, ?_, ?_, ?_, ?_⟩
        · intro h
          have hwrong := h.1
          rw [hsite, hdstF] at hwrong
          cases hwrong
        · intro h
          have hwrong := h.1
          rw [hsite, hdstF] at hwrong
          cases hwrong
        · intro h
          have hwrong := h.1
          rw [hsite, hdstF] at hwrong
          cases hwrong
        · intro h
          have hwrong := h.1
          rw [hsite, hdstF] at hwrong
          cases hwrong
        · intro h
          rw [hindex]
          exact hdstTicket
      · have hsrcNe : L3.EWord.site ring root k.val ≠ e := by
          intro h
          have hsame : L3.EWord.site ring root k.val =
              L3.EWord.site ring root g.pivot := by
            rw [← he]
            exact h
          have heq := L3.EWord.validationSiteInjective
            ring root k.val g.pivot k.isLt hpBound hsame
          exact hsrcIndex heq
        have hdstNe : L3.EWord.site ring root k.val ≠
            ring.rightNeighbor e := by
          intro h
          have hsame : L3.EWord.site ring root k.val =
              L3.EWord.site ring root (g.pivot + 1) := by
            rw [← hchildSite]
            exact h
          have heq := L3.EWord.validationSiteInjective
            ring root k.val (g.pivot + 1) k.isLt
            hf.pivotBound hsame
          exact hdstIndex heq
        have hser :
            ((bankWordEpochNext ring root z e).2.1
              (L3.EWord.site ring root k.val)).ser =
            (z.2.1 (L3.EWord.site ring root k.val)).ser := by
          change ((phiW ring z.2.1 e)
            (L3.EWord.site ring root k.val)).ser =
            (z.2.1 (L3.EWord.site ring root k.val)).ser
          exact phiW_ser_remote ring z.2.1 e
            (L3.EWord.site ring root k.val) hsrcNe hdstNe
        have ht := bankWordRenewalFrontierWaveTicketRemoteFrame
          ring root z e (L3.EWord.site ring root k.val)
          hsrcNe hdstNe
        obtain ⟨hB, hP, hI, hL, hF⟩ := hsites k hk
        refine ⟨?_, ?_, ?_, ?_, ?_⟩
        · intro h
          have hold := hB (by simpa only [hser] using h)
          simpa only [BankWordRenewalFrontierWaveSiteTicket, hser, ht] using hold
        · intro h
          have hold := hP (by simpa only [hser] using h)
          simpa only [BankWordRenewalFrontierWaveSiteTicket, hser, ht] using hold
        · intro h
          have hold := hI (by simpa only [hser] using h)
          simpa only [BankWordRenewalFrontierWaveSiteTicket, hser, ht] using hold
        · intro h
          have hold := hL (by simpa only [hser] using h)
          simpa only [BankWordRenewalFrontierWaveSiteTicket, hser, ht] using hold
        · intro h
          have hbelow : k.val < g.pivot := by
            have hkN : k.val < n := k.isLt
            have hlastN : g.pivot + 2 = n := hlast
            omega
          have hdone := (hf.completed k hbelow).1
          have hphase : (z.2.1 (L3.EWord.site ring root k.val)).ser.phase = .F := by
            simpa only [hser] using h.1
          rw [hphase] at hdone
          cases hdone
  refine ⟨hnewWave, ?_⟩
  intro hactiveNew gnew hreturn k hk hc
  have hpivot := bankWordRenewalWaveReturnPivotUnique
    ring root (bankWordEpochNext ring root z e).2.1
    { g with stage := .returning, pivot := g.pivot + 1 }
    gnew hrNew hreturn
  have hlastPivot : gnew.pivot + 1 = n := by
    have hq : gnew.pivot = g.pivot + 1 := hpivot.symm
    omega
  have hlt := k.isLt
  omega

end

section
open Classical

/-- Width port of `bankWordRenewalWaveSelectedRemoteQuietStep`: the BANK band premise is replaced by `5 ≤ n`, and the renewal constants are those of the compiled width t (lease 8t+4, quota 2t+1). Consumer: `widthWordRenewalWaveInternalChildPrechallengeQuietStep`.
 Any selected internal edge that is physically remote from
the whole scrubbed prefix preserves the actual five-clause
ticket genealogy. This is stronger than the priority-named
unvisitedSuffix class and is needed by the pre-challenge
challengedChild edge when its inherited C/B/F bytes are outside
the scrub. Consumer: forward challengedChild NEW case. -/
theorem widthWordRenewalWaveSelectedRemoteQuietStep {n : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hn : 5 ≤ n)
    (hsmallFive : 5 ≤ n)
    (hs : WidthWordSerializerRootClass ring hsmallFive root s)
    (z : BankWordEpochState n)
    (hz : BankWordEpochReachable ring root s z)
    (he : e ≠ root)
    (hj : ring.rightNeighbor e ≠ root)
    (hwave : BankWordRenewalFrontierWaveLineageQuiet ring root z)
    (hactive : (z.2.1 root).ser.cert = .RUNNING ∧
      (z.2.1 root).ser.wphase = .VALIDATING)
    (g : L3.EWord.ValidationGhost)
    (hg : g = Classical.choose (hwave.wave.2 hactive))
    (hremote : ∀ i : Fin n, i.val < g.scrub →
      L3.EWord.site ring root i.val ≠ e ∧
      L3.EWord.site ring root i.val ≠ ring.rightNeighbor e) :
    BankWordRenewalFrontierWaveLineageQuiet ring root
      (bankWordEpochNext ring root z e) := by
  have hspec := Classical.choose_spec (hwave.wave.2 hactive)
  rw [← hg] at hspec
  obtain ⟨req, stamp, hshape, hsites⟩ := hspec
  have hrootSafe := hremote
    (⟨0, (show 0 < n by omega)⟩ : Fin n)
    (by simp only [Fin.val_mk]; exact Nat.lt_of_lt_of_le (by omega : 0 < 2) hshape.lower)
  have hfirstSafe := hremote
    (⟨1, (show 1 < n by omega)⟩ : Fin n)
    (by have := hshape.lower; simp only [Fin.val_mk]; omega)
  have hchildSafe :
      ring.rightNeighbor root ≠ e ∧
      ring.rightNeighbor root ≠ ring.rightNeighbor e := by
    simpa only [Fin.val_mk, L3.EWord.siteOne] using
      hfirstSafe
  have hbase := bankWordRenewalFrontierTicketLineageRemoteStep
    ring root e z he hj hchildSafe.1.symm
      hchildSafe.2.symm hwave.wave.1
  have hf : L3.EWord.ForwardShape ring root z.2.1 g := by
    rcases hshape.stageShape with hf | hr
    · exact hf
    · have hoff := L3.EWord.validationOffsetBound ring root e
      have hloc := L3.EWord.validationOffsetRepresentative
        ring root e
      have hs := (hremote
        (⟨PPL.cyclicOffset ring root e, hoff⟩ : Fin n)
        (by simp only [Fin.val_mk]; rw [hr.covered]; exact hoff)).1
      exact False.elim (hs hloc)
  have hclass := widthWordEpochReachablePhysicalRootClass
    ring hn hsmallFive root s hs z hz
  have hfixed : WFixedRoot ring root
      (phiW ring z.2.1 e) :=
    ((widthWordSerializerRootClassClosed ring hn hsmallFive root).2
      z.2.1 hclass e).2
  have hno := widthWordRootNonrootHardAcceptFalse
    ring hn hsmallFive root s hs z hz e he
  have hghost := L3.EWord.unvisitedSuffixGhostUnchanged
    ring root z.2.1 g e hshape hremote
  have hshapeNew :
      L3.EWord.ValidationShape ring root
        (bankWordEpochNext ring root z e).2.1 g := by
    have ht := (L3.EWord.validationTransport
      (c := compileAdvice (ceilLogTwo n)) ring root)
      z.2.1 g e hshape hfixed hno
    rw [hghost] at ht
    exact ht
  have hnewWave :
      BankWordRenewalFrontierWaveLineage ring root
        (bankWordEpochNext ring root z e) := by
    refine ⟨hbase, ?_⟩
    intro hactiveNew
    refine ⟨g, req, stamp, hshapeNew, ?_⟩
    intro k hk
    have hsafe := hremote k hk
    have hsiteSer :
        ((bankWordEpochNext ring root z e).2.1
          (L3.EWord.site ring root k.val)).ser =
        (z.2.1 (L3.EWord.site ring root k.val)).ser := by
      change ((phiW ring z.2.1 e)
        (L3.EWord.site ring root k.val)).ser =
        (z.2.1 (L3.EWord.site ring root k.val)).ser
      exact phiW_ser_remote ring z.2.1 e
        (L3.EWord.site ring root k.val) hsafe.1 hsafe.2
    have hsiteTicket :=
      bankWordRenewalFrontierWaveTicketRemoteFrame
        ring root z e (L3.EWord.site ring root k.val)
        hsafe.1 hsafe.2
    simpa only [BankWordRenewalFrontierWaveSiteTicket,
      hsiteSer, hsiteTicket] using hsites k hk
  refine ⟨hnewWave, ?_⟩
  intro hactiveNew gnew hrnew k hk hc
  have hfNew : L3.EWord.ForwardShape ring root
      (bankWordEpochNext ring root z e).2.1 g := by
    rcases hshapeNew.stageShape with hforward | hreturn
    · exact hforward
    · have hbad := hreturn.isReturn
      rw [hf.isForward] at hbad
      cases hbad
  exact False.elim (bankWordRenewalWaveForwardExcludesReturnStage
    ring root (bankWordEpochNext ring root z e).2.1
    g gnew hfNew hrnew)

end

section
open Classical

/-- Width port of `bankWordRenewalWaveInternalChildPrechallengeQuietStep`: the BANK band premise is replaced by `5 ≤ n`, and the renewal constants are those of the compiled width t (lease 8t+4, quota 2t+1). Consumer: `widthWordRenewalWaveInternalChallengedChildQuietStep`.
 When the FORWARD parent has not yet challenged its child,
the physical child-service pair lies entirely outside the
causal scrubbed prefix. Unlike its priority classification as
challengedChild, it cannot alter any historical W ticket or
RETURN quiet obligation of the active prefix.
Consumer: challengedChild B/NEW subcase of R10a J-W. -/
theorem widthWordRenewalWaveInternalChildPrechallengeQuietStep {n : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hn : 5 ≤ n)
    (hsmallFive : 5 ≤ n)
    (hs : WidthWordSerializerRootClass ring hsmallFive root s)
    (z : BankWordEpochState n)
    (hz : BankWordEpochReachable ring root s z)
    (hwave : BankWordRenewalFrontierWaveLineageQuiet ring root z)
    (hactive : (z.2.1 root).ser.cert = .RUNNING ∧
      (z.2.1 root).ser.wphase = .VALIDATING)
    (g : L3.EWord.ValidationGhost)
    (hg : g = Classical.choose (hwave.wave.2 hactive))
    (hf : L3.EWord.ForwardShape ring root z.2.1 g)
    (he : e = L3.EWord.site ring root (g.pivot + 1))
    (hnew : (z.2.1 (L3.EWord.site ring root g.pivot)).ser.out =
      .NEW)
    (hj : ring.rightNeighbor e ≠ root) :
    BankWordRenewalFrontierWaveLineageQuiet ring root
      (bankWordEpochNext ring root z e) := by
  have hspec := Classical.choose_spec (hwave.wave.2 hactive)
  rw [← hg] at hspec
  obtain ⟨req, stamp, hshape, hsites⟩ := hspec
  have hsc := (L3.EWord.validationFrontierNewObligation
    ring root z.2.1 g hf hnew).2
  have hnotSeam : e ≠ L3.EWord.site ring root (n - 1) := by
    intro hseam
    exact hj (L3.EWord.validationSeamNeighbor
      ring root e hseam)
  have hbound : g.pivot + 2 < n :=
    L3.EWord.validationChildNoSeamBound
      ring root g.pivot e (by omega : 3 ≤ n)
      hf.pivotBound he hnotSeam
  have htarget : ring.rightNeighbor e =
      L3.EWord.site ring root (g.pivot + 2) :=
    L3.EWord.validationChildNeighbor ring root g.pivot e he
  have heNotRoot : e ≠ root :=
    L3.EWord.validationChildNotRoot
      ring root g.pivot e (by omega : 3 ≤ n)
      hf.pivotBound he
  have hremote : ∀ k : Fin n, k.val < g.scrub →
      L3.EWord.site ring root k.val ≠ e ∧
      L3.EWord.site ring root k.val ≠ ring.rightNeighbor e := by
    intro k hk
    have hklt : k.val < g.pivot + 1 := by
      rw [hsc] at hk
      exact hk
    constructor
    · intro h
      have hsame :
          L3.EWord.site ring root k.val =
            L3.EWord.site ring root (g.pivot + 1) := by
        rw [← he]
        exact h
      have hbad := L3.EWord.validationSiteInjective
        ring root k.val (g.pivot + 1)
        k.isLt hf.pivotBound hsame
      omega
    · intro h
      have hsame :
          L3.EWord.site ring root k.val =
            L3.EWord.site ring root (g.pivot + 2) := by
        rw [← htarget]
        exact h
      have hbad := L3.EWord.validationSiteInjective
        ring root k.val (g.pivot + 2)
        k.isLt hbound hsame
      omega
  exact widthWordRenewalWaveSelectedRemoteQuietStep
    ring root e s hn hsmallFive hs z hz heNotRoot hj
    hwave hactive g hg hremote

end

section
open Classical

/-- Width port of `bankWordRenewalWaveInternalFrontierParentQuietStep`: the BANK band premise is replaced by `5 ≤ n`, and the renewal constants are those of the compiled width t (lease 8t+4, quota 2t+1). Consumer: `widthWordRenewalWaveSelectedInternalMovingQuietStep`.
 The genuine moving FORWARD parent serves exactly one of the
three chronological S2N obligations: NEW starts a child, WAIT
with PENDING frames, WAIT/INTERNAL_OK admits the next B, or
WAIT/LEAF_OK starts RETURN. The actual old validation ticket
stages select the admission witnesses.
Consumer: INTERNAL moving frontierParent in R10a J-W. -/
theorem widthWordRenewalWaveInternalFrontierParentQuietStep {n : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hn : 5 ≤ n)
    (hsmallFive : 5 ≤ n)
    (hs : WidthWordSerializerRootClass ring hsmallFive root s)
    (z : BankWordEpochState n)
    (hz : BankWordEpochReachable ring root s z)
    (he : e ≠ root)
    (hj : ring.rightNeighbor e ≠ root)
    (hwave : BankWordRenewalFrontierWaveLineageQuiet ring root z)
    (hactive : (z.2.1 root).ser.cert = .RUNNING ∧
      (z.2.1 root).ser.wphase = .VALIDATING)
    (g : L3.EWord.ValidationGhost)
    (hg : g = Classical.choose (hwave.wave.2 hactive))
    (hf : L3.EWord.ForwardShape ring root z.2.1 g)
    (hparent : e = L3.EWord.site ring root g.pivot) :
    BankWordRenewalFrontierWaveLineageQuiet ring root
      (bankWordEpochNext ring root z e) := by
  have hpositive : 0 < g.pivot := by
    by_cases hz : g.pivot = 0
    · have hroot : e = root := by
        rw [hparent, hz, L3.EWord.siteZero]
      exact False.elim (he hroot)
    · omega
  have hchildSite : ring.rightNeighbor e =
      L3.EWord.site ring root (g.pivot + 1) :=
    L3.EWord.validationParentNeighbor ring root g.pivot e hparent
  have hb : (z.2.1 e).ser.phase = .B := by
    rw [hparent]
    exact hf.parentB
  rcases hf.currentObligation with hnew | hwait
  · have hnewOut : (z.2.1 e).ser.out = .NEW := by
      rw [hparent]
      exact hnew.2.1
    exact widthWordRenewalWaveInternalFrontierNewQuietStep
      ring root e s hn hsmallFive hs z hz hwave hactive
      g hg hf.isForward hparent hnewOut
  · have hw : (z.2.1 e).ser.out = .WAIT := by
      rw [hparent]
      exact hwait.1
    have hc : (z.2.1 (ring.rightNeighbor e)).ser.phase =
        .C := by
      rw [hchildSite]
      exact hwait.2.2.1
    rcases hwait.2.2.2 with hpend | hinter | hleaf
    · have hp : (z.2.1 (ring.rightNeighbor e)).ser.probe =
          .PENDING := by
        rw [hchildSite]
        exact hpend.1
      exact widthWordRenewalWaveInternalPendingQuietStep
        ring root e s hn hsmallFive hs z hz he hj hwave
        hb hw hc hp
    · have hi : (z.2.1 (ring.rightNeighbor e)).ser.probe =
          .INTERNAL_OK := by
        rw [hchildSite]
        exact hinter.2.1
      exact widthWordRenewalWaveInternalFrontierInternalQuietStep
        ring root e s hn hsmallFive hs z hz hwave hactive
        g hg hf hpositive hparent hw hc hi
    · have hl : (z.2.1 (ring.rightNeighbor e)).ser.probe =
          .LEAF_OK := by
        rw [hchildSite]
        exact hleaf.2.1
      exact widthWordRenewalWaveInternalFrontierLeafQuietStep
        ring root e s hn hsmallFive hs z hz hwave hactive
        g hg hf hparent hw hc hl

end

section
open Classical

/-- Width port of `bankWordRenewalWaveInternalChallengedChildQuietStep`: the BANK band premise is replaced by `5 ≤ n`, and the renewal constants are those of the compiled width t (lease 8t+4, quota 2t+1). Consumer: `widthWordRenewalWaveSelectedInternalMovingQuietStep`.
 FORWARD challengedChild updates are either causally
pre-challenge remote (parent NEW), S3 observation of a
PENDING child seeing a C responder, or nonpending C
stationary/canonical cleanup. The responder's literal
B/C/F phase supplies the exhaustive selected-row split.
Consumer: INTERNAL challengedChild case of R10a J-W. -/
theorem widthWordRenewalWaveInternalChallengedChildQuietStep {n : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hn : 5 ≤ n)
    (hsmallFive : 5 ≤ n)
    (hs : WidthWordSerializerRootClass ring hsmallFive root s)
    (z : BankWordEpochState n)
    (hz : BankWordEpochReachable ring root s z)
    (he : e ≠ root)
    (hj : ring.rightNeighbor e ≠ root)
    (hwave : BankWordRenewalFrontierWaveLineageQuiet ring root z)
    (hactive : (z.2.1 root).ser.cert = .RUNNING ∧
      (z.2.1 root).ser.wphase = .VALIDATING)
    (g : L3.EWord.ValidationGhost)
    (hg : g = Classical.choose (hwave.wave.2 hactive))
    (hf : L3.EWord.ForwardShape ring root z.2.1 g)
    (hchild : e = L3.EWord.site ring root (g.pivot + 1)) :
    BankWordRenewalFrontierWaveLineageQuiet ring root
      (bankWordEpochNext ring root z e) := by
  have hnotSeam :
      e ≠ L3.EWord.site ring root (n - 1) := by
    intro hs
    exact hj (L3.EWord.validationSeamNeighbor
      ring root e hs)
  have hbound : g.pivot + 2 < n :=
    L3.EWord.validationChildNoSeamBound ring root g.pivot e
      (by omega : 3 ≤ n) hf.pivotBound hchild hnotSeam
  have hparentWait :
      (z.2.1 (L3.EWord.site ring root g.pivot)).ser.out =
        .WAIT →
      (z.2.1 e).ser.phase = .C := by
    intro hwait
    have hpc := (L3.EWord.validationFrontierWaitObligation
      ring root z.2.1 g hf hwait).2
    exact (by rw [hchild]; exact hpc.1)
  rcases hf.currentObligation with hnew | hwait
  · exact widthWordRenewalWaveInternalChildPrechallengeQuietStep
      ring root e s hn hsmallFive hs z hz hwave hactive
      g hg hf hchild hnew.2.1 hj
  · have hsourceC : (z.2.1 e).ser.phase = .C :=
      hparentWait hwait.1
    have hpc := hwait.2.2
    rcases hpc.2 with hpend | hinter | hleaf
    · have hp : (z.2.1 e).ser.probe = .PENDING := by
        rw [hchild]
        exact hpend.1
      cases htarget :
          (z.2.1 (ring.rightNeighbor e)).ser.phase with
      | B =>
          exact widthWordRenewalWaveInternalCanonicalQuietStep
            ring root e s hn hsmallFive hs z hz hwave he hj
            (Or.inl hsourceC) (Or.inl htarget)
      | C =>
          exact widthWordRenewalWaveInternalObservedChildQuietStep
            ring root e s hn hsmallFive hs z hz hwave hactive
            g hg hf.isForward hchild hbound hwait.1
            hsourceC hp htarget
      | F =>
          exact widthWordRenewalWaveInternalCanonicalQuietStep
            ring root e s hn hsmallFive hs z hz hwave he hj
            (Or.inl hsourceC) (Or.inr htarget)
    · have hi : (z.2.1 e).ser.probe = .INTERNAL_OK := by
        rw [hchild]
        exact hinter.2.1
      have hnotPending :
          (z.2.1 e).ser.probe ≠ .PENDING := by
        rw [hi]
        decide
      cases htarget :
          (z.2.1 (ring.rightNeighbor e)).ser.phase with
      | B =>
          exact widthWordRenewalWaveInternalCanonicalQuietStep
            ring root e s hn hsmallFive hs z hz hwave he hj
            (Or.inl hsourceC) (Or.inl htarget)
      | C =>
          exact widthWordRenewalWaveInternalNonBToCQuietStep
            ring root e s hn hsmallFive hs z hz he hj hwave
            (Or.inr ⟨hsourceC, hnotPending⟩) htarget
      | F =>
          exact widthWordRenewalWaveInternalCanonicalQuietStep
            ring root e s hn hsmallFive hs z hz hwave he hj
            (Or.inl hsourceC) (Or.inr htarget)
    · have hl : (z.2.1 e).ser.probe = .LEAF_OK := by
        rw [hchild]
        exact hleaf.2.1
      have hnotPending :
          (z.2.1 e).ser.probe ≠ .PENDING := by
        rw [hl]
        decide
      cases htarget :
          (z.2.1 (ring.rightNeighbor e)).ser.phase with
      | B =>
          exact widthWordRenewalWaveInternalCanonicalQuietStep
            ring root e s hn hsmallFive hs z hz hwave he hj
            (Or.inl hsourceC) (Or.inl htarget)
      | C =>
          exact widthWordRenewalWaveInternalNonBToCQuietStep
            ring root e s hn hsmallFive hs z hz he hj hwave
            (Or.inr ⟨hsourceC, hnotPending⟩) htarget
      | F =>
          exact widthWordRenewalWaveInternalCanonicalQuietStep
            ring root e s hn hsmallFive hs z hz hwave he hj
            (Or.inl hsourceC) (Or.inr htarget)

end

section
open Classical

/-- Width port of `bankWordRenewalWaveInternalReturnCoveredQuietStep`: the BANK band premise is replaced by `5 ≤ n`, and the renewal constants are those of the compiled width t (lease 8t+4, quota 2t+1). Consumer: `widthWordRenewalWaveSelectedInternalMovingQuietStep`.
 Every RETURN coveredInside nonroot edge is either the
excluded B/DONE+B predecessor-prefix pair, the unique
B/DONE→F pivot predecessor, or a C/F suffix S3/S4 row.
The latter uses the historical RETURN nonpending clause to
exclude forged C/PENDING and routes to canonical or frame
proofs. Consumer: RETURN coveredInside of the internal moving
residue, including the pivot-one boundary. -/
theorem widthWordRenewalWaveInternalReturnCoveredQuietStep {n : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hn : 5 ≤ n)
    (hsmallFive : 5 ≤ n)
    (hs : WidthWordSerializerRootClass ring hsmallFive root s)
    (z : BankWordEpochState n)
    (hz : BankWordEpochReachable ring root s z)
    (he : e ≠ root)
    (hj : ring.rightNeighbor e ≠ root)
    (hwave : BankWordRenewalFrontierWaveLineageQuiet ring root z)
    (hactive : (z.2.1 root).ser.cert = .RUNNING ∧
      (z.2.1 root).ser.wphase = .VALIDATING)
    (g : L3.EWord.ValidationGhost)
    (hg : g = Classical.choose (hwave.wave.2 hactive))
    (hr : L3.EWord.ReturnShape ring root z.2.1 g)
    (hinside : L3.EWord.validationEdgeClass ring root g e =
      .coveredInside)
    (hnotdone : ¬ ((z.2.1 e).ser.phase = .B ∧
      (z.2.1 e).ser.out = .DONE ∧
      (z.2.1 (ring.rightNeighbor e)).ser.phase = .B)) :
    BankWordRenewalFrontierWaveLineageQuiet ring root
      (bankWordEpochNext ring root z e) := by
  have hk := L3.EWord.validationOffsetBound ring root e
  have heoff : e = L3.EWord.site ring root
      (PPL.cyclicOffset ring root e) :=
    (L3.EWord.validationOffsetRepresentative ring root e).symm
  have hbound : PPL.cyclicOffset ring root e + 1 < n :=
    L3.EWord.validationNonSeamOffset ring root e
      (L3.EWord.validationCoveredClassFacts
        ring root g e hinside).1
  have hjoff := L3.EWord.validationParentNeighbor ring root
    (PPL.cyclicOffset ring root e) e heoff
  by_cases hearly : PPL.cyclicOffset ring root e + 1 <
      g.pivot
  · have hleft := hr.completed
      (⟨PPL.cyclicOffset ring root e, hk⟩ : Fin n)
      (by simp only [Fin.val_mk]; omega)
    have hright := hr.completed
      (⟨PPL.cyclicOffset ring root e + 1, hbound⟩ : Fin n)
      (by simpa only [Fin.val_mk] using hearly)
    apply False.elim
    apply hnotdone
    refine ⟨?_, ?_, ?_⟩
    · rw [heoff]
      exact hleft.1
    · rw [heoff]
      exact hleft.2.1
    · rw [hjoff]
      exact hright.1
  · by_cases hmove :
        PPL.cyclicOffset ring root e + 1 = g.pivot
    · by_cases hone : g.pivot = 1
      · have hkzero : PPL.cyclicOffset ring root e = 0 := by
          omega
        have hroot : e = root := by
          rw [heoff, hkzero, L3.EWord.siteZero]
        exact False.elim (he hroot)
      · have hpositive : 1 < g.pivot := by
          have hp := hr.pivotPositive
          omega
        have hprev : g.pivot - 1 =
            PPL.cyclicOffset ring root e := by omega
        have hsource : e = L3.EWord.site ring root
            (g.pivot - 1) := by
          rw [hprev]
          exact heoff
        exact widthWordRenewalWaveInternalReturnMoveQuietStep
          ring root e s hn hsmallFive hs z hz hwave hactive
          g hg hr hpositive hsource
    · have hge : g.pivot ≤ PPL.cyclicOffset ring root e := by
        omega
      have hsource :
          (z.2.1 e).ser.phase = .F ∨
          ((z.2.1 e).ser.phase = .C ∧
            (z.2.1 e).ser.probe ≠ .PENDING) := by
        by_cases hsame : PPL.cyclicOffset ring root e =
            g.pivot
        · left
          rw [heoff, hsame]
          exact hr.leftmostF
        · have hgreater : g.pivot <
              PPL.cyclicOffset ring root e := by omega
          rcases hr.suffix
            (⟨PPL.cyclicOffset ring root e, hk⟩ : Fin n)
            (by simpa only [Fin.val_mk] using hgreater)
            with hF | hC
          · left
            rw [heoff]
            exact hF.1
          · have hc : (z.2.1 e).ser.phase = .C := by
              rw [heoff]
              exact hC.1
            have hq := hwave.returnSuffixQuiet
              hactive g hr
              (⟨PPL.cyclicOffset ring root e, hk⟩ : Fin n)
              (by simpa only [Fin.val_mk] using hgreater)
              (by simpa only [Fin.val_mk] using hC.1)
            right
            refine ⟨hc, ?_⟩
            rw [heoff]
            simpa only [Fin.val_mk] using hq
      have hgreater : g.pivot <
          PPL.cyclicOffset ring root e + 1 := by omega
      have htarget :
          (z.2.1 (ring.rightNeighbor e)).ser.phase = .F ∨
          (z.2.1 (ring.rightNeighbor e)).ser.phase = .C := by
        rcases hr.suffix
          (⟨PPL.cyclicOffset ring root e + 1, hbound⟩ : Fin n)
          (by simpa only [Fin.val_mk] using hgreater)
          with hF | hC
        · left
          rw [hjoff]
          exact hF.1
        · right
          rw [hjoff]
          exact hC.1
      rcases htarget with htF | htC
      · rcases hsource with hsF | ⟨hsC, hq⟩
        · exact widthWordRenewalWaveInternalCanonicalQuietStep
            ring root e s hn hsmallFive hs z hz hwave he hj
            (Or.inr hsF) (Or.inr htF)
        · exact widthWordRenewalWaveInternalCanonicalQuietStep
            ring root e s hn hsmallFive hs z hz hwave he hj
            (Or.inl hsC) (Or.inr htF)
      · exact widthWordRenewalWaveInternalNonBToCQuietStep
          ring root e s hn hsmallFive hs z hz he hj hwave
          hsource htC

end

section
open Classical

/-- Width port of `bankWordRenewalWaveSelectedInternalMovingQuietStep`: the BANK band premise is replaced by `5 ≤ n`, and the renewal constants are those of the compiled width t (lease 8t+4, quota 2t+1). Consumer: `widthWordRenewalLineageInternalMovingStepHolds`.
 The selected historical W ghost classifies every internal
moving service. The root-seam is excluded by the right-endpoint
guard; unvisitedSuffix by the selected historical witness;
covered FORWARD is the forbidden B/DONE+B pair. The remaining
frontierParent, challengedChild, and RETURN coveredInside cases
are discharged by the literal S2N/S3/S4 admission and cleanup
proofs, not by an assumed generic protocol step.
Consumer: BankWordRenewalLineageInternalMovingStep. -/
theorem widthWordRenewalWaveSelectedInternalMovingQuietStep {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hsmallFive : 5 ≤ n)
    (root e : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hs : WidthWordSerializerRootClass ring hsmallFive root s)
    (z : BankWordEpochState n)
    (hz : BankWordEpochReachable ring root s z)
    (hwave : BankWordRenewalFrontierWaveLineageQuiet ring root z)
    (hactive : (z.2.1 root).ser.cert = .RUNNING ∧
      (z.2.1 root).ser.wphase = .VALIDATING)
    (he : e ≠ root)
    (hj : ring.rightNeighbor e ≠ root)
    (g : L3.EWord.ValidationGhost)
    (hg : g = Classical.choose (hwave.wave.2 hactive))
    (hshape : L3.EWord.ValidationShape ring root z.2.1 g)
    (hnotUnvisited :
      L3.EWord.validationEdgeClass ring root g e ≠
        .unvisitedSuffix)
    (hnotdone : ¬ ((z.2.1 e).ser.phase = .B ∧
      (z.2.1 e).ser.out = .DONE ∧
      (z.2.1 (ring.rightNeighbor e)).ser.phase = .B)) :
    BankWordRenewalFrontierWaveLineageQuiet ring root
      (bankWordEpochNext ring root z e) := by
  have hnotSeam :
      e ≠ L3.EWord.site ring root (n - 1) := by
    intro hseam
    exact hj (L3.EWord.validationSeamNeighbor
      ring root e hseam)
  have hnotRootClass :
      L3.EWord.validationEdgeClass ring root g e ≠
        .rootSeam := by
    intro hseam
    unfold L3.EWord.validationEdgeClass at hseam
    rw [if_neg hnotSeam] at hseam
    by_cases hp : g.stage = .forward ∧
        e = L3.EWord.site ring root g.pivot
    · rw [if_pos hp] at hseam
      cases hseam
    · rw [if_neg hp] at hseam
      by_cases hc : g.stage = .forward ∧
          e = L3.EWord.site ring root (g.pivot + 1)
      · rw [if_pos hc] at hseam
        cases hseam
      · rw [if_neg hc] at hseam
        by_cases hu : ∀ i : Fin n, i.val < g.scrub →
            L3.EWord.site ring root i.val ≠ e ∧
            L3.EWord.site ring root i.val ≠
              ring.rightNeighbor e
        · rw [if_pos hu] at hseam
          cases hseam
        · rw [if_neg hu] at hseam
          cases hseam
  rcases L3.EWord.validationEdgeClassCover ring root g e with
    hseam | hparent | hchild | hunvisited | hinside
  · exact False.elim (hnotRootClass hseam)
  · have hp : g.stage = .forward ∧
        e = L3.EWord.site ring root g.pivot := by
      unfold L3.EWord.validationEdgeClass at hparent
      rw [if_neg hnotSeam] at hparent
      by_cases hf : g.stage = .forward ∧
          e = L3.EWord.site ring root g.pivot
      · exact hf
      · rw [if_neg hf] at hparent
        by_cases hc : g.stage = .forward ∧
            e = L3.EWord.site ring root (g.pivot + 1)
        · rw [if_pos hc] at hparent
          cases hparent
        · rw [if_neg hc] at hparent
          by_cases hu : ∀ i : Fin n, i.val < g.scrub →
              L3.EWord.site ring root i.val ≠ e ∧
              L3.EWord.site ring root i.val ≠
                ring.rightNeighbor e
          · rw [if_pos hu] at hparent
            cases hparent
          · rw [if_neg hu] at hparent
            cases hparent
    have hf : L3.EWord.ForwardShape ring root z.2.1 g := by
      rcases hshape.stageShape with hF | hR
      · exact hF
      · have hbad := hR.isReturn
        rw [hp.1] at hbad
        cases hbad
    exact widthWordRenewalWaveInternalFrontierParentQuietStep
      ring root e s hn hsmallFive hs z hz he hj hwave hactive
      g hg hf hp.2
  · have hp : g.stage = .forward ∧
        e = L3.EWord.site ring root (g.pivot + 1) := by
      unfold L3.EWord.validationEdgeClass at hchild
      rw [if_neg hnotSeam] at hchild
      by_cases hparent : g.stage = .forward ∧
          e = L3.EWord.site ring root g.pivot
      · rw [if_pos hparent] at hchild
        cases hchild
      · rw [if_neg hparent] at hchild
        by_cases hc : g.stage = .forward ∧
            e = L3.EWord.site ring root (g.pivot + 1)
        · exact hc
        · rw [if_neg hc] at hchild
          by_cases hu : ∀ i : Fin n, i.val < g.scrub →
              L3.EWord.site ring root i.val ≠ e ∧
              L3.EWord.site ring root i.val ≠
                ring.rightNeighbor e
          · rw [if_pos hu] at hchild
            cases hchild
          · rw [if_neg hu] at hchild
            cases hchild
    have hf : L3.EWord.ForwardShape ring root z.2.1 g := by
      rcases hshape.stageShape with hF | hR
      · exact hF
      · have hbad := hR.isReturn
        rw [hp.1] at hbad
        cases hbad
    exact widthWordRenewalWaveInternalChallengedChildQuietStep
      ring root e s hn hsmallFive hs z hz he hj hwave hactive
      g hg hf hp.2
  · exact False.elim (hnotUnvisited hunvisited)
  · rcases hshape.stageShape with hf | hr
    · exact False.elim (hnotdone
        (bankWordRenewalWaveForwardCoveredDonePair
          ring root e z g hshape hf hinside))
    · exact widthWordRenewalWaveInternalReturnCoveredQuietStep
        ring root e s hn hsmallFive hs z hz he hj hwave hactive
        g hg hr hinside hnotdone

end

section
open Classical

/-- Width port of `bankWordRenewalLineageInternalMovingStepHolds`: the BANK band premise is replaced by `5 ≤ n`, and the renewal constants are those of the compiled width t (lease 8t+4, quota 2t+1). Consumer: `widthWordEpochPostSOneWorkerClockHolds`, `widthWordRenewalFreshAttemptCostHolds`.
 The INTERNAL moving lineage residue of R10a is proved by
choosing the historical witness of the active validating wave,
transporting the genuinely negative unvisitedSuffix guard to
that witness using physical ghost uniqueness, and exhausting
all five priority edge classes with their actual serializer and
ticket equations. Consumer: the R10a W worker clock. -/
theorem widthWordRenewalLineageInternalMovingStepHolds {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hsmallFive : 5 ≤ n)
    (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hs : WidthWordSerializerRootClass ring hsmallFive root s) :
    BankWordRenewalLineageInternalMovingStep ring root s := by
  intro z hz hwave hrun hval e he hj hunvisited hnotdone
  have hactive :
      (z.2.1 root).ser.cert = .RUNNING ∧
      (z.2.1 root).ser.wphase = .VALIDATING :=
    ⟨hrun, hval⟩
  have hselected := Classical.choose_spec
    (hwave.wave.2 hactive)
  obtain ⟨req, stamp, hshape, hsites⟩ := hselected
  have hnotUnvisited :=
    bankWordRenewalWaveChosenNotUnvisited ring root e z
      hwave hactive hunvisited
  exact widthWordRenewalWaveSelectedInternalMovingQuietStep
    ring hn hsmallFive root e s hs z hz hwave hactive he hj
    (Classical.choose (hwave.wave.2 hactive)) rfl hshape
    hnotUnvisited hnotdone

end

section
open Classical

/-- Width port of `bankWordEpochPostSOneWorkerClockHolds`: the BANK band premise is replaced by `5 ≤ n`, and the renewal constants are those of the compiled width t (lease 8t+4, quota 2t+1). Consumer: `widthWordEpochCompletionFiveCostHolds`.
 R10a's post-S1 W worker clock has no remaining moving-row
Prop premise once the historical INTERNAL residue is discharged.
Consumer: BOARD R10a and BankRepairWord expected-cost bridge. -/
theorem widthWordEpochPostSOneWorkerClockHolds {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hsmallFive : 5 ≤ n)
    (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hs : WidthWordSerializerRootClass ring hsmallFive root s) :
    WidthWordEpochPostSOneWorkerClock ring root s := by
  exact widthWordEpochPostSOneWorkerClockOfInternalRows
    ring hn hsmallFive root s hs
    (widthWordRenewalLineageInternalMovingStepHolds
      ring hn hsmallFive root s hs)

end

section
open Classical
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

/-- Width port of `bankWordRenewalFreshAttemptCostHolds`: the BANK band premise is replaced by `5 ≤ n`, and the renewal constants are those of the compiled width t (lease 8t+4, quota 2t+1). Consumer: `widthWordRenewalFreshFourCostHoldsOfFailure`.
 The actual BANK renewal kernel has the one-block expected
attempt cost from every fresh genuine-hard-entry seed. Both
moving-row inputs are now installed; no probability failure
estimate is used in this theorem.
Consumer: the five-block fresh completion step of R10 W. -/
theorem widthWordRenewalFreshAttemptCostHolds {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hsmallFive : 5 ≤ n)
    (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hs : WidthWordSerializerRootClass ring hsmallFive root s) :
    WidthWordRenewalFreshAttemptCost ring root s := by
  exact widthWordRenewalFreshAttemptCostOfMovingRows
    ring hn hsmallFive root s hs
    (widthWordRenewalLineageRootMovingStepHolds
      ring hn hsmallFive root s hs)
    (widthWordRenewalLineageInternalMovingStepHolds
      ring hn hsmallFive root s hs)

end

section
open Classical
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

/-- Width port of `bankWordRenewalFreshFourCostHoldsOfFailure`: the BANK band premise is replaced by `5 ≤ n`, and the renewal constants are those of the compiled width t (lease 8t+4, quota 2t+1). Consumer: `widthWordRenewalFreshFourCostHolds`.
 The fresh same-word renewal inequality actually yields
FOUR blocks before the existing five-block weakening.
Using the now-unconditional J-W attempt cost, its ONLY
external premise is the three-quarter retry bound for the
ACTUAL fresh kernel. Consumer: the 1B + 4B staging budget
required by R10's exact (440*s+275)*n^2 W rate. -/
theorem widthWordRenewalFreshFourCostHoldsOfFailure {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hsmallFive : 5 ≤ n)
    (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hs : WidthWordSerializerRootClass ring hsmallFive root s)
    (hfail : ∀ seed : BankWordRenewalFreshSeed ring root s,
      ∀ T, 4 * PPL.Convergence.LDLocal.retryCount
        (bankWordRenewalFreshKernel ring root s)
        (.active seed.1) T ≤ 3 * n ^ T)
    (seed : BankWordRenewalFreshSeed ring root s)
    (T : Nat) :
    costNumerator (bankWordRenewalNext ring root s)
      (fun v : BankWordRenewalPostSOne ring root s =>
        BankWordRenewalCompleted v.1)
      seed.1 T ≤ n ^ T * (4 * widthWordRenewalBlock n) := by
  have hcost := widthWordRenewalFreshAttemptCostHolds
    ring hn hsmallFive root s hs
  have hc : ∀ a : BankWordRenewalFreshSeed ring root s,
      (bankWordRenewalFreshKernel ring root s).valid a →
      ∀ t,
        costNumerator
          (L3.Prob.attemptStepper
            (bankWordRenewalFreshKernel ring root s))
          (fun v => L3.Prob.attemptGood v ∨
            L3.Prob.attemptFail v)
          (.active ((bankWordRenewalFreshKernel ring root s).start a))
          t ≤ n ^ t * widthWordRenewalBlock n := by
    intro a _ t
    exact hcost a t
  have hf : ∀ a : BankWordRenewalFreshSeed ring root s,
      (bankWordRenewalFreshKernel ring root s).valid a →
      ∀ t, 4 * PPL.Convergence.LDLocal.retryCount
        (bankWordRenewalFreshKernel ring root s)
        (.active ((bankWordRenewalFreshKernel ring root s).start a))
        t ≤ 3 * n ^ t := by
    intro a _ t
    exact hfail a t
  have hrenewal := L3.Prob.costNumerator_renewal_le
    (bankWordRenewalNext ring root s)
    (fun v : BankWordRenewalPostSOne ring root s =>
      BankWordRenewalCompleted v.1)
    (bankWordRenewalFreshKernel ring root s)
    (fun x y : BankWordRenewalPostSOne ring root s => x = y)
    (bankWordRenewalFreshSimulation ring root s)
    (widthWordRenewalBlock n) 3 4
    (by decide : 3 < (4 : Nat))
    hc hf seed.1 seed seed.2 rfl T
  rw [bankWordQuarterRetryCeiling] at hrenewal
  exact hrenewal

end

section
open Classical
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

/-- Width port of `bankWordEpochSOneReachedOfRootTicketOrigin`: the BANK band premise is replaced by `5 ≤ n`, and the renewal constants are those of the compiled width t (lease 8t+4, quota 2t+1). Consumer: `widthWordEpochSOneReachedOfGenuine`.
 A root ticket with an actual hard-S1 origin implies that the
stopped S1 clock has fired on the represented scheduler history.
Consumer: the post-S1 premise of the first fresh worker seed. -/
theorem widthWordEpochSOneReachedOfRootTicketOrigin {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hsmallFive : 5 ≤ n)
    (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hs : WidthWordSerializerRootClass ring hsmallFive root s)
    (z : BankWordEpochState n) (ticket : WValidationTicket)
    (horigin : BankWordRootTicketOrigin ring root s z ticket) :
    BankWordEpochSOneReached z := by
  obtain ⟨pre, mid, request, hstate, hrequested, _,
    _, _, _, _, _⟩ := horigin
  have hp : BankWordEpochReachable ring root s
      (bankWordEpochRun ring root (bankWordEpochStart s) pre) :=
    ⟨pre, rfl⟩
  have hfixed := widthWordEpochFixedRootNext ring hn hsmallFive root s hs
    (bankWordEpochRun ring root (bankWordEpochStart s) pre) hp root
  have hservice : clockSerializerSOneService ring root
      (bankWordEpochRun ring root
        (bankWordEpochStart s) pre).2.1 root :=
    (clockSerializerSOneIffRequested ring root
      (bankWordEpochRun ring root (bankWordEpochStart s) pre).2.1
      (by omega : 2 ≤ n) hfixed root).2 ⟨rfl, hrequested⟩
  have hinv := widthWordEpochSOneRunningBReachable
    ring root hn hsmallFive s hs
    (bankWordEpochRun ring root (bankWordEpochStart s) pre) hp
  have hstop : BankWordEpochSOneReached
      (bankWordEpochNext ring root
        (bankWordEpochRun ring root (bankWordEpochStart s) pre)
        root) := by
    change clockSerializerIsStopped
      (clockSerializerSOneOnlyNext ring root
        (bankWordEpochRun ring root (bankWordEpochStart s) pre).1 root)
    cases hnode :
        (bankWordEpochRun ring root (bankWordEpochStart s) pre).1 with
    | stopped =>
        exact trivial
    | active w =>
        have hw :
            w = (bankWordEpochRun ring root
              (bankWordEpochStart s) pre).2.1 :=
          hinv.1 w hnode
        rw [hw]
        exact (clockSerializerSOneOnlyStopIff ring root _ root).2
          hservice
  have hfrom : BankWordEpochReachableFrom ring root
      (bankWordEpochNext ring root
        (bankWordEpochRun ring root (bankWordEpochStart s) pre)
        root) z := by
    refine ⟨mid, ?_⟩
    calc
      bankWordEpochRun ring root
          (bankWordEpochNext ring root
            (bankWordEpochRun ring root (bankWordEpochStart s) pre)
            root) mid =
        bankWordEpochRun ring root
          (bankWordEpochRun ring root (bankWordEpochStart s) pre)
          (root :: mid) := rfl
      _ = bankWordEpochRun ring root (bankWordEpochStart s)
          (pre ++ (root :: mid)) :=
        (bankWordEpochRunAppend ring root (bankWordEpochStart s)
          pre (root :: mid)).symm
      _ = z := by rw [hstate]; simp
  exact bankWordEpochSOneReachedFrom ring root _ z hfrom hstop

end

section
open Classical
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

/-- Width port of `bankWordEpochSOneReachedOfGenuine`: the BANK band premise is replaced by `5 ≤ n`, and the renewal constants are those of the compiled width t (lease 8t+4, quota 2t+1). Consumer: `widthWordEpochFreshCutOfFirstLaunch`, `widthWordEpochLiveTrailStep`.
 The represented historical done ticket at genuine S6 has a
root hard-S1 origin, so genuine acceptance cannot precede the
observer's first S1 latch. Consumer: the fresh-seed witness of
the first launched worker on the original projected W chain. -/
theorem widthWordEpochSOneReachedOfGenuine {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hsmallFive : 5 ≤ n)
    (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hs : WidthWordSerializerRootClass ring hsmallFive root s)
    (z : BankWordEpochState n)
    (hz : BankWordEpochReachable ring root s z) (e : Fin n)
    (hg : bankWordRenewalGenuine ring root z e) :
    BankWordEpochSOneReached z := by
  have hgenuine :
      bankWordHardEpochGenuine ring root
        (bankWordEpochSelectedReceipt ring z e)
        (bankWordHardEpochLedger ring root z) = true := hg
  obtain ⟨he, _, _⟩ :=
    bankWordHardEpochSelectedGenuineOwnerFlags
      ring root z e hgenuine
  subst e
  obtain ⟨ticket, sibling, hdone, _, _, _⟩ :=
    bankWordHardEpochGenuineJoinedStamps
      ring root (bankWordEpochSelectedReceipt ring z root)
      (bankWordHardEpochLedger ring root z) hgenuine
  have hdoneRoot :
      wTicketAt .done
        ((bankWordHardEpochLedger ring root z).validation root) =
      some ticket := by
    exact hdone
  have horigin :=
    (widthWordRootDoneOriginReachable
      ring hn hsmallFive root s hs z hz) ticket hdoneRoot
  exact widthWordEpochSOneReachedOfRootTicketOrigin
    ring hn hsmallFive root s hs z ticket horigin

end

section
open Classical
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

/-- Width port of `bankWordEpochFreshCutOfFirstLaunch`: the BANK band premise is replaced by `5 ≤ n`, and the renewal constants are those of the compiled width t (lease 8t+4, quota 2t+1). Consumer: `widthWordEpochCompletionFiveCostHolds`.
 The first nonempty worker edge is a genuine hard S6 and is
already a fresh post-S1 cut on the same physical scheduler word.
Consumer: first-hit entrance domination before the 4B stage. -/
theorem widthWordEpochFreshCutOfFirstLaunch {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hsmallFive : 5 ≤ n)
    (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hs : WidthWordSerializerRootClass ring hsmallFive root s)
    (z : BankWordEpochState n)
    (hz : BankWordEpochReachable ring root s z)
    (e : Fin n)
    (hnot : ¬ BankWordEpochWorkerLaunched z)
    (hlaunch : BankWordEpochWorkerLaunched
      (bankWordEpochNext ring root z e)) :
    BankWordEpochFreshCut ring root s
      (bankWordEpochNext ring root z e) := by
  have hg := bankWordEpochGenuineOfFirstLaunch
    ring root s z hz e hnot hlaunch
  have hSOne := widthWordEpochSOneReachedOfGenuine
    ring hn hsmallFive root s hs z hz e hg
  obtain ⟨seed, hseed⟩ :=
    bankWordRenewalFreshSeedAfterGenuine ring root s
      ⟨z, hz, hSOne⟩ e hg
  exact ⟨seed, congrArg Subtype.val hseed⟩

end

section
open Classical

/-- Width port of `bankWordRenewalSoftReturnIncomingStep`: the BANK band premise is replaced by `5 ≤ n`, and the renewal constants are those of the compiled width t (lease 8t+4, quota 2t+1). Consumer: `widthWordRenewalSoftReturnAllEdgesStep`.
 R10a S-frontier physical row; consumer: all-edges closure. -/
theorem widthWordRenewalSoftReturnIncomingStep {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hn : 5 ≤ n)
    (hsmallFive : 5 ≤ n)
    (hs : WidthWordSerializerRootClass ring hsmallFive root s)
    (z : BankWordRenewalPostSOne ring root s)
    (q : Nat) (hr : BankWordRenewalSoftReturnShape ring root z.1 q) :
    BankWordRenewalSoftShape ring root
      (bankWordEpochNext ring root z.1
        (L3.EWord.site ring root (n - 1))) ∧
    bankWordRenewalSoftRootedPosition ring root
      (bankWordEpochNext ring root z.1
        (L3.EWord.site ring root (n - 1))) =
      bankWordRenewalSoftRootedPosition ring root z.1 ∧
    (bankWordEpochSelectedReceipt ring z.1
      (L3.EWord.site ring root (n - 1))).serializer.row =
        "S5" := by
  have hpred :
      ring.rightNeighbor (L3.EWord.site ring root (n - 1)) =
        root :=
    L3.EWord.validationSeamNeighbor ring root
      (L3.EWord.site ring root (n - 1)) rfl
  have hsourceNonroot :=
    L3.EWord.validationSeamNotRoot ring root
      (L3.EWord.site ring root (n - 1)) (by omega : 3 ≤ n) rfl
  have hflags := widthWordRenewalSoftIncomingFlags
    ring root (L3.EWord.site ring root (n - 1))
    s hn hsmallFive hs z hsourceNonroot hpred
  have hstep := bankWordRenewalSoftRootIncomingReturnStep
    ring root s z q hn hr hflags.1 hflags.2
  have hrows := widthWordRenewalSoftIncomingRowCensus
    ring root (L3.EWord.site ring root (n - 1))
    s hn hsmallFive hs z hpred
  have hrow :
      (bankWordEpochSelectedReceipt ring z.1
        (L3.EWord.site ring root (n - 1))).serializer.row =
          "S5" := by
    rcases hrows with hzero | hfive
    · have hbad : SerCert.RUNNING = SerCert.IDLE :=
        hr.rootRunning.symm.trans hzero.1
      cases hbad
    · exact hfive.2
  exact ⟨hstep.1, hstep.2.1, hrow⟩

end

section
open Classical

/-- Width port of `bankWordRenewalSoftReturnAllEdgesStep`: the BANK band premise is replaced by `5 ≤ n`, and the renewal constants are those of the compiled width t (lease 8t+4, quota 2t+1). Consumer: `widthWordRenewalSoftShapeStep`.
 A returning soft lap is closed under every selected physical
    edge, including nonpivot B/DONE+B frames, the leftmost
    returning-F retreat, S3/S4 suffix sanitation, incoming S5,
    and the final ROOT_OUT soft S6 reset. Consumer: return branch
    of widthWordRenewalSoftShapeStep, R10a hfail. -/
theorem widthWordRenewalSoftReturnAllEdgesStep {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hn : 5 ≤ n)
    (hsmallFive : 5 ≤ n)
    (hs : WidthWordSerializerRootClass ring hsmallFive root s)
    (z : BankWordRenewalPostSOne ring root s)
    (e : Fin n) (q : Nat)
    (hr : BankWordRenewalSoftReturnShape ring root z.1 q) :
    BankWordRenewalSoftShape ring root
      (bankWordEpochNext ring root z.1 e) ∧
    bankWordRenewalSoftRootedPosition ring root
      (bankWordEpochNext ring root z.1 e) ≤
      bankWordRenewalSoftRootedPosition ring root z.1 + 1 ∧
    (bankWordRenewalSoftRootedPosition ring root
        (bankWordEpochNext ring root z.1 e) ≠
      bankWordRenewalSoftRootedPosition ring root z.1 →
      e = bankWordRenewalSoftRootedChosen ring root s z) := by
  have hshape : BankWordRenewalSoftShape ring root z.1 := by
    intro _
    exact Or.inr ⟨q, hr⟩
  rcases bankWordRenewalSoftReturnEdgeCases
      ring root e z.1 q hn hr with hroot | hseam | hinter
  · subst e
    by_cases hzero : q = 0
    · have hrootReturn :
          BankWordRenewalSoftReturnShape ring root z.1 0 := by
        simpa only [hzero] using hr
      exact widthWordRenewalSoftRootFinishStep
        ring root s hn hsmallFive hs z hrootReturn
    · have hqpos : 0 < q := by omega
      have hrootOld := hr.completed 0 (by omega)
      have hchildOld := hr.completed 1 (by omega)
      have hrootB : (z.1.2.1 root).ser.phase = .B :=
        hr.rootPhase
      have hrootDone : (z.1.2.1 root).ser.out = .DONE := by
        simpa only [L3.EWord.siteZero] using hrootOld.2.1
      have hchildB :
          (z.1.2.1 (ring.rightNeighbor root)).ser.phase =
            .B := by
        simpa only [L3.EWord.siteOne] using hchildOld.1
      have hnotReq : (z.1.2.1 root).ser.cert ≠ .REQUESTED := by
        intro h
        have hbad := hr.rootRunning.symm.trans h
        cases hbad
      have hflags := widthWordRenewalSoftOutgoingFlags
        ring root s hn hsmallFive hs z
      have hframe := bankWordRenewalSoftOutgoingCoveredDoneFrame
        ring root root z.1 hn hrootB hrootDone hchildB
        hnotReq hflags.1 hflags.2 hshape
      refine ⟨hframe.1, ?_, ?_⟩
      · rw [hframe.2]
        omega
      · intro hneq
        exact False.elim (hneq hframe.2)
  · rcases hseam with ⟨he, _⟩
    subst e
    have hstep := widthWordRenewalSoftReturnIncomingStep
      ring root s hn hsmallFive hs z q hr
    refine ⟨hstep.1, ?_, ?_⟩
    · rw [hstep.2.1]
      omega
    · intro hneq
      exact False.elim (hneq hstep.2.1)
  · rcases hinter with ⟨k, hkpos, hinside, he, hclass⟩
    subst e
    rcases hclass with hcovered | hpivot | hsuffix
    · have hstep := widthWordRenewalSoftReturnCoveredStep
        ring root s hn hsmallFive hs z q k hr hshape hkpos
        hcovered.1
      refine ⟨hstep.1, ?_, ?_⟩
      · rw [hstep.2.1]
        omega
      · intro hneq
        exact False.elim (hneq hstep.2.1)
    · have hqpositive : 0 < q := by
        omega
      have hrow := widthWordRenewalSoftReturnParentStep
        ring root s hn hsmallFive hs z q hqpositive hr
      have hk : k = q := hpivot.1
      subst k
      exact hrow
    · have hsourceNotRoot :
          L3.EWord.site ring root k ≠ root :=
        L3.EWord.validationPositiveSiteNotRoot
          ring root k (by omega) hkpos
      have htargetNotRoot :
          ring.rightNeighbor (L3.EWord.site ring root k) ≠
            root := by
        rw [L3.EWord.siteSuccessor]
        exact L3.EWord.validationPositiveSiteNotRoot
          ring root (k + 1) hinside (by omega)
      have hflags := widthWordRenewalSoftInternalFlags
        ring root (L3.EWord.site ring root k)
        s hn hsmallFive hs z hsourceNotRoot htargetNotRoot
      have hstep := bankWordRenewalSoftReturnSuffixStep
        ring root s z q k hn hr hsuffix.1 hinside
        hflags.1 hflags.2
      refine ⟨hstep.1, ?_, ?_⟩
      · rw [hstep.2.1]
        omega
      · intro hneq
        exact False.elim (hneq hstep.2.1)

end

section
open Classical

/-- Width port of `bankWordRenewalSoftForwardParentStep`: the BANK band premise is replaced by `5 ≤ n`, and the renewal constants are those of the compiled width t (lease 8t+4, quota 2t+1). Consumer: `widthWordRenewalSoftForwardAllEdgesStep`.
 R10a S-frontier physical row; consumer: all-edges closure. -/
theorem widthWordRenewalSoftForwardParentStep {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hn : 5 ≤ n)
    (hsmallFive : 5 ≤ n)
    (hs : WidthWordSerializerRootClass ring hsmallFive root s)
    (z : BankWordRenewalPostSOne ring root s)
    (p : Nat) (hp : 0 < p)
    (hf : BankWordRenewalSoftForwardShape ring root z.1 p)
    (hrun : (z.1.2.1 root).ser.cert = .RUNNING) :
    BankWordRenewalSoftShape ring root
      (bankWordEpochNext ring root z.1
        (L3.EWord.site ring root p)) ∧
    bankWordRenewalSoftRootedPosition ring root
      (bankWordEpochNext ring root z.1
        (L3.EWord.site ring root p)) ≤
      bankWordRenewalSoftRootedPosition ring root z.1 + 1 ∧
    (bankWordRenewalSoftRootedPosition ring root
        (bankWordEpochNext ring root z.1
          (L3.EWord.site ring root p)) ≠
      bankWordRenewalSoftRootedPosition ring root z.1 →
      L3.EWord.site ring root p =
        bankWordRenewalSoftRootedChosen ring root s z) := by
  have hpn : p < n := by
    have hb := hf.pivotBound
    omega
  have hsourceNonroot :=
    L3.EWord.validationPositiveSiteNotRoot ring root p hpn hp
  have htargetNonroot :
      ring.rightNeighbor (L3.EWord.site ring root p) ≠
        root := by
    rw [L3.EWord.siteSuccessor]
    exact L3.EWord.validationPositiveSiteNotRoot
      ring root (p + 1) hf.pivotBound (by omega)
  have hflags := widthWordRenewalSoftInternalFlags
    ring root (L3.EWord.site ring root p)
    s hn hsmallFive hs z hsourceNonroot htargetNonroot
  have hrootOld := hf.completed 0 hp
  have hrootPhase : (z.1.2.1 root).ser.phase = .B := by
    simpa only [L3.EWord.siteZero] using hrootOld.1
  have hrootCurrent : (z.1.2.1 root).ser.wphase =
      .CURRENT := by
    simpa only [L3.EWord.siteZero] using hrootOld.2.2
  have hactive :
      (z.1.2.1 root).ser.cert = .RUNNING ∧
      (z.1.2.1 root).ser.phase = .B ∧
      (z.1.2.1 root).ser.wphase = .CURRENT :=
    ⟨hrun, hrootPhase, hrootCurrent⟩
  rcases hf.front with hzero | hpositive
  · have hbad : False := by
      omega
    exact False.elim hbad
  · rcases hpositive.2 with hnew | hwaiting
    · have hstep := bankWordRenewalSoftForwardChallengeStep
        ring root s z p hn hp hf hrun hnew hflags.1 hflags.2
      refine ⟨hstep.1, ?_, ?_⟩
      · rw [hstep.2.1, hstep.2.2.1]
        omega
      · intro _
        exact hstep.2.2.2.symm
    · rcases hwaiting.2 with hpending | hinternal | hleaf
      · have hstep := bankWordRenewalSoftInternalPendingStall
          ring root s z p hn hp hf hactive hwaiting.1
          hpending.1 hpending.2.1 hflags.1 hflags.2
        refine ⟨hstep.1, ?_, ?_⟩
        · rw [hstep.2.1]
          omega
        · intro hne
          exact False.elim (hne hstep.2.1)
      · have hstep := bankWordRenewalSoftInternalAdmissionStep
          ring root s z p hn hp hf hrun hinternal.1
          hwaiting.1 hinternal.2.1 hinternal.2.2.1
          hflags.1 hflags.2
        refine ⟨hstep.1, ?_, ?_⟩
        · rw [hstep.2.1, hstep.2.2.1]
          omega
        · intro hne
          have heq := hstep.2.1.trans hstep.2.2.1.symm
          exact False.elim (hne heq)
      · have hpLast : p = n - 2 := by
          have hfull := hleaf.1
          omega
        subst p
        have hsub : n - 2 + 1 = n - 1 := by omega
        have hchildC :
            (z.1.2.1 (L3.EWord.site ring root (n - 1))).ser.phase = .C := by
          simpa only [hsub] using hleaf.2.1
        have hchildLeaf :
            (z.1.2.1 (L3.EWord.site ring root (n - 1))).ser.probe =
              .LEAF_OK := by
          simpa only [hsub] using hleaf.2.2.1
        have hchildOff :
            (z.1.2.1 (L3.EWord.site ring root (n - 1))).ser.wphase =
              .OFF := by
          simpa only [hsub] using hleaf.2.2.2
        have hstep := bankWordRenewalSoftLeafAdmissionStep
          ring root s z hn hf hrun hwaiting.1
          hchildC hchildLeaf hchildOff hflags.1 hflags.2
        refine ⟨hstep.1, ?_, ?_⟩
        · rw [hstep.2.1, hstep.2.2.1]
          omega
        · intro hne
          have heq := hstep.2.1.trans hstep.2.2.1.symm
          exact False.elim (hne heq)

end

section
open Classical

/-- Width port of `bankWordRenewalSoftInactiveRootOutgoingBStep`: the BANK band premise is replaced by `5 ≤ n`, and the renewal constants are those of the compiled width t (lease 8t+4, quota 2t+1). Consumer: `widthWordRenewalSoftInactiveAllEdgesStep`.
 An inactive ROOT_OUT B/S2R service cannot create RUNNING/B/CURRENT
    without a REQUESTED S1. A genuine S6 instead makes IDLE/C.
    Consumer: inactive ROOT_OUT B row of the all-edge R10a induction. -/
theorem widthWordRenewalSoftInactiveRootOutgoingBStep {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hn : 5 ≤ n)
    (hsmallFive : 5 ≤ n)
    (hs : WidthWordSerializerRootClass ring hsmallFive root s)
    (z : BankWordRenewalPostSOne ring root s)
    (hsourceB : (z.1.2.1 root).ser.phase = .B)
    (hnotRequested : (z.1.2.1 root).ser.cert ≠ .REQUESTED)
    (hinactive :
      ¬ ((z.1.2.1 root).ser.cert = .RUNNING ∧
        (z.1.2.1 root).ser.phase = .B ∧
        (z.1.2.1 root).ser.wphase = .CURRENT)) :
    BankWordRenewalSoftShape ring root
      (bankWordEpochNext ring root z.1 root) ∧
    bankWordRenewalSoftRootedPosition ring root
      (bankWordEpochNext ring root z.1 root) =
      bankWordRenewalSoftRootedPosition ring root z.1 := by
  have hflags := widthWordRenewalSoftOutgoingFlags
    ring root s hn hsmallFive hs z
  have hrootSer :
      ((bankWordEpochNext ring root z.1 root).2.1 root).ser =
        (serW (z.1.2.1 root)
          (z.1.2.1 (ring.rightNeighbor root))).x := by
    change ((phiW ring z.1.2.1 root) root).ser = _
    rw [phiW_ser_source]
  have hnextInactive :
      ¬ (((bankWordEpochNext ring root z.1 root).2.1 root).ser.cert =
          .RUNNING ∧
        ((bankWordEpochNext ring root z.1 root).2.1 root).ser.phase =
          .B ∧
        ((bankWordEpochNext ring root z.1 root).2.1 root).ser.wphase =
          .CURRENT) := by
    intro hnext
    rw [hrootSer] at hnext
    cases htarget :
      (z.1.2.1 (ring.rightNeighbor root)).ser.phase <;>
      cases hout : (z.1.2.1 root).ser.out <;>
      simp [serW, serializerStep, ProjW.lift,
        hflags.1, hflags.2, hsourceB, hnotRequested,
        htarget, hout] at hnext <;>
      first
        | exact hinactive hnext
        | exact hinactive ⟨hnext.1, hsourceB, hnext.2⟩
        | (apply hinactive
           repeat' (split at hnext)
           all_goals (try simp only [serChallengeWrite] at hnext)
           all_goals first
             | exact hnext
             | exact ⟨hnext.1, hsourceB, hnext.2⟩
             | exact ⟨hnext.1, hsourceB, hnext.2.2⟩)
  have hposOld :
      bankWordRenewalSoftRootedPosition ring root z.1 = 0 := by
    simp [bankWordRenewalSoftRootedPosition, hinactive]
  have hposNew :
      bankWordRenewalSoftRootedPosition ring root
        (bankWordEpochNext ring root z.1 root) = 0 := by
    simp [bankWordRenewalSoftRootedPosition, hnextInactive]
  exact ⟨(by intro h; exact False.elim (hnextInactive h)),
    hposNew.trans hposOld.symm⟩

end

section
open Classical

/-- Width port of `bankWordRenewalSoftTerminalObservedIncomingStep`: the BANK band premise is replaced by `5 ≤ n`, and the renewal constants are those of the compiled width t (lease 8t+4, quota 2t+1). Consumer: `widthWordRenewalSoftForwardAllEdgesStep`.
 A terminal C/LEAF_OK/OFF has already been observed. A later
    ROOT_IN S5 merely frames its serializer records; it cannot
    alter the already-paid last forward position.
    Consumer: terminal WAIT/LEAF_OK incoming-root all-edge row. -/
theorem widthWordRenewalSoftTerminalObservedIncomingStep {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hn : 5 ≤ n)
    (hsmallFive : 5 ≤ n)
    (hs : WidthWordSerializerRootClass ring hsmallFive root s)
    (z : BankWordRenewalPostSOne ring root s)
    (hf : BankWordRenewalSoftForwardShape ring root z.1 (n - 2))
    (hactive :
      (z.1.2.1 root).ser.cert = .RUNNING ∧
      (z.1.2.1 root).ser.phase = .B ∧
      (z.1.2.1 root).ser.wphase = .CURRENT)
    (hchildC :
      (z.1.2.1 (L3.EWord.site ring root (n - 1))).ser.phase = .C)
    (hchildObserved :
      (z.1.2.1 (L3.EWord.site ring root (n - 1))).ser.probe =
        .LEAF_OK) :
    BankWordRenewalSoftShape ring root
      (bankWordEpochNext ring root z.1
        (L3.EWord.site ring root (n - 1))) ∧
    bankWordRenewalSoftRootedPosition ring root
      (bankWordEpochNext ring root z.1
        (L3.EWord.site ring root (n - 1))) =
      bankWordRenewalSoftRootedPosition ring root z.1 := by
  have hpred :
      ring.rightNeighbor (L3.EWord.site ring root (n - 1)) =
        root :=
    L3.EWord.validationSeamNeighbor ring root
      (L3.EWord.site ring root (n - 1)) rfl
  have hnonIdle : (z.1.2.1 root).ser.cert ≠ .IDLE := by
    intro h
    have hbad := hactive.1.symm.trans h
    cases hbad
  have hnonPending :
      (z.1.2.1 (L3.EWord.site ring root (n - 1))).ser.probe ≠
        .PENDING := by
    intro h
    have hbad := hchildObserved.symm.trans h
    cases hbad
  have hflags := widthWordRenewalSoftIncomingFlags
    ring root (L3.EWord.site ring root (n - 1))
    s hn hsmallFive hs z
    (L3.EWord.validationSeamNotRoot ring root
      (L3.EWord.site ring root (n - 1))
      (by omega : 3 ≤ n) rfl) hpred
  have hshapeOld : BankWordRenewalSoftShape ring root z.1 := by
    intro _
    exact Or.inl ⟨n - 2, hf⟩
  exact bankWordRenewalSoftIncomingQuietFrame
    ring root (L3.EWord.site ring root (n - 1))
    z.1 hn hpred hnonIdle
    (Or.inr ⟨hchildC, hnonPending⟩)
    hflags.1 hflags.2 hshapeOld

end

section
open Classical

/-- Width port of `bankWordRenewalSoftInactiveAllEdgesStep`: the BANK band premise is replaced by `5 ≤ n`, and the renewal constants are those of the compiled width t (lease 8t+4, quota 2t+1). Consumer: `widthWordRenewalSoftShapeStep`.
 When the rooted soft activity guard is false, an INTERNAL
    or ROOT_IN service cannot create it, and a ROOT_OUT service
    either performs S1/SR or stays inactive on B/S2R/S6.
    Hence the position remains zero on every physical edge.
    Consumer: inactive half of bankWordRenewalSoftShapeStep. -/
theorem widthWordRenewalSoftInactiveAllEdgesStep {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hn : 5 ≤ n)
    (hsmallFive : 5 ≤ n)
    (hs : WidthWordSerializerRootClass ring hsmallFive root s)
    (z : BankWordRenewalPostSOne ring root s)
    (e : Fin n)
    (hinactive :
      ¬ ((z.1.2.1 root).ser.cert = .RUNNING ∧
        (z.1.2.1 root).ser.phase = .B ∧
        (z.1.2.1 root).ser.wphase = .CURRENT)) :
    BankWordRenewalSoftShape ring root
      (bankWordEpochNext ring root z.1 e) ∧
    bankWordRenewalSoftRootedPosition ring root
      (bankWordEpochNext ring root z.1 e) =
      bankWordRenewalSoftRootedPosition ring root z.1 := by
  rcases bankWordRenewalSoftEdgeGeometry ring root e hn with
    hroot | hseam | hinter
  · subst e
    by_cases hrequested :
        (z.1.2.1 root).ser.cert = .REQUESTED
    · have hcase :
          ((z.1.2.1 root).ser.cert = .REQUESTED ∧
            0 < (z.1.2.1 root).siLease.val) ∨
          ((z.1.2.1 root).ser.cert = .REQUESTED ∧
            (z.1.2.1 root).siLease.val = 0) ∨
          (((z.1.2.1 root).ser.cert = .IDLE ∨
            (z.1.2.1 root).ser.cert = .RUNNING) ∧
           ((z.1.2.1 root).ser.phase = .C ∨
            (z.1.2.1 root).ser.phase = .F)) := by
        by_cases hzero : (z.1.2.1 root).siLease.val = 0
        · exact Or.inr (Or.inl ⟨hrequested, hzero⟩)
        · exact Or.inl ⟨hrequested, (by omega)⟩
      exact widthWordRenewalSoftRootEntryStep
        ring root s hn hsmallFive hs z hcase
    · cases hphase : (z.1.2.1 root).ser.phase with
      | B =>
          exact widthWordRenewalSoftInactiveRootOutgoingBStep
            ring root s hn hsmallFive hs z hphase hrequested
            hinactive
      | C =>
          have hcert :
              (z.1.2.1 root).ser.cert = .IDLE ∨
              (z.1.2.1 root).ser.cert = .RUNNING := by
            cases hc : (z.1.2.1 root).ser.cert with
            | IDLE => exact Or.inl rfl
            | REQUESTED => exact False.elim (hrequested hc)
            | RUNNING => exact Or.inr rfl
          exact widthWordRenewalSoftRootEntryStep
            ring root s hn hsmallFive hs z
            (Or.inr (Or.inr ⟨hcert, Or.inl hphase⟩))
      | F =>
          have hcert :
              (z.1.2.1 root).ser.cert = .IDLE ∨
              (z.1.2.1 root).ser.cert = .RUNNING := by
            cases hc : (z.1.2.1 root).ser.cert with
            | IDLE => exact Or.inl rfl
            | REQUESTED => exact False.elim (hrequested hc)
            | RUNNING => exact Or.inr rfl
          exact widthWordRenewalSoftRootEntryStep
            ring root s hn hsmallFive hs z
            (Or.inr (Or.inr ⟨hcert, Or.inr hphase⟩))
  · rcases hseam with ⟨he, hpred⟩
    have hnotRoot :=
      L3.EWord.validationSeamNotRoot ring root e
        (by omega : 3 ≤ n) he
    by_cases hidle : (z.1.2.1 root).ser.cert = .IDLE
    · have hflags := widthWordRenewalSoftIncomingFlags
        ring root e s hn hsmallFive hs z hnotRoot hpred
      have hstep := bankWordRenewalSoftRootIncomingStep
        ring root e z.1 (by omega : 3 ≤ n) hpred
        hflags.1 hflags.2 hidle
      exact ⟨hstep.1, hstep.2.1⟩
    · exact widthWordRenewalSoftInactiveIncomingStep
        ring root e s hn hsmallFive hs z hnotRoot hpred
        hidle hinactive
  · rcases hinter with ⟨k, hk, hbound, he, hnotRoot,
      hnotNeighborRoot⟩
    exact bankWordRenewalSoftInactiveInternalStep
      ring root e z.1 hnotRoot hnotNeighborRoot hinactive

end

section
open Classical

/-- Width port of `bankWordRenewalSoftForwardLeafSeamStep`: the BANK band premise is replaced by `5 ≤ n`, and the renewal constants are those of the compiled width t (lease 8t+4, quota 2t+1). Consumer: `widthWordRenewalSoftForwardAllEdgesStep`.
 R10a S-frontier physical row; consumer: all-edges closure. -/
theorem widthWordRenewalSoftForwardLeafSeamStep {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hn : 5 ≤ n)
    (hsmallFive : 5 ≤ n)
    (hs : WidthWordSerializerRootClass ring hsmallFive root s)
    (z : BankWordRenewalPostSOne ring root s)
    (hf : BankWordRenewalSoftForwardShape ring root z.1 (n - 2))
    (hrun : (z.1.2.1 root).ser.cert = .RUNNING)
    (hwait :
      (z.1.2.1 (L3.EWord.site ring root (n - 2))).ser.out =
        .WAIT)
    (hchildC :
      (z.1.2.1 (L3.EWord.site ring root (n - 1))).ser.phase =
        .C)
    (hchildPending :
      (z.1.2.1 (L3.EWord.site ring root (n - 1))).ser.probe =
        .PENDING) :
    BankWordRenewalSoftShape ring root
      (bankWordEpochNext ring root z.1
        (L3.EWord.site ring root (n - 1))) ∧
    bankWordRenewalSoftRootedPosition ring root
      (bankWordEpochNext ring root z.1
        (L3.EWord.site ring root (n - 1))) =
      bankWordRenewalSoftRootedPosition ring root z.1 ∧
    bankWordRenewalSoftRootedPosition ring root z.1 =
      n - 1 ∧
    bankWordRenewalSoftRootedChosen ring root s z =
      L3.EWord.site ring root (n - 2) := by
  have hpred :
      ring.rightNeighbor (L3.EWord.site ring root (n - 1)) =
        root :=
    L3.EWord.validationSeamNeighbor ring root
      (L3.EWord.site ring root (n - 1)) rfl
  have hsourceNonroot :=
    L3.EWord.validationSeamNotRoot ring root
      (L3.EWord.site ring root (n - 1)) (by omega : 3 ≤ n) rfl
  have hflags := widthWordRenewalSoftIncomingFlags
    ring root (L3.EWord.site ring root (n - 1))
    s hn hsmallFive hs z hsourceNonroot hpred
  have hstep := bankWordRenewalSoftRootIncomingLeafStep
    ring root s z hn hf hrun hwait hchildC hchildPending
    hflags.1 hflags.2
  exact ⟨hstep.1, hstep.2.2.2.1,
    hstep.2.2.2.2.1, hstep.2.2.2.2.2⟩

end

section
open Classical

/-- Width port of `bankWordRenewalSoftForwardAllEdgesStep`: the BANK band premise is replaced by `5 ≤ n`, and the renewal constants are those of the compiled width t (lease 8t+4, quota 2t+1). Consumer: `widthWordRenewalSoftShapeStep`.
 Exhaustive rooted-forward physical edge step. Positive position
    increments occur only on the OLD nominated root-attached
    challenge/admission edge. S3 observation and arbitrary
    inherited suffix cleanup cannot add another charge.
    Consumer: forward branch of R10a hfail all-edges closure. -/
theorem widthWordRenewalSoftForwardAllEdgesStep {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hn : 5 ≤ n)
    (hsmallFive : 5 ≤ n)
    (hs : WidthWordSerializerRootClass ring hsmallFive root s)
    (z : BankWordRenewalPostSOne ring root s)
    (e : Fin n) (p : Nat)
    (hf : BankWordRenewalSoftForwardShape ring root z.1 p)
    (hactive :
      (z.1.2.1 root).ser.cert = .RUNNING ∧
      (z.1.2.1 root).ser.phase = .B ∧
      (z.1.2.1 root).ser.wphase = .CURRENT) :
    BankWordRenewalSoftShape ring root
      (bankWordEpochNext ring root z.1 e) ∧
    bankWordRenewalSoftRootedPosition ring root
      (bankWordEpochNext ring root z.1 e) ≤
      bankWordRenewalSoftRootedPosition ring root z.1 + 1 ∧
    (bankWordRenewalSoftRootedPosition ring root
        (bankWordEpochNext ring root z.1 e) ≠
      bankWordRenewalSoftRootedPosition ring root z.1 →
      e = bankWordRenewalSoftRootedChosen ring root s z) := by
  have hshape : BankWordRenewalSoftShape ring root z.1 := by
    intro _
    exact Or.inl ⟨p, hf⟩
  rcases bankWordRenewalSoftForwardEdgeCases
      ring root e z.1 p hn hf with hroot | hseam | hinter
  · subst e
    by_cases hpzero : p = 0
    · have hfzero :
          BankWordRenewalSoftForwardShape ring root z.1 0 := by
        simpa only [hpzero] using hf
      exact widthWordRenewalSoftRootFirstStep
        ring root s hn hsmallFive hs z hfzero hactive.1
    · have hpositive : 0 < p := by omega
      have hrootOld := hf.completed 0 hpositive
      have hrootB : (z.1.2.1 root).ser.phase = .B := by
        simpa only [L3.EWord.siteZero] using hrootOld.1
      have hrootDone : (z.1.2.1 root).ser.out = .DONE := by
        simpa only [L3.EWord.siteZero] using hrootOld.2.1
      have hfirstB :
          (z.1.2.1 (ring.rightNeighbor root)).ser.phase =
            .B := by
        by_cases hpone : p = 1
        · simpa only [hpone, L3.EWord.siteOne] using
            hf.parentPhase
        · have hfirst := hf.completed 1 (by omega)
          simpa only [L3.EWord.siteOne] using hfirst.1
      have hnotRequested :
          (z.1.2.1 root).ser.cert ≠ .REQUESTED := by
        intro h
        have hbad := hactive.1.symm.trans h
        cases hbad
      have hflags := widthWordRenewalSoftOutgoingFlags
        ring root s hn hsmallFive hs z
      have hstep := bankWordRenewalSoftOutgoingCoveredDoneFrame
        ring root root z.1 hn hrootB hrootDone
        hfirstB hnotRequested hflags.1 hflags.2 hshape
      refine ⟨hstep.1, ?_, ?_⟩
      · rw [hstep.2]
        omega
      · intro hneq
        exact False.elim (hneq hstep.2)
  · rcases hseam with ⟨he, _⟩
    subst e
    have hpred :
        ring.rightNeighbor (L3.EWord.site ring root (n - 1)) =
          root :=
      L3.EWord.validationSeamNeighbor ring root
        (L3.EWord.site ring root (n - 1)) rfl
    have hnotRoot :=
      L3.EWord.validationSeamNotRoot ring root
        (L3.EWord.site ring root (n - 1))
        (by omega : 3 ≤ n) rfl
    have hflags := widthWordRenewalSoftIncomingFlags
      ring root (L3.EWord.site ring root (n - 1))
      s hn hsmallFive hs z hnotRoot hpred
    have hpres :
        BankWordRenewalSoftShape ring root
          (bankWordEpochNext ring root z.1
            (L3.EWord.site ring root (n - 1))) ∧
        bankWordRenewalSoftRootedPosition ring root
          (bankWordEpochNext ring root z.1
            (L3.EWord.site ring root (n - 1))) =
        bankWordRenewalSoftRootedPosition ring root z.1 := by
      by_cases hbefore : p + 2 < n
      · have hstep := bankWordRenewalSoftForwardSeamOutsideFront
          ring root s z p hn hf hactive hbefore
          hflags.1 hflags.2
        exact ⟨hstep.1, hstep.2.1⟩
      · have hterminal : p + 2 = n := by
          have hb := hf.pivotBound
          omega
        rcases hf.front with hzero | hpositive
        · have hbad : False := by omega
          exact False.elim hbad
        · rcases hpositive.2 with hnew | hwaiting
          · have hstep := bankWordRenewalSoftTerminalNewIncomingStep
              ring root s z p hn hf hactive hterminal hnew
              hflags.1 hflags.2
            exact ⟨hstep.1, hstep.2.1⟩
          · rcases hwaiting.2 with hpending | hinternal | hleaf
            · have hpLast : p = n - 2 := by omega
              have hsub : p + 1 = n - 1 := by omega
              have hfLast :
                  BankWordRenewalSoftForwardShape ring root
                    z.1 (n - 2) := by
                simpa only [hpLast] using hf
              have hwaitLast :
                  (z.1.2.1 (L3.EWord.site ring root (n - 2))).ser.out =
                    .WAIT := by
                simpa only [hpLast] using hwaiting.1
              have hchildC :
                  (z.1.2.1 (L3.EWord.site ring root (n - 1))).ser.phase =
                    .C := by
                simpa only [hsub] using hpending.1
              have hchildPending :
                  (z.1.2.1 (L3.EWord.site ring root (n - 1))).ser.probe =
                    .PENDING := by
                simpa only [hsub] using hpending.2.1
              have hstep := widthWordRenewalSoftForwardLeafSeamStep
                ring root s hn hsmallFive hs z hfLast hactive.1
                hwaitLast hchildC hchildPending
              exact ⟨hstep.1, hstep.2.1⟩
            · have hbad : False := by omega
              exact False.elim hbad
            · have hpLast : p = n - 2 := by omega
              have hsub : p + 1 = n - 1 := by omega
              have hfLast :
                  BankWordRenewalSoftForwardShape ring root
                    z.1 (n - 2) := by
                simpa only [hpLast] using hf
              have hchildC :
                  (z.1.2.1 (L3.EWord.site ring root (n - 1))).ser.phase =
                    .C := by
                simpa only [hsub] using hleaf.2.1
              have hchildObserved :
                  (z.1.2.1 (L3.EWord.site ring root (n - 1))).ser.probe =
                    .LEAF_OK := by
                simpa only [hsub] using hleaf.2.2.1
              exact widthWordRenewalSoftTerminalObservedIncomingStep
                ring root s hn hsmallFive hs z hfLast hactive
                hchildC hchildObserved
    refine ⟨hpres.1, ?_, ?_⟩
    · rw [hpres.2]
      omega
    · intro hneq
      exact False.elim (hneq hpres.2)
  · rcases hinter with ⟨k, hkpositive, hinside, he, hcases⟩
    subst e
    rcases hcases with hcovered | hpivot | hchild | hfar
    · have hstep := widthWordRenewalSoftForwardCoveredStep
        ring root s hn hsmallFive hs z p k hf hactive hshape
        hkpositive hcovered.1
      refine ⟨hstep.1, ?_, ?_⟩
      · rw [hstep.2.1]
        omega
      · intro hneq
        exact False.elim (hneq hstep.2.1)
    · have hp : 0 < p := by omega
      have hk : k = p := hpivot.1
      subst k
      exact widthWordRenewalSoftForwardParentStep
        ring root s hn hsmallFive hs z p hp hf hactive.1
    · have hk : k = p + 1 := hchild
      by_cases hnew :
          (z.1.2.1 (L3.EWord.site ring root p)).ser.out = .NEW
      · have hfar : p < k := by omega
        have hstep := bankWordRenewalSoftForwardNewChildStep
          ring root s z p k hf hactive hfar hnew hinside
        refine ⟨hstep.1, ?_, ?_⟩
        · rw [hstep.2.1]
          omega
        · intro hneq
          exact False.elim (hneq hstep.2.1)
      · have hwait :
            (z.1.2.1 (L3.EWord.site ring root p)).ser.out =
              .WAIT := by
          rcases hf.front with hzero | hpositive
          · exact hzero.2.1
          · rcases hpositive.2 with hnewOld | hwaiting
            · exact False.elim (hnew hnewOld)
            · exact hwaiting.1
        have hchildCases :
            ((z.1.2.1 (L3.EWord.site ring root (p + 1))).ser.phase =
                .C ∧
              (z.1.2.1 (L3.EWord.site ring root (p + 1))).ser.probe =
                .PENDING ∧
              (z.1.2.1 (L3.EWord.site ring root (p + 1))).ser.wphase =
                .CURRENT) ∨
            ((z.1.2.1 (L3.EWord.site ring root (p + 1))).ser.phase =
                .C ∧
              (z.1.2.1 (L3.EWord.site ring root (p + 1))).ser.probe =
                .INTERNAL_OK ∧
              (z.1.2.1 (L3.EWord.site ring root (p + 1))).ser.wphase =
                .CURRENT) := by
          rcases hf.front with hzero | hpositive
          · rcases hzero.2.2.2.2 with hpending | hinternal
            · exact Or.inl ⟨hzero.2.2.1, hpending,
                hzero.2.2.2.1⟩
            · exact Or.inr ⟨hzero.2.2.1, hinternal,
                hzero.2.2.2.1⟩
          · rcases hpositive.2 with hnewOld | hwaiting
            · exact False.elim (hnew hnewOld)
            · rcases hwaiting.2 with hpending | hinternal | hleaf
              · exact Or.inl hpending
              · exact Or.inr ⟨hinternal.2.1, hinternal.2.2.1,
                  hinternal.2.2.2⟩
              · have hbad : False := by omega
                exact False.elim hbad
        have hsourceNotRoot :
            L3.EWord.site ring root (p + 1) ≠ root :=
          L3.EWord.validationPositiveSiteNotRoot
            ring root (p + 1) (by omega) (by omega)
        have htargetNotRoot :
            ring.rightNeighbor (L3.EWord.site ring root (p + 1)) ≠
              root := by
          rw [L3.EWord.siteSuccessor]
          exact L3.EWord.validationPositiveSiteNotRoot
            ring root (p + 2) (by omega) (by omega)
        have hflags := widthWordRenewalSoftInternalFlags
          ring root (L3.EWord.site ring root (p + 1))
          s hn hsmallFive hs z hsourceNotRoot htargetNotRoot
        have hpres :
            BankWordRenewalSoftShape ring root
              (bankWordEpochNext ring root z.1
                (L3.EWord.site ring root k)) ∧
            bankWordRenewalSoftRootedPosition ring root
              (bankWordEpochNext ring root z.1
                (L3.EWord.site ring root k)) =
            bankWordRenewalSoftRootedPosition ring root z.1 := by
          rcases hchildCases with hpending | hinternal
          · have hstep := bankWordRenewalSoftPendingObservationStep
              ring root s z p hn hf hactive (by omega)
              hwait hpending.1 hpending.2.1 hpending.2.2
              hflags.1 hflags.2
            simpa only [hk] using
              ⟨hstep.1, hstep.2.1⟩
          · have hstep := bankWordRenewalSoftInternalAnsweredChildStep
              ring root s z p hn hf hactive (by omega)
              hwait hinternal.1 hinternal.2.1 hinternal.2.2
              hflags.1 hflags.2
            simpa only [hk] using
              ⟨hstep.1, hstep.2.1⟩
        refine ⟨hpres.1, ?_, ?_⟩
        · rw [hpres.2]
          omega
        · intro hneq
          exact False.elim (hneq hpres.2)
    · have hstep := bankWordRenewalSoftForwardSuffixStep
        ring root s z p k hf hactive hfar hinside
      refine ⟨hstep.1, ?_, ?_⟩
      · rw [hstep.2.1]
        omega
      · intro hneq
        exact False.elim (hneq hstep.2.1)

end

section
open Classical

/-- Width port of `bankWordRenewalSoftShapeStep`: the BANK band premise is replaced by `5 ≤ n`, and the renewal constants are those of the compiled width t (lease 8t+4, quota 2t+1). Consumer: `widthWordRenewalSoftRootedPositionHitStep`, `widthWordRetryPrefixStep`.
 Exact selected-letter S-frontier preservation on every
    physical edge: the rooted soft normal shape N persists;
    the charged position moves by at most one; any change
    is on the old-state nominated edge. Consumer: R10a
    serializer first-H lower cover in 5B hfail. -/
theorem widthWordRenewalSoftShapeStep {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hn : 5 ≤ n)
    (hsmallFive : 5 ≤ n)
    (hs : WidthWordSerializerRootClass ring hsmallFive root s)
    (z : BankWordRenewalPostSOne ring root s)
    (e : Fin n)
    (hshape : BankWordRenewalSoftShape ring root z.1) :
    BankWordRenewalSoftShape ring root
      (bankWordEpochNext ring root z.1 e) ∧
    bankWordRenewalSoftRootedPosition ring root
      (bankWordEpochNext ring root z.1 e) ≤
      bankWordRenewalSoftRootedPosition ring root z.1 + 1 ∧
    (bankWordRenewalSoftRootedPosition ring root
        (bankWordEpochNext ring root z.1 e) ≠
      bankWordRenewalSoftRootedPosition ring root z.1 →
      e = bankWordRenewalSoftRootedChosen ring root s z) := by
  by_cases hactive :
      (z.1.2.1 root).ser.cert = .RUNNING ∧
      (z.1.2.1 root).ser.phase = .B ∧
      (z.1.2.1 root).ser.wphase = .CURRENT
  · rcases hshape hactive with hforward | hreturn
    · obtain ⟨p, hf⟩ := hforward
      exact widthWordRenewalSoftForwardAllEdgesStep
        ring root s hn hsmallFive hs z e p hf hactive
    · obtain ⟨q, hr⟩ := hreturn
      exact widthWordRenewalSoftReturnAllEdgesStep
        ring root s hn hsmallFive hs z e q hr
  · have hstep := widthWordRenewalSoftInactiveAllEdgesStep
      ring root s hn hsmallFive hs z e hactive
    refine ⟨hstep.1, ?_, ?_⟩
    · rw [hstep.2]
      omega
    · intro hneq
      exact False.elim (hneq hstep.2)

end

section
open Classical
open L3.GrantDrainEntrance
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

/-- Width port of `bankWordRenewalSoftRootedPositionHitStep`: the BANK band premise is replaced by `5 ≤ n`, and the renewal constants are those of the compiled width t (lease 8t+4, quota 2t+1). Consumer: `widthWordRetryPrefixStep`.
 Consumer: R10 serializer nominated-hit charging. On a
genuine reachable post-S1 physical edge, rooted soft-position
growth is at most the indicator of the OLD state's nominated
edge. This is an upper bound, not a claim that a hit progresses. -/
theorem widthWordRenewalSoftRootedPositionHitStep {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hn : 5 ≤ n)
    (hsmallFive : 5 ≤ n)
    (hs : WidthWordSerializerRootClass ring hsmallFive root s)
    (z : BankWordRenewalPostSOne ring root s)
    (e : Fin n)
    (hshape : BankWordRenewalSoftShape ring root z.1) :
    bankWordRenewalSoftRootedPosition ring root
        (bankWordRenewalNext ring root s z e).1 ≤
      bankWordRenewalSoftRootedPosition ring root z.1 +
        (if e = bankWordRenewalSoftRootedChosen ring root s z
          then 1 else 0) := by
  have hstep := widthWordRenewalSoftShapeStep
    ring root s hn hsmallFive hs z e hshape
  by_cases he :
      e = bankWordRenewalSoftRootedChosen ring root s z
  · rw [if_pos he]
    exact hstep.2.1
  · rw [if_neg he]
    by_cases hsame :
        bankWordRenewalSoftRootedPosition ring root
            (bankWordRenewalNext ring root s z e).1 =
          bankWordRenewalSoftRootedPosition ring root z.1
    · rw [hsame]
      exact Nat.le_refl _
    · exact False.elim (he (hstep.2.2 hsame))

end

end L3.RenewalReferenceClock

#print axioms L3.RenewalReferenceClock.widthWordRootStartCountNextLapCost
#print axioms L3.RenewalReferenceClock.widthWordEpochGenuineCostOfLapCount
#print axioms L3.RenewalReferenceClock.widthWordEpochPostSOneWorkerClockOfLapCount
#print axioms L3.RenewalReferenceClock.widthWordEpochFixedRoot
#print axioms L3.RenewalReferenceClock.widthWordEpochFixedRootNext
#print axioms L3.RenewalReferenceClock.widthWordEpochPostLatchRootFactsStep
#print axioms L3.RenewalReferenceClock.widthWordEpochPostLatchRootFactsReachable
#print axioms L3.RenewalReferenceClock.widthWordRenewalLineageQuietOfEverSix
#print axioms L3.RenewalReferenceClock.widthWordEpochLapInvariantStep
#print axioms L3.RenewalReferenceClock.widthWordEpochLapInvariantFrom
#print axioms L3.RenewalReferenceClock.widthWordEpochLapCountOfLineageStep
#print axioms L3.RenewalReferenceClock.widthWordEpochPostSOneWorkerClockOfLineageStep
#print axioms L3.RenewalReferenceClock.widthWordRenewalFreshAttemptCostOfLineageStep
#print axioms L3.RenewalReferenceClock.widthWordRenewalLineageQuietStepOfMovingRows
#print axioms L3.RenewalReferenceClock.widthWordEpochPostSOneWorkerClockOfMovingRows
#print axioms L3.RenewalReferenceClock.widthWordRenewalFreshAttemptCostOfMovingRows
#print axioms L3.RenewalReferenceClock.widthWordRenewalLineageRootMovingStepHolds
#print axioms L3.RenewalReferenceClock.widthWordEpochPostSOneWorkerClockOfInternalRows
#print axioms L3.RenewalReferenceClock.widthWordRenewalWaveInternalReturnRootLineageStep
#print axioms L3.RenewalReferenceClock.widthWordRenewalWaveInternalReturnMoveQuietStep
#print axioms L3.RenewalReferenceClock.widthWordRenewalWaveInternalFrontierInternalQuietStep
#print axioms L3.RenewalReferenceClock.widthWordRenewalWaveInternalFrontierLeafQuietStep
#print axioms L3.RenewalReferenceClock.widthWordRenewalWaveSelectedRemoteQuietStep
#print axioms L3.RenewalReferenceClock.widthWordRenewalWaveInternalChildPrechallengeQuietStep
#print axioms L3.RenewalReferenceClock.widthWordRenewalWaveInternalFrontierParentQuietStep
#print axioms L3.RenewalReferenceClock.widthWordRenewalWaveInternalChallengedChildQuietStep
#print axioms L3.RenewalReferenceClock.widthWordRenewalWaveInternalReturnCoveredQuietStep
#print axioms L3.RenewalReferenceClock.widthWordRenewalWaveSelectedInternalMovingQuietStep
#print axioms L3.RenewalReferenceClock.widthWordRenewalLineageInternalMovingStepHolds
#print axioms L3.RenewalReferenceClock.widthWordEpochPostSOneWorkerClockHolds
#print axioms L3.RenewalReferenceClock.widthWordRenewalFreshAttemptCostHolds
#print axioms L3.RenewalReferenceClock.widthWordRenewalFreshFourCostHoldsOfFailure
#print axioms L3.RenewalReferenceClock.widthWordEpochSOneReachedOfRootTicketOrigin
#print axioms L3.RenewalReferenceClock.widthWordEpochSOneReachedOfGenuine
#print axioms L3.RenewalReferenceClock.widthWordEpochFreshCutOfFirstLaunch
#print axioms L3.RenewalReferenceClock.widthWordRenewalSoftReturnIncomingStep
#print axioms L3.RenewalReferenceClock.widthWordRenewalSoftReturnAllEdgesStep
#print axioms L3.RenewalReferenceClock.widthWordRenewalSoftForwardParentStep
#print axioms L3.RenewalReferenceClock.widthWordRenewalSoftInactiveRootOutgoingBStep
#print axioms L3.RenewalReferenceClock.widthWordRenewalSoftTerminalObservedIncomingStep
#print axioms L3.RenewalReferenceClock.widthWordRenewalSoftInactiveAllEdgesStep
#print axioms L3.RenewalReferenceClock.widthWordRenewalSoftForwardLeafSeamStep
#print axioms L3.RenewalReferenceClock.widthWordRenewalSoftForwardAllEdgesStep
#print axioms L3.RenewalReferenceClock.widthWordRenewalSoftShapeStep
#print axioms L3.RenewalReferenceClock.widthWordRenewalSoftRootedPositionHitStep
