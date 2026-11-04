import Leader.L3.Grant.BlockFrozenRenewalInstance
import Leader.L3.Grant.BlockFrozenRenewalCost
import Leader.L3.Grant.BlockFrozenRenewalSums

/-!
# G16: the G13 renewal argument on the frozen chain

## Skeleton of the G13 cold proof (BankTrialRenewal.lean)

KG = generic in the kernel (reads a stopped kernel, a terminal labelling and a
cost bound); CS = specific to `Counter.resetClockBankColdNext`; LR = generic in a
Clean local reference (reads only `BankTrialLocalClean` and the local trial
machine); AR = pure arithmetic.

1. `bankTrialRenewalColdSuccessMassLower` = `..._ofClearedWindow` (AR, mass
   abstract) applied to `bankTrialRenewalColdClearedWindowAnyH` (CS statement,
   assembled from the items below).
2. Exact first-stop partition `bankTrialRenewalColdFirstStopPartition` from the
   private `bankTrialColdGenericPrefixPartition` (KG; the cold statement adds a
   DEFECT term, CS).
3. Index masses and costs of a Clean reference: `bankTrialRenewalColdCleanIndexCutBounds`
   (LR), `..._SoundIndexCutBounds` (CS wrapper: soundness of the physical CLEAN
   terminal), `bankTrialRenewalColdEarlyCleanIndexMassBound` / `..ChargeBound`
   (CS sums over first stops, KG in shape).
4. Mass convolution `bankTrialColdMassConvolution`, late convolution
   `bankTrialColdLateConvolution`, geometric sum bound (AR, KG).
5. Reward / masked-cost bridges and `bankTrialRenewalColdGlobalMaskedWindow`
   (KG in shape; the cut window `bankTrialRenewalColdCleanMaskedWord` is LR but
   carries a grant-of-`D` case, CS).
6. Joint cost: `bankTrialColdJointFirstHitCost` (KG), `..JointIndexCharge`,
   `bankTrialColdMaskedCostConvolution` (KG in shape), fed by
   `Counter.resetClockBankColdStoppedCost` (CS: C.3 Bellman on the physical
   chain plus the C.2 retry kernel).
7. `bankTrialRenewalColdDefectMass...` (CS, vanishes for the frozen chain).

Items 2-6 are ported kernel-generically in `GrantBlockFrozenRenewalTree.lean`
(copies of the private generic lemmas), `GrantBlockFrozenRenewalKernel.lean`
(the CLEAN / GRANT kernel record and items 2-6), `GrantBlockFrozenRenewalBridge.lean`
and `GrantBlockFrozenRenewalInstance.lean` (the local trial machine is the clamped
chain; the frozen kernel; proxy mass at most the frozen proxy mass), and
`GrantBlockFrozenRenewalCost.lean` (C.3 from `grantBlockFrozenLatchCanonicalBellman`,
strong-Markov composition with an explicit C.2 hypothesis).  This file holds the
arithmetic of item 1 with an abstract mass and the clock.

Missing fact (stated, not assumed): `GrantBlockFrozenRecoveryCost`, the C.2
recovery cost on the frozen chain.
-/

namespace L3

open Classical
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

set_option autoImplicit false
set_option Elab.async false

theorem grantBlockFrozenClearedWindowMassLower
    {n : Nat}
    (hn : 5 ≤ n)
    (hsmall : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hw : BankTrialLiveWindowNonalias n (ceilLogTwo n))
    (hlarge :
      2 * (compileAdvice (ceilLogTwo n)).bankLeaseCap ≤ n)
    (R L T W M : Nat)
    (hradius : (256 * R) ^ 2 ≤ n ∧
      n < (256 * (R + 1)) ^ 2)
    (hW : W = R * n / 8)
    (hL : 1024 * bankTrialRenewalWonCutoffThreshold
      n (ceilLogTwo n) ≤ L)
    (hwindow : W ≤ T)
    (hbudgetCold :
      W + bankTrialRenewalIndexWindowCount
        n (ceilLogTwo n) W * L ≤ T)
    (hL1 :
  W * (2 ^ (compileAdvice (ceilLogTwo n)).K) * n ^ T *
    bankTrialSuccessStageIndexSum (fun j =>
      (1024 * (L * 2 ^ (compileAdvice (ceilLogTwo n)).K -
        L - 2 ^ (compileAdvice (ceilLogTwo n)).K *
          ((8 * (compileAdvice (ceilLogTwo n)).b + 12) * n))) ^ j *
      (1023 * L) *
      (1024 * (L * 2 ^ (compileAdvice (ceilLogTwo n)).K)) ^
        (bankTrialRenewalIndexWindowCount
          n (ceilLogTwo n) W - (j + 1)))
      (bankTrialRenewalIndexWindowCount n (ceilLogTwo n) W) ≤
  (1024 * (L * 2 ^ (compileAdvice (ceilLogTwo n)).K)) ^
      (bankTrialRenewalIndexWindowCount n (ceilLogTwo n) W) *
    (W * (2 ^ (compileAdvice (ceilLogTwo n)).K) * M +
     n ^ T * bankTrialSuccessStageIndexSum (fun j =>
       n * ((2 * (compileAdvice (ceilLogTwo n)).bankLeaseCap +
          5 * (compileAdvice (ceilLogTwo n)).b + 13) +
          bankTrialRenewalIndexZeroCharge (ceilLogTwo n) +
          j * bankTrialRenewalIndexStepCharge (ceilLogTwo n)))
       (bankTrialRenewalIndexWindowCount n (ceilLogTwo n) W))) :
    51279921 * W * n ^ T ≤
      104857600 * (8 * (compileAdvice (ceilLogTwo n)).b + 13) *
        n * 2 ^ (compileAdvice (ceilLogTwo n)).K * M := by
  have hq : 3 ≤ ceilLogTwo n := by
    have hspec := (ceilLogTwo_spec n (by omega)).2
    by_cases hc : ceilLogTwo n ≤ 2
    · have hp := Nat.pow_le_pow_right
        (by decide : 0 < (2 : Nat)) hc
      have hfour : (2 : Nat) ^ 2 = 4 := by decide
      omega
    · omega
  have hpositive :
      0 < (compileAdvice (ceilLogTwo n)).K := by
    change 0 < 2 * ceilLogTwo n +
      productionKappa (ceilLogTwo n)
    omega
  have hK :
      (compileAdvice (ceilLogTwo n)).K <
        2 ^ (compileAdvice (ceilLogTwo n)).b :=
    Nat.lt_trans (Nat.lt_succ_self _)
      (compileAdvice_K_lt_two_pow_b (ceilLogTwo n) hq)
  have hquota := bankTrialRenewalIndexCompiledQuotas
    n R W hn hsmall hradius hW
  have hf :
      0 < n * bankTrialRenewalIndexStepCharge
        (ceilLogTwo n) := by
    apply Nat.mul_pos (by omega)
    unfold bankTrialRenewalIndexStepCharge
    omega
  have hquotaExpanded :
      n * bankTrialRenewalIndexColdCharge (ceilLogTwo n) +
        22517 * (n * bankTrialRenewalIndexStepCharge
          (ceilLogTwo n)) ≤ W := by
    simpa only [Nat.mul_add, Nat.mul_assoc, Nat.mul_left_comm,
      Nat.mul_comm] using hquota.2
  have hWpos : 0 < W := by
    have ht : 0 < 22517 *
        (n * bankTrialRenewalIndexStepCharge (ceilLogTwo n)) :=
      Nat.mul_pos (by decide) hf
    omega
  have hCle :
      n * bankTrialRenewalIndexColdCharge (ceilLogTwo n) ≤ W := by
    omega
  have hFloorBudget :
      22517 * (n * bankTrialRenewalIndexStepCharge
        (ceilLogTwo n)) ≤
      W - n * bankTrialRenewalIndexColdCharge
        (ceilLogTwo n) := by
    have hsub := Nat.sub_add_cancel hCle
    omega
  have hFloor :
      22517 ≤ bankTrialRenewalIndexWindowCount
        n (ceilLogTwo n) W := by
    unfold bankTrialRenewalIndexWindowCount
    exact grantBlockFrozenRenewalIndexFloorLower
      (W - n * bankTrialRenewalIndexColdCharge (ceilLogTwo n))
      (n * bankTrialRenewalIndexStepCharge (ceilLogTwo n))
      22517 hf hFloorBudget
  have hcover :
      (2 * (compileAdvice (ceilLogTwo n)).bankLeaseCap +
        5 * (compileAdvice (ceilLogTwo n)).b + 13) +
          bankTrialRenewalIndexZeroCharge (ceilLogTwo n) ≤
        bankTrialRenewalIndexColdCharge (ceilLogTwo n) := by
    calc
      _ = bankTrialRenewalIndexColdCharge (ceilLogTwo n) :=
        (bankTrialRenewalColdIndexChargeSplit (ceilLogTwo n)).symm
      _ ≤ _ := Nat.le_refl _
  have hcoverScaled :=
    Nat.mul_le_mul_left n hcover
  have hPpos :
      0 < 2 ^ (compileAdvice (ceilLogTwo n)).K :=
    Nat.two_pow_pos _
  have hBasePos :
      0 < 1024 * 2 ^ (compileAdvice (ceilLogTwo n)).K *
        ((8 * (compileAdvice (ceilLogTwo n)).b + 12) * n) :=
    Nat.mul_pos (Nat.mul_pos (by decide) hPpos)
      (Nat.mul_pos (by omega) (by omega))
  have hCutPos :
      0 < bankTrialRenewalWonCutoffThreshold
        n (ceilLogTwo n) := by
    have hbase :
        1024 * 2 ^ (compileAdvice (ceilLogTwo n)).K *
          ((8 * (compileAdvice (ceilLogTwo n)).b + 12) * n) ≤
        bankTrialRenewalWonCutoffThreshold
          n (ceilLogTwo n) := by
      unfold bankTrialRenewalWonCutoffThreshold
      exact Nat.le_max_right _ _
    exact Nat.lt_of_lt_of_le hBasePos hbase
  have hLpos : 0 < L := by
    have hm := Nat.mul_pos
      (by decide : 0 < (1024 : Nat)) hCutPos
    omega
  have hdenpos :
      0 < 1024 * (L * 2 ^ (compileAdvice (ceilLogTwo n)).K) :=
    Nat.mul_pos (by decide) (Nat.mul_pos hLpos hPpos)
  have hGap := bankTrialRenewalIndexCompiledGeometricBudget
    n R W
    (bankTrialRenewalIndexColdCharge (ceilLogTwo n))
    L hn hradius.1
    (grantBlockFrozenRenewalIndexConsumerWindowCap n R W hW) hL
  have hGapActual :
      bankTrialRenewalIndexWindowCount n (ceilLogTwo n) W *
        (1024 * (L + 2 ^ (compileAdvice (ceilLogTwo n)).K *
          ((8 * (compileAdvice (ceilLogTwo n)).b + 12) * n))) ≤
        (1024 * (L * 2 ^ (compileAdvice (ceilLogTwo n)).K)) /
          1024 := by
    simpa only [bankTrialRenewalIndexWindowCount,
      bankTrialRenewalIndexStepCharge] using hGap
  have hDenIdentity := bankTrialRenewalIndexLostDenIdentity
    n (ceilLogTwo n) L hpositive hL
  have hgeo (j : Nat)
      (hj : j < bankTrialRenewalIndexWindowCount
        n (ceilLogTwo n) W) :
      1023 *
        (1024 * (L * 2 ^ (compileAdvice (ceilLogTwo n)).K)) ^ j ≤
      1024 *
        (1024 * (L * 2 ^ (compileAdvice (ceilLogTwo n)).K -
          L - 2 ^ (compileAdvice (ceilLogTwo n)).K *
            ((8 * (compileAdvice (ceilLogTwo n)).b + 12) * n))) ^ j := by
    exact bankTrialRenewalIndexBernoulli
      (1024 * (L * 2 ^ (compileAdvice (ceilLogTwo n)).K -
        L - 2 ^ (compileAdvice (ceilLogTwo n)).K *
          ((8 * (compileAdvice (ceilLogTwo n)).b + 12) * n)))
      (1024 * (L + 2 ^ (compileAdvice (ceilLogTwo n)).K *
        ((8 * (compileAdvice (ceilLogTwo n)).b + 12) * n)))
      (1024 * (L * 2 ^ (compileAdvice (ceilLogTwo n)).K))
      (bankTrialRenewalIndexWindowCount n (ceilLogTwo n) W)
      j hDenIdentity hGapActual hj
  have hwin := hL1
  have hwinOpaque :
      W * (2 ^ (compileAdvice (ceilLogTwo n)).K) * n ^ T *
        bankTrialSuccessStageIndexSum (fun j =>
          (1024 * (L * 2 ^ (compileAdvice (ceilLogTwo n)).K -
            L - 2 ^ (compileAdvice (ceilLogTwo n)).K *
              ((8 * (compileAdvice (ceilLogTwo n)).b + 12) * n))) ^ j *
          (1023 * L) *
          (1024 * (L * 2 ^ (compileAdvice (ceilLogTwo n)).K)) ^
            (bankTrialRenewalIndexWindowCount
              n (ceilLogTwo n) W - (j + 1)))
          (bankTrialRenewalIndexWindowCount n (ceilLogTwo n) W) ≤
      (1024 * (L * 2 ^ (compileAdvice (ceilLogTwo n)).K)) ^
        (bankTrialRenewalIndexWindowCount n (ceilLogTwo n) W) *
        (W * (2 ^ (compileAdvice (ceilLogTwo n)).K) *
          M +
          n ^ T *
            bankTrialSuccessStageIndexSum (fun j =>
              n * ((2 * (compileAdvice (ceilLogTwo n)).bankLeaseCap +
                5 * (compileAdvice (ceilLogTwo n)).b + 13) +
                bankTrialRenewalIndexZeroCharge (ceilLogTwo n)) +
              j * (n * bankTrialRenewalIndexStepCharge
                (ceilLogTwo n)))
              (bankTrialRenewalIndexWindowCount
                n (ceilLogTwo n) W)) := by
    simpa only [bankTrialRenewalIndexStepCharge, Nat.mul_add,
      Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hwin
  have hDenShape :
      1024 * (L * 2 ^ (compileAdvice (ceilLogTwo n)).K) =
        1024 * L * 2 ^ (compileAdvice (ceilLogTwo n)).K := by
    simp only [Nat.mul_assoc]
  have hresult := grantBlockFrozenRenewalIndexVariableMassArithmetic
    W (n * bankTrialRenewalIndexStepCharge (ceilLogTwo n))
    (bankTrialRenewalIndexWindowCount n (ceilLogTwo n) W)
    (2 ^ (compileAdvice (ceilLogTwo n)).K)
    (n ^ T)
    M
    (n * bankTrialRenewalIndexColdCharge (ceilLogTwo n))
    (n * ((2 * (compileAdvice (ceilLogTwo n)).bankLeaseCap +
      5 * (compileAdvice (ceilLogTwo n)).b + 13) +
      bankTrialRenewalIndexZeroCharge (ceilLogTwo n)))
    L
    (1024 * (L * 2 ^ (compileAdvice (ceilLogTwo n)).K -
      L - 2 ^ (compileAdvice (ceilLogTwo n)).K *
        ((8 * (compileAdvice (ceilLogTwo n)).b + 12) * n)))
    (1024 * (L * 2 ^ (compileAdvice (ceilLogTwo n)).K))
    hWpos hf rfl hquota.1 hFloor
    hcoverScaled hDenShape hdenpos hgeo hwinOpaque
  simpa only [bankTrialRenewalIndexStepCharge,
    Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hresult

/-- The stopped cost of the frozen chain: the expected time to reach a
latched success or a Clean local reference, in the form
`costNumerator ≤ n ^ T * c` with the compiled coefficient
`c = (2 * lease cap + 5 * b + 13) * n` of the cold stopped cost. -/
def GrantBlockFrozenStoppedCost {n : Nat} (ring : DirectedRing n)
    (member : GrantBlockFamilyMember ring) (T : Nat) : Prop :=
  costNumerator (grantBlockFrozenKernel ring member).next
      (grantBlockFrozenKernel ring member).Terminal
      (grantBlockFrozenKernel ring member).start T ≤
    n ^ T * ((2 * (compileAdvice (ceilLogTwo n)).bankLeaseCap +
      5 * (compileAdvice (ceilLogTwo n)).b + 13) * n)

/-- The frozen local cold clock from the frozen stopped cost: the G13
renewal argument run on the frozen chain, with no transfer from the
physical cold chain.

Consumer: `grantBlockFrozenDirectMarginalOfLocalClock`. -/
theorem grantBlockFrozenLocalColdClockOfStoppedCost
    {n : Nat} (ring : DirectedRing n)
    (member : GrantBlockFamilyMember ring)
    (R L T W : Nat)
    (hcost : GrantBlockFrozenStoppedCost ring member T) :
    GrantBlockFrozenLocalColdClock ring member R L T W := by
  intro hn hsp hw hlarge hradius hW hL hWT hbudget
  have hL1 := (grantBlockFrozenKernel ring member).clearedWindow ring
    member.1 (grantBlockFrozenKernelCleanSound ring member) hn hsp hw
    hlarge L (bankTrialRenewalIndexWindowCount n (ceilLogTwo n) W) T W
    hL hWT hbudget hcost
  have harith := grantBlockFrozenClearedWindowMassLower hn hsp hw hlarge
    R L T W _ hradius hW hL hWT hbudget hL1
  exact Nat.le_trans harith
    (Nat.mul_le_mul_left _
      (grantBlockFrozenKernelProxyMassLe ring member T W))

/-- The frozen local cold clock for a buffered member, from the frozen
C.2 recovery cost only: C.3 is the canonical frozen Bellman inequality,
the renewal window is the G13 chain run on the frozen kernel.

Consumer: `grantBlockFrozenDirectMarginalOfLocalClock`. -/
theorem grantBlockFrozenLocalColdClockOfRecovery
    {n : Nat} (ring : DirectedRing n)
    (member : GrantBlockFamilyMember ring) (radius : Nat)
    (hbuffered : HeadlineGrantBufferedCounter ring member.2.val radius
      member.1)
    (hrec : GrantBlockFrozenRecoveryCost ring member)
    (R L T W : Nat) :
    GrantBlockFrozenLocalColdClock ring member R L T W := by
  intro hn hsp hw hlarge hradius hW hL hWT hbudget
  have hcost : GrantBlockFrozenStoppedCost ring member T :=
    grantBlockFrozenStoppedCostOfRecovery ring member radius hsp
      hbuffered hrec T
  exact (grantBlockFrozenLocalColdClockOfStoppedCost ring member
    R L T W hcost) hn hsp hw hlarge hradius hW hL hWT hbudget

/-- The family built from the pending first-grant branch is buffered:
every selected root, with the entrance configuration as its cold
carrier, satisfies `HeadlineGrantBufferedCounter`.  This restates
`bankTrialBufferedSpatialPreGrantFrozen`, whose statement drops the
buffered predicate that its proof obtains from
`headlineGrantSpatialSupportBridgeProved`.

Consumer: `grantBlockFrozenLocalColdClockOfRecovery`. -/
theorem grantBlockFrozenSpatialBufferedMembers {n : Nat}
    (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (radius : Nat)
    (hsize :
      (4096 * ((compileAdvice (ceilLogTwo n)).b + 2)) ^ 2 ≤ n)
    (hlower : (256 * radius) ^ 2 ≤ n)
    (hupper : n < (256 * (radius + 1)) ^ 2)
    (hdensity : defects ring C * defects ring C ≤ 4 * n)
    (hpurified : headlinePurified ring C)
    (hnotready : ¬ headlineGrantReady ring C) :
    ∃ selected : List (Fin n),
      selected.Nodup ∧
      (∀ root : Fin n, root ∈ selected →
        ∃ x : Counter.ResetClockBankColdCarrier
            (q := ceilLogTwo n) ring root,
          x.val = C ∧
          HeadlineGrantBufferedCounter ring x.val radius root) ∧
      489 * n <
        1000 * selected.length *
          ((compileAdvice (ceilLogTwo n)).b + 2) := by
  obtain ⟨selected, hnodup, hbuffered, _, hcount⟩ :=
    (headlineGrantSpatialSupportBridgeProved ring)
      C radius hsize hlower hupper hdensity
  have hs : BankTrialBufferedSelectionAtBlockEntrance
      (q := ceilLogTwo n) ring C selected :=
    bankTrialBufferedSelectionBeforeGrant
      ring C radius selected hpurified hnotready hbuffered
  refine ⟨selected, hnodup, ?_, hcount⟩
  intro root hr
  obtain ⟨x, hx, _⟩ := bankTrialBufferedColdSelected ring C selected hs
    root hr
  exact ⟨x, hx, by rw [hx]; exact hbuffered root hr⟩

end L3
#print axioms L3.grantBlockFrozenClearedWindowMassLower
#print axioms L3.grantBlockFrozenLocalColdClockOfStoppedCost
#print axioms L3.grantBlockFrozenLocalColdClockOfRecovery
#print axioms L3.grantBlockFrozenSpatialBufferedMembers
