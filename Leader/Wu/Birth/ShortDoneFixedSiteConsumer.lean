import Leader.Wu.Birth.ShortDoneParticipationLoadMass

namespace BirthShortDoneFixedSiteConsumer

open PPLL PPLLDomain PPLLResearchFormulation
  PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
  PPLLPathStallComparisonRepair PPLLLeaderCreationCleanupRepair
  BirthSigMoveDisposalRepair
open BirthShortDoneParticipationBudget
open BirthShortDoneParticipationLoadMass
open FixedSpanRenewalPayload FiniteUniformStoppingTree

set_option autoImplicit false
set_option pp.structureInstances false

variable {n ψ width κ τ T : Nat}

/-- Only the fixed physical site is required positive when it is serviced.
The nested test is the same left-priority alias convention as `localStep`. -/
def FixedSiteInputsPositive (ring : DirectedRing n)
    (R : Local ψ κ τ → Local ψ κ τ → Local ψ κ τ × Local ψ κ τ)
    (i : Fin n) : (Fin n → Local ψ κ τ) → DetSchedule n → Prop
  | _, [] => True
  | C, e :: es =>
      (if i = e then 0 < (C i).stall.val
       else if i = ring.rightNeighbor e then 0 < (C i).stall.val
       else True) ∧
      FixedSiteInputsPositive ring R i (localStep ring R C e) es

/-- Indicator of the requested bad event: at some service of the fixed physical
site, its input stall is zero.  Once witnessed, later row behavior is irrelevant. -/
def fixedSiteZeroServiceBit (ring : DirectedRing n)
    (R : Local ψ κ τ → Local ψ κ τ → Local ψ κ τ × Local ψ κ τ)
    (i : Fin n) : (Fin n → Local ψ κ τ) → DetSchedule n → Nat
  | _, [] => 0
  | C, e :: es =>
      if i = e then
        if (C i).stall.val = 0 then 1
        else fixedSiteZeroServiceBit ring R i (localStep ring R C e) es
      else if i = ring.rightNeighbor e then
        if (C i).stall.val = 0 then 1
        else fixedSiteZeroServiceBit ring R i (localStep ring R C e) es
      else fixedSiteZeroServiceBit ring R i (localStep ring R C e) es

/-- One-site timer induction.  No timer/state hypothesis is made at any other
site.  `hcredit` itself implies the timer-contract cap because stall : Fin (τ+1). -/
theorem fixed_site_credit_of_participations
    (ring : DirectedRing n)
    (R : Local ψ κ τ → Local ψ κ τ → Local ψ κ τ × Local ψ κ τ)
    (hR : TimerContract R) (i : Fin n)
    (C : Fin n → Local ψ κ τ) (word : DetSchedule n) (reserve : Nat)
    (hcredit : reserve + endpointParticipations ring i word ≤
      (C i).stall.val) :
    FixedSiteInputsPositive ring R i C word ∧
      reserve ≤ (runLocalSchedule ring R C word i).stall.val := by
  induction word generalizing C with
  | nil =>
      constructor
      · trivial
      · simpa [runLocalSchedule, endpointParticipations] using hcredit
  | cons e es ih =>
      let D := localStep ring R C e
      by_cases hi : i = e
      · subst i
        have hp : 0 < (C e).stall.val := by
          have h := hcredit
          simp [endpointParticipations] at h
          omega
        have hneed :
            reserve + endpointParticipations ring e es + 1 ≤
              (C e).stall.val := by
          have h := hcredit
          simp [endpointParticipations] at h
          omega
        have hcap : reserve + endpointParticipations ring e es ≤ τ := by
          have hlt := (C e).stall.isLt
          omega
        have hb := hR.left
          (reserve + endpointParticipations ring e es)
          (C e) (C (ring.rightNeighbor e)) hcap hneed
        have hD : reserve + endpointParticipations ring e es ≤
            (D e).stall.val := by
          simpa [D, localStep] using hb
        have ht := ih D hD
        constructor
        · simpa [FixedSiteInputsPositive, D] using And.intro hp ht.1
        · simpa [runLocalSchedule, D] using ht.2
      · by_cases hj : i = ring.rightNeighbor e
        · subst i
          have hp : 0 < (C (ring.rightNeighbor e)).stall.val := by
            have h := hcredit
            simp [endpointParticipations, hi] at h
            omega
          have hneed :
              reserve +
                    endpointParticipations ring (ring.rightNeighbor e) es + 1 ≤
                (C (ring.rightNeighbor e)).stall.val := by
            have h := hcredit
            simp [endpointParticipations, hi] at h
            omega
          have hcap :
              reserve + endpointParticipations ring (ring.rightNeighbor e) es ≤
                τ := by
            have hlt := (C (ring.rightNeighbor e)).stall.isLt
            omega
          have hb := hR.right
            (reserve + endpointParticipations ring (ring.rightNeighbor e) es)
            (C e) (C (ring.rightNeighbor e)) hcap hneed
          have hD :
              reserve + endpointParticipations ring (ring.rightNeighbor e) es ≤
                (D (ring.rightNeighbor e)).stall.val := by
            simpa [D, localStep, hi] using hb
          have ht := ih D hD
          constructor
          · simpa [FixedSiteInputsPositive, D, hi] using And.intro hp ht.1
          · simpa [runLocalSchedule, D] using ht.2
        · have hD : reserve + endpointParticipations ring i es ≤
              (D i).stall.val := by
            simpa [endpointParticipations, D, localStep, hi, hj] using hcredit
          have ht := ih D hD
          constructor
          · simpa [FixedSiteInputsPositive, D, hi, hj] using ht.1
          · simpa [runLocalSchedule, D] using ht.2

/-- Concrete short-DONE one-site consumer; no global service-credit premise. -/
theorem actual_fixed_site_credit (hψ : 0 < ψ) (hwidth : 0 < width)
    (hle : width ≤ ψ) (ring : DirectedRing n) (i : Fin n)
    (C : Fin n → Local ψ κ τ) (word : DetSchedule n) (reserve : Nat)
    (hcredit : reserve + endpointParticipations ring i word ≤
      (C i).stall.val) :
    FixedSiteInputsPositive ring
        (BirthShortDoneDispatcher.row hψ hwidth hle) i C word ∧
      reserve ≤ (runLocalSchedule ring
        (BirthShortDoneDispatcher.row hψ hwidth hle) C word i).stall.val := by
  exact fixed_site_credit_of_participations ring
    (BirthShortDoneDispatcher.row (κ := κ) (τ := τ) hψ hwidth hle)
    (shortDoneTimerContract (κ := κ) (τ := τ) hψ hwidth hle)
    i C word reserve hcredit

/-- Fresh selected site; every other initial site remains completely arbitrary. -/
theorem actual_fixed_site_fresh (hψ : 0 < ψ) (hwidth : 0 < width)
    (hle : width ≤ ψ) (ring : DirectedRing n) (i : Fin n)
    (C : Fin n → Local ψ κ τ) (word : DetSchedule n)
    (hfresh : (C i).stall.val = τ)
    (hload : endpointParticipations ring i word ≤ τ) :
    FixedSiteInputsPositive ring
      (BirthShortDoneDispatcher.row hψ hwidth hle) i C word := by
  exact (actual_fixed_site_credit (κ := κ) (τ := τ)
    hψ hwidth hle ring i C word 0 (by omega)).1

/-- One concrete producer of the preceding fresh-credit premise.  This uses the
actual left refresh cut and then the actual `localStep` successor.  In `n=1`
the alias is stored through this left output, not the discarded right output. -/
theorem actual_left_progress_suffix_positive
    (hψ : 0 < ψ) (hwidth : 0 < width) (hle : width ≤ ψ)
    (ring : DirectedRing n) (C : Fin n → Local ψ κ τ)
    (e : Fin n) (word : DetSchedule n)
    (hp :
      let l0 := prepareExpiringDisposal hψ (C e)
      let r0 := prepareExpiringDisposal hψ (C (ring.rightNeighbor e))
      let q := BirthShortDoneCuts.doneMetadataBoundedWidth
        hψ hwidth hle l0.core r0.core
      PathProgressView.ofState q.1 ≠ PathProgressView.ofState l0.core)
    (hload : endpointParticipations ring e word ≤ τ) :
    FixedSiteInputsPositive ring
      (BirthShortDoneDispatcher.row hψ hwidth hle) e
      (localStep ring
        (BirthShortDoneDispatcher.row hψ hwidth hle) C e) word := by
  have hr := actual_row_progress_refresh (κ := κ) (τ := τ)
    hψ hwidth hle (C e) (C (ring.rightNeighbor e))
  dsimp only at hr hp
  have hs := hr.1 hp
  have hstep :
      (localStep ring
        (BirthShortDoneDispatcher.row hψ hwidth hle) C e e).stall =
        freshStall τ := by
    simpa [localStep] using hs
  apply actual_fixed_site_fresh (κ := κ) (τ := τ)
    hψ hwidth hle ring e
    (localStep ring (BirthShortDoneDispatcher.row hψ hwidth hle) C e)
    word
  · have hv := congrArg (fun z : Fin (τ + 1) => z.val) hstep
    simpa [freshStall] using hv
  · exact hload

private theorem fixedSiteZeroServiceBit_le_one
    (ring : DirectedRing n)
    (R : Local ψ κ τ → Local ψ κ τ → Local ψ κ τ × Local ψ κ τ)
    (i : Fin n) (C : Fin n → Local ψ κ τ) (word : DetSchedule n) :
    fixedSiteZeroServiceBit ring R i C word ≤ 1 := by
  induction word generalizing C with
  | nil => simp [fixedSiteZeroServiceBit]
  | cons e es ih =>
      by_cases hi : i = e
      · by_cases hz : (C i).stall.val = 0
        · simpa only [fixedSiteZeroServiceBit, if_pos hi, if_pos hz] using
            (Nat.le_refl 1)
        · simpa only [fixedSiteZeroServiceBit, if_pos hi, if_neg hz] using
            ih (localStep ring R C e)
      · by_cases hj : i = ring.rightNeighbor e
        · by_cases hz : (C i).stall.val = 0
          · simpa only [fixedSiteZeroServiceBit, if_neg hi, if_pos hj,
              if_pos hz] using (Nat.le_refl 1)
          · simpa only [fixedSiteZeroServiceBit, if_neg hi, if_pos hj,
              if_neg hz] using ih (localStep ring R C e)
        · simpa only [fixedSiteZeroServiceBit, if_neg hi, if_neg hj] using
            ih (localStep ring R C e)

private theorem fixedSiteZeroServiceBit_eq_zero_of_positive
    (ring : DirectedRing n)
    (R : Local ψ κ τ → Local ψ κ τ → Local ψ κ τ × Local ψ κ τ)
    (i : Fin n) (C : Fin n → Local ψ κ τ) (word : DetSchedule n)
    (hpos : FixedSiteInputsPositive ring R i C word) :
    fixedSiteZeroServiceBit ring R i C word = 0 := by
  induction word generalizing C with
  | nil => rfl
  | cons e es ih =>
      change
        (if i = e then 0 < (C i).stall.val
         else if i = ring.rightNeighbor e then 0 < (C i).stall.val
         else True) ∧
        FixedSiteInputsPositive ring R i (localStep ring R C e) es at hpos
      by_cases hi : i = e
      · have hp : 0 < (C i).stall.val := by
          simpa only [if_pos hi] using hpos.1
        have hz : (C i).stall.val ≠ 0 := Nat.ne_of_gt hp
        have ht := ih (localStep ring R C e) hpos.2
        simpa only [fixedSiteZeroServiceBit, if_pos hi, if_neg hz] using ht
      · by_cases hj : i = ring.rightNeighbor e
        · have hp : 0 < (C i).stall.val := by
            simpa only [if_neg hi, if_pos hj] using hpos.1
          have hz : (C i).stall.val ≠ 0 := Nat.ne_of_gt hp
          have ht := ih (localStep ring R C e) hpos.2
          simpa only [fixedSiteZeroServiceBit, if_neg hi, if_pos hj,
              if_neg hz] using ht
        · have ht := ih (localStep ring R C e) hpos.2
          simpa only [fixedSiteZeroServiceBit, if_neg hi, if_neg hj] using ht

/-- Pointwise domination on the same word and actual successors.  Threshold
`τ+1` is exact: if the load is at most τ, fresh credit forbids zero input. -/
theorem actual_zeroServiceBit_le_overload
    (hψ : 0 < ψ) (hwidth : 0 < width) (hle : width ≤ ψ)
    (ring : DirectedRing n) (C : Fin n → Local ψ κ τ)
    (i : Fin n) (word : DetSchedule n) (hfresh : (C i).stall.val = τ) :
    fixedSiteZeroServiceBit ring
        (BirthShortDoneDispatcher.row hψ hwidth hle) i C word ≤
      overloadBit ring i (τ + 1) word := by
  by_cases hov : τ + 1 ≤ endpointParticipations ring i word
  · have hb := fixedSiteZeroServiceBit_le_one ring
      (BirthShortDoneDispatcher.row (κ := κ) (τ := τ) hψ hwidth hle)
      i C word
    simpa [overloadBit, hov] using hb
  · have hload : endpointParticipations ring i word ≤ τ := by omega
    have hpos := actual_fixed_site_fresh (κ := κ) (τ := τ)
      hψ hwidth hle ring i C word hfresh hload
    have hz := fixedSiteZeroServiceBit_eq_zero_of_positive ring
      (BirthShortDoneDispatcher.row (κ := κ) (τ := τ) hψ hwidth hle)
      i C word hpos
    rw [hz]
    simp [overloadBit, hov]

/-- Exact raw-word bad-event numerator; transition replay is the actual row. -/
def actualZeroServiceNumerator
    (hψ : 0 < ψ) (hwidth : 0 < width) (hle : width ≤ ψ)
    (ring : DirectedRing n) (C : Fin n → Local ψ κ τ)
    (i : Fin n) (T : Nat) : Nat :=
  wordSum n T (fun w =>
    fixedSiteZeroServiceBit ring
      (BirthShortDoneDispatcher.row hψ hwidth hle) i C w)

/-- Bad-event mass is dominated by this site's existing endpoint overload
numerator, over the identical complete `n^T` raw words. -/
theorem actual_zeroServiceNumerator_le_overload
    (hψ : 0 < ψ) (hwidth : 0 < width) (hle : width ≤ ψ)
    (ring : DirectedRing n) (C : Fin n → Local ψ κ τ)
    (i : Fin n) (T : Nat) (hfresh : (C i).stall.val = τ) :
    actualZeroServiceNumerator hψ hwidth hle ring C i T ≤
      overloadNumerator ring i T (τ + 1) := by
  unfold actualZeroServiceNumerator overloadNumerator
  rw [<- rawWord_sum n T (fun w =>
      fixedSiteZeroServiceBit ring
        (BirthShortDoneDispatcher.row hψ hwidth hle) i C w),
    <- rawWord_sum n T (overloadBit ring i (τ + 1))]
  apply ofFn_sum_le
  intro a
  exact actual_zeroServiceBit_le_overload (κ := κ) (τ := τ)
    hψ hwidth hle ring C i (rawWord n T a) hfresh

/-- `τ=0` is literal: every Fin 1 stall has value zero, so the overload
threshold is exactly one endpoint participation. -/
theorem actual_tau_zero_badMass_le_overload
    (hψ : 0 < ψ) (hwidth : 0 < width) (hle : width ≤ ψ)
    (ring : DirectedRing n) (C : Fin n → Local ψ κ 0)
    (i : Fin n) (T : Nat) :
    actualZeroServiceNumerator hψ hwidth hle ring C i T ≤
      overloadNumerator ring i T 1 := by
  apply actual_zeroServiceNumerator_le_overload
    (κ := κ) (τ := 0) hψ hwidth hle ring C i T
  have hlt := (C i).stall.isLt
  omega

/-- One-site alias: use the exact ring-1 load, never the two-letter n≥2 cap. -/
theorem ring1_alias_badMass_le
    (hψ : 0 < ψ) (hwidth : 0 < width) (hle : width ≤ ψ)
    (ring : DirectedRing 1) (C : Fin 1 → Local ψ κ τ)
    (i : Fin 1) (T : Nat) (hfresh : (C i).stall.val = τ) :
    actualZeroServiceNumerator hψ hwidth hle ring C i T ≤
      if τ < T then 1 else 0 := by
  calc
    actualZeroServiceNumerator hψ hwidth hle ring C i T ≤
        overloadNumerator ring i T (τ + 1) :=
      actual_zeroServiceNumerator_le_overload
        (κ := κ) (τ := τ) hψ hwidth hle ring C i T hfresh
    _ = if τ < T then 1 else 0 := ring1_tau_split ring i T τ

#print axioms BirthShortDoneFixedSiteConsumer.fixed_site_credit_of_participations
#print axioms BirthShortDoneFixedSiteConsumer.actual_fixed_site_credit
#print axioms BirthShortDoneFixedSiteConsumer.actual_left_progress_suffix_positive
#print axioms BirthShortDoneFixedSiteConsumer.actual_zeroServiceNumerator_le_overload
#print axioms BirthShortDoneFixedSiteConsumer.actual_tau_zero_badMass_le_overload
#print axioms BirthShortDoneFixedSiteConsumer.ring1_alias_badMass_le

end BirthShortDoneFixedSiteConsumer
