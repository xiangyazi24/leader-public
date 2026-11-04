import Leader.Wu.Birth.ShortDoneTerminalConsumer
import Leader.Wu.Birth.ShortDoneFixedSiteConsumer

namespace BirthShortDoneTerminalFixedSite

open PPLL PPLLResearchFormulation
  PPLLExpiringComparisonRepair PPLLLeaderCreationCleanupRepair
  BirthSigMoveDisposalRepair
open BirthShortDoneParticipationBudget
open BirthShortDoneParticipationLoadMass
open BirthShortDoneFixedSiteConsumer

set_option autoImplicit false
set_option pp.structureInstances false

variable {n ψ width κ τ : Nat}

/-- Actual timer contract for the terminal-entry repaired host.  The proof uses
only its literal two expiry calls and the definitional stall frame of
`prepareExpiringDisposal`; no comparison with the older short row is used. -/
theorem terminalTimerContract (hψ : 0 < ψ) (hwidth : 0 < width)
    (hle : width ≤ ψ) :
    TimerContract
      (BirthShortDoneTerminalHost.row (κ := κ) (τ := τ) hψ hwidth hle) := by
  constructor
  · intro remaining l r hcap hcredit
    let l0 := prepareExpiringDisposal hψ l
    let r0 := prepareExpiringDisposal hψ r
    let q := BirthShortDoneTerminalHost.doneMetadataBoundedEntryWidth
      hψ hwidth hle l0.core r0.core
    have ht := BirthShortDoneTerminalConsumer.row_timers_once
      (κ := κ) (τ := τ) hψ hwidth hle l r
    change
      (BirthShortDoneTerminalHost.row hψ hwidth hle l r).1.stall =
          (deletionPriorityExpireOne τ l0
            (⟨q.1, l0.stall⟩ : Local ψ κ τ)).stall ∧
      (BirthShortDoneTerminalHost.row hψ hwidth hle l r).2.stall =
          (deletionPriorityExpireOne τ r0
            (⟨q.2, r0.stall⟩ : Local ψ κ τ)).stall at ht
    have hpre : remaining + 1 ≤ l0.stall.val := by
      simpa [l0, prepareExpiringDisposal] using hcredit
    have hb := BirthCheckParametricWait.expiry_budget remaining l0
      (⟨q.1, l0.stall⟩ : Local ψ κ τ) hcap hpre
    rw [ht.1]
    exact hb
  · intro remaining l r hcap hcredit
    let l0 := prepareExpiringDisposal hψ l
    let r0 := prepareExpiringDisposal hψ r
    let q := BirthShortDoneTerminalHost.doneMetadataBoundedEntryWidth
      hψ hwidth hle l0.core r0.core
    have ht := BirthShortDoneTerminalConsumer.row_timers_once
      (κ := κ) (τ := τ) hψ hwidth hle l r
    change
      (BirthShortDoneTerminalHost.row hψ hwidth hle l r).1.stall =
          (deletionPriorityExpireOne τ l0
            (⟨q.1, l0.stall⟩ : Local ψ κ τ)).stall ∧
      (BirthShortDoneTerminalHost.row hψ hwidth hle l r).2.stall =
          (deletionPriorityExpireOne τ r0
            (⟨q.2, r0.stall⟩ : Local ψ κ τ)).stall at ht
    have hpre : remaining + 1 ≤ r0.stall.val := by
      simpa [r0, prepareExpiringDisposal] using hcredit
    have hb := BirthCheckParametricWait.expiry_budget remaining r0
      (⟨q.2, r0.stall⟩ : Local ψ κ τ) hcap hpre
    rw [ht.2]
    exact hb

/-- Direct specialization of the existing generic one-site induction to the
actual terminal host.  No timer/state condition is imposed at another site. -/
theorem terminal_fixed_site_credit
    (hψ : 0 < ψ) (hwidth : 0 < width) (hle : width ≤ ψ)
    (ring : DirectedRing n) (i : Fin n)
    (C : Fin n → Local ψ κ τ) (word : DetSchedule n) (reserve : Nat)
    (hcredit : reserve + endpointParticipations ring i word ≤
      (C i).stall.val) :
    FixedSiteInputsPositive ring
        (BirthShortDoneTerminalHost.row hψ hwidth hle) i C word ∧
      reserve ≤ (runLocalSchedule ring
        (BirthShortDoneTerminalHost.row hψ hwidth hle) C word i).stall.val := by
  exact fixed_site_credit_of_participations ring
    (BirthShortDoneTerminalHost.row (κ := κ) (τ := τ) hψ hwidth hle)
    (terminalTimerContract (κ := κ) (τ := τ) hψ hwidth hle)
    i C word reserve hcredit

/-- Fresh credit only at the selected physical site. -/
theorem terminal_fixed_site_fresh
    (hψ : 0 < ψ) (hwidth : 0 < width) (hle : width ≤ ψ)
    (ring : DirectedRing n) (i : Fin n)
    (C : Fin n → Local ψ κ τ) (word : DetSchedule n)
    (hfresh : (C i).stall.val = τ)
    (hload : endpointParticipations ring i word ≤ τ) :
    FixedSiteInputsPositive ring
      (BirthShortDoneTerminalHost.row hψ hwidth hle) i C word := by
  exact (terminal_fixed_site_credit (κ := κ) (τ := τ)
    hψ hwidth hle ring i C word 0 (by omega)).1

/-- `localStep` retains its left-output priority on an alias.  Thus the generic
one-site induction and its nested participation charge match the actual host. -/
theorem terminal_localStep_alias_left
    (hψ : 0 < ψ) (hwidth : 0 < width) (hle : width ≤ ψ)
    (ring : DirectedRing n) (C : Fin n → Local ψ κ τ) (e : Fin n)
    (ha : ring.rightNeighbor e = e) :
    localStep ring (BirthShortDoneTerminalHost.row hψ hwidth hle) C e e =
      (BirthShortDoneTerminalHost.row hψ hwidth hle (C e) (C e)).1 := by
  simp [localStep, ha]

private theorem zeroBit_le_one
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

private theorem zeroBit_eq_zero_of_positive
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

/-- Deterministic pointwise bad-event domination for the actual terminal host.
This is not yet a scheduler-mass or factorial-moment statement. -/
theorem terminal_zeroServiceBit_le_overload
    (hψ : 0 < ψ) (hwidth : 0 < width) (hle : width ≤ ψ)
    (ring : DirectedRing n) (C : Fin n → Local ψ κ τ)
    (i : Fin n) (word : DetSchedule n) (hfresh : (C i).stall.val = τ) :
    fixedSiteZeroServiceBit ring
        (BirthShortDoneTerminalHost.row hψ hwidth hle) i C word ≤
      overloadBit ring i (τ + 1) word := by
  by_cases hov : τ + 1 ≤ endpointParticipations ring i word
  · have hb := zeroBit_le_one ring
      (BirthShortDoneTerminalHost.row (κ := κ) (τ := τ) hψ hwidth hle)
      i C word
    simpa [overloadBit, hov] using hb
  · have hload : endpointParticipations ring i word ≤ τ := by omega
    have hpos := terminal_fixed_site_fresh (κ := κ) (τ := τ)
      hψ hwidth hle ring i C word hfresh hload
    have hz := zeroBit_eq_zero_of_positive ring
      (BirthShortDoneTerminalHost.row (κ := κ) (τ := τ) hψ hwidth hle)
      i C word hpos
    rw [hz]
    simp [overloadBit, hov]

#print axioms BirthShortDoneTerminalFixedSite.terminalTimerContract
#print axioms BirthShortDoneTerminalFixedSite.terminal_fixed_site_credit
#print axioms BirthShortDoneTerminalFixedSite.terminal_fixed_site_fresh
#print axioms BirthShortDoneTerminalFixedSite.terminal_localStep_alias_left
#print axioms BirthShortDoneTerminalFixedSite.terminal_zeroServiceBit_le_overload

end BirthShortDoneTerminalFixedSite
