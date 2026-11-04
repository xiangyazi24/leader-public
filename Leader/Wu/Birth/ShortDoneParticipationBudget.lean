import Leader.Wu.Birth.ShortDoneDispatcher
import Leader.Wu.Birth.CheckParametricWait
import Leader.Wu.Comparison.PathStallRepair

namespace BirthShortDoneParticipationBudget

open PPLL PPLLDomain PPLLResearchFormulation
  PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
  PPLLPathStallComparisonRepair PPLLLeaderCreationCleanupRepair
  BirthSigMoveDisposalRepair

set_option autoImplicit false
set_option pp.structureInstances false

variable {n ψ width κ τ : Nat}

abbrev Local (ψ κ τ : Nat) := ExpiringAgentState ψ κ τ

/-- Charge the stored endpoint exactly once.  The nested `if` is the same
left-output priority as `localStep`, so an alias is not double charged. -/
def endpointParticipations (ring : DirectedRing n) (i : Fin n) :
    DetSchedule n → Nat
  | [] => 0
  | e :: es =>
      (if i = e then 1
       else if i = ring.rightNeighbor e then 1
       else 0) + endpointParticipations ring i es

structure TimerContract
    (T : Local ψ κ τ → Local ψ κ τ → Local ψ κ τ × Local ψ κ τ) : Prop where
  left : ∀ remaining l r,
    remaining ≤ τ → remaining + 1 ≤ l.stall.val →
    remaining ≤ (T l r).1.stall.val
  right : ∀ remaining l r,
    remaining ≤ τ → remaining + 1 ≤ r.stall.val →
    remaining ≤ (T l r).2.stall.val

/-- At every scheduled service, both row inputs have positive current credit.
For an alias these are the same physical site, still charged once. -/
def ServiceInputsPositive (ring : DirectedRing n)
    (T : Local ψ κ τ → Local ψ κ τ → Local ψ κ τ × Local ψ κ τ) :
    (Fin n → Local ψ κ τ) → DetSchedule n → Prop
  | _, [] => True
  | C, e :: es =>
      0 < (C e).stall.val ∧
      0 < (C (ring.rightNeighbor e)).stall.val ∧
      ServiceInputsPositive ring T (localStep ring T C e) es

/-- `reserve` is explicit credit required after the whole word. -/
theorem run_credit_of_participations
    (ring : DirectedRing n)
    (T : Local ψ κ τ → Local ψ κ τ → Local ψ κ τ × Local ψ κ τ)
    (hT : TimerContract T)
    (C : Fin n → Local ψ κ τ) (word : DetSchedule n)
    (reserve : Fin n → Nat)
    (hcap : ∀ i, reserve i + endpointParticipations ring i word ≤ τ)
    (hcredit : ∀ i, reserve i + endpointParticipations ring i word ≤
      (C i).stall.val) :
    ServiceInputsPositive ring T C word ∧
      ∀ i, reserve i ≤ (runLocalSchedule ring T C word i).stall.val := by
  induction word generalizing C with
  | nil =>
      constructor
      · trivial
      · intro i
        simpa [runLocalSchedule, endpointParticipations] using hcredit i
  | cons e es ih =>
      let D := localStep ring T C e
      have hpL : 0 < (C e).stall.val := by
        have h := hcredit e
        simp [endpointParticipations] at h
        omega
      have hpR : 0 < (C (ring.rightNeighbor e)).stall.val := by
        by_cases ha : ring.rightNeighbor e = e
        · rw [ha]
          exact hpL
        · have h := hcredit (ring.rightNeighbor e)
          simp [endpointParticipations, ha] at h
          omega
      have hc : ∀ i, reserve i + endpointParticipations ring i es ≤ τ := by
        intro i
        have h := hcap i
        by_cases hi : i = e
        · simp [endpointParticipations, hi] at h
          simp only [hi]
          omega
        · by_cases hj : i = ring.rightNeighbor e
          · simp [endpointParticipations, hi, hj] at h
            simp only [hj]
            omega
          · simpa [endpointParticipations, hi, hj] using h
      have hC : ∀ i,
          reserve i + endpointParticipations ring i es ≤ (D i).stall.val := by
        intro i
        by_cases hi : i = e
        · subst i
          have hneed :
              reserve e + endpointParticipations ring e es + 1 ≤
                (C e).stall.val := by
            have h := hcredit e
            simp [endpointParticipations] at h
            omega
          have hb := hT.left
            (reserve e + endpointParticipations ring e es)
            (C e) (C (ring.rightNeighbor e)) (hc e) (by omega)
          simpa [D, localStep] using hb
        · by_cases hj : i = ring.rightNeighbor e
          · subst i
            have hneed :
                reserve (ring.rightNeighbor e) +
                    endpointParticipations ring (ring.rightNeighbor e) es + 1 ≤
                  (C (ring.rightNeighbor e)).stall.val := by
              have h := hcredit (ring.rightNeighbor e)
              simp [endpointParticipations, hi] at h
              omega
            have hb := hT.right
              (reserve (ring.rightNeighbor e) +
                endpointParticipations ring (ring.rightNeighbor e) es)
              (C e) (C (ring.rightNeighbor e))
              (hc (ring.rightNeighbor e)) hneed
            simpa [D, localStep, hi] using hb
          · have h := hcredit i
            simp [endpointParticipations, hi, hj] at h
            simpa [D, localStep, hi, hj] using h
      have ht := ih D hc hC
      constructor
      · exact ⟨hpL, hpR, ht.1⟩
      · simpa [runLocalSchedule, D] using ht.2

/-- The substantive timer law for the actual short-DONE row.  Preparation
frames stall, and `row_timers_once` exposes exactly the two existing priority
expiry calls after normalization and final K2. -/
theorem shortDoneTimerContract (hψ : 0 < ψ) (hwidth : 0 < width)
    (hle : width ≤ ψ) :
    TimerContract
      (BirthShortDoneDispatcher.row (κ := κ) (τ := τ) hψ hwidth hle) := by
  constructor
  · intro remaining l r hcap hcredit
    let l0 := prepareExpiringDisposal hψ l
    let r0 := prepareExpiringDisposal hψ r
    let q := BirthShortDoneCuts.doneMetadataBoundedWidth
      hψ hwidth hle l0.core r0.core
    have ht := BirthShortDoneDispatcher.row_timers_once
      (κ := κ) (τ := τ) hψ hwidth hle l r
    change
      (BirthShortDoneDispatcher.row hψ hwidth hle l r).1.stall =
          (deletionPriorityExpireOne τ l0
            (⟨q.1, l0.stall⟩ : Local ψ κ τ)).stall ∧
      (BirthShortDoneDispatcher.row hψ hwidth hle l r).2.stall =
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
    let q := BirthShortDoneCuts.doneMetadataBoundedWidth
      hψ hwidth hle l0.core r0.core
    have ht := BirthShortDoneDispatcher.row_timers_once
      (κ := κ) (τ := τ) hψ hwidth hle l r
    change
      (BirthShortDoneDispatcher.row hψ hwidth hle l r).1.stall =
          (deletionPriorityExpireOne τ l0
            (⟨q.1, l0.stall⟩ : Local ψ κ τ)).stall ∧
      (BirthShortDoneDispatcher.row hψ hwidth hle l r).2.stall =
          (deletionPriorityExpireOne τ r0
            (⟨q.2, r0.stall⟩ : Local ψ κ τ)).stall at ht
    have hpre : remaining + 1 ≤ r0.stall.val := by
      simpa [r0, prepareExpiringDisposal] using hcredit
    have hb := BirthCheckParametricWait.expiry_budget remaining r0
      (⟨q.2, r0.stall⟩ : Local ψ κ τ) hcap hpre
    rw [ht.2]
    exact hb

/-- Concrete consumer: no timer contract remains as a premise. -/
theorem actual_row_run_credit (hψ : 0 < ψ) (hwidth : 0 < width)
    (hle : width ≤ ψ) (ring : DirectedRing n)
    (C : Fin n → Local ψ κ τ) (word : DetSchedule n)
    (reserve : Fin n → Nat)
    (hcap : ∀ i, reserve i + endpointParticipations ring i word ≤ τ)
    (hcredit : ∀ i, reserve i + endpointParticipations ring i word ≤
      (C i).stall.val) :
    ServiceInputsPositive ring
        (BirthShortDoneDispatcher.row hψ hwidth hle) C word ∧
      ∀ i, reserve i ≤
        (runLocalSchedule ring
          (BirthShortDoneDispatcher.row hψ hwidth hle) C word i).stall.val := by
  exact run_credit_of_participations ring
    (BirthShortDoneDispatcher.row (κ := κ) (τ := τ) hψ hwidth hle)
    (shortDoneTimerContract (κ := κ) (τ := τ) hψ hwidth hle)
    C word reserve hcap hcredit

/-- Deletion priority is included: either its active branch refreshes directly,
or the existing path-progress branch does. -/
theorem deletionPriorityExpireOne_of_progress (τ : Nat)
    (old out : Local ψ κ τ)
    (hp : PathProgressView.ofState out.core ≠
      PathProgressView.ofState old.core) :
    deletionPriorityExpireOne τ old out = ⟨out.core, freshStall τ⟩ := by
  unfold deletionPriorityExpireOne
  split
  · rfl
  · exact pathExpireOne_of_progress τ old out hp

/-- Exact refresh cut of the actual row: progress is compared with the
prepared endpoint, at the bounded metadata output immediately before expiry. -/
theorem actual_row_progress_refresh (hψ : 0 < ψ) (hwidth : 0 < width)
    (hle : width ≤ ψ) (l r : Local ψ κ τ) :
    let l0 := prepareExpiringDisposal hψ l
    let r0 := prepareExpiringDisposal hψ r
    let q := BirthShortDoneCuts.doneMetadataBoundedWidth
      hψ hwidth hle l0.core r0.core
    (PathProgressView.ofState q.1 ≠ PathProgressView.ofState l0.core →
      (BirthShortDoneDispatcher.row hψ hwidth hle l r).1.stall = freshStall τ) ∧
    (PathProgressView.ofState q.2 ≠ PathProgressView.ofState r0.core →
      (BirthShortDoneDispatcher.row hψ hwidth hle l r).2.stall = freshStall τ) := by
  let l0 := prepareExpiringDisposal hψ l
  let r0 := prepareExpiringDisposal hψ r
  let q := BirthShortDoneCuts.doneMetadataBoundedWidth
    hψ hwidth hle l0.core r0.core
  have ht := BirthShortDoneDispatcher.row_timers_once
    (κ := κ) (τ := τ) hψ hwidth hle l r
  change
    (BirthShortDoneDispatcher.row hψ hwidth hle l r).1.stall =
        (deletionPriorityExpireOne τ l0
          (⟨q.1, l0.stall⟩ : Local ψ κ τ)).stall ∧
    (BirthShortDoneDispatcher.row hψ hwidth hle l r).2.stall =
        (deletionPriorityExpireOne τ r0
          (⟨q.2, r0.stall⟩ : Local ψ κ τ)).stall at ht
  constructor
  · intro hp
    have he := deletionPriorityExpireOne_of_progress τ l0
      (⟨q.1, l0.stall⟩ : Local ψ κ τ) hp
    have hs := congrArg (fun u : Local ψ κ τ => u.stall) he
    exact ht.1.trans (by simpa using hs)
  · intro hp
    have he := deletionPriorityExpireOne_of_progress τ r0
      (⟨q.2, r0.stall⟩ : Local ψ κ τ) hp
    have hs := congrArg (fun u : Local ψ κ τ => u.stall) he
    exact ht.2.trans (by simpa using hs)

private def ring3 : DirectedRing 3 := ⟨by decide⟩
private def ring1 : DirectedRing 1 := ⟨by decide⟩

/-- Distinct endpoints charge their two sites; an untouched site pays zero.
A one-site alias pays once per raw edge, not twice. -/
theorem service_count_witness :
    ring3.rightNeighbor (0 : Fin 3) = 1 ∧
    endpointParticipations ring3 (0 : Fin 3) [0, 0] = 2 ∧
    endpointParticipations ring3 (1 : Fin 3) [0, 0] = 2 ∧
    endpointParticipations ring3 (2 : Fin 3) [0, 0] = 0 ∧
    ring1.rightNeighbor (0 : Fin 1) = 0 ∧
    endpointParticipations ring1 (0 : Fin 1) [0, 0, 0] = 3 := by
  decide

/-- The old global word-length charge is a stronger corollary. -/
theorem endpointParticipations_le_length
    (ring : DirectedRing n) (i : Fin n) (word : DetSchedule n) :
    endpointParticipations ring i word ≤ word.length := by
  induction word with
  | nil => simp [endpointParticipations]
  | cons e es ih =>
      by_cases hi : i = e
      · simp only [hi] at ih
        simp [endpointParticipations, hi]
        omega
      · by_cases hj : i = ring.rightNeighbor e
        · simp only [hj] at ih
          simp [endpointParticipations, hi, hj]
          omega
        · simp [endpointParticipations, hi, hj]
          omega

/-- Hence the previous uniform length budget implies positive service inputs
for the same actual row, but is not required by `actual_row_run_credit`. -/
theorem actual_row_service_inputs_of_length
    (hψ : 0 < ψ) (hwidth : 0 < width) (hle : width ≤ ψ)
    (ring : DirectedRing n) (C : Fin n → Local ψ κ τ)
    (word : DetSchedule n) (hcap : word.length ≤ τ)
    (hcredit : ∀ i, word.length ≤ (C i).stall.val) :
    ServiceInputsPositive ring
      (BirthShortDoneDispatcher.row hψ hwidth hle) C word := by
  have hc : ∀ i,
      0 + endpointParticipations ring i word ≤ τ := by
    intro i
    have hp := endpointParticipations_le_length ring i word
    omega
  have hi : ∀ i,
      0 + endpointParticipations ring i word ≤ (C i).stall.val := by
    intro i
    have hp := endpointParticipations_le_length ring i word
    have h := hcredit i
    omega
  exact (actual_row_run_credit (κ := κ) (τ := τ)
    hψ hwidth hle ring C word (fun _ => 0) hc hi).1

#print axioms BirthShortDoneParticipationBudget.run_credit_of_participations
#print axioms BirthShortDoneParticipationBudget.shortDoneTimerContract
#print axioms BirthShortDoneParticipationBudget.actual_row_run_credit
#print axioms BirthShortDoneParticipationBudget.actual_row_progress_refresh
#print axioms BirthShortDoneParticipationBudget.service_count_witness

end BirthShortDoneParticipationBudget
