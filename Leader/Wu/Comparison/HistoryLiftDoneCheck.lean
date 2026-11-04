import Leader.Wu.Comparison.HistoryEntryResetSanitize
import Leader.Wu.Birth.GenerationDone

set_option autoImplicit false
set_option Elab.async false
set_option pp.structureInstances false

namespace PPLLComparisonHistory

open PPLL PPLLRepair
open PPLLAuthorizedComparisonRepair
open BirthCheckCongestGuardRepair
open BirthTossCheckPreservationRepair
open BirthGenerationDone

variable {n ψ : Nat}

/-! ## Current DONE/toss/congest CHECK wrapper -/

/-- The exact branch on which `preserveDoneCheck` reaches physical Algorithm 11.
The three preceding guards are written endpointwise so that callers can consume
the predicate without reopening the nested disjunctions. -/
def PreserveDoneCheckActive
    (l r : MarkedAuthorizedAgentState n ψ) : Prop :=
  l.concrete.core.state ≠ .done ∧
    r.concrete.core.state ≠ .done ∧
    l.concrete.core.state ≠ .toss ∧
    r.concrete.core.state ≠ .toss ∧
    l.concrete.core.state ≠ .congest ∧
    r.concrete.core.state ≠ .congest

/-- The sole source-join premise for the current CHECK wrapper.  It is required
only when DONE, toss, and congestion are all absent.  At that point it is
exactly the already-proved Algorithm-11 compatibility boundary: both endpoints
have passed `markedCheckSetReady`, and the initiator has additionally passed
its offset-zero `markedCheckL` before the responder's later-bit CHECK. -/
def PreserveDoneCheckCompatible (hψ : ψ > 0)
    (l r : MarkedAuthorizedAgentState n ψ) : Prop :=
  PreserveDoneCheckActive l r →
    (let lm : MarkedAgentState n ψ :=
        ⟨l.concrete.core, l.history⟩
     let rm : MarkedAgentState n ψ :=
        ⟨r.concrete.core, r.history⟩
     let l0 := markedCheckSetReady lm
     let r0 := markedCheckSetReady rm
     let l1 := markedCheckL hψ l0
     CheckPairCompatible hψ l1 r0)

/-- Exact marked lift of `BirthGenerationDone.preserveDoneCheck`.

The first three branches are literal identity, matching the physical `.done`,
`.toss`, and `.congest` guards.  On the final branch the physical authorized
CHECK is retained exactly, while its raw comparison histories come from the
existing `markedCheckSig`. -/
def markedPreserveDoneCheck (hψ : ψ > 0)
    (l r : MarkedAuthorizedAgentState n ψ) :
    MarkedAuthorizedAgentState n ψ × MarkedAuthorizedAgentState n ψ :=
  if _hdone :
      l.concrete.core.state = .done ∨ r.concrete.core.state = .done then
    (l, r)
  else if _htoss :
      l.concrete.core.state = .toss ∨ r.concrete.core.state = .toss then
    (l, r)
  else if _hcongest :
      l.concrete.core.state = .congest ∨
        r.concrete.core.state = .congest then
    (l, r)
  else
    let lm : MarkedAgentState n ψ :=
      ⟨l.concrete.core, l.history⟩
    let rm : MarkedAgentState n ψ :=
      ⟨r.concrete.core, r.history⟩
    let m := markedCheckSig hψ lm rm
    let q := authorizedCheckSig hψ l.concrete r.concrete
    (⟨q.1, m.1.history⟩, ⟨q.2, m.2.history⟩)

/-- The marked wrapper erases exactly to the current physical
`preserveDoneCheck`, including all three identity guards and the active
`authorizedCheckSig` branch. -/
theorem erase_markedPreserveDoneCheck (hψ : ψ > 0)
    (l r : MarkedAuthorizedAgentState n ψ) :
    let q := markedPreserveDoneCheck hψ l r
    (q.1.concrete, q.2.concrete) =
      preserveDoneCheck hψ l.concrete r.concrete := by
  unfold markedPreserveDoneCheck
  split
  next hdone =>
    simp [preserveDoneCheck, hdone]
  next hdone =>
    split
    next htoss =>
      simp [preserveDoneCheck, preserveTossCheck, hdone, htoss]
    next htoss =>
      split
      next hcongest =>
        simp [preserveDoneCheck, preserveTossCheck, congestGuardCheck,
          hdone, htoss, hcongest]
      next hcongest =>
        simp [preserveDoneCheck, preserveTossCheck, congestGuardCheck,
          hdone, htoss, hcongest]

/-! ## The fourth history field through raw CHECK -/

private theorem checkSigSetReady_pCarry (u : AgentState ψ) :
    (checkSigSetReady u).p_carry = u.p_carry := by
  unfold checkSigSetReady
  repeat (first | rfl | split)

private theorem checkSigCheckL_pCarry (hψ : ψ > 0)
    (u : AgentState ψ) :
    (checkSigCheckL hψ u).p_carry = u.p_carry := by
  unfold checkSigCheckL
  repeat (first | rfl | split)

private theorem checkSigCheckR_pCarry (hψ : ψ > 0)
    (l r : AgentState ψ) :
    (checkSigCheckR hψ l r).p_carry = r.p_carry := by
  unfold checkSigCheckR
  repeat (first | rfl | split)

private theorem checkSigSetResult_pCarry (u : AgentState ψ) :
    (checkSigSetResult u).p_carry = u.p_carry := by
  unfold checkSigSetResult
  repeat (first | rfl | split | dsimp only)

private theorem checkSigSetLeader_pCarry (hψ : ψ > 0)
    (u : AgentState ψ) :
    (checkSigSetLeader hψ u).p_carry = u.p_carry := by
  unfold checkSigSetLeader
  repeat (first | rfl | split)

/-- Algorithm 11 never writes the DISAPPEAR carry bit. -/
private theorem checkSig_pCarry_frame (hψ : ψ > 0)
    (l r : AgentState ψ) :
    let q := checkSig hψ l r
    q.1.p_carry = l.p_carry ∧ q.2.p_carry = r.p_carry := by
  rw [checkSig_eq_staged]
  let l0 := checkSigSetReady l
  let r0 := checkSigSetReady r
  let l1 := checkSigCheckL hψ l0
  let r1 := checkSigCheckR hψ l1 r0
  let l2 := checkSigSetResult l1
  let r2 := checkSigSetResult r1
  have hl0 := checkSigSetReady_pCarry l
  have hr0 := checkSigSetReady_pCarry r
  have hl1 := checkSigCheckL_pCarry hψ l0
  have hr1 := checkSigCheckR_pCarry hψ l1 r0
  have hl2 := checkSigSetResult_pCarry l1
  have hr2 := checkSigSetResult_pCarry r1
  change l0.p_carry = l.p_carry at hl0
  change r0.p_carry = r.p_carry at hr0
  change l1.p_carry = l0.p_carry at hl1
  change r1.p_carry = r0.p_carry at hr1
  change l2.p_carry = l1.p_carry at hl2
  change r2.p_carry = r1.p_carry at hr2
  change
    l2.p_carry = l.p_carry ∧
      (checkSigSetLeader hψ r2).p_carry = r.p_carry
  exact ⟨hl2.trans (hl1.trans hl0),
    (checkSigSetLeader_pCarry hψ r2).trans
      (hr2.trans (hr1.trans hr0))⟩

private theorem markedCheckSetReady_pCarry_history
    (u : MarkedAgentState n ψ) :
    (markedCheckSetReady u).history.pCarry = u.history.pCarry := by
  unfold markedCheckSetReady
  repeat (first | rfl | split)

private theorem markedCheckL_pCarry_history (hψ : ψ > 0)
    (u : MarkedAgentState n ψ) :
    (markedCheckL hψ u).history.pCarry = u.history.pCarry := by
  unfold markedCheckL
  repeat (first | rfl | split)

private theorem markedCheckR_pCarry_history (hψ : ψ > 0)
    (l r : MarkedAgentState n ψ) :
    (markedCheckR hψ l r).history.pCarry = r.history.pCarry := by
  unfold markedCheckR
  repeat (first | rfl | split)

private theorem markedCheckSetResult_pCarry_history
    (u : MarkedAgentState n ψ) :
    (markedCheckSetResult u).history.pCarry = u.history.pCarry := by
  unfold markedCheckSetResult
  repeat (first | rfl | split)

/-- The marked Algorithm-11 source updates never touch the lottery-carry mark. -/
private theorem markedCheckSig_pCarry_history_frame (hψ : ψ > 0)
    (l r : MarkedAgentState n ψ) :
    let q := markedCheckSig hψ l r
    q.1.history.pCarry = l.history.pCarry ∧
      q.2.history.pCarry = r.history.pCarry := by
  let l0 := markedCheckSetReady l
  let r0 := markedCheckSetReady r
  let l1 := markedCheckL hψ l0
  let r1 := markedCheckR hψ l1 r0
  let l2 := markedCheckSetResult l1
  let r2 := markedCheckSetResult r1
  have hl0 := markedCheckSetReady_pCarry_history l
  have hr0 := markedCheckSetReady_pCarry_history r
  have hl1 := markedCheckL_pCarry_history hψ l0
  have hr1 := markedCheckR_pCarry_history hψ l1 r0
  have hl2 := markedCheckSetResult_pCarry_history l1
  have hr2 := markedCheckSetResult_pCarry_history r1
  change l0.history.pCarry = l.history.pCarry at hl0
  change r0.history.pCarry = r.history.pCarry at hr0
  change l1.history.pCarry = l0.history.pCarry at hl1
  change r1.history.pCarry = r0.history.pCarry at hr1
  change l2.history.pCarry = l1.history.pCarry at hl2
  change r2.history.pCarry = r1.history.pCarry at hr2
  change
    l2.history.pCarry = l.history.pCarry ∧
      r2.history.pCarry = r.history.pCarry
  exact ⟨hl2.trans (hl1.trans hl0),
    hr2.trans (hr1.trans hr0)⟩

private theorem fullLocalHistoryTrusted_of_audit_pCarry_frame
    (old out : AgentState ψ)
    (oldHistory outHistory : LocalComparisonHistory n)
    (hold : FullLocalHistoryTrusted old oldHistory)
    (haudit : AuditLocalHistoryTrusted out outHistory)
    (hpCarry : out.p_carry = old.p_carry)
    (hhistory : outHistory.pCarry = oldHistory.pCarry) :
    FullLocalHistoryTrusted out outHistory := by
  constructor
  · exact haudit
  · unfold PCarryHistoryTrusted
    rw [hpCarry, hhistory]
    exact hold.2

/-- Promote the existing three-field CHECK theorem to the current four-field
history predicate.  The only compatibility premise remains the existing
`CheckPairCompatible` at its exact intermediate boundary. -/
private theorem markedCheckSig_preserves_fullLocalHistoryTrusted_local
    (hψ : ψ > 0) (l r : MarkedAgentState n ψ)
    (hl : FullLocalHistoryTrusted l.concrete l.history)
    (hr : FullLocalHistoryTrusted r.concrete r.history)
    (hcompat :
      let l0 := markedCheckSetReady l
      let r0 := markedCheckSetReady r
      let l1 := markedCheckL hψ l0
      CheckPairCompatible hψ l1 r0) :
    let q := markedCheckSig hψ l r
    FullLocalHistoryTrusted q.1.concrete q.1.history ∧
      FullLocalHistoryTrusted q.2.concrete q.2.history := by
  let q := markedCheckSig hψ l r
  have ha := markedCheckSig_preserves_auditLocalHistoryTrusted
    hψ l r hl.1 hr.1 hcompat
  change AuditLocalHistoryTrusted q.1.concrete q.1.history ∧
    AuditLocalHistoryTrusted q.2.concrete q.2.history at ha
  have he := erase_markedCheckSig hψ l r
  change (q.1.concrete, q.2.concrete) =
    checkSig hψ l.concrete r.concrete at he
  have hp := checkSig_pCarry_frame hψ l.concrete r.concrete
  change
    (checkSig hψ l.concrete r.concrete).1.p_carry = l.concrete.p_carry ∧
      (checkSig hψ l.concrete r.concrete).2.p_carry = r.concrete.p_carry at hp
  have hh := markedCheckSig_pCarry_history_frame hψ l r
  change q.1.history.pCarry = l.history.pCarry ∧
    q.2.history.pCarry = r.history.pCarry at hh
  have heL := congrArg
    (fun p : AgentState ψ × AgentState ψ => p.1.p_carry) he
  have heR := congrArg
    (fun p : AgentState ψ × AgentState ψ => p.2.p_carry) he
  have hpL : q.1.concrete.p_carry = l.concrete.p_carry :=
    heL.trans hp.1
  have hpR : q.2.concrete.p_carry = r.concrete.p_carry :=
    heR.trans hp.2
  exact ⟨
    fullLocalHistoryTrusted_of_audit_pCarry_frame
      l.concrete q.1.concrete l.history q.1.history
      hl ha.1 hpL hh.1,
    fullLocalHistoryTrusted_of_audit_pCarry_frame
      r.concrete q.2.concrete r.history q.2.history
      hr ha.2 hpR hh.2⟩

/-! ## Full current wrapper preservation -/

/-- `preserveDoneCheck` preserves all four local history marks.  DONE, toss,
and congest are exact identity branches.  The active CHECK branch needs only
`PreserveDoneCheckCompatible`, whose conclusion is precisely the existing
Algorithm-11 `CheckPairCompatible` premise at the actual marked intermediate
pair. -/
theorem markedPreserveDoneCheck_preserves_fullLocalHistoryTrusted
    (hψ : ψ > 0) (l r : MarkedAuthorizedAgentState n ψ)
    (hl : FullLocalHistoryTrusted l.concrete.core l.history)
    (hr : FullLocalHistoryTrusted r.concrete.core r.history)
    (hcompat : PreserveDoneCheckCompatible hψ l r) :
    let q := markedPreserveDoneCheck hψ l r
    FullLocalHistoryTrusted q.1.concrete.core q.1.history ∧
      FullLocalHistoryTrusted q.2.concrete.core q.2.history := by
  unfold PreserveDoneCheckCompatible at hcompat
  by_cases hdone :
      l.concrete.core.state = .done ∨ r.concrete.core.state = .done
  · simpa [markedPreserveDoneCheck, hdone] using And.intro hl hr
  · by_cases htoss :
        l.concrete.core.state = .toss ∨ r.concrete.core.state = .toss
    · simpa [markedPreserveDoneCheck, hdone, htoss] using And.intro hl hr
    · by_cases hcongest :
          l.concrete.core.state = .congest ∨
            r.concrete.core.state = .congest
      · simpa [markedPreserveDoneCheck, hdone, htoss, hcongest] using
          And.intro hl hr
      · have hnDoneL : l.concrete.core.state ≠ .done := by
          intro h
          exact hdone (Or.inl h)
        have hnDoneR : r.concrete.core.state ≠ .done := by
          intro h
          exact hdone (Or.inr h)
        have hnTossL : l.concrete.core.state ≠ .toss := by
          intro h
          exact htoss (Or.inl h)
        have hnTossR : r.concrete.core.state ≠ .toss := by
          intro h
          exact htoss (Or.inr h)
        have hnCongestL : l.concrete.core.state ≠ .congest := by
          intro h
          exact hcongest (Or.inl h)
        have hnCongestR : r.concrete.core.state ≠ .congest := by
          intro h
          exact hcongest (Or.inr h)
        have hactive : PreserveDoneCheckActive l r := by
          unfold PreserveDoneCheckActive
          exact ⟨hnDoneL, hnDoneR, hnTossL, hnTossR,
            hnCongestL, hnCongestR⟩

        let lm : MarkedAgentState n ψ :=
          ⟨l.concrete.core, l.history⟩
        let rm : MarkedAgentState n ψ :=
          ⟨r.concrete.core, r.history⟩
        let m := markedCheckSig hψ lm rm
        let q := authorizedCheckSig hψ l.concrete r.concrete

        have hc := hcompat hactive
        change
          (let l0 := markedCheckSetReady lm
           let r0 := markedCheckSetReady rm
           let l1 := markedCheckL hψ l0
           CheckPairCompatible hψ l1 r0) at hc

        have hlm : FullLocalHistoryTrusted lm.concrete lm.history := by
          simpa [lm] using hl
        have hrm : FullLocalHistoryTrusted rm.concrete rm.history := by
          simpa [rm] using hr
        have hm := markedCheckSig_preserves_fullLocalHistoryTrusted_local
          hψ lm rm hlm hrm hc
        change FullLocalHistoryTrusted m.1.concrete m.1.history ∧
          FullLocalHistoryTrusted m.2.concrete m.2.history at hm

        have he := erase_markedCheckSig hψ lm rm
        change (m.1.concrete, m.2.concrete) =
          checkSig hψ l.concrete.core r.concrete.core at he
        have hqCore :
            (q.1.core, q.2.core) =
              checkSig hψ l.concrete.core r.concrete.core := by
          rfl
        have hcore :
            (q.1.core, q.2.core) =
              (m.1.concrete, m.2.concrete) :=
          hqCore.trans he.symm
        have hcoreL : q.1.core = m.1.concrete :=
          congrArg Prod.fst hcore
        have hcoreR : q.2.core = m.2.concrete :=
          congrArg Prod.snd hcore
        have htrust :
            FullLocalHistoryTrusted q.1.core m.1.history ∧
              FullLocalHistoryTrusted q.2.core m.2.history := by
          constructor
          · rw [hcoreL]
            exact hm.1
          · rw [hcoreR]
            exact hm.2

        simpa [markedPreserveDoneCheck, hdone, htoss, hcongest,
          lm, rm, m, q] using htrust

end PPLLComparisonHistory

#print axioms PPLLComparisonHistory.erase_markedPreserveDoneCheck
#print axioms PPLLComparisonHistory.markedPreserveDoneCheck_preserves_fullLocalHistoryTrusted
