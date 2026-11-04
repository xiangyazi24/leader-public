import Leader.Wu.Comparison.HistoryEntryResetSanitize
import Leader.Wu.Comparison.HistoryCompare
import Leader.Wu.Elimination.MultiLeaderCleanup

set_option autoImplicit false
set_option Elab.async false
set_option pp.structureInstances false

namespace PPLLComparisonHistory

open PPLL PPLLRepair PPLLComparisonLifecycle
open PPLLAuthorizedComparisonRepair
open PPLLCompleteMultiLeaderCleanup

variable {n ψ : Nat}

/-! ## Small full-trust helpers -/

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

private theorem setStateSource_fullLocalHistoryTrusted
    (s : AgentState ψ) (h : LocalComparisonHistory n)
    (hu : FullLocalHistoryTrusted s h)
    (newState : MainState) (hactive : newState ≠ .none)
    (source : Fin n) :
    FullLocalHistoryTrusted
      { s with state := newState }
      { h with state := .trusted source } := by
  constructor
  · exact setStateSource_auditTrusted
      s h hu.1 newState hactive source
  · exact hu.2

private theorem copyStateSource_right_full
    (l r : MarkedAgentState n ψ)
    (hl : FullLocalHistoryTrusted l.concrete l.history)
    (hr : FullLocalHistoryTrusted r.concrete r.history)
    (hactive : l.concrete.state ≠ .none)
    (newState : MainState) (hnew : newState ≠ .none) :
    FullLocalHistoryTrusted
      { r.concrete with state := newState }
      { r.history with
        state := SourceMark.preserveTrusted l.history.state } := by
  obtain ⟨source, hsource⟩ :=
    stateSource_of_active l.concrete l.history hl.1 hactive
  have hpreserve : SourceMark.preserveTrusted l.history.state =
      .trusted source := by
    rw [hsource]
    rfl
  rw [hpreserve]
  exact setStateSource_fullLocalHistoryTrusted
    r.concrete r.history hr newState hnew source

private theorem copyStateSource_left_full
    (l r : MarkedAgentState n ψ)
    (hl : FullLocalHistoryTrusted l.concrete l.history)
    (hr : FullLocalHistoryTrusted r.concrete r.history)
    (hactive : r.concrete.state ≠ .none)
    (newState : MainState) (hnew : newState ≠ .none) :
    FullLocalHistoryTrusted
      { l.concrete with state := newState }
      { l.history with
        state := SourceMark.preserveTrusted r.history.state } := by
  obtain ⟨source, hsource⟩ :=
    stateSource_of_active r.concrete r.history hr.1 hactive
  have hpreserve : SourceMark.preserveTrusted r.history.state =
      .trusted source := by
    rw [hsource]
    rfl
  rw [hpreserve]
  exact setStateSource_fullLocalHistoryTrusted
    l.concrete l.history hl newState hnew source

/-! ## Promote the two old comparison joins to the four-field predicate -/

private theorem cmpUpdateSetPath2_pCarry_frame
    (hψ : ψ > 0) (u : AgentState ψ) :
    (cmpUpdateSetPath2 hψ u).p_carry = u.p_carry := by
  unfold cmpUpdateSetPath2
  repeat (first | rfl | split)

private theorem markedCmpUpdateSetPath2_pCarry_history_frame
    (hψ : ψ > 0) (u : MarkedAgentState n ψ) :
    (markedCmpUpdateSetPath2 hψ u).history.pCarry =
      u.history.pCarry := by
  unfold markedCmpUpdateSetPath2
  repeat (first | rfl | split)

private theorem markedCmpUpdateSetPath2_preserves_fullLocalHistoryTrusted
    (hψ : ψ > 0) (u : MarkedAgentState n ψ)
    (hu : FullLocalHistoryTrusted u.concrete u.history)
    (hcompat : CmpSetPath2Compatible hψ u) :
    FullLocalHistoryTrusted
      (markedCmpUpdateSetPath2 hψ u).concrete
      (markedCmpUpdateSetPath2 hψ u).history := by
  have ha := markedCmpUpdateSetPath2_preserves_auditLocalHistoryTrusted
    hψ u hu.1 hcompat
  have hp : (markedCmpUpdateSetPath2 hψ u).concrete.p_carry =
      u.concrete.p_carry := by
    rw [erase_markedCmpUpdateSetPath2 hψ u]
    exact cmpUpdateSetPath2_pCarry_frame hψ u.concrete
  have hh := markedCmpUpdateSetPath2_pCarry_history_frame hψ u
  exact fullLocalHistoryTrusted_of_audit_pCarry_frame
    u.concrete (markedCmpUpdateSetPath2 hψ u).concrete
    u.history (markedCmpUpdateSetPath2 hψ u).history
    hu ha hp hh

private theorem compareBitUpdateL_pCarry_frame
    (hψ : ψ > 0) (u : AgentState ψ) :
    (compareBitUpdateL hψ u).p_carry = u.p_carry := by
  unfold compareBitUpdateL
  repeat (first | rfl | split)

private theorem markedCompareBitL_pCarry_history_frame
    (hψ : ψ > 0) (u : MarkedAgentState n ψ) :
    (markedCompareBitL hψ u).history.pCarry = u.history.pCarry := by
  unfold markedCompareBitL
  repeat (first | rfl | split)

private theorem markedCompareBitL_preserves_fullLocalHistoryTrusted
    (hψ : ψ > 0) (u : MarkedAgentState n ψ)
    (hu : FullLocalHistoryTrusted u.concrete u.history)
    (hcompat : CompareBitLCompatible u) :
    FullLocalHistoryTrusted
      (markedCompareBitL hψ u).concrete
      (markedCompareBitL hψ u).history := by
  have ha := markedCompareBitL_preserves_auditLocalHistoryTrusted
    hψ u hu.1 hcompat
  have hp : (markedCompareBitL hψ u).concrete.p_carry =
      u.concrete.p_carry := by
    rw [erase_markedCompareBitL hψ u]
    exact compareBitUpdateL_pCarry_frame hψ u.concrete
  have hh := markedCompareBitL_pCarry_history_frame hψ u
  exact fullLocalHistoryTrusted_of_audit_pCarry_frame
    u.concrete (markedCompareBitL hψ u).concrete
    u.history (markedCompareBitL hψ u).history
    hu ha hp hh

private theorem compareSigInit_pCarry_frame (u : AgentState ψ) :
    (compareSigInit u).p_carry = u.p_carry := by
  unfold compareSigInit
  repeat (first | rfl | split)

private theorem markedCompareSigInit_pCarry_history_frame
    (u : MarkedAgentState n ψ) :
    (markedCompareSigInit u).history.pCarry = u.history.pCarry := by
  unfold markedCompareSigInit
  repeat (first | rfl | split)

private theorem markedCompareSigInit_preserves_fullLocalHistoryTrusted
    (u : MarkedAgentState n ψ)
    (hu : FullLocalHistoryTrusted u.concrete u.history) :
    FullLocalHistoryTrusted
      (markedCompareSigInit u).concrete
      (markedCompareSigInit u).history := by
  have ha := markedCompareSigInit_preserves_auditLocalHistoryTrusted u hu.1
  have hp : (markedCompareSigInit u).concrete.p_carry =
      u.concrete.p_carry := by
    rw [erase_markedCompareSigInit u]
    exact compareSigInit_pCarry_frame u.concrete
  have hh := markedCompareSigInit_pCarry_history_frame u
  exact fullLocalHistoryTrusted_of_audit_pCarry_frame
    u.concrete (markedCompareSigInit u).concrete
    u.history (markedCompareSigInit u).history
    hu ha hp hh

/-! ## Current authorization-gated CMP_UPDATE start -/

/-- Mark the exact current fresh-comparison start.  The executable permission
bit remains physical-only; when it actually starts `.congest`, the proof-side
state source is copied from the already trusted payload-zero path. -/
def markedAuthorizedCmpStart (hψ : ψ > 0)
    (u : MarkedAuthorizedAgentState n ψ) : MarkedAgentState n ψ :=
  let allowed := freshComparisonStart hψ u.concrete
  let fire := allowed && !comparisonActive u.concrete.core.state
  let out := if fire then
    { u.concrete.core with state := .congest }
  else u.concrete.core
  match fire with
  | true =>
      ⟨out, { u.history with
        state := SourceMark.preserveTrusted u.history.path }⟩
  | false => ⟨out, u.history⟩

/-- Erasure of the marked current start is the exact `lCore` expression used by
`authorizedCmpUpdate`. -/
theorem erase_markedAuthorizedCmpStart (hψ : ψ > 0)
    (u : MarkedAuthorizedAgentState n ψ) :
    (markedAuthorizedCmpStart hψ u).concrete =
      (if freshComparisonStart hψ u.concrete &&
          !comparisonActive u.concrete.core.state then
        { u.concrete.core with state := .congest }
      else u.concrete.core) := by
  unfold markedAuthorizedCmpStart
  dsimp only
  cases ha : freshComparisonStart hψ u.concrete <;>
    cases hc : comparisonActive u.concrete.core.state <;> rfl

/-- The authorization-gated start needs no compatibility premise: a true fresh
start already entails a present payload-zero path, whose trusted source is the
source of the new `.congest` state. -/
theorem markedAuthorizedCmpStart_preserves_fullLocalHistoryTrusted
    (hψ : ψ > 0) (u : MarkedAuthorizedAgentState n ψ)
    (hu : FullLocalHistoryTrusted u.concrete.core u.history) :
    FullLocalHistoryTrusted
      (markedAuthorizedCmpStart hψ u).concrete
      (markedAuthorizedCmpStart hψ u).history := by
  unfold markedAuthorizedCmpStart
  dsimp only
  cases ha : freshComparisonStart hψ u.concrete with
  | false =>
      simpa [ha] using hu
  | true =>
      cases hc : comparisonActive u.concrete.core.state with
      | true =>
          simpa [ha, hc] using hu
      | false =>
          have hpath : u.concrete.core.path ≠ .bot := by
            intro hbot
            simp [freshComparisonStart, hbot] at ha
          obtain ⟨source, hsource⟩ :=
            pathSource_of_present u.concrete.core u.history hu.1 hpath
          have hpreserve : SourceMark.preserveTrusted u.history.path =
              .trusted source := by
            rw [hsource]
            rfl
          have hs := setStateSource_fullLocalHistoryTrusted
            u.concrete.core u.history hu .congest (by decide) source
          simpa [ha, hc, hpreserve] using hs

/-! ## Current return-priority CMP_UPDATE state propagation -/

/-- Proof-side mirror of `cmpUpdateReturnPriority`.  Each physical state copy
copies exactly the source mark of the endpoint whose state drives that copy. -/
def markedCmpUpdateReturnPriority (hψ : ψ > 0)
    (l r : MarkedAgentState n ψ) :
    MarkedAgentState n ψ × MarkedAgentState n ψ :=
  let q := cmpUpdateReturnPriority hψ l.concrete r.concrete
  if _h1 : l.concrete.label = ⟨ψ - 1, by omega⟩ ∧
      r.concrete.state = .compare1 then
    (⟨q.1, { l.history with
      state := SourceMark.preserveTrusted r.history.state }⟩,
     ⟨q.2, r.history⟩)
  else if _h2 : r.concrete.state = .compare1 ∨
      r.concrete.state = .compare2 then
    (⟨q.1, { l.history with
      state := SourceMark.preserveTrusted r.history.state }⟩,
     ⟨q.2, r.history⟩)
  else if _h3 : l.concrete.label = ⟨ψ - 1, by omega⟩ ∧
      l.concrete.state = .congest then
    (⟨q.1, l.history⟩,
     ⟨q.2, { r.history with
      state := SourceMark.preserveTrusted l.history.state }⟩)
  else if _h4 : r.concrete.label = ⟨ψ - 1, by omega⟩ ∧
      l.concrete.state = .lock then
    (⟨q.1, l.history⟩,
     ⟨q.2, { r.history with
      state := SourceMark.preserveTrusted l.history.state }⟩)
  else if _h5 : l.concrete.state = .congest ∨
      l.concrete.state = .lock then
    (⟨q.1, l.history⟩,
     ⟨q.2, { r.history with
      state := SourceMark.preserveTrusted l.history.state }⟩)
  else
    (⟨q.1, l.history⟩, ⟨q.2, r.history⟩)

/-- Exact erasure to the current return-priority physical state propagation. -/
theorem erase_markedCmpUpdateReturnPriority (hψ : ψ > 0)
    (l r : MarkedAgentState n ψ) :
    let q := markedCmpUpdateReturnPriority hψ l r
    (q.1.concrete, q.2.concrete) =
      cmpUpdateReturnPriority hψ l.concrete r.concrete := by
  unfold markedCmpUpdateReturnPriority
  repeat (first | rfl | split)

/-- Every current return-priority state assignment preserves all four local
history fields.  No common-source join is performed by this stage. -/
theorem markedCmpUpdateReturnPriority_preserves_fullLocalHistoryTrusted
    (hψ : ψ > 0) (l r : MarkedAgentState n ψ)
    (hl : FullLocalHistoryTrusted l.concrete l.history)
    (hr : FullLocalHistoryTrusted r.concrete r.history) :
    let q := markedCmpUpdateReturnPriority hψ l r
    FullLocalHistoryTrusted q.1.concrete q.1.history ∧
      FullLocalHistoryTrusted q.2.concrete q.2.history := by
  unfold markedCmpUpdateReturnPriority
  dsimp only
  split
  next h1 =>
    have hq : cmpUpdateReturnPriority hψ l.concrete r.concrete =
        ({ l.concrete with state := .compare2 }, r.concrete) := by
      unfold cmpUpdateReturnPriority
      rw [if_pos h1]
    rw [hq]
    exact ⟨copyStateSource_left_full l r hl hr
      (by rw [h1.2]; decide) .compare2 (by decide), hr⟩
  next h1 =>
    split
    next h2 =>
      have hq : cmpUpdateReturnPriority hψ l.concrete r.concrete =
          ({ l.concrete with state := r.concrete.state }, r.concrete) := by
        unfold cmpUpdateReturnPriority
        rw [if_neg h1, if_pos h2]
      rw [hq]
      have hactive : r.concrete.state ≠ .none := by
        rcases h2 with hcompare1 | hcompare2
        · rw [hcompare1]
          decide
        · rw [hcompare2]
          decide
      exact ⟨copyStateSource_left_full l r hl hr
        hactive r.concrete.state hactive, hr⟩
    next h2 =>
      split
      next h3 =>
        have hq : cmpUpdateReturnPriority hψ l.concrete r.concrete =
            (l.concrete, { r.concrete with state := .lock }) := by
          unfold cmpUpdateReturnPriority
          rw [if_neg h1, if_neg h2, if_pos h3]
        rw [hq]
        exact ⟨hl, copyStateSource_right_full l r hl hr
          (by rw [h3.2]; decide) .lock (by decide)⟩
      next h3 =>
        split
        next h4 =>
          have hq : cmpUpdateReturnPriority hψ l.concrete r.concrete =
              (l.concrete, { r.concrete with state := .compare1 }) := by
            unfold cmpUpdateReturnPriority
            rw [if_neg h1, if_neg h2, if_neg h3, if_pos h4]
          rw [hq]
          exact ⟨hl, copyStateSource_right_full l r hl hr
            (by rw [h4.2]; decide) .compare1 (by decide)⟩
        next h4 =>
          split
          next h5 =>
            have hq : cmpUpdateReturnPriority hψ l.concrete r.concrete =
                (l.concrete, { r.concrete with state := l.concrete.state }) := by
              unfold cmpUpdateReturnPriority
              rw [if_neg h1, if_neg h2, if_neg h3, if_neg h4,
                if_pos h5]
            rw [hq]
            have hactive : l.concrete.state ≠ .none := by
              rcases h5 with hcongest | hlock
              · rw [hcongest]
                decide
              · rw [hlock]
                decide
            exact ⟨hl, copyStateSource_right_full l r hl hr
              hactive l.concrete.state hactive⟩
          next h5 =>
            have hq : cmpUpdateReturnPriority hψ l.concrete r.concrete =
                (l.concrete, r.concrete) := by
              unfold cmpUpdateReturnPriority
              rw [if_neg h1, if_neg h2, if_neg h3, if_neg h4,
                if_neg h5]
            rw [hq]
            exact ⟨hl, hr⟩

/-! ## Exact marked current `authorizedCmpUpdate` -/

/-- The sole source-join premise of the current authorized CMP_UPDATE.  It is
exactly the old `CmpSetPath2Compatible`, but evaluated after the authorization-
gated fresh start and the current return-priority state propagation. -/
def CurrentAuthorizedCmpUpdateCompatible (hψ : ψ > 0)
    (l r : MarkedAuthorizedAgentState n ψ) : Prop :=
  let l0 := markedAuthorizedCmpStart hψ l
  let rm : MarkedAgentState n ψ := ⟨r.concrete.core, r.history⟩
  let q1 := markedCmpUpdateReturnPriority hψ l0 rm
  CmpSetPath2Compatible hψ q1.1

/-- Exact marked lift of the current executable `authorizedCmpUpdate`.  Physical
permission consumption/normalization is left untouched; only the proof-side
state/path2 histories are threaded through its raw core stages. -/
def markedAuthorizedCmpUpdate (hψ : ψ > 0)
    (l r : MarkedAuthorizedAgentState n ψ) :
    MarkedAuthorizedAgentState n ψ × MarkedAuthorizedAgentState n ψ :=
  let l0 := markedAuthorizedCmpStart hψ l
  let rm : MarkedAgentState n ψ := ⟨r.concrete.core, r.history⟩
  let q1 := markedCmpUpdateReturnPriority hψ l0 rm
  let mL := markedCmpUpdateSetPath2 hψ q1.1
  let q := authorizedCmpUpdate hψ l.concrete r.concrete
  (⟨q.1, mL.history⟩, ⟨q.2, q1.2.history⟩)

/-- The marked current CMP_UPDATE erases definitionally to the executable
`authorizedCmpUpdate`, including its permission bit updates. -/
theorem erase_markedAuthorizedCmpUpdate (hψ : ψ > 0)
    (l r : MarkedAuthorizedAgentState n ψ) :
    let q := markedAuthorizedCmpUpdate hψ l r
    (q.1.concrete, q.2.concrete) =
      authorizedCmpUpdate hψ l.concrete r.concrete := by
  rfl

/-- Current authorized CMP_UPDATE preserves full local history under exactly
its post-propagation `CmpSetPath2Compatible` source join. -/
theorem markedAuthorizedCmpUpdate_preserves_fullLocalHistoryTrusted
    (hψ : ψ > 0)
    (l r : MarkedAuthorizedAgentState n ψ)
    (hl : FullLocalHistoryTrusted l.concrete.core l.history)
    (hr : FullLocalHistoryTrusted r.concrete.core r.history)
    (hcompat : CurrentAuthorizedCmpUpdateCompatible hψ l r) :
    let q := markedAuthorizedCmpUpdate hψ l r
    FullLocalHistoryTrusted q.1.concrete.core q.1.history ∧
      FullLocalHistoryTrusted q.2.concrete.core q.2.history := by
  let l0 := markedAuthorizedCmpStart hψ l
  have h0 := markedAuthorizedCmpStart_preserves_fullLocalHistoryTrusted
    hψ l hl
  change FullLocalHistoryTrusted l0.concrete l0.history at h0

  let rm : MarkedAgentState n ψ := ⟨r.concrete.core, r.history⟩
  let q1 := markedCmpUpdateReturnPriority hψ l0 rm
  have h1 := markedCmpUpdateReturnPriority_preserves_fullLocalHistoryTrusted
    hψ l0 rm h0 hr
  change FullLocalHistoryTrusted q1.1.concrete q1.1.history ∧
    FullLocalHistoryTrusted q1.2.concrete q1.2.history at h1

  change CmpSetPath2Compatible hψ q1.1 at hcompat
  let mL := markedCmpUpdateSetPath2 hψ q1.1
  have h2 := markedCmpUpdateSetPath2_preserves_fullLocalHistoryTrusted
    hψ q1.1 h1.1 hcompat
  change FullLocalHistoryTrusted mL.concrete mL.history at h2

  let phys := authorizedCmpUpdate hψ l.concrete r.concrete
  have he0 := erase_markedAuthorizedCmpStart hψ l
  have he1 := erase_markedCmpUpdateReturnPriority hψ l0 rm
  have he2 := erase_markedCmpUpdateSetPath2 hψ q1.1
  change l0.concrete =
    (if freshComparisonStart hψ l.concrete &&
        !comparisonActive l.concrete.core.state then
      { l.concrete.core with state := .congest }
    else l.concrete.core) at he0
  change (q1.1.concrete, q1.2.concrete) =
    cmpUpdateReturnPriority hψ l0.concrete r.concrete.core at he1
  change mL.concrete = cmpUpdateSetPath2 hψ q1.1.concrete at he2
  have he1L := congrArg Prod.fst he1
  have he1R := congrArg Prod.snd he1

  have hL : phys.1.core = mL.concrete := by
    dsimp [phys]
    unfold authorizedCmpUpdate
    dsimp only
    rw [← he0, ← he1L]
    exact he2.symm
  have hR : phys.2.core = q1.2.concrete := by
    dsimp [phys]
    unfold authorizedCmpUpdate
    dsimp only
    rw [← he0, ← he1R]

  change FullLocalHistoryTrusted phys.1.core mL.history ∧
    FullLocalHistoryTrusted phys.2.core q1.2.history
  rw [hL, hR]
  exact ⟨h2, h1.2⟩

/-! ## Action-one responder and COMPARE_BIT -/

/-- Exact marked responder repair.  The physical action-one helper changes only
an already-present path2 payload/action, so its source mark is retained. -/
def markedCompareBitRActionOne (hψ : ψ > 0)
    (u : MarkedAgentState n ψ) : MarkedAgentState n ψ :=
  ⟨compareBitUpdateRActionOne hψ u.concrete, u.history⟩

/-- The marked action-one responder erases exactly. -/
theorem erase_markedCompareBitRActionOne (hψ : ψ > 0)
    (u : MarkedAgentState n ψ) :
    (markedCompareBitRActionOne hψ u).concrete =
      compareBitUpdateRActionOne hψ u.concrete := by
  rfl

private theorem compareBitUpdateRActionOne_frame
    (hψ : ψ > 0) (u : AgentState ψ) :
    (compareBitUpdateRActionOne hψ u).state = u.state ∧
      (compareBitUpdateRActionOne hψ u).path = u.path ∧
      ((compareBitUpdateRActionOne hψ u).path2 = none ↔
        u.path2 = none) ∧
      (compareBitUpdateRActionOne hψ u).p_carry = u.p_carry := by
  unfold compareBitUpdateRActionOne
  repeat (first | constructor | rfl | split | simp_all)

/-- No compatibility premise is needed on the responder: action-one COMPARE_BIT
preserves path2 presence and all other tracked physical fields. -/
theorem markedCompareBitRActionOne_preserves_fullLocalHistoryTrusted
    (hψ : ψ > 0) (u : MarkedAgentState n ψ)
    (hu : FullLocalHistoryTrusted u.concrete u.history) :
    FullLocalHistoryTrusted
      (markedCompareBitRActionOne hψ u).concrete
      (markedCompareBitRActionOne hψ u).history := by
  have hf := compareBitUpdateRActionOne_frame hψ u.concrete
  unfold markedCompareBitRActionOne
  refine fullLocalHistoryTrusted_of_audit_pCarry_frame
    u.concrete (compareBitUpdateRActionOne hψ u.concrete)
    u.history u.history hu ?_ hf.2.2.2 rfl
  unfold AuditLocalHistoryTrusted
  constructor
  · rw [hf.1]
    exact hu.1.1
  constructor
  · rw [hf.2.1]
    exact hu.1.2.1
  · rcases hu.1.2.2 with hinactive | htrusted
    · left
      exact ⟨hf.2.2.1.mpr hinactive.1, hinactive.2⟩
    · right
      exact ⟨fun houtNone =>
        htrusted.1 (hf.2.2.1.mp houtNone), htrusted.2⟩

/-- Marked current COMPARE_BIT: responder uses the action-one guard, initiator
keeps the existing exact action-2 reconstruction history. -/
def markedCompareBitActionOne (hψ : ψ > 0)
    (l r : MarkedAgentState n ψ) :
    MarkedAgentState n ψ × MarkedAgentState n ψ :=
  let r' := markedCompareBitRActionOne hψ r
  (markedCompareBitL hψ l, r')

/-- Exact erasure to `PPLLCompleteMultiLeaderCleanup.compareBitActionOne`. -/
theorem erase_markedCompareBitActionOne (hψ : ψ > 0)
    (l r : MarkedAgentState n ψ) :
    let q := markedCompareBitActionOne hψ l r
    (q.1.concrete, q.2.concrete) =
      compareBitActionOne hψ l.concrete r.concrete := by
  change ((markedCompareBitL hψ l).concrete,
    (markedCompareBitRActionOne hψ r).concrete) = _
  rw [erase_markedCompareBitL hψ l,
    erase_markedCompareBitRActionOne hψ r]
  rfl

/-- Action-one COMPARE_BIT preserves all four local histories under only the
existing initiator reconstruction join. -/
theorem markedCompareBitActionOne_preserves_fullLocalHistoryTrusted
    (hψ : ψ > 0) (l r : MarkedAgentState n ψ)
    (hl : FullLocalHistoryTrusted l.concrete l.history)
    (hr : FullLocalHistoryTrusted r.concrete r.history)
    (hcompat : CompareBitLCompatible l) :
    let q := markedCompareBitActionOne hψ l r
    FullLocalHistoryTrusted q.1.concrete q.1.history ∧
      FullLocalHistoryTrusted q.2.concrete q.2.history := by
  exact ⟨markedCompareBitL_preserves_fullLocalHistoryTrusted
      hψ l hl hcompat,
    markedCompareBitRActionOne_preserves_fullLocalHistoryTrusted
      hψ r hr⟩

/-- Exact marked dispatcher for the current action-one COMPARE wrapper. -/
def markedCompareSigDispatchActionOne (hψ : ψ > 0)
    (l r : MarkedAgentState n ψ) :
    MarkedAgentState n ψ × MarkedAgentState n ψ :=
  match l.concrete.path2, r.concrete.path2 with
  | some _, _ => markedCompareBitActionOne hψ l r
  | _, some _ => markedCompareBitActionOne hψ l r
  | _, _ => (l, r)

/-- The marked action-one dispatcher erases exactly. -/
theorem erase_markedCompareSigDispatchActionOne (hψ : ψ > 0)
    (l r : MarkedAgentState n ψ) :
    let q := markedCompareSigDispatchActionOne hψ l r
    (q.1.concrete, q.2.concrete) =
      compareSigDispatchActionOne hψ l.concrete r.concrete := by
  unfold markedCompareSigDispatchActionOne compareSigDispatchActionOne
  cases l.concrete.path2 <;> cases r.concrete.path2
  · rfl
  · exact erase_markedCompareBitActionOne hψ l r
  · exact erase_markedCompareBitActionOne hψ l r
  · exact erase_markedCompareBitActionOne hψ l r

/-- Dispatch preservation needs only the initiator reconstruction join; the
responder action-one update itself is join-free. -/
theorem markedCompareSigDispatchActionOne_preserves_fullLocalHistoryTrusted
    (hψ : ψ > 0) (l r : MarkedAgentState n ψ)
    (hl : FullLocalHistoryTrusted l.concrete l.history)
    (hr : FullLocalHistoryTrusted r.concrete r.history)
    (hcompat : CompareBitLCompatible l) :
    let q := markedCompareSigDispatchActionOne hψ l r
    FullLocalHistoryTrusted q.1.concrete q.1.history ∧
      FullLocalHistoryTrusted q.2.concrete q.2.history := by
  unfold markedCompareSigDispatchActionOne
  cases l.concrete.path2 <;> cases r.concrete.path2
  · exact ⟨hl, hr⟩
  · exact markedCompareBitActionOne_preserves_fullLocalHistoryTrusted
      hψ l r hl hr hcompat
  · exact markedCompareBitActionOne_preserves_fullLocalHistoryTrusted
      hψ l r hl hr hcompat
  · exact markedCompareBitActionOne_preserves_fullLocalHistoryTrusted
      hψ l r hl hr hcompat

/-! ## Exact current authorized action-one COMPARE wrapper -/

/-- Authorized marked initialization.  The executable permit normalization is
kept exactly; only the existing marked `compareSigInit` history is attached. -/
def markedAuthorizedCompareSigInit
    (l : MarkedAuthorizedAgentState n ψ) : MarkedAuthorizedAgentState n ψ :=
  let lm : MarkedAgentState n ψ := ⟨l.concrete.core, l.history⟩
  let m := markedCompareSigInit lm
  let core := compareSigInit l.concrete.core
  let q : AuthorizedAgentState ψ :=
    ⟨core, normalizePermit core l.concrete.path0Crossed⟩
  ⟨q, m.history⟩

/-- Exact erasure of the authorized marked COMPARE initialization. -/
theorem erase_markedAuthorizedCompareSigInit
    (l : MarkedAuthorizedAgentState n ψ) :
    (markedAuthorizedCompareSigInit l).concrete =
      ⟨compareSigInit l.concrete.core,
        normalizePermit (compareSigInit l.concrete.core)
          l.concrete.path0Crossed⟩ := by
  rfl

/-- Authorized initialization preserves all four proof-side histories. -/
theorem markedAuthorizedCompareSigInit_preserves_fullLocalHistoryTrusted
    (l : MarkedAuthorizedAgentState n ψ)
    (hl : FullLocalHistoryTrusted l.concrete.core l.history) :
    FullLocalHistoryTrusted
      (markedAuthorizedCompareSigInit l).concrete.core
      (markedAuthorizedCompareSigInit l).history := by
  let lm : MarkedAgentState n ψ := ⟨l.concrete.core, l.history⟩
  let m := markedCompareSigInit lm
  have hm := markedCompareSigInit_preserves_fullLocalHistoryTrusted lm hl
  change FullLocalHistoryTrusted m.concrete m.history at hm
  have he := erase_markedCompareSigInit lm
  change m.concrete = compareSigInit l.concrete.core at he
  change FullLocalHistoryTrusted (compareSigInit l.concrete.core) m.history
  rw [← he]
  exact hm

/-- Exact source-join boundary for the current action-one authorized COMPARE.
The premise is demanded only after initialization when both physical paths are
present.  It contains exactly the current CMP_UPDATE path2-creation join and
the post-CMP_UPDATE initiator reconstruction join. -/
def CurrentCompareSigActionOneCompatible (hψ : ψ > 0)
    (l r : MarkedAuthorizedAgentState n ψ) : Prop :=
  let l0 := markedAuthorizedCompareSigInit l
  ∀ (_hlpath : l0.concrete.core.path ≠ .bot)
      (_hrpath : r.concrete.core.path ≠ .bot),
    CurrentAuthorizedCmpUpdateCompatible hψ l0 r ∧
      (let q := markedAuthorizedCmpUpdate hψ l0 r
       let lm : MarkedAgentState n ψ :=
         ⟨q.1.concrete.core, q.1.history⟩
       CompareBitLCompatible lm)

/-- Exact proof-side lift of
`PPLLCompleteMultiLeaderCleanup.authorizedCompareSigActionOne`. -/
def markedAuthorizedCompareSigActionOne (hψ : ψ > 0)
    (l r : MarkedAuthorizedAgentState n ψ) :
    MarkedAuthorizedAgentState n ψ × MarkedAuthorizedAgentState n ψ :=
  let l0 := markedAuthorizedCompareSigInit l
  match l0.concrete.core.path with
  | .bot => (l0, r)
  | .some _ _ =>
    match r.concrete.core.path with
    | .bot => (l0, r)
    | .some _ _ =>
      let q := markedAuthorizedCmpUpdate hψ l0 r
      let lm : MarkedAgentState n ψ :=
        ⟨q.1.concrete.core, q.1.history⟩
      let rm : MarkedAgentState n ψ :=
        ⟨q.2.concrete.core, q.2.history⟩
      let m := markedCompareSigDispatchActionOne hψ lm rm
      let out := compareSigDispatchActionOne
        hψ q.1.concrete.core q.2.concrete.core
      let lOut : AuthorizedAgentState ψ :=
        ⟨out.1, normalizePermit out.1 q.1.concrete.path0Crossed⟩
      let rOut : AuthorizedAgentState ψ :=
        ⟨out.2, normalizePermit out.2 q.2.concrete.path0Crossed⟩
      (⟨lOut, m.1.history⟩, ⟨rOut, m.2.history⟩)

theorem erase_markedAuthorizedCompareSigActionOne
    (hψ : ψ > 0)
    (l r : MarkedAuthorizedAgentState n ψ) :
    let q := markedAuthorizedCompareSigActionOne hψ l r
    (q.1.concrete, q.2.concrete) =
      authorizedCompareSigActionOne hψ l.concrete r.concrete := by
  change ((markedAuthorizedCompareSigActionOne hψ l r).1.concrete,
    (markedAuthorizedCompareSigActionOne hψ l r).2.concrete) =
      authorizedCompareSigActionOne hψ l.concrete r.concrete


  let init : AuthorizedAgentState ψ :=
    AuthorizedAgentState.mk
      (compareSigInit l.concrete.core)
      (normalizePermit (compareSigInit l.concrete.core)
        l.concrete.path0Crossed)


  let exec : AuthorizedAgentState ψ × AuthorizedAgentState ψ :=
    match init.core.path with
    | .bot => (init, r.concrete)
    | .some _ _ =>
      match r.concrete.core.path with
      | .bot => (init, r.concrete)
      | .some _ _ =>
        let q0 := authorizedCmpUpdate hψ init r.concrete
        let out0 := compareSigDispatchActionOne
          hψ q0.1.core q0.2.core
        (Prod.mk
          (AuthorizedAgentState.mk out0.1
            (normalizePermit out0.1 q0.1.path0Crossed))
          (AuthorizedAgentState.mk out0.2
            (normalizePermit out0.2 q0.2.path0Crossed)) :
          AuthorizedAgentState ψ × AuthorizedAgentState ψ)


  have hexec :
      authorizedCompareSigActionOne hψ l.concrete r.concrete = exec := by
    rfl
  rw [hexec]


  unfold markedAuthorizedCompareSigActionOne
  dsimp only
  let l0 := markedAuthorizedCompareSigInit l
  have h0 : l0.concrete = init := by
    simpa only [init] using erase_markedAuthorizedCompareSigInit l


  cases hlpath : l0.concrete.core.path with
  | bot =>
      change (l0.concrete, r.concrete) = exec
      have hinitpath : init.core.path = .bot := by
        rw [← h0]
        exact hlpath
      unfold exec
      rw [hinitpath]
      exact congrArg
        (fun x : AuthorizedAgentState ψ => (x, r.concrete)) h0


  | some pathLabel pathBit =>
      have hinitpath :
          init.core.path = .some pathLabel pathBit := by
        rw [← h0]
        exact hlpath
      cases hrpath : r.concrete.core.path with
      | bot =>
          change (l0.concrete, r.concrete) = exec
          unfold exec
          rw [hinitpath, hrpath]
          exact congrArg
            (fun x : AuthorizedAgentState ψ => (x, r.concrete)) h0


      | some rightLabel rightBit =>
          let q := markedAuthorizedCmpUpdate hψ l0 r
          have h1 := erase_markedAuthorizedCmpUpdate hψ l0 r
          let q0 := authorizedCmpUpdate hψ init r.concrete
          have h1' : (q.1.concrete, q.2.concrete) = q0 := by
            calc
              (q.1.concrete, q.2.concrete) =
                  authorizedCmpUpdate hψ l0.concrete r.concrete := by
                exact h1
              _ = authorizedCmpUpdate hψ init r.concrete := by
                rw [h0]
              _ = q0 := rfl
          have h1L := congrArg Prod.fst h1'
          have h1R := congrArg Prod.snd h1'


          let out := compareSigDispatchActionOne
            hψ q.1.concrete.core q.2.concrete.core
          change
            (Prod.mk
              (AuthorizedAgentState.mk out.1
                (normalizePermit out.1 q.1.concrete.path0Crossed))
              (AuthorizedAgentState.mk out.2
                (normalizePermit out.2 q.2.concrete.path0Crossed)) :
              AuthorizedAgentState ψ × AuthorizedAgentState ψ) = exec


          have hexecBranch :
              exec =
                (let out0 := compareSigDispatchActionOne
                    hψ q0.1.core q0.2.core
                 (Prod.mk
                   (AuthorizedAgentState.mk out0.1
                     (normalizePermit out0.1 q0.1.path0Crossed))
                   (AuthorizedAgentState.mk out0.2
                     (normalizePermit out0.2 q0.2.path0Crossed)) :
                   AuthorizedAgentState ψ × AuthorizedAgentState ψ)) := by
            unfold exec
            rw [hinitpath, hrpath]
          rw [hexecBranch]
          dsimp only
          rw [← h1L, ← h1R]

/-- The exact current action-one authorized COMPARE preserves all four local
history fields under exactly `CurrentCompareSigActionOneCompatible`.  No premise
can suppress a physical branch; both joins are checked only at the actual
intermediate states that consume them. -/
theorem markedAuthorizedCompareSigActionOne_preserves_fullLocalHistoryTrusted
    (hψ : ψ > 0)
    (l r : MarkedAuthorizedAgentState n ψ)
    (hl : FullLocalHistoryTrusted l.concrete.core l.history)
    (hr : FullLocalHistoryTrusted r.concrete.core r.history)
    (hcompat : CurrentCompareSigActionOneCompatible hψ l r) :
    let q := markedAuthorizedCompareSigActionOne hψ l r
    FullLocalHistoryTrusted q.1.concrete.core q.1.history ∧
      FullLocalHistoryTrusted q.2.concrete.core q.2.history := by
  change FullLocalHistoryTrusted
      (markedAuthorizedCompareSigActionOne hψ l r).1.concrete.core
      (markedAuthorizedCompareSigActionOne hψ l r).1.history ∧
    FullLocalHistoryTrusted
      (markedAuthorizedCompareSigActionOne hψ l r).2.concrete.core
      (markedAuthorizedCompareSigActionOne hψ l r).2.history
  unfold markedAuthorizedCompareSigActionOne
  dsimp only
  let l0 := markedAuthorizedCompareSigInit l
  have h0 := markedAuthorizedCompareSigInit_preserves_fullLocalHistoryTrusted
    l hl
  change FullLocalHistoryTrusted l0.concrete.core l0.history at h0
  cases hlpath : l0.concrete.core.path with
  | bot =>
      exact ⟨h0, hr⟩
  | some pathLabel pathBit =>
      cases hrpath : r.concrete.core.path with
      | bot =>
          exact ⟨h0, hr⟩
      | some rightLabel rightBit =>
          have hlpresent : l0.concrete.core.path ≠ .bot := by
            rw [hlpath]
            intro hbad
            contradiction
          have hrpresent : r.concrete.core.path ≠ .bot := by
            rw [hrpath]
            intro hbad
            contradiction
          obtain ⟨hcmp, hbit⟩ := hcompat hlpresent hrpresent
          let q := markedAuthorizedCmpUpdate hψ l0 r
          have h1 :=
            markedAuthorizedCmpUpdate_preserves_fullLocalHistoryTrusted
              hψ l0 r h0 hr hcmp
          change FullLocalHistoryTrusted q.1.concrete.core q.1.history ∧
            FullLocalHistoryTrusted q.2.concrete.core q.2.history at h1

          let lm : MarkedAgentState n ψ :=
            ⟨q.1.concrete.core, q.1.history⟩
          let rm : MarkedAgentState n ψ :=
            ⟨q.2.concrete.core, q.2.history⟩
          change CompareBitLCompatible lm at hbit
          let m := markedCompareSigDispatchActionOne hψ lm rm
          have h2 :=
            markedCompareSigDispatchActionOne_preserves_fullLocalHistoryTrusted
              hψ lm rm h1.1 h1.2 hbit
          change FullLocalHistoryTrusted m.1.concrete m.1.history ∧
            FullLocalHistoryTrusted m.2.concrete m.2.history at h2

          have he := erase_markedCompareSigDispatchActionOne hψ lm rm
          change (m.1.concrete, m.2.concrete) =
            compareSigDispatchActionOne
              hψ q.1.concrete.core q.2.concrete.core at he
          have heL := congrArg Prod.fst he
          have heR := congrArg Prod.snd he
          change FullLocalHistoryTrusted
              (compareSigDispatchActionOne
                hψ q.1.concrete.core q.2.concrete.core).1
              m.1.history ∧
            FullLocalHistoryTrusted
              (compareSigDispatchActionOne
                hψ q.1.concrete.core q.2.concrete.core).2
              m.2.history
          rw [← heL, ← heR]
          exact h2

end PPLLComparisonHistory

#print axioms PPLLComparisonHistory.erase_markedAuthorizedCmpUpdate
#print axioms PPLLComparisonHistory.markedAuthorizedCmpUpdate_preserves_fullLocalHistoryTrusted
#print axioms PPLLComparisonHistory.erase_markedCompareBitRActionOne
#print axioms PPLLComparisonHistory.markedCompareBitRActionOne_preserves_fullLocalHistoryTrusted
#print axioms PPLLComparisonHistory.erase_markedAuthorizedCompareSigActionOne
#print axioms PPLLComparisonHistory.markedAuthorizedCompareSigActionOne_preserves_fullLocalHistoryTrusted
