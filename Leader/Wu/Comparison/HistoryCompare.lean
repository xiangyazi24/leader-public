import Leader.Wu.Comparison.HistoryStages

/-!
# Comparison-state and path2 provenance

This module completes the Algorithm-6/7/8 comparison lifecycle.  Comparison
state waves are sourced from an authenticated `path`; path2 controls retain
that source while moving and changing action.  Whenever physical pseudocode can
splice independently valid fields, preservation carries an explicit common-
source premise rather than silently choosing one history.
-/

namespace PPLLComparisonHistory

open PPLL PPLLRepair PPLLComparisonLifecycle

/-! ## CMP_UPDATE state-wave start -/

/-- The no-source-rearm repair creates `congest` only from a present path and
copies that path's source into the comparison state wave. -/
def markedCmpUpdateStart (hψ : ψ > 0)
    (u : MarkedAgentState n ψ) : MarkedAgentState n ψ :=
  let out := if u.concrete.label = ⟨0, hψ⟩ ∧
      u.concrete.state ≠ .depart then
    { u.concrete with state := .congest }
  else u.concrete
  if _hstart : u.concrete.label = ⟨0, hψ⟩ ∧
      u.concrete.state ≠ .depart then
    ⟨out, { u.history with
      state := SourceMark.preserveTrusted u.history.path }⟩
  else ⟨out, u.history⟩

/-- Marked CMP_UPDATE start erases to its physical repaired prefix. -/
theorem erase_markedCmpUpdateStart (hψ : ψ > 0)
    (u : MarkedAgentState n ψ) :
    (markedCmpUpdateStart hψ u).concrete =
      (if u.concrete.label = ⟨0, hψ⟩ ∧ u.concrete.state ≠ .depart then
        { u.concrete with state := .congest }
      else u.concrete) := by
  unfold markedCmpUpdateStart
  split <;> rfl

/-- Starting the comparison state wave preserves fieldwise trust when the path
required by Algorithm 6 is present. -/
theorem markedCmpUpdateStart_preserves_auditLocalHistoryTrusted
    (hψ : ψ > 0) (u : MarkedAgentState n ψ)
    (hu : AuditLocalHistoryTrusted u.concrete u.history)
    (hpath : u.concrete.path ≠ .bot) :
    AuditLocalHistoryTrusted (markedCmpUpdateStart hψ u).concrete
      (markedCmpUpdateStart hψ u).history := by
  unfold markedCmpUpdateStart
  dsimp only
  split
  next hstart =>
    obtain ⟨source, hsource⟩ :=
      pathSource_of_present u.concrete u.history hu hpath
    have hpreserve : SourceMark.preserveTrusted u.history.path =
        .trusted source := by rw [hsource]; rfl
    rw [hpreserve]
    exact setStateSource_auditTrusted u.concrete u.history
      hu .congest (by decide) source
  next _ =>
    exact hu

/-! ## CMP_UPDATE state propagation -/

/-- Copy the source mark along exactly the same state-wave assignments as
`cmpUpdatePropagate`. -/
def markedCmpUpdatePropagate (hψ : ψ > 0)
    (l r : MarkedAgentState n ψ) :
    MarkedAgentState n ψ × MarkedAgentState n ψ :=
  let q := cmpUpdatePropagate hψ l.concrete r.concrete
  if _h1 : l.concrete.label = ⟨ψ - 1, by omega⟩ ∧
      l.concrete.state = .congest then
    (⟨q.1, l.history⟩, ⟨q.2, { r.history with
      state := SourceMark.preserveTrusted l.history.state }⟩)
  else if _h2 : r.concrete.label = ⟨ψ - 1, by omega⟩ ∧
      l.concrete.state = .lock then
    (⟨q.1, l.history⟩, ⟨q.2, { r.history with
      state := SourceMark.preserveTrusted l.history.state }⟩)
  else if _h3 : l.concrete.label = ⟨ψ - 1, by omega⟩ ∧
      r.concrete.state = .compare1 then
    (⟨q.1, { l.history with
      state := SourceMark.preserveTrusted r.history.state }⟩,
     ⟨q.2, r.history⟩)
  else if _h4 : l.concrete.state = .congest ∨ l.concrete.state = .lock then
    (⟨q.1, l.history⟩, ⟨q.2, { r.history with
      state := SourceMark.preserveTrusted l.history.state }⟩)
  else if _h5 : r.concrete.state = .compare1 ∨
      r.concrete.state = .compare2 then
    (⟨q.1, { l.history with
      state := SourceMark.preserveTrusted r.history.state }⟩,
     ⟨q.2, r.history⟩)
  else (⟨q.1, l.history⟩, ⟨q.2, r.history⟩)

/-- Marked CMP_UPDATE propagation erases exactly. -/
theorem erase_markedCmpUpdatePropagate (hψ : ψ > 0)
    (l r : MarkedAgentState n ψ) :
    let q := markedCmpUpdatePropagate hψ l r
    (q.1.concrete, q.2.concrete) =
      cmpUpdatePropagate hψ l.concrete r.concrete := by
  unfold markedCmpUpdatePropagate
  repeat (first | rfl | split)

private theorem copyStateSource_right
    (l r : MarkedAgentState n ψ)
    (hl : AuditLocalHistoryTrusted l.concrete l.history)
    (hr : AuditLocalHistoryTrusted r.concrete r.history)
    (hactive : l.concrete.state ≠ .none) (newState : MainState)
    (hnew : newState ≠ .none) :
    AuditLocalHistoryTrusted
      { r.concrete with state := newState }
      { r.history with state := SourceMark.preserveTrusted l.history.state } := by
  obtain ⟨source, hsource⟩ := stateSource_of_active
    l.concrete l.history hl hactive
  have hpreserve : SourceMark.preserveTrusted l.history.state =
      .trusted source := by rw [hsource]; rfl
  rw [hpreserve]
  exact setStateSource_auditTrusted r.concrete r.history hr
    newState hnew source

private theorem copyStateSource_left
    (l r : MarkedAgentState n ψ)
    (hl : AuditLocalHistoryTrusted l.concrete l.history)
    (hr : AuditLocalHistoryTrusted r.concrete r.history)
    (hactive : r.concrete.state ≠ .none) (newState : MainState)
    (hnew : newState ≠ .none) :
    AuditLocalHistoryTrusted
      { l.concrete with state := newState }
      { l.history with state := SourceMark.preserveTrusted r.history.state } := by
  obtain ⟨source, hsource⟩ := stateSource_of_active
    r.concrete r.history hr hactive
  have hpreserve : SourceMark.preserveTrusted r.history.state =
      .trusted source := by rw [hsource]; rfl
  rw [hpreserve]
  exact setStateSource_auditTrusted l.concrete l.history hl
    newState hnew source

/-- Every CMP_UPDATE state-wave assignment preserves fieldwise source trust by
copying the source of the state that drives that assignment. -/
theorem markedCmpUpdatePropagate_preserves_auditLocalHistoryTrusted
    (hψ : ψ > 0) (l r : MarkedAgentState n ψ)
    (hl : AuditLocalHistoryTrusted l.concrete l.history)
    (hr : AuditLocalHistoryTrusted r.concrete r.history) :
    let q := markedCmpUpdatePropagate hψ l r
    AuditLocalHistoryTrusted q.1.concrete q.1.history ∧
      AuditLocalHistoryTrusted q.2.concrete q.2.history := by
  unfold markedCmpUpdatePropagate
  dsimp only
  split
  next h1 =>
    have hq : cmpUpdatePropagate hψ l.concrete r.concrete =
        (l.concrete, { r.concrete with state := .lock }) := by
      unfold cmpUpdatePropagate
      rw [if_pos h1]
    rw [hq]
    exact ⟨hl, copyStateSource_right l r hl hr
      (by rw [h1.2]; decide) .lock (by decide)⟩
  next h1 =>
    split
    next h2 =>
      have hq : cmpUpdatePropagate hψ l.concrete r.concrete =
          (l.concrete, { r.concrete with state := .compare1 }) := by
        unfold cmpUpdatePropagate
        rw [if_neg h1, if_pos h2]
      rw [hq]
      exact ⟨hl, copyStateSource_right l r hl hr
        (by rw [h2.2]; decide) .compare1 (by decide)⟩
    next h2 =>
      split
      next h3 =>
        have hq : cmpUpdatePropagate hψ l.concrete r.concrete =
            ({ l.concrete with state := .compare2 }, r.concrete) := by
          unfold cmpUpdatePropagate
          rw [if_neg h1, if_neg h2, if_pos h3]
        rw [hq]
        exact ⟨copyStateSource_left l r hl hr
          (by rw [h3.2]; decide) .compare2 (by decide), hr⟩
      next h3 =>
        split
        next h4 =>
          have hq : cmpUpdatePropagate hψ l.concrete r.concrete =
              (l.concrete, { r.concrete with state := l.concrete.state }) := by
            unfold cmpUpdatePropagate
            rw [if_neg h1, if_neg h2, if_neg h3, if_pos h4]
          rw [hq]
          have hactive : l.concrete.state ≠ .none := by
            rcases h4 with hcongest | hlock
            · rw [hcongest]
              decide
            · rw [hlock]
              decide
          exact ⟨hl, copyStateSource_right l r hl hr
            hactive l.concrete.state hactive⟩
        next h4 =>
          split
          next h5 =>
            have hq : cmpUpdatePropagate hψ l.concrete r.concrete =
                ({ l.concrete with state := r.concrete.state }, r.concrete) := by
              unfold cmpUpdatePropagate
              rw [if_neg h1, if_neg h2, if_neg h3, if_neg h4,
                if_pos h5]
            rw [hq]
            have hactive : r.concrete.state ≠ .none := by
              rcases h5 with hcompare1 | hcompare2
              · rw [hcompare1]
                decide
              · rw [hcompare2]
                decide
            exact ⟨copyStateSource_left l r hl hr
              hactive r.concrete.state hactive, hr⟩
          next h5 =>
            have hq : cmpUpdatePropagate hψ l.concrete r.concrete =
                (l.concrete, r.concrete) := by
              unfold cmpUpdatePropagate
              rw [if_neg h1, if_neg h2, if_neg h3, if_neg h4,
                if_neg h5]
            rw [hq]
            exact ⟨hl, hr⟩

/-! ## CMP_UPDATE path2 creation -/

/-- Creating comparison-control path2 at label zero requires the returning state
wave and local path to share one source. -/
def CmpSetPath2Compatible (hψ : ψ > 0)
    (u : MarkedAgentState n ψ) : Prop :=
  (u.concrete.path ≠ .bot ∧ u.concrete.label = ⟨0, hψ⟩ ∧
      u.concrete.state = .compare2) →
    ∃ source, u.history.state = .trusted source ∧
      u.history.path = .trusted source

/-- Mark `cmpUpdateSetPath2`, tainting a physically allowed forged splice. -/
def markedCmpUpdateSetPath2 (hψ : ψ > 0)
    (u : MarkedAgentState n ψ) : MarkedAgentState n ψ :=
  let out := cmpUpdateSetPath2 hψ u.concrete
  match u.concrete.path with
  | .some _ _ =>
    if _hset : u.concrete.label = ⟨0, hψ⟩ ∧
        u.concrete.state = .compare2 then
      let source := SourceMark.agree u.history.state u.history.path
      ⟨out, { u.history with path2 := source }⟩
    else ⟨out, u.history⟩
  | .bot => ⟨out, u.history⟩

/-- Marked path2 creation erases exactly. -/
theorem erase_markedCmpUpdateSetPath2 (hψ : ψ > 0)
    (u : MarkedAgentState n ψ) :
    (markedCmpUpdateSetPath2 hψ u).concrete =
      cmpUpdateSetPath2 hψ u.concrete := by
  unfold markedCmpUpdateSetPath2
  repeat (first | rfl | split)

/-- Path2 creation preserves fieldwise source trust under common-source
compatibility. -/
theorem markedCmpUpdateSetPath2_preserves_auditLocalHistoryTrusted
    (hψ : ψ > 0) (u : MarkedAgentState n ψ)
    (hu : AuditLocalHistoryTrusted u.concrete u.history)
    (hcompat : CmpSetPath2Compatible hψ u) :
    AuditLocalHistoryTrusted (markedCmpUpdateSetPath2 hψ u).concrete
      (markedCmpUpdateSetPath2 hψ u).history := by
  unfold markedCmpUpdateSetPath2
  dsimp only
  split
  next pathLabel pathBit hpath =>
    split
    next hset =>
      have hpresent : u.concrete.path ≠ .bot := by
        rw [hpath]
        intro hbad
        contradiction
      obtain ⟨source, hstate, hpathSource⟩ := hcompat
        ⟨hpresent, hset.1, hset.2⟩
      have hagree : SourceMark.agree u.history.state u.history.path =
          .trusted source := by simp [SourceMark.agree, hstate, hpathSource]
      have hout : cmpUpdateSetPath2 hψ u.concrete =
          { u.concrete with path2 := some ⟨pathLabel, pathBit, ψ, 1⟩ } := by
        simp [cmpUpdateSetPath2, hpath, hset]
      rw [hout, hagree]
      unfold AuditLocalHistoryTrusted
      exact ⟨hu.1, hu.2.1,
        .inr ⟨by intro hbad; contradiction, source, rfl⟩⟩
    next hset =>
      have hout : cmpUpdateSetPath2 hψ u.concrete = u.concrete := by
        simp [cmpUpdateSetPath2, hpath, hset]
      rw [hout]
      exact hu
  next hpath =>
    have hout : cmpUpdateSetPath2 hψ u.concrete = u.concrete := by
      simp [cmpUpdateSetPath2, hpath]
    rw [hout]
    exact hu

/-- Full marked no-source-rearm CMP_UPDATE. -/
def markedCmpUpdate (hψ : ψ > 0)
    (l r : MarkedAgentState n ψ) :
    MarkedAgentState n ψ × MarkedAgentState n ψ :=
  let l0 := markedCmpUpdateStart hψ l
  let q1 := markedCmpUpdatePropagate hψ l0 r
  (markedCmpUpdateSetPath2 hψ q1.1, q1.2)

/-- Full marked CMP_UPDATE erases exactly to the integrated repair helper. -/
theorem erase_markedCmpUpdate (hψ : ψ > 0)
    (l r : MarkedAgentState n ψ) :
    let q := markedCmpUpdate hψ l r
    (q.1.concrete, q.2.concrete) =
      cmpUpdateNoSourceRearm hψ l.concrete r.concrete := by
  let l0 := markedCmpUpdateStart hψ l
  let q1 := markedCmpUpdatePropagate hψ l0 r
  have h0 := erase_markedCmpUpdateStart hψ l
  have h1 := erase_markedCmpUpdatePropagate hψ l0 r
  have h2 := erase_markedCmpUpdateSetPath2 hψ q1.1
  change l0.concrete =
    (if l.concrete.label = ⟨0, hψ⟩ ∧ l.concrete.state ≠ .depart then
      { l.concrete with state := .congest }
    else l.concrete) at h0
  change (q1.1.concrete, q1.2.concrete) =
    cmpUpdatePropagate hψ l0.concrete r.concrete at h1
  rw [h0] at h1
  have h1l := congrArg Prod.fst h1
  have h1r := congrArg Prod.snd h1
  change q1.1.concrete = _ at h1l
  change q1.2.concrete = _ at h1r
  change (markedCmpUpdateSetPath2 hψ q1.1).concrete =
    cmpUpdateSetPath2 hψ q1.1.concrete at h2
  change ((markedCmpUpdateSetPath2 hψ q1.1).concrete,
    q1.2.concrete) = _
  rw [h2, h1l, h1r]
  rfl

/-- Full CMP_UPDATE preserves fieldwise history when the caller provides a
present trusted path and the exact post-propagation path2-creation compatibility. -/
theorem markedCmpUpdate_preserves_auditLocalHistoryTrusted
    (hψ : ψ > 0) (l r : MarkedAgentState n ψ)
    (hl : AuditLocalHistoryTrusted l.concrete l.history)
    (hr : AuditLocalHistoryTrusted r.concrete r.history)
    (hlpath : l.concrete.path ≠ .bot)
    (hcompat :
      let l0 := markedCmpUpdateStart hψ l
      let q1 := markedCmpUpdatePropagate hψ l0 r
      CmpSetPath2Compatible hψ q1.1) :
    let q := markedCmpUpdate hψ l r
    AuditLocalHistoryTrusted q.1.concrete q.1.history ∧
      AuditLocalHistoryTrusted q.2.concrete q.2.history := by
  let l0 := markedCmpUpdateStart hψ l
  have h0 := markedCmpUpdateStart_preserves_auditLocalHistoryTrusted
    hψ l hl hlpath
  change AuditLocalHistoryTrusted l0.concrete l0.history at h0
  let q1 := markedCmpUpdatePropagate hψ l0 r
  have h1 := markedCmpUpdatePropagate_preserves_auditLocalHistoryTrusted
    hψ l0 r h0 hr
  change AuditLocalHistoryTrusted q1.1.concrete q1.1.history ∧
    AuditLocalHistoryTrusted q1.2.concrete q1.2.history at h1
  change CmpSetPath2Compatible hψ q1.1 at hcompat
  have h2 := markedCmpUpdateSetPath2_preserves_auditLocalHistoryTrusted
    hψ q1.1 h1.1 hcompat
  exact ⟨h2, h1.2⟩

/-! ## COMPARE_BIT path2 provenance -/

/-- Responder comparison updates the path2 payload/action but preserves its
source mark. -/
def markedCompareBitR (hψ : ψ > 0)
    (u : MarkedAgentState n ψ) : MarkedAgentState n ψ :=
  ⟨compareBitUpdateR hψ u.concrete, u.history⟩

/-- Responder COMPARE_BIT erases exactly. -/
theorem erase_markedCompareBitR (hψ : ψ > 0)
    (u : MarkedAgentState n ψ) :
    (markedCompareBitR hψ u).concrete = compareBitUpdateR hψ u.concrete := by
  rfl

private theorem compareBitUpdateR_frame (hψ : ψ > 0) (u : AgentState ψ) :
    (compareBitUpdateR hψ u).state = u.state ∧
      (compareBitUpdateR hψ u).path = u.path ∧
      ((compareBitUpdateR hψ u).path2 = none ↔ u.path2 = none) := by
  unfold compareBitUpdateR
  repeat (first | constructor | rfl | split | simp_all)

/-- Responder COMPARE_BIT preserves fieldwise source trust. -/
theorem markedCompareBitR_preserves_auditLocalHistoryTrusted
    (hψ : ψ > 0) (u : MarkedAgentState n ψ)
    (hu : AuditLocalHistoryTrusted u.concrete u.history) :
    AuditLocalHistoryTrusted (markedCompareBitR hψ u).concrete
      (markedCompareBitR hψ u).history := by
  have hf := compareBitUpdateR_frame hψ u.concrete
  unfold markedCompareBitR AuditLocalHistoryTrusted
  constructor
  · rw [hf.1]
    exact hu.1
  constructor
  · rw [hf.2.1]
    exact hu.2.1
  · rcases hu.2.2 with hinactive | htrusted
    · left
      exact ⟨hf.2.2.mpr hinactive.1, hinactive.2⟩
    · right
      exact ⟨fun houtNone => htrusted.1 (hf.2.2.mp houtNone), htrusted.2⟩

/-- Returning action-2 path2 and the local path must name one source before the
next-bit path2 payload is reconstructed. -/
def CompareBitLCompatible (u : MarkedAgentState n ψ) : Prop :=
  (u.concrete.path2 ≠ none ∧ u.concrete.path ≠ .bot ∧
      ∃ p2, u.concrete.path2 = some p2 ∧
        p2.action = 2 ∧ p2.position = 0) →
    ∃ source, u.history.path2 = .trusted source ∧
      u.history.path = .trusted source

/-- Mark initiator next-bit reconstruction, tainting incompatible sources. -/
def markedCompareBitL (hψ : ψ > 0)
    (u : MarkedAgentState n ψ) : MarkedAgentState n ψ :=
  let out := compareBitUpdateL hψ u.concrete
  match u.concrete.path2, u.concrete.path with
  | some p2, .some _ _ =>
    if _hset : p2.action = 2 ∧ p2.position = 0 then
      let source := SourceMark.agree u.history.path2 u.history.path
      ⟨out, { u.history with path2 := source }⟩
    else ⟨out, u.history⟩
  | _, _ => ⟨out, u.history⟩

/-- Initiator COMPARE_BIT erases exactly. -/
theorem erase_markedCompareBitL (hψ : ψ > 0)
    (u : MarkedAgentState n ψ) :
    (markedCompareBitL hψ u).concrete = compareBitUpdateL hψ u.concrete := by
  unfold markedCompareBitL
  repeat (first | rfl | split)

/-- Initiator next-bit reconstruction preserves fieldwise trust under source
compatibility. -/
theorem markedCompareBitL_preserves_auditLocalHistoryTrusted
    (hψ : ψ > 0) (u : MarkedAgentState n ψ)
    (hu : AuditLocalHistoryTrusted u.concrete u.history)
    (hcompat : CompareBitLCompatible u) :
    AuditLocalHistoryTrusted (markedCompareBitL hψ u).concrete
      (markedCompareBitL hψ u).history := by
  unfold markedCompareBitL
  dsimp only
  split
  next p2 pathLabel pathBit hp2 hpath =>
    split
    next hset =>
      have hp2Present : u.concrete.path2 ≠ none := by
        rw [hp2]
        intro hbad
        contradiction
      have hpathPresent : u.concrete.path ≠ .bot := by
        rw [hpath]
        intro hbad
        contradiction
      obtain ⟨source, hp2Source, hpathSource⟩ := hcompat
        ⟨hp2Present, hpathPresent, p2, hp2, hset.1, hset.2⟩
      have hagree : SourceMark.agree u.history.path2 u.history.path =
          .trusted source := by
        simp [SourceMark.agree, hp2Source, hpathSource]
      have hout : compareBitUpdateL hψ u.concrete =
          { u.concrete with path2 := some ⟨pathLabel, pathBit, ψ, 1⟩ } := by
        simp [compareBitUpdateL, hp2, hpath, hset]
      rw [hout, hagree]
      unfold AuditLocalHistoryTrusted
      exact ⟨hu.1, hu.2.1,
        .inr ⟨by intro hbad; contradiction, source, rfl⟩⟩
    next hset =>
      have hout : compareBitUpdateL hψ u.concrete = u.concrete := by
        simp [compareBitUpdateL, hp2, hpath, hset]
      rw [hout]
      exact hu
  next hother =>
    have hout : compareBitUpdateL hψ u.concrete = u.concrete := by
      unfold compareBitUpdateL
      cases hp2 : u.concrete.path2 with
      | none => rfl
      | some p2 =>
        cases hpath : u.concrete.path with
        | bot => rfl
        | some label bit =>
          exact (hother p2 label bit hp2 hpath).elim
    rw [hout]
    exact hu

/-- Full marked COMPARE_BIT, preserving the physical responder-first order. -/
def markedCompareBit (hψ : ψ > 0)
    (l r : MarkedAgentState n ψ) :
    MarkedAgentState n ψ × MarkedAgentState n ψ :=
  let r' := markedCompareBitR hψ r
  (markedCompareBitL hψ l, r')

/-- Full marked COMPARE_BIT erases exactly. -/
theorem erase_markedCompareBit (hψ : ψ > 0)
    (l r : MarkedAgentState n ψ) :
    let q := markedCompareBit hψ l r
    (q.1.concrete, q.2.concrete) = compareBit hψ l.concrete r.concrete := by
  change ((markedCompareBitL hψ l).concrete,
    (markedCompareBitR hψ r).concrete) = _
  rw [erase_markedCompareBitL, erase_markedCompareBitR]
  rfl

/-- Full COMPARE_BIT preserves fieldwise trust under initiator source
compatibility. -/
theorem markedCompareBit_preserves_auditLocalHistoryTrusted
    (hψ : ψ > 0) (l r : MarkedAgentState n ψ)
    (hl : AuditLocalHistoryTrusted l.concrete l.history)
    (hr : AuditLocalHistoryTrusted r.concrete r.history)
    (hcompat : CompareBitLCompatible l) :
    let q := markedCompareBit hψ l r
    AuditLocalHistoryTrusted q.1.concrete q.1.history ∧
      AuditLocalHistoryTrusted q.2.concrete q.2.history := by
  exact ⟨markedCompareBitL_preserves_auditLocalHistoryTrusted
      hψ l hl hcompat,
    markedCompareBitR_preserves_auditLocalHistoryTrusted hψ r hr⟩

/-! ## Full COMPARE dispatch and composition -/

/-- Algorithm 6 clears comparison-state history exactly when its initialization
clears state because the initiator has no path. -/
def markedCompareSigInit (u : MarkedAgentState n ψ) :
    MarkedAgentState n ψ :=
  let out := compareSigInit u.concrete
  match u.concrete.path with
  | .bot => ⟨out, { u.history with state := .absent }⟩
  | .some _ _ => ⟨out, u.history⟩

/-- Marked COMPARE initialization erases exactly. -/
theorem erase_markedCompareSigInit (u : MarkedAgentState n ψ) :
    (markedCompareSigInit u).concrete = compareSigInit u.concrete := by
  unfold markedCompareSigInit
  cases u.concrete.path <;> rfl

/-- Deleting state when no path exists preserves fieldwise source trust. -/
theorem markedCompareSigInit_preserves_auditLocalHistoryTrusted
    (u : MarkedAgentState n ψ)
    (hu : AuditLocalHistoryTrusted u.concrete u.history) :
    AuditLocalHistoryTrusted (markedCompareSigInit u).concrete
      (markedCompareSigInit u).history := by
  cases hpath : u.concrete.path with
  | bot =>
      have hu' := hu
      unfold AuditLocalHistoryTrusted at hu'
      rw [hpath] at hu'
      unfold markedCompareSigInit compareSigInit
      rw [hpath]
      dsimp only
      unfold AuditLocalHistoryTrusted
      exact ⟨.inl ⟨rfl, rfl⟩, hu'.2⟩
  | some pathLabel pathBit =>
      unfold markedCompareSigInit compareSigInit
      rw [hpath]
      exact hu

/-- Marked Algorithm-6 dispatch invokes COMPARE_BIT exactly when either path2
control is present. -/
def markedCompareSigDispatch (hψ : ψ > 0)
    (l r : MarkedAgentState n ψ) :
    MarkedAgentState n ψ × MarkedAgentState n ψ :=
  match l.concrete.path2, r.concrete.path2 with
  | some _, _ => markedCompareBit hψ l r
  | _, some _ => markedCompareBit hψ l r
  | _, _ => (l, r)

/-- Marked COMPARE dispatch erases exactly. -/
theorem erase_markedCompareSigDispatch (hψ : ψ > 0)
    (l r : MarkedAgentState n ψ) :
    let q := markedCompareSigDispatch hψ l r
    (q.1.concrete, q.2.concrete) =
      compareSigDispatch hψ l.concrete r.concrete := by
  unfold markedCompareSigDispatch compareSigDispatch
  cases l.concrete.path2 <;> cases r.concrete.path2
  · rfl
  · exact erase_markedCompareBit hψ l r
  · exact erase_markedCompareBit hψ l r
  · exact erase_markedCompareBit hψ l r

/-- COMPARE dispatch preserves fieldwise trust when an initiator next-bit
reconstruction, if enabled, joins path2 and path from one source. -/
theorem markedCompareSigDispatch_preserves_auditLocalHistoryTrusted
    (hψ : ψ > 0) (l r : MarkedAgentState n ψ)
    (hl : AuditLocalHistoryTrusted l.concrete l.history)
    (hr : AuditLocalHistoryTrusted r.concrete r.history)
    (hcompat : CompareBitLCompatible l) :
    let q := markedCompareSigDispatch hψ l r
    AuditLocalHistoryTrusted q.1.concrete q.1.history ∧
      AuditLocalHistoryTrusted q.2.concrete q.2.history := by
  unfold markedCompareSigDispatch
  cases l.concrete.path2 <;> cases r.concrete.path2
  · exact ⟨hl, hr⟩
  · exact markedCompareBit_preserves_auditLocalHistoryTrusted
      hψ l r hl hr hcompat
  · exact markedCompareBit_preserves_auditLocalHistoryTrusted
      hψ l r hl hr hcompat
  · exact markedCompareBit_preserves_auditLocalHistoryTrusted
      hψ l r hl hr hcompat

/-- The two source joins used by full COMPARE, demanded only when both physical
paths are present and CMP_UPDATE actually runs. -/
def CompareSigCompatible (hψ : ψ > 0)
    (l r : MarkedAgentState n ψ) : Prop :=
  let l0 := markedCompareSigInit l
  ∀ (_hlpath : l0.concrete.path ≠ .bot)
      (_hrpath : r.concrete.path ≠ .bot),
    (let l1 := markedCmpUpdateStart hψ l0
     let q1 := markedCmpUpdatePropagate hψ l1 r
     CmpSetPath2Compatible hψ q1.1) ∧
      CompareBitLCompatible (markedCmpUpdate hψ l0 r).1

/-- Full marked Algorithm 6 with the no-source-rearm physical repair. -/
def markedCompareSig (hψ : ψ > 0)
    (l r : MarkedAgentState n ψ) :
    MarkedAgentState n ψ × MarkedAgentState n ψ :=
  let l0 := markedCompareSigInit l
  match l0.concrete.path with
  | .bot => (l0, r)
  | .some _ _ =>
    match r.concrete.path with
    | .some _ _ =>
      let q := markedCmpUpdate hψ l0 r
      markedCompareSigDispatch hψ q.1 q.2
    | .bot => (l0, r)

/-- Full marked COMPARE erases exactly to `compareSigNoSourceRearm`. -/
theorem erase_markedCompareSig (hψ : ψ > 0)
    (l r : MarkedAgentState n ψ) :
    let q := markedCompareSig hψ l r
    (q.1.concrete, q.2.concrete) =
      compareSigNoSourceRearm hψ l.concrete r.concrete := by
  change ((markedCompareSig hψ l r).1.concrete,
    (markedCompareSig hψ l r).2.concrete) = _
  unfold markedCompareSig
  dsimp only
  let l0 := markedCompareSigInit l
  have h0 := erase_markedCompareSigInit l
  change l0.concrete = compareSigInit l.concrete at h0
  cases hlpath : l0.concrete.path with
  | bot =>
      change (l0.concrete, r.concrete) = _
      unfold compareSigNoSourceRearm
      rw [← h0]
      dsimp only
      rw [hlpath]
  | some pathLabel pathBit =>
      cases hrpath : r.concrete.path with
      | bot =>
          change (l0.concrete, r.concrete) = _
          unfold compareSigNoSourceRearm
          rw [← h0]
          dsimp only
          rw [hlpath, hrpath]
      | some rightLabel rightBit =>
          let q := markedCmpUpdate hψ l0 r
          let out := markedCompareSigDispatch hψ q.1 q.2
          have h1 := erase_markedCmpUpdate hψ l0 r
          have h2 := erase_markedCompareSigDispatch hψ q.1 q.2
          change (q.1.concrete, q.2.concrete) =
            cmpUpdateNoSourceRearm hψ l0.concrete r.concrete at h1
          change (out.1.concrete, out.2.concrete) =
            compareSigDispatch hψ q.1.concrete q.2.concrete at h2
          have h1l := congrArg Prod.fst h1
          have h1r := congrArg Prod.snd h1
          change q.1.concrete = _ at h1l
          change q.2.concrete = _ at h1r
          change (out.1.concrete, out.2.concrete) = _
          unfold compareSigNoSourceRearm
          rw [← h0]
          dsimp only
          rw [hlpath, hrpath, h2, h1l, h1r]

/-- Full COMPARE preserves fieldwise source history under exactly its two
physical join compatibilities. No premise can suppress a physical branch. -/
theorem markedCompareSig_preserves_auditLocalHistoryTrusted
    (hψ : ψ > 0) (l r : MarkedAgentState n ψ)
    (hl : AuditLocalHistoryTrusted l.concrete l.history)
    (hr : AuditLocalHistoryTrusted r.concrete r.history)
    (hcompat : CompareSigCompatible hψ l r) :
    let q := markedCompareSig hψ l r
    AuditLocalHistoryTrusted q.1.concrete q.1.history ∧
      AuditLocalHistoryTrusted q.2.concrete q.2.history := by
  change AuditLocalHistoryTrusted (markedCompareSig hψ l r).1.concrete
    (markedCompareSig hψ l r).1.history ∧
    AuditLocalHistoryTrusted (markedCompareSig hψ l r).2.concrete
      (markedCompareSig hψ l r).2.history
  unfold markedCompareSig
  dsimp only
  let l0 := markedCompareSigInit l
  have h0 := markedCompareSigInit_preserves_auditLocalHistoryTrusted l hl
  change AuditLocalHistoryTrusted l0.concrete l0.history at h0
  cases hlpath : l0.concrete.path with
  | bot => exact ⟨h0, hr⟩
  | some pathLabel pathBit =>
      cases hrpath : r.concrete.path with
      | bot => exact ⟨h0, hr⟩
      | some rightLabel rightBit =>
          have hlpresent : l0.concrete.path ≠ .bot := by
            rw [hlpath]
            intro hbad
            contradiction
          have hrpresent : r.concrete.path ≠ .bot := by
            rw [hrpath]
            intro hbad
            contradiction
          obtain ⟨hset, hbit⟩ := hcompat hlpresent hrpresent
          let q := markedCmpUpdate hψ l0 r
          have h1 := markedCmpUpdate_preserves_auditLocalHistoryTrusted
            hψ l0 r h0 hr hlpresent hset
          change AuditLocalHistoryTrusted q.1.concrete q.1.history ∧
            AuditLocalHistoryTrusted q.2.concrete q.2.history at h1
          exact markedCompareSigDispatch_preserves_auditLocalHistoryTrusted
            hψ q.1 q.2 h1.1 h1.2 hbit

/-! ## Active compatibility witnesses -/

/-- A concrete active path/state join whose marks share source zero. This small
witness shows CMP_UPDATE's path2-creation premise is not an empty interface. -/
def activeCmpSetWitness : MarkedAgentState 1 2 :=
  let concrete : AgentState 2 :=
    { PPLLCounterexample.state2 0 with state := .compare2, path := .some 0 0 }
  ⟨concrete, { state := .trusted 0, path := .trusted 0, path2 := .absent, pCarry := .absent }⟩

/-- The active path/state witness satisfies the CMP_UPDATE join premise. -/
theorem activeCmpSetWitness_compatible :
    CmpSetPath2Compatible (by decide : 2 > 0) activeCmpSetWitness := by
  intro _
  exact ⟨0, rfl, rfl⟩

/-- A concrete active returning path2/path join with a common source. -/
def activeCompareBitWitness : MarkedAgentState 1 2 :=
  let concrete : AgentState 2 :=
    { PPLLCounterexample.state2 0 with path := .some 0 0, path2 := some ⟨0, 0, 0, 2⟩ }
  ⟨concrete, { state := .absent, path := .trusted 0, path2 := .trusted 0, pCarry := .absent }⟩

/-- The returning comparison-control witness satisfies COMPARE_BIT's join. -/
theorem activeCompareBitWitness_compatible :
    CompareBitLCompatible activeCompareBitWitness := by
  intro _
  exact ⟨0, rfl, rfl⟩

/-- If COMPARE has no initiator path after initialization, its compatibility
interface is inhabited because no source join can execute. -/
theorem compareSigCompatible_of_initialized_path_bot
    (hψ : ψ > 0) (l r : MarkedAgentState n ψ)
    (hbot : (markedCompareSigInit l).concrete.path = .bot) :
    CompareSigCompatible hψ l r := by
  intro hlpath _
  exact (hlpath hbot).elim

end PPLLComparisonHistory
