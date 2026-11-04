import Leader.Wu.Comparison.History

/-!
# Comparison history through cleaning, movement, checking, and lottery

This module continues the edge-aware comparison history after GENSIG.  Each
physical subalgorithm is factored into source-mark updates with exact erasure
and a structural preservation theorem.  Compatibility premises are exposed
only at physical joins where independently valid lineages can otherwise splice.
-/

namespace PPLLComparisonHistory

open PPLL PPLLRepair PPLLComparisonLifecycle

/-! ## CLEAN_SIG deletion-only history -/

/-- Projection of exactly the three fields whose provenance is tracked here. -/
structure ComparisonFieldView (ψ : Nat) where
  state : MainState
  path : PathInfo
  path2 : Option Path2Info
  deriving DecidableEq, Repr

/-- Extract the comparison field view from an audit state. -/
def ComparisonFieldView.ofState (s : AgentState ψ) : ComparisonFieldView ψ :=
  ⟨s.state, s.path, s.path2⟩

private theorem cleanSigGenConnect_view (u : AgentState ψ) :
    ComparisonFieldView.ofState (cleanSigGenConnect u) =
      ComparisonFieldView.ofState u := by
  unfold cleanSigGenConnect ComparisonFieldView.ofState
  split <;> simp

private theorem cleanSigStep3_view (l r : AgentState ψ) :
    ComparisonFieldView.ofState (cleanSigStep3 l r).1 =
        ComparisonFieldView.ofState l ∧
      ComparisonFieldView.ofState (cleanSigStep3 l r).2 =
        ComparisonFieldView.ofState r := by
  unfold cleanSigStep3 ComparisonFieldView.ofState
  repeat (first | constructor | rfl | split)

private theorem cleanSigStep4_view (l r : AgentState ψ) :
    ComparisonFieldView.ofState (cleanSigStep4 l r).1 =
        ComparisonFieldView.ofState l ∧
      ComparisonFieldView.ofState (cleanSigStep4 l r).2 =
        ComparisonFieldView.ofState r := by
  unfold cleanSigStep4 ComparisonFieldView.ofState
  repeat (first | constructor | rfl | split)

private theorem cleanSigStep5_view (hψ : ψ > 0) (l r : AgentState ψ) :
    ComparisonFieldView.ofState (cleanSigStep5 hψ l r).1 =
        ComparisonFieldView.ofState l ∧
      ComparisonFieldView.ofState (cleanSigStep5 hψ l r).2 =
        ComparisonFieldView.ofState r := by
  unfold cleanSigStep5 ComparisonFieldView.ofState
  repeat (first | constructor | rfl | split)

private theorem cleanSigStep6_view (hψ : ψ > 0) (l r : AgentState ψ) :
    ComparisonFieldView.ofState (cleanSigStep6 hψ l r).1 =
        ComparisonFieldView.ofState l ∧
      ComparisonFieldView.ofState (cleanSigStep6 hψ l r).2 =
        ComparisonFieldView.ofState r := by
  unfold cleanSigStep6 ComparisonFieldView.ofState
  repeat (first | constructor | rfl | split)

private theorem cleanSigCleanApply_frame (u : AgentState ψ) :
    ((cleanSigCleanApply u).path = .bot ∨
        (cleanSigCleanApply u).path = u.path) ∧
      (cleanSigCleanApply u).state = u.state ∧
      (cleanSigCleanApply u).path2 = u.path2 := by
  cases hp : u.path with
  | bot => simp [cleanSigCleanApply, hp]
  | some label bit =>
    cases hp4 : u.path4 with
    | none =>
      cases hp5 : u.path5 with
      | none => simp [cleanSigCleanApply, hp, hp4, hp5]
      | some p5 =>
        rcases p5 with ⟨label5, bit5⟩
        by_cases h5 : label5 = (-1 : Int) <;>
          simp [cleanSigCleanApply, hp, hp4, hp5, h5]
    | some p4 =>
      rcases p4 with ⟨label4, bit4⟩
      cases hp5 : u.path5 with
      | none =>
        by_cases h4 : label4 = (-1 : Int) <;>
          simp [cleanSigCleanApply, hp, hp4, hp5, h4]
      | some p5 =>
        rcases p5 with ⟨label5, bit5⟩
        by_cases h4 : label4 = (-1 : Int) <;>
          by_cases h5 : label5 = (-1 : Int) <;>
            simp [cleanSigCleanApply, hp, hp4, hp5, h4, h5]

/-- CLEAN_SIG can only preserve or delete `path`; it leaves `state` and
`path2` unchanged.  This structural fact justifies treating path4/path5 as
untrusted deletion controls rather than source-bearing data. -/
theorem cleanSig_comparison_frame (hψ : ψ > 0) (l r : AgentState ψ) :
    let q := cleanSig hψ l r
    (q.1.path = .bot ∨ q.1.path = l.path) ∧
      (q.2.path = .bot ∨ q.2.path = r.path) ∧
      q.1.state = l.state ∧ q.2.state = r.state ∧
      q.1.path2 = l.path2 ∧ q.2.path2 = r.path2 := by
  let l0 := cleanSigGenConnect l
  let r0 := cleanSigGenConnect r
  let q1 := cleanSigStep3 l0 r0
  let q2 := cleanSigStep4 q1.1 q1.2
  let q3 := cleanSigStep5 hψ q2.1 q2.2
  let q4 := cleanSigStep6 hψ q3.1 q3.2
  have hl0 := cleanSigGenConnect_view l
  have hr0 := cleanSigGenConnect_view r
  have h1 := cleanSigStep3_view l0 r0
  have h2 := cleanSigStep4_view q1.1 q1.2
  have h3 := cleanSigStep5_view hψ q2.1 q2.2
  have h4 := cleanSigStep6_view hψ q3.1 q3.2
  have hlpre : ComparisonFieldView.ofState q4.1 =
      ComparisonFieldView.ofState l := h4.1.trans
    (h3.1.trans (h2.1.trans (h1.1.trans hl0)))
  have hrpre : ComparisonFieldView.ofState q4.2 =
      ComparisonFieldView.ofState r := h4.2.trans
    (h3.2.trans (h2.2.trans (h1.2.trans hr0)))
  have hlapply := cleanSigCleanApply_frame q4.1
  have hrapply := cleanSigCleanApply_frame q4.2
  change ((cleanSigCleanApply q4.1).path = .bot ∨
      (cleanSigCleanApply q4.1).path = l.path) ∧
    ((cleanSigCleanApply q4.2).path = .bot ∨
      (cleanSigCleanApply q4.2).path = r.path) ∧ _
  constructor
  · rcases hlapply.1 with hclear | hkeep
    · exact .inl hclear
    · exact .inr (hkeep.trans (congrArg ComparisonFieldView.path hlpre))
  constructor
  · rcases hrapply.1 with hclear | hkeep
    · exact .inl hclear
    · exact .inr (hkeep.trans (congrArg ComparisonFieldView.path hrpre))
  · exact ⟨hlapply.2.1.trans (congrArg ComparisonFieldView.state hlpre),
      hrapply.2.1.trans (congrArg ComparisonFieldView.state hrpre),
      hlapply.2.2.trans (congrArg ComparisonFieldView.path2 hlpre),
      hrapply.2.2.trans (congrArg ComparisonFieldView.path2 hrpre)⟩

private def pathMarkAfterDeletion (out : AgentState ψ)
    (old : SourceMark n) : SourceMark n :=
  if out.path = .bot then .absent else old

/-- CLEAN_SIG history update: clear a path source exactly when the physical
path is gone; otherwise preserve it.  State and path2 provenance are framed. -/
def markedCleanSig (hψ : ψ > 0) (l r : MarkedAgentState n ψ) :
    MarkedAgentState n ψ × MarkedAgentState n ψ :=
  let q := cleanSig hψ l.concrete r.concrete
  (⟨q.1, { l.history with path := pathMarkAfterDeletion q.1 l.history.path }⟩,
   ⟨q.2, { r.history with path := pathMarkAfterDeletion q.2 r.history.path }⟩)

/-- Marked CLEAN_SIG erases exactly to the physical cleaning transition. -/
theorem erase_markedCleanSig (hψ : ψ > 0)
    (l r : MarkedAgentState n ψ) :
    let q := markedCleanSig hψ l r
    (q.1.concrete, q.2.concrete) = cleanSig hψ l.concrete r.concrete := by
  rfl

private theorem auditTrust_after_deletion
    (old out : AgentState ψ) (history : LocalComparisonHistory n)
    (htrust : AuditLocalHistoryTrusted old history)
    (hpath : out.path = .bot ∨ out.path = old.path)
    (hstate : out.state = old.state) (hpath2 : out.path2 = old.path2) :
    AuditLocalHistoryTrusted out
      { history with path := pathMarkAfterDeletion out history.path } := by
  unfold AuditLocalHistoryTrusted at htrust ⊢
  constructor
  · rw [hstate]
    exact htrust.1
  constructor
  · by_cases hbot : out.path = .bot
    · left
      exact ⟨hbot, by simp [pathMarkAfterDeletion, hbot]⟩
    · have hkeep : out.path = old.path := hpath.resolve_left hbot
      have holdActive : old.path ≠ .bot := by
        intro hold
        exact hbot (hkeep.trans hold)
      rcases htrust.2.1 with holdAbsent | holdTrusted
      · exact (holdActive holdAbsent.1).elim
      · have hmark : pathMarkAfterDeletion out history.path =
            history.path := by simp [pathMarkAfterDeletion, hbot]
        right
        constructor
        · rw [hkeep]
          exact holdTrusted.1
        · rw [hmark]
          exact holdTrusted.2
  · rw [hpath2]
    exact htrust.2.2

/-- CLEAN_SIG preserves fieldwise source trust.  It may intentionally leave a
stale nonneutral state after deleting its path, so the stronger GENSIG phase
predicate is not claimed beyond this stage. -/
theorem markedCleanSig_preserves_auditLocalHistoryTrusted
    (hψ : ψ > 0) (l r : MarkedAgentState n ψ)
    (hl : AuditLocalHistoryTrusted l.concrete l.history)
    (hr : AuditLocalHistoryTrusted r.concrete r.history) :
    let q := markedCleanSig hψ l r
    AuditLocalHistoryTrusted q.1.concrete q.1.history ∧
      AuditLocalHistoryTrusted q.2.concrete q.2.history := by
  have hf := cleanSig_comparison_frame hψ l.concrete r.concrete
  dsimp only at hf ⊢
  exact ⟨auditTrust_after_deletion l.concrete _ l.history hl
      hf.1 hf.2.2.1 hf.2.2.2.2.1,
    auditTrust_after_deletion r.concrete _ r.history hr
      hf.2.1 hf.2.2.2.1 hf.2.2.2.2.2⟩

/-! ## ELIMINATE_SIG cleanup history -/

/-- An active trusted state carries a finite source mark. -/
theorem stateSource_of_active
    (s : AgentState ψ) (h : LocalComparisonHistory n)
    (htrust : AuditLocalHistoryTrusted s h) (hactive : s.state ≠ .none) :
    ∃ source, h.state = .trusted source := by
  rcases htrust.1 with hinactive | htrusted
  · exact (hactive hinactive.1).elim
  · exact htrusted.2

/-- Edge-aware Algorithm 9 history.  The elimination control copies its state
source left; the responder's cleared state/path marks become absent. -/
def markedEliminateSig (hψ : ψ > 0)
    (l r : MarkedAgentState n ψ) :
    MarkedAgentState n ψ × MarkedAgentState n ψ :=
  let q := eliminateSig hψ l.concrete r.concrete
  if helim : r.concrete.state = .eliminate_signal then
    let lHistory := if l.concrete.label ≠ ⟨ψ - 1, by omega⟩ then
      { l.history with state := SourceMark.preserveTrusted r.history.state }
    else l.history
    let rHistory := { r.history with state := .absent, path := .absent }
    (⟨q.1, lHistory⟩, ⟨q.2, rHistory⟩)
  else
    (⟨q.1, l.history⟩, ⟨q.2, r.history⟩)

/-- Marked elimination erases exactly to Algorithm 9. -/
theorem erase_markedEliminateSig (hψ : ψ > 0)
    (l r : MarkedAgentState n ψ) :
    let q := markedEliminateSig hψ l r
    (q.1.concrete, q.2.concrete) = eliminateSig hψ l.concrete r.concrete := by
  unfold markedEliminateSig
  split <;> rfl

private theorem setEliminateState_auditTrusted
    (s : AgentState ψ) (h : LocalComparisonHistory n)
    (htrust : AuditLocalHistoryTrusted s h) (source : Fin n) :
    AuditLocalHistoryTrusted
      { s with state := .eliminate_signal }
      { h with state := .trusted source } := by
  unfold AuditLocalHistoryTrusted
  constructor
  · right
    exact ⟨by intro hbad; contradiction, source, rfl⟩
  · exact htrust.2

private theorem clearStatePath_auditTrusted
    (s : AgentState ψ) (h : LocalComparisonHistory n)
    (htrust : AuditLocalHistoryTrusted s h) :
    AuditLocalHistoryTrusted
      { s with state := .none, path := .bot }
      { h with state := .absent, path := .absent } := by
  unfold AuditLocalHistoryTrusted
  exact ⟨.inl ⟨rfl, rfl⟩, .inl ⟨rfl, rfl⟩, htrust.2.2⟩

/-- Algorithm 9 preserves fieldwise source trust.  Arbitrary elimination
controls remain representable; only an already trusted state source can be
copied, while physical deletion always removes the corresponding marks. -/
theorem markedEliminateSig_preserves_auditLocalHistoryTrusted
    (hψ : ψ > 0) (l r : MarkedAgentState n ψ)
    (hl : AuditLocalHistoryTrusted l.concrete l.history)
    (hr : AuditLocalHistoryTrusted r.concrete r.history) :
    let q := markedEliminateSig hψ l r
    AuditLocalHistoryTrusted q.1.concrete q.1.history ∧
      AuditLocalHistoryTrusted q.2.concrete q.2.history := by
  unfold markedEliminateSig eliminateSig
  dsimp only
  split
  next helim =>
    obtain ⟨source, hsource⟩ := stateSource_of_active
      r.concrete r.history hr (by rw [helim]; decide)
    split
    next _ =>
      have hpreserve : SourceMark.preserveTrusted r.history.state =
          .trusted source := by rw [hsource]; rfl
      rw [hpreserve]
      exact ⟨setEliminateState_auditTrusted l.concrete l.history hl source,
        clearStatePath_auditTrusted r.concrete r.history hr⟩
    next _ =>
      exact ⟨hl, clearStatePath_auditTrusted r.concrete r.history hr⟩
  next _ =>
    exact ⟨hl, hr⟩

/-! ## SIGMOVE path transport history -/

/-- Move `path` provenance with the exact Algorithm-10 stage-1 transfer.  The
initiator's cleared path/state marks become absent; the responder receives the
source attached to the moved physical path. -/
def markedSigMoveStep1 (l r : MarkedAgentState n ψ) :
    MarkedAgentState n ψ × MarkedAgentState n ψ :=
  let q := sigMoveStep1 l.concrete r.concrete
  match l.concrete.path, r.concrete.path with
  | .some pathLabel _, .bot =>
    if _hstate : l.concrete.state ≠ .lock ∧
        l.concrete.state ≠ .compare1 ∧
        l.concrete.state ≠ .CHECK_ready then
      if _hdest : r.concrete.state ≠ .produce ∨ pathLabel ≠ ψ - 1 then
        let lHistory := { l.history with state := .absent, path := .absent }
        let rHistory := { r.history with path := l.history.path }
        (⟨q.1, lHistory⟩, ⟨q.2, rHistory⟩)
      else (⟨q.1, l.history⟩, ⟨q.2, r.history⟩)
    else (⟨q.1, l.history⟩, ⟨q.2, r.history⟩)
  | _, _ => (⟨q.1, l.history⟩, ⟨q.2, r.history⟩)

/-- Marked path movement erases exactly to `sigMoveStep1`. -/
theorem erase_markedSigMoveStep1 (l r : MarkedAgentState n ψ) :
    let q := markedSigMoveStep1 l r
    (q.1.concrete, q.2.concrete) = sigMoveStep1 l.concrete r.concrete := by
  unfold markedSigMoveStep1
  repeat (first | rfl | split)

theorem pathSource_of_present
    (s : AgentState ψ) (h : LocalComparisonHistory n)
    (htrust : AuditLocalHistoryTrusted s h) (hpresent : s.path ≠ .bot) :
    ∃ source, h.path = .trusted source := by
  rcases htrust.2.1 with hinactive | htrusted
  · exact (hpresent hinactive.1).elim
  · exact htrusted.2

/-- Algorithm-10 stage 1 preserves fieldwise history.  The moved path keeps its
source; an arbitrary responder state remains independently marked and is not
laundered by path movement. -/
theorem markedSigMoveStep1_preserves_auditLocalHistoryTrusted
    (l r : MarkedAgentState n ψ)
    (hl : AuditLocalHistoryTrusted l.concrete l.history)
    (hr : AuditLocalHistoryTrusted r.concrete r.history) :
    let q := markedSigMoveStep1 l r
    AuditLocalHistoryTrusted q.1.concrete q.1.history ∧
      AuditLocalHistoryTrusted q.2.concrete q.2.history := by
  unfold markedSigMoveStep1
  dsimp only
  split
  next pathLabel pathBit hlpath hrpath =>
    split
    next hstate =>
      split
      next hdest =>
        have hq : sigMoveStep1 l.concrete r.concrete =
            ({ l.concrete with path := .bot, state := .none },
             { r.concrete with path := l.concrete.path }) := by
          simp [sigMoveStep1, hlpath, hrpath, hstate, hdest]
        rw [hq]
        have hlPresent : l.concrete.path ≠ .bot := by
          rw [hlpath]
          intro hbad
          contradiction
        obtain ⟨source, hsource⟩ :=
          pathSource_of_present l.concrete l.history hl hlPresent
        have hrPathAbsent : r.history.path = .absent := by
          rcases hr.2.1 with hinactive | hactive
          · exact hinactive.2
          · exact (hactive.1 hrpath).elim
        constructor
        · unfold AuditLocalHistoryTrusted
          exact ⟨.inl ⟨rfl, rfl⟩, .inl ⟨rfl, rfl⟩, hl.2.2⟩
        · unfold AuditLocalHistoryTrusted
          constructor
          · exact hr.1
          constructor
          · right
            exact ⟨by rw [hlpath]; intro hbad; contradiction,
              source, hsource⟩
          · exact hr.2.2
      next hdest =>
        have hq : sigMoveStep1 l.concrete r.concrete =
            (l.concrete, r.concrete) := by
          simp [sigMoveStep1, hlpath, hrpath, hstate, hdest]
        rw [hq]
        exact ⟨hl, hr⟩
    next hstate =>
      have hq : sigMoveStep1 l.concrete r.concrete =
          (l.concrete, r.concrete) := by
        simp [sigMoveStep1, hlpath, hrpath, hstate]
      rw [hq]
      exact ⟨hl, hr⟩
  next hother =>
    have hq : sigMoveStep1 l.concrete r.concrete =
        (l.concrete, r.concrete) := by
      unfold sigMoveStep1
      cases hlp : l.concrete.path with
      | bot => rfl
      | some label bit =>
        cases hrp : r.concrete.path with
        | bot => exact (hother label bit hlp hrp).elim
        | some _ _ => rfl
    rw [hq]
    exact ⟨hl, hr⟩

/-! ### SIGMOVE path2 movement -/

theorem path2Source_of_present
    (s : AgentState ψ) (h : LocalComparisonHistory n)
    (htrust : AuditLocalHistoryTrusted s h) (hpresent : s.path2 ≠ none) :
    ∃ source, h.path2 = .trusted source := by
  rcases htrust.2.2 with hinactive | htrusted
  · exact (hpresent hinactive.1).elim
  · exact htrusted.2

/-- Mark Algorithm-10 stage 2, which moves action-1 path2 right and decrements
its remaining position. -/
def markedSigMoveStep2 (l r : MarkedAgentState n ψ) :
    MarkedAgentState n ψ × MarkedAgentState n ψ :=
  let q := sigMoveStep2 l.concrete r.concrete
  match l.concrete.path2 with
  | some p2 =>
    if _hmove : p2.action = 1 ∧ p2.position ≠ 0 then
      (⟨q.1, { l.history with path2 := .absent }⟩,
       ⟨q.2, { r.history with path2 := l.history.path2 }⟩)
    else (⟨q.1, l.history⟩, ⟨q.2, r.history⟩)
  | none => (⟨q.1, l.history⟩, ⟨q.2, r.history⟩)

/-- Stage-2 history erases exactly. -/
theorem erase_markedSigMoveStep2 (l r : MarkedAgentState n ψ) :
    let q := markedSigMoveStep2 l r
    (q.1.concrete, q.2.concrete) = sigMoveStep2 l.concrete r.concrete := by
  unfold markedSigMoveStep2
  repeat (first | rfl | split)

/-- Moving action-1 path2 preserves fieldwise source trust. -/
theorem markedSigMoveStep2_preserves_auditLocalHistoryTrusted
    (l r : MarkedAgentState n ψ)
    (hl : AuditLocalHistoryTrusted l.concrete l.history)
    (hr : AuditLocalHistoryTrusted r.concrete r.history) :
    let q := markedSigMoveStep2 l r
    AuditLocalHistoryTrusted q.1.concrete q.1.history ∧
      AuditLocalHistoryTrusted q.2.concrete q.2.history := by
  unfold markedSigMoveStep2
  dsimp only
  split
  next p2 hp2 =>
    split
    next hmove =>
      have hq : sigMoveStep2 l.concrete r.concrete =
          ({ l.concrete with path2 := none },
           { r.concrete with path2 := some { p2 with position := p2.position - 1 } }) := by
        simp [sigMoveStep2, hp2, hmove]
      rw [hq]
      have hpresent : l.concrete.path2 ≠ none := by
        rw [hp2]
        intro hbad
        contradiction
      obtain ⟨source, hsource⟩ :=
        path2Source_of_present l.concrete l.history hl hpresent
      constructor
      · unfold AuditLocalHistoryTrusted
        exact ⟨hl.1, hl.2.1, .inl ⟨rfl, rfl⟩⟩
      · unfold AuditLocalHistoryTrusted
        exact ⟨hr.1, hr.2.1,
          .inr ⟨by intro hbad; contradiction, source, hsource⟩⟩
    next hmove =>
      have hq : sigMoveStep2 l.concrete r.concrete =
          (l.concrete, r.concrete) := by
        simp [sigMoveStep2, hp2, hmove]
      rw [hq]
      exact ⟨hl, hr⟩
  next hp2 =>
    have hq : sigMoveStep2 l.concrete r.concrete =
        (l.concrete, r.concrete) := by simp [sigMoveStep2, hp2]
    rw [hq]
    exact ⟨hl, hr⟩

/-- Mark Algorithm-10 stage 3, which moves action-2 path2 left and decrements
its remaining position. -/
def markedSigMoveStep3 (l r : MarkedAgentState n ψ) :
    MarkedAgentState n ψ × MarkedAgentState n ψ :=
  let q := sigMoveStep3 l.concrete r.concrete
  match r.concrete.path2 with
  | some p2 =>
    if _hmove : p2.action = 2 ∧ p2.position ≠ 0 then
      (⟨q.1, { l.history with path2 := r.history.path2 }⟩,
       ⟨q.2, { r.history with path2 := .absent }⟩)
    else (⟨q.1, l.history⟩, ⟨q.2, r.history⟩)
  | none => (⟨q.1, l.history⟩, ⟨q.2, r.history⟩)

/-- Stage-3 history erases exactly. -/
theorem erase_markedSigMoveStep3 (l r : MarkedAgentState n ψ) :
    let q := markedSigMoveStep3 l r
    (q.1.concrete, q.2.concrete) = sigMoveStep3 l.concrete r.concrete := by
  unfold markedSigMoveStep3
  repeat (first | rfl | split)

/-- Moving action-2 path2 preserves fieldwise source trust. -/
theorem markedSigMoveStep3_preserves_auditLocalHistoryTrusted
    (l r : MarkedAgentState n ψ)
    (hl : AuditLocalHistoryTrusted l.concrete l.history)
    (hr : AuditLocalHistoryTrusted r.concrete r.history) :
    let q := markedSigMoveStep3 l r
    AuditLocalHistoryTrusted q.1.concrete q.1.history ∧
      AuditLocalHistoryTrusted q.2.concrete q.2.history := by
  unfold markedSigMoveStep3
  dsimp only
  split
  next p2 hp2 =>
    split
    next hmove =>
      have hq : sigMoveStep3 l.concrete r.concrete =
          ({ l.concrete with path2 := some { p2 with position := p2.position - 1 } },
           { r.concrete with path2 := none }) := by
        simp [sigMoveStep3, hp2, hmove]
      rw [hq]
      have hpresent : r.concrete.path2 ≠ none := by
        rw [hp2]
        intro hbad
        contradiction
      obtain ⟨source, hsource⟩ :=
        path2Source_of_present r.concrete r.history hr hpresent
      constructor
      · unfold AuditLocalHistoryTrusted
        exact ⟨hl.1, hl.2.1,
          .inr ⟨by intro hbad; contradiction, source, hsource⟩⟩
      · unfold AuditLocalHistoryTrusted
        exact ⟨hr.1, hr.2.1, .inl ⟨rfl, rfl⟩⟩
    next hmove =>
      have hq : sigMoveStep3 l.concrete r.concrete =
          (l.concrete, r.concrete) := by
        simp [sigMoveStep3, hp2, hmove]
      rw [hq]
      exact ⟨hl, hr⟩
  next hp2 =>
    have hq : sigMoveStep3 l.concrete r.concrete =
        (l.concrete, r.concrete) := by simp [sigMoveStep3, hp2]
    rw [hq]
    exact ⟨hl, hr⟩

/-- Mark Algorithm-10 stage 4, which moves action 3 or 6 path2 left
without changing its payload. -/
def markedSigMoveStep4 (l r : MarkedAgentState n ψ) :
    MarkedAgentState n ψ × MarkedAgentState n ψ :=
  let q := sigMoveStep4 l.concrete r.concrete
  match r.concrete.path2 with
  | some p2 =>
    if _hmove : p2.action = 3 ∨ p2.action = 6 then
      (⟨q.1, { l.history with path2 := r.history.path2 }⟩,
       ⟨q.2, { r.history with path2 := .absent }⟩)
    else (⟨q.1, l.history⟩, ⟨q.2, r.history⟩)
  | none => (⟨q.1, l.history⟩, ⟨q.2, r.history⟩)

/-- Stage-4 history erases exactly. -/
theorem erase_markedSigMoveStep4 (l r : MarkedAgentState n ψ) :
    let q := markedSigMoveStep4 l r
    (q.1.concrete, q.2.concrete) = sigMoveStep4 l.concrete r.concrete := by
  unfold markedSigMoveStep4
  repeat (first | rfl | split)

/-- Moving action-3/6 path2 preserves fieldwise source trust. -/
theorem markedSigMoveStep4_preserves_auditLocalHistoryTrusted
    (l r : MarkedAgentState n ψ)
    (hl : AuditLocalHistoryTrusted l.concrete l.history)
    (hr : AuditLocalHistoryTrusted r.concrete r.history) :
    let q := markedSigMoveStep4 l r
    AuditLocalHistoryTrusted q.1.concrete q.1.history ∧
      AuditLocalHistoryTrusted q.2.concrete q.2.history := by
  unfold markedSigMoveStep4
  dsimp only
  split
  next p2 hp2 =>
    split
    next hmove =>
      have hq : sigMoveStep4 l.concrete r.concrete =
          ({ l.concrete with path2 := r.concrete.path2 },
           { r.concrete with path2 := none }) := by
        simp [sigMoveStep4, hp2, hmove]
      rw [hq]
      have hpresent : r.concrete.path2 ≠ none := by
        rw [hp2]
        intro hbad
        contradiction
      obtain ⟨source, hsource⟩ :=
        path2Source_of_present r.concrete r.history hr hpresent
      constructor
      · unfold AuditLocalHistoryTrusted
        exact ⟨hl.1, hl.2.1,
          .inr ⟨by rw [hp2]; intro hbad; contradiction,
            source, hsource⟩⟩
      · unfold AuditLocalHistoryTrusted
        exact ⟨hr.1, hr.2.1, .inl ⟨rfl, rfl⟩⟩
    next hmove =>
      have hq : sigMoveStep4 l.concrete r.concrete =
          (l.concrete, r.concrete) := by
        simp [sigMoveStep4, hp2, hmove]
      rw [hq]
      exact ⟨hl, hr⟩
  next hp2 =>
    have hq : sigMoveStep4 l.concrete r.concrete =
        (l.concrete, r.concrete) := by simp [sigMoveStep4, hp2]
    rw [hq]
    exact ⟨hl, hr⟩

/-- Mark Algorithm-10 stage 5, which moves action 4 or 5 path2 right. -/
def markedSigMoveStep5 (l r : MarkedAgentState n ψ) :
    MarkedAgentState n ψ × MarkedAgentState n ψ :=
  let q := sigMoveStep5 l.concrete r.concrete
  match l.concrete.path2 with
  | some p2 =>
    if _hmove : p2.action = 4 ∨ p2.action = 5 then
      (⟨q.1, { l.history with path2 := .absent }⟩,
       ⟨q.2, { r.history with path2 := l.history.path2 }⟩)
    else (⟨q.1, l.history⟩, ⟨q.2, r.history⟩)
  | none => (⟨q.1, l.history⟩, ⟨q.2, r.history⟩)

/-- Stage-5 history erases exactly. -/
theorem erase_markedSigMoveStep5 (l r : MarkedAgentState n ψ) :
    let q := markedSigMoveStep5 l r
    (q.1.concrete, q.2.concrete) = sigMoveStep5 l.concrete r.concrete := by
  unfold markedSigMoveStep5
  repeat (first | rfl | split)

/-- Moving action-4/5 path2 preserves fieldwise source trust. -/
theorem markedSigMoveStep5_preserves_auditLocalHistoryTrusted
    (l r : MarkedAgentState n ψ)
    (hl : AuditLocalHistoryTrusted l.concrete l.history)
    (hr : AuditLocalHistoryTrusted r.concrete r.history) :
    let q := markedSigMoveStep5 l r
    AuditLocalHistoryTrusted q.1.concrete q.1.history ∧
      AuditLocalHistoryTrusted q.2.concrete q.2.history := by
  unfold markedSigMoveStep5
  dsimp only
  split
  next p2 hp2 =>
    split
    next hmove =>
      have hq : sigMoveStep5 l.concrete r.concrete =
          ({ l.concrete with path2 := none },
           { r.concrete with path2 := l.concrete.path2 }) := by
        simp [sigMoveStep5, hp2, hmove]
      rw [hq]
      have hpresent : l.concrete.path2 ≠ none := by
        rw [hp2]
        intro hbad
        contradiction
      obtain ⟨source, hsource⟩ :=
        path2Source_of_present l.concrete l.history hl hpresent
      constructor
      · unfold AuditLocalHistoryTrusted
        exact ⟨hl.1, hl.2.1, .inl ⟨rfl, rfl⟩⟩
      · unfold AuditLocalHistoryTrusted
        exact ⟨hr.1, hr.2.1,
          .inr ⟨by rw [hp2]; intro hbad; contradiction,
            source, hsource⟩⟩
    next hmove =>
      have hq : sigMoveStep5 l.concrete r.concrete =
          (l.concrete, r.concrete) := by
        simp [sigMoveStep5, hp2, hmove]
      rw [hq]
      exact ⟨hl, hr⟩
  next hp2 =>
    have hq : sigMoveStep5 l.concrete r.concrete =
        (l.concrete, r.concrete) := by simp [sigMoveStep5, hp2]
    rw [hq]
    exact ⟨hl, hr⟩

/-! ### SIGMOVE control-state derivation -/

/-- Mark the control-state update derived from a local path2 action. -/
def markedSigMoveApplyControl (hψ : ψ > 0)
    (u : MarkedAgentState n ψ) : MarkedAgentState n ψ :=
  let out := sigMoveApplyControl hψ u.concrete
  match u.concrete.path2 with
  | some p2 =>
    if _hcontrol :
        (u.concrete.label = ⟨ψ - 1, by omega⟩ ∧
          (p2.action = 3 ∨ p2.action = 4 ∨ p2.action = 5)) ∨
        (u.concrete.label = ⟨0, hψ⟩ ∧ p2.action = 6) then
      ⟨out, { u.history with
        state := SourceMark.preserveTrusted u.history.path2 }⟩
    else ⟨out, u.history⟩
  | none => ⟨out, u.history⟩

/-- Marked control application erases exactly. -/
theorem erase_markedSigMoveApplyControl (hψ : ψ > 0)
    (u : MarkedAgentState n ψ) :
    (markedSigMoveApplyControl hψ u).concrete =
      sigMoveApplyControl hψ u.concrete := by
  unfold markedSigMoveApplyControl
  repeat (first | rfl | split)

/-- Every control state physically derived from path2 inherits that path2's
trusted source; no current state shape can create provenance. -/
theorem markedSigMoveApplyControl_preserves_auditLocalHistoryTrusted
    (hψ : ψ > 0) (u : MarkedAgentState n ψ)
    (hu : AuditLocalHistoryTrusted u.concrete u.history) :
    AuditLocalHistoryTrusted
      (markedSigMoveApplyControl hψ u).concrete
      (markedSigMoveApplyControl hψ u).history := by
  unfold markedSigMoveApplyControl
  dsimp only
  split
  next p2 hp2 =>
    split
    next hcontrol =>
      have hpresent : u.concrete.path2 ≠ none := by
        rw [hp2]
        intro hbad
        contradiction
      obtain ⟨source, hsource⟩ :=
        path2Source_of_present u.concrete u.history hu hpresent
      have hpreserve : SourceMark.preserveTrusted u.history.path2 =
          .trusted source := by rw [hsource]; rfl
      rw [hpreserve]
      unfold AuditLocalHistoryTrusted
      constructor
      · right
        refine ⟨?_, source, rfl⟩
        rcases hcontrol with hterminal | hzero
        · rcases hterminal with ⟨hlabel, haction⟩
          rcases haction with h3 | h45
          · simp [sigMoveApplyControl, hp2, hlabel, h3]
          · rcases h45 with h4 | h5
            · simp [sigMoveApplyControl, hp2, hlabel, h4]
            · simp [sigMoveApplyControl, hp2, hlabel, h5]
        · rcases hzero with ⟨hlabel, h6⟩
          simp [sigMoveApplyControl, hp2, hlabel, h6]
      · constructor
        · simpa [sigMoveApplyControl, hp2] using hu.2.1
        · simpa [sigMoveApplyControl, hp2] using hu.2.2
    next hcontrol =>
      have hout : sigMoveApplyControl hψ u.concrete = u.concrete := by
        unfold sigMoveApplyControl
        rw [hp2]
        simp only
        by_cases h34 : u.concrete.label = ⟨ψ - 1, by omega⟩ ∧
            (p2.action = 3 ∨ p2.action = 4)
        · have : (u.concrete.label = ⟨ψ - 1, by omega⟩ ∧
              (p2.action = 3 ∨ p2.action = 4 ∨ p2.action = 5)) ∨
              (u.concrete.label = ⟨0, hψ⟩ ∧ p2.action = 6) :=
            .inl ⟨h34.1, h34.2.elim .inl (fun h => .inr (.inl h))⟩
          exact (hcontrol this).elim
        · rw [if_neg h34]
          by_cases h5 : u.concrete.label = ⟨ψ - 1, by omega⟩ ∧
              p2.action = 5
          · exact (hcontrol (.inl ⟨h5.1, .inr (.inr h5.2)⟩)).elim
          · rw [if_neg h5]
            by_cases h6 : u.concrete.label = ⟨0, hψ⟩ ∧ p2.action = 6
            · exact (hcontrol (.inr h6)).elim
            · rw [if_neg h6]
      rw [hout]
      exact hu
  next hp2 =>
    have hout : sigMoveApplyControl hψ u.concrete = u.concrete := by
      simp [sigMoveApplyControl, hp2]
    rw [hout]
    exact hu

/-! ### SIGMOVE final departure and composition -/

/-- The final CHECK-ready/depart handoff may join two state lineages, so a
trusted edge must certify that they name one source. -/
def SigMoveDepartCompatible (_hψ : ψ > 0)
    (l r : MarkedAgentState n ψ) : Prop :=
  (r.concrete.state = .depart ∧ l.concrete.label.val < ψ - 1 ∧
      l.concrete.state = .CHECK_ready) →
    ∃ source, l.history.state = .trusted source ∧
      r.history.state = .trusted source

/-- Final marked departure propagation.  Conflicting histories are retained as
tainted while the physical assignment still executes. -/
def markedSigMoveDepart (_hψ : ψ > 0)
    (l r : MarkedAgentState n ψ) :
    MarkedAgentState n ψ × MarkedAgentState n ψ :=
  let lout := if r.concrete.state = .depart then
    if l.concrete.label.val < ψ - 1 ∧ l.concrete.state = .CHECK_ready then
      { l.concrete with state := .depart }
    else l.concrete
  else l.concrete
  if _hmove : r.concrete.state = .depart ∧
      l.concrete.label.val < ψ - 1 ∧ l.concrete.state = .CHECK_ready then
    let source := SourceMark.agree l.history.state r.history.state
    (⟨lout, { l.history with state := source }⟩, r)
  else (⟨lout, l.history⟩, r)

/-- Final marked departure erases to Algorithm 10 lines 28–30. -/
theorem erase_markedSigMoveDepart (hψ : ψ > 0)
    (l r : MarkedAgentState n ψ) :
    let q := markedSigMoveDepart hψ l r
    (q.1.concrete, q.2.concrete) =
      (let lout := if r.concrete.state = .depart then
        if l.concrete.label.val < ψ - 1 ∧
            l.concrete.state = .CHECK_ready then
          { l.concrete with state := .depart }
        else l.concrete
      else l.concrete
      (lout, r.concrete)) := by
  unfold markedSigMoveDepart
  repeat (first | rfl | split)

theorem setStateSource_auditTrusted
    (s : AgentState ψ) (h : LocalComparisonHistory n)
    (htrust : AuditLocalHistoryTrusted s h) (newState : MainState)
    (hactive : newState ≠ .none) (source : Fin n) :
    AuditLocalHistoryTrusted
      { s with state := newState }
      { h with state := .trusted source } := by
  unfold AuditLocalHistoryTrusted
  exact ⟨.inr ⟨hactive, source, rfl⟩, htrust.2⟩

/-- Final departure preserves fieldwise trust under the explicit same-source
handoff premise. -/
theorem markedSigMoveDepart_preserves_auditLocalHistoryTrusted
    (hψ : ψ > 0) (l r : MarkedAgentState n ψ)
    (hl : AuditLocalHistoryTrusted l.concrete l.history)
    (hr : AuditLocalHistoryTrusted r.concrete r.history)
    (hcompat : SigMoveDepartCompatible hψ l r) :
    let q := markedSigMoveDepart hψ l r
    AuditLocalHistoryTrusted q.1.concrete q.1.history ∧
      AuditLocalHistoryTrusted q.2.concrete q.2.history := by
  unfold markedSigMoveDepart
  dsimp only
  split
  next hmove =>
    obtain ⟨source, hleft, hright⟩ := hcompat hmove
    have hagree : SourceMark.agree l.history.state r.history.state =
        .trusted source := by
      simp [SourceMark.agree, hleft, hright]
    rw [hagree]
    have hleftTrusted := setStateSource_auditTrusted
      l.concrete l.history hl .depart (by decide) source
    simp [hmove.1, hmove.2] at hleftTrusted ⊢
    exact ⟨hleftTrusted, hr⟩
  next hmove =>
    by_cases hrdepart : r.concrete.state = .depart
    · have hguard : ¬(l.concrete.label.val < ψ - 1 ∧
          l.concrete.state = .CHECK_ready) := by
        intro hg
        exact hmove ⟨hrdepart, hg⟩
      simp [hrdepart, hguard]
      exact ⟨hl, hr⟩
    · simp [hrdepart]
      exact ⟨hl, hr⟩

/-- Full marked Algorithm 10. -/
def markedSigMove (hψ : ψ > 0) (l r : MarkedAgentState n ψ) :
    MarkedAgentState n ψ × MarkedAgentState n ψ :=
  let q1 := markedSigMoveStep1 l r
  let q2 := markedSigMoveStep2 q1.1 q1.2
  let q3 := markedSigMoveStep3 q2.1 q2.2
  let q4 := markedSigMoveStep4 q3.1 q3.2
  let q5 := markedSigMoveStep5 q4.1 q4.2
  let l6 := markedSigMoveApplyControl hψ q5.1
  let r6 := markedSigMoveApplyControl hψ q5.2
  markedSigMoveDepart hψ l6 r6

/-- Marked SIGMOVE erases exactly to Algorithm 10. -/
theorem erase_markedSigMove (hψ : ψ > 0)
    (l r : MarkedAgentState n ψ) :
    let q := markedSigMove hψ l r
    (q.1.concrete, q.2.concrete) = sigMove hψ l.concrete r.concrete := by
  let q1 := markedSigMoveStep1 l r
  let p1 := sigMoveStep1 l.concrete r.concrete
  have hq1 := erase_markedSigMoveStep1 l r
  change (q1.1.concrete, q1.2.concrete) = p1 at hq1
  have hq1l := congrArg Prod.fst hq1
  have hq1r := congrArg Prod.snd hq1
  change q1.1.concrete = p1.1 at hq1l
  change q1.2.concrete = p1.2 at hq1r
  let q2 := markedSigMoveStep2 q1.1 q1.2
  let p2 := sigMoveStep2 p1.1 p1.2
  have hq2 := erase_markedSigMoveStep2 q1.1 q1.2
  change (q2.1.concrete, q2.2.concrete) =
    sigMoveStep2 q1.1.concrete q1.2.concrete at hq2
  rw [hq1l, hq1r] at hq2
  change (q2.1.concrete, q2.2.concrete) = p2 at hq2
  have hq2l := congrArg Prod.fst hq2
  have hq2r := congrArg Prod.snd hq2
  change q2.1.concrete = p2.1 at hq2l
  change q2.2.concrete = p2.2 at hq2r
  let q3 := markedSigMoveStep3 q2.1 q2.2
  let p3 := sigMoveStep3 p2.1 p2.2
  have hq3 := erase_markedSigMoveStep3 q2.1 q2.2
  change (q3.1.concrete, q3.2.concrete) =
    sigMoveStep3 q2.1.concrete q2.2.concrete at hq3
  rw [hq2l, hq2r] at hq3
  change (q3.1.concrete, q3.2.concrete) = p3 at hq3
  have hq3l := congrArg Prod.fst hq3
  have hq3r := congrArg Prod.snd hq3
  change q3.1.concrete = p3.1 at hq3l
  change q3.2.concrete = p3.2 at hq3r
  let q4 := markedSigMoveStep4 q3.1 q3.2
  let p4 := sigMoveStep4 p3.1 p3.2
  have hq4 := erase_markedSigMoveStep4 q3.1 q3.2
  change (q4.1.concrete, q4.2.concrete) =
    sigMoveStep4 q3.1.concrete q3.2.concrete at hq4
  rw [hq3l, hq3r] at hq4
  change (q4.1.concrete, q4.2.concrete) = p4 at hq4
  have hq4l := congrArg Prod.fst hq4
  have hq4r := congrArg Prod.snd hq4
  change q4.1.concrete = p4.1 at hq4l
  change q4.2.concrete = p4.2 at hq4r
  let q5 := markedSigMoveStep5 q4.1 q4.2
  let p5 := sigMoveStep5 p4.1 p4.2
  have hq5 := erase_markedSigMoveStep5 q4.1 q4.2
  change (q5.1.concrete, q5.2.concrete) =
    sigMoveStep5 q4.1.concrete q4.2.concrete at hq5
  rw [hq4l, hq4r] at hq5
  change (q5.1.concrete, q5.2.concrete) = p5 at hq5
  have hq5l := congrArg Prod.fst hq5
  have hq5r := congrArg Prod.snd hq5
  change q5.1.concrete = p5.1 at hq5l
  change q5.2.concrete = p5.2 at hq5r
  let l6 := markedSigMoveApplyControl hψ q5.1
  let r6 := markedSigMoveApplyControl hψ q5.2
  let pl6 := sigMoveApplyControl hψ p5.1
  let pr6 := sigMoveApplyControl hψ p5.2
  have hl6 := erase_markedSigMoveApplyControl hψ q5.1
  have hr6 := erase_markedSigMoveApplyControl hψ q5.2
  change l6.concrete = sigMoveApplyControl hψ q5.1.concrete at hl6
  change r6.concrete = sigMoveApplyControl hψ q5.2.concrete at hr6
  rw [hq5l] at hl6
  rw [hq5r] at hr6
  change l6.concrete = pl6 at hl6
  change r6.concrete = pr6 at hr6
  let q7 := markedSigMoveDepart hψ l6 r6
  let p7 :=
    let left := if pr6.state = .depart then
      if pl6.label.val < ψ - 1 ∧ pl6.state = .CHECK_ready then
        { pl6 with state := .depart }
      else pl6
    else pl6
    (left, pr6)
  have hq7 := erase_markedSigMoveDepart hψ l6 r6
  change (q7.1.concrete, q7.2.concrete) =
    (let left := if r6.concrete.state = .depart then
      if l6.concrete.label.val < ψ - 1 ∧
          l6.concrete.state = .CHECK_ready then
        { l6.concrete with state := .depart }
      else l6.concrete
    else l6.concrete
    (left, r6.concrete)) at hq7
  rw [hl6, hr6] at hq7
  change (q7.1.concrete, q7.2.concrete) = p7 at hq7
  change (q7.1.concrete, q7.2.concrete) = _
  exact hq7.trans (by rfl)

/-- Full SIGMOVE preserves fieldwise source trust once the exact intermediate
post-control pair satisfies departure compatibility. -/
theorem markedSigMove_preserves_auditLocalHistoryTrusted
    (hψ : ψ > 0) (l r : MarkedAgentState n ψ)
    (hl : AuditLocalHistoryTrusted l.concrete l.history)
    (hr : AuditLocalHistoryTrusted r.concrete r.history)
    (hcompat :
      let q1 := markedSigMoveStep1 l r
      let q2 := markedSigMoveStep2 q1.1 q1.2
      let q3 := markedSigMoveStep3 q2.1 q2.2
      let q4 := markedSigMoveStep4 q3.1 q3.2
      let q5 := markedSigMoveStep5 q4.1 q4.2
      let l6 := markedSigMoveApplyControl hψ q5.1
      let r6 := markedSigMoveApplyControl hψ q5.2
      SigMoveDepartCompatible hψ l6 r6) :
    let q := markedSigMove hψ l r
    AuditLocalHistoryTrusted q.1.concrete q.1.history ∧
      AuditLocalHistoryTrusted q.2.concrete q.2.history := by
  let q1 := markedSigMoveStep1 l r
  have h1 := markedSigMoveStep1_preserves_auditLocalHistoryTrusted l r hl hr
  change AuditLocalHistoryTrusted q1.1.concrete q1.1.history ∧
    AuditLocalHistoryTrusted q1.2.concrete q1.2.history at h1
  let q2 := markedSigMoveStep2 q1.1 q1.2
  have h2 := markedSigMoveStep2_preserves_auditLocalHistoryTrusted
    q1.1 q1.2 h1.1 h1.2
  change AuditLocalHistoryTrusted q2.1.concrete q2.1.history ∧
    AuditLocalHistoryTrusted q2.2.concrete q2.2.history at h2
  let q3 := markedSigMoveStep3 q2.1 q2.2
  have h3 := markedSigMoveStep3_preserves_auditLocalHistoryTrusted
    q2.1 q2.2 h2.1 h2.2
  change AuditLocalHistoryTrusted q3.1.concrete q3.1.history ∧
    AuditLocalHistoryTrusted q3.2.concrete q3.2.history at h3
  let q4 := markedSigMoveStep4 q3.1 q3.2
  have h4 := markedSigMoveStep4_preserves_auditLocalHistoryTrusted
    q3.1 q3.2 h3.1 h3.2
  change AuditLocalHistoryTrusted q4.1.concrete q4.1.history ∧
    AuditLocalHistoryTrusted q4.2.concrete q4.2.history at h4
  let q5 := markedSigMoveStep5 q4.1 q4.2
  have h5 := markedSigMoveStep5_preserves_auditLocalHistoryTrusted
    q4.1 q4.2 h4.1 h4.2
  change AuditLocalHistoryTrusted q5.1.concrete q5.1.history ∧
    AuditLocalHistoryTrusted q5.2.concrete q5.2.history at h5
  let l6 := markedSigMoveApplyControl hψ q5.1
  let r6 := markedSigMoveApplyControl hψ q5.2
  have hl6 := markedSigMoveApplyControl_preserves_auditLocalHistoryTrusted
    hψ q5.1 h5.1
  have hr6 := markedSigMoveApplyControl_preserves_auditLocalHistoryTrusted
    hψ q5.2 h5.2
  change AuditLocalHistoryTrusted l6.concrete l6.history at hl6
  change AuditLocalHistoryTrusted r6.concrete r6.history at hr6
  change SigMoveDepartCompatible hψ l6 r6 at hcompat
  have h7 := markedSigMoveDepart_preserves_auditLocalHistoryTrusted
    hψ l6 r6 hl6 hr6 hcompat
  simpa [markedSigMove, q1, q2, q3, q4, q5, l6, r6] using h7

/-! ## CHECK comparison history -/

/-- CHECK-ready state is derived from the aligned physical path and therefore
inherits its source, even if the state value was already CHECK-ready. -/
def markedCheckSetReady (u : MarkedAgentState n ψ) : MarkedAgentState n ψ :=
  let out := checkSigSetReady u.concrete
  match u.concrete.path with
  | .some label _ =>
    if _hready : u.concrete.label.val = label ∧
        u.concrete.state ≠ .depart ∧ u.concrete.state ≠ .equal ∧
        u.concrete.state ≠ .larger ∧ u.concrete.state ≠ .less then
      ⟨out, { u.history with
        state := SourceMark.preserveTrusted u.history.path }⟩
    else ⟨out, u.history⟩
  | .bot => ⟨out, u.history⟩

/-- Marked ready-state setup erases exactly. -/
theorem erase_markedCheckSetReady (u : MarkedAgentState n ψ) :
    (markedCheckSetReady u).concrete = checkSigSetReady u.concrete := by
  unfold markedCheckSetReady
  repeat (first | rfl | split)

/-- CHECK-ready setup preserves fieldwise history. -/
theorem markedCheckSetReady_preserves_auditLocalHistoryTrusted
    (u : MarkedAgentState n ψ)
    (hu : AuditLocalHistoryTrusted u.concrete u.history) :
    AuditLocalHistoryTrusted
      (markedCheckSetReady u).concrete (markedCheckSetReady u).history := by
  unfold markedCheckSetReady
  dsimp only
  split
  next label bit hpath =>
    split
    next hready =>
      have hpresent : u.concrete.path ≠ .bot := by
        rw [hpath]
        intro hbad
        contradiction
      obtain ⟨source, hsource⟩ :=
        pathSource_of_present u.concrete u.history hu hpresent
      have hpreserve : SourceMark.preserveTrusted u.history.path =
          .trusted source := by rw [hsource]; rfl
      have hout : checkSigSetReady u.concrete =
          { u.concrete with state := .CHECK_ready } := by
        simp [checkSigSetReady, hpath, hready]
      rw [hout, hpreserve]
      unfold AuditLocalHistoryTrusted
      exact ⟨.inr ⟨by intro hbad; contradiction, source, rfl⟩,
        hu.2.1, hu.2.2⟩
    next hready =>
      have hout : checkSigSetReady u.concrete = u.concrete := by
        simp [checkSigSetReady, hpath, hready]
      rw [hout]
      exact hu
  next hpath =>
    have hout : checkSigSetReady u.concrete = u.concrete := by
      simp [checkSigSetReady, hpath]
    rw [hout]
    exact hu

/-- Mark the offset-zero CHECK_BIT result from its authenticated path. -/
def markedCheckL (hψ : ψ > 0) (u : MarkedAgentState n ψ) :
    MarkedAgentState n ψ :=
  let out := checkSigCheckL hψ u.concrete
  match u.concrete.path with
  | .some 0 _ =>
    if _hcheck : u.concrete.label = ⟨0, hψ⟩ ∧
        u.concrete.state = .CHECK_ready then
      ⟨out, { u.history with
        state := SourceMark.preserveTrusted u.history.path }⟩
    else ⟨out, u.history⟩
  | _ => ⟨out, u.history⟩

/-- Marked first-bit CHECK erases exactly. -/
theorem erase_markedCheckL (hψ : ψ > 0) (u : MarkedAgentState n ψ) :
    (markedCheckL hψ u).concrete = checkSigCheckL hψ u.concrete := by
  unfold markedCheckL
  repeat (first | rfl | split)

/-- The first CHECK result preserves fieldwise source trust. -/
theorem markedCheckL_preserves_auditLocalHistoryTrusted
    (hψ : ψ > 0) (u : MarkedAgentState n ψ)
    (hu : AuditLocalHistoryTrusted u.concrete u.history) :
    AuditLocalHistoryTrusted (markedCheckL hψ u).concrete
      (markedCheckL hψ u).history := by
  unfold markedCheckL
  dsimp only
  split
  next pathBit hpath =>
    split
    next hcheck =>
      have hpresent : u.concrete.path ≠ .bot := by
        rw [hpath]
        intro hbad
        contradiction
      obtain ⟨source, hsource⟩ :=
        pathSource_of_present u.concrete u.history hu hpresent
      have hpreserve : SourceMark.preserveTrusted u.history.path =
          .trusted source := by rw [hsource]; rfl
      have hout : checkSigCheckL hψ u.concrete =
          { u.concrete with state := checkBit u.concrete.bit pathBit } := by
        simp [checkSigCheckL, hpath, hcheck]
      have hstate : checkBit u.concrete.bit pathBit ≠ .none := by
        unfold checkBit
        let bitValue := if u.concrete.bit then 1 else 0
        change (if bitValue = pathBit then MainState.equal
          else if bitValue > pathBit then MainState.larger
          else MainState.less) ≠ MainState.none
        by_cases heq : bitValue = pathBit
        · simp [heq]
        · rw [if_neg heq]
          by_cases hgt : bitValue > pathBit <;> simp [hgt]
      rw [hout, hpreserve]
      exact setStateSource_auditTrusted u.concrete u.history
        hu _ hstate source
    next hcheck =>
      have hout : checkSigCheckL hψ u.concrete = u.concrete := by
        simp [checkSigCheckL, hpath, hcheck]
      rw [hout]
      exact hu
  next hpath =>
    have hout : checkSigCheckL hψ u.concrete = u.concrete := by
      cases hp : u.concrete.path <;> simp_all [checkSigCheckL]
    rw [hout]
    exact hu

/-- Adjacent equal-prefix propagation must use one source across the already
checked left state and the responder path component. -/
def CheckPairCompatible (_hψ : ψ > 0)
    (l r : MarkedAgentState n ψ) : Prop :=
  (l.concrete.label.val < ψ - 1 ∧ l.concrete.state = .equal ∧
      r.concrete.state = .CHECK_ready ∧ r.concrete.path ≠ .bot) →
    ∃ source, l.history.state = .trusted source ∧
      r.history.path = .trusted source

/-- Mark a later CHECK_BIT result, tainting a physically permitted splice when
its equal-prefix and path sources disagree. -/
def markedCheckR (hψ : ψ > 0)
    (l r : MarkedAgentState n ψ) : MarkedAgentState n ψ :=
  let out := checkSigCheckR hψ l.concrete r.concrete
  match r.concrete.path with
  | .some _ _ =>
    if _hcheck : l.concrete.label.val < ψ - 1 ∧
        l.concrete.state = .equal ∧ r.concrete.state = .CHECK_ready then
      let source := SourceMark.agree l.history.state r.history.path
      ⟨out, { r.history with state := source }⟩
    else ⟨out, r.history⟩
  | .bot => ⟨out, r.history⟩

/-- Marked later-bit CHECK erases exactly. -/
theorem erase_markedCheckR (hψ : ψ > 0)
    (l r : MarkedAgentState n ψ) :
    (markedCheckR hψ l r).concrete = checkSigCheckR hψ l.concrete r.concrete := by
  unfold markedCheckR
  repeat (first | rfl | split)

/-- Later CHECK preserves fieldwise trust under the common-source prefix
premise. -/
theorem markedCheckR_preserves_auditLocalHistoryTrusted
    (hψ : ψ > 0) (l r : MarkedAgentState n ψ)
    (_hl : AuditLocalHistoryTrusted l.concrete l.history)
    (hr : AuditLocalHistoryTrusted r.concrete r.history)
    (hcompat : CheckPairCompatible hψ l r) :
    AuditLocalHistoryTrusted (markedCheckR hψ l r).concrete
      (markedCheckR hψ l r).history := by
  unfold markedCheckR
  dsimp only
  split
  next label pathBit hpath =>
    split
    next hcheck =>
      have hpresent : r.concrete.path ≠ .bot := by
        rw [hpath]
        intro hbad
        contradiction
      obtain ⟨source, hleft, hright⟩ := hcompat
        ⟨hcheck.1, hcheck.2.1, hcheck.2.2, hpresent⟩
      have hagree : SourceMark.agree l.history.state r.history.path =
          .trusted source := by simp [SourceMark.agree, hleft, hright]
      have hout : checkSigCheckR hψ l.concrete r.concrete =
          { r.concrete with state := checkBit r.concrete.bit pathBit } := by
        simp [checkSigCheckR, hpath, hcheck]
      have hstate : checkBit r.concrete.bit pathBit ≠ .none := by
        unfold checkBit
        let bitValue := if r.concrete.bit then 1 else 0
        change (if bitValue = pathBit then MainState.equal
          else if bitValue > pathBit then MainState.larger
          else MainState.less) ≠ MainState.none
        by_cases heq : bitValue = pathBit
        · simp [heq]
        · rw [if_neg heq]
          by_cases hgt : bitValue > pathBit <;> simp [hgt]
      rw [hout, hagree]
      exact setStateSource_auditTrusted r.concrete r.history
        hr _ hstate source
    next hcheck =>
      have hout : checkSigCheckR hψ l.concrete r.concrete = r.concrete := by
        unfold checkSigCheckR
        rw [hpath]
        simp only
        by_cases hleft : l.concrete.label.val < ψ - 1 ∧
            l.concrete.state = .equal
        · rw [if_pos hleft]
          by_cases hready : r.concrete.state = .CHECK_ready
          · exact (hcheck ⟨hleft.1, hleft.2, hready⟩).elim
          · simp [hready]
        · simp [hleft]
      rw [hout]
      exact hr
  next hpath =>
    have hout : checkSigCheckR hψ l.concrete r.concrete = r.concrete := by
      simp [checkSigCheckR, hpath]
    rw [hout]
    exact hr

/-- Mark CHECK's action-4/action-6 path2 creation from the authenticated
comparison state. -/
def markedCheckSetResult (u : MarkedAgentState n ψ) :
    MarkedAgentState n ψ :=
  let out := checkSigSetResult u.concrete
  if _hresult : u.concrete.state = .larger ∨ u.concrete.state = .less then
    ⟨out, { u.history with
      path2 := SourceMark.preserveTrusted u.history.state }⟩
  else ⟨out, u.history⟩

/-- Marked CHECK result action erases exactly. -/
theorem erase_markedCheckSetResult (u : MarkedAgentState n ψ) :
    (markedCheckSetResult u).concrete = checkSigSetResult u.concrete := by
  unfold markedCheckSetResult
  split <;> rfl

/-- CHECK result action creation preserves fieldwise source trust. -/
theorem markedCheckSetResult_preserves_auditLocalHistoryTrusted
    (u : MarkedAgentState n ψ)
    (hu : AuditLocalHistoryTrusted u.concrete u.history) :
    AuditLocalHistoryTrusted (markedCheckSetResult u).concrete
      (markedCheckSetResult u).history := by
  unfold markedCheckSetResult
  dsimp only
  split
  next hresult =>
    have hactive : u.concrete.state ≠ .none := by
      intro hnone
      rcases hresult with hlarger | hless <;> rw [hnone] at * <;> contradiction
    obtain ⟨source, hsource⟩ := stateSource_of_active
      u.concrete u.history hu hactive
    have hpreserve : SourceMark.preserveTrusted u.history.state =
        .trusted source := by rw [hsource]; rfl
    rw [hpreserve]
    unfold AuditLocalHistoryTrusted
    constructor
    · simpa [checkSigSetResult] using hu.1
    constructor
    · simpa [checkSigSetResult] using hu.2.1
    · right
      refine ⟨?_, source, rfl⟩
      rcases hresult with hlarger | hless
      · simp [checkSigSetResult, hlarger]
      · simp [checkSigSetResult, hless]
  next hresult =>
    have hnLarger : u.concrete.state ≠ .larger := by
      intro hlarger
      exact hresult (.inl hlarger)
    have hnLess : u.concrete.state ≠ .less := by
      intro hless
      exact hresult (.inr hless)
    have hout : checkSigSetResult u.concrete = u.concrete := by
      simp [checkSigSetResult, hnLarger, hnLess]
    rw [hout]
    exact hu

/-- Full marked Algorithm 11. -/
def markedCheckSig (hψ : ψ > 0)
    (l r : MarkedAgentState n ψ) :
    MarkedAgentState n ψ × MarkedAgentState n ψ :=
  let l0 := markedCheckSetReady l
  let r0 := markedCheckSetReady r
  let l1 := markedCheckL hψ l0
  let r1 := markedCheckR hψ l1 r0
  let l2 := markedCheckSetResult l1
  let r2 := markedCheckSetResult r1
  (l2, ⟨checkSigSetLeader hψ r2.concrete, r2.history⟩)

/-- Marked CHECK erases exactly to Algorithm 11. -/
theorem erase_markedCheckSig (hψ : ψ > 0)
    (l r : MarkedAgentState n ψ) :
    let q := markedCheckSig hψ l r
    (q.1.concrete, q.2.concrete) = checkSig hψ l.concrete r.concrete := by
  let l0 := markedCheckSetReady l
  let r0 := markedCheckSetReady r
  let l1 := markedCheckL hψ l0
  let r1 := markedCheckR hψ l1 r0
  let l2 := markedCheckSetResult l1
  let r2 := markedCheckSetResult r1
  have hl0 := erase_markedCheckSetReady l
  have hr0 := erase_markedCheckSetReady r
  have hl1 := erase_markedCheckL hψ l0
  have hr1 := erase_markedCheckR hψ l1 r0
  have hl2 := erase_markedCheckSetResult l1
  have hr2 := erase_markedCheckSetResult r1
  change l0.concrete = checkSigSetReady l.concrete at hl0
  change r0.concrete = checkSigSetReady r.concrete at hr0
  change l1.concrete = checkSigCheckL hψ l0.concrete at hl1
  change r1.concrete = checkSigCheckR hψ l1.concrete r0.concrete at hr1
  change l2.concrete = checkSigSetResult l1.concrete at hl2
  change r2.concrete = checkSigSetResult r1.concrete at hr2
  have hl2' := hl2
  rw [hl1, hl0] at hl2'
  have hr2' := hr2
  rw [hr1, hl1, hr0, hl0] at hr2'
  change (l2.concrete, checkSigSetLeader hψ r2.concrete) = _
  rw [hl2', hr2']
  exact (checkSig_eq_staged hψ l.concrete r.concrete).symm

/-- Full CHECK preserves fieldwise source history when the exact later-bit
comparison boundary has common-source prefix compatibility. -/
theorem markedCheckSig_preserves_auditLocalHistoryTrusted
    (hψ : ψ > 0) (l r : MarkedAgentState n ψ)
    (hl : AuditLocalHistoryTrusted l.concrete l.history)
    (hr : AuditLocalHistoryTrusted r.concrete r.history)
    (hcompat :
      let l0 := markedCheckSetReady l
      let r0 := markedCheckSetReady r
      let l1 := markedCheckL hψ l0
      CheckPairCompatible hψ l1 r0) :
    let q := markedCheckSig hψ l r
    AuditLocalHistoryTrusted q.1.concrete q.1.history ∧
      AuditLocalHistoryTrusted q.2.concrete q.2.history := by
  let l0 := markedCheckSetReady l
  let r0 := markedCheckSetReady r
  have hl0 := markedCheckSetReady_preserves_auditLocalHistoryTrusted l hl
  have hr0 := markedCheckSetReady_preserves_auditLocalHistoryTrusted r hr
  change AuditLocalHistoryTrusted l0.concrete l0.history at hl0
  change AuditLocalHistoryTrusted r0.concrete r0.history at hr0
  let l1 := markedCheckL hψ l0
  have hl1 := markedCheckL_preserves_auditLocalHistoryTrusted hψ l0 hl0
  change AuditLocalHistoryTrusted l1.concrete l1.history at hl1
  change CheckPairCompatible hψ l1 r0 at hcompat
  let r1 := markedCheckR hψ l1 r0
  have hr1 := markedCheckR_preserves_auditLocalHistoryTrusted
    hψ l1 r0 hl1 hr0 hcompat
  change AuditLocalHistoryTrusted r1.concrete r1.history at hr1
  let l2 := markedCheckSetResult l1
  let r2 := markedCheckSetResult r1
  have hl2 := markedCheckSetResult_preserves_auditLocalHistoryTrusted l1 hl1
  have hr2 := markedCheckSetResult_preserves_auditLocalHistoryTrusted r1 hr1
  change AuditLocalHistoryTrusted l2.concrete l2.history at hl2
  change AuditLocalHistoryTrusted r2.concrete r2.history at hr2
  change AuditLocalHistoryTrusted l2.concrete l2.history ∧
    AuditLocalHistoryTrusted (checkSigSetLeader hψ r2.concrete) r2.history
  constructor
  · exact hl2
  · simpa [checkSigSetLeader, AuditLocalHistoryTrusted] using hr2

/-! ## DISAPPEAR lottery history -/

/-- The moving lottery carry is an independent causal token. -/
def PCarryHistoryTrusted (s : AgentState ψ)
    (h : LocalComparisonHistory n) : Prop :=
  MarkMatches (s.p_carry = false) h.pCarry

/-- Fieldwise comparison trust extended by the DISAPPEAR carry token. -/
def FullLocalHistoryTrusted (s : AgentState ψ)
    (h : LocalComparisonHistory n) : Prop :=
  AuditLocalHistoryTrusted s h ∧ PCarryHistoryTrusted s h

/-- Mark Algorithm 13's responder toss completion.  Action-5 path2 inherits
the trusted toss-state source. -/
def markedDisappearStartR (hψ : ψ > 0)
    (l r : MarkedAgentState n ψ) :
    MarkedAgentState n ψ × MarkedAgentState n ψ :=
  let q := disappearStartR hψ l.concrete r.concrete
  if _hstart : r.concrete.state = .toss ∧
      r.concrete.label = ⟨0, hψ⟩ then
    let source := SourceMark.preserveTrusted r.history.state
    (l, ⟨q.2, { r.history with state := source, path2 := source }⟩)
  else (l, ⟨q.2, r.history⟩)

/-- Marked responder toss completion erases exactly. -/
theorem erase_markedDisappearStartR (hψ : ψ > 0)
    (l r : MarkedAgentState n ψ) :
    let q := markedDisappearStartR hψ l r
    (q.1.concrete, q.2.concrete) = disappearStartR hψ l.concrete r.concrete := by
  unfold markedDisappearStartR
  split <;> rfl

/-- Responder toss completion preserves full local history. -/
theorem markedDisappearStartR_preserves_fullLocalHistoryTrusted
    (hψ : ψ > 0) (l r : MarkedAgentState n ψ)
    (hl : FullLocalHistoryTrusted l.concrete l.history)
    (hr : FullLocalHistoryTrusted r.concrete r.history) :
    let q := markedDisappearStartR hψ l r
    FullLocalHistoryTrusted q.1.concrete q.1.history ∧
      FullLocalHistoryTrusted q.2.concrete q.2.history := by
  unfold markedDisappearStartR disappearStartR
  dsimp only
  split
  next hstart =>
    have hactive : r.concrete.state ≠ .none := by
      rw [hstart.1]
      decide
    obtain ⟨source, hsource⟩ := stateSource_of_active
      r.concrete r.history hr.1 hactive
    have hpreserve : SourceMark.preserveTrusted r.history.state =
        .trusted source := by rw [hsource]; rfl
    rw [hpreserve]
    constructor
    · exact hl
    · constructor
      · unfold AuditLocalHistoryTrusted
        constructor
        · right
          exact ⟨by intro hbad; contradiction, source, rfl⟩
        constructor
        · exact hr.1.2.1
        · right
          exact ⟨by intro hbad; contradiction, source, rfl⟩
      · unfold PCarryHistoryTrusted
        change MarkMatches (r.concrete.p_carry = false) r.history.pCarry
        exact hr.2
  next _ =>
    exact ⟨hl, hr⟩

/-- Mark Algorithm 13's initiator lottery increment.  A newly emitted p_carry
inherits the trusted toss-state source. -/
def markedDisappearStartL (hψ : ψ > 0)
    (l r : MarkedAgentState n ψ) :
    MarkedAgentState n ψ × MarkedAgentState n ψ :=
  let q := disappearStartL hψ l.concrete r.concrete
  if _hstart : l.concrete.state = .toss ∧
      l.concrete.label = ⟨0, hψ⟩ ∧ l.concrete.p = true then
    let source := SourceMark.preserveTrusted l.history.state
    (⟨q.1, { l.history with pCarry := source }⟩, r)
  else (⟨q.1, l.history⟩, r)

/-- Marked initiator lottery increment erases exactly. -/
theorem erase_markedDisappearStartL (hψ : ψ > 0)
    (l r : MarkedAgentState n ψ) :
    let q := markedDisappearStartL hψ l r
    (q.1.concrete, q.2.concrete) = disappearStartL hψ l.concrete r.concrete := by
  unfold markedDisappearStartL
  split <;> rfl

/-- Initiator lottery increment preserves full local history. -/
theorem markedDisappearStartL_preserves_fullLocalHistoryTrusted
    (hψ : ψ > 0) (l r : MarkedAgentState n ψ)
    (hl : FullLocalHistoryTrusted l.concrete l.history)
    (hr : FullLocalHistoryTrusted r.concrete r.history) :
    let q := markedDisappearStartL hψ l r
    FullLocalHistoryTrusted q.1.concrete q.1.history ∧
      FullLocalHistoryTrusted q.2.concrete q.2.history := by
  unfold markedDisappearStartL disappearStartL
  dsimp only
  split
  next hstart =>
    have hactive : l.concrete.state ≠ .none := by
      rw [hstart.1]
      decide
    obtain ⟨source, hsource⟩ := stateSource_of_active
      l.concrete l.history hl.1 hactive
    have hpreserve : SourceMark.preserveTrusted l.history.state =
        .trusted source := by rw [hsource]; rfl
    have hlAudit := hl.1
    unfold AuditLocalHistoryTrusted at hlAudit
    rw [hstart.1] at hlAudit
    simp only [hstart.1, hstart.2.1, hstart.2.2, true_and,
      if_pos, hpreserve]
    constructor
    · constructor
      · exact hlAudit
      · unfold PCarryHistoryTrusted
        right
        exact ⟨by intro hbad; contradiction, source, rfl⟩
    · exact hr
  next hstart =>
    by_cases hroot : l.concrete.state = .toss ∧
        l.concrete.label = ⟨0, hψ⟩
    · have hpfalse : l.concrete.p = false := by
        cases hp : l.concrete.p
        · rfl
        · exact (hstart ⟨hroot.1, hroot.2, hp⟩).elim
      have hl' := hl
      unfold FullLocalHistoryTrusted AuditLocalHistoryTrusted
        PCarryHistoryTrusted at hl'
      rw [hroot.1] at hl'
      simp only [hroot.1, hroot.2, hpfalse, true_and, if_pos]
      simpa [FullLocalHistoryTrusted, AuditLocalHistoryTrusted,
        PCarryHistoryTrusted] using And.intro hl' hr
    · simp only [hroot]
      exact ⟨hl, hr⟩

/-- Existing and incoming lottery carries may merge physically into one Boolean
field; trusted histories must agree at that exact nonterminal merge boundary. -/
def DisappearCarryCompatible (hψ : ψ > 0)
    (l r : MarkedAgentState n ψ) : Prop :=
  (l.concrete.p_carry = true ∧ r.concrete.p = true ∧
      r.concrete.label ≠ ⟨ψ - 1, by omega⟩ ∧
      r.concrete.p_carry = true) →
    ∃ source, l.history.pCarry = .trusted source ∧
      r.history.pCarry = .trusted source

private def outgoingCarrySource (r : MarkedAgentState n ψ)
    (incoming : SourceMark n) : SourceMark n :=
  if r.concrete.p_carry = true then
    SourceMark.agree incoming r.history.pCarry
  else incoming

/-- Mark Algorithm 13's single-use carry stage. -/
def markedDisappearCarry (hψ : ψ > 0)
    (l r : MarkedAgentState n ψ) :
    MarkedAgentState n ψ × MarkedAgentState n ψ :=
  let q := disappearCarry hψ l.concrete r.concrete
  if _hcarry : l.concrete.p_carry = true then
    let incoming := SourceMark.preserveTrusted l.history.pCarry
    let lHistory := { l.history with pCarry := .absent }
    if _hrbit : r.concrete.p = true then
      if _hterminal : r.concrete.label = ⟨ψ - 1, by omega⟩ then
        (⟨q.1, lHistory⟩,
         ⟨q.2, { r.history with state := incoming }⟩)
      else
        (⟨q.1, lHistory⟩,
         ⟨q.2, { r.history with
           pCarry := outgoingCarrySource r incoming }⟩)
    else
      (⟨q.1, lHistory⟩, ⟨q.2, r.history⟩)
  else
    (⟨q.1, l.history⟩, ⟨q.2, r.history⟩)

/-- Marked lottery carry erases exactly. -/
theorem erase_markedDisappearCarry (hψ : ψ > 0)
    (l r : MarkedAgentState n ψ) :
    let q := markedDisappearCarry hψ l r
    (q.1.concrete, q.2.concrete) = disappearCarry hψ l.concrete r.concrete := by
  unfold markedDisappearCarry
  repeat (first | rfl | split)

private theorem pCarrySource_of_true
    (s : AgentState ψ) (h : LocalComparisonHistory n)
    (htrust : PCarryHistoryTrusted s h) (htrue : s.p_carry = true) :
    ∃ source, h.pCarry = .trusted source := by
  unfold PCarryHistoryTrusted at htrust
  rcases htrust with hinactive | htrusted
  · rw [htrue] at hinactive
    exact Bool.noConfusion hinactive.1
  · exact htrusted.2

/-- The lottery carry stage preserves full local history under the explicit
same-source merge premise. -/
theorem markedDisappearCarry_preserves_fullLocalHistoryTrusted
    (hψ : ψ > 0) (l r : MarkedAgentState n ψ)
    (hl : FullLocalHistoryTrusted l.concrete l.history)
    (hr : FullLocalHistoryTrusted r.concrete r.history)
    (hcompat : DisappearCarryCompatible hψ l r) :
    let q := markedDisappearCarry hψ l r
    FullLocalHistoryTrusted q.1.concrete q.1.history ∧
      FullLocalHistoryTrusted q.2.concrete q.2.history := by
  unfold markedDisappearCarry disappearCarry
  dsimp only
  split
  next hcarry =>
    obtain ⟨source, hsource⟩ := pCarrySource_of_true
      l.concrete l.history hl.2 hcarry
    have hincoming : SourceMark.preserveTrusted l.history.pCarry =
        .trusted source := by rw [hsource]; rfl
    rw [hincoming]
    split
    next hrbit =>
      split
      next hterminal =>
        constructor
        · constructor
          · simpa [FullLocalHistoryTrusted, AuditLocalHistoryTrusted]
              using hl.1
          · unfold PCarryHistoryTrusted
            exact .inl ⟨rfl, rfl⟩
        · constructor
          · exact setStateSource_auditTrusted r.concrete r.history
              hr.1 .eliminate_signal (by decide) source
          · have hpcarry :
                (if r.concrete.p_carry = true then true else false) =
                  r.concrete.p_carry := by cases r.concrete.p_carry <;> rfl
            simpa [PCarryHistoryTrusted, hpcarry] using hr.2
      next hterminal =>
        have houtgoing : outgoingCarrySource r (.trusted source) =
            .trusted source := by
          unfold outgoingCarrySource
          by_cases hrold : r.concrete.p_carry = true
          · obtain ⟨sameSource, hleft, hright⟩ := hcompat
              ⟨hcarry, hrbit, hterminal, hrold⟩
            have hsEq : sameSource = source := by
              rw [hsource] at hleft
              exact SourceMark.trusted.inj hleft.symm
            subst sameSource
            simp [hrold, SourceMark.agree, hright]
          · simp [hrold]
        rw [houtgoing]
        constructor
        · constructor
          · simpa [FullLocalHistoryTrusted, AuditLocalHistoryTrusted]
              using hl.1
          · unfold PCarryHistoryTrusted
            exact .inl ⟨rfl, rfl⟩
        · constructor
          · simpa [AuditLocalHistoryTrusted] using hr.1
          · unfold PCarryHistoryTrusted
            right
            exact ⟨by intro hbad; contradiction, source, rfl⟩
    next hrbit =>
      constructor
      · constructor
        · simpa [FullLocalHistoryTrusted, AuditLocalHistoryTrusted]
            using hl.1
        · unfold PCarryHistoryTrusted
          exact .inl ⟨rfl, rfl⟩
      · have hrTracked :
            FullLocalHistoryTrusted
              { r.concrete with p := true } r.history := by
          simpa [FullLocalHistoryTrusted, AuditLocalHistoryTrusted,
            PCarryHistoryTrusted] using hr
        exact hrTracked
  next hcarry =>
    exact ⟨hl, hr⟩

/-- Full marked Algorithm 13. -/
def markedDisappear (hψ : ψ > 0)
    (l r : MarkedAgentState n ψ) :
    MarkedAgentState n ψ × MarkedAgentState n ψ :=
  let q0 := markedDisappearStartR hψ l r
  let q1 := markedDisappearStartL hψ q0.1 q0.2
  markedDisappearCarry hψ q1.1 q1.2

/-- Marked DISAPPEAR erases exactly to Algorithm 13. -/
theorem erase_markedDisappear (hψ : ψ > 0)
    (l r : MarkedAgentState n ψ) :
    let q := markedDisappear hψ l r
    (q.1.concrete, q.2.concrete) = disappear hψ l.concrete r.concrete := by
  let q0 := markedDisappearStartR hψ l r
  let q1 := markedDisappearStartL hψ q0.1 q0.2
  have h0 := erase_markedDisappearStartR hψ l r
  have h1 := erase_markedDisappearStartL hψ q0.1 q0.2
  have h2 := erase_markedDisappearCarry hψ q1.1 q1.2
  change (q0.1.concrete, q0.2.concrete) =
    disappearStartR hψ l.concrete r.concrete at h0
  have h0l := congrArg Prod.fst h0
  have h0r := congrArg Prod.snd h0
  change q0.1.concrete = (disappearStartR hψ l.concrete r.concrete).1 at h0l
  change q0.2.concrete = (disappearStartR hψ l.concrete r.concrete).2 at h0r
  change (q1.1.concrete, q1.2.concrete) =
    disappearStartL hψ q0.1.concrete q0.2.concrete at h1
  rw [h0l, h0r] at h1
  have h1l := congrArg Prod.fst h1
  have h1r := congrArg Prod.snd h1
  change q1.1.concrete =
    (disappearStartL hψ
      (disappearStartR hψ l.concrete r.concrete).1
      (disappearStartR hψ l.concrete r.concrete).2).1 at h1l
  change q1.2.concrete =
    (disappearStartL hψ
      (disappearStartR hψ l.concrete r.concrete).1
      (disappearStartR hψ l.concrete r.concrete).2).2 at h1r
  change ((markedDisappear hψ l r).1.concrete,
    (markedDisappear hψ l r).2.concrete) = _
  change ((markedDisappearCarry hψ q1.1 q1.2).1.concrete,
    (markedDisappearCarry hψ q1.1 q1.2).2.concrete) = _
  rw [h2, h1l, h1r]
  exact (disappear_eq_staged hψ l.concrete r.concrete).symm

/-- Full DISAPPEAR preserves comparison/lottery history under the exact
nonterminal carry-merge compatibility premise. -/
theorem markedDisappear_preserves_fullLocalHistoryTrusted
    (hψ : ψ > 0) (l r : MarkedAgentState n ψ)
    (hl : FullLocalHistoryTrusted l.concrete l.history)
    (hr : FullLocalHistoryTrusted r.concrete r.history)
    (hcompat :
      let q0 := markedDisappearStartR hψ l r
      let q1 := markedDisappearStartL hψ q0.1 q0.2
      DisappearCarryCompatible hψ q1.1 q1.2) :
    let q := markedDisappear hψ l r
    FullLocalHistoryTrusted q.1.concrete q.1.history ∧
      FullLocalHistoryTrusted q.2.concrete q.2.history := by
  let q0 := markedDisappearStartR hψ l r
  have h0 := markedDisappearStartR_preserves_fullLocalHistoryTrusted
    hψ l r hl hr
  change FullLocalHistoryTrusted q0.1.concrete q0.1.history ∧
    FullLocalHistoryTrusted q0.2.concrete q0.2.history at h0
  let q1 := markedDisappearStartL hψ q0.1 q0.2
  have h1 := markedDisappearStartL_preserves_fullLocalHistoryTrusted
    hψ q0.1 q0.2 h0.1 h0.2
  change FullLocalHistoryTrusted q1.1.concrete q1.1.history ∧
    FullLocalHistoryTrusted q1.2.concrete q1.2.history at h1
  change DisappearCarryCompatible hψ q1.1 q1.2 at hcompat
  have h2 := markedDisappearCarry_preserves_fullLocalHistoryTrusted
    hψ q1.1 q1.2 h1.1 h1.2 hcompat
  simpa [markedDisappear, q0, q1] using h2


end PPLLComparisonHistory
