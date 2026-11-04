import Leader.Wu.Comparison.HistoryEntryResetSanitize
import Leader.Wu.Comparison.HistoryTrustImmediateLift
import Leader.Wu.Birth.ShortDoneTerminalEntryCut


set_option autoImplicit false


namespace PPLLComparisonHistory


open PPLL PPLLRepair
open PPLLAuthorizedComparisonRepair
open BirthGenerationControlRepair
open BirthShortDoneTerminalEntryCut


variable {n ψ width κ : Nat}


/-! ## Full-trust helpers for the current GEN writers -/


private theorem setProduce_fullLocalHistoryTrusted
    (s : AgentState ψ) (h : LocalComparisonHistory n)
    (hu : FullLocalHistoryTrusted s h) (source : Fin n) :
    FullLocalHistoryTrusted
      { s with state := .produce }
      { h with state := .trusted source } := by
  constructor
  · unfold AuditLocalHistoryTrusted
    exact ⟨.inr ⟨by simp, source, rfl⟩, hu.1.2⟩
  · exact hu.2


private theorem setDonePathClearPath2_fullLocalHistoryTrusted
    (s : AgentState ψ) (h : LocalComparisonHistory n)
    (hu : FullLocalHistoryTrusted s h)
    (source : Fin n) (label bit : Nat) :
    FullLocalHistoryTrusted
      { s with
        state := .done
        path := .some label bit
        path2 := none }
      { h with
        state := .trusted source
        path := .trusted source
        path2 := .absent } := by
  constructor
  · unfold AuditLocalHistoryTrusted
    exact ⟨
      .inr ⟨by simp, source, rfl⟩,
      .inr ⟨by simp, source, rfl⟩,
      .inl ⟨rfl, rfl⟩⟩
  · exact hu.2


private theorem setDepart_fullLocalHistoryTrusted
    (s : AgentState ψ) (h : LocalComparisonHistory n)
    (hu : FullLocalHistoryTrusted s h) (source : Fin n) :
    FullLocalHistoryTrusted
      { s with state := .depart }
      { h with state := .trusted source } := by
  constructor
  · unfold AuditLocalHistoryTrusted
    exact ⟨.inr ⟨by simp, source, rfl⟩, hu.1.2⟩
  · exact hu.2


private theorem doneToDepartWait_fullLocalHistoryTrusted
    (s : AgentState ψ) (h : LocalComparisonHistory n)
    (hu : FullLocalHistoryTrusted s h)
    (hdone : s.state = .done) (newWait : Bool) :
    FullLocalHistoryTrusted
      { s with state := .depart, wait := newWait } h := by
  have hactive : s.state ≠ .none := by
    rw [hdone]
    decide
  obtain ⟨source, hsource⟩ :=
    stateSource_of_active s h hu.1 hactive
  constructor
  · unfold AuditLocalHistoryTrusted
    exact ⟨.inr ⟨by simp, source, hsource⟩, hu.1.2⟩
  · exact hu.2


/-! ## Start: reuse the existing edge-aware source creation -/


private theorem markedGenSigStart_preserves_fullLocalHistoryTrusted_current
    (hψ : ψ > 0) (source : Fin n)
    (l r : MarkedAgentState n ψ)
    (hl : FullLocalHistoryTrusted l.concrete l.history)
    (hr : FullLocalHistoryTrusted r.concrete r.history) :
    let q := markedGenSigStart hψ source l r
    FullLocalHistoryTrusted q.1.concrete q.1.history ∧
      FullLocalHistoryTrusted q.2.concrete q.2.history := by
  unfold markedGenSigStart genSigSaturatedStart
  dsimp only
  split
  next hroot =>
    have hlnew := setProduce_fullLocalHistoryTrusted
      l.concrete l.history hl source
    split
    next _hrstart =>
      have hpreserve : SourceMark.preserveTrusted
          (.trusted source : SourceMark n) = .trusted source := rfl
      rw [hpreserve]
      exact ⟨hlnew,
        setProduce_fullLocalHistoryTrusted
          r.concrete r.history hr source⟩
    next _ =>
      exact ⟨hlnew, hr⟩
  next _hroot =>
    split
    next hrstart =>
      have hactive : l.concrete.state ≠ .none := by
        rw [hrstart.2.1]
        decide
      obtain ⟨existingSource, hsource⟩ :=
        stateSource_of_active l.concrete l.history hl.1 hactive
      have hpreserve : SourceMark.preserveTrusted l.history.state =
          .trusted existingSource := by
        rw [hsource]
        rfl
      rw [hpreserve]
      exact ⟨hl,
        setProduce_fullLocalHistoryTrusted
          r.concrete r.history hr existingSource⟩
    next _ =>
      exact ⟨hl, hr⟩


/-! ## Current CLEAN-emission writer -/


/-- Current marked terminal emission.  This is the old GENSIG source-copy rule
plus the current physical `path2 := none`; the consumed control mark is therefore
set to `.absent` at the same endpoint. -/
def markedGenCleanEmit (hψ : ψ > 0)
    (l r : MarkedAgentState n ψ) :
    MarkedAgentState n ψ × MarkedAgentState n ψ :=
  let q := genCleanEmit hψ l.concrete r.concrete
  let emitted := r.concrete.label = ⟨ψ - 1, by omega⟩ ∧
    r.concrete.state = .produce
  let source := SourceMark.preserveTrusted r.history.state
  let rHistory := if emitted then
    { r.history with
      state := source
      path := source
      path2 := .absent }
  else r.history
  (⟨q.1, l.history⟩, ⟨q.2, rHistory⟩)


/-- The current marked emission erases exactly to `genCleanEmit`. -/
theorem erase_markedGenCleanEmit (hψ : ψ > 0)
    (l r : MarkedAgentState n ψ) :
    let q := markedGenCleanEmit hψ l r
    (q.1.concrete, q.2.concrete) =
      genCleanEmit hψ l.concrete r.concrete := by
  rfl


/-- Terminal emission derives state/path ancestry from the already trusted
production state and clears the replaced path2 ancestry. -/
theorem markedGenCleanEmit_preserves_fullLocalHistoryTrusted
    (hψ : ψ > 0) (l r : MarkedAgentState n ψ)
    (hl : FullLocalHistoryTrusted l.concrete l.history)
    (hr : FullLocalHistoryTrusted r.concrete r.history) :
    let q := markedGenCleanEmit hψ l r
    FullLocalHistoryTrusted q.1.concrete q.1.history ∧
      FullLocalHistoryTrusted q.2.concrete q.2.history := by
  unfold markedGenCleanEmit genCleanEmit
  dsimp only
  split
  next hemit =>
    have hactive : r.concrete.state ≠ .none := by
      rw [hemit.2]
      decide
    obtain ⟨source, hsource⟩ :=
      stateSource_of_active r.concrete r.history hr.1 hactive
    have hpreserve : SourceMark.preserveTrusted r.history.state =
        .trusted source := by
      rw [hsource]
      rfl
    rw [hpreserve]
    exact ⟨hl,
      setDonePathClearPath2_fullLocalHistoryTrusted
        r.concrete r.history hr source r.concrete.label.val
          (if r.concrete.bit then 1 else 0)⟩
  next _ =>
    exact ⟨hl, hr⟩


/-! ## Current CLEAN-propagation writer -/


/-- Current marked backward generation.  It keeps the existing anti-splice
source join and additionally marks the writer's physically cleared path2 as
absent. -/
def markedGenCleanPropagate (hψ : ψ > 0)
    (l r : MarkedAgentState n ψ) :
    MarkedAgentState n ψ × MarkedAgentState n ψ :=
  let q := genCleanPropagate hψ l.concrete r.concrete
  let propagated := l.concrete.label ≠ ⟨ψ - 1, by omega⟩ ∧
    l.concrete.state = .produce ∧ r.concrete.state = .done
  let source := SourceMark.agree l.history.state
    (SourceMark.agree r.history.state r.history.path)
  let lHistory := if propagated then
    { l.history with
      state := source
      path := source
      path2 := .absent }
  else l.history
  let rHistory := if propagated then
    { r.history with state := source }
  else r.history
  (⟨q.1, lHistory⟩, ⟨q.2, rHistory⟩)


/-- The current marked propagation erases exactly to `genCleanPropagate`. -/
theorem erase_markedGenCleanPropagate (hψ : ψ > 0)
    (l r : MarkedAgentState n ψ) :
    let q := markedGenCleanPropagate hψ l r
    (q.1.concrete, q.2.concrete) =
      genCleanPropagate hψ l.concrete r.concrete := by
  rfl


/-- The sole nonlocal GEN obligation is the existing common-source propagation
premise.  When it holds, the new writer and the responder departure remain
trusted, and the writer's cleared path2 is marked absent. -/
theorem markedGenCleanPropagate_preserves_fullLocalHistoryTrusted
    (hψ : ψ > 0) (l r : MarkedAgentState n ψ)
    (hl : FullLocalHistoryTrusted l.concrete l.history)
    (hr : FullLocalHistoryTrusted r.concrete r.history)
    (hcompat : GenerationPairCompatible hψ l r) :
    let q := markedGenCleanPropagate hψ l r
    FullLocalHistoryTrusted q.1.concrete q.1.history ∧
      FullLocalHistoryTrusted q.2.concrete q.2.history := by
  unfold markedGenCleanPropagate genCleanPropagate
  dsimp only
  split
  next hpropagate =>
    obtain ⟨source, hleftSource, hrightState, hrightPath⟩ :=
      hcompat hpropagate
    have hagree : SourceMark.agree l.history.state
        (SourceMark.agree r.history.state r.history.path) =
        .trusted source := by
      simp [SourceMark.agree, hleftSource, hrightState, hrightPath]
    rw [hagree]
    exact ⟨
      setDonePathClearPath2_fullLocalHistoryTrusted
        l.concrete l.history hl source l.concrete.label.val
          (if l.concrete.bit then 1 else 0),
      setDepart_fullLocalHistoryTrusted
        r.concrete r.history hr source⟩
  next _ =>
    exact ⟨hl, hr⟩


/-! ## Finish and the exact post-WAIT tail -/


private theorem markedGenSigFinish_preserves_fullLocalHistoryTrusted_current
    (hψ : ψ > 0) (l r : MarkedAgentState n ψ)
    (hl : FullLocalHistoryTrusted l.concrete l.history)
    (hr : FullLocalHistoryTrusted r.concrete r.history) :
    let q := markedGenSigFinish hψ l r
    FullLocalHistoryTrusted q.1.concrete q.1.history ∧
      FullLocalHistoryTrusted q.2.concrete q.2.history := by
  unfold markedGenSigFinish genSigSaturatedFinish
  dsimp only
  split
  next hfinish =>
    exact ⟨doneToDepartWait_fullLocalHistoryTrusted
      l.concrete l.history hl hfinish.2 true, hr⟩
  next _ =>
    exact ⟨hl, hr⟩


/-- Exact marked version of the current `genCleanAfterWait` tail. -/
def markedGenCleanAfterWait (hψ : ψ > 0) (sourcePos : Fin n)
    (l r : MarkedAgentState n ψ) :
    MarkedAgentState n ψ × MarkedAgentState n ψ :=
  let q1 := markedGenSigStart hψ sourcePos l r
  let q2 := markedGenCleanEmit hψ q1.1 q1.2
  let q3 := markedGenCleanPropagate hψ q2.1 q2.2
  markedGenSigFinish hψ q3.1 q3.2


/-- Erasure of the current marked post-WAIT GEN tail is exact. -/
theorem erase_markedGenCleanAfterWait
    (hψ : ψ > 0) (sourcePos : Fin n)
    (l r : MarkedAgentState n ψ) :
    let q := markedGenCleanAfterWait hψ sourcePos l r
    (q.1.concrete, q.2.concrete) =
      genCleanAfterWait hψ l.concrete r.concrete := by
  rfl


/-- Full local trust through the current post-WAIT GEN tail.  The compatibility
premise is deliberately evaluated after Start and the current clean emission,
which is the exact input read by `genCleanPropagate`. -/
theorem markedGenCleanAfterWait_preserves_fullLocalHistoryTrusted
    (hψ : ψ > 0) (sourcePos : Fin n)
    (l r : MarkedAgentState n ψ)
    (hl : FullLocalHistoryTrusted l.concrete l.history)
    (hr : FullLocalHistoryTrusted r.concrete r.history)
    (hcompat :
      let q1 := markedGenSigStart hψ sourcePos l r
      let q2 := markedGenCleanEmit hψ q1.1 q1.2
      GenerationPairCompatible hψ q2.1 q2.2) :
    let q := markedGenCleanAfterWait hψ sourcePos l r
    FullLocalHistoryTrusted q.1.concrete q.1.history ∧
      FullLocalHistoryTrusted q.2.concrete q.2.history := by
  let q1 := markedGenSigStart hψ sourcePos l r
  have h1 := markedGenSigStart_preserves_fullLocalHistoryTrusted_current
    hψ sourcePos l r hl hr
  change FullLocalHistoryTrusted q1.1.concrete q1.1.history ∧
    FullLocalHistoryTrusted q1.2.concrete q1.2.history at h1


  let q2 := markedGenCleanEmit hψ q1.1 q1.2
  have h2 := markedGenCleanEmit_preserves_fullLocalHistoryTrusted
    hψ q1.1 q1.2 h1.1 h1.2
  change FullLocalHistoryTrusted q2.1.concrete q2.1.history ∧
    FullLocalHistoryTrusted q2.2.concrete q2.2.history at h2


  change GenerationPairCompatible hψ q2.1 q2.2 at hcompat
  let q3 := markedGenCleanPropagate hψ q2.1 q2.2
  have h3 := markedGenCleanPropagate_preserves_fullLocalHistoryTrusted
    hψ q2.1 q2.2 h2.1 h2.2 hcompat
  change FullLocalHistoryTrusted q3.1.concrete q3.1.history ∧
    FullLocalHistoryTrusted q3.2.concrete q3.2.history at h3


  have h4 := markedGenSigFinish_preserves_fullLocalHistoryTrusted_current
    hψ q3.1 q3.2 h3.1 h3.2
  simpa [markedGenCleanAfterWait, q1, q2, q3] using h4


/-! ## Exact current width-entry authorized lift -/


/-- The one compatibility obligation at the real current GEN/CLEAN entry cut.
It is exactly `GenerationPairCompatible` after the corrected shortened WAIT,
source creation, and the current terminal writer. -/
def CurrentGenCleanEntryWidthCompatible
    (hψ : 0 < ψ) (hwidth : 0 < width) (hle : width ≤ ψ)
    (κ : Nat) (sourcePos : Fin n)
    (l r : MarkedAuthorizedAgentState n ψ) : Prop :=
  let lm : MarkedAgentState n ψ := ⟨l.concrete.core, l.history⟩
  let rm : MarkedAgentState n ψ := ⟨r.concrete.core, r.history⟩
  let w := Q11525CurrentHistoryFrames.markedWaitWidthEntry
    hψ hwidth hle κ lm rm
  let q1 := markedGenSigStart hψ sourcePos w.1 w.2
  let q2 := markedGenCleanEmit hψ q1.1 q1.2
  GenerationPairCompatible hψ q2.1 q2.2


/-- Exact marked lift of the current authorized GEN/CLEAN width-entry stage. -/
def markedAuthorizedGenCleanEntryWidth
    (hψ : 0 < ψ) (hwidth : 0 < width) (hle : width ≤ ψ)
    (κ : Nat) (sourcePos : Fin n)
    (l r : MarkedAuthorizedAgentState n ψ) :
    MarkedAuthorizedAgentState n ψ × MarkedAuthorizedAgentState n ψ :=
  let lm : MarkedAgentState n ψ := ⟨l.concrete.core, l.history⟩
  let rm : MarkedAgentState n ψ := ⟨r.concrete.core, r.history⟩
  let w := Q11525CurrentHistoryFrames.markedWaitWidthEntry
    hψ hwidth hle κ lm rm
  let m := markedGenCleanAfterWait hψ sourcePos w.1 w.2
  let q := BirthShortDoneTerminalEntryCut.authorizedGenCleanEntryWidth
    hψ hwidth hle κ l.concrete r.concrete
  (⟨q.1, m.1.history⟩, ⟨q.2, m.2.history⟩)


/-- The marked authorized lift erases exactly to the current physical
`authorizedGenCleanEntryWidth`. -/
theorem erase_markedAuthorizedGenCleanEntryWidth
    (hψ : 0 < ψ) (hwidth : 0 < width) (hle : width ≤ ψ)
    (κ : Nat) (sourcePos : Fin n)
    (l r : MarkedAuthorizedAgentState n ψ) :
    let q := markedAuthorizedGenCleanEntryWidth
      hψ hwidth hle κ sourcePos l r
    (q.1.concrete, q.2.concrete) =
      BirthShortDoneTerminalEntryCut.authorizedGenCleanEntryWidth
        hψ hwidth hle κ l.concrete r.concrete := by
  rfl


/-- The current authorized GEN/CLEAN entry stage preserves all four local
history fields under exactly the one backward-generation compatibility premise.
The two new physical path2 clears are matched by `.absent` history writes. -/
theorem markedAuthorizedGenCleanEntryWidth_preserves_fullLocalHistoryTrusted
    (hψ : 0 < ψ) (hwidth : 0 < width) (hle : width ≤ ψ)
    (κ : Nat) (sourcePos : Fin n)
    (l r : MarkedAuthorizedAgentState n ψ)
    (hl : FullLocalHistoryTrusted l.concrete.core l.history)
    (hr : FullLocalHistoryTrusted r.concrete.core r.history)
    (hcompat : CurrentGenCleanEntryWidthCompatible
      hψ hwidth hle κ sourcePos l r) :
    let q := markedAuthorizedGenCleanEntryWidth
      hψ hwidth hle κ sourcePos l r
    FullLocalHistoryTrusted q.1.concrete.core q.1.history ∧
      FullLocalHistoryTrusted q.2.concrete.core q.2.history := by
  let lm : MarkedAgentState n ψ := ⟨l.concrete.core, l.history⟩
  let rm : MarkedAgentState n ψ := ⟨r.concrete.core, r.history⟩
  let w := Q11525CurrentHistoryFrames.markedWaitWidthEntry
    hψ hwidth hle κ lm rm
  let m := markedGenCleanAfterWait hψ sourcePos w.1 w.2
  let q := BirthShortDoneTerminalEntryCut.authorizedGenCleanEntryWidth
    hψ hwidth hle κ l.concrete r.concrete


  have hw :=
    Q11525CurrentHistoryFrames.markedWaitWidthEntry_preserves_fullLocalHistoryTrusted
      hψ hwidth hle κ lm rm hl hr
  change FullLocalHistoryTrusted w.1.concrete w.1.history ∧
    FullLocalHistoryTrusted w.2.concrete w.2.history at hw


  have hcompat' :
      let q1 := markedGenSigStart hψ sourcePos w.1 w.2
      let q2 := markedGenCleanEmit hψ q1.1 q1.2
      GenerationPairCompatible hψ q2.1 q2.2 := by
    simpa [CurrentGenCleanEntryWidthCompatible, lm, rm, w] using hcompat


  have hm := markedGenCleanAfterWait_preserves_fullLocalHistoryTrusted
    hψ sourcePos w.1 w.2 hw.1 hw.2 hcompat'
  change FullLocalHistoryTrusted m.1.concrete m.1.history ∧
    FullLocalHistoryTrusted m.2.concrete m.2.history at hm


  have hew := Q11525CurrentHistoryFrames.erase_markedWaitWidthEntry
    hψ hwidth hle κ lm rm
  change (w.1.concrete, w.2.concrete) =
    BirthShortWaitTerminalEntryRepair.waitWidthEntry
      hψ hwidth hle κ l.concrete.core r.concrete.core at hew
  have hewL : w.1.concrete =
      (BirthShortWaitTerminalEntryRepair.waitWidthEntry
        hψ hwidth hle κ l.concrete.core r.concrete.core).1 :=
    congrArg Prod.fst hew
  have hewR : w.2.concrete =
      (BirthShortWaitTerminalEntryRepair.waitWidthEntry
        hψ hwidth hle κ l.concrete.core r.concrete.core).2 :=
    congrArg Prod.snd hew


  have hem := erase_markedGenCleanAfterWait hψ sourcePos w.1 w.2
  change (m.1.concrete, m.2.concrete) =
    genCleanAfterWait hψ w.1.concrete w.2.concrete at hem
  rw [hewL, hewR] at hem
  have hraw :
      (m.1.concrete, m.2.concrete) =
        BirthShortDoneTerminalEntryCut.genCleanEntryWidth
          hψ hwidth hle κ l.concrete.core r.concrete.core := by
    simpa [BirthShortDoneTerminalEntryCut.genCleanEntryWidth] using hem


  have hcore : (q.1.core, q.2.core) =
      (m.1.concrete, m.2.concrete) := by
    calc
      (q.1.core, q.2.core) =
          BirthShortDoneTerminalEntryCut.genCleanEntryWidth
            hψ hwidth hle κ l.concrete.core r.concrete.core := by
        rfl
      _ = (m.1.concrete, m.2.concrete) := hraw.symm
  have hL : q.1.core = m.1.concrete := congrArg Prod.fst hcore
  have hR : q.2.core = m.2.concrete := congrArg Prod.snd hcore


  change FullLocalHistoryTrusted q.1.core m.1.history ∧
    FullLocalHistoryTrusted q.2.core m.2.history
  constructor
  · rw [hL]
    exact hm.1
  · rw [hR]
    exact hm.2


end PPLLComparisonHistory


#print axioms PPLLComparisonHistory.erase_markedGenCleanEmit
#print axioms PPLLComparisonHistory.markedGenCleanEmit_preserves_fullLocalHistoryTrusted
#print axioms PPLLComparisonHistory.erase_markedGenCleanPropagate
#print axioms PPLLComparisonHistory.markedGenCleanPropagate_preserves_fullLocalHistoryTrusted
#print axioms PPLLComparisonHistory.erase_markedGenCleanAfterWait
#print axioms PPLLComparisonHistory.markedGenCleanAfterWait_preserves_fullLocalHistoryTrusted
#print axioms PPLLComparisonHistory.erase_markedAuthorizedGenCleanEntryWidth
#print axioms PPLLComparisonHistory.markedAuthorizedGenCleanEntryWidth_preserves_fullLocalHistoryTrusted
