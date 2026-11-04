import Leader.Wu.Comparison.Lifecycle

/-!
# Edge-aware finite comparison history

A pointwise local ghost cannot recover ring positions, but a proof refinement of
an entire fixed-size configuration sees the scheduled edge.  It can therefore
record where a GENSIG wave was born while leaving the finite physical protocol
unchanged.  This module supplies that configuration-level erasure layer and a
finite source-mark vocabulary.

The history updater remains a parameter here.  Consequently the generic
simulation theorems are infrastructure, not a provenance or safety result.  The
next layer must instantiate the updater stage by stage and prove that trusted
source marks imply the static route objects in `SignalCoherence.lean`.
-/

namespace PPLLComparisonHistory

open PPLL PPLLRepair PPLLComparisonLifecycle PPLLDomain
  PPLLResearchFormulation

/-! ## Finite source marks -/

/-- Provenance status for one independently moving comparison field.  A trusted
mark records the physical ring position at which its generation lineage began;
`tainted` represents arbitrary or conflicting history without excluding the
physical state. -/
inductive SourceMark (n : Nat) where
  | absent
  | trusted (source : Fin n)
  | tainted
  deriving DecidableEq, Repr

namespace SourceMark

/-- Constructive certificate that source marks are finite for fixed `n`.  The
nested option encodes `tainted`, `absent`, and a trusted finite source. -/
def certificate (n : Nat) : ExhaustiveList (SourceMark n) :=
  ExhaustiveList.mapSurjective
    (ExhaustiveList.option (ExhaustiveList.option (ExhaustiveList.fin n)))
    (fun x => match x with
      | none => .tainted
      | some none => .absent
      | some (some source) => .trusted source)
    (by
      intro m
      cases m with
      | absent => exact ⟨some none, rfl⟩
      | trusted source => exact ⟨some (some source), rfl⟩
      | tainted => exact ⟨none, rfl⟩)

end SourceMark

/-- Independent source marks for `MainState`, `path`, `path2`, and the
DISAPPEAR lottery carry. These fields can be created, moved, or cleared at
different stages, so combining them into one provenance bit loses information. -/
structure LocalComparisonHistory (n : Nat) where
  state : SourceMark n
  path : SourceMark n
  path2 : SourceMark n
  pCarry : SourceMark n
  deriving DecidableEq, Repr

namespace LocalComparisonHistory

/-- Constructive finite certificate for the four local source marks. -/
def certificate (n : Nat) : ExhaustiveList (LocalComparisonHistory n) :=
  ExhaustiveList.mapSurjective
    (ExhaustiveList.prod (SourceMark.certificate n)
      (ExhaustiveList.prod (SourceMark.certificate n)
        (ExhaustiveList.prod (SourceMark.certificate n)
          (SourceMark.certificate n))))
    (fun x =>
      ({ state := x.1, path := x.2.1, path2 := x.2.2.1,
         pCarry := x.2.2.2 } : LocalComparisonHistory n))
    (by
      intro h
      exact ⟨(h.state, (h.path, (h.path2, h.pCarry))),
        by cases h; rfl⟩)

end LocalComparisonHistory

/-! ## Configuration-level erasing refinement -/

/-- A finite physical configuration plus edge-aware proof history.  History is
configuration semantics, not executable local agent memory. -/
structure HistoricalConfig (n ψ κ : Nat) where
  concrete : Fin n → BoundedAgentState ψ κ
  history : Fin n → LocalComparisonHistory n

/-- Forget all comparison history. -/
def eraseConfig (R : HistoricalConfig n ψ κ) :
    Fin n → BoundedAgentState ψ κ := R.concrete

private def freshStateMark (s : BoundedAgentState ψ κ) : SourceMark n :=
  if s.erase.state = .none then .absent else .tainted

private def freshPathMark (s : BoundedAgentState ψ κ) : SourceMark n :=
  if s.erase.path = .bot then .absent else .tainted

private def freshPath2Mark (s : BoundedAgentState ψ κ) : SourceMark n :=
  if s.erase.path2 = none then .absent else .tainted

private def freshPCarryMark (s : BoundedAgentState ψ κ) : SourceMark n :=
  if s.erase.p_carry = false then .absent else .tainted

/-- Canonical total lift: absent comparison fields receive `absent`; every
active arbitrary field is represented but starts tainted. -/
def liftConfig (C : Fin n → BoundedAgentState ψ κ) :
    HistoricalConfig n ψ κ where
  concrete := C
  history := fun i =>
    { state := freshStateMark (C i)
      path := freshPathMark (C i)
      path2 := freshPath2Mark (C i)
      pCarry := freshPCarryMark (C i) }

@[simp] theorem erase_liftConfig
    (C : Fin n → BoundedAgentState ψ κ) :
    eraseConfig (liftConfig C) = C := by
  rfl

/-- A history updater sees the ring, scheduled edge, old refined configuration,
and exact physical successor, but returns proof history only. -/
abbrev HistoryUpdate (n ψ κ : Nat) :=
  DirectedRing n → HistoricalConfig n ψ κ → Fin n →
    (Fin n → BoundedAgentState ψ κ) →
      (Fin n → LocalComparisonHistory n)

/-- One edge-aware refined interaction.  The physical successor is fixed before
history is updated. -/
def step (hψ : ψ > 0) (κ : Nat) (update : HistoryUpdate n ψ κ)
    (ring : DirectedRing n) (R : HistoricalConfig n ψ κ) (e : Fin n) :
    HistoricalConfig n ψ κ :=
  let concrete' := localStep ring (integratedBoundedTransition hψ κ)
    R.concrete e
  { concrete := concrete'
    history := update ring R e concrete' }

/-- Configuration history cannot alter one physical interaction. -/
theorem erase_step (hψ : ψ > 0) (κ : Nat)
    (update : HistoryUpdate n ψ κ) (ring : DirectedRing n)
    (R : HistoricalConfig n ψ κ) (e : Fin n) :
    eraseConfig (step hψ κ update ring R e) =
      localStep ring (integratedBoundedTransition hψ κ)
        (eraseConfig R) e := by
  rfl

/-- Execute a deterministic edge schedule in the history refinement. -/
def runSchedule (hψ : ψ > 0) (κ : Nat)
    (update : HistoryUpdate n ψ κ) (ring : DirectedRing n)
    (R : HistoricalConfig n ψ κ) : DetSchedule n → HistoricalConfig n ψ κ
  | [] => R
  | e :: rest => runSchedule hψ κ update ring
      (step hψ κ update ring R e) rest

/-- Exact physical erasure extends to every finite schedule. -/
theorem erase_runSchedule (hψ : ψ > 0) (κ : Nat)
    (update : HistoryUpdate n ψ κ) (ring : DirectedRing n)
    (R : HistoricalConfig n ψ κ) (s : DetSchedule n) :
    eraseConfig (runSchedule hψ κ update ring R s) =
      runLocalSchedule ring (integratedBoundedTransition hψ κ)
        (eraseConfig R) s := by
  induction s generalizing R with
  | nil => rfl
  | cons e rest ih =>
    simp only [runSchedule, runLocalSchedule]
    rw [ih, erase_step]

/-! ## Canonical trust boundary -/

/-- A physical absence must carry `absent`; an active field is trusted only
when a concrete finite source is recorded.  Tainted marks never satisfy this
relation. -/
def MarkMatches (inactive : Prop) (mark : SourceMark n) : Prop :=
  (inactive ∧ mark = .absent) ∨
    (¬inactive ∧ ∃ source, mark = .trusted source)

private theorem markMatches_fresh_iff {n : Nat} (p : Prop) [Decidable p] :
    MarkMatches (n := n) p (if p then .absent else .tainted) ↔ p := by
  by_cases hp : p <;> simp [MarkMatches, hp]

/-- Current field/source consistency.  This is still only a local obligation;
it does not assert that components of one complete carrier share a source or
that a route survived every intervening larger group. -/
def LocalHistoryTrusted (s : BoundedAgentState ψ κ)
    (h : LocalComparisonHistory n) : Prop :=
  MarkMatches (s.erase.state = .none) h.state ∧
  MarkMatches (s.erase.path = .bot) h.path ∧
  MarkMatches (s.erase.path2 = none) h.path2

/-- The canonical lift satisfies local trust exactly when all three comparison
fields are idle.  Active arbitrary fields remain represented with tainted
history and are therefore outside the trusted subset. -/
theorem lift_localHistoryTrusted_iff_idle
    (C : Fin n → BoundedAgentState ψ κ) (i : Fin n) :
    LocalHistoryTrusted (C i) ((liftConfig C).history i) ↔
      (C i).erase.state = .none ∧ (C i).erase.path = .bot ∧
        (C i).erase.path2 = none := by
  simp [LocalHistoryTrusted, liftConfig, freshStateMark,
    freshPathMark, freshPath2Mark, markMatches_fresh_iff]

/-! ## Finite bounded GENSIG stage -/

/-- Algorithm 4's repaired finite physical stage, reified through the already
proved numeric-domain theorem. -/
def boundedGenSig (hψ : ψ > 0) (κ : Nat)
    (l r : BoundedAgentState ψ κ) :
    BoundedAgentState ψ κ × BoundedAgentState ψ κ :=
  let q := genSigSaturated hψ κ l.erase r.erase
  let hq := genSigSaturated_inProtocolDomain hψ l.erase r.erase
    l.erase_inProtocolDomain r.erase_inProtocolDomain
  (BoundedAgentState.ofDomain q.1 hq.1,
    BoundedAgentState.ofDomain q.2 hq.2)

/-- The bounded GENSIG stage erases exactly to `genSigSaturated`. -/
theorem erase_boundedGenSig (hψ : ψ > 0) (κ : Nat)
    (l r : BoundedAgentState ψ κ) :
    BoundedAgentState.erase (boundedGenSig hψ κ l r).1 =
        (genSigSaturated hψ κ l.erase r.erase).1 ∧
      BoundedAgentState.erase (boundedGenSig hψ κ l r).2 =
        (genSigSaturated hψ κ l.erase r.erase).2 := by
  simp [boundedGenSig, BoundedAgentState.erase_ofDomain]

/-! ## Edge-aware GENSIG birth history -/

/-- Audit state paired with comparison and lottery-carry source marks. -/
structure MarkedAgentState (n ψ : Nat) where
  concrete : AgentState ψ
  history : LocalComparisonHistory n
  deriving DecidableEq, Repr

/-- Audit-state counterpart of `LocalHistoryTrusted`. -/
def AuditLocalHistoryTrusted (s : AgentState ψ)
    (h : LocalComparisonHistory n) : Prop :=
  MarkMatches (s.state = .none) h.state ∧
  MarkMatches (s.path = .bot) h.path ∧
  MarkMatches (s.path2 = none) h.path2

/-- Two active fields name one authenticated source. -/
def SameTrustedSource (a b : SourceMark n) : Prop :=
  ∃ source, a = .trusted source ∧ b = .trusted source

/-- Extra Algorithm-4 phase coherence.  A production wave has no path yet;
`done` and `depart` phases already carry a path whose source agrees with the
state-wave source.  This excludes the malformed `done`/no-path splice that a
pure fieldwise predicate would accept. -/
def GenerationPhaseCoherent (s : AgentState ψ)
    (h : LocalComparisonHistory n) : Prop :=
  (s.state = .produce → s.path = .bot) ∧
  ((s.state = .done ∨ s.state = .depart) →
    s.path ≠ .bot ∧ SameTrustedSource h.state h.path)

/-- Local trusted surface for the staged GENSIG proof. -/
def GenerationLocalTrusted (s : MarkedAgentState n ψ) : Prop :=
  AuditLocalHistoryTrusted s.concrete s.history ∧
    GenerationPhaseCoherent s.concrete s.history

/-- Preserve a source only when it is already authenticated; absent or tainted
input cannot be upgraded by copying. -/
def SourceMark.preserveTrusted (mark : SourceMark n) : SourceMark n :=
  match mark with
  | .trusted source => .trusted source
  | .absent => .tainted
  | .tainted => .tainted

/-- Combine two causal lineages only when both are trusted and name the same
source.  A malformed splice remains physically executable but becomes tainted. -/
def SourceMark.agree (a b : SourceMark n) : SourceMark n :=
  match a, b with
  | .trusted source, .trusted source' =>
      if source = source' then .trusted source else .tainted
  | _, _ => .tainted

/-- WAIT changes no comparison field, so its source marks are unchanged. -/
def markedWait (hψ : ψ > 0) (κ : Nat)
    (l r : MarkedAgentState n ψ) :
    MarkedAgentState n ψ × MarkedAgentState n ψ :=
  let q := waitSaturated hψ κ l.concrete r.concrete
  (⟨q.1, l.history⟩, ⟨q.2, r.history⟩)

private theorem generationLocalTrusted_of_fields
    (s : MarkedAgentState n ψ) (t : AgentState ψ)
    (h : GenerationLocalTrusted s)
    (hstate : t.state = s.concrete.state)
    (hpath : t.path = s.concrete.path)
    (hpath2 : t.path2 = s.concrete.path2) :
    GenerationLocalTrusted ⟨t, s.history⟩ := by
  unfold GenerationLocalTrusted AuditLocalHistoryTrusted
    GenerationPhaseCoherent at h ⊢
  rw [hstate, hpath, hpath2]
  exact h

private theorem waitSaturated_comparison_frame (hψ : ψ > 0) (κ : Nat)
    (l r : AgentState ψ) :
    let q := waitSaturated hψ κ l r
    q.1.state = l.state ∧ q.1.path = l.path ∧ q.1.path2 = l.path2 ∧
      q.2.state = r.state ∧ q.2.path = r.path ∧ q.2.path2 = r.path2 := by
  simp [waitSaturated, waitSaturatedPrepare, waitSaturatedCarry,
    waitSaturatedReset, waitSaturatedFinish]

/-- Saturating WAIT preserves the complete local generation-history relation
because it changes none of the three comparison fields. -/
theorem markedWait_preserves_generationLocalTrusted
    (hψ : ψ > 0) (κ : Nat) (l r : MarkedAgentState n ψ)
    (hl : GenerationLocalTrusted l) (hr : GenerationLocalTrusted r) :
    let q := markedWait hψ κ l r
    GenerationLocalTrusted q.1 ∧ GenerationLocalTrusted q.2 := by
  have hf := waitSaturated_comparison_frame hψ κ l.concrete r.concrete
  dsimp only at hf ⊢
  rcases hf with ⟨hls, hlp, hlp2, hrs, hrp, hrp2⟩
  exact ⟨generationLocalTrusted_of_fields l _ hl hls hlp hlp2,
    generationLocalTrusted_of_fields r _ hr hrs hrp hrp2⟩

/-- Mark Algorithm 4's production-wave start.  A new label-zero initiator
receives its actual ring position as source; a newly reached responder copies
the already marked production source. -/
def markedGenSigStart (hψ : ψ > 0) (sourcePos : Fin n)
    (l r : MarkedAgentState n ψ) :
    MarkedAgentState n ψ × MarkedAgentState n ψ :=
  let q := genSigSaturatedStart hψ l.concrete r.concrete
  let lStarts := l.concrete.leader = false ∧
    l.concrete.label = ⟨0, hψ⟩ ∧ l.concrete.wait = false ∧
    l.concrete.path = .bot
  let lState := if lStarts then .trusted sourcePos else l.history.state
  let rStarts := r.concrete.label ≠ ⟨0, hψ⟩ ∧
    q.1.state = .produce ∧ r.concrete.path = .bot
  let rState := if rStarts then SourceMark.preserveTrusted lState else r.history.state
  (⟨q.1, { l.history with state := lState }⟩,
   ⟨q.2, { r.history with state := rState }⟩)

private theorem pathMark_absent_of_bot (s : MarkedAgentState n ψ)
    (h : GenerationLocalTrusted s) (hp : s.concrete.path = .bot) :
    s.history.path = .absent := by
  rcases h.1.2.1 with hmark | hmark
  · exact hmark.2
  · exact (hmark.1 hp).elim

private theorem stateSource_of_produce (s : MarkedAgentState n ψ)
    (h : GenerationLocalTrusted s) (hs : s.concrete.state = .produce) :
    ∃ source, s.history.state = .trusted source := by
  rcases h.1.1 with hmark | hmark
  · have hactive : s.concrete.state ≠ .none := by rw [hs]; decide
    exact (hactive hmark.1).elim
  · exact hmark.2

private theorem setProduce_trusted (s : MarkedAgentState n ψ)
    (h : GenerationLocalTrusted s) (hp : s.concrete.path = .bot)
    (source : Fin n) :
    GenerationLocalTrusted
      ⟨{ s.concrete with state := .produce },
       { s.history with state := .trusted source }⟩ := by
  have hpathAbsent := pathMark_absent_of_bot s h hp
  rcases h with ⟨hfields, _⟩
  constructor
  · unfold AuditLocalHistoryTrusted
    constructor
    · right
      constructor
      · intro hnone
        contradiction
      · exact ⟨source, rfl⟩
    constructor
    · exact .inl ⟨hp, hpathAbsent⟩
    · exact hfields.2.2
  · unfold GenerationPhaseCoherent
    constructor
    · intro _
      exact hp
    · intro hbad
      rcases hbad with hbad | hbad <;> contradiction

/-- The production-start stage preserves local generation history.  Actual
label-zero roots create a new trusted source position; responder production
copies an existing trusted wave and never upgrades tainted state by shape. -/
theorem markedGenSigStart_preserves_generationLocalTrusted
    (hψ : ψ > 0) (source : Fin n) (l r : MarkedAgentState n ψ)
    (hl : GenerationLocalTrusted l) (hr : GenerationLocalTrusted r) :
    let q := markedGenSigStart hψ source l r
    GenerationLocalTrusted q.1 ∧ GenerationLocalTrusted q.2 := by
  unfold markedGenSigStart genSigSaturatedStart
  dsimp only
  split
  next hroot =>
    have hlnew := setProduce_trusted l hl hroot.2.2.2 source
    split
    next hrstart =>
      have hpreserve : SourceMark.preserveTrusted
          (.trusted source : SourceMark n) = .trusted source := rfl
      have hrnew := setProduce_trusted r hr hrstart.2.2 source
      simpa only [hpreserve] using And.intro hlnew hrnew
    next _ =>
      exact ⟨hlnew, hr⟩
  next _ =>
    split
    next hrstart =>
      obtain ⟨existingSource, hsource⟩ :=
        stateSource_of_produce l hl hrstart.2.1
      have hpreserve : SourceMark.preserveTrusted l.history.state =
          .trusted existingSource := by rw [hsource]; rfl
      have hrnew := setProduce_trusted r hr hrstart.2.2 existingSource
      rw [hpreserve]
      exact ⟨hl, hrnew⟩
    next _ =>
      exact ⟨hl, hr⟩

/-- Terminal emission authenticates both the terminal `done` state and its new
path from the marked production wave. -/
def markedGenSigEmit (hψ : ψ > 0)
    (l r : MarkedAgentState n ψ) :
    MarkedAgentState n ψ × MarkedAgentState n ψ :=
  let q := genSigSaturatedEmit hψ l.concrete r.concrete
  let emitted := r.concrete.label = ⟨ψ - 1, by omega⟩ ∧
    r.concrete.state = .produce
  let source := SourceMark.preserveTrusted r.history.state
  let rHistory := if emitted then
    { r.history with state := source, path := source }
  else r.history
  (⟨q.1, l.history⟩, ⟨q.2, rHistory⟩)

private theorem setDonePath_trusted (s : MarkedAgentState n ψ)
    (h : GenerationLocalTrusted s) (source : Fin n) (label bit : Nat) :
    GenerationLocalTrusted
      ⟨{ s.concrete with state := .done, path := .some label bit },
       { s.history with state := .trusted source, path := .trusted source }⟩ := by
  rcases h with ⟨hfields, _⟩
  constructor
  · unfold AuditLocalHistoryTrusted
    constructor
    · right
      exact ⟨by intro hbad; contradiction, source, rfl⟩
    constructor
    · right
      exact ⟨by intro hbad; contradiction, source, rfl⟩
    · exact hfields.2.2
  · unfold GenerationPhaseCoherent
    constructor
    · intro hbad
      contradiction
    · intro _
      constructor
      · intro hbad
        contradiction
      · exact ⟨source, rfl, rfl⟩

/-- A terminal emission preserves local generation history and copies the
trusted production source to both the `done` state and new path. -/
theorem markedGenSigEmit_preserves_generationLocalTrusted
    (hψ : ψ > 0) (l r : MarkedAgentState n ψ)
    (hl : GenerationLocalTrusted l) (hr : GenerationLocalTrusted r) :
    let q := markedGenSigEmit hψ l r
    GenerationLocalTrusted q.1 ∧ GenerationLocalTrusted q.2 := by
  unfold markedGenSigEmit genSigSaturatedEmit
  dsimp only
  split
  next hemit =>
    obtain ⟨source, hsource⟩ := stateSource_of_produce r hr hemit.2
    have hpreserve : SourceMark.preserveTrusted r.history.state =
        .trusted source := by rw [hsource]; rfl
    rw [hpreserve]
    exact ⟨hl, setDonePath_trusted r hr source _ _⟩
  next _ =>
    exact ⟨hl, hr⟩

/-- Edge-local anti-splicing premise for backward generation.  Whenever the
physical propagation guard is enabled, the producer state and the responder's
`done` state/path must name one source. -/
def GenerationPairCompatible (hψ : ψ > 0)
    (l r : MarkedAgentState n ψ) : Prop :=
  (l.concrete.label ≠ ⟨ψ - 1, by omega⟩ ∧
      l.concrete.state = .produce ∧ r.concrete.state = .done) →
    ∃ source, l.history.state = .trusted source ∧
      r.history.state = .trusted source ∧
      r.history.path = .trusted source

/-- Backward generation propagates the terminal wave's source mark to the new
path component and preserves it when the responder departs. -/
def markedGenSigPropagate (hψ : ψ > 0)
    (l r : MarkedAgentState n ψ) :
    MarkedAgentState n ψ × MarkedAgentState n ψ :=
  let q := genSigSaturatedPropagate hψ l.concrete r.concrete
  let propagated := l.concrete.label ≠ ⟨ψ - 1, by omega⟩ ∧
    l.concrete.state = .produce ∧ r.concrete.state = .done
  let source := SourceMark.agree l.history.state
    (SourceMark.agree r.history.state r.history.path)
  let lHistory := if propagated then
    { l.history with state := source, path := source }
  else l.history
  let rHistory := if propagated then
    { r.history with state := source }
  else r.history
  (⟨q.1, lHistory⟩, ⟨q.2, rHistory⟩)

private theorem done_to_depart_preserves_generationLocalTrusted
    (s : MarkedAgentState n ψ) (h : GenerationLocalTrusted s)
    (hs : s.concrete.state = .done) (newWait : Bool) :
    GenerationLocalTrusted
      ⟨{ s.concrete with state := .depart, wait := newWait }, s.history⟩ := by
  unfold GenerationLocalTrusted AuditLocalHistoryTrusted
    GenerationPhaseCoherent at h ⊢
  rcases h with ⟨hfields, _, hfinished⟩
  constructor
  · constructor
    · rcases hfields.1 with hinactive | hactive
      · have hne : s.concrete.state ≠ .none := by rw [hs]; decide
        exact (hne hinactive.1).elim
      · rcases hactive with ⟨_, source, hsource⟩
        right
        exact ⟨by intro hbad; contradiction, source, hsource⟩
    · exact hfields.2
  · constructor
    · intro hbad
      contradiction
    · intro _
      exact hfinished (.inl hs)

private theorem setDepart_trusted (s : MarkedAgentState n ψ)
    (h : GenerationLocalTrusted s) (hs : s.concrete.state = .done)
    (source : Fin n) (hpathSource : s.history.path = .trusted source) :
    GenerationLocalTrusted
      ⟨{ s.concrete with state := .depart },
       { s.history with state := .trusted source }⟩ := by
  have hfinished := h.2.2 (.inl hs)
  constructor
  · unfold AuditLocalHistoryTrusted
    constructor
    · right
      exact ⟨by intro hbad; contradiction, source, rfl⟩
    constructor
    · right
      exact ⟨hfinished.1, source, hpathSource⟩
    · exact h.1.2.2
  · unfold GenerationPhaseCoherent SameTrustedSource
    constructor
    · intro hbad
      contradiction
    · intro _
      exact ⟨hfinished.1, source, rfl, hpathSource⟩

/-- Backward propagation preserves the local trusted relation provided the two
halves of the physical wave satisfy the explicit common-source compatibility
premise.  Without this premise a physically permitted forged splice is marked
tainted, so fieldwise local trust alone is intentionally not closed. -/
theorem markedGenSigPropagate_preserves_generationLocalTrusted
    (hψ : ψ > 0) (l r : MarkedAgentState n ψ)
    (hl : GenerationLocalTrusted l) (hr : GenerationLocalTrusted r)
    (hcompat : GenerationPairCompatible hψ l r) :
    let q := markedGenSigPropagate hψ l r
    GenerationLocalTrusted q.1 ∧ GenerationLocalTrusted q.2 := by
  unfold markedGenSigPropagate genSigSaturatedPropagate
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
    have hleft := setDonePath_trusted l hl source
      l.concrete.label.val (if l.concrete.bit then 1 else 0)
    have hright := setDepart_trusted r hr hpropagate.2.2
      source hrightPath
    exact ⟨hleft, hright⟩
  next _ =>
    exact ⟨hl, hr⟩

/-- Source departure changes only the control phase and preserves its source. -/
def markedGenSigFinish (hψ : ψ > 0)
    (l r : MarkedAgentState n ψ) :
    MarkedAgentState n ψ × MarkedAgentState n ψ :=
  let q := genSigSaturatedFinish hψ l.concrete r.concrete
  (⟨q.1, l.history⟩, ⟨q.2, r.history⟩)

/-- Source departure preserves local history: `done` and `depart` have the same
path/source obligation and Finish changes no comparison payload. -/
theorem markedGenSigFinish_preserves_generationLocalTrusted
    (hψ : ψ > 0) (l r : MarkedAgentState n ψ)
    (hl : GenerationLocalTrusted l) (hr : GenerationLocalTrusted r) :
    let q := markedGenSigFinish hψ l r
    GenerationLocalTrusted q.1 ∧ GenerationLocalTrusted q.2 := by
  unfold markedGenSigFinish genSigSaturatedFinish
  dsimp only
  split
  next hfinish =>
    exact ⟨done_to_depart_preserves_generationLocalTrusted
      l hl hfinish.2 true, hr⟩
  next _ =>
    exact ⟨hl, hr⟩

/-- Full edge-aware Algorithm 4 history, including saturated WAIT. -/
def markedGenSig (hψ : ψ > 0) (κ : Nat) (sourcePos : Fin n)
    (l r : MarkedAgentState n ψ) :
    MarkedAgentState n ψ × MarkedAgentState n ψ :=
  let q := markedWait hψ κ l r
  let q := markedGenSigStart hψ sourcePos q.1 q.2
  let q := markedGenSigEmit hψ q.1 q.2
  let q := markedGenSigPropagate hψ q.1 q.2
  markedGenSigFinish hψ q.1 q.2

/-- Full GENSIG preserves local generation history once the exact
post-Start/post-Emit pair satisfies the common-source anti-splicing premise.
The premise is stated at the only stage that combines two partial waves; a
future configuration invariant must supply it on every scheduled edge. -/
theorem markedGenSig_preserves_generationLocalTrusted
    (hψ : ψ > 0) (κ : Nat) (source : Fin n)
    (l r : MarkedAgentState n ψ)
    (hl : GenerationLocalTrusted l) (hr : GenerationLocalTrusted r)
    (hcompat :
      let q0 := markedWait hψ κ l r
      let q1 := markedGenSigStart hψ source q0.1 q0.2
      let q2 := markedGenSigEmit hψ q1.1 q1.2
      GenerationPairCompatible hψ q2.1 q2.2) :
    let q := markedGenSig hψ κ source l r
    GenerationLocalTrusted q.1 ∧ GenerationLocalTrusted q.2 := by
  let q0 := markedWait hψ κ l r
  have h0 := markedWait_preserves_generationLocalTrusted hψ κ l r hl hr
  change GenerationLocalTrusted q0.1 ∧ GenerationLocalTrusted q0.2 at h0
  let q1 := markedGenSigStart hψ source q0.1 q0.2
  have h1 := markedGenSigStart_preserves_generationLocalTrusted
    hψ source q0.1 q0.2 h0.1 h0.2
  change GenerationLocalTrusted q1.1 ∧ GenerationLocalTrusted q1.2 at h1
  let q2 := markedGenSigEmit hψ q1.1 q1.2
  have h2 := markedGenSigEmit_preserves_generationLocalTrusted
    hψ q1.1 q1.2 h1.1 h1.2
  change GenerationLocalTrusted q2.1 ∧ GenerationLocalTrusted q2.2 at h2
  change GenerationPairCompatible hψ q2.1 q2.2 at hcompat
  let q3 := markedGenSigPropagate hψ q2.1 q2.2
  have h3 := markedGenSigPropagate_preserves_generationLocalTrusted
    hψ q2.1 q2.2 h2.1 h2.2 hcompat
  change GenerationLocalTrusted q3.1 ∧ GenerationLocalTrusted q3.2 at h3
  have h4 := markedGenSigFinish_preserves_generationLocalTrusted
    hψ q3.1 q3.2 h3.1 h3.2
  simpa [markedGenSig, q0, q1, q2, q3] using h4

/-- Erasing the marked generation stage gives exactly the repaired physical
GENSIG transition. -/
theorem erase_markedGenSig (hψ : ψ > 0) (κ : Nat) (sourcePos : Fin n)
    (l r : MarkedAgentState n ψ) :
    let q := markedGenSig hψ κ sourcePos l r
    (q.1.concrete, q.2.concrete) =
      genSigSaturated hψ κ l.concrete r.concrete := by
  rfl

private def absentHistory4 : LocalComparisonHistory 4 :=
  ⟨.absent, .absent, .absent, .absent⟩

/-- Left endpoint of the canonical ψ=2 genuine generation regression. -/
def twoAgentBirthLeft : MarkedAgentState 4 2 :=
  ⟨{ PPLLCounterexample.state2 0 with wait := false }, absentHistory4⟩

/-- Right endpoint of the canonical ψ=2 genuine generation regression. -/
def twoAgentBirthRight : MarkedAgentState 4 2 :=
  ⟨PPLLCounterexample.state2 1, absentHistory4⟩

/-- Exact intermediate boundary immediately before backward propagation in the
ψ=2 generation cascade. -/
def twoAgentBirthBeforePropagate :
    MarkedAgentState 4 2 × MarkedAgentState 4 2 :=
  let q0 := markedWait (by omega : 2 > 0) 10
    twoAgentBirthLeft twoAgentBirthRight
  let q1 := markedGenSigStart (by omega : 2 > 0) 2 q0.1 q0.2
  markedGenSigEmit (by omega : 2 > 0) q1.1 q1.2

/-- The idle endpoints inhabit the staged generation trusted surface. -/
theorem twoAgentBirth_initial_trusted :
    GenerationLocalTrusted twoAgentBirthLeft ∧
      GenerationLocalTrusted twoAgentBirthRight := by
  constructor <;>
    simp [twoAgentBirthLeft, twoAgentBirthRight, absentHistory4,
      GenerationLocalTrusted, AuditLocalHistoryTrusted,
      GenerationPhaseCoherent, MarkMatches, SameTrustedSource,
      PPLLCounterexample.state2]

/-- Before backward propagation, both state waves and the emitted terminal path
carry the actual source position 2. -/
theorem twoAgentBirth_beforePropagate_sources :
    twoAgentBirthBeforePropagate.1.history.state = .trusted 2 ∧
      twoAgentBirthBeforePropagate.2.history.state = .trusted 2 ∧
      twoAgentBirthBeforePropagate.2.history.path = .trusted 2 := by
  decide

/-- The anti-splicing premise is concretely satisfiable on a genuine birth. -/
theorem twoAgentBirth_intermediate_compatible :
    GenerationPairCompatible (by omega : 2 > 0)
      twoAgentBirthBeforePropagate.1 twoAgentBirthBeforePropagate.2 := by
  intro _
  exact ⟨2, twoAgentBirth_beforePropagate_sources.1,
    twoAgentBirth_beforePropagate_sources.2.1,
    twoAgentBirth_beforePropagate_sources.2.2⟩

/-- The full ψ=2 marked GENSIG execution is locally trusted; this discharges
non-vacuity of the compatibility premise used by the general theorem. -/
theorem twoAgentBirth_output_trusted :
    let q := markedGenSig (by omega : 2 > 0) 10 2
      twoAgentBirthLeft twoAgentBirthRight
    GenerationLocalTrusted q.1 ∧ GenerationLocalTrusted q.2 := by
  apply markedGenSig_preserves_generationLocalTrusted (by omega) 10 2
    twoAgentBirthLeft twoAgentBirthRight
    twoAgentBirth_initial_trusted.1 twoAgentBirth_initial_trusted.2
  exact twoAgentBirth_intermediate_compatible

/-- The ψ=2 same-interaction cascade receives one common, actual source
position on both generated path components and both departure states. -/
theorem markedGenSig_two_agent_birth_records_source :
    let l : MarkedAgentState 4 2 :=
      ⟨{ PPLLCounterexample.state2 0 with wait := false }, absentHistory4⟩
    let r : MarkedAgentState 4 2 :=
      ⟨PPLLCounterexample.state2 1, absentHistory4⟩
    let q := markedGenSig (by omega : 2 > 0) 10 2 l r
    q.1.concrete.path = .some 0 0 ∧
      q.2.concrete.path = .some 1 0 ∧
      q.1.concrete.state = .depart ∧ q.2.concrete.state = .depart ∧
      q.1.history.state = .trusted 2 ∧ q.1.history.path = .trusted 2 ∧
      q.2.history.state = .trusted 2 ∧ q.2.history.path = .trusted 2 := by
  decide


end PPLLComparisonHistory
