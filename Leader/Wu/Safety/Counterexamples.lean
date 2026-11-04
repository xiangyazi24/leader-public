import Leader.Wu.Protocol.Algorithm
import Leader.Wu.Safety.SafeConfig
import Leader.Wu.Scheduler.Probability
import Leader.Wu.Safety.SignalCoherence
import Leader.Wu.Protocol.Repairs
import Leader.Wu.WriteSeq.CommandProvenance
import Leader.Wu.Safety.ConvergencePhasePredicates

/-!
# Machine-checked counterexamples for the concrete P_PLL encoding

Wu's five safe-configuration conditions constrain leaders, bullets, barriers,
overwriting signals, labels, and group bits, but do not constrain auxiliary
comparison provenance. The example below satisfies all five conditions and
contains a complete two-agent payload whose labels/bits locally match the
agents, together with terminal `.equal` states. Nothing ties this plausible
payload to a genuine source group. A single concrete `ppll` interaction
promotes the follower and migrates the new leader one position left, leaving
two leaders.

Thus Definition 2 is not closed over arbitrary values of the encoded
`AgentState` fields.  A faithful closedness theorem needs an additional
reachable-state/signal-coherence invariant; quiescence is not a solution,
because the protocol intentionally creates comparison signals.
-/

namespace PPLLCounterexample

open PPLL

def state2 (label : Fin 2) (leader : Bool := false)
    (state : MainState := .none) : AgentState 2 :=
  { leader, probe := false, phase := false, bit := false, wait := true,
    state, path := .bot, reset := false, carry := false, count := 0,
    label, h_field := false, path2 := none, path3 := none,
    path4 := none, path5 := none, p := false, p_carry := false,
    reset_cmd := false, echo := false, signal_B := 0, bullet := 0,
    shield := true, write_state := .none, write := .none, last := false,
    last_set := false, last_unset := false, b_carry := false, gen_ws := false,
    ws_echo := false, signal_ws := false }

/-- The present Lean state type is not finite: its unbounded `count : Nat`
field alone embeds all natural numbers into `AgentState 2`.  Bounds intended by
the pseudocode must be represented with `Fin` or proved as reachability
invariants before a finite/polylogarithmic state-space theorem is possible. -/
def countFamily (k : Nat) : AgentState 2 := { state2 0 with count := k }

theorem countFamily_injective : Function.Injective countFamily := by
  intro x y h
  have hcount := congrArg AgentState.count h
  simpa [countFamily, state2] using hcount

def a0 : AgentState 2 := { state2 0 true with bit := true }
def a1 : AgentState 2 := { state2 1 with bit := true }
def a2 : AgentState 2 :=
  { state2 0 false .equal with path := .some 0 0 }
def a3 : AgentState 2 :=
  { state2 1 false .equal with path := .some 1 0 }

/-- Labels are `0,1,0,1` and the sole leader is at 0. Leader group `g₀`
has bits `11`, while stable non-leader group `g₁` has bits `00`. Positions 2–3
carry a complete `00`, locally bit-consistent comparison payload, but nothing
ties it to a distinct genuine source group or valid traversal position. -/
def counterConfig : Fin 4 → AgentState 2
  | ⟨0, _⟩ => a0
  | ⟨1, _⟩ => a1
  | ⟨2, _⟩ => a2
  | ⟨3, _⟩ => a3

/-- A deliberately weak local sanity check: any terminal `.equal` state has
a path entry at the agent's own label carrying that agent's actual bit. The
counterexample satisfies this; local payload checks cannot replace provenance. -/
def locallyBitConsistent {ψ n : Nat} (C : Fin n → AgentState ψ) : Prop :=
  ∀ i, (C i).state = .equal →
    ∃ bit : Nat, (C i).path = .some (C i).label.val bit ∧
      bit = if (C i).bit then 1 else 0

theorem ring4 : DirectedRing 4 := ⟨by omega⟩

private theorem fin4_cases (i : Fin 4) :
    i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by
  have h : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ i.val = 3 := by omega
  rcases h with h | h | h | h
  · exact .inl (Fin.ext h)
  · exact .inr (.inl (Fin.ext h))
  · exact .inr (.inr (.inl (Fin.ext h)))
  · exact .inr (.inr (.inr (Fin.ext h)))

/-- Use κ=10 so WAIT does not independently start a fresh comparison during
this interaction; the counterexample isolates a pre-existing fake signal. -/
def badPair : AgentState 2 × AgentState 2 :=
  ppll (by omega) 10 a2 a3

def counterSuccessor : Fin 4 → AgentState 2 := fun k =>
  if k = (2 : Fin 4) then badPair.1
  else if k = (3 : Fin 4) then badPair.2
  else counterConfig k

def counterProtocol : PopulationProtocol :=
  { Q := AgentState 2, Y := LeaderOutput,
    transition := ppll (by omega) 10, output := AgentState.outputFn }

/-! ## Auditable stage-by-stage trace of the bad interaction

These definitions mirror Algorithm 1's sequential call order.  They make the
counterexample independent of a single opaque reduction of `ppll`: every
intermediate pair and the unique leader-creation/migration points are checked
separately below. `genSig` includes Algorithm 3 (`WAIT`). -/

def badAfterPPsi : AgentState 2 × AgentState 2 :=
  pPsi (by omega) a2 a3

def badAfterGenSig : AgentState 2 × AgentState 2 :=
  genSig (by omega) 10 badAfterPPsi.1 badAfterPPsi.2

def badAfterCleanSig : AgentState 2 × AgentState 2 :=
  cleanSig (by omega) badAfterGenSig.1 badAfterGenSig.2

def badAfterEliminateSig : AgentState 2 × AgentState 2 :=
  eliminateSig (by omega) badAfterCleanSig.1 badAfterCleanSig.2

def badAfterSigMove : AgentState 2 × AgentState 2 :=
  sigMove (by omega) badAfterEliminateSig.1 badAfterEliminateSig.2

def badAfterCheckSig : AgentState 2 × AgentState 2 :=
  checkSig (by omega) badAfterSigMove.1 badAfterSigMove.2

def badAfterDisappear : AgentState 2 × AgentState 2 :=
  disappear (by omega) badAfterCheckSig.1 badAfterCheckSig.2

def badAfterCompareSig : AgentState 2 × AgentState 2 :=
  compareSig (by omega) badAfterDisappear.1 badAfterDisappear.2

def badAfterSuppressSig : AgentState 2 × AgentState 2 :=
  suppressSig (by omega) badAfterCompareSig.1 badAfterCompareSig.2

def badAfterEliminateLeaders : AgentState 2 × AgentState 2 :=
  eliminateLeaders (by omega) badAfterSuppressSig.1 badAfterSuppressSig.2

def badAfterWriteSeq : AgentState 2 × AgentState 2 :=
  writeSeq (by omega) badAfterEliminateLeaders.1 badAfterEliminateLeaders.2

/-- Algorithm 2 is inert on the non-barrier edge carrying the fake signal. -/
theorem bad_trace_pPsi : badAfterPPsi = (a2, a3) := by decide

/-- `WAIT`, called inside GENSIG, only toggles the initiator's `h_field` here;
it does not create either leader or alter the comparison payload. -/
theorem bad_trace_genSig :
    badAfterGenSig = ({ a2 with h_field := true }, a3) := by decide

/-- Algorithms 5, 9, and 10 preserve the relevant pair exactly. CLEAN_SIG's
short-lived local connector fields cancel during this interaction. -/
theorem bad_trace_clean_eliminate_move :
    badAfterCleanSig = badAfterGenSig ∧
    badAfterEliminateSig = badAfterCleanSig ∧
    badAfterSigMove = badAfterEliminateSig := by decide

/-- Algorithm 11 is the unique point in this trace where a leader is created:
the terminal responder already carries `.equal`. -/
theorem bad_trace_check_creates_responder :
    badAfterCheckSig =
      ({ a2 with h_field := true }, { a3 with leader := true }) := by decide

/-- Algorithms 13 and 6--8 retain that new leader. Comparison changes both
state-machine tags to `.congest` but does not validate signal provenance. -/
theorem bad_trace_disappear_compare :
    badAfterDisappear = badAfterCheckSig ∧
    badAfterCompareSig =
      ({ a2 with h_field := true, state := .congest },
       { a3 with leader := true, state := .congest }) := by decide

/-- Algorithms 14 and 15 do not remove the newly created responder leader. -/
theorem bad_trace_suppress_eliminateLeaders :
    badAfterSuppressSig = badAfterCompareSig ∧
    badAfterEliminateLeaders = badAfterSuppressSig := by decide

/-- Algorithm 16 migrates a nonzero-label responder leader to its left neighbor.
The old leader at ring position 0 is outside this interacting pair and remains. -/
theorem bad_trace_writeSeq_migrates :
    badAfterWriteSeq =
      ({ a2 with h_field := true, state := .congest, leader := true },
       { a3 with state := .congest, write_state := .depart }) := by decide

/-- The explicit staged execution is definitionally the top-level Algorithm-1
transition. This closes the audit gap between the one-shot counterexample and
its individual pseudocode components. -/
theorem bad_trace_matches_ppll : badAfterWriteSeq = badPair := by decide

/-! ## Algorithm-19 increment regression checks -/

private def incrementL : AgentState 2 := state2 0
private def incrementR (bit : Bool) : AgentState 2 :=
  { state2 1 with bit, write := .increment_group }

/-- On a `1` bit, increment flips to `0` and propagates the carry left.
This guards the correction of the former implementation, which incorrectly
set `depart` unconditionally and stopped every carry. -/
theorem writeAction_increment_carries_through_one :
    let out := writeAction (by omega : 2 > 0) incrementL (incrementR true)
    out.2.bit = false ∧ out.1.write_state = .increment_group := by
  decide

/-- On a `0` bit, increment flips to `1` and terminates the carry. -/
theorem writeAction_increment_stops_at_zero :
    let out := writeAction (by omega : 2 > 0) incrementL (incrementR false)
    out.2.bit = true ∧ out.1.write_state = .depart := by
  decide

/-! ## Algorithm-1 value-domain escape -/

private def overflowL : AgentState 2 :=
  { state2 0 with carry := true, h_field := false }

private def overflowR : AgentState 2 :=
  { state2 1 with count := 1, h_field := true }

/-- Both inputs obey Algorithm 1's declared bounds for κ=1. -/
theorem overflow_inputs_inProtocolDomain :
    overflowL.inProtocolDomain 1 ∧ overflowR.inProtocolDomain 1 := by
  simp [AgentState.inProtocolDomain, overflowL, overflowR, state2]

/-- WAIT increments `count=κ` to `κ+1`. Hence the pseudocode, interpreted
with ordinary natural-number addition, does not map its declared finite state
space to itself from arbitrary legal field combinations. -/
theorem wait_escapes_count_domain :
    (wait (by omega : 2 > 0) 1 overflowL overflowR).2.count = 2 ∧
    ¬(wait (by omega : 2 > 0) 1 overflowL overflowR).2.inProtocolDomain 1 := by
  have hcount : (wait (by omega : 2 > 0) 1 overflowL overflowR).2.count = 2 := by
    decide
  refine ⟨hcount, ?_⟩
  intro hdom
  unfold AgentState.inProtocolDomain at hdom
  rw [hcount] at hdom
  omega

/-- The same overflow survives the complete top-level transition. -/
theorem ppll_escapes_count_domain :
    ¬(ppll (by omega : 2 > 0) 1 overflowL overflowR).2.inProtocolDomain 1 := by
  have hcount : (ppll (by omega : 2 > 0) 1 overflowL overflowR).2.count = 2 := by
    decide
  intro hdom
  unfold AgentState.inProtocolDomain at hdom
  rw [hcount] at hdom
  omega

/-- The combined explicit repair branch clamps the same witness at κ. -/
theorem repaired_ppll_clamps_overflow_witness :
    (PPLLRepair.ppllSaturatedNoCollision (by omega : 2 > 0) 1
      overflowL overflowR).2.count = 1 := by
  decide

private theorem counter_unique : hasUniqueLeader 4 counterConfig := by
  refine ⟨0, by decide, ?_⟩
  intro j hj
  rcases fin4_cases j with h | h | h | h <;> subst j
  · rfl
  · simp [counterConfig, a1, state2, AgentState.isLeader] at hj
  · simp [counterConfig, a2, state2, AgentState.isLeader] at hj
  · simp [counterConfig, a3, state2, AgentState.isLeader] at hj

private theorem counter_no_bad_bullet :
    noNonPeacefulBullet (by omega : 2 > 0) ring4 counterConfig := by
  intro i hi
  rcases fin4_cases i with h | h | h | h <;> subst i <;>
    simp [counterConfig, a0, a1, a2, a3, state2] at hi

private theorem counter_no_free_barrier :
    noFreeBarrier (by omega : 2 > 0) ring4 counterConfig := by
  intro i
  rcases fin4_cases i with h | h | h | h <;> subst i <;>
    simp [DirectedRing.rightNeighbor, isBarrier, counterConfig,
      a0, a1, a2, a3, state2]

private theorem counter_no_free_ow :
    noFreeOverwritingSignal (by omega : 2 > 0) ring4 counterConfig := by
  refine ⟨0, by decide, by decide, ?_⟩
  intro i hi hbound hfree
  obtain ⟨_, haligned⟩ := hfree.1
  obtain ⟨p, hpath, _⟩ := haligned 0 (by omega)
  have hnone : ∀ k : Fin 4, (counterConfig k).path3 = none := by
    intro k
    rcases fin4_cases k with h | h | h | h <;> subst k <;>
      decide
  rw [hnone] at hpath
  contradiction

private theorem counter_stable_id :
    isStableIDSequence (by omega : 2 > 0) ring4 counterConfig := by
  refine ⟨0, by decide, by decide, ?_, ?_⟩
  · intro k hk
    have h : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
    rcases h with h | h | h | h <;> subst k <;> decide
  · intro i hi hlt
    have : i = 1 := by omega
    subst i
    unfold groupID
    simp [List.range_succ, counterConfig, a0, a1, a2, a3, state2,
      trailingZeros]

/-- The fake complete signal is locally consistent with the bits at positions
2–3. What is missing is a relation to the signal's genuine source group. -/
theorem counterConfig_locallyBitConsistent :
    locallyBitConsistent counterConfig := by
  intro i heq
  rcases fin4_cases i with h | h | h | h <;> subst i
  · simp [counterConfig, a0, state2] at heq
  · simp [counterConfig, a1, state2] at heq
  · exact ⟨0, by decide, by decide⟩
  · exact ⟨0, by decide, by decide⟩

/-- Every value in the counterexample lies in the bounded domains of
Algorithm 1. The failure is therefore not caused by the unbounded Lean
over-approximation; it is caused by missing cross-field signal coherence. -/
theorem counterConfig_inProtocolDomain :
    ∀ i, (counterConfig i).inProtocolDomain 10 := by
  intro i
  rcases fin4_cases i with h | h | h | h <;> subst i <;>
    simp [AgentState.inProtocolDomain, counterConfig, a0, a1, a2, a3, state2]

/-- The initial configuration satisfies Wu's five-condition schema under
the documented T6 interpretation of free overwriting signals. Because every
path3 field is absent, this witness is insensitive to that interpretation. -/
theorem counterConfig_paper_safe :
    PaperSafeConfig (by omega : 2 > 0) ring4 counterConfig where
  unique_leader := counter_unique
  no_nonpeaceful_bullet := counter_no_bad_bullet
  no_free_barrier := counter_no_free_barrier
  no_free_overwriting_signal := counter_no_free_ow
  stable_id_sequence := counter_stable_id

/-- The corrupted comparison result creates a leader at position 3, after
which WRITE_SEQ migrates it to position 2. -/
theorem badPair_creates_left_leader : badPair.1.leader = true := by
  decide

/-- WAIT saturation and bullet collision repair do not address the independent
comparison-provenance defect. -/
theorem combined_repair_still_creates_fake_signal_leader :
    (PPLLRepair.ppllSaturatedNoCollision (by omega : 2 > 0) 10 a2 a3).1.leader =
      true := by
  decide

/-- The one-step successor has leaders at both positions 0 and 2. -/
theorem counterSuccessor_not_unique :
    ¬hasUniqueLeader 4 counterSuccessor := by
  intro ⟨i, _, huniq⟩
  have h0 : (counterSuccessor 0).isLeader := by decide
  have h2 : (counterSuccessor 2).isLeader := by decide
  have h02 : (0 : Fin 4) = 2 := (huniq 0 h0).trans (huniq 2 h2).symm
  have := congrArg Fin.val h02
  omega

/-- **Counterexample to literal Definition-2 closedness.**  There is a
five-condition-safe configuration whose successor under one concrete `ppll`
interaction is not five-condition-safe. -/
theorem paperSafe_not_closed :
    ∃ (C C' : Fin 4 → AgentState 2) (e : Fin 4),
      PaperSafeConfig (by omega : 2 > 0) ring4 C ∧
      C' = PopulationProtocol.step counterProtocol ring4 C e ∧
      ¬PaperSafeConfig (by omega : 2 > 0) ring4 C' := by
  refine ⟨counterConfig, counterSuccessor, 2, counterConfig_paper_safe, ?_, ?_⟩
  · funext k
    rfl
  · intro hsafe
    exact counterSuccessor_not_unique hsafe.unique_leader

/-- Direct `ClosedPred` form of the same counterexample: the concrete protocol
does not preserve the literal five-condition predicate in one step. -/
theorem paperSafe_not_closed_pred :
    ¬PopulationProtocol.ClosedPred counterProtocol ring4
      (PaperSafeConfig (by omega : 2 > 0) ring4) := by
  intro hclosed
  have hsafe' := hclosed counterConfig counterConfig_paper_safe
    counterSuccessor ⟨2, by funext k; rfl⟩
  exact counterSuccessor_not_unique hsafe'.unique_leader

/-- Even intersecting Definition 2 with all Algorithm-1 value bounds is not
closed. A relational signal-coherence invariant, not mere field bounds, is
necessary. -/
theorem boundedPaperSafe_not_closed_pred :
    ¬PopulationProtocol.ClosedPred counterProtocol ring4
      (fun C => PaperSafeConfig (by omega : 2 > 0) ring4 C ∧
        ∀ i, (C i).inProtocolDomain 10) := by
  intro hclosed
  have hnext := hclosed counterConfig
    ⟨counterConfig_paper_safe, counterConfig_inProtocolDomain⟩
    counterSuccessor ⟨2, by funext k; rfl⟩
  exact counterSuccessor_not_unique hnext.1.unique_leader

/-- Definition 2 remains non-closed even after adding value bounds and the
obvious local bit-consistency check. Signal provenance must be global. -/
theorem locallyConsistentPaperSafe_not_closed_pred :
    ¬PopulationProtocol.ClosedPred counterProtocol ring4
      (fun C => PaperSafeConfig (by omega : 2 > 0) ring4 C ∧
        (∀ i, (C i).inProtocolDomain 10) ∧ locallyBitConsistent C) := by
  intro hclosed
  have hnext := hclosed counterConfig
    ⟨counterConfig_paper_safe, counterConfig_inProtocolDomain,
      counterConfig_locallyBitConsistent⟩
    counterSuccessor ⟨2, by funext k; rfl⟩
  exact counterSuccessor_not_unique hnext.1.unique_leader

/-- The fake complete payload has every component aligned with the target
(non-leader) group's current bits. -/
theorem counterConfig_comparisonBitsMatch :
    comparisonBitsMatchConfigAt ring4 counterConfig counterConfig 2 := by
  intro k hk
  have h : k = 0 ∨ k = 1 := by omega
  rcases h with h | h <;> subst k
  · exact ⟨0, 0, by decide, rfl, by decide⟩
  · exact ⟨1, 0, by decide, rfl, by decide⟩

/-- T1 cannot be certified as a complete carrier with a strict stable source
route. Unlike `counterConfig_not_checkBoundarySafe`, this contradiction is
obtained from runtime payload alignment plus source/traversal provenance, not
by assuming the CHECK-boundary conclusion. -/
theorem counterConfig_no_strict_completeComparisonCarrier
    (carrier : CompleteComparisonCarrier ring4 counterConfig counterConfig 0)
    (htarget : carrier.route.target = 1)
    (hstrict : carrier.route.source < carrier.route.target) : False := by
  obtain ⟨lp, hlp, _, _, hgroups⟩ := counter_stable_id
  obtain ⟨unique, _, huniq⟩ := counter_unique
  have h0 : (counterConfig 0).isLeader := by decide
  have hlp0 : lp = 0 := (huniq lp hlp).trans (huniq 0 h0).symm
  subst lp
  have hstart :
      stableGroupStart ring4 0 2 carrier.route.target = (2 : Fin 4) := by
    rw [htarget]
    decide
  have hbits : comparisonBitsMatchConfigAt ring4 counterConfig counterConfig
      (stableGroupStart ring4 0 2 carrier.route.target) := by
    rw [hstart]
    exact counterConfig_comparisonBitsMatch
  exact carrier.not_bits_match_target ring4 counterConfig counterConfig 0
    hgroups hstrict hbits

/-- The stronger source-component tagging interface also rejects T1. -/
theorem counterConfig_no_strict_sourceTaggedCarrier
    (carrier : SourceTaggedCompleteComparisonCarrier
      ring4 counterConfig counterConfig 0)
    (htarget : carrier.route.target = 1)
    (hstrict : carrier.route.source < carrier.route.target) : False :=
  counterConfig_no_strict_completeComparisonCarrier
    carrier.toCompleteComparisonCarrier htarget hstrict

/-- T1 also fails the lower-level invariant requiring every runtime `.equal`
state after CHECK to have one strict source-tagged prefix. -/
theorem counterConfig_afterCheck_not_equalStateProvenance :
    EqualStateProvenance ring4
      (afterCheckStep (by omega : 2 > 0) 10 ring4 counterConfig 2)
      counterConfig → False := by
  intro h
  have hedge := h.checkEdgeSafe (by omega : 2 > 0) 10 ring4
    (by omega : 1 < 4) counterConfig 2
  exact hedge (by decide)

/-- The exact CHECK-boundary obligation rejects the fake payload before it
can be used in a strengthened closedness theorem. -/
theorem counterConfig_not_checkBoundarySafe :
    ¬CheckBoundarySafe (by omega : 2 > 0) 10 ring4 counterConfig := by
  intro hsafe
  exact hsafe 2 (by decide)

/-- Consequently the fake payload cannot be equipped with the new concrete
field/history certificate. -/
theorem counterConfig_not_fieldCheckHistoryCertified :
    FieldCheckHistoryCertified (by omega : 2 > 0) 10 ring4 counterConfig →
      False := by
  intro hcert
  exact counterConfig_not_checkBoundarySafe hcert.toCheckBoundarySafe

/-! ## Faithfully generated source-self comparison counterexample -/

private def selfSourceL : AgentState 2 := { state2 0 with wait := false }
private def selfSourceR : AgentState 2 := state2 1

def selfSourceConfig : Fin 4 → AgentState 2
  | ⟨0, _⟩ => a0
  | ⟨1, _⟩ => a1
  | ⟨2, _⟩ => selfSourceL
  | ⟨3, _⟩ => selfSourceR

def selfSourceRound1 : AgentState 2 × AgentState 2 :=
  PPLLRepair.ppllSaturatedNoCollision (by omega) 10 selfSourceL selfSourceR

def selfSourceAfterOne : Fin 4 → AgentState 2
  | ⟨0, _⟩ => a0
  | ⟨1, _⟩ => a1
  | ⟨2, _⟩ => selfSourceRound1.1
  | ⟨3, _⟩ => selfSourceRound1.2

def selfSourceRound2BeforeCheck : AgentState 2 × AgentState 2 :=
  ppllBeforeCheck (by omega) 10 selfSourceRound1.1 selfSourceRound1.2

def selfSourceRound2AfterCheck : AgentState 2 × AgentState 2 :=
  checkSig (by omega) selfSourceRound2BeforeCheck.1 selfSourceRound2BeforeCheck.2

def selfSourceRound2 : AgentState 2 × AgentState 2 :=
  PPLLRepair.ppllSaturatedNoCollision (by omega) 10
    selfSourceRound1.1 selfSourceRound1.2

def selfSourceAfterTwo : Fin 4 → AgentState 2 :=
  PopulationProtocol.step (PPLLRepair.protocol (by omega) 10)
    ring4 selfSourceAfterOne 2

/-- The repaired first round faithfully generates the source group's own
complete `00` signal, but COMPARE re-arms both still-source-aligned components
as `.congest`. -/
theorem selfSource_round1_rearmed_in_place :
    selfSourceRound1.1.path = .some 0 0 ∧
    selfSourceRound1.2.path = .some 1 0 ∧
    selfSourceRound1.1.state = .congest ∧
    selfSourceRound1.2.state = .congest ∧
    selfSourceRound1.2.leader = false := by
  decide

/-- On the same edge's next interaction SIGMOVE is blocked by the complete
source-aligned signal, so the re-armed fields reach CHECK unchanged. -/
theorem selfSource_round2_before_check_still_source_aligned :
    selfSourceRound2BeforeCheck.1.path = .some 0 0 ∧
    selfSourceRound2BeforeCheck.2.path = .some 1 0 ∧
    selfSourceRound2BeforeCheck.1.state = .congest ∧
    selfSourceRound2BeforeCheck.2.state = .congest := by
  decide

set_option maxRecDepth 4096 in
/-- CHECK compares the signal to its own source group and creates a terminal
leader without any forged path or stale `.equal` input. -/
theorem selfSource_source_self_terminal_check :
    selfSourceRound2AfterCheck.1.state = .equal ∧
    selfSourceRound2AfterCheck.2.state = .equal ∧
    selfSourceRound2AfterCheck.2.label = (1 : Fin 2) ∧
    selfSourceRound2AfterCheck.2.leader = true := by
  decide

set_option maxRecDepth 4096 in
/-- The combined WAIT/bullet repair leaves this independent comparison defect:
the second full interaction migrates the newly created leader to the left. -/
theorem combined_repair_source_self_creates_leader :
    selfSourceRound2.1.leader = true := by
  decide

private theorem selfSource_unique (C : Fin 4 → AgentState 2)
    (h0 : (C 0).leader = true)
    (h1 : (C 1).leader = false)
    (h2 : (C 2).leader = false)
    (h3 : (C 3).leader = false) : hasUniqueLeader 4 C := by
  refine ⟨0, by simpa [AgentState.isLeader] using h0, ?_⟩
  intro j hj
  rcases fin4_cases j with h | h | h | h <;> subst j
  · rfl
  · simp [AgentState.isLeader, h1] at hj
  · simp [AgentState.isLeader, h2] at hj
  · simp [AgentState.isLeader, h3] at hj

private theorem selfSource_no_bad_bullet (C : Fin 4 → AgentState 2)
    (hb : ∀ i, (C i).bullet = 0) :
    noNonPeacefulBullet (by omega : 2 > 0) ring4 C := by
  intro i hi
  rw [hb i] at hi
  contradiction

private def parityLabel (i : Fin 4) : Fin 2 :=
  ⟨i.val % 2, Nat.mod_lt _ (by omega)⟩

private theorem selfSource_no_free_barrier (C : Fin 4 → AgentState 2)
    (hlabels : ∀ i, (C i).label = parityLabel i)
    (hleader : (C 0).leader = true) :
    noFreeBarrier (by omega : 2 > 0) ring4 C := by
  have hl0 : (C 0).label = 0 := (hlabels 0).trans (by decide)
  have hl1 : (C 1).label = 1 := (hlabels 1).trans (by decide)
  have hl2 : (C 2).label = 0 := (hlabels 2).trans (by decide)
  have hl3 : (C 3).label = 1 := (hlabels 3).trans (by decide)
  intro i
  dsimp only
  rcases fin4_cases i with h | h | h | h <;> subst i
  · simp [DirectedRing.rightNeighbor, isBarrier, hl0, hl1]
  · simp [DirectedRing.rightNeighbor, isBarrier, hl1, hl2]
  · simp [DirectedRing.rightNeighbor, isBarrier, hl2, hl3]
  · have hj : ring4.rightNeighbor (3 : Fin 4) = 0 := by decide
    rw [hj]
    intro _
    simpa [AgentState.isLeader] using hleader

private theorem selfSource_no_free_ow (C : Fin 4 → AgentState 2)
    (hleader : (C 0).leader = true) (hlabel : (C 0).label = 0)
    (hpath3 : ∀ i, (C i).path3 = none) :
    noFreeOverwritingSignal (by omega : 2 > 0) ring4 C := by
  refine ⟨0, by simpa [AgentState.isLeader] using hleader, hlabel, ?_⟩
  intro i hi hbound hfree
  obtain ⟨_, haligned⟩ := hfree.1
  obtain ⟨p, hp, _⟩ := haligned 0 (by omega)
  rw [hpath3] at hp
  contradiction

private theorem selfSource_stable (C : Fin 4 → AgentState 2)
    (hleader : (C 0).leader = true) (hlabel : (C 0).label = 0)
    (hlabels : ∀ i, (C i).label = parityLabel i)
    (hbits2 : (C 2).bit = false) (hbits3 : (C 3).bit = false) :
    isStableIDSequence (by omega : 2 > 0) ring4 C := by
  refine ⟨0, by simpa [AgentState.isLeader] using hleader, hlabel, ?_, ?_⟩
  · intro k hk
    have hk' : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
    rcases hk' with hk | hk | hk | hk <;> subst k
    · change (C 0).label = 0
      exact (hlabels 0).trans (by apply Fin.ext; decide)
    · change (C 1).label = 1
      exact (hlabels 1).trans (by apply Fin.ext; decide)
    · change (C 2).label = 0
      exact (hlabels 2).trans (by apply Fin.ext; decide)
    · change (C 3).label = 1
      exact (hlabels 3).trans (by apply Fin.ext; decide)
  · intro i hi hlt
    have hi1 : i = 1 := by omega
    subst i
    dsimp only
    change groupID ring4.hn C 2 = trailingZeros 1
    unfold groupID
    simp [List.range_succ, hbits2, hbits3, trailingZeros]

private theorem selfSource_all4 {P : Fin 4 → Prop}
    (h0 : P 0) (h1 : P 1) (h2 : P 2) (h3 : P 3) : ∀ i, P i := by
  intro i
  rcases fin4_cases i with h | h | h | h <;> subst i <;> assumption

theorem selfSourceConfig_paper_safe :
    PaperSafeConfig (by omega : 2 > 0) ring4 selfSourceConfig := by
  apply PaperSafeConfig.mk
  · exact selfSource_unique selfSourceConfig (by decide) (by decide)
      (by decide) (by decide)
  · exact selfSource_no_bad_bullet selfSourceConfig
      (selfSource_all4 (by decide) (by decide) (by decide) (by decide))
  · exact selfSource_no_free_barrier selfSourceConfig
      (selfSource_all4 (by decide) (by decide) (by decide) (by decide))
      (by decide)
  · exact selfSource_no_free_ow selfSourceConfig (by decide) (by decide)
      (selfSource_all4 (by decide) (by decide) (by decide) (by decide))
  · exact selfSource_stable selfSourceConfig (by decide) (by decide)
      (selfSource_all4 (by decide) (by decide) (by decide) (by decide))
      (by decide) (by decide)

theorem selfSourceAfterOne_paper_safe :
    PaperSafeConfig (by omega : 2 > 0) ring4 selfSourceAfterOne := by
  apply PaperSafeConfig.mk
  · exact selfSource_unique selfSourceAfterOne (by decide) (by decide)
      (by decide) (by decide)
  · exact selfSource_no_bad_bullet selfSourceAfterOne
      (selfSource_all4 (by decide) (by decide) (by decide) (by decide))
  · exact selfSource_no_free_barrier selfSourceAfterOne
      (selfSource_all4 (by decide) (by decide) (by decide) (by decide))
      (by decide)
  · exact selfSource_no_free_ow selfSourceAfterOne (by decide) (by decide)
      (selfSource_all4 (by decide) (by decide) (by decide) (by decide))
  · exact selfSource_stable selfSourceAfterOne (by decide) (by decide)
      (selfSource_all4 (by decide) (by decide) (by decide) (by decide))
      (by decide) (by decide)

/-- The first source-signal configuration is itself reached in one repaired
protocol step from a paper-safe state. -/
theorem selfSourceAfterOne_eq_repaired_step :
    selfSourceAfterOne = PopulationProtocol.step
      (PPLLRepair.protocol (by omega : 2 > 0) 10)
      ring4 selfSourceConfig 2 := by
  funext k
  change selfSourceAfterOne k =
    if k = (2 : Fin 4) then selfSourceRound1.1
    else if k = (3 : Fin 4) then selfSourceRound1.2
    else selfSourceConfig k
  rcases fin4_cases k with h | h | h | h <;> subst k <;> decide

set_option maxRecDepth 4096 in
/-- The repaired protocol's safe schema is not one-step closed even when the
comparison signal was generated faithfully in the immediately preceding
interaction. -/
theorem repaired_paperSafe_not_closed_by_source_self :
    ∃ (C C' : Fin 4 → AgentState 2) (e : Fin 4),
      PaperSafeConfig (by omega : 2 > 0) ring4 C ∧
      C' = PopulationProtocol.step (PPLLRepair.protocol (by omega) 10)
        ring4 C e ∧
      ¬PaperSafeConfig (by omega : 2 > 0) ring4 C' := by
  refine ⟨selfSourceAfterOne, selfSourceAfterTwo, 2,
    selfSourceAfterOne_paper_safe, ?_, ?_⟩
  · rfl
  · intro hsafe
    obtain ⟨lp, _, huniq⟩ := hsafe.unique_leader
    have h0 : (selfSourceAfterTwo 0).isLeader := by decide
    have h2 : (selfSourceAfterTwo 2).isLeader := by decide
    have h02 : (0 : Fin 4) = 2 := (huniq 0 h0).trans (huniq 2 h2).symm
    have := congrArg Fin.val h02
    omega

set_option maxRecDepth 4096 in
/-- Any proposed strengthening that accepts this faithfully generated
source-aligned carrier is non-closed under the current repaired protocol. -/
theorem any_strengthening_accepting_source_signal_not_closed
    (I : (Fin 4 → AgentState 2) → Prop) (hI : I selfSourceAfterOne) :
    ¬PopulationProtocol.ClosedPred (PPLLRepair.protocol (by omega) 10) ring4
      (fun C => PaperSafeConfig (by omega : 2 > 0) ring4 C ∧ I C) := by
  intro hclosed
  have hnext := hclosed selfSourceAfterOne
    ⟨selfSourceAfterOne_paper_safe, hI⟩ selfSourceAfterTwo ⟨2, rfl⟩
  obtain ⟨lp, _, huniq⟩ := hnext.1.unique_leader
  have h0 : (selfSourceAfterTwo 0).isLeader := by decide
  have h2 : (selfSourceAfterTwo 2).isLeader := by decide
  have h02 : (0 : Fin 4) = 2 := (huniq 0 h0).trans (huniq 2 h2).symm
  have := congrArg Fin.val h02
  omega

private def selfSourceBadTest (C : Fin 4 → AgentState 2) : Bool :=
  (C 2).leader

set_option maxRecDepth 4096 in
theorem self_source_bad_schedule_count :
    hitCount ring4 (PPLLRepair.ppllSaturatedNoCollision (by omega) 10)
      selfSourceBadTest selfSourceConfig 2 = 1 := by
  decide

theorem self_source_bad_event_probability :
    hitProbability ring4 (PPLLRepair.ppllSaturatedNoCollision (by omega) 10)
      selfSourceBadTest selfSourceConfig 2 = (1 : Rat) / 16 := by
  unfold hitProbability
  rw [self_source_bad_schedule_count, allSchedules_length]
  simp only [Nat.pow_succ, Nat.pow_zero, Nat.one_mul, Rat.natCast_ofNat]
  rfl

/-! ## Regression for the explicit T9 source-rearm repair candidate -/

def integratedSelfSourceRound1 : AgentState 2 × AgentState 2 :=
  PPLLRepair.ppllIntegratedRepair (by omega) 10 selfSourceL selfSourceR

def integratedSelfSourceRound2 : AgentState 2 × AgentState 2 :=
  PPLLRepair.ppllIntegratedRepair (by omega) 10
    integratedSelfSourceRound1.1 integratedSelfSourceRound1.2

theorem integrated_repair_keeps_source_departing :
    integratedSelfSourceRound1.1.path = .some 0 0 ∧
    integratedSelfSourceRound1.2.path = .some 1 0 ∧
    integratedSelfSourceRound1.1.state = .depart ∧
    integratedSelfSourceRound1.2.state = .depart := by
  decide

set_option maxRecDepth 4096 in
/-- The candidate removes the exact two-interaction T9 leader creation. This is
only a witness regression, not yet a general closedness theorem. -/
theorem integrated_repair_removes_source_self_witness :
    integratedSelfSourceRound2.1.leader = false ∧
    integratedSelfSourceRound2.2.leader = false ∧
    integratedSelfSourceRound2.1.state = .depart ∧
    integratedSelfSourceRound2.2.state = .depart := by
  decide

/-! ## Independent condition-2 counterexample: peaceful bullet becomes non-peaceful -/

private def bulletA0 : AgentState 2 := a0
private def bulletA1 : AgentState 2 := { a1 with bullet := 2 }
private def bulletA2 : AgentState 2 := state2 0
private def bulletA3 : AgentState 2 := state2 1

def bulletCounterConfig : Fin 4 → AgentState 2
  | ⟨0, _⟩ => bulletA0
  | ⟨1, _⟩ => bulletA1
  | ⟨2, _⟩ => bulletA2
  | ⟨3, _⟩ => bulletA3

private theorem bullet_counter_unique :
    hasUniqueLeader 4 bulletCounterConfig := by
  refine ⟨0, by decide, ?_⟩
  intro j hj
  rcases fin4_cases j with h | h | h | h <;> subst j
  · rfl
  · simp [bulletCounterConfig, bulletA1, a1, state2,
      AgentState.isLeader] at hj
  · simp [bulletCounterConfig, bulletA2, state2,
      AgentState.isLeader] at hj
  · simp [bulletCounterConfig, bulletA3, state2,
      AgentState.isLeader] at hj

/-- The live bullet at position 1 is peaceful with distance 3 to the unique
shielded leader at position 0. All four inclusive signal/label checks hold. -/
theorem bullet_counter_initially_peaceful :
    isPeacefulBullet (by omega : 2 > 0) ring4 bulletCounterConfig 1 := by
  refine ⟨by decide, 3, by omega, ?_⟩
  dsimp only
  refine ⟨by decide, by decide, ?_, ?_⟩
  · intro k hk
    have hcases : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
    rcases hcases with h | h | h | h <;> subst k <;> decide
  · intro k hk
    have hcases : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
    rcases hcases with h | h | h | h <;> subst k <;> decide

private theorem bullet_counter_no_bad_bullet :
    noNonPeacefulBullet (by omega : 2 > 0) ring4 bulletCounterConfig := by
  intro i hi
  rcases fin4_cases i with h | h | h | h <;> subst i
  · simp [bulletCounterConfig, bulletA0, a0, state2] at hi
  · exact bullet_counter_initially_peaceful
  · simp [bulletCounterConfig, bulletA2, state2] at hi
  · simp [bulletCounterConfig, bulletA3, state2] at hi

private theorem bullet_counter_no_free_barrier :
    noFreeBarrier (by omega : 2 > 0) ring4 bulletCounterConfig := by
  intro i
  rcases fin4_cases i with h | h | h | h <;> subst i <;>
    simp [DirectedRing.rightNeighbor, isBarrier, bulletCounterConfig,
      bulletA0, bulletA1, bulletA2, bulletA3, a0, a1, state2]

private theorem bullet_counter_no_free_ow :
    noFreeOverwritingSignal (by omega : 2 > 0) ring4
      bulletCounterConfig := by
  refine ⟨0, by decide, by decide, ?_⟩
  intro i hi hbound hfree
  obtain ⟨_, haligned⟩ := hfree.1
  obtain ⟨p, hpath, _⟩ := haligned 0 (by omega)
  have hnone : ∀ k : Fin 4, (bulletCounterConfig k).path3 = none := by
    intro k
    rcases fin4_cases k with h | h | h | h <;> subst k <;> decide
  rw [hnone] at hpath
  contradiction

private theorem bullet_counter_stable_id :
    isStableIDSequence (by omega : 2 > 0) ring4 bulletCounterConfig := by
  refine ⟨0, by decide, by decide, ?_, ?_⟩
  · intro k hk
    have hcases : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
    rcases hcases with h | h | h | h <;> subst k <;> decide
  · intro i hi hlt
    have hieq : i = 1 := by omega
    subst i
    unfold groupID
    simp [List.range_succ, bulletCounterConfig, bulletA0, bulletA1,
      bulletA2, bulletA3, a0, a1, state2, trailingZeros]

/-- All initial values also lie in the declared Algorithm-1 domains. -/
theorem bulletCounterConfig_inProtocolDomain :
    ∀ i, (bulletCounterConfig i).inProtocolDomain 10 := by
  intro i
  rcases fin4_cases i with h | h | h | h <;> subst i <;>
    simp [AgentState.inProtocolDomain, bulletCounterConfig, bulletA0,
      bulletA1, bulletA2, bulletA3, a0, a1, state2]

/-- No comparison signal is present, so the exact CHECK-boundary obligation
holds. This separates the condition-2 failure from T1's provenance issue. -/
theorem bulletCounterConfig_checkBoundarySafe :
    CheckBoundarySafe (by omega : 2 > 0) 10 ring4 bulletCounterConfig := by
  intro e
  rcases fin4_cases e with h | h | h | h <;> subst e <;> decide

/-- This second witness satisfies the five-field paper schema and has no
comparison/path payload at all. -/
theorem bulletCounterConfig_paper_safe :
    PaperSafeConfig (by omega : 2 > 0) ring4 bulletCounterConfig where
  unique_leader := bullet_counter_unique
  no_nonpeaceful_bullet := bullet_counter_no_bad_bullet
  no_free_barrier := bullet_counter_no_free_barrier
  no_free_overwriting_signal := bullet_counter_no_free_ow
  stable_id_sequence := bullet_counter_stable_id

def bulletCounterPair : AgentState 2 × AgentState 2 :=
  ppll (by omega) 10 bulletA0 bulletA1

def bulletCounterSuccessor : Fin 4 → AgentState 2 := fun k =>
  if k = (0 : Fin 4) then bulletCounterPair.1
  else if k = (1 : Fin 4) then bulletCounterPair.2
  else bulletCounterConfig k

/-- Algorithm 15 leaves the shield-blocked live bullet at the responder, then
writes the leader's bullet-absence signal onto that same responder. -/
theorem bullet_counter_collision_fields :
    bulletCounterPair.2.bullet = 2 ∧ bulletCounterPair.2.signal_B = 1 := by
  decide

/-- Under the literal p.42 inclusive condition, the surviving bullet is now
non-peaceful because offset zero requires its own `signal_B` to be zero. -/
theorem bulletCounterSuccessor_not_noNonPeaceful :
    ¬noNonPeacefulBullet (by omega : 2 > 0) ring4
      bulletCounterSuccessor := by
  intro hpeace
  have hp := hpeace 1 (by decide)
  obtain ⟨_, d, _, _, _, hsignals, _⟩ := hp
  have hzero := hsignals 0 (Nat.zero_le d)
  dsimp only at hzero
  let m : Fin 4 :=
    ⟨((1 : Fin 4).val + 0) % 4, Nat.mod_lt _ ring4.hn⟩
  change (bulletCounterSuccessor m).signal_B = 0 at hzero
  have hm : m = 1 := by apply Fin.ext; decide
  rw [hm] at hzero
  have hone : (bulletCounterSuccessor 1).signal_B = 1 := by decide
  rw [hone] at hzero
  contradiction

/-- Concrete P_PLL does not preserve paper condition 2, independently of the
comparison-signal provenance counterexample. -/
theorem paperSafe_not_closed_by_bullet :
    ∃ (C C' : Fin 4 → AgentState 2) (e : Fin 4),
      PaperSafeConfig (by omega : 2 > 0) ring4 C ∧
      C' = PopulationProtocol.step counterProtocol ring4 C e ∧
      ¬PaperSafeConfig (by omega : 2 > 0) ring4 C' := by
  refine ⟨bulletCounterConfig, bulletCounterSuccessor, 0,
    bulletCounterConfig_paper_safe, ?_, ?_⟩
  · funext k
    rfl
  · intro hsafe
    exact bulletCounterSuccessor_not_noNonPeaceful
      hsafe.no_nonpeaceful_bullet

/-- Adding value bounds and the exact CHECK-boundary signal obligation still
cannot make the literal five-field predicate closed: the independent bullet
witness satisfies both strengthenings. -/
theorem signal_coherence_alone_cannot_close_paper_safe :
    ¬PopulationProtocol.ClosedPred counterProtocol ring4
      (fun C => PaperSafeConfig (by omega : 2 > 0) ring4 C ∧
        (∀ i, (C i).inProtocolDomain 10) ∧
        CheckBoundarySafe (by omega : 2 > 0) 10 ring4 C) := by
  intro hclosed
  have hnext := hclosed bulletCounterConfig
    ⟨bulletCounterConfig_paper_safe,
      bulletCounterConfig_inProtocolDomain,
      bulletCounterConfig_checkBoundarySafe⟩
    bulletCounterSuccessor ⟨0, by funext k; rfl⟩
  exact bulletCounterSuccessor_not_noNonPeaceful
    hnext.1.no_nonpeaceful_bullet

/-- Generic form: any proposed additional invariant that accepts the bullet
witness cannot repair closedness of the literal paper predicate. -/
theorem any_strengthening_accepting_bullet_witness_not_closed
    (I : (Fin 4 → AgentState 2) → Prop) (hI : I bulletCounterConfig) :
    ¬PopulationProtocol.ClosedPred counterProtocol ring4
      (fun C => PaperSafeConfig (by omega : 2 > 0) ring4 C ∧ I C) := by
  intro hclosed
  have hnext := hclosed bulletCounterConfig
    ⟨bulletCounterConfig_paper_safe, hI⟩
    bulletCounterSuccessor ⟨0, by funext k; rfl⟩
  exact bulletCounterSuccessor_not_noNonPeaceful
    hnext.1.no_nonpeaceful_bullet

private def bulletCollisionTest (C : Fin 4 → AgentState 2) : Bool :=
  ((C 1).bullet == 2) && ((C 1).signal_B == 1)

theorem bullet_bad_schedule_count :
    hitCount ring4 (ppll (by omega : 2 > 0) 10)
      bulletCollisionTest bulletCounterConfig 1 = 1 := by
  decide

/-- The independent condition-2 violation also occurs with exact one-step
probability 1/4 under the uniform four-edge scheduler. -/
theorem bullet_bad_event_probability :
    hitProbability ring4 (ppll (by omega : 2 > 0) 10)
      bulletCollisionTest bulletCounterConfig 1 = (1 : Rat) / 4 := by
  unfold hitProbability
  rw [bullet_bad_schedule_count, allSchedules_length]
  simp only [Nat.pow_succ, Nat.pow_zero, Nat.one_mul, Rat.natCast_ofNat]

/-- Regression check for the separately named Algorithm-15 repair candidate. -/
def bulletRepairedPair : AgentState 2 × AgentState 2 :=
  PPLLRepair.ppllNoBulletSignalCollision (by omega) 10 bulletA0 bulletA1

def bulletRepairedSuccessor : Fin 4 → AgentState 2 := fun k =>
  if k = (0 : Fin 4) then bulletRepairedPair.1
  else if k = (1 : Fin 4) then bulletRepairedPair.2
  else bulletCounterConfig k

theorem bullet_repair_removes_collision :
    bulletRepairedPair.2.bullet = 2 ∧
    bulletRepairedPair.2.signal_B = 0 := by
  decide

/-- The minimal no-collision candidate repairs this exact witness while keeping
the literal inclusive peacefulness predicate. This is not yet a general
condition-2 preservation theorem. -/
theorem bullet_repair_witness_remains_peaceful :
    isPeacefulBullet (by omega : 2 > 0) ring4
      bulletRepairedSuccessor 1 := by
  refine ⟨by decide, 3, by omega, ?_⟩
  dsimp only
  refine ⟨by decide, by decide, ?_, ?_⟩
  · intro k hk
    have hcases : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
    rcases hcases with h | h | h | h <;> subst k <;> decide
  · intro k hk
    have hcases : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
    rcases hcases with h | h | h | h <;> subst k <;> decide

/-! ## Small-ring counterexample to the no-collision bullet repair -/

theorem ringOne : DirectedRing 1 := ⟨by omega⟩

private def loneLeader : AgentState 2 :=
  { state2 0 true with signal_B := 1, shield := true }

def loneLeaderConfig : Fin 1 → AgentState 2 := fun _ => loneLeader

def loneLeaderRepairedPair : AgentState 2 × AgentState 2 :=
  PPLLRepair.ppllSaturatedNoCollision (by omega) 10 loneLeader loneLeader

def loneLeaderSuccessor : Fin 1 → AgentState 2 :=
  PopulationProtocol.step (PPLLRepair.protocol (by omega) 10)
    ringOne loneLeaderConfig 0

theorem loneLeader_repair_fires_live_bullet :
    (loneLeaderSuccessor 0).bullet = 2 ∧
    (loneLeaderSuccessor 0).leader = true ∧
    (loneLeaderSuccessor 0).shield = true ∧
    (loneLeaderSuccessor 0).signal_B = 0 ∧
    (loneLeaderSuccessor 0).label = 0 := by
  decide

/-- The lone initial configuration satisfies the five-field safe schema. The
stable-label condition constrains only offset zero, and the self-edge barrier is
blocked by the leader. -/
theorem loneLeaderConfig_paper_safe :
    PaperSafeConfig (by omega : 2 > 0) ringOne loneLeaderConfig := by
  apply PaperSafeConfig.mk
  · refine ⟨0, by decide, ?_⟩
    intro j _
    apply Fin.ext
    omega
  · intro i hi
    simp [loneLeaderConfig, loneLeader, state2] at hi
  · intro i
    have hi : i = 0 := by apply Fin.ext; omega
    subst i
    dsimp only
    intro _
    decide
  · refine ⟨0, by decide, by decide, ?_⟩
    intro i hi hbound
    omega
  · refine ⟨0, by decide, by decide, ?_, ?_⟩
    · intro k hk
      have hk0 : k = 0 := by omega
      subst k
      decide
    · intro i hi hbound
      omega

/-- For n=1 and ψ=2, the newly fired live bullet cannot satisfy the inclusive
k=0 label-successor clause: its right neighbor is itself, with label 0 rather
than 1. -/
theorem loneLeaderSuccessor_not_peaceful :
    ¬isPeacefulBullet (by omega : 2 > 0) ringOne loneLeaderSuccessor 0 := by
  intro hp
  obtain ⟨_, d, hd, _, _, _, hlabels⟩ := hp
  have hd0 : d = 0 := by omega
  subst d
  have hl := hlabels 0 (by omega)
  dsimp only at hl
  have hm : (⟨((0 : Fin 1).val + 0) % 1, by omega⟩ : Fin 1) = 0 := by
    apply Fin.ext; omega
  have hm' : (⟨((0 : Fin 1).val + 0 + 1) % 1, by omega⟩ : Fin 1) = 0 := by
    apply Fin.ext; omega
  have hmval := congrArg
    (fun x : Fin 1 => (loneLeaderSuccessor x).label.val) hm
  have hmval' := congrArg
    (fun x : Fin 1 => (loneLeaderSuccessor x).label.val) hm'
  have hc : (loneLeaderSuccessor 0).label = 0 := by decide
  have hcv := congrArg Fin.val hc
  have hv := congrArg Fin.val hl
  dsimp only at hcv hv
  omega

theorem loneLeaderSuccessor_not_noNonPeaceful :
    ¬noNonPeacefulBullet (by omega : 2 > 0) ringOne loneLeaderSuccessor := by
  intro h
  exact loneLeaderSuccessor_not_peaceful (h 0 (by decide))

/-- The explicit no-collision candidate does not preserve condition 2 on the
literal arbitrary-size parameter domain. -/
theorem repaired_paperSafe_not_closed_by_lone_bullet :
    ∃ (C C' : Fin 1 → AgentState 2) (e : Fin 1),
      PaperSafeConfig (by omega : 2 > 0) ringOne C ∧
      C' = PopulationProtocol.step (PPLLRepair.protocol (by omega) 10)
        ringOne C e ∧
      ¬PaperSafeConfig (by omega : 2 > 0) ringOne C' := by
  refine ⟨loneLeaderConfig, loneLeaderSuccessor, 0,
    loneLeaderConfig_paper_safe, rfl, ?_⟩
  intro hsafe
  exact loneLeaderSuccessor_not_noNonPeaceful hsafe.no_nonpeaceful_bullet

/-! ## Independent condition-5 counterexample: orphan write command -/

private def writeA0 : AgentState 2 := a0
private def writeA1 : AgentState 2 := a1
private def writeA2 : AgentState 2 := state2 0
private def writeA3 : AgentState 2 :=
  { state2 1 with write := .increment_group }

def writeCounterConfig : Fin 4 → AgentState 2
  | ⟨0, _⟩ => writeA0
  | ⟨1, _⟩ => writeA1
  | ⟨2, _⟩ => writeA2
  | ⟨3, _⟩ => writeA3

private theorem write_counter_unique : hasUniqueLeader 4 writeCounterConfig := by
  refine ⟨0, by decide, ?_⟩
  intro j hj
  rcases fin4_cases j with h | h | h | h <;> subst j
  · rfl
  · simp [writeCounterConfig, writeA1, a1, state2,
      AgentState.isLeader] at hj
  · simp [writeCounterConfig, writeA2, state2,
      AgentState.isLeader] at hj
  · simp [writeCounterConfig, writeA3, state2,
      AgentState.isLeader] at hj

private theorem write_counter_no_bad_bullet :
    noNonPeacefulBullet (by omega : 2 > 0) ring4 writeCounterConfig := by
  intro i hi
  rcases fin4_cases i with h | h | h | h <;> subst i <;>
    simp [writeCounterConfig, writeA0, writeA1, writeA2, writeA3,
      a0, a1, state2] at hi

private theorem write_counter_no_free_barrier :
    noFreeBarrier (by omega : 2 > 0) ring4 writeCounterConfig := by
  intro i
  rcases fin4_cases i with h | h | h | h <;> subst i <;>
    simp [DirectedRing.rightNeighbor, isBarrier, writeCounterConfig,
      writeA0, writeA1, writeA2, writeA3, a0, a1, state2]

private theorem write_counter_no_free_ow :
    noFreeOverwritingSignal (by omega : 2 > 0) ring4
      writeCounterConfig := by
  refine ⟨0, by decide, by decide, ?_⟩
  intro i hi hbound hfree
  obtain ⟨_, haligned⟩ := hfree.1
  obtain ⟨p, hpath, _⟩ := haligned 0 (by omega)
  have hnone : ∀ k : Fin 4, (writeCounterConfig k).path3 = none := by
    intro k
    rcases fin4_cases k with h | h | h | h <;> subst k <;> decide
  rw [hnone] at hpath
  contradiction

private theorem write_counter_stable_id :
    isStableIDSequence (by omega : 2 > 0) ring4 writeCounterConfig := by
  refine ⟨0, by decide, by decide, ?_, ?_⟩
  · intro k hk
    have hcases : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
    rcases hcases with h | h | h | h <;> subst k <;> decide
  · intro i hi hlt
    have hieq : i = 1 := by omega
    subst i
    unfold groupID
    simp [List.range_succ, writeCounterConfig, writeA0, writeA1,
      writeA2, writeA3, a0, a1, state2, trailingZeros]

theorem writeCounterConfig_paper_safe :
    PaperSafeConfig (by omega : 2 > 0) ring4 writeCounterConfig where
  unique_leader := write_counter_unique
  no_nonpeaceful_bullet := write_counter_no_bad_bullet
  no_free_barrier := write_counter_no_free_barrier
  no_free_overwriting_signal := write_counter_no_free_ow
  stable_id_sequence := write_counter_stable_id

theorem writeCounterConfig_inProtocolDomain :
    ∀ i, (writeCounterConfig i).inProtocolDomain 10 := by
  intro i
  rcases fin4_cases i with h | h | h | h <;> subst i <;>
    simp [AgentState.inProtocolDomain, writeCounterConfig, writeA0,
      writeA1, writeA2, writeA3, a0, a1, state2]

theorem writeCounterConfig_checkBoundarySafe :
    CheckBoundarySafe (by omega : 2 > 0) 10 ring4 writeCounterConfig := by
  intro e
  rcases fin4_cases e with h | h | h | h <;> subst e <;> decide

/-- T8's terminal increment command has no local path3 support and is rejected
by the first operational write-provenance layer. -/
theorem writeCounter_orphan_increment_not_supported :
    ¬PPLLWriteProvenance.IncrementCommandSupported writeA3 := by
  intro h
  obtain ⟨p, hpath, _⟩ := h rfl
  simp [writeA3, state2] at hpath

def writeCounterPair : AgentState 2 × AgentState 2 :=
  ppll (by omega) 10 writeA2 writeA3

def writeCounterSuccessor : Fin 4 → AgentState 2 := fun k =>
  if k = (2 : Fin 4) then writeCounterPair.1
  else if k = (3 : Fin 4) then writeCounterPair.2
  else writeCounterConfig k

/-- The orphan command is activated at terminal label 1 and increments the
stable non-leader group's low bit. -/
theorem write_counter_changes_stable_group_id :
    groupID ring4.hn writeCounterSuccessor 2 = 1 := by
  decide

/-- The exact overwriting boundary obligation detects the orphan command. -/
theorem writeCounterConfig_not_groupIDBoundarySafe :
    ¬GroupIDBoundarySafe (by omega : 2 > 0) 10 ring4
      writeCounterConfig := by
  intro hsafe
  have hstep := hsafe 2 2
  have hsucc : ppllStep (by omega : 2 > 0) 10 ring4 writeCounterConfig 2 =
      writeCounterSuccessor := by
    funext k
    rfl
  rw [hsucc] at hstep
  have hin : groupID ring4.hn writeCounterConfig 2 = 0 := by decide
  have hout := write_counter_changes_stable_group_id
  rw [hin, hout] at hstep
  contradiction

theorem writeCounterSuccessor_not_stable :
    ¬isStableIDSequence (by omega : 2 > 0) ring4
      writeCounterSuccessor := by
  intro hstable
  obtain ⟨lp, hlp, _, _, hgroups⟩ := hstable
  have hlpeq : lp = 0 := by
    rcases fin4_cases lp with h | h | h | h <;> subst lp
    · rfl
    · have hf : (writeCounterSuccessor 1).isLeader = false := by decide
      have himpossible : false = true := hf.symm.trans hlp
      exact Bool.noConfusion himpossible
    · have hf : (writeCounterSuccessor 2).isLeader = false := by decide
      have himpossible : false = true := hf.symm.trans hlp
      exact Bool.noConfusion himpossible
    · have hf : (writeCounterSuccessor 3).isLeader = false := by decide
      have himpossible : false = true := hf.symm.trans hlp
      exact Bool.noConfusion himpossible
  subst lp
  have hg := hgroups 1 (by omega) (by decide)
  dsimp only at hg
  let gs : Fin 4 := ⟨((0 : Fin 4).val + 1 * 2) % 4,
    Nat.mod_lt _ ring4.hn⟩
  change groupID ring4.hn writeCounterSuccessor gs = trailingZeros 1 at hg
  have hgseq : gs = 2 := by apply Fin.ext; decide
  rw [hgseq] at hg
  have hgid := write_counter_changes_stable_group_id
  rw [hgid] at hg
  simp [trailingZeros] at hg

/-- Under the current aligned-path3 interpretation of condition 4, an orphan
write command independently destroys condition 5 in one step. -/
theorem paperSafe_not_closed_by_orphan_write :
    ∃ (C C' : Fin 4 → AgentState 2) (e : Fin 4),
      PaperSafeConfig (by omega : 2 > 0) ring4 C ∧
      C' = PopulationProtocol.step counterProtocol ring4 C e ∧
      ¬PaperSafeConfig (by omega : 2 > 0) ring4 C' := by
  refine ⟨writeCounterConfig, writeCounterSuccessor, 2,
    writeCounterConfig_paper_safe, ?_, ?_⟩
  · funext k
    rfl
  · intro hsafe
    exact writeCounterSuccessor_not_stable hsafe.stable_id_sequence

private def orphanWriteTest (C : Fin 4 → AgentState 2) : Bool :=
  (C 3).bit

theorem orphan_write_bad_schedule_count :
    hitCount ring4 (ppll (by omega : 2 > 0) 10)
      orphanWriteTest writeCounterConfig 1 = 1 := by
  decide

theorem orphan_write_bad_event_probability :
    hitProbability ring4 (ppll (by omega : 2 > 0) 10)
      orphanWriteTest writeCounterConfig 1 = (1 : Rat) / 4 := by
  unfold hitProbability
  rw [orphan_write_bad_schedule_count, allSchedules_length]
  simp only [Nat.pow_succ, Nat.pow_zero, Nat.one_mul, Rat.natCast_ofNat]

/-! ## Concrete suppression-profile counterexample -/

theorem ringTwo : DirectedRing 2 := ⟨by omega⟩

def suppressionCounterConfig : Fin 2 → AgentState 2
  | ⟨0, _⟩ => state2 0 true
  | ⟨1, _⟩ => state2 1

private def suppressionTest (C : Fin 2 → AgentState 2) : Bool :=
  (C 0).reset_cmd && (C 1).reset_cmd

private theorem suppressionTest_decides (C : Fin 2 → AgentState 2) :
    suppressionTest C = true ↔ isSuppressed ringTwo C := by
  constructor
  · intro h i
    have hi : i = 0 ∨ i = 1 := by omega
    simp [suppressionTest] at h
    rcases hi with hi | hi <;> subst i
    · exact h.1
    · exact h.2
  · intro h
    simp [suppressionTest, h 0, h 1]

/-- Concrete version of the phase-4 metadata at n=2,c=1: six steps and
claimed failure at most 1/2. -/
def concreteSuppressionProfile : ReachSpec ringTwo
    (PPLLRepair.ppllSaturatedNoCollision (ψ := 2) (by omega) 10) where
  Pre := hasLeader 2
  Post := isSuppressed ringTwo
  steps := fun _ => 6
  failProb := fun _ => (1 : Rat) / 2

private theorem suppressionCounterConfig_hasLeader :
    hasLeader 2 suppressionCounterConfig := by
  exact ⟨0, by decide⟩

set_option maxRecDepth 4096 in
theorem suppression_bad_schedule_count :
    hitCount ringTwo (PPLLRepair.ppllSaturatedNoCollision (by omega) 10)
      suppressionTest suppressionCounterConfig 6 = 0 := by
  decide

theorem suppression_hit_probability_zero :
    hitProbability ringTwo (PPLLRepair.ppllSaturatedNoCollision (by omega) 10)
      suppressionTest suppressionCounterConfig 6 = 0 := by
  unfold hitProbability
  rw [suppression_bad_schedule_count]
  rw [Rat.div_def]
  change (0 : Rat) * ((allSchedules 2 6).length : Rat)⁻¹ = 0
  rw [Rat.zero_mul]

/-- The literal `isSuppressed := ∀i, reset_cmd=true` phase target is not reached
at all in the claimed n=2,c=1 horizon from this concrete leader configuration.
Thus the analogous concrete phase profile is semantically invalid. -/
theorem concreteSuppressionProfile_not_semantically_valid :
    ¬concreteSuppressionProfile.SemanticallyValid suppressionTest := by
  intro h
  have hbound := h.2 suppressionCounterConfig suppressionCounterConfig_hasLeader
  simp only [concreteSuppressionProfile] at hbound
  rw [suppression_hit_probability_zero] at hbound
  have hnot : ¬((1 : Rat) - (1 : Rat) / 2 ≤ 0) := by
    intro hle
    have h2 : (0 : Rat) < 2 := by rw [Rat.lt_iff]; decide
    have h12 : (1 : Rat) < 2 := by rw [Rat.lt_iff]; decide
    have hinv : (0 : Rat) < (2 : Rat)⁻¹ := Rat.inv_pos.mpr h2
    have hhalf : (1 : Rat) / 2 < 1 := by
      have hm := Rat.mul_lt_mul_of_pos_right h12 hinv
      have h2ne : (2 : Rat) ≠ 0 := (Rat.ne_of_lt h2).symm
      rw [Rat.one_mul, Rat.mul_inv_cancel 2 h2ne] at hm
      rw [Rat.div_def, Rat.one_mul]
      exact hm
    have hadd : ((1 : Rat) - (1 : Rat) / 2) + (1 : Rat) / 2 ≤
        0 + (1 : Rat) / 2 := Rat.add_le_add_right.mpr hle
    rw [Rat.sub_eq_add_neg, Rat.add_assoc, Rat.neg_add_cancel,
      Rat.add_zero, Rat.zero_add] at hadd
    exact (Rat.not_le.mpr hhalf) hadd
  exact hnot hbound

/-! ## Exact probability of the witnessed bad interaction -/

def leadersAtZeroAndTwo (C : Fin 4 → AgentState 2) : Bool :=
  (C 0).leader && (C 2).leader

theorem counter_bad_schedule_count :
    hitCount ring4 (ppll (by omega : 2 > 0) 10)
      leadersAtZeroAndTwo counterConfig 1 = 1 := by
  decide

/-- Under one uniform random edge interaction, the explicit two-leader bad
event occurs with probability exactly 1/4 (edge 2 of four). -/
theorem counter_bad_event_probability :
    hitProbability ring4 (ppll (by omega : 2 > 0) 10)
      leadersAtZeroAndTwo counterConfig 1 = (1 : Rat) / 4 := by
  unfold hitProbability
  rw [counter_bad_schedule_count, allSchedules_length]
  simp only [Nat.pow_succ, Nat.pow_zero, Nat.one_mul, Rat.natCast_ofNat]

/-- A one-step profile for the concrete bad event. Unlike the historical phase
profiles, this metadata will be paired with an actual semantic proof below. -/
def counterBadProfile :
    ReachSpec ring4 (ppll (by omega : 2 > 0) 10) where
  Pre := fun C => C = counterConfig
  Post := fun C => leadersAtZeroAndTwo C = true
  steps := fun _ => 1
  failProb := fun _ => (3 : Rat) / 4

/-- The counterexample is also the first nontrivial protocol-specific profile
certified against the exact uniform scheduler: from the designated pre-state,
the two-leader event is hit within one step with probability at least `1-3/4`.
This is a bad-event certificate, not a convergence theorem. -/
theorem counterBadProfile_semantically_valid :
    counterBadProfile.SemanticallyValid leadersAtZeroAndTwo := by
  refine ⟨fun _ => Iff.rfl, ?_⟩
  intro C hC
  change C = counterConfig at hC
  subst C
  change (1 : Rat) - (3 : Rat) / 4 ≤
    hitProbability ring4 (ppll (by omega : 2 > 0) 10)
      leadersAtZeroAndTwo counterConfig 1
  rw [counter_bad_event_probability]
  rw [Rat.sub_right_le_iff_le_add]
  have hfourpos : (0 : Rat) < 4 := by
    rw [Rat.lt_iff]
    decide
  apply Rat.le_of_mul_le_mul_right (c := (4 : Rat))
  · rw [Rat.one_mul, Rat.add_mul,
      Rat.div_mul_cancel (Rat.ne_of_lt hfourpos).symm,
      Rat.div_mul_cancel (Rat.ne_of_lt hfourpos).symm]
    have hadd : (1 : Rat) + 3 = 4 := by
      rw [← Rat.natCast_ofNat (a := 1), ← Rat.natCast_ofNat (a := 3),
        ← Rat.natCast_add]
      rw [show (1 + 3 : Nat) = 4 by decide, Rat.natCast_ofNat]
    rw [hadd]
    exact Rat.le_refl
  · exact hfourpos

/-- Bundled semantic certificate for model-checking clients. -/
def certifiedCounterBadProfile :
    CertifiedReachSpec ring4 (ppll (by omega : 2 > 0) 10) where
  spec := counterBadProfile
  postTest := leadersAtZeroAndTwo
  valid := counterBadProfile_semantically_valid

end PPLLCounterexample
