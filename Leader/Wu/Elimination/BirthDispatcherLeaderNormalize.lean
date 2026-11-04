import Leader.Wu.Elimination.BirthDispatcherObserver
import Leader.Wu.Elimination.SinkTwoGapEpochSuccessor

/-!
# Leader-label normalization seam for the mixed birth dispatcher

Normalization is applied only to the two computed metadata endpoints, after
metadata/reification/expiry and before the existing newborn initialization and
final collision/K2 stage.  The original endpoints are still passed to
`finalPhysical`, so newborn detection remains the actual old/computed leader-bit
test.  No DONE guard or stationary-writer postcondition is added here.
-/

namespace K2BirthLeaderNormalize

open PPLL PPLLDomain PPLLResearchFormulation
  PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
  LDSinkBoundedKernel LDSinkKernelC LDSinkTwoGapEpochSuccessor
  ExpiringK2Projection K2OutputSafety

set_option autoImplicit false
set_option pp.structureInstances false

variable {ψ κ τ n : Nat}

/-- The one physical field changed by normalization. -/
def putLabel (q : ExpiringAgentState ψ κ τ) (a : Fin ψ) :
    ExpiringAgentState ψ κ τ :=
  { q with core := { q.core with core := { q.core.core with label := a } } }

@[simp] theorem putLabel_twice (q : ExpiringAgentState ψ κ τ) (a b : Fin ψ) :
    putLabel (putLabel q a) b = putLabel q b := rfl

@[simp] theorem putLabel_self (q : ExpiringAgentState ψ κ τ) :
    putLabel q q.core.core.label = q := by
  cases q with
  | mk auth stall =>
    cases auth with
    | mk core crossed =>
      cases core <;> rfl

/-- Label replacement is invisible to the four-field K2 observation. -/
theorem observe_putLabel (q : ExpiringAgentState ψ κ τ) (a : Fin ψ) :
    observeCell (putLabel q a) = observeCell q := rfl

/-- Normalize exactly a current leader. Followers retain their current label. -/
def normalizeLeader (hψ : 0 < ψ) (q : ExpiringAgentState ψ κ τ) :
    ExpiringAgentState ψ κ τ :=
  if q.core.core.leader = true then putLabel q ⟨0, hψ⟩ else q

/-- Exact all-other-fields frame: restoring the old label recovers the whole
expiring record, including permit and stall. -/
theorem normalizeLeader_field_frame (hψ : 0 < ψ) (q : ExpiringAgentState ψ κ τ) :
    putLabel (normalizeLeader hψ q) q.core.core.label = q := by
  unfold normalizeLeader
  split
  · rw [putLabel_twice, putLabel_self]
  · exact putLabel_self q

theorem normalizeLeader_leader (hψ : 0 < ψ) (q : ExpiringAgentState ψ κ τ) :
    (normalizeLeader hψ q).core.core.leader = q.core.core.leader := by
  unfold normalizeLeader
  split <;> rfl

theorem normalizeLeader_observation (hψ : 0 < ψ) (q : ExpiringAgentState ψ κ τ) :
    observeCell (normalizeLeader hψ q) = observeCell q := by
  unfold normalizeLeader
  split
  · exact observe_putLabel q _
  · rfl

/-- This is phrased on the normalized output, so it covers both an existing
leader and a newly-computed leader. -/
theorem normalizeLeader_label_zero (hψ : 0 < ψ) (q : ExpiringAgentState ψ κ τ) :
    (normalizeLeader hψ q).core.core.leader = true →
      (normalizeLeader hψ q).core.core.label = ⟨0, hψ⟩ := by
  unfold normalizeLeader
  split
  · intro _
    rfl
  · rename_i hn
    intro hl
    exact (hn hl).elim

/-- The finite bounded representation remains in its declared numeric domain. -/
theorem normalizeLeader_domain (hψ : 0 < ψ) (q : ExpiringAgentState ψ κ τ) :
    (normalizeLeader hψ q).core.core.erase.inProtocolDomain κ :=
  (normalizeLeader hψ q).core.core.erase_inProtocolDomain

/-- The accepted metadata/expiry output, then endpoint-local leader normalization. -/
def normalizedMetadata (hψ : 0 < ψ) (l r : ExpiringAgentState ψ κ τ) :
    ExpiringAgentState ψ κ τ × ExpiringAgentState ψ κ τ :=
  let q := K2BirthDispatcher.metadata hψ l r
  (normalizeLeader hψ q.1, normalizeLeader hψ q.2)

theorem normalizedMetadata_raw_leaders (hψ : 0 < ψ)
    (l r : ExpiringAgentState ψ κ τ) :
    (normalizedMetadata hψ l r).1.core.core.leader =
        (K2BirthDispatcher.metadata hψ l r).1.core.core.leader ∧
      (normalizedMetadata hψ l r).2.core.core.leader =
        (K2BirthDispatcher.metadata hψ l r).2.core.core.leader := by
  unfold normalizedMetadata
  dsimp only
  exact ⟨normalizeLeader_leader hψ _, normalizeLeader_leader hψ _⟩

/-- Normalization changes no leader/bullet/shield/signal observation. -/
theorem normalizedMetadata_observation_raw (hψ : 0 < ψ)
    (l r : ExpiringAgentState ψ κ τ) :
    (observeCell (normalizedMetadata hψ l r).1,
      observeCell (normalizedMetadata hψ l r).2) =
    (observeCell (K2BirthDispatcher.metadata hψ l r).1,
      observeCell (K2BirthDispatcher.metadata hψ l r).2) := by
  unfold normalizedMetadata
  dsimp only
  rw [normalizeLeader_observation, normalizeLeader_observation]

/-- The baseline computed no-birth frame therefore survives normalization. -/
theorem normalizedMetadata_signal_of_no_birth (hψ : 0 < ψ)
    (l r : ExpiringAgentState ψ κ τ)
    (hn : K2BirthDispatcher.birthEvent hψ l r = false) :
    (observeCell (normalizedMetadata hψ l r).1,
      observeCell (normalizedMetadata hψ l r).2) =
      (observeCell l, observeCell r) :=
  (normalizedMetadata_observation_raw hψ l r).trans
    (K2BirthDispatcher.metadata_signal_of_no_birth hψ l r hn)

theorem normalizedMetadata_leader_labels_zero (hψ : 0 < ψ)
    (l r : ExpiringAgentState ψ κ τ) :
    ((normalizedMetadata hψ l r).1.core.core.leader = true →
      (normalizedMetadata hψ l r).1.core.core.label = ⟨0, hψ⟩) ∧
    ((normalizedMetadata hψ l r).2.core.core.leader = true →
      (normalizedMetadata hψ l r).2.core.core.label = ⟨0, hψ⟩) := by
  unfold normalizedMetadata
  dsimp only
  exact ⟨normalizeLeader_label_zero hψ _, normalizeLeader_label_zero hψ _⟩

/-- Newborn comparison still uses the original endpoint and the computed leader
bit; normalization cannot alter that Boolean. -/
theorem newborn_normalize (hψ : 0 < ψ) (old q : ExpiringAgentState ψ κ τ) :
    K2BirthDispatcher.newborn old (normalizeLeader hψ q) =
      K2BirthDispatcher.newborn old q := by
  unfold K2BirthDispatcher.newborn
  rw [normalizeLeader_leader]

theorem normalized_birth_event (hψ : 0 < ψ)
    (l r : ExpiringAgentState ψ κ τ) :
    let q := normalizedMetadata hψ l r
    (K2BirthDispatcher.newborn l q.1 ||
      K2BirthDispatcher.newborn r q.2) =
      K2BirthDispatcher.birthEvent hψ l r := by
  unfold normalizedMetadata K2BirthDispatcher.birthEvent
  dsimp only
  rw [newborn_normalize, newborn_normalize]

/-- Complete row: accepted metadata/expiry, normalization, then the unchanged
newborn initialization and final collision/K2 stage. -/
def row (hψ : 0 < ψ) (l r : ExpiringAgentState ψ κ τ) :
    ExpiringAgentState ψ κ τ × ExpiringAgentState ψ κ τ :=
  let q := normalizedMetadata hψ l r
  K2BirthDispatcher.finalPhysical hψ l r q.1 q.2

/-- Complete-output frame is intentionally against normalized metadata. -/
theorem row_metadata_frame (hψ : 0 < ψ) (l r : ExpiringAgentState ψ κ τ) :
    putSignals (row hψ l r).1 (observeCell (normalizedMetadata hψ l r).1) =
        (normalizedMetadata hψ l r).1 ∧
      putSignals (row hψ l r).2 (observeCell (normalizedMetadata hψ l r).2) =
        (normalizedMetadata hψ l r).2 := by
  unfold row
  dsimp only
  exact K2BirthDispatcher.finalPhysical_frame hψ l r _ _

/-- `nonK2` retains labels, hence this frame also compares only with normalized
metadata, never with the raw metadata output. -/
theorem row_metadata_nonK2 (hψ : 0 < ψ) (l r : ExpiringAgentState ψ κ τ) :
    nonK2 (row hψ l r).1 = nonK2 (normalizedMetadata hψ l r).1 ∧
      nonK2 (row hψ l r).2 = nonK2 (normalizedMetadata hψ l r).2 := by
  unfold row
  dsimp only
  exact K2BirthDispatcher.finalPhysical_nonK2 hψ l r _ _

/-- In particular, the physical tail retains the normalized labels exactly. -/
theorem row_labels_metadata (hψ : 0 < ψ) (l r : ExpiringAgentState ψ κ τ) :
    (row hψ l r).1.core.core.label =
        (normalizedMetadata hψ l r).1.core.core.label ∧
      (row hψ l r).2.core.core.label =
        (normalizedMetadata hψ l r).2.core.core.label := by
  have h := row_metadata_nonK2 hψ l r
  have hl := congrArg (fun q : ExpiringAgentState ψ κ τ => q.core.core.label) h.1
  have hr := congrArg (fun q : ExpiringAgentState ψ κ τ => q.core.core.label) h.2
  change (row hψ l r).1.core.core.label =
    (normalizedMetadata hψ l r).1.core.core.label at hl
  change (row hψ l r).2.core.core.label =
    (normalizedMetadata hψ l r).2.core.core.label at hr
  exact ⟨hl, hr⟩

/-- The existing K2 row cannot create a leader on an endpoint that entered it
as a follower. -/
private theorem expiringK2_no_new_leaders (hψ : 0 < ψ)
    (l r : ExpiringAgentState ψ κ τ) :
    ((ExpiringK2Projection.row hψ l r).1.core.core.leader = true →
      l.core.core.leader = true) ∧
    ((ExpiringK2Projection.row hψ l r).2.core.core.leader = true →
      r.core.core.leader = true) := by
  have ho := ExpiringK2Projection.observe_row hψ l r
  have hk := LDSinkTwoGapEpochSuccessor.kernelC_no_leader_creation
    (by decide : 0 < 1) (observeCell l) (observeCell r)
  constructor
  · intro hout
    cases hl : l.core.core.leader with
    | false =>
      have hlf : (observeCell l).leader = false := hl
      have hf := hk.1 hlf
      have he := congrArg (fun q : AgentState 1 × AgentState 1 => q.1.leader) ho
      change (ExpiringK2Projection.row hψ l r).1.core.core.leader =
        (sinkKernelC (by decide) (observeCell l) (observeCell r)).1.leader at he
      have hz := he.trans hf
      simp_all
    | true => rfl
  · intro hout
    cases hr : r.core.core.leader with
    | false =>
      have hrf : (observeCell r).leader = false := hr
      have hf := hk.2 hrf
      have he := congrArg (fun q : AgentState 1 × AgentState 1 => q.2.leader) ho
      change (ExpiringK2Projection.row hψ l r).2.core.core.leader =
        (sinkKernelC (by decide) (observeCell l) (observeCell r)).2.leader at he
      have hz := he.trans hf
      simp_all
    | true => rfl

private theorem collisionRow_no_new_leaders (hψ : 0 < ψ)
    (l r : ExpiringAgentState ψ κ τ) :
    ((K2BirthDispatcher.collisionRow hψ l r).1.core.core.leader = true →
      l.core.core.leader = true) ∧
    ((K2BirthDispatcher.collisionRow hψ l r).2.core.core.leader = true →
      r.core.core.leader = true) := by
  by_cases hb : l.core.core.leader = true ∧ r.core.core.leader = true
  · exact ⟨fun _ => hb.1, fun _ => hb.2⟩
  · rw [K2BirthDispatcher.collisionRow_of_not_both hψ l r hb]
    exact expiringK2_no_new_leaders hψ l r

private theorem finalPhysical_no_new_leaders (hψ : 0 < ψ)
    (oldL oldR metaL metaR : ExpiringAgentState ψ κ τ) :
    ((K2BirthDispatcher.finalPhysical hψ oldL oldR metaL metaR).1.core.core.leader = true →
      metaL.core.core.leader = true) ∧
    ((K2BirthDispatcher.finalPhysical hψ oldL oldR metaL metaR).2.core.core.leader = true →
      metaR.core.core.leader = true) := by
  unfold K2BirthDispatcher.finalPhysical
  have h := collisionRow_no_new_leaders hψ
    (K2BirthDispatcher.initializeNewborn oldL metaL)
    (K2BirthDispatcher.initializeNewborn oldR metaR)
  exact ⟨fun hout => (K2BirthDispatcher.initializeNewborn_leader oldL metaL).symm.trans (h.1 hout),
    fun hout => (K2BirthDispatcher.initializeNewborn_leader oldR metaR).symm.trans (h.2 hout)⟩

/-- Every leader surviving the complete touched row has the physical label zero.
This includes old leaders and leaders created by the metadata prefix. -/
theorem row_leader_labels_zero (hψ : 0 < ψ)
    (l r : ExpiringAgentState ψ κ τ) :
    ((row hψ l r).1.core.core.leader = true →
      (row hψ l r).1.core.core.label = ⟨0, hψ⟩) ∧
    ((row hψ l r).2.core.core.leader = true →
      (row hψ l r).2.core.core.label = ⟨0, hψ⟩) := by
  have hs :
      ((row hψ l r).1.core.core.leader = true →
        (normalizedMetadata hψ l r).1.core.core.leader = true) ∧
      ((row hψ l r).2.core.core.leader = true →
        (normalizedMetadata hψ l r).2.core.core.leader = true) := by
    unfold row
    dsimp only
    exact finalPhysical_no_new_leaders hψ l r _ _
  have hz := normalizedMetadata_leader_labels_zero hψ l r
  have hf := row_labels_metadata hψ l r
  exact ⟨fun h => hf.1.trans (hz.1 (hs.1 h)),
    fun h => hf.2.trans (hz.2 (hs.2 h))⟩

/-- Actual computed `birthEvent = false` gives the same collision/K2
four-signal row as the accepted dispatcher. -/
theorem observe_row_of_no_birth (hψ : 0 < ψ)
    (l r : ExpiringAgentState ψ κ τ)
    (hn : K2BirthDispatcher.birthEvent hψ l r = false) :
    (observeCell (row hψ l r).1, observeCell (row hψ l r).2) =
      K2BirthDispatcher.shadowRow (observeCell l) (observeCell r) := by
  have hraw :
      K2BirthDispatcher.newborn l (K2BirthDispatcher.metadata hψ l r).1 = false ∧
      K2BirthDispatcher.newborn r (K2BirthDispatcher.metadata hψ l r).2 = false := by
    simpa only [K2BirthDispatcher.birthEvent, Bool.or_eq_false_iff] using hn
  have hnorm :
      K2BirthDispatcher.newborn l (normalizedMetadata hψ l r).1 = false ∧
      K2BirthDispatcher.newborn r (normalizedMetadata hψ l r).2 = false := by
    unfold normalizedMetadata
    dsimp only
    constructor
    · rw [newborn_normalize]
      exact hraw.1
    · rw [newborn_normalize]
      exact hraw.2
  unfold row
  dsimp only
  rw [K2BirthDispatcher.finalPhysical_of_no_birth hψ l r _ _ hnorm.1 hnorm.2]
  exact (K2BirthDispatcher.observe_collisionRow hψ _ _).trans
    (congrArg (fun q : AgentState 1 × AgentState 1 =>
      K2BirthDispatcher.shadowRow q.1 q.2)
      (normalizedMetadata_signal_of_no_birth hψ l r hn))

/-- Unconditional range closure on the same finite expiring carrier. -/
theorem row_domain (hψ : 0 < ψ) (l r : ExpiringAgentState ψ κ τ) :
    (row hψ l r).1.core.core.erase.inProtocolDomain κ ∧
      (row hψ l r).2.core.core.erase.inProtocolDomain κ :=
  ⟨(row hψ l r).1.core.core.erase_inProtocolDomain,
    (row hψ l r).2.core.core.erase_inProtocolDomain⟩

def protocol (hψ : 0 < ψ) (κ τ : Nat) : PopulationProtocol where
  Q := ExpiringAgentState ψ κ τ
  Y := Bool
  transition := row hψ
  output := fun q => q.core.core.leader

def step (hψ : 0 < ψ) (ring : DirectedRing n)
    (C : Fin n → ExpiringAgentState ψ κ τ) (e : Fin n) :
    Fin n → ExpiringAgentState ψ κ τ :=
  (protocol hψ κ τ).step ring C e

/-- Same exhaustive finite carrier certificate; normalization adds no state. -/
def stateCertificate (hψ : 0 < ψ) (κ τ : Nat) :
    ExhaustiveList (protocol hψ κ τ).Q :=
  K2BirthDispatcher.stateCertificate hψ κ τ

theorem finite_state_bound (hψ : 0 < ψ) (κ τ : Nat) :
    Function.Injective (stateCertificate hψ κ τ).decode ∧
    Function.Surjective (stateCertificate hψ κ τ).decode ∧
    (stateCertificate hψ κ τ).values.length ≤ ExpiringK2Projection.localBound ψ κ τ :=
  K2BirthDispatcher.finite_state_bound hψ κ τ

theorem observe_step_of_no_birth (hψ : 0 < ψ) (ring : DirectedRing n)
    (C : Fin n → ExpiringAgentState ψ κ τ) (e : Fin n)
    (hn : K2BirthDispatcher.birthEvent hψ (C e) (C (ring.rightNeighbor e)) = false) :
    ExpiringK2Projection.observe (step hψ ring C e) =
      K2BirthDispatcher.shadowStep ring (ExpiringK2Projection.observe C) e := by
  have hq := observe_row_of_no_birth hψ (C e) (C (ring.rightNeighbor e)) hn
  funext i
  simp only [ExpiringK2Projection.observe, step, PopulationProtocol.step, protocol,
    K2BirthDispatcher.shadowStep, updatePair]
  split
  · exact congrArg Prod.fst hq
  · split
    · exact congrArg Prod.snd hq
    · rfl

/-- Proof-side condition on the actual normalized mixed execution. -/
def NoBirthAlong (hψ : 0 < ψ) (ring : DirectedRing n)
    (C : Fin n → ExpiringAgentState ψ κ τ) : List (Fin n) → Prop
  | [] => True
  | e :: es =>
      K2BirthDispatcher.birthEvent hψ (C e) (C (ring.rightNeighbor e)) = false ∧
      NoBirthAlong hψ ring (step hψ ring C e) es

theorem observe_run_of_no_birth (hψ : 0 < ψ) (ring : DirectedRing n)
    (C : Fin n → ExpiringAgentState ψ κ τ) (es : List (Fin n))
    (hn : NoBirthAlong hψ ring C es) :
    ExpiringK2Projection.observe (run (step hψ ring) C es) =
      run (K2BirthDispatcher.shadowStep ring) (ExpiringK2Projection.observe C) es := by
  induction es generalizing C with
  | nil => rfl
  | cons e es ih =>
    simpa only [run, observe_step_of_no_birth hψ ring C e hn.1] using
      ih (step hψ ring C e) hn.2

/-- Same scheduler word and supplied actual UCell observer, with no fabricated
controller or physical embedding. -/
theorem same_word_adjacent (hψ : 0 < ψ) (ring : DirectedRing n)
    (C : Fin n → ExpiringAgentState ψ κ τ)
    (D : Fin n → StateBoundUnifiedCell.UCell ψ κ) (es : List (Fin n))
    (h0 : ExpiringK2Projection.observe C = LabelFreeElimination.observe D)
    (hn : NoBirthAlong hψ ring C es) :
    ExpiringK2Projection.observe (run (step hψ ring) C es) =
      LabelFreeElimination.observe
        (run (AdjacentLeaderElimination.step hψ ring) D es) := by
  rw [observe_run_of_no_birth hψ ring C es hn,
    K2BirthDispatcher.adjacent_observe_run hψ ring D es, h0]

/-- Actual global premise needed for untouched sites.  A single scheduled edge
never claims to normalize arbitrary remote old leaders. -/
def LeadersZero (hψ : 0 < ψ)
    (C : Fin n → ExpiringAgentState ψ κ τ) : Prop :=
  ∀ i, (C i).core.core.leader = true → (C i).core.core.label = ⟨0, hψ⟩

theorem step_left (hψ : 0 < ψ) (ring : DirectedRing n)
    (C : Fin n → ExpiringAgentState ψ κ τ) (e : Fin n) :
    step hψ ring C e e = (row hψ (C e) (C (ring.rightNeighbor e))).1 := by
  simp only [step, PopulationProtocol.step, protocol, if_true]

theorem step_right (hψ : 0 < ψ) (ring : DirectedRing n)
    (C : Fin n → ExpiringAgentState ψ κ τ) (e : Fin n)
    (hne : ring.rightNeighbor e ≠ e) :
    step hψ ring C e (ring.rightNeighbor e) =
      (row hψ (C e) (C (ring.rightNeighbor e))).2 := by
  simp only [step, PopulationProtocol.step, protocol, if_neg hne, if_true]

theorem step_other (hψ : 0 < ψ) (ring : DirectedRing n)
    (C : Fin n → ExpiringAgentState ψ κ τ) (e i : Fin n)
    (hi : i ≠ e) (hj : i ≠ ring.rightNeighbor e) :
    step hψ ring C e i = C i := by
  simp only [step, PopulationProtocol.step, protocol, if_neg hi, if_neg hj]

/-- Global zero-label-leader closure, using the real global precondition exactly
where an untouched old leader needs it. -/
theorem leadersZero_step (hψ : 0 < ψ) (ring : DirectedRing n)
    (C : Fin n → ExpiringAgentState ψ κ τ) (e : Fin n)
    (hC : LeadersZero hψ C) : LeadersZero hψ (step hψ ring C e) := by
  intro i hi
  by_cases he : i = e
  · subst i
    rw [step_left hψ ring C e] at hi ⊢
    exact (row_leader_labels_zero hψ (C e) (C (ring.rightNeighbor e))).1 hi
  · by_cases hr : i = ring.rightNeighbor e
    · subst i
      rw [step_right hψ ring C e he] at hi ⊢
      exact (row_leader_labels_zero hψ (C e) (C (ring.rightNeighbor e))).2 hi
    · rw [step_other hψ ring C e i he hr] at hi ⊢
      exact hC i hi

theorem leadersZero_run (hψ : 0 < ψ) (ring : DirectedRing n)
    (C : Fin n → ExpiringAgentState ψ κ τ) (es : List (Fin n))
    (hC : LeadersZero hψ C) : LeadersZero hψ (run (step hψ ring) C es) := by
  induction es generalizing C with
  | nil => simpa only [LDSinkBoundedKernel.run] using hC
  | cons e es ih =>
    simp only [run]
    exact ih (step hψ ring C e) (leadersZero_step hψ ring C e hC)

/-- Alias convention remains the actual population-protocol left-output
priority. -/
theorem step_alias (hψ : 0 < ψ) (ring : DirectedRing n)
    (C : Fin n → ExpiringAgentState ψ κ τ) (e : Fin n)
    (ha : ring.rightNeighbor e = e) :
    step hψ ring C e e = (row hψ (C e) (C e)).1 := by
  simp only [step, PopulationProtocol.step, protocol, ha, if_true]

/-- The singleton alias still really deletes its sole leader, and because that
same touched metadata endpoint was normalized first, the retained physical
label is genuinely zero as well. -/
theorem singleton_leader_deleted_realzero (hψ : 0 < ψ)
    (ring : DirectedRing 1) (C : Fin 1 → ExpiringAgentState ψ κ τ)
    (hl : (C 0).core.core.leader = true) :
    (step hψ ring C 0 0).core.core.leader = false ∧
      (step hψ ring C 0 0).core.core.label = ⟨0, hψ⟩ := by
  have ha : ring.rightNeighbor (0 : Fin 1) = 0 := Subsingleton.elim _ _
  have hraw := K2BirthDispatcher.metadata_existing_leaders hψ (C 0) (C 0)
  have hml := normalizedMetadata_raw_leaders hψ (C 0) (C 0)
  have hm :
      (normalizedMetadata hψ (C 0) (C 0)).1.core.core.leader = true ∧
      (normalizedMetadata hψ (C 0) (C 0)).2.core.core.leader = true :=
    ⟨hml.1.trans (hraw.1 hl), hml.2.trans (hraw.2 hl)⟩
  have hil :
      (K2BirthDispatcher.initializeNewborn (C 0)
        (normalizedMetadata hψ (C 0) (C 0)).1).core.core.leader = true :=
    (K2BirthDispatcher.initializeNewborn_leader _ _).trans hm.1
  have hir :
      (K2BirthDispatcher.initializeNewborn (C 0)
        (normalizedMetadata hψ (C 0) (C 0)).2).core.core.leader = true :=
    (K2BirthDispatcher.initializeNewborn_leader _ _).trans hm.2
  have hc := K2BirthDispatcher.collisionRow_of_both hψ
    (K2BirthDispatcher.initializeNewborn (C 0)
      (normalizedMetadata hψ (C 0) (C 0)).1)
    (K2BirthDispatcher.initializeNewborn (C 0)
      (normalizedMetadata hψ (C 0) (C 0)).2) hil hir
  have hdel : (row hψ (C 0) (C 0)).1.core.core.leader = false := by
    simpa only [row, K2BirthDispatcher.finalPhysical] using hc.1
  have hz := normalizedMetadata_leader_labels_zero hψ (C 0) (C 0)
  have hlabel : (row hψ (C 0) (C 0)).1.core.core.label = ⟨0, hψ⟩ :=
    (row_labels_metadata hψ (C 0) (C 0)).1.trans (hz.1 hm.1)
  rw [step_alias hψ ring C 0 ha]
  exact ⟨hdel, hlabel⟩

end K2BirthLeaderNormalize
