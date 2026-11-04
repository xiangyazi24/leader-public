import Leader.Wu.Elimination.BirthDispatcherDone
import Leader.Wu.Elimination.BirthDispatcherLeaderNormalize

/-!
# DONE-aware current-leader normalization

The DONE metadata/expiry result is normalized only at its two computed
endpoints.  The original endpoints remain the first two arguments of the one
existing `finalPhysical` call, so newborn detection remains the actual
old/computed leader-bit test.  No writer-input normalization, WAIT replacement,
or second physical/expiry pass is introduced here.
-/

namespace K2BirthDoneNormalize

open PPLL PPLLDomain PPLLResearchFormulation
  PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
  PPLLLeaderCreationCleanupRepair BirthSigMoveDisposalRepair
  LDSinkBoundedKernel LDSinkKernelC LDSinkTwoGapEpochSuccessor
  ExpiringK2Projection K2OutputSafety

open K2BirthDispatcher K2BirthDispatcherDone K2BirthLeaderNormalize

set_option autoImplicit false
set_option pp.structureInstances false

variable {ψ κ τ n : Nat}

/-- Actual DONE metadata/expiry, then endpoint-local normalization of every
current computed leader. -/
def metadata (hψ : 0 < ψ) (l r : ExpiringAgentState ψ κ τ) :
    ExpiringAgentState ψ κ τ × ExpiringAgentState ψ κ τ :=
  let q := K2BirthDispatcherDone.doneMetadata hψ l r
  (K2BirthLeaderNormalize.normalizeLeader hψ q.1,
    K2BirthLeaderNormalize.normalizeLeader hψ q.2)

/-- The executable birth bit is tested against the original endpoints and the
normalized computed endpoints. -/
def birthEvent (hψ : 0 < ψ) (l r : ExpiringAgentState ψ κ τ) : Bool :=
  let q := metadata hψ l r
  K2BirthDispatcher.newborn l q.1 || K2BirthDispatcher.newborn r q.2

/-- One complete row: DONE metadata, current-leader normalization, then exactly
one existing newborn/collision/K2 tail. -/
def row (hψ : 0 < ψ) (l r : ExpiringAgentState ψ κ τ) :
    ExpiringAgentState ψ κ τ × ExpiringAgentState ψ κ τ :=
  let q := metadata hψ l r
  K2BirthDispatcher.finalPhysical hψ l r q.1 q.2

attribute [local irreducible] metadata birthEvent row

/-- Restoring each pre-normalization label recovers the complete DONE metadata
record, including permit, controls and timer. -/
theorem metadata_field_frame (hψ : 0 < ψ)
    (l r : ExpiringAgentState ψ κ τ) :
    K2BirthLeaderNormalize.putLabel (metadata hψ l r).1
        (K2BirthDispatcherDone.doneMetadata hψ l r).1.core.core.label =
        (K2BirthDispatcherDone.doneMetadata hψ l r).1 ∧
      K2BirthLeaderNormalize.putLabel (metadata hψ l r).2
        (K2BirthDispatcherDone.doneMetadata hψ l r).2.core.core.label =
        (K2BirthDispatcherDone.doneMetadata hψ l r).2 := by
  unfold metadata
  dsimp only
  exact ⟨K2BirthLeaderNormalize.normalizeLeader_field_frame hψ _,
    K2BirthLeaderNormalize.normalizeLeader_field_frame hψ _⟩

/-- Normalization changes neither computed leader bit. -/
theorem metadata_raw_leaders (hψ : 0 < ψ)
    (l r : ExpiringAgentState ψ κ τ) :
    (metadata hψ l r).1.core.core.leader =
        (K2BirthDispatcherDone.doneMetadata hψ l r).1.core.core.leader ∧
      (metadata hψ l r).2.core.core.leader =
        (K2BirthDispatcherDone.doneMetadata hψ l r).2.core.core.leader := by
  unfold metadata
  dsimp only
  exact ⟨K2BirthLeaderNormalize.normalizeLeader_leader hψ _,
    K2BirthLeaderNormalize.normalizeLeader_leader hψ _⟩

/-- The four-field K2 observation is unchanged by endpoint normalization. -/
theorem metadata_observation_raw (hψ : 0 < ψ)
    (l r : ExpiringAgentState ψ κ τ) :
    (observeCell (metadata hψ l r).1,
      observeCell (metadata hψ l r).2) =
    (observeCell (K2BirthDispatcherDone.doneMetadata hψ l r).1,
      observeCell (K2BirthDispatcherDone.doneMetadata hψ l r).2) := by
  unfold metadata
  dsimp only
  rw [K2BirthLeaderNormalize.normalizeLeader_observation,
    K2BirthLeaderNormalize.normalizeLeader_observation]

/-- The complete normalized metadata still has exactly the original shield,
bullet and signal fields. -/
theorem metadata_bullets (hψ : 0 < ψ)
    (l r : ExpiringAgentState ψ κ τ) :
    ((metadata hψ l r).1.core.core.shield = l.core.core.shield ∧
      (metadata hψ l r).1.core.core.bullet = l.core.core.bullet ∧
      (metadata hψ l r).1.core.core.signal_B = l.core.core.signal_B) ∧
    ((metadata hψ l r).2.core.core.shield = r.core.core.shield ∧
      (metadata hψ l r).2.core.core.bullet = r.core.core.bullet ∧
      (metadata hψ l r).2.core.core.signal_B = r.core.core.signal_B) := by
  have hf := metadata_field_frame hψ l r
  have hb := K2BirthDispatcherDone.doneMetadata_bullets hψ l r
  have eLs := congrArg
    (fun q : ExpiringAgentState ψ κ τ => q.core.core.shield) hf.1
  have eLb := congrArg
    (fun q : ExpiringAgentState ψ κ τ => q.core.core.bullet) hf.1
  have eLz := congrArg
    (fun q : ExpiringAgentState ψ κ τ => q.core.core.signal_B) hf.1
  have eRs := congrArg
    (fun q : ExpiringAgentState ψ κ τ => q.core.core.shield) hf.2
  have eRb := congrArg
    (fun q : ExpiringAgentState ψ κ τ => q.core.core.bullet) hf.2
  have eRz := congrArg
    (fun q : ExpiringAgentState ψ κ τ => q.core.core.signal_B) hf.2
  change (metadata hψ l r).1.core.core.shield =
    (K2BirthDispatcherDone.doneMetadata hψ l r).1.core.core.shield at eLs
  change (metadata hψ l r).1.core.core.bullet =
    (K2BirthDispatcherDone.doneMetadata hψ l r).1.core.core.bullet at eLb
  change (metadata hψ l r).1.core.core.signal_B =
    (K2BirthDispatcherDone.doneMetadata hψ l r).1.core.core.signal_B at eLz
  change (metadata hψ l r).2.core.core.shield =
    (K2BirthDispatcherDone.doneMetadata hψ l r).2.core.core.shield at eRs
  change (metadata hψ l r).2.core.core.bullet =
    (K2BirthDispatcherDone.doneMetadata hψ l r).2.core.core.bullet at eRb
  change (metadata hψ l r).2.core.core.signal_B =
    (K2BirthDispatcherDone.doneMetadata hψ l r).2.core.core.signal_B at eRz
  exact ⟨
    ⟨eLs.trans hb.1.1, eLb.trans hb.1.2.1, eLz.trans hb.1.2.2⟩,
    ⟨eRs.trans hb.2.1, eRb.trans hb.2.2.1, eRz.trans hb.2.2.2⟩⟩

/-- Existing leaders survive the complete DONE metadata prefix and normalization. -/
theorem metadata_existing_leaders (hψ : 0 < ψ)
    (l r : ExpiringAgentState ψ κ τ) :
    (l.core.core.leader = true →
      (metadata hψ l r).1.core.core.leader = true) ∧
    (r.core.core.leader = true →
      (metadata hψ l r).2.core.core.leader = true) := by
  have hd := K2BirthDispatcherDone.doneMetadata_existing_leaders hψ l r
  have hn := metadata_raw_leaders hψ l r
  exact ⟨fun hl => hn.1.trans (hd.1 hl),
    fun hr => hn.2.trans (hd.2 hr)⟩

/-- Every computed metadata leader, old or newly created, has physical label zero. -/
theorem metadata_leader_labels_zero (hψ : 0 < ψ)
    (l r : ExpiringAgentState ψ κ τ) :
    ((metadata hψ l r).1.core.core.leader = true →
      (metadata hψ l r).1.core.core.label = ⟨0, hψ⟩) ∧
    ((metadata hψ l r).2.core.core.leader = true →
      (metadata hψ l r).2.core.core.label = ⟨0, hψ⟩) := by
  unfold metadata
  dsimp only
  exact ⟨K2BirthLeaderNormalize.normalizeLeader_label_zero hψ _,
    K2BirthLeaderNormalize.normalizeLeader_label_zero hψ _⟩

/-- Normalizing the computed leader label changes no birth bit. -/
theorem birthEvent_eq_done (hψ : 0 < ψ)
    (l r : ExpiringAgentState ψ κ τ) :
    birthEvent hψ l r = K2BirthDispatcherDone.doneBirthEvent hψ l r := by
  unfold birthEvent metadata K2BirthDispatcherDone.doneBirthEvent
  dsimp only
  rw [K2BirthLeaderNormalize.newborn_normalize,
    K2BirthLeaderNormalize.newborn_normalize]

/-- The actual no-birth Boolean forces exact equality of the four K2 fields.
Leader equality is derived from `newborn` plus DONE old-leader preservation;
the other three fields come from the actual DONE metadata computation. -/
theorem metadata_signal_of_no_birth (hψ : 0 < ψ)
    (l r : ExpiringAgentState ψ κ τ)
    (hn : birthEvent hψ l r = false) :
    (observeCell (metadata hψ l r).1,
      observeCell (metadata hψ l r).2) =
      (observeCell l, observeCell r) := by
  have hnb :
      K2BirthDispatcher.newborn l (metadata hψ l r).1 = false ∧
      K2BirthDispatcher.newborn r (metadata hψ l r).2 = false := by
    simpa only [birthEvent, Bool.or_eq_false_iff] using hn
  have hp := metadata_existing_leaders hψ l r
  have hb := metadata_bullets hψ l r
  have hleadL :
      (metadata hψ l r).1.core.core.leader = l.core.core.leader := by
    cases hl : l.core.core.leader with
    | false =>
        simpa [K2BirthDispatcher.newborn, hl] using hnb.1
    | true =>
        simpa [hl] using (hp.1 hl)
  have hleadR :
      (metadata hψ l r).2.core.core.leader = r.core.core.leader := by
    cases hr : r.core.core.leader with
    | false =>
        simpa [K2BirthDispatcher.newborn, hr] using hnb.2
    | true =>
        simpa [hr] using (hp.2 hr)
  apply Prod.ext
  · unfold ExpiringK2Projection.observeCell K2OutputSafety.signalView
    apply congrArg PPLLNoCheckBirthConditionTwoProtocol.PeaceView.toState
    apply PPLLNoCheckBirthConditionTwoPhysical.PeaceView.ext
    · exact hleadL
    · rfl
    · exact hb.1.1
    · exact hb.1.2.1
    · exact hb.1.2.2
  · unfold ExpiringK2Projection.observeCell K2OutputSafety.signalView
    apply congrArg PPLLNoCheckBirthConditionTwoProtocol.PeaceView.toState
    apply PPLLNoCheckBirthConditionTwoPhysical.PeaceView.ext
    · exact hleadR
    · rfl
    · exact hb.2.1
    · exact hb.2.2.1
    · exact hb.2.2.2

/-- The one physical tail frames the normalized computed metadata. -/
theorem row_metadata_frame (hψ : 0 < ψ)
    (l r : ExpiringAgentState ψ κ τ) :
    putSignals (row hψ l r).1 (observeCell (metadata hψ l r).1) =
        (metadata hψ l r).1 ∧
      putSignals (row hψ l r).2 (observeCell (metadata hψ l r).2) =
        (metadata hψ l r).2 := by
  unfold row
  dsimp only
  exact K2BirthDispatcher.finalPhysical_frame hψ l r _ _

/-- All non-K2 fields after the physical tail are exactly those of normalized
DONE metadata. -/
theorem row_metadata_nonK2 (hψ : 0 < ψ)
    (l r : ExpiringAgentState ψ κ τ) :
    nonK2 (row hψ l r).1 = nonK2 (metadata hψ l r).1 ∧
      nonK2 (row hψ l r).2 = nonK2 (metadata hψ l r).2 := by
  unfold row
  dsimp only
  exact K2BirthDispatcher.finalPhysical_nonK2 hψ l r _ _

/-- In particular the physical tail retains the normalized labels exactly. -/
theorem row_labels_metadata (hψ : 0 < ψ)
    (l r : ExpiringAgentState ψ κ τ) :
    (row hψ l r).1.core.core.label = (metadata hψ l r).1.core.core.label ∧
      (row hψ l r).2.core.core.label = (metadata hψ l r).2.core.core.label := by
  have h := row_metadata_nonK2 hψ l r
  have hl := congrArg
    (fun q : ExpiringAgentState ψ κ τ => q.core.core.label) h.1
  have hr := congrArg
    (fun q : ExpiringAgentState ψ κ τ => q.core.core.label) h.2
  change (row hψ l r).1.core.core.label =
    (metadata hψ l r).1.core.core.label at hl
  change (row hψ l r).2.core.core.label =
    (metadata hψ l r).2.core.core.label at hr
  exact ⟨hl, hr⟩

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
      have he := congrArg
        (fun q : AgentState 1 × AgentState 1 => q.1.leader) ho
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
      have he := congrArg
        (fun q : AgentState 1 × AgentState 1 => q.2.leader) ho
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
  exact ⟨
    fun hout =>
      (K2BirthDispatcher.initializeNewborn_leader oldL metaL).symm.trans
        (h.1 hout),
    fun hout =>
      (K2BirthDispatcher.initializeNewborn_leader oldR metaR).symm.trans
        (h.2 hout)⟩

/-- Every leader surviving the complete touched row has physical label zero. -/
theorem row_leader_labels_zero (hψ : 0 < ψ)
    (l r : ExpiringAgentState ψ κ τ) :
    ((row hψ l r).1.core.core.leader = true →
      (row hψ l r).1.core.core.label = ⟨0, hψ⟩) ∧
    ((row hψ l r).2.core.core.leader = true →
      (row hψ l r).2.core.core.label = ⟨0, hψ⟩) := by
  have hs :
      ((row hψ l r).1.core.core.leader = true →
        (metadata hψ l r).1.core.core.leader = true) ∧
      ((row hψ l r).2.core.core.leader = true →
        (metadata hψ l r).2.core.core.leader = true) := by
    unfold row
    dsimp only
    exact finalPhysical_no_new_leaders hψ l r _ _
  have hz := metadata_leader_labels_zero hψ l r
  have hf := row_labels_metadata hψ l r
  exact ⟨fun h => hf.1.trans (hz.1 (hs.1 h)),
    fun h => hf.2.trans (hz.2 (hs.2 h))⟩

/-- Actual computed no-birth gives exactly the frozen collision/K2 observation. -/
theorem observe_row_of_no_birth (hψ : 0 < ψ)
    (l r : ExpiringAgentState ψ κ τ)
    (hn : birthEvent hψ l r = false) :
    (observeCell (row hψ l r).1, observeCell (row hψ l r).2) =
      K2BirthDispatcher.shadowRow (observeCell l) (observeCell r) := by
  have hnorm :
      K2BirthDispatcher.newborn l (metadata hψ l r).1 = false ∧
      K2BirthDispatcher.newborn r (metadata hψ l r).2 = false := by
    simpa only [birthEvent, Bool.or_eq_false_iff] using hn
  unfold row
  dsimp only
  rw [K2BirthDispatcher.finalPhysical_of_no_birth hψ l r _ _
    hnorm.1 hnorm.2]
  exact (K2BirthDispatcher.observe_collisionRow hψ _ _).trans
    (congrArg (fun q : AgentState 1 × AgentState 1 =>
      K2BirthDispatcher.shadowRow q.1 q.2)
      (metadata_signal_of_no_birth hψ l r hn))

/-- The only expiry calls are still the two calls inside the one DONE metadata
computation, once per endpoint role. -/
theorem row_timers_once (hψ : 0 < ψ)
    (l r : ExpiringAgentState ψ κ τ) :
    let l0 := prepareExpiringDisposal hψ l
    let r0 := prepareExpiringDisposal hψ r
    let q := K2BirthDispatcherDone.doneMetadataBounded hψ l0.core r0.core
    (row hψ l r).1.stall =
        (deletionPriorityExpireOne τ l0 ⟨q.1, l0.stall⟩).stall ∧
      (row hψ l r).2.stall =
        (deletionPriorityExpireOne τ r0 ⟨q.2, r0.stall⟩).stall := by
  have hf := row_metadata_frame hψ l r
  have hL := congrArg ExpiringAgentState.stall hf.1
  have hR := congrArg ExpiringAgentState.stall hf.2
  change (row hψ l r).1.stall = (metadata hψ l r).1.stall at hL
  change (row hψ l r).2.stall = (metadata hψ l r).2.stall at hR
  have hm := metadata_field_frame hψ l r
  have mL := congrArg ExpiringAgentState.stall hm.1
  have mR := congrArg ExpiringAgentState.stall hm.2
  change (metadata hψ l r).1.stall =
    (K2BirthDispatcherDone.doneMetadata hψ l r).1.stall at mL
  change (metadata hψ l r).2.stall =
    (K2BirthDispatcherDone.doneMetadata hψ l r).2.stall at mR
  unfold K2BirthDispatcherDone.doneMetadata at mL mR
  exact ⟨hL.trans mL, hR.trans mR⟩

/-- Unconditional range closure on the same finite expiring carrier. -/
theorem row_domain (hψ : 0 < ψ)
    (l r : ExpiringAgentState ψ κ τ) :
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

/-- Same exhaustive finite carrier; normalization adds no state. -/
def stateCertificate (hψ : 0 < ψ) (κ τ : Nat) :
    ExhaustiveList (protocol hψ κ τ).Q :=
  K2BirthDispatcher.stateCertificate hψ κ τ

theorem finite_state_bound (hψ : 0 < ψ) (κ τ : Nat) :
    Function.Injective (stateCertificate hψ κ τ).decode ∧
    Function.Surjective (stateCertificate hψ κ τ).decode ∧
    (stateCertificate hψ κ τ).values.length ≤
      ExpiringK2Projection.localBound ψ κ τ :=
  K2BirthDispatcher.finite_state_bound hψ κ τ

theorem observe_step_of_no_birth (hψ : 0 < ψ) (ring : DirectedRing n)
    (C : Fin n → ExpiringAgentState ψ κ τ) (e : Fin n)
    (hn : birthEvent hψ (C e) (C (ring.rightNeighbor e)) = false) :
    ExpiringK2Projection.observe (step hψ ring C e) =
      K2BirthDispatcher.shadowStep ring (ExpiringK2Projection.observe C) e := by
  have hq := observe_row_of_no_birth hψ (C e) (C (ring.rightNeighbor e)) hn
  funext i
  simp only [ExpiringK2Projection.observe, step, PopulationProtocol.step,
    protocol, K2BirthDispatcher.shadowStep, updatePair]
  split
  · exact congrArg Prod.fst hq
  · split
    · exact congrArg Prod.snd hq
    · rfl

/-- Proof-side condition on the actual evolving DONE+normalization execution. -/
def NoBirthAlong (hψ : 0 < ψ) (ring : DirectedRing n)
    (C : Fin n → ExpiringAgentState ψ κ τ) : List (Fin n) → Prop
  | [] => True
  | e :: es =>
      birthEvent hψ (C e) (C (ring.rightNeighbor e)) = false ∧
      NoBirthAlong hψ ring (step hψ ring C e) es

theorem NoBirthAlong.take (hψ : 0 < ψ) (ring : DirectedRing n)
    (C : Fin n → ExpiringAgentState ψ κ τ) (es : List (Fin n))
    (hn : NoBirthAlong hψ ring C es) (t : Nat) :
    NoBirthAlong hψ ring C (es.take t) := by
  induction t generalizing C es with
  | zero => trivial
  | succ t ih =>
    cases es with
    | nil => trivial
    | cons e es => exact ⟨hn.1, ih _ _ hn.2⟩

theorem observe_run_of_no_birth (hψ : 0 < ψ) (ring : DirectedRing n)
    (C : Fin n → ExpiringAgentState ψ κ τ) (es : List (Fin n))
    (hn : NoBirthAlong hψ ring C es) :
    ExpiringK2Projection.observe (run (step hψ ring) C es) =
      run (K2BirthDispatcher.shadowStep ring)
        (ExpiringK2Projection.observe C) es := by
  induction es generalizing C with
  | nil => rfl
  | cons e es ih =>
    simpa only [run, observe_step_of_no_birth hψ ring C e hn.1] using
      ih (step hψ ring C e) hn.2

/-- Every scheduler prefix has the same four-field K2 observation. -/
theorem observe_all_prefixes_of_no_birth (hψ : 0 < ψ)
    (ring : DirectedRing n) (C : Fin n → ExpiringAgentState ψ κ τ)
    (es : List (Fin n)) (hn : NoBirthAlong hψ ring C es) (t : Nat) :
    ExpiringK2Projection.observe (run (step hψ ring) C (es.take t)) =
      run (K2BirthDispatcher.shadowStep ring)
        (ExpiringK2Projection.observe C) (es.take t) :=
  observe_run_of_no_birth hψ ring C _
    (NoBirthAlong.take hψ ring C es hn t)

/-- Same scheduler word and caller-supplied actual UCell configuration. -/
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

/-- Direct all-prefix equality to the frozen AdjacentLeaderElimination system. -/
theorem same_word_adjacent_all_prefixes (hψ : 0 < ψ)
    (ring : DirectedRing n) (C : Fin n → ExpiringAgentState ψ κ τ)
    (D : Fin n → StateBoundUnifiedCell.UCell ψ κ) (es : List (Fin n))
    (h0 : ExpiringK2Projection.observe C = LabelFreeElimination.observe D)
    (hn : NoBirthAlong hψ ring C es) (t : Nat) :
    ExpiringK2Projection.observe (run (step hψ ring) C (es.take t)) =
      LabelFreeElimination.observe
        (run (AdjacentLeaderElimination.step hψ ring) D (es.take t)) :=
  same_word_adjacent hψ ring C D _ h0
    (NoBirthAlong.take hψ ring C es hn t)

/-- Unscheduled sites retain their complete raw records. -/
theorem step_other (hψ : 0 < ψ) (ring : DirectedRing n)
    (C : Fin n → ExpiringAgentState ψ κ τ) (e i : Fin n)
    (hi : i ≠ e) (hj : i ≠ ring.rightNeighbor e) :
    step hψ ring C e i = C i := by
  simp only [step, PopulationProtocol.step, protocol, if_neg hi, if_neg hj]

/-- Self-edge aliasing retains the population protocol's real left-output
priority; no responder copy is inserted. -/
theorem step_alias (hψ : 0 < ψ) (ring : DirectedRing n)
    (C : Fin n → ExpiringAgentState ψ κ τ) (e : Fin n)
    (ha : ring.rightNeighbor e = e) :
    step hψ ring C e e = (row hψ (C e) (C e)).1 := by
  simp only [step, PopulationProtocol.step, protocol, ha, if_true]

#print axioms K2BirthDoneNormalize.metadata_field_frame
#print axioms K2BirthDoneNormalize.metadata_raw_leaders
#print axioms K2BirthDoneNormalize.metadata_observation_raw
#print axioms K2BirthDoneNormalize.metadata_bullets
#print axioms K2BirthDoneNormalize.metadata_existing_leaders
#print axioms K2BirthDoneNormalize.metadata_leader_labels_zero
#print axioms K2BirthDoneNormalize.birthEvent_eq_done
#print axioms K2BirthDoneNormalize.metadata_signal_of_no_birth
#print axioms K2BirthDoneNormalize.row_metadata_frame
#print axioms K2BirthDoneNormalize.row_metadata_nonK2
#print axioms K2BirthDoneNormalize.row_labels_metadata
#print axioms K2BirthDoneNormalize.row_leader_labels_zero
#print axioms K2BirthDoneNormalize.observe_row_of_no_birth
#print axioms K2BirthDoneNormalize.row_timers_once
#print axioms K2BirthDoneNormalize.row_domain
#print axioms K2BirthDoneNormalize.finite_state_bound
#print axioms K2BirthDoneNormalize.observe_step_of_no_birth
#print axioms K2BirthDoneNormalize.NoBirthAlong.take
#print axioms K2BirthDoneNormalize.observe_run_of_no_birth
#print axioms K2BirthDoneNormalize.observe_all_prefixes_of_no_birth
#print axioms K2BirthDoneNormalize.same_word_adjacent
#print axioms K2BirthDoneNormalize.same_word_adjacent_all_prefixes
#print axioms K2BirthDoneNormalize.step_other
#print axioms K2BirthDoneNormalize.step_alias

end K2BirthDoneNormalize
