import Leader.Wu.Elimination.SinkTwoGapReachInvariant
import Leader.Wu.Elimination.CleanBoundaryDecision
import Leader.Core.ThreePortSerialCount

set_option autoImplicit false

open FiniteUniformStoppingTree PPLLRepair
open LDSinkGapCleanup LDSinkKernelC LDSinkProtectedAbsorption LDTwoGapFrame
open LDSinkTwoGapNoResetKernel LDSinkTwoGapEntrance LDSinkTwoGapDeletion
open LDSinkTwoGapDeletionWired LDSinkTwoGapReachInvariant
open LDSinkTwoGapEpochSuccessor

namespace LDSinkTwoGapArrivalRaceMass

variable {n psi : Nat}

/-!
The useful local order at `RaceReady` is recovery-entry first, then the
attack-victim edge.  The first edge makes the victim a responder and clears
its shield and signal; the second consumes the parked live bullet.  The
edge leaving the parked bullet is a third competing edge, since an upstream
dummy bullet can overwrite the parked live shot there.
-/

/-- The incoming recovery edge makes the shared leader a responder. -/
def preparePort (F : TwoGapFrame n) : Fin n :=
  F.recovery.pos (F.recovery.d - 1)

/-- The attack victim edge consumes the parked live bullet. -/
def deletePort (F : TwoGapFrame n) : Fin n := F.attack.pos 0

/-- This edge can replace the parked shot by an upstream bullet. -/
def overwritePort (F : TwoGapFrame n) : Fin n := F.attack.pos 1

theorem preparePort_ne_deletePort (F : TwoGapFrame n) :
    preparePort F ≠ deletePort F := by
  exact F.recovery_before_shared_ne_attack (F.recovery.d - 1) 0
    (by have h := F.recovery.hd; omega) (by omega)

theorem preparePort_ne_overwritePort (F : TwoGapFrame n) :
    preparePort F ≠ overwritePort F := by
  exact F.recovery_before_shared_ne_attack (F.recovery.d - 1) 1
    (by have h := F.recovery.hd; omega)
    (by have h := F.attack.hd; omega)

theorem deletePort_ne_overwritePort (F : TwoGapFrame n) :
    deletePort F ≠ overwritePort F := by
  intro heq
  have h := F.attack_pos_injective 0 1 (by omega)
    (by have h := F.attack.hd; omega) heq
  omega

theorem preparePort_right (F : TwoGapFrame n) :
    F.attack.ring.rightNeighbor (preparePort F) = deletePort F := by
  unfold preparePort deletePort
  rw [← F.same_ring, gap_rightNeighbor_pos]
  have hd : F.recovery.d - 1 + 1 = F.recovery.d := by
    have h := F.recovery.hd
    omega
  rw [hd]
  exact F.shared

theorem deletePort_right (F : TwoGapFrame n) :
    F.attack.ring.rightNeighbor (deletePort F) = overwritePort F := by
  exact gap_rightNeighbor_pos F.attack 0

private theorem right_injective (G : GapFrame n) (e f : Fin n)
    (h : G.ring.rightNeighbor e = G.ring.rightNeighbor f) : e = f := by
  have hv := congrArg Fin.val h
  change (e.val + 1) % n = (f.val + 1) % n at hv
  have he := e.isLt
  have hf := f.isLt
  apply Fin.ext
  by_cases he1 : e.val + 1 < n
  · rw [Nat.mod_eq_of_lt he1] at hv
    by_cases hf1 : f.val + 1 < n
    · rw [Nat.mod_eq_of_lt hf1] at hv
      omega
    · have hfn : f.val + 1 = n := by omega
      rw [hfn, Nat.mod_self] at hv
      omega
  · have hen : e.val + 1 = n := by omega
    rw [hen, Nat.mod_self] at hv
    by_cases hf1 : f.val + 1 < n
    · rw [Nat.mod_eq_of_lt hf1] at hv
      omega
    · omega

/-- Edges outside the three competitors frame both the shared victim and
the follower holding the parked live bullet. -/
theorem neutral_frames (hpsi : psi > 0) (F : TwoGapFrame n)
    (C : Fin n → AgentState psi) (e : Fin n)
    (ha : e ≠ preparePort F) (hb : e ≠ deletePort F)
    (hc : e ≠ overwritePort F) :
    sinkStepC hpsi F.attack C e (deletePort F) = C (deletePort F) ∧
    sinkStepC hpsi F.attack C e (overwritePort F) = C (overwritePort F) := by
  constructor
  · apply sinkStepC_other hpsi F.attack C e (deletePort F) hb.symm
    intro heq
    exact ha (right_injective F.attack e (preparePort F)
      (heq.symm.trans (preparePort_right F).symm))
  · apply sinkStepC_other hpsi F.attack C e (overwritePort F) hc.symm
    intro heq
    exact hb (right_injective F.attack e (deletePort F)
      (heq.symm.trans (deletePort_right F).symm))

/-- The exact responder preparation row.  MOVE transfers FIRE's fresh dummy
to the incoming follower, clearing its signal before SIGNAL runs.  Thus no
assumption about the incoming follower's old bullet or signal is needed. -/
theorem kernelC_prepare_responder (hpsi : psi > 0) (l r : AgentState psi)
    (hl : l.leader = false) (hr : r.leader = true)
    (hs : r.signal_B = (1 : Fin 2))
    (halign : r.label = nextLabel hpsi l) :
    let q := sinkKernelC hpsi l r
    q.2.leader = true ∧ q.2.shield = false ∧
      q.2.signal_B = (0 : Fin 2) ∧ q.2.bullet = (0 : Fin 3) := by
  simp [sinkKernelC, eliminateLeadersNoCollisionFire, hl, hr, hs,
    absorbProtectedMove, eliminateLeadersNoCollisionZeroLeaderEgressMove,
    nextLabel, halign, eliminateLeadersNoCollisionSignalLeaderSink,
    dummyBulletSink]
  rfl

/-- With the victim prepared, the exact C kernel deletes it.  This theorem
uses the production kernel's FIRE/MOVE/SIGNAL/dummy-sink composition. -/
theorem kernelC_delete_prepared (hpsi : psi > 0) (l r : AgentState psi)
    (hl : l.leader = true) (hs : l.shield = false)
    (hsg : l.signal_B = (0 : Fin 2)) (hr : r.leader = false)
    (hb : r.bullet = (2 : Fin 3)) :
    (sinkKernelC hpsi l r).1.leader = false := by
  simp [sinkKernelC, eliminateLeadersNoCollisionFire, hl, hs, hsg, hr, hb,
    absorbProtectedMove, eliminateLeadersNoCollisionZeroLeaderEgressMove,
    eliminateLeadersNoCollisionSignalLeaderSink, dummyBulletSink]

/-- Minimal first-stage physical data, all produced by `GapPair` and
`RaceReady`.  Only the incoming label pair is needed from gap geometry. -/
structure FirstReady (hpsi : psi > 0) (F : TwoGapFrame n)
    (b : AState n psi) : Prop where
  incoming_follower : (b.conf (preparePort F)).leader = false
  victim_leader : (b.conf (deletePort F)).leader = true
  victim_signal : (b.conf (deletePort F)).signal_B = (1 : Fin 2)
  incoming_aligned :
    (b.conf (deletePort F)).label = nextLabel hpsi (b.conf (preparePort F))
  parked_follower : (b.conf (overwritePort F)).leader = false
  parked_live : (b.conf (overwritePort F)).bullet = (2 : Fin 3)

/-- Minimal second-stage physical data after the responder preparation. -/
structure SecondReady (F : TwoGapFrame n) (b : AState n psi) : Prop where
  victim_leader : (b.conf (deletePort F)).leader = true
  victim_shield : (b.conf (deletePort F)).shield = false
  victim_signal : (b.conf (deletePort F)).signal_B = (0 : Fin 2)
  parked_follower : (b.conf (overwritePort F)).leader = false
  parked_live : (b.conf (overwritePort F)).bullet = (2 : Fin 3)

/-- The real entrance produces every local fact consumed by the race. -/
theorem firstReady_of_gapPair_raceReady (hpsi : psi > 0)
    (F : TwoGapFrame n) (b : AState n psi)
    (hg : GapPair hpsi F b) (hr : RaceReady F b.conf) :
    FirstReady hpsi F b := by
  have hd := F.recovery.hd
  have ha := F.attack.hd
  have hpred : F.recovery.d - 1 + 1 = F.recovery.d := by omega
  refine ⟨hg.recovery.2.1 _ (by omega) (by omega), hg.attack.1.1,
    ?_, ?_, hg.attack.2.1 1 (by omega) (by omega), hr.1⟩
  · change (b.conf (F.attack.pos 0)).signal_B = _
    rw [← F.shared]
    exact hr.2.1
  · have halign := hg.recovery.2.2.1 (F.recovery.d - 1) (by omega)
    rw [hpred, F.shared] at halign
    exact halign

/-- Noncompeting physical steps preserve the first-stage local relation.
The incoming follower and both labels use unconditional C-kernel laws. -/
theorem firstReady_neutral (hpsi : psi > 0) (F : TwoGapFrame n)
    (b : AState n psi) (h : FirstReady hpsi F b) (e : Fin n)
    (ha : e ≠ preparePort F) (hb : e ≠ deletePort F)
    (hc : e ≠ overwritePort F) :
    FirstReady hpsi F (postState hpsi F b e) := by
  have hf := neutral_frames hpsi F b.conf e ha hb hc
  change FirstReady hpsi F
    (advanceAState F b (sinkStepC hpsi F.attack b.conf e))
  constructor
  · exact sinkStepC_follower_preserved hpsi F.attack b.conf e _
      h.incoming_follower
  · exact (congrArg AgentState.leader hf.1).trans h.victim_leader
  · exact (congrArg AgentState.signal_B hf.1).trans h.victim_signal
  · simpa only [sinkStepC_label_eq, nextLabel, advanceAState] using
      h.incoming_aligned
  · exact (congrArg AgentState.leader hf.2).trans h.parked_follower
  · exact (congrArg AgentState.bullet hf.2).trans h.parked_live

/-- The good first event produces the exact deleting relation, while the
parked shot is outside both endpoints of this incoming edge. -/
theorem firstReady_prepare (hpsi : psi > 0) (F : TwoGapFrame n)
    (b : AState n psi) (h : FirstReady hpsi F b) :
    SecondReady F (postState hpsi F b (preparePort F)) := by
  have hrow := kernelC_prepare_responder hpsi
    (b.conf (preparePort F)) (b.conf (deletePort F))
    h.incoming_follower h.victim_leader h.victim_signal h.incoming_aligned
  have hv :
      sinkStepC hpsi F.attack b.conf (preparePort F) (deletePort F) =
        (sinkKernelC hpsi (b.conf (preparePort F))
          (b.conf (deletePort F))).2 := by
    simp only [sinkStepC, preparePort_right]
    exact updatePair_responder _ _ _ _ (preparePort_ne_deletePort F).symm
  have hp :
      sinkStepC hpsi F.attack b.conf (preparePort F) (overwritePort F) =
        b.conf (overwritePort F) := by
    apply sinkStepC_other hpsi F.attack b.conf (preparePort F)
      (overwritePort F) (preparePort_ne_overwritePort F).symm
    rw [preparePort_right]
    exact (deletePort_ne_overwritePort F).symm
  change SecondReady F
    (advanceAState F b (sinkStepC hpsi F.attack b.conf (preparePort F)))
  constructor
  · exact (congrArg AgentState.leader hv).trans hrow.1
  · exact (congrArg AgentState.shield hv).trans hrow.2.1
  · exact (congrArg AgentState.signal_B hv).trans hrow.2.2.1
  · exact (congrArg AgentState.leader hp).trans h.parked_follower
  · exact (congrArg AgentState.bullet hp).trans h.parked_live

/-- Noncompeting steps frame every second-stage race field. -/
theorem secondReady_neutral (hpsi : psi > 0) (F : TwoGapFrame n)
    (b : AState n psi) (h : SecondReady F b) (e : Fin n)
    (ha : e ≠ preparePort F) (hb : e ≠ deletePort F)
    (hc : e ≠ overwritePort F) :
    SecondReady F (postState hpsi F b e) := by
  have hf := neutral_frames hpsi F b.conf e ha hb hc
  change SecondReady F (advanceAState F b (sinkStepC hpsi F.attack b.conf e))
  constructor
  · exact (congrArg AgentState.leader hf.1).trans h.victim_leader
  · exact (congrArg AgentState.shield hf.1).trans h.victim_shield
  · exact (congrArg AgentState.signal_B hf.1).trans h.victim_signal
  · exact (congrArg AgentState.leader hf.2).trans h.parked_follower
  · exact (congrArg AgentState.bullet hf.2).trans h.parked_live

/-- The good second event deletes the shared leader in the physical
configuration, hence satisfies the actual stopped success predicate. -/
theorem secondReady_delete (hpsi : psi > 0) (F : TwoGapFrame n)
    (b : AState n psi) (h : SecondReady F b) :
    NoResetSuccess F (attemptStepConf hpsi F b (deletePort F)) := by
  have hrow := kernelC_delete_prepared hpsi
    (b.conf (deletePort F)) (b.conf (overwritePort F))
    h.victim_leader h.victim_shield h.victim_signal
    h.parked_follower h.parked_live
  apply Or.inl
  apply Or.inl
  rw [attemptStepConf_eq_sinkStepC]
  change (sinkStepC hpsi F.attack b.conf (deletePort F) (deletePort F)).leader = false
  simpa [sinkStepC, deletePort_right, updatePair] using hrow

/-! ## A physical simulation of the protected two-event race -/

/-- `false` waits for preparation and `true` waits for deletion.  Only the
first two occurrences among the three fixed ports are consulted: the
successful order is preparation followed by deletion.  An overwrite or
an out-of-order competing event is a source failure. -/
def protectedRaceStep (F : TwoGapFrame n) : Bool → Fin n → StopNode Bool
  | false, e =>
      if e = preparePort F then .active true
      else if e = deletePort F ∨ e = overwritePort F then .failure
      else .active false
  | true, e =>
      if e = deletePort F then .success
      else if e = preparePort F ∨ e = overwritePort F then .failure
      else .active true

/-- Source failures may be discarded and early physical deletions are
accepted.  Every live source phase has an established local physical
invariant; no unrestricted `SecondSupport` premise is carried. -/
def protectedRaceRel (hpsi : psi > 0) (F : TwoGapFrame n) :
    StopNode Bool → StopNode (AState n psi) → Prop
  | .failure, _ => True
  | _, .success => True
  | .active false, .active b => FirstReady hpsi F b
  | .active true, .active b => SecondReady F b
  | _, _ => False

private theorem protectedRaceRel_success (hpsi : psi > 0)
    (F : TwoGapFrame n) (u : StopNode Bool) :
    protectedRaceRel hpsi F u .success := by
  cases u with
  | failure => trivial
  | success => trivial
  | active p => cases p <;> trivial

private theorem protectedRaceRel_failure (hpsi : psi > 0)
    (F : TwoGapFrame n) (v : StopNode (AState n psi)) :
    protectedRaceRel hpsi F .failure v := by
  trivial

private theorem protectedRaceRel_active_next (hpsi : psi > 0)
    (F : TwoGapFrame n) (p : Bool) (b : AState n psi)
    (h : protectedRaceRel hpsi F (.active p) (.active b)) (e : Fin n) :
    protectedRaceRel hpsi F (protectedRaceStep F p e)
      (physicalBlockStep hpsi F b e) := by
  classical
  rw [physicalBlockStep_normal_form]
  by_cases hd : NoResetSuccess F (attemptStepConf hpsi F b e)
  · rw [if_pos hd]
    exact protectedRaceRel_success hpsi F _
  · rw [if_neg hd]
    cases p with
    | false =>
        change FirstReady hpsi F b at h
        by_cases ha : e = preparePort F
        · subst e
          simpa [protectedRaceStep, protectedRaceRel] using
            firstReady_prepare hpsi F b h
        · by_cases hbc : e = deletePort F ∨ e = overwritePort F
          · simp only [protectedRaceStep, if_neg ha, if_pos hbc, protectedRaceRel]
          · simpa only [protectedRaceStep, if_neg ha, if_neg hbc, protectedRaceRel]
              using firstReady_neutral hpsi F b h e ha
                (fun hb => hbc (.inl hb)) (fun hc => hbc (.inr hc))
    | true =>
        change SecondReady F b at h
        by_cases hb : e = deletePort F
        · subst e
          exact (hd (secondReady_delete hpsi F b h)).elim
        · by_cases hac : e = preparePort F ∨ e = overwritePort F
          · simp only [protectedRaceStep, if_neg hb, if_pos hac, protectedRaceRel]
          · simpa only [protectedRaceStep, if_neg hb, if_neg hac, protectedRaceRel]
              using secondReady_neutral hpsi F b h e
                (fun ha => hac (.inl ha)) hb (fun hc => hac (.inr hc))

/-- The corrected three-port race admits an unconditional same-edge
simulation on its actual locally produced support.  Its success leaf is
physical deletion by `secondReady_delete`, including the FIRE stage. -/
theorem protectedRace_simulation (hpsi : psi > 0) (F : TwoGapFrame n) :
    SuccessSimulation (protectedRaceStep F) (physicalBlockStep hpsi F)
      (protectedRaceRel hpsi F) where
  terminal := by
    intro u v h
    cases u with
    | failure => exact Nat.zero_le _
    | active p => exact Nat.zero_le _
    | success =>
        cases v with
        | success => exact Nat.le_refl _
        | failure => exact h.elim
        | active b => exact h.elim
  next := by
    intro u v h e
    cases u with
    | failure => exact protectedRaceRel_failure hpsi F _
    | success =>
        cases v with
        | success => trivial
        | failure => exact h.elim
        | active b => exact h.elim
    | active p =>
        cases v with
        | success => exact protectedRaceRel_success hpsi F _
        | failure => cases p <;> exact h.elim
        | active b => exact protectedRaceRel_active_next hpsi F p b h e

/-- Every abstract successful scheduler word is an actual physical success
by the same raw horizon.  All physical premises are produced by the real
gap invariant and race entrance; there is no mass-transfer assumption. -/
theorem protectedRace_successCount_le_physical (hpsi : psi > 0)
    (F : TwoGapFrame n) (b : AState n psi)
    (hg : GapPair hpsi F b) (hr : RaceReady F b.conf) (T : Nat) :
    successCount (protectedRaceStep F) (.active false) T ≤
      successCount (physicalBlockStep hpsi F) (.active b) T := by
  exact successCount_le_of_simulation (protectedRaceStep F)
    (physicalBlockStep hpsi F) (protectedRaceRel hpsi F)
    (protectedRace_simulation hpsi F) (.active false) (.active b)
    (firstReady_of_gapPair_raceReady hpsi F b hg hr) T

/-! ## Eager entrance composition without a physical-transfer assumption -/

/-- Entrance success consumes its edge once.  A physical deletion stops
immediately; otherwise the next raw edge begins the protected race. -/
noncomputable def protectedHandoff (hpsi : psi > 0) (F : TwoGapFrame n)
    (b : AState n psi) (e : Fin n) : StopNode Bool := by
  classical
  exact if NoResetSuccess F (attemptStepConf hpsi F b e) then .success
    else .active false

noncomputable def entranceRaceStep (hpsi : psi > 0) (F : TwoGapFrame n) :
    Sum (AState n psi) Bool → Fin n → StopNode (Sum (AState n psi) Bool) :=
  sequentialStep (entranceStep hpsi F) (protectedRaceStep F)
    (protectedHandoff hpsi F)

/-- During entrance, source and target are the same physical state.  At
handoff the produced race invariant replaces that equality; the protocol
configuration itself is never reset. -/
def entranceRaceRel (hpsi : psi > 0) (F : TwoGapFrame n) :
    StopNode (Sum (AState n psi) Bool) → StopNode (AState n psi) → Prop
  | .failure, _ => True
  | _, .success => True
  | .active (.inl x), .active b => x = b ∧ GapPair hpsi F b
  | .active (.inr p), .active b =>
      protectedRaceRel hpsi F (.active p) (.active b)
  | _, _ => False

private theorem entranceRaceRel_success (hpsi : psi > 0)
    (F : TwoGapFrame n) (u : StopNode (Sum (AState n psi) Bool)) :
    entranceRaceRel hpsi F u .success := by
  cases u with
  | failure => trivial
  | success => trivial
  | active s => cases s <;> trivial

private theorem entranceRaceRel_inRace (hpsi : psi > 0)
    (F : TwoGapFrame n) (u : StopNode Bool) (v : StopNode (AState n psi)) :
    entranceRaceRel hpsi F (inRace u) v ↔ protectedRaceRel hpsi F u v := by
  cases u with
  | failure => rfl
  | success => cases v <;> rfl
  | active p => cases v <;> cases p <;> rfl

private theorem entranceRaceRel_entrance_next (hpsi : psi > 0)
    (F : TwoGapFrame n) (b : AState n psi)
    (hg : GapPair hpsi F b) (e : Fin n) :
    entranceRaceRel hpsi F (entranceRaceStep hpsi F (.inl b) e)
      (physicalBlockStep hpsi F b e) := by
  classical
  by_cases hd : NoResetSuccess F (attemptStepConf hpsi F b e)
  · rw [physicalBlockStep_normal_form, if_pos hd]
    exact entranceRaceRel_success hpsi F _
  · have ht : physicalBlockStep hpsi F b e = .active (postState hpsi F b e) := by
      rw [physicalBlockStep_normal_form, if_neg hd]
    have hnext : GapPair hpsi F (postState hpsi F b e) :=
      LDSinkTwoGapRestartClosure.gapPair_physical_step hpsi F
        (CleanBoundaryDecision.restartCleanBoundarySignalResidual_K2 hpsi F)
        b e (postState hpsi F b e) hg ht
    rw [ht]
    simp only [entranceRaceStep, sequentialStep]
    rw [entrance_normal_form]
    by_cases he : EntranceSuccess F (attemptStepConf hpsi F b e)
    · rw [if_pos he]
      have hr : RaceReady F (postState hpsi F b e).conf := by
        rcases he with hr | hs
        · exact hr
        · exact (hd hs).elim
      simp only [protectedHandoff, if_neg hd, inRace, entranceRaceRel]
      exact firstReady_of_gapPair_raceReady hpsi F _ hnext hr
    · rw [if_neg he]
      exact ⟨rfl, hnext⟩

/-- The entrance-to-race handoff preserves actual time and configuration.
The clean-boundary theorem supplies gap closure; the parked entrance
supplies the first-stage race invariant. -/
theorem entranceRace_simulation (hpsi : psi > 0) (F : TwoGapFrame n) :
    SuccessSimulation (entranceRaceStep hpsi F) (physicalBlockStep hpsi F)
      (entranceRaceRel hpsi F) where
  terminal := by
    intro u v h
    cases u with
    | failure => exact Nat.zero_le _
    | active s => exact Nat.zero_le _
    | success =>
        cases v with
        | success => exact Nat.le_refl _
        | failure => exact h.elim
        | active b => exact h.elim
  next := by
    intro u v h e
    cases u with
    | failure => trivial
    | success =>
        cases v with
        | success => trivial
        | failure => exact h.elim
        | active b => exact h.elim
    | active s =>
        cases v with
        | success => exact entranceRaceRel_success hpsi F _
        | failure => cases s <;> exact h.elim
        | active b =>
            cases s with
            | inl x =>
                change x = b ∧ GapPair hpsi F b at h
                rcases h with ⟨hxb, hg⟩
                subst x
                exact entranceRaceRel_entrance_next hpsi F b hg e
            | inr p =>
                exact (entranceRaceRel_inRace hpsi F _ _).mpr
                  (protectedRaceRel_active_next hpsi F p b h e)

/-- The eager entrance-plus-race tree is dominated by the physical process
at every horizon, with the sole initial premise being the real gap pair. -/
theorem entranceRace_successCount_le_physical (hpsi : psi > 0)
    (F : TwoGapFrame n) (b : AState n psi) (hg : GapPair hpsi F b) (T : Nat) :
    successCount (entranceRaceStep hpsi F) (.active (.inl b)) T ≤
      successCount (physicalBlockStep hpsi F) (.active b) T := by
  exact successCount_le_of_simulation (entranceRaceStep hpsi F)
    (physicalBlockStep hpsi F) (entranceRaceRel hpsi F)
    (entranceRace_simulation hpsi F) (.active (.inl b)) (.active b)
    ⟨rfl, hg⟩ T

/-- Compose genuine entrance and protected-race count bounds into a physical
deletion bound.  The hypotheses are the two numerical counting estimates;
their physical realization and multiplication are proved here.  In
particular, no globally quantified raw-state Bellman certificate or
`RaceMassSpec.transfer` is hidden in this interface. -/
theorem physical_entranceRace_mass (hpsi : psi > 0)
    (F : TwoGapFrame n) (b : AState n psi) (hg : GapPair hpsi F b)
    (HE HR p c : Nat) (hc : 1 ≤ c)
    (hEntrance : n ^ HE ≤ p * successCount (entranceStep hpsi F) (.active b) HE)
    (hRace : n ^ HR ≤ c * successCount (protectedRaceStep F) (.active false) HR) :
    n ^ (HE + HR) ≤
      (p * c) * successCount (physicalBlockStep hpsi F) (.active b) (HE + HR) := by
  have hHandoff : ∀ y e, entranceStep hpsi F y e = .success →
      n ^ HR ≤ c * successCount (protectedRaceStep F)
        (protectedHandoff hpsi F y e) HR := by
    intro y e _
    classical
    unfold protectedHandoff
    split
    · simp only [successCount, treeWeight_success, successWeight, Nat.mul_one]
      simpa using Nat.mul_le_mul_right (n ^ HR) hc
    · exact hRace
  have hseq := sequential_mass (entranceStep hpsi F) (protectedRaceStep F)
    (protectedHandoff hpsi F) b HE HR p c hEntrance hHandoff
  exact Nat.le_trans hseq (Nat.mul_le_mul_left (p * c)
    (entranceRace_successCount_le_physical hpsi F b hg (HE + HR)))

/-! ## The physical race bound with its numerical constants discharged -/

/-- The geometric frame produces the exact three symbols required by the
pure scheduler theorem, including all distinctness proofs. -/
def protectedPorts (F : TwoGapFrame n) : ThreePortSerialCount.Ports n :=
  ⟨preparePort F, deletePort F, overwritePort F,
    preparePort_ne_deletePort F, preparePort_ne_overwritePort F,
    deletePort_ne_overwritePort F⟩

/-- The counted race uses precisely the already simulated scheduler rows.
The difference between nested conditionals and an `Or` guard is syntactic. -/
theorem protectedRaceStep_eq_serialStep (F : TwoGapFrame n) :
    protectedRaceStep F = ThreePortSerialCount.serialStep (protectedPorts F) := by
  funext phase e
  cases phase <;>
    by_cases ha : e = preparePort F <;>
    by_cases hb : e = deletePort F <;>
    by_cases hc : e = overwritePort F <;>
    simp [protectedRaceStep, ThreePortSerialCount.serialStep,
      protectedPorts, ha, hb, hc]

/-- At least a sixteenth of all length-`4*n` words win the protected race.
Every premise of the independent scheduler count is supplied by geometry. -/
theorem protectedRace_mass (F : TwoGapFrame n) :
    n ^ (4 * n) ≤
      16 * successCount (protectedRaceStep F) (.active false) (4 * n) := by
  rw [protectedRaceStep_eq_serialStep]
  apply ThreePortSerialCount.serial_sixteenth
  have hr := F.recovery.hd
  have ha := F.attack.hd
  have hn := F.length_lt
  omega

/-- Physical deletion from the actual race entrance, with the original
`1/16` success mass and `4*n` interaction horizon preserved.  All scheduler,
simulation, local FIRE/MOVE, and support obligations are proved upstream. -/
theorem physical_race_mass (hpsi : psi > 0) (F : TwoGapFrame n)
    (b : AState n psi) (hg : GapPair hpsi F b) (hr : RaceReady F b.conf) :
    n ^ (4 * n) ≤
      16 * successCount (physicalBlockStep hpsi F) (.active b) (4 * n) := by
  exact Nat.le_trans (protectedRace_mass F) (Nat.mul_le_mul_left 16
    (protectedRace_successCount_le_physical hpsi F b hg hr (4 * n)))

/-- A half-mass physical entrance bound now gives a `1/32` deletion bound.
Only the entrance estimate at this concrete legal seed remains a premise;
the old globally quantified entrance potential is not used. -/
theorem physical_entrance_then_race_mass (hpsi : psi > 0)
    (F : TwoGapFrame n) (b : AState n psi) (hg : GapPair hpsi F b)
    (HE : Nat)
    (hEntrance : n ^ HE ≤
      2 * successCount (entranceStep hpsi F) (.active b) HE) :
    n ^ (HE + 4 * n) ≤
      32 * successCount (physicalBlockStep hpsi F) (.active b) (HE + 4 * n) := by
  exact physical_entranceRace_mass hpsi F b hg HE (4 * n) 2 16
    (by decide) hEntrance (protectedRace_mass F)

end LDSinkTwoGapArrivalRaceMass

#print axioms LDSinkTwoGapArrivalRaceMass.firstReady_of_gapPair_raceReady
#print axioms LDSinkTwoGapArrivalRaceMass.firstReady_neutral
#print axioms LDSinkTwoGapArrivalRaceMass.firstReady_prepare
#print axioms LDSinkTwoGapArrivalRaceMass.secondReady_delete
#print axioms LDSinkTwoGapArrivalRaceMass.protectedRace_simulation
#print axioms LDSinkTwoGapArrivalRaceMass.protectedRace_successCount_le_physical
#print axioms LDSinkTwoGapArrivalRaceMass.entranceRace_simulation
#print axioms LDSinkTwoGapArrivalRaceMass.entranceRace_successCount_le_physical
#print axioms LDSinkTwoGapArrivalRaceMass.physical_entranceRace_mass
#print axioms LDSinkTwoGapArrivalRaceMass.protectedRace_mass
#print axioms LDSinkTwoGapArrivalRaceMass.physical_race_mass
#print axioms LDSinkTwoGapArrivalRaceMass.physical_entrance_then_race_mass
