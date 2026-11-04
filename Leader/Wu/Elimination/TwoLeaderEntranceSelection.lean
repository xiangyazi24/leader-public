import Leader.Wu.Elimination.TwoLeaderGeometry
import Leader.Wu.RaceEntrance.ControlledRank
import Leader.Wu.RaceEntrance.ControlledTail
import Leader.Wu.RaceEntrance.DummyService
import Leader.Core.ControlledSchedulerMass

/-!
Physical rows and proof-side selection for a complementary two-leader pair.
The shorter actual gap is the attack gap.  Every transition below is the
unchanged K2 row on the original n-site ring; no endpoint is copied.
-/

set_option autoImplicit false

namespace K2TwoLeaderEntranceCore

open PPLLRepair LDSinkGapCleanup LDSinkKernelC LDSinkProtectedAbsorption
  LDSinkGapDoneInvariant LDSinkGapServiceRank LDSinkGapCleanupBound
  K2OutputSafety K2GlobalGapClosure K2TwoLeaderGeometry
  FiniteUniformStoppingTree

variable {n ψ : Nat}

/-- Rotate the actual two-entry layout, exchanging the two physical gaps. -/
def swapFrame (F : TwoLeaderFrame n) : TwoLeaderFrame n where
  gap := fun i => if i = 0 then F.attack else F.recovery
  shared := by
    intro i
    rcases fin2_cases i with rfl | rfl
    · simpa [MinimalTripleChoice.cyclicSucc] using F.outer_alias
    · simpa [MinimalTripleChoice.cyclicSucc] using F.shared_endpoint
  mass := by
    simpa [List.ofFn_succ, Nat.add_comm] using F.lengths_sum

@[simp] theorem swap_recovery (F : TwoLeaderFrame n) :
    (swapFrame F).recovery = F.attack := rfl
@[simp] theorem swap_attack (F : TwoLeaderFrame n) :
    (swapFrame F).attack = F.recovery := rfl

/-- Selection is pure geometry; no physical state or scheduler row changes. -/
def orderedFrame (F : TwoLeaderFrame n) : TwoLeaderFrame n :=
  if F.attack.d ≤ F.recovery.d then F else swapFrame F

theorem ordered_attack_le (F : TwoLeaderFrame n) :
    (orderedFrame F).attack.d ≤ (orderedFrame F).recovery.d := by
  unfold orderedFrame
  split
  · assumption
  · simp only [swap_attack, swap_recovery]
    omega

theorem ordered_invariant (hψ : 0 < ψ) (F : TwoLeaderFrame n)
    (C : Fin n → AgentState ψ) (h : WrapInvariant hψ F C) :
    WrapInvariant hψ (orderedFrame F) C := by
  unfold orderedFrame
  split
  · exact h
  · exact ⟨h.2, h.1⟩

theorem ordered_support (F : TwoLeaderFrame n) (C : Fin n → AgentState ψ)
    (h : TwoLeaderSupport F C) : TwoLeaderSupport (orderedFrame F) C := by
  unfold orderedFrame
  split
  · exact h
  · refine ⟨h.1, ?_⟩
    intro v
    change (C v).leader = true ↔ v = deletePort F ∨ v = outerLeader F
    exact (h.2 v).trans Or.comm

def orderedCanonical (hψ : 0 < ψ) (ring : DirectedRing n)
    (C : Fin n → AgentState ψ) (hC : GlobalClass hψ ring 2 C) : TwoLeaderFrame n :=
  orderedFrame (canonicalFrame hψ ring C hC)

/-- Both physical gap invariants and the ordering are derived from the real
count-two class, with no strict combined-span premise. -/
theorem orderedCanonical_data (hψ : 0 < ψ) (ring : DirectedRing n)
    (C : Fin n → AgentState ψ) (hC : GlobalClass hψ ring 2 C) :
    let F := orderedCanonical hψ ring C hC
    WrapInvariant hψ F C ∧ TwoLeaderSupport F C ∧ F.attack.d ≤ F.recovery.d ∧
      F.recovery.d + F.attack.d = n :=
  ⟨ordered_invariant hψ _ C (canonical_invariants hψ ring C hC),
    ordered_support _ C (canonical_support hψ ring C hC),
    ordered_attack_le _, (orderedCanonical hψ ring C hC).lengths_sum⟩

/-- The sole physical configuration transition used by every service. -/
def rawConf (hψ : 0 < ψ) (F : TwoLeaderFrame n)
    (C : Fin n → AgentState ψ) (e : Fin n) : Fin n → AgentState ψ :=
  rawStep hψ F.attack.ring C e

theorem rawConf_eq_gap (hψ : 0 < ψ) (F : TwoLeaderFrame n) (G : GapFrame n)
    (C : Fin n → AgentState ψ) (e : Fin n) :
    rawConf hψ F C e = sinkStepC hψ G C e :=
  rawStep_eq_frame hψ F.attack.ring G C e

/-- Any presentation of `DirectedRing n` gives the identical actual row. -/
theorem rawConf_eq_rawStep (hψ : 0 < ψ) (ring : DirectedRing n)
    (F : TwoLeaderFrame n) (C : Fin n → AgentState ψ) (e : Fin n) :
    rawConf hψ F C e = rawStep hψ ring C e := by
  rw [rawConf_eq_gap hψ F F.attack, rawStep_eq_frame hψ ring F.attack]

theorem rawConf_invariant (hψ : 0 < ψ) (F : TwoLeaderFrame n)
    (C : Fin n → AgentState ψ) (h : WrapInvariant hψ F C) (e : Fin n)
    (hn : ¬ Deleted F (rawConf hψ F C e)) : WrapInvariant hψ F (rawConf hψ F C e) :=
  wrapInvariant_step hψ F.attack.ring F C h e hn

def SharedReady (F : TwoLeaderFrame n) (C : Fin n → AgentState ψ) : Prop :=
  (C (deletePort F)).signal_B = 1

/-- Exactly the existing controlled scheduler rule: a ready B choice executes
A.  This is proof-side scheduling, not a new protocol transition. -/
noncomputable def controlledPort (F : TwoLeaderFrame n)
    (C : Fin n → AgentState ψ) (e : Fin n) : Fin n := by
  classical
  exact if SharedReady F C ∧ e = deletePort F then preparePort F else e

theorem controlledPort_prepare (F : TwoLeaderFrame n) (C : Fin n → AgentState ψ) :
    controlledPort F C (preparePort F) = preparePort F := by
  classical
  simp [controlledPort, prepare_ne_delete]

theorem controlledPort_delete_ready (F : TwoLeaderFrame n)
    (C : Fin n → AgentState ψ) (h : SharedReady F C) :
    controlledPort F C (deletePort F) = preparePort F := by
  classical
  simp [controlledPort, h]

theorem controlledPort_of_not_ready (F : TwoLeaderFrame n)
    (C : Fin n → AgentState ψ) (h : ¬ SharedReady F C) (e : Fin n) :
    controlledPort F C e = e := by
  classical
  simp [controlledPort, h]

theorem controlledPort_of_ne_delete (F : TwoLeaderFrame n)
    (C : Fin n → AgentState ψ) (e : Fin n) (h : e ≠ deletePort F) :
    controlledPort F C e = e := by
  classical
  simp [controlledPort, h]

theorem signal_zero_of_not_ready (F : TwoLeaderFrame n)
    (C : Fin n → AgentState ψ) (h : ¬ SharedReady F C) :
    (C (deletePort F)).signal_B = 0 := by
  rcases fin2_cases (C (deletePort F)).signal_B with h0 | h1
  · exact h0
  · exact (h h1).elim

theorem controlled_ready_ne_delete (F : TwoLeaderFrame n)
    (C : Fin n → AgentState ψ) (hr : SharedReady F C) (e : Fin n) :
    controlledPort F C e ≠ deletePort F := by
  classical
  by_cases he : e = deletePort F
  · rw [he, controlledPort_delete_ready F C hr]
    exact prepare_ne_delete F
  · rw [controlledPort_of_ne_delete F C e he]
    exact he

private theorem right_injective (ring : DirectedRing n) (e f : Fin n)
    (h : ring.rightNeighbor e = ring.rightNeighbor f) : e = f := by
  have hv := congrArg Fin.val h
  change (e.val + 1) % n = (f.val + 1) % n at hv
  apply Fin.ext
  have he := e.isLt
  have hf := f.isLt
  by_cases he1 : e.val + 1 < n <;> by_cases hf1 : f.val + 1 < n
  · rw [Nat.mod_eq_of_lt he1, Nat.mod_eq_of_lt hf1] at hv
    omega
  · rw [Nat.mod_eq_of_lt he1, show f.val + 1 = n by omega, Nat.mod_self] at hv
    omega
  · rw [show e.val + 1 = n by omega, Nat.mod_self, Nat.mod_eq_of_lt hf1] at hv
    omega
  · omega

/-- The victim has exactly two incident scheduler edges, including wrap. -/
theorem shared_frame (hψ : 0 < ψ) (F : TwoLeaderFrame n)
    (C : Fin n → AgentState ψ) (e : Fin n)
    (ha : e ≠ preparePort F) (hb : e ≠ deletePort F) :
    rawConf hψ F C e (deletePort F) = C (deletePort F) := by
  apply updatePair_other _ _ _ _ _ hb.symm
  intro he
  exact ha (right_injective F.attack.ring e (preparePort F)
    (he.symm.trans (prepare_right F F.attack.ring).symm))

/-- The actual incoming K2 FIRE makes the shared leader unshielded and
signal-zero, with its dummy already transferred to the incoming follower. -/
theorem prepare_row (hψ : 0 < ψ) (F : TwoLeaderFrame n)
    (C : Fin n → AgentState ψ) (hg : WrapInvariant hψ F C) (hr : SharedReady F C) :
    let D := rawConf hψ F C (preparePort F)
    (D (deletePort F)).leader = true ∧ (D (deletePort F)).shield = false ∧
      (D (deletePort F)).signal_B = 0 ∧ (D (deletePort F)).bullet = 0 := by
  have hd := F.recovery.hd
  have hp : F.recovery.d - 1 + 1 = F.recovery.d := by omega
  have ha : (C (deletePort F)).label = nextLabel hψ (C (preparePort F)) := by
    have h := hg.1.2.2.1 (F.recovery.d - 1) (by omega)
    simpa only [hp, F.shared_endpoint, preparePort, deletePort] using h
  have hrow := LDSinkTwoGapArrivalRaceMass.kernelC_prepare_responder hψ
    (C (preparePort F)) (C (deletePort F))
    (hg.1.2.1 _ (by omega) (by omega)) hg.2.1.1 hr ha
  have he : rawConf hψ F C (preparePort F) (deletePort F) =
      (sinkKernelC hψ (C (preparePort F)) (C (deletePort F))).2 := by
    simp only [rawConf, rawStep, prepare_right]
    exact updatePair_responder _ _ _ _ (prepare_ne_delete F).symm
  simpa only [he] using hrow

/-- Once false, the real victim shield stays false under every controlled
edge.  Only the actual source/responder K2 shield rows are used. -/
theorem controlled_shield_closed (hψ : 0 < ψ) (F : TwoLeaderFrame n)
    (C : Fin n → AgentState ψ) (hs : (C (deletePort F)).shield = false) (e : Fin n) :
    (rawConf hψ F C (controlledPort F C e) (deletePort F)).shield = false := by
  let f := controlledPort F C e
  by_cases ha : f = preparePort F
  · change (rawConf hψ F C f (deletePort F)).shield = false
    rw [ha, rawConf, rawStep, prepare_right,
      updatePair_responder _ _ _ _ (prepare_ne_delete F).symm]
    exact LDSinkTwoGapRaceEntranceControlledTail.kernelC_right_shield_false hψ _ _ hs
  · by_cases hb : f = deletePort F
    · have hr : ¬ SharedReady F C := fun hr => controlled_ready_ne_delete F C hr e hb
      change (rawConf hψ F C f (deletePort F)).shield = false
      rw [hb, rawConf, rawStep, updatePair_initiator]
      exact (LDSinkTwoGapRaceEntranceControlledRank.kernelC_left_quiet_fields hψ _ _
        (signal_zero_of_not_ready F C hr)).1.trans hs
    · change (rawConf hψ F C f (deletePort F)).shield = false
      rw [shared_frame hψ F C f ha hb]
      exact hs

/-- Concrete state-dependent two-port redirection for the existing finite
word change-of-measure theorem.  It contains no probability premise. -/
noncomputable def redirection (F : TwoLeaderFrame n) :
    ControlledSchedulerMass.Redirection (Fin n → AgentState ψ) n := by
  classical
  exact ⟨by have := F.four_le; omega, fun C => decide (SharedReady F C),
    fun _ => preparePort F, fun _ => deletePort F, fun _ _ => prepare_ne_delete F⟩

theorem effective_eq (F : TwoLeaderFrame n) (C : Fin n → AgentState ψ) (e : Fin n) :
    (redirection F).effective C e = controlledPort F C e := by
  classical
  simp only [ControlledSchedulerMass.Redirection.effective, redirection,
    decide_eq_true_eq, controlledPort]

theorem collapses_iff (F : TwoLeaderFrame n) (C : Fin n → AgentState ψ) (e : Fin n) :
    (redirection F).Collapses C e ↔
      SharedReady F C ∧ (e = preparePort F ∨ e = deletePort F) := by
  classical
  simp only [ControlledSchedulerMass.Redirection.Collapses, redirection, decide_eq_true_eq]

def outgoingPort (F : TwoLeaderFrame n) : Fin n := F.attack.pos F.attack.d
def incomingPort (F : TwoLeaderFrame n) : Fin n := F.attack.pos (F.attack.d - 1)

theorem prepare_ne_outgoing (F : TwoLeaderFrame n) :
    preparePort F ≠ outgoingPort F := by
  unfold outgoingPort
  rw [F.outer_alias]
  exact (outer_ne_ports F).1.symm

theorem delete_ne_outgoing (F : TwoLeaderFrame n) :
    deletePort F ≠ outgoingPort F := by
  unfold outgoingPort
  rw [F.outer_alias]
  exact (outer_ne_ports F).2.1.symm

def firingPorts (F : TwoLeaderFrame n) : ThreePortSerialCount.Ports n where
  a := outgoingPort F
  b := incomingPort F
  c := deletePort F
  ab := F.attack.pos_ne F.attack.hdn (by have := F.attack.hdn; omega)
    (by have := F.attack.hd; omega)
  ac := (delete_ne_outgoing F).symm
  bc := outerIncoming_ne_delete F

/-- Positive attack cells include the aliased outer endpoint.  The endpoint
case is handled by its real equality with recovery.pos 0, not by span<n. -/
theorem prepare_ne_attack_positive (F : TwoLeaderFrame n) (k : Nat)
    (hk : 1 ≤ k) (hkd : k ≤ F.attack.d) : preparePort F ≠ F.attack.pos k := by
  by_cases he : k = F.attack.d
  · rw [he]
    exact prepare_ne_outgoing F
  · unfold preparePort
    rw [F.attack_pos_offset]
    have := F.recovery.hd
    have := F.attack.hd
    have := F.lengths_sum
    exact F.recovery.pos_ne (by omega) (by omega) (by omega)

theorem prepare_frames_attack (hψ : 0 < ψ) (F : TwoLeaderFrame n)
    (C : Fin n → AgentState ψ) (k : Nat) (hk : 1 ≤ k) (hkd : k ≤ F.attack.d) :
    rawConf hψ F C (preparePort F) (F.attack.pos k) = C (F.attack.pos k) := by
  apply updatePair_other _ _ _ _ _ (prepare_ne_attack_positive F k hk hkd).symm
  rw [prepare_right]
  exact F.attack.pos_ne (Nat.lt_of_le_of_lt hkd F.attack.hdn)
    (by have := F.four_le; omega) (by omega)

/-- Responder preparation frames the exact existing C5 attack rank. -/
theorem prepare_attack_rank_eq (hψ : 0 < ψ) (F : TwoLeaderFrame n)
    (C : Fin n → AgentState ψ) :
    gapWC F.attack (rawConf hψ F C (preparePort F)) = gapWC F.attack C := by
  classical
  let D := rawConf hψ F C (preparePort F)
  have hf : ∀ k, 1 ≤ k → k ≤ F.attack.d → D (F.attack.pos k) = C (F.attack.pos k) :=
    prepare_frames_attack hψ F C
  have hleader : (D (F.attack.pos 0)).leader = (C (F.attack.pos 0)).leader := by
    exact rawStep_leader_away hψ F.attack.ring C (preparePort F) _ (prepare_ne_delete F).symm
  have hclean : CleanReady F.attack D ↔ CleanReady F.attack C := by
    unfold CleanReady
    rw [hf F.attack.d (by have := F.attack.hd; omega) (Nat.le_refl _)]
    constructor <;> intro h <;> refine ⟨h.1, ?_⟩ <;> intro k hk hkd
    · have hb := h.2 k hk hkd
      rwa [hf k hk hkd] at hb
    · rw [hf k hk hkd]
      exact h.2 k hk hkd
  have hdone : GapDoneC F.attack D ↔ GapDoneC F.attack C := by
    unfold GapDoneC EndpointDeleted
    rw [hclean, hleader, hf F.attack.d (by have := F.attack.hd; omega) (Nat.le_refl _)]
  have hbullet : bulletTop F.attack D = bulletTop F.attack C := by
    apply topIdx_congr
    intro k hk hkd
    rw [hf k hk hkd]
  have hsignal : signalTop F.attack D = signalTop F.attack C := by
    apply topIdx_congr
    intro k hk hkd
    rw [hf k hk hkd]
  change gapWC F.attack D = gapWC F.attack C
  simp only [gapWC, hdone, hbullet, hsignal]

theorem invariant_not_deleted (hψ : 0 < ψ) (F : TwoLeaderFrame n)
    (C : Fin n → AgentState ψ) (hg : WrapInvariant hψ F C) : ¬ Deleted F C := by
  rintro (h | h)
  · exact Bool.noConfusion (hg.2.1.1.symm.trans h)
  · exact Bool.noConfusion (hg.1.1.1.symm.trans h)

theorem prepare_not_success (hψ : 0 < ψ) (F : TwoLeaderFrame n)
    (C : Fin n → AgentState ψ) (hg : WrapInvariant hψ F C) :
    ¬ Deleted F (rawConf hψ F C (preparePort F)) := by
  have hd := F.recovery.hd
  have hlead := LDSinkTwoGapRaceEntranceControlledRank.follower_edge_leaders hψ
    F.attack C (preparePort F) (hg.1.2.1 _ (by omega) (by omega))
  intro h
  apply invariant_not_deleted hψ F C hg
  simpa only [rawConf_eq_gap hψ F F.attack, Deleted, hlead] using h

theorem ready_delete_not_success (hψ : 0 < ψ) (F : TwoLeaderFrame n)
    (C : Fin n → AgentState ψ) (hg : WrapInvariant hψ F C) (hs : SharedReady F C) :
    ¬ Deleted F (rawConf hψ F C (deletePort F)) := by
  have hlead := LDSinkTwoGapRaceEntranceLocalService.outgoing_fire_leaders hψ
    F.attack C (deletePort F) hg.2.1.1 hs
  intro h
  apply invariant_not_deleted hψ F C hg
  simpa only [rawConf_eq_gap hψ F F.attack, Deleted, hlead] using h

/-- Cleanliness survives every row away from the actual shooter's two
incident edges, unless an actual endpoint is deleted. -/
theorem clean_neutral (hψ : 0 < ψ) (F : TwoLeaderFrame n)
    (C : Fin n → AgentState ψ) (hg : WrapInvariant hψ F C)
    (hc : CleanReady F.attack C) (e : Fin n)
    (ho : e ≠ outgoingPort F) (hi : e ≠ incomingPort F)
    (hn : ¬ Deleted F (rawConf hψ F C e)) :
    WrapInvariant hψ F (rawConf hψ F C e) ∧ CleanReady F.attack (rawConf hψ F C e) := by
  have hg' := rawConf_invariant hψ F C hg e hn
  refine ⟨hg', (LDSinkTwoGapRaceEntranceLocalService.cleanReady_iff_shooter_signal
    hψ F.attack _ hg'.2).mpr ?_⟩
  have hr : F.attack.ring.rightNeighbor (incomingPort F) = outgoingPort F := by
    unfold incomingPort outgoingPort
    rw [GapFrame.rightNeighbor_pos]
    congr 1
    have := F.attack.hd
    omega
  have hf : rawConf hψ F C e (outgoingPort F) = C (outgoingPort F) := by
    apply updatePair_other _ _ _ _ _ ho.symm
    intro he
    exact hi (right_injective F.attack.ring e (incomingPort F) (he.symm.trans hr.symm))
  change (rawConf hψ F C e (outgoingPort F)).signal_B = _
  rw [hf]
  exact hc.1

/-- A tracked live shot is the unique nonzero positive-sector bullet.  Its
position is proof bookkeeping on the actual configuration. -/
def ShotAt (F : TwoLeaderFrame n) (C : Fin n → AgentState ψ) (t : Nat) : Prop :=
  0 < t ∧ t ≤ F.attack.d ∧ (C (F.attack.pos t)).bullet = 2 ∧
    ∀ u, 0 < u → u ≤ F.attack.d → (C (F.attack.pos u)).bullet ≠ 0 → u = t

def FreshShot (hψ : 0 < ψ) (F : TwoLeaderFrame n) (C : Fin n → AgentState ψ) : Prop :=
  WrapInvariant hψ F C ∧ ShotAt F C F.attack.d

/-- Actual clean outgoing FIRE produces a fresh live shot at the aliased
outer leader.  Its responder lies beyond the attack sector, even at a=2. -/
theorem clean_outgoing_fresh (hψ : 0 < ψ) (F : TwoLeaderFrame n)
    (C : Fin n → AgentState ψ) (hg : WrapInvariant hψ F C) (hc : CleanReady F.attack C) :
    FreshShot hψ F (rawConf hψ F C (outgoingPort F)) := by
  have ha := F.attack.hd
  have hr := F.recovery.hd
  have hn := F.lengths_sum
  have hdn : F.attack.d + 1 < n := by omega
  have hlead := LDSinkTwoGapRaceEntranceLocalService.outgoing_fire_leaders hψ F.attack
    C (outgoingPort F) hg.2.1.2 hc.1
  have hnd : ¬ Deleted F (rawConf hψ F C (outgoingPort F)) := by
    intro h
    apply invariant_not_deleted hψ F C hg
    simpa only [rawConf_eq_gap hψ F F.attack, Deleted, hlead] using h
  refine ⟨rawConf_invariant hψ F C hg _ hnd, by omega, Nat.le_refl _, ?_, ?_⟩
  · have hrow := congrArg AgentState.bullet
      (kernel_source_fire hψ (C (outgoingPort F))
        (C (F.attack.ring.rightNeighbor (outgoingPort F))) hg.2.1.2 hc.1)
    simpa [rawConf, rawStep, updatePair, outgoingPort] using hrow
  · intro u hu hud hb
    by_cases he : u = F.attack.d
    · exact he
    · have hf : rawConf hψ F C (outgoingPort F) (F.attack.pos u) = C (F.attack.pos u) := by
        apply updatePair_other _ _ _ _ _
          (F.attack.pos_ne (by omega) F.attack.hdn (by omega))
        rw [show F.attack.ring.rightNeighbor (outgoingPort F) =
          F.attack.pos (F.attack.d + 1) from GapFrame.rightNeighbor_pos F.attack F.attack.d]
        exact F.attack.pos_ne (by omega) hdn (by omega)
      rw [hf] at hb
      exact (hb (hc.2 u (by omega) hud)).elim

/-- Original physical K2 stopping tree, stopped only by an actual endpoint deletion. -/
noncomputable def originalPhysicalStep (hψ : 0 < ψ) (F : TwoLeaderFrame n) :=
  K2TwoLeaderGeometry.physicalStep hψ F.attack.ring F

/-- The same physical row under the concrete two-port redirection. -/
noncomputable def controlledPhysicalStep (hψ : 0 < ψ) (F : TwoLeaderFrame n)
    (C : Fin n → AgentState ψ) (e : Fin n) : StopNode (Fin n → AgentState ψ) :=
  originalPhysicalStep hψ F C (controlledPort F C e)

open Classical in
theorem originalPhysicalStep_normal_form (hψ : 0 < ψ) (F : TwoLeaderFrame n)
    (C : Fin n → AgentState ψ) (e : Fin n) :
    originalPhysicalStep hψ F C e =
      if Deleted F (rawConf hψ F C e) then .success else .active (rawConf hψ F C e) := by
  classical
  rfl

open Classical in
theorem controlledPhysicalStep_normal_form (hψ : 0 < ψ) (F : TwoLeaderFrame n)
    (C : Fin n → AgentState ψ) (e : Fin n) :
    controlledPhysicalStep hψ F C e =
      if Deleted F (rawConf hψ F C (controlledPort F C e)) then .success
      else .active (rawConf hψ F C (controlledPort F C e)) := by
  classical
  rfl

theorem physical_controlled_eq (hψ : 0 < ψ) (F : TwoLeaderFrame n) :
    ControlledSchedulerMass.controlledStep (originalPhysicalStep hψ F) (redirection F) =
      controlledPhysicalStep hψ F := by
  funext C e
  unfold ControlledSchedulerMass.controlledStep
  rw [effective_eq]
  rfl

end K2TwoLeaderEntranceCore

#print axioms K2TwoLeaderEntranceCore.orderedCanonical_data
#print axioms K2TwoLeaderEntranceCore.rawConf_eq_rawStep
#print axioms K2TwoLeaderEntranceCore.prepare_row
#print axioms K2TwoLeaderEntranceCore.controlled_shield_closed
#print axioms K2TwoLeaderEntranceCore.effective_eq
#print axioms K2TwoLeaderEntranceCore.prepare_frames_attack
#print axioms K2TwoLeaderEntranceCore.prepare_attack_rank_eq
#print axioms K2TwoLeaderEntranceCore.clean_outgoing_fresh

#print axioms K2TwoLeaderEntranceCore.physical_controlled_eq
