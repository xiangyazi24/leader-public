import Leader.Wu.Elimination.OutputSafety
import Leader.Wu.WallSweep.ShieldCircuit

/-!
Concrete compatibility bridges between K2's physical `RowSafe` predicate
and the existing leader-probe wall, authorized CHECK stages, and gated WRITE.
The proofs concern one actual row at its actual input.  They do not supply a
dispatcher, a future CHECK condition, or an arrival/complexity theorem.
-/

namespace K2ControllerCompatibility

open PPLL PPLLRepair PPLLVerify K2OutputSafety
  PPLLNoCheckBirthConditionTwoPhysical PPLLNoCheckBirthConditionTwoProtocol
  PPLLNoCheckBirthConditionTwoFrames PPLLNoCheckBirthConditionTwoWriteFrames
  PPLLWriteIncrementGate PPLLAuthorizedComparisonRepair
  PPLLLeaderCreationCleanupRepair
  PPLLWallSweepRepair PPLLWallSweepFinite PPLLWallSweepNormalResetContract
  PPLLWallSweepShieldCircuit PPLLPathStallComparisonRepair
  PPLLExpiringComparisonRepair PPLLNoCheckBirthOutputLegitimacy

set_option autoImplicit false
set_option pp.structureInstances false

variable {n ψ κ τ : Nat}

attribute [local irreducible]
  writeSeqIncrementGate wallSweepNormalSanitizedStage wallSweepNormalCheckedStage

/-! ## Transport through a proved physical observation frame -/

/-- A physical five-field frame also frames the exact singleton-label
observation used by K2.  Auxiliary controller fields remain arbitrary. -/
theorem signalView_eq_of_peaceView {a b : AgentState ψ}
    (h : PeaceView.ofState a = PeaceView.ofState b) :
    signalView a = signalView b := by
  exact congrArg (fun v : PeaceView ψ => PeaceView.toState
    { leader := v.leader, label := (0 : Fin 1), shield := v.shield,
      bullet := v.bullet, signal_B := v.signal_B }) h

/-- A pointwise physical frame transports all three actual `RowSafe`
conjuncts: signal safety, zero-labelled leaders, and no free barriers. -/
theorem rowSafe_of_peaceView (hψ : 0 < ψ) (ring : DirectedRing n)
    (C D : Fin n → AgentState ψ) (hC : RowSafe hψ ring C)
    (hview : ∀ i, PeaceView.ofState (D i) = PeaceView.ofState (C i)) :
    RowSafe hψ ring D := by
  have hleader : ∀ i, (D i).leader = (C i).leader :=
    fun i => congrArg PeaceView.leader (hview i)
  have hlabel : ∀ i, (D i).label = (C i).label :=
    fun i => congrArg PeaceView.label (hview i)
  have hsignal : signalConfig D = signalConfig C :=
    funext (fun i => signalView_eq_of_peaceView (hview i))
  refine ⟨?_, ?_, ?_⟩
  · rw [hsignal]
    exact hC.1
  · intro i hi
    apply (hlabel i).trans
    apply hC.2.1 i
    change (C i).leader = true
    exact (hleader i).symm.trans hi
  · intro i
    dsimp only
    intro hb
    have hb' : isBarrier hψ (C i) (C (ring.rightNeighbor i)) := by
      simpa only [isBarrier, hlabel] using hb
    change (D (ring.rightNeighbor i)).leader = true
    exact (hleader _).trans (hC.2.2 i hb')

/-- The existing finite-carrier `PeaceViewConfigFrame` has exactly the
pointwise meaning needed to transport `RowSafe` on its real erased cores. -/
theorem rowSafe_of_expiring_peaceViewConfigFrame
    (hψ : 0 < ψ) (ring : DirectedRing n)
    (C D : Fin n → ExpiringAgentState ψ κ τ)
    (hC : RowSafe hψ ring (fun i => (C i).core.erase.core))
    (hview : PeaceViewConfigFrame C D) :
    RowSafe hψ ring (fun i => (D i).core.erase.core) :=
  rowSafe_of_peaceView hψ ring _ _ hC hview

/-- Lift a concrete pair frame through the existing physical two-position
update.  The statement also covers a singleton ring; it needs no distinctness
assumption because both projected outputs already frame their inputs. -/
theorem updatePair_peaceView_of_pair (C : Fin n → AgentState ψ)
    (i j : Fin n) (q : AgentState ψ × AgentState ψ)
    (hpair : peaceViewPair q = peaceViewPair (C i, C j)) (v : Fin n) :
    PeaceView.ofState (updatePair C i j q v) = PeaceView.ofState (C v) := by
  by_cases hi : v = i
  · subst v
    simpa [updatePair, peaceViewPair] using congrArg Prod.fst hpair
  · by_cases hj : v = j
    · subst v
      simpa [updatePair, peaceViewPair, hi] using congrArg Prod.snd hpair
    · simp only [updatePair, if_neg hi, if_neg hj]

/-! ## Leader-probe wall on the actual selected edge -/

/-- Every mismatch enters an existing leader by `noFreeBarrier`.  The
existing probe wall clears that leader's probe before P-prime, so even the
zero-label hypothesis is unnecessary for this responder frame. -/
theorem pPsiLeaderProbeWall_responder_frame_of_noFreeBarrier
    (hψ : 0 < ψ) (ring : DirectedRing n) (C : Fin n → AgentState ψ)
    (hbar : noFreeBarrier hψ ring C) (e : Fin n) :
    let r := ring.rightNeighbor e
    let q := pPsiLeaderProbeWall hψ (C e) (C r)
    q.2.leader = (C r).leader ∧ q.2.label = (C r).label := by
  by_cases ha : (C (ring.rightNeighbor e)).label =
      ⟨((C e).label.val + 1) % ψ, Nat.mod_lt _ hψ⟩
  · exact pPsiLeaderProbeWall_responder_frame_of_aligned hψ _ _ ha
  · exact pPsiLeaderProbeWall_responder_frame_of_responder_leader
      hψ _ _ (hbar e ha)

/-- The actual leader-probe wall frames both leader bits and both labels on
every `RowSafe` edge, including a nondivisible closing label barrier. -/
theorem pPsiLeaderProbeWall_rowSafe_frame
    (hψ : 0 < ψ) (ring : DirectedRing n) (C : Fin n → AgentState ψ)
    (hC : RowSafe hψ ring C) (e : Fin n) :
    let r := ring.rightNeighbor e
    let q := pPsiLeaderProbeWall hψ (C e) (C r)
    q.1.leader = (C e).leader ∧ q.1.label = (C e).label ∧
      q.2.leader = (C r).leader ∧ q.2.label = (C r).label := by
  let l := C e
  let r := C (ring.rightNeighbor e)
  let l0 := if l.leader = true then { l with probe := false } else l
  let r0 := if r.leader = true ∨ l.leader = true then
    { r with probe := false } else r
  have hlLeader : l0.leader = l.leader := by unfold l0; split <;> rfl
  have hlLabel : l0.label = l.label := by unfold l0; split <;> rfl
  have hr := pPsiLeaderProbeWall_responder_frame_of_noFreeBarrier hψ ring C hC.2.2 e
  exact ⟨(pPsi_initiator_leader_eq hψ l0 r0).trans hlLeader,
    (pPsi_initiator_label_eq hψ l0 r0).trans hlLabel, hr.1, hr.2⟩

private theorem probeWall_bulletFieldPair (hψ : 0 < ψ) (l r : AgentState ψ) :
    bulletFieldPair (pPsiLeaderProbeWall hψ l r) = bulletFieldPair (l, r) := by
  let l0 := if l.leader = true then { l with probe := false } else l
  let r0 := if r.leader = true ∨ l.leader = true then
    { r with probe := false } else r
  change bulletFieldPair (pPsi hψ l0 r0) = bulletFieldPair (l, r)
  exact (pPsi_bulletFieldPair hψ l0 r0).trans (by
    apply Prod.ext <;> apply BulletFields.ext
    all_goals
      unfold l0 r0 bulletFieldPair BulletFields.ofState
      try dsimp only []
      repeat (first | rfl | split))

/-- P-prime's existing bullet-field frame completes the full physical
observation frame; the wall may still change comparison/probe controls. -/
theorem pPsiLeaderProbeWall_peace_of_rowSafe_edge
    (hψ : 0 < ψ) (ring : DirectedRing n) (C : Fin n → AgentState ψ)
    (hC : RowSafe hψ ring C) (e : Fin n) :
    peaceViewPair (pPsiLeaderProbeWall hψ (C e) (C (ring.rightNeighbor e))) =
      peaceViewPair (C e, C (ring.rightNeighbor e)) := by
  have hf := pPsiLeaderProbeWall_rowSafe_frame hψ ring C hC e
  exact peaceViewPair_eq_of_frames (Prod.ext hf.1 hf.2.2.1)
    (Prod.ext hf.2.1 hf.2.2.2) (probeWall_bulletFieldPair hψ _ _)

/-- One isolated actual leader-probe wall row preserves the complete raw
configuration invariant.  This is not a full wall-dispatch statement. -/
theorem pPsiLeaderProbeWall_rowSafe_step
    (hψ : 0 < ψ) (ring : DirectedRing n) (C : Fin n → AgentState ψ)
    (hC : RowSafe hψ ring C) (e : Fin n) :
    RowSafe hψ ring (updatePair C e (ring.rightNeighbor e)
      (pPsiLeaderProbeWall hψ (C e) (C (ring.rightNeighbor e)))) :=
  rowSafe_of_peaceView hψ ring C _ hC
    (updatePair_peaceView_of_pair C _ _ _
      (pPsiLeaderProbeWall_peace_of_rowSafe_edge hψ ring C hC e))

/-! ## Exact normalized and sanitized authorized CHECK signatures -/

/-- Normalization changes only auxiliary fields and thus supplies `RowSafe`
on the actual cores consumed by the leader-probe prefix. -/
theorem rowSafe_normalizeDeletion (hψ : 0 < ψ) (ring : DirectedRing n)
    (C : Fin n → AuthorizedAgentState ψ)
    (hC : RowSafe hψ ring (fun i => (C i).core)) :
    RowSafe hψ ring (fun i => (normalizeDeletion (C i)).core) :=
  rowSafe_of_peaceView hψ ring _ _ hC (fun i => normalizeDeletion_peaceView (C i))

/-- Construct the existing complete edge contract from raw `RowSafe` and
the sole remaining CHECK frame at its real sanitized input.  Both the
normalized P-prime responder field and responder-zero field are derived. -/
theorem WallPeaceEdgeFrame.of_rowSafe_check_frame
    (hψ : 0 < ψ) (kappa : Nat) (ring : DirectedRing n)
    (C : Fin n → AuthorizedAgentState ψ)
    (hC : RowSafe hψ ring (fun i => (C i).core)) (e : Fin n)
    (hcheck :
      (wallSweepNormalCheckedStage hψ kappa (C e) (C (ring.rightNeighbor e))).2.core.leader =
      (wallSweepNormalSanitizedStage hψ kappa (C e) (C (ring.rightNeighbor e))).2.core.leader) :
    WallPeaceEdgeFrame hψ kappa (C e) (C (ring.rightNeighbor e)) := by
  have hn := rowSafe_normalizeDeletion hψ ring C hC
  have hp := pPsiLeaderProbeWall_rowSafe_frame hψ ring _ hn e
  have hv := normalizeDeletion_peaceView (C (ring.rightNeighbor e))
  refine ⟨?_, hcheck, hC.2.1 _⟩
  exact ⟨hp.2.2.1.trans (congrArg PeaceView.leader hv),
    hp.2.2.2.trans (congrArg PeaceView.label hv)⟩

/-- `authorizedCheckSig` has exactly the raw CHECK core.  The existing
stage-local executable safety condition therefore discharges the actual
checked-versus-sanitized responder equation, including authorization wrappers. -/
theorem wallSweepNormalCheckedStage_responder_frame_of_safe
    (hψ : 0 < ψ) (kappa : Nat) (l r : AuthorizedAgentState ψ)
    (hsafe : CheckResponderSafe hψ
      (wallSweepNormalSanitizedStage hψ kappa l r).2.core) :
    (wallSweepNormalCheckedStage hψ kappa l r).2.core.leader =
      (wallSweepNormalSanitizedStage hψ kappa l r).2.core.leader := by
  rw [wallSweepNormalCheckedStage_eq]
  change (checkSig hψ
    (wallSweepNormalSanitizedStage hψ kappa l r).1.core
    (wallSweepNormalSanitizedStage hψ kappa l r).2.core).2.leader = _
  exact checkSig_responder_leader_eq_of_safe hψ _ _ hsafe

/-- A current sanitized `CheckResponderSafe` condition and raw `RowSafe`
produce all existing full-wall edge obligations, without disabling CHECK. -/
theorem WallPeaceEdgeFrame.of_rowSafe_check_safe
    (hψ : 0 < ψ) (kappa : Nat) (ring : DirectedRing n)
    (C : Fin n → AuthorizedAgentState ψ)
    (hC : RowSafe hψ ring (fun i => (C i).core)) (e : Fin n)
    (hsafe : CheckResponderSafe hψ
      (wallSweepNormalSanitizedStage hψ kappa (C e) (C (ring.rightNeighbor e))).2.core) :
    WallPeaceEdgeFrame hψ kappa (C e) (C (ring.rightNeighbor e)) :=
  WallPeaceEdgeFrame.of_rowSafe_check_frame hψ kappa ring C hC e
    (wallSweepNormalCheckedStage_responder_frame_of_safe hψ kappa _ _ hsafe)

/-- Exact expiring/bounded-carrier adapter.  The premise concerns the
sanitized authorized stage of the actual erased endpoints, not raw input
neutrality or an arbitrary future stage. -/
theorem wallPeaceEdgeFrame_of_expiring_rowSafe_check_safe
    (hψ : 0 < ψ) (ring : DirectedRing n)
    (C : Fin n → ExpiringAgentState ψ κ τ)
    (hC : RowSafe hψ ring (fun i => (C i).core.erase.core)) (e : Fin n)
    (hsafe : CheckResponderSafe hψ
      (wallSweepNormalSanitizedStage hψ κ
        (C e).core.erase (C (ring.rightNeighbor e)).core.erase).2.core) :
    WallPeaceEdgeFrame hψ κ (C e).core.erase (C (ring.rightNeighbor e)).core.erase :=
  WallPeaceEdgeFrame.of_rowSafe_check_safe hψ κ ring
    (fun i => (C i).core.erase) hC e hsafe

/-- The established aligned-neutral producer feeds the exact sanitized
condition of the new bridge.  Neutrality is used only on the two present
inputs; no assertion of future neutrality is made. -/
theorem WallPeaceEdgeFrame.of_rowSafe_aligned_neutral
    (hψ : 0 < ψ) (kappa : Nat) (ring : DirectedRing n)
    (C : Fin n → AuthorizedAgentState ψ)
    (hC : RowSafe hψ ring (fun i => (C i).core)) (e : Fin n)
    (halign : (C (ring.rightNeighbor e)).core.label =
      ⟨((C e).core.label.val + 1) % ψ, Nat.mod_lt _ hψ⟩)
    (hl : ComparisonNeutral (C e).core)
    (hr : ComparisonNeutral (C (ring.rightNeighbor e)).core) :
    WallPeaceEdgeFrame hψ kappa (C e) (C (ring.rightNeighbor e)) :=
  WallPeaceEdgeFrame.of_rowSafe_check_safe hψ kappa ring C hC e
    (wallSweepNormalSanitizedStage_check_safe_of_aligned_neutral
      hψ kappa _ _ halign hl hr)

/-! ## The existing isolated gated WRITE row -/

/-- The three existing WRITE frame lemmas give the complete five-field
frame when an input responder leader is already at label zero. -/
theorem writeSeqIncrementGate_peace_of_responder_zero
    (hψ : 0 < ψ) (l r : AgentState ψ)
    (hzero : r.leader = true → r.label = ⟨0, hψ⟩) :
    peaceViewPair (writeSeqIncrementGate hψ l r) = peaceViewPair (l, r) := by
  have hl := writeSeqIncrementGate_leaders_of_responder_zero hψ l r hzero
  have ha := writeSeqIncrementGate_labels hψ l r
  exact peaceViewPair_eq_of_frames (Prod.ext hl.1 hl.2) (Prod.ext ha.1 ha.2)
    (writeSeqIncrementGate_bulletFieldPair hψ l r)

/-- On actual `RowSafe` input, WRITE's responder-zero condition is supplied
internally.  No restriction on other writer/controller fields is added. -/
theorem writeSeqIncrementGate_peace_of_rowSafe_edge
    (hψ : 0 < ψ) (ring : DirectedRing n) (C : Fin n → AgentState ψ)
    (hC : RowSafe hψ ring C) (e : Fin n) :
    peaceViewPair (writeSeqIncrementGate hψ (C e) (C (ring.rightNeighbor e))) =
      peaceViewPair (C e, C (ring.rightNeighbor e)) :=
  writeSeqIncrementGate_peace_of_responder_zero hψ _ _ (hC.2.1 _)

/-- The isolated existing gated WRITE row preserves `RowSafe` on the whole
physical configuration.  A preceding birth-capable CHECK is not part of this
row; the theorem's premise is at WRITE's actual input. -/
theorem writeSeqIncrementGate_rowSafe_step
    (hψ : 0 < ψ) (ring : DirectedRing n) (C : Fin n → AgentState ψ)
    (hC : RowSafe hψ ring C) (e : Fin n) :
    RowSafe hψ ring (updatePair C e (ring.rightNeighbor e)
      (writeSeqIncrementGate hψ (C e) (C (ring.rightNeighbor e)))) :=
  rowSafe_of_peaceView hψ ring C _ hC
    (updatePair_peaceView_of_pair C _ _ _
      (writeSeqIncrementGate_peace_of_rowSafe_edge hψ ring C hC e))

end K2ControllerCompatibility
