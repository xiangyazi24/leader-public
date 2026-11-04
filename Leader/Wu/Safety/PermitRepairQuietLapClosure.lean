import Leader.Wu.Safety.PermitRepairQuietLap
import Leader.Wu.Birth.ShortDoneTerminalOrdinaryLabel

namespace R1CandidateClosure

open PPLL PPLLResearchFormulation PPLLExpiringComparisonRepair
  PPLLAuthorizedComparisonRepair R1CandidateKernel
  PPLLNoCheckBirthConditionTwoGeometry
  BirthSigMoveDisposalRepair BirthShortDoneTerminalCheckInputSources
  BirthShortDoneTerminalBirthSources

set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096

variable {n psi kappa tau : Nat}
variable (hpsi : 0 < psi) (h2 : 2 ≤ psi) (ring : DirectedRing n)

abbrev S (C : FC n psi kappa tau) (e : Fin n) : FC n psi kappa tau :=
  BirthCheckPermitRepairLeaf.step1 hpsi h2 ring C e

theorem candidate_rows (C : FC n psi kappa tau)
    (hC : CandR1 hpsi h2 ring C) :
    ∀ e, EdgeSafe hpsi h2 (C e) (C (ring.rightNeighbor e)) := by
  rcases hC with ⟨_, _, _, _, _, h⟩
  exact h

-- Guard contradictions are proved on abstract records, not row terms.
private theorem ruler_excludes_pprime (l r : AuthorizedAgentState psi)
    (hR : r.core.leader = false → r.core.label =
      ⟨(l.core.label.val + 1) % psi, Nat.mod_lt _ hpsi⟩) :
    ¬ PPrimeBarrierBirthGuard hpsi l r := by
  intro hb
  exact hb.2.2.2.2 (hR hb.2.1)

private theorem quiet_right_excludes_check (b : AP psi)
    (hq : AuthQuiet b.2) : ¬ ActualCheckBirthInput hpsi b := by
  intro hb
  have hf : CheckFollowerBirthInput hpsi b.1.core b.2.core :=
    hb.2.2.2.2.2.2
  rcases hf.2.2 with heq | ⟨lab, bit, hpath, _⟩
  · have bad : MainState.none = MainState.equal := hq.1.1.symm.trans heq
    cases bad
  · have bad : PathInfo.bot = PathInfo.some lab bit :=
      hq.1.2.1.symm.trans hpath
    cases bad

section CutBridges

-- Match cut aliases explicitly; never normalize the underlying pipeline.
attribute [local irreducible]
  prepared checkInput checkOutput
  BirthShortDoneTerminalEntryCut.doneBeforeCheckEntryWidth
  BirthShortDoneTerminalEntryCut.doneThroughCheckEntryWidth
  BirthCheckPermitRepair.expiring BirthShortDoneTerminalObserver.birthEvent

private theorem noEqual_of_edge (l r : ExpiringAgentState psi kappa tau)
    (h : EdgeSafe hpsi h2 l r) :
    BirthCheckPermitRepairAgree.NoEqualOutcome hpsi h2 l r := by
  simpa only [BirthCheckPermitRepairAgree.NoEqualOutcome,
    BirthCheckPermitRepairAgree.AuthNoEqual, checkOutput, prepared]
    using h.2.2.2.1

private theorem consumer_noBirth (l r : ExpiringAgentState psi kappa tau)
    (h : EdgeSafe hpsi h2 l r) :
    BirthShortDoneTerminalObserver.birthEvent
      hpsi (by decide : 0 < 2) h2 l r = false := by
  have hp : ¬ PPrimeBarrierBirthGuard
      hpsi (prepared hpsi l) (prepared hpsi r) :=
    ruler_excludes_pprime hpsi (prepared hpsi l) (prepared hpsi r) h.1
  have hc : ¬ ActualCheckBirthInput hpsi (checkInput hpsi h2 l r) :=
    quiet_right_excludes_check hpsi (checkInput hpsi h2 l r) h.2.2.1
  apply birthEvent_false_of_no_input_sources
    hpsi (by decide : 0 < 2) h2 l r
  · simpa only [prepared] using hp
  · simpa only [checkInput, prepared] using hc

end CutBridges

private theorem next_ne (hn : 1 < n) (e : Fin n) :
    ring.rightNeighbor e ≠ e := by
  intro he
  have hv := congrArg Fin.val he
  change (e.val + 1) % n = e.val at hv
  have hi := e.isLt
  by_cases ht : e.val + 1 < n
  · rw [Nat.mod_eq_of_lt ht] at hv
    omega
  · have ht' : e.val + 1 = n := by omega
    rw [ht', Nat.mod_self] at hv
    omega

private theorem signal_observeCell (u : ExpiringAgentState psi kappa tau) :
    K2OutputSafety.signalView (ExpiringK2Projection.observeCell u) =
      ExpiringK2Projection.observeCell u := rfl

private theorem shadowRow_observed (l r : ExpiringAgentState psi kappa tau)
    (h : ¬ (l.core.core.leader = true ∧ r.core.core.leader = true)) :
    K2BirthDispatcher.shadowRow
        (ExpiringK2Projection.observeCell l) (ExpiringK2Projection.observeCell r) =
      LDSinkKernelC.sinkKernelC (by decide : 0 < 1)
        (ExpiringK2Projection.observeCell l) (ExpiringK2Projection.observeCell r) := by
  have hn : ¬ ((K2OutputSafety.signalView
        (ExpiringK2Projection.observeCell l)).leader = true ∧
      (K2OutputSafety.signalView
        (ExpiringK2Projection.observeCell r)).leader = true) := h
  calc
    K2BirthDispatcher.shadowRow
        (ExpiringK2Projection.observeCell l)
        (ExpiringK2Projection.observeCell r) =
      LDSinkKernelC.sinkKernelC (by decide : 0 < 1)
        (K2OutputSafety.signalView (ExpiringK2Projection.observeCell l))
        (K2OutputSafety.signalView (ExpiringK2Projection.observeCell r)) :=
      if_neg hn
    _ = _ := by rw [signal_observeCell l, signal_observeCell r]

/-- Same edge and actual R1 successor, on this candidate input only. -/
theorem observe_step_eq_raw (hn : 1 < n) (C : FC n psi kappa tau)
    (hC : CandR1 hpsi h2 ring C) (e : Fin n) :
    ExpiringK2Projection.observe (S hpsi h2 ring C e) =
      K2OutputSafety.rawStep (by decide : 0 < 1) ring
        (ExpiringK2Projection.observe C) e := by
  have hE := candidate_rows hpsi h2 ring C hC e
  have hsame : S hpsi h2 ring C e =
      BirthShortDoneTerminalConsumer.step
        hpsi (by decide : 0 < 2) h2 ring C e :=
    BirthCheckPermitRepairAgree.step1_eq hpsi h2 ring C e
      (noEqual_of_edge hpsi h2 _ _ hE)
  have ho := BirthShortDoneTerminalObserver.observe_step_of_no_birth
    hpsi (by decide : 0 < 2) h2 ring C e
    (consumer_noBirth hpsi h2 _ _ hE)
  obtain ⟨root, _, honly⟩ := candR1_unique hpsi h2 ring C hC
  have hnoboth : ¬ ((C e).core.core.leader = true ∧
      (C (ring.rightNeighbor e)).core.core.leader = true) := by
    intro hb
    exact next_ne ring hn e ((honly _ hb.2).trans (honly _ hb.1).symm)
  have hr := shadowRow_observed (C e) (C (ring.rightNeighbor e)) hnoboth
  have hraw :
      K2BirthDispatcher.shadowStep ring (ExpiringK2Projection.observe C) e =
        K2OutputSafety.rawStep (by decide : 0 < 1) ring
          (ExpiringK2Projection.observe C) e := by
    -- This lambda is the common updatePair context. Neither local row
    -- is executed, and no rewrite must match observe against observeCell.
    exact congrArg
      (fun q : AgentState 1 × AgentState 1 =>
        fun i : Fin n =>
          if i = e then q.1
          else if i = ring.rightNeighbor e then q.2
          else ExpiringK2Projection.observe C i)
      hr
  exact (congrArg
    (fun D : FC n psi kappa tau => ExpiringK2Projection.observe D)
    hsame).trans (ho.trans hraw)

private theorem observed_rowSafe (C : FC n psi kappa tau)
    (hC : CandR1 hpsi h2 ring C) :
    K2OutputSafety.RowSafe (by decide : 0 < 1) ring
      (ExpiringK2Projection.observe C) := by
  apply K2OutputSafety.rowSafe_of_outputSafe (by decide : 0 < 1) ring
  refine {
    unique_leader := ?_
    leader_label_zero := ?_
    no_nonpeaceful_bullet := ?_
    no_free_barrier := ?_
  }
  · exact candR1_unique hpsi h2 ring C hC
  · intro i _
    exact Subsingleton.elim _ _
  · exact K2PeacefulGlobal.nearest_implies_literal ring _
      (candR1_nearest_peaceful hpsi h2 ring C hC)
  · unfold noFreeBarrier
    intro e
    dsimp only
    intro hb
    exact (hb (Subsingleton.elim _ _)).elim

/-- This includes survival of the last leader, not just non-creation. -/
theorem step1_leader_eq (hn : 1 < n) (C : FC n psi kappa tau)
    (hC : CandR1 hpsi h2 ring C) (e i : Fin n) :
    (S hpsi h2 ring C e i).core.core.leader = (C i).core.core.leader := by
  have h := congrArg (fun F : Fin n → AgentState 1 => (F i).leader)
    (observe_step_eq_raw hpsi h2 ring hn C hC e)
  exact h.trans (K2OutputSafety.rawStep_leader (by decide : 0 < 1)
    ring _ (observed_rowSafe hpsi h2 ring C hC) e i)

theorem candR1_unique_step (hn : 1 < n) (C : FC n psi kappa tau)
    (hC : CandR1 hpsi h2 ring C) (e : Fin n) :
    UniqueLeaderOutput (R1LegitKernel.protocolR1 hpsi h2 kappa tau)
      n (S hpsi h2 ring C e) R1LegitKernel.isLeaderR1 := by
  obtain ⟨root, hl, hu⟩ := candR1_unique hpsi h2 ring C hC
  refine ⟨root, (step1_leader_eq hpsi h2 ring hn C hC e root).trans hl, ?_⟩
  intro i hi
  exact hu i ((step1_leader_eq hpsi h2 ring hn C hC e i).symm.trans hi)

private theorem label_eq_of_restore
    (u v : ExpiringAgentState psi kappa tau)
    (he : ExpiringK2Projection.putSignals u
      (ExpiringK2Projection.observeCell v) = v) :
    u.core.core.label = v.core.core.label := by
  -- Only abstract records occur while reducing the putSignals lens.
  have h := congrArg
    (fun z : ExpiringAgentState psi kappa tau => z.core.core.label) he
  exact h

private theorem row_old_leader_zero (l r : ExpiringAgentState psi kappa tau)
    (hE : EdgeSafe hpsi h2 l r) :
    (l.core.core.leader = true →
      (BirthCheckPermitRepair.row hpsi (by decide : 0 < 2) h2 l r).1.core.core.label = ⟨0, hpsi⟩) ∧
    (r.core.core.leader = true →
      (BirthCheckPermitRepair.row hpsi (by decide : 0 < 2) h2 l r).2.core.core.label = ⟨0, hpsi⟩) := by
  have hrow := BirthCheckPermitRepairAgree.row_eq hpsi h2 l r
    (noEqual_of_edge hpsi h2 l r hE)
  let d := BirthShortDoneTerminalHost.doneMetadataEntryWidth
    hpsi (by decide : 0 < 2) h2 l r
  have hp := BirthShortDoneTerminalConsumer.metadata_existing_leaders
    hpsi (by decide : 0 < 2) h2 l r
  have hf := BirthShortDoneTerminalHost.row_metadata_frame
    hpsi (by decide : 0 < 2) h2 l r
  constructor
  · intro hl
    have hc := congrArg
      (fun q : ExpiringAgentState psi kappa tau ×
          ExpiringAgentState psi kappa tau => q.1.core.core.label) hrow
    exact hc.trans ((label_eq_of_restore _ _ hf.1).trans
      (K2BirthLeaderNormalize.normalizeLeader_label_zero
        hpsi d.1 (hp.1 hl)))
  · intro hr
    have hc := congrArg
      (fun q : ExpiringAgentState psi kappa tau ×
          ExpiringAgentState psi kappa tau => q.2.core.core.label) hrow
    exact hc.trans ((label_eq_of_restore _ _ hf.2).trans
      (K2BirthLeaderNormalize.normalizeLeader_label_zero
        hpsi d.2 (hp.2 hr)))

private theorem protocol_step_cases
    (p : PopulationProtocol) (g : DirectedRing n)
    (C : Fin n → p.Q) (e i : Fin n) (P : p.Q → Prop)
    (hl : i = e → P ((p.transition (C e) (C (g.rightNeighbor e))).1))
    (hr : i ≠ e → i = g.rightNeighbor e →
      P ((p.transition (C e) (C (g.rightNeighbor e))).2))
    (ho : i ≠ e → i ≠ g.rightNeighbor e → P (C i)) :
    P (p.step g C e i) := by
  -- p is abstract here: these reductions cannot expose an R1 row.
  by_cases hi : i = e
  · simpa only [PopulationProtocol.step, if_pos hi] using hl hi
  · by_cases hj : i = g.rightNeighbor e
    · simpa only [PopulationProtocol.step, if_neg hi, if_pos hj]
        using hr hi hj
    · simpa only [PopulationProtocol.step, if_neg hi, if_neg hj]
        using ho hi hj

theorem root_label_zero_step (C : FC n psi kappa tau) (root : Fin n)
    (hA : CandR1At hpsi h2 ring C root) (e : Fin n) :
    (S hpsi h2 ring C e root).core.core.label = ⟨0, hpsi⟩ := by
  have hz := row_old_leader_zero hpsi h2 _ _ (hA.2.2.2.2 e)
  refine protocol_step_cases
    (BirthCheckPermitRepair.protocol hpsi (by decide : 0 < 2) h2 kappa tau)
    ring C e root (fun u => u.core.core.label = ⟨0, hpsi⟩) ?_ ?_ ?_
  · intro he
    exact hz.1 (he ▸ hA.1.1)
  · intro _ he
    exact hz.2 (he ▸ hA.1.1)
  · intro _ _
    exact hA.1.2.2.1
/-- The physical root survives at label zero, also on incident rows. -/
theorem root_anchor_step (hn : 1 < n) (C : FC n psi kappa tau)
    (root : Fin n) (hA : CandR1At hpsi h2 ring C root) (e : Fin n) :
    (S hpsi h2 ring C e root).core.core.leader = true ∧
    (∀ i, (S hpsi h2 ring C e i).core.core.leader = true → i = root) ∧
    (S hpsi h2 ring C e root).core.core.label = ⟨0, hpsi⟩ := by
  have hC : CandR1 hpsi h2 ring C := ⟨root, hA⟩
  refine ⟨(step1_leader_eq hpsi h2 ring hn C hC e root).trans hA.1.1,
    ?_, root_label_zero_step hpsi h2 ring C root hA e⟩
  intro i hi
  exact hA.1.2.1 i ((step1_leader_eq hpsi h2 ring hn C hC e i).symm.trans hi)

theorem k2Peaceful_step (hn : 1 < n) (C : FC n psi kappa tau)
    (hC : CandR1 hpsi h2 ring C) (e : Fin n) :
    K2PeacefulFinite ring (S hpsi h2 ring C e) := by
  have hp := K2PeacefulGlobal.nearest_rawStep hn ring _
    (candR1_nearest_peaceful hpsi h2 ring C hC) e
  rw [← observe_step_eq_raw hpsi h2 ring hn C hC e] at hp
  intro i hi
  obtain ⟨d, hs⟩ := hp i hi
  exact ⟨⟨d, hs.distance_lt⟩, hs.target_leader, hs.target_shield,
    fun k hk => hs.signal_zero k.val hk,
    fun k hk => hs.before_follower k.val hk⟩

/-- The imported ordinary-label theorem retains its TWO-follower premise. -/
theorem labels_step_away_root (C : FC n psi kappa tau) (root : Fin n)
    (hA : CandR1At hpsi h2 ring C root) (e : Fin n)
    (he : e ≠ root) (hr : ring.rightNeighbor e ≠ root) (i : Fin n) :
    (S hpsi h2 ring C e i).core.core.label = (C i).core.core.label := by
  have hl0 : (C e).core.core.leader = false := by
    cases hx : (C e).core.core.leader with
    | false => rfl
    | true => exact (he (hA.1.2.1 e hx)).elim
  have hr0 : (C (ring.rightNeighbor e)).core.core.leader = false := by
    cases hx : (C (ring.rightNeighbor e)).core.core.leader with
    | false => rfl
    | true => exact (hr (hA.1.2.1 _ hx)).elim
  have hE := hA.2.2.2.2 e
  have hop : BirthShortDoneTerminalOrdinaryLabelR1.PreparedOrdinaryOpen
      hpsi (C e) (C (ring.rightNeighbor e)) :=
    ⟨(hA.2.2.2.1 _).2.2.2, (hA.2.2.2.1 e).2.2.2⟩
  have hp := BirthShortDoneTerminalOrdinaryLabelR1.ordinary_row_labels_of_no_birth
    hpsi (by decide : 0 < 2) h2 _ _ hl0 hr0 hop
    (consumer_noBirth hpsi h2 _ _ hE)
  have hrow := BirthCheckPermitRepairAgree.row_eq hpsi h2 _ _
    (noEqual_of_edge hpsi h2 _ _ hE)
  have hleft : (BirthCheckPermitRepair.row hpsi (by decide : 0 < 2)
      h2 (C e) (C (ring.rightNeighbor e))).1.core.core.label =
        (C e).core.core.label :=
    (congrArg
      (fun q : ExpiringAgentState psi kappa tau ×
          ExpiringAgentState psi kappa tau => q.1.core.core.label)
      hrow).trans hp.1
  have hright : (BirthCheckPermitRepair.row hpsi (by decide : 0 < 2)
      h2 (C e) (C (ring.rightNeighbor e))).2.core.core.label =
        (C (ring.rightNeighbor e)).core.core.label :=
    (congrArg
      (fun q : ExpiringAgentState psi kappa tau ×
          ExpiringAgentState psi kappa tau => q.2.core.core.label)
      hrow).trans (hp.2.trans (hA.1.2.2.2.2.1 e hr).symm)
  refine protocol_step_cases
    (BirthCheckPermitRepair.protocol hpsi (by decide : 0 < 2) h2 kappa tau)
    ring C e i
    (fun u => u.core.core.label = (C i).core.core.label) ?_ ?_ ?_
  · intro hi
    exact hleft.trans (congrArg
      (fun j : Fin n => (C j).core.core.label) hi.symm)
  · intro _ hi
    exact hright.trans (congrArg
      (fun j : Fin n => (C j).core.core.label) hi.symm)
  · intro _ _
    rfl

theorem rootedLap_step_away_root (hn : 1 < n) (C : FC n psi kappa tau)
    (root : Fin n) (hA : CandR1At hpsi h2 ring C root) (e : Fin n)
    (he : e ≠ root) (hr : ring.rightNeighbor e ≠ root) :
    RootedLap hpsi ring (S hpsi h2 ring C e) root := by
  have hz := root_anchor_step hpsi h2 ring hn C root hA e
  have hf := labels_step_away_root hpsi h2 ring C root hA e he hr
  have hroot : S hpsi h2 ring C e root = C root :=
    BirthCheckPermitRepairLeaf.step1_other hpsi h2 ring C e root
      (Ne.symm he) (Ne.symm hr)
  refine ⟨hz.1, hz.2.1, hz.2.2, ?_, ?_, ?_, ?_⟩
  · intro d
    exact (hf (cwPos ring root d.val)).trans (hA.1.2.2.2.1 d)
  · intro f hfr
    apply Fin.ext
    exact (congrArg Fin.val (hf (ring.rightNeighbor f))).trans
      ((congrArg Fin.val (hA.1.2.2.2.2.1 f hfr)).trans
        (congrArg (fun a : Fin psi => (a.val + 1) % psi) (hf f)).symm)
  · rw [hroot]
    exact hA.1.2.2.2.2.2.1
  · rw [hroot]
    exact hA.1.2.2.2.2.2.2

/-- Zeta-reduce the let-bound neighbour before introducing the barrier. -/
theorem rootedLap_noFreeBarrier (C : FC n psi kappa tau) (root : Fin n)
    (hG : RootedLap hpsi ring C root) :
    noFreeBarrier hpsi ring (fun i => raw (C i)) := by
  unfold noFreeBarrier
  intro e
  dsimp only
  intro hb
  change (C (ring.rightNeighbor e)).core.core.leader = true
  by_cases he : ring.rightNeighbor e = root
  · rw [he]
    exact hG.1
  · exact (hb (hG.2.2.2.2.1 e he)).elim

theorem noFreeBarrier_step_away_root (hn : 1 < n)
    (C : FC n psi kappa tau) (root : Fin n)
    (hA : CandR1At hpsi h2 ring C root) (e : Fin n)
    (he : e ≠ root) (hr : ring.rightNeighbor e ≠ root) :
    noFreeBarrier hpsi ring (fun i => raw (S hpsi h2 ring C e i)) :=
  rootedLap_noFreeBarrier hpsi ring _ root
    (rootedLap_step_away_root hpsi h2 ring hn C root hA e he hr)

private theorem quiet_normalize (u : ExpiringAgentState psi kappa tau)
    (hu : AuthQuiet u.core.erase) :
    AuthQuiet (K2BirthLeaderNormalize.normalizeLeader hpsi u).core.erase := by
  unfold K2BirthLeaderNormalize.normalizeLeader
  split <;> exact hu

private theorem quiet_of_restore (u v : ExpiringAgentState psi kappa tau)
    (he : ExpiringK2Projection.putSignals u
      (ExpiringK2Projection.observeCell v) = v)
    (hv : AuthQuiet v.core.erase) : AuthQuiet u.core.erase := by
  have h := congrArg (fun z : ExpiringAgentState psi kappa tau =>
    AuthQuiet z.core.erase) he
  change AuthQuiet u.core.erase = AuthQuiet v.core.erase at h
  exact Eq.mpr h hv

/-- Transport the actual expiry-cut clause through the physical tail. -/
theorem edgeSafe_row_quiet (l r : ExpiringAgentState psi kappa tau)
    (hE : EdgeSafe hpsi h2 l r) :
    AuthQuiet (BirthCheckPermitRepair.row
      hpsi (by decide : 0 < 2) h2 l r).1.core.erase ∧
    AuthQuiet (BirthCheckPermitRepair.row
      hpsi (by decide : 0 < 2) h2 l r).2.core.erase := by
  rcases hE with ⟨_, _, _, _, _, _, _, hq⟩
  let q := BirthCheckPermitRepair.expiring hpsi (by decide : 0 < 2) h2 l r
  let a := K2BirthLeaderNormalize.normalizeLeader hpsi q.1
  let b := K2BirthLeaderNormalize.normalizeLeader hpsi q.2
  have ha : AuthQuiet a.core.erase := quiet_normalize hpsi q.1 hq.1
  have hb : AuthQuiet b.core.erase := quiet_normalize hpsi q.2 hq.2
  have hf := K2BirthDispatcher.finalPhysical_frame hpsi l r a b
  have ht :
      AuthQuiet (K2BirthDispatcher.finalPhysical hpsi l r a b).1.core.erase ∧
      AuthQuiet (K2BirthDispatcher.finalPhysical hpsi l r a b).2.core.erase :=
    ⟨quiet_of_restore _ _ hf.1 ha, quiet_of_restore _ _ hf.2 hb⟩
  -- Open only the whole-pair row wrapper, not its projected fields.
  have he : BirthCheckPermitRepair.row hpsi (by decide : 0 < 2) h2 l r =
      K2BirthDispatcher.finalPhysical hpsi l r a b := rfl
  exact Eq.mpr
    (congrArg
      (fun z : ExpiringAgentState psi kappa tau ×
          ExpiringAgentState psi kappa tau =>
        AuthQuiet z.1.core.erase ∧ AuthQuiet z.2.core.erase)
      he) ht

theorem step1_authQuiet (C : FC n psi kappa tau)
    (hC : CandR1 hpsi h2 ring C) (e i : Fin n) :
    AuthQuiet (S hpsi h2 ring C e i).core.erase := by
  obtain ⟨root, hA⟩ := hC
  have hq := edgeSafe_row_quiet hpsi h2 _ _ (hA.2.2.2.2 e)
  exact protocol_step_cases
    (BirthCheckPermitRepair.protocol hpsi (by decide : 0 < 2) h2 kappa tau)
    ring C e i (fun u => AuthQuiet u.core.erase)
    (fun _ => hq.1)
    (fun _ _ => hq.2)
    (fun _ _ => (hA.2.2.2.1 i).1)

theorem step1_no_stored_permit (C : FC n psi kappa tau)
    (hC : CandR1 hpsi h2 ring C) (e i : Fin n) :
    (S hpsi h2 ring C e i).core.path0Crossed = false :=
  (step1_authQuiet hpsi h2 ring C hC e i).2

private theorem no_pending_of_path2_none (u : AgentState psi)
    (hp : u.path2 = none) : pendingTerminalDisposal hpsi u = false := by
  simp only [pendingTerminalDisposal, hp]

theorem step1_no_pending_disposal (C : FC n psi kappa tau)
    (hC : CandR1 hpsi h2 ring C) (e i : Fin n) :
    pendingTerminalDisposal hpsi (raw (S hpsi h2 ring C e i)) = false := by
  exact no_pending_of_path2_none hpsi (raw (S hpsi h2 ring C e i))
    (step1_authQuiet hpsi h2 ring C hC e i).1.2.2.1
/-- Disjointness of both endpoint sets, not just distinct edge indices. -/
def DisjointEdges (e f : Fin n) : Prop :=
  f ≠ e ∧ f ≠ ring.rightNeighbor e ∧
  ring.rightNeighbor f ≠ e ∧
  ring.rightNeighbor f ≠ ring.rightNeighbor e

theorem classE_step_disjoint (C : FC n psi kappa tau)
    (hC : CandR1 hpsi h2 ring C) (e f : Fin n)
    (hd : DisjointEdges ring e f) :
    ¬ ClassE hpsi h2 (S hpsi h2 ring C e f)
      (S hpsi h2 ring C e (ring.rightNeighbor f)) := by
  rcases hd with ⟨h1, h2', h3, h4⟩
  have hl := BirthCheckPermitRepairLeaf.step1_other hpsi h2 ring C e f h1 h2'
  have hr := BirthCheckPermitRepairLeaf.step1_other hpsi h2 ring C e
    (ring.rightNeighbor f) h3 h4
  change ¬ ClassE hpsi h2
    (BirthCheckPermitRepairLeaf.step1 hpsi h2 ring C e f)
    (BirthCheckPermitRepairLeaf.step1 hpsi h2 ring C e (ring.rightNeighbor f))
  rw [hl, hr]
  exact candR1_not_classE hpsi h2 ring C hC f

/- PLAN: WAIT/GEN/DONE run before the next CHECK. Boundary neutrality
alone does not prove neutrality at that computed cut. Only overlapping
edges remain after classE_step_disjoint; those need the actual join proof. -/
def ClassEOverlapObligation : Prop :=
  ∀ C : FC n psi kappa tau, CandR1 hpsi h2 ring C → ∀ e f,
    ¬ DisjointEdges ring e f →
    ¬ ClassE hpsi h2 (S hpsi h2 ring C e f)
      (S hpsi h2 ring C e (ring.rightNeighbor f))

theorem classE_step_of_overlap
    (hO : ClassEOverlapObligation (kappa := kappa) (tau := tau) hpsi h2 ring)
    (C : FC n psi kappa tau) (hC : CandR1 hpsi h2 ring C) (e f : Fin n) :
    ¬ ClassE hpsi h2 (S hpsi h2 ring C e f)
      (S hpsi h2 ring C e (ring.rightNeighbor f)) := by
  by_cases hd : DisjointEdges ring e f
  · exact classE_step_disjoint hpsi h2 ring C hC e f hd
  · exact hO C hC e f hd

section WriterCuts

-- Expose only the suffix-to-writer connection. The writer and its inputs
-- remain opaque during elaboration; no symbolic execution is requested.
attribute [local irreducible]
  prepared checkOutput writerInput checkedSuffix
  BirthShortDoneTerminalEntryCut.doneThroughCheckEntryWidth
  BirthShortDoneCuts.beforeWriteWidth
  BirthStationaryWrite.stationaryPersistentAuthorizedRow
  BirthCheckPermitRepair.row BirthCheckPermitRepair.expiring

private theorem checkedSuffix_eq_writer
    (l r : ExpiringAgentState psi kappa tau) :
    checkedSuffix hpsi h2 l r =
      let w := writerInput hpsi h2 l r
      BirthStationaryWrite.stationaryPersistentAuthorizedRow hpsi w.1 w.2 := by
  simp only [checkedSuffix, writerInput,
    BirthShortDoneCuts.afterCheckMetadataWidth]

private theorem writer_cut_bit_silent
    (l r : ExpiringAgentState psi kappa tau) (hE : EdgeSafe hpsi h2 l r) :
    (checkedSuffix hpsi h2 l r).1.core.bit =
        (writerInput hpsi h2 l r).1.core.bit ∧
      (checkedSuffix hpsi h2 l r).2.core.bit =
        (writerInput hpsi h2 l r).2.core.bit :=
  hE.2.2.2.2.2.2.1

/-- The stored exact bit frame applies to the actual persistent writer. -/
theorem writer_stage_bit_silent (C : FC n psi kappa tau)
    (hC : CandR1 hpsi h2 ring C) (e : Fin n) :
    let w := writerInput hpsi h2 (C e) (C (ring.rightNeighbor e))
    let z := BirthStationaryWrite.stationaryPersistentAuthorizedRow hpsi w.1 w.2
    z.1.core.bit = w.1.core.bit ∧ z.2.core.bit = w.2.core.bit := by
  have hb := writer_cut_bit_silent hpsi h2 _ _
    (candidate_rows hpsi h2 ring C hC e)
  simpa only [checkedSuffix_eq_writer] using hb

/- PLAN: The writer cut is silent. The outside stages still require the
pre-writer bit frame and mark/reify/expiry/normalization/physical-tail
bit frame below. A four-field K2 observation cannot supply a bit frame. -/
def WriterOuterFrames (C : FC n psi kappa tau) (e : Fin n) : Prop :=
  let l := C e
  let r := C (ring.rightNeighbor e)
  let w := writerInput hpsi h2 l r
  let z := checkedSuffix hpsi h2 l r
  let q := BirthCheckPermitRepair.row hpsi (by decide : 0 < 2) h2 l r
  (w.1.core.bit = l.core.core.bit ∧ w.2.core.bit = r.core.core.bit) ∧
  (q.1.core.core.bit = z.1.core.bit ∧ q.2.core.core.bit = z.2.core.bit)

def WriterOuterFrameObligation : Prop :=
  ∀ C : FC n psi kappa tau, CandR1 hpsi h2 ring C →
    ∀ e, WriterOuterFrames hpsi h2 ring C e

theorem step1_bit_eq_of_outer_frames
    (hF : WriterOuterFrameObligation (kappa := kappa) (tau := tau) hpsi h2 ring)
    (C : FC n psi kappa tau) (hC : CandR1 hpsi h2 ring C) (e i : Fin n) :
    (S hpsi h2 ring C e i).core.core.bit = (C i).core.core.bit := by
  have hf := hF C hC e
  have hw := writer_cut_bit_silent hpsi h2 _ _
    (candidate_rows hpsi h2 ring C hC e)
  have hl : (BirthCheckPermitRepair.row hpsi (by decide : 0 < 2) h2
      (C e) (C (ring.rightNeighbor e))).1.core.core.bit = (C e).core.core.bit :=
    hf.2.1.trans (hw.1.trans hf.1.1)
  have hr : (BirthCheckPermitRepair.row hpsi (by decide : 0 < 2) h2
      (C e) (C (ring.rightNeighbor e))).2.core.core.bit =
        (C (ring.rightNeighbor e)).core.core.bit :=
    hf.2.2.trans (hw.2.trans hf.1.2)
  refine protocol_step_cases
    (BirthCheckPermitRepair.protocol hpsi (by decide : 0 < 2) h2 kappa tau)
    ring C e i
    (fun u => u.core.core.bit = (C i).core.core.bit) ?_ ?_ ?_
  · intro hi
    exact hl.trans (congrArg
      (fun j : Fin n => (C j).core.core.bit) hi.symm)
  · intro _ hi
    exact hr.trans (congrArg
      (fun j : Fin n => (C j).core.core.bit) hi.symm)
  · intro _ _
    rfl

end WriterCuts

/- PLAN: The root anchor is proved, but the imported ordinary-label
lemma assumes two followers. The leader-initiated stagewise label frame
and transport of the root's shield/zero signal remain separate premises. -/
def OutgoingRootedObligation : Prop :=
  ∀ (C : FC n psi kappa tau) (root : Fin n),
    CandR1At hpsi h2 ring C root → ∀ e, e = root →
      RootedLap hpsi ring (S hpsi h2 ring C e) root

/- PLAN: Incoming-root service permits a closing label defect. Prove the
predecessor-label frame and root protection through the leader wall and
metadata; do not replace this with all-edge alignment or divisibility. -/
def IncomingRootedObligation : Prop :=
  ∀ (C : FC n psi kappa tau) (root : Fin n),
    CandR1At hpsi h2 ring C root → ∀ e, ring.rightNeighbor e = root →
      RootedLap hpsi ring (S hpsi h2 ring C e) root

theorem rootedLap_step_of_incident_obligations (hn : 1 < n)
    (ho : OutgoingRootedObligation (kappa := kappa) (tau := tau) hpsi h2 ring)
    (hi : IncomingRootedObligation (kappa := kappa) (tau := tau) hpsi h2 ring)
    (C : FC n psi kappa tau) (root : Fin n)
    (hA : CandR1At hpsi h2 ring C root) (e : Fin n) :
    RootedLap hpsi ring (S hpsi h2 ring C e) root := by
  by_cases he : e = root
  · exact ho C root hA e he
  · by_cases hr : ring.rightNeighbor e = root
    · exact hi C root hA e hr
    · exact rootedLap_step_away_root hpsi h2 ring hn C root hA e he hr

/- PLAN: After a complete bit frame, transport PositivePeak through its
actual groupID fold. A future live-writer extension instead requires
an invariant on changing current IDs, not an assertion that they freeze. -/
def PeakPreservationObligation : Prop :=
  ∀ (C : FC n psi kappa tau) (root : Fin n),
    CandR1At hpsi h2 ring C root → ∀ e,
      PositivePeak ring (S hpsi h2 ring C e) root

/- PLAN: Reevaluate every next-row cut on the actual successor. Boundary
AuthQuiet does not imply the next prepared ruler, neutral CHECK inputs,
no-equal result, writer-input dormancy, or expiry-neutrality checks. -/
def EdgeSafePreservationObligation : Prop :=
  ∀ C : FC n psi kappa tau, CandR1 hpsi h2 ring C → ∀ e f,
    EdgeSafe hpsi h2 (S hpsi h2 ring C e f)
      (S hpsi h2 ring C e (ring.rightNeighbor f))

/- PLAN: This obligation is contradicted by the separate signal_ws ->
gen_ws counterexample in R1CandidateNotClosed. Bit silence in the current
writer stage is not preservation of writer dormancy on the successor. -/
def WriterDormancyObligation : Prop :=
  ∀ C : FC n psi kappa tau, CandR1 hpsi h2 ring C → ∀ e i,
    WriterDormant (raw (S hpsi h2 ring C e i))

/- PLAN: The full successor has AuthQuiet and no pending disposal above.
The remaining bridge must carry its empty path through preparation and
normalizeDeletion to discharge deletionActive=false on that successor. -/
def PreparedDeletionObligation : Prop :=
  ∀ C : FC n psi kappa tau, CandR1 hpsi h2 ring C → ∀ e i,
    PPLLLeaderCreationCleanupRepair.deletionActive
      (prepared hpsi (S hpsi h2 ring C e i)) = false

/- PLAN
Do not prove candR1_closed for the unchanged quiet predicate. File 1
isolates its finite escape, independently of this generic proof file.

The obligations above remain explicit Props, not axioms or facts.
A wider candidate must admit writer activation and the subsequent live
writer phases, then prove their actual CHECK, ID, disposal, and expiry
joins. None of these conditional lemmas assumes a future-word kernel,
proves entry, or transfers safety to the final B9+R1 composition.
-/

end R1CandidateClosure
