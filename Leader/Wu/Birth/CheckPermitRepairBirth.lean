import Leader.Wu.Birth.CheckChainRow
import Leader.Wu.Birth.ShortDoneTerminalObserver
import Leader.Wu.Elimination.GapClosure
import Leader.Wu.Birth.ShortDoneTerminalBirthPhysical

set_option autoImplicit false

/-! # A CHECK birth input on the actual R1 row creates a physical leader

The K2 tail helpers are copies of the private helpers of `BirthShortDoneTerminalBirthPhysical` (same statements
and proofs), so that this module does not change an accepted file.  `r1_expiring_observation` relates the
observed K2 cells of the R1 expiring layer to the authorized R1 output; `r1_row_physical_leader_of_input` is the
R1 analogue of `physical_leader_of_prepared_ordinary_check_input`. -/

namespace BirthCheckPermitRepairBirth

open PPLL PPLLResearchFormulation PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
  PPLLLeaderCreationCleanupRepair BirthSigMoveDisposalRepair BirthShortDoneTerminalEntryCut
open K2BirthDispatcher ExpiringK2Projection LDSinkKernelC K2BirthLeaderNormalize

set_option Elab.async false
set_option pp.structureInstances false

variable {ψ κ τ : Nat}

/-- A left leader protected by a true shield cannot be deleted by the K2 row
when the responder is a follower.  This is the exact case produced by a
left-only `initializeNewborn`. -/
theorem r1_k2_left_protected_leader
    (hψ : 0 < ψ) (l r : ExpiringAgentState ψ κ τ)
    (hl : l.core.core.leader = true)
    (hs : l.core.core.shield = true)
    (hr : r.core.core.leader = false) :
    (ExpiringK2Projection.row hψ l r).1.core.core.leader = true := by
  have ho := ExpiringK2Projection.observe_row hψ l r
  have hl' : (ExpiringK2Projection.observeCell l).leader = true := hl
  have hs' : (ExpiringK2Projection.observeCell l).shield = true := hs
  have hr' : (ExpiringK2Projection.observeCell r).leader = false := hr
  have hk :
      (sinkKernelC (by decide : 0 < 1)
        (ExpiringK2Projection.observeCell l)
        (ExpiringK2Projection.observeCell r)).1.leader = true := by
    cases h :
        (sinkKernelC (by decide : 0 < 1)
          (ExpiringK2Projection.observeCell l)
          (ExpiringK2Projection.observeCell r)).1.leader with
    | true => rfl
    | false =>
        have hd := (K2GlobalGapClosure.kernel_delete_iff
          (by decide : 0 < 1)
          (ExpiringK2Projection.observeCell l)
          (ExpiringK2Projection.observeCell r) hl' hr').mp h
        have hbad : (true : Bool) = false := hs'.symm.trans hd.1
        cases hbad
  have he := congrArg
    (fun q : AgentState 1 × AgentState 1 => q.1.leader) ho
  change (ExpiringK2Projection.row hψ l r).1.core.core.leader =
    (sinkKernelC (by decide : 0 < 1)
      (ExpiringK2Projection.observeCell l)
      (ExpiringK2Projection.observeCell r)).1.leader at he
  exact he.trans hk

/-- The responder leader bit is framed exactly by the K2 C-kernel. -/
theorem r1_k2_right_leader
    (hψ : 0 < ψ) (l r : ExpiringAgentState ψ κ τ)
    (hr : r.core.core.leader = true) :
    (ExpiringK2Projection.row hψ l r).2.core.core.leader = true := by
  have ho := ExpiringK2Projection.observe_row hψ l r
  have hk := LDSinkTwoGapEpochSuccessor.kernelC_right_leader_eq
    (by decide : 0 < 1)
    (ExpiringK2Projection.observeCell l)
    (ExpiringK2Projection.observeCell r)
  have hr' : (ExpiringK2Projection.observeCell r).leader = true := hr
  have he := congrArg
    (fun q : AgentState 1 × AgentState 1 => q.2.leader) ho
  change (ExpiringK2Projection.row hψ l r).2.core.core.leader =
    (sinkKernelC (by decide : 0 < 1)
      (ExpiringK2Projection.observeCell l)
      (ExpiringK2Projection.observeCell r)).2.leader at he
  exact he.trans (hk.trans hr')

/-- A true newborn bit on either role survives the complete physical tail as
at least one physical leader. -/
theorem r1_finalPhysical_birth_has_leader
    (hψ : 0 < ψ)
    (oldL oldR metaL metaR : ExpiringAgentState ψ κ τ)
    (hb : K2BirthDispatcher.newborn oldL metaL = true ∨
      K2BirthDispatcher.newborn oldR metaR = true) :
    (K2BirthDispatcher.finalPhysical hψ oldL oldR metaL metaR).1.core.core.leader = true ∨
      (K2BirthDispatcher.finalPhysical hψ oldL oldR metaL metaR).2.core.core.leader = true := by
  let iL := K2BirthDispatcher.initializeNewborn oldL metaL
  let iR := K2BirthDispatcher.initializeNewborn oldR metaR
  change
    (K2BirthDispatcher.collisionRow hψ iL iR).1.core.core.leader = true ∨
      (K2BirthDispatcher.collisionRow hψ iL iR).2.core.core.leader = true
  rcases hb with hbL | hbR
  · have hx := K2BirthDispatcher.initializeNewborn_exact oldL metaL hbL
    have hL : iL.core.core.leader = true := hx.2.1
    have hS : iL.core.core.shield = true := hx.2.2.2.1
    by_cases hR : iR.core.core.leader = true
    · exact Or.inr
        (K2BirthDispatcher.collisionRow_of_both hψ iL iR hL hR).2.1
    · have hRf : iR.core.core.leader = false := by
        cases h : iR.core.core.leader with
        | false => rfl
        | true => exact (hR h).elim
      have hnot : ¬ (iL.core.core.leader = true ∧ iR.core.core.leader = true) :=
        fun h => hR h.2
      rw [K2BirthDispatcher.collisionRow_of_not_both hψ iL iR hnot]
      exact Or.inl (r1_k2_left_protected_leader hψ iL iR hL hS hRf)
  · have hx := K2BirthDispatcher.initializeNewborn_exact oldR metaR hbR
    have hR : iR.core.core.leader = true := hx.2.1
    by_cases hL : iL.core.core.leader = true
    · exact Or.inr
        (K2BirthDispatcher.collisionRow_of_both hψ iL iR hL hR).2.1
    · have hnot : ¬ (iL.core.core.leader = true ∧ iR.core.core.leader = true) :=
        fun h => hL h.1
      rw [K2BirthDispatcher.collisionRow_of_not_both hψ iL iR hnot]
      exact Or.inr (r1_k2_right_leader hψ iL iR hR)


theorem r1_bounded_erase (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (l r : AuthorizedBoundedAgentState ψ κ) :
    ((BirthCheckPermitRepair.bounded hψ (by decide : 0 < 2) h2 l r).1.erase,
      (BirthCheckPermitRepair.bounded hψ (by decide : 0 < 2) h2 l r).2.erase) =
      BirthCheckPermitRepair.authorized hψ (by decide : 0 < 2) h2 κ l.erase r.erase := by
  unfold BirthCheckPermitRepair.bounded
  simp only [AuthorizedBoundedAgentState.erase, BoundedAgentState.erase_ofDomain]

theorem r1_expiring_observation (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (l r : ExpiringAgentState ψ κ τ) :
    (observeCell (BirthCheckPermitRepair.expiring hψ (by decide : 0 < 2) h2 l r).1,
      observeCell (BirthCheckPermitRepair.expiring hψ (by decide : 0 < 2) h2 l r).2) =
      authSignalPair (BirthCheckPermitRepair.authorized hψ (by decide : 0 < 2) h2 κ
        (prepareExpiringDisposal hψ l).core.erase (prepareExpiringDisposal hψ r).core.erase) := by
  let l0 := prepareExpiringDisposal hψ l
  let r0 := prepareExpiringDisposal hψ r
  let q := BirthCheckPermitRepair.bounded hψ (by decide : 0 < 2) h2 l0.core r0.core
  have he := congrArg authSignalPair (r1_bounded_erase hψ h2 l0.core r0.core)
  have hx :
      (observeCell (deletionPriorityExpireOne τ l0 ⟨q.1, l0.stall⟩),
        observeCell (deletionPriorityExpireOne τ r0 ⟨q.2, r0.stall⟩)) =
      (observeCell (⟨q.1, l0.stall⟩ : ExpiringAgentState ψ κ τ),
        observeCell (⟨q.2, r0.stall⟩ : ExpiringAgentState ψ κ τ)) :=
    Prod.ext (priority_expiry_observation l0 ⟨q.1, l0.stall⟩)
      (priority_expiry_observation r0 ⟨q.2, r0.stall⟩)
  unfold BirthCheckPermitRepair.expiring
  exact hx.trans he

/-- A follower birth input at the actual CHECK cut of the prepared, normalized, deletion-free R1 row gives a
physical leader on the R1 row. -/
theorem r1_row_physical_leader_of_input (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (l r : ExpiringAgentState ψ κ τ)
    (hrDeletion : deletionActive (normalizeDeletion (prepareExpiringDisposal hψ r).core.erase) = false)
    (hlDeletion : deletionActive (normalizeDeletion (prepareExpiringDisposal hψ l).core.erase) = false)
    (hrFollower : r.core.core.leader = false)
    (hcheck : BirthShortDoneTerminalCheckInputSources.ActualCheckBirthInput hψ
      (doneBeforeCheckEntryWidth hψ (by decide : 0 < 2) h2 κ
        (normalizeDeletion (prepareExpiringDisposal hψ l).core.erase)
        (normalizeDeletion (prepareExpiringDisposal hψ r).core.erase))) :
    (BirthCheckPermitRepair.row hψ (by decide : 0 < 2) h2 l r).1.core.core.leader = true ∨
      (BirthCheckPermitRepair.row hψ (by decide : 0 < 2) h2 l r).2.core.core.leader = true := by
  have hord := BirthCheckChainR1.ordinary_right_leader_of_input hψ (by decide : 0 < 2) h2 κ _ _ hcheck
  have hbranch : BirthCheckPermitRepair.authorized hψ (by decide : 0 < 2) h2 κ
      (prepareExpiringDisposal hψ l).core.erase (prepareExpiringDisposal hψ r).core.erase =
      BirthCheckPermitRepair.ordinary hψ (by decide : 0 < 2) h2 κ
        (normalizeDeletion (prepareExpiringDisposal hψ l).core.erase)
        (normalizeDeletion (prepareExpiringDisposal hψ r).core.erase) := by
    unfold BirthCheckPermitRepair.authorized
    simp only [hrDeletion, hlDeletion, Bool.false_eq_true, if_false]
  have ho := r1_expiring_observation (κ := κ) (τ := τ) hψ h2 l r
  rw [hbranch] at ho
  have hleader : (BirthCheckPermitRepair.expiring hψ (by decide : 0 < 2) h2 l r).2.core.core.leader = true := by
    have := congrArg (fun z : AgentState 1 × AgentState 1 => z.2.leader) ho
    exact this.trans hord
  let q := BirthCheckPermitRepair.expiring hψ (by decide : 0 < 2) h2 l r
  have hnorm : (normalizeLeader hψ q.2).core.core.leader = true := by
    have := congrArg AgentState.leader (normalizeLeader_observation hψ q.2)
    exact this.trans hleader
  have hb : newborn r (normalizeLeader hψ q.2) = true := by
    unfold newborn; rw [hrFollower, hnorm]; rfl
  exact r1_finalPhysical_birth_has_leader hψ l r _ _ (Or.inr hb)

theorem prepare_identity (hψ : 0 < ψ) (u : ExpiringAgentState ψ κ τ) (h : u.core.erase.core.path2 = none) :
    prepareExpiringDisposal hψ u = u := by
  unfold prepareExpiringDisposal
  rw [prepareBoundedDisposal_eq_of_clear hψ u.core (by simp [pendingTerminalDisposal, h])]

theorem normalize_identity (u : AuthorizedAgentState ψ) (h : u.core.state ≠ .eliminate_signal) :
    normalizeDeletion u = u := by
  simp [normalizeDeletion, h]

theorem deletion_inactive (u : AuthorizedAgentState ψ) (h : u.core.state ≠ .eliminate_signal) :
    deletionActive u = false := by
  simp [deletionActive, h]

/-- A chain-ready terminal edge on the actual R1 row: the label psi-2 initiator is `equal` and the terminal
responder is a check-open matching carrier (clean registers), so the R1 row output has a physical leader. -/
theorem r1_terminal_edge_leader (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (l r : ExpiringAgentState ψ κ τ) (i bl : Nat)
    (hcons : r.core.erase.core.label = ⟨(l.core.erase.core.label.val + 1) % ψ, Nat.mod_lt _ hψ⟩)
    (hll : l.core.erase.core.leader = false) (hrl : r.core.erase.core.leader = false)
    (hlp : l.core.erase.core.path = .some i bl) (hlab : l.core.erase.core.label.val = i) (hterm : i + 1 = ψ - 1)
    (hrm : BirthCheckChainR1.CheckOpenMatch r.core.erase.core) (hrlab : r.core.erase.core.label.val = i + 1)
    (hleq : l.core.erase.core.state = .equal) (hlp2 : l.core.erase.core.path2 = none)
    (hrpr : r.core.erase.core.state ≠ .produce) (hrdn : r.core.erase.core.state ≠ .done)
    (hrel : r.core.erase.core.state ≠ .eliminate_signal)
    (hrt : r.core.erase.core.state ≠ .toss) (hrc : r.core.erase.core.state ≠ .congest)
    (hlr : l.core.erase.core.reset_cmd = false) (hrr : r.core.erase.core.reset_cmd = false)
    (hl4 : i = 0 → ∀ p, l.core.erase.core.path4 = some p → p.1 ≠ -1)
    (hr5 : ∀ p, r.core.erase.core.path5 = some p → p.1 ≠ -1) :
    (BirthCheckPermitRepair.row hψ (by decide : 0 < 2) h2 l r).1.core.core.leader = true ∨
      (BirthCheckPermitRepair.row hψ (by decide : 0 < 2) h2 l r).2.core.core.leader = true := by
  have hlel : l.core.erase.core.state ≠ .eliminate_signal := by rw [hleq]; decide
  have hpl := prepare_identity hψ l hlp2
  have hpr := prepare_identity hψ r hrm.path2
  have hnl := normalize_identity l.core.erase hlel
  have hnr := normalize_identity r.core.erase hrel
  apply r1_row_physical_leader_of_input hψ h2 l r
  · rw [hpr, hnr]; exact deletion_inactive _ hrel
  · rw [hpl, hnl]; exact deletion_inactive _ hlel
  · exact hrl
  · rw [hpl, hpr, hnl, hnr]
    exact BirthCheckChainR1.terminal_birth_input hψ h2 κ l.core.erase r.core.erase i bl hcons hll hrl hlp hlab hterm
      hrm hrlab hleq hlp2 hrpr hrdn hrel hrt hrc hlr hrr hl4 hr5

end BirthCheckPermitRepairBirth
