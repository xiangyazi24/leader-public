import Leader.Wu.Birth.CheckPermitRepairBirth
import Leader.Wu.Birth.CountAlongNoBirth
import Leader.Wu.Splice.OrdinaryLeftLeaderFrame

set_option autoImplicit false

/-! # CHECK chain rows lifted to the actual R1 row output

`BirthCheckChainR1Row` states the first and intermediate CHECK chain rows on the ordinary branch.  This module
frames the rest of the actual R1 row (disposal preparation, deletion normalization, reification, path expiry
with a positive stall, leader normalization and the final physical tail) around those conclusions, so that the
chain view (state `equal`, path, empty `path2`, label, follower) holds on the erased cores of the R1 row output. -/

namespace BirthCheckPermitRepairRowLift

open PPLL PPLLResearchFormulation PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
  PPLLLeaderCreationCleanupRepair BirthSigMoveDisposalRepair BirthShortDoneTerminalEntryCut
open K2BirthDispatcher ExpiringK2Projection LDSinkKernelC K2BirthLeaderNormalize
open BirthCheckPermitRepairBirth

set_option Elab.async false
set_option pp.structureInstances false

variable {ψ κ τ : Nat}

/-- With a positive stall on the old cell, the deletion-priority path expiry keeps the computed core. -/
theorem expire_core_of_stall (old out : ExpiringAgentState ψ κ τ) (h : old.stall.val ≠ 0) :
    (deletionPriorityExpireOne τ old out).core = out.core := by
  unfold deletionPriorityExpireOne PPLLPathStallComparisonRepair.pathExpireOne
  by_cases h1 : deletionActive out.core.erase = true
  · rw [if_pos h1]
  · by_cases h2 : PPLLPathStallComparisonRepair.PathProgressView.ofState out.core ≠
        PPLLPathStallComparisonRepair.PathProgressView.ofState old.core
    · rw [if_neg h1, if_pos h2]
    · rw [if_neg h1, if_neg h2, dif_neg h]

/-- Two cells with equal non-K2 parts agree on every comparison field of their erased cores. -/
theorem nonK2_fields (a b : ExpiringAgentState ψ κ τ) (h : nonK2 a = nonK2 b) :
    a.core.erase.core.state = b.core.erase.core.state ∧ a.core.erase.core.path = b.core.erase.core.path ∧
      a.core.erase.core.path2 = b.core.erase.core.path2 ∧ a.core.erase.core.label = b.core.erase.core.label ∧
      a.core.erase.core.bit = b.core.erase.core.bit ∧ a.core.erase.core.reset_cmd = b.core.erase.core.reset_cmd ∧
      a.core.erase.core.path4 = b.core.erase.core.path4 ∧ a.core.erase.core.path5 = b.core.erase.core.path5 ∧
      a.core.path0Crossed = b.core.path0Crossed := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hh := congrArg (fun u : ExpiringAgentState ψ κ τ => u.core.erase.core.state) h; exact hh
  · have hh := congrArg (fun u : ExpiringAgentState ψ κ τ => u.core.erase.core.path) h; exact hh
  · have hh := congrArg (fun u : ExpiringAgentState ψ κ τ => u.core.erase.core.path2) h; exact hh
  · have hh := congrArg (fun u : ExpiringAgentState ψ κ τ => u.core.erase.core.label) h; exact hh
  · have hh := congrArg (fun u : ExpiringAgentState ψ κ τ => u.core.erase.core.bit) h; exact hh
  · have hh := congrArg (fun u : ExpiringAgentState ψ κ τ => u.core.erase.core.reset_cmd) h; exact hh
  · have hh := congrArg (fun u : ExpiringAgentState ψ κ τ => u.core.erase.core.path4) h; exact hh
  · have hh := congrArg (fun u : ExpiringAgentState ψ κ τ => u.core.erase.core.path5) h; exact hh
  · have hh := congrArg (fun u : ExpiringAgentState ψ κ τ => u.core.path0Crossed) h; exact hh

theorem normalizeLeader_of_follower (hψ : 0 < ψ) (q : ExpiringAgentState ψ κ τ)
    (h : q.core.core.leader = false) : normalizeLeader hψ q = q := by
  simp [normalizeLeader, h]

/-- A follower responder metadata stays a follower through the final physical tail. -/
theorem finalPhysical_right_follower (hψ : 0 < ψ) (oldL oldR metaL metaR : ExpiringAgentState ψ κ τ)
    (h : metaR.core.core.leader = false) :
    (finalPhysical hψ oldL oldR metaL metaR).2.core.core.leader = false := by
  have hb : newborn oldR metaR = false := by unfold newborn; rw [h]; exact Bool.and_false _
  unfold finalPhysical
  rw [initializeNewborn_of_false oldR metaR hb]
  generalize initializeNewborn oldL metaL = iL
  have hnot : ¬ (iL.core.core.leader = true ∧ metaR.core.core.leader = true) := by
    intro hh; rw [h] at hh; exact Bool.false_ne_true hh.2
  rw [collisionRow_of_not_both hψ iL metaR hnot]
  have ho := congrArg (fun q : AgentState 1 × AgentState 1 => q.2.leader) (observe_row hψ iL metaR)
  have hk := LDSinkTwoGapEpochSuccessor.kernelC_right_leader_eq (by decide : 0 < 1) (observeCell iL) (observeCell metaR)
  have hr' : (observeCell metaR).leader = false := h
  exact ho.trans (hk.trans hr')

/-- A follower initiator metadata stays a follower when the responder metadata is also a follower. -/
theorem finalPhysical_left_follower (hψ : 0 < ψ) (oldL oldR metaL metaR : ExpiringAgentState ψ κ τ)
    (hL : metaL.core.core.leader = false) (hR : metaR.core.core.leader = false) :
    (finalPhysical hψ oldL oldR metaL metaR).1.core.core.leader = false := by
  have hbL : newborn oldL metaL = false := by unfold newborn; rw [hL]; exact Bool.and_false _
  have hbR : newborn oldR metaR = false := by unfold newborn; rw [hR]; exact Bool.and_false _
  unfold finalPhysical
  rw [initializeNewborn_of_false oldL metaL hbL, initializeNewborn_of_false oldR metaR hbR]
  have hnot : ¬ (metaL.core.core.leader = true ∧ metaR.core.core.leader = true) := by
    intro hh; rw [hL] at hh; exact Bool.false_ne_true hh.1
  rw [collisionRow_of_not_both hψ metaL metaR hnot]
  have ho := congrArg (fun q : AgentState 1 × AgentState 1 => q.1.leader) (observe_row hψ metaL metaR)
  have hk := LDSinkTwoGapEpochSuccessor.kernelC_left_follower (by decide : 0 < 1) (observeCell metaL) (observeCell metaR) hL
  exact ho.trans hk

/-- On clean, deletion-free carriers the authorized R1 branch is the ordinary branch on the erased cores. -/
theorem authorized_eq_ordinary (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (l r : AuthorizedAgentState ψ)
    (hlel : l.core.state ≠ .eliminate_signal) (hrel : r.core.state ≠ .eliminate_signal) :
    BirthCheckPermitRepair.authorized hψ (by decide : 0 < 2) h2 κ l r =
      BirthCheckPermitRepair.ordinary hψ (by decide : 0 < 2) h2 κ l r := by
  unfold BirthCheckPermitRepair.authorized
  simp only [normalize_identity l hlel, normalize_identity r hrel, deletion_inactive r hrel,
    deletion_inactive l hlel, Bool.false_eq_true, if_false]

/-- The R1 expiring layer on clean, deletion-free carriers: a positive stall keeps the ordinary output core. -/
theorem expiring_right_erase (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (l r : ExpiringAgentState ψ κ τ)
    (hlp2 : l.core.erase.core.path2 = none) (hrp2 : r.core.erase.core.path2 = none)
    (hlel : l.core.erase.core.state ≠ .eliminate_signal) (hrel : r.core.erase.core.state ≠ .eliminate_signal)
    (hstall : r.stall.val ≠ 0) :
    (BirthCheckPermitRepair.expiring hψ (by decide : 0 < 2) h2 l r).2.core.erase =
      (BirthCheckPermitRepair.ordinary hψ (by decide : 0 < 2) h2 κ l.core.erase r.core.erase).2 := by
  have hb := congrArg Prod.snd (r1_bounded_erase (κ := κ) hψ h2 l.core r.core)
  rw [authorized_eq_ordinary hψ h2 _ _ hlel hrel] at hb
  unfold BirthCheckPermitRepair.expiring
  dsimp only
  rw [prepare_identity hψ l hlp2, prepare_identity hψ r hrp2, expire_core_of_stall r _ hstall]
  exact hb

theorem expiring_left_erase (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (l r : ExpiringAgentState ψ κ τ)
    (hlp2 : l.core.erase.core.path2 = none) (hrp2 : r.core.erase.core.path2 = none)
    (hlel : l.core.erase.core.state ≠ .eliminate_signal) (hrel : r.core.erase.core.state ≠ .eliminate_signal)
    (hstall : l.stall.val ≠ 0) :
    (BirthCheckPermitRepair.expiring hψ (by decide : 0 < 2) h2 l r).1.core.erase =
      (BirthCheckPermitRepair.ordinary hψ (by decide : 0 < 2) h2 κ l.core.erase r.core.erase).1 := by
  have hb := congrArg Prod.fst (r1_bounded_erase (κ := κ) hψ h2 l.core r.core)
  rw [authorized_eq_ordinary hψ h2 _ _ hlel hrel] at hb
  unfold BirthCheckPermitRepair.expiring
  dsimp only
  rw [prepare_identity hψ l hlp2, prepare_identity hψ r hrp2, expire_core_of_stall l _ hstall]
  exact hb

/-- The responder of the actual R1 row output agrees with the ordinary responder on the chain fields when the
ordinary responder is a follower and the old responder stall is positive. -/
theorem row_right_frame (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (l r : ExpiringAgentState ψ κ τ)
    (hlp2 : l.core.erase.core.path2 = none) (hrp2 : r.core.erase.core.path2 = none)
    (hlel : l.core.erase.core.state ≠ .eliminate_signal) (hrel : r.core.erase.core.state ≠ .eliminate_signal)
    (hstall : r.stall.val ≠ 0)
    (hfol : (BirthCheckPermitRepair.ordinary hψ (by decide : 0 < 2) h2 κ l.core.erase r.core.erase).2.core.leader =
      false) :
    let q := BirthCheckPermitRepair.ordinary hψ (by decide : 0 < 2) h2 κ l.core.erase r.core.erase
    let o := (BirthCheckPermitRepair.row hψ (by decide : 0 < 2) h2 l r).2
    o.core.erase.core.state = q.2.core.state ∧ o.core.erase.core.path = q.2.core.path ∧
      o.core.erase.core.path2 = q.2.core.path2 ∧ o.core.erase.core.label = q.2.core.label ∧
      o.core.erase.core.reset_cmd = q.2.core.reset_cmd ∧ o.core.erase.core.leader = false := by
  intro q o
  have he := expiring_right_erase (κ := κ) hψ h2 l r hlp2 hrp2 hlel hrel hstall
  have hn := (finalPhysical_nonK2 hψ l r
    (normalizeLeader hψ (BirthCheckPermitRepair.expiring hψ (by decide : 0 < 2) h2 l r).1)
    (normalizeLeader hψ (BirthCheckPermitRepair.expiring hψ (by decide : 0 < 2) h2 l r).2)).2
  have hf := finalPhysical_right_follower hψ l r
    (normalizeLeader hψ (BirthCheckPermitRepair.expiring hψ (by decide : 0 < 2) h2 l r).1)
    (normalizeLeader hψ (BirthCheckPermitRepair.expiring hψ (by decide : 0 < 2) h2 l r).2)
  have ho : o = (finalPhysical hψ l r
      (normalizeLeader hψ (BirthCheckPermitRepair.expiring hψ (by decide : 0 < 2) h2 l r).1)
      (normalizeLeader hψ (BirthCheckPermitRepair.expiring hψ (by decide : 0 < 2) h2 l r).2)).2 := rfl
  rw [← ho] at hn hf
  clear_value o
  generalize hE : BirthCheckPermitRepair.expiring hψ (by decide : 0 < 2) h2 l r = E at he hn hf
  have hEl : E.2.core.core.leader = false := (congrArg (fun s : AuthorizedAgentState ψ => s.core.leader) he).trans hfol
  rw [normalizeLeader_of_follower hψ E.2 hEl] at hn hf
  have hx := nonK2_fields o E.2 hn
  refine ⟨?_, ?_, ?_, ?_, ?_, hf hEl⟩
  · exact hx.1.trans (congrArg (fun s : AuthorizedAgentState ψ => s.core.state) he)
  · exact hx.2.1.trans (congrArg (fun s : AuthorizedAgentState ψ => s.core.path) he)
  · exact hx.2.2.1.trans (congrArg (fun s : AuthorizedAgentState ψ => s.core.path2) he)
  · exact hx.2.2.2.1.trans (congrArg (fun s : AuthorizedAgentState ψ => s.core.label) he)
  · exact hx.2.2.2.2.2.1.trans (congrArg (fun s : AuthorizedAgentState ψ => s.core.reset_cmd) he)

/-- The initiator of the actual R1 row output agrees with the ordinary initiator on the chain fields when both
ordinary endpoints are followers and the old initiator stall is positive. -/
theorem row_left_frame (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (l r : ExpiringAgentState ψ κ τ)
    (hlp2 : l.core.erase.core.path2 = none) (hrp2 : r.core.erase.core.path2 = none)
    (hlel : l.core.erase.core.state ≠ .eliminate_signal) (hrel : r.core.erase.core.state ≠ .eliminate_signal)
    (hlstall : l.stall.val ≠ 0) (hrstall : r.stall.val ≠ 0)
    (hfolL : (BirthCheckPermitRepair.ordinary hψ (by decide : 0 < 2) h2 κ l.core.erase r.core.erase).1.core.leader =
      false)
    (hfolR : (BirthCheckPermitRepair.ordinary hψ (by decide : 0 < 2) h2 κ l.core.erase r.core.erase).2.core.leader =
      false) :
    let q := BirthCheckPermitRepair.ordinary hψ (by decide : 0 < 2) h2 κ l.core.erase r.core.erase
    let o := (BirthCheckPermitRepair.row hψ (by decide : 0 < 2) h2 l r).1
    o.core.erase.core.state = q.1.core.state ∧ o.core.erase.core.path = q.1.core.path ∧
      o.core.erase.core.path2 = q.1.core.path2 ∧ o.core.erase.core.label = q.1.core.label ∧
      o.core.erase.core.leader = false := by
  intro q o
  have heL := expiring_left_erase (κ := κ) hψ h2 l r hlp2 hrp2 hlel hrel hlstall
  have heR := expiring_right_erase (κ := κ) hψ h2 l r hlp2 hrp2 hlel hrel hrstall
  have hn := (finalPhysical_nonK2 hψ l r
    (normalizeLeader hψ (BirthCheckPermitRepair.expiring hψ (by decide : 0 < 2) h2 l r).1)
    (normalizeLeader hψ (BirthCheckPermitRepair.expiring hψ (by decide : 0 < 2) h2 l r).2)).1
  have hf := finalPhysical_left_follower hψ l r
    (normalizeLeader hψ (BirthCheckPermitRepair.expiring hψ (by decide : 0 < 2) h2 l r).1)
    (normalizeLeader hψ (BirthCheckPermitRepair.expiring hψ (by decide : 0 < 2) h2 l r).2)
  have ho : o = (finalPhysical hψ l r
      (normalizeLeader hψ (BirthCheckPermitRepair.expiring hψ (by decide : 0 < 2) h2 l r).1)
      (normalizeLeader hψ (BirthCheckPermitRepair.expiring hψ (by decide : 0 < 2) h2 l r).2)).1 := rfl
  rw [← ho] at hn hf
  clear_value o
  generalize hE : BirthCheckPermitRepair.expiring hψ (by decide : 0 < 2) h2 l r = E at heL heR hn hf
  have hEl : E.1.core.core.leader = false :=
    (congrArg (fun s : AuthorizedAgentState ψ => s.core.leader) heL).trans hfolL
  have hEr : E.2.core.core.leader = false :=
    (congrArg (fun s : AuthorizedAgentState ψ => s.core.leader) heR).trans hfolR
  rw [normalizeLeader_of_follower hψ E.1 hEl, normalizeLeader_of_follower hψ E.2 hEr] at hf
  rw [normalizeLeader_of_follower hψ E.1 hEl] at hn
  have hx := nonK2_fields o E.1 hn
  refine ⟨?_, ?_, ?_, ?_, hf hEl hEr⟩
  · exact hx.1.trans (congrArg (fun s : AuthorizedAgentState ψ => s.core.state) heL)
  · exact hx.2.1.trans (congrArg (fun s : AuthorizedAgentState ψ => s.core.path) heL)
  · exact hx.2.2.1.trans (congrArg (fun s : AuthorizedAgentState ψ => s.core.path2) heL)
  · exact hx.2.2.2.1.trans (congrArg (fun s : AuthorizedAgentState ψ => s.core.label) heL)

/-- The initiator leader bit through the pre-CHECK prefix and CHECK cut (from the consumer's ordinary left-leader
frame; the prefix is shared with R1). -/
theorem doneThrough_left_leader (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (κ : Nat) (l r : AuthorizedAgentState ψ)
    (hlel : l.core.state ≠ .eliminate_signal) (hrel : r.core.state ≠ .eliminate_signal) :
    (doneThroughCheckEntryWidth hψ (by decide : 0 < 2) h2 κ l r).1.core.leader = l.core.leader := by
  have h := B9SpliceV8LeftLeaderFrame.ordinary_normalized_left_leader (kappa := κ) hψ (by decide : 0 < 2) h2 l r
  dsimp only at h
  rw [normalize_identity l hlel, normalize_identity r hrel] at h
  unfold BirthShortDoneTerminalHost.doneOrdinaryMetadataEntryWidth at h
  dsimp only at h
  generalize doneThroughCheckEntryWidth hψ (by decide : 0 < 2) h2 κ l r = c at h ⊢
  have hq := BirthShortDoneCuts.afterCheckMetadataWidth_signal hψ (by decide : 0 < 2) h2 c.1 c.2
  generalize BirthShortDoneCuts.afterCheckMetadataWidth hψ (by decide : 0 < 2) h2 c.1 c.2 = q at hq h
  have hs := (K2BirthDispatcher.markBirth_signal (K2BirthDispatcher.authBirth l r q) q).trans hq
  have hl : (markLeaderBirth (K2BirthDispatcher.authBirth l r q) q).1.core.leader = c.1.core.leader :=
    congrArg (fun z : AgentState 1 × AgentState 1 => z.1.leader) hs
  exact hl.symm.trans h

/-- On deletion-free follower-initiator rows with reset-free inputs, the R1 ordinary branch outputs no reset
command. -/
theorem ordinary_reset_false (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (κ : Nat) (l r : AuthorizedAgentState ψ)
    (hlel : l.core.state ≠ .eliminate_signal) (hrel : r.core.state ≠ .eliminate_signal)
    (hll : l.core.leader = false) (hlr : l.core.reset_cmd = false) (hrr : r.core.reset_cmd = false) :
    (BirthCheckPermitRepair.ordinary hψ (by decide : 0 < 2) h2 κ l r).1.core.reset_cmd = false ∧
      (BirthCheckPermitRepair.ordinary hψ (by decide : 0 < 2) h2 κ l r).2.core.reset_cmd = false := by
  have hlead := (doneThrough_left_leader hψ h2 κ l r hlel hrel).trans hll
  have hc := BirthB1InnerCountMono.doneThroughCheckEntryWidth_reset_cmd hψ (by decide : 0 < 2) h2 κ l r
  unfold BirthCheckPermitRepair.ordinary
  dsimp only
  generalize doneThroughCheckEntryWidth hψ (by decide : 0 < 2) h2 κ l r = c at hlead hc ⊢
  have hq := BirthShortDoneCuts.afterCheckMetadataWidth_signal hψ (by decide : 0 < 2) h2
    (BirthCheckPermitRepair.permitFix c.1) c.2
  have hlp : (BirthCheckPermitRepair.permitFix c.1).core.leader = false := by
    rw [BirthCheckPermitRepair.permitFix_core]; exact hlead
  have hrs1 : (BirthCheckPermitRepair.permitFix c.1).core.reset_cmd = false := by
    rw [BirthCheckPermitRepair.permitFix_core, hc.1]; exact hlr
  have hrs2 : c.2.core.reset_cmd = false := by rw [hc.2]; exact hrr
  have ha := fun hh => BirthB1CountAlongNoBirth.afterCheckMetadataWidth_reset_false hψ (by decide : 0 < 2) h2
    (BirthCheckPermitRepair.permitFix c.1) c.2 hrs1 hrs2 hh
  generalize BirthShortDoneCuts.afterCheckMetadataWidth hψ (by decide : 0 < 2) h2
    (BirthCheckPermitRepair.permitFix c.1) c.2 = q at hq ha ⊢
  have hql : q.1.core.leader = false :=
    (congrArg (fun z : AgentState 1 × AgentState 1 => z.1.leader) hq).trans hlp
  have ha' := ha hql
  have hm := BirthB1InnerFieldFrames.markLeaderBirth_reset_cmd (K2BirthDispatcher.authBirth l r q) q
  exact ⟨hm.1.trans ha'.1, hm.2.trans ha'.2⟩

/-- Intermediate CHECK chain row on the actual R1 row: an `equal` label-i initiator and a check-open matching
label-(i+1) responder with a positive stall leave the responder `equal`, on its path, with empty `path2`, its
label, and a follower. -/
theorem r1_chain_row (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (l r : ExpiringAgentState ψ κ τ) (i bl : Nat)
    (hcons : r.core.erase.core.label = ⟨(l.core.erase.core.label.val + 1) % ψ, Nat.mod_lt _ hψ⟩)
    (hll : l.core.erase.core.leader = false) (hrl : r.core.erase.core.leader = false)
    (hlp : l.core.erase.core.path = .some i bl) (hlab : l.core.erase.core.label.val = i) (hi : i + 1 < ψ - 1)
    (hrm : BirthCheckChainR1.CheckOpenMatch r.core.erase.core) (hrlab : r.core.erase.core.label.val = i + 1)
    (hleq : l.core.erase.core.state = .equal) (hlp2 : l.core.erase.core.path2 = none)
    (hrpr : r.core.erase.core.state ≠ .produce) (hrdn : r.core.erase.core.state ≠ .done)
    (hrel : r.core.erase.core.state ≠ .eliminate_signal)
    (hrt : r.core.erase.core.state ≠ .toss) (hrc : r.core.erase.core.state ≠ .congest)
    (hlr : l.core.erase.core.reset_cmd = false) (hrr : r.core.erase.core.reset_cmd = false)
    (hl4 : i = 0 → ∀ p, l.core.erase.core.path4 = some p → p.1 ≠ -1)
    (hr5 : ∀ p, r.core.erase.core.path5 = some p → p.1 ≠ -1)
    (hstall : r.stall.val ≠ 0) :
    let o := (BirthCheckPermitRepair.row hψ (by decide : 0 < 2) h2 l r).2
    o.core.erase.core.state = .equal ∧ o.core.erase.core.path = r.core.erase.core.path ∧
      o.core.erase.core.path2 = none ∧ o.core.erase.core.label = r.core.erase.core.label ∧
      o.core.erase.core.reset_cmd = false ∧ o.core.erase.core.leader = false := by
  intro o
  have hc := BirthCheckChainR1.ordinary_chain_row hψ h2 κ l.core.erase r.core.erase i bl hcons hll hrl hlp hlab hi
    hrm hrlab hleq hlp2 hrpr hrdn hrel hrt hrc hlr hrr hl4 hr5
  have hlel : l.core.erase.core.state ≠ .eliminate_signal := by rw [hleq]; decide
  have hf := row_right_frame (κ := κ) hψ h2 l r hlp2 hrm.path2 hlel hrel hstall hc.2.2.2.2
  have hres := (ordinary_reset_false hψ h2 κ l.core.erase r.core.erase hlel hrel hll hlr hrr).2
  exact ⟨hf.1.trans hc.1, hf.2.1.trans hc.2.1, hf.2.2.1.trans hc.2.2.1, hf.2.2.2.1.trans hc.2.2.2.1,
    hf.2.2.2.2.1.trans hres, hf.2.2.2.2.2⟩

/-- First CHECK chain row on the actual R1 row (psi at least three): two check-open matching carriers at labels
0 and 1 with positive stalls both become `equal` on their paths, as followers. -/
theorem r1_first_row (hψ : 0 < ψ) (h3 : 2 < ψ) (l r : ExpiringAgentState ψ κ τ)
    (hcons : r.core.erase.core.label = ⟨(l.core.erase.core.label.val + 1) % ψ, Nat.mod_lt _ hψ⟩)
    (hll : l.core.erase.core.leader = false) (hrl : r.core.erase.core.leader = false)
    (hlm : BirthCheckChainR1.CheckOpenMatch l.core.erase.core) (hlab : l.core.erase.core.label.val = 0)
    (hrm : BirthCheckChainR1.CheckOpenMatch r.core.erase.core) (hrlab : r.core.erase.core.label.val = 1)
    (hlpr : l.core.erase.core.state ≠ .produce) (hldn : l.core.erase.core.state ≠ .done)
    (hlt : l.core.erase.core.state ≠ .toss) (hlc : l.core.erase.core.state ≠ .congest)
    (hlel : l.core.erase.core.state ≠ .eliminate_signal)
    (hrpr : r.core.erase.core.state ≠ .produce) (hrdn : r.core.erase.core.state ≠ .done)
    (hrel : r.core.erase.core.state ≠ .eliminate_signal)
    (hrt : r.core.erase.core.state ≠ .toss) (hrc : r.core.erase.core.state ≠ .congest)
    (hlr : l.core.erase.core.reset_cmd = false) (hrr : r.core.erase.core.reset_cmd = false)
    (hl4 : ∀ p, l.core.erase.core.path4 = some p → p.1 ≠ -1)
    (hr5 : ∀ p, r.core.erase.core.path5 = some p → p.1 ≠ -1)
    (hlstall : l.stall.val ≠ 0) (hrstall : r.stall.val ≠ 0) :
    let o := BirthCheckPermitRepair.row hψ (by decide : 0 < 2) (by omega) l r
    o.1.core.erase.core.state = .equal ∧ o.1.core.erase.core.path = l.core.erase.core.path ∧
      o.1.core.erase.core.label = l.core.erase.core.label ∧ o.1.core.erase.core.leader = false ∧
      o.2.core.erase.core.state = .equal ∧ o.2.core.erase.core.path = r.core.erase.core.path ∧
      o.2.core.erase.core.path2 = none ∧ o.2.core.erase.core.label = r.core.erase.core.label ∧
      o.2.core.erase.core.reset_cmd = false ∧ o.2.core.erase.core.leader = false := by
  intro o
  have h2 : 2 ≤ ψ := by omega
  have hc := BirthCheckChainR1.ordinary_first_row hψ h3 κ l.core.erase r.core.erase hcons hll hrl hlm hlab hrm hrlab
    hlpr hldn hlt hlc hrpr hrdn hrel hrt hrc hlr hrr hl4 hr5
  have hfR := row_right_frame (κ := κ) hψ h2 l r hlm.path2 hrm.path2 hlel hrel hrstall hc.2.2.2.2.2.2.2.2
  have hfL := row_left_frame (κ := κ) hψ h2 l r hlm.path2 hrm.path2 hlel hrel hlstall hrstall hc.2.2.2.1
    hc.2.2.2.2.2.2.2.2
  have hres := (ordinary_reset_false hψ h2 κ l.core.erase r.core.erase hlel hrel hll hlr hrr).2
  exact ⟨hfL.1.trans hc.1, hfL.2.1.trans hc.2.1, hfL.2.2.2.1.trans hc.2.2.1, hfL.2.2.2.2,
    hfR.1.trans hc.2.2.2.2.1, hfR.2.1.trans hc.2.2.2.2.2.1, hfR.2.2.1.trans hc.2.2.2.2.2.2.1,
    hfR.2.2.2.1.trans hc.2.2.2.2.2.2.2.1, hfR.2.2.2.2.1.trans hres, hfR.2.2.2.2.2⟩

end BirthCheckPermitRepairRowLift
