import Leader.Wu.Birth.IncreaseOrCapRawFireExtraction
import Leader.Wu.Birth.WidthTwoWaitTransfer
import Leader.Wu.Birth.WaitClockRows

namespace BirthPhaseB3NoBoundarySurvival

open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
  PPLLExpiringComparisonRepair
open BirthWaitPassive BirthShortWait BirthShortWaitProjection
  BirthShortWaitDomainWitness BirthShortWaitTerminalEntryRepair
open BirthShortDoneTerminalPassiveR4
open BirthShortDoneTerminalPassiveLocal3
open BirthShortDoneTerminalPassiveLocal3Rotation

set_option autoImplicit false
set_option Elab.async false
set_option pp.structureInstances false

variable {n psi kappa tau : Nat}

abbrev FC (n psi kappa tau : Nat) :=
  BirthPhaseWait2Transfer.FC n psi kappa tau

private theorem leftNeighbor_rightNeighbor_local
    (ring : DirectedRing n) (i : Fin n) :
    ring.leftNeighbor (ring.rightNeighbor i) = i := by
  apply Fin.ext
  simp only [DirectedRing.leftNeighbor, DirectedRing.rightNeighbor]
  by_cases hi : i.val + 1 < n
  · rw [Nat.mod_eq_of_lt hi]
    have heq : i.val + 1 + n - 1 = n + i.val := by omega
    rw [heq, add_self_mod, Nat.mod_eq_of_lt i.isLt]
  · have hie : i.val + 1 = n := by omega
    rw [hie, Nat.mod_self]
    have hlt : n - 1 < n := by omega
    rw [Nat.zero_add, Nat.mod_eq_of_lt hlt]
    omega

private theorem rightNeighbor_injective_local
    (ring : DirectedRing n) : Function.Injective ring.rightNeighbor := by
  intro a b hab
  have h := congrArg ring.leftNeighbor hab
  simpa only [leftNeighbor_rightNeighbor_local] using h

private theorem right_anchor_is_internal
    (hn : 4 <= n) (ring : DirectedRing n) (anchor : Fin n) :
    InternalLine3EdgeAt hn ring anchor (ring.rightNeighbor anchor) := by
  unfold InternalLine3EdgeAt InternalLine3Edge
  have h := congrArg (unrotateIndex ring anchor)
    (rotateIndex_p1 hn ring anchor)
  have hp :
      unrotateIndex ring anchor (ring.rightNeighbor anchor) = p1 hn := by
    simpa only [unrotateIndex_rotateIndex] using h.symm
  rw [hp]
  exact Or.inr rfl

private theorem raw_count_le
    (u : ExpiringAgentState psi kappa tau) : (raw u).count <= kappa := by
  change u.core.core.count.val <= kappa
  have h := u.core.core.count.isLt
  omega

private theorem active_regs2
    (hpsi : 0 < psi) (h2 : 2 <= psi) (kappa : Nat)
    (l r : AgentState psi) (hl : l.label.val < 2) (hr : r.label.val < 2) :
    waitRegsPair
        (waitWidthEntry hpsi (by decide : 0 < 2) h2 kappa l r) =
      waitRegsPair
        (waitSaturated (by decide : 0 < 2) kappa
          (waitPrefixProject l hl) (waitPrefixProject r hr)) := by
  rw [waitWidthEntry_eq_old_of_active_labels
    hpsi (by decide : 0 < 2) h2 kappa l r hl hr]
  simpa only using waitWidth_regs_eq_waitSaturated_prefix
    (kappa := kappa) hpsi (by decide : 0 < 2) h2 l r hl hr

private theorem prepare_right_count_frame2 (l r : AgentState 2) :
    (waitSaturatedPrepare (by decide : 0 < 2) l r).2.count = r.count := by
  simp [waitSaturatedPrepare]

private theorem waitSaturated_responder_count_nondec
    (kappa : Nat) (l r : AgentState 2) (hc : r.count <= kappa) :
    r.count <= (waitSaturated (by decide : 0 < 2) kappa l r).2.count := by
  rw [BirthWaitClockAudit.prepared_count_row
    (by decide : 0 < 2) kappa l r, prepare_right_count_frame2 l r]
  split
  · exact Nat.le_min.mpr ⟨by omega, hc⟩
  · exact Nat.le_refl _

private theorem active_responder_count_nondec
    (hpsi : 0 < psi) (h2 : 2 <= psi) (kappa : Nat)
    (l r : AgentState psi) (hl : l.label.val < 2) (hr : r.label.val < 2)
    (hc : r.count <= kappa) :
    r.count <= (waitWidthEntry hpsi (by decide : 0 < 2) h2 kappa l r).2.count := by
  have hp := congrArg Prod.snd (active_regs2 hpsi h2 kappa l r hl hr)
  have he := congrArg WaitRegs.count hp
  have he' :
      (waitWidthEntry hpsi (by decide : 0 < 2) h2 kappa l r).2.count =
        (waitSaturated (by decide : 0 < 2) kappa
          (waitPrefixProject l hl) (waitPrefixProject r hr)).2.count := by
    simpa only [waitRegsPair, WaitRegs.ofState] using he
  rw [he']
  exact waitSaturated_responder_count_nondec kappa
    (waitPrefixProject l hl) (waitPrefixProject r hr)
    (by simpa only [waitPrefixProject_count] using hc)

private theorem waitWidthEntry_left_count_frame
    (hpsi : 0 < psi) (h2 : 2 <= psi) (kappa : Nat)
    (l r : AgentState psi) :
    (waitWidthEntry hpsi (by decide : 0 < 2) h2 kappa l r).1.count = l.count := by
  simp [waitWidthEntry, waitSaturatedPrepare, terminalInactiveClear,
    waitWidthCarry, waitWidthReset, waitWidthFinish]

/-- Case (a): the anchor row has the tracked site as responder. -/
theorem anchor_responder_count_nondec
    (hpsi : 0 < psi) (h2 : 2 <= psi) (hn : 4 <= n)
    (kappa tau : Nat) (ring : DirectedRing n) (anchor : Fin n)
    (C : FC n psi kappa tau)
    (hC : BirthPhaseWait2Transfer.LocalWait2Carrier hpsi h2 hn ring anchor C)
    (hproj : RowProjection2 hpsi h2 kappa tau ring C anchor) :
    BirthPhaseWait2BlockProgress.shortCountAt ring anchor C <=
      BirthPhaseWait2BlockProgress.shortCountAt ring anchor
        (BirthPhaseWait2Transfer.hostStep hpsi h2 ring C anchor) := by
  have hline : LocalLine3At hpsi hn ring anchor C := hC
  let l := raw (C anchor)
  let r := raw (C (ring.rightNeighbor anchor))
  have hl : l.label.val < 2 := by dsimp [l]; rw [hline.lab0]; omega
  have hr : r.label.val < 2 := by dsimp [r]; rw [hline.lab1]; omega
  have hw := active_responder_count_nondec hpsi h2 kappa l r hl hr
    (raw_count_le (C (ring.rightNeighbor anchor)))
  let w := waitWidthEntry hpsi (by decide : 0 < 2) h2 kappa l r
  let q := BirthShortDoneTerminalHost.row hpsi (by decide : 0 < 2) h2
    (C anchor) (C (ring.rightNeighbor anchor))
  have hp := hproj
  unfold RowProjection2 at hp
  change clock (raw q.1) = clock w.1 /\ clock (raw q.2) = clock w.2 at hp
  have hc := congrArg (fun z : Clock psi => z.count) hp.2
  change (raw q.2).count = w.2.count at hc
  have hraw : r.count <= (raw q.2).count := by rw [hc]; exact hw
  have hne := rightNeighbor_ne_self_of_one_lt ring (by omega : 1 < n) anchor
  have hstep :
      BirthPhaseWait2Transfer.hostStep hpsi h2 ring C anchor
          (ring.rightNeighbor anchor) = q.2 :=
    BirthShortDoneTerminalPassiveR4.hostStep_right hpsi h2 ring C anchor hne
  unfold BirthPhaseWait2BlockProgress.shortCountAt
  rw [hstep]
  change r.count <= (raw q.2).count
  exact hraw

/-- Case (b): the tracked site itself is the initiator; its count is framed. -/
theorem tracked_initiator_count_frame
    (hpsi : 0 < psi) (h2 : 2 <= psi) (kappa tau : Nat)
    (ring : DirectedRing n) (anchor : Fin n) (C : FC n psi kappa tau)
    (hproj : RowProjection2 hpsi h2 kappa tau ring C (ring.rightNeighbor anchor)) :
    BirthPhaseWait2BlockProgress.shortCountAt ring anchor C =
      BirthPhaseWait2BlockProgress.shortCountAt ring anchor
        (BirthPhaseWait2Transfer.hostStep hpsi h2 ring C (ring.rightNeighbor anchor)) := by
  let j := ring.rightNeighbor anchor
  let l := raw (C j)
  let r := raw (C (ring.rightNeighbor j))
  let w := waitWidthEntry hpsi (by decide : 0 < 2) h2 kappa l r
  let q := BirthShortDoneTerminalHost.row hpsi (by decide : 0 < 2) h2
    (C j) (C (ring.rightNeighbor j))
  have hp := hproj
  unfold RowProjection2 at hp
  change clock (raw q.1) = clock w.1 /\ clock (raw q.2) = clock w.2 at hp
  have hc := congrArg (fun z : Clock psi => z.count) hp.1
  change (raw q.1).count = w.1.count at hc
  have hraw : (raw q.1).count = l.count :=
    hc.trans (waitWidthEntry_left_count_frame hpsi h2 kappa l r)
  have hstep : BirthPhaseWait2Transfer.hostStep hpsi h2 ring C j j = q.1 :=
    BirthShortDoneTerminalPassiveR4.hostStep_left hpsi h2 ring C j
  unfold BirthPhaseWait2BlockProgress.shortCountAt
  change (C j).core.core.count.val =
    (BirthPhaseWait2Transfer.hostStep hpsi h2 ring C j j).core.core.count.val
  rw [hstep]
  change l.count = (raw q.1).count
  exact hraw.symm

/-- Case (c): every other edge misses the tracked site at both endpoints. -/
theorem other_edge_count_frame
    (hpsi : 0 < psi) (h2 : 2 <= psi)
    (ring : DirectedRing n) (anchor e : Fin n) (C : FC n psi kappa tau)
    (he0 : e ≠ anchor) (he1 : e ≠ ring.rightNeighbor anchor) :
    BirthPhaseWait2BlockProgress.shortCountAt ring anchor C =
      BirthPhaseWait2BlockProgress.shortCountAt ring anchor
        (BirthPhaseWait2Transfer.hostStep hpsi h2 ring C e) := by
  have hr : ring.rightNeighbor anchor ≠ ring.rightNeighbor e := by
    intro h
    exact he0 (rightNeighbor_injective_local ring h).symm
  have hf :
      BirthPhaseWait2Transfer.hostStep hpsi h2 ring C e
          (ring.rightNeighbor anchor) = C (ring.rightNeighbor anchor) := by
    exact BirthShortDoneTerminalPassiveR4.hostStep_other hpsi h2 ring C e
      (ring.rightNeighbor anchor) (Ne.symm he1) hr
  unfold BirthPhaseWait2BlockProgress.shortCountAt
  rw [hf]

/-- A single no-stop Local3 suffix row never decreases the tracked count. -/
theorem noBoundaryNoCap_one_step_nondec
    (hpsi : 0 < psi) (h2 : 2 <= psi) (hn : 4 <= n)
    (kappa tau : Nat) (ring : DirectedRing n) (anchor : Fin n)
    (C : FC n psi kappa tau)
    (hC : BirthPhaseWait2Transfer.LocalWait2Carrier hpsi h2 hn ring anchor C)
    (e : Fin n)
    (hgo : ¬ (BirthPhaseWait2Transfer.LocalWait2StopNow
      hpsi h2 hn kappa tau ring anchor C e)) :
    BirthPhaseWait2BlockProgress.shortCountAt ring anchor C <=
      BirthPhaseWait2BlockProgress.shortCountAt ring anchor
        (BirthPhaseWait2Transfer.hostStep hpsi h2 ring C e) := by
  have hs := BirthPhaseWait2Transfer.local_wait2_one_edge_until_stop
    hpsi h2 hn kappa tau ring anchor C hC e hgo
  by_cases h0 : e = anchor
  · subst e
    exact anchor_responder_count_nondec hpsi h2 hn kappa tau ring anchor C hC
      (hs.2 (BirthPhaseB3BridgeStageA.anchor_is_internal hn ring anchor))
  · by_cases h1 : e = ring.rightNeighbor anchor
    · subst e
      exact Nat.le_of_eq (tracked_initiator_count_frame hpsi h2 kappa tau ring anchor C
        (hs.2 (right_anchor_is_internal hn ring anchor)))
    · exact Nat.le_of_eq (other_edge_count_frame hpsi h2 ring anchor e C h0 h1)

/-- Induction over the executable no-cap/no-boundary suffix. -/
theorem noBoundaryNoCap_suffix_count_nondec
    (hpsi : 0 < psi) (h2 : 2 <= psi) (hn : 4 <= n)
    (kappa tau : Nat) (ring : DirectedRing n) (anchor : Fin n)
    (C : FC n psi kappa tau)
    (hC : BirthPhaseWait2Transfer.LocalWait2Carrier hpsi h2 hn ring anchor C)
    (post : List (Fin n))
    (hrun : BirthPhaseWait2Transfer.LocalWait2RunSource
      hpsi h2 hn kappa tau ring anchor C post) :
    BirthPhaseWait2BlockProgress.shortCountAt ring anchor C <=
      BirthPhaseWait2BlockProgress.shortCountAt ring anchor
        (BirthPhaseGenericRenewal.rawEndpoint
          (BirthPhaseWait2BlockProgress.currentStep2 hpsi h2 ring) C post) := by
  induction post generalizing C with
  | nil => simp [BirthPhaseGenericRenewal.rawEndpoint]
  | cons e rest ih =>
      change
        (¬ (BirthPhaseWait2Transfer.LocalWait2StopNow
          hpsi h2 hn kappa tau ring anchor C e)) /\
        BirthPhaseWait2Transfer.LocalWait2RunSource hpsi h2 hn kappa tau ring anchor
          (BirthPhaseWait2Transfer.hostStep hpsi h2 ring C e) rest at hrun
      have hs := BirthPhaseWait2Transfer.local_wait2_one_edge_until_stop
        hpsi h2 hn kappa tau ring anchor C hC e hrun.1
      have h1 := noBoundaryNoCap_one_step_nondec
        hpsi h2 hn kappa tau ring anchor C hC e hrun.1
      have hrest := ih (C := BirthPhaseWait2Transfer.hostStep hpsi h2 ring C e)
        hs.1 hrun.2
      rw [BirthPhaseWait2BlockProgress.hostStep_eq_currentStep2 hpsi h2 ring C e] at h1 hrest
      simpa [BirthPhaseGenericRenewal.rawEndpoint] using Nat.le_trans h1 hrest

/-- A strict gain at the B3 fire survives every suffix that reaches neither
another cap nor a Local3 crossing, hence the B4 rank is still strictly lower. -/
theorem noBoundaryNoCap_suffix_strict_rank_drop
    (hpsi : 0 < psi) (h2 : 2 <= psi) (hn : 4 <= n)
    (kappa tau : Nat) (ring : DirectedRing n) (anchor : Fin n)
    (C fired : FC n psi kappa tau)
    (hstrict : BirthPhaseWait2BlockProgress.shortCountAt ring anchor C <
      BirthPhaseWait2BlockProgress.shortCountAt ring anchor fired)
    (hfired : BirthPhaseWait2Transfer.LocalWait2Carrier hpsi h2 hn ring anchor fired)
    (post : List (Fin n))
    (hrun : BirthPhaseWait2Transfer.LocalWait2RunSource
      hpsi h2 hn kappa tau ring anchor fired post) :
    BirthPhaseWait2BlockProgress.rank kappa ring anchor
        (BirthPhaseGenericRenewal.rawEndpoint
          (BirthPhaseWait2BlockProgress.currentStep2 hpsi h2 ring) fired post) <
      BirthPhaseWait2BlockProgress.rank kappa ring anchor C := by
  apply (BirthPhaseWait2BlockProgress.rank_lt_iff_shortCount_lt
    kappa ring anchor C
      (BirthPhaseGenericRenewal.rawEndpoint
        (BirthPhaseWait2BlockProgress.currentStep2 hpsi h2 ring) fired post)).2
  exact Nat.lt_of_lt_of_le hstrict
    (noBoundaryNoCap_suffix_count_nondec
      hpsi h2 hn kappa tau ring anchor fired hfired post hrun)

end BirthPhaseB3NoBoundarySurvival

#print axioms BirthPhaseB3NoBoundarySurvival.noBoundaryNoCap_one_step_nondec
#print axioms BirthPhaseB3NoBoundarySurvival.noBoundaryNoCap_suffix_count_nondec
#print axioms BirthPhaseB3NoBoundarySurvival.noBoundaryNoCap_suffix_strict_rank_drop
