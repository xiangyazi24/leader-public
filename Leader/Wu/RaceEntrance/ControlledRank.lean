import Leader.Wu.RaceEntrance.LocalService
import Leader.Wu.RaceEntrance.ArrivalRaceMass

set_option autoImplicit false

open PPLLRepair LDSinkGapCleanup LDSinkKernelC LDSinkProtectedAbsorption
open LDSinkGapDoneInvariant LDSinkGapServiceRank LDTwoGapFrame
open LDSinkTwoGapNoResetKernel LDSinkTwoGapReachInvariant LDSinkTwoGapEpochSuccessor
open LDSinkTwoGapArrivalRaceMass LDSinkTwoGapRaceEntranceLocalService

namespace LDSinkTwoGapRaceEntranceControlledRank

variable {n psi : Nat}

/-!
Ready-edge redirection loses at most two units of the attack cleanup rank.
The actual outgoing shared-leader FIRE clears attack position one and
seeds its signal; every higher positive attack cell is framed.  The incoming
shared edge frames the complete positive attack projection.  These are
physical row statements, with no scheduler-mass premise.
-/

/-- The outgoing ready leader is protected before MOVE, and every follower
bullet colour is cleared at its responder before the final SIGNAL/sink. -/
theorem ready_victim_pair (hpsi : psi > 0) (l r : AgentState psi)
    (hl : l.leader = true) (hs : l.signal_B = (1 : Fin 2))
    (hr : r.leader = false) :
    sinkKernelC hpsi l r =
      ({ l with bullet := 2, shield := true, signal_B := 0 },
       { r with bullet := 0, signal_B := 1 }) := by
  have hb : r.bullet = (0 : Fin 3) ∨ r.bullet = 1 ∨ r.bullet = 2 := by
    have h := r.bullet.isLt
    rcases (by omega : r.bullet.val = 0 ∨ r.bullet.val = 1 ∨ r.bullet.val = 2)
      with h0 | h1 | h2
    · exact .inl (Fin.ext h0)
    · exact .inr (.inl (Fin.ext h1))
    · exact .inr (.inr (Fin.ext h2))
  have ht : r.signal_B = (0 : Fin 2) ∨ r.signal_B = 1 := by
    have h := r.signal_B.isLt
    rcases (by omega : r.signal_B.val = 0 ∨ r.signal_B.val = 1) with h0 | h1
    · exact .inl (Fin.ext h0)
    · exact .inr (Fin.ext h1)
  rcases hb with hb | hb | hb <;> rcases ht with ht | ht <;>
    simp [sinkKernelC, eliminateLeadersNoCollisionFire, hl, hs, hr, hb, ht,
      absorbProtectedMove, eliminateLeadersNoCollisionZeroLeaderEgressMove,
      eliminateLeadersNoCollisionSignalLeaderSink, dummyBulletSink] <;> rfl

theorem victim_frames_higher (hpsi : psi > 0) (G : GapFrame n)
    (C : Fin n → AgentState psi) (k : Nat) (hk : 2 ≤ k) (hkd : k ≤ G.d) :
    sinkStepC hpsi G C (G.pos 0) (G.pos k) = C (G.pos k) := by
  have hn := G.hdn
  apply sinkStepC_other
  · exact G.pos_ne (by omega) (by omega) (by omega)
  · rw [gap_rightNeighbor_pos]
    exact G.pos_ne (by omega) (by omega) (by omega)

theorem ready_victim_front (hpsi : psi > 0) (G : GapFrame n)
    (C : Fin n → AgentState psi) (hi : GapInvariant hpsi G C)
    (hs : (C (G.pos 0)).signal_B = (1 : Fin 2)) :
    sinkStepC hpsi G C (G.pos 0) (G.pos 1) =
      { C (G.pos 1) with bullet := 0, signal_B := 1 } := by
  have hd := G.hd
  have hn := G.hdn
  have hrow := ready_victim_pair hpsi (C (G.pos 0)) (C (G.pos 1))
    hi.1.1 hs (hi.2.1 1 (by omega) (by omega))
  rw [sinkStepC, gap_rightNeighbor_pos]
  rw [updatePair_responder _ _ _ _ (G.pos_ne (by omega) (by omega) (by omega))]
  exact congrArg Prod.snd hrow

private theorem ready_victim_not_done (hpsi : psi > 0) (G : GapFrame n)
    (C : Fin n → AgentState psi) (hi : GapInvariant hpsi G C)
    (hn : ¬ GapDoneC G C) (hs : (C (G.pos 0)).signal_B = (1 : Fin 2)) :
    ¬ GapDoneC G (sinkStepC hpsi G C (G.pos 0)) := by
  have hlead := outgoing_fire_leaders hpsi G C (G.pos 0) hi.1.1 hs
  have hd := G.hd
  have hf := victim_frames_higher hpsi G C G.d hd (Nat.le_refl _)
  rintro (hc | h0 | hd')
  · have hsc : (C (G.pos G.d)).signal_B = (1 : Fin 2) := by
      have ht := hc.1
      rw [hf] at ht
      exact ht
    exact hn (.inl ((cleanReady_iff_shooter_signal hpsi G C hi).mpr hsc))
  · rw [hlead, hi.1.1] at h0
    cases h0
  · rw [hlead, hi.1.2] at hd'
    cases hd'

/-- Even with arbitrarily many old gap bullets, suppressing one ready
victim FIRE loses at most two numerical cleanup services. -/
theorem ready_victim_rank_loss_le_two (hpsi : psi > 0) (G : GapFrame n)
    (C : Fin n → AgentState psi) (hi : GapInvariant hpsi G C)
    (hn : ¬ GapDoneC G C) (hs : (C (G.pos 0)).signal_B = (1 : Fin 2)) :
    gapWC G C ≤ gapWC G (sinkStepC hpsi G C (G.pos 0)) + 2 := by
  classical
  let D := sinkStepC hpsi G C (G.pos 0)
  have hd := G.hd
  have hnD : ¬ GapDoneC G D := ready_victim_not_done hpsi G C hi hn hs
  have hfront : D (G.pos 1) = { C (G.pos 1) with bullet := 0, signal_B := 1 } :=
    ready_victim_front hpsi G C hi hs
  have hframe : ∀ k, 2 ≤ k → k ≤ G.d → D (G.pos k) = C (G.pos k) :=
    victim_frames_higher hpsi G C
  have hbC := bulletTop_le G C
  have hsD := signalTop_le G D
  change gapWC G C ≤ gapWC G D + 2
  unfold gapWC
  rw [if_neg hn, if_neg hnD]
  by_cases hb0 : bulletTop G C = 0
  · have hbD : bulletTop G D = 0 := by
      apply bulletTop_eq_zero_of
      intro k hk hkd
      by_cases hk1 : k = 1
      · subst k
        rw [hfront]
        rfl
      · rw [hframe k (by omega) hkd]
        exact bulletTop_zero_at G C (by omega) hkd
    have hsle : signalTop G D ≤ signalTop G C + 1 := by
      apply topIdx_le_of
      intro k hk hkd
      simp only [decide_eq_false_iff_not]
      have hzero : (D (G.pos k)).signal_B = (0 : Fin 2) := by
        rw [hframe k (by omega) hkd]
        exact signalTop_zero_at G C (by omega) hkd
      rw [hzero]
      decide
    rw [if_pos hb0, if_pos hbD]
    omega
  · by_cases hb1 : bulletTop G C = 1
    · have hbD : bulletTop G D = 0 := by
        apply bulletTop_eq_zero_of
        intro k hk hkd
        by_cases hk1 : k = 1
        · subst k
          rw [hfront]
          rfl
        · rw [hframe k (by omega) hkd]
          exact bulletTop_zero_at G C (by omega) hkd
      have hbone : (C (G.pos 1)).bullet ≠ (0 : Fin 3) := by
        have h := bulletTop_ne_zero G C (by omega)
        rw [hb1] at h
        exact h
      have hsle : signalTop G D ≤ 1 := by
        apply topIdx_le_of
        intro k hk hkd
        simp only [decide_eq_false_iff_not]
        have hzero : (D (G.pos k)).signal_B = (0 : Fin 2) := by
          rw [hframe k (by omega) hkd]
          exact hi.2.2.2 1 k (by decide) (by omega) hbone (by omega) hkd
        rw [hzero]
        decide
      rw [if_neg hb0, if_pos hbD, hb1]
      omega
    · have hbge : bulletTop G C ≤ bulletTop G D := by
        apply bulletTop_ge_of G D hbC
        rw [hframe (bulletTop G C) (by omega) hbC]
        exact bulletTop_ne_zero G C (by omega)
      have hbD : bulletTop G D ≠ 0 := by omega
      rw [if_neg hb0, if_neg hbD]
      omega

/-- The incoming shared edge is outside all positive attack cells. -/
theorem prepare_frames_attack (hpsi : psi > 0) (F : TwoGapFrame n)
    (C : Fin n → AgentState psi) (k : Nat) (hk : 1 ≤ k) (hkd : k ≤ F.attack.d) :
    sinkStepC hpsi F.attack C (preparePort F) (F.attack.pos k) = C (F.attack.pos k) := by
  apply sinkStepC_other
  · exact (F.recovery_before_shared_ne_attack (F.recovery.d - 1) k
      (by have h := F.recovery.hd; omega) hkd).symm
  · rw [preparePort_right]
    exact F.attack.pos_ne (Nat.lt_of_le_of_lt hkd F.attack.hdn)
      (by have h := F.attack.ring.hn; omega) (by omega)

/-- Preparation changes the shared leader only as responder, so it frames
the attack cleanup rank even at clean and nonclean boundaries. -/
theorem prepare_attack_rank_eq (hpsi : psi > 0) (F : TwoGapFrame n)
    (C : Fin n → AgentState psi) :
    gapWC F.attack (sinkStepC hpsi F.attack C (preparePort F)) = gapWC F.attack C := by
  classical
  let D := sinkStepC hpsi F.attack C (preparePort F)
  have hf : ∀ k, 1 ≤ k → k ≤ F.attack.d → D (F.attack.pos k) = C (F.attack.pos k) :=
    prepare_frames_attack hpsi F C
  have hleader : (D (F.attack.pos 0)).leader = (C (F.attack.pos 0)).leader := by
    change (sinkStepC hpsi F.attack C (preparePort F) (deletePort F)).leader = _
    rw [sinkStepC, preparePort_right,
      updatePair_responder _ _ _ _ (preparePort_ne_deletePort F).symm]
    exact kernelC_right_leader_eq hpsi _ _
  have hclean : CleanReady F.attack D ↔ CleanReady F.attack C := by
    unfold CleanReady
    rw [hf F.attack.d (by have h := F.attack.hd; omega) (Nat.le_refl _)]
    constructor <;> intro h <;> refine ⟨h.1, ?_⟩ <;> intro k hk hkd
    · have hb := h.2 k hk hkd
      rwa [hf k hk hkd] at hb
    · rw [hf k hk hkd]
      exact h.2 k hk hkd
  have hdone : GapDoneC F.attack D ↔ GapDoneC F.attack C := by
    unfold GapDoneC EndpointDeleted
    rw [hclean, hleader, hf F.attack.d (by have h := F.attack.hd; omega) (Nat.le_refl _)]
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

private theorem move_left_quiet_fields (hpsi : psi > 0) (nl : Fin psi)
    (l r : AgentState psi) (hs : l.signal_B = (0 : Fin 2)) :
    (absorbProtectedMove hpsi nl l r).1.shield = l.shield ∧
      (absorbProtectedMove hpsi nl l r).1.signal_B = (0 : Fin 2) := by
  unfold absorbProtectedMove
  split
  · exact ⟨rfl, hs⟩
  · unfold eliminateLeadersNoCollisionZeroLeaderEgressMove
    repeat first | exact ⟨rfl, hs⟩ | exact ⟨rfl, rfl⟩ | split

/-- Without initiator FIRE, the shared shield is unchanged and its zero
signal remains zero, even when a follower bullet is absorbed or deletes it. -/
theorem kernelC_left_quiet_fields (hpsi : psi > 0) (l r : AgentState psi)
    (hs : l.signal_B = (0 : Fin 2)) :
    (sinkKernelC hpsi l r).1.shield = l.shield ∧
      (sinkKernelC hpsi l r).1.signal_B = (0 : Fin 2) := by
  have hf := fire_left_eq hpsi l r (Or.inr hs)
  unfold sinkKernelC
  rw [dummyBulletSink_left_eq, signal_left, hf]
  exact move_left_quiet_fields hpsi _ l _ hs

/-- A follower initiator cannot remove any leader in this physical step. -/
theorem follower_edge_leaders (hpsi : psi > 0) (G : GapFrame n)
    (C : Fin n → AgentState psi) (e : Fin n) (hl : (C e).leader = false) :
    ∀ v, (sinkStepC hpsi G C e v).leader = (C v).leader := by
  intro v
  by_cases hv : v = e
  · subst v
    rw [sinkStepC, updatePair_initiator, hl]
    exact (kernelC_no_leader_creation hpsi (C e) (C (G.ring.rightNeighbor e))).1 hl
  · by_cases hr : v = G.ring.rightNeighbor e
    · subst v
      rw [sinkStepC, updatePair_responder _ _ _ _ hv]
      exact kernelC_right_leader_eq hpsi _ _
    · rw [sinkStepC_other hpsi G C e v hv hr]

private theorem gapPair_not_success (hpsi : psi > 0) (F : TwoGapFrame n)
    (b : AState n psi) (hg : GapPair hpsi F b) : ¬ NoResetSuccess F b.conf := by
  rintro ((hl | hr) | (hl | hr))
  · have hh := hg.attack.1.1
    rw [hh] at hl
    cases hl
  · have hh := hg.attack.1.2
    rw [hh] at hr
    cases hr
  · have hh := hg.recovery.1.1
    rw [hh] at hl
    cases hl
  · have hh := hg.recovery.1.2
    rw [hh] at hr
    cases hr

theorem prepare_not_success (hpsi : psi > 0) (F : TwoGapFrame n)
    (b : AState n psi) (hg : GapPair hpsi F b) :
    ¬ NoResetSuccess F (attemptStepConf hpsi F b (preparePort F)) := by
  have hd := F.recovery.hd
  have hlead := follower_edge_leaders hpsi F.attack b.conf (preparePort F)
    (hg.recovery.2.1 (F.recovery.d - 1) (by omega) (by omega))
  intro hd
  apply gapPair_not_success hpsi F b hg
  simpa only [attemptStepConf_eq_sinkStepC, NoResetSuccess, EndpointDeleted, hlead] using hd

theorem ready_delete_not_success (hpsi : psi > 0) (F : TwoGapFrame n)
    (b : AState n psi) (hg : GapPair hpsi F b)
    (hs : (b.conf (deletePort F)).signal_B = (1 : Fin 2)) :
    ¬ NoResetSuccess F (attemptStepConf hpsi F b (deletePort F)) := by
  have hlead := outgoing_fire_leaders hpsi F.attack b.conf (deletePort F)
    hg.attack.1.1 hs
  intro hd
  apply gapPair_not_success hpsi F b hg
  simpa only [attemptStepConf_eq_sinkStepC, NoResetSuccess, EndpointDeleted, hlead] using hd

end LDSinkTwoGapRaceEntranceControlledRank

#print axioms LDSinkTwoGapRaceEntranceControlledRank.ready_victim_pair
#print axioms LDSinkTwoGapRaceEntranceControlledRank.ready_victim_rank_loss_le_two
#print axioms LDSinkTwoGapRaceEntranceControlledRank.prepare_attack_rank_eq
#print axioms LDSinkTwoGapRaceEntranceControlledRank.kernelC_left_quiet_fields
#print axioms LDSinkTwoGapRaceEntranceControlledRank.prepare_not_success
#print axioms LDSinkTwoGapRaceEntranceControlledRank.ready_delete_not_success
