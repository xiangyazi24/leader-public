import Leader.Wu.RaceEntrance.ColourCoupling
import Leader.Wu.RaceEntrance.ControlledRank
import Leader.Wu.RaceEntrance.ControlledTail

set_option autoImplicit false

open PPLLRepair LDSinkGapCleanup LDSinkKernelC LDSinkProtectedAbsorption
open LDSinkGapDoneInvariant LDSinkGapServiceRank LDSinkGapCleanupBound LDTwoGapFrame
open LDSinkTwoGapNoResetKernel LDSinkTwoGapReachInvariant LDSinkTwoGapArrivalRaceMass
open LDSinkTwoGapRaceEntranceLocalService LDSinkTwoGapRaceEntranceColourCoupling
open LDSinkTwoGapRaceEntranceControlledTail

namespace LDSinkTwoGapRaceEntranceDummyService

variable {n psi : Nat}

/-!
After an incoming shared FIRE, its highest recovery bullet is the new dummy.
Before that dummy reaches the victim edge, the shared leader cannot become
ready again.  Its position changes only at its single predecessor port.
The carrier permits arbitrary older bullets below that highest dummy.
-/

def DummyFront (G : GapFrame n) (C : Fin n → AgentState psi) (p : Nat) : Prop :=
  (C (G.pos p)).bullet = (1 : Fin 3) ∧
    ∀ k, p < k → k ≤ G.d → (C (G.pos k)).bullet = (0 : Fin 3)

def nextDummyPosition (G : GapFrame n) (p : Nat) (e : Fin n) : Nat :=
  if p = 0 then 0 else if e = G.pos (p - 1) then p - 1 else p

private theorem predecessor_of_head (G : GapFrame n) (e : Fin n)
    (p : Nat) (hp : 1 ≤ p) (he : G.ring.rightNeighbor e = G.pos p) :
    e = G.pos (p - 1) := by
  have hh : G.ring.rightNeighbor e = G.ring.rightNeighbor (G.pos (p - 1)) := by
    simpa only [gap_rightNeighbor_pos, Nat.sub_add_cancel hp] using he
  have hv := congrArg Fin.val hh
  change (e.val + 1) % n = ((G.pos (p - 1)).val + 1) % n at hv
  have heB := e.isLt
  have hfB := (G.pos (p - 1)).isLt
  apply Fin.ext
  by_cases ha : e.val + 1 < n <;> by_cases hb : (G.pos (p - 1)).val + 1 < n
  · rw [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at hv
    omega
  · have hn : (G.pos (p - 1)).val + 1 = n := by omega
    rw [hn, Nat.mod_self, Nat.mod_eq_of_lt ha] at hv
    omega
  · have hn : e.val + 1 = n := by omega
    rw [hn, Nat.mod_self, Nat.mod_eq_of_lt hb] at hv
    omega
  · omega

private theorem quiet_follower_left (hpsi : psi > 0) (l r : AgentState psi)
    (hl : l.leader = false) (hr : r.leader = false ∨ r.signal_B = (0 : Fin 2))
    (hb : r.bullet = (0 : Fin 3)) : (sinkKernelC hpsi l r).1 = l := by
  have hf := fire_eq_self hpsi l r (Or.inl hl) hr
  have hg : ¬ ProtectedGuard hpsi l r := by
    unfold ProtectedGuard
    rw [hf]
    simp [hl]
  rw [kernelC_eq_of_not_protected hpsi l r hg, sinkKernel_staged, hf]
  dsimp only
  rw [move_eq_self_of_bullet_zero hpsi (nextLabel hpsi l) l r hb,
    dummyBulletSink_left_eq, signal_left]

private theorem dummy_not_done (hpsi : psi > 0) (G : GapFrame n)
    (C : Fin n → AgentState psi) (hi : GapInvariant hpsi G C)
    (p : Nat) (hp : 0 < p) (hpd : p ≤ G.d)
    (hb : (C (G.pos p)).bullet = (1 : Fin 3)) : ¬ GapDoneC G C := by
  rintro (hc | hl | hr)
  · have hz := hc.2 p (by omega) hpd
    rw [hb] at hz
    cases hz
  · rw [hi.1.1] at hl
    cases hl
  · rw [hi.1.2] at hr
    cases hr

private theorem dummy_bulletTop (G : GapFrame n) (C : Fin n → AgentState psi)
    (p : Nat) (_hp : 0 < p) (hpd : p ≤ G.d) (hf : DummyFront G C p) :
    bulletTop G C = p := by
  apply Nat.le_antisymm
  · apply topIdx_le_of
    intro k hk hkd
    simp only [decide_eq_false_iff_not, Nat.not_lt, Nat.le_zero]
    rw [hf.2 k hk hkd]
    rfl
  · apply bulletTop_ge_of G C hpd
    rw [hf.1]
    change (1 : Fin 3) ≠ 0
    decide

/-- A nonservice edge preserves the highest dummy itself.  It may change
lower cells, including earlier bullets and absence signals. -/
theorem dummy_nonservice (hpsi : psi > 0) (G : GapFrame n)
    (C : Fin n → AgentState psi) (hi : GapInvariant hpsi G C)
    (p : Nat) (hp : 0 < p) (hpd : p < G.d) (hf : DummyFront G C p)
    (e : Fin n) (he : e ≠ G.pos (p - 1)) :
    (sinkStepC hpsi G C e (G.pos p)).bullet = (1 : Fin 3) := by
  by_cases ht : e = G.pos p
  · subst e
    rw [sinkStepC, updatePair_initiator, gap_rightNeighbor_pos]
    have hright : (C (G.pos (p + 1))).leader = false ∨
        (C (G.pos (p + 1))).signal_B = (0 : Fin 2) := by
      by_cases hd : p + 1 = G.d
      · apply Or.inr
        exact hi.2.2.2 p (p + 1) (by omega) (by omega)
          (by rw [hf.1]; decide) (by omega) (by omega)
      · exact .inl (hi.2.1 (p + 1) (by omega) (by omega))
    rw [quiet_follower_left hpsi _ _ (hi.2.1 p (by omega) hpd)
      hright (hf.2 (p + 1) (by omega) (by omega))]
    exact hf.1
  · rw [sinkStepC_other hpsi G C e (G.pos p) (fun h => ht h.symm) ?_]
    · exact hf.1
    · intro h
      exact he (predecessor_of_head G e p (by omega) h.symm)

/-- The unique service edge transfers the actual dummy and clears its old
position.  Both cells are followers because this is before the victim hit. -/
theorem dummy_transfer (hpsi : psi > 0) (G : GapFrame n)
    (C : Fin n → AgentState psi) (hi : GapInvariant hpsi G C)
    (p : Nat) (hp : 1 < p) (hpd : p < G.d) (hf : DummyFront G C p) :
    (sinkStepC hpsi G C (G.pos (p - 1)) (G.pos (p - 1))).bullet = (1 : Fin 3) ∧
      (sinkStepC hpsi G C (G.pos (p - 1)) (G.pos p)).bullet = (0 : Fin 3) := by
  have hsig : (C (G.pos p)).signal_B = (0 : Fin 2) :=
    hi.2.2.2 p p (by omega) (by omega) (by rw [hf.1]; decide) (Nat.le_refl _) (by omega)
  have ha : (C (G.pos p)).label = nextLabel hpsi (C (G.pos (p - 1))) := by
    simpa only [Nat.sub_add_cancel (by omega : 1 ≤ p)] using
      hi.2.2.1 (p - 1) (by omega)
  have hrow := quiet_transfer_pair hpsi (C (G.pos (p - 1))) (C (G.pos p))
    (hi.2.1 (p - 1) (by omega) (by omega)) hsig (by rw [hf.1]; decide) ha
  have hhead : G.ring.rightNeighbor (G.pos (p - 1)) = G.pos p := by
    rw [gap_rightNeighbor_pos, Nat.sub_add_cancel (by omega : 1 ≤ p)]
  have hne : G.pos p ≠ G.pos (p - 1) :=
    G.pos_ne (by have h := G.hdn; omega) (by have h := G.hdn; omega) (by omega)
  constructor
  · rw [sinkStepC, updatePair_initiator, hhead, hrow]
    exact hf.1
  · rw [sinkStepC, hhead, updatePair_responder _ _ _ _ hne, hrow]

/-- On a surviving physical gap, the remembered highest dummy follows
exactly one predecessor service port until its remaining distance is zero.
The C5 rank prevents any new higher bullet from appearing. -/
theorem dummy_front_row (hpsi : psi > 0) (G : GapFrame n)
    (C : Fin n → AgentState psi) (hi : GapInvariant hpsi G C)
    (p : Nat) (hp : 0 < p) (hpd : p < G.d) (hf : DummyFront G C p)
    (e : Fin n) (hpost : GapInvariant hpsi G (sinkStepC hpsi G C e))
    (hpos : 0 < nextDummyPosition G p e) :
    DummyFront G (sinkStepC hpsi G C e) (nextDummyPosition G p e) := by
  classical
  have hpre := dummy_not_done hpsi G C hi p hp (by omega) hf.1
  have hbpre := dummy_bulletTop G C p hp (by omega) hf
  have hmono := gapWC_step_le' hpsi G C hi hpre e
  have hne0 : p ≠ 0 := by omega
  by_cases he : e = G.pos (p - 1)
  · have hpp : 1 < p := by
      have hh : 0 < p - 1 := by
        simpa only [nextDummyPosition, if_neg hne0, if_pos he] using hpos
      omega
    subst e
    have hrow := dummy_transfer hpsi G C hi p hpp hpd hf
    have hpostn := dummy_not_done hpsi G _ hpost (p - 1) (by omega) (by omega) hrow.1
    have hbt : bulletTop G (sinkStepC hpsi G C (G.pos (p - 1))) ≠ 0 := by
      have hh := bulletTop_ge_of G (sinkStepC hpsi G C (G.pos (p - 1))) (by omega : p - 1 ≤ G.d)
        (by rw [hrow.1]; change (1 : Fin 3) ≠ 0; decide)
      omega
    have hle : bulletTop G (sinkStepC hpsi G C (G.pos (p - 1))) ≤ p := by
      simp only [gapWC, if_neg hpre, if_neg hpostn, if_neg hbt, hbpre, if_neg hne0] at hmono
      omega
    simp only [nextDummyPosition, if_neg hne0, ite_true]
    refine ⟨hrow.1, ?_⟩
    intro k hk hkd
    by_cases hkp : k = p
    · subst k
      exact hrow.2
    · exact bulletTop_zero_at G _ (by omega) hkd
  · have hb := dummy_nonservice hpsi G C hi p hp hpd hf e he
    have hpostn := dummy_not_done hpsi G _ hpost p hp (by omega) hb
    have hbt : bulletTop G (sinkStepC hpsi G C e) ≠ 0 := by
      have hh := bulletTop_ge_of G (sinkStepC hpsi G C e) (by omega : p ≤ G.d)
        (by rw [hb]; change (1 : Fin 3) ≠ 0; decide)
      omega
    have hle : bulletTop G (sinkStepC hpsi G C e) ≤ p := by
      simp only [gapWC, if_neg hpre, if_neg hpostn, if_neg hbt, hbpre, if_neg hne0] at hmono
      omega
    simp only [nextDummyPosition, if_neg hne0, if_neg he]
    exact ⟨hb, fun k hk hkd => bulletTop_zero_at G _ (by omega) hkd⟩

/-- A pending recovery dummy prevents the shared FIRE gate from reopening. -/
theorem dummy_not_sharedReady (hpsi : psi > 0) (F : TwoGapFrame n)
    (b : AState n psi) (hg : GapPair hpsi F b) (p : Nat)
    (hp : 0 < p) (hpd : p < F.recovery.d) (hf : DummyFront F.recovery b.conf p) :
    ¬ SharedReady F b.conf := by
  have hz := hg.recovery.2.2.2 p F.recovery.d (by omega) (by omega)
    (by rw [hf.1]; decide) (by omega) (Nat.le_refl _)
  rw [F.shared] at hz
  intro hs
  change (b.conf (F.attack.pos 0)).signal_B = (1 : Fin 2) at hs
  rw [hz] at hs
  cases hs

/-- Every collapsed ready event physically starts a new highest dummy at
distance `a-1`.  Its shooter cell is cleared in this same FIRE/MOVE row. -/
theorem prepare_dummy_front (hpsi : psi > 0) (F : TwoGapFrame n)
    (b : AState n psi) (hg : GapPair hpsi F b) (hr : SharedReady F b.conf) :
    DummyFront F.recovery (attemptStepConf hpsi F b (preparePort F)) (F.recovery.d - 1) := by
  have hd := F.recovery.hd
  have hp : F.recovery.d - 1 + 1 = F.recovery.d := by omega
  have ha : (b.conf (deletePort F)).label = nextLabel hpsi (b.conf (preparePort F)) := by
    have h := hg.recovery.2.2.1 (F.recovery.d - 1) (by omega)
    simpa only [hp, F.shared, preparePort, deletePort] using h
  have hrow := incoming_fire_pair hpsi (b.conf (preparePort F)) (b.conf (deletePort F))
    (hg.recovery.2.1 (F.recovery.d - 1) (by omega) (by omega)) hg.attack.1.1 hr ha
  constructor
  · change (attemptStepConf hpsi F b (preparePort F) (preparePort F)).bullet = (1 : Fin 3)
    rw [attemptStepConf_eq_sinkStepC, sinkStepC, updatePair_initiator, preparePort_right, hrow]
  · intro k hk hkd
    have he : k = F.recovery.d := by omega
    subst k
    rw [F.shared]
    change (attemptStepConf hpsi F b (preparePort F) (deletePort F)).bullet = (0 : Fin 3)
    rw [attemptStepConf_eq_sinkStepC, sinkStepC, preparePort_right,
      updatePair_responder _ _ _ _ (preparePort_ne_deletePort F).symm, hrow]

end LDSinkTwoGapRaceEntranceDummyService

#print axioms LDSinkTwoGapRaceEntranceDummyService.dummy_nonservice
#print axioms LDSinkTwoGapRaceEntranceDummyService.dummy_transfer
#print axioms LDSinkTwoGapRaceEntranceDummyService.dummy_front_row
#print axioms LDSinkTwoGapRaceEntranceDummyService.dummy_not_sharedReady
#print axioms LDSinkTwoGapRaceEntranceDummyService.prepare_dummy_front
