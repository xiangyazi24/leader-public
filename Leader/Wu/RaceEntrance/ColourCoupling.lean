import Leader.Wu.RaceEntrance.LocalService

set_option autoImplicit false

open PPLLRepair LDSinkKernelC LDSinkGapCleanup
open LDSinkProtectedAbsorption LDSinkGapDoneInvariant LDTwoGapFrame
open LDSinkTwoGapNoResetKernel LDSinkTwoGapReachInvariant
open LDSinkTwoGapRaceEntranceLocalService

namespace LDSinkTwoGapRaceEntranceColourCoupling

variable {n psi : Nat}

/-!
Exact local rows for the FIRE-direction time correction.  Incoming FIRE
places a dummy one cell into the gap during the firing interaction itself.
Outgoing FIRE leaves a live bullet at the shooter; the next incoming edge
places it in that same cell.  After this one extra service interaction,
the two recovery projections differ only in bullet colour and shooter shield.
No unbiasedness at an arbitrary arrival time is asserted.
-/

/-- Responder FIRE and the following MOVE happen in the same interaction. -/
theorem incoming_fire_pair (hpsi : psi > 0) (l r : AgentState psi)
    (hl : l.leader = false) (hr : r.leader = true)
    (hs : r.signal_B = (1 : Fin 2)) (ha : r.label = nextLabel hpsi l) :
    sinkKernelC hpsi l r =
      ({ l with bullet := 1, signal_B := 0 },
       { r with bullet := 0, shield := false, signal_B := 0 }) := by
  simp [sinkKernelC, eliminateLeadersNoCollisionFire, hl, hr, hs,
    absorbProtectedMove, eliminateLeadersNoCollisionZeroLeaderEgressMove,
    nextLabel, ha, eliminateLeadersNoCollisionSignalLeaderSink, dummyBulletSink]
  rfl

/-- Quiet follower MOVE treats the two nonzero bullet colours identically:
the exact colour is copied one cell left and both signal fields are zero. -/
theorem quiet_transfer_pair (hpsi : psi > 0) (l r : AgentState psi)
    (hl : l.leader = false) (hs : r.signal_B = (0 : Fin 2))
    (hb : r.bullet ≠ (0 : Fin 3)) (ha : r.label = nextLabel hpsi l) :
    sinkKernelC hpsi l r =
      ({ l with bullet := r.bullet, signal_B := 0 },
       { r with bullet := 0, signal_B := 0 }) := by
  have hp : 0 < r.bullet.val := by
    have hz : r.bullet.val ≠ 0 := by
      intro he
      exact hb (Fin.ext he)
    omega
  simp [sinkKernelC, eliminateLeadersNoCollisionFire, hl, hs,
    absorbProtectedMove, eliminateLeadersNoCollisionZeroLeaderEgressMove,
    nextLabel, ha, hp, eliminateLeadersNoCollisionSignalLeaderSink, dummyBulletSink]
  rfl

/-- At a protected surviving victim the live and dummy rows have identical
outputs after clearing the incoming bullet.  This includes SIGNAL after
absorption and the final dummy sink. -/
theorem protected_colour_clear (hpsi : psi > 0) (l r : AgentState psi)
    (hl : l.leader = true) (hs : l.signal_B = (0 : Fin 2))
    (hp : l.shield = true) (hr : r.leader = false)
    (ht : r.signal_B = (0 : Fin 2)) (c : Fin 3)
    (hc : c = 1 ∨ c = 2) :
    sinkKernelC hpsi l { r with bullet := c } =
      (l, { r with bullet := 0, signal_B := 1 }) := by
  rcases hc with rfl | rfl <;>
    (simp [sinkKernelC, eliminateLeadersNoCollisionFire, hl, hs, hr,
      absorbProtectedMove, hp, eliminateLeadersNoCollisionZeroLeaderEgressMove,
      eliminateLeadersNoCollisionSignalLeaderSink, dummyBulletSink, ht] <;> rfl)

/-- An outgoing FIRE needs one additional incoming interaction to put its
live shot where an incoming FIRE places the dummy immediately. -/
theorem outgoing_then_incoming_pair (hpsi : psi > 0)
    (l r outside : AgentState psi) (hl : l.leader = false)
    (hr : r.leader = true) (hs : r.signal_B = (1 : Fin 2))
    (ha : r.label = nextLabel hpsi l) :
    sinkKernelC hpsi l (sinkKernelC hpsi r outside).1 =
      ({ l with bullet := 2, signal_B := 0 },
       { r with bullet := 0, shield := true, signal_B := 0 }) := by
  rw [kernelC_outgoing_fire_left hpsi r outside hr hs]
  exact quiet_transfer_pair hpsi l
    { r with bullet := 2, shield := true, signal_B := 0 } hl rfl
    (by change (2 : Fin 3) ≠ 0; decide) ha

private theorem predecessor_right (G : GapFrame n) :
    G.ring.rightNeighbor (G.pos (G.d - 1)) = G.pos G.d := by
  rw [gap_rightNeighbor_pos]
  have hd := G.hd
  congr 1
  omega

private theorem predecessor_ne_shooter (G : GapFrame n) :
    G.pos (G.d - 1) ≠ G.pos G.d := by
  intro he
  have h := pos_injective_below_n G (G.d - 1) G.d (by have h := G.hdn; omega)
    G.hdn he
  have hd := G.hd
  omega

/-- The exact comparison on a physical ring.  No outside state hypothesis
is needed: outgoing FIRE protects its shooter, and its outside responder
is disjoint from the incoming follower.  Each displayed cell preserves
every field not explicitly changed below. -/
theorem physical_firing_time_correction (hpsi : psi > 0)
    (G : GapFrame n) (hdn : G.d + 1 < n)
    (C : Fin n → AgentState psi) (hi : GapInvariant hpsi G C)
    (hc : CleanReady G C) :
    let a := G.pos (G.d - 1)
    let b := G.pos G.d
    let dummy := sinkStepC hpsi G C a
    let live := sinkStepC hpsi G (sinkStepC hpsi G C b) a
    dummy a = { C a with bullet := 1, signal_B := 0 } ∧
    dummy b = { C b with bullet := 0, shield := false, signal_B := 0 } ∧
    live a = { C a with bullet := 2, signal_B := 0 } ∧
    live b = { C b with bullet := 0, shield := true, signal_B := 0 } := by
  dsimp only
  let a := G.pos (G.d - 1)
  let b := G.pos G.d
  have hd := G.hd
  have hab : a ≠ b := predecessor_ne_shooter G
  have hra : G.ring.rightNeighbor a = b := predecessor_right G
  have hl : (C a).leader = false := hi.2.1 (G.d - 1) (by omega) (by omega)
  have hr : (C b).leader = true := hi.1.2
  have hs : (C b).signal_B = (1 : Fin 2) := hc.1
  have ha : (C b).label = nextLabel hpsi (C a) := by
    have ht := hi.2.2.1 (G.d - 1) (by omega)
    have he : G.d - 1 + 1 = G.d := by omega
    simpa only [he] using ht
  have hpair := incoming_fire_pair hpsi (C a) (C b) hl hr hs ha
  have hfa : sinkStepC hpsi G C b a = C a := by
    apply sinkStepC_other _ _ _ _ _ hab
    rw [gap_rightNeighbor_pos]
    intro he
    have ht := pos_injective_below_n G (G.d - 1) (G.d + 1) (by omega) hdn he
    omega
  have hfb : sinkStepC hpsi G C b b =
      (sinkKernelC hpsi (C b) (C (G.ring.rightNeighbor b))).1 := by
    simp only [sinkStepC, updatePair_initiator]
  have hlpair :
      sinkKernelC hpsi (sinkStepC hpsi G C b a)
        (sinkStepC hpsi G C b b) =
      ({ C a with bullet := 2, signal_B := 0 },
       { C b with bullet := 0, shield := true, signal_B := 0 }) := by
    rw [hfa, hfb]
    exact outgoing_then_incoming_pair hpsi (C a) (C b)
      (C (G.ring.rightNeighbor b)) hl hr hs ha
  change
    sinkStepC hpsi G C a a = { C a with bullet := 1, signal_B := 0 } ∧
    sinkStepC hpsi G C a b = { C b with bullet := 0, shield := false, signal_B := 0 } ∧
    sinkStepC hpsi G (sinkStepC hpsi G C b) a a =
      { C a with bullet := 2, signal_B := 0 } ∧
    sinkStepC hpsi G (sinkStepC hpsi G C b) a b =
      { C b with bullet := 0, shield := true, signal_B := 0 }
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [sinkStepC, updatePair_initiator, hra]
    exact congrArg Prod.fst hpair
  · rw [sinkStepC, hra, updatePair_responder _ _ _ _ hab.symm]
    exact congrArg Prod.snd hpair
  · rw [sinkStepC, updatePair_initiator, hra]
    exact congrArg Prod.fst hlpair
  · rw [sinkStepC, hra, updatePair_responder _ _ _ _ hab.symm]
    exact congrArg Prod.snd hlpair

end LDSinkTwoGapRaceEntranceColourCoupling

#print axioms LDSinkTwoGapRaceEntranceColourCoupling.incoming_fire_pair
#print axioms LDSinkTwoGapRaceEntranceColourCoupling.quiet_transfer_pair
#print axioms LDSinkTwoGapRaceEntranceColourCoupling.protected_colour_clear
#print axioms LDSinkTwoGapRaceEntranceColourCoupling.physical_firing_time_correction
