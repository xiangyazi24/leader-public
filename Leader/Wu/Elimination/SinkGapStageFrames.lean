import Leader.Wu.Elimination.SinkGapDoneInvariant
import Leader.Wu.Elimination.TwoGapFrame

open LDSinkGapCleanup LDSinkKernelC LDSinkProtectedAbsorption
  LDSinkGapDoneInvariant LDTwoGapFrame PPLLRepair

namespace LDSinkGapBlockedPreStep

set_option autoImplicit false

variable {n ψ : Nat} (hψ : ψ > 0) (F : GapFrame n)
  (C : Fin n → AgentState ψ) (e : Fin n)

private theorem edge_of_head (k : Nat) (hk : 1 ≤ k)
    (he : F.ring.rightNeighbor e = F.pos k) : e = F.pos (k - 1) := by
  have h : F.ring.rightNeighbor e = F.ring.rightNeighbor (F.pos (k - 1)) := by
    simpa only [gap_rightNeighbor_pos, Nat.sub_add_cancel hk] using he
  apply Fin.ext
  have hv := congrArg Fin.val h
  change (e.val + 1) % n = ((F.pos (k - 1)).val + 1) % n at hv
  have heB := e.isLt
  have hfB := (F.pos (k - 1)).isLt
  by_cases ha : e.val + 1 < n <;> by_cases hb : (F.pos (k - 1)).val + 1 < n
  · rw [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at hv
    omega
  · have hh : (F.pos (k - 1)).val + 1 = n := by omega
    rw [hh, Nat.mod_self, Nat.mod_eq_of_lt ha] at hv
    omega
  · have hh : e.val + 1 = n := by omega
    rw [hh, Nat.mod_self, Nat.mod_eq_of_lt hb] at hv
    omega
  · omega

private theorem head_ne : F.ring.rightNeighbor e ≠ e := by
  intro h
  have hv := congrArg Fin.val h
  change (e.val + 1) % n = e.val at hv
  have he := e.isLt
  have hd := F.hd
  have hdn := F.hdn
  by_cases ha : e.val + 1 < n
  · rw [Nat.mod_eq_of_lt ha] at hv
    omega
  · have hh : e.val + 1 = n := by omega
    rw [hh, Nat.mod_self] at hv
    omega

private theorem pos_ne (i j : Nat) (hi : i ≤ F.d) (hj : j ≤ F.d)
    (hij : i ≠ j) : F.pos i ≠ F.pos j := by
  intro h
  exact hij (pos_injective_below_n F i j
    (Nat.lt_of_le_of_lt hi F.hdn) (Nat.lt_of_le_of_lt hj F.hdn) h)

theorem protected_edge_is_victim_edge (k : Nat) (hi : GapInvariant hψ F C)
    (hg : ProtectedGuard hψ (C e) (C (F.ring.rightNeighbor e)))
    (hk : 1 ≤ k) (hkd : k ≤ F.d)
    (he : F.ring.rightNeighbor e = F.pos k) : e = F.pos 0 := by
  have hp := edge_of_head F e k hk he
  have hl := (protectedGuard_input_leaders hψ _ _ hg).1
  by_cases h : k = 1
  · simpa [h] using hp
  · have hf := hi.2.1 (k - 1) (by omega) (by omega)
    have ht : (C (F.pos (k - 1))).leader = true := by
      simpa only [hp] using hl
    simp_all

/-! Stage-local field frames.  These deliberately do not simplify the whole
variant-C kernel in one call. -/

private theorem fire_leaders (l r : AgentState ψ) :
    (eliminateLeadersNoCollisionFire hψ l r).1.leader = l.leader ∧
    (eliminateLeadersNoCollisionFire hψ l r).2.leader = r.leader := by
  constructor <;>
    (simp only [eliminateLeadersNoCollisionFire] <;>
      (repeat split <;> rfl))

private theorem fire_left_zero (l r : AgentState ψ)
    (hs : l.signal_B = (0 : Fin 2)) :
    (eliminateLeadersNoCollisionFire hψ l r).1.signal_B = (0 : Fin 2) := by
  unfold eliminateLeadersNoCollisionFire
  dsimp only
  repeat (first | exact hs | rfl | split)

private theorem fire_right_zero (l r : AgentState ψ)
    (hs : r.signal_B = (0 : Fin 2)) :
    (eliminateLeadersNoCollisionFire hψ l r).2.signal_B = (0 : Fin 2) := by
  unfold eliminateLeadersNoCollisionFire
  dsimp only
  repeat (first | exact hs | rfl | split)

private theorem move_left_follower (nl : Fin ψ) (l r : AgentState ψ)
    (hl : l.leader = false) :
    (absorbProtectedMove hψ nl l r).1.leader = false := by
  unfold absorbProtectedMove
  try unfold eliminateLeadersNoCollisionZeroLeaderEgressMove
  try unfold eliminateLeadersNoCollisionMove
  repeat (first | exact hl | rfl | split)

private theorem move_right_leader (nl : Fin ψ) (l r : AgentState ψ) :
    (absorbProtectedMove hψ nl l r).2.leader = r.leader := by
  unfold absorbProtectedMove
  try unfold eliminateLeadersNoCollisionZeroLeaderEgressMove
  try unfold eliminateLeadersNoCollisionMove
  repeat (first | rfl | split)

private theorem move_left_zero (nl : Fin ψ) (l r : AgentState ψ)
    (hs : l.signal_B = (0 : Fin 2)) :
    (absorbProtectedMove hψ nl l r).1.signal_B = (0 : Fin 2) := by
  unfold absorbProtectedMove
  try unfold eliminateLeadersNoCollisionZeroLeaderEgressMove
  try unfold eliminateLeadersNoCollisionMove
  repeat (first | exact hs | rfl | split)

private theorem move_right_signal (nl : Fin ψ) (l r : AgentState ψ) :
    (absorbProtectedMove hψ nl l r).2.signal_B = r.signal_B := by
  unfold absorbProtectedMove
  try unfold eliminateLeadersNoCollisionZeroLeaderEgressMove
  try unfold eliminateLeadersNoCollisionMove
  repeat (first | rfl | split)

private theorem move_right_clear (nl : Fin ψ) (l r : AgentState ψ)
    (hl : l.leader = false) :
    (absorbProtectedMove hψ nl l r).2.bullet = (0 : Fin 3) := by
  have hp : ¬ (l.leader = true ∧ l.shield = true ∧
      r.leader = false ∧ r.bullet = (2 : Fin 3)) := by
    intro h
    have hbad := h.1
    rw [hl] at hbad
    cases hbad
  simp only [absorbProtectedMove, if_neg hp]
  unfold eliminateLeadersNoCollisionZeroLeaderEgressMove
  try unfold eliminateLeadersNoCollisionMove
  by_cases hleader : r.bullet.val > 0 ∧ l.leader = true
  · have hbad := hleader.2
    rw [hl] at hbad
    cases hbad
  · rw [if_neg hleader]
    by_cases hmove : r.bullet.val > 0 ∧ l.leader = false
    · rw [if_pos hmove]
      split <;> rfl
    · rw [if_neg hmove]
      have hz : ¬ r.bullet.val > 0 := by
        intro hpos
        exact hmove ⟨hpos, hl⟩
      change r.bullet = (0 : Fin 3)
      apply Fin.ext
      change r.bullet.val = 0
      omega

private theorem signal_leaders (nl : Fin ψ) (l r : AgentState ψ) :
    (eliminateLeadersNoCollisionSignalLeaderSink nl l r).1.leader = l.leader ∧
    (eliminateLeadersNoCollisionSignalLeaderSink nl l r).2.leader = r.leader := by
  constructor <;>
    (unfold eliminateLeadersNoCollisionSignalLeaderSink
     dsimp only
     repeat (first | rfl | split))

private theorem signal_left_signal (nl : Fin ψ) (l r : AgentState ψ) :
    (eliminateLeadersNoCollisionSignalLeaderSink nl l r).1.signal_B =
      l.signal_B := by
  rfl

private theorem signal_right_bullet (nl : Fin ψ) (l r : AgentState ψ) :
    (eliminateLeadersNoCollisionSignalLeaderSink nl l r).2.bullet = r.bullet := by
  unfold eliminateLeadersNoCollisionSignalLeaderSink
  dsimp only
  repeat (first | rfl | split)

private theorem signal_right_zero (nl : Fin ψ) (l r : AgentState ψ)
    (hl : l.leader = false)
    (hs : l.signal_B = (0 : Fin 2))
    (ht : r.signal_B = (0 : Fin 2)) :
    (eliminateLeadersNoCollisionSignalLeaderSink nl l r).2.signal_B =
      (0 : Fin 2) := by
  unfold eliminateLeadersNoCollisionSignalLeaderSink
  dsimp only
  split
  · split
    · rfl
    · have hlt : ¬ l.leader = true := by
        intro h
        rw [hl] at h
        cases h
      dsimp only
      rw [if_neg hlt, hs, ht]
      apply Fin.ext
      rfl
  · exact ht
private theorem dummy_leaders (q : AgentState ψ × AgentState ψ) :
    (dummyBulletSink q).1.leader = q.1.leader ∧
    (dummyBulletSink q).2.leader = q.2.leader := by
  constructor <;>
    (unfold dummyBulletSink
     dsimp only
     repeat (first | rfl | split))

private theorem dummy_signals (q : AgentState ψ × AgentState ψ) :
    (dummyBulletSink q).1.signal_B = q.1.signal_B ∧
    (dummyBulletSink q).2.signal_B = q.2.signal_B := by
  constructor <;>
    (unfold dummyBulletSink
     dsimp only
     repeat (first | rfl | split))

private theorem dummy_right_zero (q : AgentState ψ × AgentState ψ)
    (hb : q.2.bullet = (0 : Fin 3)) :
    (dummyBulletSink q).2.bullet = (0 : Fin 3) := by
  unfold dummyBulletSink
  dsimp only
  repeat (first | exact hb | rfl | split)

private theorem left_follower (l r : AgentState ψ) (hl : l.leader = false) :
    (sinkKernelC hψ l r).1.leader = false := by
  let nl : Fin ψ := ⟨(l.label.val + 1) % ψ, Nat.mod_lt _ hψ⟩
  let q0 := eliminateLeadersNoCollisionFire hψ l r
  let q1 := absorbProtectedMove hψ nl q0.1 q0.2
  let q2 := eliminateLeadersNoCollisionSignalLeaderSink nl q1.1 q1.2
  have h0 := (fire_leaders hψ l r).1.trans hl
  have h1 := move_left_follower hψ nl q0.1 q0.2 h0
  have h2 := (signal_leaders nl q1.1 q1.2).1
  have h3 := (dummy_leaders q2).1
  change (dummyBulletSink q2).1.leader = false
  exact h3.trans (h2.trans h1)

private theorem right_leader (l r : AgentState ψ) :
    (sinkKernelC hψ l r).2.leader = r.leader := by
  let nl : Fin ψ := ⟨(l.label.val + 1) % ψ, Nat.mod_lt _ hψ⟩
  let q0 := eliminateLeadersNoCollisionFire hψ l r
  let q1 := absorbProtectedMove hψ nl q0.1 q0.2
  let q2 := eliminateLeadersNoCollisionSignalLeaderSink nl q1.1 q1.2
  have h0 := (fire_leaders hψ l r).2
  have h1 := move_right_leader hψ nl q0.1 q0.2
  have h2 := (signal_leaders nl q1.1 q1.2).2
  have h3 := (dummy_leaders q2).2
  change (dummyBulletSink q2).2.leader = r.leader
  exact h3.trans (h2.trans (h1.trans h0))

private theorem left_zero (l r : AgentState ψ)
    (hs : l.signal_B = (0 : Fin 2)) :
    (sinkKernelC hψ l r).1.signal_B = (0 : Fin 2) := by
  let nl : Fin ψ := ⟨(l.label.val + 1) % ψ, Nat.mod_lt _ hψ⟩
  let q0 := eliminateLeadersNoCollisionFire hψ l r
  let q1 := absorbProtectedMove hψ nl q0.1 q0.2
  let q2 := eliminateLeadersNoCollisionSignalLeaderSink nl q1.1 q1.2
  have h0 := fire_left_zero hψ l r hs
  have h1 := move_left_zero hψ nl q0.1 q0.2 h0
  have h2 := signal_left_signal nl q1.1 q1.2
  have h3 := (dummy_signals q2).1
  change (dummyBulletSink q2).1.signal_B = (0 : Fin 2)
  exact h3.trans (h2.trans h1)

private theorem pair_zero (l r : AgentState ψ) (hl : l.leader = false)
    (hs : l.signal_B = (0 : Fin 2)) (ht : r.signal_B = (0 : Fin 2)) :
    (sinkKernelC hψ l r).2.signal_B = (0 : Fin 2) := by
  let nl : Fin ψ := ⟨(l.label.val + 1) % ψ, Nat.mod_lt _ hψ⟩
  let q0 := eliminateLeadersNoCollisionFire hψ l r
  let q1 := absorbProtectedMove hψ nl q0.1 q0.2
  let q2 := eliminateLeadersNoCollisionSignalLeaderSink nl q1.1 q1.2
  have h0l := (fire_leaders hψ l r).1.trans hl
  have h0s := fire_left_zero hψ l r hs
  have h0t := fire_right_zero hψ l r ht
  have h1l := move_left_follower hψ nl q0.1 q0.2 h0l
  have h1s := move_left_zero hψ nl q0.1 q0.2 h0s
  have h1t := (move_right_signal hψ nl q0.1 q0.2).trans h0t
  have h2 := signal_right_zero nl q1.1 q1.2 h1l h1s h1t
  have h3 := (dummy_signals q2).2
  change (dummyBulletSink q2).2.signal_B = (0 : Fin 2)
  exact h3.trans h2

private theorem right_clear (l r : AgentState ψ) (hl : l.leader = false) :
    (sinkKernelC hψ l r).2.bullet = (0 : Fin 3) := by
  let nl : Fin ψ := ⟨(l.label.val + 1) % ψ, Nat.mod_lt _ hψ⟩
  let q0 := eliminateLeadersNoCollisionFire hψ l r
  let q1 := absorbProtectedMove hψ nl q0.1 q0.2
  let q2 := eliminateLeadersNoCollisionSignalLeaderSink nl q1.1 q1.2
  have h0 := (fire_leaders hψ l r).1.trans hl
  have h1 := move_right_clear hψ nl q0.1 q0.2 h0
  have h2 := (signal_right_bullet nl q1.1 q1.2).trans h1
  change (dummyBulletSink q2).2.bullet = (0 : Fin 3)
  exact dummy_right_zero q2 h2

/-! These three strong-hypothesis rows already elaborate.  Keep the
old finite case split only for them; the generic field frames above no longer
simplify the entire kernel. -/

macro "c2b_concrete" : tactic => `(tactic|
  (simp_all [sinkKernelC, absorbProtectedMove, eliminateLeadersNoCollisionFire,
    eliminateLeadersNoCollisionZeroLeaderEgressMove, eliminateLeadersNoCollisionMove,
    eliminateLeadersNoCollisionSignalLeaderSink, dummyBulletSink, nextLabel] <;>
   repeat (first | assumption | rfl | contradiction | omega |
     (apply Fin.ext; omega) | (split <;> simp_all))))

private theorem no_fresh (l r : AgentState ψ) (hl : l.leader = false)
    (hf : r.leader = true → r.signal_B = (0 : Fin 2))
    (hb : l.bullet = (0 : Fin 3)) (hc : r.bullet = (0 : Fin 3)) :
    (sinkKernelC hψ l r).1.bullet = (0 : Fin 3) := by
  c2b_concrete

private theorem transfer_zero (l r : AgentState ψ) (hl : l.leader = false)
    (hs : r.signal_B = (0 : Fin 2)) (hb : r.bullet ≠ (0 : Fin 3))
    (ha : r.label = nextLabel hψ l) :
    (sinkKernelC hψ l r).1.signal_B = (0 : Fin 2) ∧
    (sinkKernelC hψ l r).2.signal_B = (0 : Fin 2) := by
  constructor <;> c2b_concrete

private theorem survives_clear (l r : AgentState ψ) (hl : l.leader = true)
    (hr : r.leader = false)
    (hs : (sinkKernelC hψ l r).1.leader = true) :
    (sinkKernelC hψ l r).2.bullet = (0 : Fin 3) := by
  have bc : ∀ b : Fin 3, b = 0 ∨ b = 1 ∨ b = 2 := by decide
  have sc : ∀ s : Fin 2, s = 0 ∨ s = 1 := by decide
  rcases bc r.bullet with hb | hb | hb <;>
    rcases sc l.signal_B with ht | ht <;> cases hh : l.shield <;> c2b_concrete

private theorem atL : sinkStepC hψ F C e e =
    (sinkKernelC hψ (C e) (C (F.ring.rightNeighbor e))).1 := by
  simp [sinkStepC, updatePair]

private theorem atR : sinkStepC hψ F C e (F.ring.rightNeighbor e) =
    (sinkKernelC hψ (C e) (C (F.ring.rightNeighbor e))).2 := by
  simp [sinkStepC, updatePair, head_ne F e]

private theorem bullet_tail (hi : GapInvariant hψ F C) (k : Nat)
    (hk : 1 ≤ k) (hkd : k ≤ F.d)
    (hb : (C (F.pos k)).bullet ≠ (0 : Fin 3)) :
    ∀ j, k ≤ j → j ≤ F.d →
      (C (F.pos j)).signal_B = (0 : Fin 2) :=
  fun j hkj hjd => hi.2.2.2 k j hk hkd hb hkj hjd

private theorem step_basic (hi : GapInvariant hψ F C)
    (hn : ¬ EndpointDeleted F (sinkStepC hψ F C e)) :
    GapEndpointsPresent F (sinkStepC hψ F C e) ∧
    GapInteriorFollowers F (sinkStepC hψ F C e) ∧
    GapLabelAligned hψ F (sinkStepC hψ F C e) := by
  have hp := kernelC_labels hψ (C e) (C (F.ring.rightNeighbor e))
  have labels : ∀ v, (sinkStepC hψ F C e v).label = (C v).label := by
    intro v
    by_cases h : v = e
    · simpa only [h, atL] using hp.1
    by_cases h' : v = F.ring.rightNeighbor e
    · simpa only [h', atR] using hp.2
    · rw [sinkStepC_other hψ F C e v h h']
  refine ⟨?_, ?_, ?_⟩
  · cases h0 : (sinkStepC hψ F C e (F.pos 0)).leader <;>
      cases hd : (sinkStepC hψ F C e (F.pos F.d)).leader <;>
      simp_all [GapEndpointsPresent, EndpointDeleted]
  · intro k hk hkd
    have hf := hi.2.1 k hk hkd
    by_cases h : F.pos k = e
    · simpa only [h, atL] using
        left_follower hψ (C e) (C (F.ring.rightNeighbor e))
          (by simpa only [h] using hf)
    by_cases h' : F.pos k = F.ring.rightNeighbor e
    · simpa only [h', atR, right_leader] using hf
    · rw [sinkStepC_other hψ F C e (F.pos k) h h']
      exact hf
  · intro k hk
    simpa only [nextLabel, labels] using hi.2.2.1 k hk

private theorem shooter_zero (hi : GapInvariant hψ F C)
    (hn : ¬ CleanReady F C) :
    (C (F.pos F.d)).signal_B = (0 : Fin 2) := by
  by_cases hzv : (C (F.pos F.d)).signal_B.val = 0
  · apply Fin.ext
    exact hzv
  · have hs : (C (F.pos F.d)).signal_B = (1 : Fin 2) := by
      apply Fin.ext
      omega
    exfalso
    apply hn
    refine ⟨hs, ?_⟩
    intro k hk hkd
    by_cases hb : (C (F.pos k)).bullet = (0 : Fin 3)
    · exact hb
    · have hz := hi.2.2.2 k F.d hk hkd hb hkd (Nat.le_refl _)
      have hbad : (1 : Fin 2) = (0 : Fin 2) := hs.symm.trans hz
      exact False.elim ((by decide : (1 : Fin 2) ≠ (0 : Fin 2)) hbad)

private theorem tail_step (hi : GapInvariant hψ F C) (a : Nat) (ha : 1 ≤ a)
    (hz : ∀ i, a ≤ i → i ≤ F.d →
      (C (F.pos i)).signal_B = (0 : Fin 2)) :
    ∀ j, a < j → j ≤ F.d →
      (sinkStepC hψ F C e (F.pos j)).signal_B = (0 : Fin 2) := by
  intro j haj hjd
  by_cases hl : F.pos j = e
  · have hzj := hz j (by omega) hjd
    rw [hl] at hzj
    rw [hl, atL]
    exact left_zero hψ (C e) (C (F.ring.rightNeighbor e)) hzj
  by_cases hr : F.pos j = F.ring.rightNeighbor e
  · have hp := edge_of_head F e j (by omega) hr.symm
    have hlf : (C e).leader = false := by
      rw [hp]
      exact hi.2.1 (j - 1) (by omega) (by omega)
    have hls := hz (j - 1) (by omega) (by omega)
    rw [← hp] at hls
    have hrs := hz j (by omega) hjd
    rw [hr] at hrs
    rw [hr, atR]
    exact pair_zero hψ (C e) (C (F.ring.rightNeighbor e)) hlf hls hrs
  · rw [sinkStepC_other hψ F C e (F.pos j) hl hr]
    exact hz j (by omega) hjd

private theorem head_clear (hi : GapInvariant hψ F C)
    (hn : ¬ EndpointDeleted F (sinkStepC hψ F C e)) (k : Nat)
    (hk : 1 ≤ k) (hkd : k ≤ F.d)
    (he : F.ring.rightNeighbor e = F.pos k) :
    (sinkStepC hψ F C e (F.pos k)).bullet = (0 : Fin 3) := by
  have hp := edge_of_head F e k hk he
  by_cases h : k = 1
  · subst k
    have hE : e = F.pos 0 := by simpa using hp
    have hl := hi.1.1
    rw [← hE] at hl
    have hr : (C (F.ring.rightNeighbor e)).leader = false := by
      rw [he]
      exact hi.2.1 1 (by omega) (by have := F.hd; omega)
    have hs := (step_basic hψ F C e hi hn).1.1
    rw [← hE, atL] at hs
    rw [← he, atR]
    exact survives_clear hψ (C e) (C (F.ring.rightNeighbor e)) hl hr hs
  · have hl : (C e).leader = false := by
      rw [hp]
      exact hi.2.1 (k - 1) (by omega) (by omega)
    rw [← he, atR]
    exact right_clear hψ (C e) (C (F.ring.rightNeighbor e)) hl

private theorem preserve (hi : GapInvariant hψ F C) (hc : ¬ CleanReady F C)
    (hn : ¬ EndpointDeleted F (sinkStepC hψ F C e)) :
    GapInvariant hψ F (sinkStepC hψ F C e) := by
  have hs := shooter_zero hψ F C hi hc
  have hnf : ∀ i, 1 ≤ i → i ≤ F.d →
      (C (F.pos i)).leader = true →
      (C (F.pos i)).signal_B = (0 : Fin 2) := by
    intro i hi' hid hl
    by_cases h : i = F.d
    · rw [h]
      exact hs
    · have hf := hi.2.1 i hi' (by omega)
      rw [hf] at hl
      cases hl
  have hb := step_basic hψ F C e hi hn
  refine ⟨hb.1, hb.2.1, hb.2.2, ?_⟩
  intro k j hk hkd hbullet hkj hjd
  by_cases hh : F.pos k = F.ring.rightNeighbor e
  · exact False.elim
      (hbullet (head_clear hψ F C e hi hn k hk hkd hh.symm))
  by_cases ht : F.pos k = e
  · by_cases hd : k = F.d
    · have hj : j = k := by omega
      subst j
      rw [← hd, ht] at hs
      rw [ht, atL]
      exact left_zero hψ (C e) (C (F.ring.rightNeighbor e)) hs
    have hkl : k < F.d := by omega
    have hl := hi.2.1 k hk hkl
    rw [ht] at hl
    have hnext : F.ring.rightNeighbor e = F.pos (k + 1) := by
      rw [← ht, gap_rightNeighbor_pos]
    have hqb :
        (sinkKernelC hψ (C e) (C (F.ring.rightNeighbor e))).1.bullet ≠
          (0 : Fin 3) := by
      intro hz
      apply hbullet
      rw [ht, atL]
      exact hz
    by_cases hbl : (C e).bullet = (0 : Fin 3)
    · have hfresh :
          (C (F.ring.rightNeighbor e)).leader = true →
          (C (F.ring.rightNeighbor e)).signal_B = (0 : Fin 2) := by
        have h := hnf (k + 1) (by omega) (by omega)
        rw [← hnext] at h
        exact h
      have hbr : (C (F.ring.rightNeighbor e)).bullet ≠ (0 : Fin 3) := by
        intro hz
        exact hqb
          (no_fresh hψ (C e) (C (F.ring.rightNeighbor e))
            hl hfresh hbl hz)
      have hbr' : (C (F.pos (k + 1))).bullet ≠ (0 : Fin 3) := by
        rw [← hnext]
        exact hbr
      have hz := bullet_tail hψ F C hi (k + 1) (by omega) (by omega) hbr'
      have hsig := hz (k + 1) (Nat.le_refl _) (by omega)
      rw [← hnext] at hsig
      have ha := hi.2.2.1 k hkl
      rw [ht, ← hnext] at ha
      have hq := transfer_zero hψ (C e) (C (F.ring.rightNeighbor e))
        hl hsig hbr ha
      by_cases hj : j = k
      · subst j
        rw [ht, atL]
        exact hq.1
      by_cases hj' : j = k + 1
      · subst j
        rw [← hnext, atR]
        exact hq.2
      · exact tail_step hψ F C e hi (k + 1) (by omega) hz j (by omega) hjd
    · have hbk : (C (F.pos k)).bullet ≠ (0 : Fin 3) := by
        rw [ht]
        exact hbl
      have hz := bullet_tail hψ F C hi k hk hkd hbk
      by_cases hj : j = k
      · subst j
        have hzk := hz k (Nat.le_refl _) hkd
        rw [ht] at hzk
        rw [ht, atL]
        exact left_zero hψ (C e) (C (F.ring.rightNeighbor e)) hzk
      · exact tail_step hψ F C e hi k hk hz j (by omega) hjd
  · have hf := sinkStepC_other hψ F C e (F.pos k) ht hh
    have hbk : (C (F.pos k)).bullet ≠ (0 : Fin 3) := by
      intro hz
      apply hbullet
      rw [hf]
      exact hz
    have hz := bullet_tail hψ F C hi k hk hkd hbk
    by_cases hj : j = k
    · subst j
      rw [hf]
      exact hz k (Nat.le_refl _) hkd
    · exact tail_step hψ F C e hi k hk hz j (by omega) hjd

theorem sinkStepC_invariant_or_done' (hi : GapInvariant hψ F C)
    (hn : ¬ GapDoneC F C) :
    GapDoneC F (sinkStepC hψ F C e) ∨
      GapInvariant hψ F (sinkStepC hψ F C e) := by
  by_cases hd : EndpointDeleted F (sinkStepC hψ F C e)
  · exact Or.inl (Or.inr hd)
  · exact Or.inr
      (preserve hψ F C e hi
        (fun h => hn (Or.inl h)) hd)

theorem blocked_pre_steps_protected_or_fire
    (hb : GapBlocked F C) (hi : GapInvariant hψ F C) :
    ProtectedGuard hψ (C (F.pos 0))
      (C (F.ring.rightNeighbor (F.pos 0))) ∧
    GapInvariant hψ F (sinkStepC hψ F C (F.pos 0)) ∧
    (sinkStepC hψ F C (F.pos 0) (F.pos 1)).bullet = (0 : Fin 3) ∧
    (sinkStepC hψ F C (F.pos 0) (F.pos 1)).signal_B = (1 : Fin 2) := by
  have hd := F.hd
  have hl := hi.1.1
  have hr := hi.2.1 1 (by omega) (by omega)
  have hg : ProtectedGuard hψ (C (F.pos 0))
      (C (F.ring.rightNeighbor (F.pos 0))) := by
    rw [gap_rightNeighbor_pos]
    have hb1 := hb.1
    rcases hb.2.2 with hsh | hsg
    · by_cases hs : (C (F.pos 0)).signal_B = 1 <;>
        simp [ProtectedGuard, eliminateLeadersNoCollisionFire,
          hl, hr, hb1, hsh, hs]
    · simp [ProtectedGuard, eliminateLeadersNoCollisionFire,
        hl, hr, hb1, hsg]
  obtain ⟨s, fr⟩ := sinkStepC_protected_shape hψ F C (F.pos 0) hg
  have hf := fr (F.pos F.d)
    (pos_ne F F.d 0 (by omega) (by omega) (by omega))
    (by
      rw [gap_rightNeighbor_pos]
      exact pos_ne F F.d 1 (by omega) (by omega) (by omega))
  have hnd : ¬ EndpointDeleted F (sinkStepC hψ F C (F.pos 0)) := by
    intro h
    rcases h with h | h
    · have hh := s.2.2.1.trans hi.1.1
      rw [hh] at h
      cases h
    · rw [hf, hi.1.2] at h
      cases h
  have hnc : ¬ CleanReady F C :=
    fun h => gapBlocked_not_doneC hψ F C hb hi (Or.inl h)
  have hz :
      (sinkStepC hψ F C (F.pos 0) (F.pos 1)).bullet = (0 : Fin 3) ∧
      (sinkStepC hψ F C (F.pos 0) (F.pos 1)).signal_B = (1 : Fin 2) := by
    simpa only [gap_rightNeighbor_pos, Nat.zero_add] using And.intro s.1 s.2.1
  exact ⟨hg, preserve hψ F C (F.pos 0) hi hnc hnd, hz.1, hz.2⟩

theorem blocked_pre_other_edges_frame
    (hb : GapBlocked F C) (hi : GapInvariant hψ F C)
    (_he : e ≠ F.pos 0) :
    GapDoneC F (sinkStepC hψ F C e) ∨
      GapInvariant hψ F (sinkStepC hψ F C e) :=
  sinkStepC_invariant_or_done' hψ F C e hi
    (gapBlocked_not_doneC hψ F C hb hi)

end LDSinkGapBlockedPreStep

#print axioms LDSinkGapBlockedPreStep.protected_edge_is_victim_edge
#print axioms LDSinkGapBlockedPreStep.blocked_pre_steps_protected_or_fire
#print axioms LDSinkGapBlockedPreStep.blocked_pre_other_edges_frame
#print axioms LDSinkGapBlockedPreStep.sinkStepC_invariant_or_done'
