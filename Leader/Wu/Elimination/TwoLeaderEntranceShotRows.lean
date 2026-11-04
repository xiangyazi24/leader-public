import Leader.Wu.Elimination.TwoLeaderEntranceSelection

set_option autoImplicit false

open PPLLRepair LDSinkGapCleanup LDSinkKernelC LDSinkProtectedAbsorption
open LDTwoGapFrame K2TwoLeaderGeometry K2TwoLeaderEntranceCore
open LDSinkTwoGapAttemptCells

namespace K2TwoLeaderEntranceShotRows

variable {n ψ : Nat}

/-- A real unique live shot, its actual position, and a false victim shield.
Every field is physical data or a predicate on that same configuration. -/
structure ShotState (hψ : 0 < ψ) (F : TwoLeaderFrame n) where
  conf : Fin n → AgentState ψ
  invariant : WrapInvariant hψ F conf
  position : Nat
  shot : ShotAt F conf position
  shield : (conf (deletePort F)).shield = false

private theorem head_ne (G : GapFrame n) (e : Fin n) :
    G.ring.rightNeighbor e ≠ e := by
  intro h
  have hv := congrArg Fin.val h
  change (e.val + 1) % n = e.val at hv
  have he := e.isLt
  have hd := G.hd
  have hdn := G.hdn
  by_cases ha : e.val + 1 < n
  · rw [Nat.mod_eq_of_lt ha] at hv
    omega
  · have hh : e.val + 1 = n := by omega
    rw [hh, Nat.mod_self] at hv
    omega


private theorem at_left (hψ : ψ > 0) (G : GapFrame n)
    (C : Fin n → AgentState ψ) (e : Fin n) :
    sinkStepC hψ G C e e =
      (sinkKernelC hψ (C e) (C (G.ring.rightNeighbor e))).1 := by
  simp [sinkStepC, updatePair]


private theorem at_right (hψ : ψ > 0) (G : GapFrame n)
    (C : Fin n → AgentState ψ) (e : Fin n) :
    sinkStepC hψ G C e (G.ring.rightNeighbor e) =
      (sinkKernelC hψ (C e) (C (G.ring.rightNeighbor e))).2 := by
  have hh := head_ne G e
  simp [sinkStepC, updatePair, hh]


private theorem edge_of_head (G : GapFrame n) (e : Fin n) (k : Nat)
    (hk : 1 ≤ k) (he : G.ring.rightNeighbor e = G.pos k) :
    e = G.pos (k - 1) := by
  have h : G.ring.rightNeighbor e = G.ring.rightNeighbor (G.pos (k - 1)) := by
    simpa only [gap_rightNeighbor_pos, Nat.sub_add_cancel hk] using he
  apply Fin.ext
  have hv := congrArg Fin.val h
  change (e.val + 1) % n = ((G.pos (k - 1)).val + 1) % n at hv
  have heB := e.isLt
  have hfB := (G.pos (k - 1)).isLt
  by_cases ha : e.val + 1 < n <;> by_cases hb : (G.pos (k - 1)).val + 1 < n
  · rw [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at hv
    omega
  · have hh : (G.pos (k - 1)).val + 1 = n := by omega
    rw [hh, Nat.mod_self, Nat.mod_eq_of_lt ha] at hv
    omega
  · have hh : e.val + 1 = n := by omega
    rw [hh, Nat.mod_self, Nat.mod_eq_of_lt hb] at hv
    omega
  · omega


private theorem live_ne_zero {b : Fin 3} (hb : b = (2 : Fin 3)) :
    b ≠ (0 : Fin 3) := by
  rw [hb]
  decide


theorem old_bullet_unique (hψ : 0 < ψ) (F : TwoLeaderFrame n)
    (x : ShotState hψ F) (u v : Nat)
    (hu : 0 < u) (hud : u ≤ F.attack.d) (hv : 0 < v) (hvd : v ≤ F.attack.d)
    (hbu : (x.conf (F.attack.pos u)).bullet ≠ 0)
    (hbv : (x.conf (F.attack.pos v)).bullet ≠ 0) : u = v :=
  (x.shot.2.2.2 u hu hud hbu).trans (x.shot.2.2.2 v hv hvd hbv).symm

theorem attack_shooter_signal_zero (hψ : 0 < ψ) (F : TwoLeaderFrame n)
    (x : ShotState hψ F) : (x.conf (F.attack.pos F.attack.d)).signal_B = 0 :=
  x.invariant.2.2.2.2 x.position F.attack.d x.shot.1 x.shot.2.1
    (live_ne_zero x.shot.2.2.1) x.shot.2.1 (Nat.le_refl _)

theorem attack_cell_quiet (hψ : 0 < ψ) (F : TwoLeaderFrame n)
    (x : ShotState hψ F) (u : Nat) (hu : 0 < u) (hud : u ≤ F.attack.d) :
    Quiet (x.conf (F.attack.pos u)) := by
  by_cases he : u = F.attack.d
  · subst u
    exact Or.inr (attack_shooter_signal_zero hψ F x)
  · exact Or.inl (x.invariant.2.2.1 u hu (by omega))

theorem post_bullet_origin (hψ : ψ > 0) (F : TwoLeaderFrame n)
    (x : ShotState hψ F) (e : Fin n) (u : Nat)
    (hu : 0 < u) (hud : u ≤ F.attack.d)
    (hb : (rawConf hψ F x.conf e (F.attack.pos u)).bullet ≠ (0 : Fin 3)) :
    (x.conf (F.attack.pos u)).bullet ≠ (0 : Fin 3) ∨
      (u < F.attack.d ∧ e = F.attack.pos u ∧
       (x.conf (F.attack.pos (u + 1))).bullet ≠ (0 : Fin 3)) := by
  by_cases hz : (x.conf (F.attack.pos u)).bullet = (0 : Fin 3)
  · by_cases hl : F.attack.pos u = e
    · subst e
      by_cases he : u = F.attack.d
      · subst u
        have ho := pair_leader_left_zero hψ
          (x.conf (F.attack.pos F.attack.d))
          (x.conf (F.attack.ring.rightNeighbor (F.attack.pos F.attack.d)))
          x.invariant.2.1.2 (attack_shooter_signal_zero hψ F x) hz
        apply False.elim
        apply hb
        rw [rawConf_eq_gap hψ F F.attack, at_left]
        exact ho
      · have hul : u < F.attack.d := by omega
        by_cases hrz : (x.conf (F.attack.pos (u + 1))).bullet = (0 : Fin 3)
        · have ho := pair_quiet_zero hψ
            (x.conf (F.attack.pos u)) (x.conf (F.attack.pos (u + 1)))
            (attack_cell_quiet hψ F x u hu hud)
            (attack_cell_quiet hψ F x (u + 1) (by omega) (by omega)) hz hrz
          apply False.elim
          apply hb
          rw [rawConf_eq_gap hψ F F.attack, at_left, gap_rightNeighbor_pos]
          exact ho
        · exact Or.inr ⟨hul, rfl, hrz⟩
    · by_cases hr : F.attack.pos u = F.attack.ring.rightNeighbor e
      · have hq : Quiet (x.conf (F.attack.ring.rightNeighbor e)) := by
          rw [← hr]
          exact attack_cell_quiet hψ F x u hu hud
        have hz' : (x.conf (F.attack.ring.rightNeighbor e)).bullet =
            (0 : Fin 3) := by
          rw [← hr]
          exact hz
        have ho := pair_right_zero hψ (x.conf e)
          (x.conf (F.attack.ring.rightNeighbor e)) hq hz'
        apply False.elim
        apply hb
        rw [rawConf_eq_gap hψ F F.attack, hr, at_right]
        exact ho
      · apply False.elim
        apply hb
        rw [rawConf_eq_gap hψ F F.attack, sinkStepC_other hψ F.attack x.conf e
          (F.attack.pos u) hl hr]
        exact hz
  · exact Or.inl hz


/-- A positive responder beyond position one has an interior follower initiator. -/
theorem post_responder_zero (hψ : ψ > 0) (F : TwoLeaderFrame n)
    (x : ShotState hψ F) (e : Fin n) (u : Nat)
    (hu : 1 < u) (hud : u ≤ F.attack.d)
    (he : F.attack.ring.rightNeighbor e = F.attack.pos u) :
    (rawConf hψ F x.conf e (F.attack.pos u)).bullet = (0 : Fin 3) := by
  have he' := edge_of_head F.attack e u (by omega) he
  have hl : (x.conf e).leader = false := by
    rw [he']
    exact x.invariant.2.2.1 (u - 1) (by omega) (by omega)
  rw [rawConf_eq_gap hψ F F.attack, ← he, at_right]
  exact pair_follower_right_zero hψ (x.conf e)
    (x.conf (F.attack.ring.rightNeighbor e)) hl


/-- Uniqueness of all nonzero sector bullets, including dummy bullets. -/
theorem post_bullet_unique (hψ : ψ > 0) (F : TwoLeaderFrame n)
    (x : ShotState hψ F) (e : Fin n) (u v : Nat)
    (hu : 0 < u) (hud : u ≤ F.attack.d)
    (hv : 0 < v) (hvd : v ≤ F.attack.d)
    (hbu : (rawConf hψ F x.conf e (F.attack.pos u)).bullet ≠ (0 : Fin 3))
    (hbv : (rawConf hψ F x.conf e (F.attack.pos v)).bullet ≠ (0 : Fin 3)) :
    u = v := by
  rcases post_bullet_origin hψ F x e u hu hud hbu with hou | hou
  · rcases post_bullet_origin hψ F x e v hv hvd hbv with hov | hov
    · exact old_bullet_unique hψ F x u v hu hud hv hvd hou hov
    · rcases hov with ⟨hvl, hev, hov⟩
      have huv := old_bullet_unique hψ F x u (v + 1)
        hu hud (by omega) (by omega) hou hov
      have hhead : F.attack.ring.rightNeighbor e = F.attack.pos u := by
        rw [hev, gap_rightNeighbor_pos, ← huv]
      exact (hbu (post_responder_zero hψ F x e u (by omega) hud hhead)).elim
  · rcases hou with ⟨hul, heu, hou⟩
    rcases post_bullet_origin hψ F x e v hv hvd hbv with hov | hov
    · have huv := old_bullet_unique hψ F x (u + 1) v
        (by omega) (by omega) hv hvd hou hov
      have hhead : F.attack.ring.rightNeighbor e = F.attack.pos v := by
        rw [heu, gap_rightNeighbor_pos, huv]
      exact (hbv (post_responder_zero hψ F x e v (by omega) hvd hhead)).elim
    · rcases hov with ⟨hvl, _hev, hov⟩
      have huv := old_bullet_unique hψ F x (u + 1) (v + 1)
        (by omega) (by omega) (by omega) (by omega) hou hov
      omega


/-- The effective scheduler edge determines the actual live-shot motion. -/
def nextShotPosition (F : TwoLeaderFrame n) (t : Nat) (e : Fin n) : Nat :=
  if e = F.attack.pos (t - 1) then t - 1 else t

theorem transit_position_row (hψ : ψ > 0) (F : TwoLeaderFrame n)
    (x : ShotState hψ F) (t : Nat) (ht : 0 < t) (htd : t ≤ F.attack.d)
    (hb : (x.conf (F.attack.pos t)).bullet = (2 : Fin 3)) (e : Fin n)
    (hallow : 1 < t ∨ e ≠ deletePort F) :
    (rawConf hψ F x.conf e (F.attack.pos (nextShotPosition F t e))).bullet =
      (2 : Fin 3) := by
  by_cases he : e = F.attack.pos (t - 1)
  · have hlarge : 1 < t := by
      rcases hallow with hh | hh
      · exact hh
      · apply Classical.byContradiction
        intro hh'
        have ht1 : t = 1 := by omega
        apply hh
        simpa only [ht1, Nat.sub_self, deletePort] using he
    rw [nextShotPosition, if_pos he, he, rawConf_eq_gap hψ F F.attack,
      sinkStepC, updatePair_initiator, gap_rightNeighbor_pos,
      Nat.sub_add_cancel (by omega : 1 ≤ t)]
    apply (pair_transfer_live hψ
      (x.conf (F.attack.pos (t - 1))) (x.conf (F.attack.pos t))
      (x.invariant.2.2.1 (t - 1) (by omega) (by omega))
      (attack_cell_quiet hψ F x t (by omega) htd) hb ?_).1
    simpa only [Nat.sub_add_cancel (by omega : 1 ≤ t)] using
      x.invariant.2.2.2.1 (t - 1) (by omega)
  · rw [nextShotPosition, if_neg he, rawConf_eq_gap hψ F F.attack]
    by_cases htouched : e = F.attack.pos t
    · subst e
      rw [sinkStepC, updatePair_initiator]
      by_cases hlast : t = F.attack.d
      · subst t
        exact pair_leader_left_live hψ _ _ x.invariant.2.1.2
          (attack_shooter_signal_zero hψ F x) hb
      · have hlt : t < F.attack.d := by omega
        rw [gap_rightNeighbor_pos]
        have hz : (x.conf (F.attack.pos (t + 1))).bullet = (0 : Fin 3) := by
          by_cases hz : (x.conf (F.attack.pos (t + 1))).bullet = (0 : Fin 3)
          · exact hz
          · have heq := old_bullet_unique hψ F x t (t + 1)
              (by omega) htd (by omega) (by omega) (by rw [hb]; decide) hz
            omega
        exact pair_left_live_empty_right hψ _ _
          (attack_cell_quiet hψ F x t (by omega) htd)
          (attack_cell_quiet hψ F x (t + 1) (by omega) (by omega)) hb hz
    · rw [sinkStepC_other hψ F.attack x.conf e (F.attack.pos t)
        (fun h => htouched h.symm) ?_]
      · exact hb
      · intro hh
        exact he (edge_of_head F.attack e t (by omega) hh.symm)

/-- All positive-sector bullet provenance is retained on the actual row. -/
theorem shot_row (hψ : 0 < ψ) (F : TwoLeaderFrame n) (x : ShotState hψ F)
    (e : Fin n) (hallow : 1 < x.position ∨ e ≠ deletePort F) :
    ShotAt F (rawConf hψ F x.conf e) (nextShotPosition F x.position e) := by
  have ht := x.shot.1
  have htd := x.shot.2.1
  have hu : 0 < nextShotPosition F x.position e ∧
      nextShotPosition F x.position e ≤ F.attack.d := by
    unfold nextShotPosition
    split
    · rename_i he
      have hl : 1 < x.position := by
        rcases hallow with h | h
        · exact h
        · apply Classical.byContradiction
          intro hh
          have ht1 : x.position = 1 := by omega
          apply h
          simpa only [ht1, Nat.sub_self, deletePort] using he
      omega
    · omega
  have hlive := transit_position_row hψ F x x.position ht htd x.shot.2.2.1 e hallow
  refine ⟨hu.1, hu.2, hlive, ?_⟩
  intro u hup hud hb
  exact post_bullet_unique hψ F x e u (nextShotPosition F x.position e)
    hup hud hu.1 hu.2 hb (live_ne_zero hlive)

end K2TwoLeaderEntranceShotRows

#print axioms K2TwoLeaderEntranceShotRows.attack_cell_quiet
#print axioms K2TwoLeaderEntranceShotRows.post_bullet_unique
#print axioms K2TwoLeaderEntranceShotRows.transit_position_row
#print axioms K2TwoLeaderEntranceShotRows.shot_row
