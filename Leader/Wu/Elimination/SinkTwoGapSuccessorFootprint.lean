import Leader.Wu.Elimination.SinkTwoGapNoResetKernel
import Leader.Wu.Elimination.SinkTwoGapEpochSuccessor

open LDSinkGapCleanup LDSinkKernelC LDSinkProtectedAbsorption LDSinkGapDoneInvariant
  LDSinkGapBlockedPreStep LDSinkGapServiceRank LDSinkGapCleanupBound LDTwoGapFrame
  LDSinkTwoGapEpochDefs LDSinkTwoGapEpochCost LDSinkTwoGapEpochLaws
  LDSinkTwoGapEpochKernel LDSinkTwoGapEpochSuccessor LDSinkTwoGapNoResetKernel
  PPLLRepair FiniteUniformStoppingTree
open Classical

namespace LDSinkTwoGapAttemptResidual

set_option autoImplicit false

noncomputable section

variable {n ψ : Nat}

/-! The common physical successor and its two-cell footprint. -/

abbrev postConf (hψ : ψ > 0) (F : TwoGapFrame n)
    (x : AState n ψ) (e : Fin n) : Fin n → AgentState ψ :=
  attemptStepConf hψ F x e

def Touched (G : GapFrame n) (e v : Fin n) : Prop :=
  v = e ∨ v = G.ring.rightNeighbor e

theorem postConf_eq_attack (hψ : ψ > 0) (F : TwoGapFrame n)
    (x : AState n ψ) (e : Fin n) :
    postConf hψ F x e = sinkStepC hψ F.attack x.conf e := by
  rfl

theorem postConf_eq_recovery (hψ : ψ > 0) (F : TwoGapFrame n)
    (x : AState n ψ) (e : Fin n) :
    postConf hψ F x e = sinkStepC hψ F.recovery x.conf e := by
  exact (postConf_eq_attack hψ F x e).trans
    (twoGap_sinkStepC_eq hψ F x.conf e).symm

theorem cell_eq_of_not_touched (hψ : ψ > 0) (G : GapFrame n)
    (C : Fin n → AgentState ψ) (e v : Fin n)
    (hv : ¬ Touched G e v) :
    sinkStepC hψ G C e v = C v := by
  exact sinkStepC_other hψ G C e v
    (fun h => hv (Or.inl h)) (fun h => hv (Or.inr h))

theorem postConf_cell_eq_attack (hψ : ψ > 0) (F : TwoGapFrame n)
    (x : AState n ψ) (e v : Fin n)
    (hv : ¬ Touched F.attack e v) :
    postConf hψ F x e v = x.conf v := by
  rw [postConf_eq_attack]
  exact cell_eq_of_not_touched hψ F.attack x.conf e v hv

theorem postConf_cell_eq_recovery (hψ : ψ > 0) (F : TwoGapFrame n)
    (x : AState n ψ) (e v : Fin n)
    (hv : ¬ Touched F.recovery e v) :
    postConf hψ F x e v = x.conf v := by
  rw [postConf_eq_recovery]
  exact cell_eq_of_not_touched hψ F.recovery x.conf e v hv

/-! Lift the supplied pair-local no-creation fact to the whole ring.
The projection proofs mirror the existing C2b `atL`/`atR` proofs. -/

private theorem rightNeighbor_ne_self (G : GapFrame n) (e : Fin n) :
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

private theorem step_at_left (hψ : ψ > 0) (G : GapFrame n)
    (C : Fin n → AgentState ψ) (e : Fin n) :
    sinkStepC hψ G C e e =
      (sinkKernelC hψ (C e) (C (G.ring.rightNeighbor e))).1 := by
  simp [sinkStepC, updatePair]

private theorem step_at_right (hψ : ψ > 0) (G : GapFrame n)
    (C : Fin n → AgentState ψ) (e : Fin n) :
    sinkStepC hψ G C e (G.ring.rightNeighbor e) =
      (sinkKernelC hψ (C e) (C (G.ring.rightNeighbor e))).2 := by
  have hn := rightNeighbor_ne_self G e
  simp [sinkStepC, updatePair, hn, Ne.symm hn]

theorem follower_after_step (hψ : ψ > 0) (G : GapFrame n)
    (C : Fin n → AgentState ψ) (e v : Fin n)
    (hv : (C v).leader = false) :
    (sinkStepC hψ G C e v).leader = false := by
  by_cases hl : v = e
  · subst v
    rw [step_at_left]
    exact (LDSinkTwoGapEpochSuccessor.kernelC_no_leader_creation
      hψ (C e) (C (G.ring.rightNeighbor e))).1 hv
  · by_cases hr : v = G.ring.rightNeighbor e
    · subst v
      rw [step_at_right]
      exact (LDSinkTwoGapEpochSuccessor.kernelC_no_leader_creation
        hψ (C e) (C (G.ring.rightNeighbor e))).2 hv
    · rw [sinkStepC_other hψ G C e v hl hr]
      exact hv

/-- Shape preservation has no non-done precondition. Only the signal
component of GapInvariant needs a separate clean-pre argument. -/
theorem shape_after_step (hψ : ψ > 0) (G : GapFrame n)
    (C : Fin n → AgentState ψ) (e : Fin n)
    (hi : GapInvariant hψ G C)
    (hdel : ¬ EndpointDeleted G (sinkStepC hψ G C e)) :
    GapEndpointsPresent G (sinkStepC hψ G C e) ∧
    GapInteriorFollowers G (sinkStepC hψ G C e) ∧
    GapLabelAligned hψ G (sinkStepC hψ G C e) := by
  refine ⟨?_, ?_, ?_⟩
  · cases h0 : (sinkStepC hψ G C e (G.pos 0)).leader <;>
      cases hd : (sinkStepC hψ G C e (G.pos G.d)).leader <;>
      simp_all [GapEndpointsPresent, EndpointDeleted]
  · intro k hk hkd
    exact follower_after_step hψ G C e (G.pos k) (hi.2.1 k hk hkd)
  · intro k hk
    simpa only [nextLabel, LDSinkTwoGapEpochSuccessor.sinkStepC_label_eq]
      using hi.2.2.1 k hk

/-! Exact consequences of a continuation. No closure residual is used. -/

theorem continuation_data (hψ : ψ > 0) (F : TwoGapFrame n)
    (x : AActive hψ F) (e : Fin n) (y : AState n ψ)
    (hy : attemptStepRaw hψ F x.1 e = .active y) :
    y.conf = postConf hψ F x.1 e ∧
    y.phase = advanceAPhase F x.1.phase (postConf hψ F x.1 e) ∧
    ¬ NoResetSuccess F y.conf ∧ ¬ NoResetAbsorbedAt F x.1 e y.conf := by
  rcases attemptStepRaw_active_data hψ F x.1 e y hy with ⟨hs, ha, hy'⟩
  rw [hy']
  exact ⟨rfl, rfl, hs, ha⟩

theorem continuation_guards (hψ : ψ > 0) (F : TwoGapFrame n)
    (x : AActive hψ F) (e : Fin n) (y : AState n ψ)
    (hy : attemptStepRaw hψ F x.1 e = .active y) :
    ¬ NoResetSuccess F (postConf hψ F x.1 e) ∧
    ¬ NoResetAbsorbedAt F x.1 e (postConf hψ F x.1 e) := by
  have h := attemptStepRaw_active_data hψ F x.1 e y hy
  exact ⟨h.1, h.2.1⟩

theorem continuation_no_endpoint_deleted (hψ : ψ > 0) (F : TwoGapFrame n)
    (x : AActive hψ F) (e : Fin n) (y : AState n ψ)
    (hy : attemptStepRaw hψ F x.1 e = .active y) :
    ¬ EndpointDeleted F.attack y.conf ∧
    ¬ EndpointDeleted F.recovery y.conf := by
  have hs := (continuation_data hψ F x e y hy).2.2.1
  exact ⟨fun h => hs (Or.inl h), fun h => hs (Or.inr h)⟩

private theorem present_not_deleted (G : GapFrame n)
    (C : Fin n → AgentState ψ) (hp : GapEndpointsPresent G C) :
    ¬ EndpointDeleted G C := by
  rcases hp with ⟨hl, hr⟩
  intro hd
  rcases hd with hd | hd
  · have hb : true = false := hl.symm.trans hd
    cases hb
  · have hb : true = false := hr.symm.trans hd
    cases hb

theorem recovery_done_pre_is_clean (hψ : ψ > 0) (F : TwoGapFrame n)
    (x : AActive hψ F) (hd : GapDoneC F.recovery x.1.conf) :
    CleanReady F.recovery x.1.conf := by
  rcases hd with hc | he
  · exact hc
  · exact (present_not_deleted F.recovery x.1.conf x.2.recovery.1 he).elim

/-- Stronger than Attempt2.attackInvariant_of_continuation: successor
non-doneness is unnecessary once Kernel2 and NoResetSuccess are used. -/
theorem attackInvariant_on_continuation (hψ : ψ > 0) (F : TwoGapFrame n)
    (x : AActive hψ F) (e : Fin n) (y : AState n ψ)
    (hy : attemptStepRaw hψ F x.1 e = .active y) :
    GapInvariant hψ F.attack y.conf := by
  have hc := attemptStepRaw_active_conf hψ F x.1 e y hy
  have hdel := (continuation_no_endpoint_deleted hψ F x e y hy).1
  rw [hc] at hdel ⊢
  exact LDSinkTwoGapEpochSuccessor.gapInvariant_step_of_not_endpointDeleted
    hψ F.attack x.1.conf e x.2.attack x.2.tag.not_done hdel

theorem recovery_shape_on_continuation (hψ : ψ > 0) (F : TwoGapFrame n)
    (x : AActive hψ F) (e : Fin n) (y : AState n ψ)
    (hy : attemptStepRaw hψ F x.1 e = .active y) :
    GapEndpointsPresent F.recovery y.conf ∧
    GapInteriorFollowers F.recovery y.conf ∧
    GapLabelAligned hψ F.recovery y.conf := by
  have hc : y.conf = sinkStepC hψ F.recovery x.1.conf e :=
    (continuation_data hψ F x e y hy).1.trans
      (postConf_eq_recovery hψ F x.1 e)
  have hdel := (continuation_no_endpoint_deleted hψ F x e y hy).2
  rw [hc] at hdel ⊢
  exact shape_after_step hψ F.recovery x.1.conf e x.2.recovery hdel

/-- In particular, a done post-state causes no gap in the non-done-pre proof. -/
theorem recoveryInvariant_of_nonDone_pre (hψ : ψ > 0) (F : TwoGapFrame n)
    (x : AActive hψ F) (e : Fin n) (y : AState n ψ)
    (hy : attemptStepRaw hψ F x.1 e = .active y)
    (hn : ¬ GapDoneC F.recovery x.1.conf) :
    GapInvariant hψ F.recovery y.conf := by
  have hc : y.conf = sinkStepC hψ F.recovery x.1.conf e :=
    (continuation_data hψ F x e y hy).1.trans
      (postConf_eq_recovery hψ F x.1 e)
  have hdel := (continuation_no_endpoint_deleted hψ F x e y hy).2
  rw [hc] at hdel ⊢
  exact LDSinkTwoGapEpochSuccessor.gapInvariant_step_of_not_endpointDeleted
    hψ F.recovery x.1.conf e x.2.recovery hn hdel

theorem recoveryInvariant_of_clean_post (hψ : ψ > 0) (F : TwoGapFrame n)
    (x : AActive hψ F) (e : Fin n) (y : AState n ψ)
    (hy : attemptStepRaw hψ F x.1 e = .active y)
    (hc : CleanReady F.recovery y.conf) :
    GapInvariant hψ F.recovery y.conf := by
  have hshape := recovery_shape_on_continuation hψ F x e y hy
  exact LDSinkTwoGapEpochKernel.gapInvariant_of_cleanReady_and_shape
    hψ F.recovery y.conf hshape.1 hshape.2.1 hshape.2.2 hc

/-! Static tag consequences and pure phase bookkeeping. -/

theorem uniqueLiveShot_not_done (F : TwoGapFrame n)
    (C : Fin n → AgentState ψ) (hshot : UniqueLiveShot F C)
    (hdel : ¬ EndpointDeleted F.attack C) :
    ¬ GapDoneC F.attack C := by
  intro hd
  rcases hd with hc | he
  · rcases hshot with ⟨t, ht, htd, hb, _⟩
    have hz := hc.2 t ht htd
    have hbad : (2 : Fin 3) = (0 : Fin 3) := hb.symm.trans hz
    exact (by decide : (2 : Fin 3) ≠ (0 : Fin 3)) hbad
  · exact hdel he

/-- Transit is automatic. The only physical premise is that an already
parked bullet remains live at position 1 on a continuation. -/
theorem advance_parked_iff (F : TwoGapFrame n) (p : APhase)
    (C : Fin n → AgentState ψ)
    (hp : p = .parked → (C (F.attack.pos 1)).bullet = (2 : Fin 3)) :
    advanceAPhase F p C = .parked ↔
      (C (F.attack.pos 1)).bullet = (2 : Fin 3) := by
  cases p with
  | transit =>
      by_cases hb : (C (F.attack.pos 1)).bullet = (2 : Fin 3)
      · simp [advanceAPhase, hb]
      · simp [advanceAPhase, hb]
  | parked =>
      have hb := hp rfl
      simp [advanceAPhase, hb]

/-! The remaining physical obligations. None concludes TagDomain,
GapInvariant, AttemptClosed, or a numerical rank law.

All three are conditional facts about the actual K2 successor. They are
not declared as axioms and no instance is manufactured below. -/

structure AttemptCellResidual (hψ : ψ > 0) (F : TwoGapFrame n) : Prop where
  /-- The scheduled pair cannot lose a live tag except at an already
  classified terminal. The surviving live position does not move away
  from the victim. At t=1 this says exactly that the parked tag stays live. -/
  liveTouched :
    ∀ (x : AActive hψ F) (e : Fin n) (t : Nat),
      0 < t → t ≤ F.attack.d →
      (x.1.conf (F.attack.pos t)).bullet = (2 : Fin 3) →
      Touched F.attack e (F.attack.pos t) →
      ¬ NoResetSuccess F (postConf hψ F x.1 e) →
      ¬ NoResetAbsorbedAt F x.1 e (postConf hψ F x.1 e) →
      ∃ u : Nat, 0 < u ∧ u ≤ t ∧
        (postConf hψ F x.1 e (F.attack.pos u)).bullet = (2 : Fin 3)
  /-- Rule out a new/duplicated bullet involving a written cell. If both
  queried cells are untouched, old uniqueness proves the result below. -/
  noDuplicateTouched :
    ∀ (x : AActive hψ F) (e : Fin n) (u v : Nat),
      0 < u → u ≤ F.attack.d → 0 < v → v ≤ F.attack.d →
      (postConf hψ F x.1 e (F.attack.pos u)).bullet ≠ (0 : Fin 3) →
      (postConf hψ F x.1 e (F.attack.pos v)).bullet ≠ (0 : Fin 3) →
      (Touched F.attack e (F.attack.pos u) ∨
        Touched F.attack e (F.attack.pos v)) →
      ¬ NoResetSuccess F (postConf hψ F x.1 e) →
      ¬ NoResetAbsorbedAt F x.1 e (postConf hψ F x.1 e) → u = v
  /-- Only clean-pre/nonclean-post recovery is left. Every resulting
  nonzero sector bullet must be in the written pair; the remaining
  condition is that its entire signal tail is zero, including the shooter.
  Label/leader preservation and the C5 rank inequalities do not assert this. -/
  cleanRecoverySignal :
    ∀ (x : AActive hψ F) (e : Fin n),
      CleanReady F.recovery x.1.conf →
      ¬ CleanReady F.recovery (postConf hψ F x.1 e) →
      ¬ NoResetSuccess F (postConf hψ F x.1 e) →
      ¬ NoResetAbsorbedAt F x.1 e (postConf hψ F x.1 e) →
      ∀ k j : Nat, 0 < k → k ≤ F.recovery.d →
        (postConf hψ F x.1 e (F.recovery.pos k)).bullet ≠ (0 : Fin 3) →
        k ≤ j → j ≤ F.recovery.d →
        Touched F.recovery e (F.recovery.pos k) →
        (postConf hψ F x.1 e (F.recovery.pos j)).signal_B = (0 : Fin 2)

/-! Complete the untouched cases, then assemble the shot invariant. -/

theorem live_image_of_cells (hψ : ψ > 0) (F : TwoGapFrame n)
    (hR : AttemptCellResidual hψ F) (x : AActive hψ F) (e : Fin n)
    (hs : ¬ NoResetSuccess F (postConf hψ F x.1 e))
    (ha : ¬ NoResetAbsorbedAt F x.1 e (postConf hψ F x.1 e))
    (t : Nat) (ht : 0 < t) (htd : t ≤ F.attack.d)
    (hb : (x.1.conf (F.attack.pos t)).bullet = (2 : Fin 3)) :
    ∃ u : Nat, 0 < u ∧ u ≤ t ∧
      (postConf hψ F x.1 e (F.attack.pos u)).bullet = (2 : Fin 3) := by
  classical
  by_cases htouched : Touched F.attack e (F.attack.pos t)
  · exact hR.liveTouched x e t ht htd hb htouched hs ha
  · refine ⟨t, ht, Nat.le_refl _, ?_⟩
    rw [postConf_cell_eq_attack hψ F x.1 e (F.attack.pos t) htouched]
    exact hb

theorem uniqueLiveShot_of_cells (hψ : ψ > 0) (F : TwoGapFrame n)
    (hR : AttemptCellResidual hψ F) (x : AActive hψ F) (e : Fin n)
    (hs : ¬ NoResetSuccess F (postConf hψ F x.1 e))
    (ha : ¬ NoResetAbsorbedAt F x.1 e (postConf hψ F x.1 e)) :
    UniqueLiveShot F (postConf hψ F x.1 e) := by
  classical
  rcases x.2.tag.shot with ⟨t, ht, htd, hb, huniq⟩
  rcases live_image_of_cells hψ F hR x e hs ha t ht htd hb with
    ⟨u, hu, hut, hbu⟩
  have hud : u ≤ F.attack.d := Nat.le_trans hut htd
  have hnu :
      (postConf hψ F x.1 e (F.attack.pos u)).bullet ≠ (0 : Fin 3) := by
    intro hz
    exact (by decide : (2 : Fin 3) ≠ (0 : Fin 3)) (hbu.symm.trans hz)
  refine ⟨u, hu, hud, hbu, ?_⟩
  intro v hv hvd hnv
  by_cases hvt : Touched F.attack e (F.attack.pos v)
  · exact hR.noDuplicateTouched x e v u hv hvd hu hud hnv hnu
      (Or.inl hvt) hs ha
  · by_cases hut' : Touched F.attack e (F.attack.pos u)
    · exact hR.noDuplicateTouched x e v u hv hvd hu hud hnv hnu
        (Or.inr hut') hs ha
    · have hvcell :=
        postConf_cell_eq_attack hψ F x.1 e (F.attack.pos v) hvt
      have hucell :=
        postConf_cell_eq_attack hψ F x.1 e (F.attack.pos u) hut'
      have hnv0 : (x.1.conf (F.attack.pos v)).bullet ≠ (0 : Fin 3) := by
        simpa only [hvcell] using hnv
      have hnu0 : (x.1.conf (F.attack.pos u)).bullet ≠ (0 : Fin 3) := by
        simpa only [hucell] using hnu
      exact (huniq v hv hvd hnv0).trans (huniq u hu hud hnu0).symm

theorem parked_live_of_cells (hψ : ψ > 0) (F : TwoGapFrame n)
    (hR : AttemptCellResidual hψ F) (x : AActive hψ F) (e : Fin n)
    (hs : ¬ NoResetSuccess F (postConf hψ F x.1 e))
    (ha : ¬ NoResetAbsorbedAt F x.1 e (postConf hψ F x.1 e))
    (hp : x.1.phase = .parked) :
    (postConf hψ F x.1 e (F.attack.pos 1)).bullet = (2 : Fin 3) := by
  have hb := x.2.tag.parked_iff.mp hp
  have hd : 1 ≤ F.attack.d := by
    have h := F.attack.hd
    omega
  rcases live_image_of_cells hψ F hR x e hs ha 1 (by decide) hd hb with
    ⟨u, hu, hu1, hbu⟩
  have heq : u = 1 := by omega
  simpa only [heq] using hbu

theorem tagContinuation_of_cells (hψ : ψ > 0) (F : TwoGapFrame n)
    (hR : AttemptCellResidual hψ F)
    (x : AActive hψ F) (e : Fin n) (y : AState n ψ)
    (hy : attemptStepRaw hψ F x.1 e = .active y) : TagDomain F y := by
  have hd := continuation_data hψ F x e y hy
  have hg := continuation_guards hψ F x e y hy
  have hshot : UniqueLiveShot F y.conf := by
    simpa only [hd.1] using uniqueLiveShot_of_cells hψ F hR x e hg.1 hg.2
  have hp : y.phase = .parked ↔
      (y.conf (F.attack.pos 1)).bullet = (2 : Fin 3) := by
    rw [hd.1, hd.2.1]
    exact advance_parked_iff F x.1.phase (postConf hψ F x.1 e)
      (parked_live_of_cells hψ F hR x e hg.1 hg.2)
  exact ⟨hshot, hp, uniqueLiveShot_not_done F y.conf hshot
    (continuation_no_endpoint_deleted hψ F x e y hy).1⟩

/-! The only recovery case not supplied by Kernel2: clean before firing. -/

theorem recovery_signal_after_clean (hψ : ψ > 0) (F : TwoGapFrame n)
    (hR : AttemptCellResidual hψ F) (x : AActive hψ F) (e : Fin n)
    (hc0 : CleanReady F.recovery x.1.conf)
    (hc1 : ¬ CleanReady F.recovery (postConf hψ F x.1 e))
    (hs : ¬ NoResetSuccess F (postConf hψ F x.1 e))
    (ha : ¬ NoResetAbsorbedAt F x.1 e (postConf hψ F x.1 e)) :
    GapSignalBelowBullets F.recovery (postConf hψ F x.1 e) := by
  classical
  intro k j hk hkd hb hkj hjd
  by_cases ht : Touched F.recovery e (F.recovery.pos k)
  · exact hR.cleanRecoverySignal x e hc0 hc1 hs ha k j hk hkd hb hkj hjd ht
  · have hcell :=
      postConf_cell_eq_recovery hψ F x.1 e (F.recovery.pos k) ht
    have hz :
        (postConf hψ F x.1 e (F.recovery.pos k)).bullet = (0 : Fin 3) := by
      rw [hcell]
      exact hc0.2 k hk hkd
    exact (hb hz).elim

/-- No old/post GapDoneC disjunction is needed in the conclusion. -/
theorem recoveryInvariant_on_continuation (hψ : ψ > 0) (F : TwoGapFrame n)
    (hR : AttemptCellResidual hψ F)
    (x : AActive hψ F) (e : Fin n) (y : AState n ψ)
    (hy : attemptStepRaw hψ F x.1 e = .active y) :
    GapInvariant hψ F.recovery y.conf := by
  classical
  by_cases hdone : GapDoneC F.recovery x.1.conf
  · have hc0 := recovery_done_pre_is_clean hψ F x hdone
    by_cases hc1 : CleanReady F.recovery y.conf
    · exact recoveryInvariant_of_clean_post hψ F x e y hy hc1
    · have hd := continuation_data hψ F x e y hy
      have hg := continuation_guards hψ F x e y hy
      have hc1' : ¬ CleanReady F.recovery (postConf hψ F x.1 e) := by
        intro hc
        apply hc1
        simpa only [hd.1] using hc
      have hsignal := recovery_signal_after_clean hψ F hR x e hc0 hc1' hg.1 hg.2
      have hshape := recovery_shape_on_continuation hψ F x e y hy
      refine ⟨hshape.1, hshape.2.1, hshape.2.2, ?_⟩
      simpa only [hd.1] using hsignal
  · exact recoveryInvariant_of_nonDone_pre hψ F x e y hy hdone

/-! Reconstruct the original residual and retain the existing Bellman layer. -/

theorem attemptResidual_of_cells (hψ : ψ > 0) (F : TwoGapFrame n)
    (hR : AttemptCellResidual hψ F) : AttemptResidual hψ F := by
  constructor
  · intro x e y hy
    exact tagContinuation_of_cells hψ F hR x e y hy
  · intro x e y hy _
    exact recoveryInvariant_on_continuation hψ F hR x e y hy

theorem attemptLaws_of_cells (hψ : ψ > 0) (F : TwoGapFrame n)
    (hR : AttemptCellResidual hψ F) : AttemptLaws hψ F := by
  exact attemptLaws_of_residual hψ F (attemptResidual_of_cells hψ F hR)

theorem attempt_cost_le_of_cells (hψ : ψ > 0) (F : TwoGapFrame n)
    (hR : AttemptCellResidual hψ F) (x : AActive hψ F) (T : Nat) :
    truncatedActiveCostNumerator
        (attemptStep hψ F (attemptLaws_of_cells hψ F hR).continuation)
        (.active x) T ≤
      n ^ T * (n * 16 * (F.recovery.d + F.attack.d)) := by
  exact attempt_cost_le_of_laws hψ F (attemptLaws_of_cells hψ F hR) x T

end

end LDSinkTwoGapAttemptResidual

#print axioms LDSinkTwoGapAttemptResidual.cell_eq_of_not_touched
#print axioms LDSinkTwoGapAttemptResidual.follower_after_step
#print axioms LDSinkTwoGapAttemptResidual.shape_after_step
#print axioms LDSinkTwoGapAttemptResidual.continuation_no_endpoint_deleted
#print axioms LDSinkTwoGapAttemptResidual.attackInvariant_on_continuation
#print axioms LDSinkTwoGapAttemptResidual.recoveryInvariant_of_nonDone_pre
#print axioms LDSinkTwoGapAttemptResidual.recoveryInvariant_of_clean_post
#print axioms LDSinkTwoGapAttemptResidual.uniqueLiveShot_not_done
#print axioms LDSinkTwoGapAttemptResidual.advance_parked_iff
#print axioms LDSinkTwoGapAttemptResidual.live_image_of_cells
#print axioms LDSinkTwoGapAttemptResidual.uniqueLiveShot_of_cells
#print axioms LDSinkTwoGapAttemptResidual.parked_live_of_cells
#print axioms LDSinkTwoGapAttemptResidual.tagContinuation_of_cells
#print axioms LDSinkTwoGapAttemptResidual.recovery_signal_after_clean
#print axioms LDSinkTwoGapAttemptResidual.recoveryInvariant_on_continuation
#print axioms LDSinkTwoGapAttemptResidual.attemptResidual_of_cells
#print axioms LDSinkTwoGapAttemptResidual.attemptLaws_of_cells
#print axioms LDSinkTwoGapAttemptResidual.attempt_cost_le_of_cells
