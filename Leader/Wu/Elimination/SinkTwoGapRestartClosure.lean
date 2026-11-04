import Leader.Wu.Elimination.SinkTwoGapReachInvariant

open FiniteUniformStoppingTree PPLLRepair
open LDSinkGapCleanup LDSinkKernelC LDSinkProtectedAbsorption
open LDSinkGapDoneInvariant LDSinkGapBlockedPreStep LDSinkGapServiceRank
open LDSinkGapCleanupBound LDTwoGapFrame
open LDSinkTwoGapEpochKernel LDSinkTwoGapEpochSuccessor
open LDSinkTwoGapNoResetKernel LDSinkTwoGapAttemptCells
open LDSinkTwoGapEntrance LDSinkTwoGapDeletionWired
open LDSinkTwoGapReachInvariant

namespace LDSinkTwoGapRestartClosure

set_option autoImplicit false

noncomputable section

variable {n ψ : Nat}

/-! ## Wrapper-independent clean-boundary seam

The older residual is restricted by `EntranceReach`.  That is too small for
physical restart closure because physicalBlockStep continues through states
where entranceStep may already have returned success.  The signal fact itself
is about the common physical post-configuration, so quantify it there. -/

structure RestartCleanBoundarySignalResidual
    (hψ : ψ > 0) (F : TwoGapFrame n) : Prop where
  signal : ∀ (x : AState n ψ) (e : Fin n) (G : GapFrame n),
    (G = F.recovery ∨ G = F.attack) →
    GapPair hψ F x →
    (¬ AInvariant hψ F x ∨ attemptStepRaw hψ F x e = .failure) →
    ¬ NoResetSuccess F (attemptStepConf hψ F x e) →
    CleanReady G x.conf →
    ¬ CleanReady G (attemptStepConf hψ F x e) →
    GapSignalBelowBullets G (attemptStepConf hψ F x e)

/-! ## The two wrappers share the same post-state -/

theorem physical_active_eq_entrance_active
    (hψ : ψ > 0) (F : TwoGapFrame n)
    (x : AState n ψ) (e : Fin n) (y : AState n ψ)
    (hy : physicalBlockStep hψ F x e = .active y) :
    entranceStep hψ F x e = .active y ∨
      (entranceStep hψ F x e = .success ∧
        y = postState hψ F x e) := by
  classical
  have hs : ¬ NoResetSuccess F (attemptStepConf hψ F x e) := by
    intro hs
    have hh := hy
    rw [physicalBlockStep_normal_form, if_pos hs] at hh
    cases hh
  have hpost : y = postState hψ F x e := by
    have hh := hy
    rw [physicalBlockStep_normal_form, if_neg hs] at hh
    exact (StopNode.active.inj hh).symm
  by_cases hE : EntranceSuccess F (attemptStepConf hψ F x e)
  · exact Or.inr ⟨by rw [entrance_normal_form, if_pos hE], hpost⟩
  · apply Or.inl
    rw [entrance_normal_form, if_neg hE]
    exact congrArg StopNode.active hpost.symm

/-- A physical active successor comes from either the ordinary raw active
branch or a raw absorption that retryStep reactivates. -/
theorem physical_active_source_cases
    (hψ : ψ > 0) (F : TwoGapFrame n)
    (x : AState n ψ) (e : Fin n) (y : AState n ψ)
    (hy : physicalBlockStep hψ F x e = .active y) :
    attemptStepRaw hψ F x e = .active y ∨
      (attemptStepRaw hψ F x e = .failure ∧
        y = postState hψ F x e) := by
  classical
  have hs : ¬ NoResetSuccess F (attemptStepConf hψ F x e) := by
    intro hs
    have hh := hy
    rw [physicalBlockStep_normal_form, if_pos hs] at hh
    cases hh
  have hpost : y = postState hψ F x e := by
    have hh := hy
    rw [physicalBlockStep_normal_form, if_neg hs] at hh
    exact (StopNode.active.inj hh).symm
  by_cases ha : NoResetAbsorbedAt F x e (attemptStepConf hψ F x e)
  · exact Or.inr
      ⟨(attemptStepRaw_failure_iff hψ F x e).mpr ⟨hs, ha⟩, hpost⟩
  · have hr : attemptStepRaw hψ F x e =
        .active (postState hψ F x e) := by
      simp [attemptStepRaw, hs, ha, postState]
    exact Or.inl (hr.trans (congrArg StopNode.active hpost.symm))

/-- Entrance-active implies physical-active.  Entrance success is the only
place where the physical wrapper can continue while entrance stops. -/
theorem entrance_active_implies_physical_active
    (hψ : ψ > 0) (F : TwoGapFrame n)
    (x : AState n ψ) (e : Fin n) (y : AState n ψ)
    (hy : entranceStep hψ F x e = .active y) :
    physicalBlockStep hψ F x e = .active y := by
  classical
  have hd := entrance_active_data_wired hψ F x y e hy
  have hs : ¬ NoResetSuccess F (attemptStepConf hψ F x e) :=
    fun hs => hd.1 (Or.inr hs)
  rw [physicalBlockStep_normal_form, if_neg hs]
  exact congrArg StopNode.active hd.2.symm

/-! ## GapInvariant preservation without the old EntranceReach premise -/

theorem restart_invariant_not_deleted
    (hψ : ψ > 0) (G : GapFrame n) (C : Fin n → AgentState ψ)
    (hi : GapInvariant hψ G C) : ¬ EndpointDeleted G C := by
  intro hd
  rcases hd with h0 | hd
  · have hh : true = false := hi.1.1.symm.trans h0
    cases hh
  · have hh : true = false := hi.1.2.symm.trans hd
    cases hh

theorem restart_follower_after_step
    (hψ : ψ > 0) (G : GapFrame n) (C : Fin n → AgentState ψ)
    (e v : Fin n) (hv : (C v).leader = false) :
    (sinkStepC hψ G C e v).leader = false := by
  by_cases hL : v = e
  · subst v
    have hh := (LDSinkTwoGapEpochSuccessor.kernelC_no_leader_creation
      hψ (C e) (C (G.ring.rightNeighbor e))).1 hv
    simpa [sinkStepC, updatePair] using hh
  · by_cases hR : v = G.ring.rightNeighbor e
    · subst v
      have hh := (LDSinkTwoGapEpochSuccessor.kernelC_no_leader_creation
        hψ (C e) (C (G.ring.rightNeighbor e))).2 hv
      simpa [sinkStepC, updatePair, hL] using hh
    · rw [sinkStepC_other hψ G C e v hL hR]
      exact hv

theorem restart_shape_after_step
    (hψ : ψ > 0) (G : GapFrame n) (C : Fin n → AgentState ψ)
    (e : Fin n) (hi : GapInvariant hψ G C)
    (hdel : ¬ EndpointDeleted G (sinkStepC hψ G C e)) :
    GapEndpointsPresent G (sinkStepC hψ G C e) ∧
    GapInteriorFollowers G (sinkStepC hψ G C e) ∧
    GapLabelAligned hψ G (sinkStepC hψ G C e) := by
  refine ⟨?_, ?_, ?_⟩
  · change
      (sinkStepC hψ G C e (G.pos 0)).leader = true ∧
      (sinkStepC hψ G C e (G.pos G.d)).leader = true
    constructor
    · cases he : (sinkStepC hψ G C e (G.pos 0)).leader with
      | false => exact (hdel (Or.inl he)).elim
      | true => rfl
    · cases he : (sinkStepC hψ G C e (G.pos G.d)).leader with
      | false => exact (hdel (Or.inr he)).elim
      | true => rfl
  · intro k hk hkd
    exact restart_follower_after_step hψ G C e (G.pos k)
      (hi.2.1 k hk hkd)
  · intro k hk
    simpa only [nextLabel, LDSinkTwoGapEpochSuccessor.sinkStepC_label_eq]
      using hi.2.2.1 k hk

theorem restart_gap_step_of_clean_boundary_signal
    (hψ : ψ > 0) (G : GapFrame n) (C : Fin n → AgentState ψ)
    (e : Fin n) (hi : GapInvariant hψ G C)
    (hdel : ¬ EndpointDeleted G (sinkStepC hψ G C e))
    (hboundary : CleanReady G C →
      ¬ CleanReady G (sinkStepC hψ G C e) →
      GapSignalBelowBullets G (sinkStepC hψ G C e)) :
    GapInvariant hψ G (sinkStepC hψ G C e) := by
  classical
  by_cases hd : GapDoneC G C
  · have hc : CleanReady G C := by
      rcases hd with hc | hdelPre
      · exact hc
      · exact (restart_invariant_not_deleted hψ G C hi hdelPre).elim
    have hshape := restart_shape_after_step hψ G C e hi hdel
    have hsignal : GapSignalBelowBullets G (sinkStepC hψ G C e) := by
      by_cases hpost : CleanReady G (sinkStepC hψ G C e)
      · exact gapSignalBelowBullets_of_cleanReady G _ hpost
      · exact hboundary hc hpost
    exact ⟨hshape.1, hshape.2.1, hshape.2.2, hsignal⟩
  · exact LDSinkTwoGapEpochSuccessor.gapInvariant_step_of_not_endpointDeleted
      hψ G C e hi hd hdel

/-! ## Physical restart closure -/

theorem gapPair_physical_step
    (hψ : ψ > 0) (F : TwoGapFrame n)
    (hBoundary : RestartCleanBoundarySignalResidual hψ F)
    (x : AState n ψ) (e : Fin n) (y : AState n ψ)
    (hi : GapPair hψ F x)
    (hy : physicalBlockStep hψ F x e = .active y) :
    GapPair hψ F y := by
  classical
  have hc : y.conf = attemptStepConf hψ F x e :=
    physicalBlockStep_active hψ F x e y hy
  have hatt : y.conf = sinkStepC hψ F.attack x.conf e :=
    hc.trans (attemptStepConf_eq_sinkStepC hψ F x e)
  have hrec : y.conf = sinkStepC hψ F.recovery x.conf e :=
    hatt.trans (twoGap_sinkStepC_eq hψ F x.conf e).symm
  have hs0 : ¬ NoResetSuccess F (attemptStepConf hψ F x e) := by
    intro hs
    have hh := hy
    rw [physicalBlockStep_normal_form, if_pos hs] at hh
    cases hh
  have hn : ¬ NoResetSuccess F y.conf := by
    intro hs
    apply hs0
    simpa only [hc] using hs
  have remaining :
      (¬ AInvariant hψ F x ∨ attemptStepRaw hψ F x e = .failure) →
      GapPair hψ F y := by
    intro hcase
    have one : ∀ G : GapFrame n,
        (G = F.recovery ∨ G = F.attack) →
        GapInvariant hψ G x.conf →
        y.conf = sinkStepC hψ G x.conf e →
        ¬ EndpointDeleted G y.conf → GapInvariant hψ G y.conf := by
      intro G hG hiG heq hdel
      rw [heq]
      apply restart_gap_step_of_clean_boundary_signal hψ G x.conf e hiG
      · intro hd
        exact hdel (heq.symm ▸ hd)
      · intro hpre hpost
        have hca : attemptStepConf hψ F x e =
            sinkStepC hψ G x.conf e := hc.symm.trans heq
        have hpost' : ¬ CleanReady G (attemptStepConf hψ F x e) := by
          intro hh
          exact hpost (hca ▸ hh)
        have hsig := hBoundary.signal x e G hG hi hcase hs0 hpre hpost'
        exact hca ▸ hsig
    exact ⟨
      one F.recovery (Or.inl rfl) hi.recovery hrec
        (fun h => hn (Or.inr h)),
      one F.attack (Or.inr rfl) hi.attack hatt
        (fun h => hn (Or.inl h))⟩
  by_cases hiA : AInvariant hψ F x
  · rcases physical_active_source_cases hψ F x e y hy with ha | hf
    · have hiY := (attemptLaws_K2 hψ F).continuation ⟨x, hiA⟩ e y ha
      exact ⟨hiY.recovery, hiY.attack⟩
    · exact remaining (Or.inr hf.1)
  · exact remaining (Or.inl hiA)

/-- The same broadened boundary field also closes a fresh conceptual entrance
run started from an arbitrary GapPair state. -/
theorem gapPair_entrance_step_from_pair
    (hψ : ψ > 0) (F : TwoGapFrame n)
    (hBoundary : RestartCleanBoundarySignalResidual hψ F)
    (x : AState n ψ) (e : Fin n) (y : AState n ψ)
    (hi : GapPair hψ F x)
    (hy : entranceStep hψ F x e = .active y) :
    GapPair hψ F y := by
  exact gapPair_physical_step hψ F hBoundary x e y hi
    (entrance_active_implies_physical_active hψ F x e y hy)

theorem physicalReach_gapPair
    (hψ : ψ > 0) (F : TwoGapFrame n)
    (hBoundary : RestartCleanBoundarySignalResidual hψ F)
    (x : AState n ψ)
    (hx : ActiveReach (physicalBlockStep hψ F) (GapPair hψ F) x) :
    GapPair hψ F x := by
  induction hx with
  | base hi => exact hi
  | next e hprev he ih =>
      exact gapPair_physical_step hψ F hBoundary _ e _ ih he

/-- The audit's restart-rank coverage: the same fixed frame bound holds at
every active physical state reachable from a GapPair seed. -/
theorem uniform_rank_bound
    (hψ : ψ > 0) (F : TwoGapFrame n)
    (hBoundary : RestartCleanBoundarySignalResidual hψ F)
    (x : AState n ψ)
    (hx : ActiveReach (physicalBlockStep hψ F) (GapPair hψ F) x) :
    R F x ≤ 16 * (F.recovery.d + F.attack.d) := by
  have hi := physicalReach_gapPair hψ F hBoundary x hx
  exact R_le hψ F x hi.recovery hi.attack

/-! ## The one remaining quantitative seam

The invariant branch already has pointwise nonincrease and a strict edge.
For states where the old tag certificate is absent, ask only for the aggregate
Bellman inequality actually consumed by the finite-tree entrance argument.
This is weaker than requiring every edge to be nonincreasing. -/

structure RestartEntranceBellmanResidual
    (hψ : ψ > 0) (F : TwoGapFrame n) : Prop where
  bellman : ∀ (x : AState n ψ),
    GapPair hψ F x → ¬ AInvariant hψ F x →
    n + (List.ofFn (fun e : Fin n =>
      entrancePotential F (entranceStep hψ F x e))).sum ≤
        n * entrancePotential F (.active x)

#print axioms physical_active_eq_entrance_active
#print axioms physical_active_source_cases
#print axioms entrance_active_implies_physical_active
#print axioms restart_invariant_not_deleted
#print axioms restart_follower_after_step
#print axioms restart_shape_after_step
#print axioms restart_gap_step_of_clean_boundary_signal
#print axioms gapPair_physical_step
#print axioms gapPair_entrance_step_from_pair
#print axioms physicalReach_gapPair
#print axioms uniform_rank_bound

end

end LDSinkTwoGapRestartClosure
