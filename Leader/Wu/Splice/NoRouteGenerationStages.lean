import Leader.Wu.Splice.CheckCleanupReleasedSafe
import Leader.Wu.Comparison.HistoryTrustImmediateLift


set_option autoImplicit false
set_option Elab.async false


namespace B9NoRouteStagesA


open PPLL PPLLRepair PPLLAuthorizedComparisonRepair
  PPLLWallSweepRepair PPLLWallSweepFinite PPLLComparisonHistory
open BirthGenerationControlRepair BirthShortWaitTerminalEntryRepair
open Q11525CurrentHistoryFrames


variable {ψ κ : Nat}


def NoEqualEndpoint (u : AgentState ψ) : Prop :=
  u.state ≠ .equal ∧ u.path2 = none


def NoEqualOnPair (q : AgentState ψ × AgentState ψ) : Prop :=
  NoEqualEndpoint q.1 ∧ NoEqualEndpoint q.2


private theorem produce_ne_equal : MainState.produce ≠ .equal := by intro h; cases h
private theorem done_ne_equal : MainState.done ≠ .equal := by intro h; cases h
private theorem depart_ne_equal : MainState.depart ≠ .equal := by intro h; cases h


private theorem noEqualEndpoint_of_view
    (u v : AgentState ψ)
    (h : ComparisonTrackedView.ofState u = ComparisonTrackedView.ofState v)
    (hv : NoEqualEndpoint v) : NoEqualEndpoint u := by
  constructor
  · intro heq
    exact hv.1 ((congrArg ComparisonTrackedView.state h).symm.trans heq)
  · exact (congrArg ComparisonTrackedView.path2 h).trans hv.2


theorem neutral_noEqualOnPair (l r : AgentState ψ)
    (hl : ComparisonNeutral l) (hr : ComparisonNeutral r) :
    NoEqualOnPair (l, r) := by
  refine ⟨⟨?_, hl.2.2.1⟩, ⟨?_, hr.2.2.1⟩⟩
  · intro heq
    cases hl.1.symm.trans heq
  · intro heq
    cases hr.1.symm.trans heq


/-- P-prime preserves the pairwise no-equal/control-empty invariant. -/
theorem pprime_noEqualOnPair
    (hψ : 0 < ψ) (l r : AuthorizedAgentState ψ)
    (h : NoEqualOnPair (l.core, r.core)) :
    let q := authorizedPPsiLeaderResetProbeWall hψ l r
    NoEqualOnPair (q.1.core, q.2.core) := by
  change NoEqualOnPair (pPsiLeaderResetProbeWall hψ l.core r.core)
  have hf := pPsiLeaderResetProbeWall_comparisonTracked_frame hψ l.core r.core
  exact ⟨noEqualEndpoint_of_view _ _ hf.1 h.1,
    noEqualEndpoint_of_view _ _ hf.2 h.2⟩


private theorem two_pos : 0 < 2 := Nat.zero_lt_succ 1


/-- The corrected width-two WAIT preserves the same invariant. -/
theorem wait2_noEqualOnPair
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (κ : Nat) (l r : AgentState ψ)
    (h : NoEqualOnPair (l, r)) :
    let q := waitWidthEntry hψ two_pos h2 κ l r
    NoEqualOnPair q := by
  have hf := waitWidthEntry_comparisonTracked_frame hψ two_pos h2 κ l r
  exact ⟨noEqualEndpoint_of_view _ _ hf.1 h.1,
    noEqualEndpoint_of_view _ _ hf.2 h.2⟩


private theorem genStart_noEqualOnPair
    (hψ : 0 < ψ) (l r : AgentState ψ) (h : NoEqualOnPair (l, r)) :
    NoEqualOnPair (genSigSaturatedStart hψ l r) := by
  rcases h with ⟨hl, hr⟩
  unfold genSigSaturatedStart
  dsimp only
  split
  · split
    · exact ⟨⟨produce_ne_equal, hl.2⟩, ⟨produce_ne_equal, hr.2⟩⟩
    · exact ⟨⟨produce_ne_equal, hl.2⟩, hr⟩
  · split
    · exact ⟨hl, ⟨produce_ne_equal, hr.2⟩⟩
    · exact ⟨hl, hr⟩


private theorem genEmit_noEqualOnPair
    (hψ : 0 < ψ) (l r : AgentState ψ) (h : NoEqualOnPair (l, r)) :
    NoEqualOnPair (genCleanEmit hψ l r) := by
  rcases h with ⟨hl, hr⟩
  unfold genCleanEmit
  dsimp only
  split
  · exact ⟨hl, ⟨done_ne_equal, rfl⟩⟩
  · exact ⟨hl, hr⟩


private theorem genPropagate_noEqualOnPair
    (hψ : 0 < ψ) (l r : AgentState ψ) (h : NoEqualOnPair (l, r)) :
    NoEqualOnPair (genCleanPropagate hψ l r) := by
  rcases h with ⟨hl, hr⟩
  unfold genCleanPropagate
  split
  · exact ⟨⟨done_ne_equal, rfl⟩, ⟨depart_ne_equal, hr.2⟩⟩
  · exact ⟨hl, hr⟩


private theorem genFinish_noEqualOnPair
    (hψ : 0 < ψ) (l r : AgentState ψ) (h : NoEqualOnPair (l, r)) :
    NoEqualOnPair (genSigSaturatedFinish hψ l r) := by
  rcases h with ⟨hl, hr⟩
  unfold genSigSaturatedFinish
  dsimp only
  split
  · exact ⟨⟨depart_ne_equal, hl.2⟩, hr⟩
  · exact ⟨hl, hr⟩


/-- GENSIG never introduces `.equal`; its two writers also clear `path2`. -/
theorem gensig_noEqualOnPair
    (hψ : 0 < ψ) (l r : AgentState ψ) (h : NoEqualOnPair (l, r)) :
    let q := genCleanAfterWait hψ l r
    NoEqualOnPair q := by
  let s := genSigSaturatedStart hψ l r
  have hs := genStart_noEqualOnPair hψ l r h
  let e := genCleanEmit hψ s.1 s.2
  have he := genEmit_noEqualOnPair hψ s.1 s.2 hs
  let p := genCleanPropagate hψ e.1 e.2
  have hp := genPropagate_noEqualOnPair hψ e.1 e.2 he
  change NoEqualOnPair (genSigSaturatedFinish hψ p.1 p.2)
  exact genFinish_noEqualOnPair hψ p.1 p.2 hp


/-- CLEAN uses its comparison frame fieldwise: state and `path2` are fixed. -/
theorem clean_noEqualOnPair
    (hψ : 0 < ψ) (l r : AgentState ψ) (h : NoEqualOnPair (l, r)) :
    let q := cleanSig hψ l r
    NoEqualOnPair q := by
  rcases h with ⟨hl, hr⟩
  have hf := cleanSig_comparison_frame hψ l r
  rcases hf with ⟨_, _, hsl, hsr, h2l, h2r⟩
  refine ⟨⟨?_, h2l.trans hl.2⟩, ⟨?_, h2r.trans hr.2⟩⟩
  · intro heq
    exact hl.1 (hsl.symm.trans heq)
  · intro heq
    exact hr.1 (hsr.symm.trans heq)


end B9NoRouteStagesA


#print axioms B9NoRouteStagesA.neutral_noEqualOnPair
#print axioms B9NoRouteStagesA.pprime_noEqualOnPair
#print axioms B9NoRouteStagesA.wait2_noEqualOnPair
#print axioms B9NoRouteStagesA.gensig_noEqualOnPair
#print axioms B9NoRouteStagesA.clean_noEqualOnPair
