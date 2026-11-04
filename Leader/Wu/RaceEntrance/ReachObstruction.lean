import Leader.Wu.RaceEntrance.SupportResolution

set_option autoImplicit false

open FiniteUniformStoppingTree PPLLRepair
open LDSinkGapCleanup LDSinkProtectedAbsorption LDSinkGapDoneInvariant
open LDTwoGapFrame LDSinkTwoGapNoResetKernel LDSinkTwoGapEntrance
open LDSinkTwoGapDeletionWired LDSinkTwoGapReachInvariant
open LDSinkTwoGapRaceSupportResolution

namespace LDSinkTwoGapRaceEntranceReachObstruction

/-!
The inherited entrance potential fails even on states actually reached from
the old `AInvariant` seed, before any entrance success.  A protected parked
shot is absorbed, then one signal edge cleans the attack gap.  The sticky
`parked` ghost remains, so the old rank is one although every next raw edge
still leaves the entrance active.  This isolates an actual renewal cost,
rather than relying on arbitrary phase initialization in `GapPair`.
-/

/-- A shielded shared victim faces one parked live attack bullet.  The
recovery signal has not arrived, so this is not already `RaceReady`. -/
def blockedConf (i : Fin 5) : AgentState 1 :=
  if i.val = 2 then { coldConf i with shield := true }
  else if i.val = 3 then { coldConf i with bullet := 2 }
  else coldConf i

def blockedState : AState 5 1 := ⟨blockedConf, .parked⟩

private theorem blocked_gapPair : GapPair coldHPsi coldFrame blockedState := by
  have hc := cold_gapPair
  constructor
  · refine ⟨?_, ?_, ?_, ?_⟩
    · constructor <;> decide
    · intro k hk hkd
      have hk1 : k = 1 := by change k < 2 at hkd; omega
      subst k
      decide
    · intro k hk
      have hk01 : k = 0 ∨ k = 1 := by change k < 2 at hk; omega
      rcases hk01 with hk0 | hk1 <;> subst k <;> decide
    · intro k j hk hkd hb hkj hjd
      have hk12 : k = 1 ∨ k = 2 := by change k ≤ 2 at hkd; omega
      rcases hk12 with hk1 | hk2 <;> subst k <;> exact (hb (by decide)).elim
  · refine ⟨?_, ?_, ?_, ?_⟩
    · constructor <;> decide
    · intro k hk hkd
      have hk1 : k = 1 := by change k < 2 at hkd; omega
      subst k
      decide
    · intro k hk
      have hk01 : k = 0 ∨ k = 1 := by change k < 2 at hk; omega
      rcases hk01 with hk0 | hk1 <;> subst k <;> decide
    · intro k j hk hkd hb hkj hjd
      have hj12 : j = 1 ∨ j = 2 := by change j ≤ 2 at hjd; omega
      rcases hj12 with hj1 | hj2 <;> subst j <;> decide

/-- The old fresh-shot predicate itself admits this protected parked seed:
the shot is unique, the parked equivalence holds, and attack cleanup is not
already done. -/
theorem blocked_invariant : AInvariant coldHPsi coldFrame blockedState := by
  refine ⟨blocked_gapPair.recovery, blocked_gapPair.attack, ?_⟩
  constructor
  · refine ⟨1, by decide, by decide, by decide, ?_⟩
    intro u hu hud hb
    have hu12 : u = 1 ∨ u = 2 := by change u ≤ 2 at hud; omega
    rcases hu12 with h1 | h2
    · exact h1
    · subst u
      exact (hb (by decide)).elim
  · constructor <;> intro _ <;> decide
  · intro hd
    rcases hd with hclean | hdeleted
    · have hz := hclean.2 1 (by decide) (by decide)
      exact (by decide : (2 : Fin 3) ≠ 0) hz
    · have hn : ¬ EndpointDeleted coldFrame.attack blockedConf := by
        unfold EndpointDeleted
        decide
      exact hn hdeleted

/-- The first physical edge absorbs the live follower shot. -/
def absorbedConf : Fin 5 → AgentState 1 :=
  sinkStepC coldHPsi coldFrame.attack blockedConf 2

def absorbedState : AState 5 1 := ⟨absorbedConf, .parked⟩

/-- The second physical edge transfers the absence signal into the attack
shooter.  The physical configuration now needs a fresh shot. -/
def renewedConf : Fin 5 → AgentState 1 :=
  sinkStepC coldHPsi coldFrame.attack absorbedConf 3

def renewedState : AState 5 1 := ⟨renewedConf, .parked⟩

private theorem post_absorption :
    postState coldHPsi coldFrame blockedState 2 = absorbedState := rfl

private theorem post_renewal :
    postState coldHPsi coldFrame absorbedState 3 = renewedState := rfl

private theorem cold_no_success : ¬ NoResetSuccess coldFrame coldConf := by
  unfold NoResetSuccess EndpointDeleted
  decide

private theorem not_entrance_of_fields (C : Fin 5 → AgentState 1)
    (hb : (C 3).bullet ≠ (2 : Fin 3))
    (hl : ∀ v : Fin 5, (C v).leader = (coldConf v).leader) :
    ¬ EntranceSuccess coldFrame C := by
  intro h
  rcases h with hr | hd
  · exact hb hr.1
  · apply cold_no_success
    simpa only [NoResetSuccess, EndpointDeleted, hl] using hd

private theorem absorption_active :
    entranceStep coldHPsi coldFrame blockedState 2 = .active absorbedState := by
  classical
  have hn : ¬ EntranceSuccess coldFrame absorbedConf :=
    not_entrance_of_fields absorbedConf (by decide) (by decide)
  rw [entrance_normal_form]
  change (if EntranceSuccess coldFrame absorbedConf then StopNode.success
    else StopNode.active (postState coldHPsi coldFrame blockedState 2)) = _
  rw [if_neg hn, post_absorption]

private theorem renewal_active :
    entranceStep coldHPsi coldFrame absorbedState 3 = .active renewedState := by
  classical
  have hn : ¬ EntranceSuccess coldFrame renewedConf :=
    not_entrance_of_fields renewedConf (by decide) (by decide)
  rw [entrance_normal_form]
  change (if EntranceSuccess coldFrame renewedConf then StopNode.success
    else StopNode.active (postState coldHPsi coldFrame absorbedState 3)) = _
  rw [if_neg hn, post_renewal]

theorem absorbed_entranceReach : EntranceReach coldHPsi coldFrame absorbedState :=
  .next 2 (.base blocked_invariant) absorption_active

/-- Two actual active entrance edges, from a proved old valid seed, reach
the state where the inherited phase budget has been exhausted. -/
theorem renewed_entranceReach : EntranceReach coldHPsi coldFrame renewedState :=
  .next 3 absorbed_entranceReach renewal_active

theorem renewed_cleanReady : CleanReady coldFrame.attack renewedConf := by
  refine ⟨by decide, ?_⟩
  intro k hk hkd
  have hk12 : k = 1 ∨ k = 2 := by change k ≤ 2 at hkd; omega
  rcases hk12 with hk1 | hk2 <;> subst k <;> decide

theorem renewed_not_entrance : ¬ EntranceSuccess coldFrame renewedConf :=
  not_entrance_of_fields renewedConf (by decide) (by decide)

/-- The failure of cleanup-to-entrance conversion occurs on a real row
whose source has the proposed seeking invariant and is actually reached.
The post-state has no parked live bullet, so attack cleanliness cannot
serve as the race entrance certificate. -/
theorem reachable_cleanup_without_entrance :
    EntranceReach coldHPsi coldFrame absorbedState ∧
    GapPair coldHPsi coldFrame absorbedState ∧
    ¬ GapDoneC coldFrame.attack absorbedState.conf ∧
    GapDoneC coldFrame.attack (attemptStepConf coldHPsi coldFrame absorbedState 3) ∧
    ¬ EntranceSuccess coldFrame (attemptStepConf coldHPsi coldFrame absorbedState 3) ∧
    entranceStep coldHPsi coldFrame absorbedState 3 = .active renewedState := by
  refine ⟨absorbed_entranceReach, ?_, ?_, .inl renewed_cleanReady,
    renewed_not_entrance, renewal_active⟩
  · exact LDSinkTwoGapRestartClosure.gapPair_entrance_step_from_pair
      coldHPsi coldFrame
      (CleanBoundaryDecision.restartCleanBoundarySignalResidual_K2 coldHPsi coldFrame)
      blockedState 2 absorbedState blocked_gapPair absorption_active
  · intro hd
    rcases hd with hclean | hdel
    · exact (by decide : (absorbedConf (coldFrame.attack.pos coldFrame.attack.d)).signal_B ≠
        (1 : Fin 2)) hclean.1
    · have hn : ¬ EndpointDeleted coldFrame.attack absorbedConf := by
        unfold EndpointDeleted
        decide
      exact hn hdel

/-- In particular the proposed `SeekingWrapperRows.done_success` field is
false, even when restricted to actual seeking sources on entrance runs. -/
theorem no_done_success_wrapper :
    ¬ (∀ (x : AState 5 1) (e : Fin 5),
      EntranceReach coldHPsi coldFrame x → GapPair coldHPsi coldFrame x →
      ¬ GapDoneC coldFrame.attack x.conf →
      GapDoneC coldFrame.attack (attemptStepConf coldHPsi coldFrame x e) →
        EntranceSuccess coldFrame (attemptStepConf coldHPsi coldFrame x e)) := by
  intro H
  rcases reachable_cleanup_without_entrance with ⟨hr, hg, hn, hd, he, _⟩
  exact he (H absorbedState 3 hr hg hn hd)

/-- The attack is physically clean while the old parked flag remains set. -/
theorem renewed_rank_one : R coldFrame renewedState = 1 := by
  have hd : GapDoneC coldFrame.attack renewedConf := .inl renewed_cleanReady
  simp [R, phaseDebtA, W, renewedState, LDSinkGapServiceRank.gapWC, hd]

private theorem renewed_step_fields : ∀ e : Fin 5,
    (sinkStepC coldHPsi coldFrame.attack renewedConf e 3).bullet ≠ (2 : Fin 3) ∧
    ∀ v : Fin 5,
      (sinkStepC coldHPsi coldFrame.attack renewedConf e v).leader =
        (coldConf v).leader := by
  decide

theorem renewed_every_step_active (e : Fin 5) :
    entranceStep coldHPsi coldFrame renewedState e =
      .active (postState coldHPsi coldFrame renewedState e) := by
  classical
  have hn : ¬ EntranceSuccess coldFrame
      (sinkStepC coldHPsi coldFrame.attack renewedConf e) :=
    not_entrance_of_fields _ (renewed_step_fields e).1 (renewed_step_fields e).2
  rw [entrance_normal_form]
  change (if EntranceSuccess coldFrame
    (sinkStepC coldHPsi coldFrame.attack renewedConf e) then
      (StopNode.success : StopNode (AState 5 1)) else _) = _
  rw [if_neg hn]

/-- Even actual active reachability from `AInvariant` cannot rescue the
old Bellman row: it would need to pay 30 from a budget of 25 at this node. -/
theorem no_reachable_entrance_bellman_row :
    ¬ (∀ b : AState 5 1, EntranceReach coldHPsi coldFrame b →
      1 * 5 + (List.ofFn (fun e : Fin 5 =>
        entrancePotential coldFrame (entranceStep coldHPsi coldFrame b e))).sum ≤
          5 * entrancePotential coldFrame (.active b)) := by
  intro H
  have hstep := H renewedState renewed_entranceReach
  have hpositive : ∀ e : Fin 5, 5 ≤ entrancePotential coldFrame
      (entranceStep coldHPsi coldFrame renewedState e) := by
    intro e
    rw [renewed_every_step_active]
    change 5 ≤ 5 * R coldFrame (postState coldHPsi coldFrame renewedState e)
    have hp := R_pos coldFrame (postState coldHPsi coldFrame renewedState e)
    omega
  have hsum := ofFn_sum_le (fun _ : Fin 5 => 5)
    (fun e : Fin 5 => entrancePotential coldFrame
      (entranceStep coldHPsi coldFrame renewedState e)) hpositive
  rw [FiniteUniformStoppingTree.ofFn_sum_const] at hsum
  change 1 * 5 + _ ≤ 5 * (5 * R coldFrame renewedState) at hstep
  rw [renewed_rank_one] at hstep
  omega

end LDSinkTwoGapRaceEntranceReachObstruction

#print axioms LDSinkTwoGapRaceEntranceReachObstruction.blocked_invariant
#print axioms LDSinkTwoGapRaceEntranceReachObstruction.renewed_entranceReach
#print axioms LDSinkTwoGapRaceEntranceReachObstruction.reachable_cleanup_without_entrance
#print axioms LDSinkTwoGapRaceEntranceReachObstruction.no_done_success_wrapper
#print axioms LDSinkTwoGapRaceEntranceReachObstruction.no_reachable_entrance_bellman_row
