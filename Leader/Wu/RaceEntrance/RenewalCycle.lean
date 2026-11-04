import Leader.Wu.RaceEntrance.ReachObstruction

set_option autoImplicit false

open FiniteUniformStoppingTree PPLLRepair
open LDSinkGapCleanup LDSinkProtectedAbsorption LDSinkGapDoneInvariant
open LDTwoGapFrame LDSinkTwoGapNoResetKernel LDSinkTwoGapEntrance
open LDSinkTwoGapDeletionWired LDSinkTwoGapReachInvariant
open LDSinkTwoGapRaceSupportResolution LDSinkTwoGapRaceEntranceReachObstruction

namespace LDSinkTwoGapRaceEntranceRenewalCycle

/-!
A real active entrance cycle repeatedly creates and absorbs a fresh live
shot.  It rules out a finite nonrenewable absorption budget on the actual
entrance process.  This is an obstruction to that accounting method, not
to a probabilistic service estimate: the repeated word is not a fair run.
-/

def renewalPort (t : Nat) : Fin 5 :=
  if t % 4 = 0 then 4 else if t % 4 = 2 then 2 else 3

def renewalConfAt (t : Nat) (i : Fin 5) : AgentState 1 :=
  { coldConf i with
    signal_B := if i.val = 0 ∧ t ≠ 0 then 1
      else if i.val = 3 ∧ t % 4 ≠ 2 then 1
      else if i.val = 4 ∧ t % 4 = 0 then 1 else 0
    bullet := if i.val = 0 ∧ 5 ≤ t then 1
      else if i.val = 4 ∧ t % 4 = 1 then 2
      else if i.val = 3 ∧ t % 4 = 2 then 2 else 0
    shield := i.val = 2 || (i.val = 4 && t ≠ 0) }

def renewalStateAt (t : Nat) : AState 5 1 := ⟨renewalConfAt t, .parked⟩

private theorem physical_rows : ∀ t : Fin 12, ∀ i : Fin 5,
    sinkStepC coldHPsi coldFrame.attack (renewalConfAt t.val) (renewalPort t.val) i =
      renewalConfAt (t.val + 1) i := by
  decide

private theorem post_row (t : Nat) (ht : t < 12) :
    postState coldHPsi coldFrame (renewalStateAt t) (renewalPort t) =
      renewalStateAt (t + 1) := by
  exact congrArg (fun C => (⟨C, .parked⟩ : AState 5 1))
    (funext (physical_rows ⟨t, ht⟩))

private theorem successor_fields : ∀ t : Fin 12,
    (renewalConfAt (t.val + 1) 2).signal_B = (0 : Fin 2) ∧
    ∀ i : Fin 5,
      (renewalConfAt (t.val + 1) i).leader = (coldConf i).leader := by
  decide

private theorem no_entrance_at_successor (t : Nat) (ht : t < 12) :
    ¬ EntranceSuccess coldFrame (renewalConfAt (t + 1)) := by
  intro he
  have hf := successor_fields ⟨t, ht⟩
  rcases he with hr | hd
  · have hs := hr.2.1
    change (renewalConfAt (t + 1) 2).signal_B = (1 : Fin 2) at hs
    rw [hf.1] at hs
    exact (by decide : (0 : Fin 2) ≠ 1) hs
  · have hn : ¬ NoResetSuccess coldFrame coldConf := by
      unfold NoResetSuccess EndpointDeleted
      decide
    apply hn
    simpa only [NoResetSuccess, EndpointDeleted, hf.2] using hd

theorem active_row (t : Nat) (ht : t < 12) :
    entranceStep coldHPsi coldFrame (renewalStateAt t) (renewalPort t) =
      .active (renewalStateAt (t + 1)) := by
  classical
  rw [entrance_normal_form]
  have hn := no_entrance_at_successor t ht
  have hc := congrArg AState.conf (post_row t ht)
  change attemptStepConf coldHPsi coldFrame (renewalStateAt t) (renewalPort t) =
    renewalConfAt (t + 1) at hc
  rw [hc]
  change (if EntranceSuccess coldFrame (renewalConfAt (t + 1)) then
    StopNode.success else StopNode.active
      (postState coldHPsi coldFrame (renewalStateAt t) (renewalPort t))) = _
  rw [if_neg hn, post_row t ht]

theorem renewal_reachable (t : Nat) (ht : t ≤ 12) :
    EntranceReach coldHPsi coldFrame (renewalStateAt t) := by
  induction t with
  | zero =>
      have hf : ∀ i : Fin 5, renewalConfAt 0 i = renewedConf i := by decide
      have hs : renewalStateAt 0 = renewedState :=
        congrArg (fun C => (⟨C, .parked⟩ : AState 5 1)) (funext hf)
      rw [hs]
      exact renewed_entranceReach
  | succ t ih =>
      exact .next (renewalPort t) (ih (by omega)) (active_row t (by omega))

/-- After two harmless warm-up rounds, the whole physical configuration
and the retained phase return after `[4,3,2,3]`. -/
theorem renewal_cycle_closed : renewalStateAt 12 = renewalStateAt 8 := by
  have hf : ∀ i : Fin 5, renewalConfAt 12 i = renewalConfAt 8 i := by decide
  exact congrArg (fun C => (⟨C, .parked⟩ : AState 5 1)) (funext hf)

/-- The third interaction of this actual cycle is the old absorption
failure.  The entrance wrapper reactivates its physical successor. -/
theorem cycle_absorbs :
    attemptStepRaw coldHPsi coldFrame (renewalStateAt 10) (renewalPort 10) =
      .failure := by
  rw [attemptStepRaw_failure_iff]
  constructor
  · intro hd
    have hc := congrArg AState.conf (post_row 10 (by decide))
    have hl := (successor_fields (⟨10, by decide⟩ : Fin 12)).2
    change attemptStepConf coldHPsi coldFrame (renewalStateAt 10) (renewalPort 10) =
      renewalConfAt 11 at hc
    have hn : ¬ NoResetSuccess coldFrame coldConf := by
      unfold NoResetSuccess EndpointDeleted
      decide
    apply hn
    simpa only [hc, NoResetSuccess, EndpointDeleted, hl] using hd
  · change (renewalStateAt 10).phase = .parked ∧
      renewalPort 10 = coldFrame.attack.pos 0 ∧
      LDSinkTwoGapEpochDefs.AbsorbedAt coldFrame (renewalStateAt 10).conf
        (attemptStepConf coldHPsi coldFrame (renewalStateAt 10) (renewalPort 10))
    refine ⟨rfl, by decide, ?_⟩
    unfold LDSinkTwoGapEpochDefs.AbsorbedAt
    decide

/-- A rank-zero completion can emit another live token and return to the
same state.  Therefore no natural remaining budget can be nonincreasing
on every reachable active row and strictly decrease on each absorption.
In particular, simultaneous live-shot capacity is not a nonrenewable
total reset budget. -/
theorem no_nonrenewable_absorption_budget :
    ¬ (∃ budget : AState 5 1 → Nat,
      ∀ (x : AState 5 1) (e : Fin 5) (y : AState 5 1),
        EntranceReach coldHPsi coldFrame x →
        entranceStep coldHPsi coldFrame x e = .active y →
        budget y ≤ budget x ∧
          (attemptStepRaw coldHPsi coldFrame x e = .failure → budget y < budget x)) := by
  rintro ⟨budget, H⟩
  have h8 := H _ _ _ (renewal_reachable 8 (by decide)) (active_row 8 (by decide))
  have h9 := H _ _ _ (renewal_reachable 9 (by decide)) (active_row 9 (by decide))
  have h10 := H _ _ _ (renewal_reachable 10 (by decide)) (active_row 10 (by decide))
  have h11 := H _ _ _ (renewal_reachable 11 (by decide)) (active_row 11 (by decide))
  have hfirst : budget (renewalStateAt 9) ≤ budget (renewalStateAt 8) := h8.1
  have hsecond : budget (renewalStateAt 10) ≤ budget (renewalStateAt 9) := h9.1
  have hstrict : budget (renewalStateAt 11) < budget (renewalStateAt 10) :=
    h10.2 cycle_absorbs
  have hlast : budget (renewalStateAt 12) ≤ budget (renewalStateAt 11) := h11.1
  rw [renewal_cycle_closed] at hlast
  omega

end LDSinkTwoGapRaceEntranceRenewalCycle

#print axioms LDSinkTwoGapRaceEntranceRenewalCycle.renewal_reachable
#print axioms LDSinkTwoGapRaceEntranceRenewalCycle.renewal_cycle_closed
#print axioms LDSinkTwoGapRaceEntranceRenewalCycle.cycle_absorbs
#print axioms LDSinkTwoGapRaceEntranceRenewalCycle.no_nonrenewable_absorption_budget
