import Leader.Wu.RaceEntrance.LocalService
import Leader.Core.ThreePortSerialCount

set_option autoImplicit false

open FiniteUniformStoppingTree PPLLRepair
open LDSinkGapCleanup LDSinkProtectedAbsorption LDSinkGapDoneInvariant
open LDTwoGapFrame LDSinkTwoGapNoResetKernel LDSinkTwoGapEntrance
open LDSinkTwoGapDeletion LDSinkTwoGapDeletionWired LDSinkTwoGapReachInvariant
open LDSinkTwoGapRaceEntranceLocalService

namespace LDSinkTwoGapRaceEntranceFreshService

variable {n psi : Nat}

/-!
A priced physical fresh-shot producer.  From a clean attack gap, the first
outgoing shooter interaction creates a fresh live shot.  All interactions
away from its incoming and outgoing ports preserve cleanliness, unless a
tagged leader is deleted.  A three-port subevent therefore gives a quarter
of the actual scheduler words within `2*n`.  The stopping target here is
fresh-shot birth or deletion; it is not the stronger race entrance.
-/

def outgoingPort (F : TwoGapFrame n) : Fin n := F.attack.pos F.attack.d

def incomingPort (F : TwoGapFrame n) : Fin n := F.attack.pos (F.attack.d - 1)

private theorem incoming_right (F : TwoGapFrame n) :
    F.attack.ring.rightNeighbor (incomingPort F) = outgoingPort F := by
  unfold incomingPort outgoingPort
  rw [gap_rightNeighbor_pos]
  have hd := F.attack.hd
  congr 1
  omega

private theorem right_injective (G : GapFrame n) (e f : Fin n)
    (h : G.ring.rightNeighbor e = G.ring.rightNeighbor f) : e = f := by
  have hv := congrArg Fin.val h
  change (e.val + 1) % n = (f.val + 1) % n at hv
  have he := e.isLt
  have hf := f.isLt
  apply Fin.ext
  by_cases he1 : e.val + 1 < n
  · rw [Nat.mod_eq_of_lt he1] at hv
    by_cases hf1 : f.val + 1 < n
    · rw [Nat.mod_eq_of_lt hf1] at hv
      omega
    · have hfn : f.val + 1 = n := by omega
      rw [hfn, Nat.mod_self] at hv
      omega
  · have hen : e.val + 1 = n := by omega
    rw [hen, Nat.mod_self] at hv
    by_cases hf1 : f.val + 1 < n
    · rw [Nat.mod_eq_of_lt hf1] at hv
      omega
    · omega

/-- The physical gap invariant supplies all bullet-zero fields once the
untouched shooter signal is framed.  Neutral rows need not be identities
on the other cells. -/
theorem clean_neutral (hpsi : psi > 0) (F : TwoGapFrame n)
    (b : AState n psi) (hg : GapPair hpsi F b)
    (hc : CleanReady F.attack b.conf) (e : Fin n)
    (ho : e ≠ outgoingPort F) (hi : e ≠ incomingPort F)
    (hn : ¬ NoResetSuccess F (attemptStepConf hpsi F b e)) :
    GapPair hpsi F (postState hpsi F b e) ∧
      CleanReady F.attack (attemptStepConf hpsi F b e) := by
  classical
  have ha : physicalBlockStep hpsi F b e = .active (postState hpsi F b e) := by
    rw [physicalBlockStep_normal_form, if_neg hn]
  have hg' := LDSinkTwoGapRestartClosure.gapPair_physical_step hpsi F
    (CleanBoundaryDecision.restartCleanBoundarySignalResidual_K2 hpsi F)
    b e (postState hpsi F b e) hg ha
  refine ⟨hg', (cleanReady_iff_shooter_signal hpsi F.attack _ hg'.attack).mpr ?_⟩
  have hf : sinkStepC hpsi F.attack b.conf e (outgoingPort F) =
      b.conf (outgoingPort F) := by
    apply sinkStepC_other _ _ _ _ _ ho.symm
    intro he
    exact hi (right_injective F.attack e (incomingPort F)
      (he.symm.trans (incoming_right F).symm))
  change (sinkStepC hpsi F.attack b.conf e (outgoingPort F)).signal_B = _
  rw [hf]
  exact hc.1

/-- A fresh proof-level phase is certified from the actual configuration.
The physical step itself still retains its existing phase update. -/
def FreshOrDeleted (hpsi : psi > 0) (F : TwoGapFrame n)
    (C : Fin n → AgentState psi) : Prop :=
  AttemptEntrance hpsi F ⟨C, .transit⟩ ∨ NoResetSuccess F C

noncomputable def freshStep (hpsi : psi > 0) (F : TwoGapFrame n)
    (b : AState n psi) (e : Fin n) : StopNode (AState n psi) := by
  classical
  exact if FreshOrDeleted hpsi F (attemptStepConf hpsi F b e) then .success
    else .active (postState hpsi F b e)

def firingPorts (F : TwoGapFrame n) : ThreePortSerialCount.Ports n where
  a := outgoingPort F
  b := incomingPort F
  c := F.attack.pos 0
  ab := by
    intro he
    have h := F.attack_pos_injective F.attack.d (F.attack.d - 1)
      (by omega) (by omega) he
    have hd := F.attack.hd
    omega
  ac := by
    intro he
    have h := F.attack_pos_injective F.attack.d 0 (by omega) (by omega) he
    have hd := F.attack.hd
    omega
  bc := by
    intro he
    have h := F.attack_pos_injective (F.attack.d - 1) 0 (by omega) (by omega) he
    have hd := F.attack.hd
    omega

def firingRel (hpsi : psi > 0) (F : TwoGapFrame n) :
    StopNode Unit → StopNode (AState n psi) → Prop
  | .failure, _ => True
  | _, .success => True
  | .active _, .active b => GapPair hpsi F b ∧ CleanReady F.attack b.conf
  | _, _ => False

private theorem firingRel_success (hpsi : psi > 0) (F : TwoGapFrame n)
    (u : StopNode Unit) : firingRel hpsi F u .success := by
  cases u <;> trivial

private theorem firing_active_next (hpsi : psi > 0) (F : TwoGapFrame n)
    (b : AState n psi) (hg : GapPair hpsi F b)
    (hc : CleanReady F.attack b.conf) (e : Fin n) :
    firingRel hpsi F (ThreePortSerialCount.stageStep (firingPorts F) () e)
      (freshStep hpsi F b e) := by
  classical
  unfold freshStep
  by_cases hs : FreshOrDeleted hpsi F (attemptStepConf hpsi F b e)
  · rw [if_pos hs]
    exact firingRel_success hpsi F _
  · rw [if_neg hs]
    by_cases ho : e = outgoingPort F
    · subst e
      exact (hs (.inl (clean_outgoing_attemptEntrance hpsi F b hg hc))).elim
    · change firingRel hpsi F
        (if e = outgoingPort F then .success else
          if e = incomingPort F then .failure else
            if e = F.attack.pos 0 then .failure else .active ())
        (.active (postState hpsi F b e))
      rw [if_neg ho]
      by_cases hi : e = incomingPort F
      · rw [if_pos hi]
        trivial
      · rw [if_neg hi]
        by_cases hv : e = F.attack.pos 0
        · rw [if_pos hv]
          trivial
        · rw [if_neg hv]
          exact clean_neutral hpsi F b hg hc e ho hi (fun hd => hs (.inr hd))

theorem firing_simulation (hpsi : psi > 0) (F : TwoGapFrame n) :
    SuccessSimulation (ThreePortSerialCount.stageStep (firingPorts F))
      (freshStep hpsi F) (firingRel hpsi F) where
  terminal := by
    intro u v h
    cases u with
    | failure => exact Nat.zero_le _
    | active p => exact Nat.zero_le _
    | success =>
        cases v with
        | success => exact Nat.le_refl _
        | failure => exact h.elim
        | active b => exact h.elim
  next := by
    intro u v h e
    cases u with
    | failure => trivial
    | success =>
        cases v with
        | success => trivial
        | failure => exact h.elim
        | active b => exact h.elim
    | active p =>
        cases v with
        | success => exact firingRel_success hpsi F _
        | failure => exact h.elim
        | active b => exact firing_active_next hpsi F b h.1 h.2 e

/-- A quarter of the actual words produce a certified fresh attack shot
or delete a tagged leader by `2*n`, from every physically clean gap pair. -/
theorem clean_fresh_shot_quarter (hpsi : psi > 0) (F : TwoGapFrame n)
    (b : AState n psi) (hg : GapPair hpsi F b)
    (hc : CleanReady F.attack b.conf) :
    n ^ (2 * n) ≤ 4 * successCount (freshStep hpsi F) (.active b) (2 * n) := by
  have hn : 3 ≤ n := by
    have hr := F.recovery.hd
    have ha := F.attack.hd
    have hs := F.length_lt
    omega
  have hmass := ThreePortSerialCount.single_stage_quarter (firingPorts F) hn
  have hsim := successCount_le_of_simulation
    (ThreePortSerialCount.stageStep (firingPorts F)) (freshStep hpsi F)
    (firingRel hpsi F) (firing_simulation hpsi F) (.active ()) (.active b)
    ⟨hg, hc⟩ (2 * n)
  exact Nat.le_trans hmass (Nat.mul_le_mul_left 4 hsim)

end LDSinkTwoGapRaceEntranceFreshService

#print axioms LDSinkTwoGapRaceEntranceFreshService.clean_neutral
#print axioms LDSinkTwoGapRaceEntranceFreshService.firing_simulation
#print axioms LDSinkTwoGapRaceEntranceFreshService.clean_fresh_shot_quarter
