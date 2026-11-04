import Leader.PPL.Elim.LocalDeletionCounting
import Leader.PPL.Elim.CleanReadyRank
import Leader.PPL.Elim.TwoLeaderSealedProduct

set_option autoImplicit false
set_option Elab.async false

namespace PPL.Convergence.LDLocal

open FiniteUniformStoppingTree

/-!
# LD(736): controlled vulnerable trial

File 3 is not yet on main. The phase vocabulary below is the exact File-3
surface from design/LDLOCAL_LEAN_PLAN.md. SealedStepSpec is exactly the
one-step closure theorem that File 3 will provide.

ControlRowSpec packages the three local inequalities checked exhaustively by
scripts/ldc_check_control.py. This repair proves the pointwise target-cycle
credit row from SealedStepSpec and the controlled physical step. The remaining
aggregate attacker and retained-live Bellman child-sums are exposed separately
as ControlAttackerBellmanSpec and ControlRetainedBellmanSpec.
-/

structure VulnerableState
    {n : Nat} {ring : DirectedRing n} {C0 : Config n}
    (F : TripleFrame ring C0) where
  cfg : Config n
  attackPhase : SectorPhase
  targetPhase : SectorPhase
  hAttack : PhaseHolds F.A cfg attackPhase
  hTarget : PhaseHolds F.B cfg targetPhase
  alive : ¬ TaggedDeleted F cfg
  targetUnshielded : (cfg F.j).shield = false

def L_j
    {n : Nat} {ring : DirectedRing n} {C0 : Config n}
    (F : TripleFrame ring C0) : Fin n :=
  ring.leftNeighbor F.j

def R_j
    {n : Nat} {ring : DirectedRing n} {C0 : Config n}
    (F : TripleFrame ring C0) : Fin n :=
  F.j

theorem fin3_cases_control (b : Fin 3) :
    b = (0 : Fin 3) ∨ b = (1 : Fin 3) ∨ b = (2 : Fin 3) := by
  rcases b with ⟨v, hv⟩
  rcases v with _ | _ | _ | v
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)
  · omega

theorem rowE_left_shield_false_of_signal_false
    (l r : PPL.Elim.Cell4)
    (hshield : l.shield = false)
    (hsignal : l.signalB = false) :
    (PPL.Elim.rowE l r).1.shield = false := by
  rcases l with ⟨ll, lb, lsh, lsb⟩
  rcases r with ⟨rl, rb, rsh, rsb⟩
  rcases fin3_cases_control lb with h | h | h <;> subst lb <;>
  rcases fin3_cases_control rb with h | h | h <;> subst rb <;>
  cases ll <;> cases lsh <;> cases lsb <;>
  cases rl <;> cases rsh <;> cases rsb <;>
  simp_all [PPL.Elim.rowE]

theorem rowE_right_shield_false_of_false
    (l r : PPL.Elim.Cell4)
    (hshield : r.shield = false) :
    (PPL.Elim.rowE l r).2.shield = false := by
  rcases l with ⟨ll, lb, lsh, lsb⟩
  rcases r with ⟨rl, rb, rsh, rsb⟩
  rcases fin3_cases_control lb with h | h | h <;> subst lb <;>
  rcases fin3_cases_control rb with h | h | h <;> subst rb <;>
  cases ll <;> cases lsh <;> cases lsb <;>
  cases rl <;> cases rsh <;> cases rsb <;>
  simp_all [PPL.Elim.rowE]

theorem leftNeighbor_ne_self_control
    {n : Nat} (ring : DirectedRing n) (hn2 : 2 ≤ n)
    (x : Fin n) :
    ring.leftNeighbor x ≠ x := by
  intro h
  have hv := congrArg Fin.val h
  change (x.val + n - 1) % n = x.val at hv
  rcases Nat.eq_zero_or_pos x.val with h0 | hpos
  · have h1 : (x.val + n - 1) % n = n - 1 := by
      rw [h0, Nat.zero_add]
      exact Nat.mod_eq_of_lt (by omega)
    rw [h1, h0] at hv
    omega
  · have h1 : (x.val + n - 1) % n = x.val - 1 := by
      rw [show x.val + n - 1 = (x.val - 1) + n by omega,
        Nat.add_mod_right]
      exact Nat.mod_eq_of_lt (by omega)
    rw [h1] at hv
    omega

theorem frame_two_le_control
    {n : Nat} {ring : DirectedRing n} {C0 : Config n}
    (F : TripleFrame ring C0) :
    2 ≤ n := by
  have hp := F.B.gap_pos
  have hlt := F.B.gap_lt_n
  omega

theorem vulnerable_not_endpoint_A
    {n : Nat} {ring : DirectedRing n} {C0 : Config n}
    (F : TripleFrame ring C0) (x : VulnerableState F) :
    ¬ EndpointDeleted F.A x.cfg := by
  intro h
  apply x.alive
  rcases h with h | h
  · exact Or.inl (by simpa [F.A_left] using h)
  · exact Or.inr (Or.inl (by simpa [F.A_right] using h))

theorem vulnerable_not_endpoint_B
    {n : Nat} {ring : DirectedRing n} {C0 : Config n}
    (F : TripleFrame ring C0) (x : VulnerableState F) :
    ¬ EndpointDeleted F.B x.cfg := by
  intro h
  apply x.alive
  rcases h with h | h
  · exact Or.inr (Or.inl (by simpa [F.B_left] using h))
  · exact Or.inr (Or.inr (by simpa [F.B_right] using h))

theorem endpointA_deleted_tagged
    {n : Nat} {ring : DirectedRing n} {C0 : Config n}
    (F : TripleFrame ring C0) (C : Config n)
    (h : EndpointDeleted F.A C) :
    TaggedDeleted F C := by
  rcases h with h | h
  · exact Or.inl (by simpa [F.A_left] using h)
  · exact Or.inr (Or.inl (by simpa [F.A_right] using h))

theorem endpointB_deleted_tagged
    {n : Nat} {ring : DirectedRing n} {C0 : Config n}
    (F : TripleFrame ring C0) (C : Config n)
    (h : EndpointDeleted F.B C) :
    TaggedDeleted F C := by
  rcases h with h | h
  · exact Or.inr (Or.inl (by simpa [F.B_left] using h))
  · exact Or.inr (Or.inr (by simpa [F.B_right] using h))

theorem targetSourceSignal_false_of_not_ready
    {n : Nat} {ring : DirectedRing n} {C0 : Config n}
    (F : TripleFrame ring C0) (x : VulnerableState F)
    (hnot : x.targetPhase ≠ .ready) :
    (x.cfg F.j).signalB = false := by
  have ht := x.hTarget
  cases hph : x.targetPhase with
  | ready =>
      exact False.elim (hnot hph)
  | dummy p =>
      rw [hph] at ht
      have hz := ht.2.2.2
      have h0 := hz 0 (Nat.zero_le p)
      simpa [advance_zero, F.B_left] using h0
  | live p =>
      rw [hph] at ht
      have hz := ht.2.2.2
      have h0 := hz 0 (Nat.zero_le p)
      simpa [advance_zero, F.B_left] using h0
  | ret q =>
      rw [hph] at ht
      have hs := ht.2.2.2.2.1
      simpa [F.B_left] using hs

theorem stepE_shield_false_of_source_safe
    {n : Nat} (ring : DirectedRing n)
    (C : Config n) (j e : Fin n)
    (hshield : (C j).shield = false)
    (hsource : e = j → (C j).signalB = false) :
    ((stepE ring C e) j).shield = false := by
  by_cases hje : j = e
  · subst j
    have hs := hsource rfl
    simpa [stepE, PopulationProtocol.step, PPL.Elim.protocolE] using
      (rowE_left_shield_false_of_signal_false
        (C e) (C (ring.rightNeighbor e)) hshield hs)
  · by_cases hjr : j = ring.rightNeighbor e
    · subst j
      simpa [stepE, PopulationProtocol.step, PPL.Elim.protocolE, hje] using
        (rowE_right_shield_false_of_false
          (C e) (C (ring.rightNeighbor e)) hshield)
    · simpa [stepE, PopulationProtocol.step, PPL.Elim.protocolE, hje, hjr] using
        hshield

theorem targetUnshielded_after_physical
    {n : Nat} {ring : DirectedRing n} {C0 : Config n}
    (F : TripleFrame ring C0) (x : VulnerableState F)
    (e : Fin n)
    (hport : x.targetPhase = .ready → e ≠ F.j) :
    ((stepE ring x.cfg e) F.j).shield = false := by
  apply stepE_shield_false_of_source_safe ring x.cfg F.j e x.targetUnshielded
  intro he
  by_cases hready : x.targetPhase = .ready
  · exact False.elim ((hport hready) he)
  · exact targetSourceSignal_false_of_not_ready F x hready

theorem sealedSurvivor_exists
    (hseal : SealedStepSpec)
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (A : SectorFrame ring C0)
    (C : Config n) (ph : SectorPhase)
    (hphase : PhaseHolds A C ph)
    (halive : ¬ EndpointDeleted A C)
    (e : Fin n)
    (hnext : ¬ EndpointDeleted A (stepE ring C e)) :
    ∃ ph',
      PhaseHolds A (stepE ring C e) ph' ∧
      PhaseTransition A ph e ph' := by
  exact
    Or.elim
      (hseal ring A C ph hphase halive e)
      (fun hdel => False.elim (hnext hdel))
      (fun h => h)

noncomputable def sealedSurvivorPhase
    (hseal : SealedStepSpec)
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (A : SectorFrame ring C0)
    (C : Config n) (ph : SectorPhase)
    (hphase : PhaseHolds A C ph)
    (halive : ¬ EndpointDeleted A C)
    (e : Fin n)
    (hnext : ¬ EndpointDeleted A (stepE ring C e)) :
    SectorPhase :=
  Classical.choose
    (sealedSurvivor_exists
      hseal ring A C ph hphase halive e hnext)

theorem sealedSurvivorPhase_holds
    (hseal : SealedStepSpec)
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (A : SectorFrame ring C0)
    (C : Config n) (ph : SectorPhase)
    (hphase : PhaseHolds A C ph)
    (halive : ¬ EndpointDeleted A C)
    (e : Fin n)
    (hnext : ¬ EndpointDeleted A (stepE ring C e)) :
    PhaseHolds A (stepE ring C e)
      (sealedSurvivorPhase
        hseal ring A C ph hphase halive e hnext) := by
  unfold sealedSurvivorPhase
  exact
    (Classical.choose_spec
      (sealedSurvivor_exists
        hseal ring A C ph hphase halive e hnext)).1

theorem sealedSurvivorPhase_transition
    (hseal : SealedStepSpec)
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (A : SectorFrame ring C0)
    (C : Config n) (ph : SectorPhase)
    (hphase : PhaseHolds A C ph)
    (halive : ¬ EndpointDeleted A C)
    (e : Fin n)
    (hnext : ¬ EndpointDeleted A (stepE ring C e)) :
    PhaseTransition A ph e
      (sealedSurvivorPhase
        hseal ring A C ph hphase halive e hnext) := by
  unfold sealedSurvivorPhase
  exact
    (Classical.choose_spec
      (sealedSurvivor_exists
        hseal ring A C ph hphase halive e hnext)).2

theorem vulnerableChild_not_endpoint_A
    {n : Nat} {ring : DirectedRing n} {C0 : Config n}
    (F : TripleFrame ring C0) (x : VulnerableState F)
    (e : Fin n)
    (hnotdel : ¬ TaggedDeleted F (stepE ring x.cfg e)) :
    ¬ EndpointDeleted F.A (stepE ring x.cfg e) := by
  intro hdel
  exact hnotdel
    (endpointA_deleted_tagged F (stepE ring x.cfg e) hdel)

theorem vulnerableChild_not_endpoint_B
    {n : Nat} {ring : DirectedRing n} {C0 : Config n}
    (F : TripleFrame ring C0) (x : VulnerableState F)
    (e : Fin n)
    (hnotdel : ¬ TaggedDeleted F (stepE ring x.cfg e)) :
    ¬ EndpointDeleted F.B (stepE ring x.cfg e) := by
  intro hdel
  exact hnotdel
    (endpointB_deleted_tagged F (stepE ring x.cfg e) hdel)

noncomputable def vulnerableAttackPhase
    {n : Nat} {ring : DirectedRing n} {C0 : Config n}
    (hseal : SealedStepSpec)
    (F : TripleFrame ring C0) (x : VulnerableState F)
    (e : Fin n)
    (hnotdel : ¬ TaggedDeleted F (stepE ring x.cfg e)) :
    SectorPhase :=
  sealedSurvivorPhase
    hseal ring F.A x.cfg x.attackPhase x.hAttack
      (vulnerable_not_endpoint_A F x) e
      (vulnerableChild_not_endpoint_A F x e hnotdel)

noncomputable def vulnerableTargetPhase
    {n : Nat} {ring : DirectedRing n} {C0 : Config n}
    (hseal : SealedStepSpec)
    (F : TripleFrame ring C0) (x : VulnerableState F)
    (e : Fin n)
    (hnotdel : ¬ TaggedDeleted F (stepE ring x.cfg e)) :
    SectorPhase :=
  sealedSurvivorPhase
    hseal ring F.B x.cfg x.targetPhase x.hTarget
      (vulnerable_not_endpoint_B F x) e
      (vulnerableChild_not_endpoint_B F x e hnotdel)

theorem vulnerableAttackPhase_holds
    {n : Nat} {ring : DirectedRing n} {C0 : Config n}
    (hseal : SealedStepSpec)
    (F : TripleFrame ring C0) (x : VulnerableState F)
    (e : Fin n)
    (hnotdel : ¬ TaggedDeleted F (stepE ring x.cfg e)) :
    PhaseHolds F.A (stepE ring x.cfg e)
      (vulnerableAttackPhase hseal F x e hnotdel) := by
  unfold vulnerableAttackPhase
  exact
    sealedSurvivorPhase_holds
      hseal ring F.A x.cfg x.attackPhase x.hAttack
        (vulnerable_not_endpoint_A F x) e
        (vulnerableChild_not_endpoint_A F x e hnotdel)

theorem vulnerableTargetPhase_holds
    {n : Nat} {ring : DirectedRing n} {C0 : Config n}
    (hseal : SealedStepSpec)
    (F : TripleFrame ring C0) (x : VulnerableState F)
    (e : Fin n)
    (hnotdel : ¬ TaggedDeleted F (stepE ring x.cfg e)) :
    PhaseHolds F.B (stepE ring x.cfg e)
      (vulnerableTargetPhase hseal F x e hnotdel) := by
  unfold vulnerableTargetPhase
  exact
    sealedSurvivorPhase_holds
      hseal ring F.B x.cfg x.targetPhase x.hTarget
        (vulnerable_not_endpoint_B F x) e
        (vulnerableChild_not_endpoint_B F x e hnotdel)

theorem vulnerableAttackPhase_transition
    {n : Nat} {ring : DirectedRing n} {C0 : Config n}
    (hseal : SealedStepSpec)
    (F : TripleFrame ring C0) (x : VulnerableState F)
    (e : Fin n)
    (hnotdel : ¬ TaggedDeleted F (stepE ring x.cfg e)) :
    PhaseTransition F.A x.attackPhase e
      (vulnerableAttackPhase hseal F x e hnotdel) := by
  unfold vulnerableAttackPhase
  exact
    sealedSurvivorPhase_transition
      hseal ring F.A x.cfg x.attackPhase x.hAttack
        (vulnerable_not_endpoint_A F x) e
        (vulnerableChild_not_endpoint_A F x e hnotdel)

theorem vulnerableTargetPhase_transition
    {n : Nat} {ring : DirectedRing n} {C0 : Config n}
    (hseal : SealedStepSpec)
    (F : TripleFrame ring C0) (x : VulnerableState F)
    (e : Fin n)
    (hnotdel : ¬ TaggedDeleted F (stepE ring x.cfg e)) :
    PhaseTransition F.B x.targetPhase e
      (vulnerableTargetPhase hseal F x e hnotdel) := by
  unfold vulnerableTargetPhase
  exact
    sealedSurvivorPhase_transition
      hseal ring F.B x.cfg x.targetPhase x.hTarget
        (vulnerable_not_endpoint_B F x) e
        (vulnerableChild_not_endpoint_B F x e hnotdel)

noncomputable def vulnerableChild
    {n : Nat} {ring : DirectedRing n} {C0 : Config n}
    (hseal : SealedStepSpec)
    (F : TripleFrame ring C0) (x : VulnerableState F)
    (e : Fin n)
    (hport : x.targetPhase = .ready → e ≠ F.j)
    (hnotdel : ¬ TaggedDeleted F (stepE ring x.cfg e)) :
    VulnerableState F :=
  {
    cfg := stepE ring x.cfg e
    attackPhase := vulnerableAttackPhase hseal F x e hnotdel
    targetPhase := vulnerableTargetPhase hseal F x e hnotdel
    hAttack := vulnerableAttackPhase_holds hseal F x e hnotdel
    hTarget := vulnerableTargetPhase_holds hseal F x e hnotdel
    alive := hnotdel
    targetUnshielded := targetUnshielded_after_physical F x e hport
  }

theorem vulnerableChild_attack_transition
    {n : Nat} {ring : DirectedRing n} {C0 : Config n}
    (hseal : SealedStepSpec)
    (F : TripleFrame ring C0) (x : VulnerableState F)
    (e : Fin n)
    (hport : x.targetPhase = .ready → e ≠ F.j)
    (hnotdel : ¬ TaggedDeleted F (stepE ring x.cfg e)) :
    PhaseTransition F.A x.attackPhase e
      (vulnerableChild hseal F x e hport hnotdel).attackPhase := by
  change
    PhaseTransition F.A x.attackPhase e
      (vulnerableAttackPhase hseal F x e hnotdel)
  exact vulnerableAttackPhase_transition hseal F x e hnotdel

theorem vulnerableChild_target_transition
    {n : Nat} {ring : DirectedRing n} {C0 : Config n}
    (hseal : SealedStepSpec)
    (F : TripleFrame ring C0) (x : VulnerableState F)
    (e : Fin n)
    (hport : x.targetPhase = .ready → e ≠ F.j)
    (hnotdel : ¬ TaggedDeleted F (stepE ring x.cfg e)) :
    PhaseTransition F.B x.targetPhase e
      (vulnerableChild hseal F x e hport hnotdel).targetPhase := by
  change
    PhaseTransition F.B x.targetPhase e
      (vulnerableTargetPhase hseal F x e hnotdel)
  exact vulnerableTargetPhase_transition hseal F x e hnotdel

noncomputable def vulnerableStep
    {n : Nat} {ring : DirectedRing n} {C0 : Config n}
    (hseal : SealedStepSpec)
    (F : TripleFrame ring C0) :
    VulnerableState F → Fin n → StopNode (VulnerableState F) := by
  classical
  exact fun x e =>
    if hfail : x.targetPhase = .ready ∧ e = R_j F then
      .failure
    else
      let D := stepE ring x.cfg e
      if hdel : TaggedDeleted F D then
        .success
      else
        .active
          (vulnerableChild hseal F x e
            (by
              intro hready he
              exact hfail ⟨hready, by simpa [R_j] using he⟩)
            hdel)

def targetRedirection
    {n : Nat} {ring : DirectedRing n} {C0 : Config n}
    (F : TripleFrame ring C0) (hb : 2 ≤ F.b) :
    ControlledSchedulerMass.Redirection (VulnerableState F) n where
  two_le := frame_two_le_control F
  gate := fun x => decide (x.targetPhase = .ready)
  portA := fun _ => L_j F
  portB := fun _ => R_j F
  distinct := by
    intro x hg
    exact leftNeighbor_ne_self_control ring
      (frame_two_le_control F) F.j

noncomputable def qStep
    {n : Nat} {ring : DirectedRing n} {C0 : Config n}
    (hseal : SealedStepSpec)
    (F : TripleFrame ring C0) (hb : 2 ≤ F.b) :
    VulnerableState F → Fin n → StopNode (VulnerableState F) :=
  ControlledSchedulerMass.controlledStep
    (vulnerableStep hseal F) (targetRedirection F hb)

theorem targetRedirection_effective_R
    {n : Nat} {ring : DirectedRing n} {C0 : Config n}
    (F : TripleFrame ring C0) (hb : 2 ≤ F.b)
    (x : VulnerableState F)
    (hready : x.targetPhase = .ready) :
    (targetRedirection F hb).effective x (R_j F) = L_j F := by
  have hg : (targetRedirection F hb).gate x = true := by
    simp [targetRedirection, hready]
  simpa [targetRedirection] using
    (ControlledSchedulerMass.Redirection.effective_B
      (targetRedirection F hb) x hg)

theorem targetRedirection_no_failure_port
    {n : Nat} {ring : DirectedRing n} {C0 : Config n}
    (F : TripleFrame ring C0) (hb : 2 ≤ F.b)
    (x : VulnerableState F) (e : Fin n) :
    ¬ (x.targetPhase = .ready ∧
      (targetRedirection F hb).effective x e = R_j F) := by
  intro h
  have hg : (targetRedirection F hb).gate x = true := by
    simp [targetRedirection, h.1]
  have hne :=
    ControlledSchedulerMass.Redirection.effective_ne_B
      (targetRedirection F hb) x hg e
  exact hne (by simpa [targetRedirection] using h.2)

theorem qStep_no_failure
    {n : Nat} {ring : DirectedRing n} {C0 : Config n}
    (hseal : SealedStepSpec)
    (F : TripleFrame ring C0) (hb : 2 ≤ F.b)
    (x : VulnerableState F) (e : Fin n) :
    qStep hseal F hb x e ≠ .failure := by
  have hguard :=
    targetRedirection_no_failure_port F hb x e
  classical
  unfold qStep ControlledSchedulerMass.controlledStep vulnerableStep
  rw [dif_neg hguard]
  by_cases hdel :
      TaggedDeleted F
        (stepE ring x.cfg
          ((targetRedirection F hb).effective x e))
  · rw [dif_pos hdel]
    intro h
    cases h
  · rw [dif_neg hdel]
    intro h
    cases h

theorem qStep_active_target_transition
    {n : Nat} {ring : DirectedRing n} {C0 : Config n}
    (hseal : SealedStepSpec)
    (F : TripleFrame ring C0) (hb : 2 ≤ F.b)
    (x y : VulnerableState F) (e : Fin n)
    (hactive : qStep hseal F hb x e = .active y) :
    PhaseTransition F.B x.targetPhase
      ((targetRedirection F hb).effective x e) y.targetPhase := by
  classical
  have hguard :=
    targetRedirection_no_failure_port F hb x e
  have hport :
      x.targetPhase = .ready →
        (targetRedirection F hb).effective x e ≠ F.j := by
    intro hready he
    exact hguard
      ⟨hready, by simpa [R_j] using he⟩
  by_cases hdel :
      TaggedDeleted F
        (stepE ring x.cfg
          ((targetRedirection F hb).effective x e))
  · have hstep :
        qStep hseal F hb x e = .success := by
      simp [qStep, ControlledSchedulerMass.controlledStep,
        vulnerableStep, hguard, hdel]
    have hbad :
        (StopNode.success : StopNode (VulnerableState F)) =
          .active y :=
      hstep.symm.trans hactive
    cases hbad
  · have hstep :
        qStep hseal F hb x e =
          .active
            (vulnerableChild hseal F x
              ((targetRedirection F hb).effective x e)
              hport hdel) := by
      simp [qStep, ControlledSchedulerMass.controlledStep,
        vulnerableStep, hguard, hdel]
    have hsame :
        (StopNode.active
            (vulnerableChild hseal F x
              ((targetRedirection F hb).effective x e)
              hport hdel) :
          StopNode (VulnerableState F)) =
        .active y :=
      hstep.symm.trans hactive
    cases hsame
    exact
      vulnerableChild_target_transition
        hseal F x
          ((targetRedirection F hb).effective x e)
          hport hdel

def targetCycleRank
    {n : Nat} {ring : DirectedRing n} {C0 : Config n}
    (F : TripleFrame ring C0) :
    StopNode (VulnerableState F) → Nat
  | .success => 2 * F.b - 1
  | .failure => 2 * F.b - 1
  | .active x =>
      match x.targetPhase with
      | .ready => 0
      | .dummy p => 2 * F.b - p - 1
      | .live _ => 0
      | .ret q => q

def targetServiceEdge
    {n : Nat} {ring : DirectedRing n} {C0 : Config n}
    (F : TripleFrame ring C0) (x : VulnerableState F) : Fin n :=
  match x.targetPhase with
  | .ready => L_j F
  | .dummy p => advance ring F.B.left p
  | .live p => advance ring F.B.left p
  | .ret q => advance ring F.B.left (q - 1)

def targetServiceCharge
    {n : Nat} {ring : DirectedRing n} {C0 : Config n}
    (F : TripleFrame ring C0) (hb : 2 ≤ F.b) :
    StopNode (VulnerableState F) → Fin n → Nat
  | .active x, e =>
      match x.targetPhase with
      | .ready => 0
      | .live _ => 0
      | .dummy _ =>
          if (targetRedirection F hb).effective x e =
              targetServiceEdge F x then 1 else 0
      | .ret _ =>
          if (targetRedirection F hb).effective x e =
              targetServiceEdge F x then 1 else 0
  | .success, _ => 0
  | .failure, _ => 0

noncomputable def targetServiceWordCount
    {n : Nat} {ring : DirectedRing n} {C0 : Config n}
    (hseal : SealedStepSpec)
    (F : TripleFrame ring C0) (hb : 2 ≤ F.b) :
    StopNode (VulnerableState F) → List (Fin n) → Nat
  | _, [] => 0
  | .success, _ :: _ => 0
  | .failure, _ :: _ => 0
  | .active x, e :: es =>
      targetServiceCharge F hb (.active x) e +
        targetServiceWordCount hseal F hb (qStep hseal F hb x e) es

def attackerCoeff
    {n : Nat} {ring : DirectedRing n} {C0 : Config n}
    (F : TripleFrame ring C0) : SectorPhase → Nat
  | .ready => 3 * F.a - 1
  | .live p => F.a - p
  | .dummy p => 5 * F.a - p - 2
  | .ret q => q + 3 * F.a - 1

def attackerPotential
    {n : Nat} {ring : DirectedRing n} {C0 : Config n}
    (F : TripleFrame ring C0) :
    StopNode (VulnerableState F) → Nat
  | .success => 0
  | .failure => 0
  | .active x => n * attackerCoeff F x.attackPhase

structure RetainedState
    {n : Nat} {ring : DirectedRing n} {C0 : Config n}
    (F : TripleFrame ring C0) where
  base : VulnerableState F
  p : Nat
  phase_eq : base.attackPhase = .live p
  remaining_le : F.a - p ≤ 2 * F.b

noncomputable def retainedStep
    {n : Nat} {ring : DirectedRing n} {C0 : Config n}
    (hseal : SealedStepSpec)
    (F : TripleFrame ring C0) (hb : 2 ≤ F.b) :
    RetainedState F → Fin n → StopNode (RetainedState F) := by
  classical
  exact fun r e =>
    match qStep hseal F hb r.base e with
    | .success => .success
    | .failure => .failure
    | .active y =>
        if h :
            ∃ p, y.attackPhase = .live p ∧ F.a - p ≤ 2 * F.b then
          let p := Classical.choose h
          let hp := Classical.choose_spec h
          .active {
            base := y
            p := p
            phase_eq := hp.1
            remaining_le := hp.2
          }
        else .success

def retainedPotential
    {n : Nat} {ring : DirectedRing n} {C0 : Config n}
    (F : TripleFrame ring C0) :
    StopNode (RetainedState F) → Nat
  | .success => 0
  | .failure => 0
  | .active r => n * (F.a - r.p)

/-- The single File-5-specific residual. Its fields are exactly the local
rows checked by scripts/ldc_check_control.py after the targetUnshielded
amendment. No probability statement is hidden here. -/
structure ControlRowSpec
    {n : Nat} {ring : DirectedRing n} {C0 : Config n}
    (hseal : SealedStepSpec)
    (F : TripleFrame ring C0) (hb : 2 ≤ F.b) : Prop where
  targetCycle :
    ∀ x e,
      (2 * F.b - 1) *
            ControlledSchedulerMass.eventCost
              (targetRedirection F hb) (.active x) e +
          targetCycleRank F (.active x) ≤
        targetServiceCharge F hb (.active x) e +
          targetCycleRank F (qStep hseal F hb x e)
  attackerBellman :
    ∀ x,
      n +
          (List.ofFn (fun e : Fin n =>
            attackerPotential F (qStep hseal F hb x e))).sum ≤
        n * attackerPotential F (.active x)
  retainedBellman :
    ∀ r,
      n +
          (List.ofFn (fun e : Fin n =>
            retainedPotential F (retainedStep hseal F hb r e))).sum ≤
        n * retainedPotential F (.active r)

/-- Remaining aggregate File-5 row: the attacker potential child-sum. -/
noncomputable def ControlAttackerBellmanSpec
    {n : Nat} {ring : DirectedRing n} {C0 : Config n}
    (hseal : SealedStepSpec)
    (F : TripleFrame ring C0) (hb : 2 ≤ F.b) : Prop :=
  ∀ x,
    n +
        (List.ofFn (fun e : Fin n =>
          attackerPotential F (qStep hseal F hb x e))).sum ≤
      n * attackerPotential F (.active x)

/-- Remaining aggregate File-5 row: the retained-live potential child-sum. -/
noncomputable def ControlRetainedBellmanSpec
    {n : Nat} {ring : DirectedRing n} {C0 : Config n}
    (hseal : SealedStepSpec)
    (F : TripleFrame ring C0) (hb : 2 ≤ F.b) : Prop :=
  ∀ r,
    n +
        (List.ofFn (fun e : Fin n =>
          retainedPotential F (retainedStep hseal F hb r e))).sum ≤
      n * retainedPotential F (.active r)

theorem targetCycleRank_le
    {n : Nat} {ring : DirectedRing n} {C0 : Config n}
    (F : TripleFrame ring C0) (hb : 2 ≤ F.b)
    (x : StopNode (VulnerableState F)) :
    targetCycleRank F x ≤ 2 * F.b - 1 := by
  cases x with
  | success => exact Nat.le_refl _
  | failure => exact Nat.le_refl _
  | active x =>
      have ht := x.hTarget
      cases hph : x.targetPhase with
      | ready =>
          simp [targetCycleRank, hph]
      | live p =>
          simp [targetCycleRank, hph]
      | dummy p =>
          rw [hph] at ht
          have hp : p < F.b := by
            have h := ht.2.1.1
            rw [F.B_gap] at h
            exact h
          simp [targetCycleRank, hph]
          omega
      | ret q =>
          rw [hph] at ht
          have hq : q < F.b := by
            have h := ht.2.2.1
            rw [F.B_gap] at h
            exact h
          simp [targetCycleRank, hph]
          omega

theorem sealedIncomingEdge_B_eq_L_j
    {n : Nat} {ring : DirectedRing n} {C0 : Config n}
    (F : TripleFrame ring C0) :
    sealedIncomingEdge F.B = L_j F := by
  unfold sealedIncomingEdge L_j
  rw [F.B_left]

theorem targetRedirection_effective_of_not_ready
    {n : Nat} {ring : DirectedRing n} {C0 : Config n}
    (F : TripleFrame ring C0) (hb : 2 ≤ F.b)
    (x : VulnerableState F) (e : Fin n)
    (hnot : x.targetPhase ≠ .ready) :
    (targetRedirection F hb).effective x e = e := by
  apply
    ControlledSchedulerMass.Redirection.effective_of_gate_false
  simp [targetRedirection, hnot]

theorem targetRedirection_eventCost_of_not_ready
    {n : Nat} {ring : DirectedRing n} {C0 : Config n}
    (F : TripleFrame ring C0) (hb : 2 ≤ F.b)
    (x : VulnerableState F) (e : Fin n)
    (hnot : x.targetPhase ≠ .ready) :
    ControlledSchedulerMass.eventCost
        (targetRedirection F hb) (.active x) e = 0 := by
  simp [ControlledSchedulerMass.eventCost,
    ControlledSchedulerMass.Redirection.Collapses,
    targetRedirection, hnot]

theorem targetEventRank_le_terminal
    {n : Nat} {ring : DirectedRing n} {C0 : Config n}
    (F : TripleFrame ring C0) (hb : 2 ≤ F.b)
    (x : VulnerableState F) (e : Fin n) :
    (2 * F.b - 1) *
          ControlledSchedulerMass.eventCost
            (targetRedirection F hb) (.active x) e +
        targetCycleRank F (.active x) ≤
      2 * F.b - 1 := by
  by_cases hready : x.targetPhase = .ready
  · have hr :
        targetCycleRank F (.active x) = 0 := by
      simp [targetCycleRank, hready]
    rw [hr, Nat.add_zero]
    have hc :
        ControlledSchedulerMass.eventCost
            (targetRedirection F hb) (.active x) e ≤ 1 := by
      simp [ControlledSchedulerMass.eventCost]
      split <;> omega
    simpa using
      (Nat.mul_le_mul_left (2 * F.b - 1) hc)
  · have hc :=
      targetRedirection_eventCost_of_not_ready
        F hb x e hready
    rw [hc, Nat.mul_zero, Nat.zero_add]
    exact targetCycleRank_le F hb (.active x)

theorem targetPhase_row
    {n : Nat} {ring : DirectedRing n} {C0 : Config n}
    (F : TripleFrame ring C0) (hb : 2 ≤ F.b)
    (x y : VulnerableState F) (e : Fin n)
    (htr :
      PhaseTransition F.B x.targetPhase
        ((targetRedirection F hb).effective x e)
        y.targetPhase) :
    (2 * F.b - 1) *
          ControlledSchedulerMass.eventCost
            (targetRedirection F hb) (.active x) e +
        targetCycleRank F (.active x) ≤
      targetServiceCharge F hb (.active x) e +
        targetCycleRank F (.active y) := by
  cases hph : x.targetPhase with
  | ready =>
      have htr' := htr
      rw [hph] at htr'
      by_cases hcol :
          (targetRedirection F hb).Collapses x e
      · have heffPort :=
          ((targetRedirection F hb).collapses_iff_effective x e).mp
            hcol
        have heffL :
            (targetRedirection F hb).effective x e = L_j F := by
          simpa [targetRedirection] using heffPort.2
        have heffIn :
            (targetRedirection F hb).effective x e =
              sealedIncomingEdge F.B :=
          heffL.trans (sealedIncomingEdge_B_eq_L_j F).symm
        have hy : y.targetPhase = .dummy 0 := by
          simpa [PhaseTransition, nextSectorPhase, heffIn] using htr'
        simp [ControlledSchedulerMass.eventCost, hcol,
          targetCycleRank, hph, targetServiceCharge, hy]
      · have hc :
            ControlledSchedulerMass.eventCost
                (targetRedirection F hb) (.active x) e = 0 := by
          simp [ControlledSchedulerMass.eventCost, hcol]
        simp [hc, targetCycleRank, hph, targetServiceCharge]
  | live p =>
      have hnot : x.targetPhase ≠ .ready := by
        rw [hph]
        intro h
        cases h
      have hc :=
        targetRedirection_eventCost_of_not_ready
          F hb x e hnot
      rw [hc]
      simp [targetCycleRank, hph, targetServiceCharge]
  | dummy p =>
      have ht := x.hTarget
      rw [hph] at ht
      have hp : p < F.b := by
        have hp' := ht.2.1.1
        rw [F.B_gap] at hp'
        exact hp'
      have hnot : x.targetPhase ≠ .ready := by
        rw [hph]
        intro h
        cases h
      have heff :=
        targetRedirection_effective_of_not_ready
          F hb x e hnot
      have hc :=
        targetRedirection_eventCost_of_not_ready
          F hb x e hnot
      have htr' := htr
      rw [hph] at htr'
      rw [heff] at htr'
      by_cases hsrv : e = targetServiceEdge F x
      · have hsrv' : e = advance ring F.B.left p := by
          simpa [targetServiceEdge, hph] using hsrv
        have heffService :
            (targetRedirection F hb).effective x e =
              targetServiceEdge F x :=
          heff.trans hsrv
        have hcharge :
            targetServiceCharge F hb (.active x) e = 1 := by
          simp [targetServiceCharge, hph, heffService]
        by_cases hnext : p + 1 < F.b
        · have hnextB : p + 1 < F.B.gap := by
            simpa [F.B_gap] using hnext
          have hy : y.targetPhase = .dummy (p + 1) := by
            simpa [PhaseTransition, nextSectorPhase,
              heff, hsrv', hnextB] using htr'
          rw [hc, hcharge]
          simp [targetCycleRank, hph, hy]
          omega
        · have hnextB : ¬ (p + 1 < F.B.gap) := by
            rw [F.B_gap]
            exact hnext
          have hgap1 : F.B.gap ≠ 1 := by
            rw [F.B_gap]
            omega
          have hb1 : F.b ≠ 1 := by omega
          have hy : y.targetPhase = .ret (F.b - 1) := by
            simpa [PhaseTransition, nextSectorPhase,
              heff, hsrv', hnextB, hgap1, F.B_gap, hnext, hb1] using htr'
          rw [hc, hcharge]
          simp [targetCycleRank, hph, hy]
          omega
      · have hsrv' : e ≠ advance ring F.B.left p := by
          simpa [targetServiceEdge, hph] using hsrv
        have hcharge :
            targetServiceCharge F hb (.active x) e = 0 := by
          simp [targetServiceCharge, hph, heff, hsrv]
        have hy : y.targetPhase = .dummy p := by
          simpa [PhaseTransition, nextSectorPhase,
            heff, hsrv'] using htr'
        rw [hc, hcharge]
        simp [targetCycleRank, hph, hy]
  | ret q =>
      have ht := x.hTarget
      rw [hph] at ht
      have hq0 : 0 < q := ht.2.1
      have hnot : x.targetPhase ≠ .ready := by
        rw [hph]
        intro h
        cases h
      have heff :=
        targetRedirection_effective_of_not_ready
          F hb x e hnot
      have hc :=
        targetRedirection_eventCost_of_not_ready
          F hb x e hnot
      have htr' := htr
      rw [hph] at htr'
      rw [heff] at htr'
      by_cases hsrv : e = targetServiceEdge F x
      · have hsrv' :
            e = advance ring F.B.left (q - 1) := by
          simpa [targetServiceEdge, hph] using hsrv
        have heffService :
            (targetRedirection F hb).effective x e =
              targetServiceEdge F x :=
          heff.trans hsrv
        have hcharge :
            targetServiceCharge F hb (.active x) e = 1 := by
          simp [targetServiceCharge, hph, heffService]
        by_cases hq1 : q = 1
        · have hy : y.targetPhase = .ready := by
            simpa [PhaseTransition, nextSectorPhase,
              heff, hsrv', hq1] using htr'
          rw [hc, hcharge]
          simp [targetCycleRank, hph, hy]
          omega
        · have hy : y.targetPhase = .ret (q - 1) := by
            simpa [PhaseTransition, nextSectorPhase,
              heff, hsrv', hq1] using htr'
          rw [hc, hcharge]
          simp [targetCycleRank, hph, hy]
          omega
      · have hsrv' :
            e ≠ advance ring F.B.left (q - 1) := by
          simpa [targetServiceEdge, hph] using hsrv
        have hcharge :
            targetServiceCharge F hb (.active x) e = 0 := by
          simp [targetServiceCharge, hph, heff, hsrv]
        have hy : y.targetPhase = .ret q := by
          simpa [PhaseTransition, nextSectorPhase,
            heff, hsrv'] using htr'
        rw [hc, hcharge]
        simp [targetCycleRank, hph, hy]

theorem targetCycleRow_proved
    {n : Nat} {ring : DirectedRing n} {C0 : Config n}
    (hseal : SealedStepSpec)
    (F : TripleFrame ring C0) (hb : 2 ≤ F.b) :
    ∀ x e,
      (2 * F.b - 1) *
            ControlledSchedulerMass.eventCost
              (targetRedirection F hb) (.active x) e +
          targetCycleRank F (.active x) ≤
        targetServiceCharge F hb (.active x) e +
          targetCycleRank F (qStep hseal F hb x e) := by
  intro x e
  cases hq : qStep hseal F hb x e with
  | success =>
      have hbase :=
        targetEventRank_le_terminal F hb x e
      calc
        (2 * F.b - 1) *
              ControlledSchedulerMass.eventCost
                (targetRedirection F hb) (.active x) e +
            targetCycleRank F (.active x) ≤
          2 * F.b - 1 := hbase
        _ ≤
          targetServiceCharge F hb (.active x) e +
            targetCycleRank F .success := by
              have hrank :
                  targetCycleRank F (.success : StopNode (VulnerableState F)) =
                    2 * F.b - 1 := rfl
              rw [hrank]
              omega
  | failure =>
      exact False.elim
        ((qStep_no_failure hseal F hb x e) hq)
  | active y =>
      have htr :=
        qStep_active_target_transition
          hseal F hb x y e hq
      have hrow :=
        targetPhase_row F hb x y e htr
      simpa [hq] using hrow

theorem controlRowSpec_of_residuals
    {n : Nat} {ring : DirectedRing n} {C0 : Config n}
    (hseal : SealedStepSpec)
    (F : TripleFrame ring C0) (hb : 2 ≤ F.b)
    (hattack : ControlAttackerBellmanSpec hseal F hb)
    (hretained : ControlRetainedBellmanSpec hseal F hb) :
    ControlRowSpec hseal F hb := by
  exact {
    targetCycle := targetCycleRow_proved hseal F hb
    attackerBellman := hattack
    retainedBellman := hretained
  }

theorem target_cycle_telescope
    {n : Nat} {ring : DirectedRing n} {C0 : Config n}
    (hseal : SealedStepSpec)
    (F : TripleFrame ring C0) (hb : 2 ≤ F.b)
    (hrows : ControlRowSpec hseal F hb)
    (x : StopNode (VulnerableState F))
    (w : List (Fin n)) :
    (2 * F.b - 1) *
          ControlledSchedulerMass.eventCount
            (qStep hseal F hb) (targetRedirection F hb) x w +
        targetCycleRank F x ≤
      targetServiceWordCount hseal F hb x w +
        targetCycleRank F
          (ControlledSchedulerMass.runWord (qStep hseal F hb) x w) := by
  induction w generalizing x with
  | nil =>
      simp [ControlledSchedulerMass.eventCount,
        ControlledSchedulerMass.runWord, targetServiceWordCount]
  | cons e es ih =>
      cases x with
      | success =>
          simpa [ControlledSchedulerMass.eventCount,
            ControlledSchedulerMass.eventCost,
            ControlledSchedulerMass.eventCount_success,
            ControlledSchedulerMass.runWord,
            ControlledSchedulerMass.runWord_success,
            targetServiceWordCount, targetCycleRank, stepNode] using
            (Nat.le_refl (2 * F.b - 1))
      | failure =>
          simpa [ControlledSchedulerMass.eventCount,
            ControlledSchedulerMass.eventCost,
            ControlledSchedulerMass.eventCount_failure,
            ControlledSchedulerMass.runWord,
            ControlledSchedulerMass.runWord_failure,
            targetServiceWordCount, targetCycleRank, stepNode] using
            (Nat.le_refl (2 * F.b - 1))
      | active s =>
          have hrow := hrows.targetCycle s e
          have htail := ih (qStep hseal F hb s e)
          simp only [ControlledSchedulerMass.eventCount,
            ControlledSchedulerMass.runWord, targetServiceWordCount,
            stepNode]
          rw [Nat.mul_add]
          calc
            (2 * F.b - 1) *
                  ControlledSchedulerMass.eventCost
                    (targetRedirection F hb) (.active s) e +
                (2 * F.b - 1) *
                  ControlledSchedulerMass.eventCount
                    (qStep hseal F hb) (targetRedirection F hb)
                    (qStep hseal F hb s e) es +
                targetCycleRank F (.active s)
                =
              ((2 * F.b - 1) *
                    ControlledSchedulerMass.eventCost
                      (targetRedirection F hb) (.active s) e +
                  targetCycleRank F (.active s)) +
                (2 * F.b - 1) *
                  ControlledSchedulerMass.eventCount
                    (qStep hseal F hb) (targetRedirection F hb)
                    (qStep hseal F hb s e) es := by
                      ac_rfl
            _ ≤
              (targetServiceCharge F hb (.active s) e +
                  targetCycleRank F (qStep hseal F hb s e)) +
                (2 * F.b - 1) *
                  ControlledSchedulerMass.eventCount
                    (qStep hseal F hb) (targetRedirection F hb)
                    (qStep hseal F hb s e) es :=
              Nat.add_le_add_right hrow _
            _ =
              targetServiceCharge F hb (.active s) e +
                ((2 * F.b - 1) *
                    ControlledSchedulerMass.eventCount
                      (qStep hseal F hb) (targetRedirection F hb)
                      (qStep hseal F hb s e) es +
                  targetCycleRank F (qStep hseal F hb s e)) := by
                    ac_rfl
            _ ≤
              targetServiceCharge F hb (.active s) e +
                (targetServiceWordCount hseal F hb
                    (qStep hseal F hb s e) es +
                  targetCycleRank F
                    (ControlledSchedulerMass.runWord
                      (qStep hseal F hb)
                      (qStep hseal F hb s e) es)) :=
              Nat.add_le_add_left htail _
            _ =
              targetServiceCharge F hb (.active s) e +
                targetServiceWordCount hseal F hb
                  (qStep hseal F hb s e) es +
                targetCycleRank F
                  (ControlledSchedulerMass.runWord
                    (qStep hseal F hb)
                    (qStep hseal F hb s e) es) := by
                      ac_rfl

theorem target_cycle_pathwise
    {n : Nat} {ring : DirectedRing n} {C0 : Config n}
    (hseal : SealedStepSpec)
    (F : TripleFrame ring C0) (hb : 2 ≤ F.b)
    (hrows : ControlRowSpec hseal F hb)
    (x : VulnerableState F)
    (hstart : x.targetPhase = .dummy 0)
    (w : List (Fin n)) :
    (2 * F.b - 1) *
        ControlledSchedulerMass.eventCount
          (qStep hseal F hb) (targetRedirection F hb) (.active x) w ≤
      targetServiceWordCount hseal F hb (.active x) w := by
  have ht :=
    target_cycle_telescope hseal F hb hrows (.active x) w
  have hr0 :
      targetCycleRank F (.active x) = 2 * F.b - 1 := by
    simp [targetCycleRank, hstart]
  rw [hr0] at ht
  have hend :=
    targetCycleRank_le F hb
      (ControlledSchedulerMass.runWord (qStep hseal F hb) (.active x) w)
  have hplus :
      (2 * F.b - 1) *
            ControlledSchedulerMass.eventCount
              (qStep hseal F hb) (targetRedirection F hb) (.active x) w +
          (2 * F.b - 1) ≤
        targetServiceWordCount hseal F hb (.active x) w +
          (2 * F.b - 1) :=
    Nat.le_trans ht
      (Nat.add_le_add_left hend
        (targetServiceWordCount hseal F hb (.active x) w))
  have hcancel :
      (2 * F.b - 1) +
          (2 * F.b - 1) *
            ControlledSchedulerMass.eventCount
              (qStep hseal F hb) (targetRedirection F hb) (.active x) w ≤
        (2 * F.b - 1) +
          targetServiceWordCount hseal F hb (.active x) w := by
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hplus
  exact Nat.le_of_add_le_add_left hcancel

theorem attackerCoeff_le_five_a
    {n : Nat} {ring : DirectedRing n} {C0 : Config n}
    (F : TripleFrame ring C0) (x : VulnerableState F) :
    attackerCoeff F x.attackPhase ≤ 5 * F.a := by
  have hA := x.hAttack
  cases hph : x.attackPhase with
  | ready =>
      have ha : 0 < F.a := by
        have h := F.A.gap_pos
        rw [F.A_gap] at h
        exact h
      simp [attackerCoeff, hph]
      omega
  | live p =>
      rw [hph] at hA
      have hp : p < F.a := by
        have h := hA.2.1.1
        rw [F.A_gap] at h
        exact h
      simp [attackerCoeff, hph]
      omega
  | dummy p =>
      rw [hph] at hA
      have hp : p < F.a := by
        have h := hA.2.1.1
        rw [F.A_gap] at h
        exact h
      simp [attackerCoeff, hph]
      omega
  | ret q =>
      rw [hph] at hA
      have hq : q < F.a := by
        have h := hA.2.2.1
        rw [F.A_gap] at h
        exact h
      simp [attackerCoeff, hph]
      omega

theorem attackerPotential_le_five_na
    {n : Nat} {ring : DirectedRing n} {C0 : Config n}
    (F : TripleFrame ring C0) (x : VulnerableState F) :
    attackerPotential F (.active x) ≤ 5 * n * F.a := by
  have hc := attackerCoeff_le_five_a F x
  calc
    attackerPotential F (.active x) =
        n * attackerCoeff F x.attackPhase := rfl
    _ ≤ n * (5 * F.a) := Nat.mul_le_mul_left n hc
    _ = 5 * n * F.a := by ac_rfl

theorem attackerPotential_super
    {n : Nat} {ring : DirectedRing n} {C0 : Config n}
    (hseal : SealedStepSpec)
    (F : TripleFrame ring C0) (hb : 2 ≤ F.b)
    (hrows : ControlRowSpec hseal F hb) :
    NatBellmanSuperSolution
      (qStep hseal F hb) 1 (attackerPotential F) := by
  refine ⟨rfl, rfl, ?_⟩
  intro x
  simpa [Nat.one_mul] using hrows.attackerBellman x

theorem qTrial_cost_five_na
    {n : Nat} {ring : DirectedRing n} {C0 : Config n}
    (hseal : SealedStepSpec)
    (F : TripleFrame ring C0) (hb : 2 ≤ F.b)
    (hrows : ControlRowSpec hseal F hb)
    (x : VulnerableState F) :
    ∀ T,
      truncatedActiveCostNumerator
          (qStep hseal F hb) (.active x) T ≤
        n ^ T * (5 * n * F.a) := by
  intro T
  have hraw :=
    truncatedActiveCostNumerator_mul_le_of_natSuperSolution
      (qStep hseal F hb) 1 (attackerPotential F)
      (attackerPotential_super hseal F hb hrows)
      (.active x) T
  have h0 :
      truncatedActiveCostNumerator
          (qStep hseal F hb) (.active x) T ≤
        n ^ T * attackerPotential F (.active x) := by
    simpa using hraw
  exact Nat.le_trans h0
    (Nat.mul_le_mul_left (n ^ T) (attackerPotential_le_five_na F x))

theorem retainedPotential_super
    {n : Nat} {ring : DirectedRing n} {C0 : Config n}
    (hseal : SealedStepSpec)
    (F : TripleFrame ring C0) (hb : 2 ≤ F.b)
    (hrows : ControlRowSpec hseal F hb) :
    NatBellmanSuperSolution
      (retainedStep hseal F hb) 1 (retainedPotential F) := by
  refine ⟨rfl, rfl, ?_⟩
  intro r
  simpa [Nat.one_mul] using hrows.retainedBellman r

theorem retainedTrial_cost_nr
    {n : Nat} {ring : DirectedRing n} {C0 : Config n}
    (hseal : SealedStepSpec)
    (F : TripleFrame ring C0) (hb : 2 ≤ F.b)
    (hrows : ControlRowSpec hseal F hb)
    (r : RetainedState F) :
    ∀ T,
      truncatedActiveCostNumerator
          (retainedStep hseal F hb) (.active r) T ≤
        n ^ T * (n * (F.a - r.p)) := by
  intro T
  have hraw :=
    truncatedActiveCostNumerator_mul_le_of_natSuperSolution
      (retainedStep hseal F hb) 1 (retainedPotential F)
      (retainedPotential_super hseal F hb hrows)
      (.active r) T
  simpa [retainedPotential] using hraw

end PPL.Convergence.LDLocal

#print axioms PPL.Convergence.LDLocal.fin3_cases_control
#print axioms PPL.Convergence.LDLocal.rowE_left_shield_false_of_signal_false
#print axioms PPL.Convergence.LDLocal.rowE_right_shield_false_of_false
#print axioms PPL.Convergence.LDLocal.leftNeighbor_ne_self_control
#print axioms PPL.Convergence.LDLocal.frame_two_le_control
#print axioms PPL.Convergence.LDLocal.vulnerable_not_endpoint_A
#print axioms PPL.Convergence.LDLocal.vulnerable_not_endpoint_B
#print axioms PPL.Convergence.LDLocal.endpointA_deleted_tagged
#print axioms PPL.Convergence.LDLocal.endpointB_deleted_tagged
#print axioms PPL.Convergence.LDLocal.targetSourceSignal_false_of_not_ready
#print axioms PPL.Convergence.LDLocal.stepE_shield_false_of_source_safe
#print axioms PPL.Convergence.LDLocal.targetUnshielded_after_physical
#print axioms PPL.Convergence.LDLocal.sealedSurvivor_exists
#print axioms PPL.Convergence.LDLocal.sealedSurvivorPhase_holds
#print axioms PPL.Convergence.LDLocal.sealedSurvivorPhase_transition
#print axioms PPL.Convergence.LDLocal.vulnerableChild_not_endpoint_A
#print axioms PPL.Convergence.LDLocal.vulnerableChild_not_endpoint_B
#print axioms PPL.Convergence.LDLocal.vulnerableAttackPhase_holds
#print axioms PPL.Convergence.LDLocal.vulnerableTargetPhase_holds
#print axioms PPL.Convergence.LDLocal.vulnerableAttackPhase_transition
#print axioms PPL.Convergence.LDLocal.vulnerableTargetPhase_transition
#print axioms PPL.Convergence.LDLocal.vulnerableChild_attack_transition
#print axioms PPL.Convergence.LDLocal.vulnerableChild_target_transition
#print axioms PPL.Convergence.LDLocal.targetRedirection_effective_R
#print axioms PPL.Convergence.LDLocal.targetRedirection_no_failure_port
#print axioms PPL.Convergence.LDLocal.qStep_no_failure
#print axioms PPL.Convergence.LDLocal.qStep_active_target_transition
#print axioms PPL.Convergence.LDLocal.targetCycleRank_le
#print axioms PPL.Convergence.LDLocal.sealedIncomingEdge_B_eq_L_j
#print axioms PPL.Convergence.LDLocal.targetRedirection_effective_of_not_ready
#print axioms PPL.Convergence.LDLocal.targetRedirection_eventCost_of_not_ready
#print axioms PPL.Convergence.LDLocal.targetEventRank_le_terminal
#print axioms PPL.Convergence.LDLocal.targetPhase_row
#print axioms PPL.Convergence.LDLocal.targetCycleRow_proved
#print axioms PPL.Convergence.LDLocal.controlRowSpec_of_residuals
#print axioms PPL.Convergence.LDLocal.target_cycle_telescope
#print axioms PPL.Convergence.LDLocal.target_cycle_pathwise
#print axioms PPL.Convergence.LDLocal.attackerCoeff_le_five_a
#print axioms PPL.Convergence.LDLocal.attackerPotential_le_five_na
#print axioms PPL.Convergence.LDLocal.attackerPotential_super
#print axioms PPL.Convergence.LDLocal.qTrial_cost_five_na
#print axioms PPL.Convergence.LDLocal.retainedPotential_super
#print axioms PPL.Convergence.LDLocal.retainedTrial_cost_nr



