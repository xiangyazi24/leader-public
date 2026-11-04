import Leader.Wu.Elimination.SinkTwoGapReachInvariant


open FiniteUniformStoppingTree PPLLRepair
open LDSinkGapCleanup LDSinkKernelC LDSinkProtectedAbsorption
open LDSinkGapDoneInvariant LDSinkGapBlockedPreStep LDSinkGapServiceRank
open LDSinkGapCleanupBound LDTwoGapFrame
open LDSinkTwoGapEpochKernel LDSinkTwoGapEpochSuccessor
open LDSinkTwoGapNoResetKernel LDSinkTwoGapAttemptCells
open LDSinkTwoGapEntrance LDSinkTwoGapDeletionWired
open LDSinkTwoGapReachInvariant
open LDSinkTwoGapEpochDefs
open Classical


namespace LDSinkTwoGapAbsorptionWitness


set_option autoImplicit false
noncomputable section


variable {n psi : Nat}


/-! ## Task 1: failure itself supplies the clearing premise -/


theorem absorption_clears_bullet
    (hpsi : psi > 0) (F : TwoGapFrame n) (x : AState n psi) (e : Fin n)
    (hf : attemptStepRaw hpsi F x e = .failure) :
    (attemptStepConf hpsi F x e (F.attack.pos 1)).bullet !=
      (2 : Fin 3) := by
  have ha : AbsorbedAt F x.conf (attemptStepConf hpsi F x e) :=
    ((attemptStepRaw_failure_iff hpsi F x e).mp hf).2.2.2
  rw [ha.2.2.1]
  decide


theorem no_old_closure_of_absorption
    (hpsi : psi > 0) (F : TwoGapFrame n) (x : AState n psi) (e : Fin n)
    (hi : AInvariant hpsi F x)
    (hf : attemptStepRaw hpsi F x e = .failure) :
    !(forall y : AState n psi,
      EntranceReach hpsi F y -> AInvariant hpsi F y) := by
  have hb : (attemptStepConf hpsi F x e (F.attack.pos 1)).bullet ≠ (2 : Fin 3) := by
    simpa using absorption_clears_bullet hpsi F x e hf
  simpa using no_old_closure_of_cleared_absorption hpsi F x e hi hf hb


/-! ## Task 2: explicit n=5, psi=1 absorption witness -/


def witnessRing : DirectedRing 5 :=
  ⟨by decide⟩


def witnessRecovery : GapFrame 5 where
  ring := witnessRing
  low := ⟨0, by decide⟩
  d := 2
  hd := by decide
  hdn := by decide


def witnessAttack : GapFrame 5 where
  ring := witnessRing
  low := ⟨2, by decide⟩
  d := 2
  hd := by decide
  hdn := by decide


def witnessFrame : TwoGapFrame 5 where
  recovery := witnessRecovery
  attack := witnessAttack
  shared := by decide
  length_lt := by decide


def witnessHPsi : (1 : Nat) > 0 := by decide


def witnessBase : AgentState 1 where
  leader := false
  probe := false
  phase := false
  bit := false
  wait := false
  state := .none
  path := .bot
  reset := false
  carry := false
  count := 0
  label := ⟨0, by decide⟩
  h_field := false
  path2 := none
  path3 := none
  path4 := none
  path5 := none
  p := false
  p_carry := false
  reset_cmd := false
  echo := false
  signal_B := 0
  bullet := 0
  shield := false
  write_state := .none
  write := .none
  last := false
  last_set := false
  last_unset := false
  b_carry := false
  gen_ws := false
  ws_echo := false
  signal_ws := false


def witnessLeader : AgentState 1 :=
  { witnessBase with leader := true }


def witnessProtectedLeader : AgentState 1 :=
  { witnessBase with leader := true, shield := true }


def witnessLive : AgentState 1 :=
  { witnessBase with bullet := 2 }


/-- Global cells 0..4 are:
    leader, follower, protected leader, live-bullet follower, leader. -/
def witnessConf (i : Fin 5) : AgentState 1 :=
  match i.val with
  | 0 => witnessLeader
  | 2 => witnessProtectedLeader
  | 3 => witnessLive
  | 4 => witnessLeader
  | _ => witnessBase


def witnessState : AState 5 1 where
  conf := witnessConf
  phase := .parked


theorem witness_recovery_invariant :
    GapInvariant witnessHPsi witnessFrame.recovery witnessConf := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · constructor
    · change (witnessConf (witnessFrame.recovery.pos 0)).leader = true
      decide
    · change
        (witnessConf
          (witnessFrame.recovery.pos witnessFrame.recovery.d)).leader = true
      decide
  · intro k hk hkd
    have hk1 : k = 1 := by
      have hrd : witnessFrame.recovery.d = 2 := rfl
      have had : witnessFrame.attack.d = 2 := rfl
      omega
    subst k
    decide
  · intro k hk
    have hcases : k = 0 ∨ k = 1 := by
      have hrd : witnessFrame.recovery.d = 2 := rfl
      have had : witnessFrame.attack.d = 2 := rfl
      omega
    rcases hcases with h | h
    · subst k
      decide
    · subst k
      decide
  · intro k j hk hkd _hbullet hkj hjd
    have hj : j = 1 ∨ j = 2 := by
      have hrd : witnessFrame.recovery.d = 2 := rfl
      have had : witnessFrame.attack.d = 2 := rfl
      omega
    rcases hj with h | h
    · subst j
      decide
    · subst j
      decide


theorem witness_attack_invariant :
    GapInvariant witnessHPsi witnessFrame.attack witnessConf := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · constructor
    · change (witnessConf (witnessFrame.attack.pos 0)).leader = true
      decide
    · change
        (witnessConf
          (witnessFrame.attack.pos witnessFrame.attack.d)).leader = true
      decide
  · intro k hk hkd
    have hk1 : k = 1 := by
      have hrd : witnessFrame.recovery.d = 2 := rfl
      have had : witnessFrame.attack.d = 2 := rfl
      omega
    subst k
    decide
  · intro k hk
    have hcases : k = 0 ∨ k = 1 := by
      have hrd : witnessFrame.recovery.d = 2 := rfl
      have had : witnessFrame.attack.d = 2 := rfl
      omega
    rcases hcases with h | h
    · subst k
      decide
    · subst k
      decide
  · intro k j hk hkd _hbullet hkj hjd
    have hj : j = 1 ∨ j = 2 := by
      have hrd : witnessFrame.recovery.d = 2 := rfl
      have had : witnessFrame.attack.d = 2 := rfl
      omega
    rcases hj with h | h
    · subst j
      decide
    · subst j
      decide


theorem witness_attack_blocked :
    GapBlocked witnessFrame.attack witnessConf := by
  refine ⟨?_, ?_, ?_⟩
  · change (witnessConf (witnessFrame.attack.pos 1)).bullet = (2 : Fin 3)
    decide
  · intro k hk hkd
    have hk2 : k = 2 := by
      have hrd : witnessFrame.recovery.d = 2 := rfl
      have had : witnessFrame.attack.d = 2 := rfl
      omega
    subst k
    decide
  · exact Or.inl (by
      change (witnessConf (witnessFrame.attack.pos 0)).shield = true
      decide)


theorem witness_unique_live_shot :
    UniqueLiveShot witnessFrame witnessConf := by
  refine ⟨1, by decide, by decide, by decide, ?_⟩
  intro u hu hud hbu
  have hcases : u = 1 ∨ u = 2 := by
      have hrd : witnessFrame.recovery.d = 2 := rfl
      have had : witnessFrame.attack.d = 2 := rfl
      omega
  rcases hcases with h | h
  · exact h
  · subst u
    have hz :
        (witnessConf (witnessFrame.attack.pos 2)).bullet = (0 : Fin 3) := by
      decide
    exact (hbu hz).elim


theorem witness_tag :
    TagDomain witnessFrame witnessState := by
  refine ⟨witness_unique_live_shot, ?_, ?_⟩
  · constructor
    · intro _
      decide
    · intro _
      rfl
  · exact gapBlocked_not_doneC witnessHPsi witnessFrame.attack witnessConf
      witness_attack_blocked witness_attack_invariant


theorem witness_invariant :
    AInvariant witnessHPsi witnessFrame witnessState := by
  exact ⟨witness_recovery_invariant, witness_attack_invariant, witness_tag⟩


/-! The only kernel computation needed for the witness.  On the protected
victim edge, FIRE is quiet, K2 MOVE absorbs the responder live bullet, and
later stages frame the victim's leader/shield fields. -/


macro "witness_kernel_cases" : tactic => `(tactic|
  (unfold sinkKernelC
   unfold eliminateLeadersNoCollisionFire
   unfold absorbProtectedMove
   try unfold eliminateLeadersNoCollisionZeroLeaderEgressMove
   try unfold eliminateLeadersNoCollisionMove
   unfold eliminateLeadersNoCollisionSignalLeaderSink
   unfold dummyBulletSink
   repeat (first
     | rfl
     | assumption
     | contradiction
     | omega
     | (apply Fin.ext; omega)
     | (split <;> simp_all))))


theorem protected_absorption_fields
    (hpsi : psi > 0) (l r : AgentState psi)
    (hl : l.leader = true)
    (hshield : l.shield = true)
    (hsignal : l.signal_B = (0 : Fin 2))
    (hr : r.leader = false)
    (hbullet : r.bullet = (2 : Fin 3)) :
    let q := sinkKernelC hpsi l r
    q.1.leader = true ∧ q.1.shield = true ∧
      q.2.bullet = (0 : Fin 3) := by
  witness_kernel_cases


theorem witness_post_absorption_fields :
    let C' := sinkStepC witnessHPsi witnessFrame.attack witnessConf
      (witnessFrame.attack.pos 0)
    (C' (witnessFrame.attack.pos 0)).leader = true ∧
      (C' (witnessFrame.attack.pos 0)).shield = true ∧
      (C' (witnessFrame.attack.pos 1)).bullet = (0 : Fin 3) := by
  have hnext :
      witnessFrame.attack.ring.rightNeighbor (witnessFrame.attack.pos 0) =
        witnessFrame.attack.pos 1 := by
    simpa using gap_rightNeighbor_pos witnessFrame.attack 0
  have hne :
      witnessFrame.attack.pos 1 ≠ witnessFrame.attack.pos 0 := by decide
  have hp := protected_absorption_fields witnessHPsi
    (witnessConf (witnessFrame.attack.pos 0))
    (witnessConf (witnessFrame.attack.pos 1))
    (by decide) (by decide) (by decide) (by decide) (by decide)
  dsimp only at hp ⊢
  unfold sinkStepC updatePair
  rw [hnext]
  simpa [hne] using hp


theorem gapInvariant_not_endpointDeleted
    (hpsi : psi > 0) (G : GapFrame n) (C : Fin n -> AgentState psi)
    (hi : GapInvariant hpsi G C) :
    ! EndpointDeleted G C := by
  suffices h : ¬ EndpointDeleted G C by simpa using h
  intro hd
  rcases hd with h0 | hd
  · have hb : true = false := hi.1.1.symm.trans h0
    cases hb
  · have hb : true = false := hi.1.2.symm.trans hd
    cases hb


theorem witness_post_no_success :
    ! NoResetSuccess witnessFrame
      (attemptStepConf witnessHPsi witnessFrame witnessState
        (witnessFrame.attack.pos 0)) := by
  suffices h : ¬ NoResetSuccess witnessFrame
      (attemptStepConf witnessHPsi witnessFrame witnessState
        (witnessFrame.attack.pos 0)) by simpa using h
  have heq := attemptStepConf_eq_sinkStepC witnessHPsi witnessFrame
    witnessState (witnessFrame.attack.pos 0)
  rw [heq]
  intro hs
  have hstep := blocked_pre_steps_protected_or_fire witnessHPsi
    witnessFrame.attack witnessConf witness_attack_blocked
    witness_attack_invariant
  rcases hs with hatt | hrec
  · have hnd : ¬ EndpointDeleted witnessFrame.attack
        (sinkStepC witnessHPsi witnessFrame.attack witnessConf
          (witnessFrame.attack.pos 0)) := by
      simpa using gapInvariant_not_endpointDeleted witnessHPsi witnessFrame.attack
        (sinkStepC witnessHPsi witnessFrame.attack witnessConf
          (witnessFrame.attack.pos 0)) hstep.2.1
    exact hnd hatt
  · rcases hrec with hleft | hright
    · have hneL :
          witnessFrame.recovery.pos 0 ≠ witnessFrame.attack.pos 0 := by decide
      have hneR :
          witnessFrame.recovery.pos 0 ≠
            witnessFrame.attack.ring.rightNeighbor
              (witnessFrame.attack.pos 0) := by decide
      have hframe := sinkStepC_other witnessHPsi witnessFrame.attack witnessConf
        (witnessFrame.attack.pos 0) (witnessFrame.recovery.pos 0)
        hneL hneR
      have hpre :
          (witnessConf (witnessFrame.recovery.pos 0)).leader = true := by
        decide
      have hpost :
          (sinkStepC witnessHPsi witnessFrame.attack witnessConf
            (witnessFrame.attack.pos 0)
            (witnessFrame.recovery.pos 0)).leader = true := by
        rw [hframe]
        exact hpre
      have hbad : true = false := hpost.symm.trans hleft
      cases hbad
    · have hshared :
          witnessFrame.recovery.pos witnessFrame.recovery.d =
            witnessFrame.attack.pos 0 :=
        witnessFrame.shared
      have hpost :
          (sinkStepC witnessHPsi witnessFrame.attack witnessConf
            (witnessFrame.attack.pos 0)
            (witnessFrame.recovery.pos witnessFrame.recovery.d)).leader = true := by
        rw [hshared]
        exact hstep.2.1.1.1
      have hbad : true = false := hpost.symm.trans hright
      cases hbad


theorem witness_failure :
    attemptStepRaw witnessHPsi witnessFrame witnessState
      (witnessFrame.attack.pos 0) = .failure := by
  apply (attemptStepRaw_failure_iff witnessHPsi witnessFrame witnessState
    (witnessFrame.attack.pos 0)).2
  refine ⟨by simpa using witness_post_no_success, ?_⟩
  refine ⟨rfl, rfl, ?_⟩
  refine ⟨by decide, by decide, ?_⟩
  unfold Loss
  have hp := witness_post_absorption_fields
  have heq := attemptStepConf_eq_sinkStepC witnessHPsi witnessFrame
    witnessState (witnessFrame.attack.pos 0)
  rw [heq]
  exact ⟨hp.2.2, hp.2.1, hp.1⟩


theorem witness_refutes :
    !(forall y : AState 5 1,
      EntranceReach witnessHPsi witnessFrame y ->
        AInvariant witnessHPsi witnessFrame y) := by
  exact no_old_closure_of_absorption witnessHPsi witnessFrame witnessState
    (witnessFrame.attack.pos 0) witness_invariant witness_failure


/-! ## Task 3: option (c), exact one-edge reduction -/


/-- This is the smallest missing one-gap fact: only the selected physical edge
and a positive gap cell carrying a post-step bullet matter.  The final
disjunction says that cell is one of the two selected-edge endpoints. -/
def CleanTouchedSignalLaw
    (hpsi : psi > 0) (G : GapFrame n) : Prop :=
  forall (C : Fin n -> AgentState psi) (e : Fin n) (k j : Nat),
    GapInvariant hpsi G C ->
    CleanReady G C ->
    0 < k -> k <= G.d ->
    (sinkStepC hpsi G C e (G.pos k)).bullet != (0 : Fin 3) ->
    k <= j -> j <= G.d ->
    (G.pos k = e ∨ G.pos k = G.ring.rightNeighbor e) ->
    (sinkStepC hpsi G C e (G.pos j)).signal_B = (0 : Fin 2)


theorem gap_signal_after_clean_of_touched
    (hpsi : psi > 0) (G : GapFrame n)
    (hLocal : CleanTouchedSignalLaw hpsi G)
    (C : Fin n -> AgentState psi) (e : Fin n)
    (hi : GapInvariant hpsi G C)
    (hClean : CleanReady G C) :
    GapSignalBelowBullets G (sinkStepC hpsi G C e) := by
  intro k j hk hkd hbullet hkj hjd
  by_cases ht : G.pos k = e ∨ G.pos k = G.ring.rightNeighbor e
  · exact hLocal C e k j hi hClean hk hkd (by simpa using hbullet) hkj hjd ht
  · have hneL : G.pos k ≠ e := by
      intro h
      exact ht (Or.inl h)
    have hneR : G.pos k ≠ G.ring.rightNeighbor e := by
      intro h
      exact ht (Or.inr h)
    have hframe := sinkStepC_other hpsi G C e (G.pos k) hneL hneR
    rw [hframe] at hbullet
    exact (hbullet (hClean.2 k hk hkd)).elim


theorem cleanBoundarySignalResidual_of_touched
    (hpsi : psi > 0) (F : TwoGapFrame n)
    (hLocal : forall G : GapFrame n, CleanTouchedSignalLaw hpsi G) :
    CleanBoundarySignalResidual hpsi F := by
  refine ⟨?_⟩
  intro x e y G hG _hReach hPair _hExceptional hy hClean _hNotClean
  have hd := entrance_active_data_wired hpsi F x y e hy
  have hc : y.conf = attemptStepConf hpsi F x e :=
    congrArg (fun z : AState n psi => z.conf) hd.2
  have hatt : y.conf = sinkStepC hpsi F.attack x.conf e :=
    hc.trans (attemptStepConf_eq_sinkStepC hpsi F x e)
  rcases hG with hG | hG
  · subst G
    have hrec : y.conf = sinkStepC hpsi F.recovery x.conf e :=
      hatt.trans (twoGap_sinkStepC_eq hpsi F x.conf e).symm
    rw [hrec]
    exact gap_signal_after_clean_of_touched hpsi F.recovery
      (hLocal F.recovery) x.conf e hPair.recovery hClean
  · subst G
    rw [hatt]
    exact gap_signal_after_clean_of_touched hpsi F.attack
      (hLocal F.attack) x.conf e hPair.attack hClean


#print axioms absorption_clears_bullet
#print axioms no_old_closure_of_absorption
#print axioms witness_recovery_invariant
#print axioms witness_attack_invariant
#print axioms witness_attack_blocked
#print axioms witness_unique_live_shot
#print axioms witness_tag
#print axioms witness_invariant
#print axioms protected_absorption_fields
#print axioms witness_post_absorption_fields
#print axioms gapInvariant_not_endpointDeleted
#print axioms witness_post_no_success
#print axioms witness_failure
#print axioms witness_refutes
#print axioms gap_signal_after_clean_of_touched
#print axioms cleanBoundarySignalResidual_of_touched


end
end LDSinkTwoGapAbsorptionWitness
