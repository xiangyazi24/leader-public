import Leader.Wu.Splice.MovingFrontTable
import Leader.Wu.Splice.LeaderLossCensus


set_option autoImplicit false
set_option Elab.async false
set_option pp.structureInstances false


namespace B9SpliceR2ArmDelete


open PPLL PPLLDomain PPLLResearchFormulation
  PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
open PPLLLeaderCreationCleanupRepair
open BirthSigMoveDisposalRepair
  BirthShortDoneTerminalBirthSources
open Q11593SpliceControllerDesign
open B9SpliceControllerR1Table
open B9LeaderLossCensus


variable {n psi width kappa tau : Nat}


/-! ## Tiny structural helpers -/


/-- Clockwise successor is injective on every nonempty directed ring. -/
private theorem rightNeighbor_injective (ring : DirectedRing n) :
    Function.Injective ring.rightNeighbor := by
  intro a b hab
  apply Fin.ext
  have hv := congrArg Fin.val hab
  unfold DirectedRing.rightNeighbor at hv
  dsimp only at hv
  by_cases ha : a.val + 1 < n
  · rw [Nat.mod_eq_of_lt ha] at hv
    by_cases hb : b.val + 1 < n
    · rw [Nat.mod_eq_of_lt hb] at hv
      omega
    · have hbeq : b.val + 1 = n := by omega
      rw [hbeq, Nat.mod_self] at hv
      omega
  · have haeq : a.val + 1 = n := by omega
    rw [haeq, Nat.mod_self] at hv
    by_cases hb : b.val + 1 < n
    · rw [Nat.mod_eq_of_lt hb] at hv
      omega
    · have hbeq : b.val + 1 = n := by omega
      omega


private theorem normalizeDeletion_leader_eq_local
    (u : AuthorizedAgentState psi) :
    (normalizeDeletion u).core.leader = u.core.leader := by
  unfold normalizeDeletion
  split <;> rfl


private theorem prepareDisposal_leader_eq_local
    (hpsi : 0 < psi) (u : AuthorizedAgentState psi) :
    (prepareDisposal hpsi u).core.leader = u.core.leader := by
  unfold prepareDisposal
  split
  · unfold markComparisonForDeletion
    split <;> rfl
  · rfl


/-- The R1 preparation cut frames the physical leader bit. -/
private theorem preparedR1_leader_eq
    (hpsi : 0 < psi) (u : R1AgentState psi kappa tau) :
    (preparedR1 hpsi u).core.leader = u.splice.base.core.core.leader := by
  unfold preparedR1 prepared prepareExpiringDisposal
  rw [erase_prepareBoundedDisposal hpsi u.splice.base.core]
  rw [normalizeDeletion_leader_eq_local,
    prepareDisposal_leader_eq_local]
  rfl


private theorem preparedDangerAt_congr_base
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (C D : R1Config n psi kappa tau)
    (hbase : forall i, (D i).splice.base = (C i).splice.base)
    (i : Fin n) :
    PreparedDangerAt hpsi ring D i <->
      PreparedDangerAt hpsi ring C i := by
  unfold PreparedDangerAt PreparedBarrierAt
  dsimp only
  simp only [projectSpliceConfig, preparedR1, prepared]
  rw [hbase i, hbase (ring.rightNeighbor i)]


private theorem protected_left_predecessor
    (ring : DirectedRing n) (C : R1Config n psi kappa tau)
    (i : Fin n) (h : R1ProtectedSpliceEdge ring C i) :
    role (C i) = .predecessorArmed := by
  unfold R1ProtectedSpliceEdge at h
  dsimp only at h
  exact h.1


private theorem protected_right_ne_none
    (ring : DirectedRing n) (C : R1Config n psi kappa tau)
    (i : Fin n) (h : R1ProtectedSpliceEdge ring C i) :
    role (C (ring.rightNeighbor i)) != .none := by
  unfold R1ProtectedSpliceEdge at h
  dsimp only at h
  apply bne_iff_ne.mpr
  intro hn
  rcases h.2 with hf | hv | hp
  · have hx := hf.1
    rw [hn] at hx
    cases hx
  · have hx := hv.1
    rw [hn] at hx
    cases hx
  · have hx := hp.1
    rw [hn] at hx
    cases hx


private theorem step_other
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (ring : DirectedRing n) (C : R1Config n psi kappa tau)
    (e i : Fin n) (hi : i != e)
    (hj : i != ring.rightNeighbor e) :
    step hpsi hwidth hle ring C e i = C i := by
  have hi' : i ≠ e := bne_iff_ne.mp hi
  have hj' : i ≠ ring.rightNeighbor e := bne_iff_ne.mp hj
  simp [step, hi', hj']


private theorem row_of_armA
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (l r : R1AgentState psi kappa tau)
    (h : ArmAGuard hpsi hwidth hle l r) :
    row hpsi hwidth hle l r =
      (setControl l .victimArmed false,
        setControl r .front false) := by
  simp [row, h]


private theorem row_of_armB
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (l r : R1AgentState psi kappa tau)
    (h : ArmBGuard l r) :
    row hpsi hwidth hle l r =
      (setControl l .predecessorArmed false,
        setControl r .front false) := by
  have hx := h
  rcases hx with ⟨hl, hlp, hr, hrp, hleader⟩
  have hA : ¬ ArmAGuard hpsi hwidth hle l r := by
    intro ha
    have hn := ha.2.1
    rw [hr] at hn
    cases hn
  simp [row, hA, h]


private theorem row_of_pendingHold
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (l r : R1AgentState psi kappa tau)
    (h : PendingHoldGuard hpsi hwidth hle l r) :
    row hpsi hwidth hle l r = (l, r) := by
  have hx := h
  rcases hx with ⟨hl, hr, hlp, hrp, hdel⟩
  have hA : ¬ ArmAGuard hpsi hwidth hle l r := by
    intro ha
    have hn := ha.1
    rw [hl] at hn
    cases hn
  have hB : ¬ ArmBGuard l r := by
    intro hb
    have hn := hb.1
    rw [hl] at hn
    cases hn
  have hD : ¬ DeleteGuard hpsi hwidth hle l r := by
    intro hd
    have hf := hd.1
    rw [hl] at hf
    cases hf
  simp [row, hA, hB, hD, h]


private theorem row_of_pendingAbort
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (l r : R1AgentState psi kappa tau)
    (h : PendingAbortGuard hpsi hwidth hle l r) :
    row hpsi hwidth hle l r =
      (clearControl l, clearControl r) := by
  have hx := h
  rcases hx with ⟨hl, hr, hlp, hrp, hleader, hnodel⟩
  have hA : ¬ ArmAGuard hpsi hwidth hle l r := by
    intro ha
    have hn := ha.1
    rw [hl] at hn
    cases hn
  have hB : ¬ ArmBGuard l r := by
    intro hb
    have hn := hb.1
    rw [hl] at hn
    cases hn
  have hD : ¬ DeleteGuard hpsi hwidth hle l r := by
    intro hd
    have hf := hd.1
    rw [hl] at hf
    cases hf
  have hH : ¬ PendingHoldGuard hpsi hwidth hle l r := by
    intro hh
    exact hnodel hh.2.2.2.2
  simp [row, hA, hB, hD, hH, h]


private theorem step_base_armA
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (ring : DirectedRing n) (C : R1Config n psi kappa tau)
    (e : Fin n)
    (h : ArmAGuard hpsi hwidth hle
      (C e) (C (ring.rightNeighbor e))) :
    forall i,
      (step hpsi hwidth hle ring C e i).splice.base =
        (C i).splice.base := by
  intro i
  have hrow := row_of_armA hpsi hwidth hle
    (C e) (C (ring.rightNeighbor e)) h
  by_cases hi : i = e
  · subst i
    simp [step, hrow, setControl]
  · by_cases hj : i = ring.rightNeighbor e
    · subst i
      simp [step, hrow, hi, setControl]
    · simp [step, hrow, hi, hj]


private theorem step_base_armB
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (ring : DirectedRing n) (C : R1Config n psi kappa tau)
    (e : Fin n)
    (h : ArmBGuard (C e) (C (ring.rightNeighbor e))) :
    forall i,
      (step hpsi hwidth hle ring C e i).splice.base =
        (C i).splice.base := by
  intro i
  have hrow := row_of_armB hpsi hwidth hle
    (C e) (C (ring.rightNeighbor e)) h
  by_cases hi : i = e
  · subst i
    simp [step, hrow, setControl]
  · by_cases hj : i = ring.rightNeighbor e
    · subst i
      simp [step, hrow, hi, setControl]
    · simp [step, hrow, hi, hj]


private theorem step_base_pendingAbort
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (ring : DirectedRing n) (C : R1Config n psi kappa tau)
    (e : Fin n)
    (h : PendingAbortGuard hpsi hwidth hle
      (C e) (C (ring.rightNeighbor e))) :
    forall i,
      (step hpsi hwidth hle ring C e i).splice.base =
        (C i).splice.base := by
  intro i
  have hrow := row_of_pendingAbort hpsi hwidth hle
    (C e) (C (ring.rightNeighbor e)) h
  by_cases hi : i = e
  · subst i
    simp [step, hrow, clearControl, setControl]
  · by_cases hj : i = ring.rightNeighbor e
    · subst i
      simp [step, hrow, hi, clearControl, setControl]
    · simp [step, hrow, hi, hj]


private theorem step_pendingHold_eq
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (ring : DirectedRing n) (C : R1Config n psi kappa tau)
    (e : Fin n)
    (h : PendingHoldGuard hpsi hwidth hle
      (C e) (C (ring.rightNeighbor e))) :
    step hpsi hwidth hle ring C e = C := by
  funext i
  have hrow := row_of_pendingHold hpsi hwidth hle
    (C e) (C (ring.rightNeighbor e)) h
  by_cases hi : i = e
  · subst i
    simp [step, hrow]
  · by_cases hj : i = ring.rightNeighbor e
    · subst i
      simp [step, hrow, hi]
    · simp [step, hrow, hi, hj]


/-! ## ARM-A -/


theorem armA_preserves_spliceSafeR1
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (ring : DirectedRing n) (C : R1Config n psi kappa tau)
    (e : Fin n)
    (hsafe : SpliceSafeR1 hpsi ring C)
    (hguard : ArmAGuard hpsi hwidth hle
      (C e) (C (ring.rightNeighbor e))) :
    SpliceSafeR1 hpsi ring
      (step hpsi hwidth hle ring C e) := by
  let D := step hpsi hwidth hle ring C e
  have hbase : forall i, (D i).splice.base = (C i).splice.base := by
    intro i
    exact step_base_armA hpsi hwidth hle ring C e hguard i
  have hg := hguard
  rcases hg with ⟨heNone, hjNone, hePending, hjPending, hdel⟩
  unfold SpliceSafeR1 at hsafe ⊢
  constructor
  · intro i hd
    have hd0 := (preparedDangerAt_congr_base hpsi ring C D hbase i).1 hd
    have hp := hsafe.1 i hd0
    have hl := protected_left_predecessor ring C i hp
    have hrn : role (C (ring.rightNeighbor i)) ≠ .none :=
      bne_iff_ne.mp (protected_right_ne_none ring C i hp)
    have hie : i ≠ e := by
      intro h
      subst i
      rw [heNone] at hl
      cases hl
    have hij : i ≠ ring.rightNeighbor e := by
      intro h
      subst i
      rw [hjNone] at hl
      cases hl
    have hre : ring.rightNeighbor i ≠ e := by
      intro h
      apply hrn
      rw [h, heNone]
    have hrj : ring.rightNeighbor i ≠ ring.rightNeighbor e := by
      intro h
      apply hrn
      rw [h, hjNone]
    unfold R1ProtectedSpliceEdge at hp ⊢
    dsimp only at hp ⊢
    rw [step_other hpsi hwidth hle ring C e i
          (bne_iff_ne.mpr hie) (bne_iff_ne.mpr hij),
      step_other hpsi hwidth hle ring C e
        (ring.rightNeighbor i)
        (bne_iff_ne.mpr hre) (bne_iff_ne.mpr hrj)]
    exact hp
  · intro i hpending
    have hrow := row_of_armA hpsi hwidth hle
      (C e) (C (ring.rightNeighbor e)) hguard
    by_cases hie : i = e
    · subst i
      simp [step, hrow, setControl] at hpending
    · by_cases hij : i = ring.rightNeighbor e
      · subst i
        simp [step, hrow, hie, setControl] at hpending
      · have hfi :
          step hpsi hwidth hle ring C e i = C i :=
          step_other hpsi hwidth hle ring C e i
            (bne_iff_ne.mpr hie) (bne_iff_ne.mpr hij)
        rw [hfi] at hpending
        have hold := hsafe.2 i hpending
        have hre : ring.rightNeighbor i ≠ e := by
          intro h
          have hf := hold.2.1
          rw [h, heNone] at hf
          cases hf
        have hrj : ring.rightNeighbor i ≠ ring.rightNeighbor e := by
          intro h
          have hf := hold.2.1
          rw [h, hjNone] at hf
          cases hf
        have hfr :
            step hpsi hwidth hle ring C e (ring.rightNeighbor i) =
              C (ring.rightNeighbor i) :=
          step_other hpsi hwidth hle ring C e
            (ring.rightNeighbor i)
            (bne_iff_ne.mpr hre) (bne_iff_ne.mpr hrj)
        rw [hfi, hfr]
        exact hold


theorem armB_preserves_spliceSafeR1
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (ring : DirectedRing n) (C : R1Config n psi kappa tau)
    (e : Fin n)
    (hsafe : SpliceSafeR1 hpsi ring C)
    (hguard : ArmBGuard (C e) (C (ring.rightNeighbor e))) :
    SpliceSafeR1 hpsi ring
      (step hpsi hwidth hle ring C e) := by
  let D := step hpsi hwidth hle ring C e
  have hbase : forall i, (D i).splice.base = (C i).splice.base := by
    intro i
    exact step_base_armB hpsi hwidth hle ring C e hguard i
  have hg := hguard
  rcases hg with ⟨heNone, hePending, hjVictim, hjPending, hjLeader⟩
  unfold SpliceSafeR1 at hsafe ⊢
  constructor
  · intro i hd
    have hd0 := (preparedDangerAt_congr_base hpsi ring C D hbase i).1 hd
    have hp := hsafe.1 i hd0
    have hl := protected_left_predecessor ring C i hp
    have hrnB := protected_right_ne_none ring C i hp
    have hrn : role (C (ring.rightNeighbor i)) ≠ .none := by
      simpa only [bne_iff_ne] using hrnB
    have hie : i ≠ e := by
      intro h
      subst i
      rw [heNone] at hl
      cases hl
    have hij : i ≠ ring.rightNeighbor e := by
      intro h
      subst i
      rw [hjVictim] at hl
      cases hl
    have hre : ring.rightNeighbor i ≠ e := by
      intro h
      apply hrn
      rw [h, heNone]
    have hrj : ring.rightNeighbor i ≠ ring.rightNeighbor e := by
      intro h
      exact hie (rightNeighbor_injective ring h)
    have hieB : i != e := by
      rw [bne_iff_ne]
      exact hie
    have hijB : i != ring.rightNeighbor e := by
      rw [bne_iff_ne]
      exact hij
    have hreB : ring.rightNeighbor i != e := by
      rw [bne_iff_ne]
      exact hre
    have hrjB : ring.rightNeighbor i != ring.rightNeighbor e := by
      rw [bne_iff_ne]
      exact hrj
    unfold R1ProtectedSpliceEdge at hp ⊢
    dsimp only at hp ⊢
    rw [step_other hpsi hwidth hle ring C e i hieB hijB,
      step_other hpsi hwidth hle ring C e
        (ring.rightNeighbor i) hreB hrjB]
    exact hp
  · intro i hpending
    have hrow := row_of_armB hpsi hwidth hle
      (C e) (C (ring.rightNeighbor e)) hguard
    by_cases hie : i = e
    · subst i
      simp [D, step, hrow, setControl] at hpending
    · by_cases hij : i = ring.rightNeighbor e
      · subst i
        simp [D, step, hrow, hie, setControl] at hpending
      · have hieB : i != e := by
          rw [bne_iff_ne]
          exact hie
        have hijB : i != ring.rightNeighbor e := by
          rw [bne_iff_ne]
          exact hij
        have hfi : D i = C i :=
          step_other hpsi hwidth hle ring C e i hieB hijB
        rw [show step hpsi hwidth hle ring C e i = C i from hfi] at hpending
        have hold := hsafe.2 i hpending
        have hre : ring.rightNeighbor i ≠ e := by
          intro h
          have hf := hold.2.1
          rw [h, heNone] at hf
          cases hf
        have hrj : ring.rightNeighbor i ≠ ring.rightNeighbor e := by
          intro h
          exact hie (rightNeighbor_injective ring h)
        have hreB : ring.rightNeighbor i != e := by
          rw [bne_iff_ne]
          exact hre
        have hrjB : ring.rightNeighbor i != ring.rightNeighbor e := by
          rw [bne_iff_ne]
          exact hrj
        have hfr : D (ring.rightNeighbor i) = C (ring.rightNeighbor i) :=
          step_other hpsi hwidth hle ring C e
            (ring.rightNeighbor i) hreB hrjB
        rw [show step hpsi hwidth hle ring C e i = C i from hfi,
          show step hpsi hwidth hle ring C e (ring.rightNeighbor i) =
            C (ring.rightNeighbor i) from hfr]
        exact hold


theorem pendingHold_preserves_spliceSafeR1
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (ring : DirectedRing n) (C : R1Config n psi kappa tau)
    (e : Fin n)
    (hsafe : SpliceSafeR1 hpsi ring C)
    (hguard : PendingHoldGuard hpsi hwidth hle
      (C e) (C (ring.rightNeighbor e))) :
    SpliceSafeR1 hpsi ring
      (step hpsi hwidth hle ring C e) := by
  rw [step_pendingHold_eq hpsi hwidth hle ring C e hguard]
  exact hsafe


/-! ## PendingAbort -/


theorem pendingAbort_preserves_spliceSafeR1
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (ring : DirectedRing n) (C : R1Config n psi kappa tau)
    (e : Fin n)
    (hsafe : SpliceSafeR1 hpsi ring C)
    (hguard : PendingAbortGuard hpsi hwidth hle
      (C e) (C (ring.rightNeighbor e))) :
    SpliceSafeR1 hpsi ring
      (step hpsi hwidth hle ring C e) := by
  let D := step hpsi hwidth hle ring C e
  have hbase : forall i, (D i).splice.base = (C i).splice.base := by
    intro i
    exact step_base_pendingAbort hpsi hwidth hle ring C e hguard i
  have hg := hguard
  rcases hg with
    ⟨heVictim, hjFront, hePending, hjPending, heLeader, hnodel⟩
  unfold SpliceSafeR1 at hsafe ⊢
  constructor
  · intro i hd
    have hd0 := (preparedDangerAt_congr_base hpsi ring C D hbase i).1 hd
    have hp := hsafe.1 i hd0
    have hl := protected_left_predecessor ring C i hp
    have hie : i ≠ e := by
      intro h
      subst i
      rw [heVictim] at hl
      cases hl
    have hij : i ≠ ring.rightNeighbor e := by
      intro h
      subst i
      rw [hjFront] at hl
      cases hl
    have hre : ring.rightNeighbor i ≠ e := by
      intro h
      have hb := hd0.2
      unfold PreparedBarrierAt at hb
      dsimp only at hb
      have hfollower :
          (preparedR1 hpsi (C (ring.rightNeighbor i))).core.leader = false := by
        simpa [projectSpliceConfig, preparedR1] using hb.1
      rw [h] at hfollower
      have hprepared :
          (preparedR1 hpsi (C e)).core.leader = true :=
        (preparedR1_leader_eq hpsi (C e)).trans heLeader
      have hbad : (true : Bool) = false :=
        hprepared.symm.trans hfollower
      cases hbad
    have hrj : ring.rightNeighbor i ≠ ring.rightNeighbor e := by
      intro h
      exact hie (rightNeighbor_injective ring h)
    have hieB : i != e := by
      rw [bne_iff_ne]
      exact hie
    have hijB : i != ring.rightNeighbor e := by
      rw [bne_iff_ne]
      exact hij
    have hreB : ring.rightNeighbor i != e := by
      rw [bne_iff_ne]
      exact hre
    have hrjB : ring.rightNeighbor i != ring.rightNeighbor e := by
      rw [bne_iff_ne]
      exact hrj
    unfold R1ProtectedSpliceEdge at hp ⊢
    dsimp only at hp ⊢
    rw [step_other hpsi hwidth hle ring C e i hieB hijB,
      step_other hpsi hwidth hle ring C e
        (ring.rightNeighbor i) hreB hrjB]
    exact hp
  · intro i hpending
    have hrow := row_of_pendingAbort hpsi hwidth hle
      (C e) (C (ring.rightNeighbor e)) hguard
    by_cases hie : i = e
    · subst i
      simp [D, step, hrow, clearControl, setControl] at hpending
    · by_cases hij : i = ring.rightNeighbor e
      · subst i
        simp [D, step, hrow, hie, clearControl, setControl] at hpending
      · have hieB : i != e := by
          rw [bne_iff_ne]
          exact hie
        have hijB : i != ring.rightNeighbor e := by
          rw [bne_iff_ne]
          exact hij
        have hfi : D i = C i :=
          step_other hpsi hwidth hle ring C e i hieB hijB
        rw [show step hpsi hwidth hle ring C e i = C i from hfi] at hpending
        have hold := hsafe.2 i hpending
        have hre : ring.rightNeighbor i ≠ e := by
          intro h
          have hf := hold.2.1
          rw [h, heVictim] at hf
          cases hf
        have hrj : ring.rightNeighbor i ≠ ring.rightNeighbor e := by
          intro h
          exact hie (rightNeighbor_injective ring h)
        have hreB : ring.rightNeighbor i != e := by
          rw [bne_iff_ne]
          exact hre
        have hrjB : ring.rightNeighbor i != ring.rightNeighbor e := by
          rw [bne_iff_ne]
          exact hrj
        have hfr : D (ring.rightNeighbor i) = C (ring.rightNeighbor i) :=
          step_other hpsi hwidth hle ring C e
            (ring.rightNeighbor i) hreB hrjB
        rw [show step hpsi hwidth hle ring C e i = C i from hfi,
          show step hpsi hwidth hle ring C e (ring.rightNeighbor i) =
            C (ring.rightNeighbor i) from hfr]
        exact hold


/-- The following instances are only for the closed finite `decide` fixture. -/
private instance instDecidablePreparedDangerAtLocal
    {n psi kappa tau : Nat}
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (C : R1Config n psi kappa tau) (e : Fin n) :
    Decidable (PreparedDangerAt hpsi ring C e) := by
  unfold PreparedDangerAt PreparedBarrierAt
  dsimp only
  unfold isBarrier
  infer_instance


private instance instDecidableR1ProtectedSpliceEdgeLocal
    {n psi kappa tau : Nat}
    (ring : DirectedRing n) (C : R1Config n psi kappa tau)
    (e : Fin n) :
    Decidable (R1ProtectedSpliceEdge ring C e) := by
  unfold R1ProtectedSpliceEdge
  dsimp only
  infer_instance


private instance instDecidableSpliceSafeR1Local
    {n psi kappa tau : Nat}
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (C : R1Config n psi kappa tau) :
    Decidable (SpliceSafeR1 hpsi ring C) := by
  unfold SpliceSafeR1
  infer_instance


private instance instDecidableDeleteGuardLocal
    {psi width kappa tau : Nat}
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (l r : R1AgentState psi kappa tau) :
    Decidable (DeleteGuard hpsi hwidth hle l r) := by
  unfold DeleteGuard LeftDeletionCandidate
  infer_instance


private theorem hOne : 0 < 1 := by decide
private theorem hOneLe : 1 <= 1 := by decide
private theorem hThree : 0 < 3 := by decide


private def ring3 : DirectedRing 3 := ⟨hThree⟩


private def leaderCore : BoundedAgentState 1 0 :=
  { leader := true
    probe := false
    phase := false
    bit := false
    wait := false
    state := .none
    path := .bot
    reset := false
    carry := false
    count := 0
    label := 0
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
    signal_ws := false }


private def leaderPhysical : ExpiringAgentState 1 0 0 :=
  { core :=
      { core := leaderCore
        path0Crossed := false }
    stall := 0 }


private def leaderR1
    (r : SpliceRole) (pending : Bool) : R1AgentState 1 0 0 :=
  { splice :=
      { base := leaderPhysical
        spliceRole := r }
    repairPending := pending }


/--
Three sites, clockwise:


* 0 = predecessorArmed, pending=true;
* 1 = front, pending=false;
* 2 = front, pending=false;


All three physical cells are leaders.  Hence the prepared-danger clause is
vacuous, while the pending lease at 0 is correctly backed by the front at 1.
-/
private def deleteStart : R1Config 3 1 0 0 := fun i =>
  if i = 0 then leaderR1 .predecessorArmed true
  else leaderR1 .front false


/-- The census confirms the old host never removes the existing right leader
on the DELETE pair. -/
private theorem delete_fixture_right_leader_survives :
    (BirthShortDoneTerminalHost.row hOne hOne hOneLe
      leaderPhysical leaderPhysical).2.core.core.leader = true := by
  exact host_right_existing_leader_survives
    hOne hOne hOneLe leaderPhysical leaderPhysical rfl


set_option maxHeartbeats 50000000 in
set_option maxRecDepth 32768 in
/-- DELETE is false as a preservation obligation for the current R1 table.
The actual executable step on edge 1 changes site 1 from the front backing
site 0's pending lease into another pending predecessor.  Site 0 is untouched,
so the post-state violates the backing conjunct of `SpliceSafeR1`.


This is the smallest non-self-edge shape: one pending predecessor, its backing
front, and the backing front's right endpoint are three distinct sites. -/
theorem delete_branch_counterexample :
    SpliceSafeR1 hOne ring3 deleteStart /\
    DeleteGuard hOne hOne hOneLe
      (deleteStart (1 : Fin 3)) (deleteStart (2 : Fin 3)) /\
    (BirthShortDoneTerminalHost.row hOne hOne hOneLe
      (deleteStart (1 : Fin 3)).splice.base
      (deleteStart (2 : Fin 3)).splice.base).1.core.core.leader = false /\
    (BirthShortDoneTerminalHost.row hOne hOne hOneLe
      (deleteStart (1 : Fin 3)).splice.base
      (deleteStart (2 : Fin 3)).splice.base).2.core.core.leader = true /\
    (step hOne hOne hOneLe ring3 deleteStart
      (1 : Fin 3) (0 : Fin 3)).repairPending = true /\
    role (step hOne hOne hOneLe ring3 deleteStart
      (1 : Fin 3) (ring3.rightNeighbor (0 : Fin 3))) =
        .predecessorArmed /\
    not (SpliceSafeR1 hOne ring3
      (step hOne hOne hOneLe ring3 deleteStart (1 : Fin 3))) := by
  decide


end B9SpliceR2ArmDelete


#print axioms B9SpliceR2ArmDelete.armA_preserves_spliceSafeR1
#print axioms B9SpliceR2ArmDelete.armB_preserves_spliceSafeR1
#print axioms B9SpliceR2ArmDelete.pendingHold_preserves_spliceSafeR1
#print axioms B9SpliceR2ArmDelete.pendingAbort_preserves_spliceSafeR1
#print axioms B9SpliceR2ArmDelete.delete_branch_counterexample
