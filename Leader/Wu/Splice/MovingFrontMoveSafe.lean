import Leader.Wu.Splice.MovingFrontTable


set_option autoImplicit false


namespace B9SpliceR2MoveFrame


open PPLL PPLLResearchFormulation
  PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
open PPLLLeaderCreationCleanupRepair
open BirthSigMoveDisposalRepair
open Q11593SpliceControllerDesign
open B9SpliceControllerR1Table


variable {n psi width kappa tau : Nat}


/-! ## Small reusable facts -/


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


@[simp] private theorem physical_setControl
    (u : R1AgentState psi kappa tau) (r : SpliceRole) (p : Bool) :
    physical (setControl u r p) = physical u := rfl


@[simp] private theorem physical_clearControl
    (u : R1AgentState psi kappa tau) :
    physical (clearControl u) = physical u := rfl


@[simp] private theorem role_setControl
    (u : R1AgentState psi kappa tau) (r : SpliceRole) (p : Bool) :
    role (setControl u r p) = r := rfl


@[simp] private theorem pending_setControl
    (u : R1AgentState psi kappa tau) (r : SpliceRole) (p : Bool) :
    (setControl u r p).repairPending = p := rfl


private theorem normalizeDeletion_label
    (u : AuthorizedAgentState psi) :
    (normalizeDeletion u).core.label = u.core.label := by
  unfold normalizeDeletion
  split <;> rfl


private theorem prepareDisposal_label
    (hpsi : 0 < psi) (u : AuthorizedAgentState psi) :
    (prepareDisposal hpsi u).core.label = u.core.label := by
  unfold prepareDisposal
  split
  · unfold markComparisonForDeletion
    split <;> rfl
  · rfl


private theorem prepared_splice_label
    (hpsi : 0 < psi) (u : SpliceAgentState psi kappa tau) :
    (prepared hpsi u).core.label = u.base.core.core.label := by
  unfold prepared prepareExpiringDisposal
  rw [erase_prepareBoundedDisposal hpsi u.base.core]
  rw [normalizeDeletion_label, prepareDisposal_label]
  rfl


private theorem preparedR1_label
    (hpsi : 0 < psi) (u : R1AgentState psi kappa tau) :
    (preparedR1 hpsi u).core.label = (physical u).core.core.label := by
  unfold preparedR1 physical
  exact prepared_splice_label hpsi u.splice


private theorem preparedR1_eq_of_physical_eq
    (hpsi : 0 < psi) (a b : R1AgentState psi kappa tau)
    (h : physical a = physical b) :
    preparedR1 hpsi a = preparedR1 hpsi b := by
  change a.splice.base = b.splice.base at h
  unfold preparedR1 prepared
  rw [h]


private theorem danger_congr_at
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (C D : R1Config n psi kappa tau) (e : Fin n)
    (hL : physical (D e) = physical (C e))
    (hR : physical (D (ring.rightNeighbor e)) =
      physical (C (ring.rightNeighbor e))) :
    PreparedDangerAt hpsi ring D e <->
      PreparedDangerAt hpsi ring C e := by
  have hl := preparedR1_eq_of_physical_eq hpsi (D e) (C e) hL
  have hr := preparedR1_eq_of_physical_eq hpsi
    (D (ring.rightNeighbor e)) (C (ring.rightNeighbor e)) hR
  unfold PreparedDangerAt PreparedBarrierAt projectSpliceConfig
  dsimp only
  change
    ((preparedR1 hpsi (D e)).core.leader = false /\
      ((preparedR1 hpsi (D (ring.rightNeighbor e))).core.leader = false /\
        isBarrier hpsi (preparedR1 hpsi (D e)).core
          (preparedR1 hpsi (D (ring.rightNeighbor e))).core)) <->
    ((preparedR1 hpsi (C e)).core.leader = false /\
      ((preparedR1 hpsi (C (ring.rightNeighbor e))).core.leader = false /\
        isBarrier hpsi (preparedR1 hpsi (C e)).core
          (preparedR1 hpsi (C (ring.rightNeighbor e))).core))
  rw [hl, hr]


private theorem danger_congr_of_physical
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (C D : R1Config n psi kappa tau)
    (hphys : forall i, physical (D i) = physical (C i))
    (e : Fin n) :
    PreparedDangerAt hpsi ring D e <->
      PreparedDangerAt hpsi ring C e :=
  danger_congr_at hpsi ring C D e
    (hphys e) (hphys (ring.rightNeighbor e))


private theorem localPreparedBarrier_of_danger
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (C : R1Config n psi kappa tau) (e : Fin n)
    (h : PreparedDangerAt hpsi ring C e) :
    LocalPreparedBarrier hpsi (C e) (C (ring.rightNeighbor e)) := by
  simpa [PreparedBarrierAt, LocalPreparedBarrier,
    projectSpliceConfig, preparedR1] using h.2


private theorem localPreparedBarrier_false_of_aligned
    (hpsi : 0 < psi) (l r : R1AgentState psi kappa tau)
    (halign :
      (physical r).core.core.label =
        ⟨((physical l).core.core.label.val + 1) % psi,
          Nat.mod_lt _ hpsi⟩) :
    ¬ LocalPreparedBarrier hpsi l r := by
  intro h
  unfold LocalPreparedBarrier at h
  dsimp only at h
  unfold isBarrier at h
  apply h.2
  apply Fin.ext
  change (preparedR1 hpsi r).core.label.val =
    ((preparedR1 hpsi l).core.label.val + 1) % psi
  rw [preparedR1_label hpsi r, preparedR1_label hpsi l]
  exact congrArg Fin.val halign


private theorem predFalse_not_ownedRight
    (u : R1AgentState psi kappa tau)
    (hr : role u = .predecessorArmed)
    (hp : u.repairPending = false) :
    ¬ ((role u = .front /\ u.repairPending = false) \/
       (role u = .victimArmed /\ u.repairPending = false) \/
       (role u = .predecessorArmed /\ u.repairPending = true)) := by
  intro h
  rcases h with h | h | h
  · rw [hr] at h
    cases h.1
  · rw [hr] at h
    cases h.1
  · rw [hp] at h
    cases h.2


private theorem r1_step_other
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (ring : DirectedRing n) (C : R1Config n psi kappa tau)
    (e i : Fin n) (hi : i ≠ e) (hj : i ≠ ring.rightNeighbor e) :
    step hpsi hwidth hle ring C e i = C i := by
  simp [step, hi, hj]


private theorem step_left_of_row
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (ring : DirectedRing n) (C : R1Config n psi kappa tau)
    (e : Fin n)
    (out : R1AgentState psi kappa tau × R1AgentState psi kappa tau)
    (hrow : row hpsi hwidth hle (C e) (C (ring.rightNeighbor e)) = out) :
    step hpsi hwidth hle ring C e e = out.1 := by
  simp [step, hrow]


private theorem step_right_of_row
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (ring : DirectedRing n) (C : R1Config n psi kappa tau)
    (e : Fin n)
    (out : R1AgentState psi kappa tau × R1AgentState psi kappa tau)
    (hrow : row hpsi hwidth hle (C e) (C (ring.rightNeighbor e)) = out)
    (hne : ring.rightNeighbor e ≠ e) :
    step hpsi hwidth hle ring C e (ring.rightNeighbor e) = out.2 := by
  simp [step, hrow, hne]


private theorem physical_frame_of_row
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (ring : DirectedRing n) (C : R1Config n psi kappa tau)
    (e : Fin n)
    (out : R1AgentState psi kappa tau × R1AgentState psi kappa tau)
    (hrow : row hpsi hwidth hle (C e) (C (ring.rightNeighbor e)) = out)
    (hne : ring.rightNeighbor e ≠ e)
    (hL : physical out.1 = physical (C e))
    (hR : physical out.2 = physical (C (ring.rightNeighbor e))) :
    forall i, physical (step hpsi hwidth hle ring C e i) = physical (C i) := by
  intro i
  by_cases hi : i = e
  · subst i
    rw [step_left_of_row hpsi hwidth hle ring C e out hrow]
    exact hL
  · by_cases hj : i = ring.rightNeighbor e
    · subst i
      rw [step_right_of_row hpsi hwidth hle ring C e out hrow hne]
      exact hR
    · rw [r1_step_other hpsi hwidth hle ring C e i hi hj]


/-! ## Exact branch reductions -/


private theorem row_of_moveCommit
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (l r : R1AgentState psi kappa tau)
    (h : MoveCommitGuard l r) :
    row hpsi hwidth hle l r =
      (clearControl l,
        setControl (repairResponder hpsi l r) .predecessorArmed false) := by
  rcases h with ⟨hl, hlp, hr, hrp, hrf⟩
  simp [row, ArmAGuard, ArmBGuard, DeleteGuard,
    PendingHoldGuard, PendingAbortGuard, MoveCommitGuard,
    hl, hlp, hr, hrp, hrf]


private theorem row_of_moveStop
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (l r : R1AgentState psi kappa tau)
    (h : MoveStopGuard hpsi l r) :
    row hpsi hwidth hle l r = (clearControl l, clearControl r) := by
  rcases h with ⟨hl, hlp, hr, hrp, hstop⟩
  simp [row, ArmAGuard, ArmBGuard, DeleteGuard,
    PendingHoldGuard, PendingAbortGuard, MoveCommitGuard,
    MoveStopGuard, hl, hlp, hr, hrp, hstop]


private theorem row_of_moveSeek
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (l r : R1AgentState psi kappa tau)
    (h : MoveSeekGuard hpsi l r) :
    row hpsi hwidth hle l r =
      (l, setControl r .victimArmed false) := by
  rcases h with ⟨hl, hlp, hr, hrp, hseek⟩
  simp [row, ArmAGuard, ArmBGuard, DeleteGuard,
    PendingHoldGuard, PendingAbortGuard, MoveCommitGuard,
    MoveStopGuard, MoveSeekGuard,
    hl, hlp, hr, hrp, hseek]


private theorem row_of_moveSeekHold
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (l r : R1AgentState psi kappa tau)
    (h : MoveSeekHoldGuard l r) :
    row hpsi hwidth hle l r = (l, r) := by
  rcases h with ⟨hl, hlp, hr, hrp, hrf⟩
  simp [row, ArmAGuard, ArmBGuard, DeleteGuard,
    PendingHoldGuard, PendingAbortGuard, MoveCommitGuard,
    MoveStopGuard, MoveSeekGuard, MoveSeekHoldGuard,
    hl, hlp, hr, hrp, hrf]


private theorem row_of_moveAcquire
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (l r : R1AgentState psi kappa tau)
    (h : MoveAcquireGuard l r) :
    row hpsi hwidth hle l r =
      (setControl l .predecessorArmed true,
        setControl r .front false) := by
  rcases h with ⟨hl, hlp, hlf, hrp, hr | hr⟩
  · simp [row, ArmAGuard, ArmBGuard, DeleteGuard,
      PendingHoldGuard, PendingAbortGuard, MoveCommitGuard,
      MoveStopGuard, MoveSeekGuard, MoveSeekHoldGuard,
      MoveAcquireGuard, LeftDeletionCandidate,
      hl, hlp, hlf, hrp, hr]
  · simp [row, ArmAGuard, ArmBGuard, DeleteGuard,
      PendingHoldGuard, PendingAbortGuard, MoveCommitGuard,
      MoveStopGuard, MoveSeekGuard, MoveSeekHoldGuard,
      MoveAcquireGuard, LeftDeletionCandidate,
      hl, hlp, hlf, hrp, hr]


private theorem moveCommit_ne
    (ring : DirectedRing n) (C : R1Config n psi kappa tau) (e : Fin n)
    (h : MoveCommitGuard (C e) (C (ring.rightNeighbor e))) :
    ring.rightNeighbor e ≠ e := by
  intro hs
  have h' := h
  rw [hs] at h'
  rcases h' with ⟨_, hp0, _, hp1, _⟩
  rw [hp0] at hp1
  cases hp1


private theorem moveStop_ne
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (C : R1Config n psi kappa tau) (e : Fin n)
    (h : MoveStopGuard hpsi (C e) (C (ring.rightNeighbor e))) :
    ring.rightNeighbor e ≠ e := by
  intro hs
  have h' := h
  rw [hs] at h'
  rcases h' with ⟨hp, _, hf, _, _⟩
  rw [hp] at hf
  cases hf


private theorem moveSeek_ne
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (C : R1Config n psi kappa tau) (e : Fin n)
    (h : MoveSeekGuard hpsi (C e) (C (ring.rightNeighbor e))) :
    ring.rightNeighbor e ≠ e := by
  intro hs
  have h' := h
  rw [hs] at h'
  rcases h' with ⟨hp, _, hf, _, _⟩
  rw [hp] at hf
  cases hf


private theorem moveSeekHold_ne
    (ring : DirectedRing n) (C : R1Config n psi kappa tau) (e : Fin n)
    (h : MoveSeekHoldGuard (C e) (C (ring.rightNeighbor e))) :
    ring.rightNeighbor e ≠ e := by
  intro hs
  have h' := h
  rw [hs] at h'
  rcases h' with ⟨hp, _, hv, _, _⟩
  rw [hp] at hv
  cases hv


private theorem moveAcquire_ne
    (ring : DirectedRing n) (C : R1Config n psi kappa tau) (e : Fin n)
    (h : MoveAcquireGuard (C e) (C (ring.rightNeighbor e))) :
    ring.rightNeighbor e ≠ e := by
  intro hs
  have h' := h
  rw [hs] at h'
  rcases h' with ⟨hv, _, _, _, hn | hf⟩
  · rw [hv] at hn
    cases hn
  · rw [hv] at hf
    cases hf


/-! ## 1. Move-family preservation -/


theorem moveCommit_preserves_spliceSafeR1
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (ring : DirectedRing n) (C : R1Config n psi kappa tau) (e : Fin n)
    (hsafe : SpliceSafeR1 hpsi ring C)
    (hg : MoveCommitGuard (C e) (C (ring.rightNeighbor e))) :
    SpliceSafeR1 hpsi ring (step hpsi hwidth hle ring C e) := by
  let D := step hpsi hwidth hle ring C e
  change SpliceSafeR1 hpsi ring D
  have hrow := row_of_moveCommit hpsi hwidth hle
    (C e) (C (ring.rightNeighbor e)) hg
  have hne := moveCommit_ne ring C e hg
  have hE : D e = clearControl (C e) := by
    exact step_left_of_row hpsi hwidth hle ring C e
      (clearControl (C e),
        setControl (repairResponder hpsi (C e) (C (ring.rightNeighbor e)))
          .predecessorArmed false) hrow
  have hJ : D (ring.rightNeighbor e) =
      setControl (repairResponder hpsi (C e) (C (ring.rightNeighbor e)))
        .predecessorArmed false := by
    exact step_right_of_row hpsi hwidth hle ring C e
      (clearControl (C e),
        setControl (repairResponder hpsi (C e) (C (ring.rightNeighbor e)))
          .predecessorArmed false) hrow hne
  rcases hg with ⟨hLe, hLp, hJpred, hJp, _hJfollower⟩
  constructor
  · intro x hd
    by_cases hxe : x = e
    · subst x
      have halign :
          (physical (D (ring.rightNeighbor e))).core.core.label =
            ⟨((physical (D e)).core.core.label.val + 1) % psi,
              Nat.mod_lt _ hpsi⟩ := by
        rw [hE, hJ]
        rfl
      exact (localPreparedBarrier_false_of_aligned hpsi
        (D e) (D (ring.rightNeighbor e)) halign
          (localPreparedBarrier_of_danger hpsi ring D e hd)).elim
    · by_cases hxj : x = ring.rightNeighbor e
      · subst x
        have hback := hsafe.2 (ring.rightNeighbor e) hJp
        have hsE :
            ring.rightNeighbor (ring.rightNeighbor e) ≠ e := by
          intro hs
          have hf := hback.2.1
          rw [hs, hLe] at hf
          cases hf
        have hsJ :
            ring.rightNeighbor (ring.rightNeighbor e) ≠ ring.rightNeighbor e := by
          intro hs
          have hf := hback.2.1
          rw [hs, hJpred] at hf
          cases hf
        have hS :
            D (ring.rightNeighbor (ring.rightNeighbor e)) =
              C (ring.rightNeighbor (ring.rightNeighbor e)) :=
          r1_step_other hpsi hwidth hle ring C e
            (ring.rightNeighbor (ring.rightNeighbor e)) hsE hsJ
        unfold R1ProtectedSpliceEdge
        dsimp only
        rw [hJ, hS]
        exact ⟨rfl, Or.inl ⟨hback.2.1, hback.2.2⟩⟩
      · by_cases hrxe : ring.rightNeighbor x = e
        · have hDx : D x = C x :=
            r1_step_other hpsi hwidth hle ring C e x hxe hxj
          have hLphys : physical (D x) = physical (C x) :=
            congrArg (fun u : R1AgentState psi kappa tau => physical u) hDx
          have hRphys :
              physical (D (ring.rightNeighbor x)) =
                physical (C (ring.rightNeighbor x)) := by
            rw [hrxe, hE]
            rfl
          have hd0 := (danger_congr_at hpsi ring C D x hLphys hRphys).1 hd
          have hp0 := hsafe.1 x hd0
          unfold R1ProtectedSpliceEdge at hp0
          dsimp only at hp0
          rw [hrxe] at hp0
          exact (predFalse_not_ownedRight (C e) hLe hLp hp0.2).elim
        · have hrxj :
              ring.rightNeighbor x ≠ ring.rightNeighbor e := by
            intro h
            exact hxe (rightNeighbor_injective ring h)
          have hDx : D x = C x :=
            r1_step_other hpsi hwidth hle ring C e x hxe hxj
          have hDr : D (ring.rightNeighbor x) =
              C (ring.rightNeighbor x) :=
            r1_step_other hpsi hwidth hle ring C e
              (ring.rightNeighbor x) hrxe hrxj
          have hLphys : physical (D x) = physical (C x) :=
            congrArg (fun u : R1AgentState psi kappa tau => physical u) hDx
          have hRphys : physical (D (ring.rightNeighbor x)) =
              physical (C (ring.rightNeighbor x)) :=
            congrArg (fun u : R1AgentState psi kappa tau => physical u) hDr
          have hd0 :=
            (danger_congr_at hpsi ring C D x hLphys hRphys).1 hd
          have hp0 := hsafe.1 x hd0
          unfold R1ProtectedSpliceEdge at hp0 ⊢
          dsimp only at hp0 ⊢
          rw [hDx, hDr]
          exact hp0
  · intro i hp
    by_cases hie : i = e
    · subst i
      rw [hE] at hp
      change false = true at hp
      cases hp
    · by_cases hij : i = ring.rightNeighbor e
      · subst i
        rw [hJ] at hp
        change false = true at hp
        cases hp
      · have hDi : D i = C i :=
          r1_step_other hpsi hwidth hle ring C e i hie hij
        have hp0 : (C i).repairPending = true := by
          rw [hDi] at hp
          exact hp
        have hb := hsafe.2 i hp0
        have hrE : ring.rightNeighbor i ≠ e := by
          intro h
          have hf := hb.2.1
          rw [h, hLe] at hf
          cases hf
        have hrJ : ring.rightNeighbor i ≠ ring.rightNeighbor e := by
          intro h
          exact hie (rightNeighbor_injective ring h)
        have hDr : D (ring.rightNeighbor i) =
            C (ring.rightNeighbor i) :=
          r1_step_other hpsi hwidth hle ring C e
            (ring.rightNeighbor i) hrE hrJ
        rw [hDi, hDr]
        exact hb


theorem moveStop_preserves_spliceSafeR1
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (ring : DirectedRing n) (C : R1Config n psi kappa tau) (e : Fin n)
    (hsafe : SpliceSafeR1 hpsi ring C)
    (hg : MoveStopGuard hpsi (C e) (C (ring.rightNeighbor e))) :
    SpliceSafeR1 hpsi ring (step hpsi hwidth hle ring C e) := by
  let D := step hpsi hwidth hle ring C e
  change SpliceSafeR1 hpsi ring D
  have hrow := row_of_moveStop hpsi hwidth hle
    (C e) (C (ring.rightNeighbor e)) hg
  have hne := moveStop_ne hpsi ring C e hg
  have hE : D e = clearControl (C e) :=
    step_left_of_row hpsi hwidth hle ring C e
      (clearControl (C e), clearControl (C (ring.rightNeighbor e))) hrow
  have hJ : D (ring.rightNeighbor e) = clearControl (C (ring.rightNeighbor e)) :=
    step_right_of_row hpsi hwidth hle ring C e
      (clearControl (C e), clearControl (C (ring.rightNeighbor e))) hrow hne
  have hphys : forall i, physical (D i) = physical (C i) :=
    physical_frame_of_row hpsi hwidth hle ring C e
      (clearControl (C e), clearControl (C (ring.rightNeighbor e)))
      hrow hne (by rfl) (by rfl)
  rcases hg with ⟨hLe, hLp, hJf, hJp, hstop⟩
  constructor
  · intro x hd
    have hd0 := (danger_congr_of_physical hpsi ring C D hphys x).1 hd
    by_cases hxe : x = e
    · subst x
      exact (hstop (localPreparedBarrier_of_danger hpsi ring C e hd0)).elim
    · by_cases hxj : x = ring.rightNeighbor e
      · subst x
        have hp0 := hsafe.1 (ring.rightNeighbor e) hd0
        unfold R1ProtectedSpliceEdge at hp0
        dsimp only at hp0
        have hbad := hp0.1
        rw [hJf] at hbad
        cases hbad
      · by_cases hrxe : ring.rightNeighbor x = e
        · have hp0 := hsafe.1 x hd0
          unfold R1ProtectedSpliceEdge at hp0
          dsimp only at hp0
          rw [hrxe] at hp0
          exact (predFalse_not_ownedRight (C e) hLe hLp hp0.2).elim
        · have hrxj : ring.rightNeighbor x ≠ ring.rightNeighbor e := by
            intro h
            exact hxe (rightNeighbor_injective ring h)
          have hDx : D x = C x :=
            r1_step_other hpsi hwidth hle ring C e x hxe hxj
          have hDr : D (ring.rightNeighbor x) =
              C (ring.rightNeighbor x) :=
            r1_step_other hpsi hwidth hle ring C e
              (ring.rightNeighbor x) hrxe hrxj
          have hp0 := hsafe.1 x hd0
          unfold R1ProtectedSpliceEdge at hp0 ⊢
          dsimp only at hp0 ⊢
          rw [hDx, hDr]
          exact hp0
  · intro i hp
    by_cases hie : i = e
    · subst i
      rw [hE] at hp
      change false = true at hp
      cases hp
    · by_cases hij : i = ring.rightNeighbor e
      · subst i
        rw [hJ] at hp
        change false = true at hp
        cases hp
      · have hDi : D i = C i :=
          r1_step_other hpsi hwidth hle ring C e i hie hij
        have hp0 : (C i).repairPending = true := by
          rw [hDi] at hp
          exact hp
        have hb := hsafe.2 i hp0
        have hrE : ring.rightNeighbor i ≠ e := by
          intro h
          have hf := hb.2.1
          rw [h, hLe] at hf
          cases hf
        have hrJ : ring.rightNeighbor i ≠ ring.rightNeighbor e := by
          intro h
          exact hie (rightNeighbor_injective ring h)
        have hDr : D (ring.rightNeighbor i) =
            C (ring.rightNeighbor i) :=
          r1_step_other hpsi hwidth hle ring C e
            (ring.rightNeighbor i) hrE hrJ
        rw [hDi, hDr]
        exact hb


theorem moveSeek_preserves_spliceSafeR1
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (ring : DirectedRing n) (C : R1Config n psi kappa tau) (e : Fin n)
    (hsafe : SpliceSafeR1 hpsi ring C)
    (hg : MoveSeekGuard hpsi (C e) (C (ring.rightNeighbor e))) :
    SpliceSafeR1 hpsi ring (step hpsi hwidth hle ring C e) := by
  let D := step hpsi hwidth hle ring C e
  change SpliceSafeR1 hpsi ring D
  have hrow := row_of_moveSeek hpsi hwidth hle
    (C e) (C (ring.rightNeighbor e)) hg
  have hne := moveSeek_ne hpsi ring C e hg
  have hE : D e = C e :=
    step_left_of_row hpsi hwidth hle ring C e
      (C e, setControl (C (ring.rightNeighbor e)) .victimArmed false) hrow
  have hJ : D (ring.rightNeighbor e) =
      setControl (C (ring.rightNeighbor e)) .victimArmed false :=
    step_right_of_row hpsi hwidth hle ring C e
      (C e, setControl (C (ring.rightNeighbor e)) .victimArmed false) hrow hne
  have hphys : forall i, physical (D i) = physical (C i) :=
    physical_frame_of_row hpsi hwidth hle ring C e
      (C e, setControl (C (ring.rightNeighbor e)) .victimArmed false)
      hrow hne (by rfl) (by rfl)
  rcases hg with ⟨hLe, hLp, hJf, hJp, _hseek⟩
  constructor
  · intro x hd
    have hd0 := (danger_congr_of_physical hpsi ring C D hphys x).1 hd
    by_cases hxe : x = e
    · subst x
      unfold R1ProtectedSpliceEdge
      dsimp only
      rw [hE, hJ]
      exact ⟨hLe, Or.inr (Or.inl ⟨rfl, rfl⟩)⟩
    · by_cases hxj : x = ring.rightNeighbor e
      · subst x
        have hp0 := hsafe.1 (ring.rightNeighbor e) hd0
        unfold R1ProtectedSpliceEdge at hp0
        dsimp only at hp0
        have hbad := hp0.1
        rw [hJf] at hbad
        cases hbad
      · by_cases hrxe : ring.rightNeighbor x = e
        · have hp0 := hsafe.1 x hd0
          unfold R1ProtectedSpliceEdge at hp0
          dsimp only at hp0
          rw [hrxe] at hp0
          exact (predFalse_not_ownedRight (C e) hLe hLp hp0.2).elim
        · have hrxj : ring.rightNeighbor x ≠ ring.rightNeighbor e := by
            intro h
            exact hxe (rightNeighbor_injective ring h)
          have hDx : D x = C x :=
            r1_step_other hpsi hwidth hle ring C e x hxe hxj
          have hDr : D (ring.rightNeighbor x) =
              C (ring.rightNeighbor x) :=
            r1_step_other hpsi hwidth hle ring C e
              (ring.rightNeighbor x) hrxe hrxj
          have hp0 := hsafe.1 x hd0
          unfold R1ProtectedSpliceEdge at hp0 ⊢
          dsimp only at hp0 ⊢
          rw [hDx, hDr]
          exact hp0
  · intro i hp
    by_cases hie : i = e
    · subst i
      rw [hE, hLp] at hp
      cases hp
    · by_cases hij : i = ring.rightNeighbor e
      · subst i
        rw [hJ] at hp
        change false = true at hp
        cases hp
      · have hDi : D i = C i :=
          r1_step_other hpsi hwidth hle ring C e i hie hij
        have hp0 : (C i).repairPending = true := by
          rw [hDi] at hp
          exact hp
        have hb := hsafe.2 i hp0
        have hrE : ring.rightNeighbor i ≠ e := by
          intro h
          have hf := hb.2.1
          rw [h, hLe] at hf
          cases hf
        have hrJ : ring.rightNeighbor i ≠ ring.rightNeighbor e := by
          intro h
          exact hie (rightNeighbor_injective ring h)
        have hDr : D (ring.rightNeighbor i) =
            C (ring.rightNeighbor i) :=
          r1_step_other hpsi hwidth hle ring C e
            (ring.rightNeighbor i) hrE hrJ
        rw [hDi, hDr]
        exact hb


theorem moveSeekHold_preserves_spliceSafeR1
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (ring : DirectedRing n) (C : R1Config n psi kappa tau) (e : Fin n)
    (hsafe : SpliceSafeR1 hpsi ring C)
    (hg : MoveSeekHoldGuard (C e) (C (ring.rightNeighbor e))) :
    SpliceSafeR1 hpsi ring (step hpsi hwidth hle ring C e) := by
  have hrow := row_of_moveSeekHold hpsi hwidth hle
    (C e) (C (ring.rightNeighbor e)) hg
  have hne := moveSeekHold_ne ring C e hg
  have hcfg : step hpsi hwidth hle ring C e = C := by
    funext i
    by_cases hi : i = e
    · subst i
      exact step_left_of_row hpsi hwidth hle ring C e
        (C e, C (ring.rightNeighbor e)) hrow
    · by_cases hj : i = ring.rightNeighbor e
      · subst i
        exact step_right_of_row hpsi hwidth hle ring C e
          (C e, C (ring.rightNeighbor e)) hrow hne
      · exact r1_step_other hpsi hwidth hle ring C e i hi hj
  rw [hcfg]
  exact hsafe


theorem moveAcquire_preserves_spliceSafeR1
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (ring : DirectedRing n) (C : R1Config n psi kappa tau) (e : Fin n)
    (hsafe : SpliceSafeR1 hpsi ring C)
    (hg : MoveAcquireGuard (C e) (C (ring.rightNeighbor e))) :
    SpliceSafeR1 hpsi ring (step hpsi hwidth hle ring C e) := by
  let D := step hpsi hwidth hle ring C e
  change SpliceSafeR1 hpsi ring D
  have hrow := row_of_moveAcquire hpsi hwidth hle
    (C e) (C (ring.rightNeighbor e)) hg
  have hne := moveAcquire_ne ring C e hg
  have hE : D e = setControl (C e) .predecessorArmed true :=
    step_left_of_row hpsi hwidth hle ring C e
      (setControl (C e) .predecessorArmed true,
        setControl (C (ring.rightNeighbor e)) .front false) hrow
  have hJ : D (ring.rightNeighbor e) =
      setControl (C (ring.rightNeighbor e)) .front false :=
    step_right_of_row hpsi hwidth hle ring C e
      (setControl (C e) .predecessorArmed true,
        setControl (C (ring.rightNeighbor e)) .front false) hrow hne
  have hphys : forall i, physical (D i) = physical (C i) :=
    physical_frame_of_row hpsi hwidth hle ring C e
      (setControl (C e) .predecessorArmed true,
        setControl (C (ring.rightNeighbor e)) .front false)
      hrow hne (by rfl) (by rfl)
  rcases hg with ⟨hEv, hEp, hEfollower, hJp, hJshape⟩
  have hJnotPred : role (C (ring.rightNeighbor e)) ≠ .predecessorArmed := by
    intro hpred
    rcases hJshape with hnone | hfront
    · rw [hnone] at hpred
      cases hpred
    · rw [hfront] at hpred
      cases hpred
  constructor
  · intro x hd
    have hd0 := (danger_congr_of_physical hpsi ring C D hphys x).1 hd
    by_cases hxe : x = e
    · subst x
      unfold R1ProtectedSpliceEdge
      dsimp only
      rw [hE, hJ]
      exact ⟨rfl, Or.inl ⟨rfl, rfl⟩⟩
    · by_cases hxj : x = ring.rightNeighbor e
      · subst x
        have hp0 := hsafe.1 (ring.rightNeighbor e) hd0
        unfold R1ProtectedSpliceEdge at hp0
        dsimp only at hp0
        exact (hJnotPred hp0.1).elim
      · by_cases hrxe : ring.rightNeighbor x = e
        · have hp0 := hsafe.1 x hd0
          unfold R1ProtectedSpliceEdge at hp0
          dsimp only at hp0
          have hDx : D x = C x :=
            r1_step_other hpsi hwidth hle ring C e x hxe hxj
          unfold R1ProtectedSpliceEdge
          dsimp only
          rw [hDx, hrxe, hE]
          exact ⟨hp0.1, Or.inr (Or.inr ⟨rfl, rfl⟩)⟩
        · have hrxj : ring.rightNeighbor x ≠ ring.rightNeighbor e := by
            intro h
            exact hxe (rightNeighbor_injective ring h)
          have hDx : D x = C x :=
            r1_step_other hpsi hwidth hle ring C e x hxe hxj
          have hDr : D (ring.rightNeighbor x) =
              C (ring.rightNeighbor x) :=
            r1_step_other hpsi hwidth hle ring C e
              (ring.rightNeighbor x) hrxe hrxj
          have hp0 := hsafe.1 x hd0
          unfold R1ProtectedSpliceEdge at hp0 ⊢
          dsimp only at hp0 ⊢
          rw [hDx, hDr]
          exact hp0
  · intro i hp
    by_cases hie : i = e
    · subst i
      rw [hE, hJ]
      exact ⟨rfl, rfl, rfl⟩
    · by_cases hij : i = ring.rightNeighbor e
      · subst i
        rw [hJ] at hp
        change false = true at hp
        cases hp
      · have hDi : D i = C i :=
          r1_step_other hpsi hwidth hle ring C e i hie hij
        have hp0 : (C i).repairPending = true := by
          rw [hDi] at hp
          exact hp
        have hb := hsafe.2 i hp0
        have hrE : ring.rightNeighbor i ≠ e := by
          intro h
          have hf := hb.2.1
          rw [h, hEv] at hf
          cases hf
        have hrJ : ring.rightNeighbor i ≠ ring.rightNeighbor e := by
          intro h
          exact hie (rightNeighbor_injective ring h)
        have hDr : D (ring.rightNeighbor i) =
            C (ring.rightNeighbor i) :=
          r1_step_other hpsi hwidth hle ring C e
            (ring.rightNeighbor i) hrE hrJ
        rw [hDi, hDr]
        exact hb


def ControlClear (u : R1AgentState psi kappa tau) : Prop :=
  role u = .none /\ u.repairPending = false


def NoSpliceGuard
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (l r : R1AgentState psi kappa tau) : Prop :=
  ¬ ArmAGuard hpsi hwidth hle l r /\
  ¬ ArmBGuard l r /\
  ¬ DeleteGuard hpsi hwidth hle l r /\
  ¬ PendingHoldGuard hpsi hwidth hle l r /\
  ¬ PendingAbortGuard hpsi hwidth hle l r /\
  ¬ MoveCommitGuard l r /\
  ¬ MoveStopGuard hpsi l r /\
  ¬ MoveSeekGuard hpsi l r /\
  ¬ MoveSeekHoldGuard l r /\
  ¬ MoveAcquireGuard l r


private theorem row_of_clear_noSpliceGuard
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (l r : R1AgentState psi kappa tau)
    (hl : ControlClear l) (hr : ControlClear r)
    (hno : NoSpliceGuard hpsi hwidth hle l r) :
    row hpsi hwidth hle l r = ordinaryRow hpsi hwidth hle l r := by
  rcases hl with ⟨hlr, hlp⟩
  rcases hr with ⟨hrr, hrp⟩
  rcases hno with ⟨ha, hb, hd, hph, hpa, hmc, hms, hmseek, hmhold, hma⟩
  simp [row, ha, hb, hd, hph, hpa, hmc, hms, hmseek, hmhold, hma,
    hlr, hlp, hrr, hrp]


theorem ordinary_row_frame
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (ring : DirectedRing n) (C : R1Config n psi kappa tau) (e : Fin n)
    (hl : ControlClear (C e))
    (hr : ControlClear (C (ring.rightNeighbor e)))
    (hno : NoSpliceGuard hpsi hwidth hle
      (C e) (C (ring.rightNeighbor e))) :
    (fun i => physical (step hpsi hwidth hle ring C e i)) =
        BirthShortDoneTerminalConsumer.step
          hpsi hwidth hle ring (fun i => physical (C i)) e /\
      (forall i,
        role (step hpsi hwidth hle ring C e i) = role (C i) /\
        (step hpsi hwidth hle ring C e i).repairPending =
          (C i).repairPending) := by
  have hrow := row_of_clear_noSpliceGuard hpsi hwidth hle
    (C e) (C (ring.rightNeighbor e)) hl hr hno
  constructor
  · funext i
    by_cases hi : i = e
    · subst i
      simp [step, hrow, ordinaryRow, physical, setPhysical,
        BirthShortDoneTerminalConsumer.step, PopulationProtocol.step,
        BirthShortDoneTerminalConsumer.protocol]
    · by_cases hj : i = ring.rightNeighbor e
      · subst i
        simp [step, hrow, ordinaryRow, physical, setPhysical,
          BirthShortDoneTerminalConsumer.step, PopulationProtocol.step,
          BirthShortDoneTerminalConsumer.protocol, hi]
      · rw [r1_step_other hpsi hwidth hle ring C e i hi hj]
        rw [BirthShortDoneTerminalConsumer.step_other
          hpsi hwidth hle ring (fun i => physical (C i)) e i hi hj]
  · intro i
    by_cases hi : i = e
    · subst i
      simp [step, hrow, ordinaryRow, setPhysical, role]
    · by_cases hj : i = ring.rightNeighbor e
      · subst i
        simp [step, hrow, ordinaryRow, setPhysical, role, hi]
      · rw [r1_step_other hpsi hwidth hle ring C e i hi hj]
        exact ⟨rfl, rfl⟩


end B9SpliceR2MoveFrame


#print axioms B9SpliceR2MoveFrame.moveCommit_preserves_spliceSafeR1
#print axioms B9SpliceR2MoveFrame.moveStop_preserves_spliceSafeR1
#print axioms B9SpliceR2MoveFrame.moveSeek_preserves_spliceSafeR1
#print axioms B9SpliceR2MoveFrame.moveSeekHold_preserves_spliceSafeR1
#print axioms B9SpliceR2MoveFrame.moveAcquire_preserves_spliceSafeR1
#print axioms B9SpliceR2MoveFrame.ordinary_row_frame
