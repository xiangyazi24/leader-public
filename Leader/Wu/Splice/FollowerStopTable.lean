import Leader.Wu.Splice.MoveLeaseStopCounterexample
import Leader.Wu.Birth.ShortDoneParameterChoice

set_option autoImplicit false
set_option Elab.async false
set_option pp.structureInstances false

namespace B9SpliceControllerR1TableV4

open PPLL PPLLDomain PPLLResearchFormulation
  PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
  PPLLLeaderCreationCleanupRepair
open BirthSigMoveDisposalRepair
  BirthShortDoneTerminalBirthSources
open Q11593SpliceControllerDesign
open B9SpliceControllerR1Table
open B9SpliceControllerR1TableV2
open B9SpliceControllerR1TableV3
open B9SpliceControllerV3Safety

variable {n psi width kappa tau : Nat}

abbrev R1AgentStateV4 (psi kappa tau : Nat) :=
  R1AgentStateV3 psi kappa tau

abbrev R1ConfigV4 (n psi kappa tau : Nat) :=
  R1ConfigV3 n psi kappa tau

private instance q11674DecidableMoveStopGuardV3
    {psi kappa tau : Nat}
    (hpsi : 0 < psi)
    (l r : R1AgentStateV4 psi kappa tau) :
    Decidable (MoveStopGuardV3 hpsi l r) := by
  unfold MoveStopGuardV3 ReservedFrontHoldGuard LocalPreparedBarrier
  dsimp only
  unfold isBarrier
  infer_instance

/-- V4 keeps the V3 STOP guard.  The only change is its write:
a surviving leader front is disposable, but a follower front remains reserved
because its outgoing edge may use `front,true` as its sole safety certificate. -/
def moveStopWriteV4
    (l r : R1AgentStateV4 psi kappa tau) :
    R1AgentStateV4 psi kappa tau × R1AgentStateV4 psi kappa tau :=
  if r.splice.base.core.core.leader = true then
    (clearControl l, clearControl r)
  else
    (clearControl l, r)

/-- V4 is literally V3 except when the V3 MOVE-STOP guard is selected. -/
def rowV4
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (l r : R1AgentStateV4 psi kappa tau) :
    R1AgentStateV4 psi kappa tau × R1AgentStateV4 psi kappa tau :=
  if MoveStopGuardV3 hpsi l r then
    moveStopWriteV4 l r
  else
    rowV3 hpsi hwidth hle l r

theorem rowV4_eq_rowV3_of_not_moveStop
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (l r : R1AgentStateV4 psi kappa tau)
    (h : ¬ MoveStopGuardV3 hpsi l r) :
    rowV4 hpsi hwidth hle l r = rowV3 hpsi hwidth hle l r := by
  simp [rowV4, h]

private theorem rowV4_of_moveStop
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (l r : R1AgentStateV4 psi kappa tau)
    (h : MoveStopGuardV3 hpsi l r) :
    rowV4 hpsi hwidth hle l r = moveStopWriteV4 l r := by
  simp [rowV4, h]

/-- Ring lift, with the same one-site fail-closed convention as V3. -/
def stepV4
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (ring : DirectedRing n) (C : R1ConfigV4 n psi kappa tau)
    (e : Fin n) : R1ConfigV4 n psi kappa tau :=
  let j := ring.rightNeighbor e
  if j = e then C
  else
    let q := rowV4 hpsi hwidth hle (C e) (C j)
    fun i =>
      if i = e then q.1
      else if i = j then q.2
      else C i

/-- No state is added in V4. -/
def controllerStateFactorV4 : Nat := controllerStateFactorV3

theorem controllerStateFactorV4_eq : controllerStateFactorV4 = 8 := by
  decide

/-! ## Structural helpers for MOVE-STOP preservation -/

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

@[simp] private theorem physical_clearControl
    (u : R1AgentStateV4 psi kappa tau) :
    physical (clearControl u) = physical u := rfl

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

private theorem preparedR1_leader_eq_local
    (hpsi : 0 < psi) (u : R1AgentStateV4 psi kappa tau) :
    (preparedR1 hpsi u).core.leader =
      u.splice.base.core.core.leader := by
  unfold preparedR1 prepared prepareExpiringDisposal
  rw [erase_prepareBoundedDisposal hpsi u.splice.base.core]
  rw [normalizeDeletion_leader_eq_local,
    prepareDisposal_leader_eq_local]
  rfl

private theorem preparedR1_eq_of_physical_eq
    (hpsi : 0 < psi)
    (a b : R1AgentStateV4 psi kappa tau)
    (h : physical a = physical b) :
    preparedR1 hpsi a = preparedR1 hpsi b := by
  change a.splice.base = b.splice.base at h
  unfold preparedR1 prepared
  rw [h]

private theorem danger_congr_at
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (C D : R1ConfigV4 n psi kappa tau) (e : Fin n)
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

private theorem localPreparedBarrier_of_danger
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (C : R1ConfigV4 n psi kappa tau) (e : Fin n)
    (h : PreparedDangerAt hpsi ring C e) :
    LocalPreparedBarrier hpsi (C e) (C (ring.rightNeighbor e)) := by
  simpa [PreparedBarrierAt, LocalPreparedBarrier,
    projectSpliceConfig, preparedR1] using h.2

private theorem moveStop_ne
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (C : R1ConfigV4 n psi kappa tau) (e : Fin n)
    (h : MoveStopGuardV3 hpsi (C e) (C (ring.rightNeighbor e))) :
    ring.rightNeighbor e ≠ e := by
  intro hs
  have h' := h
  rw [hs] at h'
  rcases h' with ⟨hp, _, hf, _⟩
  have hfr := hf.1
  rw [hp] at hfr
  cases hfr

private theorem stepV4_other
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (ring : DirectedRing n) (C : R1ConfigV4 n psi kappa tau)
    (e i : Fin n)
    (hne : ring.rightNeighbor e ≠ e)
    (hi : i ≠ e) (hj : i ≠ ring.rightNeighbor e) :
    stepV4 hpsi hwidth hle ring C e i = C i := by
  simp [stepV4, hne, hi, hj]

/-- If a safe pre-state has a danger entering the left endpoint of a STOP,
that danger cannot have been protected by the stopping predecessor itself:
that endpoint is `predecessorArmed,false`.  Therefore the left endpoint of the
danger is already a reserved front, and clearing the STOP predecessor cannot
hurt it. -/
private theorem protected_incoming_to_stop_left
    (ring : DirectedRing n) (C : R1ConfigV4 n psi kappa tau)
    (x e : Fin n)
    (hp : R1ProtectedSpliceEdgeV3 ring C x)
    (hre : ring.rightNeighbor x = e)
    (hLe : role (C e) = .predecessorArmed)
    (hLp : (C e).repairPending = false) :
    ReservedFrontHoldGuard (C x) := by
  unfold R1ProtectedSpliceEdgeV3 at hp
  dsimp only at hp
  rw [hre] at hp
  rcases hp with hres | hright | hleft
  · exact hres
  · have hb := hright.2
    rw [hLp] at hb
    cases hb
  · rcases hleft with ⟨_, _, hshape⟩
    rcases hshape with hres | hv | hpend
    · have hf := hres.1
      rw [hLe] at hf
      cases hf
    · have hf := hv.1
      rw [hLe] at hf
      cases hf
    · have hb := hpend.2
      rw [hLp] at hb
      cases hb

/-! ## MOVE-STOP preservation -/

/-- V4 MOVE-STOP preserves the unchanged V3 safety predicate.

If the stopping front is a leader, clearing it cannot expose a prepared danger
starting there.  If it is a follower, V4 leaves `front,true` untouched, so any
outgoing danger remains protected by the first V3 protection disjunct. -/
theorem moveStop_preserves_spliceSafeR1V3
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (ring : DirectedRing n) (C : R1ConfigV4 n psi kappa tau) (e : Fin n)
    (hsafe : SpliceSafeR1V3 hpsi ring C)
    (hg : MoveStopGuardV3 hpsi
      (C e) (C (ring.rightNeighbor e))) :
    SpliceSafeR1V3 hpsi ring
      (stepV4 hpsi hwidth hle ring C e) := by
  let D := stepV4 hpsi hwidth hle ring C e
  change SpliceSafeR1V3 hpsi ring D
  have hne := moveStop_ne hpsi ring C e hg
  have hgSaved := hg
  rcases hg with ⟨hLe, hLp, hJres, hstop⟩
  rcases hJres with ⟨hJfront, hJpending⟩
  have hE : D e = clearControl (C e) := by
    dsimp [D]
    by_cases hlead :
        (C (ring.rightNeighbor e)).splice.base.core.core.leader = true
    · simp [stepV4, hne, rowV4, moveStopWriteV4, hgSaved, hlead]
    · simp [stepV4, hne, rowV4, moveStopWriteV4, hgSaved, hlead]
  have hJclear :
      (C (ring.rightNeighbor e)).splice.base.core.core.leader = true ->
        D (ring.rightNeighbor e) =
          clearControl (C (ring.rightNeighbor e)) := by
    intro hlead
    dsimp [D]
    simp [stepV4, hne, rowV4, moveStopWriteV4, hgSaved, hlead]
  have hJkeep :
      (C (ring.rightNeighbor e)).splice.base.core.core.leader ≠ true ->
        D (ring.rightNeighbor e) = C (ring.rightNeighbor e) := by
    intro hlead
    dsimp [D]
    simp [stepV4, hne, rowV4, moveStopWriteV4, hgSaved, hlead]
  have hphys : forall i, physical (D i) = physical (C i) := by
    intro i
    by_cases hi : i = e
    · subst i
      rw [hE]
      rfl
    · by_cases hj : i = ring.rightNeighbor e
      · subst i
        by_cases hlead :
            (C (ring.rightNeighbor e)).splice.base.core.core.leader = true
        · rw [hJclear hlead]
          rfl
        · rw [hJkeep hlead]
      · exact congrArg physical (stepV4_other hpsi hwidth hle ring C e i hne hi hj)
  constructor
  · intro x hd
    have hd0 :=
      (danger_congr_at hpsi ring C D x
        (hphys x) (hphys (ring.rightNeighbor x))).1 hd
    by_cases hxe : x = e
    · subst x
      exact (hstop
        (localPreparedBarrier_of_danger hpsi ring C e hd0)).elim
    · by_cases hxj : x = ring.rightNeighbor e
      · subst x
        by_cases hlead :
            (C (ring.rightNeighbor e)).splice.base.core.core.leader = true
        · have hptrue :
              (preparedR1 hpsi (C (ring.rightNeighbor e))).core.leader = true :=
            (preparedR1_leader_eq_local hpsi
              (C (ring.rightNeighbor e))).trans hlead
          have hbad : (true : Bool) = false :=
            hptrue.symm.trans hd0.1
          cases hbad
        · have hJ := hJkeep hlead
          unfold R1ProtectedSpliceEdgeV3
          dsimp only
          rw [hJ]
          exact Or.inl ⟨hJfront, hJpending⟩
      · by_cases hrxe : ring.rightNeighbor x = e
        · have hp0 := hsafe.1 x hd0
          have hres := protected_incoming_to_stop_left
            ring C x e hp0 hrxe hLe hLp
          have hDx : D x = C x := by
            exact stepV4_other hpsi hwidth hle ring C e x
              hne hxe hxj
          unfold R1ProtectedSpliceEdgeV3
          dsimp only
          rw [hDx]
          exact Or.inl hres
        · have hrxj :
              ring.rightNeighbor x ≠ ring.rightNeighbor e := by
            intro h
            exact hxe (rightNeighbor_injective ring h)
          have hDx : D x = C x := by
            exact stepV4_other hpsi hwidth hle ring C e x
              hne hxe hxj
          have hDr :
              D (ring.rightNeighbor x) = C (ring.rightNeighbor x) := by
            exact stepV4_other hpsi hwidth hle ring C e
              (ring.rightNeighbor x) hne hrxe hrxj
          have hp0 := hsafe.1 x hd0
          unfold R1ProtectedSpliceEdgeV3 at hp0 ⊢
          dsimp only at hp0 ⊢
          rw [hDx, hDr]
          exact hp0
  · intro i hpred hpending
    by_cases hie : i = e
    · subst i
      rw [hE] at hpred
      have hbad : SpliceRole.none = SpliceRole.predecessorArmed := by
        simpa [clearControl, setControl, role] using hpred
      cases hbad
    · by_cases hij : i = ring.rightNeighbor e
      · subst i
        by_cases hlead :
            (C (ring.rightNeighbor e)).splice.base.core.core.leader = true
        · have hJ := hJclear hlead
          rw [hJ] at hpred
          have hbad : SpliceRole.none = SpliceRole.predecessorArmed := by
            simpa [clearControl, setControl, role] using hpred
          cases hbad
        · have hJ := hJkeep hlead
          rw [hJ] at hpred
          have hbad : SpliceRole.front = SpliceRole.predecessorArmed :=
            hJfront.symm.trans hpred
          cases hbad
      · have hDi : D i = C i := by
          exact stepV4_other hpsi hwidth hle ring C e i
            hne hie hij
        have hpred0 := hpred
        rw [hDi] at hpred0
        have hp0 := hpending
        rw [hDi] at hp0
        have hb := hsafe.2 i hpred0 hp0
        have hrE : ring.rightNeighbor i ≠ e := by
          intro h
          have hf := hb.1
          rw [h, hLe] at hf
          cases hf
        have hrJ :
            ring.rightNeighbor i ≠ ring.rightNeighbor e := by
          intro h
          exact hie (rightNeighbor_injective ring h)
        have hDr :
            D (ring.rightNeighbor i) = C (ring.rightNeighbor i) := by
          exact stepV4_other hpsi hwidth hle ring C e
            (ring.rightNeighbor i) hne hrE hrJ
        rw [hDr]
        exact hb

/-! ## Closed decidability support -/

private instance q11674DecidablePreparedDangerAtLocal
    {n psi kappa tau : Nat}
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (C : R1ConfigV4 n psi kappa tau) (e : Fin n) :
    Decidable (PreparedDangerAt hpsi ring C e) := by
  unfold PreparedDangerAt PreparedBarrierAt
  dsimp only
  unfold isBarrier
  infer_instance

private instance q11674DecidableR1ProtectedSpliceEdgeV3Local
    {n psi kappa tau : Nat}
    (ring : DirectedRing n) (C : R1ConfigV4 n psi kappa tau)
    (e : Fin n) :
    Decidable (R1ProtectedSpliceEdgeV3 ring C e) := by
  unfold R1ProtectedSpliceEdgeV3 ReservedFrontHoldGuard
  dsimp only
  infer_instance

private instance q11674DecidableSpliceSafeR1V3Local
    {n psi kappa tau : Nat}
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (C : R1ConfigV4 n psi kappa tau) :
    Decidable (SpliceSafeR1V3 hpsi ring C) := by
  unfold SpliceSafeR1V3
  infer_instance

private instance q11674DecidablePPrimeBarrierBirthGuardLocal
    {psi : Nat} (hpsi : 0 < psi)
    (l r : AuthorizedAgentState psi) :
    Decidable (PPrimeBarrierBirthGuard hpsi l r) := by
  unfold PPrimeBarrierBirthGuard
  unfold isBarrier
  infer_instance

private instance q11674DecidableR1AmendedPPrimeAtV3Local
    {n psi kappa tau : Nat}
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (C : R1ConfigV4 n psi kappa tau) (e : Fin n) :
    Decidable (R1AmendedPPrimeAtV3 hpsi ring C e) := by
  unfold R1AmendedPPrimeAtV3
  dsimp only
  infer_instance

private instance q11674DecidableR1SourceFreeV3Local
    {n psi kappa tau : Nat}
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (C : R1ConfigV4 n psi kappa tau) :
    Decidable (R1SourceFreeV3 hpsi ring C) := by
  unfold R1SourceFreeV3
  infer_instance

private instance q11674DecidableLeaderlessV3Local
    {n : Nat} (C : R1ConfigV4 n 2 0 0) :
    Decidable (LeaderlessV3 C) := by
  unfold LeaderlessV3
  infer_instance

private instance q11674DecidableRolesClearV3Local
    {n : Nat} (C : R1ConfigV4 n 2 0 0) :
    Decidable (RolesClearV3 C) := by
  unfold RolesClearV3
  infer_instance

/-! ## MOVE-STOP witness, repaired in one V4 STOP -/

private theorem hOne : 0 < 1 := by decide
private theorem hTwo : 0 < 2 := by decide
private theorem hThree : 0 < 3 := by decide
private theorem hFour : 0 < 4 := by decide
private theorem hFive : 0 < 5 := by decide
private theorem hOneThree : 1 <= 3 := by decide
private theorem hTwoLe : 2 <= 2 := by decide
private theorem hTwoThree : 2 <= 3 := by decide

private def ring2 : DirectedRing 2 := ⟨hTwo⟩
private def ring3 : DirectedRing 3 := ⟨hThree⟩
private def ring4 : DirectedRing 4 := ⟨hFour⟩
private def ring5 : DirectedRing 5 := ⟨hFive⟩

private def raw3
    (leader : Bool) (label : Fin 3) : AgentState 3 :=
  { leader := leader
    probe := false
    phase := false
    bit := false
    wait := true
    state := .none
    path := .bot
    reset := false
    carry := false
    count := 0
    label := label
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
    shield := true
    write_state := .none
    write := .none
    last := false
    last_set := false
    last_unset := false
    b_carry := false
    gen_ws := false
    ws_echo := false
    signal_ws := false }

private theorem raw3_domain0 (leader : Bool) (label : Fin 3) :
    (raw3 leader label).inProtocolDomain 0 := by
  simp [raw3, AgentState.inProtocolDomain]

private theorem raw3_domain3 (leader : Bool) (label : Fin 3) :
    (raw3 leader label).inProtocolDomain 3 := by
  simp [raw3, AgentState.inProtocolDomain]

private def cell3_0
    (leader : Bool) (label : Fin 3) : ExpiringAgentState 3 0 0 :=
  ⟨⟨BoundedAgentState.ofDomain
      (raw3 leader label) (raw3_domain0 leader label), false⟩, 0⟩

private def x3_0
    (leader : Bool) (label : Fin 3)
    (r : SpliceRole) (pending : Bool) : R1AgentStateV4 3 0 0 :=
  { splice :=
      { base := cell3_0 leader label
        spliceRole := r }
    repairPending := pending }

private def q11668Start2V4 : R1ConfigV4 2 3 0 0 := fun i =>
  if i = 0 then x3_0 false 0 .predecessorArmed false
  else x3_0 false 1 .front true

private def q11668After2V4 : R1ConfigV4 2 3 0 0 :=
  stepV4 hThree hOne hOneThree ring2 q11668Start2V4 (0 : Fin 2)

theorem q11668_moveStop_repaired_v4 :
    SpliceSafeR1V3 hThree ring2 q11668Start2V4 /\
    MoveStopGuardV3 hThree
      (q11668Start2V4 (0 : Fin 2))
      (q11668Start2V4 (ring2.rightNeighbor (0 : Fin 2))) /\
    role (q11668After2V4 (0 : Fin 2)) = .none /\
    (q11668After2V4 (0 : Fin 2)).repairPending = false /\
    ReservedFrontHoldGuard (q11668After2V4 (1 : Fin 2)) /\
    PreparedDangerAt hThree ring2 q11668After2V4 (1 : Fin 2) /\
    R1ProtectedSpliceEdgeV3 ring2 q11668After2V4 (1 : Fin 2) /\
    SpliceSafeR1V3 hThree ring2 q11668After2V4 := by
  decide

/-! ## Same failure at the protocol's first Local3-admissible parameters -/

private def cell3_3_48
    (leader : Bool) (label : Fin 3) : ExpiringAgentState 3 3 48 :=
  ⟨⟨BoundedAgentState.ofDomain
      (raw3 leader label) (raw3_domain3 leader label), false⟩, 0⟩

private def x3_3_48
    (leader : Bool) (label : Fin 3)
    (r : SpliceRole) (pending : Bool) : R1AgentStateV4 3 3 48 :=
  { splice :=
      { base := cell3_3_48 leader label
        spliceRole := r }
    repairPending := pending }

/-- At n=4 the feasibility audit gives psi=3, width=2, kappa=3, tau=48.
Sites 0,1,2 reproduce the STOP exposure; site 3 is a leader, making every
other edge irrelevant to `PreparedDangerAt`. -/
private def protocolStopStart4 : R1ConfigV4 4 3 3 48 := fun i =>
  if i = 0 then x3_3_48 false 0 .predecessorArmed false
  else if i = 1 then x3_3_48 false 1 .front true
  else if i = 2 then x3_3_48 false 1 .none false
  else x3_3_48 true 0 .none false

private def protocolStopAfter4V3 : R1ConfigV4 4 3 3 48 :=
  stepV3 hThree hTwo hTwoThree ring4 protocolStopStart4 (0 : Fin 4)

private def protocolStopAfter4V4 : R1ConfigV4 4 3 3 48 :=
  stepV4 hThree hTwo hTwoThree ring4 protocolStopStart4 (0 : Fin 4)

theorem moveStop_failure_at_protocol_parameters_n4 :
    Q11497FeasibilityAudit.psiChoice 4 = 3 /\
    Q11497FeasibilityAudit.widthChoice = 2 /\
    Q11497FeasibilityAudit.kappaChoice 4 = 3 /\
    Q11497FeasibilityAudit.tauChoice 4 = 48 /\
    SpliceSafeR1V3 hThree ring4 protocolStopStart4 /\
    MoveStopGuardV3 hThree
      (protocolStopStart4 (0 : Fin 4))
      (protocolStopStart4 (1 : Fin 4)) /\
    PreparedDangerAt hThree ring4 protocolStopAfter4V3 (1 : Fin 4) /\
    ¬ R1ProtectedSpliceEdgeV3 ring4 protocolStopAfter4V3 (1 : Fin 4) /\
    ¬ SpliceSafeR1V3 hThree ring4 protocolStopAfter4V3 := by
  decide

theorem moveStop_protocol_parameters_repaired_v4 :
    SpliceSafeR1V3 hThree ring4 protocolStopStart4 /\
    SpliceSafeR1V3 hThree ring4 protocolStopAfter4V4 /\
    ReservedFrontHoldGuard (protocolStopAfter4V4 (1 : Fin 4)) /\
    PreparedDangerAt hThree ring4 protocolStopAfter4V4 (1 : Fin 4) /\
    R1ProtectedSpliceEdgeV3 ring4 protocolStopAfter4V4 (1 : Fin 4) := by
  decide

/-! ## V4 replay harness at psi=2 -/

def serveV4 {n : Nat}
    (ring : DirectedRing n)
    (C : R1ConfigV4 n 2 0 0) (e : Fin n) :
    R1ConfigV4 n 2 0 0 :=
  stepV4 hTwo hTwo hTwoLe ring C e

def runV4 {n : Nat}
    (ring : DirectedRing n)
    (C : R1ConfigV4 n 2 0 0)
    (word : List (Fin n)) : R1ConfigV4 n 2 0 0 :=
  List.foldl (fun D e => serveV4 ring D e) C word

def safeAlongV4 {n : Nat} (ring : DirectedRing n) :
    R1ConfigV4 n 2 0 0 -> List (Fin n) -> Bool
  | C, [] => decide (SpliceSafeR1V3 hTwo ring C)
  | C, e :: es =>
      decide (SpliceSafeR1V3 hTwo ring C) &&
        safeAlongV4 ring (serveV4 ring C e) es

def sourceFreeAlongV4 {n : Nat} (ring : DirectedRing n) :
    R1ConfigV4 n 2 0 0 -> List (Fin n) -> Bool
  | C, [] => decide (R1SourceFreeV3 hTwo ring C)
  | C, e :: es =>
      decide (R1SourceFreeV3 hTwo ring C) &&
        sourceFreeAlongV4 ring (serveV4 ring C e) es

/-! ### Three leaderless drain reruns -/

def loop3DrainPrefixV4 : List (Fin 3) := [0, 1, 0]

theorem leaderless_cycle3_v4_killed :
    LeaderlessV3 B9SpliceR2AttackRerun.loop3Start /\
    RolesClearV3
      (runV4 ring3 B9SpliceR2AttackRerun.loop3Start loop3DrainPrefixV4) /\
    role (serveV4 ring3 B9SpliceR2AttackRerun.loop3Start (0 : Fin 3)
      (1 : Fin 3)) = .none := by
  decide

def loop4DrainWordV4 : List (Fin 4) := [0, 2, 0, 2]

def loop4OldPrefixV4 : R1ConfigV4 4 2 0 0 :=
  runV4 ring4 B9SpliceR2AttackRerun.loop4Start [(0 : Fin 4), (2 : Fin 4)]

theorem leaderless_deadlock4_v4_killed :
    LeaderlessV3 B9SpliceR2AttackRerun.loop4Start /\
    role (loop4OldPrefixV4 (0 : Fin 4)) = .predecessorArmed /\
    role (serveV4 ring4 loop4OldPrefixV4 (0 : Fin 4) (0 : Fin 4)) = .none /\
    RolesClearV3
      (runV4 ring4 B9SpliceR2AttackRerun.loop4Start loop4DrainWordV4) := by
  decide

def loop5DrainPrefixV4 : List (Fin 5) := [0, 1, 0]

theorem leaderless_cycle5_v4_killed :
    LeaderlessV3 B9SpliceR2AttackRerun.loop5Start /\
    RolesClearV3
      (runV4 ring5 B9SpliceR2AttackRerun.loop5Start loop5DrainPrefixV4) /\
    role (serveV4 ring5 B9SpliceR2AttackRerun.loop5Start (0 : Fin 5)
      (1 : Fin 5)) = .none := by
  decide

/-! ### Four repelled-attack reruns -/

def q11592Armed4V4 : R1ConfigV4 4 2 0 0 :=
  serveV4 ring4 B9SpliceR2AttackRerun.q11592Start4 (1 : Fin 4)

def q11592Replay4V4 : R1ConfigV4 4 2 0 0 :=
  serveV4 ring4 q11592Armed4V4 (1 : Fin 4)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
theorem q11592_pending_hold_replay_v4 :
    role (q11592Armed4V4 (1 : Fin 4)) = .victimArmed /\
    (q11592Armed4V4 (1 : Fin 4)).repairPending = false /\
    role (q11592Armed4V4 (2 : Fin 4)) = .front /\
    (q11592Armed4V4 (2 : Fin 4)).repairPending = false /\
    PendingHoldGuard hTwo hTwo hTwoLe
      (q11592Armed4V4 (1 : Fin 4))
      (q11592Armed4V4 (2 : Fin 4)) /\
    (forall i, q11592Replay4V4 i = q11592Armed4V4 i) := by
  decide

def followerOldFirstV4 : R1ConfigV4 5 2 0 0 :=
  serveV4 ring5 B9SpliceR2AttackRerun.followerStart5 (0 : Fin 5)

theorem follower_old_unreserved_front_does_not_move_v4 :
    role (followerOldFirstV4 (0 : Fin 5)) = .predecessorArmed /\
    role (followerOldFirstV4 (1 : Fin 5)) = .none := by
  decide

def followerAfter5V4 : R1ConfigV4 5 2 0 0 :=
  runV4 ring5
    B9SpliceControllerR1TableV3.followerStart5V3
    B9SpliceControllerR1TableV3.followerWord5V3

theorem follower_anchor_authenticated_chain_safe_v4 :
    safeAlongV4 ring5
      B9SpliceControllerR1TableV3.followerStart5V3
      B9SpliceControllerR1TableV3.followerWord5V3 = true /\
    sourceFreeAlongV4 ring5
      B9SpliceControllerR1TableV3.followerStart5V3
      B9SpliceControllerR1TableV3.followerWord5V3 = true /\
    role (followerAfter5V4 (2 : Fin 5)) = .predecessorArmed /\
    (followerAfter5V4 (2 : Fin 5)).repairPending = false /\
    role (followerAfter5V4 (3 : Fin 5)) = .front /\
    (followerAfter5V4 (3 : Fin 5)).repairPending = true /\
    (followerAfter5V4 (2 : Fin 5)).splice.base.core.core.probe = false := by
  decide

def stagedArmed3V4 : R1ConfigV4 3 2 0 0 :=
  serveV4 ring3 B9SpliceR2AttackRerun.stagedStart3 (1 : Fin 3)

def starvationFinal3V4 : R1ConfigV4 3 2 0 0 :=
  runV4 ring3 B9SpliceR2AttackRerun.stagedStart3
    B9SpliceR2AttackRerun.starvationWord3

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
theorem staged_deletion_not_arm_scrub_starved_v4 :
    (forall i,
      serveV4 ring3 stagedArmed3V4 (2 : Fin 3) i = stagedArmed3V4 i) /\
    (forall i,
      serveV4 ring3 stagedArmed3V4 (1 : Fin 3) i = stagedArmed3V4 i) /\
    safeAlongV4 ring3 B9SpliceR2AttackRerun.stagedStart3
      B9SpliceR2AttackRerun.starvationWord3 = true /\
    RolesClearV3 starvationFinal3V4 /\
    (starvationFinal3V4 (1 : Fin 3)).splice.base.core.core.leader = false /\
    (starvationFinal3V4 (2 : Fin 3)).splice.base.core.core.leader = true := by
  decide

end B9SpliceControllerR1TableV4

#print axioms B9SpliceControllerR1TableV4.controllerStateFactorV4_eq
#print axioms B9SpliceControllerR1TableV4.moveStop_preserves_spliceSafeR1V3
#print axioms B9SpliceControllerR1TableV4.q11668_moveStop_repaired_v4
#print axioms B9SpliceControllerR1TableV4.moveStop_failure_at_protocol_parameters_n4
#print axioms B9SpliceControllerR1TableV4.moveStop_protocol_parameters_repaired_v4
#print axioms B9SpliceControllerR1TableV4.leaderless_cycle3_v4_killed
#print axioms B9SpliceControllerR1TableV4.leaderless_deadlock4_v4_killed
#print axioms B9SpliceControllerR1TableV4.leaderless_cycle5_v4_killed
#print axioms B9SpliceControllerR1TableV4.q11592_pending_hold_replay_v4
#print axioms B9SpliceControllerR1TableV4.follower_old_unreserved_front_does_not_move_v4
#print axioms B9SpliceControllerR1TableV4.follower_anchor_authenticated_chain_safe_v4
#print axioms B9SpliceControllerR1TableV4.staged_deletion_not_arm_scrub_starved_v4
