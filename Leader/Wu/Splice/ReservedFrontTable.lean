import Leader.Wu.Splice.MovingFrontTable

set_option autoImplicit false
set_option Elab.async false
set_option pp.structureInstances false

namespace B9SpliceControllerR1TableV2

open PPLL PPLLResearchFormulation
  PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
open PPLLLeaderCreationCleanupRepair
open BirthSigMoveDisposalRepair
  BirthShortDoneTerminalBirthSources
open Q11593SpliceControllerDesign
open B9SpliceControllerR1Table

variable {n psi width kappa tau : Nat}

/-! ## Same carrier, broader meaning of the existing bit -/

/-- V2 adds no local state.  The existing Boolean is interpreted by role:

* `predecessorArmed,true`: incoming repair is still pending;
* `front,true`: the front is reserved as that owner's backing site.

Thus the raw controller factor remains four roles times one Boolean. -/
abbrev R1AgentStateV2 (psi kappa tau : Nat) :=
  R1AgentState psi kappa tau

abbrev R1ConfigV2 (n psi kappa tau : Nat) :=
  R1Config n psi kappa tau

/-- A reserved front must not be consumed or scrubbed by an unrelated edge. -/
def ReservedFrontHoldGuard
    (u : R1AgentStateV2 psi kappa tau) : Prop :=
  role u = .front /\ u.repairPending = true

/-- V2 ownership has the three old moving shapes plus two frozen seam shapes.

The two new alternatives are exactly what DELETE needs while a repair is in
flight:

* a reserved front owns/f freezes its outgoing seam;
* a pending predecessor freezes its incoming seam.

The ordinary predecessor-owned seam remains the final disjunct. -/
def R1ProtectedSpliceEdgeV2
    (ring : DirectedRing n) (C : R1ConfigV2 n psi kappa tau)
    (e : Fin n) : Prop :=
  let l := C e
  let r := C (ring.rightNeighbor e)
  (role l = .front /\ l.repairPending = true) \/
  (role r = .predecessorArmed /\ r.repairPending = true) \/
  (role l = .predecessorArmed /\
    (role r = .front \/
     (role r = .victimArmed /\ r.repairPending = false) \/
     (role r = .predecessorArmed /\ r.repairPending = true)))

/-- V2 splice safety.

The first clause is the P-prime ownership certificate with the two frozen
reservation shapes above.  The second clause is the moving-front lease:
`predecessorArmed,true` is backed by a right `front,true` reservation.

As in R1, this is a safety predicate, not a genuineness predicate for
every forged control mark. -/
def SpliceSafeR1V2
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (C : R1ConfigV2 n psi kappa tau) : Prop :=
  (forall e,
      PreparedDangerAt hpsi ring C e ->
        R1ProtectedSpliceEdgeV2 ring C e) /\
  (forall i,
      role (C i) = .predecessorArmed ->
      (C i).repairPending = true ->
        role (C (ring.rightNeighbor i)) = .front /\
        (C (ring.rightNeighbor i)).repairPending = true)

/-! ## The only reservation-sensitive guard changes -/

/-- After an incoming repair has committed, stop may consume either an old
unreserved front or the v2 reserved backing front. -/
def MoveStopGuardV2
    (hpsi : 0 < psi)
    (l r : R1AgentStateV2 psi kappa tau) : Prop :=
  role l = .predecessorArmed /\ l.repairPending = false /\
  role r = .front /\
  ¬ LocalPreparedBarrier hpsi l r

/-- Likewise a continuing barrier may turn either kind of front into the next
follower acquisition request.  This consumes the reservation atomically. -/
def MoveSeekGuardV2
    (hpsi : 0 < psi)
    (l r : R1AgentStateV2 psi kappa tau) : Prop :=
  role l = .predecessorArmed /\ l.repairPending = false /\
  role r = .front /\
  LocalPreparedBarrier hpsi l r

/-! ## Module-local computable guard instances -/

private instance q11647DecidableArmAGuard
    {psi width kappa tau : Nat}
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (l r : R1AgentStateV2 psi kappa tau) :
    Decidable (ArmAGuard hpsi hwidth hle l r) := by
  unfold ArmAGuard LeftDeletionCandidate
  infer_instance

private instance q11647DecidableArmBGuard
    {psi kappa tau : Nat}
    (l r : R1AgentStateV2 psi kappa tau) :
    Decidable (ArmBGuard l r) := by
  unfold ArmBGuard
  infer_instance

private instance q11647DecidableDeleteGuard
    {psi width kappa tau : Nat}
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (l r : R1AgentStateV2 psi kappa tau) :
    Decidable (DeleteGuard hpsi hwidth hle l r) := by
  unfold DeleteGuard LeftDeletionCandidate
  infer_instance

private instance q11647DecidablePendingHoldGuard
    {psi width kappa tau : Nat}
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (l r : R1AgentStateV2 psi kappa tau) :
    Decidable (PendingHoldGuard hpsi hwidth hle l r) := by
  unfold PendingHoldGuard LeftDeletionCandidate
  infer_instance

private instance q11647DecidablePendingAbortGuard
    {psi width kappa tau : Nat}
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (l r : R1AgentStateV2 psi kappa tau) :
    Decidable (PendingAbortGuard hpsi hwidth hle l r) := by
  unfold PendingAbortGuard LeftDeletionCandidate
  infer_instance

private instance q11647DecidableMoveCommitGuard
    {psi kappa tau : Nat}
    (l r : R1AgentStateV2 psi kappa tau) :
    Decidable (MoveCommitGuard l r) := by
  unfold MoveCommitGuard
  infer_instance

private instance q11647DecidableMoveStopGuardV2
    {psi kappa tau : Nat}
    (hpsi : 0 < psi)
    (l r : R1AgentStateV2 psi kappa tau) :
    Decidable (MoveStopGuardV2 hpsi l r) := by
  unfold MoveStopGuardV2 LocalPreparedBarrier
  dsimp only
  unfold isBarrier
  infer_instance

private instance q11647DecidableMoveSeekGuardV2
    {psi kappa tau : Nat}
    (hpsi : 0 < psi)
    (l r : R1AgentStateV2 psi kappa tau) :
    Decidable (MoveSeekGuardV2 hpsi l r) := by
  unfold MoveSeekGuardV2 LocalPreparedBarrier
  dsimp only
  unfold isBarrier
  infer_instance

private instance q11647DecidableMoveSeekHoldGuard
    {psi kappa tau : Nat}
    (l r : R1AgentStateV2 psi kappa tau) :
    Decidable (MoveSeekHoldGuard l r) := by
  unfold MoveSeekHoldGuard
  infer_instance

private instance q11647DecidableMoveAcquireGuard
    {psi kappa tau : Nat}
    (l r : R1AgentStateV2 psi kappa tau) :
    Decidable (MoveAcquireGuard l r) := by
  unfold MoveAcquireGuard
  infer_instance

private instance q11647DecidableReservedFrontHoldGuard
    {psi kappa tau : Nat}
    (u : R1AgentStateV2 psi kappa tau) :
    Decidable (ReservedFrontHoldGuard u) := by
  unfold ReservedFrontHoldGuard
  infer_instance

/-! ## V2 row and ring lift -/

/-- Additive v2 table.

Every v1 guard is reused literally except `MoveStop`/`MoveSeek`, which must be
able to consume the new reserved-front value.  DELETE and MOVE-ACQUIRE write a
reservation on the right front.  A reserved front otherwise fails closed. -/
def rowV2
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (l r : R1AgentStateV2 psi kappa tau) :
    R1AgentStateV2 psi kappa tau × R1AgentStateV2 psi kappa tau :=
  -- ARM-A: unchanged.
  if ArmAGuard hpsi hwidth hle l r then
    (setControl l .victimArmed false,
      setControl r .front false)
  -- ARM-B: unchanged.
  else if ArmBGuard l r then
    (setControl l .predecessorArmed false,
      setControl r .front false)
  -- DELETE: old physical row, but reserve the surviving backing front.
  else if DeleteGuard hpsi hwidth hle l r then
    let q := BirthShortDoneTerminalHost.row
      hpsi hwidth hle l.splice.base r.splice.base
    (setControl (setPhysical l q.1) .predecessorArmed true,
      setControl (setPhysical r q.2) .front true)
  -- Pending deletion freeze: unchanged.
  else if PendingHoldGuard hpsi hwidth hle l r then
    (l, r)
  -- Pending deletion abort: unchanged.
  else if PendingAbortGuard hpsi hwidth hle l r then
    (clearControl l, clearControl r)
  -- MOVE-COMMIT: unchanged.  Its outgoing reserved front is not on this edge.
  else if MoveCommitGuard l r then
    (clearControl l,
      setControl (repairResponder hpsi l r) .predecessorArmed false)
  -- Reservation-aware STOP and SEEK.
  else if MoveStopGuardV2 hpsi l r then
    (clearControl l, clearControl r)
  else if MoveSeekGuardV2 hpsi l r then
    (l, setControl r .victimArmed false)
  -- MOVE-SEEK-HOLD: unchanged.
  else if MoveSeekHoldGuard l r then
    (l, r)
  -- Pending owner cannot act on its outgoing seam before incoming repair.
  else if role l = .predecessorArmed /\ l.repairPending = true then
    (l, r)
  -- MOVE-ACQUIRE: acquire first, and record the new backing reservation.
  else if MoveAcquireGuard l r then
    (setControl l .predecessorArmed true,
      setControl r .front true)
  -- Busy follower request: unchanged fail-closed behavior.
  else if role l = .victimArmed /\
      l.splice.base.core.core.leader = false then
    (l, r)
  -- A reserved front never drives an unrelated outgoing transition.
  else if ReservedFrontHoldGuard l then
    (l, r)
  -- Malformed bits remain scrub-able, but front,true is now well-formed.
  else if l.repairPending = true /\
      role l ≠ .predecessorArmed /\ role l ≠ .front then
    ({ l with repairPending := false }, r)
  else if r.repairPending = true /\
      role r ≠ .predecessorArmed /\ role r ≠ .front then
    (l, { r with repairPending := false })
  -- A reserved front also fails closed when seen as responder, unless the
  -- owner-side STOP/SEEK branches above consumed it.
  else if ReservedFrontHoldGuard r then
    (l, r)
  -- Remaining oriented cleanup is v1 verbatim.
  else if role r = .front then
    (l, clearControl r)
  else if role r = .victimArmed then
    (l, clearControl r)
  else if role l = .predecessorArmed then
    (clearControl l, r)
  else if role l = .victimArmed then
    (clearControl l, r)
  else if role l = .front then
    (l, r)
  else if role l ≠ .none \/ role r ≠ .none /\
      (l.repairPending = true \/ r.repairPending = true) then
    (l, r)
  else
    ordinaryRow hpsi hwidth hle l r

/-- Ring lift.  The splice protocol is intrinsically a two-endpoint protocol;
on the degenerate one-site self-edge v2 fails closed rather than installing a
pending owner with no distinct backing front. -/
def stepV2
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (ring : DirectedRing n) (C : R1ConfigV2 n psi kappa tau)
    (e : Fin n) : R1ConfigV2 n psi kappa tau :=
  let j := ring.rightNeighbor e
  if j = e then C
  else
    let q := rowV2 hpsi hwidth hle (C e) (C j)
    fun i =>
      if i = e then q.1
      else if i = j then q.2
      else C i

/-! ## Structural helpers for the DELETE proof -/

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

private theorem stepV2_left_of_row
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (ring : DirectedRing n) (C : R1ConfigV2 n psi kappa tau)
    (e : Fin n)
    (out : R1AgentStateV2 psi kappa tau × R1AgentStateV2 psi kappa tau)
    (hne : ring.rightNeighbor e ≠ e)
    (hrow : rowV2 hpsi hwidth hle
      (C e) (C (ring.rightNeighbor e)) = out) :
    stepV2 hpsi hwidth hle ring C e e = out.1 := by
  simp [stepV2, hne, hrow]

private theorem stepV2_right_of_row
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (ring : DirectedRing n) (C : R1ConfigV2 n psi kappa tau)
    (e : Fin n)
    (out : R1AgentStateV2 psi kappa tau × R1AgentStateV2 psi kappa tau)
    (hne : ring.rightNeighbor e ≠ e)
    (hrow : rowV2 hpsi hwidth hle
      (C e) (C (ring.rightNeighbor e)) = out) :
    stepV2 hpsi hwidth hle ring C e (ring.rightNeighbor e) = out.2 := by
  simp [stepV2, hne, hrow]

private theorem stepV2_other
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (ring : DirectedRing n) (C : R1ConfigV2 n psi kappa tau)
    (e i : Fin n)
    (hne : ring.rightNeighbor e ≠ e)
    (hi : i ≠ e) (hj : i ≠ ring.rightNeighbor e) :
    stepV2 hpsi hwidth hle ring C e i = C i := by
  simp [stepV2, hne, hi, hj]

private theorem preparedDangerAt_congr_states
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (C D : R1ConfigV2 n psi kappa tau) (e : Fin n)
    (hL : D e = C e)
    (hR : D (ring.rightNeighbor e) = C (ring.rightNeighbor e)) :
    PreparedDangerAt hpsi ring D e <->
      PreparedDangerAt hpsi ring C e := by
  unfold PreparedDangerAt PreparedBarrierAt projectSpliceConfig
  dsimp only
  rw [hL, hR]

private theorem rowV2_of_delete
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (l r : R1AgentStateV2 psi kappa tau)
    (h : DeleteGuard hpsi hwidth hle l r) :
    rowV2 hpsi hwidth hle l r =
      let q := BirthShortDoneTerminalHost.row
        hpsi hwidth hle l.splice.base r.splice.base
      (setControl (setPhysical l q.1) .predecessorArmed true,
        setControl (setPhysical r q.2) .front true) := by
  have hg := h
  rcases hg with ⟨hl, _hr, _hlp, _hrp, _hdel⟩
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
  simp [rowV2, hA, hB, h]

/-! ## 1. DELETE preservation -/

theorem delete_preserves_spliceSafeR1V2
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (ring : DirectedRing n) (C : R1ConfigV2 n psi kappa tau)
    (e : Fin n)
    (hsafe : SpliceSafeR1V2 hpsi ring C)
    (hguard : DeleteGuard hpsi hwidth hle
      (C e) (C (ring.rightNeighbor e))) :
    SpliceSafeR1V2 hpsi ring
      (stepV2 hpsi hwidth hle ring C e) := by
  by_cases hself : ring.rightNeighbor e = e
  · simpa [stepV2, hself] using hsafe
  · let D := stepV2 hpsi hwidth hle ring C e
    let q := BirthShortDoneTerminalHost.row
      hpsi hwidth hle
      (C e).splice.base (C (ring.rightNeighbor e)).splice.base
    have hrow :
        rowV2 hpsi hwidth hle (C e) (C (ring.rightNeighbor e)) =
          (setControl (setPhysical (C e) q.1) .predecessorArmed true,
            setControl
              (setPhysical (C (ring.rightNeighbor e)) q.2) .front true) := by
      simpa [q] using
        (rowV2_of_delete hpsi hwidth hle
          (C e) (C (ring.rightNeighbor e)) hguard)
    have hE :
        D e =
          setControl (setPhysical (C e) q.1) .predecessorArmed true := by
      dsimp [D]
      exact stepV2_left_of_row hpsi hwidth hle ring C e
        (setControl (setPhysical (C e) q.1) .predecessorArmed true,
          setControl
            (setPhysical (C (ring.rightNeighbor e)) q.2) .front true)
        hself hrow
    have hJ :
        D (ring.rightNeighbor e) =
          setControl
            (setPhysical (C (ring.rightNeighbor e)) q.2) .front true := by
      dsimp [D]
      exact stepV2_right_of_row hpsi hwidth hle ring C e
        (setControl (setPhysical (C e) q.1) .predecessorArmed true,
          setControl
            (setPhysical (C (ring.rightNeighbor e)) q.2) .front true)
        hself hrow
    have hErole : role (D e) = .predecessorArmed := by
      have h := congrArg role hE
      simpa [role, setControl, setPhysical] using h
    have hEpending : (D e).repairPending = true := by
      have h := congrArg
        (fun u : R1AgentStateV2 psi kappa tau => u.repairPending) hE
      simpa [setControl, setPhysical] using h
    have hJrole : role (D (ring.rightNeighbor e)) = .front := by
      have h := congrArg role hJ
      simpa [role, setControl, setPhysical] using h
    have hJpending :
        (D (ring.rightNeighbor e)).repairPending = true := by
      have h := congrArg
        (fun u : R1AgentStateV2 psi kappa tau => u.repairPending) hJ
      simpa [setControl, setPhysical] using h
    have hg := hguard
    rcases hg with ⟨_heFront, _hjFront, heFree, _hjFree, _hdel⟩
    constructor
    · intro x hd
      by_cases hxe : x = e
      · subst x
        unfold R1ProtectedSpliceEdgeV2
        dsimp only
        exact Or.inr (Or.inr ⟨hErole, Or.inl hJrole⟩)
      · by_cases hxj : x = ring.rightNeighbor e
        · subst x
          unfold R1ProtectedSpliceEdgeV2
          dsimp only
          exact Or.inl ⟨hJrole, hJpending⟩
        · by_cases hrxe : ring.rightNeighbor x = e
          · have hrRole :
                role (D (ring.rightNeighbor x)) = .predecessorArmed := by
              exact
                (congrArg (fun y : Fin n => role (D y)) hrxe).trans hErole
            have hrPending :
                (D (ring.rightNeighbor x)).repairPending = true := by
              exact
                (congrArg
                  (fun y : Fin n => (D y).repairPending) hrxe).trans
                  hEpending
            unfold R1ProtectedSpliceEdgeV2
            dsimp only
            exact Or.inr (Or.inl ⟨hrRole, hrPending⟩)
          · have hrxj :
                ring.rightNeighbor x ≠ ring.rightNeighbor e := by
              intro h
              exact hxe (rightNeighbor_injective ring h)
            have hDx : D x = C x := by
              dsimp [D]
              exact stepV2_other hpsi hwidth hle ring C e x
                hself hxe hxj
            have hDr :
                D (ring.rightNeighbor x) = C (ring.rightNeighbor x) := by
              dsimp [D]
              exact stepV2_other hpsi hwidth hle ring C e
                (ring.rightNeighbor x) hself hrxe hrxj
            have hd0 :=
              (preparedDangerAt_congr_states
                hpsi ring C D x hDx hDr).1 hd
            have hp0 := hsafe.1 x hd0
            unfold R1ProtectedSpliceEdgeV2 at hp0 ⊢
            dsimp only at hp0 ⊢
            have hDx' : stepV2 hpsi hwidth hle ring C e x = C x := hDx
            have hDr' : stepV2 hpsi hwidth hle ring C e (ring.rightNeighbor x) =
                C (ring.rightNeighbor x) := hDr
            simpa only [hDx', hDr'] using hp0
    · intro i hpred hp
      by_cases hie : i = e
      · subst i
        exact ⟨hJrole, hJpending⟩
      · by_cases hij : i = ring.rightNeighbor e
        · subst i
          have hbad : SpliceRole.front = SpliceRole.predecessorArmed :=
            hJrole.symm.trans hpred
          cases hbad
        · have hDi : D i = C i := by
            dsimp [D]
            exact stepV2_other hpsi hwidth hle ring C e i
              hself hie hij
          have hroleDi : role (D i) = role (C i) :=
            congrArg role hDi
          have hpendingDi :
              (D i).repairPending = (C i).repairPending :=
            congrArg
              (fun u : R1AgentStateV2 psi kappa tau => u.repairPending) hDi
          have hpred0 : role (C i) = .predecessorArmed :=
            hroleDi.symm.trans hpred
          have hp0 : (C i).repairPending = true :=
            hpendingDi.symm.trans hp
          have hb := hsafe.2 i hpred0 hp0
          have hrE : ring.rightNeighbor i ≠ e := by
            intro h
            have hindex := congrArg
              (fun y : Fin n => (C y).repairPending) h
            have hbitE : (C e).repairPending = true :=
              hindex.symm.trans hb.2
            have hbad : false = true := heFree.symm.trans hbitE
            cases hbad
          have hrJ :
              ring.rightNeighbor i ≠ ring.rightNeighbor e := by
            intro h
            exact hie (rightNeighbor_injective ring h)
          have hDr :
              D (ring.rightNeighbor i) = C (ring.rightNeighbor i) := by
            dsimp [D]
            exact stepV2_other hpsi hwidth hle ring C e
              (ring.rightNeighbor i) hself hrE hrJ
          have hroleDr :
              role (D (ring.rightNeighbor i)) =
                role (C (ring.rightNeighbor i)) :=
            congrArg role hDr
          have hpendingDr :
              (D (ring.rightNeighbor i)).repairPending =
                (C (ring.rightNeighbor i)).repairPending :=
            congrArg
              (fun u : R1AgentStateV2 psi kappa tau => u.repairPending) hDr
          exact ⟨hroleDr.trans hb.1, hpendingDr.trans hb.2⟩

/-- Closed-fixture decision instances only. -/
private instance q11647DecidablePreparedDangerAtLocal
    {n psi kappa tau : Nat}
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (C : R1ConfigV2 n psi kappa tau) (e : Fin n) :
    Decidable (PreparedDangerAt hpsi ring C e) := by
  unfold PreparedDangerAt PreparedBarrierAt
  dsimp only
  unfold isBarrier
  infer_instance

private instance q11647DecidableR1ProtectedSpliceEdgeV2Local
    {n psi kappa tau : Nat}
    (ring : DirectedRing n) (C : R1ConfigV2 n psi kappa tau)
    (e : Fin n) :
    Decidable (R1ProtectedSpliceEdgeV2 ring C e) := by
  unfold R1ProtectedSpliceEdgeV2
  dsimp only
  infer_instance

private instance q11647DecidableSpliceSafeR1V2Local
    {n psi kappa tau : Nat}
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (C : R1ConfigV2 n psi kappa tau) :
    Decidable (SpliceSafeR1V2 hpsi ring C) := by
  unfold SpliceSafeR1V2
  infer_instance

private instance q11647DecidableLeftDeletionCandidateLocal
    {psi width kappa tau : Nat}
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (l r : SpliceAgentState psi kappa tau) :
    Decidable (LeftDeletionCandidate hpsi hwidth hle l r) := by
  unfold LeftDeletionCandidate
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
    (r : SpliceRole) (pending : Bool) : R1AgentStateV2 1 0 0 :=
  { splice :=
      { base := leaderPhysical
        spliceRole := r }
    repairPending := pending }

/-- Same physical/role shape, now with the incoming reservation
recorded where v2 says it belongs:

* site 0 = `predecessorArmed,true`;
* site 1 = `front,true` (reserved by site 0);
* site 2 = `front,false`.

All three physical cells remain leaders. -/
private def deleteStartV2 : R1ConfigV2 3 1 0 0 := fun i =>
  if i = 0 then leaderR1 .predecessorArmed true
  else if i = 1 then leaderR1 .front true
  else leaderR1 .front false

set_option maxHeartbeats 50000000 in
set_option maxRecDepth 32768 in
/-- The old physical deletion is still live on 1 -> 2, but v2 sees that site 1
is somebody else's reserved front.  Hence DELETE is disabled and the explicit
reserved-front HOLD leaves all three sites unchanged. -/
theorem q11644_three_site_v2_fixture :
    SpliceSafeR1V2 hOne ring3 deleteStartV2 /\
    LeftDeletionCandidate hOne hOne hOneLe
      (deleteStartV2 (1 : Fin 3)).splice
      (deleteStartV2 (2 : Fin 3)).splice /\
    ¬ DeleteGuard hOne hOne hOneLe
      (deleteStartV2 (1 : Fin 3))
      (deleteStartV2 (2 : Fin 3)) /\
    rowV2 hOne hOne hOneLe
      (deleteStartV2 (1 : Fin 3))
      (deleteStartV2 (2 : Fin 3)) =
        (deleteStartV2 (1 : Fin 3), deleteStartV2 (2 : Fin 3)) /\
    stepV2 hOne hOne hOneLe ring3 deleteStartV2
      (1 : Fin 3) (0 : Fin 3) = deleteStartV2 (0 : Fin 3) /\
    stepV2 hOne hOne hOneLe ring3 deleteStartV2
      (1 : Fin 3) (1 : Fin 3) = deleteStartV2 (1 : Fin 3) /\
    stepV2 hOne hOne hOneLe ring3 deleteStartV2
      (1 : Fin 3) (2 : Fin 3) = deleteStartV2 (2 : Fin 3) := by
  decide

/-! ## 3. State-count factor -/

/-- No new role and no new bit were added. -/
def controllerStateFactorV2 : Nat := controllerStateFactor

/-- V2 therefore remains exactly four splice roles times one Boolean: 8. -/
theorem controllerStateFactorV2_eq :
    controllerStateFactorV2 = 8 := by
  decide

/-- In particular the v2 factor is definitionally the same as R1's factor. -/
theorem controllerStateFactorV2_eq_v1 :
    controllerStateFactorV2 = controllerStateFactor := by
  rfl

end B9SpliceControllerR1TableV2

#print axioms B9SpliceControllerR1TableV2.delete_preserves_spliceSafeR1V2
#print axioms B9SpliceControllerR1TableV2.q11644_three_site_v2_fixture
#print axioms B9SpliceControllerR1TableV2.controllerStateFactorV2_eq
#print axioms B9SpliceControllerR1TableV2.controllerStateFactorV2_eq_v1
