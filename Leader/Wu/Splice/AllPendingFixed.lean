import Leader.Wu.Splice.HostTable
import Leader.Wu.Splice.CertifiedDeleteWholeStepSafe
import Leader.Wu.Birth.TwoStageEscape
import Leader.Wu.Birth.WaitPassiveRows

/-!
# All-pending controller fixed points

The physical host is arbitrary. The lower table layers hold on two pending
predecessors with false tickets. The top deletion test is excluded by the
physical initiator being a follower. No host result is installed.

The arbitrary-start family is not provenance-safe: its pending predecessors
have no reserved backing fronts. This file does not assume that invariant.
-/

set_option autoImplicit false
set_option Elab.async false

namespace B9AllPendingFixed

open PPLL PPLLDomain PPLLResearchFormulation
open Q11593SpliceControllerDesign
open B9SpliceControllerR1Table B9SpliceControllerR1TableV2
  B9SpliceControllerR1TableV3 B9SpliceControllerR1TableV6
  B9SpliceControllerR1TableV7 B9SpliceControllerR1TableV8
  B9SpliceControllerR1TableV9 B9SpliceControllerR1TableV10b
open B9OrphanToFence B9SpliceV10hControllerRowsSafe
open B9Host (HostRow Phys PhysConfig r1Host)
open B9SpliceTableHost
open BirthTwoStageEscape

variable {n psi kappa tau : Nat}

-- Open each table only at its own equation, never the complete nested row.
attribute [local irreducible]
  row7H row8H row9H row10bH row10cH row10dgH row10gH rowB9 stepB9

/-- Legal controller garbage over a completely unchanged physical cell. -/
def pendingCell (x : Phys psi kappa tau) : Cell psi kappa tau :=
  ⟨⟨⟨x, .predecessorArmed⟩, true⟩, false⟩

def allPending (X : PhysConfig n psi kappa tau) :
    Config n psi kappa tau :=
  fun i => pendingCell (X i)

/-- Physical follower status, with no restrictions on other fields. -/
def HostLeaderless (X : PhysConfig n psi kappa tau) : Prop :=
  ∀ i : Fin n, B9Host.leader (X i) = false

/-- The final-step leaderless predicate observes the erased physical state. -/
def Leaderless' (C : Config n psi kappa tau) : Prop :=
  HostLeaderless (erase C)

def LiftTarget (Target : PhysConfig n psi kappa tau → Prop)
    (C : Config n psi kappa tau) : Prop :=
  Target (erase C)

theorem pendingCell_fields (x : Phys psi kappa tau) :
    role (pendingCell x).carrier = .predecessorArmed ∧
    (pendingCell x).carrier.repairPending = true ∧
    (pendingCell x).acquireTicket = false ∧ base (pendingCell x) = x :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem erase_allPending (X : PhysConfig n psi kappa tau) :
    erase (allPending X) = X := rfl

theorem allPending_leaderless (X : PhysConfig n psi kappa tau)
    (hX : HostLeaderless X) : Leaderless' (allPending X) := hX

theorem pendingCell_not_fence (x : Phys psi kappa tau) :
    ¬ HostFenceShapeV7 (pendingCell x) := by
  intro h
  have hr : SpliceRole.predecessorArmed = .none := h.1
  cases hr

theorem pendingCell_not_reserved (x : Phys psi kappa tau) :
    ¬ ReservedFrontHoldGuard (pendingCell x).carrier := by
  intro h
  have hr : SpliceRole.predecessorArmed = .front := h.1
  cases hr

/-- The abort guard fires, but its write only clears an already-false ticket. -/
theorem pendingOwnerAbort_pendingCell (l r : Phys psi kappa tau) :
    pendingOwnerAbortWriteV6 (pendingCell l) (pendingCell r) =
      (pendingCell l, pendingCell r) := by
  change (pendingCell l, clearTicketV6 (pendingCell r)) =
    (pendingCell l, pendingCell r)
  rw [B9SpliceV10hWholeStepSafe.clearTicketV6_of_false
    (pendingCell r) (show (pendingCell r).acquireTicket = false from rfl)]

/-- No physical follower premise is needed below the top-level ldc test. -/
theorem row7H_pending_fixed
    (host : HostRow (Phys psi kappa tau)) (hp : 0 < psi)
    (l r : Phys psi kappa tau) :
    row7H host hp (pendingCell l) (pendingCell r) =
      (pendingCell l, pendingCell r) := by
  classical
  have hAcquire : ¬ MoveAcquireFrontGuardV6 hp
      (pendingCell l) (pendingCell r) := by
    intro h
    exact pendingCell_not_reserved l h.1
  have hA : ¬ ArmAGuardH host
      (pendingCell l).carrier (pendingCell r).carrier := by
    intro h
    have hr : SpliceRole.predecessorArmed = .none := h.1
    cases hr
  have hB : ¬ ArmBGuard
      (pendingCell l).carrier (pendingCell r).carrier := by
    intro h
    have hr : SpliceRole.predecessorArmed = .none := h.1
    cases hr
  have hDelete : ¬ DeleteGuardH host
      (pendingCell l).carrier (pendingCell r).carrier := by
    intro h
    have hr : SpliceRole.predecessorArmed = .front := h.1
    cases hr
  have hHold : ¬ PendingHoldGuardH host
      (pendingCell l).carrier (pendingCell r).carrier := by
    intro h
    have hr : SpliceRole.predecessorArmed = .victimArmed := h.1
    cases hr
  have hAbort : ¬ PendingAbortGuardH host
      (pendingCell l).carrier (pendingCell r).carrier := by
    intro h
    have hr : SpliceRole.predecessorArmed = .victimArmed := h.1
    cases hr
  have hCommit : ¬ MoveCommitGuard
      (pendingCell l).carrier (pendingCell r).carrier := by
    intro h
    have ht : true = false := h.2.1
    cases ht
  have hStop : ¬ MoveStopGuardV3 hp
      (pendingCell l).carrier (pendingCell r).carrier := by
    intro h
    have ht : true = false := h.2.1
    cases ht
  have hSeek : ¬ MoveSeekGuardV3 hp
      (pendingCell l).carrier (pendingCell r).carrier := by
    intro h
    have ht : true = false := h.2.1
    cases ht
  have hSeekHold : ¬ MoveSeekHoldGuardV3
      (pendingCell l).carrier (pendingCell r).carrier := by
    intro h
    have ht : true = false := h.2.1
    cases ht
  have hOwner : PendingOwnerAbortGuardV3
      (pendingCell l).carrier (pendingCell r).carrier := by
    refine ⟨rfl, rfl, ?_⟩
    intro h
    have ht : true = false := h.2
    cases ht
  unfold row7H
  rw [if_neg (pendingCell_not_fence l),
    if_neg (pendingCell_not_fence r), if_neg hAcquire,
    if_neg hA, if_neg hB, if_neg hDelete, if_neg hHold,
    if_neg hAbort, if_neg hCommit, if_neg hStop, if_neg hSeek,
    if_neg hSeekHold, if_pos hOwner]
  exact pendingOwnerAbort_pendingCell l r

/-- Both outcomes of the V8 guard are the same pair. -/
theorem row8H_pending_fixed
    (host : HostRow (Phys psi kappa tau)) (hp : 0 < psi)
    (l r : Phys psi kappa tau) :
    row8H host hp (pendingCell l) (pendingCell r) =
      (pendingCell l, pendingCell r) := by
  classical
  unfold row8H
  split
  · rfl
  · exact row7H_pending_fixed host hp l r

theorem row9H_pending_fixed
    (host : HostRow (Phys psi kappa tau)) (hp : 0 < psi)
    (l r : Phys psi kappa tau) :
    row9H host hp (pendingCell l) (pendingCell r) =
      (pendingCell l, pendingCell r) := by
  classical
  have hBusy : ¬ HostFenceBusyFrontGuardV9 hp
      (pendingCell l) (pendingCell r) := by
    intro h
    exact pendingCell_not_fence l h.1
  unfold row9H
  rw [if_neg hBusy]
  exact row8H_pending_fixed host hp l r

theorem row10bH_pending_fixed
    (host : HostRow (Phys psi kappa tau)) (hp : 0 < psi)
    (l r : Phys psi kappa tau) :
    row10bH host hp (pendingCell l) (pendingCell r) =
      (pendingCell l, pendingCell r) := by
  classical
  have hAdvance : ¬ HostFenceAdvanceGuardV10b hp
      (pendingCell l) (pendingCell r) := by
    intro h
    exact pendingCell_not_fence l h.1
  unfold row10bH
  rw [if_neg hAdvance]
  exact row9H_pending_fixed host hp l r

/-- Do not evaluate the host-dependent zero-refresh guard. -/
theorem row10cH_pending_fixed
    (host : HostRow (Phys psi kappa tau)) (hp : 0 < psi)
    (l r : Phys psi kappa tau) :
    row10cH host hp (pendingCell l) (pendingCell r) =
      (pendingCell l, pendingCell r) := by
  classical
  unfold row10cH
  split
  · rfl
  · exact row10bH_pending_fixed host hp l r

/-- None of the four garbage-repair guards recognizes this pair. -/
theorem row10dgH_pending_fixed
    (host : HostRow (Phys psi kappa tau)) (hp : 0 < psi)
    (l r : Phys psi kappa tau) :
    row10dgH host hp (pendingCell l) (pendingCell r) =
      (pendingCell l, pendingCell r) := by
  classical
  have hFront : ¬ OrphanReservedFrontGuardV3
      (pendingCell l).carrier (pendingCell r).carrier := by
    intro h
    exact pendingCell_not_reserved r h.1
  have hVictim : ¬ OrphanVictimGuard
      (pendingCell l) (pendingCell r) := by
    intro h
    have hr : SpliceRole.predecessorArmed = .victimArmed := h.1
    cases hr
  have hOwned : ¬ OwnedPendingVictimGuard
      (pendingCell l) (pendingCell r) := by
    intro h
    have ht : true = false := h.2.1
    cases ht
  have hOwnerless : ¬ OwnerlessPendingPredGuard
      (pendingCell l) (pendingCell r) := by
    intro h
    have hr : SpliceRole.predecessorArmed = .none := h.1
    cases hr
  unfold row10dgH
  rw [if_neg hFront, if_neg hVictim, if_neg hOwned, if_neg hOwnerless]
  exact row10cH_pending_fixed host hp l r

/-- The first stutter fallback holds, before any physicalHoldH fallback. -/
theorem row10gH_pending_fixed
    (host : HostRow (Phys psi kappa tau)) (hp : 0 < psi)
    (l r : Phys psi kappa tau) :
    row10gH host hp (pendingCell l) (pendingCell r) =
      (pendingCell l, pendingCell r) := by
  classical
  have hLeft : role (pendingCell l).carrier = .predecessorArmed ∧
      (pendingCell l).carrier.repairPending = true := ⟨rfl, rfl⟩
  unfold row10gH
  dsimp only
  rw [row10dgH_pending_fixed host hp l r, if_pos rfl, if_pos hLeft]

/-- Only the physical initiator's follower bit is needed here. -/
theorem pendingCell_not_ldc
    (host : HostRow (Phys psi kappa tau))
    (l r : Phys psi kappa tau) (hl : B9Host.leader l = false) :
    ¬ ldc host (pendingCell l).carrier (pendingCell r).carrier := by
  intro h
  have hleader : B9Host.leader l = true := h.1
  rw [hl] at hleader
  cases hleader

theorem rowB9_pending_fixed
    (host : HostRow (Phys psi kappa tau)) (hp : 0 < psi)
    (l r : Phys psi kappa tau) (hl : B9Host.leader l = false) :
    rowB9 host hp (pendingCell l) (pendingCell r) =
      (pendingCell l, pendingCell r) := by
  classical
  unfold rowB9
  rw [if_neg (pendingCell_not_ldc host l r hl)]
  exact row10gH_pending_fixed host hp l r

/-- Every scheduler edge holds, including the controller's self-edge case. -/
theorem allPending_step_fixed
    (host : HostRow (Phys psi kappa tau)) (hp : 0 < psi)
    (ring : DirectedRing n) (X : PhysConfig n psi kappa tau)
    (hX : HostLeaderless X) (e : Fin n) :
    stepB9 host hp ring (allPending X) e = allPending X := by
  classical
  have hrow : rowB9 host hp ((allPending X) e)
        ((allPending X) (ring.rightNeighbor e)) =
      ((allPending X) e, (allPending X) (ring.rightNeighbor e)) :=
    rowB9_pending_fixed host hp (X e) (X (ring.rightNeighbor e)) (hX e)
  unfold stepB9
  split
  · rfl
  · rw [hrow]
    exact B9SpliceV10hWholeStepSafe.writeAt_self ring (allPending X) e

theorem allPending_run_fixed
    (host : HostRow (Phys psi kappa tau)) (hp : 0 < psi)
    (ring : DirectedRing n) (X : PhysConfig n psi kappa tau)
    (hX : HostLeaderless X) (w : List (Fin n)) :
    w.foldl (stepB9 host hp ring) (allPending X) = allPending X := by
  induction w with
  | nil => rfl
  | cons e w ih =>
      change w.foldl (stepB9 host hp ring)
        (stepB9 host hp ring (allPending X) e) = allPending X
      rw [allPending_step_fixed host hp ring X hX e]
      exact ih

theorem allPending_erased_run_fixed
    (host : HostRow (Phys psi kappa tau)) (hp : 0 < psi)
    (ring : DirectedRing n) (X : PhysConfig n psi kappa tau)
    (hX : HostLeaderless X) (w : List (Fin n)) :
    erase (w.foldl (stepB9 host hp ring) (allPending X)) = X := by
  rw [allPending_run_fixed host hp ring X hX w, erase_allPending X]

/-- This initial family is legal as a carrier, but violates safe provenance. -/
theorem allPending_not_provenance
    (ring : DirectedRing n) (X : PhysConfig n psi kappa tau) :
    ¬ ProvenanceSafeV7 ring (allPending X) := by
  intro h
  let i : Fin n := ⟨0, ring.hn⟩
  have hback := h.2 i
    (show role ((allPending X) i).carrier = .predecessorArmed from rfl)
    (show ((allPending X) i).carrier.repairPending = true from rfl)
  exact pendingCell_not_reserved (X (ring.rightNeighbor i)) hback.1

/-- Generic fixed-state count: every one of the original n^B words avoids. -/
private theorem fixed_avoidCount {S : Type}
    (step : S → Fin n → S) (Good Target : S → Prop) (x : S)
    (hx : Good x ∧ ¬ Target x) (hfixed : ∀ e, step x e = x) (B : Nat) :
    avoidCount step Good Target x B = n ^ B := by
  induction B with
  | zero =>
      simpa only [Nat.pow_zero] using avoidCount_zero step Good Target x hx
  | succ B ih =>
      rw [avoidCount_succ step Good Target x hx B]
      calc
        (List.ofFn (fun e : Fin n =>
            avoidCount step Good Target (step x e) B)).sum =
            (List.ofFn (fun _ : Fin n => n ^ B)).sum := by
          apply FiniteUniformStoppingTree.ofFn_sum_eq
          intro e
          rw [hfixed e]
          exact ih
        _ = n * n ^ B := FiniteUniformStoppingTree.ofFn_sum_const n (n ^ B)
        _ = n ^ (B + 1) := by rw [Nat.pow_succ, Nat.mul_comm]

/-- An arbitrary final-configuration target, not necessarily physical. -/
theorem allPending_avoidCount
    (host : HostRow (Phys psi kappa tau)) (hp : 0 < psi)
    (ring : DirectedRing n) (X : PhysConfig n psi kappa tau)
    (hX : HostLeaderless X) (Target : Config n psi kappa tau → Prop)
    (hTarget : ¬ Target (allPending X)) (B : Nat) :
    avoidCount (stepB9 host hp ring) Leaderless' Target
      (allPending X) B = n ^ B :=
  fixed_avoidCount (stepB9 host hp ring) Leaderless' Target (allPending X)
    ⟨allPending_leaderless X hX, hTarget⟩
    (allPending_step_fixed host hp ring X hX) B

/-- Positive escape mass is impossible for any target missing the fixed state. -/
theorem no_escape_mass_for_finalTarget
    (host : HostRow (Phys psi kappa tau)) (hp : 0 < psi)
    (ring : DirectedRing n) (X : PhysConfig n psi kappa tau)
    (hX : HostLeaderless X) (Target : Config n psi kappa tau → Prop)
    (hTarget : ¬ Target (allPending X)) (Q B : Nat) (hQ : 1 ≤ Q) :
    ¬ (Q * avoidCount (stepB9 host hp ring) Leaderless' Target
          (allPending X) B ≤ (Q - 1) * n ^ B) := by
  intro h
  rw [allPending_avoidCount host hp ring X hX Target hTarget B] at h
  have hpow : 0 < n ^ B := Nat.pow_pos ring.hn
  have hscaled : n ^ B * Q ≤ n ^ B * (Q - 1) := by
    simpa only [Nat.mul_comm] using h
  have hbad : Q ≤ Q - 1 := Nat.le_of_mul_le_mul_left hscaled hpow
  omega

/-- Requested physical-target form; Leaderless' is defined using erase. -/
theorem no_escape_mass
    (host : HostRow (Phys psi kappa tau)) (hp : 0 < psi)
    (ring : DirectedRing n) (X : PhysConfig n psi kappa tau)
    (hX : HostLeaderless X) (Target : PhysConfig n psi kappa tau → Prop)
    (hTarget : ¬ Target X) (Q B : Nat) (hQ : 1 ≤ Q) :
    ¬ (Q * avoidCount (stepB9 host hp ring) Leaderless' (LiftTarget Target)
          (allPending X) B ≤ (Q - 1) * n ^ B) := by
  have ht : ¬ LiftTarget Target (allPending X) := by
    change ¬ Target (erase (allPending X))
    rw [erase_allPending X]
    exact hTarget
  exact no_escape_mass_for_finalTarget host hp ring X hX
    (LiftTarget Target) ht Q B hQ

/-- The same obstruction for the named R1-native final step. -/
theorem stepV10kR1_allPending_fixed
    (hp : 0 < psi) (h2 : 2 ≤ psi) (ring : DirectedRing n)
    (X : PhysConfig n psi kappa tau) (hX : HostLeaderless X) (e : Fin n) :
    stepV10kR1 hp h2 ring (allPending X) e = allPending X := by
  change stepB9 (r1Host hp h2) hp ring (allPending X) e = allPending X
  exact allPending_step_fixed (r1Host hp h2) hp ring X hX e

/-! ## Closed three-cell fixture

The physical records use the repository's passive cell constructor. All
payloads are absent, all bits are false, wait=true, and labels are 0,1,2.
Only the surrounding controller is malformed. The full-step fixture below
uses the structural theorem instead of evaluating the classical B9 table.
-/

def cleanRaw3 (lab : Fin 3) : AgentState 3 :=
  BirthWaitPassive.cell
    { label := lab, h := false, carry := false, reset := false,
      count := 0, wait := true, bit := false, phase := false, writer := .none }

theorem cleanRaw3_domain (lab : Fin 3) : (cleanRaw3 lab).inProtocolDomain 3 := by
  simp [cleanRaw3, BirthWaitPassive.cell, AgentState.inProtocolDomain]

def cleanPhys3 (lab : Fin 3) : Phys 3 3 1 :=
  ⟨⟨BoundedAgentState.ofDomain (cleanRaw3 lab) (cleanRaw3_domain lab), false⟩,
    Fin.last 1⟩

def cleanX3 : PhysConfig 3 3 3 1 := fun i => cleanPhys3 i

def ring3 : DirectedRing 3 := ⟨by decide⟩

def cleanR1Host3 : HostRow (Phys 3 3 1) :=
  r1Host (kappa := 3) (tau := 1)
    (by decide : 0 < 3) (by decide : 2 ≤ 3)

theorem cleanX3_leaderless : HostLeaderless cleanX3 := by
  intro i
  change (BoundedAgentState.ofDomain
    (cleanRaw3 i) (cleanRaw3_domain i)).erase.leader = false
  rw [BoundedAgentState.erase_ofDomain]
  rfl

/-- Kernel sanity check of two concrete cells and the ticket-only write. -/
theorem clean3_ticket_abort_sanity :
    pendingOwnerAbortWriteV6 (pendingCell (cleanPhys3 0))
        (pendingCell (cleanPhys3 1)) =
      (pendingCell (cleanPhys3 0), pendingCell (cleanPhys3 1)) := by
  decide +kernel

theorem r1_clean3_step_fixed (e : Fin 3) :
    stepB9 cleanR1Host3 (by decide : 0 < 3) ring3 (allPending cleanX3) e =
      allPending cleanX3 :=
  allPending_step_fixed cleanR1Host3 (by decide) ring3
    cleanX3 cleanX3_leaderless e

theorem r1_clean3_run_fixed (w : List (Fin 3)) :
    w.foldl (stepB9 cleanR1Host3 (by decide : 0 < 3) ring3)
        (allPending cleanX3) = allPending cleanX3 :=
  allPending_run_fixed cleanR1Host3 (by decide) ring3
    cleanX3 cleanX3_leaderless w

/-- With Target=False, escaping would require an actual first leader. -/
theorem r1_clean3_no_first_leader_mass (Q B : Nat) (hQ : 1 ≤ Q) :
    ¬ (Q * avoidCount (stepB9 cleanR1Host3 (by decide : 0 < 3) ring3)
          Leaderless' (fun _ : Config 3 3 3 1 => False)
          (allPending cleanX3) B ≤ (Q - 1) * 3 ^ B) :=
  no_escape_mass_for_finalTarget cleanR1Host3 (by decide) ring3
    cleanX3 cleanX3_leaderless (fun _ => False) (fun h => h) Q B hQ

end B9AllPendingFixed
