import Leader.Wu.Splice.StaleHoldTable
import Leader.Wu.Splice.CheckFreezeLifetime
import Leader.Wu.Scheduler.FixedSpanRenewalPayload
import Leader.Wu.Birth.GenericRenewal


set_option autoImplicit false
set_option Elab.async false
set_option pp.structureInstances false


namespace B9SpliceLifetime


open Q11593SpliceControllerDesign
open B9SpliceControllerR1Table
open B9SpliceControllerR1TableV2
open B9SpliceControllerR1TableV3
open B9SpliceControllerR1TableV4
open B9SpliceControllerR1TableV6
open B9SpliceControllerR1TableV7
open B9SpliceControllerR1TableV8
open FiniteUniformStoppingTree


variable {n psi width kappa tau : Nat}


/-! ## 1. Raw-word lifetime of one splice transaction


The input configuration is the state immediately after the designated ARM or
SEEK start row has fired.  For a one-transaction projection, `RolesClearV7`
means that transaction has committed/stopped or safely aborted and all of its
controller/fence state has drained.


As in B9LeaseLifetime, an unresolved finite word gets the sentinel `|u|+1`.
This is a finite-word stopping time, not a deterministic scheduler cap. -/


private instance instDecidableRolesClearLifetime
    (C : R1ConfigV6 n psi kappa tau) : Decidable (RolesClearV7 C) := by
  unfold RolesClearV7
  infer_instance


def spliceRun
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (ring : DirectedRing n) :
    R1ConfigV6 n psi kappa tau -> List (Fin n) -> R1ConfigV6 n psi kappa tau
  | C, [] => C
  | C, e :: u => spliceRun hpsi hwidth hle ring
      (stepV8 hpsi hwidth hle ring C e) u


def spliceLife
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (ring : DirectedRing n) :
    R1ConfigV6 n psi kappa tau -> List (Fin n) -> Nat
  | C, [] => if RolesClearV7 C then 0 else 1
  | C, e :: u =>
      if RolesClearV7 C then 0
      else 1 + spliceLife hpsi hwidth hle ring
        (stepV8 hpsi hwidth hle ring C e) u


def spliceResolutionWeight
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (ring : DirectedRing n)
    (C : R1ConfigV6 n psi kappa tau) (u : List (Fin n)) : Nat :=
  if spliceLife hpsi hwidth hle ring C u <= u.length then 1 else 0


def spliceFailureWeight
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (ring : DirectedRing n)
    (C : R1ConfigV6 n psi kappa tau) (u : List (Fin n)) : Nat :=
  if spliceLife hpsi hwidth hle ring C u <= u.length then 0 else 1


def spliceResolutionMass
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (ring : DirectedRing n)
    (C : R1ConfigV6 n psi kappa tau) (L : Nat) : Nat :=
  FixedSpanRenewalPayload.wordSum n L
    (spliceResolutionWeight hpsi hwidth hle ring C)


def spliceFailureMass
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (ring : DirectedRing n)
    (C : R1ConfigV6 n psi kappa tau) (L : Nat) : Nat :=
  FixedSpanRenewalPayload.wordSum n L
    (spliceFailureWeight hpsi hwidth hle ring C)


/-- Exact project `HMass` form: success probability in one raw block is at
least `1/Q`. -/
def SpliceBlockMassBound
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (ring : DirectedRing n)
    (C : R1ConfigV6 n psi kappa tau) (L Q : Nat) : Prop :=
  n ^ L <= Q * spliceResolutionMass hpsi hwidth hle ring C L


/-- Exact Bellman/B7 numerator form for a geometric block tail. -/
def SpliceGeometricTailBound
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (ring : DirectedRing n)
    (C : R1ConfigV6 n psi kappa tau) (L Q : Nat) : Prop :=
  forall k,
    Q ^ k * spliceFailureMass hpsi hwidth hle ring C (L * k) <=
      (Q - 1) ^ k * n ^ (L * k)


/-! ## 2. The horizon suggested by the old V6 drain


V6 proves `controllerPotentialV6 C <= 8*n`.  If every live V8 state had an
enabled progress edge and every such edge paid at least one unit, `8*n`
consecutive progress choices would suffice.  Since at least one of `n`
scheduler letters would be progress, one prescribed all-progress word would
give the crude but exact word-sum choice `Q = n^L`.


The two counterexamples below show that these are only candidate constants on
current V8. -/


def v6CandidateSpliceBlockLength (n : Nat) : Nat := 8 * n


def v6CandidateSpliceBlockQ (n : Nat) : Nat :=
  n ^ v6CandidateSpliceBlockLength n


/-- B7-style amplified raw-letter horizon, conditional on the missing block
renewal theorem.  This is deliberately not connected to the pointwise
`SpliceLifetimeBound`. -/
def b9SpliceHorizonCandidate (n s : Nat) : Nat :=
  v6CandidateSpliceBlockLength n *
    BirthPhaseGenericRenewal.renewalK (v6CandidateSpliceBlockQ n) s


/-! ## 3. First obstruction: V8 progress need not lower the V6 drain weight -/


def SameControllerV8
    (C D : R1ConfigV6 n psi kappa tau) : Prop :=
  forall i,
    role (C i).carrier = role (D i).carrier /\
    (C i).carrier.repairPending = (D i).carrier.repairPending /\
    (C i).acquireTicket = (D i).acquireTicket


private instance instDecidableSameControllerV8
    (C D : R1ConfigV6 n psi kappa tau) :
    Decidable (SameControllerV8 C D) := by
  unfold SameControllerV8
  infer_instance


def ControllerChangedV8
    (C D : R1ConfigV6 n psi kappa tau) : Prop :=
  not (SameControllerV8 C D)


private instance instDecidableControllerChangedV8
    (C D : R1ConfigV6 n psi kappa tau) :
    Decidable (ControllerChangedV8 C D) := by
  unfold ControllerChangedV8
  infer_instance


set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
/-- The first q11703 fence ADVANCE is non-stuttering, but it only transports
one unit of ticket weight.  Therefore the V6 potential is not a strict V8
progress rank. -/
theorem q11703_fence_advance_nondrain :
    ControllerChangedV8 q11703ArmedAfterV8 q11703Fence1V8 /\
    controllerPotentialV6 q11703Fence1V8 =
      controllerPotentialV6 q11703ArmedAfterV8 := by
  decide


/-! ## 4. Second obstruction: a literal safe two-site fence livelock -/


private theorem hOneLife : 0 < 1 := by decide
private theorem hTwoLife : 0 < 2 := by decide
private theorem hOneTwoLife : 1 <= 2 := by decide


private def ring2Life : DirectedRing 2 :=
  ⟨hTwoLife⟩


private instance instDecidableHostFenceShapeLifetime
    (u : R1AgentStateV6 psi kappa tau) :
    Decidable (HostFenceShapeV7 u) := by
  unfold HostFenceShapeV7
  infer_instance


private instance instDecidableTicketShapeLifetime
    (u : R1AgentStateV6 psi kappa tau) :
    Decidable (TicketShapeV7 u) := by
  unfold TicketShapeV7 HostFenceShapeV7 ReservedFrontHoldGuard
  infer_instance


private instance instDecidablePreparedDangerLifetime
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (C : R1ConfigV6 n psi kappa tau) (e : Fin n) :
    Decidable (PreparedDangerAt hpsi ring (projectV6 C) e) := by
  unfold PreparedDangerAt PreparedBarrierAt projectV6
  dsimp only
  unfold isBarrier
  infer_instance


private instance instDecidableProtectedSpliceEdgeLifetime
    (ring : DirectedRing n)
    (C : R1ConfigV6 n psi kappa tau) (e : Fin n) :
    Decidable (ProtectedSpliceEdgeV7 ring C e) := by
  unfold ProtectedSpliceEdgeV7 R1ProtectedSpliceEdgeV3
    HostFenceShapeV7 ReservedFrontHoldGuard projectV6
  dsimp only
  infer_instance


private instance instDecidableProvenanceSafeLifetime
    (ring : DirectedRing n)
    (C : R1ConfigV6 n psi kappa tau) :
    Decidable (ProvenanceSafeV7 ring C) := by
  unfold ProvenanceSafeV7
  infer_instance


private instance instDecidableSpliceSafeLifetime
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (C : R1ConfigV6 n psi kappa tau) :
    Decidable (SpliceSafeV7 hpsi ring C) := by
  unfold SpliceSafeV7
  infer_instance


private instance instDecidableLocalPreparedBarrierLifetime
    (hpsi : 0 < psi)
    (l r : R1AgentStateV6 psi kappa tau) :
    Decidable (LocalPreparedBarrier hpsi l.carrier r.carrier) := by
  unfold LocalPreparedBarrier
  dsimp only
  unfold isBarrier
  infer_instance


private instance instDecidableHostFenceTargetClearLifetime
    (u : R1AgentStateV6 psi kappa tau) :
    Decidable (HostFenceTargetClearV7 u) := by
  unfold HostFenceTargetClearV7
  infer_instance


/-- Start from the existing two-site q11681 SEEK geometry.  Replace site 0's
controller mark by a neutral host fence, preserving its physical state; leave
the busy reserved front at site 1 unchanged. -/
def fenceLivelock2 : R1ConfigV6 2 2 0 0 := fun i =>
  if i = (0 : Fin 2) then
    setTicketV6 (setControlV6 (q11681Start2V6 i) .none false) true
  else
    q11681Start2V6 i


/-- Smallest non-singleton literal global livelock.


* edge 0: left host fence + prepared barrier + busy target -> left-fence HOLD;
* edge 1: the right endpoint is the host fence -> right-fence HOLD.


The whole configuration is nevertheless SpliceSafeV7. -/
theorem fenceLivelock2_literal :
    SpliceSafeV7 hTwoLife ring2Life fenceLivelock2 /\
    not (RolesClearV7 fenceLivelock2) /\
    HostFenceShapeV7 (fenceLivelock2 (0 : Fin 2)) /\
    LocalPreparedBarrier hTwoLife
      (fenceLivelock2 (0 : Fin 2)).carrier
      (fenceLivelock2 (1 : Fin 2)).carrier /\
    not (HostFenceTargetClearV7 (fenceLivelock2 (1 : Fin 2))) /\
    (forall e i,
      stepV8 hTwoLife hOneLife hOneTwoLife ring2Life
        fenceLivelock2 e i = fenceLivelock2 i) := by
  decide


theorem fenceLivelock2_step_fixed (e : Fin 2) :
    stepV8 hTwoLife hOneLife hOneTwoLife ring2Life fenceLivelock2 e =
      fenceLivelock2 := by
  funext i
  exact fenceLivelock2_literal.2.2.2.2.2 e i


theorem fenceLivelock2_run_fixed (u : List (Fin 2)) :
    spliceRun hTwoLife hOneLife hOneTwoLife ring2Life fenceLivelock2 u =
      fenceLivelock2 := by
  induction u with
  | nil => rfl
  | cons e u ih =>
      simp only [spliceRun]
      rw [fenceLivelock2_step_fixed]
      exact ih


theorem fenceLivelock2_life (u : List (Fin 2)) :
    spliceLife hTwoLife hOneLife hOneTwoLife ring2Life fenceLivelock2 u =
      u.length + 1 := by
  have hfalse : decide (RolesClearV7 fenceLivelock2) = false := by
    decide
  have hlive : Not (RolesClearV7 fenceLivelock2) :=
    of_decide_eq_false hfalse
  induction u with
  | nil =>
      simp [spliceLife, hlive]
  | cons e u ih =>
      have hstep :
          stepV8 hTwoLife hOneLife hOneTwoLife ring2Life fenceLivelock2 e =
            fenceLivelock2 := by
        have hrun := fenceLivelock2_run_fixed [e]
        simpa [spliceRun] using hrun
      simp [spliceLife, hlive, hstep, ih,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]


theorem fenceLivelock2_resolutionWeight_zero (u : List (Fin 2)) :
    spliceResolutionWeight hTwoLife hOneLife hOneTwoLife ring2Life
      fenceLivelock2 u = 0 := by
  unfold spliceResolutionWeight
  rw [fenceLivelock2_life]
  simp


private theorem wordSum_zero_of_zero
    {m T : Nat} (f : List (Fin m) -> Nat)
    (hf : forall u, f u = 0) :
    FixedSpanRenewalPayload.wordSum m T f = 0 := by
  induction T generalizing f with
  | zero =>
      change f [] = 0
      exact hf []
  | succ T ih =>
      rw [FixedSpanRenewalPayload.wordSum_succ]
      calc
        (List.ofFn (fun e : Fin m =>
          FixedSpanRenewalPayload.wordSum m T
            (fun u => f (e :: u)))).sum =
            (List.ofFn (fun _ : Fin m => 0)).sum := by
          apply ofFn_sum_eq
          intro e
          apply ih
          intro u
          exact hf (e :: u)
        _ = m * 0 := ofFn_sum_const m 0
        _ = 0 := Nat.mul_zero m


theorem fenceLivelock2_resolutionMass_zero (L : Nat) :
    spliceResolutionMass hTwoLife hOneLife hOneTwoLife ring2Life
      fenceLivelock2 L = 0 := by
  unfold spliceResolutionMass
  apply wordSum_zero_of_zero
  intro u
  exact fenceLivelock2_resolutionWeight_zero u


private instance instDecidableFenceLivelock2BlockMass
    (L Q : Nat) :
    Decidable (SpliceBlockMassBound hTwoLife hOneLife hOneTwoLife ring2Life
      fenceLivelock2 L Q) := by
  unfold SpliceBlockMassBound
  infer_instance


/-- Consequently no finite block and no finite `Q` can give positive uniform
completion mass on the current V8 live-state class. -/
theorem fenceLivelock2_no_block_mass (L Q : Nat) :
    not (SpliceBlockMassBound hTwoLife hOneLife hOneTwoLife ring2Life
      fenceLivelock2 L Q) := by
  have hfalse :
      decide (SpliceBlockMassBound hTwoLife hOneLife hOneTwoLife ring2Life
        fenceLivelock2 L Q) = false := by
    simp only [decide_eq_false_iff_not]
    unfold SpliceBlockMassBound
    rw [fenceLivelock2_resolutionMass_zero]
    simp
  simp [hfalse]


end B9SpliceLifetime


#print axioms B9SpliceLifetime.q11703_fence_advance_nondrain
#print axioms B9SpliceLifetime.fenceLivelock2_literal
#print axioms B9SpliceLifetime.fenceLivelock2_step_fixed
#print axioms B9SpliceLifetime.fenceLivelock2_run_fixed
#print axioms B9SpliceLifetime.fenceLivelock2_life
#print axioms B9SpliceLifetime.fenceLivelock2_resolutionMass_zero
#print axioms B9SpliceLifetime.fenceLivelock2_no_block_mass
