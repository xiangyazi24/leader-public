import Leader.Wu.PartialProtocol.MinimalLockDoubleCover
import Leader.Wu.PartialProtocol.StaleLockCounterexample

/-!
# A two-bit reset sweep above the minimal lock

The accepted Boolean lock is static: once every endpoint is locked, a copied
two-leader word is fixed.  This file adds one more Boolean phase.  `false`
means that the lock has not yet been validated by the current sweep and
`true` means sealed.  A sealed initiator, a sealed responder, or a current
initiator leader activates the edge.  The initiator is retained and sealed;
an unsealed responder is sealed after its physical leader bit is cleared.

Thus a chosen leader launches a clockwise, monotone seal wave.  The chosen
leader is sealed before the wave moves, every other leader encountered as a
responder is removed, and the final wrap edge cannot remove the already sealed
source.  On the explicit double cover of the accepted one-leader word, the
length `2*n - 1` clockwise word reaches an all-sealed one-leader kernel.

Every all-sealed pair is exact identity, so the kernel is pointwise-output
closed.  The unlocked/unsealed branch delegates to the accepted minimal-lock
transition, including its real P'_psi birth route.

This is not arbitrary-state convergence.  An adversary can initialize the new
phase to `true` everywhere, reproducing an all-sealed multi-leader fixed point.
The result proves a concrete dynamic escape from the `false`-phase lift of the
accepted double-cover trap, not provenance authentication.  The carrier is
the exact factor-four product over physical `P_partial` state: the accepted
lock bit and one new sweep bit.
-/

namespace PPLLCompleteMultiLeaderCleanup
namespace PPartialDynamicSweepLockSol

open PPLL PPLLResearchFormulation
  PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
  PPLLNoCheckBirthOutputLegitimacy PPLLNoCheckBirthConditionTwoGeometry
open PPartialMinimalLockRepairSol
open PPartialStaticDoubleCoverSol
open PPLLStaticDoubleCoverNoGo

set_option autoImplicit false

variable {n psi kappa tau : Nat}

/-! ## Carrier and executable transition -/

/-- The accepted physical state and lock bit, plus one sweep/seal bit. -/
abbrev SweepLockState (psi kappa tau : Nat) :=
  MinimalLockState psi kappa tau × Bool

abbrev SweepLockConfig (n psi kappa tau : Nat) :=
  Fin n → SweepLockState psi kappa tau

/-- Output-visible physical leader bit. -/
def sweepLockLeader (u : SweepLockState psi kappa tau) : Bool :=
  minimalLockLeader u.1

/-- Clear only the physical leader bit, retaining the complete accepted
bounded carrier, timer, authorization bit, and original lock bit. -/
def clearMinimalLockLeader
    (u : MinimalLockState psi kappa tau) :
    MinimalLockState psi kappa tau :=
  ({ u.1 with core :=
      { u.1.core with core :=
        { u.1.core.core with leader := false } } }, u.2)

@[simp] theorem clearMinimalLockLeader_leader
    (u : MinimalLockState psi kappa tau) :
    minimalLockLeader (clearMinimalLockLeader u) = false := by
  rfl

@[simp] theorem clearMinimalLockLeader_lock
    (u : MinimalLockState psi kappa tau) :
    (clearMinimalLockLeader u).2 = u.2 := by
  rfl

/-- A sealed endpoint on either side, or a current initiator leader, activates
the directed seal edge. -/
def sweepLockTrigger
    (l r : SweepLockState psi kappa tau) : Bool :=
  l.2 || r.2 || sweepLockLeader l

/-- Dynamic two-bit transition.  An active edge retains the initiator, seals
both endpoints, and clears the responder leader exactly when the responder was
not yet sealed.  Inactive pairs execute the accepted minimal-lock transition
and remain unsealed, so the existing first-birth branch is retained. -/
def P_partialSweepLock
    (hpsi : psi > 0) (kappa tau : Nat)
    (l r : SweepLockState psi kappa tau) :
    SweepLockState psi kappa tau × SweepLockState psi kappa tau :=
  if sweepLockTrigger l r then
    let rPhysical :=
      if r.2 then r.1 else clearMinimalLockLeader r.1
    ((l.1, true), (rPhysical, true))
  else
    let q := P_partialMinimalLock hpsi kappa tau l.1 r.1
    ((q.1, false), (q.2, false))

/-- Packaged protocol.  Both repair bits are output-invisible. -/
def P_partialSweepLockProtocol
    (hpsi : psi > 0) (kappa tau : Nat) : PopulationProtocol where
  Q := SweepLockState psi kappa tau
  Y := LeaderOutput
  transition := P_partialSweepLock hpsi kappa tau
  output := fun s =>
    if sweepLockLeader s then LeaderOutput.leader
    else LeaderOutput.follower

/-- The new phase is output-invisible, pointwise and without transporting
between dependent protocol configuration types. -/
theorem sweepLock_output_eq_minimalLock
    (hpsi : psi > 0) (kappa tau : Nat)
    (u : MinimalLockState psi kappa tau) (phase : Bool) :
    (P_partialSweepLockProtocol hpsi kappa tau).output (u, phase) =
      (P_partialMinimalLockProtocol hpsi kappa tau).output u := by
  rfl

/-- The bounded physical domain remains closed by construction. -/
theorem P_partialSweepLock_output_inProtocolDomain
    (hpsi : psi > 0) (kappa tau : Nat)
    (l r : SweepLockState psi kappa tau) :
    let q := P_partialSweepLock hpsi kappa tau l r
    q.1.1.1.core.erase.core.inProtocolDomain kappa ∧
      q.2.1.1.core.erase.core.inProtocolDomain kappa := by
  let q := P_partialSweepLock hpsi kappa tau l r
  exact ⟨q.1.1.1.core.core.erase_inProtocolDomain,
    q.2.1.1.core.core.erase_inProtocolDomain⟩

/-- With no phase trigger, the physical pair is exactly the accepted
minimal-lock transition. -/
theorem P_partialSweepLock_of_inactive
    (hpsi : psi > 0) (kappa tau : Nat)
    (l r : SweepLockState psi kappa tau)
    (htrigger : sweepLockTrigger l r = false) :
    P_partialSweepLock hpsi kappa tau l r =
      let q := P_partialMinimalLock hpsi kappa tau l.1 r.1
      ((q.1, false), (q.2, false)) := by
  simp [P_partialSweepLock, htrigger]

/-- A left leader in the unsealed accepted birth output can therefore launch
the dynamic phase on its next initiator interaction. -/
theorem P_partialSweepLock_of_leftLeader_rightUnsealed
    (hpsi : psi > 0) (kappa tau : Nat)
    (l r : SweepLockState psi kappa tau)
    (hleader : sweepLockLeader l = true)
    (hr : r.2 = false) :
    P_partialSweepLock hpsi kappa tau l r =
      ((l.1, true), (clearMinimalLockLeader r.1, true)) := by
  simp [P_partialSweepLock, sweepLockTrigger, hleader, hr]

/-! ## Closed, nonempty one-leader kernel -/

/-- Every endpoint has been visited by the dynamic sweep. -/
def SweepLockAllSealed
    (C : SweepLockConfig n psi kappa tau) : Prop :=
  ∀ i : Fin n, (C i).2 = true

/-- Operational kernel: a complete seal and exactly one current leader
output.  Future output stability is derived below. -/
def SweepLockLegit
    (hpsi : psi > 0) (kappa tau : Nat)
    (C : SweepLockConfig n psi kappa tau) : Prop :=
  SweepLockAllSealed C ∧
    UniqueLeaderOutput
      (P_partialSweepLockProtocol hpsi kappa tau)
      n C isLeaderOutput

/-- Two sealed inputs make the complete local transition identity. -/
theorem P_partialSweepLock_eq_self_of_sealed
    (hpsi : psi > 0) (kappa tau : Nat)
    (l r : SweepLockState psi kappa tau)
    (hl : l.2 = true) (hr : r.2 = true) :
    P_partialSweepLock hpsi kappa tau l r = (l, r) := by
  rcases l with ⟨l, lb⟩
  rcases r with ⟨r, rb⟩
  cases lb <;> cases rb <;>
    simp_all [P_partialSweepLock, sweepLockTrigger]

/-- An all-sealed configuration is a fixed point of every exact step. -/
theorem P_partialSweepLock_step_eq_of_allSealed
    (hpsi : psi > 0) (kappa tau : Nat)
    (ring : DirectedRing n)
    (C : SweepLockConfig n psi kappa tau)
    (hsealed : SweepLockAllSealed C) (e : Fin n) :
    (P_partialSweepLockProtocol hpsi kappa tau).step ring C e = C := by
  let j := ring.rightNeighbor e
  have hpair : P_partialSweepLock hpsi kappa tau (C e) (C j) =
      (C e, C j) :=
    P_partialSweepLock_eq_self_of_sealed hpsi kappa tau
      (C e) (C j) (hsealed e) (hsealed j)
  funext i
  by_cases hie : i = e
  · subst i
    simp [PopulationProtocol.step, P_partialSweepLockProtocol, j, hpair]
  · by_cases hij : i = j
    · subst i
      simp [PopulationProtocol.step, P_partialSweepLockProtocol,
        j, hie, hpair]
    · simp [PopulationProtocol.step, P_partialSweepLockProtocol,
        j, hie, hij]

/-- The one-leader kernel is closed. -/
theorem sweepLockLegit_closed
    (hpsi : psi > 0) (kappa tau : Nat)
    (ring : DirectedRing n) :
    PopulationProtocol.ClosedPred
      (P_partialSweepLockProtocol hpsi kappa tau) ring
      (SweepLockLegit hpsi kappa tau) := by
  intro C hC D hstep
  obtain ⟨e, rfl⟩ := hstep
  rw [P_partialSweepLock_step_eq_of_allSealed
    hpsi kappa tau ring C hC.1 e]
  exact hC

/-- Every step in the kernel preserves the complete pointwise output vector. -/
theorem sweepLockLegit_stepOutputPreserving
    (hpsi : psi > 0) (kappa tau : Nat)
    (ring : DirectedRing n) :
    StepOutputPreservingOn
      (P_partialSweepLockProtocol hpsi kappa tau) ring
      (SweepLockLegit hpsi kappa tau) := by
  intro C hC D hstep i
  obtain ⟨e, rfl⟩ := hstep
  rw [P_partialSweepLock_step_eq_of_allSealed
    hpsi kappa tau ring C hC.1 e]

/-- Canonical sealed lift of the accepted one-leader witness. -/
def sweepLockWitness
    (hpsi : psi > 0) (kappa tau : Nat) :
    SweepLockConfig n psi kappa tau :=
  fun i => (minimalLockWitness (n := n) hpsi kappa tau i, true)

/-- The dynamic kernel is inhabited on every nonempty ring. -/
theorem sweepLockLegit_inhabited
    (hpsi : psi > 0) (kappa tau : Nat)
    (ring : DirectedRing n) :
    SweepLockLegit hpsi kappa tau
      (sweepLockWitness (n := n) hpsi kappa tau) := by
  constructor
  · intro i
    rfl
  · obtain ⟨leader, hleader, honly⟩ :=
      minimalLockWitness_unique hpsi kappa tau ring
    refine ⟨leader, ?_, ?_⟩
    · have hout := congrArg isLeaderOutput
        (sweepLock_output_eq_minimalLock hpsi kappa tau
          (minimalLockWitness (n := n) hpsi kappa tau leader) true)
      exact hout.trans hleader
    · intro j hj
      apply honly j
      have hout := congrArg isLeaderOutput
        (sweepLock_output_eq_minimalLock hpsi kappa tau
          (minimalLockWitness (n := n) hpsi kappa tau j) true)
      exact hout.symm.trans hj

/-- Kernel membership implies Definition-1 semantic safety. -/
theorem sweepLockLegit_isSafe
    (hpsi : psi > 0) (kappa tau : Nat)
    (ring : DirectedRing n)
    {C : SweepLockConfig n psi kappa tau}
    (hC : SweepLockLegit hpsi kappa tau C) :
    PopulationProtocol.IsSafe
      (P_partialSweepLockProtocol hpsi kappa tau)
      ring C isLeaderOutput := by
  exact isSafe_of_operational_legitimacy
    (P_partialSweepLockProtocol hpsi kappa tau)
    ring isLeaderOutput
    (SweepLockLegit hpsi kappa tau)
    (sweepLockLegit_closed hpsi kappa tau ring)
    (fun _ h => h.2)
    (sweepLockLegit_stepOutputPreserving hpsi kappa tau ring)
    hC

/-! ## Exact local sweep effect -/

/-- A nontrivial ring's active edge with an unsealed responder retains and
seals the initiator, clears the responder leader, seals the responder, and
frames every other site. -/
theorem sweepLock_localStep_active_unsealed
    (hpsi : psi > 0) (kappa tau : Nat)
    (ring : DirectedRing n) (hn : 1 < n)
    (C : SweepLockConfig n psi kappa tau) (e : Fin n)
    (hactive : (C e).2 = true ∨ sweepLockLeader (C e) = true)
    (hr : (C (ring.rightNeighbor e)).2 = false) :
    let D := localStep ring
      (P_partialSweepLock hpsi kappa tau) C e
    D e = ((C e).1, true) ∧
      (D (ring.rightNeighbor e)).2 = true ∧
      sweepLockLeader (D (ring.rightNeighbor e)) = false ∧
      ∀ i : Fin n, i ≠ e → i ≠ ring.rightNeighbor e →
        D i = C i := by
  let j := ring.rightNeighbor e
  have hpair : P_partialSweepLock hpsi kappa tau (C e) (C j) =
      (((C e).1, true),
        (clearMinimalLockLeader (C j).1, true)) := by
    rcases hactive with hsealed | hleader
    · simp [P_partialSweepLock, sweepLockTrigger, hsealed, hr, j]
    · simp [P_partialSweepLock, sweepLockTrigger, hleader, hr, j]
  have hje : j ≠ e := rightNeighbor_ne_self_of_one_lt ring hn e
  dsimp only
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [localStep, j, hpair]
  · simp [localStep, j, hpair, hje]
  · simp [localStep, j, hpair, hje, sweepLockLeader]
  · intro i hie hij
    simp [localStep, j, hpair, hie, hij]

/-- Every explicit local word is an actual execution of the packaged dynamic
protocol. -/
theorem P_partialSweepLock_runLocalSchedule_reachable
    (hpsi : psi > 0) (kappa tau : Nat)
    (ring : DirectedRing n)
    (C : SweepLockConfig n psi kappa tau)
    (word : DetSchedule n) :
    PopulationProtocol.Reachable
      (P_partialSweepLockProtocol hpsi kappa tau) ring C
      (runLocalSchedule ring
        (P_partialSweepLock hpsi kappa tau) C word) := by
  induction word generalizing C with
  | nil =>
      exact @PopulationProtocol.Reachable.refl n
        (P_partialSweepLockProtocol hpsi kappa tau) ring C
  | cons e rest ih =>
      exact (PopulationProtocol.OneStep.to_reachable ⟨e, rfl⟩).trans
        (ih (localStep ring
          (P_partialSweepLock hpsi kappa tau) C e))

private theorem cwPos_ne_of_ne_below_sweep
    (ring : DirectedRing n) (start : Fin n)
    {a b : Nat} (ha : a < n) (hb : b < n) (hab : a ≠ b) :
    cwPos ring start a ≠ cwPos ring start b := by
  intro hpos
  apply hab
  have ha' := cwPos_bounded_unique ring start
    (cwPos ring start a) a ha rfl
  have hb' := cwPos_bounded_unique ring start
    (cwPos ring start a) b hb hpos.symm
  exact ha'.trans hb'.symm

/-- Prefix invariant for the explicit clockwise seal word.  After any positive
proper prefix, the source is sealed and unchanged, every positive visited
offset is sealed with leader cleared, and every site strictly ahead is still
its initial unsealed state. -/
theorem sweepLock_clockwise_prefix
    (hpsi : psi > 0) (kappa tau : Nat)
    (ring : DirectedRing n) (hn : 1 < n)
    (C : SweepLockConfig n psi kappa tau) (seed : Fin n)
    (hunsealed : ∀ i : Fin n, (C i).2 = false)
    (hseed : sweepLockLeader (C seed) = true)
    (steps : Nat) (hpos : 0 < steps) (hlt : steps < n) :
    let D := runLocalSchedule ring
      (P_partialSweepLock hpsi kappa tau) C
      (clockwiseEdgeSchedule ring seed steps)
    D seed = ((C seed).1, true) ∧
      (∀ k : Nat, 0 < k → k ≤ steps →
        (D (cwPos ring seed k)).2 = true ∧
          sweepLockLeader (D (cwPos ring seed k)) = false) ∧
      (∀ k : Nat, steps < k → k < n →
        D (cwPos ring seed k) = C (cwPos ring seed k)) := by
  induction steps with
  | zero => omega
  | succ s ih =>
      cases s with
      | zero =>
          let e := seed
          let j := ring.rightNeighbor e
          have hedge := sweepLock_localStep_active_unsealed
            hpsi kappa tau ring hn C e (Or.inr hseed)
              (by simpa [e, j] using hunsealed j)
          have hrun :
              runLocalSchedule ring
                  (P_partialSweepLock hpsi kappa tau) C
                  (clockwiseEdgeSchedule ring seed 1) =
                localStep ring
                  (P_partialSweepLock hpsi kappa tau) C e := by
            simp [clockwiseEdgeSchedule, runLocalSchedule, e]
          rw [hrun]
          constructor
          · simpa [e] using hedge.1
          constructor
          · intro k hk hkle
            have hk1 : k = 1 := by omega
            subst k
            have hjpos : j = cwPos ring seed 1 := by
              simpa [j, e] using (cwPos_succ ring seed 0).symm
            rw [← hjpos]
            exact ⟨hedge.2.1, hedge.2.2.1⟩
          · intro k hk hkn
            have hke : cwPos ring seed k ≠ e := by
              simpa [e] using cwPos_ne_of_ne_below_sweep
                ring seed hkn (by omega : 0 < n) (by omega)
            have hkj : cwPos ring seed k ≠ j := by
              have hjpos : j = cwPos ring seed 1 := by
                simpa [j, e] using (cwPos_succ ring seed 0).symm
              rw [hjpos]
              exact cwPos_ne_of_ne_below_sweep
                ring seed hkn (by omega) (by omega)
            exact hedge.2.2.2 (cwPos ring seed k) hke hkj
      | succ s =>
          have hprev := ih (by omega) (by omega)
          let D := runLocalSchedule ring
            (P_partialSweepLock hpsi kappa tau) C
            (clockwiseEdgeSchedule ring seed (s + 1))
          change D seed = ((C seed).1, true) ∧
              (∀ k : Nat, 0 < k → k ≤ s + 1 →
                (D (cwPos ring seed k)).2 = true ∧
                  sweepLockLeader (D (cwPos ring seed k)) = false) ∧
              (∀ k : Nat, s + 1 < k → k < n →
                D (cwPos ring seed k) = C (cwPos ring seed k)) at hprev
          let e := cwPos ring seed (s + 1)
          let j := ring.rightNeighbor e
          have hjpos : j = cwPos ring seed (s + 2) := by
            simpa [j, e, Nat.add_assoc] using
              (cwPos_succ ring seed (s + 1)).symm
          have hDj : D j = C j := by
            rw [hjpos]
            exact hprev.2.2 (s + 2) (by omega) hlt
          have hedge := sweepLock_localStep_active_unsealed
            hpsi kappa tau ring hn D e
              (Or.inl (by
                simpa [e] using (hprev.2.1 (s + 1)
                  (by omega) (Nat.le_refl _)).1))
              (by rw [hDj]; exact hunsealed j)
          let E := localStep ring
            (P_partialSweepLock hpsi kappa tau) D e
          have hrun :
              runLocalSchedule ring
                  (P_partialSweepLock hpsi kappa tau) C
                  (clockwiseEdgeSchedule ring seed (s + 2)) = E := by
            change runLocalSchedule ring
                (P_partialSweepLock hpsi kappa tau) C
                (clockwiseEdgeSchedule ring seed (s + 1) ++ [e]) = _
            rw [PPLLSchedulerBlocks.runLocalSchedule_append]
            rfl
          rw [hrun]
          constructor
          · have hse : seed ≠ e := by
              have hzero : 0 < n := by omega
              have heoff : s + 1 < n := by omega
              have hne : (0 : Nat) ≠ s + 1 := by omega
              simpa [e] using cwPos_ne_of_ne_below_sweep
                ring seed hzero heoff hne
            have hsj : seed ≠ j := by
              have hzero : 0 < n := by omega
              have hne : (0 : Nat) ≠ s + 2 := by omega
              rw [hjpos]
              simpa using cwPos_ne_of_ne_below_sweep
                ring seed hzero hlt hne
            exact (hedge.2.2.2 seed hse hsj).trans hprev.1
          constructor
          · intro k hk hkle
            by_cases hnew : k = s + 2
            · subst k
              rw [← hjpos]
              exact ⟨hedge.2.1, hedge.2.2.1⟩
            have hkprev : k ≤ s + 1 := by omega
            by_cases hcurrent : k = s + 1
            · subst k
              have heq := hedge.1
              change (E e).2 = true ∧
                sweepLockLeader (E e) = false
              constructor
              · exact congrArg (fun u => u.2) heq
              · have hout := congrArg sweepLockLeader heq
                have hold :=
                  (hprev.2.1 (s + 1) (by omega) (Nat.le_refl _)).2
                have hepos : e = cwPos ring seed (s + 1) := by
                  rfl
                have hold' : sweepLockLeader (D e) = false := by
                  rw [hepos]
                  exact hold
                have hout' : sweepLockLeader (E e) =
                    sweepLockLeader (D e) := by
                  simpa [sweepLockLeader] using hout
                exact hout'.trans hold'
            · have hke : cwPos ring seed k ≠ e := by
                have hklt : k < n := by omega
                have helt : s + 1 < n := by omega
                simpa [e] using cwPos_ne_of_ne_below_sweep
                  ring seed hklt helt hcurrent
              have hkj : cwPos ring seed k ≠ j := by
                have hklt : k < n := by omega
                have hne : k ≠ s + 2 := hnew
                rw [hjpos]
                exact cwPos_ne_of_ne_below_sweep
                  ring seed hklt hlt hne
              have hoff := hedge.2.2.2
                (cwPos ring seed k) hke hkj
              have hold := hprev.2.1 k hk hkprev
              exact ⟨(congrArg (fun u => u.2) hoff).trans hold.1,
                (congrArg sweepLockLeader hoff).trans hold.2⟩
          · intro k hk hkn
            have hke : cwPos ring seed k ≠ e := by
              have helt : s + 1 < n := by omega
              have hne : k ≠ s + 1 := by omega
              simpa [e] using cwPos_ne_of_ne_below_sweep
                ring seed hkn helt hne
            have hkj : cwPos ring seed k ≠ j := by
              have hne : k ≠ s + 2 := by omega
              rw [hjpos]
              exact cwPos_ne_of_ne_below_sweep
                ring seed hkn hlt hne
            exact (hedge.2.2.2 (cwPos ring seed k) hke hkj).trans
              (hprev.2.2 k (by omega) hkn)

/-! ## The accepted double cover has a concrete escape word -/

/-- Add an initially false sweep bit to the exact accepted double cover. -/
def unsealedMinimalLockDoubleCover
    (hpsi : psi > 0) (kappa tau : Nat) (hn : n > 0) :
    SweepLockConfig (2 * n) psi kappa tau :=
  fun i =>
    (doubleCoverConfig
      (P_partialMinimalLockProtocol hpsi kappa tau) hn
      (minimalLockWitness (n := n) hpsi kappa tau) i,
      false)

/-- The lifted starting configuration still contains the two copied leader
outputs proved by the accepted static double-cover theorem. -/
theorem unsealedMinimalLockDoubleCover_hasTwoLeaders
    (hpsi : psi > 0) (kappa tau : Nat) (hn : n > 0) :
    HasTwoLeaderOutputs
      (P_partialSweepLockProtocol hpsi kappa tau)
      isLeaderOutput
      (unsealedMinimalLockDoubleCover hpsi kappa tau hn) := by
  have htwo :=
    (minimalLock_static_double_cover_no_go hpsi kappa tau hn).2.1
  have hword :
      (minimalLockProtectedWord hpsi kappa tau hn).config =
        minimalLockWitness (n := n) hpsi kappa tau := by
    rfl
  rw [hword] at htwo
  rcases htwo with ⟨i, j, hij, hi, hj⟩
  refine ⟨i, j, hij, ?_, ?_⟩
  · have hout := congrArg isLeaderOutput
        (sweepLock_output_eq_minimalLock hpsi kappa tau
          (doubleCoverConfig
            (P_partialMinimalLockProtocol hpsi kappa tau) hn
            (minimalLockWitness (n := n) hpsi kappa tau) i) false)
    exact hout.trans hi
  · have hout := congrArg isLeaderOutput
        (sweepLock_output_eq_minimalLock hpsi kappa tau
          (doubleCoverConfig
            (P_partialMinimalLockProtocol hpsi kappa tau) hn
            (minimalLockWitness (n := n) hpsi kappa tau) j) false)
    exact hout.trans hj

/-- Any initially unsealed nontrivial ring with a chosen current leader reaches
the closed one-leader kernel by the literal clockwise word of length `n - 1`.
All other current leaders are removed when first visited as responders. -/
theorem unsealedLeader_clockwise_reaches_legit
    (hpsi : psi > 0) (kappa tau : Nat)
    (ring : DirectedRing n) (hn : 1 < n)
    (C : SweepLockConfig n psi kappa tau)
    (hunsealed : ∀ i : Fin n, (C i).2 = false)
    (seed : Fin n) (hseed : sweepLockLeader (C seed) = true) :
    SweepLockLegit hpsi kappa tau
      (runLocalSchedule ring
        (P_partialSweepLock hpsi kappa tau) C
        (clockwiseEdgeSchedule ring seed (n - 1))) := by
  have hpos : 0 < n - 1 := by omega
  have hlt : n - 1 < n := by omega
  have hp := sweepLock_clockwise_prefix
    hpsi kappa tau ring hn C seed hunsealed hseed
      (n - 1) hpos hlt
  let D := runLocalSchedule ring
    (P_partialSweepLock hpsi kappa tau) C
    (clockwiseEdgeSchedule ring seed (n - 1))
  change D seed = ((C seed).1, true) ∧
      (∀ k : Nat, 0 < k → k ≤ n - 1 →
        (D (cwPos ring seed k)).2 = true ∧
          sweepLockLeader (D (cwPos ring seed k)) = false) ∧
      (∀ k : Nat, n - 1 < k → k < n →
        D (cwPos ring seed k) = C (cwPos ring seed k)) at hp
  constructor
  · intro i
    let d := cwDist ring seed i
    have hdlt : d < n := cwDist_lt ring seed i
    have hdle : d ≤ n - 1 := by omega
    by_cases hi : i = seed
    · subst i
      exact congrArg (fun u => u.2) hp.1
    · have hdpos : 0 < d := by
        have hdne : d ≠ 0 := by
          intro hd0
          have hd0' : cwDist ring seed i = 0 := by
            simpa [d] using hd0
          have hreach := cwPos_cwDist ring seed i
          rw [hd0', cwPos_zero] at hreach
          exact hi hreach.symm
        omega
      rw [← cwPos_cwDist ring seed i]
      exact (hp.2.1 d hdpos hdle).1
  · refine ⟨seed, ?_, ?_⟩
    · have hslead : sweepLockLeader (D seed) = true := by
        have hs := congrArg sweepLockLeader hp.1
        have hs' : sweepLockLeader (D seed) =
            sweepLockLeader (C seed) := by
          simpa [sweepLockLeader] using hs
        exact hs'.trans hseed
      change isLeaderOutput
        (if sweepLockLeader (D seed) then LeaderOutput.leader
          else LeaderOutput.follower) = true
      rw [hslead]
      rfl
    · intro i hiout
      by_cases his : i = seed
      · exact his
      exfalso
      let d := cwDist ring seed i
      have hdlt : d < n := cwDist_lt ring seed i
      have hdle : d ≤ n - 1 := by omega
      have hdpos : 0 < d := by
        have hdne : d ≠ 0 := by
          intro hd0
          have hd0' : cwDist ring seed i = 0 := by
            simpa [d] using hd0
          have hreach := cwPos_cwDist ring seed i
          rw [hd0', cwPos_zero] at hreach
          exact his hreach.symm
        omega
      have hfalse : sweepLockLeader (D i) = false := by
        rw [← cwPos_cwDist ring seed i]
        exact (hp.2.1 d hdpos hdle).2
      change isLeaderOutput
        (if sweepLockLeader (D i) then LeaderOutput.leader
          else LeaderOutput.follower) = true at hiout
      simp [hfalse, isLeaderOutput] at hiout

/-- The exact false-phase lift of the accepted double cover has two leaders,
yet a concrete `2*n - 1`-edge clockwise schedule reaches the closed kernel.
This is the promised dynamic escape and contains no convergence premise. -/
theorem minimalLockDoubleCover_dynamic_escape
    (hpsi : psi > 0) (kappa tau : Nat) (hn : n > 0) :
    let ring := doubleRing hn
    let C := unsealedMinimalLockDoubleCover hpsi kappa tau hn
    HasTwoLeaderOutputs
        (P_partialSweepLockProtocol hpsi kappa tau)
        isLeaderOutput C ∧
      ∃ seed : Fin (2 * n),
        let word := clockwiseEdgeSchedule ring seed (2 * n - 1)
        word.length = 2 * n - 1 ∧
          PopulationProtocol.Reachable
            (P_partialSweepLockProtocol hpsi kappa tau)
            ring C
            (runLocalSchedule ring
              (P_partialSweepLock hpsi kappa tau) C word) ∧
          SweepLockLegit hpsi kappa tau
            (runLocalSchedule ring
              (P_partialSweepLock hpsi kappa tau) C word) := by
  dsimp only
  let ring := doubleRing hn
  let C := unsealedMinimalLockDoubleCover hpsi kappa tau hn
  have htwo := unsealedMinimalLockDoubleCover_hasTwoLeaders
    hpsi kappa tau hn
  refine ⟨htwo, ?_⟩
  rcases htwo with ⟨seed, other, hne, hseedOut, hotherOut⟩
  refine ⟨seed, ?_⟩
  change
    (clockwiseEdgeSchedule ring seed (2 * n - 1)).length =
        2 * n - 1 ∧
      PopulationProtocol.Reachable
        (P_partialSweepLockProtocol hpsi kappa tau)
        ring C
        (runLocalSchedule ring
          (P_partialSweepLock hpsi kappa tau) C
          (clockwiseEdgeSchedule ring seed (2 * n - 1))) ∧
      SweepLockLegit hpsi kappa tau
        (runLocalSchedule ring
          (P_partialSweepLock hpsi kappa tau) C
          (clockwiseEdgeSchedule ring seed (2 * n - 1)))
  refine ⟨clockwiseEdgeSchedule_length ring seed (2 * n - 1), ?_, ?_⟩
  · exact P_partialSweepLock_runLocalSchedule_reachable
      hpsi kappa tau ring C
      (clockwiseEdgeSchedule ring seed (2 * n - 1))
  · have hseed : sweepLockLeader (C seed) = true := by
      change isLeaderOutput
        (if sweepLockLeader (C seed) then LeaderOutput.leader
          else LeaderOutput.follower) = true at hseedOut
      cases h : sweepLockLeader (C seed)
      · simp [h, isLeaderOutput] at hseedOut
      · rfl
    exact unsealedLeader_clockwise_reaches_legit
      hpsi kappa tau ring (by omega) C
      (by intro i; rfl) seed hseed

/-! ## Exact factor-four finite carrier -/

/-- Constructive exhaustive certificate for the two-bit product carrier. -/
def sweepLockStateCertificate (psi kappa tau : Nat) :
    ExhaustiveList (SweepLockState psi kappa tau) :=
  ExhaustiveList.prod
    (minimalLockStateCertificate psi kappa tau)
    ExhaustiveList.bool

/-- The dynamic repair has exactly four times as many local states as physical
`P_partial`, and exactly twice as many as the accepted one-bit repair. -/
theorem sweepLockStateCertificate_values_length
    (psi kappa tau : Nat) :
    (sweepLockStateCertificate psi kappa tau).values.length =
      ((2 * (PPLLFinite.boundedAgentState psi kappa).values.length) *
        (tau + 1)) * 4 := by
  unfold sweepLockStateCertificate
  rw [ExhaustiveList.values_length_prod,
    minimalLockStateCertificate_values_length,
    ExhaustiveList.values_length_bool]
  omega

end PPartialDynamicSweepLockSol
end PPLLCompleteMultiLeaderCleanup
