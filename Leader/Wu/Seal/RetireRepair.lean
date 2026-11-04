import Leader.Wu.Seal.PositiveLanding

/-!
# Factor-one zero-leader repair for the seal overlay

`P_partialSealSweep` has a complete positive-leader landing theorem, but an
all-closed zero-leader configuration is an identity trap.  A direct birth on
a closed follower/follower pair would also destroy the existing all-closed
unique-leader safety kernel: a remote follower/follower edge cannot see the
leader.

This module instead reuses the existing outer Boolean as a one-way retirement
bit.  `true` means unprocessed and `false` means permanently retired.  A
closed follower/follower interaction creates one initiator leader and retires
both endpoints.  A retired follower then advances clockwise across an
unprocessed responder, retiring it and clearing its leader if necessary.
Pairs whose endpoints are both retired are exact identity.  Thus a serialized
clockwise word turns every site retired and leaves exactly one leader; the
resulting all-retired unique-output configuration is Definition-1 safe under
every future schedule.

No state is added: the carrier is definitionally `SealSweepState`, hence still
the accepted factor-four carrier over physical `P_partial`.  The theorem here
closes the exact zero-count side of the all-closed split.  The positive side is
handled separately by `PPartialSealSweepPositiveLandingSol`; combining the two
requires using this retiring transition throughout, rather than treating a
safe configuration for one transition as safe for the other.
-/

namespace PPLLCompleteMultiLeaderCleanup
namespace PPartialSealSweepZeroLeaderRepairSol

open PPLL PPLLResearchFormulation
  PPLLNoCheckBirthConditionTwoGeometry
open PPLLStaticDoubleCoverNoGo
open PPartialMinimalLockRepairSol
open PPartialDynamicSweepLockSol
open PPartialDynamicSweepResetSol
open PPartialSealSweepOverlaySol
open PPartialSealSweepPositiveLandingSol

set_option autoImplicit false

variable {n psi kappa tau : Nat}

/-! ## Exact factor-one transition -/

/-- Set only the physical leader bit, retaining every bounded physical field,
authorization field, timer, and both existing repair bits. -/
def setMinimalLockLeader
    (u : MinimalLockState psi kappa tau) :
    MinimalLockState psi kappa tau :=
  ({ u.1 with core :=
      { u.1.core with core :=
        { u.1.core.core with leader := true } } }, u.2)

@[simp] theorem setMinimalLockLeader_leader
    (u : MinimalLockState psi kappa tau) :
    minimalLockLeader (setMinimalLockLeader u) = true := by
  rfl

@[simp] theorem setMinimalLockLeader_lock
    (u : MinimalLockState psi kappa tau) :
    (setMinimalLockLeader u).2 = u.2 := by
  rfl

/-- The zero-leader repair on exactly the R82 carrier.

The first case freezes the terminal all-retired region.  The next case is the
only new birth.  The following two cases advance a retired follower frontier,
clearing a responder leader if present.  Every remaining pair delegates to
the accepted seal overlay. -/
def P_partialSealRetire
    (l r : SealSweepState psi kappa tau) :
    SealSweepState psi kappa tau × SealSweepState psi kappa tau :=
  match l.2, r.2, sweepLockLeader l, sweepLockLeader r with
  | false, false, _, _ => (l, r)
  | true, true, false, false =>
      ((setMinimalLockLeader l.1, false), (r.1, false))
  | false, true, false, false =>
      (l, (r.1, false))
  | false, true, false, true =>
      (l, (clearMinimalLockLeader r.1, false))
  | _, _, _, _ => P_partialSealSweep l r

/-- Packaged factor-one protocol. -/
def P_partialSealRetireProtocol
    (psi kappa tau : Nat) : PopulationProtocol where
  Q := SealSweepState psi kappa tau
  Y := LeaderOutput
  transition := P_partialSealRetire
  output := fun s =>
    if sweepLockLeader s then LeaderOutput.leader
    else LeaderOutput.follower

/-- Output remains exactly the R82 output map. -/
theorem sealRetire_output_eq_sealSweep
    (u : SealSweepState psi kappa tau) :
    (P_partialSealRetireProtocol psi kappa tau).output u =
      (P_partialSealSweepProtocol psi kappa tau).output u := by
  rfl

/-- Physical bounded-domain closure is unchanged. -/
theorem P_partialSealRetire_output_inProtocolDomain
    (l r : SealSweepState psi kappa tau) :
    let q := P_partialSealRetire l r
    q.1.1.1.core.erase.core.inProtocolDomain kappa ∧
      q.2.1.1.core.erase.core.inProtocolDomain kappa := by
  let q := P_partialSealRetire l r
  exact ⟨q.1.1.1.core.core.erase_inProtocolDomain,
    q.2.1.1.core.core.erase_inProtocolDomain⟩

theorem P_partialSealRetire_birth
    (l r : SealSweepState psi kappa tau)
    (hlc : l.2 = true) (hrc : r.2 = true)
    (hl : sweepLockLeader l = false)
    (hr : sweepLockLeader r = false) :
    P_partialSealRetire l r =
      ((setMinimalLockLeader l.1, false), (r.1, false)) := by
  simp [P_partialSealRetire, hlc, hrc, hl, hr]

theorem P_partialSealRetire_advance_follower
    (l r : SealSweepState psi kappa tau)
    (hlc : l.2 = false) (hrc : r.2 = true)
    (hl : sweepLockLeader l = false)
    (hr : sweepLockLeader r = false) :
    P_partialSealRetire l r = (l, (r.1, false)) := by
  simp [P_partialSealRetire, hlc, hrc, hl, hr]

theorem P_partialSealRetire_advance_leader
    (l r : SealSweepState psi kappa tau)
    (hlc : l.2 = false) (hrc : r.2 = true)
    (hl : sweepLockLeader l = false)
    (hr : sweepLockLeader r = true) :
    P_partialSealRetire l r =
      (l, (clearMinimalLockLeader r.1, false)) := by
  simp [P_partialSealRetire, hlc, hrc, hl, hr]

/-- A closed source leader launches exactly the accepted open anchor/frontier
pair. -/
theorem P_partialSealRetire_launch
    (l r : SealSweepState psi kappa tau)
    (hlc : l.2 = true) (hrc : r.2 = true)
    (hl : sweepLockLeader l = true)
    (hr : sweepLockLeader r = false) :
    P_partialSealRetire l r = ((l.1, false), (r.1, false)) := by
  simp [P_partialSealRetire, hlc, hrc, hl, hr,
    P_partialSealSweep]

/-- A closed adjacent-leader collision is unchanged from R82/R86. -/
theorem P_partialSealRetire_twoClosedLeaders
    (l r : SealSweepState psi kappa tau)
    (hlc : l.2 = true) (hrc : r.2 = true)
    (hl : sweepLockLeader l = true)
    (hr : sweepLockLeader r = true) :
    P_partialSealRetire l r =
      ((l.1, true), (clearMinimalLockLeader r.1, true)) := by
  simp [P_partialSealRetire, hlc, hrc, hl, hr,
    P_partialSealSweep]

/-- Every pair in the terminal retired region is exact identity. -/
theorem P_partialSealRetire_eq_self_of_open
    (l r : SealSweepState psi kappa tau)
    (hl : l.2 = false) (hr : r.2 = false) :
    P_partialSealRetire l r = (l, r) := by
  cases hll : sweepLockLeader l <;> cases hrl : sweepLockLeader r <;>
    simp [P_partialSealRetire, hl, hr, hll, hrl]

/-! ## The all-retired safety kernel -/

/-- Every site has permanently left the initialization/sweep region. -/
def SealRetireAllOpen
    (C : SealSweepConfig n psi kappa tau) : Prop :=
  ∀ i : Fin n, (C i).2 = false

private theorem sealRetire_step_eq_of_pair_eq
    (ring : DirectedRing n)
    (C : SealSweepConfig n psi kappa tau) (e : Fin n)
    (hpair : P_partialSealRetire (C e)
        (C (ring.rightNeighbor e)) =
      (C e, C (ring.rightNeighbor e))) :
    localStep ring P_partialSealRetire C e = C := by
  funext i
  by_cases hie : i = e
  · subst i
    simp [localStep, hpair]
  · by_cases hij : i = ring.rightNeighbor e
    · subst i
      simp [localStep, hie, hpair]
    · simp [localStep, hie, hij, hpair]

/-- An all-retired configuration is a fixed point under every edge, including
the left-biased self-edge of the one-agent ring. -/
theorem sealRetireAllOpen_step_eq
    (ring : DirectedRing n)
    (C : SealSweepConfig n psi kappa tau)
    (hopen : SealRetireAllOpen C) (e : Fin n) :
    localStep ring P_partialSealRetire C e = C := by
  apply sealRetire_step_eq_of_pair_eq ring C e
  exact P_partialSealRetire_eq_self_of_open
    (C e) (C (ring.rightNeighbor e))
    (hopen e) (hopen (ring.rightNeighbor e))

/-- Reachability from the all-retired region is literal equality. -/
theorem sealRetireAllOpen_reachable_eq
    (ring : DirectedRing n)
    (C D : SealSweepConfig n psi kappa tau)
    (hopen : SealRetireAllOpen C)
    (hreach : PopulationProtocol.Reachable
      (P_partialSealRetireProtocol psi kappa tau) ring C D) :
    D = C := by
  have hsingleton :
      PopulationProtocol.ClosedPred
        (P_partialSealRetireProtocol psi kappa tau) ring
        (fun X => X = C) := by
    intro X hX Y hstep
    subst X
    obtain ⟨e, rfl⟩ := hstep
    change localStep ring P_partialSealRetire C e = C
    exact sealRetireAllOpen_step_eq ring C hopen e
  exact hsingleton.reachable rfl hreach

/-- All-retired uniqueness is a genuine Definition-1 safety kernel. -/
theorem allOpenUnique_isSafe
    (ring : DirectedRing n)
    (C : SealSweepConfig n psi kappa tau)
    (hopen : SealRetireAllOpen C)
    (hunique : UniqueLeaderOutput
      (P_partialSealRetireProtocol psi kappa tau) n C isLeaderOutput) :
    PopulationProtocol.IsSafe
      (P_partialSealRetireProtocol psi kappa tau) ring C
      isLeaderOutput := by
  constructor
  · exact hunique
  · intro D hreach i
    rw [sealRetireAllOpen_reachable_eq ring C D hopen hreach]

/-! ## Serialized zero-leader sweep on nontrivial rings -/

private theorem cwPos_ne_of_ne_below_sealRetire
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

theorem P_partialSealRetire_runLocalSchedule_reachable
    (ring : DirectedRing n)
    (C : SealSweepConfig n psi kappa tau)
    (word : DetSchedule n) :
    PopulationProtocol.Reachable
      (P_partialSealRetireProtocol psi kappa tau) ring C
      (runLocalSchedule ring P_partialSealRetire C word) := by
  induction word generalizing C with
  | nil =>
      exact @PopulationProtocol.Reachable.refl n
        (P_partialSealRetireProtocol psi kappa tau) ring C
  | cons e rest ih =>
      exact (PopulationProtocol.OneStep.to_reachable ⟨e, rfl⟩).trans
        (ih (localStep ring P_partialSealRetire C e))

/-- One birth edge on a nontrivial ring creates an open leader at the
initiator, an open follower at the responder, and frames every other site. -/
theorem sealRetire_localStep_birth
    (ring : DirectedRing n) (hn : 1 < n)
    (C : SealSweepConfig n psi kappa tau) (e : Fin n)
    (hclosed : SealSweepAllClosed C)
    (hzero : ∀ i : Fin n, sweepLockLeader (C i) = false) :
    let D := localStep ring P_partialSealRetire C e
    D e = (setMinimalLockLeader (C e).1, false) ∧
      D (ring.rightNeighbor e) =
        ((C (ring.rightNeighbor e)).1, false) ∧
      ∀ i : Fin n, i ≠ e → i ≠ ring.rightNeighbor e →
        D i = C i := by
  let j := ring.rightNeighbor e
  have hje : j ≠ e := rightNeighbor_ne_self_of_one_lt ring hn e
  have hpair : P_partialSealRetire (C e) (C j) =
      ((setMinimalLockLeader (C e).1, false), ((C j).1, false)) :=
    P_partialSealRetire_birth (C e) (C j)
      (hclosed e) (hclosed j) (hzero e) (hzero j)
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · simp [localStep, j, hpair]
  · simp [localStep, j, hpair, hje]
  · intro i hie hij
    simp [localStep, j, hpair, hie, hij]

/-- A retired follower advances into an unprocessed follower while leaving
the old site retired. -/
theorem sealRetire_localStep_advanceFollower
    (ring : DirectedRing n) (hn : 1 < n)
    (C : SealSweepConfig n psi kappa tau) (e : Fin n)
    (hleader : sweepLockLeader (C e) = false)
    (hopen : (C e).2 = false)
    (hrleader : sweepLockLeader (C (ring.rightNeighbor e)) = false)
    (hrclosed : (C (ring.rightNeighbor e)).2 = true) :
    let D := localStep ring P_partialSealRetire C e
    D e = C e ∧
      D (ring.rightNeighbor e) =
        ((C (ring.rightNeighbor e)).1, false) ∧
      ∀ i : Fin n, i ≠ e → i ≠ ring.rightNeighbor e →
        D i = C i := by
  let j := ring.rightNeighbor e
  have hje : j ≠ e := rightNeighbor_ne_self_of_one_lt ring hn e
  have hpair : P_partialSealRetire (C e) (C j) =
      (C e, ((C j).1, false)) :=
    P_partialSealRetire_advance_follower (C e) (C j)
      hopen hrclosed hleader hrleader
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · simp [localStep, j, hpair]
  · simp [localStep, j, hpair, hje]
  · intro i hie hij
    simp [localStep, j, hpair, hie, hij]

/-- A closed source leader launches a retired source and retired follower
frontier. -/
theorem sealRetire_localStep_launch
    (ring : DirectedRing n) (hn : 1 < n)
    (C : SealSweepConfig n psi kappa tau) (e : Fin n)
    (hleader : sweepLockLeader (C e) = true)
    (hclosed : (C e).2 = true)
    (hrleader : sweepLockLeader (C (ring.rightNeighbor e)) = false)
    (hrclosed : (C (ring.rightNeighbor e)).2 = true) :
    let D := localStep ring P_partialSealRetire C e
    D e = ((C e).1, false) ∧
      D (ring.rightNeighbor e) =
        ((C (ring.rightNeighbor e)).1, false) ∧
      ∀ i : Fin n, i ≠ e → i ≠ ring.rightNeighbor e →
        D i = C i := by
  let j := ring.rightNeighbor e
  have hje : j ≠ e := rightNeighbor_ne_self_of_one_lt ring hn e
  have hpair : P_partialSealRetire (C e) (C j) =
      (((C e).1, false), ((C j).1, false)) :=
    P_partialSealRetire_launch (C e) (C j)
      hclosed hrclosed hleader hrleader
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · simp [localStep, j, hpair]
  · simp [localStep, j, hpair, hje]
  · intro i hie hij
    simp [localStep, j, hpair, hie, hij]

/-- A retired follower crosses any closed responder, retiring it and making
its output follower.  The old frontier stays retired. -/
theorem sealRetire_localStep_advance
    (ring : DirectedRing n) (hn : 1 < n)
    (C : SealSweepConfig n psi kappa tau) (e : Fin n)
    (hleader : sweepLockLeader (C e) = false)
    (hopen : (C e).2 = false)
    (hrclosed : (C (ring.rightNeighbor e)).2 = true) :
    let D := localStep ring P_partialSealRetire C e
    D e = C e ∧
      (D (ring.rightNeighbor e)).2 = false ∧
      sweepLockLeader (D (ring.rightNeighbor e)) = false ∧
      ∀ i : Fin n, i ≠ e → i ≠ ring.rightNeighbor e →
        D i = C i := by
  let j := ring.rightNeighbor e
  have hje : j ≠ e := rightNeighbor_ne_self_of_one_lt ring hn e
  cases hrleader : sweepLockLeader (C j) with
  | false =>
      have hpair : P_partialSealRetire (C e) (C j) =
          (C e, ((C j).1, false)) :=
        P_partialSealRetire_advance_follower (C e) (C j)
          hopen hrclosed hleader hrleader
      dsimp only
      refine ⟨?_, ?_, ?_, ?_⟩
      · simp [localStep, j, hpair]
      · simp [localStep, j, hpair, hje]
      · simpa [localStep, j, hpair, hje, sweepLockLeader]
          using hrleader
      · intro i hie hij
        simp [localStep, j, hpair, hie, hij]
  | true =>
      have hpair : P_partialSealRetire (C e) (C j) =
          (C e, (clearMinimalLockLeader (C j).1, false)) :=
        P_partialSealRetire_advance_leader (C e) (C j)
          hopen hrclosed hleader hrleader
      dsimp only
      refine ⟨?_, ?_, ?_, ?_⟩
      · simp [localStep, j, hpair]
      · simp [localStep, j, hpair, hje]
      · simp [localStep, j, hpair, hje, sweepLockLeader]
      · intro i hie hij
        simp [localStep, j, hpair, hie, hij]

/-- Proper-prefix invariant for the zero-leader word.  The source is the
new open leader, every positive visited offset is its original physical
follower with the retirement bit open, and every later offset is untouched. -/
theorem sealRetire_zero_clockwise_prefix
    (ring : DirectedRing n) (hn : 1 < n)
    (C : SealSweepConfig n psi kappa tau) (seed : Fin n)
    (hclosed : SealSweepAllClosed C)
    (hzero : ∀ i : Fin n, sweepLockLeader (C i) = false)
    (steps : Nat) (hpos : 0 < steps) (hlt : steps < n) :
    let D := runLocalSchedule ring P_partialSealRetire C
      (clockwiseEdgeSchedule ring seed steps)
    D seed = (setMinimalLockLeader (C seed).1, false) ∧
      (∀ k : Nat, 0 < k → k ≤ steps →
        D (cwPos ring seed k) = ((C (cwPos ring seed k)).1, false)) ∧
      (∀ k : Nat, steps < k → k < n →
        D (cwPos ring seed k) = C (cwPos ring seed k)) := by
  induction steps with
  | zero => omega
  | succ s ih =>
      cases s with
      | zero =>
          let e := seed
          let j := ring.rightNeighbor e
          have hedge := sealRetire_localStep_birth
            ring hn C e hclosed hzero
          have hrun :
              runLocalSchedule ring P_partialSealRetire C
                  (clockwiseEdgeSchedule ring seed 1) =
                localStep ring P_partialSealRetire C e := by
            simp [clockwiseEdgeSchedule, runLocalSchedule, e]
          rw [hrun]
          have hjpos : j = cwPos ring seed 1 := by
            simpa [j, e] using (cwPos_succ ring seed 0).symm
          refine ⟨by simpa [e] using hedge.1, ?_, ?_⟩
          · intro k hk hkle
            have hkone : k = 1 := by omega
            subst k
            rw [← hjpos]
            exact hedge.2.1
          · intro k hk hkn
            have hke : cwPos ring seed k ≠ e := by
              simpa [e] using cwPos_ne_of_ne_below_sealRetire
                ring seed hkn (by omega : 0 < n) (by omega)
            have hkj : cwPos ring seed k ≠ j := by
              rw [hjpos]
              exact cwPos_ne_of_ne_below_sealRetire
                ring seed hkn (by omega) (by omega)
            exact hedge.2.2 (cwPos ring seed k) hke hkj
      | succ s =>
          have hprev := ih (by omega) (by omega)
          let D := runLocalSchedule ring P_partialSealRetire C
            (clockwiseEdgeSchedule ring seed (s + 1))
          change D seed = (setMinimalLockLeader (C seed).1, false) ∧
              (∀ k : Nat, 0 < k → k ≤ s + 1 →
                D (cwPos ring seed k) =
                  ((C (cwPos ring seed k)).1, false)) ∧
              (∀ k : Nat, s + 1 < k → k < n →
                D (cwPos ring seed k) = C (cwPos ring seed k))
              at hprev
          let e := cwPos ring seed (s + 1)
          let j := ring.rightNeighbor e
          have hjpos : j = cwPos ring seed (s + 2) := by
            simpa [j, e, Nat.add_assoc] using
              (cwPos_succ ring seed (s + 1)).symm
          have hDe : D e = ((C e).1, false) := by
            simpa [e] using hprev.2.1 (s + 1) (by omega) (by omega)
          have hDj : D j = C j := by
            rw [hjpos]
            exact hprev.2.2 (s + 2) (by omega) hlt
          have hedge := sealRetire_localStep_advanceFollower
            ring hn D e
              (by rw [hDe]; exact hzero e)
              (by rw [hDe])
              (by rw [hDj]; exact hzero j)
              (by rw [hDj]; exact hclosed j)
          let E := localStep ring P_partialSealRetire D e
          have hrun :
              runLocalSchedule ring P_partialSealRetire C
                  (clockwiseEdgeSchedule ring seed (s + 2)) = E := by
            change runLocalSchedule ring P_partialSealRetire C
                (clockwiseEdgeSchedule ring seed (s + 1) ++ [e]) = _
            rw [PPLLSchedulerBlocks.runLocalSchedule_append]
            rfl
          rw [hrun]
          refine ⟨?_, ?_, ?_⟩
          · have hse : seed ≠ e := by
              have hzero : 0 < n := by omega
              have heoff : s + 1 < n := by omega
              have hne : (0 : Nat) ≠ s + 1 := by omega
              simpa [e] using cwPos_ne_of_ne_below_sealRetire
                ring seed hzero heoff hne
            have hsj : seed ≠ j := by
              have hzero : 0 < n := by omega
              have hne : (0 : Nat) ≠ s + 2 := by omega
              rw [hjpos]
              simpa using cwPos_ne_of_ne_below_sealRetire
                ring seed hzero hlt hne
            exact (hedge.2.2 seed hse hsj).trans hprev.1
          · intro k hk hkle
            by_cases hnew : k = s + 2
            · subst k
              rw [← hjpos]
              have hnewState := hedge.2.1
              change E j = ((D j).1, false) at hnewState
              rw [hDj] at hnewState
              exact hnewState
            · have hkprev : k ≤ s + 1 := by omega
              by_cases hcurrent : k = s + 1
              · subst k
                have heq := hedge.1
                change E e = D e at heq
                exact heq.trans
                  (by simpa [e] using
                    hprev.2.1 (s + 1) (by omega) (by omega))
              · have hke : cwPos ring seed k ≠ e := by
                  have hkbound : k < n := by omega
                  have hebound : s + 1 < n := by omega
                  simpa [e] using cwPos_ne_of_ne_below_sealRetire
                    ring seed hkbound hebound hcurrent
                have hkj : cwPos ring seed k ≠ j := by
                  have hkbound : k < n := by omega
                  rw [hjpos]
                  exact cwPos_ne_of_ne_below_sealRetire
                    ring seed hkbound hlt hnew
                exact (hedge.2.2 (cwPos ring seed k) hke hkj).trans
                  (hprev.2.1 k hk hkprev)
          · intro k hk hkn
            have hke : cwPos ring seed k ≠ e := by
              have hebound : s + 1 < n := by omega
              have hne : k ≠ s + 1 := by omega
              simpa [e] using cwPos_ne_of_ne_below_sealRetire
                ring seed hkn hebound hne
            have hkj : cwPos ring seed k ≠ j := by
              have hne : k ≠ s + 2 := by omega
              rw [hjpos]
              exact cwPos_ne_of_ne_below_sealRetire
                ring seed hkn hlt hne
            exact (hedge.2.2 (cwPos ring seed k) hke hkj).trans
              (hprev.2.2 k (by omega) hkn)

/-- Proper-prefix invariant for a sweep launched by an existing source
leader.  Every positive visited offset is retired and outputs follower; later
offsets retain their arbitrary original leader bits until the frontier visits
them. -/
theorem sealRetire_source_clockwise_prefix
    (ring : DirectedRing n) (hn : 1 < n)
    (C : SealSweepConfig n psi kappa tau) (seed : Fin n)
    (hclosed : SealSweepAllClosed C)
    (hseed : sweepLockLeader (C seed) = true)
    (hsucc : sweepLockLeader (C (ring.rightNeighbor seed)) = false)
    (steps : Nat) (hpos : 0 < steps) (hlt : steps < n) :
    let D := runLocalSchedule ring P_partialSealRetire C
      (clockwiseEdgeSchedule ring seed steps)
    D seed = ((C seed).1, false) ∧
      (∀ k : Nat, 0 < k → k ≤ steps →
        (D (cwPos ring seed k)).2 = false ∧
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
          have hedge := sealRetire_localStep_launch
            ring hn C e hseed (hclosed e)
              (by simpa [e, j] using hsucc) (hclosed j)
          have hrun :
              runLocalSchedule ring P_partialSealRetire C
                  (clockwiseEdgeSchedule ring seed 1) =
                localStep ring P_partialSealRetire C e := by
            simp [clockwiseEdgeSchedule, runLocalSchedule, e]
          rw [hrun]
          have hjpos : j = cwPos ring seed 1 := by
            simpa [j, e] using (cwPos_succ ring seed 0).symm
          refine ⟨by simpa [e] using hedge.1, ?_, ?_⟩
          · intro k hk hkle
            have hkone : k = 1 := by omega
            subst k
            rw [← hjpos, hedge.2.1]
            exact ⟨rfl, hsucc⟩
          · intro k hk hkn
            have hke : cwPos ring seed k ≠ e := by
              simpa [e] using cwPos_ne_of_ne_below_sealRetire
                ring seed hkn (by omega : 0 < n) (by omega)
            have hkj : cwPos ring seed k ≠ j := by
              rw [hjpos]
              exact cwPos_ne_of_ne_below_sealRetire
                ring seed hkn (by omega) (by omega)
            exact hedge.2.2 (cwPos ring seed k) hke hkj
      | succ s =>
          have hprev := ih (by omega) (by omega)
          let D := runLocalSchedule ring P_partialSealRetire C
            (clockwiseEdgeSchedule ring seed (s + 1))
          change D seed = ((C seed).1, false) ∧
              (∀ k : Nat, 0 < k → k ≤ s + 1 →
                (D (cwPos ring seed k)).2 = false ∧
                  sweepLockLeader (D (cwPos ring seed k)) = false) ∧
              (∀ k : Nat, s + 1 < k → k < n →
                D (cwPos ring seed k) = C (cwPos ring seed k))
              at hprev
          let e := cwPos ring seed (s + 1)
          let j := ring.rightNeighbor e
          have hjpos : j = cwPos ring seed (s + 2) := by
            simpa [j, e, Nat.add_assoc] using
              (cwPos_succ ring seed (s + 1)).symm
          have hDj : D j = C j := by
            rw [hjpos]
            exact hprev.2.2 (s + 2) (by omega) hlt
          have heCurrent := hprev.2.1 (s + 1) (by omega) (by omega)
          have hedge := sealRetire_localStep_advance
            ring hn D e
              (by simpa [e] using heCurrent.2)
              (by simpa [e] using heCurrent.1)
              (by rw [hDj]; exact hclosed j)
          let E := localStep ring P_partialSealRetire D e
          have hrun :
              runLocalSchedule ring P_partialSealRetire C
                  (clockwiseEdgeSchedule ring seed (s + 2)) = E := by
            change runLocalSchedule ring P_partialSealRetire C
                (clockwiseEdgeSchedule ring seed (s + 1) ++ [e]) = _
            rw [PPLLSchedulerBlocks.runLocalSchedule_append]
            rfl
          rw [hrun]
          refine ⟨?_, ?_, ?_⟩
          · have hse : seed ≠ e := by
              have hzero : 0 < n := by omega
              have heoff : s + 1 < n := by omega
              have hne : (0 : Nat) ≠ s + 1 := by omega
              simpa [e] using cwPos_ne_of_ne_below_sealRetire
                ring seed hzero heoff hne
            have hsj : seed ≠ j := by
              have hzero : 0 < n := by omega
              have hne : (0 : Nat) ≠ s + 2 := by omega
              rw [hjpos]
              simpa using cwPos_ne_of_ne_below_sealRetire
                ring seed hzero hlt hne
            exact (hedge.2.2.2 seed hse hsj).trans hprev.1
          · intro k hk hkle
            by_cases hnew : k = s + 2
            · subst k
              rw [← hjpos]
              exact ⟨hedge.2.1, hedge.2.2.1⟩
            · have hkprev : k ≤ s + 1 := by omega
              by_cases hcurrent : k = s + 1
              · subst k
                have heq := hedge.1
                change E e = D e at heq
                exact ⟨(congrArg (fun u => u.2) heq).trans heCurrent.1,
                  (congrArg sweepLockLeader heq).trans heCurrent.2⟩
              · have hke : cwPos ring seed k ≠ e := by
                  have hkbound : k < n := by omega
                  have hebound : s + 1 < n := by omega
                  simpa [e] using cwPos_ne_of_ne_below_sealRetire
                    ring seed hkbound hebound hcurrent
                have hkj : cwPos ring seed k ≠ j := by
                  have hkbound : k < n := by omega
                  rw [hjpos]
                  exact cwPos_ne_of_ne_below_sealRetire
                    ring seed hkbound hlt hnew
                have hframe := hedge.2.2.2
                  (cwPos ring seed k) hke hkj
                have hold := hprev.2.1 k hk hkprev
                exact ⟨(congrArg (fun u => u.2) hframe).trans hold.1,
                  (congrArg sweepLockLeader hframe).trans hold.2⟩
          · intro k hk hkn
            have hke : cwPos ring seed k ≠ e := by
              have hebound : s + 1 < n := by omega
              have hne : k ≠ s + 1 := by omega
              simpa [e] using cwPos_ne_of_ne_below_sealRetire
                ring seed hkn hebound hne
            have hkj : cwPos ring seed k ≠ j := by
              have hne : k ≠ s + 2 := by omega
              rw [hjpos]
              exact cwPos_ne_of_ne_below_sealRetire
                ring seed hkn hlt hne
            exact (hedge.2.2.2 (cwPos ring seed k) hke hkj).trans
              (hprev.2.2 k (by omega) hkn)

/-- A chosen closed leader with a follower successor reaches the common
all-retired safety kernel in exactly `n-1` serialized interactions.  Every
other original leader is cleared when the frontier visits it. -/
theorem sealRetire_source_reaches_isSafe
    (ring : DirectedRing n) (hn : 1 < n)
    (C : SealSweepConfig n psi kappa tau)
    (hclosed : SealSweepAllClosed C)
    (seed : Fin n)
    (hseed : sweepLockLeader (C seed) = true)
    (hsucc : sweepLockLeader (C (ring.rightNeighbor seed)) = false) :
    let word := clockwiseEdgeSchedule ring seed (n - 1)
    let D := runLocalSchedule ring P_partialSealRetire C word
    word.length = n - 1 ∧
      PopulationProtocol.Reachable
        (P_partialSealRetireProtocol psi kappa tau) ring C D ∧
      SealRetireAllOpen D ∧
      PopulationProtocol.IsSafe
        (P_partialSealRetireProtocol psi kappa tau) ring D
        isLeaderOutput := by
  let steps := n - 1
  let word := clockwiseEdgeSchedule ring seed steps
  let D := runLocalSchedule ring P_partialSealRetire C word
  have hprefix := sealRetire_source_clockwise_prefix
    ring hn C seed hclosed hseed hsucc steps (by omega) (by omega)
  change D seed = ((C seed).1, false) ∧
      (∀ k : Nat, 0 < k → k ≤ steps →
        (D (cwPos ring seed k)).2 = false ∧
          sweepLockLeader (D (cwPos ring seed k)) = false) ∧
      (∀ k : Nat, steps < k → k < n →
        D (cwPos ring seed k) = C (cwPos ring seed k)) at hprefix
  have hopen : SealRetireAllOpen D := by
    intro i
    let k := cwDist ring seed i
    have hklt : k < n := cwDist_lt ring seed i
    have hkpos : cwPos ring seed k = i := cwPos_cwDist ring seed i
    by_cases hkzero : k = 0
    · have hiseed : i = seed := by
        rw [hkzero, cwPos_zero] at hkpos
        exact hkpos.symm
      rw [hiseed, hprefix.1]
    · have hkpositive : 0 < k := by omega
      have hkle : k ≤ steps := by omega
      have hv := hprefix.2.1 k hkpositive hkle
      rw [hkpos] at hv
      exact hv.1
  have hunique : UniqueLeaderOutput
      (P_partialSealRetireProtocol psi kappa tau) n D
      isLeaderOutput := by
    refine ⟨seed, ?_, ?_⟩
    · rw [hprefix.1]
      change isLeaderOutput
        (if sweepLockLeader ((C seed).1, false)
          then LeaderOutput.leader else LeaderOutput.follower) = true
      rw [show sweepLockLeader ((C seed).1, false) = true by
        exact hseed]
      rfl
    · intro i hi
      let k := cwDist ring seed i
      have hklt : k < n := cwDist_lt ring seed i
      have hkpos : cwPos ring seed k = i := cwPos_cwDist ring seed i
      by_cases hkzero : k = 0
      · rw [hkzero, cwPos_zero] at hkpos
        exact hkpos.symm
      · have hkpositive : 0 < k := by omega
        have hkle : k ≤ steps := by omega
        have hv := hprefix.2.1 k hkpositive hkle
        rw [hkpos] at hv
        change isLeaderOutput
          (if sweepLockLeader (D i) then LeaderOutput.leader
            else LeaderOutput.follower) = true at hi
        simp [hv.2, isLeaderOutput] at hi
  dsimp only
  refine ⟨clockwiseEdgeSchedule_length ring seed steps,
    P_partialSealRetire_runLocalSchedule_reachable ring C word,
    hopen, allOpenUnique_isSafe ring D hopen hunique⟩

/-! ## Zero-count capstone -/

/-- Count zero is exactly pointwise absence of the output leader bit. -/
theorem sealSweepLeaderCount_eq_zero_iff_allFollower
    (C : SealSweepConfig n psi kappa tau) :
    sealSweepLeaderCount C = 0 ↔
      ∀ i : Fin n, sweepLockLeader (C i) = false := by
  induction n with
  | zero => simp [sealSweepLeaderCount]
  | succ n ih =>
      rw [sealSweepLeaderCount, List.ofFn_succ, List.sum_cons]
      constructor
      · intro hsum
        have hhead : sweepLockLeader (C 0) = false := by
          cases h : sweepLockLeader (C 0) <;> simp_all
        have htailCount :
            sealSweepLeaderCount (fun i : Fin n => C i.succ) = 0 := by
          unfold sealSweepLeaderCount
          simp [hhead] at hsum
          exact hsum
        have htail :=
          (ih (fun i : Fin n => C i.succ)).1 htailCount
        intro i
        cases i using Fin.cases with
        | zero => exact hhead
        | succ i => exact htail i
      · intro hall
        have hhead : sweepLockLeader (C 0) = false := hall 0
        have htail :
            sealSweepLeaderCount (fun i : Fin n => C i.succ) = 0 :=
          (ih (fun i : Fin n => C i.succ)).2 (fun i => hall i.succ)
        unfold sealSweepLeaderCount at htail
        simp [hhead, htail]

/-- On every nontrivial ring, the first `n-1` clockwise edges create one
leader, retire every site, and reach the all-schedules safety kernel. -/
theorem sealRetire_allClosedZero_reaches_isSafe_nontrivial
    (ring : DirectedRing n) (hn : 1 < n)
    (C : SealSweepConfig n psi kappa tau)
    (hclosed : SealSweepAllClosed C)
    (hzeroCount : sealSweepLeaderCount C = 0) :
    let seed : Fin n := ⟨0, by omega⟩
    let word := clockwiseEdgeSchedule ring seed (n - 1)
    let D := runLocalSchedule ring P_partialSealRetire C word
    word.length = n - 1 ∧
      PopulationProtocol.Reachable
        (P_partialSealRetireProtocol psi kappa tau) ring C D ∧
      SealRetireAllOpen D ∧
      PopulationProtocol.IsSafe
        (P_partialSealRetireProtocol psi kappa tau) ring D
        isLeaderOutput := by
  let seed : Fin n := ⟨0, by omega⟩
  let steps := n - 1
  let word := clockwiseEdgeSchedule ring seed steps
  let D := runLocalSchedule ring P_partialSealRetire C word
  have hzero : ∀ i : Fin n, sweepLockLeader (C i) = false :=
    (sealSweepLeaderCount_eq_zero_iff_allFollower C).1 hzeroCount
  have hprefix := sealRetire_zero_clockwise_prefix
    ring hn C seed hclosed hzero steps (by omega) (by omega)
  change D seed = (setMinimalLockLeader (C seed).1, false) ∧
      (∀ k : Nat, 0 < k → k ≤ steps →
        D (cwPos ring seed k) = ((C (cwPos ring seed k)).1, false)) ∧
      (∀ k : Nat, steps < k → k < n →
        D (cwPos ring seed k) = C (cwPos ring seed k)) at hprefix
  have hopen : SealRetireAllOpen D := by
    intro i
    let k := cwDist ring seed i
    have hklt : k < n := cwDist_lt ring seed i
    have hkpos : cwPos ring seed k = i := cwPos_cwDist ring seed i
    by_cases hkzero : k = 0
    · have hiseed : i = seed := by
        rw [hkzero, cwPos_zero] at hkpos
        exact hkpos.symm
      rw [hiseed, hprefix.1]
    · have hkpositive : 0 < k := by omega
      have hkle : k ≤ steps := by omega
      have hv := hprefix.2.1 k hkpositive hkle
      rw [hkpos] at hv
      rw [hv]
  have hunique : UniqueLeaderOutput
      (P_partialSealRetireProtocol psi kappa tau) n D
      isLeaderOutput := by
    refine ⟨seed, ?_, ?_⟩
    · rw [hprefix.1]
      change isLeaderOutput
        (if minimalLockLeader (setMinimalLockLeader (C seed).1)
          then LeaderOutput.leader else LeaderOutput.follower) = true
      rw [setMinimalLockLeader_leader]
      rfl
    · intro i hi
      let k := cwDist ring seed i
      have hklt : k < n := cwDist_lt ring seed i
      have hkpos : cwPos ring seed k = i := cwPos_cwDist ring seed i
      by_cases hkzero : k = 0
      · rw [hkzero, cwPos_zero] at hkpos
        exact hkpos.symm
      · have hkpositive : 0 < k := by omega
        have hkle : k ≤ steps := by omega
        have hv := hprefix.2.1 k hkpositive hkle
        rw [hkpos] at hv
        change isLeaderOutput
          (if sweepLockLeader (D i) then LeaderOutput.leader
            else LeaderOutput.follower) = true at hi
        have hfollower : sweepLockLeader (D i) = false := by
          rw [hv]
          exact hzero i
        simp [hfollower, isLeaderOutput] at hi
  dsimp only
  refine ⟨clockwiseEdgeSchedule_length ring seed steps,
    P_partialSealRetire_runLocalSchedule_reachable ring C word,
    hopen, allOpenUnique_isSafe ring D hopen hunique⟩

/-- The one-agent self-edge is not an exception to the construction.  The
packaged step is left-biased when initiator and responder coincide, so the
leader-producing initiator output is retained. -/
theorem sealRetire_allClosedZero_reaches_isSafe_one
    (ring : DirectedRing 1)
    (C : SealSweepConfig 1 psi kappa tau)
    (hclosed : SealSweepAllClosed C)
    (hzeroCount : sealSweepLeaderCount C = 0) :
    let seed : Fin 1 := 0
    let word : DetSchedule 1 := [seed]
    let D := runLocalSchedule ring P_partialSealRetire C word
    word.length = 1 ∧
      PopulationProtocol.Reachable
        (P_partialSealRetireProtocol psi kappa tau) ring C D ∧
      SealRetireAllOpen D ∧
      PopulationProtocol.IsSafe
        (P_partialSealRetireProtocol psi kappa tau) ring D
        isLeaderOutput := by
  let seed : Fin 1 := 0
  let word : DetSchedule 1 := [seed]
  let D := runLocalSchedule ring P_partialSealRetire C word
  have hzero : ∀ i : Fin 1, sweepLockLeader (C i) = false :=
    (sealSweepLeaderCount_eq_zero_iff_allFollower C).1 hzeroCount
  have hneighbor : ring.rightNeighbor seed = seed := Subsingleton.elim _ _
  have hpair : P_partialSealRetire (C seed)
      (C (ring.rightNeighbor seed)) =
      ((setMinimalLockLeader (C seed).1, false),
        ((C (ring.rightNeighbor seed)).1, false)) := by
    exact P_partialSealRetire_birth
      (C seed) (C (ring.rightNeighbor seed))
      (hclosed seed) (hclosed (ring.rightNeighbor seed))
      (hzero seed) (hzero (ring.rightNeighbor seed))
  have hDseed : D seed =
      (setMinimalLockLeader (C seed).1, false) := by
    simp [D, word, runLocalSchedule, localStep, hpair]
  have hall : ∀ i : Fin 1, i = seed := fun i => Subsingleton.elim _ _
  have hopen : SealRetireAllOpen D := by
    intro i
    rw [hall i, hDseed]
  have hunique : UniqueLeaderOutput
      (P_partialSealRetireProtocol psi kappa tau) 1 D
      isLeaderOutput := by
    refine ⟨seed, ?_, ?_⟩
    · rw [hDseed]
      change isLeaderOutput
        (if minimalLockLeader (setMinimalLockLeader (C seed).1)
          then LeaderOutput.leader else LeaderOutput.follower) = true
      rw [setMinimalLockLeader_leader]
      rfl
    · intro i _
      exact hall i
  dsimp only
  refine ⟨rfl,
    P_partialSealRetire_runLocalSchedule_reachable ring C word,
    hopen, allOpenUnique_isSafe ring D hopen hunique⟩

/-- Uniform zero-count landing on every nonempty directed ring.  The witness
has length at most `n`; nontrivial rings use exactly `n-1`, while the one-site
self-edge uses one interaction. -/
theorem sealRetire_allClosedZero_reaches_isSafe
    (ring : DirectedRing n)
    (C : SealSweepConfig n psi kappa tau)
    (hclosed : SealSweepAllClosed C)
    (hzeroCount : sealSweepLeaderCount C = 0) :
    ∃ word : DetSchedule n,
      word.length ≤ n ∧
      PopulationProtocol.Reachable
        (P_partialSealRetireProtocol psi kappa tau) ring C
        (runLocalSchedule ring P_partialSealRetire C word) ∧
      PopulationProtocol.IsSafe
        (P_partialSealRetireProtocol psi kappa tau) ring
        (runLocalSchedule ring P_partialSealRetire C word)
        isLeaderOutput := by
  by_cases hn : 1 < n
  · let seed : Fin n := ⟨0, by omega⟩
    let word := clockwiseEdgeSchedule ring seed (n - 1)
    obtain ⟨hlength, hreach, _hopen, hsafe⟩ :=
      sealRetire_allClosedZero_reaches_isSafe_nontrivial
        ring hn C hclosed hzeroCount
    refine ⟨word, ?_, hreach, hsafe⟩
    change word.length = n - 1 at hlength
    omega
  · have hnOne : n = 1 := by
      have hpositive := ring.hn
      omega
    subst n
    let seed : Fin 1 := 0
    let word : DetSchedule 1 := [seed]
    obtain ⟨hlength, hreach, _hopen, hsafe⟩ :=
      sealRetire_allClosedZero_reaches_isSafe_one
        ring C hclosed hzeroCount
    exact ⟨word, by simp [word], hreach, hsafe⟩

/-! ## Positive-count integration for the same transition -/

@[simp] theorem sealRetire_isLeaderOutput_iff
    (u : SealSweepState psi kappa tau) :
    isLeaderOutput
          ((P_partialSealRetireProtocol psi kappa tau).output u) = true ↔
      sweepLockLeader u = true := by
  cases h : sweepLockLeader u <;>
    simp [P_partialSealRetireProtocol, h, isLeaderOutput]

/-- Count one is the unique-output predicate for the repaired protocol as
well, since the output map is unchanged. -/
theorem sealRetire_unique_iff_leaderCount_eq_one
    (C : SealSweepConfig n psi kappa tau) :
    UniqueLeaderOutput
        (P_partialSealRetireProtocol psi kappa tau) n C isLeaderOutput ↔
      sealSweepLeaderCount C = 1 := by
  constructor
  · rintro ⟨root, hroot, honly⟩
    apply (sealSweep_unique_iff_leaderCount_eq_one C).1
    refine ⟨root, ?_, ?_⟩
    · rw [← sealRetire_output_eq_sealSweep]
      exact hroot
    · intro i hi
      apply honly i
      rw [sealRetire_output_eq_sealSweep]
      exact hi
  · intro hcount
    obtain ⟨root, hroot, honly⟩ :=
      (sealSweep_unique_iff_leaderCount_eq_one C).2 hcount
    refine ⟨root, ?_, ?_⟩
    · rw [sealRetire_output_eq_sealSweep]
      exact hroot
    · intro i hi
      apply honly i
      rw [← sealRetire_output_eq_sealSweep]
      exact hi

/-- The unchanged output map also transports the two-leader witness. -/
theorem sealRetire_hasTwo_of_two_le_leaderCount
    (C : SealSweepConfig n psi kappa tau)
    (hcount : 2 ≤ sealSweepLeaderCount C) :
    HasTwoLeaderOutputs
      (P_partialSealRetireProtocol psi kappa tau) isLeaderOutput C := by
  obtain ⟨i, j, hij, hi, hj⟩ :=
    sealSweep_hasTwo_of_two_le_leaderCount C hcount
  refine ⟨i, j, hij, ?_, ?_⟩
  · rw [sealRetire_output_eq_sealSweep]
    exact hi
  · rw [sealRetire_output_eq_sealSweep]
    exact hj

/-- On an all-closed adjacent-leader pair, the repaired transition is exactly
the R82/R86 collision transition, so it preserves closedness and removes one
leader. -/
theorem sealRetire_adjacentCollision_step
    (ring : DirectedRing n) (hn : 1 < n)
    (C : SealSweepConfig n psi kappa tau)
    (hclosed : SealSweepAllClosed C)
    (e : Fin n) (hadj : SealSweepAdjacentLeaders ring C e) :
    let D := localStep ring P_partialSealRetire C e
    SealSweepAllClosed D ∧
      sealSweepLeaderCount D + 1 = sealSweepLeaderCount C := by
  let j := ring.rightNeighbor e
  have hnew : P_partialSealRetire (C e) (C j) =
      (((C e).1, true), (clearMinimalLockLeader (C j).1, true)) :=
    P_partialSealRetire_twoClosedLeaders
      (C e) (C j) (hclosed e) (hclosed j)
        hadj.1 (by simpa [j] using hadj.2)
  have hold : P_partialSealSweep (C e) (C j) =
      (((C e).1, true), (clearMinimalLockLeader (C j).1, true)) :=
    P_partialSealSweep_twoClosedLeaders
      (C e) (C j) hadj.1 (hclosed e)
        (by simpa [j] using hadj.2) (hclosed j)
  have hstepEq :
      localStep ring P_partialSealRetire C e =
        localStep ring P_partialSealSweep C e := by
    funext i
    simp only [localStep]
    rw [show P_partialSealRetire (C e) (C (ring.rightNeighbor e)) =
        P_partialSealSweep (C e) (C (ring.rightNeighbor e)) by
      simpa [j] using hnew.trans hold.symm]
  dsimp only
  rw [hstepEq]
  exact sealSweep_adjacentCollision_step ring hn C hclosed e hadj

/-- Collision normalization from R86, replayed using only actual steps of the
repaired transition.  Every prefix interaction removes exactly one leader. -/
theorem sealRetire_collisionNormalization
    (ring : DirectedRing n)
    (C : SealSweepConfig n psi kappa tau)
    (hclosed : SealSweepAllClosed C)
    (hpositive : 0 < sealSweepLeaderCount C) :
    ∃ pre : DetSchedule n,
      let D := runLocalSchedule ring P_partialSealRetire C pre
      SealSweepAllClosed D ∧
        0 < sealSweepLeaderCount D ∧
        sealSweepLeaderCount D + pre.length = sealSweepLeaderCount C ∧
        (UniqueLeaderOutput
            (P_partialSealRetireProtocol psi kappa tau) n D isLeaderOutput ∨
          (2 ≤ sealSweepLeaderCount D ∧
            SweepResetNoAdjacentLeaders ring D)) := by
  classical
  have hnormalize : ∀ k : Nat,
      ∀ X : SealSweepConfig n psi kappa tau,
        sealSweepLeaderCount X = k →
        SealSweepAllClosed X →
        0 < sealSweepLeaderCount X →
        ∃ pre : DetSchedule n,
          let D := runLocalSchedule ring P_partialSealRetire X pre
          SealSweepAllClosed D ∧
            0 < sealSweepLeaderCount D ∧
            sealSweepLeaderCount D + pre.length =
              sealSweepLeaderCount X ∧
            (UniqueLeaderOutput
                (P_partialSealRetireProtocol psi kappa tau)
                n D isLeaderOutput ∨
              (2 ≤ sealSweepLeaderCount D ∧
                SweepResetNoAdjacentLeaders ring D)) := by
    intro k
    induction k using Nat.strongRecOn with
    | ind k ih =>
        intro X hXcount hXclosed hXpositive
        by_cases hunique : UniqueLeaderOutput
            (P_partialSealRetireProtocol psi kappa tau) n X isLeaderOutput
        · refine ⟨[], ?_, ?_, ?_, Or.inl ?_⟩
          · exact hXclosed
          · exact hXpositive
          · simp [runLocalSchedule]
          · exact hunique
        by_cases hnoAdjacent : SweepResetNoAdjacentLeaders ring X
        · have hneOne : sealSweepLeaderCount X ≠ 1 := by
            intro hone
            exact hunique
              ((sealRetire_unique_iff_leaderCount_eq_one X).2 hone)
          have htwo : 2 ≤ sealSweepLeaderCount X := by omega
          refine ⟨[], ?_, ?_, ?_, Or.inr ⟨htwo, ?_⟩⟩
          · exact hXclosed
          · exact hXpositive
          · simp [runLocalSchedule]
          · exact hnoAdjacent
        · have hadjExists : ∃ e : Fin n,
              SealSweepAdjacentLeaders ring X e := by
            apply Classical.byContradiction
            intro hnone
            apply hnoAdjacent
            intro e he
            apply hnone
            exact ⟨e, he⟩
          obtain ⟨e, hadj⟩ := hadjExists
          have hneOne : sealSweepLeaderCount X ≠ 1 := by
            intro hone
            exact hunique
              ((sealRetire_unique_iff_leaderCount_eq_one X).2 hone)
          have htwo : 2 ≤ sealSweepLeaderCount X := by omega
          have hn : 1 < n := by
            have hle := sealSweepLeaderCount_le X
            omega
          let Y := localStep ring P_partialSealRetire X e
          have hstep := sealRetire_adjacentCollision_step
            ring hn X hXclosed e hadj
          change SealSweepAllClosed Y ∧
            sealSweepLeaderCount Y + 1 = sealSweepLeaderCount X at hstep
          have hYpositive : 0 < sealSweepLeaderCount Y := by omega
          have hYlt : sealSweepLeaderCount Y < k := by omega
          obtain ⟨tail, htailClosed, htailPositive,
              htailCount, htailTerminal⟩ :=
            ih (sealSweepLeaderCount Y) hYlt Y rfl hstep.1 hYpositive
          refine ⟨e :: tail, ?_, ?_, ?_, ?_⟩
          · exact htailClosed
          · exact htailPositive
          · change
              sealSweepLeaderCount
                  (runLocalSchedule ring P_partialSealRetire Y tail) +
                  (tail.length + 1) =
                sealSweepLeaderCount X
            omega
          · exact htailTerminal
  exact hnormalize (sealSweepLeaderCount C) C rfl hclosed hpositive

/-! ### The one-site positive kernel -/

private theorem sealRetire_allClosedLeader_step_eq_one
    (ring : DirectedRing 1)
    (C : SealSweepConfig 1 psi kappa tau)
    (hclosed : SealSweepAllClosed C)
    (hleader : ∀ i : Fin 1, sweepLockLeader (C i) = true)
    (e : Fin 1) :
    localStep ring P_partialSealRetire C e = C := by
  have hneighbor : ring.rightNeighbor e = e := Subsingleton.elim _ _
  have hpair : P_partialSealRetire (C e) (C e) =
      (((C e).1, true),
        (clearMinimalLockLeader (C e).1, true)) :=
    P_partialSealRetire_twoClosedLeaders
      (C e) (C e) (hclosed e) (hclosed e)
        (hleader e) (hleader e)
  have hfirst : (P_partialSealRetire (C e) (C e)).1 = C e := by
    rw [hpair]
    exact Prod.ext rfl (hclosed e).symm
  funext i
  have hie : i = e := Subsingleton.elim _ _
  subst i
  simp [localStep, hneighbor, hfirst]

private theorem sealRetire_allClosedLeader_reachable_eq_one
    (ring : DirectedRing 1)
    (C D : SealSweepConfig 1 psi kappa tau)
    (hclosed : SealSweepAllClosed C)
    (hleader : ∀ i : Fin 1, sweepLockLeader (C i) = true)
    (hreach : PopulationProtocol.Reachable
      (P_partialSealRetireProtocol psi kappa tau) ring C D) :
    D = C := by
  have hsingleton :
      PopulationProtocol.ClosedPred
        (P_partialSealRetireProtocol psi kappa tau) ring
        (fun X => X = C) := by
    intro X hX Y hstep
    subst X
    obtain ⟨e, rfl⟩ := hstep
    change localStep ring P_partialSealRetire C e = C
    exact sealRetire_allClosedLeader_step_eq_one
      ring C hclosed hleader e
  exact hsingleton.reachable rfl hreach

private theorem sealRetire_allClosedUnique_isSafe_one
    (ring : DirectedRing 1)
    (C : SealSweepConfig 1 psi kappa tau)
    (hclosed : SealSweepAllClosed C)
    (hunique : UniqueLeaderOutput
      (P_partialSealRetireProtocol psi kappa tau) 1 C
      isLeaderOutput) :
    PopulationProtocol.IsSafe
      (P_partialSealRetireProtocol psi kappa tau) ring C
      isLeaderOutput := by
  have hleader : ∀ i : Fin 1, sweepLockLeader (C i) = true := by
    obtain ⟨root, hroot, _⟩ := hunique
    intro i
    have hi : i = root := Subsingleton.elim _ _
    subst i
    exact (sealRetire_isLeaderOutput_iff (C root)).1 hroot
  refine ⟨hunique, ?_⟩
  intro D hreach i
  rw [sealRetire_allClosedLeader_reachable_eq_one
    ring C D hclosed hleader hreach]

/-! ### Positive landing and the unified all-closed repair -/

/-- State-dependent positive landing for the repaired transition.  Unlike the
R86 proof, even a unique all-closed state runs the retirement sweep, because
remote closed follower/follower pairs are birth-enabled until the common
all-retired kernel is reached. -/
theorem sealRetire_allClosedPositive_reaches_isSafe_stateBound
    (ring : DirectedRing n)
    (C : SealSweepConfig n psi kappa tau)
    (hclosed : SealSweepAllClosed C)
    (hpositive : 0 < sealSweepLeaderCount C) :
    ∃ word : DetSchedule n,
      word.length ≤ n + sealSweepLeaderCount C - 2 ∧
      PopulationProtocol.Reachable
        (P_partialSealRetireProtocol psi kappa tau) ring C
        (runLocalSchedule ring P_partialSealRetire C word) ∧
      PopulationProtocol.IsSafe
        (P_partialSealRetireProtocol psi kappa tau) ring
        (runLocalSchedule ring P_partialSealRetire C word)
        isLeaderOutput := by
  by_cases hn : 1 < n
  · obtain ⟨pre, hDclosed, hDpositive, hcount, hterminal⟩ :=
      sealRetire_collisionNormalization ring C hclosed hpositive
    let D := runLocalSchedule ring P_partialSealRetire C pre
    change SealSweepAllClosed D at hDclosed
    change 0 < sealSweepLeaderCount D at hDpositive
    change sealSweepLeaderCount D + pre.length =
      sealSweepLeaderCount C at hcount
    change UniqueLeaderOutput
        (P_partialSealRetireProtocol psi kappa tau) n D isLeaderOutput ∨
      (2 ≤ sealSweepLeaderCount D ∧
        SweepResetNoAdjacentLeaders ring D) at hterminal
    have hseedExists : ∃ seed : Fin n,
        sweepLockLeader (D seed) = true ∧
          sweepLockLeader (D (ring.rightNeighbor seed)) = false := by
      rcases hterminal with hDunique | ⟨hDtwo, hDnoAdjacent⟩
      · obtain ⟨seed, hseedOutput, honly⟩ := hDunique
        have hseed : sweepLockLeader (D seed) = true :=
          (sealRetire_isLeaderOutput_iff (D seed)).1 hseedOutput
        refine ⟨seed, hseed, ?_⟩
        cases hsucc : sweepLockLeader (D (ring.rightNeighbor seed)) with
        | false => rfl
        | true =>
            have heq := honly (ring.rightNeighbor seed)
              ((sealRetire_isLeaderOutput_iff
                (D (ring.rightNeighbor seed))).2 hsucc)
            exact False.elim
              ((rightNeighbor_ne_self_of_one_lt ring hn seed) heq)
      · obtain ⟨seed, other, _hne,
            hseedOutput, _hotherOutput⟩ :=
          sealRetire_hasTwo_of_two_le_leaderCount D hDtwo
        have hseed : sweepLockLeader (D seed) = true :=
          (sealRetire_isLeaderOutput_iff (D seed)).1 hseedOutput
        refine ⟨seed, hseed, ?_⟩
        cases hsucc : sweepLockLeader (D (ring.rightNeighbor seed)) with
        | false => rfl
        | true =>
            exact False.elim
              (hDnoAdjacent seed ⟨hseed, hsucc⟩)
    obtain ⟨seed, hseed, hsucc⟩ := hseedExists
    let tail := clockwiseEdgeSchedule ring seed (n - 1)
    obtain ⟨htailLength, htailReach, _hopen, hEsafe⟩ :=
      sealRetire_source_reaches_isSafe
        ring hn D hDclosed seed hseed hsucc
    refine ⟨pre ++ tail, ?_,
      P_partialSealRetire_runLocalSchedule_reachable
        ring C (pre ++ tail), ?_⟩
    · simp only [List.length_append]
      change tail.length = n - 1 at htailLength
      omega
    · have hrun :
          runLocalSchedule ring P_partialSealRetire C (pre ++ tail) =
            runLocalSchedule ring P_partialSealRetire D tail := by
          rw [PPLLSchedulerBlocks.runLocalSchedule_append]
      have hsafeEq := congrArg
        (fun X : SealSweepConfig n psi kappa tau =>
          PopulationProtocol.IsSafe
            (P_partialSealRetireProtocol psi kappa tau) ring X
            isLeaderOutput)
        hrun
      exact Eq.mpr hsafeEq hEsafe
  · have hnOne : n = 1 := by
      have hnonempty := ring.hn
      omega
    subst n
    have hcountOne : sealSweepLeaderCount C = 1 := by
      have hle := sealSweepLeaderCount_le C
      omega
    have hunique : UniqueLeaderOutput
        (P_partialSealRetireProtocol psi kappa tau) 1 C
        isLeaderOutput :=
      (sealRetire_unique_iff_leaderCount_eq_one C).2 hcountOne
    refine ⟨[], ?_, ?_, ?_⟩
    · simp [runLocalSchedule]
    · simpa [runLocalSchedule] using
        (PopulationProtocol.Reachable.refl
          (P := P_partialSealRetireProtocol psi kappa tau)
          (ring := ring) C)
    · simpa [runLocalSchedule] using
        sealRetire_allClosedUnique_isSafe_one ring C hclosed hunique

/-- Uniform positive bound, retaining R86's factor `2*n-2`. -/
theorem sealRetire_allClosedPositive_reaches_isSafe_two_mul_sub_two
    (ring : DirectedRing n)
    (C : SealSweepConfig n psi kappa tau)
    (hclosed : SealSweepAllClosed C)
    (hpositive : 0 < sealSweepLeaderCount C) :
    ∃ word : DetSchedule n,
      word.length ≤ 2 * n - 2 ∧
      PopulationProtocol.Reachable
        (P_partialSealRetireProtocol psi kappa tau) ring C
        (runLocalSchedule ring P_partialSealRetire C word) ∧
      PopulationProtocol.IsSafe
        (P_partialSealRetireProtocol psi kappa tau) ring
        (runLocalSchedule ring P_partialSealRetire C word)
        isLeaderOutput := by
  obtain ⟨word, hlength, hreach, hsafe⟩ :=
    sealRetire_allClosedPositive_reaches_isSafe_stateBound
      ring C hclosed hpositive
  refine ⟨word, ?_, hreach, hsafe⟩
  have hle := sealSweepLeaderCount_le C
  omega

/-- On every nontrivial ring, the single repaired transition lands from every
all-closed configuration, including leader count zero, within `2*n-2` actual
interactions. -/
theorem sealRetire_allClosed_reaches_isSafe_nontrivial
    (ring : DirectedRing n) (hn : 1 < n)
    (C : SealSweepConfig n psi kappa tau)
    (hclosed : SealSweepAllClosed C) :
    ∃ word : DetSchedule n,
      word.length ≤ 2 * n - 2 ∧
      PopulationProtocol.Reachable
        (P_partialSealRetireProtocol psi kappa tau) ring C
        (runLocalSchedule ring P_partialSealRetire C word) ∧
      PopulationProtocol.IsSafe
        (P_partialSealRetireProtocol psi kappa tau) ring
        (runLocalSchedule ring P_partialSealRetire C word)
        isLeaderOutput := by
  by_cases hzero : sealSweepLeaderCount C = 0
  · let seed : Fin n := ⟨0, by omega⟩
    let word := clockwiseEdgeSchedule ring seed (n - 1)
    obtain ⟨hlength, hreach, _hopen, hsafe⟩ :=
      sealRetire_allClosedZero_reaches_isSafe_nontrivial
        ring hn C hclosed hzero
    refine ⟨word, ?_, hreach, hsafe⟩
    change word.length = n - 1 at hlength
    omega
  · have hpositive : 0 < sealSweepLeaderCount C := by omega
    exact sealRetire_allClosedPositive_reaches_isSafe_two_mul_sub_two
      ring C hclosed hpositive

/-! ## Exact boundary outside the all-closed initialization domain -/

/-- In the terminal all-retired region, semantic safety is equivalent to
already having a unique output. -/
theorem sealRetire_allOpen_isSafe_iff_unique
    (ring : DirectedRing n)
    (C : SealSweepConfig n psi kappa tau)
    (hopen : SealRetireAllOpen C) :
    PopulationProtocol.IsSafe
        (P_partialSealRetireProtocol psi kappa tau) ring C
        isLeaderOutput ↔
      UniqueLeaderOutput
        (P_partialSealRetireProtocol psi kappa tau) n C
        isLeaderOutput := by
  constructor
  · exact fun hsafe => hsafe.1
  · exact allOpenUnique_isSafe ring C hopen

/-- Any all-retired invalid-output state is a fixed bad trap: every reachable
configuration equals it, hence no schedule can repair it.  This is the exact
machine-checked limitation on arbitrary mixed initialization bits. -/
theorem sealRetire_allOpen_no_reachable_isSafe_of_not_unique
    (ring : DirectedRing n)
    (C D : SealSweepConfig n psi kappa tau)
    (hopen : SealRetireAllOpen C)
    (hnotUnique : ¬ UniqueLeaderOutput
      (P_partialSealRetireProtocol psi kappa tau) n C
      isLeaderOutput)
    (hreach : PopulationProtocol.Reachable
      (P_partialSealRetireProtocol psi kappa tau) ring C D) :
    ¬ PopulationProtocol.IsSafe
      (P_partialSealRetireProtocol psi kappa tau) ring D
      isLeaderOutput := by
  have hDC : D = C := sealRetireAllOpen_reachable_eq
    ring C D hopen hreach
  subst D
  intro hsafe
  exact hnotUnique hsafe.1

end PPartialSealSweepZeroLeaderRepairSol
end PPLLCompleteMultiLeaderCleanup
