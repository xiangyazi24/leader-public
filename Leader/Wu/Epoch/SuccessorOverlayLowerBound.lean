import Leader.Wu.Epoch.VoterDefinitionOneLower
import Leader.Wu.Epoch.FilterPolynomialUpper

/-!
# State lower bound for successor-certified epoch overlays

This module isolates the state-complexity price paid by the epoch certificate.
The scope is explicit: a terminal configuration carries a certificate in
`Fin k`, every clockwise edge applies one fixed deterministic successor to the
certificate, and the leader output at that terminal configuration factors
through the certificate.  The underlying population protocol and all other
local state are arbitrary.

On a directed ring, equality of two certificates propagates clockwise.  Moving
one of the equal positions to the unique Definition-1 leader therefore moves
the other to a leader as well.  Uniqueness and injectivity of ring rotation
force the two positions to coincide.  Thus the terminal certificate map is
injective and `n <= k`.

The scheduler theorem is stronger than an asymptotic obstruction: when
`k < n`, the exact number of length-`t` schedules reaching such a certified
Definition-1 state at any prefix is zero, for every initial configuration and
every horizon.  Consequently no polynomial iid bound with a nontrivial failure
budget exists in this class.  This is not a lower bound for protocols whose
safe outputs do not factor through a deterministic successor certificate.
-/

namespace PPLLEpochSuccessorOverlayLowerBound

open PPLLResearchFormulation PPLLProtectedEpochProtocol
  PPLLProtectedEpochSweep PPLLDerivedEpochRepair PPLLDerivedEpochSweep
  PPLLEpochVoterReduction PPLLEpochVoterPolynomialUpper
  PPLLEpochVoterDefinitionOneLower PPLLEpochVoterTwoDomain

/-! ## The scoped terminal class -/

/-- A successor-certified Definition-1 terminal configuration.

The first field is the anonymous local successor constraint.  The second says
that, at this terminal configuration, the leader predicate factors through the
`k`-color certificate.  The third is Wu's full Definition-1 safety predicate,
including preservation under every reachable execution. -/
def SuccessorCertificateSafe (P : PopulationProtocol)
    (ring : DirectedRing n) (isLeader : P.Y → Bool)
    (certificate : P.Q → Fin k) (advance : Fin k → Fin k)
    (certificateLeader : Fin k → Bool)
    (C : P.Configuration n) : Prop :=
  (∀ i, certificate (C (ring.rightNeighbor i)) =
      advance (certificate (C i))) ∧
  (∀ i, isLeader (P.output (C i)) =
      certificateLeader (certificate (C i))) ∧
  PopulationProtocol.IsSafe P ring C isLeader

/-- Protocol-class hypothesis saying that every Definition-1 safe state is
certified by the same successor overlay.  This lets the lower bound target the
repository's standard finite-horizon stabilization definition directly. -/
def DefinitionOneSafeStatesUseSuccessorCertificate
    (P : PopulationProtocol) (ring : DirectedRing n)
    (isLeader : P.Y → Bool) (certificate : P.Q → Fin k)
    (advance : Fin k → Fin k) (certificateLeader : Fin k → Bool) : Prop :=
  ∀ C : P.Configuration n,
    PopulationProtocol.IsSafe P ring C isLeader →
      (∀ i, certificate (C (ring.rightNeighbor i)) =
        advance (certificate (C i))) ∧
      (∀ i, isLeader (P.output (C i)) =
        certificateLeader (certificate (C i)))

/-! ## Clockwise propagation -/

/-- Position reached after `t` clockwise edges.  This local definition keeps
the state lower bound independent of the unrelated physical-geometry repair
modules. -/
def ringShift (ring : DirectedRing n) (i : Fin n) (t : Nat) : Fin n :=
  ⟨(i.val + t) % n, Nat.mod_lt _ ring.hn⟩

@[simp] theorem ringShift_zero (ring : DirectedRing n) (i : Fin n) :
    ringShift ring i 0 = i := by
  apply Fin.ext
  simp [ringShift, Nat.mod_eq_of_lt i.isLt]

@[simp] theorem ringShift_succ (ring : DirectedRing n) (i : Fin n) (t : Nat) :
    ringShift ring i (t + 1) = ring.rightNeighbor (ringShift ring i t) := by
  apply Fin.ext
  unfold ringShift DirectedRing.rightNeighbor
  dsimp only
  rw [mod_succ_eq]
  congr 1

/-- The canonical clockwise displacement from `i` reaches `j`. -/
theorem ringShift_distance (ring : DirectedRing n) (i j : Fin n) :
    ringShift ring i ((j.val + n - i.val) % n) = j := by
  apply Fin.ext
  unfold ringShift
  dsimp only
  rw [Nat.add_mod_mod]
  have hsum : i.val + (j.val + n - i.val) = j.val + n := by omega
  rw [hsum]
  simp [Nat.mod_eq_of_lt j.isLt]

private theorem rightNeighbor_injective (ring : DirectedRing n) :
    Function.Injective ring.rightNeighbor := by
  intro i j hij
  have h := congrArg ring.leftNeighbor hij
  simpa only [leftNeighbor_rightNeighbor] using h

/-- Clockwise displacement by any fixed distance is a permutation of the
physical positions. -/
theorem ringShift_injective (ring : DirectedRing n) (t : Nat) :
    Function.Injective (fun i ↦ ringShift ring i t) := by
  induction t with
  | zero =>
      intro i j hij
      simpa only [ringShift_zero] using hij
  | succ t ih =>
      intro i j hij
      apply ih
      apply rightNeighbor_injective ring
      simpa only [ringShift_succ] using hij

/-- Equal certificates remain equal after the same number of clockwise steps.
Only determinism of the common successor map is used. -/
theorem certificate_eq_propagates
    (ring : DirectedRing n) (certificate : Fin n → Fin k)
    (advance : Fin k → Fin k)
    (hsuccessor : ∀ i, certificate (ring.rightNeighbor i) =
      advance (certificate i))
    {i j : Fin n} (hij : certificate i = certificate j) (t : Nat) :
    certificate (ringShift ring i t) = certificate (ringShift ring j t) := by
  induction t with
  | zero => simpa only [ringShift_zero] using hij
  | succ t ih =>
      calc
        certificate (ringShift ring i (t + 1)) =
            advance (certificate (ringShift ring i t)) := by
              rw [ringShift_succ]
              exact hsuccessor _
        _ = advance (certificate (ringShift ring j t)) := congrArg advance ih
        _ = certificate (ringShift ring j (t + 1)) := by
              rw [ringShift_succ]
              exact (hsuccessor _).symm

/-- A deterministic successor certificate with a unique certificate-controlled
leader cannot repeat a color around the ring. -/
theorem certificate_injective_of_successor_unique
    (ring : DirectedRing n) (certificate : Fin n → Fin k)
    (advance : Fin k → Fin k) (certificateLeader : Fin k → Bool)
    (hsuccessor : ∀ i, certificate (ring.rightNeighbor i) =
      advance (certificate i))
    (hunique : ∃ leaderPos : Fin n,
      certificateLeader (certificate leaderPos) = true ∧
      ∀ j : Fin n, certificateLeader (certificate j) = true →
        j = leaderPos) :
    Function.Injective certificate := by
  obtain ⟨leaderPos, hleader, honly⟩ := hunique
  intro i j hij
  let t := (leaderPos.val + n - i.val) % n
  have hit : ringShift ring i t = leaderPos := ringShift_distance ring i leaderPos
  have hprop : certificate (ringShift ring i t) =
      certificate (ringShift ring j t) :=
    certificate_eq_propagates ring certificate advance hsuccessor hij t
  have hjLeader :
      certificateLeader (certificate (ringShift ring j t)) = true := by
    rw [← hprop, hit]
    exact hleader
  have hjHit : ringShift ring j t = leaderPos := honly _ hjLeader
  apply ringShift_injective ring t
  exact hit.trans hjHit.symm

/-! ## Finite-cardinality consequence -/

private theorem nodup_ofFn_of_injective {q : Nat} {alpha : Type}
    (f : Fin q → alpha) (hf : Function.Injective f) :
    (List.ofFn f).Nodup := by
  induction q with
  | zero => simp
  | succ q ih =>
      rw [List.ofFn_succ, List.nodup_cons]
      constructor
      · intro hmem
        rw [List.mem_ofFn] at hmem
        obtain ⟨i, hi⟩ := hmem
        have h := hf hi
        cases h
      · apply ih
        intro i j hij
        exact Fin.succ_inj.mp (hf hij)

/-- An injection from `Fin n` to `Fin k` gives the explicit arithmetic bound
`n <= k`, without a `Fintype` or external cardinality premise. -/
theorem fin_le_of_injective (f : Fin n → Fin k)
    (hf : Function.Injective f) : n ≤ k := by
  have hnodup : (List.ofFn f).Nodup := nodup_ofFn_of_injective f hf
  have hsubset : List.ofFn f ⊆ List.ofFn (fun i : Fin k ↦ i) := by
    intro color hcolor
    exact List.mem_ofFn.mpr ⟨color, rfl⟩
  have hle := hnodup.length_le_of_subset hsubset
  simpa using hle

/-- Main state lower bound.  Any Definition-1 safe successor-certified
terminal configuration on `n` agents needs at least `n` certificate colors. -/
theorem successorCertificate_color_lower_bound
    (P : PopulationProtocol) (ring : DirectedRing n)
    (isLeader : P.Y → Bool) (certificate : P.Q → Fin k)
    (advance : Fin k → Fin k) (certificateLeader : Fin k → Bool)
    (C : P.Configuration n)
    (hterminal : SuccessorCertificateSafe P ring isLeader certificate
      advance certificateLeader C) :
    n ≤ k := by
  obtain ⟨hsuccessor, houtput, hsafe⟩ := hterminal
  obtain ⟨leaderPos, hleader, honly⟩ := hsafe.1
  have hunique : ∃ leaderPos : Fin n,
      certificateLeader (certificate (C leaderPos)) = true ∧
      ∀ j : Fin n,
        certificateLeader (certificate (C j)) = true → j = leaderPos := by
    refine ⟨leaderPos, ?_, ?_⟩
    · rw [← houtput leaderPos]
      exact hleader
    · intro j hj
      apply honly j
      rw [houtput j]
      exact hj
  exact fin_le_of_injective (fun i ↦ certificate (C i))
    (certificate_injective_of_successor_unique ring
      (fun i ↦ certificate (C i)) advance certificateLeader
      hsuccessor hunique)

/-- With fewer than `n` colors, no configuration in the scoped terminal class
exists, independently of the transition function or reachability history. -/
theorem no_successorCertificateSafe_of_fewer_colors
    (P : PopulationProtocol) (ring : DirectedRing n)
    (isLeader : P.Y → Bool) (certificate : P.Q → Fin k)
    (advance : Fin k → Fin k) (certificateLeader : Fin k → Bool)
    (hcolors : k < n) (C : P.Configuration n) :
    ¬ SuccessorCertificateSafe P ring isLeader certificate
      advance certificateLeader C := by
  intro hterminal
  exact Nat.not_le_of_lt hcolors
    (successorCertificate_color_lower_bound P ring isLeader certificate
      advance certificateLeader C hterminal)

/-- In a protocol whose safe states are all successor-certified, fewer than
`n` colors rule out Definition-1 safety itself, not merely one chosen
legitimacy predicate. -/
theorem no_definitionOneSafe_of_fewer_colors
    (P : PopulationProtocol) (ring : DirectedRing n)
    (isLeader : P.Y → Bool) (certificate : P.Q → Fin k)
    (advance : Fin k → Fin k) (certificateLeader : Fin k → Bool)
    (hclass : DefinitionOneSafeStatesUseSuccessorCertificate P ring isLeader
      certificate advance certificateLeader)
    (hcolors : k < n) (C : P.Configuration n) :
    ¬ PopulationProtocol.IsSafe P ring C isLeader := by
  intro hsafe
  obtain ⟨hsuccessor, houtput⟩ := hclass C hsafe
  exact no_successorCertificateSafe_of_fewer_colors P ring isLeader
    certificate advance certificateLeader hcolors C
    ⟨hsuccessor, houtput, hsafe⟩

/-! ## Exact iid scheduler obstruction -/

/-- A finite schedule succeeds in the scoped repair class when some prefix
reaches a successor-certified Definition-1 safe state. -/
def ReachesSuccessorCertificateSafeWithinSchedule
    (P : PopulationProtocol) (ring : DirectedRing n)
    (isLeader : P.Y → Bool) (certificate : P.Q → Fin k)
    (advance : Fin k → Fin k) (certificateLeader : Fin k → Bool)
    (C : P.Configuration n) (schedule : DetSchedule n) : Prop :=
  ∃ prefixLength : Nat, prefixLength ≤ schedule.length ∧
    SuccessorCertificateSafe P ring isLeader certificate advance
      certificateLeader
      (runSchedule P ring C (schedule.take prefixLength))

/-- Exact multiplicity count of length-`t` scheduler words that reach the
scoped terminal class at some prefix. -/
noncomputable def successorCertificateStabilizingScheduleCount
    (P : PopulationProtocol) (ring : DirectedRing n)
    (isLeader : P.Y → Bool) (certificate : P.Q → Fin k)
    (advance : Fin k → Fin k) (certificateLeader : Fin k → Bool)
    (C : P.Configuration n) (t : Nat) : Nat := by
  classical
  exact (allSchedules n t).countP (fun schedule ↦
    if ReachesSuccessorCertificateSafeWithinSchedule P ring isLeader
      certificate advance certificateLeader C schedule then true else false)

/-- If `k < n`, no schedule can reach the scoped terminal class, even at an
intermediate prefix. -/
theorem not_reachesSuccessorCertificateSafe_of_fewer_colors
    (P : PopulationProtocol) (ring : DirectedRing n)
    (isLeader : P.Y → Bool) (certificate : P.Q → Fin k)
    (advance : Fin k → Fin k) (certificateLeader : Fin k → Bool)
    (hcolors : k < n) (C : P.Configuration n) (schedule : DetSchedule n) :
    ¬ ReachesSuccessorCertificateSafeWithinSchedule P ring isLeader
      certificate advance certificateLeader C schedule := by
  rintro ⟨prefixLength, _hprefix, hterminal⟩
  exact no_successorCertificateSafe_of_fewer_colors P ring isLeader
    certificate advance certificateLeader hcolors _ hterminal

/-- Exact iid no-go: below `n` colors, the successful scheduler count is zero
at every horizon and from every initial configuration. -/
theorem successorCertificateStabilizingScheduleCount_eq_zero
    (P : PopulationProtocol) (ring : DirectedRing n)
    (isLeader : P.Y → Bool) (certificate : P.Q → Fin k)
    (advance : Fin k → Fin k) (certificateLeader : Fin k → Bool)
    (hcolors : k < n) (C : P.Configuration n) (t : Nat) :
    successorCertificateStabilizingScheduleCount P ring isLeader certificate
      advance certificateLeader C t = 0 := by
  classical
  unfold successorCertificateStabilizingScheduleCount
  have hpred :
      (fun schedule : DetSchedule n ↦
        if ReachesSuccessorCertificateSafeWithinSchedule P ring isLeader
          certificate advance certificateLeader C schedule
        then true else false) = (fun _ ↦ false) := by
    funext schedule
    rw [if_neg]
    exact not_reachesSuccessorCertificateSafe_of_fewer_colors P ring
      isLeader certificate advance certificateLeader hcolors C schedule
  rw [hpred]
  simp

/-- For the protocol class above, the repository's standard Definition-1
successful-schedule count is exactly zero at every horizon. -/
theorem definitionOneStabilizingScheduleCount_eq_zero
    (P : PopulationProtocol) (ring : DirectedRing n)
    (isLeader : P.Y → Bool) (certificate : P.Q → Fin k)
    (advance : Fin k → Fin k) (certificateLeader : Fin k → Bool)
    (hclass : DefinitionOneSafeStatesUseSuccessorCertificate P ring isLeader
      certificate advance certificateLeader)
    (hcolors : k < n) (C : P.Configuration n) (t : Nat) :
    stabilizingScheduleCount P ring isLeader C t = 0 := by
  classical
  unfold stabilizingScheduleCount
  have hpred :
      (fun schedule : DetSchedule n ↦
        if ReachesSafeWithinSchedule P ring isLeader C schedule
        then true else false) = (fun _ ↦ false) := by
    funext schedule
    rw [if_neg]
    rintro ⟨prefixLength, _hprefix, hsafe⟩
    exact no_definitionOneSafe_of_fewer_colors P ring isLeader certificate
      advance certificateLeader hclass hcolors _ hsafe
  rw [hpred]
  simp

/-- Uniform finite-horizon iid success statement for the scoped repair class.
The scheduler list retains all `n^t` words with their exact multiplicities. -/
def SuccessorCertificateUniformFiniteHorizon
    (P : PopulationProtocol) (ring : DirectedRing n)
    (isLeader : P.Y → Bool) (certificate : P.Q → Fin k)
    (advance : Fin k → Fin k) (certificateLeader : Fin k → Bool)
    (t allowedFailures : Nat) : Prop :=
  ∀ C : P.Configuration n,
    (allSchedules n t).length ≤
      successorCertificateStabilizingScheduleCount P ring isLeader certificate
        advance certificateLeader C t + allowedFailures

/-- No horizon, polynomial or otherwise, can give a failure budget below the
full iid sample space when `k < n`.  The explicit state `q0` discharges
inhabitedness of the arbitrary-initialization quantifier. -/
theorem no_nontrivial_uniform_iid_bound_of_fewer_colors
    (P : PopulationProtocol) (ring : DirectedRing n)
    (isLeader : P.Y → Bool) (certificate : P.Q → Fin k)
    (advance : Fin k → Fin k) (certificateLeader : Fin k → Bool)
    (q0 : P.Q) (hcolors : k < n) (t allowedFailures : Nat)
    (hbudget : allowedFailures < n ^ t) :
    ¬ SuccessorCertificateUniformFiniteHorizon P ring isLeader certificate
      advance certificateLeader t allowedFailures := by
  intro hbound
  let C0 : P.Configuration n := fun _ ↦ q0
  have hC0 := hbound C0
  rw [allSchedules_length,
    successorCertificateStabilizingScheduleCount_eq_zero P ring isLeader
      certificate advance certificateLeader hcolors C0 t,
    Nat.zero_add] at hC0
  exact Nat.not_le_of_lt hbudget hC0

/-- Direct no-go for the repository's standard arbitrary-initialization iid
Definition-1 specification.  Any failure budget smaller than the full `n^t`
sample space is impossible, at every horizon. -/
theorem no_standard_uniformFiniteHorizonSSLE_of_fewer_colors
    (P : PopulationProtocol) (ring : DirectedRing n)
    (isLeader : P.Y → Bool) (certificate : P.Q → Fin k)
    (advance : Fin k → Fin k) (certificateLeader : Fin k → Bool)
    (hclass : DefinitionOneSafeStatesUseSuccessorCertificate P ring isLeader
      certificate advance certificateLeader)
    (q0 : P.Q) (hcolors : k < n) (t allowedFailures : Nat)
    (hbudget : allowedFailures < n ^ t) :
    ¬ UniformFiniteHorizonSSLE P ring isLeader t allowedFailures := by
  intro hbound
  let C0 : P.Configuration n := fun _ ↦ q0
  have hC0 := hbound C0
  rw [allSchedules_length,
    definitionOneStabilizingScheduleCount_eq_zero P ring isLeader certificate
      advance certificateLeader hclass hcolors C0 t,
    Nat.zero_add] at hC0
  exact Nat.not_le_of_lt hbudget hC0

/-! ## Equality witness: the existing factor-`n` epoch repair -/

/-- The filtered epoch protocol itself satisfies the protocol-class hypothesis
on every nontrivial ring.  R107 supplies color consensus from Definition-1
safety; equal consensus colors determine the successor rotation, while output
preservation to the clean sweep endpoint identifies the certificate leader. -/
theorem epochFilter_safeStatesUseSuccessorCertificate
    {n psi : Nat} (hn2 : 1 < n) (hpsi : psi > 0) (kappa : Nat)
    (ring : DirectedRing n) :
    DefinitionOneSafeStatesUseSuccessorCertificate
      (ppllEpochFilterProtocol hpsi kappa ring.hn) ring isLeaderOutput
      (fun state ↦ state.slot) (nextSlot ring.hn) slotLeader := by
  intro C hsafe
  obtain ⟨anchor, hcolor⟩ :=
    epochColorConsensus_of_filtered_isSafe hn2 hpsi kappa ring C hsafe
  have hrotation : ∀ i, (C i).slot.val = (anchor.val + i.val) % n := by
    intro i
    apply slot_rotation_of_epochColor_eq anchor i (C i)
    exact hcolor i
  have hsuccessor : ∀ i, (C (ring.rightNeighbor i)).slot =
      nextSlot ring.hn (C i).slot :=
    rotation_implies_covered ring.hn ring anchor C hrotation
  refine ⟨hsuccessor, ?_⟩
  let base := ppllEpochFilterPreWrapRun hpsi kappa hn2 ring C
  have hbaseProtected : ProtectedEpoch ring.hn ring base :=
    ppllEpochFilter_sweep_enters_protected hpsi kappa hn2 ring C
  have hbaseReach : PopulationProtocol.Reachable
      (ppllEpochFilterProtocol hpsi kappa ring.hn) ring C base :=
    ppllEpochFilter_sweep_reachable hpsi kappa hn2 ring C
  obtain ⟨_, _, _, hbaseClean⟩ := hbaseProtected
  intro i
  have hbaseColor : epochColor i (base i) = anchor := by
    calc
      epochColor i (base i) = epochColorConfig C ⟨0, ring.hn⟩ :=
        epochColorConfig_ppllEpochFilterPreWrapRun
          hn2 hpsi kappa ring C i
      _ = anchor := hcolor ⟨0, ring.hn⟩
  have hcurrentColor : epochColor i (C i) = anchor := hcolor i
  have hbaseSlot := slot_rotation_of_epochColor_eq anchor i (base i) hbaseColor
  have hcurrentSlot :=
    slot_rotation_of_epochColor_eq anchor i (C i) hcurrentColor
  have hslot : (base i).slot = (C i).slot := by
    apply Fin.ext
    rw [hbaseSlot, hcurrentSlot]
  have hout := hsafe.2 base hbaseReach i
  have hbaseOutput : isLeaderOutput
      ((ppllEpochFilterProtocol hpsi kappa ring.hn).output (base i)) =
      slotLeader (base i).slot := by
    have hleader := EpochClean.leader_eq (hbaseClean i)
    change isLeaderOutput
        (if (base i).core.leader then LeaderOutput.leader else .follower) =
      slotLeader (base i).slot
    rw [hleader]
    cases slotLeader (base i).slot <;>
      simp [isLeaderOutput]
  change isLeaderOutput
      ((ppllEpochFilterProtocol hpsi kappa ring.hn).output (C i)) =
    slotLeader (C i).slot
  exact (congrArg isLeaderOutput hout.symm).trans
    (hbaseOutput.trans (congrArg slotLeader hslot))

/-- A concrete bounded core used to make the equality witness closed rather
than conditional on an externally supplied base configuration. -/
def witnessBoundedCore {psi : Nat} (hpsi : psi > 0) (kappa : Nat) :
    BoundedAgentState psi kappa where
  leader := false
  probe := false
  phase := false
  bit := false
  wait := false
  state := .none
  path := .bot
  reset := false
  carry := false
  count := ⟨0, by omega⟩
  label := ⟨0, hpsi⟩
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

/-- Every protected state of the existing filtered epoch repair belongs to the
scoped successor-certificate class with exactly `k = n` colors. -/
theorem protectedEpoch_successorCertificateSafe
    {n psi : Nat} (hpsi : psi > 0) (kappa : Nat) (ring : DirectedRing n)
    (C : Fin n → EpochAgentState n psi kappa)
    (hprotected : ProtectedEpoch ring.hn ring C) :
    SuccessorCertificateSafe
      (ppllEpochFilterProtocol hpsi kappa ring.hn) ring isLeaderOutput
      (fun state ↦ state.slot) (nextSlot ring.hn) slotLeader C := by
  obtain ⟨anchor, hrotation, hsuccessor, hclean⟩ := hprotected
  have hprotected' : ProtectedEpoch ring.hn ring C :=
    ⟨anchor, hrotation, hsuccessor, hclean⟩
  refine ⟨hsuccessor, ?_, ppllEpochFilter_isSafe hpsi kappa ring hprotected'⟩
  intro i
  have hleader := EpochClean.leader_eq (hclean i)
  change isLeaderOutput
      (if (C i).core.leader then LeaderOutput.leader else .follower) =
    slotLeader (C i).slot
  rw [hleader]
  cases slotLeader (C i).slot <;>
    simp [isLeaderOutput]

/-- Canonical protected rotations show that the assumptions of the lower bound
are inhabited at equality `k = n`. -/
theorem canonicalEpoch_successorCertificateSafe
    {n psi : Nat} (hpsi : psi > 0) (kappa : Nat) (ring : DirectedRing n)
    (base : Fin n → BoundedAgentState psi kappa) :
    SuccessorCertificateSafe
      (ppllEpochFilterProtocol hpsi kappa ring.hn) ring isLeaderOutput
      (fun state ↦ state.slot) (nextSlot ring.hn) slotLeader
      (canonicalEpochConfig base) := by
  exact protectedEpoch_successorCertificateSafe hpsi kappa ring _
    (canonicalEpochConfig_protected ring.hn ring base)

/-- Fully concrete equality witness for every nonempty ring and positive label
alphabet: `k = n` successor colors really attain a Definition-1 safe state. -/
theorem exists_successorCertificateSafe_at_n_colors
    {n psi : Nat} (hpsi : psi > 0) (kappa : Nat)
    (ring : DirectedRing n) :
    ∃ C : Fin n → EpochAgentState n psi kappa,
      SuccessorCertificateSafe
        (ppllEpochFilterProtocol hpsi kappa ring.hn) ring isLeaderOutput
        (fun state ↦ state.slot) (nextSlot ring.hn) slotLeader C := by
  let base : Fin n → BoundedAgentState psi kappa :=
    fun _ ↦ witnessBoundedCore hpsi kappa
  exact ⟨canonicalEpochConfig base,
    canonicalEpoch_successorCertificateSafe hpsi kappa ring base⟩

/-- The existing filtered epoch carrier has exact factor-`n` semantic state
cardinality over its bounded core. -/
theorem epochFilter_exact_factor_n_state_count (n psi kappa : Nat) :
    (ppllEpochFilterStateCertificate n psi kappa).values.length =
      (PPLLFinite.boundedAgentState psi kappa).values.length * n :=
  ppllEpochFilterState_values_length n psi kappa

/-- The equality-size epoch repair stabilizes from every full-carrier initial
configuration with the existing explicit cubic iid Definition-1 bound. -/
theorem epochFilter_arbitrary_initialization_cubic_definitionOne
    {n psi : Nat} (hn2 : 1 < n) (hpsi : psi > 0) (kappa : Nat)
    (ring : DirectedRing n) (C : Fin n → EpochAgentState n psi kappa) :
    8 * filteredDefinitionOneFinalMissTree hpsi kappa ring C (8 * n ^ 3) ≤
      n ^ (8 * n ^ 3) := by
  apply filteredDefinitionOne_failure_eighth_at_eight_cubic
    hn2 hpsi kappa ring C (8 * n ^ 3)
  omega

/-- The selected corrected endpoint theorem in its state-complexity context:
the existing epoch carrier costs exactly one `Fin n` factor over the bounded
core, while `Nat.log2 n + 1` exact cubic blocks reduce the final Definition-1
failure numerator to at most a `1/n` fraction of all scheduler words. -/
theorem epochFilter_factor_n_state_count_and_oneOverN_definitionOne
    {n psi : Nat} (hn2 : 1 < n) (hpsi : psi > 0) (kappa : Nat)
    (ring : DirectedRing n) (C : Fin n → EpochAgentState n psi kappa) :
    (ppllEpochFilterStateCertificate n psi kappa).values.length =
        (PPLLFinite.boundedAgentState psi kappa).values.length * n ∧
      (let blockLength := 8 * n ^ 3
       let blocks := n.log2 + 1
       n * filteredDefinitionOneFinalMissTree hpsi kappa ring C
            (blocks * blockLength) ≤
         n ^ (blocks * blockLength)) := by
  constructor
  · exact epochFilter_exact_factor_n_state_count n psi kappa
  · exact epochFilter_arbitrary_initialization_oneOverN_definitionOne
      hn2 hpsi kappa ring C

end PPLLEpochSuccessorOverlayLowerBound
