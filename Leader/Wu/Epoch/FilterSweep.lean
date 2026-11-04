import Leader.Wu.Epoch.FilterRepair

/-!
# Arbitrary-state entry for the P_PLL-derived epoch filter

The non-wrap schedule `[0,1,...,n-2]` used by the pure epoch protocol also
works after the integrated P_PLL core is inserted.  The proof does not assume
that the filtered initiator is unchanged: P_PLL may update retained `bit` and
`label`.  It uses only the exact local contract that the initiator slot is
framed, the responder receives its successor slot, and both outputs are clean.

This yields a corrected finite stabilization capstone for the explicitly named
repair.  Counting one favorable schedule gives a valid but tiny success bound;
a WHP runtime analogue of Theorem 4.1.13 remains a separate theorem.
-/

namespace PPLLDerivedEpochSweep

open PPLL PPLLResearchFormulation PPLLProtectedEpochProtocol
  PPLLProtectedEpochSweep PPLLDerivedEpochRepair

/-! ## Structural sweep invariant -/

private theorem runLocalSchedule_append
    {Q : Type} (ring : DirectedRing n) (T : Q → Q → Q × Q)
    (C : Fin n → Q) (s t : DetSchedule n) :
    runLocalSchedule ring T C (s ++ t) =
      runLocalSchedule ring T (runLocalSchedule ring T C s) t := by
  induction s generalizing C with
  | nil => rfl
  | cons e rest ih =>
      simp only [List.cons_append, runLocalSchedule]
      exact ih (localStep ring T C e)

private theorem rightNeighbor_nonwrap
    (ring : DirectedRing n) {k : Nat} (hk : k + 1 < n) :
    ring.rightNeighbor (⟨k, by omega⟩ : Fin n) =
      (⟨k + 1, hk⟩ : Fin n) := by
  apply Fin.ext
  simp [DirectedRing.rightNeighbor, Nat.mod_eq_of_lt hk]

/-- Execute the first `k` ordered edges under the P_PLL-derived filter. -/
def ppllEpochFilterPrefixRun
    (hψ : ψ > 0) (κ : Nat) (ring : DirectedRing n)
    (C : Fin n → EpochAgentState n ψ κ)
    (k : Nat) (hk : k ≤ n) : Fin n → EpochAgentState n ψ κ :=
  runLocalSchedule ring (ppllEpochFilterTransition hψ κ ring.hn) C
    (epochSweepPrefix n k hk)

private theorem run_filteredPrefix_succ
    (hψ : ψ > 0) (κ : Nat) (ring : DirectedRing n)
    (C : Fin n → EpochAgentState n ψ κ)
    {k : Nat} (hk : k + 1 ≤ n) :
    ppllEpochFilterPrefixRun hψ κ ring C (k + 1) hk =
      localStep ring (ppllEpochFilterTransition hψ κ ring.hn)
        (ppllEpochFilterPrefixRun hψ κ ring C k
          (Nat.le_trans (Nat.le_succ k) hk))
        ⟨k, Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk⟩ := by
  change runLocalSchedule ring (ppllEpochFilterTransition hψ κ ring.hn) C
      (epochSweepPrefix n k (Nat.le_trans (Nat.le_succ k) hk) ++
        [⟨k, Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk⟩]) = _
  rw [runLocalSchedule_append]
  rfl

private theorem filteredSweepInv_step
    (hψ : ψ > 0) (κ : Nat) (ring : DirectedRing n)
    (anchor : Fin n) (k : Nat) (hnext : k + 1 < n)
    (D : Fin n → EpochAgentState n ψ κ)
    (hD : SweepPrefixInv anchor k D) :
    SweepPrefixInv anchor (k + 1)
      (localStep ring (ppllEpochFilterTransition hψ κ ring.hn)
        D ⟨k, by omega⟩) := by
  let e : Fin n := ⟨k, by omega⟩
  let j : Fin n := ⟨k + 1, hnext⟩
  let q := ppllEpochFilterTransition hψ κ ring.hn (D e) (D j)
  let D' := localStep ring (ppllEpochFilterTransition hψ κ ring.hn) D e
  have hneighbor : ring.rightNeighbor e = j :=
    rightNeighbor_nonwrap ring hnext
  have hne : j ≠ e := by
    intro h
    have hv := congrArg Fin.val h
    change k + 1 = k at hv
    omega
  have hq := ppllEpochFilter_local_contract hψ κ ring.hn (D e) (D j)
  change q.1.slot = (D e).slot ∧
    q.2.slot = nextSlot ring.hn q.1.slot ∧
    EpochClean q.1 ∧ EpochClean q.2 at hq
  have hD'e : D' e = q.1 := by
    simp [D', localStep, hneighbor, q]
  have hD'j : D' j = q.2 := by
    simp [D', localStep, hneighbor, hne, q]
  change SweepPrefixInv anchor (k + 1) D'
  constructor
  · intro i hi
    by_cases hold : i.val ≤ k
    · by_cases hie : i = e
      · subst i
        rw [hD'e, hq.1]
        exact hD.1 e (by simp [e])
      · have hij : i ≠ j := by
          intro hij
          have hv := congrArg Fin.val hij
          change i.val = k + 1 at hv
          omega
        simp [D', localStep, hneighbor, hie, hij]
        exact hD.1 i hold
    · have hval : i.val = k + 1 := by omega
      have hij : i = j := Fin.ext hval
      subst i
      rw [hD'j, hq.2.1, hq.1]
      change ((D e).slot.val + 1) % n =
        (anchor.val + (k + 1)) % n
      rw [hD.1 e (by simp [e])]
      exact mod_add_one anchor.val k n
  · intro i hi
    by_cases hold : i.val ≤ k
    · by_cases hie : i = e
      · subst i
        rw [hD'e]
        exact hq.2.2.1
      · have hij : i ≠ j := by
          intro hij
          have hv := congrArg Fin.val hij
          change i.val = k + 1 at hv
          omega
        simpa [D', localStep, hneighbor, hie, hij] using hD.2 i hold
    · have hval : i.val = k + 1 := by omega
      have hij : i = j := Fin.ext hval
      subst i
      rw [hD'j]
      exact hq.2.2.2

private theorem filteredSweep_one_inv
    (hψ : ψ > 0) (κ : Nat) (hn2 : 1 < n)
    (ring : DirectedRing n)
    (C : Fin n → EpochAgentState n ψ κ) :
    let e : Fin n := ⟨0, by omega⟩
    let D := ppllEpochFilterPrefixRun hψ κ ring C 1 (by omega)
    SweepPrefixInv (C e).slot 1 D := by
  let e : Fin n := ⟨0, by omega⟩
  let j : Fin n := ⟨1, by omega⟩
  let q := ppllEpochFilterTransition hψ κ ring.hn (C e) (C j)
  let D := ppllEpochFilterPrefixRun hψ κ ring C 1 (by omega)
  have hneighbor : ring.rightNeighbor e = j :=
    rightNeighbor_nonwrap ring (k := 0) (by omega)
  have hrun := run_filteredPrefix_succ hψ κ ring C
    (k := 0) (by omega : 0 + 1 ≤ n)
  change D = localStep ring
    (ppllEpochFilterTransition hψ κ ring.hn) C e at hrun
  have hne : j ≠ e := by
    intro h
    have hv := congrArg Fin.val h
    change (1 : Nat) = 0 at hv
    omega
  have hDe : D e = q.1 := by
    rw [hrun]
    simp [localStep, hneighbor, q]
  have hDj : D j = q.2 := by
    rw [hrun]
    simp [localStep, hneighbor, hne, q]
  have hq := ppllEpochFilter_local_contract hψ κ ring.hn (C e) (C j)
  change q.1.slot = (C e).slot ∧
    q.2.slot = nextSlot ring.hn q.1.slot ∧
    EpochClean q.1 ∧ EpochClean q.2 at hq
  change SweepPrefixInv (C e).slot 1 D
  constructor
  · intro i hi
    have hv : i.val = 0 ∨ i.val = 1 := by omega
    rcases hv with hv | hv
    · have hie : i = e := Fin.ext hv
      subst i
      rw [hDe, hq.1]
      change (C e).slot.val = ((C e).slot.val + 0) % n
      simp [Nat.mod_eq_of_lt (C e).slot.isLt]
    · have hij : i = j := Fin.ext hv
      subst i
      rw [hDj, hq.2.1, hq.1]
      rfl
  · intro i hi
    have hv : i.val = 0 ∨ i.val = 1 := by omega
    rcases hv with hv | hv
    · have hie : i = e := Fin.ext hv
      subst i
      rw [hDe]
      exact hq.2.2.1
    · have hij : i = j := Fin.ext hv
      subst i
      rw [hDj]
      exact hq.2.2.2

private theorem filteredSweep_inv
    (hψ : ψ > 0) (κ : Nat) (hn2 : 1 < n)
    (ring : DirectedRing n)
    (C : Fin n → EpochAgentState n ψ κ)
    (k : Nat) (hk1 : 1 ≤ k) (hklt : k < n) :
    let e0 : Fin n := ⟨0, by omega⟩
    SweepPrefixInv (C e0).slot k
      (ppllEpochFilterPrefixRun hψ κ ring C k (Nat.le_of_lt hklt)) := by
  induction k with
  | zero => omega
  | succ k ih =>
      by_cases hk0 : k = 0
      · subst k
        simpa using filteredSweep_one_inv hψ κ hn2 ring C
      · have hkpos : 1 ≤ k := by omega
        have hklt' : k < n := by omega
        let e0 : Fin n := ⟨0, by omega⟩
        let D := ppllEpochFilterPrefixRun hψ κ ring C k
          (Nat.le_of_lt hklt')
        have hprev : SweepPrefixInv (C e0).slot k D :=
          ih hkpos hklt'
        have hstep := filteredSweepInv_step hψ κ ring (C e0).slot k
          hklt D hprev
        have hrun := run_filteredPrefix_succ hψ κ ring C
          (k := k) (Nat.le_of_lt hklt)
        change ppllEpochFilterPrefixRun hψ κ ring C (k + 1)
          (Nat.le_of_lt hklt) =
          localStep ring (ppllEpochFilterTransition hψ κ ring.hn)
            D ⟨k, by omega⟩ at hrun
        rw [hrun]
        exact hstep

/-! ## Protected entry, reachability, and exact scheduler semantics -/

/-- Endpoint of the non-wrap sweep under the P_PLL-derived filter. -/
def ppllEpochFilterPreWrapRun
    (hψ : ψ > 0) (κ : Nat) (hn2 : 1 < n)
    (ring : DirectedRing n)
    (C : Fin n → EpochAgentState n ψ κ) :
    Fin n → EpochAgentState n ψ κ :=
  runLocalSchedule ring (ppllEpochFilterTransition hψ κ ring.hn) C
    (epochPreWrapSweep n hn2)

/-- Every arbitrary filtered-P_PLL state enters the protected rotation after
the ordered non-wrap sweep. -/
theorem ppllEpochFilter_sweep_enters_protected
    (hψ : ψ > 0) (κ : Nat) (hn2 : 1 < n)
    (ring : DirectedRing n)
    (C : Fin n → EpochAgentState n ψ κ) :
    ProtectedEpoch ring.hn ring
      (ppllEpochFilterPreWrapRun hψ κ hn2 ring C) := by
  let e0 : Fin n := ⟨0, by omega⟩
  let anchor := (C e0).slot
  let D := ppllEpochFilterPreWrapRun hψ κ hn2 ring C
  have hprefix := filteredSweep_inv hψ κ hn2 ring C (n - 1)
    (by omega) (by omega)
  change SweepPrefixInv anchor (n - 1) D at hprefix
  have hrot : ∀ i, (D i).slot.val = (anchor.val + i.val) % n := by
    intro i
    exact hprefix.1 i (by omega)
  have hclean : ∀ i, EpochClean (D i) := by
    intro i
    exact hprefix.2 i (by omega)
  exact ⟨anchor, hrot,
    rotation_implies_covered ring.hn ring anchor D hrot, hclean⟩

/-- The sweep endpoint is genuine Definition-1 safe for the repaired protocol. -/
theorem ppllEpochFilter_sweep_isSafe
    (hψ : ψ > 0) (κ : Nat) (hn2 : 1 < n)
    (ring : DirectedRing n)
    (C : Fin n → EpochAgentState n ψ κ) :
    PopulationProtocol.IsSafe
      (ppllEpochFilterProtocol hψ κ ring.hn) ring
      (ppllEpochFilterPreWrapRun hψ κ hn2 ring C) isLeaderOutput :=
  ppllEpochFilter_isSafe hψ κ ring
    (ppllEpochFilter_sweep_enters_protected hψ κ hn2 ring C)

private theorem ppllEpochFilter_run_reachable
    (hψ : ψ > 0) (κ : Nat) (ring : DirectedRing n)
    (C : Fin n → EpochAgentState n ψ κ) (s : DetSchedule n) :
    PopulationProtocol.Reachable
      (ppllEpochFilterProtocol hψ κ ring.hn) ring C
      (runLocalSchedule ring
        (ppllEpochFilterTransition hψ κ ring.hn) C s) := by
  induction s generalizing C with
  | nil =>
      exact @PopulationProtocol.Reachable.refl n
        (ppllEpochFilterProtocol hψ κ ring.hn) ring C
  | cons e rest ih =>
      exact (PopulationProtocol.OneStep.to_reachable ⟨e, rfl⟩).trans
        (ih (localStep ring
          (ppllEpochFilterTransition hψ κ ring.hn) C e))

/-- The explicit filtered sweep is a reachable execution. -/
theorem ppllEpochFilter_sweep_reachable
    (hψ : ψ > 0) (κ : Nat) (hn2 : 1 < n)
    (ring : DirectedRing n)
    (C : Fin n → EpochAgentState n ψ κ) :
    PopulationProtocol.Reachable
      (ppllEpochFilterProtocol hψ κ ring.hn) ring C
      (ppllEpochFilterPreWrapRun hψ κ hn2 ring C) := by
  exact ppllEpochFilter_run_reachable hψ κ ring C
    (epochPreWrapSweep n hn2)

/-- The named length-`n-1` schedule reaches semantic safety at its full prefix. -/
theorem ppllEpochFilter_reachesSafeWithinSchedule
    (hψ : ψ > 0) (κ : Nat) (hn2 : 1 < n)
    (ring : DirectedRing n)
    (C : Fin n → EpochAgentState n ψ κ) :
    ReachesSafeWithinSchedule
      (ppllEpochFilterProtocol hψ κ ring.hn) ring isLeaderOutput C
      (epochPreWrapSweep n hn2) := by
  have hlen : (epochPreWrapSweep n hn2).length = n - 1 :=
    epochSweepPrefix_length n (n - 1) (by omega)
  refine ⟨n - 1, by omega, ?_⟩
  have htake : (epochPreWrapSweep n hn2).take (n - 1) =
      epochPreWrapSweep n hn2 := by
    rw [← hlen]
    exact List.take_length
  rw [htake]
  have heq := runLocalSchedule_eq_runSchedule
    (ppllEpochFilterProtocol hψ κ ring.hn) ring C
      (epochPreWrapSweep n hn2)
  rw [← heq]
  exact ppllEpochFilter_sweep_isSafe hψ κ hn2 ring C

/-- At least one exact scheduler outcome stabilizes every arbitrary input. -/
theorem ppllEpochFilter_stabilizingScheduleCount_pos
    (hψ : ψ > 0) (κ : Nat) (hn2 : 1 < n)
    (ring : DirectedRing n)
    (C : Fin n → EpochAgentState n ψ κ) :
    0 < stabilizingScheduleCount
      (ppllEpochFilterProtocol hψ κ ring.hn) ring isLeaderOutput C (n - 1) := by
  classical
  unfold stabilizingScheduleCount
  apply List.countP_pos_iff.mpr
  refine ⟨epochPreWrapSweep n hn2,
    mem_allSchedules_of_length n (n - 1) (epochPreWrapSweep n hn2)
      (epochSweepPrefix_length n (n - 1) (by omega)), ?_⟩
  simp [ppllEpochFilter_reachesSafeWithinSchedule hψ κ hn2 ring C]

/-- Exact finite uniform phase for the P_PLL-derived epoch repair. -/
theorem ppllEpochFilter_uniformFiniteHorizon
    (hψ : ψ > 0) (κ : Nat) (hn2 : 1 < n)
    (ring : DirectedRing n) :
    UniformFiniteHorizonSSLE
      (ppllEpochFilterProtocol hψ κ ring.hn) ring isLeaderOutput
      (n - 1) (n ^ (n - 1) - 1) := by
  intro C
  rw [allSchedules_length]
  have hcount :=
    ppllEpochFilter_stabilizingScheduleCount_pos hψ κ hn2 ring C
  have htotal : 0 < n ^ (n - 1) := Nat.pow_pos ring.hn
  omega

/-- End-to-end corrected finite stabilization capstone.  It combines the
closed protected set (the repaired Lemma-4.1.1 role), semantic safety, and
arbitrary-state exact finite scheduler convergence.  It intentionally makes no
WHP asymptotic claim corresponding to the full Theorem 4.1.13. -/
theorem ppllEpochFilter_finite_ssle_capstone
    (hψ : ψ > 0) (κ : Nat) (hn2 : 1 < n)
    (ring : DirectedRing n) :
    PopulationProtocol.ClosedPred
        (ppllEpochFilterProtocol hψ κ ring.hn) ring
        (ProtectedEpoch ring.hn ring) ∧
      (∀ C : Fin n → EpochAgentState n ψ κ,
        ProtectedEpoch ring.hn ring C →
          PopulationProtocol.IsSafe
            (ppllEpochFilterProtocol hψ κ ring.hn) ring C
            isLeaderOutput) ∧
      UniformFiniteHorizonSSLE
        (ppllEpochFilterProtocol hψ κ ring.hn) ring isLeaderOutput
        (n - 1) (n ^ (n - 1) - 1) := by
  exact ⟨ppllEpochFilter_closed hψ κ ring,
    fun C hC => ppllEpochFilter_isSafe hψ κ ring hC,
    ppllEpochFilter_uniformFiniteHorizon hψ κ hn2 ring⟩

end PPLLDerivedEpochSweep
