import Leader.Wu.Epoch.ProtectedProtocol
import Leader.Core.ModArith

/-!
# General directed sweep into the protected epoch

For `n≥2`, the non-wrap schedule `[0,1,...,n-2]` propagates the initial slot at
position zero through the ring, cleaning each endpoint.  The resulting complete
rotation already implies wrap-edge coverage, so edge `n-1` is redundant.  For
`n=1`, the single self-edge is needed to sanitize the sole endpoint.

This file develops the structural induction for arbitrary `n`; it uses no state
enumeration.  Combined with protected closedness, the explicit sweep is the
deterministic entry event for a later exact uniform-scheduler bound.
-/

namespace PPLLProtectedEpochSweep

open PPLL PPLLResearchFormulation PPLLProtectedEpochProtocol

/-- First `k` directed edges `[0,1,...,k-1]`. -/
def epochSweepPrefix (n : Nat) : (k : Nat) → k ≤ n → DetSchedule n
  | 0, _ => []
  | k + 1, hk =>
      epochSweepPrefix n k (Nat.le_trans (Nat.le_succ k) hk) ++
        [⟨k, Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk⟩]

/-- Prefix construction has exactly the requested number of edges. -/
theorem epochSweepPrefix_length (n k : Nat) (hk : k ≤ n) :
    (epochSweepPrefix n k hk).length = k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      simp [epochSweepPrefix, ih]

/-- Full edge sweep `[0,1,...,n-1]`. -/
def epochSweep (n : Nat) : DetSchedule n :=
  epochSweepPrefix n n (Nat.le_refl n)

private theorem epochRunLocalSchedule_reachable
    (ring : DirectedRing n) (C : Fin n → EpochAgentState n ψ κ)
    (s : DetSchedule n) :
    PopulationProtocol.Reachable (epochProtocol ring.hn ψ κ) ring C
      (runLocalSchedule ring (epochTransition ring.hn) C s) := by
  induction s generalizing C with
  | nil =>
      exact @PopulationProtocol.Reachable.refl n
        (epochProtocol ring.hn ψ κ) ring C
  | cons e rest ih =>
      exact (PopulationProtocol.OneStep.to_reachable ⟨e, rfl⟩).trans
        (ih (localStep ring (epochTransition ring.hn) C e))

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

private theorem run_epochSweepPrefix_succ
    (hn : n > 0) (ring : DirectedRing n)
    (C : Fin n → EpochAgentState n ψ κ)
    {k : Nat} (hk : k + 1 ≤ n) :
    runLocalSchedule ring (epochTransition hn) C
        (epochSweepPrefix n (k + 1) hk) =
      localStep ring (epochTransition hn)
        (runLocalSchedule ring (epochTransition hn) C
          (epochSweepPrefix n k (Nat.le_trans (Nat.le_succ k) hk)))
        ⟨k, Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk⟩ := by
  change runLocalSchedule ring (epochTransition hn) C
      (epochSweepPrefix n k (Nat.le_trans (Nat.le_succ k) hk) ++
        [⟨k, Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk⟩]) = _
  rw [runLocalSchedule_append]
  rfl

private theorem rightNeighbor_nonwrap
    (ring : DirectedRing n) {k : Nat} (hk : k + 1 < n) :
    ring.rightNeighbor (⟨k, by omega⟩ : Fin n) =
      (⟨k + 1, hk⟩ : Fin n) := by
  apply Fin.ext
  simp [DirectedRing.rightNeighbor, Nat.mod_eq_of_lt hk]

private theorem epochTransition_fst_eq_of_clean
    (hn : n > 0) {l r : EpochAgentState n ψ κ}
    (hl : EpochClean l) :
    (epochTransition hn l r).1 = l := by
  unfold epochTransition
  dsimp only
  exact hl

private theorem mod_add_mod_right (a b n : Nat) :
    (a + b % n) % n = (a + b) % n := by
  rw [Nat.add_mod a (b % n) n, Nat.mod_mod]
  exact (Nat.add_mod a b n).symm

/-- A complete slot rotation automatically covers every directed edge,
including the modular wrap. -/
theorem rotation_implies_covered
    (hn : n > 0) (ring : DirectedRing n)
    (anchor : Fin n) (D : Fin n → EpochAgentState n ψ κ)
    (hrot : ∀ i, (D i).slot.val = (anchor.val + i.val) % n) :
    ∀ i, (D (ring.rightNeighbor i)).slot = nextSlot hn (D i).slot := by
  intro i
  apply Fin.ext
  change (D (ring.rightNeighbor i)).slot.val =
    ((D i).slot.val + 1) % n
  rw [hrot (ring.rightNeighbor i), hrot i]
  change (anchor.val + (i.val + 1) % n) % n =
    ((anchor.val + i.val) % n + 1) % n
  rw [mod_add_mod_right, mod_succ_eq]
  simp [Nat.add_assoc]

/-- Prefix invariant: positions through `k` form the anchored rotation and are
physically clean. -/
def SweepPrefixInv (anchor : Fin n) (k : Nat)
    (D : Fin n → EpochAgentState n ψ κ) : Prop :=
  (∀ i, i.val ≤ k →
    (D i).slot.val = (anchor.val + i.val) % n) ∧
  (∀ i, i.val ≤ k → EpochClean (D i))

/-- Run the first `k` sweep edges. -/
def epochSweepPrefixRun (ring : DirectedRing n)
    (C : Fin n → EpochAgentState n ψ κ) (k : Nat) (hk : k ≤ n) :=
  runLocalSchedule ring (epochTransition ring.hn) C
    (epochSweepPrefix n k hk)

private theorem sweepPrefixInv_step
    (hn : n > 0) (ring : DirectedRing n)
    (anchor : Fin n) (k : Nat) (hnext : k + 1 < n)
    (D : Fin n → EpochAgentState n ψ κ)
    (hD : SweepPrefixInv anchor k D) :
    SweepPrefixInv anchor (k + 1)
      (localStep ring (epochTransition hn) D ⟨k, by omega⟩) := by
  let e : Fin n := ⟨k, by omega⟩
  let j : Fin n := ⟨k + 1, hnext⟩
  let q := epochTransition hn (D e) (D j)
  let D' := localStep ring (epochTransition hn) D e
  have hneighbor : ring.rightNeighbor e = j :=
    rightNeighbor_nonwrap ring hnext
  have hne : j ≠ e := by
    intro h
    have hv := congrArg Fin.val h
    change k + 1 = k at hv
    omega
  have hDeClean : EpochClean (D e) := hD.2 e (by
    change k ≤ k
    omega)
  have hleft : q.1 = D e :=
    epochTransition_fst_eq_of_clean hn hDeClean
  have hq := epochTransition_covers_selected hn (D e) (D j)
  change q.2.slot = nextSlot hn q.1.slot ∧
    EpochClean q.1 ∧ EpochClean q.2 at hq
  have hD'e : D' e = q.1 := by
    simp [D', localStep, hneighbor, q]
  have hD'j : D' j = q.2 := by
    simp [D', localStep, hneighbor, hne, q]
  have hprefix : ∀ i, i.val ≤ k → D' i = D i := by
    intro i hi
    by_cases hie : i = e
    · subst i
      rw [hD'e, hleft]
    · have hij : i ≠ j := by
        intro hij
        have hv := congrArg Fin.val hij
        change i.val = k + 1 at hv
        omega
      simp [D', localStep, hneighbor, hie, hij]
  change SweepPrefixInv anchor (k + 1) D'
  constructor
  · intro i hi
    by_cases hold : i.val ≤ k
    · rw [hprefix i hold]
      exact hD.1 i hold
    · have hval : i.val = k + 1 := by omega
      have hij : i = j := Fin.ext hval
      subst i
      have heq : e.val ≤ k := by
        change k ≤ k
        omega
      rw [hD'j, hq.1, hleft]
      change ((D e).slot.val + 1) % n =
        (anchor.val + j.val) % n
      rw [hD.1 e heq]
      change (((anchor.val + k) % n + 1) % n) =
        (anchor.val + (k + 1)) % n
      rw [mod_succ_eq]
      congr 1
  · intro i hi
    by_cases hold : i.val ≤ k
    · rw [hprefix i hold]
      exact hD.2 i hold
    · have hval : i.val = k + 1 := by omega
      have hij : i = j := Fin.ext hval
      subst i
      rw [hD'j]
      exact hq.2.2

private theorem sweepPrefix_one_inv
    (hn2 : 1 < n) (ring : DirectedRing n)
    (C : Fin n → EpochAgentState n ψ κ) :
    let e : Fin n := ⟨0, by omega⟩
    let anchor := (C e).slot
    let D := epochSweepPrefixRun ring C 1 (by omega)
    SweepPrefixInv anchor 1 D := by
  let e : Fin n := ⟨0, by omega⟩
  let j : Fin n := ⟨1, by omega⟩
  let q := epochTransition ring.hn (C e) (C j)
  let D := epochSweepPrefixRun ring C 1 (by omega)
  have hneighbor : ring.rightNeighbor e = j := by
    exact rightNeighbor_nonwrap ring (k := 0) (by omega)
  have hrun := run_epochSweepPrefix_succ ring.hn ring C (k := 0)
    (by omega : 0 + 1 ≤ n)
  change D = localStep ring (epochTransition ring.hn) C e at hrun
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
  have hq := epochTransition_covers_selected ring.hn (C e) (C j)
  change q.2.slot = nextSlot ring.hn q.1.slot ∧
    EpochClean q.1 ∧ EpochClean q.2 at hq
  have hq1slot : q.1.slot = (C e).slot := by rfl
  change SweepPrefixInv (C e).slot 1 D
  constructor
  · intro i hi
    have hv : i.val = 0 ∨ i.val = 1 := by omega
    rcases hv with hv | hv
    · have hie : i = e := Fin.ext hv
      subst i
      rw [hDe, hq1slot]
      change (C e).slot.val = ((C e).slot.val + 0) % n
      simp [Nat.mod_eq_of_lt (C e).slot.isLt]
    · have hij : i = j := Fin.ext hv
      subst i
      rw [hDj, hq.1, hq1slot]
      rfl
  · intro i hi
    have hv : i.val = 0 ∨ i.val = 1 := by omega
    rcases hv with hv | hv
    · have hie : i = e := Fin.ext hv
      subst i
      rw [hDe]
      exact hq.2.1
    · have hij : i = j := Fin.ext hv
      subst i
      rw [hDj]
      exact hq.2.2

private theorem sweepPrefix_inv
    (hn2 : 1 < n) (ring : DirectedRing n)
    (C : Fin n → EpochAgentState n ψ κ)
    (k : Nat) (hk1 : 1 ≤ k) (hklt : k < n) :
    let e0 : Fin n := ⟨0, by omega⟩
    SweepPrefixInv (C e0).slot k
      (epochSweepPrefixRun ring C k (Nat.le_of_lt hklt)) := by
  induction k with
  | zero => omega
  | succ k ih =>
      by_cases hk0 : k = 0
      · subst k
        simpa [epochSweepPrefixRun] using
          (sweepPrefix_one_inv (ψ := ψ) (κ := κ) hn2 ring C)
      · have hkpos : 1 ≤ k := by omega
        have hklt' : k < n := by omega
        let e0 : Fin n := ⟨0, by omega⟩
        let D := epochSweepPrefixRun ring C k (Nat.le_of_lt hklt')
        have hprev : SweepPrefixInv (C e0).slot k D := by
          exact ih hkpos hklt'
        have hstep := sweepPrefixInv_step ring.hn ring (C e0).slot k
          hklt D hprev
        have hrun := run_epochSweepPrefix_succ ring.hn ring C
          (k := k) (Nat.le_of_lt hklt)
        change epochSweepPrefixRun ring C (k + 1) (Nat.le_of_lt hklt) =
          localStep ring (epochTransition ring.hn) D ⟨k, by omega⟩ at hrun
        rw [hrun]
        exact hstep

/-- Non-wrap sweep `[0,1,...,n-2]`; it already covers the wrap algebraically. -/
def epochPreWrapSweep (n : Nat) (hn2 : 1 < n) : DetSchedule n :=
  epochSweepPrefix n (n - 1) (by omega)

/-- Execute the non-wrap sweep. -/
def epochPreWrapRun (hn2 : 1 < n) (ring : DirectedRing n)
    (C : Fin n → EpochAgentState n ψ κ) :=
  runLocalSchedule ring (epochTransition ring.hn) C
    (epochPreWrapSweep n hn2)

/-- For every nontrivial ring, the shorter non-wrap sweep enters the protected
epoch from every arbitrary physical state. -/
theorem epochPreWrapSweep_enters_protected
    (hn2 : 1 < n) (ring : DirectedRing n)
    (C : Fin n → EpochAgentState n ψ κ) :
    ProtectedEpoch ring.hn ring (epochPreWrapRun hn2 ring C) := by
  let e0 : Fin n := ⟨0, by omega⟩
  let anchor := (C e0).slot
  let D := epochPreWrapRun hn2 ring C
  have hprefix := sweepPrefix_inv hn2 ring C (n - 1)
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

/-- The general non-wrap sweep endpoint is Definition-1 safe. -/
theorem epochPreWrapSweep_isSafe
    (hn2 : 1 < n) (ring : DirectedRing n)
    (C : Fin n → EpochAgentState n ψ κ) :
    PopulationProtocol.IsSafe (epochProtocol ring.hn ψ κ) ring
      (epochPreWrapRun hn2 ring C) isLeaderOutput :=
  protectedEpoch_isSafe ring.hn ring
    (epochPreWrapSweep_enters_protected hn2 ring C)

/-- The general non-wrap sweep endpoint is reachable. -/
theorem epochPreWrapSweep_reachable
    (hn2 : 1 < n) (ring : DirectedRing n)
    (C : Fin n → EpochAgentState n ψ κ) :
    PopulationProtocol.Reachable (epochProtocol ring.hn ψ κ) ring C
      (epochPreWrapRun hn2 ring C) := by
  exact epochRunLocalSchedule_reachable ring C (epochPreWrapSweep n hn2)

/-- The named `n-1` scheduler outcome reaches semantic safety at its full
prefix. -/
theorem epochPreWrap_reachesSafeWithinSchedule
    (hn2 : 1 < n) (ring : DirectedRing n)
    (C : Fin n → EpochAgentState n ψ κ) :
    ReachesSafeWithinSchedule (epochProtocol ring.hn ψ κ) ring
      isLeaderOutput C (epochPreWrapSweep n hn2) := by
  have hlen : (epochPreWrapSweep n hn2).length = n - 1 := by
    exact epochSweepPrefix_length n (n - 1) (by omega)
  refine ⟨n - 1, by omega, ?_⟩
  have htake : (epochPreWrapSweep n hn2).take (n - 1) =
      epochPreWrapSweep n hn2 := by
    rw [← hlen]
    exact List.take_length
  rw [htake]
  have heq := runLocalSchedule_eq_runSchedule
    (epochProtocol ring.hn ψ κ) ring C (epochPreWrapSweep n hn2)
  rw [← heq]
  exact epochPreWrapSweep_isSafe hn2 ring C

/-- At least one uniform length-`n-1` outcome reaches genuine semantic safety
from every initial epoch configuration. -/
theorem epochPreWrap_stabilizingScheduleCount_pos
    (hn2 : 1 < n) (ring : DirectedRing n)
    (C : Fin n → EpochAgentState n ψ κ) :
    0 < stabilizingScheduleCount (epochProtocol ring.hn ψ κ) ring
      isLeaderOutput C (n - 1) := by
  classical
  unfold stabilizingScheduleCount
  apply List.countP_pos_iff.mpr
  refine ⟨epochPreWrapSweep n hn2,
    mem_allSchedules_of_length n (n - 1) (epochPreWrapSweep n hn2)
      (epochSweepPrefix_length n (n - 1) (by omega)), ?_⟩
  simp [epochPreWrap_reachesSafeWithinSchedule hn2 ring C]

/-- General finite uniform phase for the expensive epoch protocol: one known
favorable schedule among `n^(n-1)` outcomes. -/
theorem epoch_uniformFiniteHorizon
    (hn2 : 1 < n) (ring : DirectedRing n) :
    UniformFiniteHorizonSSLE (epochProtocol ring.hn ψ κ) ring
      isLeaderOutput (n - 1) (n ^ (n - 1) - 1) := by
  intro C
  rw [allSchedules_length]
  have hcount := epochPreWrap_stabilizingScheduleCount_pos hn2 ring C
  have htotal : 0 < n ^ (n - 1) := Nat.pow_pos ring.hn
  omega

/-- End-to-end finite SSLE capstone for the separately named epoch protocol:
physical legitimacy is closed and semantically safe, and every arbitrary state
has at least one favorable uniform scheduler outcome at horizon `n-1`. -/
theorem epoch_finite_ssle_capstone
    (hn2 : 1 < n) (ring : DirectedRing n) :
    PopulationProtocol.ClosedPred (epochProtocol ring.hn ψ κ) ring
        (ProtectedEpoch ring.hn ring) ∧
      (∀ C : Fin n → EpochAgentState n ψ κ,
        ProtectedEpoch ring.hn ring C →
          PopulationProtocol.IsSafe (epochProtocol ring.hn ψ κ) ring C
            isLeaderOutput) ∧
      UniformFiniteHorizonSSLE (epochProtocol ring.hn ψ κ) ring
        isLeaderOutput (n - 1) (n ^ (n - 1) - 1) := by
  exact ⟨protectedEpoch_closed ring.hn ring,
    fun C hC => protectedEpoch_isSafe ring.hn ring hC,
    epoch_uniformFiniteHorizon hn2 ring⟩

/-- Every nontrivial-ring start has a reachable safe future under the explicit
`n-1` edge sweep. -/
theorem epoch_exists_reachable_safe
    (hn2 : 1 < n) (ring : DirectedRing n)
    (C : Fin n → EpochAgentState n ψ κ) :
    ∃ C' : Fin n → EpochAgentState n ψ κ,
      PopulationProtocol.Reachable (epochProtocol ring.hn ψ κ) ring C C' ∧
      PopulationProtocol.IsSafe (epochProtocol ring.hn ψ κ) ring C'
        isLeaderOutput :=
  ⟨epochPreWrapRun hn2 ring C,
    epochPreWrapSweep_reachable hn2 ring C,
    epochPreWrapSweep_isSafe hn2 ring C⟩

end PPLLProtectedEpochSweep
