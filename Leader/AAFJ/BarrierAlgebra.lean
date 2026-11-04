import Leader.AAFJ.Protocol
import Leader.Core.ModArith
import Init.GrindInstances.Ring.Fin
import Init.Data.List.Perm


/-!
# Deterministic charged-barrier algebra for generalized AAFJ `P_k`


This module sits strictly above `AAFJProtocol6`: the local journal transition is
not redefined here.  Instead we project a ring configuration to its labels,
define a modular defect on every directed edge, and prove the deterministic
algebra of one genuine barrier advance.


No stabilization, fairness, or probability theorem is stated here.
-/


namespace AAFJPK
namespace BarrierAlgebra


/-- A label configuration on an `n`-node ring. -/
abbrev Labels (n k : Nat) := Fin n → Fin k


/-- Forget every local field except the AAFJ label. -/
def labelsOf {n k : Nat} (C : Fin n → State k) : Labels n k :=
  fun i => (C i).label


/-- Explicit additive zero in `Fin k`, avoiding a declaration-level `NeZero k`
typeclass assumption when positivity is already carried as data. -/
def zeroResidue {k : Nat} (hk : 0 < k) : Fin k := ⟨0, hk⟩


/-! ## Minimal directed-ring geometry


The repository has equivalent geometry inside the P_PLL repair stack, but
importing that stack would be a false dependency for this AAFJ-only layer.
-/


/-- Clockwise successor is injective on every nonempty directed ring. -/
theorem rightNeighbor_injective (ring : DirectedRing n) :
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


/-- On a non-singleton ring an edge has distinct endpoints. -/
theorem rightNeighbor_ne_self (ring : DirectedRing n) (hn2 : 1 < n)
    (e : Fin n) : ring.rightNeighbor e ≠ e := by
  intro h
  have hv := congrArg Fin.val h
  unfold DirectedRing.rightNeighbor at hv
  dsimp only at hv
  by_cases he : e.val + 1 < n
  · rw [Nat.mod_eq_of_lt he] at hv
    omega
  · have heq : e.val + 1 = n := by omega
    rw [heq, Nat.mod_self] at hv
    omega


/-- Canonical enumeration of the ring positions, used only for the telescoping
argument showing that a barrier-free labeling forces `k ∣ n`. -/
def ringVertex (ring : DirectedRing n) (t : Nat) : Fin n :=
  ⟨t % n, Nat.mod_lt _ ring.hn⟩


/-- The canonical enumeration advances by the physical right-neighbor map. -/
theorem rightNeighbor_ringVertex (ring : DirectedRing n) (t : Nat) :
    ring.rightNeighbor (ringVertex ring t) = ringVertex ring (t + 1) := by
  apply Fin.ext
  unfold DirectedRing.rightNeighbor ringVertex
  dsimp only
  exact mod_succ_eq t n


/-- After exactly `n` canonical steps the enumeration returns to its start. -/
@[simp] theorem ringVertex_period (ring : DirectedRing n) :
    ringVertex ring n = ringVertex ring 0 := by
  apply Fin.ext
  simp [ringVertex]


/-! ## Modular defect and barrier support -/


/-- Charged defect on directed edge `e → e⁺`.


A zero defect means exactly `label(e⁺) = label(e)+1 (mod k)`.  Nonzero defects
are the generalized AAFJ barriers.  `Fin k` supplies the residue arithmetic;
no Mathlib `ZMod` is used.
-/
def defect {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (L : Labels n k) (e : Fin n) : Fin k :=
  L (ring.rightNeighbor e) - succLabel hk (L e)


/-- An edge is a barrier exactly when its modular defect is nonzero. -/
def BarrierAt {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (L : Labels n k) (e : Fin n) : Prop :=
  defect hk ring L e ≠ zeroResidue hk


instance instDecidableBarrierAt {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (L : Labels n k) (e : Fin n) :
    Decidable (BarrierAt hk ring L e) := by
  unfold BarrierAt
  infer_instance


/-- The defect definition is exactly the journal generalized-`P_k` barrier
condition. -/
theorem barrierAt_iff_journal {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (L : Labels n k) (e : Fin n) :
    BarrierAt hk ring L e ↔
      succLabel hk (L e) ≠ L (ring.rightNeighbor e) := by
  letI : NeZero k := ⟨by omega⟩
  have hz : zeroResidue hk = (0 : Fin k) := by
    apply Fin.ext
    simp [zeroResidue]
  unfold BarrierAt defect
  rw [hz]
  grind


/-- Projecting a full protocol state recovers the protocol's `IsBarrier` predicate. -/
theorem barrierAt_labelsOf_iff {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (C : Fin n → State k) (e : Fin n) :
    BarrierAt hk ring (labelsOf C) e ↔
      IsBarrier hk (C e) (C (ring.rightNeighbor e)) := by
  rw [barrierAt_iff_journal]
  rfl


/-- A non-barrier edge has the required successor label. -/
theorem label_successor_of_not_barrier {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (L : Labels n k) (e : Fin n)
    (h : ¬ BarrierAt hk ring L e) :
    L (ring.rightNeighbor e) = succLabel hk (L e) := by
  rw [barrierAt_iff_journal] at h
  exact (Decidable.not_not.mp h).symm


/-- Duplicate-free finite support of all charged barriers. -/
def barrierSupport {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (L : Labels n k) : List (Fin n) :=
  (ExhaustiveList.fin n).values.filter
    (fun e => decide (BarrierAt hk ring L e))


/-- Membership in the support is exactly the barrier predicate. -/
theorem mem_barrierSupport_iff {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (L : Labels n k) (e : Fin n) :
    e ∈ barrierSupport hk ring L ↔ BarrierAt hk ring L e := by
  simp [barrierSupport, (ExhaustiveList.fin n).complete e]


/-- The support list has no duplicate edges. -/
theorem barrierSupport_nodup {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (L : Labels n k) :
    (barrierSupport hk ring L).Nodup := by
  unfold barrierSupport
  exact (ExhaustiveList.values_nodup_fin n).filter _


/-- Number of currently charged barriers. -/
def barrierCount {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (L : Labels n k) : Nat :=
  (barrierSupport hk ring L).length


/-! ## Label-only barrier advance -/


/-- The label effect of a genuine barrier advance at edge `e`: only the
responder `e⁺` is relabeled, to the successor of the initiator's old label. -/
def advanceLabels {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (L : Labels n k) (e : Fin n) : Labels n k :=
  fun i =>
    if i = ring.rightNeighbor e then succLabel hk (L e) else L i


@[simp] theorem advanceLabels_right {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (L : Labels n k) (e : Fin n) :
    advanceLabels hk ring L e (ring.rightNeighbor e) = succLabel hk (L e) := by
  simp [advanceLabels]


/-- Every vertex other than the responder keeps its label. -/
theorem advanceLabels_other {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (L : Labels n k) (e i : Fin n)
    (h : i ≠ ring.rightNeighbor e) :
    advanceLabels hk ring L e i = L i := by
  simp [advanceLabels, h]


/-- Advancing a barrier repairs the activated edge itself.


`1 < n` is essential: on a singleton ring the initiator and responder are the
same physical node, and changing that one label cannot make its self-edge
successor-consecutive for `k > 1`.
-/
theorem defect_advance_edge {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (hn2 : 1 < n)
    (L : Labels n k) (e : Fin n) :
    defect hk ring (advanceLabels hk ring L e) e = zeroResidue hk := by
  letI : NeZero k := ⟨by omega⟩
  have hre : ring.rightNeighbor e ≠ e := rightNeighbor_ne_self ring hn2 e
  have her : e ≠ ring.rightNeighbor e := Ne.symm hre
  simp [defect, advanceLabels, zeroResidue, her]


/-- In barrier language, the source edge disappears after its advance. -/
theorem advance_repairs_edge {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (hn2 : 1 < n)
    (L : Labels n k) (e : Fin n) :
    ¬ BarrierAt hk ring (advanceLabels hk ring L e) e := by
  intro h
  exact h (defect_advance_edge hk ring hn2 L e)


/-- The exact charged-barrier law: after advancing `e`, the new charge on
`e⁺` is the old charge on `e` plus the old charge on `e⁺`, modulo `k`.


This is the deterministic coalescence algebra; it says nothing about when the
protocol scheduler enables or selects the advance.
-/
theorem defect_advance_edgePlus {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (hn2 : 1 < n)
    (L : Labels n k) (e : Fin n) :
    defect hk ring (advanceLabels hk ring L e) (ring.rightNeighbor e) =
      defect hk ring L e + defect hk ring L (ring.rightNeighbor e) := by
  letI : NeZero k := ⟨by omega⟩
  let r := ring.rightNeighbor e
  have hre : r ≠ e := rightNeighbor_ne_self ring hn2 e
  have hrr : ring.rightNeighbor r ≠ r :=
    rightNeighbor_ne_self ring hn2 r
  have hsucc (x : Fin k) : succLabel hk x = x + 1 := by
    apply Fin.ext
    change (x.val + 1) % k = (x.val + (1 % k)) % k
    calc
      (x.val + 1) % k = (x.val % k + 1 % k) % k := Nat.add_mod _ _ _
      _ = (x.val + 1 % k) % k := by rw [Nat.mod_eq_of_lt x.isLt]
  unfold defect
  simp [advanceLabels, r, hrr, hsucc]
  grind


/-- Every edge other than `e` and `e⁺` keeps exactly the same defect. -/
theorem defect_advance_other {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (L : Labels n k) (e j : Fin n)
    (hje : j ≠ e) (hjr : j ≠ ring.rightNeighbor e) :
    defect hk ring (advanceLabels hk ring L e) j = defect hk ring L j := by
  have hjnext : ring.rightNeighbor j ≠ ring.rightNeighbor e := by
    intro h
    exact hje (rightNeighbor_injective ring h)
  simp [defect, advanceLabels, hjr, hjnext]


/-! ## Barrier-count monotonicity of an advance -/


/-- One label advance cannot increase the number of barriers.


The proof injects every post-advance barrier into the old support after mapping
old edge `e` to `e⁺`.  If `e⁺` was already a barrier it represents itself; if it
was not, a nonzero post-charge there must come from the old charge on `e` by
`defect_advance_edgePlus`.
-/
theorem barrierCount_advance_le {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (hn2 : 1 < n)
    (L : Labels n k) (e : Fin n) :
    barrierCount hk ring (advanceLabels hk ring L e) ≤
      barrierCount hk ring L := by
  letI : NeZero k := ⟨by omega⟩
  let D := advanceLabels hk ring L e
  let r := ring.rightNeighbor e
  let redirect : Fin n → Fin n := fun x => if x = e then r else x
  have hre : r ≠ e := rightNeighbor_ne_self ring hn2 e
  have hsubset :
      barrierSupport hk ring D ⊆
        (barrierSupport hk ring L).map redirect := by
    intro j hj
    have hjbar := (mem_barrierSupport_iff hk ring D j).mp hj
    unfold BarrierAt at hjbar
    by_cases hje : j = e
    · subst j
      exact (hjbar (defect_advance_edge hk ring hn2 L e)).elim
    · by_cases hjr : j = r
      · subst j
        by_cases hpre : BarrierAt hk ring L r
        · have hm : r ∈ barrierSupport hk ring L :=
            (mem_barrierSupport_iff hk ring L r).mpr hpre
          have him := List.mem_map_of_mem (f := redirect) hm
          simpa [redirect, hre] using him
        · unfold BarrierAt at hpre
          have hprezero : defect hk ring L r = zeroResidue hk :=
            Decidable.not_not.mp hpre
          have htransfer := defect_advance_edgePlus hk ring hn2 L e
          have hebar : BarrierAt hk ring L e := by
            unfold BarrierAt
            intro hezero
            apply hjbar
            rw [htransfer, hezero, hprezero]
            apply Fin.ext
            change (0 + 0) % k = 0
            exact Nat.zero_mod k
          have hm : e ∈ barrierSupport hk ring L :=
            (mem_barrierSupport_iff hk ring L e).mpr hebar
          have him := List.mem_map_of_mem (f := redirect) hm
          simpa [redirect] using him
      · have hsame := defect_advance_other hk ring L e j hje hjr
        have hjpre : BarrierAt hk ring L j := by
          unfold BarrierAt
          intro hz
          apply hjbar
          rw [hsame, hz]
        have hm : j ∈ barrierSupport hk ring L :=
          (mem_barrierSupport_iff hk ring L j).mpr hjpre
        have him := List.mem_map_of_mem (f := redirect) hm
        simpa [redirect, hje] using him
  have hlen :=
    (barrierSupport_nodup hk ring D).length_le_of_subset hsubset
  simpa [barrierCount, List.length_map] using hlen


/-! ## Connection back to the literal transition -/


/-- The precise local gate under which Protocol 6 takes its label-advance
branch. -/
def PairAdvanceReady {k : Nat} (hk : 0 < k) (u v : State k) : Prop :=
  IsBarrier hk u v ∧ u.phase = true ∧ v.probe = false


/-- Readiness at physical ring edge `e`. -/
def AdvanceReady {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (C : Fin n → State k) (e : Fin n) : Prop :=
  PairAdvanceReady hk (C e) (C (ring.rightNeighbor e))


/-- Outside the advancing branch the local transition preserves both labels. -/
theorem transition_labels_of_not_pairAdvanceReady {k : Nat} (hk : 0 < k)
    (u v : State k) (hnot : ¬ PairAdvanceReady hk u v) :
    (transition hk u v).1.label = u.label ∧
      (transition hk u v).2.label = v.label := by
  by_cases hbar : IsBarrier hk u v
  · cases hphase : u.phase with
    | false =>
        rw [transition_of_barrier hk u v hbar]
        rw [barrierStep_phase_zero hk u v hphase]
        constructor
        · simp
        · split <;> rfl
    | true =>
        cases hprobe : v.probe with
        | false =>
            exact (hnot ⟨hbar, hphase, hprobe⟩).elim
        | true =>
            rw [transition_of_barrier hk u v hbar]
            rw [barrierStep_phase_one_probe_blocked hk u v hphase hprobe]
            simp
  · rw [transition_of_nonbarrier hk u v hbar]
    cases hv : v.leader <;>
      cases hb : v.bullet <;>
      cases hp : u.probe <;>
      simp [nonBarrierStep, hv, hb, hp]


/-- If the advance gate is closed, one packaged physical step preserves the
entire label configuration.  This remains true even on a singleton ring. -/
theorem labelsOf_step_eq_self_of_not_ready {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (C : Fin n → State k) (e : Fin n)
    (hnot : ¬ AdvanceReady hk ring C e) :
    labelsOf ((protocol k hk).step ring C e) = labelsOf C := by
  have hp := transition_labels_of_not_pairAdvanceReady hk
    (C e) (C (ring.rightNeighbor e)) hnot
  funext i
  by_cases hie : i = e
  · subst i
    simp [labelsOf, PopulationProtocol.step, protocol, hp.1]
  · by_cases hir : i = ring.rightNeighbor e
    · subst i
      simp [labelsOf, PopulationProtocol.step, protocol, hie, hp.2]
    · simp [labelsOf, PopulationProtocol.step, protocol, hie, hir]


/-- When the exact journal advance gate is open, the packaged transition has
exactly the abstract `advanceLabels` effect. -/
theorem labelsOf_step_eq_advance_of_ready {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (hn2 : 1 < n)
    (C : Fin n → State k) (e : Fin n)
    (hready : AdvanceReady hk ring C e) :
    labelsOf ((protocol k hk).step ring C e) =
      advanceLabels hk ring (labelsOf C) e := by
  rcases hready with ⟨hbar, hphase, hprobe⟩
  have hre : ring.rightNeighbor e ≠ e := rightNeighbor_ne_self ring hn2 e
  have her : e ≠ ring.rightNeighbor e := Ne.symm hre
  have hpair :
      transition hk (C e) (C (ring.rightNeighbor e)) =
        (probeHitsBarrier (C e),
          { C (ring.rightNeighbor e) with
            label := succLabel hk (C e).label
            phase := false
            bullet := false }) := by
    rw [transition_of_barrier hk _ _ hbar]
    exact barrierStep_phase_one_probe_free hk _ _ hphase hprobe
  funext i
  by_cases hie : i = e
  · subst i
    simp [labelsOf, advanceLabels, PopulationProtocol.step, protocol,
      hpair, her]
  · by_cases hir : i = ring.rightNeighbor e
    · simp [labelsOf, advanceLabels, PopulationProtocol.step, protocol,
        hpair, hir, hre]
    · simp [labelsOf, advanceLabels, PopulationProtocol.step, protocol,
        hpair, hie, hir]


/-- A real `P_k` advance repairs its activated edge. -/
theorem protocol_advance_repairs_edge {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (hn2 : 1 < n)
    (C : Fin n → State k) (e : Fin n)
    (hready : AdvanceReady hk ring C e) :
    ¬ BarrierAt hk ring
      (labelsOf ((protocol k hk).step ring C e)) e := by
  rw [labelsOf_step_eq_advance_of_ready hk ring hn2 C e hready]
  exact advance_repairs_edge hk ring hn2 (labelsOf C) e


/-- A real `P_k` advance adds the old charge of `e` into `e⁺`. -/
theorem protocol_advance_charge_edgePlus {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (hn2 : 1 < n)
    (C : Fin n → State k) (e : Fin n)
    (hready : AdvanceReady hk ring C e) :
    defect hk ring (labelsOf ((protocol k hk).step ring C e))
        (ring.rightNeighbor e) =
      defect hk ring (labelsOf C) e +
        defect hk ring (labelsOf C) (ring.rightNeighbor e) := by
  rw [labelsOf_step_eq_advance_of_ready hk ring hn2 C e hready]
  exact defect_advance_edgePlus hk ring hn2 (labelsOf C) e


/-- Every physical transition weakly decreases the barrier count on a
non-singleton ring.  The only branch changing labels is the advance branch;
all other branches are label-identical. -/
theorem protocol_step_barrierCount_le {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (hn2 : 1 < n)
    (C : Fin n → State k) (e : Fin n) :
    barrierCount hk ring
        (labelsOf ((protocol k hk).step ring C e)) ≤
      barrierCount hk ring (labelsOf C) := by
  by_cases hready : AdvanceReady hk ring C e
  · rw [labelsOf_step_eq_advance_of_ready hk ring hn2 C e hready]
    exact barrierCount_advance_le hk ring hn2 (labelsOf C) e
  · rw [labelsOf_step_eq_self_of_not_ready hk ring C e hready]
    exact Nat.le_refl _


/-! ## A barrier exists whenever `k` does not divide the ring length -/


/-- On a barrier-free labeling, labels along the canonical clockwise walk are
`base+t (mod k)`. -/
theorem labels_ringVertex_of_no_barriers {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (L : Labels n k)
    (hnone : ∀ e : Fin n, ¬ BarrierAt hk ring L e) (t : Nat) :
    (L (ringVertex ring t)).val =
      ((L (ringVertex ring 0)).val + t) % k := by
  induction t with
  | zero =>
      simpa using (Nat.mod_eq_of_lt (L (ringVertex ring 0)).isLt).symm
  | succ t ih =>
      have hs := label_successor_of_not_barrier hk ring L
        (ringVertex ring t) (hnone (ringVertex ring t))
      rw [rightNeighbor_ringVertex] at hs
      have hv := congrArg Fin.val hs
      change (L (ringVertex ring (t + 1))).val =
        ((L (ringVertex ring t)).val + 1) % k at hv
      calc
        (L (ringVertex ring (t + 1))).val =
            ((L (ringVertex ring t)).val + 1) % k := hv
        _ = (((L (ringVertex ring 0)).val + t) % k + 1) % k := by
          rw [ih]
        _ = ((L (ringVertex ring 0)).val + t + 1) % k :=
          mod_succ_eq ((L (ringVertex ring 0)).val + t) k
        _ = ((L (ringVertex ring 0)).val + (t + 1)) % k := by
          rw [Nat.add_assoc]


/-- A barrier-free cycle can close only when `k` divides the number of nodes. -/
theorem dvd_ring_length_of_no_barriers {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (L : Labels n k)
    (hnone : ∀ e : Fin n, ¬ BarrierAt hk ring L e) :
    k ∣ n := by
  have hwalk := labels_ringVertex_of_no_barriers hk ring L hnone n
  rw [ringVertex_period ring] at hwalk
  exact dvd_of_lt_mod_add_eq
    (L (ringVertex ring 0)).val n k hk
    (L (ringVertex ring 0)).isLt hwalk


/-- Main static obstruction: if `k ∤ n`, every labeling of the directed ring
contains at least one generalized AAFJ barrier. -/
theorem exists_barrier_of_not_dvd {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (L : Labels n k)
    (hndvd : ¬ k ∣ n) :
    ∃ e : Fin n, BarrierAt hk ring L e := by
  classical
  by_cases hex : ∃ e : Fin n, BarrierAt hk ring L e
  · exact hex
  · exfalso
    apply hndvd
    apply dvd_ring_length_of_no_barriers hk ring L
    intro e he
    exact hex ⟨e, he⟩


/-- The same existence theorem stated directly for the full five-field
configuration and its source-level `IsBarrier` predicate. -/
theorem exists_state_barrier_of_not_dvd {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (C : Fin n → State k)
    (hndvd : ¬ k ∣ n) :
    ∃ e : Fin n,
      IsBarrier hk (C e) (C (ring.rightNeighbor e)) := by
  obtain ⟨e, he⟩ :=
    exists_barrier_of_not_dvd hk ring (labelsOf C) hndvd
  exact ⟨e, (barrierAt_labelsOf_iff hk ring C e).mp he⟩


/-- Nondivisibility makes the barrier support nonempty in every full state. -/
theorem barrierCount_pos_of_not_dvd {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (C : Fin n → State k)
    (hndvd : ¬ k ∣ n) :
    0 < barrierCount hk ring (labelsOf C) := by
  obtain ⟨e, he⟩ := exists_barrier_of_not_dvd hk ring (labelsOf C) hndvd
  have hm : e ∈ barrierSupport hk ring (labelsOf C) :=
    (mem_barrierSupport_iff hk ring (labelsOf C) e).mpr he
  unfold barrierCount
  exact List.length_pos_of_mem hm


/-- On a nondivisible non-singleton ring, one barrier remains exactly one
after every physical protocol interaction. -/
theorem protocol_step_preserves_oneBarrier {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (hn2 : 1 < n)
    (C : Fin n → State k) (e : Fin n)
    (hndvd : ¬ k ∣ n)
    (hone : barrierCount hk ring (labelsOf C) = 1) :
    barrierCount hk ring
        (labelsOf ((protocol k hk).step ring C e)) = 1 := by
  have hle := protocol_step_barrierCount_le hk ring hn2 C e
  have hpos := barrierCount_pos_of_not_dvd hk ring
    ((protocol k hk).step ring C e) hndvd
  omega


end BarrierAlgebra
end AAFJPK
